#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量迁移（先全写再统一验证）。

## 为什么批量

单模块迁移 + 立即验证的代价：
- 每个模块的 `lake build <单模块>` 要编它自己的依赖链（5–20 分钟）
- 每轮再跑一次全库验证（约 19 分钟）

攒一批一起验证，构建只做一次，且失败时能一次性看到所有问题模块。

## 代价

失败定位要逐个文件看。所以本脚本会：
1. 一次性写出 N 个模块（不做 per-module 编译）
2. 跑一次全库 build
3. 从输出里解析出失败模块，逐个删除并报告

## 用法

    python _migration/batch_all.py --plan 6        # 只列计划
    python _migration/batch_all.py --run 6         # 迁 6 个并验证
    python _migration/batch_all.py --run 6 --domain Predict
"""
import os, re, sys, json, argparse, subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import port_v2

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
V2 = os.path.join(ROOT, 'FateWorld', 'FateV2')

# 人工判定的域分配（按依赖+职责，不按文件名）
DOMAIN_HINT = {
    # —— 第四十七批 ——
    'NonDescendantsMem': 'Predict', 'BarSdiffEq': 'Predict',
    # —— 第四十六批 ——
    'SolutionCLMGcCounterexample': 'Predict', 'SdiffEraseEq': 'Predict',
    'LMGcProjectionNote': 'Predict', 'SolutionCLMGcNote': 'Predict',
    # —— 第四十五批（含纯文档模块）——
    'SinkPeelDiagnosis': 'Predict', 'LMGcCoverObstacle': 'Predict',
    'NaryIndexCheck': 'Modeling', 'RouteBGapNote': 'Predict',
    'TwoRoutesNote': 'Predict',
    # —— 第四十四批 ——
    'MassSdiffConst': 'Predict',
    # —— 第四十三批 ——
    'TailBlockReal2Consumer': 'Predict', 'BlockCIDerivation': 'Predict',
    'GhostAliases': 'Predict', 'SinkPeelCounterexample': 'Predict',
    'NaryFin2': 'Modeling', 'TailBlockIntegration': 'Predict',
    # —— 第四十二批 ——
    'TailBlockReal2': 'Predict', 'TailFromDSepIntegration': 'Predict',
    'NaryIndex': 'Modeling', 'TailBlockAssemble': 'Predict',
    'BlockCIFactorization': 'Predict', 'BlockCIUltimate': 'Predict',
    'MassMultSBridge': 'Predict',
    # —— 第四十一批 ——
    'MultSUnify': 'Modeling', 'TailBlockBridge': 'Predict',
    'NaryGeneric': 'Modeling', 'BlockCIGeneralC': 'Predict',
    # —— 第四十批 ——
    'MassBoundaryValues': 'Predict', 'TailBlockCondIndep': 'Predict',
    'MassAEqCorrected': 'Predict', 'MassFactorOfReads': 'Predict',
    'NaryPointwise': 'Modeling',
    # —— 第三十九批 ——
    'BridgeGeneralizeTight': 'Predict', 'BridgeGeneralizeWiring': 'Predict',
    'DAGBridgeConsumer': 'Predict', 'NaryBridgeDone': 'Modeling',
    'MassInsertCorrected': 'Predict', 'BlockCIOfBlockSplit': 'Predict',
    'NaryClose': 'Modeling', 'TailBlockMassDcomp': 'Predict',
    # —— 第三十八批 ——
    'SplitFromDSepComplete': 'Predict', 'BridgeGeneralize': 'Predict',
    'TailBlockV4Consumer': 'Predict', 'TailFromDSep': 'Predict',
    'MassADecompFinal': 'Predict', 'SubFibCard': 'Predict',
    'BridgeDSepGeneral': 'Predict', 'NaryBridgeFinal': 'Modeling',
    # —— 第三十七批 ——
    'TailBlockV4': 'Predict', 'CondIndepCondMulBridge': 'Modeling',
    'SplitFromDAG': 'Predict', 'RebaseSplit': 'Predict',
    'TailFromDSepFork': 'Predict', 'TailBlockFinal': 'Predict',
    'BridgeIntegrated': 'Predict', 'LMGcCondIndepEquiv': 'Predict',
    'ArrowEquivA': 'Modeling', 'BlockCIOfBlockSplitFinal': 'Predict',
    'NaryConnect3': 'Modeling', 'TailTailCollapse': 'Predict',
    # —— 第三十六批（链尾释放）——
    'CondIndepGeneralNZ': 'Modeling', 'FactorizesToHyper': 'Predict',
    'NaryLink': 'Modeling',
    # —— 第三十五批 ——
    'CondIndepEmptyZ': 'Modeling', 'NaryCancel': 'Modeling',
    # —— 第三十四批 ——
    'View16PotentialTransport': 'Predict', 'MainTheoremCFinal': 'Predict',
    'BalanceFactorPart': 'Predict', 'NaryProduct': 'Modeling',
    # —— 第三十三批 ——
    'BalanceComponents': 'Modeling', 'NaryMassLink': 'Modeling',
    # —— 第三十二批 ——
    'BridgeMinZPrimeConsumer': 'Predict', 'ZipDownFalseZStarConsumer': 'Predict',
    'BridgeZipAConsumer': 'Predict', 'ZipDownFalseConsumer': 'Predict',
    'BridgeDirectConsumer': 'Predict', 'BridgeExpandedT7': 'Predict',
    'R44CutBridge': 'Loop', 'R44SubstanceBridge': 'Loop',
    'SumMulSepFull': 'Modeling', 'NaryAssembly': 'Modeling',
    # —— 第三十一批 ——
    'BridgeDirect': 'Predict', 'BridgeExpanded': 'Predict',
    'BridgeFullFixed': 'Predict', 'BridgeFull': 'Predict',
    'MVFCAFinset': 'Rules', 'StrongSignature': 'Rules',
    'SumMulSep': 'Modeling', 'NaryFiberDecomp': 'Modeling',
    # —— 第三十批（纯定义模块筛选修正后）——
    'FcaToRuleTerm': 'Rules', 'FcaRuleEntersWorldModel': 'Predict',
    'RuleReadSetWiringConsumer': 'Rules',
    'ConcreteBridgeQuant': 'Predict', 'WorldModelCompleteV2W': 'Loop',
    'NaryMargSum': 'Modeling', 'SumSeparation': 'Modeling',
    'ThreeNode': 'Modeling', 'UnifyVerification': 'Meta',
    '_T1A2_Gap': 'Predict',
    # —— 第二十九批 ——
    'RuleReadSetWiring': 'Rules', 'WorldModelCompleteV2NonDeg': 'Loop',
    'AlphaDataToLawRule': 'Rules', 'AlphaAndStochasticWiringConsumer': 'Rules',
    'T611FullConsumer': 'Rules', 'AlphaDataConsumed': 'Rules',
    'QuantCompletion': 'Predict', 'NaryFinalBridge': 'Modeling',
    # —— 第二十八批 ——
    'T611Full': 'Rules', 'AlphaAndStochasticWiring': 'Rules',
    'AlphaDataConsumed': 'Rules', 'AlphaDataToPartition': 'Rules',
    'PairingAlphaBridge': 'Predict', 'PairingToAlphaData': 'Predict',
    'QuotientCardinality': 'Predict', 'WorldModelCompleteV2': 'Loop',
    'NaryRealSum': 'Modeling',
    # —— 第二十七批（Completeness 误判清除后释放）——
    'AlphaFCAConstruction': 'Rules', 'Satisfiability': 'Rules',
    'Minimality': 'Rules', 'T611Full': 'Rules',
    'AlphaDataConsumed': 'Rules',
    'ComposeDefault': 'Rules', 'ComposeEmbedding': 'Rules',
    'LoopBound': 'Error', 'NaryBridgeMulti': 'Modeling',
    # —— 第二十六批 ——
    'AdaptiveEtaConsumer': 'Loop', 'AlphaFourOpConsumer': 'Rules',
    'ComposeUnified': 'Rules', 'NaryBridge': 'Modeling',
    # —— 第二十五批 ——
    'AlphaFourOp': 'Rules', 'WiringFCAAlphaConsumer': 'Rules',
    'RuleRelaxation': 'Rules', 'EvaluationSystemsConsumer': 'Rules',
    'UpsilonIterationConsumer': 'Rules', 'ComposeSemantics': 'Rules',
    'UpsilonIterConsumer': 'Rules',
    'EndToEndWithRulesNegative': 'Loop', 'NaryConnect2': 'Modeling',
    # —— 第二十四批 ——
    'UpsilonIteration': 'Rules', 'EvaluationSystems': 'Rules',
    'WiringFCAAlpha': 'Rules', 'WiringFourOpFixed': 'Rules',
    'WiringFourOperators': 'Rules', 'FourOperators': 'Rules',
    'GaloisEmbedding': 'Rules', 'LabelAudit': 'Rules',
    'InstSpaceToLawRule': 'Rules', 'StepToLawGenFiber': 'Rules',
    'RoundtripAsymmetry': 'Rules', 'AlphaKernelAudit': 'Rules',
    'TailVerdict': 'Predict', 'TailBlockMassDecomp': 'Predict',
    'FactorizesNotImpliesLMG': 'Predict',
    'KernelQuotientRecovery': 'Modeling', 'NaryConnect': 'Modeling',
    'NonemptyFree3': 'Predict',
    # —— 第二十三批 ——
    'UpsilonOperator': 'Rules', 'GammaOperator': 'Rules',
    'AlphaConcreteInstance': 'Rules', 'Adjunction': 'Rules',
    'VarsigmaScale': 'Rules', 'AlphaStatistical': 'Rules',
    'AlphaKernel': 'Rules', 'Stage1A': 'Rules',
    'CellDiameter': 'Rules', 'StepToLaw': 'Rules',
    'RuleEntersWorldModel': 'Loop', 'InvarianceContentful': 'Meta',
    'CompNotCommutative': 'Rules',
    'PathDepIsDerived': 'Model', 'TrajLawIsProb': 'Model',
    'TailBlockReal': 'Predict', 'NaryFinal': 'Modeling',
    'ColliderDAGValues': 'Predict',
    # —— 第二十二批（Basic 误判修正后释放）——
    'Alpha': 'Rules', 'Adjunction': 'Rules',
    'AlphaConcreteInstance': 'Rules', 'ConceptLatticeComplete': 'Rules',
    'ComposeOperator': 'Rules',
    'T1MultiDim': 'Predict', 'ThetaMatters': 'Loop',
    'PathDependence': 'Predict', 'Adjudication': 'Meta',
    'GhostBoundaries': 'Predict', 'TrajGenArbitrary': 'Model',
    'RuleEvaluation': 'Rules', 'TrajGenStochastic': 'Model',
    'TailOutExtract': 'Predict', 'DetFunToStep': 'Model',
    'MainTheoremC': 'Predict', 'NaryKernel2': 'Modeling',
    'NotLMGColliderP': 'Predict', 'StepToLawDraft': 'Rules',
    # —— 第二十一批 ——
    'GraphToProbView7': 'Predict', 'ZipDownFalse': 'Predict',
    'Strategy13Filler': 'Predict', 'T1A2Fin': 'Predict',
    'ColliderPValues': 'Predict', 'MassProCover': 'Predict',
    'NaryKernel': 'Modeling',
    # —— 第二十批 ——
    'CondIndepIntersection': 'Modeling', 'NaryTrim': 'Modeling',
    'BridgeMinZPrime': 'Predict', 'BridgeZipA': 'Predict',
    'BridgeZipDown': 'Predict', 'BridgeA3': 'Predict',
    'View2ElimIterate': 'Predict', 'NonemptyFree2': 'Predict',
    'View3FiberMassBridge': 'Predict', 'BridgeA1Prime': 'Predict',
    'BridgeB4': 'Predict', 'RouteC': 'Predict',
    'View10AdmissibleReach': 'Predict', 'ProdSplitSides': 'Predict',
    'Strategy13TypedSplit': 'Predict', 'TailBlockQuadraticCounterexample': 'Predict',
    'T1A2Prob': 'Predict', 'BridgeA4Fixed': 'Predict',
    # —— 第十九批 ——
    'NKernelValue': 'Modeling', 'CondIndepContraction': 'Modeling',
    'MainlineIntegration': 'Modeling',
    'View3AtomStratification': 'Predict', 'Strategy11AncestralHull': 'Predict',
    'View14CutReweight': 'Predict', 'BridgeThreeNode': 'Predict',
    'Strategy9TopoLayerTruncation': 'Predict', 'BridgeView2Elimination': 'Predict',
    'BridgeA1': 'Predict', 'Strategy13FiberFubini': 'Predict',
    'View15KernelSeparation': 'Predict', 'BridgeA2': 'Predict',
    'BridgeStrategy1TopoPeel': 'Predict',
    'BridgeView9EdgeKernelConsumer': 'Predict',
    'Strategy11FiberPinned': 'Predict', 'BridgeB1Final': 'Predict',
    'SeparatedCondMulUnified': 'Predict', 'T1A2CI3': 'Predict',
    'ViewTenThreeBlock': 'Predict', 'Strategy9SinkPeelVerdict': 'Predict',
    'View11SplitterChain': 'Predict',
    'BridgeStrategy5FiberBijection': 'Predict', 'TowerExactLaw': 'Predict',
    'FactorizesOnComponents': 'Predict',
    # —— 第十八批 ——
    'CondIndepSemigraphoid': 'Modeling', 'NaryMeasure': 'Modeling',
    'NaryAlgebra': 'Modeling',
    'SeparatedCondMulZ': 'Predict', 'T1A2Substance': 'Predict',
    'BridgeView9EdgeKernel': 'Predict', 'AncestralInheritanceRouteB': 'Predict',
    'ThreeNodeFactorizes': 'Predict',
    'FactorRecursionRouteB_Obligations': 'Predict',
    'Strategy11TopoPrefix': 'Predict', 'BridgeView3AtomStratification': 'Predict',
    'LMGGlobalMarkovRoute5': 'Predict', 'Strategy13FactorHoist': 'Predict',
    'View18BayesBallBlock': 'Predict', 'Audit10Factorizes': 'Predict',
    'View21StableBorder': 'Predict', 'DSepTopoPeel': 'Predict',
    'FourNodeCondMul': 'Predict', 'G1ParentNonDescendant': 'Predict',
    'Strategy12FactorSplitBridge': 'Predict', 'View20GraphToProb': 'Predict',
    'Strategy9SinkPeelNorm': 'Predict', 'View19FactorGraphSplit': 'Predict',
    'TowerAudit': 'Predict', 'Strategy13Fixed': 'Predict',
    'BarCorrected': 'Predict',
    'GuardNecessary': 'Modeling', 'BridgeSingleFiber': 'Modeling',
    'BridgeReverse': 'Modeling',
    # —— 第十七批 ——
    'ChainGenuineGap1': 'Predict', 'CondIndepN': 'Modeling',
    'MarkovEquivalence': 'Predict', 'T1A1Graphs': 'Predict',
    'FactorRecursionRouteB': 'Predict', 'MarkovToSeparableGen': 'Predict',
    'BridgeB2': 'Modeling', 'FactorMarkov': 'Predict',
    'MarkovGroupWiring': 'Predict', 'BridgeEquiv': 'Modeling',
    'SeparatedCondMul': 'Predict', 'USeparatedMoral': 'Predict',
    'EndToEndQConsumer': 'Loop', 'EndToEndUnconditionalEval': 'Loop',
    'View6FactorSupportConsumer': 'Predict', 'MainChainConsumer': 'Loop',
    # —— 第十六批 ——
    'CondMassTower': 'Predict', 'View6FactorSupport': 'Predict',
    'DAGFactorizationGeneral': 'Predict', 'BridgeStrategy4CoordSlice': 'Predict',
    'ChainMarkovExplicitAntecedent': 'Predict',
    'SetupXMYDemoLawConsumer': 'Predict', 'View6ZoneCut': 'Predict',
    'View6ElimComplete': 'Predict', 'SetupXMYDemoLawConsumer2': 'Predict',
    'T1A1': 'Predict', 'MarkovBridgeTopo': 'Predict',
    'SeparatedImpliesSide': 'Predict', 'MarkovToSeparable': 'Predict',
    'RuleActivationClosureOpConsumer': 'Rules',
    'DeadPremiseAuditConsumer': 'Meta',
    'GapTrimWeightedCount': 'Modeling', 'BridgeFinal': 'Modeling',
    'RegressStep9Fiber': 'Modeling',
    'SCMWorldModelEval': 'Loop', 'SCMEndToEndGeneralQ': 'Loop',
    'EndToEndUnconditionalConsumer': 'Loop', 'EndToEndUnconditionalQ': 'Loop',
    # —— 第十五批 ——
    'DAGFactorization': 'Predict', 'RuleActivationClosureOp': 'Rules',
    'SetupXMYDemoLaw': 'Predict', 'BridgeKernel': 'Modeling',
    'SCMWorldModelEvalNum': 'Loop', 'CliqueSideSeparable': 'Predict',
    'SCMEndToEndConsumer': 'Loop', 'CausalCtxUnified': 'Predict',
    'LawRuleCondMulConsumer': 'Predict', 'GlobalMarkovChainNConsumer': 'Predict',
    'EndToEndUnconditional': 'Loop', 'NonemptyFree4': 'Predict',
    'SCMEndToEndGeneral': 'Loop', 'Pairing': 'Model', 'NonemptyFree': 'Predict',
    'MarkovBridgeReal': 'Predict',
    # —— 第十四批（清空候选池）——
    'ChainDsepFull': 'Predict', 'BackdoorXMY': 'Predict',
    'CliqueChain': 'Predict', 'SetupXMYDemo': 'Predict',
    'CausalClassificationBridge': 'Predict',
    'MarkovBridgeTheorem': 'Predict', 'Adjacency': 'Rules',
    'RuleReadSet': 'Rules', 'LawRuleCondMul': 'Predict',
    'MinimalLegSet': 'Predict',
    'SCMEndToEnd': 'Loop', 'TwoDPrediction': 'Loop', 'FillGapStrong': 'Loop',
    'EndToEndPipelineTendsto': 'Loop',
    'PipelineAdaptiveEtaMartingale': 'Loop',
    'ErrorBoundE2d': 'Error', 'ErrorBoundE2f': 'Error',
    'BridgeProofStep3': 'Modeling',
    # —— 第十三批 ——
    'WiringBackdoorConsumer': 'Predict',
    'BackdoorGraphicalGeneral': 'Predict', 'LegContribution': 'Predict',
    'CliqueGrouping': 'Predict', 'CausBayesBallEquiv': 'Predict',
    'CliqueDecompositionGenuine': 'Predict', 'SetupXMY': 'Predict',
    'T1A2N': 'Predict', 'T21Decidable': 'Predict', 'CoreBridge': 'Predict',
    'CounterfactualLip': 'Predict', 'ChainMarkovInductive': 'Predict',
    'FCAcl': 'Rules', 'TrajPattern': 'Rules',
    'FirstLayerUnified': 'Error', 'FirstLayerExpectedFinalRedundant': 'Error',
    'BridgeProof': 'Modeling',
    'FillGap': 'Loop', 'PipelineTendstoSpecializes': 'Loop',
    'MacroShiftsMicro': 'Predict',
    'TrajGenMeasurableFull': 'Model',
    'PipelineAdaptiveEtaStochastic': 'Loop',
    'PipelineEndToEndCapstone': 'Loop',
    'WorldModelCapstoneConsumerFixes': 'Loop',
    'WorldModelInstance2D': 'Loop',
    # —— 第十二批 ——
    'WiringBackdoor': 'Predict', 'WiringDoCalcFixedConsumer': 'Predict',
    'ChainDsepN': 'Predict', 'ChainDsepNInvariant': 'Predict',
    'G2Backdoor': 'Predict', 'G2Counterexample': 'Predict',
    'BackdoorZGraphical': 'Predict', 'UnifiedMainline': 'Predict',
    'MarkovBridge': 'Predict', 'GazeRevisesCausal': 'Predict',
    'UndirectedGlobalMarkov': 'Predict', 'T1A2Bridge': 'Predict',
    'T1A2Chain': 'Predict', 'VerifyFalseClaim': 'Predict',
    'StepExpressiveness': 'Model', 'MultiObject': 'Model',
    'T112Exactly': 'Rules', 'RuleExecDemo': 'Rules',
    'AssemblyInstance': 'Predict', 'NLegAssembly': 'Predict',
    'CategoricalStratification': 'Modeling',
    'FinCondIndepMeasure': 'Modeling',
    'ChainErrorBudgetTightWiring': 'Error',
    'FirstLayerExpectedFinal': 'Error', 'FirstLayerExpectedGeneral': 'Error',
    'ObsEstimationStrongG4Link': 'Error',
    'PipelineAdaptiveEtaRobust': 'Loop',
    'WorldModelMainTheorem': 'Loop',
    # —— 第十一批 ——
    'T112FCASpecific': 'Rules', 'T112FCASpecific2': 'Rules',
    'T112FCATheorems': 'Rules',
    'BackdoorWithM': 'Predict', 'GlobalMarkovChainN': 'Predict',
    'WiringDoCalcFixed': 'Predict', 'Rule13GenuineConsumer': 'Predict',
    'Assembly': 'Predict', 'FixDead': 'Predict', 'T1A2CI': 'Predict',
    'CounterfactualGenuine': 'Predict', 'AlphaOf': 'Rules',
    'BridgeQuotient': 'Predict',
    'KernelQuotientCategorical': 'Modeling', 'KernelAdjunction': 'Modeling',
    'EquivalenceLevels': 'Modeling', 'BridgeCarriers': 'Modeling',
    'ClosedLoopUnified': 'Loop', 'PipelineComplexityOptimal': 'Loop',
    'EndToEndConvergence': 'Loop',
    'ErrorBoundE2cFull': 'Error', 'AudUnivLayer2b': 'Error',
    'ChainErrorBudgetPredNTight': 'Error',
    'TrajGenMeasurable': 'Model', 'Core': 'Core',
    # —— 第十批 ——
    'Rule1Genuine': 'Predict', 'Rule2Genuine': 'Predict',
    'Rule13Genuine': 'Predict', 'GlobalMarkovChain4': 'Predict',
    'T112Candidates': 'Rules', 'T112FCAPolar': 'Rules',
    'T112PairProbe': 'Rules', 'DirectedClosure': 'Rules',
    'AlphaRulesLocal': 'Rules',
    'T35Rule1SplitConsumer': 'Predict',
    'ObservationUnifiedConsumer': 'Predict',
    'DoLawGen': 'Predict', 'CounterfactualAlgebra': 'Predict',
    'ViewThreeCounterfactual': 'Predict', 'ProxyRefinement': 'Predict',
    'CausalOnWorldModelAdjust': 'Predict',
    'MarkovBridgeAncestral': 'Predict',
    'NoDescendantWitness': 'Predict',
    'ThetaStabilityMetric': 'Model', 'FrameBridge': 'Model',
    'EndToEndPipelineBridge': 'Loop', 'EndToEndSelectorNotConstant': 'Loop',
    'ConvergeToOptimalIter': 'Loop', 'ChainErrorBudgetPredNGen': 'Error',
    'NoiseIdentifiability': 'Error', 'ErrorBoundE2b': 'Error',
    'ErrorBoundE4Full': 'Error', 'KernelQuotientExtra': 'Modeling',
    # —— 第九批 ——
    'T112SecondQuotient': 'Rules', 'T112UnaryClosure': 'Rules',
    'UpsilonRefine': 'Rules',
    'T35Rule1Split': 'Predict', 'Rule23Semantic': 'Predict',
    'ObservationUnified': 'Predict', 'MinimalSufficient': 'Predict',
    'PearlMarkovCrossFrameworks': 'Predict', 'PearlPathCompose': 'Predict',
    'AlphaMVFCA': 'Predict', 'CausalOnWorldModel': 'Predict',
    'ViewOneCounterfactual': 'Predict', 'CtxStructureSurvey': 'Model',
    'DSepCondNonMonotone': 'Predict', 'DoLawFin2': 'Predict',
    'G1True': 'Predict', 'T1VerifyStrong': 'Loop',
    'ClosedLoopWiring': 'Loop', 'ConvergeToOptimalDemoConsumer': 'Loop',
    'PipelineAdaptiveEtaComplexity': 'Loop',
    'FirstLayerCapstone': 'Error', 'ChainErrorBudgetPredN': 'Error',
    'ErrorBoundE1Euler': 'Error', 'ObsErrorRandom': 'Error',
    'ObsEstimationWeakConsumer': 'Error',
    # —— 第八批 ——
    'CFLatticeGen': 'Predict',
    'Rule1Semantic': 'Predict',
    'LawRuleAlgebraUnify': 'Predict',      # 依赖 LawRuleSatisfiabilityConsumer(已移Predict)
    'LawRuleRuleBridge': 'Rules',
    'T112FCAConnection': 'Rules', 'MVFCAClosure': 'Rules',
    'TermSizeConsumer': 'Rules',
    'PearlLawRuleBridgeConsumer': 'Predict',
    'Layer1NoisyChain': 'Error', 'ChainErrorBudgetBound': 'Error',
    'R44SigmaAssembly': 'Error',
    'T33DoGraphConsumer': 'Predict',
    'CounterfactualStrictness': 'Predict',
    'DoSemanticsBridge': 'Predict',
    'GapFalse': 'Loop',
    'CorrectsPropertiesConsumer': 'Loop',
    'EndToEndConvergeConsumer': 'Loop',
    'DemoConcrete': 'Loop',
    'PipelineAdaptiveEtaNormed': 'Loop',
    'ConvergeToOptimalStrong': 'Loop',
    'CfUnconditionalVertex': 'Loop',
    'MarginSizeIrrelevant': 'Loop',
    'MiddleZoneDichotomy': 'Predict',
    'DSepMarkov': 'Predict',
    'GraphToProbView17Consumer': 'Predict',
    'PearlMarkov': 'Predict',
    'ScenarioSharpForTree': 'Predict', 'ScenarioSharpWiring': 'Predict',
    'SCMIdentifiabilityCorrect': 'Modeling', 'SCMUnificationA': 'Modeling',
    # —— 第七批 ——
    'T33DoGraph': 'Predict', 'ParentMap': 'Predict',
    'DoCalculusRules': 'Predict', 'T1A2Encode': 'Predict',
    'FactorizesCondMul': 'Predict', 'InterventionSharpWiring': 'Predict',
    'PathWitnessDep': 'Predict', 'CausalClosureTight': 'Predict',
    'CFLattice': 'Predict', 'ConcreteBridge': 'Predict',
    'LawRuleMarginal': 'Rules', 'StatAlphaConsumer': 'Rules',
    'FusionConvergence': 'Rules', 'TieredScheme': 'Predict',
    'EndToEndConverge': 'Loop', 'PipelineAdaptiveEta': 'Loop',
    'ScratchAssemblyLearns': 'Loop', 'SimEndToEndLink': 'Loop',
    'CapstoneLipschitzLink': 'Loop', 'WorldModelCapstoneConsumer': 'Loop',
    'CausalDrivesGazeV2': 'Loop', 'ContinuousEval': 'Loop',
    'FirstLayerExpected': 'Error', 'FirstLayerExpectation': 'Error',
    'ShellEscrow': 'Error',
    # —— 第六批 ——
    'DetTrajScan': 'Model',                  # TrajGen*/Frame
    'TermSizeConsumer2': 'Rules',            # TermSize/RuleSyntaxOps
    'InstanceChain': 'Rules',                # LawRule
    'LawRuleSatisfiabilityConsumer': 'Rules',
    'LawRuleIdentifiability': 'Rules',
    'SynClosureBounded': 'Rules',            # Implication
    'SynClosureSemiNaive': 'Rules',
    'VersionSpaceBoundary': 'Rules',         # VersionSpace
    'CausalFCAAdjacency': 'Predict',
    'T1DegeneracyVerifyConsumer': 'Predict',
    'GraphOps': 'Predict',                   # DoCalculus/CausalDirection
    'T21DSepWellDefined': 'Predict',
    'T35Rule1NoConfounding': 'Predict',
    'View17Consumer': 'Predict',
    'T1A2Theta': 'Predict',                  # FinJoint/FinCondIndep
    'FactorizesToCondMul': 'Predict',
    'InterventionSharp': 'Predict',
    'InterventionSupConsumer': 'Predict',
    'ParametricEquiv': 'Predict',
    'EndToEndBounds': 'Loop',                # EndToEnd
    'ErrIterGeneral': 'Loop',                # WiringConvergence
    'EstimateErrorBound': 'Error',           # ChainBudgetBound/FirstLayerBound
    'FinFactorization': 'Modeling',          # FiniteCondIndep
    'RegressBridge': 'Modeling',             # FinMeasureBridge
    'SCMGraphSemantics': 'Modeling',         # SCMSemantics/SCMGraph
    # —— 第五批 ——
    'TermSize': 'Rules',                       # RuleExec
    'LawRuleSatisfiability': 'Rules',           # LawRuleLattice
    'LawRuleTwoDomains': 'Rules',
    'Compactness': 'Rules',                     # Implication
    'GazeAlgebraConsumer': 'Rules',             # Classification/GazeAlgebra
    'LawRulePointDecidabilityConsumer': 'Rules',
    'T68ComposeSemanticsConsumer': 'Rules',
    'T21FiniteSearchConsumer': 'Predict',
    'SCMIdentifiability': 'Loop',               # SCMResidual/ParamSCM
    'GapIsFalse': 'Loop',                       # EndToEnd
    'AdjudicationKUnified': 'Error',            # H5AdjudicationK/FitBoundary
    'TrajGenScan': 'Model',                     # TrajGenDeterministic/Frame
    'ActInputDecomp': 'Model',                  # Frame
    'CausalEventFormal': 'Predict',
    'BridgeZPrimeDSep': 'Predict',
    # —— 第四批（按依赖归属）——
    'SCMResidual': 'Loop',                  # SCMWorldModel/EndToEnd/BoundWriteBack
    'TwoVersionsConsumer': 'Loop',          # TwoVersions/LearnFunction
    'EvalDemo': 'Loop',                     # WorldModel/TrajGenDeterministic
    'KK1NoiseAsymmetryConsumer': 'Loop',    # ThetaConvergence/PipelineTendstoGen
    'RuleSyntaxGenOps': 'Rules',            # RuleSyntaxGen/RuleSyntaxExt
    'RuleExec': 'Rules',                    # RuleSyntax*
    'LawRuleUnion': 'Rules',                # LawRule/LawRuleLattice
    'SCMLawBridgeAdvance': 'Rules',         # SCMLawBridge/LawRuleToTraj
    'FCAGenuine': 'Rules',                  # FCA
    'ScottContinuity': 'Rules',             # FCA/Implication
    'H3LowerBound': 'Error',                # ObsEstimationStrong
    'H5AdjudicationK': 'Error',             # FitBoundary
    'Ancestral': 'Predict', 'KahnTopo': 'Predict',
    'PearlJointLaw': 'Predict', 'FinsetUnivOpt1': 'Predict',
    'MarkovFaithfulness': 'Predict', 'RegressFinMarkov': 'Predict',
    'ThreeViews': 'Predict', 'ZPrimeDSepRelation': 'Predict',
    # —— 第三批（按依赖归属）——
    'RuleSyntaxExt': 'Rules', 'RuleSyntaxGen': 'Rules',
    'LawRulePointDecidability': 'Rules', 'LawRulePointExtract': 'Rules',
    'SCMLawBridge': 'Rules',                # 依赖 LawRule
    'LearnFunctionUnified': 'Loop',         # 依赖 LearnFunction
    'EvalRealProof': 'Loop',                # 依赖 EvalReal
    'ConvergenceContrast': 'Loop',          # 依赖 WiringConvergence
    'PipelineTendstoGen': 'Loop',           # 依赖 WorldModelPipeline
    'DoLawWorldModel': 'Loop',              # 依赖 WorldModel/T34/T35
    'SCMWorldModel': 'Loop',                # 依赖 WorldModel
    'InterventionSup': 'Predict',           # 依赖 InterventionTight
    'View17SectionGlue': 'Predict',
    'OptimalityThirdInstance': 'Error',     # 依赖 FitBoundary（误差层）
    'FinMeasureBridge': 'Modeling',         # 依赖 FiniteCondIndep
    # —— 第二批判定（按依赖归属）——
    'RuleSyntaxOps': 'Rules',              # 依赖 RuleSyntax
    'FunThetaWorldModel': 'Loop',          # 依赖 EndToEnd（闭环）
    'EvalClosedLoop': 'Loop',              # 依赖 WiringConvergence
    'EvalReal': 'Loop',                    # 依赖 EndToEnd
    'AssemblyGainShared': 'Meta',          # 依赖 AssemblyMeta
    'CorrectsProperties': 'Loop',          # 依赖 BoundWriteBack / ConvergeToOptimal*
    'ResidualReducesInj': 'Loop',          # 依赖 ResidualReduces
    'InterventionGeneral': 'Predict',      # 依赖 InterventionTight
    'SCMKernel': 'Modeling',               # 依赖 SCMSemantics / CausDAG
    'ThetaExpressiveness': 'Modeling',     # 依赖 Frame
    'T1A2': 'Predict',                     # 依赖 CausDAG
    'ZBlockedWiringAudit': 'Predict',      # 依赖 WiringBackdoor*
    'CfPartialIdentConsumer': 'Predict',   # 依赖 CfPartialIdent
    'CondMI': 'Predict',                   # 依赖 FinCondIndep
    'BridgeB3': 'Predict',                 # 依赖 CausSeparation
    # —— Predict（因果推断 / d-分离 / 干预 / 可辨识性）——
    'GraphToProbView17': 'Predict', 'View17': 'Predict',
    'CausalClassificationBridge': 'Predict', 'DAGBridge': 'Predict',
    'PearlLawRuleBridge': 'Predict', 'T1DegeneracyVerify': 'Predict',
    'KK1NoiseAsymmetry': 'Predict', 'CausalPath': 'Predict',
    'CausalDescendant': 'Predict',
    # —— Loop（闭环 / 收敛 / 世界模型）——
    'DemoEndToEnd': 'Loop', 'WorldModelPipeline': 'Loop',
    'ConvergeToOptimalCounterexample': 'Loop', 'SharedThetaChain': 'Loop',
    'SharedParamGain': 'Loop',
    # —— Error（误差界 / σ）——
    'FirstLayerBound': 'Error', 'LoopBoundReal': 'Error',
    # —— Rules（规则 / 语法）——
    'RuleSyntax': 'Rules',
    # —— Modeling（建模）——
    'T43CounterfactualAbduction': 'Modeling',
}


def candidates():
    v2m = port_v2.v2_index()
    rows = []
    for dp, _, fs in os.walk(port_v2.LEGACY):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            n = f[:-5]
            if n in v2m:
                continue
            info = port_v2.analyze(n)
            if info and not info['unresolved'] and not info['blocked'] :
                rows.append(info)
    rows.sort(key=lambda r: -r['theorems'])
    return rows


def guess_domain(name):
    if name in DOMAIN_HINT:
        return DOMAIN_HINT[name]
    return 'Predict'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--plan', type=int, default=0)
    ap.add_argument('--run', type=int, default=0)
    ap.add_argument('--domain')
    a = ap.parse_args()

    rows = candidates()
    n = a.run or a.plan
    if not n:
        print(f'候选 {len(rows)} 个')
        return

    picked = rows[:n]
    plan = [(r['name'], a.domain or guess_domain(r['name'])) for r in picked]

    print(f'计划迁移 {len(plan)} 个：')
    for name, dom in plan:
        thm = next(r['theorems'] for r in picked if r['name'] == name)
        print(f'  {name:<32} → {dom:<10} {thm:>3} 定理')

    if not a.run:
        return

    print('\n=== 写入 ===')
    written = []
    for name, dom in plan:
        r = port_v2.port_one(name, dom, verify=False)
        if r.get('ok'):
            written.append((name, dom, r['dst']))
            print(f'  [写] {name:<32} → {dom}')
        else:
            print(f'  [跳过] {name}: {r.get("why")}')

    if not written:
        return

    print(f'\n=== 统一验证（{len(written)} 个）===')
    proc = subprocess.run(['lake', 'build', 'FateWorld'], cwd=ROOT,
                          capture_output=True, text=True,
                          encoding='utf-8', errors='replace', timeout=7200)
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0

    # 解析失败模块（形如 error: FateWorld/FateV2/<域>/<模块>.lean:行:列:）
    bad = set()
    for m in re.finditer(r'error: FateWorld/(FateV2/[^\s:]+\.lean)', out):
        bad.add(m.group(1).replace('/', os.sep))

    print(f'1) 构建结果: {"成功" if ok else "失败"}')
    if bad:
        print(f'2) 失败文件 {len(bad)} 个:')
        for b in sorted(bad):
            print(f'   {b}')
        # 回滚失败的那些
        for name, dom, dst in written:
            rel = dst[len(ROOT) + 1:]
            if rel in bad:
                os.remove(dst)
                print(f'   [回滚] {name}')
    else:
        print('2) 无失败文件')

    survivors = [w for w in written
                 if os.path.exists(w[2])]
    print(f'\n净成功 {len(survivors)} / {len(written)}')


if __name__ == '__main__':
    main()
