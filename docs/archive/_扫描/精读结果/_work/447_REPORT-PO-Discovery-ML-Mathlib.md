# Causalean Dependency Audit — PO / Discovery / ML / Mathlib (local)

**Repo:** `CausalSmith` (formerly CausalForge) — https://github.com/Jiyuan-Tan/CausalSmith
**Commit audited:** `47acf19565b6c280f0f515fcf1f11f26324381c6` (HEAD of the blobless clone)
**Method:** blobless clone, no checkout. All file contents read via `git ls-tree -r --name-only HEAD` + `git show HEAD:<path>` (dumped to a scratch tree, then grepped/read locally). The working tree was never checked out.

> **Coverage note.** The promisor remote was intermittently unreachable (`schannel: failed to receive handshake`), so per-blob lazy fetches sometimes failed. I retried until every file was local. **All 977 files in the four clusters were read** — 154 PO + 41 Discovery + 52 ML + 730 Mathlib — with zero unread files remaining. Every count below is over the complete cluster.

---

## File inventory

| Cluster | Files (`.lean`) | Declarations extracted | theorem/lemma | def/abbrev | structure/class/inductive | instance | axiom |
|---|---|---|---|---|---|---|---|
| `Causalean/PO` | **154** | **1416** | 1116 | 224 | 68 | 8 | **0** |
| `Causalean/Discovery` | **41** | **264** | 178 | 78 | 8 | 0 | **0** |
| `Causalean/ML` | **52** | **139** | 101 | 26 | 12 | 0 | **0** |
| `Causalean/Mathlib` | **730** | **3690** | 2906 | 664 | 94 | 26 | **0** |
| **Total (my scope)** | **977** | **5509** | 4301 | 992 | 182 | 34 | **0** |

Repo total at this commit: **12457 files**. My four clusters are 977 of them (7.8%).

### Full file listing — `Causalean/PO` (154 files)

```
PO/Analysis/Quantile.lean                              PO/ID/Exact/LATE.lean
PO/Analysis/Regression.lean                            PO/ID/Exact/MultipleInstrumentIV/{FiniteIndex,Main,POBridge,Population,ResponseTypes}.lean
PO/Assumptions/{Consistency,ConsistencyLemmas,IndepCF}.lean
PO/Bridge/{FiniteCellGFormula,FiniteCellOneDraw,FiniteCellTwoDraw,FiniteCellUStatistic,FromSCM,FromSCMCondIndep,Induce}.lean
PO/Conditioning/{Bundle,CondExpTooling,EventCondExp,EventCondExpBundle}.lean
PO/Core/{Counterfactual,Regime,System,Variable}.lean
PO/ID/Exact/{ATE,ATT,CSDID,DID,Frontdoor,LATE}.lean
PO/ID/Exact/DTR/{Helpers,Induction,Main,Setup,StrongCancellation}.lean
PO/ID/Exact/DynamicLATE/{Bridges,Consistency,Setup,WhenToTreat}.lean
PO/ID/Exact/HeckmanRoy/{Setup,Wald}.lean
PO/ID/Exact/PartialLinear/{Identification,Setup}.lean
PO/ID/Exact/Proximal/{Assumptions,Helpers,Main,Setup}.lean
PO/ID/Exact/QTE/{DistributionalBackdoor,QuantileEffect}.lean
PO/ID/Exact/RDD/{FuzzyRDD,RDDLimits,SharpRDD}.lean
PO/ID/Exact/VariableIntensityIV/{OrderedTreatment,VariableIntensity}.lean
PO/ID/Exact/VariableIntensityIV/VariableIntensity/{Basic,Identification,SpecialCases}.lean
PO/ID/Partial/{Basic,BalkePearl,Frechet,Lee,Manski,Proxy}.lean
PO/ID/Partial/BalkePearl/{Assumptions,ClosedForm,ClosedFormAttainment,IntervalForm,LatentTable,Main,Setup,Sharp}.lean
PO/ID/Partial/BalkePearl/Attainment/{Basic,Lower,Upper}.lean
PO/ID/Partial/BalkePearl/Sharp/{CanonicalModel,Sharpness}.lean
PO/ID/Partial/CriterionSet/{Basic,Consistency}.lean
PO/ID/Partial/Inference/{Basic,ImbensManski,IntervalCI}.lean
PO/ID/Partial/LP/ConicDuality.lean
PO/ID/Partial/Lee/{Assumptions,ControlMean,LatentSupport,Main,MixtureIdentity,PrincipalStrata,Setup,Trim,TrimBound,TrimMean,TrimWeight}.lean
PO/ID/Partial/Manski/{Assumptions,Combined,Helpers,IntervalForm,MIV,MTR,MTS,NonAsp,Setup}.lean
PO/ID/Partial/Proxy/{Assumptions,IntervalForm,Setup,TwoProxy,WBased,ZBased}.lean
PO/ID/Partial/Proxy/Helpers/{BridgeW,BridgeWZ,Common,CondExpQ}.lean
PO/ID/Partial/Proxy/ZBased/ArmChain.lean
PO/ID/Partial/RandomSet/{Aumann,GridTest,Hausdorff,Interval,IntervalCLT,IntervalInference,SetValued,SupportProcess}.lean
PO/ID/Partial/Sensitivity/MSM/*.lean  (32 files: ATE, ATEClosedForm, Bounds, Calibrated, Compatible,
    CompatibleRealization, ControlCutoff, ControlCutoffConstruct, ControlLowerBound, ControlObservedCandidates,
    ControlQuantileBalance, Converse, ConverseObserved, CutoffConstruct, CutoffConstruct/{ConstantCutoff,VariableCutoff},
    CutoffExists, CutoffSelection, Gaussian, GaussianHalfWidth, LowerBound, ObservedCandidates, QuantileBalance,
    Realization, Setup, Sharp)
PO/ID/Partial/SupportFunction/{AffineBall,Basic,Calculus,Interval,Sensitivity}.lean
```

### Full file listing — `Causalean/Discovery` (41 files)

```
Discovery/{InvariantPrediction,LinearDisentanglement,LiNGAM}.lean
Discovery/InvariantPrediction/{Model,Invariance,IdentifiedSet,Soundness,LinearGaussian}.lean
Discovery/InvariantPrediction/Helpers/MechanismFactor.lean
Discovery/InvariantPrediction/LinearGaussian/{Completeness,Model,Regression}.lean
Discovery/InvariantPrediction/LinearGaussian/Helpers/{Invariance,Moments,Residual}.lean
Discovery/LinearDisentanglement/{KeyIdentity,Model,PartialOrderRQ,Rowspan,SigmaSolutions,Uniqueness,
    Uniqueness_Part1,Uniqueness_Part2,Uniqueness_Part3,Uniqueness_Part4,Quantitative,SimultaneousCongruence}.lean
Discovery/LinearDisentanglement/Quantitative/{CompactExclusion,Definitions,Quantitative}.lean
Discovery/LinearDisentanglement/SimultaneousCongruence/{Algebra,Definitions,DefinitionsPairwiseAffine,
    LocalBranch,Main,PairwiseControl,SmallParameter,Stability}.lean
Discovery/LiNGAM/{Identifiability,Kurtosis,LiNGAMKurtosis}.lean
```

### Full file listing — `Causalean/ML` (52 files)

```
ML/{Binary,CausalApplication,Core,Kernel,Lasso,Linear,Margin,NeuralNet,PartitionPredictor,Ridge,Surrogate}.lean
ML/Binary/{FisherConsistency,Logistic,Rate}.lean
ML/CausalApplication/{AIPWExample,Nuisance,RateAssembly,RegressionBridge}.lean
ML/Core/{Bridge,Convex,ERM,Hypothesis,Losses,PopulationTarget,Rate,Risk}.lean
ML/Kernel/{EffectiveDimension,RKHSRademacher,Ridge}.lean
ML/Lasso/{Finite,HighProbability,Optimality,OracleInequality,Rate,SquaredLoss,SubGaussian}.lean
ML/Linear/{ClosedForm,Finite,L2BallRate,L2BallSquaredLoss,Population}.lean
ML/Margin/Rate.lean
ML/NeuralNet/{FeedForward,Layer}.lean
ML/PartitionPredictor/{Ensemble,FinitePartitionPredictor}.lean
ML/Ridge/{ClosedForm,Finite,Population,Rate}.lean
ML/Surrogate/{ClampedSquare,ProperLoss}.lean
```

### Full file listing — `Causalean/Mathlib` (730 files) — subdirectory structure

Top-level subdirectories (file counts), with declaration counts in parentheses:

| Subdir | Files | Decls | What it backfills |
|---|---|---|---|
| `Analysis/` | 354 | 1822 | Chebyshev/Jackson approximation, cube Hölder extension & jet interpolation, interval arithmetic + contour certification, complex argument principle, Fourier, real interpolation, quantization, spectral/SVD |
| `Probability/` | 195 | 970 | Independence & conditional independence (graphoid rules), kernels/condDistrib, Poisson finite-partition theory, Stein-method CLTs (incl. dependency-graph CLT), sub-Gaussian, birthday problem, Hermite/Gaussian, certified numerics (NormalCDF) |
| `MeasureTheory/` | 42 | 150 | Cond-exp tooling, `withDensity` transport/inverse, `rnDeriv` bounds, finite atomic measures, universal measurability of analytic sets |
| `Topology/` | 24 | 67 | Compact exclusion, space-filling (Gray-code/Hilbert) curves, subsequential limits, affine uniform convergence |
| `LinearAlgebra/` | 23 | 146 | Real Cholesky existence/uniqueness, (confluent/stacked) Vandermonde, normal equations, monomial matrices, Perron–Frobenius, symmetric-pencil tensor recovery |
| `Optimization/` | 19 | 112 | Affine sign-cell geometry, KKT (from vendored optlib), rational LP, quadratic saddle, finite knapsack |
| `AlgebraicGeometry/` | 19 | 101 | Polynomial/rational maps, affine-algebraic dimension, polynomial zero locus, rational derivative |
| `InformationTheory/` | 15 | 87 | Entropy, conditional entropy, finite KL & mutual information, Fano, Gaussian KL, density tilt / KL expansion |
| `Algorithms/` | 12 | 132 | Monotone-deque sliding-window correctness, mutation counts, storage bounds |
| `Geometry/` | 5 | 49 | Embedded normal geometry, shape operator, normal bundle |
| `Combinatorics/` | 5 | 40 | Boolean-cube Möbius expansion, Johnson scheme harmonics & Kneser graph |
| `Algebra/` | 4 | 11 | Arithmetic–geometric sums, finite-product moments, antidiagonal count vectors |
| `Data/` | 3 | 3 | List append, Nat choose bounds & multinomial |
| `*.lean` roll-ups | 10 | — | `AlgebraicGeometry, Algorithms, Analysis, Combinatorics, InformationTheory, LinearAlgebra, MeasureTheory, Optimization, Probability, Topology` |

Verbatim roll-up docstrings (evidence of intent):

- `Mathlib/Probability.lean` — *"General probabilistic infrastructure for independence, kernels, Gaussian and Poisson laws, distributional convergence, Stein approximations, and certified calculations. It supplies the measure-theoretic and quantitative tools underlying the library's statistical results."*
- `Mathlib/Analysis.lean` — *"Analytic tools for approximation, convexity, smoothness, matrix perturbation, interval certification, complex root analysis, and Hilbert-space geometry. They provide reusable quantitative estimates for statistical and optimization arguments."*
- `Mathlib/MeasureTheory.lean` — *"Measure-theoretic tools for conditional expectation, densities, partitions, integration, measurable selection, finite supports, and moment restrictions."*
- `Mathlib/Optimization.lean` — *"Finite-dimensional optimization: sign cells of an affine system and their closure, Karush-Kuhn-Tucker conditions for constrained problems, and linear programs over the rationals."*
- `Mathlib/LinearAlgebra.lean` — *"Linear-algebra tools including Cholesky and Vandermonde constructions, normal equations, monomial matrices, positive-matrix spectra, and tensor recovery. They support moment inversion, least squares, and spectral identification."*
- `Mathlib/Topology.lean` — *"Compact-set exclusion, subsequential limits, and affine uniform convergence. These results support stability arguments for estimators and optimization problems."*
- `Mathlib/InformationTheory.lean` — *"Entropy, conditional entropy, finite KL and mutual-information identities, Fano bounds, Gaussian and product calculations, density tilts, and finite chain rules."*
- `Mathlib/Algorithms.lean` — *"Finite algorithms centered on monotone-deque sliding-window calculations, with correctness, mutation-count, and storage guarantees for rolling extrema in discrete data."*
- `Mathlib/Combinatorics.lean` — *"Boolean-cube Möbius identities and the Johnson scheme with its harmonic and Kneser-graph structure."*
- `Mathlib/AlgebraicGeometry.lean` — *"Polynomial and rational maps, rational derivatives, and affine-algebraic dimension tools."*

**Reading of the Mathlib cluster:** it is a **general-purpose Mathlib gap-filler**, not causal-specific. It supplies quantitative/analytic infrastructure (approximation theory, interval arithmetic, concentration, measure-theoretic transport, linear algebra) that upstream Mathlib lacked at the pinned toolchain, plus a few *directly* causal-facing pieces (`Probability/Independence/Conditional` — conditional independence and graphoid rules; `MeasureTheory/ConditionalExpectationTransport`; `LinearAlgebra/Cholesky` used by `Discovery.LinearDisentanglement`).

---

## Declaration inventory

Kind legend: `T` = theorem, `L` = lemma, `S` = structure, `D` = def/abbrev.

### PO — Selected key declarations

| Declaration | file:line | Kind | One-line meaning |
|---|---|---|---|
| `POSystem` | `PO/Core/System.lean:40` | S | Core potential-outcome system: finite variables, value spaces, probability space, jointly measurable `eval : Regime → Ω → ∀ v, X v`. Implements `def:po-system`. |
| `POVar` | `PO/Core/Variable.lean:40` | S | A potential-outcome variable, with `cf`, `factual`, `event`, `cfUnder`. |
| `RegimedVar` | `PO/Core/Variable.lean:299` | S | Variable paired with a regime. |
| `Regime` | `PO/Core/Regime.lean:38` | S | Intervention regime (target/assign pair). |
| `crossWorldEval` | `PO/Core/Counterfactual.lean:39` | D | Cross-world evaluation map (counterfactual comparison). |
| `POSystem.Consistency` | `PO/Assumptions/Consistency.lean:61` | S | Factual consistency: under an applied regime, non-target POs equal factual outcomes. |
| `POSystem.CompositionConsistency` | `PO/Assumptions/Consistency.lean:81` | S | Nested-regime composition (Pearl §7.3 eq. 7.19; Robins recursive substitution). |
| `POSystem.IntermediateAgrees` | `PO/Assumptions/Consistency.lean:48` | D | Pathwise predicate for sequential interventions. |
| `POSystem.IndepCF` | `PO/Assumptions/IndepCF.lean:107` | D | Independence of counterfactual variables. |
| `POSystem.CondIndepCF` | `PO/Assumptions/IndepCF.lean:117` | D | Conditional independence of counterfactual variables. |
| `POSystem.CondIndepCFBundle` | `PO/Conditioning/Bundle.lean:292` | D | Bundled conditional-independence structure. |
| `POBackdoorSystem` | `PO/ID/Exact/ATE.lean:65` | S | Binary-treatment backdoor system; carries `Assumptions` (consistency, unconfoundedness, overlap, integrability). |
| **`ate_backdoor`** | `PO/ID/Exact/ATE.lean:579` | T | **ATE = adjustedATE** under backdoor assumptions. |
| `conditionalMeanOutcome_backdoor` | `PO/ID/Exact/ATE.lean:564` | T | `E[Y(d)|σX] =ᵐ adjustedCE d`. |
| `regression_adjustment` | `PO/ID/Exact/ATE.lean:746` | T | Adjustment functional is the observable outcome regression. |
| `propScore_ne_of_overlap` | `PO/ID/Exact/ATE.lean:363` | L | Overlap gives per-arm nonvanishing propensity. |
| `ATTAssumptions` | `PO/ID/Exact/ATT.lean:100` | S | ATT identifying bundle. |
| **`ATT_eq_adjustedATT`** | `PO/ID/Exact/ATT.lean:425` | T | ATT equals the adjusted (regression) ATT functional. |
| `adjustedATT_eq_aipwForm` | `PO/ID/Exact/ATT.lean:496` | T | Adjusted ATT equals its AIPW (doubly-robust) representation. |
| `PODIDSystem` | `PO/ID/Exact/DID.lean:46` | S | Two-period DID system; field `parallelTrends` at line 157, `noAnticipation` at 154. |
| **`att_did`** | `PO/ID/Exact/DID.lean:192` | T | **ATT = (treated mean change) − (control mean change).** |
| `POCSDIDSystem` | `PO/ID/Exact/CSDID.lean:60` | S | Callaway–Sant'Anna staggered-adoption DID system. |
| **`att_csdid`** | `PO/ID/Exact/CSDID.lean:495` | T | **ATT(g,t) = E[Y_t−Y_{g−1}‖G_g] − E[Y_t−Y_{g−1}‖C].** |
| `neverTreatedEvent` | `PO/ID/Exact/CSDID.lean:289` | D | The never-treated comparison group. |
| `POFrontdoorSystem` | `PO/ID/Exact/Frontdoor.lean:60` | S | Frontdoor system with mediator. |
| **`ate_frontdoor`** | `PO/ID/Exact/Frontdoor.lean:753` | T | **ATE = frontdoorATE.** |
| `EofY_eq_frontdoorTerm` | `PO/ID/Exact/Frontdoor.lean:561` | T | Per-arm frontdoor functional identity. |
| `POIVSystem` | `PO/ID/Exact/LATE.lean:48` | S | Binary IV subsystem (`def:po-iv-system`): instrument `Z`, treatment `D`, outcome `Y`. |
| `complierEvent` | `PO/ID/Exact/LATE.lean:120` | D | `{D(1)=1, D(0)=0}` — complier stratum. |
| `pointwise_monotonicity` | `PO/ID/Exact/LATE.lean:460` | T | Instrument-induced outcome change vanishes off compliers (a.s.). |
| **`late_wald`** | `PO/ID/Exact/LATE.lean:499` | T | **Wald ratio = LATE** (`prop:po-late`). |
| `PODynLATESystem` | `PO/ID/Exact/DynamicLATE/Setup.lean:65` | S | Dynamic (when-to-treat) LATE system. |
| `mixtureLATE_wald` | `PO/ID/Exact/DynamicLATE/WhenToTreat.lean:374` | T | Mixture-LATE Wald identification. |
| `cMixtureLATE_wald` | `PO/ID/Exact/DynamicLATE/WhenToTreat.lean:509` | T | Conditional mixture-LATE Wald identification. |
| `POHeckmanRoySystem` | `PO/ID/Exact/HeckmanRoy/Setup.lean:60` | S | Heckman–Roy selection model. |
| `intervalComplierEvent` | `PO/ID/Exact/HeckmanRoy/Setup.lean:152` | D | Interval-valued complier stratum. |
| `complier_measure` | `PO/ID/Exact/HeckmanRoy/Wald.lean:111` | L | Complier probability identity. |
| `POMultipleIVSystem` | `PO/ID/Exact/MultipleInstrumentIV/POBridge.lean:78` | S | Multiple-instrument IV system. |
| `PopulationBridge` | `PO/ID/Exact/MultipleInstrumentIV/ResponseTypes.lean:139` | S | Response-type population bridge (`FiniteIndex` scores). |
| `centeredScoreIVPopulationBridge_eq_positiveResponseTypeAverage_of_signAligned` | `PO/ID/Exact/MultipleInstrumentIV/Main.lean:96` | T | Centered-score IV ratio is a convex response-type average (sign-aligned). |
| `POSystem.ofSCM_consistency` | `PO/Bridge/FromSCM.lean:421` | T | Consistency is automatic for PO systems induced from an SCM. |
| `POSystem.ofSCM_compositionConsistency` | `PO/Bridge/FromSCM.lean:464` | T | Same for composition consistency. |
| `ofSCM_condIndepCF_of_dSep` | `PO/Bridge/FromSCMCondIndep.lean:122` | T | d-separation ⇒ conditional independence of counterfactuals (bridges to `Causalean.Graph.DSep`). |
| `restrict_consistency` | `PO/Bridge/Induce.lean:206` | T | Consistency preserved under system restriction. |
| `POLongitudinalPathSystem` | `PO/ID/Exact/DTR/Setup.lean:83` | S | Dynamic treatment regime / longitudinal path system. |
| `treatmentPath_backdoor` | `PO/ID/Exact/DTR/Main.lean:129` | T | Backdoor identification for treatment paths (g-formula style). |
| `conditionalPath_backdoor` | `PO/ID/Exact/DTR/Main.lean:104` | T | Conditional path backdoor identification. |
| `POProximalSystem` | `PO/ID/Exact/Proximal/Setup.lean:36` | S | Proximal causal inference system (negative-control proxies). |
| **`ate_proximal`** | `PO/ID/Exact/Proximal/Main.lean:484` | T | **ATE identified by the proximal (bridge-function) formula.** |
| `POSharpRDDSystem` | `PO/ID/Exact/RDD/SharpRDD.lean:37` | S | Sharp regression discontinuity design. |
| **`rdd_identification`** | `PO/ID/Exact/RDD/SharpRDD.lean:365` | T | **τ_RDD(c) = lim_{x↓c} ν(x) − lim_{x↑c} ν(x)** (`prop:po-sharp-rdd`). |
| `POFuzzyRDDSystem` | `PO/ID/Exact/RDD/FuzzyRDD.lean:68` | S | Fuzzy RDD design. |
| `frd_identification` | `PO/ID/Exact/RDD/FuzzyRDD.lean:674` | T | Fuzzy-RDD Wald identification. |
| `tau_late_identification_of_globalMonotonicity` | `PO/ID/Exact/RDD/FuzzyRDD.lean:738` | T | Fuzzy-RDD LATE under global monotonicity. |
| `qte_backdoor` | `PO/ID/Exact/QTE/QuantileEffect.lean:136` | T | Quantile treatment effect under backdoor. |
| `cfUnderLaw_eq_ipwLaw` | `PO/ID/Exact/QTE/DistributionalBackdoor.lean:466` | T | Counterfactual law equals IPW law (distributional identification). |
| `POPartialLinearSystem` / `POPartialLinearModel` | `PO/ID/Exact/PartialLinear/Setup.lean:57,210` | S | Partially linear model. |
| `VariableIntensityIVSystem` | `PO/ID/Exact/VariableIntensityIV/VariableIntensity/Basic.lean:49` | S | Variable-intensity IV (ordered treatment). |
| `POManskiIVSystem` | `PO/ID/Partial/Manski/Setup.lean:42` | S | Manski worst-case IV system. |
| `POManskiIVSystem.BaseAssumptions` | `PO/ID/Partial/Manski/Assumptions.lean:45` | S | Bounded outcome, integrability. |
| `MeanIndep` | `PO/ID/Partial/Manski/Assumptions.lean:119` | S | Mean independence of the instrument. |
| `MTR` / `MTS` / `MIV` | `PO/ID/Partial/Manski/Assumptions.lean:127,133,143` | S | Monotone treatment response / selection / IV assumptions. |
| **`manski_bounds_ATE`** | `PO/ID/Partial/Manski/NonAsp.lean:81` | T | **Manski no-assumption ATE bounds from two instrument strata.** |
| `manski_bounds_ATE_ciSup` | `PO/ID/Partial/Manski/NonAsp.lean:138` | T | Supremum-form Manski bounds. |
| `manski_ATE_mem_Icc` | `PO/ID/Partial/Manski/IntervalForm.lean:50` | T | ATE lies in the Manski interval. |
| `mtr_bounds_ATE` | `PO/ID/Partial/Manski/MTR.lean:264` | T | MTR-conditioned bounds. |
| `mts_bounds_ATE` | `PO/ID/Partial/Manski/MTS.lean:330` | T | MTS-conditioned bounds. |
| `miv_bounds_ATE` | `PO/ID/Partial/Manski/MIV.lean:379` | T | MIV-conditioned bounds. |
| `mtr_mts_bounds_ATE` / `mtr_miv_bounds_ATE` | `PO/ID/Partial/Manski/Combined.lean:48,69` | T | Combined-assumption bounds. |
| `POBalkePearlSystem` | `PO/ID/Partial/BalkePearl/Setup.lean:44` | S | Balke–Pearl IV system (latent response-type table). |
| `BPFeasible` | `PO/ID/Partial/BalkePearl/Main.lean:59` | S | Feasibility of a latent table for the BP linear program. |
| `BPIdentifiedInterval` | `PO/ID/Partial/BalkePearl/Main.lean:80` | D | Sharp identified interval = LP-objective range over feasible tables. |
| `ATE_mem_BPIdentifiedInterval` | `PO/ID/Partial/BalkePearl/Main.lean:108` | T | Necessity: true ATE lies in the BP interval. |
| `bpLower` / `bpUpper` | `PO/ID/Partial/BalkePearl/ClosedForm.lean` | D | Closed-form BP endpoints. |
| `bpLower_le_BPObjective` / `BPObjective_le_bpUpper` | `PO/ID/Partial/BalkePearl/ClosedForm.lean:197,203` | T | Closed forms bracket the LP objective. |
| **`balkePearl_sharp`** | `PO/ID/Partial/BalkePearl/Sharp/Sharpness.lean:453` | T | **Sharpness/attainment: every feasible latent table is realised by some PO model with the same observed cells and ATE = LP objective.** |
| `balkePearl_sharp_of_mem` | `PO/ID/Partial/BalkePearl/Sharp/Sharpness.lean:473` | T | Every value in the BP interval is the ATE of some BP-feasible model. |
| `canonical_baseAssumptions` | `PO/ID/Partial/BalkePearl/Sharp/Sharpness.lean:288` | T | The canonical witness model satisfies BP base assumptions. |
| `POLeeSystem` | `PO/ID/Partial/Lee/Setup.lean:50` | S | Lee (2009) trimming-bounds system. |
| `Lee.BaseAssumptions` | `PO/ID/Partial/Lee/Assumptions.lean:56` | S | Lee base assumptions (consistency, distributional). |
| `POLeeSystem` trimming lemmas | `PO/ID/Partial/Lee/{Trim,TrimBound,TrimMean,TrimWeight,MixtureIdentity,PrincipalStrata}.lean` | T/L | Lee trimming bounds machinery. |
| `PartialID.mem_identifiedSet` | `PO/ID/Partial/Basic.lean` | T | Membership in the identified set (shared partial-ID API). |
| `ate_mem_Icc_calib_of_msm` | `PO/ID/Partial/Sensitivity/MSM/ATE.lean:148` | T | MSM sensitivity bounds on the ATE. |
| `msmUpper_eq` / `msmLower_eq` | `PO/ID/Partial/Sensitivity/MSM/Bounds.lean:205,373` | T | MSM bound equalities. |
| `imbensManski_pointwise_coverage` | `PO/ID/Partial/Inference/ImbensManski.lean:197` | T | Imbens–Manski pointwise CI coverage for partially identified ATE. |
| `POBalkePearlSystem` etc. | — | — | (See above.) |

Sub-cluster declaration counts inside PO: `ID/Exact` = 563, `ID/Partial` = 620, rest (Core/Assumptions/Bridge/Conditioning/Analysis) = 233.

### Discovery — Key declarations

| Declaration | file:line | Kind | One-line meaning |
|---|---|---|---|
| `EnvFamily` | `Discovery/InvariantPrediction/Model.lean:64` | S | ICP model: `Fintype`-indexed family of SCMs sharing target mechanism/parents/noise law. |
| `EnvFamily.Invariant` | `Discovery/InvariantPrediction/Invariance.lean:84` | D | `S` invariant when `Y ⊥⊥ E ‖ X_S` in every environment. |
| `mechanism_invariant` | `Discovery/InvariantPrediction/Invariance.lean:220` | T | Observed parents `PA(Y)` are always an invariant set. |
| `invariantSets` | `Discovery/InvariantPrediction/IdentifiedSet.lean:39` | D | All invariant predictor sets. |
| `idSet` | `Discovery/InvariantPrediction/IdentifiedSet.lean:49` | D | `S(E) = ⋂{invariant S}`. |
| `paObs_mem_invariantSets` | `Discovery/InvariantPrediction/IdentifiedSet.lean:60` | T | Parent set is invariant. |
| **`icp_sound`** | `Discovery/InvariantPrediction/Soundness.lean:45` | T | **`S(E) ⊆ PA(Y)`: ICP never selects a non-parent.** |
| `EnvFamily` (LinearGaussian) | `Discovery/InvariantPrediction/LinearGaussian/Model.lean:227` | S | Random-variable/regression ICP API. |
| `ObsSEM` | `Discovery/InvariantPrediction/LinearGaussian/Model.lean:101` | S | Observational linear-Gaussian SEM. |
| `HasShiftedSingleInterventions` | `Discovery/InvariantPrediction/LinearGaussian/Completeness.lean:97` | D | One single-node do-intervention shifting each predictor off its mean. |
| `icp_sound_linearGaussian_of_exogeneity` | `Discovery/InvariantPrediction/LinearGaussian/Completeness.lean:118` | T | Soundness in the linear-Gaussian API. |
| **`icp_complete_linearGaussian_of_exogeneity`** | `Discovery/InvariantPrediction/LinearGaussian/Completeness.lean:303` | T | **`identifiedSet = paY` — Theorem 2(i) specialization.** |
| `Solution` | `Discovery/LinearDisentanglement/Model.lean:79` | S | Linear disentanglement solution: latent SEM + full-rank mixing `X = G Z`, one perfect single-node intervention per context. |
| `Theta0` / `Theta` | `Discovery/LinearDisentanglement/Model.lean:117,123` | D | Observational / interventional precision matrices `Θ_k = Hᵀ Bₖᵀ Bₖ H`. |
| `InSG` | `Discovery/LinearDisentanglement/Model.lean:129` | D | Order-preserving latent relabelings `S(𝒢)`. |
| `permMat` | `Discovery/LinearDisentanglement/Model.lean:66` | D | Permutation matrix. |
| `key_identity` | `Discovery/LinearDisentanglement/KeyIdentity.lean:50` | T | Rank-one precision-difference identity. |
| `rowspan_inclusion_a/b` | `Discovery/LinearDisentanglement/Rowspan.lean:226,360` | T | Lemma 1: precision differences ↔ latent graph rowspans. |
| `rowspan_inclusion_c_of_ancestor_closed` | `Discovery/LinearDisentanglement/Rowspan.lean:571` | T | Ancestor-closed rowspan inclusion. |
| `sigma_solutions` | `Discovery/LinearDisentanglement/SigmaSolutions.lean:154` | T | (⊇) direction: every `σ ∈ S(𝒢)` yields a solution with the same precision matrices. |
| `porq_exists` / `porq_unique` | `Discovery/LinearDisentanglement/PartialOrderRQ.lean:461,520` | T | Partial-order RQ decomposition existence/uniqueness. |
| `exists_orderPerm` | `Discovery/LinearDisentanglement/Uniqueness_Part3.lean:594` | T | Orthogonal-correctness collapse to an order-preserving permutation. |
| **`disentanglement_uniqueness_up_to_signed_scaling_of_nondegenerate`** | `Discovery/LinearDisentanglement/Uniqueness_Part4.lean:57` | T | **Main uniqueness: two solutions with equal `{Θ_k}` differ by an order-preserving relabeling + nonzero signed scalings.** |
| `exists_collinear_simultaneous_congruence_ambiguity` | `Discovery/LinearDisentanglement/SimultaneousCongruence/Main.lean:38` | T | Non-uniqueness when two diagonal-shift coordinates are affinely collinear. |
| `exists_interior_collinear_ambiguity_example` | `Discovery/LinearDisentanglement/SimultaneousCongruence/Main.lean:82` | T | Concrete interior example. |
| `opNorm_sub_le_of_approximate_simultaneous_congruence` | `Discovery/LinearDisentanglement/Quantitative/Quantitative.lean:475` | T | Explicit `‖B − B₀‖ ≤ C·ε` perturbation bound. |
| `opNorm_sub_le_of_pairwise_affine` | `Discovery/LinearDisentanglement/SimultaneousCongruence/Stability.lean:151` | T | Stability under pairwise-affine perturbations. |
| `exists_small_admissible_parameter` | `Discovery/LinearDisentanglement/SimultaneousCongruence/SmallParameter.lean:213` | T | Existence of a small admissible deformation parameter. |
| `exists_sqMatrix_uniformExclusionTolerance` | `Discovery/LinearDisentanglement/Quantitative/CompactExclusion.lean:107` | T | Uniform exclusion tolerance over a compact family. |
| `cross_fourth_cumulant_eq_sum` | `Discovery/LiNGAM/Kurtosis.lean:56` | T | Fourth cross-cumulant of two linear mixtures of independent sources. |
| `colSupport_of_kurtosis` | `Discovery/LiNGAM/Kurtosis.lean:628` | T | Two independent same-sign-kurtotic mixtures cannot both load on the same source. |
| `lingam_identifiable` | `Discovery/LiNGAM/Identifiability.lean:47` | T | `I − B'` = row-permuted/signed-scaled `I − B` + acyclicity ⇒ `B = B'`. |
| `ica_genPerm_relation` | `Discovery/LiNGAM/LiNGAMKurtosis.lean:42` | T | Two unmixing matrices differ by a permutation and nonzero scaling. |
| **`lingam_identifiability_kurtosis`** | `Discovery/LiNGAM/LiNGAMKurtosis.lean:92` | T | **Main LiNGAM identification under same-sign kurtosis.** |

### ML — Key declarations

| Declaration | file:line | Kind | One-line meaning |
|---|---|---|---|
| `Predictor` / `HypothesisClass` / `FeatureMap` | `ML/Core/Hypothesis.lean:34,43,53` | S | Parametrized predictor, hypothesis class, feature map. |
| `Loss` | `ML/Core/Risk.lean:31` | D | Loss type alias. |
| `IsERMP` / `IsApproxERMP` / `RegularizedERM` / `IsERM` | `ML/Core/ERM.lean:32,39,50,63` | S | ERM-minimizer predicates (parametric + extensional). |
| `IsPopulationRiskMinimizer` | `ML/Core/ERM.lean:79` | S | Population risk minimizer. |
| `isERMP_to_extensional` | `ML/Core/Bridge.lean:40` | T | Parametric ↔ extensional ERM bridge. |
| `populationTarget_pushforward` | `ML/Core/Bridge.lean:61` | T | Population target pushforward. |
| `IsResidualOrthogonal` | `ML/Core/PopulationTarget.lean:58` | D | Residual-orthogonality moment condition. |
| `square_loss_population_target_of_isResidualOrthogonal` | `ML/Core/PopulationTarget.lean:72` | T | Squared-loss population target = regression function under residual orthogonality. |
| `AchievesL2Rate` | `ML/Core/Rate.lean:191` | D | `L²` rate predicate. |
| `olsCoef_normalEq` / `olsCoef_unique` | `ML/Linear/ClosedForm.lean:123,131` | T | OLS normal equations + uniqueness. |
| `bestLinearPredictor_minimizes_populationRisk` | `ML/Linear/Population.lean:41` | T | Population OLS minimizes population risk. |
| `rademacherComplexity_l2_ball_le` | `ML/Linear/L2BallRate.lean:35` | T | L²-ball Rademacher bound. |
| `l2Ball_erm_excess_rate` | `ML/Linear/L2BallRate.lean:95` | T | L²-ball ERM excess-rate bound. |
| `l2Ball_erm_squaredLoss_excess_rate` | `ML/Linear/L2BallSquaredLoss.lean:58` | T | Squared-loss variant. |
| `ridgeGram_posDef` | `ML/Ridge/ClosedForm.lean:44` | T | `XᵀX + λI` positive definite for `λ > 0`. |
| `ridgeCoef_normalEq` / `ridgeCoef_unique` | `ML/Ridge/ClosedForm.lean:58,74` | T | Ridge normal equations + uniqueness (no rank condition on `X`). |
| `populationRidge_minimizes` | `ML/Ridge/Population.lean:56` | T | Population ridge minimizer. |
| **`ridge_achievesL2Rate`** | `ML/Ridge/Rate.lean:797` | T | **Sample ridge → population ridge in `L²(P)` at rate `n^{-1/2}` under finite 4th moments.** |
| `softThreshold_isMinOn` | `ML/Lasso/Optimality.lean:26` | T | Scalar soft-thresholding optimality. |
| `RestrictedEigenvalue` | `ML/Lasso/OracleInequality.lean:104` | D | Restricted-eigenvalue condition. |
| `IsLassoMinimizer` | `ML/Lasso/OracleInequality.lean:75` | D | Exact normalized Lasso minimizer predicate. |
| **`lasso_oracle_inequality`** | `ML/Lasso/OracleInequality.lean:342` | T | **`‖β̂−β*‖ ≤ 3√s λ/κ`, `‖·‖₁ ≤ 12sλ/κ`, prediction error `≤ 9sλ²/κ`.** |
| `exists_lassoMinimizer` | `ML/Lasso/OracleInequality.lean:285` | T | Lasso minimizer exists (coercivity). |
| `lasso_oracle_inequality_of_subgaussian` | `ML/Lasso/HighProbability.lean:119` | T | Sub-Gaussian high-probability oracle inequality. |
| `exists_measurable_lassoMinimizer` | `ML/Lasso/HighProbability.lean:32` | T | Borel-measurable Lasso response rule. |
| `rademacherComplexity_l1_ball_le` | `ML/Lasso/Rate.lean:37` | T | L¹-ball Rademacher bound `Xinf·W·√(2 log 2d)/√n`. |
| `lasso_erm_excess_rate` | `ML/Lasso/Rate.lean:88` | T | L¹-ball ERM excess-rate bound. |
| `lasso_erm_squaredLoss_excess_rate` | `ML/Lasso/SquaredLoss.lean:66` | T | Squared-loss variant. |
| `lasso_score_event_of_subgaussian` | `ML/Lasso/SubGaussian.lean:110` | T | Sub-Gaussian score calibration event. |
| `representer_theorem` | `ML/Kernel/Ridge.lean:40` | T | Kernel-ridge representer theorem. |
| `effectiveDimension` | `ML/Kernel/EffectiveDimension.lean:56` | D | `N(λ) = Σ' μᵢ/(μᵢ+λ)`. |
| `effectiveDimension_le_trace_div` / `_le_card` / `_antitone` | `ML/Kernel/EffectiveDimension.lean:95,104,117` | T | Structural bounds on effective dimension. |
| `empiricalRademacherComplexity_innerBall_le` | `ML/Kernel/RKHSRademacher.lean:453` | T | Hilbert-space linear Rademacher bound `κr/√n`. |
| **`rkhs_ball_empiricalRademacher_le`** | `ML/Kernel/RKHSRademacher.lean:478` | T | **RKHS-ball Rademacher complexity `≤ κ·r/√n`.** |
| `convexOn_logisticScoreLoss` / `logistic_exists_minimizer_on_compact` | `ML/Binary/Logistic.lean:69,138` | T | Logistic loss convexity + compact minimizer existence. |
| `bernoulliCE_isMinOn` | `ML/Binary/FisherConsistency.lean:36` | T | Bernoulli cross-entropy Fisher consistency. |
| `regLogistic_achievesL2Rate` | `ML/Binary/Rate.lean:482` | T | Root-n rate for `L²`-regularized logistic M-estimator. |
| `margin_erm_surrogate_excess_rate` | `ML/Margin/Rate.lean:41` | T | Margin-surrogate ERM excess-rate bound. |
| `properLoss_population_risk_le` | `ML/Surrogate/ProperLoss.lean:67` | T | True conditional probability minimizes population risk. |
| `properLoss_population_minimizer_recovers_eta` | `ML/Surrogate/ProperLoss.lean:86` | T | Strict properness ⇒ minimizer recovers `η` a.e. |
| `lipschitzAt0_clampedSq` | `ML/Surrogate/ClampedSquare.lean:66` | T | Clamped square is `2c`-Lipschitz and vanishes at 0. |
| `DenseLayer.eval_lipschitz` / `evalLayers_lipschitz` | `ML/NeuralNet/FeedForward.lean:50,125` | T | Layer / network Lipschitz bounds by constant multiplication. |
| `FinitePartitionPredictor.eval_eqOn_cell` | `ML/PartitionPredictor/FinitePartitionPredictor.lean:44` | T | Piecewise-constant on cells. |
| `PartitionEnsemble.eval_mem_Icc` | `ML/PartitionPredictor/Ensemble.lean:45` | T | Ensemble range preservation. |
| `isResidualOrthogonal_of_condExp` / `condExp_of_isResidualOrthogonal` | `ML/CausalApplication/RegressionBridge.lean:53,129` | T | Full equivalence: residual orthogonality ⟺ conditional mean. |
| `response_condExp_ae_eq_of_isResidualOrthogonal` | `ML/CausalApplication/Nuisance.lean:38` | T | Nuisance identification for AIPW. |
| `aipw_mlNuisance_meanZero_transport_of_exact_nuisances` | `ML/CausalApplication/AIPWExample.lean:44` | T | Exact nuisance equalities ⇒ ATE mean-zero identification. |
| **`dml_rate_conditions_of_quarter_rates`** | `ML/CausalApplication/RateAssembly.lean:51` | T | **Abstract `o_p(n^{-1/4})` errors ⇒ DML's three nuisance-rate conditions.** |

### Mathlib — Representative declarations (indicative, not exhaustive)

| Declaration area | file:line | Kind | One-line meaning |
|---|---|---|---|
| `mobius_expansion` | `Mathlib/Combinatorics/BooleanCubeMobius.lean` | T | Normalized Boolean-cube Möbius/inclusion–exclusion recovery. |
| `orthogonal_upperTri_pos_diag_eq_one` | `Mathlib/LinearAlgebra/Cholesky.lean` | T | Uniqueness core of real Cholesky. |
| Cholesky existence | `Mathlib/LinearAlgebra/Cholesky.lean` | T | Every real SPD matrix has a unique `UᵀU` with `U` upper-triangular, positive diagonal. |
| Fano inequality | `Mathlib/InformationTheory/Fano.lean` | T | Cover–Thomas Thm 2.10.1 for finite alphabets. |
| `cdf_tendsto_of_charFun_tendsto` | `Mathlib/Probability/SteinMethod/CLT.lean` | T | Char-function convergence ⇒ Gaussian CDF convergence. |
| Dep-graph CLT | `Mathlib/Probability/SteinMethod/{DepGraphCLT,StandardizedDepGraphCLT}.lean` | T | Dependency-graph CLT via Stein bounds. |
| Sub-Gaussian finite max | `Mathlib/Probability/SubGaussian/Tail.lean` | T | Tail of a finite max ≤ sum of tails, no independence needed. |
| Conditional independence graphoid rules | `Mathlib/Probability/Independence/Conditional.lean` | T | Weak union, contraction, and (under a positivity hypothesis) intersection. |
| Cond-exp transport | `Mathlib/MeasureTheory/ConditionalExpectationTransport.lean` | T | Cond-exp under measure/σ-algebra changes. |
| `withDensity` transport/inverse | `Mathlib/MeasureTheory/{WithDensityTransport,WithDensityInverse}.lean` | T | Density-change calculus. |
| KKT (from vendored `optlib`) | `Mathlib/Optimization/KKT.lean` | T | First-order KKT necessary conditions on ℝⁿ. |
| Rational LP | `Mathlib/Optimization/RationalLP.lean` | T | Linear programs over the rationals. |
| Compact exclusion | `Mathlib/Topology/CompactExclusion.lean` | T | Positive residual margin away from the only zero; uniform family version. |
| Gray-code / space-filling curve | `Mathlib/Topology/SpaceFillingCurve/*.lean` (20 files) | T | Traversal, cube cover, proximity, bijection. |
| Jackson / Chebyshev approximation | `Mathlib/Analysis/Approximation/Chebyshev/*.lean` (72 files) | T | Polynomial/trig approximation with quantitative error bounds. |
| Cube Hölder extension | `Mathlib/Analysis/Calculus/CubeExtension/*.lean` (57 files) | T | Jet-level Hölder completion and controlled global extension. |
| Interval arithmetic + contour certification | `Mathlib/Analysis/IntervalArithmetic/*.lean` (23 files) | T/D | Rigorous interval bounds; certified complex contour evaluation. |
| Perron–Frobenius (finite) | `Mathlib/LinearAlgebra/PerronFrobenius/Finite/*.lean` | T | Positive-matrix spectra. |
| Symmetric-pencil tensor recovery | `Mathlib/LinearAlgebra/Tensor/SymmetricPencil/*.lean` | T | Spectral matching and recovery. |

---

## Axiom/sorry audit

### Exact commands used

Because the clone is blobless and `git grep` triggers lazy fetches, I materialized every blob to a scratch tree first and then grepped locally. The commands were:

```powershell
# 1. Materialize every blob (blobless clone; NO checkout)
$files = git -C $repo ls-tree -r --name-only HEAD | Where-Object {$_ -like "Causalean/PO/*" -or ... }
foreach($f in $files){ git -C $repo show "HEAD:$f" | Out-File -Encoding utf8 (Join-Path $dst ($f -replace '/','\')) }

# 2. Audit (per cluster)
Get-ChildItem -Recurse -File ".\src\Causalean\<CLUSTER>" -Filter *.lean |
  Where-Object {$_.Length -gt 0} | Select-String -Pattern 'sorry' -CaseSensitive:$false
Get-ChildItem -Recurse -File ".\src\Causalean\<CLUSTER>" -Filter *.lean |
  Where-Object {$_.Length -gt 0} | Select-String -Pattern '^\s*(noncomputable\s+)?(private\s+)?axiom\b'
Get-ChildItem -Recurse -File ".\src\Causalean\<CLUSTER>" -Filter *.lean |
  Where-Object {$_.Length -gt 0} | Select-String -Pattern 'native_decide'
Get-ChildItem -Recurse -File ".\src\Causalean\<CLUSTER>" -Filter *.lean |
  Where-Object {$_.Length -gt 0} | Select-String -Pattern '\badmit\b'
```

### Exact results

| Cluster | Files scanned | `sorry` | `axiom` declaration | `native_decide` | `admit` |
|---|---|---|---|---|---|
| `Causalean/PO` | 154 | **0** | **0** | **0** | 1 (prose) |
| `Causalean/Discovery` | 41 | **0** | **0** | **0** | 0 |
| `Causalean/ML` | 52 | **0** | **0** | **0** | 1 (prose) |
| `Causalean/Mathlib` | 730 | **0** | **0** | **0** | 2 (prose) |
| **Total** | **977** | **0** | **0** | **0** | **4 (all English prose)** |

### Context of every residual textual hit

`axiom` appears **10 times as an English word inside docstrings**, and **never as a declaration keyword** — 9 in PO, 1 in Mathlib:

```
PO/ID/Exact/MultipleInstrumentIV/ResponseTypes.lean:350 : support order.  This is an axiom field, not a derived fact. -/
PO/ID/Exact/Proximal/Assumptions.lean:66               : /-- Consistency axiom for the ambient PO system. -/
PO/ID/Partial/BalkePearl/Assumptions.lean:68           : potential-outcome consistency axiom for arbitrary regimes. -/
PO/ID/Partial/Lee/Assumptions.lean:11                  : * `consistency` -- the standard PO consistency axiom;
PO/ID/Partial/Lee/Assumptions.lean:36                  : The structure `BaseAssumptions` stores the consistency axiom, distributional
PO/ID/Partial/Lee/Assumptions.lean:57                  : /-- The PO system satisfies the consistency axiom. -/
PO/ID/Partial/Proxy/Assumptions.lean:93                : /-- Consistency axiom for the ambient PO system. -/
PO/ID/Partial/Proxy/Assumptions.lean:187               : /-- Consistency axiom for the ambient PO system. -/
PO/ID/Partial/Proxy/Assumptions.lean:291               : /-- Consistency axiom for the ambient PO system. -/
Mathlib/Probability/Independence/Conditional/DensityIntersection/Main.lean:8 :
    This module proves the measure-level intersection axiom for the four canonical coordinate maps.
```

Note these describe *causal modelling assumptions* stored as **structure fields** (e.g. `Consistency.factual`, `BaseAssumptions.consistency`), which is the correct Lean encoding — they are hypotheses, not trusted axioms.

`admit` appears 4 times, always as the plain English verb:

```
PO/Bridge/FiniteCellTwoDraw.lean:8     : Independent observations from the induced observed law admit pair-kernel
ML/Lasso/HighProbability.lean:28      : /-- [Exact Lasso solutions admit a Borel measurable response rule](goal) for
Mathlib/Analysis/Calculus/CubeExtension/ReflectionCoefficients.lean:18 : ... admit weights all ...
Mathlib/MeasureTheory/MomentSliceSupport.lean:29 : ... always admit a nonzero perturbation ...
```

Additionally verified (same command shape):

| Cluster | `unsafe` | `partial def` | `opaque` |
|---|---|---|---|
| `Causalean/PO` | 0 | 0 | 0 |
| `Causalean/Discovery` | 0 | 0 | 0 |
| `Causalean/ML` | 0 | 0 | 0 |
| `Causalean/Mathlib` | 0 | 0 | 0 |

**Conclusion:** the PO, Discovery, ML and local-Mathlib clusters are **entirely free of `sorry`, `axiom` declarations, `native_decide`, `admit`, `unsafe`, `partial def`, and `opaque`**. All 4301 theorems/lemmas are closed proofs at this commit.

---

## Verbatim key statements

### PO

**1. `ate_backdoor` — `PO/ID/Exact/ATE.lean:572-580`**
```lean
/-- **Integrated backdoor ATE identification.** In [a binary-treatment backdoor
system](hyp:S), under [the backdoor
identification assumptions — consistency, unconfoundedness, two-sided
overlap, and integrable potential outcomes](hyp:hA), [the average treatment
effect equals the adjusted-outcome functional obtained by averaging the
two arm-specific conditional-mean backdoor identities over the covariate
distribution](goal). -/
theorem ate_backdoor [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hA : S.Assumptions) : S.ATE = S.adjustedATE := by
```

**2. `att_did` — `PO/ID/Exact/DID.lean:186-197`**
```lean
/-- In [a two-period DID system](hyp:S), under [the identifying assumptions —
consistency, no-anticipation,
parallel trends, and positive-probability, integrable treatment and control
groups](hyp:hA), [the average treatment effect on the treated equals the
difference between the treated group's mean pre-to-post outcome change and
the control group's mean pre-to-post outcome change](goal). -/
theorem att_did (hA : S.Assumptions) :
    S.ATT
      = normalizedRestrictedIntegral P.μ (S.dEvent true)
          (fun ω => S.factualY₁ ω - S.factualY₀ ω)
        - normalizedRestrictedIntegral P.μ (S.dEvent false)
            (fun ω => S.factualY₁ ω - S.factualY₀ ω) := by
```
The `parallelTrends` field it consumes (`DID.lean:155-161`):
```lean
  /-- Parallel trends: the average untreated change from the pre- to the
  post-period is the same in the treated group as in the control group. -/
  parallelTrends :
    normalizedRestrictedIntegral P.μ (S.dEvent true)
        (fun ω => S.Y1ofD false ω - S.Y0ofD false ω)
      = normalizedRestrictedIntegral P.μ (S.dEvent false)
          (fun ω => S.Y1ofD false ω - S.Y0ofD false ω)
```

**3. `att_csdid` (Callaway–Sant'Anna) — `PO/ID/Exact/CSDID.lean:483-501`**
```lean
/-- **Callaway--Sant'Anna group-time DID identification.** In [a staggered-adoption
DID system](hyp:S), [the group-time average treatment effect on the treated equals the
cohort's mean outcome change minus the corresponding never-treated mean change](goal)
under [irreversible adoption, consistency, no anticipation, group-time parallel trends,
positive cohort and comparison-group probabilities, and integrable potential
outcomes](hyp:hA), for
[the selected treatment cohort](hyp:g) [which is not the initial period](hyp:hg) and
[the selected outcome period](hyp:t) [which is no earlier than treatment](hyp:hgt):

    ATT(g, t) = E[Y_t − Y_{g−1} | G_g] − E[Y_t − Y_{g−1} | C].

Mirrors `PODIDSystem.att_did` line by line. -/
theorem att_csdid (hA : S.Assumptions) (g t : Fin S.T)
    (hg : 1 ≤ g.val) (hgt : g.val ≤ t.val) :
    S.ATT g t hg
      = normalizedRestrictedIntegral P.μ (S.cohortEvent g hg)
            (fun ω => S.factualY t ω - S.factualY (S.predFin g hg) ω)
        - normalizedRestrictedIntegral P.μ S.neverTreatedEvent
            (fun ω => S.factualY t ω - S.factualY (S.predFin g hg) ω) := by
```

**4. `late_wald` — `PO/ID/Exact/LATE.lean:492-506`**
```lean
/-- **Wald identification of LATE** (`prop:po-late`). Under [the binary-
instrument LATE identifying assumption bundle](hyp:hA), when [the event
`{Z=1}` has positive probability](hyp:hZ1), [the event `{Z=0}` has positive
probability](hyp:hZ0), and [the potential outcomes under treatment](hyp:hY1)
and [under control](hyp:hY0) are integrable, [the Wald ratio
`(E[Y|Z=1] − E[Y|Z=0]) / (E[D|Z=1] − E[D|Z=0])` equals the local average
treatment effect `LATE`](goal). -/
theorem late_wald (hA : S.Assumptions)
    (hZ1 : 0 < (P.μ (S.zEvent true)).toReal)
    (hZ0 : 0 < (P.μ (S.zEvent false)).toReal)
    (hY1 : Integrable (S.YofD true) P.μ)
    (hY0 : Integrable (S.YofD false) P.μ) :
    (S.condExpYZ true - S.condExpYZ false) /
      (S.condExpDZ true - S.condExpDZ false)
      = S.LATE := by
```

**5. `manski_bounds_ATE` — `PO/ID/Partial/Manski/NonAsp.lean:75-85`**
```lean
/-- **Manski bounds for the ATE under an imperfect instrument.** For [any two instrument strata
`z₁` and `z₀` in the support of the instrument](hyp:hz₁,hz₀), [the average treatment effect is
sandwiched between the worst-case lower bound formed from the `z₁`-stratum lower envelope and
`z₀`-stratum upper envelope, and the corresponding upper bound with the roles reversed](goal) —
using only [bounded outcomes](hyp:hA) and [mean independence of the instrument](hyp:hMI), with no
selection assumptions. -/
theorem manski_bounds_ATE [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep)
    {z₁ z₀ : α} (hz₁ : z₁ ∈ S.support) (hz₀ : z₀ ∈ S.support) :
    S.lowerBound1 hA.lo z₁ - S.upperBound0 hA.hi z₀ ≤ S.ATE
    ∧ S.ATE ≤ S.upperBound1 hA.hi z₁ - S.lowerBound0 hA.lo z₀ := by
```

**6. `balkePearl_sharp` — `PO/ID/Partial/BalkePearl/Sharp/Sharpness.lean:442-458`**
```lean
/-- **Sharpness.** Under [the Balke-Pearl IV base assumptions](hyp:hA), for [a latent
treatment-response table `π`](hyp:π) that is [feasible for the linear program —
nonnegative, summing to one, and reproducing the observed cell probabilities as its
marginals](hyp:hπ), [there exists another potential-outcome system, satisfying the same
base assumptions, whose observed cell probabilities agree with the original system's and
whose average treatment effect equals the LP objective value of `π`](goal): every feasible
latent table is realised by some potential-outcome model.

The proof builds the canonical model in `POBalkePearlSharp.canonicalPOSystem`
/ `POBalkePearlSharp.canonicalBP` and verifies its `BaseAssumptions` and
the marginal identities. -/
theorem balkePearl_sharp (hA : S.BaseAssumptions)
    (π : Bool → Bool → Bool → Bool → ℝ) (hπ : BPFeasible S hA π) :
    ∃ (P' : POSystem.{0,0,0}) (S' : POBalkePearlSystem P')
        (_hA' : S'.BaseAssumptions),
      (∀ y d z, S'.cellProb y d z = S.cellProb y d z) ∧
      S'.ATE = BPObjective π := by
```

**7. `POSystem.Consistency` — `PO/Assumptions/Consistency.lean:51-67`**
```lean
/-- For [a potential-outcome system](hyp:P), [consistency](hyp:factual) says
that whenever a unit factually receives an intervention regime, every non-target
potential outcome under that regime equals its observed factual outcome.

This is the observed/counterfactual linkage component of consistency in Hernán
and Robins (2020, §3.5). Their §3.4 separately discusses the requirement that
counterfactual outcomes be sufficiently well-defined, which this structure does
not encode. See also Cole and Frangakis (2009). A researcher studying a one-shot
treatment can assume this linkage without also imposing a recursive composition
law. -/
structure Consistency (P : POSystem) : Prop where
  /-- Factual consistency. -/
  factual :
    ∀ (r : Regime P.V P.X) (Y : Finset P.V),
      _root_.Disjoint Y r.target →
      ∀ ω : P.Ω, P.FactualAgrees r ω →
        P.poVariable r Y ω = P.poVariable Regime.empty Y ω
```

**8. `rdd_identification` — `PO/ID/Exact/RDD/SharpRDD.lean:352-366`**
```lean
/-- **Sharp RDD identification at the cutoff** (textbook form). For [a sharp-RDD
design](hyp:S), under [the sharp-RDD
assumption bundle — SUTVA consistency, deterministic treatment assignment `D = 1{X ≥ c}`
almost surely, regression-function representatives for the potential and observed outcomes,
continuity of the potential-outcome regression functions at the cutoff, positive local mass
of the running variable on each side of `c`, and existence of both one-sided limits of the
observed-outcome regression function at `c`](hyp:hA), [the cutoff-local treatment effect
equals the difference of the right- and left-hand limits of the observed-outcome regression
function at the cutoff](goal):

    τ_RDD(c) = lim_{x ↓ c} ν(x) - lim_{x ↑ c} ν(x).

The existence of both side limits is part of the `Assumptions` bundle. -/
theorem rdd_identification (hA : S.Assumptions) :
    S.tau_RDD hA = S.nu_right_limit hA - S.nu_left_limit hA := by
```

### Discovery

**1. `icp_sound` — `Discovery/InvariantPrediction/Soundness.lean:42-47`**
```lean
/-- **Population ICP soundness from parent-set invariance.** For [an environment family](hyp:F) and [an index i₀ selecting
the target's observed-parent set](hyp:i₀), [the identified set is contained in the target's
observed parents: every node selected by ICP is a genuine direct cause](goal). -/
theorem icp_sound (F : EnvFamily N Ω ι) (i₀ : ι) :
    F.idSet ⊆ (↑(F.paObs i₀) : Set (SWIGNode N)) :=
  F.idSet_subset_of_mem (F.paObs_mem_invariantSets i₀)
```

**2. `icp_complete_linearGaussian_of_exogeneity` — `Discovery/InvariantPrediction/LinearGaussian/Completeness.lean:293-305`**
```lean
/-- **Conditional completeness for do-interventions (Theorem 2(i) specialization).**
For [a linear-Gaussian environment family whose models separately certify target
exogeneity](hyp:F), with [integrable observational regressors](hyp:hInt), such
that [every predictor $j$ receives at least one environment with a single
do-intervention $A^e = \{j\}$ whose shifted value $a^e_j$ differs from its
observational mean $E[X^1_j]$](hyp:hInterv), [the ICP identified set — the
intersection of all invariant predictor sets — equals exactly the parent set of the
target node, $S(E) = PA(Y)$](goal).

This is the main result of this sub-development. -/
theorem icp_complete_linearGaussian_of_exogeneity
    (hInt : F.ObsIntegrable) (hInterv : F.HasShiftedSingleInterventions) :
    F.identifiedSet = F.paY := by
```

**3. `disentanglement_uniqueness_up_to_signed_scaling_of_nondegenerate` — `Discovery/LinearDisentanglement/Uniqueness_Part4.lean:37-69`**
```lean
/-- **Conditional unnormalized uniqueness up to signed scaling.** Let [two solutions `S` and
`S'`](hyp:S,S') of the linear causal disentanglement model have [intervention-target maps
that are bijections onto the latent coordinates, i.e. one intervention per latent
node](hyp:hcov,hcov') and suppose [`S`'s interventions are non-degenerate: every
intervened precision matrix `Θ_k` differs from the observational precision matrix
`Θ_0`](hyp:hNondeg). If [`S` and `S'` share the
same observational precision matrix](hyp:hΘ0) and [agree, context by context, on
every interventional precision matrix](hyp:hΘ), then [`S` and `S'` are related by a
single order-preserving relabeling `σ` of the latent coordinates, a nonzero scaling
vector `μ`, and a `±1` sign vector `ν`, transporting `S`'s latent-direction and
structural coefficient matrices onto `S'`'s, with `σ` carrying `S`'s intervention
targets onto `S'`'s](goal).

The proof is the clean orthogonal-matrix route:
(L1) `H' = M H` for an invertible `M` (`exists_change_of_basis`, from rowspace equality
forced by `Θ₀ = Θ₀'`); (L2) the per-context Gram identity `BᵀB = (B'M)ᵀ(B'M)`
(`gram_identity`); (L3) hence `Oₖ = B'ₖ M Bₖ⁻¹` is orthogonal (`gram_to_orthogonal`);
(L4) the orthogonal-correctness collapse to a single order-preserving permutation
(`exists_orderPerm`, the geometric core); (L5) the signed conclusion is obtained by
substituting the monomial form of `M`. -/
theorem disentanglement_uniqueness_up_to_signed_scaling_of_nondegenerate
    (S S' : Solution d p K)
    (hcov : Function.Bijective S.target) (hcov' : Function.Bijective S'.target)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ), S.InSG σ ∧
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      S'.H = Matrix.diagonal μ * permMat σ * S.H ∧
      S'.B0 * (Matrix.diagonal μ * permMat σ) =
        Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * (Matrix.diagonal μ * permMat σ) =
        Matrix.diagonal ν * permMat σ * S.Bint k) ∧
      (∀ k, S'.target k = σ (S.target k)) := by
```

**4. `Discovery.lean` roll-up (the module's own statement of scope) — `Causalean/Discovery.lean`**
```lean
/-!
# Causal-discovery interfaces

This directory collects three identification mechanisms: invariant prediction
across environments, non-Gaussian linear structural models via LiNGAM, and
linear latent disentanglement from intervention-indexed precision matrices.
Each subdirectory exposes its own model assumptions and recovery guarantee.
-/
```

**5. `lingam_identifiability_kurtosis` — declared `Discovery/LiNGAM/LiNGAMKurtosis.lean:92`** (docstring from `Discovery/LiNGAM.lean:15-22`):
```
Identifiability of the linear non-Gaussian acyclic model x = B·x + e (Shimizu et al. 2006) under
a fourth-cumulant assumption. Suppose two models x = A·e and x = A'·e' with invertible mixing
matrices generate the same law of the observed vector, both coefficient matrices A⁻¹ = I − B and
A'⁻¹ = I − B' have unit diagonal, A⁻¹ is acyclic in some causal order, and both disturbance
vectors have independent coordinates. If the coordinates of e are centered with finite fourth
moments and fourth cumulants that are all strictly positive or all strictly negative, then
B = B'. The argument uses a fourth-cumulant identity in place of the Darmois–Skitovich theorem,
so it covers the all-super-Gaussian and all-sub-Gaussian cases, not general non-Gaussian noise.
```

**6. `icp_sound` — scope caveat, `Discovery/InvariantPrediction.lean:41-49`**
```
## Status

The Proposition 1 mechanism-validity/population-soundness analogue is formalized
in the nonparametric SCM setting. A separate random-variable/regression API under
`LinearGaussian/` proves
`icp_complete_linearGaussian_of_exogeneity`, a specialization of the paper's
Theorem 2(i) with observational and interventional target exogeneity supplied as
structure fields. Its `identifiedSet` is not definitionally the nonparametric
`idSet`; no equivalence theorem between the two APIs is claimed here.
```

### ML

**1. `lasso_oracle_inequality` — `ML/Lasso/OracleInequality.lean:327-357`**
```lean
/-- **Fixed-design Lasso oracle inequality under restricted eigenvalues.** For
[a positive sample size](hyp:hn), let [the response obey
the fixed-design model `y = Xβ⋆ + w`](hyp:hmodel), let [the true coefficient be
supported on `S`](hyp:hsupp) with [support size `s`](hyp:hcard), and let [the
positive penalty level](hyp:hlam) satisfy [twice the score infinity norm is at
most the penalty](hyp:hscore).  If [the restricted-eigenvalue curvature `κ` is
positive](hyp:hkappa), [the design satisfies restricted eigenvalues on the
factor-three cone](hyp:hRE), and [the candidate is an exact normalized Lasso
minimizer](hyp:hmin), then [its error has Euclidean norm at most
`3√s λ/κ`, one-norm at most `12sλ/κ`, and normalized prediction error at most
`9sλ²/κ`](goal).

The constants follow the classical basic-inequality proof: optimality and score
domination put the error in the factor-three cone, after which restricted
curvature and Cauchy--Schwarz on the true support close all three bounds. -/
theorem lasso_oracle_inequality
    (X : Matrix (Fin n) (Fin p) ℝ) (y w : Fin n → ℝ)
    (βstar βhat : Fin p → ℝ) (S : Finset (Fin p)) (s : ℕ)
    (lam kappa : ℝ)
    (hn : 0 < n)
    (hmodel : y = X *ᵥ βstar + w)
    (hsupp : ∀ j ∉ S, βstar j = 0)
    (hcard : S.card = s)
    (hlam : 0 < lam)
    (hscore : 2 * lassoScoreSupNorm X w ≤ lam)
    (hkappa : 0 < kappa)
    (hRE : RestrictedEigenvalue X S kappa)
    (hmin : IsLassoMinimizer X y lam βhat) :
    finiteL2Norm (βhat - βstar) ≤ 3 * Real.sqrt s * lam / kappa ∧
      l1penalty (βhat - βstar) ≤ 12 * s * lam / kappa ∧
      fixedDesignPredictionError X (βhat - βstar) ≤ 9 * s * lam ^ 2 / kappa := by
```

**2. `rkhs_ball_empiricalRademacher_le` — `ML/Kernel/RKHSRademacher.lean:470-484`**
```lean
/-- If [evaluation on `H` has supplied reproducing representers](hyp:hK),
[`κ` is a nonnegative bound](hyp:hκ), [`r` is a nonnegative radius](hyp:hr), and
[every sampled representer `representer (xs k)` has norm at most `κ`](hyp:hbound), then
[the empirical Rademacher complexity](goal), on [the sample `xs`](hyp:xs), of the closed ball
of radius `r` in `H` is at most `κ·r/√n`.

Only the reproducing identity is used to reduce evaluation to the abstract
Hilbert-space linear bound; no function-space embedding is assumed. -/
theorem rkhs_ball_empiricalRademacher_le
    {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {feval : H → X → ℝ} {representer : X → H}
    (hK : HasReproducingRepresenters X H feval representer)
    {n : ℕ} {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (xs : Fin n → X) (hbound : ∀ k, ‖representer (xs k)‖ ≤ κ) :
    empiricalRademacherComplexity n
```

**3. `ridge_achievesL2Rate` — declared `ML/Ridge/Rate.lean:797`.** Docstring from `ML/Ridge.lean`:
```
Ridge regression in a finite feature basis: penalized least squares with penalty λ‖β‖², in the
sample and in the population. For λ > 0 the matrix XᵀX + λI is positive definite, so
β̂ = (XᵀX + λI)⁻¹Xᵀy is the unique solution of the ridge normal equations with no rank condition
on X, and for λ ≥ 0 any solution of the normal equations minimizes the penalized objective; the
same holds for the population objective. For a fixed λ > 0 and an i.i.d. sample, the sample ridge
predictor converges in L²(P) at rate n^{-1/2} to the population ridge predictor, given finite
fourth moments of the features and square-integrable scores. The limit is the penalized
pseudo-true linear predictor, not in general the conditional mean.
```

**4. `condExp_of_isResidualOrthogonal` — `ML/CausalApplication/RegressionBridge.lean:120-133`**
```lean
/-- [A residual-orthogonal candidate agrees almost everywhere with the response conditional
mean given covariates](goal) under [a finite joint covariate--response law](hyp:P) on
[a measurable covariate space](hyp:X), provided [the candidate is measurable](hyp:m,hm),
[the response is integrable](hyp:hY), [the candidate evaluated at covariates is
integrable](hyp:hmint), and [every admissible covariate function is orthogonal to its
residual](hyp:hproj).

Together with the forward direction, this gives the full equivalence connecting
the squared-loss population target to the regression-function nuisance. -/
theorem condExp_of_isResidualOrthogonal
    (P : Measure (X × ℝ)) [IsFiniteMeasure P] {m : X → ℝ} (hm : Measurable m)
    (hY : Integrable (fun z => z.2) P) (hmint : Integrable (fun z => m z.1) P)
    (hproj : Causalean.ML.IsResidualOrthogonal P m) :
    (fun z => m z.1) =ᵐ[P] (P[fun z => z.2 | covarSigma (X := X)]) := by
```

**5. `dml_rate_conditions_of_quarter_rates` — `ML/CausalApplication/RateAssembly.lean:44-58`**
```lean
/-- **Assembly.** On [a measurable sample space with sampling law](hyp:Ω,μ), for [outcome
and propensity error sequences](hyp:μErr,eErr), if, for every treatment arm, [the
outcome-regression estimation error is `o_p(n^{-1/4})`](hyp:hμ), and [the propensity
estimation error is `o_p(n^{-1/4})`](hyp:he), then [each error is separately `o_p(1)`, and
for every arm the
pointwise product of the outcome and propensity errors is `o_p(n^{-1/2})`](goal) —
together these are DML's three nuisance-rate conditions. -/
theorem dml_rate_conditions_of_quarter_rates
    {μErr : Bool → ℕ → Ω → ℝ} {eErr : ℕ → Ω → ℝ}
    (hμ : ∀ a, IsLittleOp (μErr a) (fun n => (n : ℝ) ^ (-(1 / 4 : ℝ))) μ)
    (he : IsLittleOp eErr (fun n => (n : ℝ) ^ (-(1 / 4 : ℝ))) μ) :
    (∀ a, IsLittleOp (μErr a) (fun _ => 1) μ) ∧
      IsLittleOp eErr (fun _ => 1) μ ∧
      (∀ a, IsLittleOp (fun n ω => μErr a n ω * eErr n ω)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :=
```

**6. `lasso_erm_excess_rate` — `ML/Lasso/Rate.lean:78-94`**
```lean
/-- **L¹-ball constrained ERM linear-functional deviation rate.** For linear predictors indexed
by the `L¹` ball, if [the dimension `d` is positive](hyp:hd), [the sample size `n` is
positive](hyp:hn), [the coordinatewise feature bound `Xinf` is
nonnegative](hyp:hXinf), [the weight bound `W` is nonnegative](hyp:hW), [the feature map
`X` is measurable](hyp:hX), [the constant `t` satisfies the calibration
`t·(Xinf·W)² ≤ 1/2`](hyp:ht'), [the tolerance `ε` is nonnegative](hyp:hε), and [the
estimator `ŵ` attains an empirical linear functional no larger than that of the comparator
`wstar`](hyp:hERM), then [the probability that the corresponding excess population linear
functional of `ŵ` over
`wstar` exceeds `4·(Xinf·W/√n)·√(2 log 2d) + 2ε` is at most `exp(-ε²tn)`](goal). -/
theorem lasso_erm_excess_rate {d n : ℕ} (hd : 0 < d) (hn : 0 < n) {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {Xinf W : ℝ}
    (hXinf : 0 ≤ Xinf) (hW : 0 ≤ W)
    (X : Ω → LinftyBall (d := d) Xinf)
    (hX : Measurable fun ω => (X ω).1)
    {t : ℝ} (ht' : t * (Xinf * W) ^ 2 ≤ 1 / 2) {ε : ℝ} (hε : 0 ≤ ε)
    (ŵ : (Fin n → Ω) → L1Ball (d := d) W) (wstar : L1Ball (d := d) W)
```

### Mathlib (representative)

**`orthogonal_upperTri_pos_diag_eq_one` — `Mathlib/LinearAlgebra/Cholesky.lean`** (uniqueness core; consumed by `Discovery.LinearDisentanglement`):
```lean
/-- If [a matrix is orthogonal](hyp:hortho), [upper-triangular](hyp:hupp), and has
[strictly positive diagonal](hyp:hpos), [it is the identity matrix](goal). -/
theorem orthogonal_upperTri_pos_diag_eq_one {ι K : Type*} [Fintype ι] [LinearOrder ι]
```

---

## Gaps / TODOs / caveats

These are **documented by the library itself**, quoted verbatim. No gap below is my inference.

### Discovery

1. **ICP finite-sample coverage not formalized.** `Discovery/InvariantPrediction.lean:23` — *"The paper's finite-sample coverage guarantee is not formalized."* And `Soundness.lean:22-23`: *"The paper's Theorem 1 is a finite-sample coverage result and is not asserted here."* What **is** proved (`icp_sound`) is explicitly characterized as *"a population set-inclusion consequence of the mechanism validity represented by Proposition 1"*.

2. **Two non-connected ICP APIs.** `Discovery/InvariantPrediction.lean:48-49` — *"Its `identifiedSet` is not definitionally the nonparametric `idSet`; no equivalence theorem between the two APIs is claimed here."*

3. **Disentanglement result is weaker than the paper's.** `Discovery/LinearDisentanglement.lean:24-25, 39-40` — *"The model here does not impose the paper's row normalization, so the ambiguity is not reduced to relabelings alone."* / *"Unlike the paper's Theorem 2, this model does not impose its row normalization and therefore does not reduce the ambiguity to permutations alone."* And `Uniqueness_Part4.lean:24-25` — *"The result is weaker than the normalized permutation-only conclusion of the paper's Theorem 2."*

4. **`sigma_solutions` is only one direction.** `Discovery/LinearDisentanglement.lean:42-43` — *"This constructs the pure-permutation subclass; it is not a converse for every signed-scaling ambiguity allowed by the uniqueness theorem."*

5. **LiNGAM covers only the same-sign-kurtosis case.** `Discovery/LiNGAM.lean:21-22` — *"The argument uses a fourth-cumulant identity in place of the Darmois–Skitovich theorem, so it covers the all-super-Gaussian and all-sub-Gaussian cases, not general non-Gaussian noise."*

### ML

6. **Kernel-ridge `L²` rate theorem is NOT present.** `ML/Kernel/EffectiveDimension.lean:34-38` — *"The downstream **rate** theorem (`N(λ)`/eigenvalue-decay ⇒ the `n^{-2rb/(2rb+1)}` kernel-ridge `L²` rate) additionally requires Hilbert-space operator-concentration machinery (an operator Bernstein inequality for `(T+λ)^{-1/2}(T − T̂ₙ)(T+λ)^{-1/2}`) that is a separate substrate; this file is the definitional foundation it would build on."* This is a **declared missing substrate**.

7. **DML layer is not connected to a concrete learner.** `ML/CausalApplication.lean` (roll-up) — *"This layer does not yet connect a concrete learner or its proved rate to those hypotheses."* Repeated in `RateAssembly.lean:13-15`: *"It does not connect those sequences to a concrete learner or invoke a method-specific `AchievesL2Rate` theorem."* And `RateAssembly.lean:19-21`: *"Fixed-penalty ridge and logistic rates target penalized pseudo-true predictors; they do not by themselves provide this identification."*

8. **Ridge's limit is not the conditional mean.** `ML/Ridge.lean` — *"The limit is the penalized pseudo-true linear predictor, not in general the conditional mean."*

### PO

9. **`Consistency` deliberately omits SUTVA well-definedness.** `PO/Assumptions/Consistency.lean:56-60` — *"Their §3.4 separately discusses the requirement that counterfactual outcomes be sufficiently well-defined, which this structure does not encode. ... A researcher studying a one-shot treatment can assume this linkage without also imposing a recursive composition law."*

10. **Composition consistency is an extra assumption, not automatic.** `PO/Assumptions/Consistency.lean:74-80` — *"It is a separate modelling assumption: automatic for a potential-outcome system induced by an SCM, but genuinely additional for a bare potential-outcome system."* (The bridging theorems `POSystem.ofSCM_consistency` / `ofSCM_compositionConsistency` at `Bridge/FromSCM.lean:421,464` formalize exactly the "automatic for SCM" half.)

11. **RDD one-sided limits are assumed, not derived.** `PO/ID/Exact/RDD/SharpRDD.lean:364` — *"The existence of both side limits is part of the `Assumptions` bundle."*

### Axiom/sorry-adjacent honesty note

12. The `MultipleInstrumentIV` docstring flags a modelling field as an assumption rather than a derived fact: `ResponseTypes.lean:350` — *"This is an axiom field, not a derived fact."* This is **correct Lean practice** (a hypothesis field), but it is worth noting the library says so in plain language.

### Method caveats for this audit

- All findings are from **HEAD `47acf195`** of a blobless clone. Only committed content was inspected; working-tree state and branches were not examined.
- Absence claims are **textual** (grep over `.lean` sources). A concept could exist under a name I did not search for. I searched all the terms the task named plus close variants; **未能确认** applies to any concept outside that search list.
- Counts of "declarations" come from a line-based regex extractor matching `^(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)` with a leading identifier. It does not count `where`-clause helpers, `let` bindings, or declarations whose keyword is indented inside a `section` without a leading keyword at line start. **Order of magnitude is reliable; the exact figure may be slightly low.**
- I did not compile or type-check anything (no `lake build`); a sorry-free source tree is not proof the library builds at this commit.

---

## What is NOT present

Searched over **all 977 files** of the four clusters. Counts are exact greps. Substring false positives are called out.

### Discovery — algorithm implementations (the critical determination)

| Searched | Hits | Verdict |
|---|---|---|
| `PCAlgorithm` | **0** | absent |
| `\bPC\b` | **0** in Discovery | absent (repo-wide hits are local variables `Pc`/`pC` in PO SupportFunction and Mathlib Chebyshev) |
| `\bGES\b` | **0** (word-boundary) | **absent.** The 18–35 raw substring hits are inside **"ranges"**, **"packages"**, **"edges"**, **"changes"** |
| `GreedyEquivalenceSearch` | **0** | absent |
| `\bBIC\b` | **0** | absent |
| `BDeu` | **0** | absent |
| `scoreBased` / `constraintBased` | **0** / **0** | absent |
| `MarkovEquivalence` | **0** | **absent from Discovery** — it exists in `Causalean/Graph/MarkovEquiv/**` (outside my scope) |
| `CPDAG` / `essentialGraph` / `\bMEC\b` | **0** / **0** / **0** | absent (raw "MEC" substring hits are inside **"mechanism"**) |
| `\bFCI\b` / `\bPAG\b` | **0** / **0** | absent — no latent-confounding discovery |
| `Lindley` | **0** | absent |
| `faithfulness` (the assumption) | **0** | **absent.** 2 hits are prose: *"Faithful to the paper's ..."* / *"Faithful do-semantics"* |
| `causalDiscovery` | **0** | absent |
| `skeleton` / `Meek` / `d-sep` / `dSep` / `collider` | **0** / **0** / **0** / **0** / **0** | absent from Discovery (d-separation lives in `Causalean/Graph/DSep/**`, outside scope) |

**Verdict: the Discovery cluster contains no PC, no GES, no FCI, no score-based or constraint-based structure-learning algorithm, and no faithfulness/Markov-equivalence/CPDAG machinery.** It is **identification theory**, not algorithm implementation. Its own `Discovery.lean` roll-up says so: *"This directory collects three identification mechanisms."* The three are (i) population-level ICP, (ii) LiNGAM fourth-cumulant identifiability, (iii) intervention-based linear latent disentanglement. There is no hypothesis testing and no sample-complexity analysis either — **未能确认** any such content; the ICP finite-sample theorem is explicitly declared unformalized.

### ML

| Searched | Hits | Verdict |
|---|---|---|
| `\bPAC\b` | **0** (word-boundary) | absent. Raw "PAC" substring hits (361) are inside **"capacity"**, **"packages"**, **"space"** |
| `\bVC\b` / `VC dimension` | **0** | absent |
| `regret` | **0** | absent |
| `bandit` | **0** | absent |
| `uniform convergence` / `uniformConvergence` | **0** | absent |
| `covering number` / `coveringNumber` | **0** | absent |
| `McDiarmid` | **0** | absent |
| `generalization` | **0** | absent |
| `\bRademacher\b` | **27** | **present** — via `Causalean.Stat.Concentration.Rademacher` and `third_party/lean-rademacher` |
| `concentration` | 17 | present, but mostly imports of `Causalean.Stat.Concentration.*` (outside my scope) |

The ML cluster does have Rademacher complexity and ERM excess-risk rates (Lasso, L¹/L²-ball linear, margin, logistic, RKHS ball), but **no PAC/VC generalization theory, no covering numbers, no McDiarmid, and no online-learning/regret/bandits**.

### PO

| Searched | Hits | Verdict |
|---|---|---|
| `eventStudy` / `EventStudy` | **0** | **absent** — no event-study estimator formalization (CS-DID group-time ATT is present instead) |
| `partialIdentif` / `PartialIdentif` | **0** | absent as a name — the concept is present as `PartialID`, `BPIdentifiedInterval`, `CriterionSet`, `IVBounds`, etc. |
| `SUTVA` | 15 | **present** — named as the consistency/SUTVA assumption in every major identification system: `PO/Assumptions/ConsistencyLemmas.lean:204`, `PO/ID/Exact/ATE.lean:272`, `ATT.lean:90,102`, `DID.lean:149`, `LATE.lean:221` |
| `CSDID` | 0 as a bare token | present as `POCSDIDSystem` / `att_csdid` |

Everything the task asked me to look for in PO — `PotentialOutcome`, `Counterfactual`, `Y_`, `PO`, `response`, `ATE`/`ATT`/`CATE`/`LATE`, `averageTreatmentEffect`/`treatmentEffect`, identification, `backdoor`/`frontdoor`/`adjustment`, `DiD`/`DID`/`parallelTrends`, IV/`instrument`/`complier`/`monotonicity`/`exclusion`, `Manski`/`Balke`/`Pearl`/`bound`/`Bounds`/`sharp`, `CondIndep`/`Indep`, and SUTVA/consistency/positivity/overlap/ignorability — **is present**, except `eventStudy` and the literal token `CATE` (the CATE *concept* is present as a CATE-to-ATE integration lemma in `PO/Conditioning/CondExpTooling.lean:333-343`).

### Mathlib

Nothing named in the task was expected absent here. Note the local Mathlib does **not** contain: kernel-ridge optimal-rate theorems, operator Bernstein inequalities, or any causal-graph theory (those live in `Causalean/Stat`, `Causalean/Graph`, `Causalean/SCM` — outside my scope).

---

## Cross-cluster context (outside my scope, stated for orientation only)

Two clusters that my scope does **not** cover hold machinery a reader might expect inside Discovery:

- `Causalean/Graph` (48 files) contains `DSep/**` (d-separation, Bayes-ball, active paths), `MarkovEquiv/**` (`MarkovEquivalence`, `CoveredReversal`, `Moralization`, `Decompose`), `Density/FiniteDAG/**`, and `DAG.lean`.
- `Causalean/SCM` (116 files) contains `ID/{Backdoor,BackdoorCriterion,Adjustment}.lean`, `ID/Assumptions/Monotonicity.lean`, `Do/{DoCalculus,Rule2,Rule3,Overlap,GlobalMarkov,LocalMarkov}.lean`, `Examples/{BackDoor,Frontdoor,IV,MonotoneCounterfactualBound}.lean`.

PO **does** import from these (`PO/Bridge/FromSCM.lean`, `PO/Bridge/FromSCMCondIndep.lean` bridging d-separation to counterfactual conditional independence), so the PO identification results are wired to graph-level theory — just not through the Discovery directory.

Remaining `Causalean` clusters, for completeness: `Estimation` (237), `Experimentation` (112), `Panel` (61), `SCM` (116), `Stat` (1055), `Tactic` (5), `Graph` (48).

---

## Bottom line

1. **Discovery is identification theory, not causal-discovery algorithms.** Zero PC/GES/FCI/CPDAG/MEC/faithfulness/score-based/constraint-based content. It is ICP (population-level), LiNGAM (same-sign-kurtosis), and linear disentanglement (unnormalized).
2. **Zero `sorry`, zero `axiom` declarations, zero `native_decide`** across all 977 files / 5509 declarations of the four clusters. Every textual "axiom"/"admit" hit is English prose in a docstring.
3. **PO is the substantive causal-inference cluster** (154 files, 1416 declarations) with genuinely broad coverage: ATE/ATT backdoor, DID, Callaway–Sant'Anna staggered DID, frontdoor, LATE/IV (incl. multiple-instrument and dynamic), RDD (sharp + fuzzy), proximal, DTR, QTE, partial linear, Heckman–Roy, plus a full partial-identification stack (Manski MTR/MTS/MIV/NonAsp, Balke–Pearl with a real sharpness theorem, Lee trimming, MSM sensitivity, Imbens–Manski inference, random-set inference, support functions).
4. **ML has real Rademacher-based rates** (Lasso oracle inequality, L¹/L²-ball, margin, logistic, RKHS ball, ridge) but **no PAC/VC/covering-number/generalization theory**, and its two most important downstream targets are self-declared absent: the kernel-ridge optimal-rate theorem and the connection from a concrete learner to the DML nuisance-rate hypotheses.
5. **Local Mathlib is a general-purpose Mathlib gap-filler** (730 files, 3690 declarations) heavy on approximation theory, calculus/cube extension, interval arithmetic, probability (independence, kernels, Poisson, Stein CLTs, sub-Gaussian), and measure theory — plus a few causal-facing pieces (`Independence/Conditional`, `Cholesky`, `ConditionalExpectationTransport`).
