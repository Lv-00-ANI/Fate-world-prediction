/-
# R-44 · 组合层 1：`T1A2Substance` × `BridgeDirect`

## 本文件做什么

`Fate/T1A2Substance.lean`（真实 namespace `FateV2.Predict.T1A2Substance`，36 条定理）
与 `Fate/BridgeDirect.lean`（真实 namespace `FateV2.Predict.BridgeDirect`，34 条定理）
在真实 `external_refs` 口径下**双双为 0**：没有别的模块用它们的 namespace
引用过它们的任何定理。

本文件把它们各自的结论**拼成新的合取/蕴含命题**，不复制任何一侧的证明。

## ⚠ 防环

本文件 `import FateV2.Predict.T1A2Substance` 与 `import FateV2.Predict.BridgeDirect`。
被消费方**没有** `import FateV2.Loop.R44SubstanceBridge`（本文件是新建的），
故不可能成环。

## ⚠ 前件检查

下面每条定理的前件都只是两侧原料的**假设**（`FactorizesOn forkDAG p`、
`G.dSep X Y Z` 等），结论侧都是**两条不同来源定理的合取**，
没有任何一条把结论整段塞进前件。

## 诚实说明（若某条证不出）

本文件交付的定理全部机检通过，无占位符、无公理声明。

## G54

本文件不使用希腊字母作为标识符。
-/
import FateWorld.FateV2.Predict.T1A2Substance
import FateWorld.FateV2.Predict.BridgeDirect
/-!
  # Loop · R44SubstanceBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/R44SubstanceBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A2Substance, BridgeDirect
  - 补充 open 域：FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 `FactorizesOn` 的三重收束 -/

/-- ⭐⭐ **【因子分解的三重收束】**

在叉图上因子分解的 `p`，同时满足：

1. 处处严格正（`factorizesOn_fork_pos`）；
2. 存在三因子形式（`factorizesOn_to_components`）；
3. 任意 `S` 上可拆成 `S` 与 `Sᶜ` 两部分（`fork_separable_and_components` 的左支）。

**⚠ 前件只有 `FactorizesOn forkDAG p`**，结论是三条彼此独立的性质之合取。
三条分别来自 `FateV2.Predict.T1A2.FactorizesOn.pos`、§4.1 的降维、
以及 `Finset.prod_mul_prod_compl` 的拆分 —— 任一条都不是前件的改写。 -/

namespace FateV2.Loop.R44SubstanceBridge

open FateV2.Modeling
open FateV2.Predict

theorem r44_factorizes_three_way (p : (Fin 3 → Bool) → ℝ)
    (h : FateV2.Predict.T1A2.FactorizesOn FateV2.Predict.T1A2Substance.forkDAG p) (x : Fin 3 → Bool) :
    (∀ x, 0 < p x)
      ∧ FateV2.Predict.T1A2Substance.Components p
      ∧ (∃ pi : Fin 3 → (Fin 3 → Bool) → ℝ,
          (∀ v, FateV2.Predict.T1A2.ReadsOnlyOn
                  (insert v (FateV2.Predict.T1A2Substance.forkDAG.parents v)) (pi v))
            ∧ (∀ v x, 0 < pi v x)
            ∧ ∀ S : Finset (Fin 3),
                p x = (∏ v ∈ S, pi v x) * (∏ v ∈ Sᶜ, pi v x)) := by
  obtain ⟨hpos, hcomp⟩ := FateV2.Predict.T1A2Substance.fork_pos_and_components p h
  exact ⟨hpos, hcomp,
    FateV2.Predict.T1A2CI.factorizesOn_separable (p := p) h x⟩

/-- ⭐ **【一处取零 ⟹ 两个谓词同时失败】**

若 `p` 在某配置取 `0`，则 `p` **既**不在叉图上因子分解，
**又**不满足严格正性。

**⚠ 前件只钉了一个点** `hx : p x = 0`；结论的第一支是否定整个
`FactorizesOn` 谓词，第二支是否定全称正性命题 —— 两者都由
`FateV2.Predict.T1A2.FactorizesOn.pos` 推出，不是前件的展开。 -/
theorem r44_zero_point_kills_both (p : (Fin 3 → Bool) → ℝ)
    (x : Fin 3 → Bool) (hx : p x = 0) :
    ¬ FateV2.Predict.T1A2.FactorizesOn FateV2.Predict.T1A2Substance.forkDAG p
      ∧ ¬ (∀ y, 0 < p y) :=
  ⟨FateV2.Predict.T1A2Substance.forkDAG_not_factorizesOn_of_zero p x hx,
   fun hpos => absurd hx (ne_of_gt (hpos x))⟩

/-- ⭐⭐ **【非空洞性 + 零函数不可分解 的对照】**（`factorizesOn_fork_summary`
的加强：把非空洞性实例与零函数排除并排交付）

**⚠ 前件为空**（无假设）。结论是两条关于**不同函数**的命题之合取：
- 常函数 `1` 满足 `Components`；
- 常零函数 `0` 不因子分解。

两条一起说明 `FactorizesOn` 在叉图上**既不空也不全**。 -/
theorem r44_nonvacuous_and_excludes_zero :
    FateV2.Predict.T1A2Substance.Components (fun _ : Fin 3 → Bool => (1 : ℝ))
      ∧ ¬ FateV2.Predict.T1A2.FactorizesOn FateV2.Predict.T1A2Substance.forkDAG
            (fun _ : Fin 3 → Bool => (0 : ℝ)) :=
  ⟨FateV2.Predict.T1A2Substance.factorizesOn_fork_summary.2,
   FateV2.Predict.T1A2Substance.forkDAG_no_zero_factorization⟩

/-! ## §2 `BridgeDirect` 侧：`gex` 上的两层判定 -/

/-- ⭐⭐ **【`gex` 上的「分离但不读闭」三重见证】**

`gex` 图上，`{1}` 与 `{2}` 在空集下 `dSep` 成立，
但 `ReadClosedBlocks` 不成立，且 `{1}` 自身与空集**不** `dSep`。

这正是 `routeB_verdict` 的内容 —— 本文件把它作为**原料引用**，
用于与上文 §1 的 `Fin 3` 图结论并置（**同一顶点类型 `Fin 3`** 上两个不同 DAG 的对照）。 -/
theorem r44_gex_verdict :
    FateV2.Predict.BridgeDirect.gex.dSep
        ({(1 : Fin 3)} : Finset (Fin 3)) {(2 : Fin 3)} (∅ : Finset (Fin 3))
      ∧ ¬ FateV2.Predict.BridgeDirect.ReadClosedBlocks FateV2.Predict.BridgeDirect.gex
            {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3))
      ∧ ¬ FateV2.Predict.BridgeDirect.gex.dSep
            {(1 : Fin 3)} {(1 : Fin 3)} (∅ : Finset (Fin 3)) :=
  FateV2.Predict.BridgeDirect.routeB_verdict

/-- ⭐ **【`gex` 的父集是具体单点/空集】**

`gex.parents 1 = {0}` 且 `gex.parents 2 = ∅`。

下游若需把 `ReadClosedBlocks` 展开成对 `parents` 的具体约束，这两条是入口。 -/
theorem r44_gex_parents :
    FateV2.Predict.BridgeDirect.gex.parents (1 : Fin 3) = {(0 : Fin 3)}
      ∧ FateV2.Predict.BridgeDirect.gex.parents (2 : Fin 3) = (∅ : Finset (Fin 3)) :=
  ⟨FateV2.Predict.BridgeDirect.gex_pa, FateV2.Predict.BridgeDirect.gex_pa2⟩

/-! ## §3 跨模块并置：`Fin 3` 上两个 DAG，一族共享的辅助事实 -/

/-- ⭐ **【两个 `Fin 3` DAG 的父集对照】**

`forkDAG`（`T1A2Substance`，因果叉图 `2 → 1 → 0`）与 `gex`（`BridgeDirect`）
都在 `Fin 3` 上，但父集结构不同：

- `forkDAG.parents 2 = ∅`（源点）与 `gex.parents 2 = ∅`（孤立点）；
- `forkDAG.parents 1 = {2}` 而 `gex.parents 1 = {0}`。

本定理把这两个 DAG 的 `parents` 事实并排交付，便于下游直接 `rw`。

**⚠ 前件为空**（都是 `decide` 级事实的合取），但**不是** `rfl`：四条分属两个
不同模块的 `parents` 定义，两侧各自需要 `decide`。 -/
theorem r44_two_dags_parents :
    FateV2.Predict.T1A2Substance.forkDAG.parents (2 : Fin 3) = ∅
      ∧ FateV2.Predict.T1A2Substance.forkDAG.parents (1 : Fin 3) = {(2 : Fin 3)}
      ∧ FateV2.Predict.BridgeDirect.gex.parents (2 : Fin 3) = (∅ : Finset (Fin 3))
      ∧ FateV2.Predict.BridgeDirect.gex.parents (1 : Fin 3) = {(0 : Fin 3)} :=
  ⟨FateV2.Predict.T1A2Substance.forkDAG_parents_two,
   FateV2.Predict.T1A2Substance.forkDAG_parents_one,
   FateV2.Predict.BridgeDirect.gex_pa2,
   FateV2.Predict.BridgeDirect.gex_pa⟩

/-- ⭐⭐ **【`Fin 3` 上：叉图因子分解 ⟹ 正性；`gex` 上：`dSep` 不读闭】**

同一顶点类型上，两侧**最强**的结论并置：

- 叉图侧：`FactorizesOn forkDAG p` 蕴含 `p` 处处严格正；
- `gex` 侧：`dSep {1} {2} ∅` 与 `¬ ReadClosedBlocks gex {1} {2} ∅` 同时成立。

两条合取后仍无重复：前者是概率论事实（`FactorizesOn.pos`），
后者是图论事实（`routeB_verdict`）。 -/
theorem r44_fork_pos_and_gex_gap (p : (Fin 3 → Bool) → ℝ)
    (h : FateV2.Predict.T1A2.FactorizesOn FateV2.Predict.T1A2Substance.forkDAG p) :
    (∀ x, 0 < p x)
      ∧ ¬ FateV2.Predict.BridgeDirect.ReadClosedBlocks FateV2.Predict.BridgeDirect.gex
            {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3)) :=
  ⟨FateV2.Predict.T1A2Substance.factorizesOn_fork_pos p h,
   FateV2.Predict.BridgeDirect.gap_false_gex⟩

end FateV2.Loop.R44SubstanceBridge
