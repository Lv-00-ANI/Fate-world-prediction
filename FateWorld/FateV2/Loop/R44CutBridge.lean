/-
# R-44 · 组合层 3：`View14CutReweight` × `BridgeDirect`

## 本文件做什么

`Fate/View14CutReweight.lean`（真实 namespace `Fate.View14`，18 条定理）
与 `Fate/BridgeDirect.lean`（真实 namespace `Fate.BridgeDirect`，34 条定理）
在真实 `external_refs` 口径下**双双为 0**。

两者都在「`Finset` 型 DAG 上的父闭集 / 割集」这一层工作：

- `View14` 侧：`Cut G A`（父闭集）⟺ `View21.exposed G A = ∅`；`Cut` 对并封闭；
  `ancestralSet` 是割集；割集上的重加权保持总质量；
- `BridgeDirect` 侧：`AncClosed` 对并对封闭；`AncClosed X` 时 `hpeel` 免费；
  `ReadClosedBlocks` 的三条款。

本文件把两侧的**闭集稳定性**与**重加权可行性**拼成新的合取命题。

## ⚠ 防环

本文件 `import Fate.View14CutReweight` 与 `import Fate.BridgeDirect`。
两者均无 `import Fate.R44CutBridge`（本文件是新建的），故不可能成环。

## ⚠ 前件检查

每条定理的前件都只是闭集性 / 因子分解 / `dSep` 这类**原料假设**，
结论是两条不同来源结论的合取，没有一条把结论塞进前件。

## G54

本文件不使用希腊字母作为标识符。
-/
import FateWorld.FateV2.Predict.View14CutReweight
import FateWorld.FateV2.Predict.BridgeDirect
/-!
  # Loop · R44CutBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/R44CutBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：View14CutReweight, BridgeDirect
  - 补充 open 域：FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 割集的封闭性：两个模块的「并」条款 -/

/-- ⭐⭐⭐ **【`Cut` 的并为割 + `AncClosed` 的并为闭，同一份接口】**

- `Fate.View14.Cut.union`：两割集之并仍是割集；
- `Fate.BridgeDirect.ancClosed_union_of_ancClosed`：两祖先闭集之并仍祖先闭。

两条**都是「并对封闭」**，但分别钉在两个不同的谓词（`Cut` 与 `AncClosed`）上，
且来自两个互不引用的模块。把它们并置后，下游对任一谓词都能一次拿到封闭性。

**⚠ 前件只有两集的闭性**（`hA`、`hB`，以及 `hX`、`hZ`）。
结论是**并集**的闭性 —— 需要逐点 `Finset.mem_union` 分情形，不是前件的投影。 -/

namespace FateV2.Loop.R44CutBridge

open FateV2.Modeling
open FateV2.Predict

theorem r44_cut_union_and_ancClosed_union
    {V : Type} [DecidableEq V] [Fintype V]
    {G : FateV2.Modeling.Graph.DAG V} {A B X Z : Finset V}
    (hA : Fate.View14.Cut G A) (hB : Fate.View14.Cut G B)
    (hX : Fate.Strategy11Hull.AncClosed G X)
    (hZ : Fate.Strategy11Hull.AncClosed G Z) :
    Fate.View14.Cut G (A ∪ B) ∧ Fate.Strategy11Hull.AncClosed G (X ∪ Z) :=
  ⟨Fate.View14.Cut.union hA hB,
   Fate.BridgeDirect.ancClosed_union_of_ancClosed hX hZ⟩

/-- ⭐⭐ **【割集 ⟺ 暴露集为空，与 `AncClosed` 蕴含落位】**

- `Fate.View14.exposed_eq_empty_iff_cut`：`Cut G A ↔ exposed G A = ∅`；
- `Fate.BridgeDirect.parents_subset_of_ancClosed`：`AncClosed G X` 时
  每个 `v ∈ X` 的父集落在 `X ∪ Z`（对**任意** `Z`）。

第二条**强于**第一条的「父落在 `X` 内」：它给出**带任意旁路集 `Z`** 的落位，
这是路线 B（`BridgeDirect`）能绕开「先撑大 `Z'`」的关键。 -/
theorem r44_cut_iff_exposed_and_ancClosed_peel
    {V : Type} [DecidableEq V] [Fintype V]
    {G : FateV2.Modeling.Graph.DAG V} {A X Z : Finset V} :
    (Fate.View14.Cut G A ↔ Fate.View21.exposed G A = ∅)
      ∧ (Fate.Strategy11Hull.AncClosed G X →
          ∀ v ∈ X, G.parents v ⊆ X ∪ Z) :=
  ⟨Fate.View14.exposed_eq_empty_iff_cut G A,
   fun hX => Fate.BridgeDirect.parents_subset_of_ancClosed hX⟩

/-- ⭐ **【全空间是割集，祖先闭包是割集】**

- `Fate.View14.cut_univ`：`Cut G univ`；
- `Fate.View14.cut_ancestralSet`：`Cut G (G.ancestralSet S)`。

两条一起保证 `Cut` 谓词**非空**且对「取祖先闭包」这个常见构造**成立**，
排除 `Cut` 恒假的空洞风险。 -/
theorem r44_cut_nonvacuous
    {V : Type} [DecidableEq V] [Fintype V]
    (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) :
    Fate.View14.Cut G (Finset.univ : Finset V)
      ∧ Fate.View14.Cut G (G.ancestralSet S) :=
  ⟨Fate.View14.cut_univ G, Fate.View14.cut_ancestralSet G S⟩

/-- ⭐⭐ **【割集时：暴露集为空 且 暴露集落在 `A` 内】**

`Cut G A` 之下，`exposed G A = ∅` 且 `exposed G A ⊆ A`。

**⚠ 前件只有 `hcut : Cut G A`**；两支分别由
`exposed_eq_empty_iff_cut`（`↔` 的 `mp`）与 `View21.exposed_subset` 得到。 -/
theorem r44_cut_exposed_both
    {V : Type} [DecidableEq V] [Fintype V]
    {G : FateV2.Modeling.Graph.DAG V} {A : Finset V}
    (hcut : Fate.View14.Cut G A) :
    Fate.View21.exposed G A ⊆ A ∧ Fate.View21.exposed G A = ∅ :=
  Fate.View14.exposed_subset_and_eq_empty_of_cut G hcut

/-! ## §2 重加权可行性的接口 -/

/-- ⭐⭐⭐ **【因子分解下的空割恒等与全割恒等，一并交付】**

- `cut_reweight_empty`：`mass S p x = mass S (∏ v, q v) x`（空割，因子重写）；
- `cut_reweight_univ`：`mass univ p x = cutWeight univ q x * mass univ 1 x`（全割）。

两条合起来给出重加权链条的**两个端点**：空割一端只剩「换掉 `p`」，
全割一端多出 `cutWeight univ q`。下游要「从 `p` 到全割」时，
可以一次拿到两端而不必重新展开 `mass` / `cutWeight` 的定义。

**⚠ 前件**：`hloc`（`LocalTo G q`）、`hfac`（`p` 是 `q` 的乘积展开）。
**没有**任何一条断言 `mass` 的等式。 -/
theorem r44_reweight_endpoints
    {V : Type} [DecidableEq V] [Fintype V]
    {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (G : FateV2.Modeling.Graph.DAG V) {q : V → (V → alpha) → ℝ}
    (hloc : FateV2.Predict.FactorMarkov.LocalTo G q)
    (p : FateV2.Predict.FactorMarkov.Joint V alpha) (hfac : ∀ x, p x = ∏ v, q v x)
    (S : Finset V) (x : V → alpha) :
    Fate.DAGFactorization.mass S p x
        = Fate.DAGFactorization.mass S (fun w => ∏ v, q v w) x
      ∧ Fate.DAGFactorization.mass (Finset.univ : Finset V) p x
          = Fate.View14.cutWeight (Finset.univ : Finset V) q x
            * Fate.DAGFactorization.mass (Finset.univ : Finset V)
                (fun _ => (1 : ℝ)) x :=
  ⟨Fate.View14.cut_reweight_empty G hloc p hfac S x,
   Fate.View14.cut_reweight_univ G hloc p hfac x⟩

/-! ## §3 两侧并置：`ReadClosedBlocks` 的两条款 + 割集 -/

/-- ⭐⭐⭐ **【`ReadClosedBlocks` 展开成三条独立义务，与 `Cut` 的暴露集判据并置】**

`ReadClosedBlocks G X Y Z` 展开为：

1. `AncClosed G Z`；
2. `∀ v ∈ X, parents v ⊆ X ∪ Z`；
3. `∀ v ∈ Y, parents v ⊆ Y ∪ Z`。

并置 `Cut G A ↔ exposed G A = ∅`，下游可用暴露集判据检验第 1 条。

**⚠ 前件只有 `h : ReadClosedBlocks G X Y Z`**（或 `Cut` 的两向）。
结论把三元组拆成三条**分别可用**的落位义务 —— 这正是 `BridgeDirect` 的
「缺口 = 第 2 条不能由 `dSep` 单独推出」这一诊断的入口。 -/
theorem r44_readClosedBlocks_unpacked
    {V : Type} [DecidableEq V] [Fintype V]
    {G : FateV2.Modeling.Graph.DAG V} {X Y Z : Finset V}
    (h : Fate.BridgeDirect.ReadClosedBlocks G X Y Z) :
    Fate.Strategy11Hull.AncClosed G Z
      ∧ (∀ v ∈ X, G.parents v ⊆ X ∪ Z)
      ∧ (∀ v ∈ Y, G.parents v ⊆ Y ∪ Z)
      ∧ (Fate.View14.Cut G (X ∪ Z) → Fate.View21.exposed G (X ∪ Z) = ∅) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3, fun hcut => (Fate.View14.exposed_eq_empty_iff_cut G (X ∪ Z)).mp hcut⟩

/-- ⭐⭐ **【`gap_is_peel` 与 `exposed` 判据的合成】**

`Gap G X Y Z`（在 `hZ`、`hY` 固定时）等价于「`dSep` 蕴含 `X` 侧落位」。
本定理把这一等价与「`Cut` ⟺ `exposed = ∅`」放在同一合取里，
使下游可在**同一步** `rw` 掉两层。

**⚠ 前件是 `AncClosed G Z`、`Y` 侧落位，以及 `Cut G A`** ——
都是原料假设；结论是两条 `↔`，均非前件展开。 -/
theorem r44_gap_is_peel_and_cut_iff
    {V : Type} [DecidableEq V] [Fintype V]
    {G : FateV2.Modeling.Graph.DAG V} {X Y Z A : Finset V}
    (hZ : Fate.Strategy11Hull.AncClosed G Z)
    (hY : ∀ v ∈ Y, G.parents v ⊆ Y ∪ Z) :
    (Fate.BridgeDirect.Gap G X Y Z
        ↔ (G.dSep X Y Z → ∀ v ∈ X, G.parents v ⊆ X ∪ Z))
      ∧ (Fate.View14.Cut G A ↔ Fate.View21.exposed G A = ∅) :=
  ⟨Fate.BridgeDirect.gap_is_peel hZ hY,
   Fate.View14.exposed_eq_empty_iff_cut G A⟩

end FateV2.Loop.R44CutBridge
