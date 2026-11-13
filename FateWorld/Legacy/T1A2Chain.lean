import FateWorld.Legacy.T1A2
import FateWorld.Legacy.T1A2CI
import FateWorld.Legacy._root.CausDAG
import Mathlib.Tactic

/-!
# `Fate/T1A2Chain` —— `T1A.2` 在**链图**上的 specialize

## 背景

`T1A.2` 的已有成果：

- `Fate.T1A2`：读集谓词 `ReadsOnlyOn` 与因子分解 `FactorizesOn` 的定义；
- `Fate.T1A2CI`：可分离性 `factorizesOn_separable`；
- `T1A2Substance`：**叉图**（`2 → 1 → 0`）的具体实例；
- `Fate.T1A2N`：**任意 DAG** 上的抽象推广
  （**⚠ 注意**：本文件的证明**不依赖** `Fate.T1A2N` —— 服务器上
  `T1A2N.olean` 尚未构建，`Fate.T1A2N.lean` 仅有源码；
  且三条目标定理均为纯组合事实，不需要 `T1A2N` 的任何结论，
  故本文件只 `import Fate.T1A2`、`Fate.T1A2CI`、`CausDAG`）。

本文件补上**链图**（形如 `2 → 1 → 0` 的线性链）这一档 specialize 所缺的
**读集分析**部分，全部是 `V` 上的**纯组合**事实（不涉及概率/测度）：

1. `chain_reads_single_parent` —— 单父节点的读集收缩为 `{v, u}`；
2. `reads_mono_transfer` —— 读集对超集的单调传递；
3. `prod_reads_union` —— 乘积的读集上界（并集形式）。
-/

namespace Fate.T1A2Chain

open Finset
open Fate.T1A2

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐⭐ **链图的读集性质**（抽象版）：

若 `v` 的父集是单元素集 `{u}`（这正是链图/单父情形），则条件因子 `π v`
只读 `{v, u}`。

**⚠ 这是链图每个节点「继承父节点信息」的形式表达**：
`π v` 在定义上被允许读 `insert v (G.parents v)`，
单父假设把它收缩成两元素集合 `{v, u}`。 -/
/- 注：trap #7 —— `insert v {u} = {v, u}`。

实测（Lean/Mathlib 当前版本）：`rw [hpa] at h` 之后，
`h : ReadsOnlyOn (insert v {u}) (π v)` 与目标 `ReadsOnlyOn {v, u} (π v)`
在**定义上**已经一致，故 `exact h` 即通过。
（`simpa [Finset.insert_eq]` 会触发 `simp` 递归深度超限，勿用。） -/
theorem chain_reads_single_parent
    {G : Causalean.Graph.DAG V} (π : V → (V → Bool) → ℝ)
    (hreads : ∀ v, ReadsOnlyOn (insert v (G.parents v)) (π v))
    (v u : V) (hpa : G.parents v = {u}) :
    ReadsOnlyOn {v, u} (π v) := by
  have h := hreads v
  rw [hpa] at h
  exact h

/-- ⭐⭐⭐ **读集的单调传递**：

若 `π v` 只读 `S` 且 `S ⊆ T`，则 `π v` 只读 `T`。

这是 `Fate.T1A2.ReadsOnlyOn.mono` 的显式命名版（**⚠ 注意其参数顺序是
`mono (hST : S ⊆ T) (h : ReadsOnlyOn S f)`**，即子集关系在前）：
与 `chain_reads_single_parent` 配合，可把 `{v, u}` 扩大为任意包含它的集合
（例如整条链的顶点集）。 -/
theorem reads_mono_transfer
    (π : V → (V → Bool) → ℝ) (v : V)
     (S T : Finset V) (h : ReadsOnlyOn S (π v)) (hST : S ⊆ T) :
    ReadsOnlyOn T (π v) :=
  ReadsOnlyOn.mono hST h

/-- ⭐⭐⭐ **乘积的读集**（保守界）：

`fun x => ∏ v ∈ S, π v x` 只读 `S.biUnion (fun v => insert v (G.parents v))`。

**推断说明**：`x` 与 `y` 在该并集上一致 ⟹ 对每个 `v ∈ S`，它们在
`insert v (G.parents v)` 上一致 ⟹ 由 `hreads v` 得 `π v x = π v y` ⟹
乘积逐项相等。

**⚠ 注意这是「保守界」而非「最小界」**：它不利用 DAG 的祖先结构
（即没有把父节点的父节点传递进来）；更精细的传递上界是独立的目标。 -/
theorem prod_reads_union
    {G : Causalean.Graph.DAG V}
    (π : V → (V → Bool) → ℝ)
    (hreads : ∀ v, ReadsOnlyOn (insert v (G.parents v)) (π v))
    (S : Finset V) :
    ReadsOnlyOn (S.biUnion (fun v => insert v (G.parents v)))
      (fun x => ∏ v ∈ S, π v x) := by
  intro x y hxy
  apply Finset.prod_congr rfl
  intro v hv
  apply hreads v
  intro a ha
  exact hxy a (Finset.mem_biUnion.mpr ⟨v, hv, ha⟩)

-- ⭐ **公理审计**
#print axioms chain_reads_single_parent
#print axioms reads_mono_transfer
#print axioms prod_reads_union

end Fate.T1A2Chain
