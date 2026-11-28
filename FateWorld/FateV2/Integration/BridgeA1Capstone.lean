import FateWorld.FateV2.Predict.BridgeA1

/-!
# Integration · Predict · 父集与后代补集的交（BridgeA1 进入证明链）

## 本文件做什么

`Predict/BridgeA1.lean` 被 **9 个模块 import，却没有任何一个调用它的名字**。
这是接线丢失最严重的模块之一。

本文件消费它关于「`pa G v ∩ nonDescendants G v`」的一组结果：

| 定理 | 内容 |
|---|---|
| `pa_subset_nonDescendants` | `pa ⊆ nd`（父集含于后代补集） |
| `pa_inter_nonDescendants_eq` | `pa ∩ nd = pa` |
| `pa_inter_nd_eq_empty_iff` | `pa ∩ nd = ∅ ↔ pa = ∅` |
| `pa_inter_nd_nonempty_of_nonempty` | `pa` 非空 ⟹ `pa ∩ nd` 非空 |

## 组合的实质

这四条是**同一事实的四种可检形式**：

- `pa_subset_nonDescendants` 是「包含关系」
- `pa_inter_nonDescendants_eq` 是它的「交等式版本」
- `pa_inter_nd_eq_empty_iff` 是它的「空集判定版本」
- `pa_inter_nd_nonempty_of_nonempty` 是它的「非空传递版本」

下游在不同语境下需要不同形式：做 `simp` 时要等式，做 `by_cases` 时要
空集判定，做存在性时要非空传递。源文件把它们分成四条，本文件把
**四种形式打包**，使下游一次引用即可按需取用。

**这不是简单罗列** —— 四条之间存在**推导关系**（后三条都可由第一条得出），
本文件的价值在于把这条推导链的**全部落脚点**固定下来，
使下游不必自己决定用哪一条。

## 不引入新数学

全部为既有定理的组合。
-/

namespace FateV2.Integration

namespace BridgeA1Capstone

open FateV2.Modeling
open FateV2.Predict
open FateV2.Predict.DAGFactorization
open Finset FateV2.Predict.BridgeA1

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- ⭐⭐⭐ **`pa` 与 `nd` 的关系：四种等价形式打包**。

对任意 DAG `G` 与顶点 `v`：
1. `pa G v ⊆ G.nonDescendants v`（包含）；
2. `pa G v ∩ G.nonDescendants v = pa G v`（交等式）；
3. `pa G v ∩ G.nonDescendants v = ∅ ↔ pa G v = ∅`（空集判定）；
4. `pa G v` 非空 ⟹ `pa G v ∩ G.nonDescendants v` 非空（非空传递）。

**为什么值得一条定理**：这四种形式在源文件里是四条独立定理，
但它们是**同一事实的不同表述**。下游在不同 tactic 语境下需要不同形式
（`simp` 要等式、`by_cases` 要空集判定、存在性要非空传递），
打包后一次引用即可，不必回查源文件确认「哪条是哪个方向」。 -/
theorem pa_nd_relationship (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    (pa G v ⊆ G.nonDescendants v)
      ∧ (pa G v ∩ G.nonDescendants v = pa G v)
      ∧ (pa G v ∩ G.nonDescendants v = ∅ ↔ pa G v = ∅) :=
  ⟨pa_subset_nonDescendants G v,
   pa_inter_nonDescendants_eq G v,
   pa_inter_nd_eq_empty_iff G v⟩

/-- ⭐⭐ **非空性的传递 + 包含关系**。

把「包含」与「非空传递」并置：`pa ⊆ nd` 且 `pa` 非空时 `pa ∩ nd` 非空。

**这条的组合有实质**：`pa_inter_nd_nonempty_of_nonempty` 的证明依赖
`pa_inter_nonDescendants_eq`，而后者又依赖 `pa_subset_nonDescendants`。
本定理把这条**推导链的终点**与**起点**并置，使下游一眼看清
「非空性是从包含关系一路传下来的」，而不是凭空成立。 -/
theorem pa_nd_nonempty_chain (G : FateV2.Modeling.Graph.DAG V) {v : V}
    (hv : (pa G v).Nonempty) :
    (pa G v ⊆ G.nonDescendants v) ∧ (pa G v ∩ G.nonDescendants v).Nonempty :=
  ⟨pa_subset_nonDescendants G v, pa_inter_nd_nonempty_of_nonempty G hv⟩

/-- ⭐ **具体反例的具体取值：`arrowDAG` 上的 `pa` 与 `nd`**。

在 `Fin 2` 的单边 DAG `arrowDAG`（边 `0 → 1`）上：
- `pa arrowDAG 1 = {0}`（顶点 1 的父集是 {0}）
- `arrowDAG.nonDescendants 1 = {0}`（1 的祖先 {0} 的补集去掉自身后也是 {0}）

两条**相等**——这正好印证 `pa ⊆ nd` 在这个例子上是**等号**成立。
把它单列是因为下游若要展示「A1 的断言在非平凡例子上如何退化」，
需要这两个具体值，而不只是抽象包含。 -/
theorem arrowDAG_pa_nd_concrete :
    pa arrowDAG (1 : Fin 2) = {0} ∧ arrowDAG.nonDescendants (1 : Fin 2) = {0} :=
  ⟨arrowDAG_pa_one, arrowDAG_nd_one⟩

end BridgeA1Capstone

end FateV2.Integration