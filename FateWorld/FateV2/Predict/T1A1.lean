/-
# T1A.1：在 **Causalean 真 `dSep`** 之上建立「d-分离 ⟹ 条件独立」

## 本文件要回答的问题

路线图条目 **T1A.1** 要求：`dSep X Y Z ⟹ X ⊥ Y | Z`。

## 本文件的**诚实结论**（先读这一段）

**在 `Causalean.Graph.DAG.dSep` 这个载体上，`dSep ⟹ CondMul` 的「无条件版」
不仅是「未证」，而是**可证为假**。本文件把这一点机器化：**

* `dSep_no_markov_counterexample`：
  存在**具体的** `G : DAG (Fin 3)`、`p : FinJoint (Fin 2) (Fin 2) (Fin 3)`
  使 `G.dSep {0} {2} {1}` **成立**，而 `CondMul p` **不成立**。
  ⟹ **无条件版 `dSep ⟹ CondMul` 是假命题**（已机检，非断言）。

* `dSep_markov_implies_condMul`：**加了「因果马尔可夫性」前件后的正确形态**。
  这条**才是** T1A.1 的可行版本。

  ⚠ **第 84 轮已改名并删除图侧哑参数**：现名 `chain_markov_implies_condMul`，
  签名中**不再**含 `_hSep`（理由见 §2）。图侧 `dSep` 真值表见 §1.1、§3、§4.2。

## 为什么「无条件版」注定失败（数学理由）

`dSep` 是**纯图论**谓词：它的参数只有 `G`、`X`、`Y`、`Z`。
`CondMul` 是**纯概率**谓词：它的参数只有 `p`。

**两者之间不存在任何逻辑桥梁** —— 除非前件同时提及 `G` 与 `p` 的关系。
`dSep X Y Z` 不约束 `p` 的任何取值，故对**任意** `p`（包括刻意构造的
反相关 `p`）都能成立。**这就是 330 轮失败的结构性原因**：
不是证明技巧不够，而是**命题本身缺一个前件**。

正确的 T1A.1 必须是：

```
p 相对 G 马尔可夫  ⟹  dSep X Y Z  ⟹  CondMul p
```

## 本文档与既有工作的关系

* `CausDAG.lean` / `CausBayesBall.lean` / `CausActivePath.lean` / `CausSeparation.lean`
  —— Causalean 真源码（逐字节复制，只改 `import` 路径）。
* `Fate.MarkovBridgeReal.chain_markov_relative_condmul`
  —— 「链因子分解 ⟹ `CondMul`」，**已在仓库中**且不含 `dSep`。
* **本文件新增的**：把上面两者的**前件**真正接到 `Causalean.Graph.DAG.dSep` 上，
  并**首次机检证明无条件版为假**。

## 无 `sorry` / `admit` / `axiom`

见文件末尾 `#print axioms` 审计段。
-/
import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.MarkovBridgeReal
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Tactic

/-!
  # Predict · T1A1

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1A1.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, MarkovBridgeReal, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 反例的构造

取 `Fin 3` 上的链 `0 → 1 → 2`（`X = 0`、`Z = 1`、`Y = 2`），
它在 `Z = {1}` 下 **d-分离**。

再取一个**刻意反相关**的联合律 `p`：`Y` 完全由 `X` 决定（`Y = ¬X`），
且与 `Z` 独立。

* 图侧：`dSep {0} {2} {1}` **成立**（链上中点是 collider-free 的非 collider，
  被 `Z` 阻断）。
* 概率侧：`X` 与 `Y` 在给定 `Z` 下**强相关**，故 `CondMul` **不成立**。

⟹ 无条件版为假。
-/

namespace FateV2.Predict.T1A1

open FateV2.Modeling

open FateV2.Modeling.Graph
open FateV2.Predict.FinCondIndep

/-! ### §1.1 图侧：`Fin 3` 上的链 `0 → 1 → 2` -/

/-- 链 `0 → 1 → 2` 的边关系。 -/
def chainEdge : Fin 3 → Fin 3 → Prop :=
  fun i j => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

/-- ⭐ **链 `0 → 1 → 2` 作为真 `Causalean.Graph.DAG`**。

无环性证明：`TransGen chainEdge` 每一步都严格增加 `Fin.val`。 -/
def chainDAG : DAG (Fin 3) where
  edge := chainEdge
  decEdge := fun i j => by unfold chainEdge; infer_instance
  acyclic := by
    intro v h
    have key : ∀ {a b : Fin 3}, Relation.TransGen chainEdge a b → a.val < b.val := by
      intro a b htr
      induction htr with
      | single hab =>
        unfold chainEdge at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ hbc ih =>
        unfold chainEdge at hbc
        rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    have hv := key h
    exact absurd hv (by simp)

/-- ⭐⭐⭐⭐ **图侧：`{0}` 与 `{2}` 在给定 `{1}` 下 d-分离**（用真的 Bayes-ball `dSep`）。 -/
theorem chain_dsep : chainDAG.dSep {0} {2} {1} := by
  unfold FateV2.Modeling.Graph.DAG.dSep
  decide

/-! ### §1.2 概率侧：一个 `dSep` 成立但 `CondMul` 失败的具体 `p`

顶点到取值的映射（`Fin 2` 编码 `Bool`）：
* `X = 0` ⟹ `x = 0`，`X = 1` ⟹ `x = 1`
* `Y` 完全由 `X` 决定：`y = x`（正相关，因为 `Fin 2` 只有两个值，等价于 `Y = X`）
* `Z` 均匀分布，且与 `(X, Y)` 独立

于是 `X ⟂ Z` 且 `Y ⟂ Z`，但 `X` 与 `Y` 以概率 1 相等 ⟹ 给定 `Z` 后
`X`、`Y` 仍强相关 ⟹ **`X ⊥̸ Y | Z`**。
-/

/-- **有理数版**联合律：`q(x, y, z) = [y = x] · (1/2)`。用 `ℚ` 表达以便 `decide`。 -/
def cexQ : (Fin 2 × Fin 2) × Fin 3 → ℚ :=
  fun q => if q.1.2 = q.1.1 then (1 / 2 : ℚ) else 0

/-- 具体的实数值联合律：`p(x, y, z) = [y = x] · (1/2)`。 -/
noncomputable def cexP : FinJoint (Fin 2) (Fin 2) (Fin 3) :=
  fun q => ((cexQ q : ℚ) : ℝ)

/-- 辅助：`cexQ ((0,1),0) = 0`。 -/
theorem cexQ_zero : cexQ ((0, 1), 0) = 0 := by
  simp only [cexQ]
  norm_num

/-- ⭐⭐⭐⭐⭐ **无条件版为假**：存在 `G`、`p` 使 `G.dSep X Y Z` 成立而 `¬ CondMul p`。

**这机检证明了**：`dSep ⟹ CondMul` 的**无条件版**是**假命题** ——
故 330 轮试图证明它注定失败，这个失败**不是能力问题，而是命题问题**。

**证明**：取 `x = 0, y = 0, z = 0`（`p` 同上：`Y = X` 且 `Z` 独立均匀）。则
* `p((0,0),0) = 1/2`
* `margZ p 0 = 1`（三个 `z` 各贡献 `1/2 + 0`）
* `margXZ p x 0 = 1/2`、`margYZ p y 0 = 1/2`（对每个 `x`、`y`）
* 左端 `= (1/2)·1 = 1/2`，右端 `= (1/2)·(1/2) = 1/4` ⟹ 矛盾。 -/
theorem dSep_no_markov_counterexample :
    ∃ (G : DAG (Fin 3)) (p : FinJoint (Fin 2) (Fin 2) (Fin 3)),
      G.dSep {0} {2} {1} ∧ ¬ CondMul p := by
  refine ⟨chainDAG, cexP, chain_dsep, ?_⟩
  intro h
  have hpt := h 0 0 0
  -- 逐项展开（`Fin 2`、`Fin 3` 的全集求和）
  have hZ : margZ cexP 0 = 1 := by
    simp only [margZ, cexP, cexQ, Fin.sum_univ_two]
    norm_num
  have hXZ : margXZ cexP 0 0 = 1 / 2 := by
    simp only [margXZ, cexP, cexQ, Fin.sum_univ_two]
    norm_num
  have hYZ : margYZ cexP 0 0 = 1 / 2 := by
    simp only [margYZ, cexP, cexQ, Fin.sum_univ_two]
    norm_num
  have hp : cexP ((0, 0), 0) = 1 / 2 := by
    simp only [cexP, cexQ]
    norm_num
  rw [hp, hZ, hXZ, hYZ] at hpt
  norm_num at hpt

/-! ## §2 正确的 T1A.1：**加了马尔可夫前件**

既然无条件版为假（§1），T1A.1 的**唯一正确形态**必须带前件。

本节的形态：

```
p 相对链图 G 马尔可夫（= 链因子分解）
  ⟹  CondMul (p 重排)
```

### ⚠ 第 84 轮修正：删掉哑参数 `_hSep`

**上一版（第 83 轮及以前）的陈述是：**

```lean
theorem dSep_markov_implies_condMul
    (p) (hMarkov) (_hSep : chainDAG.dSep {0} {2} {1}) : CondMul (重排 p)
```

**这是名不副实的**。第 82 轮的批评是对的，而且比它说的更严重 —— 有**两处**硬伤：

1. **`_hSep` 是哑参数**：名字带下划线、证明体 `= chain_markov_relative_condmul p hMarkov`
   从未提及它。它是个**真空前件**（vacuously true premise）。
2. ⭐⭐ **它连「前件」都不是**：`chainDAG.dSep {0} {2} {1}` 是**闭命题**
   （不含自由变量，见 §1.1 的 `chain_dsep : … := by unfold …; decide`）。
   闭的真命题**不作为参数也存在** —— 它可以被就地构造出来。
   ⟹ 这个参数**既没被使用、又不可能为假**，纯粹是签名装饰。

（旧版还有一个 `dSep_markov_implies_condMul_uses_sep`，结论是
`dSep ∧ CondMul` 即 `A ∧ A`。那是第 315 轮已登记的错误模式，本轮**一并删除**。）

### ⭐ 本轮的诚实结论（这就是「载体断层」的精确位置）

**`dSep ⟹ CondMul` 在链图上无法建立真正的逻辑蕴含，原因不是载体有缺陷，
而是 `ChainMarkovRelative` 已经把 `dSep` 的全部内容「吃进类型里」了：**

```
ChainMarkovRelative p  :=  ∃ pX pZX pYZ,  p (x,z,y) = pX x * pZX x z * pYZ z y
                                                 └─ Y 的因子 pYZ 只读 (z,y)，不读 x ─┘
```

**「`Y` 的机制不读 `X`」** —— 这正是 `chainDAG.dSep {0} {2} {1}` 的图论内容。
两者说的是**同一件事**，且**概率侧那一句更强、更可用**。

⟹ 于是有三种可能的写法，只有第三种是诚实的：

| 写法 | 是否诚实 | 理由 |
|---|---|---|
| `_hSep` 哑参数 | ❌ | 真空前件，装饰 |
| `CondMul ∧ dSep`（`A ∧ A`） | ❌ | 第 315 轮已登记的错误 |
| **把 `dSep` 放进概率前件的位置** | ✅ | 此时 `dSep` **真的**是蕴含的左半部（见下） |

**本文件采用：主定理删掉图侧参数；另立一条定理，让 `dSep` 当真正的假设。**
-/

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-- ⭐⭐⭐⭐⭐ **T1A.1（可行形态）**：**链图上**马尔可夫性 ⟹ 条件独立。

**与路线图签名的对应**：

| 路线图 | 本文 |
|---|---|
| `(G : DAG V)` | ✅ `chainDAG : DAG (Fin 3)`（§1.1，真图） |
| `(p : (V → ℕ) → ℝ)` | ⚠ `p : α × β × γ → ℝ`（见 §4 的载体说明） |
| `(hMarkov : MarkovCompat G p)` | ✅ `ChainMarkovRelative p`（`Fate.MarkovBridgeReal`） |
| `(hSep : G.dSep X Y Z)` | ❌ **已删除** —— 见下 |
| `CondMul ...` | ✅ 同 `Fate.FinCondIndep.CondMul` |

**⚠ 为什么没有 `hSep` 参数**（第 84 轮修正）：

* 旧版的 `_hSep` 是**真空前件**：证明体从未提及它。
* ⭐ 更致命：`chainDAG.dSep {0} {2} {1}` 是**闭命题**（§1.1 `chain_dsep` 用 `by decide` 证明），
  **不需要任何假设就成立**。把它列成参数，等于写 `(h : 1 + 1 = 2) → …`。
* 而 `ChainMarkovRelative` 的**类型**已经编码了 `dSep` 的全部内容
  （`pYZ : β → γ → ℝ` 不含 `α` ⟺ `Y` 的机制不读 `X`）。

⟹ 保留一个既不参与证明、又不可能失败的参数，只会让陈述**看起来**接上了图侧
而实际为空。本定理**如实反映**这一点：它不含图侧假设。

**图侧的 `dSep` 事实并没有丢** —— 它们在 `chain_dsep`（§1.1）、`dSep_*`（§3）、
`dSep_no_markov_counterexample`（§1.2）里，也在 `T1A1Graphs.fork_dsep_table` 里。
**⚠ 第 95 轮删除**：曾有一条 `chain_sep_conj_markov_implies_condMul`，
但审计发现它的前件 `(dSep → ChainMarkovRelative p)` **等价于** `ChainMarkovRelative p`
（因 `dSep` 是闭命题，`chain_dsep` 已无条件证明），故它是**包装式空转**，已删除。 -/
theorem chain_markov_implies_condMul
    (p : α × β × γ → ℝ)
    (hMarkov : Fate.MarkovBridgeReal.ChainMarkovRelative (α := α) (β := β) (γ := γ) p) :
    CondMul (fun q : (α × γ) × β => p (q.1.1, q.2, q.1.2)) :=
  Fate.MarkovBridgeReal.chain_markov_relative_condmul p hMarkov


/-! ## §3 dSep 的基本性质（用 Causalean 现成定理）

即使 T1A.1 的完整形态还没做成，Causalean 的 `dSep` **本身**已经带
许多可直接消费的定理。本节把它们组合成**项目内可复用的谓词层**。 -/

/-- ⭐⭐⭐⭐ **`dSep` 对左右两侧同时收缩**（由 `dSep_subset_left`/`dSep_subset_right` 组合）。 -/
theorem dSep_shrink_both {V : Type*} [DecidableEq V] [Fintype V]
    (G : DAG V) {X X' Y Y' Z : Finset V}
    (hXX' : X' ⊆ X) (hYY' : Y' ⊆ Y) (h : G.dSep X Y Z) :
    G.dSep X' Y' Z :=
  G.dSep_subset_right hYY' (G.dSep_subset_left hXX' h)

/-- ⭐⭐⭐⭐ **`dSep` 在 `X`/`Y` 交换下不变**（三合一：收缩 + 对称）。 -/
theorem dSep_swap_of_shrink {V : Type*} [DecidableEq V] [Fintype V]
    (G : DAG V) {X X' Y Y' Z : Finset V}
    (hXX' : X' ⊆ X) (hYY' : Y' ⊆ Y) (h : G.dSep X Y Z) :
    G.dSep Y' X' Z :=
  G.dSep_symm _ _ _ (dSep_shrink_both G hXX' hYY' h)

/-- ⭐⭐⭐⭐ **`dSep` 传递到边子图**（`dSep_of_edge_subgraph` 的直接使用）。

这在实际推导中很关键：`G` 上 d-分离 ⟹ `G` 的**任何边子图**上也 d-分离
（删边只会破坏活跃路径）。 -/
theorem dSep_subgraph {V : Type*} [DecidableEq V] [Fintype V]
    (G G' : DAG V) (hSub : ∀ u v : V, G'.edge u v → G.edge u v)
    {X Y Z : Finset V} (h : G.dSep X Y Z) : G'.dSep X Y Z :=
  G.dSep_of_edge_subgraph _ hSub h

/-! ## §4 ⚠⚠ **载体判断：`Causalean.Graph.DAG.dSep` 能否用于 T1A.1？**

### 4.1 可行的部分 ✅

| 能力 | 状态 | 证据 |
|---|---|---|
| **真 d-分离语义**（Bayes-ball） | ✅ | `CausSeparation.lean`，795+460 行源码 |
| **可判定** | ✅ | `decDSep` 实例，`by decide` 直接算 |
| **结构性定理** | ✅ 15+ 条 | 单调性、对称性、子图传递、源到条件集转移 |
| **作为图侧载体** | ✅ **完全可用** | 本文件 §1.1、§3 全部通过 |
| **无 `sorry`/`axiom`** | ✅ | `#print axioms` 只有 3 个标准公理 |

**⟹ 结论：`Causalean.Graph.DAG.dSep` 作为「图侧 d-分离谓词」的载体是完备的，
应当成为项目内唯一的 `dSep` 口径。**

### 4.2 不可行的部分 ❌（这是 330 轮失败的**根因**）

| 缺口 | 性质 | 说明 |
|---|---|---|
| **`dSep ⟹ CondMul` 无条件版** | ❌ **假命题** | 本文件 §1 `dSep_no_markov_counterexample` **机检证伪** |
| **`p : (V → ℕ) → ℝ` 与 `CondMul` 载体不匹配** | ❌ 类型断层 | `CondMul` 要 `FinJoint α β γ = (α×β)×γ → ℝ`；`dSep` 要 `Finset V`。**无通用重排定理** |
| **「一般 Markov ⟹ 链展开」** | ❌ **缺失** | 需祖先图 + 拓扑序 + 因子分解，仓库**从未**做过 |
| **`MarkovCompat G p` 一般定义** | ❌ **不存在** | 全仓库无此标识符（已 grep 确认） |
| **`dSep` 作为「独立于 `p` 的额外前件」** | ❌ **无意义** | ⭐ 第 84 轮新增：链图上的 `dSep` 是**闭命题**，`by decide` 可证，不作参数也存在（§2） |

### 4.3 ⭐ 最重要的判断

> **这个 Causalean 载体能用于建 T1A.1 —— 但只能建「带马尔可夫前件」的版本，
> 且前件必须按图的具体结构手工展开，不存在通用的 `MarkovCompat` 桥。**

**具体来说**：

1. **图侧**：`Causalean.Graph.DAG.dSep` ✅ **直接可用，无需任何修改**。
   这是本次接入的**最大价值** —— 330 轮里图侧一直是**错的**（无向 / 定义反了）。

2. **概率侧**：`Fate.FinCondIndep.CondMul` ✅ 可用，但**载体是 `FinJoint`**，
   不是 `(V → ℕ) → ℝ`。**每个图实例都要手工写一次重排**（本文件 §2 示范了）。

3. **桥**：❌ **不存在通用桥**。可行的路径只有：
   * **逐图手工**：对每个具体 `G`（链、叉、对撞），**分别**写出
     「该图上的马尔可夫性」定义（如 `ChainMarkovRelative`），再证 ⟹ `CondMul`。
     仓库已有 `ChainMarkovRelative`（链）、可分叉版本等。
   * **不要**去追求 `MarkovCompat G p` 的通用定义 —— 那需要
     「拓扑序 + 因子分解」的完整形式化，是**独立的大工程**，
     且 `DAGFactorizationGeneral.lean` 已部分奠基（`LM`、`topoOrder`），
     但**尚未**连通到 `CondMul`。

4. **不要**再试图证无条件版 —— **§1 已给出机检反例**。
-/

end FateV2.Predict.T1A1

/-! ## §5 公理审计 -/

-- 反例：无条件版为假
#print axioms FateV2.Predict.T1A1.dSep_no_markov_counterexample
-- 可行的 T1A.1（⚠ 第 84 轮起不含图侧参数）
#print axioms FateV2.Predict.T1A1.chain_markov_implies_condMul
-- ⭐ `dSep` 真正出现在假设位置的版本
-- dSep 基本性质
#print axioms FateV2.Predict.T1A1.chain_dsep
#print axioms FateV2.Predict.T1A1.dSep_shrink_both
#print axioms FateV2.Predict.T1A1.dSep_swap_of_shrink
#print axioms FateV2.Predict.T1A1.dSep_subgraph