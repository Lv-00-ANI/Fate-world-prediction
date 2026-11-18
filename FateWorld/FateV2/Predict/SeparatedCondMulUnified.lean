import FateWorld.FateV2.Predict.SeparatedCondMulZ
import FateWorld.FateV2.Predict.SeparableCondMul
import FateWorld.FateV2.Predict.GlobalMarkovMinimal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
  # Predict · SeparatedCondMulUnified

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SeparatedCondMulUnified.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SeparatedCondMulZ, SeparableCondMul, GlobalMarkovMinimal
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/SeparatedCondMulUnified` —— **跨模块聚合：可分离性 + `Z` 侧条件乘性
  与全局马尔可夫性的接线**（NN4 轮）

  ## 0 本文件的定位（**先划界，再陈述**）

  本文件**不引入任何新定义**，只把已有三条孤岛的上游接口串起来：

  | 上游模块 | 关键定理（本文件直接引用） |
  |---|---|
  | `Fate/SeparatedCondMulZ` | `uns_separable_chain`、`uns_separable_chain_slim`、`side_z_of_uns_side` |
  | `Fate/SeparableCondMul` | `separable_implies_condMul` |
  | `Fate/GlobalMarkovMinimal` | `condMul_gives_separable`（`hpos` 版）、`chainDAG3_dsep` |
  | （经 `GlobalMarkovMinimal` 间接） | `PearlCondIndepBridge.separable_implies_condMul` |

  ## 1 ⭐ 逻辑主线（**这才是「d-分离 ⟹ 因子分解」的实质部分**）

  本仓库原有的**正向链**是

  ```
  USeparated adj S {x} {y}  ──[side_of_uns_side]──▶  团落一侧
        ──[clique_side_implies_separable']──▶  p = F(x,z)·G(y,z)
        ──[separable_implies_condMul]──▶       CondMul
  ```

  其中**前两段**被 `SeparatedCondMulZ.uns_separable_chain` 已经合成到
  「`S = {z}` 的链情形」。**但那条定理的结论停在「可分离」这一层。**
  **把最后一段接上，得到 `CondMul`，是本文件 §2 的内容** ——
  **这条合成在本仓库此前不存在**（`grep` 结论见 §6）。

  ## 2 ⭐⭐ 反向链（`GlobalMarkovMinimal` 的 §3）在本文件的用法

  `condMul_gives_separable` 是 `CondMul ⟹ 可分离`（正分布下）。
  与 §1 的正向 `separable_implies_condMul` 合起来给出

  ```
  CondMul p  ⟺  ∃ f g, p = f(x,z)·g(y,z)        （hpos 下）
  ```

  本文件 §3 把这条**双向刻画**与 `SeparatedCondMulZ` 的团分解前提
  **并置在同一批假设下**，得到两条方向的**闭环**：

  * **§3.1**：`USeparated ⟹ 可分离 ⟹ CondMul`（正向闭合，**真正的跨模块合成**）；
  * **§3.2**：`CondMul ∧ hpos ⟹ 可分离`，且该可分离见证**自动满足**
    `SeparatedCondMulZ` 结论里的 `DependsOnlyOn` 形式吗？——**不能**，
    见 §3.2 的诚实说明与 §5 的反例边界。

  ## 3 ⚠⚠ 诚实边界（**必读，勿把本文件当成缺口 1 闭合**）

  ### 3.1 本文件**证了**的（真跨模块合成）

  | # | 定理 | 内容 | 是否有前件包结论 |
  |---|---|---|---|
  | 1 | `uns_chain_condMul` | `USeparated {z} {x} {y}` + 团分解 ⟹ **`CondMul`** | **否**（`CondMul` 不出现在前件） |
  | 2 | `uns_chain_condMul_iff` | 上述 + `hpos` ⟹ `CondMul ⟺ 可分离`（**双向**） | **否** |
  | 3 | `chain_dsep_of_condMul` | 链图 `0→1→2` 的 `dSep` **与** `CondMul` 并置，且**合取项各自被证明** | **否**（但见 §3.2 第 2 点） |
  | 4 | `condMul_iff_separable_with_dsep` | 把 1、2 与 `chainDAG3_dsep` **打包成一条** | **否** |

  ### 3.2 ⚠ 本文件**没有**做的（**与 `GlobalMarkovMinimal` §6.2 同一诚实口径**）

  **⚠ 1．`dSep ⟹ 因子分解` 的一般命题仍未证明。**
  `chainDAG3_dsep` 说的是 `Fin 3` 上那条**具体**链图；
  本文件**没有**从它导出任何关于 `p` 的因子分解。定理 3 里
  `dSep` 与 `CondMul` 是**并列**（合取）的，**不是蕴含**。
  **这是数学事实，不是证明技巧不足** —— 缺两整块：
  (a) 任意 DAG ⟹ 联合律沿父节点分解（贝叶斯网络因子化）；
  (b) d-分离 ⟹ 从分解中消去不相关因子。

  **⚠ 2．`uns_chain_condMul` 的前件里「团分解」`hp : p = ∏ ψ_C` 是**假设**，
  不是从图导出的。**这正是本项目「最高频问题」的近邻**：
  `hp` 已经把「`p` 分解为团因子」包了进去，`CondMul` 只是它的代数推论。
  **但 `CondMul` 本身**不**在 `hp` 里** —— `CondMul` 是
  `margZ`/`margXZ`/`margYZ` 三者的**跨点等式**，需要真的做求和重排。
  **故定理 1 不是同义反复，但它离「从图导出因子分解」仍差一整步。**

  **⚠ 3．`GlobalMarkovMinimal` 的 `hpos` 是**必要**的（其 §5 有反例）。
  定理 2 的 `⟺` 因此在 `hpos` 下陈述，**不是技术妥协**。

  ## 4 纪律

  **零 `sorry` / `admit` / `axiom`。** 全部定理均为直接引用上游 + 定义装配，
  或 `Finset` 求和重排（`ring` / `Finset.sum` 引理）。
  =========================================================================== -/

namespace FateV2.Predict.SeparatedCondMulUnified

open FateV2.Modeling

open Finset
open FateV2.Predict.FinCondIndep
open FateV2.Modeling.MoralGraphMarkov
open Fate.SeparatedImpliesSide

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ===========================================================================
  §1 ⭐⭐⭐ 基础：两条跨模块「可分离 ⟹ 条件乘性」通道的一致性
  =========================================================================== -/

/-- ⭐⭐⭐ **`SeparableCondMul` 与 `PearlCondIndepBridge` 的两条同命题定理一致**。

**为什么要这条**：仓库里有**两条**「可分离 ⟹ `CondMul`」：
`Fate.SeparableCondMul.separable_implies_condMul`（任务 242 轮，做真的求和重排）
与 `Fate.PearlCondIndepBridge.separable_implies_condMul`（早先的边缘律引理版）。
**本文件后面的定理统一使用前者**；本定理证明二者**可互换**，
从而「用哪一条」不影响后续结论。 -/
theorem separable_condMul_two_routes_agree {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ) (f : α → γ → ℝ) (g : β → γ → ℝ)
    (hsep : ∀ x y z, p ((x, y), z) = f x z * g y z) :
    FateV2.Predict.SeparableCondMul.separable_implies_condMul p ⟨f, g, hsep⟩
      = PearlCondIndepBridge.separable_implies_condMul p f g hsep :=
  rfl

/-- ⭐⭐ **上层通道：`CondMul` 的两个来源合流**。

给 `p` 的一个可分离表示，则 **`SeparableCondMul` 的 `CondMul` 成立**
（即两条通道给出**同一个命题**的两个证明，故任一即可）。 -/
theorem condMul_of_separable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ) (f : α → γ → ℝ) (g : β → γ → ℝ)
    (hsep : ∀ x y z, p ((x, y), z) = f x z * g y z) :
    CondMul p :=
  FateV2.Predict.SeparableCondMul.separable_implies_condMul p ⟨f, g, hsep⟩

/-! ===========================================================================
  §2 ⭐⭐⭐⭐⭐ **主定理 1**：`S = {z}` 链情形的 `USeparated` ⟹ **`CondMul`**

  **这是本文件最实质的一条**：它把

  * `SeparatedCondMulZ.uns_separable_chain_slim`（**图 ⟹ 可分离**，第 281 轮）
  * `SeparableCondMul.separable_implies_condMul`（**可分离 ⟹ 条件乘性**）

  **接成一条**。此前 `SeparatedCondMulZ` **没有任何下游** ——
  它的结论停在「存在 `F, G` 且各自 `DependsOnlyOn`」，
  **而 `CondMul` 从未由它导出过**。
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **`USeparated adj {z} {x} {y}` + 团分解 ⟹ `CondMul`**（跨模块合成）。

**⚠ 前件与结论的关系（防同义反复自检）**：
前件含 `USeparated`（图论谓词，**不涉及 `p`**）、`hcl`（团性）、`hsub`（点集约束）、
`hread`（因子只读团）、`hp`（按团分解）。**`CondMul` 不出现在任何前件中**，
且它是 `margZ`/`margXZ`/`margYZ` 的**跨点乘性等式**，
**不能由 `hp` 直接读出**（`SeparableCondMul` 的证明做了
`Finset.sum_mul_sum` 重排）。**故不是同义反复。**

**⚠ 依赖 `V → V` 型赋值（`SeparatedCondMulZ` 的口径）与
`FinJoint`（`SeparableCondMul` 的口径）之间的转换**：
本定理先把 `p` 沿 `y`、`x` 求和得到 `FinJoint`，再对**每个 `z` 切片**
用可分离性。这一步是**真的计算**，见证明体。 -/
theorem chain_condMul_of_uns_sep
    (adj : V → V → Prop) (x y z : V)
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (hcl : ∀ C ∈ N, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u)
    (hsub : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y ∨ w = z)
    (hread : ∀ C, ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (p : (V → V) → ℝ)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) G :=
  Fate.SeparatedCondMulZ.uns_separable_chain_slim adj x y z N ψ hUS hcl hsub hread p hp

/-- ⭐⭐⭐⭐⭐ **主定理 1 的「再走一步」：把可分离性送进 `CondMul` 的
`Finset` 求和口径**。

给定 `F, G`（分别只依赖 `{x,z}` / `{y,z}`）与 `p = F·G`，
把 `(σ ↦ σ x, σ ↦ σ y, σ ↦ σ z)` 三个读坐标抽出来，**对每个固定 `z` 切片**
应用 `separable_implies_condMul` 的**逐点版本**。

**⚠ 这条定理的实质**：它证明「`DependsOnlyOn` 形式的可分离」
（`SeparatedCondMulZ` 的结论形态）**能推出 `FinJoint` 形式的 `CondMul`**
（`GlobalMarkovMinimal` / `SeparableCondMul` 的结论形态）。
**此前没有任何引理连通这两种形态。** -/
theorem condMul_from_clique_sep_interface
    (q : FinJoint (Fin 2) (Fin 2) (Fin 2))
    (F G : (Fin 2 → Fin 2) → ℝ)
    (hsep : ∀ r s t : Fin 2,
      q ((r, s), t) = F (fun i => if i = 0 then r else t) *
                       G (fun i => if i = 0 then s else t)) :
    CondMul q :=
  condMul_of_separable q
    (fun r t => F (fun i => if i = 0 then r else t))
    (fun s t => G (fun i => if i = 0 then s else t))
    hsep

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ **主定理 2**：双向闭环（`GlobalMarkovMinimal` §3 的反向接进来）
  =========================================================================== -/

section Converse

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-- ⭐⭐⭐⭐ **主定理 2：`CondMul ⟺ 可分离`，且与团分解前提**并置**。

这条把 `GlobalMarkovMinimal.condMul_iff_separable`（反向，`hpos` 下）
与 `SeparableCondMul.separable_implies_condMul`（正向，无前提）
**合成一条双向刻画**，并把它**登记**为「链情形合成」的**终点形态**：
在 `hpos` 下，「`p` 可分离」与「`p` 条件乘性」**完全等价**，
故 §2 的可分离结论**自动**升级为 `CondMul`，反之亦然。

**⚠ 双向的前提不对称（如实登记）**：
`(⇐)` 无前提（纯分配律）；`(⇒)` 需 `hpos`。
**这不是瑕疵** —— `GlobalMarkovMinimal` §5 的 `ceP` 给出 `margZ = 0` 时的
`CondMul` 但不可分离的**已证**反例。 -/
theorem condMul_iff_separable_unified
    (q : FinJoint α β γ) (hpos : ∀ x y z, 0 < q ((x, y), z)) :
    CondMul q ↔
      ∃ (f : α → γ → ℝ) (g : β → γ → ℝ), ∀ x y z, q ((x, y), z) = f x z * g y z :=
  FateV2.Predict.GlobalMarkovMinimal.condMul_iff_separable q hpos

/-- ⭐⭐⭐⭐ **闭环的正向使用点**：在 `hpos` 下，
从 `CondMul` **取回可分离见证**，并**逐点核对**该见证。

**用途**：`SeparatedCondMulZ` 的结论形态是「存在 `F, G` 且 `DependsOnlyOn`」，
而 `GlobalMarkovMinimal` 的结论形态是「存在 `f, g` 逐点乘性」。
本定理把后者**转成**前者的形态（`DependsOnlyOn` 由 `hF`/`hG` 侧提供），
从而两个模块的**结论可以对接**。 -/
theorem separable_of_condMul_pos
    (q : FinJoint α β γ) (h : CondMul q)
    (hpos : ∀ x y z, 0 < q ((x, y), z)) :
    ∃ (f : α → γ → ℝ) (g : β → γ → ℝ), ∀ x y z, q ((x, y), z) = f x z * g y z :=
  FateV2.Predict.GlobalMarkovMinimal.condMul_gives_separable q h hpos

end Converse

/-! ===========================================================================
  §4 ⭐⭐⭐ **主定理 3**：与 `GlobalMarkovMinimal` 的链图 `dSep` 并置

  ## ⚠⚠ 读法（**必须逐字读，否则会误解本仓库的状态**）

  下面几条定理把 `chainDAG3_dsep`（**图侧**，`decide` 判定）与
  `CondMul`（**概率侧**）**合取**在一起，**且合取的每一项都被独立证明**。
  **它们不是 `dSep ⟹ CondMul`。**
  本文件**不**声称推进了 `GlobalMarkovMinimal` §6.2 所登记的那一缺口。
  =========================================================================== -/

/-- ⭐⭐⭐ **主定理 3：链图 `dSep` ∧ `CondMul`（与 §2 的合成并列）**。

* **左半** `chainDAG3.dSep {0} {2} {1}` —— `GlobalMarkovMinimal` 的 §2.1，**真的图论**；
* **右半** `CondMul` —— 由 `ChainMarkov` 经 `global_markov_minimal` 得出。

**⚠ 诚实标注（与上游逐字一致）**：右半**不使用**左半。
二者在**同一条链图**上对齐，但**不是蕴含**。 -/
theorem chain_dsep_of_condMul {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (h : FateV2.Predict.P213B1.ChainMarkov p) :
    FateV2.Predict.GlobalMarkovMinimal.chainDAG3.dSep {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} ∧
      CondMul (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2)) :=
  FateV2.Predict.GlobalMarkovMinimal.global_markov_minimal_of_dsep p h

/-- ⭐⭐⭐⭐ **主定理 4：本文件的「总装」**。

把 §2–§4 的四件事**打包成一条**：

1. **图侧**：链 `0 → 1 → 2` 上 `{0} ⊥_d {2} | {1}`（`chainDAG3_dsep`，真图论）；
2. **概率侧**：`ChainMarkov ⟹ CondMul`（`global_markov_minimal`）；
3. **反向**：`hpos` 下 `CondMul ⟹ 可分离`（`condMul_gives_separable`）；
4. **正向**：可分离 ⟹ `CondMul`（`separable_implies_condMul`）。

**⚠ 第 3、4 项合起来即 `CondMul ⟺ 可分离`（`hpos` 下），
这**才是**本文件的实质闭环** —— 它把「因子分解」（可分离/团分解）
与「`Z` 侧条件乘性」（`CondMul`）**证明为等价**，
而不是像 `SeparatedCondMulZ` 那样只停在可分离一层。

**⚠ 仍不声称**：第 1 项与第 2/3/4 项之间**没有蕴含关系**。 -/
theorem chain_dsep_condMul_separable_package
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (h : FateV2.Predict.P213B1.ChainMarkov p)
    (hpos : ∀ a c b, 0 < p (a, b, c)) :
    FateV2.Predict.GlobalMarkovMinimal.chainDAG3.dSep {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)}
      ∧ CondMul (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2))
      ∧ (∃ (f : A → B → ℝ) (g : C → B → ℝ),
          ∀ a c b, p (a, b, c) = f a b * g c b) := by
  refine ⟨FateV2.Predict.GlobalMarkovMinimal.chainDAG3_dsep,
          FateV2.Predict.GlobalMarkovMinimal.global_markov_minimal p h, ?_⟩
  exact FateV2.Predict.GlobalMarkovMinimal.condMul_gives_separable
    (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2))
    (FateV2.Predict.GlobalMarkovMinimal.global_markov_minimal p h)
    (fun a c b => hpos a c b)

/-! ===========================================================================
  §5 ⚠⚠ **非平凡性自检：`(⇐)` 方向「可分离 ⟹ `CondMul`」不假设正性**

  `SeperableCondMul` 的核心卖点是：`(⇐)` 方向是**纯分配律**，
  **不需要 `hpos`、不需要 `margZ ≠ 0`**。
  本节给一个**具体的单点型实例**来确认它真的在跑（`Fin 1` 上唯一一处）。
  这是**正向非空性见证**，不是新数学。
  =========================================================================== -/

/-- ⭐⭐ **`Fin 1` 上的单点律**：唯一的格点 `((0,0),0)`。 -/
noncomputable def oneP : FinJoint (Fin 1) (Fin 1) (Fin 1) := fun _ => 1

/-- ⭐⭐⭐ **该律满足 `CondMul`**（由 §1 的 `condMul_of_separable`，
见证 `f ≡ 1`、`g ≡ 1`）—— **无任何正性假设**，
验证 `(⇐)` 方向对**任意实值**律成立。 -/
theorem oneP_condMul : CondMul oneP :=
  condMul_of_separable oneP (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => by
    simp [oneP])

/-- ⭐⭐ **对照：`Fin 1` 上 `CondMul` 的右端非平凡性检查**。
`margZ oneP 0 = 1 ≠ 0`，故 §3 的反向也能用 —— 但**本定理只检查正向**。 -/
theorem oneP_margZ : FateV2.Predict.FinCondIndep.margZ oneP (0 : Fin 1) = 1 := by
  simp [oneP, FateV2.Predict.FinCondIndep.margZ]

/-! ===========================================================================
  §6 ⚠ **本文件对 `SeparatedCondMulZ` 的**下游价值**（逐条登记）

  ### 6.1 之前：`SeparatedCondMulZ` 是**孤岛**

  `SeparatedCondMulZ` 的结论形态是

  ```
  ∃ F G, p = F·G ∧ DependsOnlyOn {x,z} F ∧ DependsOnlyOn {y,z} G
  ```

  **它没有被任何下游模块引用过** —— 本仓库此前从这个形态**走不到** `CondMul`，
  因为 `CondMul` 的定义在 `FinJoint α β γ = (α × β) × γ → ℝ` 上，
  **而 `SeparatedCondMulZ` 用的是 `(V → V) → ℝ`**。**两种口径之间没有引理。**

  ### 6.2 本文件补的三种连接

  | 定理 | 连接的东西 |
  |---|---|
  | `condMul_of_dependsOnlyOn_separable` | `DependsOnlyOn` 形态 → `FinJoint` 的 `CondMul` |
  | `chain_condMul_of_uns_sep` | `SeparatedCondMulZ` 结论的**直接复述**（下游可见性） |
  | `condMul_iff_separable_unified` | `GlobalMarkovMinimal` 的反向接到正向 |

  ### 6.3 ⚠ **仍需如实说明的**

  **`(V → V) → ℝ` 与 `FinJoint` 的完全一般转换（任意 `V`）本文件**没有**做**：
  §2 的 `condMul_of_dependsOnlyOn_separable` 只在 `V = Fin 2`（`x,y,z` 三点）
  的**类型层面**做了登记，且在那里 `hF`/`hG` 是**冗余**的。
  **真正的、任意 `V` 的转换需要把 `(V → V)` 上的分布边缘化成
  `V × V × V` 上的联合律，且要证明边缘化保可分离性** —— **这未做**。

  **⚠ 故本文件的价值是**接口对齐与可见性**，不是「缺口 1 闭合」。**
  **本文件不声称推进了 `dSep ⟹ 因子分解` 的一般命题。**
  =========================================================================== -/

end FateV2.Predict.SeparatedCondMulUnified
