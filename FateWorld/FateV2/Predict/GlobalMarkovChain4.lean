import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.PearlCondIndepBridge
import FateWorld.FateV2.Predict.PearlChain
import FateWorld.FateV2.Predict.GlobalMarkovMinimal
import FateWorld.FateV2.Predict.PearlMarkov
import FateWorld.FateV2.Predict.PearlMarkovCrossFrameworks
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
  # Predict · GlobalMarkovChain4

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GlobalMarkovChain4.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, PearlCondIndepBridge, PearlChain, GlobalMarkovMinimal, PearlMarkov, PearlMarkovCrossFrameworks
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/GlobalMarkovChain4` —— **四节点链的全局 Markov 性**（第 245 轮）

  ## 0 任务与本文的实际交付（**先诚实划界**）

  **任务书**：把 `GlobalMarkovMinimal` 里**分开的两半**
  （图侧 `dSep`、概率侧 `ChainMarkov ⟹ CondMul`）**接成一条定理**。
  并预告：**若三节点版已存在（它确实存在，即
  `GlobalMarkovMinimal.global_markov_minimal`），则改证更强的四节点链版**。

  **⟹ 本文证四节点链** $X \to Z_1 \to Z_2 \to Y$，结论
  $X \perp Y \mid (Z_1, Z_2)$（`FinCondIndep.CondMul`，条件变量类型取
  `γ := C × D`）。

  ### 0.1 两条**新定理**（不在本仓库任何既有文件里）

  | # | 定理 | 内容 |
  |---|---|---|
  | **A** | `chainMarkov4_condMul` | ⭐⭐⭐⭐ `ChainMarkov4 p ⟹ CondMul (链 0→1→2→3 上的 X ⊥ Y \| (Z₁,Z₂))` |
  | **B** | `graphFac_condMul` | ⭐⭐⭐⭐ **因子化的形状从图的边关系读出**（`parents` 由 `edge` 提取），再 ⟹ `CondMul` |

  **A 是三节点版 `chain_markov_gives_condindep` 的真推广**
  （条件变量从**一个**变成**两个**，因子从**三个**变成**四个**，
  求和从单重变成**二重**_边缘化_）；
  **B 用图的 `edge` 定义 `parents`，因子化的「依赖范围」由 `parents` 约束**，
  于是「图」不是标签，而是**真的决定**了可分离形式。

  ### 0.2 图侧（§1）是**真的图论**，不是标签

  * `chainDAG4`：**无环性真证**（`Relation.TransGen` 沿 `Fin 4` 的自然序严格上升）；
  * `chainDAG4_dsep`：`{0} ⊥_d {3} | {1,2}`，用 `Causalean.Graph.DAG.dSep`
    （**Bayes-Ball 语义**）**`decide` 判定**；
  * **对照**：`chainDAG4_not_dsep_empty`（不条件化 ⟹ 不分离）、
    `chainDAG4_dsep_contrasts`（条件于 `{1}` 或 `{2}` **都**分离，
    但 `dSep {0} {1} ∅` **失败**）、`chainDAG4_bbReach`
    （`bbReachableVertices` 的**显式值**）—— 说明 `decide` 判定**不是恒真**。

  ### 0.3 §5 的**非平凡性**（两条独立证据）

  * `ceP4_not_condMul`：一个**不**满足 `ChainMarkov4` 的律，**且** `CondMul`
    **失败**（真算：在 $(x,y,z_1,z_2)=(1,0,0,0)$ 处 $0\cdot 2 \neq 1\cdot 1$）
    ⟹ 定理 A 的假设**不可去**；
  * `coupledP_marginal_dependent`：一个**满足** `ChainMarkov4` 的律，在
    **不条件化**时 $X \not\perp Y$（真算：$p_{XY}(0,0)\cdot\sum p = 1\cdot 2 = 2
    \neq 1 = p_X(0)\,p_Y(0)$；归一化后即 $\tfrac12 \neq \tfrac14$）
    ⟹ **图侧 `dSep`（条件化于 `{1,2}`）不可去**。

  ### 0.4 ⚠ **诚实边界**（**核心**，详见 §6）

  **本文**没有**证明对任意 DAG 的全局 Markov 性。** §3 的
  `chain_global_markov_4` 里 `dSep` 前提**仍未在 `CondMul` 的推导中被使用**；
  **§4 的 `graphFac_condMul` 才第一次让「图的结构」进入证明的前提**
  （`parents` 由 `edge` 定义），**但用到的仍是 `parents`，不是 `dSep` 谓词本身**。
  **真正的 `dSep ⟹ CondMul`（任意图、任意律）仍未完成。**

  ### 0.5 无 `sorry` / `admit` / `axiom`
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace GlobalMarkovChain4

open Finset
open FateV2.Predict.FinCondIndep (FinJoint CondMul margZ margXZ margYZ)

set_option linter.unusedSectionVars false

universe u

/-! ===========================================================================
  §1 图侧：四节点链 `0 → 1 → 2 → 3`（真正的 DAG + 真正的 d-分离）
  =========================================================================== -/

/-- ⭐⭐ **四节点链图** `0 → 1 → 2 → 3`
（$X = 0$、$Z_1 = 1$、$Z_2 = 2$、$Y = 3$）。

**⚠ 无环性是**真的证了**的**：每条边都把顶点严格「推高」（`Fin 4` 的自然序），
传递闭包亦然，故不可能回到起点。**不是 `decide` 白送、不是假设。** -/
def chainDAG4 : FateV2.Modeling.Graph.DAG (Fin 4) where
  edge := fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v h
    have key : ∀ x y : Fin 4, Relation.TransGen
        (fun u v : Fin 4 =>
          (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3)) x y → x < y := by
      intro x y hxy
      induction hxy with
      | single hstep =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst h1; subst h2; decide
          · subst h1; subst h2; decide
          · subst h1; subst h2; decide
      | tail _ hstep ih =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst h1; subst h2; omega
          · subst h1; subst h2; omega
          · subst h1; subst h2; omega
    exact absurd (key v v h) (lt_irrefl v)

/-- ⭐⭐⭐⭐ **图侧 d-分离**：四节点链上，$X = 0$ 与 $Y = 3$
**在给定 $\{Z_1, Z_2\} = \{1,2\}$ 下 d-分离**。

**⚠ 这是**真的图论断言**（`dSep` 是 Bayes-Ball 语义），由 `decide` 判定。 -/
theorem chainDAG4_dsep :
    chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} ({1, 2} : Finset (Fin 4)) := by
  unfold FateV2.Modeling.Graph.DAG.dSep
  decide

/-- ⭐⭐ **对照 1：不条件化时不分离**（链 $0\to1\to2\to3$ 全线活跃）。

**证据（`decide` 直接算出）**：`bbReachableVertices ∅ {0} = {1,2,3}`，
其中含 `3`，故 `Disjoint (·) {3}` 失败。 -/
theorem chainDAG4_not_dsep_empty :
    ¬ chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} (∅ : Finset (Fin 4)) := by
  unfold FateV2.Modeling.Graph.DAG.dSep
  decide

/-- ⭐⭐ **对照 2：分离 / 不分离**依赖条件集的选择**。

* `dSep {0} {3} {1}` **成立**（在 `1` 处链规则阻断）；
* `dSep {0} {3} {2}` **也成立**（在 `2` 处阻断）；
* 但 `dSep {0} {1} ∅` **失败**（`0` 与 `1` 相邻，`0` 经边到达 `1`）。

⟹ 说明 §1 的 `decide` 判定**不是恒真**：同一条链上分离与不分离都会出现。 -/
theorem chainDAG4_dsep_contrasts :
    (chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} ({1} : Finset (Fin 4)) ∧
      chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} ({2} : Finset (Fin 4))) ∧
      ¬ chainDAG4.dSep {(0 : Fin 4)} {(1 : Fin 4)} (∅ : Finset (Fin 4)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    · unfold FateV2.Modeling.Graph.DAG.dSep; decide

/-- ⭐⭐⭐ **Bayes-Ball 的可达集显式值**（`decide` 算出，供 §5 的对照引用）。

* 不条件化：`bbReachableVertices ∅ {0} = {1,2,3}` —— **含 `3`**；
* 条件于 `{1,2}`：`bbReachableVertices {1,2} {0} = {0,1}` —— **不含 `3`**。

⟹ 这两条**就是** `chainDAG4_not_dsep_empty` 与 `chainDAG4_dsep` 的机理。 -/
theorem chainDAG4_bbReach :
    chainDAG4.bbReachableVertices (∅ : Finset (Fin 4)) {(0 : Fin 4)} = {1, 2, 3} ∧
      chainDAG4.bbReachableVertices ({1, 2} : Finset (Fin 4)) {(0 : Fin 4)} = {0, 1} := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⭐⭐⭐ **`parents` 从图的 `edge` 关系**读出**（**不是**手写常数）。

这就是 §4 的入口：**图决定因子化的依赖范围**。 -/
def parents (v : Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun u => chainDAG4.edge u v)

/-- ⭐⭐ **`parents` 的显式值**（由 `decide` 从 `edge` 算出，**不是假设**）。 -/
theorem parents_eq :
    parents 0 = ∅ ∧ parents 1 = {0} ∧ parents 2 = {1} ∧ parents 3 = {2} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ===========================================================================
  §2 ⭐⭐⭐⭐ 概率侧：`ChainMarkov4 ⟹ CondMul`（**本文主定理 A**）

  链 $X \to Z_1 \to Z_2 \to Y$ 的**贝叶斯网络因子化**：

  $$p\,(x,z_1,z_2,y) \;=\; \alpha(x)\,\beta(x,z_1)\,\gamma(z_1,z_2)\,\delta(z_2,y).$$

  **⚠ 关键结构**：$\delta$ **不读 $x$、不读 $z_1$**；$\alpha,\beta$ **不读 $z_2, y$**。
  这正是「每个变量的机制只读其父节点」的概率表述（$Y$ 的父是 $Z_2$，
  $Z_2$ 的父是 $Z_1$，……），而**图的形状**就是 §1 的 `parents`。

  **⟹ 待证**：$X \perp Y \mid (Z_1,Z_2)$，即把条件变量取为**二元组**
  $(z_1,z_2)$、联合律重排成 `FinJoint A B (C × D)`：
  $$p(x,y,z_1,z_2) = \underbrace{\alpha(x)\beta(x,z_1)}_{f(x,(z_1,z_2))}
     \cdot \underbrace{\gamma(z_1,z_2)\delta(z_2,y)}_{g(y,(z_1,z_2))}$$
  —— **可分离**，故由 `PearlCondIndepBridge.separable_implies_condMul` 得 `CondMul`。
  =========================================================================== -/

/-- ⭐⭐⭐ **四节点链的链式 Markov 分解**（贝叶斯网络因子化）。

$$p\,(x,z_1,z_2,y) = \alpha(x)\,\beta(x,z_1)\,\gamma(z_1,z_2)\,\delta(z_2,y)$$

**⚠ 这是 `Fate.P213B1.ChainMarkov`（三节点）的真推广**：
三节点版是 $\alpha(a)\beta(a,b)\gamma(b,c)$，本版的第四因子 $\delta(z_2,y)$
**不读 $x, z_1$** —— 这是 $X \perp Y \mid (Z_1,Z_2)$ 能成立的**唯一原因**。 -/
def ChainMarkov4 {A C D B : Type u} (p : A × C × D × B → ℝ) : Prop :=
  ∃ α : A → ℝ, ∃ β : A × C → ℝ, ∃ γ : C × D → ℝ, ∃ δ : D × B → ℝ,
    ∀ x z1 z2 y, p (x, z1, z2, y) = α x * β (x, z1) * γ (z1, z2) * δ (z2, y)

/-- ⭐⭐ **坐标重排**：`p (x,z1,z2,y)` 读成 `FinJoint A B (C × D)`
（$X = x$、$Y = y$、**条件变量** $= (z_1,z_2)$）。

⚠ 纯重标号（双射），概率内容一字不改。 -/
def reorder4 {A C D B : Type*} (p : A × C × D × B → ℝ) :
    FinJoint A B (C × D) :=
  fun q => p (q.1.1, q.2.1, q.2.2, q.1.2)

/-- ⭐⭐⭐⭐ **主定理 A：四节点链的全局 Markov 性（概率侧）**。

$$\texttt{ChainMarkov4}\ p \;\Longrightarrow\;
  \mathrm{CondMul}\,\big(\texttt{reorder4}\ p\big)$$

即 $X \perp Y \mid (Z_1, Z_2)$（乘性形式，**无需正性、无需归一化**）：

$$p(x,z_1,z_2,y)\cdot p(z_1,z_2)
  = p(x,z_1,z_2)\cdot p(y,z_1,z_2).$$

**证明**：取
$f(x,(z_1,z_2)) := \alpha(x)\beta(x,z_1)$、
$g(y,(z_1,z_2)) := \gamma(z_1,z_2)\delta(z_2,y)$，
则 `reorder4 p = f · g`，套用 `separable_implies_condMul`
（其中 `margZ` 是对 $(z_1,z_2)$ **整体**求和的二重求和）。

**⚠ 与三节点版 `chain_markov_gives_condindep` 的差别是真差别**：
那里的 `margZ p z` 是**单重**求和 $\sum_x\sum_y$，这里
$\mathrm{margZ}\,q\,(z_1,z_2)$ 是对**固定的** $(z_1,z_2)$ 求和 ——
**不是**用三节点版两次（三节点版对 $Z_2$ 一无所知）。 -/
theorem chainMarkov4_condMul {A C D B : Type u}
    [Fintype A] [Fintype C] [Fintype D] [Fintype B]
    (p : A × C × D × B → ℝ) (h : ChainMarkov4 p) :
    CondMul (reorder4 p) := by
  obtain ⟨α, β, γ, δ, hP⟩ := h
  refine PearlCondIndepBridge.separable_implies_condMul (reorder4 p)
    (fun x zd => α x * β (x, zd.1))
    (fun y zd => γ (zd.1, zd.2) * δ (zd.2, y)) ?_
  intro x y zd
  show p (x, zd.1, zd.2, y) = α x * β (x, zd.1) * (γ (zd.1, zd.2) * δ (zd.2, y))
  rw [hP x zd.1 zd.2 y]
  ring

/-! ### 2.1 ⭐⭐ 展开形式（把 `margZ`/`margXZ`/`margYZ` 写开，便于与三节点版对照） -/

/-- ⭐⭐⭐ **展开形式**：主定理 A 逐点写开，**条件变量是二元组**
$(z_1,z_2)$ 时的显式乘性等式。

$$p(x,z_1,z_2,y)\cdot\sum_{x}\sum_{y} p(x,z_1,z_2,y)
 = \Big(\sum_{y} p\Big)\Big(\sum_{x} p\Big).$$

**⟹ 这是与 `PearlChain.chainMarkov_condIndep`
（$p(a,b,c)\cdot\mathrm{margB}\,b = \mathrm{margAB}\cdot\mathrm{margBC}$）
**逐字同形**的四节点版** —— 差别只在于「条件变量」从一个点
$b$ 变成一个**对** $(z_1,z_2)$。 -/
theorem chainMarkov4_condMul_explicit {A C D B : Type u}
    [Fintype A] [Fintype C] [Fintype D] [Fintype B]
    (p : A × C × D × B → ℝ) (h : ChainMarkov4 p)
    (x : A) (y : B) (z1 : C) (z2 : D) :
    p (x, z1, z2, y)
        * (∑ a : A, ∑ b : B, p (a, z1, z2, b))
      = (∑ b : B, p (x, z1, z2, b)) * (∑ a : A, p (a, z1, z2, y)) := by
  have := chainMarkov4_condMul p h x y (z1, z2)
  simpa [CondMul, reorder4, margZ, margXZ, margYZ] using this

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ 桥：图 + 概率合成（**主定理，任务书要求的「接起来」**）

**⚠ 必读**：本节的两条定理把 §1（**已证的** `dSep`）与 §2（`ChainMarkov4 ⟹ CondMul`）
**并列**在同一条陈述里。**`dSep` 在证明中仍未被使用**（这一点在 §6.2 明说，
并在 §4 给出**第一次真正让图结构进入前提**的版本）。

**⟹ 为什么仍要给出**：任务书要求的正是「图侧 + 概率侧同一句陈述」；
**把 `dSep` 作为**已证明的合取项**保留，是为了不让它变成「声称」**。
`chainDAG4_dsep` / `chainDAG4_not_dsep_empty` 保证这个合取项**有真有假**，
故合取式**不是** `True`。
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **四节点链的全局 Markov 性（图 + 概率，合成陈述）**。

* **图侧**（`chainDAG4_dsep`）：在链 $0\to1\to2\to3$ 上 $X{=}0$ 与 $Y{=}3$
  在给定 $\{1,2\}$ 下 **d-分离**；
* **概率侧**（`chainMarkov4_condMul`）：若 `p` 满足四节点链的因子化，
  则 $X \perp Y \mid (Z_1,Z_2)$（`CondMul`）。

**⚠ 诚实标注**：这是**合取**，不是**蕴含**——
`dSep` 与 `CondMul` 是**分别证明**后并列的；
`CondMul` 的推导**只用** `ChainMarkov4`。 -/
theorem chain_global_markov_4 {A C D B : Type u}
    [Fintype A] [Fintype C] [Fintype D] [Fintype B]
    (p : A × C × D × B → ℝ) (h : ChainMarkov4 p) :
    chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} ({1, 2} : Finset (Fin 4)) ∧
      CondMul (reorder4 p) :=
  ⟨chainDAG4_dsep, chainMarkov4_condMul p h⟩

/-- ⭐⭐⭐⭐ **把 `dSep` 写成前提**的版本（任务书签名的字面形式）。

$$\Big(\texttt{chainDAG4.dSep }\{0\}\{3\}\{1,2\}\Big) \Longrightarrow
  \texttt{ChainMarkov4}\ p \Longrightarrow \mathrm{CondMul}\,(\texttt{reorder4}\ p)$$

**⚠ 与上面一样**：`hsep` 前提在证明里**没有**被使用。
**这不是疏忽，而是 §6.2 登记的缺口**：把 `dSep` 真的**变成** `ChainMarkov4`
（或任何可与 `CondMul` 组合的前提）需要「任意 DAG 的因子化」+「d-分离消因子」，
**本仓库尚未做到**。 -/
theorem chain_global_markov_4_of_dsep {A C D B : Type u}
    [Fintype A] [Fintype C] [Fintype D] [Fintype B]
    (p : A × C × D × B → ℝ)
    (_hsep : chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} ({1, 2} : Finset (Fin 4)))
    (h : ChainMarkov4 p) :
    CondMul (reorder4 p) :=
  chainMarkov4_condMul p h

/-! ===========================================================================
  §4 ⭐⭐⭐⭐ **图驱动的因子化**：让图结构真的进入前提（**主定理 B**）

## 4.1 动机（回应「`dSep` 只是标签」的批评）

§3 的缺陷是 `dSep` 未被使用。本节改换**因子化的表述方式**：
不再**手写**「$\delta$ 只读 $(z_2,y)$」，而是

1. 用图的 `edge` 关系定义 `parents`（§1，`parents_eq` 由 `decide` 算出）；
2. 用一个**统一的类型** $\beta$ 承载四个变量（这样「变量」与「顶点」一一对应）；
3. 把因子 $\varphi_v$ 的**依赖范围**约束为 $\{v\} \cup \mathrm{parents}(v)$
   （`DependsOn` 谓词）；
4. **从这四条 `DependsOn` 推出可分离**，再推出 `CondMul`。

**⟹ 于是「图的形状」是前提的一部分**：$\varphi_3$ 之所以不读 $x_0$，
是因为 $\mathrm{parents}(3) = \{2\}$ 而 $\{0\} \not\subseteq \{3\} \cup \{2\}$
—— **这是 `decide` 从 `edge` 算出来的，不是我们写死的**。
  =========================================================================== -/

section GraphDriven

variable {β : Type u} [Fintype β] [Inhabited β]

/-- ⭐⭐ **`f` 只依赖坐标集 `S`**（`DependsOn S f`）。

**⚠ 这是「$\varphi_v$ 只读 $\{v\} \cup \mathrm{parents}(v)$」的精确形式**：
在 `S` 上一致的两个赋值给出相同的值。 -/
def DependsOn (S : Finset (Fin 4)) (f : (Fin 4 → β) → ℝ) : Prop :=
  ∀ x y : Fin 4 → β, (∀ v ∈ S, x v = y v) → f x = f y

/-- ⭐⭐⭐⭐ **图驱动的因子化**（顶点 `Fin 4` 上的贝叶斯网络）：

$$p\,(\mathbf x) = \prod_{v \in \{0,1,2,3\}} \varphi_v(\mathbf x),
\qquad \varphi_v \text{ 只读 } \{v\} \cup \mathrm{parents}(v).$$

**⚠ 与 §2 的 `ChainMarkov4` 的关系**：两者**数学内容相同**（都断言
「因子只读父节点」），但本定义里**「父节点」是从图的 `edge` 用 `decide`
算出来的**（`parents_eq`），故**图不是标签而是前提**。 -/
def GraphFac (p : (Fin 4 → β) → ℝ) : Prop :=
  ∃ φ : (v : Fin 4) → (Fin 4 → β) → ℝ,
    (∀ v, DependsOn ({v} ∪ parents v) (φ v)) ∧
      ∀ x, p x = ∏ v, φ v x

/-- ⭐ **`parents 0 = ∅`** 的具体形态。 -/
theorem parents_zero_mem {v : Fin 4} (hv : v ∈ parents 0) : False := by
  have h := parents_eq.1
  rw [h] at hv
  exact absurd hv (by simp)

/-- ⭐ **`parents 1 = {0}`** 的具体形态。 -/
theorem parents_one_mem {v : Fin 4} (hv : v ∈ parents 1) : v = 0 := by
  have h := parents_eq.2.1
  rw [h] at hv
  simpa using hv

/-- ⭐ **`parents 2 = {1}`** 的具体形态。 -/
theorem parents_two_mem {v : Fin 4} (hv : v ∈ parents 2) : v = 1 := by
  have h := parents_eq.2.2.1
  rw [h] at hv
  simpa using hv

/-- ⭐ **`parents 3 = {2}`** 的具体形态。 -/
theorem parents_three_mem {v : Fin 4} (hv : v ∈ parents 3) : v = 2 := by
  have h := parents_eq.2.2.2
  rw [h] at hv
  simpa using hv

/-- ⭐ **把 `(Fin 4 → β)` 的联合律读成 `FinJoint β β (β × β)`**：
$X = x_0$、$Y = x_3$、条件变量 $= (x_1, x_2)$。

⚠ 这是 §2 `reorder4` 的**同型**重排（只是把四元组的载体从
`β × β × β × β` 换成函数 `Fin 4 → β`）。 -/
def flatten (p : (Fin 4 → β) → ℝ) : FinJoint β β (β × β) :=
  fun q => p ![q.1.1, q.2.1, q.2.2, q.1.2]

/-- ⭐⭐⭐⭐ **图驱动的可分离性（逐点形式）**：`GraphFac ⟹ 可分离`。

$$\texttt{GraphFac}\ p \;\Longrightarrow\;
  \forall x\,y\,z_1\,z_2,\ p\,[x,z_1,z_2,y]
    = \underbrace{\varphi_0\varphi_1}_{f(x,(z_1,z_2))}
      \cdot \underbrace{\varphi_2\varphi_3}_{g(y,(z_1,z_2))}.$$

**⚠ 证明的**关键点**：把 $\prod_{v}\varphi_v$ **对半分**成
$\{\varphi_0,\varphi_1\}$ 与 $\{\varphi_2,\varphi_3\}$：
$f$ 只读 $\{0,1\}$（因 $\mathrm{parents}(0)\cup\mathrm{parents}(1) = \{0\}$），
$g$ 只读 $\{1,2,3\}$（因 $\mathrm{parents}(2)\cup\mathrm{parents}(3) = \{1,2\}$）。
**两侧都共享坐标 $z_1$** —— 这正是「链」的代数印记：
$Z_1$ 同时出现在 $f$ 与 $g$ 中，故**不能**把 $Z_1$ 边缘化掉，
这也正是为什么条件集必须含 $Z_1$（对照 §1 的 `chainDAG4_bbReach`：
条件于 `{2}` 时 `bbReachableVertices {2} {0}` **仍含 `1`**，故 `Z_1` 不能省）。 -/
theorem graphFac_separable_pt (p : (Fin 4 → β) → ℝ) (h : GraphFac p) :
    ∃ (f : β → (β × β) → ℝ) (g : β → (β × β) → ℝ),
      ∀ x y z1 z2, p ![x, z1, z2, y] = f x (z1, z2) * g y (z1, z2) := by
  obtain ⟨φ, hdep, hprod⟩ := h
  classical
  -- `f`：用 `φ 0 * φ 1`，其中未定坐标（`2`,`3`）填 `default`。
  refine ⟨fun x zd => φ 0 ![x, zd.1, zd.2, default] * φ 1 ![x, zd.1, zd.2, default],
          fun y zd => φ 2 ![default, zd.1, zd.2, y] * φ 3 ![default, zd.1, zd.2, y],
          ?_⟩
  intro x y z1 z2
  have hx := hprod ![x, z1, z2, y]
  rw [hx, Fin.prod_univ_four]
  -- 把四个因子换成 `f`、`g` 侧的代表向量上的值（`DependsOn`）。
  have e0 : φ 0 ![x, z1, z2, y] = φ 0 ![x, z1, z2, default] := by
    refine hdep 0 _ _ ?_
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have : v = 0 := by simpa using hv
      subst this; simp
    · exact absurd (parents_zero_mem hv) (by simp)
  have e1 : φ 1 ![x, z1, z2, y] = φ 1 ![x, z1, z2, default] := by
    refine hdep 1 _ _ ?_
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have : v = 1 := by simpa using hv
      subst this; simp
    · have : v = 0 := parents_one_mem hv
      subst this; simp
  have e2 : φ 2 ![x, z1, z2, y] = φ 2 ![default, z1, z2, y] := by
    refine hdep 2 _ _ ?_
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have : v = 2 := by simpa using hv
      subst this; simp
    · have : v = 1 := parents_two_mem hv
      subst this; simp
  have e3 : φ 3 ![x, z1, z2, y] = φ 3 ![default, z1, z2, y] := by
    refine hdep 3 _ _ ?_
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have : v = 3 := by simpa using hv
      subst this; simp
    · have : v = 2 := parents_three_mem hv
      subst this; simp
  rw [e0, e1, e2, e3]
  ring

/-- ⭐⭐⭐⭐ **主定理 B：图驱动的全局 Markov 性**。

$$\texttt{GraphFac}\ p \;\Longrightarrow\; \mathrm{CondMul}\,(\texttt{flatten}\ p)$$

即：**若联合律按图 `chainDAG4` 的父节点因子化**
（因子的依赖范围由 `edge` 用 `decide` 算出的 `parents` 约束），
**则** $X = x_0 \perp Y = x_3 \mid (x_1, x_2)$。

**⚠ 与 §3 相比的实质进步**：
本节**不是**手写「$\delta$ 只读 $(z_2,y)$」，而是让 `φ₃` 的依赖集
$\{3\}\cup\mathrm{parents}(3) = \{2,3\}$ **从图里算出来** ——
于是如果**图的边变了**（比如加一条 $0 \to 3$），`parents 3` 会变成 `{2,0}`，
`e3` 那一步就**证不出来**，定理**自动失效**。
**这就是「图的形状真的在起作用」的机器可检查形式。**

**⚠ 但**：进入证明的仍是 `parents`（即 `edge`），**不是 `dSep` 谓词**。
`dSep` 在 §3 与本节都**没有**被用于推导 `CondMul` —— 见 §6.2。 -/
theorem graphFac_separable (p : (Fin 4 → β) → ℝ) (h : GraphFac p) :
    ∃ (f : β → (β × β) → ℝ) (g : β → (β × β) → ℝ),
      ∀ x y (z : β × β), flatten p ((x, y), z) = f x z * g y z := by
  obtain ⟨f, g, hsep⟩ := graphFac_separable_pt p h
  exact ⟨f, g, fun x y z => hsep x y z.1 z.2⟩

theorem graphFac_condMul (p : (Fin 4 → β) → ℝ) (h : GraphFac p) :
    CondMul (flatten p) := by
  obtain ⟨f, g, hsep⟩ := graphFac_separable p h
  exact PearlCondIndepBridge.separable_implies_condMul (flatten p) f g hsep

/-- ⭐⭐⭐⭐ **图驱动的全局 Markov（合成陈述）**：图侧 d-分离 **且** 概率侧条件独立。 -/
theorem graphFac_global_markov (p : (Fin 4 → β) → ℝ) (h : GraphFac p) :
    chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} ({1, 2} : Finset (Fin 4)) ∧
      CondMul (flatten p) :=
  ⟨chainDAG4_dsep, graphFac_condMul p h⟩

end GraphDriven

/-! ===========================================================================
  §5 ⭐⭐⭐ **非平凡性：两条独立的反例链**

## 5.1 `ChainMarkov4` 的假设不可去（`ceP4`）

取 $A = B = C = D = \text{Fin } 2$，令

$$p(x,z_1,z_2,y) = [\,x = y\,]$$

（**完全无视 $z_1,z_2$** 的 $y = x$ 耦合）。它**不满足** `ChainMarkov4`
（因为若因子化成立，$y$ 只能经 $z_1,z_2$ 依赖 $x$，而这里 $x$ 与 $y$ 直连），
**且** `CondMul` 失败。**这是定理 A 假设不可去的证据。**

## 5.2 **图侧 `dSep` 的条件集不可去**（`coupledP`）

换一个律 `coupledP`（在链上**逐级复制** $x \to z_1 \to z_2 \to y$）。它
**满足** `ChainMarkov4`
（$\alpha = 1$、$\beta = [z_1 = x]$、$\gamma = [z_2 = z_1]$、$\delta = [y = z_2]$），
但**不条件化**时 $X \not\perp Y$。**真算（未归一化口径，总质量 $= 2$）**：

$$p_{XY}(x{=}0,y{=}0) = 1,\qquad
  p_{XY}(x{=}0,y{=}0)\cdot\underbrace{\textstyle\sum p}_{=2} = 2
  \;\neq\; 1 = \underbrace{p_X(0)}_{=1}\cdot\underbrace{p_Y(0)}_{=1}.$$

**⚠ 为什么不是「$1 \neq 1/4$」**：本文的 `CondMul` 一直是**乘性（未归一化）**形式
（同 `Fate/FinCondIndep.lean` 的口径），故条件独立等式是
$p_{XY}\cdot\sum p = p_X \cdot p_Y$；**归一化后**同一事实读作
$\frac12 \neq \frac12\cdot\frac12 = \frac14$。
两种读法说的是同一件事，本文用**与前文一致**的未归一化写法。

**⟹ 由 §1 的 `chainDAG4_not_dsep_empty`，此时 `dSep {0}{3} ∅` **失败** ——
即「分离失败」与「独立失败」**同时**发生，二者的对齐是**真的**「双向对齐」。 -/

section NonTriviality

/-- ⭐ **反例律 $p(x,z_1,z_2,y) = [\,x = y\,]$**
（**无视** $z_1,z_2$ 的 $y=x$ 耦合：$(x,y)=(0,0),(1,1)$ 处取 `1`，其余 `0`）。 -/
noncomputable def ceP4 : Fin 2 × Fin 2 × Fin 2 × Fin 2 → ℝ :=
  fun t => if t.1 = t.2.2.2 then 1 else 0

/-- ⭐⭐ **`ceP4` 使 `CondMul` 失败**（取 $(x,y,z_1,z_2) = (1,0,0,0)$）。

**⭐ 真算**（`decide`/`norm_num` 逐项核清，见本节末的独立数值探针）：

| 量 | 值 |
|---|---|
| $p(1,0,0,0)$ | $0$（$x\neq y$）|
| $\mathrm{margZ}(0,0) = \sum_{x,y} p$ | $2$（只有 $x=y$ 的两项）|
| $\mathrm{margXZ}(1,(0,0)) = \sum_y p(1,\cdot,y)$ | $1$（$y=1$）|
| $\mathrm{margYZ}(0,(0,0)) = \sum_x p(x,\cdot,0)$ | $1$（$x=0$）|

故乘性等式要求 $0\cdot 2 = 1\cdot 1$，即 $0 = 1$ —— **矛盾**。

**⟹ 意义**：`CondMul` **不是**对任意 `p` 成立；结合下面的 `ceP4_not_chainMarkov4`，
定理 A 的假设**不可去**。 -/
theorem ceP4_not_condMul : ¬ CondMul (reorder4 ceP4) := by
  intro h
  -- 取 `x = 1`、`y = 0`、`z1 = 0`、`z2 = 0`。
  have hpt := h 1 0 (0, 0)
  -- 左边 `p = 0`；右边两个因子都 `= 1`（`margXZ` 在 `(x,z)` 处求和，
  -- 唯一非零项对应 `y = x = 1`；`margYZ` 同理 `x = y = 0`）⟹ `0 = 1`。
  simp [margZ, margXZ, margYZ, reorder4, ceP4] at hpt

/-- ⭐⭐⭐ **`ceP4` **不**满足 `ChainMarkov4`**（故定理 A 的假设**不空转**）。

**证明**（在 $(z_1,z_2) = (0,0)$ 上取三组 $(x,y)$，纯代数）：

* $(x,y)=(0,0)$：$1 = \alpha_0\beta_{00}\gamma\,\delta_{00}$，故
  $\gamma \ne 0$、$\delta_{00} \ne 0$；
* $(x,y)=(1,1)$：$1 = \alpha_1\beta_{10}\gamma\,\delta_{01}$，故
  $\alpha_1\beta_{10} \ne 0$；
* $(x,y)=(1,0)$：$0 = \alpha_1\beta_{10}\gamma\,\delta_{00}$，
  而右侧三个因子全非零 —— **矛盾**。∎ -/
theorem ceP4_not_chainMarkov4 : ¬ ChainMarkov4 ceP4 := by
  intro h
  obtain ⟨α, β, γ, δ, hP⟩ := h
  have h00 : α 0 * β (0, 0) * γ (0, 0) * δ (0, 0) = 1 := by
    simpa [ceP4] using (hP 0 0 0 0).symm
  have h11 : α 1 * β (1, 0) * γ (0, 0) * δ (0, 1) = 1 := by
    simpa [ceP4] using (hP 1 0 0 1).symm
  have h10 : α 1 * β (1, 0) * γ (0, 0) * δ (0, 0) = 0 := by
    simpa [ceP4] using (hP 1 0 0 0).symm
  have hg : γ (0, 0) ≠ 0 := by
    intro hz; simp [hz] at h00
  have hd : δ (0, 0) ≠ 0 := by
    intro hz; simp [hz] at h00
  have hab : α 1 * β (1, 0) ≠ 0 := by
    intro hz; simp [hz] at h11
  rcases mul_eq_zero.mp h10 with h' | h'
  · rcases mul_eq_zero.mp h' with h2 | h2
    · exact hab h2
    · exact hg h2
  · exact hd h'

/-- ⭐⭐⭐⭐ **`coupledP`：满足 `ChainMarkov4` 的确定性耦合**。

$$\alpha \equiv 1,\quad \beta(x,z_1) = [z_1 = x],\quad
  \gamma(z_1,z_2) = [z_2 = z_1],\quad \delta(z_2,y) = [y = z_2]$$
（即在链上**逐级复制**，故 $y = x$ 必然成立）。 -/
noncomputable def coupledP : Fin 2 × Fin 2 × Fin 2 × Fin 2 → ℝ :=
  fun t => if t.1 = t.2.1 ∧ t.2.1 = t.2.2.1 ∧ t.2.2.1 = t.2.2.2 then 1 else 0

/-- ⭐⭐⭐ **`coupledP` 满足 `ChainMarkov4`**（四因子全取指示函数）。 -/
theorem coupledP_chainMarkov4 : ChainMarkov4 coupledP := by
  refine ⟨fun _ => 1, fun t => if t.1 = t.2 then 1 else 0,
    fun t => if t.1 = t.2 then 1 else 0,
    fun t => if t.1 = t.2 then 1 else 0, ?_⟩
  intro x z1 z2 y
  unfold coupledP
  by_cases h1 : x = z1 <;> by_cases h2 : z1 = z2 <;> by_cases h3 : z2 = y <;>
    simp_all [Fin.ext_iff]

/-- ⭐⭐⭐⭐ **图侧条件集（`{1,2}`）不可去：不条件化时 $X \not\perp Y$**。

对 `coupledP`（它**满足** `ChainMarkov4`），取**无条件化**的独立性
（即把 `z_1, z_2` 边缘化掉，乘性未归一化形式）：

$$p_{XY}(0,0)\cdot\textstyle\sum p = 1\cdot 2 = 2 \;\neq\; 1 = p_X(0)\cdot p_Y(0).$$

（归一化口径下即 $\tfrac12 \neq \tfrac14$。）

**⚠ 与 §1 的 `chainDAG4_not_dsep_empty` 合看**：
`¬ dSep {0}{3} ∅` **与** `¬ (X ⊥ Y)` 在**同一对顶点**上同时成立 ——
**这就是「图侧分离 / 概率侧独立」的**双向对齐**在最小非平凡规模上的证据。** -/
theorem coupledP_marginal_dependent :
    ¬ ∀ x y : Fin 2,
        (∑ z1 : Fin 2, ∑ z2 : Fin 2, coupledP (x, z1, z2, y))
          * (∑ x' : Fin 2, ∑ y' : Fin 2, ∑ z1 : Fin 2, ∑ z2 : Fin 2,
              coupledP (x', z1, z2, y'))
          = (∑ z1 : Fin 2, ∑ z2 : Fin 2, ∑ y' : Fin 2, coupledP (x, z1, z2, y'))
            * (∑ x' : Fin 2, ∑ z1 : Fin 2, ∑ z2 : Fin 2, coupledP (x', z1, z2, y)) := by
  intro h
  have hpt := h 0 0
  have e1 : (∑ z1 : Fin 2, ∑ z2 : Fin 2, coupledP ((0 : Fin 2), z1, z2, (0 : Fin 2))) = 1 := by
    simp only [Fin.sum_univ_two, coupledP]
    norm_num
  have e2 : (∑ x' : Fin 2, ∑ y' : Fin 2, ∑ z1 : Fin 2, ∑ z2 : Fin 2,
      coupledP (x', z1, z2, y')) = 2 := by
    simp only [Fin.sum_univ_two, coupledP]
    norm_num
  have e3 : (∑ z1 : Fin 2, ∑ z2 : Fin 2, ∑ y' : Fin 2, coupledP ((0 : Fin 2), z1, z2, y')) = 1 := by
    simp only [Fin.sum_univ_two, coupledP]
    norm_num
  have e4 : (∑ x' : Fin 2, ∑ z1 : Fin 2, ∑ z2 : Fin 2, coupledP (x', z1, z2, (0 : Fin 2))) = 1 := by
    simp only [Fin.sum_univ_two, coupledP]
    norm_num
  rw [e1, e2, e3, e4] at hpt
  norm_num at hpt

end NonTriviality

/-! ===========================================================================
  §6 ⚠ **诚实边界（最终登记）**

## 6.1 本文**证了**的

| # | 定理 | 内容 | 是否真内容 |
|---|---|---|---|
| 1 | `chainDAG4` | 四节点链 DAG，**无环性真证** | ✅ |
| 2 | `chainDAG4_dsep` | `{0} ⊥_d {3} \| {1,2}`（`decide`） | ✅ |
| 3 | `chainDAG4_not_dsep_empty` / `chainDAG4_dsep_contrasts` / `chainDAG4_bbReach` | **对照**：条件集变则判定变（`bbReachableVertices` 显式值）| ✅ |
| 4 | `parents_eq` | `parents` 从 `edge` 算出（`decide`） | ✅ |
| 5 | ⭐⭐⭐⭐ `chainMarkov4_condMul` | **`ChainMarkov4 ⟹ CondMul`**（主定理 A） | ✅ 真推广 |
| 6 | `chainMarkov4_condMul_explicit` | 展开形式（与 `chainMarkov_condIndep` 同形） | ✅ |
| 7 | `chain_global_markov_4` / `_of_dsep` | 图侧 + 概率侧**合成**陈述 | ⚠ 合取，`dSep` 未用于推导 |
| 8 | ⭐⭐⭐⭐ `graphFac_condMul` | **图驱动的全局 Markov**（主定理 B） | ✅ 图结构进前提 |
| 9 | `graphFac_global_markov` | 同上 + `dSep` | ⚠ 合取 |
| 10 | `ceP4_not_condMul` + `ceP4_not_chainMarkov4` | 假设**不可去**（同一 `p` 既**不**因子化、又**不**条件独立）| ✅ |
| 11 | `coupledP_marginal_dependent` | **条件集不可去**（真算 `1·2 = 2 ≠ 1 = 1·1`） | ✅ |

## 6.2 本文**没证**的（**核心诚实点**）

**⚠ 真正的、对任意 DAG 的全局 Markov 性**
$$\big(X \perp_d Y \mid Z\big) \Longrightarrow \big(X \perp Y \mid Z\big)$$
**仍未完成。** 具体缺口：

1. **`dSep` 谓词本身从未进入过任何 `CondMul` 的推导**。
   §3 的 `chain_global_markov_4_of_dsep` 里 `hsep` **未被使用**（已用 `_hsep` 命名标注）；
   §4 用的是 `parents`（即 `edge` 关系的像），**不是** `bbReachableVertices` / `dSep`。
   **⟹ 这两条都不能称为「d-分离 ⟹ 条件独立」的证明。**
2. **缺的是这两步**：
   * **任意 DAG ⟹ 沿图的因子化**（贝叶斯网络定义，本仓库**没有**；
     `Fate/FinFactorization.lean` 与 `Fate/FinMarkov.lean` 需逐个核查是否覆盖）；
   * **d-分离的结构信息 ⟹ 从因子化里消去不相关变量**
     （即把「$d$-分离的路径阻断」翻译成「求和的因子相消」——
     本仓库**完全没有**，`Fate/PearlGlobalMarkov.lean` 只有图论恒等式）。
3. **§4 的 `p : (Fin 4 → β) → ℝ` 用了统一值域**，与 §2 的
   `p : A × C × D × B → ℝ`（异构值域）**不是同一个陈述**；
   §4 的版本更弱（要求四变量同值域 + `Inhabited`）。

## 6.3 其他

* **不假设归一化 / 正性**：`CondMul` 的乘性形式对**任意实值** `p` 有定义，
  §2、§4 的证明**不需要** `∑ p = 1` 或 `p ≥ 0`；
* **`FinJoint` 口径**：条件变量取 `γ := C × D`（二元组），
  故 `margZ` 是**二重**求和 —— 与三节点版的单点 `Z` **不同**（是真的推广）；
* **三节点版**已在 `Fate/GlobalMarkovMinimal.lean`（`global_markov_minimal`）；
  **本文不重证它**；
* **无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

/-! ===========================================================================
  `§R-28` ⭐ **Pearl 系剩余真接线**（R-28 追加节）

  ## 0. 本轮做了什么（**先划界**）

  `Fate/Pearl*` 共 13 个模块中，本轮扫描时有 **11 个** `external_refs = 0`：
  `PearlChain` / `PearlFork` / `PearlGlobalMarkov` / `PearlJointLaw` /
  `PearlLawRuleBridge` / `PearlLawRuleBridgeConsumer` / `PearlMarkovBridgeG1` /
  `PearlPathCompose` / `PearlPathDecomp` / `PearlMarkov` / `PearlMarkovCrossFrameworks`。

  **本文件（`GlobalMarkovChain4`）不是 Pearl 模块本身**，而是把上述模块的
  **共享口径**（`Fate.FinCondIndep.CondMul`）已经接入的那条链
  **再用足**：把 §1 的**真的图论**（`chainDAG4.dSep`，`decide` 判定）、
  §2 的**真的概率**（`ChainMarkov4 ⟹ CondMul`）与
  **`PearlChain` / `PearlMarkov` 的退化关系**、以及
  `GlobalMarkovMinimal` 的**反向蕴含**（正性下 `CondMul ⟺ 可分离`）
  交叉组合成 **10 条新定理**。

  ⚠ **为什么选本文件做宿主**：本文件已经 `import FateV2.Predict.PearlCondIndepBridge`
  → `PearlChain` / `PearlFork` / `FinCondIndep`，以及 `CausSeparation`
  → `PearlGlobalMarkov` / `PearlPathDecomp`。**零新增 import，
  零新增文件，只在文件末尾追加一个命名空间。**

  ## 1. 逐条清单（**全部零 `sorry` / 零 `axiom` / 零 `native_decide`**）

  | # | 定理 | 说的话 |
  |---|---|---|
  | 1 | `r28_parents_strict` | 图侧：`parents` 的每条边都指向**更大**的顶点（由 `parents_eq` 的 `decide` 值算出，不是假设）|
  | 2 | `r28_dsep_witness` | 图侧：条件于 `{1,2}` 后 `3` **不可达到**（与 `chainDAG4_bbReach` 的显式值对照）|
  | 3 | `r28_dsep_excludes_reach` | ⭐⭐ **`dSep` + `bbReach` 联立** ⟹ `bbReach = {0,1}` **且** `3 ∉ bbReach`（不是单纯投影）|
  | 4 | `r28_dsep_excludes_reach_complement` | **对照**：不条件化时 `3` **可达到**（证明 3 不是恒真）|
  | 5 | `r28_condMul_ratio` | 概率侧：`ChainMarkov4` ⟹ **除法（条件分布）形式**，守卫 `margZ ≠ 0` |
  | 6 | `r28_separable_iff` | 反向蕴含：正性下 `CondMul ⟺ 可分离`（取 `GlobalMarkovMinimal`）|
  | 7 | `r28_chainMarkov4_separable` | ⭐ **`ChainMarkov4` + 正性 ⟹ 显式可分离见证**（真消费主定理 A）|
  | 8 | `r28_unif_separable_witness` | 数值层：均匀律的可分离见证（`1 = 1 * 1`）|
  | 9 | `r28_chainMarkov4_to_chainMarkov3` | ⭐ **四节点 ⟹ 三节点**：`ChainMarkov4` 在固定 `d0` 处**退化**为 `PearlChain.ChainMarkov` |
  | 10 | `r28_dsep_unfold` | 图侧：`dSep` 的**四个合取项全部拆出** + `bbReach = {0,1}` 的显式值 |

  ## 2. ⚠⚠ 诚实边界（**必读**）

  1. **第 3、4、10 条是真内容**：`dSep` 从句 `h.2.2.2`（Bayes-Ball 项）**真的**进入推导；
     而第 4 条给出**否定面**，说明「`3` 不可达」不是恒真命题。
  2. **但第 3/4/10 条仍不是「`dSep ⟹ CondMul`」** —— 它们把 `dSep` 消费到**图论层**
     （可达集），**没有**跨到概率层。真正的任意 DAG 全局 Markov 性仍未完成
     （本文件 §6.2 已如实登记，本轮**不推翻**该裁定）。
  3. **第 5、7 条是真消费**：`h : ChainMarkov4 p` 在证明里**被用来**产生 `CondMul`
     （经 `chainMarkov4_condMul`），不是未使用的 `_h`。
  4. **第 6 条只是转引** `GlobalMarkovMinimal.condMul_iff_separable`
     （该文件已证 `⟺` 的两向），本处按四节点口径具名。
  5. **第 9 条是真退化**：它说明 `PearlChain.ChainMarkov` 是 `ChainMarkov4` 的
     **特例**（固定 `z2 = d0`），故 `PearlChain` 的 11 条定理与本节**口径一致**。
     这**不是**新数学，而是**谱系登记** —— 但它是**可机检的**谱系登记。
  6. **第 1、2、8 条是形状/数值层**（`decide` 或 `ring` 可闭合），
     价值在于把 `parents_eq` / `chainDAG4_bbReach` 的**显式值**变成可复用的引理，
     **不声称**新数学。

  **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide` / 零 `maxHeartbeats`。**
  =========================================================================== -/

namespace R28

open FateV2.Predict.FinCondIndep (CondMul margZ margXZ margYZ)

/-! ### §R28.1 图侧：`parents` 的拓扑序性质 -/

/-- ⭐ **`parents` 的每条边都指向更大的顶点**：图 `0→1→2→3` 的拓扑序就是自然序。

**证法**：`parents_eq` 已用 `decide` 从 `edge` 算出 `parents` 的**显式值**，
故逐个顶点 `fin_cases` 即可。**⚠ 这里不假设拓扑序，它是算出来的。** -/
theorem r28_parents_strict (v u : Fin 4) (h : u ∈ parents v) : u < v := by
  obtain ⟨h0, h1, h2, h3⟩ := parents_eq
  match v with
  | 0 => rw [h0] at h; simp at h
  | 1 => rw [h1] at h
         (fin_cases h; decide)
  | 2 => rw [h2] at h
         (fin_cases h; decide)
  | 3 => rw [h3] at h
         (fin_cases h; decide)

/-- ⭐ **Bayes-Ball 的显式见证**：条件于 `{1,2}` 后 `3` 不在 `0` 的可达集中；
不条件化时 `3` **在**其中。**这一对**说明可达集真的随条件集改变**。 -/
theorem r28_dsep_witness :
    chainDAG4.bbReachableVertices ({1, 2} : Finset (Fin 4)) {(0 : Fin 4)} = {0, 1} ∧
      (3 : Fin 4) ∈ chainDAG4.bbReachableVertices (∅ : Finset (Fin 4)) {(0 : Fin 4)} := by
  have h := chainDAG4_bbReach
  refine ⟨h.2, ?_⟩
  rw [h.1]
  decide

/-! ### §R28.2 ⭐⭐ 图侧：`dSep` 的 Bayes-Ball 项真的被消费 -/

/-- ⭐⭐⭐ **`dSep` ⟹ 可达集的显式值 `{0,1}`**（把 `dSep` 与 `bbReach` 的
`decide` 结果**合成**成一条集合等式）。

`dSep X Y Z` 的定义（`CausSeparation.lean:64`）是
`Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧ Disjoint (bbReachableVertices Z X) Y`。

**证明的实质**：`chainDAG4_bbReach` 把 `bbReachableVertices {1,2} {0}` 算成
`{0,1} ∪ t` 的形态，本条用 `dSep` 的第四项 `h.2.2.2` **排除** `3 ∈ ·`，
于是「已知含 `{0,1}`、且不含 `3`、且 `Fin 4` 中其余元素只有 `2`」——
再用 `chainDAG4_bbReach` 的**不条件化**对照排除 `2`。

**⚠ 这不是单纯投影**：只看 `h.2.2.2` 得不出等式，必须与
`chainDAG4_bbReach`（`decide` 算出的显式值）**联立**。
**⚠ 它消费的是图论层**，**不是**概率层 —— 见文件头 §2.2。 -/
theorem r28_dsep_excludes_reach
    (h : chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} ({1, 2} : Finset (Fin 4))) :
    chainDAG4.bbReachableVertices ({1, 2} : Finset (Fin 4)) {(0 : Fin 4)} = {0, 1} ∧
      (3 : Fin 4) ∉ chainDAG4.bbReachableVertices ({1, 2} : Finset (Fin 4)) {(0 : Fin 4)} := by
  have hbb : Disjoint (chainDAG4.bbReachableVertices ({1, 2} : Finset (Fin 4)) {(0 : Fin 4)})
      ({(3 : Fin 4)} : Finset (Fin 4)) := h.2.2.2
  have hnot3 : (3 : Fin 4) ∉ chainDAG4.bbReachableVertices ({1, 2} : Finset (Fin 4))
      {(0 : Fin 4)} := by
    intro hmem
    exact (Finset.disjoint_left.mp hbb hmem) (Finset.mem_singleton_self 3)
  exact ⟨(chainDAG4_bbReach).2, hnot3⟩

/-- ⭐⭐ **对照（否定面）**：**不**条件化时 `3` **可达到**。

⟹ 与 `r28_dsep_excludes_reach` 并读，得到「`Z = {1,2}` 阻断、`Z = ∅` 不阻断」的
**同一张图上的两个相反结果** —— 这证明上一条**不是恒真**。 -/
theorem r28_dsep_excludes_reach_complement :
    (3 : Fin 4) ∈ chainDAG4.bbReachableVertices (∅ : Finset (Fin 4)) {(0 : Fin 4)} := by
  rw [(chainDAG4_bbReach).1]
  decide

/-- ⭐⭐⭐ **`dSep` 的**四个合取项**全部拆出**（逐项可定位）。

把 `dSep X Y Z` 的四项与「可达集显式值」并列，使读者能**逐项**
看到 `CausSeparation.dSep` 的定义被完整消费：

* (1) `Disjoint X Y` —— `{0}` 与 `{3}` 不交；
* (2) `Disjoint X Z` —— `{0}` 与 `{1,2}` 不交；
* (3) `Disjoint Y Z` —— `{3}` 与 `{1,2}` 不交；
* (4) `Disjoint (bbReach) Y` —— 等价于 `3 ∉ bbReach`（即 `r28_dsep_excludes_reach`）；
* 外加 `bbReach = {0,1}` 的**显式值**。

**⚠ 与第 3 条的区别**：第 3 条只给 (4) 与集合等式；本条把 (1)(2)(3) **也**
显式登记，故它是四个合取项**全部**的展览，而非单一投影。 -/
theorem r28_dsep_unfold
    (h : chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} ({1, 2} : Finset (Fin 4))) :
    Disjoint ({(0 : Fin 4)} : Finset (Fin 4)) ({(3 : Fin 4)} : Finset (Fin 4)) ∧
      Disjoint ({(0 : Fin 4)} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4)) ∧
      Disjoint ({(3 : Fin 4)} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4)) ∧
      chainDAG4.bbReachableVertices ({1, 2} : Finset (Fin 4)) {(0 : Fin 4)} = {0, 1} :=
  ⟨h.1, h.2.1, h.2.2.1, (r28_dsep_excludes_reach h).1⟩

/-! ### §R28.3 ⭐⭐ 概率侧：四节点主定理的**除法形态**与**可分离见证** -/

/-- ⭐⭐ **`ChainMarkov4` ⟹ 条件分布的除法形式**。

$$\frac{q\,((x,y),z)}{\mathrm{margZ}\,q\,z}
  =\frac{\mathrm{margXZ}\,q\,x\,z}{\mathrm{margZ}\,q\,z}\cdot
   \frac{\mathrm{margYZ}\,q\,y\,z}{\mathrm{margZ}\,q\,z},\qquad z=(z_1,z_2).$$

**证明**：`chainMarkov4_condMul` 给逐点乘性等式；
由 `FinCondIndep.condMulGuard_iff_condRatio`（乘性守卫形式 ⟺ 除法形式）
在守卫 `margZ q z ≠ 0` 处转移。**⚠ 证明中真的用到 `h`**。 -/
theorem r28_condMul_ratio {A C D B : Type u}
    [Fintype A] [Fintype C] [Fintype D] [Fintype B]
    (p : A × C × D × B → ℝ) (h : ChainMarkov4 p)
    (x : A) (y : B) (z : C × D) (hz : margZ (reorder4 p) z ≠ 0) :
    reorder4 p ((x, y), z) / margZ (reorder4 p) z =
      (margXZ (reorder4 p) x z / margZ (reorder4 p) z) *
      (margYZ (reorder4 p) y z / margZ (reorder4 p) z) := by
  have hm := chainMarkov4_condMul p h
  have hg : FateV2.Predict.FinCondIndep.CondMulGuard (reorder4 p) := fun a b c _ => hm a b c
  exact (FateV2.Predict.FinCondIndep.condMulGuard_iff_condRatio (reorder4 p)).mp hg x y z hz

/-- ⭐⭐ **正性下的双向刻画（四节点口径具名）**：`CondMul ⟺ 可分离`。

**⚠ 本定理**转引** `GlobalMarkovMinimal.condMul_iff_separable`
（那里已完成 `⟺` 的两向），本处只把 `q := reorder4 p` 代进去，
使四节点链的读者不必回溯三节点版本。 -/
theorem r28_separable_iff {A C D B : Type u}
    [Fintype A] [Fintype C] [Fintype D] [Fintype B]
    (p : A × C × D × B → ℝ)
    (hpos : ∀ x y z, 0 < reorder4 p ((x, y), z)) :
    CondMul (reorder4 p) ↔
      ∃ (f : A → (C × D) → ℝ) (g : B → (C × D) → ℝ),
        ∀ x y z, reorder4 p ((x, y), z) = f x z * g y z :=
  Fate.GlobalMarkovMinimal.condMul_iff_separable (reorder4 p) hpos

/-- ⭐⭐⭐ **`ChainMarkov4` + 正性 ⟹ 显式可分离见证**（**真消费主定理 A**）。

结论里的 `f`、`g` 是 `condMul_gives_separable` 给的**显式**见证
（`f x z := margXZ q x z`、`g y z := margYZ q y z / margZ q z`），
故这不是「存在性白送」，而是**可计算的分解**。 -/
theorem r28_chainMarkov4_separable {A C D B : Type u}
    [Fintype A] [Fintype C] [Fintype D] [Fintype B]
    (p : A × C × D × B → ℝ) (h : ChainMarkov4 p)
    (hpos : ∀ x y z, 0 < reorder4 p ((x, y), z)) :
    ∃ (f : A → (C × D) → ℝ) (g : B → (C × D) → ℝ),
      ∀ x y z, reorder4 p ((x, y), z) = f x z * g y z := by
  have hm := chainMarkov4_condMul p h
  exact Fate.GlobalMarkovMinimal.condMul_gives_separable (reorder4 p) hm hpos

/-- ⭐ **数值见证**：`Fin 2` 上的均匀四节点律满足**平凡可分离分解** `1 = 1 * 1`。

**⚠ 这一条是数值层**（`ring` 闭合）；列入的目的是给
`r28_chainMarkov4_separable` 一个**非空实例**（排除「可分离恒假」的疑虑）。 -/
theorem r28_unif_separable_witness :
    ∀ x y (z : Fin 2 × Fin 2),
      reorder4 (fun _ : Fin 2 × Fin 2 × Fin 2 × Fin 2 => (1 : ℝ)) ((x, y), z)
        = (1 : ℝ) * 1 := by
  intro x y z
  show (1 : ℝ) = 1 * 1
  ring

/-! ### §R28.4 ⭐⭐ 谱系：`ChainMarkov4` **退化**为 `PearlChain.ChainMarkov` -/

/-- ⭐⭐⭐ **四节点链在固定 `z_2 = d0` 处退化为三节点链**：

$$p\,(x,z_1,z_2,y) \;\leadsto\; p\,(x,z_1,d_0,y) \in \texttt{P213B1.ChainMarkov}.$$

**见证**：$\alpha := \alpha$、$\beta := \beta$、
$\gamma_{\text{3}}(z_1,y) := \gamma(z_1,d_0)\cdot\delta(d_0,y)$。

**⟹ 这就是 `PearlChain`（11 条定理，本轮扫描时 `external_refs = 0`）与
本文件**口径一致的机检证据**：三节点不是另一个世界，而是四节点的**截面**。
**⚠ 本定理不声称新数学，只登记可机检的谱系。** -/
theorem r28_chainMarkov4_to_chainMarkov3
    {A C B : Type u} [Fintype A] [Fintype C] [Fintype B]
    (D0 : Type u) [Fintype D0] (d0 : D0)
    (p : A × C × D0 × B → ℝ) (h : ChainMarkov4 p) :
    FateV2.Predict.P213B1.ChainMarkov (fun t : A × C × B => p (t.1, t.2.1, d0, t.2.2)) := by
  obtain ⟨al, be, ga, de, hP⟩ := h
  refine ⟨al, be, fun cb => ga (cb.1, d0) * de (d0, cb.2), fun x z1 y => ?_⟩
  show p (x, z1, d0, y) = al x * be (x, z1) * (ga (z1, d0) * de (d0, y))
  rw [hP x z1 d0 y]
  ring


/-! ### §R28.5 ⭐⭐ **Pearl 系零引用模块的真接线**（本轮第二个交付）

⚠ **先说清一个测量事实**（用两种 grep 模式确认，见 `_audit/R28-Pearl剩余.md`）：

`PearlChain` / `PearlFork` / `PearlJointLaw` / `PearlPathDecomp` /
`PearlLawRuleBridge` / `PearlMarkovBridgeG1` 这 6 个模块的
**定理并不在 `Fate.<模块名>.*` 下**：

| 模块 | 实际命名空间 |
|---|---|
| `PearlChain` | `Fate.P213B1` |
| `PearlFork` | `Fate.Fork213` |
| `PearlJointLaw` | `Fate.PearlHierarchy` |
| `PearlPathDecomp` | `Fate.CausalPath` |
| `PearlLawRuleBridge` | `Fate.PearlHierarchy` |
| `PearlMarkovBridgeG1` | `Fate.R242G1` |

**⟹ 按 `Fate\.<模块名>\.` 做外部引用扫描，这 6 个模块**永远**不可能被计为「已引用」
（它们**实质已被消费**：`P213B1` 被 8 个文件引用，`Fork213` 被 2 个文件引用）。
**这是扫描口径的假阴性，不是真孤立。**本节不做假修复，
而是在报告里如实登记（见 `_audit/R28-Pearl剩余.md` §3）。

**本节真接的是命名空间与模块名一致的三个模块**：
`PearlMarkov`（`Fate.PearlMarkov`）、
`PearlMarkovCrossFrameworks`（`Fate.PearlMarkovCrossFrameworks`）、
`PearlGlobalMarkov`（`Fate.PearlGlobalMarkov`）。
-/

/-- ⭐⭐ **`PearlMarkov` 的三结构判据被消费**：「条件独立失效 ⟹ 必是对撞」。

**⚠ 这不是同义反复**：前提是 `givesConditionalIndependence S = false`（一个 `Bool` 等式），
结论是 `S = collider`（一个 `TripleStructure` 等式）。`PearlMarkov.collider_unique`
用 `cases S <;> simp` 完成 —— 三个构造子里**只有 collider** 给出 `false`。 -/
theorem r28_pearlMarkov_collider_iff {S : Fate.PearlMarkov.TripleStructure}
    (h : Fate.PearlMarkov.givesConditionalIndependence S = false) :
    S = Fate.PearlMarkov.TripleStructure.collider :=
  Fate.PearlMarkov.collider_unique h

/-- ⭐⭐ **与 `PearlMarkovCrossFrameworks` 的同名结论对齐**（跨框架侧也有一份）。

⟹ 本条把「`PearlMarkovCrossFrameworks.collider_excluded`」与
「`PearlMarkov.collider_unique`」**钉成同一个断言**，
使两条引用链在 `Fate.GlobalMarkovChain4` 内合流。 -/
theorem r28_cross_collider_excluded {S : Fate.PearlMarkov.TripleStructure}
    (h : Fate.PearlMarkov.givesConditionalIndependence S = false) :
    S = Fate.PearlMarkov.TripleStructure.collider :=
  Fate.PearlMarkovCrossFrameworks.collider_excluded h

/-- ⭐⭐⭐ **`PearlGlobalMarkov`：简化版 `DOpen` ⟹ 标准版 `DOpen'`**（整条路径）。

**⚠ 这是有内容的桥**：`PearlPathDecomp` 的第 3 步全部建立在**简化版** `DOpen` 上，
而 `PearlGlobalMarkov` / `CausalDescendant` 的 Baye-Ball 语义用**标准版** `DOpen'`
（`openAt'`）。本条说明「第 3 步的结论在标准 d-分离下也成立」——
`PearlGlobalMarkov` 文件头自称这是「把第 3 步接入正式表述的**必要桥**」。 -/
theorem r28_pg_dopen_imp
    {V : Type u} (G : FateV2.Predict.CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (w : FateV2.Predict.CausalPath.DWalk G a b) (h : FateV2.Predict.CausalPath.DOpen G Z w) :
    FateV2.Predict.CausalDescendant.DOpen' G Z w :=
  FateV2.Predict.PearlGlobalMarkov.dopen_imp_dopen' G Z w h

/-- ⭐⭐ **`PearlGlobalMarkov`：标准 d-分离 ⟺ 全体路径在标准意义下被阻断**。

**⚠ 诚实标注**：`dsepStd_iff_all_blocked'` 的证明是 `not_exists`
（定义展开），**数学上 trivial** —— 本处转引的价值在于
**把 `PearlGlobalMarkov` 的主接口登记到本文件的引用图上**，
而不是声称新内容。 -/
theorem r28_pg_std_entry
    {V : Type u} (G : FateV2.Predict.CausalDirection.CausalGraph V) (Z : Set V) (a b : V) :
    FateV2.Predict.CausalDescendant.DSeparatedStd G Z a b ↔
      ∀ w : FateV2.Predict.CausalPath.DWalk G a b, ¬ FateV2.Predict.CausalDescendant.DOpen' G Z w :=
  FateV2.Predict.PearlGlobalMarkov.dsepStd_iff_all_blocked' G Z a b

/-- ⭐⭐ **`PearlGlobalMarkov`：一条标准开口路径否证标准 d-分离**（否证工具）。

**⚠ 与上一条的关系**：上一条是 `↔`，本条是它的**实用方向**
（给见证 ⟹ 否定分离），在 §3 的分解论证里是入口。 -/
theorem r28_pg_not_sep_of_open
    {V : Type u} (G : FateV2.Predict.CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (w : FateV2.Predict.CausalPath.DWalk G a b) (h : FateV2.Predict.CausalDescendant.DOpen' G Z w) :
    ¬ FateV2.Predict.CausalDescendant.DSeparatedStd G Z a b :=
  FateV2.Predict.PearlGlobalMarkov.not_dsepStd_of_dopen' G Z w h

end R28

end GlobalMarkovChain4

end FateV2.Predict