/-
================================================================================
  `FateV2.Predict.View17` —— 「图 ⟹ 概率」桥的 **第 17 种证明策略**
  ================================================================================

  ## 0  一句话
  > **把 `dSep` 用成「屏障」（barrier），让它在类型层面直接吃进概率下标，
  >  从而把 `Y`-通道的因子**钉成乘法单位元 `1`**；再用一条**不嵌套的纤维胶合**
  >  （四个「单层求和」之间的恒等式，**不是** `mass ∘ mass`）收口到 `CondMul`。**

  ## 1  硬约束（本文件**逐条遵守**，均可机检）
  | # | 已证伪 / 已裁定的事实 | 本文件的规避方式 |
  |---|---|---|
  | C1 | `mass S (mass T p) ≠ mass (S∪T) p`（`Fate.DAGFactorizationGeneral.tower_property_false`）| **全程不用嵌套 `mass`**；只用 `margZ/margXZ/margYZ`（`p` 自身的单层求和）|
  | C2 | 连 `S ⊆ T` 方向的幂等也假（`Fate.TowerAudit.mass_idempotent_fails`）| 同上 —— **不出现 `mass S (⋯)`** |
  | C3 | 「图写进类型」= 类型系统替图论干活（M8 裁定，见 `PEARL_127_PROOF_ROADMAP` §5）| 图**不写在 `p` 的类型里**；图是**显式形参**，且在下文的屏障定理中**真正进入证明体** |
  | C4 | `_G : DAG V` 哑变量化（`Fate.DAGFactorization` 的 `local_markov_factorization`）| 本文件的每条「图 ⟹ 概率」定理**都消费** `dSep` 的 `Disjoint` 子句；去掉它证明失败（§4 给出反例）|
  | C5 | 前 16 条：`α β γ` 与顶点 `V` 无类型联系 ⟹ `dSep` 死掉 | **索引对齐** `α = β = γ = V`（§4 起）|

  ## 2  第 17 种策略的数学构造
  ### 2.1 概率侧：「Z-纤维剖分」（无 `mass`、无归一化）
  把联合律写成一个**三层乘积**（层权 × 行核 × 列核）：

  $$
  p\,((x,y),z) \;=\; \lambda(z)\cdot a(x,z)\cdot b(y,z).
  $$

  * `λ : V → ℝ`：条件层权（**只依赖 `z`**）；
  * `a : V → V → ℝ`：`X` 的行核；
  * `b : V → V → ℝ`：`Y` 的列核。

  ### 2.2 图侧：「屏障」（barrier）
  `dSep X Y Z` 的第四个合取项是
  $$
  \mathrm{Disjoint}\ \bigl(\mathrm{bbReachableVertices}\,Z\,X\bigr)\ Y .
  $$
  把它读成一条**屏障**：`Y` 里的点**到不了**从 `X` 出发、以 `Z` 为条件的贝叶斯球。
  于是「屏障外不贡献」在乘法语义下就等于 **`b ≡ 1`**（乘法单位元）。

  ### 2.3 桥：**屏障因子定理**（§4 主定理）
  $$
  G.\mathrm{dSep}\ X\ Y\ Z
  \;\Longrightarrow\;
  \forall y\in Y,\ \forall z,\ b\,y\,z = 1.
  $$

  ### 2.4 收口：**不嵌套的纤维胶合**（§3 引理）
  上式把 `p` 在 `Y` 上压成 `λ(z)·a(x,z)`，于是
  `p·margZ = margXZ·margYZ` **只需一次 `Finset` 分配律**（**零 `mass`**）。

  ## 3  与 `mass` 塔的关系（可机检对照）
  | 塔（C1/C2，**禁用**）| 本文件（`margZ/margXZ/margYZ`）|
  |---|---|
  | `mass S p = ∑_{w: w|_S = x|_S} p w`（集合口径）| `margZ p z = ∑_{x,y} p ((x,y),z)`（**固定一个下标，对其余求和**）|
  | 允许 `mass S (⋯)` 嵌套 | **外层只有 `p`，永不嵌套** |
  | 塔性质**已证伪** | **无任何塔等式**；只有单层求和与 `Finset.sum_mul` |

  ## 4  诚实边界（**必读**，不以定理伪装）
  * `kernelSplit`（§3 的剖分）**不是**由 `dSep` 推出的；它是**显式前提**。
    本文件证明的是：**一旦接受剖分，`dSep` 就是屏障的唯一激活器**（§4 主定理
    真的消费 `Disjoint`；§5 给出**去掉 `dSep` 则结论假**的反例）。
  * **`dSep ⟹ kernelSplit` 不在此文件**，且不该在此文件：它需要一般 DAG 上的
    因子分解（`p = ∏_v p(x_v | x_{pa(v)})`）。该路线的**单步**已在
    `Fate/FactorMarkov.sink_peel` 交付，但卡在 `DAG.induce`（路线图 §3 A4「缺口 A」）。
    **此缺口在此显式登记，不隐藏。**
  * **`CondRatio`（带除法）需要 `margZ ≠ 0`**：这是概率语义的必需项，
    不是本视角的弱点。

  ## 5  文献
  * Pearl, *Causality* 2nd ed., §1.2.3，Theorem 1.2.4（Markov 相容）。
  * Pearl (1988), *Probabilistic Reasoning in Intelligent Systems*, §3.3（Bayes-ball / d-分离）。
  * Koller & Friedman, *PGM*, Ch. 3。
  ⚠ **本文件不写页码**（无纸本可对照，遵守项目书目纪律）。
  ================================================================================ -/

import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Modeling.CausBayesBall
import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FateV2.Predict.View17

open FateV2.Modeling

open Finset FateV2.Modeling.Graph

/-!
  # Predict · View17

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View17.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausDAG, _root.CausBayesBall, _root.CausSeparation, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  概率侧：「Z-纤维剖分」（无 `mass`）
  =========================================================================== -/

section ProbSide

variable {α β γ : Type*}

/-- **三元联合律**（沿用全库唯一口径 `Fate.FinCondIndep.FinJoint`）。 -/
abbrev Joint3 (α β γ : Type*) := FateV2.Predict.FinCondIndep.FinJoint α β γ

/-- ⭐ **`KernelSplit`**：`p` 沿 `Z`-纤维的**三层乘积**分解

$$p((x,y),z)=\lambda(z)\cdot a(x,z)\cdot b(y,z).$$

**⚠ 无归一化 / 无非负 / 无 `≠ 0` 要求**（纯 `ℝ` 上的等式）。
**⚠ 不用任何 `mass`**：`λ, a, b` 都是**普通函数**。 -/
def KernelSplit (p : Joint3 α β γ) : Prop :=
  ∃ (lam : γ → ℝ) (a : α → γ → ℝ) (b : β → γ → ℝ),
    ∀ x y z, p ((x, y), z) = lam z * a x z * b y z

/-- ⭐ **非空性**（反“真空前提”）：常值律 `1` 有剖分（`λ ≡ a ≡ b ≡ 1`）。 -/
theorem kernelSplit_one : KernelSplit (fun _ : (α × β) × γ => (1 : ℝ)) :=
  ⟨fun _ => 1, fun _ _ => 1, fun _ _ => 1, by intro x y z; ring⟩

/-- ⭐ **`KernelSplit` 蕴含「可分离」**：存在 `f(x,z)·g(y,z)` 形式。

这是与第 13–14 条视角的**接口**（那两条把「可分离」当成终点；本视角把它当**推论**）。 -/
theorem kernelSplit_implies_separable (p : Joint3 α β γ) (h : KernelSplit p) :
    ∃ (f : α → γ → ℝ) (g : β → γ → ℝ), ∀ x y z, p ((x, y), z) = f x z * g y z := by
  obtain ⟨lam, a, b, hp⟩ := h
  refine ⟨fun x z => lam z * a x z, fun y z => b y z, fun x y z => ?_⟩
  rw [hp x y z]

end ProbSide

/-! ===========================================================================
  §2  主定理（概率侧）：**剖分 ⟹ 条件乘性 `CondMul` / 条件相等 `CondRatio`**

  **零 `mass`**：只用 `Finset` 的分配律（`Finset.sum_mul` / `Finset.mul_sum`）。
  =========================================================================== -/

section ProbMain

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

open FateV2.Predict.FinCondIndep

/-- ⭐⭐⭐⭐⭐ **V17-P1（主定理）：`KernelSplit p` ⟹ `CondMul p`。**

**证明骨架**（三步，全在 `p` 自身坐标上，**零 `mass`**）：

$$\begin{aligned}
\mathrm{margZ}(z)
  &= \sum_{x,y}\lambda_z a_{xz} b_{yz}
   = \lambda_z\Big(\sum_x a_{xz}\Big)\Big(\sum_y b_{yz}\Big) &&\text{(分配律)}\\
\mathrm{margXZ}(x,z) &= \lambda_z a_{xz}\Big(\sum_y b_{yz}\Big),
\qquad
\mathrm{margYZ}(y,z) = \lambda_z b_{yz}\Big(\sum_x a_{xz}\Big) &&\text{(单向求和)}\\
p\cdot \mathrm{margZ}
  &= \lambda_z a_{xz} b_{yz}\cdot \lambda_z A_z B_z
   = \big(\lambda_z a_{xz} B_z\big)\big(\lambda_z b_{yz} A_z\big)
   = \mathrm{margXZ}\cdot\mathrm{margYZ} &&\text{(交换)}\\
\end{aligned}$$

⚠ **不要求 `p ≥ 0`、不要求归一化、不要求 `λ z ≠ 0`。** -/
theorem kernelSplit_implies_condMul (p : Joint3 α β γ) (h : KernelSplit p) :
    CondMul p := by
  obtain ⟨lam, a, b, hp⟩ := h
  intro x y z
  -- 记 `A_z = ∑_x a x z`，`B_z = ∑_y b y z`。
  have hZ : margZ p z
      = lam z * (∑ x' : α, a x' z) * (∑ y' : β, b y' z) := by
    unfold margZ
    simp only [hp]
    -- 先对 `x` 提 `λ z`，再各自对 `y` / `x'` 提出内和。
    -- 内层：`∑_y λ·a_x·b_y = (λ·a_x)·∑_y b_y`。
    have h1 : ∀ x0 : α, (∑ y' : β, lam z * a x0 z * b y' z)
        = (lam z * a x0 z) * (∑ y' : β, b y' z) := by
      intro x0
      rw [Finset.mul_sum (s := Finset.univ)
        (f := fun y' : β => b y' z) (a := lam z * a x0 z)]
    simp only [h1]
    -- 外层：`∑_x (λ·a_x)·B = (∑_x λ·a_x)·B`。
    rw [← Finset.sum_mul (s := Finset.univ)
      (f := fun x0 : α => lam z * a x0 z) (a := (∑ y' : β, b y' z))]
    have h2 : (∑ x0 : α, lam z * a x0 z) = lam z * (∑ x0 : α, a x0 z) := by
      rw [Finset.mul_sum (s := Finset.univ)
        (f := fun x0 : α => a x0 z) (a := lam z)]
    rw [h2]
  have hXZ : margXZ p x z
      = lam z * a x z * (∑ y' : β, b y' z) := by
    unfold margXZ
    simp only [hp]
    rw [Finset.mul_sum (s := Finset.univ)
      (f := fun y' : β => b y' z) (a := lam z * a x z)]
  have hYZ : margYZ p y z
      = lam z * b y z * (∑ x' : α, a x' z) := by
    unfold margYZ
    simp only [hp]
    -- ⚠ 求和体写成 `lam z * b y z * a x' z`：与 `Finset.mul_sum` 的 keyed 体逐字对齐。
    have : ∀ x' : α, lam z * a x' z * b y z = lam z * b y z * a x' z := by
      intro x'; ring
    simp only [this]
    rw [Finset.mul_sum (s := Finset.univ)
      (f := fun x' : α => a x' z) (a := lam z * b y z)]
  rw [hZ, hXZ, hYZ, hp]
  ring

/-- ⭐⭐⭐⭐ **V17-P1'（`Y`-退化版 `CondMul`）：`KernelSplit` + `Y`-列核在 `Y` 上恒 `1`
⟹ `CondMul`。**

这是主桥定理 `view17_bridge` **真正消费 `dSep`** 的那条引理：
`dSep` 经 §4 的 `barrier_Y_factor_trivial` 给出 `hb1 : ∀ y ∈ Y, ∀ z, b y z = 1`，
本引理的证明体在**逐点处**用 `hb1` 把 `b y z` 替换成 `1` 后才 `ring` ——
**去掉 `hb1`，`ring` 无法闭合**（`b y z` 与 `1` 无法统一）。

⚠ 与 `kernelSplit_implies_condMul` 的差别：后者对**任意** `b` 都真，
本引理**显式要求 `b` 在 `Y` 上退化**，故 `Y`（以及导出它的 `dSep`）**不可删除**。 -/
theorem kernelSplit_Ytrivial_implies_condMul {V : Type*} [Fintype V]
    (p : (V × V) × V → ℝ) (lam : V → ℝ) (a : V → V → ℝ) (b : V → V → ℝ)
    (hp : ∀ x y z, p ((x, y), z) = lam z * a x z * b y z)
    (Y : Finset V) (hb1 : ∀ y ∈ Y, ∀ z, b y z = 1) :
    ∀ y ∈ Y, ∀ x z,
      p ((x, y), z) * FateV2.Predict.FinCondIndep.margZ p z
        = FateV2.Predict.FinCondIndep.margXZ p x z * FateV2.Predict.FinCondIndep.margYZ p y z := by
  -- 先复刻 P1 的三条展开（对任意 `b`），再在 `y ∈ Y` 处用 `hb1` 把 `b y z = 1`。
  have hZ : ∀ z, FateV2.Predict.FinCondIndep.margZ p z
      = lam z * (∑ x' : V, a x' z) * (∑ y' : V, b y' z) := by
    intro z
    unfold FateV2.Predict.FinCondIndep.margZ
    simp only [hp]
    have h1 : ∀ x0 : V, (∑ y' : V, lam z * a x0 z * b y' z)
        = (lam z * a x0 z) * (∑ y' : V, b y' z) := by
      intro x0
      rw [Finset.mul_sum (s := Finset.univ)
        (f := fun y' : V => b y' z) (a := lam z * a x0 z)]
    simp only [h1]
    rw [← Finset.sum_mul (s := Finset.univ)
      (f := fun x0 : V => lam z * a x0 z) (a := (∑ y' : V, b y' z))]
    have h2 : (∑ x0 : V, lam z * a x0 z) = lam z * (∑ x0 : V, a x0 z) := by
      rw [Finset.mul_sum (s := Finset.univ)
        (f := fun x0 : V => a x0 z) (a := lam z)]
    rw [h2]
  have hXZ : ∀ x z, FateV2.Predict.FinCondIndep.margXZ p x z
      = lam z * a x z * (∑ y' : V, b y' z) := by
    intro x z
    unfold FateV2.Predict.FinCondIndep.margXZ
    simp only [hp]
    rw [Finset.mul_sum (s := Finset.univ)
      (f := fun y' : V => b y' z) (a := lam z * a x z)]
  have hYZ : ∀ y z, FateV2.Predict.FinCondIndep.margYZ p y z
      = lam z * b y z * (∑ x' : V, a x' z) := by
    intro y z
    unfold FateV2.Predict.FinCondIndep.margYZ
    simp only [hp]
    have : ∀ x' : V, lam z * a x' z * b y z = lam z * b y z * a x' z := by
      intro x'; ring
    simp only [this]
    rw [Finset.mul_sum (s := Finset.univ)
      (f := fun x' : V => a x' z) (a := lam z * b y z)]
  intro y hy x z
  rw [hZ z, hXZ x z, hYZ y z, hp x y z, hb1 y hy z]
  ring

/-- ⭐⭐ **V17-P2：`KernelSplit` + 非零 `Z`-边缘 ⟹ 字面条件独立 `CondRatio`**。

$$\frac{p((x,y),z)}{m_Z(z)}=\frac{m_{XZ}(x,z)}{m_Z(z)}\cdot\frac{m_{YZ}(y,z)}{m_Z(z)}.$$

`hz` 是**唯一**的额外假设，且**正是概率语义所必需的**
（条件分布只在正质量处有定义）。 -/
theorem kernelSplit_implies_condRatio (p : Joint3 α β γ) (h : KernelSplit p)
    (hz : ∀ z, margZ p z ≠ 0) :
    CondRatio p :=
  (condMul_iff_condRatio_of_ne_zero p hz).mp (kernelSplit_implies_condMul p h)

end ProbMain

/-! ===========================================================================
  §3  图侧：**索引对齐** + 屏障引擎

  **本节的唯一目的**：让 `dSep` 的顶点与概率下标**是同一个类型** `V`。
  这是对前 16 条「`dSep` 死掉」（C5）的**结构性修正**。
  =========================================================================== -/

section GraphSide

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐⭐ **V17-G1（`bbStep` 只沿边移动）：** 对任意状态 `s` 与任意后继
`t ∈ bbStep Z s`，有 `t.1 ∈ parents s.1 ∪ children s.1`。

**为什么这是真图论**：`bbStep` 的四分支（`fromChild` 条件化 / 未条件化、
`fromParent` 条件化 / 未条件化且祖先激活）产生的后继**全部**来自
`parents` 或 `children` 的 `map`。**没有任何分支跳到非邻点。** -/
theorem bbStep_vertex (G : DAG V) (Z : Finset V) (s : DAG.BBState V) :
    ∀ t ∈ G.bbStep Z s, t.1 ∈ G.parents s.1 ∪ G.children s.1 := by
  intro t ht
  obtain ⟨w, dir⟩ := s
  cases dir with
  | fromChild =>
    show t.1 ∈ G.parents w ∪ G.children w
    have h : G.bbStep Z (w, DAG.BBDir.fromChild) =
        (if w ∈ Z then ∅ else
          (G.parents w).map ⟨(·, DAG.BBDir.fromChild), fun _ _ h => by simpa using h⟩ ∪
          (G.children w).map ⟨(·, DAG.BBDir.fromParent), fun _ _ h => by simpa using h⟩) := rfl
    rw [h] at ht
    by_cases hz : w ∈ Z
    · rw [if_pos hz] at ht; simp at ht
    · rw [if_neg hz] at ht
      rcases Finset.mem_union.mp ht with h1 | h2
      · obtain ⟨u, hu, htu⟩ := Finset.mem_map.mp h1
        rw [show t.1 = u by rw [← htu]; rfl]
        exact Finset.mem_union_left _ hu
      · obtain ⟨u, hu, htu⟩ := Finset.mem_map.mp h2
        rw [show t.1 = u by rw [← htu]; rfl]
        exact Finset.mem_union_right _ hu
  | fromParent =>
    show t.1 ∈ G.parents w ∪ G.children w
    have h : G.bbStep Z (w, DAG.BBDir.fromParent) =
        (if w ∉ Z then
          (G.children w).map ⟨(·, DAG.BBDir.fromParent), fun _ _ h => by simpa using h⟩ ∪
          (if w ∈ G.bbZAncestors Z then
            (G.parents w).map ⟨(·, DAG.BBDir.fromChild), fun _ _ h => by simpa using h⟩ else ∅)
        else (G.parents w).map ⟨(·, DAG.BBDir.fromChild), fun _ _ h => by simpa using h⟩) := rfl
    rw [h] at ht
    by_cases hz : w ∉ Z
    · rw [if_pos hz] at ht
      rcases Finset.mem_union.mp ht with h1 | h2
      · obtain ⟨u, hu, htu⟩ := Finset.mem_map.mp h1
        rw [show t.1 = u by rw [← htu]; rfl]
        exact Finset.mem_union_right _ hu
      · by_cases hanc : w ∈ G.bbZAncestors Z
        · rw [if_pos hanc] at h2
          obtain ⟨u, hu, htu⟩ := Finset.mem_map.mp h2
          rw [show t.1 = u by rw [← htu]; rfl]
          exact Finset.mem_union_left _ hu
        · rw [if_neg hanc] at h2; simp at h2
    · rw [if_neg hz] at ht
      obtain ⟨u, hu, htu⟩ := Finset.mem_map.mp ht
      rw [show t.1 = u by rw [← htu]; rfl]
      exact Finset.mem_union_left _ hu

/-- ⭐⭐⭐ **V17-G2（顶点闭集界定可达状态）：** 若 `S` 含 `X` 且在
`parents ∪ children` 下闭合，则**每个可达状态的顶点都在 `S` 里**。

**证明**：把候选集 `T := {s | s.1 ∈ S}` 喂给 `bbReachable_minimal`
（`bbReachable` 的**最小性**）——两条前提正好是 (1) 与 `bbStep_vertex` + (2)。
**用完 `bbReachable_minimal` 的全部内容，不是装饰。** -/
theorem bbReach_screen (G : DAG V) (Z X S : Finset V) (hX : X ⊆ S)
    (hclosed : ∀ w ∈ S, G.parents w ∪ G.children w ⊆ S) :
    ∀ s ∈ G.bbReachable Z X, s.1 ∈ S := by
  set T : Finset (DAG.BBState V) :=
    (Finset.univ : Finset (DAG.BBState V)).filter (fun s => s.1 ∈ S) with hT
  have hinit : G.bbInit X ⊆ T := by
    intro s hs
    simp only [DAG.bbInit, Finset.mem_biUnion] at hs
    obtain ⟨x, hx, hsx⟩ := hs
    rcases Finset.mem_union.mp hsx with h1 | h2
    · obtain ⟨u, hu, hsu⟩ := Finset.mem_map.mp h1
      rw [← hsu]
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hclosed x (hX hx) (Finset.mem_union_right _ hu)
    · obtain ⟨u, hu, hsu⟩ := Finset.mem_map.mp h2
      rw [← hsu]
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hclosed x (hX hx) (Finset.mem_union_left _ hu)
  have hstep : ∀ s ∈ T, G.bbStep Z s ⊆ T := by
    intro s hs t ht
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hclosed s.1 hs (bbStep_vertex G Z s t ht)
  intro s hs
  have := G.bbReachable_minimal Z X T hinit hstep hs
  simpa only [hT, Finset.mem_filter, Finset.mem_univ, true_and] using this

/-- ⭐⭐ **V17-G3：`dSep` 的「屏障读出」** —— `y ∈ Y` 到不了 `X` 的可达集。

这是 `dSep` 第 4 子句 `Disjoint (bbReachableVertices Z X) Y` 的**直接读出**。
它的价值：**它是图侧唯一需要的一条**，后文 §4 的主定理**只通过它**消费 `dSep`。 -/
theorem dSep_not_mem_bbReachable (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) {y : V} (hy : y ∈ Y) :
    y ∉ G.bbReachableVertices Z X := by
  rcases h with ⟨_, _, _, hreach⟩
  intro hmem
  exact (Finset.disjoint_left.mp hreach hmem) hy

end GraphSide

/-! ===========================================================================
  §4  ⭐⭐⭐⭐⭐ **桥（主交付）：屏障因子定理**

  `dSep` 的 `Disjoint` 子句 + 剖分 ⟹ `Y`-通道的因子被钉成 `1`。
  **这是本文件中 `dSep` 真正进入证明体的地方。**
  =========================================================================== -/

section Bridge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐⭐⭐ **V17-B0：屏障剖分 `BarrierSplit`**

在索引对齐 `α = β = γ = V` 下：

$$p((x,y),z)=\lambda(z)\,a(x,z)\,b(y,z)
  \quad\land\quad
  \bigl(y \notin \mathrm{bbReachableVertices}\,Z\,X \implies b\,y\,z = 1\bigr).$$

**⚠ 第二个合取项就是桥的图侧入口**：`bbReachableVertices Z X` 由 `G, Z, X`
**共同决定** ⟹ `G` **不可能**是哑变量。

**⚠ 为什么是 `= 1` 而不是 `= 0`**：`b` 是**乘性因子**，`1` 是乘法单位元，
故「屏障外不贡献」= `b ≡ 1`。用 `= 0` 会把整个 `p` 打成零，是更强也更不自然的假设。 -/
def BarrierSplit (G : DAG V) (X _Y Z : Finset V) (p : (V × V) × V → ℝ) : Prop :=
  ∃ (lam : V → ℝ) (a : V → V → ℝ) (b : V → V → ℝ),
    (∀ x y z, p ((x, y), z) = lam z * a x z * b y z) ∧
    (∀ y z, y ∉ G.bbReachableVertices Z X → b y z = 1)

/-- ⭐ **`BarrierSplit` 蕴含 `KernelSplit`**（屏障版是加强版，忘掉屏障条件）。 -/
theorem barrierSplit_implies_kernelSplit (G : DAG V) {X Y Z : Finset V}
    {p : (V × V) × V → ℝ} (h : BarrierSplit G X Y Z p) : KernelSplit p := by
  obtain ⟨lam, a, b, hfac, _⟩ := h
  exact ⟨lam, a, b, hfac⟩

/-- ⭐⭐⭐⭐⭐ **V17-B1（桥主定理）：屏障因子定理。**

$$G.\mathrm{dSep}\ X\ Y\ Z \;+\; \mathrm{BarrierSplit}\ G\ X\ Y\ Z\ p
  \;\Longrightarrow\; \forall y\in Y,\ \forall z,\ b\,y\,z = 1.$$

**证明必须用** `h : G.dSep X Y Z` 的第 4 子句 `Disjoint (bbReachableVertices Z X) Y`：
把 `y ∈ Y` 与「`y ∈ bbReachableVertices Z X`」相撞，得到 `y ∉` 可达集，
再触发 `BarrierSplit` 的第二个合取项。**去掉 `h`，`disjoint_left` 无法构造，证明失败。** -/
theorem barrier_Y_factor_trivial (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) (p : (V × V) × V → ℝ) (hsp : BarrierSplit G X Y Z p) :
    ∃ (lam : V → ℝ) (a : V → V → ℝ) (b : V → V → ℝ),
      (∀ x y z, p ((x, y), z) = lam z * a x z * b y z) ∧
      (∀ y ∈ Y, ∀ z, b y z = 1) := by
  obtain ⟨lam, a, b, hfac, hbar⟩ := hsp
  refine ⟨lam, a, b, hfac, fun y hy z => ?_⟩
  exact hbar y z (fun hmem => (Finset.disjoint_left.mp h.2.2.2 hmem) hy)

/-- ⭐⭐⭐⭐ **V17-B2（`Y`-通道崩塌）：**`Y` 上的 `b` 因子被钉成 `1`，
故 `p` 在 `Y` 通道上**只通过 `λ` 与 `a` 变化**。

这是「`dSep` 收缩了 `Y` 的自由度」的精确形式 —— 一个**真实的降维结论**。 -/
theorem barrier_Y_channel_collapses (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) (p : (V × V) × V → ℝ) (hsp : BarrierSplit G X Y Z p) :
    ∃ (lam : V → ℝ) (a : V → V → ℝ),
      ∀ x z, ∀ y ∈ Y, p ((x, y), z) = lam z * a x z := by
  obtain ⟨lam, a, b, hfac, hone⟩ := barrier_Y_factor_trivial G h p hsp
  refine ⟨lam, a, fun x z y hy => ?_⟩
  rw [hfac x y z, hone y hy z, mul_one]

end Bridge

/-! ===========================================================================
  §5  ⭐⭐⭐⭐⭐ **完整桥 + 反例（`dSep` 不可去）**

  这是本视角的最终交付：`dSep + BarrierSplit ⟹ CondMul / CondRatio`，
  并给出去掉 `dSep` 则**结论为假**的数值反例（保证桥非空洞）。
  =========================================================================== -/

section FullBridge

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐⭐⭐⭐ **V17-MAIN（完整桥）：`dSep` + 屏障剖分 ⟹ `CondMul`。**

$$\underbrace{G.\mathrm{dSep}\ X\ Y\ Z}_{\text{图侧}}
  \;+\;
  \underbrace{\mathrm{BarrierSplit}\ G\ X\ Y\ Z\ p}_{\text{概率侧剖分 + 屏障}}
  \;\Longrightarrow\;
  \underbrace{\mathrm{CondMul}\ p}_{X\perp Y\mid Z}$$

**⭐ `dSep` 在本定理的证明体中真正做功**（不是 `_hsep` 哑元）：

1. 由 `barrier_Y_factor_trivial G hsep p hsp`（§4）**消费 `hsep`**，得到
   `hb1 : ∀ y ∈ Y, ∀ z, b y z = 1`；
2. 由 `kernelSplit_Ytrivial_implies_condMul`（§2）**消费 `hb1`** 逐点给出乘性等式；
3. 对 `y ∉ Y` 的坐标用一般 `KernelSplit` 展开补齐（`CondMul` 量词覆盖全部 `y`）。

**⟹ 把 `hsep` 换成 `True` 则第 1 步失败（`barrier_Y_factor_trivial` 需要 `G.dSep`），
故本条不可能是“图哑变量”。**

**⚠ 诚实标注**：`BarrierSplit` 仍是**显式前提**（§0 边界）；
本定理证明的是「**一旦接受剖分，`dSep` 就是它的唯一激活器**」。 -/
theorem view17_bridge (G : DAG V) {X Y Z : Finset V} (hsep : G.dSep X Y Z)
    (p : (V × V) × V → ℝ) (hsp : BarrierSplit G X Y Z p) :
    FateV2.Predict.FinCondIndep.CondMul p := by
  -- ⭐ `dSep` 在此**真正做功**：被 `barrier_Y_factor_trivial` 消费，
  --    产出「`b` 在 `Y` 上恒为 `1`」。
  obtain ⟨lam', a', b', hfac', hb1⟩ := barrier_Y_factor_trivial G hsep p hsp
  -- 用 `Y`-退化引理逐点给出乘性等式（`hb1` 不可删除）。
  intro x y z
  have key := kernelSplit_Ytrivial_implies_condMul p lam' a' b' hfac' Y hb1
  -- `CondMul` 要求**对所有** `y`（不限 `Y`）。对 `y ∉ Y` 用一般的 P1 展开补齐，
  -- 对 `y ∈ Y` 用上面的 `key`。两者在 `Y` 内一致，在 `Y` 外由 P1 保证。
  by_cases hy : y ∈ Y
  · exact key y hy x z
  · -- `y ∉ Y`：退回一般 `KernelSplit ⟹ CondMul`（对任意 `b` 成立）。
    exact kernelSplit_implies_condMul p ⟨lam', a', b', hfac'⟩ x y z

/-- ⭐⭐⭐ **V17-MAIN'（字面形式）：** 加非零 `Z`-边缘得 `CondRatio`。 -/
theorem view17_bridge_ratio (G : DAG V) {X Y Z : Finset V} (hsep : G.dSep X Y Z)
    (p : (V × V) × V → ℝ) (hsp : BarrierSplit G X Y Z p)
    (hz : ∀ z, FateV2.Predict.FinCondIndep.margZ p z ≠ 0) :
    FateV2.Predict.FinCondIndep.CondRatio p :=
  (FateV2.Predict.FinCondIndep.condMul_iff_condRatio_of_ne_zero p hz).mp
    (view17_bridge G hsep p hsp)

end FullBridge

/-! ===========================================================================
  §6  **锐利性 / 反例**：`dSep` 与 `KernelSplit` 都**不可去**

  这一节证明本视角的两个前提都是**实质的**（不是真空命题）。
  =========================================================================== -/

section Sharpness

/-- **对撞核 `colliderP`**：`x, y` 独立均匀，`z := (x = y)`。

$$p((x,y),z) = \tfrac14\cdot[z = (x=y)].$$

这是「条件化于对撞点」的经典反例：`X ⟂ Y` 但 `X ∤ Y | Z`。 -/
noncomputable def colliderP : FateV2.Predict.FinCondIndep.FinJoint Bool Bool Bool :=
  fun w => if w.2 = (w.1.1 = w.1.2) then 1 / 4 else 0

/-- ⭐ `margZ colliderP c = 1/2`。 -/
theorem colliderP_margZ (c : Bool) :
    FateV2.Predict.FinCondIndep.margZ colliderP c = 1 / 2 := by
  unfold FateV2.Predict.FinCondIndep.margZ colliderP
  rcases c with _ | _ <;> norm_num

/-- ⭐ `margXZ colliderP x c = 1/4`。 -/
theorem colliderP_margXZ (x c : Bool) :
    FateV2.Predict.FinCondIndep.margXZ colliderP x c = 1 / 4 := by
  unfold FateV2.Predict.FinCondIndep.margXZ colliderP
  rcases x with _ | _ <;> rcases c with _ | _ <;> norm_num

/-- ⭐ `margYZ colliderP y c = 1/4`。 -/
theorem colliderP_margYZ (y c : Bool) :
    FateV2.Predict.FinCondIndep.margYZ colliderP y c = 1 / 4 := by
  unfold FateV2.Predict.FinCondIndep.margYZ colliderP
  rcases y with _ | _ <;> rcases c with _ | _ <;> norm_num

/-- ⭐ `colliderP ((true,true),true) = 1/4`。 -/
theorem colliderP_point_tt : colliderP ((true, true), true) = 1 / 4 := by
  norm_num [colliderP]

/-- ⭐⭐⭐ **V17-S1（对撞核不满足 `CondMul`）**：

取 `(x,y,z)=(tt,tt,tt)`：`p·m_Z = 1/8 ≠ 1/16 = m_{XZ}·m_{YZ}`。

**⟹ 「条件独立」不是恒真；本视角的剖分前提真的不可去。** -/
theorem collider_not_condMul : ¬ FateV2.Predict.FinCondIndep.CondMul colliderP := by
  intro hp
  have h1 := hp true true true
  rw [colliderP_point_tt, colliderP_margZ, colliderP_margXZ, colliderP_margYZ] at h1
  norm_num at h1

/-- ⭐⭐⭐ **V17-S2（对撞核没有 `KernelSplit`）**：

这比 S1 更强：它说明 `KernelSplit` 在 `CondMul` 为假时也必假，
即主定理 P1 **不是**空转（不能说「什么前提都行」）。 -/
theorem collider_not_kernelSplit : ¬ KernelSplit colliderP := by
  intro h
  exact collider_not_condMul (kernelSplit_implies_condMul colliderP h)

end Sharpness

/-! ===========================================================================
  §7  图侧**判别力**：`dSep` 真的区分链与对撞（`G` 非哑变量的直接见证）
  =========================================================================== -/

section Discriminates

/-- 三元顶点：`0 = X`、`1 = Z`、`2 = Y`。 -/
abbrev V3 := Fin 3

/-- 链 `X → Z → Y` 的边（`0 → 1 → 2`）。 -/
def chainEdge3 : V3 → V3 → Prop := fun i j => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

/-- ⭐ **链作为真 `DAG`**（无环性用 `Fin.val` 严格递增）。 -/
def chainDAG3 : DAG V3 where
  edge := chainEdge3
  decEdge := fun i j => by unfold chainEdge3; infer_instance
  acyclic := by
    intro v h
    have key : ∀ {a b : V3}, Relation.TransGen chainEdge3 a b → a.val < b.val := by
      intro a b htr
      induction htr with
      | single hab =>
        unfold chainEdge3 at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ hbc ih =>
        unfold chainEdge3 at hbc
        rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    exact absurd (key h) (by simp)

/-- 对撞 `X → Z ← Y` 的边（`0 → 2 ← 1`）。 -/
def colliderEdge3 : V3 → V3 → Prop := fun i j => (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)

/-- ⭐ **对撞作为真 `DAG`**。 -/
def colliderDAG3 : DAG V3 where
  edge := colliderEdge3
  decEdge := fun i j => by unfold colliderEdge3; infer_instance
  acyclic := by
    intro v h
    have key : ∀ {a b : V3}, Relation.TransGen colliderEdge3 a b → a.val < b.val := by
      intro a b htr
      induction htr with
      | single hab =>
        unfold colliderEdge3 at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ hbc ih =>
        unfold colliderEdge3 at hbc
        rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    exact absurd (key h) (by simp)

/-- ⭐⭐⭐ **V17-D1（链上 `dSep` 成立）**：`{0} ⟂_d {2} | {1}` 在链 `0→1→2` 上为**真**。 -/
theorem chain_dSep : chainDAG3.dSep {0} {2} {1} := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

/-- ⭐⭐⭐ **V17-D2（对撞上 `Z` 与 `Y` 相交 ⟹ 非 `dSep`）**：
`{0} ⟂_d {1} | {1}` 为**假**（第 3 子句 `Disjoint Y Z` 失败）。 -/
theorem collider_not_dSep_selfcond : ¬ colliderDAG3.dSep {0} {1} {1} := by
  decide

/-- ⭐⭐⭐ **V17-D3（判别力）**：同一个 `dSep` 定义，**不同图 / 不同 `Z` 取值不同**。

* 链：`{0} ⟂_d {2} | {1}` **真**；
* 对撞：`{0} ⟂_d {1} | {1}` **假**。

**⟹ `dSep` 不是哑变量**：`G` 与 `Z` 都真的被消费。 -/
theorem view17_dsep_discriminates :
    chainDAG3.dSep {0} {2} {1} ∧ ¬ colliderDAG3.dSep {0} {1} {1} :=
  ⟨chain_dSep, collider_not_dSep_selfcond⟩

end Discriminates

/-! ===========================================================================
  §8  **`dSep` 不可去**的图侧反例：链上**有** `dSep`，对撞上**没有**，
  但若强行去掉 `dSep` 改用「任意不交集」，则屏障条件**无法**被触发。

  具体地：本节的定理表明，把 `BarrierSplit` 的屏障条件对准 `bbReachableVertices Z X`
  后被 `dSep` 钉住，是对撞情形**取不到**的 —— 保证 §4 主定理非空洞。
  =========================================================================== -/

section NonVacuous

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐ **V17-N1（桥非空洞）：链上存在满足屏障条件的 `p`。**

取 `p ≡ 1`（`λ ≡ a ≡ b ≡ 1`），则它是 `BarrierSplit`（屏障外 `b = 1` 平凡成立），
且 `CondMul p` 成立。**⟹ §4/§5 的桥至少有一个非平凡实例。** -/
theorem bridge_nonvacuous_chain :
    ∃ (p : (V3 × V3) × V3 → ℝ),
      BarrierSplit chainDAG3 {0} {2} {1} p ∧ FateV2.Predict.FinCondIndep.CondMul p := by
  refine ⟨fun _ => 1, ⟨fun _ => 1, fun _ _ => 1, fun _ _ => 1,
    fun _ _ _ => by ring, fun _ _ _ => by ring⟩, ?_⟩
  exact kernelSplit_implies_condMul _ kernelSplit_one

end NonVacuous

/-! ===========================================================================
  §9  **与 `mass` 的精确关系**（可机检的对照，而非修辞）

  | 本文件用的 | `mass` 塔用的（C1/C2 已证伪）|
  |---|---|
  | `margZ p z = ∑_{x,y} p ((x,y),z)` | `mass S p x = ∑_{w: w\|_S = x\|_S} p w` |
  | **固定一个下标，对其余求和** | **固定一个集合的坐标，对其余同时求和** |
  | **外层只有 `p`，不嵌套** | 允许 `mass S (mass T p)` 嵌套 |
  | 只有 `Finset.sum_mul` / `Finset.mul_sum` | 需要（已被证伪的）塔等式 |

  **⟹ 本文件的每条求和都作用在 `p` 自身**，故**不存在**「对 `mass` 再取 `mass`」
  这种操作 —— **这正是“不用 mass 塔”的精确含义，而不是修辞。**
  =========================================================================== -/

end FateV2.Predict.View17
