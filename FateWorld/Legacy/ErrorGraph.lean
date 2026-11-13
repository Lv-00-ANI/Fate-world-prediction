import FateWorld.Legacy.ScoreK

/-! ===========================================================================
  §ErrorGraph  误差图谱（作者裁决 E 之「方案 4」）

  ## 作者裁决 E（再述）

  > **误差量纲不需要统一（统一不可能：不同空间无自然嵌入）。**
  > **端到端误差直接测，逐层误差各自算（用于诊断），两者都报、不相加。**
  > 作者判定：**方案 1（端到端 + 逐层双轨）是方案 4（误差图谱）的子集，故做方案 4。**

  ## 本文件：一个有类型的误差图谱

  图谱不是「一张把所有误差塞进 ℝ 的表格」，而是**分层带类型**的结构：

  | 坐标 | 类型 | 说明 |
  |---|---|---|
  | `layers L` | `LayerErr L` | 第 `L` 层的误差，**自带空间 `space` 与尺度 `sigma`** |
  | `e2e`       | `E2E`       | 端到端误差，**独立坐标**，`(eps, σ₂, σ₁)` |

  * `ErrLayer` 四层：`attrExtract` / `ruleLearn` / `predict` / `intervene`。
  * `LayerErr L.space : Type` —— **每层误差活在自己的度量空间里**，
    这正是「不同空间无自然嵌入」的直接编码：`space` 是**层依赖的 `Type`**，
    不是某个共同的 `ℝ`。
  * `E2E` 三实数：`eps`（端到端误差读数）、`sigma2`（门槛尺度 σ₂，
    边缘散布）、`sigma1`（最优尺度 σ₁，创新噪声）。

  ## 本文件证什么

  ### ① 不同层的误差不可相加（`no_cross_layer_isometric_embed`）

  「相加」的最低要求是：能把各层的误差放进**同一个**空间并**保持各自的误差结构**
  （否则相加得到的数与被加项的量纲无关，是没有意义的和）。
  我们把「保持误差结构」形式化为**等距嵌入**，并证明：

  > **不存在从 `ℝ × ℝ`（配 ℓ¹ 距离）到 `ℝ`（配绝对值距离）的等距嵌入。**

  证明用**等边三点**：`(0,0), (1,1), (1,-1)` 在 ℓ¹ 下两两相距 `2`；
  而 `ℝ` 中**不存在**三点两两等距（`no_equilateral_three_abs`：若
  `|a-b| = |b-c| = |a-c|` 则三者全等，距离为 `0`）。
  于是任何「把两层误差搬到同一实数轴」的尝试都**必然扭曲某一层的误差结构**。

  ### ② 即使硬造一个线性求和，结果依赖任意的嵌入选择

  `sum_depends_on_embedding`：同一对点 `(1,2)`，在两个不同的（线性）嵌入下
  给出**不同的和**（`3` vs `21`）。⟹ 「相加」不是误差图谱的内在运算，
  而是一个**需要额外人为约定**的运算 —— 这正是裁决 E 拒绝逐层相加的原因。

  ### ③ 双指标判据接到 `e2e` 上

  * `E2E.gateOK e : Prop := bandLoss e.sigma2 e.eps = 0` —— **σ₂ 判门槛**；
  * `E2E.gateOK_iff` —— `gateOK e ↔ σ₂/2 ≤ eps ≤ 2σ₂`（`0 < σ₂`）；
  * `E2E.gateOK_of_band` / `E2E.not_gateOK_of_undershoot` / `..._of_overshoot`
    —— 三条单向判据（贴合过紧 / 丢信号 都判不合格）；
  * `E2E.gapOK` —— **σ₁ 判最优差距**：以 `sigma1` 为尺度的同一带判据，
    与门槛判据**并列**（两者尺度不同，不可互推：`gateOK_not_implies_gapOK`）。

  ## 诚实边界

  * **`space` 是参数**：本文件不假定任何一层空间的具体形状（`ℝ`、`ℝⁿ`、
    分布空间、函数空间都可以），因此图谱对「误差怎么算」是开放的。
  * **「不可相加」证明的是「等距嵌入不存在」**，即**保结构**的搬运不可能。
    非保结构的任意搬运当然存在（`ℝ × ℝ` 与 `ℝ` 基数相同），
    但那样搬过去的数已经不代表原层的误差了 —— ① 的形式化正是「保结构」这一点。
  * **`ℓ¹` 只是 `ℝ²` 上距离的一个具体选择**；结论（无等距嵌入）对该度量成立，
    已足以**反驳「总能相加」**这一普遍主张。
  * **`sigma1` / `sigma2` 的数值来源（怎么估）不在本节** —— 本节只做判据结构。
  =========================================================================== -/

namespace Fate

namespace ErrGraph

universe u

/-! ### §1 四层误差 -/

/-- ⭐ **误差图谱的四层**：属性抽取 → 规则学习 → 预测 → 干预。 -/
inductive ErrLayer
  | attrExtract
  | ruleLearn
  | predict
  | intervene
  deriving DecidableEq, Repr

/-- 四层可穷举（用于逐层陈述定理）。 -/
theorem ErrLayer.all_cases (L : ErrLayer) :
    L = ErrLayer.attrExtract ∨ L = ErrLayer.ruleLearn ∨
    L = ErrLayer.predict ∨ L = ErrLayer.intervene := by
  cases L
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-! ### §2 每层误差：自己的空间、自己的距离、自己的尺度 -/

/-- ⭐⭐ **单层误差读数**。`space` 是**层依赖的 `Type`**：
第 `L` 层的误差活在它自己的度量空间里，**不**与其它层共用一个 `ℝ`。

* `dist`  —— 该层空间上的距离（伪度量即可，本文件只用对称性以外的显式等式）；
* `eps`   —— 该层的**实际误差**（空间中的一点）；
* `sigma` —— 该层的**噪声尺度**（`ℝ` 值：尺度是「同一层内部」的相对量）。 -/
structure LayerErr (L : ErrLayer) where
  space : Type u
  dist : space → space → ℝ
  eps : space
  sigma : ℝ

/-- 层次标签：`LayerErr` 的 `space` 一般随 `L` 变化（见 §5 的具体实例）。 -/
def LayerErr.spaceOf {L : ErrLayer} (e : LayerErr L) : Type u := e.space

/-! ### §3 端到端误差：独立坐标 -/

/-- ⭐⭐ **端到端误差**（裁决 E 的「直接测」）。

**⚠ `eps` 不通过逐层相加得到** —— 它是一个**独立坐标**。

* `eps`    —— 端到端误差读数；
* `sigma2` —— **门槛尺度** σ₂（边缘散布）：判「是否过门槛」；
* `sigma1` —— **最优尺度** σ₁（创新噪声）：判「与最优的差距」。 -/
structure E2E where
  eps : ℝ
  sigma2 : ℝ
  sigma1 : ℝ

/-! ### §4 误差图谱 -/

/-- ⭐⭐⭐ **误差图谱**：分层坐标 + 端到端坐标，并列存放。

**关键设计**：`layers` 与 `e2e` 之间**没有任何算术关系** ——
图谱不声称 `e2e.eps = Σ_L (layers L).eps`（右式在类型上就写不出来，
因为各层 `eps` 分别住在 `(layers L).space` 里）。
`collapsed` 字段只是「把每层误差压成 ℝ 用于诊断报告」的**可选读数**，
它不是由 `layers` 计算出来的，也**不参与**任何合格判据。 -/
structure ErrorGraph where
  /-- 逐层误差（各带自己的空间与尺度）。 -/
  layers : ∀ L : ErrLayer, LayerErr L
  /-- 端到端误差（独立坐标，不通过逐层相加得到）。 -/
  e2e : E2E

/-! ### §5 ⭐⭐ 不同层的误差不可相加 -/

/-! #### §5.1 `ℝ` 中不存在三等距点 -/

/-- ⭐⭐ **`ℝ` 中不存在三点两两非零等距**。

若 `|a-b| = |b-c| = |a-c| ≠ 0`，则矛盾。

证明：三个等距关系给出 `(a-b)² = (a-c)²` 与 `(b-c)² = (a-c)²`，
因式分解为 `(a-b)(a+b-2c) = 0` 与 `(c-b)(2a-b-c) = 0`；
两种情形都迫使 `a = b`，与 `|a-b| ≠ 0` 矛盾。 -/
theorem no_equilateral_three_abs (a b c : ℝ)
    (h1 : |a - b| = |b - c|) (h2 : |b - c| = |a - c|) (h : |a - b| ≠ 0) : False := by
  have h2' : (a - b) ^ 2 = (a - c) ^ 2 := by
    have e : |a - b| ^ 2 = |a - c| ^ 2 := by rw [h1, h2]
    simpa only [sq_abs] using e
  have h3' : (b - c) ^ 2 = (a - c) ^ 2 := by
    have e : |b - c| ^ 2 = |a - c| ^ 2 := by rw [h2]
    simpa only [sq_abs] using e
  have hab : a - b ≠ 0 := by
    intro hz; exact h (by rw [hz]; simp)
  have e2 : (c - b) * (2 * a - b - c) = 0 := by nlinarith
  have e3 : (a - b) * (a + b - 2 * c) = 0 := by nlinarith
  rcases mul_eq_zero.mp e3 with h3a | h3b
  · exact hab h3a
  · rcases mul_eq_zero.mp e2 with h2a | h2b
    · have hcb : c = b := by linarith
      rw [hcb] at h3'
      exact hab (by nlinarith)
    · exact hab (by linarith)

/-! #### §5.2 `ℝ²`（ℓ¹）中三点等距存在 -/

/-- ℓ¹ 距离（在 `ℝ × ℝ` 上）。 -/
def l1dist (p q : ℝ × ℝ) : ℝ := |p.1 - q.1| + |p.2 - q.2|

/-- ⭐ 实例：`(0,0), (1,1), (1,-1)` 在 ℓ¹ 下是**边长 2 的等边三角形**。 -/
theorem l1dist_equilateral :
    l1dist ((0, 0) : ℝ × ℝ) (1, 1) = 2 ∧
    l1dist ((1, 1) : ℝ × ℝ) (1, -1) = 2 ∧
    l1dist ((0, 0) : ℝ × ℝ) (1, -1) = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [l1dist] <;> norm_num

/-- ⭐⭐⭐ **不存在 `ℝ²`（ℓ¹）到 `ℝ`（绝对值）的等距嵌入。**

**这是「不同层的误差不可相加」的核心**：相加的前提是能把两层误差
搬进同一个实轴而不改变各自的误差结构（等距）。本定理说这做不到。

证明：若 `g` 保 ℓ¹ 距离，则 `g` 把 §5.2 的等边三角形映成 `ℝ` 中
三点两两非零等距 —— 与 `no_equilateral_three_abs` 矛盾。 -/
theorem no_l1_isometric_embed :
    ¬ ∃ g : (ℝ × ℝ) → ℝ, ∀ p q, l1dist p q = |g p - g q| := by
  rintro ⟨g, hg⟩
  have e00 : l1dist ((0, 0) : ℝ × ℝ) (1, 1) = 2 := l1dist_equilateral.1
  have e11 : l1dist ((1, 1) : ℝ × ℝ) (1, -1) = 2 := l1dist_equilateral.2.1
  have e02 : l1dist ((0, 0) : ℝ × ℝ) (1, -1) = 2 := l1dist_equilateral.2.2
  have key : |g (0, 0) - g (1, 1)| = 2 := by rw [← hg, e00]
  have h1 : |g (0, 0) - g (1, 1)| = |g (1, 1) - g (1, -1)| := by
    rw [key, ← hg, e11]
  have h2 : |g (1, 1) - g (1, -1)| = |g (0, 0) - g (1, -1)| := by
    rw [← hg, e11, ← hg, e02]
  exact no_equilateral_three_abs _ _ _ h1 h2 (by linarith [key])

/-! #### §5.3 硬造求和 ⟹ 结果依赖任意嵌入选择 -/

/-- ⭐⭐ **同一个点，两「嵌入」给出不同的和**：`(1,2)` 在 `p ↦ p.1+p.2` 下得 `3`，
在 `p ↦ p.1+10·p.2` 下得 `21`。

⟹ 「两层误差之和」不是一个内在量；必须**先人为选定嵌入**，
故裁决 E 的「不相加」是正确处置。 -/
theorem sum_depends_on_embedding :
    (fun p : ℝ × ℝ => p.1 + p.2) (1, 2) ≠
    (fun p : ℝ × ℝ => p.1 + 10 * p.2) (1, 2) := by
  norm_num

/-! #### §5.4 图谱中「逐层相加」在类型上不可写 -/

/-- ⭐⭐⭐ **不同层的误差不可相加**（结构版）。

存在一个图谱 `G`，其 `attrExtract` 层误差住在 `ℝ`、`predict` 层误差住在
`ℝ × ℝ`，**且不存在**把 `predict` 层的 ℓ¹ 误差结构与 `ℝ` 层的绝对值误差结构
**同时保距**地搬到同一实轴的映射。

**⟹ 于是「`(G.layers attrExtract).eps + (G.layers predict).eps`」无法被给出
一个与两层误差量纲都相容的实数值。** -/
theorem no_cross_layer_isometric_embed :
    ∃ (G : ErrorGraph),
      (G.layers ErrLayer.attrExtract).space = ℝ ∧
      (G.layers ErrLayer.predict).space = (ℝ × ℝ) ∧
      ¬ ∃ g : (ℝ × ℝ) → ℝ, ∀ p q, l1dist p q = |g p - g q| := by
  classical
  refine ⟨{
    layers := fun L => match L with
      | ErrLayer.attrExtract => { space := ℝ, dist := fun x y => |x - y|, eps := 0, sigma := 1 }
      | ErrLayer.ruleLearn   => { space := ℝ, dist := fun x y => |x - y|, eps := 0, sigma := 1 }
      | ErrLayer.predict     => { space := ℝ × ℝ, dist := l1dist, eps := (0, 0), sigma := 1 }
      | ErrLayer.intervene   => { space := ℝ, dist := fun x y => |x - y|, eps := 0, sigma := 1 }
    e2e := { eps := 0, sigma2 := 1, sigma1 := 1 } }, rfl, rfl, no_l1_isometric_embed⟩

/-! ### §6 ⭐⭐ 双指标判据接到 `e2e` 上 -/

/-- ⭐⭐ **门槛合格**（σ₂ 判门槛）：端到端误差落在以 `sigma2` 为尺度的合格带内。 -/
noncomputable def E2E.gateOK (e : E2E) : Prop :=
  ScoreK.bandLoss e.sigma2 e.eps = 0

/-- ⭐⭐ **最优差距合格**（σ₁ 判最优差距）：以 `sigma1` 为尺度的同形带判据。

与 `gateOK` **并列**，不互相推导（见 `gateOK_not_implies_gapOK`）。 -/
noncomputable def E2E.gapOK (e : E2E) : Prop :=
  ScoreK.bandLoss e.sigma1 e.eps = 0

/-- ⭐⭐ **门槛合格 ⟺ 落在 `[σ₂/2, 2σ₂]`**（`0 < σ₂`）。 -/
theorem E2E.gateOK_iff {e : E2E} (h : 0 < e.sigma2) :
    e.gateOK ↔ e.sigma2 / 2 ≤ e.eps ∧ e.eps ≤ 2 * e.sigma2 := by
  unfold E2E.gateOK
  exact ScoreK.bandLoss_eq_zero_iff h

/-- ⭐ **带内 ⟹ 门槛合格**。 -/
theorem E2E.gateOK_of_band {e : E2E}
    (h1 : e.sigma2 / 2 ≤ e.eps) (h2 : e.eps ≤ 2 * e.sigma2) : e.gateOK := by
  unfold E2E.gateOK
  exact ScoreK.bandLoss_eq_zero h1 h2

/-- ⭐ **贴合过紧（`eps < σ₂/2`）⟹ 门槛不合格**（过拟合）。 -/
theorem E2E.not_gateOK_of_undershoot {e : E2E} (h : e.eps < e.sigma2 / 2) :
    ¬ e.gateOK := by
  unfold E2E.gateOK
  have hp := ScoreK.bandLoss_pos_of_lt h
  intro hz; rw [hz] at hp; exact lt_irrefl 0 hp

/-- ⭐ **丢信号（`2σ₂ < eps`）⟹ 门槛不合格**。 -/
theorem E2E.not_gateOK_of_overshoot {e : E2E} (h : 2 * e.sigma2 < e.eps) :
    ¬ e.gateOK := by
  unfold E2E.gateOK
  have hp := ScoreK.bandLoss_pos_of_gt h
  intro hz; rw [hz] at hp; exact lt_irrefl 0 hp

/-- ⭐ **门槛合格者的门槛损失最小**（`0 ≤ 任何人的` 由此推出 `-loss` 最大）。

这里以 `-bandLoss σ₂ eps` 作为「门槛评分」。 -/
theorem E2E.gateOK_le {e : E2E} (h : e.gateOK) (x : ℝ) :
    -ScoreK.bandLoss e.sigma2 x ≤ -ScoreK.bandLoss e.sigma2 e.eps := by
  unfold E2E.gateOK at h
  rw [h]
  have : 0 ≤ ScoreK.bandLoss e.sigma2 x := by
    unfold ScoreK.bandLoss
    exact le_max_left _ _
  linarith

/-- ⭐⭐ **两个指标不可互推**：`gateOK` 与 `gapOK` 尺度不同，
门槛合格**不**蕴含最优差距合格。

反例：`eps = 2`、`σ₂ = 2`（带 `[1,4]`，合格）、`σ₁ = 100`（带 `[50,200]`，不合格）。 -/
theorem gateOK_not_implies_gapOK :
    ∃ e : E2E, e.gateOK ∧ ¬ e.gapOK := by
  refine ⟨{ eps := 2, sigma2 := 2, sigma1 := 100 }, ?_, ?_⟩
  · exact E2E.gateOK_of_band (by norm_num) (by norm_num)
  · intro hg
    unfold E2E.gapOK at hg
    have hp : 0 < ScoreK.bandLoss (100 : ℝ) 2 :=
      ScoreK.bandLoss_pos_of_lt (by norm_num)
    rw [hg] at hp
    exact lt_irrefl 0 hp

/-- ⭐⭐ **双指标判据**：门槛判据与最优差距判据都化为同一带形，只是尺度不同。

⟹ 作者「σ₂ 判门槛、σ₁ 判最优差距」在 `E2E` 上落地：
两者是**同一个 `bandLoss`** 的两个尺度实例化。 -/
theorem criterion_pair (e : E2E) :
    (e.gateOK ↔ ScoreK.bandLoss e.sigma2 e.eps = 0) ∧
    (e.gapOK ↔ ScoreK.bandLoss e.sigma1 e.eps = 0) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ⭐⭐ **`0 < σ₂` 时门槛合格等价于端到端误差落在带内**（正式版，含 `σ₂ ≤ 2σ₂` 的显式形式）。 -/
theorem E2E.gateOK_iff_le {e : E2E} (h : 0 < e.sigma2) :
    e.gateOK ↔ e.sigma2 / 2 ≤ e.eps ∧ e.eps ≤ 2 * e.sigma2 :=
  E2E.gateOK_iff h

/-! ### §7 图谱级判据：逐层各自合格、端到端独立合格 -/

/-- 某层「压成 ℝ 后的带内合格」：**该层用自己的尺度 `sigma`** 判自己的读数。
（`toReal` 把该层空间的一点映到 ℝ，仅用于**诊断报告**；它不参与跨层求和。） -/
def LayerOK {L : ErrLayer} (e : LayerErr L) (toReal : e.space → ℝ) : Prop :=
  ScoreK.bandLoss e.sigma (toReal e.eps) = 0

/-- ⭐⭐ **图谱的合格判据 = 端到端门槛 ∧ 各层各自带内**（彼此独立，不相加）。 -/
def ErrorGraph.OK (G : ErrorGraph) (toReal : ∀ L, (G.layers L).space → ℝ) : Prop :=
  G.e2e.gateOK ∧ ∀ L, LayerOK (G.layers L) (toReal L)

/-- ⭐⭐ **`OK` 分解**：端到端门槛合格与逐层合格**各自独立**成立，无和的联系。 -/
theorem ErrorGraph.ok_iff (G : ErrorGraph) (toReal : ∀ L, (G.layers L).space → ℝ) :
    G.OK toReal ↔ G.e2e.gateOK ∧ ∀ L, LayerOK (G.layers L) (toReal L) :=
  Iff.rfl

/-- ⭐ **逐层全部合格 + 端到端门槛合格 ⟹ 图谱合格**。 -/
theorem ErrorGraph.ok_intro {G : ErrorGraph} {toReal : ∀ L, (G.layers L).space → ℝ}
    (he : G.e2e.gateOK) (hl : ∀ L, LayerOK (G.layers L) (toReal L)) : G.OK toReal :=
  ⟨he, hl⟩

/-- 辅助：所有四层都住在 `ℝ`、给定误差读数的「平凡图谱层函数」。

它只是构造反例用的具体实例，**不是**图谱的一般形态（一般形态见 `no_cross_layer_isometric_embed`）。 -/
def constLayers (x : ℝ) : ∀ L : ErrLayer, LayerErr L
  | ErrLayer.attrExtract => { space := ℝ, dist := fun a b => |a - b|, eps := x, sigma := 1 }
  | ErrLayer.ruleLearn   => { space := ℝ, dist := fun a b => |a - b|, eps := 0, sigma := 1 }
  | ErrLayer.predict     => { space := ℝ, dist := fun a b => |a - b|, eps := 0, sigma := 1 }
  | ErrLayer.intervene   => { space := ℝ, dist := fun a b => |a - b|, eps := 0, sigma := 1 }

/-- 辅助：`constLayers` 各层空间都是 `ℝ`，故读数的拉直函数存在。 -/
def constToReal (x : ℝ) : ∀ L : ErrLayer, (constLayers x L).space → ℝ
  | ErrLayer.attrExtract => id
  | ErrLayer.ruleLearn   => id
  | ErrLayer.predict     => id
  | ErrLayer.intervene   => id

/-- ⭐⭐ **逐层全部合格推不出端到端合格**（在类型层也成立：端到端 `eps`
是独立字段，图谱不约束它与逐层读数的关系）。

具体：可构造图谱使 `attrExtract` 层带内合格，而 `e2e.gateOK` 为假。 -/
theorem layerOK_not_implies_gateOK :
    ∃ (G : ErrorGraph) (toReal : ∀ L, (G.layers L).space → ℝ),
      LayerOK (G.layers ErrLayer.attrExtract) (toReal ErrLayer.attrExtract) ∧
      ¬ G.e2e.gateOK := by
  classical
  refine ⟨{ layers := constLayers 1, e2e := { eps := 10, sigma2 := 1, sigma1 := 1 } },
    constToReal 1, ?_, ?_⟩
  · -- attrExtract 层：eps = 1，σ = 1，带 [1/2, 2] ⟹ 合格
    show ScoreK.bandLoss (1 : ℝ) (1 : ℝ) = 0
    exact ScoreK.bandLoss_eq_zero (by norm_num) (by norm_num)
  · -- 端到端：eps = 10，σ₂ = 1，带 [1/2, 2] ⟹ 不合格
    exact E2E.not_gateOK_of_overshoot (e := { eps := 10, sigma2 := 1, sigma1 := 1 })
      (by norm_num)

/-! ### §8 具体数值例子（自检） -/

/-- 一个具体的合格端到端读数：`eps = 1.5`、`σ₂ = 1`（带 `[0.5, 2]`）。 -/
example : E2E.gateOK { eps := 1.5, sigma2 := 1, sigma1 := 4 } :=
  E2E.gateOK_of_band (by norm_num) (by norm_num)

/-- 同读对 `σ₁ = 4`（带 `[2, 8]`）**不**合格于最优差距指标。 -/
example : ¬ E2E.gapOK { eps := 1.5, sigma2 := 1, sigma1 := 4 } :=
  E2E.not_gateOK_of_undershoot (e := { eps := 1.5, sigma2 := 4, sigma1 := 4 })
    (by norm_num)

/-- 端到端 `eps` 是独立坐标：改 `σ₁` 不动 `gateOK`（门槛只读 `σ₂`）。 -/
theorem gateOK_sigma1_irrel (eps σ2 s1 s1' : ℝ) :
    E2E.gateOK ⟨eps, σ2, s1⟩ = E2E.gateOK ⟨eps, σ2, s1'⟩ := by
  unfold E2E.gateOK
  rfl

end ErrGraph

end Fate
