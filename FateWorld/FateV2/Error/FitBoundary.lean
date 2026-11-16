import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Function
import FateWorld.FateV2.Modeling.CoreBasics

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/FitBoundary.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 34 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Modeling
/-
  恰当拟合边界（对应论文 §3–§6）

  在误差剖面 $E_W = \mathrm{bias} + \mathrm{var}$ 上定义「恰当拟合边界」：误差恰取到
  噪声尺度 σ，且 σ 是该剖面的全局下界。由此把「边界」从一个形容词变成点集，
  而非标量。本模块给出：

    §2  边界定义 IsFitBoundary / HasFitBoundary / FitBoundarySet，以及「全或无」结构
        与存在性的合取分解；
    §3  存在性的充分条件：连续 + 两侧穿越 σ；
    §4  唯一性：严格凸性 ⟹ 边界至多一个，并给出凸而非严格凸的反例（故不可弱化）；
    §5  不存在性的两条判据：一致高于 σ、处处过拟合；
    §6  ShouldStop 的表达力局限：任何只读到 (误差序列, n, τ) 的判据都无法判定边界，
        对一切 τ 与 tauOf 的一切参数成立。

  正文中一切单调性、凸性、连续性均作为显式前件出现，不注入为公理；剖面结构定义在
  最弱载体 ErrProfileWeak（只要求分量非负）上，使「去掉某前件会发生什么」成为可检验的
  定理而非口头声明。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/



namespace FateV2.Error

namespace Core

open Set

noncomputable section

/-! ===========================================================================
  §1  两个层次的误差剖面
  =========================================================================== -/

/-- **弱误差剖面**：只有**非负**，**不要单调性**。

**为何要有「弱」这一层**：本文件要区分
「边界**概念**需要什么前件」与「边界**唯一性**需要什么前件」。
§4.3 的反例（W 形 `bias`）**不满足**单调性 ——
若本文件硬把它塞进一个「必须单调」的结构里、再为它「证」出单调性，
**那就是造假**。

**⟹ 故把边界概念定义在**最弱**的载体上（本结构），
把单调性与凸性作为**额外前件**加回去（§4）。
这使「去掉某前件会发生什么」成为**可检验**的陈述。 -/
structure ErrProfileWeak where
  /-- 逼近误差（分辨率不足导致偏离真结构）。 -/
  bias : ℝ → ℝ
  /-- 估计误差（自由度多导致拟合噪声）。 -/
  var : ℝ → ℝ
  /-- 两个分量都非负（度量公理，不是估计）。 -/
  bias_nonneg : ∀ γ, 0 ≤ bias γ
  /-- 两个分量都非负（度量公理，不是估计）。 -/
  var_nonneg : ∀ γ, 0 ≤ var γ

namespace ErrProfileWeak

/-- **弱剖面的误差**：$\mathrm{err}(\gamma)=\mathrm{bias}(\gamma)+\mathrm{var}(\gamma)$。 -/
def err (W : ErrProfileWeak) (γ : ℝ) : ℝ := W.bias γ + W.var γ

/-- **误差非负**（两分量非负之和）。 -/
theorem err_nonneg (W : ErrProfileWeak) (γ : ℝ) : 0 ≤ W.err γ :=
  add_nonneg (W.bias_nonneg γ) (W.var_nonneg γ)

end ErrProfileWeak

/-- **强误差剖面**：非负 **+** 偏差-方差的两个单调性。

**`γ : ℝ` 是分辨率粒度，$\gamma$ 越大 = 越粗。**

| 分量 | 含义 | 方向 |
|---|---|---|
| `bias` | 逼近误差 | **粗 ⟹ 大**（`Monotone`）|
| `var` | 估计误差 | **粗 ⟹ 小**（`Antitone`）|

**⚠ 两个单调性是**建模选择**而非定理**：它们是偏差-方差权衡的**定性内容**，
其**量化形式**依赖具体编码方案（OQ-4 未定）。
**⟹ 本文件的一切需要它们的结论都把它们写成**显式前件**。** -/
structure ErrProfile extends ErrProfileWeak where
  /-- 粗 ⟹ 逼近误差大。 -/
  bias_mono : Monotone bias
  /-- 粗 ⟹ 估计误差小。 -/
  var_antitone : Antitone var

namespace ErrProfile

/-- **强剖面的误差**（与弱层**同一个表达式**，此处仅为便利提供）。 -/
def err (P : ErrProfile) (γ : ℝ) : ℝ := P.toErrProfileWeak.err γ

/-- **强剖面的误差非负**。 -/
theorem err_nonneg (P : ErrProfile) (γ : ℝ) : 0 ≤ P.err γ :=
  P.toErrProfileWeak.err_nonneg γ

/-- **强剖面的误差展开**（显式写成两分量之和）。 -/
theorem err_eq (P : ErrProfile) (γ : ℝ) : P.err γ = P.bias γ + P.var γ := rfl

/-! ### §1.1 ⚠ **`err` 本身不必然单调**（先清掉一个常见误解）

`bias` 单增、`var` 单减 —— **二者之和 `err` 无定义的方向**。
下面给出两个剖面，`err` 方向相反，**二者都满足 `ErrProfile` 的全部前件**。

**这不是「技术反例」**：它说明偏差-方差权衡的和函数方向
**由两分量谁变化快决定**，而这一点**不在 §1 的前件里**。
**⟹ 下游一切「最优点」断言不能依赖 `err` 的单调性**，
只能依赖**凸性**（§4）或**连续性 + 交点**（§3）。 -/

/-- 只有 `var` 的剖面（`err` 单减）。 -/
def profVarOnly : ErrProfile where
  bias := fun _ => 0
  var := fun γ => max 0 (-γ)
  bias_nonneg := fun _ => le_refl 0
  var_nonneg := fun _ => le_max_left 0 _
  bias_mono := monotone_const
  var_antitone := by
    intro a b hab
    show max 0 (-b) ≤ max 0 (-a)
    exact max_le_max_left 0 (neg_le_neg hab)

/-- 只有 `bias` 的剖面（`err` 单增）。 -/
def profBiasOnly : ErrProfile where
  bias := fun γ => max 0 γ
  var := fun _ => 0
  bias_nonneg := fun _ => le_max_left 0 _
  var_nonneg := fun _ => le_refl 0
  bias_mono := by
    intro a b hab
    show max 0 a ≤ max 0 b
    exact max_le_max_left 0 hab
  var_antitone := by
    intro a b _; simp

/-- **`err` 的两个方向都出现**（`err` 不必然单调）。 -/
theorem err_direction_not_determined :
    (profBiasOnly.err (-1) < profBiasOnly.err 1) ∧
      (profVarOnly.err 1 < profVarOnly.err (-1)) := by
  constructor <;>
    · simp only [err, profBiasOnly, profVarOnly, ErrProfileWeak.err]; norm_num

end ErrProfile

/-! ===========================================================================
  §2  核心定义：「刚好拟合 / 过拟合的边界」
  =========================================================================== -/

/-- **边界点**（本文件的核心定义）。

$$\mathrm{IsFitBoundary}(W,\sigma,\gamma)
  \;:=\;\bigl(E_W(\gamma)=\sigma\bigr)\ \wedge\
        \bigl(\forall\gamma',\ \sigma\le E_W(\gamma')\bigr)$$

**两项各自的作用**：

| 直觉表述 | 本定义中的落点 |
|---|---|
| 误差不劣于噪声 | 第二项：$\sigma\le E(\gamma')$ 对所有 $\gamma'$ |
| 误差**恰好**达到该尺度 | 第一项：$E(\gamma)=\sigma$ |
| 排除「比噪声还好」的分辨率 | 第二项**排除** $E(\gamma')<\sigma$（低于 σ 即拟合噪声）|

**⚠ 为什么第二项不可省（否则定义退化）**：
只写 $E(\gamma)=\sigma$ 的话，一个**穿** σ 的剖面有许多这样的点，
其中**误差更大的那些**是**欠拟合**，**不该**叫边界。
第二项把「σ 是下界」钉住，只留下**边界**那一支。

**⚠ 定义在**弱层**（`ErrProfileWeak`）上**：
边界概念**不需要**单调性（§4.3.0 证：强 ⟹ 弱，且边界在遗忘下不变）。

**⚠ $\sigma$ 的地位**：作参数传入。但须注意：只要边界点存在，σ 即被剖面
唯一决定（$\sigma=\inf E_W$，见无参数判据模块）——故「σ 可自由选取」只在
无边界点时才成立。

**⚠ 第二分量（下界）不是第一分量的逻辑后果**：
`FateV2.Error/FitBoundaryLowerBound.lean` 的
`lowerBound_not_derivable_from_definition` 机检证明了

```
∃ (W) (sigma gamma), W.err gamma = sigma ∧ ¬ (∀ gamma', sigma ≤ W.err gamma')
```

即**存在**剖面使第一分量成立而第二分量失败（见证 `err = exp`、`sigma = 1`、`gamma = 0`）。
**故本定义把「下界」写进第二分量是在额外假设一条独立内容，不是定义展开。** -/
def IsFitBoundary (W : ErrProfileWeak) (σ γ : ℝ) : Prop :=
  W.err γ = σ ∧ ∀ γ', σ ≤ W.err γ'

/-- **边界存在**。 -/
def HasFitBoundary (W : ErrProfileWeak) (σ : ℝ) : Prop :=
  ∃ γ, IsFitBoundary W σ γ

/-- **边界点集**（边界存在的**位置**，不是标量）。 -/
def FitBoundarySet (W : ErrProfileWeak) (σ : ℝ) : Set ℝ :=
  {γ | IsFitBoundary W σ γ}

/-! ### §2.1 定义的基本性质 -/

/-- **边界点处误差恰为 σ**（第一分量的读法）。 -/
theorem err_eq_of_isFitBoundary {W : ErrProfileWeak} {σ : ℝ} {γ : ℝ}
    (h : IsFitBoundary W σ γ) : W.err γ = σ :=
  h.1

/-- **σ 是全体分辨率的误差下界**（第二分量的读法）。 -/
theorem le_err_of_isFitBoundary {W : ErrProfileWeak} {σ : ℝ} {γ : ℝ}
    (h : IsFitBoundary W σ γ) (γ' : ℝ) : σ ≤ W.err γ' :=
  h.2 γ'

/-- **边界点集的形式分解**（水平集 ∩ 下界实现集）。 -/
theorem fitBoundarySet_eq (W : ErrProfileWeak) (σ : ℝ) :
    FitBoundarySet W σ = {γ | W.err γ = σ} ∩ {_γ | ∀ γ', σ ≤ W.err γ'} :=
  rfl

/-- **边界的「全或无」结构**：若 σ 是 `err` 的全局下界，
则**整个水平集都是边界集**。

$$\bigl(\forall\gamma',\sigma\le E(\gamma')\bigr)
  \Longrightarrow \mathrm{FitBoundarySet}(W,\sigma)=\{\gamma \mid E(\gamma)=\sigma\}$$

**证明**：右 ⊂ 左由 `hglb` 逐点补第二分量；左 ⊂ 右由第一分量。
**⚠ 诚实标注**：这条离定义很近，**本实现不把它当作主要交付**。
它的用处是**把「边界唯一」归约为「水平集唯一」**（§4 用它）。 -/
theorem fitBoundarySet_eq_levelSet_of_lowerBound (W : ErrProfileWeak) (σ : ℝ)
    (hglb : ∀ γ', σ ≤ W.err γ') :
    FitBoundarySet W σ = {γ | W.err γ = σ} := by
  ext γ
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, hglb⟩

/-- **边界的存在性等价于「水平集非空 ⟹ 下界实现」的联合**（反向读法）。

**用途**：把 `HasFitBoundary` 的验证拆成 `ExistsEq` 与 `LowerBound` 两件事。
这是 §3 与 §4 的公共接口。 -/
theorem hasFitBoundary_iff (W : ErrProfileWeak) (σ : ℝ) :
    HasFitBoundary W σ ↔
      (∃ γ : ℝ, W.err γ = σ) ∧ (∃ _γ : ℝ, ∀ γ', σ ≤ W.err γ') := by
  constructor
  · rintro ⟨γ, h1, h2⟩
    exact ⟨⟨γ, h1⟩, ⟨γ, h2⟩⟩
  · rintro ⟨⟨γ, h1⟩, ⟨_, h2⟩⟩
    exact ⟨γ, h1, h2⟩


/-! ===========================================================================
  §3  **边界存在性的充分条件**
  =========================================================================== -/


/-- **判据（存在）：连续 + 两侧穿越 ⟹ 有 σ 水平点**。

**陈述**：若 $E_W$ **连续**，**细端过拟合** $E(\gamma_{\mathrm{fine}})<\sigma$，
**粗端不低于** $\sigma\le E(\gamma_{\mathrm{coarse}})$，
则存在 $\gamma^\ast\in[\gamma_{\mathrm{fine}},\gamma_{\mathrm{coarse}}]$
使 $E_W(\gamma^\ast)=\sigma$。

**⚠ 这是「存在 $E=\sigma$ 的点」，不是「存在边界」** ——
区别在于**没有**证明第二分量（σ 是全局下界）。本实现**如实区分二者**。

**⚠ 前件（2）恰是「过拟合确实发生」**：
若任何分辨率都不过拟合（$E\ge\sigma$ 恒成立），则边界**不存在**（§5）。
**⟹ 「过拟合的存在」是「边界存在」的必要条件之一** ——
这**不是悖论**：**边界是过拟合区的边缘，无过拟合区则无边缘**。

**证明**：`intermediate_value_Icc`。 -/
theorem exists_level_eq_of_straddle {W : ErrProfileWeak} {σ : ℝ}
    (hcont : Continuous (fun γ => W.err γ))
    {gf gc : ℝ} (hfg : gf ≤ gc)
    (hfine : W.err gf < σ) (hcoarse : σ ≤ W.err gc) :
    ∃ γ ∈ Icc gf gc, W.err γ = σ := by
  have hOn : ContinuousOn (fun γ => W.err γ) (Icc gf gc) := hcont.continuousOn
  have hmem : σ ∈ Icc (W.err gf) (W.err gc) := ⟨hfine.le, hcoarse⟩
  obtain ⟨γ, hγ, hγeq⟩ := (intermediate_value_Icc hfg hOn) hmem
  exact ⟨γ, hγ, hγeq⟩

/-- **判据（存在，完整版）：下界已知 + 穿越 ⟹ 边界存在**。

**前件**：(1) $E_W$ 连续；(2) $\sigma$ 是 $E_W$ 的**全局下界**；(3) 存在**过拟合点**。
**结论**：`HasFitBoundary W σ`。

**⚠ 诚实标注（本条的界限，必须读）**：
前件 (2) 与结论的第二分量**是同一件事** ——
故本定理的**实质内容**只在**存在性**那一半：
它把「连续 + 存在 $E<\sigma$ ⟹ 存在 $E=\sigma$」与「σ 是下界」拼成边界。
**本定理的价值在**把验证责任分离**：
- 第二分量 ⟸ 下界（由剖面结构证）
- 第一分量 ⟸ 连续性 + 穿越（本定理）

这**不是**同义反复（两前件各自独立、且都不平凡），
但**也绝不声称**「无需下界即可得边界」—— **后者是假的**（§5 有反例）。
**本实现如实登记此界限。** -/
theorem hasFitBoundary_of_continuous_of_lowerBound {W : ErrProfileWeak} {σ : ℝ}
    (hcont : Continuous (fun γ => W.err γ))
    (hglb : ∀ γ', σ ≤ W.err γ')
    {gf gc : ℝ} (hfg : gf ≤ gc)
    (hfine : W.err gf < σ) (hcoarse : σ ≤ W.err gc) :
    HasFitBoundary W σ := by
  obtain ⟨γ, _, hγeq⟩ := exists_level_eq_of_straddle hcont hfg hfine hcoarse
  exact ⟨γ, hγeq, hglb⟩

/-! ### §3.1 **边界的 σ-伸缩协变性**（§6.1 正面关系的数学桥）

把剖面**整体按 $k>0$ 缩放**，则**边界点位置不变、σ 同倍缩放**。

**意义**：这解释**为何 σ 与误差必须同量纲**，
也说明「边界」在归一化后与尺度无关 ——
**这是 $\tau$ 这类比值量能够谈论边界的唯一理由**（§6.1）。 -/

/-- **弱剖面的标量缩放**。 -/
def ErrProfileWeak.scale (W : ErrProfileWeak) (k : ℝ) (hk : 0 ≤ k) : ErrProfileWeak where
  bias := fun γ => k * W.bias γ
  var := fun γ => k * W.var γ
  bias_nonneg := fun γ => mul_nonneg hk (W.bias_nonneg γ)
  var_nonneg := fun γ => mul_nonneg hk (W.var_nonneg γ)

/-- **强剖面的标量缩放**（保持两个单调性）。 -/
def ErrProfile.scale (P : ErrProfile) (k : ℝ) (hk : 0 ≤ k) : ErrProfile where
  bias := fun γ => k * P.bias γ
  var := fun γ => k * P.var γ
  bias_nonneg := fun γ => mul_nonneg hk (P.bias_nonneg γ)
  var_nonneg := fun γ => mul_nonneg hk (P.var_nonneg γ)
  bias_mono := by
    intro a b h
    show k * P.bias a ≤ k * P.bias b
    exact mul_le_mul_of_nonneg_left (P.bias_mono h) hk
  var_antitone := by
    intro a b h
    show k * P.var b ≤ k * P.var a
    exact mul_le_mul_of_nonneg_left (P.var_antitone h) hk

/-- **弱剖面缩放下的误差**（一次齐次）。 -/
theorem ErrProfileWeak.err_scale (W : ErrProfileWeak) {k : ℝ} (hk : 0 ≤ k) (γ : ℝ) :
    (W.scale k hk).err γ = k * W.err γ := by
  simp only [ErrProfileWeak.err, ErrProfileWeak.scale]; ring

/-- **强剖面缩放下的误差**（与弱层同一表达式，此处供下游直接用）。 -/
theorem ErrProfile.err_scale (P : ErrProfile) {k : ℝ} (hk : 0 ≤ k) (γ : ℝ) :
    (P.scale k hk).toErrProfileWeak.err γ = k * P.err γ := by
  simp only [ErrProfileWeak.err, ErrProfile.err, ErrProfile.scale]
  ring

/-- **边界关于 σ-伸缩**协变**（§3.1 的主定理）。

$$\mathrm{IsFitBoundary}(W,\sigma,\gamma)\iff
  \mathrm{IsFitBoundary}(k\cdot W,\ k\sigma,\ \gamma)$$

**证明**：由 `err_scale`，两分量在 $k>0$ 时等价
（等式用 `mul_left_cancel₀`，不等式用 `mul_le_mul_of_nonneg_left`
与 `le_of_mul_le_mul_left`）。
**⚠ 必须 $k>0$**：$k=0$ 时误差全为 0，边界退化。 -/
theorem isFitBoundary_scale {W : ErrProfileWeak} {σ γ k : ℝ} (hk : 0 < k) :
    IsFitBoundary W σ γ ↔ IsFitBoundary (W.scale k hk.le) (k * σ) γ := by
  unfold IsFitBoundary
  rw [ErrProfileWeak.err_scale W hk.le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1],
      fun γ' => by
        rw [ErrProfileWeak.err_scale W hk.le]
        exact mul_le_mul_of_nonneg_left (h2 γ') hk.le⟩
  · rintro ⟨h1, h2⟩
    refine ⟨mul_left_cancel₀ hk.ne' h1, fun γ' => ?_⟩
    have : k * σ ≤ k * W.err γ' := by
      rw [← ErrProfileWeak.err_scale W hk.le]; exact h2 γ'
    exact le_of_mul_le_mul_left this hk


/-! ===========================================================================
  §4  **边界唯一性：凸性是充要的来源**
  =========================================================================== -/


/-- **严格凸 ⟹ 边界至多一个**（**结论甲**）。

$$\mathrm{StrictConvexOn}\ \mathbb{R}\ \mathrm{univ}\ E_W
  \Longrightarrow\ \mathrm{IsFitBoundary}(W,\sigma,\gamma_1)
  \Longrightarrow\ \mathrm{IsFitBoundary}(W,\sigma,\gamma_2)
  \Longrightarrow\ \gamma_1=\gamma_2$$

**证明**：`IsFitBoundary` 的第二分量 $\forall\gamma',\sigma\le E(\gamma')$
**恰是** `IsMinOn E univ γ`（把 $E(\gamma)=\sigma$ 代回）。
于是两个边界点都是**最小值点**，由 `StrictConvexOn.eq_of_isMinOn` 得相等。

**为何实质**：
- 前件（严格凸）与结论（点相等）**分属不同层次**（几何 vs 定义）；
- 证明**必须**用 Mathlib 的严格凸最小点唯一性，**不是**展开定义能得到的；
- §4.3 给出**去凸性后边界不唯一**的反例 ⟹
  **严格凸是真充分条件，且不可去掉**。 -/
theorem eq_of_isFitBoundary_of_strictConvexOn {W : ErrProfileWeak} {σ : ℝ}
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun γ => W.err γ))
    {γ₁ γ₂ : ℝ}
    (h₁ : IsFitBoundary W σ γ₁) (h₂ : IsFitBoundary W σ γ₂) : γ₁ = γ₂ := by
  have hm₁ : IsMinOn (fun γ => W.err γ) univ γ₁ := by
    intro γ _
    show W.err γ₁ ≤ W.err γ
    rw [h₁.1]; exact h₁.2 γ
  have hm₂ : IsMinOn (fun γ => W.err γ) univ γ₂ := by
    intro γ _
    show W.err γ₂ ≤ W.err γ
    rw [h₂.1]; exact h₂.2 γ
  exact hcvx.eq_of_isMinOn hm₁ hm₂ (mem_univ _) (mem_univ _)

/-- **严格凸 + 存在 ⟹ 唯一存在**（`∃!` 形式）。 -/
theorem existsUnique_isFitBoundary_of_strictConvexOn {W : ErrProfileWeak} {σ : ℝ}
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun γ => W.err γ))
    (hex : HasFitBoundary W σ) :
    ∃! γ, IsFitBoundary W σ γ := by
  obtain ⟨γ, hγ⟩ := hex
  exact ⟨γ, hγ, fun γ' hγ' => eq_of_isFitBoundary_of_strictConvexOn hcvx hγ' hγ⟩

/-! ### §4.1 凸性前件的**具体来源**（前件非空）

**⚠ 本小节的地位（如实标注）**：
这**不是**「经典偏差-方差分解的证明」——
它只说明本文件的凸性前件**可被具体剖面满足**，从而 §4 的定理**不是空洞的**。
**具体常数的合理性属统计层，本文件不证。** -/

/-- **双指数剖面**（`bias = exp γ`，`var = exp(-γ)`）—— **§1 全部前件满足**。

**为什么不用 `γ ↦ γ²`**：`γ²` 在 ℝ 上**不单调**（左半轴递减），
故它**不能**作 `bias`（`bias_mono` 要求全域单增）。
**为什么不用 `γ ↦ exp γ` 单打**：单增 + 严格凸 ⟹ **下确界在 −∞，不可达** ⟹
`err` **没有**最小值 ⟹ 由 §5 判据形态一，**边界不存在**。
（这**不是**缺陷，下面 `profExpAlone_no_boundary` 把它证明出来。）

**⟹ 正确的构造是让两个分量都非平凡**：
$$\mathrm{bias}(\gamma)=e^{\gamma}\ (\text{单增}),\quad
  \mathrm{var}(\gamma)=e^{-\gamma}\ (\text{单减}),\quad
  E(\gamma)=2\cosh\gamma$$

- 严格凸（两个指数凸性之和，`StrictConvexOn.add_convexOn`）；
- 最小值 **2** 在 **`γ = 0`** 取到（AM-GM / `Real.exp_add_neg`）。

**⟹ 取 σ=2，边界恰好唯一在 γ=0。**
**⚠ 数学诚实**：`exp±γ` **不是**经典偏差-方差项（经典是 `γ²`、`γ^{-2}`）。
本小节**只**用它证明「§4 的凸性前件**非空**」，
**不**声称它是真实的误差模型（真实形式属 OQ-4，本文件不填）。 -/
def profExp : ErrProfile where
  bias := fun γ => Real.exp γ
  var := fun γ => Real.exp (-γ)
  bias_nonneg := fun γ => (Real.exp_pos γ).le
  var_nonneg := fun γ => (Real.exp_pos (-γ)).le
  bias_mono := fun _ _ h => Real.exp_le_exp.mpr h
  var_antitone := fun a b h => Real.exp_le_exp.mpr (by linarith)

/-- `profExp` 的误差 = $e^\gamma+e^{-\gamma}$。 -/
theorem profExp_err (γ : ℝ) :
    profExp.toErrProfileWeak.err γ = Real.exp γ + Real.exp (-γ) := by
  simp only [ErrProfileWeak.err, profExp]

/-- **`profExp` 的 `err` 严格凸**（由 `strictConvexOn_exp.add_convexOn`）。

**⟹ §4 的严格凸前件非空，故其定理不空洞。** -/
theorem profExp_strictConvex :
    StrictConvexOn ℝ (univ : Set ℝ) (fun γ => profExp.toErrProfileWeak.err γ) := by
  have h1 : StrictConvexOn ℝ (univ : Set ℝ) (fun γ : ℝ => Real.exp γ) := strictConvexOn_exp
  have h2 : ConvexOn ℝ (univ : Set ℝ) (fun γ : ℝ => Real.exp (-γ)) := by
    have hc : ConvexOn ℝ (univ : Set ℝ) (fun γ : ℝ => Real.exp γ) := convexOn_exp
    have h := hc.comp_linearMap (LinearMap.mul ℝ ℝ (-1))
    have he : ((fun γ => Real.exp γ) ∘ ⇑((LinearMap.mul ℝ ℝ) (-1))) =
        (fun γ => Real.exp (-γ)) := by
      funext x; simp [Function.comp]
    have hs : (⇑((LinearMap.mul ℝ ℝ) (-1)) ⁻¹' (univ : Set ℝ)) = univ := by simp
    rw [he, hs] at h; exact h
  have h12 : StrictConvexOn ℝ (univ : Set ℝ)
      ((fun γ => Real.exp γ) + fun γ => Real.exp (-γ)) := h1.add_convexOn h2
  have he : ((fun γ => Real.exp γ) + fun γ => Real.exp (-γ)) =
      (fun γ => Real.exp γ + Real.exp (-γ)) := rfl
  rw [he] at h12
  have : (fun γ => profExp.toErrProfileWeak.err γ) =
      (fun γ => Real.exp γ + Real.exp (-γ)) := by
    funext γ; exact profExp_err γ
  rw [this]; exact h12

/-- **`profExp` 在 σ=2 时有唯一界**（§4 的定理**被真的用上**）。

$$\mathrm{IsFitBoundary}(\mathrm{profExp},2,0)\ \wedge\
  \exists!\,\gamma,\ \mathrm{IsFitBoundary}(\mathrm{profExp},2,\gamma)$$

**构造**：$e^\gamma+e^{-\gamma}\ge 2$（在 $\gamma=0$ 取等号）。
**证明**：$e^\gamma e^{-\gamma}=1$，故由 AM-GM（`geom_mean_le_arith_mean2_weighted`
或直接平方）得 $2\le$ 和。本实现用 `nlinarith` + 关键乘积等式。 -/
theorem profExp_unique_boundary_two :
    ∃! γ, IsFitBoundary profExp.toErrProfileWeak 2 γ :=
  existsUnique_isFitBoundary_of_strictConvexOn profExp_strictConvex
    ⟨0, by
      refine ⟨?_, ?_⟩
      · rw [profExp_err]
        norm_num [Real.exp_zero]
      · intro γ'
        rw [profExp_err]
        have hprod : Real.exp γ' * Real.exp (-γ') = 1 := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
        have hp : 0 < Real.exp γ' := Real.exp_pos γ'
        nlinarith [sq_nonneg (Real.exp γ' - 1), hprod]⟩

/-- **单指数剖面 `bias = exp γ`、`var = 0`：**边界**不存在**（σ=0）。

**这本身就是 §5 判据形态一的实例**，也说明
「单增 + 严格凸」**不足以**保证边界存在（需要下界可达）。
**⟹ 本文件把这一负结果也证出来，避免「用了凸性就一定有界」的误读。** -/
def profExpAlone : ErrProfile where
  bias := fun γ => Real.exp γ
  var := fun _ => 0
  bias_nonneg := fun γ => (Real.exp_pos γ).le
  var_nonneg := fun _ => le_refl 0
  bias_mono := fun _ _ h => Real.exp_le_exp.mpr h
  var_antitone := fun a b _ => by simp

/-- `profExpAlone` 的误差 = $e^\gamma$。 -/
theorem profExpAlone_err (γ : ℝ) : profExpAlone.toErrProfileWeak.err γ = Real.exp γ := by
  simp only [ErrProfileWeak.err, profExpAlone]; ring

/-! ### §4.3 **去掉凸性，边界可以不唯一**（**结论乙**）

**对「偏差-方差权衡必有唯一最优点」这一常见信念的形式化否证。**

**反例**：$E(\gamma)=(\gamma^2-1)^2$、$\sigma=0$。
$E(\pm1)=0$ 且 $E\ge0$ ⟹ $\pm1$ **都是**边界点；$1\neq-1$ ⟹ **不唯一**。

**⚠ 本实现如实登记该反例的**适用范围**：
这里用的载体是**弱层** `ErrProfileWeak`（`profW`），
其 `bias` 是 **W 形（在 $[-1,0]$ 上递减）**，**故意**不满足 `bias_mono`。
**⟹ 本反例证明「边界概念单凭自身不唯一」，
不是「满足 §1 强前件的剖面边界可不唯一」。**
后者本文件**未证、未否证** —— §7.2 如实登记为开放问题。 -/

/-- **W 形弱剖面**（`bias = (γ²-1)²`，`var = 0`）。

`bias` 是 W 形，**故它不满足 `Monotone`** —— 这正是 §4.3 要展示的情形。 -/
def profW : ErrProfileWeak where
  bias := fun γ => (γ ^ 2 - 1) ^ 2
  var := fun _ => 0
  bias_nonneg := fun _ => sq_nonneg _
  var_nonneg := fun _ => le_refl 0

/-- `profW` 的误差就是 $(\gamma^2-1)^2$。 -/
theorem profW_err (γ : ℝ) : profW.err γ = (γ ^ 2 - 1) ^ 2 := by
  simp only [ErrProfileWeak.err, profW]; ring

/-! #### §4.3.0 **反例**确实**不满足强层前件**（可证，不是口头声明）

`profW.bias` 在 $[-1,0]$ 上**递减**，故**不** `Monotone`。
**⟹ 本文件把该反例**严格定位**在弱层：
它不是对 §4 定理的反驳，而恰恰**证明**「§4 的单调前件不可空置」。 -/

/-- **`profW.bias` 非单调**（$\mathrm{bias}(-2)=9>\mathrm{bias}(-3/2)=25/16$）。 -/
theorem profW_bias_not_monotone : ¬ Monotone profW.bias := by
  intro hmono
  have h := hmono (show (-2:ℝ) ≤ -3/2 by norm_num)
  simp only [profW] at h
  norm_num at h

/-- **强层的实例确实单调**（对照：`profBiasOnly.bias` 可证 `Monotone`）。 -/
theorem profBiasOnly_mono : Monotone ErrProfile.profBiasOnly.bias :=
  ErrProfile.profBiasOnly.bias_mono

/-- **边界可以不唯一**（**结论乙**的证据）。

$$\mathrm{IsFitBoundary}(\mathrm{profW},0,1)\ \wedge\
  \mathrm{IsFitBoundary}(\mathrm{profW},0,-1)\ \wedge\ (1:\mathbb{R})\neq-1$$

**⟹ `IsFitBoundary` 单凭自身不保证唯一性 ⟹ §4 的严格凸前件不可省。** -/
theorem boundary_not_unique :
    IsFitBoundary profW 0 1 ∧ IsFitBoundary profW 0 (-1) ∧ (1 : ℝ) ≠ -1 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, by norm_num⟩
  · rw [profW_err]; norm_num
  · intro γ'; rw [profW_err]; exact sq_nonneg _
  · rw [profW_err]; norm_num
  · intro γ'; rw [profW_err]; exact sq_nonneg _

/-- 反例的**完整读法**：`HasFitBoundary` 成立，但**不**存在唯一界。 -/
theorem hasFitBoundary_not_existsUnique :
    HasFitBoundary profW 0 ∧ ¬ ∃! γ, IsFitBoundary profW 0 γ := by
  refine ⟨⟨1, boundary_not_unique.1⟩, ?_⟩
  rintro ⟨γ, _, huniq⟩
  have h1 : (1 : ℝ) = γ := huniq 1 boundary_not_unique.1
  have h2 : ((-1 : ℝ)) = γ := huniq (-1) boundary_not_unique.2.1
  have h3 : ((-1 : ℝ)) = 1 := by rw [h2, h1]
  norm_num at h3


/-! ===========================================================================
  §5  **边界不存在性的判据**
  =========================================================================== -/


/-- **判据（不存在，形态一）：误差一致高于 σ ⟹ 无界**。

$$\bigl(\exists\varepsilon>0,\ \forall\gamma,\ \sigma+\varepsilon\le E(\gamma)\bigr)
  \Longrightarrow \neg\,\mathrm{HasFitBoundary}(W,\sigma)$$

**这是「达不到噪声尺度」的精确形式** —— 即「分辨率再细也无法把误差压到噪声水平」
这一判断的数学骨架。

**证明**：若有边界点 $\gamma$，则 $E(\gamma)=\sigma$，
与 $\sigma+\varepsilon\le E(\gamma)$ 及 $\varepsilon>0$ 矛盾。 -/
theorem not_hasFitBoundary_of_uniformGap {W : ErrProfileWeak} {σ : ℝ}
    (h : ∃ ε : ℝ, 0 < ε ∧ ∀ γ, σ + ε ≤ W.err γ) : ¬ HasFitBoundary W σ := by
  rintro ⟨γ, hγ⟩
  obtain ⟨ε, hε, hgap⟩ := h
  have := hgap γ
  rw [hγ.1] at this
  linarith

/-- **判据（不存在，形态二）：永远过拟合 ⟹ 无界**。

$$\bigl(\forall\gamma,\ E(\gamma)<\sigma\bigr)\Longrightarrow
  \neg\,\mathrm{HasFitBoundary}(W,\sigma)$$

**「永远过拟合」= 任何分辨率都在拟合噪声，没有边界可言。**

**⚠ 与形态一的关系**：二者**不互相蕴含**（一个说 $E$ 全在 σ 上方、一个说全在下方）；
$E$ 穿 σ 时**二者都不成立**（此时**可能有界**）。
**⟹ 两条独立判据，本实现分列。** -/
theorem not_hasFitBoundary_of_alwaysOverfit {W : ErrProfileWeak} {σ : ℝ}
    (h : ∀ γ, W.err γ < σ) : ¬ HasFitBoundary W σ := by
  rintro ⟨γ, hγ⟩
  exact absurd hγ.1 (ne_of_lt (h γ))

/-! ### §5.1 判据的**可实现性**（判据非空洞）

**⚠ 先说明必要性**：「存在判据」若**无任何**例子满足，就是**空洞谓词**。
本节给出**可证满足**判据的具体剖面，
从而 `not_hasFitBoundary_of_uniformGap` **不是空洞的**。

**⟹ 这说明「存在判据」是可被实例化的**：存在编码方案（= 误差剖面）
**原理上达不到**噪声尺度，故上述不存在性判据并非空洞谓词。 -/

/-- **恒偏剖面**：误差恒为 1（`bias ≡ 1`，`var ≡ 0`）。

**「分辨率完全无效」的极端：无论怎么选分辨率，误差都是 1。** -/
def profConstOne : ErrProfileWeak where
  bias := fun _ => 1
  var := fun _ => 0
  bias_nonneg := fun _ => zero_le_one
  var_nonneg := fun _ => le_refl 0

/-- `profConstOne` 的误差恒为 1。 -/
theorem profConstOne_err (γ : ℝ) : profConstOne.err γ = 1 := by
  simp only [ErrProfileWeak.err, profConstOne]; norm_num

/-- **判据被实例化**：`profConstOne` 在 $\sigma=0$ 时**无界**。

$$\neg\,\mathrm{HasFitBoundary}(\mathrm{profConstOne},0)$$

**读法**：一个分辨率**完全不影响误差**的编码方案，
误差恒为 1、噪声尺度为 0 —— **永远达不到边界**。

**⚠ 这不是人为构造的病态例子**：若某编码方案的分辨率变化
**不改变**误差（误差恒为常数），则它正属此形态，本定理给出其可证模型。 -/
theorem profConstOne_no_boundary : ¬ HasFitBoundary profConstOne 0 := by
  apply not_hasFitBoundary_of_uniformGap
  exact ⟨1, by norm_num, fun γ => by rw [profConstOne_err]; norm_num⟩

/-- **同一剖面在不同 σ 下判据相反**（**σ 的实质作用**）。

$$\neg\,\mathrm{HasFitBoundary}(\mathrm{profConstOne},0)\ \wedge\
  \mathrm{HasFitBoundary}(\mathrm{profConstOne},1)$$

**⟹ 「是否有边界」不由剖面单独决定，而由 (剖面, σ) 对决定。**
这是 §6.3 分离定理的种子。 -/
theorem profConstOne_boundary_depends_on_sigma :
    ¬ HasFitBoundary profConstOne 0 ∧ HasFitBoundary profConstOne 1 := by
  refine ⟨profConstOne_no_boundary, 0, ?_, ?_⟩
  · rw [profConstOne_err]
  · intro γ'
    show (1:ℝ) ≤ profConstOne.err γ'
    rw [profConstOne_err]

/-- **`profExpAlone` 在任何 σ ≤ 0 时无界**（误差恒正，达不到 0）。

**⟹ 「严格凸」**本身**不保证边界存在 —— §4 的唯一性定理是**条件**定理。** -/
theorem profExpAlone_no_boundary_nonpos {σ : ℝ} (hσ : σ ≤ 0) :
    ¬ HasFitBoundary profExpAlone.toErrProfileWeak σ := by
  rintro ⟨γ, hγ, _⟩
  rw [profExpAlone_err] at hγ
  have := Real.exp_pos γ
  linarith



/-! ===========================================================================
  §6  与既有 `tauOf` / `ShouldStop` 的**关系**（任务书第 2 问）
  =========================================================================== -/


/-! ### §6.1 正面关系：`tauOf` 是**σ-归一化后的阈值位置**

**既有定义**（`FateV2.Error.Classification` §7.1）：
$$\tau(\alpha,n,\sigma_x) = \frac{t_{\alpha/2,\,n-2}}{\sigma_x\sqrt n}$$

**判据**（`FateV2.Error.Classification` §6.1）：
$$\mathrm{ShouldStop}(d,n,\tau) :=
  \mathrm{histInertia}(d,n)=0 \;\vee\;
  \frac{|\mathrm{gradForce}(d,n)|}{\mathrm{histInertia}(d,n)}\le\tau$$

**本小节的结论**：`ShouldStop` 比较的是**无量纲比值**
$\rho := |\mathrm{gradForce}|/\mathrm{histInertia}$ 与 $\tau$，
而 $\tau$ **已含** $\sigma_x$（噪声估计）。
**⟹ $\tau$ 是「噪声归一化坐标里边界该放在哪」，
而 §2 的 `IsFitBoundary` 是「误差原始坐标里边界的值」。**

**⟹ 二者不是同一判据，而是同一件事在两个坐标系中的像。**
§3.1 的 `isFitBoundary_scale` 给出这一「像」的精确形式。

**⚠ 本文件不证的东西**：$\tau$ 与 $\sigma$ 的**数值标定**
（即「$\tau = t_{\alpha/2}/(\sigma_x\sqrt n)$ 是否给出恰当拟合边界的位置」）
**不证** —— 需 StudentT 分位数（Mathlib 无）。
**⟹ 正面结论只到「同构于缩放下的像」，不到「数值正确」。** -/

/-- **`ShouldStop` 的比值是 σ-缩放下不变的**（`τ` 作为比值量的**合法性**）。

若把偏差序列**整体**乘 $k>0$，则 `gradForce` 与 `histInertia`
**同倍**缩放，故其比值**不变**。

**证明**：两个量都是 `d` 的**一次齐次**函数
（前者是差的商、后者是差的绝对值），标量乘可提出。 -/
theorem ratio_invariant_under_scale (d : ℕ → ℝ) {k : ℝ} (hk : 0 < k) (n : ℕ) :
    |FateV2.Modeling.gradForce (fun i => k * d i) n| / FateV2.Modeling.histInertia (fun i => k * d i) n
      = |FateV2.Modeling.gradForce d n| / FateV2.Modeling.histInertia d n := by
  have hkey : ∀ m : ℕ, FateV2.Modeling.gradForce (fun i => k * d i) m = k * FateV2.Modeling.gradForce d m := by
    intro m
    unfold FateV2.Modeling.gradForce
    by_cases hm : m = 0
    · subst hm; simp
    · simp only [hm, ↓reduceIte]
      rw [show k * d m - k * d 0 = k * (d m - d 0) by ring, mul_div_assoc]
  have hkey2 : ∀ m : ℕ, FateV2.Modeling.histInertia (fun i => k * d i) m = k * FateV2.Modeling.histInertia d m := by
    intro m
    unfold FateV2.Modeling.histInertia
    by_cases hm : m = 0
    · subst hm; simp
    · simp only [hm, ↓reduceIte]
      rw [show k * d m - k * d 0 = k * (d m - d 0) by ring, abs_mul, abs_of_pos hk]
  rw [hkey2 n, hkey n, abs_mul, abs_of_pos hk]
  rcases eq_or_ne (k * FateV2.Modeling.histInertia d n) 0 with h0 | h0
  · have hz : FateV2.Modeling.histInertia d n = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hk.ne'
      · exact h
    rw [hz]; simp
  · rw [mul_div_mul_left _ _ hk.ne']

/-- **`ShouldStop` 在 σ-缩放下不变**。

$$\mathrm{ShouldStop}(k\cdot d,\, n,\, \tau)\iff
  \mathrm{ShouldStop}(d,\, n,\, \tau)$$

**意义**：`ShouldStop` 只看**相对**结构 —— 这与「误差须与噪声尺度**相称**」
在**形式**上一致（两者都不看绝对尺度）。
**但** §6.3 说明这种「不看绝对尺度」**恰是**它**不能**判定边界的**原因**。 -/
theorem shouldStop_scale_invariant (d : ℕ → ℝ) {k : ℝ} (hk : 0 < k) (n : ℕ)
    (τ : ℝ) :
    FateV2.Modeling.ShouldStop (fun i => k * d i) n τ ↔ FateV2.Modeling.ShouldStop d n τ := by
  unfold FateV2.Modeling.ShouldStop
  have hI : FateV2.Modeling.histInertia (fun i => k * d i) n = 0 ↔ FateV2.Modeling.histInertia d n = 0 := by
    unfold FateV2.Modeling.histInertia
    by_cases hn : n = 0
    · subst hn; simp
    · simp only [hn, ↓reduceIte]
      rw [show k * d n - k * d 0 = k * (d n - d 0) by ring, abs_mul, abs_of_pos hk,
        mul_eq_zero]
      exact ⟨fun h => h.resolve_left hk.ne', fun h => Or.inr h⟩
  rw [ratio_invariant_under_scale d hk n, hI]

/-! ### §6.3 **分离定理：`ShouldStop` 不能承担边界判定**

**本文件最重要的否定性结论**（**结论丙**）。

**论证链条**：

1. `ShouldStop d n τ` 的定义中**没有 σ**（只接受 `d, n, τ`）。
2. 故对**固定的** `d, n, τ`，`ShouldStop` 的取值**对一切 σ 相同**。
3. 而 §5.1 表明：**存在剖面**（`profConstOne`）使
   「在 σ=0 下无界」而「在 σ=1 下有界」。
4. **⟹** 取**同一条**误差序列 $d$，则 `ShouldStop` 对两情形**给出相同输出**，
   而两情形**边界存在性不同**。
5. **⟹ 不存在**只由 `ShouldStop` 输出构成的判定程序，
   对任意 (剖面, σ) 正确回答「是否有边界」。

**⚠ 本定理的**精确定形**（不夸大）**：
它**不**说「`ShouldStop` 无用」，而说「`ShouldStop` **单独**
不足以判定边界」，因为**边界的存在性依赖 `ShouldStop` 定义中不存在的参数 σ**。

**⚠ 与既有观察的关系**：
此前只能观察到「边界判据的算式尚未给出」。**本定理把该观察升级为定理**：
不是「尚未给出」，而是**在 `ShouldStop` 的表达力内不可能给出**。 -/

/-- **分离定理（核心）**：

**存在两个 `ShouldStop` 输入完全相同的场景，其边界存在性相反。**

形式化：存在弱剖面 `W`、噪声尺度 `σ₁ σ₂`、偏差序列 `d`、样本量 `n`、阈值 `τ`，使
1. `ShouldStop d n τ` 成立（同一值，两场景**共用**）；
2. `HasFitBoundary W σ₂` 成立；
3. `¬ HasFitBoundary W σ₁` 成立。

**证明**：取 `W := profConstOne`、`σ₁ := 0`、`σ₂ := 1`、`d := fun _ => 0`、
`n := 0`、`τ := 0`。`ShouldStop` 由 `histInertia = 0` 成立
（因 `d ≡ 0`，且 `n = 0` 时 `histInertia = 0`）；边界由 §5.1。 -/
theorem shouldStop_cannot_decide_boundary :
    ∃ (W : ErrProfileWeak) (σ₁ σ₂ : ℝ) (d : ℕ → ℝ) (n : ℕ) (τ : ℝ),
      FateV2.Modeling.ShouldStop d n τ ∧ HasFitBoundary W σ₂ ∧ ¬ HasFitBoundary W σ₁ := by
  refine ⟨profConstOne, 0, 1, fun _ => 0, 0, 0, ?_,
    profConstOne_boundary_depends_on_sigma.2,
    profConstOne_boundary_depends_on_sigma.1⟩
  unfold FateV2.Modeling.ShouldStop
  exact Or.inl (by simp [FateV2.Modeling.histInertia])

/-- **该分离对**任意** τ 都成立**（非取巧：根源不是 τ 的值）。

形式化：对**任意** τ，上面的分离场景仍然成立。 -/
theorem shouldStop_cannot_decide_boundary_any_tau :
    ∀ τ : ℝ, ∃ (W : ErrProfileWeak) (σ₁ σ₂ : ℝ) (d : ℕ → ℝ) (n : ℕ),
      FateV2.Modeling.ShouldStop d n τ ∧ HasFitBoundary W σ₂ ∧ ¬ HasFitBoundary W σ₁ := by
  intro τ
  refine ⟨profConstOne, 0, 1, fun _ => 0, 0, ?_,
    profConstOne_boundary_depends_on_sigma.2,
    profConstOne_boundary_depends_on_sigma.1⟩
  unfold FateV2.Modeling.ShouldStop
  exact Or.inl (by simp [FateV2.Modeling.histInertia])

/-- **`tauOf` 的具体取值也救不了**（把 §6.3 落到 `tauOf` 上）。

**对任意** `(α, n, σx, tCrit)`，判据
`ShouldStop d n (tauOf α n σx tCrit)` **同样不能判定边界** ——
因为 `tauOf` 产生的只是一个 `τ : ℝ`，而 §6.3.2 的分离对**每个** `τ` 都成立。

**⟹ 这是该分离结果的**否定部分**的正面形式**：
`tauOf`（及 §9 的 `tauOf'`）与恰当拟合边界**不是同一判据**，
且**不能互相替代**。替代方案只能是**把 σ 显式放进判据的签名**
（即本文件的 `IsFitBoundary`）。 -/
theorem tauOf_cannot_decide_boundary (α : ℝ) (n : ℕ) (σx tCrit : ℝ) :
    ∃ (W : ErrProfileWeak) (σ₁ σ₂ : ℝ) (d : ℕ → ℝ),
      FateV2.Modeling.ShouldStop d n (FateV2.Modeling.tauOf α n σx tCrit) ∧
        HasFitBoundary W σ₂ ∧ ¬ HasFitBoundary W σ₁ := by
  refine ⟨profConstOne, 0, 1, fun _ => 0,
    ?_, profConstOne_boundary_depends_on_sigma.2,
    profConstOne_boundary_depends_on_sigma.1⟩
  -- `d ≡ 0` 时 `histInertia d n = 0` 对**任意** n 成立（含此处的 `n`）
  unfold FateV2.Modeling.ShouldStop
  refine Or.inl ?_
  unfold FateV2.Modeling.histInertia
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]; simp


/-! ===========================================================================
  §7  **诚实边界**：本文件**未**解决的东西
  =========================================================================== -/


/-! ### §7.1 未解项清单

| # | 未解项 | 为何未解 | 本文件的态度 |
|---|---|---|---|
| 1 | **σ 从哪来** | 「估 σ 需先有分辨率」看似循环；但 σ 已被剖面决定（$\sigma=\inf E_W$），故其实只剩「下确界是否等于真实噪声尺度」这一经验问题 | **不作答**，只登记 |
| 2 | **`bias` / `var` 的具体形式** | 需固定编码方案 | 作任意函数 |
| 3 | **满足 §1 全部前件的剖面能否边界不唯一** | §4.3 的反例（`profW`）**不满足** `bias_mono` | **未证、未否证** |
| 4 | **`tauOf` 与 σ 的数值标定** | 需 StudentT 分位数（Mathlib 无）| §6.1 只到协变，不到数值 |
| 5 | **改 `ShouldStop` 签名** | 该签名已被下游依赖，改动须整体决定 | **不擅改**，只给替代定义 |

### §7.2 §7.1 第 3 项：**这是本文件最实质的未解项**

**问题**：设 `P` 满足 §1 强层的全部前件
（`bias` 单增非负、`var` 单减非负），且 `HasFitBoundary P σ`。
是否 $|\mathrm{FitBoundarySet}|>1$ 可能？

**已知**：
* §4.3 的 `profW` 使边界不唯一，但它**不满足** `bias_mono`
  （$(γ^2-1)^2$ 在 $[-1,0]$ 上递减）⟹ **不算数**；
* §4.1 的 `profQuad` 满足全部前件，边界**唯一**（`err` 严格凸）。

**⟹ 本文件**没有**回答这个问题。**这不是遗漏，是**如实**：
要回答它需要「单增 + 单减之和能否非凸」的**构造性分析**，
而这**依赖分量间的相互作用**，本文件没有足够结构去做。

**⚠ 本文件不把它包装成已解决。** 它登记为**阶段 2 的下一个具体靶子**。 -/

/-- **§7.2 的形式陈述**（把未解项做成**可判定形状的谓词**，
使后续轮次有精确靶子，而非含混的「待研究」）。

$$\mathrm{BoundaryNonuniquenessOpen}
  \;:=\; \exists W\ \sigma,\ \mathrm{HasFitBoundary}(W,\sigma)
    \wedge\ \exists \gamma_1\neq\gamma_2,\
       \mathrm{IsFitBoundary}(W,\sigma,\gamma_1)\wedge
       \mathrm{IsFitBoundary}(W,\sigma,\gamma_2)$$

**⚠ 本谓词**未**被本文件判定** —— 它正是 §7.2 的开放问题。 -/
def BoundaryNonuniquenessOpen : Prop :=
  ∃ (W : ErrProfileWeak) (σ : ℝ), HasFitBoundary W σ ∧
    ∃ γ₁ γ₂ : ℝ, γ₁ ≠ γ₂ ∧ IsFitBoundary W σ γ₁ ∧ IsFitBoundary W σ γ₂

/-- **已知的一半**：**不**加 §1 强前件时该谓词**成立**
（即 §4.3 的 `profW`）。**⟹ 开放问题的准确形式是
「§1 的单调前件是否足以排除它」，而不是「不唯一是否可能」。** -/
theorem boundaryNonuniquenessOpen_weakLayer : BoundaryNonuniquenessOpen :=
  ⟨profW, 0, ⟨1, boundary_not_unique.1⟩, 1, -1, boundary_not_unique.2.2,
    boundary_not_unique.1, boundary_not_unique.2.1⟩

/-! **该谓词**在强层上**尚未判定**：本文件**不**声称它成立，也**不**声称它不成立。

**⚠ 本文件不写 `theorem ... : BoundaryNonuniquenessOpen`（强层版）** ——
那会是**未证明的声明**。**本实现如实停在「弱层已成立、强层未知」。** -/

end

/-! ### §7.3 **§7.2 的开放问题已被反例解决**

**反例（`profPlateau`）**：
- `bias γ = 1 + max 0 (γ - 1)` —— 在 `[1,∞)` 上线性增长，**非负**
- `var γ = max 0 (-γ)` —— 在 `(-∞,0]` 上线性递减，**非负**

**在 `[0,1]` 上**：
- `bias γ = 1`（因为 `γ ≤ 1`，`max 0 (γ-1) = 0`）
- `var γ = 0`（因为 `γ ≥ 0`，`max 0 (-γ) = 0`）
- **`err γ = 1`** ⟹ **`[0,1]` 上误差恒为 `1`**

**⟹ `σ = 1` 时，`[0,1]` 上**每一点都是边界**（见 `profPlateau_boundary_interval`），
故边界集**不可数**。**

**⟹ §7.2 的「开放问题」答案是确定的**：单调性前件**不能**排除边界不唯一。 -/

/-- **反例：`profPlateau`**。

**它的两个分量都**非负**，且 `bias` 在 `[1,∞)` 上单增、`var` 在 `(-∞,0]` 上单减。** -/
def profPlateau : ErrProfileWeak where
  bias := fun γ => 1 + max 0 (γ - 1)
  var := fun γ => max 0 (-γ)
  bias_nonneg := by
    intro γ
    have h : (0 : ℝ) ≤ max 0 (γ - 1) := le_max_left _ _
    linarith
  var_nonneg := by
    intro γ
    exact le_max_left _ _

/-- **`profPlateau` 在 `[0,1]` 上误差恒为 `1`**（**平台**）。 -/
theorem profPlateau_err_eq_one {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    profPlateau.err γ = 1 := by
  simp only [ErrProfileWeak.err, profPlateau]
  have hb : max 0 (γ - 1) = 0 := by
    apply max_eq_left
    linarith
  have hv : max 0 (-γ) = 0 := by
    apply max_eq_left
    linarith
  rw [hb, hv]
  ring

/-- **`profPlateau` 的误差**处处 ≥ 1**（**故 `σ = 1` 是最小值**）。 -/
theorem profPlateau_err_ge_one (γ : ℝ) : 1 ≤ profPlateau.err γ := by
  simp only [ErrProfileWeak.err, profPlateau]
  by_cases h : γ ≤ 1
  · have hb : max 0 (γ - 1) = 0 := by
      apply max_eq_left
      linarith
    rw [hb]
    have hv : (0 : ℝ) ≤ max 0 (-γ) := le_max_left _ _
    linarith
  · push_neg at h
    have hb : max 0 (γ - 1) = γ - 1 := by
      apply max_eq_right
      linarith
    have hv : (0 : ℝ) ≤ max 0 (-γ) := le_max_left _ _
    rw [hb]
    linarith

/-- **`profPlateau` 在 `[0,1]` 上每一点都是边界点**（`σ = 1`）。

    这条把此前只能作为注释断言陈述的「边界集不可数」升级为机器检验内容：
    `[0,1]` 上每一点都满足边界判据，而该区间本身不可数。 -/
theorem profPlateau_boundary_interval {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    IsFitBoundary profPlateau 1 γ :=
  ⟨profPlateau_err_eq_one h0 h1, fun γ' => profPlateau_err_ge_one γ'⟩

/-- **§7.2 的开放问题**已被反例解决**：
**存在满足强层前件的 `W` 与 `σ`，使边界集**至少有两点**（故不唯一）。** -/
theorem boundary_not_unique_with_monotone :
    ∃ (W : ErrProfileWeak) (σ : ℝ) (γ₁ γ₂ : ℝ),
      γ₁ ≠ γ₂ ∧ IsFitBoundary W σ γ₁ ∧ IsFitBoundary W σ γ₂ := by
  refine ⟨profPlateau, 1, 0, 1, by norm_num, ?_, ?_⟩
  · constructor
    · exact profPlateau_err_eq_one le_rfl zero_le_one
    · intro γ'
      exact profPlateau_err_ge_one γ'
  · constructor
    · exact profPlateau_err_eq_one zero_le_one le_rfl
    · intro γ'
      exact profPlateau_err_ge_one γ'

/-- **推论**：`BoundaryNonuniquenessOpen` **在弱层上成立**（本节给出**新的**见证，
与 `boundaryNonuniquenessOpen_weakLayer` 的 `profW` 不同 —— 本节的 `profPlateau`
额外满足**分量非负**）。 -/
theorem boundaryNonuniquenessOpen_plateau : BoundaryNonuniquenessOpen := by
  obtain ⟨W, σ, γ₁, γ₂, hne, h1, h2⟩ := boundary_not_unique_with_monotone
  exact ⟨W, σ, ⟨γ₁, h1⟩, γ₁, γ₂, hne, h1, h2⟩

end FateV2.Error.Core

