import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import FateWorld.Legacy.LawRule

/-! ===========================================================================
  §Stat  α 的**统计版本**：用实例的经验分布构造 α（经验条件核 + 置信带）

  ## 定位

  `Fate.LawRule` 把规则钉成**约束集**
  $\text{Rule}(c,x)\subseteq\mathcal{P}(\mathcal{M}(Y))$，并给出单点档判据
  `LawRule.IsPoint`。`Fate.Alpha` 把 α 具体化为 FCA 取概念过程（裁决 D）。
  本文件给出 α 的**第三种读法**：**从样本出发的经验 α**（频率层）。

  | | α 是什么 | 输入 | α 的像 |
  |---|---|---|
  | `Fate.Alpha.takeConcept` | 形式背景上的闭包 | 属性集 | 闭集 |
  | `Fate.AlphaKernel.alphaKernel` | α 的核（Q-3） | 实例对 | 等价类 |
  | **本文件 `StatRule`** | **经验条件核 + 置信带** | **样本** | **带宽度的频率集** |

  ## 构造（三段式）

  1. **经验条件核**：
     $\hat p_{c,x}(y)=N_{c,x,y}/N_{c,x}$，
     $N_{c,x}=\#\{w: w.1=c\wedge w.2.1=x\}$，$N_{c,x,y}=\#\{w:w.1=c\wedge w.2.1=x\wedge w.2.2=y\}$。
  2. **置信带**（半径 $r(c,x)\ge0$）：
     $$\mathrm{Band}_{c,x}=\{f:Y\to\mathbb R\mid\textstyle\sum_y f=1,\ 0\le f,\ \mathrm{TV}(f,\hat p_{c,x})\le r(c,x)\}.$$
  3. **α**：$\alpha_{\text{stat}}:=(c,x)\mapsto\mathrm{Band}_{c,x}$。

  $\mathrm{TV}(f,g)=\sum_y|f(y)-g(y)|$（**不去半**，见 `tv`）。

  ## ⭐ 主结果：**何时 `IsPoint`**

  > 层非空、$|Y|\ge2$ 时：$\mathrm{Band}_{c,x}$ 是**单点** $\iff$ $r(c,x)=0$。

  **⟸** `band_isPoint_of_zero_radius`（**前提 `layerCount D c x ≠ 0`**，
  见诚实边界 4：空层时球为空，故该前件**不可省**）；**⟹** `band_not_singleton_of_pos_radius`
  （用**移动质量** $f=\hat p+t(e_a-e_b)$，$0<t\le\min(r/2,\hat p_b)$，
  得 $f\ne\hat p$、$f\ge0$、$\sum f=1$、$\mathrm{TV}=2t\le r$）。

  **⟹ 结论**：α 可当**确定性世界模型**用 $\iff$
  **半径处处为零**（统计条件）**且每层纯**（数据条件）。
  两项**不可互推**（`isPoint_iff_all_zero_radius`、`diracRule_iff_zero_and_pure`）。

  ## 诚实边界

  1. **不填 $r$ 的统计公式**（DKW/Hoeffding/Bernstein…）。$r$ 是输入参数，
     其「覆盖真核」的概率断言属统计前提。填数即为虚构。
  2. **$Y$ 取有限型**（`[Fintype Y]`）；无穷 $Y$ 版须改 `Measure`，**未做**。
  3. **频率向量 $\ne$ `Measure`**：`LawRule` 的元素是 `Measure Y`，
     本文件是 $Y\to\mathbb R$。桥 `freqToMeasure` 的**单射性未证**，
     故 `IsPointFreq` 与 `LawRule.IsPoint` 的等价是**登记缺口**。
  4. **空层**：`empFreq` 取 $0$，此时球不含概率向量，故 `band_nonempty` 带非空层前件。
     **⚠ 2026-P1 修复记录**：`band_isPoint_of_zero_radius` 原陈述**漏了该前件**
     （`StatRule = ∅` 而 `{empFreq} = {0}`，命题**为假**）。已补 `layerCount D c x ≠ 0`，
     并沿调用链同步补前件于 `isPoint_of_all_zero_radius` / `zero_radius_and_back` /
     `pure_and_zero_gives_dirac`（及其 `diracRule_iff_zero_and_pure` 内部调用）。
     修复后**零 error / 零 sorry**（本文件无 `sorry`/`admit`/`axiom`）。
  =========================================================================== -/

namespace Fate

namespace StatAlpha

open Finset

variable {C X Y : Type*} [DecidableEq C] [DecidableEq X] [DecidableEq Y] [Fintype Y]

/-! ===========================================================================
    §1  样本与经验条件频率
    =========================================================================== -/

/-- **数据集**：有限个三元组 $(c,x,y)$。 -/
abbrev Data (C X Y : Type*) := Finset (C × X × Y)

/-- **层**：给定 $(c,x)$ 的样本集合。 -/
def layerSet (D : Data C X Y) (c : C) (x : X) : Finset (C × X × Y) :=
  D.filter (fun w => w.1 = c ∧ w.2.1 = x)

/-- **层的大小** $N_{c,x}$。 -/
def layerCount (D : Data C X Y) (c : C) (x : X) : ℕ :=
  (layerSet D c x).card

/-- **层的输出计数** $N_{c,x,y}$。 -/
def outCount (D : Data C X Y) (c : C) (x : X) (y : Y) : ℕ :=
  (D.filter (fun w => w.1 = c ∧ w.2.1 = x ∧ w.2.2 = y)).card

/-- 输出计数与层内过滤一致。 -/
theorem outCount_eq_filter (D : Data C X Y) (c : C) (x : X) (y : Y) :
    outCount D c x y = ((layerSet D c x).filter (fun w => w.2.2 = y)).card := by
  unfold outCount layerSet
  rw [Finset.filter_filter]
  congr 1
  ext w; simp only [Finset.mem_filter]; tauto

/-- ⭐ **层可加性**：$N_{c,x}=\sum_y N_{c,x,y}$（层的样本被输出完全分光）。 -/
theorem layerCount_eq_sum_outCount (D : Data C X Y) (c : C) (x : X) :
    layerCount D c x = ∑ y : Y, outCount D c x y := by
  simp only [layerCount, outCount_eq_filter]
  rw [← Finset.card_eq_sum_card_fiberwise (t := (Finset.univ : Finset Y))
        (f := fun w : C × X × Y => w.2.2) (fun w _ => Finset.mem_univ _)]

/-! ===========================================================================
    §2  经验条件核
    =========================================================================== -/

/-- **经验条件频率** $\hat p_{c,x}(y)=N_{c,x,y}/N_{c,x}$（**空层取 $0$**，见诚实边界 4）。 -/
noncomputable def empFreq (D : Data C X Y) (c : C) (x : X) : Y → ℝ :=
  fun y => if layerCount D c x = 0 then 0
    else (outCount D c x y : ℝ) / (layerCount D c x : ℝ)

theorem empFreq_nonneg (D : Data C X Y) (c : C) (x : X) :
    ∀ y, 0 ≤ empFreq D c x y := by
  intro y
  unfold empFreq
  split_ifs with h
  · exact le_refl (0:ℝ)
  · positivity

/-- ⭐ **非空层上经验频率求和为 $1$**（**经验核确是一个概率分布**）。 -/
theorem empFreq_sum (D : Data C X Y) (c : C) (x : X)
    (h : layerCount D c x ≠ 0) : ∑ y, empFreq D c x y = 1 := by
  set N := layerCount D c x with hN
  have hsum : ∑ y : Y, empFreq D c x y = (∑ y : Y, (outCount D c x y : ℝ)) / (N : ℝ) := by
    have step : ∀ y : Y, empFreq D c x y
        = (outCount D c x y : ℝ) / (N : ℝ) := by
      intro y; unfold empFreq; rw [if_neg h]
    rw [Finset.sum_congr rfl (fun y _ => step y)]
    rw [Finset.sum_congr rfl (fun y _ => show (outCount D c x y : ℝ) / (N:ℝ)
      = (outCount D c x y : ℝ) * (N:ℝ)⁻¹ from div_eq_mul_inv _ _)]
    show (∑ y : Y, (outCount D c x y : ℝ) * (N:ℝ)⁻¹) = (∑ y : Y, (outCount D c x y : ℝ)) * (N:ℝ)⁻¹
    rw [Finset.sum_mul]
  rw [hsum]
  have hcast : (N : ℝ) = ∑ y : Y, (outCount D c x y : ℝ) := by
    rw [hN, layerCount_eq_sum_outCount]; push_cast; ring
  rw [hcast]
  have hz : (∑ y : Y, (outCount D c x y : ℝ)) ≠ 0 := by rw [← hcast]; exact_mod_cast h
  exact div_self hz

/-! ===========================================================================
    §3  有限总变差
    =========================================================================== -/

/-- **有限（不去半的）总变差** $\mathrm{TV}(f,g)=\sum_y|f(y)-g(y)|$。 -/
noncomputable def tv (f g : Y → ℝ) : ℝ := ∑ y, |f y - g y|

theorem tv_nonneg (f g : Y → ℝ) : 0 ≤ tv f g :=
  Finset.sum_nonneg (fun y _ => abs_nonneg _)

theorem tv_self (f : Y → ℝ) : tv f f = 0 := by
  unfold tv; simp

theorem tv_symm (f g : Y → ℝ) : tv f g = tv g f := by
  unfold tv
  exact Finset.sum_congr rfl (fun y _ => abs_sub_comm _ _)

theorem tv_triangle (f g h : Y → ℝ) : tv f h ≤ tv f g + tv g h := by
  unfold tv
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun y _ => by
    calc |f y - h y| = |(f y - g y) + (g y - h y)| := by ring_nf
      _ ≤ |f y - g y| + |g y - h y| := abs_add_le _ _)

/-- ⭐ **零距离刻画**：$\mathrm{TV}(f,g)=0\iff f=g$。 -/
theorem tv_eq_zero_iff (f g : Y → ℝ) : tv f g = 0 ↔ f = g := by
  constructor
  · intro ht
    funext y
    have hle : |f y - g y| ≤ tv f g := by
      unfold tv
      exact Finset.single_le_sum (f := fun y => |f y - g y|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ y)
    have hz : |f y - g y| = 0 := le_antisymm (by linarith) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  · rintro rfl; exact tv_self f

/-! ===========================================================================
    §4  ⭐ α 的统计版本
    =========================================================================== -/

/-- **置信半径**：$r(c,x)\ge0$。`nonneg` **类型层强制**非负——否则球可能不含经验核。 -/
structure Radius (C X : Type*) where
  r : C → X → ℝ
  nonneg : ∀ c x, 0 ≤ r c x

/-- ⭐ **α 的统计版本**：每层给出经验条件核的**置信带**。 -/
noncomputable def StatRule (D : Data C X Y) (ρ : Radius C X) (c : C) (x : X) :
    Set (Y → ℝ) :=
  { f | (∑ y, f y = 1) ∧ (∀ y, 0 ≤ f y) ∧ tv f (empFreq D c x) ≤ ρ.r c x }

/-- ⭐ **经验核落在自己的带宽球里**（⟹ α 的像不含矛盾规则）。 -/
theorem empFreq_mem_band (D : Data C X Y) (ρ : Radius C X) (c : C) (x : X)
    (h : layerCount D c x ≠ 0) : empFreq D c x ∈ StatRule D ρ c x :=
  ⟨empFreq_sum D c x h, empFreq_nonneg D c x, by
    rw [tv_self]; exact ρ.nonneg c x⟩

/-- ⭐⭐ **带宽球非空**（非空层时）。 -/
theorem band_nonempty (D : Data C X Y) (ρ : Radius C X) (c : C) (x : X)
    (h : layerCount D c x ≠ 0) : (StatRule D ρ c x).Nonempty :=
  ⟨empFreq D c x, empFreq_mem_band D ρ c x h⟩

/-- ⭐⭐ **零半径 ⟹ 带宽球是单点 $\{\hat p\}$**。 -/
theorem band_isPoint_of_zero_radius (D : Data C X Y) (ρ : Radius C X) (c : C) (x : X)
    (hN : layerCount D c x ≠ 0) (hρ : ρ.r c x = 0) : StatRule D ρ c x = {empFreq D c x} := by
  ext f
  simp only [StatRule, Set.mem_setOf_eq, Set.mem_singleton_iff, hρ]
  constructor
  · rintro ⟨_, _, h3⟩
    exact (tv_eq_zero_iff f (empFreq D c x)).mp (le_antisymm h3 (tv_nonneg _ _))
  · intro hf
    subst hf
    exact ⟨empFreq_sum D c x hN, empFreq_nonneg D c x,
      by rw [tv_self]⟩

/-! ### §4.1  技术核心：**正半径 ⟹ 球不止一点** -/

/-- **移动质量算子** $f=\hat p+t(e_a-e_b)$。 -/
noncomputable def shift (p : Y → ℝ) (a b : Y) (t : ℝ) : Y → ℝ :=
  fun y => p y + t * ((if y = a then 1 else 0) - (if y = b then 1 else 0))

theorem shift_sum (p : Y → ℝ) (a b : Y) (t : ℝ) (h : ∑ y, p y = 1) :
    ∑ y, shift p a b t y = 1 := by
  unfold shift
  rw [Finset.sum_add_distrib, h]
  have hsplit : ∀ y, t * ((if y = a then (1:ℝ) else 0) - (if y = b then (1:ℝ) else 0))
      = t * (if y = a then (1:ℝ) else 0) - t * (if y = b then (1:ℝ) else 0) := by
    intro y; ring
  rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_sub_distrib]
  simp

theorem shift_nonneg (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y) {a b : Y} (hab : a ≠ b)
    {t : ℝ} (ht : 0 ≤ t) (hba : t ≤ p b) : ∀ y, 0 ≤ shift p a b t y := by
  intro y
  unfold shift
  rcases eq_or_ne y a with hya | hya
  · rw [if_pos hya, if_neg (by subst hya; exact hab)]
    rw [show t * (1 - 0) = t by ring]; linarith [hp y]
  · rcases eq_or_ne y b with hyb | hyb
    · rw [if_neg hya, if_pos hyb, show t * (0 - 1) = -t by ring]; subst hyb; linarith
    · rw [if_neg hya, if_neg hyb, sub_self, mul_zero, add_zero]; exact hp y

theorem tv_shift (p : Y → ℝ) {a b : Y} (hab : a ≠ b) (t : ℝ) (ht : 0 ≤ t) :
    tv (shift p a b t) p = 2 * t := by
  unfold tv shift
  have h1 : ∀ y : Y,
      |p y + t * ((if y = a then (1:ℝ) else 0) - (if y = b then (1:ℝ) else 0)) - p y|
      = |t * ((if y = a then (1:ℝ) else 0) - (if y = b then (1:ℝ) else 0))| := by
    intro y; congr 1; ring
  rw [Finset.sum_congr rfl (fun y _ => h1 y)]
  have key : ∀ y : Y,
      |t * ((if y = a then (1:ℝ) else 0) - (if y = b then (1:ℝ) else 0))|
      = (if y = a then t else 0) + (if y = b then t else 0) := by
    intro y
    rcases eq_or_ne y a with hya | hya
    · subst hya
      rw [if_pos rfl, if_neg hab, show t * (1 - 0) = t by ring, abs_of_nonneg ht,
        if_pos rfl, if_neg hab]
      ring
    · rcases eq_or_ne y b with hyb | hyb
      · subst hyb
        rw [if_neg hya, if_pos rfl, show t * (0 - 1) = -t by ring, abs_neg,
          abs_of_nonneg ht, if_neg hya, if_pos rfl]
        ring
      · rw [if_neg hya, if_neg hyb, sub_self, mul_zero, abs_zero,
          if_neg hya, if_neg hyb, add_zero]
  rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']
  ring

theorem shift_ne (p : Y → ℝ) {a b : Y} (hab : a ≠ b) {t : ℝ} (ht : 0 < t) :
    shift p a b t ≠ p := by
  intro h
  have := congrFun h a
  unfold shift at this
  rw [if_pos rfl, if_neg hab] at this
  have hz : t * (1 - 0) = 0 := by linarith
  linarith

/-- **存在正质量坐标**（$Y$ 非空、$p$ 归一）。 -/
theorem exists_pos_of_sum_one [Nonempty Y] (p : Y → ℝ) (h : ∑ y, p y = 1) :
    ∃ b, 0 < p b := by
  by_contra hc
  push Not at hc
  have : ∑ y, p y ≤ 0 := Finset.sum_nonpos (fun y _ => hc y)
  linarith

/-- ⭐⭐ **正半径 ⟹ 带宽球至少两点**（层非空、$|Y|\ge2$）。

**构造**：正质量坐标 $b$、另一点 $a\ne b$，$t:=\min(r/2,\hat p_b)>0$。
则 $2t\le r$（故 $\mathrm{TV}=2t\le r$）且 $t\le\hat p_b$（故 $f\ge0$），
$f\ne\hat p$。两点 $\hat p$、$f$ 都在球内。 -/
theorem band_not_singleton_of_pos_radius [Nonempty Y]
    (D : Data C X Y) (ρ : Radius C X) (c : C) (x : X)
    (hY : ∃ a b : Y, a ≠ b)
    (hsum : ∑ y, empFreq D c x y = 1)
    (hpos : 0 < ρ.r c x) :
    ∃ f₁ f₂ : Y → ℝ, f₁ ≠ f₂ ∧ f₁ ∈ StatRule D ρ c x ∧ f₂ ∈ StatRule D ρ c x := by
  set p := empFreq D c x with hp
  obtain ⟨b, hb⟩ := exists_pos_of_sum_one p hsum
  obtain ⟨a, b', hab'⟩ := hY
  obtain ⟨a', ha'b⟩ : ∃ a' : Y, a' ≠ b := by
    by_cases hab : a = b
    · exact ⟨b', by subst hab; exact hab'.symm⟩
    · exact ⟨a, hab⟩
  set t : ℝ := min (ρ.r c x / 2) (p b) with ht
  have ht_pos : 0 < t := lt_min (by linarith) hb
  have ht_le_r : 2 * t ≤ ρ.r c x := by
    have := min_le_left (ρ.r c x / 2) (p b); linarith
  have ht_le_pb : t ≤ p b := min_le_right _ _
  refine ⟨p, shift p a' b t, (shift_ne p ha'b ht_pos).symm, ?_, ?_⟩
  · exact ⟨hsum, empFreq_nonneg D c x, by rw [tv_self]; exact ρ.nonneg c x⟩
  · exact ⟨shift_sum p a' b t hsum, shift_nonneg p (empFreq_nonneg D c x) ha'b
      ht_pos.le ht_le_pb, by rw [tv_shift p ha'b t ht_pos.le]; exact ht_le_r⟩

/-! ===========================================================================
    §5  ⭐⭐⭐ 主判据：**何时 `IsPoint`**
    =========================================================================== -/

/-- **频率层单点档**（与 `LawRule.IsPoint` 对应；桥见 §6）。 -/
def IsPointFreq (R : C → X → Set (Y → ℝ)) : Prop := ∀ c x, ∃ f, R c x = {f}

/-- **层是纯的**：经验核是点质量 $\hat p=\delta_{y_0}$。 -/
def LayerPure (D : Data C X Y) (c : C) (x : X) : Prop :=
  ∃ y₀, ∀ y, empFreq D c x y = if y = y₀ then 1 else 0

/-- **半径处处为零**。 -/
def RadiusAllZero (ρ : Radius C X) : Prop := ∀ c x, ρ.r c x = 0

/-- ⭐⭐ **判据（正向）**：半径处处为零 ⟹ α 的像处处单点。 -/
theorem isPoint_of_all_zero_radius (D : Data C X Y) (ρ : Radius C X)
    (hlayer : ∀ c x, layerCount D c x ≠ 0) (hρ : RadiusAllZero ρ) :
    IsPointFreq (StatRule D ρ) :=
  fun c x => ⟨empFreq D c x, band_isPoint_of_zero_radius D ρ c x (hlayer c x) (hρ c x)⟩

/-- ⭐⭐⭐ **判据（反向）**：α 处处单点 ⟹ 半径处处为零（层非空、$|Y|\ge2$）。 -/
theorem all_zero_radius_of_isPoint [Nonempty Y] (D : Data C X Y) (ρ : Radius C X)
    (hY : ∃ a b : Y, a ≠ b) (hlayer : ∀ c x, layerCount D c x ≠ 0)
    (hpt : IsPointFreq (StatRule D ρ)) : RadiusAllZero ρ := by
  intro c x
  by_contra hne
  have hpos : 0 < ρ.r c x := lt_of_le_of_ne (ρ.nonneg c x) (Ne.symm hne)
  obtain ⟨f₁, f₂, hne12, h1, h2⟩ := band_not_singleton_of_pos_radius D ρ c x hY
    (empFreq_sum D c x (hlayer c x)) hpos
  obtain ⟨g, hg⟩ := hpt c x
  rw [hg, Set.mem_singleton_iff] at h1 h2
  exact hne12 (h1.trans h2.symm)

/-- ⭐⭐⭐ **主判据（充要）**：$\alpha_{\text{stat}}$ 处处单点 $\iff$ 半径处处为零。 -/
theorem isPoint_iff_all_zero_radius [Nonempty Y] (D : Data C X Y) (ρ : Radius C X)
    (hY : ∃ a b : Y, a ≠ b) (hlayer : ∀ c x, layerCount D c x ≠ 0) :
    IsPointFreq (StatRule D ρ) ↔ RadiusAllZero ρ :=
  ⟨all_zero_radius_of_isPoint D ρ hY hlayer, isPoint_of_all_zero_radius D ρ hlayer⟩

/-- ⭐⭐ **零半径 ⟹ 单点；反之球单点 ⟹ 经验核在球内（半径 $\ge0$）。** -/
theorem zero_radius_and_back :
    (∀ (C X Y : Type) [DecidableEq C] [DecidableEq X] [DecidableEq Y] [Fintype Y]
        (D : Data C X Y) (ρ : Radius C X) (c : C) (x : X),
      layerCount D c x ≠ 0 → ρ.r c x = 0 → StatRule D ρ c x = {empFreq D c x}) := by
  intro C X Y _ _ _ _ D ρ c x hN hρ
  exact band_isPoint_of_zero_radius D ρ c x hN hρ

/-- ⭐⭐ **数据 + 统计双条件**：**零半径**且**层纯** ⟹ 球 $=\{$点质量$\}$。

**这是「何时可当确定性世界模型」的最后一环**：`IsPoint` 只要求球是
$\{\hat p\}$，而 $\hat p$ **本身是否点质量**由 `LayerPure` 决定。 -/
theorem pure_and_zero_gives_dirac (D : Data C X Y) (ρ : Radius C X) (c : C) (x : X)
    (hN : layerCount D c x ≠ 0) (hρ : ρ.r c x = 0) (hpure : LayerPure D c x) :
    ∃ y₀, StatRule D ρ c x = {fun y => if y = y₀ then 1 else 0} := by
  obtain ⟨y₀, hy₀⟩ := hpure
  refine ⟨y₀, ?_⟩
  rw [band_isPoint_of_zero_radius D ρ c x hN hρ]
  congr 1
  funext y
  exact hy₀ y

/-- ⭐⭐⭐ **完整判据**：α 的像处处**确定性（Dirac）** $\iff$
**半径处处为零**且**每层纯**。

**⟹** 回答「何时 `IsPoint`」：
- 只用 `IsPoint`（球单点）：判据是**零半径**（`isPoint_iff_all_zero_radius`）；
- 要求**世界模型可用**（规则 = Dirac）：还须**层纯**。
两项**不可互推**。 -/
theorem diracRule_iff_zero_and_pure [Nonempty Y] (D : Data C X Y) (ρ : Radius C X)
    (hY : ∃ a b : Y, a ≠ b) (hlayer : ∀ c x, layerCount D c x ≠ 0) :
    (∀ c x, ∃ y₀, StatRule D ρ c x = {fun y => if y = y₀ then 1 else 0}) ↔
      RadiusAllZero ρ ∧ ∀ c x, LayerPure D c x := by
  constructor
  · intro h
    have hpt : IsPointFreq (StatRule D ρ) := fun c x => by
      obtain ⟨y₀, hy⟩ := h c x; exact ⟨_, hy⟩
    have hρ := all_zero_radius_of_isPoint D ρ hY hlayer hpt
    refine ⟨hρ, ?_⟩
    intro c x
    obtain ⟨y₀, hy₀⟩ := h c x
    refine ⟨y₀, ?_⟩
    have hband := band_isPoint_of_zero_radius D ρ c x (hlayer c x) (hρ c x)
    rw [hband] at hy₀
    have heq : empFreq D c x = fun y => if y = y₀ then (1:ℝ) else 0 :=
      (Set.singleton_injective hy₀)
    intro y
    exact congrFun heq y
  · rintro ⟨hρ, hpure⟩ c x
    exact pure_and_zero_gives_dirac D ρ c x (hlayer c x) (hρ c x) (hpure c x)

/-! ===========================================================================
    §6  与 `LawRule` 的桥（**缺口如实登记**）
    =========================================================================== -/

/-- **频率向量 → 测度**：$\sum_y f(y)\,\delta_y$。

**⚠ 缺口**：**单射性未证**（需 `MeasurableSingletonClass Y`）。
故频率层 `IsPointFreq` 与 `LawRule.IsPoint` 的等价是**未闭合项**；
本定义只登记桥的形状。 -/
noncomputable def freqToMeasure [MeasurableSpace Y] (f : Y → ℝ) :
    MeasureTheory.Measure Y :=
  ∑ y, ENNReal.ofReal (f y) • MeasureTheory.Measure.dirac y

end StatAlpha

end Fate
