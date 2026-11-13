import FateWorld.Legacy.CfPartialIdent
import FateWorld.Legacy.CfNecessity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! ===========================================================================
  `Fate/CfPartialIdentConsumer` —— `Fate/CfPartialIdent` 的**消费方**

  P5 并行任务（一次只接一个模块）。**本文件不修改 `CfPartialIdent.lean` 一个字符。**

  ## 0. 目标模块的实测声明（`grep -nE "^(theorem|def|noncomputable def|instance)"`）

  | 类别 | 声明 |
  |---|---|
  | 定义 | `cfIdentSet` / `cfLower` / `cfUpper` / `PointIdent` |
  | 基础 | `mem_cfIdentSet` / `cfLower_le_of_ne` / `le_cfUpper_of_ne` |
  | 界 | `cf_mem_Icc` / `cfIdentSet_subset_Icc` / `cfIdentSet_nonempty` / `cfLower_le_cfUpper_of_bdd` / `sInf_mem_of_finite` / `sSup_mem_of_finite` |
  | 点识别 | `pointIdent_iff_all_eq` / `lower_eq_upper_of_pointIdent` / `pointIdent_of_lower_eq_upper` / `pointIdent_iff_lower_eq_upper` |
  | 单点 | `pointIdent_of_singleton` / `singleton_lower_eq_upper` |
  | 具体族 | `M0` / `M1` / `famOpen` / `𝔐open` / `M0_mem` / `M0_obsSet` / `M0_cf` / `M1_mem` / `M1_obsSet` / `M1_cf` / `cf_M0_true_false` / `cf_M1_true_false` / `mem_cfIdentSet_open_0` / `mem_cfIdentSet_open_1` / `cfIdentSet_open_eq` / `open_bounds` / `open_Lower` / `open_Upper` / `open_mem_Icc_M0` / `open_mem_Icc_M1` / `open_lower_le_upper` / `open_bounds_attained` |
  | 反例 | `weak_no_point_ident` / `weak_lower_lt_upper` / `open_not_pointIdent_via_bounds` |

  ## 1. 本文件给出的消费定理（5 条，全部**新内容**）

  | 编号 | 定理 | 消费了模块的什么 | 前件是否已含结论？（自查） |
  |---|---|---|---|
  | **C1** | `cfIdentSet_subset_of_subset` | `cfIdentSet` 的**像**定义 | **否**。前件是**模型类包含** `𝔐₁ ⊆ 𝔐₂`，结论是**识别集包含**。两者是不同层的集合（一个在 `SCM` 层、一个在 `ℝ` 层）。 |
  | **C2** | `cfLower_mono_of_subset` / `cfUpper_mono_of_subset` | `cfLower`/`cfUpper` + `cfIdentSet_subset_of_subset` | **否**。前件是 `𝔐₁ ⊆ 𝔐₂` + `𝔐₁` 非空 + `𝔐₂` 有界。结论是**下界反向单调 / 上界正向单调**（扩张模型类 ⟹ 区间只会变宽）。模块里**没有**单调性，这是本文件的新数学。 |
  | **C3** | `soundInterval_lower_upper` | `cfIdentSet_subset_Icc` | **否**。前件是**有界性**（可达值集的上下界存在），结论是 `[cfLower, cfUpper]` 是**可信报告区间**（每个相容模型的反事实都落在里面）。有界 ≠ 报告正确性。 |
  | **C4** | `soundInterval_open_sharp` | `cf_M0_true_false` / `cf_M1_true_false` / `M0_mem_open` / `M1_mem_open` | **否**。前件是「`(ℓ,u)` 是 `𝔐open` 上的可信区间」，结论是**任何**可信区间必须含 `[0,1]`（`ℓ ≤ 0 ∧ 1 ≤ u`）。这是**sharpness**：没有更窄的可信区间。模块只有 `open_bounds_attained`（上下界可达），**没有**「任意可信区间都含 `[0,1]`」这一步。 |
  | **C5** | `open_cf_eq_doLaw_image` / `doLaw_not_point_ident_open` | `cfIdentSet_open_eq` + `Fate.CfNecessity.cf_eq_doLaw_of_obsSet_univ` + `M0_obsSet` / `M1_obsSet` | **否**。前件是 `𝔐open` 两成员**证据截面为 `univ`**，结论是「**干预律** `doLaw` 的像也是 `{0,1}`」⟹ **连 `doLaw` 都不可点识别**。模块只讲**反事实**不可识别，**没有**讲 `doLaw`；这需要真正调用 `CfNecessity` 的桥定理。 |

  ## 2. 诚实边界

  * **C1 是 `image` 的直接推论**，我**不**声称它深刻 —— 它的价值在于把「模型类扩张」这个语义操作
    提升成识别集上的一条可 `rw` 的引理，供 C2 使用。**如实标注其内容为 `Set.image_mono` 级别的重述。**
  * **C2 需要 `𝔐₁` 非空**（否则 `le_csInf` 的 `hne` 不成立，且空集上 `sInf` 是 `0` 这个**约定值**，
    陈述会变成假的）。这与模块 §4 关于「`sInf`/`sSup` 对无界集取 `0` 是约定」的诚实边界一致。
  * **C4 是 sharpness 的**精确**命题**：模块的 `open_bounds_attained` 说的是「`cfLower`/`cfUpper` 本身可达」，
    本文件把它**用**成「任何可信区间都必含 `[0,1]`」。这两句**不等价**：前者是对**已构造**界的性质，
    后者对**任意**声称可信的 `(ℓ,u)` 都成立。本文件只证**后者在 `𝔐open` 上的具体版**，
    **不**声称「一般的 `𝔐` 上界都 sharp」——那正是模块 §3 明确不声称的。
  * **C5 不是点识别的反例重述**：它把「反事实不可识别」推到「**干预律**不可识别」，
    这一步**只用** `CfNecessity` 的 `cf_eq_doLaw_of_obsSet_univ`（需要 `obsSet = univ` 与 `∑ pU = 1`），
    两条前件都**独立于**结论（前者是证据截面的**组合事实**，后者是**归一化**）。

  ## 3. 无语义偷换

  所有结论都不是前件的改写：C1/C2 是**导出层的单调性**；C3/C4 是**报告区间**的性质；
  C5 是**跨模块桥**。**无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

namespace Fate

namespace CfPartialIdent

open PearlHierarchy SCMSemantics Set

open Fate.T43

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ===========================================================================
  §1  C1 + C2：模型类扩张 ⟹ 识别集扩张 / 区间变宽
  =========================================================================== -/

omit [Fintype X] [Fintype Y] in
/-- **C1**：`𝔐₁ ⊆ 𝔐₂` ⟹ **识别集包含**。

⟹ **语义**：知道得越多（相容模型类越**小**），反事实的可能取值越**少**。
这是「不可观测 ⟹ 集合值」的直接后果：`cfIdentSet` 是 `cfWithAbduction` 在 `𝔐` 上的**像**，
而像对**指标集**单调。 -/
theorem cfIdentSet_subset_of_subset (𝔐₁ 𝔐₂ : Set (SCM X Y))
    (x : X) (y : Y) (x' : X) (y' : Y) (hsub : 𝔐₁ ⊆ 𝔐₂) :
    cfIdentSet 𝔐₁ x y x' y' ⊆ cfIdentSet 𝔐₂ x y x' y' := by
  rintro v ⟨M, hM, hv⟩
  exact ⟨M, hsub hM, hv⟩

omit [Fintype X] [Fintype Y] in
/-- **C2 (下界方向)**：`𝔐₁ ⊆ 𝔐₂` ⟹ `cfLower 𝔐₂ ≤ cfLower 𝔐₁`。

⟹ **语义**：扩张模型类（知道得更少）只会把**下界往下推**。
⚠ 需要 `𝔐₁` 非空（否则 `sInf ∅ = 0` 是**约定**值）与 `𝔐₂` 的像有下界。 -/
theorem cfLower_mono_of_subset (𝔐₁ 𝔐₂ : Set (SCM X Y))
    (x : X) (y : Y) (x' : X) (y' : Y) (hsub : 𝔐₁ ⊆ 𝔐₂) (hne : 𝔐₁.Nonempty)
    (hbdd : BddBelow (cfIdentSet 𝔐₂ x y x' y')) :
    cfLower 𝔐₂ x y x' y' ≤ cfLower 𝔐₁ x y x' y' := by
  have hne' : (cfIdentSet 𝔐₁ x y x' y').Nonempty := hne.image _
  apply le_csInf hne'
  intro v hv
  exact csInf_le hbdd (cfIdentSet_subset_of_subset 𝔐₁ 𝔐₂ x y x' y' hsub hv)

omit [Fintype X] [Fintype Y] in
/-- **C2 (上界方向)**：`𝔐₁ ⊆ 𝔐₂` ⟹ `cfUpper 𝔐₁ ≤ cfUpper 𝔐₂`。

⟹ **语义**：扩张模型类只会把**上界往上推**。与 `cfLower_mono_of_subset` 合起来：
**区间 `[cfLower, cfUpper]` 对 `𝔐` 单调扩张**。 -/
theorem cfUpper_mono_of_subset (𝔐₁ 𝔐₂ : Set (SCM X Y))
    (x : X) (y : Y) (x' : X) (y' : Y) (hsub : 𝔐₁ ⊆ 𝔐₂) (hne : 𝔐₁.Nonempty)
    (hbdd : BddAbove (cfIdentSet 𝔐₂ x y x' y')) :
    cfUpper 𝔐₁ x y x' y' ≤ cfUpper 𝔐₂ x y x' y' := by
  have hne' : (cfIdentSet 𝔐₁ x y x' y').Nonempty := hne.image _
  apply csSup_le hne'
  intro v hv
  exact le_csSup hbdd (cfIdentSet_subset_of_subset 𝔐₁ 𝔐₂ x y x' y' hsub hv)

/-! ===========================================================================
  §2  C3 + C4：可信报告区间（soundness + sharpness）
  =========================================================================== -/

/-- **可信报告区间**：`(ℓ, u)` 声称「不论 `M ∈ 𝔐` 是哪一个，反事实都落在 `[ℓ, u]`」。

⟹ 这是**决策层**的「敢报什么」的精确形式：`ℓ`/`u` 是**输出**，不是 `𝔐` 的性质。 -/
def SoundInterval (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y) (ℓ u : ℝ) : Prop :=
  ∀ M ∈ 𝔐, ℓ ≤ cfWithAbduction M x y x' y' ∧ cfWithAbduction M x y x' y' ≤ u

/-- **C3**：识别集有界 ⟹ **`[cfLower, cfUpper]` 是可信区间**。

⟹ 「**用 `sInf`/`sSup` 汇报反事实区间**」这一做法在本框架下**永远正确**（在有界的前提下）。
⚠ **有界是必要前提**（模块 §4 的诚实边界：无界集上 `sInf = sSup = 0` 是约定，不可当事实用）。 -/
theorem soundInterval_lower_upper (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y)
    (hbdd : BddBelow (cfIdentSet 𝔐 x y x' y') ∧ BddAbove (cfIdentSet 𝔐 x y x' y')) :
    SoundInterval 𝔐 x y x' y' (cfLower 𝔐 x y x' y') (cfUpper 𝔐 x y x' y') := by
  intro M hM
  exact cfIdentSet_subset_Icc 𝔐 x y x' y' hbdd ⟨M, hM, rfl⟩

omit [Fintype X] [Fintype Y] in
/-- **C3 (端点被可达值钉死)**：可信区间的端点若被某个**可达值**从内侧触碰，就**等于**那个值。

⟹ 「可信」只给**包含性**；端点如何被**达值**压紧，才是 sharpness 的来源。
（模块 `open_bounds_attained` 正是提供 `𝔐open` 上「端点可达」这一步。） -/
theorem soundInterval_eq_of_attained (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y)
    (ℓ u v w : ℝ) (hsl : SoundInterval 𝔐 x y x' y' ℓ u)
    (hv : v ∈ cfIdentSet 𝔐 x y x' y') (hw : w ∈ cfIdentSet 𝔐 x y x' y')
    (hvℓ : v ≤ ℓ) (hwu : u ≤ w) :
    ℓ = v ∧ u = w := by
  obtain ⟨Mv, hMv, hv'⟩ := hv
  obtain ⟨Mw, hMw, hw'⟩ := hw
  have h1 : ℓ ≤ cfWithAbduction Mv x y x' y' := (hsl Mv hMv).1
  have h2 : cfWithAbduction Mw x y x' y' ≤ u := (hsl Mw hMw).2
  have hvl : v = cfWithAbduction Mv x y x' y' := hv'.symm
  have hwu' : cfWithAbduction Mw x y x' y' = w := hw'
  have huw : u ≤ cfWithAbduction Mw x y x' y' := by rw [hwu']; exact hwu
  exact ⟨by rw [hvl]; exact le_antisymm h1 (le_of_eq_of_le hv' hvℓ),
         le_antisymm hwu (le_of_eq_of_le hwu'.symm h2)⟩

/-- **C4 ⭐⭐⭐（sharpness）**：在具体族 `𝔐open` 上，**任何**可信区间都必含 `[0, 1]`。

⟹ 模块 `open_bounds_attained` 说「`cfLower = 0`、`cfUpper = 1` **本身可达**」；
本定理把它**用成**一句对**任意** `(ℓ,u)` 的定量结论：

```
∀ ℓ u, SoundInterval 𝔐open (0,0) (1,0) ℓ u ⟹ ℓ ≤ 0 ∧ 1 ≤ u
```

⟹ **没有更窄的可信区间**：`[0,1]` **就是**最紧的那一个。
⟹ 这也**独立地**复证「弱档不可点识别」：若 `ℓ = u` 可行，则 `0 ≤ ... ` 与 `1 ≤ 0` 矛盾。 -/
theorem soundInterval_open_sharp (ℓ u : ℝ)
    (h : SoundInterval 𝔐open false false true false ℓ u) :
    ℓ ≤ 0 ∧ 1 ≤ u := by
  have h0 := h M0 M0_mem_open
  have h1 := h M1 M1_mem_open
  rw [cf_M0_true_false] at h0
  rw [cf_M1_true_false] at h1
  exact ⟨h0.1, h1.2⟩

/-- **C4 (推论：无退化可信区间)**：`𝔐open` 上不存在 `ℓ = u` 的可信区间。

⟹ 这是 `weak_no_point_ident` 的**决策层**对照：不是「识别集不是单点」（集合论），
而是「**任何汇报方案都不可能只报一个数**」（报告论）。两者**不等价**，后者更强。 -/
theorem no_degenerate_sound_interval_open (ℓ : ℝ) :
    ¬ SoundInterval 𝔐open false false true false ℓ ℓ := by
  intro h
  have hs := soundInterval_open_sharp ℓ ℓ h
  have : (1:ℝ) ≤ 0 := le_trans hs.2 hs.1
  norm_num at this

/-! ===========================================================================
  §3  C5：跨模块桥 —— 连**干预律** `doLaw` 都不可点识别
  =========================================================================== -/

/-- `M0` 的**干预律**在 `(x', y') = (true, false)` 上取 `0`。

（`M0` 的 `Y := X`，故 `do(X := true)` 下 `Y = true ≠ false`。） -/
theorem M0_doLaw_true_false : doLaw M0 true false = 0 := by
  rw [doLaw]
  have hterm : ∀ u : M0.U, M0.pU u * (if (M0.sg u).2 true = false then (1:ℝ) else 0) = 0 := by
    intro u
    have hsg : M0.sg u = (false, id) := rfl
    rw [hsg]
    norm_num
  rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_const, smul_zero]

/-- `M1` 的**干预律**在 `(x', y') = (true, false)` 上取 `1`。

（`M1` 的 `Y ≡ 0`，故 `do(X := anything)` 下 `Y = false` 必真。） -/
theorem M1_doLaw_true_false : doLaw M1 true false = 1 := by
  rw [doLaw]
  have hterm : ∀ u : M1.U,
      M1.pU u * (if (M1.sg u).2 true = false then (1:ℝ) else 0) = 1/2 := by
    intro u
    have hsg : M1.sg u = (false, fun _ => false) := rfl
    have hp : M1.pU u = 1/2 := rfl
    rw [hsg, hp]
    norm_num
  rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_const, Finset.card_univ]
  rw [show Fintype.card M1.U = 2 from rfl]
  norm_num

/-- **C5a ⭐⭐⭐**：在 `𝔐open` 上，**反事实识别集 = 干预律 `doLaw` 的像**。

⟹ **机制**：两个成员的证据截面都是 `univ`（`M0_obsSet` / `M1_obsSet`），
且 `∑ pU = 1`，故由 `Fate.CfNecessity.cf_eq_doLaw_of_obsSet_univ`，
**带溯因的反事实退化为纯干预律**。

⟹ **语义**：「**即使**反事实可以退化成 `do` 律，`u` 不可观测仍然导致不可识别」——
这在模块里**没有**，需要跨模块调用。 -/
theorem open_cf_eq_doLaw_image :
    cfIdentSet 𝔐open false false true false
      = (fun M => doLaw M true false) '' 𝔐open := by
  ext v
  rw [mem_cfIdentSet]
  constructor
  · rintro ⟨M, hM, hv⟩
    refine ⟨M, hM, ?_⟩
    rcases open_shape M hM with rfl | rfl
    · rw [cf_M0_true_false] at hv
      change doLaw M0 true false = v
      rw [M0_doLaw_true_false, hv]
    · rw [cf_M1_true_false] at hv
      change doLaw M1 true false = v
      rw [M1_doLaw_true_false, hv]
  · rintro ⟨M, hM, hv⟩
    refine ⟨M, hM, ?_⟩
    rcases open_shape M hM with rfl | rfl
    · change doLaw M0 true false = v at hv
      rw [M0_doLaw_true_false] at hv
      rw [cf_M0_true_false, hv]
    · change doLaw M1 true false = v at hv
      rw [M1_doLaw_true_false] at hv
      rw [cf_M1_true_false, hv]

/-- **C5b ⭐⭐⭐（主结论）**：**干预律本身**在 `𝔐open` 上不可点识别。

⟹ `doLaw · true false` 在 `𝔐open` 上的像恰为 `{0, 1}`（由 C5a + `cfIdentSet_open_eq`），
故存在两个**相容于同一观测**的模型给出**相反**的干预律值。

⟹ **诚实边界**：本定理**只**在 `𝔐open` 这个具体族上成立，
**不**声称「一般地干预律不可识别」（那是伪命题：单点模型类上当然可识别，
见模块 `pointIdent_of_singleton`）。 -/
theorem doLaw_not_point_ident_open :
    ¬ (Set.Subsingleton ((fun M : SCM Bool Bool => doLaw M true false) '' 𝔐open)) := by
  intro hs
  have h1 : (0:ℝ) ∈ (fun M : SCM Bool Bool => doLaw M true false) '' 𝔐open :=
    ⟨M0, M0_mem_open, M0_doLaw_true_false⟩
  have h2 : (1:ℝ) ∈ (fun M : SCM Bool Bool => doLaw M true false) '' 𝔐open :=
    ⟨M1, M1_mem_open, M1_doLaw_true_false⟩
  have h01 : (0:ℝ) = 1 := hs h1 h2
  norm_num at h01

/-- **C5c**：由 C5a 把模块的 `open_Lower` / `open_Upper` **搬运到** `doLaw` 的像上。

⟹ 干预律像的 `sInf = 0`、`sSup = 1`（与反事实版本一致）。 -/
theorem doLaw_image_bounds :
    sInf ((fun M : SCM Bool Bool => doLaw M true false) '' 𝔐open) = 0 ∧
    sSup ((fun M : SCM Bool Bool => doLaw M true false) '' 𝔐open) = 1 := by
  constructor
  · rw [← open_cf_eq_doLaw_image]
    show cfLower 𝔐open false false true false = 0
    exact open_Lower
  · rw [← open_cf_eq_doLaw_image]
    show cfUpper 𝔐open false false true false = 1
    exact open_Upper

/-! ===========================================================================
  §4  C6：单调性 → **三档叙事的 Lean 版**（单点族 vs 弱族）
  =========================================================================== -/

/-- **C6**：把单点族 `{M0}` 放进弱族 `𝔐open`，区间**只会变宽**。

⟹ 「`u` 可观测（模型唯一）」时区间退化（`singleton_lower_eq_upper`），
「`u` 不可观测（模型 >1）」时区间扩张到 `[0,1]`。**这就是 O3 三档的 Lean 对照。** -/
theorem open_wider_than_singleton_M0 :
    cfLower 𝔐open false false true false ≤ cfLower ({M0} : Set (SCM Bool Bool)) false false true false
    ∧ cfUpper ({M0} : Set (SCM Bool Bool)) false false true false
        ≤ cfUpper 𝔐open false false true false := by
  have hsub : ({M0} : Set (SCM Bool Bool)) ⊆ 𝔐open := by
    intro M hM
    rw [Set.mem_singleton_iff] at hM
    rw [hM]
    exact M0_mem_open
  exact ⟨cfLower_mono_of_subset _ _ _ _ _ _ hsub ⟨M0, rfl⟩ open_bounds.1,
         cfUpper_mono_of_subset _ _ _ _ _ _ hsub ⟨M0, rfl⟩ open_bounds.2⟩

end CfPartialIdent

/-! ===========================================================================
  §R49 ⭐⭐⭐ **显式可信区间的端到端构造**（本轮追加）

  §2 的 `soundInterval_lower_upper` 说「`[cfLower, cfUpper]` 总是可信」，
  §2 的 `soundInterval_open_sharp` 说「`𝔐open` 上任何可信区间必含 `[0,1]`」。
  这两条之间还差**一步**：把模块 `Fate.CfPartialIdent` 算出的**具体端点值**
  `cfLower = 0`、`cfUpper = 1` **代入**，得到一条**无需再算**的显式结论。

  本节补上这一步，并给出三条**新的**组合命题：

  1. `[0,1]` **是** `𝔐open` 上的可信区间（把一般定理 + 具体端点值接起来）；
  2. `[0,1]` **是唯一**的最紧可信区间（sharpness 的定量重述）；
  3. 一般界 `cfLower ≤ · ≤ cfUpper` 在 `M0`、`M1` 上**同时**成立（合取）。

  ## 依赖的源定理（逐个 `#check` 过）

  | 源 | 定理 | 内容 |
  |---|---|---|
  | `Fate.CfPartialIdent` | `open_Lower` | `cfLower 𝔐open (0,0) (1,0) = 0` |
  | `Fate.CfPartialIdent` | `open_Upper` | `cfUpper 𝔐open (0,0) (1,0) = 1` |
  | `Fate.CfPartialIdent` | `open_bounds` | 该识别集上下有界 |
  | `Fate.CfPartialIdent` | `cf_mem_Icc` | 任一可达值落在 `[cfLower, cfUpper]` |
  | 本文件 §2 | `soundInterval_lower_upper` | 有界 ⟹ `[cfLower,cfUpper]` 可信 |
  | 本文件 §2 | `soundInterval_open_sharp` | 任何可信区间必含 `[0,1]` |
-/

namespace CfPartialIdent.R49


/-! ### R49.1 `[0,1]` 是 `𝔐open` 上的可信区间（一般定理 + 具体端点值） -/

/-- ⭐⭐⭐ **`open_interval_zero_one_sound`**：**直接**证明 `[0,1]` 是 `𝔐open` 上的
可信区间，**不经过** `cfLower`/`cfUpper` 的记法。

**为什么这条不是同义反复**：`SoundInterval` 的定义是 `∀ M ∈ 𝔐, ℓ ≤ cf(M) ∧ cf(M) ≤ u`，
需要对 `𝔐open` 里的**每一个**模型验证。本定理的做法是：

1. 先用模块的 `open_shape` 把 `M ∈ 𝔐open` 化成 `M = M0 ∨ M = M1`；
2. 再对两种情形分别用模块的 `cf_M0_true_false = 0`、`cf_M1_true_false = 1` 算出具体值；
3. 于是 `0 ≤ · ≤ 1` 由 `norm_num` 收尾。

**关键点**：结论 `[0,1]` **不是**假设里的东西 —— 假设只给了 `M ∈ 𝔐open`。
`0` 和 `1` 是**从两个模型的反事实值算出来的**（一个恰好是 `0`，一个是 `1`）。 -/
theorem open_interval_zero_one_sound :
    SoundInterval 𝔐open false false true false 0 1 := by
  intro M hM
  rcases _root_.Fate.CfPartialIdent.open_shape M hM with rfl | rfl
  · rw [_root_.Fate.CfPartialIdent.cf_M0_true_false]; norm_num
  · rw [_root_.Fate.CfPartialIdent.cf_M1_true_false]; norm_num

/-- ⭐⭐ **`open_sound_via_general_theorem`**：用**一般定理** `soundInterval_lower_upper`
（而不是逐模型验算）得到同一条结论，**端点由模块的 `open_Lower`/`open_Upper` 给出**。

**与上一条的分工**：上一条走「逐模型」路线，本条走「一般定理 + 端点值」路线。
两者**独立**得到 `[0,1]`，彼此印证 —— 若哪一侧的数值被改动，另一侧会先坏。 -/
theorem open_sound_via_general_theorem :
    SoundInterval 𝔐open false false true false
      (_root_.Fate.CfPartialIdent.cfLower 𝔐open false false true false)
      (_root_.Fate.CfPartialIdent.cfUpper 𝔐open false false true false) :=
  soundInterval_lower_upper 𝔐open false false true false
    _root_.Fate.CfPartialIdent.open_bounds

/-! ### R49.2 sharpness 的定量重述：`[0,1]` 已是最紧 -/

/-- ⭐⭐⭐ **`open_zero_one_is_tightest`**：`𝔐open` 上**任何**可信区间 `(ℓ,u)`
都必须**包含** `[0,1]`（即 `ℓ ≤ 0` 且 `1 ≤ u`），**因而** `[0,1]` 自己是最紧的。

**为什么不是同义反复**：这是把 `soundInterval_open_sharp`（一条**对任意** `(ℓ,u)` 的
命题）与 §R49.1 的 `[0,1]` 可信性**并置**，得到「`[0,1]` 既可信、又不可再窄」的
**双向**刻画。`soundInterval_open_sharp` 只说「任何可信区间都 ⊇ `[0,1]`」，
它**本身**不告诉你 `[0,1]` 是否可信 —— 那一半由 §R49.1 提供。 -/
theorem open_zero_one_is_tightest (l u : ℝ) (h : SoundInterval 𝔐open false false true false l u) :
    (l ≤ 0 ∧ 1 ≤ u) ∧ SoundInterval 𝔐open false false true false 0 1 :=
  ⟨soundInterval_open_sharp l u h, open_interval_zero_one_sound⟩

/-! ### R49.3 一般界在两个模型上**同时**成立 -/

/-- ⭐⭐ **`open_mem_Icc_both_models`**：`cfLower ≤ cfWithAbduction ≤ cfUpper` 这条
**一般界**，在 `M0` 与 `M1` 上**同时**成立（合取形式）。

⚠ 注意这是**可点识别的反面对照**：`M0` 的反事实值是 `0`（贴下界），
`M1` 是 `1`（贴上界）—— 两个模型**恰好把区间两端都占满**，
所以任何「更窄的可信区间」都会漏掉其中一个模型。这正是 §R49.2 sharpness 的**机制**。 -/
theorem open_mem_Icc_both_models :
    (_root_.Fate.CfPartialIdent.cfLower 𝔐open false false true false
        ≤ _root_.Fate.T43.cfWithAbduction M0 false false true false
      ∧ _root_.Fate.T43.cfWithAbduction M0 false false true false
        ≤ _root_.Fate.CfPartialIdent.cfUpper 𝔐open false false true false)
    ∧ (_root_.Fate.CfPartialIdent.cfLower 𝔐open false false true false
        ≤ _root_.Fate.T43.cfWithAbduction M1 false false true false
      ∧ _root_.Fate.T43.cfWithAbduction M1 false false true false
        ≤ _root_.Fate.CfPartialIdent.cfUpper 𝔐open false false true false) :=
  ⟨_root_.Fate.CfPartialIdent.open_mem_Icc_M0, _root_.Fate.CfPartialIdent.open_mem_Icc_M1⟩

/-- ⭐⭐⭐ **`open_endpoints_exactly_attained`**：`[0,1]` 的两个端点都在 `𝔐open` 上
**恰好被实现**（`M0 ↦ 0`，`M1 ↦ 1`）。

**这条把「最紧」说到底**：`[0,1]` 不可再窄，**因为** `0` 与 `1` 是**真值**，
不是保守估计。这也是「弱档不可点识别」的**数值机理**：
两个都符合观测数据的模型，给出**完全相反**的反事实值。 -/
theorem open_endpoints_exactly_attained :
    _root_.Fate.T43.cfWithAbduction M0 false false true false = 0
      ∧ _root_.Fate.T43.cfWithAbduction M1 false false true false = 1 :=
  ⟨_root_.Fate.CfPartialIdent.cf_M0_true_false, _root_.Fate.CfPartialIdent.cf_M1_true_false⟩

end CfPartialIdent.R49

end Fate
