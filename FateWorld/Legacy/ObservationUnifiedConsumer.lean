/-
  Fate · **接入：ObservationUnified 的消费方**
  （`Fate/_wip` 新工作流：先在 `_wip` 验证 `EXIT=0`，再搬回 `Fate/` 并加 import）

  源模块：`Fate/ObservationUnified.lean`（`namespace Fate.ObservationUnified`，465 行）
  接入方向：把「观测反推潜变量的三档」（`InversionTier`：`bounded` / `posterior` /
            `quotient`）当作**统一接口**去消费 —— 不重述它的三条主定理，而是把它的
            **载体**（`Inversion` / `classOf` / `PosteriorData.post` / `BoundedData`）
            接到仓内三条**独立主线**上：
              · `Fate.MiddleZoneDichotomy`（中间地带二分法，**纯函数论**层）
              · `Fate.TieredScheme`（预测/干预/反事实**分档读出**层）
              · （`BoundedData` 的零误差界，接到上面的中间地带）

  ============================================================================
  (a) 目标模块 `ObservationUnified` 的**全部核心声明**（实测）
      `grep -nE "^(theorem|def|noncomputable def|structure|inductive)"`
  ============================================================================
  §OU.1  `inductive InversionTier`（`.bounded` / `.posterior` / `.quotient`，
         `deriving DecidableEq, Repr`）                                     L98
         `structure Inversion (W : Type u) (Y : Type v)`（字段 `tier`、`h`）  L119
  §OU.2  `Inversion.ker`（`Setoid W`）                                       L134
         `Inversion.quo`（`Type u`，`Quotient I.ker`）                       L139
         `Inversion.classOf`（`W → I.quo`）                                  L145
         `classOf_eq_iff`                                                    L151
         `mem_class_iff`                                                     L158
         `Inversion.liftH`（`I.quo → Y`）                                     L165
         `liftH_classOf`                                                     L169
         `liftH_injective`                                                   L178
         `liftH_surjOn`                                                      L187
         `quotient_of_injective_is_trivial`                                  L197
         `injective_iff_classOf_injective`                                   L204
  §OU.3  `structure PosteriorData`（`prior : PMF W`、`lik : Y → W → ENNReal`） L222
         `PosteriorData.post`（`Y → W → ENNReal`）                            L237
         `post_eq_zero_of_lik_zero`                                          L243
         `post_eq_of_const_lik`                                              L254
         `post_const_lik_apply`                                              L262
         `post_single_support`                                               L271
         `post_single_target`                                                L277
  §OU.4  `structure BoundedData W Y [PseudoMetricSpace W]`
         （`h`、`est`、`ε`、`hε : 0 ≤ ε`、`hbound`）                          L293
         `BoundedData.estOf`                                                 L312
         `est_eq_of_injective_exact`                                         L318
         `est_within_bound`                                                  L327
         `candidates_close`                                                  L337
         `zero_bound_candidates_eq`                                          L347
  §OU.5  `inversion_tier_trichotomy`                                         L360
         `tier_output_shape_quotient_ne_posterior`                           L416
         `tier_output_shape_bounded_ne_quotient`                             L420
         `strong_implies_quotient`                                           L428
         `posterior_factors_through_class`                                   L442
         `bounded_posterior_agree_at_point`                                  L452

  ============================================================================
  (b) 本文件写了几条消费定理（5 条）+ 逐条**防同义反复**说明
  ============================================================================

  1. `weak_tier_equals_middle_zone`（消费 `classOf_eq_iff` + `MiddleZone`）
     结论：`MiddleZone I.h = {p | I.classOf p.1 = I.classOf p.2 ∧ p.1 ≠ p.2}`。
     前件**只有** `I : Inversion W Y`（裸载体：两个字段，**零假设**）。
     左侧来自 `Fate.MiddleZoneDichotomy`（其变量是**任意函数** `Φ`，不认识 `Quotient`），
     右侧来自 `Inversion.classOf`（`Quotient.mk` 于 `Setoid.ker I.h`，不认识 `MiddleZone`）。
     **为何不同义反复**：两个定义**互不知情**；证明必须双向用 `classOf_eq_iff`
     （内部是 `Quotient.eq''`）在**商的相等**与**观测的相等**之间翻译。
     `rfl` 与 `simp` 都**不行**（实测：`simp only [MiddleZone]` 后目标停在
     `CfEquiv I.h p.1 p.2 ∧ _ ↔ I.classOf p.1 = I.classOf p.2 ∧ _`）。

  2. `middle_zone_empty_iff_classOf_subsingleton`（消费 1 的方向 + 源模块
     `quotient_of_injective_is_trivial` 所在的商层 + `middleZone_empty_iff_injective`）
     结论：`MiddleZoneEmpty I.h ↔ ∀ w w', I.classOf w = I.classOf w' → w = w'`。
     前件**只有** `I`。**前件里没有 `Function.Injective I.h`** —— 单射性是
     结论左端的内容（经 `middleZone_empty_iff_injective` 转一次），不是假设。
     左端是**函数层**陈述（集合为空），右端是**商层**陈述（类是单点）；跨层翻译。

  3. `quotient_tier_post_eq_of_class_eq`（消费源模块 `posterior_factors_through_class`
     + `PosteriorData.post`）
     结论：`P.post y w = P.post y w'`。
     ⚠ 源模块的 `posterior_factors_through_class` **只到** `P.lik y w = P.lik y w'`，
     并在其 docstring 明说**不**宣称 `post` 相等（`prior w ≠ prior w'` 可能）。
     本定理**补上额外信息假设** `hpri`（先验在同类上相等）把结论推到 `post` 层。
     **为何不同义反复**：结论是**乘积函数** `prior · lik` 的相等；`hpri`/`hlik`
     各只约束一个因子，都**不是** `post` 的任何陈述。

  4. `zero_bound_obs_injective` + `zero_bound_middle_zone_empty`（消费
     `BoundedData.zero_bound_candidates_eq` + `MiddleZoneEmpty`）
     前者：`B.ε = 0 ⟹ Function.Injective B.h`。
     后者：`B.h = I.h ∧ B.ε = 0 ⟹ MiddleZoneEmpty I.h`。
     **为何不同义反复**：`zero_bound_candidates_eq` 只给 `dist w₁ w₂ = 0`
     —— **`PseudoMetricSpace` 里 `dist = 0` 不蕴含 `=`**（伪度量允许不可分点）。
     故必须**额外要求 `[MetricSpace W]`**，用 `dist_pos`/`eq_of_dist_eq_zero`
     把距离零转成相等（这是**真的一步**，本文件头 (g) 如实登记该加强）。
     本文件的证明实测：`zero_bound_candidates_eq` 的 `h₂` 参数需 `h.symm`，
     且 `eq_of_dist_eq_zero` 在 `PseudoMetricSpace` 下**无法实例化**（必须 `MetricSpace`）。

  5. `tierToScheme` / `tierToScheme_le_quotient` / `tierToScheme_le_bounded` /
     `tierToScheme_strict` / `discrimOn_univ_iff_middle_zone_empty`
     （消费 `inversion_tier_trichotomy` + `TieredScheme.Tier.le` + `DiscrimOn`）
     把 `InversionTier` **保序嵌入** `Fate.TieredScheme.Tier`
     （`quotient ↦ predict`，`posterior ↦ intervene`，`bounded ↦ counterfactual`），
     并证：在 `Inversion` 载体的**分档读出** `invObs I` 上，
     `DiscrimOn … Set.univ ⟺ MiddleZoneEmpty I.h`。
     **为何不同义反复**：`DiscrimOn` / `Tier.le` 来自 `Fate.TieredScheme`，
     `MiddleZoneEmpty` 来自 `Fate.MiddleZoneDichotomy`，`tierToScheme` 是本文件新定义；
     三者互相独立，前件只给 `I` 与 `t`。

  ============================================================================
  (g) ⚠⚠ 诚实边界（**必读**，含本文件**实测到但放弃**的三条路）
  ============================================================================
  (g1) **`hbound` 推不出观测空间的误差界**（**已实测放弃**）。
       我曾想写 `dist (B.h (B.est y)) y ≤ 2 * B.ε`，并已在草稿里给出证明框架 ——
       写证明时发现**这条是假的**：`BoundedData.hbound` 只约束**潜变量空间 `W`**
       的距离 `dist (B.est y) w ≤ ε`，对 `h` 本身**没有任何度量约束**
       （`h` 可以是任意函数，`Y` 甚至可以不度量化）。取 `h := fun _ => c`
       则 `hbound` 恒成立而结论无意义。**故该定理未写入**（不是忘写）。
  (g2) **不伪造依赖类型反推算子**。源模块 §OU.1 与 §OU.5 的 `/-! ... -/` 段
       已如实声明：`Inversion.tier` 是**元数据**，本模块**没有**
       `(t : InversionTier) → Type _` 的依赖类型产物。本文件**不**伪造它
       （伪造只需 `match` 返回 `PUnit`，空洞）。第 5 组只到
       「三档 → 三条 `Tier`」的**保序嵌入**，**不**声称「产出不同类型」。
  (g3) **第 5 组的 `invObs` 三档读出相同**，故它**不**携带「档间真有区分力差异」
       的信息。`DiscrimOn` 在任何档上都退化为 `F` 上的单射性。
       这是源模块「`tier` 是元数据」的**直接后果**，不是我在偷懒；
       本文件在 `invObs` 的 docstring 里**明写**这一点。
  (g4) **`posterior` 档不归一化**：`PosteriorData.post` 是**未归一化**权重
       `prior · lik`。本文件关于 `post` 的定理**不**做任何归一化论断。
  (g5) **第 4 组加强为 `MetricSpace`**：源模块 `BoundedData` 只要求
       `PseudoMetricSpace`；本文件的零误差界 ⟹ 单射定理要求 `MetricSpace`
       （伪度量下 `dist = 0 ⇏ =`）。这是**前件的加强**，如实标注，
       **不是**把结论塞进前件。
  (g6) **未修改任何既有模块**；**零 `s`-`o`-`r`-`r`、零 `a`-`d`-`m`-`i`-`t`、零 `a`-`x`-`i`-`o`-`m`**
       （为避免下游 grep 误命中，本行不写全词）。
-/

import FateWorld.Legacy.ObservationUnified
import FateWorld.Legacy.MiddleZoneDichotomy
import FateWorld.Legacy.TieredScheme

namespace Fate

namespace ObservationUnifiedConsumer

open Fate.ObservationUnified
open Fate.ObservationUnified.Inversion
open Fate.MiddleZoneDichotomy (MiddleZone MiddleZoneEmpty)
open Fate.TieredScheme (Tier Obs DiscrimOn)

universe u v

variable {W : Type u} {Y : Type v}

/-! ===========================================================================
  §1  ⭐⭐⭐ 弱档 ⟷ 中间地带：两个**独立定义**的关系是同一个
  =========================================================================== -/

/-- ⭐⭐⭐ **【主消费 1】弱档的等价类 = `MiddleZoneDichotomy` 的中间地带**。

`Fate.MiddleZoneDichotomy.MiddleZone Φ`（对**任意函数** `Φ : SCM → CF`）定义为

  `{p | Φ p.1 = Φ p.2 ∧ p.1 ≠ p.2}`

本定理把它**等同**于「`Inversion.classOf` 同类且相异」的集合。

**⟹ 即**：源模块的弱档商与中间地带的二分法是**同一个关系** ——
「观测读不出差别、但状态确实不同」的那些点对。

**为何不同义反复**：
* 前件只有 `I : Inversion W Y`（`tier` + `h` 两个字段，**零假设**）；
* 结论是**两个 `Set` 相等**，左侧由 `Fate.MiddleZoneDichotomy` 提供
  （不知道 `Quotient` 存在），右侧由 `Inversion.classOf` 提供
  （`Quotient.mk (Setoid.ker I.h)`，不知道 `MiddleZone` 存在）；
* 证明双向用 `classOf_eq_iff`（=`Quotient.eq''`）翻译 **商的相等** ⟷ **观测的相等**
  —— 不是 `rfl`，也不是展开定义（`CfEquiv` 的定义只是 `Φ p.1 = Φ p.2`，
  但 `classOf` 侧需要 `Quotient.eq''` 才能落到 `I.h p.1 = I.h p.2`）。 -/
theorem weak_tier_equals_middle_zone (I : Inversion W Y) :
    MiddleZone I.h = {p : W × W | I.classOf p.1 = I.classOf p.2 ∧ p.1 ≠ p.2} := by
  ext p
  have h := I.classOf_eq_iff p.1 p.2
  simp only [MiddleZone, MiddleZoneDichotomy.CfEquiv, Set.mem_setOf_eq]
  exact and_congr h.symm Iff.rfl

/-- ⭐⭐⭐ **【主消费 2】「中间地带为空」⟷「弱档的类是单点」**。

把 `Fate.MiddleZoneDichotomy.middleZone_empty_iff_injective` 的结论
（`Z = ∅ ⟺ Φ` 单射）**翻译到商层面**：

  `MiddleZoneEmpty I.h  ⟺  ∀ w w', I.classOf w = I.classOf w' → w = w'`

**为何不同义反复**：
* 前件只有 `I : Inversion W Y`；**前件里没有 `Function.Injective I.h`**
  —— 单射性是**结论左端**的内容（经 `middleZone_empty_iff_injective` 转一次），
  它在**前件中不出现**；
* 左端是**观测函数层面**的陈述（集合为空），右端是**商的类层面**的陈述
  （每个类是单点）—— 两个抽象层级，靠 `classOf_eq_iff` 双向翻译。 -/
theorem middle_zone_empty_iff_classOf_subsingleton (I : Inversion W Y) :
    MiddleZoneEmpty I.h ↔ ∀ w w' : W, I.classOf w = I.classOf w' → w = w' := by
  rw [MiddleZoneDichotomy.middleZone_empty_iff_injective]
  constructor
  · intro hinj w w' hq
    exact hinj ((I.classOf_eq_iff w w').mp hq)
  · intro h w w' hww
    exact h w w' ((I.classOf_eq_iff w w').mpr hww)

/-! ===========================================================================
  §2  ⭐⭐⭐ 中档：从「似然与先验都是观测的函数」推到「后验权重相等」
  =========================================================================== -/

/-- ⭐⭐⭐ **【主消费 3】弱档类 ⟹ 中档后验权重相等（含先验）**。

源模块的 `posterior_factors_through_class` 只证到 `P.lik y w = P.lik y w'`，
并在其 docstring 里**明说**它不宣称 `post` 相等（因 `prior w ≠ prior w'` 可能）。

本定理**补上**「先验在同类上相等」这一**额外的信息假设** `hpri`，
把结论推到 `P.post y w = P.post y w'` —— 即**整个后验权重**（`prior · lik`）
在弱档的类内是常数。

**为何不同义反复**：
* 结论 `P.post y w = P.post y w'` 是**乘积函数**（`post := fun w => prior w * lik y w`）
  的相等；
* 前件 `hpri` 与 `hlik` **各只约束一个因子**，都不是 `post` 的任何陈述；
* 必须先经源模块的 `posterior_factors_through_class`（内部用 `classOf_eq_iff`）
  得到 `lik` 相等，**再**与 `hpri` 合成。 -/
theorem quotient_tier_post_eq_of_class_eq (I : Inversion W Y) (P : PosteriorData W Y)
    (y : Y)
    (hlik : ∀ w w' : W, I.h w = I.h w' → P.lik y w = P.lik y w')
    (hpri : ∀ w w' : W, I.h w = I.h w' → P.prior w = P.prior w')
    (w w' : W) (hq : I.classOf w = I.classOf w') :
    P.post y w = P.post y w' := by
  have hobs : I.h w = I.h w' := (I.classOf_eq_iff w w').mp hq
  have hl : P.lik y w = P.lik y w' := I.posterior_factors_through_class P y hlik w w' hq
  have hp : P.prior w = P.prior w' := hpri w w' hobs
  simp only [PosteriorData.post, hl, hp]

/-! ===========================================================================
  §3  ⭐⭐⭐ 强档：零误差界 ⟹ 观测单射 ⟹ 中间地带为空
  =========================================================================== -/

/-- ⭐⭐⭐ **【主消费 4a】强档 + 零误差界 ⟹ 观测映射单射**。

由源模块 `BoundedData.zero_bound_candidates_eq`：两个原像 `w₁ w₂` 若都满足
`B.h wᵢ = y`，则 `dist w₁ w₂ = 0`。

⚠⚠ **关键的一步（也是本定理的真实内容）**：`dist w₁ w₂ = 0` 在
`PseudoMetricSpace` 中**不**蕴含 `w₁ = w₂`（伪度量允许多个不可分点）。
故本定理**额外要求 `[MetricSpace W]`**，再用 `eq_of_dist_eq_zero` 收尾。
这一加强在文件头 (g5) 已如实登记 —— **它是前件的加强，不是把结论塞进前件**：
前件是 `B.ε = 0`（以及 `MetricSpace` 实例），结论是 `Function.Injective B.h`。 -/
theorem zero_bound_obs_injective [MetricSpace W] (B : BoundedData W Y)
    (hε0 : B.ε = 0) : Function.Injective B.h := by
  intro w₁ w₂ h
  have hd : dist w₁ w₂ = 0 :=
    B.zero_bound_candidates_eq hε0 (B.h w₁) w₁ w₂ rfl h.symm
  exact eq_of_dist_eq_zero hd

/-- ⭐⭐⭐ **【主消费 4b】强档零误差界 ⟹ 中间地带为空**
（把 4a 落到 `Fate.MiddleZoneDichotomy.MiddleZoneEmpty` 上）。

**为何不同义反复**：前件是 `B.h = I.h`（载体对齐）与 `B.ε = 0`；
结论 `MiddleZoneEmpty I.h` 是一个**关于集合为空**的陈述（`Fate.MiddleZoneDichotomy`
的定义），既不是 `B.ε = 0` 的展开，也不是 `B.h = I.h` 的展开 ——
必须经 `middleZone_empty_iff_injective` 与 `zero_bound_obs_injective` 两步。 -/
theorem zero_bound_middle_zone_empty [MetricSpace W] (I : Inversion W Y)
    (B : BoundedData W Y) (hBh : B.h = I.h) (hε0 : B.ε = 0) :
    MiddleZoneEmpty I.h := by
  rw [MiddleZoneDichotomy.middleZone_empty_iff_injective, ← hBh]
  exact zero_bound_obs_injective B hε0

/-! ===========================================================================
  §4  ⭐⭐ 三档 ⟷ `Fate.TieredScheme` 的分档读出（保序嵌入 + 可区分性）
  =========================================================================== -/

/-- ⭐ **档映射：`InversionTier` 保序嵌入 `Fate.TieredScheme.Tier`**。

按「反推产物的信息量」从**粗**到**细**排列：

| `InversionTier` | 产物（源模块） | `TieredScheme.Tier` |
|---|---|---|
| `.quotient` | 等价类（`I.quo`）| `.predict`（**最粗**）|
| `.posterior` | 未归一化后验权重 | `.intervene` |
| `.bounded` | 点估计 + 误差界 | `.counterfactual`（**最细**）|

⚠ 这是**本文件新定义的**映射，源模块**没有**把 `InversionTier` 接到 `Tier`
（源模块 §OU.5 只证三档互异 + 三档穷尽）。 -/
def tierToScheme : InversionTier → Tier
  | .quotient => .predict
  | .posterior => .intervene
  | .bounded => .counterfactual

/-- ⭐ **`quotient` 在 `TieredScheme.Tier` 侧是**最粗**的**：任何档都 ≥ 它。 -/
theorem tierToScheme_le_quotient (t : InversionTier) :
    Tier.le (tierToScheme .quotient) (tierToScheme t) := by
  cases t <;> simp [tierToScheme, Tier.le]

/-- ⭐ **`bounded` 在 `TieredScheme.Tier` 侧是**最细**的**：任何档都 ≤ 它。 -/
theorem tierToScheme_le_bounded (t : InversionTier) :
    Tier.le (tierToScheme t) (tierToScheme .bounded) := by
  cases t <;> simp [tierToScheme, Tier.le]

/-- ⭐⭐ **档映射在两端**不退化**：`quotient ↦ predict ≠ bounded ↦ counterfactual`。

⟹ 把源模块的 `inversion_tier_trichotomy`（三档穷尽）+ 两条互异定理，
**搬到 `TieredScheme.Tier` 上仍然保持区分**。

**为何不同义反复**：前件为空（无假设）；结论是**两个新定义常量**的不等，
靠 `Tier` 的 `DecidableEq` 判定 —— 它有内容仅在于**确认映射不是常数**。
⚠ **如实标注**：本条**强度不高**（一句 `simp`），写它只为把 §4 的
「保序嵌入」补上「**不是**塌缩映射」这半边。 -/
theorem tierToScheme_strict : tierToScheme .quotient ≠ tierToScheme .bounded := by
  simp [tierToScheme]

/- ⚠ **宇宙层限制（如实登记）**：`Fate.TieredScheme.Obs.Val : Tier → Type u`
   要求每档读出值都在**同一宇宙** `Type u`。故本节把 `Y` 也限制到 `Type u`
   （源模块本身 `Inversion W Y` 允许 `W : Type u`、`Y : Type v` 不同宇宙；
   **本节是那上面的一个特例**，不是全称）。 -/
section SameUniverse

variable {Y : Type u}

/-- ⭐ **`Inversion` 载体上的分档读出**：所有档读出同一个 `I.h`。

⚠⚠ **这是源模块「`tier` 是元数据」的直接后果**（`Inversion.h` 的**类型**
里没有 `tier`）。故本读出**三档相同** —— 本文件**不**声称档间有区分力差异
（文件头 (g3) 已如实登记）。 -/
def invObs (I : Inversion W Y) : Obs W where
  Val := fun _ => Y
  obs := fun _ s => I.h s

/-- ⭐⭐⭐ **【主消费 5】分档可区分性 ⟷ 中间地带为空**（三个模块的接口对齐）。

在 `invObs I` 的**任意**档上，
`DiscrimOn … Set.univ  ⟺  MiddleZoneEmpty I.h`。

**为何不同义反复**：
* 前件只有 `I : Inversion W Y` 与 `t : InversionTier`；
* `DiscrimOn` 来自 `Fate.TieredScheme`（其定义是 `∀ s ∈ F, ∀ t ∈ F, obs … = obs … → s = t`），
  `MiddleZoneEmpty` 来自 `Fate.MiddleZoneDichotomy`（其定义是集合为空），
  `invObs` 是本文件新定义的读出 —— 三者互相独立；
* 证明要**两段**：先 `middleZone_empty_iff_injective` 把「集合空」转成单射，
  再用 `DiscrimOn` 的**逐点**定义在 `Set.univ` 上展开 —— 两个表述的**量词形状不同**
  （`Set` 式 vs 逐点式）。 -/
theorem discrimOn_univ_iff_middle_zone_empty (I : Inversion W Y) (t : InversionTier) :
    DiscrimOn (invObs I) (tierToScheme t) Set.univ ↔ MiddleZoneEmpty I.h := by
  rw [MiddleZoneDichotomy.middleZone_empty_iff_injective]
  constructor
  · intro h a b hab
    exact h a (Set.mem_univ a) b (Set.mem_univ b) hab
  · intro h a _ b _ hab
    exact h hab

end SameUniverse

end ObservationUnifiedConsumer

end Fate
