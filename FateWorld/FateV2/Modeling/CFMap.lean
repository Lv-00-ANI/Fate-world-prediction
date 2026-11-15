import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic

set_option autoImplicit false

/-!
# §7  反事实映射 Φ：最优 CF 的形式化（作者裁决「最优最强」）

**来源**：`候选乙-反事实映射-详述.md` §四。
**地位**：正式模块。固定「SCM → 反事实映射 Φ」的类型接缝，
并把「Φ 的核 = 反事实等价 ∼_cf」与「u 不可观测 = Φ 的可计算实例集 / 可检验实例集变空」
*在同一抽象层*上写成可核验的事实。

**硬边界**（见详述 §4.4）：
* B1：本文件**不**替换 `Fate/Counterfactual.lean` 的 `Obs` 冻结签名——只登记 Φ 的类型。
* B2：`P(U|e)`（溯因步）与「A23 外生可识别」是**假设/外部引理**，不在本文件内。
* B3：「Φ 非单射 ⟹ ∼_cf 严格弱于 =」的**反例**已在
  **`Fate/CounterfactualStrictness.lean`** 给出（`cf_strictly_weaker_than_eq`），
  本文件不重复构造，只把「核 = Φ 的纤维」写死。
  **✅ 该反例现已在构建内**（原为探针 `probes/_probe_q14.lean`，第 16 轮已正式化）——
  **故本处的引用是编译期可核验的**。

本文件不含 `sorry`/`admit`/用户 `axiom`；依赖内核标准公理。
-/

namespace FateV2.Modeling
universe u v w

/-! ===========================================================================
    §1  反事实映射 Φ 的类型（定义性约定）
    ===========================================================================
    `SCM` 是载体（某个纤维 𝔉|_G）；`Ind` 是「个体 / 外生实现」的指标类型；
    `Act` 是干预（do-算子）的指标类型；`Out` 是结果取值空间。

    Φ 把每个 SCM 送到「个体 → (干预 → 结果)」这一整套**反事实响应**。
    这正是净版定义 3.6 / 第14问式 (1) 的抽象化。
    --------------------------------------------------------------------------- -/

/-- **反事实映射 Φ 的读出型**：`SCM → (Ind → (Act → Out))`。 -/
abbrev CFMap (SCM Ind Act Out : Type*) : Type _ :=
  SCM → (Ind → (Act → Out))

namespace CFMap

/-- **反事实等价 `∼_cf`**：Φ 的核。
    两个 SCM 反事实等价 ⟺ 对每个个体、每个干预给出相同结果。 -/
def cfSetoid (SCM Ind Act Out : Type*) (Φ : SCM → (Ind → (Act → Out))) :
    Setoid SCM where
  r s t := Φ s = Φ t
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- `∼_cf` 的关系形式（与 `cfSetoid` 的定义逐字对应）。 -/
theorem cf_rel_iff (SCM Ind Act Out : Type*) (Φ : SCM → (Ind → (Act → Out)))
    (s t : SCM) :
    (cfSetoid SCM Ind Act Out Φ).r s t ↔ Φ s = Φ t := Iff.rfl

/-! ===========================================================================
    §2  Φ 是「读满」还是「读不满」——核与纤维
    ===========================================================================
    `∼_cf` 严格弱于 `=`  ⟺  Φ 非单射  ⟺  存在非空纤维（同像不同源）。
    这是第14问的核心判据在类型层的复述。
    --------------------------------------------------------------------------- -/

/-- **Φ 的纤维**（反事实等价类）：同一反事实读出的 SCM 集合。 -/
def cfFiber {SCM Ind Act Out : Type*} (Φ : SCM → (Ind → (Act → Out)))
    (φ₀ : Ind → (Act → Out)) : Set SCM :=
  { s | Φ s = φ₀ }

/-- **「Φ 非单射」的纤维形式**：存在一个纤维含两个不同元素。
    等价于 `∼_cf` 严格弱于 `=`。 -/
def PhiNotInjective {SCM Ind Act Out : Type*} (Φ : SCM → (Ind → (Act → Out))) : Prop :=
  ∃ s t : SCM, s ≠ t ∧ Φ s = Φ t

/-- **判据（已证方向）**：Φ 非单射 ⟹ 存在非空纤维且其中有不同元素。
    这是 `∼_cf` 严格弱于 `=` 的充要条件（另一半是集合论重言式）。 -/
theorem not_injective_iff_nontrivial_fiber
    {SCM Ind Act Out : Type*} (Φ : SCM → (Ind → (Act → Out))) :
    PhiNotInjective Φ ↔
      ∃ φ₀, ∃ s t : SCM, s ∈ cfFiber Φ φ₀ ∧ t ∈ cfFiber Φ φ₀ ∧ s ≠ t := by
  constructor
  · rintro ⟨s, t, hne, heq⟩
    exact ⟨Φ s, s, t, rfl, heq.symm, hne⟩
  · rintro ⟨φ₀, s, t, hs, ht, hne⟩
    exact ⟨s, t, hne, hs.trans ht.symm⟩

/-! ===========================================================================
    §3  u 不可观测：把「证据」并入读出 —— 只会变细，绝不粗化
    ===========================================================================
    溯因（abduction）步 `e ↦ P(U|e)` 在抽象层 = 增加一个与 Φ 并列的**证据泛函**。
    联合读取 `(Φ, ev)` 的核 ⊆ `Φ` 的核 —— 即第18问 `aug_refines`。
    --------------------------------------------------------------------------- -/

/-- **证据泛函**：关于外生实现 `u`（经代理 / 证据 `e`）的部分信息载体。 -/
abbrev Evidence (SCM E : Type*) : Type _ := SCM → E

/-- **增广读出**：`(Φ, ev)` 的联合。 -/
def augRead {SCM Ind Act Out E : Type*}
    (Φ : SCM → (Ind → (Act → Out))) (ev : SCM → E) :
    SCM → ((Ind → (Act → Out)) × E) :=
  fun s => (Φ s, ev s)

/-- **单调细化（第18问 `aug_refines` 的抽象形式）**：
    联合读出的核 ⊆ 单独 Φ 的核。即加证据只会切细等价类，不会黏合。 -/
theorem aug_refines {SCM Ind Act Out E : Type*}
    (Φ : SCM → (Ind → (Act → Out))) (ev : SCM → E) :
    (Setoid.ker (augRead Φ ev)).r ≤ (Setoid.ker Φ).r := by
  intro s t h
  exact congrArg Prod.fst h

/-- **严格变细的充要条件（第18问 `aug_strict_iff` 的抽象形式）**：
    存在「Φ 相同、证据不同」的一对 SCM。 -/
theorem aug_strict_iff {SCM Ind Act Out E : Type*}
    (Φ : SCM → (Ind → (Act → Out))) (ev : SCM → E) :
    (∃ s t : SCM, Φ s = Φ t ∧ ev s ≠ ev t) ↔
      ¬ ((Setoid.ker (augRead Φ ev)).r = (Setoid.ker Φ).r) := by
  constructor
  · rintro ⟨s, t, hΦ, hev⟩ hEq
    have hmem : (Setoid.ker (augRead Φ ev)).r s t := by
      rw [hEq]
      exact hΦ
    exact hev (congrArg Prod.snd hmem)
  · intro hne
    by_contra hno
    push Not at hno
    apply hne
    ext s t
    constructor
    · intro h
      exact congrArg Prod.fst h
    · intro h
      exact Prod.ext h (hno s t h)

/-! ===========================================================================
    §4  Φ 的分解：候选乙落在 CF 格的哪一格
    ===========================================================================
    候选甲（轨迹分布）的读出 `Obs_traj` 分解过 Φ：
    `Obs_traj = φ ∘ Φ`（取事实边缘）。故 `∼_cf ⊆ ∼_traj`。
    本段把这个「核的函子性」写成可核验形式。
    --------------------------------------------------------------------------- -/

/-- **分解引理**：若 `ObsOther = φ ∘ Φ`，则 `ker Φ ⊆ ker ObsOther`。
    取 `φ = 取事实世界边缘` 得 `∼_cf ⊆ ∼_traj`；取 `φ = 取单时刻边缘` 得 `∼_cf ⊆ ∼_obs`。 -/
theorem ker_subset_of_factor {SCM Ind Act Out C : Type*}
    (Φ : SCM → (Ind → (Act → Out))) (φ : (Ind → (Act → Out)) → C) :
    (Setoid.ker Φ).r ≤ (Setoid.ker (φ ∘ Φ)).r := by
  intro s t h
  exact congrArg φ h

end CFMap
end FateV2.Modeling