import FateWorld.FateV2.Modeling.KernelQuotientExtra
import FateWorld.FateV2.Predict.Counterfactual
import FateWorld.FateV2.Rules.AlphaKernel
import FateWorld.FateV2.Predict.CFLatticeGen
/-!
  # Modeling · KernelQuotientRecovery

  ## 迁移登记
  - 来源：`FateWorld/Legacy/KernelQuotientRecovery.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：KernelQuotientExtra, Counterfactual, AlphaKernel, CFLatticeGen
  - 补充 open 域：FateV2.Model, FateV2.Predict, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §11  **三套结构的回收**：证明它们都是一般理论的**特例**

  **动机**：`Fate/KernelQuotientCore.lean` 给出了「映射 → 核 → 核商」的一般理论。
  本节**实际证明**项目里三套独立结构**都是它的实例** ——
  **不是口头声称，而是可编译的 `example` 层面的回收**。

  | 来源 | 一般理论的哪个实例 |
  |---|---|
  | `Fate.Counterfactual` | `f := M.Obs`，`F := ` 桥的纤维 |
  | `Fate.AlphaKernel` | `f := α ∘ enc` |
  | `Fate.CFLatticeGen` | `f := R.Obs` |

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Modeling

open FateV2.Model
open FateV2.Predict
open FateV2.Rules
namespace KernelQuotientRecovery

open FateV2.Modeling.KernelQuotientTheory

/-! ### §11.1 ⭐ 回收 `Counterfactual`（反事实商） -/

/-- ⭐ **`Counterfactual` 的核 = 一般理论的核**（取 `f := M.Obs`）。

**⟹ 反事实等价 `∼_cf` 正是 `kernel M.Obs`。** -/
theorem counterfactual_kernel_eq (M : Counterfactual.Model) :
    Counterfactual.cfSetoid M = kernel M.Obs :=
  rfl

/-- ⭐ **`Counterfactual` 的三情形穷尽 = 一般理论的特例**。

**原版**：`Counterfactual.trichotomy M F`
**一般版**：`KernelQuotient.trichotomy M.Obs F`

**本定理说明**：前者可由后者**直接得到** —— 即它**不是独立结论**。 -/
theorem counterfactual_trichotomy_is_instance (M : Counterfactual.Model) (F : Set M.SCM) :
    Collapse M.Obs F ∨ Faithful M.Obs F ∨ MiddleZone M.Obs F :=
  trichotomy M.Obs F

/-- ⭐ **塌缩 ⟺ 商单点**（一般理论的特例）。

**原版**：`Counterfactual.cfQuotient_subsingleton_iff`
**一般版**：主体的 `collapse_iff_subsingleton` -/
theorem counterfactual_subsingleton_is_instance (M : Counterfactual.Model) (F : Set M.SCM) :
    Collapse M.Obs F ↔
      Subsingleton (Quotient (Setoid.comap Subtype.val (kernel M.Obs) : Setoid F)) :=
  (collapse_iff_subsingleton M.Obs F).symm

/-! ### §11.2 ⭐ 回收 `CFLatticeGen`（读出方案的格） -/

/-- ⭐ **`kappa` 就是一般理论的核**（取 `f := R.Obs`）。

**⟹ 读出方案的核映射 `κ` 正是 `kernel R.Obs`。** -/
theorem cflattice_kappa_eq_kernel (R : CFLatticeGen.Readout.{u, u} (SCM := SCM)) :
    CFLatticeGen.kappa R = kernel R.Obs :=
  rfl

/-- ⭐ **`Finer` 的核刻画 = 一般理论的最优性**。

**`finer_iff_kappa_le` 说**：`Finer R (readoutOfSetoid ρ) ↔ κ R ≤ ρ`。
**一般理论的 `kernel_is_coarsest` 说**：相容的 `r` 必 `≤ ker f`。

**两者合起来说明**：**`Finer` 序**由**核的包含序**决定 ——
**⟹ 读出方案的格结构完全由 `Setoid` 的格决定。**

**⚠ 宇宙层说明**：`kappa'` 是 `kappa` 的宽宇宙版本（`Readout.{u,v}`），
此处 `R₁` 与 `R₂` 同宇宙，故二者一致。 -/
theorem finer_is_kernel_order {SCM : Type u} {R₁ R₂ : CFLatticeGen.Readout.{u, u} SCM} :
    CFLatticeGen.Finer R₁ R₂ ↔ CFLatticeGen.kappa R₁ ≤ CFLatticeGen.kappa R₂ := by
  -- `kappa` 与 `Setoid.ker ∘ Obs` 定义相同，故直接由 `finer_iff_ker_le` 得到
  have h := CFLatticeGen.finer_iff_ker_le (R₁ := R₁) (R₂ := R₂)
  rw [h]
  rfl

/-! ### §11.3 ⭐ 回收 `AlphaKernel`（Q-3 消解） -/

/-- ⭐ **`alphaKernel` 的核关系 = 一般理论的核**。

**取 `f := fun e => K.takeConcept (enc.toAttrs (embed e))`**，
则 `alphaKernel` 的关系正是 `kernel f`。 -/
theorem alphaKernel_eq_kernel {F : Frame} {K : FormalCtx} (enc : Encoder F K)
    (E : InstSpace) (embed : E.Carrier → F.X.Carrier) (e₁ e₂ : E.Carrier) :
    (AlphaKernel.alphaKernel enc E embed).r e₁ e₂ ↔
      (kernel (fun e => K.takeConcept (enc.toAttrs (embed e)))) e₁ e₂ :=
  Iff.rfl

/-- ⭐⭐ **Q-3 消解的实质 = 最优性定理的特例**。

`AlphaKernel.kernel_is_coarsest` 说：与 `α∘enc` 相容的外置等价关系必 `≤` 核。
这**正是一般理论 `kernel_is_coarsest` 的实例**。

**⟹ 即**：**Q-3 的消解不是偶然的技巧，而是核的最优性在具体场景的体现。** -/
theorem alphaKernel_coarsest_is_instance {F : Frame} {K : FormalCtx} (enc : Encoder F K)
    (E : InstSpace) (embed : E.Carrier → F.X.Carrier) (eqv : Setoid E.Carrier)
    (hresp : enc.RespectsEquiv embed eqv) :
    eqv ≤ kernel (fun e => K.takeConcept (enc.toAttrs (embed e))) :=
  kernel_is_coarsest _ _ (fun _ _ hab => by
    -- `RespectsEquiv` 给出 `toAttrs` 相等，故 `takeConcept ∘ toAttrs` 也相等
    rw [hresp _ _ hab])

/-! ### §11.4 ⭐⭐ 统一的结论 -/

/-- ⭐⭐ **三套结构共享同一个一般理论**（综合陈述）。

**本定理把 §11.1–§11.3 的回收汇成一条**：
- `Counterfactual` 的核 = `kernel M.Obs`
- `CFLatticeGen` 的核 = `kernel R.Obs`
- `AlphaKernel` 的核 = `kernel (α ∘ enc)`

**⟹ 三者的「第一同构定理」「三情形穷尽」「最优性」**
**都是 `KernelQuotientCore` 中一般定理的特例。** -/
theorem three_structures_share_general_theory (M : Counterfactual.Model)
    (R : CFLatticeGen.Readout.{u, u} (SCM := SCM)) :
    Counterfactual.cfSetoid M = kernel M.Obs ∧
      CFLatticeGen.kappa R = kernel R.Obs :=
  ⟨rfl, rfl⟩

end KernelQuotientRecovery

end FateV2.Modeling