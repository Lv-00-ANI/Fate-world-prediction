import FateWorld.FateV2.Modeling.KernelQuotientExtra
import FateWorld.FateV2.Predict.CFLatticeGen
/-!
  # Predict · KernelAdjunction

  ## 迁移登记
  - 来源：`FateWorld/Legacy/KernelAdjunction.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：KernelQuotientExtra, CFLatticeGen
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §14  **核映射的伴随结构**：读出格与 setoid 格的精确对应

  **动机**：`KernelQuotientRecovery` 已证「读出序由核序决定」——
  本节深化为「伴随结构」，并把它定位为统一理论的一层。

  **⚠ 命名说明**：本文件用**主体 `KernelQuotientTheory` 的 API**
  （`kernel` / `kernel_is_coarsest` 等），
  **不引入新的同名概念**（如 `Compatible`）—— 主体的定理直接用
  「`∀ a b, r a b → f a = f b`」的原始谓词形式，本节沿用之。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Predict
namespace KernelAdjunction

open FateV2.Modeling.KernelQuotientTheory

universe u v

/-! ### §14.1 ⭐ 核的基本性质（用主体的 API） -/

/-- ⭐ **核自身相容**：核当然使 `f` 能下降。

**与主体 §10.5 的 `kernel_is_coarsest` 配合**，
给出完整的「核 = 相容关系的**最大**元」。 -/
theorem kernel_self_compatible {A : Type u} {B : Type v} (f : A → B) :
    ∀ a b, kernel f a b → f a = f b :=
  fun _ _ h => h

/-- ⭐⭐ **核是最大的相容等价关系**（最优性的格论形式）。

**陈述**：核自身相容，**且**任何相容的 `r` 都 ≤ 核。

**一般化了 `AlphaKernel.kernel_is_coarsest` 的最优性内容** ——
它把「核是最粗的相容关系」这一断言拆成**两条**并同时给出。 -/
theorem kernel_is_greatest_compatible {A : Type u} {B : Type v} (f : A → B) :
    (∀ a b, kernel f a b → f a = f b) ∧
      ∀ r : Setoid A, (∀ a b, r a b → f a = f b) → r ≤ kernel f :=
  ⟨kernel_self_compatible f, fun _ h => kernel_is_coarsest f _ h⟩

/-! ### §14.2 ⭐ 核与复合 -/

/-- ⭐ **复合只会使核变粗**：`ker f ≤ ker (g ∘ f)`。

**即**：`g` 可能把 `f` 已区分的点再合并 —— **故复合不增信息**。 -/
theorem kernel_le_kernel_comp {A : Type u} {B : Type v} {f : A → B} {g : B → A} :
    kernel f ≤ kernel (g ∘ f) :=
  fun _ _ hab => congrArg g hab

/-- ⭐ **外延相等 ⟹ 核相同**（核是 `f` 的**外延量**）。 -/
theorem kernel_congr {A : Type u} {B : Type v} {f g : A → B} (h : ∀ a, f a = g a) :
    kernel f = kernel g := by
  ext a b
  simp only [Setoid.ker_def]
  rw [h a, h b]

/-! ### §14.3 ⭐⭐ 读出格与 setoid 格的对应 -/

/-- ⭐⭐ **读出序 ⟺ 核序**（`KernelQuotientRecovery` 的深化）。

**陈述**：`Finer R₁ R₂` 精确对应 `ker R₁.Obs ≤ ker R₂.Obs`。

**⟹ 即**：**读出方案的序完全由核的序决定** ——
这解释了为何 `CFLatticeGen` 能证明「`Readout` 是完备格」：
**因为完备性是从 `Setoid` 的完备格经核映射继承的**。 -/
theorem readout_order_reflects_kernel_order
    {SCM : Type u} {R₁ R₂ : CFLatticeGen.Readout.{u, u} SCM} :
    CFLatticeGen.Finer R₁ R₂ ↔ kernel R₁.Obs ≤ kernel R₂.Obs :=
  CFLatticeGen.finer_iff_ker_le

/-- ⭐⭐ **核相等 ⟺ 互相 Finer**（核是读出的**完全序不变量**）。 -/
theorem kernel_eq_iff_finer_both {SCM : Type u}
    {R₁ R₂ : CFLatticeGen.Readout.{u, u} SCM} :
    kernel R₁.Obs = kernel R₂.Obs ↔
      (CFLatticeGen.Finer R₁ R₂ ∧ CFLatticeGen.Finer R₂ R₁) := by
  constructor
  · intro h
    exact ⟨(CFLatticeGen.finer_iff_ker_le (R₁ := R₁) (R₂ := R₂)).mpr h.le,
           (CFLatticeGen.finer_iff_ker_le (R₁ := R₂) (R₂ := R₁)).mpr h.ge⟩
  · intro ⟨h₁, h₂⟩
    exact le_antisymm
      ((CFLatticeGen.finer_iff_ker_le (R₁ := R₁) (R₂ := R₂)).mp h₁)
      ((CFLatticeGen.finer_iff_ker_le (R₁ := R₂) (R₂ := R₁)).mp h₂)

/-! ### §14.4 ⭐⭐ 综合：统一理论的三层结构 -/

/-- ⭐⭐ **统一理论的三层**（综合陈述）。

**第一层（一般）**：`kernel` / `descend` / `descend_injective`
**第二层（最优性）**：`kernel_is_greatest_compatible`
**第三层（应用）**：`readout_order_reflects_kernel_order`

**本定理把三层串起来**：
**核的最优性在读出方案上给出序对应。** -/
theorem general_theory_three_layers
    {SCM : Type u} {R₁ R₂ : CFLatticeGen.Readout.{u, u} SCM} :
    (∀ (A : Type u) (B : Type u) (f : A → B),
        (∀ a b, kernel f a b → f a = f b) ∧
          ∀ r : Setoid A, (∀ a b, r a b → f a = f b) → r ≤ kernel f) ∧
      (CFLatticeGen.Finer R₁ R₂ ↔ kernel R₁.Obs ≤ kernel R₂.Obs) :=
  ⟨fun _ _ f => kernel_is_greatest_compatible f, readout_order_reflects_kernel_order⟩

end KernelAdjunction

end FateV2.Predict