/-
  FateV2.Rules.AlphaKernelAudit
  =====================

  **审计问题**：`α` 是否保持了抽象等价（`AlphaKernel` 里的核）？给出条件与证明。

  ---------------------------------------------------------------------------
  结论（一句话）
  ---------------------------------------------------------------------------
  **是，且无条件**（`rfl` 级，零公理）。
  但**"保持"有两种含义，必须分清**：

  | 问法 | 答案 | 定理 | 前件 |
  |---|---|---|---|
  | α 是否**在核上良定义**（保核本身）？ | **是，无条件** | `alpha_respects_kernel` | **无** |
  | α 是否保**外置**等价 `∼_E`（`RespectsEquiv`）？ | 是，**有前件** | `alpha_respects_equiv` | `enc.RespectsEquiv embed eqv` |
  | 两者关系 | `∼_E ⊆ ker α`，**严格** | `equiv_le_kernel` + `kernel_strictly_coarser` | — |

  ---------------------------------------------------------------------------
  条件的精确内容
  ---------------------------------------------------------------------------
  设 `enc : Encoder F K`，`embed : E.Carrier → F.X.Carrier`。

  * **核**（`AlphaKernel.alphaKernel`，内生，无参数）：
    e₁ ≈ e₂  :⟺  takeConcept (toAttrs (embed e₁)) = takeConcept (toAttrs (embed e₂))

  * **外置等价 + 相容性**（`Alpha.Encoder.RespectsEquiv`，外置参数）：
    enc.RespectsEquiv embed eqv  :⟺  ∀ e₁ e₂, e₁ ≈ e₂ → toAttrs (embed e₁) = toAttrs (embed e₂)

  **关键**：`RespectsEquiv` 要求**编码层**（`toAttrs`）相等，
  比核的**抽象层**（`toAttrs` 再取 `takeConcept`）相等**更强**。

  ---------------------------------------------------------------------------
  证明速写
  ---------------------------------------------------------------------------
  1. `alpha_respects_kernel`：核的定义就是 `takeConcept ∘ toAttrs ∘ embed` 的相等，
     故"保持"是**定义的重言**（证明项即 `fun _ _ h => h`）。∎

  2. `alpha_respects_equiv`：由 `RespectsEquiv` 得 `toAttrs(embed e₁) = toAttrs(embed e₂)`，
     两边同取 `takeConcept`（`rw`）。∎

  3. `equiv_le_kernel`：`e₁ ≈ e₂ ⟹ toAttrs 相等（hresp）⟹ takeConcept 相等（rw）`。∎

  4. `kernel_strictly_coarser`：见下方反例，证明一般地 `RespectsEquiv ⇏` 核相容的逆。∎

  ---------------------------------------------------------------------------
  反例（核**严格**更粗）
  ---------------------------------------------------------------------------
  形式背景 `GFCA = Unit, MFCA = Unit, Irel ≡ False`，`X = Bool`，
  编码 `toAttrs true = ∅`，`toAttrs false = univ`，`eqv = ⊤`。
  则 `RespectsEquiv` 要求 `toAttrs` 在 `Bool` 上恒定 —— 但 `∅ ≠ univ`，
  故 `¬ RespectsEquiv`。**⟹ 旧版前件并非自动成立**，
  这正是 `AlphaKernel` 版把它**消解为定理**的实质所得。
-/

import FateWorld.FateV2.Rules.AlphaKernel
open FateV2.Rules.AlphaKernel FateV2.Rules.FormalCtx

namespace FateV2.Rules.AlphaKernel

open FateV2.Model

variable {F : Frame} {K : FormalCtx.{u,v}}

/-!
  # Rules · AlphaKernelAudit

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaKernelAudit.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：AlphaKernel
  - 补充 open 域：FateV2.Model
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1  核的定义性刻画（双向，`rfl`） -/

/-- 核关系 ⟺ `takeConcept ∘ toAttrs ∘ embed` 取值相等。 -/
theorem kernel_iff (enc : Encoder F K) (E : InstSpace) (embed : E.Carrier → F.X.Carrier)
    (e₁ e₂ : E.Carrier) :
    (alphaKernel enc E embed).r e₁ e₂ ↔
      K.takeConcept (enc.toAttrs (embed e₁)) = K.takeConcept (enc.toAttrs (embed e₂)) :=
  Iff.rfl

/-! ## §2  α 在核商上的取值（点态交换图，`rfl`） -/

/-- `alphaOnKernelQuotient` 在代表元上的值就是 `takeConcept ∘ toAttrs ∘ embed`。 -/
theorem alphaOnKernelQuotient_mk (enc : Encoder F K) (E : InstSpace)
    (embed : E.Carrier → F.X.Carrier) (e : E.Carrier) :
    alphaOnKernelQuotient enc E embed (Quotient.mk (alphaKernel enc E embed) e)
      = K.takeConcept (enc.toAttrs (embed e)) := rfl

/-! ## §3  条件的精确形式：相容 ⟹ 外置 ⊆ 核（**单侧**） -/

/-- `RespectsEquiv` 蕴含"外置等价 ⊆ 核"。注意方向：**只有 `→`**。 -/
theorem respectsEquiv_imp_le_kernel (enc : Encoder F K) (E : InstSpace)
    (embed : E.Carrier → F.X.Carrier) (eqv : Setoid E.Carrier) :
    enc.RespectsEquiv embed eqv →
      ∀ e₁ e₂ : E.Carrier, eqv.r e₁ e₂ → (alphaKernel enc E embed).r e₁ e₂ :=
  equiv_le_kernel enc E embed eqv

/-! ## §4  §3 的逆**不成立**：反例

以下构造一个编码算子，使 `eqv = ⊤` 时 `RespectsEquiv` 为假 ——
即"外置等价 ⊆ 核"**不能**反推相容性。 -/

/-- 反例 Frame：`X = Bool`。 -/
def auditFrame : Frame where
  Θ := ⟨PUnit⟩
  X := { Carrier := Bool, topo := ⊤, meas := ⊤, borel_le := le_top }
  U := ⟨PUnit⟩
  Act := ⟨PUnit⟩
  Ν := ⟨PUnit⟩

/-- 单对象单属性、`Irel` 恒假的形式背景。 -/
def auditCtx : FormalCtx where
  GFCA := Unit
  MFCA := Unit
  Irel := fun _ _ => False

/-- 编码：`true ↦ ∅`，`false ↦ univ`（**非单值**）。 -/
def auditEnc : Encoder auditFrame auditCtx where
  toObjects := fun _ => ∅
  toAttrs := fun b => match b with
    | true => ∅
    | false => Set.univ

/-- 反例实例集。 -/
def auditE : InstSpace := { Carrier := Bool }

/-- ⭐ **反例**：`¬ RespectsEquiv`（故 `RespectsEquiv` 是**真前件**，非重言）。

取 `eqv = ⊤`：相容性要求 `toAttrs` 在 `Bool` 上恒定，
但 `toAttrs true = ∅` 而 `toAttrs false = univ`。∎ -/
theorem kernel_strictly_coarser :
    ¬ auditEnc.RespectsEquiv id (⊤ : Setoid auditE.Carrier) := by
  intro h
  have h' : auditEnc.toAttrs (id true) = auditEnc.toAttrs (id false) :=
    h true false (by trivial)
  have hmem : ((⟨⟩ : Unit) : auditCtx.MFCA) ∈ auditEnc.toAttrs (id false) := by
    show ((⟨⟩ : Unit) : auditCtx.MFCA) ∈ (Set.univ : Set auditCtx.MFCA)
    trivial
  have hnot : ((⟨⟩ : Unit) : auditCtx.MFCA) ∉ auditEnc.toAttrs (id true) := by
    show ((⟨⟩ : Unit) : auditCtx.MFCA) ∉ (∅ : Set auditCtx.MFCA)
    intro hh; exact hh
  rw [h'] at hnot
  exact absurd hmem hnot

end FateV2.Rules.AlphaKernel
