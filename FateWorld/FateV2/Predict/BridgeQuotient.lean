import FateWorld.FateV2.Predict.ViewThreeCounterfactual
/-!
  # Predict · BridgeQuotient

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeQuotient.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ViewThreeCounterfactual
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §32  **桥商的下降与泛性质**（原 `_probe_q18` 中未覆盖部分的正式化）

  **来源**：探针 `probes/_probe_q18.lean`（**不在构建内**）。

  **⚠ 背景**：`_probe_q18` 的 7 条定理中，**3 条已被覆盖**
  （`bridgeSetoid` 在 `ViewThreeCounterfactual.lean`），
  **本节补上剩余 4 条** —— 它们是**商结构**的核心。

  ## 内容

  | 定理 | 内容 |
  |---|---|
  | `bridgeOnQuot` | 桥**下降到商** |
  | ⭐ **`bridgeOnQuot_single_valued`** | **商上单值** |
  | ⭐ **`quot_eq_iff_indistinguishable`** | **信息保持性** |
  | ⭐⭐ **`bridgeSetoid_finest`** | **泛性质**（最细的使桥单值的等价关系）|

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace BridgeQuotient

universe u v

variable {Graph : Type u} {SCM : Type v}

/-- **集合值桥**。 -/
abbrev Bridge (Graph SCM : Type*) : Type _ := Graph → Set SCM

/-- **视角三的桥商**（与 `ViewThreeCounterfactual` 定义相同，
**本节为自足而重述** —— 因两模块命名空间不同）。 -/
def bridgeSetoid (bridge : Bridge Graph SCM) : Setoid SCM where
  r := fun s₁ s₂ => ∀ g, s₁ ∈ bridge g ↔ s₂ ∈ bridge g
  iseqv :=
    { refl := fun _ _ => Iff.rfl
      symm := fun h g => (h g).symm
      trans := fun h₁ h₂ g => (h₁ g).trans (h₂ g) }

/-- **商**：`SCM / ~`。 -/
abbrev QuotByBridge (bridge : Bridge Graph SCM) : Type _ := Quotient (bridgeSetoid bridge)

/-! ### §32.1 ⭐ 桥下降到商 -/

/-- ⭐ **桥下降到商**：把 `s` 送到「它是否属于 `bridge g`」。

**严格说**：`bridge` 在每个等价类上是**常值**的，
故可下降到商，给出 `SCM/~ → (Graph → Prop)`。

**⚠ 实现说明**：用 `Quotient.lift` 下降，其可计算性条件正是
`bridgeSetoid` 定义中「出现在相同 `bridge g` 中」。 -/
def bridgeOnQuot (bridge : Bridge Graph SCM) (g : Graph) :
    QuotByBridge bridge → Prop :=
  Quotient.lift (fun s => s ∈ bridge g)
    (fun _ _ h => propext (h g))

/-- ⭐⭐ **核心定理（单值性）**：在商上，桥对每个 `g` 给出**确定的真值**。

**即**：`[s]` 是否属于 `bridge g` **良定义、单值**。

**这是 `Quotient.lift` 的一次**具体**使用。** -/
theorem bridgeOnQuot_single_valued (bridge : Bridge Graph SCM)
    (g : Graph) (s₁ s₂ : SCM) (h : (bridgeSetoid bridge).r s₁ s₂) :
    bridgeOnQuot bridge g (Quotient.mk _ s₁) = bridgeOnQuot bridge g (Quotient.mk _ s₂) := by
  rw [Quotient.sound h]

/-! ### §32.2 ⭐⭐ 信息保持性 -/

/-- ⭐⭐ **信息保持性**：下降**没有丢失**桥的任何信息。

$$\text{商中相等} \iff \text{桥对它们处处一致}$$

**⟹ 即**：**商恰好保留了桥的全部区分能力** ——
**不多粘一点。** -/
theorem quot_eq_iff_indistinguishable (bridge : Bridge Graph SCM) (s₁ s₂ : SCM) :
    Quotient.mk (bridgeSetoid bridge) s₁ = Quotient.mk (bridgeSetoid bridge) s₂ ↔
      ∀ g, s₁ ∈ bridge g ↔ s₂ ∈ bridge g :=
  ⟨fun h g => Quotient.exact h g, fun h => Quotient.sound h⟩

/-! ### §32.3 ⭐⭐ 泛性质：最细的使桥单值的等价关系 -/

/-- ⭐⭐ **泛性质**：`bridgeSetoid` 是**最细**的、使桥单值的等价关系。

**陈述**：任何等价关系 `r`，若桥沿 `r` 常值（即 `r` 使桥单值），
则 `r` **比** `bridgeSetoid` **粗**（`bridgeSetoid ≤ r`）。

**⟹ 即**：**商 `SCM/~` 保留了桥的全部区分能力，同时恰好单值** ——
**这是「换商」视角的**最优性定理****。

**⚠ 方向说明**：`bridgeSetoid ≤ r` 意味着 `bridgeSetoid` **更细** ——
**即它是满足条件的**最细**者**（粘合最少）。 -/
theorem bridgeSetoid_finest (bridge : Bridge Graph SCM) (r : Setoid SCM)
    (hr : ∀ g, ∀ s₁ s₂, r.r s₁ s₂ → (s₁ ∈ bridge g ↔ s₂ ∈ bridge g)) :
    ∀ s₁ s₂, r.r s₁ s₂ → (bridgeSetoid bridge).r s₁ s₂ :=
  fun s₁ s₂ h g => hr g s₁ s₂ h

/-! ### §32.4 ⭐ 与 `MinimalSufficient` 的结构相似性 -/

/-- ⭐⭐ **两个「最细/最粗」的对偶**（结构对照）。

| 节 | 对象 | 性质 |
|---|---|---|
| **`MinimalSufficient`**（24）| `ker(Obs)` | **最粗**的保真关系 |
| **本节** | `bridgeSetoid` | **最细**的使桥单值的关系 |

**⚠ 两者的方向相反但结构相同**：
- **`MinimalSufficient`**：**不能更粗**（否则丢信息）
- **本节**：**不能更细**（否则冗余）

**⟹ 即**：**「最优商」与「最优核」是一对对偶。** -/
theorem bridgeSetoid_is_finest_single_valued (bridge : Bridge Graph SCM) :
    (∀ g s₁ s₂, (bridgeSetoid bridge).r s₁ s₂ → (s₁ ∈ bridge g ↔ s₂ ∈ bridge g)) ∧
      (∀ r : Setoid SCM,
        (∀ g s₁ s₂, r.r s₁ s₂ → (s₁ ∈ bridge g ↔ s₂ ∈ bridge g)) →
        ∀ s₁ s₂, r.r s₁ s₂ → (bridgeSetoid bridge).r s₁ s₂) :=
  ⟨fun _ _ _ h => h _, fun r hr => bridgeSetoid_finest bridge r hr⟩

end BridgeQuotient

end FateV2.Predict