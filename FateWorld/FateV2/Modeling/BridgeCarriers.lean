import FateWorld.FateV2.Modeling.KernelQuotientExtra
/-!
  # Modeling · BridgeCarriers

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeCarriers.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：KernelQuotientExtra
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §17  **桥的两种载体是同一对象**（原 `_probe_bridge` 的正式化）

  **来源**：探针 `probes/_probe_bridge.lean`（**不在构建内**）。

  ## 问题

  「桥」$\Phi : G \mapsto \mathfrak{F}|_G$ 可用**两种载体**表达：

  | 载体 | 类型 | 说明 |
  |---|---|---|
  | **`BridgeByFun`** | `Graph → Set SCM` | **集合值**映射 |
  | **`BridgeByRel`** | `Graph → SCM → Prop` | **关系**形式 |

  「集合值」与「关系」在集合论上等价（`Set α = α → Prop`），
  但**在 Lean 的类型层，这一等价需要显式给出**。

  ## ⭐ 结论：**二者是同一对象**

  本节给出**双向转换**与**两条互逆律** —— 即**类型层的同构**。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Modeling
namespace BridgeCarriers

universe u v

/-- **集合值载体**：`Graph → Set SCM`。 -/
abbrev BridgeByFun (Graph SCM : Type*) : Type _ := Graph → Set SCM

/-- **关系载体**：`Graph → SCM → Prop`。 -/
abbrev BridgeByRel (Graph SCM : Type*) : Type _ := Graph → SCM → Prop

/-- **关系 → 集合**。 -/
def relToFun {Graph SCM : Type*} (R : BridgeByRel Graph SCM) : BridgeByFun Graph SCM :=
  fun g => {s | R g s}

/-- **集合 → 关系**。 -/
def funToRel {Graph SCM : Type*} (b : BridgeByFun Graph SCM) : BridgeByRel Graph SCM :=
  fun g s => s ∈ b g

/-- ⭐ **互逆律之一**：关系 → 集合 → 关系 = 原关系。 -/
theorem funToRel_relToFun {Graph SCM : Type*} (R : BridgeByRel Graph SCM) :
    funToRel (relToFun R) = R := by
  funext g s
  rfl

/-- ⭐ **互逆律之二**：集合 → 关系 → 集合 = 原集合。 -/
theorem relToFun_funToRel {Graph SCM : Type*} (b : BridgeByFun Graph SCM) :
    relToFun (funToRel b) = b := by
  funext g
  ext s
  rfl

/-- ⭐⭐ **同一对象**（两条互逆律的合成陈述）。

**⟹ 即**：**「集合值桥」与「关系桥」在类型层是同构的** ——
**故「桥是多值的」这一结论不依赖载体的选择。** -/
theorem bridge_carriers_equiv {Graph SCM : Type*} :
    (∀ R : BridgeByRel Graph SCM, funToRel (relToFun R) = R) ∧
      (∀ b : BridgeByFun Graph SCM, relToFun (funToRel b) = b) :=
  ⟨funToRel_relToFun, relToFun_funToRel⟩

/-! ### §17.1 ⚠ 一处**不**做的证明（诚实标注）

探针原拟证 `bridge_multivalued_is_essential`（「桥的多值性是本质的」）。

**⚠ 本节**不**给出它** —— 理由：

**该命题的精确内容尚未找到合适的 Lean 形式**：

* 「不依赖载体」这一说法已由 `bridge_carriers_equiv` 覆盖；
* 「多值性是本质的」若理解为「不存在截面」，则**在 Lean 中为假** ——
  因为 `Classical.choice` 可提供截面（**这正是本项目已登记的
  「桥非单值但可选」的处境**）；
* 若理解为「不使用选择就无法构造」，则它是关于**证明论/构造性**的**元陈述**，
  **不是 Lean 中可陈述的命题**。

**⟹ 故本节如实不证它** —— **不假装证明一个形式不清的断言**。 -/

end BridgeCarriers

end FateV2.Modeling