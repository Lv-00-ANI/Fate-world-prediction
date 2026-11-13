import FateWorld.FateV2.Core.Judgment

/-!
  # Classical · 三条基础公理作为**假设**

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：（新增）D-016 的落点
  - 依赖裁决：**D-016**（底座纯 CIC，三条公理降为基础假设）、
              **D-017**（核内不用 Quot）、**D-019**（自由度最大化）
  - 改动：旧项目把三条公理当**内核门禁的白名单**（`#print axioms ⊆ 三条`）。
          此处改为**账本条目**：用它们就要在 `support` 里登记，门禁从「白名单」
          升级为「**账实相符**」——`#print axioms` 必须**等于**声明的来源。
  - 状态：已编译未验证

  ## 为什么这样更好

  | 旧门禁 | 新门禁 |
  |---|---|
  | `#print axioms` ⊆ {那三条} | `#print axioms` **≡** `support.assumptions` |
  | 三条是「允许的公理」 | 三条是「**要登记的假设**」，与 A1–A34 同级 |
  | 「不需要公理」只能是一个立场 | 变成一个**可机检的架构事实**：构造性核 `support = ∅` |

  ## 边界

  * `FateV2/Core/` —— **不许 import 本文件**（G7 检查）
  * 需要 `ℝ` / `Measure` / 拓扑 / 经典逻辑的，一律放在本目录之下
-/

namespace FateV2.Classical

open FateV2.Core

/-! ## 三条基础公理的假设标识 -/

/-- 命题外延性 -/
def axPropext : AssumptionId := "propext"

/-- 选择公理 -/
def axChoice : AssumptionId := "Classical.choice"

/-- 商的可靠性 -/
def axQuotSound : AssumptionId := "Quot.sound"

/-- 排中律（**派生**自 `axChoice`，单列以便精确登记） -/
def axEm : AssumptionId := "Classical.em"

/-! ## 外壳 -/

/-- **经典外壳**：一组被允许使用的假设。

    `⟨[]⟩` 是构造性外壳（等价于不用任何经典假设）；
    `classical` 是默认的三条。 -/
structure Shell where
  assumptions : List AssumptionId
  deriving DecidableEq, Repr

/-- 构造性外壳：不启用任何假设。 -/
def pure : Shell := ⟨[]⟩

/-- 默认经典外壳：三条基础公理。 -/
def classical : Shell := ⟨[axPropext, axChoice, axQuotSound]⟩

/-- 加排中律的外壳（与 `classical` 实际等价，但登记更精确）。 -/
def classicalWithEm : Shell := ⟨[axPropext, axChoice, axQuotSound, axEm]⟩

namespace Shell

/-- **覆盖**：外壳 `s` 覆盖来源 `sup`——`sup` 里每个假设都在 `s` 中。

    这是「这条定理的登记来源是否被允许」的判据。 -/
def covers (s : Shell) (sup : Support) : Prop :=
  ∀ a ∈ sup.assumptions, a ∈ s.assumptions

/-- `pure` 只覆盖空来源——**构造性定理的判据**。 -/
theorem covers_pure_iff (sup : Support) :
    pure.covers sup ↔ sup.assumptions = [] := by
  constructor
  · intro h
    unfold covers pure at h
    cases hcase : sup.assumptions with
    | nil => rfl
    | cons x xs =>
      have hx : x ∈ ([] : List AssumptionId) := by
        exact h x (by rw [hcase]; exact List.Mem.head xs)
      cases hx
  · intro h
    unfold covers pure
    intro a ha
    rw [h] at ha
    cases ha

/-- `classical` 覆盖三条。 -/
theorem covers_classical_of_subset (sup : Support)
    (h : ∀ a ∈ sup.assumptions, a = axPropext ∨ a = axChoice ∨ a = axQuotSound) :
    classical.covers sup := by
  unfold covers classical
  intro a ha
  rcases h a ha with rfl | rfl | rfl
  · exact List.Mem.head [axChoice, axQuotSound]
  · exact List.Mem.tail _ (List.Mem.head [axQuotSound])
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head []))

end Shell

/-! ## 演示：三条公理各自被真实使用

  这三个定理**故意**用到公理，用来验证 G5（账实相符）。
  它们的声明来源必须**恰好等于** `#print axioms` 的结果，
  登记在 `_support_registry.csv`。 -/

/-- 用 `propext`：命题等价给命题相等。 -/
theorem propext_demo {a b : Prop} (h : a ↔ b) : a = b := propext h

/-- 用 `Classical.choice`：排中律。 -/
theorem em_demo (p : Prop) : p ∨ ¬p := Classical.em p

/-- 用 `Quot.sound`：相关元素在商中等。 -/
theorem quot_sound_demo :
    Quot.mk (fun (_ _ : Nat) => True) 0 = Quot.mk (fun (_ _ : Nat) => True) 1 :=
  Quot.sound trivial

/-- 组合：`propext` + 排中律一起用，来源应为两条。 -/
theorem propext_em_demo {a b : Prop} (h : a ↔ b) : (a = b) ∨ (a ≠ b) :=
  Or.elim (Classical.em (a = b)) (fun h1 => Or.inl h1) (fun h1 => Or.inr h1)

end FateV2.Classical
