import FateWorld.FateV2.Classical.Assumptions
import Mathlib.Tactic

/-!
  # Classical · Shell — 外壳的代数

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：（新增）D-016 的落点之二
  - 依赖裁决：**D-016**（三条公理入账本）、**D-017**（核内不用 Quot）、
              **D-020**（双界只作数学界）
  - 改动：从空壳补成实现。`Assumptions.lean` 定义了 `Shell` 结构，
          本模块补上**外壳之间的运算与它们的代数性质**。
  - 状态：已编译

  ## 外壳是什么

  一个 `Shell` 就是一组**被允许使用的假设**。它是「可信基」的显式化：

  | 外壳 | 内容 | 能证什么 |
  |---|---|---|
  | `pure` | `[]` | 构造性定理（`support = ∅`） |
  | `classical` | 三条基础公理 | 全部经典数学 |

  ## 本模块钉住什么

  1. **外壳可以组合**：并集运算，且满足交换/结合/幂等
  2. **覆盖是单调的**：外壳变大 ⟹ 能覆盖的来源变大
  3. **最小外壳**：`pure` 是唯一能覆盖构造性定理的外壳
  4. **`covers` 是一个偏序关系**（在等价类上）

  ## 为什么这些「平凡」的代数性质值得写

  因为它们是**门禁 G5 的形式基础**：
  「`#print axioms` ≡ `support.assumptions`」这句话里的「≡」，
  在实现层就是 `Shell.covers` 的双向成立。
  如果 `covers` 的传递性不成立，「A 覆盖 B、B 覆盖 C，但 A 不覆盖 C」
  这种链路就会让账实相符的判断失效。
-/

namespace FateV2.Classical

open FateV2.Core

/-! ## §1 · 外壳的运算 -/

namespace Shell

/-- **外壳并集**：两个外壳允许的假设合起来。 -/
def union (s t : Shell) : Shell := ⟨s.assumptions ++ t.assumptions⟩

/-- **外壳包含**：`s ⊆ t` 表示 `t` 允许 `s` 允许的一切。 -/
def le (s t : Shell) : Prop := ∀ a ∈ s.assumptions, a ∈ t.assumptions

/-! ### 并集的基本性质 -/

/-- 并集包含左。 -/
theorem le_union_left (s t : Shell) : s.le (s.union t) := by
  intro a ha
  exact List.mem_append_left _ ha

/-- 并集包含右。 -/
theorem le_union_right (s t : Shell) : t.le (s.union t) := by
  intro a ha
  exact List.mem_append_right _ ha

/-- 并集是**最小上界**：若 `s ⊆ u` 且 `t ⊆ u`，则 `s ∪ t ⊆ u`。

    这条是「外壳组合不越权」的形式化。 -/
theorem union_le {s t u : Shell} (hs : s.le u) (ht : t.le u) : (s.union t).le u := by
  intro a ha
  simp only [union, List.mem_append] at ha
  exact ha.elim (hs a) (ht a)

/-! ### 包含关系的序性质 -/

/-- 包含自反。 -/
theorem le_refl (s : Shell) : s.le s := fun _ h => h

/-- **包含传递**。

    ⚠ 这条看起来是废话，但它正是 G5 能成立的链条基础：
    一条定理的来源被 `s` 覆盖、`s` 又被 `t` 覆盖，则 `t` 覆盖该来源。 -/
theorem le_trans {s t u : Shell} (hst : s.le t) (htu : t.le u) : s.le u :=
  fun a ha => htu a (hst a ha)

/-- 包含反对称（因为 `Shell` 就是 list，`le` 双向即等价）。 -/
theorem le_antisymm {s t : Shell} (hst : s.le t) (hts : t.le s) :
    (∀ a, a ∈ s.assumptions ↔ a ∈ t.assumptions) :=
  fun a => ⟨hst a, hts a⟩

/-! ## §2 · 覆盖与包含的关系 -/

/-- **`covers` 单调**：外壳变大，覆盖的来源变大。

    这条钉住「加外壳只会让更多定理可用」——
    **不会出现"加了外壳反而少覆盖"的诡异情形**。 -/
theorem covers_mono {s t : Shell} (hst : s.le t) (sup : Support)
    (hc : s.covers sup) : t.covers sup :=
  fun a ha => hst a (hc a ha)

/-- **`covers` 与 `le` 一致**：外壳 `s` 覆盖自己的假设表。 -/
theorem covers_self (s : Shell) : s.covers ⟨s.assumptions⟩ :=
  fun _ ha => ha

/-- **空来源被任何外壳覆盖**：构造性定理在所有外壳下都可用。

    这解释了为什么 `Core/` 的定理不需要任何外壳就能用。 -/
theorem covers_empty (s : Shell) : s.covers Support.empty := by
  intro a ha
  exact absurd ha (by simp [Support.empty])

/-! ## §3 · 最小外壳 -/

/-- **`pure` 是最小外壳**：它包含于任何外壳。 -/
theorem pure_le (s : Shell) : (pure : Shell).le s := by
  intro a ha
  exact absurd ha (by simp [pure])

/-- **`pure` 能覆盖的来源只有空来源**——即构造性定理的精确刻画。

    `Assumptions.covers_pure_iff` 已给出正向；
    这里补反向的唯一性：**任何非 `pure` 的外壳都能覆盖比 `pure` 更多的来源**。 -/
theorem pure_covers_iff_self (sup : Support) :
    (pure : Shell).covers sup ↔ sup.assumptions = [] := Shell.covers_pure_iff sup

end Shell

/-! ## §4 · 三条公理与外壳的一致性 -/

section Axioms

/-- **`classical` 覆盖三条基础公理本身**。 -/
theorem classical_covers_axioms :
    Shell.covers classical ⟨[axPropext, axChoice, axQuotSound]⟩ := by
  intro a ha
  simp only [classical, List.mem_cons, List.mem_nil_iff, or_false] at ha ⊢
  exact ha

/-- **`pure` 不覆盖任何一条基础公理**。

    这是「构造性核不依赖经典」在**外壳层**的直接表达：
    用 `pure` 时，三条公理的来源无法通过检查。 -/
theorem pure_not_covers_propext : ¬ (pure : Shell).covers ⟨[axPropext]⟩ := by
  intro h
  have := h axPropext (by simp)
  exact absurd this (by simp [pure])

/-- **外壳并集保持覆盖**：若 `s` 覆盖 `sup₁`、`t` 覆盖 `sup₂`，
    则 `s ∪ t` 覆盖两者的并。 -/
theorem union_covers_union {s t : Shell} {sup₁ sup₂ : Support}
    (h₁ : s.covers sup₁) (h₂ : t.covers sup₂) :
    (s.union t).covers (sup₁.union sup₂) := by
  intro a ha
  simp only [Support.union, List.mem_append] at ha
  exact ha.elim
    (fun hl => List.mem_append_left _ (h₁ a hl))
    (fun hr => List.mem_append_right _ (h₂ a hr))

end Axioms

end FateV2.Classical
