import FateWorld.FateV2.Predict.CausalEventFormal

/-!
  # Predict · MacroShiftsMicro

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MacroShiftsMicro.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CausalEventFormal
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-
================================================================================
MacroShiftsMicro.lean  ——  「宏观状态改变微观因果」的非平凡见证（简化版）
================================================================================

## (a) 净版原文

净版 `10-命运理论-净版.md:194`（已知 1.3）：

    P(e_j | e_i, {x_τ}_{τ ≤ t})  ≠  P(e_j | e_i)

净版 `10-命运理论-净版.md:196` 的注释：

    「其中 e_i, e_j 为因果事件。『宏观状态改变微观因果的条件概率』——这是
     『命运参与因果』的严格形式，其形式是**条件化**，不是集合论上的包含。
     **本框架内未证**：该不等式的成立条件本章不给，e_i 与 x_t 的关系亦未定义
     （见开放问题 1.3）。」

## (b) 本文件做到了什么

本文件证明 **`macro_related_to_micro`**，即任务书中给出的**「简化版」**：

    存在 V（有限、非空）、两个因果事件 e_i, e_j、两个宏观历史 ρ₁ ≠ ρ₂，
    使得 e_i 在 ρ₁ 上发生而在 ρ₂ 上不发生（`e_i.holdsAt ρ₁ ↔ ¬ e_i.holdsAt ρ₂`）。

即：**两个不同的宏观历史，改变了同一微观因果事件是否成立**。
结论不是「两个 Bool 值碰巧不同」的巧合：`e_i.holdsAt` 由 `holdsAt` 的定义
（`ρ` 在 `e.vars` 上与 `e.assign` 一致）逐变量判定，而 `ρ₁`、`ρ₂` 在 `e_i.vars`
的某个变量上确实取了不同的值。故本定理是「宏观历史改变微观事件成立性」的
一个具体而正确的见证。

## (c) 本文件没做到什么

1. **概率版未做。** 目标签名中的
   `μ {ω | e_j.holdsAt ρ₁} / μ {ω | e_i.holdsAt ρ₁} ≠ …` 这一形式**本文件未证明**，
   也未提出。任务书规定「只做一条，不要两个都试」，本文件选了简化版。
2. **不含条件化 / 测度。** 净版 `:196` 强调其形式是「**条件化**」；本文件的结论
   是**集合/谓词层面**的成立性差异，**没有**在任何概率空间上给出条件概率的
   不相等。因此它只是 1.3 的**必要条件的弱化版本**，不是 1.3 的形式化。
3. **不刻画 `{x_τ}_{τ ≤ t}` 的时间维度。** 本文件把「宏观状态历史」抽象为单个
   赋值 `V → ℝ`，没有轨迹、没有时间下标、没有 `CausalEvent` 与 `x_t` 的读出关系
   （本文件中 `ρ₁, ρ₂` 直接扮演的是 `CausalEvent.holdsAt` 所接受的变量赋值角色）。
4. **不声称「开放问题 1.3 已解决」。** 恰恰相反：1.3 要求的是「该不等式的
   **成立条件**」——本文件只给出**一个特例的存在性**，没有给出任何充分条件、
   必要条件或刻画。净版 `:196` 所述的「未证」状态**依然成立**。

## (d) 依赖

仅依赖已入链模块 `Fate/CausalEventFormal.lean`（`CausalEvent`、`holdsAt`、
`holdsAt_iff`、`holdsAt_assign` 等，命名空间 `FateV2.Predict.CausalEventFormal`）。
本文件**新建**，不覆盖、不修改任何已入链模块。

--------------------------------------------------------------------------------
标签：**[存在性]**、**[简化版，非概率版]**、**[不宣称解决开放问题 1.3]**
--------------------------------------------------------------------------------

## (e) 修复记录（本次「只修不建」任务）

本任务接到的报告是「2 error：`:98` 与 `:111` 的 Application type mismatch」。
在本机实测（`lake env lean Fate/MacroShiftsMicro.lean`，连跑三遍）**均为 EXIT=0、
零 error、零 warning**，`:98` / `:111` 处不存在类型不匹配。故本轮**未做任何证明
改动**，仅新增本节记录。

另外核实两点（防止同义反复 / 防止虚假通过）：

* `#print axioms` 显示两条定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`，
  **不含 `sorryAx`**，也**不含任何自定义 `axiom`**。
* 本文件含**两条**定理，均保留：`macro_related_to_micro`（核心，**未删**）与
  `not_forall_history_invariant`（配套否命题，**未删**）。没有任何定理因编译不过
  而被删除；**因此无「删了哪条、为什么」需要登记**。
-/

open FateV2.Error
open FateV2.Predict.CausalEventFormal

namespace FateV2.Predict

open FateV2.Modeling
namespace CausalEventFormal

/-- **【简化版】宏观历史改变微观因果的必要条件**（净版 `:194` 的弱化见证）：

存在一个有限非空变量集 `V`、两个因果事件 `e_i, e_j`、以及两个**不同的**宏观历史
`ρ₁ ≠ ρ₂`（在某变量上取值不同），使得

* `e_i` 在 `ρ₁` 上发生、在 `ρ₂` 上**不**发生（`e_i.holdsAt ρ₁ ↔ ¬ e_i.holdsAt ρ₂`），
* 并且 `e_j` 的成立性同样被历史翻转（`e_j.holdsAt ρ₂ ↔ ¬ e_j.holdsAt ρ₁`）。

具体见证：`V := Fin 2`、`e_i.vars := {0}`、`e_i.assign ≡ 0`、
`e_j.vars := {1}`、`e_j.assign ≡ 0`、`ρ₁ 0 = 0, ρ₁ 1 = 1`、`ρ₂ 0 = 1, ρ₂ 1 = 0`。
两个历史是同一个赋值域的**互补**取值，于是「变量 `0` 是否取 0」与「变量 `1` 是否取 0」
在两者之间恰好互换真值。这不是「`Bool` 碰巧不同」的巧合，而是
`CausalEvent.holdsAt`（即 `agreeOn`）逐变量判定的直接后果。

⚠ 这是**存在性**陈述，不是全称陈述，也不是条件概率不等式的证明（见文件头 (c)）。 -/
theorem macro_related_to_micro :
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V)
      (e_i e_j : CausalEvent V) (ρ₁ ρ₂ : V → ℝ),
      (∃ v : V, ρ₁ v ≠ ρ₂ v)
      ∧ (e_i.holdsAt ρ₁ ↔ ¬ e_i.holdsAt ρ₂)
      ∧ (e_j.holdsAt ρ₂ ↔ ¬ e_j.holdsAt ρ₁) := by
  -- 变量集 `Fin 2`；`e_i` 约束变量 `0` 取 0，`e_j` 约束变量 `1` 取 0。
  -- 历史 `ρ₁ = ![0, 1]`（即 `if v = 0 then 0 else 1`），历史 `ρ₂` 与之逐点互补。
  refine ⟨Fin 2, inferInstance, inferInstance,
    ⟨{0}, fun _ => 0⟩, ⟨{1}, fun _ => 0⟩,
    fun v => if v = 0 then 0 else 1, fun v => if v = 0 then 1 else 0, ?_, ?_, ?_⟩
  · -- 宏观历史确实不同：变量 `0` 上取值 `0` 与 `1` 不同。
    refine ⟨0, ?_⟩
    show (if (0 : Fin 2) = 0 then (0 : ℝ) else 1) ≠ (if (0 : Fin 2) = 0 then (1 : ℝ) else 0)
    rw [if_pos rfl, if_pos rfl]
    norm_num
  · -- `e_i`：在 `ρ₁` 上发生（变量 `0` 取 `0`），在 `ρ₂` 上不发生（变量 `0` 取 `1`）。
    have h₁ : (⟨{0}, fun _ => 0⟩ : CausalEvent (Fin 2)).holdsAt
        (fun v => if v = 0 then 0 else 1) := by
      intro v hv
      have hv0 : v = 0 := by simpa using hv
      subst hv0
      show (if (0 : Fin 2) = 0 then (0 : ℝ) else 1) = 0
      rw [if_pos rfl]
    have h₂ : ¬ (⟨{0}, fun _ => 0⟩ : CausalEvent (Fin 2)).holdsAt
        (fun v => if v = 0 then 1 else 0) := by
      intro h
      have h0 : ((0 : Fin 2)) ∈ ({0} : Set (Fin 2)) := by rfl
      have hv : (if (0 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := h 0 h0
      rw [if_pos rfl] at hv
      norm_num at hv
    exact ⟨fun _ hb => h₂ hb, fun _ => h₁⟩
  · -- `e_j`：在 `ρ₂` 上发生（变量 `1` 取 `0`），在 `ρ₁` 上不发生（变量 `1` 取 `1`）。
    have h₂ : (⟨{1}, fun _ => 0⟩ : CausalEvent (Fin 2)).holdsAt
        (fun v => if v = 0 then 1 else 0) := by
      intro v hv
      have hv1 : v = 1 := by simpa using hv
      subst hv1
      show (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0
      rw [if_neg (by norm_num : (1 : Fin 2) ≠ 0)]
    have h₁ : ¬ (⟨{1}, fun _ => 0⟩ : CausalEvent (Fin 2)).holdsAt
        (fun v => if v = 0 then 0 else 1) := by
      intro h
      have h1 : ((1 : Fin 2)) ∈ ({1} : Set (Fin 2)) := by rfl
      have hv : (if (1 : Fin 2) = 0 then (0 : ℝ) else 1) = 0 := h 1 h1
      rw [if_neg (by norm_num : (1 : Fin 2) ≠ 0)] at hv
      norm_num at hv
    exact ⟨fun _ hb => h₁ hb, fun _ => h₂⟩

/-- **配套的否命题形态**：上述见证同时说明「`CausalEvent.holdsAt` 不是宏观历史的
常函数」——不存在「对所有历史取值都相同」的成立性。 -/
theorem not_forall_history_invariant :
    ¬ ∀ (V : Type) (_ : Fintype V) (e : CausalEvent V) (ρ σ : V → ℝ),
        e.holdsAt ρ ↔ e.holdsAt σ := by
  intro h
  obtain ⟨V, hF, _hN, e_i, _e_j, ρ₁, ρ₂, _hne, hiff, _hiff2⟩ := macro_related_to_micro
  -- `hiff : e_i.holdsAt ρ₁ ↔ ¬ e_i.holdsAt ρ₂`，而 `h` 断言两者同真假。
  have hsame : e_i.holdsAt ρ₁ ↔ e_i.holdsAt ρ₂ := h V hF e_i ρ₁ ρ₂
  have hnot : ¬ e_i.holdsAt ρ₂ :=
    fun hb => (hiff.mp (hsame.mpr hb)) hb
  exact hnot (hsame.mp (hiff.mpr hnot))

end CausalEventFormal
end FateV2.Predict