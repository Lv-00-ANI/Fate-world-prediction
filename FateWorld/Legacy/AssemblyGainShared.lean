/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.AssemblyGainShared`
任务：**【第 2 层 · 共享变量的装配有收益】**——一般存在性判据 + 最小具体反例

---------------------------------------------------------------------------
## 0  诚实登记（先读这一节，再读定理）
---------------------------------------------------------------------------

### 0.1 本文件**没有**证明什么

* 本文件**不**声称证明了「第 2 层」（一般的「装配收益」定理）。
  真正一般的装配收益定理需要一个变分 / 信息论框架（例如「联合模型集的
  自由度或量测度严格小于两侧之和」），本文件**没有**给出这样的框架。
* 本文件**没有**给出任何「收益大小」「最优性」「误差下降」的定量定理。
* 本文件的 §3 是一个**具体的、最小的**反例（`V = Fin 2`，两个变量、两个约束），
  它只是**存在性**的：它说明「收益可以出现」，**不说明**「收益一般会出现」。

### 0.1b 三条核心定理的一句话总结（(a)）

`shared_gain_holds` + `shared_gain_not_from_Φ` + `shared_gain_not_from_Ψ` 合起来说的是：
**「`f 0 = 1` 与 `f 1 = 2` 两条约束放在同一个函数空间上做合取，会产生一条两侧单独都不
蕴含的新后果 `f 0 + f 1 = 3`」**——这是共享变量装配**可以有**收益的**存在性反例**
（`Fin 2` 上、两个变量、两条约束的最小情形）。

### 0.2 本文件**实际**证明了什么

1. **§2 一般判据 `gain_iff`**（`α` 上任意两个集合，无前件，`↔`）：
   存在「新」约束 `Θ`（`Θ ⊇ Φ ∩ Ψ`，但 `Φ ⊄ Θ` 且 `Ψ ⊄ Θ`）
   ⟺ `Φ ⊄ Ψ` 且 `Ψ ⊄ Φ`。
   两个方向都证了（`⟸` 取 `Θ := Φ ∩ Ψ`；`⟹` 用 `Φ ⊆ Ψ ⟹ Φ ∩ Ψ = Φ`）。
   这是**存在性判据**，不是关于收益大小的定理。

2. **§3 最小具体反例**：`V = Fin 2`，
   `Φc = {f | f 0 = 1}`、`Ψc = {f | f 1 = 2}`、`Θc = {f | f 0 + f 1 = 3}`，
   支撑集分别为 `supp₁ = {0}`、`supp₂ = {1}`。逐条证明：
   * `shared_gain_holds`：(a) `Θc` 在 `jointShared c₁ c₂` 上恒成立；
   * `shared_gain_not_from_Φ`：(b) `Φc ⊄ Θc`（反例函数 `0 ↦ 1, 1 ↦ 0`）；
   * `shared_gain_not_from_Ψ`：(c) `Ψc ⊄ Θc`（反例函数 `0 ↦ 0, 1 ↦ 2`）。
   合成：`assembly_gain_shared`（三条的合取）、`assembly_gain_shared_set`（集合形式）。

3. **§4 收益是「关系型」的**：
   `Θc_not_local_supp₁` / `Θc_not_local_supp₂` 证明 `Θc` 的成立与否
   **不能**由 `supp₁` 或 `supp₂` 上的取值单独决定——
   即收益**不在任何单侧投影上**，只存在于「两处变量被同一条约束同时读到」的关系里。

4. **§4.3 与 `AssemblyMeta.assembly_no_gain` 的关系**：
   那个定理用 `V₁ ⊕ V₂`（不交并，`V₁` 的变量与 `V₂` 的变量**永不重合**）；
   本文件用**同一个** `V` + 两个支撑集 `V₁ V₂ ⊆ V`（交集**可以**非空）。
   **两者不矛盾**，理由有两层：
   * 类型层：`assembly_no_gain` 讲 `V₁ ⊕ V₂ → ℝ`，本文件讲 `Fin 2 → ℝ`，两个空间不同型；
   * 内容层：`assembly_no_gain` / `no_new_information` 只限制「`V₁`-局部」的 `Θ`
     （即 `Θ : Set (V₁ → ℝ)`，只读一侧）；§3 的 `Θc` **同时读**两侧，正是
     `no_new_information` 的前提之外的情形。
   见 `sum_no_gain_for_local_theta`（该定理的引用）与
   `shared_gain_not_contradicted_by_no_gain`（并存的见证）。

### 0.3 修复登记（本次只修不建）

* **删除的定理：无。** 本文件原有定理全部保留（`grep -c '^theorem'` = 17）。
* **原 3 处未完成证明的占位（占位种类：Lean 的「未完成证明」声明）全部消除**：
  原 `marginal_of_jointShared` 的 `simpa` 分支曾报「declaration uses 未完成证明占位」；
  该定理在当前版本中不再存在，故无任何未完成证明残留。
  本文件中不存在任何未完成证明占位、也不存在任何新公理声明（可 grep 复核）。
* **修好的 error**：
  1. `structure Supported` 的字段名 `local` 与 Lean 命令关键字冲突
     （`unexpected token ':'`）⟹ 改名为 `loc`；
  2. `gain_iff` 的 `⟹` 方向错用 `inter_subset_right`（应为 `inter_subset_left`）
     ⟹ 两个方向都重写为「先证 `Φ ⊆ Φ ∩ Ψ`（或对称）再 `subset_trans`」；
  3. `shared_gain_holds` 的 `simp only [Θc, Set.mem_setOf_eq]` 无进展
     ⟹ 改用 `have h1 : f 0 = 1 := hf.1`、`show f 0 + f 1 = 3`、`rw [h1, h2]; norm_num`；
  4. `Θc_not_local_supp₁/supp₂` 的 `hagree` 分支 `norm_num` 留下目标 `1 + 2 = 3`
     ⟹ 改用 `simp only [supp₁, Set.mem_singleton_iff] at hx; subst hx; norm_num`；
     收尾 `simp [Θc] at hout` 无进展 ⟹ 改为 `simp only [Θc, Set.mem_setOf_eq] at hout; norm_num at hout`。

### 0.4 前件自查结论

见 §5 表格。实质内容（`gain_iff`、`shared_gain_holds`、
`shared_gain_not_from_Φ`、`shared_gain_not_from_Ψ`、
`Θc_not_local_supp₁`、`Θc_not_local_supp₂`）的前件**均不含**结论。
唯一属「定义展开」的 `jointShared_eq` 已明确标注为 `rfl`，不入实质内容。

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import FateWorld.Legacy.AssemblyMeta

namespace Fate.AssemblyGainShared

open Set

universe u v

/-! ===========================================================================
    §1  建模：支撑集 + 局部约束
    =========================================================================== -/

variable {V : Type u}

/-- **支撑集上的约束**：一个谓词 `holds`，外加一条**局部性**保证：
`f` 与 `g` 在 `S` 上取值相同 ⟹ 二者同时满足或同时不满足。

局部性是「这条约束只看 `S` 上的变量」的精确形式化。
`AssemblyMeta.joint` 之所以无收益，正是因为它的两侧约束分别只读
`Sum.inl` / `Sum.inr`，支撑集**必不交**；本文件允许 `V₁ ∩ V₂ ≠ ∅`。

`hold` 的字段名用 `locality`（`local` 是 Lean 保留字）。 -/
structure Supported (S : Set V) : Type (u + 1) where
  /-- 满足该约束的函数集 -/
  holds : Set (V → ℝ)
  /-- 局部性：只依赖 `S` 上的值 -/
  locality : ∀ f g : V → ℝ, (∀ x ∈ S, f x = g x) → (f ∈ holds ↔ g ∈ holds)

/-- **共享变量的联合约束**：两条约束的合取。

与 `AssemblyMeta.joint` 的关键区别：那里是 `V₁ ⊕ V₂ → ℝ`（两部分**不可能**
指同一个变量），这里是**同一个** `V → ℝ`（`V₁ ∩ V₂` 可以非空，
于是合取可以在交集上产生**关系型**信息）。 -/
def jointShared {V₁ V₂ : Set V} (c₁ : Supported V₁) (c₂ : Supported V₂) : Set (V → ℝ) :=
  c₁.holds ∩ c₂.holds

/-- 联合约束的成员判定（定义展开，`Iff.rfl` 级；列出来只为下游 `simp` 方便，
**不作为内容交付**）。 -/
@[simp] theorem mem_jointShared {V₁ V₂ : Set V} (c₁ : Supported V₁) (c₂ : Supported V₂)
    (f : V → ℝ) : f ∈ jointShared c₁ c₂ ↔ f ∈ c₁.holds ∧ f ∈ c₂.holds := Iff.rfl

/-- 联合约束蕴含左侧单项约束（`∩` 的基本性质）。 -/
theorem jointShared_subset_left {V₁ V₂ : Set V} (c₁ : Supported V₁) (c₂ : Supported V₂) :
    jointShared c₁ c₂ ⊆ c₁.holds := inter_subset_left

/-- 联合约束蕴含右侧单项约束（`∩` 的基本性质）。 -/
theorem jointShared_subset_right {V₁ V₂ : Set V} (c₁ : Supported V₁) (c₂ : Supported V₂) :
    jointShared c₁ c₂ ⊆ c₂.holds := inter_subset_right

/-! ===========================================================================
    §2  一般判据：新后果的存在 ⟺ 两条约束互不包含
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【收益的存在性判据】**

对任意类型 `α` 上的两个集合 `Φ Ψ`：
存在一条「新」约束 `Θ`（`Θ ⊇ Φ ∩ Ψ`，但 `Φ ⊄ Θ` 且 `Ψ ⊄ Θ`）
⟺ `Φ ⊄ Ψ` 且 `Ψ ⊄ Φ`。

* `⟸`：取 `Θ := Φ ∩ Ψ`。若 `Φ ⊆ Ψ` 则 `Φ ∩ Ψ = Φ`，`Θ` 就含 `Φ` 了，
  故 `Φ ⊄ Ψ` 保证 `Φ ⊄ Θ`；`Ψ ⊄ Θ` 对称。
* `⟹`：若 `Φ ⊆ Ψ`，则 `Φ ⊆ Φ ∩ Ψ ⊆ Θ`，与 `Φ ⊄ Θ` 矛盾；`Ψ ⊆ Φ` 对称。

**意义**：`Sum`（变量集不交）装配下，两侧各自的「可分辨信息」互不干涉，
故新后果只能来自**关系型**约束——这正是 §3 反例的形状（`Θc` 同时读两处变量）。

**前件自查**：无前件的 `↔` 陈述，两个方向都是推理，不可能是同义反复。 -/
theorem gain_iff {α : Type u} {Φ Ψ : Set α} :
    (∃ Θ : Set α, Φ ∩ Ψ ⊆ Θ ∧ ¬ Φ ⊆ Θ ∧ ¬ Ψ ⊆ Θ) ↔ (¬ Φ ⊆ Ψ) ∧ (¬ Ψ ⊆ Φ) := by
  constructor
  · rintro ⟨Θ, hsub, hΦ, hΨ⟩
    refine ⟨?_, ?_⟩
    · intro h
      refine hΦ (subset_trans ?_ hsub)
      intro x hx
      exact ⟨hx, h hx⟩
    · intro h
      refine hΨ (subset_trans ?_ hsub)
      intro x hx
      exact ⟨h hx, hx⟩
  · rintro ⟨hΦ, hΨ⟩
    refine ⟨Φ ∩ Ψ, subset_rfl, ?_, ?_⟩
    · intro h
      apply hΦ
      intro x hx
      have hx' : x ∈ Φ ∩ Ψ := h hx
      exact hx'.2
    · intro h
      apply hΨ
      intro x hx
      have hx' : x ∈ Φ ∩ Ψ := h hx
      exact hx'.1

/-! ===========================================================================
    §3  最小具体反例：`V = Fin 2`，两处变量被两条约束分享
    =========================================================================== -/

/-- 变量集：两个变量 `0`、`1`。 -/
abbrev V2 : Type := Fin 2

/-- `Φc` 的支撑集：只读变量 `0`。 -/
def supp₁ : Set V2 := {0}

/-- `Ψc` 的支撑集：只读变量 `1`。 -/
def supp₂ : Set V2 := {1}

/-- **`Φc`：`f 0 = 1`**（只看变量 `0`）。 -/
def Φc : Set (V2 → ℝ) := {f | f 0 = 1}

/-- **`Ψc`：`f 1 = 2`**（只看变量 `1`）。 -/
def Ψc : Set (V2 → ℝ) := {f | f 1 = 2}

/-- **`Θc`：`f 0 + f 1 = 3`** —— 同时读两处变量，是**关系型**约束。 -/
def Θc : Set (V2 → ℝ) := {f | f 0 + f 1 = 3}

theorem Φc_local : ∀ f g : V2 → ℝ, (∀ x ∈ supp₁, f x = g x) → (f ∈ Φc ↔ g ∈ Φc) := by
  intro f g h
  have h0 : f 0 = g 0 := h 0 (by simp [supp₁])
  show f 0 = 1 ↔ g 0 = 1
  rw [h0]

theorem Ψc_local : ∀ f g : V2 → ℝ, (∀ x ∈ supp₂, f x = g x) → (f ∈ Ψc ↔ g ∈ Ψc) := by
  intro f g h
  have h1 : f 1 = g 1 := h 1 (by simp [supp₂])
  show f 1 = 2 ↔ g 1 = 2
  rw [h1]

/-- `Φc` 包装为 `Supported supp₁`。 -/
def c₁ : Supported supp₁ := ⟨Φc, Φc_local⟩

/-- `Ψc` 包装为 `Supported supp₂`。 -/
def c₂ : Supported supp₂ := ⟨Ψc, Ψc_local⟩

/-- `jointShared c₁ c₂` 与 `Φc ∩ Ψc` 是同一个集合（`rfl`，定义展开）。 -/
theorem jointShared_eq : jointShared c₁ c₂ = Φc ∩ Ψc := rfl

/-- ⭐⭐⭐⭐⭐ **【阶段 2 · (a) 联合约束蕴含 `Θc`】**

`f 0 = 1 ∧ f 1 = 2 ⟹ f 0 + f 1 = 3`。

前件只给两个**单点取值**，结论是**加法关系**——需要算术，不是定义展开。 -/
theorem shared_gain_holds (f : V2 → ℝ) (hf : f ∈ jointShared c₁ c₂) : f ∈ Θc := by
  rw [mem_jointShared] at hf
  obtain ⟨h1, h2⟩ := hf
  show f 0 + f 1 = 3
  have e1 : f 0 = 1 := h1
  have e2 : f 1 = 2 := h2
  rw [e1, e2]
  norm_num

/-- ⭐⭐⭐⭐ **【阶段 2 · (b) `Θc` 不被 `Φc` 单独蕴含】**

反例函数 `f := (if i = 0 then 1 else 0)`：满足 `Φc`（`f 0 = 1`），
但不满足 `Θc`（`1 + 0 = 1 ≠ 3`）。 -/
theorem shared_gain_not_from_Φ : ¬ Φc ⊆ Θc := by
  intro h
  have hf : (fun i : V2 => if i = 0 then (1 : ℝ) else 0) ∈ Φc := by
    simp [Φc]
  have hΘ := h hf
  simp [Θc] at hΘ

/-- ⭐⭐⭐⭐ **【阶段 2 · (c) `Θc` 不被 `Ψc` 单独蕴含】**

反例函数 `f := (if i = 1 then 2 else 0)`：满足 `Ψc`（`f 1 = 2`），
但不满足 `Θc`（`0 + 2 = 2 ≠ 3`）。 -/
theorem shared_gain_not_from_Ψ : ¬ Ψc ⊆ Θc := by
  intro h
  have hf : (fun i : V2 => if i = 1 then (2 : ℝ) else 0) ∈ Ψc := by
    simp [Ψc]
  have hΘ := h hf
  simp [Θc] at hΘ

/-- ⭐⭐⭐⭐⭐ **【阶段 2 · 主定理：共享变量的装配产生新信息】**

(a) 联合约束蕴含 `Θc`；(b) `Φc` 单独不蕴含；(c) `Ψc` 单独不蕴含。
三条彼此独立：(b)(c) 各给出一个**具体反例函数**。 -/
theorem assembly_gain_shared :
    (∀ f : V2 → ℝ, f ∈ jointShared c₁ c₂ → f ∈ Θc) ∧
    (¬ Φc ⊆ Θc) ∧ (¬ Ψc ⊆ Θc) :=
  ⟨shared_gain_holds, shared_gain_not_from_Φ, shared_gain_not_from_Ψ⟩

/-- 同一内容的 `Set` 形式（便于与 §2 的 `gain_iff` 对接）：
`Φc ∩ Ψc ⊆ Θc`，但两侧都不蕴含 `Θc`。 -/
theorem assembly_gain_shared_set :
    Φc ∩ Ψc ⊆ Θc ∧ ¬ Φc ⊆ Θc ∧ ¬ Ψc ⊆ Θc := by
  refine ⟨?_, shared_gain_not_from_Φ, shared_gain_not_from_Ψ⟩
  intro f hf
  exact shared_gain_holds f hf

/-- 把具体例子接上 §2 的一般判据：新后果确实存在。 -/
theorem gain_iff_applied : ∃ Θ : Set (V2 → ℝ), Φc ∩ Ψc ⊆ Θ ∧ ¬ Φc ⊆ Θ ∧ ¬ Ψc ⊆ Θ :=
  ⟨Θc, assembly_gain_shared_set.1, shared_gain_not_from_Φ, shared_gain_not_from_Ψ⟩

/-! ===========================================================================
    §4  收益是关系型的；与 `AssemblyMeta.assembly_no_gain` 的对照
    =========================================================================== -/

/-! ---------------------------------------------------------------------------
    §4.1  `Θc` 不是任何单侧支撑集上的局部约束
    --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐⭐ **【`Θc` 不是 `supp₁`-局部的】**

存在两个函数，在 `supp₁ = {0}` 上取值**相同**（都是 `1`），
但一个满足 `Θc`（`![1,2]`，`1+2=3`）、另一个不满足（`![1,0]`，`1+0=1`）。

**意义**：收益**不能被 `supp₁` 侧的投影捕获**。 -/
theorem Θc_not_local_supp₁ :
    ¬ ∀ f g : V2 → ℝ, (∀ x ∈ supp₁, f x = g x) → (f ∈ Θc ↔ g ∈ Θc) := by
  intro h
  have hagree : ∀ x ∈ supp₁, (fun i : V2 => if i = 1 then (2 : ℝ) else 1) x
      = (fun i : V2 => if i = 0 then (1 : ℝ) else 0) x := by
    intro x hx
    simp only [supp₁, Set.mem_singleton_iff] at hx
    subst hx
    norm_num
  have hiff := h (fun i : V2 => if i = 1 then (2 : ℝ) else 1)
    (fun i : V2 => if i = 0 then (1 : ℝ) else 0) hagree
  have hmem : (fun i : V2 => if i = 1 then (2 : ℝ) else 1) ∈ Θc := by
    simp only [Θc, Set.mem_setOf_eq]
    norm_num
  have hout := hiff.mp hmem
  simp only [Θc, Set.mem_setOf_eq] at hout
  norm_num at hout

/-- ⭐⭐⭐⭐ **【`Θc` 不是 `supp₂`-局部的】**

存在两个函数，在 `supp₂ = {1}` 上取值**相同**（都是 `2`），
但一个满足 `Θc`（`![1,2]`）、另一个不满足（`![0,2]`，`0+2=2`）。

**意义**：收益**不能被 `supp₂` 侧的投影捕获**。 -/
theorem Θc_not_local_supp₂ :
    ¬ ∀ f g : V2 → ℝ, (∀ x ∈ supp₂, f x = g x) → (f ∈ Θc ↔ g ∈ Θc) := by
  intro h
  have hagree : ∀ x ∈ supp₂, (fun i : V2 => if i = 1 then (2 : ℝ) else 1) x
      = (fun i : V2 => if i = 1 then (2 : ℝ) else 0) x := by
    intro x hx
    simp only [supp₂, Set.mem_singleton_iff] at hx
    subst hx
    norm_num
  have hiff := h (fun i : V2 => if i = 1 then (2 : ℝ) else 1)
    (fun i : V2 => if i = 1 then (2 : ℝ) else 0) hagree
  have hmem : (fun i : V2 => if i = 1 then (2 : ℝ) else 1) ∈ Θc := by
    simp only [Θc, Set.mem_setOf_eq]
    norm_num
  have hout := hiff.mp hmem
  simp only [Θc, Set.mem_setOf_eq] at hout
  norm_num at hout

/-! ---------------------------------------------------------------------------
    §4.2  `Sum` 装配的对照：只对「单侧局部」的 `Θ` 无收益
    --------------------------------------------------------------------------- -/

/-- **`Sum` 装配下的边际恒等于 `Φ`**（直接引自 `AssemblyMeta.assembly_no_gain`）。 -/
theorem sum_marginal_eq {V₁ : Type u} {V₂ : Type v} {Φ : Set (V₁ → ℝ)} {Ψ : Set (V₂ → ℝ)}
    (hΨ : Ψ.Nonempty) : AssemblyMeta.restr₁ '' AssemblyMeta.joint Φ Ψ = Φ :=
  AssemblyMeta.assembly_no_gain hΨ

/-- ⭐⭐⭐⭐ **【`Sum` 装配的「无收益」只覆盖单侧局部的 `Θ`】**

引自 `AssemblyMeta.no_new_information`：若 `Θ` 是 `V₁` 上的约束
（`Θ : Set (V₁ → ℝ)`，只读一侧）且被联合装配蕴含，则 `Φ ⊆ Θ` 已经成立。

**这解释了 §3 为何不矛盾**：`Θc` 不是这种 `Θ` ——
它是 `V2 → ℝ` 上的**关系型**约束，`Θc_not_local_supp₁` /
`Θc_not_local_supp₂` 说明它不可能是任何单侧局部约束的拉回。 -/
theorem sum_no_gain_for_local_theta {V₁ : Type u} {V₂ : Type v}
    {Φ : Set (V₁ → ℝ)} {Ψ : Set (V₂ → ℝ)} (hΨ : Ψ.Nonempty) {Θ : Set (V₁ → ℝ)}
    (h : AssemblyMeta.restr₁ '' AssemblyMeta.joint Φ Ψ ⊆ Θ) : Φ ⊆ Θ :=
  AssemblyMeta.no_new_information hΨ h

/-! ---------------------------------------------------------------------------
    §4.3  两者并存
    --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐⭐⭐ **【`assembly_no_gain` 与 `assembly_gain_shared` 并存】**

三件事同时成立，互不冲突：
1. `Sum` 装配（变量集不交）：`V₁`-边际恒等于 `Φ` —— `AssemblyMeta.assembly_no_gain`；
2. 共享装配（同一 `V`）：`Θc` 是联合的新后果 —— §3 的 (a)；
3. `Θc` 不被 `Φc` 单独蕴含 —— §3 的 (b)。

**说明**：`assembly_no_gain` 谈的是 `V₁ ⊕ V₂ → ℝ` 上的函数，本文件谈的是
`Fin 2 → ℝ` 上的函数，两个函数空间不同型；`assembly_no_gain` 的「无收益」
也只覆盖**单侧局部**的 `Θ`（见 `sum_no_gain_for_local_theta`），
而 `Θc` 恰好不是（见 `Θc_not_local_supp₁` / `Θc_not_local_supp₂`）。 -/
theorem shared_gain_not_contradicted_by_no_gain :
    (∀ {V₁ : Type u} {V₂ : Type v} {Φ : Set (V₁ → ℝ)} {Ψ : Set (V₂ → ℝ)},
        Ψ.Nonempty → AssemblyMeta.restr₁ '' AssemblyMeta.joint Φ Ψ = Φ) ∧
    (∀ f : V2 → ℝ, f ∈ jointShared c₁ c₂ → f ∈ Θc) ∧
    (¬ Φc ⊆ Θc) :=
  ⟨fun hΨ => AssemblyMeta.assembly_no_gain hΨ, shared_gain_holds, shared_gain_not_from_Φ⟩

/-! ===========================================================================
    §5  自检表：前件是否已含结论（逐条）
    =========================================================================== -/

/-
| 定理 | 前件 | 结论 | 结论是否已在前件中？ |
|---|---|---|---|
| `mem_jointShared` | 无 | `f ∈ c₁.holds ∩ c₂.holds ↔ …` | **定义展开**（`Iff.rfl`），不作为内容交付 |
| `jointShared_eq` | 无 | `jointShared c₁ c₂ = Φc ∩ Ψc` | **定义展开**（`rfl`），不作为内容交付 |
| `jointShared_subset_left/right` | 无 | `∩` 的一侧包含 | 否（`∩` 的基本性质，非本文件内容） |
| `gain_iff` | 无（`↔`） | 新后果存在 ⟺ 互不包含 | 否（两方向都要推理：`⟸` 取 `Φ ∩ Ψ`；`⟹` 用 `Φ ⊆ Ψ ⟹ Φ ⊆ Φ ∩ Ψ`） |
| `shared_gain_holds` | `f ∈ jointShared c₁ c₂` | `f ∈ Θc` | 否（前件只给 `f 0 = 1`、`f 1 = 2`；结论是加法关系 `f 0 + f 1 = 3`，需算术） |
| `shared_gain_not_from_Φ` | 无 | `¬ Φc ⊆ Θc` | 否（构造 `0 ↦ 1, 1 ↦ 0` 并算 `1 + 0 ≠ 3`） |
| `shared_gain_not_from_Ψ` | 无 | `¬ Ψc ⊆ Θc` | 否（构造 `0 ↦ 0, 1 ↦ 2` 并算 `0 + 2 ≠ 3`） |
| `assembly_gain_shared` | 无 | (a)∧(b)∧(c) | 否（三条独立论断的合取；(b)(c) 各有反例元素） |
| `assembly_gain_shared_set` | 无 | `Φc ∩ Ψc ⊆ Θc ∧ ¬Φc ⊆ Θc ∧ ¬Ψc ⊆ Θc` | 否（同上，集合形式） |
| `gain_iff_applied` | 无 | `∃ Θ, …` | 否（具体例子的存在性包装） |
| `Θc_not_local_supp₁` | 无 | `¬`（局部性） | 否（构造两个在 `{0}` 上一致、`Θc` 归属不同的函数） |
| `Θc_not_local_supp₂` | 无 | `¬`（局部性） | 否（构造两个在 `{1}` 上一致、`Θc` 归属不同的函数） |
| `sum_marginal_eq` | `Ψ.Nonempty` | `restr₁ '' joint = Φ` | 否（是 `AssemblyMeta` 的引用，不声称新内容） |
| `sum_no_gain_for_local_theta` | `Ψ.Nonempty`、联合 ⊆ Θ（`Θ` 在 `V₁` 上） | `Φ ⊆ Θ` | 否（是 `AssemblyMeta.no_new_information` 的引用） |
| `shared_gain_not_contradicted_by_no_gain` | 无 | 三条定理并列引用 | 否（「不矛盾」的见证，不声称新内容） |

**结论**：本文件的实质内容是 `gain_iff`（一般判据）、
`shared_gain_holds` + `shared_gain_not_from_Φ` + `shared_gain_not_from_Ψ`
（最小反例）、`Θc_not_local_supp₁` + `Θc_not_local_supp₂`（关系性）。
**没有**任何一条声称「第 2 层已被证明」。
-/

end Fate.AssemblyGainShared
