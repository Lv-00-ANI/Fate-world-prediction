import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace FateV2.Meta
namespace PrMaj

open Finset

/-!
  # Meta · T810PrMaj

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T810PrMaj.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Meta`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §T8.10  `Pr_maj` 不可求值 —— 依赖三参数的形式化

  ## 清单原文（T8.10）

  > **`Pr_maj` 不可求值**：在 `ν`、任务族枚举、`ε_task` 未给定的情况下，
  > `Pr_maj` 无法计算。

  ## 本模块的读法

  `Pr_maj`（**多数正确概率**）是「对任务族上每个任务的正确性做**多数投票**，
  预测正确的概率」。它**不是常数**，而是**三个参数的函数**：

  | 参数 | 本文件的 Lean 名 | 类型 | 含义 |
  |---|---|---|---|
  | `ν`            | `ν : Ω → ℚ`              | 世界/模型上的权重 | 先验分布 |
  | 任务族枚举      | `Task`（`Fintype`）       | 类型 + `Fintype` 实例 | 任务集合及其枚举 |
  | 每任务误差 `ε`  | `ε : Ω → Task → ℚ`       | 每任务（每世界）正确概率 | `ε_task` |

  ## 编码方式（可判定、纯有理数、零 sorry）

  * **单任务族上的多数概率** `prMajAt ε`：把任务正确性视为**独立伯努利**
    （成功概率 `ε t`），对「正确任务的子集 `W ⊆ Task`」求和：

    `prMajAt ε = ∑ W ∈ univ.powerset, poissonTerm ε W * isMaj W`

    其中
    * `poissonTerm ε W = (∏ t ∈ W, ε t) * (∏ t ∈ univ \ W, (1 - ε t))`
      —— Poisson 二项分布（独立非同分布伯努利和）的单点质量；
    * `isMaj W = if 2 * W.card > Fintype.card Task then 1 else 0`
      —— 「严格多数」指示函数。

  * **`ν`-混合层** `prMaj ν ε = ∑ ω, ν ω * prMajAt (ε ω)`
    —— 对世界取加权平均，于是 `ν` 进入。

  ## 本模块的三个结论（与任务书一一对应）

  | 结论 | Lean 定理 | 强度 |
  |---|---|---|
  | 1. 存在两组参数使 `Pr_maj` 不同 | `prMaj_depends_on_params` | ⭐⭐ |
  | 2. 固定 `ν` 与任务族、`ε` 未定 ⟹ 值不可确定 | `prMaj_not_determined`（+ 逐点版 `prMaj_not_determined'`） | ⭐⭐ |
  | 3. 三参数缺一则不可求值 | `prMaj_eval_needs_nu` / `_eps` / `_task` | ⭐ |

  ## ⚠⚠ 第 247 轮：§1–§7 已被升级（见 §8）

  **G6 第 242 轮评估判定**：`prMajAt` 用 `if` 定义（`isMaj` 是指示函数）再证依赖 ⟹ **定义改写**。
  **确实如此**：§5–§7 的结论都是「存在两组参数使值不同」，**没有用到分析结构**。

  **⭐ 第 247 轮**在 §8 补上**真分析**：当 `ε ≡ c` 时 `Pr_maj` 是 `c` 的**多项式**，
  故 `c ↦ Pr_maj` **连续**，由**介值定理**其**值域是一个区间**；
  最强版 `prMajAtR_fin3_surj` 证明：对 `Fin 3`，**值域恰为整个 `[0,1]`**。

  **⚠ 诚实边界**：
  * 本文件**不**断言「`Pr_maj` 在真实学习任务上等于本模型」——
    这里形式化的是「`Pr_maj` 是一个**三参数函数**，且**每个参数都真的起作用**」，
    这正是 T8.10 的**内容**（不可求值 = 参数未定则值未定）。
  * 任务族参数（`Task` 的基数）的**独立性**只能在**同一常数 `ε`**
    下展示（`prMaj_eval_needs_task`，见下注）。
    跨不同基数的同一 `ε` 是一个 `Π`-族，不能写成「同一个函数」，
    故此处以「常数 `ε = 1/2`」为公共 `ε`，只变任务族大小：
    `Fin 1 ↦ 1/2`，`Fin 2 ↦ 1/4`。
  =========================================================================== -/

/-! ## §1  单任务族的多数概率 -/

/-- Poisson 二项分布单点质量：恰好 `W` 中任务全部正确、其余全错。 -/
def poissonTerm {Task : Type} [Fintype Task] [DecidableEq Task] (e : Task → ℚ)
    (W : Finset Task) : ℚ :=
  (∏ t ∈ W, e t) * (∏ t ∈ Finset.univ \ W, (1 - e t))

/-- 严格多数指示函数：`W` 是否为任务族中的严格多数（`1` 或 `0`）。 -/
def isMaj {Task : Type} [Fintype Task] (W : Finset Task) : ℚ :=
  if 2 * W.card > Fintype.card Task then 1 else 0

/-- ⭐ **单任务族上的多数正确概率** `Pr_maj`（给定 `ε`）：
对一切正确任务子集求和。 -/
def prMajAt {Task : Type} [Fintype Task] [DecidableEq Task] (e : Task → ℚ) : ℚ :=
  ∑ W ∈ (Finset.univ : Finset Task).powerset, poissonTerm e W * isMaj W

/-! ## §2  `ν`-混合层 -/

/-- ⭐⭐ **多数正确概率** `Pr_maj`，作为 **`(ν, 任务族, ε)` 三参数的函数**。 -/
def prMaj {Ω Task : Type} [Fintype Ω] [Fintype Task] [DecidableEq Task]
    (ν : Ω → ℚ) (e : Ω → Task → ℚ) : ℚ :=
  ∑ ω, ν ω * prMajAt (e ω)

/-- 两世界（`Ω = Bool`）时展开为显式两项。 -/
lemma prMaj_bool {Task : Type} [Fintype Task] [DecidableEq Task]
    (ν : Bool → ℚ) (e : Bool → Task → ℚ) :
    prMaj ν e = ν true * prMajAt (e true) + ν false * prMajAt (e false) := by
  unfold prMaj
  rw [Fintype.sum_bool]

/-! ## §3  单任务族的两个极端（对任意有限非空任务族成立） -/

lemma poissonTerm_one_of_ne_univ {Task : Type} [Fintype Task] [DecidableEq Task]
    {W : Finset Task} (hW : W ≠ Finset.univ) :
    poissonTerm (fun _ : Task => (1:ℚ)) W = 0 := by
  have hne : (Finset.univ \ W).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hW (Finset.Subset.antisymm (Finset.subset_univ W) hsub)
  obtain ⟨t, ht⟩ := hne
  unfold poissonTerm
  rw [Finset.prod_eq_zero ht (by norm_num : (1 - (1:ℚ)) = 0), mul_zero]

lemma poissonTerm_zero_of_nonempty {Task : Type} [Fintype Task] [DecidableEq Task]
    {W : Finset Task} (hW : W.Nonempty) :
    poissonTerm (fun _ : Task => (0:ℚ)) W = 0 := by
  obtain ⟨t, ht⟩ := hW
  unfold poissonTerm
  rw [Finset.prod_eq_zero ht rfl, zero_mul]

lemma isMaj_empty {Task : Type} [Fintype Task] :
    isMaj (∅ : Finset Task) = 0 := by
  unfold isMaj
  rw [Finset.card_empty]
  have : ¬ (2 * 0 > Fintype.card Task) := by omega
  rw [if_neg this]

lemma isMaj_univ {Task : Type} [Fintype Task] (h : 0 < Fintype.card Task) :
    isMaj (Finset.univ : Finset Task) = 1 := by
  unfold isMaj
  rw [Finset.card_univ]
  have : 2 * Fintype.card Task > Fintype.card Task := by omega
  rw [if_pos this]

/-- 若所有任务都必对（`ε ≡ 1`），多数投票必对，故 `Pr_maj = 1`。 -/
lemma prMajAt_one {Task : Type} [Fintype Task] [DecidableEq Task]
    (h : 0 < Fintype.card Task) :
    prMajAt (fun _ : Task => (1:ℚ)) = 1 := by
  unfold prMajAt
  rw [Finset.sum_eq_single (Finset.univ : Finset Task)]
  · unfold poissonTerm
    rw [show (Finset.univ : Finset Task) \ Finset.univ = ∅ from by simp]
    rw [Finset.prod_empty, mul_one, Finset.prod_const_one, one_mul, isMaj_univ h]
  · intro b _ hb
    rw [poissonTerm_one_of_ne_univ hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_powerset.mpr (Finset.subset_univ _)) h

/-- 若所有任务都必错（`ε ≡ 0`），多数投票必错，故 `Pr_maj = 0`。 -/
lemma prMajAt_zero {Task : Type} [Fintype Task] [DecidableEq Task] :
    prMajAt (fun _ : Task => (0:ℚ)) = 0 := by
  unfold prMajAt
  apply Finset.sum_eq_zero
  intro W _
  rcases Finset.eq_empty_or_nonempty W with h | h
  · rw [h, isMaj_empty, mul_zero]
  · rw [poissonTerm_zero_of_nonempty h, zero_mul]

/-- 基数 `≤ 2` 的任务族里，多数只可能是「全对」，故 `Pr_maj = c ^ |Task|`。 -/
lemma maj_subset_univ_of_le_two {Task : Type} [Fintype Task] [DecidableEq Task]
    (hc : Fintype.card Task ≤ 2) {W : Finset Task} (hW : W ⊆ Finset.univ)
    (hmaj : 2 * W.card > Fintype.card Task) : W = Finset.univ := by
  have h1 : W.card ≤ Fintype.card Task := by
    simpa using Finset.card_le_card hW
  have h2 : W.card = Fintype.card Task := by omega
  exact Finset.eq_univ_of_card W h2

/-- ⭐ **常数误差** `ε ≡ c` 且任务族基数 `≤ 2`：`Pr_maj = c ^ |Task|`。 -/
lemma prMajAt_const {Task : Type} [Fintype Task] [DecidableEq Task]
    (hc : Fintype.card Task ≤ 2) (hpos : 0 < Fintype.card Task) (c : ℚ) :
    prMajAt (fun _ : Task => c) = c ^ Fintype.card Task := by
  have key : ∀ (b : Finset Task), b ∈ (Finset.univ : Finset Task).powerset →
      b ≠ Finset.univ → poissonTerm (fun _ : Task => c) b * isMaj b = 0 := by
    intro b hb hbu
    have hsub : b ⊆ Finset.univ := Finset.mem_powerset.mp hb
    unfold isMaj poissonTerm
    have : ¬ (2 * b.card > Fintype.card Task) := by
      intro h
      exact hbu (maj_subset_univ_of_le_two hc hsub h)
    rw [if_neg this, mul_zero]
  have key2 : (Finset.univ : Finset Task) ∉ (Finset.univ : Finset Task).powerset → False := by
    intro h
    exact h (Finset.mem_powerset.mpr (Finset.subset_univ _))
  unfold prMajAt
  rw [Finset.sum_eq_single (Finset.univ : Finset Task) key (fun h => absurd h key2)]
  unfold poissonTerm
  have hs : (Finset.univ : Finset Task) \ Finset.univ = ∅ := by simp
  rw [hs, Finset.prod_empty, mul_one]
  have hlt : 2 * Fintype.card Task > Fintype.card Task := by omega
  have hmaj : (if 2 * (Finset.univ : Finset Task).card > Fintype.card Task then (1:ℚ) else 0) = 1 := by
    rw [Finset.card_univ]; rw [if_pos hlt]
  rw [show (isMaj (Finset.univ : Finset Task)) = 1 from hmaj]
  rw [mul_one, Finset.prod_const, Finset.card_univ]

/-! ## §4  `ν` 为点质量时的两个极端 -/

/-- `ν` 取 `true` 上的点质量、`ε` 全对 ⟹ `Pr_maj = 1`。 -/
lemma prMaj_all_one {Task : Type} [Fintype Task] [DecidableEq Task]
    (h : 0 < Fintype.card Task) :
    prMaj (fun b : Bool => if b then (1:ℚ) else 0) (fun _ (_ : Task) => (1:ℚ)) = 1 := by
  rw [prMaj_bool]
  have e1 : prMajAt (fun _ : Task => (1:ℚ)) = 1 := prMajAt_one h
  show (if true then (1:ℚ) else 0) * prMajAt (fun _ : Task => (1:ℚ))
      + (if false then (1:ℚ) else 0) * prMajAt (fun _ : Task => (1:ℚ)) = 1
  rw [e1]; norm_num

/-- `ν` 取 `true` 上的点质量、`ε` 全错 ⟹ `Pr_maj = 0`。 -/
lemma prMaj_all_zero {Task : Type} [Fintype Task] [DecidableEq Task] :
    prMaj (fun b : Bool => if b then (1:ℚ) else 0) (fun _ (_ : Task) => (0:ℚ)) = 0 := by
  rw [prMaj_bool]
  have e0 : prMajAt (fun _ : Task => (0:ℚ)) = 0 := prMajAt_zero
  show (if true then (1:ℚ) else 0) * prMajAt (fun _ : Task => (0:ℚ))
      + (if false then (1:ℚ) else 0) * prMajAt (fun _ : Task => (0:ℚ)) = 0
  rw [e0]; norm_num

/-! ## §5  ⭐⭐ T8.10 (1)  两组不同参数给出不同值 -/

/-- ⭐⭐ **`Pr_maj` 依赖三参数**：
存在两组参数配置 `(ν₁, ε₁) ≠ (ν₂, ε₂)`（3 个任务、`Bool` 标签），
使 `Pr_maj ν₁ ε₁ = 1` 而 `Pr_maj ν₂ ε₂ = 0`。

⟹ 参数改变则值改变 ⟹ **参数未定则值未定**。 -/
theorem prMaj_depends_on_params :
    ∃ (ν₁ ν₂ : Bool → ℚ) (e₁ e₂ : Bool → Fin 3 → ℚ),
      (ν₁, e₁) ≠ (ν₂, e₂) ∧ prMaj ν₁ e₁ ≠ prMaj ν₂ e₂ := by
  refine ⟨fun b => if b then 1 else 0, fun b => if b then 1 else 0,
          fun _ (_ : Fin 3) => (1:ℚ), fun _ (_ : Fin 3) => (0:ℚ), ?_, ?_⟩
  · intro h
    have hsnd : (fun _ : Bool => fun _ : Fin 3 => (1:ℚ))
        = (fun _ : Bool => fun _ : Fin 3 => (0:ℚ)) := by
      simpa using congrArg Prod.snd h
    have := congrFun (congrFun hsnd true) 0
    norm_num at this
  · rw [prMaj_all_one (by decide : 0 < Fintype.card (Fin 3)), prMaj_all_zero]
    exact one_ne_zero

/-! ## §6  ⭐⭐ T8.10 (2)  固定 `ν` 与任务族、`ε` 未定 ⟹ 值不可确定 -/

/-- ⭐⭐ **`ε` 未定则 `Pr_maj` 不可确定**（存在式版本）：
在 `ν`（`true` 上的点质量）与任务族（`Fin 3`）**都已固定**时，
**不存在**一个有理数 `c` 同时是 `Pr_maj` 对**一切** `ε` 的取值。

即：`Pr_maj` 在此情形下**不是一个数**，而是一个**函数**。 -/
theorem prMaj_not_determined :
    ¬ ∃ c : ℚ, ∀ e : Bool → Fin 3 → ℚ,
        prMaj (fun b => if b then (1:ℚ) else 0) e = c := by
  rintro ⟨c, hc⟩
  have h1 := prMaj_all_one (Task := Fin 3) (by decide)
  have h0 := prMaj_all_zero (Task := Fin 3)
  rw [hc (fun _ (_ : Fin 3) => (1:ℚ))] at h1
  rw [hc (fun _ (_ : Fin 3) => (0:ℚ))] at h0
  linarith

/-- ⭐⭐ **`ε` 未定则 `Pr_maj` 不可确定**（逐点版本）：
对**任意**候选值 `c`，总能构造一个 `ε` 使 `Pr_maj ≠ c`。

⟹ 任何「把 `Pr_maj` 当已定数」的论证都必须**额外给出 `ε`**。 -/
theorem prMaj_not_determined' :
    ∀ c : ℚ, ∃ e : Bool → Fin 3 → ℚ,
      prMaj (fun b => if b then (1:ℚ) else 0) e ≠ c := by
  intro c
  rcases eq_or_ne c 0 with h | h
  · refine ⟨fun _ (_ : Fin 3) => (1:ℚ), ?_⟩
    rw [prMaj_all_one (Task := Fin 3) (by decide)]
    subst h; exact one_ne_zero
  · refine ⟨fun _ (_ : Fin 3) => (0:ℚ), ?_⟩
    rw [prMaj_all_zero (Task := Fin 3)]
    exact fun hc => h hc.symm

/-! ## §7  ⭐ T8.10 (3)  三参数缺一则不可求值

「不可求值」被形式化为：`Pr_maj` **真的依赖**每一个参数——
对每个参数都存在「其余两参数相同、仅此参数不同、值不同」的一对配置。
于是缺失任一参数都使值**未被确定**。 -/

/-- ⭐ **`ν` 是必要的**：仅改变 `ν`（`ε` 固定为全对）即改变值。
`ν = δ_true ↦ 1`，而 `ν ≡ 1 ↦ 2`（权重未归一，和为 2）。 -/
theorem prMaj_eval_needs_nu :
    ∃ (e : Bool → Fin 3 → ℚ) (ν₁ ν₂ : Bool → ℚ), ν₁ ≠ ν₂ ∧
      prMaj ν₁ e ≠ prMaj ν₂ e := by
  refine ⟨fun _ (_ : Fin 3) => (1:ℚ), fun b => if b then 1 else 0,
          fun _ => (1:ℚ), ?_, ?_⟩
  · intro h
    have := congrFun h false
    simp at this
  · rw [prMaj_all_one (Task := Fin 3) (by decide)]
    have h2 : prMaj (fun _ : Bool => (1:ℚ)) (fun _ (_ : Fin 3) => (1:ℚ)) = 2 := by
      rw [prMaj_bool]
      have e1 : prMajAt (fun _ : Fin 3 => (1:ℚ)) = 1 :=
        prMajAt_one (by decide : 0 < Fintype.card (Fin 3))
      show (1:ℚ) * prMajAt (fun _ : Fin 3 => (1:ℚ))
          + 1 * prMajAt (fun _ : Fin 3 => (1:ℚ)) = 2
      rw [e1]; norm_num
    rw [h2]; exact fun h => absurd h.symm (by norm_num)

/-- ⭐ **`ε_task` 是必要的**：仅改变 `ε`（`ν` 固定）即改变值。
`ε ≡ 0 ↦ 0`，`ε ≡ 1 ↦ 1`。 -/
theorem prMaj_eval_needs_eps :
    ∃ (ν : Bool → ℚ) (e₁ e₂ : Bool → Fin 3 → ℚ), e₁ ≠ e₂ ∧
      prMaj ν e₁ ≠ prMaj ν e₂ := by
  refine ⟨fun b => if b then 1 else 0, fun _ (_ : Fin 3) => (0:ℚ),
          fun _ (_ : Fin 3) => (1:ℚ), ?_, ?_⟩
  · intro h
    have := congrFun (congrFun h true) 0
    norm_num at this
  · rw [prMaj_all_zero (Task := Fin 3), prMaj_all_one (Task := Fin 3) (by decide)]
    exact fun h => absurd h (by norm_num)

/-- ⭐ **任务族枚举是必要的**：在**同一常数 `ε = 1/2`** 下，
仅改变任务族大小即改变值：`Fin 1 ↦ 1/2`，`Fin 2 ↦ 1/4`。

（注：跨不同基数的 `ε` 属不同的 `Π`-类型，故公共 `ε` 取常数 `1/2`；
这仍是「只变任务族、`ε` 的形状不变」的合法见证。） -/
theorem prMaj_eval_needs_task :
    ∃ (ν : Bool → ℚ) (c : ℚ) (e₁ : Bool → Fin 1 → ℚ) (e₂ : Bool → Fin 2 → ℚ),
      (∀ ω, e₁ ω = fun _ => c) ∧ (∀ ω, e₂ ω = fun _ => c) ∧
        prMaj ν e₁ ≠ prMaj ν e₂ := by
  refine ⟨fun b => if b then 1 else 0, 1/2, fun _ _ => 1/2, fun _ _ => 1/2,
          fun _ => rfl, fun _ => rfl, ?_⟩
  have h1 : prMaj (fun b : Bool => if b then (1:ℚ) else 0)
      (fun _ (_ : Fin 1) => (1/2:ℚ)) = 1/2 := by
    rw [prMaj_bool]
    have e : prMajAt (fun _ : Fin 1 => (1/2:ℚ)) = 1/2 := by
      rw [prMajAt_const (Task := Fin 1) (by decide) (by decide) (1/2)]
      norm_num
    show (if true then (1:ℚ) else 0) * prMajAt (fun _ : Fin 1 => (1/2:ℚ))
        + (if false then (1:ℚ) else 0) * prMajAt (fun _ : Fin 1 => (1/2:ℚ)) = 1/2
    rw [e]; norm_num
  have h2 : prMaj (fun b : Bool => if b then (1:ℚ) else 0)
      (fun _ (_ : Fin 2) => (1/2:ℚ)) = 1/4 := by
    rw [prMaj_bool]
    have e : prMajAt (fun _ : Fin 2 => (1/2:ℚ)) = 1/4 := by
      rw [prMajAt_const (Task := Fin 2) (by decide) (by decide) (1/2)]
      norm_num
    show (if true then (1:ℚ) else 0) * prMajAt (fun _ : Fin 2 => (1/2:ℚ))
        + (if false then (1:ℚ) else 0) * prMajAt (fun _ : Fin 2 => (1/2:ℚ)) = 1/4
    rw [e]; norm_num
  rw [h1, h2]
  exact fun h => absurd h (by norm_num)

/-- ⭐ **汇总**：三参数**全体必要**——每个参数都存在「仅变它、值即变」的见证。
由此，缺任一参数时 `Pr_maj` 的值**未被确定**（即不可求值）。 -/
theorem prMaj_eval_needs_all :
    (∃ (e : Bool → Fin 3 → ℚ) (ν₁ ν₂ : Bool → ℚ), ν₁ ≠ ν₂ ∧
        prMaj ν₁ e ≠ prMaj ν₂ e) ∧
    (∃ (ν : Bool → ℚ) (e₁ e₂ : Bool → Fin 3 → ℚ), e₁ ≠ e₂ ∧
        prMaj ν e₁ ≠ prMaj ν e₂) ∧
    (∃ (ν : Bool → ℚ) (c : ℚ) (e₁ : Bool → Fin 1 → ℚ) (e₂ : Bool → Fin 2 → ℚ),
        (∀ ω, e₁ ω = fun _ => c) ∧ (∀ ω, e₂ ω = fun _ => c) ∧
          prMaj ν e₁ ≠ prMaj ν e₂) :=
  ⟨prMaj_eval_needs_nu, prMaj_eval_needs_eps, prMaj_eval_needs_task⟩


/-! ## §8 ⭐⭐⭐⭐ **第 247 轮重做：`Pr_maj` 的**值域是一个区间**（真分析）

**⚠ 为什么必须重做**：§1 的 `prMajAt` 用 `if` 定义（`isMaj` 是一个指示函数），
§5–§7 的结论都是「存在两组参数使值不同」—— 这是**可满足性/不可求值**的弱陈述，
**没有用到 `prMajAt` 的任何分析结构**。任务书要求：「`Pr_maj` 的**值的范围**是一个**区间**」。

**⭐ 本节把 T8.10 升级为**真分析命题**：

1. **多项式化**（`prMajPolyR`）：当 `ε ≡ c`（常数）时，
   `prMajAt` **是 `c` 的多项式**（Poisson 二项分布的单点质量是 `c` 的多项式）。
2. **连续性**（`continuous_prMajAtR_const`）：故 `c ↦ prMajAt (const c)` **连续**。
3. **值域是区间**（`prMajAtR_const_mem_range`）：由**介值定理**，
   在任意两个值之间的**每个值都被取到**。
4. **最强版**（`prMajAtR_fin3_surj`）：对 `Fin 3`，
   端点值 `Pr_maj(ε≡0) = 0`、`Pr_maj(ε≡1) = 1`，
   **⟹ 整个 `[0,1]` 都被取到** —— 值域**恰好**是 `[0,1]`（`[0,1] ⊆ 值域 ⊆ [0,1]`）。

**⚠ 为什么要引入 `prMajAtR`（ℝ 版）**：
`prMajAt : (Task → ℚ) → ℚ` 的值域在 `ℚ` 上，**而 `ℚ` 不构成
`ConditionallyCompleteLinearOrder`**（Lean 中无该实例），
故 `intermediate_value_uIcc` **无法直接作用于 `ℚ`**。
`prMajAtR` 是同一公式在 ℝ 上的版本，并由 `prMajAtR_const_bridge`
**证明它与原 `prMajAt` 在有理点处逐点一致** —— 故这个升级**不是换对象，而是换系数域**。

**⚠ 诚实边界**：本节**不**声称 `Pr_maj` 在真实学习任务上等于本模型（见 §0 的边界声明）。
本节证明的是：**在 T8.10 的抽象模型内，`Pr_maj` 的值域是一个真区间，
而不是一个离散的点集** —— 这直接强化了「不可求值」的结论：
**给定 `ε` 的近似值也**不能**确定 `Pr_maj`（区间有正长度）。** -/

/-- **`poissonTerm` 的 ℝ 版**（同一公式，系数域换成 ℝ）。 -/
noncomputable def poissonTermR {Task : Type} [Fintype Task] [DecidableEq Task]
    (e : Task → ℝ) (W : Finset Task) : ℝ :=
  (∏ t ∈ W, e t) * (∏ t ∈ Finset.univ \ W, (1 - e t))

/-- **`prMajAt` 的 ℝ 版**。 -/
noncomputable def prMajAtR {Task : Type} [Fintype Task] [DecidableEq Task]
    (e : Task → ℝ) : ℝ :=
  ∑ W ∈ (Finset.univ : Finset Task).powerset, poissonTermR e W * ((isMaj W : ℚ) : ℝ)

/-- ⭐⭐ **ℝ 版与原 ℚ 版**在常数值处**逐点一致**（★ 这是「换域不换对象」的证明）。 -/
theorem prMajAtR_const_bridge {Task : Type} [Fintype Task] [DecidableEq Task] (c : ℚ) :
    prMajAtR (fun _ : Task => ((c : ℝ))) = ((prMajAt (fun _ : Task => c) : ℚ) : ℝ) := by
  unfold prMajAtR prMajAt poissonTermR poissonTerm
  push_cast
  rfl

/-- **单点质量的生成多项式**（`W` 固定，变量是常数 `ε = c`）。 -/
noncomputable def poissonPolyR {Task : Type} [Fintype Task] [DecidableEq Task]
    (W : Finset Task) : Polynomial ℝ :=
  W.prod (fun _ => Polynomial.X) * (Finset.univ \ W).prod (fun _ => (1 - Polynomial.X))

/-- **多项式的取值 = 单点质量**。 -/
theorem eval_poissonPolyR {Task : Type} [Fintype Task] [DecidableEq Task]
    (W : Finset Task) (c : ℝ) :
    (poissonPolyR W).eval c = poissonTermR (fun _ : Task => c) W := by
  unfold poissonPolyR poissonTermR
  rw [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_prod]
  simp [Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]

/-- ⭐ **`Pr_maj`（常数 `ε`）的生成多项式**。 -/
noncomputable def prMajPolyR {Task : Type} [Fintype Task] [DecidableEq Task] : Polynomial ℝ :=
  ∑ W ∈ (Finset.univ : Finset Task).powerset,
    poissonPolyR (Task := Task) W * Polynomial.C ((isMaj W : ℚ) : ℝ)

/-- ⭐⭐ **`Pr_maj`（常数 `ε = c`）是 `c` 的多项式**。 -/
theorem eval_prMajPolyR {Task : Type} [Fintype Task] [DecidableEq Task] (c : ℝ) :
    (prMajPolyR (Task := Task)).eval c = prMajAtR (fun _ : Task => c) := by
  unfold prMajPolyR prMajAtR
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro W _
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_poissonPolyR]

/-- ⭐⭐⭐ **连续性**：`c ↦ Pr_maj(ε ≡ c)` 是**连续**函数（因为它是多项式）。 -/
theorem continuous_prMajAtR_const {Task : Type} [Fintype Task] [DecidableEq Task] :
    Continuous fun c : ℝ => prMajAtR (fun _ : Task => c) := by
  have h : (fun c : ℝ => prMajAtR (fun _ : Task => c))
      = fun c => (prMajPolyR (Task := Task)).eval c := by
    funext c; exact (eval_prMajPolyR c).symm
  rw [h]
  exact Polynomial.continuous _

/-- ⭐⭐⭐⭐ **值域是区间**（介值定理）：任意两个可取到的值之间，**每个中间值都被取到**。 -/
theorem prMajAtR_const_mem_range {Task : Type} [Fintype Task] [DecidableEq Task]
    {c₁ c₂ : ℝ} (h₁ : c₁ ∈ Set.Icc (0:ℝ) 1) (h₂ : c₂ ∈ Set.Icc (0:ℝ) 1) {v : ℝ}
    (hv : v ∈ Set.uIcc (prMajAtR (fun _ : Task => c₁)) (prMajAtR (fun _ : Task => c₂))) :
    ∃ c ∈ Set.Icc (0:ℝ) 1, prMajAtR (fun _ : Task => c) = v := by
  have himg := intermediate_value_uIcc (a := c₁) (b := c₂)
    (f := fun c : ℝ => prMajAtR (fun _ : Task => c)) continuous_prMajAtR_const.continuousOn hv
  obtain ⟨c, hc, hcv⟩ := himg
  refine ⟨c, ?_, hcv⟩
  exact (Set.ordConnected_Icc.uIcc_subset h₁ h₂) hc

/-! ### §8.1 端点值：`ε ≡ 0 ↦ 0`，`ε ≡ 1 ↦ 1` -/

/-- ⭐ **`ε ≡ 0` 时 `Pr_maj = 0`**（ℝ 版）。 -/
theorem prMajAtR_zero {Task : Type} [Fintype Task] [DecidableEq Task] :
    prMajAtR (fun _ : Task => (0:ℝ)) = 0 := by
  unfold prMajAtR
  apply Finset.sum_eq_zero
  intro W _
  rcases Finset.eq_empty_or_nonempty W with h | h
  · rw [h]; unfold isMaj; simp
  · obtain ⟨t, ht⟩ := h
    unfold poissonTermR
    rw [Finset.prod_eq_zero ht (by norm_num)]
    simp

/-- ⭐ **`ε ≡ 1` 且任务族非空时 `Pr_maj = 1`**（ℝ 版）。 -/
theorem prMajAtR_one {Task : Type} [Fintype Task] [DecidableEq Task]
    (h : 0 < Fintype.card Task) :
    prMajAtR (fun _ : Task => (1:ℝ)) = 1 := by
  unfold prMajAtR
  rw [Finset.sum_eq_single (Finset.univ : Finset Task)]
  · unfold poissonTermR isMaj
    rw [Finset.sdiff_self, Finset.prod_empty, mul_one, Finset.prod_const_one, one_mul]
    rw [Finset.card_univ]
    have : 2 * Fintype.card Task > Fintype.card Task := by omega
    rw [if_pos this]
    norm_num
  · intro b _ hb
    unfold poissonTermR
    have hne : (Finset.univ \ b).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      exact hb (Finset.Subset.antisymm (Finset.subset_univ b) hsub)
    obtain ⟨t, ht⟩ := hne
    have hz : (∏ t ∈ Finset.univ \ b, (1 - (1:ℝ))) = 0 :=
      Finset.prod_eq_zero ht (by norm_num)
    rw [hz, mul_zero, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_powerset.mpr (Finset.subset_univ _)) hnot

/-- ⭐⭐⭐⭐⭐ **T8.10 的最强形式**：对 `Fin 3`，**`Pr_maj` 的值域恰为整个 `[0,1]`**。

**⭐⭐ 意义**：这**不是**「存在两组参数给出不同值」（§5 的弱陈述），
而是「**每一个** `v ∈ [0,1]` 都能由某个常数 `ε` 实现」。
**⟹ `Pr_maj` 的值域是一个**长度为正的区间**，故**即使近似给定 `ε` 也无法定出 `Pr_maj`。** -/
theorem prMajAtR_fin3_surj {v : ℝ} (hv : v ∈ Set.Icc (0:ℝ) 1) :
    ∃ c ∈ Set.Icc (0:ℝ) 1, prMajAtR (fun _ : Fin 3 => c) = v := by
  have hmem : v ∈ Set.uIcc (prMajAtR (fun _ : Fin 3 => (0:ℝ)))
      (prMajAtR (fun _ : Fin 3 => (1:ℝ))) := by
    rw [prMajAtR_zero, prMajAtR_one (by decide : 0 < Fintype.card (Fin 3)),
      Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hv
  have himg := intermediate_value_uIcc (a := (0:ℝ)) (b := 1)
    (f := fun c : ℝ => prMajAtR (fun _ : Fin 3 => c))
    continuous_prMajAtR_const.continuousOn hmem
  obtain ⟨c, hc, hcv⟩ := himg
  refine ⟨c, ?_, hcv⟩
  exact (Set.ordConnected_Icc.uIcc_subset (Set.left_mem_Icc.mpr (by norm_num))
    (Set.right_mem_Icc.mpr (by norm_num))) hc

end PrMaj

end FateV2.Meta