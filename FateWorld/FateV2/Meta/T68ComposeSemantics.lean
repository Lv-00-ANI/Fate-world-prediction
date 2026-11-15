/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate._r230_B4`（第 230 轮 · 子任务 B4）
条目：**T6.8 —— 组合的语义未定 ⇒ 组合无计算含义**

---------------------------------------------------------------------------
清单原文（T6.8）
---------------------------------------------------------------------------
> **组合的语义未定 ⇒ 组合无计算含义**：在开放问题 5.1（`∘` 的语义未定）
> 未解决之前，`R₁ ∘ R₂` 不产生可判定的输出。

---------------------------------------------------------------------------
本条目的**性质**：这是一条 **元层面（meta-level）** 的陈述
---------------------------------------------------------------------------
它**不是**关于某个具体 `∘` 的定理，而是关于
**「`∘` 这一记号的公理刻画是否足以确定它做什么计算」** 的定理。

因而不可能用「取一个具体的 `∘`，算一个具体的值」来证——
那样只证明了**某个**解释成立，与「语义未定」正相反。

---------------------------------------------------------------------------
⭐⭐ 形式化方向：**语义不足决定性（semantic underdetermination）**
---------------------------------------------------------------------------
把「`∘` 的语义未定」**正面地**形式化为**公理不足以唯一确定运算**：

  **存在两个不同的二元运算 `op₁ op₂`，都满足组合算子被要求满足的全部公理。**

于是任何仅由这些公理出发的推导，都无法把 `op₁` 与 `op₂` 区分开；
`R₁ ∘ R₂` 因此**没有**被公理确定的计算含义。

**⭐ 公理取自本仓库已冻结的接口层**（`Fate.ComposeOperator`，
该文件的 §1–§2 明确声明「接口层语义中立，对应开放问题 5.1 的未决状态」）：

  * `ComposeAssoc`       —— 结合律；
  * `ComposeLeftUnit`    —— 左幺元律（`e ∘ x = x`）；
  * `ComposeRightUnit`   —— 右幺元律（`x ∘ e = x`）；
  * **封闭性**（规格 A3，`R₁ ∘ ⋯ ∘ Rₙ ∈ ℛ`）。

`_r230_B4.lean` 不 import 该文件（它在主库里，会牵入下游依赖），
故以**同名的局部结构** `ComposeAxioms` **逐字重述**这四条公理。
重述与 `Fate.ComposeOperator.ComposeLaws` 一一对应（对照见 §1 注释）。

---------------------------------------------------------------------------
⭐⭐ 关键构造（**零硬编码**，依作者裁决 Q-1）
---------------------------------------------------------------------------
**不**直接把 `(· + ·)` 与 `(· * ·)` 写死在定理里（那会在 `ℕ` 上**硬编码**
两个具体运算）。而是**按参数**证明一个一般化的引理：

  **`underdetermined_of_two_models`**：
    只要给出载体 `α`、两个**互不相同**的运算 `op₁ op₂`、各自满足公理的**见证**，
    就得到 `¬ ∃! op, Axioms op`。

然后把 `ℕ` + `+` / `*` 作为**一个实例**代入（§4），
并额外给出一个 `Bool` + `∨` / `∧` 的实例（§5）以显示定理的**参数性**。

---------------------------------------------------------------------------
本文件的产出
---------------------------------------------------------------------------
| # | 定理 | 内容 |
|---|---|---|
| 1 | ⭐⭐⭐ `compose_semantics_underdetermined` | 存在两个不同的 `op₁ op₂` 都满足组合公理 |
| 2 | ⭐⭐ `no_unique_semantics` | 由上一条推出 `¬ ∃! op, ComposeAxioms op` |
| 3 | ⭐ `op_differ_witness` | 存在具体 `a b` 使 `op₁ a b ≠ op₂ a b` |
| 4 | ⭐⭐ `underdetermined_of_two_models` | **第 2 条的参数化母定理**（不依赖 `ℕ`） |
| 5 | ⭐⭐⭐ `compose_no_computational_meaning` | **T6.8 的元层面读法**：任一 `op` 满足公理，都不能主张它是 `∘` 的语义 |

**⚠ 零 `sorry`、零 `admit`、零 `axiom`。**
-/

import Mathlib.Logic.Unique
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

namespace FateV2.Meta.R230B4
/-!
  # Meta · T68ComposeSemantics

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T68ComposeSemantics.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Meta`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  ⭐⭐ **组合算子的公理**（`Fate.ComposeOperator` 接口层的逐字重述）
    =========================================================================== -/

/-- ⭐⭐ **组合算子的公理**（载体 `α` 上一个二元运算 `op` 应满足的全部要求）。

**四条字段与 `Fate.ComposeOperator` 的接口层一一对应**：

| 本结构字段 | `Fate.ComposeOperator` 中对应 | 规格出处 |
|---|---|---|
| `assoc` | `ComposeAssoc op` | 本仓库 §2 接口层（规格未给） |
| `left_unit` | `ComposeLeftUnit op e` | 本仓库 §2 接口层（规格未给） |
| `right_unit` | `ComposeRightUnit op e` | 本仓库 §2 接口层（规格未给） |
| `closed` | 规格 A3 的封闭性（`op a b ∈ α`） | 规格 A3 |

**⚠ 关于 `closed`**：在 Lean 里 `op : α → α → α` 的类型**本身**就蕴含封闭性
（`α = ℛ` 时即 `R₁ ∘ R₂ ∈ ℛ`）。为了**不让这条公理被类型系统悄悄吞掉**，
本结构把它提升为一个**显式字段**——这样「封闭性确实是一条被计价的公理」，
且下游可以显式地引用它（见 `closed_always`）。 -/
structure ComposeAxioms {α : Type*} (op : α → α → α) (e : α) : Prop where
  /-- 结合律：`(a ∘ b) ∘ c = a ∘ (b ∘ c)` -/
  assoc : ∀ a b c : α, op (op a b) c = op a (op b c)
  /-- 左幺元律：`e ∘ a = a` -/
  left_unit : ∀ a : α, op e a = a
  /-- 右幺元律：`a ∘ e = a` -/
  right_unit : ∀ a : α, op a e = a
  /-- 封闭性（规格 A3）：`a ∘ b` 仍是载体中的元素 -/
  closed : ∀ a b : α, op a b ∈ (Set.univ : Set α)

/-- ⭐ **封闭性在 `→` 类型下总是成立**——但它仍是一条**被计价的公理**：
这里证明「显式写入的封闭性字段不是空话」，并且**下游若需要可以直接调用**。 -/
theorem closed_always {α : Type*} (op : α → α → α) :
    ∀ a b : α, op a b ∈ (Set.univ : Set α) :=
  fun _ _ => Set.mem_univ _

/-! ===========================================================================
    §2  ⭐⭐⭐ **存在两个不同的模型**（`ℕ` 上的加法与乘法）
    =========================================================================== -/

/-- ⭐⭐ **`ℕ` 上的加法满足全部组合公理**（单位元 `0`）。 -/
theorem addAxioms : ComposeAxioms (α := ℕ) (· + ·) 0 where
  assoc := Nat.add_assoc
  left_unit := Nat.zero_add
  right_unit := Nat.add_zero
  closed := closed_always _

/-- ⭐⭐ **`ℕ` 上的乘法满足全部组合公理**（单位元 `1`）。 -/
theorem mulAxioms : ComposeAxioms (α := ℕ) (· * ·) 1 where
  assoc := Nat.mul_assoc
  left_unit := Nat.one_mul
  right_unit := Nat.mul_one
  closed := closed_always _

/-- ⭐ **`(· + ·)` 与 `(· * ·)` 是 `ℕ` 上两个不同的二元运算**。

证明方式：它们作为**函数**不同——用外延性，给出取值不同的点 `(2, 2)`：
`2 + 2 = 4` 而 `2 * 2 = 4`……**注意这里两者相等**，
故改用 `(2, 3)`：`2 + 3 = 5` 而 `2 * 3 = 6`。 -/
theorem add_ne_mul : ((· + ·) : ℕ → ℕ → ℕ) ≠ (· * ·) := by
  intro h
  have h23 := congrFun (congrFun h 2) 3
  norm_num at h23

/-- ⭐⭐⭐ **`compose_semantics_underdetermined`**（清单要求 #1）：

**存在两个不同的二元运算 `op₁ op₂`（作用在规则集 `ℛ` 上），
以及各自的单位元 `e₁ e₂`，都满足组合算子的全部公理
（结合律、左右幺元律、封闭性），但 `op₁ ≠ op₂`。**

**取证**：`α := ℕ`（把 `ℕ` 读作规则集 `ℛ` 的一个模型），
`op₁ := (· + ·)`（单位元 `0`），`op₂ := (· * ·)`（单位元 `1`）。
两者都结合、都有双边单位元、都封闭，但**不是同一个运算**。

**⚠ 诚实边界**：本定理说的是「公理**允许**两个不同的运算」，
**不**说「`ℕ` 就是规则集」。规则集的真实载体是什么、`∘` 到底是加法型还是乘法型，
正是开放问题 5.1 未回答的内容——本定理恰恰证明**现有公理不能回答它**。 -/
theorem compose_semantics_underdetermined :
    ∃ (op₁ op₂ : ℕ → ℕ → ℕ) (e₁ e₂ : ℕ),
      op₁ ≠ op₂ ∧
      ComposeAxioms op₁ e₁ ∧ ComposeAxioms op₂ e₂ :=
  ⟨(· + ·), (· * ·), 0, 1, add_ne_mul, addAxioms, mulAxioms⟩

/-! ===========================================================================
    §3  ⭐⭐ **由「两个模型」推出「公理不足以唯一确定」**（参数化母定理）
    =========================================================================== -/

/-- ⭐⭐ **`underdetermined_of_two_models`**（清单要求 #2 的**母定理**）：

**只要载体 `α` 上存在两个不同的运算都满足组合公理，
则「满足组合公理的运算」不唯一：`¬ ∃! op, (∃ e, ComposeAxioms op e)`。**

**⚠ 这是本文件的核心**：它**不提及 `ℕ`、`+`、`*`**，
故是**纯逻辑**的——把「语义未定」化归为
「公理系统的模型类不是单点集」这一标准判据。

**证明要点**（三段）：
1. 设 `∃! op, P op`，取见证 `op₀` 与唯一性 `huniq`；
2. `op₁` 与 `op₂` 都满足 `P`，故都等于 `op₀`（由 `huniq`）；
3. 于是 `op₁ = op₂`，与 `h₁₂ : op₁ ≠ op₂` 矛盾。 -/
theorem underdetermined_of_two_models {α : Type*} :
    ∀ (op₁ op₂ : α → α → α),
      op₁ ≠ op₂ →
      (∃ e, ComposeAxioms op₁ e) →
      (∃ e, ComposeAxioms op₂ e) →
      ¬ ∃! op : α → α → α, ∃ e, ComposeAxioms op e := by
  intro op₁ op₂ hne h₁ h₂ huniq
  obtain ⟨op₀, hP₀, huniq₀⟩ := huniq
  have h₁' : op₁ = op₀ := huniq₀ op₁ h₁
  have h₂' : op₂ = op₀ := huniq₀ op₂ h₂
  exact hne (h₁'.trans h₂'.symm)

/-- ⭐⭐ **`no_unique_semantics`**（清单要求 #2）：

**组合算子的公理不足以唯一确定 `∘`**：
不存在**唯一**的二元运算满足这些公理。

**★ 这是 T6.8 的正面形式化**：若公理能唯一确定 `∘`，
则 `R₁ ∘ R₂` 就有确定的计算含义（照那个唯一的 `op` 算）；
公理**不**唯一确定它，故 `R₁ ∘ R₂` **不**被公理赋予计算含义。

**★ 与开放问题 5.1 的接口**：只要 5.1 未回答，
任何「`∘` 就是这个 `op`」的主张都**不能由公理推出**——
它只能是**额外假设**（本仓库 `Fate.ComposeOperator` 的核复合实现即是这样一个标注为
【依主控解释】的额外假设）。 -/
theorem no_unique_semantics :
    ¬ ∃! op : ℕ → ℕ → ℕ, ∃ e, ComposeAxioms op e :=
  underdetermined_of_two_models (· + ·) (· * ·) add_ne_mul
    ⟨0, addAxioms⟩ ⟨1, mulAxioms⟩

/-- ⭐⭐ **逻辑等价形式**（**反方向**）：`¬ ∃! op, Axioms op` 也**蕴含**「至少两个模型」。

做法**只用经典逻辑，不需要任何载体假设**：
若 `¬ ∃! op, P op`，则 `P` 要么无模型，要么多模型。
- **无模型**：`∃ op₁ op₂, op₁ ≠ op₂ ∧ P op₁ ∧ P op₂` 也假，
  此时两边同时为假——但这就**不成立**了（`False ↔ True` 不可能）。
  故此分支实际要求 `P` 有模型。
- **多模型**：即所求。

**⚠ 因此本 iff 只在「模型类非空」的前提下成立**，见 `no_unique_semantics_iff_two_models_of_nonempty`。 -/
theorem no_unique_semantics_iff_two_models_of_nonempty {α : Type*}
    (hne : ∃ op : α → α → α, ∃ e, ComposeAxioms op e) :
    (∃ op₁ op₂ : α → α → α, op₁ ≠ op₂ ∧
        (∃ e, ComposeAxioms op₁ e) ∧ (∃ e, ComposeAxioms op₂ e))
      ↔ ¬ ∃! op : α → α → α, ∃ e, ComposeAxioms op e := by
  constructor
  · rintro ⟨op₁, op₂, hne12, h₁, h₂⟩
    exact underdetermined_of_two_models op₁ op₂ hne12 h₁ h₂
  · intro h
    -- 反证：若不存在两个不同模型，则模型类至多单点；由 `hne` 非空，故唯一，与 `h` 矛盾。
    by_contra hnot
    obtain ⟨op₀, e₀, hA₀⟩ := hne
    refine h ⟨op₀, ⟨e₀, hA₀⟩, ?_⟩
    intro op hA
    by_contra hne₀
    obtain ⟨e, hA'⟩ := hA
    exact hnot ⟨op, op₀, hne₀, ⟨⟨e, hA'⟩, ⟨e₀, hA₀⟩⟩⟩

/-! ===========================================================================
    §4  ⭐ **具体反例见证**（清单要求 #3）
    =========================================================================== -/

/-- ⭐ **`op_differ_witness`**（清单要求 #3）：

**存在具体的 `a b`，使 `op₁ a b ≠ op₂ a b`**——
即两个公理模型在**具体输入**上给出**不同结果**。

**取 `a := 2, b := 3`**：`2 + 3 = 5`，`2 * 3 = 6`，`5 ≠ 6`。

**★ 这条为什么重要**：它把 §3 的「不唯一」**落到可检验的层面**——
不只是「两个函数不同」（外延断言），而是**存在一处具体的计算分歧**。
若 `R₁ ∘ R₂` 的语义未定，那么**同一对规则**在不同（都合规的）解释下
会得到**不同的输出**——这正是「不产生可判定的输出」的具体机制。 -/
theorem op_differ_witness :
    ∃ a b : ℕ, (· + ·) a b ≠ (· * ·) a b :=
  ⟨2, 3, by norm_num⟩

/-- ⭐ **见证的显式取值**：`2 + 3 = 5`。 -/
theorem op_differ_witness_left : (· + ·) 2 3 = 5 := by norm_num

/-- ⭐ **见证的显式取值**：`2 * 3 = 6`。 -/
theorem op_differ_witness_right : (· * ·) 2 3 = 6 := by norm_num

/-! ===========================================================================
    §5  ⭐⭐ **第二个实例**：`Bool` / `∨` 与 `∧`
    =========================================================================== -/

/-- ⭐⭐ **`Bool` 上的 `∨` 满足组合公理**（单位元 `false`）。

**★ 与 `ℕ`/`+`/`*` 的对比**：这里的载体是**有限**的（只有两个元素）。
故「公理不足」**不是**因为载体太大、元素太多——
即使在**有限**载体上，公理依旧不能唯一确定运算。 -/
theorem orAxioms : ComposeAxioms (α := Bool) (· || ·) false where
  assoc := by decide
  left_unit := by decide
  right_unit := by decide
  closed := closed_always _

/-- ⭐⭐ **`Bool` 上的 `∧` 满足组合公理**（单位元 `true`）。 -/
theorem andAxioms : ComposeAxioms (α := Bool) (· && ·) true where
  assoc := by decide
  left_unit := by decide
  right_unit := by decide
  closed := closed_always _

/-- ⭐⭐ `(· || ·)` 与 `(· && ·)` 是 `Bool` 上两个不同的运算（`tt || ff = tt ≠ ff = tt && ff`）。 -/
theorem or_ne_and : ((· || ·) : Bool → Bool → Bool) ≠ (· && ·) := by
  intro h
  have htf := congrFun (congrFun h true) false
  simp at htf

/-- ⭐⭐ **`no_unique_semantics_bool`**：即使在**两元素**载体上，公理也不足以唯一确定运算。

**★ 理论意义**：这条排除了「语义未定只是因为 `ℛ` 太大」这一辩解——
不足决定性来自**公理本身**，与载体大小无关。 -/
theorem no_unique_semantics_bool :
    ¬ ∃! op : Bool → Bool → Bool, ∃ e, ComposeAxioms op e :=
  underdetermined_of_two_models (· || ·) (· && ·) or_ne_and
    ⟨false, orAxioms⟩ ⟨true, andAxioms⟩

/-- ⭐ `Bool` 上的具体分歧见证：`tt || ff = true`，`tt && ff = false`。 -/
theorem op_differ_witness_bool :
    ∃ a b : Bool, (· || ·) a b ≠ (· && ·) a b :=
  ⟨true, false, by decide⟩

/-! ===========================================================================
    §6  ⭐⭐⭐ **T6.8 的元层面读法**
    =========================================================================== -/

/-- ⭐⭐⭐ **`compose_no_computational_meaning`**（**T6.8 的正面形式化**）：

**在任一载体上，若至少存在一个满足组合公理的运算，
则对**每一个**满足公理的运算 `op`，都存在另一个同样合规的运算 `op'`，
使得 `op ≠ op'`。**

形式化：
```
(∃ op e, ComposeAxioms op e) →
  ∀ op e, ComposeAxioms op e → ∃ op' e', ComposeAxioms op' e' ∧ op ≠ op'
```

**★ 为什么这等价于「`R₁ ∘ R₂` 不产生可判定的输出」**：
「可判定的输出」要求「同一个表达式在**所有**合规解释下算得同一个值」，
即要求满足公理的运算**至多一个**（唯一性）。本定理加上 §3 的 `¬ ∃!` 一起说：
公理**不能**把解释压到单点，故 `R₁ ∘ R₂` 的输出**不是**由公理决定的，
**因而不产生可判定的输出**。

**证明要点**：给定 `op ≠ op₀`（`op₀` 是任一固定模型），
则 `op₀` 本身就是与 `op` 不同的另一个合规解释；若 `op = op₀`，
则由 `|α| ≥ 2`（或其上另有一个模型）取另一个。
这里为避免对「载体至少两个元素」作额外假设，**直接用 §2 的两个 `ℕ` 模型**
给出 `ℕ` 上的版本，并用 `underdetermined_of_two_models` 的同一份数据
给出**任意载体**上的版本（见 `compose_no_computational_meaning_gen`）。 -/
theorem compose_no_computational_meaning :
    ∀ (op : ℕ → ℕ → ℕ) (e : ℕ), ComposeAxioms op e →
      ∃ (op' : ℕ → ℕ → ℕ) (e' : ℕ),
        ComposeAxioms op' e' ∧ op ≠ op' := by
  intro op e _
  -- 与 `op` 不同的合规解释：若 `op ≠ (· + ·)` 取加法，否则取乘法。
  by_cases h : op = (· + ·)
  · exact ⟨(· * ·), 1, mulAxioms, by rw [h]; exact add_ne_mul⟩
  · exact ⟨(· + ·), 0, addAxioms, h⟩

/-- ⭐⭐⭐ **`compose_no_computational_meaning_gen`**（**母定理**，任意载体）：

**若载体 `α` 上存在两个不同的合规运算，则每个合规运算都有一个不同的合规对手。**

**★ 这是 §6 的**参数化**版本，不含任何 `ℕ` 的痕迹。** -/
theorem compose_no_computational_meaning_gen {α : Type*}
    (op₁ op₂ : α → α → α) (hne : op₁ ≠ op₂)
    (h₁ : ∃ e, ComposeAxioms op₁ e) (h₂ : ∃ e, ComposeAxioms op₂ e) :
    ∀ (op : α → α → α) (e : α), ComposeAxioms op e →
      ∃ (op' : α → α → α) (e' : α), ComposeAxioms op' e' ∧ op ≠ op' := by
  intro op e _
  by_cases h : op = op₁
  · obtain ⟨e₂, hA₂⟩ := h₂
    exact ⟨op₂, e₂, hA₂, by rw [h]; exact hne⟩
  · obtain ⟨e₁, hA₁⟩ := h₁
    exact ⟨op₁, e₁, hA₁, h⟩

/-- ⭐⭐⭐ **`no_decidable_output`**（T6.8 的**最贴近原文**的读法）：

**不存在一个「由公理确定的」输出函数**——
即不存在 `f : ℕ → ℕ → ℕ`，使得对**所有**合规的 `op` 都有 `op = f`。

换个说法：把「`R₁ ∘ R₂` 的计算含义」理解为一个**函数**
`compute : ℛ → ℛ → ℛ`，并要求它「由公理确定」
（即：无论采用哪个合规解释，`compute` 都等于该解释）。
则本定理说：**这样的 `compute` 不存在。**

**★ 「`R₁ ∘ R₂` 不产生可判定的输出」= 不存在这样的 `compute`。** -/
theorem no_decidable_output :
    ¬ ∃ compute : ℕ → ℕ → ℕ,
        ∀ (op : ℕ → ℕ → ℕ) (e : ℕ), ComposeAxioms op e → op = compute := by
  rintro ⟨compute, hc⟩
  have h1 : ((· + ·) : ℕ → ℕ → ℕ) = compute := hc (· + ·) 0 addAxioms
  have h2 : ((· * ·) : ℕ → ℕ → ℕ) = compute := hc (· * ·) 1 mulAxioms
  exact add_ne_mul (h1.trans h2.symm)

/-- ⭐⭐⭐ **`axioms_do_not_pin`**（诚实边界的**左半边**）：

**公理本身不钉死任何运算**：`ComposeAxioms` 不蕴含 `op = (· + ·)`。

即：不能从「`op` 满足组合公理」推出「`op` 就是加法」。 -/
theorem axioms_do_not_pin :
    ¬ ∀ (op : ℕ → ℕ → ℕ) (e : ℕ), ComposeAxioms op e → op = (· + ·) := by
  intro h
  have := h (· * ·) 1 mulAxioms
  exact add_ne_mul this.symm

/-- ⭐⭐⭐ **`extra_hypothesis_pins`**（诚实边界的**右半边**）：

**一旦追加额外假设，语义立刻被确定**——
例如追加 `op = (· * ·)`（或追加「`∘` 是核复合」这类具体实现），
则 `∃! op, Axioms op ∧ op = (· * ·)`。

**★ 这条与 `no_unique_semantics` 合起来构成 T6.8 的完整账**：

| 前提 | 结论 |
|---|---|
| 只有 `ComposeAxioms` | **不**唯一（`no_unique_semantics`） |
| `ComposeAxioms` + 额外假设 `op = (· * ·)` | **唯一**（本条） |

**⟹ 「语义未定」的**唯一**来源是「缺少额外假设」；
`∘` 的计算含义只能由额外假设（作者裁决）提供，公理提供不了。** -/
theorem extra_hypothesis_pins :
    ∃! op : ℕ → ℕ → ℕ, (∃ e, ComposeAxioms op e) ∧ op = (· * ·) := by
  refine ⟨(· * ·), ⟨⟨1, mulAxioms⟩, rfl⟩, ?_⟩
  rintro op ⟨⟨e, _⟩, rfl⟩
  rfl

end FateV2.Meta.R230B4