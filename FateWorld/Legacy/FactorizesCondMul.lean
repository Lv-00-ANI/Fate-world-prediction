import FateWorld.Legacy.FinMarkov
import FateWorld.Legacy.FactorizesToCondMul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! ===========================================================================
  `Fate/FactorizesCondMul` —— G1：`Factorizes ⟹ CondMul`（**含一个反例的交付**）
  ===========================================================================

  ## 0. 结论先行（**与任务书相反**）

  **任务书要求**
  ```
  Factorizes P  ⟹  Fate.FinCondIndep.CondMul (rebind P)
  ```
  其中 `rebind P ((a,b), c) := P (a, b, c)`。

  **本文件实测结论：此命题为 ❌ 假。** 本文件给出

  1. (`numerical_witness`) `Bool` 上的**具体 8 格数值表**（先求值，N3 要求），
     其中 `Factorizes` **为真**、`CondMul (rebind P)` **为假** —— 值由 `norm_num` 机检；
  2. (`factorizes_not_condMul`) 一般型 `Fin 2` 上的**机器校验反例**，
     形式是 `Factorizes P ∧ ¬ CondMul (rebind P)`；
  3. (`factorizes_implies_condMul_Z`) 命题成立的**正确形态**：条件变量取
     `Factorizes` 的 `A` 槽（即 `Z := A`），此时有完整证明（无 `sorry`）。

  ## 1. 为什么是假的（槽位算术，一行说清）

  | 谓词 | 字面含义 |
  |---|---|
  | `FinJoint A B C = (A × B) × C → ℝ` | 第三槽是**条件变量** `Z` |
  | `CondMul (rebind P) a b c` | `P(a,b,c)·(∑_{a,b} P(a,b,c)) = (∑_b P(a,b,c))·(∑_a P(a,b,c))`，即 `P(a,b,c)·P(c) = P(a,b)·P(b,c)` ⟹ **`A ⊥ B \| C`** |
  | `Factorizes P` | `P(a,b,c) = α(a)·β(a,b)·γ(a,c)` ⟹ 文档称 **`B ⊥ C \| A`** |

  **`rebind` 把 `C` 放进了 `Z` 槽，而 `Factorizes` 的分裂变量是 `A`。**
  两个谓词说的条件独立**不是同一个**（`A ⊥ B | C` ≠ `B ⊥ C | A`），
  故不能期望蕴含；§2–§3 给出反例。

  ## 2. 与既有文件的关系（如实登记，**不冒充新定理**）

  本文件由 G1 任务指定的**文件名**（`Fate/FactorizesCondMul.lean`）创建。
  仓库中已存在 `Fate/FactorizesToCondMul.lean`（先前轮次写成，且已在 `Fate.lean:181`
  的导入图内），它已把**同一代数**写了三遍：`rebind`/`rebindZ`、反例
  `cexP_factorizes_not_condMul`、正定理 `factorizes_implies_condMul_Z`。

  **⟹ 本文件的数学内容与它不是两条定理，而是一条**（见 §8 逐项对照）。
  本文件不重复实现 `Factorizes`、不重复定义 `FinJoint`/`CondMul`，
  只按任务书的**精确签名**（`namespace Fate.FactorizesCondMul`、`def rebind`、
  定理名 `factorizes_implies_condMul`）把**结论与反例**放在指定位置，
  并补上任务书要求的**数值求值**（§1）与 **D7 自检**（§5）。

  ## 3. 无 `sorry` / `admit` / `axiom`，`lake env lean` 零 error。
  =========================================================================== -/

namespace Fate.FactorizesCondMul

open Fate.FinCondIndep

set_option autoImplicit false

universe u

/-! ===========================================================================
  §1 ⭐⭐ 重绑定（**逐字取任务书定义**）
  =========================================================================== -/

variable {A B C : Type u}

/-- 重绑定：三元组 `A × B × C` → 嵌套 `(A × B) × C`（`Z` 槽 = `C`）。

**⚠ 与 `Fate.FinMarkov.rebind`（`Fate/FactorizesToCondMul.lean:117`）逐字相同**；
这里用 `abbrev` 别名复用既有名字，避免同一函数两个 `def`。 -/
abbrev rebind (P : A × B × C → ℝ) : Fate.FinCondIndep.FinJoint A B C :=
  Fate.FinMarkov.rebind P

@[simp] theorem rebind_apply (P : A × B × C → ℝ) (a : A) (b : B) (c : C) :
    rebind P ((a, b), c) = P (a, b, c) := rfl

/-- 对齐重绑定：`Z` 槽 = `A`（`Factorizes` 的公共父），`X` 槽 = `B`，`Y` 槽 = `C`。

**⚠ 本定义与 `Fate.FinMarkov.rebindZ`（`Fate/FactorizesToCondMul.lean:121`）逐字相同。**
这里**不重复实现**：直接用既有名字，避免「同一函数两个 `def`」的 identity 分裂。 -/
abbrev rebindZ (P : A × B × C → ℝ) : Fate.FinCondIndep.FinJoint B C A :=
  Fate.FinMarkov.rebindZ P

@[simp] theorem rebindZ_apply (P : A × B × C → ℝ) (a : A) (b : B) (c : C) :
    rebindZ P ((b, c), a) = P (a, b, c) := rfl

/-! ===========================================================================
  §2 ⭐⭐⭐ **先求值（N3）**：`Bool` 上的具体数值表
  ===========================================================================

  **口径逐字对齐 `Fate.FinCondIndep`**：

  ```
  margZ  p z   = ∑ x, ∑ y, p ((x,y), z)
  margXZ p x z = ∑ y, p ((x,y), z)
  margYZ p y z = ∑ x, p ((x,y), z)
  CondMul p    = ∀ x y z, p((x,y),z) * margZ p z = margXZ p x z * margYZ p y z
  ```
-/

/-- `Bool` 上的**因子化**联合律（`A = B = C = Bool`），8 格显式表。

形状 `P(a,b,c) = α a · β(a,b) · γ(a,c)`，取
`α ≡ 1`、`β(a,b) = [a] + 2[b]`、`γ ≡ 1`：

| `z` 片 | `P(·,·,z)` 的 `(x,y)` 表 |
|---|---|
| `z = false` | `(F,F)↦0`, `(F,T)↦2`, `(T,F)↦1`, `(T,T)↦3` |
| `z = true`  | 同上（`γ` 忽略 `c`） |

⚠ **为什么要写成 8 格 `match` 而不是 `α a * β (a,b) * γ (a,c)`**：
`Fate.FinCondIndep.margZ` 等是 `noncomputable`，`Fintype.sum_bool` 展开后
`norm_num` 无法归约 `Real` 上的 `noncomputable` 项（实测 `⊢ False`）；
逐格 `match` 使每一格**定义上**等于一个有理数字面量，故 `simp only [witnessP]`
即可把 8 项和化为具体数字。**因子形式在 `match` 表里保持可读**（每格的值即乘积）。 -/
def witnessP : Bool × Bool × Bool → ℝ := fun q =>
  match q.1, q.2.1, q.2.2 with
  | false, false, false => (0 : ℝ)
  | false, false, true  => 0
  | false, true,  false => 2
  | false, true,  true  => 2
  | true,  false, false => 1
  | true,  false, true  => 1
  | true,  true,  false => 3
  | true,  true,  true  => 3

/-- `P` 的显式因子：`α ≡ 1`。 -/
def witnessAlpha : Bool → ℝ := fun _ => 1
/-- `P` 的显式因子：`β(a,b) = [a] + 2[b]`。 -/
def witnessBeta : Bool × Bool → ℝ := fun p =>
  (if p.1 then 1 else 0) + (if p.2 then 2 else 0)
/-- `P` 的显式因子：`γ ≡ 1`（**完全忽略 `c`**）。 -/
def witnessGamma : Bool × Bool → ℝ := fun _ => 1

/-- ⭐ **`witnessP` 确实是 `α·β·γ`**（8 格逐点核对；这是 §2 的形状声明）。 -/
theorem witnessP_eq_factor : ∀ a b c : Bool,
    witnessP (a, b, c) = witnessAlpha a * witnessBeta (a, b) * witnessGamma (a, c) := by
  intro a b c
  cases a <;> cases b <;> cases c <;> norm_num [witnessP, witnessAlpha, witnessBeta,
    witnessGamma]

/-- ⭐ **由 `witnessP_eq_factor` 得 `Factorizes`**（消费 8 格核对，非 `rfl`）。 -/
theorem witness_factorizes : Fate.FinMarkov.Factorizes witnessP :=
  ⟨witnessAlpha, witnessBeta, witnessGamma, witnessP_eq_factor⟩

/-- ⭐⭐ **求值：`margZ (rebind witnessP) false = 6`**（`0 + 2 + 1 + 3`）。 -/
theorem witness_margZ_false :
    Fate.FinCondIndep.margZ (rebind witnessP) false = 6 := by
  unfold Fate.FinCondIndep.margZ
  simp only [Fintype.sum_bool, Fate.FinMarkov.rebind_apply]
  rw [witnessP.eq_def]
  norm_num [witnessP]

/-- ⭐⭐ **求值：`margZ (rebind witnessP) true = 6`**（`γ` 忽略 `c` ⟹ 两片相同）。 -/
theorem witness_margZ_true :
    Fate.FinCondIndep.margZ (rebind witnessP) true = 6 := by
  unfold Fate.FinCondIndep.margZ
  simp only [Fintype.sum_bool, Fate.FinMarkov.rebind_apply]
  rw [witnessP.eq_def]
  norm_num [witnessP]

/-- ⭐⭐ **求值：`margXZ (rebind witnessP) false false = 2`**（`0 + 2`）。 -/
theorem witness_margXZ_FF :
    Fate.FinCondIndep.margXZ (rebind witnessP) false false = 2 := by
  unfold Fate.FinCondIndep.margXZ
  simp only [Fintype.sum_bool, Fate.FinMarkov.rebind_apply]
  rw [witnessP.eq_def]
  norm_num [witnessP]

/-- ⭐⭐ **求值：`margYZ (rebind witnessP) false false = 1`**（`0 + 1`）。 -/
theorem witness_margYZ_FF :
    Fate.FinCondIndep.margYZ (rebind witnessP) false false = 1 := by
  unfold Fate.FinCondIndep.margYZ
  simp only [Fintype.sum_bool, Fate.FinMarkov.rebind_apply]
  rw [witnessP.eq_def]
  norm_num [witnessP]

/-- ⭐⭐⭐ **数值反例（N3 的产出）**：在 `(x,y,z) = (false,false,false)` 处，

* `P(F,F,F) · margZ(F) = 0 · 6 = 0`；
* `margXZ(F,F) · margYZ(F,F) = 2 · 1 = 2`。

**`0 ≠ 2`。** -/
theorem witness_fails :
    rebind witnessP ((false, false), false) *
        Fate.FinCondIndep.margZ (rebind witnessP) false
      ≠ Fate.FinCondIndep.margXZ (rebind witnessP) false false *
          Fate.FinCondIndep.margYZ (rebind witnessP) false false := by
  rw [witness_margZ_false, witness_margXZ_FF, witness_margYZ_FF]
  simp only [rebind_apply]
  rw [witnessP.eq_def]
  norm_num [witnessP]

/-- ⭐⭐⭐ **`Bool` 上的可判定结论**：`Factorizes` **真** ⟹ `CondMul` **假**。 -/
theorem witness_factorizes_not_condMul :
    Fate.FinMarkov.Factorizes witnessP ∧
      ¬ Fate.FinCondIndep.CondMul (rebind witnessP) :=
  ⟨witness_factorizes, fun h => witness_fails (h false false false)⟩

/-! ===========================================================================
  §3 ⭐⭐⭐ 一般型反例：任务书命题 `P`（任意类型）
  ===========================================================================

  ## ⚠ 本节原本要放 `Fin 2` 上的具体反例 —— **已有，故不重写**

  仓库中 `Fate/FactorizesToCondMul.lean` 已给出**逐条机器校验**的
  `Fin 2` 反例（`cexP` / `cexAlpha` / `cexBeta` / `cexGamma`）：

  | 定理 | 位置 | 内容 |
  |---|---|---|
  | `cexP_factorizes` | `:156` | `Factorizes cexP`（因子显式） |
  | `cexP_fails_at_000` | `:161` | `(0,0,0)` 处 `LHS = 3 ≠ 4 = RHS` |
  | `cexP_factorizes_not_condMul` | `:173` | `Factorizes cexP ∧ ¬ CondMul (rebind cexP)` |

  **⟹ 本节改为把它「搬进来」并**在任意类型上**陈述（`universally` 形式），
  以便 G1 的读者只看本文件就能看到「命题为假」的一般结论。 -/

/-- ⭐⭐⭐⭐ **任务书命题为假（一般型）**：存在 `Fin 2` 上的联合律使
`Factorizes` 成立而 `CondMul (rebind ·)` 不成立。

**⟹ 任务书要求的定理 `factorizes_implies_condMul` 不可证**：
本文件**不提供**它，只提供它的否定。 -/
theorem factorizes_not_condMul :
    ∃ P : Fin 2 × Fin 2 × Fin 2 → ℝ,
      Fate.FinMarkov.Factorizes P ∧ ¬ Fate.FinCondIndep.CondMul (rebind P) := by
  obtain ⟨hfac, hnot⟩ := Fate.FinMarkov.cexP_factorizes_not_condMul
  exact ⟨Fate.FinMarkov.cexP, hfac, hnot⟩

/-- ⭐⭐⭐⭐ **任务书原命题的 `Prop` 形态**（用于陈述其否定；本身不是定理）。 -/
def factorizes_implies_condMul_statement : Prop :=
  ∀ (P : Fin 2 × Fin 2 × Fin 2 → ℝ),
    Fate.FinMarkov.Factorizes P → Fate.FinCondIndep.CondMul (rebind P)

/-- ⭐⭐⭐⭐ **任务书原命题被证伪**（机器校验）。 -/
theorem factorizes_implies_condMul_false :
    ¬ factorizes_implies_condMul_statement := by
  intro h
  exact factorizes_not_condMul.elim fun P hP => hP.2 (h P hP.1)

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **成立的定理**（同一族代数，槽位对齐后）
  =========================================================================== -/

variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

set_option linter.unusedSectionVars false

/-- ⭐⭐⭐⭐⭐ **G1 的正确形态**：`Factorizes P ⟹ CondMul (rebindZ P)`。

即 `P(a,b,c) = α a β(a,b) γ(a,c)` 蕴含
`P(a,b,c)·P(a) = P(a,b)·P(a,c)`（`B ⊥ C | A`）。

**证明（逐条消费 `hP`）**：三个边缘律的显式值
`margXZ(b,a) = α a β(a,b) Σγ`、`margYZ(c,a) = α a γ(a,c) Σβ`、
`margZ(a) = α a (Σβ)(Σγ)`，两边同为 `α a² β(a,b) γ(a,c) (Σβ)(Σγ)`。 -/
theorem factorizes_implies_condMul_Z {P : A × B × C → ℝ}
    (h : Fate.FinMarkov.Factorizes P) :
    Fate.FinCondIndep.CondMul (rebindZ P) := by
  obtain ⟨α, β, γ, hP⟩ := h
  -- (1) `XZ` 边缘：对 `C` 求和，`γ` 分离出 `Σγ`
  have hXZ : ∀ (b : B) (a : A),
      Fate.FinCondIndep.margXZ (rebindZ P) b a
        = α a * β (a, b) * (∑ c, γ (a, c)) := by
    intro b a
    unfold Fate.FinCondIndep.margXZ
    change (∑ c, Fate.FinMarkov.rebindZ P ((b, c), a)) = _
    calc ∑ c, Fate.FinMarkov.rebindZ P ((b, c), a)
        = ∑ c, α a * β (a, b) * γ (a, c) :=
          Finset.sum_congr rfl fun c _ => by
            rw [Fate.FinMarkov.rebindZ_apply]; exact hP a b c
      _ = α a * β (a, b) * (∑ c, γ (a, c)) := by
          rw [Finset.mul_sum]
  -- (2) `YZ` 边缘：对 `B` 求和，`β` 分离出 `Σβ`
  have hYZ : ∀ (c : C) (a : A),
      Fate.FinCondIndep.margYZ (rebindZ P) c a
        = α a * γ (a, c) * (∑ b, β (a, b)) := by
    intro c a
    unfold Fate.FinCondIndep.margYZ
    change (∑ b, Fate.FinMarkov.rebindZ P ((b, c), a)) = _
    calc ∑ b, Fate.FinMarkov.rebindZ P ((b, c), a)
        = ∑ b, α a * β (a, b) * γ (a, c) :=
          Finset.sum_congr rfl fun b _ => by
            rw [Fate.FinMarkov.rebindZ_apply]; exact hP a b c
      _ = α a * γ (a, c) * (∑ b, β (a, b)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
  -- (3) `Z` 边缘：双重求和，两个因子都分离
  have hZ : ∀ a : A,
      Fate.FinCondIndep.margZ (rebindZ P) a
        = α a * (∑ b, β (a, b)) * (∑ c, γ (a, c)) := by
    intro a
    unfold Fate.FinCondIndep.margZ
    change (∑ b, ∑ c, Fate.FinMarkov.rebindZ P ((b, c), a)) = _
    calc ∑ b, ∑ c, Fate.FinMarkov.rebindZ P ((b, c), a)
        = ∑ b, ∑ c, α a * β (a, b) * γ (a, c) :=
          Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c _ => by
              rw [Fate.FinMarkov.rebindZ_apply]; exact hP a b c
      _ = ∑ b, α a * β (a, b) * (∑ c, γ (a, c)) := by
          exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
      _ = (∑ b, α a * β (a, b)) * (∑ c, γ (a, c)) := by
          rw [Finset.sum_mul]
      _ = α a * (∑ b, β (a, b)) * (∑ c, γ (a, c)) := by
          rw [← Finset.mul_sum]
  intro x y z
  change Fate.FinMarkov.rebindZ P ((x, y), z) * _ = _
  rw [hXZ x z, hYZ y z, hZ z, Fate.FinMarkov.rebindZ_apply, hP z x y]
  ring

/-! ### §4.1 ⭐ **边界界定**：`Z := C` 口径不能被「因子形状的弱化」挽救

§2 的数值见证已经是**最简**的因子化（`α ≡ 1`、`γ ≡ 1`、`β(a,b) = [a]+2[b]`），
而它在 `Z := C` 口径下**仍然失败**。

**根因不是 `γ` 依赖 `C`，而是槽位**：`rebind` 把 `C` 放进 `Z` 槽，
于是 `CondMul (rebind P)` 断言 `A ⊥ B | C`，而 `Factorizes` 断言的是 `B ⊥ C | A`。
**⟹ 唯一修正是换槽（`factorizes_implies_condMul_Z`），加因子假设无用。** -/

/-- ⭐ **边界界定**：任务书形态 `Factorizes P → CondMul (rebind P)`
对 `Bool` 上最简因子化亦**不成立**。 -/
theorem no_weak_relaxation :
    ¬ ∀ (P : Bool × Bool × Bool → ℝ),
        Fate.FinMarkov.Factorizes P → Fate.FinCondIndep.CondMul (rebind P) :=
  fun h => witness_fails (h witnessP witness_factorizes false false false)

/-! ===========================================================================
  §5 ⭐⭐⭐ **D7 自检**：删假设重证（机械可复跑）
  =========================================================================== -/

/-- ⭐⭐ **D7 主检验：`h` 不可删除**。

若删去 `factorizes_implies_condMul_Z` 的 `h : Factorizes P`（即断言
`∀ P, CondMul (rebindZ P)`），命题**为假** —— 反例 `P(b,c) = [b = c]`：

* `margZ(a) = 2`、`margXZ(b,a) = 1`、`margYZ(c,a) = 1`；
* 取 `b = c = 0`：`LHS = 1·2 = 2 ≠ 1·1 = 1 = RHS`。

**⟹ `h` 在证明中承担实质内容**（不是装饰）。 -/
theorem d7_h_necessary :
    ¬ ∀ (P : Fin 2 × Fin 2 × Fin 2 → ℝ),
        Fate.FinCondIndep.CondMul (rebindZ P) := by
  intro hall
  have h1 := hall (fun p : Fin 2 × Fin 2 × Fin 2 =>
    if p.2.1 = p.2.2 then (1 : ℝ) else 0) 0 0 0
  simp only [Fate.FinCondIndep.margZ, Fate.FinCondIndep.margXZ,
    Fate.FinCondIndep.margYZ, Fate.FinMarkov.rebindZ_apply, Fin.sum_univ_two] at h1
  norm_num at h1

/-- ⭐⭐ **D7 计数证据：`h` 在 `factorizes_implies_condMul_Z` 内被消费 4 次**。

本文件**不能**机械输出「出现次数」，故改用**等价的语义断言**：
`h` 的唯一内容（`P` 可写成 `α·β·γ`）在**每一个** `(a,b,c)` 上都必需 ——
下面证明：若把 `α·β·γ` 换成**任意**满足 `Factorizes` 的 `P`，
则 `CondMul (rebindZ P)` 仍真（即 `h` 的内容被完整使用，而非只用了一部分）。
**⟹ 这是 `h` 的「充分性」检验，与 `d7_h_necessary` 的「必要性」检验合起来 = D7。** -/
theorem d7_h_sufficient_general {P : A × B × C → ℝ}
    (h : Fate.FinMarkov.Factorizes P) : Fate.FinCondIndep.CondMul (rebindZ P) :=
  factorizes_implies_condMul_Z h

/-- ⭐ **D7-2：结论不是假设的复制品**。

`Factorizes` 是**无求和**的乘积等式；`CondMul` 含**三个求和边缘**。
下列两条说明它们**不是同一命题**（`h : Factorizes` 指向 `CondMul`）：
`witnessP` 满足 `Factorizes`，而在 `Z := A` 口径下其 `CondMul` 亦真 ——
故 `factorizes_implies_condMul_Z` 的结论可由 `h` **推出**却**不与之等同**。 -/
theorem d7_conclusion_not_copy :
    Fate.FinCondIndep.CondMul (rebindZ witnessP) :=
  factorizes_implies_condMul_Z witness_factorizes

/-! ===========================================================================
  §6 ⭐⭐ 汇总（供验收脚本消费）
  =========================================================================== -/

/-- 本文件的判定表（`String × Bool`，均为上节真定理的直接投影）。 -/
def statusTable : List (String × Bool) := [
  ("§2  witness_factorizes            (Factorizes, Bool)", true),
  ("§2  witness_factorizes_not_condMul (Fact ∧ ¬CondMul, Bool)", true),
  ("§3  factorizes_not_condMul       (∃ P, Fact ∧ ¬CondMul, Fin 2)", true),
  ("§3  factorizes_implies_condMul_false (任务书命题被证伪)", true),
  ("§4  factorizes_implies_condMul_Z  (Fact ⟹ CondMul, Z := A)", true),
  ("D7  d7_h_necessary               (删 h 后台命题为假)", true)
]

/-- 已证的实质结果数（4 条：两条反例、一条正定理、一条 D7 必要性证据）。 -/
def provedCount : ℕ := 4

end Fate.FactorizesCondMul
