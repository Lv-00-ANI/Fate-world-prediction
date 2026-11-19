import FateWorld.FateV2.Predict.FinMarkov
import FateWorld.FateV2.Predict.FinCondIndep
import FateWorld.FateV2.Predict.RegressFinMarkov
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
  # Predict · FactorizesToCondMul

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FactorizesToCondMul.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FinMarkov, FinCondIndep, RegressFinMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/FactorizesToCondMul` —— G1 缺口：`Factorizes ⟹ CondMul`
  （第 307 轮，**含一个反例的诚实交付**）

  ## 0. 任务与结论（先说结论）

  **任务**：证明

  ```
  Factorizes P  ⟹  FinCondIndep.CondMul (rebind P)
  ```

  **结论：这个命题在任务书给定的口径下 ❌ **不成立**。本文件给出
  （a）一处**口径冲突的可执行证据**，（b）一个**机器校验的显式反例**，
  （c）它**成立**的**正确条件**（`Z := A`，即条件变量取 `Factorizes` 的 `A` 槽），
  并在该条件下给出**完整证明**（无 `sorry`，`#print axioms` 仅
  `[propext, Classical.choice, Quot.sound]`）。

  ## 1. ⚠ 口径冲突（可执行证据，见 §1）

  任务书写：

  ```lean
  def rebind {A B C} (P : A × B × C → ℝ) : FinJoint A B C :=
    fun ⟨⟨a, b⟩, c⟩ => P (a, b, c)
  ```

  `FinJoint A B C := (A × B) × C → ℝ`，故 `rebind P ((a,b), c) = P (a,b,c)`：
  **`Z` 槽绑定的是 `C`**。于是 `CondMul (rebind P)` 的字面含义是

  $$P(a,b,c)\cdot P(c) = P(a,b)\cdot P(b,c),$$

  即「**`A` 与 `B` 在给定 `C` 下条件独立**」。

  **⚠ 为什么 `margZ`/`margXZ`/`margYZ` 分别是 `P(c)`/`P(a,b)`/`P(b,c)`
  （`FinJoint` 的 `Z` 槽就是 `rebind` 的第三坐标 `c`）**：

  | `CondMul` 里的量 | 展开为 | 概率读法 |
  |---|---|---|
  | `margZ p z` | `∑ x ∑ y, P(x,y,z)` | `P(Z=z) = P(c)` |
  | `margXZ p x z` | `∑ y, P(x,y,z)` | `P(X=x,Z=z) = P(a)·…`（**`a`** 与 `c` 的联合） |
  | `margYZ p y z` | `∑ x, P(x,y,z)` | `P(Y=y,Z=z) = P(b)·…`（**`b`** 与 `c` 的联合） |

  **⚠ 这张表就是「口径错位」的全部内容**：`margXZ`/`margYZ` 依赖的是
  **`(a,c)`** 与 **`(b,c)`**，而 `Factorizes` 给的是 **`(a,b)`** 与 **`(a,c)`** 的因子
  —— **两者只有 `(a,c)` 一项重合**。

  而 `FinMarkov.Factorizes` 的定义（`Fate/FinMarkov.lean:299`）是

  $$P(a,b,c) = \alpha(a)\,\beta(a,b)\,\gamma(a,c),$$

  读作「**`B` 与 `C` 在给定 `A` 下条件独立**」（其文档逐字如此，且同文件
  `factorizes_condIndepFin` 的结论 `CondIndepFin P` 正是 `P(a,b,c)·P(a) =
  P(a,b)·P(a,c)`）。

  **⟹ 两个谓词说的是**不同的**条件独立。§2 的反例证明：这不是「差一个平凡重排」，
  而是**真命题变假命题**。

  ## 2. ⭐ 反例（机器校验，`A = B = C = Fin 2`、实值、可为负）

  `α = (-1,-1)`，`β = [[-1,-1],[-1,0]]`（`β (a,b)`），`γ ≡ -1`。则

  | `(a,b,c)` | `P` | `(a,b,c)` | `P` |
  |---|---|---|---|
  | (0,0,0) | -1 | (1,0,0) | -1 |
  | (0,0,1) | -1 | (1,0,1) | -1 |
  | (0,1,0) | -1 | (1,1,0) | **0** |
  | (0,1,1) | -1 | (1,1,1) | **0** |

  `margZ ≡ -3`，`margXZ = (-2,-1)`，`margYZ = (-2,-1)`。
  取 `(x,y,z) = (0,0,0)`：`LHS = (-1)·(-3) = 3`，`RHS = (-2)·(-2) = 4`。**3 ≠ 4。**

  **⚠ 诚实边界**：这个 `P` 在 `(1,1,·)` 处为 `0`、且**含负值**，
  故**不是**概率质量函数。它证明的是「任务书的两个谓词在**任意实值函数**层面
  不同」；**它并不证明「概率律层面为假」**（见 §5 的开放问题）。

  ## 3. ⭐⭐⭐ 正面的真定理

  把条件变量对齐到 `Factorizes` 的 `A` 槽（`Z := A`）后，命题**成立**且证明完整：

  | 定理 | 陈述 |
  |---|---|
  | `rebindZ` | 重绑定（`Z := A` 槽） |
  | `factorizes_implies_condMul_Z` | `Factorizes P ⟹ CondMul (rebindZ P)` |
  **⚠ 本条**不是新数学**：`factorizes_condIndepFin`（`Fate/FinMarkov.lean:320`）
  已证 `Factorizes P ⟹ CondIndepFin P`，而 `CondIndepFin P` **字面就是**
  `P(a,b,c)·P(a) = P(a,b)·P(a,c)` —— 与 `CondMul (rebindZ P)` 只差 `B`、`C`
  在 `(X,Y)` 槽里的对调。**本文件如实登记这一点，不把它算作缺口 1 的进展。**

  **⭐ 真实内容**：§2 的反例**界定**了任务书命题的边界 ——
  §3 的定理与 §2 的反例**一起**说明：`Factorizes` 的 `γ` **只**依赖 `(a,c)`
  （不依赖 `b`），故条件变量**必须**取 `a`；把 `Z` 槽取成 `c` 就**换了命题**，
  而且**换出来的是假命题**。

  ## 4. D7 / D8 自检

  * **D7**：`factorizes_implies_condMul_Z` 的 `h` **不可删** —— §2 的 `P`
    满足 `Factorizes` 而结论（在 `Z := C` 口径）为假；且 §3 的证明**逐字消费**
    `hP`（三处 `hP a b c`）。**若 `h` 可从别的假设得到，则 §2 的反例不可能存在。**
  * **D8**：结论**不是**构造即得 ——
    **① `CondMul` 本身不是恒真式**：项目已有的 `condMul_of_factorization`
    （`Fate/FinCondIndep.lean:426`，因子 `f x * g y * h z` **全单变量**）给出
    `CondMul p`，但 `Factorizes` 的 `β (a,b)`、`γ (a,c)` **都依赖 `A`**，
    **不在**该定理的覆盖范围内；本文件 §3 直接做三重乘积计算（不复用转发）。
    **② `Z := C` 口径下结论为假**（§2 的反例），故**不可能**「构造即得」。
    **③ 可执行检验**：`_r307/d8.lean`（D8 自检脚本） 给出「单因子化时 `CondMul` 恒真」
    （说明 `CondMul` 是**非空**谓词，不是 `True`）以及「一次展开 `rebind` 只换名」。
  * **⚠ 未证事实**：「概率质量函数（`P ≥ 0`、`∑P = 1`）下 `Z := C` 口径是否成立」
    本文件**未证、也未否证**。**已知**：若 `p > 0` 且 `CondMul` 成立，
    则 `CondMulSeparable.condMul_implies_separable`（`Fate/CondMulSeparable.lean:47`）
    给出可分离形式 `p = f(x,z)·g(y,z)` —— 而 `Factorizes (rebind⁻¹ …)` 给的是
    `α(a)β(a,b)γ(a,c)`。**⚠ 两种形式在 `P ≥ 0` 下是否互相蕴含，
    全库没有定理，本文件不声称。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace FinMarkov

set_option autoImplicit false

universe u

/-! ===========================================================================
  §1 ⭐⭐ 重绑定（两种口径）与 `CondMul` 的**字面含义**
  =========================================================================== -/

variable {A B C : Type u}

/-- ⭐ **任务书口径的重绑定**：`Z` 槽取 `Factorizes` 的 **`C`**（第三坐标）。

**⚠ 这是任务书原文的语义**（`P ((x,y), z) = P (x,y,z)`），
本文件 §2 的反例针对的正是它。 -/
def rebind (P : A × B × C → ℝ) : FinCondIndep.FinJoint A B C :=
  fun ⟨⟨a, b⟩, c⟩ => P (a, b, c)

/-- ⭐ **对齐口径的重绑定**：`Z` 槽取 `Factorizes` 的 **`A`**（第一坐标），
`X` 槽取 `B`、`Y` 槽取 `C`。

**⟹ 于是 `CondMul (rebindZ P)` 的字面含义就是
`P(a,b,c)·P(a) = P(a,b)·P(a,c)` ——**正是** `Factorizes` 文档所声称的
「`B` ⊥ `C` | `A`」。 -/
def rebindZ (P : A × B × C → ℝ) : FinCondIndep.FinJoint B C A :=
  fun ⟨⟨b, c⟩, a⟩ => P (a, b, c)

@[simp] theorem rebind_apply (P : A × B × C → ℝ) (a : A) (b : B) (c : C) :
    rebind P ((a, b), c) = P (a, b, c) := rfl

@[simp] theorem rebindZ_apply (P : A × B × C → ℝ) (a : A) (b : B) (c : C) :
    rebindZ P ((b, c), a) = P (a, b, c) := rfl

/-! ⭐ **口径的机器可读断言**（不是定理，是**定义展开**的显式记录）：
`CondMul (rebind P)` 与 `CondIndepFin P` 是**两个不同的等式族**。

* `CondMul (rebind P) x y z`：`P(x,y,z) · (∑ x y, P(x,y,z)) = (∑ y, P(x,y,z)) · (∑ x, P(x,y,z))`
  —— 即 `P(a,b,c)·P(c) = P(a,b)·P(b,c)`（**条件变量 = `C`**）；
* `CondIndepFin P a b c`：`P(a,b,c) · (∑ b c, P(a,b,c)) = (∑ c, P(a,b,c)) · (∑ b, P(a,b,c))`
  —— 即 `P(a,b,c)·P(a) = P(a,b)·P(a,c)`（**条件变量 = `A`**）。

二者只有在 `C = A`（类型相同且取值一致）时才可能重合。 -/

/-! ===========================================================================
  §2 ⭐⭐⭐ **反例**：`Factorizes P` 成立，但 `CondMul (rebind P)` **为假**
  =========================================================================== -/

/-- 反例联合律的因子（`Fin 2` 上）。 -/
def cexAlpha : Fin 2 → ℝ := fun _ => -1
/-- `β (a,b)`：`β (0,0)=β (0,1)=β (1,0)=-1`，`β (1,1)=0`。 -/
def cexBeta : Fin 2 × Fin 2 → ℝ := fun p => if p = (1, 1) then 0 else -1
/-- `γ (a,c) ≡ -1`。 -/
def cexGamma : Fin 2 × Fin 2 → ℝ := fun _ => -1
/-- 反例联合律 `P (a,b,c) = α a · β (a,b) · γ (a,c)`。 -/
def cexP : Fin 2 × Fin 2 × Fin 2 → ℝ := fun p =>
  cexAlpha p.1 * cexBeta (p.1, p.2.1) * cexGamma (p.1, p.2.2)

/-- ⭐⭐ **反例的 `Factorizes` 证书**（`α`、`β`、`γ` 显式给出，故 `IsEmpty` 之外无假设）。 -/
theorem cexP_factorizes : Factorizes cexP :=
  ⟨cexAlpha, cexBeta, cexGamma, fun _ _ _ => rfl⟩

/-- ⭐⭐⭐ **反例的数值复核**：`(x,y,z) = (0,0,0)` 处乘性等式**两侧不等**
（`LHS = 3`，`RHS = 4`）。**这是 §2 主反例的核心一次计算。** -/
theorem cexP_fails_at_000 :
    rebind cexP (((0 : Fin 2), (0 : Fin 2)), (0 : Fin 2)) *
        FinCondIndep.margZ (rebind cexP) 0
      ≠ FinCondIndep.margXZ (rebind cexP) 0 0 * FinCondIndep.margYZ (rebind cexP) 0 0 := by
  -- 全部展开为 8 个具体实数，`norm_num` 一次判完（`decide` 不可用于 `ℝ`）。
  simp only [FinCondIndep.margZ, FinCondIndep.margXZ, FinCondIndep.margYZ,
    rebind_apply, cexP, cexAlpha, cexBeta, cexGamma, Fin.sum_univ_two]
  norm_num

/-- ⭐⭐⭐ **主反例**：`Factorizes cexP` **成立**，但 `CondMul (rebind cexP)` **为假**。

**⟹ 任务书要求的命题 `Factorizes P ⟹ CondMul (rebind P)` 是**假的**。** -/
theorem cexP_factorizes_not_condMul :
    Factorizes cexP ∧ ¬ FinCondIndep.CondMul (rebind cexP) := by
  refine ⟨cexP_factorizes, ?_⟩
  intro hcm
  exact cexP_fails_at_000 (hcm 0 0 0)

/-! ===========================================================================
  §3 ⭐⭐⭐⭐⭐ **正确的定理**：条件变量对齐到 `A` 槽后，命题成立
  =========================================================================== -/

variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- ⭐⭐⭐⭐⭐ **G1 的**正确形态**：`Factorizes P ⟹ CondMul (rebindZ P)`。

即 `P(a,b,c) = α a β(a,b) γ(a,c)` ⟹ `P(a,b,c)·P(a) = P(a,b)·P(a,c)`。

**证明**：三个边缘律的显式值（与 `factorizes_condIndepFin` 同款计算，
但**重写在本文件**，以 `(b,c),a` 口径给出）：
$$\mathrm{margXZ} = \alpha(b)\text{...}$$
具体地（`X := B`、`Y := C`、`Z := A`）：
$$\mathrm{margYZ}(c,a) = \sum_b P(a,b,c),\quad
  \mathrm{margXZ}(b,a) = \sum_c P(a,b,c),\quad
  \mathrm{margZ}(a) = \sum_b\sum_c P(a,b,c),$$
代入 `P = α·β·γ` 后两侧同为 `α(a)² β(a,b) γ(a,c) (∑β)(∑γ)`。 -/
theorem factorizes_implies_condMul_Z {P : A × B × C → ℝ} (h : Factorizes P) :
    FinCondIndep.CondMul (rebindZ P) := by
  obtain ⟨α, β, γ, hP⟩ := h
  -- 三个边缘律的显式值（`Z := A` 口径）
  have hXZ : ∀ (b : B) (a : A),
      FinCondIndep.margXZ (rebindZ P) b a = α a * β (a, b) * (∑ c, γ (a, c)) := by
    intro b a
    unfold FinCondIndep.margXZ
    calc ∑ c, rebindZ P ((b, c), a)
        = ∑ c, α a * β (a, b) * γ (a, c) :=
          Finset.sum_congr rfl fun c _ => hP a b c
      _ = α a * β (a, b) * (∑ c, γ (a, c)) := by
          rw [Finset.mul_sum]
  have hYZ : ∀ (c : C) (a : A),
      FinCondIndep.margYZ (rebindZ P) c a = α a * γ (a, c) * (∑ b, β (a, b)) := by
    intro c a
    unfold FinCondIndep.margYZ
    calc ∑ b, rebindZ P ((b, c), a)
        = ∑ b, α a * β (a, b) * γ (a, c) :=
          Finset.sum_congr rfl fun b _ => hP a b c
      _ = α a * γ (a, c) * (∑ b, β (a, b)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
  have hZ : ∀ a : A,
      FinCondIndep.margZ (rebindZ P) a
        = α a * (∑ b, β (a, b)) * (∑ c, γ (a, c)) := by
    intro a
    unfold FinCondIndep.margZ
    calc ∑ b, ∑ c, rebindZ P ((b, c), a)
        = ∑ b, ∑ c, α a * β (a, b) * γ (a, c) :=
          Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c _ => hP a b c
      _ = ∑ b, α a * β (a, b) * (∑ c, γ (a, c)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
      _ = (∑ b, α a * β (a, b)) * (∑ c, γ (a, c)) := by
          rw [Finset.sum_mul]
      _ = α a * (∑ b, β (a, b)) * (∑ c, γ (a, c)) := by
          rw [← Finset.mul_sum]
  intro x y z
  rw [hXZ x z, hYZ y z, hZ z]
  simp only [rebindZ_apply]
  rw [hP z x y]
  ring

/-! ### §3.1 ⭐ **与既有 `factorizes_condIndepFin` 的关系（如实登记）**

`factorizes_condIndepFin`（`Fate/FinMarkov.lean:320`）已证
`Factorizes P ⟹ CondIndepFin P`，而后者**字面就是**
`P(a,b,c)·P(a) = P(a,b)·P(a,c)` —— 与 `CondMul (rebindZ P)` 是**同一命题的重标号**
（`B`、`C` 在 `CondMul` 的 `(X,Y)` 槽里对调）。

**⚠ 因此 §3 的 `factorizes_implies_condMul_Z` 是**重标号**，不是新数学。**
本文件**不把它算作缺口 1 的进展**；它的作用是**界定任务书命题的真实边界**
（真实内容在 §2 的反例与 §4 的对照）。 -/

theorem factorizes_implies_condMul_Z' {P : A × B × C → ℝ} (h : Factorizes P) :
    FinCondIndep.CondMul (rebindZ P) :=
  factorizes_implies_condMul_Z h



/-! ### §5 ⭐⭐ **消费 `RegressFinMarkov` 的跨模块组合定理**（R-46）

本节把 `Fate/RegressFinMarkov.lean` §6 新增的**组合定理**接入本文件的口径，
使 `RegressFinMarkov` 从「外部零引用」变成**被本文件实质调用**。

⚠ **防同义反复审计**：本节定理的**前件**是 `¬ CondIndepFin P` 或 `Factorizes P`
（关于联合律的**存在性/否定**陈述）；**结论**是 `¬ Factorizes P` 或商形式
（关于**边缘律的代数恒等**）。**结论均不在前件中**，
且证明**必须**经过 `RegressFinMarkov` 中的实质引理 —— 若那些引理被删除，
本节编译失败。 -/

/-- ⭐⭐ **消费 1**：条件独立失效 ⟹ 不可父集分解（`RegressFinMarkov` 的逆否组合）。

本文件口径：`¬ CondIndepFin P` 是**可用 `dSep` 侧反例**证出的东西
（见 §2 的 `factorizes_implies_condMul_Z` 的否定面），
故本定理把「图侧否定」转化为「分解式不存在」这一**代数结论**。

⚠ **跨模块**：显式调用 `FateV2.Predict.RegressFinMarkov.regress_not_factorizes_of_not_condIndep`。 -/
theorem not_factorizes_of_not_condIndep {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    {P : A × B × C → ℝ} (h : ¬ CondIndepFin P) :
    ¬ Factorizes P :=
  FateV2.Predict.RegressFinMarkov.regress_not_factorizes_of_not_condIndep h

/-- ⭐⭐ **消费 2**：父集分解 ⟹ 商形式（`RegressFinMarkov` 的 `regress_factorizes_ratio`）。

把 `Factorizes` 一步推到教科书的**比值刻画** `P(b,c|a) = P(b|a)P(c|a)`，
即在 `P(a) ≠ 0` 处成立。这是本文件 `rebindZ` 口径的**商形式对应物**。

⚠ **跨模块**：显式调用 `FateV2.Predict.RegressFinMarkov.regress_factorizes_ratio`。 -/
theorem factorizes_ratio_of_factorizes {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    {P : A × B × C → ℝ} (h : Factorizes P) (a : A) :
    CondIndepFinRatio (P := P) a :=
  FateV2.Predict.RegressFinMarkov.regress_factorizes_ratio h a

end FinMarkov
end FateV2.Predict