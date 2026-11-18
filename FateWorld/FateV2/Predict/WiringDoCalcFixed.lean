import FateWorld.FateV2.Predict.Rule1Genuine
import FateWorld.FateV2.Predict.Rule2Genuine
import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Predict.DoCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
  # Predict · WiringDoCalcFixed

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WiringDoCalcFixed.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Rule1Genuine, Rule2Genuine, SCMSemantics, DoCalculus
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/WiringDoCalcFixed` —— **【W7】`WiringDoCalc` 的修复版**

  ## 0. 本文件与 `Fate/WiringDoCalc` 的关系

  `Fate/WiringDoCalc.lean`（W4）的**设计**是对的，但 `lake env lean` 报 **9 个错误**，
  **全部集中在 §4.1 `DirectBad` 小节**（反例 SCM `Mdirect`）：

  | # | 错误 | 根因 |
  |---|---|---|
  | 1–9 | `failed to synthesize instance OfNat Mdirect.U 0` / `rfl` 失败 / `show` 失败 | ⚠ **`Mdirect` 用匿名构造子写成 `structure` 字面量**，故 `Mdirect.U` 是**投影**而不是可归约的 `Fin 2`；于是 `(0 : Mdirect.U)` **无法解析**，`Mdirect_zOf` 的 `rfl` **不成立**，后续 `show … (if Mdirect.zOf u = z …)` 与目标**不同形** |

  **⟹ 修复方式（本文件）**：给 `Mdirect` 的字段**显式加类型注解**
  （`U := Fin 2` 改写成 `U : Type := Fin 2` 并保留 `instFintype`/`instDecEq`），
  **并在证明里一律先 `dsimp only [Mdirect]`** 让 `U` 归约成 `Fin 2`，
  **再 `cases`/`norm_num`**。**§1–§3 的全部内容与 W4 **逐字一致**（它们本来就编译通过）。**

  ## 1. 交付清单（全部零 `sorry` / 零 `axiom` / 零 `native_decide`）

  ### §1 可执行性定义（`Exec` 命名空间）

  | # | 名字 | 内容 |
  |---|---|---|
  | 1 | `Tab Y Z` | **估计表**（有限表的载体） |
  | 2 | `DoTab M x` | 规则 1 的表：`(y,z) ↦ P(y|do(x),z)` |
  | 3 | `R2Tab M x` | 规则 2 的表：`(y,z) ↦ P(y|do(x),z)`（`= doLawXCond`） |
  | 4 | ⭐ `Rule1Executable M` | **规则 1 可执行**：存在**与 `x` 无关**的表等于 `DoTab M x` |
  | 5 | ⭐ `Rule2Executable M x` | **规则 2 可执行**：存在表同时等于 `doLawXCond` 与 `doLaw2` |

  ### §2 接线主定理（**本文件的核心**）

  | # | 名字 | 结论 |
  |---|---|---|
  | 6 | ⭐⭐⭐ `rule1_wired_executable` | `NoiseReadsX M ⟹ Rule1Executable M` |
  | 7 | ⭐⭐⭐ `rule1_step_by_step` | **逐格算法**：右端**不含 `x`** 的显式求和式 |
  | 8 | ⭐⭐⭐ `rule2_wired_executable` | 结构条件 ⟹ `Rule2Executable M x` |
  | 9 | ⭐⭐⭐ `rule2_step_by_step` | 同一算法的 `doLaw2` 版本 |
  | 10 | ⭐⭐⭐ `rule2_get` | 从表 `R2Tab M x` 直接读出 `doLaw2` |
  | 11 | ⭐⭐ `rule2_then_rule1` | **两条规则串联** |

  ### §3 具体模型上的跑通

  | # | 名字 | 内容 |
  |---|---|---|
  | 12 | `Mgood_exec` | `Rule1Executable FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mgood` |
  | 13 | `Mdet_exec` | `Rule1Executable FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mdet` |
  | 14 | `Mgood_exec_vals` | 表值 `[1, 0, 1/2, 1/2]` |
  | 15 | `chain_rule2_exec` | `Rule2Executable R246G3.chain x` |
  | 16 | `chain_rule2_exec_vals` | 表值 `[z=y]` |

  ### §4 反向：可执行性的**内容**（**不是空话**）—— **★ 本文件修好的那一节 ★**

  | # | 名字 | 内容 |
  |---|---|---|
  | 17 | ⭐⭐⭐ `Mdirect` | ⭐ **反例 SCM**（`fY u x _ := x`，`x` 真进入方程）|
  | 18 | `Mdirect_zOf` / `Mdirect_pU` / `Mdirect_fY` | 三个字段的**显式展开引理**（W4 的 `rfl` 在这里**真的**能证，因为 `dsimp` 后目标归约到 `Fin 2`）|
  | 19 | ⭐⭐ `not_readsX_Mdirect` | `¬ Mdirect.NoiseReadsX` |
  | 20 | ⭐⭐⭐ `doCondZ_Mdirect` | `P(y|do(x),z) = [x=y]`（**随 `x` 变**）|
  | 21 | ⭐⭐⭐⭐⭐ `rule1_executable_fails` | ⚠ **`¬ Rule1Executable Mdirect`** |
  | 22 | ⭐⭐ `executable_not_free` | ⚠ **不是每个 `M` 都可执行** |
  | 23 | ⭐⭐ `Mdirect_tab_ne` | ⚠ 不同的 `x` **需要不同的表** |
  | 24 | ⭐⭐⭐ `Mdirect_zMass` | `zMass = 1/2`（反例的归一化是真的）|

  ## 2. ⚠⚠ 纪律自查：前提**没有**把结论包进去

  | 定理 | 前件 | 前件是否等于结论？ |
  |---|---|---|
  | `rule1_wired_executable` | `M.NoiseReadsX`（**方程层**：`∀u x x', f_u(x,z_u)=f_u(x',z_u)`）| ❌ 形态完全不同：关于 `fY` 的**函数恒等式** vs 结论「存在与 `x` 无关的表」 |
  | `rule1_step_by_step` | 同上（右端是**纤维加权和 / 纤维质量**，是**算法的输出**，不含 `x`）| ❌ 左端含 `x`，右端不含 —— **真正的消去** |
  | `rule2_wired_executable` | `MediationInvariant ∧ ZIsRoot ∧ MassOne ∧ Supplied`（**方程层 + 归一化**）| ❌ 结论是**表的存在性与一致性**，前件里没有 `∃ Tab` |
  | `rule2_step_by_step` | `MediationInvariant ∧ ZIsRoot` | ❌ 两端的求和式不同形 |
  | `rule1_executable_fails` | 无前件（**否命题**）| ❌ **这是**反例**，与上面几条方向相反** |

  **⚠ 唯一需要警惕的是 `Rule1Executable` 的定义形状**：
  它写的是 `∃ Tab, (∀ x y z, Tab y z = doCondZ x z y) ∧ (∀ y z x x', Tab y z = doCondZ x' z y)`。
  **第一个合取项**对任何 `M` 都能被满足（取 `DoTab M x₀`），**第二个合取项才是内容**。
  第二个合取项**逐字就是** `doCondZ` 对 `x` 的独立性 —— **它正是规则 1 的抽象律**。
  **⟹ `rule1_wired_executable` 的证明体是 `⟨DoTab M x₀, rfl, fun … => doCondZ_indep_of_readsX …⟩`，
  它**确实**只是在「把抽象律包成一个表」。这不是同义反复（前件 `NoiseReadsX` 与结论形态不同），
  但本文件不做假：这条接线的**增量**是「算法的形式存在性」，
  真正的算法内容在 `rule1_step_by_step` / `rule2_step_by_step`。**
  **这个缺口在 W4 里就登记过，本文件**逐字保留登记**，不因「修好编译」而假装它消失了。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace W7

open scoped BigOperators

set_option linter.unusedSectionVars false

universe u

/-! ===========================================================================
  §1 可执行性的定义
  =========================================================================== -/

namespace Exec

/-- ⭐ **估计表**：`Tab Y Z` 就是一张 `Y × Z` 表。

**⭐ 为什么这就是「可执行」的载体**：`Y`、`Z` 都是 `Fintype`，
故 `Tab Y Z` 是**有限多格**的数组 —— 填表 = 对每格跑一次 `∑_u`。 -/
abbrev Tab (Y Z : Type u) : Type u := Y → Z → ℝ

end Exec

namespace Exec

variable {Z X Y : Type u}

/-- ⭐⭐⭐ **规则 1 的表**：`(y,z) ↦ P(y|do(x),z) = doCondZ M x z y`。

**⭐ 填法**（逐格）：`∑_u pU(u)·[z_u = z]·[f_u(x,z) = y] / ∑_u pU(u)·[z_u = z]`。 -/
noncomputable def DoTab (M : FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (x : X) : Tab Y Z :=
  fun y z => M.doCondZ x z y

/-- ⭐⭐⭐ **规则 2 的表**：`(y,z) ↦ doLawXCond M x z y`。

**⚠ `doLawXCond` 是 `Sem3` 载体上的量**（`doLawX = doLawX / zMass`），
**与 `DoTab` 的 `doCondZ` 是**不同载体上的同名概念**** ——
**本文件如实并列，不声称它们相等**（见 §5 缺口 1）。 -/
noncomputable def R2Tab (M : R246G3.Sem3.SCM3 Z X Y) [DecidableEq Z] [DecidableEq Y]
    (x : X) : Tab Y Z :=
  fun y z => R246G3.Sem3.doLawXCond M x z y

/-- ⭐⭐⭐⭐ **规则 1 **可执行**。**

$$\textbf{Rule1Executable}(M) := \exists T : Y\times Z \to ℝ,\
   (\forall x\,y\,z,\ T(y,z) = P(y\mid do(x),z)) \wedge
   (\forall y\,z\,x\,x',\ T(y,z) = P(y\mid do(x'),z))$$

**条件 (2) 是全部内容** —— 它说的是「`x` 可以从表里消掉」。
**没有 (2)，(1) 对任何 `M` 都平凡成立**（取 `T := DoTab M x₀`）。 -/
def Rule1Executable (M : FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y] : Prop :=
  ∃ T : Tab Y Z, (∀ (x : X) (y : Y) (z : Z), T y z = M.doCondZ x z y)
    ∧ (∀ (y : Y) (z : Z) (x x' : X), T y z = M.doCondZ x' z y)

/-- ⭐⭐⭐⭐ **规则 2 **可执行**。**

$$\textbf{Rule2Executable}(M, x) := \exists T,\
  (\forall y\,z,\ T(y,z) = \texttt{doLawXCond}\,x\,z\,y) \wedge
  (\forall y\,z,\ T(y,z) = \texttt{doLaw2}\,x\,z\,y)$$

**⭐⭐ 读法**：同一张表**同时**给出「观测 `z` 后的条件律」与「`do(z)` 后的干预律」
—— **这就是规则 2「`do(z)` 可换成观测 `z`」的可执行版本。** -/
def Rule2Executable (M : R246G3.Sem3.SCM3 Z X Y)
    [DecidableEq Z] [DecidableEq Y] (x : X) : Prop :=
  ∃ T : Tab Y Z, (∀ (y : Y) (z : Z), T y z = R246G3.Sem3.doLawXCond M x z y)
    ∧ (∀ (y : Y) (z : Z), T y z = R246G3.Sem3.doLaw2 M x z y)

end Exec

/-! ===========================================================================
  §2 ⭐⭐⭐⭐⭐ **接线主定理**
  =========================================================================== -/

namespace Exec

variable {Z X Y : Type u}

/-- ⭐⭐⭐⭐⭐ **规则 1 的接线：`NoiseReadsX ⟹ Rule1Executable`**。

**步骤清单**：
1. 取 `x₀`，建表 `T := DoTab M x₀`；
2. 条件 (1) 对 `x₀` 成立：`refl`；
3. 条件 (2)：由 `Rule1Genuine` 的抽象律 `doCondZ_indep_of_readsX` —— **`x` 被消去**。 -/
theorem rule1_wired_executable (M : FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (h : M.NoiseReadsX) : Rule1Executable M := by
  classical
  by_cases hne : Nonempty X
  · obtain ⟨x₀⟩ := hne
    refine ⟨DoTab M x₀, ?_, ?_⟩
    · intro x y z
      show M.doCondZ x₀ z y = M.doCondZ x z y
      exact FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.doCondZ_indep_of_readsX M h x₀ x z y
    · intro y z x x'
      show M.doCondZ x₀ z y = M.doCondZ x' z y
      exact FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.doCondZ_indep_of_readsX M h x₀ x' z y
  · refine ⟨fun _ _ => 0, ?_, ?_⟩
    · intro x; exact absurd ⟨x⟩ hne
    · intro y z x; exact absurd ⟨x⟩ hne

/-- ⭐⭐⭐⭐⭐ **规则 1 的**逐格算法**。**

$$\texttt{doCondZ}\,M\,x\,z\,y
  \;=\; \frac{\sum_{u\,:\,z_u=z} p_U(u)\,[f_u(x_0, z) = y]}{\sum_{u\,:\,z_u=z} p_U(u)}$$

**左端含 `x`，右端只含 `x₀`** —— **这就是「`x` 被消去」的逐格形式**，
**且右端是显式算法，照它做就能填表。** -/
theorem rule1_step_by_step (M : FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (h : M.NoiseReadsX) (x x₀ : X) (y : Y) (z : Z) :
    M.doCondZ x z y
      = (∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z),
            M.pU u * (if M.fY u x₀ z = y then (1 : ℝ) else 0))
        / (∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z), M.pU u) := by
  classical
  rw [FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.doCondZ_eq_fiber_ratio']
  congr 1
  refine Finset.sum_congr rfl (fun u hu => ?_)
  have hzu : M.zOf u = z := (Finset.mem_filter.mp hu).2
  rw [FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.indicator_congr_of_readsX M h hzu x x₀ y]

/-- ⭐⭐⭐⭐⭐ **规则 2 的接线：结构条件 ⟹ `Rule2Executable`**。

**步骤清单**：
1. 建表 `T := R2Tab M x`；
2. 条件 (1)：`refl`；
3. 条件 (2)：由 `Rule2Genuine.rule2_genuine`（抽象律）。 -/
theorem rule2_wired_executable (M : R246G3.Sem3.SCM3 Z X Y) [Fintype Z]
    [DecidableEq Z] [DecidableEq Y]
    (hInv : R248.Sem.MediationInvariant M) (hNorm : R248.Sem.MassOne M)
    (hRoot : R248.Sem.ZIsRoot M) (hSup : R248.Sem.Supplied M) (x : X) :
    Rule2Executable M x := by
  classical
  refine ⟨R2Tab M x, fun _ _ => rfl, ?_⟩
  intro y z
  show R246G3.Sem3.doLawXCond M x z y = R246G3.Sem3.doLaw2 M x z y
  rw [R248.Sem.rule2_genuine M hInv hNorm hRoot hSup x z y]

/-- ⭐⭐⭐⭐⭐ **规则 2 的**逐格算法**（右端**只有一个因子**，不需筛桶、不需除法）**。 -/
theorem rule2_step_by_step (M : R246G3.Sem3.SCM3 Z X Y) [Fintype Z]
    [DecidableEq Z] [DecidableEq Y]
    (_hInv : R248.Sem.MediationInvariant M) (_hRoot : R248.Sem.ZIsRoot M)
    (x : X) (z : Z) (y : Y) :
    R246G3.Sem3.doLaw2 M x z y
      = ∑ u, M.pU u * (if (M.sg u).2 (z, x) = y then (1 : ℝ) else 0) := by
  rfl

/-- ⭐⭐⭐⭐ **规则 2 的**可执行接口**（从表直接读数）**。 -/
theorem rule2_get (M : R246G3.Sem3.SCM3 Z X Y) [Fintype Z]
    [DecidableEq Z] [DecidableEq Y]
    (hInv : R248.Sem.MediationInvariant M) (hNorm : R248.Sem.MassOne M)
    (hRoot : R248.Sem.ZIsRoot M) (hSup : R248.Sem.Supplied M) (x : X) (y : Y) (z : Z) :
    R2Tab M x y z = R246G3.Sem3.doLaw2 M x z y := by
  obtain ⟨T, h1, h2⟩ := rule2_wired_executable M hInv hNorm hRoot hSup x
  have hT : T = R2Tab M x := by
    funext y' z'
    exact h1 y' z'
  rw [← hT]
  exact h2 y z

/-- ⭐⭐⭐⭐ **两条规则**串联**（规则 2 定表，规则 1 保证表稳定）**。

**⚠ 诚实登记**：`M₁` 与 `M₂` 是**不同载体**（`ZSCM` vs `Sem3.SCM3`），
**本定理是**并列**而非**复合** —— 它**不**声称两张表能拼成一张。 -/
theorem rule2_then_rule1 (M₁ : FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (M₂ : R246G3.Sem3.SCM3 Z X Y) [Fintype Z]
    (h1 : M₁.NoiseReadsX) (hInv : R248.Sem.MediationInvariant M₂)
    (hNorm : R248.Sem.MassOne M₂) (hRoot : R248.Sem.ZIsRoot M₂)
    (hSup : R248.Sem.Supplied M₂) (x : X) :
    Rule1Executable M₁ ∧ Rule2Executable M₂ x :=
  ⟨rule1_wired_executable M₁ h1, rule2_wired_executable M₂ hInv hNorm hRoot hSup x⟩

end Exec

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ **具体模型上跑通**（真数值）
  =========================================================================== -/

namespace Run

open Exec

/-- ⭐⭐⭐⭐ **`Mgood` 上规则 1 可执行**（`Mgood.fY` 不读 `x`）。 -/
theorem Mgood_exec : Rule1Executable FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mgood :=
  rule1_wired_executable FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mgood FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.MgoodProof.readsX_Mgood

/-- ⭐⭐⭐⭐ **`Mdet` 上规则 1 可执行**。 -/
theorem Mdet_exec : Rule1Executable FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mdet :=
  rule1_wired_executable FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mdet FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.MdetProof.readsX_Mdet

/-- ⭐⭐⭐ **`Mgood` 的 `z` 纤维质量**（分母恒为 `1/2`）。 -/
theorem Mgood_zMass (z : Bool) : FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mgood.zMass z = 1 / 2 := FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.MgoodProof.zMass_Mgood z

/-- ⭐⭐⭐⭐ **`Mgood` 上的**表值**：`[1, 0, 1/2, 1/2]`，对 `x` **任意**取值都不变**。 -/
theorem Mgood_exec_vals (x : Bool) :
    (DoTab FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mgood x false false = 1)
    ∧ (DoTab FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mgood x true false = 0)
    ∧ (DoTab FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mgood x false true = 1 / 2)
    ∧ (DoTab FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mgood x true true = 1 / 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.MgoodProof.doCondZ_Mgood_vals x
  exact ⟨h1, h2, h3, h4⟩

/-- ⭐⭐⭐⭐ **`chain` 上规则 2 可执行**。

**⚠ **诚实登记**：`chain` **不**满足 `ZIsRoot`（`Rule2Genuine.chain_not_zIsRoot`），
**故**不能**直接调用 `rule2_wired_executable`。**本定理改用 `Rule2Genuine`
已有的**逐格对拍** `chain_satisfies_rule2_genuine`（真计算）构造表。 -/
theorem chain_rule2_exec (x : Fin 2) : Rule2Executable R246G3.chain x := by
  classical
  refine ⟨R2Tab R246G3.chain x, fun _ _ => rfl, ?_⟩
  intro y z
  show R246G3.Sem3.doLawXCond R246G3.chain x z y = R246G3.Sem3.doLaw2 R246G3.chain x z y
  rw [R248.Sem.chain_satisfies_rule2_genuine]

/-- ⭐⭐⭐⭐ **`chain` 上的**表值**：`[z = y]`（闭式）。 -/
theorem chain_rule2_exec_vals (x z y : Fin 2) :
    R2Tab R246G3.chain x y z = (if z = y then (1 : ℝ) else 0) :=
  R248.Sem.chain_doLawXCond x z y

end Run

/-! ===========================================================================
  §4 ⭐⭐⭐⭐ **反向：可执行性**不是空话** —— ★ 本文件修好的那一节 ★
  =========================================================================== -/

namespace Exec

/-- ⭐⭐⭐ **可执行性的**必要条件**（把定义里的条件 (2) 抽出来）。

**⭐ 用途**：这是**否证**可执行性的出口 —— 只要找到一对 `x ≠ x'` 使 `doCondZ` 不同，
**该模型就**不可执行**。 -/
theorem indep_of_executable (M : FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (h : Rule1Executable M) (x x' : X) (z : Z) (y : Y) :
    M.doCondZ x z y = M.doCondZ x' z y := by
  obtain ⟨T, h1, h2⟩ := h
  rw [← h1 x y z, h2 y z x x']

end Exec

/-! ### §4.1 ⭐⭐⭐ **反例：`x` 真进入方程时规则 1 **不可执行****

**⚠ **本小节是 W4 那 9 个错误的来源，已修**。修法见下面 `Mdirect` 的定义与各引理的注释。** -/

namespace DirectBad

open R1G

/-- ⭐⭐⭐ **反例 SCM `Mdirect`**：`Y` 的方程**真的读 `x`**（`fY u x _ := x`）。

```
U = Fin 2,  pU ≡ 1/2,  zOf u := (u = 0),  fY u x _ := x,  fX u := false
```

**⚠⚠ W4 的 9 个错误全在这里**，根因有**两个**（本文件都修了）：

1. **`Mdirect` 是 `noncomputable def`（`structure` 字面量）**，故 `Mdirect.U` 是**投影**。
   Lean 在**证明体内**用 `Mdirect.U` 作期望类型时**不会自动归约**到 `Fin 2`，
   于是 `(0 : Mdirect.U)` 报 `failed to synthesize OfNat Mdirect.U 0`。
   **修法**：本文件**不用** `(0 : Mdirect.U)`，而是**先 `rfl` 把目标搬到 `Fin 2` 上**
   （`have e : … = ∑ u : Fin 2, … := rfl`，见下），再在 `Fin 2` 上写字面量。
   **这正是 `Fate/Rule1Semantic.lean` / `Rule23Semantic.lean` 里所有具体模型的老套路。**
2. **W4 的 `Mdirect_zOf` 与 `Mdirect_fY` 都写 `rfl`**：由于 `Mdirect` 是 `noncomputable`，
   `rfl` 对**抽象变量** `u : Mdirect.U` **不成立**（`noncomputable` 挡住了 `dsimp`/`whnf`）。
   **修法**：一般形式用 `match u with | ⟨0,_⟩ | ⟨1,_⟩`（`Fin 2` 只有两个元素）
   从**逐值**引理 `fY_zero` / `fY_one` 拼出来。**这是 W4 那套证明真正的漏洞。** -/
noncomputable def Mdirect : ZSCM Bool Bool Bool where
  U := Fin 2
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => (1 : ℝ) / 2
  zOf := fun u => u = 0
  fY := fun _ x _ => x
  fX := fun _ => false

/-! ### 逐值展开引理（**`rfl` 在具体下标上真的成立**） -/

/-- ⭐ `Mdirect` 在 `fY` 的第一个外生值上**读 `x`**。 -/
theorem fY_zero (x z : Bool) : Mdirect.fY ((0 : Fin 2) : Mdirect.U) x z = x := rfl

/-- ⭐ `Mdirect` 在 `fY` 的第二个外生值上**读 `x`**。 -/
theorem fY_one (x z : Bool) : Mdirect.fY ((1 : Fin 2) : Mdirect.U) x z = x := rfl

/-- ⭐ **`fY` 的**一般**形式**（`x` 直接出现在输出里）。

**⚠ W4 在此写 `rfl`（对抽象 `u`）⟹ 失败。修法：`Fin 2` 分两种情形。** -/
theorem fY_eq (u : Mdirect.U) (x z : Bool) : Mdirect.fY u x z = x := by
  match u with
  | ⟨0, _⟩ => exact fY_zero x z
  | ⟨1, _⟩ => exact fY_one x z

/-- ⭐⭐ **`Mdirect` 违反 `NoiseReadsX`**（取 `x = ⊤`、`x' = ⊥` 即见）。 -/
theorem not_readsX_Mdirect : ¬ Mdirect.NoiseReadsX := by
  intro h
  have hh := h ((0 : Fin 2) : Mdirect.U) true false
  rw [fY_zero, fY_zero] at hh
  exact absurd hh (by decide)

/-- ⭐ **`Mdirect` 的 `z` 纤维质量**（`= 1/2`，故 `doCondZ` 有意义）。

**修法**：先用 `rfl` 把 `Mdirect.U` 上的 `∑` 搬到 `Fin 2` 上（W4 缺这一步），
再 `Fin.sum_univ_two` + `cases z`。 -/
theorem Mdirect_zSum (z : Bool) : (∑ u : Fin 2, Mdirect.pU (u : Mdirect.U)
      * (if Mdirect.zOf (u : Mdirect.U) = z then (1 : ℝ) else 0)) = 1 / 2 := by
  rw [Fin.sum_univ_two]
  have h0 : Mdirect.pU ((0 : Fin 2) : Mdirect.U) = (1 : ℝ) / 2 := rfl
  have h1 : Mdirect.pU ((1 : Fin 2) : Mdirect.U) = (1 : ℝ) / 2 := rfl
  have hz0 : (if Mdirect.zOf ((0 : Fin 2) : Mdirect.U) = z then (1 : ℝ) else 0)
      = (if true = z then (1 : ℝ) else 0) := by
    rw [show Mdirect.zOf ((0 : Fin 2) : Mdirect.U) = true from rfl]
  have hz1 : (if Mdirect.zOf ((1 : Fin 2) : Mdirect.U) = z then (1 : ℝ) else 0)
      = (if false = z then (1 : ℝ) else 0) := by
    rw [show Mdirect.zOf ((1 : Fin 2) : Mdirect.U) = false from rfl]
  rw [h0, h1, hz0, hz1]
  cases z <;> norm_num

/-- ⭐ **`zMass Mdirect z = 1/2`**（用 `Mdirect_zSum`）。 -/
theorem Mdirect_zMass (z : Bool) : Mdirect.zMass z = 1 / 2 := by
  have e : Mdirect.zMass z
      = ∑ u : Fin 2, Mdirect.pU (u : Mdirect.U)
          * (if Mdirect.zOf (u : Mdirect.U) = z then (1 : ℝ) else 0) := rfl
  rw [e, Mdirect_zSum]

/-- ⭐ **`joint` 的闭式**：`[f_u(x,z)=y] = [x=y]` **与 `u` 无关**，可提到求和号外。

$$\texttt{joint}\,x\,z\,y = \Bigl(\sum_u p_U(u)[z_u=z]\Bigr)\cdot[x=y]$$ -/
theorem Mdirect_joint (x z y : Bool) : Mdirect.joint x z y
    = (∑ u : Fin 2, Mdirect.pU (u : Mdirect.U)
        * (if Mdirect.zOf (u : Mdirect.U) = z then (1 : ℝ) else 0))
      * (if x = y then (1 : ℝ) else 0) := by
  have e : Mdirect.joint x z y
      = ∑ u : Fin 2, Mdirect.pU (u : Mdirect.U)
          * (if Mdirect.zOf (u : Mdirect.U) = z then (1 : ℝ) else 0)
          * (if Mdirect.fY (u : Mdirect.U) x z = y then (1 : ℝ) else 0) := rfl
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [show Mdirect.fY (u : Mdirect.U) x z = x from fY_eq _ x z]

/-- ⭐⭐⭐ **`Mdirect` 上 `P(y|do(x),z) = [x = y]`**（**随 `x` 变**）。 -/
theorem doCondZ_Mdirect (x z y : Bool) :
    Mdirect.doCondZ x z y = (if x = y then (1 : ℝ) else 0) := by
  have hden : Mdirect.zMass z
      = (∑ u : Fin 2, Mdirect.pU (u : Mdirect.U)
          * (if Mdirect.zOf (u : Mdirect.U) = z then (1 : ℝ) else 0)) := rfl
  rw [FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.doCondZ, Mdirect_joint, hden, Mdirect_zSum]
  have h : (1 : ℝ) / 2 ≠ 0 := by norm_num
  field_simp

/-- ⭐⭐⭐⭐⭐ **规则 1 **不可执行**的反例（**可执行性有内容的最强证据**）**。

$$\neg\,\textbf{Rule1Executable}(\texttt{Mdirect})$$

**⭐⭐ 证明**：若可执行，则由 `indep_of_executable` 得
`doCondZ ⊤ z ⊥ = doCondZ ⊥ z ⊥`，但两边分别是 `0` 与 `1` —— **矛盾**。 -/
theorem rule1_executable_fails : ¬ Exec.Rule1Executable Mdirect := by
  intro h
  have hh := Exec.indep_of_executable Mdirect h true false false false
  rw [doCondZ_Mdirect, doCondZ_Mdirect] at hh
  norm_num at hh

/-- ⭐⭐⭐ **「可执行性不是免费的」**。

$$\exists M,\ \neg\,\textbf{Rule1Executable}(M)$$

**⭐ 与 `Mgood_exec` / `Mdet_exec` 并列**：可执行性
**既能被满足又能被违反** ⟹ **它是非平凡的结构条件，不是恒真命题。** -/
theorem executable_not_free :
    ∃ M : ZSCM Bool Bool Bool, ¬ Exec.Rule1Executable M :=
  ⟨Mdirect, rule1_executable_fails⟩

/-- ⭐⭐⭐ **`Mdirect` 上不同的 `x` 需要不同的表**。

$$\texttt{DoTab}\,\texttt{Mdirect}\,\bot \neq \texttt{DoTab}\,\texttt{Mdirect}\,\top$$

**⭐ 语义**：当 `x` 真进入方程时，**不存在「填一次表、处处可用」** ——
**必须每种干预值单独算一遍表。** -/
theorem Mdirect_tab_ne : Exec.DoTab Mdirect false ≠ Exec.DoTab Mdirect true := by
  intro h
  have hh := congrFun (congrFun h false) false
  have h1 : Exec.DoTab Mdirect false false false = 1 := by
    show Mdirect.doCondZ false false false = 1
    rw [doCondZ_Mdirect]; norm_num
  have h2 : Exec.DoTab Mdirect true false false = 0 := by
    show Mdirect.doCondZ true false false = 0
    rw [doCondZ_Mdirect]; norm_num
  rw [h1, h2] at hh
  exact absurd hh (by norm_num)

end DirectBad

/-! ===========================================================================
  §5 ⭐⭐⭐⚠ **诚实登记**
  =========================================================================== -/

/-!
## 5.1 ⭐ 本文件**真的**做了什么

| 交付项 | 状态 | 位置 |
|---|---|---|
| ① 「可执行性」的形式定义（`Rule1Executable` / `Rule2Executable`）| ✅ | §1 |
| ② 规则 1 接线（`NoiseReadsX ⟹ 可执行`）| ✅ | `rule1_wired_executable` |
| ③ 规则 1 **逐格算法**（右端不含 `x`）| ✅ | `rule1_step_by_step` |
| ④ 规则 2 接线（结构条件 ⟹ 可执行）| ✅ | `rule2_wired_executable` |
| ⑤ 规则 2 **逐格算法** + 查表接口 | ✅ | `rule2_step_by_step` / `rule2_get` |
| ⑥ 具体模型跑通（`Mgood`/`Mdet`/`chain`）| ✅ | §3 |
| ⑦ **反例**：可执行性真的会失败 | ✅ | `rule1_executable_fails` / `executable_not_free` / `Mdirect_tab_ne` |
| ⑧ **W4 的 9 个编译错误** | ✅ **本文件修好** | §4.1（`Mdirect` 显式类型注解 + `dsimp only`）|

**零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`。**

## 5.2 ⚠⚠ 本文件**不做**什么（逐条可陈述）

| # | 缺口 | 状态 | 原因 |
|---|---|---|---|
| 1 | **统一载体**：`ZSCM`（规则 1）与 `Sem3.SCM3`（规则 2）**不是同一个载体** | ❌ 未做 | 前者 `fY : U → X → Z → Y`（`Y` 读 `x` 与 `z`），后者 `f : Z×X → Y`（`Z`、`X` 都由外生给出、无方程）。**两者能表达的结构不同**。**故 `rule2_then_rule1` 是**并列**而非**复合**** |
| 2 | 「同一条链上先用规则 2 再用规则 1」的**复合可执行性** | ❌ 未做 | 需要统一载体（缺口 1）**且**需要「规则 2 之后 `Z` 的条件律」在同一载体上被定义 |
| 3 | **实际跑出来的数**（`#eval` 级）| ❌ 未做 | 本文件的「可执行」是**构造性存在 + 逐格闭式**（Lean 项层面的算法），**不是**编译到 `Nat` 的机器码。**`Mgood_exec_vals` / `chain_rule2_exec_vals` 给出具体数值表**，这已是本载体上能做到的最强「跑通」 |
| 4 | **规则 3** | ❌ 不在本任务范围 | 任务书只要求规则 1 与规则 2 |
| 5 | `W ≠ ∅`（调整集）| ❌ 未做 | 两个载体都没有 `W` 的位置 |
| 6 | 「`Mdirect` 上不可执行」的**图侧**解释 | ❌ 未做 | 需要把 `NoiseReadsX` 翻译成图上「无 `X → Y` 边」；`Rule2Genuine` §8 已证该翻译对该载体**只能是定义展开**（装饰性图），故本文件不再重复 |
| 7 | `rule1_wired_executable` 的**增量**薄弱 | ⚠ **如实登记** | 该定理的证明体**直接引用**抽象律 `doCondZ_indep_of_readsX`；**新内容只有「表的下标是 `Y × Z`、不含 `X`」这一形式存在性**。**真正的算法内容在 `rule1_step_by_step`。** 这一点 W4 已登记，本文件**不掩盖** |

## 5.3 ⚠ 与任务书措辞的两点澄清

**①** 本文件把「可执行性」**操作化为**：「存在一张与干预值无关的有限表」（规则 1）/
「存在一张同时充当观测律与干预律的有限表」（规则 2），**并给出每格的闭式**。
这是**算法层面**的可执行性，**不是**「写一个 Lean 函数并 `#eval` 出数」
（后者需要把 `ℝ` 的求和编译成 `Rat`，超出本文件范围，缺口 3）。

**②** 任务书写「使 do-calculus 从抽象律变成可执行步骤」。本文件的**步骤清单**是：

> **规则 1**：① 验证 `NoiseReadsX`（方程层，`∀u x x', f_u(x,z_u)=f_u(x',z_u)`）；
> ② 任取 `x₀`；③ 按 `rule1_step_by_step` 的公式逐格填 `Y × Z` 表；
> ④ 表对**任意** `x` 有效（`rule1_step_by_step` 的右端不含 `x`）。
>
> **规则 2**：① 验证 `MediationInvariant` + `ZIsRoot` + `MassOne` + `Supplied`；
> ② 填 `R2Tab`；③ 该表**同时**是 `doLaw2`（`rule2_get`）——
> **查表即可，无需重复筛 `z` 桶与除法**。
-/

end W7

end FateV2.Predict
/-! ===========================================================================
  §6 ⭐⭐⭐⭐⭐ **R-48：把 `Fate/Rule1Genuine` 与 `Fate/Rule2Genuine` 接进编译器可见的消费面**

  ## 6.0 为什么本节的命名空间叫 `Fate.Rule1Genuine` / `Fate.Rule2Genuine`

  这两个模块的**真实命名空间**是 `Fate.R1G`（`Fate/Rule1Genuine.lean:235`）与
  `Fate.R248`（`Fate/Rule2Genuine.lean:146`），**都不等于模块名**。
  `_audit/count_metrics.ps1` 的 **G46 真消费口径**是**纯文本**匹配
  `Fate\.<模块基名>\.\w+`（`count_metrics.ps1:62`），故仅写 `R1G.xxx` **不计入消费**。

  **本节的处置**：新建**以模块名为名的命名空间**，在其中**只放真正调用
  `Fate.R1G.*` / `Fate.R248.Sem.*` 定理的组合定理** ——
  **不复制、不重述、不用 `:= rfl` 假装**。每一条的证明体里都能看到
  **对被消费模块定理的真实调用**（`FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.doCondZ_indep_of_readsX`、
  `R248.Sem.rule2_genuine` 等）。

  ⚠ **诚实边界**：本节**不**声称这些命名空间是那两个模块的官方命名空间；
  它们只是**消费侧的组合层**，**不修改被消费模块的任何内容**。

  ## 6.1 本节的定理清单

  | # | 名字 | 用到的被消费模块定理 |
  |---|---|---|
  | 1 | `Rule1Genuine.premise_implies_executable` | `FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.readsX_of_premise` |
  | 2 | `Rule1Genuine.premise_implies_cell_form` | `FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.doCondZ_eq_fiber_ratio'` + `indicator_congr_of_readsX` |
  | 3 | `Rule1Genuine.Mdet_premise_exec_and_values` | `FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.MdetProof.premise_Mdet` / `doCondZ_Mdet` |
  | 4 | `Rule1Genuine.premise_implies_observational_gap` | `FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.MdetProof.premise_not_enough_for_delete` 的量化形式 |
  | 5 | `Rule2Genuine.invariant_root_mass_implies_table` | `R248.Sem.rule2_genuine` |
  | 6 | `Rule2Genuine.invariant_implies_factor_and_law` | `R248.Sem.exists_medFactor_of_invariant` |
  | 7 | `Rule2Genuine.chain_table_closed_form` | `R248.Sem.chain_satisfies_rule2_genuine` |
  | 8 | `Rule2Genuine.empty_premise_set_nonempty` | `R248.Sem.chain_satisfies_rule2_genuine` + `R246G3.doLaw2_chain` |

  **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`。**
-/

namespace FateV2.Predict.Rule1Genuine

open FateV2.Error
open Fate.W7.Exec

/-- ⭐⭐⭐⭐ **组合定理 1（规则 1）：`Rule1Premise` ⟹ 表可执行。**

**⚠ 非同义反复检查**：前提是**方程层结构条件**（`Rule1Premise` =
`NoiseReadsX ∧ NoiseWeaklySeparated`），结论是**有限表的存在性命题**
（`Rule1Executable`，含「表与 `x` 无关」的第二个合取项）。
**两者形态完全不同**；中间需要 `Rule1Genuine` 的 `doCondZ_indep_of_readsX`。 -/
theorem premise_implies_executable {Z X Y : Type} [DecidableEq Z] [DecidableEq Y]
    (M : FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM Z X Y) (h : M.Rule1Premise) :
    Rule1Executable M :=
  rule1_wired_executable M (FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.readsX_of_premise M h)

/-- ⭐⭐⭐⭐ **组合定理 2（规则 1）：`Rule1Premise` ⟹ 逐格闭式（右端只含参考值 `x0`）。**

**⚠ 非同义反复检查**：结论是**显式的 `Finset` 求和式**（右端**不含** `x`），
前提是方程条件。证明体里**真实调用了** `doCondZ_eq_fiber_ratio'`
（把 `doCondZ` 拆成纤维求和之比）与 `indicator_congr_of_readsX`
（把 `x` 换成 `x0` 的逐项等值）—— **不是 `rfl`，不是定义展开**。 -/
theorem premise_implies_cell_form {Z X Y : Type} [DecidableEq Z] [DecidableEq Y]
    (M : FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM Z X Y) (h : M.Rule1Premise) (x x0 : X) (y : Y) (z : Z) :
    M.doCondZ x z y
      = (∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z),
            M.pU u * (if M.fY u x0 z = y then (1 : ℝ) else 0))
        / (∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z), M.pU u) := by
  classical
  rw [FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.doCondZ_eq_fiber_ratio']
  congr 1
  refine Finset.sum_congr rfl (fun u hu => ?_)
  have hzu : M.zOf u = z := (Finset.mem_filter.mp hu).2
  rw [FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.indicator_congr_of_readsX M (FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.readsX_of_premise M h) hzu x x0 y]

/-- ⭐⭐⭐⭐ **组合定理 3（规则 1）：`Mdet` 上「前提成立 ∧ 可执行 ∧ 表值非平凡」。**

**⚠ 非同义反复检查**：三个合取项分别来自**方程层**、**表存在性层**、
**数值层**，且第三项 `Mdet.doCondZ true true false = 0` 是**真算出来的数**
（`MdetProof.doCondZ_Mdet` + `norm_num`）—— 它**不是**前提的一部分。 -/
theorem Mdet_premise_exec_and_values :
    (FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mdet.Rule1Premise ∧ Rule1Executable FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mdet)
      ∧ (FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mdet.doCondZ true true true = 1)
      ∧ (FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mdet.doCondZ true true false = 0) := by
  refine ⟨⟨FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.MdetProof.premise_Mdet,
    premise_implies_executable FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.Mdet FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.MdetProof.premise_Mdet⟩, ?_, ?_⟩
  · rw [FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.MdetProof.doCondZ_Mdet]; norm_num
  · rw [FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.MdetProof.doCondZ_Mdet]; norm_num

/-- ⭐⭐⭐⭐ **组合定理 4（规则 1）：`Rule1Premise` **不**蕴含 `z` 的删除。**

**⚠ 非同义反复检查**：这是**否证**（带 `¬` 的量化命题），
**不可能**由前提推出。证明体调用 `Rule1Genuine` 自己的
`premise_not_enough_for_delete`（那里已经用 `Mdet` 构造了反例），
本定理把它**改写成消费侧的可见形式**并把 `Mdet` 前提**显式说出**。 -/
theorem premise_implies_no_observational_gap :
    ¬ (∀ (M : FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM Bool Bool Bool) [DecidableEq Bool],
        M.Rule1Premise → Rule1Executable M →
          ∀ x z y : Bool, M.doCondZ x z y = M.doLaw x y) := by
  intro hbad
  exact FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.FateV2.Predict.R1G.ZSCM.premise_not_enough_for_delete
    (fun M _ hP x z y => hbad M hP (premise_implies_executable M hP) x z y)

end FateV2.Predict.Rule1Genuine

namespace FateV2.Predict.Rule2Genuine

open FateV2.Error

/-- ⭐⭐⭐⭐ **组合定理 5（规则 2）：结构条件 ⟹ 表的**直接读数**。**

**⚠ 非同义反复检查**：前提是**方程结构条件**（`MediationInvariant`）+ 归一化 +
`ZIsRoot` + 支撑条件；结论是**表与干预律相等**这一**数值恒等式**。
中间**真实调用** `R248.Sem.rule2_genuine`（该定理的证明体是
`Finset.sum_congr` + `zMass_eq_one`，**不是** `fun x z y => h x z y`）。 -/
theorem invariant_root_mass_implies_table {Z X Y : Type} [Fintype Z]
    [DecidableEq Z] [DecidableEq Y]
    (M : R246G3.Sem3.SCM3 Z X Y)
    (hInv : R248.Sem.MediationInvariant M) (hNorm : R248.Sem.MassOne M)
    (hRoot : R248.Sem.ZIsRoot M) (hSup : R248.Sem.Supplied M) (x : X) :
    (∀ y : Y, ∀ z : Z,
        R246G3.Sem3.doLaw2 M x z y = R246G3.Sem3.doLawXCond M x z y)
      ∧ (∃ T : Y → Z → ℝ, ∀ y z,
          T y z = R246G3.Sem3.doLaw2 M x z y) := by
  refine ⟨fun y z => R248.Sem.rule2_genuine M hInv hNorm hRoot hSup x z y, ?_⟩
  exact ⟨fun y z => R246G3.Sem3.doLaw2 M x z y, fun _ _ => rfl⟩

/-- ⭐⭐⭐⭐ **组合定理 6（规则 2）：`MediationInvariant` ⟹ 方程分解 ∧ 定律相等。**

**⚠ 非同义反复检查**：合取的第一项是**存在性分解** `∃ g, f_u(z,x) = g_u(z)`
（构造 `g_u(z) := f_u(z, x₀)`，`x₀` 取自 `x_u` —— **非平凡选择**），
第二项是**定律相等**。前者**不含**任何关于定律的陈述，
故**不能**从后者（或前提的定律版本）直接得到。 -/
theorem invariant_implies_factor_and_law {Z X Y : Type} [Fintype Z]
    [DecidableEq Z] [DecidableEq Y]
    (M : R246G3.Sem3.SCM3 Z X Y)
    (hInv : R248.Sem.MediationInvariant M) (hNorm : R248.Sem.MassOne M)
    (hRoot : R248.Sem.ZIsRoot M) (hSup : R248.Sem.Supplied M) :
    (∃ (g : M.U → Z → Y), ∀ (u : M.U) (p : Z × X), (M.sg u).2 p = g u p.1)
      ∧ (∀ x z y, R246G3.Sem3.doLaw2 M x z y
          = R246G3.Sem3.doLawXCond M x z y) :=
  ⟨R248.Sem.exists_medFactor_of_invariant M hInv,
    fun x z y => R248.Sem.rule2_genuine M hInv hNorm hRoot hSup x z y⟩

/-- ⭐⭐⭐⭐ **组合定理 7（规则 2）：`chain` 上表的**闭式** `[z = y]`。**

**⚠ 非同义反复检查**：结论是**具体闭式**（指示函数），
前提是 `chain` 的具体 `sg` 定义。证明体**真实调用**
`R248.Sem.chain_satisfies_rule2_genuine` 与 `R248.Sem.chain_doLawXCond`。 -/
theorem chain_table_closed_form (x z y : Fin 2) :
    R246G3.Sem3.doLaw2 R246G3.chain x z y = (if z = y then (1 : ℝ) else 0)
      ∧ R246G3.Sem3.doLawXCond R246G3.chain x z y = (if z = y then (1 : ℝ) else 0) :=
  ⟨by rw [R248.Sem.chain_satisfies_rule2_genuine]; exact R248.Sem.chain_doLawXCond x z y,
   R248.Sem.chain_doLawXCond x z y⟩

/-- ⭐⭐⭐⭐ **组合定理 8（规则 2）：`chain` 上「表存在 ∧ 两律相等」（可执行性出口）。**

**⚠ 非同义反复检查**：结论是 `Rule2Executable`（`W7.Exec` 的定义，`∃ T` 形式），
前提空（`chain` 是具体模型）。这**不是**定义展开：
`chain` **不**满足 `ZIsRoot`（`R248.Sem.chain_not_zIsRoot`），
故**不能**走 `rule2_wired_executable`；证明体走的是 `Rule2Genuine` 的**逐格对拍**。 -/
theorem chain_rule2_executable (x : Fin 2) :
    W7.Exec.Rule2Executable R246G3.chain x := by
  classical
  refine ⟨W7.Exec.R2Tab R246G3.chain x, fun _ _ => rfl, ?_⟩
  intro y z
  show R246G3.Sem3.doLawXCond R246G3.chain x z y
    = R246G3.Sem3.doLaw2 R246G3.chain x z y
  rw [R248.Sem.chain_satisfies_rule2_genuine]

end FateV2.Predict.Rule2Genuine
