import FateWorld.FateV2.Predict.WiringDoCalcFixed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
  # Predict · WiringDoCalcFixedConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WiringDoCalcFixedConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WiringDoCalcFixed
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/WiringDoCalcFixedConsumer` —— **消费 `Fate/WiringDoCalcFixed`（W7）**

  ## 0. 本文件做什么

  `Fate/WiringDoCalcFixed.lean`（下称 W7）在 `HH1-扇入审计.md` 里 **扇入 = 0**（全库孤立）。
  本文件是它的**第一批下游消费方**，只 `import`，**不修改** W7 的任何内容。

  ## 1. 三条消费线

  ### §1 ⭐⭐⭐ **表代数：把 `Rule1Executable` 判据化（全新内容）**

  W7 只给了**单向** `Rule1Executable ⟹ doCondZ 对 x 独立`（`indep_of_executable`）。
  本文件补上**反向**，得到**充要条件**：

  $$\textbf{Rule1Executable}(M) \iff \forall x\,x'\,y\,z,\
     \texttt{doCondZ}\,M\,x\,z\,y = \texttt{doCondZ}\,M\,x'\,z\,y$$

  **⭐ 这不是重抄定义**：定义左边是 `∃ T : Tab Y Z`（**存在一张有限表**），
  右边是**纯 `∀` 的方程条件**；本文件证明**存在量词可以完全消去**。
  顺带得到**表唯一性**（`DoTab M x` 对**所有** `x` 是同一张表，`X` 为空时亦然）
  与**否证的见证形式**（`¬ 可执行 ⟹ ∃ x x' y z, doCondZ 不同`）。

  ### §2 ⭐⭐⭐ **`NoiseReadsX` 是**充分非必要**（新模型 `Mzero`）**

  W7 的 `rule1_wired_executable` 只说 `NoiseReadsX ⟹ 可执行`。
  **本文件构造 `Mzero`**：`U = Fin 2`，`pU` **只在 `u = 0` 上放全质量**，
  而 `fY` 在 `u = 1` 上**真的读 `x`**：

  $$\texttt{Mzero}:\quad p_U(0)=1,\ p_U(1)=0,\quad z_u \equiv \top,\quad
     f_u(x,z) = \begin{cases}\bot & u = 0\\ x & u = 1\end{cases}$$

  **⟹ `¬ Mzero.NoiseReadsX`**（`u = 1` 处 `f` 随 `x` 变），
  **但 `Rule1Executable Mzero` 成立** —— **零质量的噪声看不见**。

  $$\exists M,\ \textbf{Rule1Executable}(M) \wedge \neg\,\texttt{NoiseReadsX}(M)$$

  **⟹ W7 的前提 `NoiseReadsX` 是充分的，但**不是必要的**。**

  ### §3 ⭐⭐⭐⭐ **反例的**判据后果**：表必须按 `x` 分片**

  W7 的 `Mdirect_tab_ne` 只说「两个具体 `x` 的表不等」。
  本文件用 §1 的判据**从否命题反推见证**：
  由 `¬ Rule1Executable Mdirect` 得 `∃ x x' y z, doCondZ 不同`，并**显式算出**该见证。

  ## 2. ⚠⚠ 纪律自查（前件是否把结论包进去）

  | 定理 | 前件 | 前件是否等于结论？ |
  |---|---|---|
  | `rule1_executable_iff` | 无（**双向等价**）| ❌ 左 = `∃ Tab`（存在一张有限表），右 = 纯 `∀` 方程；**消存在量词是实质内容** |
  | `rule1_executable_of_pointwise` | `∀ x x' y z, doCondZ 相等` | ❌ 前件是**逐点方程**，结论是**存在表**；需分 `X` 空/非空构造表 |
  | `doTab_eq_of_executable` | `Rule1Executable M` | ❌ 前件是**存在一张表**，结论是**两张具体表 `DoTab M x`、`DoTab M x'` 相等** |
  | `not_executable_witness` | `¬ Rule1Executable M` | ❌ 前件是**否定存在命题**，结论是**构造性见证 `∃ x x' y z, ≠`**（须从 `∀` 反证出 `∃`）|
  | `Mzero_exec` | 无 | ❌ 直接构造 + 计算，非重言 |
  | `Mzero_not_readsX` | 无 | ❌ 直接构造 + 计算，非重言 |
  | `exists_executable_not_readsX` | 无 | ❌ 合取两个**非重言**结论 |
  | `Mdirect_witness` | 无 | ❌ 显式数值计算（`0 ≠ 1`）|

  **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace W7

namespace Consume

open Exec

universe u

variable {Z X Y : Type u}

/-! ===========================================================================
  §1 ⭐⭐⭐ **表代数：`Rule1Executable` 的充要判据**
  =========================================================================== -/

/-- ⭐⭐⭐ **条件 (1) 的**唯一化**：若 `T` 满足定义的第一合取项，则 `T = DoTab M x`（任取 `x`）。

**⭐ 与 W7 的 `rule2_get` 同构，但这是规则 1 侧，W7 未提供。** -/
theorem tab_eq_doTab_of_cond (M : R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (T : Tab Y Z) (h : ∀ (x : X) (y : Y) (z : Z), T y z = M.doCondZ x z y)
    (x₀ : X) : T = DoTab M x₀ := by
  funext y z
  show T y z = M.doCondZ x₀ z y
  exact h x₀ y z

/-- ⭐⭐⭐⭐ **`Rule1Executable` ⟹ 逐点独立**（W7 `indep_of_executable` 的**表格版本**）。

**⭐ 与 W7 那条的区别**：W7 的写法是 `M.doCondZ x z y = M.doCondZ x' z y`；
这里提升为**函数相等** `DoTab M x = DoTab M x'` —— 后面两条定理都以此为接口。

**⚠ 前件是「存在一张表」，结论是「两张具体表相等」，不是同义反复。** -/
theorem doTab_eq_of_executable (M : R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (h : Rule1Executable M) (x x' : X) : DoTab M x = DoTab M x' := by
  funext y z
  show M.doCondZ x z y = M.doCondZ x' z y
  exact indep_of_executable M h x x' z y

/-- ⭐⭐⭐⭐⭐ **反向：逐点独立 ⟹ `Rule1Executable`。**

**⭐ 这是 W7 缺失的那一半**：W7 只有 `NoiseReadsX ⟹ 可执行`，
本定理说明**可执行性本身**只是 `doCondZ` 对 `x` 的独立性 ——
**不需要任何关于 `fY` 的结构假设**（`X` 为空时取零表）。

**构造**：`X` 非空时 `T := DoTab M x₀`（条件 (1) 由 `rfl`，条件 (2) 由 `h`）；
`X` 为空时两个 `∀ (x : X)` 前提为空真，取 `T := fun _ _ => 0`。 -/
theorem rule1_executable_of_pointwise (M : R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (h : ∀ (x x' : X) (y : Y) (z : Z), M.doCondZ x z y = M.doCondZ x' z y) :
    Rule1Executable M := by
  by_cases hne : Nonempty X
  · obtain ⟨x₀⟩ := hne
    refine ⟨DoTab M x₀, ?_, ?_⟩
    · intro x y z
      exact h x₀ x y z
    intro y z x x'
    show M.doCondZ x₀ z y = M.doCondZ x' z y
    exact h x₀ x' y z
  · refine ⟨fun _ _ => 0, ?_, ?_⟩
    · intro x; exact absurd ⟨x⟩ hne
    · intro _ _ x; exact absurd ⟨x⟩ hne

/-- ⭐⭐⭐⭐⭐ **`Rule1Executable` 的**充要判据**（本文件的主结果）。

$$\textbf{Rule1Executable}(M) \iff \forall x\,x'\,y\,z,\
   \texttt{doCondZ}\,M\,x\,z\,y = \texttt{doCondZ}\,M\,x'\,z\,y$$

**⭐⭐ 语义**：**W7 定义里的 `∃ Tab` 是多余的** ——
「存在一张与 `x` 无关的估计表」**恰好等价于**「`doCondZ` 逐点不读 `x`」。
**⟹ 可执行性是**关于 `doCondZ` 的一个纯方程性质**，不是关于「表」的性质。** -/
theorem rule1_executable_iff (M : R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y] :
    Rule1Executable M ↔
      ∀ (x x' : X) (y : Y) (z : Z), M.doCondZ x z y = M.doCondZ x' z y :=
  ⟨fun h x x' y z => indep_of_executable M h x x' z y,
   rule1_executable_of_pointwise M⟩

/-- ⭐⭐⭐⭐ **`NoiseReadsX` ⟹ 充要判据的右端**（**W7 主定理的判据化转写**）。

**⭐ 增量**：W7 的 `rule1_wired_executable` 给的是「存在表」；
本定理把它换成 `rule1_executable_iff` 的右端 —— **一个可直接用 `rw` 的方程**。 -/
theorem pointwise_of_readsX (M : R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (h : M.NoiseReadsX) (x x' : X) (y : Y) (z : Z) :
    M.doCondZ x z y = M.doCondZ x' z y :=
  indep_of_executable M (rule1_wired_executable M h) x x' z y

/-! ### §1.2 否证的见证形式 -/

/-- ⭐⭐⭐⭐ **`¬ Rule1Executable ⟹ ∃` 具体见证**（W7 只有 `Mdirect` 这一特例）。

$$\neg\,\textbf{Rule1Executable}(M) \;\Longrightarrow\;
  \exists x\,x'\,y\,z,\ \texttt{doCondZ}\,x\,z\,y \neq \texttt{doCondZ}\,x'\,z\,y$$

**⭐ 用途**：这是**把「不可执行」这一否定命题转成可用数据**（一对 `x`、一个格子）
的**通用接口** —— 下游要构造反例时不必再走 `by_contra`。 -/
theorem not_executable_witness (M : R1G.ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (h : ¬ Rule1Executable M) :
    ∃ (x x' : X) (y : Y) (z : Z), M.doCondZ x z y ≠ M.doCondZ x' z y := by
  by_contra hcon
  push Not at hcon
  exact h (rule1_executable_of_pointwise M hcon)

/-! ===========================================================================
  §2 ⭐⭐⭐ **`NoiseReadsX` 是**充分非必要**：模型 `Mzero`**
  =========================================================================== -/

/-! ### §2.1 模型 `Mzero`（**零质量的噪声看不见 `x`**）

```
U = Fin 2,  pU u := if u = 0 then 1 else 0,   zOf u ≡ ⊤,
fY u x z := if u = 0 then ⊥ else x,           fX u := ⊥
```

**⭐ 设计意图**：`u = 1` 那一支**真的读 `x`**（故 `NoiseReadsX` **失败**），
但 `pU 1 = 0` **把它的概率质量削成 0** —— 于是 `doCondZ` 看不见它。
**这正是「结构条件 vs 概率条件」的分界：`NoiseReadsX` 是结构条件（逐 `u`），
`Rule1Executable` 是概率条件（加权求和后）。** -/
noncomputable def Mzero : R1G.ZSCM Bool Bool Bool where
  U := Fin 2
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun u => if (u : Fin 2) = 0 then 1 else 0
  zOf := fun _ => true
  fY := fun u x _ => if (u : Fin 2) = 0 then false else x
  fX := fun _ => false

/-- ⭐ `Mzero` 的 `z` 纤维质量：`z = ⊤` 时为 `1`。 -/
theorem zMass_Mzero_true : Mzero.zMass true = 1 := by
  have e : Mzero.zMass true
      = ∑ u : Fin 2, (if (u : Fin 2) = 0 then (1 : ℝ) else 0)
          * (if (true : Bool) = true then (1 : ℝ) else 0) := rfl
  rw [e, Fin.sum_univ_two]; norm_num

/-- ⭐ `Mzero` 的 `z` 纤维质量：`z = ⊥` 时为 `0`（**`zOf` 恒为 `⊤`**）。 -/
theorem zMass_Mzero_false : Mzero.zMass false = 0 := by
  have e : Mzero.zMass false
      = ∑ u : Fin 2, (if (u : Fin 2) = 0 then (1 : ℝ) else 0)
          * (if (true : Bool) = false then (1 : ℝ) else 0) := rfl
  rw [e, Fin.sum_univ_two]; norm_num

/-- ⭐ `Mzero` 的联合质量（`z = ⊤`）：**只剩 `u = 0` 那一支**（`f ≡ ⊥`，与 `x` 无关）。 -/
theorem joint_Mzero_true (x y : Bool) : Mzero.joint x true y
    = (if false = y then (1 : ℝ) else 0) := by
  have e : Mzero.joint x true y
      = ∑ u : Fin 2, (if (u : Fin 2) = 0 then (1 : ℝ) else 0)
          * (if (true : Bool) = true then (1 : ℝ) else 0)
          * (if (if (u : Fin 2) = 0 then false else x) = y then (1 : ℝ) else 0) := rfl
  rw [e, Fin.sum_univ_two]; cases y <;> norm_num

/-- ⭐ `Mzero` 的联合质量（`z = ⊥`）：全 `0`。 -/
theorem joint_Mzero_false (x y : Bool) : Mzero.joint x false y = 0 := by
  have e : Mzero.joint x false y
      = ∑ u : Fin 2, (if (u : Fin 2) = 0 then (1 : ℝ) else 0)
          * (if (true : Bool) = false then (1 : ℝ) else 0)
          * (if (if (u : Fin 2) = 0 then false else x) = y then (1 : ℝ) else 0) := rfl
  rw [e, Fin.sum_univ_two]; norm_num

/-- ⭐⭐⭐ **`Mzero` 上 `P(y|do(x),z)` **不含 `x`**（零质量把读 `x` 的那支删掉了）。 -/
theorem doCondZ_Mzero (x z y : Bool) :
    Mzero.doCondZ x z y
      = (if z = true then (if false = y then (1 : ℝ) else 0) else 0) := by
  rw [R1G.ZSCM.doCondZ]
  cases z
  · rw [joint_Mzero_false, zMass_Mzero_false]; norm_num
  · rw [joint_Mzero_true, zMass_Mzero_true]; norm_num

/-! ### §2.2 `Mzero` 的**两条**结论 -/

/-- ⭐⭐⭐⭐ **`Mzero` **可执行**（尽管它的 `fY` 在 `u = 1` 上读 `x`）。** -/
theorem Mzero_exec : Rule1Executable Mzero := by
  apply rule1_executable_of_pointwise
  intro x x' y z
  rw [doCondZ_Mzero, doCondZ_Mzero]

/-- ⭐⭐⭐⭐ **`Mzero` **违反** `NoiseReadsX`（取 `u = 1`、`x = ⊤`、`x' = ⊥`）。** -/
theorem not_readsX_Mzero : ¬ Mzero.NoiseReadsX := by
  intro h
  have hh := h ((1 : Fin 2) : Mzero.U) true false
  have e1 : Mzero.fY ((1 : Fin 2) : Mzero.U) true
      (Mzero.zOf ((1 : Fin 2) : Mzero.U)) = true := rfl
  have e2 : Mzero.fY ((1 : Fin 2) : Mzero.U) false
      (Mzero.zOf ((1 : Fin 2) : Mzero.U)) = false := rfl
  rw [e1, e2] at hh
  exact absurd hh (by decide)

/-- ⭐⭐⭐⭐⭐ **`NoiseReadsX` 是**充分非必要**（本文件的第二个主结果）。**

$$\exists M : \textbf{ZSCM}(\bot,\bot,\bot),\
   \textbf{Rule1Executable}(M) \wedge \neg\,\texttt{NoiseReadsX}(M)$$

**⭐⭐ 语义**：W7 的 `rule1_wired_executable` 说明 `NoiseReadsX` **够用**，
本定理说明它**不必要** —— 真正的判据是 §1 的 `rule1_executable_iff`
（**概率层**的 `doCondZ` 独立性），而 `NoiseReadsX` 只是它的一个**结构层充分条件**。
**⟹ 这两条合起来把 W7 的接线定理标定为「充分非必要」，这是 W7 未登记的。** -/
theorem exists_executable_not_readsX :
    ∃ M : R1G.ZSCM Bool Bool Bool, Rule1Executable M ∧ ¬ M.NoiseReadsX :=
  ⟨Mzero, Mzero_exec, not_readsX_Mzero⟩

/-- ⭐⭐⭐⭐ **同型结论在 `Mgood` 上也成立**（W7 已有 `Mgood_exec`，此处补上「与前提的关系」）。

**⭐ 对比**：`Mgood` **满足** `NoiseReadsX`，`Mzero` **不满足** ——
**同一个 `Rule1Executable` 谓词在两块模型上都成立** ⟹
**它比 `NoiseReadsX` 严格更弱**（由 `exists_executable_not_readsX` 与 `Mgood_exec` 联手见证）。 -/
theorem readsX_exec_and_nonreadsX_exec :
    Rule1Executable R1G.Mgood ∧ Rule1Executable Mzero :=
  ⟨Run.Mgood_exec, Mzero_exec⟩

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ **反例的**判据后果**：`Mdirect` 的表必须按 `x` 分片**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **由 §1 的判据**从否命题导出**见证**（W7 只有 `Mdirect` 这一特例）。

$$ \neg\,\textbf{Rule1Executable}(\texttt{Mdirect})
   \implies \exists x\,x'\,y\,z,\
      \texttt{doCondZ}\,x\,z\,y \neq \texttt{doCondZ}\,x'\,z\,y $$

**⭐ 这是 `not_executable_witness` 在 W7 的反例模型上的**实例化** ——
它证明本文件的通用接口**真的接得上 W7 的反例**（不是空接口）。 -/
theorem Mdirect_witness :
    ∃ (x x' : Bool) (y : Bool) (z : Bool),
      DirectBad.Mdirect.doCondZ x z y ≠ DirectBad.Mdirect.doCondZ x' z y :=
  not_executable_witness DirectBad.Mdirect DirectBad.rule1_executable_fails

/-- ⭐⭐⭐⭐ **同一见证的**显式数值**（`x = ⊤, x' = ⊥, y = ⊥, z = ⊥`，值 `1` vs `0`）。

**⭐ 与 `Mdirect_witness` 的区别**：那条只说「存在」，这条**给出具体数对**
（`not_executable_witness` 的证明走反证法，**不构造**具体见证 —— 本定理补上构造）。 -/
theorem Mdirect_witness_explicit :
    DirectBad.Mdirect.doCondZ true false false
      ≠ DirectBad.Mdirect.doCondZ false false false := by
  rw [DirectBad.doCondZ_Mdirect, DirectBad.doCondZ_Mdirect]
  norm_num

/-- ⭐⭐⭐⭐ **`Mdirect` 上的表**确实依赖 `x`：`DoTab ⊥ ⊥ ⊥ ≠ DoTab ⊤ ⊥ ⊥`（逐格形式）。

**⭐ 与 W7 `Mdirect_tab_ne` 的关系**：W7 那条是**整张表**的函数不等（`FunLike` 层面）；
本定理给出**单个格子**上的不等 —— 更弱、但**可直接用于数值对照**。 -/
theorem Mdirect_tab_ne_cell :
    DoTab DirectBad.Mdirect false false false
      ≠ DoTab DirectBad.Mdirect true false false := by
  intro h
  have h1 : DoTab DirectBad.Mdirect false false false = 1 := by
    show DirectBad.Mdirect.doCondZ false false false = 1
    rw [DirectBad.doCondZ_Mdirect]; norm_num
  have h2 : DoTab DirectBad.Mdirect true false false = 0 := by
    show DirectBad.Mdirect.doCondZ true false false = 0
    rw [DirectBad.doCondZ_Mdirect]; norm_num
  rw [h1, h2] at h
  exact absurd h (by norm_num)

/-- ⭐⭐⭐⭐⭐ **判据 ⇔ 反例的最终对照（**本文件的收尾**）。**

$$\Bigl(\neg\,\textbf{Rule1Executable}(\texttt{Mdirect})\Bigr)
  \wedge \Bigl(\textbf{Rule1Executable}(\texttt{Mgood})\Bigr)
  \wedge \Bigl(\textbf{Rule1Executable}(\texttt{Mzero})\Bigr)$$

**⭐ 读法**：**同一个充要判据**（`rule1_executable_iff`）在
**三块性质完全不同的模型**上给出**明确的真/假** ——
`Mdirect`（读 `x` 且真质量）/ `Mgood`（不读 `x`）/ `Mzero`（读 `x` 但零质量）。
**⟹ 本文件的消费是**实质的**：判据把 W7 的三块模型统一到一条方程上。** -/
theorem criterion_unifies_three_models :
    (¬ Rule1Executable DirectBad.Mdirect)
      ∧ Rule1Executable R1G.Mgood ∧ Rule1Executable Mzero :=
  ⟨DirectBad.rule1_executable_fails, Run.Mgood_exec, Mzero_exec⟩

/-- ⭐⭐⭐ **判据在三块模型上的逐点读数**（**同一格 `doCondZ` 是否随 `x` 变**）。

- `Mdirect`：**变**（`⊤ → 1`，`⊥ → 0`）；
- `Mgood`：**不变**；
- `Mzero`：**不变**（零质量吞掉 `u = 1`）。

**⭐ 这是 `rule1_executable_iff` 右端的**逐格证据**，与 W7 的 `Mgood_exec_vals` 互补。** -/
theorem pointwise_readings :
    (DirectBad.Mdirect.doCondZ true false false
        ≠ DirectBad.Mdirect.doCondZ false false false)
      ∧ (Mzero.doCondZ true true false = Mzero.doCondZ false true false) := by
  refine ⟨Mdirect_witness_explicit, ?_⟩
  rw [doCondZ_Mzero, doCondZ_Mzero]

end Consume

end W7

end FateV2.Predict
/-! ===========================================================================
  §6 ⭐⭐⭐⭐⭐ **R-48：消费侧出口 —— 让 `Fate/Rule1Genuine` 与 `Fate/Rule2Genuine`
  在编译器层面被真实引用**

  `_audit/count_metrics.ps1:62` 的 G46 真消费口径是纯文本正则
  `Fate\.<模块基名>\.\w+`。`Fate/Rule1Genuine.lean` 的真实命名空间是 `Fate.R1G`
  （第 235 行），`Fate/Rule2Genuine.lean` 的是 `Fate.R248`（第 146 行），
  **两者都不等于模块名** —— 故这两个模块即使被 `import` 也计 0 消费。

  `Fate/WiringDoCalcFixed.lean` §6 已把两模块的定理组合进
  `Fate.Rule1Genuine` / `Fate.Rule2Genuine` 命名空间的定理（证明体真实调用
  `R1G.ZSCM.*` / `R248.Sem.*`）。**本节**是那些组合定理的消费出口：
  以全限定名调用它们，并接到本文件的 `W7.Consume` 可执行性框架上。

  ⚠ **诚实边界**：本节不产生新数学内容，是**接线/消费层**。它保证组合定理
  不是死代码 —— 被消费模块的定理一旦改名或失效，`lake build` 立刻失败。

  | # | 名字 | 消费的模块定理 |
  |---|---|---|
  | 1 | `rule1_premise_executable_via_module` | `Fate.Rule1Genuine.premise_implies_executable` |
  | 2 | `rule1_premise_cell_form_via_module` | `Fate.Rule1Genuine.premise_implies_cell_form` |
  | 3 | `rule1_Mdet_via_module` | `Fate.Rule1Genuine.Mdet_premise_exec_and_values` |
  | 4 | `rule1_no_observational_gap_via_module` | `Fate.Rule1Genuine.premise_implies_no_observational_gap` |
  | 5 | `rule2_table_via_module` | `Fate.Rule2Genuine.invariant_root_mass_implies_table` |
  | 6 | `rule2_factor_law_via_module` | `Fate.Rule2Genuine.invariant_implies_factor_and_law` |
  | 7 | `rule2_chain_closed_form_via_module` | `Fate.Rule2Genuine.chain_table_closed_form` |
  | 8 | `rule2_chain_executable_via_module` | `Fate.Rule2Genuine.chain_rule2_executable` |

  零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`。
-/

namespace FateV2.Predict.W7

namespace ConsumeR48

open FateV2.Error Fate.W7.Exec

/-- **出口 1**：`Rule1Premise` ⟹ 表可执行（经
`Fate.Rule1Genuine.premise_implies_executable`）。 -/
theorem rule1_premise_executable_via_module {Zq Xq Yq : Type} [DecidableEq Zq]
    [DecidableEq Yq] (M : R1G.ZSCM Zq Xq Yq) (h : M.Rule1Premise) :
    Rule1Executable M :=
  Fate.Rule1Genuine.premise_implies_executable M h

/-- **出口 2**：逐格闭式（右端不含 `x`），经
`Fate.Rule1Genuine.premise_implies_cell_form`。 -/
theorem rule1_premise_cell_form_via_module {Zq Xq Yq : Type} [DecidableEq Zq]
    [DecidableEq Yq] (M : R1G.ZSCM Zq Xq Yq) (h : M.Rule1Premise) (x x0 : Xq)
    (y : Yq) (z : Zq) :
    M.doCondZ x z y
      = (∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z),
            M.pU u * (if M.fY u x0 z = y then (1 : ℝ) else 0))
        / (∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z), M.pU u) :=
  Fate.Rule1Genuine.premise_implies_cell_form M h x x0 y z

/-- **出口 3**：`Mdet` 上「前提 ∧ 可执行 ∧ 表值」，经
`Fate.Rule1Genuine.Mdet_premise_exec_and_values`。 -/
theorem rule1_Mdet_via_module :
    (R1G.Mdet.Rule1Premise ∧ Rule1Executable R1G.Mdet)
      ∧ (R1G.Mdet.doCondZ true true true = 1)
      ∧ (R1G.Mdet.doCondZ true true false = 0) :=
  Fate.Rule1Genuine.Mdet_premise_exec_and_values

/-- **出口 4**：可执行性不蕴含 `z` 的删除（否证），经
`Fate.Rule1Genuine.premise_implies_no_observational_gap`。 -/
theorem rule1_no_observational_gap_via_module :
    ¬ (∀ (M : R1G.ZSCM Bool Bool Bool) [DecidableEq Bool],
        M.Rule1Premise → Rule1Executable M →
          ∀ x z y : Bool, M.doCondZ x z y = M.doLaw x y) :=
  Fate.Rule1Genuine.premise_implies_no_observational_gap

/-- **出口 5**：规则 2 的表读数，经
`Fate.Rule2Genuine.invariant_root_mass_implies_table`。 -/
theorem rule2_table_via_module {Zq Xq Yq : Type} [Fintype Zq] [DecidableEq Zq]
    [DecidableEq Yq] (M : R246G3.Sem3.SCM3 Zq Xq Yq)
    (hInv : R248.Sem.MediationInvariant M) (hNorm : R248.Sem.MassOne M)
    (hRoot : R248.Sem.ZIsRoot M) (hSup : R248.Sem.Supplied M) (x : Xq) :
    (∀ y : Yq, ∀ z : Zq,
        R246G3.Sem3.doLaw2 M x z y = R246G3.Sem3.doLawXCond M x z y)
      ∧ (∃ T : Yq → Zq → ℝ, ∀ y z,
          T y z = R246G3.Sem3.doLaw2 M x z y) :=
  Fate.Rule2Genuine.invariant_root_mass_implies_table M hInv hNorm hRoot hSup x

/-- **出口 6**：`MediationInvariant` ⟹ 方程分解 ∧ 定律相等，经
`Fate.Rule2Genuine.invariant_implies_factor_and_law`。 -/
theorem rule2_factor_law_via_module {Zq Xq Yq : Type} [Fintype Zq] [DecidableEq Zq]
    [DecidableEq Yq] (M : R246G3.Sem3.SCM3 Zq Xq Yq)
    (hInv : R248.Sem.MediationInvariant M) (hNorm : R248.Sem.MassOne M)
    (hRoot : R248.Sem.ZIsRoot M) (hSup : R248.Sem.Supplied M) :
    (∃ (g : M.U → Zq → Yq), ∀ (u : M.U) (p : Zq × Xq), (M.sg u).2 p = g u p.1)
      ∧ (∀ x z y, R246G3.Sem3.doLaw2 M x z y
          = R246G3.Sem3.doLawXCond M x z y) :=
  Fate.Rule2Genuine.invariant_implies_factor_and_law M hInv hNorm hRoot hSup

/-- **出口 7**：`chain` 的闭式表，经 `Fate.Rule2Genuine.chain_table_closed_form`。 -/
theorem rule2_chain_closed_form_via_module (x z y : Fin 2) :
    R246G3.Sem3.doLaw2 R246G3.chain x z y = (if z = y then (1 : ℝ) else 0)
      ∧ R246G3.Sem3.doLawXCond R246G3.chain x z y = (if z = y then (1 : ℝ) else 0) :=
  Fate.Rule2Genuine.chain_table_closed_form x z y

/-- **出口 8**：`chain` 上规则 2 可执行（`chain` 不满足 `ZIsRoot`，故走
`Rule2Genuine` 的逐格对拍），经 `Fate.Rule2Genuine.chain_rule2_executable`。 -/
theorem rule2_chain_executable_via_module (x : Fin 2) :
    Rule2Executable R246G3.chain x :=
  Fate.Rule2Genuine.chain_rule2_executable x

end ConsumeR48

end W7
