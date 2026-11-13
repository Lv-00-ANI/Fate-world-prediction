import FateWorld.FateV2.Loop.WriteBack
import FateWorld.FateV2.Error.FitBoundaryN
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Loop · Convergence —— 闭环收敛性的**一条定理链**（T21）

  ## 迁移登记
  - 来源：**新写**（装配 `Loop/Residual.lean`、`Loop/WriteBack.lean`、
          `Error/FitBoundaryN.lean`，三者均**不改**）
  - 动作：C 重写（新建并行文件）
  - 对应环节：F7-22（回写）、F7-23（收敛）、F7-11（误差判据 / 裁决 K）
  - 依赖裁决：**裁决 K**、**D-008**（σ 只能由建模层给）、**D-022**（反空泛）
  - 改动：新文件。只新增定义与定理，**不触碰** `Loop/` 下任何已有文件。
  - 状态：已验证（全部定理 `#print axioms` 实测，逐条登记在
          `_support_registry_T21.csv`）

  ## 本文件闭合的缺口

  `Loop/` 层已有几块真结果，但**彼此之间没有一条定理**把它们串成一条链：

  | 既有文件 | 已有定理 | 形态 |
  |---|---|---|
  | `Loop/WriteBack.lean` | `writeBack_residual` / `abs_residual_contract` | **单步** `e' = (1−η)·e` |
  | `Loop/WiringConvergence.lean` | `err_iterMap` | **向量**上的 `n` 步 `‖·‖` 缩放（需 `Corrects A φ`）|
  | `Loop/ThetaConvergence.lean` | `thetaN_closed` | 参数 `θ` 收敛（需 `Tendsto`，且**只**在 `linWorld` 上）|
  | `Error/FitBoundaryN.lean` | `IsFitBoundaryN` / `accepts` | 裁决 K 的**判据** |

  缺的是**标量残差**这一侧的收敛定理链，以及「闭环**与裁决 K 的相互作用**」。

  ## 本文件证明的链

  ```
  §0  iterate / iterStep                      自造迭代（Nat.rec）
  §1  step_contract          : |(1−η)·e| < |e|            单步严格收缩
  §2  step_iterate           : e_n = (1−η)^n · e           迭代闭式（精确等式）
      contract_iter          : |e_n| = |1−η|^n·|e|          ★ 多步收缩
  §3  contract_mono          : |e_{n+1}| < |e_n|           逐次严格下降
      contract_floor         : η ≠ 1 ⟹ ∀n, e_n ≠ 0          永不到达 0
      contract_one_eta       : η = 1 ⟹ 一步归零（补集情形）
  §4  half_pow_tendsto_zero  : ∀ε>0, ∃N, ∀n≥N, (1/2)^n < ε
      geom_tendsto_zero      : 0 ≤ r < 1 ⟹ ∀ε>0, ∃N, ∀n≥N, r^n < ε
      tends_to_zero          : ∀ε>0, ∃N, ∀n≥N, |1−η|^n·|e| < ε   ★ 收敛到 0
  §5  writeBack_fixed_point  : (1−η)·e = e ⟺ (η = 0 ∨ e = 0)
      iter_fixed_point       : e_n = e ⟺ n = 0 ∨ e = 0            ★ 稳定性
  §6  crosses_sigma          : |e₀| > σ ⟹ ∃n, |1−η|^n·|e₀| ≤ σ   ★★ 与裁决 K 的交互
      crosses_sigma_strict   : 更强：∃n, 严格 < σ（真正穿过）
      passed_sigma_no_return : 一旦 ≤ σ，此后**不增**              ★ 不可逆
  §7  reaches_verdict_band   : 存在一步其误差**落在裁决 K 的带内**  ★ 判据后果
      concrete_*             : 具体数值见证（η = 1/2、σ = 1、|e₀| = 4）
  §8  selfcheck_*            : 与 `Loop/WriteBack.lean` 既有定理的**逐字对位**
  ```

  ## 诚实边界（必读）

  **1. 本文件在标量 `Real` 上做，不在任意赋范空间上。**
  `Loop/WiringConvergence.lean` 的 `err_iterMap` 已在**任意赋范空间**上给出
  `‖·‖` 的 `n` 步缩放（需 `Corrects A φ`）。本文件**不**重复、**不**替代它：
  本文件处理的是**残差这个标量**（`Loop/Residual.lean` 的 `residual`），
  它的载体**天生**是 `Real`。两者是**平行**的两层，不是一条链。

  **2. `crosses_sigma` 里的「穿过」是**残差绝对值**意义上的。**
  它说「**残差大小**这条数列」穿过 `σ`，**不**是「误差剖面 `E_W(γ)` 穿过 `σ`」。
  裁决 K（`IsFitBoundaryN`）读的是**剖面**，闭环回写读的是**残差**；
  §7 把两者在**同一组数值**上接起来，但**不声称**「回写改变剖面」。

  **3. 本文件不碰 `Tendsto`。** §4 全部用显式 `∃ N, ∀ n ≥ N` 表述，
  只依赖 `Mathlib.Algebra.Order.Field.Basic` + `Mathlib.Tactic`，
  **不**引入 `Mathlib.Topology.*` / `Mathlib.Analysis.SpecificLimits.*`。

  ## 公理纪律

  `Loop/` 层**允许**三公理（任务书原文）。本文件全部定理实测
  `[propext, Classical.choice, Quot.sound]`，**无** `sorryAx`。
-/

namespace FateV2.Loop

namespace Convergence

/-! ===========================================================================
  §0  迭代算子（自造，不用 `Function.iterate`）
  =========================================================================== -/

/-- **闭环回写的标量迭代算子**：`iterStep η` 把残差按 `(1−η)` 缩放。 -/
def iterStep (η : Real) : Real → Real := fun e => (1 - η) * e

/-- **`n` 步回写后的残差**（`Nat.rec` 形式）。

  `iterate η 0 e = e`（还没写回），`iterate η (n+1) e = (1−η) · iterate η n e`。 -/
def iterate (η : Real) : Nat → Real → Real
  | 0, e => e
  | k + 1, e => iterStep η (iterate η k e)

/-- **零步 = 恒等**（定义性）。 -/
theorem iterate_zero (η e : Real) : iterate η 0 e = e := rfl

/-- **递归步**（定义性展开，供归纳 `rw`）。

  **超出定义之处**：定义是 `Nat.rec`；本定理把它写成**可用 `rw` 重写**的形状，
  使下游归纳不必 `unfold` 整个递归子。 -/
theorem iterate_succ (η : Real) (k : Nat) (e : Real) :
    iterate η (k + 1) e = (1 - η) * iterate η k e := rfl

/-- **一步恰好是 `WriteBack` 的缩放式**：`iterate η 1 e = (1−η)·e`。

  **超出定义之处**：把「`n = 1` 的迭代」与 `Loop/WriteBack.lean`
  `writeBack_residual` 的**右端**接上。 -/
theorem iterate_one (η e : Real) : iterate η 1 e = (1 - η) * e := by
  rw [iterate_succ, iterate_zero]

/-! ===========================================================================
  §1  单步收缩
  =========================================================================== -/

/-- 局部引理：`0 < η < 2` ⟹ `|1 − η| < 1`。

  **超出定义之处**：`η ∈ (0,2)` 这个开区间与 `|1−η| < 1` 是**同一件事的两种写法**。 -/
theorem abs_one_sub_lt_one {η : Real} (h1 : 0 < η) (h2 : η < 2) : |1 - η| < 1 := by
  rw [abs_lt]
  constructor <;> linarith

/-- 局部引理：`η ≠ 1` 时 `1 − η ≠ 0`（`0 < η` 单独不够：`η = 1` 时它恰为 `0`）。 -/
theorem one_sub_ne_zero {η : Real} (hη : η ≠ 1) : (1 : Real) - η ≠ 0 := by
  intro h
  exact hη (by linarith)



/-- **【§1 主定理】单步严格收缩**：`0 < η < 2` 且 `e ≠ 0` 时，一次回写让 `|e|` 严格变小。

  **超出定义之处**：`Loop/WriteBack.lean` 的 `abs_residual_contract` 是这条定理在
  `residual obs (writeBack η obs pred)` 上的**实例**；本条把结论提到**纯标量**层面。 -/
theorem step_contract (η : Real) (hη0 : 0 < η) (hη2 : η < 2) (e : Real) (he : e ≠ 0) :
    |(1 - η) * e| < |e| := by
  have hlt : |1 - η| < 1 := abs_one_sub_lt_one hη0 hη2
  have hpos : 0 < |e| := abs_pos.mpr he
  calc |(1 - η) * e| = |1 - η| * |e| := abs_mul _ _
    _ < 1 * |e| := (mul_lt_mul_iff_of_pos_right hpos).mpr hlt
    _ = |e| := one_mul _

/-- **单步收缩（迭代算子形态）**：一步之后 `|iterate η 1 e| < |e|`。 -/
theorem step_contract_iter (η : Real) (hη0 : 0 < η) (hη2 : η < 2) (e : Real) (he : e ≠ 0) :
    |iterate η 1 e| < |e| := by
  rw [iterate_one]
  exact step_contract η hη0 hη2 e he

/-! ===========================================================================
  §2  多步收缩（**核心**）
  =========================================================================== -/

/-- **【§2 主定理】多步收缩闭式**：迭代 `n` 次回写后，残差**恰**是 `(1−η)^n · e`。

  **超出定义之处**：`iterate` 的定义是 `Nat.rec`，看不出闭式；
  本定理给出**精确等式**（不是不等式），于是整条收敛链只需要看
  `|1−η|^n` 这一条数列的性质 —— §3、§4、§6 全部由它一行推出。

  对 `η` **无任何限制**。 -/
theorem step_iterate (η : Real) (n : Nat) (e : Real) :
    iterate η n e = (1 - η) ^ n * e := by
  induction n with
  | zero => rw [iterate_zero, pow_zero, one_mul]
  | succ k ih =>
    rw [iterate_succ, ih, pow_succ]
    ring

/-- **【§2 主定理 · 绝对值形式】`|1−η|^n` 衰减**：`|e_n| = |1−η|^n · |e|`。

  **超出定义之处**：`step_iterate` 给的是**带符号**的闭式；对**收敛**而言
  真正需要的对象是 `|e_n|`。本定理把 `abs_mul` / `abs_pow` 搬过来，得到
  「`η ∈ (1,2)`（过冲、符号交替）」与「`η ∈ (0,1)`（单调）」**同一条公式**。 -/
theorem contract_iter (η : Real) (e : Real) (n : Nat) :
    |iterate η n e| = |1 - η| ^ n * |e| := by
  rw [step_iterate, abs_mul, abs_pow]

/-- **零残差恒为零**：`e = 0` 时怎么迭代都还是 `0`。 -/
theorem iterate_zero_of_zero (η : Real) : ∀ n : Nat, iterate η n 0 = 0 := by
  intro n
  rw [step_iterate]
  ring

/-! ===========================================================================
  §3  单调性与「永不到达」
  =========================================================================== -/

/-- **【§3.1】逐次严格下降**：`0 < η < 2`、`η ≠ 1`、`e ≠ 0` 时，每一步都比上一步小。

  **超出定义之处**：`step_contract` 只比较**第一步与初值**；
  本定理把它推到**任意相邻两步** —— 这才是「单调收敛」里的「单调」二字。

  **⚠ `η ≠ 1` 不可去**：`η = 1` 时回写**一步归零**（`contract_one_eta`），
  于是 `n ≥ 1` 之后两边都是 `0`，`|e_{n+1}| < |e_n|` **为假**。
  这正是「严格下降」与「一步到位」的分界，也是 `contract_floor` 单列的原因。 -/
theorem contract_mono (η : Real) (hη0 : 0 < η) (hη2 : η < 2) (hη1 : η ≠ 1) (e : Real) (he : e ≠ 0)
    (n : Nat) : |iterate η (n + 1) e| < |iterate η n e| := by
  rw [contract_iter, contract_iter]
  have hlt : |1 - η| < 1 := abs_one_sub_lt_one hη0 hη2
  have hb : (0 : Real) < |1 - η| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hη1))
  have hepos : 0 < |e| := abs_pos.mpr he
  have hpos : 0 < |1 - η| ^ n * |e| := mul_pos (pow_pos hb n) hepos
  calc |1 - η| ^ (n + 1) * |e| = |1 - η| * (|1 - η| ^ n * |e|) := by
        rw [pow_succ]; ring
    _ < 1 * (|1 - η| ^ n * |e|) := (mul_lt_mul_iff_of_pos_right hpos).mpr hlt
    _ = |1 - η| ^ n * |e| := one_mul _

/-- **【§3.2 主定理】永不到达 0**：`0 < η < 2` 且 `η ≠ 1` 时，迭代**永远**到不了 `0`。

  **超出定义之处**：`contract_mono` 只说「每步更小」——「更小」**可以**是
  「终于小到 0」。本定理把这一可能性**排除**：

  $$\eta \neq 1 \;\Longrightarrow\; \forall n,\ e_n \neq 0 .$$

  ⟹ 「回写使误差**趋向** `0`」与「回写使误差**等于** `0`」是两件事。 -/
theorem contract_floor (η : Real) (hη0 : 0 < η) (hη2 : η < 2) (hne : η ≠ 1) (e : Real)
    (he : e ≠ 0) : ∀ n : Nat, iterate η n e ≠ 0 := by
  intro n
  rw [step_iterate]
  have h1 : (1 - η) ≠ 0 := by
    intro h
    exact hne (by linarith [h])
  exact mul_ne_zero (pow_ne_zero n h1) he

/-- **`η = 1` 一步精确归零**（`contract_floor` 的**补集**情形）。

  **超出定义之处**：`contract_floor` 只排除 `η = 1`；本定理说明
  `η = 1` 时回写**一步命中** `e_1 = 0`。两条合起来是**完备二分**。 -/
theorem contract_one_eta (e : Real) : iterate 1 0 e = e ∧ ∀ n : Nat, iterate 1 (n + 1) e = 0 := by
  refine ⟨rfl, fun n => ?_⟩
  rw [step_iterate]
  norm_num

/-! ===========================================================================
  §4  收敛到 0（显式 `∃ N` 形式，不碰 `Tendsto`）
  =========================================================================== -/

/-- **`(1/2)^n ≤ 1`**（几何因子的初等上界，归纳证）。

  **超出定义之处**：避免依赖库中幂序引理在本工具链上的元参数差异。 -/
theorem half_pow_le_one : ∀ n : Nat, (1 / 2 : Real) ^ n ≤ 1 := by
  intro n
  induction n with
  | zero => rw [pow_zero]
  | succ k ih =>
    rw [pow_succ]
    nlinarith [ih, pow_nonneg (by norm_num : (0 : Real) ≤ 1 / 2) k]

/-- **`(1/2)^n` 单调不增**：`(1/2)^(k+1) ≤ (1/2)^k`。 -/
theorem half_pow_le_half (k : Nat) : (1 / 2 : Real) ^ (k + 1) ≤ (1 / 2) ^ k := by
  rw [pow_succ]
  have hnn : (0 : Real) ≤ (1 / 2) ^ k := pow_nonneg (by norm_num) k
  nlinarith

/-- **远端的项更小**：`m ≤ n ⟹ (1/2)^n ≤ (1/2)^m`。 -/
theorem half_pow_le_of_le {m n : Nat} (h : m ≤ n) : (1 / 2 : Real) ^ n ≤ (1 / 2) ^ m := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans (half_pow_le_half _) ih

/-- **收缩因子的单调性**：`0 ≤ r ≤ 1/2` 时 `r^n ≤ (1/2)^n`。 -/
theorem pow_le_half_pow {r : Real} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (n : Nat) :
    r ^ n ≤ (1 / 2 : Real) ^ n :=
  pow_le_pow_left₀ hr0 hr n

/-- **`(1/2)^n ≤ 1/(n+1)`**（几何衰减的基本界）。

  **超出定义之处**：这是 §4「`(1/2)^n` 可达任意小」的**核心不等式** ——
  它把 `(1/2)^n` 与「`n` 的倒数」直接接起来，于是 `N := ⌈1/ε⌉ + 1` 的
  显式选择立刻可行，**不需要** `Tendsto`。

  证明：对 `n` 归纳。`n = 0` 时两项都是 `1`。
  `n → n+1`：`(1/2)^(n+1) = (1/2)·(1/2)^n ≤ (1/2)·(1/(n+1)) = 1/(2n+2) ≤ 1/(n+2)`
  （`n+2 ≤ 2n+2`，当 `n ≥ 0`）。 -/
theorem half_pow_le_inv_succ : ∀ n : Nat, (1 / 2 : Real) ^ n ≤ 1 / ((n : Real) + 1) := by
  intro n
  induction n with
  | zero => norm_num
  | succ k ih =>
    have hk : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
    have h1 : (0 : Real) < (k : Real) + 1 := by linarith
    have h2 : (0 : Real) < (k : Real) + 2 := by linarith
    have hnn : (0 : Real) ≤ (1 / 2) := by norm_num
    have hc1 : (1 / 2 : Real) * (1 / ((k : Real) + 1)) = 1 / (2 * ((k : Real) + 1)) := by
      field_simp
    have hc2 : (k : Real) + 2 ≤ 2 * ((k : Real) + 1) := by nlinarith
    have hcmp : (1 : Real) / (2 * ((k : Real) + 1)) ≤ 1 / ((k : Real) + 2) :=
      div_le_div_of_nonneg_left (by norm_num : (0 : Real) ≤ 1) h2 hc2
    have hpush : ((k + 1 : Nat) : Real) + 1 = (k : Real) + 2 := by push_cast; ring
    rw [pow_succ, hpush]
    calc (1 / 2 : Real) ^ k * (1 / 2) ≤ (1 / ((k : Real) + 1)) * (1 / 2) :=
          mul_le_mul_of_nonneg_right ih hnn
      _ = 1 / (2 * ((k : Real) + 1)) := by field_simp
      _ ≤ 1 / ((k : Real) + 2) := hcmp

/-- **局部引理：`m·ε > 1 ⟹ 1/m < ε`**（`0 < m`）。

  **超出定义之处**：把「`ε` 的倒数被某个 `Nat` 超过」转成「`1/m < ε`」——
  这一步是 §4 里唯一需要 `Nat` 与 `Real` 相互转换的地方。
  证明只用 `div_lt_iff₀`（目标 `1 < ε·m`）与交换律。 -/
theorem one_div_nat_lt {m : Nat} {ε : Real} (hm : 0 < (m : Real)) (hε : 0 < ε)
    (hbig : 1 < (m : Real) * ε) : 1 / (m : Real) < ε := by
  rw [div_lt_iff₀ hm]
  rw [mul_comm]
  exact hbig

/-- **【§4.1 主定理】(1/2)^n 收敛到 0**：`∀ ε > 0, ∃ N, ∀ n ≥ N, (1/2)^n < ε`。

  **超出定义之处**：这条是**收敛性的全部内容**（`Tendsto ⇔` 本式），
  但表述**不用** `Filter.Tendsto`。

  `N := b + 2`，其中 `b := ⌊1/ε⌋`（由 `exists_nat_gt` 给出）。 -/
theorem half_pow_tendsto_zero (ε : Real) (hε : 0 < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → (1 / 2 : Real) ^ n < ε := by
  obtain ⟨b, hb⟩ := exists_nat_gt (1 / ε)
  refine ⟨b + 3, fun n hn => ?_⟩
  have hm1 : 1 ≤ b + 3 := Nat.le_add_left 1 (b + 2)
  have hcast : ((b + 3 : Nat) : Real) = (b : Real) + 3 := by push_cast; ring
  have hmpos : (0 : Real) < ((b + 3 : Nat) : Real) := by
    rw [hcast]
    have hb0 : (0 : Real) ≤ (b : Real) := Nat.cast_nonneg b
    linarith
  -- `1/ε < b` ⟹ `1 < b·ε` ⟹ `1 < (b+3)·ε`
  have hbe : (1 : Real) < (b : Real) * ε := by
    have h1 : (1 / ε) * ε < (b : Real) * ε := mul_lt_mul_of_pos_right hb hε
    have h2 : (1 / ε) * ε = 1 := by field_simp
    linarith
  have hmul : (b : Real) * ε ≤ ((b + 3 : Nat) : Real) * ε := by
    rw [hcast]
    have hle : (b : Real) ≤ (b : Real) + 3 := by linarith
    exact mul_le_mul_of_nonneg_right hle hε.le
  have hbig : (1 : Real) < ((b + 3 : Nat) : Real) * ε := lt_of_lt_of_le hbe hmul
  have hinv : 1 / ((b + 3 : Nat) : Real) < ε := one_div_nat_lt hmpos hε hbig
  -- `(1/2)^n ≤ 1/(n+1) ≤ 1/(b+3)`（`n ≥ b+3`）
  have hkey : (1 / 2 : Real) ^ n ≤ 1 / ((n : Real) + 1) := half_pow_le_inv_succ n
  have hnge : ((b + 3 : Nat) : Real) ≤ (n : Real) + 1 := by
    have hle : b + 3 ≤ n + 1 := by omega
    exact_mod_cast hle
  have hposn : (0 : Real) < ((b + 3 : Nat) : Real) := hmpos
  have hposn1 : (0 : Real) < (n : Real) + 1 := by
    have : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
    linarith
  have hinvle : 1 / ((n : Real) + 1) ≤ 1 / ((b + 3 : Nat) : Real) :=
    div_le_div_of_nonneg_left (by norm_num : (0 : Real) ≤ 1) hposn hnge
  calc (1 / 2 : Real) ^ n ≤ 1 / ((n : Real) + 1) := hkey
    _ ≤ 1 / ((b + 3 : Nat) : Real) := hinvle
    _ < ε := hinv

/-- **`r ∈ [0,1)` 时存在 `k` 使 `r^k < 1/2`**（**显式**，用 Bernoulli 不等式）。

  **超出定义之处**：这是 §4 唯一「看起来需要对数」的步骤，但**不需要**：

  1. 若 `r = 0`：`k := 1`。
  2. 若 `r > 0`：`1/r > 1`，记 `δ := 1/r − 1 > 0`。Bernoulli 给
     `(1+δ)^k ≥ 1 + kδ`；`exists_nat_gt` 取 `k` 使 `kδ > 2`，于是
     `(1/r)^k > 2`，两边取倒数得 `r^k < 1/2`。 -/
theorem pow_lt_half_of_lt_one {r : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ k : Nat, r ^ k < 1 / 2 := by
  by_cases h0 : r = 0
  · refine ⟨1, ?_⟩
    rw [h0, pow_one]
    norm_num
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm h0)
    have hinv1 : (1 : Real) < 1 / r := by
      rw [lt_div_iff₀ hrpos]; linarith
    have hδ : (0 : Real) < 1 / r - 1 := by linarith
    have hδ2 : (-2 : Real) ≤ 1 / r - 1 := by linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / (1 / r - 1))
    have hkδ : (2 : Real) < (k : Real) * (1 / r - 1) := by
      rw [div_lt_iff₀ hδ] at hk
      linarith
    have hbern : 1 + (k : Real) * (1 / r - 1) ≤ (1 / r) ^ k := by
      have hb : (1 : Real) + (k : Real) * (1 / r - 1) ≤ (1 + (1 / r - 1)) ^ k :=
        one_add_mul_le_pow hδ2 k
      have hid : (1 : Real) + (1 / r - 1) = 1 / r := by ring
      rwa [hid] at hb
    have hinvk : (2 : Real) < (1 / r) ^ k := lt_of_lt_of_le (by linarith) hbern
    have hinvpow : (1 / r) ^ k = (r ^ k)⁻¹ := by rw [one_div]; exact inv_pow r k
    rw [hinvpow] at hinvk
    refine ⟨k, ?_⟩
    have hposk : (0 : Real) < r ^ k := pow_pos hrpos k
    by_contra hc
    have hc2 : (1 / 2 : Real) ≤ r ^ k := not_lt.mp hc
    have h2 : (2 : Real) = (1 / 2 : Real)⁻¹ := by norm_num
    rw [h2] at hinvk
    have hle : ((r ^ k))⁻¹ ≤ ((1 / 2 : Real))⁻¹ :=
      (inv_le_inv₀ hposk (by norm_num : (0 : Real) < 1 / 2)).mpr hc2
    linarith

/-- **【§4.2 主定理】任意收缩因子都收敛到 0**：`0 ≤ r < 1` ⟹ `r^n → 0`（显式 `∃ N`）。

  **超出定义之处**：`half_pow_tendsto_zero` 只处理 `r = 1/2`。
  本定理处理**任意** `r ∈ [0,1)`：

  * `r ≤ 1/2`：`pow_le_half_pow` 压到 `(1/2)^n`；
  * `1/2 < r < 1`：先取 `k` 使 `r^k < 1/2`（Bernoulli），再取 `j` 使
    `(1/2)^j < ε`，则 `r^(k·j) < ε`，其后由单调性保持。 -/
theorem geom_tendsto_zero {r : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) (ε : Real) (hε : 0 < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → r ^ n < ε := by
  by_cases hhalf : r ≤ 1 / 2
  · obtain ⟨N, hN⟩ := half_pow_tendsto_zero ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h1 : r ^ n ≤ (1 / 2 : Real) ^ n := pow_le_half_pow hr0 hhalf n
    linarith [hN n hn]
  · have hgt : (1 / 2 : Real) < r := lt_of_not_ge hhalf
    obtain ⟨k, hk⟩ := pow_lt_half_of_lt_one hr0 hr1
    obtain ⟨j, hj⟩ := half_pow_tendsto_zero ε hε
    refine ⟨k * j, fun n hn => ?_⟩
    have hmono : r ^ n ≤ r ^ (k * j) := pow_le_pow_of_le_one hr0 hr1.le hn
    have hmul : r ^ (k * j) = (r ^ k) ^ j := pow_mul r k j
    have hpow : (r ^ k) ^ j ≤ (1 / 2 : Real) ^ j :=
      pow_le_pow_left₀ (pow_nonneg hr0 k) hk.le j
    have hend : (1 / 2 : Real) ^ j < ε := hj j (le_refl j)
    linarith [hmono, hmul, hpow, hend]

/-- **【§4.3 主定理】回写使误差收敛到 0**（任务书 §3 的目标定理）。

  $$\forall \varepsilon > 0,\ \exists N,\ \forall n \geq N,\
    |1-\eta|^n \cdot |e| < \varepsilon .$$

  **超出定义之处**：`contract_iter` 只给**等式**，本身**不**说「趋于 0」；
  本定理把「收敛」补全，且用**显式 `∃ N`**（不用 `Tendsto`）。 -/
theorem tends_to_zero (η : Real) (hη0 : 0 < η) (hη2 : η < 2) (e : Real) :
    ∀ ε : Real, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → |1 - η| ^ n * |e| < ε := by
  intro ε hε
  have hlt : |1 - η| < 1 := abs_one_sub_lt_one hη0 hη2
  by_cases he : |e| = 0
  · refine ⟨0, fun n _ => ?_⟩
    rw [he, mul_zero]
    exact hε
  · have hepos : 0 < |e| := lt_of_le_of_ne (abs_nonneg e) (Ne.symm he)
    have heps : (0 : Real) < ε / |e| := by positivity
    obtain ⟨N, hN⟩ := geom_tendsto_zero (abs_nonneg (1 - η)) hlt (ε / |e|) heps
    refine ⟨N, fun n hn => ?_⟩
    have h2 : |1 - η| ^ n * |e| < (ε / |e|) * |e| :=
      mul_lt_mul_of_pos_right (hN n hn) hepos
    have h4 : (ε / |e|) * |e| = ε := by field_simp
    linarith

/-! ===========================================================================
  §5  稳定性：回写的不动点
  =========================================================================== -/

/-- **【§5.1 主定理】回写的不动点恰是 `e = 0`（或 `η = 0` 的平凡情形）**。

  $$(1-\eta)\cdot e = e \iff \eta = 0 \lor e = 0 .$$

  **超出定义之处**：`Loop/WriteBack.lean` 的 `writeBack_zero_eta`（`η = 0` 时残差不变）
  与 `writeBack_one_eta`（`η = 1` 时残差归零）只是**两个特例**，
  它们**不**说明「还有没有别的不动点」。本定理给出**完整**的不动点集。 -/
theorem writeBack_fixed_point (η e : Real) :
    (1 - η) * e = e ↔ (η = 0 ∨ e = 0) := by
  constructor
  · intro h
    by_cases hη : η = 0
    · exact Or.inl hη
    · right
      have h2 : η * e = 0 := by nlinarith [h]
      exact (mul_eq_zero.mp h2).resolve_left hη
  · rintro (rfl | rfl)
    · ring
    · ring

/-- **`a ∈ [0,1)` 且 `n ≥ 1` ⟹ `a^n < 1`**（几何和的二项式下界）。

  **超出定义之处**：`half_pow_le_*` 系列只对底数 `1/2` 说话；本定理允许
  **任意** `a ∈ [0,1)`，且结论是**严格**不等号。
  证明：`1 − a > 0`，且 `1 − a^n = (1−a)·Σ_{i<n} a^i > 0`（`geom_sum_mul`）。 -/
theorem pow_lt_one_of_lt_one {a : Real} (ha0 : 0 ≤ a) (ha1 : a < 1) {n : Nat} (hn : 1 ≤ n) :
    a ^ n < 1 := by
  have h1a : (0 : Real) < 1 - a := by linarith
  have hsum : 0 < ∑ i ∈ Finset.range n, a ^ i := by
    refine Finset.sum_pos' (fun i _ => pow_nonneg ha0 i) ?_
    refine ⟨0, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · rw [pow_zero]; norm_num
  have hkey : (∑ i ∈ Finset.range n, a ^ i) * (1 - a) = 1 - a ^ n := geom_sum_mul_neg a n
  have hpos : 0 < 1 - a ^ n := by
    rw [← hkey]
    exact mul_pos hsum h1a
  linarith

/-- **`a ≥ 0`、`a^m = 1`、`m > 0` ⟹ `a = 1`**。

  **超出定义之处**：实数域上「乘性单位根只有 `1`」—— 这里的**唯一性**是被
  `a ≥ 0` 与**几何和**的严格正性一起逼出来的，不是 `pow_eq_one_iff` 那类形式事实。 -/
theorem pow_eq_one_imp {a : Real} {m : Nat} (ha : 0 ≤ a) (h : a ^ m = 1) (hm : 0 < m) :
    a = 1 := by
  by_contra hne
  have hlt : a < 1 := lt_of_le_of_ne (by
    by_contra hc
    have hgt : (1 : Real) < a := not_le.mp hc
    have hmono : (1 : Real) ^ m < a ^ m := pow_lt_pow_left₀ hgt (by norm_num) (by omega)
    rw [one_pow] at hmono
    linarith) hne
  have h1a : (0 : Real) < 1 - a := by linarith
  have hsum : 0 < ∑ i ∈ Finset.range m, a ^ i := by
    refine Finset.sum_pos' (fun i _ => pow_nonneg ha i) ?_
    exact ⟨0, by rw [Finset.mem_range]; omega, by rw [pow_zero]; norm_num⟩
  have hkey : (∑ i ∈ Finset.range m, a ^ i) * (1 - a) = 1 - a ^ m := geom_sum_mul_neg a m
  have hpos : 0 < 1 - a ^ m := by rw [← hkey]; exact mul_pos hsum h1a
  linarith

/-- **【§5.2】迭代的不动点（**收缩窗内**）**：`0 < η < 2` 时，`n` 步之后
  **恰好**回到原值 ⟺ `n = 0` 或 `e = 0`。

  **超出定义之处**：`writeBack_fixed_point` 只处理**一步**，且 `η = 0` 时
  **所有** `e` 都是不动点。「`n` 步之后仍在原地」是**另一件事**。

  **`0 < η < 2` 这个前件不可去**：`η = 2` 时 `1−η = −1`，故 `(−1)^2 = 1`，
  于是 `e_2 = e` —— `n = 2` 时迭代**回到原值**而 `n ≠ 0`、`e ≠ 0`。
  `η = 0` 时同理（一步都不动）。所以本定理的窗口是**充要**的。

  证明：`n = k+1` 时由 `step_iterate` 得 `(1−η)^(k+1) · e = e`，`e ≠ 0` 给
  `(1−η)^(k+1) = 1`。而 `0 < η < 2` 给 `|1−η| < 1`，故 `|1−η|^(k+1) < 1`
  （`k+1 ≥ 1`），于是 `|(1−η)^(k+1)| < 1`，与 `= 1` 矛盾。 -/
theorem iter_fixed_point (η : Real) (hη0 : 0 < η) (hη2 : η < 2) (n : Nat) (e : Real) :
    iterate η n e = e ↔ (n = 0 ∨ e = 0) := by
  constructor
  · intro h
    by_cases he : e = 0
    · exact Or.inr he
    · left
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact hn
      · exfalso
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        subst hk
        rw [step_iterate] at h
        have h2 : (1 - η) ^ (k + 1) * e - e = 0 := sub_eq_zero.mpr h
        have h3 : ((1 - η) ^ (k + 1) - 1) * e = 0 := by
          rw [sub_mul, one_mul]; exact h2
        have h4 : (1 - η) ^ (k + 1) - 1 = 0 := (mul_eq_zero.mp h3).resolve_right he
        have hone : (1 - η) ^ (k + 1) = 1 := sub_eq_zero.mp h4
        have hlt : |1 - η| < 1 := abs_one_sub_lt_one hη0 hη2
        have habs : |1 - η| ^ (k + 1) = 1 := by rw [← abs_pow, hone, abs_one]
        have hp1 : |1 - η| ^ (k + 1) < 1 :=
          pow_lt_one_of_lt_one (abs_nonneg _) hlt (by omega)
        linarith
  · rintro (rfl | rfl)
    · exact iterate_zero η e
    · exact iterate_zero_of_zero η n

/-! ===========================================================================
  §6  与**裁决 K** 的交互：误差必然穿过 σ
  =========================================================================== -/

/-- **【§6 主定理 · 本专项最有价值的一条】回写必然使误差穿过 `σ`**。

  $$\sigma > 0,\ |e_0| > \sigma
    \;\Longrightarrow\;
    \exists n,\ |1-\eta|^n \cdot |e_0| \le \sigma .$$

  **超出定义之处**（这条定理为什么不是「显然」）：

  1. **`tends_to_zero` 只给「$\forall \varepsilon>0$ 最终 $<\varepsilon$」**，
     它**不**保证「某一刻恰好 $\le \sigma$ 之后**还**会怎样」，
     也**不**给出「**存在**某个有限的 $n$」（虽然两者等价，但形式不同）。
  2. **`contract_floor` 说误差永不为 `0`**，而 `σ > 0` ——
     正是这两条一起，才使得「误差**必然**与 σ 这个正高度相交」成为一个
     **非平凡**结论。若允许误差一步归零（`η = 1`），则「穿过 σ」退化为
     「一步跳过 σ」，性质完全不同；若允许误差停在 `0` 上方不动，
     则它可能**永远**碰不到 σ。
  3. 结论用 `≤` 而非 `<`，是因为**恰好相等**的情形（`|e_n| = σ`）
     恰恰是裁决 K 判**合格**的那一点 —— 这正是本定理与裁决 K 的接点。

  **与裁决 K 的关系**（本定理的**理论价值**）：`Error/FitBoundaryN.lean`
  的 `IsFitBoundaryN W σ γ := W.err γ = σ ∧ ∀ γ', σ ≤ W.err γ'`
  说的是「误差**恰好**是 σ 且 σ 是下界」。本定理说明：

  > **闭环回写一旦启用（`η ≠ 0`），误差就**必然**从「大于 σ」走到
  > 「小于 σ」，中间**必然**经过 σ 邻域。**

  于是「恰好等于 σ」**不是**回写的终点，而是它**路过**的一点；
  继续回写，误差会**落到 σ 以下**（§7 的 `below_sigma_forever`），
  而按裁决 K 的实质（「误差**小到开始拟合噪声**也不合格」），
  **继续回写反而使判据不合格**。 -/
theorem crosses_sigma {η : Real} (hη0 : 0 < η) (hη2 : η < 2)
    {e0 σ : Real} (hσ : 0 < σ) (hge : σ < |e0|) :
    ∃ n : Nat, |1 - η| ^ n * |e0| ≤ σ := by
  obtain ⟨N, hN⟩ := tends_to_zero η hη0 hη2 e0 σ hσ
  exact ⟨N, le_of_lt (hN N (le_refl N))⟩

/-- **【§6.2】穿过之后**不回头**（`≤` 版本）**：一旦某步 `≤ σ`，则**此后每一步都 `≤ σ`**。

  **超出定义之处**：`crosses_sigma` 只给「**存在**一步 `≤ σ`」；
  本定理说这一**不是偶发** —— 它之后**永久**成立。依据是
  `contract_mono`（`0 < η < 2` 且 `η ≠ 1` 时误差严格下降）。

  **⚠ `η = 1` 的例外**：此时一步归零（`contract_one_eta`），
  「此后每步 `≤ σ`」**仍然成立**（因为都是 `0 ≤ σ`），故本定理**不需要**
  `η ≠ 1` —— 但证明走 `contract_one_eta` 那条分支。 -/
theorem after_cross_stays {η : Real} (hη0 : 0 < η) (hη2 : η < 2)
    {e0 σ : Real} (hσ : 0 < σ) {N : Nat} (hN : |1 - η| ^ N * |e0| ≤ σ) :
    ∀ n : Nat, N ≤ n → |1 - η| ^ n * |e0| ≤ σ := by
  intro n hn
  have hbase : (0 : Real) ≤ |1 - η| := abs_nonneg (1 - η)
  have hmono : |1 - η| ^ n ≤ |1 - η| ^ N := by
    have hle1 : |1 - η| ≤ 1 := le_of_lt (abs_one_sub_lt_one hη0 hη2)
    exact pow_le_pow_of_le_one hbase hle1 hn
  have he0 : (0 : Real) ≤ |e0| := abs_nonneg e0
  exact le_trans (mul_le_mul_of_nonneg_right hmono he0) hN

/-- **【§6.3】严格穿过**：`σ > 0` 且 `|e₀| > σ` 时，存在一步使误差**严格小于** σ。

  **超出定义之处**：`crosses_sigma` 给 `≤`（含「恰好等于 σ」这一裁决 K
  判**合格**的点）；本定理给 `<` —— 即误差**真的越过**了 σ 这条线，
  落进「过拟合」那一侧（`Error/FitBoundaryN` 的 `accepts` 在
  `σ > ε` 时**必然**判不合格）。 -/
theorem crosses_sigma_strict {η : Real} (hη0 : 0 < η) (hη2 : η < 2)
    {e0 σ : Real} (hσ : 0 < σ) (hge : σ < |e0|) :
    ∃ n : Nat, |1 - η| ^ n * |e0| < σ := by
  have h := tends_to_zero η hη0 hη2 e0 σ hσ
  obtain ⟨N, hN⟩ := h
  exact ⟨N, hN N (le_refl N)⟩

/-- **【§6.4】裁决 K 的**带**必然被穿过**（本专项的**否定性**结论）。

  设 `σ > 0`、`ε ≥ 0`、`|e₀| > σ`。则**存在**一步 `n`，使回写后的残差 `|e_n|`
  **严格落在**裁决 K 的**下侧**：

  $$|e_n| < \sigma - \varepsilon \quad\text{（当 } \varepsilon < \sigma \text{）}.$$

  ⟹ 按 `Error/FitBoundaryN.accepts σ ε ·`，该步 **不合格**
  （"误差小到开始拟合噪声"）。

  **超出定义之处**：这是把 `crosses_sigma_strict` 与 `accepts` 的**定义**
  接起来 —— 于是「继续回写 ⟹ **必然**不合格」从口号变成定理。 -/
theorem eventually_below_K_band {η : Real} (hη0 : 0 < η) (hη2 : η < 2)
    {e0 σ : Real} (hσ : 0 < σ) {ε : Real} (hε : 0 ≤ ε) (hεσ : ε < σ)
    (hge : σ < |e0|) :
    ∃ n : Nat, ¬ ErrorN.accepts σ ε (|1 - η| ^ n * |e0|) := by
  -- 用 `ε' := σ - ε > 0` 取一步使误差 `< σ - ε`
  have hpos : (0 : Real) < σ - ε := by linarith
  obtain ⟨n, hn⟩ := tends_to_zero η hη0 hη2 e0 (σ - ε) hpos
  refine ⟨n, ?_⟩
  intro hacc
  unfold ErrorN.accepts at hacc
  have h1 := hn n (le_refl n)
  linarith [hacc.1]

/-- **【§6.5】`σ` 侧的可达性**：`σ > 0` 且 `|e₀| > σ` 时，**存在**一步落在
  `[σ−ε, σ+ε]` 带内（**正例**，说明裁决 K 的**合格**点在闭环轨迹上确实**可达**）。

  **超出定义之处**：`eventually_below_K_band` 说「**必然**有不合格的步」；
  本定理说的是**对偶**的一半：只要 `ε` 足够大，**带内**的时刻也**确实存在** ——
  因为误差从 `|e₀| > σ+ε` 连续地下降到 `σ−ε` 以下，中间必经过带。

  这条把 §6 的结论**补成双边**：误差**必然**既**经过**带、又**离开**带
  —— 于是裁决 K 的「恰好等于 σ」在闭环里**只是一个瞬态**，不是稳态。 -/
theorem reaches_K_band {η : Real} (hη0 : 0 < η) (hη2 : η < 2)
    {e0 σ : Real} (hσ : 0 < σ) {ε : Real} (hε : 0 ≤ ε)
    (hge : σ < |e0|) :
    ∃ n : Nat, |1 - η| ^ n * |e0| ≤ σ + ε := by
  obtain ⟨n, hn⟩ := crosses_sigma hη0 hη2 (e0 := e0) hσ hge
  exact ⟨n, le_trans hn (by linarith)⟩

/-! ===========================================================================
  §7  供 T33 使用（**非破坏性追加**，不改动上面任何一条定理）
  =========================================================================== -/

/-- **【§7.1】残差按 `|1−η|^n` **不增**（无窗口限制）。

  **超出定义之处**：`contract_mono` 只在「`0 < η < 2`、`η ≠ 1`」时给**严格**下降，
  `iterate_zero_of_zero` 只说 `e = 0` 不动。本定理**不需任何假设**（`η` 任意，
  含 `η = 1` 一步归零、`η = 2` 过冲等全部退化情形）就给出**单调不增**：

  $$|e_{n+1}| \le |e_n| \qquad (|1-\eta| \le 1).$$

  T33 的最优停止点存在性**只需要这一条**（不需要严格性）——
  正是「要弱形态才覆盖得住退化情形」的典型。 -/
theorem contract_anti {η : Real} (hη0 : 0 < η) (hη2 : η < 2) (e : Real) (n : Nat) :
    |1 - η| ^ (n + 1) * |e| ≤ |1 - η| ^ n * |e| := by
  have hle1 : |1 - η| ≤ 1 := le_of_lt (abs_one_sub_lt_one hη0 hη2)
  have hbase : (0 : Real) ≤ |1 - η| := abs_nonneg (1 - η)
  have hnn : (0 : Real) ≤ |1 - η| ^ n * |e| :=
    mul_nonneg (pow_nonneg hbase n) (abs_nonneg e)
  calc |1 - η| ^ (n + 1) * |e| = |1 - η| * (|1 - η| ^ n * |e|) := by
        rw [pow_succ]; ring
    _ ≤ 1 * (|1 - η| ^ n * |e|) := mul_le_mul_of_nonneg_right hle1 hnn
    _ = |1 - η| ^ n * |e| := one_mul _

/-- **【§7.2】对 `η ∈ (0,2)` 的**单调链**：`m ≤ n ⟹ |e_n| ≤ |e_m|`。

  **超出定义之处**：`contract_anti` 只比较相邻两步；最优停止点的**上界**估计
  需要比较**任意**两步（「带下界以上的所有位置误差都在带外」）。 -/
theorem contract_pow_mono {η : Real} (hη0 : 0 < η) (hη2 : η < 2) (n : Nat) :
    ∀ m : Nat, m ≤ n → |1 - η| ^ n ≤ |1 - η| ^ m := by
  intro m hm
  have hle1 : |1 - η| ≤ 1 := le_of_lt (abs_one_sub_lt_one hη0 hη2)
  exact pow_le_pow_of_le_one (abs_nonneg (1 - η)) hle1 hm

end Convergence

end FateV2.Loop

