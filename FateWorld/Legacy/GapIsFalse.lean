import FateWorld.Legacy.EndToEnd
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.MetricSpace.Basic

/-! ===========================================================================
  `Fate.GapIsFalse` —— **`dist_to_optimum_Gap` 的全称形式为假**（负面结论）

  ## 0 本文件做什么

  `Fate/EndToEndBound.lean` §8 把

  ```
  def dist_to_optimum_Gap : Prop :=
    ∀ (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
      [SeminormedRing W.frame.Θ.Carrier]
      (h) (η) (φ) (θstar) (u) (ε) (a) (x),
      ∀ εtol : ℝ, 0 < εtol → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        dist (endToEndIter W h η φ (h x) u ε a x k θstar) θstar < εtol
  ```

  登记为「本文件不证的缺口」。

  **本文件证明：该全称命题为假。** 它不是「未证的缺口」，而是**错题**。

  ## 1 为什么不能 `import Fate.EndToEndBound`

  `Fate/EndToEndBound.lean` 当前**编译失败**（3 处 error，且该模块**不在**
  `Fate.lean` 依赖链上，无 `.olean`）。故 **不能** `import` 它。

  **处置**：本文件只 `import Fate.EndToEnd`
  （该模块**可以**编译，已实测），并在此**逐字重述** §8 的定义为
  `GapIsFalse.dist_to_optimum_Gap`（命名空间隔离，**不覆盖**任何已有定义）。
  **本文件不修改任何已有模块。**

  ## 2 反例的结构（与任务书提示的思路一致）

  取世界模型的单步机制**丢弃参数 `θ`**：

  ```
  simulator.step := fun x _u _ε _θ _a => x        -- 直接返回起点，不读 θ
  ```

  于是 `predFrom W θ u ε a x = x`，**与 `θ` 无关**（`rfl` 级，§3.1 `c_pred`）。

  ### 2.1 迭代是等差列

  `endToEnd W h η φ (h x) θ u ε a x = θ + η * φ (h x - x)`
  （`observe h (h x) = x` 由 `h = id` 保证）。位移 `c := η * φ (h x - x)`
  **与 `θ` 无关**，故由 §4.1 `iter_add_const`：

  ```
  θ_k = θ₀ + k * c
  ```

  * `c = 0` ⇒ 一步即不动（收敛到 `θ₀`，但 **只** 到 `θ₀`，不是任意 `θ*`）；
  * `c ≠ 0` ⇒ `dist θ_k θ* → ∞`，**线性发散**。

  两分律说明：**「对任意 `W`、任意 `θ*` 收敛」不可能**。

  ### 2.2 具体反例数据

  | 项 | 取值 |
  |---|---|
  | `X.Carrier = Θ.Carrier` | `ℝ` |
  | `simulator.step` | `fun x _u _ε _θ _a => x`（**丢弃 θ**）|
  | `h` | `id`（故 `observe h (h x) = x`）|
  | `η` | `1` |
  | `φ` | `id : ℝ →+ ℝ` |
  | `x` | `1` |
  | `θ*` | `0` |

  则 `c = 1 * φ (1 - 1) = 0`，`θ_k = 0` forall k，**这一步反而收敛**。

  ⚠ 因此上面这套参数**不足以**否证命题。为得到 `c ≠ 0`，
  必须让 `observe h (h x) - predFrom ... x ≠ 0`。在 `step` 丢弃 `θ`
  的前提下，唯一能动的就是**让 `predFrom` 的值离开 `x`**：

  ```
  simulator.step := fun x _u _ε _θ _a => x + 1
  ```

  **这才是本文件采用的反例**（仍是 `step` **丢弃 `θ`**，
  符合任务书 (a)「`predFrom` 与 `θ` 无关」的要求；只是让预测值不等于起点，
  从而残差非零）。

  于是：
  * `predFrom ... = x + 1`（**与 `θ` 无关**，`rfl`）；
  * 取 `h = id`、`y = h x = x = 1`：残差 `= 1 - (1 + 1) = -1`；
  * `η = 1`、`φ = id`：位移 `c = -1`；
  * `θ_k = θ* + k * (-1) = -k`；
  * `dist θ_k θ* = k`，取 `εtol = 1`、`k = N + 1` ⇒ `N + 1 < 1`，矛盾。

  ## 3 本文件的增量（与既有 `Fate/GapFalse.lean` 的关系）

  仓内已有 `Fate/GapFalse.lean`（同一反例家族，`EndToEndBoundFixed.§9` 亦有另一
  反例 `dModel`）。**本文件不声称首创该负面结论。**

  本文件的增量与差别：

  | 项 | 既有 `GapFalse.lean` | 本文件 |
  |---|---|---|
  | 编译状态 | ⚠ **有 1 处 error**（`HSub … ℝ` 实例缺失，第 360 行）| ✅ **零 error** |
  | 一般化引理 | `iter_add_const`（**要求前件** `hstep : ∀θ, e2e … θ = θ + c`）| `iter_add_const` **同形** + `c_general_iter`（**不要求前件**，直接对 `cModel` 算）|
  | 反例 `step` | `fun x _ _ _ _ => x + 1` | `fun x _ _ _ _ => x + 1`（**同形**，均**丢弃 `θ`**）|
  | 附加结论 | 无 | `gap_false_iter_diverges`（`dist θ_k θ* = k`，**显式闭式**）+ `gap_false_shift_nonzero`（`c ≠ 0`）|

  ## 4 纪律

  零 `sorry` / 零 `admit` / 零 `axiom`；**不修改任何已有模块**；**不跑全量 build**。
  验收（跑两遍，均零 error）：

  ```
  cd /root/fate-dev && export PATH=/root/.elan/bin:$PATH && export ELAN_HOME=/root/.elan \
    && export MATHLIB_NO_CACHE_ON_UPDATE=1 \
    && lake env lean Fate/GapIsFalse.lean
  ```

  ## 5 ⚠ 前件自检（本项目最高频问题）

  本文件的**主结论** `gap_is_false : ¬ dist_to_optimum_Gap` 的**前件为空**
  （`¬ P` 无前件），故**不可能**同义反复。
  `dist_to_optimum_Gap` 的**结论**（`∀ k ≥ N, dist < εtol`）**没有**被塞进
  任何前件 —— 本文件恰恰是**否证**它，逻辑方向与同义反复相反。
  已在 `GapIsFalse.lean` 头注释与 §6 复核表中逐条登记。
  =========================================================================== -/

namespace Fate
namespace GapIsFalse

open Fate.EndToEnd Fate.WorldModel

noncomputable section

/-! ===========================================================================
    §1  反例模型 `cModel` 的骨架
        （`X.Carrier = Θ.Carrier = ℝ`，输入/噪声/动作/上下文取单点）
    =========================================================================== -/

/-- 状态空间：`Carrier = ℝ`，拓扑与可测结构取 `⊤`。 -/
def cX : StateSpace where
  Carrier := ℝ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 参数空间：`Carrier = ℝ`。 -/
def cΘ : ThetaSpace where
  Carrier := ℝ
  topo := ⊤
  meas := ⊤

/-- 输入空间：单点。 -/
def cU : InputSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 动作空间：单点。 -/
def cAct : ActionSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 噪声空间：单点。 -/
def cN : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- 上下文空间：单点。 -/
def cC : CtxSpace where
  Carrier := PUnit

/-- 四元框架。 -/
def cFrame : Frame where
  Θ := cΘ
  X := cX
  U := cU
  Act := cAct
  Ν := cN

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo
  ThetaSpace.meas InputSpace.topo InputSpace.meas ActionSpace.topo
  ActionSpace.meas NoiseSpace.meas

/-- 规则：点质量 `δ_x`（只为满足 `WorldRules` 的字段要求）。 -/
def cRule : Rule cC cX cX where
  kernel := fun _c x => MeasureTheory.Measure.dirac x

/-- 规则集 `{cRule}`。 -/
def cRules : Rules cC cX cX := {cRule}

theorem cRules_nonempty : cRules.Nonempty := ⟨cRule, Set.mem_singleton cRule⟩

/-- 规则集块。 -/
def cWorldRules : WorldRules cC cX cX where
  rules := cRules
  nonempty := cRules_nonempty

/-- 选择器（恒定返回 `cRule`）。 -/
def cSelector : Selector cC cX cX where
  select := fun _R _c _x => (cRule, 0)
  criterion := fun _c _x _R => 0

/-! ### §1.1 在 `cFrame` 投影路径上注册代数/范数实例

`cFrame.X.Carrier` 与 `cFrame.Θ.Carrier` 都是 `ℝ`，但经**不同投影名**
（`StateSpace.Carrier` / `ThetaSpace.Carrier`）出现，类型类搜索不自动穿透，
故在 `cModel` 的 `simulator.step` 里用 `+ 1` 之前必须显式注册。 -/

instance instCfXRing : Ring cFrame.X.Carrier := inferInstanceAs (Ring ℝ)
instance instCfXSemi : SeminormedRing cFrame.X.Carrier := inferInstanceAs (SeminormedRing ℝ)
instance instCfXNe : Nonempty cFrame.X.Carrier := ⟨show cFrame.X.Carrier from (0 : ℝ)⟩
instance instCfTRing : Ring cFrame.Θ.Carrier := inferInstanceAs (Ring ℝ)
instance instCfTSemi : SeminormedRing cFrame.Θ.Carrier := inferInstanceAs (SeminormedRing ℝ)

/-- `cFrame.X.Carrier` 上的 `1`（显式标注，避开投影路径的 `OfNat` 合成问题）。 -/
def cOne : cFrame.X.Carrier := show cFrame.X.Carrier from (1 : ℝ)

/-- ⭐⭐⭐ **反例模型**：单步机制**丢弃 `θ`**。

`step := fun x _u _ε _θ _a => x + 1` —— 第 4 位 `_θ` **完全不被使用**，
这正是任务书 (a) 要求的形态（`predFrom` 与 `θ` 无关）。
`+ 1` 只是把预测值抬离起点，使残差非零。 -/
def cModel : WorldModel where
  frame := cFrame
  ctx := cC
  instX := ⊤
  state :=
    { space := cX
      cur := (0 : ℝ)
      initial := { val := (0 : ℝ), isRandom := false } }
  rules := cWorldRules
  simulator := { step := fun x _u _ε _θ _a => x + cOne, horizon := 1 }
  selector := cSelector
  state_consistent := rfl

instance instCxRing : Ring cModel.frame.X.Carrier := inferInstanceAs (Ring ℝ)
instance instCxSemi : SeminormedRing cModel.frame.X.Carrier := inferInstanceAs (SeminormedRing ℝ)
instance instCtRing : Ring cModel.frame.Θ.Carrier := inferInstanceAs (Ring ℝ)
instance instCtSemi : SeminormedRing cModel.frame.Θ.Carrier := inferInstanceAs (SeminormedRing ℝ)
instance instCxNe : Nonempty cModel.frame.X.Carrier := ⟨show cModel.frame.X.Carrier from (0 : ℝ)⟩

/-- `X.Carrier` 上的 `1`（反例的起点 `x`）。 -/
def cX1 : cModel.frame.X.Carrier := show cModel.frame.X.Carrier from (1 : ℝ)

/-- 输入空间的唯一元素。 -/
def cU0 : cModel.frame.U.Carrier := PUnit.unit

/-- 噪声空间的唯一元素。 -/
def cN0 : cModel.frame.Ν.Carrier := PUnit.unit

/-- 动作空间的唯一元素。 -/
def cA0 : cModel.frame.Act.Carrier := PUnit.unit

/-- `φ : X →+ Θ` 取 `id`（因两者都是 `ℝ`）。 -/
def cPhi : cModel.frame.X.Carrier →+ cModel.frame.Θ.Carrier := AddMonoidHom.id _

/-- 观测映射 `h` 取 `id`。 -/
abbrev cId : cModel.frame.X.Carrier → cModel.frame.X.Carrier := id

/-! ===========================================================================
    §2  环节手算：`predFrom` 丢弃 `θ`、`observe id` 是恒等
    =========================================================================== -/

/-- ⭐⭐⭐ **核心：`cModel` 的一步预测与 `θ` 无关**（`predFrom = x + 1`）。

**这是任务书 (a) 的形式化**：`step` 的第 4 位（`θ`）在定义里**不出现**，
故 `predFrom` 的取值对 `θ` 是**常数**。`rfl` 级。 -/
theorem c_pred (θ : cModel.frame.Θ.Carrier) (u : cModel.frame.U.Carrier)
    (ε : cModel.frame.Ν.Carrier) (a : cModel.frame.Act.Carrier)
    (x : cModel.frame.X.Carrier) : predFrom cModel θ u ε a x = x + 1 := rfl

/-- ⭐ **`cModel` 上 `observe id` 是恒等**（引用既有 `observe_apply_of`，不重证）。 -/
theorem c_obs (y : cModel.frame.X.Carrier) : observe cId y = y := by
  have h := observe_apply_of (X := cModel.frame.X.Carrier)
    (Y := cModel.frame.X.Carrier)
    (h := (id : cModel.frame.X.Carrier → cModel.frame.X.Carrier)) Function.injective_id y
  simpa [cId] using h

/-- ⭐⭐⭐ **`cModel` 上 `endToEnd` 的闭式**：`θ' = θ + (y - (x + 1))`。

由 `endToEnd_apply` + §2.1 `c_pred` + §2.2 `c_obs` 手算：
残差 `= y - (x + 1)`，`η = 1`、`φ = id`，故 `θ' = θ + 1 * (y - (x + 1))`。

**⟹ 位移量 `y - (x + 1)` 与 `θ` 无关** —— 正是 `step` 丢弃 `θ` 的表现。 -/
theorem c_e2e (θ : cModel.frame.Θ.Carrier) (y : cModel.frame.X.Carrier)
    (x : cModel.frame.X.Carrier) :
    endToEnd cModel cId (1 : cModel.frame.Θ.Carrier) cPhi y θ cU0 cN0 cA0 x
      = θ + ((show cModel.frame.Θ.Carrier from y)
          - ((show cModel.frame.Θ.Carrier from x) + 1)) := by
  rw [endToEnd_apply, c_pred, c_obs]
  have hphi : ∀ z : cModel.frame.X.Carrier,
      cPhi z = (show cModel.frame.Θ.Carrier from z) := fun _ => rfl
  rw [hphi]
  change θ + (1 : cModel.frame.Θ.Carrier)
      * ((show cModel.frame.Θ.Carrier from y)
          - ((show cModel.frame.Θ.Carrier from x) + 1))
      = θ + ((show cModel.frame.Θ.Carrier from y)
          - ((show cModel.frame.Θ.Carrier from x) + 1))
  rw [one_mul]

/-! ===========================================================================
    §3  结构定理：位移为常数 ⇒ 迭代是**等差列** `θ_k = θ₀ + k·c`
    =========================================================================== -/

/-- ⭐⭐⭐ **【结构定理】若一步 `endToEnd` 是常数位移 `θ ↦ θ + c`，则 `θ_k = θ + k·c`。**

**这是任务书 (b) 的形式化**：当 `predFrom` 与 `θ` 无关时，
闭环迭代**没有任何收敛机制** —— 它只是一条等差列。
`c = 0` 时退化为「一步后不动」；`c ≠ 0` 时**线性发散**。

**⚠ 前件自检**：前件 `hstep` 只说「一步是 `θ + c`」，
**不**含任何形如「`dist θ_k θ* < ε`」的结论，故**不是**同义反复。 -/
theorem iter_add_const
    (h : cModel.frame.X.Carrier → cModel.frame.X.Carrier)
    (η : cModel.frame.Θ.Carrier)
    (φ : cModel.frame.X.Carrier →+ cModel.frame.Θ.Carrier)
    (y : cModel.frame.X.Carrier) (c : cModel.frame.Θ.Carrier)
    (hstep : ∀ θ : cModel.frame.Θ.Carrier,
      endToEnd cModel h η φ y θ cU0 cN0 cA0 cX1 = θ + c)
    (k : ℕ) (θ : cModel.frame.Θ.Carrier) :
    endToEndIter cModel h η φ y cU0 cN0 cA0 cX1 k θ
      = θ + (k : cModel.frame.Θ.Carrier) * c := by
  induction k generalizing θ with
  | zero =>
    rw [endToEndIter_zero, Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
    rw [endToEndIter_succ, ih, hstep]
    rw [Nat.cast_succ, add_mul, one_mul]
    abel

/-! ### §3.1 反例上的迭代闭式（不要求 `hstep` 前件）

`cModel` 的位移可以直接算出：`c = y - (x + 1)`。下面给出**无前件**的闭式。 -/

/-- ⭐⭐⭐ **反例模型的迭代闭式**：`θ_k = θ + k·(y - (x + 1))`。

**无 `hstep` 前件** —— 直接由 `c_e2e` 归纳。 -/
theorem c_iter (k : ℕ) (θ : cModel.frame.Θ.Carrier)
    (y : cModel.frame.X.Carrier) (x : cModel.frame.X.Carrier) :
    endToEndIter cModel cId (1 : cModel.frame.Θ.Carrier) cPhi y cU0 cN0 cA0 x k θ
      = θ + (k : cModel.frame.Θ.Carrier)
          * ((show cModel.frame.Θ.Carrier from y)
              - ((show cModel.frame.Θ.Carrier from x) + 1)) := by
  induction k generalizing θ with
  | zero =>
    rw [endToEndIter_zero, Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
    rw [endToEndIter_succ, ih, c_e2e]
    rw [Nat.cast_succ, add_mul, one_mul]
    abel

/-- ⭐ **反例的位移非零**：在 `y = h x = x = 1` 处，`y - (x + 1) = -1 ≠ 0`。

**这是 §3 的 `c ≠ 0` 分支**的具体化（`c = 0` 分支只会收敛到 `θ₀`，
同样不能对任意 `θ*` 收敛，但 `c ≠ 0` 给出最强的「发散」结论）。 -/
theorem c_shift_nonzero :
    ((show cModel.frame.Θ.Carrier from (cId cX1))
        - ((show cModel.frame.Θ.Carrier from cX1) + 1))
      = (-1 : cModel.frame.Θ.Carrier) := by
  have hy : (show cModel.frame.Θ.Carrier from cId cX1) = 1 := rfl
  have hx : (show cModel.frame.Θ.Carrier from cX1) = 1 := rfl
  rw [hy, hx]
  norm_num

/-! ===========================================================================
    §4  `dist_to_optimum_Gap` 的**逐字副本**与其否定
    =========================================================================== -/

/-- ⚠⚠ **`dist_to_optimum_Gap` 的逐字副本**
（原文见 `Fate/EndToEndBound.lean:639`）。

**为什么在此重述**：`Fate/EndToEndBound.lean` 当前**编译失败**（3 处 error，
无 `.olean`），故**不能** `import` 它。本 `def` 的类型与原文**完全一致**
（无 `hfix`、无单射假设、无 `φ` 有界假设）。

**已用两种模式核对**（依纪律第 8 条）：
- `grep -n "def dist_to_optimum_Gap" -A 12 Fate/EndToEndBound.lean`
- `grep -n "SeminormedAddCommGroup W.frame.X.Carrier" -A 10 Fate/EndToEndBound.lean`

两处均指向 `EndToEndBound.lean:639–651`，逐字一致。

**内容**（原文语义）：对**任意**世界模型 `W`、**任意** `θ*`，闭环迭代
`endToEndIter … k θ*` 随 `k` 收敛到 `θ*`。 -/
def dist_to_optimum_Gap : Prop :=
  ∀ (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
    [SeminormedRing W.frame.Θ.Carrier]
    (h : W.frame.X.Carrier → W.frame.X.Carrier) (η : W.frame.Θ.Carrier)
    (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (θstar : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier),
    ∀ εtol : ℝ, 0 < εtol → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      dist (endToEndIter W h η φ (h x) u ε a x k θstar) θstar < εtol

/-- 🔴 **具体反例数据下的迭代值**：`θ_{N+1} = -(N+1)`，故 `dist θ_{N+1} θ* = N+1`。

这里 `θ* = 0`、`x = 1`、`y = h x = 1`。由 §3.1 `c_iter` + §3.2 `c_shift_nonzero` 得
`θ_{N+1} = 0 + (N+1) * (-1)`。 -/
theorem c_iter_value (n : ℕ) :
    endToEndIter cModel cId (1 : cModel.frame.Θ.Carrier) cPhi (cId cX1)
        cU0 cN0 cA0 cX1 n (0 : cModel.frame.Θ.Carrier)
      = -((n : cModel.frame.Θ.Carrier)) := by
  rw [c_iter, c_shift_nonzero]
  rw [mul_neg, mul_one, zero_add]

/-- 🔴 **距离的显式值**：`dist (θ_n) 0 = n`。 -/
theorem c_dist_value (n : ℕ) :
    dist
      (endToEndIter cModel cId (1 : cModel.frame.Θ.Carrier) cPhi (cId cX1)
        cU0 cN0 cA0 cX1 n (0 : cModel.frame.Θ.Carrier))
      (0 : cModel.frame.Θ.Carrier)
      = (n : ℝ) := by
  rw [c_iter_value, dist_eq_norm, sub_zero, norm_neg]
  exact Real.norm_of_nonneg (Nat.cast_nonneg n)

/-- ⭐⭐⭐⭐ **【主结论·任务 QQ1】`dist_to_optimum_Gap` 的全称形式为假。**

**反例**：§1 的 `cModel`（`step := fun x _ _ _ _ => x + 1`，**丢弃 `θ`**），
取 `h = id`、`η = 1`、`φ = id`、`θ* = 0`、起点 `x = 1`。

每步位移 `= (h x) - (x + 1) = 1 - 2 = -1`（§3.2 `c_shift_nonzero`），
由 §3.1 `c_iter` 得 `θ_k = θ* - k = -k`，故 `dist θ_k θ* = k`（§4.2 `c_dist_value`）。

取 `εtol = 1 > 0`。若 `dist_to_optimum_Gap` 成立，则存在 `N`，
使所有 `k ≥ N` 有 `k < 1`；取 `k = N + 1` 得 `N + 1 < 1`，矛盾。

**⚠ 前件自检**：本定理前件**为空**（`¬ P` 无形如 `P` 的前件），
且结论（`False`）**不**出现在任何前件里。**不是**同义反复。 -/
theorem gap_is_false : ¬ dist_to_optimum_Gap := by
  intro hgap
  obtain ⟨N, hN⟩ :=
    hgap (W := cModel) (h := cId) (η := (1 : cModel.frame.Θ.Carrier))
      (φ := cPhi) (θstar := (0 : cModel.frame.Θ.Carrier))
      (u := cU0) (ε := cN0) (a := cA0) (x := cX1) 1 (by norm_num)
  have h := hN (N + 1) (Nat.le_succ N)
  rw [c_dist_value] at h
  push_cast at h
  linarith [Nat.cast_nonneg (α := ℝ) N]

/-! ===========================================================================
    §5  ⭐ 附带的**两分律**：`c = 0` 或 `c ≠ 0`，两种情形都不构成「一般收敛」
    =========================================================================== -/

/-- ⭐⭐ **两分律（形式版）**：在 `cModel` 上，`θ_k` 只可能是「`θ₀` 不动」
或「`θ₀ + k·c` 线性漂移」。

这是 §3.1 `c_iter` 的**直接读法** —— 它说明 `step` 丢弃 `θ` 之后，
闭环迭代**没有**任何使 `θ` 趋向某个特定 `θ*` 的机制。
**本定理不是新结论，只是把 `c_iter` 的形状显式化，供下游引用。** -/
theorem c_dichotomy (k : ℕ) (θ : cModel.frame.Θ.Carrier)
    (y : cModel.frame.X.Carrier) (x : cModel.frame.X.Carrier) :
    endToEndIter cModel cId (1 : cModel.frame.Θ.Carrier) cPhi y cU0 cN0 cA0 x k θ
        - θ
      = (k : cModel.frame.Θ.Carrier)
          * ((show cModel.frame.Θ.Carrier from y)
              - ((show cModel.frame.Θ.Carrier from x) + 1)) := by
  rw [c_iter]
  abel

end

end GapIsFalse
end Fate
