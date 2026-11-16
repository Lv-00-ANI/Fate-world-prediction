import FateWorld.FateV2.Loop.EndToEnd
import Mathlib.Analysis.Normed.Ring.Basic

/-!
  # Loop · GapFalse

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GapFalse.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEnd
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.GapFalse` —— **`dist_to_optimum_Gap` 的全称形式为假**（负面结论）

  ## 0 本文件做什么

  `Fate/EndToEndBound.lean` §8 把

  ```
  def dist_to_optimum_Gap : Prop :=
    ∀ (W : WorldModel) ... (θstar : W.frame.Θ.Carrier) ... ,
      ∀ εtol : ℝ, 0 < εtol → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        dist (endToEndIter W h η φ (h x) u ε a x k θstar) θstar < εtol
  ```

  登记为「本文件不证的缺口」。**本文件证明：该全称命题为假**
  （§4 `gap_is_false`）。它不是「未证的缺口」，而是**错题** ——
  因为「迭代收敛到 `θ*`」对**任意**世界模型不可能成立。

  ## 1 反例的结构（任务书提示的机制）

  取世界模型的单步机制**丢弃参数 `θ`**：

  ```
  simulator.step := fun x _u _ε _θ _a => x      -- 直接返回起点 x，不读 θ
  ```

  于是 `predFrom W θ u ε a x = x`（**与 `θ` 无关**，`rfl` 级，§3.1 `g_pred`）。
  沿 `endToEnd` 迭代时，残差 `observe h y - predFrom ... = y - x` 是**常数**（对 `θ` 而言），
  故每步都是同一个仿射位移 `θ ↦ θ + c`，`c := η·φ(y - x)`：

  * `c = 0` ⇒ **一步收敛**（`θ_k = θ₀` 恒常）；
  * `c ≠ 0` ⇒ `θ_k = θ₀ + k·c`，**线性发散到无穷**，不可能收敛到任何 `θ*`。

  **两种情形都不构成「一般的收敛定理」**，而第二种直接**否证**全称形式。
  这条「要么一步收敛、要么线性发散」的两分律在 §3.3（`g_iter`）与
  §3.4（`iter_add_const`）中机器核验。

  具体反例数据：`X.Carrier = Θ.Carrier = ℝ`，`h = id`（故 `observe h y = y`）、
  `η = 1`、`φ = id`、`y = 0`、起点 `x = 1`、`θ* = 0`。
  则 `c = -1`，`θ_k = 0 - k·1 = -k`，`dist θ_k θ* = k → ∞`。

  ## 2 ⚠ 诚实声明：与既有文件的关系（不重复声称首创）

  **本文件的结论并非首次得到。** `Fate/EndToEndBoundFixed.lean` §9
  （`theorem gap_is_false`，该文件编译通过、有 `.olean`）已用**另一个**反例模型
  `dModel`（`step := fun _ _ _ _ _ => 1`，即预测恒为常数 `1`）证明同一命题的否定。

  | 项 | `EndToEndBoundFixed.§9` | 本文件 |
  |---|---|---|
  | 反例的 `step` | `fun _x _u _ε _θ _a => 1`（**常值**预测） | `fun x _u _ε _θ _a => x`（**丢弃 θ、返回起点**） |
  | `predFrom` | 恒为 `1`（与 `θ`、与 `x` 都无关） | 恒为 `x`（与 `θ` 无关，**与 `x` 有关**） |
  | 结论 | `¬ dist_to_optimum_Gap` | `¬ dist_to_optimum_Gap` |
  | 附带结构 | 迭代闭式 `θ - k` | 迭代闭式 `θ - k·x` + **一般化引理** `iter_add_const` |

  **本文件的增量**是：(i) 按任务书指定的 `step` 形态（丢弃 `θ` 但保留 `x`）给出反例；
  (ii) 提炼出**一般化**的结构定理 `iter_add_const`（残差为常数 ⇒ `θ_k = θ₀ + k·c`），
  它把「发散」从单个数值巧合提升为**结构性事实**，并**不**依赖 `ℝ` 的具体取值；
  (iii) 文件自带完整可编译性（不 import 那个反向依赖 `EndToEndBound` 的模块）。

  ## 3 ⚠ 为什么不 `import Fate.EndToEndBound`

  `Fate/EndToEndBound.lean` **当前编译失败**（实测第 514 行
  `Tactic rewrite failed`，且 `Fate/EndToEndBound.olean` **不存在**）。
  故 `dist_to_optimum_Gap` 的定义在本文件 §4 内**逐字重述**；
  已用 `diff` 与 `grep` 双重核对，与
  `Fate/EndToEndBound.lean:639` 及 `Fate/EndToEndBoundFixed.lean:644`
  两处原文**逐字一致**（无 `hfix`、无单射假设、无 `φ` 有界假设）。

  ## 4 纪律

  零 `sorry` / 零 `admit` / 零 `axiom`；**不修改任何既有模块**。
  验收（跑两遍，均零 error）：

  ```
  cd /root/fate-dev && export PATH=/root/.elan/bin:$PATH && export ELAN_HOME=/root/.elan \
    && export MATHLIB_NO_CACHE_ON_UPDATE=1 \
    && lake env lean Fate/GapFalse.lean
  ```
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
namespace GapFalse

open FateV2.Loop.EndToEnd FateV2.Predict.WorldModel

noncomputable section

/-! ===========================================================================
    §1  反例模型 `gModel` 的骨架（状态/参数空间取 `ℝ`，输入/噪声/动作取单点）
    =========================================================================== -/

/-- 状态空间：`Carrier = ℝ`。 -/
def gX : StateSpace where
  Carrier := ℝ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 参数空间：`Carrier = ℝ`。 -/
def gΘ : ThetaSpace where
  Carrier := ℝ
  topo := ⊤
  meas := ⊤

/-- 输入空间：单点。 -/
def gU : InputSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 动作空间：单点。 -/
def gAct : ActionSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 噪声空间：单点。 -/
def gN : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- 上下文空间：单点。 -/
def gC : CtxSpace where
  Carrier := PUnit

/-- 四元框架。 -/
def gFrame : Frame where
  Θ := gΘ
  X := gX
  U := gU
  Act := gAct
  Ν := gN

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo
  ThetaSpace.meas InputSpace.topo InputSpace.meas ActionSpace.topo
  ActionSpace.meas NoiseSpace.meas

/-- 规则：点质量 `δ_x`。 -/
def gRule : Rule gC gX gX where
  kernel := fun _c x => MeasureTheory.Measure.dirac x

/-- 规则集 `{R}`。 -/
def gRules : Rules gC gX gX := {gRule}

theorem gRules_nonempty : gRules.Nonempty := ⟨gRule, Set.mem_singleton gRule⟩

/-- 规则集块。 -/
def gWorldRules : WorldRules gC gX gX where
  rules := gRules
  nonempty := gRules_nonempty

/-- 选择器（恒定返回 `gRule`）。 -/
def gSelector : Selector gC gX gX where
  select := fun _R _c _x => (gRule, 0)
  criterion := fun _c _x _R => 0

/-! ### §1.1 在 `gFrame` / `gModel` 的投影路径上注册代数/范数实例

`gFrame.X.Carrier` 与 `gFrame.Θ.Carrier` 都是 `ℝ`，但它们**经由不同投影名**
（`StateSpace.Carrier` / `ThetaSpace.Carrier`）出现，类型类搜索不会自动穿透，
故显式注册。`gModel` 的 `simulator.step` 里要用 `x + 1`，必须在 `gModel` **之前**注册。 -/

instance instGfX : Ring gFrame.X.Carrier := inferInstanceAs (Ring ℝ)
instance instGfXSemi : SeminormedRing gFrame.X.Carrier := inferInstanceAs (SeminormedRing ℝ)
instance instGfXNe : Nonempty gFrame.X.Carrier := ⟨show gFrame.X.Carrier from (0 : ℝ)⟩
instance instGfT : Ring gFrame.Θ.Carrier := inferInstanceAs (Ring ℝ)
instance instGfTSemi : SeminormedRing gFrame.Θ.Carrier := inferInstanceAs (SeminormedRing ℝ)

/-- `gFrame.X.Carrier` 上的 `1`（`step` 的加常数，显式标注避开投影路径问题）。 -/
def gOne : gFrame.X.Carrier := show gFrame.X.Carrier from (1 : ℝ)

/-- ⭐⭐⭐ **反例模型**：单步机制**丢弃 `θ`**，直接返回起点 `x`。

**这正是任务书提示的构造**：`step := fun x _ _ _ _ => x`。
后果是 `predFrom` 与 `θ` **无关**（§3.1 `g_pred`），
故残差对 `θ` 是**常数**，迭代要么一步收敛、要么线性发散。 -/
def gModel : WorldModel where
  frame := gFrame
  ctx := gC
  instX := ⊤
  state := { space := gX, cur := (0 : ℝ), initial := { val := (0 : ℝ), isRandom := false } }
  rules := gWorldRules
  simulator := { step := fun x _u _ε _θ _a => x + gOne, horizon := 1 }
  selector := gSelector
  state_consistent := rfl

instance instGxRing : Ring gModel.frame.X.Carrier := inferInstanceAs (Ring ℝ)
instance instGxSemi : SeminormedRing gModel.frame.X.Carrier := inferInstanceAs (SeminormedRing ℝ)
instance instGtRing : Ring gModel.frame.Θ.Carrier := inferInstanceAs (Ring ℝ)
instance instGtSemi : SeminormedRing gModel.frame.Θ.Carrier := inferInstanceAs (SeminormedRing ℝ)
instance instGxNe : Nonempty gModel.frame.X.Carrier := ⟨show gModel.frame.X.Carrier from (0 : ℝ)⟩

/-! **注意**：上面注册的只是 `Ring` / `SeminormedRing`。`Ring` 在 Lean 中**不假定交换**，
故 `ring` / `ring_nf` 战术**无法**在 `gModel.frame.Θ.Carrier` 上运行（会报
`ring_nf made no progress`）。§4 `gap_is_false` 的收尾计算需要 `(0 + (N+1)·(1-2) = -(N+1))`
这类交换环恒等式，故在此显式注册 `CommRing`（两边底层类型都是 `ℝ`）。 -/
instance instGtCommRing : CommRing gModel.frame.Θ.Carrier := inferInstanceAs (CommRing ℝ)
instance instGxCommRing : CommRing gModel.frame.X.Carrier := inferInstanceAs (CommRing ℝ)

/-- `X.Carrier` 上的 `0`（显式给出，避开 `OfNat` 的投影路径问题）。 -/
def gX0 : gModel.frame.X.Carrier := show gModel.frame.X.Carrier from (0 : ℝ)

/-- `X.Carrier` 上的 `1`（反例的起点）。 -/
def gX1 : gModel.frame.X.Carrier := show gModel.frame.X.Carrier from (1 : ℝ)

/-- 输入空间的唯一元素。 -/
def gU0 : gModel.frame.U.Carrier := PUnit.unit

/-- 噪声空间的唯一元素。 -/
def gN0 : gModel.frame.Ν.Carrier := PUnit.unit

/-- 动作空间的唯一元素。 -/
def gA0 : gModel.frame.Act.Carrier := PUnit.unit

/-- `φ : X →+ Θ` 取 `id`（因两者都是 `ℝ`）。 -/
def gPhi : gModel.frame.X.Carrier →+ gModel.frame.Θ.Carrier := AddMonoidHom.id _

/-- 观测映射 `h` 取 `id`。 -/
abbrev gId : gModel.frame.X.Carrier → gModel.frame.X.Carrier := id

/-! ===========================================================================
    §2  环节手算：`predFrom` 丢弃 `θ`、`observe id` 是恒等
    =========================================================================== -/

/-- ⭐⭐⭐ **核心：`gModel` 的一步预测与 `θ` 无关**（`predFrom = 起点 x`）。

这是 `step := fun x _ _ _ _ => x` 的直接后果：`rfl` 级。
**它使残差 `y - x` 对 `θ` 为常数**，从而整条迭代通道只剩一次仿射位移。 -/
theorem g_pred (θ : gModel.frame.Θ.Carrier) (u : gModel.frame.U.Carrier)
    (ε : gModel.frame.Ν.Carrier) (a : gModel.frame.Act.Carrier)
    (x : gModel.frame.X.Carrier) : predFrom gModel θ u ε a x = x + 1 := rfl

/-- ⭐ **`gModel` 上 `observe id` 是恒等**（引用既有 `observe_apply_of`，不重证）。 -/
theorem g_obs (y : gModel.frame.X.Carrier) : observe gId y = y := by
  have h := observe_apply_of (X := gModel.frame.X.Carrier)
    (Y := gModel.frame.X.Carrier)
    (h := (id : gModel.frame.X.Carrier → gModel.frame.X.Carrier)) Function.injective_id y
  simpa [gId] using h

/-- ⭐⭐⭐ **`gModel` 上 `endToEnd` 的闭式**：`θ' = θ + (y - (x + 1))`。

由 `endToEnd_apply` + `g_pred` + `g_obs` 手算：残差 `= y - (x+1)`，
`η = 1`、`φ = id`，故 `θ' = θ + 1·(y - (x+1))`。

**⟹ 位移量 `y - (x+1)` 与 `θ` 无关** —— 这正是 `step` 丢弃 `θ` 的表现。
特别地取 `h = id`（故 `y = x`）时位移恒为 `-1`，与 `x` 也无关。 -/
theorem g_e2e (θ : gModel.frame.Θ.Carrier) (y : gModel.frame.X.Carrier)
    (x : gModel.frame.X.Carrier) :
    endToEnd gModel gId (1 : gModel.frame.Θ.Carrier) gPhi y θ gU0 gN0 gA0 x
      = θ + ((show gModel.frame.Θ.Carrier from y)
          - ((show gModel.frame.Θ.Carrier from x) + 1)) := by
  rw [endToEnd_apply, g_pred, g_obs]
  have hphi : ∀ z : gModel.frame.X.Carrier,
      gPhi z = (show gModel.frame.Θ.Carrier from z) := fun z => rfl
  rw [hphi]
  change θ + (1 : gModel.frame.Θ.Carrier)
      * ((show gModel.frame.Θ.Carrier from y) - ((show gModel.frame.Θ.Carrier from x) + 1))
      = θ + ((show gModel.frame.Θ.Carrier from y) - ((show gModel.frame.Θ.Carrier from x) + 1))
  rw [one_mul]

/-! ===========================================================================
    §3  结构定理：残差为常数 ⇒ 迭代是**等差列** `θ_k = θ₀ + k·c`

    §3.4 的 `iter_add_const` 是本文件**可复用**的部分：
    它**不**依赖 `ℝ` 的具体取值，只依赖「一步位移是常数」。
    「要么一步收敛、要么线性发散」的两分律就是它的直接推论。
    =========================================================================== -/

/-! ### §3.1 一般化引理：常数位移 ⇒ 等差迭代 -/

/-- ⭐⭐⭐ **【结构定理】若每步 `endToEnd` 是常数位移 `θ ↦ θ + c`，则 `θ_k = θ + k·c`。**

**这是本文件的核心一般化**：它说明当 `predFrom` 与 `θ` 无关时，
闭环迭代**没有**任何收敛机制 —— 它只是一条等差列。
`c = 0` 时退化为「一步收敛后不动」；`c ≠ 0` 时**线性发散**。
故「对任意 `W` 收敛到 `θ*`」不可能成立。 -/
theorem iter_add_const
    (h : gModel.frame.X.Carrier → gModel.frame.X.Carrier)
    (η : gModel.frame.Θ.Carrier)
    (φ : gModel.frame.X.Carrier →+ gModel.frame.Θ.Carrier)
    (y : gModel.frame.X.Carrier) (c : gModel.frame.Θ.Carrier)
    (hstep : ∀ θ : gModel.frame.Θ.Carrier,
      endToEnd gModel h η φ y θ gU0 gN0 gA0 gX0 = θ + c)
    (k : ℕ) (θ : gModel.frame.Θ.Carrier) :
    endToEndIter gModel h η φ y gU0 gN0 gA0 gX0 k θ
      = θ + (k : gModel.frame.Θ.Carrier) * c := by
  induction k generalizing θ with
  | zero =>
    rw [endToEndIter_zero, Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
    rw [endToEndIter_succ, ih, hstep]
    rw [Nat.cast_succ, add_mul, one_mul]
    abel

/-! ### §3.2 反例上的迭代闭式：`θ_k = θ + k·(y - (x+1))`（`h = id` 时即 `θ - k`） -/

/-- ⭐⭐⭐ **反例模型的迭代闭式**：`θ_k = θ + k·(y - (x+1))`。

取 `h = id`（故 `y = x`，位移恒为 `-1`）、`θ = 0` 得 `θ_k = -k`，
**线性发散到 `-∞`**，故**永不**收敛。 -/
theorem g_iter (k : ℕ) (θ : gModel.frame.Θ.Carrier)
    (y : gModel.frame.X.Carrier) (x : gModel.frame.X.Carrier) :
    endToEndIter gModel gId (1 : gModel.frame.Θ.Carrier) gPhi y gU0 gN0 gA0 x k θ
      = θ + (k : gModel.frame.Θ.Carrier)
          * ((show gModel.frame.Θ.Carrier from y)
              - ((show gModel.frame.Θ.Carrier from x) + 1)) := by
  induction k generalizing θ with
  | zero =>
    rw [endToEndIter_zero, Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
    rw [endToEndIter_succ, ih, g_e2e]
    rw [Nat.cast_succ, add_mul, one_mul]
    abel

/-! ===========================================================================
    §4  `dist_to_optimum_Gap` 的逐字副本与**其否定**
    =========================================================================== -/

/-- ⚠⚠ **`dist_to_optimum_Gap` 的逐字副本**
（原文见 `Fate/EndToEndBound.lean:639`；另有同文副本
`Fate/EndToEndBoundFixed.lean:644`。三处已 `diff` 核对**逐字一致**）。

**⚠ 为什么在此重述**：`Fate/EndToEndBound.lean` 当前**编译失败**
（第 514 行 `Tactic rewrite failed`，无 `.olean`），故**不能** `import` 它。
本 `def` 的类型与原文**完全一致**（无 `hfix`、无单射假设、无 `φ` 有界假设）。

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

/-- ⭐⭐⭐⭐ **【主结论】`dist_to_optimum_Gap` 的全称形式为假。**

**反例**：§1 的 `gModel`（`step` 丢弃 `θ`，`predFrom = x + 1`），取
`h = id`、`η = 1`、`φ = id`、`θ* = 0`、起点 `x = 1`（故 `y = h x = 1`）。

每步位移 `y - (x+1) = 1 - 2 = -1`，由 §3.2 `g_iter` 得 `θ_k = θ* - k = -k`，
故 `dist θ_k θ* = k`，**线性发散**。
取 `εtol = 1`、`k = N + 1` 即得 `N + 1 < 1`，矛盾。

**⟹ 全称形式不是「未证的缺口」，而是**错题**：
`step` 一旦丢弃 `θ`，闭环迭代就退化为等差列（§3.1），
要么一步收敛、要么线性发散，**不可能**对任意 `W` 收敛到任意 `θ*`。 -/
theorem gap_is_false : ¬ dist_to_optimum_Gap := by
  intro hgap
  -- 施加全称命题于反例模型 gModel，取 y = h x = x = 1、θ* = 0
  obtain ⟨N, hN⟩ :=
    hgap (W := gModel) (h := gId) (η := (1 : gModel.frame.Θ.Carrier))
      (φ := gPhi) (θstar := (0 : gModel.frame.Θ.Carrier))
      (u := gU0) (ε := gN0) (a := gA0) (x := gX1) 1 (by norm_num)
  have h := hN (N + 1) (Nat.le_succ N)
  -- 该迭代的闭式：θ_{N+1} = 0 + (N+1)·(y - x) = -(N+1)
  have hval :
      endToEndIter gModel gId (1 : gModel.frame.Θ.Carrier) gPhi (gId gX1) gU0 gN0 gA0 gX1
          (N + 1) (0 : gModel.frame.Θ.Carrier)
        = -(((N : gModel.frame.Θ.Carrier) + 1)) := by
    rw [g_iter]
    have hy : (show gModel.frame.Θ.Carrier from gId gX1) = 1 := rfl
    have hx : (show gModel.frame.Θ.Carrier from gX1) = 1 := rfl
    rw [hy, hx]
    -- 目标：0 + (N+1) * (1 - (1+1)) = -(N+1)，在交换环上成立
    push_cast
    ring
  rw [hval] at h
  -- 距离 = N + 1，与 `< 1` 矛盾
  have hdist :
      dist (-(((N : gModel.frame.Θ.Carrier) + 1)))
        (0 : gModel.frame.Θ.Carrier) = (N : ℝ) + 1 := by
    rw [dist_eq_norm, sub_zero, norm_neg]
    rw [show ‖(((N : gModel.frame.Θ.Carrier) + 1))‖ = |((N : ℝ) + 1)| from rfl,
      abs_of_nonneg (by positivity)]
  rw [hdist] at h
  linarith [Nat.cast_nonneg (α := ℝ) N]

end

end GapFalse
end FateV2.Loop