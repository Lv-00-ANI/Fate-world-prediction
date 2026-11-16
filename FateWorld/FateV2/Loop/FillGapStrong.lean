import FateWorld.FateV2.Loop.FillGap
import FateWorld.FateV2.Loop.EndToEndBoundFixed
/-!
  # Loop · FillGapStrong

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FillGapStrong.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FillGap, EndToEndBoundFixed
  - 补充 open 域：FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `FillGapStrong` —— 把 `endToEnd_distance_to_optimum` 的 `hfix` 前件
      换成**可验证**的 `hpred` 前件（第 59 轮，承 `Fate.FillGap`）

  ## 0.1 背景（审计的纠正）

  `Fate/EndToEndBound.lean` §8 把 `dist_to_optimum_Gap` 登记为「证不出」，并给出
  三条理由。审计指出其**第 2 条是误读**：它把 `endToEnd_step_diff` 说的
  「**不同 `y`** 的差是常数」读成「**同一条轨迹**不收敛」。
  这两件事不同：`endToEnd_step_diff` 比较的是**两条平行轨迹**
  （同一个 `θ`、不同的观测），它对「同一条迭代轨迹是否停住」**什么都没说**。

  主控已在 `Fate/FillGap.lean` 证明
  `fixed_iff_phi_resid_zero`（不动点 ⟺ 残差经 `φ` 为零）与
  `fixed_of_predicts_exactly`（精确命中 ⟹ 不动点），
  把 `endToEnd_distance_to_optimum` 的 `hfix` 前件换成**可证的** `hpred`。

  ## 0.2 ⚠ 依赖选择：为什么 import `EndToEndBoundFixed` 而不是 `EndToEndBound`

  `Fate/EndToEndBound.lean` **当前不可编译**（`lake build` 失败、无 `.olean`），
  实测其 §5/§7 的自检段有 3 处 `rewrite` 失败
  （`rWorldModel` 上 `X.Carrier` / `Θ.Carrier` 投影路径不同所致，属**既有**问题，
  本文件**不修**、也**不改**该文件）。
  `Fate/EndToEndBoundFixed.lean` 是同一内容**可编译**的版本，
  其中 `endToEnd_error_bound_of_noise` / `endToEnd_distance_to_optimum`
  与原文件**逐字相同**（仅 `PhiBound` 落在 `Fate.EndToEndBoundFixed` 命名空间）。
  故本文件对 `Fate.EndToEndBoundFixed` 做**同一件事**：把 `hfix` 换成 `hpred`。

  ## 0.3 本文件证明什么

  `Fate.EndToEndBoundFixed.endToEnd_distance_to_optimum` 把
  `hfix : endToEnd W h η φ (h xt) θstar u ε a x = θstar`
  当作**前件**。本文件把它换成**可验证的代数条件**

  > `hpred : predFrom W θstar u ε a x = observe h (h xt)`

  （「在 `θstar` 处，规则预测恰好命中无噪声观测的估计」——
  「`θstar` 已把无噪声数据拟合到位」的**可判定**形式），
  并证明**同一条界**仍然成立，**不需要** `hfix`。

  ## 0.4 定理清单

  | # | 定理 | 内容 |
  |---|---|---|
  | 1 | `endToEnd_eq_self_of_hpred` | `hpred` ⟹ `endToEnd` 在 `θstar` 处不动 |
  | 2 | `hpred_iff_fixed` | `η ≠ 0`、`φ` 单射时：`hpred` ⟺ 不动（**双向**） |
  | 3 | `distance_to_optimum_of_predicts_exactly` | ⭐⭐⭐ **主结论**：`hpred` ⟹ 界，**无 `hfix`** |
  | 4 | `noiseless_step_of_hpred` | ⭐⭐ `hpred` ⟹ *无噪声*一步**恰为** `θstar` |
  | 5 | `iter_stays_at_optimum_of_hpred` | ⭐⭐ `hpred` ⟹ **任意**多步迭代停在 `θstar` |
  | 6 | `gap_conclusion_of_hpred` | ⭐⭐⭐ `dist_to_optimum_Gap` 的**结论形状**在 `hpred` 下成立（`N = 0`） |
  | 7 | `gap_requires_hit` | ⭐⭐ 无 `hpred` 时全称形式**假**（引用 `gap_is_false`） |

  ## 0.5 ⚠ 诚实边界（必读）

  **5.1 `hpred` **不是**同义反复 —— 前件与结论涉及的量集不相交。**
  `hpred` 是**状态空间**里的一个**等式**：`predFrom W θstar u ε a x = observe h (h xt)`。
  定理 3 的结论是**参数空间**里的一个**不等式**：
  `dist (endToEnd W h η φ (h xt + ηn) θstar u ε a x) θstar ≤ ‖η‖ * C * (L * ‖ηn‖)`。
  `hpred` 中**不出现**：`ηn`、`dist`、`‖·‖`、`C`、`L`、`endToEnd`、`endToEndIter`。
  结论中**不出现**：`predFrom`、`observe`、`h xt` 的相等性。
  故结论**不被**前件包含。（第 8 条纪律的检查：逐个数过的。）

  **5.2 `hpred` 是**真前件**，不可删。**
  定理 2 证明在 `η ≠ 0`、`φ` 单射时 `hpred` **恰好等价于** `hfix`
  —— 它**不多不少**地替换了 `hfix`。但 `hpred` **可验证**（一个等式），
  `hfix` 不可直接验证（是复合算子 `endToEnd` 的等式）。

  **5.3 定理 6 **不是** `dist_to_optimum_Gap` 本身 —— 后者**已被证伪**。**
  `Fate.EndToEndBoundFixed.lean` §9 的 `gap_is_false` **证明**
  `¬ dist_to_optimum_Gap`（反例 `dModel`：一步预测恒为 `1`，`θ_k = -k` 发散）。
  故 §8 所谓「缺口」**不是**「未证但可能真」，而是**错题**：无任何命中条件的
  全称形式**假**。定理 6 因此在**唯一能成立的形式**上给出正面结果：
  **给定精确解 `θstar`（`hpred`）后**，该 `Prop` 的**结论形状**
  `∀ εtol > 0, ∃ N, ∀ k ≥ N, dist < εtol` 成立，取 `N = 0`。
  定理 7 显式登记「`hpred` 不可省」。

  **5.4 定理 5/6 的实质内容是真的，不是空转。**
  `hpred` ⟹ `endToEnd` 不动（定理 1，用 `Fate.EndToEnd.endToEnd_fixed`），
  再由 `Fate.EndToEnd.endToEndIter_fixed` 的**归纳**传导到**任意**步数。
  真的用了 `endToEnd_fixed` 与一条归纳定理；**没有**把结论写进前件。
  **⚠ 但这是「收敛」的**退化情形**：误差从第 0 步就是 `0`。
  它**不**证明「非零误差衰减」—— 后者仍需学习率调度或 Lyapunov 势
  （`Fate/RealConvergence.lean` 方向），**本文件不涉及，不声称**。

  ## 0.6 纪律

  零 `sorry` / 零 `admit` / 零 `axiom`；**本文件不改动任何既有模块**。
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Modeling
open FateV2.Predict
namespace FillGapStrong

open FateV2.Loop.EndToEnd FateV2.Loop.EndToEndBoundFixed FateV2.Modeling.RA14Strong

universe v

noncomputable section

/-! ===========================================================================
    §1  `hpred` ⟹ 不动：桥接（承 `Fate.EndToEnd.endToEnd_fixed`）
    =========================================================================== -/

/-- ⭐⭐ **【桥 1】`hpred` ⟹ `endToEnd` 在 `θ` 处不动。**

`hpred : predFrom W θ u ε a x = observe h y` 正是
`Fate.EndToEnd.endToEnd_fixed` 的前件 `observe h y = predFrom ...` 的**反写**。

**⚠ 本引理**不需要** `η ≠ 0`、不需要 `φ` 单射、不需要 `NoZeroDivisors`**：
`endToEnd_fixed` 是**定义性**的（残差为零 ⟹ 写回为零），
这比 `Fate.FillGap.fixed_of_predicts_exactly`（需单射）**更宽**，
故本文件主定理走这条路。 -/
theorem endToEnd_eq_self_of_hpred (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hpred : FateV2.Loop.EndToEnd.predFrom W θ u ε a x = FateV2.Loop.EndToEnd.observe h y) :
    FateV2.Loop.EndToEnd.endToEnd W h η φ y θ u ε a x = θ :=
  FateV2.Loop.EndToEnd.endToEnd_fixed W h η φ y θ u ε a x hpred.symm

/-- ⭐⭐ **【桥 2】`η ≠ 0` 且 `φ` 单射时：`hpred` ⟺ 不动点。**

`⟸` 用 `Fate.FillGap.fixed_of_predicts_exactly`；
`⟹` 用 `Fate.FillGap.fixed_iff_phi_resid_zero`（不动 ⟹ 残差经 `φ` 为零）+ 单射。

**⚠ 与主定理的语境差异**：`Fate.FillGap` 的两条核心定理需要 `Ring` + `NoZeroDivisors`，
与主定理用的 `SeminormedRing` 不并存（instance diamond，见 `EndToEndBoundFixed` §3.4 同款说明），
故本引理在 `Ring` 语境下**单独**陈述，**不**用于主定理 —— 主定理只需单向（桥 1）。 -/
theorem hpred_iff_fixed (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] [NoZeroDivisors W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (hφ : Function.Injective φ) (hη : η ≠ 0)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    FateV2.Loop.EndToEnd.endToEnd W h η φ y θ u ε a x = θ
      ↔ FateV2.Loop.EndToEnd.predFrom W θ u ε a x = FateV2.Loop.EndToEnd.observe h y := by
  constructor
  · intro hfix
    rw [Fate.FillGap.fixed_iff_phi_resid_zero W h η φ y θ u ε a x hη] at hfix
    have hz : FateV2.Loop.EndToEnd.observe h y - FateV2.Loop.EndToEnd.predFrom W θ u ε a x = 0 :=
      hφ (by rw [hfix, map_zero])
    exact (sub_eq_zero.mp hz).symm
  · intro hpred
    exact Fate.FillGap.fixed_of_predicts_exactly W h η φ hφ y θ u ε a x hη hpred

/-! ===========================================================================
    §2  ⭐⭐⭐ **主结论**：`hfix` → `hpred`
    =========================================================================== -/

variable (W : WorldModel) [SeminormedAddCommGroup W.frame.X.Carrier]
  [SeminormedRing W.frame.Θ.Carrier]

/-- ⭐⭐⭐⭐ **【主结论】**：`θ*` 的**预测精确命中无噪声观测** ⟹ 离最优的界。

**前提**（与 `endToEnd_distance_to_optimum` **逐字相同**，除最后一条）：

| 前提 | 内容 |
|---|---|
| `hinj` | `h : X → X` 单射 |
| `hL`, `hLI` | `0 < L`，`h` 为 `L`-Lipschitz 可逆 |
| `hx'` | `h x' = h xt + ηn`（噪声观测的原像存在） |
| `hC`, `hφ` | `0 ≤ C`，`PhiBound φ C` |
| **`hpred`** | **`predFrom W θstar u ε a x = observe h (h xt)`** |
| 取代 `hfix` | ~~`endToEnd W h η φ (h xt) θstar u ε a x = θstar`~~ |

**结论**：

$$\operatorname{dist}\bigl(\mathrm{endToEnd}\,(h\,xt+\eta_n)\,\theta^*\bigr)\theta^*
  \;\le\; \|\eta\|\cdot C\cdot L\cdot\|\eta_n\| .$$

**⭐ 相对原定理的实质改进**：`hfix` 是**复合算子** `endToEnd` 的等式（不可直接检验）；
`hpred` 是**两个原始原子** `predFrom`、`observe` 之间的等式（可直接检验）。
定理 2 证明非退化情形下两者**等价**，故**没有**削弱结论，只**换了入口**。 -/
theorem distance_to_optimum_of_predicts_exactly
    (h : W.frame.X.Carrier → W.frame.X.Carrier) (hinj : Function.Injective h)
    (L : ℝ) (hL : 0 < L) (hLI : LipschitzInvertibleOn h L)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (C : ℝ) (hC : 0 ≤ C) (hφ : PhiBound φ C)
    (xt x' : W.frame.X.Carrier) (ηn : W.frame.X.Carrier)
    (hx' : h x' = h xt + ηn)
    (θstar : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hpred : FateV2.Loop.EndToEnd.predFrom W θstar u ε a x = FateV2.Loop.EndToEnd.observe h (h xt)) :
    dist (FateV2.Loop.EndToEnd.endToEnd W h η φ (h xt + ηn) θstar u ε a x) θstar
      ≤ ‖η‖ * C * (L * ‖ηn‖) :=
  FateV2.Loop.EndToEndBoundFixed.endToEnd_distance_to_optimum W h hinj L hL hLI η φ C hC hφ
    xt x' ηn hx' θstar u ε a x
    (endToEnd_eq_self_of_hpred W h η φ (h xt) θstar u ε a x hpred)

/-- ⭐⭐ **【主结论的精确形态】**：`hpred` ⟹ **无噪声**一步把 `θstar` **恰好**留在 `θstar`。

这是定理 3 中 `hfix` 得以消去的**直接原因**，
也是「`hpred` 真的蕴含不动」的独立见证（不经过 `dist`、不涉及界常数 `C`、`L`）。 -/
theorem noiseless_step_of_hpred
    (h : W.frame.X.Carrier → W.frame.X.Carrier)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (xt : W.frame.X.Carrier)
    (θstar : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hpred : FateV2.Loop.EndToEnd.predFrom W θstar u ε a x = FateV2.Loop.EndToEnd.observe h (h xt)) :
    FateV2.Loop.EndToEnd.endToEnd W h η φ (h xt) θstar u ε a x = θstar :=
  endToEnd_eq_self_of_hpred W h η φ (h xt) θstar u ε a x hpred

/-! ===========================================================================
    §3  ⭐⭐ **多步**：`hpred` ⟹ 迭代**停在** `θstar`
    =========================================================================== -/

/-- ⭐⭐ **【多步 1】**：`hpred` ⟹ **任意** `n` 步闭环迭代都停在 `θstar`。

用 `Fate.EndToEnd.endToEndIter_fixed`（**归纳**：一步不动 ⟹ 步步不动）。
**⚠ 这是「收敛」的**退化情形**：误差从第 0 步起就是 `0`，
故它**不**证明「非零误差衰减」——那仍需学习率调度或 Lyapunov 结构（见 §0.5 5.4）。 -/
theorem iter_stays_at_optimum_of_hpred
    (h : W.frame.X.Carrier → W.frame.X.Carrier)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (xt : W.frame.X.Carrier)
    (θstar : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hpred : FateV2.Loop.EndToEnd.predFrom W θstar u ε a x = FateV2.Loop.EndToEnd.observe h (h xt)) :
    ∀ n : ℕ,
      FateV2.Loop.EndToEnd.endToEndIter W h η φ (h xt) u ε a x n θstar = θstar :=
  FateV2.Loop.EndToEnd.endToEndIter_fixed W h η φ (h xt) u ε a x θstar
    (endToEnd_eq_self_of_hpred W h η φ (h xt) θstar u ε a x hpred)

/-- ⭐⭐⭐ **【多步 2：`dist_to_optimum_Gap` 的结论形状】**：

在 `hpred` 之下，§8 的 `dist_to_optimum_Gap` 所要求的**结论形状**

> `∀ εtol > 0, ∃ N, ∀ k ≥ N, dist (endToEndIter … k θstar) θstar < εtol`

**成立**（取 `N = 0`：所有步的距离都是 `0`）。

**⚠ 诚实标注（三重）**：
1. 这是**实例形式**（`W`、`θstar`、`hpred` 给定时），**不是** §8 那条
   **无命中条件的全称** `Prop` —— 后者已被
   `Fate.EndToEndBoundFixed.gap_is_false` **证伪**（定理 7）；
2. 它证明「**精确解**给出后闭环**不漂移**」，**不是**「从任意初值收敛」；
3. 因此它是 §8 那个「缺口」在**唯一能成立的形式**上的正面回答 ——
   缺的**不是**证明技巧，而是 `hpred` 这个结构条件（发明者必须提供）。 -/
theorem gap_conclusion_of_hpred
    (h : W.frame.X.Carrier → W.frame.X.Carrier)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (xt : W.frame.X.Carrier)
    (θstar : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hpred : FateV2.Loop.EndToEnd.predFrom W θstar u ε a x = FateV2.Loop.EndToEnd.observe h (h xt)) :
    ∀ εtol : ℝ, 0 < εtol → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      dist (FateV2.Loop.EndToEnd.endToEndIter W h η φ (h xt) u ε a x k θstar) θstar < εtol := by
  intro εtol hε
  refine ⟨0, fun k _ => ?_⟩
  rw [iter_stays_at_optimum_of_hpred W h η φ xt θstar u ε a x hpred k, dist_self]
  exact hε

/-! ===========================================================================
    §4  ⚠ **`hpred` 不可省**：无命中条件的全称形式**假**
    =========================================================================== -/

/-- ⭐⭐ **【`hpred` 不可省】**：`dist_to_optimum_Gap` 的**全称形式为假**。

直接引用 `Fate.EndToEndBoundFixed.gap_is_false`（反例 `dModel`：
一步预测恒为 `1`，`θ_k = θ - k` 发散）。

**⟹ 本文件的意义**：§8 的「缺口」**不是**「未证但可能真」，而是**错题**
（去掉命中条件后为假）。故本文件走**唯一正确**的路线：
**保留可验证的命中条件 `hpred`**，把不可验证的 `hfix` 换成它。 -/
theorem gap_requires_hit : ¬ FateV2.Loop.EndToEndBoundFixed.dist_to_optimum_Gap :=
  FateV2.Loop.EndToEndBoundFixed.gap_is_false

end

end FillGapStrong
end FateV2.Loop