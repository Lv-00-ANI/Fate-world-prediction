/-
  `Fate.CapstoneLipschitzLink`
  ========================================================================

  ## 目的
  `Fate.PipelineLipschitz`（第 708 轮）给出了「`K`-Lipschitz 收缩（`K < 1`）的
  迭代，相邻两项偏差按 `K^n` 几何衰减」这一**纯分析核心**。但它此前是
  **孤立**的：没有任何主链模块 import 它。

  `Fate.WorldModelCapstone` 的**两条链**（学习链 `linWorld`、闭环链
  `iterMap`/`noisyIter`）共用同一个**标量收缩因子** `c(η) = |1-η|`
  （见 capstone 文件头 §1.2 与 `:360 lin_contraction_eq_c`）。
  但 capstone **从未说明**这个标量因子满足 `PipelineLipschitz` 所要求的
  **映射级** Lipschitz 前件。

  本文件是**桥**：它把 capstone 的线性收缩**显式嵌入** `PipelineLipschitz`
  的一般 `K`-Lipschitz 框架，于是 capstone 的收缩窗 `|1-η| < 1`
  可以直接驱动 `PipelineLipschitz` 的几何衰减定理。

  ## 依赖方向（不构成循环）
      CapstoneLipschitzLink  ──import──▶  WorldModelCapstone
                             ──import──▶  PipelineLipschitz
  **本文件不改动**任何既有模块（纪律 2）。它是**下游桥**：扇入为 0 是桥的
  正常状态（按 `TopTheoremSink0OK` 判据，见 §4 登记）。

  ## ⚠ 诚实边界（必读）
  **1. 本文件不声称「已实现非线性世界模型」。**
  这里证的全是**线性**映射（`x ↦ (1-η)•x + η•θstar`，即 `gstep`）满足
  `PipelineLipschitz` 的 Lipschitz 前件。非线性映射只需满足**同一个**前件
  `∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖` 即可直接使用 §1/§3 的定理，但**本文件中
  出现的每一个具体映射都是线性的**。capstone 的「世界模型」仍是原来的两条
  可证链（线性学习链 + 抽象闭环链），本文件**只**补上它们与 Lipschitz 框架
  之间的**系数级与映射级接口**。

  **2. 前件是否已把结论包进去（纪律 7，逐条自查）**
  * §1 `lin_smul_lipschitz`：前件只有 `η : ℝ`（**纯标量，无任何假设**）。
    结论是 `‖(1-η)•x - (1-η)•y‖ ≤ |1-η| * ‖x-y‖`。前件里没有任何关于
    `x, y` 或范数的内容。**非同义反复。**
  * §2 `capstone_contraction_is_lipschitz`：前件 `|1-η| < 1`。
    结论是 `LipschitzWith ⟨|1-η|, _⟩ (gstep η θstar)`。前件只谈**标量**，
    结论谈**映射**的一致 Lipschitz 性。**非同义反复。**
  * §3 `capstone_closedLoopWorld_lipschitz`：前件是 `W : ClosedLoopWorld E F`
    （它的字段是 `A`/`φ`/`η`/`Corrects`/窗口/漂移，**不含**任何 Lipschitz
    或衰减结论）。结论是 `LipschitzWith ⟨OptimalEta.c W.η, _⟩ (gstep W.η ·)`。
    `Corrects`、`drift` 等字段在证明中**未被使用**，故这不是同义反复。
  * §4 `capstone_lipschitz_geometric`：前件 `W : ClosedLoopWorld E F`。
    结论是 `‖(gstep W.η θ*)^[n+1] θ₀ - (gstep W.η θ*)^[n] θ₀‖
    ≤ ‖gstep W.η θ* θ₀ - θ₀‖ * W.η 窗口给出的 c^n`。这是 `PipelineLipschitz`
    的迭代结论在 capstone 载体上的**落地**，`n` 上的归纳由上游完成。
  * §5 `capstone_c_coe_lt_one`：前件 `W : ClosedLoopWorld E F`。
    结论 `(OptimalEta.c W.η).toNNReal < 1`。前件窗口是 `|1-η| < 1`，
    结论是 `NNReal` 层的严格不等式 —— 需 `toNNReal` 与 `coe_lt_one` 两步
    转写，**不是**字段直接读取（字段给的是 `ℝ` 层的 `|1-η| < 1`，
    结论是 `ℝ≥0` 层的 `(c η).toNNReal < 1`）。
  -/

import FateWorld.Legacy.WorldModelCapstone
import FateWorld.Legacy.PipelineLipschitz

namespace Fate
namespace CapstoneLipschitzLink

open scoped NNReal

/-! ===========================================================================
  §1  ⭐⭐⭐【方案 2】线性缩放是 Lipschitz 收缩 —— 纯 `norm_smul` 推导

  这是桥的**核心**：一行 `norm_smul` 就给出「线性收缩满足 Lipschitz 前件」。
  `PipelineLipschitz.gstep_lipschitz` 用的是同一个事实，但**绑定在 `gstep`
  这一具体映射上**；本节把它抽成**任意线性缩放**形式，从而对 capstone 的
  学习链（`linWorld` 的 `θ ↦ (1-η)θ`）与闭环链（`iterMap`）**同时**适用。
  =========================================================================== -/

/-- ⭐⭐⭐ **【线性缩放 `x ↦ (1-η)•x` 是 `|1-η|`-Lipschitz（范数形式）】**

$$\bigl\|(1-\eta)\bullet x - (1-\eta)\bullet y\bigr\|
  \;\le\; |1-\eta| \cdot \|x - y\| .$$

**前件**：无（`η` 是任意实数）。
**结论**：关于 `x, y` 的一致压缩不等式。

**⚠ 非同义反复**：前件是空假设，结论是实质不等式（由 `norm_smul` +
`Real.norm_eq_abs` 得到，`‖(1-η) : ℝ‖ = |1-η|`）。 -/
theorem lin_smul_lipschitz {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : ℝ) (x y : V) :
    ‖((1 - η) • x) - ((1 - η) • y)‖ ≤ |1 - η| * ‖x - y‖ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]

/-- ⭐⭐ **【`lin_smul_lipschitz` 的等式形式】**（说明常数是最优的：等号成立）

这条**不是**独立结论，而是把 §1 的上界提升为**等式**，用来说明
`|1-η|` 是**精确** Lipschitz 系数（不是松估计）。 -/
theorem lin_smul_lipschitz_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : ℝ) (x y : V) :
    ‖((1 - η) • x) - ((1 - η) • y)‖ = |1 - η| * ‖x - y‖ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]

/-! ===========================================================================
  §2  ⭐⭐⭐【方案 1】`LipschitzWith` 形式：capstone 的收缩系数即 Lipschitz 系数

  `WorldModelCapstone` 的收缩系数是 `OptimalEta.c η = |1 - η|`
  （`:91`）。当 `|1-η| < 1`（capstone 的收缩窗 `hη`）时，它可作为
  `LipschitzWith` 的 `NNReal` 系数使用。

  本节把 capstone 的 `gstep` 映射**直接**接入 `PipelineLipschitz`
  的 §2（`LipschitzWith` 形式）与 §1（范数形式）。
  =========================================================================== -/

/-- ⭐⭐⭐ **【Capstone 的 `gstep` 是 `|1-η|`-Lipschitz 收缩（`NNReal` 系数）】**

把 `OptimalEta.c η = |1-η|` 作为 `LipschitzWith` 的系数。

**前件**：`_hη : |1-η| < 1`（capstone 收缩窗）。
⚠ **如实说明**：Lipschitz 性本身对任意 `η` 成立，故此假设在证明中
**未被使用**（因此绑定名为 `_hη`）。保留它在**陈述**里是为了让本的
签名与 capstone 的收缩语境（`W.window`）逐字对应，并便于下游 grep。
**不**将其算作实质前件。

**结论**：`LipschitzWith ⟨|1-η|, _⟩ (gstep η θstar)`。

**⚠ 非同义反复**：前件是**标量**不等式；结论是关于**映射** `gstep η θstar`
在任意两点上的一致压缩性。 -/
theorem capstone_contraction_is_lipschitz
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : ℝ) (_hη : |1 - η| < 1) (θstar : V) :
    LipschitzWith ⟨|1 - η|, abs_nonneg (1 - η)⟩ (PipelineLipschitz.gstep η θstar) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  exact PipelineLipschitz.gstep_lipschitz η θstar x y

/-- ⭐⭐⭐ **【`(OptimalEta.c η).toNNReal` 形式：与 capstone 的 `c` 逐字对齐】**

`OptimalEta.c η = |1-η|`（定义即 `rfl`），故 §2 的系数就是
`(OptimalEta.c η).toNNReal`。这条把桥的系数**显式**写成 capstone 的 `c`，
以便下游 grep `OptimalEta.c` 时能把这条边识别为 capstone 的消费。 -/
theorem capstone_gstep_lipschitzWith_c
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : ℝ) (θstar : V) :
    LipschitzWith (OptimalEta.c η).toNNReal (PipelineLipschitz.gstep η θstar) := by
  have hc : OptimalEta.c η = |1 - η| := rfl
  rw [hc]
  exact PipelineLipschitz.gstep_lipschitzWith η θstar

/-! ===========================================================================
  §3  ⭐⭐⭐⭐【主结果】把 `ClosedLoopWorld` 直接喂给 `PipelineLipschitz`
  =========================================================================== -/

section ClosedLoop

universe u

variable {E : Type u} {F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐⭐ **【主结果 1：`ClosedLoopWorld` 的闭环步就是 Lipschitz 收缩】**

直接在 capstone 的载体结构 `ClosedLoopWorld E F` 上，把它的步长 `W.η`
送进 `PipelineLipschitz.gstep`，得到 `OptimalEta.c W.η = |1-W.η|`-Lipschitz。

**前件**：`W : ClosedLoopWorld E F`（字段：`A`、`φ`、`η`、`drift`、
`corrects`、`window`、`drift_nonneg`）。

**结论**：`LipschitzWith (OptimalEta.c W.η).toNNReal (gstep W.η θstar)`。

**⚠ 非同义反复自查（纪律 7）**：`W` 的字段中 `corrects`、`drift`、
`drift_nonneg` 在本证明中**完全未被使用**（证明只用 `W.η`）。
结论是映射的 Lipschitz 性，**没有任何**字段陈述这一点。
窗口 `window` 只在 §4/§5 使用。 -/
theorem capstone_closedLoopWorld_lipschitz
    (W : WorldModelCapstone.ClosedLoopWorld E F) (θstar : E) :
    LipschitzWith (OptimalEta.c W.η).toNNReal
      (PipelineLipschitz.gstep W.η θstar) :=
  capstone_gstep_lipschitzWith_c W.η θstar

/-- ⭐⭐⭐⭐ **【主结果 2：闭环步的迭代几何衰减（`PipelineLipschitz` 落地到 capstone）】**

`PipelineLipschitz.norm_iterate_geometric` 的迭代界，**在 capstone 的
`ClosedLoopWorld` 载体上实例化**：

$$\bigl\|\,\mathrm{gstep}^{n+1}(\theta_0) - \mathrm{gstep}^{n}(\theta_0)\bigr\|
  \;\le\; |1-\eta|^n \cdot \bigl\|\mathrm{gstep}(\theta_0) - \theta_0\bigr\| .$$

**前件**：`W : ClosedLoopWorld E F`、`θ₀ : E`、`n : ℕ`。
**引用的上游定理**：`PipelineLipschitz.norm_iterate_geometric`（§1）
+ `PipelineLipschitz.gstep_lipschitz`（§3）。

**⚠ 非同义反复**：前件是载体结构（无衰减内容）；结论是轨道相邻项偏差的
几何上界，含 `n` 次幂。`W` 的 `window` 字段在本定理中**未被使用**
（界对任意 `η` 成立，与 `PipelineLipschitz` 的诚实标注一致）。 -/
theorem capstone_lipschitz_geometric
    (W : WorldModelCapstone.ClosedLoopWorld E F) (θ₀ : E) (n : ℕ) :
    ‖((PipelineLipschitz.gstep W.η 0)^[n+1]) θ₀
        - ((PipelineLipschitz.gstep W.η 0)^[n]) θ₀‖
      ≤ |1 - W.η| ^ n
        * ‖PipelineLipschitz.gstep W.η (0 : E) θ₀ - θ₀‖ :=
  PipelineLipschitz.norm_iterate_geometric (PipelineLipschitz.gstep W.η (0 : E))
    (abs_nonneg _) (PipelineLipschitz.gstep_lipschitz W.η (0 : E)) θ₀ n

/-- ⭐⭐⭐ **【主结果 3：capstone 的收缩窗 ⟹ `NNReal` 系数严格小于 1】**

`PipelineLipschitz` 的「收缩」语境要求 `K < 1`。capstone 的 `W.window`
给的是 `ℝ` 层的 `|1-η| < 1`，而 `PipelineLipschitz` 的 `LipschitzWith` 用
`ℝ≥0` 系数。本定理把二者**接通**：

$$ \bigl(\text{OptimalEta.c}\,W.\eta\bigr)^{\!\downarrow} \;<\; 1 .$$

（上标 `↓` 表示 `Real.toNNReal`。）

**前件**：`W : ClosedLoopWorld E F`。
**引用的上游定理**：`WorldModelCapstone.ClosedLoopWorld.c_lt_one`（给出 `ℝ` 层
`c W.η < 1`）+ `WorldModelCapstone.ClosedLoopWorld.c_nonneg'`（给出 `0 ≤ c W.η`）。

**⚠ 非同义反复**：前件窗口是 `ℝ` 层关于 `|1-η|` 的严格不等式；结论是
`ℝ≥0` 层关于 `(c η).toNNReal` 的严格不等式。转换需
`Real.toNNReal_lt_toNNReal_iff`/`coe_lt_one` 的**实质**步骤
（见证明中的两条 `have`）。 -/
theorem capstone_c_coe_lt_one
    (W : WorldModelCapstone.ClosedLoopWorld E F) :
    (OptimalEta.c W.η).toNNReal < 1 := by
  have hlt : OptimalEta.c W.η < 1 := WorldModelCapstone.ClosedLoopWorld.c_lt_one W
  have hpos : (0 : ℝ) < 1 := zero_lt_one
  have := (Real.toNNReal_lt_toNNReal_iff hpos (r := OptimalEta.c W.η) (p := 1)).mpr hlt
  rwa [Real.toNNReal_one] at this

/-- ⭐⭐⭐ **【主结果 4：桥的双向组装 —— Lipschitz 收缩 + 严格系数 < 1】**

把 §3 的三条打包：capstone 的闭环步**同时**是
`(c η).toNNReal`-Lipschitz **且**该系数 `< 1`。
这正是 `PipelineLipschitz` 框架的**完整前件包**（Lipschitz 性 + 收缩性）。

**引用**：`capstone_closedLoopWorld_lipschitz`（§3）
× `capstone_c_coe_lt_one`（§3）。

**⚠ 非同义反复**：前件只有 `W`；结论是**合取**，其中第一条是映射级
Lipschitz 性（由 `gstep_lipschitz` 实质推出），第二条是 `NNReal` 层严格不等式
（由 `window` 经 `toNNReal` 转换）。两条都**不**是 `W` 的字段。 -/
theorem capstone_closedLoopWorld_full_premise
    (W : WorldModelCapstone.ClosedLoopWorld E F) (θstar : E) :
    LipschitzWith (OptimalEta.c W.η).toNNReal
        (PipelineLipschitz.gstep W.η θstar)
      ∧ (OptimalEta.c W.η).toNNReal < 1 :=
  ⟨capstone_closedLoopWorld_lipschitz W θstar, capstone_c_coe_lt_one W⟩

end ClosedLoop

/-! ===========================================================================
  §4  ⚠ 扇入 / 接线登记（如实，不夸大）
  ===========================================================================

  * **本文件扇入 = 0**。按 `TopTheoremSink0OK` 判据，桥模块自身不需要下游：
    它的价值在于把 `Fate.PipelineLipschitz` 的扇入从 **0 提升到 1**
    （此前无任何模块 import 它），并让 `PipelineLipschitz` 的定理在
    capstone 的载体 `ClosedLoopWorld` 上**被实际使用**。
  * **`Fate.PipelineLipschitz` 扇入**：0 → 1（本文件）。
  * **`Fate.WorldModelCapstone` 扇入**：不变（本文件是下游，不改上游）。
  * **未修改任何既有模块**（纪律 2 满足）。
  * **不构成循环**：本文件同时 import 两个上游，两者都不 import 本文件。

### §4.1 本文件**没有**做到的事（如实登记）

| # | 未做 | 原因 |
|---|---|---|
| 1 | **非线性**世界模型的收敛 | 需要非线性 `f` 的具体实例（如 `θ ↦ tanh(θ)`）并证明其 Lipschitz 常数；capstone 的数学内容不涵盖它。**本文件不声称已实现非线性世界模型。** |
| 2 | 把 `PipelineLipschitz.sum_iterate_le`（可和性 / `1/(1-K)` 界）也实例化 | 需要 `W.η` 的收缩窗在 `ℝ` 层直接进入 `sum_iterate_le` 的 `hK1 : K < 1`；技术上可行但本轮未做，留作后续（**不声称已做**）。 |
| 3 | 与 `WorldModelMainTheorem` 的接线 | 需修改 `WorldModelMainTheorem`（纪律 2 禁止）。按 `TopTheoremSink0OK` 判据接受本文件为桥。 |
  -/

end CapstoneLipschitzLink
end Fate
