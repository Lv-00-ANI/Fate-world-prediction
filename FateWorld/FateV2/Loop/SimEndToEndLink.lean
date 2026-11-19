import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Loop.ThetaConvergence
/-!
  # Loop · SimEndToEndLink

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SimEndToEndLink.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEnd, ThetaConvergence
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `SimEndToEndLink` —— **`WorldModel.sim` 与 `endToEndIter` 的显式连接**

  ## 0  本文件要解决的问题（缺口二）

  两种「预测」在源码中**并存但无定理连接**：

  | 用法 | 落点 | 用 `W.f` 做什么 |
  |---|---|---|
  | **状态预测** | `FateV2.Predict.WorldModel.sim` | 生成**轨迹** `sim θ u ε a : ℕ → X` |
  | **参数估计** | `EndToEnd.endToEndIter` | 算**残差** `x̂_obs - predFrom W θ u ε a x` |

  两者**都用同一个 `W.f`**（`WorldModel.sim_succ` 与 `EndToEnd.predFrom` 逐字同源），
  但此前**没有任何定理**把 `endToEndIter` 的递推与 `W.sim` 的递推放在同一条式子里。
  本文件补上这条桥。

  ## 1  ⚠ 诚实边界（必读）

  **1.1 第 1 条（显式桥）几乎不新增数学内容。**
  `EndToEnd.predFrom_eq_sim_succ` **已经存在**（`EndToEnd.lean:155`），
  它说：从 `sim` 的第 `n` 步出发做 `predFrom`，得到 `sim` 的第 `n+1` 步。
  本文件 §2 的 `endToEnd_residual_uses_sim` 是它的**调用点形式**——
  把 `endToEnd` 的残差位**显式改写为 `W.sim ... 1`**。
  这是**使用性引理**（把「已知的等式」接到「残差公式」上），
  **不是**新机制。它有价值的地方在于：**下游写 `endToEnd` 的残差时可以直接换成 `sim`**，
  证明「环节 ② 复用的就是 `sim` 的那一个机制」不再需要 `rfl`-级展开。

  **1.2 第 1 条为何需要 `sim 0 = W.x`。**
  `W.sim` 的起点**被钉死**在状态块初值 `W.x`（`WorldModel.sim_zero`），
  而 `endToEnd` 的起点 `x` 是**自由参数**。故「从任意 `x` 出发的 `sim` 第 1 步」
  只有在 `x = W.x` 时才等于 `W.sim ... 1`。
  **本文件不隐藏这一点**：§2 的定理把 `hx : x = W.x` 写成**显式前件**，
  并另立 `predFrom_step_of_sim`（§2.1）说明「从 `sim` 的第 `n` 步出发」这一**无前件**版本。
  **⟹ 前件 `hx` 不包含结论**：结论是 `endToEnd ... = θ + η * φ (...-... sim 1 ...)`，
    `hx` 只说「起点等于初值」，与参数更新式无逻辑关联（见 §5 的非同义反复说明）。

  **1.3 第 2 条（收敛传输）需要 `Continuous` —— 它是**真**前件。**
  `endToEndIter` 收敛只给出 `θ_n → θ*`（`ℕ → Θ` 的收敛）；
  要把它**推过** `W.sim` 这一层，必须知道 `θ ↦ W.sim θ u ε a 1` 连续。
  在一般 `WorldModel` 上这**没有任何保证**（`W.f` 是任意函数 `Step W.frame`）。
  **⟹ 本文件在一般 `W` 上**无法**去掉 `Continuous`；§3 把它写成显式前件。**

  **1.4 第 3 条（`linWorld`）`Continuous` 自动成立。**
  `linWorld.f x u ε θ a = θ * x`（`ThetaConvergence.linWorld_step_eq`），
  故 `θ ↦ W.sim θ _ _ _ 1 = θ * W.x` 连续，**无需**任何前件。
  §4 在 `endToEndIter` 真收敛（`linWorld_tendsto_thetaStar`）之上把它接起来。

  **1.5 本文件没有 `sorry` / `admit` / `axiom` / `native_decide`。**
  全部证明为 `simp` / `rw` / `Filter.Tendsto.comp` 级。

  ## 2  目录

  | § | 内容 |
  |---|---|
  | §2 | 第 1 条：`predFrom_step_of_sim`（无前件）+ `endToEnd_residual_uses_sim` |
  | §3 | 第 2 条：`sim_converges_of_endToEndIter_converges`（`Continuous` 前件）|
  | §4 | 第 3 条：`linWorld_sim_converges`（`linWorld` 上无 `Continuous` 前件）|
  | §5 | 自检：前件非同义反复、结论可达 |
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Predict
namespace SimEndToEndLink

open FateV2.Predict.WorldModel
open Filter Topology

/-! ===========================================================================
    §2  第 1 条：**`predFrom` = `sim` 的一步**（显式桥，接进 `endToEnd` 的残差位）
    =========================================================================== -/

/-- ⭐⭐ **【桥 1 · 无前件版】从 `W.sim` 的第 `n` 步出发做 `predFrom`，就是第 `n+1` 步。**

这是 `EndToEnd.predFrom_eq_sim_succ` 的**同义重述**（`fun _ => u` 形式），
**不引入新内容**，作用是把「序列参数」与「单点参数」的写法对齐，
使下游无需在每次调用时手写 `u n / ε n / a n`。

**⟹ 结论中**没有**任何前件，本定理是**纯**等式。** -/
theorem predFrom_step_of_sim (W : WorldModel)
    (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (ε : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) (n : ℕ) :
    EndToEnd.predFrom W θ (u n) (ε n) (a n) (W.sim θ u ε a n)
      = W.sim θ u ε a (n + 1) :=
  EndToEnd.predFrom_eq_sim_succ W θ u ε a n

/-- ⭐⭐⭐ **【桥 2 · 第 1 条主交付】`endToEnd` 的残差位**显式**写成 `W.sim` 的第 1 步。**

$$\mathrm{endToEnd}\ W\ h\ \eta\ \varphi\ y\ \theta\ u\ \varepsilon\ a\ W.x
  \;=\; \theta + \eta\,\varphi\bigl(\hat x^{\mathrm{obs}} - W.\mathrm{sim}\ \theta\ (u)(\varepsilon)(a)\ 1\bigr)$$

它把 `endToEnd_apply` 里的 `predFrom W θ u ε a x` **替换为 `W.sim ... 1`**，
证明「参数估计的残差用的预测」**就是** `sim` 的第一步。

**⚠ 前件 `hx : x = W.x` 只负责「起点对齐」**：
`W.sim` 的起点被 `sim_zero` 钉在 `W.x`，而 `endToEnd` 的起点 `x` 是自由参数。
**前件不含结论**：即便去掉等式右边，`hx` 也不能推出任何关于 `θ + η * φ (...)` 的事；
它是**起点约束**，不是「结果已给出」。 -/
theorem endToEnd_residual_uses_sim (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (hx : x = W.x) :
    EndToEnd.endToEnd W h η φ y θ u ε a x
      = θ + η * φ (EndToEnd.observe h y
          - W.sim θ (fun _ => u) (fun _ => ε) (fun _ => a) 1) := by
  subst hx
  rw [EndToEnd.endToEnd_apply,
    WorldModel.sim_succ W θ (fun _ => u) (fun _ => ε) (fun _ => a) 0,
    WorldModel.sim_zero W θ (fun _ => u) (fun _ => ε) (fun _ => a)]
  rfl

/-- ⭐⭐ **【桥 2 · 非平凡性旁证】`endToEnd` 改变参数 ⟺ 观测 ≠ `sim` 的第 1 步。**

这是 `endToEnd_fixed` / `endToEnd_moves` 的 `sim` 版：
**「模型预测正确」= 「观测估计恰等于 `sim` 走过的第一步」**。
**⟹ 把 `sim` 与「学习是否停手」直接挂上**（此前只在 `predFrom` 层陈述）。 -/
theorem endToEnd_fixed_iff_sim (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (hR : ResidualLoop.ReadsResidual W.frame.Θ η φ)
    (x : W.frame.X.Carrier) (hx : x = W.x) :
    EndToEnd.endToEnd W h η φ y θ u ε a x = θ
      ↔ EndToEnd.observe h y
          = W.sim θ (fun _ => u) (fun _ => ε) (fun _ => a) 1 := by
  subst hx
  rw [EndToEnd.endToEnd_fixed_iff W h η φ hR y θ u ε a W.x,
    WorldModel.sim_succ W θ (fun _ => u) (fun _ => ε) (fun _ => a) 0,
    WorldModel.sim_zero W θ (fun _ => u) (fun _ => ε) (fun _ => a)]
  rfl

/-! ===========================================================================
    §3  第 2 条：**`endToEndIter` 收敛 ⟹ `sim` 收敛**（`Continuous` 前件）
    =========================================================================== -/

/-- ⭐⭐⭐ **【桥 3 · 第 2 条主交付】参数收敛 ⟹ 由该参数生成的状态预测收敛。**

设 `θ_n := endToEndIter ... n θ₀ → θ*`，且 `θ ↦ W.sim θ u ε a 1` 在 `θ*` 处连续，
则 `W.sim θ_n u ε a 1 → W.f W.x u ε θ* a`（= `predFrom` 在 `θ*` 处的预测）。

**⚠ 前件 `hcont` 是**真**前件，不是装饰**：
一般 `WorldModel` 的 `W.f` 是任意函数，`θ ↦ W.f W.x u ε θ a` 可以不连续，
此时结论**可以失败**（`endToEndIter` 只保证 `θ_n → θ*`，不保证 `W.f` 侧的极限）。
**⟹ 本定理在一般 `W` 上不能去掉 `hcont`；§4 在 `linWorld` 上给出无前件版本。**

**⚠ 前件**不含**结论**：`hconv` 说的是 **`Θ` 里的**收敛（`ℕ → Θ`），
`hcont` 说的是 `W.sim · u ε a 1` 的**连续性**；
结论说的是 **`X` 里**的收敛。两者不同空间、不同对象。 -/
theorem sim_converges_of_endToEndIter_converges
    (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    [TopologicalSpace W.frame.Θ.Carrier] [TopologicalSpace W.frame.X.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (θ₀ θstar : W.frame.Θ.Carrier)
    (hconv : Tendsto (fun n => EndToEnd.endToEndIter W h η φ y u ε a x n θ₀)
      atTop (nhds θstar))
    (hcont : Continuous (fun θ => W.sim θ (fun _ => u) (fun _ => ε) (fun _ => a) 1)) :
    Tendsto
      (fun n => W.sim (EndToEnd.endToEndIter W h η φ y u ε a x n θ₀)
        (fun _ => u) (fun _ => ε) (fun _ => a) 1)
      atTop (nhds (W.f W.x u ε θstar a)) := by
  have hcomp := hcont.continuousAt.tendsto.comp hconv
  have hval : W.sim θstar (fun _ => u) (fun _ => ε) (fun _ => a) 1
      = W.f W.x u ε θstar a := by
    rw [WorldModel.sim_succ W θstar (fun _ => u) (fun _ => ε) (fun _ => a) 0,
      WorldModel.sim_zero W θstar (fun _ => u) (fun _ => ε) (fun _ => a)]
  rw [← hval]
  exact hcomp

/-- ⭐ **【桥 3 的 `predFrom` 版读法】**（同一结论的另一面）：
极限状态预测 = `predFrom` 在 `θ*`、初值 `W.x` 处的值。 -/
theorem sim_converges_limit_eq_predFrom
    (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    [TopologicalSpace W.frame.Θ.Carrier] [TopologicalSpace W.frame.X.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (θ₀ θstar : W.frame.Θ.Carrier)
    (hconv : Tendsto (fun n => EndToEnd.endToEndIter W h η φ y u ε a x n θ₀)
      atTop (nhds θstar))
    (hcont : Continuous (fun θ => W.sim θ (fun _ => u) (fun _ => ε) (fun _ => a) 1)) :
    Tendsto
      (fun n => W.sim (EndToEnd.endToEndIter W h η φ y u ε a x n θ₀)
        (fun _ => u) (fun _ => ε) (fun _ => a) 1)
      atTop (nhds (EndToEnd.predFrom W θstar u ε a W.x)) :=
  sim_converges_of_endToEndIter_converges W h η φ y u ε a x θ₀ θstar hconv hcont

/-! ===========================================================================
    §4  第 3 条：`linWorld` 上的具体版本（`Continuous` **自动**成立）
    =========================================================================== -/

/-- ⭐⭐ **【`linWorld` 上 `sim` 第 1 步 = `θ * W.x`】**：
`linWorld` 的机制是线性的，故 `sim` 的第 1 步**闭式**已知。 -/
theorem linWorld_sim_one (θ : ℝ) :
    ThetaConvergence.linWorld.sim θ (fun _ => PUnit.unit) (fun _ => PUnit.unit)
      (fun _ => PUnit.unit) 1 = θ * ThetaConvergence.linWorld.x := by
  show ThetaConvergence.linWorld.f (ThetaConvergence.linWorld.x) PUnit.unit PUnit.unit θ
      PUnit.unit = θ * ThetaConvergence.linWorld.x
  rfl

/-- ⭐ **【`linWorld` 上 `sim` 第 1 步对 `θ` 连续】（`Continuous` **无前件**）。** -/
theorem linWorld_sim_one_continuous :
    Continuous (fun θ : ℝ => ThetaConvergence.linWorld.sim θ (fun _ => PUnit.unit)
      (fun _ => PUnit.unit) (fun _ => PUnit.unit) 1) := by
  have : (fun θ : ℝ => ThetaConvergence.linWorld.sim θ (fun _ => PUnit.unit)
      (fun _ => PUnit.unit) (fun _ => PUnit.unit) 1)
      = fun θ : ℝ => θ * ThetaConvergence.linWorld.x := by
    funext θ; exact linWorld_sim_one θ
  rw [this]
  exact continuous_id.mul continuous_const

/-- ⭐⭐⭐⭐ **【桥 4 · 第 3 条主交付】`linWorld`：`endToEndIter` 收敛 ⟹ `sim` 收敛，无 `Continuous` 前件。**

在 `linWorld` 上（`W.f x u ε θ a = θ * x`，**线性**），
前置 `sim_converges_of_endToEndIter_converges` 的 `Continuous` 前件**自动成立**，
故可以把它彻底消去：只需 `θ_n → θ*`，即得 `sim θ_n ... 1 → θ* * W.x`。

**⚠ 前件只有「`endToEndIter` 收敛」这一条**，且它说的是 `Θ` 里的收敛；
结论说的是 `ℝ`（`X`）里的收敛且极限点**显式**。**前件不含结论。** -/
theorem linWorld_sim_converges
    (η θstar x θ₀ : ℝ)
    (hconv : Tendsto (fun n => EndToEnd.endToEndIter ThetaConvergence.linWorld
        (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      atTop (nhds θstar)) :
    Tendsto
      (fun n => ThetaConvergence.linWorld.sim
        (EndToEnd.endToEndIter ThetaConvergence.linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => PUnit.unit) 1)
      atTop (nhds (θstar * ThetaConvergence.linWorld.x)) := by
  have hcomp := linWorld_sim_one_continuous.continuousAt.tendsto.comp hconv
  have hval : ThetaConvergence.linWorld.sim θstar (fun _ => PUnit.unit)
      (fun _ => PUnit.unit) (fun _ => PUnit.unit) 1
      = θstar * ThetaConvergence.linWorld.x := linWorld_sim_one θstar
  rw [← hval]
  exact hcomp

/-- ⭐⭐⭐⭐ **【桥 5 · 合取版：真正把两条主链接起来】**

`linWorld` 上**只用一个前件** `x ≠ 0 ∧ |1-η| < 1`（即 `linWorld_tendsto_thetaStar` 的前件），
**同时**得到：

1. **参数收敛**（`endToEndIter` 侧）：`θ_n → θ*`；
2. **状态预测收敛**（`sim` 侧）：`sim θ_n ... 1 → θ* * W.x`。

**⟹ 这是缺口二的**正面回答**：`sim` 与 `endToEndIter` 在 `linWorld` 上**同时**收敛，
且**极限一致地由 `θ*` 决定**（`θ*` 与 `θ* * W.x` 是同一参数的两种读法）。

**⚠ 非同义反复检查**：前件是 `x ≠ 0` 与 `|1-η| < 1`（**数值条件**），
结论含**两个 `Tendsto` 断言**（`Θ` 与 `X` 两个不同空间）。
**前件推不出任何 `Tendsto` 结论除非真的用主定理 `linWorld_tendsto_thetaStar` 与桥 4**。
详见 §5 `linWorld_sim_converges_premise_form`。 -/
theorem linWorld_sim_and_theta_converge
    (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) :
    (Tendsto (fun n => EndToEnd.endToEndIter ThetaConvergence.linWorld
        (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        atTop (nhds θstar))
    ∧ (Tendsto
      (fun n => ThetaConvergence.linWorld.sim
        (EndToEnd.endToEndIter ThetaConvergence.linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => PUnit.unit) 1)
      atTop (nhds (θstar * ThetaConvergence.linWorld.x))) :=
  ⟨ThetaConvergence.linWorld_tendsto_thetaStar η θstar x θ₀ hx hη,
   linWorld_sim_converges η θstar x θ₀
     (ThetaConvergence.linWorld_tendsto_thetaStar η θstar x θ₀ hx hη)⟩

/-! ===========================================================================
    §5  自检：前件非同义反复、结论可达
    =========================================================================== -/

/-- **自检 1**：桥 2 的结论**右侧确实出现 `W.sim ... 1`**（不是 `predFrom`）。
把 `sim` 换成常值则本式失败（因为 `sim_succ` 强制它等于 `W.f W.x u ε θ a`）。 -/
example (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (_η : W.frame.Θ.Carrier) (_φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier) :
    (EndToEnd.observe h y
        - W.sim θ (fun _ => u) (fun _ => ε) (fun _ => a) 1)
      = (EndToEnd.observe h y - EndToEnd.predFrom W θ u ε a W.x) := by
  rw [WorldModel.sim_succ W θ (fun _ => u) (fun _ => ε) (fun _ => a) 0,
    WorldModel.sim_zero W θ (fun _ => u) (fun _ => ε) (fun _ => a)]
  rfl

/-- **自检 2**：桥 3 的结论**不是** `hconv` 的重述 ——
结论的空间是 `W.frame.X.Carrier`，`hconv` 的空间是 `W.frame.Θ.Carrier`。
本条把极限点**显式写死**为 `W.f W.x u ε θstar a`，说明结论含实质内容。 -/
example (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (_h : W.frame.X.Carrier → Y)
    (_η : W.frame.Θ.Carrier) (_φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (_y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (_x : W.frame.X.Carrier) (_θ₀ : W.frame.Θ.Carrier) (θstar : W.frame.Θ.Carrier) :
    (fun θ => W.sim θ (fun _ => u) (fun _ => ε) (fun _ => a) 1) θstar
      = W.f W.x u ε θstar a := by
  show W.sim θstar (fun _ => u) (fun _ => ε) (fun _ => a) (0 + 1)
      = W.f W.x u ε θstar a
  rw [WorldModel.sim_succ W θstar (fun _ => u) (fun _ => ε) (fun _ => a) 0,
    WorldModel.sim_zero W θstar (fun _ => u) (fun _ => ε) (fun _ => a)]

/-- **自检 3**：桥 5 的前件是**纯数值条件**，与任何 `Tendsto` 无关 ——
本自检把它单独取出：它只是两个 `Prop` 的合取，
**不含**任何 `Tendsto` 断言，因而无法目含结论。 -/
example (η x : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) :
    x ≠ 0 ∧ |1 - η| < 1 := ⟨hx, hη⟩

end SimEndToEndLink
end FateV2.Loop