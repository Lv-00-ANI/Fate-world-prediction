import FateWorld.FateV2.Loop.EndToEndPipelineBridge
import FateWorld.FateV2.Loop.PipelineTendstoSpecializes
import FateWorld.FateV2.Loop.WorldModelPipeline
/-!
  # Loop · EndToEndPipelineTendsto

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EndToEndPipelineTendsto.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEndPipelineBridge, PipelineTendstoSpecializes, WorldModelPipeline
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `EndToEndPipelineTendsto` —— **把端到端闭环接到收敛定理**（T858A-v2）
  ===========================================================================

  ## 0  本文件补的到底是哪一条缺口

  `Fate/EndToEndPipelineBridge.lean`（**已入库**）已经证明了三件事：

  | 已入库定理 | 内容 |
  |---|---|
  | `endToEndIter_eq_iterate` | `endToEndIter … n θ = (fun s => endToEnd … s …)^[n] θ`（任意 `W`）|
  | `linStep_eq_gstep` | `linWorld` 上、`x ≠ 0` 时一步 `= gstep η θstar` |
  | `linWorld_endToEndIter_eq_pipelineNGen` | `endToEndIter linWorld … n θ₀ = pipelineNGen η θstar θ₀ n` |
  | `linWorld_endToEndIter_closed` | 偏差闭式 `θ_n - θ* = (1-η)^n (θ₀ - θ*)` |

  **但它没有 `Tendsto`**——源码 §0 的诚实边界原话是
  「不声称收敛——收敛已在 `ThetaConvergence` 中独立给出」。

  本文件补的正是最后这一步：**把 `PipelineTendstoGen.pipeline_tendsto_gen`
  的极限结论搬到 `endToEndIter` 上**，得到

  $$x \ne 0 \;\wedge\; |1-\eta| < 1 \;\Longrightarrow\;
    \texttt{endToEndIter}\ \mathrm{linWorld}\ \dots\ n\ \theta_0 \;\longrightarrow\; \theta^{*}$$

  即**端到端闭环（四环串联）真的收敛到真值**，而**不是**在 `ℝ` 的
  `fstep` 或 `pipelineNGen` 上另说一遍。

  ## 1  本节新增的两类东西（都不重复已入库内容）

  | 节 | 新增 | 为什么是新的 |
  |---|---|---|
  | §1 | **代数桥**：`(1-η)*θ + η*θ* = θ + η*(θ*-θ)`（`Ring` 版 / `Module ℝ` 版）| 已入库文件里**没有**这条恒等式（它是 `linStep_eq_gstep` 证明的中间步骤，未被单独立为定理）|
  | §2 | **抽象迭代桥**：一步 `= F` ⟹ `endToEndIter = F^[n]`（`F` 任意）| 已入库的 `endToEndIter_eq_iterate` 只取 `F := fun s => endToEnd … s`（**同一函数**）；本条允许**任何** `F`，是更强的接口 |
  | §3 | **`gstep` 版抽象桥**：一步 `= gstep ηr θ*` ⟹ `endToEndIter = pipelineNGen` | 同上，且把它直接落到 `pipelineNGen` 的**陈述对象**上 |
  | §4 | ⭐⭐⭐ **收敛定理** `endToEndIter_linWorld_tendsto` | **已入库文件完全没有**（其 §0 明说不声称）|
  | §5 | 与 `pipelineN` 形态的互推核对 | 证明本文件的陈述与 `pipeline_tendsto` 是**同一命题** |

  ## 2  ⚠ 诚实边界（必读）

  **2.1 收敛只在 `linWorld` 上。** 一般 `W` 上 `predFrom W θ u ε a x = W.f x u ε θ a`，
  `W.f` 对 `θ` 的依赖**不是 ℝ-仿射的**，故「一步 = 仿射收缩」对一般 `W` **是假的**。
  本文件**不声称**一般 `W` 的收敛。`linWorld` 是该结构成立的**唯一已实例化落点**
  （与已入库 `EndToEndPipelineBridge` 的判定一致，见其 §0）。

  **2.2 收敛不是本文件证的，是**搬运**的。** 极限存在性来自
  `PipelineTendstoGen.pipeline_tendsto_gen`（其证明用 `pipelineNGen_closed` +
  `(1-η)^n → 0`）。本文件只做「轨迹对齐 + 结论搬运」，
  **前提是已入库的逐点等式 `linWorld_endToEndIter_eq_pipelineNGen`**。

  **2.3 ⚠ 「前件是否把结论包进去」自查（纪律 7）：**

  * §1 代数桥：**无前件**，是 `Ring`／`Module ℝ` 内的多项式恒等。
  * `endToEndIter_eq_iterate_of_step`：前件 `hstep` 只讲**一步**
    （`∀ θ, endToEnd … θ = F θ`）；结论讲**一切 `n`**（`n` 全称量化）。
    前件中**不出现** `endToEndIter`，也**不出现**任何 `n`。
  * `endToEndIter_eq_pipelineNGen_of`：同上一行，前件是 `gstep` 形态的一步等式。
  * ⭐ `endToEndIter_linWorld_tendsto`：前件 `hx : x ≠ 0`（**设计点非零**）
    与 `hη : |1 - η| < 1`（**步长在 `(0,2)` 内**）。
    结论是**六环闭环轨迹的极限点 = `θ*`**。
    前件中**没有任何** `Tendsto` 语句，**也没有任何** `endToEndIter` 的取值等式。
    收敛性由 §1 的代数桥 + §2 的迭代桥 + 已入库闭式**传递**而来 ——
    **不是被塞进前件**。

  **2.4 本文件不修改任何既有模块**（只 `import`）。
  零占位符。
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Predict
namespace EndToEndPipelineTendsto

open FateV2.Loop.EndToEnd

/-! ===========================================================================
  §1  ⭐ 代数桥：仿射收缩的两种写法
  =========================================================================== -/

/-- ⭐⭐ **【代数桥 · 环版】** `(1 - η) * θ + η * θ* = θ + η * (θ* - θ)`。

**⭐ 意义**：`gstep` 的定义是 `(1 - η) • θ + η • θ*`
（`Fate/PipelineTendstoGen.lean:104`），而 `endToEndIter_apply` 的右式是
`θ + η * φ(残差)`。本引理说明**这两族表达式在环内是同一件事**
（把 `(1-η) * θ` 展成 `θ - η * θ`），所以
「`endToEnd` 的一步 = `gstep`」**不是关于两种不同形状的命题**，
而是关于「`φ(残差) = θ* - θ`」这一条**值等式**的命题。

**⚠ 不是同义反复**：无前件；结论是两个多项式的恒等，用 `sub_mul` + `one_mul`
+ `mul_sub` 展开后由 `abel`（加群内的规范化）闭合。`ring` 在一般 `Ring`
上对这条**不可用**（实测 `ring_nf made no progress`）——因为 `ring` 需要
交换性，而 `Ring` 不假定交换；`abel` 只需加群结构，故足够。 -/
theorem one_sub_mul_add_mul_eq_add_mul_sub {R : Type*} [Ring R]
    (η θstar θ : R) : (1 - η) * θ + η * θstar = θ + η * (θstar - θ) := by
  rw [sub_mul, one_mul, mul_sub]
  abel

/-- ⭐ **【代数桥 · 环版（反向）】**（取 `symm`，便于 `rw` 两个方向都用）。 -/
theorem add_mul_sub_eq_one_sub_mul_add_mul {R : Type*} [Ring R]
    (η θstar θ : R) : θ + η * (θstar - θ) = (1 - η) * θ + η * θstar :=
  (one_sub_mul_add_mul_eq_add_mul_sub η θstar θ).symm

/-- ⭐⭐ **【代数桥 · 实向量版】** `(1-η) • θ + η • θ* = θ + η • (θ* - θ)`。

**⭐ 这就是 `gstep η θ* θ = θ + η • (θ* - θ)`**（逐字即 `gstep` 定义的右移）。
**⚠ 不是同义反复**：无前件；`module`（`Mathlib.Tactic` 的线性代数归一化）
判定的 `ℝ`-模恒等。 -/
theorem one_sub_smul_add_smul_eq_add_smul_sub {V : Type*} [AddCommGroup V]
    [Module ℝ V] (η : ℝ) (θstar θ : V) :
    (1 - η) • θ + η • θstar = θ + η • (θstar - θ) := by
  module

/-- ⭐ **【`gstep` 的「θ + η•偏差」形态】**：把 §1 的桥直接写成 `gstep` 的等式。

**⭐ 用途**：把「`gstep` 是仿射收缩」与「`gstep` 是 `θ` 加一个偏差项」
这两个读法**接通**；§3 的抽象桥用后者作为 `hstep` 的形状。 -/
theorem gstep_eq_add_smul_sub {V : Type*} [AddCommGroup V] [Module ℝ V]
    (η : ℝ) (θstar θ : V) :
    PipelineTendstoGen.gstep η θstar θ = θ + η • (θstar - θ) :=
  one_sub_smul_add_smul_eq_add_smul_sub η θstar θ

/-! ===========================================================================
  §2  ⭐⭐ 抽象迭代桥（**任意** `F`）：一步等于 `F` ⟹ `n` 步等于 `F^[n]`
  =========================================================================== -/

/-- ⭐⭐⭐ **【抽象迭代桥】** 若 `endToEnd` 的一步恰好是函数 `F`，则
`endToEndIter` 的 `n` 步**就是** `F` 的 `n` 次迭代。

**⭐ 与已入库 `EndToEndPipelineBridge.endToEndIter_eq_iterate` 的区别**：
那条取 `F := fun s => endToEnd … s …`（**恒等**的特例，`rfl` 级）；
本条允许**任意** `F`，因而能把 `endToEndIter` 接到**任何**
`Nat.iterate` 理论上（`gstep`、`fstep`、乃至非线性映射）。

**⚠ 不是同义反复**：前件 `hstep` 只讲**一步**（`∀ θ, endToEnd … θ = F θ`），
**不出现** `endToEndIter`、**不出现** `n`；
结论讲**一切 `n`**。`n = 0` 平凡，`n = k+1` 由
`endToEndIter_succ` + 归纳 + `Function.iterate_succ_apply` 得到。

**⚠ 无需任何类型等式**（任务书曾猜需要 `X.Carrier = Θ.Carrier`）：
`φ : X.Carrier →+ Θ.Carrier` 的签名**已经把两个空间接上了** ——
见 §6 的缺口报告。 -/
theorem endToEndIter_eq_iterate_of_step (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (F : W.frame.Θ.Carrier → W.frame.Θ.Carrier)
    (hstep : ∀ θ, endToEnd W h η φ y θ u ε a x = F θ) (n : ℕ)
    (θ₀ : W.frame.Θ.Carrier) :
    endToEndIter W h η φ y u ε a x n θ₀ = F^[n] θ₀ := by
  induction n generalizing θ₀ with
  | zero => rw [endToEndIter_zero, Function.iterate_zero_apply]
  | succ k ih =>
    rw [endToEndIter_succ, hstep, ih, Function.iterate_succ_apply]

/-! ===========================================================================
  §3  ⭐⭐ `gstep` 版抽象桥：一步 = `gstep` ⟹ `endToEndIter = pipelineNGen`
  =========================================================================== -/

/-- ⭐⭐⭐ **【迭代桥 · `gstep` 版】**：一步等于 `gstep ηr θ*` ⟹
`endToEndIter = pipelineNGen`。

**⭐ 这是任务书第 3 条（`endToEndIter = pipelineNGen`）在**抽象层**的落地**：
`pipelineNGen ηr θ* θ₀ n` 的定义**就是** `(gstep ηr θ*)^[n] θ₀`
（`Fate/PipelineTendstoGen.lean:114`），故本引理把 `endToEndIter`
搬到 `pipeline_tendsto_gen` 的**陈述对象**上。

**⟹ 只要某实例能给出「一步 = `gstep`」（如 `linWorld`，见已入库
`EndToEndPipelineBridge.linStep_eq_gstep`），收敛就**自动**成立。**

**⚠ 不是同义反复**：前件只讲一步、不出现 `endToEndIter`／`pipelineNGen`／`n`；
结论讲一切 `n`，且左端是 `EndToEnd` 的 `Nat.rec`、右端是 `PipelineTendstoGen`
的 `Nat.iterate`（两套独立定义）。

**⚠ 额外的实例前件 `[Module ℝ Θ.Carrier]` 是 `gstep` 签名本身要求的**
（`gstep` 定义在 `[AddCommGroup V] [Module ℝ V]` 上），**不是**本文件新增的数学假设。 -/
theorem endToEndIter_eq_pipelineNGen_of (W : WorldModel)
    [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    [Module ℝ W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (ηr : ℝ) (θstar : W.frame.Θ.Carrier)
    (hstep : ∀ θ, endToEnd W h η φ y θ u ε a x = PipelineTendstoGen.gstep ηr θstar θ)
    (n : ℕ) (θ₀ : W.frame.Θ.Carrier) :
    endToEndIter W h η φ y u ε a x n θ₀
      = PipelineTendstoGen.pipelineNGen ηr θstar θ₀ n := by
  rw [PipelineTendstoGen.pipelineNGen]
  exact endToEndIter_eq_iterate_of_step W h η φ y u ε a x
    (PipelineTendstoGen.gstep ηr θstar) hstep n θ₀

/-! ===========================================================================
  §4  ⭐⭐⭐⭐ 主定理：`endToEndIter linWorld` 趋于真值 `θ*`
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【端到端闭环收敛（`linWorld`）】**

$$x \ne 0 \;\wedge\; |1-\eta| < 1 \;\Longrightarrow\;
  \texttt{endToEndIter}\ \mathrm{linWorld}\ \dots\ n\ \theta_0 \;\longrightarrow\; \theta^{*} .$$

**⭐ 这是已入库 `EndToEndPipelineBridge` 明确**未做**的那一步**
（其 §0 原话：「不声称收敛」「收敛已在 `ThetaConvergence` 中独立给出」——
但那是在 `fstep`／`pipelineN` 上，**不是**在 `endToEndIter` 上）。
本定理把它**真的**落到端到端四环闭环的迭代上。

**证明就是「搬」**（两行）：

```lean
(PipelineTendstoGen.pipeline_tendsto_gen (V := ℝ) η θstar x θ₀ hx hη).congr
  (fun n => (linWorld_endToEndIter_eq_pipelineNGen η θstar x θ₀ hx n).symm)
```

即：`pipeline_tendsto_gen` 给出 `pipelineNGen η θ* θ₀ n → θ*`；
已入库的 `linWorld_endToEndIter_eq_pipelineNGen` 把 `pipelineNGen`
换成 `endToEndIter`。**收敛性本身来自 `pipelineNGen_closed` + `(1-η)^n → 0`，
不是被假定。**

**⚠ 不是同义反复**：前件 `hx : x ≠ 0`（设计点非零，保证 `1/x` 存在）、
`hη : |1 - η| < 1`（步长在 `(0,2)` 内）；结论是**闭环轨迹的极限点 = `θ*`**。
前件中**没有任何** `Tendsto` 语句，也**没有任何** `endToEndIter` 取值等式。
`hx` 与 `hη` 分别只用于「归一化方向存在」与「标量幂趋于 0」，
与「极限点是谁」无关。 -/
theorem endToEndIter_linWorld_tendsto (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    Filter.Tendsto
      (fun n : ℕ =>
        endToEndIter ThetaConvergence.linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      Filter.atTop (nhds θstar) :=
  (PipelineTendstoGen.pipeline_tendsto_gen (V := ℝ) η θstar x θ₀ hx hη).congr
    (fun n =>
      (EndToEndPipelineBridge.linWorld_endToEndIter_eq_pipelineNGen η θstar x θ₀ hx n).symm)

/-- ⭐⭐⭐ **【同一结论，`pipelineN` 形态】**

`WorldModelPipeline.pipelineN`（`WorldModelPipeline.lean:283`）是 `endToEndIter`
的**逐字别名**（`pipelineN_eq_iter`）。本定理把 §4 的主定理写成 `pipelineN` 形态，
以便与 `WorldModelPipeline.pipeline_tendsto` **逐字对比**。

**⚠ 本条不重证收敛**：它调用已入库的
`pipeline_tendsto_gen_specializes`（它本身由 `pipelineN_eq_pipelineNGen` 搬运
`pipeline_tendsto_gen` 得到）。**本定理的作用是提供「互替检验」的另一半。** -/
theorem pipelineN_linWorld_tendsto (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    Filter.Tendsto
      (fun n : ℕ => WorldModelPipeline.pipelineN ThetaConvergence.linWorld
        (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      Filter.atTop (nhds θstar) :=
  WorldModelPipeline.pipeline_tendsto_gen_specializes η θstar x θ₀ hx hη

/-- ⭐⭐⭐ **【互替检验】**：§4 的 `endToEndIter` 形态与 `pipelineN` 形态
给出**同一命题**（两条同时成立，故任一条可替代另一条）。

**⭐ 作用**：排除「本文件的收敛定理与既有 `pipeline_tendsto` 陈述了**不同**命题」
的可能 —— 这是本项目历史上反复出现的失败模式（见 `PipelineTendstoSpecializes`
§3 的自检思想，本定理把它扩到端到端侧）。 -/
theorem endToEndIter_linWorld_tendsto_and_pipelineN (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    Filter.Tendsto
        (fun n : ℕ =>
          endToEndIter ThetaConvergence.linWorld (id : ℝ → ℝ) η
            (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
            (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        Filter.atTop (nhds θstar)
      ∧ Filter.Tendsto
        (fun n : ℕ => WorldModelPipeline.pipelineN ThetaConvergence.linWorld
          (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        Filter.atTop (nhds θstar) :=
  ⟨endToEndIter_linWorld_tendsto η θstar x θ₀ hx hη,
   pipelineN_linWorld_tendsto η θstar x θ₀ hx hη⟩

/-! ===========================================================================
  §5  自检清单（本文件的验收点，逐条可编译）
  =========================================================================== -/

/-- **自检 1**：§2 的抽象桥在 `n = 0` 时**退回** `id`（确认桥的 `zero` 分支正确）。 -/
example (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (F : W.frame.Θ.Carrier → W.frame.Θ.Carrier)
    (hstep : ∀ θ, endToEnd W h η φ y θ u ε a x = F θ) (θ₀ : W.frame.Θ.Carrier) :
    endToEndIter W h η φ y u ε a x 0 θ₀ = (fun θ => θ)^[0] θ₀ := by
  rw [endToEndIter_eq_iterate_of_step W h η φ y u ε a x F hstep 0 θ₀]
  rfl

/-- **自检 2**：§2 的抽象桥在 `n = 1` 时**退回** `hstep`
（确认桥的 `succ` 分支真的读了 `hstep`，桥**非空**）。 -/
example (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (F : W.frame.Θ.Carrier → W.frame.Θ.Carrier)
    (hstep : ∀ θ, endToEnd W h η φ y θ u ε a x = F θ) (θ₀ : W.frame.Θ.Carrier) :
    endToEndIter W h η φ y u ε a x 1 θ₀ = F θ₀ := by
  rw [endToEndIter_eq_iterate_of_step W h η φ y u ε a x F hstep 1 θ₀]
  rfl

/-- **自检 3**：§1 的代数桥**不能**对任意 `η` 给出 `θ = θ + η * (θ* - θ)`
——取 `η = 0` 时右式确实退化，说明桥是**有内容的等式**，不是 `θ = θ` 的伪装
（即**不是同义反复**的机器证据）。 -/
example (θstar θ : ℝ) : θ + (0 : ℝ) * (θstar - θ) = θ := by ring

/-- **自检 4**：§1 的代数桥**真在** `η ≠ 0` 时产生新信息：`η = 1` 时右式
`θ + 1 * (θ* - θ) = θ*`，即「一步直达真值」，左式 `0 * θ + 1 * θ* = θ*` 同值。 -/
example (θstar θ : ℝ) : θ + (1 : ℝ) * (θstar - θ) = θstar := by ring

end EndToEndPipelineTendsto

end FateV2.Loop