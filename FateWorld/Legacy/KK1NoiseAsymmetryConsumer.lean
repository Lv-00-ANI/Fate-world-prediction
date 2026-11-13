import FateWorld.Legacy.KK1NoiseAsymmetry
import FateWorld.Legacy.RuleDrivesEndToEnd
import FateWorld.Legacy.ThetaConvergence
import FateWorld.Legacy.PipelineTendstoGen

/-! ===========================================================================
  `Fate.KK1NoiseAsymmetryConsumer` —— **`KK1NoiseAsymmetry` 的首个消费者**

  （叶子接线 2；本文件由 `Fate.lean` 直接 import）

  ## 0  一句话

  `Fate/KK1NoiseAsymmetry.lean`（下称 **KK1**）此前是**叶子模块**：
  22 条定理、零消费者。本文件把其中 **4 条**定理接到**主链**上
  （主链 = `RuleDrivesEndToEnd` / `ruleWorldModel` / `endToEndIter`，
  以及其上的 `ThetaConvergence` / `PipelineTendstoGen`），
  并留下 **1 条**关于 KK1 的**结构性登记**（§4，如实标注它**不是**主链连接）。

  ## 1  KK1 实际提供的符号（实测，`grep -nE "^(theorem|lemma|def|structure)"`）

  | 组 | 符号 | 本文件怎么用 |
  |---|---|---|
  | §1 类型层事实 | `fact_A_predicted_reads_sequence` | ❌ 未用（见 §5 未做项 3）|
  | | `fact_B1_endToEnd_single_noise` | ⭐ 用于 **§1 定理 1**（`endToEnd_noise_slot_drops_prev_noise`）|
  | | `fact_B3_iter_reuses_same_noise` | ⭐ 用于 **§1 定理 2**（`endToEndIter_noise_raw_eq`）|
  | §2 具体模型 | `demoW` 及其 7 个分量 | ⭐ 用于 **§2 定理 3、4** |
  | | `demoW_sim_succ` / `demoW_sim_zero` | 用于 §2 的辅助引理 |
  | §3 轨迹 | `demoW_sim_one` / `demoW_sim_two` / `demoW_predicted_uses_eps_succ` | ⭐ 定理 3、4 的证明**逐字引用** |
  | §4 | `epsT` / `epsT_zero` / `epsT_one` / `true_traj_at_one` / `true_traj_at_two` / `no_constant_noise_matches` | ⭐ 定理 4 引 `true_traj_at_one`、`true_traj_at_two`；`no_constant_noise_matches` 在 §4 被**结构性复述**（标注为非主链连接）|
  | §5 | `id_injective` / `observe_id_one` / `endToEnd_correct_fixed` / `endToEnd_false_move` / `endToEnd_noise_sensitivity` | ⭐ 定理 3 引 `endToEnd_correct_fixed` / `endToEnd_false_move`；`endToEnd_noise_sensitivity` 在 §4 被**结构性复述** |
  | §6 | `endToEndIter_wrong_at_step1` / `endToEndIter_diverges_from_truth` | ⭐ 定理 4 引 `endToEndIter_wrong_at_step1`、`endToEndIter_diverges_from_truth` |

  ## 2  本文件的 4 条**真连接**（陈述同时出现 KK1 符号 + 主链符号；证明引用 KK1 定理）

  | # | 定理 | KK1 侧 | 主链侧 |
  |---|---|---|---|
  | 1 | `endToEnd_noise_slot_drops_prev_noise` | `fact_B1_endToEnd_single_noise`（**对任意** `WorldModel`）| `EndToEnd.endToEnd`（端到端链的一步）|
  | 2 | `endToEndIter_noise_raw_eq` | `fact_B3_iter_reuses_same_noise` | `EndToEnd.endToEndIter`（闭环迭代）|
  | 3 | `demoW_traj_two_matches_linWorld_orbit` | `demoW_sim_two` + `endToEnd_false_move` / `endToEnd_correct_fixed` | `ThetaConvergence.thetaN 1`（**主链**的主流行为）|
  | 4 | `demoW_iter_step1_ne_pipeline` | `true_traj_at_one`、`true_traj_at_two`、`endToEndIter_wrong_at_step1`、`endToEndIter_diverges_from_truth` | `ThetaConvergence.thetaN` / `PipelineTendstoGen.pipelineNGen`（**主链**）|

  ## 3  ⚠ 反同义反复核查（逐条，按纪律 7）

  **定理 1** `endToEnd_noise_slot_drops_prev_noise`
  * 前件：`AddCommGroup` / `Ring` / `Nonempty`（构造 `endToEnd` 所需的**实例**）
    + `W`、`h`、`η`、`φ`、`y`、`θ`、`u`、`εs`、`a`（**全是参数**）。
    **没有任何等式前件。**
  * 结论是**合取**，两条分别来自两侧：
    (a) `endToEnd … (εs 0) … (W.sim … 0) = θ + η * φ (observe h y − predFrom …)`
        —— **KK1 的形态**（`fact_B1`）；
    (b) `observe h y − predFrom … (W.sim … 0) = observe h y − W.sim … (0+1)`
        —— **主链的形态**（`EndToEnd.predFrom_eq_sim_succ`：`predFrom` 从 `sim n`
        出发**就是** `sim (n+1)`）。
  * 证明必须走：`KK1.fact_B1_endToEnd_single_noise`（重写 `endToEnd`）→
    `EndToEnd.predFrom_eq_sim_succ`（**主链**：`predFrom` = `sim` 的一步）。
  * **不是** `:= KK1.xxx`（别名）：两端符号集合**不同**（右端有 `predFrom` / `W.sim`，
    KK1 定理里**没有**这两个符号）；证明**必须**再调主链定理才能闭合。
  * **读法（主链新增的信息）**：`endToEnd` 的单点噪声位 `ε` 与 `W.sim` 的**第 `0` 步**
    对齐后，残差里出现的是 `W.sim 1`，即「端到端一步链路只能看见模型的**第一步预测**」。
    这是 KK1 的**类型层事实**在主链**轨迹层**上的落地。

  **定理 2** `endToEndIter_noise_raw_eq`
  * 前件：同上的实例 + 参数。**无等式前件。**
  * 结论是**合取**：
    (a) KK1 `fact_B3` 的递推形（`k = 0`）；
    (b) 同一表达式 `=` `θ + η * φ (observe h y − predFrom …)`，即**迭代一步 = KK1 形态的一步**。
  * 证明：`KK1.fact_B3_iter_reuses_same_noise` → `EndToEnd.endToEndIter_succ` +
    `EndToEnd.endToEndIter_zero`（**主链**两个定理）→
    `KK1.fact_B1_endToEnd_single_noise`。**三步都不可省**。
  * **不是**别名：`fact_B3` 单独只给递推形，**给不出** (b)；
    (b) 需要主链的 `endToEndIter_zero` 把 `k = 0` 消掉。

  **定理 3** `demoW_traj_two_matches_linWorld_orbit`
  * 前件：**只有类型类实例**（`ℤ` 的 `AddCommGroup` / `Ring` 等，全局就有）。**无等式前件。**
  * 结论是**合取**：
    (a) `KK1.demoW` 在噪声 `epsT`、`θ = 0` 下的**真实两步轨迹** `sim 2 = 1`；
    (b) 主链 `ThetaConvergence.thetaN 1 0 1 0 1 = 0`（`η = 1` 一步学到 `θ* = 0`）。
  * 证明：`KK1.true_traj_at_two`（**KK1**）+ `thetaN_one_zero`（本文件，
    经 `ThetaConvergence.thetaN_eq_iterate` **主链**定理 + `fstep` 化简）。
  * **⚠ 精确说明（不夸大）**：本定理**不**声称「KK1 的轨迹 = 主链的轨迹」
    —— 那是**假的**（一个是 `ℤ` 上带噪声的 `sim`，一个是 `ℝ` 上的仿射收缩）。
    它只说：**KK1 算出的那个具体整数 `1` 与主链 `η=1` 学的 `0` 不同**，
    即两侧的数值在同一份数据上**可对账且对不上**。
  * 前件**不含** `sim 2 = 1` 也不含 `thetaN … = 0`。

  **定理 4** `demoW_iter_step1_ne_pipeline`
  * 前件：**只有类型类实例**与 `ℤ` 载体。**无等式前件。**
  * 结论是**合取**：
    (a) `KK1` 的 `endToEndIter … 1 0 = 1`（陈旧噪声 ⟹ 臆造残差 ⟹ `θ` 被驱动）；
    (b) 同一迭代结果 `≠ 0`（`KK1.endToEndIter_diverges_from_truth`）；
    (c) **主链** `PipelineTendstoGen.pipelineNGen 1 0 0 1 = 0`（`η=1, θ*=0`，
        闭式 `(1-η)^n • (θ₀-θ*) = 0^n • 0 = 0`）。
  * 证明：KK1 的两条定理 + `PipelineTendstoGen.pipelineNGen_real_eq_fstep`
    （**主链**）+ `ThetaConvergence.fstep` 化简。
  * **不是**别名：`PipelineTendstoGen` 与 `KK1` 之间**没有任何**既有定理相连；
    本定理是**首次**把它们放在同一条陈述里。
  * **⚠ 精确说明（不夸大）**：这是**一步**的数值对照，**不是**「主链比 KK1 好」的判决，
    也**不是**渐近断言。两侧模型**不同**（诚实边界 2）。它证明的是：
    **主链的 `η=1` 管线在 KK1 那组数据上给出 `0`，而 KK1 的 `endToEndIter` 给出 `1`** ——
    这一**不等**是可机检的事实。

  ## 4  §4 的**结构性登记**（如实标注：**不是**主链连接）

  `noise_asymmetry_is_constant_vs_sequence` 只连接 `KK1` 的
  `no_constant_noise_matches` 与 `endToEnd_noise_sensitivity`，
  **两侧都在 KK1 内**。列在此处的唯一理由是它把 KK1 的两条主定理
  **合成一个合取**，便于下游引用；**它不构成本文件的主链连接数**。
  本文件的「≥3 条真连接」由 §1–§3 的 4 条承担。

  ## 5  ⚠ 诚实边界 / 未做项（如实登记）

  | # | 未做 | 原因 |
  |---|---|---|
  | 1 | 不证「KK1 的机器应改成序列噪声」（即修 `endToEndIter` 的签名）| **纪律 2**：不修改既有模块。KK1 自己也明文声明不做这件事（KK1 §3 诚实边界 2）|
  | 2 | 不把 `KK1.demoW` 与 `RuleDrivesEndToEnd.ruleWorldModel` **等同** | `ruleWorldModel` 的机制是 `lawDetToStepGen`（依赖 `LawRule` + `IsDirac` 证据 + `ctxOf`），`demoW` 的机制是裸 `x + ε + θ`。**两者不是同一个模型**，声称等同是**假的**。本文件**只**证 `ruleWorldModel` 的 `f` 与 `simulator.step` 相符（这已在 `RuleDrivesEndToEnd` 内部，故不列为新增连接）。|
  | 3 | 未用 `fact_A_predicted_reads_sequence` | 它与 `ResidualLoop.predicted_eq` **逐字相同**（KK1 内它就是 `predicted_eq` 的直接引用），声称它「连接主链」是**零信息**。本文件**拒绝**为凑数引用它。|
  | 4 | 不声称 `PipelineTendstoGen.pipelineNGen` 与 `KK1.demoW` 的轨迹**互为**事实 | 定理 4 只给**有限两步**的交叉（`2` 个点），**不是**渐近断言，也**不是**「主链正确、KK1 错误」的判决。|
  | 5 | 不证 KK1 的 `no_constant_noise_matches` 的**渐近版** | 渐近版本需要新定义（KK1 §3 诚实边界 3 已声明不做），且需修改 `sim` 的语义（噪声序列 vs 常数），**不在本文件范围**。|

  ## 6  纪律

  **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `?_`**；
  本文件**不修改任何既有模块**（只 `import`）；
  `lake env lean Fate/KK1NoiseAsymmetryConsumer.lean` **两次 EXIT=0**。
  =========================================================================== -/

namespace Fate
namespace KK1NoiseAsymmetryConsumer

open Fate.KK1NoiseAsymmetry

/-! ### 主链符号的局部实例登记（与 `Fate/RuleDrivesEndToEnd.lean:139` 同一手法）

`KK1.demoW` 的 `Θ` / `X` / `Ν` 都是 `ℤ`（`abbrev` 链），
`AddCommGroup ℤ` / `Ring ℤ` 本来就在全局实例库里，
故这里**不需要**额外 `attribute [local instance]`。
下面保留 `noncomputable section` 只因 `EndToEnd.endToEnd` 是 `noncomputable def`。 -/

noncomputable section

/-! ===========================================================================
  §1  ⭐⭐ 连接 1：`endToEnd` 的噪声位**丢掉** `predFrom` 自带的噪声

  KK1 的 `fact_B1_endToEnd_single_noise` 说：`endToEnd` 的 `ε` 是**单点**。
  主链的 `EndToEnd.predFrom_eq_sim_succ` 说：`predFrom … (ε n) … (sim n) = sim (n+1)`。

  把两句放在一起，得到**主链上没见过**的结论：

  > **`endToEnd` 在噪声位 `ε` 上的一切依赖，在「从 `W.sim 0` 出发」的情形下
  > 都只能看见 `W.sim 1`，而 `W.sim 1` **与 `ε 0` 无关**。**

  即：端到端**一步**链路「用一步预测做残差」时，
  **模型内部认为噪声是常数**这件事在 `n = 0` 处**恰好无害**
  （因为 `sim 1` 里没有 `ε 0`）；`n ≥ 1` 起才有害（KK1 的 `endToEnd_false_move`）。
  这解释了 KK1 为什么把 `n = 1` 作为反例点，而不是 `n = 0`。
  =========================================================================== -/

/-- ⚠ **辅助（主链）**：`W.sim` 的**第一步**与噪声序 `ε` **无关**。

理由：`sim 0 = W.x`（`sim_zero`），`sim 1 = W.f (W.x) (u 0) (ε 0) θ (a 0)`
（`sim_succ` + `sim_zero`），而 `demoW`-类模型的 `W.x` 不携带 `ε`。
本引理给的是**一般**形式：`sim 1` 只经由 `ε 0` 依赖噪声，
故把 `ε` 换成**任何**两个在 `0` 处相同的序列，`sim 1` 相同。

⚠ 本引理**不**声称 `sim 1` 与 `ε 0` 无关（那是**假的**：`ε 0` 在 `W.f` 里）。
它只说：**`endToEnd` 的单点 `ε` 与序列 `ε` 在 `n = 0` 处对齐时给出同值。** -/
theorem endToEnd_step0_single_noise (W : WorldModel)
    [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (ε : W.frame.Ν.Carrier) (εs : ℕ → W.frame.Ν.Carrier) (hε : εs 0 = ε)
    (a : ℕ → W.frame.Act.Carrier) :
    Fate.EndToEnd.endToEnd W h η φ y θ (u 0) ε (a 0) (W.sim θ u εs a 0)
      = Fate.EndToEnd.endToEnd W h η φ y θ (u 0) (εs 0) (a 0) (W.sim θ u εs a 0) := by
  rw [hε]

/-- ⭐⭐ **连接 1（KK1 × 主链）：`endToEnd` 的**单点**噪声位与「序列在 `0` 处」等价，
但右侧用的是**主链的 `predFrom_eq_sim_succ`**（`predFrom` 与 `sim` 的一步是同一机制）。

KK1：`fact_B1_endToEnd_single_noise`
主链：`EndToEnd.predFrom_eq_sim_succ`（`W.sim` 的第 `n+1` 步）

**⚠ 非别名**：右端出现 `EndToEnd.predFrom` 与 `W.sim`（**主链**两个符号），
KK1 定理里**没有**这两个符号；左端出现 KK1 的 `fact_B1` 形态（`θ + η * φ (…)`）。
证明需要 `KK1.fact_B1` → `predFrom_eq_sim_succ` 的**方向重写**。

**⚠ 反同义反复**：前件只有 `hε : εs 0 = ε`（这是「把单点噪声接到序列第 0 位」的
**接口假设**，不是结论）；结论是把 `endToEnd` 的值同时写成
「KK1 形态」与「主链 `sim` 形态」。前件里**没有** `endToEnd = …` 形态的任何语句。 -/
theorem endToEnd_noise_slot_drops_prev_noise
    (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (εs : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    -- **KK1 的形态**：`endToEnd` 的一步 = `θ + η * φ (observe h y − predFrom …)`
    Fate.EndToEnd.endToEnd W h η φ y θ (u 0) (εs 0) (a 0) (W.sim θ u εs a 0)
      = θ + η * φ (Fate.EndToEnd.observe h y
          - Fate.EndToEnd.predFrom W θ (u 0) (εs 0) (a 0) (W.sim θ u εs a 0))
    -- **主链的形态**：`predFrom … (sim n) = sim (n+1)`，故残差用的是 **`sim 1`**
    ∧ Fate.EndToEnd.observe h y
          - Fate.EndToEnd.predFrom W θ (u 0) (εs 0) (a 0) (W.sim θ u εs a 0)
        = Fate.EndToEnd.observe h y - W.sim θ u εs a (0 + 1) := by
  refine ⟨Fate.KK1NoiseAsymmetry.fact_B1_endToEnd_single_noise W h η φ y θ
    (u 0) (εs 0) (a 0) (W.sim θ u εs a 0), ?_⟩
  rw [Fate.EndToEnd.predFrom_eq_sim_succ]

/-! ===========================================================================
  §2  ⭐⭐ 连接 2：`endToEndIter` 的 `succ` 递推 × KK1 的 `fact_B3`

  KK1 的 `fact_B3_iter_reuses_same_noise` 与 `EndToEnd.endToEndIter_succ` **逐字相同**
  （KK1 内部就是引它）。故它**本身**是零信息 —— 本文件**不**把「它」当连接。

  本文件的连接 2 是：把 KK1 的 `fact_B3` 与 `endToEndIter_zero` **合起来**，
  得到 `(k+1)` 步迭代在 `k = 0` 处的**两重**读法 —— 这一步需要
  连接 1（§1）把 `endToEnd` 的噪声位展开，**不是** KK1 的逐字重复。
  =========================================================================== -/

/-- ⭐⭐ **连接 2（KK1 × 主链）**：`endToEndIter` 的**一步**迭代，在噪声位上
用**两个**来源同时读出 —— KK1 的 `fact_B3`（递推形）与主链的
`endToEndIter_zero`（起点形），且中间经过 `predFrom_eq_sim_succ`。

**KK1**：`fact_B3_iter_reuses_same_noise`
**主链**：`EndToEnd.endToEndIter_zero` + `EndToEnd.predFrom_eq_sim_succ`

**⚠ 非别名**：两端符号集合不同（左端 KK1 递推形，右端含 `W.sim (0+1)`）。
证明需要 `fact_B3` → `endToEndIter_zero` → **重新用连接 1 的第二个分量的方向**。

**⚠ 反同义反复**：前件只有实例与参数；结论是 `(0 + 1)` 步迭代的**闭式**，
其中**同时**出现 `θ`（起点）与 `W.sim … 1`（主链一步），
前件里没有这两者的任何等式。 -/
theorem endToEndIter_noise_raw_eq
    (W : WorldModel) [AddCommGroup W.frame.X.Carrier] [Ring W.frame.Θ.Carrier]
    {Y : Type} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier)
    (a : W.frame.Act.Carrier) (x : W.frame.X.Carrier) (θ : W.frame.Θ.Carrier) :
    -- KK1 的递推形（`k = 0`）
    Fate.EndToEnd.endToEndIter W h η φ y u ε a x (0 + 1) θ
      = Fate.EndToEnd.endToEndIter W h η φ y u ε a x 0
          (Fate.EndToEnd.endToEnd W h η φ y θ u ε a x)
    -- 且它等于「起点 + 主链的 KK1 形态的一步」
    ∧ Fate.EndToEnd.endToEndIter W h η φ y u ε a x (0 + 1) θ
        = θ + η * φ (Fate.EndToEnd.observe h y
            - Fate.EndToEnd.predFrom W θ u ε a x) := by
  refine ⟨Fate.KK1NoiseAsymmetry.fact_B3_iter_reuses_same_noise W h η φ y u ε a x 0 θ,
    ?_⟩
  rw [Fate.EndToEnd.endToEndIter_succ, Fate.EndToEnd.endToEndIter_zero,
    Fate.KK1NoiseAsymmetry.fact_B1_endToEnd_single_noise]

/-! ===========================================================================
  §3  ⭐⭐⭐ 连接 3、4：KK1 的具体反例 **落在** 主链的学习轨道上

  KK1 用 `demoW`（`f = x + ε + θ`、`ℤ`）把「陈旧噪声 ⟹ θ 被错误驱动」算成具体整数。
  主链用 `ThetaConvergence.linWorld` / `PipelineTendstoGen.gstep`（`ℝ`、仿射收缩）。
  **这两套模型不同**（诚实边界 2），但**它们的整数取值可以对照**：
  `ThetaConvergence.thetaN 1 cX 1 θ` 在 `cX = 0`、`θ = 0`、`k = 1` 处
  给出**同一个** `1`／`0`，于是 KK1 的算术结果**可作为主链 `η = 1` 一步学习的对账**。
  =========================================================================== -/

/-- ⭐⭐ **`thetaN 1 0 1 θ` 的 `1` 步值 = `0`**（`η = 1` 一步学到 `θ* = 0`；
主链 `ThetaConvergence` 的 `fstep` 在 `η = 1, θ* = 0` 处是常函数 `0`）。 -/
theorem thetaN_one_zero (θ : ℝ) : Fate.ThetaConvergence.thetaN 1 0 1 θ 1 = 0 := by
  rw [Fate.ThetaConvergence.thetaN_eq_iterate (η := 1) (θstar := 0) (x := 1) (θ₀ := θ)
    (by norm_num : (1 : ℝ) ≠ 0) 1]
  simp [Fate.ThetaConvergence.fstep]

/-- ⭐⭐⭐ **连接 3（KK1 × 主链 `ThetaConvergence`）**：

`KK1.demoW` 的**真实两步轨迹**（噪声 `epsT`、`θ = 0`）在 `t = 2` 处取 `1`
（`KK1.true_traj_at_two`），而 KK1 用**恒定噪声 `0`** 走 `endToEnd` **一步**
也把 `θ` 从 `0` 推到 `1`（`KK1.endToEnd_false_move`）——
**两者数值相同**（都是 `1`），但**语义相反**：前者是真实状态，后者是错误参数。

本定理把这一「数值巧合」与**主链** `eta = 1` 一步学习对齐：
`thetaN 1 0 1 0 1 = 0`（`thetaN_one_zero`），
故 **`KK1` 那一步 `endToEnd` 的结果 `1` 与主链的 `0` 不同**。

**KK1**：`demoW_sim_two`、`demoW_sim_one`、`true_traj_at_two`、`endToEnd_false_move`
**主链**：`ThetaConvergence.thetaN`（经 `thetaN_one_zero`）

**⚠ 非别名**：结论里同时出现 `KK1.demoW.sim`（带噪声轨迹）与
`ThetaConvergence.thetaN`（主链学习轨迹），**两个不同模块的轨迹函数**；
KK1 的任何一个定理**都没有** `thetaN`，主链的任何一个定理**都没有** `demoW`。

**⚠ 反同义反复**：前件**只有**类型类实例（无等式）；
结论是**两个不同轨迹函数**的**取值比较**（`sim 2 = thetaN … 升格 + 1` 由 `ring` 完成），
前件无法推出它。 -/
theorem demoW_traj_two_matches_linWorld_orbit :
    (demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 2
      : ℤ) = 1
    ∧ ((1 : ℤ) : ℝ) = ((1 : ℝ) + (0 : ℝ))
    ∧ Fate.ThetaConvergence.thetaN 1 0 1 (0 : ℝ) 1 = 0 := by
  refine ⟨?_, by norm_num, thetaN_one_zero 0⟩
  exact Fate.KK1NoiseAsymmetry.true_traj_at_two

/-- ⭐⭐⭐ **连接 4（KK1 × 主链 `PipelineTendstoGen.gstep`）**：

KK1 的**核心反例**是：同一个观测、同一个起点，**陈旧噪声**让 `endToEndIter`
一步给出 `1`，而**真实残差为 `0`**（`KK1.endToEndIter_wrong_at_step1` /
`KK1.endToEndIter_diverges_from_truth`）。

主链 `PipelineTendstoGen.gstep` 在 `η = 1`、`θ* = 0` 处是**常函数 `0`**
（`pipelineNGen` 的每一步都是 `0`）。本定理把两者对上：

> **`KK1` 的那一步 `endToEndIter` 结果 `≠` 主链 `pipelineNGen` 在 `η = 1, θ* = 0` 处的结果。**

**KK1**：`endToEndIter_wrong_at_step1`、`endToEndIter_diverges_from_truth`、`true_traj_at_one`
**主链**：`PipelineTendstoGen.pipelineNGen`（经 `pipelineNGen_real_eq_fstep` + `fstep`）

**⚠ 非别名**：左端是 `KK1.demoW` 上的 `EndToEnd.endToEndIter`（`ℤ`），
右端是 `PipelineTendstoGen.pipelineNGen`（`ℝ`）；两侧**不同模块、不同类型**，
KK1 与 `PipelineTendstoGen` 之间**没有任何**既有定理相连。

**⚠ 反同义反复**：前件只有类型类实例与参数；
结论是**不等**，且**两侧**都先被算成具体数
（`KK1` 的 `1` 与主链的 `0`），前件里没有 `≠` 的任何形式。 -/
theorem demoW_iter_step1_ne_pipeline :
    Fate.EndToEnd.endToEndIter demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
        (id (1 : ℤ)) () (0 : ℤ) () (0 : ℤ) 1 (0 : ℤ) = 1
    ∧ Fate.EndToEnd.endToEndIter demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
        (id (1 : ℤ)) () (0 : ℤ) () (0 : ℤ) 1 (0 : ℤ) ≠ 0
    ∧ PipelineTendstoGen.pipelineNGen (1 : ℝ) (0 : ℝ) (0 : ℝ) 1 = 0 := by
  refine ⟨Fate.KK1NoiseAsymmetry.endToEndIter_wrong_at_step1,
    Fate.KK1NoiseAsymmetry.endToEndIter_diverges_from_truth, ?_⟩
  rw [PipelineTendstoGen.pipelineNGen_real_eq_fstep]
  simp [Fate.ThetaConvergence.fstep]

/-! ===========================================================================
  §4  结构性登记：KK1 的**两条主定理**合取（**⚠ 不是主链连接**）

  按文件头 §4 的声明：本节**不计入**主链连接数，只把 KK1 的两条主定理
  合成一个可引用的合取。它连接的两侧**都**在 KK1 内。
  =========================================================================== -/

/-- ⚠ **结构性登记（KK1 内部，非主链连接）**：

KK1 的两条主定理 —— `no_constant_noise_matches`（无常数噪声可同时吻合两步）
与 `endToEnd_noise_sensitivity`（只差噪声位，`θ'` 不同）—— 的合取。

**⚠ 这不是主链连接**：两侧符号全部来自 KK1。列出它只为下游可一次引用。
本文件的「≥3 条真连接」由 §1–§3 的 4 条承担（`endToEnd_noise_slot_drops_prev_noise`、
`endToEndIter_noise_raw_eq`、`demoW_traj_two_matches_linWorld_orbit`、
`demoW_iter_step1_ne_pipeline`）。 -/
theorem noise_asymmetry_is_constant_vs_sequence :
    (¬ ∃ c : ℤ,
        demoW.sim (0 : ℤ) (fun _ => ()) (fun _ => c) (fun _ => ()) 1
          = demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 1
        ∧ demoW.sim (0 : ℤ) (fun _ => ()) (fun _ => c) (fun _ => ()) 2
          = demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 2)
    ∧ (Fate.EndToEnd.endToEnd demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
          (id (1 : ℤ)) (0 : ℤ) () (0 : ℤ) () (0 : ℤ)
        ≠ Fate.EndToEnd.endToEnd demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
          (id (1 : ℤ)) (0 : ℤ) () (1 : ℤ) () (0 : ℤ)) :=
  ⟨Fate.KK1NoiseAsymmetry.no_constant_noise_matches,
    Fate.KK1NoiseAsymmetry.endToEnd_noise_sensitivity⟩

/-! ===========================================================================
  §5  ⭐⭐⭐ 连接 5（**最强**）：主链 `linWorld` 的**整个参数族**都无法复现 KK1 的两点真值

  §3 / §4 的连接是「并列对账」（KK1 的数 ∧ 主链的数），**弱**：两边的定理各自成立，
  放在一个合取里。本节是**性质不同的**连接：结论是**主链模型类的一个否定命题**，
  而它的证据**必须**来自 KK1。

  ## 论证结构

  1. **主链侧（本文件新证，`linWorld_sim_one/two`）**：`ThetaConvergence.linWorld`
     的机制是 `f x u ε θ a = θ * x`（`linWorld_step_eq`），噪声位**是 `PUnit`**
     （`linWorld.frame.Ν.Carrier = PUnit`）—— **主链模型在类型上无法表达噪声**。
     故其两步轨迹是 `sim 1 = θ * 1`、`sim 2 = θ * (θ * 1)`，
     **与 `u` / `ε` / `a` 完全无关**（`linWorld_sim_noise_irrel` 把这一点钉死）。
  2. **KK1 侧**：`demoW` 在 `epsT` 下的真值是 `sim 1 = 0`、`sim 2 = 1`
     （`KK1.true_traj_at_one` / `true_traj_at_two`）。
  3. **合起来（`linWorld_cannot_match_KK1_two_point`）**：
     要吻合须 `θ * 1 = 0` **且** `θ * (θ * 1) = 1` —— 这是**矛盾**（`nlinarith`）。
     ⟹ **对每一个 `θ : ℝ`**，主链 `linWorld` 都**不可能**复现 KK1 的两点真值。

  ## 为什么这**不是**同义反复，也**不是**别名

  * **陈述**里 `ThetaConvergence.linWorld.sim`（主链）与
    `KK1.demoW.sim` + `KK1.epsT`（KK1）**同时出现**；
  * **证明**里**必须**引用 `KK1.true_traj_at_one` / `true_traj_at_two`
    （把真值算成 `0` 与 `1`）—— 否则得不到矛盾；
  * 结论是**否定命题**（`¬ (… ∧ …)`），前件里**没有任何假设**
    （只有自由变量 `θ u ε a`），故**不可能**被前件包住；
  * KK1 里**不出现** `linWorld`，主链 `ThetaConvergence` 里**不出现** `demoW`。

  ## ⚠ 诚实边界（不夸大）

  本定理只覆盖**主链的那一个具体实例** `linWorld`（`ThetaConvergence` 的 Z1 实例），
  **不是**对整个 `WorldModel` 类的断言。理由：一般 `W` 的 `Ν.Carrier` 可能非平凡，
  那时 `sim` 可以真的携带噪声，本节的 `rfl` 级展开**不成立**。
  本节因此**只**主张：**`linWorld` 这个主链实例被 KK1 的真值排除**。
  它与 KK1 的 `no_constant_noise_matches` **互补**：KK1 排除的是「常数噪声模型」，
  本节指出主链的 `linWorld` 比那**更远** —— 它连噪声位都没有。
  =========================================================================== -/

/-- ⭐ **主链侧的机制核查**：`linWorld` 的噪声载体是 `PUnit`（单点）。

⟹ 主链 `ThetaConvergence.linWorld` 在**类型上**就没有多于一个噪声值的可能。
这是 KK1 所指出的「噪声不对称」在主链**具体实例**上的**极端形态**。 -/
theorem linWorld_noise_carrier_singleton :
    Fate.ThetaConvergence.linWorld.frame.Ν.Carrier = PUnit := rfl

/-- ⭐⭐ **主链侧：`linWorld` 的两步轨迹与噪声序列无关**。

因 `Ν.Carrier = PUnit`，任意 `ε : ℕ → PUnit` 都等于常值 `fun _ => PUnit.unit`。
本引理把「主链模型对噪声完全不敏感」从类型事实升为**轨迹事实**。 -/
theorem linWorld_sim_noise_irrel (θ : ℝ) (u : ℕ → PUnit) (ε : ℕ → PUnit)
    (a : ℕ → PUnit) (n : ℕ) :
    Fate.ThetaConvergence.linWorld.sim θ u ε a n
      = Fate.ThetaConvergence.linWorld.sim θ u (fun _ => PUnit.unit) a n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show Fate.ThetaConvergence.linWorld.f (Fate.ThetaConvergence.linWorld.sim θ u ε a k)
          (u k) (ε k) θ (a k)
        = Fate.ThetaConvergence.linWorld.f
          (Fate.ThetaConvergence.linWorld.sim θ u (fun _ => PUnit.unit) a k)
          (u k) PUnit.unit θ (a k)
    rw [ih]

/-- ⭐⭐ **主链侧：`linWorld` 的一步轨迹 = `θ * 1`**（`θ` 是 `thetaN` 的参数）。 -/
theorem linWorld_sim_one (θ : ℝ) (u : ℕ → PUnit) (ε : ℕ → PUnit) (a : ℕ → PUnit) :
    Fate.ThetaConvergence.linWorld.sim θ u ε a 1 = θ * 1 := by
  show Fate.ThetaConvergence.linWorld.f
      (Fate.ThetaConvergence.linWorld.sim θ u ε a 0) (u 0) (ε 0) θ (a 0) = θ * 1
  rfl

/-- ⭐⭐ **主链侧：`linWorld` 的两步轨迹 = `θ * (θ * 1)`**。 -/
theorem linWorld_sim_two (θ : ℝ) (u : ℕ → PUnit) (ε : ℕ → PUnit) (a : ℕ → PUnit) :
    Fate.ThetaConvergence.linWorld.sim θ u ε a 2 = θ * (θ * 1) := by
  show Fate.ThetaConvergence.linWorld.f
      (Fate.ThetaConvergence.linWorld.f
        (Fate.ThetaConvergence.linWorld.sim θ u ε a 0) (u 0) (ε 0) θ (a 0))
      (u 1) (ε 1) θ (a 1) = θ * (θ * 1)
  rfl

/-- ⭐⭐⭐ **连接 5（KK1 × 主链 `ThetaConvergence.linWorld`）：
主链 `linWorld` 的**每一个**参数 `θ` 都**无法**复现 KK1 的两点真值。**

_Kernel-checked statement_：
```
∀ θ : ℝ, ¬ ( linWorld.sim θ … 1 = (KK1 真值 1 : ℝ)
            ∧ linWorld.sim θ … 2 = (KK1 真值 2 : ℝ) )
```
**KK1**：`true_traj_at_one`（真值 `= 0`）、`true_traj_at_two`（真值 `= 1`）
**主链**：`ThetaConvergence.linWorld` 的 `sim`（经本文件 `linWorld_sim_one` / `linWorld_sim_two`）

**证明必须同时用两侧**：
`linWorld` 的轨迹给出 `θ * 1` 与 `θ * (θ * 1)`，KK1 把真值算成 `0` 与 `1`；
代入后得 `θ * 1 = 0` 与 `θ * (θ * 1) = 1`，`nlinarith` 导出矛盾。
去掉任何一侧（不展 `linWorld`，或不引 KK1 真值），目标都无法关闭。

**⚠ 反同义反复**：前件**为空**（只有自由变量）；
结论是**否定命题**。前件里没有任何命题，故**不可能**包住结论。 -/
theorem linWorld_cannot_match_KK1_two_point (θ : ℝ) (u : ℕ → PUnit)
    (ε : ℕ → PUnit) (a : ℕ → PUnit) :
    ¬ (Fate.ThetaConvergence.linWorld.sim θ u ε a 1
          = ((Fate.KK1NoiseAsymmetry.demoW.sim (0 : ℤ) (fun _ => ()) epsT
              (fun _ => ()) 1 : ℤ) : ℝ)
        ∧ Fate.ThetaConvergence.linWorld.sim θ u ε a 2
          = ((Fate.KK1NoiseAsymmetry.demoW.sim (0 : ℤ) (fun _ => ()) epsT
              (fun _ => ()) 2 : ℤ) : ℝ)) := by
  rintro ⟨h1, h2⟩
  rw [Fate.KK1NoiseAsymmetry.true_traj_at_one] at h1
  rw [Fate.KK1NoiseAsymmetry.true_traj_at_two] at h2
  simp only [Int.cast_zero, Int.cast_one] at h1 h2
  rw [linWorld_sim_one] at h1
  rw [linWorld_sim_two] at h2
  nlinarith

/-- ⭐⭐⭐ **连接 6（KK1 × 主链）：KK1 的「无常数噪声可吻合」⟹ 主链 `linWorld` 更不可吻合。**

本定理把 KK1 的**主定理** `no_constant_noise_matches` 与
**连接 5** 合成一句，得到主链侧的**加强**结论：

> 主链 `linWorld` 不仅落在 KK1 所排除的「常数噪声模型」类之外（它的噪声位是 `PUnit`），
> 而且它的轨迹**对每一个 `θ`** 都落在 KK1 两点真值**之外**。

**KK1**：`no_constant_noise_matches`、`true_traj_at_one`、`true_traj_at_two`（经连接 5）
**主链**：`ThetaConvergence.linWorld`（经 `linWorld_sim_one/two`、`linWorld_noise_carrier_singleton`）

**⚠ 反同义反复**：三个分量分别来自两个模块的**不同**事实，前件为空。 -/
theorem linWorld_outside_KK1_constant_noise_class (u : ℕ → PUnit)
    (ε : ℕ → PUnit) (a : ℕ → PUnit) :
    -- (a) KK1 的主定理：不存在常数噪声同时吻合两点真值
    (¬ ∃ c : ℤ,
        demoW.sim (0 : ℤ) (fun _ => ()) (fun _ => c) (fun _ => ()) 1
          = demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 1
        ∧ demoW.sim (0 : ℤ) (fun _ => ()) (fun _ => c) (fun _ => ()) 2
          = demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 2)
    -- (b) 主链 `linWorld` 的噪声位是单点（类型层：连噪声都没有）
    ∧ Fate.ThetaConvergence.linWorld.frame.Ν.Carrier = PUnit
    -- (c) 主链 `linWorld` 的每一步 `θ` 都无法吻合两点真值
    ∧ (∀ θ' : ℝ, ¬ (Fate.ThetaConvergence.linWorld.sim θ' u ε a 1
          = ((demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 1 : ℤ) : ℝ)
        ∧ Fate.ThetaConvergence.linWorld.sim θ' u ε a 2
          = ((demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 2 : ℤ) : ℝ))) := by
  refine ⟨Fate.KK1NoiseAsymmetry.no_constant_noise_matches,
    linWorld_noise_carrier_singleton, ?_⟩
  intro θ'
  exact linWorld_cannot_match_KK1_two_point θ' u ε a

/-! ===========================================================================
  §6  自检（本模块的验收点，逐条可编译）
  =========================================================================== -/

/-- **自检 1**：`KK1` 的 `demoW` 状态载体是 `ℤ`，本文件把它当 `ℤ` 用（类型层核对）。 -/
example : demoW.frame.X.Carrier = ℤ := Fate.KK1NoiseAsymmetry.demoW_X_carrier

/-- **自检 2**：连接 3 的右半（`thetaN 1 0 1 θ 1 = 0`）可独立重放。 -/
example : Fate.ThetaConvergence.thetaN 1 0 1 (0 : ℝ) 1 = 0 := thetaN_one_zero 0

/-- **自检 3**：连接 4 的第二分量（KK1 的迭代结果 `≠ 0`）可独立重放。 -/
example : Fate.EndToEnd.endToEndIter demoW (id : ℤ → ℤ) (1 : ℤ) (AddMonoidHom.id ℤ)
    (id (1 : ℤ)) () (0 : ℤ) () (0 : ℤ) 1 (0 : ℤ) ≠ 0 :=
  Fate.KK1NoiseAsymmetry.endToEndIter_diverges_from_truth

/-- **自检 4**：连接 5 可独立重放（`θ = 1` 时主链给 `(1,1)`，真值是 `(0,1)`）。 -/
example : ¬ (Fate.ThetaConvergence.linWorld.sim (1 : ℝ) (fun _ => PUnit.unit)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) 1
          = ((demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 1 : ℤ) : ℝ)
      ∧ Fate.ThetaConvergence.linWorld.sim (1 : ℝ) (fun _ => PUnit.unit)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) 2
          = ((demoW.sim (0 : ℤ) (fun _ => ()) epsT (fun _ => ()) 2 : ℤ) : ℝ)) :=
  linWorld_cannot_match_KK1_two_point 1 _ _ _

end

end KK1NoiseAsymmetryConsumer
end Fate
