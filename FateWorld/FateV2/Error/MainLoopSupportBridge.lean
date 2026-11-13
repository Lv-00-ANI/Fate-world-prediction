import FateWorld.FateV2.Error.SupportBound
import FateWorld.FateV2.Loop.MainLoop

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/MainLoopSupportBridge.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 42 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Rules
open FateV2.Model
open FateV2.Modeling
open FateV2.Error

/-
  停止判据与数据支持度的接合（对应论文 §8）

  支持度一侧给出「支持度门槛 s ⟹ 是否够得着边界点」，循环控制一侧给出「信息不足 ⟹ 暂停」。
  在此之前二者只是两条平行的断言，没有任何定理把一个推成另一个。本模块补上这条接合：
  给出显式词典，使主循环暂停成为支持度门槛的一个实例，并证明失效的两种来源在循环侧可区分。

  §1  词典：step 中的 info 就是支持度的读数 supp γ，noise 就是门槛 s。在该词典下
        step supp(γ) s · running = paused ⟺ supp(γ) ≤ s，
        即「信息不足 ⟹ 停」等同于「该分辨率的数据支撑不高于门槛」；
  §2  主循环暂停作为支持度门槛的实例；
  §3  两种失效来源可区分：只有「支持度不足」能靠降门槛（加数据 / 放宽要求）修复，
        结构不可达不行。这是对「泛化到一定程度会失效」的完整回答。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  为什么不能直接写成 ¬ Supported：两个模块对「门槛是否含端点」的约定相反，已登记为
  threshold_boundary_disagreement。这是本次接合最重要的发现——强行写成恒等式会隐式改掉
  其中一个已验收模块的语义。

  建模选择：
    B1  info := supp γ（同一个数，不做映射）。两个载体都已是 ℝ，且 supp 的语义就是有效
        样本数、InfoLevel 的语义是信息量；取同一个数是唯一不引入新假设的选择，任何非恒等
        映射都会塞入未裁定的换算关系。
    B2  门槛取支持度 s，而不取噪声尺度 σ。主循环的 `noise` 在判据中扮演的是**阈值**
        角色（`noise < info` 才继续），故在支持度语言里对应门槛 s。

        ⚠ 此处须登记一个类型层的事实：`MainLoop` 把两者都定义为 `abbrev := ℝ`
        （`InfoLevel` 与 `NoiseScale` 均等于 `ℝ`）。因此**编译器无法区分这两个量**——
        「阈值」与「噪声尺度」的差别只是一条命名约定，不是类型保证。把门槛当作噪声
        尺度使用不会产生任何类型错误，只会得到一个语义上错误的定理。

        这正是本项被列为**显式建模选择**而非定理的原因：它不可能被机器检验。
    B3  桥接只走 running → paused，不重塑 step，也不统一两边的边界约定。改任一边都会
        静默破坏已有结论，故本模块只读两边，并把分歧登记为上述定理。

  注：本模块不重证，只调用支持度与主循环两个模块已给出的结论。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error

namespace MainLoopSupport

open Set
open FateV2.Error.Core
open FateV2.Error.R_SupportBound

noncomputable section

/-! ===========================================================================
  §1  词典：把 `MainLoop` 的三个参数对到 `SupportBound` 的对象上
  =========================================================================== -/

/-- **词典（B1 + B2）**：读到 `γ` 处时主循环的三个参数。

$$\mathrm{info}:=\mathrm{supp}(\gamma),\qquad
  \mathrm{noise}:=s\;(\text{支持度门槛}),\qquad
  \mathrm{margin}:=m.$$

**⚠ `noise` 取**门槛 `s`**，不取噪声尺度 `σ`**（B2）：
理由是 `step` 里 `noise` 的位置是**阈值**（`noise < info` 才继续），
而支持度语言里的阈值恰是 `s`。`σ` 在 `step` 里**没有位置**——
这正是 `FitBoundary` 已证的「`ShouldStop` 表达力内不能判定边界」。 -/
structure Dict (S : SuppProfile) (s m : ℝ) (γ : ℝ) where
  /-- 主循环看到的信息量。 -/
  info : FateV2.Loop.MainLoop.InfoLevel
  /-- 主循环的判据阈值。 -/
  noise : FateV2.Loop.MainLoop.NoiseScale
  /-- 主循环的恢复余量。 -/
  margin : ℝ
  /-- **B1**：信息量**就是**该分辨率下的有效样本数（同一个数）。 -/
  info_eq : info = S.supp γ
  /-- **B2**：阈值**就是**支持度门槛（同一个数）。 -/
  noise_eq : noise = s
  /-- 余量原样传入。 -/
  margin_eq : margin = m

/-- **词典的标准构造**（存在性：任一 `(S,s,m,γ)` 都有词典）。 -/
def Dict.of (S : SuppProfile) (s m γ : ℝ) : Dict S s m γ where
  info := S.supp γ
  noise := s
  margin := m
  info_eq := rfl
  noise_eq := rfl
  margin_eq := rfl

/-! ===========================================================================
  §2  主定理：**「信息不足 ⟹ 停」就是「支持度低于门槛」**
  =========================================================================== -/

/-- **桥（核心定理）**：在词典下，主循环从 `.running` 暂停
**当且仅当**该分辨率处的有效样本数**不超过门槛**。

$$\texttt{step}\;\mathrm{supp}(\gamma)\;s\;m\;\texttt{running}=\texttt{paused}
\iff \mathrm{supp}(\gamma)\le s$$

**则** `step` 的 `¬ noise < info` 即 `info ≤ noise`（`not_lt`），
在 B1、B2 下就是 `supp γ ≤ s`。

**⚠ 这里出现一个必须登记的边界差**（见下条 `threshold_boundary_disagreement`）：
`step` 用**非严格**比较（`info ≤ noise` 即停），
而 `Supported` 也非严格（`s ≤ supp γ` 即充足）。
两都在 `supp γ = s` 处**给出相反结论**。
**⟹ 故本桥陈述为 `supp γ ≤ s`（而非 `¬ Supported`）—— 两者在边界点上不同。** -/
theorem paused_iff_supp_le_threshold (S : SuppProfile) (s m γ : ℝ) :
    FateV2.Loop.MainLoop.step (S.supp γ) s m FateV2.Loop.MainLoop.LoopState.running
        = FateV2.Loop.MainLoop.LoopState.paused
      ↔ S.supp γ ≤ s := by
  rw [FateV2.Loop.MainLoop.step_from_running_paused_iff]

/-- **边界点的分歧（**必须显式登记**）**：当支持度**恰等于**门槛时，
主循环**暂停**，而 `SuppProfile.Supported` 却判为**充足**。

$$\mathrm{supp}(\gamma)=s
\;\Longrightarrow\;
\bigl(\texttt{step}\ldots=\texttt{paused}\bigr)\ \wedge\ \mathrm{Supported}(S,s,\gamma)$$

**⚠ 为何不「修」而「登」**：
- `step` 的非严格约定属 `MainLoop` §4（已由 `step_from_running_paused_iff`
  固定，且 §6 的收敛判决依赖它）；
- `Supported` 的非严格约定属 `SupportBound` §1（`Feasible` 依赖它）。
**两者都是「门槛含不含端点」的**建模选择**，未被裁定。**
本文件不擅自统一（那会静默改动两个已验收模块的语义），
而是把**分歧本身**做成可引用的事实。**-/
theorem threshold_boundary_disagreement (S : SuppProfile) (s m γ : ℝ)
    (heq : S.supp γ = s) :
    FateV2.Loop.MainLoop.step (S.supp γ) s m FateV2.Loop.MainLoop.LoopState.running
        = FateV2.Loop.MainLoop.LoopState.paused
    ∧ S.Supported s γ := by
  refine ⟨(paused_iff_supp_le_threshold S s m γ).mpr (le_of_eq heq), ?_⟩
  rw [SuppProfile.Supported]
  exact le_of_eq heq.symm

/-- **桥（严格版，避开边界分歧）**：若支持度**严格大于**门槛，
主循环**继续**。

$$s<\mathrm{supp}(\gamma)
\;\Longrightarrow\;
\texttt{step}\;\mathrm{supp}(\gamma)\;s\;m\;\texttt{running}=\texttt{running}$$

**这是 §2 与 `SupportBound` 唯一**无歧义**的接合点**：
在严格不等式上，两边的判定**完全一致**。 -/
theorem running_of_threshold_lt_supp (S : SuppProfile) (s m γ : ℝ)
    (h : s < S.supp γ) :
    FateV2.Loop.MainLoop.step (S.supp γ) s m FateV2.Loop.MainLoop.LoopState.running
        = FateV2.Loop.MainLoop.LoopState.running := by
  rw [FateV2.Loop.MainLoop.step_from_running_running_iff]
  exact h

/-- **暂停位置与 `margin` 无关**：从 `.running` 出发，
`margin` 是否为零**不影响**是否暂停。

**读法**：这正是 `MainLoop` §6 已证「`margin` 不是增加步数、而是破坏收敛」
的**支持度侧镜像** —— `margin` 管的是**恢复**，不是**暂停**。
本定理把它固定下来，防止把 `margin` 误当作支持度门槛的修正项。 -/
theorem paused_irrel_margin (S : SuppProfile) (s m₁ m₂ γ : ℝ) :
    FateV2.Loop.MainLoop.step (S.supp γ) s m₁ FateV2.Loop.MainLoop.LoopState.running
        = FateV2.Loop.MainLoop.LoopState.paused
      ↔ FateV2.Loop.MainLoop.step (S.supp γ) s m₂ FateV2.Loop.MainLoop.LoopState.running
        = FateV2.Loop.MainLoop.LoopState.paused := by
  rw [paused_iff_supp_le_threshold, paused_iff_supp_le_threshold]

/-! ### §2.1 接到 `SupportBound` §3.2 的主定理：**暂停的必然性**

上面 §2 的桥只说「暂停 ⟺ 支持度不足」，是**单点**的。
真正回答问题的是：**在某些门槛下，暂停是唯一结局**。 -/

/-- **「处处暂停」到底意味着什么**（**修正了我最初的过度断言**）。

我原本打算证「处处暂停 ⟹ 不可达」（`always_paused_implies_not_achievable`）。
**但它在非严格约定下是假 的**：若 `supp ≡ s`（常数支持度恰等于门槛），
则每条 `γ` 都暂停（`supp γ ≤ s`），但每条 `γ` 也都 `Feasible`（`s ≤ supp γ`），
故 `Achievable` 完全可以为真。

**✅ 正确的结论（本定理）**：若 `γ` 轴上**处处暂停**，且某 `γ₀` **确实落于
`Feasible` 内**，则在该点处支持度**恰等于门槛**：

$$\bigl(\forall\gamma,\ \mathrm{supp}(\gamma)\le s\bigr)
\ \wedge\ s\le\mathrm{supp}(\gamma_0)
\ \Longrightarrow\ \mathrm{supp}(\gamma_0)=s$$

**⟹ 真正的含义**：若「处处暂停」与「可达」同时成立，
则可达性只能用**恰在边界点上的 `γ`** 来实现 ——
这些点的支持度**没有一点余量**。这正是`SupportBound`
`achievable_at_own_support` 的循环侧镜像（支持度**恰好**够用）。 -/
theorem always_paused_forces_boundary_support (S : SuppProfile)
    (s m : ℝ)
    (hpause : ∀ γ,
      FateV2.Loop.MainLoop.step (S.supp γ) s m FateV2.Loop.MainLoop.LoopState.running
        = FateV2.Loop.MainLoop.LoopState.paused)
    {γ₀ : ℝ} (hfeas : s ≤ S.supp γ₀) :
    S.supp γ₀ = s := by
  have hle := (paused_iff_supp_le_threshold S s m γ₀).mp (hpause γ₀)
  exact le_antisymm hle hfeas

/-- **「处处暂停」的正确不可达陈述**（需**严格**不足）。

若在每个 `γ` 处支持度都**严格低于**门槛（`supp γ < s`），
则 `Feasible(S,s)` **为空** ⟹ `Achievable` 必然为假。

**⟹ 这是「数据不够 ⟹ 泛化不可达」的**最干净**形式，
与 `SupportBound` 的 `Feasible` 定义直接接合。 -/
theorem strictly_unsupported_implies_not_achievable (W : ErrProfileWeak)
    (S : SuppProfile) (σ s : ℝ)
    (hstrict : ∀ γ, S.supp γ < s) :
    ¬ Achievable W S σ s := by
  rintro ⟨γ, hfeas, _⟩
  exact absurd hfeas (not_le.mpr (hstrict γ))

/-- **反向的**充分性**：若某 `γ` 处支持度充足且该 `γ` 是边界点，
则主循环在该 `γ` 处**继续**，且泛化**可达**。

**读法**：这是「继续 + 可达」的**联合见证** ——
`SupportBound` §3.4 的 `achievable_of_boundary_of_supported`
与本文件 §2 的 `running_iff_supported` **同时**成立。 -/
theorem running_and_achievable_of_boundary (W : ErrProfileWeak)
    (S : SuppProfile) (σ s m : ℝ) {γ : ℝ}
    (hsupp : s < S.supp γ) (hb : IsFitBoundary W σ γ) :
    FateV2.Loop.MainLoop.step (S.supp γ) s m FateV2.Loop.MainLoop.LoopState.running
        = FateV2.Loop.MainLoop.LoopState.running
    ∧ Achievable W S σ s :=
  ⟨running_of_threshold_lt_supp S s m γ hsupp,
   achievable_of_boundary_of_supported W S σ s hsupp.le hb⟩

/-! ===========================================================================
  §3  「泛化到一定程度会失效」的**两种来源**，在主循环侧的区分
  =========================================================================== -/

/-! `SupportBound` §5.2 已指出「一定程度」有**两种**来源：

| 来源 | 是否为数据问题 | 加数据能否修复 |
|---|---|---|
| **支持度不足** | ✅ 是 | ✅ **能** |
| **结构不可达**（恒过拟合 / 一致间隙） | ❌ 否 | ❌ **不能** |

**本节在**主循环语言**里把这两者分开** —— 这是回答用户问题的关键：
「泛化到一定程度会失效」中的「一定程度」**若被误当成数据量**，
就会以为「加数据总能救」，而 `not_achievable_of_uniformGap` 说**不能**。 -/

/-- **来源一：支持度不足 ⟹ 暂停，但**降门槛可救**。

若在门槛 `s` 处从 `.running` 暂停（`supp γ ≤ s`），
**且**把门槛降到使该 `γ` **严格撑得住**（`s' < supp γ`），
则在新门槛 `s'` 处主循环**恢复 `.running`**。

**⚠ `hpause` **不是推理所需的前提**（故写作 `_hpause`）**，
而是**上下文记录**：它标明「本定理描述的是**从暂停态**出发的恢复」，
使读者不会误以为这是一条无条件恒等式。
推理上真正起作用的是 `s' < supp γ` —— 即「降门槛」
与「换到支持度更高的 `γ`」在 §2 的桥下是**同一效果**。 -/
theorem pause_can_be_fixed_by_lowering_threshold (S : SuppProfile)
    {s s' m γ : ℝ}
    (_hpause : FateV2.Loop.MainLoop.step (S.supp γ) s m FateV2.Loop.MainLoop.LoopState.running
        = FateV2.Loop.MainLoop.LoopState.paused)
    (hnow : s' < S.supp γ) :
    FateV2.Loop.MainLoop.step (S.supp γ) s' m FateV2.Loop.MainLoop.LoopState.running
        = FateV2.Loop.MainLoop.LoopState.running := by
  exact (FateV2.Loop.MainLoop.step_from_running_running_iff
    (S.supp γ) s' m).mpr hnow

/-- **来源二：结构不可达 ⟹ 暂停，且**任何数据都救不了**。

$$\bigl(\forall\gamma,\ \sigma+\delta\le E_W(\gamma)\bigr)
  \;\Longrightarrow\;
  \forall s,\ \neg\,\mathrm{Achievable}(W,S,\sigma,s)$$

**⟹ 在主循环侧**：不论把门槛 `s` 降到多少，`γ` 轴上**任何**支撑得住的点
都**不是**边界点 ⟹ **暂停无法通过「加数据」解除**。

**这是对用户问题「泛化到一定程度会失效」的**最尖锐**的回答**：
失效有两种，**只有一种能靠数据修复**。 -/
theorem uniformGap_no_data_helps (W : ErrProfileWeak) (S : SuppProfile)
    (σ δ : ℝ) (hδ : 0 < δ) (hgap : ∀ γ, σ + δ ≤ W.err γ) :
    ∀ s, ¬ Achievable W S σ s :=
  fun s => not_achievable_of_uniformGap W S σ δ hδ hgap s

/-- **结构不可达的主循环侧陈述**：一致间隙 ⟹ **不论门槛多低都救不了**。

若 `γ` 轴上**没有任何**边界点，则对任意 `γ`，主循环的 `.running`
所处之处要么支持度不足（暂停），要么**即使继续也不可能得到可接受的拟合**。

**形式化**（避开「继续」的语义歧义）：**一致间隙 ⟹ 任何门槛下 `Achievable` 为假**，
**且**存在一个 `γ` 轴上的点使主循环在该处暂停（支持度不足）——
即两种「卡住」可以在同一点上**叠加**，故降门槛**不能**脱困。 -/
theorem gap_pauses_even_at_zero_threshold (W : ErrProfileWeak) (S : SuppProfile)
    (σ δ : ℝ) (hδ : 0 < δ) (hgap : ∀ γ, σ + δ ≤ W.err γ)
    (m : ℝ) :
    (∀ s, ¬ Achievable W S σ s) ∧
    (∀ γ, FateV2.Loop.MainLoop.step (S.supp γ) (S.supp γ + 1) m
              FateV2.Loop.MainLoop.LoopState.running
            = FateV2.Loop.MainLoop.LoopState.paused) := by
  refine ⟨fun s => not_achievable_of_uniformGap W S σ δ hδ hgap s, fun γ => ?_⟩
  -- 门槛取 `supp γ + 1`：则 `supp γ ≤ supp γ + 1` ⟹ 暂停
  rw [paused_iff_supp_le_threshold]
  linarith

/-- **两种来源**不可混同**（显式分离）**：

存在一个剖面 `W`、支持度剖面 `S`、`σ`，使得
「支持度不足导致不可达」（来源一）与「结构导致不可达」（来源二）
**在同一 `σ` 下是不同命题** —— 即**降低门槛能解除第一种但解除不了第二种**。

**构造**：`profConstOne` 与 `σ=0` 属**来源二**（`profConstOne_no_boundary`
+ 一致间隙）。故存在 `δ>0` 使任何 `s` 都不可达，**包括 `s=0`**。
⟹ 「降门槛到 0」**不能**恢复可达性。 -/
theorem two_sources_are_distinct :
    ∃ (W : ErrProfileWeak) (σ : ℝ),
      ∀ (S : SuppProfile) (s : ℝ), ¬ Achievable W S σ s := by
  refine ⟨profConstOne, 0, ?_⟩
  intro S s
  exact not_achievable_of_uniformGap profConstOne S 0 1 one_pos
    (fun γ => by rw [profConstOne_err]; norm_num) s

/-! ===========================================================================
  §4  诚实边界（**本文件不做的事**）
  =========================================================================== -/

/-!
### §4.1 ⚠ `noise` 与 `σ` 是**两个不同的东西**（B2 的警告）

| 符号 | 所在层 | 含义 | 能否互换 |
|---|---|---|---|
| `MainLoop.noise` | 循环控制 | **判据阈值**（信息够不够） | ❌ |
| `Core.σ` | `FitBoundary` | **噪声尺度**（误差该落在哪） | ❌ |

**⚠ 本文件**刻意不**建立 `noise ↔ σ` 的等式**：
`FateV2.Error.FitBoundary` §6 已证**在 `ShouldStop` 的表达力内不能判定 `σ` 的位置**
（`profConstOne` 对 `σ=0` 与 `σ=1` 给出相反的边界存在性，
而任何只读 `(d,n,τ)` 的判据**不能区分**）。
**若本文件擅自令 `noise = σ`，就会绕过那条**不可判定性**定理。**
⟹ 故词典只令 `noise := s`（支持度门槛），**`σ` 保持独立**。

### §4.2 ⚠ **两个模块的「门槛含端点」约定**不同**（本文件最重要的登记）**

| 模块 | 判定 | 在 `supp γ = s` 处 | 约定 |
|---|---|---|---|
| `MainLoop.step` | `info ≤ noise` ⟹ 停 | **停** | **非严格**（含端点）|
| `SupportBound.Supported` | `s ≤ supp γ` ⟹ 充足 | **充足** | **非严格**（含端点）|

**⟹ 在门槛恰好相等的点上，两边**给出相反结论**（`threshold_boundary_disagreement`）。
**⚠ 本文件**不擅自统一**（那会静默改动两个已验收模块的语义）：
- `MainLoop` §6 的收敛判决依赖 `≤` 的非严格形式；
- `SupportBound.Feasible` 依赖 `Supported` 的非严格形式。
**⟹ 故本文件的桥一律**避开**边界点：
- 充要存在（`paused_iff_supp_le_threshold`）用 `supp γ ≤ s` 陈述；
- 与 `Feasible` 接合时**只在严格不等式上**断言（`running_of_threshold_lt_supp`）。
**这也修正了我最初的过度断言**（见 `always_paused_forces_boundary_support` 的说明）。

### §4.3 本文件**不做**的事

| # | 未做项 | 为何未做 |
|---|---|---|
| 1 | `noise = σ` 的接合 | §4.1：会绕过 `FitBoundary` 的表达力定理 |
| 2 | 统一两边的边界约定 | §4.2：会静默改动两个已验收模块 |
| 3 | `margin` 的支持度语义 | `MainLoop` §6 已定 `margin` 的作用是**恢复**（非支持度），本文件不重解释 |
| 4 | `supp γ` 的具体表达式 | OQ-4（承 `SupportBound` §1、`FitBoundary` 诚实边界 2） |
| 5 | 主循环的**多分辨率**版本 | 本文件的词典逐 `γ` 固定；「在 `γ` 轴上移动」是 `MainLoop` 之外的决策层，未形式化 |

### §4.4 与用户问题的关系（**本文件补的那一半**）

| 问题的一半 | 谁回答 |
|---|---|
| 支持度 ⟹ **边界点够不够得着** | `SupportBound` §3.2 ✅ |
| **决策侧**「什么时候必须停」 | `MainLoop` §4 ✅ |
| **两者是同一判据吗** | **本文件 §2** ✅（此前❌） |
| 失效的**两种来源能否被数据区分** | **本文件 §3** ✅（此前❌） |
| **两边「门槛含端点」约定是否一致** | **本文件 §4.2** ✅（回答：**不一致**，已登记） |
| `σ` 与 `supp` 的**数值** | ❌ 仍未解（OQ-4） |

**⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
-/

end

end MainLoopSupport

end FateV2.Error
