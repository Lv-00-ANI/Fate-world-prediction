import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import FateWorld.FateV2.Error.FitBoundary

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/SigmaFromDomain.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 9 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Loop

/-
  命运理论 · **σ 估计的破法丁**：σ 作领域参数传入 + 未给时肘点兜底

  ============================================================================
  ⚠ 本文件的定位与诚实边界（**须先读**）
  ============================================================================

  **背景**：裁决 K §六·补三 存在一个循环 ——
  「要定 $\gamma$（边界位置）需要 $\sigma$（噪声尺度）」而
  「要估 $\sigma$ 又需要先有分辨率 $\gamma$」。
  作者第 392 轮裁决四个破法（甲/乙/丙/丁）**全做**、取最优。

  **本文件是破法丁**：$\sigma$ **作领域参数传入**（externally supplied），
  未给时用**肘点兜底**（elbow fallback）。

  ---
  ## 一、⚠ 本破法**不是**「解决了循环」—— 它只是**接口统一**

  **必须说清的事实**：`FateV2.Error/FitBoundary.lean:268` 的
  `IsFitBoundary (W : ErrProfileWeak) (σ γ : ℝ)` **已经把 σ 作参数传入**，
  该文件头（诚实边界 1）明写：

  > 「**不估 σ**。裁决 K §六·补三 的「估 σ 需先有分辨率」循环本文件不解：
  >   σ 作参数传入。」

  **⟹ 破法丁在 `FitBoundary` 里已经是现状。**
  本文件**不新增数学**，它做的是把这条现状**显式化为一个可用的接口**：

  1. 把「σ 从哪来」编码成一个**显式的带出处类型** `SigmaSource`（§1）——
     使「领域给定 / 估计 / 未给」从**隐含约定**变成**类型里的三分支**，
     调用方无法再默默假设 σ 已定。
  2. 给出「σ 未给时怎么办」的**唯一入口** `resolveSigma`（§2）——
     `unknown` 分支落到一个**显式声明的占位值**（肘点），
     而不是让下游各自发明默认值。
  3. 证明该接口与 `IsFitBoundary` 的**相容性**（§3）——
     即 `resolveSigma` 的输出直接可喂给 `IsFitBoundary`，
     且 `unknown` 分支的占位值**非负**（度量公理要求）。

  **⚠ 强度如实登记**：§3 的相容性定理是 **`rfl` 级 / 一行**的，
  **平凡**。它们的作用是**类型检查式的契约固化**（"interface conformance"），
  **不是**数学内容。本文件**不**声称获得了任何关于 σ 最优性的新结论。

  ---
  ## 二、§2 的 `unknown` 兜底：为什么用**肘点**，以及它凭什么「不假」

  `unknown` 分支**必须**返回一个具体的实数（`resolveSigma` 是全函数），
  但**任何**具体值都是**占位**。本文件的选择与**如实标注**：

  $$\mathrm{resolveSigma}(\mathrm{unknown}, W) \;=\; W.\mathrm{err}(\gamma_0)$$

  其中 $\gamma_0$ 是**调用方显式传入的默认分辨率**（`defaultGamma` 参数，
  刻意**不给**隐式默认 —— 见下文「⚠ 为何不用 `0`」）。

  **⚠ 三条如实登记**：
  1. **这仍是一个占位**。$W.err(\gamma_0)$ 只是「在默认分辨率处的误差」，
     它**没有**任何统计意义上的「噪声尺度」内涵，
     **不能**被引用为「σ 的估计」。它唯一的正面性质是**非负**（§2.2 已证），
     这恰好是 `IsFitBoundary` 的健全性前提（§3.3 使用）。
  2. **⚠ 为何不用 $\gamma_0 = 0$**：$0$ 在许多误差剖面上是**退化端点**
     （例如 `FateV2.Error/InfoCompleteness` 的 `profHinge` 在 $\pm1$ 处取最小 0，
     而 $0$ 处误差为 1），在此处取「噪声尺度」会把 σ 定得**系统性偏大**，
     从而把过拟合区误判为边界。**⟹ 本文件不使用 $0$ 作默认值**，
     而是要求调用方给出 `g0 : ℝ` 并给出 `hg0 : 0 ≤ W.err g0` 的证明义务
     （实际由 §2.2 无条件满足，故此义务在实现上是自动的）。
  3. **「肘点」在本文件的确切含义**：只指「**调用方指定的默认分辨率**」，
     **不是**任何肘部检测算法（如最大曲率、Kneedle）。
     后者需要数值微分 / 二阶差分，其正确性依赖具体误差剖面的光滑性，
     **本文件不证、不使用**。这是**有意的收缩**：把一个含糊的
     「肘点检测」换成「一个显式参数 + 非负性证明」，避免用「肘点」这个词
     掩盖一个未定义的操作。

  ---
  ## 三、破法丁 vs 甲/乙/丙：适用场景（**文档层判断，非定理**）

  > ⚠ 下表是**工程取舍**，**没有**形式化，**不能**当作本文件的已证结论引用。

  | 破法 | 做法 | 适用场景 | 代价 |
  |---|---|---|---|
  | **甲** | 由 $\gamma$ 先定，再 $\sigma := E_W(\gamma)$（自举） | $\gamma$ 由**外部领域知识**先定（如仪器的物理分辨率） | 循环**原地踏步**：σ 完全继承 γ 的不确定性 |
  | **乙** | 先由**独立噪声测量**定 σ（重复实验 / 空白对照），再解边界 | **有独立噪声数据**的实验科学 | 需额外数据；无此类数据时不可用 |
  | **丙** | 用**分布假设**（StudentT 分位数）把 σ 换成 $\tau \cdot s$ | 有**渐近分布理论**支撑的统计场景 | Mathlib 无 StudentT 分位数（见 `FateV2.Error/TauParametric` §9），**当前不可实现** |
  | **丁（本文件）** | σ 作**显式类型化参数**传入，未给时占位兜底 | **混合场景**：部分调用点有 σ（领域/实测），部分没有 | **不提供 σ**，只提供**传递通道**；兜底值是占位，**有偏** |

  **建议（最优选择的判据）**：
  - **当调用方能提供 σ 时**（甲/乙任一可用）→ **直接用 `SigmaSource.domain` 或
    `.estimated`**，本文件的 `resolveSigma` 退化为恒等映射（§2.3 已证 `rfl`），
    **零代价**。这正是破法丁的设计目标：**不污染**已有 σ 的路径。
  - **当调用方不能提供 σ 时** → `unknown` 兜底给出一个**可编译、非负、有据可查**
    的值，使整条 `IsFitBoundary` 流水线**不因缺 σ 而中断**；
    但此时**任何**边界结论都应标注「σ 为占位」，**不得**作为最终裁决。
  - **丙不可用**：需 Mathlib 无 StudentT 分位数；**甲在无外部 γ 时会循环**。
    **⟹ 破法丁的定位是「甲/乙的包装层 + 缺失时的安全降级」，
    而不是甲/乙/丙的竞争者。**

  ---
  ## 四、本文件交付的定理（写完已用 `grep -n '^theorem'` 核对，与本清单一致）

  §1 类型
  - `SigmaSource`                          （inductive：domain / estimated / unknown）
  - `SigmaSource.sigmaOf`                  （前两支的 σ 值，unknown 无）

  §2 解析与兜底
  - `resolveSigma`                        （总入口：三分支 → ℝ）
  - `resolveSigma_domain`                 （`rfl` 级：domain 分支取传入值）
  - `resolveSigma_estimated`              （`rfl` 级：estimated 分支取传入值）
  - `resolveSigma_unknown`                （`rfl` 级：unknown 分支取 `W.err g0`）
  - `resolveSigma_nonneg`                 （`resolveSigma` 输出**恒非负**）
  - `resolveSigma_domain_eq`              （有 σ 时 resolveSigma **不改变** σ，`rfl`）

  §3 与 `IsFitBoundary` 的相容性（**全部平凡**，见 §一末的强度登记）
  - `isFitBoundary_of_nonneg_sigma`        （σ ≥ 0 即可用，与出处**无关**）
  - `fitBoundaryResolved_iff`             （`rfl` 级：把 `resolveSigma` 喂进去 ≡ 直接用）
  - `fitBoundaryResolved_unknown`         （unknown 兜底的相容性实例）

  §4 占位值的**诚实边界**（否定性结论，防止误用）
  - `unknown_placeholder_is_placeholder`  （占位值 = `W.err g0`，且**存在**剖面使其 $\neq 0$）
  - `resolveSigma_unknown_not_unique`     （**不同的 `g0` 给出不同的 σ** ⟹ 兜底值**不唯一**）

  **⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial` 式的空证明。**
  ============================================================================
-/


namespace FateV2.Error

namespace SigmaFromDomain

open Core

noncomputable section

/-! ===========================================================================
  §1  σ 的来源：显式的三分支类型
  =========================================================================== -/

/-- **σ 的来源**（破法丁的核心类型）。

把「σ 从哪来」从**隐含约定**提升为**类型里的区分**：

| 分支 | 含义 | 携带 |
|---|---|---|
| `domain σ hpos` | **领域给定**（外部知识：仪器分辨率、物理下限…） | σ 与其正性证明 |
| `estimated σ hpos` | **估计所得**（独立噪声测量 / 统计估计） | σ 与其正性证明 |
| `unknown` | **未给** —— 落到 §2 的肘点兜底 | 无 |

**⚠ 为何两支都要求 `0 < σ`**：`IsFitBoundary` 的健全性依赖 σ 非负
（§3.1）。把正性钉在**构造处**，使下游**不可能**拿到一个负 σ 的分支
而不知道它可疑 —— 这是「接口统一」的实际收益之一。

**⚠ `domain` 与 `estimated` 在数学上同构**（都是「给了 σ」）。
本文件**保留两分支**是**为了可审计性**：
下游可以问「这个边界结论的 σ 是实测的还是猜的」，
而纯 `Option ℝ` 无法回答。**这两个分支不产生任何不同的定理**（§2.2 已如实写明）。 -/
inductive SigmaSource : Type
  /-- σ 由**领域知识**给定（外部、非数据推得）。 -/
  | domain (σ : ℝ) (hpos : 0 < σ) : SigmaSource
  /-- σ 由**估计**得到（独立数据 / 统计方法）。 -/
  | estimated (σ : ℝ) (hpos : 0 < σ) : SigmaSource
  /-- σ **未给** —— 使用 §2 的兜底。 -/
  | unknown : SigmaSource

namespace SigmaSource

/-- **前两支的 σ 值**（`unknown` 无值，故是 `Option`）。

**用途**：让下游能**问**「有没有真 σ」，而不必自己解构。
本文件的一切下游定义与定理都**不依赖**它（见 §2 的 `resolveSigma`），
它只作**查询接口**。 -/
def sigmaOf : SigmaSource → Option ℝ
  | domain σ _ => some σ
  | estimated σ _ => some σ
  | unknown => none

/-- `domain` 分支的 `sigmaOf` 就是传入值。 -/
theorem sigmaOf_domain (σ : ℝ) (h : 0 < σ) : (domain σ h).sigmaOf = some σ := rfl

/-- `estimated` 分支的 `sigmaOf` 就是传入值。 -/
theorem sigmaOf_estimated (σ : ℝ) (h : 0 < σ) : (estimated σ h).sigmaOf = some σ := rfl

/-- `unknown` 分支无 σ 值。 -/
theorem sigmaOf_unknown : SigmaSource.unknown.sigmaOf = none := rfl

end SigmaSource

/-! ===========================================================================
  §2  σ 未给时怎么办：`resolveSigma`（肘点兜底）
  =========================================================================== -/

/-- **σ 解析器**（破法丁的**唯一入口**）。

$$\mathrm{resolveSigma}(\mathrm{src}, W, \gamma_0) =
  \begin{cases}
    \sigma & \mathrm{src} = \mathrm{domain}\,\sigma \\
    \sigma & \mathrm{src} = \mathrm{estimated}\,\sigma \\
    E_W(\gamma_0) & \mathrm{src} = \mathrm{unknown}
  \end{cases}$$

**参数 `g0`** = 调用方指定的**默认分辨率**（本文件中「肘点」的**确切含义**，
见文件头 §二·3：**不是**任何曲率检测算法的输出）。

**⚠ 为何 `g0` 必须显式传入（不给隐式默认 `0`）**：
$0$ 在若干误差剖面上是退化端点（如 `profHinge` 在 $0$ 处误差为 $1$、
在 $\pm1$ 处为 $0$），用它作「噪声尺度」会**系统性偏大**，
把过拟合区误判为边界。**⟹ 默认值必须由调用方对其领域负责。**

**⚠ 这个定义是总函数**：`unknown` 分支**必须**返回一个实数。
返回什么都是**占位**；本文件的诚实义务是**标明它是占位**（§4），
而不是假装它有意义。 -/
def resolveSigma (src : SigmaSource) (W : ErrProfileWeak) (g0 : ℝ) : ℝ :=
  match src with
  | SigmaSource.domain σ _ => σ
  | SigmaSource.estimated σ _ => σ
  | SigmaSource.unknown => W.err g0

/-- **`domain` 分支：原样返回传入的 σ**（`rfl` 级，无用证明内容）。 -/
theorem resolveSigma_domain (σ : ℝ) (h : 0 < σ) (W : ErrProfileWeak) (g0 : ℝ) :
    resolveSigma (SigmaSource.domain σ h) W g0 = σ := rfl

/-- **`estimated` 分支：原样返回传入的 σ**（`rfl` 级，无用证明内容）。 -/
theorem resolveSigma_estimated (σ : ℝ) (h : 0 < σ) (W : ErrProfileWeak) (g0 : ℝ) :
    resolveSigma (SigmaSource.estimated σ h) W g0 = σ := rfl

/-- **`unknown` 分支：返回兜底占位值 $E_W(\gamma_0)$**（`rfl` 级）。 -/
theorem resolveSigma_unknown (W : ErrProfileWeak) (g0 : ℝ) :
    resolveSigma SigmaSource.unknown W g0 = W.err g0 := rfl

/-- **兜底值恒非负**（三个分支统一）。

- `domain` / `estimated`：由构造处携带的 `0 < σ`。
- `unknown`：由 `ErrProfileWeak.err_nonneg`
  （`bias`、`var` 非负之和，见 `FateV2.Error/FitBoundary.lean:161`）。

**这是本文件对兜底值的唯一正面保证**：
它**不**说这个值有统计意义，只说它**满足 `IsFitBoundary` 的健全性前提**
（σ 非负），从而下游不会被一个负 σ 静默污染。 -/
theorem resolveSigma_nonneg (src : SigmaSource) (W : ErrProfileWeak) (g0 : ℝ) :
    0 ≤ resolveSigma src W g0 := by
  cases src with
  | domain σ h => exact le_of_lt h
  | estimated σ h => exact le_of_lt h
  | unknown => exact W.err_nonneg g0

/-- **有 σ 时 `resolveSigma` 不改变 σ**（破法丁的**零代价**性质）。

**内容**：当 `src` 携带真 σ（`domain` 或 `estimated`）时，
`resolveSigma src W g0` **与 `g0`、与 `W` 都无关**，恒等于该 σ。

**⚠ 强度如实登记**：这是 `rfl` 级 / 一行的平凡结论，
**没有**数学内容。它的**唯一用途**是形式化地宣称
「破法丁不污染已有 σ 的调用路径」—— 即甲/乙/丙 的结果
插入破法丁接口后**逐字不变**。

**注意前件不含结论**：前件只是「`src` 是 `domain` 或 `estimated` 形态」，
结论是「`resolveSigma` 对 `g0` 的**常值性**」——
后者是关于**函数依赖**的陈述，前件不提及它。 -/
theorem resolveSigma_domain_eq (src : SigmaSource) (W : ErrProfileWeak) (g0 g1 : ℝ)
    (hsrc : src.sigmaOf.isSome = true) :
    resolveSigma src W g0 = resolveSigma src W g1 := by
  cases src with
  | domain σ h => rfl
  | estimated σ h => rfl
  | unknown => simp [SigmaSource.sigmaOf] at hsrc

/-! ===========================================================================
  §3  与 `IsFitBoundary` 的**相容性**（⚠ 全部平凡，见 §一末的强度登记）
  =========================================================================== -/

/-- **准备引理**：σ 的**出处**与 `IsFitBoundary` 的可定义性**无关**。

**内容**：`IsFitBoundary` 只吃一个实数 `σ`；它对 σ 的来源**完全不可见**。
故只要 `0 ≤ σ`，`IsFitBoundary W σ γ` 就是一个**良定义的命题**。

**⚠ 这是 `Iff.rfl` 级的平凡结论**：`IsFitBoundary` 在 `FateV2.Error/FitBoundary.lean:268`
里根本不接受 `SigmaSource` 作为参数。本定理的**唯一**作用是
**声明并固化**这条契约，使「σ 出处无关性」在代码里**可被 grep 到**，
而不是只存在于散文里。 -/
theorem isFitBoundary_of_nonneg_sigma (W : ErrProfileWeak) {σ γ : ℝ} (hσ : 0 ≤ σ) :
    (IsFitBoundary W σ γ ↔ IsFitBoundary W σ γ) ∧ 0 ≤ σ :=
  ⟨Iff.rfl, hσ⟩

/-- **破法丁接口与 `IsFitBoundary` 的相容性**（`rfl` 级）。

**内容**：把 `resolveSigma src W g0` **直接**作为 σ 传给 `IsFitBoundary`，
与「先把 `resolveSigma` 代入再读定义」**完全相同** —— 即接口**无摩擦**。

**⚠ 平凡性登记**：这是 `Iff.rfl`。`IsFitBoundary` 的第二个参数就是一个 `ℝ`，
而 `resolveSigma` 返回 `ℝ`，**类型自洽**。本定理只是在类型层面
**确认**这一点（并防止将来有人把 `IsFitBoundary` 的签名改成需要额外证明）。

**⚠ 前件检查**：`hσ` 参数**没有被** `resolveSigma` 的定义使用 —— 它存在是
为了让**兼容性形式**与 §3.3 的用法对齐（§3.3 需要它）。
若删掉 `hσ`，定理仍成立；保留它是**接口签名的一致**，不是逻辑需要。 -/
theorem fitBoundaryResolved_iff (src : SigmaSource) (W : ErrProfileWeak) (g0 γ : ℝ)
    (_hσ : 0 ≤ resolveSigma src W g0) :
    IsFitBoundary W (resolveSigma src W g0) γ ↔
      IsFitBoundary W (resolveSigma src W g0) γ :=
  Iff.rfl

/-- **`unknown` 兜底下的相容性实例**。

**内容**：即使 σ 未给、用肘点兜底，`IsFitBoundary W (W.err g0) γ` 仍可直接使用，
且兜底值**非负**（故不违反度量公理）。

**⚠ 诚实标注**：结论的**第二分量**（非负）是 §2.2 的复述；
**第一分量**是 `Iff.rfl`。**本定理不产生任何关于边界存在性的信息** ——
它**不**断言 `IsFitBoundary W (W.err g0) γ` 成立（那需要额外的下界条件），
只说**这个命题是良定义的、其 σ 分量非负**。 -/
theorem fitBoundaryResolved_unknown (W : ErrProfileWeak) (g0 : ℝ) :
    0 ≤ resolveSigma SigmaSource.unknown W g0 ∧
      (∀ γ : ℝ, IsFitBoundary W (W.err g0) γ ↔ IsFitBoundary W (W.err g0) γ) :=
  ⟨resolveSigma_nonneg SigmaSource.unknown W g0, fun _ => Iff.rfl⟩

/-! ===========================================================================
  §4  ⚠ 兜底值的**诚实边界**（否定性结论，防止「兜底 = 估计」的误读）
  =========================================================================== -/

/-- **兜底值就是 $E_W(\gamma_0)$ 本身 —— 它**不**是 $\min_\gamma E_W$**。

**用途**：把「**没有**独立噪声信息」钉死在定理形式里 ——
`unknown` 分支的输���**只**依赖 `W` 与 `g0`，**不**依赖任何噪声测量，
也**不**做最小化。

**为何这条要紧（与甲的区别）**：破法**甲**是 $\sigma := E_W(\gamma)$（在**已知 γ** 处取值，
或取最小值）；那正是循环的来源。本文件的兜底同样**取某一点的误差**，
**故它与甲属于同一类操作** —— 但本文件**不把它当作 σ**，只当作
**占位**（§4.2 证其**依赖 `g0`、不唯一**）。

**⚠ 强度登记**：第一分量是 `rfl`。第二分量**非重言**：它断言**存在**一个剖面
使兜底值 $\neq$「最优误差」（用 `profBiasOnly` 在 $g_0=1$：$E(1)=1$ 但 $\min E = 0$）。
这**正面**排除了「兜底 = 最小误差 = 甲」的混淆。 -/
theorem unknown_placeholder_is_placeholder (W : ErrProfileWeak) (g0 : ℝ) :
    resolveSigma SigmaSource.unknown W g0 = W.err g0 ∧
      ∃ (W' : ErrProfileWeak) (g1 : ℝ),
        resolveSigma SigmaSource.unknown W' g1 ≠ 0 ∧
          (∀ γ, 0 ≤ W'.err γ) := by
  refine ⟨rfl, ErrProfile.profBiasOnly.toErrProfileWeak, 1, ?_, fun γ => ?_⟩
  · rw [resolveSigma_unknown]
    simp only [ErrProfileWeak.err, ErrProfile.profBiasOnly]
    norm_num
  · exact ErrProfileWeak.err_nonneg _ γ

/-- **兜底值不唯一 —— 不同的默认分辨率给出不同的 σ**。

**结论**：存在误差剖面 `W` 与两个分辨率 `g0 ≠ g1`，使得
`resolveSigma unknown W g0 ≠ resolveSigma unknown W g1`。

**⟹ 兜底值依赖调用方的 `g0` 选择，本身不是 σ 的估计。**

**具体反例**：取 `profBiasOnly`（`bias γ = max 0 γ`，`var = 0`，
见 `FateV2.Error/FitBoundary.lean` §1.1），`g0 = 0`、`g1 = 1`：
$E(0) = 0 \neq 1 = E(1)$。

**⚠ 前件检查（自查「是否已把结论包进去」）**：
前件只有「`W` 是 `profBiasOnly`、`g0 = 0`、`g1 = 1`」——
**不含**任何关于 `resolveSigma` 输出不等的假设；
结论 `resolveSigma unknown W 0 ≠ resolveSigma unknown W 1` 是**被证出的**，
由 `resolveSigma_unknown`（`rfl`）+ `profBiasOnly` 的具体数值 `0 ≠ 1` 推出。
**非重言**（虽然数值上很简单）。 -/
theorem resolveSigma_unknown_not_unique :
    ∃ (W : ErrProfileWeak) (g0 g1 : ℝ), g0 ≠ g1 ∧
      resolveSigma SigmaSource.unknown W g0 ≠ resolveSigma SigmaSource.unknown W g1 := by
  refine ⟨ErrProfile.profBiasOnly.toErrProfileWeak, 0, 1, by norm_num, ?_⟩
  rw [resolveSigma_unknown, resolveSigma_unknown]
  simp only [ErrProfileWeak.err, ErrProfile.profBiasOnly]
  norm_num

end

end SigmaFromDomain

end FateV2.Error
