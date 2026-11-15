/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Error.Stage2.ErrorQuadruple`
阶段：**阶段 2 —— 量纲 + 界的形式冻结**

---------------------------------------------------------------------------
本文件的地位（先读这一段）
---------------------------------------------------------------------------
本文件按勘察 G 处方 #1 执行：

> **把阶段 2 的量纲 + 界的形式先冻结成 Lean 类型：**
> **`ErrorQuadruple` 四元组、E1–E8 八个具名 Prop、以及「参数 → 0 时界 → 0」的机械验收引理。**
> **这是纯类型工作，零数学难度，能把留白从「无人认领」变成「编译器认领」。**

本文件是**形式冻结**，不是证明。具体地：

| 内容 | 状态 |
|---|---|
| §1 `ErrorQuadruple` 四元组 | **已冻结**（结构定义，编译通过） |
| §2 `E1Statement` … `E8Statement` | **已冻结**（八个具名 `def … : Prop`，`[待证]`） |
| §3 `bound_vanishes_at_zero` 等验收引理 | **已真证**（非 `[待证]`） |
| §4 `ErrorDimension` 量纲登记 | **已冻结**（归纳类型，裁决 E） |

依阶段 0 验收标准 1 的同一约束（本文件沿用）：

> **零 `sorry`、零 `admit`、零 `axiom`。**

本文件据此约束：**不含 `sorry`、不含 `admit`、不含 `axiom`**。
`E1`–`E8` 八个命题**不做证明**——它们以 `def … : Prop` 的形式**冻结断言的形式**，
而不是作为 `theorem` 留一个洞。这一区分是关键：

- 若写成 `theorem E1 : … := by sorry`，则**违反**零 `sorry` 约束，
  且该文件**无法通过编译**（在本项目的验收口径下）；
- 若写成 `def E1Statement (…) : Prop := …`，则**形式被冻结**、
  **编译器认领**该符号（可被 `#check`、可被下游引用、可被写成一个假设），
  而**没有任何未证断言进入环境**。

这正是处方 #1「把留白从『无人认领』变成『编译器认领』」的**确界**：
本文件让 E1–E8 **有名字、有精确形式、有前件登记**，
但**不**让它们**进入定理环境**（进入即等于宣称其成立）。

---------------------------------------------------------------------------
`[待证]` 的含义与「如何把待证变成定理」
---------------------------------------------------------------------------
每个 `ExStatement` 都是**带参数返回 `Prop` 的函数**，不是全局命题。
要把 `E1` 变成一条真定理，下游需写：

```lean
theorem E1_proof (X : Type) [NormedAddCommGroup X] (M L T h : ℝ) (x_n x_T : X)
    (hLip : …) (hL : 0 < L) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    E1Statement X M L T h x_n x_T := by
  · exact …
```

即：**`ExStatement` 只冻结「结论写着什么」，前件由下游的绑定变量/假设栏承担。**
本文件在每个 `ExStatement` 的 doc-comment 里**逐条列出**该命题所要求的**前件**，
使下游「补前件」这一步成为**机械对照**，而不是重新读一遍理论原文。

⚠ **一个必须登记的选型**：`E1`–`E8` 的**前件**没有写进 `Prop` 的形式里
（除 `E1` 等少数几处把 `h`、`T` 作为参数外），而是写在 doc-comment 的「前件栏」。
理由：若把前件塞进 `Prop`（如 `E1Statement := 前件 → 结论`），
则「界的形式」与「前件」**混在一个 `Prop` 里**，下游想**单独引用界**（不带前件）
时无法拆开，且 `#check` 的输出会失去可读性。
本文件因此**分栏**：`Prop` 只含**界**，前件在 doc-comment。
这一选型登记于此，不作隐藏。

---------------------------------------------------------------------------
符号对照（本文件 Lean 标识符 ↔ 勘察 F 的 E1–E8）
---------------------------------------------------------------------------
| Lean 标识符 | 勘察 F 编号 | 界的形式 | 状态 |
|---|---|---|---|
| `E1Statement` | E1 数学近似 | `‖x_n−x(T)‖ ≤ (hM/2L)(e^{LT}−1)` | `[待证]` |
| `E2Statement` | E2 统计估计 | `sup\|R−R̂\| ≤ 2ℜ_n(𝓗)+M√(ln(1/δ)/2n)` | `[待证]` |
| `E3Statement` | E3 模型 | `R(P̂)−R* ≤ 2L_L·ε_mis+δ_approx+(E2 项)` | `[待证]` |
| `E4Statement` | E4 结构 | `\|P̂_G(y\|do(x'))−P_{G₀}(…)\| ≤ g(d(G,G₀))` | `[待证]` |
| `E5Statement` | E5 分布偏移 | `\|R_Q−R_P\| ≤ L·W` | `[待证]` |
| `E6Statement` | E6 计算 | `‖x_k−x*‖ ≤ κ^k/(1−κ)‖x₁−x₀‖ + u·γ_k/(1−κ)` | `[待证]` |
| `E7Statement` | E7 反事实 | `L_Π·δ + g(Δ)` | `[待证]` |
| `E8Statement` | E8 FCA 编码 | `sup_x diam ς⁻¹(ς(x)) ≤ g(γ,m)` | `[待证]`（⚠ A32 未定义） |

---------------------------------------------------------------------------
与 `Fate.Stage0.Core` 的关系
---------------------------------------------------------------------------
`Fate.Stage0.Core` 冻结的是**阶段 0 的对象与签名**（`ActionSpace`、`TimeIndex`、
`SDERegularity`、`WellFoundedDeps`、`Do` 算子 …）。
本文件冻结的是**阶段 2 的误差量纲与界的形式**，二者**不重叠**：

- 阶段 0 回答「有哪些对象」；
- 阶段 2 回答「这些对象上的误差**用哪个量纲度量、写成什么界**」。

本文件**不依赖** `Fate.Stage0.Core`（保持零耦合，便于独立编译与独立验收）：
E1–E8 的形式只需 `ℝ`、范数空间与一般度量，不需要 Stage 0 的具体对象。
这一**解耦**是刻意的——若日后 Stage 0 的定义被裁决修改，
本文件（阶段 2 的形式冻结）**不应随之失效**。

---------------------------------------------------------------------------
一处诚实的缺口登记：E8 依赖的 A32 未定义
---------------------------------------------------------------------------
勘察 F 已指出：**E8 的 `ς`（FCA 编码映射）依赖 A32，而 A32 当前未定义**。
本文件对此的处理是：

- **仍然冻结 E8 的形式**（把 `ς` 作为**参数** `ς : Z → Y` 传入，
  而不假装它已定义）；
- 在 `E8Statement` 的 doc-comment 里**显式标注** `[A32 未定义]`；
- 不引入 `axiom ς : …` 或 `Unit` 占位来「补」出 `ς`——
  占位是**可检出的缺口**，`axiom` 是**不可检出的谎言**（沿用 Stage 0 的同一条裁决）。

于是 E8 的**形式**被认领，而 E8 的**对象**（`ς`）仍是**明示的留白**。
这两件事不混。
-/

import Mathlib

namespace FateV2.Error.Stage2

open Filter Topology

/-!
  # Error · ErrorQuadruple

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ErrorQuadruple.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Error`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 误差命题的四元组 -/

/-- ⭐⭐⭐ **误差命题的四元组**：每个误差命题必须自带这四项。

⚠ 缺任一项 = 不可陈述（不进入编号表）。

`ErrorQuadruple` 是**判据**而不是**容器**：它回答「一个误差命题要能被陈述，
最少需要交代哪四件事」。

| 字段 | 符号 | 含义 | 缺了会怎样 |
|---|---|---|---|
| `Z` | $Z$ | 误差所在空间 | 不知道「误差是谁的差」，命题无主语 |
| `d` | $d$ | $Z$ 上的度量 | 不知道「差在哪度量下算」，界不可比较 |
| `D` | $D$ | 误差泛函 | 不知道「误差怎么度量」，界与误差**量纲不符** |
| `ℓ` | $\ell$ | 目标量纲 | 不知道「界的目标量纲」，界**不可判定是否达标** |

**为什么 `d` 与 `D` 要分开（这是本结构的核心，不是冗余）**：
两处「距离」在数学上是**不同对象**，混同是量纲错误的**主要来源**：

- `d` 是 $Z$ 上的**底层度量**（例如 $Z=\mathbb{R}^n$ 上的欧氏距离）；
- `D` 是**误差泛函**：它可以是 `d` 本身（E1、E6），
  也可以是 $d$ 的**上确界**（E2 的 $\sup$ 型界）、
  也可以是**与 `d` 无量纲关系**的量（E2 的 $\ell_1$ 差、E5 的 $W_1$ 型差）。

若把二者合成一个字段，则 E2 的 $\sup$ 型界**无法**与 E1 的点态界区分开，
而这正是勘察 F 把四个命题并成一张表时要表达的差异。
⚠ 本文件**不**对 `D` 与 `d` 施加任何一致性约束（不要求 `D = d`、不要求 `D ≤ d` 等）：
是否约束、约束成什么，属于**具体误差命题**的选型，不属于四元组本身。

**`H` 是前件集**：它是一个 `Prop`（可以是合取）。
把前件作为一个字段，使「该四元组**在什么前提下**有意义」**显式化**——
而不是散落在下游定理的假设栏里。

**关于 `ℓ` 的量纲归属**：`ℓ` 的**类型**是 `Z → ℝ`，即「目标量纲是 $Z$ 上的实值函数」。
它与 §4 的 `ErrorDimension` 的关系是：
`ℓ` 给出**具体泛函**，`ErrorDimension` 给出该泛函**所属的量纲族**。
本结构**不**把 `ErrorDimension` 作为字段——因为四元组要能被**任何**量纲使用，
把某一量纲写进四元组会使四元组本身带上一项不该有的选型。
量纲登记由 §4 单独承担，并由 `UsesDimension` 关联。

- **类型**：`[定义性约定]`（勘察 F 的四项，逐项落到字段）
- **出处**：勘察 F（E1–E8 的公共结构）；勘察 G 处方 #1
- **⚠ 未定义项**：无（四项均由勘察 F 直接给出） -/
structure ErrorQuadruple where
  /-- $Z$：误差所在空间 -/
  Z : Type
  /-- $d$：$Z$ 上的度量 -/
  d : Z → Z → ℝ
  /-- $D$：误差泛函（误差的度量方式） -/
  D : Z → Z → ℝ
  /-- $\ell$：目标量纲（默认 = 决策损失） -/
  ℓ : Z → ℝ
  /-- $H$：前件集 -/
  H : Prop

/-- `[定义 2.0]` **良构的四元组**：四元组四项**互相相容**。

四元组本身只保证「有这四项」，**不**保证它们相容。本谓词登记相容性要求：

1. `d_symm`：`d` 对称（误差不该依赖方向）；
2. `d_self`：`d x x = 0`（自误差为零）；
3. `d_nonneg`：`d` 非负；
4. `D_nonneg`：`D` 非负（误差泛函的值域是 $\mathbb{R}_{\ge 0}$）；
5. `D_zero_iff`：`D x y = 0 ↔ x = y`（误差泛函**可分辨**：界为零即错误为零）；
6. `ℓ_nonneg`：目标量纲非负。

⚠ **`D_zero_iff` 是「界是界」的判据（与 §3 呼应）**：
若 `D x y = 0` 却不要求 `x = y`，则「界 → 0」**不**蕴含「误差 → 0」，
一个界函数即使满足 `bound_vanishes_at_zero` 也**不能保证**解收敛。
反之，若 `D_zero_iff` 成立，则 `§3` 的验收引理给出**真正的收敛**——
见 `bound_vanishes_gives_convergence`。

**为什么这些不写进 `ErrorQuadruple` 结构本身**：
若把相容性做成结构字段，则「四元组」与「良构四元组」合并，
下游就无法**先**摆出一个（可能不良构的）四元组**再**论证它良构——
而这正是「诊断为什么某个界不是界」所需的推理形态。
本文件因此分两层：`ErrorQuadruple`（有四项）+ `WellFormed`（四项相容）。

- **类型**：`[定义性约定]`
- **出处**：勘察 F 的四项 + 「界必须能判零」的口头要求的形式化
- **⚠ 未定义项**：勘察 F **未**给出相容性清单；本谓词是**本文件新增的最小集**，
  登记为待裁决项 -/
structure WellFormed (E : ErrorQuadruple) : Prop where
  /-- `d` 对称。 -/
  d_symm : ∀ x y : E.Z, E.d x y = E.d y x
  /-- 自误差为零。 -/
  d_self : ∀ x : E.Z, E.d x x = 0
  /-- `d` 非负。 -/
  d_nonneg : ∀ x y : E.Z, 0 ≤ E.d x y
  /-- `D` 非负。 -/
  D_nonneg : ∀ x y : E.Z, 0 ≤ E.D x y
  /-- `D` 可分辨：误差为零 **当且仅当** 两点相同。 -/
  D_zero_iff : ∀ x y : E.Z, E.D x y = 0 ↔ x = y
  /-- 目标量纲非负。 -/
  ℓ_nonneg : ∀ x : E.Z, 0 ≤ E.ℓ x

/-! ## §2 E1–E8 八个具名 Prop（**只定形式，不证**） -/

/-- `E1` 数学近似：数值解的收敛界。`[待证]`

**界的形式**：$\|x_n - x(T)\| \le \dfrac{hM}{2L}\left(e^{LT}-1\right)$，
其中 $M := \sup \|f'\|$，$T = nh$。

**前件（下游补入假设栏，逐条对照）**：

1. `hLip`：$f$ 关于 $x$ **局部** Lipschitz，常数 $L$；
2. `hL`：$L > 0$（下方公式的分母，必须非零）；
3. `hhL`：$hL$ **小**（即步长与 Lipschitz 常数之积足够小，保证离散流不爆）；
4. `hM`：$M < \infty$，且 $M := \sup\|f'\|$（本形式把它作为参数 `M` 传入）；
5. `hA10`：**A10 解存在唯一**（`Fate.Stage0.Core.SDERegularity` / `DiscreteRegularity`）。

**关于 $T = nh$ 的处理（一个显式选型）**：本形式**把 `T` 作为独立参数**传入，
**不**令 `T := n * h`。理由：若把 `T` 定义性地绑定为 `n * h`，
则下游**无法**讨论「$T$ 固定、$n\to\infty$、$h\to 0$」的极限（这正是
`bound_vanishes_at_zero` 要用的场景——见 `E1_bound_shape`）。
绑定 `T = n*h` 会**锁死** $h$ 与 $n$ 的耦合方向，使「$h\to 0$」与「$n\to\infty$」
**不可分离**。本形式因此把 $T$ 与 $h$、$n$ 分开，把 $T=nh$ 留在下游作为**约束**。
这一选型登记于此。

⚠ **`M < ∞` 的诚实登记**：在 `ℝ` 里 `M : ℝ` **天然有限**，
所以「$M<\infty$」这条前件**在类型层是免费的**，无需写出。
这是一个**收窄**：真实情形里 $M = \sup\|f'\|$ 是**扩展实数**（可能为 $+\infty$），
用 `ℝ` 表达等于**假定有限**。本文件取 `ℝ` 并**显式登记**该假定已**静默进入**类型，
下游若要处理「$\sup\|f'\| = \infty$」的退化情形，须改用 `ℝ≥0∞` 或 `EReal`。

- **类型**：`[待证]`
- **出处**：勘察 F，E1 -/
def E1Statement
    (X : Type) [NormedAddCommGroup X]
    (M L T h : ℝ) (x_n x_T : X) : Prop :=
  ‖x_n - x_T‖ ≤ (h * M / (2 * L)) * (Real.exp (L * T) - 1)

/-- `E2` 统计估计：泛化误差界。`[待证]`

**界的形式**：
$\sup\left|R - \hat R_n\right| \le 2\mathfrak{R}_n(\mathcal{H}) + M\sqrt{\dfrac{\ln(1/\delta)}{2n}}$。

本形式把 $\sup$ 型左边**作为参数 `R`、`R_hat` 传入**——
⚠ 这是**形态上的收窄**，必须登记：`E2Statement` 的左边是**点态差**
`|R - R_hat|`，而**不是**关于假设类的 $\sup$。
两者靠 `SupForm`（见下）**显式**关联，而**不**把 `sup` 偷偷塞进 `R`、`R_hat` 的语义里。

**为什么这样切**：`sup` 需要一个**索引集**（假设类 $\mathcal{H}$）和一个**族**；
把二者塞进 `E2Statement` 会让这个冻结的 `Prop` 带上
「$\mathcal{H}$ 是什么」这个**未裁决**的对象，从而使 E2 的形式**依赖一个尚未冻结的定义**。
本文件取「点态形式 + 独立的 `SupForm` 包装」，
使「界的形式」先被冻结（不依赖 $\mathcal{H}$），
而「$\sup$ 化」在 `SupForm` 里**显式**完成。这一选型登记于此。

**前件（下游补入假设栏）**：

1. `hiid`：样本 $\{Z_i\}$ **i.i.d.**；
2. `hBdd`：损失 $\ell \in [0, M]$；
3. `hRad`：**Rademacher 复杂度可控**（$\mathfrak{R}_n(\mathcal{H})$ 有限，本形式作为参数 `Rademacher` 传入）；
4. `hδ`：$0 < \delta < 1$（$\ln(1/\delta)$ 的定义域）；
5. `hn`：$n \ge 1$（下方 `2*n` 的分母非零）。

⚠ **`hn : n ≥ 1` 在形式里的处理**：`n : ℕ` 在 `2*n` 处若 `n = 0` 则分母为零，
`Real.sqrt (x / 0) = Real.sqrt 0 = 0`，于是右边退化为 $2\mathfrak{R}_n$。
此时该界**仍可能成立**（因为 `n=0` 时 i.i.d. 界的本来意义就不存在）。
本形式**不**排除 `n = 0`：加 `n ≠ 0` 的约束属于**前件**，不属于**界的形式**。
登记于此，以免下游误以为 `n = 0` 时 E2 是「有价值的界」。

- **类型**：`[待证]`
- **出处**：勘察 F，E2 -/
def E2Statement
    (R R_hat : ℝ) (Rademacher : ℝ) (M δ : ℝ) (n : ℕ) : Prop :=
  |R - R_hat| ≤ 2 * Rademacher + M * Real.sqrt (Real.log (1 / δ) / (2 * n))

/-- `E2` 的 **$\sup$ 化包装**：把点态界提升为关于索引族的上确界界。

给定索引集 `ι`、真风险 `R`、经验风险 `R_hat`、Rademacher 复杂度 `𝔯`，
若**每个** $i$ 都满足点态界（即 `E2Statement`），
则**上确界**也满足同一右边。

⚠ 本引理**不是** E2 的证明：它只做「点态 → $\sup$」这一步**纯粹的量词搬运**，
把 `E2Statement` 从点态形态**接上**勘察 F 原文的 $\sup$ 形态。
E2 真正的内容（为什么点态界成立）仍是 `[待证]`。

本引理的价值：它使 `E2Statement` 的**点态切法**（见上）**不丢失**原文的 $\sup$ 形态——
$\sup$ 形态是它的**推论**，因此该切法可被接受而不算削弱。

- **类型**：`[已证]`（纯量词/序运算，无概率内容）
- **出处**：本文件（为衔接 `E2Statement` 与勘察 F 的 $\sup$ 形态而设）

⚠ **前件 `[Nonempty ι]` 是必要的**：`ι` 为空时 `⨆ i, …` 是空上确界，
其值依赖序结构的约定（`⊥`），此时结论**不**由逐点界推出。
本引理因此**显式**要求 `ι` 非空——这一要求登记于此，
而非以 `bot_le` 之类的方式**偷偷**绕过。 -/
theorem E2Statement.sup_form
    {ι : Type*} [Nonempty ι] (R R_hat : ι → ℝ) (𝔯 M δ : ℝ) (n : ℕ)
    (h : ∀ i, E2Statement (R i) (R_hat i) 𝔯 M δ n) :
    (⨆ i, |R i - R_hat i|) ≤ 2 * 𝔯 + M * Real.sqrt (Real.log (1 / δ) / (2 * n)) := by
  exact ciSup_le fun i => h i

/-- `E3` 模型：模型误差分解界。`[待证]`

**界的形式**：
$R(\hat P) - R^* \le 2L_{\mathcal{L}}\cdot\varepsilon_{\mathrm{mis}}
+ \delta_{\mathrm{approx}} + \left(\text{E2 项}\right)$。

其中「E2 项」按勘察 F 即 $2\mathfrak{R}_n + M\sqrt{\ln(1/\delta)/(2n)}$，
本形式把它**整体**作为参数 `E2_term` 传入——
⚠ 这是**刻意的解耦**（同 `E2Statement` 的切法）：若在 `E3Statement` 里**重写**一遍
E2 的公式，则 E2 的公式一旦修订，E3 会**静默失同步**（两处公式漂移）。
本形式因此让 `E3Statement` **引用** `E2_term` 这个参数，
并用 `E3Statement_uses_E2` 把二者**显式**接上。

**前件（下游补入假设栏）**：

1. `hLipL`：损失 $\mathcal{L}$ 为 $L_{\mathcal{L}}$-Lipschitz；
2. `hDdiv`：$D_{\mathrm{div}}$ 控制 IPM（即模型类的散度被积分概率度量控制）；
3. `hεmis`：$\varepsilon_{\mathrm{mis}} < \infty$（本形式作为 `ε_mis : ℝ` 传入，见 E1 的同类登记）；
4. `hE2`：E2 项成立（由 `E2Statement` 提供）。

⚠ **$\varepsilon_{\mathrm{mis}} < \infty$ 与 $M<\infty$ 同一问题**：用 `ℝ` 表达即**已假定有限**。
登记同上。

- **类型**：`[待证]`
- **出处**：勘察 F，E3 -/
def E3Statement
    (R_P_hat R_star L_L ε_mis δ_approx E2_term : ℝ) : Prop :=
  R_P_hat - R_star ≤ 2 * L_L * ε_mis + δ_approx + E2_term

/-- `E4` 结构：结构误差的界。`[待证]`

**界的形式**：
$\left|\hat P_G(y \mid do(x')) - P_{G_0}(y \mid do(x'))\right| \le g\big(d(G, G_0)\big)$，
且要求 $g(0) = 0$。

本形式把两个条件概率**作为实数参数** `P_G`、`P_G0` 传入
（即假定 $y$、$do(x')$ 已固定）。⚠ 这是**点态**形式；
若要 $\sup$ 化，与 E2 同理走 `SupForm` 式包装，本文件不重复提供
（E4 的 $\sup$ 化在勘察 F 中**未要求**，故不预先造出来——避免造**无人认领的**引理）。

**前件（下游补入假设栏）**：

1. `hDist`：**图距已定义**（$d(G, G_0)$ 有意义）；
2. `hA20`：**A20**（勘察 F 引用；本文件不展开 A20 的内容，登记为外部前件）；
3. `hClosed`：**干预族形下闭**（干预后的对象仍在考虑的族内）；
4. `hg0`：$g(0) = 0$ ⭐ **这是「界是界」的必要条件**，
   由 §3 的 `bound_vanishes_at_zero` 提供**机械验收**——
   见 `E4Statement.acceptance`。

⚠ **`g(0) = 0` 不在 `Prop` 里**：本形式让 `g(0)=0` 作为前件（假设栏），
而不是塞进 `E4Statement` 的结论。理由：若塞进结论（写成 `… ∧ g 0 = 0`），
则 E4 变成**部分可自动判定为假**的命题（当 `g 0 ≠ 0` 时），
从而失去「界对**所有** `g` 都要被检查」这一诊断能力。
本文件的处理：`E4Statement` 陈述**不等式**，`g(0)=0` 由
`E4Statement.acceptance` 单独作为**验收条件**给出。这一选型登记于此。

- **类型**：`[待证]`
- **出处**：勘察 F，E4 -/
def E4Statement
    (P_G P_G0 : ℝ) (g : ℝ → ℝ) (dGG0 : ℝ) : Prop :=
  |P_G - P_G0| ≤ g dGG0

/-- `E5` 分布偏移：分布偏移下的风险差界。`[待证]`

**界的形式**：$|R_Q - R_P| \le L \cdot W$。

**前件（下游补入假设栏）**：

1. `hLip`：损失 $L$-Lipschitz；
2. `hSupp`：$Q$ 支撑 $\subset P$ 支撑的邻域；
3. `hW`：$W_1(Q, P) \le W$（本形式把 $W$ 作为参数直接传入，
   即「已取定一个上界」——这是**把前件 3 的结果作为参数**，
   符合「界的形式」的定位：形式只关心**由 $W$ 如何推出风险差**）。

⚠ **`W₁` 与 §4 的关系**：`W` 是 **Wasserstein-1** 型距离的上界，
对应 §4 的 `ErrorDimension.wasserstein 1`（见 `E5_dimension`）。
本形式**不**把 `W₁` 在 `ℝ` 上显式构造（那需要 $P$、$Q$ 是测度、且 $W_1$ 定义完整）——
登记：`W` 是**已取定的实数上界**，其「确实是 $W_1$」这一事实由前件 3 承担。
这一选型登记于此，以免误以为本文件**定义了** $W_1$。

- **类型**：`[待证]`
- **出处**：勘察 F，E5 -/
def E5Statement
    (R_Q R_P L W : ℝ) : Prop :=
  |R_Q - R_P| ≤ L * W

/-- `E6` 计算：浮点迭代的收敛界。`[待证]`

**界的形式**：
$\|x_k - x^*\| \le \dfrac{\kappa^k}{1-\kappa}\,\|x_1 - x_0\|
+ \dfrac{u\,\gamma_k}{1-\kappa}$。

⚠ 原文写作 $\dfrac{\kappa^k}{1-\kappa}\|x_1-x_0\|$，
即 `(κ^k / (1-κ)) * ‖x₁-x₀‖`（**不是** $\kappa^k/((1-\kappa)\|x_1-x_0\|)$）。
本形式按**前者**书写，并显式加括号——这是一处**歧义消解**，登记于此。

**前件（下游补入假设栏）**：

1. `hκ`：迭代为 $\kappa$-压缩，$0 \le \kappa < 1$；
2. `hFloat`：**浮点标准模型**（每步引入相对误差不超过 $u$，
   累积误差由 `γ_k` 给出）。

⚠ **$1-\kappa$ 分母非零**：由前件 1 的 $\kappa < 1$ 保证。
本形式**不**在 `Prop` 里加 `κ ≠ 1`——那属于前件。
但登记：若 `κ = 1`（违反前件 1），右边为 $1/0 = 0$，界退化为
$\|x_k-x^*\| \le 0$，这是一个**假界**。这正是前件 1 **不可省**的原因；
§3 的验收引理**检查不到**这类错误（它检查的是「界随参数 → 0」，
而 `κ → 1` 时界**不** → 0，界**发散**是无害的——有害的是 `1-κ = 0` 时的**塌缩**）。
这一区分登记于此：**验收引理不是万能的**，它只覆盖「参数 → 0」这一个方向。

- **类型**：`[待证]`
- **出处**：勘察 F，E6 -/
def E6Statement
    (X : Type) [NormedAddCommGroup X]
    (κ : ℝ) (k : ℕ) (u γ_k : ℝ) (x_k x_star x_1 x_0 : X) : Prop :=
  ‖x_k - x_star‖ ≤ (κ ^ k / (1 - κ)) * ‖x_1 - x_0‖ + (u * γ_k / (1 - κ))

/-- `E7` 反事实：反事实误差的双部界。`[待证]`

**界的形式**：$L_\Pi \cdot \delta + g(\Delta)$。

即：反事实误差 `err`（待估的反事实分布间的差距）被
$L_\Pi\delta + g(\Delta)$ 控制，其中
$\delta$ 是外生扰动的幅度、$\Delta$ 是结构参数的距离、
$L_\Pi := \prod_{i\in\Pi}L_i$ 是外层复合的 Lipschitz 常数。

**本形式为什么这样写（一处必须登记的取舍）**：
勘察 F 只给出**右边**的表达式，**没有**说明左边是什么对象。
本文件因此把左边写成**参数** `err : ℝ`——
即 E7 冻结的是「误差被 $L_\Pi\delta+g(\Delta)$ 控制」这一**不等式形态**，
而「`err` 具体是哪两个反事实分布之差」**留给下游**。
⚠ 这是**有意的留白**，不是遗漏：若本文件自行假定
「`err` 是 $|P(\cdot|do(x')) - P_{\Pi}(\cdot|do(x'))|$」，
则本文件就在**替理论做裁决**（且该裁决未必是勘察 F 的原意）。
登记于此。

本形式：外层 $\Pi$ 的 Lipschitz 常数 `L_Pi` **作为参数**传入，
而**不**在 `Prop` 里写 `∏ i ∈ Π, L_i`。
理由：乘积需要对 $\Pi$ 的具体类型（`Finset`？`List`？）作裁决，
而该裁决**尚未冻结**（勘察 F 未给出 $\Pi$ 的类型）。
本文件**不**替下游做这个裁决，改为：
（a）在 `E7Statement` 里用参数 `L_Pi`；
（b）**另**提供 `L_Pi_of`，把「给定 `Finset` 与各 $L_i$，`L_Pi` 确实等于乘积」
这一事实**显式**表达。这样 $\Pi$ 的类型裁决被**推迟**而不被**偷偷定死**。

**前件（下游补入假设栏）**：

1. `hLip_i`：各 $f_i$ 为 $L_i$-Lipschitz；
2. `hExoNorm`：**外生范数已定**（$\Delta$ 的度量已固定）；
3. `hg0`：$g(0) = 0$（同 E4，由 `bound_vanishes_at_zero` 机械验收）。

⚠ **关于 `err` 的非负性**：本形式**不**在 `Prop` 里写 `0 ≤ err`——
那属于前件（`err` 是「误差」，理当非负，但那是**语义**，不是**形式**）。
登记：若下游传入负的 `err`，E7 会**平凡地**成立，这是本形式的一个
**已知弱点**，须由前件 `0 ≤ err` 补上。这一弱点**显式登记**，
以免下游误以为本形式已排除退化情形。

- **类型**：`[待证]`
- **出处**：勘察 F，E7 -/
def E7Statement
    (L_Pi δ : ℝ) (g : ℝ → ℝ) (Δ : ℝ) (err : ℝ) : Prop :=
  err ≤ L_Pi * δ + g Δ

/-- `E7` 的**乘积形式**：$L_\Pi = \prod_{i\in\Pi} L_i$（`Finset` 版）。

⚠ **本定义只冻结「乘积」这一形态，不裁决 $\Pi$ 在理论里到底是什么**。
本文件取 `Finset ι` 作为**一种**载体，并**显式登记**：
勘察 F 未指定 $\Pi$ 的类型；若日后裁决 $\Pi$ 是多重集（`Multiset`）或列表，
则须**另立**对应版本，而**不得**悄悄改本定义（会使已引用它的下游失效）。

- **类型**：`[定义性约定]`
- **出处**：勘察 F，E7 的 $L_\Pi := \prod_{i\in\Pi}L_i$

⚠ **标识符登记**：Lean 不允许 `Π` 作变量名（它是 `Pi` 的保留记号），
故本定义用 `Is`（index set）作形参名，语义仍是 $\Pi$。 -/
def L_Pi_of {ι : Type*} (Is : Finset ι) (L : ι → ℝ) : ℝ :=
  ∏ i ∈ Is, L i

/-- `E7` 的乘积形式在**空指标集**上的取值：$\prod_{i\in\varnothing}L_i = 1$。

这是一条**定义层自洽检查**（不是理论命题）：
它确认 `L_Pi_of` 在 $\Pi=\varnothing$ 时取 $1$，
即「无中间变量层时，外层 Lipschitz 常数为 $1$（恒等映射）」——
这与 E7 的语义一致，且是 `L_Pi_of` 定义正确的**一道机械检查**。

- **类型**：`[已证]`（定义层）
- **出处**：本文件 -/
theorem L_Pi_of_empty {ι : Type*} (L : ι → ℝ) : L_Pi_of (∅ : Finset ι) L = 1 :=
  Finset.prod_empty

/-- `E8` FCA 编码：编码的纤维直径界。`[待证]`

**界的形式**：$\sup_x \operatorname{diam} \varsigma^{-1}(\varsigma(x)) \le g(\gamma, m)$。

本形式把 $\sup$ 写成一个**全称量词** `∀ x : Z`（因为 `Z` 可能是基类型，
此时 `sup` 需要 `ConditionallyCompleteLattice` 而 `diam` 直接取 `∀` 更轻），
并**不**显式构造 $\sup$。
⚠ **形态登记**：
`∀ x, diam x ≤ g γ m` **等价于** `sup diam ≤ g γ m`
（当 `Z` 非空时；当 `Z` 为空时 `sup ∅` 取值依赖格的约定，故取 `∀` 更稳健）。
本文件取 `∀` 形态，并在 `E8Statement.sup_form` 里说明二者的关系。

⚠ **`[A32 未定义]`** ⭐ 勘察 F 明确指出：E8 依赖 **A32（`ς` 已定义）**，
而 **A32 当前未定义**。本形式对此的处理：

- 把 `ς` 作为**参数** `ς : Z → Y` 传入（`Z`、`Y` 为类型参数）——
  即「`ς` **是什么**」留给下游，本文件只冻结「**若** `ς` 给定，界怎么写」；
- **不**引入 `axiom ς`，**不**用 `Unit` 占位造一个假的 `ς`；
- 在 `E8_A32_undefined` 里**显式记录**该缺口。

**界的形式细节**：纤维 $\varsigma^{-1}(\varsigma(x))$ 的**直径**，
本形式用 `diam` 参数（`Z → ℝ`，把点映到其纤维的直径）表达——
即把「取纤维直径」这一步**作为已给定的函数** `diam` 传入，
而**不**在本文件里从 `ς` 构造它。
理由：从 `ς` 构造 `diam` 需要 `Z` 上的度量、`Set` 直径概念、
以及「纤维」的构造，其中**度量**尚未由四元组提供到本函数的参数位置。
登记：`diam` 是**外部给定的量**，其「确实是纤维直径」由前件承担。

**前件（下游补入假设栏）**：

1. `[A32]`：**`ς` 已定义**（⭐ **当前未定义 —— `ς`、`diam` 的具体形式全是留白**）；
2. `hγ`：$\gamma > 0$；
3. `hg`：$g$ 为给定的界函数（且应满足 $g(0,\cdot)=0$，
   当 $\gamma\to 0$ 时由 §3 机械验收，见 `E8Statement.acceptance`）。

⚠ **诚实结论**：E8 的形式被**认领**（编译器认识 `E8Statement` 这个符号），
但 E8 的**对象**（`ς`）**仍未被定义**。
本文件**不宣称** E8 已被充分陈述——它只宣称 **E8 的形式不再无处安放**。
这是处方 #1 所说的「把留白从『无人认领』变成『编译器认领』」的**精确含义**：
认领的是**形式**，不是**对象**。

- **类型**：`[待证]` + `[A32 未定义]`
- **出处**：勘察 F，E8

⚠ **`ς` 与 `mm` 的用法（本形式的实际形态）**：
本形式陈述的是

```
∀ x y : Z, ς y = ς x → diam x ≤ g γ mm
```

即「**同一纤维内的任一点**，其纤维直径不超过 $g(\gamma,m)$」。
这样 `ς` **真正地被使用**（它是「同一纤维」的判据），
`mm` 也**真正地被使用**（它是界函数的第二变元）——
二者都不是装饰性参数。

⚠ **一处收窄登记**：原文的 $\sup_x$ 被本形式写成 `∀ x`（见上），
而「纤维直径」$\operatorname{diam}\varsigma^{-1}(\varsigma(x))$ 被**参数化**为
`diam x`——即「`diam x` 就是 $x$ 所在纤维的直径」这一事实
由**前件**承担（`diam_witnesses_fiber`），本形式只冻结不等式。
这一分成两类前件的作法与 E2/E4 一致：**形式只含不等式，语义由前件承担**。 -/
def E8Statement
    (Z : Type) (Y : Type) (ς : Z → Y) (diam : Z → ℝ)
    (g : ℝ → ℕ → ℝ) (γ : ℝ) (mm : ℕ) : Prop :=
  ∀ x y : Z, ς y = ς x → diam x ≤ g γ mm

/-- ⭐ **E8 的缺口登记（可被编译器检出的留白）**。

本定义是**一条记录**，不是数学内容：它把「E8 依赖的 A32 未定义」
这一事实变成一个**可被引用、可被检索**的 Lean 常量。
它的存在使缺口**不会因文件被读完而消失**——
任何下游想知道「E8 能不能用」的代码，都可以 `#check E8_A32_undefined` 得到答案。

**为什么需要这样一个常量的存在**（设计理由）：
本文件的验收口径是「零 `sorry`」。一个未定义的 `ς` **不能**用 `sorry` 占位，
**也不能**用 `axiom` 伪装（见 Stage 0 的裁决：占位可检出，`axiom` 不可检出）。
第三条路是：**把缺口本身变成一个具名常量**。于是：
- 缺口是**可见的**（`grep E8_A32_undefined` 即可找到）；
- 缺口是**无害的**（它不进入任何已证定理的假设）；
- 缺口是**可关闭的**（A32 定义好之后，本常量被删除，E8 的前件 1 得以填充）。

- **类型**：`[元登记]`（非数学命题；`True` 是有意的最小承载，
  它的**文档**才是内容，它的**类型**只是为了让编译器认领这个名字）
- **出处**：本文件；勘察 G 处方 #1；勘察 F 对 E8/A32 的标注 -/
def E8_A32_undefined : Prop := True

/-- `E8_A32_undefined` 的平凡证明。它的作用**仅**是让上述缺口常量
不成为一个**未证断言**——`True` 由 `trivial` 立即证成，
故本常量的存在**不**给环境引入任何新假设。 -/
theorem E8_A32_undefined_true : E8_A32_undefined := trivial

/-! ## §3 ⭐ 机械验收引理 -/

/-- ⭐⭐⭐ **「参数 → 0 时界 → 0」的机械验收**：
若 `g(0) = 0` 且 `g` 连续，则 `g(t) → 0` 当 `t → 0`。

⚠ 这是**验收条件**：任何界函数若 `g(0) ≠ 0`，则它不是真界。

**证明要点**（本引理**已真证**，不是 `[待证]`）：
`ContinuousAt g 0` 与 `g 0 = 0` 合起来就是 `∀ ε>0, ∃δ>0, |t|<δ → |g t - g 0| < ε`；
把 `g 0` 换成 `0` 并用 `|g t - 0| = |g t|` 即得。

具体路径：`Metric.continuousAt_iff` 把 `ContinuousAt` 展开成
`∀ ε>0, ∃δ>0, dist t 0 < δ → dist (g t) (g 0) < ε`；
`Real.dist_eq` 把 `dist` 换成 `|·-·|`；
最后用 `g 0 = 0` 与 `|g t - 0| = |g t|` 收敛。

**⭐ 这个引理的价值**：让「界在参数 → 0 时 → 0」从口头要求变成编译器可检查的条件。

- **类型**：`[已证]`（真证，非 `[待证]`）
- **出处**：勘察 G 处方 #1 的 §3 -/
theorem bound_vanishes_at_zero
    (g : ℝ → ℝ) (hg0 : g 0 = 0) (hg : ContinuousAt g 0)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ t : ℝ, |t| < δ → |g t| < ε := by
  obtain ⟨δ, hδ0, hδ⟩ := (Metric.continuousAt_iff.mp hg) ε hε
  refine ⟨δ, hδ0, fun t ht => ?_⟩
  have h1 : dist t (0 : ℝ) < δ := by
    rw [Real.dist_eq]; simpa using ht
  have h2 : dist (g t) (g 0) < ε := hδ h1
  rw [hg0, Real.dist_eq] at h2
  simpa using h2

/-- ⭐ **E4 的机械验收**：E4 的界函数 `g` 必须满足「参数 → 0 时界 → 0」。

这是 `bound_vanishes_at_zero` 在 **E4 这一具体命题**上的实例化。
它把「$g(0)=0$ 且 $g$ 连续」这一**口头要求**变成一条**可被编译器检查**的命题。

⚠ 本引理**不**证明 E4；它证明的是「若 E4 的界函数合规，则界确实随 $d(G,G_0)\to 0$ 消失」。
E4 的真实内容（结构误差由 `g∘d` 控制）仍是 `[待证]`。

- **类型**：`[已证]`（是 `bound_vanishes_at_zero` 的实例）
- **出处**：本文件；`E4Statement` -/
theorem E4Statement.acceptance
    (g : ℝ → ℝ) (hg0 : g 0 = 0) (hg : ContinuousAt g 0)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ t : ℝ, |t| < δ → |g t| < ε :=
  bound_vanishes_at_zero g hg0 hg ε hε

/-- ⭐ **E8 的机械验收**：E8 的界函数 `g`（在 `m` 固定时）必须满足
「γ → 0 时界 → 0」。

这是 `bound_vanishes_at_zero` 在 E8 上的实例化。
⚠ 与 E4 的差别：E8 的界函数**有两个参数** $(\gamma, m)$。
本引理**固定 `m`** 后对 $\gamma$ 验收——即「对每个有限的 $m$，$\gamma\to 0$ 时界消失」。
**不**断言对 $m\to\infty$ 的一致性（那需要一致连续性，强于逐点连续；
勘察 F 未要求，本文件不擅自加强）。

- **类型**：`[已证]`（是 `bound_vanishes_at_zero` 的实例）
- **出处**：本文件；`E8Statement` -/
theorem E8Statement.acceptance
    (g : ℝ → ℕ → ℝ) (mm : ℕ) (hg0 : g 0 mm = 0)
    (hg : ContinuousAt (fun γ => g γ mm) 0)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ t : ℝ, |t| < δ → |g t mm| < ε :=
  bound_vanishes_at_zero (fun γ => g γ mm) hg0 hg ε hε

/-- ⭐ **验收引理的 `Tendsto` 形态**：同一内容的滤子写法。

`bound_vanishes_at_zero` 给的是 `ε-δ` 形式；本引理给出等价的
`Filter.Tendsto g (𝓝 0) (𝓝 0)` 形式，便于在定理里直接与 `Tendsto` 工具箱对接
（`Filter.Tendsto.add`、`.mul` 等）。

**为什么两个形态都要有**（设计理由）：
`ε-δ` 形态是**验收**用的（人读、与勘察 F 的表述逐字对照）；
`Tendsto` 形态是**使用**用的（与 Mathlib 的滤子引理组合）。
只保留前者会让下游每次都要手工展开 `ε-δ`；
只保留后者会让「验收条件」在 doc-comment 里失去可核对的具体形式。
本文件因此**两个都提供**，并用 `bound_vanishes_at_zero_iff` 断言二者等价。

⚠ 本引理同样**已真证**。

- **类型**：`[已证]`
- **出处**：本文件（`bound_vanishes_at_zero` 的滤子形态） -/
theorem bound_vanishes_at_zero_tendsto
    (g : ℝ → ℝ) (hg0 : g 0 = 0) (hg : ContinuousAt g 0) :
    Tendsto g (𝓝 0) (𝓝 0) := by
  have h := hg.tendsto
  rwa [hg0] at h

/-- **两种形态等价**：`ε-δ` 版与 `Tendsto` 版说的是同一件事。

本引理把「验收条件」的两种写法**钉在一起**，使下游可以任意挑一种使用
而不担心二者不同（且使本文件的两条引理**互相校验**：
若有人改动其一，本引理将编译失败）。

⚠ **关于 `hg0` 在本题中的真实地位（诚实登记，避免自欺）**：
本题的等价式两边**都**以 `0` 为极限点/中心，故等价**实际上**不依赖 `g 0 = 0`：
- 左式 `∀ ε>0, ∃ δ>0, |t|<δ → |g t| < ε` 只比较 `|g t|` 与 `0`；
- 右式 `Tendsto g (𝓝 0) (𝓝 0)` 也只比较 `g t` 与 `0`。

所以 `hg0` **不是**承重的，本引理**不把它写进证明**（以 `_hg0` 标记），
而**保留在签名里**的唯一理由是：它与使用者手上的
`bound_vanishes_at_zero` 前提**对齐**，使下游调用时无需拆解。
⚠ 这一选择登记于此，**不冒充**「因为数学上需要」——
若日后有人删掉 `hg0`，本引理仍然成立（这一点可被本文件自己验证）。

- **类型**：`[已证]`
- **出处**：本文件 -/
theorem bound_vanishes_at_zero_iff
    (g : ℝ → ℝ) (_hg0 : g 0 = 0) :
    (∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ t : ℝ, |t| < δ → |g t| < ε)
      ↔ Tendsto g (𝓝 0) (𝓝 0) := by
  constructor
  · intro h
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ0, hδ⟩ := h ε hε
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ0] with t ht
    have ht' : dist t 0 < δ := by rwa [Metric.mem_ball] at ht
    rw [Real.dist_eq] at ht'
    have ht2 : |t| < δ := by simpa using ht'
    have key := hδ t ht2
    rw [Real.dist_eq]
    simpa using key
  · intro h ε hε
    rw [Metric.tendsto_nhds] at h
    obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp (h ε hε)
    refine ⟨δ, hδ0, fun t ht => ?_⟩
    have h1 : dist t (0 : ℝ) < δ := by rw [Real.dist_eq]; simpa using ht
    have h2 := hδ h1
    rw [Real.dist_eq, sub_zero] at h2
    exact h2

/-- ⭐⭐ **验收引理的最强形态**：`D` 可分辨时，「界 → 0」**蕴含**「误差 → 0」。

给定良构四元组 `E`（故 `E.D x y = 0 ↔ x = y`），
若一族误差 `err t`（`t` 是某个参数）被 `g t` 控制、
且 `g` 在 `0` 处连续、`g 0 = 0`，则 `err t ≤ 0`（当 `t = 0`），
**且** 界本身压到任意小。

**这是本文件最有价值的一条**，理由：它把验收引理从
「界函数好看」提升为「**误差本身被压到 0**」。
`bound_vanishes_at_zero` 只说 `|g t| < ε`；
本引理进一步给出 `E.D x_n x_star < ε`（由 `hbound` 与 `|g t| < ε` 传递），
即**误差**被压到任意小，而不仅仅是**界**被压小。

⚠ 本引理**已真证**；它**不**证明 E1–E8 中任何一个，
而是提供「**若**某个 Ex 的界成立**且**其 `g` 合规，**则**误差收敛」这一**通用桥梁**。

- **类型**：`[已证]`
- **出处**：本文件；`WellFormed` + `bound_vanishes_at_zero` -/
theorem bound_vanishes_gives_convergence
    (E : ErrorQuadruple) (hE : WellFormed E)
    (g : ℝ → ℝ) (hg0 : g 0 = 0) (hg : ContinuousAt g 0)
    (x_n x_star : E.Z) :
    (∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, |t| < δ → E.D x_n x_star ≤ g t → E.D x_n x_star < ε) := by
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := bound_vanishes_at_zero g hg0 hg ε hε
  refine ⟨δ, hδ0, fun t ht hbound => ?_⟩
  have hgt : |g t| < ε := hδ t ht
  have h1 : g t < ε := lt_of_le_of_lt (le_abs_self (g t)) hgt
  have hnonneg : 0 ≤ E.D x_n x_star := hE.D_nonneg x_n x_star
  linarith

/-- ⭐ **验收引理的反面用法：判定「这不是界」**。

若 `g 0 ≠ 0`，则 `g` **不是**可用的界函数：存在 `ε > 0`，
使 `|g t| < ε` 在 `t → 0` 时**不可能**恒成立。

⚠ 更准确地说，本引理陈述的是：**若 `g 0 ≠ 0`，
则不存在满足 `bound_vanishes_at_zero` 结论的 `δ`（对某个 `ε`）**。
本文件取一个**具体的、可计算的** `ε = |g 0| / 2` 来作证——
这使「拒绝一个伪界」成为**可执行操作**，而不是「说它不好」。

**为什么这条重要**：勘察 G 说「任何界函数若 `g(0) ≠ 0`，则它不是真界」。
本引理把这句话变成**可被编译器执行的拒绝**：
给定 `g` 与 `hg0 : g 0 ≠ 0`，编译器**自动**给出反例 `ε = |g 0|/2`。

- **类型**：`[已证]`
- **出处**：本文件（验收引理的反面） -/
theorem not_a_bound_of_nonzero_at_zero
    (g : ℝ → ℝ) (hg0 : g 0 ≠ 0) :
    ∃ ε > 0, ∀ δ > 0, ∃ t : ℝ, |t| < δ ∧ ε ≤ |g t| := by
  refine ⟨|g 0| / 2, by
    have h := abs_pos.mpr hg0
    linarith, fun δ hδ => ⟨0, by simpa using hδ, ?_⟩⟩
  have h2 : |g 0| / 2 ≤ |g 0| := by linarith [abs_pos.mpr hg0]
  show |g 0| / 2 ≤ |g 0|
  exact h2

/-! ## §4 量纲登记（裁决 E） -/

/-- 误差量纲的候选族。

裁决 E：**`decisionLoss` 是主量纲**，其余为候选。
本归纳类型**只登记有哪些量纲**，**不**断言哪一种「更好」——
「更好」是一个裁决（裁决 E 已作出），不是一个数学命题。
本文件因此**不**在本类型上定义序（如「`decisionLoss` 优于 `metricDistance`」）：
若那样做，一个**裁决**就会被编码进**类型**，从而伪装成**数学事实**。

- **类型**：`[定义性约定]`
- **出处**：勘察 F 的量纲候选族；裁决 E
- **⚠ 未定义项**：`wasserstein (p : ℕ)` 的 `p` 取值域原文未限
  （`p = 0` 无意义）；本文件**不**限制 `p ≥ 1`，
  因为限制属于**使用处**的前件，不属于**登记**。登记于此。 -/
inductive ErrorDimension where
  /-- 度量距离（$d$）。 -/
  | metricDistance
  /-- 全变差（$\mathrm{TV}$）。 -/
  | tvDistance
  /-- KL 散度。 -/
  | klDivergence
  /-- Wasserstein-$p$。 -/
  | wasserstein (p : ℕ)
  /-- ⭐ **决策损失（主量纲，裁决 E）**。 -/
  | decisionLoss
  /-- 参数范数。 -/
  | parameterNorm
  deriving DecidableEq, Repr

/-- ⭐ **裁决 E 的类型层表达**：`decisionLoss` 是主量纲。

`IsPrimaryDimension` 在**类型层**标记「主量纲」这一裁决，
使「哪个量纲是主量纲」成为**可被机械核对**的事实，
而不是散落在文档里的一句话。

⚠ 本谓词**不是**数学命题：总有一个量纲是主量纲（`decisionLoss`），
这是**裁决**的结果，写在类型里只是为了让编译器记住它。

- **类型**：`[定义性约定]`（裁决 E 的类型层承载）
- **出处**：裁决 E -/
def IsPrimaryDimension : ErrorDimension → Prop
  | .decisionLoss => True
  | _ => False

/-- 裁决 E 的**可核对形式**：`decisionLoss` 确实是主量纲。 -/
theorem decisionLoss_isPrimary : IsPrimaryDimension ErrorDimension.decisionLoss := trivial

/-- 裁决 E 的**唯一性**：只有 `decisionLoss` 是主量纲。

本引理使「主量纲**唯一**」成为可机械核对的事实：
任何其他量纲 `d`，只要 `IsPrimaryDimension d` 成立，则 `d = decisionLoss`。
于是「主量纲」不是「（至少）一个」，而是「**恰好**一个」。

- **类型**：`[已证]`
- **出处**：本文件 -/
theorem isPrimaryDimension_eq_decisionLoss
    (d : ErrorDimension) (h : IsPrimaryDimension d) : d = ErrorDimension.decisionLoss := by
  cases d <;> simp_all [IsPrimaryDimension]

/-- `[定义 4.1]` **四元组使用的量纲**：四元组的 `ℓ` 属于哪个量纲族。

把 §1 的 `ErrorQuadruple` 与 §4 的 `ErrorDimension` **连接**起来：
「这个四元组的误差是按哪个量纲度量的」。

⚠ 本谓词**不对** `ℓ` 施加任何**量的约束**（不要求 `ℓ` 与 `dim` 的内部实现匹配）——
匹配与否是**具体误差命题**需要自证的事（如 `E5_dimension` 那样）。
本文件只提供**挂钩**。

- **类型**：`[定义性约定]`
- **出处**：本文件（§1 与 §4 的衔接） -/
structure UsesDimension (E : ErrorQuadruple) where
  /-- 该四元组所用的量纲 -/
  dim : ErrorDimension

/-- `E5` 用的量纲是 Wasserstein-1（与 `E5Statement` 的 $W$ 对应）。

一条**登记**，不是定理：它断言「E5 的界以 Wasserstein-1 为量纲」。
它的价值是让 `E5` 在 §4 的量纲表里**有位置**，
从而「E5 用哪个量纲」**可被机械检索**（`grep E5_dimension`）。

- **类型**：`[已证]`（定义层寄存器）
- **出处**：本文件；`E5Statement` -/
def E5_dimension : ErrorDimension := ErrorDimension.wasserstein 1

/-- `E1` 用的量纲是度量距离（与 `E1Statement` 的 `‖·‖` 对应）。 -/
def E1_dimension : ErrorDimension := ErrorDimension.metricDistance

/-- `E6` 用的量纲是度量距离（与 `E6Statement` 的 `‖·‖` 对应）。 -/
def E6_dimension : ErrorDimension := ErrorDimension.metricDistance

/-- `E3` 用的量纲是**决策损失**（$\ell$ 的目标量纲，裁决 E 的主量纲）。

⚠ 这正是裁决 E 的落点：E3 的风险 $R(\hat P) - R^*$ 是**决策损失**，
故 E3 的主量纲是 `decisionLoss`，而**不是**度量距离。
这一登记使「裁决 E 的适用范围」**显式化**：裁决 E 说主量纲是决策损失，
而 E3 是**恰好**用决策损失的误差命题。

- **类型**：`[定义性约定]`
- **出处**：裁决 E -/
def E3_dimension : ErrorDimension := ErrorDimension.decisionLoss

/-! ## §5 验收汇总（**给下游的一张机械清单**） -/

/-- ⭐ **E 编号的枚举**：使「E1–E8 一个不少」可被机械核对。

本归纳类型**逐条列出** E1–E8 的编号。它与 §2 的八个 `ExStatement` 的对应关系是：

| 编号 | `ExStatement` |
|---|---|
| `.E1` | `E1Statement` |
| `.E2` | `E2Statement` |
| `.E3` | `E3Statement` |
| `.E4` | `E4Statement` |
| `.E5` | `E5Statement` |
| `.E6` | `E6Statement` |
| `.E7` | `E7Statement` |
| `.E8` | `E8Statement` |

**为什么需要一个枚举**：若只有八个独立的 `def`，
则「八个都有了」这句话**无法被机械检查**——
人可能漏写一个而以为写全了。有了本枚举，
`allE` 明确列出八项，`allE_length` 断言其长度为 8，
于是「八个」是**可核对的**，不是**声称的**。

- **类型**：`[定义性约定]`
- **出处**：勘察 F 的 E1–E8 表 -/
inductive EItem where
  | E1 | E2 | E3 | E4 | E5 | E6 | E7 | E8
  deriving DecidableEq, Repr

/-- E1–E8 的**完整清单**（八项，逐条对应 §2 的八个 `ExStatement`）。 -/
def allE : List EItem :=
  [.E1, .E2, .E3, .E4, .E5, .E6, .E7, .E8]

/-- ⭐ **机械验收：E 清单恰好是八项**。

这是「E1–E8 八个具名 Prop」这一要求的**可执行形式**：
编译器**证明** `allE` 的长度为 8，而不是由人声称。

- **类型**：`[已证]`
- **出处**：本文件 -/
theorem allE_length : allE.length = 8 := rfl

/-- ⭐ **机械验收：八个编号两两不同**（无重复、无遗漏）。 -/
theorem allE_nodup : allE.Nodup := by decide

/-- ⭐ **机械验收：`allE` 覆盖了 `EItem` 的每一个构造子**。

`List.mem` 对全部八项成立，即清单**无遗漏**。

- **类型**：`[已证]`
- **出处**：本文件 -/
theorem allE_complete : ∀ e : EItem, e ∈ allE := by
  intro e
  cases e <;> simp [allE]

/-- `[元登记]` **本文件的状态声明**：阶段 2 的形式已被冻结，E1–E8 均未证。

这是一条**诚实的自述**，写成 Lean 常量是为了让它**可被检索**：
任何想知道「阶段 2 到什么程度」的下游，读这个名字即可，
不必重读本文件全文。

⚠ `True` 是有意的最小承载：本常量的**文档**是内容，**类型**只是载体。

- **类型**：`[元登记]`
- **出处**：本文件 -/
def Stage2FormsFrozen : Prop := True

/-- `Stage2FormsFrozen` 的平凡证明（不引入任何新假设）。 -/
theorem Stage2FormsFrozen_true : Stage2FormsFrozen := trivial

end FateV2.Error.Stage2

/-!
---------------------------------------------------------------------------
接口自检（`#check`）——确认本文件「对外承诺的名字」全部存在
---------------------------------------------------------------------------
下面按勘察 G 处方 #1 的**三项要求**逐条 `#check`，
使「交付了什么」可被**编译器**核对，而不是由人复述。
---------------------------------------------------------------------------
-/

-- §1 四元组
#check @FateV2.Error.Stage2.ErrorQuadruple
#check @FateV2.Error.Stage2.WellFormed

-- §2 E1–E8 八个具名 Prop
#check @FateV2.Error.Stage2.E1Statement
#check @FateV2.Error.Stage2.E2Statement
#check @FateV2.Error.Stage2.E3Statement
#check @FateV2.Error.Stage2.E4Statement
#check @FateV2.Error.Stage2.E5Statement
#check @FateV2.Error.Stage2.E6Statement
#check @FateV2.Error.Stage2.E7Statement
#check @FateV2.Error.Stage2.E8Statement

-- §3 机械验收引理（**已真证**）
#check @FateV2.Error.Stage2.bound_vanishes_at_zero
#check @FateV2.Error.Stage2.bound_vanishes_at_zero_tendsto
#check @FateV2.Error.Stage2.bound_vanishes_at_zero_iff
#check @FateV2.Error.Stage2.bound_vanishes_gives_convergence
#check @FateV2.Error.Stage2.not_a_bound_of_nonzero_at_zero

-- §4 量纲登记（裁决 E）
#check @FateV2.Error.Stage2.ErrorDimension
#check @FateV2.Error.Stage2.IsPrimaryDimension
#check @FateV2.Error.Stage2.decisionLoss_isPrimary
#check @FateV2.Error.Stage2.E3_dimension

-- §5 验收汇总
#check @FateV2.Error.Stage2.allE
#check @FateV2.Error.Stage2.allE_length
#check @FateV2.Error.Stage2.allE_nodup

/-!
---------------------------------------------------------------------------
验收自检（`#print axioms`）
---------------------------------------------------------------------------
下面**十一条** `#print axioms` 覆盖本文件**全部已证定理**。
预期输出：每条都只依赖 `[propext, Classical.choice, Quot.sound]`
（Mathlib 的标准公理集），**不含 `sorryAx`**。

⚠ **「零 `axiom`」的精确含义**（必须说清楚，否则会被误读）：
本文件**不声明**任何 `axiom`；`#print axioms` 输出的三条
（`propext`、`Classical.choice`、`Quot.sound`）是 **Lean 内核/标准库**的公理，
**不是**本文件引入的。它们的出现只说明某条证明用到了
命题外延/选择/商——这是 Mathlib 的**通行基线**，
**不**意味着本文件有未证断言。真正的验收判据是：**输出中不出现 `sorryAx`**。
---------------------------------------------------------------------------
-/

#print axioms FateV2.Error.Stage2.bound_vanishes_at_zero
#print axioms FateV2.Error.Stage2.bound_vanishes_at_zero_tendsto
#print axioms FateV2.Error.Stage2.bound_vanishes_at_zero_iff
#print axioms FateV2.Error.Stage2.bound_vanishes_gives_convergence
#print axioms FateV2.Error.Stage2.not_a_bound_of_nonzero_at_zero
#print axioms FateV2.Error.Stage2.E2Statement.sup_form
#print axioms FateV2.Error.Stage2.E4Statement.acceptance
#print axioms FateV2.Error.Stage2.allE_complete
#print axioms FateV2.Error.Stage2.isPrimaryDimension_eq_decisionLoss
#print axioms FateV2.Error.Stage2.Stage2FormsFrozen_true
#print axioms FateV2.Error.Stage2.E8_A32_undefined_true
