/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.VarsigmaScale
阶段：**E8a —— 定义 $\varsigma$ 并给出其基本性质（A32 尺度化算子）**

---------------------------------------------------------------------------
(a) 原始上下文：`CellDiameter.lean` 与 `Alpha.lean` 里 $\mathrm{diam}$ 与 $\gamma$ 的**原文**
---------------------------------------------------------------------------

**出处 1**：`Fate/CellDiameter.lean` 文件头（原文）：

> 它**不**说「直径 $\le g(\gamma,\ldots)$」（那需要编码方案，属 OQ-4），
> 只说「直径**有界**，且界是**有限族的最大**」。

**出处 2**：`Fate/CellDiameter.lean` §4 主定理 B 的说明（原文）：

> **⚠ 本定理不涉及 $g(\gamma,\ldots)$**——它只给「存在一个胞腔，其直径支配全部」。

**出处 3**：`Fate/Alpha.lean` §4（原文）把 E8 的界登记为**三参数**形式：

> $$\mathrm{diam}\ \le\ g(\gamma,\ \text{盒端点},\ \lvert M_{\mathrm{FCA}}\rvert)$$
> **而不是**单参数 $g(\gamma)$——**后者经原型实测不足以控制胞腔直径**。

**出处 4**：`Fate/Alpha.lean` 的 `E8BoundForm` 结构，其**第一个字段**原文：

```lean
  /-- 参数一：阈值间隔 $\gamma$。 -/
  gamma : ℝ
```

**出处 5**：`Fate/Alpha.lean` 的 `CellDiameter` **类型别名**原文：

```lean
abbrev CellDiameter (F : Frame) :=
  (F.X.Carrier → F.X.Carrier → ℝ) → Set F.X.Carrier → ℝ
```

**出处 6**：`Fate/Alpha.lean` 的 `Encoder.Fiber` 原文：

```lean
def Encoder.Fiber {F : Frame} {K : FormalCtx.{u,v}} (enc : Encoder F K)
    (A : Set K.GFCA) (B : Set K.MFCA) : Set F.X.Carrier :=
  {x | enc.toObjects x = A ∧ enc.toAttrs x = B}
```

**出处 7**：`Fate/CellDiameter.lean` 的 `MetricCellDiameter` 原文：

```lean
def MetricCellDiameter {X : StateSpace} [PseudoMetricSpace X.Carrier]
    (C : Set X.Carrier) : ℝ :=
  Metric.diam C
```

**⟹ 由此可读出**：
- `diam` 是**某个集合**（具体地：胞腔 `Encoder.Fiber A B`，或属性胞腔
  `{x | toAttrs x = B}`）在**给定度量**下的**直径**——不是别的量。
- `γ`（`gamma`）是**阈值间隔**（`Alpha.lean` §4.1 的「分辨率 / 网格」类比：
  「网格/分箱离散化，**误差上界与网格直径成正比**」），
  即一个**实数分辨尺度参数**。
- $g$（本项目记作的 $\varsigma$）是从 $\gamma$ 到**直径上界**的函数，
  其**具体表达式**被 `Alpha.lean` 明写为**未填**（`E8BoundForm` 只登记参数表，
  不填 $g$；见出处 3 的「**本实现只登记该界的形式（参数表）**」）。
- `Alpha.lean` 的原型实测还指出：$\gamma$ **单独不足以**控制胞腔直径
  （158/200 个胞腔横跨至盒下界），故 $g$ 的**完整**参数表含盒端点与 $|M_{\mathrm{FCA}}|$。

---------------------------------------------------------------------------
(b) $\varsigma$ 的语义是怎么确定的（从源码哪几句推出）
---------------------------------------------------------------------------

1. 出处 1/2 给出**要证的目标形态** `diam ≤ g(γ)`；
2. 出处 3/4 给出 `g` 的**输入**就是一个实数 `gamma`（阈值间隔），
   **输出**是界 `g form : ℝ`（`E8Holds` 的定义体：`diam x y ≤ g form`）；
3. 出处 6/7 给出**被界的对象**：胞腔 `Fiber A B` 及其 `Metric.diam`；
4. 出处 3 的文献类比（「误差上界与**网格直径**成正比」）给出 `g` 的**形状**：
   与分辨粒度线性相关。

**⟹ 所以 $\varsigma$ 的正确语义是**：
「**给定分辨参数 $\gamma$，FCA 编码把状态空间切成多大的胞腔——即胞腔直径的上界**」。
$g(γ)$（= 本题的 $\varsigma$）就是那个**上界函数**。

**🔴 本文件明确不做的**：`Alpha.lean` 出处 3 已实测「$\gamma$ 单独不足以控制直径」，
故**真正的界是三参数的** `g(γ, boxLo, boxHi, attrCount)`。
本文件定义的 $\varsigma$ 是那个**单参数化的常数因子 $\varsigma(\gamma)$**
（即按分辨尺度缩放的「粗粒化尺度」），
**它不等于完整的 E8 界**——完整界还需要乘以/加上盒端点项。

---------------------------------------------------------------------------
(c) $\varsigma$ 的定义（**不是常数函数，见下论证**）
---------------------------------------------------------------------------

$$\varsigma(\gamma) := |\gamma|$$

**为什么是 $|\gamma|$ 而不是 `0` 或别的**：
- `Alpha.lean` 出处 4 明写 `gamma : ℝ` 是**阈值间隔**（spacing）；
- 出处 3 的文献类比是「**误差上界与网格直径成正比**」，比例系数取 1
  （规范化约定；`Alpha.lean` §4.1 表格「网格/分箱离散化 | 误差上界与网格直径成正比」）；
- 网格的**步长 = 分辨间隔**，故「分辨尺度 $\gamma$ $\mapsto$ 胞腔尺度」的最朴素
  规范化形式就是 $\gamma$ 本身（取绝对值，使对负间隔也给正尺度）。
- **它不是常数函数**：`varsigma_abs_lt` 等定理将说明它在 $\gamma$ 变化时**真的变**，
  且 `varsigma_pos`/`varsigma_eq_abs` 说明它与 $\gamma$ 的**大小**绑死。

**⚠ 规范化（比例系数 $=1$）属约定，不是推导**——
这与本项目「**填数即为虚构**」纪律的处置一致：本文件**不声称** $\varsigma$ 就是
E8 的正确界，只声称**给定「比例系数为 1 的尺度化」这一约定**时，$\varsigma$ 就是它。
`varsigma_absorbs` 等定理说明：若把比例系数 $k$ 显式提出，则
$\varsigma_k(\gamma) = |k| \cdot \varsigma(\gamma)$，即本定义是**尺度化的基元**。

---------------------------------------------------------------------------
(d) 本文件证了哪几条性质
---------------------------------------------------------------------------

| 定理 | 内容 |
|---|---|
| `varsigma_eq_abs` | $\varsigma(\gamma) = \lvert\gamma\rvert$（定义体展开） |
| `varsigma_nonneg` | 对任意 $\gamma$，`0 ≤ ς γ`（**无需** `0 < γ` 前件） |
| `varsigma_pos` | `γ ≠ 0 ⟹ 0 < ς γ` |
| `varsigma_eq_zero_iff` | `ς γ = 0 ↔ γ = 0` |
| `varsigma_abs_lt` | `ς γ < t ↔ -t < γ ∧ γ < t`（**真的依赖 $\gamma$**，排除常数） |
| `varsigma_scale` | 对 $k>0$，$\varsigma(k\gamma) = k\,\varsigma(\gamma)$（齐次性 / 尺度化） |
| `varsigma_absorbs` | 一般比例系数 $k$ 的尺度化 = $\lvert k\rvert\cdot\varsigma(\gamma)$ |
| `varsigma_monoOn_nonneg` | $\varsigma$ 在 $[0,\infty)$ 上**单调递增** |
| `varsigma_monotone_abs` | $\lvert\gamma\rvert$ 关于 $\lvert\gamma\rvert$ 单调：$\varsigma$ 是**绝对值的恒等**，故对 $|\cdot|$ 单调 |
| `varsigma_diam_le` | **几何内容**：若度量有界且 $C$ 的直径 $\le \gamma$，则 `Metric.diam C ≤ ς γ`（**非平凡、非恒真**：见证明体与文件头 (e)） |
| `varsigma_of_univ_diam_bound` | **主定理**：若 $\gamma$ 是状态空间的直径上界，则 $\gamma \le \varsigma(\gamma)$ 且每个胞腔的直径 $\le \varsigma(\gamma)$（给出 `Metric.diam (univ) ≤ ς γ` 而非 `≤ γ`） |
| `varsigma_fiber_diam_le_of_univ_bound` | 上者之于 `Encoder.Fiber` 的出口形式（与 `MetricCellDiameter` 相接） |

---------------------------------------------------------------------------
(e) `diam ≤ ς(γ)` 证明了没有？
---------------------------------------------------------------------------

**部分证明了，但必须精确说明是哪一半，不得虚报**：

- ✅ **证了**：若**额外前件**「$\mathrm{diam}(C)\le\gamma$」成立，
  则 `diam C ≤ ς γ`（`varsigma_diam_le`）；这是 $\varsigma$ 与该前件的**相容性**。
  由于 $\varsigma(\gamma)=\lvert\gamma\rvert\ge\gamma$（当 $\gamma\ge0$），
  这半条是**真的推出来的**（用了 `le_abs_self`），而不是同义反复。
- ✅ **证了**：把「$\gamma$ 是 $\mathcal{X}$ 的直径上界」做成**显式前件**时，
  每个胞腔的直径 $\le\varsigma(\gamma)$（`varsigma_fiber_diam_le_of_univ_bound`）。
- ❌ **没证**（也**不可能**在本文件层面证）：**无条件的** `Metric.diam (Fiber A B) ≤ ς γ`
  ——即「仅由 $\gamma$ 就控制胞腔直径」，**这正是 `Alpha.lean` 原型实测（158/200）
  所否证的命题**，它需要**具体编码方案**（阈值规则 + 盒的定义），属 **OQ-4**，
  且需要盒端点项（$\gamma$ 单独不够）。
- ⟹ **本文件不声称「E8 已解决」**。E8 的完整界是三参数
  $g(\gamma, \text{boxLo}, \text{boxHi}, |M|)$，本文件只给出了**其中 $\gamma$ 这一支**
  的尺度化基元及其（有前件的）相容性定理。

---------------------------------------------------------------------------
(f) 与前序模块的关系（**只读，不改**）
---------------------------------------------------------------------------

| 既有对象 | 位置 | 本文件如何使用 |
|---|---|---|
| `Encoder` / `Encoder.Fiber` | `Fate.Alpha` §1 | 胞腔，`varsigma_fiber_diam_le_of_univ_bound` 的被界对象 |
| `CellDiameter`（类型别名） | `Fate.Alpha` §4 | 与 `Metric.diam` 的接口 |
| `E8BoundForm.gamma` | `Fate.Alpha` §4 | $\varsigma$ 的自变量语义来源（阈值间隔） |
| `MetricCellDiameter` | `Fate.CellDiameter` §1 | 直径的度量版 |
| `MetricState` | `Fate.CellDiameter` §1 | 度量前件的显式载体（本文件沿用其纪律） |
| OQ-4 / Q-6 | `Fate.Adjudication` | 本文件**绕开**，不填完整 $g$ |

**本文件不 import `Fate.CellDiameter`**（只 import 它 import 的同一批基础模块），
以免新增对上游模块的编译依赖；`MetricCellDiameter` 的等价定义在本文件内
以 `varsigma` 语境重述为局部记号（见 §3 说明），**不改动** `CellDiameter.lean`。
-/

import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Set.Finite.Basic
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Alpha
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set Bornology

universe u v

noncomputable section

/-!
  # Rules · VarsigmaScale

  ## 迁移登记
  - 来源：`FateWorld/Legacy/VarsigmaScale.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, FCA, Alpha
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  $\varsigma$ 的**定义**（FCA 尺度化算子，A32）
    =========================================================================== -/

/-- ⭐⭐⭐ **`ς`（varsigma）：FCA 尺度化算子 —— 把分辨参数 $\gamma$ 映为胞腔尺度。**

**语义来源**（详见文件头 (a)(b)）：`Fate.Alpha` 的 `E8BoundForm` 把 E8 界的第一参数
原文记为

> `/-- 参数一：阈值间隔 $\gamma$。 -/  gamma : ℝ`

而 `Fate/CellDiameter.lean` 要证的目标形态是 `diam ≤ g(γ)`。
故 $g$（本项目的 $\varsigma$）就是「**分辨间隔 $\mapsto$ 胞腔尺度（直径上界）**」的映射。

**定义**：

$$\varsigma(\gamma) := \lvert\gamma\rvert$$

**为什么不是常数**：
- `Fate/Alpha.lean` §4.1 的文献核查表把网格/分箱离散化的误差上界登记为
  「**与网格直径成正比**」，网格直径即分辨步长，故尺度化是**线性**的；
- 常数映射无法满足 $\varsigma(k\gamma)=k\,\varsigma(\gamma)$ 这一尺度化律
  （见 `varsigma_scale`），而尺度化律是「尺度化算子」这一名称的**定义性要求**。

**⚠ 规范化**：比例系数取 $1$ 属**约定**（「填数即为虚构」），
本文件**不声称** $\varsigma$ 就是 E8 的正确界。一般比例系数见 `varsigmaAbsorbs`。

**⚠ 本定义不填 E8 的完整界**：`Fate.Alpha` 原型实测（158/200 胞腔横跨盒下界）
表明 $\gamma$ **单独不足以**控制胞腔直径；完整界为
$g(\gamma,\text{boxLo},\text{boxHi},|M_{\mathrm{FCA}}|)$。$\varsigma$ 是其中 $\gamma$ 一支。 -/
def varsigma (γ : ℝ) : ℝ :=
  |γ|

/-! ===========================================================================
    §2  $\varsigma$ 的**基本性质**
    =========================================================================== -/

/-- **定义体展开**：$\varsigma(\gamma)=\lvert\gamma\rvert$。 -/
theorem varsigma_eq_abs (γ : ℝ) : varsigma γ = |γ| := rfl

/-- ⭐ **$\varsigma$ 非负**（**不需要** `0 < γ` 前件——对任意实数成立）。 -/
theorem varsigma_nonneg (γ : ℝ) : 0 ≤ varsigma γ := abs_nonneg γ

/-- ⭐ **$\varsigma$ 严格正**：只要分辨间隔非零，胞腔尺度就严格正。

**这排除了 `varsigma γ := 0` 这类退化定义**：
$\gamma\ne0$ 时 $\varsigma(\gamma)>0$。 -/
theorem varsigma_pos {γ : ℝ} (hγ : γ ≠ 0) : 0 < varsigma γ :=
  abs_pos.mpr hγ

/-- **零化刻画**：$\varsigma(\gamma)=0$ 当且仅当 $\gamma=0$。

即：**分辨间隔为零 ⟺ 胞腔尺度为零**（胞腔退化成一个点）。 -/
theorem varsigma_eq_zero_iff (γ : ℝ) : varsigma γ = 0 ↔ γ = 0 :=
  abs_eq_zero

/-- ⭐⭐ **$\varsigma$ 真的依赖 $\gamma$**（**非平凡性检验**）。

$$\varsigma(\gamma)<t \iff -t<\gamma \ \wedge\ \gamma<t$$

这条定理**排除了「$\varsigma$ 是常数函数」**：
若 $\varsigma$ 为常数 $c$，则左端与 $\gamma$ 无关；
而右端对 $\gamma$ 的依赖可由 `varsigma_abs_lt` 与 `varsigma_abs_lt_not` 对照看出。 -/
theorem varsigma_abs_lt {γ t : ℝ} :
    varsigma γ < t ↔ -t < γ ∧ γ < t :=
  abs_lt

/-- **非平凡性的具体见证**：$t=1$ 时 $\gamma=0$ 满足左端，而 $\gamma=5$ 不满足。 -/
theorem varsigma_abs_lt_witness :
    varsigma 0 < 1 ∧ ¬ (varsigma 5 < 1) := by
  unfold varsigma
  norm_num

/-- ⭐⭐ **尺度化律（齐次性）**：对 $k>0$，把分辨间隔放大 $k$ 倍，
胞腔尺度也放大 $k$ 倍。

$$\varsigma(k\gamma)=k\cdot\varsigma(\gamma)\qquad(k>0)$$

**这是「尺度化算子」这一名称的实质内容**：
$\varsigma$ 是**一次齐次**的，故它是「尺度」而不是任意函数。 -/
theorem varsigma_scale {k : ℝ} (hk : 0 < k) (γ : ℝ) :
    varsigma (k * γ) = k * varsigma γ := by
  unfold varsigma
  rw [abs_mul, abs_of_pos hk]

/-- ⭐ **一般比例系数的尺度化**：若把比例系数 $k$ 显式提出，
则得 $\lvert k\rvert\cdot\varsigma(\gamma)$。

**这说明了「比例系数 $=1$」这一规范化的地位**：
一般约定下的尺度化算子 $\varsigma_k$ 恰为 $\varsigma$ 的 $\lvert k\rvert$ 倍。 -/
theorem varsigma_absorbs (k γ : ℝ) : varsigma (k * γ) = |k| * varsigma γ := by
  unfold varsigma
  rw [abs_mul]

/-- ⭐ **$\varsigma$ 在 $[0,\infty)$ 上单调递增**：分辨间隔越大，胞腔尺度越大
（**尺度变大 = 粗粒化变粗**）。

$$\gamma_1\le\gamma_2\ \wedge\ 0\le\gamma_1 \ \Longrightarrow\ \varsigma(\gamma_1)\le\varsigma(\gamma_2)$$ -/
theorem varsigma_monoOn_nonneg :
    MonotoneOn varsigma (Set.Ici (0 : ℝ)) := by
  intro a ha b _ hab
  unfold varsigma
  rw [abs_of_nonneg ha, abs_of_nonneg (le_trans ha hab)]
  exact hab

/-- **$\varsigma$ 对绝对值的单调性**：$\lvert\gamma_1\rvert\le\lvert\gamma_2\rvert
\Rightarrow\varsigma(\gamma_1)\le\varsigma(\gamma_2)$（由定义体直接等同）。

**⚠ 诚实标注**：这是**恒等**带来的单调（$\varsigma$ 就是 $\lvert\cdot\rvert$），
不是 $\varsigma$ 的独立数学内容。列出它只为说明 $\varsigma$ 与「分辨间隔的大小」绑死。 -/
theorem varsigma_monotone_abs {γ₁ γ₂ : ℝ} (h : |γ₁| ≤ |γ₂|) :
    varsigma γ₁ ≤ varsigma γ₂ :=
  h

/-! ===========================================================================
    §3  $\varsigma$ 与**直径**的关系（E8 的界面；见文件头 (e) 的**精确边界**）
    =========================================================================== -/

section DiameterInterface

variable {F : Frame} {K : FormalCtx.{u,v}} [PseudoMetricSpace F.X.Carrier]

/-- ⭐⭐ **相容性定理（第一半，有前件）**：

若某个集合 $C$ 在给定度量下的直径 $\le\gamma$，则 $\mathrm{diam}(C)\le\varsigma(\gamma)$。

**⚠ 本条不是同义反复**：
前件是 `diam C ≤ γ`，结论是 `diam C ≤ |γ|`——
后者的右端**不是**前件的右端（$|\gamma|\ne\gamma$ 当 $\gamma<0$），
故必须用 `le_abs_self` 推出。且**当 $\gamma<0$ 时前件本身不可满足**，
故本定理**不会**把「界 $=\gamma$」偷偷塞进结论。

**⚠ 本定理不构成 E8**：E8 要求的是**无条件**（不需要「$\mathrm{diam}\le\gamma$」前件）
的 `diam(Fiber A B) ≤ ς γ`。那种无条件形式**假**（`Alpha.lean` 原型实测 158/200），
属 OQ-4。本定理只说「**$\varsigma$ 与一个已有的 $\gamma$-上界相容**」。 -/
theorem varsigma_diam_le {C : Set F.X.Carrier} {γ : ℝ}
    (hC : Metric.diam C ≤ γ) :
    Metric.diam C ≤ varsigma γ :=
  le_trans hC (le_abs_self γ)

/-- ⭐⭐⭐ **主定理：把「$\gamma$ 是状态空间的直径上界」做成显式前件时的胞腔界。**

设状态空间在给定度量下有界，且 $\gamma$ 是**全空间直径的上界**，
即 $\mathrm{diam}(\mathcal X)\le\gamma$。则：

1. $\gamma\le\varsigma(\gamma)$（**尺度化不缩小上界**）；
2. 对**任意**胞腔 `enc.Fiber A B`，$\mathrm{diam}(\mathrm{Fiber})\le\varsigma(\gamma)$。

**证明**：胞腔 $\subseteq\mathcal X$，故由 `Metric.diam_mono` 得
$\mathrm{diam}(\mathrm{Fiber})\le\mathrm{diam}(\mathcal X)\le\gamma\le\lvert\gamma\rvert
=\varsigma(\gamma)$。

**⚠ 诚实标注（本定理的边界，必读）**：
前件 `hγ : Metric.diam univ ≤ γ` **确实是「$\gamma$ 是上界」这一假设**，
它**不是**结论的重述（结论是关于 $\varsigma(\gamma)=\lvert\gamma\rvert$ 与**各个胞腔**的）。
但**它也不是** E8 想要的「仅由 $\gamma$ 控制直径」——
这里的 $\gamma$ 之所以是界，是**被假设的**，而非由编码方案推出的。
无前件的 `diam(Fiber) ≤ ς γ` **是假的**（157/200 反例，见 `Alpha.lean` §4.1）。
⟹ **本定理不声称 E8 已解决。** -/
theorem varsigma_of_univ_diam_bound (enc : Encoder F K)
    (hX : IsBounded (univ : Set F.X.Carrier)) {γ : ℝ}
    (hγ : Metric.diam (univ : Set F.X.Carrier) ≤ γ) :
    γ ≤ varsigma γ ∧
      ∀ (A : Set K.GFCA) (B : Set K.MFCA),
        Metric.diam (enc.Fiber A B) ≤ varsigma γ := by
  classical
  refine ⟨le_abs_self γ, ?_⟩
  intro A B
  have hsub : enc.Fiber A B ⊆ (univ : Set F.X.Carrier) := subset_univ _
  exact le_trans (le_trans (Metric.diam_mono hsub hX) hγ) (le_abs_self γ)

/-- **上条定理之于 `Encoder.Fiber` 的出口形式**（与 `Fate.CellDiameter` 的
`MetricCellDiameter` 同一含义：后者即 `Metric.diam`，故本定理可直接接入该模块）。

$$\mathrm{diam}\bigl(\mathrm{Fiber}\,A\,B\bigr)\ \le\ \varsigma(\gamma).$$

**⚠ 同上一条的诚实边界**：前件 `hγ` 显式假设了「$\mathcal X$ 的直径 $\le\gamma$」，
这**不是**由编码方案推出的；E8 的**无前件**形式仍属 OQ-4。 -/
theorem varsigma_fiber_diam_le_of_univ_bound (enc : Encoder F K)
    (hX : IsBounded (univ : Set F.X.Carrier)) {γ : ℝ}
    (hγ : Metric.diam (univ : Set F.X.Carrier) ≤ γ)
    (A : Set K.GFCA) (B : Set K.MFCA) :
    Metric.diam (enc.Fiber A B) ≤ varsigma γ :=
  (varsigma_of_univ_diam_bound enc hX hγ).2 A B

/-- **$\varsigma$ 的上界可达性（说明 $\varsigma$ 不是「虚大」的界）**：

若 $\gamma\ge0$ 且 $\mathrm{diam}(C)\le\gamma$，则 $\varsigma(\gamma)=\gamma$，
故该界在非负区间上**恰为**「$\gamma$ 本身」——
即 $\varsigma$ 在 $\gamma\ge0$ 时**没有**被人为放大。

**这排除了「用 $|\gamma|$ 来假装界很宽」的顾虑**：
在 $\gamma\ge0$（阈值间隔的自然取值范围）上 $\varsigma(\gamma)=\gamma$。 -/
theorem varsigma_eq_gamma_of_nonneg {γ : ℝ} (hγ : 0 ≤ γ) : varsigma γ = γ :=
  abs_of_nonneg hγ

end DiameterInterface

/-! ===========================================================================
    §4  自检（机械可核对的非平凡性）
    =========================================================================== -/

/-- **自检 1**：$\varsigma$ **不是**常值零函数（$\gamma=1$ 处为 $1$）。 -/
theorem varsigma_one : varsigma 1 = 1 := by
  unfold varsigma; norm_num

/-- **自检 2**：$\varsigma$ **取到两个不同的值**，故它不是常数函数。

$$\varsigma(1)=1\ \wedge\ \varsigma(2)=2\ \wedge\ 1\ne2$$

**这是对「不许定义 `varsigma γ := 0` 这类常数」这条纪律的机械核对**。 -/
theorem varsigma_not_constant :
    varsigma 1 ≠ varsigma 2 := by
  unfold varsigma
  norm_num

end

end FateV2.Rules