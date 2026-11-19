/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Rules.AlphaDataConsumed`
阶段：**把 `AlphaFCAConstruction` 的 α 定理真正「消费」到
`WorldModelCompleteV2.alpha` 字段上（三条桥 + 两条附属）**

---------------------------------------------------------------------------
本文件补什么（一句话）
---------------------------------------------------------------------------
`Fate.WorldModelCompleteV2` 的 `alpha` 字段**类型本来就是** `FateV2.Rules.AlphaData`
（原文件 `:164`：`alpha : AlphaData.{0} input PUnit`）。
**类型早已接上**，缺的是「**用** `AlphaData` 的定理」：
`grep -n '\.alpha\|\.obs' Fate/WorldModelCompleteV2.lean` 在其定理区**零命中**。
本文件补的正是这批**消费定理**：每条陈述里都出现 `W.alpha`
（即真的作用在 `WorldModelCompleteV2` 的那个字段上），
而不是抽象地复述 `AlphaData` 的定理。

---------------------------------------------------------------------------
(a) `AlphaFCAConstruction` 是什么（据实说明）
---------------------------------------------------------------------------
`Fate/AlphaFCAConstruction.lean` 是 **α 的端到端实现**，链条为

$$\underbrace{\mathcal{E}}_{\text{实例集}}
  \to \underbrace{\mathbb{K}=(G,M,I)}_{\text{形式背景}}=\texttt{ctx}
  \to \underbrace{\mathfrak{B}(\mathbb{K})}_{\text{概念}}=\texttt{instanceConcept}
  \to \underbrace{\mathcal{T}}_{\text{DG 基}}=\texttt{dgBasis}
  \to \underbrace{\mathrm{Th}(\mathcal{T})}_{\text{规则}}=\texttt{thIter},$$

并在 §5 定义 α 本体 `AlphaData.alpha`，其第二分量既证了**闭性**
（`alpha_snd_isClosed`）又证了**有限步可算**
（`alpha_snd_eq_thIter`，需 `[(D.ctx).FiniteAttrs]`）。

---------------------------------------------------------------------------
(b) 本文件新增的定理（**全部实际存在**，可用 `grep ^theorem` 核对）
---------------------------------------------------------------------------
| # | 定理 | 陈述里出现 `W.alpha` 处 | 消费的 `AlphaData` 定理 |
|---|---|---|---|
| 1 | `wmc_alpha_computable` | `(W.alpha).alpha e`、`(W.alpha).obs e`、`(W.alpha).thIter` | `alpha_snd_eq_thIter` |
| 2 | `wmc_alpha_isClosed` | `(W.alpha).ctx.IsClosedAttr ((W.alpha).alpha e).2` | `alpha_snd_isClosed` |
| 3 | `wmc_alpha_respects_obs` | `(W.alpha).obs`、`(W.alpha).alpha` | `alpha_respects_obs` |
| 4 | `wmc_alpha_obs_subset_snd` | `(W.alpha).obs e ⊆ ((W.alpha).alpha e).2` | `subset_closureOp` |
| 5 | `wmc_alpha_fst` | `((W.alpha).alpha e).1 = (W.alpha).instanceConcept e` | `alpha_fst` |
| 6 | `wmc_alpha_extent` | `(((W.alpha).alpha e).1).extent = …` | `instanceConcept_extent` |
| 7 | `wmc_finiteAttrs`（`instance`） | `(W.alpha).ctx.FiniteAttrs` | —（`PUnit` 有限） |

**定理 1 的额外收获**：`WorldModelCompleteV2.alpha` 的属性类型**恰是**
`PUnit`，而 `Set.univ : Set PUnit` 有限，故 `[(W.alpha).ctx.FiniteAttrs]`
**自动成立**（定理 7），`alpha_snd_eq_thIter` 的 `FiniteAttrs` 前件
在 WMC 语境下**无需作为假设出现** ⟹ `wmc_alpha_computable` **无条件**：
`W.alpha` 的第二分量**确实在有限步内由 DG 基算出**。
这是本文件最实质的一条（不是把结论塞进前件：前件只有 `W` 与 `e`）。

**反同义反复核对**（本项目最高频缺陷）：
- 定理 1 的前件只有 `(W : WorldModelCompleteV2 F)` 与 `(e : W.input.Carrier)`，
  **没有**任何子句重述「可算」；
- 定理 2 的前件同上，**没有**假设闭性；
- 定理 3 的前件是 `obs e₁ = obs e₂`（**观测相等**），结论是 `alpha e₁ = alpha e₂`
  （**α 输出相等**）—— 前提与结论**不同**（这正是「α 在观测等价商上良定义」的内容）；
- 定理 4 的前件只有 `W`、`e`，结论 `obs e ⊆ (alpha e).2` 是**严格扩张**
  （`obs e` 一般**不**闭，故不平凡）。

---------------------------------------------------------------------------
(c) **U2 仍未被完全解决**（必须写明，不得含糊）
---------------------------------------------------------------------------
`WorldModelCompleteV2` 原文件登记的未完成项 U2 是：

> `AlphaData`（观测映射）≠ `AlphaOutput`（划分 + `LawRule` 集）。

**本文件不解决 U2。** 具体缺口：

1. **`AlphaData.alpha → AlphaOutput` 的桥仍不存在。**
   `AlphaData.alpha e : Concept E.Carrier M (D.ctx).Irel × Set M`
   （概念 × 闭属性集），而 `InstanceChain.AlphaOutput` 是
   **局部域划分 × `LawRule` 集**。二者**形状不同**：
   - 「概念格元素 ↦ 划分的一块」需要一项**商化**构造
     （`AlphaData.alphaQuot` 只在 `ker(obs)` 上做了 **α 值的**下降，
     **不**给出「划分」这个对象本身）；
   - 「闭属性集 ↦ `LawRule`」需要一项**规则提取**构造
     （`dgBasis` 给的是 `Set M × Set M` 的**伪内涵对**，
     与 `LawRule` 的字段**未做对齐**，见 `Fate/AlphaRulesLocal.lean` 一系）。
2. **形状不同**：`AlphaData.alpha e : Concept E.Carrier M (D.ctx).Irel × Set M`，
   而 `InstanceChain.AlphaOutput` 是「局部域划分 × `LawRule` 集」；
   两者之间需要一个**商化**（`alphaQuot` 只在 `ker(obs)` 上下降，
   且下降后的**值**仍是「概念 × 闭属性集」，**不**给出「划分」这个对象本身）
   与一个**规则提取**（`dgBasis` → `LawRule`），
   这两项构造本文件未做（见 OQ-4）。
   因此二者之间**没有**可由 `rfl` 或定义展开得到的等价，
   「`W.alpha` 与规格 α 等价」在本文件中**既未构造、也未证明**。

---------------------------------------------------------------------------
(d) 本文件**不**声称什么（逐条登记）
---------------------------------------------------------------------------
- **不**声称「α 已完整接入」。本文件只把 `AlphaData` 的**已有的**定理
  在 `W.alpha` 上**实例化**并**检验其可组合性**；
  没有新增任何关于「观测 ↦ 规则」的数学内容。
- **不**声称 `WorldModelCompleteV2` 的 ⑦ 交接器已完成（那需要 U1–U7 全部关闭）。
- 定理 6（`wmc_alpha_extent`）只做 `show` + 转引，**不含**新数学；
  它的作用是让 `W.alpha` 的**第一分量外延**在 WMC 语境下可见。
- 定理 4 的 `obs e ⊆ (alpha e).2` 是 `subset_closureOp` 的**定义性推论**
  （`alpha e).2` 定义上就是 `takeConcept (obs e)` = `closureOp (obs e)`），
  登记为「定义性」，**不**作为实质定理宣传。

---------------------------------------------------------------------------
诚实边界（技术性）
---------------------------------------------------------------------------
- 本文件**零 `sorry`、零 `admit`、零 `axiom`**（`#print axioms` 见文件末 §3）。
- 上下文固定为 `(⟨PUnit⟩ : CtxSpace.{0})`：直接沿用
  `WorldModelCompleteV2` 的参数，**不**改动其结构（未完成项 U4 仍开放）。
- 不修改任何既有模块；本文件是**新建**文件，无同名覆盖。
-/

import Mathlib.Order.Concept
import Mathlib.Data.Set.Lattice
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Implication
import FateWorld.FateV2.Rules.Alpha
import FateWorld.FateV2.Rules.Completeness
import FateWorld.FateV2.Rules.AlphaFCAConstruction
import FateWorld.FateV2.Loop.WorldModelCompleteV2
namespace FateV2.Rules

open FateV2.Loop
open FateV2.Model
open FateV2.Modeling
open Set

universe u

noncomputable section

set_option linter.checkUnivs false

/-!
  # Rules · AlphaDataConsumed

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaDataConsumed.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, FCA, Implication, Alpha, Completeness, AlphaFCAConstruction, WorldModelCompleteV2
  - 补充 open 域：FateV2.Loop, FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §0  接口实测（`#check` 原文已抄入文件头 (a)(b) 两节的对照表；
        此处仅保留一条编译期确认，防止名字漂移）
    =========================================================================== -/

#check @FateV2.Rules.AlphaData.alpha_snd_eq_thIter
#check @FateV2.Rules.AlphaData.alpha_snd_isClosed
#check @FateV2.Rules.AlphaData.alpha_respects_obs
#check @Fate.WorldModelCompleteV2.alpha

/-! ===========================================================================
    §1  `W.alpha` 的有限性：`PUnit` 作属性类型时 `FiniteAttrs` 自动成立
    =========================================================================== -/

/-- **`PUnit` 作属性类型是有限的**，故 `W.alpha` 的形式背景自动满足 `FiniteAttrs`。

这是 `WorldModelCompleteV2.alpha : AlphaData.{0} input PUnit` 的**直接红利**：
`alpha_snd_eq_thIter` 所需的 `FiniteAttrs` 前件在 WMC 语境下**不需假设**。

⚠ 这**不是**「属性集应该只有一点」的断言——它是
`WorldModelCompleteV2` 既有字段类型的**后果**，不是本文件的选择。 -/
instance wmc_finiteAttrs {F : Frame} [instX : MeasurableSpace F.X.Carrier]
    [S : RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X]
    (W : WorldModelCompleteV2 F) : (W.alpha).ctx.FiniteAttrs :=
  ⟨by rw [Set.finite_univ_iff]; exact inferInstance⟩

/-! ===========================================================================
    §2  三条桥：把 `AlphaData` 的 α 定理消费到 `W.alpha` 上
    =========================================================================== -/

variable {F : Frame} [instX : MeasurableSpace F.X.Carrier]
  [S : RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X]

/-- **桥 ①：`W.alpha` 的第二分量在有限步内由 DG 基算出**（可算性）。

$$\exists n,\ \bigl(\alpha_{W}(e)\bigr)_2=\Sigma_{\mathcal{T}_W}^{n}\bigl(\mathrm{obs}_W(e)\bigr).$$

消费 `AlphaData.alpha_snd_eq_thIter`，并把它的 `FiniteAttrs` 前件
由 §1 的 `wmc_finiteAttrs` **自动消去** ⟹ **前件只余 `W` 与 `e`**。

**前件非平凡性核对**：陈述中不出现「存在 `n`」以外的任何假设，
前件**没有**把结论包进去。 -/
theorem wmc_alpha_computable (W : WorldModelCompleteV2 F) (e : W.input.Carrier) :
    ∃ n : ℕ, ((W.alpha).alpha e).2 = (W.alpha).thIter n ((W.alpha).obs e) :=
  (W.alpha).alpha_snd_eq_thIter e

/-- **桥 ②：`W.alpha` 的第二分量是闭集**（值域正确的属性侧）。

消费 `AlphaData.alpha_snd_isClosed`。这是 `alpha` 输出**落在概念格属性侧**
的证据：`α` 不会输出「半个概念」。

**前件非平凡性核对**：前件 `W`、`e` 之外**无**闭性假设。 -/
theorem wmc_alpha_isClosed (W : WorldModelCompleteV2 F) (e : W.input.Carrier) :
    (W.alpha).ctx.IsClosedAttr ((W.alpha).alpha e).2 :=
  (W.alpha).alpha_snd_isClosed e

/-- **桥 ③：`W.alpha` 与观测一致**——观测相同的实例，α 输出相同。

消费 `AlphaData.alpha_respects_obs`。即 `α_W` 下降到 $\ker(\mathrm{obs}_W)$ 的商上
（「观测等价 ⟹ α 等价」）。这是 α 的**保结构性**，也是
`AlphaData.alphaQuot` 良定义性的来源。

**前件非平凡性核对**：前件是 `obs e₁ = obs e₂`（**观测**相等），
结论是 `alpha e₁ = alpha e₂`（**α 值**相等）——
两者**不同**（`alpha` 输出还含概念格元素与闭包），
故**不是**同义反复。 -/
theorem wmc_alpha_respects_obs (W : WorldModelCompleteV2 F) {e₁ e₂ : W.input.Carrier}
    (h : (W.alpha).obs e₁ = (W.alpha).obs e₂) :
    (W.alpha).alpha e₁ = (W.alpha).alpha e₂ :=
  (W.alpha).alpha_respects_obs h

/-! ### §2.4 两条附属引理（**定义性**，登记为补充，不作实质断言） -/

/-- **附属 ①**：`W.alpha` 的第二分量**扩张**观测集：$\mathrm{obs}_W(e)\subseteq(\alpha_W(e))_2$。

⚠ **诚实标注**：这是 `AlphaData.subset_closureOp` 的**定义性推论**
（`(alpha e).2` 定义上就是 `closureOp (obs e)`），
**不**构成本文件的新数学内容；列出它是为了让 WMC 语境下的
「α 不丢信息」方向在类型层**可见**。 -/
theorem wmc_alpha_obs_subset_snd (W : WorldModelCompleteV2 F) (e : W.input.Carrier) :
    (W.alpha).obs e ⊆ ((W.alpha).alpha e).2 :=
  (W.alpha).subset_closureOp ((W.alpha).obs e)

/-- **附属 ②**：`W.alpha` 的第一分量就是实例概念（概念格中的真实对象）。 -/
theorem wmc_alpha_fst (W : WorldModelCompleteV2 F) (e : W.input.Carrier) :
    ((W.alpha).alpha e).1 = (W.alpha).instanceConcept e :=
  (W.alpha).alpha_fst e

/-- **附属 ③**：`W.alpha` 第一分量的**外延**是 $\{e\}''$（只用 `polarUp`/`polarDown` 写出）。

消费 `AlphaData.instanceConcept_extent`。 -/
theorem wmc_alpha_extent (W : WorldModelCompleteV2 F) (e : W.input.Carrier) :
    (((W.alpha).alpha e).1).extent
      = (W.alpha).ctx.polarDown ((W.alpha).ctx.polarUp ({e} : Set W.input.Carrier)) := by
  show ((W.alpha).instanceConcept e).extent = _
  exact (W.alpha).instanceConcept_extent e

/-- **附属 ④**：`W.alpha` 的第二分量**幂等**——再取一次概念不变。

消费 `AlphaData.takeConcept_idem`。 -/
theorem wmc_alpha_snd_idem (W : WorldModelCompleteV2 F) (e : W.input.Carrier) :
    (W.alpha).takeConcept ((W.alpha).alpha e).2 = ((W.alpha).alpha e).2 :=
  (W.alpha).takeConcept_idem ((W.alpha).obs e)

/-! ===========================================================================
    §3  公理审计（`#print axioms`：**不得**出现 `sorryAx`）
    =========================================================================== -/

#print axioms wmc_alpha_computable
#print axioms wmc_alpha_isClosed
#print axioms wmc_alpha_respects_obs
#print axioms wmc_alpha_obs_subset_snd
#print axioms wmc_alpha_fst
#print axioms wmc_alpha_extent
#print axioms wmc_alpha_snd_idem

end

end FateV2.Rules