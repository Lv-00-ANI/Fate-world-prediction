/-
命运理论 · **`LawRule` 的实例层**：`α : InstSpace → LawRule` 需要什么？
======================================================================

模块：`InstSpaceToLawRule`
上游：`Fate/LawRule.lean`（`LawRule`、`IsPoint`、`Deterministic`、`compose`、`top`、`bot`）、
　　　`Fate/LawRuleToTraj.lean`（`IsDirac`、`toDetFun`、`toDetFun_toLaw`）、
　　　`Fate/Frame.lean`（`InstSpace`、`CtxSpace`、`StateSpace`、`OutSpace`、`Rules`、`Alpha`）、
　　　`Fate/Alpha.lean`（`takeConcept`、`Encoder`）。

**⚠ 不依赖 `Fate/SCMLawBridge`**：该文件当前**编译失败**
（`lake build FateV2.Rules` → `OutSpace := StateSpace` 统一后
`Rule C X` 类型参数不匹配，3 error）。本文件**不 import 它、不引用其定理名**，
故「`lawObs` 口径」在 §4a 里只作**形态登记**（`obsAlpha`，独立重写）。

---------------------------------------------------------------------------
问题
---------------------------------------------------------------------------
`Fate/Frame.lean:709` 把 $\alpha$ 的签名定为

  `Alpha E C X Y := E.Carrier → Rule C X Y`   （`Rule` = 条件分布核）

`Fate/LawRule.lean` 把规则层换成
$$\text{LawRule} := C \to X \to \mathcal{P}(\mathrm{Measure}\ Y).$$

**问**：要让 $\alpha$ 落在 `LawRule` 而不是 `Rule`，需要什么？

---------------------------------------------------------------------------
答案（先给结论）
---------------------------------------------------------------------------
**三件事，第一件免费，第二件必须外置，第三件是唯一的实质内容。**

| # | 闸 | 需要什么 | 能不能自动得到 |
|---|---|---|---|
| **① 提升闸** | `Rule → LawRule` | `Rule.toLaw`（`μ ↦ {μ}`） | ✅ **免费**，`rfl` 级，库里已有 |
| **② 编码闸** | `embed : E.Carrier → F.X.Carrier` ＋ `enc : Encoder F K` ＋ `code` | `InstSpace` 只有 `Carrier : Type*`，**无任何结构**；从实例到「状态 / 属性集 / 规则」的映射**一个都没有** | ❌ **必须外置为参数**，库里不存在典范映射 |
| **③ 语义闸** | 值域落进 `IsTrueConstraint`（允许集含**≥2 个不同分布**） | `LawRule` 相对 `Rule` 的**唯一**增益。`toLaw` 只产出**单点档** | ❌ **不能**：见 §3 主定理 `liftRule_not_trueConstraint` |

**⟹ 一句话**：$\alpha : \mathcal E \to \text{LawRule}$ **在类型上免费**（①+②），
**在语义上不免费**。只用 ①+②（即「核 + `toLaw`」）得到的 `α`，
**每一个值都必然是单点档**，与 `Rule` 信息完全等价 ——
`LawRule` 的「约束」语义**一点也用不上**。

**⟹ 真正的答案是**：`LawRule` 的实例层需要的不是类型转换，
而是**`Rule` 侧没有的信息** —— 即「允许集**不止一个分布**」这种多值语义。
库里**没有**任何现成构造能提供它（§4a 的 `obsAlpha` 只是形态登记，
`SCMLawBridge.lawObs` 当前不可编译；FCA 路线 §4b 是缺口，
其全部内容都在外部参数 `interp` 里）。

---------------------------------------------------------------------------
与第 6–11 路的关系（**必读**）
---------------------------------------------------------------------------
第 6–11 路（`Fate/DSepTopoPeel`、`ThreeNodeFactorizes`、`FourNode*`、
`PEARL_127_PROOF_ROADMAP`）全部在 **`FactorMarkov.Joint = (V → α) → ℝ`** 上工作，
**没有一路消费 `LawRule`**。两者之间**只有一条**合法通道：

```
LawRule  --(IsDirac：选出一个 Dirac δ_y)-->  确定性函数  --(点质量函数)-->  Joint
```

**⟹ 本文件 §5 把这条通道写成定理**（`readDetFun` / `readDetFun_spec`），
并证明前件**不可去除**：一个 `α : InstSpace → LawRule` 若只经 ①+②，它**只是** `IsPoint`，
而 **`IsPoint` 不蕴含 `IsDirac`**（§5 `isPoint_not_implies_isDirac`，机器见证），
故**不能**直接喂给第 6–11 路。要在 `LawRule` 与 `FactorMarkov` 之间架桥，
必须**额外**要求 `α` 的值域落在 `IsDirac` 里 —— 这是本文件对那 6 路的净新增要求。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 零 `sorry` / 零 `axiom` / 零 `native_decide`。
- 每个额外输入一律作**显式参数或前件**，不塞进定义。
- 「`LawRule` 相对 `Rule` 无增益」写成**可编译定理**（§3），不是注释。
- 「`IsPoint` 不足以喂第 6–11 路」写成**可编译定理**（§5），不是注释。
-/

import FateWorld.FateV2.Rules.LawRule
import FateWorld.FateV2.Rules.LawRuleToTraj
import FateWorld.FateV2.Rules.Alpha
import FateWorld.FateV2.Rules.AlphaKernel
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace InstSpaceToLawRule

open MeasureTheory
open FateV2.Rules.LawRule (LawRule)

variable {E : InstSpace} {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
  [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]

/-!
  # Rules · InstSpaceToLawRule

  ## 迁移登记
  - 来源：`FateWorld/Legacy/InstSpaceToLawRule.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule, LawRuleToTraj, Alpha, AlphaKernel
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  ① 提升闸（免费）：`Rule → LawRule`
    =========================================================================== -/

/-- **① + ② 的管道**：把 `Fate/Frame.lean:709` 的
`Alpha E C X Y = E.Carrier → Rule C X Y` 逐点提升到 `LawRule` 层。

这是 `α : InstSpace → LawRule` 的**免费的一半** ——
不添加任何假设，只做类型搬运（`Rule.toLaw`）。

§3 将证明**它也就只值这么多**。 -/
def liftRule (a : E.Carrier → Rule C X Y) : E.Carrier → LawRule C X Y :=
  fun e => LawRule.Rule.toLaw (a e)

/-- **提升的定义等式**（`rfl` 级，无内容的登记）。 -/
theorem liftRule_apply (a : E.Carrier → Rule C X Y) (e : E.Carrier) :
    liftRule a e = LawRule.Rule.toLaw (a e) := rfl

/-- **`liftRule` 必然落在单点档**（`IsPoint` **无条件**成立）。

**这是 §2 一切结论的源头**：`Rule.toLaw` 的定义就是 `μ ↦ {μ}`，
故从 `Rule` 出发的一切 `α`，在 `LawRule` 上都**只能**是单点档。 -/
theorem liftRule_isPoint (a : E.Carrier → Rule C X Y) (e : E.Carrier) :
    LawRule.IsPoint (liftRule a e) :=
  fun _ _ => ⟨_, rfl⟩

/-- **`liftRule` 也是 `Deterministic`**（单点档的直接推论）。 -/
theorem liftRule_deterministic (a : E.Carrier → Rule C X Y) (e : E.Carrier) :
    LawRule.Deterministic (liftRule a e) :=
  LawRule.IsPoint.deterministic _ (liftRule_isPoint a e)

/-! ===========================================================================
    §2  ⭐ `LawRule` **相对** `Rule` 唯一的增益：**多值档**
    =========================================================================== -/

/-- **真约束档（多值档）**：$R\,c\,x$ 至少含**两个不同的**分布。

**为什么这才是唯一的增益**：`IsPoint` 的 `LawRule` 与 `Rule` **信息等价**
（`Rule.toLaw` 的像恰是 `IsPoint` 档）。
故「改用 `LawRule` 而不是 `Rule`」若只落在 `IsPoint` 上，是**换名不换内容**
—— 允许集是单点，等于一个分布，等价于一个核。

真正的增益只有一种：允许集**不止一个分布** —— 规律**不算出**一个分布，
而是**约束**一族分布（「物理规律式」的排除语义，见 `Fate/LawRule.lean` 头注）。

**⚠ 注意（原稿此处曾写错）**：`IsPoint` **不**蕴含「允许集是全集」，
故不能用「存在被排除的元素」来刻画增益 —— 单点集也排除很多元素。
正确的增益口径是「允许集**多大**」，不是「是否排除某些成员」。

**⚠ 本定义不施加概率性（`IsProbabilityMeasure`）约束** ——
那属 SCM 桥（`SCMLawBridge.lawObs`）的口径，本文件不重复。 -/
def IsTrueConstraint (R : LawRule C X Y) : Prop :=
  ∀ c x, ∃ μ ν : Measure Y.Carrier, μ ∈ R c x ∧ ν ∈ R c x ∧ μ ≠ ν

/-- ⭐⭐ **`IsTrueConstraint` 与 `IsPoint` 互斥**（增益的**严格性**）。

「允许集含两个不同分布」与「允许集是单点集」不能同时成立。

**⟹ 这是本文件的核心判词**：
$$\underbrace{\texttt{liftRule}}_{①+②}\ \text{给出}\ \texttt{IsPoint},
\qquad
\underbrace{\texttt{IsTrueConstraint}}_{\`LawRule\`\text{ 的唯一增益}}\ \text{给出}\ \neg\texttt{IsPoint}.$$
**⟹ `liftRule` 的像与「`LawRule` 有意义」的部分不相交。** -/
theorem isTrueConstraint_not_isPoint {R : LawRule C X Y}
    [Nonempty C.Carrier] [Nonempty X.Carrier]
    (h : IsTrueConstraint R) (hpt : LawRule.IsPoint R) : False := by
  obtain ⟨c⟩ := ‹Nonempty C.Carrier›
  obtain ⟨x⟩ := ‹Nonempty X.Carrier›
  obtain ⟨u, v, hu, hv, huv⟩ := h c x
  obtain ⟨μ, hμ⟩ := hpt c x
  rw [hμ, Set.mem_singleton_iff] at hu hv
  exact huv (hu.trans hv.symm)

/-- **`top` 是真约束**（只要 `Measure Y.Carrier` 有两个不同元素 ——
例如 `0` 与 `δ_y`；单位元 `0` 与任一 `dirac` 总不相同）。

**⚠ 这是原稿搞反的一条**：`top` 的允许集是全集，当然含两个不同分布，
故 `top` **是**真约束档；而 `bot`（空集）**不是**
（空集里取不出两个成员）—— 见下条。 -/
theorem isTrueConstraint_top [Nonempty Y.Carrier] :
    IsTrueConstraint (LawRule.top C X Y) := by
  intro c x
  obtain ⟨y⟩ := ‹Nonempty Y.Carrier›
  refine ⟨0, MeasureTheory.Measure.dirac y, by simp [LawRule.top],
    by simp [LawRule.top], ?_⟩
  intro h
  have huniv : (MeasureTheory.Measure.dirac y) Set.univ = (0 : Measure Y.Carrier) Set.univ := by
    rw [h]
  simp at huniv

/-- **`bot` 不是真约束**（空集取不出两个不同成员）—— 它连一个都没有。 -/
theorem not_isTrueConstraint_bot [Nonempty C.Carrier] [Nonempty X.Carrier] :
    ¬ IsTrueConstraint (LawRule.bot C X Y) := by
  intro h
  obtain ⟨c⟩ := ‹Nonempty C.Carrier›
  obtain ⟨x⟩ := ‹Nonempty X.Carrier›
  obtain ⟨u, -, hu, -, -⟩ := h c x
  exact Set.notMem_empty u hu

/-! ===========================================================================
    §3  ⭐⭐ 主判词：只经 ①② 的 `α` 必然零增益
    =========================================================================== -/

/-- ⭐⭐ **主定理：类型管道免费、语义不免费。**

凡是经 `liftRule`（「核 + `toLaw`」）构造出的 `α`，
**其每个值都不满足 `IsTrueConstraint`**（即都不会是多值档）。

$$\forall a,\ \forall e,\ \neg\,\texttt{IsTrueConstraint}\,(\texttt{liftRule}\,a\,e).$$

**⟹ 这是对「`LawRule` 的实例层需要什么」的直接回答**：
需要的**不是**类型转换（有现成的 `toLaw`），
**而是**一种 `Rule` 侧**不具备**的信息 —— 见 §4 的两条候选来源。 -/
theorem liftRule_not_trueConstraint [Nonempty C.Carrier] [Nonempty X.Carrier]
    (a : E.Carrier → Rule C X Y) (e : E.Carrier) :
    ¬ IsTrueConstraint (liftRule a e) := by
  intro ht
  exact isTrueConstraint_not_isPoint ht (liftRule_isPoint a e)

/-- **`α := fun _ => top` 是合法的零信息实例**：

$$\exists \alpha : \mathcal E \to \text{LawRule},\ \forall e,\ \alpha\,e = \texttt{top}.$$

**⟹ 「存在 `α : InstSpace → LawRule`」是**平凡真**的。**
故**单凭 A1 的类型签名不能说明 `α` 有内容**。
本定理把这个「平凡真」钉成可编译事实，防止把签名当成定理。 -/
theorem exists_trivial_alpha (E : InstSpace) :
    ∃ α : E.Carrier → LawRule C X Y, ∀ e, α e = LawRule.top C X Y :=
  ⟨fun _ => LawRule.top C X Y, fun _ => rfl⟩

/-! ===========================================================================
    §4  语义闸的两条候选来源（`LawRule` 的实例层真正需要的）
    =========================================================================== -/

/-- **② 编码闸的完整参数包**：把实例送进「可谈分布」的位置所需的
一切**非 `InstSpace` 自带**的原料。

| 字段 | 作用 | 为什么不能省 |
|---|---|---|
| `embed` | $e \mapsto x$ | 所有下游构造都在 `F.X.Carrier` 上定义 |
| `enc` | $x \mapsto (A_t, B_t)$ | 裁决 D 规定 $\alpha$ 是 FCA 取概念过程，这是它的输入 |
| `code` | $e \mapsto \text{LawRule}$ | 「实例决定了什么」的**内容**；本文件**不预设**其结构 |

**⚠ 诚实边界**：第三个字段的**存在**不说明 `α` 有内容
（`code := fun _ => top` 合法，见 `exists_trivial_alpha`）。
把它做成字段，正是为了让「`α` 有没有内容」成为**可检验命题**而非默认假设。 -/
structure InstCode (E : InstSpace) (F : Frame) (K : FormalCtx.{u,v})
    (C : CtxSpace) (X : StateSpace) (Y : OutSpace) [MeasurableSpace Y.Carrier] where
  /-- 实例 ↦ 状态（**`InstSpace` 不提供**，必须外置） -/
  embed : E.Carrier → F.X.Carrier
  /-- 状态 ↦ 二值形式背景（裁决 D 之 α 的输入侧） -/
  enc : Encoder F K
  /-- 实例 ↦ 规则（内容住在这一位） -/
  code : E.Carrier → LawRule C X Y

variable {F : Frame} {K : FormalCtx.{u,v}}

/-! ### §4a **来源 (a)：观测约束（`lawObs` 口径）** —— 目前**不可用** -/

/-- **来源 (a) 的形态登记**：若每个实例携带一个「观测表」
`obs : E.Carrier → X.Carrier → Y.Carrier → ENNReal`（在 `x,y` 处的观测质量），
则「与观测相容的一切分布」可以写成

$$\alpha\,e\,c\,x = \{\mu \mid \forall y,\ \mu\,\{y\} = \mathrm{obs}\ e\ x\ y\}.$$

这就是 `Fate/SCMLawBridge.lawObs` 的**无 SCM 版本**：它只消费观测表，
**不**消费外生律与结构方程。

**⚠⚠ 依赖状态（必须如实登记）**：
`Fate/SCMLawBridge` **当前编译失败**
（`lake build FateV2.Rules` → `OutSpace := StateSpace` 统一后
`Rule C X` 的类型参数不匹配，3 个 error）。
**⟹ 本文件不 import 它，也不引用它的任何定理名。**
下面的 `obsAlpha` 是**在 `LawRule` 侧独立重写**的同一个形态，
使「来源 (a)」的意义不依赖那个坏文件。 -/
noncomputable def obsAlpha
    (obs : E.Carrier → X.Carrier → Y.Carrier → ENNReal) :
    E.Carrier → LawRule C X Y :=
  fun e c x => {μ | ∀ y : Y.Carrier, μ {y} = obs e x y}

/-- ⭐ **来源 (a) 的成员判据**（`Iff.rfl`，无内容的登记）。

**⚠ 本文件对来源 (a) 只做到这一步，并如实登记其局限**：
`obsAlpha` 的形态是「每个 `y` 一个质量值」，`Y` 有限时它能表达
「与观测表相容的一切测度」。但：
1. 它**不保证**允许集非空（观测表不相容时为空集）；
2. 它**不保证**允许集非单点（相容且支撑唯一时退化为 `IsPoint`）——
   这正是 `SCMLawBridge` 的 `isPoint_lawObs_iff` / `lawObs_not_point_modelD`
   想说的东西，但那些定理**当前不可编译**（见 §4a 头注）；
3. **⟹ 来源 (a) 是否真能产出 `IsTrueConstraint`，本文件不主张。**
   真正的相容性论证缺 **可编译的 SCM 桥**这一件。 -/
theorem obsAlpha_mem_iff
    (obs : E.Carrier → X.Carrier → Y.Carrier → ENNReal) (e : E.Carrier)
    (c : C.Carrier) (x : X.Carrier) (μ : Measure Y.Carrier) :
    μ ∈ obsAlpha obs e c x ↔
      ∀ y : Y.Carrier, μ {y} = obs e x y :=
  Iff.rfl

/-! ### §4b **来源 (b)：FCA 取概念后落到 `LawRule`** —— **缺口** -/

/-- **来源 (b)**：把 `takeConcept` 的输出经一个**解释映射**读成 `LawRule`。

`takeConcept` 的值域是 `Set K.MFCA`（属性闭集，`Fate/Alpha.takeConcept_isClosed`）。
把它读成「这个概念允许哪些下一分布」，需要一个
$$\text{interp} : \text{闭属性集} \to C \to X \to \mathcal P(\text{Measure}\ Y).$$

**⚠ 这就是本文件要登记的缺口**：库里**没有** `interp`。
`Fate/Alpha.lean` 的 `takeConcept` 与 `Measure Y.Carrier` **没有任何桥**。
故 (b) **不是构造，是缺口**，除非另行证明 `interp` 由数据决定。 -/
def fcaAlphaOf
    (interp : Set K.MFCA → C.Carrier → X.Carrier → Set (Measure Y.Carrier))
    (enc : Encoder F K) (embed : E.Carrier → F.X.Carrier) :
    E.Carrier → LawRule C X Y :=
  fun e => interp (K.takeConcept (enc.toAttrs (embed e)))

/-- ⭐ **来源 (b) 的诚实边界定理**：`fcaAlphaOf` **把 `interp` 当作输入**，
即 **(b) 的全部内容都在 `interp` 里**，`takeConcept` 只贡献「取闭包」这一步。

**⟹ 这条不构成「α 从实例出发产生 `LawRule`」的证明**，
除非另行证明 `interp` 存在且由数据决定。本定理使该依赖**不可隐藏**。 -/
theorem fcaAlphaOf_factors_through_interp
    (interp : Set K.MFCA → C.Carrier → X.Carrier → Set (Measure Y.Carrier))
    (enc : Encoder F K) (embed : E.Carrier → F.X.Carrier) (e : E.Carrier) :
    fcaAlphaOf interp enc embed e
      = interp (K.takeConcept (enc.toAttrs (embed e))) := rfl

/-! ===========================================================================
    §5  ⭐⭐ 与第 6–11 路的接线：`LawRule` ⟹ `Joint` 的**唯一**通道
    =========================================================================== -/

/-- ⭐⭐ **`LawRule` 到概率层的读出**（第 6–11 路消费的形态）。

`LawRule` 是**测度集**；`FactorMarkov` 消费的是 `Joint V α = (V → α) → ℝ`。
两者之间的**唯一**通道是：**选出**一个允许分布，取其点质量函数。

**⚠ 前件 `IsDirac`（不是 `IsPoint`）**：
- `IsPoint` 只说「允许集是 `{μ}`」，`μ` 是**任意测度**
  —— 从它读不出 `V → α` 上的函数（没有「点」）；
- `IsDirac` 说「允许集是 `{δ_y}`」，`y` 是**点**
  —— 这才是 `V → α` 的取值来源。

**⟹ 本定义把「`α` 的输出能否被 `Factorizes`/`LMG`/`GM` 消费」
变成一个**有明确前件的构造**，而不是一句「应该可以接上」。** -/
noncomputable def readDetFun (R : LawRule C X Y) (h : LawRuleToTraj.IsDirac R) :
    C.Carrier → X.Carrier → Y.Carrier :=
  LawRuleToTraj.toDetFun R h

/-- ⭐⭐ **读出的正确性**：`readDetFun` 精确复现 `R`（`IsDirac` 档无信息丢失）。 -/
theorem readDetFun_spec (R : LawRule C X Y) (h : LawRuleToTraj.IsDirac R)
    (c : C.Carrier) (x : X.Carrier) :
    R c x = {MeasureTheory.Measure.dirac (readDetFun R h c x)} :=
  LawRuleToTraj.toDetFun_spec R h c x

/-- ⭐⭐ **`IsPoint` 不足以喂第 6–11 路**（`IsDirac` 前件不可去除）。

存在一个 `LawRule` 满足 `IsPoint` 却**不**满足 `IsDirac`。

**⟹ 本定理钉死的事实**：
$$\texttt{liftRule}\ \text{的像} \subseteq \texttt{IsPoint},
\qquad
\text{第 6–11 路需要}\ \texttt{IsDirac},$$
而 `IsPoint ⊋ IsDirac`（`LawRuleToTraj.IsDirac.isPoint` 是严格包含的 `→`）。
故「把 `α : InstSpace → LawRule` 直接接到第 6–11 路」**在数学上不成立**，
必须先证（或假设）`α` 的值域落在 `IsDirac` 内。

**构造（具体见证）**：取 `Y.Carrier = Bool`，允许集恒为 `{0}`（零测度）。
- `IsPoint`：`{0}` 是单点集。✅
- `¬ IsDirac`：若 `{0} = {δ_y}` 则 `δ_y = 0`，但 `δ_y univ = 1 ≠ 0`。❌

**⚠ 为什么用零测度而不��概率测度的「非 Dirac 单点」**：
零测度让 `IsDirac` 的失败**纯由 `δ_y ≠ 0` 决定**（`δ_y univ = 1`），
不需要构造 `½δ_true + ½δ_false` 那种「和」——后者在 `Measure` 上
要证 `≠ δ_y` 需逐 `Set` 比较，代价更高且与结论无关。
**本见证虽然「不概率」，但足以证明 `IsPoint ⇏ IsDirac`** ——
这正是本定理需要的全部。 -/
theorem isPoint_not_implies_isDirac :
    ∃ (C₀ : CtxSpace.{0}) (X₀ : StateSpace.{0}) (Y₀ : OutSpace.{0})
      (_ : MeasurableSpace Y₀.Carrier) (_ : MeasurableSpace X₀.Carrier)
      (R : LawRule C₀ X₀ Y₀), LawRule.IsPoint R ∧ ¬ LawRuleToTraj.IsDirac R := by
  classical
  let Y₀ : StateSpace.{0} :=
    { Carrier := Bool
      topo := ⊥
      meas := ⊤
      borel_le := by rw [borel_eq_top_of_discrete] }
  letI : MeasurableSpace Y₀.Carrier := Y₀.meas
  refine ⟨⟨PUnit⟩, Y₀, Y₀, Y₀.meas, Y₀.meas, fun _ _ => {0}, ?_, ?_⟩
  · intro c x
    exact ⟨0, rfl⟩
  · intro hd
    obtain ⟨y, hy⟩ := hd (Classical.arbitrary _) (Classical.arbitrary _)
    have h0 : (MeasureTheory.Measure.dirac y : Measure Bool) = 0 := by
      rw [Set.singleton_eq_singleton_iff] at hy
      exact hy.symm
    have huniv : (MeasureTheory.Measure.dirac y) Set.univ = (0 : Measure Bool) Set.univ := by
      rw [h0]
    simp at huniv

end InstSpaceToLawRule

end FateV2.Rules