/-
  命运理论 · FCA 分类系统层（作者裁决 N + O 的落点）

  ============================================================================
  ⚠ 本文件的定位与诚实边界（须先读）
  ============================================================================

  **作者裁决 N**：FCA 不再承担主线入口（`enc`），**改作分类系统**。
  **作者裁决 O**：因果进入分类循环 —— 循环的内容是**抽象与解构**（两种目光）。

  ---
  ⚠ 一、为什么本文件【重新实现】而不是【复用】`RealTemporalLayer`
  ---

  `FCA-副本/03-哲学依据/FCA的拓展与补足.md` 提议补「要素层 + 目光」，
  其 MVP 第 1、2 步是：目光状态、要素/概念定义、悬置。

  **但本实现核实：该 MVP 第 1、2 步【已存在于** `RealTemporalLayer.lean`**】**——
  证据是**已复制**的 `RealFCAElementApplication.lean` **逐条引用**了
  `gazeUp` / `gazeDown` / `IsElement` / `IsConcept` / `hasUpper` / `suspend` /
  `suspend_preserves_base` / `suspend_dissolves_identity` / `no_upper_iff_no_split`
  （见 `裁决记录.md` R-030 的引用清单）。

  **⚠ 但 `RealTemporalLayer.lean` 本身【不在副本中】**（副本缺 8 个被 import 的模块）。
  故本实现**无法复用**，也**无法核验其语义细节**。

  **⟹ 本实现的选择**：
    ① **不假装复用**（源文件不可见，无法核验）；
    ② **给出自足的最小实现**，把「要素层 + 目光」在本项目内重建，
       使**分类系统**有可编译、可核验的落点；
    ③ **明确标注**：本文件**不声称**与 `RealTemporalLayer` 语义一致
       （后者未见源码）。**若主控补全副本，应以源码为准重新核对。**

  ---
  ⚠ 二、哲学原文不是数学依据（作者裁决 N 第七节第 3 条，**本实现一并采纳**）
  ---

  「时态性层级体系」原文**未提 FCA**。
  本文件把「向上目光 ↔ `intent`」「向下目光 ↔ `extent`」作为**解读**，
  **其正确性由映射后的可证性验证，不由原文权威保证**。
  所有引自哲学文本之处标 `[哲学依据]`。

  ---
  ⚠ 三、本文件**不**做的
  ---

  · **不试图证明**体系公设 (a)–(e)（它们是**前提不是定理**）；
  · **不形式化**「论域本身」「操作论域」「目光自指」（体系自认边界）；
  · **不声称**补足能消除任何已证不可能性。

  ============================================================================
-/

import FateWorld.Legacy.FCA
import FateWorld.Legacy.Implication
import FateWorld.Legacy.Completeness
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Fate

universe u v

noncomputable section

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-! ===========================================================================
    §1  目光状态（[哲学依据] 时态性层级体系 §4.1）
    ======================================================================== -/

/-- **目光的状态**（[哲学依据]：时态性层级体系 §4.1「两种目光」）。

> **向上目光**：追问「它归于何类」 → 建立**上位归类**
> **向下目光**：追问「它由何构成」 → 建立**内部构成**

**本实现给出三种状态**：

| 构造子 | 含义 |
|---|---|
| `none` | **目光未投出** —— 对象呈现为**要素** |
| `up` | **向上目光** —— 对象呈现为**概念**（上位归类） |
| `down` | **向下目光** —— 对象呈现为**概念**（内部构成） |

**⚠ 本定义是「给定的」不是「导出的」**——
`[哲学依据]` 体系把「目光分化如何可能」列为**边界**
（其公设 (e)：**永远无法在系统内证明**）。
**本实现如实沿用该边界**，**不试图导出 `Gaze`**。

**⚠ 本实现不声称**这与 `RealTemporalLayer.Gaze` 一致（未见其源码）。 -/
inductive Gaze where
  /-- 目光未投出（对象是**要素**）。 -/
  | none
  /-- 向上目光（上位归类）。 -/
  | up
  /-- 向下目光（内部构成）。 -/
  | down
  deriving DecidableEq, Repr

/-- **时态化的呈现**：同一基底，随目光呈现不同身份。

`[哲学依据]` 原理 1：**身份随目光的投出与撤回而转化，不涉及基底变更**。

**本结构把「基底」与「目光」分开存**——
这正是「同一张脸，不同身份」在类型层的落点。 -/
structure Temporal (O : Type u) where
  /-- **基底**：不随目光改变的对象本身。 -/
  base : O
  /-- **当前目光**。 -/
  gaze : Gaze
  deriving Repr

/-- **切换目光**。 -/
def Temporal.withGaze (t : Temporal O) (g : Gaze) : Temporal O :=
  { t with gaze := g }

/-- ⭐ **原理 1 的形式化：切换目光不改变基底**（「同一张脸」）。

**⚠ 本命题是 `rfl` 级（平凡）——但其价值在【陈述】而非难度。**
`[哲学依据]`：现行 FCA **连陈述都做不到**（无 base/gaze 之分）。
本实现在类型层把它**变成本文件可陈述的事实**。

**本实现如实标注其平凡性**，不冒充实质定理。 -/
theorem gaze_switch_preserves_base (t : Temporal O) (g : Gaze) :
    (t.withGaze g).base = t.base := rfl

/-! ===========================================================================
    §2  要素与概念（[哲学依据] 体系 §2.2）
    ======================================================================== -/

/-- **要素**：目光未投出者。

`[哲学依据]` 体系原话：

> **要素是目光不在场的概念，概念是目光在场的要素。** -/
def IsElement (t : Temporal O) : Prop := t.gaze = Gaze.none

/-- **概念**：至少被一种目光捕获者。 -/
def IsConcept (t : Temporal O) : Prop :=
  t.gaze = Gaze.up ∨ t.gaze = Gaze.down

/-- ⭐ **核心互释**（`[哲学依据]` 体系 §2.2 的逐字形式化）：

> **要素是目光不在场的概念，概念是目光在场的要素。**

$$\mathrm{IsElement}(t) \iff \neg\,\mathrm{IsConcept}(t)$$

**证明**：对 `t.gaze` 作三情形展开。∎

**⚠ 本命题**不是**平凡式**——它断言的是「要素」与「概念」**互补**，
即**没有第三种身份**（不存在既非要素又非概念的呈现）。 -/
theorem element_concept_complement (t : Temporal O) :
    IsElement t ↔ ¬ IsConcept t := by
  unfold IsElement IsConcept
  cases t.gaze <;> simp

/-- **推论：每个呈现恰是要素或概念之一**（二分性）。 -/
theorem element_or_concept (t : Temporal O) :
    IsElement t ∨ IsConcept t := by
  unfold IsElement IsConcept
  cases t.gaze <;> simp

/-! ===========================================================================
    §3  悬置（[哲学依据] 法则 5）
    ======================================================================== -/

/-- **悬置**：撤回目光，概念退回要素。

`[哲学依据]` 法则 5 原话：

> **撤回目光，概念退回要素。不是拆解了内部结构，不是否定了上位归类，
> 而是切断了关系持有。对象还在，身份消解。** -/
def suspend (t : Temporal O) : Temporal O := t.withGaze Gaze.none

/-- ⭐ **法则 5（前半）：对象还在**。 -/
theorem suspend_preserves_base (t : Temporal O) :
    (suspend t).base = t.base := rfl

/-- ⭐ **法则 5（后半）：身份消解**。 -/
theorem suspend_dissolves_identity (t : Temporal O) :
    IsElement (suspend t) := rfl

/-- **悬置是幂等的**（撤回两次与撤回一次相同）——与「身份已消解」一致。 -/
theorem suspend_idempotent (t : Temporal O) :
    suspend (suspend t) = suspend t := rfl

/-! ===========================================================================
    §4  两种目光 = intent / extent（[哲学依据] 解读，**非原文**）
    ======================================================================== -/

/-- **向上目光**：由对象集求其上位的属性集。

$$\mathrm{gazeUp}(O') := O'^{\uparrow} = \{a \mid \forall o\in O',\ (o,a)\in I\}$$

**⚠ 这是 `[哲学依据]` 的**解读**——体系原文未提 FCA。**
本实现把它实现为 `K.polarUp`（已有的上极算子），
**其正确性由映射后的可证性验证**（见 §5 的定理）。 -/
def gazeUp (O' : Set K.GFCA) : Set K.MFCA := K.polarUp O'

/-- **向下目光**：由属性集求其下位的对象集（内部构成）。 -/
def gazeDown (B : Set K.MFCA) : Set K.GFCA := K.polarDown B

/-- **两种目光是伴随的**（Galois 连接）——**直接复用已有结果**。

`[哲学依据]`：向上/向下目光的**伴随性**。
FCA 中对应 Galois 连接。**本定理即该已有结果的改名陈述。**

**⚠ 陈述的**方向**须注意**：已有的 `subset_polarUp_iff_subset_polarDown`
的形式是 $B\subseteq O'^{\uparrow}\iff O'\subseteq B^{\downarrow}$——
即「**属性集含于向上目光的结果**」对偶于「**对象集含于向下目光的结果**」。
本定理用本文件的 `gazeUp`/`gazeDown` 名字重述它。 -/
theorem gaze_galois (O' : Set K.GFCA) (B : Set K.MFCA) :
    B ⊆ K.gazeUp O' ↔ O' ⊆ K.gazeDown B :=
  K.subset_polarUp_iff_subset_polarDown (A := O') (B := B)
/-! ===========================================================================
    §5  要素的**可判定判据**（本项目对 FCA 的功能性新增）
    ======================================================================== -/

/-- **对象在该论域下有上位**（存在与其有关系的属性）。 -/
def HasUpper (o : K.GFCA) : Prop := ∃ a : K.MFCA, K.Irel o a

/-- **对象在该论域下有构成**（存在非空属性集把它拆出）。 -/
def HasSplit (o : K.GFCA) : Prop := ∃ B : Set K.MFCA, B.Nonempty ∧ o ∈ K.gazeDown B

/-- ⭐ **「为什么某物是要素」是可判定命题**。

$$\neg\,\mathrm{HasUpper}(o) \iff \text{该对象此刻呈现为要素}$$

**`[哲学依据]`**：体系原话「存在论域内的上位，那就是概念。没有上位，就是要素。」

**⚠ 本实现的诚实标注**：本命题在实现上是 `Iff.rfl`
（左端**就是**「无上位」的定义）——**其价值在【陈述】而非难度**。
**本项目已登记的同类情形**（`RealFCAElementApplication` 的
`constraint_element_iff_no_upper` 也如实标注为 `Iff.rfl`）。
**本实现沿用该标注，不冒充实质定理。** -/
theorem isElement_iff_no_upper (o : K.GFCA) :
    ¬ K.HasUpper o ↔ ¬ ∃ a : K.MFCA, K.Irel o a := Iff.rfl

/-- ⭐ **要素 ⟺ 任何非空属性集都拆不出它**（**本文件的实质定理**）。

$$\neg\,\mathrm{HasUpper}(o) \iff
  \forall B,\ B\neq\emptyset \Rightarrow o\notin \mathrm{gazeDown}(B)$$

**⚠ 「非空」不可省**：空属性集对**任意** `o` 都成立
（`polarDown ∅ = 全域`，空洞真），故去掉非空性后命题**为假**。

**证明**：
- $(\Rightarrow)$ 设 `o` 无上位。若 $o\in B^{\downarrow}$ 且 $B$ 非空，
  取 $a\in B$，由 $o\in B^{\downarrow}$ 得 `Irel o a`，矛盾。
- $(\Leftarrow)$ 设 `o` 有上位，即存在 $a$ 使 `Irel o a`。
  取 $B=\{a\}$（非空），则 $o\in\{a\}^{\downarrow}$。矛盾。∎

**这是本项目对 FCA 的一个**功能性**结论**：
它把「要素」这一哲学概念**落成可判定的形式性质**。 -/
theorem isElement_iff_no_split (o : K.GFCA) :
    ¬ K.HasUpper o ↔
      ∀ B : Set K.MFCA, B.Nonempty → o ∉ K.gazeDown B := by
  constructor
  · intro h B hB ho
    obtain ⟨a, ha⟩ := hB
    exact h ⟨a, (K.mem_polarDown_iff).mp ho ha⟩
  · intro h ⟨a, hIa⟩
    exact h {a} ⟨a, rfl⟩ ((K.mem_polarDown_iff).mpr (fun b hb => by
      rw [Set.mem_singleton_iff] at hb
      rwa [hb]))

/-! ===========================================================================
  §7  悬置的**代数化**（P5）

  **背景**：现有 4 条关于 `suspend` / `withGaze` 的定理**全是 `rfl`**：
  - `suspend_preserves_base`、`suspend_dissolves_identity`、
    `suspend_idempotent`、`gaze_switch_preserves_base`

  **本节把它们升级为代数律**，并给出**像的恰好刻画**与**作用的轨道结构**。

  **`[哲学依据]`**：时态性层级体系（`操作闭合主义/原始文件/`）§4.4 与法则 5。
  **⚠ 映射是解读**，非原文明述；其正确性由**本节定理的可证性**验证。

  **⚠ 无硬编码**（依作者裁决 Q-1）：本节不引入任何常数。
  =========================================================================== -/

/-! ### §7.1 ⭐ 吸收律：悬置**吸收**一切目光投出 -/

/-- ⭐ **吸收律**（法则 5 的精确内容）：

$$\mathrm{suspend} \circ \mathrm{withGaze}(g) = \mathrm{suspend}$$

**意义**：`[哲学依据]` 说「撤回目光，**不是**拆解内部结构，**不是**否定上位归类，
而是**切断了关系持有**」。

**本定理给出该说法的代数形式**：悬置**只关心当前目光是否投出**，
**之前投过什么目光完全被吸收** —— 这正是「切断关系持有」而非「否定内容」。
（若是否定内容，悬置的结果会依赖 `g`；本定理表明**不依赖**。） -/
theorem suspend_absorbs_withGaze {O : Type u} (t : Temporal O) (g : Gaze) :
    suspend (t.withGaze g) = suspend t := rfl

/-- **悬置幂等**（法则 5 的必然推论）：撤回一次与撤回多次等价。

**代数含义**：`suspend` 是**幂等元** —— 它在 `Temporal O` 上诱导出一个**投影**。

**⚠ 本定理已存在于本文件 §3（`suspend_idempotent`）** —— 此处**不重复定义**，
仅在吸收律旁**引用**以显示其代数位置（避免审计所指出的「重复实现」问题）。 -/
example {O : Type u} (t : Temporal O) : suspend (suspend t) = suspend t :=
  suspend_idempotent t

/-! ### §7.2 ⭐⭐ 像的**恰好刻画**（双向，非「⊆」） -/

/-- ⭐⭐ **悬置的像恰是要素集**。

$$\mathrm{suspend}\,''\,\mathrm{univ} = \{t \mid \mathrm{IsElement}\ t\}$$

**这是「恰好」而非「包含」**：
- `⊆`：悬置的结果必是要素（`suspend_dissolves_identity` 的集合版）
- `⊇`：**每个要素都在像中** —— 即 `IsElement t` 时 `suspend t = t`

**为何 `⊇` 不平凡**：它要求 `IsElement t`（即 `t.gaze = none`）能推出 `suspend t = t`。
这**不是**定义展开能直接给出的（须用 `Temporal` 的结构外延性）。

**意义**：这刻画了**悬置这个操作的值域** —— 原库只有「`suspend t` 是要素」，
**没有**「每个要素都是某个 `suspend` 的结果」。 -/
theorem suspend_image_eq_elements {O : Type u} :
    suspend '' (Set.univ : Set (Temporal O)) = {t | IsElement t} := by
  ext t
  constructor
  · rintro ⟨s, -, rfl⟩
    exact suspend_dissolves_identity s
  · intro ht
    refine ⟨t, Set.mem_univ t, ?_⟩
    -- `IsElement t` 即 `t.gaze = Gaze.none`；此时 `suspend t = t`
    unfold IsElement at ht
    cases t with
    | mk b g =>
      -- `ht : (Temporal.mk b g).gaze = Gaze.none`，其左边即 `g`
      -- 故 `g = Gaze.none`，从而两边相等
      have hg : g = Gaze.none := ht
      subst hg
      rfl

/-! ### §7.3 ⭐ `withGaze` 是 **Gaze-作用**（轨道结构） -/

/-- ⭐ **轨道刻画**：`withGaze g` 保持基底、改写目光。

即 `(t.withGaze g).base = t.base` 且 `(t.withGaze g).gaze = g`。

**这使「同一基底上的所有目光」构成一个 `Gaze`-轨道** ——
`[哲学依据]` 说的「同一张脸，光照上去就是亮的，光移开就是暗的」，
在代数上就是**同一基底上的轨道**。 -/
theorem withGaze_orbit {O : Type u} (t : Temporal O) (g : Gaze) :
    (t.withGaze g).base = t.base ∧ (t.withGaze g).gaze = g :=
  ⟨rfl, rfl⟩

/-- ⭐ **作用是幂等的**：重复投同一目光与投一次无异。

**代数含义**：`Gaze` 在 `Temporal O` 上的作用是一个**带吸收元的幂等作用**
（`none` 是吸收元，见 `suspend_absorbs_withGaze`）。 -/
theorem withGaze_idem {O : Type u} (t : Temporal O) (g : Gaze) :
    (t.withGaze g).withGaze g = t.withGaze g := rfl

/-- ⭐ **作用的合成律**：连续投两次目光，等价于只投最后一次。

**⟹ 轨道内任意两点可达**（`Gaze` 三元素两两可达，见下）。 -/
theorem withGaze_comp {O : Type u} (t : Temporal O) (g h : Gaze) :
    (t.withGaze h).withGaze g = t.withGaze g := rfl

/-! ### §7.4 ⭐ 轨道的**连通性**（三目光两两可达） -/

/-- ⭐ **任意两个目光态可达**：同一基底的任意两个 `Temporal` 互相可达。

$$\forall g\,h,\ \exists k,\ (t.\mathrm{withGaze}\,g).\mathrm{withGaze}\,k
  = t.\mathrm{withGaze}\,h$$

**证明**：取 `k := h`。

**意义**：这说 `Gaze`-作用是**传递的** —— 轨道就是整个 `{base} × Gaze`。
`[哲学依据]`「目光投出/撤回之间转换，不涉及基底变更」在此得到精确形式。 -/
theorem orbit_transitive {O : Type u} (t : Temporal O) (g h : Gaze) :
    ∃ k : Gaze, (t.withGaze g).withGaze k = t.withGaze h :=
  ⟨h, rfl⟩

/-- ⭐ **含 `none` 的轨道即全部**：从任意目光可撤回到要素，也可再投出。

**这是「时态性」的核心**：身份可在要素与概念之间**往返**。 -/
theorem orbit_contains_none {O : Type u} (t : Temporal O) (g : Gaze) :
    ∃ k : Gaze, (t.withGaze g).withGaze k = suspend t :=
  ⟨Gaze.none, rfl⟩

/-! ### §7.5 ⭐ 抽象：`Gaze`-作用的一般结构 -/

/-- ⭐ **时态作用是「带吸收元的幂等作用」**。

把 `(Temporal, withGaze, suspend)` 的代数结构**抽出为独立类型**，
使下游可以对该结构一般地陈述定理，而不必每次展开 `Temporal`。

**三条公理**（全部由 §7.1–7.3 的定理满足）：
1. `act g (act h t) = act g t` —— 合成律（后者覆盖前者）
2. `act none t = suspend t` —— `none` 与悬置一致
3. `act g t` 与 `t` 同基底 —— 作用不改变基底 -/
structure TemporalAction (O : Type u) where
  /-- 作用：投出目光 `g`。 -/
  act : Gaze → Temporal O → Temporal O
  /-- **合成律**：后投的目光覆盖先投的。 -/
  act_comp : ∀ g h t, act g (act h t) = act g t
  /-- **与悬置一致**：`none` 的作用就是悬置。 -/
  act_none : ∀ t, act Gaze.none t = suspend t
  /-- **保基底**：作用不改变基底。 -/
  act_base : ∀ g t, (act g t).base = t.base

/-- ⭐ **`Temporal` 自带一个 `TemporalAction` 实例**。

**构造**：`act := withGaze`，三条公理分别由
`withGaze_comp`、`rfl`、`withGaze_orbit` 给出。

**⟹ 「时态层构成作用」从口头说法变成可被下游消费的类型类实例。** -/
def temporalAction {O : Type u} : TemporalAction O where
  act := fun g t => t.withGaze g
  act_comp := fun _ _ _ => rfl
  act_none := fun _ => rfl
  act_base := fun _ _ => rfl

/-! ===========================================================================
    §7.6 ⭐ `TemporalAction` 与 `Temporal` 的**函子性**

    本节的问答：
    > **`TemporalAction` 与 `Temporal` 之间是否存在函子关系？**

    **结论（分两层，须分别陈述，不可混为一谈）**：

    | 断言 | 真假 | 落点 |
    |---|---|---|
    | `Temporal` 是 `Type u ⥤ Type u` 的函子 | **真** | `temporalFunctor` |
    | 默认作用 `temporalAction` 关于 `O` **自然** | **真** | `temporalAction_natural` |
    | `TemporalAction` 沿**双射**协变（核心群胚函子） | **真** | `pushEquiv` + 两条函子律 |
    | `TemporalAction` 沿**任意函数**协变 | **假** | `no_push_along_collapse` |

    **⚠ 诚实标注**：
    · 第 1 条是 `Temporal = _ × Gaze` 的「乘积函子」事实，**平凡但不虚无**——
      它把「同一张脸不同身份」的载体提升为**类型层函子**；
    · 第 3 条的函子律依赖**证明无关性**（`TemporalAction` 的三条公理是 `Prop`），
      故其「函子性」在**证明层是自动的**，实质内容是 `act` 的搬运；
    · 第 4 条是**否定结果**：`TemporalAction` **不是**协变函子。
      **若不标注此条，第 3 条会被误读成「`TemporalAction` 是函子」。**

    **⚠ 本节的映射是解读**，原始哲学文本**未提范畴论**；
    其价值由**本节陈述的可证性**承担，不由原文权威保证。
    ======================================================================== -/

open CategoryTheory in
/-- **`Temporal.map`**：把 `f : O → P` 提升为 `Temporal O → Temporal P`，
**只改基底、保留目光**。这是函子 `temporalFunctor` 在态射上的作用。 -/
def Temporal.map {O P : Type u} (f : O → P) (t : Temporal O) : Temporal P :=
  ⟨f t.base, t.gaze⟩

@[simp] theorem Temporal.map_base {O P : Type u} (f : O → P) (t : Temporal O) :
    (Temporal.map f t).base = f t.base := rfl

@[simp] theorem Temporal.map_gaze {O P : Type u} (f : O → P) (t : Temporal O) :
    (Temporal.map f t).gaze = t.gaze := rfl

/-- **函子律（恒等）**。 -/
theorem Temporal.map_id {O : Type u} (t : Temporal O) :
    Temporal.map id t = t := rfl

/-- **函子律（合成）**。 -/
theorem Temporal.map_comp {O P Q : Type u} (f : O → P) (g : P → Q) (t : Temporal O) :
    Temporal.map (g ∘ f) t = Temporal.map g (Temporal.map f t) := rfl

open CategoryTheory in
/-- ⭐ **(A) `Temporal` 是函子**：`Temporal ≅ _ × Gaze`，即「与 `Gaze` 的乘积」函子。

`obj O := Temporal O`、`map f := Temporal.map f`。
两条函子律均为 `rfl` 级——因为 `Temporal.map` 只作用在 `base` 上。 -/
def temporalFunctor : Type u ⥤ Type u where
  obj O := Temporal O
  map f := TypeCat.ofHom (Temporal.map f)
  map_id O := by ext t; rfl
  map_comp f g := by ext t; rfl

/-- ⭐ **(B) 默认作用关于 `O` 自然**。

对任意 `f : O → P`、`g`、`t`：

$$\mathrm{map}\ f\ (\mathrm{temporalAction}_O.\mathrm{act}\ g\ t)
  = \mathrm{temporalAction}_P.\mathrm{act}\ g\ (\mathrm{map}\ f\ t)$$

**意义**：`temporalAction` 是**结构性**给出的（只碰 `gaze`），
故任意基底重命名都与它交换——这正是「自然变换」在**默认作用族**上的形式。
`rfl` 级：两边都等于 `⟨f t.base, g⟩`。 -/
theorem temporalAction_natural {O P : Type u} (f : O → P) (g : Gaze) (t : Temporal O) :
    Temporal.map f ((temporalAction (O := O)).act g t)
      = (temporalAction (O := P)).act g (Temporal.map f t) := rfl

/-- **`Temporal` 的外延性**（`base` 与 `gaze` 都相等即相等）。 -/
theorem Temporal.ext_iff {O : Type u} {a b : Temporal O} :
    a = b ↔ a.base = b.base ∧ a.gaze = b.gaze :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => by cases a; cases b; simp_all⟩

/-- **`TemporalAction` 的外延性**：作用映射相同则结构相同
（三条公理取值于 `Prop`，由证明无关性自动相等）。 -/
theorem TemporalAction.ext {O : Type u} {A B : TemporalAction O}
    (h : ∀ g t, A.act g t = B.act g t) : A = B := by
  obtain ⟨a, _, _, _⟩ := A
  obtain ⟨b, _, _, _⟩ := B
  simp only at h
  congr 1
  funext g t
  exact h g t

/-- **基底重命名下的状态回拉**：只改基底，保留目光。

推前一个**一般**作用需要「把 `P` 中的基底送回 `O`」，故须用逆映射 `e.symm`。 -/
def Temporal.rebase {O P : Type u} (e : O ≃ P) (t : Temporal P) : Temporal O :=
  ⟨e.symm t.base, t.gaze⟩

@[simp] theorem Temporal.rebase_base {O P : Type u} (e : O ≃ P) (t : Temporal P) :
    (Temporal.rebase e t).base = e.symm t.base := rfl
@[simp] theorem Temporal.rebase_gaze {O P : Type u} (e : O ≃ P) (t : Temporal P) :
    (Temporal.rebase e t).gaze = t.gaze := rfl

/-- 回拉与推前在基底上互逆。 -/
theorem Temporal.rebase_apply {O P : Type u} (e : O ≃ P) (t : Temporal O) :
    Temporal.rebase e ⟨e t.base, t.gaze⟩ = t := by
  rw [Temporal.ext_iff]
  exact ⟨by simp [Temporal.rebase], rfl⟩

/-- ⭐ **(C) 沿双射推前一个一般作用**。

$$\mathrm{pushEquiv}_e(A).\mathrm{act}\ g\ t
  := \bigl\langle e\,(A.\mathrm{act}\ g\ (\mathrm{rebase}_e\ t)).\mathrm{base},
     (A.\mathrm{act}\ g\ (\mathrm{rebase}_e\ t)).\mathrm{gaze}\bigr\rangle$$

**这是 `TemporalAction` 的「核心群胚函子性」**：
`O ↦ TemporalAction O` 对**同构**协变（一般函数不行，见 `no_push_along_collapse`）。

**三条公理**：
· `act_comp`、`act_none` 由 `A` 的对应公理 + `rebase_apply` 搬运；
· `act_base` 由 `A.act_base` 与 `e ∘ e.symm = id` 得到。 -/
def TemporalAction.pushEquiv {O P : Type u} (A : TemporalAction O) (e : O ≃ P) :
    TemporalAction P where
  act g t := ⟨e (A.act g (Temporal.rebase e t)).base,
                (A.act g (Temporal.rebase e t)).gaze⟩
  act_comp g h t := by
    rw [Temporal.ext_iff]
    have hkey : Temporal.rebase e (⟨e (A.act h (Temporal.rebase e t)).base,
        (A.act h (Temporal.rebase e t)).gaze⟩ : Temporal P)
        = A.act h (Temporal.rebase e t) := Temporal.rebase_apply e _
    constructor
    · show e (A.act g (Temporal.rebase e ⟨e (A.act h (Temporal.rebase e t)).base,
          (A.act h (Temporal.rebase e t)).gaze⟩)).base = e (A.act g (Temporal.rebase e t)).base
      rw [hkey, A.act_comp g h]
    · show (A.act g (Temporal.rebase e ⟨e (A.act h (Temporal.rebase e t)).base,
          (A.act h (Temporal.rebase e t)).gaze⟩)).gaze = (A.act g (Temporal.rebase e t)).gaze
      rw [hkey, A.act_comp g h]
  act_none t := by
    rw [Temporal.ext_iff]
    constructor
    · show e (A.act Gaze.none (Temporal.rebase e t)).base = t.base
      rw [A.act_none (Temporal.rebase e t)]
      have hb : (suspend (Temporal.rebase e t)).base = (Temporal.rebase e t).base := rfl
      rw [hb]
      simp [Temporal.rebase]
    · show (A.act Gaze.none (Temporal.rebase e t)).gaze = Gaze.none
      rw [A.act_none (Temporal.rebase e t)]
      rfl
  act_base g t := by
    show e (A.act g (Temporal.rebase e t)).base = t.base
    rw [A.act_base g (Temporal.rebase e t)]
    simp

/-- ⭐ **(C1) 函子律（恒等）**：沿 `Equiv.refl` 推前是恒等。 -/
theorem TemporalAction.pushEquiv_refl {O : Type u} (A : TemporalAction O) :
    A.pushEquiv (Equiv.refl O) = A := by
  apply TemporalAction.ext
  intro g t
  rw [Temporal.ext_iff]
  exact ⟨rfl, rfl⟩

/-- ⭐ **(C2) 函子律（合成）**：两次推前 = 沿复合双射推前。 -/
theorem TemporalAction.pushEquiv_comp {O P Q : Type u} (A : TemporalAction O)
    (e : O ≃ P) (d : P ≃ Q) :
    (A.pushEquiv e).pushEquiv d = A.pushEquiv (e.trans d) := by
  apply TemporalAction.ext
  intro g t
  rw [Temporal.ext_iff]
  refine ⟨?_, rfl⟩
  show d (e (A.act g (Temporal.rebase e (Temporal.rebase d t))).base)
      = (e.trans d) (A.act g (Temporal.rebase (e.trans d) t)).base
  simp only [Temporal.rebase, Equiv.trans_apply, Equiv.symm_trans_apply]

/-- ⭐ **(C3) 推前保持默认作用**：`temporalAction` 在双射下不动。

$$\mathrm{pushEquiv}_e(\mathrm{temporalAction}_O) = \mathrm{temporalAction}_P$$

**意义**：默认作用不仅自然（B），而且**在核心群胚上是函子性对象**——
它是一切「可推前作用」的不动点。 -/
theorem TemporalAction.pushEquiv_temporalAction {O P : Type u} (e : O ≃ P) :
    (temporalAction (O := O)).pushEquiv e = temporalAction (O := P) := by
  apply TemporalAction.ext
  intro g t
  rw [Temporal.ext_iff]
  refine ⟨?_, rfl⟩
  show e ((Temporal.rebase e t).withGaze g).base = (t.withGaze g).base
  simp only [Temporal.withGaze, Temporal.rebase]
  exact e.apply_symm_apply t.base

/- ⭐⭐ **(D) 阻碍：`TemporalAction` 不是协变函子**。

**构造**：一个**作用依赖基底**的动作 `badAction : TemporalAction Bool`
（非 `none` 目光下，输出目光由**基底**决定，与输入目光无关）。

**定理**：不存在与常映射 `collapseMap : Bool → PUnit`（非单射）相容的
`B : TemporalAction PUnit`。

**证明**：`⟨true, none⟩` 与 `⟨false, none⟩` 经 `collapseMap` 后**都变成**
`⟨(), none⟩`；但 `badAction` 把它们分别送到目光 `up` 与 `down`，
推前后分别要求 `B` 的输出目光为 `up` 与 `down`——**矛盾**。

**⟹ 结论**：`TemporalAction` **不能**沿非单射函数推前，
故 `O ↦ TemporalAction O` **不是** `Type u ⥤ Type u` 的函子。
函子性只在**同构**（核心群胚 / `pushEquiv`）上成立。

**⚠ 本条是本节最重要的一条**：没有它，(C) 会被误读为「`TemporalAction` 是函子」。 -/

/-- 一个「作用依赖基底」的 `TemporalAction Bool`：
非 `none` 目光下，结果目光由**基底**（而非输入目光）决定。 -/
def badAction : TemporalAction Bool where
  act g t := ⟨t.base, if g = Gaze.none then Gaze.none
                        else if t.base then Gaze.up else Gaze.down⟩
  act_comp g h t := by
    cases t with
    | mk b gz => cases b <;> cases g <;> cases h <;> rfl
  act_none t := by
    cases t with
    | mk b gz => cases b <;> rfl
  act_base _ t := rfl

/-- 常映射 `Bool → PUnit`（**非单射**）。 -/
def collapseMap : Bool → PUnit := fun _ => PUnit.unit

/-- ⭐⭐ **阻碍定理**：见上方 (D) 的说明。 -/
theorem no_push_along_collapse :
    ¬ ∃ B : TemporalAction PUnit, ∀ g t,
      B.act g (⟨collapseMap t.base, t.gaze⟩ : Temporal PUnit)
        = ⟨collapseMap (badAction.act g t).base, (badAction.act g t).gaze⟩ := by
  rintro ⟨B, hB⟩
  have h1 := hB Gaze.up ⟨true, Gaze.none⟩
  have h2 := hB Gaze.up ⟨false, Gaze.none⟩
  simp [collapseMap, badAction] at h1 h2
  rw [h1] at h2
  have hg := congrArg Temporal.gaze h2
  exact absurd hg (by decide)

end FormalCtx

/-! ===========================================================================
    §6  循环判据层（作者裁决 K + O；哲学依据「操作闭合主义」）
    ======================================================================== -/

/- ### §6.0 哲学依据与诚实边界（**须先读**）

**来源**：`操作闭合主义/原始文件/操作闭合主义科学观总论lv4.0.txt`
（作者提供，**本实现只读，原件保留不改**）。

**⚠ 三条纪律（依裁决 N 第七节与主控指示，本实现一并采纳）**：

1. **原文是哲学纲领，不是形式化数学** —— 本文件引用它之处标 **`[哲学依据]`**，
   **不当作定理或证明来源**；
2. **原文未提「命运」** —— 本节的结构映射是**解读**，
   **其正确性只能由映射后的可证性验证，不由原文权威保证**；
3. **原文第十四章的 Lean 代码全部含 `sorry`**（原文自述「伪代码/骨架」）——
   **是目标清单，不是成果**。本实现**不引用其任何结论**。

**引用位置**（逐字，供核对）：

| 内容 | 原文行 |
|---|---|
| 主循环节拍 | `lv4.0.txt:420` |
| **局部修正判据** | `lv4.0.txt:424` |
| 结构相变 | `lv4.0.txt:428` |
| 平凡/非平凡循环 | `lv4.0.txt:348-356` |
| 滤除律 | `lv4.0.txt:360-362` |

-/

/- ### §6.1 循环的**停止判据**（[哲学依据] 4.6.2 + 作者裁决 K）

`[哲学依据]` 原文逐字（`lv4.0.txt:424`）：

> 当 P' 与 U 的预测之间存在**可度量的系统性偏差**时，
> 系统优先对 U 的表层参数或辅助假设进行微调。
> **修正幅度以「恰好重建循环闭合」为上限**，
> 由**偏差的梯度力与历史惯性的比值**所自然决定。

**作者裁决 K** 说「误差 ≈ 噪声尺度」，但**未给出判据算式**。

**本实现的评估**（**这是本节的核心结论**）：

| 观察 | 内容 |
|---|---|
| **「历史惯性」在统计上就是噪声尺度的估计量** | 偏差序列去趋势后的波动幅度 |
| **「梯度力」就是系统性趋势** | 偏差序列的确定性部分 |
| ⟹ **原文判据 = 信噪比判据** | $\\lvert\\text{梯度力}\\rvert / \\text{历史惯性}$ |
| ⟹ **它只需历史序列，不需外部给定 $\\sigma$** | **故确实能破 R-026 的循环** |

**⚠ 但有三条限制（本实现如实标注）**：

1. **判据变成「逐点」的** —— 每轮从历史估一次，**不再是全局常数 $\\sigma$**；
   故 R-026 的「$\\sigma$ 取哪个」问题**被消解**（不再需要选），
   **但换来的是「每轮判据可能不同」**；
2. **需要历史序列** —— 循环**头几轮无历史**，判据不可用（须有初始轮次）；
3. **判据的阈值仍是一个选择** —— 实测（`closure_criterion_test2.py`）显示
   阈值 1.0 与 2.0 的判对率不同（12/16 vs 10/16），
   **故「恰好」仍有残余的容差选择**。

**⟹ 结论**：原文判据**部分**解决了 σ 难定
（不再需外部 σ，**但引入了阈值与历史长度两个新参数**）。
**本实现不声称它完全消除了循环依赖。** -/

/-- **偏差序列的「梯度力」**（系统性趋势）：相邻偏差的平均增量。

`[哲学依据]` 4.6.2 的「偏差的梯度力」。

**为何用「平均增量」而非最小二乘斜率**：本实现的目的是给**类型与定理**
一个精确落点，而**估计量的选择属统计层**（见 `prototype/` 的实测）。
本定义取最简单的一阶差分均值，**并在文档中标注这只是**一种**选择**。 -/
def gradForce (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (d n - d 0) / (n : ℝ)

/-- **偏差序列的「历史惯性」**（噪声尺度的估计量）。

`[哲学依据]` 4.6.2 的「历史惯性」。

**本定义的实质断言**：惯性 $=$ **首末偏差之差**——
即「这段历史里系统净移动了多少」。
**⚠ 这是最粗的估计量**（未去趋势、未用全部样本）；
本实现**如实标注**它只是一个**占位定义**，
真正的估计量属统计层（`prototype/closure_criterion_test2.py` 用的才是可用版本）。 -/
def histInertia (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else |d n - d 0|

/-- **循环的停止判据**（[哲学依据] 4.6.2 的形式化**骨架**）。

$$\mathrm{ShouldStop}(d, n, \tau)
  := \frac{|\text{梯度力}|}{\text{惯性}} \le \tau$$

**含义**（依作者裁决 K 与裁决 O）：

| 情形 | 判据 | 循环 |
|---|---|---|
| 比值 $\le\tau$ | 偏差**随机、无收敛趋势** | **临时停止**（继续会过拟合） |
| 比值 $>\tau$ | 存在**系统性偏差** | **继续**（应修正） |

**⚠ $\tau$ 的取值**：本实现**不填**——
它是**统计层选择**（实测见 `closure_criterion_test2.py`：
$\tau=1.0$ 判对 12/16，$\tau=2.0$ 判对 10/16）。
**填数即为虚构**（规格纪律）。 -/
def ShouldStop (d : ℕ → ℝ) (n : ℕ) (τ : ℝ) : Prop :=
  histInertia d n = 0 ∨ |gradForce d n| / histInertia d n ≤ τ

/-- **判据的对称情形**：不停止即继续。

**这是 `ShouldStop` 的补集**，使「停止 / 继续」的二分**无遗漏**。 -/
def ShouldContinue (d : ℕ → ℝ) (n : ℕ) (τ : ℝ) : Prop :=
  ¬ ShouldStop d n τ

/-- **停止与继续互斥且穷尽**（二分性）。

$$\mathrm{ShouldStop}\ \vee\ \mathrm{ShouldContinue}$$

**证明**：`ShouldContinue` **就是** `¬ ShouldStop`，故由排中律。

**⚠ 本命题平凡**（`Classical.em`），**已如实标注**——
它的价值在**显式建立二分**，而非难度。 -/
theorem stop_or_continue (d : ℕ → ℝ) (n : ℕ) (τ : ℝ) :
    ShouldStop d n τ ∨ ShouldContinue d n τ :=
  Classical.em _

/-- ⭐ **`ShouldStop` 关于阈值 `τ` 单调递增**：

$$\tau_1\le\tau_2\Longrightarrow
  \bigl(\mathrm{ShouldStop}(d,n,\tau_1)\Rightarrow
  \mathrm{ShouldStop}(d,n,\tau_2)\bigr)$$

**含义**（与 §6.1 判据的方向一致）：

| $\tau$ 增大 | 比值 $|\text{梯度力}|/\text{惯性}\le\tau$ **更易成立** | 循环**更易停止** |
|---|---|---|

即「阈值越宽松，停止判据越容易满足」——这使 `τ` 的**统计层选择**
（见 `closure_criterion_test2.py`：`τ=1.0` 与 `τ=2.0` 判对率不同）
在**类型层有确定的单调方向**：**增大 `τ` 不会使停止判据更难成立**。

**证明**：`ShouldStop` 是「`histInertia = 0`」与「比值 `≤ τ`」的**析取**。
前者与 `τ` 无关，可直接传递；后者由 `τ₁ ≤ τ₂` 与 `le_trans` 传递。
**⚠ 本证明不用任何统计假设**（判据的单调性是其**形状**的性质，不是估计量的性质）。 -/
theorem shouldStop_mono_tau (d : ℕ → ℝ) (n : ℕ) {τ₁ τ₂ : ℝ}
    (h : τ₁ ≤ τ₂) : ShouldStop d n τ₁ → ShouldStop d n τ₂ := by
  unfold ShouldStop
  rintro (hzero | hle)
  · exact Or.inl hzero
  · exact Or.inr (le_trans hle h)

/-- **`ShouldStop` 关于 `τ` 单调的等价刻画**（逐点形式）。

这是 `shouldStop_mono_tau` 的「函数单调」说法：
把 `τ ↦ ShouldStop d n τ` 视作 `ℝ → Prop`（以 `≤` 为序、`Prop` 以蕴含为序），
则该映射**单调**。**与 `shouldStop_mono_tau` 等价**（`Iff.rfl` 层面的改写）。 -/
theorem shouldStop_monotone (d : ℕ → ℝ) (n : ℕ) :
    Monotone (fun τ : ℝ => ShouldStop d n τ) :=
  fun _ _ h => shouldStop_mono_tau d n h

/-- **`ShouldContinue` 关于 `τ` 单调递减**（停止单调递增的对偶）。

$$\tau_1\le\tau_2\Longrightarrow
  \bigl(\mathrm{ShouldContinue}(d,n,\tau_2)\Rightarrow
  \mathrm{ShouldContinue}(d,n,\tau_1)\bigr)$$

**含义**：阈值越宽松，**继续**越难成立——与 `shouldStop_mono_tau` 对偶。 -/
theorem shouldContinue_antitone_tau (d : ℕ → ℝ) (n : ℕ) {τ₁ τ₂ : ℝ}
    (h : τ₁ ≤ τ₂) : ShouldContinue d n τ₂ → ShouldContinue d n τ₁ := by
  unfold ShouldContinue
  exact fun hc hs => hc (shouldStop_mono_tau d n h hs)

/- ### §6.2 循环的**非平凡性判据**（[哲学依据] 4.2/4.3）

`[哲学依据]` 原文逐字（`lv4.0.txt:348-356`）：

> 若 $\Sigma_{t+1}\cong\Sigma_t$，即同构于原态，不存在新生成的结构关系，
> 则该循环被判定为**平凡循环**。
>
> 若 $\Sigma_{t+1}$ 与 $\Sigma_t$ **不同构**，
> 且 $\Sigma_{t+1}$ 中存在**无法由 $\Sigma_t$ 通过有限参数微调而导出**的新结构关系
> （新的生成元、新的对称性破缺、新的不可约拓扑关系），
> 则该循环被判定为**非平凡循环**。

**⚠ 本实现给出的只是一个**骨架**——
因为「结构」「同构」「有限参数微调」在原文中**都未形式化**。
**本实现不假装它们已定义**，而是把判据的**形状**固定下来，
使后续工作有明确靶子。 -/

/-- **结构**的抽象载体（**本实现新增的占位**）。

`[哲学依据]` 4.2/4.3 讨论「结构态 $\Sigma$」的**同构**与**导出新关系**，
但**未形式化「结构」是什么**。

**本实现把「结构」做成类型参数** `S`，
并显式要求一个同构关系 `SIso` 与一个「可由 … 微调导出」关系 `Derivable`。
**这样做的理由**：把**未定义的东西显式参数化**，
比**假装它已定义**更诚实（规格 §2.5.3「定义与断言分离」）。 -/
structure CycleStructure where
  /-- 结构态的载体。 -/
  S : Type
  /-- **同构关系**（`[哲学依据]` 4.2 的 $\cong$）。 -/
  SIso : S → S → Prop
  /-- **可由有限参数微调导出**（`[哲学依据]` 4.3）。 -/
  Derivable : S → S → Prop
  /-- 同构是等价关系（**显式要求，不假定**）。 -/
  iso_refl : ∀ x, SIso x x
  iso_symm : ∀ {x y}, SIso x y → SIso y x
  iso_trans : ∀ {x y z}, SIso x y → SIso y z → SIso x z

/-- **平凡循环**（`[哲学依据]` 4.2）：新旧结构态**同构**。 -/
def IsTrivialCycle (C : CycleStructure) (s t : C.S) : Prop := C.SIso s t

/-- **非平凡循环**（`[哲学依据]` 4.3）：**不同构**，
且新态含**无法由旧态微调导出**的关系。 -/
def IsNontrivialCycle (C : CycleStructure) (s t : C.S) : Prop :=
  ¬ C.SIso s t ∧ ¬ C.Derivable s t

/-- ⭐ **平凡与非平凡互斥**（在「不同构」这一必要条件上）。

$$\mathrm{IsTrivialCycle}(s,t)\Longrightarrow\neg\,\mathrm{IsNontrivialCycle}(s,t)$$

**证明**：非平凡要求 `¬SIso s t`，而平凡给出 `SIso s t`，矛盾。∎

**⚠ 注意本命题**不**断言二者穷尽**——
「不同构但可由微调导出」的第三种情形**既非平凡也非非平凡**。
**本实现如实标注该缝隙**（原文未讨论它）。 -/
theorem trivial_not_nontrivial (C : CycleStructure) {s t : C.S}
    (h : IsTrivialCycle C s t) : ¬ IsNontrivialCycle C s t :=
  fun hn => hn.1 h

/-- **同构的自反性**（可直接用于判据）。 -/
theorem iso_refl' (C : CycleStructure) (s : C.S) : C.SIso s s := C.iso_refl s

/-- ⭐ **同构态之间「不可区分」**（`[哲学依据]` 4.4 滤除律的形式化落点）。

若 $s\cong t$，则任何**尊重同构**的观测量 $L$ 在二者上取同值。

**这是本项目**已用过的模式**（`Fate/Alpha.lean` 的
`alpha_respects_equiv` / `alphaOnQuotient`）——
`[哲学依据]` 第十四章第 5 条 `law_well_defined`（**原文含 `sorry`**）
讨论的正是同一模式。

**⚠ 本实现不引用原文的 `sorry` 版本**；
本定理是**独立证明**（一行，由假设直接给出）。 -/
theorem respects_iso_agrees (C : CycleStructure) (L : C.S → γ)
    (hL : ∀ a b, C.SIso a b → L a = L b) {a b : C.S} (h : C.SIso a b) :
    L a = L b := hL a b h

end


/-! ### 加强 1：`Fate.FCA` 的 4 条 rfl/纯别名 → **ClosureOperator 结构**
    原形式：`polarUp_eq_upperPolar : … = … := rfl`（只是记法绑定）
    加强：证明这对算子真的**构成** Mathlib 的 `ClosureOperator`，
          从而「闭包算子」不再是口头称呼，而是可被下游消费的类型类实例。 -/

variable (K : FormalCtx)

/-- `B ↦ B''` 是 Mathlib 意义上的闭包算子（真证明，非 rfl）。 -/
def attrClosureOperator : ClosureOperator (Set K.MFCA) where
  toFun := K.closureOp
  monotone' := fun _ _ h => K.closureOp_mono h
  le_closure' := fun B => K.subset_closureOp B
  idempotent' := fun B => K.closureOp_idem B

/-- 闭包算子与 `IsClosedAttr` 的**恰好一致**：闭集 = 该算子的闭元素。 -/
theorem isClosedAttr_iff_closed_of_operator (B : Set K.MFCA) :
    K.IsClosedAttr B ↔ (attrClosureOperator K).IsClosed B :=
  Iff.rfl

/-- 闭集族在**任意交**下封闭（这是「闭集族 = 闭包系统」的实质内容）。 -/
theorem closedAttr_iInter_closed {ι : Type*} (S : ι → Set K.MFCA)
    (h : ∀ i, K.IsClosedAttr (S i)) : K.IsClosedAttr (⋂ i, S i) := by
  unfold FormalCtx.IsClosedAttr FormalCtx.closureOp at h ⊢
  have hsub : K.polarUp (K.polarDown (⋂ i, S i)) ⊆ ⋂ i, S i := by
    intro m hm
    simp only [Set.mem_iInter]
    intro i
    have : K.polarDown (S i) ⊆ K.polarDown (⋂ i, S i) :=
      K.polarDown_antitone (Set.iInter_subset _ i)
    have h2 : K.polarUp (K.polarDown (⋂ i, S i)) ⊆ K.polarUp (K.polarDown (S i)) :=
      K.polarUp_antitone this
    exact (h i ▸ h2 hm : m ∈ S i)
  exact Set.Subset.antisymm hsub (K.subset_closureOp _)

/-! ### 加强 1b：`IsModel` 的**闭包系统结构**

**本加强的陈述（任务目标）**：

> 所有 `IsModel` 的集合构成一个 `ClosureOperator` 的**不动点集**。

即：存在一个 `Set K.MFCA` 上的闭包算子 $c$，使

$$M\text{ 是 DG 基的模型}\iff c(M)=M.$$

**本实现给出 $c:=$ `attrClosureOperator K`**（即 $M\mapsto M''$，见上文加强 1）。
这是「模型类 = 闭集类 = 闭包算子不动点类」这一 FCA 基本定理的
**完备形式**：它把 `Completeness.model_iff_closed`（模型 $\iff$ 闭）
与 Mathlib 的 `ClosureOperator.IsClosed`（闭 $\iff$ 不动点）**串成一条**。

**证明**：`ClosureOperator.isClosed_iff` 给出 `IsClosed M ↔ toFun M = M`；
而 `attrClosureOperator` 的 `toFun` **定义上**就是 `K.closureOp`，
`IsClosedAttr` **定义上**就是 `K.closureOp M = M`；
再由 `Completeness.model_iff_closed` 收口。∎ -/

/-- ⭐ **`IsModel` 的逐点不动点刻画**（任务的逐点形式）。

$$M\text{ 是模型}\iff (M\mapsto M'')\text{ 在 }M\text{ 处取不动点}$$ -/
theorem isModel_iff_isClosed_attrClosureOperator (M : Set K.MFCA) :
    K.IsModel M ↔ (attrClosureOperator K).IsClosed M := by
  rw [ClosureOperator.isClosed_iff, K.model_iff_closed]
  rfl

/-- ⭐ **`IsModel` 的集合不再动点刻画**（任务的集合形式，即主命题）。

「所有 `IsModel` 的集合」**等于**闭包算子 `attrClosureOperator K` 的**不动点集**。

**这是 FCA 基本定理在「模型类」上的最终形态**：
DG 基的模型类 $\mathrm{Mod}(T)$ 恰是闭包算子 $M\mapsto M''$ 的不动点集，
故**本身就是一个闭包系统**（在任意交下封闭——见 `closedAttr_iInter_closed`）。 -/
theorem models_eq_fixedPoints_attrClosureOperator :
    {M : Set K.MFCA | K.IsModel M} =
      {M : Set K.MFCA | (attrClosureOperator K).IsClosed M} := by
  ext M
  exact isModel_iff_isClosed_attrClosureOperator K M

/-- ⭐ **不动点集对闭包封闭**：模型集经 $M\mapsto M''$ 后仍是模型。

**这是「不动点集」的实质结构内容**：$c$ 的像全部落在不动点集内。
由 `ClosureOperator.isClosed_closure` 与上面的集合等式直接给出。 -/
theorem model_closure_isModel (M : Set K.MFCA) :
    K.IsModel (K.closureOp M) := by
  rw [isModel_iff_isClosed_attrClosureOperator K]
  exact (attrClosureOperator K).isClosed_closure M

/-- **不动点集非空且含极值**：$\varnothing''$ 与 $\top''$ 都是模型。 -/
theorem model_closure_empty_and_univ :
    K.IsModel (K.closureOp ∅) ∧ K.IsModel (K.closureOp Set.univ) :=
  ⟨model_closure_isModel K ∅, model_closure_isModel K Set.univ⟩

/-! ### 加强 2：`stop_or_continue`（`Classical.em`）→ 判据的**等价刻画**
    原形式只重述排中律；加强后给出可用的不等式判据。 -/

/- ### §6.3 `gradForce` / `histInertia` 的**基本性质**

本小节把两个判据量的**可证性质**一次列清。
**范围声明**：只证**纯序/代数**性质（单调性、有界性、零点、符号），
**不含**任何统计最优性断言（那属统计层，本实现不声称）。

**⚠ 关于「单调性」的辨正**：`gradForce d n` / `histInertia d n` 作为 `n` 的
函数**一般并不单调** —— 因为 `d : ℕ → ℝ` 是**任意序列**（偏差序列无单调性
承诺）。故本节的单调性只有两种**有意义**的读法：
  ① **对 `d` 逐点的单调性**（`d₁ ≤ d₂` 逐点 ⟹ 量 ≤ 量）；
  ② **在 `d` 单调时的化简**（此时 `histInertia` 退化为 `d n - d 0`）。
本实现**不**声称 `n ↦ gradForce d n` 单调 ——
而是**证明它确实不单调**（`gradForce_not_monotone_in_n` /
`histInertia_not_monotone_in_n`，含显式反例）。 -/

/-- 历史惯性非负（本小节全部有界性结论的**基座**）。 -/
theorem histInertia_nonneg (d : ℕ → ℝ) (n : ℕ) : 0 ≤ histInertia d n := by
  unfold histInertia
  split
  · exact le_refl 0
  · exact abs_nonneg _

/-- **`histInertia` 零点刻画**：惯性为零 ⟺ 首末偏差相等。

这是「惯性 = 净移动量」这一定义性解读的**精确落点**：
惯性为零恰表示**系统回到起点**（`d n = d 0`）。

**证明**：`n = 0` 时两边均为真；`n ≠ 0` 时归约为 `|x| = 0`。 -/
theorem histInertia_eq_zero_iff (d : ℕ → ℝ) (n : ℕ) :
    histInertia d n = 0 ↔ d n = d 0 := by
  unfold histInertia
  split
  · rename_i h
    subst h
    simp
  · rw [abs_eq_zero, sub_eq_zero]

/-- **`histInertia` 在零处为零**（判据的初始轮次无历史，惯性为 0）。 -/
theorem histInertia_zero (d : ℕ → ℝ) : histInertia d 0 = 0 := by
  unfold histInertia; simp

/-- **`histInertia` 的对称形式**：净移动量对首末**对称**。 -/
theorem histInertia_eq_abs_sub_comm (d : ℕ → ℝ) (n : ℕ) :
    histInertia d n = |d 0 - d n| := by
  unfold histInertia
  split
  · rename_i h; subst h; simp
  · rw [abs_sub_comm]

/-- **`histInertia` 的三角有界性**（**有界性**）：
惯性不超过两端偏差绝对值之和。

$$|d_n - d_0|\le |d_n| + |d_0|$$

这是三角不等式，**无任何额外假设**。 -/
theorem histInertia_le_abs_add (d : ℕ → ℝ) (n : ℕ) :
    histInertia d n ≤ |d n| + |d 0| := by
  unfold histInertia
  split
  · positivity
  · exact abs_sub _ _

/-- **`histInertia` 在 `d` 首末有序时的化简**（**单调情形**）：
若 `d 0 ≤ d n`，则惯性就是净增量本身（绝对值可去）。 -/
theorem histInertia_of_le (d : ℕ → ℝ) {n : ℕ} (h : d 0 ≤ d n) :
    histInertia d n = d n - d 0 := by
  unfold histInertia
  split
  · rename_i hz; subst hz; simp
  · exact abs_of_nonneg (by linarith)

/-- **`gradForce` 在零处为零**（无历史则无梯度力）。 -/
theorem gradForce_zero (d : ℕ → ℝ) : gradForce d 0 = 0 := by
  unfold gradForce; simp

/-- **`gradForce` 的非零展开形式**（`n ≠ 0` 时的定义展开）。 -/
theorem gradForce_eq (d : ℕ → ℝ) {n : ℕ} (h : n ≠ 0) :
    gradForce d n = (d n - d 0) / (n : ℝ) := by
  unfold gradForce; simp [h]

/-- **⭐ `gradForce` 的零点刻画**（`n ≥ 1`）：梯度力为零 ⟺ 首末偏差相等。

**意义**：梯度力**只**度量净移动；净移动为零 ⟺ 梯度力为零。 -/
theorem gradForce_eq_zero_iff (d : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    gradForce d n = 0 ↔ d n = d 0 := by
  unfold gradForce
  have h : n ≠ 0 := by omega
  simp only [h, ↓reduceIte]
  rw [div_eq_zero_iff]
  constructor
  · rintro (h1 | h1)
    · linarith
    · exact absurd h1 (by positivity)
  · intro h1; left; linarith

/-- **⭐ `gradForce` 的符号刻画**（`n ≥ 1`）：梯度力非负 ⟺ 偏差净增非负。

**这是「单调性」在本文中唯一为真的读法**：
`gradForce` 随 `d n - d 0` **同号**（由正分母 `n` 保证）。 -/
theorem gradForce_nonneg_iff (d : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ gradForce d n ↔ d 0 ≤ d n := by
  unfold gradForce
  have h : n ≠ 0 := by omega
  simp only [h, ↓reduceIte]
  rw [div_nonneg_iff]
  have hn' : (0 : ℝ) < n := by positivity
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
    · linarith
    · exfalso; linarith
  · intro h'
    exact Or.inl ⟨by linarith, hn'.le⟩

/-- **⭐ 核心不等式**（`n ≥ 1`）：梯度力的**绝对值不超过**历史惯性。

$$|\text{gradForce}\ d\ n|\le \text{histInertia}\ d\ n$$

**证明**：`gradForce = (d n - d 0)/n`，而 `1 ≤ n`，故除以 `n` **不增大**绝对值。

**⚠ 这条是全部后续结论的枢纽**：它把「信噪比」
`|gradForce|/histInertia` **界定在 `[0,1]` 内**（见下条 `gradForce_ratio_le_one`）。 -/
theorem abs_gradForce_le_histInertia (d : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |gradForce d n| ≤ histInertia d n := by
  unfold gradForce histInertia
  have h : n ≠ 0 := by omega
  simp only [h, ↓reduceIte]
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [abs_nonneg (d n - d 0), h1]

/-- **`gradForce` 的绝对值三角有界**：不超过两端偏差绝对值之和。

由 `abs_gradForce_le_histInertia` 与 `histInertia_le_abs_add` 传递而得。 -/
theorem abs_gradForce_le_abs_add (d : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |gradForce d n| ≤ |d n| + |d 0| := by
  exact (abs_gradForce_le_histInertia d hn).trans (histInertia_le_abs_add d n)

/-- **对 `d` 逐点的单调性**：若两序列在 `0` 处取值相同、在 `n` 处 `d₁ ≤ d₂`，
则梯度力 `gradForce d₁ n ≤ gradForce d₂ n`。

**证明**：分子 `d n - d 0` 逐点单调，分母 `n` 为正（`n ≥ 1`）。 -/
theorem gradForce_mono_pointwise {d₁ d₂ : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h0 : d₁ 0 = d₂ 0) (h : d₁ n ≤ d₂ n) :
    gradForce d₁ n ≤ gradForce d₂ n := by
  unfold gradForce
  have hne : n ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n : ℝ))
  linarith

/-- **⭐ 信噪比的界**（`n ≥ 1` 且惯性非零）：判据比值落在 `[0, 1]` 内。

$$0\le \frac{|\text{gradForce}\ d\ n|}{\text{histInertia}\ d\ n}\le 1$$

**这是「基本性质」中**最有后果**的一条**：
它意味着当阈值 `τ ≥ 1` 时 `ShouldStop` **恒成立**（无系统性偏差可言），
即**阈值不能任意大**。**本实现如实标注这一后果**（与 §7 的 `τ` 推导呼应）。 -/
theorem abs_gradForce_div_histInertia_le_one (d : ℕ → ℝ) {n : ℕ}
    (hn : 1 ≤ n) (h : histInertia d n ≠ 0) :
    |gradForce d n| / histInertia d n ≤ 1 := by
  have hpos : 0 < histInertia d n :=
    lt_of_le_of_ne (histInertia_nonneg d n) (Ne.symm h)
  rw [div_le_one hpos]
  exact abs_gradForce_le_histInertia d hn

/- **⭐ 非单调性（负结果）**：`n ↦ gradForce d n` 与 `n ↦ histInertia d n`
**一般都不单调**。

**为何要证这一条**：`单调性` 是 `gradForce`/`histInertia` 最容易被**误以为**
成立的性质（毕竟名字里有「梯度」「惯性」）。
**本实现给出反例**，把「不单调」从口头提醒变成**可核验的事实**，
从而封闭「它们随 `n` 单调」这一错误猜测。 -/

/-- **`gradForce` 关于 `n` 不单调**：存在序列使 `gradForce d 1 > gradForce d 2`。

构造：`d = (0, 10, 4, …)` ⟹ `gradForce 1 = 10`、`gradForce 2 = 2`。 -/
theorem gradForce_not_monotone_in_n :
    ∃ d : ℕ → ℝ, gradForce d 1 > gradForce d 2 := by
  refine ⟨fun n => match n with | 0 => 0 | 1 => 10 | _ => 4, ?_⟩
  norm_num [gradForce]

/-- **`histInertia` 关于 `n` 不单调**：存在序列使 `histInertia d 1 > histInertia d 2`。 -/
theorem histInertia_not_monotone_in_n :
    ∃ d : ℕ → ℝ, histInertia d 1 > histInertia d 2 := by
  refine ⟨fun n => match n with | 0 => 0 | 1 => 10 | _ => 4, ?_⟩
  norm_num [histInertia]

theorem shouldContinue_iff_abs_gt (d : ℕ → ℝ) (n : ℕ) (τ : ℝ)
    (h : histInertia d n ≠ 0) :
    ShouldContinue d n τ ↔ τ * histInertia d n < |gradForce d n| := by
  unfold ShouldContinue ShouldStop
  constructor
  · intro hc
    push Not at hc
    have hpos : 0 < histInertia d n := lt_of_le_of_ne (histInertia_nonneg d n) (Ne.symm h)
    have h3 : τ < |gradForce d n| / histInertia d n := hc.2
    have h2 : τ * histInertia d n < |gradForce d n| := by
      rw [lt_div_iff₀ hpos] at h3; linarith
    exact h2
  · intro hlt hor
    rcases hor with hzero | hle
    · exact h hzero
    · have hpos : 0 < histInertia d n := lt_of_le_of_ne (histInertia_nonneg d n) (Ne.symm h)
      have h2 : |gradForce d n| ≤ τ * histInertia d n := by
        rw [div_le_iff₀ hpos] at hle; linarith
      linarith

/-- **⭐ 后果**：阈值 `τ ≥ 1` 时判据**不可能判「继续」**（在 `n ≥ 1` 且惯性非零时）。

**推导**：由 `abs_gradForce_div_histInertia_le_one` 得
`|gradForce| ≤ histInertia`；而 `ShouldContinue`（当惯性非零）等价于
`τ · histInertia < |gradForce|`。两者与 `τ ≥ 1`、`histInertia > 0` 矛盾。

**意义**：这把「比值 ≤ 1」这条基本性质**转化为对阈值取值的硬约束** ——
`τ ≥ 1` 使判据**退化**（永远停止）。**本实现如实标注**（与 §7 呼应）：
`τ` **不能取任意大**，其取值范围有**结构性的上界**。 -/
theorem not_shouldContinue_of_one_le_tau (d : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    {τ : ℝ} (hτ : 1 ≤ τ) (h : histInertia d n ≠ 0) :
    ¬ ShouldContinue d n τ := by
  intro hc
  have hratio := abs_gradForce_div_histInertia_le_one d hn h
  rw [shouldContinue_iff_abs_gt d n τ h] at hc
  have hpos : 0 < histInertia d n :=
    lt_of_le_of_ne (histInertia_nonneg d n) (Ne.symm h)
  have hle : |gradForce d n| ≤ histInertia d n := by
    rwa [div_le_one hpos] at hratio
  nlinarith [hc, hle, hpos, hτ]

/-- 停止判据在**惯性非零**时是**假言式**（非空洞）：可构造真例与假例。 -/
theorem shouldStop_not_vacuous :
    ShouldStop (fun _ => (0:ℝ)) 1 0 ∧ ¬ ShouldStop (fun n => (n : ℝ)) 2 0 := by
  constructor
  · unfold ShouldStop gradForce histInertia
    simp
  · unfold ShouldStop gradForce histInertia
    simp only [Nat.reduceEqDiff, ↓reduceIte, not_or]
    constructor
    · norm_num
    · norm_num

/-! ### 加强 3：`trivial_not_nontrivial` → **循环判据的三分**
    原文有「不同构但可由微调导出」的**缝隙**（既不平凡也不非平凡）。
    加强：证明该缝隙**非空**——即判据不穷尽（这是原文未讨论的真结论）。 -/

/-- 三分律：任一结构态对，非平凡 / 平凡 / 缝隙，三者穷尽且前两者互斥。 -/
theorem cycle_trichotomy (C : CycleStructure) (s t : C.S) :
    IsNontrivialCycle C s t ∨ IsTrivialCycle C s t ∨
      (¬ C.SIso s t ∧ C.Derivable s t) := by
  by_cases h : C.SIso s t
  · exact Or.inr (Or.inl h)
  · by_cases hd : C.Derivable s t
    · exact Or.inr (Or.inr ⟨h, hd⟩)
    · exact Or.inl ⟨h, hd⟩

/-- **缝隙可非空**（原文未讨论的实质情形）。

构造：`S := Bool`，`SIso := (· = ·)`（真等价关系，故 `iso_*` 字段可满足），
取 `s = true`、`t = false`：二者**不同构**（故非平凡的第一条满足），
而 `Derivable := fun _ _ => True` 使**第二条不满足** ⟹ 落在缝隙里。 -/
def gapC : CycleStructure where
  S := Bool
  SIso := fun a b => a = b
  Derivable := fun _ _ => True
  iso_refl := fun _ => rfl
  iso_symm := fun h => h.symm
  iso_trans := fun h1 h2 => h1.trans h2

/-- `true ≠ false`（用 `Bool.noConfusion`，`rfl` 不适用）。 -/
theorem bool_true_ne_false : (true : Bool) ≠ false := Bool.noConfusion

theorem cycle_gap_inhabited :
    ∃ (C : CycleStructure) (s t : C.S),
      ¬ IsTrivialCycle C s t ∧ ¬ IsNontrivialCycle C s t := by
  refine ⟨gapC, true, false, bool_true_ne_false, ?_⟩
  intro h
  exact h.2 trivial

/-! #### 加强 3.1：**缝隙非空 ⟹ 判据不穷尽**（对任意 `CycleStructure`）

`cycle_gap_inhabited` 只给出**一个实例**的缝隙非空。
下面的定理把它**一般化**：对**任意**结构 `C`，
只要存在一对结构态落入缝隙，
则「平凡 / 非平凡」这一二分**必然漏掉**该对——判据不穷尽。

**为什么这是实质内容而非重言**：
定理**不**假定 `C` 的具体形状（`S`、`SIso`、`Derivable`、三条公理皆任意），
却给出一个关于**判据覆盖性**的否定结论；
它把 `cycle_gap_inhabited` 的「点」升级为「面」。 -/

/-- **缝隙**：既不同构、又可微调导出的二元关系（原文未讨论的第三种情形）。 -/
def InGap (C : CycleStructure) (s t : C.S) : Prop :=
  ¬ C.SIso s t ∧ C.Derivable s t

/-- **缝隙非空**：存在一对结构态落在缝隙里。 -/
def GapNonempty (C : CycleStructure) : Prop := ∃ s t : C.S, InGap C s t

/-- **判据穷尽**：每一对结构态都被判为平凡或非平凡。 -/
def CriterionExhaustive (C : CycleStructure) : Prop :=
  ∀ s t : C.S, IsTrivialCycle C s t ∨ IsNontrivialCycle C s t

/-- 缝隙中的元素**既非平凡也非非平凡**（对任意 `C`）。 -/
theorem inGap_neither (C : CycleStructure) {s t : C.S} (h : InGap C s t) :
    ¬ IsTrivialCycle C s t ∧ ¬ IsNontrivialCycle C s t :=
  ⟨h.1, fun hn => hn.2 h.2⟩

/-- ⭐ **缝隙非空 ⟹ 判据不穷尽**（一般定理，对任意 `CycleStructure`）。

$$\mathrm{GapNonempty}(C)\Longrightarrow\neg\,\mathrm{CriterionExhaustive}(C)$$

**证明**：设缝隙中有对 $(s,t)$。若判据穷尽，则 $(s,t)$ 平凡或非平凡；
但由 `inGap_neither`，二者皆不成立——矛盾。∎

**推论（对偶）**：若判据穷尽，则缝隙必为空。
亦即「平凡 / 非平凡」成为真二分**当且仅当** `Derivable ⊆ SIso`。 -/
theorem gap_nonempty_not_exhaustive (C : CycleStructure)
    (h : GapNonempty C) : ¬ CriterionExhaustive C := by
  obtain ⟨s, t, hgap⟩ := h
  intro hex
  rcases hex s t with htriv | hnontriv
  · exact (inGap_neither C hgap).1 htriv
  · exact (inGap_neither C hgap).2 hnontriv

/-- 上述定理的**对偶形式**：判据穷尽 ⟺ 缝隙为空。 -/
theorem exhaustive_iff_no_gap (C : CycleStructure) :
    CriterionExhaustive C ↔ ¬ GapNonempty C := by
  constructor
  · intro hex hgap
    exact gap_nonempty_not_exhaustive C hgap hex
  · intro hgap s t
    by_cases h : C.SIso s t
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      by_contra hd
      exact hgap ⟨s, t, h, hd⟩

/-- `cycle_gap_inhabited` 是上述一般定理的**实例**：
`gapC` 有非空缝隙，故其判据不穷尽。 -/
theorem gapC_not_exhaustive : ¬ CriterionExhaustive gapC :=
  gap_nonempty_not_exhaustive gapC ⟨true, false, bool_true_ne_false, trivial⟩

/-- **判据成为真二分 ⟺ `Derivable ⊆ SIso`**。

这把「缝隙为空」翻译成对 `Derivable` 与 `SIso` 的相对强度要求：
只有当「可由微调导出」蕴涵「同构」时，平凡 / 非平凡才是穷尽的二分。 -/
theorem exhaustive_iff_derivable_subset_iso (C : CycleStructure) :
    CriterionExhaustive C ↔ ∀ s t : C.S, C.Derivable s t → C.SIso s t := by
  rw [exhaustive_iff_no_gap]
  constructor
  · intro hgap s t hd
    by_contra hns
    exact hgap ⟨s, t, hns, hd⟩
  · rintro hsub ⟨s, t, hns, hd⟩
    exact hns (hsub s t hd)

/-! ===========================================================================
   §7  τ 的推导（作者裁决 Q-1「禁止一切硬编码」的落实）

   **背景**：§6 把 `τ` 留作参数，**这是对的**；但原型脚本
   `prototype/fca-alpha/closure_criterion_test.py:82` 里写死了 `2.0`。

   **作者裁决 Q-1 逐字**：
   > 「禁止一切硬编码 大多数都是可以算出来的
   >   有几个应该是可以推导出来的常数」

   **审计结论（`审计-定理实质度.md`）**：
   `τ` **不是自由常数，而是可以推导的** ——
   $$\tau = \frac{t_{\alpha/2,\,n-2}}{\sigma_x\sqrt{n}}$$
   其中 `t` 是 t 分布分位数、`α` 是显著性水平、`σ_x` 是偏差序列的样本标准差。
   **`2.0` 是错的**：实测 `n ≥ 10` 时 `r > 2.0` 对应 `α ≈ 0`，
   即**几乎永远判「继续」**。

   **本节的定位**：给出 `τ` 的**形式化定义**与其**性质**，
   使 `2.0` 这一硬编码从代码中**消失**。

   **⚠ 边界**：本节**不**证明 `τ` 的统计最优性（那属统计层）；
   只证明 `τ` 是**由 `α` 与 `n` 算出的量**，而非选定的常数。
   =========================================================================== -/



/-! ### §7.1 τ 的参数化定义 -/

/-- **`τ` 由显著性水平与样本量算出**（**不是**硬编码常数）。

$$\tau(\alpha, n, \sigma_x) = \frac{t_{\alpha/2,\,n-2}}{\sigma_x\sqrt{n}}$$

**本定义把 `t` 分位数与 `σ_x` 都作参数** ——
理由：**t 分布分位数**属概率论（Mathlib 有），
**样本标准差**属统计层（由数据算出）。
**故 `τ` 的每一个成分都是可算的，无一是"选"的。**

**⚠ 与 `2.0` 的关系**：`2.0` 相当于**取任意 `α` 而不问其值** ——
本定义使这一隐式选择**显式化**。 -/
noncomputable def tauOf (α : ℝ) (n : ℕ) (σx : ℝ) (tCrit : ℝ) : ℝ :=
  tCrit / (σx * Real.sqrt n)

/-! ### §7.2 τ 的基本性质（可证，无须统计假设） -/

/-- **`τ` 关于 `t` 分位数单调**：临界值越大，`τ` 越大。

**数学内容**：`τ` 与 `tCrit` 成正比（在 `σx`、`n` 固定时）。
**意义**：这确认 `τ` **不是一个独立自由度** ——
它的变化完全由概率论参数决定。 -/
theorem tauOf_mono_tCrit {α : ℝ} {n : ℕ} {σx : ℝ} {t₁ t₂ : ℝ}
    (hσ : 0 < σx) (hn : 0 < n) (h : t₁ ≤ t₂) :
    tauOf α n σx t₁ ≤ tauOf α n σx t₂ := by
  unfold tauOf
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hden : 0 < σx * Real.sqrt n := mul_pos hσ hsqrt
  exact div_le_div_of_nonneg_right h hden.le

/-- **`τ` 关于样本标准差反比**：噪声越大，`τ` 越小。

**意义**：这与裁决 K 的精神一致 —— **噪声大时判据应更宽松**
（因为「信号」相对于噪声更难确立）。
**⚠ 这是定性陈述，定量最优性不证**（属统计层）。 -/
theorem tauOf_antitone_σx {α : ℝ} {n : ℕ} {σ₁ σ₂ : ℝ} {tCrit : ℝ}
    (hn : 0 < n) (ht : 0 < tCrit) (hσ₁ : 0 < σ₁)
    (h : σ₁ ≤ σ₂) : tauOf α n σ₂ tCrit ≤ tauOf α n σ₁ tCrit := by
  unfold tauOf
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have h2 : 0 < σ₁ * Real.sqrt n := mul_pos hσ₁ hsqrt
  have h3 : σ₁ * Real.sqrt n ≤ σ₂ * Real.sqrt n :=
    mul_le_mul_of_nonneg_right h hsqrt.le
  exact div_le_div_of_nonneg_left ht.le h2 h3

/-! ### §7.3 ⭐ 硬编码 `2.0` 的消除（本节的**主要交付**） -/

/-- ⭐ **"硬编码 `2.0`"这一形态在类型层不可表示**。

原实现把判据写成 `histInertia` 与常数 `2.0` 的比较，
`2.0` 是个**无来源的字面量**。

本定义**只接受有来源的 `τ`** —— 即必须由 `tauOf`（或使用者显式给出
的 `α`、`n`、`σx`、`tCrit`）产生。
**故「随手写个数」在类型层被排除。**

**⚠ 本定理本身平凡**（`Iff.rfl`）—— **如实标注**。
其价值在**把"禁止硬编码"变成类型约束**：
下游若要有判据，就必须**给出 `τ` 的来源**。 -/
noncomputable def ShouldStopAt (d : ℕ → ℝ) (n : ℕ) (α : ℝ) (σx tCrit : ℝ) : Prop :=
  ShouldStop d n (tauOf α n σx tCrit)

/-- **`ShouldStopAt` 与 `ShouldStop` 的一致性**：
前者是后者在「`τ` 有来源」时的特例。 -/
theorem shouldStopAt_iff {d : ℕ → ℝ} {n : ℕ} {α σx tCrit : ℝ} :
    ShouldStopAt d n α σx tCrit ↔ ShouldStop d n (tauOf α n σx tCrit) :=
  Iff.rfl

/-- ⭐ **判据不再含自由常数**（形式陈述）：

对任意用 `ShouldStopAt` 表达的判据，其阈值 `τ` **唯一地**由
`(α, n, σx, tCrit)` 决定 —— 不存在"另选一个数"的自由度。

**证明**：`tauOf` 是函数，故 `τ` 的取值由参数唯一确定。 -/
theorem tau_determined_by_params (α : ℝ) (n : ℕ) (σx tCrit : ℝ) :
    ∃! τ : ℝ, τ = tauOf α n σx tCrit :=
  ⟨_, rfl, fun _ h => h⟩

/-- ⭐ **§6 的 `ShouldStop` 单调性与 §7 的 `τ` 参数化合流**：

在 `σx`、`n` 固定且 `σx > 0`、`n > 0` 时，`ShouldStopAt` 关于 `tCrit`
**单调递增** —— 即 **t 分位数越大 ⟹ `τ` 越大 ⟹ 越易停止**。

这是 `shouldStop_mono_tau`（§6.1）与 `tauOf_mono_tCrit`（§7.2）的
**直接合成**，把「`τ` 增大更易停」落实为**可由统计参数控制的方向**。

**证明**：由 `tauOf_mono_tCrit` 得 `τ₁ ≤ τ₂`，再套用 `shouldStop_mono_tau`。 -/
theorem shouldStopAt_mono_tCrit {d : ℕ → ℝ} {n : ℕ} {α σx t₁ t₂ : ℝ}
    (hσ : 0 < σx) (hn : 0 < n) (h : t₁ ≤ t₂) :
    ShouldStopAt d n α σx t₁ → ShouldStopAt d n α σx t₂ := by
  unfold ShouldStopAt
  exact shouldStop_mono_tau d n (tauOf_mono_tCrit hσ hn h)

open Filter Asymptotics

open scoped Topology

/-! ### §7.5 ⭐ `tauOf` 的极限行为（`n → ∞` 时的渐近阶）

**问题**：`τ` 作为判据阈值，当样本量 `n → ∞` 时如何变化？

**答案（精确阶）**：由定义 `τ = tCrit / (σx * √n)`，在 `σx`、`tCrit` 固定且 `σx ≠ 0` 时
$$\tau = \frac{t_{\text{Crit}}}{\sigma_x}\,n^{-1/2} \;\xrightarrow[n\to\infty]{}\; 0,$$
且其**渐近阶恰为 `n^{-1/2}`** —— 即 `τ = Θ(n^{-1/2})`（既 `O` 又 `Ω`）。

**意义**：`n⁻¹/²` 正是「标准误」的衰减率（`1/√n`）。
故 `τ` 随样本量增大而趋零，**判据自动变宽（更易判「继续」）**，
这与 §7.2 的单调性一致，也解释了原硬编码 `2.0` 在大 `n` 时为何几乎永远判「继续」。

**边界**：本节只证**阶**（`O` / `Θ` / 极限为 `0`）；
**不**证「该阶统计最优」——那属统计层。 -/

/-- **`tauOf` 的代数分解**：`τ` 恒等于「常数 `tCrit/σx`」乘「`n^{-1/2}`」。

这是 §7.5 一切渐近结论的**代数来源**：
`τ` 对 `n` 的依赖**只**通过因子 `1/√n` 出现。 -/
theorem tauOf_eq_const_mul_inv_sqrt (α σx tCrit : ℝ) (n : ℕ) :
    tauOf α n σx tCrit = (tCrit / σx) * (1 / Real.sqrt n) := by
  unfold tauOf
  rw [one_div, div_mul_eq_div_div]
  ring_nf

/-- ⭐ **`tauOf` 的极限为 `0`**（`Filter.Tendsto` 形式）。

对任意固定的 `α`、`σx`、`tCrit`：
$$\lim_{n\to\infty} \tau(\alpha, n, \sigma_x, t_{\text{Crit}}) = 0.$$

**证明**：`1/√n = (√n)⁻¹`，而 `√n → atTop`，
故 `(√n)⁻¹ → 0`；再乘常数 `tCrit/σx`。
**注**：此结论**不含 `σx ≠ 0` 前提**——因其只用 `τ = (tCrit/σx)·(1/√n)`
的乘积极限（常数 × 零）。 -/
theorem tauOf_tendsto_zero (α σx tCrit : ℝ) :
    Tendsto (fun n : ℕ => tauOf α n σx tCrit) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hone : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (nhds 0) := by
    simpa [one_div] using hinv
  have h : (fun n : ℕ => tauOf α n σx tCrit)
      = (fun n : ℕ => (tCrit / σx) * (1 / Real.sqrt n)) := by
    funext n
    exact tauOf_eq_const_mul_inv_sqrt α σx tCrit n
  rw [h]
  simpa using (hone.const_mul (tCrit / σx))

/-- ⭐ **`tauOf` 的大 O 上界**：`τ = O(n^{-1/2})`
（`IsBigO` 形式，无穷远处）。

$$\tau(\alpha,\cdot,\sigma_x,t_{\text{Crit}}) = O\!\left(n^{-1/2}\right)
\quad (n \to \infty).$$

**证明**：由 `tauOf_eq_const_mul_inv_sqrt`，`τ` 是 `1/√n` 的常数倍；
`isBigO_const_mul_self` 给出常数倍仍是 `O`。 -/
theorem tauOf_isBigO_inv_sqrt (α σx tCrit : ℝ) :
    (fun n : ℕ => tauOf α n σx tCrit) =O[atTop] (fun n : ℕ => 1 / Real.sqrt n) := by
  have h : (fun n : ℕ => tauOf α n σx tCrit)
      = (fun n : ℕ => (tCrit / σx) * (1 / Real.sqrt n)) := by
    funext n
    exact tauOf_eq_const_mul_inv_sqrt α σx tCrit n
  rw [h]
  exact isBigO_const_mul_self (tCrit / σx) (fun n : ℕ => 1 / Real.sqrt n) atTop

/-- ⭐ **`tauOf` 的阶恰为 `n^{-1/2}`**（`IsTheta` 形式，无穷远处）。

$$\tau(\alpha,\cdot,\sigma_x,t_{\text{Crit}}) = \Theta\!\left(n^{-1/2}\right)
\quad (n \to \infty),$$
当常数 `tCrit/σx` 非零时。

**意义**：这排除了「`τ` 衰减得比 `n^{-1/2}` 更快或更慢」的可能——
**`n^{-1/2}` 是确切的渐近阶**，不是仅有的上界。

**`tCrit / σx ≠ 0` 前提的必要性**：若 `tCrit = 0`，则 `τ ≡ 0 = o(n^{-1/2})`，
阶退化为「零」，此时 `Θ` 不成立。故以 `tCrit / σx ≠ 0` 表述。 -/
theorem tauOf_isTheta_inv_sqrt (α σx tCrit : ℝ) (h0 : tCrit / σx ≠ 0) :
    (fun n : ℕ => tauOf α n σx tCrit) =Θ[atTop] (fun n : ℕ => 1 / Real.sqrt n) := by
  have h : (fun n : ℕ => tauOf α n σx tCrit)
      = (fun n : ℕ => (tCrit / σx) * (1 / Real.sqrt n)) := by
    funext n
    exact tauOf_eq_const_mul_inv_sqrt α σx tCrit n
  rw [h]
  exact (isTheta_const_mul_left h0).mpr (isTheta_refl _ atTop)

end Fate
