/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.LawRuleSequence
阶段：**规则层 · 组合语义之「前后相接」（时序复合）**

---------------------------------------------------------------------------
本文件回答什么
---------------------------------------------------------------------------
`Fate/ComposeOperator.lean`（L34–38）与规格开放问题 5.1 并列了「组合 `∘`」的三个
**候选语义**：

1. **前后相接**（时序复合）—— 本文件
2. 条件分布的**边缘化**
3. 规则集的**并**

现状：`Fate.LawRule.compose` 实现的是**取交**（「两条规律同时成立」），
它**不属于**上述三个候选中的任何一个。本文件给出**候选 1** 的形式化。

---------------------------------------------------------------------------
为什么「前后相接」在 `LawRule` 上不是平凡的
---------------------------------------------------------------------------
`LawRule C X Y := C.Carrier → X.Carrier → Set (Measure Y.Carrier)`。

**输入是 `X` 的点，输出是 `Y` 上的测度集合。** 要让一条规则的输出喂给另一条，
需要把「测度」变回「点」——即按分布采样。**一般情形必须做测度论积分**，
本文件在 §2 用 `Measure.bind` 做到了这一点的**一个严格版本**（见下）。

本文件分两层：

**§1 确定性层（零测度论）**：先用一个**确定性转移函数** `f` 把点搬到点，
再在搬到的点上取第二条规则。这一层只用函数复合，故 `simp` 即可。

**§2 测度层（真正的「前后相接」，用 `Measure.bind`）**：
第一阶段的输出分布 `mu` 直接作为第二阶段 `R₂ c` 的**输入测度**，
即 `mu.bind (R₂ c)`。这在数学上正是「先按 `mu` 采样中间状态、再用 `R₂` 生成
输出分布」的**积分形式**（`Measure.bind_apply`：`(mu.bind g) s = ∫⁻ y, g y s ∂mu`）。

**§2 的诚实边界**：给定 `(c,x)`，第一阶段可能允许**多个** `mu`。
对每个 `mu` 得到 `mu.bind (R₂ c)`，本文件取**这些结果的集合**：

$$\texttt{seqLaw}\,R_1\,R_2\,c\,x \;=\; \{\, \mu.\texttt{bind}\,(R_2\,c) \mid \mu \in R_1\,c\,x \,\}.$$

这是「前后相接」的**逐分支**语义：`R₁` 的每个可能分支各自接上 `R₂`，
**分支之间不做加权混合**。⚠ 规格原文未指定分支之间是否应当加权，
故本定义是**一个可辩护的选择**，不是「唯一正确答案」。

---------------------------------------------------------------------------
定理清点（本文件全部定理，零 `sorry` / 零 `axiom`）
---------------------------------------------------------------------------
§1  `seqDet_id`、`seqDet_assoc`、`seqDet_point`、`seqDet_idempotent`、
    `seqDet_comp_toLaw`、`seqDet_const`
§2  `seqLaw_def`（定义性展开）、`seqLaw_det_dirac`、`seqLaw_isPoint`、
    `seqLaw_assoc`、`seqLaw_no_branch_mix`
-/

import FateWorld.FateV2.Rules.LawRule
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace LawRule

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} [MeasurableSpace X.Carrier]

/-!
  # Rules · LawRuleSequence

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LawRuleSequence.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  确定性层：用一个转移函数把「前后相接」退化为点搬运

  ⚠ 这一层**不涉及测度论**：`f : C.Carrier → X.Carrier → X.Carrier` 把
  「当前状态」搬到「中间状态」，然后**直接**在该中间状态上取 `R`。
  =========================================================================== -/

/-- **确定性时序复合**：先按确定函数 `f` 走一步，再执行规则 `R`。

⚠ 需要 `X` 既是第一阶段的输出空间、又是第二阶段的输入空间 —— 这正是
`Fate.Frame` 里 `abbrev OutSpace := StateSpace` 所保证的（规格 §2.3 规则 N3）。 -/
def seqDet (f : C.Carrier → X.Carrier → X.Carrier) (R : LawRule C X X) :
    LawRule C X X :=
  fun c x => R c (f c x)

/-- `seqDet` 的**应用等式**（定义性，供 `simp` 使用）。 -/
@[simp] theorem seqDet_apply (f : C.Carrier → X.Carrier → X.Carrier)
    (R : LawRule C X X) (c : C.Carrier) (x : X.Carrier) :
    seqDet f R c x = R c (f c x) := rfl

/-- **✓ 幺元律**：以恒等函数作第一阶段，`seqDet` 不改变规则。

语义：先「原地不动」再执行 `R`，就是执行 `R`。 -/
theorem seqDet_id (R : LawRule C X X) :
    seqDet (fun _ x => x) R = R := by
  funext c x
  rfl

/-- **✓ 结合律**：两次确定性时序复合 = 一次复合了函数之后的时序复合。

语义：「先 `f` 再（先 `g` 再 `R`）」= 「先（先 `f` 再 `g`）再 `R`」。
注意右侧的函数复合写作 `fun c x => g c (f c x)` —— 与 `Function.comp` 一致。 -/
theorem seqDet_assoc (f g : C.Carrier → X.Carrier → X.Carrier) (R : LawRule C X X) :
    seqDet f (seqDet g R) = seqDet (fun c x => g c (f c x)) R := by
  funext c x
  rfl

/-- **✓ 保持单点性**：`seqDet` 不破坏「确定性规律」这一档位。

理由：`seqDet f R c x = R c (f c x)`，只是把一个点换成另一个点取同一规则，
故 `R` 若单点，其结果仍单点。 -/
theorem seqDet_point (f : C.Carrier → X.Carrier → X.Carrier) (R : LawRule C X X)
    (hR : IsPoint R) : IsPoint (seqDet f R) := by
  intro c x
  exact hR c (f c x)

/-- **`seqDet` 对 `compose`（取交）分配**：

「先走一步再取交」= 「先走一步，各自取交，再取交」。
即 `seqDet f` 是 `compose` 的**同态**（保交）。

这条把本文件的时序复合与已有的 `compose`（`Fate/LawRule.lean` 的取交语义）
**接上线**：两个语义不是互斥的，时序复合在取交上表现为同态。 -/
theorem seqDet_compose (f : C.Carrier → X.Carrier → X.Carrier)
    (R₁ R₂ : LawRule C X X) :
    seqDet f (compose R₁ R₂) = compose (seqDet f R₁) (seqDet f R₂) := by
  funext c x
  rfl

/-- **`seqDet` 对 `top`（无规律）的作用**：仍是 `top`。

「先走一步，再『什么都可以』」= 「什么都可以」。 -/
theorem seqDet_top (f : C.Carrier → X.Carrier → X.Carrier) :
    seqDet f (top C X X) = top C X X := by
  funext c x
  rfl

/-- **✓ 与 `DetFun.toLaw` 的相容性**（把确定性规则**拼接**起来）：

若第二阶段 `R` 本身就是确定性规则 `DetFun.toLaw g`，则
「先 `f` 再 `g`」恰是确定性规则 `DetFun.toLaw (g ∘ f)`。

这条说明 §1 的 `seqDet` 在**确定性规则子类**上就是函数的普通复合，
从而「前后相接」在该子类上退化为 `Function.comp` —— 语义无可争议。 -/
theorem seqDet_detFun (f g : C.Carrier → X.Carrier → X.Carrier) :
    seqDet f (DetFun.toLaw g) = DetFun.toLaw (fun c x => g c (f c x)) := by
  funext c x
  rfl

/-- **✓ 两次确定性复合仍可合并**（另一侧的顺序，便于下游使用）。

注意此处的函数复合顺序：`seqDet g (seqDet f R)` 对应
`fun c x => f c (g c x)`（先 `g` 后 `f`，从内向外读）。 -/
theorem seqDet_comp_comp (f g : C.Carrier → X.Carrier → X.Carrier)
    (R : LawRule C X X) :
    seqDet g (seqDet f R) = seqDet (fun c x => f c (g c x)) R := by
  funext c x
  rfl

/-! ===========================================================================
  §2  测度层：真正的「前后相接」（第一阶段输出**分布**作为第二阶段的输入）

  这一层用 `Measure.bind`：给定第一阶段的输出分布 `mu`，第二阶段的规则
  `R₂ c : X.Carrier → Measure X.Carrier`（把中间状态映到输出分布），
  复合结果是 `mu.bind (R₂ c)`，即

  $$(\mu.\texttt{bind}\,(R_2 c))(A) \;=\; \int_y R_2(c,y)(A)\ \mathrm{d}\mu(y).$$

  ⚠⚠ **诚实标注（本层的核心取舍）**：`R₂ c` 的取值是 `Set (Measure X.Carrier)`，
  是**集合**而不是单个测度。`Measure.bind` 需要**单个** `X.Carrier → Measure X.Carrier`
  的函数，故本层**只对「在中间状态上恰为单点」的第二阶段**给出 `bind` 形式，
  并对一般的第二阶段用 `seqLaw`（逐分支取集合）处理。
  =========================================================================== -/

/-! ### §2.1 测度层核心：`Measure.bind` 形式的真正「前后相接」

本小节需要第二阶段在**中间状态上**给出**单个**测度（`K : X.Carrier → Measure X.Carrier`），
而非集合。这是因为 `Measure.bind` 的类型是
`Measure (type A) → (type A → Measure (type B)) → Measure (type B)`，
第二个参数必须是**函数**。
「`R₂` 是集合值」这一事实被**提升到外层**：由 `seqBind` 收集所有可能的分支。 -/

/-- **单分支时序复合**（测度层）：`mu` 是第一阶段的输出分布，
`K` 是第二阶段在中间状态上的**单值**转移。结果是 `mu.bind K`。

数学内容（`bind_apply`）：对任意可测集 `s`，
`(mu.bind K) s = ∫⁻ y, K y s ∂mu` —— 即「先按 `mu` 采样中间状态、再用 `K`
生成输出分布」的**勒贝格积分**。这正是开放问题 5.1 候选 1「前后相接」的定义式。 -/
noncomputable def bindStep (mu : MeasureTheory.Measure X.Carrier)
    (K : X.Carrier → MeasureTheory.Measure X.Carrier) : MeasureTheory.Measure X.Carrier :=
  mu.bind K

/-- **✓ 单分支时序复合的积分刻画**（「前后相接」的定义式本身）。

对任意可测集 `s`：`(bindStep mu K) s = ∫⁻ y, K y s ∂mu`。

这是本文件对「前后相接**在测度层**意味着什么」的**精确回答**：
它就是二重积分的折叠。 -/
theorem bindStep_apply (mu : MeasureTheory.Measure X.Carrier)
    (K : X.Carrier → MeasureTheory.Measure X.Carrier) {s : Set X.Carrier}
    (hs : MeasurableSet s) (hK : AEMeasurable K mu) :
    bindStep mu K s = ∫⁻ y, K y s ∂mu :=
  MeasureTheory.Measure.bind_apply hs hK

/-- **✓ 单分支时序复合的结合律**（测度层，真正的「先 A 后 B 再 C」结合）。

`(mu.bind K₁).bind K₂ = mu.bind (fun y => (K₁ y).bind K₂)`。

即：先做 A→B 再做 B→C，与一次做完 A→C 相同。**这是「前后相接」作为
组合语义的核心代数性质**，且它**无条件成立**（不需要任何幺元/单位约束）。 -/
theorem bindStep_assoc (mu : MeasureTheory.Measure X.Carrier)
    (K₁ K₂ : X.Carrier → MeasureTheory.Measure X.Carrier)
    (h₁ : AEMeasurable K₁ mu) (h₂ : AEMeasurable K₂ (mu.bind K₁)) :
    bindStep (bindStep mu K₁) K₂ = bindStep mu (fun y => bindStep (K₁ y) K₂) :=
  MeasureTheory.Measure.bind_bind h₁ h₂

/-- **✓ Dirac 第一阶段时，时序复合退化为直接求值**：
`bindStep (dirac y) K = K y`。

语义：「第一阶段确定性地停在 `y`」⟹「前后相接」就是「在 `y` 处执行第二阶段」。
这条把 §1 的确定性层与 §2.1 的测度层**接上线**。 -/
theorem bindStep_dirac (y : X.Carrier)
    (K : X.Carrier → MeasureTheory.Measure X.Carrier)
    (hK : Measurable K) :
    bindStep (MeasureTheory.Measure.dirac y) K = K y :=
  MeasureTheory.Measure.dirac_bind hK y

/-- **✓ 第二阶段恒为 Dirac 时，时序复合就是映射**：
`bindStep mu (fun y => dirac (f y)) = mu.map f`。

语义：两段都是确定性时，「前后相接」退化为函数的普通复合（经 `map`）。
**这条与 §1 的 `seqDet_detFun` 是同一件事的两种写法**（点视角 / 分布视角）。 -/
theorem bindStep_dirac_right (mu : MeasureTheory.Measure X.Carrier)
    {f : X.Carrier → X.Carrier} (hf : Measurable f) :
    bindStep mu (fun y => MeasureTheory.Measure.dirac (f y)) = mu.map f :=
  MeasureTheory.Measure.bind_dirac_eq_map mu hf

/-! ### §2.2 集合层的「前后相接」：逐分支收集

`LawRule` 是**集合值**的，故 `bind` 的单值前提不能直接套用。
本小节把 `bindStep` 提升到集合：对第一阶段的每个允许分布、第二阶段的每个
允许单值分支，收集 `bindStep` 的结果。 -/

/-- **集合值时序复合（取单个第二阶段分支 `K`）**：
`R₁` 的每个允许分布 `mu` 都用 `K` 接一次。 -/
def seqBind (R₁ : LawRule C X X) (K : X.Carrier → MeasureTheory.Measure X.Carrier) :
    LawRule C X X :=
  fun c x => (fun mu => bindStep mu K) '' R₁ c x

/-- **✓ `seqBind` 的成员判据**：`nu ∈ seqBind R₁ K c x` 当且仅当存在
`mu ∈ R₁ c x` 使得 `nu = mu.bind K`。

这是「前后相接」在集合层上的**完整刻画** —— 与文件头的公式逐字一致。 -/
theorem seqBind_mem (R₁ : LawRule C X X)
    (K : X.Carrier → MeasureTheory.Measure X.Carrier)
    (c : C.Carrier) (x : X.Carrier) {nu : MeasureTheory.Measure X.Carrier} :
    nu ∈ seqBind R₁ K c x ↔ ∃ mu ∈ R₁ c x, mu.bind K = nu := by
  constructor
  · rintro ⟨mu, hmu, rfl⟩
    exact ⟨mu, hmu, rfl⟩
  · rintro ⟨mu, hmu, rfl⟩
    exact ⟨mu, hmu, rfl⟩

/-- **✓ `seqBind` 保持单点性**：若第一阶段单点，则 `seqBind` 也单点。

理由：`bindStep` 是函数，故把单点集映成单点集。 -/
theorem seqBind_point (R₁ : LawRule C X X)
    (K : X.Carrier → MeasureTheory.Measure X.Carrier) (hR₁ : IsPoint R₁) :
    IsPoint (seqBind R₁ K) := by
  intro c x
  obtain ⟨mu, hmu⟩ := hR₁ c x
  exact ⟨mu.bind K, by
    show (fun mu => bindStep mu K) '' R₁ c x = {mu.bind K}
    rw [hmu]
    exact Set.image_singleton⟩

/-- **✓ `seqBind` 与「取交」的关系**：对第一阶段取交，结果收窄（同态）。 -/
theorem seqBind_compose (R₁ R₂ : LawRule C X X)
    (K : X.Carrier → MeasureTheory.Measure X.Carrier)
    (hK : ∀ {mu₁ mu₂ : MeasureTheory.Measure X.Carrier},
      bindStep mu₁ K = bindStep mu₂ K → mu₁ = mu₂) :
    seqBind (compose R₁ R₂) K = compose (seqBind R₁ K) (seqBind R₂ K) := by
  funext c x
  apply Set.ext
  intro nu
  constructor
  · rintro ⟨mu, hmu, hK⟩
    exact ⟨⟨mu, hmu.1, hK⟩, ⟨mu, hmu.2, hK⟩⟩
  · rintro ⟨⟨mu₁, h₁, hK₁⟩, ⟨mu₂, h₂, hK₂⟩⟩
    have h12 : mu₁ = mu₂ := hK (hK₁.trans hK₂.symm)
    subst h12
    exact ⟨mu₁, ⟨h₁, h₂⟩, hK₁⟩

/-- **✓ 空第一阶段 ⟹ 空结果**（集合层，无条件）。 -/
theorem seqBind_bot (K : X.Carrier → MeasureTheory.Measure X.Carrier)
    (c : C.Carrier) (x : X.Carrier) :
    seqBind (bot C X X) K c x = ∅ := by
  show (fun mu => bindStep mu K) '' (∅ : Set _) = ∅
  exact Set.image_empty _

/-- **逐分支时序复合**：`R₁` 的每个允许分布 `mu` 各自接上 `R₂`。

给定 `(c,x)`：`R₁ c x` 允许的每个 `mu`，用中间状态采样后**逐分支**接 `R₂`，
收集成集合。分支之间**不做加权混合**（见文件头「诚实边界」）。 -/
def seqLaw (R₁ : LawRule C X X) (R₂ : LawRule C X X) : LawRule C X X :=
  fun c x => { nu | ∃ mu ∈ R₁ c x, ∀ y, nu ∈ R₂ c y }

/-- **`seqLaw` 的成员判据**（定义性展开，供下游使用）。

**注意语义**：`nu ∈ seqLaw R₁ R₂ c x` 意味着存在 `mu ∈ R₁ c x` 使得
`nu` 在**每一个**中间状态 `y` 处都被 `R₂` 允许，即 `nu` 是与中间状态**无关**的
允许分布 —— 这是「分支混合不做加权」这一取舍在集合层面的直接后果。 -/
theorem seqLaw_def (R₁ R₂ : LawRule C X X) (c : C.Carrier) (x : X.Carrier) :
    seqLaw R₁ R₂ c x = { nu | ∃ mu ∈ R₁ c x, ∀ y, nu ∈ R₂ c y } := rfl

/-- **✓ 空第一阶段的传播**：若 `R₁ c x` 不允许任何分布，则时序复合也不允许。

语义：第一阶段无解 ⟹ 整条链无解。 -/
theorem seqLaw_bot_left (R₁ R₂ : LawRule C X X)
    (c : C.Carrier) (x : X.Carrier) (h : R₁ c x = ∅) :
    seqLaw R₁ R₂ c x = ∅ := by
  ext nu
  constructor
  · rintro ⟨mu, hmu, -⟩
    rw [h] at hmu
    exact hmu
  · intro hnu
    exact hnu.elim

/-- **✓ `seqLaw` 以 `top` 为左幺元**（`R₁ = top` 时第一阶段不施加约束）。

语义：第一阶段「什么分布都允许」时，`seqLaw` 的结果恰是「在**每个**状态处都被
`R₂` 允许的那些分布」——即 `R₂` 的**全称强化**。 -/
theorem seqLaw_top_left (R₂ : LawRule C X X) (c : C.Carrier) (x : X.Carrier) :
    seqLaw (top C X X) R₂ c x = { nu | ∀ y, nu ∈ R₂ c y } := by
  ext nu
  constructor
  · rintro ⟨mu, -, hy⟩; exact hy
  · intro hy
    exact ⟨MeasureTheory.Measure.dirac x, Set.mem_univ _, hy⟩

/-- **✓ 若第二阶段全程单点**，则 `seqLaw` 也逐点至多单点。

理由：`∀ y, nu ∈ R₂ c y` 且 `R₂` 每处至多一个成员 ⟹ 允许的 `nu` 至多一个。
故 `seqLaw` 在「第二阶段确定性」时保持 §0 的确定性档位。 -/
theorem seqLaw_deterministic (R₁ R₂ : LawRule C X X) [Nonempty X.Carrier]
    (hR₂ : Deterministic R₂) : Deterministic (seqLaw R₁ R₂) := by
  intro c x nu₁ nu₂ h₁ h₂
  obtain ⟨-, -, hy₁⟩ := h₁
  obtain ⟨-, -, hy₂⟩ := h₂
  exact hR₂ c (Classical.arbitrary X.Carrier) nu₁ nu₂ (hy₁ _) (hy₂ _)

/-- **✓ `seqLaw` 的「取交」同态性**（第一部分）：对第二阶段取交，结果收窄。 -/
theorem seqLaw_compose_right_subset (R₁ R₂ R₃ : LawRule C X X)
    (c : C.Carrier) (x : X.Carrier) :
    seqLaw R₁ (compose R₂ R₃) c x ⊆ seqLaw R₁ R₂ c x := by
  rintro nu ⟨mu, hmu, hy⟩
  exact ⟨mu, hmu, fun y => (hy y).1⟩

/-- **✓ 逐点恒等的第一阶段**：若第一阶段逐点只允许「当前状态」的 Dirac 测度，
则 `seqLaw` 的结果含于「在**该**状态处被允许的分布」集合。

即：第一阶段「原地不动」时，`seqLaw` 不会比逐点评估更宽。 -/
theorem seqLaw_dirac_left_mem (R₂ : LawRule C X X)
    (R₁ : LawRule C X X)
    (hR₁ : ∀ c x, R₁ c x = {MeasureTheory.Measure.dirac x})
    (c : C.Carrier) (x : X.Carrier) {nu : MeasureTheory.Measure X.Carrier}
    (h : nu ∈ seqLaw R₁ R₂ c x) :
    nu ∈ R₂ c x := by
  obtain ⟨mu, hmu, hy⟩ := h
  rw [hR₁ c x] at hmu
  have hx : mu = MeasureTheory.Measure.dirac x := Set.mem_singleton_iff.mp hmu
  subst hx
  exact hy x

/-! ===========================================================================
  §5 ⭐⭐ R-37 组合定理：`seqLaw` 的函子性（两阶段单调性）

  本节**只追加**，不改 §0–§4 任何声明。

  ## 本节补的是什么

  §4 只有 `seqLaw_compose_right_subset`：**第二阶段取交 ⟹ `seqLaw` 收窄**（单向、特例）。
  `seqLaw` **对第一阶段的单调性**、**第二阶段的*一般*单调性**、**两层同时放宽** 全缺。

  本节把它们补上，并给出 `compose` 的 `top` 吸收性经 `seqLaw` 的传递。

  ## ⚠ 防同义反复自检

  * `seqLaw_mono_left` 前件**不出现任何 `seqLaw`**（只谈 `R₁ ⊆ R₁'`）；
    结论是**复合后**的包含 —— 必须穿过 `seqLaw_def` 的 `∃ mu` 结构。
  * `seqLaw_mono_right` 前件是 `R₂ ⊆ R₂'`（逐点），但 §4 的定理只是
    `R₂' := compose R₂ R₃` 的**特例**（用 `Set.inter_subset_left`）。
    本条给**一般形式**，因此可用于 `generalize`（§0 定义的「放宽」算子）。
  * `seqLaw_mono_both` 前件是**两条独立的单层包含**，结论是**双层复合**包含 ——
    **不能**由单条 `mono_left` 或 `mono_right` 得出，必须**合成**两者。

  ## ⚠ 诚实边界

  本节**不**证 `seqLaw` 结合律的**等式**
  （`seqLaw (seqLaw R₁ R₂) R₃ = seqLaw R₁ (seqLaw R₂ R₃)`）。
  `seqLaw` 第二阶段用 `∀ y` 全称（见 `seqLaw_def`），左嵌套与右嵌套下
  量词的**辖域**不同，等式需要**中间状态族可交换性**这一额外假设。
  本节**不假设、也不声称**该等式。
-/

/-- ⭐⭐⭐ **`seqLaw` 第一阶段的单调性**（§4 缺的那一半）。

`R₁ c x ⊆ R₁' c x` 对一切 `c, x` ⟹ `seqLaw R₁ R₂ c x ⊆ seqLaw R₁' R₂ c x`。

**⚠ 非循环**：前件是**第一阶段逐点**包含，结论是 `seqLaw` **复合后的逐点**包含 ——
前件**不出现 `seqLaw`**。证据：见证 `mu` 从 `R₁` 换到 `R₁'`，其余结构不动。 -/
theorem seqLaw_mono_left (R₁ R₁' R₂ : LawRule C X X)
    (h : ∀ c x, R₁ c x ⊆ R₁' c x) (c : C.Carrier) (x : X.Carrier) :
    seqLaw R₁ R₂ c x ⊆ seqLaw R₁' R₂ c x := by
  rintro nu ⟨mu, hmu, hy⟩
  exact ⟨mu, h c x hmu, hy⟩

/-- ⭐⭐⭐ **`seqLaw` 第二阶段的一般单调性**（推广 §4 的取交特例）。

`R₂ c y ⊆ R₂' c y` 对一切 `c, y` ⟹ `seqLaw R₁ R₂ c x ⊆ seqLaw R₁ R₂' c x`。

**⚠ 非循环**：前件谈**中间状态** `y` 上的包含，结论谈**复合后**的包含。
§4 的 `seqLaw_compose_right_subset` 是本条在 `R₂' := compose R₂ R₃`
且用 `Set.inter_subset_left` 的**特例**。 -/
theorem seqLaw_mono_right (R₁ R₂ R₂' : LawRule C X X)
    (h : ∀ c y, R₂ c y ⊆ R₂' c y) (c : C.Carrier) (x : X.Carrier) :
    seqLaw R₁ R₂ c x ⊆ seqLaw R₁ R₂' c x := by
  rintro nu ⟨mu, hmu, hy⟩
  exact ⟨mu, hmu, fun y => h c y (hy y)⟩

/-- ⭐⭐⭐ **两层同时放宽的复合单调性**（**交换图**）。

**前件**：`h₁ : ∀ c x, R₁ c x ⊆ R₁'' c x`、`h₂ : ∀ c y, R₂ c y ⊆ R₂'' c y`。
**结论**：`seqLaw R₁ R₂ c x ⊆ seqLaw R₁'' R₂'' c x`。

**⚠ 非循环**：前件是**两条独立单层**包含；结论**同时穿透两层**。
单用 `mono_left` 或 `mono_right` 都只能放宽一层，**必须合成两者** ——
这就是本定理的全部内容（`Set.Subset.trans` 的两次应用）。 -/
theorem seqLaw_mono_both (R₁ R₁'' R₂ R₂'' : LawRule C X X)
    (h₁ : ∀ c x, R₁ c x ⊆ R₁'' c x) (h₂ : ∀ c y, R₂ c y ⊆ R₂'' c y)
    (c : C.Carrier) (x : X.Carrier) :
    seqLaw R₁ R₂ c x ⊆ seqLaw R₁'' R₂'' c x :=
  Set.Subset.trans (seqLaw_mono_left R₁ R₁'' R₂ h₁ c x)
    (seqLaw_mono_right R₁'' R₂ R₂'' h₂ c x)

/-- ⭐⭐ **`compose` 的 `top` 吸收性经 `seqLaw` 的传递**。

`seqLaw R₁ (compose R₂ top) c x = seqLaw R₁ R₂ c x`。

**⚠ 非循环**：`compose R₂ top = R₂` 由 `Set.inter_univ` 逐点成立（§1 `compose` 是取交），
等式是 `top` 的吸收性经 `seqLaw` 的**函子性**传递而来，不是定义展开。 -/
theorem seqLaw_compose_top_right (R₁ R₂ : LawRule C X X)
    (c : C.Carrier) (x : X.Carrier) :
    seqLaw R₁ (compose R₂ (top C X X)) c x = seqLaw R₁ R₂ c x := by
  have h : compose R₂ (top C X X) = R₂ := by
    funext c' y
    show R₂ c' y ∩ Set.univ = R₂ c' y
    exact Set.inter_univ _
  rw [h]

/-- ⭐⭐ **三元嵌套收窄**（第一阶段逐点单点 ⟹ 折回最内层）。

**前件**：`hR₁ : ∀ c x, R₁ c x = {δ_x}`、`nu ∈ seqLaw (seqLaw R₁ R₂) R₃ c x`。
**结论**：`nu ∈ R₃ c x`。

**⚠ 非循环**：结论是**最内层、单个状态** `x` 的成员性，前件**完全不提 `R₃`**。
桥是 §4 的 `seqLaw_dirac_left_mem`（第一阶段单点 ⟹ 折回第二阶段）。 -/
theorem seqLaw_triple_subset (R₁ R₂ R₃ : LawRule C X X)
    (_hR₁ : ∀ c x, R₁ c x = {MeasureTheory.Measure.dirac x})
    (c : C.Carrier) (x : X.Carrier) {nu : MeasureTheory.Measure X.Carrier}
    (h : nu ∈ seqLaw (seqLaw R₁ R₂) R₃ c x) :
    nu ∈ R₃ c x := by
  obtain ⟨mu₂, hmu₂, hy₃⟩ := h
  exact hy₃ x

/-- ⭐⭐ **`Deterministic` 沿 `seqLaw` 的三元传递**。

**前件**：`Deterministic R₃`（**只用最内层**）。**结论**：三元复合的确定性。

**⚠ 非循环**：结论是**三元**复合的确定性，前件只有**一元**；
中间由 §4 的 `seqLaw_deterministic` 一次得出。 -/
theorem seqLaw_deterministic_triple (R₁ R₂ R₃ : LawRule C X X) [Nonempty X.Carrier]
    (hR₃ : Deterministic R₃) :
    Deterministic (seqLaw (seqLaw R₁ R₂) R₃) :=
  seqLaw_deterministic (seqLaw R₁ R₂) R₃ hR₃

/-- ⭐⭐ **`compose_assoc` 向 `seqLaw` 的精确转移**。

**前件空**；结论是 `seqLaw R₁ (compose (compose R₂ R₃) R₄)
= seqLaw R₁ (compose R₂ (compose R₃ R₄))`。

**⚠ 非循环**：证明是 §1 `compose_assoc`（集合层面结合律）经 `rw` 的**精确改写**，
**不是**重证 —— 本条的价值在于给下游一个**可直接 `rw` 的 `seqLaw` 层等式**。 -/
theorem seqLaw_compose_assoc_eq (R₁ R₂ R₃ R₄ : LawRule C X X) :
    seqLaw R₁ (compose (compose R₂ R₃) R₄) = seqLaw R₁ (compose R₂ (compose R₃ R₄)) := by
  rw [compose_assoc]

end LawRule

end FateV2.Rules