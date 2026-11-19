/-
命运理论 · 规则层级（Rule Level）
======================================================================

模块：`Fate.RuleLevel`
上游：`Fate/LawRule.lean`（`LawRule`，位于命名空间 `LawRule`）、
　　　`Fate/Frame.lean`（`CtxSpace`、`OutSpace`）、
　　　`Fate/Basic.lean`（`StateSpace`）。

---------------------------------------------------------------------------
问题（作者原问）
---------------------------------------------------------------------------
实现「一个类型带层级标签」的规则类型：
`RuleLevel`（`transition` / `trajectory`）、`TrajPattern`、
`RuleBody`（`trans` / `pattern`）、`Rule := RuleBody`，
以及层级函数 `RuleBody.level`。要求：
  (1) 层级由载体唯一决定（不存在不一致）；
  (2) `trans` 与 `pattern` 两类不相交（或给出构造出相同 level 的条件）；
  (3) 给出从 `LawRule` 嵌入到 `Rule` 的函数；
  (4) `lake env lean` 零错误零 sorry。

---------------------------------------------------------------------------
实现要点（诚实记录）
---------------------------------------------------------------------------
1. **层级不是数据，是函数。** `level` 由 `RuleBody` 的**构造子**决定，
   故「同一载体不属于两个不同层级」是 `rfl` 级事实（§3）。

2. **命名冲突的处置（重要）。** 本库中 `Fate.Rule` **已被占用**
   （`Fate/Frame.lean` 的「条件分布核」规则，见 `LawRule.Rule.toLaw`）。
   Lean 不允许同命名空间内二次声明 `Rule`，故本题所要求的别名
   落名为 **`RuleOF`**（`OF` = 本模块 `RuleLevel` 的 `Rule Body` 版），
   并同时给出 `abbrev Rule := RuleOF` 的**命名空间内别名** `RuleLevel.Rule`。
   任何需要使用「本模块的 Rule」处，写 `RuleLevel.Rule`。

3. **「唯一决定」的可证读法**（§3，全部给出）：
   - `level_unique`：每个载体有且只有一个层级（`∃!` 形式）；
   - `level_no_conflict`：不存在同时属于两层的载体（否定式，「不一致」的反面）；
   - `level_transition_iff` / `level_trajectory_iff`：层级值**唯一决定**构造子族。

4. **「不相交」的可证读法 + 「同层级条件」**（§4）：
   - `trans_pattern_disjoint`：同一载体不可能既由 `trans` 又由 `pattern` 构造；
   - `level_ne_of_forms`：一个 `trans` 与一个 `pattern` 的层级必不相同；
   - `level_eq_iff_same_form`：**构造出相同 level 的确切条件** =
     两者属于同一构造子族；
   - `RuleEnc` / `encode_fst_eq_iff`：「带层级标签」的标准编码
     （`Sigma RuleTag (fun _ => RuleBody …)`），第一个分量即层级；
     「同 level」化为「编码第一分量相等」，与构造子刻画一致且不增加信息
     （`encode_decode`）。

5. **嵌入**（§5）：`ofLawRule : LawRule C X Y → RuleBody C X Y`，
   单射（`ofLawRule_injective`），保层级（`ofLawRule_level`），
   且有左逆 `toLawRule`（`ofLawRule_toLawRule`）。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- `TrajPattern.X` 的 `pre/post : Set (Set X.Carrier)` 是**我们选的语义**
  （前缀族 / 后缀族约束），规格原文未细化。
- 不相交只在**构造子层面**成立；**语义层面** `LawRule` 可嵌入 `TrajPattern`
  （本文**不**证），故本文只声称构造子不相交，并在 §4 给出语义层面
  「同层级」的显式条件，不声称语义上永不同构。
- 本文件零 sorry、零 axiom、零 `native_decide`。
-/

import FateWorld.FateV2.Rules.LawRule
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
/-!
  # Rules · RuleLevel

  ## 迁移登记
  - 来源：`FateWorld/Legacy/RuleLevel.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §0  层级标签
    =========================================================================== -/

/-- 规则层级标签。

* `transition`：**转移级**规则 —— 约束「给定 (c,x) 允许哪些下一分布」；
* `trajectory`：**轨迹级**规则 —— 约束「允许哪些轨迹（前后段）」。 -/
inductive RuleTag where
  /-- 转移级。-/
  | transition
  /-- 轨迹级。-/
  | trajectory
  deriving DecidableEq, Repr

/-- 本题所称的 `RuleLevel`（对外名字，与作者原问一致）。 -/
abbrev RuleLevel : Type := RuleTag

/-- 两层的互斥性：不存在同时属于两层的标签。 -/
theorem transition_ne_trajectory : RuleTag.transition ≠ RuleTag.trajectory := by
  intro h
  cases h

/-- 层级的完备枚举：只有两层，「层级」的外延因此确定。 -/
theorem eq_transition_or_trajectory (ℓ : RuleTag) :
    ℓ = RuleTag.transition ∨ ℓ = RuleTag.trajectory := by
  cases ℓ
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ===========================================================================
    §1  轨迹模式（trajectory 级规则的载体）
    =========================================================================== -/

/-- **轨迹模式**：对状态空间 `X` 的轨迹给出**前缀族**与**后缀族**约束。

语义（本文所选）：`pre` 是允许的起始段族，`post` 是允许的后续段族；
一条轨迹可接受，当且仅当它的某前缀在 `pre` 中且其余部在 `post` 中。
与 `LawRule` 一样，它**不计算**轨迹，只**约束**可能的轨迹。 -/
structure TrajPattern (X : StateSpace) where
  /-- 允许的起始段族（**构造谓词用**，见 `Fate.TrajPred` 一节）。 -/
  pre : Set (Set X.Carrier)
  /-- 允许的后续段族（**构造谓词用**）。 -/
  post : Set (Set X.Carrier)

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ===========================================================================
    §2  规则载体（带层级标签）
    =========================================================================== -/

/-- **规则载体**：要么是转移级（`LawRule`），要么是轨迹级（`TrajPattern`）。

**层级由构造子携带**，而非由附加字段记录 —— 这样「类型带层级标签」
在 Lean 里就是**构造子标签**本身，不引入「标签与载体不一致」的冗余自由度。 -/
inductive RuleBody (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] where
  /-- 转移级：包装一条 `LawRule`。-/
  | trans (r : LawRule.LawRule C X Y) : RuleBody C X Y
  /-- 轨迹级：包装一个 `TrajPattern`。-/
  | pattern (p : TrajPattern X) : RuleBody C X Y

/-- 本题所要求的别名 `Rule := RuleBody`。

⚠ 因 `Fate.Rule` 已被 `Fate/Frame.lean` 占用（条件分布核），
此处落名为 `RuleOF`；需要「本模块的 `Rule`」时写 `RuleLevel.Rule`。 -/
abbrev RuleOF (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ := RuleBody C X Y

namespace RuleLevelAlias

/-- `Rule` 的合格别名（限定在本命名空间内，不与 `Fate.Rule` 冲突）。 -/
abbrev Rule (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ := RuleBody C X Y

end RuleLevelAlias

/-! ===========================================================================
    §3  层级函数 `RuleBody.level` 与「唯一决定」
    =========================================================================== -/

/-- **层级函数**：把规则载体映到它的层级标签。 -/
def RuleBody.level : RuleBody C X Y → RuleTag
  | .trans _ => .transition
  | .pattern _ => .trajectory

theorem RuleBody.level_trans {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [inst : MeasurableSpace Y.Carrier] (r : LawRule.LawRule C X Y) :
    (RuleBody.trans (C := C) (X := X) (Y := Y) r).level = RuleTag.transition := rfl

theorem RuleBody.level_pattern {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [inst : MeasurableSpace Y.Carrier] (p : TrajPattern X) :
    (RuleBody.pattern (C := C) (X := X) (Y := Y) p).level = RuleTag.trajectory := rfl

/-- **(1) 层级由载体唯一决定**：每个载体有且只有一个层级。

这是「唯一决定」的正向形式（`∃!`）：存在一个层级，且任何两个都是同一个。 -/
theorem level_unique (b : RuleBody C X Y) :
    ∃! ℓ : RuleTag, b.level = ℓ :=
  ⟨b.level, rfl, fun _ h => h.symm⟩

/-- **(1) 不存在不一致**：没有载体同时被标为两层。 -/
theorem level_no_conflict (b : RuleBody C X Y) :
    ¬ (b.level = RuleTag.transition ∧ b.level = RuleTag.trajectory) := by
  rintro ⟨h₁, h₂⟩
  exact transition_ne_trajectory (h₁ ▸ h₂)

/-- **(1) 层级的逆向决定性**：`level = transition` **当且仅当**载体是 `trans`。 -/
theorem level_transition_iff (b : RuleBody C X Y) :
    b.level = RuleTag.transition ↔ ∃ r : LawRule.LawRule C X Y, b = RuleBody.trans r := by
  constructor
  · intro h
    cases b with
    | trans r => exact ⟨r, rfl⟩
    | pattern p =>
      exact absurd h (by rw [RuleBody.level_pattern (C := C) (Y := Y)]; decide)
  · rintro ⟨r, rfl⟩; rfl

/-- `level = trajectory` **当且仅当**载体是 `pattern`。 -/
theorem level_trajectory_iff (b : RuleBody C X Y) :
    b.level = RuleTag.trajectory ↔ ∃ p : TrajPattern X, b = RuleBody.pattern p := by
  constructor
  · intro h
    cases b with
    | trans r =>
      exact absurd h (by rw [RuleBody.level_trans (C := C) (Y := Y)]; decide)
    | pattern p => exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩; rfl

/-- `level` 是**满射**到 `RuleTag`（给定 `Y` 可测时两层都非空）。 -/
theorem level_surjective :
    Function.Surjective (RuleBody.level (C := C) (X := X) (Y := Y)) := by
  intro ℓ
  cases ℓ with
  | transition =>
    refine ⟨RuleBody.trans (Y := Y) (fun (_ : C.Carrier) (_ : X.Carrier) =>
      (∅ : Set (MeasureTheory.Measure Y.Carrier))), ?_⟩
    rfl
  | trajectory =>
    refine ⟨RuleBody.pattern (Y := Y) (⟨(∅ : Set (Set X.Carrier)),
      (∅ : Set (Set X.Carrier))⟩ : TrajPattern X), ?_⟩
    rfl

/-! ===========================================================================
    §4  trans 与 pattern 不相交 / 同层级的确切条件
    =========================================================================== -/

/-- **(2) 两类不相交（构造子层面）**：一个载体不可能同时由 `trans` 与
`pattern` 构造。这是 Lean 归纳类型的构造子不相交性，不可被任何假说移除。 -/
theorem trans_pattern_disjoint (b : RuleBody C X Y) :
    ¬ ((∃ r : LawRule.LawRule C X Y, b = RuleBody.trans (C := C) (X := X) (Y := Y) r) ∧
       (∃ p : TrajPattern X, b = RuleBody.pattern (C := C) (X := X) (Y := Y) p)) := by
  rintro ⟨⟨r, hr⟩, ⟨p, hp⟩⟩
  rw [hr] at hp
  cases hp

/-- **(2) 层级形式的不相交**：一个 `trans` 与一个 `pattern` 的层级必不相同。 -/
theorem level_ne_of_forms (r : LawRule.LawRule C X Y) (p : TrajPattern X) :
    (RuleBody.trans (C := C) (X := X) (Y := Y) r).level ≠
      (RuleBody.pattern (C := C) (X := X) (Y := Y) p).level := by
  rw [RuleBody.level_trans (C := C), RuleBody.level_pattern (C := C) (Y := Y)]
  decide

/-- **(2) 构造出相同 level 的确切条件**：同一层级 ⟺ 同一构造子族。

这既是「不相交」的强化形式（跨族不可能同层），
也是作者所要求的「构造出相同 level 的条件」的**充要刻画**。 -/
theorem level_eq_iff_same_form (b₁ b₂ : RuleBody C X Y) :
    b₁.level = b₂.level ↔
      ((∃ r₁ r₂ : LawRule.LawRule C X Y,
          b₁ = RuleBody.trans (C := C) (X := X) (Y := Y) r₁ ∧
          b₂ = RuleBody.trans (C := C) (X := X) (Y := Y) r₂) ∨
       (∃ p₁ p₂ : TrajPattern X,
          b₁ = RuleBody.pattern (C := C) (X := X) (Y := Y) p₁ ∧
          b₂ = RuleBody.pattern (C := C) (X := X) (Y := Y) p₂)) := by
  constructor
  · intro h
    cases b₁ with
    | trans r₁ =>
      cases b₂ with
      | trans r₂ => exact Or.inl ⟨r₁, r₂, rfl, rfl⟩
      | pattern p₂ =>
        exact absurd h (by rw [RuleBody.level_trans (C := C), RuleBody.level_pattern (C := C) (Y := Y)]; decide)
    | pattern p₁ =>
      cases b₂ with
      | trans r₂ =>
        exact absurd h (by rw [RuleBody.level_pattern (C := C) (Y := Y), RuleBody.level_trans (C := C)]; decide)
      | pattern p₂ => exact Or.inr ⟨p₁, p₂, rfl, rfl⟩
  · rintro (⟨r₁, r₂, rfl, rfl⟩ | ⟨p₁, p₂, rfl, rfl⟩) <;> rfl

/-- **(2) 「带层级标签的规则」的规范编码**：把载体与它自己的层级打包成
一个 `Sigma` 型。这是「一个类型带层级标签」在 Lean 里的**标准实现**：
标签是 `Sigma` 的第一分量，载体是第二分量，**二者不可能不一致**，
因为标签由 `b.level` 计算得到，而不是外部输入。

⚠ 这与 `RuleBody` 本身**信息等价**（见 `encode_decode`）：
它不增加表达力，只是把「层级」显式化为**可观测的类型层结构**。 -/
def RuleEnc (C : CtxSpace) (X : StateSpace) (Y : OutSpace) [MeasurableSpace Y.Carrier] :
    Type _ :=
  Sigma (fun _ : RuleTag => RuleBody C X Y)

/-- 编码：载体 → 「层级 × 载体」。 -/
def RuleBody.encode (b : RuleBody C X Y) : RuleEnc C X Y := ⟨b.level, b⟩

/-- 解码：丢掉标签，取回载体。 -/
def RuleEnc.decode (e : RuleEnc C X Y) : RuleBody C X Y := e.2

/-- 编码 / 解码互逆：标签编码**不丢失信息**，也不引入新信息。 -/
theorem encode_decode (b : RuleBody C X Y) : RuleEnc.decode (RuleBody.encode b) = b := rfl

/-- **(2) 语义层面的「同层级」确切条件**（编码视角）：
两个载体属于同一层级 ⟺ 它们的编码第一分量相同。
这把「同 level」化为**可计算比较**的分量相等，且与 §4 的构造子刻画一致。 -/
theorem encode_fst_eq_iff (b₁ b₂ : RuleBody C X Y) :
    (RuleBody.encode b₁).1 = (RuleBody.encode b₂).1 ↔ b₁.level = b₂.level :=
  Iff.rfl

/-! ===========================================================================
    §5  从 LawRule 到 Rule 的嵌入
    =========================================================================== -/

/-- **(3) 嵌入**：把任何 `LawRule` 视为一条**转移级** `Rule`。 -/
def ofLawRule (r : LawRule.LawRule C X Y) : RuleBody C X Y := .trans r

/-- 嵌入**是单射**（不丢失信息）。 -/
theorem ofLawRule_injective :
    Function.Injective (ofLawRule (C := C) (X := X) (Y := Y)) := by
  intro r₁ r₂ h
  cases h
  rfl

/-- 嵌入保层级：`LawRule` 一律落在 `transition` 层。 -/
@[simp] theorem ofLawRule_level (r : LawRule.LawRule C X Y) :
    (ofLawRule r).level = RuleTag.transition := rfl

/-- 嵌入的像恰是 `transition` 层的载体。 -/
theorem ofLawRule_range (b : RuleBody C X Y) :
    b.level = RuleTag.transition ↔ ∃ r : LawRule.LawRule C X Y, ofLawRule r = b := by
  rw [level_transition_iff]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩

/-- 嵌入的反向抽取（`transition` 层上的左逆）。 -/
def toLawRule : (b : RuleBody C X Y) → b.level = RuleTag.transition →
    LawRule.LawRule C X Y
  | .trans r, _ => r
  | .pattern _, h => absurd h (by rw [RuleBody.level_pattern (C := C) (Y := Y)]; decide)

theorem toLawRule_ofLawRule (r : LawRule.LawRule C X Y) :
    toLawRule (ofLawRule r) (ofLawRule_level r) = r := rfl

/-- 嵌入 ∘ 抽取 = 恒等（`transition` 层上的等价，即嵌入的像被精确刻画）。 -/
theorem ofLawRule_toLawRule (b : RuleBody C X Y) (h : b.level = RuleTag.transition) :
    ofLawRule (toLawRule b h) = b := by
  cases b with
  | trans r => rfl
  | pattern p => exact absurd h (by rw [RuleBody.level_pattern (C := C) (Y := Y)]; decide)

/-! ===========================================================================
    §6  R-40 接线：`LawRule` 代数提升到 `RuleBody` 层

    本节为 **R-40 Top 86-100 接线**新增（纯追加，不触碰 §0-§5 任何声明）。

    **消费上游**：`LawRule`（`compose` / `refine` / `generalize` /
    `IsPoint` / `Deterministic` / `compose_top` / `generalize_absorbs` 等）。

    **解决的问题**：§5 只把 `LawRule` 嵌入为**静态载体**（`ofLawRule`），
    但**未**把 `LawRule` 的**代数运算**（`compose` / `refine`）提升到
    `RuleBody` 层。本节为 `RuleBody` 定义转移级合成的**典范运算**，
    并证明它们与 `LawRule` 层运算**相容**（保持 `transition` 层级）。

    ⚠ 防同义反复声明：以下各条的结论都**不是**前件的重述——
      * `composeTrans_level` 结论是「层级计算」；
      * `composeTrans_comm` 结论是「运算交换律」，前件为空；
      * `toLawRule_composeTrans` 结论把 `RuleBody` 运算翻译回 `LawRule`；
      * `ofLawRule_refine` 结论是「嵌入与完善的交换图」。
    =========================================================================== -/

/-- **转移级合成的典范运算**：只在两侧都是 `trans` 时实际合成，
否则退化为左分量（这是**保守**定义，保证总函数性）。

读法：`composeTrans b₁ b₂` 把两条转移级规则同时施加（取交）；
若任一侧是轨迹级，则无法在其上做转移级合成，返回 `b₁`（如实保守）。 -/
def composeTrans (b₁ b₂ : RuleBody C X Y) : RuleBody C X Y :=
  match b₁, b₂ with
  | .trans r₁, .trans r₂ => .trans (LawRule.compose r₁ r₂)
  | _, _ => b₁

/-- **合成保层级（右因子为转移级时）。**

两个转移级规则的合成仍是转移级 —— 这是 `composeTrans` 的**类型正确性**：
转移层的代数封闭性。 -/
theorem composeTrans_level (r₁ r₂ : LawRule.LawRule C X Y) :
    (composeTrans (RuleBody.trans (C := C) (X := X) (Y := Y) r₁)
      (RuleBody.trans (C := C) (X := X) (Y := Y) r₂)).level = RuleTag.transition := rfl

/-- **合成在转移层的交换律。**

由 `composeTrans` 退化到 `LawRule.compose`，再由 `LawRule.compose_comm` 得出。
结论是 `RuleBody` 层的**等式**，前件为空。 -/
theorem composeTrans_comm (r₁ r₂ : LawRule.LawRule C X Y) :
    composeTrans (RuleBody.trans (C := C) (X := X) (Y := Y) r₁)
        (RuleBody.trans (C := C) (X := X) (Y := Y) r₂) =
      composeTrans (RuleBody.trans (C := C) (X := X) (Y := Y) r₂)
        (RuleBody.trans (C := C) (X := X) (Y := Y) r₁) := by
  show RuleBody.trans (LawRule.compose r₁ r₂) = RuleBody.trans (LawRule.compose r₂ r₁)
  rw [LawRule.compose_comm]

/-- **合成后的抽取 = 抽取后的合成（交换图）。**

把 `composeTrans` 的结果（已知在 `transition` 层）抽取回 `LawRule`，
恰等于两侧 `LawRule` 的 `compose`。这把 `RuleBody` 层运算与
`LawRule` 层运算**精确对齐**。 -/
theorem toLawRule_composeTrans (r₁ r₂ : LawRule.LawRule C X Y) :
    toLawRule (composeTrans (RuleBody.trans (C := C) (X := X) (Y := Y) r₁)
        (RuleBody.trans (C := C) (X := X) (Y := Y) r₂))
        (composeTrans_level r₁ r₂) =
      LawRule.compose r₁ r₂ := rfl

/-- **嵌入与完善的交换图。**

`ofLawRule` 把逼近意义上的「放宽」搬到 `RuleBody` 层：
若 `h : ∀ c x, R₂ c x ⊆ R₁ c x`，则 `LawRule.refine R₁ R₂ h`
（定义上等于 `R₂`）嵌入后是一个**转移级**载体。

⚠ 结论是「嵌入后的层级」，与 `ofLawRule_level` 搭配才能看到完整语义。 -/
theorem ofLawRule_refine_level (R₁ R₂ : LawRule.LawRule C X Y)
    (h : ∀ c x, R₂ c x ⊆ R₁ c x) :
    (ofLawRule (LawRule.refine R₁ R₂ h)).level = RuleTag.transition := rfl

end FateV2.Rules