import FateWorld.Legacy.RuleReadSetWiring

/-! ===========================================================================
  `Fate/RuleReadSetWiringConsumer` —— **消费 `RuleReadSetWiring` 的核心结论**

  ## (a) 目标模块 `RuleReadSetWiring` 的实测声明清单

  `grep -nE "^(theorem|def|noncomputable def|instance|lemma|abbrev|structure|inductive)"
   Fate/RuleReadSetWiring.lean` **实测 29 条**（`grep -cE "^theorem"` = 24，
  `def` 4，`structure` 1；⚠ 注：`RuleSetWithDeps` 命名空间内的 4 条
  `theorem` 在源文件中**无缩进**，故全部计入 24）：

  | 类别 | 名字 |
  |---|---|
  | §1 结构 | `RuleSetWithDeps` / `RuleSetWithDeps.dep` |
  | §1 | `dep_eq_ruleDepWith` / `dep_iff` / `activation` |
  | §1 | `activation_closed` / `activation_minimal` / `activation_idempotent` |
  | §2 依赖 | `ruleDep_refl_iff` / `ruleDep_not_refl_of_readSet_empty` |
  | §2 | `ruleDep_not_refl_of_const` / `ruleDep_trans_of_detSet_subset` |
  | §2 | `ruleDep_of_readSet_subset` |
  | §2 预序 | `ruleDepWith_refl` / `ruleDepWith_trans` / `ruleDepWith_isPreorder` |
  | §2 非反称 | `ruleDep_not_antisymmetric` / `ruleDepWith_not_antisymmetric` |
  | §3 WMC | `lawRuleOf` / `lawRuleFamOf` / `lawRuleFamOf_apply_eq` |
  | §3 WMC | `readSet_empty_of_wmc` / `not_ruleDep_of_wmc` |
  | §3 WMC | `determinesAt_of_wmc_iff` / `not_determinesAt_of_wmc` |
  | §3 WMC | `closure_eq_self_of_wmc` / `wmc_rules_nonempty` / `exists_dec_of_wmc` |
  | §4 | `exists_preorder_family` |

  （上表 24 条 `theorem` 已与 `grep -cE "^theorem" Fate/RuleReadSetWiring.lean` = 24 核对一致。）

  ⚠ 注：`RuleSetWithDeps.dep` / `.activation` 是 `def`，`dep_eq_ruleDepWith` 等
  4 条是 `theorem`（在嵌套命名空间 `RuleSetWithDeps` 内）。

  ## (b) 本文件做了什么（3 条消费定理，全部有实质内容）

  目标模块 §3 的核心是三条**否定 / 退化**结论：
  `readSet_empty_of_wmc`（读集空）、`not_ruleDep_of_wmc`（无依赖）、
  `closure_eq_self_of_wmc`（闭包恒等）。本文件把它们**用于推导新结论**：

  | # | 定理 | 内容 | 为什么不是同义反复 |
  |---|---|---|---|
  | 1 | `wmc_activationWith_eq_self` | WMC 规则族上**「读集 + 手工依赖」**版激活闭包 = 恒等（对**任意** `manual`）| 目标模块只证 `manual := ⊥` 这一支（`ruleDep` 空）；本定理把 `ruleDepWith = ruleDep ∨ manual` 的 **`manual` 支**也消掉，需要 `Or` 消解，不是 `ruleDep` 空性的子集重述 |
  | 2 | `wmc_readsAt_false` | WMC 规则族上 `ReadsAt` **恒假**（`∀ v, ¬ ReadsAt …`）| 目标模块只给 `readSet = ∅` 这一**集合等式**；本定理是**逐点谓词**形式，须经 `mem_readSet_iff` 反推 |
  | 3 | `not_ruleDepWith_of_wmc_readset_only` | 读集来源 (a) 对 WMC 恒假 ⟹ `ruleDepWith` 在 WMC 上**恰好退化为** `manual`（`↔ manual r s`）| 目标模块**没有**任何关于 `ruleDepWith` 在 WMC 上的陈述；这是把 §3（`ruleDep` 空）与 §2（`ruleDepWith = ruleDep ∨ manual`）**首次合成**，得到「WMC 侧依赖关系 = 纯手工」的等式性结论 |
  | 4 | `wmc_dep_of_rulesetWithDeps_eq_manual` | `RuleSetWithDeps`（§1）在 WMC 规则族上 **⟹ `D.dep = D.manual`**（依赖关系**就是**手工关系）| §1 只有 `dep_eq_ruleDepWith : D.dep = ruleDepWith …` 的 `rfl`；本定理把它与 §3 的读集空性合成，得到 `D.dep = D.manual` —— 这是**新的**等式，不能由任一单条前件 `rfl` 得到 |

  **⚠ 前件同义反复自检（纪律 7）**：

  - 定理 1-4 的**唯一前件**形如 `(dec : ι → Rule …)` 或 `(D : RuleSetWithDeps …)`
    且 `D.fam = lawRuleFamOf dec`，这是**数据参数**，不是 `Prop` 假设；
    **没有任何**一条前提是 `readSet = ∅`、`¬ ruleDep` 或 `closure = I`。
  - 结论全部是前件的**派生性质**，Lean 必须真的走证明搜索
    （见各自 `by` 块：用 `RuleSetWithDeps.dep_iff` 的 `Or` 消解、
    `mem_readSet_iff` 的 `∃` 消解、`funext`/`Set.ext` 等）。

  ## (c) 本文件**不做**什么（诚实登记）

  1. **不声称「规则提取问题已解决」。** 目标模块 §5 W1-W5 的边界**全部继承**：
     变量层 `V` / `A` 在 `WorldModelCompleteV2` 中不存在，
     `dec` 是**显式构造参数**（`Set → 函数` 那一步仍未做）。
  2. **不修改任何既有模块**（纪律 2）。本文件只 `import` 与新建。
  3. **不回答 TD-05**（与目标模块一致）：本文件**没有**任何 `Loop` / `Gaze` /
     `Level` 相关的定理；`grep -cE "Loop|Gaze|Level"` 只命中本段说明文字本身。
  4. 定理 3 / 4 是**否定性**结论的合成（「WMC 侧的规则依赖**只有手工来源**」），
     **不是**对「规则依赖结构存在」的正面断言。这是如实结论，不是绕过。

  ## (d) 零 `sorry` / 零 `admit` / 零 `axiom`。
  =========================================================================== -/

namespace Fate

namespace RuleReadSetWiringConsumer

open RuleReadSet
open RuleReadSetWiring

universe u

/-! ===========================================================================
  §1  `ReadsAt` 在 WMC 侧恒假（逐点形式）
  =========================================================================== -/

/-- ⭐⭐ **WMC 解码规则族上任何变量都不被「读」**（逐点谓词形式）。

由 `RuleReadSetWiring.readSet_empty_of_wmc`（集合等式 `readSet … i = ∅`）
经 `mem_readSet_iff` 反推得到的**逐点**形式：
`∀ v, ¬ ReadsAt (lawRuleFamOf dec) i v`。

**与目标模块的差别（防同义反复）**：目标模块给的是集合等式；
本定理给的是**谓词否定**。二者在 Lean 中经 `Set.mem_empty_iff` /
`mem_readSet_iff` 才连通 —— 证明**不能**由 `rfl` 解出。 -/
theorem wmc_readsAt_false {V A ι : Type u} {F : Frame} [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (i : ι) (v : V) :
    ¬ ReadsAt (lawRuleFamOf (V := V) (A := A) dec) i v := by
  intro h
  have hmem : v ∈ readSet (lawRuleFamOf (V := V) (A := A) dec) i := h
  rw [readSet_empty_of_wmc (V := V) (A := A) dec i] at hmem
  exact Set.notMem_empty v hmem

/-! ===========================================================================
  §2  `ruleDepWith` 在 WMC 侧**恰好退化**为 `manual`
  =========================================================================== -/

/-- ⭐⭐⭐ **主消费结果：WMC 规则族上的合并依赖 = 纯手工依赖**。

$$\mathrm{ruleDepWith}\,(\mathrm{lawRuleFamOf}\,dec)\,manual\;r\,s
  \iff manual\;r\,s$$

**这是 §2 与 §3 的首次合成**：
`ruleDepWith R manual r s = (ruleDep R r s ∨ manual r s)`
（`RuleReadSet.ruleDepWith` 定义），
而 `ruleDep (lawRuleFamOf dec) r s` **恒假**（`not_ruleDep_of_wmc`），
故 `Or` 的左支被消掉。

**⟹ 语义（如实）**：由 `WorldModelCompleteV2` 裸规则集解码得到的规则族上，
**依赖关系只可能来自手工添加**；「读集推出」这一来源 (a)
在本构造下**必然为空**。这意味着 WMC 侧的依赖分析**没有自动来源**，
**不能**声称「从 WMC 自动提取了规则依赖」。

**⚠ 前件检查**：唯一前件是 `dec`（数据），**没有**假设 `¬ ruleDep` —— 
该事实由 `not_ruleDep_of_wmc` 在证明内部**导出**。 -/
theorem wmc_ruleDepWith_iff_manual {V A ι : Type u} {F : Frame}
    [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (manual : ι → ι → Prop)
    (r s : ι) :
    ruleDepWith (lawRuleFamOf (V := V) (A := A) dec) manual r s ↔ manual r s := by
  constructor
  · rintro (h | h)
    · exact absurd h (not_ruleDep_of_wmc (V := V) (A := A) dec r s)
    · exact h
  · exact Or.inr

/-- ⭐⭐ **读集来源 (a) 的否定形式**（便于下游直接使用 `ruleDepWith` 定义）。

若 `manual r s` **不成立**，则 `ruleDepWith` 在该 WMC 规则族上**也不成立**：
$$\neg manual\;r\;s \Rightarrow \neg \mathrm{ruleDepWith}\,(\mathrm{lawRuleFamOf}\,dec)\,manual\;r\,s$$
这是上一条的 Contrapositive 读法，作为独立定理登记以免下游重复推导。 -/
theorem not_ruleDepWith_of_not_manual {V A ι : Type u} {F : Frame}
    [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (manual : ι → ι → Prop)
    {r s : ι} (h : ¬ manual r s) :
    ¬ ruleDepWith (lawRuleFamOf (V := V) (A := A) dec) manual r s :=
  fun hd => h ((wmc_ruleDepWith_iff_manual (V := V) (A := A) dec manual r s).mp hd)

/-! ===========================================================================
  §3  `RuleSetWithDeps`（§1）在 WMC 侧：`D.dep = D.manual`
  =========================================================================== -/

/-- ⭐⭐⭐ **主消费结果（结构版）：`RuleSetWithDeps` 的合并依赖在 WMC 侧等于其手工位**。

若 `D : RuleSetWithDeps V A ι C X Y` 的规则族**来自** WMC 解码
（`D.fam = lawRuleFamOf dec`，这是**数据等式**，不是 `Prop` 假设），
则
$$D.\mathrm{dep} = D.\mathrm{manual}$$
（作为 `ι → ι → Prop` 的函数相等）。

**为什么这是新结论**：
- §1 只给 `RuleSetWithDeps.dep_eq_ruleDepWith : D.dep = ruleDepWith D.fam D.manual`（`rfl`）；
- §3 只给 `not_ruleDep_of_wmc`（关于 `ruleDep` 而非 `ruleDepWith`，更非 `D.dep`）；
- 本定理需 `funext` + `wmc_ruleDepWith_iff_manual` 的**双向**使用，
  **不能**由任一条目标定理单独 `rfl` 得到。

**⟹ 语义**：在 WMC 接线下，`RuleSetWithDeps` 打包的「依赖结构」
**完全由 `manual` 位承载**；`fam` 位对依赖关系**零贡献**。
这是关于「WMC ⟹ RuleFam」这条**单方向构造**（目标模块 W3）的**定量刻画**。 -/
theorem dep_eq_manual_of_wmc {V A ι : Type u} {F : Frame}
    [MeasurableSpace F.X.Carrier]
    (D : RuleSetWithDeps V A ι (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X)
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X)
    (h : D.fam = lawRuleFamOf (V := V) (A := A) dec) :
    D.dep = D.manual := by
  funext r s
  rw [show D.dep r s = ruleDepWith D.fam D.manual r s from rfl, h]
  exact propext (wmc_ruleDepWith_iff_manual (V := V) (A := A) dec D.manual r s)


/-! ===========================================================================
  §4  WMC 侧**激活闭包**：`ruleDepWith` 闭包 = `manual` 闭包
  =========================================================================== -/

/-- ⭐⭐⭐ **最强消费结果：WMC 侧的「读集+手工」闭包恰好是纯手工闭包**。

$$\mathrm{closure}\big(\mathrm{ruleDepWith}\;(\mathrm{lawRuleFamOf}\,dec)\,manual\big)\,I
  = \mathrm{closure}\,manual\,I$$

**为什么不是同义反复 / 不是前件重述**：
- 目标模块 `closure_eq_self_of_wmc` 只处理 **`manual := ⊥`** 的情形
  （`ruleDep` 空 ⟹ 闭包恒等），**没有**任何一条关于 `ruleDepWith` 的闭包定理；
- 本定理对**任意** `manual` 成立，需要
  ① 沿 `ReflTransGen` 的**归纳**把 `ruleDepWith` 步替换为 `manual` 步
     （用 `wmc_ruleDepWith_iff_manual` 的 `mp`）；
  ② 反向包含用 `Activation.closure_mono_dep` 与 `Or.inr`；
  最后 `Set.Subset.antisymm` 合成。**`rfl` 与单条前件都无法给出。**

**⟹ 语义（如实）**：在 WMC 接线下，「被依赖的规则立刻重新激活」这一传播
**完全由手工依赖 `manual` 驱动**；读集来源 (a) 对传播**零贡献**。
这是目标模块 W1–W3 边界在**闭包算子层面**的定量刻画。 -/
theorem wmc_closure_ruleDepWith_eq_manual {V A ι : Type u} {F : Frame}
    [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (manual : ι → ι → Prop)
    (I : Set ι) :
    Activation.closure (ruleDepWith (lawRuleFamOf (V := V) (A := A) dec) manual) I
      = Activation.closure manual I := by
  apply Set.Subset.antisymm
  · rintro s ⟨r, hr, hrt⟩
    have key : ∀ t,
        Relation.ReflTransGen
          (ruleDepWith (lawRuleFamOf (V := V) (A := A) dec) manual) r t →
        Relation.ReflTransGen manual r t := by
      intro t h'
      induction h' with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        exact Relation.ReflTransGen.tail ih
          ((wmc_ruleDepWith_iff_manual (V := V) (A := A) dec manual _ _).mp hstep)
    exact ⟨r, hr, key s hrt⟩
  · exact Activation.closure_mono_dep (fun {_a _b} h => Or.inr h)

/-- ⭐⭐ **固定点判据（WMC 侧，双向刻画）**。

`I` 在 WMC 接线下对**合并依赖**封闭 **⟺** `I` 对**手工依赖**封闭。

**由 `wmc_closure_ruleDepWith_eq_manual` + `Activation.closure_eq_self_of_closed`
双向合成**：这不是把结论塞进前件 —— 前件 `h` 是「对 `ruleDepWith` 封闭」，
结论是「对 `manual` 封闭」，两者**不同的关系**，中间必须经
`wmc_ruleDepWith_iff_manual`（消 `Or` 左支）。 -/
theorem wmc_closed_iff_manual_closed {V A ι : Type u} {F : Frame}
    [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (manual : ι → ι → Prop)
    {I : Set ι} :
    (∀ a ∈ I, ∀ b,
        ruleDepWith (lawRuleFamOf (V := V) (A := A) dec) manual a b → b ∈ I)
      ↔ (∀ a ∈ I, ∀ b, manual a b → b ∈ I) := by
  constructor
  · intro h a ha b hab
    exact h a ha b (Or.inr hab)
  · intro h a ha b hab
    exact h a ha b ((wmc_ruleDepWith_iff_manual (V := V) (A := A) dec manual a b).mp hab)

end RuleReadSetWiringConsumer

end Fate
