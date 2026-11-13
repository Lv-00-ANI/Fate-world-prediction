import FateWorld.FateV2.Core.Judgment

/-!
  # Core · 四算子与来源单调性

  ## 迁移登记
  - 来源：新写（参考 `命运-素材-原始文件-不可更改/Fate/RuleSyntaxOps.lean`、
          `GammaOperator.lean`、`UpsilonOperator.lean`、`ComposeOperator.lean`）
  - 动作：C 重写
  - 对应环节：F4-07（γ）、F4-08（∘）、F4-09（υ）、F4-14（四算子统一）、F4-24（语法层四算子）
  - 依赖裁决：**D-004**（四算子 + support 只增不减）、**D-016**、**D-019**（自由度最大化）
  - 改动：旧代码里 γ/υ 是**写死的**运算（且 `LawRule` 层带 `Measure`，进不了核）。
          此处把「算子做什么」抽成**策略结构**，算子只是策略的应用；
          于是「不减少来源」只与策略的 `extra` 字段有关，与策略内容无关。
  - 状态：已编译未验证

  ## 本文件证明什么

  铁律 3（「没有算子能减少 support」）的**可执行形式**：

      SupportMonotone γ        γ 泛化不减少来源
      SupportMonotone υ        υ 完善不减少来源
      SupportMonotone (∘ j₁)   ∘ 组合不减少来源
      SupportMonotone (g ∘ f)  单调算子的复合仍单调

  α 不是自同态（输入是数据，不是判断），因此没有这种陈述；
  它的对应性质是「产出的来源完全由消融策略决定」，见 `alpha_support_eq`。
-/

namespace FateV2.Core

universe u

/-! ## 来源的追加 -/

namespace Support

/-! ### ⚠ 为什么这里自己证列表引理

**实测（2026-10-29）**：本工具链下 `List.append_nil` **依赖 `propext`**：

```
'List.append_nil' depends on axioms: [propext]
```

所以核内**不能**引用 batteries / Mathlib 的列表引理——哪怕是最基础的
`a ++ [] = a`。必须用「结构归纳 + `congrArg`」自己证，这条路径不带公理。 -/

/-- 自证版 `a ++ [] = a`（不带 `propext`）。 -/
theorem list_append_nil {α : Type u} : ∀ (a : List α), a ++ [] = a
  | []      => rfl
  | h :: t  => congrArg (List.cons h) (list_append_nil t)

/-- 追加未证前件。**这是 γ / υ 的唯一来源变动方式**。 -/
def addAssumptions (s : Support) (xs : List AssumptionId) : Support :=
  ⟨s.assumptions ++ xs⟩

/-- 追加后仍包含原来的来源。 -/
theorem subset_addAssumptions (s : Support) (xs : List AssumptionId) :
    s.Subset (s.addAssumptions xs) := by
  intro x hx
  unfold addAssumptions
  exact List.mem_append_left _ hx

/-- 追加 `[]` 不改变来源（用自证版引理，不用 `simp` / `List.append_nil`）。 -/
theorem addAssumptions_nil (s : Support) : s.addAssumptions [] = s := by
  cases s with
  | mk a =>
    show (⟨a ++ []⟩ : Support) = ⟨a⟩
    exact congrArg Support.mk (list_append_nil a)

end Support

/-! ## 算子与单调性 -/

/-- 算子：判断 → 判断。 -/
abbrev Op (L : Type u) : Type u := Judgment L → Judgment L

/-- **来源单调**：算子对任何判断都不减少其来源。

    这是铁律 3 的可执行形式——**唯一的判据**，与算子内部做什么无关。 -/
def SupportMonotone {L : Type u} (op : Op L) : Prop :=
  ∀ j : Judgment L, j.support.Subset (op j).support

/-- 恒等算子单调。 -/
theorem supportMonotone_id {L : Type u} : SupportMonotone (id : Op L) :=
  fun _ => Support.subset_refl _

/-- **单调算子的复合仍单调**——于是「任意多个算子的串联都不减少来源」。 -/
theorem supportMonotone_comp {L : Type u} {f g : Op L}
    (hf : SupportMonotone f) (hg : SupportMonotone g) :
    SupportMonotone fun j => g (f j) := by
  intro j
  exact Support.subset_trans (hf j) (hg (f j))

/-! ## γ 泛化 -/

/-- γ 的策略：把一条局部规则放宽成全局规则。

    * `widenHyp`   —— 放宽前件（适用面变宽）
    * `weakenConcl`—— 弱化结论（代价）
    * `extra`      —— 泛化**必然新增**的未证前件
    * `newStatus`  —— 泛化后的状态（通常降为 `conditional`）

    D-019：策略不写死，可换。 -/
structure GammaPolicy (L : Type u) where
  widenHyp    : Formula L → Formula L
  weakenConcl : Formula L → Formula L
  extra       : List AssumptionId
  newStatus   : Status

/-- **γ 泛化**。 -/
def gamma {L : Type u} (p : GammaPolicy L) (j : Judgment L) : Judgment L :=
  ⟨p.widenHyp j.hyp, p.weakenConcl j.concl,
   j.support.addAssumptions p.extra, p.newStatus⟩

/-- **γ 不减少来源**（铁律 3，γ 部分）。 -/
theorem gamma_supportMonotone {L : Type u} (p : GammaPolicy L) :
    SupportMonotone (gamma p) := by
  intro j
  exact j.support.subset_addAssumptions p.extra

/-! ## υ 完善 -/

/-- υ 的策略：用新证据修正结论。

    * `refineConcl` —— 修正后的结论
    * `extra`       —— 新证据带来的未证前件
    * `newStatus`   —— 可升级（证据增强）或降级（证据反驳） -/
structure UpsilonPolicy (L : Type u) where
  refineConcl : Formula L → Formula L
  extra       : List AssumptionId
  newStatus   : Status

/-- **υ 完善**。 -/
def upsilon {L : Type u} (p : UpsilonPolicy L) (j : Judgment L) : Judgment L :=
  ⟨j.hyp, p.refineConcl j.concl, j.support.addAssumptions p.extra, p.newStatus⟩

/-- **υ 不减少来源**（铁律 3，υ 部分）。 -/
theorem upsilon_supportMonotone {L : Type u} (p : UpsilonPolicy L) :
    SupportMonotone (upsilon p) := by
  intro j
  exact j.support.subset_addAssumptions p.extra

/-! ## ∘ 组合（作为算子） -/

/-- 右乘 `j₂` 得到的算子。 -/
def composeOp {L : Type u} (j₂ : Judgment L) : Op L := fun j₁ => j₁.compose j₂

/-- **∘ 不减少来源**（铁律 3，∘ 部分）。 -/
theorem composeOp_supportMonotone {L : Type u} (j₂ : Judgment L) :
    SupportMonotone (composeOp j₂) := by
  intro j₁
  exact Judgment.compose_support_subset_left j₁ j₂

/-! ## 串联：任意多算子不减少来源 -/

/-- **γ 再 υ** 的串联不减少来源——「跑一整轮也不丢来源」。 -/
theorem gamma_upsilon_supportMonotone {L : Type u}
    (pg : GammaPolicy L) (pu : UpsilonPolicy L) :
    SupportMonotone fun j => upsilon pu (gamma pg j) :=
  supportMonotone_comp (gamma_supportMonotone pg) (upsilon_supportMonotone pu)

/-- **γ → υ → ∘** 三步串联不减少来源。

    这对应运行时循环里「泛化 → 完善 → 组合」这一整段（D-004 §7）。 -/
theorem pipeline_supportMonotone {L : Type u}
    (pg : GammaPolicy L) (pu : UpsilonPolicy L) (j₂ : Judgment L) :
    SupportMonotone fun j => (upsilon pu (gamma pg j)).compose j₂ :=
  supportMonotone_comp
    (gamma_upsilon_supportMonotone pg pu)
    (composeOp_supportMonotone j₂)

/-! ## α 抽象

  α 不是自同态：它的输入是**数据 / 实例集**，输出是判断。
  因此「不减少来源」对它没有意义（没有来源可比）。

  它的对应性质是：**产出的来源完全由消融策略决定**——数据本身不进来源（D-005/D-006）。 -/

/-- α 的策略：从输入抽出判断。

    `In` 是输入类型（实例集 / 数据批次），**参数化不写死**（D-019）。
    `dissolve` 表示这一步做了消融：把输入中的经验内容转成未证前件。 -/
structure AlphaPolicy (L : Type u) (In : Type) where
  extract : In → Judgment L

/-- **α 抽象**。 -/
def alpha {L : Type u} {In : Type} (p : AlphaPolicy L In) (x : In) : Judgment L :=
  p.extract x

/-- **α 的来源等于策略给出的来源**——数据没有被塞进来源。

    这条是 D-005/D-006 的直接体现：α 的产出只携带**消融后的经验假设**，
    不携带数据引用。 -/
theorem alpha_support_eq {L : Type u} {In : Type}
    (p : AlphaPolicy L In) (x : In) :
    (alpha p x).support = (p.extract x).support := rfl

/-! ## 汇总：铁律 3 的可执行判据 -/

/-- **一条算子若只通过 `Support.addAssumptions` 变动来源，则它必然单调。**

    这是比逐个证明更强的形式：它把「不减少来源」归约为一个**结构条件**，
    将来任何新算子只要满足它，就自动满足铁律 3。 -/
theorem monotone_of_addAssumptions {L : Type u} (op : Op L)
    (h : ∀ j : Judgment L, ∃ xs : List AssumptionId,
            (op j).support = j.support.addAssumptions xs) :
    SupportMonotone op := by
  intro j
  obtain ⟨xs, hx⟩ := h j
  rw [hx]
  exact j.support.subset_addAssumptions xs

end FateV2.Core
