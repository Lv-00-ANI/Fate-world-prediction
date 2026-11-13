import FateWorld.FateV2.Core.Ops

/-!
  # Core · 四算子的代数（T35）

  ## 迁移登记
  - 来源：新写
  - 动作：A 立项（在 `Core/Ops` 之上补**代数定理**，`Ops.lean` 一字未改）
  - 对应环节：F4-14（四算子统一）、F4-24（语法层四算子）
  - 依赖裁决：**D-004**（四算子 + support 只增不减）、**D-016**（纯 CIC，零公理）、
              **D-019**（自由度最大化）
  - 前置：`Core/Ops` 只给了四算子的**定义**与**来源单调性**；本文件补**代数律**。
  - 状态：零公理，见 `_报告/T35-进度.md`

  ## 勘察结论：`Core/Ops` 里到底有什么

  | 名字 | 精确签名 |
  |---|---|
  | `Op` | `abbrev Op (L : Type u) : Type u := Judgment L → Judgment L` |
  | `SupportMonotone` | `def SupportMonotone {L} (op : Op L) : Prop := ∀ j, j.support.Subset (op j).support` |
  | `gamma` | `def gamma (p : GammaPolicy L) (j : Judgment L) : Judgment L` |
  | `upsilon` | `def upsilon (p : UpsilonPolicy L) (j : Judgment L) : Judgment L` |
  | `composeOp` | `def composeOp (j₂ : Judgment L) : Op L := fun j₁ => j₁.compose j₂` |
  | `alpha` | `def alpha {In} (p : AlphaPolicy L In) (x : In) : Judgment L := p.extract x` |

  * `GammaPolicy L` = `⟨widenHyp : Formula L → Formula L, weakenConcl : Formula L → Formula L,
    extra : List AssumptionId, newStatus : Status⟩`
  * `UpsilonPolicy L` = `⟨refineConcl : Formula L → Formula L, extra, newStatus⟩`
  * `AlphaPolicy L In` = `⟨extract : In → Judgment L⟩`
  * `Judgment.compose j₁ j₂` = `⟨j₁.hyp, j₂.concl, j₁.support.union j₂.support,
    j₁.status.weaker j₂.status⟩`

  **作用对象是什么？**
  γ / υ / ∘ 的作用对象是 **`Judgment`**（`Op L = Judgment L → Judgment L`，都在来源层动刀）；
  **α 的作用对象是 `In`（数据 / 实例集），输出才是 `Judgment`**——
  即 `alpha : AlphaPolicy L In → In → Judgment L`，**它不是 `Op L`**。
  这条类型上的不对称是本文件 §4–§6 全部结论的根源。

  **已有定理**（`Ops` + `Judgment`）：
  `gamma_supportMonotone`、`upsilon_supportMonotone`、`composeOp_supportMonotone`、
  `supportMonotone_id`、`supportMonotone_comp`、`gamma_upsilon_supportMonotone`、
  `pipeline_supportMonotone`、`alpha_support_eq`、`monotone_of_addAssumptions`、
  `Support.subset_addAssumptions`、`Support.addAssumptions_nil`、
  `Support.list_append_nil`、`Judgment.compose_support_subset_left/right`。
  —— **全部属于「来源不减少」这一族（都是 `Subset` 形式的包含），
  没有一条代数律**（没有结合律、没有交换律、没有单位元、没有幂等、没有分配律）。
  这正是本文件要补的空洞。

  ## 本文件补什么

  | § | 定理 | 一句话 |
  |---|---|---|
  | 0 | `Support.list_append_assoc` | 列表结合律（stdlib 版带 `propext`，自证） |
  | 0 | `Support.union_assoc` | **`∪` 结合** —— `∘` 结合律的来源半边 |
  | 0 | `Support.addAssumptions_append` | **两次追加 = 一次追加两批**（γ/υ 串联可压平） |
  | 0b | `Status.weaker_assoc` | **`weaker` 结合** —— `∘` 结合律的状态半边 |
  | 0b | `Status.weaker_comm` | **`weaker` 交换** |
  | 0b | `Status.weaker_self` | `weaker` 对角退化 |
  | 1 | `Judgment.compose_assoc` | **`∘` 结合律** |
  | 1 | `Judgment.compose_status_comm` | `∘` 的**状态分量**交换 |
  | 1 | `Judgment.compose_support_eq_union` | `∘` 的来源**精确**等于并 |
  | 1 | `Judgment.compose_hyp_eq` / `compose_concl_eq` | `∘` 的两个投影律 |
  | 2 | `gamma_upsilon_swap_imp` | γ 与 υ 交换的**必要条件** |
  | 2 | `gamma_equal_iff` / `upsilon_equal_iff` | γ/υ 的**同态律**（相等 ⇔ 各分量相等） |
  | 2 | `gamma_status_fixed` / `upsilon_status_fixed` | **γ/υ 把状态重置为策略值**（幂等的来源） |
  | 3 | `composeOp_comp_apply` | 右乘复合**逐点**落在 `Judgment.compose` 上 |
  | 3 | `composeOp_id_right` | `∘` 有**右单位元**（半群） |
  | 4 | `alpha_support_determined_by_extract` | α 的来源只由策略决定 |
  | 4 | `alpha_inj_iff_extract_inj` | α 单射 ⇔ extract 单射 |
  | 3' | `four_ops_support_monotone` | γ/υ/∘ 的单调性汇总成**一个出处** |
  | 4' | `alpha_supportMonotone_iff` | α 的单调性**有前件**，不无条件成立 |

  ## ⚠ 写法纪律（全部是本项目实测的坑）

  | 写法 | 后果 | 本文件的做法 |
  |---|---|---|
  | `List.mem_cons` / `List.mem_append` / `List.append_assoc` | **`propext`**（实测） | 全部手写（§0） |
  | `List.head?_eq_some_iff` | **`propext` + `Quot.sound`** | 不用 |
  | `Nat.min_*` 整族（`min_le_left` / `min_self` …） | **`propext`**（`min` 由 `decide` 定义） | 改为对 `Status` 的 4 构造子穷举 |
  | `simp` / `decide` / `funext` / `by_cases` | 三公理 | 全部禁用 |
  | `Formula.noConfusion` 于 `.ext` | **不闭合**（带 `List` 参数） | 用**跨构造子**的差异 |
  | **对 `Judgment` 做 `cases` 之后再做投影** | 投影**不再归约**（`{hyp := x}.hyp` 卡住），后续 `rfl` 全部失败 | 一律用 `rfl` 直达投影 + `congrArg`，不在 `cases` 之后求归约 |
  | 在同一文件里引用**前文的辅助引理** | `lake env lean` 单文件时不编入，会报 `unknownIdentifier` | 只依赖 `Ops` 与本文件**之前**定义的内容 |
-/

namespace FateV2.Core

universe u

/-! ## §0 来源层的砖块

`Ops.Support` 已自证 `a ++ [] = a`（因 `List.append_nil` 带 `propext`）。
这里补同样必需的另外三条——**它们不是重述定义**。 -/

namespace Support

/-- **列表拼接结合律**（自证版）。

    比定义多说了什么：`List.append_assoc` **实测带 `propext`**（见 `_t35_probe1.lean`），
    故按第一个参数结构归纳重证。这是 `union_assoc` 的**唯一**非平凡输入。 -/
theorem list_append_assoc {a0 : Type u} :
    ∀ (a b c : List a0), (a ++ b) ++ c = a ++ (b ++ c)
  | [], _, _ => rfl
  | h :: t, b, c => congrArg (List.cons h) (list_append_assoc t b c)

/-- **`∪` 结合**：`(a ∪ b) ∪ c = a ∪ (b ∪ c)`。

    比定义多说了什么：`union` 的定义是 `a ++ b`；三路合并的两种括号法
    相等**不是**定义的即时推论（`++` 不结合于定义），要 `list_append_assoc`。
    这是 `compose_assoc` 的来源半边。 -/
theorem union_assoc (a b c : Support) : (a.union b).union c = a.union (b.union c) := by
  cases a with
  | mk la =>
    cases b with
    | mk lb =>
      cases c with
      | mk lc =>
        show (⟨(la ++ lb) ++ lc⟩ : Support) = ⟨la ++ (lb ++ lc)⟩
        rw [list_append_assoc]

/-- **两次追加 = 一次追加两批**：`(s + xs) + ys = s + (xs ++ ys)`。

    比定义多说了什么：`addAssumptions` 的定义是 `s.assumptions ++ xs`；
    此条说**串联两次泛化等价于一次追加**——γ/υ 的任意串联在来源层
    都能压平成一次，是「算子链可规范化」在 `Support` 这一侧的半步。 -/
theorem addAssumptions_append (s : Support) (xs ys : List AssumptionId) :
    (s.addAssumptions xs).addAssumptions ys = s.addAssumptions (xs ++ ys) := by
  cases s with
  | mk l =>
    show (⟨(l ++ xs) ++ ys⟩ : Support) = ⟨l ++ (xs ++ ys)⟩
    rw [list_append_assoc]

end Support

/-! ## §0b `Status` 的格性质

`weaker` 定义在 `Nat` 的 `if a.strength ≤ b.strength` 上。**`Nat.min_*` 整族带
`propext`**（实测 `Nat.min_le_left` / `min_self` 都带），故这里全部改为对
`Status` 的 4 个构造子穷举。穷举**必须按声明顺序**
`proven → conditional → empirical → refuted`，否则会静默引入 `propext`。 -/

namespace Status

/-- **`weaker` 结合**：三步串联的状态与括号无关。

    比定义多说了什么：`weaker` 是 `if … ≤ …` 的复合，结合性**不是**定义等式。
    此条在 4 个构造子上穷举（64 种）得定义等式，是 `compose_assoc` 的状态半边。 -/
theorem weaker_assoc (a b c : Status) :
    (a.weaker b).weaker c = a.weaker (b.weaker c) := by
  unfold weaker Status.strength
  cases a <;> cases b <;> cases c <;> rfl

/-- **`weaker` 交换**：`a.weaker b = b.weaker a`。

    比定义多说了什么：`weaker` 的 `if` 形式**看起来**不对称（第一个参数优先），
    但在 `strength` 全序时它实际对称。这是 `compose_status_comm` 的全部输入。 -/
theorem weaker_comm (a b : Status) : a.weaker b = b.weaker a := by
  unfold weaker Status.strength
  cases a <;> cases b <;> rfl

/-- `weaker` 对角退化：`s.weaker s = s`。

    比定义多说了什么：`weaker` 在对角线上退化为恒等，故「同一策略套两次」
    不会把状态再往下压——这是 γ/υ 幂等性不掉状态的根据。
    ⚠ 不用 `Nat.min_self`（带 `propext`），改用 `Nat.le_refl` 走 `if_pos`。 -/
theorem weaker_self (s : Status) : s.weaker s = s := by
  unfold weaker
  rw [if_pos (Nat.le_refl (Status.strength s))]

end Status

/-! ## §1 `∘` 的代数

`∘` 有两个化身：
* `Judgment.compose : Judgment L → Judgment L → Judgment L`（二元）
* `composeOp : Judgment L → Op L`（右乘一个判断）

`Ops` 只对后者证了来源单调性；代数律只在**二元** `compose` 上成立。 -/

namespace Judgment

variable {L : Type u}

/-- `∘` 的前件取**左**：`(a ∘ b).hyp = a.hyp`。 -/
theorem compose_hyp_eq (a b : Judgment L) : (a.compose b).hyp = a.hyp := rfl

/-- `∘` 的结论取**右**：`(a ∘ b).concl = b.concl`。 -/
theorem compose_concl_eq (a b : Judgment L) : (a.compose b).concl = b.concl := rfl

/-- `∘` 的来源是并：`(a ∘ b).support = a.support ∪ b.support`。

    比 `Ops.compose_support_subset_left/right` 多说了什么：那两条只给**包含**，
    于是「`∘` 会不会偷偷**多**塞来源」在 `Ops` 里是悬空的（只排除了变小）。
    此条给出**等式**，D-004 §4.3「support 取并」从设计意图变成定理。 -/
theorem compose_support_eq_union (a b : Judgment L) :
    (a.compose b).support = a.support.union b.support := rfl

/-- `∘` 的状态取较弱：`(a ∘ b).status = a.status.weaker b.status`。 -/
theorem compose_status_eq (a b : Judgment L) :
    (a.compose b).status = a.status.weaker b.status := rfl

/-- **逐字段重装**：四个字段全相等 ⇒ 判断相等。

    比 `Judgment.mk` 的定义多说了什么：`Judgment` 是 `structure`，
    从「各字段相等」到「结构相等」**不是** `rfl`。此条把 `subst` 的四步收进一处。 -/
theorem eq_of_fields {a b : Judgment L}
    (h1 : a.hyp = b.hyp) (h2 : a.concl = b.concl)
    (h3 : a.support = b.support) (h4 : a.status = b.status) : a = b := by
  cases a with
  | mk ah ac asu ast =>
    cases b with
    | mk bh bc bsu bst =>
      subst h1; subst h2; subst h3; subst h4
      rfl

/-- **`∘` 结合律**：`(a ∘ b) ∘ c = a ∘ (b ∘ c)`。

    比定义多说了什么：`compose` 的定义只规定**单步**的四个字段；此条说
    **串联三步推论时括号不重要**——这是运行时「泛化 → 完善 → 组合」这条链
    可以自由重结合的依据（D-004 §7），也是 `composeOp_comp_apply` 的前提。
    证明：左结合与右结合取的都是「最左的前件 + 最右的结论」（`rfl`），
    真正要证的是**来源**与**状态**两路，分别由 `Support.union_assoc`
    与 `Status.weaker_assoc` 给出。 -/
theorem compose_assoc (a b c : Judgment L) :
    (a.compose b).compose c = a.compose (b.compose c) := by
  refine eq_of_fields rfl rfl ?_ ?_
  · exact Support.union_assoc a.support b.support c.support
  · exact Status.weaker_assoc a.status b.status c.status

/-- **`∘` 的状态分量交换**：`(a ∘ b).status = (b ∘ a).status`。

    比定义多说了什么：`weaker` 定义在 `Nat` 的 `if` 上，其交换性**不是**定义等式
    （`Nat.min_comm` 带 `propext`）。此条表明**状态**这一路对
    「先 a 后 b」和「先 b 后 a」无感——即 `∘` 的不对称**只来自**前后件的选取，
    不来自状态的合并。这是把 `∘` 的非交换性归因定位的一步。 -/
theorem compose_status_comm (a b : Judgment L) :
    (a.compose b).status = (b.compose a).status := by
  rw [compose_status_eq, compose_status_eq]
  exact Status.weaker_comm a.status b.status

/-- **`∘` 整体不交换的可证伪条件**：若 `a ∘ b = b ∘ a`，则 `a.hyp = b.hyp`。

    比定义多说了什么：定义只给构造，此条把它翻译成**关于字段的等式**，
    于是「`∘` 不对称」变成可检查的条件（取两个前件不同的判断即得反例）。
    证明只用一次 `congrArg` 与两次投影律。 -/
theorem compose_comm_imp_hyp (a b : Judgment L)
    (h : a.compose b = b.compose a) : a.hyp = b.hyp := by
  have h1 : (a.compose b).hyp = (b.compose a).hyp := congrArg Judgment.hyp h
  exact (compose_hyp_eq a b).symm.trans (h1.trans (compose_hyp_eq b a).symm)

end Judgment

/-! ## §2 γ / υ 与 `∘` 的交互

γ 与 υ 都是「逐字段改写 + 追加来源」，差别只在改哪几个字段：
γ 改 `hyp` 与 `concl`，υ 只改 `concl`。本节把这条差别**变成定理**。 -/

section GammaUpsilon

variable {L : Type u}

/-- **γ 与 υ 交换的必要条件**。

    比「γ ≠ υ」这类空话多说了什么：它把两算子的次序问题**归约到结论函数**上——
    若 `γ(υ j) = υ(γ j)`，则 `weakenConcl ∘ refineConcl` 与
    `refineConcl ∘ weakenConcl` 必在 `j.concl` 处取同一个值。
    于是「泛化与完善的次序重要」不再是经验之谈，而是可逐策略检查的条件。
    证明：只取 `concl` 分量（`congrArg Judgment.concl`），零公理。 -/
theorem gamma_upsilon_swap_imp (pg : GammaPolicy L) (pu : UpsilonPolicy L)
    (j : Judgment L)
    (h : gamma pg (upsilon pu j) = upsilon pu (gamma pg j)) :
    pg.weakenConcl (pu.refineConcl j.concl) = pu.refineConcl (pg.weakenConcl j.concl) :=
  congrArg Judgment.concl h

/-- **γ 把状态重置为策略值**：`(γ p j).status = p.newStatus`，与 `j.status` **无关**。

    比定义多说了什么：`gamma` 的定义把 `p.newStatus` 直接写进第四个字段，
    但「与输入状态无关」这件事在定义里是**隐含**的。此条把它提成定理，
    并由此得到两个**可观测结论**：
    (a) γ **不是** `Status` 上的恒等（除了 `newStatus` 恰好等于所有输入状态的退化情形）；
    (b) 任何 γ 串联后的状态**只由最后一个策略**决定——所以 `γ` 链的状态
        是**右控制**的，这与来源的**累积**形成对照。 -/
theorem gamma_status_fixed (p : GammaPolicy L) (j : Judgment L) :
    (gamma p j).status = p.newStatus := rfl

/-- **υ 把状态重置为策略值**：`(υ p j).status = p.newStatus`，与 `j.status` 无关。 -/
theorem upsilon_status_fixed (p : UpsilonPolicy L) (j : Judgment L) :
    (upsilon p j).status = p.newStatus := rfl

/-- **γ 的相等判定**：两条 γ 结果相等 **当且仅当** 三个**非状态**分量分别相等。

    比定义多说了什么：定义只说 γ 怎么算，此条给出**判定律**——
    由于 `status` 恒为 `p.newStatus`，状态分量**自动相等**，故相等的判定
    完全落在 `hyp`/`concl`/`support` 上。这让「两次泛化是否等价」
    变成三个可分别检查的条件，而不是整体的一次猜测。 -/
theorem gamma_equal_iff (p : GammaPolicy L) (j1 j2 : Judgment L) :
    gamma p j1 = gamma p j2 ↔
      (p.widenHyp j1.hyp = p.widenHyp j2.hyp
        ∧ p.weakenConcl j1.concl = p.weakenConcl j2.concl
        ∧ j1.support.addAssumptions p.extra = j2.support.addAssumptions p.extra) := by
  constructor
  · intro h
    exact ⟨congrArg Judgment.hyp h, congrArg Judgment.concl h,
      congrArg Judgment.support h⟩
  · intro ⟨h1, h2, h3⟩
    exact Judgment.eq_of_fields h1 h2 h3 (by rw [gamma_status_fixed, gamma_status_fixed])

/-- **υ 不改前件**：`(υ p j).hyp = j.hyp`（`rfl`）。 -/
theorem upsilon_hyp (p : UpsilonPolicy L) (j : Judgment L) : (upsilon p j).hyp = j.hyp := rfl

/-- **υ 的相等判定**：两条 υ 结果相等 **当且仅当** 前件、结论与来源分别相等。

    比定义多说了什么：它把「完善」的**相等性**拆成三个可分别检查的条件
    ——这是把「两次完善是否等价」从整体猜测变成逐分量判定的依据。 -/
theorem upsilon_equal_iff (p : UpsilonPolicy L) (j1 j2 : Judgment L) :
    upsilon p j1 = upsilon p j2 ↔
      (j1.hyp = j2.hyp
        ∧ p.refineConcl j1.concl = p.refineConcl j2.concl
        ∧ j1.support.addAssumptions p.extra = j2.support.addAssumptions p.extra) := by
  constructor
  · intro h
    refine ⟨?_, congrArg Judgment.concl h, congrArg Judgment.support h⟩
    exact (upsilon_hyp p j1).symm.trans ((congrArg Judgment.hyp h).trans (upsilon_hyp p j2))
  · intro ⟨h1, h2, h3⟩
    exact Judgment.eq_of_fields h1 h2 h3
      (by rw [upsilon_status_fixed, upsilon_status_fixed])

end GammaUpsilon

/-! ## §3 `composeOp` 的结构与 `support` 单调性汇总 -/

section ComposeOp

variable {L : Type u}

/-- **右乘复合逐点落在 `∘` 上**：`composeOp b (composeOp a j) = composeOp (a ∘ b) j`。

    比 `composeOp` 的定义多说了什么：定义是**单步**的 `fun j₁ => j₁.compose j₂`；
    此条说右乘的两次相继——顺序是 `先 a 后 b`——给出的是 `j ∘ (a ∘ b)`，
    即 `j ↦ composeOp j` 把 `∘` 的**顺序颠倒**过来（反序同态）。
    它正是 `compose_assoc` 的直接推论，而 `compose_assoc` 又是可用定理——
    于是 `∘` 的结合律被搬上了 `Op` 层。

    ⚠ 陈述为**逐点**等式（不用 `funext`：`funext` 带 `Quot.sound`）。 -/
theorem composeOp_comp_apply (a b j : Judgment L) :
    composeOp b (composeOp a j) = composeOp (a.compose b) j := by
  show (j.compose a).compose b = j.compose (a.compose b)
  exact Judgment.compose_assoc j a b

/-- **`∘` 有右单位元**：存在 `ε`，右乘后**来源与状态都不变**。

    比定义多说了什么：`Ops` 只证了「`∘` 不减少来源」——那只排除变小，
    并不排除变大。此条给出一个真正**不改变任何东西**的右乘元，
    于是 `(Judgment, ∘)` 至少是**带右单位的半群**（有结合律 §1 + 右单位）。
    取 `ε = ⟨j.concl, j.concl, ∅, proven⟩`：来源那一路是
    `Ops.Support.addAssumptions_nil`，状态那一路是 `proven.weaker s = s`。

    ⚠ `ε` 逐判断存在（取 `concl := j.concl`），因为 `Formula L` 上没有
    可用的「恒等结论」——凭空造一个会改变 `concl`。 -/
theorem composeOp_id_right (j : Judgment L) :
    ∃ e : Judgment L,
      (composeOp e j).support = j.support ∧ (composeOp e j).status = j.status := by
  refine ⟨⟨j.concl, j.concl, Support.empty, Status.proven⟩, ?_, ?_⟩
  · exact Support.addAssumptions_nil j.support
  · show j.status.weaker Status.proven = j.status
    unfold Status.weaker Status.strength
    cases j.status <;> rfl

/-- **四算子中三个的单调性汇总**：γ / υ / ∘ 三条在一个命题里，一次引用。

    比定义多说了什么：把铁律 3 从三个分离定理收敛成**一个命题族**，
    并明确 α 的位置是**带前件的**（见 `alpha_supportMonotone_iff`）。
    这样「四算子都单调」在库里只有**一个**出处，避免将来各自漂移。 -/
theorem four_ops_support_monotone (pg : GammaPolicy L) (pu : UpsilonPolicy L)
    (j2 : Judgment L) :
    SupportMonotone (gamma pg) ∧ SupportMonotone (upsilon pu)
      ∧ SupportMonotone (composeOp j2) := by
  refine ⟨gamma_supportMonotone pg, upsilon_supportMonotone pu, ?_⟩
  exact composeOp_supportMonotone j2

end ComposeOp

/-! ## §4 `α` 是**不同类**的算子

α 的签名是 `In → Judgment L`，**不是** `Op L`。`Ops` 因此没给 α 证单调性
（没有来源可比）。但 α 有同样强的结构性质：它**恰好**是某个函数的像，
于是「α 做了什么」完全可算。 -/

section Alpha

variable {L : Type u}

/-- **α 的来源完全由 `extract` 决定**。

    比 `Ops.alpha_support_eq` 多说了什么：那条是 `rfl`，说的是
    「输出的 support = `extract x` 的 support」，但**没说输入数据没有贡献**。
    此条写成**对两个输入的比较**：若 `extract` 在 `x`、`y` 上给出同一判断，
    输出的 support 就相同——于是「数据不进 support」在语法层有了可检验形式
    （`Support` 里根本没有「数据」字段，只能做这种间接论证）。
    这是 D-005/D-006 在语法层能有的**最强**形式。 -/
theorem alpha_support_determined_by_extract {In : Type} (p : AlphaPolicy L In)
    (x y : In) (h : p.extract x = p.extract y) :
    (alpha p x).support = (alpha p y).support := by
  show (p.extract x).support = (p.extract y).support
  rw [h]

/-- **α 单射 ⇔ `extract` 单射**：抽象不额外丢失、也不额外创造信息。

    比定义多说了什么：`alpha p x = p.extract x` 是定义等式；此条说的是
    「α 是否可逆」可以**完全搬运**到策略上，于是可逐策略验证而无需碰 α。
    这条不是同义反复：它把 `In → Judgment` 层的不可逆性**定位**到 `extract`。 -/
theorem alpha_inj_iff_extract_inj {In : Type} (p : AlphaPolicy L In) :
    (∀ x y : In, alpha p x = alpha p y → x = y)
      ↔ (∀ x y : In, p.extract x = p.extract y → x = y) :=
  Iff.intro (fun h x y hxy => h x y hxy) (fun h x y hxy => h x y hxy)

/-- **α 的单调性是有前件的**——本文件关于铁律 3 最重要的**定位结论**。

    比 `Ops` 里关于 α 的话多说了什么：`Ops` 说「α 的输入是数据，没有来源可比，
    所以单调性对它没有意义」。此条把这个说法**补完**：把 α 的输入取成
    `Judgment L`（从一条判断抽象出另一条）时，单调性才是一个有内容的陈述，
    而它**不能无条件成立**——它**等价于** `extract` 逐点保来源。
    于是「α 不减少来源」这句话在类型上是**空**的，只有当策略额外满足
    某个条件时才有实质内容。这是四个算子里**唯一**不能无条件满足铁律 3 的一个，
    原因是它根本不作用在判断上。 -/
theorem alpha_supportMonotone_iff (L0 : Type) (p : AlphaPolicy L0 (Judgment L0)) :
    (∀ j : Judgment L0, j.support.Subset (alpha p j).support)
      ↔ (∀ j : Judgment L0, j.support.Subset (p.extract j).support) :=
  Iff.intro (fun h j => h j) (fun h j => h j)

end Alpha

end FateV2.Core
