import FateWorld.FateV2.Rules.T112FCATheorems
/-!
  # Rules · T112Exactly

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T112Exactly.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T112FCATheorems
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/T112Exactly` —— **T1.12 · 第 5 次尝试：把问题彻底答完**

  # 本文件回答

  > **「FCA 到底有没有一般闭包算子没有的定理？」**

  ## §1 结论（先说）

  > **没有。而且比「没有」更强：FCA 与「幂集上的闭包算子」是**外延相同**的（coextensive）。**

  这不是「前几次尝试没找到」，而是**一个可以机器验证的完全刻画**：

  $$\boxed{\;\text{每个幂集上的闭包算子都是某个形式背景的 } \mathrm{extentClosure}.\;}$$

  见 §2 的 `every_clo_on_powerset_is_extentClosure`：给定 `c : ClosureOperator (Set γ)`，
  取属性集 `M := { t : Set γ // c t = t }`（**闭集本身**），
  关系 `cloRel c g t := g ∈ t`，则 `extentClosure (cloRel c) = c`。
  （这是 FCA 教科书里的「闭集背景」/ *clarified context of closed sets*，
  本文件把它作为**判据**用，而不是作为新结果。）

  **⟹ 任何只提到「`extentClosure` 不动点」的 FCA 命题，
  都是「幂集上某个闭包算子」的命题。「两个底集」只是给同一个闭包算子换了个写法。**

  ## §2 与 §3

  * **§2**：上述完全刻画（核心定理，零 `sorry`）。
  * **§3**：用它**审计**前几轮声称「FCA 特有」的定理——逐条搬回单闭包算子。

  ## §4 五候选测试结果汇总

  | # | 候选 | 判定 | 机器依据 |
  |---|---|---|---|
  | C1 | 概念格完备 | ❌ 非特有 | `C1.fix_completeLattice`（任意完备格 + 任意闭包算子）|
  | C2 | 外延–内涵反序同构 | ❌ 非特有 | `C2.extent_eq_intent_swap`：`Extent r = Intent (swap r)`；一个关系的两个方向 |
  | C3 | 双极闭包对偶 | ❌ 非特有 | `C3.bipolar_idem_any_relation`：任意二元关系 |
  | C4 | 概念由外延唯一确定 | ❌ 非特有 | `C4.fix_determined_by_rep`：`Subtype.ext` |
  | C5 | 完全分配 / Dedekind–MacNeille | ❌ 非特有 | `C5.extent_eq_fix_of_extentClosure`：= 单侧闭包的不动点 |

  **5/5 全部非特有。** 本轮新增的 §2 解释了**为什么必然是 5/5**。

  ## §5 对前几轮「已确认 FCA 特有」的**撤回**

  | 前几轮的主张 | 出处 | 本轮判定 |
  |---|---|---|
  | 定理 A：`G` 单点 ⟹ 概念数 ≤ 2 | `T112FCATheorems.ThmA` | ❌ **撤回**。已搬回 `ClosureOperator (Set Unit)`（§3.1）|
  | 定理 D：属性不决定对象 | `T112FCATheorems.ThmD` | ❌ **撤回**。已搬回单个 `ClosureOperator (Set (Fin 2))`（§3.2）|
  | §1–§3 of `T112FCASpecific2` | 上轮 | ⚠ **降级**：陈述含双底集，但数学内容 = 一般闭包论（§3.3）|

  ⚠ **这是我本轮必须承认的**：上轮我说「3 条通过严格判据」，
  **判据本身是错的**——「陈述里有两个底集」不是「数学内容不同」的充分条件。
  真正的判据是 §2。

  ## §6 元结论

  > **「FCA 特有性」的**数学**本质是零。**
  >
  > 「FCA 看起来特有」的**唯一**来源是：FCA 把注意力限制在
  > **两类特定形状**的闭包算子上（「由一个两级关系诱导」的），
  > 但 §2 证明这类闭包算子**恰好就是全部**幂集闭包算子。
  >
  > ⟹ **没有「两个底集 vs 一个底集」的内容差别；
  > 只有「`Set G → Set M` 的写法 vs `Set γ → Set γ` 的写法」的**记法**差别。**
================================================================================ -/

namespace FateV2.Rules

open FateV2.Modeling
open Set Order

universe u

/-! ===========================================================================
  ## §2  ⭐⭐⭐ 核心定理：FCA 与「幂集闭包算子」外延相同
  ======================================================================== -/

/-- **闭集背景的关联关系**：`g` 与闭集 `t` 相关，当且仅当 `g ∈ t`。 -/
def cloRel {γ : Type*} (c : ClosureOperator (Set γ)) : γ → { t : Set γ // c t = t } → Prop :=
  fun g t => g ∈ (t : Set γ)

/-- ⭐⭐⭐ **完全刻画（主定理）**：任意幂集闭包算子 `c`，
其 `extentClosure` 恰是 `c` 自己，**来自由闭集构成的背景**。

证明：`polarUp s` = 「包含 `s` 的所有闭集」，故 `polarDown (polarUp s)` = 它们的交
= 最小的包含 `s` 的闭集 = `c s`。

⚠ 这一步用到 `c s` 自身是闭集（`c.idempotent`）且 `s ⊆ c s`（`c.le_closure`），
再对其它闭集 `t ⊇ s` 用 `c.monotone` 得 `c s ⊆ t`。 -/
theorem extentClosure_canonical {γ : Type*} (c : ClosureOperator (Set γ)) (s : Set γ) :
    lowerPolar (cloRel c) (upperPolar (cloRel c) s) = c s := by
  ext g
  show (∀ t : { t : Set γ // c t = t }, t ∈ upperPolar (cloRel c) s → g ∈ (↑t : Set γ)) ↔ g ∈ c s
  constructor
  · intro h
    apply h ⟨c s, c.idempotent s⟩
    show ∀ a ∈ s, a ∈ (c s : Set γ)
    intro a ha
    exact Set.mem_of_subset_of_mem (c.le_closure s) ha
  · intro hg t ht
    have hst : ∀ a, a ∈ s → a ∈ (↑t : Set γ) := ht
    have hcs : c s ⊆ (↑t : Set γ) := by
      rw [← t.2]
      exact c.monotone hst
    exact hcs hg

/-- ⭐⭐⭐ **主定理**：**每个**幂集上的闭包算子都是某个形式背景的 `extentClosure`。

**⟹ FCA 的「两个底集」不带来任何新的闭包论内容**：
`{Nested` 底集 `M` 可以恒取为「闭集本身」。 -/
theorem every_clo_on_powerset_is_extentClosure {γ : Type u} (c : ClosureOperator (Set γ)) :
    ∃ (M : Type u) (r : γ → M → Prop), ∀ s : Set γ, extentClosure r s = c s :=
  ⟨{ t : Set γ // c t = t }, cloRel c, extentClosure_canonical c⟩

/-- ⭐⭐ **推论（外延层面）**：闭集背景的**外延**恰是 `c` 的闭集。

**⟹ 「概念格 = 某闭包算子的不动点格」是**全部**内容，与「是否来自 FCA」无关。** -/
theorem canonical_context_extents {γ : Type u} (c : ClosureOperator (Set γ)) (s : Set γ) :
    Order.IsExtent (cloRel c) s ↔ c s = s := by
  rw [Order.isExtent_iff]
  show lowerPolar (cloRel c) (upperPolar (cloRel c) s) = s ↔ c s = s
  rw [extentClosure_canonical]

/-! ===========================================================================
  ## §3  用 §2 审计前几轮的「FCA 特有」主张
  ======================================================================== -/

/-! ### §3.1  ⚠ 撤回定理 A（`G` 单点 ⟹ 概念数 ≤ 2）

`T112FCATheorems.ThmA.single_object_at_most_two` 说：`K.GFCA` 单点 ⟹ 概念至多 2 个。

**但这条完全不需要 FCA**：`G` 单点 ⟹ `𝒫(G) = {∅, univ}` ⟹
**任意** `c : ClosureOperator (Set G)` 的闭集也至多 2 个。
下面在 `ClosureOperator (Set Unit)` 上**逐字**证明同一结论。 -/

namespace AuditA

/-- ⚠ **定理 A 的撤回证据**：`Set Unit` 上**任意**闭包算子的不动点至多 2 个。

**⟹ 「`G` 单点是 `Unit`」这个假设的全部内容是「单点上只有 2 个子集」，
而这是 `Set` 的性质，不是 FCA 的性质。** -/
theorem clo_on_unit_at_most_two (c : ClosureOperator (Set Unit)) :
    ¬ ∃ a b c' : c.Closeds, a ≠ b ∧ b ≠ c' ∧ a ≠ c' := by
  rintro ⟨a, b, c', h1, h2, h3⟩
  -- `Set Unit` 只有 `∅` 和 `univ` 两个元素：故任意两者相等或一空一满。
  have key : ∀ s : Set Unit, s = ∅ ∨ s = univ := by
    intro s; rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · exact Or.inl h
    · exact Or.inr (eq_univ_iff_forall.2 fun y => by rw [Subsingleton.elim y x]; exact hx)
  have hne : (∅ : Set Unit) ≠ (univ : Set Unit) := by
    intro hcontra
    have hmem : (() : Unit) ∈ (univ : Set Unit) := Set.mem_univ ()
    rw [← hcontra] at hmem
    exact hmem
  -- 鸽巢：三个元素、两个可能的取值，且 `∅ ≠ univ` 意味着「同值 ⟺ 相等」。
  have pigeon : ∀ s t : Set Unit, s ≠ (∅ : Set Unit) → t ≠ (∅ : Set Unit) → s = t := by
    intro s t hs ht
    rcases key s with h | h
    · exact absurd h hs
    · rcases key t with h' | h'
      · exact absurd h' ht
      · exact h.trans h'.symm
  by_cases ha0 : a.1 = ∅
  · by_cases hb0 : b.1 = ∅
    · exact h1 (Subtype.ext (ha0.trans hb0.symm))
    · by_cases hc0 : c'.1 = ∅
      · exact h3 (Subtype.ext (ha0.trans hc0.symm))
      · exact h2 (Subtype.ext (pigeon b.1 c'.1 hb0 hc0))
  · by_cases hb0 : b.1 = ∅
    · by_cases hc0 : c'.1 = ∅
      · exact h2 (Subtype.ext (hb0.trans hc0.symm))
      · exact h3 (Subtype.ext (pigeon a.1 c'.1 ha0 hc0))
    · exact h1 (Subtype.ext (pigeon a.1 b.1 ha0 hb0))

end AuditA

/-! ### §3.2  ⚠ 撤回定理 D（「属性不决定对象」）

`T112FCATheorems.ThmD.fca_object_not_determined_by_attrs` 说：
存在 `g ≠ g'` 使 `polarUp {g} = polarUp {g'}`。

**但这条的实质是**「某个闭包算子在单点上不单射」——
取 `c := ` 常值 `univ` 的闭包算子，`c {0} = univ = c {1}` 而 `0 ≠ 1`。
**完全不需要第二个底集。** -/

namespace AuditD

/-- ⚠ **定理 D 的撤回证据**：单个 `ClosureOperator (Set (Fin 2))` 即在单点上不单射。

**⟹ 「两个底集丢信息」是假的；「某些闭包算子在单点上不单射」才是真的，
而后者与底集个数无关。** -/
theorem clo_not_injective_on_singletons :
    ∃ (c : ClosureOperator (Set (Fin 2))) (g g' : Fin 2),
      g ≠ g' ∧ c ({g} : Set (Fin 2)) = c {g'} := by
  refine ⟨ClosureOperator.mk' (fun _ => (univ : Set (Fin 2))) ?_ ?_ ?_, 0, 1, ?_, rfl⟩
  · intro s t _ x _; exact Set.mem_univ x
  · intro x; exact Set.subset_univ x
  · intro x; exact Set.subset_univ _
  · exact fun h => absurd (congrArg Fin.val h) (by decide)

end AuditD

/-! ### §3.3  ⚠ 降级上一轮 `T112FCASpecific2` 的 §1–§3

上轮（第 3 次尝试）我声称三条定理「通过严格判据」：

| 定理 | 上轮的判据 | 本轮判定 |
|---|---|---|
| `polarUp_iff_adjoint_of_antitone` | 「`f` 跨两个类型」 | 内容 = `GaloisConnection` 的标准唯一性 |
| `conceptSwapEquiv` | 「交换了两个类型」 | 内容 = 「转置关系」的换名重述 |
| `polarUp_injective_on_extents` | 「需要 `polarDown` 回到 `G` 侧」 | 内容 = 闭包算子在不动点上单射 |

**判据错在哪里**：我用「陈述里出现两个类型」当**充分条件**。
但 §2 表明：**任何**双底集陈述都可以通过 `M := {闭集}` 化归为单闭包算子陈述。
**故「出现两个类型」既不充分也不必要。**

下面对第三条给出**直接**的化归证据（它是最像「需要两侧」的）。 -/

namespace AuditC

/-- ⚠ **`polarUp` 在外延上单射 = 闭包算子在不动点上单射**

右式对**任意** `ClosureOperator` 成立（`Subtype.ext`），**没有两个底集**。
故左式的「双底集外观」不携带内容。 -/
theorem extent_singleqn_is_clo_singleqn {α : Type*} [PartialOrder α]
    (c : ClosureOperator α) {a b : α} (ha : c a = a) (hb : c b = b) (h : c a = c b) :
    a = b := by
  rw [ha, hb] at h
  exact h

end AuditC

/-! ===========================================================================
  ## §4  ⭐⭐⭐ 元结论（最终版）
  ======================================================================== -/

/-!
### §4.1  结论

> **「FCA 特有的定理」不存在——不是因为没找到，而是因为可以证明不存在。**

主定理 `every_clo_on_powerset_is_extentClosure` 给出的化归是**双向**的：

* 每个 `FormalCtx` 给一个 `ClosureOperator (Set G)`（`extentClosure K.Irel`）
* 每个 `ClosureOperator (Set γ)` 来自某个 `FormalCtx`（`cloRel c`）

**两个类完全重合。** 故：

$$ \{\text{FCA 定理}\} \;=\; \{\text{幂集闭包算子定理}\} $$

特别地，**没有**「FCA 有而闭包算子没有」的定理。

### §4.2  「两个底集」到底是什么

「两个底集」**不是数学结构**，是**表示方式**：

* FCA 的数据是 `(G, M, I)` —— 三个对象；
* 闭包算子的数据是 `c : Set G → Set G` —— 一个对象；
* 化归 `(G, M, I) ↦ extentClosure I` **多对一**（不同的 `(M, I)` 给同一个 `c`）；
* 反向 `c ↦ (G, {闭集}, ∈)` 给出**规范代表元**。

⟹ 「两底集」= **同一个闭包算子的非规范表示**。
    这也是为什么 FCA 里那么多「对偶」陈述：**它们是对「非规范表示」的自由度
    做文章**，而不是对闭包算子本身。

### §4.3  为什么前几次都「找到了」FCA 特有定理

前几次（含上一轮）的判据都是**语法的**：「陈述里有两个类型 ⟹ 特有」。
§2 证明这个判据**永假**：任何双底集陈述经 `M := {闭集}` 都能化归。

⟹ **前几次的结果不是「误判了个别定理」，而是判据方向错了。**

### §4.4  T1.12 的最终回答

> **T1.12（二次商 ≃ 闭包不动点）不含 FCA 内容。**
>
> 这个结论在 `Fate/T112SecondQuotient.t112_holds_for_any_closureOperator` 里
> **已经机器证明**，且 §2 说明了它**不可能**有 FCA 内容。
>
> 「FCA 版 T1.12」的唯一新增是**写法**：把 `ClosureOperator (Set γ)`
> 写成 `FormalCtx (G, M, I)` 的 `Ext ≃ Int`。**数学上是同一句话。**
-/

end FateV2.Rules
/-! ===========================================================================
  `Fate/T112Exactly` —— **R11 追加段：T112 系列真实接线**

  本段（`namespace FateV2.Rules.R11T112`）**只做组合**：把本文件已导入的
  `T112UnaryClosure` / `T112Candidates` / `T112FCAConnection` /
  `T112SecondQuotient` / `T112FCAPolar` / `T112FCATheorems` 中的既有定理
  两两/三三组合，产生**在任一单模块中都不存在的接口**。

  ⚠ 本段**不新增假设**、**不引入任何新定义**、**零 sorry / 零 axiom**。
  ⚠ 未导入的 `T112PairProbe` / `T112FCASpecific2` / `T112FCASpecific`
     不在本段引用范围内（Lean 要求 import 位于文件头，本段按纪律只追加）。

  | # | 定理 | 组合来源 |
  |---|---|---|
  | 1 | `closure_intentClosure_fix` | `closure_eq_intentClosure` + `closureOp.idempotent` |
  | 2 | `isIntent_iff_closure_fix` | `polarUp_polarDown_eq_of_isIntent` + `closure_isIntent` |
  | 3 | `closure_range_isIntent` | `range_closure_eq_intents` |
  | 4 | `mk_eq_iff_closure_eq` | `t112_injective_iff` |
  | 5 | `class_of_closure_eq` | `closureOp.idempotent` + `attrsEquiv_self_closure` |
  | 6 | `clo_extents_eq_closed` | `every_clo_on_powerset_is_extentClosure` + `canonical_context_extents` |
  | 7 | `t112_for_canonical` | `t112_holds_for_any_closureOperator` + `canonical_context_extents` |
  | 8 | `polar_antitone_closure_bipolar` | `polar_pair_antitone` + `fca_closure_is_bipolar` |
  | 9 | `adjunction_and_closure` | `polar_adjunction` + `fca_closure_is_bipolar` |
  | 10 | `unary_extent_is_uClosure_fix` | `isExtent_iff_lowerPolar_lowerPolar` + `isExtent_iff_uClosure_fix` |
================================================================================ -/

namespace FateV2.Rules
open Set Order

namespace R11T112

universe u

/-! ## §R11.1  FCA 闭包与 `intentClosure` 的接线 -/

/-- **(R11-1)** FCA 闭包 `T112.closure K A` 是 `intentClosure K.Irel` 的**不动点**。

组合：`closure_eq_intentClosure`（把 `closure` 改写成 `intentClosure`）
+ `ClosureOperator.idempotent`（闭包算子的幂等性）。
**这是本文件首次把「闭包算子 API」直接作用到 `T112.closure` 上。** -/
theorem closure_intentClosure_fix (K : FormalCtx) (A : Set K.MFCA) :
    (intentClosure K.Irel) (T112.closure K A) = T112.closure K A := by
  rw [← FateV2.Rules.T112.closure_eq_intentClosure]
  exact (T112.closureOp K).idempotent A

/-- **(R11-2)** `A` 是内涵 ⟺ `A` 是 FCA 闭包的不动点。

**两个方向来自不同模块**：`→` 用 `T112FCAPolar` 的
`polarUp_polarDown_eq_of_isIntent`（经 `closure_eq_intentClosure` 改写），
`←` 用 `T112SecondQuotient` 的 `closure_isIntent`。
**这条双向等价把「内涵」与「闭包不动点」两个概念在本文件中焊死。** -/
theorem isIntent_iff_closure_fix (K : FormalCtx) (A : Set K.MFCA) :
    Order.IsIntent K.Irel A ↔ T112.closure K A = A := by
  constructor
  · intro hA
    rw [FateV2.Rules.T112.closure_eq_intentClosure]
    exact FormalCtx.polarUp_polarDown_eq_of_isIntent K hA
  · intro hA
    rw [← hA]
    exact FateV2.Rules.T112.closure_isIntent K A

/-- **(R11-3)** `T112.closure K A` 落在 `FateV2.Rules.T112.range_closure_eq_intents` 所刻画的
「某概念的 intent」这一集合中。 -/
theorem closure_range_isIntent (K : FormalCtx) (A : Set K.MFCA) :
    T112.closure K A ∈ { B : Set K.MFCA | ∃ c : ConceptLattice K, c.intent = B } := by
  rw [← FateV2.Rules.T112.range_closure_eq_intents]
  exact mem_image_of_mem _ (mem_univ A)

/-! ## §R11.2  二次商的类与闭包 -/

/-- **(R11-4)** 两个属性集落在同一商类 ⟺ 它们的闭包相等（`Quotient.mk` 形式）。 -/
theorem mk_eq_iff_closure_eq (K : FormalCtx) (A B : Set K.MFCA) :
    Quotient.mk (FateV2.Rules.T112.attrsEquivSetoid K) A = Quotient.mk (FateV2.Rules.T112.attrsEquivSetoid K) B ↔
      T112.closure K A = T112.closure K B :=
  FateV2.Rules.T112.t112_injective_iff K A B

/-- **(R11-5)** `A` 与其闭包同属一类，且两者再闭包后相等（幂等的类内稳定性）。 -/
theorem class_of_closure_eq (K : FormalCtx) (A : Set K.MFCA) :
    T112.closure K A = T112.closure K (T112.closure K A) ∧
      (FateV2.Rules.T112.attrsEquivSetoid K) A (T112.closure K A) :=
  ⟨((T112.closureOp K).idempotent A).symm, FateV2.Rules.T112.attrsEquiv_self_closure K A⟩

/-! ## §R11.3  任意幂集闭包算子 ↔ 规范背景 -/

/-- **(R11-6)** 任意 `c : ClosureOperator (Set γ)` 既有「双层关系」表示，
也有「以闭集为属性集的规范背景」表示，且后者的外延**恰是** `c` 的闭集。

组合 `T112Exactly.every_clo_on_powerset_is_extentClosure`（表示存在性）
与 `T112Exactly.canonical_context_extents`（外延刻画）。 -/
theorem clo_extents_eq_closed {γ : Type u} (c : ClosureOperator (Set γ)) :
    (∃ (M : Type u) (r : γ → M → Prop), ∀ s : Set γ, (extentClosure r) s = c s) ∧
      (∃ (M' : Type u) (r' : γ → M' → Prop),
        ∀ s : Set γ, Order.IsExtent r' s ↔ c s = s) := by
  exact ⟨every_clo_on_powerset_is_extentClosure c,
    ⟨{ t : Set γ // c t = t }, cloRel c, canonical_context_extents c⟩⟩

/-- **(R11-7)** T1.12 的「二次商 ≃ 闭包不动点」对**规范背景**逐字成立，
且该背景的外延恰为闭集。

组合 `T112SecondQuotient.t112_holds_for_any_closureOperator`（对任意偏序集成立）
与 `T112Exactly.canonical_context_extents`。 -/
theorem t112_for_canonical {γ : Type u} (c : ClosureOperator (Set γ)) :
    Nonempty (Quotient (Setoid.ker fun s : Set γ => c s) ≃ { s : Set γ // c s = s }) ∧
      (∀ s : Set γ, Order.IsExtent (cloRel c) s ↔ c s = s) :=
  ⟨FateV2.Rules.T112.t112_holds_for_any_closureOperator (Set γ) c, canonical_context_extents c⟩

/-! ## §R11.4  极算子：反单调、伴随、双极 -/

/-- **(R11-8)** `polarUp`/`polarDown` 同时反单调，且 FCA 闭包是它们的双极复合。 -/
theorem polar_antitone_closure_bipolar (K : FormalCtx) :
    Antitone K.polarUp ∧ Antitone K.polarDown ∧
      ∀ A : Set K.MFCA, T112.closure K A = K.polarUp (K.polarDown A) :=
  ⟨(FateV2.Rules.T112.polar_pair_antitone K).1, (FateV2.Rules.T112.polar_pair_antitone K).2,
    FateV2.Rules.T112.fca_closure_is_bipolar K⟩

/-- **(R11-9)** 伴随律 `B ⊆ A' ↔ A ⊆ B'` 与「闭包 = 双极复合」同时成立。 -/
theorem adjunction_and_closure (K : FormalCtx) (A : Set K.GFCA) (B : Set K.MFCA) :
    (B ⊆ K.polarUp A ↔ A ⊆ K.polarDown B) ∧ T112.closure K B = K.polarUp (K.polarDown B) :=
  ⟨FateV2.Rules.T112.polar_adjunction K A B, FateV2.Rules.T112.fca_closure_is_bipolar K B⟩

/-! ## §R11.5  单底集坍缩与闭包算子不动点 -/

/-- **(R11-10)** 对称关系下，「外延」既等于 `lowerPolar` 的双重应用，
也等于单底集闭包算子 `uClosure r` 的不动点条件。

组合 `T112UnaryClosure.isExtent_iff_lowerPolar_lowerPolar`
与 `T112Candidates` 的 `isExtent_iff_uClosure_fix`。 -/
theorem unary_extent_is_uClosure_fix {γ : Type*} {r : γ → γ → Prop} (hr : Std.Symm r)
    (s : Set γ) :
    (Order.IsExtent r s ↔ lowerPolar r (lowerPolar r s) = s) ∧
      (Order.IsExtent r s ↔ FateV2.Rules.T112Unary.uClosure r s = s) :=
  ⟨FateV2.Rules.T112Unary.isExtent_iff_lowerPolar_lowerPolar hr s, C5.isExtent_iff_uClosure_fix r s⟩

end R11T112

end FateV2.Rules