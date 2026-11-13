import FateWorld.Legacy.T112UnaryClosure

/-! ===========================================================================
  `Fate/T112Candidates` —— **T1.12 · 步骤 1–2：五个候选命题的探针测试**

  # 本文件的用途

  对 5 个「看似 FCA 特有」的候选命题，**逐条**做**可机器验证**的判定：

  | 判定 | 机器形式 |
  |---|---|
  | **不是 FCA 特有** | 该命题对**任意** `ClosureOperator`（或至少对 `Unary` 单底集情形）**逐字成立**。直接给出证明项。 |
  | **是 FCA 特有** | 该命题的陈述**必须**含两个不同的类型 `G`、`M`（「两个底集」）。给出**机器证据**：单底集版本不存在/是空真/坍缩。 |

  ## ⚠ 判定标准（本轮自定的唯一标准，避免前几轮的含混）

  > **FCA 特有 :⟺ 命题的陈述中出现两个（可能不同的）底集 `G` 与 `M`，
  > 且去掉其中任何一个都会使命题失去内容（或变得不可陈述）。**

  「泛函化」= 把 `G = M = γ` 代入（`Unary` 框架），看命题是否退化。
  **判据：泛函化后仍非平凡 ⟹ 不是 FCA 特有。**
================================================================================ -/

namespace Fate

open Set

/-! ## 候选 1：**概念格是完备格**

> `𝔅(𝕂) = Concept G M I` 是完备格（任意交、任意并存在）。

**探针**：对**任意** `ClosureOperator c : ClosureOperator α`，其**不动点子类型**
`{a // c a = a}` 是完备格（交 = 逐点闭包交，并 = 闭包并）。

⚠ 注意：这对**任意** `α`、**任意** `c` 成立 —— 不需要两个底集。
下面直接给出对任意 `ClosureOperator` 的**实例**证明，**不借用 FCA**。 -/

namespace C1

/-- ⭐ **候选 1 的判定：不是 FCA 特有。**

对**任意完备格** `L` 与**任意**闭包算子 `c : ClosureOperator L`，
闭集（不动点）子类型 `c.Closeds = {x // c.IsClosed x}` 是完备格——
由 `ClosureOperator.gi : GaloisInsertion c.toCloseds Subtype.val` 与
`GaloisInsertion.liftCompleteLattice` 直接给出。

⚠ 这里 `L` **只有一个**：`L` 取 `𝒫(G)` 就是「外延闭集格」，
取 `𝒫(M)` 就是「内涵闭集格」。**两句话各自都是同一句话。**
**⟹ 概念格完备性 = 任意完备格上闭包算子不动点集的完备性。** -/
theorem fix_completeLattice (L : Type*) [CompleteLattice L] (c : ClosureOperator L) :
    Nonempty (CompleteLattice c.Closeds) :=
  ⟨GaloisInsertion.liftCompleteLattice c.gi⟩

/-- ⭐⭐ **候选 1 的判定（加强）：连 `CompleteLattice` 都不需要。**

只要 `L` 是 `Lattice`（甚至 `PartialOrder`+`BoundedOrder`），闭集子类型就继承同一套结构。
**⟹ 「完备性」完全来自 `L`，与「关系」无关，更与「两个底集」无关。** -/
theorem fix_lattice (L : Type*) [Lattice L] (c : ClosureOperator L) :
    Nonempty (Lattice c.Closeds) :=
  ⟨GaloisInsertion.liftLattice c.gi⟩

end C1

/-! ## 候选 2：**外延 ↔ 内涵 反序同构**

> `Ext(𝕂) ≃o (Int(𝕂))ᵒᵈ`（`ExtentSet K ≃o (IntentSet K)ᵒᵈ`）。

**探针**：在 `Unary` 框架（单一底集 `γ`、关系 `r : γ → γ → Prop`）里，
`Extent` 与 `Intent` **是同一类型上的谓词**。故「外延 ≃o 内涵ᵒᵈ」若要成立，
就等于说「闭集格**自对偶**」——这是一个**强得多**的要求。

**机器证据**：下面证明——在单底集 + 对称关系的情形，
`IsExtent` 与 `IsIntent` 是**同一个谓词**（`T112Unary.isExtent_iff_isIntent_of_symm`），
故「反序同构」的内容**坍缩为 `s ↦ s` 的信息损失为零**：`Extent ≃o Intent` 就是
`(Subtype (IsExtent r)) ≃o (Subtype (IsExtent r))`，**恒等即可**。

⟹ **候选 2 在单底集里退化为仅「恒等」，不带任何反序信息**——
但**反向**地，在真正的 FCA 里 `polar` 给出**真正的反序**。
故候选 2 的**反序性**确实**来自两个底集**。

⚠ 但要注意：这只能说明「反序性来自两个底集」，**不能**说明「反序同构本身是 FCA 特有」——
一般闭包算子 `c` 的闭集格可能**恰好**自对偶，也可能不自对偶（见 `T112FCASpecific` 的 `clThree`）。
「自对偶」是**偶然性质**，不是普遍性质。**FCA 特有性在于「总是反序同构」，**
即 `polar` 提供了**无条件的**对偶。 -/

namespace C2

open T112Unary

/-- ⭐ **候选 2 的探针：单底集 + 对称关系 ⟹ Extent 与 Intent 是同一谓词。**

**⟹ 「外延 ↔ 内涵」的区分**在这一情形**完全消失**；
反序同构退化为 `s ↦ s`（同类上的恒等）。

⚠ 这**不是**在说「候选 2 是假的」，而是在说明**它的内容是两侧之间的对称**。 -/
theorem unary_extent_intent_collapse {γ : Type*} {r : γ → γ → Prop} (hr : Std.Symm r) :
    ∀ s : Set γ, Order.IsExtent r s ↔ Order.IsIntent r s :=
  fun s => isExtent_iff_isIntent_of_symm hr s

/-- ⭐ **候选 2 的探针（非对称 `r` 的情形）：也能坍缩**——
把 `r` 换成 `swap r`，则 `Extent r = Intent (swap r)`。

**这是关键观察**：`upperPolar r = lowerPolar (swap r)`（`upperPolar_swap`）。
⟹ **只要允许换关系，「外延」与「内涵」就互换**；
⟹ 所谓「两侧」在**关系可以取转置**时**也是同一份结构**。

⚠ **这条是对候选 2 的最强反击**：反序同构 `Ext ≃o Intᵒᵈ` 与
「转置关系的 Extent 就是 Intent」是**同一件事**，
而**转置关系仍是一个关系、仍只需一个底集对**——
**故候选 2 的「两侧」可以被压回「一个关系的两个方向」，即一个底集对。** -/
theorem extent_eq_intent_swap {γ : Type*} (r : γ → γ → Prop) (s : Set γ) :
    Order.IsExtent r s ↔ Order.IsIntent (Function.swap r) s := by
  rw [Order.isExtent_iff, Order.isIntent_iff, upperPolar_swap, lowerPolar_swap]

end C2

/-! ## 候选 3：**属性闭包与对象闭包的对偶**

> `polarUp (polarDown A) = A`` 、`polarDown (polarUp B) = B'`（`''` 运算的两侧）。

**探针**：`polarUp`/`polarDown` 是**任意关系** `r : α → β → Prop` 上的算子，
**不依赖 FCA**（Mathlib 的 `upperPolar`/`lowerPolar` 就在 `Mathlib.Order.Concept` 里，
对任意 `α β`）。故候选 3 的**代数内容**（反单调 + 构成 Galois 连接 + 双极幂等）
对**任意二元关系**成立。

**⟹ 候选 3 不是「FCA 特有」的**——它属于「任意二元关系」层，
而 FCA 只是「把 `α` 叫对象集、`β` 叫属性集」的命名。
下面把这一点**机器化**：对任意关系陈述双极幂等，**不使用 `FormalCtx`**。 -/

namespace C3

/-- ⭐ **候选 3 的判定：不是 FCA 特有（它对任意二元关系都成立）。**

`Swift` 版陈述：对**任意**类型 `α β` 与**任意** `r : α → β → Prop`，
双极幂等成立。下面用 `Fate` 的记法**重述一遍**（`K.Irel` 只是一个关系的别名）。 -/
theorem bipolar_idem_any_relation {α β : Type*} (r : α → β → Prop) (s : Set α) :
    upperPolar r (lowerPolar r (upperPolar r s)) = upperPolar r s :=
  upperPolar_lowerPolar_upperPolar r s

/-- ⭐ **同一条，用 FCA 命名**：与上一条**同一证明项**（`rfl` 级替换）。 -/
theorem bipolar_idem_fca_named (K : FormalCtx) (s : Set K.GFCA) :
    K.polarUp (K.polarDown (K.polarUp s)) = K.polarUp s :=
  bipolar_idem_any_relation K.Irel s

end C3

/-! ## 候选 4：**每个概念都由外延唯一确定 / 概念格嵌入 `𝒫(G)` 与 `𝒫(M)`**

> 概念 ⟹ 由外延唯一确定（`extent_injective`），也由内涵唯一确定（`intent_injective`）；
> 且 `Ext(𝕂) ≅ Int(𝕂)`（**不反序**的同构）。

**探针**：这条在 `Unary` 框架里**完全成立**（同一类型上）。
更强的：对**任意**闭包算子 `c`，不动点 `{a // c a = a}` 由 `a` 唯一确定，这**是 `Subtype` 的定义**。
⟹ 「由外延唯一确定」**不是 FCA 特有**（是 `Subtype` 的平凡性）。

⚠ 但「**同时**由外延和内涵唯一确定」是 FCA 的双侧事实。下面测它的**泛函化**：
在单底集里两侧是同一类型，故「同时」退化为「一次」。
**⟹ 候选 4 的双侧版本在单底集里是空真（vacuously 只测一次）。** -/

namespace C4

/-- ⭐ **候选 4 的判定（上）：不是 FCA 特有。**

任意闭包算子的不动点由代表元唯一确定——这是 `Subtype.ext`。 -/
theorem fix_determined_by_rep {α : Type*} [PartialOrder α] (c : ClosureOperator α)
    (p q : { a : α // c a = a }) (h : p.1 = q.1) : p = q :=
  Subtype.ext h

/-- ⭐ **候选 4 的判定（下）：双侧版本在单底集里会「自吞」。**

在 `Unary` 框架里 `Extent` 与 `Intent` 是同一类型上的两个谓词，
故「由外延唯一确定 **且** 由内涵唯一确定」退化成**同一条** `Subtype.ext`。
**⟹ 双侧性在单底集里不可见；它需要 `G ≠ M`。** -/
theorem unary_extent_intent_same_substrate {γ : Type*} (r : γ → γ → Prop) :
    -- 两个「侧」都是 `Set γ` 上的 `Subtype`：**底集相同**
    (∀ s : Set γ, Order.IsExtent r s ↔ s ∈ (Set.range (lowerPolar r) : Set (Set γ))) ∧
    (∀ s : Set γ, Order.IsIntent r s ↔ s ∈ (Set.range (upperPolar r) : Set (Set γ))) := by
  have hExt : ∀ s : Set γ, Order.IsExtent r s ↔ s ∈ (Set.range (lowerPolar r) : Set (Set γ)) :=
    fun s => ⟨fun h => ⟨_, h.eq⟩, fun h => Order.isExtent_iff.2 (h.elim fun t ht => ht ▸ lowerPolar_upperPolar_lowerPolar r t)⟩
  refine ⟨hExt, fun s => ?_⟩
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩; exact Order.isIntent_upperPolar

end C4

/-! ## 候选 5：**概念格的完全分配性 / 由不可约元生成（Dedekind–MacNeille 表示）**

> 概念格是**完全分配的**（并不可约元与交不可约元的对偶同构），
> 且每个概念都是「由对象生成的」概念的并（`ofObjects` 稠密性）。

**探针**：这是 **Dedekind–MacNeille 完备化** 的性质。
Dedekind–MacNeille 完备化的**输入就是一个偏序集**（单底集！），
它不会产生「两个底集」。

⟹ **候选 5 不是 FCA 特有**：`polarUp`/`polarDown` 给的是 `(𝒫(G))` 与 `(𝒫(M))` 之间的
**一对**完备化，而**任何一个**都已经是完备化；再来第二个只是重复。
换言之：**概念格 ≅ `𝒫(M)` 的闭包算子不动点格**，是一个 **Dedekind–MacNeille 完备化**，
**单侧**就能定义。

下面把这个坍缩**机器化**：在「单侧」把 `polarDown ∘ polarUp` 当闭包算子，
`Ext(𝕂)` 就是它的不动点集——**不需要 `𝒫(M)` 那一侧**。 -/

namespace C5

open T112Unary

/-- ⭐ **候选 5 的判定：不是 FCA 特有（外延集 = 单侧闭包算子的不动点集）。**

`ExtentSet K` 就是 `extentClosure K.Irel` 的不动点集。**`𝒫(M)` 一侧完全没出现**。 -/
theorem extent_eq_fix_of_extentClosure (K : FormalCtx) :
    (fun s : Set K.GFCA => s ∈ (Set.range (K.polarDown : Set K.MFCA → Set K.GFCA))) =
      (fun s : Set K.GFCA => extentClosure K.Irel s = s) := by
  funext s
  show Order.IsExtent K.Irel s = (extentClosure K.Irel s = s)
  rw [Order.isExtent_iff]
  rfl

/-- ⭐ **同一条，用 `uClosure` 形式**：`IsExtent r` 就是 `uClosure r` 的不动点。 -/
theorem isExtent_iff_uClosure_fix {γ : Type*} (r : γ → γ → Prop) (s : Set γ) :
    Order.IsExtent r s ↔ uClosure r s = s :=
  Order.isExtent_iff

end C5

end Fate
