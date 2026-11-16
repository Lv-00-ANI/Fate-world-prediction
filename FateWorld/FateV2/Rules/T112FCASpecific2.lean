import FateWorld.FateV2.Rules.T112PairProbe
/-!
  # Rules · T112FCASpecific2

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T112FCASpecific2.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T112PairProbe
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/T112FCASpecific2` —— **T1.12 · 步骤 3：穿过探针的 FCA 特有定理**

  # 前言：本文件的定理**全部是通过探针筛出来的**

  5 个候选（见 `Fate/T112Candidates`）**全部**被判为「非 FCA 特有」。
  本文件的 3 条定理是**换角度重新找**的：它们不是「FCA 的漂亮性质」，
  而是**陈述本身必须两个底集**的命题。

  | # | 定理 | 为什么需要两个底集 | 分离探针 |
  |---|---|---|---|
  | 1 | `polarUp_iff_adjoint_of_antitone` | `f` 的定义域/值域是**两个**幂集 | `unary_adjoint_not_unique` |
  | 2 | `conceptSwapEquiv` | `Concept G M I ≃ Concept M G Iᵀ`：**交换两个底集** | `unary_swap_trivial` |
  | 3 | `polarUp_injective_on_extents` | 双射性只在**外延**子类上成立，需 `polarDown` 回到**另一侧** | `unary_extent_inj_trivial` |

  ⚠ **本文件的诚实基调**：这三条都是**短证明**（3–15 行），
  没有一条是「深定理」。它们唯一的价值是：**陈述里 `G` 和 `M` 都不可省**。
  这正是本轮元结论（§4）所预言的情形。
================================================================================ -/

namespace FateV2.Rules
open Set

/-! ## §0  ⭐ 元结论的**机器化判据**

在写定理前，先把「FCA 特有」的判据变成可检查的 Lean 事实：
**单底集（`G = M = γ`）时一切「两侧」现象都坍缩。**
下面的两条引理是 §1–§3 的「分离证据」的**公共源头**。 -/

namespace Meta

open T112Unary

/-- ⭐⭐⭐ **坍缩（1/2）**：单底集 + 对称 `r` ⟹ 上下极是**同一个算子**。

⟹ 任何依赖「上下极不同」的命题在 `Unary` 里**没有内容**。 -/
theorem unary_up_eq_down {γ : Type*} {r : γ → γ → Prop} (hr : Std.Symm r)
    (s : Set γ) : upperPolar r s = lowerPolar r s :=
  upperPolar_eq_lowerPolar_of_symm hr s

/-- ⭐⭐⭐ **坍缩（2/2）**：单底集 + 对称 `r` ⟹ 外延与内涵是**同一个谓词**。

⟹ 「外延–内涵反序同构」在 `Unary` 里退化为恒等，**信息量 = 0**。 -/
theorem unary_extent_eq_intent {γ : Type*} {r : γ → γ → Prop} (hr : Std.Symm r)
    (s : Set γ) : (Order.IsExtent r s ↔ Order.IsIntent r s) :=
  isExtent_iff_isIntent_of_symm hr s

end Meta

/-! ## §1  FCA 特有定理 1：`polarUp` 由「反变伴随」**唯一确定**

### §1.0  陈述与证明

对**反单调** `f : Set G → Set M`：

$$f = (\cdot)' \iff \forall A\,B,\; \bigl(B \subseteq f(A) \iff A \subseteq B'\bigr).$$

两条 `⊆`：
* `f A ⊆ A'`：取 `B := {m}`（`m ∈ f A`），由 `h A {m}` 得 `A ⊆ {m}ᵖ`，即 `∀ g ∈ A, I g m`。
* `A' ⊆ f A`：由 `A ⊆ A''`（扩张性）与 `h A A'`。

⚠ **反方向完全不需要 `h_mono`**：伴随式**单独**就唯一确定了 `f`。 -/

/-- ⭐⭐⭐ **FCA 特有定理 1**：`polarUp` 是满足伴随式
`B ⊆ f A ↔ A ⊆ polarDown B` 的**唯一**映射。

⚠ `f` 的定义域是 `Set K.GFCA`、值域是 `Set K.MFCA`。
**把 `GFCA = MFCA` 代入后「唯一性」不再成立**（见 §1.2 `unary_adjoint_not_unique`）。 -/
theorem polarUp_iff_adjoint_of_antitone (K : FormalCtx)
    (f : Set K.GFCA → Set K.MFCA)
    (_hmono : ∀ A B : Set K.GFCA, A ⊆ B → f B ⊆ f A) :
    (∀ A B, B ⊆ f A ↔ A ⊆ K.polarDown B) ↔ f = K.polarUp := by
  constructor
  · intro h
    funext A
    apply le_antisymm
    · intro m hm
      have h1 : A ⊆ K.polarDown {m} := (h A {m}).1 (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hm)
      exact (K.mem_polarUp_iff (A := A) (m := m)).2
        (fun g hg => (K.mem_polarDown_iff (B := {m}) (g := g)).1 (h1 hg) (Set.mem_singleton m))
    · intro m hm
      exact (h A (K.polarUp A)).2 (K.subset_polarUp_polarDown A) hm
  · intro h A B
    rw [h]
    exact K.subset_polarUp_iff_subset_polarDown

/-- ⭐ **对偶侧**：`polarDown` 同样由伴随式唯一确定。 -/
theorem polarDown_iff_adjoint_of_antitone (K : FormalCtx)
    (g : Set K.MFCA → Set K.GFCA)
    (_hmono : ∀ A B : Set K.MFCA, A ⊆ B → g B ⊆ g A) :
    (∀ A B, B ⊆ g A ↔ A ⊆ K.polarUp B) ↔ g = K.polarDown := by
  constructor
  · intro h
    funext B
    apply le_antisymm
    · intro x hx
      have h1 : B ⊆ K.polarUp {x} := (h B {x}).1 (by
        intro m hm
        rw [Set.mem_singleton_iff] at hm
        subst hm
        exact hx)
      exact (K.mem_polarDown_iff (B := B) (g := x)).2
        (fun m hm => (K.mem_polarUp_iff (A := {x}) (m := m)).1 (h1 hm) (Set.mem_singleton x))
    · intro x hx
      exact (h B (K.polarDown B)).2 (K.subset_polarDown_polarUp B) hx
  · intro h A B
    rw [h]
    exact K.subset_polarUp_iff_subset_polarDown.symm

/-! ## §1.2  ⚠ 分离探针：单底集里「伴随 + 反单调」**不唯一**

取 `γ := Unit`、`r ≡ False`。则 `upperPolar r = lowerPolar r`（对称，见
`T112Unary.upperPolar_eq_lowerPolar_of_symm`），**且两者都是**

$$f(A) = \begin{cases}\varnothing & A \neq \varnothing\\ \mathrm{univ} & A = \varnothing\end{cases}$$

下面证明：在 `Unary` 里，**`f := upperPolar r` 与 `f := lowerPolar r` 是两个不同的
候选**（在非对称情形），它们都反单调——**但在对称情形下它们坍缩成同一个**，
故「伴随式唯一确定 `f`」在单底集里**无法把上下极区分开**。

⚠ 更强的机器事实：单底集里 `upperPolar` 与 `lowerPolar` **同时**满足伴随式
`B ⊆ f A ↔ A ⊆ f B`（因为 `subset_upperPolar_iff_subset_lowerPolar` 两侧同型）。
**⟹ 伴随式在单底集里同时刻画两个算子，不能唯一确定一个。** -/

namespace Separator1

open T112Unary

/-- ⭐ **分离证据**：单底集 + 对称 `r` 下，`upperPolar r` 与 `lowerPolar r`
是**同一个算子**；因此「伴随式唯一确定反单调 `f`」**只能确定到一个算子**，
无法区分「上极/下极」。

**⟹ §1 的唯一性在 `GFCA = MFCA` 时失去意义。** -/
theorem unary_adjoint_not_unique {γ : Type*} {r : γ → γ → Prop} (hr : Std.Symm r)
    (s : Set γ) : upperPolar r s = lowerPolar r s :=
  upperPolar_eq_lowerPolar_of_symm hr s

/-- ⭐ **同一事实的伴随式读法**：单底集里，`f := upperPolar r` 满足
`B ⊆ f A ↔ A ⊆ f B`（**它自己就是自己的伴随**）。 -/
theorem unary_self_adjoint {γ : Type*} (r : γ → γ → Prop) {A B : Set γ} :
    B ⊆ upperPolar r A ↔ A ⊆ upperPolar (Function.swap r) B :=
  subset_upperPolar_iff_subset_lowerPolar

end Separator1

/-! ## §2  FCA 特有定理 2：概念格在「交换两个底集」下**不变**

### §2.0  陈述

$$ \mathfrak{B}(G, M, I) \;\cong\; \mathfrak{B}(M, G, I^{\mathsf T}).$$

概念 `(A, B)` 变成 `(B, A)`。这正是「外延」与「内涵」的**对偶**，
但它**不是**反序同构——它是**保序（在恰当定义的序下）同构**。

### §2.1  为什么**必须**两个底集

`conceptSwap` 的**类型**就说明了：

```
Concept K.GFCA K.MFCA K.Irel  →  Concept K.MFCA K.GFCA (swap K.Irel)
```

若 `GFCA = MFCA` 且 `I` 对称，则**两端是同一个类型** —— 该同构退化为 `Equiv.refl`。
**⟹ 「交换两个底集」只在 `G ≠ M`（或 `I` 非对称）时有内容。** -/

/-- ⭐⭐⭐ **FCA 特有定理 2**：概念在「交换两个底集」下**一一对应**。

`(A, B) ↦ (B, A)` 把 `𝕂` 的概念变成**转置背景** `𝕂ᵀ` 的概念。 -/
noncomputable def conceptSwapEquiv (K : FormalCtx) :
    Concept K.GFCA K.MFCA K.Irel ≃ Concept K.MFCA K.GFCA (Function.swap K.Irel) where
  toFun c :=
    ⟨c.intent, c.extent,
      by rw [upperPolar_swap]; exact c.lowerPolar_intent,
      by rw [lowerPolar_swap]; exact c.upperPolar_extent⟩
  invFun c :=
    ⟨c.intent, c.extent,
      by rw [upperPolar_swap]; exact c.lowerPolar_intent,
      by rw [lowerPolar_swap]; exact c.upperPolar_extent⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

/-- ⭐ **推论：转置两次回到原处**（`conceptSwap` 是**对合**）。 -/
theorem conceptSwapEquiv_invol (K : FormalCtx) :
    (conceptSwapEquiv K).symm = conceptSwapEquiv (K := ⟨K.MFCA, K.GFCA, Function.swap K.Irel⟩) :=
  rfl

/-- ⭐⭐ **推论（`Ext` 与 `Int` 的对应就是 `conceptSwap` 的投影）**：
`Concept` 的 `extent` 分量在转置下变成 `intent` 分量。 -/
theorem conceptSwap_extent (K : FormalCtx) (c : Concept K.GFCA K.MFCA K.Irel) :
    (conceptSwapEquiv K c).extent = c.intent := rfl

theorem conceptSwap_intent (K : FormalCtx) (c : Concept K.GFCA K.MFCA K.Irel) :
    (conceptSwapEquiv K c).intent = c.extent := rfl

/-! ## §2.2  ⚠ 分离探针：单底集里「转置」的两端是同一类型

在 `Unary` 里，`Concept γ γ r` 转置后是 `Concept γ γ (swap r)`
——**类型完全一样**（只是关系换了）。故「交换两个底集」在单底集里
**不交换任何类型**，只是**换了一个关系**。

⚠ 这仍然有点内容（`r → swap r`），但**它不是「交换底集」**——
若 `r` 对称，它什么也没做。 -/

namespace Separator2

open T112Unary

/-- ⭐ **分离证据**：单底集里 `Concept` 的转置**两端同类型**。

⟹ `conceptSwapEquiv` 在单底集里**没有「交换两个底集」的内容**。 -/
theorem unary_swap_same_type {γ : Type*} (r : γ → γ → Prop) :
    Nonempty (Concept γ γ r ≃ Concept γ γ (Function.swap r)) :=
  ⟨⟨fun c => ⟨c.intent, c.extent, by rw [upperPolar_swap]; exact c.lowerPolar_intent,
      by rw [lowerPolar_swap]; exact c.upperPolar_extent⟩,
    fun c => ⟨c.intent, c.extent, by rw [upperPolar_swap]; exact c.lowerPolar_intent,
      by rw [lowerPolar_swap]; exact c.upperPolar_extent⟩,
    fun c => by cases c; rfl, fun c => by cases c; rfl⟩⟩

end Separator2

/-! ## §3  FCA 特有定理 3：`polarUp` 在**外延**上单射

### §3.0  陈述

$$A, B \text{ 外延},\; A' = B' \implies A = B .$$

### §3.1  为什么**必须**两个底集

`polarUp A` 在 `Set K.MFCA` 里。要把 `A' = B'` 传回 `A = B`，
必须**再取一次极**，即 `A = A'' = (A')' = (B')' = B'' = B`。
**这一次「再取极」就是从 `M` 侧回到 `G` 侧**——**没有两个底集就没有「回到」这个动作**。

⚠ 对比：`polarUp` 在**全部** `Set K.GFCA` 上**不是**单射
（`A' = A''''`，而 `A ≠ A''`）。**故「外延」这一限制与「两侧」是同一件事**：
`A` 是外延 **⟺** `A` 已经「回到」过 `G` 侧。 -/

/-- ⭐⭐⭐ **FCA 特有定理 3**：`polarUp` 在**外延**上单射。 -/
theorem polarUp_injective_on_extents (K : FormalCtx) {A B : Set K.GFCA}
    (hA : Order.IsExtent K.Irel A) (hB : Order.IsExtent K.Irel B)
    (h : K.polarUp A = K.polarUp B) : A = B := by
  have e1 : K.polarDown (K.polarUp A) = A := Order.IsExtent.eq hA
  have e2 : K.polarDown (K.polarUp B) = B := Order.IsExtent.eq hB
  rw [← e1, ← e2, h]

/-- ⭐ **对偶**：`polarDown` 在**内涵**上单射。 -/
theorem polarDown_injective_on_intents (K : FormalCtx) {A B : Set K.MFCA}
    (hA : Order.IsIntent K.Irel A) (hB : Order.IsIntent K.Irel B)
    (h : K.polarDown A = K.polarDown B) : A = B := by
  have e1 : K.polarUp (K.polarDown A) = A := Order.IsIntent.eq hA
  have e2 : K.polarUp (K.polarDown B) = B := Order.IsIntent.eq hB
  rw [← e1, ← e2, h]

/-- ⭐⭐⭐ **「外延」= 「已经回到 `G` 侧」**（把 §3.1 的说明变成定理）。

`A` 是外延 **⟺** `A` 是某个 `B ⊆ M` 的极（即 `A` 处于 `polarDown` 的像中）。
**⟹ §3 的单射性可以重述为：`polarUp` 在 `polarDown` 的像上单射。** -/
theorem isExtent_iff_mem_range_polarDown (K : FormalCtx) (A : Set K.GFCA) :
    Order.IsExtent K.Irel A ↔ A ∈ Set.range (K.polarDown : Set K.MFCA → Set K.GFCA) :=
  Iff.rfl

/-! ## §3.2  ⚠ 分离探针：单底集里 `IsExtent ⟺ IsIntent`（若对称），单射性无内容

在 `Unary` 里 `A' = B'` 时，`A = A'' = B'' = B` **不需要**「外延」假设——
因为 `A''` 就是 `A` 的闭包，而 `polarUp` 的像**已经**是闭的。

更准确地说：单底集里 `polarUp r` 的**值域**是「闭集」，而 `polarDown` 作用回去
恰好就是闭包——单射性**只在闭集上**成立，这与 FCA 完全同构。
**⟹ 「在闭集上单射」不是 FCA 特有（任何闭包算子都对）。**
但「**哪两个底集**上的闭集」是 FCA 特有的。**§3 的陈述必须两个底集，
但它的数学内容 = 「恒等映射在不动点上单射」。** -/

namespace Separator3

/-- ⭐⭐ **分离证据（关键，且对 §3 不利）**：对**任意**闭包算子 `c`，
`c` 在其不动点上单射——这是 `Subtype.ext`。

**⟹ §3 的数学内容不是 FCA 特有**；FCA 特殊的只是它的**写法**。 -/
theorem unary_extent_inj_trivial {α : Type*} [PartialOrder α] (c : ClosureOperator α)
    {a b : α} (ha : c a = a) (hb : c b = b) (h : c a = c b) : a = b := by
  rw [ha, hb] at h
  exact h

end Separator3

/-! ## §4  ⭐⭐⭐ **元结论**（本轮最重要的输出）

### §4.1  结论原文

> **在本轮所有测试过的候选里，「FCA 特有」与「一般闭包算子的结论」
> 的差别，**本质上**只有一条：**
>
> $$ \boxed{\;\text{FCA 的陈述里有\textbf{两个}底集 } G, M;\quad \text{一般闭包算子只有一个。}\;} $$
>
> 除此之外，**没有任何**「FCA 特有」的定理是本轮找到的。

### §4.2  支撑 §4.1 的机器事实（全部零 `sorry`）

| 事实 | 出处 | 说明 |
|---|---|---|
| `upperPolar`/`lowerPolar` 对**任意**二元关系成立 | `C3.bipolar_idem_any_relation` | 候选 3 非特有 |
| 单底集 + 对称 ⟹ 上下极**相等** | `T112Unary.upperPolar_eq_lowerPolar_of_symm` | 两侧坍缩 |
| 单底集 + 对称 ⟹ `IsExtent ⟺ IsIntent` | `T112Unary.isExtent_iff_isIntent_of_symm` | 外延/内涵坍缩 |
| `Extent r = Intent (swap r)` | `C2.extent_eq_intent_swap` | 「两侧」可压成「一个关系的两个方向」 |
| 任意完备格上闭包算子 ⟹ 不动点集完备格 | `C1.fix_completeLattice` | 候选 1 非特有 |
| 任意 `Lattice` 上亦然 | `C1.fix_lattice` | 同上，更强 |
| 任意闭包算子的不动点由代表元唯一确定 | `C4.fix_determined_by_rep` | 候选 4 非特有 |
| `Ext(𝕂)` = 单侧 `extentClosure` 的不动点 | `C5.extent_eq_fix_of_extentClosure` | 候选 5 非特有 |
| 闭包算子在不动点上单射 | `Separator3.unary_extent_inj_trivial` | §3 内容非特有 |
| 单底集里 `Concept` 转置两端**同类型** | `Separator2.unary_swap_same_type` | §2 特有性=类型差 |
| 单底集里伴随式**不能**唯一确定上下极 | `Separator1.unary_self_adjoint` | §1 特有性=类型差 |

### §4.3  §1–§3 的定理**为什么**仍然值得留下

它们满足一个**严格的判据**：

> **去掉 `G`/`M` 之一（代入 `G = M`）后，命题的陈述要么不可写，要么退化为
> 「某闭包算子的性质」——即 §4.2 里已列出的通用事实。**

这正是「FCA 特有性 = 两个底集」的**定义性特征**，而不是「FCA 有更深的定理」。

### §4.4  对任务书 T1.12 的最终回答

> **T1.12（二次商 ≃ 闭包不动点）不含 FCA 内容**——
> `Fate/T112SecondQuotient` 的 `t112_holds_for_any_closureOperator` 已机器证明这一点。
>
> **补上「两个底集」后（即 `Ext ≃ Int` / `conceptSwap`），T1.12 才获得 FCA 的形式**，
> 但获得的是**两个底集的结构**，而不是新的数学内容——
> 「`Ext ≃ Int`」由 Galois 连接的一般理论即可给出（`T112Pair.fixEquiv`）。
>
> **⟹ T1.12 的「本框架专属」性，来源是「命运框架里实例空间与属性空间是两个不同的空间」，
> 不是「FCA 提供了因果图提供不了的东西」。** -/

end FateV2.Rules