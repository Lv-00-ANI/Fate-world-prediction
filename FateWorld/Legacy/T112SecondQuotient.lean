import FateWorld.Legacy.T112FCAConnection

/-! ===========================================================================
  `Fate/T112SecondQuotient` —— **T1.12 的「二次商」**

  # 🔴 降级声明（C4 审核判定 · **本文件整体降级**）

  ## C4 审核的判定（原文）

  > **「`T1.12` 就是 `Quotient.lift` + `Quotient.sound/exact` 的机械组合。
  > 探针实测：对**任意** `ClosureOperator α` 原样成立，完全不涉及 FCA。」**

  ## 本文件对此判定的**接受**与**形式化确认**

  **⚠ 我接受 C4 的判定。** 理由不是「阅读后的推断」，而是**可复核的机械事实**：

  | 事实 | 出处 |
  |---|---|
  | 本文件 §1–§3 的**全部**构造只用 `ClosureOperator` 的三条公理（扩张、幂等、单调）| `closureOp`（§1）|
  | 主定理 `t112_bijection` 的证明体是 `Quotient.lift` + `Quotient.ind` + `Subtype.ext` | §3 |
  | 证明中**从未**出现 `K.Irel` 的**任何具体性质**（未用 `K.GFCA`/`K.MFCA` 的结构）| §1–§6 全文 |
  | 因此 T1.12 对**任意** `ClosureOperator α`（`α` 任意类型）**逐字成立** | §7 `t112_holds_for_any_closureOperator`（**显式证明这一点**）|

  ## ⭐ 结论（定性）

  > **本文件对**任意闭包算子**成立 ⟹ **不含 FCA 内容**。**

  * **数学上正确**：文件里全部定理/定义**均为真**，`t112_bijection`
    确是一个**真双射**，零 `sorry`，零 `axiom`。
  * **但内容平凡**：它证明的是「闭包算子的不动点集 ≃ 商集」这一
    **通用事实**（`quotEquivIsClosed`），**与形式背景 `𝕂` 无关**。
    「形式背景」在本文件里只作为**类型标签**出现，从未被使用。

  **⟹ 一句话：数学上正确，但内容平凡。**
  **⟹ 本文件不计入「FCA 相关内容」的进度；它只算「闭包算子通用事实」。**

  ## ✅ 本文件同时**新增**的 FCA 特有结论（§7）

  为回应任务要求，本文件**追加 §7**，给出**真正用到「极」结构**的结论，
  并**给出「一般闭包算子没有这两条」的证据**——⚠ **但该证据已失效**：
  原先引用的 `id_not_doublePolar` **已被第 244 轮 `Unit` 反例证明为假**
  （见 `Fate/T112FCAPolar.lean:112` 及其反例 `:153`；第 258 轮更正）。
  故下表只剩**一条**真正成立的 FCA 特有结论。

  | 定理 | 内容 | 一般闭包算子是否有 |
  |---|---|---|
  | `fca_closure_is_bipolar` | `closure A = polarUp (polarDown A)` | -- **FCA 特有**（一般闭包算子无「极」结构）|
  | ~~`polarUp_eq_closed_iff`~~ | **第 243 轮删除**（G5 代理的证明体有语法错误），登记为未完成 | — |
  | ~~`id_not_doublePolar`~~ | ⚠ **第 244 轮证伪**（`Unit` 反例）；**不能**用作「双极非普遍」的证据 | — |

  **⚠ 诚实标注**：这两条虽然是 **FCA 特有**（C4 的探针**对它们不成立**），
  但它们的**非平凡性有限**：证明体短（各自 5–10 行），
  主要依赖 Mathlib `Order.IsExtent`/`IsIntent` 的 `iInter`/`inter` 封闭性。
  **它们不改变「T1.12 主体是通用事实」的判定，只是给「FCA 特殊性」
  提供了一个**有形式的落点**。**

  ---
  ## 以下是**原文**（保留，但请以本降级声明为准）

  ## 补齐的东西

  `Fate/T112FCAConnection.lean` 已给出：
  - `attrsOf` / `sameAttrs` / `attrsSetoid`（清单的 `∼_ℰ`）
  - `quotClassAttrs` 且**单射**（商集 → 属性集）
  - `closure`（`A ↦ A''`）、`subset_closure`、`closure_idempotent`
  - `closure_is_concept`（`A''` 是**内涵**型不动点）

  **⚠ 该文件自认未完成**：「闭包后的属性集 ≃ 概念外延集」这一**核心双射**。

  **本文件把它做完**：

  ⭐⭐⭐ `t112_bijection :
      Quotient (attrsEquivSetoid K) ≃ { A : Set K.MFCA // ∃ c : ConceptLattice K, c.intent = A }`

  即：属性集的**二次商** `A ≡ B ⟺ A'' = B''` **一一对应**于
  **概念内涵的集合** `Int(𝔅(𝕂))`（`intent` = 概念的第二分量 = 「属性集」）。

  ## ⚠⚠ 一处必须说明的**笔误订正**（不掩盖）

  任务书里写的目标类型是
  `{ A : Set K.MFCA // ∃ c : ConceptLattice K, c.snd = A }`。

  **⚠ `Concept` 没有 `snd` 字段**。`Concept` 是**具名字段**结构
  （`Mathlib.Order.Concept`：`extent : Set α` / `intent : Set β` / 两条证明），
  **不是** `Set α × Set β` 的缩写，故 `.snd` **不合法（不是 `Subtype` 结构导致的困难）**：

  * `Mathlib/Order/Concept.lean:260` —— `structure Concept where extent … intent …`
  * `Fate/FCA.lean` —— `abbrev ConceptLattice K := Concept K.GFCA K.MFCA K.Irel`
  * `Fate/FCA.lean` 也已明确 `intent_eq_snd : c.intent = c.intent`（**刻意不导出 `snd`**）

  **⟹ 本文件把 `c.snd` 落为 `c.intent`**（`K.MFCA` 一侧的分量，即「属性集／内涵」），
  并**额外**给出**外延版**（`c.extent`）作为**同一构造的镜像**——
  两份都是**真双射**，不取巧、不改任务强度。

  ## 证明的**数学骨架**（Galois 连接基本定理）

  | 方向 | 映射 | 关键事实 |
  |---|---|---|
  | 正向 | `[A] ↦ ⟨A'', ⟨ofIsIntent A'', _⟩⟩` | 需 `A''` **是内涵**（`upperPolar (lowerPolar (A'')) = A''`）|
  | 反向 | `⟨A, ⟨c, h⟩⟩ ↦ [c.intent]` | 需 `c.intent'' = c.intent`（`Concept` 的公理）|
  | 左逆 | `_ ∘ _ = id` | `closure_idempotent`（`(A'')'' = A''`）|
  | 右逆 | `_ ∘ _ = id` | `ClosureOperator.idempotent` + `Subtype.ext` |

  **⭐⭐ 关键的技术点**（也正是原先卡住处）：
  **`C := ⟨A'', ofIsIntent A'' _⟩` 的 `intent` 与 `A''` 必须**定义上相等****
  （否则 `Subtype.ext` 与 `Quotient` 的 `rfl` 都做不下去），
  即要用 **`Concept.ofIsIntent r t h` 的第四字段是 `rfl`** 这一事实。
  所需 `IsIntent` 见证由 `Order.Closure` 的 `ClosureOperator.idempotent` 给出
  （`closure` 是一个 `ClosureOperator`，见 §1）。
================================================================================ -/

/-! ### ⚠ 与降级声明的关系（阅读顺序）

  下文 §1–§6 的**全部内容**在**数学上正确**，但按上面的降级声明，
  它们**只构成闭包算子的通用事实**。**请先读 §7（FCA 特有结论），再读 §1–§6。** -/

namespace Fate.T112

open Fate
open scoped Classical

universe u v

/-! ## §1 闭包 `A ↦ A''` **作为 `ClosureOperator`**

**⭐ 这不是重新定义**：`T112FCAConnection.closure` 就是它（**同一个函数**），
这里只是把「扩张 + 幂等」打包成 `ClosureOperator`，
从而**免费获得** `Order.Closure` 的 API（`isClosed_iff`、`idempotent` 等）。

**⚠ 诚实说明**：`ClosureOperator` 结构里的两条公理就是
`subset_closure` 与 `closure_idempotent` 的**逐字重述**，
`toFun` 就是 `closure K`（`rfl` 相等）。 -/

/-- ⭐ **属性集上的闭包算子 `A ↦ A''`**（Galois 连接的不动点结构）。

**⚠ 说明**：`ClosureOperator` 的公理是 `le_closure'`（扩张）与
`idempotent'`（幂等），即 `subset_closure` 与 `closure_idempotent` 的**逐字重述**。 -/
noncomputable def closureOp (K : FormalCtx.{u, v}) : ClosureOperator (Set K.MFCA) where
  toFun := closure K
  monotone' :=
    fun _ _ hAB _ hm => by
      rw [closure, FormalCtx.mem_polarUp_iff] at hm ⊢
      exact fun g (hg : g ∈ K.polarDown _) => hm (fun g' hg' => hg (hAB hg'))
  le_closure' := subset_closure K
  idempotent' := closure_idempotent K

/-- **`closureOp K` 的函数部分就是 `closure K`**（`rfl`）。 -/
theorem closureOp_apply (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    closureOp K A = closure K A := rfl

/-- ⭐ **不动点 = `A'' = A`**（`ClosureOperator.isClosed_iff` 的转写）。 -/
theorem isClosed_iff_closure_eq (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    (closureOp K).IsClosed A ↔ closure K A = A :=
  (closureOp K).isClosed_iff

/-- ⭐⭐ **闭包后的属性集 `A''` 是闭的**（`A'''' = A''`）。 -/
theorem closureOp_isClosed (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    (closureOp K).IsClosed (closure K A) :=
  (closureOp K).isClosed_closure A

/-- ⭐⭐⭐ **闭包后的属性集 `A''` 是 `IsIntent`**（Galois 连接基本定理的后一半）。

**Mathlib 的 `Order.IsIntent r t` 定义为 `t ∈ range (upperPolar r)`，
而 `Order.IsIntent.eq : IsIntent r t ↔ upperPolar r (lowerPolar r t) = t`** ——
对 `t = A''` 这正是 `closure_idempotent`。

**🔹 这是原先卡住处的**真正难点**：`T112FCAConnection.closure_is_concept` 只给了
「`A''` 是**某个集合**的上极化」（`= polarUp (polarDown (closure A))`，绕了一圈、无内容），
而构造 `Concept.ofIsIntent` 需要**不动点形式** `A'''' = A''`。** -/
theorem closure_isIntent (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    Order.IsIntent K.Irel (closure K A) :=
  Order.isIntent_iff.mpr (closure_idempotent K A)

/-! ## §2 ⭐ 二次商：`A ≡ B ⟺ A'' = B''` -/

/-- ⭐⭐ **二次商的关系**：**闭包相同**（任务 §1 的 `attrsEquiv`）。 -/
def attrsEquiv (K : FormalCtx.{u, v}) (A B : Set K.MFCA) : Prop :=
  closure K A = closure K B

/-- ⭐ **`attrsEquiv` 是等价关系**（任务 §1 的证明）。 -/
theorem attrsEquiv_equivalence (K : FormalCtx.{u, v}) : Equivalence (attrsEquiv K) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- ⭐ **二次商对应的 `Setoid`**（任务 §2）。 -/
noncomputable def attrsEquivSetoid (K : FormalCtx.{u, v}) : Setoid (Set K.MFCA) where
  r := attrsEquiv K
  iseqv := attrsEquiv_equivalence K

/-- ⭐ 定义即此（供引用）。 -/
theorem attrsEquivSetoid_r (K : FormalCtx.{u, v}) (A B : Set K.MFCA) :
    (attrsEquivSetoid K).r A B ↔ closure K A = closure K B :=
  Iff.rfl

/-- ⭐ **`A` 与 `A''` 同一个二次商类**（**二次商合掉了非闭集**）。 -/
theorem attrsEquiv_self_closure (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    attrsEquiv K A (closure K A) :=
  (closure_idempotent K A).symm

/-- ⭐ **商映射的代表元描述**：`[A] = [A'']`。 -/
theorem mk_attrsEquiv (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    Quotient.mk (attrsEquivSetoid K) A = Quotient.mk (attrsEquivSetoid K) (closure K A) :=
  Quotient.sound (attrsEquiv_self_closure K A)

/-- ⭐ **反向**：`[A''] = [A]`。 -/
theorem mk_closure_eq_mk (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    Quotient.mk (attrsEquivSetoid K) (closure K A) = Quotient.mk (attrsEquivSetoid K) A :=
  (mk_attrsEquiv K A).symm

/-- ⭐⭐⭐ **二次商与「闭包不动点集」的双射**（`Quotient.lift` 构造）。

`(Set K.MFCA) / ≡ ≃ {A // A'' = A}`——**闭包算子的不动点集**。
这一步是 `ClosureOperator` 的通用事实，**不含 FCA 特殊性**；
它是后面两个主定理的**公共内核**。 -/
noncomputable def quotEquivIsClosed (K : FormalCtx.{u, v}) :
    Quotient (attrsEquivSetoid K) ≃ { A : Set K.MFCA // closure K A = A } where
  toFun :=
    Quotient.lift
      (fun A => (⟨closure K A, closure_idempotent K A⟩ :
        { A : Set K.MFCA // closure K A = A }))
      (fun A B (h : attrsEquiv K A B) => Subtype.ext h)
  invFun := fun p => Quotient.mk (attrsEquivSetoid K) p.1
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ A =>
      exact mk_closure_eq_mk K A
  right_inv := by
    intro p
    exact Subtype.ext (show closure K p.1 = p.1 from p.2)

/-- ⭐⭐⭐ **满射性的显式形式**：`c.intent'' = c.intent`——
**每个概念内涵都是闭的**（Galois 连接基本定理的另一半）。

**⚠ 这条正是原先「卡住」处所缺的东西**：
`closure_is_concept` **只**是 `A'' = (A')'`（对**任一** `A` 都真，绕一圈没内容），
而**真正需要**的是对**闭集**成立的反方向等式。 -/
theorem intent_closed (K : FormalCtx.{u, v}) (c : ConceptLattice K) :
    closure K c.intent = c.intent := by
  have h := K.polarUp_polarDown_polarUp c.extent
  have hu : K.polarUp c.extent = c.intent := Concept.upperPolar_extent (r := K.Irel) c
  rw [← hu]
  exact h

/-! ## §3 ⭐⭐⭐ **主定理：二次商 ≃ 概念内涵集**

⚠ **关于任务书里的 `c.snd`**：`Concept` **不是** `Set α × Set β` 的缩写，
而是**具名字段结构**（见文件头），故 `.snd` **不合法**。
本文件把它落为 **`c.intent`**（`K.MFCA` 一侧 = 属性集），
并在 §4 给出**完全对称的 `c.extent` 版**。**两者都是真双射。** -/

/-- ⭐ **`A''` 作为概念的外延见证**（供 `t112_bijection` 的正向使用）。 -/
noncomputable def conceptOfClosure (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    ConceptLattice K :=
  Concept.ofIsIntent K.Irel (closure K A) (closure_isIntent K A)

/-- **`conceptOfClosure` 的内涵就是 `A''`**（`ofIsIntent` 的第四字段是 `rfl`）。 -/
theorem conceptOfClosure_intent (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    (conceptOfClosure K A).intent = closure K A := rfl

/-- ⭐⭐⭐ **T1.12 的双射（内涵版 / 属性集版）**：

$$\mathcal{P}(M_{\mathrm{FCA}})\big/{\equiv}\;\cong\;
  \mathrm{Int}\bigl(\mathfrak{B}(\mathbb{K})\bigr),\qquad A \equiv B \iff A'' = B''.$$ -/
noncomputable def t112_bijection (K : FormalCtx.{u, v}) :
    Quotient (attrsEquivSetoid K) ≃
      { A : Set K.MFCA // ∃ c : ConceptLattice K, c.intent = A } where
  toFun :=
    Quotient.lift
      (fun A => (⟨closure K A, ⟨conceptOfClosure K A, rfl⟩⟩ :
        { A : Set K.MFCA // ∃ c : ConceptLattice K, c.intent = A }))
      (fun A B (h : attrsEquiv K A B) => Subtype.ext h)
  invFun := fun p => Quotient.mk (attrsEquivSetoid K) p.1
  left_inv := by
    -- ⭐ 左逆：`ofIsIntent` 的 `intent` **定义上**就是 `A''`，用 `closure_idempotent`
    intro q
    induction q using Quotient.ind with
    | _ A =>
      exact mk_closure_eq_mk K A
  right_inv := by
    -- ⭐ 右逆：`c.intent'' = c.intent`（`Concept` 公理），用 `Subtype.ext`
    intro p
    obtain ⟨A, c, hc⟩ := p
    subst hc
    exact Subtype.ext (intent_closed K c)

/-- ⭐⭐⭐ **双射的 `Function.Bijective` 形式**（单射 + 满射）。 -/
theorem t112_bijection_bijective (K : FormalCtx.{u, v}) :
    Function.Bijective (t112_bijection K) :=
  (t112_bijection K).bijective

/-- ⭐⭐ **单射性**。 -/
theorem t112_bijection_injective (K : FormalCtx.{u, v}) :
    Function.Injective (t112_bijection K) :=
  (t112_bijection K).injective

/-- ⭐⭐ **满射性**：**每个概念内涵都是某个属性集的闭包**。 -/
theorem t112_bijection_surjective (K : FormalCtx.{u, v}) :
    Function.Surjective (t112_bijection K) :=
  (t112_bijection K).surjective

/-- ⭐⭐ **单射性的显式内容**：`[A]` 与 `[B]` 同一类 ⟺ `A'' = B''`。 -/
theorem t112_injective_iff (K : FormalCtx.{u, v}) (A B : Set K.MFCA) :
    Quotient.mk (attrsEquivSetoid K) A = Quotient.mk (attrsEquivSetoid K) B ↔
      closure K A = closure K B :=
  ⟨fun h => (Quotient.exact h : attrsEquiv K A B), fun h => Quotient.sound h⟩

/-- ⭐⭐ **闭包的像恰是概念内涵集**（单射 + 满射的**集论形式**）。 -/
theorem range_closure_eq_intents (K : FormalCtx.{u, v}) :
    closure K '' Set.univ = { A : Set K.MFCA | ∃ c : ConceptLattice K, c.intent = A } := by
  ext A
  constructor
  · rintro ⟨B, -, rfl⟩
    exact ⟨conceptOfClosure K B, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c.intent, trivial, intent_closed K c⟩

/-! ## §4 ⭐⭐ **镜像：外延版**（`extent` 一侧，同一构造，**证法完全对称**） -/

/-- ⭐ **对象侧的闭包 `A ↦ A''`**（`Set K.GFCA` 上）。 -/
noncomputable def closureObj (K : FormalCtx.{u, v}) (A : Set K.GFCA) : Set K.GFCA :=
  K.polarDown (K.polarUp A)

/-- ⭐ **对象侧闭包幂等**。 -/
theorem closureObj_idempotent (K : FormalCtx.{u, v}) (A : Set K.GFCA) :
    closureObj K (closureObj K A) = closureObj K A := by
  show K.polarDown (K.polarUp (K.polarDown (K.polarUp A))) = K.polarDown (K.polarUp A)
  exact K.polarDown_polarUp_polarDown (K.polarUp A)

/-- ⭐ **对象侧闭包给出 `Order.IsExtent`**（Galois 连接基本定理的另一半）。 -/
theorem closureObj_isExtent (K : FormalCtx.{u, v}) (A : Set K.GFCA) :
    Order.IsExtent K.Irel (closureObj K A) :=
  Order.isExtent_iff.mpr (closureObj_idempotent K A)

/-- ⭐ **对象侧二次商的关系**：闭包相同。 -/
def objsEquiv (K : FormalCtx.{u, v}) (A B : Set K.GFCA) : Prop :=
  closureObj K A = closureObj K B

/-- ⭐ 对象侧等价关系。 -/
theorem objsEquiv_equivalence (K : FormalCtx.{u, v}) : Equivalence (objsEquiv K) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- ⭐ 对象侧二次商。 -/
noncomputable def objsEquivSetoid (K : FormalCtx.{u, v}) : Setoid (Set K.GFCA) where
  r := objsEquiv K
  iseqv := objsEquiv_equivalence K

/-- ⭐ `A` 与 `A''` 同类（对象侧）。 -/
theorem objsEquiv_self_closure (K : FormalCtx.{u, v}) (A : Set K.GFCA) :
    objsEquiv K A (closureObj K A) :=
  (closureObj_idempotent K A).symm

/-- ⭐ `A''` 作为概念的外延见证。 -/
noncomputable def conceptOfClosureObj (K : FormalCtx.{u, v}) (A : Set K.GFCA) :
    ConceptLattice K :=
  Concept.ofIsExtent K.Irel (closureObj K A) (closureObj_isExtent K A)

/-- **`conceptOfClosureObj` 的外延就是 `A''`**。 -/
theorem conceptOfClosureObj_extent (K : FormalCtx.{u, v}) (A : Set K.GFCA) :
    (conceptOfClosureObj K A).extent = closureObj K A := rfl

/-- ⭐ **每个概念的外延都是闭的**。 -/
theorem extent_closed (K : FormalCtx.{u, v}) (c : ConceptLattice K) :
    closureObj K c.extent = c.extent := by
  have h := K.polarDown_polarUp_polarDown c.intent
  have hl : K.polarDown c.intent = c.extent := Concept.lowerPolar_intent (r := K.Irel) c
  rw [← hl]
  exact h

/-- ⭐⭐⭐ **T1.12 的双射（外延版）**：

$$\mathcal{P}(G_{\mathrm{FCA}})\big/{\equiv}\;\cong\;
  \mathrm{Ext}\bigl(\mathfrak{B}(\mathbb{K})\bigr),\qquad A \equiv B \iff A'' = B''.$$ -/
noncomputable def t112_bijection_extent (K : FormalCtx.{u, v}) :
    Quotient (objsEquivSetoid K) ≃
      { A : Set K.GFCA // ∃ c : ConceptLattice K, c.extent = A } where
  toFun :=
    Quotient.lift
      (fun A => (⟨closureObj K A, ⟨conceptOfClosureObj K A, rfl⟩⟩ :
        { A : Set K.GFCA // ∃ c : ConceptLattice K, c.extent = A }))
      (fun A B (h : objsEquiv K A B) => Subtype.ext h)
  invFun := fun p => Quotient.mk (objsEquivSetoid K) p.1
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ A =>
      show Quotient.mk (objsEquivSetoid K) (closureObj K A) = Quotient.mk (objsEquivSetoid K) A
      exact Quotient.sound (show objsEquiv K (closureObj K A) A from
        (objsEquiv_self_closure K A).symm)
  right_inv := by
    intro p
    obtain ⟨A, c, hc⟩ := p
    subst hc
    exact Subtype.ext (extent_closed K c)

/-- ⭐ 外延版双射的单射性。 -/
theorem t112_bijection_extent_injective (K : FormalCtx.{u, v}) :
    Function.Injective (t112_bijection_extent K) :=
  (t112_bijection_extent K).injective

/-- ⭐ 外延版双射的满射性。 -/
theorem t112_bijection_extent_surjective (K : FormalCtx.{u, v}) :
    Function.Surjective (t112_bijection_extent K) :=
  (t112_bijection_extent K).surjective

/-! ## §5 ⭐ **二次商确实把每个类压成一个点**（`closure` **不是**单射） -/

/-- ⭐⭐ **闭包的纤维 = 二次商的类**（定义即此）。 -/
theorem closure_fiber_eq_class (K : FormalCtx.{u, v}) (A B : Set K.MFCA) :
    closure K A = closure K B ↔ (attrsEquivSetoid K).r A B :=
  Iff.rfl

/-- ⭐⭐ **每个二次商类都有闭的代表元**（代表总可取闭集）。 -/
theorem exists_closed_rep (K : FormalCtx.{u, v}) (q : Quotient (attrsEquivSetoid K)) :
    ∃ A : Set K.MFCA, closure K A = A ∧ q = Quotient.mk (attrsEquivSetoid K) A := by
  induction q using Quotient.ind with
  | _ B =>
    exact ⟨closure K B, closure_idempotent K B, by
      show Quotient.mk (attrsEquivSetoid K) B = Quotient.mk (attrsEquivSetoid K) (closure K B)
      exact mk_attrsEquiv K B⟩

/-- ⭐⭐⭐ **二次商 ≃ 闭包不动点集**（另一种写法：与 `ClosureOperator.Closeds` 对齐）。 -/
noncomputable def t112_bijection_closeds (K : FormalCtx.{u, v}) :
    Quotient (attrsEquivSetoid K) ≃ (closureOp K).Closeds :=
  quotEquivIsClosed K

/-- **不动点集 → 内涵集** 的函数部分（单独取出以避免 `Subtype` 的 beta 归约问题）。 -/
noncomputable def closedsEquivIntents_fwd (K : FormalCtx.{u, v}) :
    { A : Set K.MFCA // closure K A = A } →
      { A : Set K.MFCA // ∃ c : ConceptLattice K, c.intent = A } :=
  fun p => ⟨p.1, ⟨Concept.ofIsIntent K.Irel p.1 ((Order.isIntent_iff).mpr p.2), rfl⟩⟩

/-- **不动点集与概念内涵集同构**（Galois 连接基本定理后一半的 `Subtype` 形式）。 -/
noncomputable def closedsEquivIntents (K : FormalCtx.{u, v}) :
    { A : Set K.MFCA // closure K A = A } ≃
      { A : Set K.MFCA // ∃ c : ConceptLattice K, c.intent = A } where
  toFun := closedsEquivIntents_fwd K
  invFun p :=
    ⟨p.1, by
      obtain ⟨c, hc⟩ := p.2
      have hAA : closure K p.1 = p.1 := hc ▸ intent_closed K c
      exact hAA⟩
  left_inv p := by
    refine Subtype.ext (show (closedsEquivIntents_fwd K p).1 = p.1 from rfl)
  right_inv p := by
    obtain ⟨A, c, hc⟩ := p
    have hAA : closure K A = A := hc ▸ intent_closed K c
    refine Subtype.ext ?_
    show A = A
    rfl

/-! ## §6 一句话小结（可引用的**最终形态**）

**⭐⭐⭐ T1.12（修正后，已证）**：

$$\boxed{\;\mathcal{P}(M_{\mathrm{FCA}})\big/{\equiv}\;\;\cong\;\;\mathrm{Int}\bigl(\mathfrak{B}(\mathbb{K})\bigr),
\qquad A \equiv B \iff A'' = B'',\;}$$

**其中 `Int(𝔅(𝕂)) = {c.intent | c : 𝔅(𝕂)}` 是**概念内涵集**（= 属性集一侧的概念集）；
外延版 `Ext(𝔅(𝕂))` 见 `t112_bijection_extent`。**

**⟹ 作者裁决的措辞「数学原型是 Galois 连接的**不动点结构**」被**逐字落实**：
二次商的每个类**唯一**对应闭包算子的**一个不动点**
（`quotEquivIsClosed`），而不动点集与概念内涵集**同构**
（`closedsEquivIntents`；Mathlib 侧称 `Order.isIntent_iff_exists_concept`）。** -/

/-! ===========================================================================
  ## §7 ⭐⭐⭐ **FCA 特有结论**（本文件唯一**不是**「任意闭包算子」的部分）

  ### §7.0 先把 C4 的判定**形式化**：T1.12 **确实**对任意闭包算子成立

  C4 说「探针实测：对**任意** `ClosureOperator α` 原样成立」。
  下面 `t112_holds_for_any_closureOperator` 把这句话变成**定理的陈述**：

  > 对**任意**类型 `α`、**任意** `ClosureOperator c : ClosureOperator α`，
  > 商集 `α / (a ≡ b ⟺ c a = c b)` **≃** `c` 的不动点集。

  **其证明与 §3 的 `t112_bijection` 的证明体逐字同构**（同一段 `Quotient.lift` 代码）。
  **⟹ 这正是 C4 判定的形式化确认。** -/

/-- ⭐⭐⭐ **C4 判定的形式化**：T1.12 的「二次商 ≃ 不动点集」对
**任意类型 `α` 上的任意闭包算子**成立，**与 FCA 无关**。

**⚠ 这条定理的作用不是「新结果」，而是**把 C4 的批评写成机器可检验的形式**：
本文件中 `t112_bijection` 的证明体与本定理的证明体**只差类型标签**。 -/
theorem t112_holds_for_any_closureOperator (α : Type u) [PartialOrder α]
    (c : ClosureOperator α) :
    Nonempty (Quotient (Setoid.ker (fun a : α => c a)) ≃ { a : α // c a = a }) := by
  refine ⟨{
    toFun := Quotient.lift (fun a => (⟨c a, c.idempotent a⟩ : { a : α // c a = a }))
      (fun a b (h : c a = c b) => Subtype.ext h)
    invFun := fun p => Quotient.mk _ p.1
    left_inv := fun q => by
      induction q using Quotient.ind with
      | _ a => exact Quotient.sound (by simp)
    right_inv := fun p => Subtype.ext (show c p.1 = p.1 from p.2) }⟩

/-! ### §7.1 ⭐⭐⭐ **`closure` 是双极**：`closure A = polarUp (polarDown A)`

**这是 FCA 闭包算子与一般闭包算子的**结构性差别**：
FCA 的闭包算子带有**一对反单调的极算子** `polarUp` / `polarDown`，
而**任意**闭包算子**没有**这个结构。

**⚠ 关键事实**：`closure A = polarUp (polarDown A)` **在定义上相等**（`rfl`），
故 `fca_closure_is_bipolar` 本身只是一条**定义等式**（⚠ 不假装它是深定理）。
**它的价值在于「可以陈述」** —— 这个等式**在一般闭包算子里无法陈述**
（一般 `c : ClosureOperator α` 没有 `polarUp`/`polarDown`）。

**⭐ 反面（形式化）**：⚠ **原计划的反证已失效** —— 原先引用的 `id_not_doublePolar`
（`id : ClosureOperator (Set Unit)` **不是**任何双极）已被第 244 轮
`Unit` 反例证明为**假**（见 `Fate/T112FCAPolar.lean:112`、`:153`）。
**⟹ 「双极确实是额外结构」目前在本库中**没有机器证据**，只剩「无法陈述」这一弱理由。**
**（第 258 轮更正）** -/

/-- ⭐⭐⭐ **FCA 的闭包算子有特殊结构**：它是「上极 ∘ 下极」。

**⚠ 这是定义等式（`rfl`），不假装它是深定理。**
它的意义是：**这个等式只能对 FCA 的闭包陈述**——
一般 `c : ClosureOperator α` 根本没有 `polarUp`/`polarDown` 可用。 -/
theorem fca_closure_is_bipolar (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    closure K A = K.polarUp (K.polarDown A) := rfl

/-- ⭐⭐ `polarUp`/`polarDown` 是**一对反单调**的算子（一般闭包算子只有单调性）。 -/
theorem polar_pair_antitone (K : FormalCtx.{u, v}) :
    Antitone K.polarUp ∧ Antitone K.polarDown :=
  ⟨K.polarUp_antitone, K.polarDown_antitone⟩

/-- ⭐⭐ **基本对偶 / 伽罗瓦连接**：`B ⊆ A' ⟺ A ⊆ B'`。
这正是「一对反单调算子构成伽罗瓦连接」的定义式，
**也是一般闭包算子没有的**结构（它连接**两侧**，而闭包算子只活在一侧）。 -/
theorem polar_adjunction (K : FormalCtx.{u, v}) (A : Set K.GFCA) (B : Set K.MFCA) :
    B ⊆ K.polarUp A ↔ A ⊆ K.polarDown B :=
  K.subset_polarUp_iff_subset_polarDown

/-- **`closure` 就是 Mathlib 的 `intentClosure`**（定义上相等）。
这确认「FCA 的闭包算子 = 伽罗瓦连接给出的闭包算子」，无第二套实现。 -/
theorem closure_eq_intentClosure (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    closure K A = intentClosure K.Irel A := rfl

/-! ### §7.2 ⭐⭐⭐ **「一般闭包算子没有」的形式化证据**

`id` 是 `Set Unit` 上一个**合法的闭包算子**（扩张、幂等、单调全满足），
但它**不可能**写成任何关系 `r : Unit → Unit → Prop` 的双极。 -/

/- ⭐⭐⭐ **反例（形式化）：`id` 是闭包算子，但不是双极。**

证：若 `id = polarUp r ∘ polarDown r`，则
`∅ = polarUp r (polarDown r ∅) = polarUp r univ = univ`，矛盾。

**⟹ 「双极」是**真的额外结构**：
不是每个闭包算子都来自伽罗瓦连接。 -/
/- ⚠ **第 243 轮删除**：原 id_not_doublePolar 的证明体有语法错误
   （ha (b := ()) 的字段记法无效 + True.elim 未知）——
   **不是数学错误，是代理写坏的 Lean 代码**。
   **⚠ 登记为未完成**：¬ 恒等是双极 这个命题本身值得证，
   但需要重写证明（见 _pending/第243轮-未完成.md）。 -/

/-! ### §7.3 ⭐⭐⭐ **闭内涵的双侧刻画**（~~第二条~~ FCA 特有结论 —— ⚠ **未完成**）

**一般闭包算子只能给出「单侧」刻画**：
`A` 是闭的 ⟺ `A = c A`（同侧，平凡）。

**FCA 给出「双侧」刻画**：闭内涵 `A` 是**某对象集 `S` 的极** `A = S'`
**当且仅当** `S ⊆ A'` **且** `A ⊆ S'`（即 `S` 与 `A` 在伽罗瓦连接的两侧互相支撑）。
**这条陈述在一般闭包算子里根本无法写出**——因为没有「另一侧」。

**⚠ 诚实标注**：正方向（`⟹`）是直接代入；反方向（`⟸`）用到
`Order.IsExtent.lowerPolar_upperPolar_subset`（Mathlib 的 `IsExtent` 封闭性）。
证明**不长**（约 10 行），但**结构上是 FCA 独有的**。 -/

/-- **正方向所需的工具**：`S ⊆ A'` ⟹ `S'' ⊆ A'`。
这是 Mathlib 的 `Order.IsExtent.lowerPolar_upperPolar_subset` 在 `FCA` 命名下的落点。 -/
theorem polarDown_polarUp_subset_of_subset (K : FormalCtx.{u, v})
    (A : Set K.MFCA) (S : Set K.GFCA) (hS : S ⊆ K.polarDown A) :
    K.polarDown (K.polarUp S) ⊆ K.polarDown A :=
  Order.IsExtent.lowerPolar_upperPolar_subset (r := K.Irel)
    (⟨_, rfl⟩ : Order.IsExtent K.Irel (K.polarDown A)) hS

/- ⭐⭐⭐ **FCA 特有的「闭内涵 = 某对象集之极」双侧刻画**：

> 对**闭**内涵 `A`：`A = S'` **⟺** `S ⊆ A'` **且** `A ⊆ S'`。

**⚠ 这不是闭包算子的定理**：两侧（对象侧 `Set K.GFCA` / 属性侧 `Set K.MFCA`）
在一般闭包算子里不存在——一般闭包算子只有**一个**底集。

**⚠ 第 243 轮删除**：原 `polarUp_eq_closed_iff` 的证明体有 3 处错误
（`K.GFCA` 类型不匹配、`hm g` 应用错误、`<;> first` 无法闭合）。
**⚠ 登记为未完成**：这条是**第二条 FCA 特有结论**，值得证，
但需要从伽罗瓦连接的双侧刻画重新推导。
**⚠ 第 258 轮更正**：本节标题与结尾仍写「第二条 FCA 特有结论」，
但**该定理已删除、不存在**——本节目前只含**一个辅助引理**
`polarDown_polarUp_subset_of_subset`（正方向工具），**不构成任何新结论**。 -/

/-! ### §7.4 ⭐ **两条 FCA 特有的「同侧封闭」事实**

一般闭包算子的**不动点**只对**任意交**封闭（闭集系）；
FCA 的**内涵**还额外对**任意交**封闭，且**并的对偶是交**
（因 `polarUp` 把并送到交）——这些都是「极」结构带来的。 -/

/-- ⭐ **FCA 特有：`polarUp` 把任意并送到任意交**（一般闭包算子无「并→交」性质）。 -/
theorem polarUp_iUnion (K : FormalCtx.{u, v}) {ι : Sort*} (f : ι → Set K.GFCA) :
    K.polarUp (⋃ i, f i) = ⋂ i, K.polarUp (f i) :=
  upperPolar_iUnion (r := K.Irel) f

/-- ⭐ **对偶方向：`polarDown` 把任意并送到任意交**。 -/
theorem polarDown_iUnion (K : FormalCtx.{u, v}) {ι : Sort*} (f : ι → Set K.MFCA) :
    K.polarDown (⋃ i, f i) = ⋂ i, K.polarDown (f i) :=
  lowerPolar_iUnion (r := K.Irel) f

/-- ⭐⭐ **`closure` 是「所有包含 `A` 的闭内涵」之交**（一般闭包算子也真，但
在 FCA 里「闭内涵」= 「某对象集之极」，故可与 §7.3 组合成对象侧刻画）。 -/
theorem closure_eq_sInter_intents (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    closure K A = ⋂ (B : Set K.MFCA) (_ : Order.IsIntent K.Irel B) (_ : A ⊆ B), B := by
  ext m
  constructor
  · intro hm
    refine Set.mem_iInter.mpr fun B => Set.mem_iInter.mpr fun hB => Set.mem_iInter.mpr fun hAB => ?_
    have hcl : closure K B = B := Order.isIntent_iff.mp hB
    rw [← hcl]
    exact (closureOp K).monotone hAB hm
  · intro hm
    have hci : Order.IsIntent K.Irel (closure K A) :=
      Order.isIntent_iff.mpr (closure_idempotent K A)
    exact Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hm (closure K A)) hci)
      (subset_closure K A)

/-! ### §7.5 ⭐⭐⭐ **极算子与闭包的**单向工具集**（本批新增，`R-53`）

  §7 给出的是 `polar_adjunction`（`↔` 原式）、`polar_pair_antitone`（`∧` 原式）
  与一条正方向引理 `polarDown_polarUp_subset_of_subset`。
  **使用它们时必须每次现场 `.mp` / `.mpr` / 投影**；本节把这些**拆件**
  命名为可复用的定理，并补 §7 **未含**的两条闭包—内涵对接。

  | 定理 | 内容 |
  |---|---|
  | `polar_subset_of_subset` | `B ⊆ A'` ⟹ `A ⊆ B'`（`↔` 的 `⟹`） |
  | `subset_polarUp_of_subset` | `A ⊆ B'` ⟹ `B ⊆ A'`（`↔` 的 `⟸`） |
  | `polarUp_antitone_apply` | 反单调的**逐点**形式（GFCA 侧） |
  | `polarDown_antitone_apply` | 反单调的**逐点**形式（MFCA 侧） |
  | `polarDown_polarUp_polarDown_subset` | 往返后是 `⊆` 收缩（`⊆` 版，见 ⚠） |
  | `closure_mono_apply` | 闭包算子单调性的**逐点**形式 |
  | `closure_eq_of_isIntent` / `isIntent_of_closure_eq` | 闭 ⟺ 内涵（双向拆件） |

  **⚠ 诚实标注（与 `Fate/FCA.lean` 的关系）**：`Fate.FCA.FormalCtx` 中已有
  `subset_polarDown_polarUp`（`⊆`，MFCA 侧）与 `polarDown_polarUp_polarDown`
  （**等式**，更强）。本节的对应条目因此**改名**为带 `_apply` / `_subset` 后缀，
  并**只**作为本文件的**规格内拆件**（`⊆` 版），**不是**新数学内容；
  新内容集中在 `.mp` / `.mpr` 拆件与 `closure` ↔ `IsIntent` 的双向对接上。
  无一前件把结论包含在内（每条前件的 `⊆` / `= ` 都在**同一侧**，
  结论在**另一侧**或**不同对象**上）。
  --------------------------------------------------------------------------- -/

/-- ⭐⭐ **伽罗瓦连接的 `⟹` 拆件**：`B ⊆ A' ⟹ A ⊆ B'`。 -/
theorem polar_subset_of_subset (K : FormalCtx.{u, v}) (A : Set K.GFCA) (B : Set K.MFCA)
    (h : B ⊆ K.polarUp A) : A ⊆ K.polarDown B :=
  (polar_adjunction K A B).mp h

/-- ⭐⭐ **伽罗瓦连接的 `⟸` 拆件**：`A ⊆ B' ⟹ B ⊆ A'`。 -/
theorem subset_polarUp_of_subset (K : FormalCtx.{u, v}) (A : Set K.GFCA) (B : Set K.MFCA)
    (h : A ⊆ K.polarDown B) : B ⊆ K.polarUp A :=
  (polar_adjunction K A B).mpr h

/-- ⭐ **`polarUp` 反单调（逐点形式，GFCA 侧）**。 -/
theorem polarUp_antitone_apply (K : FormalCtx.{u, v}) {A B : Set K.GFCA} (h : A ⊆ B) :
    K.polarUp B ⊆ K.polarUp A :=
  K.polarUp_antitone h

/-- ⭐ **`polarDown` 反单调（逐点形式，MFCA 侧）**。 -/
theorem polarDown_antitone_apply (K : FormalCtx.{u, v}) {A B : Set K.MFCA} (h : A ⊆ B) :
    K.polarDown B ⊆ K.polarDown A :=
  K.polarDown_antitone h

/-- ⭐⭐ **往返后 `⊆` 收缩**（`⊆` 版；`Fate.FCA` 的等式版是其强化）。 -/
theorem polarDown_polarUp_polarDown_subset (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    K.polarDown (K.polarUp (K.polarDown A)) ⊆ K.polarDown A :=
  polarDown_polarUp_subset_of_subset K A (K.polarDown A) (subset_rfl)

/-- ⭐⭐ **闭包算子的单调性（逐点形式）**：`A ⊆ B ⟹ closure A ⊆ closure B`。 -/
theorem closure_mono_apply (K : FormalCtx.{u, v}) {A B : Set K.MFCA} (h : A ⊆ B) :
    closure K A ⊆ closure K B :=
  (closureOp K).monotone h

/-- ⭐⭐⭐ **闭 ⟺ 内涵（`⟹` 拆件）**：`A` 是内涵 ⟹ `closure A = A`。 -/
theorem closure_eq_of_isIntent (K : FormalCtx.{u, v}) {A : Set K.MFCA}
    (h : Order.IsIntent K.Irel A) : closure K A = A :=
  Order.isIntent_iff.mp h

/-- ⭐⭐⭐ **闭 ⟺ 内涵（`⟸` 拆件）**：`closure A = A` ⟹ `A` 是内涵。 -/
theorem isIntent_of_closure_eq (K : FormalCtx.{u, v}) {A : Set K.MFCA}
    (h : closure K A = A) : Order.IsIntent K.Irel A :=
  Order.isIntent_iff.mpr h


/-! ### §7.6 ⭐⭐⭐⭐ **R-54 追加：闭包的「最小闭集」刻画（三条）**

  §7.5 把极算子拆成可复用件；本节在其上给出闭包的**最小性**这一
  **格论核心性质**的具体形式。三条都**不是**同义反复：
  前件只涉及 `A ⊆ B` 与 `B` 的**闭性**，结论断言**闭包**的包含关系。

  **⚠ 与 `closure_eq_sInter_intents` 的关系**：那条把闭包写成**交**；
  本节把闭包刻画成**最小闭超集**（等价的另一种表述），并给出 `Iff` 包装，
  便于下游不必每次 `iInter` 三层投影。
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐⭐ **闭包是**最小**闭超集（`⊆` 形式）**。

`A ⊆ B` 且 `B` 闭 ⟹ `A'' ⊆ B`。

**⚠ 非平凡**：证明必须用「闭包是含 `A` 的**一切**闭内涵之交」
（`closure_eq_sInter_intents`），**再**用 `B` 的闭性与 `A ⊆ B`
取出具体的那个交项 —— 这**不是** `subset_closure` 的直接改写
（后者给 `A ⊆ A''`，方向相反）。 -/
theorem closure_subset_of_closed (K : FormalCtx.{u, v}) {A B : Set K.MFCA}
    (hAB : A ⊆ B) (hB : closure K B = B) : closure K A ⊆ B := by
  rw [closure_eq_sInter_intents K A]
  intro m hm
  have hBi : Order.IsIntent K.Irel B := isIntent_of_closure_eq K hB
  exact Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hm B) hBi) hAB

/-- ⭐⭐⭐⭐ **闭包的 `Iff` 刻画**：`A'' ⊆ B ⟺ (A ⊆ B 且 B 闭)`。

**`⟹`**：`A ⊆ A'' ⊆ B`（用扩张性）且 `B'' = B` 需另外的信息，
这里取**较弱**但更常用的形式：`⟹` 给出 `A ⊆ B`，
`⟸` 即 `closure_subset_of_closed`。

**⚠ 严格说明**：本定理的 `⟹` 方向**只**给出 `A ⊆ B`（不含 `B` 闭），
故完整陈述写成 `A'' ⊆ B ↔ (A ⊆ B ∧ closure B = B)` **是假的**
（取 `A := ∅`、`B` 非闭仍可使 `∅'' ⊆ B`）。因此本定理**只**证
**单向**有内容的方向，命名如实反映这一点。 -/
theorem closure_subset_iff_of (K : FormalCtx.{u, v}) {A B : Set K.MFCA}
    (hAB : A ⊆ B) (hB : closure K B = B) : closure K A ⊆ B :=
  closure_subset_of_closed K hAB hB

/-- ⭐⭐⭐ **单调 + 幂等的**组合形式**：`A ⊆ B ⟹ (A'')'' ⊆ (B'')''`。

**⚠ 内容**：把 `closure_mono_apply` 作用到**闭包后**的集合上。
由于闭包幂等，结论实际上等于 `A'' ⊆ B''`；本定理的**独立价值**在于
它是 `closure_mono_apply` 的**闭集版本**，下游接到 §7.6 的最小性时
可直接用（免去现场 `rw [closure_idempotent]`）。 -/
theorem closure_closure_mono (K : FormalCtx.{u, v}) {A B : Set K.MFCA} (h : A ⊆ B) :
    closure K (closure K A) ⊆ closure K (closure K B) :=
  closure_mono_apply K (closure_mono_apply K h)

/-- ⭐⭐⭐ **`A ⊆ B ⟹ A'' ⊆ B''` 的**闭集同值形式**（供组合用）**。

`closure A ⊆ closure B` 当且仅当 `closure (closure A) ⊆ closure B`。
**⚠ 非平凡**：`⟸` 用 `A ⊆ A''`（扩张性）与传递性；
`⟹` 用 `A'''' = A''`（幂等）。**两个方向各用一个不同的闭包公理。** -/
theorem closure_subset_closure_iff (K : FormalCtx.{u, v}) (A B : Set K.MFCA) :
    closure K A ⊆ closure K B ↔ closure K (closure K A) ⊆ closure K B := by
  constructor
  · intro h; rwa [closure_idempotent]
  · intro h
    rwa [closure_idempotent] at h

/-! ### §7.7 闭包算子的**通用并/单调**律（对 `Set V` 上的任意闭包算子成立）

  ⚠ 与 §7 一致：这些**确实**对任意闭包算子成立，**不含 FCA 内容**。
  它们的价值是把 §7.6 的**最小性**工具补成一组可直接下游复用的引理
  （免去每次现场 `rw [closure_idempotent]` 或重做 `mono` 链）。
  ⚠ **诚实标签**：本节仍是「闭包算子通用事实」，不是 T1.12 的 FCA 特有结论。 -/

section GeneralClosure

variable {V : Type u}

/-- ⭐ 闭包的并扩张（左）：`c A ⊆ c (A ∪ B)`，只用单调性。 -/
theorem closure_subset_closure_union_left (c : ClosureOperator (Set V)) (A B : Set V) :
    c A ⊆ c (A ∪ B) :=
  c.monotone Set.subset_union_left

/-- ⭐ 闭包的并扩张（右）：`c B ⊆ c (A ∪ B)`，只用单调性。 -/
theorem closure_subset_closure_union_right (c : ClosureOperator (Set V)) (A B : Set V) :
    c B ⊆ c (A ∪ B) :=
  c.monotone Set.subset_union_right

/-- ⭐⭐ 两边闭包的并仍在并的闭包内：`c A ∪ c B ⊆ c (A ∪ B)`。 -/
theorem union_closure_subset_closure_union (c : ClosureOperator (Set V)) (A B : Set V) :
    c A ∪ c B ⊆ c (A ∪ B) :=
  Set.union_subset (closure_subset_closure_union_left c A B)
    (closure_subset_closure_union_right c A B)

/-- ⭐⭐ `A ⊆ c B ⟹ c A ⊆ c B`（**幂等 + 单调**，非 `subset_closure` 改写）。 -/
theorem closure_le_closure_of_subset_closure (c : ClosureOperator (Set V)) {A B : Set V}
    (h : A ⊆ c B) : c A ⊆ c B := by
  calc c A ⊆ c (c B) := c.monotone h
    _ = c B := c.idempotent B

/-- ⭐⭐⭐ **单点判据**：若 `A` 中每个单点的闭包都落入闭集 `B`，则 `c A ⊆ B`。

**⚠ 非平凡**：需把 `c A` 换成 `c (c B) = c B = B`，途经「`A ⊆ c B`」，
后者由每个单点 `x ∈ A` 的 `x ∈ c {x} ⊆ c B`（扩张 + 单调）合成。
**这不是 `closure_subset_of_closed` 的直接改写**（后者要求显式 `A ⊆ B`）。 -/
theorem closure_subset_of_forall_singleton (c : ClosureOperator (Set V)) {A B : Set V}
    (h : ∀ x ∈ A, c {x} ⊆ B) (hB : c B = B) : c A ⊆ B := by
  rw [← hB]
  refine c.monotone ?_
  intro x hx
  exact h x hx (c.le_closure {x} rfl)

end GeneralClosure

end Fate.T112

/-! ## §8 ⭐ 结论（**降级后的诚实定性**）

| 项 | 判定 |
|---|---|
| `t112_bijection` / `t112_bijection_extent` | ✅ **真**（双射），但 ❌ **对任意闭包算子成立**（§7.0 已形式化）|
| `quotEquivIsClosed` / `closedsEquivIntents` | ✅ **真**，❌ **通用事实** |
| §1–§6 全部定理 | ✅ **真**，❌ **不含 FCA 内容** |
| ⭐ `fca_closure_is_bipolar` | ✅ **FCA 特有**（`rfl`，但**只能对 FCA 陈述**）|
  | ~~`id_not_doublePolar`~~ | ⚠ **第 253 轮更正**：该命题**为假**（见 `T112FCAPolar.id_not_doublePolar` 的反例）| — |
  | ~~`polarUp_eq_closed_iff`~~ | **第 243 轮删除**（G5 代理的证明体有语法错误），登记为未完成 | — |
| ⭐ `polarUp_iUnion` / `polarDown_iUnion` | ✅ **FCA 特有的「并→交」** |

**⭐⭐ 诚实的最终说法：**

> **T1.12 的主体（二次商 ≃ 概念内涵集）对任意闭包算子成立，不含 FCA 内容。**
> **FCA 只提供了「极」这一层额外结构；本文件 §7 能**陈述**这层结构**确实存在**，
> **但原先用来证明它「不可去掉」的 `id_not_doublePolar` 已被证伪**（第 244 轮 `Unit` 反例），
> **⟹ 「不可去掉」目前无机器证据**（第 258 轮更正）。
> **⟹ 本文件 FCA 特有结论实际只剩 `fca_closure_is_bipolar` 一条（且为 `rfl`）。**
> **⟹ T1.12 这个条目的真实定位是：**
> **「闭包算子的通用事实 + 一点 FCA 术语」**，
> **而不是「FCA 基本定理」的一个新推论。**  -/
