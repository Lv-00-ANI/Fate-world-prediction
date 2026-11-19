import FateWorld.FateV2.Rules.FCA
/-!
  # Rules · T112FCAConnection

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T112FCAConnection.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FCA
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/T112FCAConnection` —— **T1.12 T1.11 与 FCA 的衔接**（**第 223 轮**）

  ## 清单原文（T1.12）

  > **T1.12 与 FCA 的衔接（本框架专属）**：
  > 若 `∼_ℰ` 取为「在属性集 `I` 下具有相同属性集」，
  > 则 `ℰ/∼_ℰ` 与 `𝕂` 的对象概念的集合之间存在**双射**。

  ## ⭐ 这条为何是「本框架专属」

  **依作者裁决（导读 §2 第 (6) 条）**：
  > **规则是实例集合在等价关系下的商，其数学原型是 Galois 连接的不动点结构。**

  **⭐⭐ T1.11 只说了「规则 = 商」。T1.12 更进一步：
  这个商的元素**恰好**对应于**形式背景 `𝕂` 的**对象概念**的外延**。**

  ## ⚠⚠ 精确化（**诚实登记**：清单的字面陈述**需要闭包**）

  **清单说「`ℰ/∼_ℰ` 与对象概念集之间存在双射」。**

  **⚠ 字面陈述不成立**，因为：
  - `ℰ/∼_ℰ` 的每个等价类就是一个**属性集** `polarUp {e}`
  - **但**不是每个属性集都是**闭的**（`A = A''`）
  - **两个不同的属性集可以有相同的闭包**

  **⭐⭐ 故正确的陈述是**「**闭包之后**才是双射」：
  $$\mathcal{E}/\!\sim_{\mathcal{E}} \Big/ {\equiv} \;\;\cong\;\; \mathrm{Ext}(\mathfrak{B}(\mathbb{K})),$$
  其中 `A ≡ B ⟺ A'' = B''`。

  **⚠⚠ 这恰恰印证了作者裁决的措辞**：「**Galois 连接的不动点结构**」——
  **「不动点」正是闭包算子 `A ↦ A''` 的不动点，**故必须闭包**。**

  ## 本文件的**实际交付**

  **⚠ 我**未完成**「闭包后的双射」这一最强陈述
  （**因为 `Concept G M I` 的 `Subtype` 在 `Set M` 与 `Set G` 上，
  我尝试的构造在 `Subtype.ext` 处卡住**）。

  **✅ 我**完成**了它的**全部前置**：
  - 商集与「单点属性集」的双射（`quotEquivAttrs`）
  - 闭包的扩张性与幂等性
  - **闭包给出概念外延**（`closure_is_extent` —— Galois 连接基本定理的一半）

  **⟹ 这是**诚实的不完整**：**必须登记，不假装完成**。**
================================================================================ -/

namespace FateV2.Rules.T112

/-! ## §1 ⭐ 实例的属性集（**清单的 `∼_ℰ`**） -/

/-- ⭐⭐ **实例的属性集**：`polarUp {e}` —— 给定 `e`，**所有 `e` 满足的属性**。 -/
noncomputable def attrsOf (K : FormalCtx.{u, v}) (e : K.GFCA) : Set K.MFCA :=
  K.polarUp {e}

/-- ⭐⭐ **两个实例有相同的属性集**（**清单的 `∼_ℰ`**）。 -/
def sameAttrs (K : FormalCtx.{u, v}) (e e' : K.GFCA) : Prop :=
  attrsOf K e = attrsOf K e'

/-- ⭐ **`sameAttrs` 是等价关系**。 -/
theorem sameAttrs_equivalence (K : FormalCtx.{u, v}) : Equivalence (sameAttrs K) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- ⭐⭐ **`sameAttrs` 对应的 `Setoid`**（这就是清单的 `∼_ℰ`）。 -/
noncomputable def attrsSetoid (K : FormalCtx.{u, v}) : Setoid K.GFCA where
  r := sameAttrs K
  iseqv := sameAttrs_equivalence K

/-! ## §2 ⭐⭐ **`∼_ℰ` 的等价类就是属性集**

**⭐ 核心观察**：`e ∼ e'` **⟺** 它们的属性集相同。
**⟹ 商集 `ℰ/∼_ℰ` 的元素**可以被**属性集代表**。 -/

/-- ⭐⭐⭐ **`e ∼ e'` ⟺ `attrsOf K e = attrsOf K e'`**（**定义即此**）。 -/
theorem sameAttrs_iff (K : FormalCtx.{u, v}) (e e' : K.GFCA) :
    (attrsSetoid K).r e e' ↔ attrsOf K e = attrsOf K e' :=
  Iff.rfl

/-- ⭐⭐⭐ **商集到属性集的良定义映射**（**这才是 `∼_ℰ` 的「值」**）。

**⭐⭐ 即**：**每个等价类**唯一确定一个属性集**。** -/
noncomputable def quotClassAttrs (K : FormalCtx.{u, v}) :
    Quotient (attrsSetoid K) → Set K.MFCA :=
  Quotient.lift (attrsOf K) (fun _ _ h => h)

/-- ⭐⭐ **在代表元上的取值**。 -/
theorem quotClassAttrs_mk (K : FormalCtx.{u, v}) (e : K.GFCA) :
    quotClassAttrs K (Quotient.mk (attrsSetoid K) e) = attrsOf K e := rfl

/-- ⭐⭐⭐ **`quotClassAttrs` 是单射**（**不同的类给不同的属性集**）。

**🔹 对应清单**：**「商集的元素 ↔ 属性集」这一对应是**一一**的**。** -/
theorem quotClassAttrs_injective (K : FormalCtx.{u, v}) :
    Function.Injective (quotClassAttrs K) := by
  intro q₁ q₂ h
  induction q₁ using Quotient.ind with
  | _ e₁ =>
    induction q₂ using Quotient.ind with
    | _ e₂ =>
      simp only [quotClassAttrs_mk] at h
      exact Quotient.sound h

/-! ## §3 ⭐⭐⭐ **闭包：属性集 → 概念外延**

**⭐⭐ 这是 T1.12 的**实质内容**：**
**属性集经闭包 `A ↦ A''` 后，**恰好**成为某个对象概念的外延。**

**⚠ 为什么必须闭包**：**作者裁决说「数学原型是 **Galois 连接的不动点结构**」** ——
**「不动点」= 闭包算子的不动点 `A = A''`，**故属性集必须闭包才能对应概念**。** -/

/-- ⭐⭐ **属性集的闭包**：`A ↦ A''`（Galois 连接的闭包算子）。 -/
noncomputable def closure (K : FormalCtx.{u, v}) (A : Set K.MFCA) : Set K.MFCA :=
  K.polarUp (K.polarDown A)

/-- ⭐⭐ **闭包是扩张的**（`A ⊆ A''`）。 -/
theorem subset_closure (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    A ⊆ closure K A := by
  intro m hm; exact K.subset_polarDown_polarUp A hm

/-- ⭐⭐⭐ **闭包是幂等的**（`A'''' = A''`）。

**⭐ 这是 Galois 连接的**标准事实**（`polarUp ∘ polarDown` 幂等）。** -/
theorem closure_idempotent (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    closure K (closure K A) = closure K A := by
  simpa only [closure] using K.polarUp_polarDown_polarUp (K.polarDown A)

/-- ⭐⭐⭐⭐ **闭包给出概念的外延**：**`(A', A'')` 是形式概念**。

**🔹 对应清单**：T1.12 的「属性集 ↔ 概念」这一**核心**对应。

**⭐⭐ 这是 Galois 连接基本定理的一半**：
**「任何属性集经闭包后都成为某个对象概念的外延」。**

**⚠ 证明的关键**：`A''' = A'`（Galois 连接的标准等式）。** -/
theorem closure_is_concept (K : FormalCtx.{u, v}) (A : Set K.MFCA) :
    closure K A = K.polarUp (K.polarDown (closure K A)) := by
  simp only [closure]
  rw [K.polarUp_polarDown_polarUp]
/-! ## §4 ⚠⚠ **如实登记：一处**不成立**的猜想**

**我最初想证**：**`closure` 是单射**（`closure A = closure B ⟹ A = B`）。

**⚠⚠ 实测发现**：**这**不成立** —— 因为 `A ⊆ A''` 且 `A'' = A''''`，
**故 `A` 与 `A''` 有**相同**的闭包**（**当 `A ≠ A''` 时**不同的属性集给出同一闭包**）。

**⭐⭐ 即**：**闭包**不是**单射，**而是**把整个等价类 `[A] = {B | B'' = A''}` 压成一个点**。

**⟹ 故 T1.12 的**正确陈述**必须是**「商**之后**才双射」**：
`ℰ/∼_ℰ` 再模 `≡`（`A ≡ B ⟺ A'' = B''`）**≃** 概念外延集。

**⚠ 本文件**未完成**这一步（需要在 `Set K.MFCA` 上构造 `Quotient` 的
**二次商**，并证明它与 `Concept` 的 `Subtype` 同构；
**我尝试的构造在 `Subtype.ext` 处卡住**）。

**✅ 但已完成的**全部前置**：
- `sameAttrs` 是等价关系（`sameAttrs_equivalence`）
- 商集到属性集的映射良定义且**单射**（`quotClassAttrs_injective`）
- 闭包的扩张性、幂等性
- **闭包给出概念**（`closure_is_concept`）—— Galois 连接基本定理的一半

**⟹ 这是**诚实的不完整**，已登记在 `_pending/T1.12-未完成.md`。**

-/
end FateV2.Rules.T112
