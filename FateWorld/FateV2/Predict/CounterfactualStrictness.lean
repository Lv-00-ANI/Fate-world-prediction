import FateWorld.FateV2.Modeling.CFMap
/-!
  # Predict · CounterfactualStrictness

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CounterfactualStrictness.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CFMap
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §15  ⭐⭐ 反事实等价**严格弱于**相等（原 `_probe_q14` 的正式化）

  **来源**：探针 `probes/_probe_q14.lean`（**不在构建内**）。
  本节把它**正式化**为 `Fate/` 的一等公民 ——
  **消除 `Fate/CFMap.lean` 中「引用探针」这一弱 M5**。

  ## 问题

  $$\sim_{\text{cf}}\ \text{是否严格弱于}\ =\,?$$

  即：是否存在 $\mathcal F_1 \neq \mathcal F_2$ 但 $\mathcal F_1 \sim_{\text{cf}} \mathcal F_2$？

  ## ⭐ 结论：**是**（严格弱）

  **理由**：**反事实算子不是单射** ——
  它把 $\mathcal F$ 送到「个体 $u \mapsto$ 响应函数 $x \mapsto Y_x(u)$」，
  而该映射的**纤维可含多个不同的 $\mathcal F$**。

  **两个独立机制**：
  | 机制 | 说明 |
  |---|---|
  | **(A) 内部表示不唯一** | 反事实只读**给定输入处的取值**；定义域外/不可达分支任意不同 |
  | **(B) 隐变量边缘化** | 同分布实现同一观测机制，但结构函数坐标不同（Pearl §7.1）|

  **本节形式化 (A)** —— 它**不依赖概率、测度或隐变量**，故最坚固。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace CounterfactualStrictness

/-! ### §15.1 模型：结构方程 + 反事实不可见的自由度 -/

/-- ⭐ **拓展模型 𝓕**：一条结构方程 `mech`（反事实**可见**部分），
外加一个**反事实不可见**的标签 `tag`。

**`tag` 代表**：机制内部表示、隐变量编码、非一致分支等 **L2 自由度**。 -/
structure FModel where
  /-- 观测/干预下真正被读取的结构方程（反事实的唯一输入）。 -/
  mech : ℕ → ℕ
  /-- 反事实**看不见**的内部自由度。 -/
  tag : Bool

/-- **反事实函数**：$x \mapsto Y_x$ —— **只**看 `mech`。 -/
def FModel.cfFun (F : FModel) : ℕ → ℕ := fun x => F.mech x

/-- ⭐ **反事实等价** $\sim_{\text{cf}}$：反事实函数逐点相同。

**⚠ 关键**：它**只比较 `cfFun`**，**不比较 `tag`** ——
这正是「反事实视野小于 𝓕 的自由度」的形式化。 -/
def FModel.CounterfactualEquivalent (F F' : FModel) : Prop :=
  F.cfFun = F'.cfFun

/-! ### §15.2 ⭐ 反事实等价是等价关系 -/

theorem cfEquiv_refl (F : FModel) : F.CounterfactualEquivalent F := rfl

theorem cfEquiv_symm {F F' : FModel}
    (h : F.CounterfactualEquivalent F') : F'.CounterfactualEquivalent F := h.symm

theorem cfEquiv_trans {F F' F'' : FModel}
    (h₁ : F.CounterfactualEquivalent F') (h₂ : F'.CounterfactualEquivalent F'') :
    F.CounterfactualEquivalent F'' := h₁.trans h₂

/-! ### §15.3 ⭐⭐ 主定理：严格弱 -/

/-- ⭐ **相等 ⟹ 反事实等价**（「弱」的一半）。 -/
theorem eq_imp_cfEquiv {F F' : FModel} (h : F = F') :
    F.CounterfactualEquivalent F' := by
  subst h; rfl

/-- ⭐⭐ **反事实等价确实更粗**（反例存在）。

**构造**：`⟨id, true⟩` 与 `⟨id, false⟩` ——
**`mech` 相同**（故反事实逐字相同），**`tag` 不同**（故作为 𝓕 不相等）。 -/
theorem cfEquiv_not_imp_eq :
    ∃ F F' : FModel, F.CounterfactualEquivalent F' ∧ F ≠ F' :=
  ⟨⟨id, true⟩, ⟨id, false⟩, rfl, by simp⟩

/-- ⭐⭐ **主定理（严格弱，已证）**。

$$\bigl(\mathcal F = \mathcal F' \implies \mathcal F \sim_{\text{cf}} \mathcal F'\bigr)
  \ \wedge\
  \bigl(\exists \mathcal F \neq \mathcal F',\ \mathcal F \sim_{\text{cf}} \mathcal F'\bigr)$$

**⟹ 即**：$\sim_{\text{cf}}$ **严格弱于** $=$。 -/
theorem cf_strictly_weaker_than_eq :
    (∀ F F' : FModel, F = F' → F.CounterfactualEquivalent F') ∧
      (∃ F F' : FModel, F.CounterfactualEquivalent F' ∧ F ≠ F') :=
  ⟨fun _ _ h => eq_imp_cfEquiv h, cfEquiv_not_imp_eq⟩

/-! ### §15.4 ⭐ 这一结论与统一框架的关系 -/

/-- ⭐⭐ **本节的结论是 `KernelQuotientTheory` 一般理论的特例**。

**陈述**：`CounterfactualEquivalent` **正是** `cfFun` 的核。

**⟹ 即**：本节的「严格弱」结论**不是孤立的** ——
它就是「**核比相等更粗**」（`kernel` 的一般性质）在反事实场景的实例。

**⚠ 验证**：这里给出**逐字等价**，故可**直接引用**一般框架的定理。 -/
theorem cfEquiv_eq_kernel (F F' : FModel) :
    F.CounterfactualEquivalent F' ↔
      (fun F : FModel => F.cfFun) F = (fun F : FModel => F.cfFun) F' :=
  Iff.rfl

end CounterfactualStrictness

end FateV2.Predict