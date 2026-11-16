import FateWorld.FateV2.Predict.GlobalMarkovChainN
import FateWorld.FateV2.Predict.LawRuleCondMul
import FateWorld.FateV2.Predict.PearlCondIndepBridge
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
  # Predict · GlobalMarkovChainNConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GlobalMarkovChainNConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：GlobalMarkovChainN, LawRuleCondMul, PearlCondIndepBridge
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/GlobalMarkovChainN` 的**消费方**（P5 并行任务；一次只接一个模块）

  ## 0. 本文件只做一件事

  把 `Fate/GlobalMarkovChainN`（任意长度链的全局 Markov 性）的结论**接到下游**
  `LawRule` 规则层（`Fate/LawRuleCondMul` 的 `condMulRule` / `lawOf` / `compose`）。
  **不修改**目标模块一个字符。

  ## 1. 目标模块的实测声明（`grep -nE "^(theorem|def|noncomputable def)"`）

  | 类别 | 声明 |
  |---|---|
  | 图侧 | `chainDAG`、`chainDAG_dsep_2/3/4/5`、`chainDAG_not_dsep_empty_2/3/4`、`chainDAG_dsep_single_3` |
  | 剥因子 | `prod_univ_peel_last` |
  | 假设 | `ChainFac`（`ChainFac n f P := ∀ x, P x = ∏ i : Fin n, f i (x i.castSucc) (x i.succ)`）|
  | 装配器 | `build`、`build_eq`、`build_zero`、`build_at_last`、`build_at_m`、`build_mid`、`init_build` |
  | 核心 | `separable_of_chainFac`、**`chainFactor_condMul`**、**`chain_markov_general`**、`chain_markov_inductive`、`chain_markov_length_invariant` |
  | 相容 | `ChainMarkovHom`、`chainFac_of_chainMarkovHom` |
  | 反例 | `Pcol`、`pcol_eval`、`p2`、`margZ_p2`、`margXZ_p2`、`margYZ_p2`、`not_condMul_Pcol` |

  ## 2. 本文件给出的消费定理（4 条）

  记号：对 `ChainFac (m+1) f P`（`m ≥ 1`），把联合律重排成 `CondMul` 的载体

  ```
  chainJoint m P := fun q : (α × α) × (Fin m → α) => P (build m q.1.1 q.2 q.1.2)
  ```

  （`q.1.1 = x₀`、`q.1.2 = x_{m+1}`、`q.2 = (x₁,…,x_m)`）。

  | 编号 | 定理 | 消费了哪些结论 | 前件是否已含结论？（自查） |
  |---|---|---|---|
  | **C1** | `chain_lawRule_nonempty` | `chainFactor_condMul` + `LawRuleCondMul.condMul_iff_condMulRule_nonempty` | **否**。前件是**链式因子化**（`P` 等于 `n` 个二变量因子之积，一个关于 `P` 的**代数分解**假设）；结论是「规则允许集非空」。模块的 `ChainFac` 陈述里**没有 `CondMul` 字样**，二者是不同形状的命题（乘积分解 vs 乘性边缘等式）。 |
  | **C2** | `chain_lawOf_nonempty` | `chainFactor_condMul` + `condMul_iff_lawOf_nonempty` | **否**，同上；换 `univ` 型编码（全约束档）。 |
  | **C3** | `chain_compose_lawOf_nonempty` | **C2** + `lawOf_compose` | **否**。前件是 `ChainFac` **加上**一个任意的附加约束 `Q (chainJoint m P)`；结论是**合取规则**的允许集非空。**这验证了「链 Markov 性可以和别的规律同时成立」**——若前件已含结论，`Q` 就会是多余的，而 `Q` 在此是**自由变量**。 |
  | **C4** | `no_chainFac_of_Pcol` + `Pcol_lawRule_bot` | `chainFactor_condMul` + `not_condMul_Pcol` | **否**（这是**反例登记**）。前件：`∃ f, ChainFac 2 f Pcol`（链式因子化**成立**的假设）。结论：`False`。即**「端点直接耦合的联合律不可能有链式因子化」**。⟹ 这是「`ChainFac` 不可弱化成仅 `n` 顶点」的**规则层登记**。 |

  ## 3. 诚实边界

  * **C1/C2/C3 的数学内容全部来自目标模块**（`chainFactor_condMul`）。
    本文件**只做形状搬运**：把 `CondMul (chainJoint m P)` 送进
    `LawRuleCondMul` 的两个已证等价（`condMul_iff_condMulRule_nonempty`、
    `condMul_iff_lawOf_nonempty`）与 `lawOf_compose`。
    **我不声称这些是深刻的**——它们是**接入**，价值在于
    「任意长度链的 Markov 性现在是 `LawRule` 层可用的规则」。
  * **C4 是新内容**：模块只证了 `¬ CondMul p2`；本文件把它提升为
    **「不存在任何 `f` 使 `ChainFac 2 f Pcol`」**（这需要 `chainFactor_condMul`，
    是模块内部的消费，不是模块里的现成定理），并进一步落到
    「该联合律的规则允许集为空」。
  * **本文件没有**把 `dSep` 前提接进 `LawRule`：模块 §9.2 第 2 条自己承认
    `dSep` 在推导中未被使用；本文件**不假装补上**这一点。
  * **无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

namespace FateV2.Predict
namespace GlobalMarkovChainN

namespace Consumer

open FateV2.Predict.FinCondIndep (FinJoint CondMul)

attribute [local instance] Classical.propDecidable

universe u

/-! ===========================================================================
  §1 把「链上的联合律」重排成 `CondMul` 的载体
  =========================================================================== -/

section Joint

variable {α : Type u} [Fintype α]

/-- ⭐ **链联合律在 `CondMul` 载体上的重排**（本文唯一的自定义 `def`）。

`P : (Fin (m+2) → α) → ℝ` 是链 `x₀ → x₁ → ⋯ → x_{m+1}` 上的联合律；
本定义把 $(x_0,\; x_{m+1};\; x_1,\dots,x_m)$ 打包成
`((x₀, x_{m+1}), (x₁,…,x_m))`，即 `CondMul` 要求的
「一对端点 × 中间整段」形状。

**⚠ 这是模块 `chainFactor_condMul` 结论里的那个 `fun q => …`，逐字相同**
（见 §2 的 `chainJoint_def`），故 §2 的定理都是它的**直接**消费。 -/
noncomputable def chainJoint (m : ℕ) (P : (Fin (m + 2) → α) → ℝ) :
    FinJoint α α (Fin m → α) :=
  fun q => P (build m q.1.1 q.2 q.1.2)

/-- ⭐ `chainJoint` 的定义展开（`rfl`，供与模块结论对形）。 -/
theorem chainJoint_def {β : Type u} (m : ℕ) (P : (Fin (m + 2) → β) → ℝ) :
    chainJoint m P = fun q : (β × β) × (Fin m → β) => P (build m q.1.1 q.2 q.1.2) :=
  rfl

/-- ⭐⭐ **主搬运引理：链式因子化 ⟹ `chainJoint` 满足 `CondMul`。**

**直接调用**模块的 `chainFactor_condMul`（同值域、`m ≥ 1`）。
这是本文件所有下游结论的**唯一数学入口**。 -/
theorem condMul_chainJoint (m : ℕ) (hm : 1 ≤ m) (f : Fin (m + 1) → α → α → ℝ)
    (P : (Fin (m + 2) → α) → ℝ) (h : ChainFac (m + 1) f P) :
    CondMul (chainJoint m P) := by
  rw [chainJoint_def]
  exact chainFactor_condMul m hm f P h

end Joint

/-! ===========================================================================
  §2 ⭐⭐⭐ C1 / C2 / C3：接到 `LawRule` 规则层
  =========================================================================== -/

section LawRuleLayer

variable {α : Type u} [Fintype α]

/-- ⭐⭐⭐ **C1：链式因子化 ⟹ 谓词型规则允许集非空**（`condMulRule` 档）。

前件：`ChainFac (m+1) f P`（`m ≥ 1`，即链至少 `2` 条边）。
结论：`(LawRuleCondMul.condMulRule (chainJoint m P) ⋆).Nonempty`。

**消费链**：`chainFactor_condMul` → `condMul_iff_condMulRule_nonempty`。
**读法**：任意长度链的 Markov 性，在规则层表现为「规则**允许**这个联合律」。 -/
theorem chain_lawRule_nonempty (m : ℕ) (hm : 1 ≤ m) (f : Fin (m + 1) → α → α → ℝ)
    (P : (Fin (m + 2) → α) → ℝ) (h : ChainFac (m + 1) f P) :
    (LawRuleCondMul.condMulRule (α := α) (β := α) (γ := Fin m → α)
        (chainJoint m P) PUnit.unit).Nonempty :=
  (LawRuleCondMul.condMul_iff_condMulRule_nonempty (chainJoint m P)).mp
    (condMul_chainJoint m hm f P h)

/-- ⭐⭐⭐ **C2：链式因子化 ⟹ 全约束型规则允许集非空**（`lawOf` 档）。

前件同 C1；结论是 `lawOf CondMul` 编码下的非空（允许集 = `univ`）。
**消费链**：`chainFactor_condMul` → `condMul_iff_lawOf_nonempty`。

**⚠ 与 C1 的差别只在编码档位**（`{δ⋆}` vs `univ`），
**数学内容相同**；保留两条是因为下游 `compose` 走的是 `lawOf` 档（见 C3）。 -/
theorem chain_lawOf_nonempty (m : ℕ) (hm : 1 ≤ m) (f : Fin (m + 1) → α → α → ℝ)
    (P : (Fin (m + 2) → α) → ℝ) (h : ChainFac (m + 1) f P) :
    (LawRuleCondMul.lawOf (CondMul (α := α) (β := α) (γ := Fin m → α))
        (chainJoint m P) PUnit.unit).Nonempty :=
  (LawRuleCondMul.condMul_iff_lawOf_nonempty (chainJoint m P)).mp
    (condMul_chainJoint m hm f P h)

/-- ⭐⭐⭐ **C3：链 Markov 约束可与任意其它规律同时成立**。

前件：
* `ChainFac (m+1) f P`（链式因子化，`m ≥ 1`），
* `Q (chainJoint m P)`（**任意**附加约束 `Q` 在该联合律上成立）。

结论：合取规则 `lawOf CondMul ∘ lawOf Q` 的允许集非空，
即「链 Markov 性 **∧** `Q`」是一条**不自相矛盾**的规律。

**消费链**：`lawOf_compose`（取交 = 合取）+ C2 的非空性。

**⚠ 前件没有把结论包进去**：`Q` 是自由的，结论要求的是
**合取规则**的非空性；若 `ChainFac` 已含此结论，则 `Q` 的位置无从解释。
本定理的实质是「`∘ = 取交` 语义下，链 Markov 性**不排他**」。 -/
theorem chain_compose_lawOf_nonempty (m : ℕ) (hm : 1 ≤ m)
    (f : Fin (m + 1) → α → α → ℝ) (P : (Fin (m + 2) → α) → ℝ)
    (h : ChainFac (m + 1) f P)
    (Q : FinJoint α α (Fin m → α) → Prop) (hQ : Q (chainJoint m P)) :
    (LawRuleCondMul.compose
        (LawRuleCondMul.lawOf (CondMul (α := α) (β := α) (γ := Fin m → α)))
        (LawRuleCondMul.lawOf Q)
        (chainJoint m P) PUnit.unit).Nonempty := by
  rw [LawRuleCondMul.lawOf_compose]
  have hC : CondMul (α := α) (β := α) (γ := Fin m → α) (chainJoint m P) :=
    condMul_chainJoint m hm f P h
  simp only [LawRuleCondMul.lawOf]
  simp [hC, hQ]

end LawRuleLayer

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ C4：反例登记 —— 端点直接耦合的律**不可能**有链式因子化
  =========================================================================== -/

section Counterexample

/-- ⭐⭐⭐⭐ **C4a：不存在任何二变量因子族使 `Pcol` 满足 `ChainFac 2`**。

`Pcol`（模块 §8）是 $P_{\text{col}}(x) = [x_0 = x_2]$ ——
**完全忽略中间变量、端点直接耦合**。

**证明**：若存在这样的 `f`，则由 `chainFactor_condMul`（`m = 1`）
得 `CondMul (chainJoint 1 Pcol)`；而 `chainJoint 1 Pcol` 与模块的 `p2`
**定义上相同**，与 `not_condMul_Pcol` 矛盾。

**⚠ 这不是 `not_condMul_Pcol` 的重述**：模块只证「`p2` 不条件独立」；
本定理证的是「**链式因子化本身不可能**」——
**把反例从「分布层的失败」升级为「结构假设的不可满足」**。 -/
theorem no_chainFac_of_Pcol :
    ¬ ∃ f : Fin 2 → Bool → Bool → ℝ, ChainFac 2 f Pcol := by
  rintro ⟨f, hf⟩
  have h := condMul_chainJoint (α := Bool) 1 le_rfl f Pcol hf
  have hp : chainJoint 1 Pcol = p2 := rfl
  rw [hp] at h
  exact not_condMul_Pcol h

/-- ⭐⭐⭐ **C4b：`Pcol` 的规则允许集为空**（反例在规则层的落地）。

`(condMulRule p2 ⋆).Nonempty` 为假 ——
即**链 Markov 规则会拒绝这个联合律**，正如它应当拒绝。
配合 C4a：拒绝不是「规则编码的偏好」，而是**该律确实没有链式因子化**。 -/
theorem Pcol_lawRule_bot :
    ¬ (LawRuleCondMul.condMulRule (α := Bool) (β := Bool) (γ := Fin 1 → Bool)
        p2 PUnit.unit).Nonempty := by
  intro hne
  exact not_condMul_Pcol
    ((LawRuleCondMul.condMul_iff_condMulRule_nonempty p2).mpr hne)

end Counterexample

/-! ===========================================================================
  §4 诚实总结
  =========================================================================== -/

/-!
## 4.1 本文件真做到的

| 定理 | 状态 |
|---|---|
| `chainJoint` / `chainJoint_def` | 定义 + `rfl` |
| `condMul_chainJoint` | ⭐⭐ 直接搬运 `chainFactor_condMul` |
| `chain_lawRule_nonempty` | ⭐⭐⭐ C1（`condMulRule` 档）|
| `chain_lawOf_nonempty` | ⭐⭐⭐ C2（`lawOf` 档）|
| `chain_compose_lawOf_nonempty` | ⭐⭐⭐ C3（合取规则）|
| `no_chainFac_of_Pcol` | ⭐⭐⭐⭐ C4a（反例：结构假设不可满足）|
| `Pcol_lawRule_bot` | ⭐⭐⭐ C4b（规则层拒绝）|

## 4.2 没做到的（诚实清单）

1. **`dSep` 前提仍未接入**。目标模块 §9.2 第 2 条自己承认 `dSep` 在
   `CondMul` 推导中未被使用；本文件**没有**假装补上，
   也没有把 `chainDAG_dsep_*`（仅 `n = 2..5`）当作一般 `n` 的图侧依据。
2. **没有输出到 `SCM` / `toLawRule`**。`SCM` 是单变量 `X → Y` 的结构方程，
   而链 Markov 性的载体是 `Fin (n+1) → α` 的**联合律**；
   把 `ChainFac` 实现为某个 `SCM` 需要「链上每个变量都有自己的结构方程」的多变量 `SCM`，
   `Fate/PearlHierarchy.lean` 的 `SCM` **不具备**该形状。**这是接不上的原因**，
   不是遗漏 —— 硬接会造出与模块陈述不符的空洞命题。
3. **C1/C2/C3 是形状搬运**，不含新数学（数学在 `chainFactor_condMul` 里）。
   我不声称它们是深刻结论。
4. **C4a 是新内容**（模块只有 `not_condMul_Pcol`，本文件升级为
   「无任何 `f` 使 `ChainFac`」），但它是**很短的推导**，价值在**反例登记**，
   不在难度。
-/

end Consumer

end GlobalMarkovChainN

end FateV2.Predict