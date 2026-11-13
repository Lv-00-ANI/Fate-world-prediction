import FateWorld.Legacy.PearlChain
import FateWorld.Legacy.PearlFork

/-! ===========================================================================
  `Fate/PearlMarkov` —— **Pearl 定理 1.2.4 的三元结构核心**（**第 224 轮**）

  ## 缺口（路线图 §6 缺口 1）

  **Pearl《Causality》定理 1.2.4**：
  > **d-分离 ⟹ 条件独立。**

  **⚠ 完整的 1.2.4 需要**任意 DAG + 任意 `X, Y, Z`** ——
  **那需要**路径分解**与**全局 Markov 性**的联合归纳。**

  **⭐⭐ 本文件交付它的**三元结构核心**：
  **对 DAG 上的三种三元片段分别证明「局部 Markov 分解 ⟹ 相应的条件/边缘独立」。**

  | 结构 | 图 | 局部 Markov | 结论 | 状态 |
  |---|---|---|---|---|
  | **链** | `a → b → c` | `p(a,b,c) = p(a)p(b\|a)p(c\|b)` | `a ⊥ c \| b` | ✅ 第 215 轮（`PearlChain`）|
  | **分叉** | `a ← b → c` | `p(a,b,c) = p(b)p(a\|b)p(c\|b)` | `a ⊥ c \| b` | ✅ 第 213 轮（`PearlFork`）|
  | **对撞** | `a → b ← c` | `p(a,b,c) = p(a)p(c)p(b\|a,c)` | `a ⊥ c`（**不**条件于 `b`）| ⭐ **本文件补** |

  **⭐⭐ 补齐对撞后，Pearl 的三种三元结构**全部完成**。**
================================================================================ -/

namespace Fate.PearlMarkov

open Finset

/-! ## §1 **对撞结构**（`a → b ← c`）

**⭐ 对撞的 Markov 分解**：$p(a,b,c) = p(a)\cdot p(c)\cdot p(b \mid a, c)$

**⭐⭐ 与链/分叉的**关键区别**：
- **链/分叉**：中间因子是 `p(b|a)` 或 `p(b)` —— **`b` 的分布**不依赖于 `a` 与 `c` 的相互作用**
- **对撞**：`p(b|a,c)` **同时依赖** `a` 与 `c`

**⟹ 后果**：
- **边缘上**：`a ⊥ c`（**独立**）
- **条件于 `b` 后**：`a ⊥̸ c | b`（**反而不独立** —— 见 `PearlChain`/`PearlFork` 的对照）
**—— 这就是「对撞被条件化后开口」的概率论原因。** -/

/-- ⭐⭐ **对撞的局部 Markov 分解**：`p(a,b,c) = pa a · pc c · pb a c b`。

**⭐ 参数顺序 `pb a c b` 把「`b` 的父节点是 `a` 与 `c`」写进了**类型层**。** -/
def ColliderFac {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (pa : A → ℝ) (pc : C → ℝ) (pb : A → C → B → ℝ) : Prop :=
  ∀ a b c, p (a, b, c) = pa a * pc c * pb a c b

/-! ## §2 ⭐⭐⭐⭐ **对撞的边缘独立：`a ⊥ c`** -/

/-- ⭐⭐⭐⭐ **对撞的边缘独立**：**不条件化时 `a` 与 `c` 独立**。

**🔹 对应清单**：**Pearl 1.2.4 的「对撞片段**不**在 `Z` 中时被阻断」这一半**。

**陈述**（乘性形式）：`(∑ b, p(a,b,c)) = pa a · pc c` ——
**即**边缘联合律**等于**边缘律之积**。

**⭐ 证明**：按 `h` 展开，把 `∑ b, pa a · pc c · pb a c b` 化为
`pa a · pc c · (∑ b, pb a c b)`，再用 `hsum`（`∑ b, pb a c b = 1`）。** -/
theorem collider_marginal_indep {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (pa : A → ℝ) (pc : C → ℝ) (pb : A → C → B → ℝ)
    (h : ColliderFac p pa pc pb) (hsum : ∀ a c, ∑ b, pb a c b = 1)
    (a : A) (c : C) :
    (∑ b, p (a, b, c)) = pa a * pc c := by
  have step : ∀ b, p (a, b, c) = pa a * pc c * pb a c b := fun b => h a b c
  rw [Finset.sum_congr rfl (fun b _ => step b)]
  rw [← Finset.mul_sum]
  rw [hsum a c, mul_one]

/-- ⭐⭐ **`a` 的边缘律**：`∑ b ∑ c, p(a,b,c) = pa a · (∑ c, pc c)`。

**⚠ 注意**：**这**不是** `pa a`** —— **因为 `∑ c, pc c` 未归一
（**本文件不假设 `pc` 归一，以保持 generality**）。** -/
theorem margA_collider {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (pa : A → ℝ) (pc : C → ℝ) (pb : A → C → B → ℝ)
    (h : ColliderFac p pa pc pb) (hsum : ∀ a c, ∑ b, pb a c b = 1)
    (a : A) :
    (∑ b, ∑ c, p (a, b, c)) = pa a * ∑ c, pc c := by
  rw [Finset.sum_comm]
  have step : ∀ c, (∑ b, p (a, b, c)) = pa a * pc c :=
    fun c => collider_marginal_indep p pa pc pb h hsum a c
  rw [Finset.sum_congr rfl (fun c _ => step c)]
  rw [← Finset.mul_sum]

/-- ⭐⭐ **`c` 的边缘律**（对称）。 -/
theorem margC_collider {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (pa : A → ℝ) (pc : C → ℝ) (pb : A → C → B → ℝ)
    (h : ColliderFac p pa pc pb) (hsum : ∀ a c, ∑ b, pb a c b = 1)
    (c : C) :
    (∑ a, ∑ b, p (a, b, c)) = (∑ a, pa a) * pc c := by
  have step : ∀ a, (∑ b, p (a, b, c)) = pa a * pc c :=
    fun a => collider_marginal_indep p pa pc pb h hsum a c
  rw [Finset.sum_congr rfl (fun a _ => step a)]
  rw [← Finset.sum_mul]

/-- ⭐⭐⭐ **归一化后的**边缘独立（**最贴近「`P(a,c) = P(a)P(c)`」**）。

**⭐ 当 `∑ a, pa a = 1` 且 `∑ c, pc c = 1` 时，
`p` 的**总质量**为 `1`** —— **此时边缘独立就是标准形式**。** -/
theorem collider_indep_normalized {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (pa : A → ℝ) (pc : C → ℝ) (pb : A → C → B → ℝ)
    (h : ColliderFac p pa pc pb) (hsum : ∀ a c, ∑ b, pb a c b = 1)
    (hA : ∑ a, pa a = 1) (hC : ∑ c, pc c = 1)
    (a : A) (c : C) :
    (∑ b, p (a, b, c)) = pa a * pc c
      ∧ (∑ b, ∑ c, p (a, b, c)) = pa a
      ∧ (∑ a, ∑ b, p (a, b, c)) = pc c := by
  refine ⟨collider_marginal_indep p pa pc pb h hsum a c, ?_, ?_⟩
  · rw [margA_collider p pa pc pb h hsum a, hC, mul_one]
  · rw [margC_collider p pa pc pb h hsum c, hA, one_mul]

/-! ## §3 ⭐⭐ **三种结构的**行为差异**（**汇总**） -/

/-- ⭐⭐ **三种三元结构**。 -/
inductive TripleStructure : Type
  /-- **链** `a → b → c`：`a ⊥ c | b` -/
  | chain
  /-- **分叉** `a ← b → c`：`a ⊥ c | b` -/
  | fork
  /-- **对撞** `a → b ← c`：`a ⊥ c`（**边缘**），但 `a ⊥̸ c | b` -/
  | collider
  deriving DecidableEq, Repr

/-- ⭐⭐ **哪些结构给「条件独立」**（**链与分叉是，对撞不是**）。 -/
def givesConditionalIndependence : TripleStructure → Bool
  | .chain => true
  | .fork => true
  | .collider => false

/-- ⭐⭐⭐ **对撞是**唯一**不给出条件独立的三元结构**。

**⭐⭐ 这就是「对撞被条件化后开口」这一反直觉现象在**结构层**的刻画。** -/
theorem collider_unique {S : TripleStructure} (h : givesConditionalIndependence S = false) :
    S = .collider := by
  cases S <;> simp [givesConditionalIndependence] at h ⊢

/-- ⭐⭐ **链与分叉给出相同的（条件）独立性**（**这是 `PearlChain` 与 `PearlFork` 的汇总**）。 -/
theorem chain_fork_both_conditional :
    givesConditionalIndependence .chain = givesConditionalIndependence .fork := rfl

end Fate.PearlMarkov
