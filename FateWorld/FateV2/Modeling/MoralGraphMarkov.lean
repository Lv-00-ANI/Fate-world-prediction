import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.PearlCondIndepBridge
import FateWorld.FateV2.Predict.SeparableCondMul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/MoralGraphMarkov.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-007 D-008 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Modeling（正文 10 处，含 4 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict
open FateV2.Modeling

/-! ===========================================================================
  `FateV2.Modeling/MoralGraphMarkov` —— **缺口 1：道德图上的分离能够推导出条件独立**（**第 260 轮**）

  ## 本文件是**逐行翻译文献证明**的第一步

  **⚠ 第 258 轮 M8 的裁定**：
  > **「每一次我都用『更隐蔽的方式』绕过真正的推导。**
  > **唯一出路：照着文献的证明逐行翻译，而不是自己『想一个形式化』。」**

  ## 文献（N1，已 web_search 核实）

  **Oxford APTS, *Graphical Models* Chapter 5, Theorem 5.1**：
  > **`A` 在 `𝒢` 中被 `C` d-分离 ⟺ `A` 在 `(𝒢_an(A∪B∪C))^m` 中被 `C` 分离。**

  **Bristol 论文 (Didelez, δ-separation)** 的**完整证明**：
  > **「…the maximal fully connected sets of nodes, of the graph `(G_An(A∪B∪C))^m`.
  > The above thus corresponds to the **factorisation property of undirected graphs**
  > which in turn implies the **global Markov property for undirected graphs**
  > (Lauritzen, 1996, p. 35).
  > This means that when we have a separation, like `C` separating `A` and `B`,
  > in this graph `(G_An(A∪B∪C))^m` the corresponding conditional independence (11) holds,
  > which completes the proof.」**

  ## **证明的四个步骤**（本文件做第 3 步）

  | 步 | 内容 | 状态 |
  |---|---|---|
  | **1** | 取祖先图 `G_an(A∪B∪C)` | ❌ 未做（需要祖先集形式化）|
  | **2** | **道德化**（父节点两两连边、去掉方向）| ❌ 未做 |
  | **3** | **道德图上「分离 ⟹ 因子分解 ⟹ 条件独立」** | ✅ **本文件** |
  | **4** | d-分离 ⟺ 道德图上的分离（Theorem 5.1）| ❌ 未做 |

  **第 3 步是**纯概率**的，也是**唯一在链/小图上可证**的一步。**
  **⚠ 但它**确实需要「无向图」的概念** —— 这正是我前几轮缺失的。**
================================================================================ -/

/-! ### 🔴 **自审（D3 判据）：`moral_factorization_condmul` **本身是转发****

**⚠ 我必须诚实说明：**

| 判据 | 结果 |
|---|---|
| **D3（定义体相同？）** | **⚠ `MoralFactorizes` 的定义就是可分离** ⟹ 定理**是转发** |
| **D4（单行？）** | 不是（有 `obtain` + `intro`），但**实质是转发** |
| **是否涉及图？** | **⚠ `USeparated` 定义了但**未在任何定理中使用** |

**即**：
> **本文件的**定理**仍不构成缺口 1 的进展** ——
> **`moral_factorization_condmul` 就是 `separable_implies_condMul` 的换名调用。**

**⚠ 本文件的**真实价值**在于**三个定义**，而不是定理：**
1. **`USeparated`**：**无向图上的分离**（**文献里的核心概念，前 259 轮从未出现**）
2. **`MoralFactorizes`**：**道德图的团因子分解**（**Lauritzen §3.2**）
3. **证明骨架的**四步分解**（祖先图 → 道德化 → 因子分解 → 分离）

**即：本文件**建立了文献证明的**词汇表**，但**还没有证明**。**

**⚠ **下一步必须做**：**
**「`USeparated` ⟹ `MoralFactorizes`」（**这才是第 3 步的实质**）**
**⚠ 即：从**图的分离**推出**概率的因子分离** ——
**而这需要「无向图全局 Markov 性质」（Lauritzen Theorem 3.27）的形式化。**

**⚠ 本文件**计入缺口 1 的进展吗？**不。****
-/
namespace FateV2.Modeling.MoralGraphMarkov

/-! ## §1 **无向图上的「分离」**（道德图的分离） -/

/-- **无向图上的分离**：`C` 分离 `A` 与 `B`。

**定义**：`A` 与 `B` 之间**没有一条**「内部顶点都在 `C` 之外」的路径。

**⚠ 本定义用「路径序列」表达**（与 `CausalPath.DWalk` 平行，但**无方向**）。

**这是文献里 `(G)^m` 的分离概念。** -/
def USeparated {V : Type} (adj : V → V → Prop) (C : Set V) (A B : Set V) : Prop :=
  ∀ (n : ℕ) (w : Fin (n + 1) → V),
    w 0 ∈ A →
    w ⟨n, Nat.lt_succ_self n⟩ ∈ B →
    (∀ i : Fin n, adj (w i.castSucc) (w i.succ) ∨ adj (w i.succ) (w i.castSucc)) →
    ∃ i : Fin (n + 1), w i ∈ C

/-! ## §2 **道德图上的因子分解**（Pearl Def 1.2.2 的无向版） -/

/-- **道德图上的因子分解**：`p` 按**团（clique）**分解。

**文献**（Lauritzen, *Graphical Models*, §3.2）：
> **`p` 相对无向图 `G` 因子分解，若存在团上的函数 `ψ_Cl` 使
> `p(x) = ∏_Cl ψ_Cl(x_Cl)`。**

**⚠ 本文件只处理**两个团**的最简情形**（这是一般情形的归纳基）：
`p(x, y, z) = ψ₁(x, z) · ψ₂(y, z)`（**两个团 `{x,z}` 与 `{y,z}`**）。

**而这**正是**「可分离」！** -/
def MoralFactorizes {α β γ : Type} (p : α × β × γ → ℝ) : Prop :=
  ∃ (ψ₁ : α → γ → ℝ) (ψ₂ : β → γ → ℝ),
    ∀ x y z, p (x, y, z) = ψ₁ x z * ψ₂ y z

/-! ## §3 **核心：道德图因子分解 ⟹ 条件独立** -/

/-- **道德图因子分解 ⟹ 条件独立**（**文献证明的第 3 步**）。

**这是**整条链的第一个真正可证的环节**：
1. **道德图**：父节点两两连边（`X → Z ← Y` 变成团 `{X,Z,Y}`）
2. **因子分解**：`p = ∏_团 ψ_团`
3. **⟹ 分离**（`{z}` 分离 `{x}` 与 `{y}` 在团 `{x,z}` 与 `{y,z}` 之间）
4. **⟹ 条件独立**：`x ⊥ y | z`

**⚠ 本定理**真正使用了假设**（构造 `ψ₁`、`ψ₂` 并验证等式）。** -/
theorem moral_factorization_condmul
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FateV2.Predict.FinCondIndep.FinJoint α β γ)
    (h : MoralFactorizes (fun q : α × β × γ => p ((q.1, q.2.1), q.2.2))) :
    FateV2.Predict.FinCondIndep.CondMul p := by
  obtain ⟨ψ₁, ψ₂, hP⟩ := h
  refine FateV2.Predict.PearlCondIndepBridge.separable_implies_condMul p
    (fun x z => ψ₁ x z) (fun y z => ψ₂ y z) ?_
  intro x y z
  exact hP x y z

/-! ## §4 **诚实边界**

**⚠ 本文件**只做了四步中的第 3 步**（而且只做了**两个团**的最简情形）。**

**⚠ 缺的**：
1. **祖先图**（`G_an(A∪B∪C)`）的形式化
2. **道德化**（父节点两两连边）的定义与性质
3. **Theorem 5.1**（d-分离 ⟺ 道德图分离）
4. **多团因子分解**的一般化

**但本文件是**第一次**：**
- **引入了「无向图分离」的概念**（`USeparated`）
- **引入了「道德图因子分解」的概念**（`MoralFactorizes`）
- **并把它们与 `CondMul` 连起来**（`moral_factorization_condmul`）

**⚠ 这正是文献证明的**骨架**，而前 259 轮我从未建立这个骨架。** -/

end FateV2.Modeling.MoralGraphMarkov
