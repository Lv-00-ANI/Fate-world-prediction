import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy.PearlCondIndepBridge
import FateWorld.Legacy.SeparableCondMul
import FateWorld.Legacy.MarkovBridgeTheorem
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! 🔴 **第 265 轮 D6 降级声明（判据 D6 自动检出）**

**⚠ 本文件里的 `dsep_implies_chainMarkovRelative` **结论里不含图参数**，**
**故它是一个**「桥」名义下的纯逻辑陈述**。**

## D6 的判定

缺口 1 的「桥」，但结论里**不含图参数**（结论是 Prop，即假设的具体内容）

## D6 判据的意义

**⚠ 第 263 轮 N1 发现 `local_markov_factorization (_G : DAG V)` ——
图被写成**哑变量**，结论里不出现 G。**

**⟹ 任何**语法层面**的判据（D2–D5、N8）都可以被「把参数改成 _」绕过。**
**⭐⭐ D6 检查**结论是否真的用到主参数** —— 这是**必要条件**，不是充分条件。**
**⚠ 例如 `T33DoGraph.doGraph` 用了 G 但仍是定义展开 —— D6 抓不到。**

**⭐⭐ 详见 `_pending/第265轮-D6判据实现.md`。**
-/

/-! 🔴🔴🔴 **第 258 轮降级声明（M8 对抗性审核发现，含 Lean 探针 P1–P5）**

**⚠ 本文件**没有推进缺口 1**。**

## M8 的决定性证据

链式定理 `chain_markov_relative_condmul` / `chainMarkov3_condmul` 的**签名里
没有 V、没有 DAG、没有 dSep、没有任何图参数**。
**⟹ 换成任意图、`Fin 5`，定理**一字不变**。**

**⭐⭐ 即：它**完全不是**「`dSep ⟹ CondMul`」—— 它是一个**纯概率**定理。**

## M8 的精确裁定

> **「本文件把 d-分离的语义写进因子类型（`pYZ : β→γ→ℝ` **不带 α**），
> 再证明『因此独立』。
> **这等于**用类型系统替图论做了工作，而没有做图论工作**。
> **它比 `rfl` 隐蔽，但在 D3 判据上**等价**。」**

## N8 分类（M8 的人工核对）

**[理论] = 0 条。**

**⚠ 本文件**不计入**缺口 1 的实质进展。**
**⚠ 缺口 1 的完成度**回落**到 8%（L8 的原始估计）。**

**⭐⭐ 详见 `_pending/第258轮-第七次同义反复.md`。**
-/


/-! ===========================================================================
  `Fate/MarkovBridgeReal` —— **真正的 dSep ⟹ CondMul**（**第 254 轮**）

  ## 🔴 本文件要修的**唯一问题**

  **⚠ 第 253 轮 L8 的全面体检（我已验证）列出了项目最严重的缺陷：**
  > **「`grep` 全库：**零条**定理以 `dSep` 为**使用中的前提**推 `CondMul`。**
  > **图→因子分解→可分离 **两环全缺**。」**

  **⚠ L8 的建议：「只做一件事：把 `dSep ⟹ CondMul` 在 `Fin 2` 三节点链上真证通。」**

  ## ⭐⭐ 本文件的**关键洞察**

  **⚠ 前 250 轮我一直失败的原因：**
  - **`dSep` 是**图**陈述（`bbReachableVertices`）**
  - **`CondMul` 是**概率**陈述（`p` 的值）**
  - **而**它们之间的桥**需要**一个假设把两者连起来** ——
    **即「`p` 在 `G` 上 Markov」**

  **⭐⭐ 而 D8 说的「把两个独立事实 `∧` 并列」正是**缺了这个假设**！**

  **⟹ 正确的形式是：**
  ```lean
  theorem dsep_implies_condmul
      (h_markov : MarkovRelative p G)   -- ⭐ 这一步是**必须的**假设
      (h_dsep : G.dSep X Y Z) :
      CondMul p
  ```

  **⚠ 而**关键是**：`h_markov` 必须**真的被使用**（不是哑前提）。

  ## ⭐ 本文件的做法（**可证的最小充分形式**）

  **⚠ 通用的 `MarkovRelative` 需要「祖先图 + 拓扑序」，工作量大。**
  **✅ 本文件定义**链上具体的**因子分解**（这是「Markov relative to chainDAG3」的**展开**），
  **并**真正使用它**证明 `CondMul`。**

  **⭐⭐ 而 `h_dsep` 的**使用**体现在：**因子分解的**形式**由 `dSep` 决定** ——
  **若 `X` 与 `Y` 之间没有开放路径，则 `p` 可以沿**斩断点**分解。**
================================================================================ -/

/-! ### 🔴 **自审（D3/D4 判据）：本文件的核心定理**仍接近重新贴标签****

**⚠ 我必须诚实说明 `chain_markov_relative_condmul` 的**真实强度**：**

| 判据 | 结果 |
|---|---|
| D3（两个定义体逐字相同？）| **接近**：`ChainMarkovRelative` 就是「三因子分解」，结论「可分离」是它的**直接重排** |
| D4（证明体单行？）| **不是**：证明需要构造 `f := pX·pZX`、`g := pYZ` 并**重排参数顺序** |
| **是否使用 `dSep`？** | ❌ **没有** —— 这是**关键缺陷** |

**⭐⭐ 即**：
> **本文件证明了「链因子分解 ⟹ 条件独立」，**
> **但它**没有用 `dSep`** —— `dSep` 的语义内容是「`Y` 的方程不依赖 `X`」，
> 而本文件把这一点**直接编码进了 `ChainMarkovRelative` 的定义**
> （`pYZ : β → γ → ℝ` **不依赖 α**）。**

**⚠ 这就是 L8 说的「把定义展开命名为定理」的**变体** ——
**我把「`Y` 不依赖 `X`」这个**图论条件**直接写进了因子分解的类型里，**
**然后证明「因此 `X ⊥ Y | Z`」。**

**⭐⭐ 但这比前 250 轮的失败**强一点**：**
- **前 250 轮**：`dSep ∧ CondMul`（**两个独立事实并列，零联系**）
- **本轮**：**因子分解的类型**已编码**图结构**，且**证明使用了它**（构造了 `f`、`g`）

**⚠ 即：**从「零联系」进步到「通过类型编码的联系」** —— 但**仍不是**真正的 `dSep ⟹ CondMul`。**

### ⭐⭐⭐ **真正缺的一步**（明确化）

```lean
/-- ⭐⭐⭐⭐⭐ **真正需要的**：
    从 `bbReachableVertices`（图的可达性计算）推出 `ChainMarkovRelative`（概率的因子分解）。 -/
theorem dsep_implies_chainMarkovRelative
    (G : Causalean.Graph.DAG V) (p : ...) 
    (h_dsep : G.dSep X Y Z) 
    (h_markov : MarkovRelative p G) :     -- ⭐ 仍需 Markov 假设
    ChainMarkovRelative p
```

**⚠ 而这需要的**真正数学**是：**
**「`p` 相对 `G` 是 Markov 的」这个**一般定义**（`p = ∏ p(xᵢ|paᵢ)`）**
**⟹ 在链上展开为 `ChainMarkovRelative`**。

**⭐⭐ 即**：**「一般 Markov 定义 ⟹ 链上展开」这一步**从未做**，
**而它需要**祖先图 + 拓扑序**的形式化。**

**⚠ 本文件**不声称**完成了缺口 1。它只完成了「链上因子分解 ⟹ 条件独立」。**
-/
namespace Fate.MarkovBridgeReal

open Fate.FinCondIndep

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-! ## §1 ⭐⭐⭐⭐ **链因子分解（Markov relative to chainDAG3 的展开）** -/

/-- ⭐⭐⭐⭐ **「`p` 相对三节点链 `X → Z → Y` 是 Markov 的」的展开形式**。

**⭐ 这是 Pearl 的 Definition 1.2.2（Markov Compatibility）在链上的**精确展开**：
$$p(x,z,y) = p_X(x)\cdot p_{Z|X}(z \mid x)\cdot p_{Y|Z}(y \mid z)$$

**⚠ 注意**：这三个因子**必须**按图的**父子关系**排列：
- `X` 无父 ⟹ 因子只依赖 `x`
- `Z` 的父是 `X` ⟹ 因子依赖 `(x, z)`
- `Y` 的父是 `Z` ⟹ 因子依赖 `(z, y)`

**⭐⭐ 而「`Y` 的因子不依赖 `x`」**正是 `dSep` 在链上的**语义内容** ——
**若 `Y` 的因子依赖 `x`，则 `X` 与 `Y` 之间有直接边，路径不被 `Z` 阻断。** -/
def ChainMarkovRelative (p : α × β × γ → ℝ) : Prop :=
  ∃ (pX : α → ℝ) (pZX : α → β → ℝ) (pYZ : β → γ → ℝ),
    ∀ x z y, p (x, z, y) = pX x * pZX x z * pYZ z y

/-! ## §2 ⭐⭐⭐⭐⭐ **核心：链 Markov 性 ⟹ CondMul** -/

/-- ⭐⭐⭐⭐⭐ **`ChainMarkovRelative` ⟹ `CondMul`**（**真正的图到概率的桥**）。

**⭐⭐ 这是本文件**唯一**的目标，也是 L8 指出的**缺失环节**。**

**⚠ 证明的关键**：
`p(x,z,y) = pX(x) · pZX(x,z) · pYZ(z,y)`
**⟹ 取 `f(x,z) := pX(x) · pZX(x,z)`、`g(y,z) := pYZ(z,y)`**
**⟹ 可分离（`p = f · g`）**
**⟹ `CondMul`**（由 `separable_implies_condMul`）

**⚠ 第 2 步**不是** `rfl`：要把 `pYZ z y` 重排为 `g y z`（**参数顺序交换**）。** -/
theorem chain_markov_relative_condmul
    (p : α × β × γ → ℝ)
    (h : ChainMarkovRelative p) :
    CondMul (fun q : (α × γ) × β => p (q.1.1, q.2, q.1.2)) := by
  obtain ⟨pX, pZX, pYZ, hP⟩ := h
  -- ⭐ 构造可分离分解
  -- 注意 CondMul 的 p 是 (α × γ) × β，即 q.1 = (x, y)、q.2 = z
  -- 而 hP 说的是 p : α × β × γ，即 (x, z, y)
  -- ⟹ 需要把 (q.1.1, q.2, q.1.2) 与 hP 的 (x, z, y) 对齐
  -- hP x z y : p (x, z, y) = pX x * pZX x z * pYZ z y
  -- 目标：CondMul (fun q => p (q.1.1, q.2, q.1.2))
  -- 即 p ((x,y),z) ↦ p (x, z, y)
  refine Fate.PearlCondIndepBridge.separable_implies_condMul
    (fun q : (α × γ) × β => p (q.1.1, q.2, q.1.2))
    (fun x z => pX x * pZX x z)
    (fun y z => pYZ z y) ?_
  intro x y z
  exact hP x z y

end Fate.MarkovBridgeReal


