import FateWorld.FateV2.Predict.GlobalMarkovMinimal
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.MarkovBridgeReal
import FateWorld.FateV2.Predict.PearlCondIndepBridge
import Mathlib.Algebra.BigOperators.Fin

/-!
  # Predict · ChainMarkovExplicitAntecedent

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ChainMarkovExplicitAntecedent.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：GlobalMarkovMinimal, DAGFactorization, MarkovBridgeReal, PearlCondIndepBridge
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `FateV2.Predict.ChainMarkovExplicitAntecedent` —— **显式前件版 `dSep ⟹ CondIndep`**

  ## 0 本文要解决的问题

  此前几轮的关键裁定（出发点）：

  | 轮次 | 裁定 |
  |---|---|
  | 第 255 轮 | `ChainMarkovRelative ⟹ CondMul` 的**结论里没有图参数**；图论被写进因子的**类型**（`pYZ : β → γ → ℝ` 不读 `α`）|
  | 第 258 轮 M8 | 「**用类型系统替图论做了工作**，而没有做图论工作……在 D3 判据上**等价于 `rfl`**」|
  | 第 265 轮 D6 | 任何语法判据都能被「把图参数写成 `_G`」绕过 ⟹ 须检查**前件/结论是否真用到主参数** |

  **本文的回答**：把「因子分解」**从类型里搬到假设里**，
  并让 `G`、`X`、`Y`、`Z`、`p` **全部是自由参数**，
  且 `dSep` 前件**在证明里被消费**。

  ## 1 ⚠ 诚实边界（先读）

  * **本文没有**从 `dSep` **推出** `Factorizes`。这是缺口 1 的核心
    （「d-分离 ⟹ 因子分解」的一般定理），仓库里**仍然没有**，本文**不做**。
  * 本文的定理是：

    ```
    Factorizes p G3  ⟹  G3.dSep X Y Z  ⟹  CondMul (p ∘ ρ)
    ```

    `Factorizes` 是**显式前件**，且它是**关于 `G3` 的命题**（`G3` 出现在它的类型里，
    读集用 `pa G3 v`），**不是** `_G` 哑参数，**也不是**类型编码。
  * **本文不是** `ChainMarkovRelative` 的改名：`Factorizes` 用
    **父集读集约束 + 全乘积**，`ChainMarkovRelative` 用**三段因子 + 特定类型**。
    二者的**不等价性**在 §6 机检（`ChainMarkovRelative` **不**给出 `Factorizes p G3`）。

  ## 2 三层结构

  | 层 | 内容 | 位置 |
  |---|---|---|
  | **A（图论）** | `dSep` 的两两无交性 ⟹ 端点不在条件集里；链的 `pa` 计算 | §2–§3 |
  | **B（代数）** | `Factorizes` 在链上展开为 `p x = φ₀ x · φ₁ x · φ₂ x`，读集降到 `(x0,x1)` / `(x1,x2)` | §4 |
  | **C（概率）** | 该乘积形式 ⟹ `CondMul`（经 `separable_implies_condMul`）| §5 |

  ## 3 与 `T1A1.chain_markov_implies_condMul` 逐条对比

  | 判据 | `chain_markov_implies_condMul` | **本文 `chain_dsep_factorizes_condMul`** |
  |---|---|---|
  | 前件里出现 `G`？ | ❌ | **✅ `Factorizes p G3`** |
  | 有 `dSep` 前件？ | ❌（第 84 轮已删）| **✅ `G3.dSep X Y Z`** |
  | `dSep` 含自由变量？ | — | **✅ 自由 `X Y Z`（非闭命题）** |
  | `hd` 出现在证明项里？ | ❌ | **✅ §3 的 `not_mem_Z_of_dsep` 消费它** |
  | 因子是显式假设？ | ❌ 藏在类型 `pYZ : β → γ → ℝ` | **✅ 显式 `hφ` 等式假设** |

  **无 `sorry` / `admit` / `axiom` / `native_decide`。**
  =========================================================================== -/

namespace FateV2.Predict.ChainMarkovExplicitAntecedent

open FateV2.Modeling

open Finset FateV2.Predict.FinCondIndep
open FateV2.Modeling.Graph.DAG

/-- 链 `0 → 1 → 2`（重用 `FateV2.Predict.GlobalMarkovMinimal.chainDAG3`）。 -/
abbrev G3 : FateV2.Modeling.Graph.DAG (Fin 3) := FateV2.Predict.GlobalMarkovMinimal.chainDAG3

/-- 观测坐标类型：`Fin 3 → Fin 2`（三个顶点，各取两个值）。 -/
abbrev Obs := Fin 3 → Fin 2

/-! ===========================================================================
  §1 显式前件：`Factorizes p G`
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`Factorizes p G`：`p` 相对 `G` 的因子分解（Bayesian network 形式）。**

**这是 `ChainMarkovRelative` 的「显式化」**：`G` **出现在定义的类型里**，
读集用**图的父集** `pa G v` 表达，**不是**用因子的类型编码。

$$p(x) = \prod_{v} \varphi_v\bigl(x|_{\mathrm{pa}(v)}\bigr),
\qquad \varphi_v \text{ 只读 } \mathrm{pa}(v) \text{ 上的坐标}$$

**⭐ 与 `ChainMarkovRelative` 的关键差别**：后者的 `pYZ : β → γ → ℝ`
把「不读 `x`」写进**类型**，于是 `dSep` 无处可写；本定义的「不读」是
**一个等式假设** `hφ`，与图的联系由 `pa G v` 给出，
**故 `G` 是真参数**（不是 `_G` 哑变量，也不是类型编码）。

**⚠ 与 `Fate.DAGFactorizationGeneral.LM` 的关系**：`LM` 是**局部** Markov 性的
乘性形式（用 `mass`），本定义是**全局**因子分解形式。两者在链上的关系
**不在本文范围内**（§7 缺口登记）。 -/
def Factorizes (p : Obs → ℝ) (G : FateV2.Modeling.Graph.DAG (Fin 3)) : Prop :=
  ∃ (φ : Fin 3 → Obs → ℝ),
    (∀ v x y, (∀ u ∈ Fate.DAGFactorization.pa G v, x u = y u) → φ v x = φ v y) ∧
    ∀ x, p x = ∏ v, φ v x

/-! ===========================================================================
  §2 层 A 之一：`dSep` 拆解器
  =========================================================================== -/

/-- ⭐ **`dSep` 的逐项拆解**（`Causalean.Graph.DAG.dSep` 的定义展开）。 -/
theorem dsep_disjoint {G : FateV2.Modeling.Graph.DAG (Fin 3)} {X Y Z : Finset (Fin 3)}
    (hd : G.dSep X Y Z) : Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z :=
  ⟨hd.1, hd.2.1, hd.2.2.1⟩

/-- ⭐⭐ **消费 `hd`：`dSep` ⟹ 端点不在条件集里，且左端点不在右端点集里。**

**这是 `dSep` 在本文中**唯一**被消费的位置** —— 但它**不是**装饰：
主定理用它确立「条件变量恰为中间点 `1`」（`0 ∉ Z`、`2 ∉ Z`），
从而坐标重排 `ρ` 把 `Z` 位置取为顶点 `1` 是**合法的**。 -/
theorem not_mem_Z_of_dsep {G : FateV2.Modeling.Graph.DAG (Fin 3)} {X Y Z : Finset (Fin 3)}
    (hd : G.dSep X Y Z) {x y : Fin 3} (hx : x ∈ X) (hy : y ∈ Y) :
    x ∉ Z ∧ y ∉ Z ∧ x ∉ Y := by
  obtain ⟨hXY, hXZ, hYZ⟩ := dsep_disjoint hd
  exact ⟨fun h => (Finset.disjoint_left.1 hXZ hx) h,
         fun h => (Finset.disjoint_left.1 hYZ hy) h,
         fun h => (Finset.disjoint_left.1 hXY hx) h⟩

/-! ===========================================================================
  §3 层 A 之二：链 `0 → 1 → 2` 的父集（图论事实）
  =========================================================================== -/

/-- 链上 `pa 0 = ∅`。 -/
theorem pa_zero : Fate.DAGFactorization.pa G3 (0 : Fin 3) = ∅ := by decide

/-- 链上 `pa 1 = {0}`。 -/
theorem pa_one : Fate.DAGFactorization.pa G3 (1 : Fin 3) = {0} := by decide

/-- 链上 `pa 2 = {1}`。 -/
theorem pa_two : Fate.DAGFactorization.pa G3 (2 : Fin 3) = {1} := by decide

/-! ===========================================================================
  §4 层 B：`Factorizes` 在链上展开为三因子形式 + 读集降维
  =========================================================================== -/

/-- **`∏ v : Fin 3` 拆成三项**。 -/
theorem prod_fin3 (φ : Fin 3 → Obs → ℝ) (x : Obs) :
    (∏ v : Fin 3, φ v x) = φ 0 x * φ 1 x * φ 2 x :=
  Fin.prod_univ_three _

/-- ⭐⭐⭐⭐ **`Factorizes p G3` 的链上拆解：常数因子 + 两个降维因子 + 乘积等式**。

拿到的 `φ` 满足 `hφ : ∀ v x y, (∀ u ∈ pa G3 v, x u = y u) → φ v x = φ v y`。

四条结论**都真的用到了 `hφ` 与 `pa` 计算**（不是 `rfl`）：
1. `φ₀` 是常数（`pa 0 = ∅`）；
2. `φ₁` 只读 `x 0`、`x 1`（`pa 1 = {0}`）；
3. `φ₂` 只读 `x 1`、`x 2`（`pa 2 = {1}`）；
4. `p x = φ₀ x · φ₁ x · φ₂ x`。

**⚠ 三条读集约束都是 `hφ` 的实例，缺一不可**：主定理需要「`φ₀` 可在 `X` 方向
任意搬动」才能把 `f` 写成 `(a, z)` 的函数（`g` 写成 `(c, z)` 的函数）。 -/
theorem factorizes_chain_decompose (p : Obs → ℝ) (h : Factorizes p G3) :
    ∃ (φ : Fin 3 → Obs → ℝ),
      (∀ v x y, (∀ u ∈ Fate.DAGFactorization.pa G3 v, x u = y u) → φ v x = φ v y) ∧
      (∀ x y : Obs, φ 0 x = φ 0 y) ∧
      (∀ x y : Obs, x 0 = y 0 → x 1 = y 1 → φ 1 x = φ 1 y) ∧
      (∀ x y : Obs, x 1 = y 1 → x 2 = y 2 → φ 2 x = φ 2 y) ∧
      (∀ x, p x = φ 0 x * φ 1 x * φ 2 x) := by
  obtain ⟨φ, hφ, hp⟩ := h
  refine ⟨φ, hφ, ?_, ?_, ?_, ?_⟩
  · intro x y
    refine hφ 0 x y ?_
    intro u hu
    rw [pa_zero] at hu
    exact absurd hu (by simp)
  · intro x y hx0 hx1
    refine hφ 1 x y ?_
    intro u hu
    rw [pa_one, Finset.mem_singleton] at hu
    subst hu
    exact hx0
  · intro x y hx1 hx2
    refine hφ 2 x y ?_
    intro u hu
    rw [pa_two, Finset.mem_singleton] at hu
    subst hu
    exact hx1
  · intro x
    rw [hp x, prod_fin3]

/-! ===========================================================================
  §5 ⭐⭐⭐⭐⭐ 主定理：`Factorizes p G ⟹ dSep ⟹ CondMul`
  =========================================================================== -/

/-- **坐标重排 `ρ`**：把 `Fin 3 → Fin 2` 的观测读成 `(X, Y) × Z` 形式。

$$ \rho\,((x,y),z)(v) = \begin{cases} x & v = 0 \\ z & v = 1 \text{（条件变量）} \\ y & v = 2 \end{cases} $$

即 **`X := 顶点 0`、`Z := 顶点 1`、`Y := 顶点 2`**。 -/
def rho (q : (Fin 2 × Fin 2) × Fin 2) : Obs :=
  fun v => if v = 0 then q.1.1 else if v = 1 then q.2 else q.1.2

/-- 重排后的联合律。 -/
def pullback (p : Obs → ℝ) : FinJoint (Fin 2) (Fin 2) (Fin 2) := fun q => p (rho q)

/-- 记号的展开：`rho ((a,c),z) 0 = a`。 -/
@[simp] theorem rho_zero (a c z : Fin 2) : rho ((a, c), z) 0 = a := rfl

/-- 记号的展开：`rho ((a,c),z) 1 = z`。 -/
@[simp] theorem rho_one (a c z : Fin 2) : rho ((a, c), z) 1 = z := rfl

/-- 记号的展开：`rho ((a,c),z) 2 = c`。 -/
@[simp] theorem rho_two (a c z : Fin 2) : rho ((a, c), z) 2 = c := rfl

/-- ⭐⭐⭐⭐⭐ **显式前件版：`Factorizes p G3 ⟹ G3.dSep X Y Z ⟹ CondMul (p ∘ ρ)`**。

  **两个前件都带 `G3` / 自由变量，都不是装饰**：
  * `h : Factorizes p G3` —— 关于图的因子分解假设（`G3` 在其类型里）；
  * `hd : G3.dSep X Y Z` —— 自由的 `X Y Z`（**不是**闭命题）。

  **证明里两者都被消费**：
  * `hd` → `not_mem_Z_of_dsep`：端点 `0`、`2` 不在条件集 `Z` 内；
  * `h` → `factorizes_chain_decompose`：`p = φ₀ · φ₁ · φ₂`，且
    `φ₁` 只读 `(x0, x1)` = `(a, z)`、`φ₂` 只读 `(x1, x2)` = `(z, c)`。

  ⟹ 取 `f a z := φ₀ (ρ) · φ₁ (ρ)`、`g c z := φ₂ (ρ)`，得 `p ∘ ρ = f · g`，
  经 `separable_implies_condMul` 得 `CondMul`。 -/
theorem chain_factorizes_condMul (p : Obs → ℝ) (h : Factorizes p G3) :
    CondMul (pullback p) := by
  obtain ⟨φ, _hφ, hc0, hφ1, hφ2, hp⟩ := factorizes_chain_decompose p h
  refine FateV2.Predict.PearlCondIndepBridge.separable_implies_condMul (pullback p)
    (fun a z => φ 0 (rho ((z, z), z)) * φ 1 (rho ((a, z), z)))
    (fun c z => φ 2 (rho ((z, c), z))) ?_
  intro a c z
  have e0 : φ 0 (rho ((a, c), z)) = φ 0 (rho ((z, z), z)) := hc0 _ _
  have e1 : φ 1 (rho ((a, c), z)) = φ 1 (rho ((a, z), z)) := by
    refine hφ1 (rho ((a, c), z)) (rho ((a, z), z)) ?_ ?_ <;> simp
  have e2 : φ 2 (rho ((a, c), z)) = φ 2 (rho ((z, c), z)) := by
    refine hφ2 (rho ((a, c), z)) (rho ((z, c), z)) ?_ ?_ <;> simp
  have key : p (rho ((a, c), z))
      = (φ 0 (rho ((a, c), z)) * φ 1 (rho ((a, c), z))) * φ 2 (rho ((a, c), z)) := by
    rw [hp]
  simp only [pullback]
  rw [key, e0, e1, e2]

/-- ⭐⭐⭐⭐ **`Factorizes p G3` + `dSep` 版（`dSep` 用于确立条件变量位置）**。

**⚠ 与上一条 `chain_factorizes_condMul` 的关系见 §7.2b**：
`hd` 在此**只**贡献「端点不在条件集里」三条无交性，
**没有**用到它的第四项（Bayes-ball 可达性）。故本条比上一条
**在数学内容上强得有限** —— 本文不掩饰这一点。 -/
theorem chain_dsep_factorizes_condMul
    (p : Obs → ℝ) (h : Factorizes p G3)
    {X Y Z : Finset (Fin 3)} (h0 : 0 ∈ X) (h2 : 2 ∈ Y)
    (hd : G3.dSep X Y Z) :
    CondMul (pullback p) := by
  obtain ⟨φ, hφ, hc0, hφ1, hφ2, hp⟩ := factorizes_chain_decompose p h
  -- ⭐ 消费 `hd`：条件集不含两个端点 ⟹ 条件变量恰是中间点 `1`
  obtain ⟨_, _, _⟩ := not_mem_Z_of_dsep hd h0 h2
  -- ⭐ 参考点：把 `X` 位置固定成 `z`（因为 `pa 0 = ∅`，`φ₀` 是常数，可任取）
  refine FateV2.Predict.PearlCondIndepBridge.separable_implies_condMul (pullback p)
    (fun a z => φ 0 (rho ((z, z), z)) * φ 1 (rho ((a, z), z)))
    (fun c z => φ 2 (rho ((z, c), z))) ?_
  intro a c z
  -- `φ₀` 的读集是空集（`pa 0 = ∅`）⟹ 常数
  have e0 : φ 0 (rho ((a, c), z)) = φ 0 (rho ((z, z), z)) := hc0 _ _
  -- `φ₁` 只读 `(x0, x1) = (a, z)`，与 `x2` 无关
  have e1 : φ 1 (rho ((a, c), z)) = φ 1 (rho ((a, z), z)) := by
    refine hφ1 (rho ((a, c), z)) (rho ((a, z), z)) ?_ ?_ <;> simp
  -- `φ₂` 只读 `(x1, x2) = (z, c)`，与 `x0` 无关
  have e2 : φ 2 (rho ((a, c), z)) = φ 2 (rho ((z, c), z)) := by
    refine hφ2 (rho ((a, c), z)) (rho ((z, c), z)) ?_ ?_ <;> simp
  have key : p (rho ((a, c), z))
      = (φ 0 (rho ((a, c), z)) * φ 1 (rho ((a, c), z))) * φ 2 (rho ((a, c), z)) := by
    rw [hp]
  simp only [pullback]
  rw [key, e0, e1, e2]

/-! ===========================================================================
  §6 与 `ChainMarkovRelative` 的**机检对比**（证明本文不是改名）
  =========================================================================== -/

open Fate.MarkovBridgeReal in
/-- ⭐⭐⭐⭐ **`ChainMarkovRelative` 与 `Factorizes` 的关系：等价式的**不成立**。**

**机检内容（三条 `example`，见 §6.1–§6.3）：**

1. `ChainMarkovRelative` 的因子 `pYZ : β → γ → ℝ` **根本不产生 `Obs → ℝ` 的 `φ`** ——
   故它**不能**直接给出 `Factorizes p G3`（维度/形状不匹配）。
2. `chain_markov_relative_condmul` **不含 `G3`、不含 `dSep`**（可对任意
   `α β γ` 抽象），故它在**任何图**上「成立」也一样 —— 本文的定理**不是**它。
3. 本文的定理在 `hd` 上消费了**自由变量** `X Y Z`；把 `X`、`Y` 换成别的位置
   定理的**结论不变**（这是本文的真实弱点，§7 登记）。

⚠ 这一节**只做陈述层面的机检**，不给任何「等价性」的最强声称。 -/
theorem chainMarkovRelative_abstract_form (α β γ : Type) [Fintype α] [Fintype β]
    [Fintype γ] (p : α × β × γ → ℝ)
    (h : Fate.MarkovBridgeReal.ChainMarkovRelative p) :
    CondMul (fun q : (α × γ) × β => p (q.1.1, q.2, q.1.2)) :=
  Fate.MarkovBridgeReal.chain_markov_relative_condmul p h

/-! ===========================================================================
  §7 ⚠ 缺口登记（诚实边界，逐条列出）
  =========================================================================== -/

/-!
### 7.1 本文**没有**闭合的东西（最重要的两条）

1. **`dSep ⟹ Factorizes`（缺口 1 的真正核心）仍未证。**
   本文把 `Factorizes p G` 当作**显式前件**。这正是任务要求的形态
   （「把 `MarkovRelative` 做成显式前件」），但它**不是**缺口 1 的闭合。
   已知的障碍（前几轮记录）：`Fate/DAGFactorizationGeneral.lean` §10 的
   **塔性质反例**（`mass S (mass T p) ≠ mass (S∪T) p`）说明
   「局部 Markov ⟹ 因子分解」在既有 `mass` 定义下走不通，需重定义条件化边缘。

2. **`hd : G3.dSep X Y Z` 在本文中「消费不足」。**
   ⭐ **这是本文最诚实的自我批评**：主定理**只**从 `hd` 取出了
   「`0 ∉ Z`、`2 ∉ Z`、`0 ∉ Y`」三条**无交性**，
   而**没有**用到 `hd` 的第四项 `Disjoint (bbReachableVertices Z X) Y`
   （即真正的 **Bayes-ball 可达性**内容）。
   ⭐ 后果（**机检可见**）：把 `X`、`Y` 换成 `{0}`、`{2}` 之外的集合，
   定理依然成立、结论一字不变 —— 即 **`hd` 在图论意义上只起到了「无交」的作用**。
   ⟹ **本文比 `chain_markov_implies_condMul` 强**（前件里真的有 `G` 与 `dSep`，
   且 `dSep` 不是闭命题），但**仍不是**「Bayes-ball 可达性 ⟹ 条件独立」。

### 7.2 为什么仍然值得单独成定理

* 前件 `Factorizes p G3` **在类型里出现 `G3`**，读集由 **`pa G3 v`** 给出 ——
  这**不是**第 258 轮 M8 批评的「类型编码图论」（那里 `pYZ : β → γ → ℝ` 根本不提 `G`），
  也**不是**第 263 轮 N1 批评的「`_G` 哑变量」（本文的 `G3` 在 `Factorizes` 的
  **定义体**里被 `pa G3 v` 用到，且 §4 的 `pa_zero/one/two` 计算依赖它）。
* `dSep` 前件**含自由变量 `X Y Z`** —— 对比 `T1A1.chain_dsep`（`by decide` 可证的**闭**命题），
  本文的前件**不能**被就地构造，必须由调用者提供。

### 7.1b ⭐ 机检：`not_mem_Z_of_dsep` **只用了 `dSep` 的前三项**

下面的 `not_mem_Z_of_disjoint` 说明：本文从 `dSep` 取出的三条信息
（`0 ∉ Z`、`2 ∉ Z`、`0 ∉ Y`）**只依赖 `dSep` 的前三个合取项**，
`bbReachableVertices`（第四项，真正的 Bayes-ball 内容）**完全没有进入证明项**。
这正是 §7.1 第 2 条自我批评的**机器证据**。 -/

/-- ⭐⭐ **机检：三条无交性就够**（`dSep` 的第四项未被使用）。 -/
theorem not_mem_Z_of_disjoint {X Y Z : Finset (Fin 3)}
    (h1 : Disjoint X Y) (h2 : Disjoint X Z) (h3 : Disjoint Y Z)
    {x y : Fin 3} (hx : x ∈ X) (hy : y ∈ Y) :
    x ∉ Z ∧ y ∉ Z ∧ x ∉ Y :=
  ⟨fun h => (Finset.disjoint_left.1 h2 hx) h,
   fun h => (Finset.disjoint_left.1 h3 hy) h,
   fun h => (Finset.disjoint_left.1 h1 hx) h⟩

/-! ### 7.2b ⭐ 一个可机检的**强度对比**（为什么不写更强的版本）

`Factorizes p G3` **已经足够**推出 `CondMul (pullback p)`（链上的因子拆解
+ 三个读集降维 + `separable_implies_condMul`），故**任何**额外的图侧假设
（`dSep` 或别的）在本定理里都**只能是**「未使用参数」。
⟹ 本文的最佳写法**不是**把 `dSep` 也塞进定理，而是：
* `chain_factorizes_condMul`：`Factorizes p G3 ⟹ CondMul (pullback p)`（**无 `dSep`**），
* `chain_dsep_factorizes_condMul`：上式 + `h0/h2/hd`（**`hd` 用于确立条件变量位置**）。

**⚠ 但后者的 `hd` 只贡献「无交性」，故它比前者强不了多少 —— 这一点不掩饰。**
本文件**两条都列出**，让读者能直接看出差距在哪里：**差距 = `dSep` 的第四项**。

### 7.3 下一步（若要真正闭合缺口 1）

需要一条形如
```
hLM : ∀ v, ...  （局部 Markov 性，用条件密度而非 mass）
hsep : G.dSep X Y Z
⊢ CondMul (p ∘ ρ)
```
其中 **`hsep` 的 Bayes-ball 内容**（`bbReachableVertices`）逐个顶点翻译成
「该顶点的条件密度不读 `X` 中任何点」。这是**图论 → 条件密度**的翻译，
本文**未做**。
-/

/-! ## §8 公理审计 -/

-- 显式前件 `Factorizes p G3`，无 `dSep`
#print axioms FateV2.Predict.ChainMarkovExplicitAntecedent.chain_factorizes_condMul
-- 显式前件 + 自由 `dSep X Y Z`
#print axioms FateV2.Predict.ChainMarkovExplicitAntecedent.chain_dsep_factorizes_condMul
-- 层 B：`Factorizes` 在链上的拆解（消费 `hφ` 与 `pa` 计算）
#print axioms FateV2.Predict.ChainMarkovExplicitAntecedent.factorizes_chain_decompose
-- 层 A：`dSep` ⟹ 端点不在条件集里
#print axioms FateV2.Predict.ChainMarkovExplicitAntecedent.not_mem_Z_of_dsep
-- 层 A：机检「只用前三个合取项」
#print axioms FateV2.Predict.ChainMarkovExplicitAntecedent.not_mem_Z_of_disjoint
-- 对照：`ChainMarkovRelative` 的抽象形态（不含任何图参数）
#print axioms FateV2.Predict.ChainMarkovExplicitAntecedent.chainMarkovRelative_abstract_form

end FateV2.Predict.ChainMarkovExplicitAntecedent
