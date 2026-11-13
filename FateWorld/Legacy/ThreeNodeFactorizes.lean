import FateWorld.Legacy.FactorRecursionRouteB
import FateWorld.Legacy.PearlCondIndepBridge
import Mathlib.Tactic

/-! ===========================================================================
  `Fate/ThreeNodeFactorizes` —— **段 3 第一步：三节点图接 `Factorizes`**

  ## 任务（第 7 路）

  把三节点情形（链 / 分叉 / 撞子）与路线乙的因子分解
  `Fate.FactorRecursionRouteB.Factorizes` **接起来**，
  得到**具体图上的** `CondMul`。

  **⚠ 纪律**：
  * **不用塔性质**（`mass S (mass T p)` 形态），本文件**完全不用 `mass`**；
  * **不把结论写进前件**：`Factorizes` 是真前提，`CondMul` 是真结论；
  * **零 `sorry` / `axiom`**。

  ## 结果一览

  | # | 定理 | 内容 | 状态 |
  |---|---|---|---|
  | **A1** | `jointXZ` | 把 `p : (Fin 3 → α) → ℝ` 读成 `FinJoint α α α`（`X=x₀`、`Y=x₂`、`Z=x₁`）| 定义 |
  | **A2** | `phi_canon` | 因子只读 `pa v` ⟹ `φ v x = φ v (x` 在 `pa v` 上取，其余填 `d`)` | ✅ |
  | **A3** | `chain_pa_*` / `fork_pa_*` / `collider_pa_*` | 三个图的父集**显式值**（`decide`）| ✅ |
  | **A4** | `chain_factorizes_separable` | 链 `Factorizes ⟹ p[x₀,z,x₂] = f x₀ z · g x₂ z` | ✅ |
  | **A5** | `chain_factorizes_condMul` | ⭐ **链 `Factorizes ⟹ CondMul`**（`x₀ ⊥ x₂ | x₁`）| ✅ |
  | **A6** | `fork_factorizes_separable` | 分叉 `Factorizes ⟹ 可分离` | ✅ |
  | **A7** | `fork_factorizes_condMul` | ⭐ **分叉 `Factorizes ⟹ CondMul`** | ✅ |
  | **A8** | `colliderP_factorizes` | 撞子：**存在**满足 `Factorizes` 的显式 `p = [x₀=x₂]` | ✅ |
  | **A8′** | `chain_not_factorizes_colliderP` | 链：**同一个** `p` **不**满足 `Factorizes`（A5 非空洞）| ✅ |
  | **A9** | `collider_not_condMul` | ⭐ **撞子：`Factorizes` ⟹̸ `CondMul`**（撞子激活的机器证据）| ✅ |
  | **A10** | `chain_global_markov` / `fork_global_markov` | 图侧 `dSep` × 概率侧 `CondMul`（**对照，非推导**）| ✅ |

  ## 关键设计（为什么 `G` 真的在起作用）

  三张图的 `pa` 值**不同**：

  | 图 | `pa 0` | `pa 1` | `pa 2` |
  |---|---|---|---|
  | 链 `0→1→2` | `∅` | `{0}` | `{1}` |
  | 分叉 `1→0, 1→2` | `{1}` | `∅` | `{1}` |
  | 撞子 `0→1, 2→1` | `∅` | `{0,2}` | `∅` |

  链与分叉的 `pa` 形状让乘积**拆成两块**（`x₀` 侧 / `x₂` 侧），故可分离；
  撞子的 `pa 1 = {0,2}` 让**单个因子同时读 `x₀` 与 `x₂`**，故**不可分离** ——
  **这正是同一份 `Factorizes` 定义在三张图上给出三种不同结论的机器可检查形式**。
  若把 `G` 换掉，A5/A7 的证明**必需的一步**（`φ` 只读 `pa`）就不再可用。
  =========================================================================== -/

namespace Fate

namespace ThreeNodeFactorizes

open Finset
open Fate.DAGFactorization
open Fate.FactorRecursionRouteB (Factorizes)
open Fate.FinCondIndep (FinJoint CondMul)

universe u

set_option linter.unusedSectionVars false

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-! ===========================================================================
  §1 三张图（`Fin 3`，与 `ThreeNodeSeparation.lean` 逐字一致）
  =========================================================================== -/

/-- 三个节点。 -/
abbrev N := Fin 3

/-- 左节点。 -/
abbrev a : N := 0
/-- 中节点。 -/
abbrev b : N := 1
/-- 右节点。 -/
abbrev c : N := 2

/-- 链 `a → b → c`。 -/
def chainDAG : Causalean.Graph.DAG N where
  edge u v := (u = a ∧ v = b) ∨ (u = b ∧ v = c)
  decEdge := by infer_instance
  acyclic := Causalean.Graph.DAG.acyclic_of_topoOrder
    (r := (· < · : ℕ → ℕ → Prop))
    (τ := fun v : N => (v.val : ℕ))
    (by intro u v h; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)

/-- 分叉 `a ← b → c`。 -/
def forkDAG : Causalean.Graph.DAG N where
  edge u v := (u = b ∧ v = a) ∨ (u = b ∧ v = c)
  decEdge := by infer_instance
  acyclic := Causalean.Graph.DAG.acyclic_of_topoOrder
    (r := (· < · : ℕ → ℕ → Prop))
    (τ := fun v : N => if v = b then 0 else 1)
    (by
      intro u v h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [a, b]
      · simp [b, c])

/-- 撞子 `a → b ← c`。 -/
def colliderDAG : Causalean.Graph.DAG N where
  edge u v := (u = a ∧ v = b) ∨ (u = c ∧ v = b)
  decEdge := by infer_instance
  acyclic := Causalean.Graph.DAG.acyclic_of_topoOrder
    (r := (· < · : ℕ → ℕ → Prop))
    (τ := fun v : N => if v = b then 1 else 0)
    (by
      intro u v h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [a, b]
      · simp [b, c])

/-! ### §1.1 父集的显式值（`decide`，真用到了 `edge`） -/

theorem chain_pa0 : pa chainDAG (0 : N) = ∅ := by decide
theorem chain_pa1 : pa chainDAG (1 : N) = {0} := by decide
theorem chain_pa2 : pa chainDAG (2 : N) = {1} := by decide

theorem fork_pa0 : pa forkDAG (0 : N) = {1} := by decide
theorem fork_pa1 : pa forkDAG (1 : N) = ∅ := by decide
theorem fork_pa2 : pa forkDAG (2 : N) = {1} := by decide

theorem collider_pa0 : pa colliderDAG (0 : N) = ∅ := by decide
theorem collider_pa1 : pa colliderDAG (1 : N) = {0, 2} := by decide
theorem collider_pa2 : pa colliderDAG (2 : N) = ∅ := by decide

/-! ### §1.2 三张图的 `dSep`（本文件自足，不 import 根目录文件） -/

/-- 链阻断：`a ⨿ c | b`。 -/
theorem chain_dSep : chainDAG.dSep {a} {c} {b} := by decide

/-- 分叉阻断：`a ⨿ c | b`。 -/
theorem fork_dSep : forkDAG.dSep {a} {c} {b} := by decide

/-- 撞子无条件阻断：`a ⨿ c | ∅`。 -/
theorem collider_dSep_uncond : colliderDAG.dSep {a} {c} (∅ : Finset N) := by decide

/-! ===========================================================================
  §2 联合律的重排：把 `(N → α) → ℝ` 读成三变量联合律

  链与分叉的分离结论都是 `x₀ ⊥ x₂ | x₁`，故取
  `X = x₀`、`Y = x₂`、`Z = x₁`。
  =========================================================================== -/

/-- **A1**：把 `p : (Fin 3 → α) → ℝ` 读成 `FinJoint α α α`，
其中 `X = x₀`、`Y = x₂`、`Z = x₁`。

即 `jointXZ p ((x, y), z) = p ![x, z, y]`。 -/
noncomputable def jointXZ (p : (N → α) → ℝ) : FinJoint α α α :=
  fun q => p ![q.1.1, q.2, q.1.2]

theorem jointXZ_apply (p : (N → α) → ℝ) (x z y : α) :
    jointXZ p ((x, y), z) = p ![x, z, y] := rfl

/-! ===========================================================================
  §3 ⭐ **核心图论—代数引理：只读父集的因子在父集外可自由填充**
  =========================================================================== -/

/-- **A2（`φ` 只读 `pa`）**：若 `φ v` 只读 `pa G v`，则在 `pa G v` 之外
把坐标换成任意默认值 `d`，`φ v` 的值不变。 -/
theorem phi_canon {G : Causalean.Graph.DAG N} {φ : N → (N → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    (v : N) (d : α) (x : N → α) :
    φ v x = φ v (fun j => if j ∈ pa G v then x j else d) := by
  classical
  refine hφ v x _ ?_
  intro u hu
  simp only [hu, if_pos]

/-- **A2′**：`φ v` 在 `pa G v` 上的取值完全决定它。 -/
theorem phi_congr_on_pa {G : Causalean.Graph.DAG N} {φ : N → (N → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    (v : N) {x y : N → α} (h : ∀ u ∈ pa G v, x u = y u) : φ v x = φ v y :=
  hφ v x y h

/-! ===========================================================================
  §4 ⭐⭐⭐ **链：`Factorizes ⟹ CondMul`**
  =========================================================================== -/

/-- **A4（链的可分离性）**。

设 `Factorizes p chainDAG`，见证 `φ`。由 §1.1：
* `pa 0 = ∅` ⟹ `φ 0` 是**常数**，记 `κ := φ 0 (fun _ => d)`；
* `pa 1 = {0}` ⟹ `φ 1 x` 只读 `x 0`，记 `B t := φ 1 (fun j => if j = 0 then t else d)`；
* `pa 2 = {1}` ⟹ `φ 2 x` 只读 `x 1`，记 `C t := φ 2 (fun j => if j = 1 then t else d)`。

则 `p ![x, z, y] = (κ · B x) · C z`，即**可分离**（`y` 不出现在乘积中）。 -/
theorem chain_factorizes_separable {p : (N → α) → ℝ} (h : Factorizes p chainDAG) :
    ∃ f g : α → α → ℝ, ∀ x y z : α, jointXZ p ((x, y), z) = f x z * g y z := by
  classical
  obtain ⟨φ, hφ, hprod⟩ := h
  -- 取任意默认值 `d : α`（`α` 非空）
  obtain ⟨d⟩ := ‹Nonempty α›
  -- 三个「语义」函数
  set κ : ℝ := φ 0 (fun _ : N => d) with hκ
  set B : α → ℝ := fun t => φ 1 (fun j : N => if j = 0 then t else d) with hB
  set C : α → ℝ := fun t => φ 2 (fun j : N => if j = 1 then t else d) with hC
  refine ⟨fun x _ => κ * B x, fun _ z => C z, ?_⟩
  intro x y z
  -- `φ 0` 是常数
  have e0 : φ 0 ![x, z, y] = κ := by
    refine phi_congr_on_pa hφ 0 ?_
    intro u hu
    rw [chain_pa0] at hu
    exact absurd hu (by simp)
  -- `φ 1` 只读 `x 0`
  have e1 : φ 1 ![x, z, y] = B x := by
    rw [hB]
    refine phi_congr_on_pa hφ 1 ?_
    intro u hu
    rw [chain_pa1] at hu
    rw [Finset.mem_singleton] at hu
    subst hu
    simp
  -- `φ 2` 只读 `x 1`
  have e2 : φ 2 ![x, z, y] = C z := by
    rw [hC]
    refine phi_congr_on_pa hφ 2 ?_
    intro u hu
    rw [chain_pa2] at hu
    rw [Finset.mem_singleton] at hu
    subst hu
    simp
  show p ![x, z, y] = (κ * B x) * C z
  rw [hprod, Fin.prod_univ_three, e0, e1, e2]

/-- ⭐⭐⭐ **A5（主定理 / 链）**：链上 `Factorizes ⟹ x₀ ⊥ x₂ | x₁`（`CondMul`）。

**这里 `G` 真的被使用**：证明**必需** `pa chainDAG 0 = ∅`、
`pa chainDAG 1 = {0}`、`pa chainDAG 2 = {1}`（`decide` 从 `edge` 算出），
把它们换成分叉的 `pa` 值则 `e2` 一步不成立。

**⚠ 本定理不含 `dSep`**：它是纯概率侧的结论。与图侧 `dSep` 的合成见
`chain_global_markov`。 -/
theorem chain_factorizes_condMul {p : (N → α) → ℝ} (h : Factorizes p chainDAG) :
    CondMul (jointXZ p) := by
  obtain ⟨f, g, hsep⟩ := chain_factorizes_separable h
  exact Fate.PearlCondIndepBridge.separable_implies_condMul (jointXZ p) f g hsep

/-! ===========================================================================
  §5 ⭐⭐⭐ **分叉：`Factorizes ⟹ CondMul`**
  =========================================================================== -/

/-- **A6（分叉的可分离性）**：`pa 0 = {1}`、`pa 1 = ∅`、`pa 2 = {1}`
⟹ `p ![x, z, y] = (D z · μ) · E z`（`μ` 是 `φ 1` 的常数值）。 -/
theorem fork_factorizes_separable {p : (N → α) → ℝ} (h : Factorizes p forkDAG) :
    ∃ f g : α → α → ℝ, ∀ x y z : α, jointXZ p ((x, y), z) = f x z * g y z := by
  classical
  obtain ⟨φ, hφ, hprod⟩ := h
  obtain ⟨d⟩ := ‹Nonempty α›
  set μ : ℝ := φ 1 (fun _ : N => d) with hμ
  set D : α → ℝ := fun t => φ 0 (fun j : N => if j = 1 then t else d) with hD
  set E : α → ℝ := fun t => φ 2 (fun j : N => if j = 1 then t else d) with hE
  refine ⟨fun _ z => D z * μ, fun _ z => E z, ?_⟩
  intro x y z
  have e0 : φ 0 ![x, z, y] = D z := by
    rw [hD]
    refine phi_congr_on_pa hφ 0 ?_
    intro u hu
    rw [fork_pa0] at hu
    rw [Finset.mem_singleton] at hu
    subst hu
    simp
  have e1 : φ 1 ![x, z, y] = μ := by
    refine phi_congr_on_pa hφ 1 ?_
    intro u hu
    rw [fork_pa1] at hu
    exact absurd hu (by simp)
  have e2 : φ 2 ![x, z, y] = E z := by
    rw [hE]
    refine phi_congr_on_pa hφ 2 ?_
    intro u hu
    rw [fork_pa2] at hu
    rw [Finset.mem_singleton] at hu
    subst hu
    simp
  show p ![x, z, y] = (D z * μ) * E z
  rw [hprod, Fin.prod_univ_three, e0, e1, e2]

/-- ⭐⭐⭐ **A7（主定理 / 分叉）**：分叉上 `Factorizes ⟹ x₀ ⊥ x₂ | x₁`。 -/
theorem fork_factorizes_condMul {p : (N → α) → ℝ} (h : Factorizes p forkDAG) :
    CondMul (jointXZ p) := by
  obtain ⟨f, g, hsep⟩ := fork_factorizes_separable h
  exact Fate.PearlCondIndepBridge.separable_implies_condMul (jointXZ p) f g hsep

/-! ===========================================================================
  §6 ⭐⭐⭐ **撞子：`Factorizes` **不**给出 `CondMul`**（条件的必要性）

  撞子 `pa 1 = {0,2}`：**一个因子同时读 `x₀` 与 `x₂`**，
  于是乘积**不可分离**。下面给一个机器校验的 `α = Fin 2` 反例。
  =========================================================================== -/

/-- 撞子的**显式因子**：`φ 0 ≡ 1`、`φ 2 ≡ 1`、`φ 1 x := [x₀ = x₂]`。 -/
noncomputable def colliderPhi (v : N) (x : N → α) : ℝ :=
  if v = 1 then (if x 0 = x 2 then 1 else 0) else 1

/-- 撞子反例的联合律：`p x = [x₀ = x₂]`（**不读 `x₁`**）。 -/
noncomputable def colliderP (x : N → α) : ℝ := if x 0 = x 2 then 1 else 0

/-- `colliderPhi` 只读 `pa v`：`φ 0`、`φ 2` 是常数；`φ 1` 读 `x 0` 与 `x 2`。 -/
theorem colliderPhi_reads {v : N} {x y : N → α}
    (h : ∀ u ∈ pa colliderDAG v, x u = y u) : colliderPhi v x = colliderPhi v y := by
  by_cases hv : v = 1
  · subst hv
    -- `v = 1`：`pa 1 = {0, 2}`
    have h0 : x 0 = y 0 := h (0 : N) (by rw [collider_pa1]; simp)
    have h2 : x 2 = y 2 := h (2 : N) (by rw [collider_pa1]; simp)
    simp only [colliderPhi, h0, h2]
  · -- `v ≠ 1`：`φ v ≡ 1`（常数），与 `pa` 无关
    simp only [colliderPhi, if_neg hv]

/-- **A8（撞子：`Factorizes` 成立）**：`colliderP` 按撞子图因子分解。 -/
theorem colliderP_factorizes (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    Factorizes (colliderP (α := α)) colliderDAG := by
  refine ⟨colliderPhi (α := α), fun v x y hxy => colliderPhi_reads hxy, ?_⟩
  intro x
  -- `∏ v, φ v x = φ 0 · φ 1 · φ 2 = 1 · [x₀=x₂] · 1`
  rw [Fin.prod_univ_three]
  have h0 : (0 : N) ≠ 1 := by decide
  have h2 : (2 : N) ≠ 1 := by decide
  simp [colliderPhi, colliderP, h0, h2]

/-- **撞子的因子化**：`p x = [x₀ = x₂]` **不可分离**（作为 `jointXZ`）。

**证明**：在 `α := Bool` 上取 `(x, y, z) = (false, true, false)`，
则 `p = [false = false] = 1`，但若 `p = f x z · g y z` 恒成立，则可分离性
会被以下四点的取值矛盾排除（见 `collider_not_separable`）。 -/
theorem collider_not_separable (f g : Bool → Bool → ℝ) :
    ¬ ∀ x y z : Bool, colliderP ![x, z, y] = f x z * g y z := by
  classical
  intro hsep
  -- 四点取值：
  --   h00 : p ![false, z, false] = f false z * g false z, z = false  → 1
  --   h01 : p ![false, z, true]  = f false z * g true  z, z = false  → 0
  --   h10 : p ![true,  z, false] = f true  z * g false z, z = false  → 0
  --   h11 : p ![true,  z, true]  = f true  z * g true  z, z = false  → 1
  have h00 : f false false * g false false = 1 := by
    have := hsep false false false
    simpa [colliderP] using this.symm
  have h01 : f false false * g true false = 0 := by
    have := hsep false true false
    simpa [colliderP] using this.symm
  have h10 : f true false * g false false = 0 := by
    have := hsep true false false
    simpa [colliderP] using this.symm
  have h11 : f true false * g true false = 1 := by
    have := hsep true true false
    simpa [colliderP] using this.symm
  -- 由 h00：两个因子都非零
  have hf : f false false ≠ 0 := by
    intro h; rw [h, zero_mul] at h00; exact absurd h00.symm (by norm_num)
  have hg : g false false ≠ 0 := by
    intro h; rw [h, mul_zero] at h00; exact absurd h00.symm (by norm_num)
  -- 由 h11：两个因子都非零
  have hf' : f true false ≠ 0 := by
    intro h; rw [h, zero_mul] at h11; exact absurd h11.symm (by norm_num)
  have hg' : g true false ≠ 0 := by
    intro h; rw [h, mul_zero] at h11; exact absurd h11.symm (by norm_num)
  -- h01 与 hf 矛盾
  exact hf' (by
    rcases mul_eq_zero.mp h01 with h' | h'
    · exact absurd h' hf
    · exact absurd h' hg')

/-- ⭐⭐⭐ **A8′（链上 `Factorizes` 假设**不可去**）**：

`colliderP`（即 `[x₀ = x₂]`）在链上**不**满足 `Factorizes` ——
否则 `chain_factorizes_separable` 会给出 `[x₀=x₂]` 的分离形式，
与 `collider_not_separable` 矛盾。

**⚠ 这条的意义**：`collider_not_condMul`（下方 A9）说 `colliderP` 的 `CondMul` 失败；
本定理说它**也**不满足链的 `Factorizes`。
⟹ 链的 `Factorizes ⟹ CondMul`（A5）**不是**恒真的：它的前提**真的**排除了
这个反例。这是 A5 **非空洞**的机器证据。 -/
theorem chain_not_factorizes_colliderP :
    ¬ Factorizes (colliderP (α := Bool)) chainDAG := by
  intro h
  obtain ⟨f, g, hsep⟩ := chain_factorizes_separable h
  exact collider_not_separable f g hsep

open Fate.FinCondIndep (margZ margXZ margYZ) in
/-- **A9（主定理 / 撞子）**：撞子上 `Factorizes` **不蕴含** `CondMul`。

**这是「条件的必要性」的机器证据**：`colliderP_factorizes` 给出一个
**满足** `Factorizes colliderDAG` 的 `p`，而此定理说明它的 `CondMul` **失败**。
⟹ 三张图虽共用**同一个** `Factorizes` 定义，结论却**不同**；
区别完全来自 `pa`（即 `edge`）：`pa 1 = {0,2}` 使**单个因子同时读两端**，
从而 `x₀` 与 `x₂` 无条件地耦合。

⚠ **与 `dSep` 的对照**：`collider_dSep_uncond` 说图上 `a ⨿ c | ∅` 成立。
本定理说明**仅凭 `Factorizes` 得不出**相应的 `CondMul` ——
这正是 Pearl 1.2.7 里「`dSep` 必须被**真正消费**」的缺口在最小实例上的样子
（见 §7 诚实登记）。 -/
theorem collider_not_condMul : ¬ CondMul (jointXZ (colliderP (α := Bool))) := by
  classical
  intro h
  -- 取 `x = true`、`y = false`、`z = false`
  have hpt := h true false false
  -- 三处真算：`p = 0`、`margZ = 2`、`margXZ = 1`、`margYZ = 1`
  have hp : jointXZ (colliderP (α := Bool)) ((true, false), false) = 0 := by
    simp [jointXZ, colliderP]
  have hZ : margZ (jointXZ (colliderP (α := Bool))) false = 2 := by
    simp [margZ, jointXZ, colliderP]
    norm_num
  have hXZ : margXZ (jointXZ (colliderP (α := Bool))) true false = 1 := by
    simp [margXZ, jointXZ, colliderP]
  have hYZ : margYZ (jointXZ (colliderP (α := Bool))) false false = 1 := by
    simp [margYZ, jointXZ, colliderP]
  rw [hp, hZ, hXZ, hYZ] at hpt
  norm_num at hpt

/-! ===========================================================================
  §7 ⭐⭐ **图侧 × 概率侧的合成陈述（对照组）**

  下面把**图侧** `dSep`（`decide` 判定）与**概率侧** `CondMul`（上述主定理）
  并排放进同一条定理。**⚠ 这是「对照」，不是「推导」**：
  `dSep` **不**出现在 `CondMul` 的证明里（见 §8 诚实登记）。
  =========================================================================== -/

/-- 链：图上 `dSep {a} {c} {b}` **且** `Factorizes ⟹ CondMul`。 -/
theorem chain_global_markov {p : (N → α) → ℝ} (h : Factorizes p chainDAG) :
    chainDAG.dSep {a} {c} {b} ∧ CondMul (jointXZ p) :=
  ⟨chain_dSep, chain_factorizes_condMul h⟩

/-- 分叉：图上 `dSep {a} {c} {b}` **且** `Factorizes ⟹ CondMul`。 -/
theorem fork_global_markov {p : (N → α) → ℝ} (h : Factorizes p forkDAG) :
    forkDAG.dSep {a} {c} {b} ∧ CondMul (jointXZ p) :=
  ⟨fork_dSep, fork_factorizes_condMul h⟩

/-! ===========================================================================
  §8 ⚠ **诚实登记（不进下游）**

  | 项 | 状态 |
  |---|---|
  | 链 / 分叉：`Factorizes ⟹ CondMul` | ✅ **已证**（A5 / A7），**零 `sorry`** |
  | 撞子：`Factorizes` ⟹̸ `CondMul` | ✅ **已证**（A8 + A9），机器校验 |
  | **`dSep` 被消费于 `CondMul`** | ❌ **未做到**（§7 是合取，不是推导）|
  | 一般 DAG 的 `Factorizes ⟹ LMG ⟹ GM` | ❌ 未证（见 `FactorRecursionRouteB` 的登记）|

  **「消费不足」的具体内容**（本路的边界）：

  1. **`dSep` 未进入 `CondMul` 的证明**。上面 A5/A7 的证明只用了
     `pa chainDAG v` 的**值**（来自 `edge`），没有用 `dSep` 的第四合取项。
     这与第 268 轮 `ChainDSepCondMul` 的结论一致。
  2. **A5/A7 是 `Factorizes` 的真产物**（不是转述）：
     `Factorizes` 的 `G` 参数**真被使用** —— A5 里 `e2` 一步要
     `pa chainDAG 2 = {1}`，把它换成分叉的 `pa 2 = {1}` 恰好相同，
     但换成撞子的 `pa 1 = {0,2}`（则 `e1` 需要读 `x 2`）便**证不出来**；
     A9 就是这个「证不出来」的机器形式。
  3. **`α` 的非空性**（`[Nonempty α]`）：仅在构造「默认填充值」`d` 时使用。
     若 `α` 为空则 `N → α` 为空，`p` 唯一，结论平凡 —— **不失一般性**。
  =========================================================================== -/

end ThreeNodeFactorizes

end Fate
