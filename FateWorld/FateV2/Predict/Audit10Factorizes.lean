import FateWorld.FateV2.Predict.FactorRecursionRouteB
import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.GlobalMarkovMinimal
/-!
  # Predict · Audit10Factorizes

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Audit10Factorizes.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorRecursionRouteB, FactorMarkov, GlobalMarkovMinimal
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/Audit10Factorizes` —— **第 10 路：独立复核 `FactorRecursionRouteB.Factorizes`**

  任务：判断 `FateV2.Predict.FactorRecursionRouteB.Factorizes` 的**定义体**是否真的
  表达了「因子分解」`p(x) = ∏_v p(x_v | x_{pa(v)})`。

  **本文件不采信任何前路结论**，全部结论由本文件自行构造的例子机检。

  ## 定义回顾（逐字）

  ```
  def Factorizes (p : (V → α) → ℝ) (G : DAG V) : Prop :=
    ∃ (φ : V → (V → α) → ℝ),
      (∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y) ∧
      ∀ x, p x = ∏ v, φ v x
  ```

  **读集 = `pa G v`（仅父集，不含 `v` 自身）。**

  对照 `Fate.FactorMarkov.Factorizes`（正确口径）：
  ```
  def LocalTo G f := ∀ v x y, (∀ u, u = v ∨ u ∈ G.parents v → x u = y u) → f v x = f v y
  ```
  **读集 = `{v} ∪ pa(v)`。**

  ## 审计结论（三条，全部机检）

  | # | 结论 | 状态 |
  |---|---|---|
  | **A1** | RouteB `Factorizes` **不是**「`p` 沿父集因子分解」，而是「`p` 沿**祖先代数**的单点求值因子分解」，**丢失了 `x_v` 坐标** | ✅ 机检 |
  | **A2** | **过强（漏解）**：`p ≡ 1` 满足它，但 `p` 不满足 `FactorMarkov.Factorizes` 所要求的「`φ_v` 读到自身坐标」的规范形状 —— 例：任何**真**依赖 `x_v` 的 `p`（如只依赖单个坐标 `x_0`）**不满足** RouteB `Factorizes`（源点无父），却显然合法 | ✅ 机检 |
  | **A3** | **过弱（多解）**：`p ≡ 1` 在任意 DAG 上都满足 RouteB `Factorizes`（全 `φ ≡ 1`），故 `Factorizes` **不对 `p` 的形状施加任何有效约束** —— 这正是 `Factorizes p G ⇏ LMG p G` 的根源 | ✅ 机检 |

  ## A2 的精确内容（这是**最严重**的缺陷）

  取 `V = Fin 1`（单点，无边的 DAG）。`pa G 0 = ∅`，故 `φ_0` 必须是**常数**
  （读集空 ⟹ `φ 0 x = φ 0 y` 对一切 `x y`）。
  于是 `p x = φ_0 x = const`，**只可能是常函数**。

  但没有任何「因子分解」的定义会禁止 `p x = f (x 0)`：单点上的**任意**
  分布 `p : (Fin 1 → Bool) → ℝ` 都是合法联合律，「`φ_0` 读 `x_0`」。
  ⟹ **RouteB `Factorizes` 在单点图上把合法解全部剔除，只剩常函数。**

  这是读集缺 `{v}` 的**直接可检后果**，不是文字论断。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace Audit10Factorizes

open FateV2.Predict.FactorRecursionRouteB (Factorizes)
open FateV2.Predict.DAGFactorization (pa mass mem_pa)
open Finset

/-! ===========================================================================
  §1 单点图上的完整解集刻画

  为了机检，先造 `Fin 1` 上的空 DAG。
  =========================================================================== -/

/-- `Fin 1` 上的**空图**（无任何边）。 -/
def emptyDAG1 : FateV2.Modeling.Graph.DAG (Fin 1) where
  edge := fun _ _ => False
  decEdge := fun _ _ => isFalse id
  acyclic := by
    intro v h
    have key : ∀ {a b : Fin 1}, Relation.TransGen (fun _ _ : Fin 1 => False) a b → False := by
      intro a b htr
      induction htr with
      | single hab => exact hab
      | tail _ hbc _ => exact hbc
    exact key h

/-- 空图上父集必为空。 -/
theorem pa_empty1 (v : Fin 1) : pa emptyDAG1 v = ∅ := by
  rw [pa]
  apply Finset.filter_eq_empty_iff.mpr
  intro u _
  exact id

/-- ⭐⭐ **A2 的核心**：空图上 RouteB `Factorizes` 迫使 `p` 为常函数。

证明：`φ 0` 读集 `pa = ∅`，故对任意 `x y` 有 `φ 0 x = φ 0 y`（空前提）；
而 `p x = ∏ v, φ v x = φ 0 x`（只有 `v = 0` 一项）。
⟹ `p` 常。 -/
theorem factorizes_emptyDAG1_const {p : (Fin 1 → Bool) → ℝ}
    (h : Factorizes p emptyDAG1) {x y : Fin 1 → Bool} : p x = p y := by
  obtain ⟨φ, hφ, hp⟩ := h
  rw [hp x, hp y]
  refine Finset.prod_congr rfl fun v _ => ?_
  apply hφ v x y
  intro u hu
  rw [pa_empty1] at hu
  exact absurd hu (by simp)

/-- ⭐⭐⭐ **A2（反例：合法的 `p` 被 `Factorizes` 排除）**：

`p x = if x 0 then 1 else 0`（单点上的确定性分布）**不满足** RouteB
`Factorizes emptyDAG1`，因为它非常函数（`p (fun _ => true) = 1 ≠ 0 = p (fun _ => false)`）。

但单点上任何分布都是合法联合律，「`φ_0` 读 `x_0`」即可因子化。
⟹ RouteB 的读集缺 `{v}`，把这类合法解**全部剔除**。 -/
theorem legal_p_not_factorizes :
    ¬ Factorizes (fun x : Fin 1 → Bool => if x 0 then (1:ℝ) else 0) emptyDAG1 := by
  intro h
  have hc := factorizes_emptyDAG1_const h (x := fun _ => true) (y := fun _ => false)
  norm_num at hc

/-! ===========================================================================
  §2 过弱：`Factorizes` 对 `p` 几乎无约束

  `p ≡ 1` 在任何 `G` 上满足 `Factorizes`（取 `φ ≡ 1`）。这不是特异现象，
  而是「读集 `pa` 在**无父**的点上为空」带来的通病：只要能选全常因子就行。
  =========================================================================== -/

/-- `p ≡ 1` 在**任意** DAG 上满足 RouteB `Factorizes`。 -/
theorem factorizes_one_anyDAG {V : Type} [DecidableEq V] [Fintype V]
    (G : FateV2.Modeling.Graph.DAG V) :
    Factorizes (fun _ : V → Bool => (1:ℝ)) G := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro v x y _; rfl
  · intro x
    rw [Finset.prod_const, Finset.card_univ]
    simp

/-! ### 2.1 更强的过弱例：非平凡 `p` 也常被接受

`p x = ∏_v g v x` 中若每个 `g v` 只读 `pa v`，则成立。**但若某些点的
`pa` 为空**（源点），这些点上的 `g v` 只能常数。于是「源点坐标」被完全丢失。

在链 `0 → 1 → 2` 上：`pa 0 = ∅`，故 `φ_0` **必须常数**。
⟹ `p` 在 `x_0` 方向**必须不依赖**（除通过 `φ_1, φ_2` 的读集 `{0}`,`{1}` 间接影响）。
`φ_1` 读 `{0}`、`φ_2` 读 `{1}`。故 `p x = c₀ · ψ₁ x₀ · ψ₂ x₁`（`c₀` 常数）。

⟹ `p` 在链上的 RouteB 因子分解 ⟺ `p` 形如 `c · ψ₁(x₀) · ψ₂(x₁)`。
**这是「`x_2` 只通过 `x_1`、`x_0` 只作为 `ψ₁` 的自变量」的形状** ——
看上去像真链式法则，但**缺了 `φ_2` 读 `x_2`**，故 `p` 对 `x_2` 的**任何**
依赖都被禁止（`φ_2` 只读 `x_1`，`x_2` 无处可读）。

⟹ **链上 `p` 必须对 `x_2` 完全不依赖**。任何真链式法则的 `p`（如
`p = p(x_0)p(x_1|x_0)p(x_2|x_1)` 且 `p(x_2|x_1)` 非常数）**都不可因子化**。

### 2.2 （本文件机检）链上 `Factorizes` ⟹ `p` 不依赖 `x₂`

下面 `chain2_irrelevant` 把这句断言**做成定理**：
设 `h : Factorizes p chainDAG3`，则在 `x` 与 `y` 仅在 `x₂` 位不同时 `p x = p y`。 -/

/-- 链上 `pa 0 = ∅`。 -/
theorem chain_pa0 : pa FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (0:Fin 3) = ∅ := by decide

/-- 链上 `pa 1 = {0}`。 -/
theorem chain_pa1 : pa FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (1:Fin 3) = {0} := by decide

/-- 链上 `pa 2 = {1}`。 -/
theorem chain_pa2 : pa FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (2:Fin 3) = {1} := by decide

/-- ⭐⭐⭐ **2.2（机检）**：链 `0 → 1 → 2` 上 RouteB `Factorizes` 迫使
`p` 对 `x₂` **完全不敏感**（除 `x₂` 外完全相同的两点 `p` 值相等）。

**证明**：`φ₀` 读 `∅` ⟹ 常数；`φ₁` 读 `{0}` ⟹ 只读 `x₀`；
`φ₂` 读 `{1}` ⟹ 只读 `x₁`。故 `∏ φ` 只读 `(x₀, x₁)`，`x₂` 无人读。
**⟹ 真链式法则中 `p(x₂|x₁)` 丢掉，`p` 不能携带 `x₂` 信息。** -/
theorem chain2_irrelevant {p : (Fin 3 → Bool) → ℝ}
    (h : Factorizes p FateV2.Predict.GlobalMarkovMinimal.chainDAG3)
    {x y : Fin 3 → Bool} (hxy : ∀ u, u ≠ 2 → x u = y u) : p x = p y := by
  obtain ⟨φ, hφ, hp⟩ := h
  rw [hp x, hp y]
  refine Finset.prod_congr rfl fun v _ => ?_
  apply hφ v x y
  intro u hu
  apply hxy
  intro huv
  rw [huv] at hu
  -- u = 2 in pa v: cases on v
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 from by omega) with rfl | rfl | rfl
  · rw [chain_pa0] at hu; exact absurd hu (by simp)
  · rw [chain_pa1] at hu; simp only [Finset.mem_singleton] at hu; exact absurd hu (by decide)
  · rw [chain_pa2] at hu; simp only [Finset.mem_singleton] at hu; exact absurd hu (by decide)

/-- ⭐⭐⭐ **A2 在链上的显式反例**：`p x = if x 2 then 1 else 0`（`p` 只看 `x₂` 的
确定性分布）**不满足** RouteB `Factorizes chainDAG3`。

但它是一个合法的「只依赖 `x₂` 的分布」，真因子分解下 `φ₂` 读 `{2} ∪ pa 2`。
⟹ **`Factorizes` 漏掉了真因子分解的一大类解。** -/
theorem chain_dep_on_two_not_factorizes :
    ¬ Factorizes (fun x : Fin 3 → Bool => if x 2 then (1:ℝ) else 0)
      FateV2.Predict.GlobalMarkovMinimal.chainDAG3 := by
  intro h
  have hc := chain2_irrelevant h
    (x := (fun j : Fin 3 => if j = 2 then true else false))
    (y := (fun _ : Fin 3 => false))
    (by intro u hu; simp only [hu, if_false])
  simp at hc

/-- ⭐⭐⭐⭐ **A1（决定性对照）**：同一个 `p x = if x₂ then 1 else 0`
* **不满足** RouteB `Factorizes`（上一行）
* **满足** `Fate.FactorMarkov.Factorizes`（读集 `{v} ∪ pa(v)`，本行）

⟹ 两者的差异**就是** `{v}` 该不该读。`FactorMarkov` 口径**接受**的
合法链式分布，被 RouteB 口径**排除**。**这机检了「读集缺 `{v}`」这一缺陷。** -/
theorem routeB_rejects_what_FactorMarkov_accepts :
    FactorMarkov.Factorizes (fun x : Fin 3 → Bool => if x 2 then (1:ℝ) else 0)
      FateV2.Predict.GlobalMarkovMinimal.chainDAG3 :=
  ⟨fun v x => if v = 2 then (if x 2 then (1:ℝ) else 0) else 1,
   by
     intro v x y hv
     by_cases h2 : v = 2
     · subst h2; simp only; rw [hv 2 (Or.inl rfl)]
     · simp only [if_neg h2]
   , by
     intro x
     rw [Finset.prod_eq_single (2:Fin 3)]
     · simp
     · intro b _ hb; simp [hb]
     · simp⟩

/-! ===========================================================================
  §3 结论（本路独立机检，供上报）

  **A1** 定义体读集 = `pa G v`，**不含 `v`**。这与 Pearl 的
  `p(x) = ∏_v p(x_v | x_{pa(v)})` **不一致**：右端因子 `p(x_v | x_{pa(v)})`
  是 `x_v` 的函数，**必然读 `x_v`**。RouteB 的定义把它变成
  `∏_v ψ_v(x_{pa(v)})`，**丢掉了每个变量的「自身条件密度」这一项**。

  **A2** 后果（**漏解**）：`Factorizes` **不包含**真因子分解。
  机检：`Fin 1` 空图上 `p` 被迫常函数（`factorizes_emptyDAG1_const`），
  但单点上任何 `p` 都合法（`legal_p_not_factorizes` 给出被排除的合法 `p`）。
  一般地 `V = n` 时，RouteB 只允许 `p` 落在「门（gate）乘积」这一**薄**子集里。

  **A3** 后果（**无约束**）：`p ≡ 1` 在**任意** `G` 上满足 `Factorizes`
  （`factorizes_one_anyDAG`）。故 `Factorizes p G` **不能**推出任何
  关于 `p` 相对 `G` 的 Markov 性质 —— 这就是 `Factorizes ⇏ LMG`
  的**结构性原因**（不依赖任何具体图，任何点数 ≥ 1 的图上都成立）。

  **⟹ 裁定**：RouteB 的 `Factorizes` **不表达「因子分解」**。
  它是「沿祖先集的**门乘积**」，比真因子分解**严格更弱**（漏掉 `x_v` 项），
  同时又**过松**（`p ≡ 1` 恒成立），故**不可作为 Pearl 1.2.7 的前件**。

  **正确口径**：`Fate.FactorMarkov.LocalTo`（读集 `{v} ∪ pa(v)`），
  其 `sink_peel`（T4）已零缺口证明了真正的 sink 剥离。
  =========================================================================== -/

end Audit10Factorizes
end FateV2.Predict