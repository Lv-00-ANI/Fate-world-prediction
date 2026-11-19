import FateWorld.FateV2.Predict.TowerAudit
import FateWorld.FateV2.Predict.AncestralInheritanceRouteB
/-!
  # Predict · BridgeView2Elimination

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeView2Elimination.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TowerAudit, AncestralInheritanceRouteB
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeView2Elimination` —— **「图 ⟹ 概率」桥的第 2 种证明策略**

  ## 0 定位

  同一座桥（`FactorizesC ⟹ LMGc`，即「因子分解 ⟹ 乘性局部 Markov」）有两条完全
  不同的落地路线：

  | 视角 | 策略 | 核心工具 | 状态 |
  |---|---|---|---|
  | **视角 1（路线丙）** | **类型收窄**：把 `mass S p` 的输出型从 `(V→α)→ℝ` 收窄成 `S→α` | `Marginal` / `MarginalSub`（`Fate/RouteC`）| 塔性质**零乘子**，但输出型变了 |
  | **视角 2（本文件）** | **完全变量消元**：不比两种 `mass`，**直接把 `mass` 算到底** | `mass_compl_singleton_eq` + 乘积拆分 | **不用塔性质**，输出型**不变** |

  ## 1 为什么必须换一种策略（诊断，已机检）

  * **塔性质 `mass S (mass T p) = mass (S∪T) p` 为假**（`DAGFactorizationGeneral.tower_property_false`）；
    其**根因**是 `mass` 非归一化，精确定律为
    `mass S (mass T p) x = multS S x · mass T p x`（`TowerExactLaw.mass_mass_of_subset`），
    `multS S x = |α|^{|V∖S|}`。
  * **视角 1 的 `mass_mul` 卡点**（`AncestralInheritanceRouteB` §5，B3 缺口）：
    `mass_mul` 要求「可分离因子的读集 ⊆ 求和集」。
    推出 `FactorizesC ⟹ LMGc` 时要算 `mass (B∪C) (f·h)`，而 `f` 读 `A ⊋ B∪C`
    （`A` 是祖先闭集，`B = Aᶜ`），**前提不成立**，故那一步无法用乘积分离完成。

  ## 2 视角 2 的做法（本文件）

  **不比两种 `mass`，而是把 `mass` 算到底。** 关键观察：

  > `mass (V∖{v}) p x` 里，求和集是 `V∖{v}`，**只有 `v` 一个坐标被求和**。
  > 而 `mass (V∖{v}) = ∑_{x_v}`（`TowerAudit.mass_compl_singleton_eq`，是
  > `mass_insert_sum` 的直接特例，**不是**塔）。

  于是对 `p = ∏_w φ_w`：

  $$\mathrm{mass}\,(V\setminus\{v\})\,p\,x
    =\sum_{a}\prod_w \varphi_w(x_v{:=}a)
    =\Bigl(\sum_{a}\varphi_v(x_v{:=}a)\Bigr)\cdot\prod_{w\ne v}\varphi_w(x)$$

  **最后一步只用「`φ_w`（`w ≠ v`）不读 `x_v`」**（`LocalTo` 的读集假设），
  **没有任何塔、没有任何 `mass` 嵌套、没有纤维乘子**。这就是 `V2-1`。

  **⟹ 视角 2 把「图侧信息」用在唯一的地方：`φ_w` 的读集。**
  图论只负责「谁的读集包含 `v`」，代数的乘法/求和分离负责其余。

  ## 3 交付清单

  | # | 定理 | 状态 | 内容 |
  |---|---|---|---|
  | **V2-A** | `factor_off` | ✅ 零缺口 | 不读 `v` 的因子在 `unpin v x a` 下不变 |
  | **V2-1** | `peel` | ✅ 零缺口 | **消元引擎**：`mass (V∖{v}) (∏φ) = (∑φ_v)·∏_{w≠v}φ_w` |
  | **V2-2** | `peel_marginal_constant` | ✅ 零缺口 | **剥离后与 `x_v` 无关**（marginal locality，不用塔）|
  | **V2-3** | `sink_factor_off` | ✅ 零缺口 | **图侧**：`v` 为 sink ⟹ 除 `φ_v` 外无人读 `x_v` |
  | **V2-4** | `sink_elim_law` | ✅ 零缺口 | **图 ⟹ 概率的一步**：sink 处消元定律 |
  | **V2-5** | `sink_marginal_constant` | ✅ 零缺口 | **递归不变量**：消元结果与 `x_v` 无关（`T5` 的视角 2 版）|
  | **V2-6** | `not_mem_pa_of_sink` | ✅ 零缺口 | **图侧**：sink 不是任何点的父 |
  | **§4** | `demo_sink_elim` / `demo_marginal_constant` | ✅ 编译期回归 | 3 节点链上的**非平凡**实例（`φ_2` 真读父 `x_1`）|

  **公理核验**：五条核心定理经 `#print axioms` 检查，均只依赖
  `propext, Classical.choice, Quot.sound`（Lean 标准三公理），
  **零 `sorry` / 零额外 `axiom` / 零 `Prop` 占位**。

  ## 4 与视角 1 的分工（诚实边界）

  * 本文件交付的是**归纳引擎**：`mass (V∖{v}) p` 的**显式值**与它的
    **`x_v` 无关性**。这正是沿拓扑序剥离所需的**单步**。
  * **未交付**：`FactorizesC ⟹ LMGc` 的**完整**归纳（需要
    在 `V∖{v}` 的诱导子图上重建设施，并同步剥离 `dSep`）。
    这与视角 1（`Marginal` 类型收窄）的残余缺口**同构**，
    但**视角 2 的残余缺口不含任何 `mass` 塔**，也不含视角 1 的
    `mass_mul` 读集卡点（因为 `mass` 已被算成求和，不再作用于乘积）。
  =========================================================================== -/

namespace FateV2.Predict.BridgeView2

open FateV2.Modeling

set_option linter.unusedSectionVars false

open Finset FateV2.Predict.DAGFactorization FateV2.Modeling.Graph

variable {V : Type} [DecidableEq V] [Fintype V]
variable {α : Type} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §1 ⭐⭐ 基础：`unpin` 只在 `v` 位改动
  =========================================================================== -/

/-- ⭐ **`unpin v x a` 在 `V∖{v}` 上与 `x` 完全一致**。 -/
lemma unpin_agree_off (v : V) (x : V → α) (a : α) :
    ∀ u ∈ (Finset.univ \ {v} : Finset V), unpin v x a u = x u := by
  intro u hu
  rw [mem_sdiff, mem_singleton] at hu
  simp only [unpin, if_neg hu.2]

/-- ⭐⭐ **V2-A**：若 `φ w` 不读 `v` 位（即只读 `V∖{v}` 上的坐标），则
`φ w (unpin v x a) = φ w x`。

**这是视角 2 唯一用到「读集」假设的地方** —— 图侧信息由此进入代数。 -/
lemma factor_off (v : V) (φ : V → (V → α) → ℝ) (x : V → α) (a : α) (w : V)
    (hread : ∀ a b : V → α, (∀ u ∈ (Finset.univ \ {v} : Finset V), a u = b u) →
      φ w a = φ w b) :
    φ w (unpin v x a) = φ w x :=
  hread _ _ (fun u hu => by rw [unpin_agree_off v x a u hu])

/-! ===========================================================================
  §2 ⭐⭐⭐⭐⭐ **消元引擎（`peel`）** —— 视角 2 的核心

  **⚠ 关键**：这里**没有**出现任何 `mass` 嵌套。`mass (V∖{v})` 被
  `mass_compl_singleton_eq` **一次性算成**「对 `v` 求和」，
  然后只剩**乘积的求和分离**（`Finset.sum_mul` + `prod_sdiff`）。
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **V2-1（消元引擎）**：

$$\mathrm{mass}\,(V\setminus\{v\})\Bigl(\prod_u\varphi_u\Bigr)(x)
  =\Bigl(\sum_{a}\varphi_v(x_v{:=}a)\Bigr)\cdot\prod_{w\ne v}\varphi_w(x).$$

**前提只有一个读集假设**：对 `w ≠ v`，`φ w` 不读 `v` 位。

**对比视角 1 的卡点**：视角 1 要算 `mass (B∪C) (f·h)` 且 `f` 读 `A ⊋ B∪C`，
`mass_mul` 的前提不成立。**这里没有 `mass` 作用在乘积上** ——
`mass (V∖{v})` 已被算成求和，所以 `f` 读多少都不影响。**这正是绕开 B3 的机制。** -/
theorem peel (v : V) (φ : V → (V → α) → ℝ) (x : V → α)
    (hread : ∀ w, w ≠ v → ∀ a b : V → α,
      (∀ u ∈ (Finset.univ \ {v} : Finset V), a u = b u) → φ w a = φ w b) :
    mass (Finset.univ \ {v}) (fun y => ∏ u, φ u y) x
      = (∑ a : α, φ v (unpin v x a)) * ∏ u ∈ (Finset.univ \ {v} : Finset V), φ u x := by
  rw [FateV2.Predict.TowerAudit.mass_compl_singleton_eq v (fun y => ∏ u, φ u y) x, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.prod_sdiff (show ({v} : Finset V) ⊆ Finset.univ from Finset.subset_univ _)]
  rw [Finset.prod_singleton, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [mem_sdiff, mem_singleton] at hw
  exact factor_off v φ x a w (hread w hw.2)

/-- ⭐⭐⭐⭐ **V2-2（marginal locality，不用塔性质）**：

消元后的结果 **只依赖 `V∖{v}` 上的坐标**，与 `x_v` 无关。

**意义**：这正是 `DAGFactorization.T5 sink_marginal_locality` 想要的递归不变量，
但那里的证明走的是「`mass` 的塔/剥离」，这里是**一次求和 + 乘积拆分**，
**从不出现 `mass (mass …)`**。 -/
theorem peel_marginal_constant (v : V) (φ : V → (V → α) → ℝ)
    (hread : ∀ w, w ≠ v → ∀ a b : V → α,
      (∀ u ∈ (Finset.univ \ {v} : Finset V), a u = b u) → φ w a = φ w b)
    {x x' : V → α} (hxx : ∀ u ∈ (Finset.univ \ {v} : Finset V), x u = x' u) :
    mass (Finset.univ \ {v}) (fun y => ∏ u, φ u y) x
      = mass (Finset.univ \ {v}) (fun y => ∏ u, φ u y) x' := by
  have hx := peel v φ x hread
  have hx' := peel v φ x' hread
  -- 求和部分：`φ v (unpin v x a) = φ v (unpin v x' a)`
  have hsum : (∑ a : α, φ v (unpin v x a)) = ∑ a : α, φ v (unpin v x' a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have hkey : unpin v x a = unpin v x' a := by
      funext u
      by_cases h : u = v
      · subst h; simp [unpin]
      · simp only [unpin, if_neg h]
        exact hxx u (by rw [mem_sdiff, mem_singleton]; exact ⟨mem_univ u, h⟩)
    rw [hkey]
  -- 乘积部分：`∏_{w≠v} φ w x = ∏_{w≠v} φ w x'`
  have hprod : (∏ u ∈ (Finset.univ \ {v} : Finset V), φ u x)
      = ∏ u ∈ (Finset.univ \ {v} : Finset V), φ u x' := by
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [mem_sdiff, mem_singleton] at hw
    exact hread w hw.2 x x' hxx
  calc mass (Finset.univ \ {v}) (fun y => ∏ u, φ u y) x
      = (∑ a : α, φ v (unpin v x a)) * ∏ u ∈ (Finset.univ \ {v} : Finset V), φ u x := hx
    _ = (∑ a : α, φ v (unpin v x' a)) * ∏ u ∈ (Finset.univ \ {v} : Finset V), φ u x' := by
          rw [hsum, hprod]
    _ = mass (Finset.univ \ {v}) (fun y => ∏ u, φ u y) x' := hx'.symm

/-! ===========================================================================
  §3 ⭐⭐⭐ **图侧：sink 的读集隔离**

  **视角 2 只在唯一一处消费图结构**：`FactorizesC` 的读集
  `{w} ∪ pa(w)`。若 `v` 是 **sink**（无出边），则 `v` 不是任何 `w` 的父，
  于是除 `w = v` 外**没有因子读 `x_v`**。这就把 §2 的 `hread` 前提落地了。
  =========================================================================== -/

variable {G : FateV2.Modeling.Graph.DAG V}

/-- ⭐⭐ **sink ⟹ `v ∉ pa w`（`w ≠ v`）**：`v` 无出边则不是任何别的点的父。 -/
lemma not_mem_pa_of_sink {v : V} (hsink : ∀ u, ¬ G.edge v u) {w : V} (_hw : w ≠ v) :
    v ∉ pa G w := by
  rw [DAGFactorization.mem_pa]
  intro hedge
  exact hsink w hedge

/-- ⭐⭐⭐ **V2-3（读集隔离）**：`v` 为 sink 时，`FactorizesC` 的因子 `φ w`（`w ≠ v`）
不读 `x_v`。

**这是「图 ⟹ 概率」在视角 2 里的**全部图论内容：sink 无出边 ⟹ 除 `φ_v` 外
无因子以 `v` 为父 ⟹ 无因子读 `x_v`。 -/
lemma sink_factor_off {φ : V → (V → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ insert v (pa G v), x u = y u) → φ v x = φ v y)
    {v : V} (hsink : ∀ u, ¬ G.edge v u) {w : V} (hw : w ≠ v)
    {a b : V → α} (hab : ∀ u ∈ (Finset.univ \ {v} : Finset V), a u = b u) :
    φ w a = φ w b := by
  refine hφ w a b (fun u hu => ?_)
  rw [mem_insert] at hu
  refine hab u ?_
  rw [mem_sdiff, mem_singleton]
  refine ⟨mem_univ u, fun huv => ?_⟩
  rcases hu with huw | hu
  · exact hw (huv.symm.trans huw).symm
  · exact not_mem_pa_of_sink hsink hw (huv ▸ hu)

/-- ⭐⭐⭐⭐⭐ **V2-4（图 ⟹ 概率的一步：sink 消元定律）**：

设 `FactorizesC p G`、`v` 为 sink，则把 `v` 消元后，联合律**显式分解**为
「(对 `v` 求和)·(其余因子原样)」。

**这正是视角 1 的 `DAGFactorization.T5 sink_marginal_locality` 的内容，
但这里通过 `peel`（一次求和 + 乘积拆分）得到，全程没有 `mass` 塔。** -/
theorem sink_elim_law {p : (V → α) → ℝ}
    (h : FateV2.Predict.AncestralInheritanceRouteB.FactorizesC p G)
    {v : V} (hsink : ∀ u, ¬ G.edge v u) (x : V → α) :
    ∃ φ : V → (V → α) → ℝ, (∀ w x y, (∀ u ∈ insert w (pa G w), x u = y u) → φ w x = φ w y) ∧
      mass (Finset.univ \ {v}) p x
        = (∑ a : α, φ v (unpin v x a)) *
            ∏ u ∈ (Finset.univ \ {v} : Finset V), φ u x := by
  obtain ⟨φ, hφ, hfac⟩ := h
  refine ⟨φ, hφ, ?_⟩
  have hpeel := peel v φ x (fun w hw a b hab => sink_factor_off hφ hsink hw hab)
  rw [funext hfac]
  exact hpeel

/-- ⭐⭐⭐⭐ **V2-5（递归不变量）**：消元后的结果与 `x_v` 无关。

即 `mass (V∖{v}) p` 是 `V∖{v}` 上的良定义函数 —— 这正是沿拓扑序**继续剥离**
所需的不变量（`DAGFactorization.T5` 的视角 2 版本）。 -/
theorem sink_marginal_constant {p : (V → α) → ℝ}
    (h : FateV2.Predict.AncestralInheritanceRouteB.FactorizesC p G)
    {v : V} (hsink : ∀ u, ¬ G.edge v u) {x x' : V → α}
    (hxx : ∀ u ∈ (Finset.univ \ {v} : Finset V), x u = x' u) :
    mass (Finset.univ \ {v}) p x = mass (Finset.univ \ {v}) p x' := by
  obtain ⟨φ, hφ, hfac⟩ := h
  have hpeel := peel_marginal_constant v φ
    (fun w hw a b hab => sink_factor_off hφ hsink hw hab) hxx
  rw [show p = fun y => ∏ u, φ u y from funext hfac]
  exact hpeel

/-! ===========================================================================
  §4 ⭐⭐⭐ **实例：3 节点链 `0 → 1 → 2` 上的消元（非平凡、可机检）**

  这一节给出**具体的**非平凡因子族（`φ_2` 真的读父 `x_1`），
  验证 `sink_elim_law` 在真 DAG、真分布、非平凡因子上确实可应用。
  sink 取 `2`（`chainDAG` 无 `2` 的出边）。
  =========================================================================== -/

namespace Demo

open FateV2.Predict.DAGFactorization

/-- 演示因子：`φ_0 ≡ 1`、`φ_1 = x_1 ↦ (if x_1 then 1 else 3)`、`φ_2 = (x_2,x_1) ↦ [x_2=x_1]`。 -/
noncomputable def demoφ : Fin 3 → (Fin 3 → Bool) → ℝ
  | 0, _ => 1
  | 1, y => if y 1 then 1 else 3
  | 2, y => if y 2 = y 1 then 1 else 0

/-- `φ_0` 不读任何坐标（读集 `{0} ∪ pa(0) = {0}`，但恒为 1）。 -/
theorem demoφ_read0 : ∀ x y : Fin 3 → Bool,
    (∀ u ∈ insert (0 : Fin 3) (pa chainDAG 0), x u = y u) → demoφ 0 x = demoφ 0 y := by
  intro x y _; rfl

/-- `φ_1` 只读 `x_1`（读集 `{1} ∪ pa(1) = {0,1}`，实际只用 `x_1`）。 -/
theorem demoφ_read1 : ∀ x y : Fin 3 → Bool,
    (∀ u ∈ insert (1 : Fin 3) (pa chainDAG 1), x u = y u) → demoφ 1 x = demoφ 1 y := by
  intro x y h; simp only [demoφ]; rw [h 1 (by simp)]

/-- `φ_2` 只读 `(x_2, x_1)`，而 `pa(2) = {1}` —— **真的用到了父坐标**。 -/
theorem demoφ_read2 : ∀ x y : Fin 3 → Bool,
    (∀ u ∈ insert (2 : Fin 3) (pa chainDAG 2), x u = y u) → demoφ 2 x = demoφ 2 y := by
  intro x y h; simp only [demoφ]
  rw [h 2 (by simp), h 1 (by simp [pa, chainDAG, chainEdge])]

/-- 演示联合律 `p = ∏ φ`。 -/
noncomputable def demoP : (Fin 3 → Bool) → ℝ := fun y => ∏ u, demoφ u y

/-- ⭐⭐ **演示分布确实 `FactorizesC`（读集真来自 `chainDAG`）。** -/
theorem demo_factorizes : FateV2.Predict.AncestralInheritanceRouteB.FactorizesC demoP chainDAG := by
  refine ⟨demoφ, ?_, ?_⟩
  · intro v
    fin_cases v
    · exact demoφ_read0
    · exact demoφ_read1
    · exact demoφ_read2
  · intro x; rfl

/-- `2` 是 sink（无出边）。 -/
theorem two_is_sink : ∀ u, ¬ chainDAG.edge (2 : Fin 3) u := by
  intro u h; simp only [chainDAG, chainEdge] at h; omega

/-- ⭐⭐⭐⭐ **`sink_elim_law` 在真实例上的应用**（编译即回归：
若 `sink_elim_law` 消失，本定理失败）。 -/
theorem demo_sink_elim :
    ∃ φ : Fin 3 → (Fin 3 → Bool) → ℝ,
      (∀ w x y, (∀ u ∈ insert w (pa chainDAG w), x u = y u) → φ w x = φ w y) ∧
      mass (Finset.univ \ ({2} : Finset (Fin 3))) demoP (fun _ => true)
        = (∑ a : Bool, φ 2 (unpin 2 (fun _ => true) a)) *
            ∏ u ∈ (Finset.univ \ ({2} : Finset (Fin 3))), φ u (fun _ => true) :=
  sink_elim_law demo_factorizes two_is_sink _

/-- ⭐⭐⭐ **`sink_marginal_constant` 在真实例上的应用**：消元结果与 `x_2` 无关。 -/
theorem demo_marginal_constant :
    mass (Finset.univ \ ({2} : Finset (Fin 3))) demoP (fun _ => true)
      = mass (Finset.univ \ ({2} : Finset (Fin 3))) demoP
          (fun u => if u = 2 then false else true) :=
  sink_marginal_constant demo_factorizes two_is_sink (fun u hu => by
    rw [mem_sdiff, mem_singleton] at hu
    simp only [hu.2, if_neg, not_false_iff])

end Demo


end FateV2.Predict.BridgeView2
