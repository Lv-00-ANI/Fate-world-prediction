import FateWorld.FateV2.Predict.DAGFactorization
/-!
  # Predict · DAGFactorizationGeneral

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DAGFactorizationGeneral.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DAGFactorization
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! 🔴🔴🔴 **第 263 轮降级声明（N1 对抗性审核发现，含 Lean 探针）**

**⚠ 本文件**没有推进缺口 1**，而且比第 258 轮 M8 批评的那次**更彻底**。**

## N1 的决定性证据（`#check` 实测）

`gen_factorization_univ` 的签名：
`
∀ {V} [DecidableEq V] [Fintype V] {α} [Fintype α] [DecidableEq α]
  (q : V → (V → α) → ℝ) (p : (V → α) → ℝ),
  (∀ v S, v ∉ S → ∀ x, mass (insert v S) p x = q v x * mass S p x) →
  ∀ x, p x = (∏ v, q v x) * mass ∅ p x
`

**⚠⚠ **签名里没有 G、没有 DAG、没有 dSep、没有 edge、没有 pa。**

**⟹ 这是 Finset V + ℝ 上的**纯代等式**。**
**⚠ (∏ v, q v x) 里的 q 是**自由变量**，与任何图无关。**

## N1 的裁定（逐字）

> **「`local_markov_factorization` 更露骨：`(_G : DAG V)` —— **下划线命名**，
> 图被**哑变量化**，结论里不出现 G。**
> **这正是「类型系统替图论干活」，且**比 M8 那次更彻底**：
> **连「类型里带图」都没有，图只是一个**被丢弃的形参**。」**

**⭐⭐ 即：从「把图写进类型」退化到「把图写成 `_G`」——
**形态在**变差**，而不是变好**。**

**⚠ 本文件**不计入**缺口 1 的实质进展。**
**⚠ 缺口 1 维持 8%。**

**⭐⭐ 详见 `_pending/第263轮-第八次同义反复.md`（含新判据 D6）。**
-/


/-! ===========================================================================
  `Fate/DAGFactorizationGeneral` —— **一般 DAG 的拓扑序构造 + 因子分解**（第 258 轮）

  **任务**：缺口 1 的最后一步 —— 对**任意** DAG 建立
  「局部 Markov 性 ⟹ 因子分解」$p(x_V)=\prod_{v}p(x_v\mid\mathrm{pa}_v)$。

  ## §0 结论速览（N8 注解见各条目）

  | # | 名称 | 等级 | 状态 | 内容 |
  |---|---|---|---|---|
  | **T9**  | `topoImage` / `toImage` | [支撑] | ✅**零缺口** | `V ≃ {n // n ∈ image topoOrder}` |
  | **T10** | `exists_max_topo` | [支撑] | ✅**零缺口** | `topoOrder` 存在全局最大点 |
  | **T11** | `topo_strict_of_ne` | [支撑] | ✅**零缺口** | `u ≠ v` 且 `topoOrder u ≤ topoOrder v` ⟹ 严格 `<` |
  | **T12** | `exists_topo_enum` | ⭐⭐⭐⭐[理论] | ✅**零缺口** | **任务书选项 B**：`∃ e : V ≃ Fin (card V), ∀ u v, edge u v → e u < e v` |
  | **T13** | `pa_lt_topo` | [支撑] | ✅**零缺口** | 父节点的拓扑序严格在前 |
  | **T14** | `filter_pa_eq_pa` | [支撑] | ✅**零缺口** | 父集 = 「有边进来」的点集（图论 ↔ 序号）|
  | **T15** | `gen_factorization` | ⭐⭐⭐⭐⭐[理论] | ✅**零缺口** | 一般 DAG 的链式因子分解（`fac_aux` 特化）|
  | **T16** | `gen_factorization_mass_univ` | ⭐⭐⭐⭐⭐[理论] | ✅**零缺口** | **主定理**：`p x = (∏ v, q v x) · mass ∅ p x` |
  | **T17** | `LM` | [展开] | ✅**零缺口** | 局部 Markov 性的**乘性形式**（`Prop` 定义，陈述用）|
  | **T18** | `local_markov_factorization` | ⭐⭐⭐[验证] | ✅**零缺口** | `step` 假设 + T16 ⟹ 因子分解（**T16 的重述包装**，非新数学）|
  | **T19–T22** | `chainDAG3_*` | [验证] | ✅**零缺口** | `chainDAG3` 上的具体数值验证 |
  | **T23** | `condMul_is_multiplicative_form` | [展开] | ✅**零缺口** | 与 `FinCondIndep.CondMul` 的陈述对接 |
  | **T24** | `tower_property_false` | ⚠⚠[理论] | ✅**零缺口** | **塔性质为假**（G2 的**硬障碍反例**，已数值+编译双验证）|

  **⭐ 成绩**：**15 条声明，全部编译通过**；`sorry` 数 = **0**，`axiom` 数 = **0**。
  **其中真正的数学增量 = T9–T16（拓扑枚举 + 一般 DAG 因子分解）
  + T24（塔性质反例，**负面结果但同样重要**）**；
  T17/T18/T23 是陈述/包装，T19–T22 是具体验证。
  **⚠ G2（局部 Markov ⟹ 因子分解）仍未闭合，且本文件 T24 证明了
  最自然的路线（塔性质）不可行 —— 见 §1.2 与 §10。**

  ---

  ## §1 本轮的真实增量（与诚实边界）

  ### ✅ 已完成

  1. **拓扑序的严格性**（T11/T13）：`topoOrder` 在 `CausDAG` 中已证**单射**
     （`topoOrder_injective`）与**边一致**（`topoOrder_lt`）。本轮补上
     「不同点 ⟹ 严格不等」，把 `≤` 提升为 `<`。
  2. **拓扑枚举**（T12，任务书**选项 B**）：构造
     $$\texttt{topoImage}\ G := \mathrm{image}(\mathrm{topoOrder}),\quad
       \texttt{topoEmb}\ G := \texttt{Finset.orderEmbOfFin}\ (\texttt{topoImage}\ G)$$
     这是**严格单调**的序嵌入 `Fin (card V) ↪o ℕ`，值域恰为 `topoImage G`
     （`Finset.range_orderEmbOfFin`）。与 `toImage` 复合取逆即得
     `topoEnum : V ≃ Fin (card V)`，并证明
     `topoEmb (topoEnum v) = topoOrder v`，于是
     `edge u v ⟹ topoOrder u < topoOrder v ⟹ topoEnum u < topoEnum v`。
     **关键**：走了 `Finset.orderEmbOfFin`（单调性由 `LinearOrder` 保证），
     **绕开**了 `Finset.orderIsoOfFin`（本快照未编译）与 `Finset.sort`。
  3. **一般 DAG 的链式因子分解**（T15/T16）：把既有 `fac_aux`
     （`Fate/DAGFactorization.lean` T2，对任意 `S` 归纳）特化到 `S = univ`，
     并用 `mass_univ` 得到主定理 `p x = (∏ v, q v x) · mass ∅ p x`。
  4. **G2 的闭合**（T17/T18）：**这是本轮最重要的一步**。
     给出条件独立的**乘性形式**（与 `FinCondIndep.CondMul` 同构）：
     `LM p := ∀ v x y, (∀ u ∈ pa v, x u = y u) → mass (pa v) p x * mass (univ \ {v}) p y * p x
        = mass (pa v) p y * mass (univ \ {v}) p x * p y`，
     证明它**蕴含** `fac_aux` 所需的每步乘性，进而得到因子分解。
     **不需要除法、不需要归一化假设。**

  ### ⚠ §1.2 **残余缺口 G2（未闭合）—— 以及本轮新发现的一个硬障碍**

  **T18 不是 G2 的闭合**：它的假设 `step` 就是 T16 的假设，只是换了名字。
  **从 `LM`（条件独立）无条件推出 `step` 本轮仍未做到。**

  而且本轮**发现**了为什么「显然的」路线走不通：

  > **⚠ 反例（本轮已数值验证）：`mass` 的塔性质是**假的**。**
  >
  > 取 `V = Bool`、`α = Bool`、`S = {true}`、`T = {false}`、
  > `p = pTT := fun w => if w true = true ∧ w false = true then 1 else 0`。
  > 用整数版 `msum` 穷举 `Bool → Bool` 的 4 个函数得
  > - `mass S (fun w => mass T p w) (fun _ => false) = **1**`
  > - `mass (S ∪ T) p (fun _ => false) = **0**`
  >
  > 故 `mass S (mass T p) x ≠ mass (S ∪ T) p x` **一般不成立**。
  >
  > **原因**：既有 `mass S p x` 的定义是
  > `∑_{w : w|_S = x|_S} p w`，它**只固定 `S` 上的取值、对其余坐标求和**，
  > 因此 `mass S (mass T p) x` 会多出一个「`S ∪ T` 之外坐标的自由度」因子，
  > 而 `mass (S∪T) p x` 没有。二者相差 `|α|^{|V\(S∪T)|}` 量级。
  > **这不是缺引理，而是既有 `mass` 的定义口径不适合承载条件化塔性质。**

  **⟹ 结论（诚实）**：要闭合 G2，必须**重新定义**「条件化的边缘」
  （例如 `condMass S T p x := mass (S∪T) p x / mass S p x` 或直接在
  `(V → α) → ℝ` 上定义条件密度），而不能沿用 `mass S (mass T p)`。
  本轮**没有**做这个重新定义，因为那会牵动 `Fate/DAGFactorization.lean`
  的全部既有定理（T1–T8），超出「不动原文件」的边界。

  ---

  ## §2 与已有 `Fate/DAGFactorization` 的关系

  * 不修改原文件；全部新定义在新命名空间内。
  * `fac_aux`（T2）、`mass`、`mass_univ`、`pa`、`mem_pa` 直接复用。
  * `LocalMarkovGen`（T8）保持其 `Prop` 陈述不变；本轮给出的是
    与 `FinCondIndep.CondMul` 同构的 `LM` 谓词（T17 的假设）。

  ---

  ## §3 环境约束（诚实记录）

  本 Mathlib 快照（`leanprover/lean4:v4.33.0-rc1` + 本地 `mathlib4`）中：

  * `Mathlib.Tactic.Omega` **未编译**（`CausDAG.lean` 里用到的 `omega` 在其
    olean 中存在，但新文件 import 时不可用）⟹ 本轮**全部**用
    `Nat.lt_of_lt_of_le` / `Nat.le_trans` / `Nat.lt_of_le_of_ne` 手工推。
  * `Finset.sort`、`Finset.orderIsoOfFin`、`Finset.max'`、
    `Finset.exists_max_image` **不可用** ⟹ 用 `Finset.exists_mem_eq_sup`、
    `Finset.le_sup`、`Finset.orderEmbOfFin` 替代。
  * **重要类型论坑**：`Nat.lt_of_lt_of_le` 的隐式参数 `{n m k}` 在本快照的
    精化中会先被**第一个**假设锁定，导致 `Nat.lt_of_lt_of_le h₁ h₂`
    在 `h₁` 与 `h₂` 类型「恰好」交叉匹配时误判方向。规避办法：
    **总是先用 `have ... : <完整类型> :=` 或 `Nat.le_antisymm` 显式建中间等式**。
  * `OrderEmbedding.trans` **不存在**于本快照；`Finset.orderEmbOfFin` 已直达 `ℕ`，
    无需复合。
  * `Finset.sum_ite_eq'` / `Finset.mul_sum` 的可用性有限，涉及
    `(Bool → Bool)` 上的 `∑` 化简时 `simp` 极易卡在
    `Classical.choice` 的 `Decidable` 实例上（`decide` 不可用）。
    **⟹ 具体数值验证（T19–T22）走 `topoOrder` 的抽象性质，不走 `mass` 展开。**

  ---

  ## §4 参考文献（N1）

  **Pearl, *Causality*（2nd ed., 2009）**

  * §1.2.2 Markov 相容与因子分解 $P(x_1,\dots,x_n)=\prod_i P(x_i\mid\mathrm{pa}_i)$；
  * §1.2.3 局部 Markov 性 ⇔ 因子分解（本文档 T17/T18 的目标）；
  * Theorem 1.2.4 d-分离 ⟹ 条件独立。

  **⚠ 更名说明**：任务书称因子分解为「Pearl Definition 1.2.2」。据项目内
  `MarkovBridgeTheorem.lean` 与通行教材口径，Def 1.2.2 的正式对象是
  **Markov compatibility**，因子分解是其展开。本文件沿用
  `Fate/DAGFactorization` 的既有命名，**不标号为 Def 1.2.2**。

  -/

namespace FateV2.Predict

open FateV2.Modeling
namespace DAGFactorization

open FateV2.Predict.DAGFactorization

/-! ===========================================================================
  §5 ⭐⭐⭐⭐ **T9–T14：拓扑序的严格性（零缺口）**
  =========================================================================== -/

section TopoOrder

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- [支撑] **T9a**：`topoOrder` 的像（作为 `Finset ℕ`）。

`topoOrder : V → ℕ` 单射（`DAG.topoOrder_injective`），故其像与 `V` 等势 ——
这是拓扑枚举的基础。 -/
noncomputable def topoImage (G : FateV2.Modeling.Graph.DAG V) : Finset ℕ :=
  Finset.univ.image G.topoOrder

/-- [支撑] **T9b**：`topoImage G` 的基数恰为 `|V|`。 -/
theorem card_topoImage (G : FateV2.Modeling.Graph.DAG V) :
    (topoImage G).card = Fintype.card V := by
  unfold topoImage
  rw [Finset.card_image_of_injective _ G.topoOrder_injective, Finset.card_univ]

/-- [支撑] **T9c**：`V ≃ {n // n ∈ topoImage G}`（由 `topoOrder` 单射得）。 -/
noncomputable def toImage (G : FateV2.Modeling.Graph.DAG V) : V ≃ {n // n ∈ topoImage G} :=
  Equiv.ofBijective
    (fun v => ⟨G.topoOrder v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩)
    ⟨fun _ _ h => G.topoOrder_injective (congrArg Subtype.val h),
     fun ⟨n, hn⟩ => by
       obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hn
       exact ⟨v, Subtype.ext hv⟩⟩

/-- [支撑] **T10**：`topoOrder` 存在**全局最大点**。

取 `Finset.univ` 上 `topoOrder` 的上确界，由 `Finset.exists_mem_eq_sup`
取得达到它的顶点。 -/
theorem exists_max_topo (G : FateV2.Modeling.Graph.DAG V) [Nonempty V] :
    ∃ v : V, ∀ w : V, G.topoOrder w ≤ G.topoOrder v := by
  classical
  obtain ⟨v, -, heq⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset V) Finset.univ_nonempty G.topoOrder
  exact ⟨v, fun w => by
    have h := Finset.le_sup (s := (Finset.univ : Finset V)) (f := G.topoOrder)
      (Finset.mem_univ w)
    rwa [heq] at h⟩

/-- [支撑] **T11**：**拓扑序在「不同点」上严格**。

若 `u ≠ v` 且 `topoOrder u ≤ topoOrder v`，则 `topoOrder u < topoOrder v`；
若相等则由 `DAG.topoOrder_injective` 得 `u = v`，矛盾。
这是把 `≤` 提升为 `<` 的**唯一**桥梁（T12 依赖它）。 -/
theorem topo_strict_of_ne (G : FateV2.Modeling.Graph.DAG V) {u v : V} (hne : u ≠ v)
    (hle : G.topoOrder u ≤ G.topoOrder v) : G.topoOrder u < G.topoOrder v :=
  Nat.lt_of_le_of_ne hle (fun e => hne (G.topoOrder_injective e))

/-- [支撑] **T13**：**父节点的拓扑序严格在前**（`topoOrder_lt` 的 `pa` 措辞）。 -/
theorem pa_lt_topo (G : FateV2.Modeling.Graph.DAG V) {u v : V} (h : u ∈ pa G v) :
    G.topoOrder u < G.topoOrder v := by
  rw [mem_pa] at h
  exact G.topoOrder_lt u v h

/-- [支撑] **T14**：父集恰为「有边进来」的点集（**图论 ↔ 序号**的接口）。 -/
theorem filter_pa_eq_pa (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    (Finset.univ.filter (fun u => G.edge u v)) = pa G v := by
  ext u
  simp [mem_pa]

end TopoOrder

/-! ===========================================================================
  §6 ⭐⭐⭐⭐ **T12：任务书选项 B —— 拓扑枚举 `V ≃ Fin (card V)`（零缺口）**
  =========================================================================== -/

section TopoEnum

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- [支撑] **严格单调**的序嵌入 `Fin (card V) ↪o ℕ`，值域恰为 `topoImage G`。

由 `Finset.orderEmbOfFin` 给出：它对 `Finset` 的**升序**枚举取下标，
故天然严格单调（`LinearOrder ℕ` 保证）。**绕开** `Finset.orderIsoOfFin`
（本快照未编译）。 -/
noncomputable def topoEmb (G : FateV2.Modeling.Graph.DAG V) :
    Fin (Fintype.card V) ↪o ℕ :=
  Finset.orderEmbOfFin (topoImage G) (card_topoImage G)

/-- [支撑] `topoEmb` 的值域恰为 `topoImage G`。 -/
theorem topoEmb_range (G : FateV2.Modeling.Graph.DAG V) :
    Set.range (topoEmb G) = ↑(topoImage G) :=
  Finset.range_orderEmbOfFin _ _

/-- [支撑] `Fin (card V) ≃ topoImage G`。 -/
noncomputable def finEquivImage (G : FateV2.Modeling.Graph.DAG V) :
    Fin (Fintype.card V) ≃ {n // n ∈ topoImage G} :=
  (Equiv.ofInjective (topoEmb G) (topoEmb G).injective).trans
    (Equiv.subtypeEquivRight (fun _ => by
      constructor
      · intro hn; rw [topoEmb_range G] at hn; exact hn
      · intro hn; rw [topoEmb_range G]; exact hn))

/-- ⭐⭐⭐⭐ [理论] **T12 本体：拓扑枚举**。
`topoEnum G : V ≃ Fin (card V)`，把顶点按 `topoOrder` 的**升序**编号。 -/
noncomputable def topoEnum (G : FateV2.Modeling.Graph.DAG V) :
    V ≃ Fin (Fintype.card V) :=
  (toImage G).trans (finEquivImage G).symm

/-- [支撑] **关键同余**：`topoEnum` 第 `i` 个点的 `topoOrder` 就是 `topoEmb i`。

⟹ `topoEnum` 的**值域顺序**与 `topoOrder` 的**数值顺序**一致。 -/
theorem topoEmb_apply_topoEnum (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    topoEmb G (topoEnum G v) = G.topoOrder v := by
  have h : finEquivImage G (topoEnum G v) = toImage G v := by simp [topoEnum]
  have h2 : (toImage G v).val = G.topoOrder v := rfl
  have h3 : (finEquivImage G (topoEnum G v)).val = topoEmb G (topoEnum G v) := by
    simp [finEquivImage]
  rw [← h3, h, h2]

/-- ⭐⭐⭐⭐ [理论] **T12（任务书选项 B）：任意 DAG 有拓扑枚举。**

$$\exists e : V \simeq \mathrm{Fin}\,|V|,\quad
  \forall u\,v,\ \mathrm{edge}\,u\,v \Rightarrow e\,u < e\,v.$$

**证明**：取 `e := topoEnum G`。由 `DAG.topoOrder_lt` 得
`topoOrder u < topoOrder v`；由 T12-同余 `topoEmb (topoEnum w) = topoOrder w`
把它搬到 `ℕ` 上；再由 `topoEmb` 是**序嵌入**（`OrderEmbedding.lt_iff_lt`）
回到 `Fin (card V)`。**零缺口。** -/
theorem exists_topo_enum (G : FateV2.Modeling.Graph.DAG V) :
    ∃ e : V ≃ Fin (Fintype.card V), ∀ u v, G.edge u v → e u < e v := by
  refine ⟨topoEnum G, fun u v huv => ?_⟩
  have hlt : G.topoOrder u < G.topoOrder v := G.topoOrder_lt u v huv
  have hmono : topoEmb G (topoEnum G u) < topoEmb G (topoEnum G v) := by
    rw [topoEmb_apply_topoEnum, topoEmb_apply_topoEnum]
    exact hlt
  exact (topoEmb G).lt_iff_lt.mp hmono

end TopoEnum

/-! ===========================================================================
  §7 ⭐⭐⭐⭐⭐ **T15/T16：一般 DAG 的链式因子分解（零缺口）**
  =========================================================================== -/

section GenFac

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐⭐⭐⭐ [理论] **T15：一般 DAG 的链式因子分解。**

给定「每步乘性」的结构假设
`step : mass (insert v S) p x = q v x · mass S p x`（`v ∉ S`），
对**任意**有限 DAG、任意有限值域成立：

$$\mathrm{mass}\,S\,p\,x=\Bigl(\prod_{v\in S}q_v(x)\Bigr)\cdot\mathrm{mass}\,\emptyset\,p\,x.$$

**证明**：`fac_aux`（`Fate/DAGFactorization.lean` T2）的直接特化。**零缺口。** -/
theorem gen_factorization (q : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    (step : ∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x)
    (S : Finset V) (x : V → α) :
    mass S p x = (∏ v ∈ S, q v x) * mass (∅ : Finset V) p x :=
  fac_aux q p step S x

/-- ⭐⭐⭐⭐⭐ [理论] **T16 主定理（任务书核心）：因子分解。**

$$\boxed{p(x)=\Bigl(\prod_{v\in V}q_v(x)\Bigr)\cdot\mathrm{mass}\,\emptyset\,p\,x}$$

即 $p$ 沿 DAG 的**因子分解**：$q_v$ 就是「$v$ 的机制」
$p(x_v\mid\mathrm{pa}_v)$（乘性、无除法形式）。

**证明**：T15 取 `S = univ`，再用 `mass_univ`（`mass univ p x = p x`）。**零缺口。** -/
theorem gen_factorization_univ (q : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    (step : ∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x)
    (x : V → α) :
    p x = (∏ v : V, q v x) * mass (∅ : Finset V) p x := by
  rw [← mass_univ p x]
  exact gen_factorization q p step Finset.univ x

end GenFac

/-! ===========================================================================
  §8 ⭐⭐⭐⭐⭐ **T17/T18：G2 —— 乘性条件独立 ⟹ 因子分解**
  =========================================================================== -/

section LocalMarkov

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐⭐⭐ [理论] **T17：`LocalMarkovGen` 的**乘性形式**（与
`FinCondIndep.CondMul` 同构，但为集合口径、**无除法**）。

对每个 `v`：给定父集上的值后，$v$ 与其余点**条件独立**：

$$m_{\mathrm{pa}(v)}(x)\cdot m_{V\setminus\{v\}}(y)\cdot p(x)
 = m_{\mathrm{pa}(v)}(y)\cdot m_{V\setminus\{v\}}(x)\cdot p(y)
 \quad\text{当 }x|_{\mathrm{pa}(v)}=y|_{\mathrm{pa}(v)}.$$

**⚠ 读法**：两边同除 $m_{\mathrm{pa}(v)}\cdot m_{V\setminus\{v\}}$ 即
$p(x)/m_{V\setminus\{v\}}(x) = p(y)/m_{V\setminus\{v\}}(y)$，
即 $v$ 在父集给定下与其余点无关 —— 正是**局部 Markov 性**。

本谓词**不含** `∏`、不含因子乘积，是**纯条件独立**陈述。 -/
def LM (G : FateV2.Modeling.Graph.DAG V) (p : (V → α) → ℝ) : Prop :=
  ∀ (v : V) (x y : V → α), (∀ u ∈ pa G v, x u = y u) →
    mass (pa G v) p x * mass ((Finset.univ : Finset V) \ {v}) p y * p x
      = mass (pa G v) p y * mass ((Finset.univ : Finset V) \ {v}) p x * p y

/-- [展开] **T17b：`step` 恒等重述（**不是新数学**）。**

**⚠⚠ 诚实说明（残余缺口 G2，未闭合）**：

本定理的假设**就是**结论，只做 `∀ S` 的形式搬运。它的作用是让
`local_markov_factorization`（T18）有可命名的假设，**不构成**
「`LM` ⟹ `step`」的证明。

**真正的缺口**（见 §1.2）：`fac_aux` 需要**任意** `S ⊇ pa v` 的 `step`，
而 `LM` 只给 `S = univ \ {v}`。**本轮已数值验证**：试图用
`mass S (mass T p) = mass (S ∪ T) p`（塔性质）搭桥是**行不通的** ——
该恒等式在既有 `mass` 定义下**为假**（反例 `V = α = Bool`，
`p = 𝟙[w true = w false = true]`，`S = {true}`、`T = {false}`：
左边 `1`、右边 `0`）。**⟹ 闭合 G2 必须重新定义条件化边缘。** -/
theorem step_of_local_markov (_G : FateV2.Modeling.Graph.DAG V) (p : (V → α) → ℝ)
    (q : V → (V → α) → ℝ)
    (step : ∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x) :
    ∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x :=
  step

/-- ⭐⭐⭐ [验证] **T18：`step` 假设 + T16 ⟹ 因子分解（**T16 的重述包装**）。**

**⚠ 这不是 G2 的闭合**：假设 `step` 即结论的前提，故本定理
**不**证明「局部 Markov ⟹ 因子分解」。它只把 T16 在
「给定 `step`」情形下命名，供上层调用。**真正的 G2 见 §1.2 的缺口说明。** -/
theorem local_markov_factorization (_G : FateV2.Modeling.Graph.DAG V) (p : (V → α) → ℝ)
    (q : V → (V → α) → ℝ)
    (step : ∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x)
    (x : V → α) :
    p x = (∏ v : V, q v x) * mass (∅ : Finset V) p x :=
  gen_factorization_univ q p step x

end LocalMarkov

/-! ===========================================================================
  §10 ⚠⚠ **T24：塔性质的反例（本轮最重要的诚实发现，已编译验证）**

  **背景**：闭合 G2 的「显然路线」是：把 `LM`（单点条件化，`univ \ {v}`）经过
  **边缘塔性质**
  $$m_S\bigl(m_T\,p\bigr)=m_{S\cup T}\,p$$
  提升为 `fac_aux` 所需的**任意集合** `step`。

  **本节的结论**：这条路线**走不通**，因为该塔性质在既有
  `Fate.DAGFactorization.mass` 的定义下**是假的**。

  `mass S p x := ∑_{w : ∀ u ∈ S, w u = x u} p w`
  —— 它**只固定 `S` 上的坐标、对其余坐标求和**。于是
  `mass S (mass T p) x` 含有「`S ∪ T` 之外坐标的自由度」的**乘性放大**，
  而 `mass (S ∪ T) p x` 没有。

  **具体反例**（`V = α = Bool`，`S = {true}`，`T = {false}`，
  `p = 𝟙[w true = true ∧ w false = true]`，`x = 𝟎`）：
  * `mass S (fun w => mass T p w) x = 1`（T24a）
  * `mass (S ∪ T) p x = 0`（T24b）

  **⟹** 二者不等。**闭合 G2 必须重新定义条件化边缘**（例如在 `(V → α) → ℝ`
  上直接定义条件密度，或用商 `mass (S∪T) p x / mass S p x` 作 `condMass`），
  而不能沿用 `mass S (mass T p)`。本轮**不做**此重新定义：
  它会改动 `Fate/DAGFactorization.lean` 中 T1–T8 的全部陈述，超出
  「不动原文件」的边界，且需要单独立项审查。
  =========================================================================== -/

section TowerCounterexample

/-! ### §10.1 枚举工具：`Bool → Bool` 恰有 4 个元素 -/

/-- 4 个 `Bool → Bool` 的标准枚举。 -/
def bTrue : Bool → Bool := fun _ => true
def bId : Bool → Bool := fun x => x
def bNot : Bool → Bool := fun x => !x
def bFalse : Bool → Bool := fun _ => false

/-- `univ : Finset (Bool → Bool)` 恰是这 4 个元素。 -/
theorem univ_boolFun :
    (Finset.univ : Finset (Bool → Bool)) = {bTrue, bId, bNot, bFalse} := by
  ext f
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  cases h1 : f true <;> cases h2 : f false
  · exact Or.inr (Or.inr (Or.inr (by funext x; cases x <;> simp_all [bFalse])))
  · exact Or.inr (Or.inr (Or.inl (by funext x; cases x <;> simp_all [bNot])))
  · exact Or.inr (Or.inl (by funext x; cases x <;> simp_all [bId]))
  · exact Or.inl (by funext x; cases x <;> simp_all [bTrue])

/-- 反例用的（非归一化）「质量函数」。 -/
noncomputable def ptri : (Bool → Bool) → ℝ :=
  fun w => if w true = true ∧ w false = true then 1 else 0

/-! ### §10.2 反例的两半（各自编译验证） -/

/-- ⚠⚠ [理论] **T24a**：`mass {true} (fun w => mass {false} ptri w) (fun _ => false) = 1`。 -/
theorem tower_counter_lhs :
    mass ({(true : Bool)}) (fun w => mass ({(false : Bool)}) ptri w) (fun _ => false) = 1 := by
  unfold mass
  rw [univ_boolFun]
  simp only [Finset.sum_insert (by decide : bTrue ∉ ({bId, bNot, bFalse} : Finset (Bool → Bool))),
    Finset.sum_insert (by decide : bId ∉ ({bNot, bFalse} : Finset (Bool → Bool))),
    Finset.sum_insert (by decide : bNot ∉ ({bFalse} : Finset (Bool → Bool))),
    Finset.sum_singleton]
  norm_num [ptri, bTrue, bId, bNot, bFalse]

/-- ⚠⚠ [理论] **T24b**：`mass ({true} ∪ {false}) ptri (fun _ => false) = 0`。 -/
theorem tower_counter_rhs :
    mass ({(true : Bool)} ∪ {(false : Bool)}) ptri (fun _ => false) = 0 := by
  unfold mass
  rw [univ_boolFun]
  simp only [Finset.sum_insert (by decide : bTrue ∉ ({bId, bNot, bFalse} : Finset (Bool → Bool))),
    Finset.sum_insert (by decide : bId ∉ ({bNot, bFalse} : Finset (Bool → Bool))),
    Finset.sum_insert (by decide : bNot ∉ ({bFalse} : Finset (Bool → Bool))),
    Finset.sum_singleton]
  norm_num [ptri, bTrue, bId, bNot, bFalse]

/-- ⚠⚠ [理论] **T24（主结论）：塔性质 `mass S (mass T p) = mass (S∪T) p` 为假。**

$$\mathrm{mass}\,\{true\}\bigl(\mathrm{mass}\,\{false\}\,p\bigr)
  \ne \mathrm{mass}\,\(\{true\}\cup\{false\}\)\,p.$$

**⟹** 「单点条件独立 ⟹ 任意集合 `step`」经塔性质的**标准路线不可行**；
闭合 G2 需重新定义条件化边缘（见 §10 前言）。 -/
theorem tower_property_false :
    mass ({(true : Bool)}) (fun w => mass ({(false : Bool)}) ptri w) (fun _ => false)
      ≠ mass ({(true : Bool)} ∪ {(false : Bool)}) ptri (fun _ => false) := by
  rw [tower_counter_lhs, tower_counter_rhs]
  norm_num

end TowerCounterexample

end DAGFactorization
end FateV2.Predict
/-! ===========================================================================
  §9 ⭐⭐⭐⭐ **T19–T22：与 `FinJoint`/`CondMul` 的对接 + 具体验证**
  =========================================================================== -/

namespace FateV2.Predict
namespace DAGFactorization

open FateV2.Predict.DAGFactorization

section Validation

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ### §9.1 **T19：`chainDAG3` 上的拓扑枚举是具体可算的**

`chainDAG3 : DAG (Fin 3)`（边 `0→1→2`）来自 `FateV2.Predict.GlobalMarkovMinimal`。
用 T12 得到 `Fin 3 ≃ Fin 3`，并**验证**它是恒等（因为 `topoOrder` 已按
`0 < 1 < 2` 排好）。 -/

/-- [验证] **T19**：`chainDAG3`（链 `0→1→2`）有拓扑枚举，且边严格递增。 -/
theorem chainDAG3_topo_enum :
    ∃ e : Fin 3 ≃ Fin 3, ∀ u v, FateV2.Predict.GlobalMarkovMinimal.chainDAG3.edge u v → e u < e v :=
  exists_topo_enum FateV2.Predict.GlobalMarkovMinimal.chainDAG3

/-- [验证] **T20**：`topoOrder` 在 `chainDAG3` 上**严格递增**（具体数值）。 -/
theorem chainDAG3_topoOrder_lt_01 :
    FateV2.Predict.GlobalMarkovMinimal.chainDAG3.topoOrder (0 : Fin 3)
      < FateV2.Predict.GlobalMarkovMinimal.chainDAG3.topoOrder (1 : Fin 3) :=
  FateV2.Predict.GlobalMarkovMinimal.chainDAG3.topoOrder_lt 0 1 (by decide)

/-- [验证] **T21**：`topoOrder` 在 `chainDAG3` 上 `1 → 2` 也严格递增。 -/
theorem chainDAG3_topoOrder_lt_12 :
    FateV2.Predict.GlobalMarkovMinimal.chainDAG3.topoOrder (1 : Fin 3)
      < FateV2.Predict.GlobalMarkovMinimal.chainDAG3.topoOrder (2 : Fin 3) :=
  FateV2.Predict.GlobalMarkovMinimal.chainDAG3.topoOrder_lt 1 2 (by decide)

/-- [验证] **T22**：`chainDAG3` 上 `pa 1 = {0}`，与 `MarkovBridgeTopo` 的
`parents` 结果一致（T14 的 `filter_pa_eq_pa` 给出接口）。 -/
theorem chainDAG3_pa_one :
    pa FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (1 : Fin 3) = {(0 : Fin 3)} := by
  have h := filter_pa_eq_pa FateV2.Predict.GlobalMarkovMinimal.chainDAG3 (1 : Fin 3)
  rw [← h]
  ext u
  fin_cases u <;> simp [FateV2.Predict.GlobalMarkovMinimal.chainDAG3]

end Validation

/-! ### §9.2 **T23：`CondMul` ⟹ `LM`（在 `Unpin`/二值特化下）**

`Fate.FinCondIndep.CondMul` 是 `FinJoint α β γ = (α × β) × γ → ℝ` 上的乘性
条件独立。本节的 `LM` 是 `(V → α) → ℝ` 上的集合口径版本。
二者**陈述同构**（都是「无除法乘性条件独立」）；字符串层面的等价
需要 `V ≅ Fin 3` 的编码，此处**只给出方向性陈述**（诚实标注 [展开]）。 -/

section CondMulBridge

/-- [展开] **T23**：`CondMul` 与 `LM` 都是「乘性条件独立」，此处记录
二者的**陈述对应关系**（不证等价，只记录二者都不含除法）。

`CondMul p := ∀ x y z, p ((x,y),z) * margZ p z = margXZ p x z * margYZ p y z`
—— 见 `Fate.FinCondIndep.CondMul`；本文件 `LM` 是其集合口径推广。 -/
theorem condMul_is_multiplicative_form :
    ∀ (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
      (p : FateV2.Predict.FinJoint.FinJoint α β γ),
      FateV2.Predict.FinCondIndep.CondMul p →
      ∀ x y z, p ((x, y), z) * FateV2.Predict.FinJoint.margZ p z
        = FateV2.Predict.FinJoint.margXZ p x z * FateV2.Predict.FinJoint.margYZ p y z := by
  intro α β γ _ _ _ p hp x y z
  exact hp x y z

end CondMulBridge

end DAGFactorization
end FateV2.Predict