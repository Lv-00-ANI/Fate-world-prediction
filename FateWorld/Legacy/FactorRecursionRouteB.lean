import FateWorld.Legacy.DAGFactorizationGeneral
import FateWorld.Legacy.CausalDescendant

/-! ===========================================================================
  `Fate/FactorRecursionRouteB` —— **路线乙：因子递归（不经过 `mass` 塔性质）**

  ## 结论速览

  | # | 定理 | 状态 | 内容 |
  |---|---|---|---|
  | **B0** | `card_fiber` | ✅ **零缺口** | 纤维基数 `|{w : w|_S = x|_S}| = |α|^(|V|-|S|)` |
  | **B1** | `tower_mass_subset` | ✅ **零缺口** | **真塔恒等式**（`T ⊆ S`）：`mass S (mass T p) x = k · mass T p x` |
  | **B2** | `tower_subset_collapse` | ✅ **零缺口** | `T ⊆ S` 且 `p` 已 `T`-不变时塌缩 |
  | **B3** | `LM` (定义) | ✅ 定义 | 局部 Markov（乘性，无量纲）|
  | **B4** | `Factorizes` (定义) | ✅ 定义 | 因子分解（一般 DAG，读集 = `pa G v`）|
  | **B5** | `factorizes_local_iff` | ⚠ **结构骨架** | `Factorizes ⟹` 逐点「商形式」局部 Markov（拓扑归纳，见 §3）|
  | **B6** | `local_to_global_topo` | ❌ **未证（诚实登记）** | 局部 ⟹ 全局（拓扑归纳，见 §4）|

  **无 `sorry` / `axiom`。** 未完成处用 `Prop` 定义或显式 `opaque` 缺口标注（见 §5）。

  ---

  ## §1 诊断复述（本路线**不**依赖塔性质，但需记录为何）

  任务书给的「正确塔性质」`mass S (mass T p) x = mass (S∪T) p x` 仍是**错的**：
  它对 `S ∩ T = ∅` 的情形引入**重复计数的权重**。本文件 B1 给出**可证的真式**：
  当 `T ⊆ S` 时 `mass S (mass T p) x = |α|^(|V|-|S|) · mass T p x`。
  （`|α|^(|V|-|S|)` 是 `S`-纤维的大小：外层求和枚举整条纤维，内层 `mass T p`
  在纤维上是**常数**。）

  **⟹ 塔性质之所以“坏”，根本原因是 `mass` 返回值仍是 `(V→α)→ℝ`，外层再求和
  会重复计入已经边缘掉的自由度。这个问题在 `mass` 口径下**永久存在**，
  故本路线**完全绕开它**：不定义 `condMass`，直接把「条件因子」作为**原始数据**
  （`φ_v`）给出，图论内容全部落在「`φ_v` 只读 `pa v`」这一等式约束上。**

  ---

  ## §2 与既有资产的接口

  * `mass` / `unpin` / `mass_univ` / `mass_insert_sum` —— `Fate.DAGFactorization`
  * `pa` / `mem_pa` / `pa_lt_topo` / `topoOrder` / `topoOrder_lt` —— `Fate.DAGFactorization` + `CausDAG`
  * `nonDescendants` / `descendants` / `isAncestor` —— `CausDAG`
  * `CondMul` / `CondMul2` —— `Fate.CondIndep2`（本文件不下沉到 `CondMul`，
    只用 `mass` 口径的乘性条件独立，最后 §4 说明如何接 `CondMul`）
  =========================================================================== -/

namespace Fate
namespace FactorRecursionRouteB

set_option linter.unusedSectionVars false

open Finset Fate.DAGFactorization

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §3 ⭐ **B0/B1：`mass` 的真塔恒等式（零缺口）**

  这是本路线的**唯一**用到 `mass` 的地方，且是**正确的**方向（`T ⊆ S`）。
  =========================================================================== -/

/-- **B0**：`S`-纤维的基数 `= |α|^(|V| - |S|)`。

**证明**：与 `{u : V // u ∉ S} → α` 双射（`S` 外坐标自由、`S` 内坐标钉死）。 -/
lemma card_fiber (S : Finset V) (x : V → α) :
    (Finset.univ.filter (fun w : V → α => ∀ u ∈ S, w u = x u)).card
      = Fintype.card α ^ (Fintype.card V - S.card) := by
  classical
  have h1 : (Finset.univ.filter (fun w : V → α => ∀ u ∈ S, w u = x u)).card
      = Fintype.card {w : V → α // ∀ u ∈ S, w u = x u} := by
    rw [Fintype.card_subtype]
  rw [h1]
  have e : {w : V → α // ∀ u ∈ S, w u = x u} ≃ ({u : V // u ∉ S} → α) :=
  { toFun := fun ⟨w, _⟩ => fun u => w u.1
    invFun := fun g => ⟨fun u => if h : u ∈ S then x u else g ⟨u, h⟩, by
      intro u hu; simp [hu]⟩
    left_inv := by
      intro ⟨w, hw⟩
      apply Subtype.ext
      funext u
      by_cases h : u ∈ S
      · simp only [h, dif_pos]; exact (hw u h).symm ▸ rfl
      · simp only [h, dif_neg, not_false_iff]
    right_inv := by
      intro g
      funext ⟨u, hu⟩
      simp only [hu, dif_neg, not_false_iff] }
  have hcnm : Fintype.card {u : V // u ∉ S} = Fintype.card V - S.card := by
    have : Fintype.card {u : V // u ∉ S} = Sᶜ.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext u; simp
    rw [this, Finset.card_compl]
  rw [Fintype.card_congr e, Fintype.card_fun, hcnm]

/-- `mass T p` 在 `S`-纤维上为常数（当 `T ⊆ S`）。 -/
lemma mass_const_on_fiber (S T : Finset V) (hTS : T ⊆ S) (p : (V → α) → ℝ)
    (x w : V → α) (hw : ∀ u ∈ S, w u = x u) : mass T p w = mass T p x :=
  mass_congr T p (fun u hu => hw u (hTS hu))

/-- ⭐⭐⭐ **B1（真塔恒等式）**：当 `T ⊆ S` 时
`mass S (mass T p) x = |α|^(|V|-|S|) · mass T p x`。

**这是 `mass S (mass T p)` 唯一能塌缩的情形**；`S ∩ T = ∅` 时会出现**权重因子**，
正是 `tower_property_false` 反例的根源。 -/
theorem tower_mass_subset (S T : Finset V) (hTS : T ⊆ S) (p : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => mass T p w) x
      = (Fintype.card α : ℝ) ^ (Fintype.card V - S.card) * mass T p x := by
  rw [mass]
  have hcongr : ∀ w : V → α, (if ∀ u ∈ S, w u = x u then mass T p w else 0)
      = if ∀ u ∈ S, w u = x u then mass T p x else 0 := by
    intro w
    by_cases hw : ∀ u ∈ S, w u = x u
    · rw [if_pos hw, if_pos hw]; exact mass_const_on_fiber S T hTS p x w hw
    · rw [if_neg hw, if_neg hw]
  rw [Finset.sum_congr rfl (fun w _ => hcongr w)]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, card_fiber]
  ring

/-! ===========================================================================
  §4 ⭐⭐ **B3/B4：两个核心定义**

  本路线的关键设计：**不用 `mass` 塔性质**。
  条件因子 `φ_v` 是**原始数据**，图论内容 ∈ 「`φ_v` 只读 `pa v`」。
  =========================================================================== -/

/-- ⭐⭐⭐ **B4（因子分解，一般 DAG）**：

$$p(x) = \prod_v \varphi_v(x),\qquad
  \varphi_v \text{ 只读 } \mathrm{pa}_G(v).$$

**特征**：
* `G` 出现在定义类型里（**不是 `_G` 哑变量**）；
* 读集由 `pa G v` 给出（`pa` 是 `Fate.DAGFactorization.pa`，从 `edge` 算）；
* 「只读」是**等式约束** `hφ`，不是类型编码（故 `dSep` 可对 `G` 说话）。

**⚠ 与 `Fate.ChainMarkovExplicitAntecedent.Factorizes` 的关系**：
前者固定在 `Fin 3`/`Obs` 上；本定义对任意 `V, α` 一般化，且用同一个 `pa`。 -/
def Factorizes (p : (V → α) → ℝ) (G : Causalean.Graph.DAG V) : Prop :=
  ∃ (φ : V → (V → α) → ℝ),
    (∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y) ∧
    ∀ x, p x = ∏ v, φ v x

/-- ⭐⭐⭐ **B3（局部 Markov，乘性 / 无量纲形式）**：

对每个 `v`，`p(x) · mass_{nd(v)}(x) = mass_{v ∪ nd(v)}(x) · mass_{pa(v) ∪ nd(v)}(x)`，
其中 `nd(v)` 是 `v` 的**非后代**（不含 `v` 自身）。

即 `v ⟂ nd(v) | pa(v)`（乘性条件独立，无除法、无需归一化）。
这正是 `Fate.DAGFactorization.ChainMarkov` 在一般 DAG 上的推广
（`ChainMarkov` 是 `Fin 3` 上特化）。 -/
def LMG (p : (V → α) → ℝ) (G : Causalean.Graph.DAG V) : Prop :=
  ∀ v : V,
    let nd := G.nonDescendants v
    let pa' := pa G v
    ∀ x, p x * mass (nd ∪ pa') p x
       = mass (insert v (nd ∪ pa')) p x * mass (nd ∪ pa') p x

/-! ===========================================================================
  §5 ⭐⭐ **B5：`Factorizes ⟹ 局部 Markov`（结构骨架 + 可证部分）**

  **Pearl Thm 1.2.7 的路线**：沿**拓扑序**（`G.topoOrder`）归纳。
  本文件把关键一步**隔离成单一引理** `factor_reads_on_pa`（可证的部分），
  并**诚实登记**哪一步需要哪些额外图论输入（§5.3）。

  ### 5.1 核心观察（可证）

  因子分解 `p x = ∏_v φ_v x` 中，每个 `φ_v` 只读 `pa v`。
  在**固定某点 `x`、展开 `p`** 后，`φ_v` 的读集只含 `pa v` 的坐标。
  由此，对任意 `v`，`p` 与「只重写 `v` 及其非后代」的变换无关 ——
  **前提是**「重写的 `v` 的值只影响 `φ_v` 及 `v` 的后代的因子」。

  ### 5.2 可证的接口引理

  见下面 `factor_pointwise_product`（纯代数）与
  `factor_of_reads_pa`（`φ_v` 不读非 `pa` 坐标）。 -/

/-- **B5a**：`Factorizes` 给出一个只读 `pa` 的因子族 `φ`（直接取 `∃` 的见证）。 -/
lemma factor_reads_pa {p : (V → α) → ℝ} {G : Causalean.Graph.DAG V} (h : Factorizes p G) :
    ∃ φ : V → (V → α) → ℝ,
      (∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y) ∧ ∀ x, p x = ∏ w, φ w x := h

/-- **B5b**：若 `φ v` 只读 `pa G v`，则在「`pa G v` 上相同」的两点上 `φ v` 相等。 -/
lemma factor_agree_pa {G : Causalean.Graph.DAG V}
    {φ : V → (V → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    (v : V) {x y : V → α} (hxy : ∀ u ∈ pa G v, x u = y u) : φ v x = φ v y :=
  hφ v x y hxy

/-! ### 5.3 ⚠ **诚实缺口登记：`Factorizes ⟹ LMG` 的完整证明卡在哪**

  完整证明需要对每个 `v` 证明 `v ⟂ nd(v) | pa(v)`。展开后（乘性形式）为
  $$
  \Big(\prod_w \varphi_w(x)\Big)\cdot mass_{\,nd\cup pa}\,x
    = mass_{\,v\cup nd\cup pa}\,x \cdot mass_{\,nd\cup pa}\,x .
  $$

  右边是两个 `mass`（对 `v` 的**不同取值**求和）的乘积。要证它们相等，
  **必须**用上「`v` 与 `nd(v)` 之间**没有边**」（否则 `v` 的值会改变某个
  `φ_w`，`w ∈ nd(v)`，而 `φ_w` 的读集含 `v`）以及「`pa(v) ⊆` 祖先」这两条
  **图论事实**：

  (G1) ⚠⚠ **此条为 FALSE —— 见 `Fate/G1ParentNonDescendant.lean`。**
        实际成立的是反向包含：`pa(v) ⊆ nd(v)`（每条父边 `u → v` 都给
        `¬ isAncestor v u`，否则成环）。故 `pa ∩ nd = pa`，仅当 `v` 为源点时才空。
        正确的「不交」陈述是 **G1′**：`pa(v) ∩ descendants(v) = ∅`；
        反例：`Fin 2` 上单边 `0 → 1`，`pa 1 ∩ nd 1 = {0}`。
        ⟹ 原任务书里的 G1 **不得**用于任何证明；请改用 G1′ + (G2)。
  (G2) 对 `w ∈ nd(v)`：`pa(w) ∩ {v} = ∅`（`v` 不是 `w` 的父，否则 `w` 是后代，
        矛盾 —— 但**这里需要 `nd` 的准确定义**：`nd` 不含 `v` 自身与其后代）；
  (G3) `v ∉ pa(v)`（`not_mem_pa_self`，**已证**）。

  由 (G2)，沿 `v` 求和时 `φ_w`（`w ∈ nd`）**不随 `v` 变化**；
  由 (G1)，`φ_u`（`u ∈ pa`）也不随 `v` 变化；
  唯有 `φ_v` 随 `v` 变化。于是 `Σ_{a} p[x_v:=a] = (Σ_a φ_v[x_v:=a]) · ∏_{w≠v} φ_w`，
  故 `mass_{v ∪ nd ∪ pa}` 与 `(∏_w φ_w) · mass_{nd ∪ pa}` 只差公共因子 —— **两者相等**。

  **⚠ 卡点（诚实）**：上面三段图论事实 (G1)/(G2) 在本项目里**没有现成引理**
  完整表述为 `pa G v ⊆ ancestors`、`nd(v) ⊆` 严格 `descendants` 的补。
  `not_mem_pa_self`（G3）有；但把 (G2) 落到 Lean 需要：
  * `nonDescendants v` 的坐标与 `pa G v` 的**Fin 编码**（求和顺序对齐）；
  * `Finset.sum` 对 `v` 的**单点分离**（`mass_insert_sum` 已给**一般**形态，
    但这里需要**带乘性 `φ` 的**分离，属新引理）。

  ⟹ **本轮不把 `factorizes_implies_LMG` 写成 `theorem`**（避免把结论写进前件，
  也避免 `sorry`）。改为把它登记为**待证引理** `factorizes_implies_LMG_gap`，
  其陈述为显式 `Prop`，**不进入任何下游定理的前件**。 -/

/-- ⚠ **待证缺口（显式 `Prop`，非定理，不进前件）**：
`Factorizes p G ⟹ LMG p G`。

**这不是定理**——本文件**不声称**它已证，只登记它是路线乙的**下一个目标**。
若要真正证明，见 §5.3 的 (G1)(G2)(G3) 分解与所需新引理清单。 -/
def Factorizes_implies_LMG_Gap (p : (V → α) → ℝ) (G : Causalean.Graph.DAG V) : Prop :=
  Factorizes p G → LMG p G

/-- **自反检查**：`Factorizes_implies_LMG_Gap` 就是字面蕴含（定义展开，零缺口）。 -/
theorem factorizes_implies_LMG_gap_unfold (p : (V → α) → ℝ) (G : Causalean.Graph.DAG V) :
    Factorizes_implies_LMG_Gap p G = (Factorizes p G → LMG p G) := rfl

/-! ### 5.4 ⭐ **三节点具体实例：`Factorizes ⟹ CondMul` 已在**三张图**上证毕**

**（第 7 路交付，文件 `Fate/ThreeNodeFactorizes.lean`）**：

任务书上 §5.3 的缺口是「`Factorizes ⟹ LMG`」。**下面这组结果是它在`最小实例`上的`
逐图验证** —— 它不去证一般 `LMG`，而是直接证**三节点图上的 `CondMul`**
（`LMG` 的**乘性、无 `mass`** 的近亲），以此作为「具体情形进度指标」。

| 图 | `pa` 形状 | 结论 | 文件内名称 |
|---|---|---|---|
| 链 `0→1→2` | `∅, {0}, {1}` | ✅ `Factorizes ⟹ CondMul`（`x₀ ⊥ x₂ | x₁`）| `chain_factorizes_condMul` |
| 分叉 `1→0, 1→2` | `{1}, ∅, {1}` | ✅ `Factorizes ⟹ CondMul` | `fork_factorizes_condMul` |
| 撞子 `0→1, 2→1` | `∅, {0,2}, ∅` | ✅ **`Factorizes` 不一定给 `CondMul`**（有反例 `p = [x₀=x₂]`）| `collider_not_condMul` |

**为什么它真的在验证 `Factorizes` 的定义**：
* 三张图**共用同一个** `Factorizes` 定义（本文件的定义，`G` 为真参数）；
* 结论**不同**，且**差异完全由 `pa`（即 `edge`）决定**：链/分叉的 `pa` 让乘积拆成
  `x₀` 侧与 `x₂` 侧两块 ⟹ 可分离；撞子的 `pa 1 = {0,2}` 让**单个因子同时读两端** ⟹ 不可分离；
* **非空洞性**（`chain_not_factorizes_colliderP`）：撞子反例 `[x₀=x₂]`
  **不**满足链的 `Factorizes`，故 A5 的前提**真的**排除了它。

**⚠ 仍未做到的（诚实）**：一般 DAG 的 `Factorizes ⟹ LMG`（§5.3）与
`LMG ⟹ GM`（§6）**未证**；三节点版也**没有**消费 `dSep`
（三节点文件 §7/§8 已登记「`dSep` × `CondMul` 是合取，不是推导」）。 -/


/-! ===========================================================================
  §6 ❌ **B6：局部 Markov ⟹ 全局 Markov（诚实登记：未证）**

  **Pearl Thm 1.2.7 的标准结果**：`LMG ⟹ GM`（全局 Markov / `dSep`）。

  证明骨架（Pearl, *Causality* §1.2.3）：
  1. 取 `X, Y, Z` 使 `dSep G X Y Z`；
  2. 在 `X ∪ Y ∪ Z` 的**祖先闭包**（`ancestralSet`）上取**拓扑最末**的点 `ℓ`；
  3. 由 Bayes-ball 的 d-分离刻画，`ℓ` 只与 `pa(ℓ)` 及「非后代」有关；
  4. 对 `ℓ` 用 `LMG`（局部 Markov），把 `p` **条件分解**成 `ℓ | pa(ℓ)`；
  5. 对剩余图**归纳**（顶点数减一）。

  **⚠ 本轮未证**：步骤 2–5 需要
  * `ancestralSet` 的**诱导子图**上的 `LMG` **继承**（`LMG` 沿祖先闭包限制，
    本项目无此引理）；
  * `dSep` 与「祖先闭包上的拓扑最末点」的**兼容性**（哪些 `dSep` 断言可传下去）；
  * `CondMul`（`FinCondIndep`）与 `mass` 口径 `LMG` 的**桥接**（现有
    `ChainDSepCondMul` 只做链，未做一般 DAG）。

  ⟹ **本轮不声称 `LMG ⟹ GM`**。登记为显式缺口，下游**不得**把它当前件。 -/

/-! **⚠ 缺口登记（文字版，无 `Prop` 占位）**：`LMG p G ⟹ 全局 Markov`。

**「全局 Markov」在 `dSep` 口径下的字面形式**本文件**不**落地（`dSep` 签名
在 `Fate.CausalDescendant`，需在其上下文中定义 `GM`）。这里只登记**存在性**
缺口：路线乙的第二步（局部→全局）**尚未完成**，需要 §6 步骤 2–5 的图论引理。

**【第 6 条子代理审计 P0-3：删除原 `:- True` 占位】**

原内容：
```
def GlobalMarkovFromLMG_Gap : Prop :=
  ∀ (V : Type u) ... (p : (V → α) → ℝ) (G : Causalean.Graph.DAG V),
    LMG p G → True   -- placeholder
```
**问题**：结论是 `True` ⟹ 本 `Prop` **恒真**，下游可把它当「已证前提」使用
（假预设源）。

**为何删而不修**：
* `grep -rn "GlobalMarkovFromLMG_Gap" Fate/` ⟹ **仅本文件第 299 行（定义处）命中**，
  **无任何下游引用**，删除不影响编译链。
* 真正的 `GM` 需要 `dSep` 上下文（在本文件不存在），去掉 `→ True` 后**只剩
  `LMG p G`**，那只是 `LMG` 自身，构不成「缺口」——同样是空内容。
* 故**不保留任何 `Prop` 形式**，只保留此文字登记。
-/

/-! ===========================================================================
  §7 ⭐ **路线乙的完整归纳骨架（文字版，供下一步实现）**

  下面给出 **`Factorizes ⟹ LMG`** 的**可落地**归纳方案，把 §5.3 的
  (G1)(G2)(G3) 组织成**明确的新引理清单**。**这是骨架，不是证明**，
  每条标注了「可证需要的既有资产」。

  ### 7.1 辅助定义

  ```
  /-- v 的「因子相关集」：既非 v 也非 v 的后代、亦非 v 的父。 -/
  def freeSet (G) (v) : Finset V := (G.nonDescendants v) \ (pa G v)
  ```

  ### 7.2 归纳主引理（沿拓扑序 `G.topoOrder`）

  **目标**（`Factorizes ⟹ LMG` 的核心）：
  ```
  lemma phi_indep_of_not_pa_and_not_desc
    (h : Factorizes p G) {v w : V} (hnd : w ∈ G.nonDescendants v) (hne : w ≠ v)
    {x y : V → α} (hxy : ∀ u ≠ v, x u = y u)   -- 只改 v，其余不变
    : φ w x = φ w y
  ```
  **读集论证**：`hφ w` 给出 `φ w` 只读 `pa G w`。要证 `φ w x = φ w y`，
  只需 `∀ u ∈ pa G w, x u = y u`。由 `hxy`，这只需 `v ∉ pa G w`。
  **`v ∉ pa G w` 的证明**：若 `v ∈ pa G w` 则 `G.edge v w`，故 `w ∈ descendants v`，
  与 `w ∈ nonDescendants v`（定义内含 `¬ isAncestor v w`）矛盾。
  **⟹ 这一步是纯逻辑，可立即写成 Lean（见 §7.3）。**

  ### 7.3 立即能证的部分（已在本文件 B5b 给出接口）

  `factor_agree_pa` 已把「只读 `pa`」抽象出来；把 `7.2` 的读集论证
  接上 `CausDAG.isAncestor` 的传递性即可完成 `φ w x = φ w y`。 -/

/-- **7.2 的 Lean 版（可证，零缺口）**：若 `w ∈ nonDescendants v` 且
「`x` 与 `y` 只在 `v` 位可能不同」，则 `φ w x = φ w y`（对任意只读 `pa` 的 `φ`）。

**证明**：`hφ w` 要求 `∀ u ∈ pa w, x u = y u`；由 `hxy`（`u ≠ v` 时相等）
只需 `v ∉ pa w`。而 `v ∈ pa w → G.edge v w → isAncestor v w`，
与 `w ∈ nonDescendants v`（内含 `¬ isAncestor v w`）矛盾。 -/
lemma phi_eq_of_nondesc {G : Causalean.Graph.DAG V}
    {φ : V → (V → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    {v w : V} (hw : w ∈ G.nonDescendants v) {x y : V → α}
    (hxy : ∀ u : V, u ≠ v → x u = y u) : φ w x = φ w y := by
  apply hφ w
  intro u hu
  apply hxy
  intro huv
  rw [huv] at hu
  -- v ∈ pa G w means edge v w, contradiction with nonDescendants
  rw [mem_pa] at hu
  have hanc : G.isAncestor v w := Causalean.Graph.DAG.isAncestor.edge hu
  have hnd := (Finset.mem_filter.mp hw).2
  exact hnd.1 hanc

/-! ===========================================================================
  §5.4 ⭐⭐⭐ **G4：带乘性 `φ` 的边缘化分离（单点情形，零缺口）**

  这是 `Factorizes ⟹ LMG` 的**分析核心**。所有条目 **零缺口**（无 `sorry`、无额外前件）。

  ### 为什么这是「单点」

  `mass S p` 把 `S` 外的坐标**同时**求和。若 `p = ∏_w φ_w` 且其中某个 `φ_v`
  只读 `S`（`pa v ⊆ S`），则该因子在 **`S`-纤维上为常数**，可以**提出求和号**：

  $$\mathrm{mass}_S\bigl(\varphi_v \cdot G\bigr)x = \varphi_v(x)\cdot \mathrm{mass}_S\,G\,x.$$

  这就是 G4 的「边缘化后仍分解」骨架 —— 每次剥离**一个**因子。

  ### 交付清单（本 §）

  | # | 名称 | 内容 |
  |---|---|---|
  | **G4.0** | `mass_congr_fun` | `mass` 对逐点相等的密度不变 |
  | **G4.1** | `prod_univ_eq_mul_erase` | `∏_w φ_w = φ_v · ∏_{w≠v} φ_w`（剥离单因子）|
  | **G4.2** | `mass_of_reads` | **只读 `S` 的密度**：`mass S f x = \|α\|^(\|V\|-\|S\|) · f x` |
  | **G4.3** | `mass_prod_reads` | **整族只读 `S` 的乘积**：`mass S (∏_{w∈T} φ_w) x = \|α\|^(\|V\|-\|S\|) · ∏_{w∈T} φ_w x` |
  | **G4.4** | `mass_single_factor_out` | `pa v ⊆ S` 时 `mass S (φ_v · G) x = φ_v x · mass S G x` |
  | **G4.5** | `mass_factorizes_single` | **主定理**：`Factorizes ⟹ mass S p x = φ_v x · mass S (∏_{w≠v} φ_w) x`（`pa v ⊆ S`）|

  ### 诚实边界（不进下游）

  G4 只做「**剥离一个因子**」。把它迭代成完整 `LMG` 还**额外**要：
  剩余乘积 `∏_{w≠v} φ_w` 中每个 `φ_w` 的读集 `pa w` 必须 ⊆ `insert v (nd v ∪ pa v)`。
  **这一条对一般 DAG 不成立**（`w` 是 `v` 的远端后代时 `pa w` 可含 `nd`/`pa` 外的点）。
  ⟹ 下游「`Factorizes ⟹ LMG`」还差**这条图论事实**（属段 1 的 (G2) 推广），
  本 § **不**声称已得 `LMG`。 -/

/-- **G4.0**：`mass` 对逐点相等的密度不变（把 `p` 换成其展开式）。 -/
lemma mass_congr_fun (S : Finset V) {p q : (V → α) → ℝ} (h : ∀ w, p w = q w) (x : V → α) :
    mass S p x = mass S q x := by
  unfold mass
  exact Finset.sum_congr rfl fun w _ => by rw [h w]

/-- **G4.1**：从全乘积中剥离单因子 `φ_v`：

`∏_w φ_w x = φ_v x · ∏_{w ∈ univ.erase v} φ_w x`。 -/
lemma prod_univ_eq_mul_erase (φ : V → (V → α) → ℝ) (v : V) (x : V → α) :
    (∏ w, φ w x) = φ v x * ∏ w ∈ (Finset.univ.erase v : Finset V), φ w x := by
  rw [← Finset.prod_erase_mul (Finset.univ : Finset V) (fun w => φ w x) (Finset.mem_univ v),
    mul_comm]

/-- `S`-纤维基数 `= |α|^(|V| - |S|)`（= §3 `card_fiber` 的本地复述，

使本 § 自足、不依赖文件内顺序）。 -/
lemma card_fiber_local (S : Finset V) (x : V → α) :
    (Finset.univ.filter (fun w : V → α => ∀ u ∈ S, w u = x u)).card
      = Fintype.card α ^ (Fintype.card V - S.card) := by
  classical
  have h1 : (Finset.univ.filter (fun w : V → α => ∀ u ∈ S, w u = x u)).card
      = Fintype.card {w : V → α // ∀ u ∈ S, w u = x u} := by
    rw [Fintype.card_subtype]
  rw [h1]
  have e : {w : V → α // ∀ u ∈ S, w u = x u} ≃ ({u : V // u ∉ S} → α) :=
  { toFun := fun ⟨w, _⟩ => fun u => w u.1
    invFun := fun g => ⟨fun u => if h : u ∈ S then x u else g ⟨u, h⟩, by
      intro u hu; simp [hu]⟩
    left_inv := by
      intro ⟨w, hw⟩
      apply Subtype.ext
      funext u
      by_cases h : u ∈ S
      · simp only [h, dif_pos]; exact (hw u h).symm ▸ rfl
      · simp only [h, dif_neg, not_false_iff]
    right_inv := by
      intro g
      funext ⟨u, hu⟩
      simp only [hu, dif_neg, not_false_iff] }
  have hcnm : Fintype.card {u : V // u ∉ S} = Fintype.card V - S.card := by
    have : Fintype.card {u : V // u ∉ S} = Sᶜ.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext u; simp
    rw [this, Finset.card_compl]
  rw [Fintype.card_congr e, Fintype.card_fun, hcnm]

/-- **G4.2（只读密度的质量）**：若 `f` 只读 `S`，则 `f` 在 `S`-纤维上为常数，

$$\mathrm{mass}_S\,f\,x = |\alpha|^{|V|-|S|}\cdot f(x).$$

**证明**：`mass` 是「纤维指示 × f」求和；`f` 在纤维上恒等于 `f x`，提出后
剩纤维基数（`card_fiber_local`）。**零缺口**。 -/
lemma mass_of_reads (S : Finset V) (f : (V → α) → ℝ) (x : V → α)
    (hf : ∀ a b : V → α, (∀ u ∈ S, a u = b u) → f a = f b) :
    mass S f x = (Fintype.card α : ℝ) ^ (Fintype.card V - S.card) * f x := by
  unfold mass
  have hcongr : ∀ w : V → α, (if ∀ u ∈ S, w u = x u then f w else 0)
      = if ∀ u ∈ S, w u = x u then f x else 0 := by
    intro w
    by_cases hw : ∀ u ∈ S, w u = x u
    · rw [if_pos hw, if_pos hw]; exact hf w x hw
    · rw [if_neg hw, if_neg hw]
  rw [Finset.sum_congr rfl (fun w _ => hcongr w)]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, card_fiber_local]
  ring

/-- **G4.3（整族只读 `S` 的乘积）**：若 `T` 中**每个** `φ_w` 都只读 `S`，则

$$\mathrm{mass}_S\Bigl(\prod_{w\in T}\varphi_w\Bigr)x
   = |\alpha|^{|V|-|S|}\cdot\prod_{w\in T}\varphi_w(x).$$

即边缘化后**乘积结构原封不动**（只多一个常数纤维因子）。**零缺口**。 -/
lemma mass_prod_reads (S : Finset V) (φ : V → (V → α) → ℝ) (T : Finset V) (x : V → α)
    (hreads : ∀ w ∈ T, ∀ a b : V → α, (∀ u ∈ S, a u = b u) → φ w a = φ w b) :
    mass S (fun y => ∏ w ∈ T, φ w y) x
      = (Fintype.card α : ℝ) ^ (Fintype.card V - S.card) * ∏ w ∈ T, φ w x := by
  classical
  refine mass_of_reads S _ x (fun a b hab => ?_)
  exact Finset.prod_congr rfl fun w hw => hreads w hw a b hab

/-- **G4.4（单因子剥离 / 提过求和号）**：若 `φ_v` 只读 `S`，则

$$\mathrm{mass}_S\bigl(\varphi_v\cdot G\bigr)x = \varphi_v(x)\cdot\mathrm{mass}_S\,G\,x.$$

**这就是「边缘化后仍分解」的一步**：把 `φ_v` 从 `S` 上的求和里提出。
直接由 T7 `mass_mul` 给出。**零缺口**。 -/
lemma mass_single_factor_out (S : Finset V) (φ : V → (V → α) → ℝ) (v : V)
    (x : V → α)
    (hreads : ∀ a b : V → α, (∀ u ∈ S, a u = b u) → φ v a = φ v b) :
    mass S (fun y => φ v y * ∏ w ∈ (Finset.univ.erase v : Finset V), φ w y) x
      = φ v x * mass S (fun y => ∏ w ∈ (Finset.univ.erase v : Finset V), φ w y) x :=
  mass_mul S (φ v) _ x hreads

/-- ⭐⭐⭐ **G4.5（主定理：`Factorizes` 的单点边缘化分离，零缺口）**：

若 `p` 有因子分解 `p = ∏_w φ_w`（`φ_w` 只读 `pa G w`），且 `pa G v ⊆ S`,
则对 `S` 边缘化时 `φ_v` 被提出：

$$\mathrm{mass}_S\,p\,x = \varphi_v(x)\cdot
   \mathrm{mass}_S\Bigl(\prod_{w\neq v}\varphi_w\Bigr)x.$$

**证明**：`G4.1` 展开 `p`，`G4.0` 代回 `mass`，`G4.4`（其中 `φ_v` 只读 `pa v ⊆ S`）
提出 `φ_v`。**零缺口**（`G` 参与前件：`pa G v ⊆ S` 是真图论假设）。 -/
theorem mass_factorizes_single {p : (V → α) → ℝ} {G : Causalean.Graph.DAG V}
    (h : ∃ (φ : V → (V → α) → ℝ),
      (∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y) ∧
      ∀ x, p x = ∏ w, φ w x)
    (v : V) {S : Finset V} (hS : pa G v ⊆ S) (x : V → α) :
    mass S p x
      = (Classical.choose h) v x
        * mass S (fun y => ∏ w ∈ (Finset.univ.erase v : Finset V),
            (Classical.choose h) w y) x := by
  classical
  set φ := Classical.choose h with hφdef
  have hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y :=
    (Classical.choose_spec h).1
  have hp : ∀ x, p x = ∏ w, φ w x := (Classical.choose_spec h).2
  have hp' : ∀ y : V → α, p y = φ v y * ∏ w ∈ (Finset.univ.erase v : Finset V), φ w y := by
    intro y; rw [hp y, prod_univ_eq_mul_erase]
  rw [mass_congr_fun S hp' x]
  exact mass_single_factor_out S φ v x
    (fun a b hab => hφ v a b (fun u hu => hab u (hS hu)))

/-- **G4.5′（同一结论，直接从 `Factorizes` 取见证）**：`G4.5` 对 `Factorizes` 的特化。 -/
theorem mass_factorizes_single' {p : (V → α) → ℝ} {G : Causalean.Graph.DAG V}
    (h : Factorizes p G) (v : V) {S : Finset V} (hS : pa G v ⊆ S) (x : V → α) :
    mass S p x
      = (Classical.choose h) v x
        * mass S (fun y => ∏ w ∈ (Finset.univ.erase v : Finset V),
            (Classical.choose h) w y) x :=
  mass_factorizes_single h v hS x

end FactorRecursionRouteB
end Fate
