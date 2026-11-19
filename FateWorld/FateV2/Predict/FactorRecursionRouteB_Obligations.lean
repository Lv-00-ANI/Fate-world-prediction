import FateWorld.FateV2.Predict.FactorRecursionRouteB
/-!
  # Predict · FactorRecursionRouteB_Obligations

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FactorRecursionRouteB_Obligations.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorRecursionRouteB
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/FactorRecursionRouteB_Obligations` —— **路线 3 的裁决与可证义务**

  ## 结论（三条，全部机器验证）

  | # | 结果 | 状态 |
  |---|---|---|
  | **G1'** | `pa G v ⊆ nonDescendants v`（父必是非后代） | ✅ **已证** |
  | **G1✗** | 任务书的 `pa ∩ nd = ∅` | ❌ **已证伪**（反例：`Fin 3` 链，`0 ∈ pa 1 ∩ nd 1`）|
  | **G2**  | `w ∈ nd v ⟹ v ∉ pa w` | ✅ **已证** |
  | **G3**  | `v ∉ pa G v` | ✅ 既有 `not_mem_pa_self` |
  | **R3✗** | `Factorizes p G ⟹ LMG p G` | ❌ **已证伪**（反例见 §3）|

  ### ⚠ 对下游的影响

  **`Factorizes_implies_LMG_Gap` 不能用 `theorem` 落地**：它不是「未证」，
  而是**在这个定义下为假**。下游**不得**把它当前件，也**不得**期望
  用 G1+G4 证出它。要救它必须有**定义修正**（见 §5）。

  **零 `sorry` / 零 `axiom`。** 所有 `False` 陈述都以**显式反例定理**给出。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace FactorRecursionRouteB

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Finset FateV2.Predict.DAGFactorization FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ===========================================================================
  §1 **G1'：正确的「父/非后代」关系**（零缺口）
  =========================================================================== -/

/-- ⭐⭐ **G1'（可证，零缺口）**：`v` 的每个父都是 `v` 的**非后代**。

理由：`u ∈ pa v` 给 `edge u v`，故 `isAncestor u v`。若 `v` 还是 `u` 的祖先，
则 `v ⇝ u → v` 是**有向环**，与 `DAG.acyclic` 矛盾。故 `¬ isAncestor v u`。
又 `u ≠ v`（`not_mem_pa_self`）。两条正是 `nonDescendants v` 的成员判据。

**⟹ 与任务书的 G1 方向**相反**：`pa` 与 `nd` **不**不相交，而是 `pa ⊆ nd`。 -/
theorem pa_subset_nonDescendants (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    pa G v ⊆ G.nonDescendants v := by
  intro u hu
  unfold FateV2.Modeling.Graph.DAG.nonDescendants
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · intro hvu
    have hanc : G.isAncestor u v :=
      FateV2.Modeling.Graph.DAG.isAncestor.edge (mem_pa.mp hu)
    exact G.isAncestor_irrefl v (G.isAncestor_trans hvu hanc)
  · intro huv
    rw [huv] at hu
    exact FateV2.Predict.DAGFactorization.not_mem_pa_self G v hu

/-- ⭐ **G1' 的推论**：`pa v ∪ nd v = nd v`（`pa` 是「冗余」的）。 -/
theorem pa_union_nonDescendants (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    pa G v ∪ G.nonDescendants v = G.nonDescendants v :=
  Finset.union_eq_right.mpr (pa_subset_nonDescendants G v)

/-! ===========================================================================
  §2 **G2 / G3**（零缺口）
  =========================================================================== -/

/-- ⭐ **G2（可证，零缺口）**：非后代 `w` 不以 `v` 为父。 -/
theorem not_pa_of_nondesc (G : FateV2.Modeling.Graph.DAG V) {v w : V}
    (hw : w ∈ G.nonDescendants v) : v ∉ pa G w := by
  rw [mem_pa]
  intro hvw
  have : G.isAncestor v w := FateV2.Modeling.Graph.DAG.isAncestor.edge hvw
  exact (Finset.mem_filter.mp hw).2.1 this

/-- ⭐ **G3（复用既有）**：`v ∉ pa G v`。 -/
theorem g3_not_mem_pa_self (G : FateV2.Modeling.Graph.DAG V) (v : V) : v ∉ pa G v :=
  FateV2.Predict.DAGFactorization.not_mem_pa_self G v

/-! ===========================================================================
  §3 ❌ **`Factorizes ⟹ LMG` 的反例（主裁决，机器验证）**

  在 `Fin 3` 的链 `0 → 1 → 2` 上取**常数** `p ≡ 2`：

  * ✅ `Factorizes p G`：取 `φ_0 ≡ 2`、`φ_1 ≡ φ_2 ≡ 1`
    （`pa 0 = ∅`，故 `φ_0` 常数合法）。乘积恒为 `2`。
  * ❌ `LMG p G`：在 `v = 1` 处，`nd(1) = {0}`、`pa(1) = {0}`，故
    `nd ∪ pa = {0}`、`insert 1 ({0}) = {0,1}`。`LMG` 断言
    `p x · mass{0} p x = mass{0,1} p x · mass{0} p x`，
    但 `mass{0} = 8`、`mass{0,1} = 4`（`α = Bool`，`2^(3−k) · 2`），
    两边 `16 ≠ 32`。

  **⟹ `Factorizes_implies_LMG_Gap p G` 在此例上为 `False`**，
  即 `Factorizes p G ⟹ LMG p G` **不可证**（除非改定义）。

  **根因（诚实登记）**：`Factorizes` 的读集是 `pa G v`，**不含 `v` 自身**。
  于是 `φ_v` 对 `v` 的取值**毫无约束**，`p` 对 `v` 的依赖全部跑到
  **`v` 的子节点因子**上；而子节点**既不在 `nd(v)` 也不在 `pa(v)`**，
  所以对 `v` 求和时 `LMG` 右端的 `mass` 与左端的 `p` 无法对齐 ——
  **G4 的「只留 `φ_v` 变化」在现定义下不成立**（`φ_v` 根本不随 `v` 变）。
  =========================================================================== -/

/-- 链 `0 → 1 → 2` 的边关系（`Fin 3`）。 -/
def chain3Edge : Fin 3 → Fin 3 → Prop := fun i j => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

/-- 链 `0 → 1 → 2` 作为真 DAG（无环性来自沿边递增的 `Fin.val`）。 -/
def chain3DAG : FateV2.Modeling.Graph.DAG (Fin 3) where
  edge := chain3Edge
  decEdge := fun i j => by unfold chain3Edge; infer_instance
  acyclic := by
    intro v h
    have key : ∀ {a b : Fin 3}, Relation.TransGen chain3Edge a b → a.val < b.val := by
      intro a b htr
      induction htr with
      | single hab => unfold chain3Edge at hab
                      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ hbc ih => unfold chain3Edge at hbc
                         rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    exact absurd (key h) (by simp)

/-- ❌ **反例第一半**：常数 `p ≡ 2` 在链 `0→1→2` 上**确实**因子分解。 -/
theorem chain3_factorizes_const :
    Factorizes (α := Bool) (fun _ => (2 : ℝ)) chain3DAG := by
  refine ⟨fun v _ => if v = (0 : Fin 3) then 2 else 1, ?_, ?_⟩
  · intro v x y _; rfl
  · intro x
    simp only
    rw [Finset.prod_eq_single (0 : Fin 3)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (mem_univ _) h

/-- `nonDescendants 1 = {0}`（链上 `1` 的非后代只有 `0`）。 -/
theorem chain3_nd_one : chain3DAG.nonDescendants 1 = {(0 : Fin 3)} := by decide

/-- `pa 1 = {0}`。 -/
theorem chain3_pa_one : pa chain3DAG 1 = {(0 : Fin 3)} := by decide

/-- 纤维计数：`Fin 3 → Bool` 上固定 `S` 的纤维大小 `= 2^(3 − |S|)`。（自足版，不改主文件。） -/
theorem fiber_card3 (S : Finset (Fin 3)) (x : Fin 3 → Bool) :
    (Finset.univ.filter (fun w : Fin 3 → Bool => ∀ u ∈ S, w u = x u)).card
      = 2 ^ (3 - S.card) := by
  classical
  have e : {w : Fin 3 → Bool // ∀ u ∈ S, w u = x u} ≃ ({u : Fin 3 // u ∉ S} → Bool) :=
  { toFun := fun ⟨w, _⟩ u => w u.1
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
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun]
  have hcn : Fintype.card {u : Fin 3 // u ∉ S} = 3 - S.card := by
    have : Fintype.card {u : Fin 3 // u ∉ S} = Sᶜ.card := by
      rw [Fintype.card_subtype]; congr 1; ext u; simp
    rw [this, Finset.card_compl, Fintype.card_fin]
  have hb : Fintype.card Bool = 2 := rfl
  rw [hcn, hb]

/-- 常数函数在 `Fin 3 → Bool` 上的 `mass`（`= 2^(3−|S|) · c`）。 -/
theorem mass_const3 (S : Finset (Fin 3)) (c : ℝ) (x : Fin 3 → Bool) :
    mass S (fun _ : Fin 3 → Bool => c) x = (2 : ℝ) ^ (3 - S.card) * c := by
  classical
  have hcard := fiber_card3 S x
  -- reformulate mass as a plain sum over the fiber
  have hmass : mass S (fun _ : Fin 3 → Bool => c) x
      = ((Finset.univ.filter (fun w : Fin 3 → Bool => ∀ u ∈ S, w u = x u)).card : ℝ) * c := by
    unfold mass
    have : ∀ w : Fin 3 → Bool,
        (if ∀ u ∈ S, w u = x u then (fun _ : Fin 3 → Bool => c) w else 0)
          = if ∀ u ∈ S, w u = x u then c else 0 := by
      intro w; by_cases hw : ∀ u ∈ S, w u = x u <;> simp [hw]
    simp only [this]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hmass, hcard]
  norm_num

/-- ❌ **反例第二半**：同一个 `p ≡ 2` 在链 `0→1→2` 上**不**满足 `LMG`。 -/
theorem chain3_not_lmg_const : ¬ LMG (α := Bool) (fun _ => (2 : ℝ)) chain3DAG := by
  intro h
  have h1 := h 1 (fun _ => true)
  simp only [chain3_nd_one, chain3_pa_one] at h1
  have e1 : mass ({(0 : Fin 3)} ∪ {(0 : Fin 3)}) (fun _ : Fin 3 → Bool => (2 : ℝ))
      (fun _ => true) = 8 := by
    rw [Finset.union_self, mass_const3]; norm_num
  have e2 : mass (insert (1 : Fin 3) ({(0 : Fin 3)} ∪ {(0 : Fin 3)}))
      (fun _ : Fin 3 → Bool => (2 : ℝ)) (fun _ => true) = 4 := by
    rw [Finset.union_self, mass_const3]
    have hc : (insert (1 : Fin 3) {(0 : Fin 3)} : Finset (Fin 3)).card = 2 := by decide
    rw [hc]; norm_num
  rw [e1, e2] at h1
  norm_num at h1

/-- ❌❌ **主裁决**：**不存在**「`Factorizes ⟹ LMG`」的证明。 -/
theorem factorizes_implies_LMG_false :
    ¬ (∀ (p : (Fin 3 → Bool) → ℝ), Factorizes p chain3DAG → LMG p chain3DAG) := by
  intro h
  exact chain3_not_lmg_const (h _ chain3_factorizes_const)

/-! ===========================================================================
  §4 ❌ **G1 原陈述的反例**（任务书写错了方向）
  =========================================================================== -/

/-- ❌ **任务书的 G1 为假**：在链 `0→1→2` 上 `pa(1) = {0}` 且 `0 ∈ nd(1)`，
故两者**相交**。 -/
theorem g1_intersection_nonempty :
    ¬ Disjoint (pa chain3DAG 1) (chain3DAG.nonDescendants 1) := by
  intro hdisj
  have hmem : (0 : Fin 3) ∈ pa chain3DAG 1 ∩ chain3DAG.nonDescendants 1 := by
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · rw [mem_pa]
      show chain3DAG.edge 0 1
      left; exact ⟨rfl, rfl⟩
    · unfold FateV2.Modeling.Graph.DAG.nonDescendants
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by decide, by decide⟩
  rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
  rw [hdisj] at hmem
  exact absurd hmem (by simp)

/-! ===========================================================================
  §5 ⚠ **救「`Factorizes ⟹ LMG`」需要的定义修正（登记，不改主文件）**

  **修正方案 A（标准 Pearl 形式）**：把读集从 `pa v` 改成 `insert v (pa v)`：

  ```
  def FactorizesReads (p) (G) : Prop :=
    ∃ φ, (∀ v x y, (∀ u ∈ insert v (pa G v), x u = y u) → φ v x = φ v y) ∧
         ∀ x, p x = ∏ v, φ v x
  ```

  **但这**仍不够**：即使 `φ_v` 读 `v`，`LMG` 在对 `v` 求和时 `v` 的子节点因子
  `φ_w (w 是 v 的子)` 仍随 `v` 变化而 `w ∉ nd(v) ∪ pa(v)`。
  真正的证明需要**沿拓扑序对子树做归纳**（Pearl Thm 1.2.7），
  把 `mass (nd(v))` 递归**展开成对整条后代子树的求和**。
  这在 `mass` 口径下等价于**塔性质**——本项目已证伪（`tower_property_false`）。

  **⟹ 结论（诚实）**：
  * 「段 1：`Factorizes ⟹ LMG`」在当前 `mass` 口径下**不能**用 G1+G4 完成；
  * 路线乙若坚持，需要**先**给出一个**自足的递归因子结构**
    （例如直接对 `p` 给出「条件因子的塔」而不是浮点 `mass`），
    并证明它与 `LMG` 的**单点分离**形式等价；
  * 本文件**不**声称该修正已证，也不把它写成 `theorem`。
  -/

/-- ⚠ **登记（显式 `Prop`，非定理）**：修正后的因子分解（读集含 `v`）。 -/
def FactorizesReadsSelf (p : (Fin 3 → Bool) → ℝ) (G : FateV2.Modeling.Graph.DAG (Fin 3)) : Prop :=
  ∃ φ : Fin 3 → (Fin 3 → Bool) → ℝ,
    (∀ v x y, (∀ u ∈ insert v (pa G v), x u = y u) → φ v x = φ v y) ∧
    ∀ x, p x = ∏ v, φ v x

/-- **自反检查**：`FactorizesReadsSelf` 的定义展开（零缺口，仅作类型对齐）。 -/
theorem factorizesReadsSelf_unfold (p : (Fin 3 → Bool) → ℝ) (G : FateV2.Modeling.Graph.DAG (Fin 3)) :
    FactorizesReadsSelf p G ↔
      ∃ φ : Fin 3 → (Fin 3 → Bool) → ℝ,
        (∀ v x y, (∀ u ∈ insert v (pa G v), x u = y u) → φ v x = φ v y) ∧
        ∀ x, p x = ∏ v, φ v x := Iff.rfl

end FactorRecursionRouteB
end FateV2.Predict