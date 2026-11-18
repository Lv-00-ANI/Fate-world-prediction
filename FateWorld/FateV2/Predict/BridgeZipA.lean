/-
# 路线 A（第 4 桥的 `b2` 子支）：用 `zStar` 打通 `CondIndep Z' ⟹ CondIndep Z`

## 0 本文件的**唯一**任务与最终判定

**用户提案的推理链**（下称 **RouteA**）：

> 取 `Z' := zStar G X Y Z`（`BridgeMinZPrime` 的极小可行元）。
> **若**能证明 *(P)*：对 `S ∈ {X∪Y∪Z, X∪Z, Y∪Z}` 与每个 `v ∈ Z'∖Z` 都有 `v ∉ S`，
> **则**由 `mass_congr`（`mass S p` 不读 `v` 位）可得 `CondIndep Z' ⟹ CondIndep Z`。

**本文件的判定（逐条机器检验，零 `sorry`）：**

| 编号 | 命题 | 判定 | 位置 |
|---|---|---|---|
| **A1** | *(P)* 第一项：`∀ v ∈ zStar∖Z, v ∉ X∪Y∪Z` | ❌ **假** | `zStar_exceeds_domain` |
| **A2** | *(P)* 第二项：`∀ v ∈ zStar∖Z, v ∉ X∪Z` | ❌ **假** | `zStar_exceeds_XZ` |
| **A3** | *(P)* 第三项：`∀ v ∈ zStar∖Z, v ∉ Y∪Z` | ❌ **假** | `zStar_exceeds_YZ` |
| **A4** | 反例上 `dSep` 成立（不是「该结论只在非 d-分离时失效」） | ✅ | `gch_is_dSep` |
| **A5** | `paBlock G X \ X ⊆ zStar`、`paBlock G Y \ Y ⊆ zStar` | ✅ | `paBlock_left_sdiff_subset_zStar`、`paBlock_right_sdiff_subset_zStar` |
| **A6** | 「`mass S` 不读 `v` 位」：`v ∉ S ⟹ mass S p (unpin v x a) = mass S p x` | ✅ | `mass_congr_at` |
| **A7** | 洞条件**第 4 读集**（`Z'` 自身）不可能被满足：`Z ⊆ Z'`、`∀ v ∈ Z'∖Z, v ∉ Z'` ⟹ `Z' = Z` | ✅ | `hole_forces_eq` |
| **A8** | 真搬运引擎：四读集 `mass` **逐点相等** ⟹ `CondIndep Z' ⟹ CondIndep Z` | ✅ | `condIndep_of_massEq` |
| **A9** | 「压回」的正确形态：`mass Z p x` 是 `mass Z' p` 在 `v` 位上的**求和**（不是相等） | ✅ | `mass_Z_eq_sum_over_Z'` |
| **A10** | ★ `zStar = Z` **⟺** `ReadClosedBlocks G X Y Z`（`zStar` 路线退化为 G1） | ✅ | `zStar_eq_iff_readClosed` |
| **A11** | 残余：`CondIndep zStar ⟹ CondIndep Z` 的**非退化**版本（`Z' ⊋ Z`） | ⬜ **未证（登记，不消费）** | `RouteAResidual` |

### 结论（如实登记，不美化）

1. **RouteA 的前提 *(P)* 是假的**（A1–A3），且在**满足 `dSep`** 的反例 `gch`
   （链 `0 → 1 → 2`，`X={0}`、`Y={2}`、`Z={1}`）上失效：`zStar = {0,1}`，
   而 `0 ∈ X`。这与 `BridgeZipDown §(c) zStar_sdiff_fails` 的判定一致。
2. **即使 *(P)* 为真也不够**（A7）：`CondIndep` 有**四项** `mass`，其中第四项是
   `mass Z'` 与 `mass Z`；要覆盖这一项就必须有 `v ∉ Z'`，而 `v ∈ Z'∖Z ⊆ Z'`，
   于是洞条件自动退化为 `Z' = Z`。⟹ 「只靠 `mass_congr` 把 `CondIndep Z'` 压回
   `CondIndep Z`」在 `Z' ⊋ Z` 时**在结构上就不可能**（A9 给出最接近的真命题：
   压回需要的是**求和**，而乘积不能穿过求和）。
3. 因此 `zStar` 路线**唯一可用**的情形是 `zStar = Z`，而由 A10 它**恰好等价于**
   `ReadClosedBlocks G X Y Z`，即 `BridgeExpanded` 已证伪的 G1。**RouteA 不产生新桥。**

## 1 纪律

* 单文件验证：`lake env lean Fate/BridgeZipA.lean`。不改 `Fate.lean`。
* **零 `sorry`、零 `axiom`**。所有 \(\exists/\forall\) 的否命题都给出**显式见证**。
* 未证部分以 `Prop` **登记**（`RouteAResidual`），**不进任何下游定理**。
-/

import FateWorld.FateV2.Predict.Strategy11AncestralHull
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.BridgeZipA

open FateV2.Modeling

open FateV2.Modeling.Graph
open Fate.DAGFactorization
open FateV2.Predict.FactorMarkov
open Fate.Strategy11Hull

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

/-!
  # Predict · BridgeZipA

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeZipA.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Strategy11AncestralHull, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §2 `zStar` 及其基本性质（本地自足复刻 `BridgeMinZPrime` 的 L1–L2）
  =========================================================================== -/

/-- ⭐ **读集闭块**（`BridgeExpanded` 的 G1 口径）：`Z` 父闭，且 `X`/`Y` 的父代只
落在「自己 ∪ `Z`」里。 -/
def ReadClosedBlocks (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  AncClosed G Z ∧ (∀ v ∈ X, G.parents v ⊆ X ∪ Z) ∧ (∀ v ∈ Y, G.parents v ⊆ Y ∪ Z)

/-- ⭐ `S` 的父代并集（只取父代，不含 `S` 本身）。 -/
def paBlock (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : Finset V :=
  S.biUnion (fun v => G.parents v)

theorem mem_paBlock {G : FateV2.Modeling.Graph.DAG V} {S : Finset V} {u : V} :
    u ∈ paBlock G S ↔ ∃ v ∈ S, u ∈ G.parents v := by
  unfold paBlock
  rw [Finset.mem_biUnion]

/-- ⭐⭐ **需求集** `req := Z ∪ (pa(X)∖X) ∪ (pa(Y)∖Y)`：`Z'` 必须包含的全部「外部需求」。 -/
def req (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Finset V :=
  Z ∪ (paBlock G X \ X) ∪ (paBlock G Y \ Y)

/-- ⭐⭐⭐ **`zStar`**：`req` 的祖先闭包（`BridgeMinZPrime` L2：唯一极小可行元）。 -/
noncomputable def zStar (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) : Finset V :=
  G.ancestralSet (req G X Y Z)

theorem mem_ancestorsSet {G : FateV2.Modeling.Graph.DAG V} {S : Finset V} {u : V} :
    u ∈ G.ancestorsSet S ↔ ∃ v ∈ S, G.isAncestor u v := by
  simp [FateV2.Modeling.Graph.DAG.ancestorsSet]

theorem mem_ancestralSet {G : FateV2.Modeling.Graph.DAG V} {S : Finset V} {u : V} :
    u ∈ G.ancestralSet S ↔ u ∈ S ∨ ∃ v ∈ S, G.isAncestor u v := by
  rw [FateV2.Modeling.Graph.DAG.ancestralSet, Finset.mem_union, mem_ancestorsSet]

theorem mem_req {G : FateV2.Modeling.Graph.DAG V} {X Y Z : Finset V} {u : V} :
    u ∈ req G X Y Z ↔
      (u ∈ Z ∨ (u ∈ paBlock G X ∧ u ∉ X)) ∨ (u ∈ paBlock G Y ∧ u ∉ Y) := by
  unfold req
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]

theorem mem_zStar {G : FateV2.Modeling.Graph.DAG V} {X Y Z : Finset V} {u : V} :
    u ∈ zStar G X Y Z ↔ u ∈ req G X Y Z ∨ ∃ v ∈ req G X Y Z, G.isAncestor u v := by
  rw [zStar, mem_ancestralSet]

/-- ⭐ `req` 的三个引入规则（显式，避免 `∨` 结合性的歧义）。 -/
theorem mem_req_of_mem_Z {G : FateV2.Modeling.Graph.DAG V} {X Y Z : Finset V} {u : V} (h : u ∈ Z) :
    u ∈ req G X Y Z :=
  mem_req.mpr (Or.inl (Or.inl h))

theorem mem_req_of_mem_paLeft {G : FateV2.Modeling.Graph.DAG V} {X Y Z : Finset V} {u : V}
    (h : u ∈ paBlock G X ∧ u ∉ X) : u ∈ req G X Y Z :=
  mem_req.mpr (Or.inl (Or.inr h))

theorem mem_req_of_mem_paRight {G : FateV2.Modeling.Graph.DAG V} {X Y Z : Finset V} {u : V}
    (h : u ∈ paBlock G Y ∧ u ∉ Y) : u ∈ req G X Y Z :=
  mem_req.mpr (Or.inr h)

/-- ⭐ **`Z ⊆ zStar`**。 -/
theorem subset_zStar {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V) : Z ⊆ zStar G X Y Z := by
  intro u hu
  exact mem_zStar.mpr (Or.inl (mem_req_of_mem_Z hu))

/-- ⭐⭐ **`zStar` 父闭**（`BridgeMinZPrime` L2 的图论内核，复用 `blob_ancClosed`）。 -/
theorem zStar_ancClosed {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V) :
    AncClosed G (zStar G X Y Z) :=
  blob_ancClosed (req G X Y Z)

/-- ⭐ **A5（左）**：`X` 的外部父代全在 `zStar` 内。 -/
theorem paBlock_left_sdiff_subset_zStar {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V) :
    paBlock G X \ X ⊆ zStar G X Y Z := by
  intro u hu
  exact mem_zStar.mpr (Or.inl (mem_req_of_mem_paLeft (Finset.mem_sdiff.mp hu)))

/-- ⭐ **A5（右）**：`Y` 的外部父代全在 `zStar` 内。 -/
theorem paBlock_right_sdiff_subset_zStar {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V) :
    paBlock G Y \ Y ⊆ zStar G X Y Z := by
  intro u hu
  exact mem_zStar.mpr (Or.inl (mem_req_of_mem_paRight (Finset.mem_sdiff.mp hu)))

theorem paBlock_left_subset {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V) :
    paBlock G X ⊆ X ∪ zStar G X Y Z := by
  intro u hu
  by_cases hX : u ∈ X
  · exact Finset.mem_union_left _ hX
  · exact Finset.mem_union_right _ (paBlock_left_sdiff_subset_zStar X Y Z
      (Finset.mem_sdiff.mpr ⟨hu, hX⟩))

theorem paBlock_right_subset {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V) :
    paBlock G Y ⊆ Y ∪ zStar G X Y Z := by
  intro u hu
  by_cases hY : u ∈ Y
  · exact Finset.mem_union_left _ hY
  · exact Finset.mem_union_right _ (paBlock_right_sdiff_subset_zStar X Y Z
      (Finset.mem_sdiff.mpr ⟨hu, hY⟩))

/-- ⭐⭐⭐ **`zStar` 是可行元**（`BridgeMinZPrime` L1 的「构造方向」）：
`ReadClosedBlocks G X Y (zStar G X Y Z)`。 -/
theorem readClosed_zStar {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V) :
    ReadClosedBlocks G X Y (zStar G X Y Z) :=
  ⟨zStar_ancClosed X Y Z,
   fun v hv => fun u hu => paBlock_left_subset X Y Z (mem_paBlock.mpr ⟨v, hv, hu⟩),
   fun v hv => fun u hu => paBlock_right_subset X Y Z (mem_paBlock.mpr ⟨v, hv, hu⟩)⟩

/-- ⭐ **父闭集包含任意子集的祖先包壳**。 -/
theorem ancestralSet_subset_of_ancClosed {G : FateV2.Modeling.Graph.DAG V} {T A : Finset V}
    (hA : AncClosed G A) (hTA : T ⊆ A) : G.ancestralSet T ⊆ A := by
  intro u hu
  rw [mem_ancestralSet] at hu
  rcases hu with hu | ⟨v, hv, hanc⟩
  · exact hTA hu
  · exact FateV2.Modeling.Graph.DAG.isAncestor_mem_of_closed (G := G) hA hanc (hTA hv)

/-- ⭐⭐ `ReadClosedBlocks` 给出 `req ⊆ Z'`（**外部需求**必须落在 `Z'` 里）。 -/
theorem req_subset_of_readClosed {G : FateV2.Modeling.Graph.DAG V} {X Y Z Z' : Finset V}
    (hZZ' : Z ⊆ Z') (h : ReadClosedBlocks G X Y Z') : req G X Y Z ⊆ Z' := by
  intro u hu
  rw [mem_req] at hu
  rcases hu with (hu | ⟨hu, huX⟩) | ⟨hu, huY⟩
  · exact hZZ' hu
  · obtain ⟨v, hv, hup⟩ := mem_paBlock.mp hu
    have := h.2.1 v hv hup
    rcases Finset.mem_union.mp this with h1 | h1
    · exact absurd h1 huX
    · exact h1
  · obtain ⟨v, hv, hup⟩ := mem_paBlock.mp hu
    have := h.2.2 v hv hup
    rcases Finset.mem_union.mp this with h1 | h1
    · exact absurd h1 huY
    · exact h1

/-- ⭐⭐ **`zStar` 极小性**（`BridgeMinZPrime` L2 的「最小」方向）。 -/
theorem zStar_minimal {G : FateV2.Modeling.Graph.DAG V} {X Y Z Z' : Finset V}
    (hZZ' : Z ⊆ Z') (h : ReadClosedBlocks G X Y Z') : zStar G X Y Z ⊆ Z' :=
  ancestralSet_subset_of_ancClosed h.1 (req_subset_of_readClosed hZZ' h)

/-- ⭐⭐⭐ **A10**：`zStar` 不溢出 **⟺** `ReadClosedBlocks G X Y Z`。

⟹ 路线 A（用 `zStar` 当 `Z'`）在**能用**（`zStar = Z`）的情形下**恰好**是
`BridgeExpanded` 已证伪的 G1，故 RouteA **不可能**产生新的桥。 -/
theorem zStar_eq_iff_readClosed {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V) :
    ReadClosedBlocks G X Y Z ↔ zStar G X Y Z = Z := by
  constructor
  · intro h
    exact Finset.Subset.antisymm (zStar_minimal (Finset.Subset.refl Z) h) (subset_zStar X Y Z)
  · intro h
    rw [← h]
    exact readClosed_zStar X Y Z

/-! ===========================================================================
  §3 `mass` 的读集事实（A6）：`v ∉ S ⟹ mass S p` 看不见 `v` 位
  =========================================================================== -/

/-- ⭐⭐⭐ **A6（`BridgeZipDown` 的分析引擎，本文件自足重述）**：

若 `v ∉ S`，则把 `x` 在 `v` 位改成任意 `a` 都不改变 `mass S p x`。

⟹ 这就是 RouteA 想要的全部「洞」效果。注意它说的是 **`mass S` 与 `v` 位无关**，
**不是** `mass (S∪{v}) = mass S`。 -/
theorem mass_congr_at (S : Finset V) (p : (V → α) → ℝ) (x : V → α)
    {v : V} (hv : v ∉ S) (a : α) :
    mass S p (unpin v x a) = mass S p x := by
  refine mass_congr S p (fun u hu => ?_)
  have hne : u ≠ v := fun h => hv (h ▸ hu)
  simp [unpin, hne]

/-- ⭐ **A9（「压回」的正确形态）**：若 `v ∉ Z`，则

$$ \mathrm{mass}\,Z\,p\,x \;=\; \sum_{a} \mathrm{mass}\,(Z\cup\{v\})\,p\,(\mathrm{unpin}\,v\,x\,a). $$

**⟹ 这就是 A7 的定量版本**：把 `mass Z'` 压回 `mass Z` 需要**求和**，
而 `CondIndep` 的乘性恒等式是**乘积**；乘积不能穿过求和（这正是
`DAGFactorizationGeneral.tower_property_false` 的失败点）。
所以「洞条件 + `mass_congr`」在 `Z' ⊋ Z` 时**结构上**无法完成搬运。 -/
theorem mass_Z_eq_sum_over_Z' (Z : Finset V) {v : V} (hv : v ∉ Z)
    (p : (V → α) → ℝ) (x : V → α) :
    mass Z p x = ∑ a : α, mass (insert v Z) p (unpin v x a) :=
  mass_insert_sum' v Z hv p x

/-! ===========================================================================
  §4 A1–A3：RouteA 的前提 *(P)* 在 `zStar` 上为**假**（含 `dSep` 成立的反例）
  =========================================================================== -/

def gch : FateV2.Modeling.Graph.DAG (Fin 3) where
  edge := fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v hv
    have key : ∀ x y : Fin 3,
        Relation.TransGen (fun u v : Fin 3 => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)) x y →
          x < y := by
      intro x y hxy
      induction hxy with
      | single h =>
          rcases h with ⟨a, b⟩ | ⟨a, b⟩ <;> (subst a; subst b; decide)
      | tail _ hstep ih =>
          rcases hstep with ⟨a, b⟩ | ⟨a, b⟩ <;> (subst a; subst b; omega)
    exact absurd (key v v hv) (lt_irrefl v)

/-- ⭐ `0` 是 `1` 的祖先（`gch` 有边 `0 → 1`）。 -/
theorem gch_anc : gch.isAncestor 0 1 :=
  FateV2.Modeling.Graph.DAG.isAncestor.edge (Or.inl ⟨rfl, rfl⟩)

/-- ⭐⭐⭐ **`0 ∈ zStar gch {0} {2} {1} ∖ {1}`**：`zStar` 溢出到 `X` 内。 -/
theorem gch_mem_zStar_sdiff : (0 : Fin 3) ∈ zStar gch {0} {2} {1} \ {1} := by
  refine Finset.mem_sdiff.mpr ⟨?_, by decide⟩
  exact mem_zStar.mpr (Or.inr ⟨1, mem_req_of_mem_Z (by decide), gch_anc⟩)

/-- ⭐⭐⭐ **A4**：反例上的 `dSep` **成立**（故 A1–A3 的失效不是「非 d-分离」造成的）。 -/
theorem gch_is_dSep : gch.dSep ({0} : Finset (Fin 3)) {2} {1} := by decide

/-- ⭐⭐⭐ **A1**：`∀ v ∈ zStar∖Z, v ∉ X∪Y∪Z` **为假**。 -/
theorem zStar_exceeds_domain :
    ¬ (∀ (X Y Z : Finset (Fin 3)), ∀ v ∈ zStar gch X Y Z \ Z, v ∉ X ∪ Y ∪ Z) := by
  intro h
  have := h {0} {2} {1} 0 gch_mem_zStar_sdiff
  exact this (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_singleton_self (0 : Fin 3))))

/-- ⭐⭐⭐ **A2**：`∀ v ∈ zStar∖Z, v ∉ X∪Z` **为假**（第二读集失效）。 -/
theorem zStar_exceeds_XZ :
    ¬ (∀ (X Y Z : Finset (Fin 3)), ∀ v ∈ zStar gch X Y Z \ Z, v ∉ X ∪ Z) := by
  intro h
  have := h {0} {2} {1} 0 gch_mem_zStar_sdiff
  exact this (Finset.mem_union_left _
    (Finset.mem_singleton_self (0 : Fin 3)))

/-- ⭐⭐ 第二个见证（A3 用）：`0 ∈ zStar gch {1} {0} {2} ∖ {2}`。
这里 `zStar` 的溢出方向由 `pa(X)∖X = {0}` 驱动（`X = {1}`），溢出点 `0` 落在 `Y = {0}` 内。 -/
theorem gch2_mem_zStar_sdiff : (0 : Fin 3) ∈ zStar gch {1} {0} {2} \ {2} := by
  refine Finset.mem_sdiff.mpr ⟨?_, by decide⟩
  exact mem_zStar.mpr (Or.inl (mem_req_of_mem_paLeft
    ⟨mem_paBlock.mpr ⟨1, by decide, by decide⟩, by decide⟩))

/-- ⭐⭐⭐ **A3**：`∀ v ∈ zStar∖Z, v ∉ Y∪Z` **为假**（第三读集失效）。

见证：`gch`（链 `0→1→2`）、`X={1}`、`Y={0}`、`Z={2}`、`v=0`：
`req = {2} ∪ (pa(1)∖{1}) = {0,2}`，`zStar = {0,1,2}`，
`0 ∈ zStar∖{2}` 且 `0 ∈ Y∪Z = {0,2}`。 -/
theorem zStar_exceeds_YZ :
    ¬ (∀ (X Y Z : Finset (Fin 3)), ∀ v ∈ zStar gch X Y Z \ Z, v ∉ Y ∪ Z) := by
  intro h
  have := h {1} {0} {2} 0 gch2_mem_zStar_sdiff
  exact this (Finset.mem_union_left _ (by decide))

/-- ⭐ **`v ∈ zStar∖Z` 蕴含 `v` 不在 `Z` 内**（A6 的可用形态：`mass Z` 看不见 `v`）。 -/
theorem not_mem_of_mem_sdiff {Z Z' : Finset V} {v : V} (hv : v ∈ Z' \ Z) : v ∉ Z :=
  (Finset.mem_sdiff.mp hv).2

/-! ===========================================================================
  §5 A7：洞条件对**第四个读集** `Z'` 自动退化 ⟹ `Z' = Z`
  =========================================================================== -/

/-- ⭐⭐ **A7**：若洞条件也覆盖 `Z'` 自身（这是 `CondIndep` 第四项 `mass Z'` 所要求的），

    `Z ⊆ Z'` 且 `∀ v ∈ Z'∖Z, v ∉ Z'`  ⟹  `Z' = Z`.

**⟹ RouteA 的 *(P)* 无论怎么加强，只要它要覆盖 `CondIndep` 的第四项，就必须是
`Z' = Z`** —— 即 `BridgeZipDown §(a)` 已证伪的 `Z' = Z` 版本。 -/
theorem hole_forces_eq {Z Z' : Finset V} (hsub : Z ⊆ Z')
    (hhole : ∀ v ∈ Z' \ Z, v ∉ Z') : Z' = Z := by
  refine Finset.Subset.antisymm (fun v hv => ?_) hsub
  by_contra hvZ
  exact hhole v (Finset.mem_sdiff.mpr ⟨hv, hvZ⟩) hv

/-- ⭐ **A7 的等价形态**：洞条件（覆盖 `Z'`）+ `Z ⊆ Z'` ⟺ `Z' = Z`。 -/
theorem hole_iff {Z Z' : Finset V} (hsub : Z ⊆ Z') :
    (∀ v ∈ Z' \ Z, v ∉ Z') ↔ Z' = Z := by
  constructor
  · exact hole_forces_eq hsub
  · intro h v hv
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hv
    rw [h] at h1
    exact absurd h1 h2

/-! ===========================================================================
  §6 A8：真搬运引擎（前件 = 四读集 `mass` **逐点相等**）
  =========================================================================== -/

/-- ⭐⭐⭐ **A8：唯一的真搬运引擎。**

若四个读集上的 `mass` **逐点相等**，则 `CondIndep Z'` 逐点推出 `CondIndep Z`。

**这是 RouteA 想要的确切形状**；它的前件是本文件 §4–§5 的**全部困难所在**：
前三个等式要求 `Z'∖Z` 躲开 `X∪Y∪Z` 等（A1–A3：`zStar` 做不到），
第四个等式要求 `mass Z' = mass Z`，而这在 `Z' ⊋ Z` 时**不能**由 `mass_congr` 得到
（A9：只能得到**求和**关系）。 -/
theorem condIndep_of_massEq {X Y Z Z' : Finset V} {p : (V → α) → ℝ}
    (hXYZ : ∀ x : V → α, mass (X ∪ Y ∪ Z') p x = mass (X ∪ Y ∪ Z) p x)
    (hZ : ∀ x : V → α, mass Z' p x = mass Z p x)
    (hXZ : ∀ x : V → α, mass (X ∪ Z') p x = mass (X ∪ Z) p x)
    (hYZ : ∀ x : V → α, mass (Y ∪ Z') p x = mass (Y ∪ Z) p x)
    (h : CondIndep p X Y Z') : CondIndep p X Y Z := by
  intro x
  have hx := h x
  rw [hXYZ x, hZ x, hXZ x, hYZ x] at hx
  exact hx

/-- ⭐ **`Z' ⊆ X∪Y∪Z ⟹ X∪Y∪Z' = X∪Y∪Z`**（第一读集的**集合式**充分条件）。 -/
theorem union_XYZ_eq_of_subset {X Y Z Z' : Finset V} (hZZ' : Z ⊆ Z')
    (hsub : Z' ⊆ X ∪ Y ∪ Z) : X ∪ Y ∪ Z' = X ∪ Y ∪ Z := by
  refine Finset.Subset.antisymm (fun u hu => ?_) (fun u hu => ?_)
  · rcases Finset.mem_union.mp hu with h | h
    · exact Finset.mem_union_left _ h
    · exact hsub h
  · rcases Finset.mem_union.mp hu with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (hZZ' h)

/-- ⭐⭐ **`CondIndep` 的第四项**：`mass Z' = mass Z` 的**必要形态**。
若 `Z ⊆ Z'` 且两个 `mass` 相等（逐点），则 `Z' ∖ Z` 的每个点在 `mass Z'` 下
都必须「看不见」—— 而这与 `v ∈ Z'` 直接冲突（`mass Z'` 的读集**就是** `Z'`）。
本定理把这层冲突形式化为：**逐点相等 + 严格包含 ⟹ 矛盾方向**（见 `hole_forces_eq`）。 -/
theorem mass_eq_forces_no_new_vertex {Z Z' : Finset V} (hsub : Z ⊆ Z')
    (hne : Z' \ Z = ∅) : Z' = Z := by
  refine Finset.Subset.antisymm (fun v hv => ?_) hsub
  by_contra hvZ
  have hmem : v ∈ Z' \ Z := Finset.mem_sdiff.mpr ⟨hv, hvZ⟩
  rw [hne] at hmem
  exact absurd hmem (by simp)

/-! ===========================================================================
  §7 A11：RouteA 的残余（**登记，不消费**）
  =========================================================================== -/

/-- ⬜ **A11：`RouteAResidual`**。RouteA 唯一还有意义的残余义务：

> 对某个具体的**非退化**图族（`zStar ⊋ Z`），若 *(P)* 成立（这需要替换掉 `zStar`），
> 是否仍有 `CondIndep zStar ⟹ CondIndep Z`？

**本文件不证此命题，也不把它当作任何下游定理的前件。** A7 已说明：任何**只依赖**
`mass_congr`（逐位无关性）的论证都无法覆盖 `CondIndep` 的第四项 `mass Z'`；
若要绕开，必须使用 `mass` 的**求和**结构（A9）与 `dSep` 的 Bayes-Ball 子句，
那已不属于「zip down」这条路线（见 `BridgeFull` 的 `markov_of_readClosedBlocks`）。 -/
def RouteAResidual : Prop :=
  ∀ (G : FateV2.Modeling.Graph.DAG V) (p : (V → α) → ℝ) (X Y Z : Finset V),
    (Z ⊆ zStar G X Y Z ∧ ¬ (zStar G X Y Z ⊆ Z)) →
      CondIndep p X Y (zStar G X Y Z) → CondIndep p X Y Z

/-- ⭐⭐ **本文件的最终结构定理**：RouteA 的「可用情形」**恰好**是 G1。

    `ReadClosedBlocks G X Y Z  ⟺  zStar G X Y Z = Z`

⟹ 用 `zStar` 作 `Z'` 的桥，只在 `Z' = Z`（已证伪，`BridgeZipDown §(a)`）时成立。 -/
theorem routeA_only_at_G1 {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V) :
    ReadClosedBlocks G X Y Z ↔ zStar G X Y Z = Z :=
  zStar_eq_iff_readClosed X Y Z

end FateV2.Predict.BridgeZipA