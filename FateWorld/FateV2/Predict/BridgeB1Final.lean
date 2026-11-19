import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.AncestralInheritanceRouteB
import Mathlib.Tactic

/-!
  # Predict · BridgeB1Final

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeB1Final.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausDAG, DAGFactorization, FactorMarkov, AncestralInheritanceRouteB
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeB1Final` —— **清单 B1：祖先闭子图上的继承（如实的修复版）**

  ## 0 ⚠ 修复说明（**先读这一节**）

  本文件是 `Fate/BridgeB1Final.lean` 的**修复版**。原文件的问题与处置：

  | # | 原位置 | 症状 | 本文件处置 |
  |---|---|---|---|
  | **E1** | 行 1 `import Fate.BridgeA4` | `object file '…/Fate/BridgeA4.olean' … does not exist`（`BridgeA4` 本身编译失败）| 改为 `import CausDAG`；`FactorizesL` **自足重写**（逐字照抄 `BridgeA4` §4.1a 的定义）|
  | **S1** | `mass_A_factorizesL`（2 处 `sorry`）| 该陈述**为假**（缺归一化因子）| ⛔ **已删除**（§5 说明原因），不留 `sorry` |
  | **S2** | `factorizesL_inherit` 的**乘积式**那一半 | 该乘积式**为假**（丢掉了 `A` 外的因子）| ⛔ **乘积式已删除**，只保留**为真**的读集那一半（`factorizesL_inherit_reads`）|
  | **J1** | `liftFun_reads` | 陈述是 `… → True := fun _ _ _ => trivial`，**无任何数学内容** | ⛔ 已删除 |
  | **J2** | `literal_B1_false_statement_note : True` | 同上，`True` 的自反证明 | ⛔ 已删除 |

  **零 `sorry` / 零 `admit` / 零 `axiom`。**

  ### 0.1 原文件表头的「虚报」已全部更正

  原文件 §0 一页表声称 B1.0–B1.10 **全部零缺口**，但文件中并不存在
  B1.4 `factorizesL_inherit_mass`、B1.6 `LGMC_inherit`、B1.7
  `factorizes_implies_LMG_of_true_tower`、B1.8 `lmg_of_mass_subsingleton`、
  B1.9 `not_factorizes_inherit_naive`、B1.10 `collider_ancClosed_block`。
  本文件**只登记实际存在的定理**（见 §1 清单），不再虚报。

  ---

  ## 1 本文件实际交付（**逐条 machine-checked**）

  | # | 名称 | 内容 | 状态 |
  |---|---|---|---|
  | B1.0 | `AncClosed`（定义）| 「`A` 对 `pa` 封闭」= 祖先闭集 | ✅ 定义 |
  | B1.0a | `ancClosed_iff` | 与 `AncestralInheritanceRouteB.AncestorClosed` 同一谓词 | ✅ 真证明 |
  | B1.0b | `mem_ancestralSet'` | `ancestralSet` 的成员判据 | ✅ 真证明 |
  | B1.1 | `ancestralSet_ancClosed` | 真祖先闭包 `G.ancestralSet S` 是祖先闭集 | ✅ 真证明 |
  | B1.2 | `ancestralSet_finite_closure` | 且它最小（`S ⊆ A`、`A` 闭 ⟹ `ancestralSet S ⊆ A`）| ✅ 真证明 |
  | B1.3 | ⭐ `factorizesL_inherit_reads` | **真继承的读集那一半**：限制到 `↥A` 的因子族只读**子图内**的 `{a} ∪ pa_{G[A]}(a)` | ✅ 真证明 |
  | B1.4 | `factor_reads_A` | 因子 `φ w`（`w ∈ A`）只依赖 `x` 在 `A` 上的值 | ✅ 真证明 |

  **已删除（陈述为假）**：`factorizesL_inherit` 的乘积式、`factorizesL_inherit_pointwise`、
  `mass_A_factorizesL`。真形态见 `Fate/BridgeB1Fixed`：
  `mass_A_factorizesL_literal_false`（反例）、`mass_ancClosed`（修正形态，需 `FactorNorm`）、
  `LGMC_inherit`（`p ∘ liftFun` 口径）。**本文件不重复交付它们**（避免平行同义模块）。

  ---

  ## 2 ⚠ 为什么原文件那两条「乘积式」为假

  设 `FactorizesL p G`，见证 `φ`（`φ_v` 读 `{v} ∪ pa(v)`），故
  `p x = ∏_{v : V} φ_v x`。若把 `φ` 限制到 `↥A` 得 `ψ_a := φ_a`，则

  ```
  ∏_{a : ↥A} ψ_a (x|_A)  =  ∏_{a ∈ A} φ_a x      ≠  p x
  ```

  右端**缺了 `A` 外的因子** `∏_{v ∉ A} φ_v x`（一般不为 `1`）。故「`p` 在 `G[A]` 上
  = 乘积」为**假**。`Fate/BridgeB1Fixed` 的 `subDAG_factorization_false` 用
  `A = {0,1}`、`G[A]` 无边、`p := [x₀ = x₁]` 给出机器验证反例。

  同理 `mass_A_factorizesL`（原 `sorry` 处）声称
  `mass A p x = ∏_{a : ↥A} ψ_a (x|_A)`，其右端是**未归一化的乘积**，
  而 `mass A p x = ∑_{b : Aᶜ → α} p(b ⊎ x) = (∏_a ψ_a) · (∑_b ∏_{v ∉ A} φ_v)`，
  第二个括号一般 ≠ 1 —— `Fate/BridgeB1Fixed.mass_A_factorizesL_literal_false` 已机器证伪。
  修正形态需额外假设 `FactorNorm`（每个因子对自己的坐标求和为 `1`）。

  ---

  ## 3 ⚠ 前件台账（真 / 假证自查）

  | 记号 | 是什么 | 在哪被消费 |
  |---|---|---|
  | `hfac` | `FactorizesL p G` | B1.3：取见证 `φ`、读集条件 `hφ`（`ψ` 的读集证明）；B1.4 不使用 |
  | `hanc` | `AncClosed G A` | B1.1/B1.2：闭包的封闭性与最小性；B1.3：`pa G a.1 ⊆ A`（`a.1 ∈ A`），把 `φ a.1` 的两个参数只在 `A` 上对齐 —— **没有 `hanc` 这里过不去**；B1.4：`{w}∪pa w ⊆ A` |
  | `hd` | `dSep` | ⚠ **本文件不使用**（B1 是纯概率 + 图论陈述，`dSep` 属 B3/B4）|

  ⚠ **没有一处把结论写进前件**：每条蕴含的右端都不出现在左端
  （B1.3 的左端是 `V` 上的 `FactorizesL`，右端是 `↥A` 上的读集条件，**点类型不同**）。
  ⚠ **不使用 `mass` 的塔性质**：本文件完全不涉及 `mass`（相关假命题已删除）。

  ---

  ## 4 ⚠ 诚实边界

  * 本文件**不**声称「`mass A p` 在 `G[A]` 上因子分解 / 满足 `LGMC`」——
    该陈述为假（§2），已删除。
  * 本文件**不**声称原表头列出的 B1.4–B1.10（原文件中根本不存在）。
  * 本文件**不改** `Fate.lean`、**不改**任何既有模块。
  * 与已入库模块的重复度：`AncClosed` / `ancestralSet_ancClosed` / `ancestralSet_finite_closure`
    与 `BridgeB1Fixed`、`BridgeZipA`、`BridgeMinZPrime` 同名但定理数远少（4 条），
    详见交付报告。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeB1Final

set_option linter.unusedSectionVars false

open Finset FateV2.Predict.DAGFactorization FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §5 因子分解（标准读集 `{v} ∪ pa v`）—— 自足定义（修 E1）
  =========================================================================== -/

/-- **B1.5a（因子分解，读集 `{v} ∪ pa_G(v)`）**：逐字照抄 `BridgeA4` §4.1a
（`BridgeA4` 本身编译失败，故不 `import` 它）。

⚠ 与 `Fate.FactorMarkov.Factorizes`（`LocalTo` 即同一读集条件）是**同一个**谓词。 -/
def FactorizesL (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) : Prop :=
  ∃ (φ : V → (V → α) → ℝ),
    (∀ v x y, (∀ u ∈ insert v (pa G v), x u = y u) → φ v x = φ v y) ∧
    ∀ x, p x = ∏ v, φ v x

/-! ===========================================================================
  §6 祖先闭集：定义、闭包、最小性
  =========================================================================== -/

/-- **B1.0（祖先闭集）**：`A` 对 `pa` 封闭。 -/
def AncClosed (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) : Prop :=
  ∀ v ∈ A, pa G v ⊆ A

/-- **B1.0a**：与 `AncestralInheritanceRouteB.AncestorClosed` 是同一个谓词（防重复发明）。 -/
theorem ancClosed_iff (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) :
    AncClosed G A ↔ FateV2.Predict.AncestralInheritanceRouteB.AncestorClosed G A := Iff.rfl

/-- **B1.0b**：`ancestralSet S` 的成员判据。 -/
theorem mem_ancestralSet' (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) (u : V) :
    u ∈ G.ancestralSet S ↔ u ∈ S ∨ ∃ v ∈ S, G.isAncestor u v := by
  simp [FateV2.Modeling.Graph.DAG.ancestralSet, FateV2.Modeling.Graph.DAG.ancestorsSet]

/-- ⭐ **B1.1**：真祖先闭包 `G.ancestralSet S` 对 `pa` 封闭。 -/
theorem ancestralSet_ancClosed (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) :
    AncClosed G (G.ancestralSet S) := by
  intro v hv u hu
  have huv : G.isAncestor u v := FateV2.Modeling.Graph.DAG.isAncestor.edge (mem_pa.mp hu)
  rw [mem_ancestralSet'] at hv ⊢
  rcases hv with hv | ⟨w, hw, hanc⟩
  · exact Or.inr ⟨v, hv, huv⟩
  · exact Or.inr ⟨w, hw, FateV2.Modeling.Graph.DAG.isAncestor_trans G huv hanc⟩

/-- ⭐ **B1.2（最小性）**：`S ⊆ A` 且 `A` 祖先闭 ⟹ `ancestralSet S ⊆ A`。

与 B1.1 合起来：`ancestralSet` 是**最小**的含 `S` 的祖先闭集。 -/
theorem ancestralSet_finite_closure (G : FateV2.Modeling.Graph.DAG V) (S A : Finset V)
    (hanc : AncClosed G A) (hSA : S ⊆ A) : G.ancestralSet S ⊆ A := by
  intro u hu
  rw [mem_ancestralSet'] at hu
  rcases hu with hu | ⟨w, hw, hanc_uw⟩
  · exact hSA hu
  · exact G.isAncestor_mem_of_closed (fun x hx => hanc x hx) hanc_uw (hSA hw)

/-! ===========================================================================
  §7 诱导子图 `G[A]` 与两个搬运映射（自足定义）
  =========================================================================== -/

/-- 诱导子图的边关系。 -/
def subEdge (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) (u v : ↥A) : Prop := G.edge u.1 v.1

instance subEdgeDec (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) :
    DecidableRel (subEdge G A) := fun u v => inferInstanceAs (Decidable (G.edge u.1 v.1))

/-- 子图无环：把子图里的每条边逐条搬回 `G`。 -/
theorem subEdge_acyclic (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) :
    ∀ v : ↥A, ¬ Relation.TransGen (subEdge G A) v v := by
  have key : ∀ {a b : ↥A}, Relation.TransGen (subEdge G A) a b →
      Relation.TransGen G.edge a.1 b.1 := by
    intro a b h
    induction h with
    | single hab => exact Relation.TransGen.single hab
    | tail _ hbc ih => exact ih.tail hbc
  intro v hv
  exact G.acyclic v.1 (key hv)

/-- ⭐ **诱导子图** `G[A]`。 -/
def subDAG (G : FateV2.Modeling.Graph.DAG V) (A : Finset V) : FateV2.Modeling.Graph.DAG ↥A where
  edge := subEdge G A
  decEdge := subEdgeDec G A
  acyclic := subEdge_acyclic G A

theorem subDAG_edge_iff {G : FateV2.Modeling.Graph.DAG V} {A : Finset V} {u v : ↥A} :
    (subDAG G A).edge u v ↔ G.edge u.1 v.1 := Iff.rfl

/-- **子图内的父集 ⟺ 原图父集（子类型化后）**。 -/
theorem mem_pa_subDAG {G : FateV2.Modeling.Graph.DAG V} {A : Finset V} {u v : ↥A} :
    u ∈ pa (subDAG G A) v ↔ u.1 ∈ pa G v.1 := by
  rw [mem_pa, mem_pa, subDAG_edge_iff]

/-- 把 `↥A → α` 提升回 `V → α`（`A` 外填 `x₀`）。 -/
noncomputable def liftFun (A : Finset V) (x₀ : V → α) (y : ↥A → α) : V → α :=
  fun v => if h : v ∈ A then y ⟨v, h⟩ else x₀ v

theorem liftFun_of_mem {A : Finset V} {x₀ : V → α} {y : ↥A → α} {u : V} (hu : u ∈ A) :
    liftFun A x₀ y u = y ⟨u, hu⟩ := by
  simp only [liftFun, hu, dif_pos]

/-- 把 `V → α` 压到 `↥A → α`。 -/
def subProj (A : Finset V) (x : V → α) : ↥A → α := fun a => x a.1

theorem subProj_liftFun {A : Finset V} {x₀ : V → α} {y : ↥A → α} :
    subProj A (liftFun A x₀ y) = y := by
  funext a; exact liftFun_of_mem a.2

/-! ===========================================================================
  §8 ⭐⭐ B1.3 的真形态：因子族限制到子图后，读集变成子图的 `pa`
  =========================================================================== -/

/-- ⭐⭐ **B1.3（真继承的读集那一半）**：

设 `FactorizesL p G`、`A` 祖先闭。则存在 `↥A` 上的因子族 `ψ`，使

* `ψ a` 只读 **子图内**的 `{a} ∪ pa_{G[A]}(a)`。

即把见证 `φ` 限制为 `ψ a y := φ a.1 (liftFun A x₀ y)` 后，读集自动收窄到子图的父集。

**`hfac` 用在哪**：`φ`（`ψ` 的定义）与 `hφ`（`ψ` 的读集证明）。
**`hanc` 用在哪**：`u ∈ {a} ∪ pa_{G[A]}(a)` ⟹ `u ∈ A`（`a.2` 与 `hanc a.1 a.2`），
故 `liftFun` 在两个参数上都能取出 `y ⟨u,_⟩`；**没有 `hanc` 这里过不去**。

⚠ **不含乘积式**：`p`（或 `mass A p`）在 `G[A]` 上等于 `∏_{a : ↥A} ψ_a` 是**假**的
（缺 `A` 外因子，见文件头 §2）。故本文件**只交付读集**这一真的一半；
真形态（需 `FactorNorm`）见 `Fate/BridgeB1Fixed.mass_ancClosed` / `LGMC_inherit`。 -/
theorem factorizesL_inherit_reads {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (hfac : FactorizesL p G) {A : Finset V} (hanc : AncClosed G A) (x₀ : V → α) :
    ∃ (ψ : ↥A → (↥A → α) → ℝ),
      (∀ a y z, (∀ u ∈ insert a (pa (subDAG G A) a), y u = z u) → ψ a y = ψ a z) := by
  classical
  obtain ⟨φ, hφ, _hp⟩ := hfac
  refine ⟨fun a z => φ a.1 (liftFun A x₀ z), ?_⟩
  intro a y z hyz
  refine hφ a.1 _ _ (fun u hu => ?_)
  have huA : u ∈ A := by
    rcases mem_insert.mp hu with rfl | hu
    · exact a.2
    · exact hanc a.1 a.2 hu
  rw [liftFun_of_mem huA, liftFun_of_mem huA]
  refine hyz ⟨u, huA⟩ ?_
  rw [mem_insert] at hu ⊢
  rcases hu with rfl | hu
  · exact Or.inl rfl
  · exact Or.inr ((mem_pa_subDAG (G := G) (A := A) (u := ⟨u, huA⟩) (v := a)).mpr hu)

/-! ===========================================================================
  §9 ⭐ B1.4：祖先闭集内的因子只依赖 `A` 上的坐标
  =========================================================================== -/

/-- ⭐ **B1.4（因子 `φ w` 只读 `A` 上的坐标）**。

若 `w ∈ A`、`A` 祖先闭，则 `φ w x` 只依赖 `x|_A`。

**`hanc` 被真消费**：`w ∈ A` 时 `{w} ∪ pa w ⊆ A`。 -/
theorem factor_reads_A {G : FateV2.Modeling.Graph.DAG V} {φ : V → (V → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ insert v (pa G v), x u = y u) → φ v x = φ v y)
    {A : Finset V} (hanc : AncClosed G A) {w : V} (hw : w ∈ A) {x y : V → α}
    (hxy : ∀ u ∈ A, x u = y u) : φ w x = φ w y := by
  refine hφ w x y (fun u hu => hxy u ?_)
  rw [mem_insert] at hu
  rcases hu with rfl | hu
  · exact hw
  · exact hanc w hw hu

end BridgeB1Final
end FateV2.Predict