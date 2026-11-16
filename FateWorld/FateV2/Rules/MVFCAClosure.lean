import FateWorld.FateV2.Rules.MVFCAPositive
import Mathlib.Order.Closure

/-!
  # Rules · MVFCAClosure

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MVFCAClosure.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MVFCAPositive
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  MVFCA 闭包的补全：`cl` 幂等 + `ClosureOperator` 实例 + 闭集交封闭

  ## 背景

  `Fate/MVFCAPositive.lean` 已定义模式结构与标准闭包：
  ```lean
  structure PatStruct (G) (L) [CompleteLattice L] where desc : G → L
  def up   (K) (A : Set G) : L     := ⨅ g ∈ A, K.desc g
  def down (K) (B : L) : Set G     := {g | B ≤ K.desc g}
  def cl   (K) (A : Set G) : Set G := K.down (K.up A)
  def IsClosed (K) (A) : Prop      := K.cl A = A
  ```
  并证了 `subset_down_up`（扩张性）、`cl_extensive`、`univ_closed`。

  **但缺关键的一环：`cl` 的幂等性。** 没有它，`IsClosed` 对应的「闭集」概念
  就没有闭包算子的标准结构（不动点 = 闭集族成完全格）。

  ## 本节补什么（作者裁决「完善的完善」）

  1. ⭐ `le_up_down`：`B ≤ up (down B)`（无条件）
  2. ⭐ `up_cl_eq`：`up (down (up A)) = up A`（**核引理**）
  3. ⭐⭐ `cl_idem`：`cl (cl A) = cl A`（**无需任何额外假设**）
  4. ⭐ `cl_mono`：单调性
  5. ⭐⭐ `ClosureOperator` 实例（接入 Mathlib 理论）
  6. ⭐⭐ 闭集族对**任意交封闭**

  ## ⚠ 一个必须记下的**错误更正**

  起初我试图证明 `up (down B) = B`（对所有 `B`）——**那是假的**。

  `down B` 的成员只保证 `B ≤ desc g`（**反方向**），故 `up (down B)` 一般**大于** `B`。

  **正确命题**：只在 `B` 是 `up` 的像时才有 `up (down B) = B`。
  即 **`up ∘ down` 是 `B` 上的投影，不是恒等**。

  而 `up (down (up A)) = up A` 恰好成立（因 `A ⊆ down (up A)`）——**这就够了**。

  ## 诚实边界

  * `down` 与 `up` 构成的是**反变** Galois 连接（`B ≤ δ g ⟺ …`），不是标准的单调 Galois 连接。
    故不能直接套 Mathlib 的 `GaloisConnection` 理论，需手工构造 `ClosureOperator`。
  * 本节**不处理** `G = ∅` 的边界情形（但 `cl_idem` 实际无需它）。
  =========================================================================== -/

namespace FateV2.Rules.MVFCA4
namespace PatStruct

universe u v

variable {G : Type u} {L : Type v} [CompleteLattice L]

/-! ### §0.1 基本引理 -/

/-- ⭐ **一侧的 Galois 不等式**（无条件）：`B ≤ up (down B)`。

**含义**：把 `B` 展开成「满足 `B` 的对象集」再取它们的下确界，得到的是 `B` 的**加强**。 -/
theorem le_up_down (K : PatStruct G L) (B : L) : B ≤ K.up (K.down B) := by
  simp only [PatStruct.up, PatStruct.down, Set.mem_setOf_eq]
  exact le_iInf fun _ => le_iInf fun hg => hg

/-! ### §0.2 ⭐ 核引理 -/

/-- ⭐⭐ **核引理**：`up (down (up A)) = up A`。

**证明**：
* `≤`：`A ⊆ down (up A)`（扩张性），故在其上取 `⨅` 更小（`iInf_le_iInf_of_subset`）。
* `≥`：由 `le_up_down` 取 `B := up A`。

**⟹ 这是 `cl` 幂等性的真正来源。** -/
theorem up_cl_eq (K : PatStruct G L) (A : Set G) : K.up (K.down (K.up A)) = K.up A := by
  apply le_antisymm
  · simp only [PatStruct.up]
    exact iInf_le_iInf_of_subset (K.cl_extensive A)
  · exact le_up_down K (K.up A)

/-! ### §0.3 ⭐⭐ 幂等性 -/

/-- ⭐⭐ **`cl` 幂等**：`cl (cl A) = cl A`（**无需任何额外假设**）。

**⚠ 更正记录**：起初误以为需要 `[Nonempty G]`，实际不需要 ——
因为 `up_cl_eq` 是无条件成立的。 -/
theorem cl_idem (K : PatStruct G L) (A : Set G) : K.cl (K.cl A) = K.cl A := by
  show K.down (K.up (K.down (K.up A))) = K.down (K.up A)
  rw [up_cl_eq K A]

/-! ### §0.4 单调性 -/

/-- ⭐ **`cl` 单调**：`A ⊆ B ⟹ cl A ⊆ cl B`。 -/
theorem cl_mono (K : PatStruct G L) {A B : Set G} (h : A ⊆ B) : K.cl A ⊆ K.cl B := by
  intro g hg
  simp only [PatStruct.cl, PatStruct.down, Set.mem_setOf_eq] at hg ⊢
  have hle : K.up B ≤ K.up A := by
    simp only [PatStruct.up]
    exact iInf_le_iInf_of_subset h
  exact le_trans hle hg

/-! ### §0.5 ⭐⭐ `ClosureOperator` 实例 -/

/-- ⭐⭐ **MVFCA 闭包是 `ClosureOperator`**（Mathlib 标准类型类）。

**⟹ 由此自动获得 Mathlib 的闭包算子理论**：
* 闭集族 = `IsClosed` 集
* 闭集族对任意交封闭（Mathlib 已证）
* 与规则层 `RuleActivation.closureOperator`、FCA 的 `attrClosureOperator` 同框架
-/
def closureOperator (K : PatStruct G L) : ClosureOperator (Set G) where
  toFun := K.cl
  monotone' := fun {_ _} h => K.cl_mono h
  le_closure' := fun A => K.cl_extensive A
  idempotent' := fun A => K.cl_idem A

/-- **`IsClosed` 与 `ClosureOperator.IsClosed` 一致**（`Iff.rfl`）。 -/
theorem isClosed_iff_closureOperator (K : PatStruct G L) (A : Set G) :
    K.IsClosed A ↔ (K.closureOperator).IsClosed A :=
  Iff.rfl

/-! ### §0.6 ⭐⭐ 闭集族对任意交封闭 -/

/-- ⭐⭐ **两个闭集的交仍闭**。

**证明**：设 `A, B` 闭。则 `A ∩ B ⊆ A`，故 `cl (A∩B) ⊆ cl A = A`；同得 `⊆ B`。
而扩张性给 `A∩B ⊆ cl (A∩B)`。故相等。 -/
theorem closed_inter (K : PatStruct G L) {A B : Set G}
    (hA : K.IsClosed A) (hB : K.IsClosed B) : K.IsClosed (A ∩ B) := by
  unfold PatStruct.IsClosed at *
  apply Set.Subset.antisymm
  · intro g hg
    have h1 : K.cl (A ∩ B) ⊆ A := by
      calc K.cl (A ∩ B) ⊆ K.cl A := K.cl_mono Set.inter_subset_left
        _ = A := hA
    have h2 : K.cl (A ∩ B) ⊆ B := by
      calc K.cl (A ∩ B) ⊆ K.cl B := K.cl_mono Set.inter_subset_right
        _ = B := hB
    exact ⟨h1 hg, h2 hg⟩
  · exact K.cl_extensive (A ∩ B)

/-- ⭐ **闭集族对任意交封闭**（由 `ClosureOperator` 理论直接得到）。

**⟹ 这是「局部域族」的良定义性根据**（部分识别时可用交来收紧）。 -/
theorem closed_sInter (K : PatStruct G L) (S : Set (Set G))
    (hS : ∀ A ∈ S, K.IsClosed A) : K.IsClosed (⋂₀ S) := by
  unfold PatStruct.IsClosed at *
  apply Set.Subset.antisymm
  · intro g hg
    -- cl (⋂₀ S) ⊆ ⋂₀ S：对每个 A ∈ S，cl (⋂₀ S) ⊆ cl A = A
    have hsub : K.cl (⋂₀ S) ⊆ ⋂₀ S := by
      rw [Set.subset_sInter_iff]
      intro A hA
      have h1 : K.cl (⋂₀ S) ⊆ K.cl A := by
        apply K.cl_mono
        exact Set.sInter_subset_of_mem hA
      rw [hS A hA] at h1
      exact h1
    exact hsub hg
  · exact K.cl_extensive _

end PatStruct

end FateV2.Rules.MVFCA4