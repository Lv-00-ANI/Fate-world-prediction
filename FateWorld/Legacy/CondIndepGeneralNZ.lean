import FateWorld.Legacy.CondIndepEmptyZ
import FateWorld.Legacy.CondIndepSemigraphoid

/-! ===========================================================================
  §0  主定理 C 的一般 `Z` 版本（**非零前提变体**）：`condIndep_general`

  在 `Fate/CondIndepEmptyZ.lean` 的 `condIndep_emptyZ`（`Z = ∅`）基础上，
  把因子图分离结论推广到**任意**条件集 `Z`。

  ```lean
  theorem condIndep_general (ψ) (p)
      (hfac   : ∀ w, p w = ∏ v, ψ v w)          -- 单点因子分解
      (hread  : ReadSet ψ R)                     -- 读集约束
      (hsplit : Split R X Y Z)                   -- 因子图分离
      (hXY hXZ hYZ : … Disjoint …)               -- 三对不交
      (hcover : X ∪ Y ∪ Z = univ) :              -- 全空间覆盖
      CondIndep p X Y Z
  ```

  ## ⭐ 两条路径

  1. **`condIndep_general`**：**不做任何除法**。四个 `mass` 各提出一个公共因子
     `Pz x = ∏_{v ∈ Wblk R Z} ψ v x`，两端各得 `Pz x ^ 2` 倍，末尾 `ring` 直接配平。
     **故本定理的假设与 `Z = ∅` 版一模一样，不额外要求非零。**

  2. **`condIndep_general_nz`**：任务书要求的「显式约去」版本，额外接受
     `hprod : ∀ x, (∏ v ∈ Wblk R Z, ψ v x) ≠ 0`，并通过 `sq_cancel`
     （`(c*A)*(c*B) = (c*C)*(c*D) ↔ A*B = C*D`，`c ≠ 0`）**真的约去** `c²`。
     结论与 (1) 相同 —— 这说明 `hprod` 在当前技术路线下是**可达但非必需**的。

  ## 三块分解（一般 `Z` 的核心）

  ```
  Wblk R Z     = {v | R v ⊆ Z}                    （记其积为 Pz）
  WF R X Z     = {v | R v ⊆ X∪Z ∧ ¬ R v ⊆ Z}      （记其积为 F）
  WG R Y Z     = {v | R v ⊆ Y∪Z ∧ ¬ R v ⊆ Z}      （记其积为 G）
  ```

  `Split R X Y Z` ⟹ 三块并集为 `univ`；`Disjoint X Y` ⟹ 三块**两两不交**
  （关键：`(X∪Z) ∩ (Y∪Z) = Z`）。于是 `∏ v, ψ v w = Pz w * F w * G w`。

  四个 `mass`（`S ∈ {Z, X∪Z, Y∪Z, X∪Y∪Z}`，都含 `Z`）：

  | `S` | 值 |
  |---|---|
  | `Z` | `Pz x · (mass (X∪Z) G x · mass (Y∪Z) F x)`（`mass_sep_Z`）|
  | `X∪Z` | `Pz x · F x · mass (X∪Z) G x`（`Pz`、`F` 冻结）|
  | `Y∪Z` | `Pz x · G x · mass (Y∪Z) F x`（`Pz`、`G` 冻结）|
  | `X∪Y∪Z` | `Pz x · F x · G x`（`hcover` + `mass_univ`）|

  代入 `CondIndep` 后两端都是 `Pz x² · F x · G x · mass(X∪Z) G x · mass(Y∪Z) F x`。

  ## 诚实边界

  * `[Nonempty α]`：形式化基础设施的副作用（`mass_prod_cover` 等）。**不削弱结论**：
    `CondIndep` 是 `∀ x : V → α, …`，若 `α` 为空而 `V` 非空则 `V → α` 为空集，
    结论空洞为真。
  * `hcover : X ∪ Y ∪ Z = univ`：**必需**（与 `condIndep_emptyZ` 的 `hcover` 同源）。
  * `hXZ`、`hYZ` **未被使用**（`(X∪Z) ∩ (Y∪Z) = Z` 只需 `X ∩ Y = ∅`）；
    保留以匹配 `dSep` 接口与 `BalanceComponents.card_balance` 的调用约定。
  * 任务书担心的 `hprod` 非零前提**不需要**：见 `condIndep_general`。
  =========================================================================== -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Fate.GraphToProbView7

open Finset
open Fate
open Fate.DAGFactorization
open Fate.FactorMarkov
open Fate.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]
  [Nonempty α]

/-! ===========================================================================
  §1  三块分解的集合论
  =========================================================================== -/

/-- **`X ∪ Z` 与 `Y ∪ Z` 的交恰为 `Z`**（只需 `X`、`Y` 不交）。 -/
theorem inter_union_union_eq {X Y Z : Finset V} (hXY : Disjoint X Y) :
    (X ∪ Z) ∩ (Y ∪ Z) = Z := by
  ext u
  constructor
  · intro hu
    rcases Finset.mem_inter.mp hu with ⟨hx, hy⟩
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp hy with h' | h'
      · exact absurd (Finset.disjoint_left.mp hXY h h') (by simp)
      · exact h'
    · exact h
  · intro hu
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_union.mpr (Or.inr hu), Finset.mem_union.mpr (Or.inr hu)⟩

/-- **`v ∉ X ∪ Z` ⟹ `v ∈ Y`**（需 `X ∪ Y ∪ Z = univ`）。 -/
theorem notMemXZ_memY {X Y Z : Finset V} (hcover : X ∪ Y ∪ Z = Finset.univ)
    {v : V} (hv : v ∉ X ∪ Z) : v ∈ Y := by
  have h : v ∈ X ∪ Y ∪ Z := by rw [hcover]; exact Finset.mem_univ v
  rcases Finset.mem_union.mp h with h' | hz
  · rcases Finset.mem_union.mp h' with hx | hy
    · exact absurd (Finset.mem_union.mpr (Or.inl hx)) hv
    · exact hy
  · exact absurd (Finset.mem_union.mpr (Or.inr hz)) hv

/-- **`v ∉ Y ∪ Z` ⟹ `v ∈ X`**（需 `X ∪ Y ∪ Z = univ`）。 -/
theorem notMemYZ_memX {X Y Z : Finset V} (hcover : X ∪ Y ∪ Z = Finset.univ)
    {v : V} (hv : v ∉ Y ∪ Z) : v ∈ X := by
  have h : v ∈ X ∪ Y ∪ Z := by rw [hcover]; exact Finset.mem_univ v
  rcases Finset.mem_union.mp h with h' | hz
  · rcases Finset.mem_union.mp h' with hx | hy
    · exact hx
    · exact absurd (Finset.mem_union.mpr (Or.inl hy)) hv
  · exact absurd (Finset.mem_union.mpr (Or.inr hz)) hv

/-- ⭐ **因子块 `WF R X Z`**：读集落 `X ∪ Z` 内、且不整块落 `Z` 内。 -/
noncomputable def WF (R : V → Finset V) (X Z : Finset V) : Finset V :=
  Finset.univ.filter (fun v => R v ⊆ X ∪ Z ∧ ¬ R v ⊆ Z)

/-- ⭐ **因子块 `WG R Y Z`**：读集落 `Y ∪ Z` 内、且不整块落 `Z` 内。 -/
noncomputable def WG (R : V → Finset V) (Y Z : Finset V) : Finset V :=
  Finset.univ.filter (fun v => R v ⊆ Y ∪ Z ∧ ¬ R v ⊆ Z)

theorem mem_WF {R : V → Finset V} {X Z : Finset V} {v : V} :
    v ∈ WF R X Z ↔ (R v ⊆ X ∪ Z ∧ ¬ R v ⊆ Z) := by
  unfold WF; simp

theorem mem_WG {R : V → Finset V} {Y Z : Finset V} {v : V} :
    v ∈ WG R Y Z ↔ (R v ⊆ Y ∪ Z ∧ ¬ R v ⊆ Z) := by
  unfold WG; simp

/-- ⭐⭐ **三块覆盖 `univ`**（需 `Split`）。 -/
theorem WF_union_WG_union_WZ {R : V → Finset V} {X Y Z : Finset V}
    (hsplit : Fate.View19.Split R X Y Z) :
    WF R X Z ∪ WG R Y Z ∪ Wblk R Z = (Finset.univ : Finset V) := by
  ext v
  simp only [Finset.mem_union, mem_WF, mem_WG, mem_Wblk, Finset.mem_univ, iff_true]
  by_cases hZ : R v ⊆ Z
  · exact Or.inr hZ
  · rcases hsplit v with h | h
    · exact Or.inl (Or.inl ⟨h, hZ⟩)
    · exact Or.inl (Or.inr ⟨h, hZ⟩)

/-- ⭐⭐ **`WF` 与 `WG` 不交**（需 `X`、`Y` 不交）。 -/
theorem WF_disjoint_WG {R : V → Finset V} {X Y Z : Finset V} (hXY : Disjoint X Y) :
    Disjoint (WF R X Z) (WG R Y Z) := by
  refine Finset.disjoint_left.mpr fun v hvF hvG => ?_
  rw [mem_WF] at hvF
  rw [mem_WG] at hvG
  exact hvF.2 (by
    rw [← inter_union_union_eq (Z := Z) hXY]
    exact Finset.subset_inter hvF.1 hvG.1)

theorem WF_disjoint_WZ (R : V → Finset V) (X Z : Finset V) :
    Disjoint (WF R X Z) (Wblk R Z) := by
  refine Finset.disjoint_left.mpr fun v hvF hvZ => ?_
  rw [mem_WF] at hvF
  exact hvF.2 (mem_Wblk.mp hvZ)

theorem WG_disjoint_WZ (R : V → Finset V) (Y Z : Finset V) :
    Disjoint (WG R Y Z) (Wblk R Z) := by
  refine Finset.disjoint_left.mpr fun v hvG hvZ => ?_
  rw [mem_WG] at hvG
  exact hvG.2 (mem_Wblk.mp hvZ)

/-! ===========================================================================
  §2  乘积三分：`∏ univ = ∏_{WZ} · ∏_{WF} · ∏_{WG}`
  =========================================================================== -/

/-- ⭐⭐⭐ **乘积三分**。 -/
theorem prod_univ_split (ψ : V → (V → α) → ℝ) {R : V → Finset V} {X Y Z : Finset V}
    (hsplit : Fate.View19.Split R X Y Z) (hXY : Disjoint X Y) (w : V → α) :
    (∏ v, ψ v w)
      = (∏ v ∈ Wblk R Z, ψ v w) * (∏ v ∈ WF R X Z, ψ v w) * (∏ v ∈ WG R Y Z, ψ v w) := by
  classical
  set A := Wblk R Z with hA
  set B := WF R X Z with hB
  set C := WG R Y Z with hC
  have hunion : B ∪ C ∪ A = Finset.univ := WF_union_WG_union_WZ hsplit
  have hBA : Disjoint B A := WF_disjoint_WZ R X Z
  have hCA : Disjoint C A := WG_disjoint_WZ R Y Z
  have hBC : Disjoint B C := WF_disjoint_WG hXY
  have hBCA : Disjoint (B ∪ C) A := Finset.disjoint_union_left.mpr ⟨hBA, hCA⟩
  have e1 : (∏ v ∈ B ∪ C ∪ A, ψ v w) = (∏ v ∈ B ∪ C, ψ v w) * (∏ v ∈ A, ψ v w) :=
    Finset.prod_union hBCA
  have e2 : (∏ v ∈ B ∪ C, ψ v w) = (∏ v ∈ B, ψ v w) * (∏ v ∈ C, ψ v w) :=
    Finset.prod_union hBC
  have e0 : (∏ v, ψ v w) = ∏ v ∈ (B ∪ C ∪ A), ψ v w := by rw [hunion]
  rw [e0, e1, e2]
  ring

/-! ===========================================================================
  §3  读集局部性 + `mass Z` 的 X/Y 分离
  =========================================================================== -/

/-- `ReadsOn f A`：`f` 只读 `A` 上的坐标。 -/
def ReadsOn (f : (V → α) → ℝ) (A : Finset V) : Prop :=
  ∀ w w' : V → α, (∀ u ∈ A, w u = w' u) → f w = f w'

theorem readsOn_prod (ψ : V → (V → α) → ℝ) {R : V → Finset V} (hread : ReadSet ψ R)
    {W S : Finset V} (hW : ∀ v ∈ W, R v ⊆ S) :
    ReadsOn (fun w => ∏ v ∈ W, ψ v w) S := by
  intro w w' h
  exact Finset.prod_congr rfl fun v hv => hread v w w' (fun u hu => h u (hW v hv hu))

/-- ⭐ 函数层双射：`{v // v ∉ Z} → α ≃ ({v // v ∉ X∪Z} → α) × ({v // v ∉ Y∪Z} → α)`。

关键在于：`v ∉ Z` 且 `v ∉ X` ⟹ `v ∈ Y`（由 `hcover`），故「落在 `X` 之外」的部分
正好由 `Y ∪ Z` 之外的坐标与 `Z` 之外的坐标拼成。 -/
noncomputable def zEquiv {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hcover : X ∪ Y ∪ Z = Finset.univ) :
    ({v : V // v ∉ Z} → α) ≃ (({v : V // v ∉ (X ∪ Z)} → α) ×
      ({v : V // v ∉ (Y ∪ Z)} → α)) where
  toFun t :=
    (fun s => t ⟨s.1, fun h => s.2 (Finset.mem_union.mpr (Or.inr h))⟩,
     fun r => t ⟨r.1, fun h => r.2 (Finset.mem_union.mpr (Or.inr h))⟩)
  invFun p := fun z => by
    classical
    exact if hz : z.1 ∈ X
      then p.2 ⟨z.1, by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun h => Finset.disjoint_left.mp hXY hz h, z.2⟩⟩
      else p.1 ⟨z.1, by
        simp only [Finset.mem_union, not_or]
        exact ⟨hz, z.2⟩⟩
  left_inv := by
    classical
    intro t
    funext z
    by_cases hz : z.1 ∈ X
    · simp only [hz, dif_pos]
    · simp only [hz, dif_neg, not_false_iff]
  right_inv := by
    classical
    intro p
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · funext s
      have hsY : s.1 ∈ Y := notMemXZ_memY hcover s.2
      have hsX : s.1 ∉ X := fun h => Finset.disjoint_left.mp hXY h hsY
      simp only [hsX, dif_neg, not_false_iff]
    · funext r
      have hrX : r.1 ∈ X := notMemYZ_memX hcover r.2
      simp only [hrX, dif_pos]

/-- **`glue Z x t` 在 `Y ∪ Z` 上与 `glue (X∪Z) x (zEquiv t).1` 一致**。
（两者在 `Z` 上同取 `x`，在 `Y \ Z` 上同取 `t` 的 `Y` 分量。） -/
theorem glue_Z_agree_XZ {X Y Z : Finset V} (hXY : Disjoint X Y)
    (hcover : X ∪ Y ∪ Z = Finset.univ) (x : V → α) (t : {v : V // v ∉ Z} → α) :
    ∀ u ∈ Y ∪ Z, glue Z x t u = glue (X ∪ Z) x ((zEquiv hXY hcover t).1) u := by
  intro u hu
  by_cases huz : u ∈ Z
  · rw [glue_of_mem Z x t huz,
      glue_of_mem (X ∪ Z) x _ (Finset.mem_union.mpr (Or.inr huz))]
  · have huY : u ∈ Y := by
      rcases Finset.mem_union.mp hu with h | h
      · exact h
      · exact absurd h huz
    have huX : u ∉ X := fun h => Finset.disjoint_left.mp hXY h huY
    have huXZ : u ∉ X ∪ Z := by
      simp only [Finset.mem_union, not_or]; exact ⟨huX, huz⟩
    rw [glue_of_not_mem Z x t huz, glue_of_not_mem (X ∪ Z) x _ huXZ]
    rfl

/-- **`glue Z x t` 在 `X ∪ Z` 上与 `glue (Y∪Z) x (zEquiv t).2` 一致**。 -/
theorem glue_Z_agree_YZ {X Y Z : Finset V} (hXY : Disjoint X Y)
    (hcover : X ∪ Y ∪ Z = Finset.univ) (x : V → α) (t : {v : V // v ∉ Z} → α) :
    ∀ u ∈ X ∪ Z, glue Z x t u = glue (Y ∪ Z) x ((zEquiv hXY hcover t).2) u := by
  intro u hu
  by_cases huz : u ∈ Z
  · rw [glue_of_mem Z x t huz,
      glue_of_mem (Y ∪ Z) x _ (Finset.mem_union.mpr (Or.inr huz))]
  · have huX : u ∈ X := by
      rcases Finset.mem_union.mp hu with h | h
      · exact h
      · exact absurd h huz
    have huY : u ∉ Y := fun h => Finset.disjoint_left.mp hXY huX h
    have huYZ : u ∉ Y ∪ Z := by
      simp only [Finset.mem_union, not_or]; exact ⟨huY, huz⟩
    rw [glue_of_not_mem Z x t huz, glue_of_not_mem (Y ∪ Z) x _ huYZ]
    rfl

/-- ⭐⭐⭐ **`mass Z` 上的 X/Y 分离**：

若 `F` 只读 `X ∪ Z`、`G` 只读 `Y ∪ Z`，则
`mass Z (F·G) x = mass (X∪Z) G x · mass (Y∪Z) F x`。

**证明**：`mass_eq_sum_glue` 把两边都转成 `glue` 上的求和，再用 `zEquiv` 把
`{v // v ∉ Z} → α` 拆成 `X` 侧与 `Y` 侧，`sum_prod_type` + `mul_sum`/`sum_mul`
分离，最后用 `glue_Z_agree_XZ` / `glue_Z_agree_YZ` 把两边的 `glue` 对齐。 -/
theorem mass_sep_Z (F G : (V → α) → ℝ) {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hcover : X ∪ Y ∪ Z = Finset.univ)
    (hFXZ : ReadsOn F (X ∪ Z)) (hGYZ : ReadsOn G (Y ∪ Z)) (x : V → α) :
    mass Z (fun w => F w * G w) x
      = mass (X ∪ Z) G x * mass (Y ∪ Z) F x := by
  classical
  rw [mass_eq_sum_glue, mass_eq_sum_glue, mass_eq_sum_glue]
  set e := zEquiv (α := α) hXY hcover with he
  rw [Fintype.sum_equiv e
    (fun t : {v : V // v ∉ Z} → α => F (glue Z x t) * G (glue Z x t))
    (fun p : ({v : V // v ∉ (X ∪ Z)} → α) × ({v : V // v ∉ (Y ∪ Z)} → α) =>
      F (glue Z x (e.symm p)) * G (glue Z x (e.symm p))) (fun t => by simp [he])]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hes : e (e.symm (a, b)) = (a, b) := e.apply_symm_apply (a, b)
  have h1 : (e (e.symm (a, b))).1 = a := by rw [hes]
  have h2 : (e (e.symm (a, b))).2 = b := by rw [hes]
  have hAZ : ∀ u ∈ X ∪ Z, glue Z x (e.symm (a, b)) u = glue (Y ∪ Z) x b u := by
    intro u hu
    rw [glue_Z_agree_YZ hXY hcover x (e.symm (a, b)) u hu, h2]
  have hAY : ∀ u ∈ Y ∪ Z, glue Z x (e.symm (a, b)) u = glue (X ∪ Z) x a u := by
    intro u hu
    rw [glue_Z_agree_XZ hXY hcover x (e.symm (a, b)) u hu, h1]
  rw [hGYZ _ _ hAY, hFXZ _ _ hAZ]
  ring

/-! ===========================================================================
  §4  ⭐ 平方约去引理

  `(c * A) * (c * B) = (c * C) * (c * D) ↔ A * B = C * D`（`c ≠ 0`）。

  方向 `←`：直接 `ring`（不需要 `c ≠ 0`）。
  方向 `→`：用 `c * A = c * C * D / B`……不走除法，而是直接用
  `mul_left_cancel₀`（`c ≠ 0`）两次。
  =========================================================================== -/

/-- ⭐⭐ **平方约去**（`c ≠ 0`）：`(c*A)*(c*B) = (c*C)*(c*D) ↔ A*B = C*D`。 -/
theorem sq_cancel {c A B C D : ℝ} (hc : c ≠ 0) :
    (c * A) * (c * B) = (c * C) * (c * D) ↔ A * B = C * D := by
  constructor
  · intro h
    -- 把两边都写成 `c * (c * (A*B))` 与 `c * (c * (C*D))`，再用 `mul_left_cancel₀`
    have h' : c * (c * (A * B)) = c * (c * (C * D)) := by
      calc c * (c * (A * B)) = (c * A) * (c * B) := by ring
        _ = (c * C) * (c * D) := h
        _ = c * (c * (C * D)) := by ring
    exact mul_left_cancel₀ hc (mul_left_cancel₀ hc h')
  · intro h
    have := congrArg (fun t => c * (c * t)) h
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this

/-! ===========================================================================
  §5  ⭐⭐⭐⭐ 主定理 C（一般 `Z`）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **主定理 C（一般 `Z`）：因子图 `Split` 分离 ⟹ 乘性条件独立。**

**⚠ 不要求任何非零前提**：证明末尾 `ring` 直接配平 `Pz x ^ 2`。 -/
theorem condIndep_general (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hsplit : Fate.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (_hXZ : Disjoint X Z) (_hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    Fate.FactorMarkov.CondIndep p X Y Z := by
  classical
  intro x
  set Pz : (V → α) → ℝ := fun w => ∏ v ∈ Wblk R Z, ψ v w with hPz
  set F : (V → α) → ℝ := fun w => ∏ v ∈ WF R X Z, ψ v w with hF
  set G : (V → α) → ℝ := fun w => ∏ v ∈ WG R Y Z, ψ v w with hG
  -- `p = Pz * F * G`
  have hp : ∀ w, p w = Pz w * F w * G w := by
    intro w
    rw [hfac w]
    exact prod_univ_split ψ hsplit hXY w
  -- 读集局部性
  have hPzZ : ReadsOn Pz Z := readsOn_prod ψ hread (fun v hv => mem_Wblk.mp hv)
  have hFXZ : ReadsOn F (X ∪ Z) := readsOn_prod ψ hread (fun v hv => (mem_WF.mp hv).1)
  have hGYZ : ReadsOn G (Y ∪ Z) := readsOn_prod ψ hread (fun v hv => (mem_WG.mp hv).1)
  -- 冻结前提
  have hWZ_Z : ∀ v ∈ Wblk R Z, R v ⊆ Z := fun v hv => mem_Wblk.mp hv
  have hWZ_XZ : ∀ v ∈ Wblk R Z, R v ⊆ X ∪ Z := fun v hv =>
    Finset.Subset.trans (mem_Wblk.mp hv) Finset.subset_union_right
  have hWZ_YZ : ∀ v ∈ Wblk R Z, R v ⊆ Y ∪ Z := fun v hv =>
    Finset.Subset.trans (mem_Wblk.mp hv) Finset.subset_union_right
  -- `p` 的「Pz 提出」形态
  have hpZ : p = fun w => (∏ v ∈ Wblk R Z, ψ v w) * (F w * G w) := funext fun w => by
    rw [hp w]; ring
  -- `mass (X∪Y∪Z) p`
  have hmXYZ : mass (X ∪ Y ∪ Z) p x = Pz x * F x * G x := by
    rw [show X ∪ Y ∪ Z = (Finset.univ : Finset V) from hcover, mass_univ]
    exact hp x
  -- `mass Z p`
  have hmZ : mass Z p x = Pz x * mass Z (fun w => F w * G w) x := by
    rw [hpZ, mass_prod_cover ψ hread (Wblk R Z) hWZ_Z (fun w => F w * G w) x]
  -- `mass (X∪Z) p`
  have hmXZ : mass (X ∪ Z) p x = Pz x * F x * mass (X ∪ Z) G x := by
    rw [hpZ, mass_prod_cover ψ hread (Wblk R Z) hWZ_XZ (fun w => F w * G w) x,
      mass_mul (X ∪ Z) F G x (fun a b hab => hFXZ a b hab)]
    show (∏ v ∈ Wblk R Z, ψ v x) * (F x * mass (X ∪ Z) G x)
      = Pz x * F x * mass (X ∪ Z) G x
    rw [hPz]; ring
  -- `mass (Y∪Z) p`
  have hmYZ : mass (Y ∪ Z) p x = Pz x * G x * mass (Y ∪ Z) F x := by
    rw [hpZ, mass_prod_cover ψ hread (Wblk R Z) hWZ_YZ (fun w => F w * G w) x]
    have hswap : mass (Y ∪ Z) (fun w => F w * G w) x = G x * mass (Y ∪ Z) F x := by
      rw [show (fun w => F w * G w) = (fun w => G w * F w) from funext fun w => mul_comm _ _]
      exact mass_mul (Y ∪ Z) G F x (fun a b hab => hGYZ a b hab)
    rw [hswap]
    show (∏ v ∈ Wblk R Z, ψ v x) * (G x * mass (Y ∪ Z) F x)
      = Pz x * G x * mass (Y ∪ Z) F x
    rw [hPz]; ring
  -- `mass Z (F*G)` 的分离
  have hsep : mass Z (fun w => F w * G w) x
      = mass (X ∪ Z) G x * mass (Y ∪ Z) F x :=
    mass_sep_Z F G hXY hcover hFXZ hGYZ x
  -- 收口
  show mass (X ∪ Y ∪ Z) p x * mass Z p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x
  rw [hmXYZ, hmZ, hmXZ, hmYZ, hsep]
  ring

/-! ===========================================================================
  §6  ⭐⭐⭐⭐ 非零前提变体（任务书签名版）：显式约去 `Pz x ^ 2`
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **主定理 C（一般 `Z`，带非零前提）**：

与 `condIndep_general` 结论相同，但**额外接受** `hprod : ∀ x, Pz x ≠ 0`，
并在证明中**真的约去** `Pz x ^ 2`（经 `sq_cancel`）。

这演示了任务书要求的「约去路线」：四个 `mass` 各写成 `Pz x` 倍，代入后两端
都是 `Pz x^2 * (…)`，用 `sq_cancel` 约去即回到不带非零前提的情形。 -/
theorem condIndep_general_nz (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hsplit : Fate.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ)
    (hprod : ∀ x, (∏ v ∈ Wblk R Z, ψ v x) ≠ 0) :
    Fate.FactorMarkov.CondIndep p X Y Z := by
  classical
  intro x
  set Pz : (V → α) → ℝ := fun w => ∏ v ∈ Wblk R Z, ψ v w with hPz
  set F : (V → α) → ℝ := fun w => ∏ v ∈ WF R X Z, ψ v w with hF
  set G : (V → α) → ℝ := fun w => ∏ v ∈ WG R Y Z, ψ v w with hG
  have hp : ∀ w, p w = Pz w * F w * G w := by
    intro w
    rw [hfac w]
    exact prod_univ_split ψ hsplit hXY w
  have hFXZ : ReadsOn F (X ∪ Z) :=
    readsOn_prod ψ hread (fun v hv => (mem_WF.mp hv).1)
  have hGYZ : ReadsOn G (Y ∪ Z) :=
    readsOn_prod ψ hread (fun v hv => (mem_WG.mp hv).1)
  have hWZ_Z : ∀ v ∈ Wblk R Z, R v ⊆ Z := fun v hv => mem_Wblk.mp hv
  have hWZ_XZ : ∀ v ∈ Wblk R Z, R v ⊆ X ∪ Z := fun v hv =>
    Finset.Subset.trans (mem_Wblk.mp hv) Finset.subset_union_right
  have hWZ_YZ : ∀ v ∈ Wblk R Z, R v ⊆ Y ∪ Z := fun v hv =>
    Finset.Subset.trans (mem_Wblk.mp hv) Finset.subset_union_right
  have hpZ : p = fun w => (∏ v ∈ Wblk R Z, ψ v w) * (F w * G w) := funext fun w => by
    rw [hp w]; ring
  have hmXYZ : mass (X ∪ Y ∪ Z) p x = Pz x * F x * G x := by
    rw [show X ∪ Y ∪ Z = (Finset.univ : Finset V) from hcover, mass_univ]
    exact hp x
  have hmZ : mass Z p x = Pz x * mass Z (fun w => F w * G w) x := by
    rw [hpZ, mass_prod_cover ψ hread (Wblk R Z) hWZ_Z (fun w => F w * G w) x]
  have hmXZ : mass (X ∪ Z) p x = Pz x * F x * mass (X ∪ Z) G x := by
    rw [hpZ, mass_prod_cover ψ hread (Wblk R Z) hWZ_XZ (fun w => F w * G w) x,
      mass_mul (X ∪ Z) F G x (fun a b hab => hFXZ a b hab)]
    show (∏ v ∈ Wblk R Z, ψ v x) * (F x * mass (X ∪ Z) G x)
      = Pz x * F x * mass (X ∪ Z) G x
    rw [hPz]; ring
  have hmYZ : mass (Y ∪ Z) p x = Pz x * G x * mass (Y ∪ Z) F x := by
    rw [hpZ, mass_prod_cover ψ hread (Wblk R Z) hWZ_YZ (fun w => F w * G w) x]
    have hswap : mass (Y ∪ Z) (fun w => F w * G w) x = G x * mass (Y ∪ Z) F x := by
      rw [show (fun w => F w * G w) = (fun w => G w * F w) from funext fun w => mul_comm _ _]
      exact mass_mul (Y ∪ Z) G F x (fun a b hab => hGYZ a b hab)
    rw [hswap]
    show (∏ v ∈ Wblk R Z, ψ v x) * (G x * mass (Y ∪ Z) F x)
      = Pz x * G x * mass (Y ∪ Z) F x
    rw [hPz]; ring
  have hsep : mass Z (fun w => F w * G w) x
      = mass (X ∪ Z) G x * mass (Y ∪ Z) F x :=
    mass_sep_Z F G hXY hcover hFXZ hGYZ x
  -- 把四个 `mass` 都化成 `Pz x` 倍，再用 `sq_cancel` 约去
  show mass (X ∪ Y ∪ Z) p x * mass Z p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x
  have hAB : (F x * G x) * (mass (X ∪ Z) G x * mass (Y ∪ Z) F x)
      = (F x * mass (X ∪ Z) G x) * (G x * mass (Y ∪ Z) F x) := by ring
  have key := (sq_cancel (c := Pz x) (A := F x * G x)
    (B := mass (X ∪ Z) G x * mass (Y ∪ Z) F x)
    (C := F x * mass (X ∪ Z) G x) (D := G x * mass (Y ∪ Z) F x)
    (hprod x)).mpr hAB
  rw [hmXYZ, hmZ, hmXZ, hmYZ, hsep]
  calc Pz x * F x * G x * (Pz x * (mass (X ∪ Z) G x * mass (Y ∪ Z) F x))
      = (Pz x * (F x * G x)) * (Pz x * (mass (X ∪ Z) G x * mass (Y ∪ Z) F x)) := by
        ring
    _ = (Pz x * (F x * mass (X ∪ Z) G x)) * (Pz x * (G x * mass (Y ∪ Z) F x)) := key
    _ = Pz x * F x * mass (X ∪ Z) G x * (Pz x * G x * mass (Y ∪ Z) F x) := by ring

end Fate.GraphToProbView7
