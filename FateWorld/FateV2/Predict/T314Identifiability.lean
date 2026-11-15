import Mathlib.Logic.Equiv.Defs
/-!
  # Predict · T314Identifiability

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T314Identifiability.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Predict`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ⚠⚠ **第 230 轮降级声明（对抗性审核 B8 发现，已独立验证）**

**本模块**已不在「已证」清单里** —— 因为它的**主体是同义反复**：

> **⚠ Mathlib 已有 `Function.factorsThrough_iff`**
> （`Mathlib/Logic/Function/Basic.lean`）：
> `Function.FactorsThrough g f ↔ ∃ e, g = e ∘ f`
> **而 `Function.FactorsThrough g f` 的定义**就是** `f a = f b → g a = g b`。**
>
> **⟹ 本模块的 `identifiable_iff_factors`（可识别 ⟺ 干预量通过观测分解）**
> **与那条 Mathlib 引理**只差命名**。**

**✅ 本模块**保留**（不删除），因为：**
1. **它的表述用的是本项目自己的词汇（`ModelFamily` / `Identifiable`），有**文档价值****
2. **它显式处理了 `𝔐 = ∅` 的边界**（`identifiable_iff_factors_iff`），
   **这一点在 Mathlib 的版本里由 `[Nonempty γ]` 隐式排除**
3. **它是**正确的**（编译通过、零 sorry）

**⚠ 但**绝不可**把它当作 T3.14 的「实质证明」——
**T3.14 的实质内容需要**图侧的 d-分离**，而本模块**完全没有图**。**

**⭐⭐ 教训（已写入 `_pending/第230轮-同义反复失误登记.md`）**：
**「Lean 编译通过」只保证形式正确，不保证内容非平凡。**
-/


/-! ===========================================================================
  `Fate/_r229_A4` —— **T3.14 识别性定义的形式化**（**第 229 轮 A4**）

  ## 清单原文

  > **识别性定义的形式化**：`P(Y|do(X=x))` 在模型类 𝔐 上**可识别**，
  > 当且仅当**存在泛函 g** 使对每个 `M ∈ 𝔐` 有
  > `P_M(Y|do(X=x)) = g(P_M(V))`，且 `g` 不依赖 `M` 的 `F`。

  ## ⭐ 关键洞察：这是**纯逻辑**

  「存在性」与「不依赖」可以用**函数空间**表达：
  * `g : Obs → DoVal` —— 泛函 `g` 的**定义域是观测量的空间 `Obs`**，
    **不是**模型空间 `M`。因此 `g` **按其类型就已经**不可能读到
    `M` 的因果机制 `F`。
  * 于是「`g` 不依赖 `M`」这一条**不需要额外公理**：
    它是 `g` 的**类型**的自动推论（`ModelFamily` 结构中只暴露
    `obs : M → Obs` 与 `doVal : M → DoVal`）。

  ## 本文件的交付

  1. `identifiable_iff_factors`（= `identifiable_iff_kernel_eq`）
     —— **可识别 ⟺ 干预量通过观测分布分解**
     （`obs m₁ = obs m₂ → doVal m₁ = doVal m₂`）。
     **注**：清单的第 1、3 条是同一个命题，本文件给出一个 `Iff` 版本，
     并以 `identifiable_iff_kernel_eq` 作为别名重述。
  2. `not_identifiable_witness`
     —— **若存在两个模型观测相同但干预量不同，则不可识别**。
  3. `not_identifiable_iff_exists_witness`
     —— 不可识别 ⟺ 存在**反例对**（与 2 对偶）。
  4. `identifiable_g_unique_on_range` / `identifiable_g_val_eq`
     —— 分解泛函 `g` 在 `obs` 的像上**唯一**（识别的「单值性」）。
  5. `identifiable_of_injective_obs` / `identifiable_const_doVal` / `identifiable_of_subsingleton`
     —— 充分条件。
  6. `identifiable_iff_exists_factor`
     —— 同一条定理的**函数合成**形式 `doVal = g ∘ obs`。

  ## 空模型的边界情形

  主定理对**非空**模型类 `𝔐` 给出完整刻画（这是清单原本的语境）。
  边界情形 `𝔐 = ∅` 另行给出精确刻画：
  `identifiable_of_isEmpty`（`∅` 上可识别 ⟺ `Obs → DoVal` 非空），
  以及 `not_factors_of_isEmpty`（`Obs` 非空但 `DoVal` 空时，
  「通过观测分解」依然成立但「可识别」不成立），
  从而 `identifiable_iff_factors_iff` 说清了主定理需要 `𝔐 ≠ ∅` 的确切理由。
-/

namespace FateV2.Predict.T314
/-! ## §0 基本结构 -/

/-- 一个模型类：每个模型有一个「观测分布」`obs` 与一个「干预量」`doVal`。

`M` 扮演清单中的模型（含其机制 `F`）；`obs` 是 `P_M(V)`；
`doVal` 是 `P_M(Y|do(X=x))`（对给定的 `x`，此处 `x` 已固定）。 -/
structure ModelFamily (M : Type*) (Obs DoVal : Type*) where
  /-- 观测层：`m ↦ P_m(V)` -/
  obs : M → Obs
  /-- 干预层：`m ↦ P_m(Y | do(X=x))` -/
  doVal : M → DoVal

variable {M Obs DoVal : Type*}

/-- ⭐ **可识别**：存在 `g : Obs → DoVal` 使对每个模型 `m`，
`g (obs m) = doVal m`，且 `g` **独立于 `m`**
（这只是「`g` 的定义域是 `Obs` 而非 `M`」，**由类型自动满足**）。 -/
def Identifiable (F : ModelFamily M Obs DoVal) : Prop :=
  ∃ g : Obs → DoVal, ∀ m, g (F.obs m) = F.doVal m

/-- 「干预量通过观测分布分解」：观测相同 ⟹ 干预量相同。 -/
def FactorsThroughObs (F : ModelFamily M Obs DoVal) : Prop :=
  ∀ m₁ m₂, F.obs m₁ = F.obs m₂ → F.doVal m₁ = F.doVal m₂

/-! ## §1 ⭐ 主定理：可识别 ⟺ 干预量通过观测分解 -/

/-- ⭐ **T3.14 的实质内容**：`P(Y|do(X=x))` 可识别
**当且仅当**「观测分布相同 ⟹ 干预量相同」（假设模型类 `𝔐` 非空）。

* **(⟹)** 若有 `g`，则 `obs m₁ = obs m₂ ⟹ g (obs m₁) = g (obs m₂) ⟹ doVal m₁ = doVal m₂`。
* **(⟸)** 在 `obs` 的像上定义 `g`：`g o = doVal (代表元)`，
  代表元由 `Classical.choose` 取；`h` 保证**选谁无关**。像外取固定兜底值 `doVal m₀`。
  **这里 `g` 只吃 `Obs`，读不到 `M` 的 `F`** —— 这正是清单要求的「`g` 不依赖 `F`」，
  而且它是 `g` 的**类型**（`Obs → DoVal`）所强制的。 -/
theorem identifiable_iff_factors (F : ModelFamily M Obs DoVal) (hM : Nonempty M) :
    Identifiable F ↔ FactorsThroughObs F := by
  classical
  constructor
  · rintro ⟨g, hg⟩ m₁ m₂ h
    rw [← hg m₁, ← hg m₂, h]
  · intro h
    obtain ⟨m0⟩ := hM
    refine ⟨fun o => if ho : ∃ m, F.obs m = o then F.doVal (Classical.choose ho)
        else F.doVal m0, fun m => ?_⟩
    have hex : ∃ m', F.obs m' = F.obs m := ⟨m, rfl⟩
    simp only [dif_pos hex]
    exact h _ _ (Classical.choose_spec hex)

/-- 别名（清单第 3 条：`obs` 的核包含于 `doVal` 的核，故 `doVal` 是 `obs` 的函数）。 -/
theorem identifiable_iff_kernel_eq (F : ModelFamily M Obs DoVal) (hM : Nonempty M) :
    Identifiable F ↔ ∀ m₁ m₂, F.obs m₁ = F.obs m₂ → F.doVal m₁ = F.doVal m₂ :=
  identifiable_iff_factors F hM

/-! ## §2 反例见证：不可识别的判定 -/

/-- **见证不可识别**：若存在两个模型**观测相同但干预量不同**，则**不可识别**。
（不需要 `𝔐` 非空 —— 两个见证模型已经给出非空性。） -/
theorem not_identifiable_witness (F : ModelFamily M Obs DoVal) (m₁ m₂ : M)
    (hobs : F.obs m₁ = F.obs m₂) (hdo : F.doVal m₁ ≠ F.doVal m₂) :
    ¬ Identifiable F := by
  intro h
  exact hdo ((identifiable_iff_factors F ⟨m₁⟩).mp h m₁ m₂ hobs)

/-- **对偶**：不可识别 ⟺ 存在**反例对**。 -/
theorem not_identifiable_iff_exists_witness (F : ModelFamily M Obs DoVal)
    (hM : Nonempty M) :
    ¬ Identifiable F ↔ ∃ m₁ m₂, F.obs m₁ = F.obs m₂ ∧ F.doVal m₁ ≠ F.doVal m₂ := by
  classical
  rw [identifiable_iff_factors F hM, FactorsThroughObs]
  constructor
  · intro h
    by_contra hcon
    apply h
    intro a b ho
    apply Classical.byContradiction
    intro hne
    exact hcon ⟨a, b, ho, hne⟩
  · rintro ⟨a, b, ho, hd⟩ hfac
    exact hd (hfac a b ho)

/-! ## §3 泛函 `g` 的单值性（识别的「唯一」部分） -/

/-- `g` 在 `obs` 的**像上取值唯一**：任何两个分解泛函在像上一致。 -/
theorem identifiable_g_unique_on_range (F : ModelFamily M Obs DoVal)
    {g₁ g₂ : Obs → DoVal} (h₁ : ∀ m, g₁ (F.obs m) = F.doVal m)
    (h₂ : ∀ m, g₂ (F.obs m) = F.doVal m) :
    ∀ m, g₁ (F.obs m) = g₂ (F.obs m) :=
  fun m => (h₁ m).trans (h₂ m).symm

/-- 具体化的取值：任一分解泛函在 `obs` 的像上等于 `doVal`。 -/
theorem identifiable_g_val_eq (F : ModelFamily M Obs DoVal) (m₀ : M)
    {g : Obs → DoVal} (hg : ∀ m, g (F.obs m) = F.doVal m) :
    g (F.obs m₀) = F.doVal m₀ :=
  hg m₀

/-- **分解泛函在像上的存在唯一性**（「存在」由可识别性给，「唯一」由上式给）。 -/
theorem existsUnique_g_on_range (F : ModelFamily M Obs DoVal) (h : Identifiable F)
    (o : Obs) (ho : ∃ m, F.obs m = o) :
    ∃! d : DoVal, ∃ m, F.obs m = o ∧ F.doVal m = d := by
  obtain ⟨m, hm⟩ := ho
  refine ⟨F.doVal m, ⟨m, hm, rfl⟩, ?_⟩
  rintro d ⟨m', hm', rfl⟩
  obtain ⟨g, hg⟩ := h
  rw [← hg m, ← hg m', hm, hm']

/-! ## §4 充分条件 -/

/-- **观测单射 ⟹ 可识别**（观测已足够区分模型）。 -/
theorem identifiable_of_injective_obs (F : ModelFamily M Obs DoVal) (hM : Nonempty M)
    (hinj : Function.Injective F.obs) : Identifiable F :=
  (identifiable_iff_factors F hM).mpr fun m₁ m₂ h => by rw [hinj h]

/-- **干预量恒定 ⟹ 可识别**（`g` 为常函数）。 -/
theorem identifiable_const_doVal (F : ModelFamily M Obs DoVal) (hM : Nonempty M)
    {d : DoVal} (h : ∀ m, F.doVal m = d) : Identifiable F :=
  (identifiable_iff_factors F hM).mpr fun m₁ m₂ _ => by rw [h m₁, h m₂]

/-- **模型类至多一个元素 ⟹ 可识别**（`g` 只需命中一个点）。 -/
theorem identifiable_of_subsingleton (F : ModelFamily M Obs DoVal) [Subsingleton M]
    (hM : Nonempty M) : Identifiable F :=
  (identifiable_iff_factors F hM).mpr fun m₁ m₂ _ => by rw [Subsingleton.elim m₁ m₂]

/-! ## §5 函数合成形式 -/

/-- **分解的合成形式**：可识别 ⟺ `doVal` 经由 `obs` 因子分解。 -/
theorem identifiable_iff_exists_factor (F : ModelFamily M Obs DoVal) :
    Identifiable F ↔ ∃ g : Obs → DoVal, F.doVal = g ∘ F.obs := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, funext fun m => (hg m).symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, fun m => by
      have := congrFun hg m
      simpa [Function.comp] using this.symm⟩

/-! ## §6 边界情形 `𝔐 = ∅`：主定理为何需要非空 -/

/-- `M` 空时「通过观测分解」**自动成立**（`∀ m` 空真）。 -/
theorem factors_of_isEmpty [IsEmpty M] (F : ModelFamily M Obs DoVal) :
    FactorsThroughObs F := by
  intro m
  exact isEmptyElim m

/-- `M` 空时，可识别 ⟺ `Obs → DoVal` 非空。 -/
theorem identifiable_of_isEmpty [IsEmpty M] (F : ModelFamily M Obs DoVal) :
    Identifiable F ↔ Nonempty (Obs → DoVal) := by
  constructor
  · rintro ⟨g, _⟩; exact ⟨g⟩
  · rintro ⟨g⟩
    refine ⟨g, fun m => ?_⟩
    exact (isEmptyElim m : g (F.obs m) = F.doVal m)

/-- **主定理的「⟸」方向在 `𝔐 = ∅` 处确实失效**：
若 `Obs` 非空但 `DoVal` 空，则「通过观测分解」成立而「可识别」不成立。
（这解释了 `identifiable_iff_factors` 中的 `Nonempty M` 假设是必要的。） -/
theorem not_identifiable_empty_doVal [IsEmpty M] (hObs : Nonempty Obs)
    [IsEmpty DoVal] (F : ModelFamily M Obs DoVal) : ¬ Identifiable F := by
  rintro ⟨g, -⟩
  exact isEmptyElim (g (Classical.choice hObs) : DoVal)

/-- 因此，`∅` 上的完整刻画：可识别 ⟺ 通过观测分解 ∧ (`Obs` 空 ∨ `DoVal` 非空)。 -/
theorem identifiable_iff_factors_iff [IsEmpty M] (F : ModelFamily M Obs DoVal) :
    Identifiable F ↔
      (FactorsThroughObs F ∧ (IsEmpty Obs ∨ Nonempty DoVal)) := by
  have key : Nonempty (Obs → DoVal) ↔ IsEmpty Obs ∨ Nonempty DoVal := by
    constructor
    · rintro ⟨f⟩
      by_cases hO : Nonempty Obs
      · exact Or.inr ⟨f (Classical.choice hO)⟩
      · exact Or.inl ⟨fun o => hO ⟨o⟩⟩
    · rintro (h | h)
      · exact ⟨fun o => (h.false o).elim⟩
      · obtain ⟨d⟩ := h
        exact ⟨fun _ => d⟩
  rw [identifiable_of_isEmpty F, key]
  exact ⟨fun h => ⟨factors_of_isEmpty F, h⟩, fun h => h.2⟩

end FateV2.Predict.T314