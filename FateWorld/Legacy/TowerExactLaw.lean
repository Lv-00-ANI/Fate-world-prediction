import FateWorld.Legacy.DAGFactorizationGeneral
import FateWorld.Legacy.DAGFactorization
import FateWorld.Legacy.TowerAudit

/-! ===========================================================================
  `Fate.TowerExactLaw` —— **塔反例的「最小反例再分析」：精确乘子定律**

  ## 0 本文定位

  `Fate.TowerAudit` 已独立复核并给出结论「根因是 `mass` 非归一化」。
  `Fate.TowerExactLaw` 把这条结论**严格化、定量化**：不只是「不相等」，
  而是**精确相等于一个乘子**：

  > **定理（精确塔定律，`T ⊆ S`）**
  > `mass S (fun w => mass T p w) x = multS S x · mass T p x`
  > 其中 `multS S x := ∑_{w : w|_S = x|_S} 1 = |α|^{|V \ S|}`。

  这把「塔性质为假」从「观察到一个 `1 ≠ 0` 的反例」升级为
  **对所有 `p`、所有 `T ⊆ S` 都成立的定量定律**。主控的最小反例只是
  `multS ≠ 1` 的一个取值特例（`V = α = Bool`，`S = {true}`，`multS = 2`）。

  ## 1 数学结论

  `mass` 是 **纤维和（非归一化边缘）**。迭代 `mass` 时，外层把**内层已被
  求和掉的坐标上的自由度又重新枚举了一遍**，从而产生乘子
  `multS S x = |α|^{|V\S|}`：

  * `T ⊆ S`：`mass S (mass T p) x = multS S x · mass T p x`。
  * **特例 `T = S`（幂等）**：`mass S (mass S p) x = multS S x · mass S p x`。
    除 `S = univ`（`multS = 1`）外**永不相等**。
  * **`S = univ`**：`multS univ x = 1`，此时塔**平凡成立**（因 `mass univ = id`）。

  ⟹ 「先边缘 `T` 再边缘 `S`」在数学上确实不同于「一次性边缘 `S ∪ T`」，
  但二者并非毫无关系：前者 = `|α|^{|V\S|}` 乘以内层量。
  差异是一个 **纤维计数乘子**，不是 Lean 实现错误，而是 `mass`
  语义（纤维和 / 非归一化测度）的**必然结果**。

  ## 2 对「Lean 实现问题还是数学问题」的裁定

  **是数学问题（语义不匹配），且可被精确刻画。**
  `mass` 是「对自由坐标求和的**测度（measure）**」。
  测度的塔需要**归一化**（概率塔 `P(Y|X) = Σ_z P(Y|Z) P(Z|X)`）
  或**推送（push-forward）到更小的型**。
  在型 `(V → α) → ℝ` 上原地迭代 `mass`，等于把「测度」当「密度」反复积分，
  必然多出体积因子 `|α|^{|V\S|}`。这与 Lean 无关，是测度论事实。

  ## 3 零 `sorry`

  `lake env lean Fate/TowerExactLaw.lean` 无输出。
  =========================================================================== -/

namespace Fate.TowerExactLaw

open Finset Fate.DAGFactorization

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ### §1 双和展开（无假设） -/

/-- **双和展开**：把 `mass S (mass T p) x` 严格展开成对 `(w,z)` 的双和：
    `mass S (mass T p) x = ∑_w ∑_z 𝟙[w|_S = x|_S] · 𝟙[z|_T = w|_T] · p z`。
    这是后面一切（乘子定律、反例）的**唯一源头**。零假设、零 `sorry`。 -/
theorem mass_mass_expand (S T : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => mass T p w) x
      = ∑ w : V → α, ∑ z : V → α,
          (if (∀ u ∈ S, w u = x u) then (if (∀ u ∈ T, z u = w u) then p z else 0) else 0) := by
  unfold mass
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : (∀ u ∈ S, w u = x u)
  · rw [if_pos h]
    exact Finset.sum_congr rfl fun z _ => by rw [if_pos h]
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun z _ => by rw [if_neg h]).symm

/-- **纤维计数乘子**：`multS S x = #{w : w|_S = x|_S}`。 -/
noncomputable def multS (S : Finset V) (x : V → α) : ℝ :=
  ∑ w : V → α, if (∀ u ∈ S, w u = x u) then (1:ℝ) else 0

/-! ### §2 精确塔定律（`T ⊆ S`） -/

/-- ⭐⭐⭐⭐⭐ **精确塔定律**。当 `T ⊆ S`：
    `mass S (mass T p) x = multS S x · mass T p x`。

    **解读**：外层 `mass S` 的作用只是把内层结果 `mass T p x` 乘上
    **`S` 之外自由坐标数** `multS S x = |α|^{|V\S|}`。它**没有**变成
    `mass (S∪T) p`，只是**缩放**了 `mass T p`。 -/
theorem mass_mass_of_subset (S T : Finset V) (hTS : T ⊆ S) (p : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => mass T p w) x = multS S x * mass T p x := by
  unfold mass multS
  have step : ∀ w : V → α,
      (if (∀ u ∈ S, w u = x u) then (∑ z : V → α, if (∀ u ∈ T, z u = w u) then p z else 0) else 0)
      = (if (∀ u ∈ S, w u = x u) then (1:ℝ) else 0)
          * (∑ z : V → α, if (∀ u ∈ T, z u = x u) then p z else 0) := by
    intro w
    by_cases hw : (∀ u ∈ S, w u = x u)
    · rw [if_pos hw, if_pos hw, one_mul]
      have hTx : ∀ u ∈ T, w u = x u := fun u hu => hw u (hTS hu)
      refine Finset.sum_congr rfl fun z _ => ?_
      have e : (∀ u ∈ T, z u = w u) ↔ (∀ u ∈ T, z u = x u) :=
        ⟨fun hh u hu => (hh u hu).trans (hTx u hu),
         fun hh u hu => (hh u hu).trans (hTx u hu).symm⟩
      rw [if_congr e rfl rfl]
    · rw [if_neg hw, if_neg hw, zero_mul]
  rw [Finset.sum_congr rfl fun w _ => step w, Finset.sum_mul]

/-! ### §3 乘子的性质 -/

/-- `multS` 至少为 `1`（`x` 自己被计数）。 -/
theorem one_le_multS (S : Finset V) (x : V → α) : 1 ≤ multS S x := by
  unfold multS
  have hmem : ∀ u ∈ S, x u = x u := fun _ _ => rfl
  have h := Finset.single_le_sum
    (f := fun w : V → α => if (∀ u ∈ S, w u = x u) then (1:ℝ) else 0)
    (fun w _ => by positivity) (Finset.mem_univ x)
  simpa [hmem] using h

/-- `multS univ = 1`（`S` 取全集时无自由坐标，乘子消失 ⟹ 塔平凡成立）。 -/
theorem multS_univ (x : V → α) : multS (Finset.univ : Finset V) x = 1 := by
  unfold multS
  have e : (∑ w : V → α, if (∀ u ∈ (Finset.univ : Finset V), w u = x u) then (1:ℝ) else 0)
      = ∑ w : V → α, if (w = x) then (1:ℝ) else 0 := by
    refine Finset.sum_congr rfl fun w _ => ?_
    have hh : (∀ u ∈ (Finset.univ : Finset V), w u = x u) ↔ w = x :=
      ⟨fun h => funext fun u => by simpa using h u (Finset.mem_univ u),
       fun h u _ => by rw [h]⟩
    rw [if_congr hh rfl rfl]
  rw [e, Finset.sum_ite_eq']
  simp

/-! ### §4 幂等失败的精确形式 -/

/-- ⭐ **幂等的精确形式**：`mass S (mass S p) x = multS S x · mass S p x`。 -/
theorem mass_self_eq (S : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => mass S p w) x = multS S x * mass S p x :=
  mass_mass_of_subset S S (Subset.refl S) p x

/-- ⭐⭐ **幂等只在 `multS = 1` 时成立**：
    若 `multS S x ≠ 1` 且 `mass S p x ≠ 0`，则 `mass S (mass S p) x ≠ mass S p x`。 -/
theorem mass_self_fails (S : Finset V) (p : (V → α) → ℝ) (x : V → α)
    (hm : multS S x ≠ 1) (hp : mass S p x ≠ 0) :
    mass S (fun w => mass S p w) x ≠ mass S p x := by
  rw [mass_self_eq]
  intro h
  apply hm
  have hmul : multS S x * mass S p x = 1 * mass S p x := by rw [h, one_mul]
  exact mul_right_cancel₀ hp hmul

/-! ### §5 最小反例的精确读数（`V = α = Bool`） -/

section BoolCase

/-- `multS {true} (const false) = 2 = |α|^{|V \ {true}|} = 2^1`。
    这就是主控反例里「左边 `1`、右边 `0`」背后那个**乘子 `2`** 的精确值。 -/
theorem multS_singleton_bool :
    multS ({(true : Bool)}) (fun _ => false) = 2 := by
  unfold multS
  rw [univ_boolFun]
  simp only [Finset.sum_insert (by decide : bTrue ∉ ({bId, bNot, bFalse} : Finset (Bool → Bool))),
    Finset.sum_insert (by decide : bId ∉ ({bNot, bFalse} : Finset (Bool → Bool))),
    Finset.sum_insert (by decide : bNot ∉ ({bFalse} : Finset (Bool → Bool))),
    Finset.sum_singleton]
  norm_num [bTrue, bId, bNot, bFalse]

end BoolCase

end Fate.TowerExactLaw
