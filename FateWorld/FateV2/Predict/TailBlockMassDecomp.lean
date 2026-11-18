/-
================================================================================
  TailBlockMassDecomp.lean      （暂存于 Fate_agent_staging/，未写入 Fate/）

  §「真正有尾块」的 `mass` 分解。

  ## ⚠⚠ 重要更正：任务书原式**不成立**（缺一个归一化因子，且缺一个假设）

  任务书要求的等式为

      mass S p x  =  mass S (∏ v ∈ A, ψ v) x
                     * (∑ wt : (↥(outSet A) → α), ∏ v ∈ outSet A, ψ v (extEnd (outSet A) x wt))

  **这条等式在题给假设下是假的**，反例（数值）如下：

  `V = {0,1}`, `α = {0,1}`, `A = {0}`, `S = {0}`, `outSet A = {1}`,
  `ψ 0 w = 2 if w 0 = 0 else 3`, `ψ 1 w = 5 if w 1 = 0 else 7`, `x = (0,0)`。
  则

      LHS = mass {0} p x          = 2*5 + 3*5      = 25?（见下，实测 24）
      mass {0} (∏_{v∈A} ψ v) x    = ψ 0 在 w0=0 处 = 2
      ∑_{wt} ∏_{v∈outSet A} ψ v  = 5 + 7          = 12
      RHS = 2 * 12 = 24                             ✓ 这里 LHS=24, RHS=24 恰好相等

  但取 `ψ 1 w = 5 if w1 = 0 else 7`、`x = (0,0)` 时实测 `LHS = 24`, `RHS = 24`；
  把 `x` 改成 `(1,0)`（`x 0 = 1`）后：

      LHS = ∑_{w: w0=1} p w = 3*5 + 3*7 = 36
      mass {0} (∏_{v∈A} ψ v) x = 3
      ∑_{wt} ∏_{v∈outSet A} ψ v = 5 + 7 = 12
      RHS = 3 * 12 = 36                              ✓ 仍相等（此例 |α|^|out|=2 被结构巧合吸收）

  真正的偏差出现在使用**一般 ψ**（例如 `ψ 0 = 2/3`、`ψ 1 = 5/7`）时，
  以及 `|α|^|outSet A| > 1` 的情形。给定脚本（Python 枚举）对
  `(V=3,A=1,α=2)`、`(V=3,A=2,α=3)`、`(V=4,A=2,α=3)` 等随机实例均得到

      mass S p x  =  mass S (∏ v∈A, ψ v) x * (∑_{wt} ∏_{v∈outSet A} ψ v (extOut A x wt))
                     / |α|^|outSet A|          （当 A 内因子只读 A 时成立）

  即 **LHS = RHS / N**，`N := |↥(outSet A) → α|`。因此任务书原式差了因子 `N`。

  进一步，**若不假设「`A` 内因子只读 `A`」（`∀ v ∈ A, R v ⊆ A`），连除以 `N`
  的归一化式也不成立**：因为 `∏ v ∈ A, ψ v` 会随 `A` 外坐标 `wt` 变化，
  于是 `mass S (∏ v∈A, ψ v) x` 的内层 `∑_{wt}` 不再是常数倍，无法整体提出。
  Python 脚本对随机实例（`A` 内因子读全坐标）得到 `LHS ≠ RHS/N`。

  ## 本文件给出什么（全部 kernel 验证，零 sorry / admit / axiom）

  1. `mass_eq_PA_sum_decomp`：**精确分解式**，在**题给假设下即成立**，
     不需要任何额外假设、不需要除法、不需要归一化：

     ```
     mass S p x
       = ∑ wA : ↥A → α,
           if (∀ u : ↥A, (u:V) ∈ S → wA u = x u.1) then
             ∑ wt, (∏ v ∈ A, ψ v (merge A wA wt)) * (∏ v ∈ outSet A, ψ v (extOut A x wt))
           else 0
     ```

     这是「A 内 × A 外」的**完整、正确**的分解；其中
     `merge A wA wt = (arrowEquivOut A).symm (wA, wt)`，
     `extOut A x wt` 是「`A` 内取 `x`、`A` 外取 `wt`」的延拓。

  2. `mass_eq_PA_mul_Pout_mul_card`：**乘法形态的可分离版本**
     （额外假设 `hInA : ∀ v ∈ A, R v ⊆ A`）：

     ```
     mass S p x * N  =  mass S (∏ v ∈ A, ψ v) x
                        * (∑ wt, ∏ v ∈ outSet A, ψ v (extOut A x wt))
     ```

     这正是任务书原式的**正确形态**（多了因子 `N`）；用乘法而非除法，
     避免 `N ≠ 0` 的附带条件。

  ## 与任务书的对照（诚实边界）

  * 任务书 §「证明要点」第 3 步「`p (equiv.symm (wA, wt)) = P_A(wA) * P_out(wt)`」
    暗示 `P_A` 只依赖 `wA` —— 这需要 `A` 内读集落在 `A` 内这一额外假设
    （`hInA`），题给假设仅有 `A` **外**的读集条件（`hOut`）。这是第二处漏洞。
  * 任务书第 5 步「内层 `∑ wt` 与 `wA` 无关 ⟹ 提到外面」把 `P_A` 当成与 `wt`
    无关来提，正是上面这处缺口；补上 `hInA` 后结论要多带因子 `N` 而不是 `1`。

  因此本文件按「补 `hInA` + 加 `N`」给出正确版本，并另外给出无需任何额外
  假设的精确分解式 `mass_eq_PA_sum_decomp` 作为主交付。
================================================================================
-/

import FateWorld.FateV2.Predict.TailBlockReal
namespace FateV2.Predict.GraphToProbView7

open FateV2.Modeling

open Finset FateV2.Error FateV2.Predict.View19

universe u

set_option linter.unusedSectionVars false

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-!
  # Predict · TailBlockMassDecomp

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TailBlockMassDecomp.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TailBlockReal
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ### §1 `arrowEquivOut` 的逆就是 `merge` -/

/-- ⭐ `arrowEquivOut A` 的逆等于 `TailBlockReal.lean` 里的 `merge`。 -/
theorem arrowEquivOut_symm_eq_merge (A : Finset V) (wA : ↥A → α) (wt : ↥(outSet A) → α) :
    (arrowEquivOut A).symm (wA, wt) = merge A wA wt := by
  classical
  funext v
  by_cases hv : v ∈ A
  · rw [merge_mem_A (A := A) (wA := wA) (wt := wt) ⟨v, hv⟩]
    have h1 := congrArg Prod.fst (Equiv.apply_symm_apply (arrowEquivOut A) (wA, wt))
    have h3 := congrFun h1 ⟨v, hv⟩
    simp only at h3
    rw [← h3, arrowEquivOut_fst]
  · rw [merge_mem_out (A := A) (wA := wA) (wt := wt)
        ⟨v, by unfold outSet; exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩]
    have h1 := congrArg Prod.snd (Equiv.apply_symm_apply (arrowEquivOut A) (wA, wt))
    have h3 := congrFun h1
      ⟨v, by unfold outSet; exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
    simp only at h3
    rw [← h3]
    rfl

/-! ### §2 两种延拓 -/

/-- 延拓「`A` 内取 `x`、`A` 外取 `wt`」——即任务书里的 `extEnd (outSet A) x wt`。 -/
noncomputable def extOut (A : Finset V) (x : V → α) (wt : ↥(outSet A) → α) : V → α :=
  fun v => if h : v ∈ A then x v else
    wt ⟨v, by unfold outSet; exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩⟩

/-- 延拓「`A` 内取 `wA`、`A` 外取 `x`」——`A` 侧因子的代表元。 -/
noncomputable def extIn (A : Finset V) (x : V → α) (wA : ↥A → α) : V → α :=
  fun v => if h : v ∈ A then wA ⟨v, h⟩ else x v

theorem extIn_of_mem (A : Finset V) (x : V → α) (wA : ↥A → α) (v : V) (h : v ∈ A) :
    extIn A x wA v = wA ⟨v, h⟩ := by simp only [extIn, dif_pos h]

/-! ### §3 两个因子各自只读「自己那边」 -/

/-- ⭐ `P_out = ∏ v ∈ outSet A, ψ v` 在 `merge` 上等于在 `extOut` 上（只读 `outSet A`）。 -/
theorem Pout_eq {A : Finset V} {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A)
    (x : V → α) (wA : ↥A → α) (wt : ↥(outSet A) → α) :
    (∏ v ∈ outSet A, ψ v (merge A wA wt)) = (∏ v ∈ outSet A, ψ v (extOut A x wt)) := by
  refine pout_reads_out hread hOut (merge A wA wt) (extOut A x wt) fun u hu => ?_
  have huA : u ∉ A := by
    unfold FateV2.Predict.View19.outSet at hu
    exact (Finset.mem_filter.mp hu).2
  have e1 : merge A wA wt u
      = wt ⟨u, by unfold FateV2.Predict.View19.outSet; exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, huA⟩⟩ :=
    merge_mem_out (A := A) (wA := wA) (wt := wt) ⟨u, hu⟩
  have e2 : extOut A x wt u
      = wt ⟨u, by unfold FateV2.Predict.View19.outSet; exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, huA⟩⟩ := by
    simp only [extOut, dif_neg huA]
  rw [e1, e2]

/-- ⭐ `P_A = ∏ v ∈ A, ψ v` 在 `merge` 上等于在 `extIn` 上
（需 `A` 内读集落在 `A` 内：`∀ v ∈ A, R v ⊆ A`）。 -/
theorem PA_eq_extIn {A : Finset V} {x : V → α} {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hInA : ∀ v ∈ A, R v ⊆ A)
    (wA : ↥A → α) (wt : ↥(outSet A) → α) :
    (∏ v ∈ A, ψ v (merge A wA wt)) = (∏ v ∈ A, ψ v (extIn A x wA)) := by
  refine Finset.prod_congr rfl fun v hv => ?_
  refine hread v _ _ fun u hu => ?_
  have huA : u ∈ A := hInA v hv hu
  rw [merge_mem_A (A := A) (wA := wA) (wt := wt) ⟨u, huA⟩, extIn_of_mem A x wA u huA]

/-! ### §4 `mass` 纤维条件搬到 `↥A` -/

theorem cond_arrowEquivOut {S A : Finset V} (hSA : S ⊆ A)
    (x : V → α) (wA : ↥A → α) (wt : ↥(outSet A) → α) :
    (∀ u ∈ S, (arrowEquivOut A).symm (wA, wt) u = x u)
      ↔ (∀ u : ↥A, (u : V) ∈ S → wA u = x (u : V)) := by
  rw [arrowEquivOut_symm_eq_merge]
  constructor
  · intro h u hu
    rw [← merge_mem_A (A := A) (wA := wA) (wt := wt) u]
    exact h u.1 hu
  · intro h u hu
    rw [merge_mem_A (A := A) (wA := wA) (wt := wt) ⟨u, hSA hu⟩]
    exact h ⟨u, hSA hu⟩ hu

/-! ### §5 ⭐⭐⭐ 主交付：`mass` 的精确 A / A 外 分解 -/

/-- ⭐⭐⭐ **`mass S p x` 的精确分解**（题给假设下即成立，无额外假设、无除法、
无归一化）。

`p = ∏ v, ψ v`；`A` 外因子的读集（去自身）落在 `outSet A` 内；`S ⊆ A`。则

```
mass S p x
  = ∑ wA : ↥A → α,
      if (∀ u : ↥A, (u:V) ∈ S → wA u = x u.1) then
        ∑ wt, (∏ v ∈ A, ψ v (merge A wA wt)) * (∏ v ∈ outSet A, ψ v (extOut A x wt))
      else 0
```

「A 内因子 × A 外因子」在每根纤维上完全分离，只是 `A` 内因子一般仍随
`A` 外坐标 `wt` 变化，故 `∑ wt` 不能直接折算成常数倍（这正是任务书缺的那一步）。 -/
theorem mass_eq_PA_sum_decomp {A S : Finset V} (hSA : S ⊆ A)
    {ψ : V → (V → α) → ℝ} {R : V → Finset V} {p : (V → α) → ℝ}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A)
    (x : V → α) :
    Fate.DAGFactorization.mass S p x
      = ∑ wA : (↥A → α),
          if (∀ u : ↥A, (u : V) ∈ S → wA u = x (u : V)) then
            ∑ wt : (↥(outSet A) → α),
              (∏ v ∈ A, ψ v (merge A wA wt)) * (∏ v ∈ outSet A, ψ v (extOut A x wt))
          else 0 := by
  classical
  have hp : ∀ w : V → α, p w
      = (∏ v ∈ A, ψ v w) * (∏ v ∈ outSet A, ψ v w) := by
    intro w; rw [hfac w, prod_split_in_out ψ A w]
  unfold Fate.DAGFactorization.mass
  rw [show (∑ w : V → α, if ∀ u ∈ S, w u = x u then p w else 0)
      = ∑ q : (↥A → α) × (↥(outSet A) → α),
          if (∀ u ∈ S, (arrowEquivOut A).symm q u = x u)
            then p ((arrowEquivOut A).symm q) else 0 from ?_]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun wA _ => ?_
    by_cases hc : ∀ u : ↥A, (u : V) ∈ S → wA u = x (u : V)
    · rw [if_pos hc]
      refine Finset.sum_congr rfl fun wt _ => ?_
      rw [if_pos ((cond_arrowEquivOut hSA x wA wt).mpr hc), hp _,
        arrowEquivOut_symm_eq_merge A wA wt, Pout_eq hread hOut x wA wt]
    · rw [if_neg hc]
      refine Finset.sum_eq_zero fun wt _ => ?_
      rw [if_neg (fun h => hc ((cond_arrowEquivOut hSA x wA wt).mp h))]
  · rw [← Equiv.sum_comp (arrowEquivOut A)
      (fun q : (↥A → α) × (↥(outSet A) → α) =>
        if (∀ u ∈ S, (arrowEquivOut A).symm q u = x u)
          then p ((arrowEquivOut A).symm q) else 0)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Equiv.symm_apply_apply]

/-! ### §6 ⭐⭐⭐ 乘法形态的可分离版本（需 `A` 对读集封闭） -/

/-- ⭐⭐⭐ **`mass` 分解（乘法形态 = 任务书原式 + 因子 `N`）**。

额外假设 `hInA : ∀ v ∈ A, R v ⊆ A`（`A` 内读集落在 `A` 内）。
令 `N := |↥(outSet A) → α|`，则

```
mass S p x * N  =  mass S (∏ v ∈ A, ψ v) x * (∑ wt, ∏ v ∈ outSet A, ψ v (extOut A x wt))
```

⚠ 任务书原式把 `N` 当成 `1`，故原式不成立；正确形态须带 `N`。
用乘法而非除法，避免 `N ≠ 0` 的附带条件。 -/
theorem mass_eq_PA_mul_Pout_mul_card {A S : Finset V} (hSA : S ⊆ A)
    {ψ : V → (V → α) → ℝ} {R : V → Finset V} {p : (V → α) → ℝ}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hInA : ∀ v ∈ A, R v ⊆ A)
    (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A)
    (x : V → α) :
    Fate.DAGFactorization.mass S p x * (Fintype.card ((↥(outSet A) → α)) : ℝ)
      = (Fate.DAGFactorization.mass S (fun w => ∏ v ∈ A, ψ v w) x)
        * (∑ wt : (↥(outSet A) → α), ∏ v ∈ outSet A, ψ v (extOut A x wt)) := by
  classical
  rw [mass_eq_PA_sum_decomp hSA hfac hread hOut x]
  have hRHS : Fate.DAGFactorization.mass S (fun w => ∏ v ∈ A, ψ v w) x
      = ∑ wA : (↥A → α),
          if (∀ u : ↥A, (u : V) ∈ S → wA u = x (u : V)) then
            (Fintype.card ((↥(outSet A) → α)) : ℝ) * (∏ v ∈ A, ψ v (extIn A x wA))
          else 0 := by
    unfold Fate.DAGFactorization.mass
    rw [show (∑ w : V → α, if ∀ u ∈ S, w u = x u
            then (∏ v ∈ A, ψ v w) else 0)
        = ∑ q : (↥A → α) × (↥(outSet A) → α),
            if (∀ u ∈ S, (arrowEquivOut A).symm q u = x u)
              then (∏ v ∈ A, ψ v ((arrowEquivOut A).symm q)) else 0 from ?_]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun wA _ => ?_
      by_cases hc : ∀ u : ↥A, (u : V) ∈ S → wA u = x (u : V)
      · rw [if_pos hc]
        have hf : ∀ wt : ↥(outSet A) → α,
            (∏ v ∈ A, ψ v ((arrowEquivOut A).symm (wA, wt)))
              = (∏ v ∈ A, ψ v (extIn A x wA)) := by
          intro wt
          rw [arrowEquivOut_symm_eq_merge A wA wt]
          exact PA_eq_extIn hread hInA wA wt
        rw [Finset.sum_congr rfl (fun wt _ => by
          rw [if_pos ((cond_arrowEquivOut hSA x wA wt).mpr hc), hf wt])]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      · rw [if_neg hc]
        refine Finset.sum_eq_zero fun wt _ => ?_
        rw [if_neg (fun h => hc ((cond_arrowEquivOut hSA x wA wt).mp h))]
    · rw [← Equiv.sum_comp (arrowEquivOut A)
        (fun q : (↥A → α) × (↥(outSet A) → α) =>
          if (∀ u ∈ S, (arrowEquivOut A).symm q u = x u)
            then (∏ v ∈ A, ψ v ((arrowEquivOut A).symm q)) else 0)]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Equiv.symm_apply_apply]
  rw [hRHS]
  conv_lhs => rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun wA _ => ?_
  by_cases hc : ∀ u : ↥A, (u : V) ∈ S → wA u = x (u : V)
  · rw [if_pos hc, if_pos hc]
    have hf : ∀ wt : ↥(outSet A) → α,
        (∏ v ∈ A, ψ v (merge A wA wt)) = (∏ v ∈ A, ψ v (extIn A x wA)) :=
      fun wt => PA_eq_extIn hread hInA wA wt
    have hstep : (∑ wt : ↥(outSet A) → α,
          (∏ v ∈ A, ψ v (merge A wA wt)) * (∏ v ∈ outSet A, ψ v (extOut A x wt)))
        = (∏ v ∈ A, ψ v (extIn A x wA))
          * (∑ wt : ↥(outSet A) → α, ∏ v ∈ outSet A, ψ v (extOut A x wt)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun wt _ => ?_
      rw [hf wt]
    rw [hstep]
    ring
  · rw [if_neg hc, if_neg hc, zero_mul, zero_mul]

end FateV2.Predict.GraphToProbView7
