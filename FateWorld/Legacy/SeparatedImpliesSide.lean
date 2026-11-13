import FateWorld.Legacy.CliqueSideSeparable
import FateWorld.Legacy.SeparationDecomposition
import FateWorld.Legacy.CliqueDecompositionGenuine
import FateWorld.Legacy.MoralGraphMarkov
/-! 🔴🔴 **第 281 轮降级声明（U8 对抗性审核发现，含 7 个探针）**

**⚠ 本文件被我在第 279/280 轮**高估了**。U8 的评分：**评分 6/10。hxy 是死前提（可从 hUS + hxS 导出）。**

## U8 的三点裁定（逐字）

### 1. ⚠ hxy : x ≠ y 是**死前提**

> 「hxy 是可推导的，属于死前提。
> 在 `clique_not_meet_x_y` 里，由 hxS : x ∉ S 和 hUS 取 
 = 0, w ≡ x 即得矛盾。
> 在 `side_of_uns_side` 里更直接：x = y 时结论右边就是 hsub 的弱化形式。
> 在 `uns_separable_of_clique_side` 里，S = ∅ 使 hxy 同样可从 hUS 导出。」

> 「你把 hxy 当实质前提列进 D7 表，**这正是你审别人时抓的那类错误**。」

**✅ U8 是对的。我第 279/280 轮报的「3/5 假设全必要」**有误** —— hxy 是死前提。**

### 2. ⚠ uns_separable 的结论是**定义展开**

> 「DependsOnlyOn {x} F 的定义是「σ、τ 在 {x} 上一致 ⟹ F σ = F τ」。
> 而 F := ∏_{C ∈ N.filter (∀ w∈C, w=x)} ψ_C，其 hread 直接给出「只看 C ⊆ {x}」，
> 于是 DependsOnlyOn {x} **一步即得，没有任何新信息**。」

### 3. ⚠ DependsOnlyOn 的局限

> 「它是「**充分条件意义下的**只依赖」——函数可以被任意常数函数「满足」，
> 而且它**不区分**「F 由 {x} 上的某个函数因子化」与「F 恒为常数」。」

## U8 的最终判断

> 「**第 279/280 轮不应记为「缺口 1 闭合」。**
> **应记为「缺口 1 的一个 ilter 级组合，USeparated 第一次被实质用在结论里」。**
> **这比 268-272 轮强，但离「moral_factorization 形式的定理」仍差一整个 MoralFactorizes。**
> **你高估了自己，方向和上一轮一致——把「能编译的构造」当成「有内容的定理」。」**

## 真实内容

**⚠ 本文件**唯一**的真内容：USeparated 排除「团横跨」。
**⚠ 而「可分离」的构造是 ilter + 乘积的**代数事实**，不是新数学。**

**⭐⭐ 详见 `_pending/第281轮-第十次失误.md`（含新判据 D8）。**
-/


/-! ===========================================================================
  `Fate/SeparatedImpliesSide` —— **缺口 1 的最后一跳：`USeparated ⟹ Side`**（**第 279 轮**）

  ## 🎯 这是缺口 1 的**最后一块拼图**

  | 层 | 内容 | D7 |
  |---|---|---|
  | 图论 | `SeparationDecomposition` | 2 条真 |
  | 图论 | `CliqueDecompositionGenuine.clique_not_cross_A_B` | 4 假设全必要 |
  | 代数桥 | `CliqueSideSeparable.clique_side_implies_separable'` | 3 假设全必要 |
  | 概率 | `PearlCondIndepBridge.separable_implies_condMul` | 已有 |
  | **本文件** | **「`USeparated ⟹ Side`」** | 本文件 |
================================================================================ -/

namespace Fate.SeparatedImpliesSide

open Fate.MoralGraphMarkov

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## §1 **团不横跨 `x`、`y`**（`USeparated` 真正起作用） -/

/-- **`S` 分离 `{x}` 与 `{y}` ⟹ 团不能同时含 `x` 与 `y`**。

参数：`x ≠ y`、`x ∉ S`、`y ∉ S`。
证明：长度 1 的路径 `x → y`。 -/
theorem clique_not_meet_x_y
    (adj : V → V → Prop) (S : Set V) (x y : V) (C : Finset V)
    (hxS : x ∉ S) (hyS : y ∉ S)
    (hUS : USeparated adj S ({x} : Set V) ({y} : Set V))
    (hcl : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u) :
    ¬ (x ∈ C ∧ y ∈ C) := by
  rintro ⟨hxC, hyC⟩
  -- ⭐ 导出 x ≠ y：若 x = y，则 hUS 的 n = 0 路径给出 x ∈ S，矛盾
  have hxy : x ≠ y := by
    rintro rfl
    obtain ⟨i, hi⟩ := hUS 0 (fun _ => x) (Set.mem_singleton x) (Set.mem_singleton x)
      (fun j => j.elim0)
    exact hxS (by simpa using hi)
  let w : Fin 2 → V := fun i => if (i : Nat) = 0 then x else y
  have hw0 : w ⟨0, by norm_num⟩ = x := by simp [w]
  have hw1 : w ⟨1, by norm_num⟩ = y := by
    simp only [w]; norm_num
  have hw0' : w (0 : Fin 2) = x := by simpa using hw0
  have hw1' : w (1 : Fin 2) = y := by simpa using hw1
  have hadj : adj (w ⟨0, by norm_num⟩) (w ⟨1, by norm_num⟩) ∨
              adj (w ⟨1, by norm_num⟩) (w ⟨0, by norm_num⟩) := by
    rw [hw0, hw1]
    exact hcl x hxC y hyC hxy
  obtain ⟨i, hi⟩ := hUS 1 w
    (by simpa using hw0')
    (by simpa using hw1')
    (fun j => by
      have hj : (j : Nat) = 0 := by have := j.isLt; omega
      have e0 : (j.castSucc : Fin 2) = ⟨0, by norm_num⟩ := by
        ext
        simpa [Fin.val_castSucc] using hj
      have e1 : (j.succ : Fin 2) = ⟨1, by norm_num⟩ := by
        ext
        simp [Fin.val_succ, hj]
      rw [e0, e1]
      exact hadj)
  fin_cases i
  · have : x ∈ S := by simpa [w] using hi
    exact hxS this
  · have : y ∈ S := by
      simp only [w] at hi
      norm_num at hi
      exact hi
    exact hyS this

/-! ## §2 **`USeparated ⟹ Side`（含 `S`）** -/

/-- **团落在一侧**（缺口 1 的最后一跳）。

若 `S` 分离 `{x}` 与 `{y}`，`x ≠ y`，`x, y ∉ S`，
`C` 是团，且 `C ⊆ {x,y} ∪ S`，
则 `C ⊆ {x} ∪ S` 或 `C ⊆ {y} ∪ S`。 -/
theorem side_of_uns_side
    (adj : V → V → Prop) (S : Set V) (x y : V) (C : Finset V)
    (hxS : x ∉ S) (hyS : y ∉ S)
    (hUS : USeparated adj S ({x} : Set V) ({y} : Set V))
    (hcl : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u)
    (hsub : ∀ w ∈ C, w = x ∨ w = y ∨ w ∈ S) :
    (∀ w ∈ C, w = x ∨ w ∈ S) ∨ (∀ w ∈ C, w = y ∨ w ∈ S) := by
  by_cases hyC : y ∈ C
  · right
    have hne := clique_not_meet_x_y adj S x y C hxS hyS hUS hcl
    intro w hw
    rcases hsub w hw with hx' | hy' | hS
    · subst hx'
      exact absurd ⟨hw, hyC⟩ hne
    · subst hy'
      exact Or.inl rfl
    · exact Or.inr hS
  · left
    intro w hw
    rcases hsub w hw with hx' | hy' | hS
    · subst hx'
      exact Or.inl rfl
    · subst hy'
      exact absurd hw hyC
    · exact Or.inr hS

end Fate.SeparatedImpliesSide
