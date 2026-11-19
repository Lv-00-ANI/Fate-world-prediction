import FateWorld.FateV2.Predict.SeparatedImpliesSide
import FateWorld.FateV2.Predict.CliqueSideSeparable
import FateWorld.FateV2.Predict.PearlCondIndepBridge
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
/-!
  # Predict · SeparatedCondMul

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SeparatedCondMul.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SeparatedImpliesSide, CliqueSideSeparable, PearlCondIndepBridge, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! 🔴🔴 **第 281 轮降级声明（U8 对抗性审核发现，含 7 个探针）**

**⚠ 本文件被我在第 279/280 轮**高估了**。U8 的评分：**评分 5/10。结论的「可分离」是 ilter 定义展开；hxy 是死前提。**

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
  `Fate/SeparatedCondMul` —— 缺口 1 的终点：`USeparated ⟹ 可分离`（第 280 轮）

  ## 四层合成

  | # | 层 | 定理 | D7 |
  |---|---|---|---|
  | 1 | 图论 | `SeparatedImpliesSide.side_of_uns_side` | 3 假设全必要 |
  | 2 | 代数桥 | `CliqueSideSeparable.clique_side_implies_separable'` | 3 假设全必要 |
  | 3 | 概率 | `PearlCondIndepBridge.separable_implies_condMul` | 已有 |
  | 4 | 合成 | 本文件 | 本文件 |

  ## 关键推理洞察

  一开始我想用 hsub（每个团点都在 {x,y} 里）直接推出「团不横跨」，
  但这是**错的** —— hsub 只说每个点是 x 或 y，允许团同时含 x 与 y。

  正是 USeparated（经 side_of_uns_side）排除了「团横跨」这一情形。
  故本定理**必须**用 hUS —— 这正是缺口 1 的核心。
================================================================================ -/

namespace FateV2.Predict.SeparatedCondMul

open FateV2.Modeling

open FateV2.Predict.FinCondIndep
open FateV2.Modeling.MoralGraphMarkov
open FateV2.Predict.SeparatedImpliesSide

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## §1 `S = ∅` 时团落一侧 -/

/-- `S = ∅` 时团落一侧（不含 S）。由 `side_of_uns_side` 特化。 -/
theorem side_empty_of_uns
    (adj : V → V → Prop) (x y : V) (C : Finset V)
    (hUS : USeparated adj (∅ : Set V) ({x} : Set V) ({y} : Set V))
    (hcl : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u)
    (hsub : ∀ w ∈ C, w = x ∨ w = y) :
    (∀ w ∈ C, w = x) ∨ (∀ w ∈ C, w = y) := by
  have h := side_of_uns_side adj (∅ : Set V) x y C (Set.notMem_empty x) (Set.notMem_empty y) hUS hcl
    (fun w hw => by
      rcases hsub w hw with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h'))
  rcases h with h | h
  · left
    intro w hw
    rcases h w hw with hx | hS
    · exact hx
    · exact absurd hS (by simp)
  · right
    intro w hw
    rcases h w hw with hy | hS
    · exact hy
    · exact absurd hS (by simp)

/-! ## §2 缺口 1 的终点：`USeparated ⟹ 可分离`（`S = ∅`） -/

/-- `USeparated ⟹ 可分离`（缺口 1 的合成）。

- `p` 按团分解 `p = ∏_{C∈N} ψ_C`（`hp`）
- 每个 `ψ_C` 只读 `C`（`hread`）
- 每个团 `C ∈ N` 是团（`hcl`）、点都在 `{x,y}` 里（`hsub`）
- `USeparated adj ∅ {x} {y}`，`x ≠ y`

则 `p` 可分离为 `F(x)·G(y)`。 -/
theorem uns_separable_of_clique_side
    (adj : V → V → Prop) (x y : V)
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hUS : USeparated adj (∅ : Set V) ({x} : Set V) ({y} : Set V))
    (hcl : ∀ C ∈ N, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u)
    (hsub : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y)
    (hread : ∀ C, ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (p : (V → V) → ℝ)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn {x} F
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn {y} G := by
  classical
  refine ⟨fun σ => ∏ C ∈ N.filter (fun C => ∀ w ∈ C, w = x), ψ C σ,
          fun σ => ∏ C ∈ N.filter (fun C => ¬ ∀ w ∈ C, w = x), ψ C σ, ?_, ?_, ?_⟩
  · intro σ
    rw [hp σ]
    exact (Finset.prod_filter_mul_prod_filter_not N (fun C => ∀ w ∈ C, w = x)
      (fun C => ψ C σ)).symm
  · -- F 只依赖 {x}
    intro σ τ hagree
    exact FateV2.Predict.CliqueSideSeparable.prod_dependsOn (S := ({x} : Finset V)) hread
      (fun C hC w hw => by
        have hw_x : w = x := (Finset.mem_filter.mp hC).2 w hw
        rw [hw_x]
        exact Finset.mem_singleton_self x) σ τ hagree
  · -- G 只依赖 {y}
    intro σ τ hagree
    exact FateV2.Predict.CliqueSideSeparable.prod_dependsOn (S := ({y} : Finset V)) hread
      (fun C hC w hw => by
        have hCN : C ∈ N := (Finset.mem_filter.mp hC).1
        have hnotx : ¬ (∀ w ∈ C, w = x) := (Finset.mem_filter.mp hC).2
        have hside := side_empty_of_uns adj x y C hUS (hcl C hCN) (hsub C hCN)
        have hall : ∀ w ∈ C, w = y := by
          rcases hside with hx | hy
          · exact absurd hx hnotx
          · exact hy
        rw [hall w hw]
        exact Finset.mem_singleton_self y) σ τ hagree

end FateV2.Predict.SeparatedCondMul
