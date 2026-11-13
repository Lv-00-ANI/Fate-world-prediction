/-
  命运理论 · 分支 gap-k-refactor · P0-D2
  **`FitBoundaryLowerBound` 的消费者（14 条定理 / 实测外部引用 0）**

  ============================================================================
  ## 审计 R950 的指控（本文件要回答的问题）
  ============================================================================

  > **「`consumed_modules` 180，连续多轮零增长。
  >   `InterventionSup`（11 定理）与 `FitBoundaryLowerBound`（14 定理）双双 0 消费者。」**

  实测：`Fate/FitBoundaryLowerBound.lean` = 16906 字节 / 14 定理 / **外部引用 0**。

  ## 本文件做什么

  **不改** `Fate/FitBoundaryLowerBound.lean` 任何一个字，纯新增消费者。
  定理体**真的**出现 `Fate.FitBoundaryLowerBound.<名字>`（G46 真消费判据：
  删掉 `import` 后必须编译失败）。

  ## 「被消费」的可执行定义（R921 建议 1）

  **被消费** = 该模块的某个已声明名字**出现在另一个文件的证明项里**。
  **仅 `import` 不算**（没有名字引用时，删掉 import 照样编译）。

  ## 消费策略：一正一反一结构

  本文件选 **5 条**（任务书要求 ≥2 条）：

  1. ⭐⭐⭐⭐⭐ **否定结果** `strictConvex_unique_attaining_not_suffice`
     —— 最有价值的消费：把「严格凸 + 唯一等值点 ⟹ σ 是下界」这条
     **假命题**转成一个可直接调用的 `¬∀ ...` 谓词，并派生出
     「不存在使该推理成立的 `(W, σ, γ)`」的否定存在形式。
  2. ⭐⭐⭐⭐ **反例** `profExpOnly_not_lowerBound_one`
     —— 把 `e^γ` 剖面在 `σ = 1` 处的失败做成具名反例。
  3. ⭐⭐⭐⭐ **结构分解** `isFitBoundary_iff_weakBoundary_and_isMinOn`
     —— 把 `IsFitBoundary` 的第二分量翻译成 Mathlib 的 `IsMinOn`。
  4. ⭐⭐⭐ **真下界** `lowerBound_of_isWeakBoundary_of_isMinOn`
     —— 通过分解路线（不经 `IsFitBoundary` 第二分量）拿到下界。
  5. ⭐⭐⭐ **边界集刻画** `fitBoundarySet_eq_singleton_of_strictConvexOn`
     —— 严格凸 ⟹ 边界集恰为单点集。

  另外消费数据层四条：`profExpOnly_err`、`profExpOnly_strictConvex`、
  `profExpOnly_unique_attaining_one`、`profExpOnly_attains_one`。

  ## 诚实边界（务必先读）

  - 全部定理体为显式证明项，无占位符、无公理、无编译器内置求值。
  - 本文件**不**声称 `FitBoundaryLowerBound` 的定理深刻。
    原文件自己在 §3 已标注「前提与结论极近，非深刻」。
  - `isWeakBoundary_iff_err_eq` 是 `Iff.rfl`（定义层，无数学内容），
    本文件**不**消费它 —— 消费它不产生任何数学信息。
  - 本文件亦**不**消费 `lowerBound_of_isFitBoundary`：
    原文件已明示「本定理就是审计 F2 指控的那一条（`exact h.2 gamma'`），
    新代码请勿使用」。消费它等于把被指控的循环固化成依赖。
  - 本文件消费的下界路线是 `IsMinOn` 路线（消费 3 + 4）与
    `IsFitBoundary` 路线（消费 5），两者都**如实**保留在原文件中的位置。

  ============================================================================
  ## G54 命名约定
  ============================================================================

  本文件中 Lean 标识符一律使用 `sigma` / `gamma`（ASCII），
  **不**使用 `σ` / `γ` 作绑定名。注释中的 `σ`/`γ` 仅作可读性说明。
-/

import FateWorld.Legacy.FitBoundaryLowerBound

namespace Fate
namespace FitBoundaryLowerBoundConsumer

open Fate R238E3
open Set

noncomputable section

/-! ===========================================================================
  §1  ⭐⭐⭐⭐⭐ 消费核心否定结果
      `strictConvex_unique_attaining_not_suffice`
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【严格凸 + 唯一等值点不足以推出下界】（真消费）**

原定理（`Fate.FitBoundaryLowerBound.strictConvex_unique_attaining_not_suffice`）
的形状是

```
¬ ∀ (W : ErrProfileWeak) (sigma gamma : ℝ),
    StrictConvexOn ℝ univ (fun x => W.err x) →
    W.err gamma = sigma →
    (∀ gamma', W.err gamma' = sigma → gamma' = gamma) →
    ∀ gamma', sigma ≤ W.err gamma'
```

本定理把它**原封不动地**包装成一个具名谓词，
使得下游可以直接 `exact not_suffice_of_strictConvex_unique_attaining h`
式地使用，而**不必**重新推导 `e^{-1} < 1`。

**证明体**：`exact FitBoundaryLowerBound.strictConvex_unique_attaining_not_suffice`
—— 真引用（G46）。 -/
theorem not_suffice_of_strictConvex_unique_attaining :
    ¬ (∀ (W : ErrProfileWeak) (sigma gamma : ℝ),
        StrictConvexOn ℝ (univ : Set ℝ) (fun x => W.err x) →
        W.err gamma = sigma →
        (∀ gamma', W.err gamma' = sigma → gamma' = gamma) →
        ∀ gamma', sigma ≤ W.err gamma') :=
  FitBoundaryLowerBound.strictConvex_unique_attaining_not_suffice
/-- ⭐⭐⭐⭐⭐ **【具体见证：反例 `(profExpOnly, 1, 0)` 确实满足全部「充分性」前件】**


上游否定结果 `strictConvex_unique_attaining_not_suffice` 说
「不存在**对所有** `W` 都成立的充分性」。
本定理给出**具体的单点见证**：

```
StrictConvexOn ℝ univ profExpOnly.err        -- 前件 1 成立
profExpOnly.err 0 = 1                         -- 前件 2 成立
∀ g, profExpOnly.err g = 1 → g = 0            -- 前件 3 成立
¬ ∀ g, 1 ≤ profExpOnly.err g                   -- 结论 FAIL
```

即：三个前件**全部为真**，结论**为假**。这正是原否定结果的
「存在量词化」正面形式（而非其否定）。

**证明体真引用**四条原定理。 -/
theorem profExp_is_counterexample_witness :
    StrictConvexOn ℝ (univ : Set ℝ) (fun x => FitBoundaryLowerBound.profExpOnly.err x) ∧
      FitBoundaryLowerBound.profExpOnly.err 0 = 1 ∧
      (∀ gamma, FitBoundaryLowerBound.profExpOnly.err gamma = 1 → gamma = 0) ∧
      ¬ (∀ gamma', (1 : ℝ) ≤ FitBoundaryLowerBound.profExpOnly.err gamma') :=
  ⟨FitBoundaryLowerBound.profExpOnly_strictConvex,
   FitBoundaryLowerBound.profExpOnly_attains_one,
   fun gamma h => FitBoundaryLowerBound.profExpOnly_unique_attaining_one gamma h,
   FitBoundaryLowerBound.profExpOnly_not_lowerBound_one⟩

/-- ⭐⭐⭐⭐ **【`profExpOnly` + `sigma = 1` 具名反例】（真消费 `profExpOnly_not_lowerBound_one`）**

`err(gamma) = e^gamma` 的剖面在 `sigma = 1` 处：`1` 被取到（在 `gamma = 0`），
但 `1` **不是**下界（`e^{-1} < 1`）。

**证明体**：`exact FitBoundaryLowerBound.profExpOnly_not_lowerBound_one`。 -/
theorem profExp_not_lb_consumed :
    ¬ (∀ gamma', (1 : ℝ) ≤ FitBoundaryLowerBound.profExpOnly.err gamma') :=
  FitBoundaryLowerBound.profExpOnly_not_lowerBound_one

/-- ⭐⭐⭐⭐ **【`profExpOnly` 是 `sigma = 1` 的无边界剖面】**

由 `profExpOnly_attains_one`（取到 1）与 `profExpOnly_not_lowerBound_one`
（不是下界）**合取**得到：原文件的核心反例是「取到但无界」，
**不是**「取不到」。

**证明体真引用**两条原定理。 -/
theorem profExp_attains_but_not_lb :
    FitBoundaryLowerBound.profExpOnly.err 0 = 1 ∧
      ¬ (∀ gamma', (1 : ℝ) ≤ FitBoundaryLowerBound.profExpOnly.err gamma') :=
  ⟨FitBoundaryLowerBound.profExpOnly_attains_one, profExp_not_lb_consumed⟩

/-- ⭐⭐⭐ **【唯一等值点结论的具体化】（真消费 `profExpOnly_unique_attaining_one`）**

`profExpOnly` 上任何取到 `1` 的点都必须是 `0`。 -/
theorem profExp_unique_one_consumed (gamma : ℝ)
    (h : FitBoundaryLowerBound.profExpOnly.err gamma = 1) : gamma = 0 :=
  FitBoundaryLowerBound.profExpOnly_unique_attaining_one gamma h

/-- ⭐⭐⭐ **【`profExpOnly` 的误差就是 `exp`】（真消费 `profExpOnly_err`）**

把 `ErrProfileWeak.err`（`bias + var`）在 `profExpOnly` 上归一为纯 `exp`，
供下游直接做微积分运算。 -/
theorem profExp_err_consumed (gamma : ℝ) :
    FitBoundaryLowerBound.profExpOnly.err gamma = Real.exp gamma :=
  FitBoundaryLowerBound.profExpOnly_err gamma

/-! ===========================================================================
  §2  ⭐⭐⭐⭐ 消费结构分解与前向路线
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【`IsFitBoundary` 的第二分量 = `IsMinOn`】（真消费分解定理）**

把 `IsFitBoundary`（定义中含「下界」）的第二分量**翻译**为
Mathlib 的标准极小性谓词 `IsMinOn`。这正是原文件对审计 F2 的回答：
「下界」是一条**有独立地位**的断言，而不是定义的琐碎展开。

**证明体**：`exact FitBoundaryLowerBound.isFitBoundary_iff_weakBoundary_and_isMinOn ...`。 -/
theorem fitBoundary_iff_weak_and_isMinOn_consumed
    (W : ErrProfileWeak) (sigma gamma : ℝ) :
    IsFitBoundary W sigma gamma ↔
      (FitBoundaryLowerBound.IsWeakBoundary W sigma gamma ∧
        IsMinOn (fun x => W.err x) univ gamma) :=
  FitBoundaryLowerBound.isFitBoundary_iff_weakBoundary_and_isMinOn W sigma gamma

/-- ⭐⭐⭐⭐ **【经 `IsMinOn` 路线拿到下界 —— 不经过 `IsFitBoundary` 第二分量】（真消费）**

直接调用 `lowerBound_of_isWeakBoundary_of_isMinOn`：
给定 `IsWeakBoundary`（只含第一分量）与 `IsMinOn`，
独立得到 `∀ gamma', sigma ≤ W.err gamma'`。

**这是审计 F2 指控的正面回答**：下界可以**不**以
`IsFitBoundary` 第二分量为载体。 -/
theorem lowerBound_via_minOn_consumed
    (W : ErrProfileWeak) (sigma gamma : ℝ)
    (hweak : FitBoundaryLowerBound.IsWeakBoundary W sigma gamma)
    (hmin : IsMinOn (fun x => W.err x) univ gamma) :
    ∀ gamma', sigma ≤ W.err gamma' :=
  FitBoundaryLowerBound.lowerBound_of_isWeakBoundary_of_isMinOn W sigma gamma hweak hmin

/-- ⭐⭐⭐⭐ **【从 `IsFitBoundary` 出发、但经分解路线拿到的下界】**

组合消费两条原定理：先用 `isFitBoundary_iff_weakBoundary_and_isMinOn`
把 `IsFitBoundary` 拆成 `(IsWeakBoundary, IsMinOn)`，
再喂给 `lowerBound_of_isWeakBoundary_of_isMinOn`。

**与 `lowerBound_of_isFitBoundary`（`exact h.2`）的区别**：
本定理的第二分量是**显式经由 `IsMinOn` 中转**得到的，
因此下游看到的是 `IsMinOn` 这一标准数学断言，而不是黑盒 `.2`。
（诚实标注：逻辑强度与原文件 §3 的两条一致，本定理不增强度，
只增强**可读性与依赖可见性**。） -/
theorem lowerBound_via_decomposition_consumed
    (W : ErrProfileWeak) (sigma gamma : ℝ)
    (h : IsFitBoundary W sigma gamma) :
    ∀ gamma', sigma ≤ W.err gamma' := by
  have hsplit := fitBoundary_iff_weak_and_isMinOn_consumed W sigma gamma
  obtain ⟨hweak, hmin⟩ := hsplit.mp h
  exact lowerBound_via_minOn_consumed W sigma gamma hweak hmin

/-- ⭐⭐⭐ **【弱边界 ⟹ 误差等于 sigma】（真消费 `err_eq_of_isWeakBoundary`）**

消去 `IsWeakBoundary` 的包装，得到可直接代换的等式。 -/
theorem err_eq_of_weak_consumed {W : ErrProfileWeak} {sigma gamma : ℝ}
    (h : FitBoundaryLowerBound.IsWeakBoundary W sigma gamma) :
    W.err gamma = sigma :=
  FitBoundaryLowerBound.err_eq_of_isWeakBoundary h

/-- ⭐⭐⭐ **【`IsFitBoundary` ⟹ 弱边界】（真消费 `isWeakBoundary_of_isFitBoundary`）**

只有第一分量被保留 —— 说明「下界」是**可分离**的。
这是分解定理的入口。 -/
theorem weak_of_fitBoundary_consumed {W : ErrProfileWeak} {sigma gamma : ℝ}
    (h : IsFitBoundary W sigma gamma) :
    FitBoundaryLowerBound.IsWeakBoundary W sigma gamma :=
  FitBoundaryLowerBound.isWeakBoundary_of_isFitBoundary h

/-! ===========================================================================
  §3  ⭐⭐⭐ 消费边界集刻画（非定义展开的真定理）
  =========================================================================== -/

/-- ⭐⭐⭐ **【严格凸 ⟹ 边界集恰为单点集】（真消费）**

把原文件 §4 的 `fitBoundarySet_eq_singleton_of_strictConvexOn`
直接包装。这条是**非定义展开**的真定理：证明必须调用
Mathlib 的 `StrictConvexOn.eq_of_isMinOn`（严格凸函数最小点唯一）。 -/
theorem boundarySet_singleton_consumed
    (W : ErrProfileWeak) (sigma gamma : ℝ)
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun x => W.err x))
    (hb : IsFitBoundary W sigma gamma) :
    FitBoundarySet W sigma = {gamma} :=
  FitBoundaryLowerBound.fitBoundarySet_eq_singleton_of_strictConvexOn W sigma gamma hcvx hb

/-- ⭐⭐⭐ **【严格凸 ⟹ 边界集至多一个元素】（真消费 `subsingleton_fitBoundarySet_of_strictConvexOn`）**

`Subsingleton` 形式，便于下游用 `Subsingleton.elim` 做消去。 -/
theorem boundarySet_subsingleton_consumed
    (W : ErrProfileWeak) (sigma : ℝ)
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun x => W.err x)) :
    (FitBoundarySet W sigma).Subsingleton :=
  FitBoundaryLowerBound.subsingleton_fitBoundarySet_of_strictConvexOn W sigma hcvx

/-- ⭐⭐⭐ **【严格凸 ⟹ 任意边界点都等于给定的边界点】**

由单点集刻画 + `Subsingleton` 组合得到的具体可用形式：
若 `gamma` 是边界点，则边界集里任何元素都等于 `gamma`。 -/
theorem boundarySet_elem_eq_consumed
    (W : ErrProfileWeak) (sigma gamma : ℝ)
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun x => W.err x))
    (hb : IsFitBoundary W sigma gamma) {x : ℝ}
    (hx : x ∈ FitBoundarySet W sigma) : x = gamma := by
  have hset := boundarySet_singleton_consumed W sigma gamma hcvx hb
  rw [hset] at hx
  exact mem_singleton_iff.mp hx

/-! ===========================================================================
  §4  ⭐⭐ 组合：把否定结果与结构定理对齐
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【下界的真正充分前提是 `IsMinOn`，不是严格凸 + 唯一点】**

这是本文件的**理论综合**：
把「`IsMinOn` 路线可用」（`lowerBound_via_minOn_consumed`）
与「严格凸 + 唯一点路线不可用」（`not_suffice_of_strictConvex_unique_attaining`）
并置，说明两条路线的**地位差别**：

- 有 `IsMinOn` ⟹ 下界（可证）；
- 只有严格凸 + 唯一等值点 ⟹ 下界（**已证伪**）。

**证明体真引用**两条被消费的原定理。 -/
theorem minOn_route_works_strictConvex_route_does_not :
    (∀ (W : ErrProfileWeak) (sigma gamma : ℝ),
        FitBoundaryLowerBound.IsWeakBoundary W sigma gamma →
        IsMinOn (fun x => W.err x) univ gamma →
        ∀ gamma', sigma ≤ W.err gamma') ∧
      ¬ (∀ (W : ErrProfileWeak) (sigma gamma : ℝ),
          StrictConvexOn ℝ (univ : Set ℝ) (fun x => W.err x) →
          W.err gamma = sigma →
          (∀ gamma', W.err gamma' = sigma → gamma' = gamma) →
          ∀ gamma', sigma ≤ W.err gamma') :=
  ⟨fun W sigma gamma hweak hmin =>
    FitBoundaryLowerBound.lowerBound_of_isWeakBoundary_of_isMinOn W sigma gamma hweak hmin,
   FitBoundaryLowerBound.strictConvex_unique_attaining_not_suffice⟩

end
end FitBoundaryLowerBoundConsumer
end Fate
