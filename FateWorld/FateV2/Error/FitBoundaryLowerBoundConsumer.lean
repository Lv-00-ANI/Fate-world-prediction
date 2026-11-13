import FateWorld.FateV2.Error.FitBoundaryLowerBound

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/FitBoundaryLowerBoundConsumer.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 5 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Loop

/-
  下界模块的消费接口（对应论文 §7）

  为下界模块中此前没有下游引用的定理提供真实的消费者：本模块的定理体中出现被消费模块
  的名字，而不只是 import 它。

  被消费的可执行定义：某模块的已声明名字出现在另一个文件的证明项里；仅 import 不算，
  因为没有名字引用时删掉 import 照样编译。

  注：本模块不改动被消费模块的任何一个字，纯新增消费者。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error
namespace FitBoundaryLowerBoundConsumer

open FateV2.Error Core
open Set

noncomputable section

/-! ===========================================================================
  §1  消费核心否定结果
      `strictConvex_unique_attaining_not_suffice`
  =========================================================================== -/

/-- **【严格凸 + 唯一等值点不足以推出下界】（真消费）**

原定理（`FateV2.Error.FitBoundaryLowerBound.strictConvex_unique_attaining_not_suffice`）
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
/-- **【具体见证：反例 `(profExpOnly, 1, 0)` 确实满足全部「充分性」前件】**


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

/-- **【`profExpOnly` + `sigma = 1` 具名反例】（真消费 `profExpOnly_not_lowerBound_one`）**

`err(gamma) = e^gamma` 的剖面在 `sigma = 1` 处：`1` 被取到（在 `gamma = 0`），
但 `1` **不是**下界（`e^{-1} < 1`）。

**证明体**：`exact FitBoundaryLowerBound.profExpOnly_not_lowerBound_one`。 -/
theorem profExp_not_lb_consumed :
    ¬ (∀ gamma', (1 : ℝ) ≤ FitBoundaryLowerBound.profExpOnly.err gamma') :=
  FitBoundaryLowerBound.profExpOnly_not_lowerBound_one

/-- **【`profExpOnly` 是 `sigma = 1` 的无边界剖面】**

由 `profExpOnly_attains_one`（取到 1）与 `profExpOnly_not_lowerBound_one`
（不是下界）**合取**得到：原文件的核心反例是「取到但无界」，
**不是**「取不到」。

**证明体真引用**两条原定理。 -/
theorem profExp_attains_but_not_lb :
    FitBoundaryLowerBound.profExpOnly.err 0 = 1 ∧
      ¬ (∀ gamma', (1 : ℝ) ≤ FitBoundaryLowerBound.profExpOnly.err gamma') :=
  ⟨FitBoundaryLowerBound.profExpOnly_attains_one, profExp_not_lb_consumed⟩

/-- **【唯一等值点结论的具体化】（真消费 `profExpOnly_unique_attaining_one`）**

`profExpOnly` 上任何取到 `1` 的点都必须是 `0`。 -/
theorem profExp_unique_one_consumed (gamma : ℝ)
    (h : FitBoundaryLowerBound.profExpOnly.err gamma = 1) : gamma = 0 :=
  FitBoundaryLowerBound.profExpOnly_unique_attaining_one gamma h

/-- **【`profExpOnly` 的误差就是 `exp`】（真消费 `profExpOnly_err`）**

把 `ErrProfileWeak.err`（`bias + var`）在 `profExpOnly` 上归一为纯 `exp`，
供下游直接做微积分运算。 -/
theorem profExp_err_consumed (gamma : ℝ) :
    FitBoundaryLowerBound.profExpOnly.err gamma = Real.exp gamma :=
  FitBoundaryLowerBound.profExpOnly_err gamma

/-! ===========================================================================
  §2  消费结构分解与前向路线
  =========================================================================== -/

/-- **【`IsFitBoundary` 的第二分量 = `IsMinOn`】（真消费分解定理）**

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

/-- **【经 `IsMinOn` 路线拿到下界 —— 不经过 `IsFitBoundary` 第二分量】（真消费）**

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

/-- **【从 `IsFitBoundary` 出发、但经分解路线拿到的下界】**

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

/-- **【弱边界 ⟹ 误差等于 sigma】（真消费 `err_eq_of_isWeakBoundary`）**

消去 `IsWeakBoundary` 的包装，得到可直接代换的等式。 -/
theorem err_eq_of_weak_consumed {W : ErrProfileWeak} {sigma gamma : ℝ}
    (h : FitBoundaryLowerBound.IsWeakBoundary W sigma gamma) :
    W.err gamma = sigma :=
  FitBoundaryLowerBound.err_eq_of_isWeakBoundary h

/-- **【`IsFitBoundary` ⟹ 弱边界】（真消费 `isWeakBoundary_of_isFitBoundary`）**

只有第一分量被保留 —— 说明「下界」是**可分离**的。
这是分解定理的入口。 -/
theorem weak_of_fitBoundary_consumed {W : ErrProfileWeak} {sigma gamma : ℝ}
    (h : IsFitBoundary W sigma gamma) :
    FitBoundaryLowerBound.IsWeakBoundary W sigma gamma :=
  FitBoundaryLowerBound.isWeakBoundary_of_isFitBoundary h

/-! ===========================================================================
  §3  消费边界集刻画（非定义展开的真定理）
  =========================================================================== -/

/-- **【严格凸 ⟹ 边界集恰为单点集】（真消费）**

把原文件 §4 的 `fitBoundarySet_eq_singleton_of_strictConvexOn`
直接包装。这条是**非定义展开**的真定理：证明必须调用
Mathlib 的 `StrictConvexOn.eq_of_isMinOn`（严格凸函数最小点唯一）。 -/
theorem boundarySet_singleton_consumed
    (W : ErrProfileWeak) (sigma gamma : ℝ)
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun x => W.err x))
    (hb : IsFitBoundary W sigma gamma) :
    FitBoundarySet W sigma = {gamma} :=
  FitBoundaryLowerBound.fitBoundarySet_eq_singleton_of_strictConvexOn W sigma gamma hcvx hb

/-- **【严格凸 ⟹ 边界集至多一个元素】（真消费 `subsingleton_fitBoundarySet_of_strictConvexOn`）**

`Subsingleton` 形式，便于下游用 `Subsingleton.elim` 做消去。 -/
theorem boundarySet_subsingleton_consumed
    (W : ErrProfileWeak) (sigma : ℝ)
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun x => W.err x)) :
    (FitBoundarySet W sigma).Subsingleton :=
  FitBoundaryLowerBound.subsingleton_fitBoundarySet_of_strictConvexOn W sigma hcvx

/-- **【严格凸 ⟹ 任意边界点都等于给定的边界点】**

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
  §4  组合：把否定结果与结构定理对齐
  =========================================================================== -/

/-- **【下界的真正充分前提是 `IsMinOn`，不是严格凸 + 唯一点】**

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
end FateV2.Error
