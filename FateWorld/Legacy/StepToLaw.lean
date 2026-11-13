/-
============================================================================
  规则核心链 · 桥路线丙（Step → LawRule）· **往返定理**（P1-1，第 722 轮）

  ## 本模块做什么

  把 `Fate/StepToLawDraft.lean` 里的三条 `example` 探针
  （P1-0 勘察中的 Q2 / Q3 / Q4）**升级为真 `theorem`**。

  `stepToLaw`（草案 `Fate/StepToLawDraft.lean`）把 `Step F` 在固定外生参数
  `(u, ν, θ, a)` 下嵌入为 `LawRule ctxPUnit F.X F.X`，逐点取 `{δ_{f x u ν θ a}}`。

  ## 本模块的定理

  | 编号 | 定理 | 前件 | 证明方式 |
  |---|---|---|---|
  | 定理 1 | `stepToLaw_isDirac` | 无 | `rfl` 级见证 `⟨f x u ν θ a, rfl⟩` |
  | 定理 2 | `toDetFun_stepToLaw` | `[MeasurableSingletonClass F.X.Carrier]` | `Classical.choose_spec` + `δ` 单射 |
  | 定理 3 | `stepToLaw_lawDetToStep` | 无（**无条件**） | `toDetFun_spec` 逐点 |
  | 定理 4 | `dirac_law_step_roundtrip` | 无 | 定理 1 + 定理 3 合并 |

  ## 诚实标注

  - 本模块**只写 theorem，不写新的 def**；`stepToLaw` 由草案模块 import。
  - 草案 `Fate/StepToLawDraft.lean` **未被修改**（保留为 P1-0 勘察证据）。
  - 零 `sorry` / 零 `admit` / 零 `axiom`。
  - ⚠ **定理 2 的 `MeasurableSingletonClass` 前件是真实的数学前提**，不是技术规避：
    `δ_y = δ_z ⟹ y = z` 在平凡 σ-代数下**不成立**（所有 Dirac 相等）。
    `Frame` 结构本身**不携带** `MeasurableSingletonClass` 实例，故本定理以
    类型类参数形式要求它 —— 这与 `Fate/LawRuleToTraj.lean` §2 已登记的
    「点分离」缺口是同一件事。
  - ⚠ **定理 3 无条件**：不涉及 `δ` 单射性（只用 `toDetFun_spec` 的等式本身）。
    故 `stepToLaw ∘ lawDetToStep = id` 比反向更松。
  - ⚠ **定理 4 的形态**：任务书给的建议签名里 `‹_›` 出现在 `∀` 绑定内，
    在 Lean 4 中不可 elaboration（`‹_›` 是已绑定实例的**回指**，不能在
    绑定器内部使用）。故本模块把「双向等价汇总」写成
    **两条无前件断言的合取**（定理 1 的 `∀` 版 + 定理 3 的 `∀` 版），
    语义上正是任务书想要的「`Dirac 规则 ⟷ Step`」的精确形式。
  - ⚠ **不声称「丙路线桥已过」**：本模块只给出 `stepToLaw` 这一**特定**嵌入
    （`PUnit` 上下文 + 固定 `(u,ν,θ,a)`）的往返；真正的桥（`Step` 与
    `TrajGen` / `trajOfLaw` 的相容等式）不在本模块范围内。
============================================================================
-/

import FateWorld.Legacy.Frame
import FateWorld.Legacy.LawRule
import FateWorld.Legacy.LawRuleToTraj
import FateWorld.Legacy.DetFunToStep
import FateWorld.Legacy.DetFunToStepDraft
import FateWorld.Legacy.StepToLawDraft

namespace Fate

open LawRule LawRuleToTraj

noncomputable section

/-! ## §1  定理 1（P1-0 的 Q2）：`stepToLaw` 是 `IsDirac`

`stepToLaw f u ν θ a` 在每个 `(c, x)` 处只允许单个分布 `{δ_{f x u ν θ a}}`，
见证就是 `f x u ν θ a` 本身。

**⟹ 这是丙路线的第一条定理：任何 `Step` 都对应一条 Dirac 规则。** -/

/-- ⭐⭐ **【`Step` 提升为 `LawRule` 后是 Dirac 型】**

`stepToLaw f u ν θ a` 是 `IsDirac`：每个 `(c, x)` 处的允许集是单点集
`{δ_{f x u ν θ a}}`。

**前件：无。** 证明是定义性的（见证就是 `f x u ν θ a`，集合相等靠 `rfl`）。 -/
theorem stepToLaw_isDirac (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX (stepToLaw F instX f u ν θ a) :=
  fun _c x => ⟨f x u ν θ a, rfl⟩

/-! ## §2  定理 2（P1-0 的 Q3）：`toDetFun ∘ stepToLaw = id`

`toDetFun` 是 `Classical.choose`，故**不是** `rfl`：
`Classical.choose_spec` 给出 `{δ_{choose}} = {δ_f}`，
再用 **`δ` 单射性**把集合等式降为点等式。

`δ` 单射性由 `dirac_inj` 提供，其前提是 `MeasurableSingletonClass`。 -/

/-- **Dirac 单射性**（局部引理，`private`，非交付定理）。

`[MeasurableSingletonClass α]` 下 `δ_y = δ_z ⟹ y = z`。

**为什么需要这个前件**：平凡 σ-代数下所有 Dirac 测度都相等，条目不真。
这是 `Fate/LawRuleToTraj.lean` 所称「点分离」的测度论形式。 -/
private lemma dirac_inj_aux {α : Type*} (m : MeasurableSpace α) [MeasurableSingletonClass α]
    {y z : α} (h : @MeasureTheory.Measure.dirac α m y = @MeasureTheory.Measure.dirac α m z) :
    y = z := by
  by_contra hne
  have hz : (@MeasureTheory.Measure.dirac α m y) ({z}ᶜ) = 0 := by
    rw [h]
    simp
  have hz2 : (@MeasureTheory.Measure.dirac α m y) ({z}ᶜ) = 1 := by
    simp [hne]
  rw [hz2] at hz
  exact one_ne_zero hz

/-- ⭐⭐⭐ **【丙路线的右侧往返：`toDetFun` 抽出 `stepToLaw` 提升的正是原 `Step`】**

`toDetFun (stepToLaw f …) h (PUnit.unit) x = f x u ν θ a`。

**前件 `[MeasurableSingletonClass F.X.Carrier]` 是必需的**：
要把 `{δ_{choose}} = {δ_f}` 降为点等式，须 `δ` 单射。
`Frame` 结构**不携带**该实例，故须显式要求 —— 这不是省略，
而是 `Measure` 依赖于 `MeasurableSpace` 的必然。 -/
theorem toDetFun_stepToLaw (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    [MeasurableSingletonClass F.X.Carrier]
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (x : F.X.Carrier) :
    @LawRuleToTraj.toDetFun ctxPUnit F.X F.X instX (stepToLaw F instX f u ν θ a)
      (stepToLaw_isDirac F instX f u ν θ a) PUnit.unit x = f x u ν θ a := by
  set hD : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX (stepToLaw F instX f u ν θ a) :=
    fun _ x => ⟨f x u ν θ a, rfl⟩
  show @LawRuleToTraj.toDetFun ctxPUnit F.X F.X instX (stepToLaw F instX f u ν θ a) hD
    PUnit.unit x = f x u ν θ a
  unfold LawRuleToTraj.toDetFun
  have hs := Classical.choose_spec (hD PUnit.unit x)
  simp only [stepToLaw] at hs
  exact dirac_inj_aux instX (Set.singleton_eq_singleton_iff.mp hs).symm

/-- ⭐ **【定理 2 的 `Step` 层形式】**：`lawDetToStep ∘ stepToLaw = id`。

即：把 `stepToLaw f …` 经 `lawDetToStep` 抽回 `Step`，再逐点应用，得到原 `f`。
这是定理 2 与 `lawDetToStep` 定义（忽略四位参数）的直接组合。

**与定理 2 的关系**：定理 2 是 `toDetFun` 层，本条是 `Step` 层。
两者前提相同（`MeasurableSingletonClass`）。 -/
theorem lawDetToStep_stepToLaw (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    [MeasurableSingletonClass F.X.Carrier]
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (x : F.X.Carrier) :
    lawDetToStep F instX (stepToLaw F instX f u ν θ a)
      (stepToLaw_isDirac F instX f u ν θ a) x u ν θ a = f x u ν θ a :=
  toDetFun_stepToLaw F instX f u ν θ a x

/-! ## §3  定理 3（P1-0 的 Q4，最核心）：`stepToLaw ∘ lawDetToStep = id`

**出发点是 `toDetFun_spec`，逐点即得**：因为 `lawDetToStep` 忽略的四位
`(u, ν, θ, a)` 恰好被 `stepToLaw` 原样灌回，而 `c` 位两处都是同一自由变量。

**重要发现**：这一向**不需要** `MeasurableSingletonClass`
（不涉及 `δ` 单射性），故反向比正向**更松**。 -/

/-- ⭐⭐⭐⭐ **【丙路线的左侧往返：`stepToLaw` 提回 `lawDetToStep` 抽出的正是原规则】**

`stepToLaw (lawDetToStep R hR) u ν θ a = R`。

**前件：无（除 `hR : IsDirac R` 这一必要的类型前提外）。**

**⟹ `IsDirac` 档的 `LawRule` 与 `Step` 之间有一个左逆**：
`LawRule(IsDirac) --lawDetToStep--> Step --stepToLaw--> LawRule(IsDirac)` 回到原点。

**⚠ 非循环性检查**：`hR` 只说「`R` 是 Dirac 型」，**不包含**任何关于
`lawDetToStep` 或 `stepToLaw` 的断言；结论是关于这两个函数的复合等式，
不是 `hR` 的展开。故**不是同义反复**。 -/
theorem stepToLaw_lawDetToStep (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (R : LawRule.LawRule ctxPUnit F.X F.X)
    (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    stepToLaw F instX (lawDetToStep F instX R hR) u ν θ a = R := by
  funext c x
  show ({MeasureTheory.Measure.dirac
      (@LawRuleToTraj.toDetFun ctxPUnit F.X F.X instX R hR c x)} :
        Set (MeasureTheory.Measure F.X.Carrier)) = R c x
  exact (LawRuleToTraj.toDetFun_spec R hR c x).symm

/-! ## §4  定理 4：双向等价的汇总

**⚠ 形态说明**：任务书建议的签名

```
(∀ R, IsDirac R → ∀ u ν θ a, stepToLaw (lawDetToStep R ‹_›) u ν θ a = R) ∧ …
```

中 `‹_›` 出现在 `∀` 的**体内部**——Lean 4 里 `‹_›` 是「回指一个已绑定的
实例局部假设」，**不能**在绑定器内凭空产生。故本模块把汇总写成
**两条无前件断言的合取**，语义与任务书一致：

1. 第一支 = 「`stepToLaw ∘ lawDetToStep = id`」在 `IsDirac` 档上逐点成立（**无条件**）；
2. 第二支 = 「任何 `Step` 提升后都是 Dirac 型」（**无条件**）。

这两支合起来正是「`Dirac 规则 ⟷ Step`」的精确形式。 -/

/-- ⭐⭐⭐⭐⭐ **【统一层的核心等价：`Dirac 规则 ⟷ Step`】**

`IsDirac` 档的 `LawRule` 与 `Step` 通过 `lawDetToStep` / `stepToLaw` 互相转换，且：

- **(1) 左逆（无条件）**：`stepToLaw (lawDetToStep R hR) u ν θ a = R`；
- **(2) 提升即 Dirac（无条件）**：`IsDirac (stepToLaw f u ν θ a)`。

**⟹ 这就是「两层本就该是同一层」的第一个精确形式。**

**⚠ 诚实标注**：反方向 `lawDetToStep (stepToLaw f …) = f`（`Step` 层等式）
**需要 `MeasurableSingletonClass`**，见定理 2 与 `lawDetToStep_stepToLaw`；
故本定理**不**把它列入无前件断言。 -/
theorem dirac_law_step_roundtrip (F : Frame) (instX : MeasurableSpace F.X.Carrier) :
    (∀ (R : LawRule.LawRule ctxPUnit F.X F.X)
        (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R),
        ∀ (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier),
          stepToLaw F instX (lawDetToStep F instX R hR) u ν θ a = R)
    ∧ (∀ (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier)
        (a : F.Act.Carrier),
          @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX (stepToLaw F instX f u ν θ a)) := by
  refine ⟨?_, ?_⟩
  · intro R hR u ν θ a
    exact stepToLaw_lawDetToStep F instX R hR u ν θ a
  · intro f u ν θ a
    exact stepToLaw_isDirac F instX f u ν θ a

end

end Fate
