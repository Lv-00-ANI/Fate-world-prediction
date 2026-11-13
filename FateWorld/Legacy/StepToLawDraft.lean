/-
============================================================================
  规则核心链 · 桥路线丙（Step → LawRule）· **可行性勘察草案**
  （第 721 轮，P1-0）

  ⚠⚠ **本文件不是桥定理，只有 def 草案 + 三条 `example` 探针。**

  目的：确认「`Step F` 能否机械地嵌入 `LawRule ctxPUnit F.X F.X`，
        并且往返（round-trip）是否成立」这一**类型层 + 定义层**问题。

  结论见 `_audit/P1-0-Step到LawRule可行性勘察.md`：
  · Q1 🟢  `stepToLaw` 草案编译通过（`instX` 显式传入，其余 5 位全用上）
  · Q2 🟢  `IsDirac (stepToLaw …)` 直接成立（`rfl` 级见证）
  · Q3 🟡  `toDetFun (stepToLaw …) … = f …` 成立，**但需要 `MeasurableSingletonClass F.X.Carrier`**
          （δ 单射性；`Measure` 在 `MeasurableSpace` 上是**依赖**的，故 `instX` 必须显式传递）
  · Q4 🟢  `stepToLaw (lawDetToStep R hR) u ν θ a = R` **无条件成立**（不需要点分离！）

  **诚实标注**：
  - 本文件**不含任何 `theorem`**，只有 `def` + `example`；
  - 故**不声称「丙路线桥已过」**，只声称上述四条形状 / 等式事实；
  - `example` 不是定理，不进库、不被下游引用；
  - 真正的桥引理（`Step` 与 `TrajGen` / `trajOfLaw` 的相容等式）留给后续轮次。
============================================================================
-/

import FateWorld.Legacy.Frame
import FateWorld.Legacy.LawRule
import FateWorld.Legacy.LawRuleToTraj
import FateWorld.Legacy.DetFunToStepDraft

namespace Fate

open LawRule LawRuleToTraj

noncomputable section

/-! ## §1  `Step → LawRule`（Q1 的 def 草案）

`Step F := F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier → F.Act.Carrier
            → F.X.Carrier`
（`Fate/Frame.lean:146`）

`LawRule ctxPUnit F.X F.X := PUnit → F.X.Carrier → Set (Measure F.X.Carrier)`
（`Fate/LawRule.lean:65`）

嵌入方式：给定**一组** `(u, ν, θ, a)`（把它们当**外生参数固定**），
把 `PUnit` 上下文忽略，逐点取 `{δ_{f x u ν θ a}}`。

**注意 `instX` 必须显式传入**：`LawRule C X Y` 的 `[MeasurableSpace Y.Carrier]`
是类型类位置，但 `F.X.meas` 是 `StateSpace` 的**字段**，
Lean 不会自动把它提升为类型类实例 —— 这是 `lawDetToStep` 里已登记的同一细节。 -/

/-- ⭐ **【Step → LawRule】草案（丙路线的 A 端）**

把单步函数 `f` 在固定外生参数 `(u, ν, θ, a)` 下，嵌入为一条
「`PUnit` 上下文 + Dirac 单点」的规律。 -/
def stepToLaw (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    LawRule.LawRule ctxPUnit F.X F.X :=
  fun _c x => {MeasureTheory.Measure.dirac (f x u ν θ a)}

/-! ## §2  Q2：`stepToLaw` 是 `IsDirac`

见证逐点就是 `f x u ν θ a` 本身，故 `rfl` 级 —— **不需要任何额外前提**。 -/

example (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX (stepToLaw F instX f u ν θ a) :=
  fun _ x => ⟨f x u ν θ a, rfl⟩

/-! ## §3  Q3：往返 `toDetFun (stepToLaw f) = f`

`toDetFun` 是 `Classical.choose`，故**不是 `rfl`**：
须 `Classical.choose_spec` 给出 `{δ_{choose}} = {δ_{f}}`，
再用 **`δ` 单射性** 把集合等式降为点等式。

**⚠ 关键缺口（登记为 Q3 的充要附加前提）**：
`δ_y = δ_z ⟹ y = z` **并非**无条件成立 —— 平凡 σ-代数下所有 Dirac 都相等。
本勘察实测：`MeasureTheory.Measure.dirac_inj` / `dirac_injective` 等名称
在本项目所用 Mathlib 版本中**均不存在**，故本文件内联一个局部引理
`dirac_inj_local`（`private`，**不是交付定理**），其前提是
`[MeasurableSingletonClass F.X.Carrier]`（这正是 `LawRuleToTraj.lean:176` 已声明的「点分离」）。 -/

/-- **局部探针**（`private`，非交付）：Dirac 单射性。
前提 `MeasurableSingletonClass` 即 `LawRuleToTraj.lean` 所称「点分离」。 -/
private lemma dirac_inj_local {α : Type*} (m : MeasurableSpace α) [MeasurableSingletonClass α]
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

example (F : Frame) (instX : MeasurableSpace F.X.Carrier) [MeasurableSingletonClass F.X.Carrier]
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (x : F.X.Carrier) :
    @LawRuleToTraj.toDetFun ctxPUnit F.X F.X instX
      (stepToLaw F instX f u ν θ a)
      (fun _ x => ⟨f x u ν θ a, rfl⟩) PUnit.unit x
    = f x u ν θ a := by
  set hD : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX (stepToLaw F instX f u ν θ a) :=
    fun _ x => ⟨f x u ν θ a, rfl⟩ with hDdef
  show @LawRuleToTraj.toDetFun ctxPUnit F.X F.X instX (stepToLaw F instX f u ν θ a) hD PUnit.unit x
    = f x u ν θ a
  unfold LawRuleToTraj.toDetFun
  have hs := Classical.choose_spec (hD PUnit.unit x)
  simp only [stepToLaw] at hs
  exact dirac_inj_local instX (Set.singleton_eq_singleton_iff.mp hs).symm

/-! ## §4  Q4 反向：`stepToLaw (lawDetToStep R hR) u ν θ a = R`

**出发点是 `toDetFun_spec`，逐点即得** —— 因为 `lawDetToStep` 忽略的四位
`(u, ν, θ, a)` 恰好被 `stepToLaw` 原样灌回，而 `c` 位两处都是同一自由变量。

**重要发现**：这一向**不需要** `MeasurableSingletonClass`（不涉及 `δ` 单射性），
故反向比正向**更松**。 -/

example (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (R : LawRule.LawRule ctxPUnit F.X F.X)
    (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    stepToLaw F instX (lawDetToStep F instX R hR) u ν θ a = R := by
  funext c x
  show ({MeasureTheory.Measure.dirac
      (@LawRuleToTraj.toDetFun ctxPUnit F.X F.X instX R hR c x)} :
        Set (MeasureTheory.Measure F.X.Carrier)) = R c x
  exact (LawRuleToTraj.toDetFun_spec R hR c x).symm

end

end Fate
