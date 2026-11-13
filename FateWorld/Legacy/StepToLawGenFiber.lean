/-
============================================================================
  规则核心链 · 桥路线丙 · **抽象版左往返的纤维形式**（P0-5 修复）

  ## 本模块为什么存在

  `Fate/StepToLawGen.lean`（P0-5 初稿）声称

  > 定理 3：`stepToLawGen (lawDetToStepGen R hR) u ν θ a = R`（**无条件**）。

  **这个断言是假的，实测编译失败**（第 725 轮）：

  ```
  Fate/StepToLawGen.lean:209:2: error: Tactic `rfl` failed
    {MeasureTheory.Measure.dirac (toDetFun R hR (ctxOf x u ν θ a) x)}
  is not definitionally equal to
    R c x
  ```

  ## 根因（真实的数学发现，不是证明技巧问题）

  * `stepToLawGen F instX ctxOf f u ν θ a` 的定义**完全不使用 `ctxOf`**：
    `fun c x => {δ_{f x u ν θ a}}`。它给出的 `LawRule` 对**每个** `c` 都返回
    同一个单点集。
  * 因此 `stepToLawGen (lawDetToStepGen R hR) u ν θ a c x` 的值是
    `{δ_{toDetFun R hR (ctxOf x u ν θ a) x}}` —— 用的是 **`ctxOf x u ν θ a`**。
  * 而目标是 `R c x = {δ_{toDetFun R hR c x}}`（`toDetFun_spec`）—— 用的是 **`c`**。
  * 只有在 `ctxOf x u ν θ a = c` 时两者才相等。

  **⟹ 抽象版左往返不是无条件成立的。**

  ## 精确边界

  * **静态版（`Fate/StepToLaw.lean`，`C := ctxPUnit := ⟨PUnit⟩`）**：
    `PUnit` 只有一个元素，`ctxOf x u ν θ a = PUnit.unit = c` **自动成立**
    ⟹ 无条件版本**是真的**（已编译通过的 `stepToLaw_lawDetToStep`）。
  * **抽象版**：`Step F` 只带**一条**上下文（由 `ctxOf x u ν θ a` 算出），
    而 `LawRule C F.X F.X` 在**每个** `c : C.Carrier` 上都有值。
    `Step → LawRule → Step` 的复合丢失了 `LawRule` 的上下文维度
    ⟹ 左往返只能**逐纤维**成立。

  **⟹ 这是总纲 §8.3 假说的精确边界**：
  > 「两层是同一层」在**静态上下文**下全局成立；
  > 在**抽象上下文**下只成立在**固定上下文的纤维**上。

  ## 本模块的定理

  1. `stepToLawGen_apply`（定义展开，`rfl`）
  2. `stepToLawGen_isDirac`（无前件）
  3. **`stepToLawGen_lawDetToStepGen_at`**：`ctxOf x u ν θ a = c` ⟹ 点等式
     `stepToLawGen (lawDetToStepGen R hR) u ν θ a c x = R c x`
  4. **`stepToLawGen_lawDetToStepGen_fiber`**：`∀ x, ctxOf x u ν θ a = c₀` ⟹
     函数等式 `stepToLawGen (lawDetToStepGen R hR) u ν θ a = fun _ x => R c₀ x`
  5. `stepToLawGen_lawDetToStepGen_global`：若 `R` 不依赖上下文
     （`∀ c c', R c = R c'`）且 `ctxOf` 在给定输入下是常数，则全局互逆
  6. `stepToLawGen_lawDetToStep_static`：**静态特例**（`C := ctxPUnit`），
     恢复 `Fate/StepToLaw.lean` 的无条件结论形态
  7. `lawDetToStepGen_stepToLawGen`（右往返，点分离，**无需 `ctxOf` 纤维性**）
  8. `dirac_law_step_roundtrip_gen_fiber`：纤维上的双向等价汇总

  ## 前件非循环（自查）

  - 定理 3 的前件 `hctx : ctxOf x u ν θ a = c` 是**上下文对齐**，
    不含任何关于 `stepToLawGen` / `lawDetToStepGen` 的断言。结论是两个**独立定义**
    的复合在一点处的值等于 `R` 在该点的值，用 `toDetFun_spec` 的非平凡改写得到。
  - 定理 4、5 同理，前件只谈 `ctxOf` / `R` 的**函数性**，不谈复合。
  - 定理 6 取 `C := ctxPUnit`，`hctx` 由 `Subsingleton.elim` 自动供给 ——
    这是静态版真正的数学内容（上下文空间单点）。
  - 定理 7 无 `ctxOf` 前件：`stepToLawGen` 的输出在 `c` 位置上是常数单点集，
    读取时经 `dirac_inj_gen` 降维即可。

  ## 诚实标注

  - **只新增文件，未修改任何已有模块**（`Fate/StepToLawGen.lean` 的初稿未动）。
  - 零 `sorry` / 零 `admit` / 零 `axiom` / 零 `set_option`。
  - **不声称抽象版双向等价无条件成立**：本模块只给出**纤维上**的版本，
    并把初稿中那条假的无条件定理**如实替换**为有条件的形式。
============================================================================
-/

import FateWorld.Legacy.Frame
import FateWorld.Legacy.LawRule
import FateWorld.Legacy.LawRuleToTraj
import FateWorld.Legacy.WorldModel
import FateWorld.Legacy.DetFunToStepDraft
import FateWorld.Legacy.LawDetToStepGen
import FateWorld.Legacy.StepToLawDraft
import FateWorld.Legacy.StepToLaw

namespace Fate

open LawRule LawRuleToTraj

noncomputable section

/-! ## §1  定义与基本性质

抽象版 `Step → LawRule`。**关键事实**：右端不含 `ctxOf`（`ctxOf` 只由调用方
用来供给 `c` 位置），这是 §3 中「左往返只能逐纤维成立」的直接来源。 -/

/-- ⭐⭐⭐⭐ **【Step → LawRule（任意上下文空间 C 与任意 ctxOf）】**

在上下文 `c` 与状态 `x` 处，允许集是单点集 `{δ_{f x u ν θ a}}`。

**注意**：右端**不含 `ctxOf` 与 `c`** —— 这正是抽象化丢失上下文维度的原因。

标签：**[定义性约定]**（`lawDetToStepGen` 的反向嵌入）。 -/
def stepToLawGen {C : CtxSpace} (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (_ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier)
    (a : F.Act.Carrier) : LawRule.LawRule C F.X F.X :=
  fun _c x => {MeasureTheory.Measure.dirac (f x u ν θ a)}

/-- ⭐ **【定义性展开】** `stepToLawGen … f u ν θ a` 在 `(c, x)` 处的值是
单点集 `{δ_{f x u ν θ a}}`，**与 `c` 无关**。 -/
theorem stepToLawGen_apply {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (_ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier)
    (a : F.Act.Carrier) (c : C.Carrier) (x : F.X.Carrier) :
    stepToLawGen F instX _ctxOf f u ν θ a c x
      = {MeasureTheory.Measure.dirac (f x u ν θ a)} :=
  rfl

/-- ⭐⭐⭐ **【抽象版 `stepToLawGen` 是 `IsDirac`】前件：无。 -/
theorem stepToLawGen_isDirac {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier)
    (a : F.Act.Carrier) :
    @LawRuleToTraj.IsDirac C F.X F.X instX (stepToLawGen F instX ctxOf f u ν θ a) :=
  fun _c x => ⟨f x u ν θ a, rfl⟩

/-- ⭐⭐⭐⭐ **【静态版 `stepToLaw` 是抽象版的确实特例】**（`rfl` 级） -/
theorem stepToLawGen_static (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier)
    (a : F.Act.Carrier) :
    stepToLawGen F instX (ctxOfStatic F) f u ν θ a = stepToLaw F instX f u ν θ a :=
  rfl

/-! ## §2  左往返：**上下文对齐后**逐点成立

这是 P0-5 错误的核心修复点。前件 `hctx : ctxOf x u ν θ a = c` 是**真实数学前提**
（上下文对齐），不是技术规避：见文件头「根因」。 -/

/-- ⭐⭐⭐⭐⭐ **【抽象版左往返（纤维上，逐点）】**

若 `ctxOf x u ν θ a = c`（**上下文对齐条件**），则

`stepToLawGen (lawDetToStepGen R hR) u ν θ a` 在 `(c, x)` 处等于 `R c x`。

**⟹ 无条件成立是不可能的**：`stepToLawGen` 生成的 `LawRule` 在每个 `c` 处
返回**同一个**单点集，而 `R` 携带随 `c` 变化的信息，故
`Step → LawRule → Step` 丢失上下文维度。

**⟹ 静态上下文（`C := ctxPUnit`，`PUnit` 单点）是这个条件的自动特例**，
所以 `Fate/StepToLaw.lean` 的无条件版本在那里成立。

**证明**：`stepToLawGen` 展开给 `{δ_{toDetFun R hR (ctxOf x …) x}}`；
`toDetFun_spec` 给 `R c x = {δ_{toDetFun R hR c x}}`；用 `hctx` 对齐后两者同项，
取 `.symm` 即得。 -/
theorem stepToLawGen_lawDetToStepGen_at {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (c : C.Carrier) (x : F.X.Carrier) (hctx : ctxOf x u ν θ a = c) :
    stepToLawGen F instX ctxOf (lawDetToStepGen F instX ctxOf R hR) u ν θ a c x
      = R c x := by
  show ({MeasureTheory.Measure.dirac
    (@LawRuleToTraj.toDetFun C F.X F.X instX R hR (ctxOf x u ν θ a) x)} :
      Set (MeasureTheory.Measure F.X.Carrier)) = R c x
  rw [hctx]
  exact (@LawRuleToTraj.toDetFun_spec C F.X F.X instX R hR c x).symm

/-- ⭐⭐⭐⭐⭐ **【抽象版左往返（纤维上，全函数）】**

若在给定外部输入 `(u, ν, θ, a)` 下 `ctxOf` 恒等于 `c₀`，则

`stepToLawGen (lawDetToStepGen R hR) u ν θ a = fun _ x => R c₀ x`，

即抽象版复合**等于 `R` 在上下文 `c₀` 处的那一条纤维**
（把它常数延拓到全部 `c`）。

**⟹ 这是「两层是同一层」在抽象上下文下的正确形式**：
不是 `= R`，而是「`R` 的单条上下文纤维」。

**静态特例**：`C := ctxPUnit` 时 `c₀ = PUnit.unit` 是唯一上下文，
本定理即退化为 `= R`（见定理 `stepToLawGen_lawDetToStep_static`）。 -/
theorem stepToLawGen_lawDetToStepGen_fiber {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (c₀ : C.Carrier)
    (hctx : ∀ x : F.X.Carrier, ctxOf x u ν θ a = c₀) :
    stepToLawGen F instX ctxOf (lawDetToStepGen F instX ctxOf R hR) u ν θ a
      = fun _ x => R c₀ x := by
  funext c x
  exact stepToLawGen_lawDetToStepGen_at F instX ctxOf R hR u ν θ a c₀ x (hctx x)

/-- ⭐⭐⭐⭐ **【抽象版左往返（`R` 不依赖上下文时全局成立）】**

若 `R` 的所有上下文纤维相同（`∀ c c', R c = R c'`）且 `ctxOf` 在给定输入下
是常数，则 `stepToLawGen (lawDetToStepGen R hR) u ν θ a = R`。

**⟹ 这是「抽象版全局互逆」的**唯一**可能形式**：必须要求 `R` 本身不含上下文信息。
`IsDirac` 单独不足（见文件头根因）。 -/
theorem stepToLawGen_lawDetToStepGen_global {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (c₀ : C.Carrier)
    (hctx : ∀ x : F.X.Carrier, ctxOf x u ν θ a = c₀)
    (hRc : ∀ c c' : C.Carrier, R c = R c') :
    stepToLawGen F instX ctxOf (lawDetToStepGen F instX ctxOf R hR) u ν θ a = R := by
  rw [stepToLawGen_lawDetToStepGen_fiber F instX ctxOf R hR u ν θ a c₀ hctx]
  funext c x
  rw [hRc c c₀]

/-- ⭐⭐⭐⭐⭐ **【静态特例：`C := ctxPUnit` 时无条件成立】**

在 `C := ctxPUnit := ⟨PUnit⟩` 处，`ctxOf` 的任何取值都等于唯一的 `c`（`PUnit` 单点），
故 `stepToLawGen (lawDetToStepGen R hR) u ν θ a = R` **无额外前提**。

**⟹ 这精确解释了为什么 `Fate/StepToLaw.lean` 的静态版无条件成立，
而抽象版必须加条件**：`PUnit` 只有一个元素，上下文对齐自动满足。 -/
theorem stepToLawGen_lawDetToStep_static (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (R : LawRule.LawRule ctxPUnit F.X F.X)
    (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    stepToLawGen F instX (ctxOfStatic F) (lawDetToStepGen F instX (ctxOfStatic F) R hR)
        u ν θ a = R := by
  funext c x
  -- `ctxPUnit.Carrier = PUnit` 只有唯一元素 `unit`，故 `ctxOfStatic F x u ν θ a`
  -- 与 `c` 是**定义相等**（两者都归约为 `PUnit.unit`）。
  exact stepToLawGen_lawDetToStepGen_at F instX (ctxOfStatic F) R hR u ν θ a c x
    (by cases c; rfl)

/-! ## §3  右往返（无需 `ctxOf` 纤维性）

初稿 `Fate/StepToLawGen.lean` 的右往返多带了 `_hctx` 前件（实际上未被使用）。
此处给出**不带该前件**的版本：`stepToLawGen` 的输出在每个 `c` 处是同一个单点集，
读取时用 `dirac_inj_gen` 降维即可，`ctxOf` 如何变化无关。 -/

/-- **Dirac 单射性**（`private` 局部引理，非交付定理）。 -/
private lemma dirac_inj_gen {α : Type*} (m : MeasurableSpace α) [MeasurableSingletonClass α]
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

/-- ⭐⭐⭐⭐ **【右往返：`lawDetToStepGen ∘ stepToLawGen = id`】**

点分离 `[MeasurableSingletonClass F.X.Carrier]` 下（`δ` 单射），
把 `stepToLawGen f u ν θ a` 经 `lawDetToStepGen` 抽回，得到原 `f`。

**前件**：仅点分离。**不**需要 `ctxOf` 的纤维性 —— 因为 `stepToLawGen` 的输出
在每个 `c` 处是**同一个**单点集，读取时 `c` 的位置无关。

**诚实标注**：点分离是**真实数学前提**（平凡 σ-代数下所有 Dirac 相等），
与 `Fate/StepToLaw.lean` 定理 2 同一缺口。 -/
theorem lawDetToStepGen_stepToLawGen {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    [MeasurableSingletonClass F.X.Carrier]
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier)
    (a : F.Act.Carrier) (x : F.X.Carrier) :
    lawDetToStepGen F instX ctxOf
        (stepToLawGen F instX ctxOf f u ν θ a)
        (stepToLawGen_isDirac F instX ctxOf f u ν θ a) x u ν θ a
      = f x u ν θ a := by
  have hD := stepToLawGen_isDirac F instX ctxOf f u ν θ a
  show @LawRuleToTraj.toDetFun C F.X F.X instX (stepToLawGen F instX ctxOf f u ν θ a) hD
    (ctxOf x u ν θ a) x = f x u ν θ a
  unfold LawRuleToTraj.toDetFun
  have hs := Classical.choose_spec (hD (ctxOf x u ν θ a) x)
  simp only [stepToLawGen] at hs
  exact dirac_inj_gen instX (Set.singleton_eq_singleton_iff.mp hs).symm

/-! ## §4  汇总：**纤维上的**双向等价

⚠ 本节**不**声称抽象版无条件双向等价。初稿 `dirac_law_step_roundtrip_gen`
的无条件左逆断言是假的，已在此替换为纤维形式。 -/

/-- ⭐⭐⭐⭐⭐ **【抽象版双向等价（纤维上）】**

对任意 `C : CtxSpace`、任意 `ctxOf`、任意 `c₀`，若 `ctxOf` 在给定输入下恒为 `c₀`：

- **(1) 左逆（该纤维上）**：
  `stepToLawGen (lawDetToStepGen R hR) u ν θ a = fun _ x => R c₀ x`；
- **(2) 提升即 Dirac（无条件）**：`IsDirac (stepToLawGen f u ν θ a)`。

**⟹ 这不是全局互逆**：`Step` 只携带一条上下文，`LawRule` 携带整族纤维，
复合 `Step → LawRule → Step` 丢失上下文维度。

**⟹ 全局互逆只在静态上下文（`C := ctxPUnit`）或 `R` 不受上下文影响时成立**，
见 `stepToLawGen_lawDetToStep_static` 与 `stepToLawGen_lawDetToStepGen_global`。 -/
theorem dirac_law_step_roundtrip_gen_fiber {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (c₀ : C.Carrier)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (hctx : ∀ x : F.X.Carrier, ctxOf x u ν θ a = c₀) :
    (∀ (R : LawRule.LawRule C F.X F.X)
        (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R),
        stepToLawGen F instX ctxOf (lawDetToStepGen F instX ctxOf R hR) u ν θ a
          = fun _ x => R c₀ x)
    ∧ (∀ (f : Step F),
        @LawRuleToTraj.IsDirac C F.X F.X instX
          (stepToLawGen F instX ctxOf f u ν θ a)) := by
  refine ⟨?_, ?_⟩
  · intro R hR
    exact stepToLawGen_lawDetToStepGen_fiber F instX ctxOf R hR u ν θ a c₀ hctx
  · intro f
    exact stepToLawGen_isDirac F instX ctxOf f u ν θ a

/-- ⭐⭐⭐⭐⭐ **【静态版本的纤维汇总退化为无条件双向等价】**

`C := ctxPUnit` 时 `hctx` 自动满足，上一条件的纤维形式退化为
「`stepToLawGen (lawDetToStepGen R hR) = R`」——**无额外前提**。
与 `Fate/StepToLaw.lean` 的 `dirac_law_step_roundtrip` 同型，但此处的
`stepToLawGen`/`lawDetToStepGen` 是 P0-5/P0-4 的抽象定义。 -/
theorem dirac_law_step_roundtrip_gen_static (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    (∀ (R : LawRule.LawRule ctxPUnit F.X F.X)
        (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R),
        stepToLawGen F instX (ctxOfStatic F)
          (lawDetToStepGen F instX (ctxOfStatic F) R hR) u ν θ a = R)
    ∧ (∀ (f : Step F),
        @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX
          (stepToLawGen F instX (ctxOfStatic F) f u ν θ a)) := by
  refine ⟨?_, ?_⟩
  · intro R hR
    exact stepToLawGen_lawDetToStep_static F instX R hR u ν θ a
  · intro f
    exact stepToLawGen_isDirac F instX (ctxOfStatic F) f u ν θ a

/-! ## §5  轨迹忠实性（抽象版，无 `ctxOf` 纤维性要求） -/

/-- ⭐⭐⭐⭐ **【抽象版轨迹忠实性：迭代的每一步都合法于 `R`】** -/
theorem lawDetToStepGen_iterate_law {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)
    (x₀ : F.X.Carrier) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) (n : ℕ) :
    R (ctxOf ((lawDetToStepGen F instX ctxOf R hR · u ν θ a)^[n] x₀) u ν θ a)
        ((lawDetToStepGen F instX ctxOf R hR · u ν θ a)^[n] x₀)
      = {MeasureTheory.Measure.dirac
          ((lawDetToStepGen F instX ctxOf R hR · u ν θ a)^[n+1] x₀)} := by
  rw [Function.iterate_succ_apply']
  exact lawDetToStepGen_spec F instX ctxOf R hR _ u ν θ a

end

end Fate
