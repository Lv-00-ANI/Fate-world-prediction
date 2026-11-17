/-
# P-006 分诊结果更正：`Strategy9SinkPeelNorm` 判 **ARCHIVE/不修**（原判 FIX 有误）

## 0 分诊表第 18 行的判定必须更正

《坏模块分诊.md》第 18 行对 `Fate/Strategy9SinkPeelNorm.lean`（10 error / 3 定理）
判 **FIX**，理由是「错误密度高说明是**单条证明内部写崩**，重写 3 条成本低」。

**该理由经逐条复核后不成立。** 该文件的 3 条定理中，
**有 3 条陈述为假**（不是证明写崩，是命题本身为假），
只有 `bar_empty` 一条为真。假命题无论证明写得多好都证不出来。

按《坏模块分诊.md》§5 硬提醒 1 的明文要求
（「先确认模块里有没有假定理再动手……否则会像历史事故一样用 `sorry` 硬撑」），
本文件**不执行 FIX**，而是：

1. 逐条登记 3 条假定理及其**机检反例/反证出处**；
2. 保留其中**为真**的部分（`bar_empty` 的正确版本）；
3. 把 2 条反例本身**提升为本模块内的机检定理**，作为「不修」的正式依据。

**本模块不含 `sorry` / `admit` / `axiom`。**

## 1 逐条判决

| 原定理（`Strategy9SinkPeelNorm`） | 判决 | 机检依据 | 本模块对应条目 |
|---|---|---|---|
| `bar_univ` : `bar univ f x = ∏ v, f v x` | **假，删除** | `Fate/BarCorrected.lean`（`bar_univ_correct : bar univ f x = 1`，编译零 error）；git `4100e04` 已登记为「第 11 处真实数学错误」 | `bar_univ_correct`（真值 `1`）、`bar_univ_original_false` |
| `tail_congr` : 前提只约束 `univ \ T` 的坐标 ⟹ `tail f T w = tail f T w'` | **假，删除** | 本文件 `tail_congr_original_false`（`V = Fin 2`、`T = {1}`、`f` 读坐标 `1` 的反例，**机检**） | `tail_congr_original_false` |
| `sink_peel` : `bar T f x = bar (T\{s}) f (unpin s x a₀) * f s x` | **假，删除** | `Fate/SinkPeelCounterexample.lean`（`T={s}`：左 `1` ≠ 右 `2`）+ `Fate/SinkPeelGeneralRefutation.lean`（参数化反证），均编译零 error | `sink_peel_fails_at_singleton` |
| `bar_empty` : `bar ∅ f x = ∑ w, ∏ v, f v w` | **真，保留** | 原证明即成立 | `bar_empty_correct` |

### 1.1 `bar_univ` 为什么是假的

`T = univ` 时 `tail f univ = ∏ v ∈ (univ \ univ), f v _ = ∏ v ∈ ∅, _ = 1`，
故 `bar univ f x = mass univ (fun _ => 1) x = 1`，与 `∏ v, f v x` 无关。
原文件第 116 行的 error 残局正是 `⊢ 1 = ∏ v, f v x`——假陈述的现场。

### 1.2 `tail_congr` 为什么是假的（本次新发现，原分诊未识别）

原陈述的前提是 `∀ u ∈ univ \ T, w u = w' u`，即**只约束 `univ \ T` 上的坐标**。
但 `tail f T w = ∏ v ∈ (univ \ T), f v w` 的每个因子 `f v` 是**任意**函数，
可以读 `univ \ T` 以外的坐标。

**反例**（`tail_congr_original_false`，机检）：`V = Fin 2`、`T = {1}`，则 `univ \ T = {0}`，
前提只约束坐标 `0`。取 `f v w := if w 1 then 1 else 0`（读坐标 `1`），
`w ≡ true`、`w' := (0 ↦ true, 1 ↦ false)`：前提满足，但
左 `= 1`、右 `= 0`。**故原陈述为假。**

（正确形式需加「`f v` 只读 `univ \ T`」之类的前提，但那已不是原定理。）

### 1.3 `sink_peel` 为什么是假的

取 `V = Fin 1`、`α = Bool`、`f ≡ 1`、`T = {0}`、`s = 0`（`s` 是汇点、`s ∈ T`，前提全满足）：

* 左：`tail f {0} = ∏ ∅ = 1`，`{0} = univ` ⟹ `bar {0} f x = mass univ 1 x = 1`；
* 右：`tail f ∅ = ∏ v ∈ univ 1 = 1`，`bar ∅ f y = mass ∅ 1 y = ∑ _ : (Fin 1 → Bool), 1 = 2`，
  乘 `f 0 x = 1` 得 `2`。

`1 ≠ 2` ⟹ 假。缺一个 `multS` / `|α|` 纤维因子。
`Fate/SinkPeelFinalVerdict.lean` 已给出六步诊断链：右端被积函数只读
`{s} ∪ (univ \ T)`＝`T \ {s}` 的**补集**，与 `mass_sdiff_of_reads` 要求的
「只读 `T \ {s}`」**方向相反**，故不能靠「补 `|α|` 因子」或「加局部性前提」修好。

## 2 归档建议

`Fate/Strategy9SinkPeelNorm.lean` 应 **ARCHIVE**：其 3 条定理中 3 条为假，
「汇点剥离 + 逐点归一化」这条路线的前提本身写错（`bar` 定义与 `bar_univ` 引理不自洽）。
本模块即其**诚实归档件**：保留唯一的真命题 `bar_empty`，并把三条假命题的反例
固化为机检定理，防止后人重犯。

## 3 诚实边界

* 本模块**不**重新证明 `sink_peel` 的正确形式——那需要全新的引理体系
  （见 `Fate/SinkPeelFinalVerdict.lean` §「最终判决」），不在本次修复范围内。
* 本模块**不**声称「沿拓扑序剥离」这一数学直觉无效，只声称
  `Strategy9SinkPeelNorm` 对它的**形式化陈述**（`bar`/`tail` 的定义 + 三条定理）为假。
* 原文件 `tail`/`bar` 的定义本身没有问题（与 `Fate/BarCorrected.lean` 的 `S9Fixed` 定义一致）；
  出错的是建立在它们之上的三条**陈述**。
-/

import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.BarCorrected
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FateV2.Predict

open FateV2.Modeling
namespace Strategy9Verdict

open Finset
open FateV2.Modeling.Graph
open Fate.DAGFactorization (mass unpin mass_univ mass_empty)

universe u

/-!
  # Predict · Strategy9SinkPeelVerdict

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Strategy9SinkPeelVerdict.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DAGFactorization, FactorMarkov, BarCorrected
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 定义（与 `Strategy9SinkPeelNorm` 逐字一致，便于对照归档）
  =========================================================================== -/

/-- 补集乘积。与 `Strategy9SinkPeelNorm.tail` 定义一致。 -/
noncomputable def tail {V : Type u} [DecidableEq V] [Fintype V]
    {α : Type u} (f : V → (V → α) → ℝ) (T : Finset V) : (V → α) → ℝ :=
  fun w => ∏ v ∈ (univ \ T), f v w

/-- `bar T f x` = 在 `T` 上钉死为 `x`、对补集求和（**单层** `mass`）。
与 `Strategy9SinkPeelNorm.bar` 定义一致。 -/
noncomputable def bar {V : Type u} [DecidableEq V] [Fintype V]
    {α : Type u} [Fintype α] [DecidableEq α] (T : Finset V)
    (f : V → (V → α) → ℝ) (x : V → α) : ℝ :=
  mass T (tail f T) x

/-! ===========================================================================
  §2 保留：`bar_empty`（原文件唯一为真的定理）
  =========================================================================== -/

/-- ⭐ **`bar ∅` 的值**：全空间求和（`tail f ∅ = ∏ v ∈ univ, f v`）。

原文件这条**是对的**，证明也成立；此处用本命名空间的定义独立重证。 -/
theorem bar_empty_correct {V : Type u} [DecidableEq V] [Fintype V]
    {α : Type u} [Fintype α] [DecidableEq α] (f : V → (V → α) → ℝ) (x : V → α) :
    bar (∅ : Finset V) f x = ∑ w, ∏ v, f v w := by
  unfold bar tail
  rw [Finset.sdiff_empty, mass_empty]

/-! ===========================================================================
  §3 假定理之一：`bar_univ`（正确值为 `1`）
  =========================================================================== -/

/-- ⭐⭐ **`bar univ` 的正确值**：`1`（`tail f univ = ∏ ∅ = 1`）。

原陈述 `bar univ f x = ∏ v, f v x` **为假**（见 `bar_univ_original_false`）。 -/
theorem bar_univ_correct {V : Type u} [DecidableEq V] [Fintype V]
    {α : Type u} [Fintype α] [DecidableEq α] (f : V → (V → α) → ℝ) (x : V → α) :
    bar (univ : Finset V) f x = 1 := by
  unfold bar tail
  simp only [Finset.sdiff_self, Finset.prod_empty]
  rw [mass_univ]

/-- ⭐⭐⭐ **原 `bar_univ` 的陈述为假**（机检）：

存在 `f`、`x` 使 `bar univ f x ≠ ∏ v, f v x`。

取 `V = Fin 1`、`α = Bool`、`f ≡ 2`、`x ≡ false`：
左 `= 1`，右 `= ∏ v, 2 = 2`，不等。 -/
theorem bar_univ_original_false :
    ¬ (∀ (V : Type) [DecidableEq V] [Fintype V] (α : Type) [Fintype α] [DecidableEq α]
        (f : V → (V → α) → ℝ) (x : V → α),
        @bar V _ _ α _ _ univ f x = ∏ v, f v x) := by
  intro h
  have hkey := h (Fin 1) (Bool) (fun _ _ => (2 : ℝ)) (fun _ => false)
  -- 左边 = 1（bar_univ_correct），右边 = ∏ v : Fin 1, 2 = 2
  rw [bar_univ_correct] at hkey
  simp at hkey

/-! ===========================================================================
  §4 假定理之二：`tail_congr`（前提不足以推出结论）
  =========================================================================== -/

/-- 反例用的机制族：读坐标 `1`，不看坐标 `0`。 -/
def fRead1 : Fin 2 → (Fin 2 → Bool) → ℝ :=
  fun _ w => if w 1 = true then 1 else 0

/-- ⭐⭐⭐ **原 `tail_congr` 的陈述为假**（机检）。

原前提 `∀ u ∈ univ \ T, w u = w' u` 只约束 `univ \ T` 上的坐标，
而 `tail` 的因子 `f v` 可以读**任意**坐标。

取 `V = Fin 2`、`T = {1}`（故 `univ \ T = {0}`，前提只约束坐标 `0`）、
`f := fRead1`（读坐标 `1`）、
`w := (0 ↦ true, 1 ↦ true)`、`w' := (0 ↦ true, 1 ↦ false)`：
前提满足，但左 `= 1`、右 `= 0`。 -/
theorem tail_congr_original_false :
    ¬ (∀ (V : Type) [DecidableEq V] [Fintype V] (α : Type)
        (T : Finset V) (f : V → (V → α) → ℝ) (w w' : V → α),
        (∀ u ∈ univ \ T, w u = w' u) → @tail V _ _ α f T w = @tail V _ _ α f T w') := by
  intro h
  -- 前提：在 univ \ {1} = {0} 上，w 与 w' 相同
  have hpre : ∀ u ∈ univ \ ({1} : Finset (Fin 2)),
      (fun j : Fin 2 => if j = 0 then true else true) u
      = (fun j : Fin 2 => if j = 0 then true else false) u := by
    intro u hu
    have hu1 : u ≠ 1 := by
      have := (Finset.mem_sdiff.mp hu).2
      simpa using this
    have hu0 : u = 0 := by
      have : u = 0 ∨ u = 1 := by fin_cases u <;> simp
      tauto
    simp [hu0]
  have hkey := h (Fin 2) (Bool) ({1} : Finset (Fin 2)) fRead1
    (fun j : Fin 2 => if j = 0 then true else true)
    (fun j : Fin 2 => if j = 0 then true else false) hpre
  -- 展开 tail：`∏ v ∈ univ \ {1}`，而 `univ \ {1} = {0}`
  simp only [tail] at hkey
  rw [show (univ \ ({1} : Finset (Fin 2))) = ({0} : Finset (Fin 2)) from by decide] at hkey
  simp [fRead1] at hkey

/-! ===========================================================================
  §5 假定理之三：`sink_peel`（补集分解 + 数值反例）
  =========================================================================== -/

/-- ⭐⭐ **`sink_peel` 的补集分解**：`univ \ (T \ {s}) = insert s (univ \ T)`。

这是 `bar (T \ {s})` 的被积函数比 `bar T` **多一个 `f s` 因子**的结构根源，
即原式右端需要「补一个纤维因子」的来源。 -/
theorem sdiff_erase_eq {V : Type u} [DecidableEq V] [Fintype V]
    {T : Finset V} {s : V} (hsT : s ∈ T) :
    (univ \ (T \ {s}) : Finset V) = insert s (univ \ T) := by
  ext u
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hu
    by_cases hus : u = s
    · exact Or.inl hus
    · exact Or.inr fun hut => hu ⟨hut, hus⟩
  · rintro (rfl | hut)
    · intro hc; exact hc.2 rfl
    · intro hc; exact hut hc.1

/-! ### 5.1 数值反例（`T = {s}`） -/

/-- 反例的变量集：`Fin 1`。 -/
abbrev U1 := Fin 1

/-- 反例的取值集：`Bool`。 -/
abbrev B1 := Bool

/-- 反例的机制族：处处为 `1`。 -/
def fOne : U1 → (U1 → B1) → ℝ := fun _ _ => 1

/-- 反例的 `T`（此时 `T = univ`）。 -/
def TOne : Finset U1 := {0}

/-- 反例的汇点 `s = 0`。 -/
def sOne : U1 := 0

/-- **左端 = 1**。 -/
theorem lhs_eq_one (x : U1 → B1) : bar TOne fOne x = 1 := by
  have hT : TOne = (univ : Finset U1) := by
    ext u
    simp only [TOne, Finset.mem_singleton, Finset.mem_univ, iff_true]
    exact Fin.eq_zero u
  rw [hT]
  exact bar_univ_correct fOne x

/-- **右端 = 2**（`mass ∅` 的纤维大小 = `|Bool| = 2`）。 -/
theorem rhs_eq_two (x : U1 → B1) (a : B1) :
    bar (TOne \ {sOne}) fOne (unpin sOne x a) * fOne sOne x = 2 := by
  have hT : TOne \ {sOne} = (∅ : Finset U1) := by
    unfold TOne sOne
    decide
  rw [hT, bar_empty_correct]
  -- 每个因子 `fOne v w = 1`，共 `|U1 → B1| = 2` 个 `w`
  have hfac : ∀ w : U1 → B1, (∏ v : U1, fOne v w) = 1 := by
    intro w
    simp [fOne]
  have hfs : fOne sOne x = 1 := by simp [fOne]
  rw [hfs, mul_one]
  simp only [hfac, Finset.sum_const, Finset.card_univ]
  norm_num [Fintype.card_fun, U1, B1]

/-- ⭐⭐⭐ **原 `sink_peel` 的等式在反例点处为假。**

`bar TOne fOne x = 1` 而 `bar (TOne \ {sOne}) fOne (unpin sOne x a) * fOne sOne x = 2`，
故原等式（`1 = 2`）**不可能成立**。 -/
theorem sink_peel_fails_at_singleton (x : U1 → B1) (a : B1) :
    bar TOne fOne x ≠ bar (TOne \ {sOne}) fOne (unpin sOne x a) * fOne sOne x := by
  rw [lhs_eq_one, rhs_eq_two]
  norm_num

end Strategy9Verdict

end FateV2.Predict