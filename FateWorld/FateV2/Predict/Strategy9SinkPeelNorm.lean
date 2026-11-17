/-
# 视角 9（第 2 版）：「图 ⟹ 概率」桥的第 9 种策略 —— 汇点剥离 + 逐点归一化

## ⚠⚠ 第 161+ 轮 FIX 记录：3 条定理中 3 条为假，已全部删除

本文件原含 **3 条定理**：`bar_univ`、`tail_congr`、`sink_peel`（另有辅助引理
`bar_empty`）。经 **机检** 复核，**这 3 条定理的陈述全为假**，
不是「证明写崩」，而是**命题本身不成立**。假命题无法证出，
按项目纪律（不得 `sorry`/`admit`/`axiom` 占位；证不出就删该定理并如实说明），
本轮处理如下：

| 原定理 | 原陈述 | 判决 | 机检依据（本文件内，已编译零 error）|
|---|---|---|---|
| `bar_univ` | `bar univ f x = ∏ v, f v x` | **假，已删除** | `bar_univ_original_false` |
| `tail_congr` | 前提只约束 `univ \ T` 的坐标 ⟹ `tail f T w = tail f T w'` | **假，已删除** | `tail_congr_original_false` |
| `sink_peel` | `bar T f x = bar (T\{s}) f (unpin s x a₀) * f s x` | **假，已删除** | `sink_peel_original_false` |
| `bar_empty` | `bar ∅ f x = ∑ w, ∏ v, f v w` | **真，保留** | `bar_empty`（原证明即成立）|

**⟹ 本文件不再含任何假定理；保留项为 `bar` / `tail` 的定义、`bar_empty`，
以及上述 3 条机检反例（它们是删除的依据，且本身为真）。**

### 0.1 三条定理为什么是假的（逐条数学理由）

**(A) `bar_univ` 假。** `bar univ f x = mass univ (tail f univ) x`，而
`tail f univ = ∏ v ∈ (univ \ univ), f v _ = ∏ v ∈ ∅, _ = 1`。
故 `bar univ f x = 1`（`bar_univ_is_one`），**与 `∏ v, f v x` 无关**。
取 `f ≡ 2` 即得 `1 ≠ 2`。
**根源**：`tail` 定义为「补集上的乘积」，`T = univ` 时补集为空，乘积退化为 `1`。

**(B) `tail_congr` 假。** 原前提只约束 **`univ \ T`** 上的坐标，
但 `tail f T w = ∏ v ∈ (univ \ T), f v w` 的每个因子 `f v` 是**任意**函数，
可以读 `univ \ T` **以外**的坐标（本文件没有任何「`f v` 只读 `univ \ T`」的前提）。
**反例**（机检 `tail_congr_original_false`）：`V = Fin 2`、`T = {1}`，则
`univ \ T = {0}`，前提只约束坐标 `0`；取 `f := fRead1`（读坐标 `1`）、
`w = (0↦tt, 1↦tt)`、`w' = (0↦tt, 1↦ff)`：前提满足，但左 `= 1`、右 `= 0`。

**(C) `sink_peel` 假。** 该等式漏了一个 **`|α|` 因子**。
`mass (T\{s})` 的纤维比 `mass T` 大 `|α|` 倍（少一条约束 `w_s = x_s`）。
**反例**（机检 `sink_peel_original_false`）：`V = Fin 1`、`α = Bool`、
`f ≡ 1`、`T = {0} = univ`、`s = 0`（`s ∈ T` 且 `s` 是汇点，前提全满足）：
* 左：`tail f {0} = ∏ ∅ = 1` ⟹ `bar {0} f x = mass univ 1 x = 1`；
* 右：`tail f ∅ = ∏ v ∈ univ 1 = 1` ⟹ `bar ∅ f y = mass ∅ 1 y = ∑_{_ : U1 → Bool} 1 = 2`，
  再乘 `f 0 x = 1`，得 `2`。
故 `1 ≠ 2`，原等式不成立。

**进一步：`sink_peel` 不是「补一个因子」或「加一个前提」能简单修的。**
被积函数 `f_s · tail_f T` 依赖 `{s} ∪ (univ \ T) = univ \ (T \ {s})`，
即 `T \ {s}` 的**补集**；而 `mass (T\{s})` 的纤维塌缩需要被积函数依赖
**`T \ {s}` 本身**（方向相反）。故本文件**不提供**该定理的任何替代版本，
留待重新设计引理体系。

### 0.2 本视角原设想中的**正确**内容（未形式化）

原文件 §2 的直觉是可救的，只是陈述写错了。正确的枢纽应是
「**对 `unpin` 后的 `T`-纤维求和**」而不是「`bar (T\{s})`」，即

```
bar T f x = (∑_a mass T (...)) ...   — 需要 f_s 只读 s，或 f_s 在 T-纤维上常值
```

这需要额外结构（`f_s` 在 `T`-纤维上常值），**原定理没有这个前提**，
故不能从 `LocalTo G f` 推出（`LocalTo` 只给「`f_v` 读 `{v} ∪ pa(v)`」，
**不**给「`f_s` 只读 `s`」）。**本文件不假装补上这一段。**

## 1 诚实边界

* 本文件 **不含 `sorry` / `admit` / `axiom`**。
* 本文件 **不含任何未证的假陈述**：原 3 条假定理已删除，此处只留
  其**机检反例**（真命题）与为真的 `bar_empty`。
* 请对照 `Fate/Strategy9SinkPeelVerdict.lean`（既有的、已入库的独立裁决模块）
  与 `Fate/BarCorrected.lean`、`Fate/SinkPeelCounterexample.lean`、
  `Fate/SinkPeelFinalVerdict.lean` 等 —— 它们记录了同一结论（本文件独立复核一致）。

## 2 依赖

* `Fate.FactorMarkov`（`LocalTo`、`FactorNorm`、`Factorizes`）
* `Fate.DAGFactorization`（`mass`、`unpin`、`mass_univ`、`mass_empty`、`mass_mul`）
* `CausSeparation`（`Causalean.Graph.DAG`、`G.edge`）
-/

import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FateV2.Predict

open FateV2.Modeling
namespace Strategy9Norm

open Finset
open FateV2.Modeling.Graph
open Fate.DAGFactorization (mass unpin mass_univ mass_empty mass_mul)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · Strategy9SinkPeelNorm

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Strategy9SinkPeelNorm.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov, DAGFactorization, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 补集乘积的质量 `bar`（定义保留）
  =========================================================================== -/

/-- 补集乘积：在 `T` 的**补集**上求积。

⚠ 注意 `T = univ` 时退化为空乘积 `1`——这正是原 `bar_univ` 陈述错误的根源。 -/
noncomputable def tail (f : V → (V → α) → ℝ) (T : Finset V) : (V → α) → ℝ :=
  fun w => ∏ v ∈ (univ \ T), f v w

/-- **`bar T f x` = 在 `T` 上钉死为 `x`、对补集求和**（**单层** `mass`）。 -/
noncomputable def bar (T : Finset V) (f : V → (V → α) → ℝ) (x : V → α) : ℝ :=
  mass T (tail f T) x

/-! ===========================================================================
  §2 保留：`bar_empty`（原文件唯一为真的定理）
  =========================================================================== -/

/-- ⭐ **`bar ∅` 的值**：全空间求和。

`tail f ∅ = ∏ v ∈ (univ \ ∅), f v _ = ∏ v, f v _`，故
`bar ∅ f x = mass ∅ (∏ v, f v ·) x = ∑ w, ∏ v, f v w`（`mass ∅` 与 `x` 无关）。 -/
theorem bar_empty (f : V → (V → α) → ℝ) (x : V → α) :
    bar ∅ f x = ∑ w, ∏ v, f v w := by
  unfold bar tail
  rw [show (univ \ (∅ : Finset V)) = univ from Finset.sdiff_empty, mass_empty]

/-! ===========================================================================
  §3 机检反例：原 3 条定理的陈述为假（删除依据）

  以下 4 条定理**为真**，内容正是「原陈述不成立」。它们替代了被删除的
  假定理，使本模块对「为何删除」自证。
  =========================================================================== -/

/-- ⭐⭐ `bar univ` 的**正确值**：`1`（`tail f univ = ∏ ∅ = 1`）。

原 `bar_univ`（`= ∏ v, f v x`）为假，见 `bar_univ_original_false`。 -/
theorem bar_univ_is_one (f : V → (V → α) → ℝ) (x : V → α) :
    bar univ f x = 1 := by
  unfold bar tail
  simp only [Finset.sdiff_self, Finset.prod_empty]
  rw [mass_univ]

/-- ⭐⭐⭐ **原 `bar_univ` 的陈述为假**（机检）。

取 `V = Fin 1`、`α = Bool`、`f ≡ 2`：左 `= 1`（`bar_univ_is_one`）、
右 `= ∏ v : Fin 1, 2 = 2`，不等。 -/
theorem bar_univ_original_false :
    ¬ (∀ (V : Type) [DecidableEq V] [Fintype V] (α : Type) [Fintype α] [DecidableEq α]
        (f : V → (V → α) → ℝ) (x : V → α),
        bar (univ : Finset V) f x = ∏ v, f v x) := by
  intro h
  have hkey := h (Fin 1) Bool (fun _ _ => (2 : ℝ)) (fun _ => false)
  rw [bar_univ_is_one] at hkey
  simp at hkey

/-- 反例用的机制族：读坐标 `1`，不看坐标 `0`。 -/
def fRead1 : Fin 2 → (Fin 2 → Bool) → ℝ :=
  fun _ w => if w 1 = true then 1 else 0

/-- ⭐⭐⭐ **原 `tail_congr` 的陈述为假**（机检）。

原前提只约束 `univ \ T` 上的坐标，而 `tail` 的因子可读任意坐标。 -/
theorem tail_congr_original_false :
    ¬ (∀ (V : Type) [DecidableEq V] [Fintype V] (α : Type)
        (T : Finset V) (f : V → (V → α) → ℝ) (w w' : V → α),
        (∀ u ∈ univ \ T, w u = w' u) → tail f T w = tail f T w') := by
  intro h
  have hpre : ∀ u ∈ univ \ ({1} : Finset (Fin 2)),
      (fun j : Fin 2 => if j = 0 then true else true) u
      = (fun j : Fin 2 => if j = 0 then true else false) u := by
    intro u hu
    have hu1 : u ≠ 1 := by
      simpa using (Finset.mem_sdiff.mp hu).2
    have hu0 : u = 0 := by
      have : u = 0 ∨ u = 1 := by fin_cases u <;> simp
      tauto
    simp [hu0]
  have hkey := h (Fin 2) Bool ({1} : Finset (Fin 2)) fRead1
    (fun j : Fin 2 => if j = 0 then true else true)
    (fun j : Fin 2 => if j = 0 then true else false) hpre
  simp only [tail] at hkey
  rw [show (univ \ ({1} : Finset (Fin 2))) = ({0} : Finset (Fin 2)) from by decide] at hkey
  simp [fRead1] at hkey

/-! ### 3.1 `sink_peel` 的数值反例（`T = {s} = univ`） -/

/-- 反例变量集：`Fin 1`。 -/
abbrev U1 := Fin 1

/-- 反例机制族：处处为 `1`。 -/
def fOne : U1 → (U1 → Bool) → ℝ := fun _ _ => 1

/-- 反例的 `T`（此时 `T = univ`）。 -/
def TOne : Finset U1 := {0}

/-- 反例的汇点 `s = 0`。 -/
def sOne : U1 := 0

/-- `sink_peel` 的左端 `= 1`。 -/
theorem lhs_eq_one (x : U1 → Bool) : bar TOne fOne x = 1 := by
  have hT : TOne = (univ : Finset U1) := by
    ext u
    simp only [TOne, Finset.mem_singleton, Finset.mem_univ, iff_true]
    exact Fin.eq_zero u
  rw [hT]
  exact bar_univ_is_one fOne x

/-- `sink_peel` 的右端 `= 2`（`mass ∅` 的纤维大小 `= |Bool| = 2`）。 -/
theorem rhs_eq_two (x : U1 → Bool) (a : Bool) :
    bar (TOne \ {sOne}) fOne (unpin sOne x a) * fOne sOne x = 2 := by
  have hT : TOne \ {sOne} = (∅ : Finset U1) := by unfold TOne sOne; decide
  rw [hT, bar_empty]
  have hfac : ∀ w : U1 → Bool, (∏ v : U1, fOne v w) = 1 := by
    intro w; simp [fOne]
  have hfs : fOne sOne x = 1 := by simp [fOne]
  rw [hfs, mul_one]
  simp only [hfac, Finset.sum_const, Finset.card_univ]
  norm_num [Fintype.card_fun]

/-- ⭐⭐⭐ **原 `sink_peel` 的等式为假**（机检）：左 `1`、右 `2`。 -/
theorem sink_peel_original_false (x : U1 → Bool) (a : Bool) :
    bar TOne fOne x ≠ bar (TOne \ {sOne}) fOne (unpin sOne x a) * fOne sOne x := by
  rw [lhs_eq_one, rhs_eq_two]
  norm_num

end Strategy9Norm

end FateV2.Predict