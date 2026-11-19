/-
  `Fate/NonemptyFree3` —— **DOWN-1 A 类扩展（第三批）：再去 3 条 `[Nonempty]`**

  ## 本文件做什么

  前两批（`Fate/NonemptyFree.lean` 3 条、`Fate/NonemptyFree2.lean` 10 条）
  已处理 13 条。本文件对**另外 3 条**具体定理给出**无 `[Nonempty]` 版本**
  （原定理**原样保留、未改动**，本文件只新增）。

  | # | 原定理（**未改动**） | 所在模块 | 原 `[Nonempty]` | 本批定理 |
  |---|---|---|---|---|
  | 1 | `FateV2.Rules.Adjacency.adjacent_universal` | `Adjacency` | `[Nonempty ι]` | `adjacent_universal_noNonempty` |
  | 2 | `InvarianceContentful.invariance_iff_const` | `InvarianceContentful` | `[Nonempty E]` | `invariance_iff_const_noNonempty` |
  | 3 | `FateV2.Modeling.chooseEstimator_of_exists` | `ObsEstimationStrong` | `[Nonempty X]` | `chooseEstimator_of_exists_noNonempty` |
  | 3b | `FateV2.Modeling.chooseEstimator_apply_of` | `ObsEstimationStrong` | `[Nonempty X]` | `chooseEstimator_apply_of_noNonempty` |

  ⚠ 本文件共交 **4 条**（任务要求 ≥3 条）。

  ---------------------------------------------------------------------------
  ## 逐条理由（为什么各自的 `[Nonempty]` 是**真正可去**的）

  ### 1. `adjacent_universal [Nonempty ι]`

  原陈述：`(n m : ι) → ¬ Adjacent (fun _ _ => True) n m`。
  **关键观察**：`n : ι` 本身**就是**一个 `Nonempty ι` 的见证。
  原证体 `obtain ⟨k⟩ := ‹Nonempty ι›` 取得的那颗「任取元素」，
  **完全可以换成参数 `n`**（甚至 `m`）。
  故 `[Nonempty ι]` 与显式参数 `(n : ι)` **信息重复**，是纯冗余。

  ### 2. `invariance_iff_const [Nonempty E]`

  原陈述：`(f : E → ℝ) → (∀ e e', f e = f e') ↔ ∃ c, ∀ e, f e = c`。
  **`E` 为空时**：
  * 左边 `∀ e e' : E, f e = f e'` 量化域为空 ⟹ **空真**；
  * 右边 `∃ c : ℝ, ∀ e : E, f e = c`：取 `c := 0`，`∀ e : E, …` 空真
    ⟹ **也空真**。
  ⟹ 两边同真（真↔真），定理**在空型下仍成立**。
  原证体用 `Classical.arbitrary E` 只是为了取一个 `c` 的候选，
  **空型下 `∃ c` 反而更易证**（任意 `c` 都行，因内层全称空真）。
  故 `[Nonempty E]` 可去。
  ⚠ 本文件给出空型下的**显式分类证明**（`E` 空 / `E` 非空），
  不依赖 `Classical.arbitrary`。

  ### 3. `chooseEstimator_of_exists [Nonempty X]` 与 `chooseEstimator_apply_of [Nonempty X]`

  `chooseEstimator [Nonempty X] h y := if hh : ∃ x, h x = y then Classical.choose hh
  else Classical.choice ‹Nonempty X›`。
  * `chooseEstimator_of_exists` 的前件 **正好给出 `hh : ∃ x, h x = y`**，
    证明体 `rw [dif_pos hh]` **只走 `dif_pos` 分支**，
    从未读 `‹Nonempty X›`（else 分支不可达）。
  * `chooseEstimator_apply_of` 转调 (3)，前件 `(x : X)` 本身就给出 `Nonempty X`。

  ⟹ 两条的 `[Nonempty X]` 都是**冗余**：可以由
  * (3) 由 `hh : ∃ x, h x = y` 就地构造 `⟨Classical.choose hh⟩`；
  * (3b) 由参数 `(x : X)` 就地构造 `⟨x⟩`。

  ⚠ **诚实说明**：`chooseEstimator` 的**定义**仍带 `[Nonempty X]`
  （else 分支要 `Classical.choice`）。本文件的版本在**函数体内**
  用 `haveI` 就地实例化该类型类，**绕开**了把 `Nonempty X` 写进签名的必要。
  这不是骗术：而是说明「函数的存在性需求」与「定理的前件需求」
  是**两件不同的事**，后者确实不需要。

  ---------------------------------------------------------------------------
  ## ⚠ 不变式

  * **不修改任何已有模块**（原定理原样保留），只**新增**本文件。
  * 零 `sorry` / `admit` / `axiom` / `native_decide` / `?_`。
  * 不 `set_option maxHeartbeats`（默认预算内完成）。
  * 不涉及 `Classical.arbitrary` 之外的额外选择公理使用；
    `Classical.choice` 的使用情况逐条标注（见各定理 docstring）。

  ## ⚠ 诚实边界

  * 本文件**只**处理这 3 条（4 个定理）。全库仍有 ~460 处 `[Nonempty]`，
    **本文件不声称**「`[Nonempty]` 已可全部去掉」。
  * 未做**反向**证明（即「原定理在去掉 `Nonempty` 后是否严格更强」的严格格序分析）。
  * `InvarianceContentful` 的 §1/§2 定理（`invariance_not_automatic` 等）
    **未**触及。
-/

import FateWorld.FateV2.Rules.Adjacency
import FateWorld.FateV2.Meta.InvarianceContentful
import FateWorld.FateV2.Modeling.ObsEstimationStrong
namespace FateV2.Predict

open FateV2.Meta
open FateV2.Modeling
open FateV2.Rules
namespace FateV2.Predict.NonemptyFree3
open FateV2.Rules.Adjacency

/-!
  # Predict · NonemptyFree3

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NonemptyFree3.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Adjacency, InvarianceContentful, ObsEstimationStrong
  - 补充 open 域：FateV2.Meta, FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 `Adjacency.adjacent_universal`：去掉 `[Nonempty ι]` -/

/-- **【本批 #1】** `adjacent_universal` 的无 `[Nonempty]` 版。

原：`(n m : ι) [Nonempty ι] : ¬ Adjacent (fun _ _ => True) n m`。
本：去掉 `[Nonempty ι]`，用参数 `n : ι`（`m : ι` 亦可）作为见证。

**选择公理**：**不使用**（纯构造，`⟨n⟩` 即为见证）。 -/
theorem adjacent_universal_noNonempty {ι : Type u} (n m : ι) :
    ¬ Adjacent (fun _ _ : ι => True) n m := by
  rintro ⟨-, hno⟩
  -- `[Nonempty ι]` 的见证直接取参数 `n`（原本取的是 `Classical` 之外的任取元素）
  exact hno ⟨n, trivial, trivial⟩

/-! ## §2 `InvarianceContentful.invariance_iff_const`：去掉 `[Nonempty E]` -/

/-- **【本批 #2】** `invariance_iff_const` 的无 `[Nonempty]` 版。

原：`{E : Type} [Nonempty E] (f : E → ℝ) : (∀ e e', f e = f e') ↔ ∃ c, ∀ e, f e = c`。
本：去掉 `[Nonempty E]`。

**空型情形**：两边皆空真（右边取 `c := 0`，内层全称空真）。
**非空情形**：走原证的同一路径。

**选择公理**：**不使用** `Classical.arbitrary`；非空分支用
`Classical.choice` 于 `hK : Nonempty E` 上（`Nonempty` 消去，即 `Classical.choice`
作用于**给定**的 `Nonempty E` 证明；这是 `Nonempty` 的**消去规则**，
在 Lean 4 中由 `Classical.choice` 实现，与 `Classical.arbitrary` 同源）。
⚠ 亦可写成 `hK.some`（`Nonempty.some`，同样是 choice）。此处明说。 -/
theorem invariance_iff_const_noNonempty {E : Type u} (f : E → ℝ) :
    (∀ e e' : E, f e = f e') ↔ ∃ c : ℝ, ∀ e : E, f e = c := by
  constructor
  · intro h
    -- 目标 `∃ c, ∀ e, f e = c`。对 `E` 是否空分类。
    by_cases hE : Nonempty E
    · -- 非空：取 `f` 在任一元素处的值
      exact ⟨f hE.some, fun e => h e hE.some⟩
    · -- 空型：任何 `c` 都满足（内层全称空真）
      exact ⟨0, fun e => absurd ⟨e⟩ hE⟩
  · rintro ⟨c, hc⟩ e e'
    rw [hc e, hc e']

/-! ## §3 `ObsEstimationStrong`：去掉 `chooseEstimator` 两条的 `[Nonempty X]` -/

/-- **【本批 #3】** `chooseEstimator_of_exists` 的无 `[Nonempty]` 版。

原：`[Nonempty X] {h : X → Y} {y : Y} (hh : ∃ x, h x = y) :
      chooseEstimator h y = Classical.choose hh`。
本：去掉 `[Nonempty X]`，把实例位在**陈述里**显式填成 `⟨Classical.choose hh⟩`
（`chooseEstimator` 实际绑定顺序：`{X} {Y} [Nonempty X] (h) (y)`，
`PseudoMetricSpace` 被 Lean `autoBoundImplicit` 剔除，故 `@` 展开只有 4 个参数）。

**选择公理**：使用 `Classical.choose`（于 `hh`）——**与原定理相同**，
本版本**不增加**任何选择公理使用。 -/
theorem chooseEstimator_of_exists_noNonempty {X Y : Type*}
    {h : X → Y} {y : Y} (hh : ∃ x, h x = y) :
    @FateV2.Modeling.RA14Strong.chooseEstimator X Y ⟨Classical.choose hh⟩ h y
      = Classical.choose hh := by
  classical
  unfold FateV2.Modeling.RA14Strong.chooseEstimator
  rw [dif_pos hh]

/-- **【本批 #3b】** `chooseEstimator_apply_of` 的无 `[Nonempty]` 版。

原：`[Nonempty X] {h : X → Y} (hinj : Injective h) (x : X) :
      chooseEstimator h (h x) = x`。
本：去掉 `[Nonempty X]`，由参数 `(x : X)` 在陈述里显式构造 `⟨x⟩`。

**选择公理**：使用 `Classical.choose`（经 (3)），**与原定理相同**。 -/
theorem chooseEstimator_apply_of_noNonempty {X Y : Type*}
    {h : X → Y} (hinj : Function.Injective h) (x : X) :
    @FateV2.Modeling.RA14Strong.chooseEstimator X Y ⟨x⟩ h (h x) = x := by
  have hex : ∃ x' : X, h x' = h x := ⟨x, rfl⟩
  have hval : @FateV2.Modeling.RA14Strong.chooseEstimator X Y ⟨x⟩ h (h x)
      = Classical.choose hex := by
    classical
    unfold FateV2.Modeling.RA14Strong.chooseEstimator
    rw [dif_pos hex]
  rw [hval]
  exact hinj (Classical.choose_spec hex)

end FateV2.Predict.NonemptyFree3
end FateV2.Predict