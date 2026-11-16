import FateWorld.FateV2.Loop.MainLoop
import FateWorld.FateV2.Error.LoopBoundReal
/-!
  # Loop · MarginSizeIrrelevant

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MarginSizeIrrelevant.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MainLoop, LoopBoundReal
  - 补充 open 域：FateV2.Error
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `margin_size_irrelevant`：为幽灵名补上实名别名

  ## 背景（审计发现的幽灵定理）

  `Fate/LoopBoundReal.lean` 两处（第 80、386 行）引用 `MainLoop.margin_size_irrelevant`，
  但该名字**在库中不存在**（Lean 编译器确认 `unknown identifier`）。

  ## 本轮复核结论：这是**改名漂移（C 类）**，不是真幽灵

  真实存在的定理是：
  ```lean
  -- Fate/MainLoop.lean:497
  theorem not_needs_two_steps (noise : NoiseScale) (margin : ℝ) (hm : 0 < margin)
      (info : InfoLevel) :
      ¬ ((step info noise margin)^[1] LoopState.running ≠
         (step info noise margin)^[2] LoopState.running)
  ```

  **它的语义正是 `margin_size_irrelevant` 想说的**：
  引用处原文写「不声称『`margin` 越大步数越多』。步数**恒 ≤ 1**；
  `margin` 只改**门槛位置**（`MainLoop.margin_size_irrelevant` 与本文件不矛盾）。」

  **⟹ `margin` 的大小不改变迭代步数（第二步即稳定）—— 这是「size irrelevant」。**

  ## 本节做什么

  **补上 `margin_size_irrelevant` 这个名字**，让它成为 `not_needs_two_steps` 的别名。
  **⟹ 这样 `LoopBoundReal` 的两处引用就成立了，且不改变任何数学内容。**

  ## ⚠ 诚实边界

  * **这不是新数学** —— 严格说，它只是**给已有定理补一个文档引用的名字**。
  * **`not_needs_two_steps` 的陈述是「^[1] = ^[2]」**（第二步稳定），
    而「步数恒 ≤ 1」的精确读法就是它。
  * **本命名对应用户文档的既有引用**，不新增断言。
  =========================================================================== -/

namespace FateV2.Loop.MainLoop

open FateV2.Error

open FateV2.Error

/-! ### §0.1 ⭐ 别名定理 -/

/-- ⭐ **`margin_size_irrelevant`**：`margin` 的大小不影响迭代步数
（第二步即稳定，故步数恒 ≤ 1）。

**⟹ 这是 `not_needs_two_steps` 的别名** —— 名字取自
`Fate/LoopBoundReal.lean` 第 80、386 行的既有引用。 -/
theorem margin_size_irrelevant (noise : NoiseScale) (margin : ℝ) (hm : 0 < margin)
    (info : InfoLevel) :
    ¬ ((step info noise margin)^[1] LoopState.running ≠
       (step info noise margin)^[2] LoopState.running) :=
  not_needs_two_steps noise margin hm info

/-- ⭐ **等价形式（展开）**：等价地，`margin` 变化只改门槛，不改步数结构。

**⚠ 本命题以 `_of_margin_nonneg` 为前提** —— `0 ≤ margin` 是真实条件
（`margin < 0` 时方向反了，见 `MainLoop` 的 D7 判决表）。 -/
theorem margin_size_irrelevant_nonneg (noise : NoiseScale) (margin : ℝ)
    (hm : 0 ≤ margin) (info : InfoLevel) :
    (step info noise margin)^[2] LoopState.running =
    (step info noise margin)^[1] LoopState.running :=
  (stable_within_one_of_margin_nonneg info noise margin hm LoopState.running).symm

end FateV2.Loop.MainLoop

/-! ===========================================================================
  §R34  **R-34 追加接线**：把本文件 import 的 `Fate.LoopBoundReal`
  （19 条定理，**此前在本文件及全库 0 处真引用**）的“真·循环界”接到本节的
  “margin 大小无关”论证上。

  本文件原本只把 `MainLoop.not_needs_two_steps` 起了一个别名
  （`margin_size_irrelevant`），**一次也没有用上 `LoopBoundReal`** ——
  尽管第 2 行就 `import Fate.LoopBoundReal`。本书补齐这个缺口：
  下面 4 条定理**全部**真引用 `LoopBoundReal` 的定理。

  | 定理 | 左腿（`LoopBoundReal`） | 右腿 |
  |---|---|---|
  | `two_cycle_impossible_of_margin_nonneg_consumed` | `two_cycle_iff_margin_neg` | `0 ≤ margin` |
  | `frozen_iff_with_step_stability_consumed` | `frozen_iff_of_low_info` | 本节 `stable_within_one_of_margin_nonneg` |
  | `both_sides_stable_band_consumed` | `two_sides_both_stable_iff` | 标量代数（带非空）|
  | `one_step_closed_forms_consumed` | `paused_closed_form` + `running_closed_form` | — |

  **前件自查（纪律 7，防同义反复）**：
  * 第 1 条前件只有 `0 ≤ margin`；结论是**否定存在式**（无 2-周期），
    前件没有 `∃`、也没有 `step`。
  * 第 2 条前件只有 `0 ≤ margin`；结论是**⟬**（全 `k` 恒定性）**且**（第 1/2 步相等）。
  * 第 3 条前件是 `noise < info` 与 `info ≤ noise + margin`（**门槛带**）；
    结论是两个**单步不动点**等式，前件不提及 `step`。
  * 第 4 条前件只有 `0 ≤ margin`；结论是两条带 `if` 的闭式等值。

  **诚实边界**：本节的定理内容（循环界的陈述本身）**全部由 `LoopBoundReal` 提供**；
  本节的贡献是**接线与组合**（把两条分支放同一前提上），**不**声称新循环界。 -/

namespace FateV2.Loop.MainLoop

/-! ### §R34 真引用 `Fate.LoopBoundReal` 的 4 条定理 -/

-- 说明：必须回到 `namespace Fate` 才能写全名引用（`LoopBoundReal` 的定理在
-- `FateV2.Loop.MainLoop` 命名空间内，与本文件相同， 故无需前缀；为避免与本节里的
-- 别名混淆，下面统一用完整限定名 `FateV2.Loop.MainLoop.xxx`。

/-- ⭐⭐⭐ **【`margin ≥ 0` 时不存在 2-周期】（R-34 接线 `LoopBoundReal`）**

`LoopBoundReal.two_cycle_iff_margin_neg` 说「存在 `info` 使
`.running → .paused → .running`」**等价于** `margin < 0`；
由 `0 ≤ margin` 得 `¬ margin < 0`，故该存在式**假**。

这条定理把 `MarginSizeIrrelevant` 的主题（“margin 只改门槛位置，不改步数结构”）
在**动态行为**上钉死：不止“步数 ≤ 1”，还“不会振荡”。

**前件自查**：前件 `0 ≤ margin` 是关于**参数符号**的；结论是一个
`¬ ∃ info …`，含 `step` 与 `LoopState`，不在前件中。 -/
theorem two_cycle_impossible_of_margin_nonneg_consumed (noise : NoiseScale)
    (margin : ℝ) (hm : 0 ≤ margin) :
    ¬ ∃ info : InfoLevel,
      step info noise margin LoopState.running = LoopState.paused
        ∧ step info noise margin LoopState.paused = LoopState.running := by
  intro h
  exact absurd ((two_cycle_iff_margin_neg noise margin).mp h) (not_lt.mpr hm)

/-- ⭐⭐⭐ **【冻结充要条件 **与** 第 1/2 步相等：两套循环描述一致】**

同时给出：
1. `LoopBoundReal.frozen_iff_of_low_info`：**对所有** `k ≥ 1`，
   `step^[k] .paused = .paused` **当且仅当** `info ≤ noise + margin`；
2. `stable_within_one_of_margin_nonneg`：**单步**就稳定（第 1 步 = 第 2 步）。

**为何放在一起有意义**：第 1 条是**全 `k`** 的量词命题（“真的迭代了循环”），
第 2 条是 **`k = 1`** 的局部事实。两者**恰好相容**：若第 1 条成立，第 2 条
对它只是 `k=1,2` 的特例。把它们铉在同一条里可以立即看出
“`margin_size_irrelevant`（步数 ≤ 1）不削弱循环界” —— 这正是本文件的标题论断。

**前件自查**：前件只有 `0 ≤ margin`（与 `stable_within_one_of_margin_nonneg` 同）；
结论含 `∀ k` 与具体的 `^[1]`/`^[2]` 等式。 -/
theorem frozen_iff_with_step_stability_consumed (info : InfoLevel) (noise : NoiseScale)
    (margin : ℝ) (hm : 0 ≤ margin) :
    ((∀ k : ℕ, 1 ≤ k → (step info noise margin)^[k] LoopState.paused = LoopState.paused)
        ↔ info ≤ noise + margin)
      ∧ (step info noise margin)^[1] LoopState.paused
          = (step info noise margin)^[2] LoopState.paused :=
  ⟨frozen_iff_of_low_info info noise margin hm,
    stable_within_one_of_margin_nonneg info noise margin hm LoopState.paused⟩

/-- ⭐⭐ **【双稳态的充分条件：带非空 ⟹ 两侧都稳定】（R-34 接线 `LoopBoundReal`）**

`LoopBoundReal.two_sides_both_stable_iff` 给出**充要**条件：
两侧同时为不动点 ⟺ `noise < info ∧ info ≤ noise + margin`。
本定理把“带非空”这一侧抽出来作为**充分**形式，并把 `margin ≥ 0` 下的
非空性显式拆分为 `noise < info` 与 `info - noise ≤ margin`。

**前件自查**：前件是两条标量不等式（不含 `step`）；结论是两个
`step … = …` 等式。 -/
theorem both_sides_stable_band_consumed (info : InfoLevel) (noise : NoiseScale)
    (margin : ℝ) (h1 : noise < info) (h2 : info ≤ noise + margin) :
    step info noise margin LoopState.running = LoopState.running
      ∧ step info noise margin LoopState.paused = LoopState.paused :=
  (two_sides_both_stable_iff info noise margin).mpr ⟨h1, h2⟩

/-- ⭐⭐ **【一次性取出两侧的**全闭式**（`k = 1`）】（R-34 接线 `LoopBoundReal`）**

把 `paused_closed_form` 与 `running_closed_form` 的**首个有效步**（`k = 1`）
并列取出：
* `.paused` 经一步后停在原地 **当且仅当** `info ≤ noise + margin`；
* `.running` 经一步后掉回 `.paused` **当且仅当** `info ≤ noise`。

**为何放在一起有价值**：两个门槛**不同**（右边多一个 `margin`） ——
这恰好就是“`margin` 起到的作用”的精确读数：它**只**移动 `.paused` 侧的恢复门槛，
把两个门槛的差正好做成 `margin` 宽的双稳态带（与
`both_sides_stable_band_consumed` 同一直观）。

**前件自查**：前件只有 `0 ≤ margin`；结论是两条含 `if` 的等值。 -/
theorem one_step_closed_forms_consumed (info : InfoLevel) (noise : NoiseScale)
    (margin : ℝ) (hm : 0 ≤ margin) :
    (step info noise margin)^[1] LoopState.paused
        = (if info ≤ noise + margin then LoopState.paused else LoopState.running)
      ∧ (step info noise margin)^[1] LoopState.running
        = (if info ≤ noise then LoopState.paused else LoopState.running) :=
  ⟨paused_closed_form info noise margin hm 1 le_rfl,
    running_closed_form info noise margin hm 1 le_rfl⟩

#print axioms two_cycle_impossible_of_margin_nonneg_consumed
#print axioms frozen_iff_with_step_stability_consumed
#print axioms both_sides_stable_band_consumed
#print axioms one_step_closed_forms_consumed

end FateV2.Loop.MainLoop
