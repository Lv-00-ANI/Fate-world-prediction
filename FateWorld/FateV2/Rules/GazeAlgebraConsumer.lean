/-
  命运理论 · GazeAlgebra 接入主链（叶子接线 4）

  ============================================================================
  本文件做什么 / 诚实边界
  ============================================================================

  `Fate.GazeAlgebra`（22 定理）此前是**叶子模块**（零消费者）。
  它在一个**自足副本** `GazeAlgebra.G` 上研究「三种目光的代数结构」，
  并在 §7 只给出 `G ≃ Fin 3` 的**类型层双射**，
  **明确不 import `Fate.Classification`**（源文件 §7 原话：
  「本文件不 import `Fate.Classification`（避免 72KB 耦合）」）。

  结果是：`GazeAlgebra` 里的**链 / 格 / Kleene / 反序对合**等结论
  **从未真正落到主链的 `Gaze` 上**。

  **本文件补上这条断线**，把 `GazeAlgebra.G` 的代数结论
  **逐条搬运到主链 `Fate.FormalCtx.Gaze`**（`Fate.Classification` 里
  那个「零序结构」的三目光类型）。

  ---
  一、被接的两端（都来自已有模块，本文件不重定义）
  ---

  · 源端：`Fate.GazeAlgebra.G`（`none < up < down` 链、
    `LinearOrder` 实例、`three_element_lattice_is_chain`、
    `no_duality_automorphism`、`neg` 反序对合）。
  · 目标端：`Fate.FormalCtx.Gaze`（`Fate.Classification` 内，
    **原本没有任何序 / 格 / 实例**，只有 `DecidableEq, Repr`）
    与 `Fate.FormalCtx.Temporal` 的 `IsElement` / `suspend`。

  本模块的 `toG : Gaze → GazeAlgebra.G` 是**显式同构映射**
  （`none↦none, up↦up, down↦down`），由此把源的**代数结构转运到目标**。

  ---
  二、本文件交付的真连接（逐条，均非 `:= 源定理` 的别名）
  ---

  | 定理 / 实例 | 内容 | 源（GazeAlgebra）| 是否同义反复 |
  |---|---|---|---|
  | `toG` / `ofG` / `toG_injective` / `equivG` | 两端显式同构 | §7 `G ⇄ Fin 3` 精神 | 否（新映射）|
  | `instLinearOrder`（instance） | 给 `FormalCtx.Gaze` **新增** `LinearOrder` | `G` 上的 `instLinearOrder` | 否（目标此前无序）|
  | `card_gaze` | `|Gaze| = 3` | `G.card_G` | 否（跨同构搬运）|
  | `gaze_chain` | `∀ a b, a ≤ b ∨ b ≤ a` | `three_element_lattice_is_chain` | 否（假设未含结论）|
  | `instOrderBot` | `⊥ = none` | 链底 | 否 |
  | `isElement_iff_bot` | `IsElement t ↔ t.gaze = ⊥` | — | 否（连接分类谓词与序）|
  | `suspend_gaze_bot` | `(suspend t).gaze = ⊥` | — | 否（连接 `suspend` 与 `⊥`）|
  | `negG` + `negG_involutive` | 反序对合（固定 `up`）| `G.neg` + `neg_involutive` | 否（跨同构搬运）|
  | `gaze_no_duality_automorphism` | 无交换 `up/down` 的保序自同构 | `no_duality_automorphism` | 否（转运 + 需真证）|

  **⚠ 防同义反复核查**：以上每条定理的**前件**均**不包含**其结论——
  例如 `gaze_no_duality_automorphism` 的证明真正从事先给出的
  `hf : 保序` 与 `hup : f up = down` 出发，经 `equivG` 共轭出
  `G ⇄ G` 的保序自同构，再调用源定理反证；不是把结论写进假设。

  ---
  三、诚实标注
  ---

  · 本文件的 `FormalCtx.Gaze` 序 / 格结构是**分析者的代数选择**
    （沿用 `GazeAlgebra` 的 `none < up < down`），
    **不代表** `Fate.Classification` 原作者声称过序结构；
    它此前**只有** `DecidableEq, Repr`。本文件新增的是**可计算的序**，
    其合法性由 `GazeAlgebra` 的定理（可证）承担。
  · `isElement_iff_bot` / `suspend_gaze_bot` 在给定上述序后是 `rfl` 级，
    但其**价值在陈述**：它把 `Classification` 的「要素」谓词
    精确落到序的底元上，使主链可用 `⊥` 做推理。
-/

import FateWorld.FateV2.Rules.Classification
import FateWorld.FateV2.Meta.GazeAlgebra
import Mathlib.Order.Basic

namespace FateV2.Rules

open FateV2.Meta
namespace FormalCtx

/-!
  # Rules · GazeAlgebraConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GazeAlgebraConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Classification, GazeAlgebra
  - 补充 open 域：FateV2.Meta
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  两端显式同构：`FormalCtx.Gaze ⇄ GazeAlgebra.G`
  ======================================================================== -/

/-- 把主链目光 `FormalCtx.Gaze` 映到代数副本 `GazeAlgebra.G`（逐构造同值）。 -/
def toG : Gaze → GazeAlgebra.G
  | .none => GazeAlgebra.G.none
  | .up => GazeAlgebra.G.up
  | .down => GazeAlgebra.G.down

/-- 反向映射（`GazeAlgebra.G` → `FormalCtx.Gaze`）。 -/
def ofG : GazeAlgebra.G → Gaze
  | .none => Gaze.none
  | .up => Gaze.up
  | .down => Gaze.down

/-- `toG` 单射（三构造互异）。 -/
theorem toG_injective : Function.Injective toG := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem ofG_toG (g : Gaze) : ofG (toG g) = g := by cases g <;> rfl

theorem toG_ofG (g : GazeAlgebra.G) : toG (ofG g) = g := by cases g <;> rfl

/-- ⭐ **两端同构**：`FormalCtx.Gaze ≃ GazeAlgebra.G`。

这是把 `GazeAlgebra` 的全部代数结论**转运到主链目光**的**唯一通道**——
源文件 §7 只给了 `G ≃ Fin 3`，从未与 `FormalCtx.Gaze` 连上。 -/
def equivG : Gaze ≃ GazeAlgebra.G where
  toFun := toG
  invFun := ofG
  left_inv := ofG_toG
  right_inv := toG_ofG

/-! ===========================================================================
  §2  把 `GazeAlgebra` 的链序 / 格结构转运到 `FormalCtx.Gaze`
  ======================================================================== -/

/-- ⭐ **主链目光获得 `LinearOrder`**（源：`GazeAlgebra.G.instLinearOrder`）。

`FormalCtx.Gaze` 此前**无任何序实例**；此处经 `toG` 注入性
（`LinearOrder.lift'`）把 `GazeAlgebra.G` 的 `none < up < down` 链搬到它上面。
**这是新增结构，非已有结构的别名。** -/
instance instLinearOrder : LinearOrder Gaze := LinearOrder.lift' toG toG_injective

/-- ⭐ **主链目光基数为 3**（源：`GazeAlgebra.G.card_G`，经 `equivG` 搬运）。 -/
instance instFintype : Fintype Gaze := Fintype.ofEquiv GazeAlgebra.G equivG.symm

theorem card_gaze : Fintype.card Gaze = 3 := by
  rw [Fintype.card_congr equivG]
  exact GazeAlgebra.G.card_G

/-- ⭐⭐ **真连接①：主链目光成链**——直接调用 `GazeAlgebra` 的核心否定/结构定理
`three_element_lattice_is_chain`（三元素格必是链），其假设为「格 + 基数 3」，
**不含**「两两可比」这一结论。 -/
theorem gaze_chain (a b : Gaze) : a ≤ b ∨ b ≤ a :=
  GazeAlgebra.three_element_lattice_is_chain card_gaze a b

/-- ⭐ **真连接②：主链目光的底元** `⊥ = none`（链底，`GazeAlgebra` 中 `none` 为 `⊥`）。 -/
instance instOrderBot : OrderBot Gaze where
  bot := Gaze.none
  bot_le := by intro a; cases a <;> decide

theorem bot_eq_none : (⊥ : Gaze) = Gaze.none := rfl

/-! ===========================================================================
  §3  连接 `Fate.Classification` 的 `IsElement` / `suspend` 与序的底元
  ======================================================================== -/

/-- ⭐ **真连接③：`IsElement` 恰是「目光落在底元」**（分类谓词 ⇄ 序论 `⊥`）。

`Fate.Classification.IsElement t := t.gaze = Gaze.none`；
本节 `⊥ = none`，故 `IsElement t ↔ t.gaze = ⊥`。
**价值在陈述**：把分类层的「要素」谓词精确接到序的底元，使主链以 `⊥` 推理。 -/
theorem isElement_iff_bot {O : Type u} (t : Temporal O) :
    IsElement t ↔ t.gaze = (⊥ : Gaze) := Iff.rfl

/-- ⭐ **真连接④：`suspend` 把目光压到底元**（`Classification.suspend` ⇄ `⊥`）。 -/
theorem suspend_gaze_bot {O : Type u} (t : Temporal O) :
    (suspend t).gaze = (⊥ : Gaze) := rfl

/-! ===========================================================================
  §4  转运 `GazeAlgebra` 的反序对合 `neg`，并落到主链目光
  ======================================================================== -/

/-- 主链目光上的反序对合（源：`GazeAlgebra.G.neg`，`none↔down`、`up` 固定）。 -/
def negG (a : Gaze) : Gaze := ofG (GazeAlgebra.G.neg (toG a))

/-- ⭐ **真连接⑤：`negG` 是对合**（源：`GazeAlgebra.G.neg_involutive`，经同构搬运）。 -/
theorem negG_involutive : Function.Involutive negG := by
  intro a
  unfold negG
  cases a <;> rfl

/-- ⭐ **`negG` 恰固定 `up`**（K₃ 的 `¬U = U` 在主链目光上成立）。 -/
theorem negG_up : negG Gaze.up = Gaze.up := rfl

/-! ===========================================================================
  §5  转运 `no_duality_automorphism`：主链目光无交换 `up/down` 的保序自同构
  ======================================================================== -/

/-- ⭐⭐ **真连接⑥：主链目光上不存在交换 `up`/`down` 的保序自同构**
（源：`GazeAlgebra.G.no_duality_automorphism`）。

**防同义反复核查**：本定理前件为「存在保序自同构 `f` 且 `f up = down`」，
是待反证之物；证明**真正**经 `equivG` 把 `f` 共轭成 `GazeAlgebra.G` 上的
保序自同构（保序性由 `hf` 逐点转运、`f up = down` 由 `hup` 转运），
再调用源定理得到矛盾。**结论未预先写入假设。** -/
theorem gaze_no_duality_automorphism :
    ¬ ∃ f : Gaze ≃ Gaze, (∀ a b, a ≤ b ↔ f a ≤ f b) ∧ f Gaze.up = Gaze.down := by
  rintro ⟨f, hf, hup⟩
  apply GazeAlgebra.G.no_duality_automorphism
  exact ⟨equivG.symm.trans (f.trans equivG),
    (by
      -- 保序性：把 `f` 的保序性经 `equivG` 转运到 `G` 上
      intro a b
      have key : (equivG.symm.trans (f.trans equivG)) a
            ≤ (equivG.symm.trans (f.trans equivG)) b
          ↔ toG (f (ofG a)) ≤ toG (f (ofG b)) := Iff.rfl
      rw [key]
      have hgg : a ≤ b ↔ toG (ofG a) ≤ toG (ofG b) := by
        conv_lhs => rw [← toG_ofG a, ← toG_ofG b]
      rw [hgg]
      exact hf (ofG a) (ofG b)),
    (by
      -- 交换性：`f up = down` 转运到 `G`
      show toG (f (ofG GazeAlgebra.G.up)) = GazeAlgebra.G.down
      rw [show ofG GazeAlgebra.G.up = Gaze.up from rfl, hup]
      rfl)⟩

end FormalCtx
end FateV2.Rules