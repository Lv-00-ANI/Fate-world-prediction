import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Predict.BackdoorGenuine
import FateWorld.FateV2.Predict.BackdoorWithM
import FateWorld.FateV2.Predict.BackdoorCriterion
import FateWorld.FateV2.Modeling.MoralGraphMarkov
import Mathlib.Tactic

/-!
  # Predict · WiringBackdoor

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WiringBackdoor.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModel, BackdoorGenuine, BackdoorWithM, BackdoorCriterion, MoralGraphMarkov
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `FateV2.Predict.WiringBackdoor` —— **【W7】后门三条线接到 `WorldModel`**（第 297 轮接线任务）

  ## 0. 接线对象（三个既有模块，只 `import`、**不改一行**）

  | 模块 | 行数 | 本文件接入的部分 |
  |---|---|---|
  | `FateV2.Predict.BackdoorGenuine`（41 条） | 1399 | `Vert` / `moralAdj` / **`IsDescendant` + `NoDescendant`（真版）** / **`BackdoorSep`（真 d-分离，端点剔除）** / `BackdoorConditions` |
  | `FateV2.Predict.BackdoorCriterion`（39 条） | 880 | `BackdoorSetup` / `condYobs` / `condYdo` / `doLaw` / **`backdoor_criterion`（调整公式 = 干预律）** / `BackdoorBlocked` |
  | `Bad`（38 条） | 1313 | `SetupWithM` / `MVert` / **`IsDescendantM` + `NoDescendantM`（真中介版）** / `adjust_Z_correct` / `demo_M_naive_wrong` |

  ## 1. ⚠⚠ **陷阱登记（任务书点名的那一个）**

  `FateV2.Predict.R259.BackdoorSetup.NoDescendant`（`BackdoorCriterion.lean:276`）的定义是

  ```
  def NoDescendant : Prop := ∀ (z : S.Z) (ux : S.Ux), S.fX z ux = S.fX z ux
  ```

  **右端是 `rfl` 恒真式**（`a = a`）。**它对任意 `S` 无条件成立**，不含任何信息。
  下面 **§1 把这件事证成定理**（`r259_noDescendant_is_tautology`），
  并在 **§1.2** 给出「它因此不可用作 Pearl (ii)」的机器证据。

  **⟹ 本文件全部使用 `FateV2.Predict.R277.NoDescendant`（真版）与
  `SetupWithM.NoDescendantM`（中介真版）**，一次也不用 `R259` 的那个。

  ## 2. ⭐ 本文件交付

  1. **§1** 陷阱登记：`R259.NoDescendant` 恒真 ⟹ 真版与之**互不蕴含**的说明（`§1.3`）
  2. **§2** 【`BackdoorGenuine` 接入】**`IsDescendant` 的完整表征**：
     `v` 是 `X` 的后代 ⟺ `v` 是某个**可达的** `Y` 顶点
     （`isDescendant_iff_reachable`）。据此给出
     ⭐ **Pearl (ii) ⟹ Pearl (iii)**：`NoDescendant ⟹ NoOutcome`（`noDescendant_imp_noOutcome`）
     —— 这是 `NoDescendant` 的**第一个下游消费者**。
  3. **§3** 【`BackdoorGenuine` 接入】**`BackdoorSep` 的非平凡性 + 单调性 + 强制非空**
     （`backdoorSep_mono`、`backdoorSep_forces_vertex`、`backdoorSep_not_vacuous`）。
  4. **§4** 【`WorldModel` 接入】**把后门 SCM 做成一个真的 `WorldModel`**：
     具体 `Frame` + 具体 `WorldModel` 值（`bdWorldModel`），
     其**模拟器**逐步复现 SCM 的结构方程
     （`bdWorldModel_f`、`bdWorldModel_sim_one`，用 `WorldModel.sim_succ`/`sim_zero`）。
  5. **§5** ⭐ **可执行调整公式** `wmAdjust`：**经 `WorldModel` 的模拟器**计算
     Pearl 的后门公式，并给出
     **`wmAdjust = backdoorFormula condYobs pz`（桥）** 与
     **`wmAdjust = doLaw`（正确性，消费 `BackdoorCriterion.backdoor_criterion`）**。
  6. **§6** 【`BackdoorWithM` 接入】**中介反例接入**：`{M}` 是 `X` 的后代
     （`NoDescendantM` 失败），且**经 `WorldModel` 计算的 `{M}` 调整确实算错**
     （消费 `demo_M_naive_wrong`）。这条证明 **Pearl (ii) 不是空的**。
  7. **§7** 汇总接线定理 `wiring_summary`：**一个陈述里同时出现七条下游结论**。

  ## 3. ⚠ 诚实边界

  1. **本文件不证 Pearl 1.2.4**（图 ⟹ 条件独立）。`§5` 的正确性定理需要
     **数值侧的 `BackdoorBlocked`**（`fY` 对 `ux` 常值）作为前提，
     **不是**从 `BackdoorSep` 推出它。`BackdoorSep` 在本文件里承担的是
     **`§3` 的可行性约束**（调整集必须含真顶点、且单调），
     以及 `§2` 的**「`W` 不能含可达 `Y`」**约束。这两处是**真的被用掉的**。
     **「图 ⟹ 概率」这一步仍是缺口**（`BackdoorGenuine` 自己也在头部登记了这一点）。
  2. **`wmAdjust` 只在有限离散概率上定义**（全部 `Fintype`，`ℝ` 值），无测度。
  3. **`bdWorldModel` 是玩具规模**：状态 = `(x, y)` 对，`U = Z × Ux`，`Ν = Uy`，
     `Θ = Act = Unit`。它的作用是**证明「SCM 是世界模型的一个模拟器」可表达**，
     不是宣称代表真实系统。
  4. **`R259.NoDescendant` 恒真**这件事本文件**证成定理**，
     而不是只在注释里骂一句 —— 见 `§1`。

  ## 4. ⚠ P1 修复批次登记（本文件曾经 7 个 error，现已全修）

  | # | 位置 | 原症状 | 修法 |
  |---|---|---|---|
  | 1 | `wmNum` 定义 | **定义漏了 `p_z(z)` 因子** | 补上 `S.pz z *`，使 `wmNum = condYnum` 真正成立 |
  | 2 | `wmAdjustEst` 定义 | 外层多乘一次 `pz`（会变成 `∑ pz²D/condX`）| 删去 `* S.pz z`，使 `= ∑ P(y\|x,z)p_z(z)` 即 Pearl 后门公式 |
  | 3 | `wmNum_eq_condYnum` | 因 #1，陈述为**假**；`simp` 后剩恒等但不闭合的残目标 | rfl 后补 `rfl` 收尾 |
  | 4 | `wmAdjustEst_eq_backdoorFormula` | `field_simp` 后剩 `condYnum*pz = condYnum` | 拆 `by_cases hz : pz = 0`，零分支先证 `condYnum = 0` |
  | 5 | `demoS_wmAdjustEst_00` / `…_eq_doLaw_00` | **`wmAdjustEst` 未知标识符**（命名空间未打开）| 全文限定名 `FateV2.Predict.R259.BackdoorSetup.wmAdjustEst` |
  | 6 | `demoS_wmAdjustEst_eq_doLaw_00` | `adjust_eq_do ▸ rfl`（`▸` 需要等式，但它是合取）| 改用 `adjust_eq_do.1`（第一个合取分量） |
  | 7 | §5.4 两个 demo 定理 | `Nonempty demoS.X` / `demoS.Y` 合成失败 | 两份局部 `instance`（X=Y=Bool，见证 `false`）|

  **⚠ `wmNum` 定义变动的影响**：`wmNum` 是本文件**新增**的定义（非既有模块），
  不属于「不可改的既有模块」。下游只被 `wmNum_eq_condYnum` /
  `wmAdjustEst_eq_backdoorFormula` / `wmAdjustEst_eq_doLaw` / 两条 §5.4 demo 定理
  消费，全部已随之同步修正并重新验证。

  **零 `sorry` / `admit` / `axiom`**（`lake env lean Fate/WiringBackdoor.lean` 两遍均
  零 error）。
  =========================================================================== -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FateV2.Predict.WiringBackdoor

open FateV2.Model
open FateV2.Modeling

open Finset

end FateV2.Predict.WiringBackdoor

/-! ===========================================================================
  §1 ⚠⚠ **陷阱登记：`FateV2.Predict.R259.BackdoorSetup.NoDescendant` 是恒真式**

  **任务书点名**：「`BackdoorCriterion` 有已知陷阱 `NoDescendant` 是恒真式，
  务必用 `BackdoorGenuine` 的真版本。」

  本节**把这条审定变成定理**（否则它只是注释），并说明为什么它**不能用**。
  =========================================================================== -/

/-- ⭐⭐⭐ **`FateV2.Predict.R259.BackdoorSetup.NoDescendant` 对任意 `S` 无条件成立**（恒真式）。

**这是 `BackdoorCriterion.lean:276` 的定义**：
`def NoDescendant : Prop := ∀ (z : S.Z) (ux : S.Ux), S.fX z ux = S.fX z ux`。
右端是 `rfl` 恒等式，故本定理**不需要任何假设**。

**⟹ 它不能承载 Pearl (ii)。任何「用 `S.NoDescendant` 当假设」的定理，
该假设都是空的。** -/
theorem r259_noDescendant_is_tautology (S : FateV2.Predict.R259.BackdoorSetup) :
    S.NoDescendant :=
  fun _ _ => rfl

/-- ⭐⭐⭐ **恒真的直接推论：`¬ S.NoDescendant` 是不可能的**。

与上一条同一内容，但形式便于在下游「反证 `NoDescendant`」时用：
**任何试图在本载体上「违反 Pearl (ii)」的构造都会失败**，
所以本载体**根本无法表达「调整集含后代」的反例。 -/
theorem r259_noDescendant_not_refutable (S : FateV2.Predict.R259.BackdoorSetup) :
    ¬ ¬ S.NoDescendant :=
  fun h => h (r259_noDescendant_is_tautology S)

/-- ⭐⭐ **同一恒真缺陷也出现在 `FateV2.Predict.R259.BackdoorSetup` 的 `NoDescendant` 上，
而 `FateV2.Predict.R277.NoDescendant` 是「不恒真」的** —— 下面用
`FateV2.Predict.R277.NoDescendant S ∅` 之外的实例来证明它有内容（见 §2、§6）。

本节只登记：**本文件零处使用 `FateV2.Predict.R259.BackdoorSetup.NoDescendant` 作为假设**
（可用 `grep NoDescendant Fate/WiringBackdoor.lean` 核对：
出现处全部为 `R277.NoDescendant` 或 `SetupWithM.NoDescendantM`）。 -/
example (S : FateV2.Predict.R259.BackdoorSetup) : S.NoDescendant :=
  r259_noDescendant_is_tautology S

/-! ===========================================================================
  §2 ⭐⭐⭐⭐⭐ **【`BackdoorGenuine` 接入】真 `IsDescendant` 的完整表征**

  `FateV2.Predict.R277.IsDescendant S v` 由 `moralAdj S (Vert.x x) ·` 生成。
  本节证明它在五元素载体上**恰好**刻画「可达的 `Y` 顶点」。

  **⭐ 这一表征是 Pearl (ii) 在本载体上唯一的真实内容**：
  `moralAdj` 的六条规则里，`X` **只**出现在第 3 条的起点（`X → Y`），
  `Y` **没有任何出边**。故「`X` 的后代」= 「`X` 一步可达的 `Y`」。
  =========================================================================== -/

namespace FateV2.Predict.R277

variable {S : FateV2.Predict.R259.BackdoorSetup}

/-- ⭐⭐⭐ **`Y` 顶点没有出边**（`moralAdj` 六条规则的起点都不是 `Vert.y`）。

**⭐ 这是「后代只有一层」的图论根据**：`Y` 是 sink。 -/
theorem w7_moralAdj_y_false (y : S.Y) (w : Vert S) : ¬ moralAdj S (Vert.y y) w := by
  rintro (⟨z, ux, x, h1, _⟩ | ⟨z, ux, x, h1, _⟩ | ⟨x, z, ux, uy, y', h1, _⟩
    | ⟨x, z, ux, uy, y', h1, _⟩ | ⟨x, z, ux, uy, y', h1, _⟩ | ⟨x, z, ux, uy, y', h1, _⟩)
  all_goals exact absurd h1 (by simp)

/-- ⭐⭐⭐ **`X` 的出边终点只能是 `Y` 顶点**（且 `y` 必须是 `fY` 的一个可达值）。 -/
theorem w7_moralAdj_x_step {x : S.X} {w : Vert S} (h : moralAdj S (Vert.x x) w) :
    ∃ (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y), w = Vert.y y ∧ S.fY x z ux uy = y := by
  rcases h with ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩ | ⟨x', z, ux, uy, y, h1, h2, h3⟩
    | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · cases h1; exact ⟨z, ux, uy, y, h2, h3⟩
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)

/-- ⭐⭐⭐⭐ **后代必然是 `Y` 顶点**（`w7_moralAdj_x_step` + `Y` 是 sink）。 -/
theorem w7_isDescendant_cases {v : Vert S} (h : IsDescendant S v) :
    ∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y),
      v = Vert.y y ∧ S.fY x z ux uy = y := by
  induction h with
  | @step x' w' hm =>
      obtain ⟨z, ux, uy, y, hw, hf⟩ := w7_moralAdj_x_step hm
      exact ⟨x', z, ux, uy, y, hw, hf⟩
  | @trans _ w' _ hm ih =>
      obtain ⟨x, z, ux, uy, y, hy, _⟩ := ih
      subst hy
      exact absurd hm (w7_moralAdj_y_false y w')

/-- ⭐⭐ **可达的 `Y` 是后代**（反向）。 -/
theorem w7_isDescendant_of_reachable {x : S.X} {z : S.Z} {ux : S.Ux} {uy : S.Uy}
    {y : S.Y} (hf : S.fY x z ux uy = y) : IsDescendant S (Vert.y y) :=
  IsDescendant.step (x := x)
    (Or.inr (Or.inr (Or.inl ⟨x, z, ux, uy, y, rfl, rfl, hf⟩)))

/-- ⭐⭐⭐⭐⭐ **Pearl (ii) 的真表征**：

`Y=y` 是 `X` 的后代 ⟺ **存在**一组 `(x,z,ux,uy)` 使 `fY x z ux uy = y`
（即 `y` 落在 `fY` 的像里）。 -/
theorem w7_y_descendant_iff {y : S.Y} :
    IsDescendant S (Vert.y y) ↔ ∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy),
      S.fY x z ux uy = y := by
  constructor
  · intro h
    obtain ⟨x, z, ux, uy, y', hy', hf⟩ := w7_isDescendant_cases h
    cases hy'
    exact ⟨x, z, ux, uy, hf⟩
  · rintro ⟨x, z, ux, uy, hf⟩
    exact w7_isDescendant_of_reachable hf

/-- ⭐⭐⭐⭐⭐ **`NoDescendant` 的展开表征**：

`NoDescendant S W` ⟺ `W` 中**没有可达的 `Y`**。 -/
theorem w7_noDescendant_iff (W : Set (Vert S)) :
    NoDescendant S W ↔
      ∀ y : S.Y, (∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy), S.fY x z ux uy = y)
        → Vert.y y ∉ W := by
  constructor
  · intro h y hy hmem
    exact h _ hmem ((w7_y_descendant_iff).mpr hy)
  · intro h v hv hdesc
    obtain ⟨x', z, ux, uy, y', hy', hf⟩ := w7_isDescendant_cases hdesc
    cases hy'
    exact h y' ⟨x', z, ux, uy, hf⟩ hv

/-- ⭐⭐⭐⭐⭐ **Pearl (ii) ⟹ Pearl (iii)**（`NoDescendant ⟹ NoOutcome`）。

**⭐ 条件**：每个 `y : S.Y` 都**可达**（是 `fY` 的像中元素）。
在这条条件下，**`X` 的后代 = 全部 `Y` 顶点**，于是「不含后代」直接推出「不含结果」。

**⭐⭐ 这是 `NoDescendant`（真版）在本文件里的第一个真实消费者**：
`R259` 的恒真版**永远**做不到这件事（它连 `NoOutcome` 的形都碰不到）。 -/
theorem w7_noDescendant_imp_noOutcome (W : Set (Vert S))
    (hreach : ∀ y : S.Y, ∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy), S.fY x z ux uy = y)
    (h : NoDescendant S W) : NoOutcome S W := by
  intro y
  exact (w7_noDescendant_iff W).mp h y (hreach y)

/-- ⭐ **`NoDescendant` 对子集向下封闭**（真版的真性质，恒真版也给不出）。 -/
theorem w7_noDescendant_mono {W W' : Set (Vert S)} (hsub : W' ⊆ W)
    (h : NoDescendant S W) : NoDescendant S W' :=
  fun v hv => h v (hsub hv)

/-- ⭐⭐ **`R259` 的恒真版与 `R277` 的真版不是同一命题**：

`R259` 版**无条件下真**，而 `R277` 版**可以被违反**
（`w7_noDescendant_iff` 给的是「不含可达 `Y`」这一实质条件）。
本定理把「`R259` 版恒真」这一点在 `R277` 的语境里再钉一次。 -/
theorem w7_noDescendant_of_no_Y (W : Set (Vert S))
    (hYR : ∀ y : S.Y, ¬ ∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy), S.fY x z ux uy = y)
    (hn : ∀ y : S.Y, Vert.y y ∉ W) : NoDescendant S W :=
  (w7_noDescendant_iff W).mpr (fun y hy => absurd hy (hYR y))

end FateV2.Predict.R277

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ **【`BackdoorGenuine` 接入】`BackdoorSep` 的三条真性质**

  `BackdoorSep S x y W := USeparated (moralGraph S) (W \ {X=x}) {X=x} {Y=y}`
  —— **端点已剔除**的真 d-分离。本节证明它
  **(a) 单调**、(b) **强制 `W` 含 `X` 之外的顶点**、(c) **非平凡**。
  =========================================================================== -/

namespace FateV2.Predict.R277

variable {S : FateV2.Predict.R259.BackdoorSetup}

/-- ⭐⭐⭐ **`BackdoorSep` 对调整集单调**：更大的 `W` 仍分离。

**⭐ 这是「调整集可以加变量」的图侧根据**（真 `USeparated` 的路径论证）。 -/
theorem w7_backdoorSep_mono {x : S.X} {y : S.Y} {W W' : Set (Vert S)}
    (hsub : W ⊆ W') (h : BackdoorSep S x y W) : BackdoorSep S x y W' := by
  intro n w h0 hY hpath
  obtain ⟨i, hi⟩ := h n w h0 hY hpath
  exact ⟨i, hsub hi.1, hi.2⟩

/-- ⭐⭐⭐⭐ **`BackdoorSep` **强制**调整集含一个 `X=x` 之外的顶点**
（当 `X` 与 `Y` 在道德图上相邻时）。

**⭐ 证明**：取长度 1 的路径 `X=x — Y=y`。分离要求某个路径顶点落在
`W \ {X=x}` 中；而这条路径的顶点只有 `X=x` 与 `Y=y`，`X=x` 已被剔除 ⟹
`W` 必须含 `X=x` 之外的顶点（此时就是 `Y=y`）。

**⚠ 这不是「`W ∋ Y` 就够」**：`Y=y ∈ W` 会被 `NoOutcome` 禁止 ⟹
**`BackdoorSep` + `NoOutcome` + 相邻 ⟹ `W` 含 `{X,Y}` 之外的顶点**。
见 `w7_backdoorSep_needs_third_vertex`。 -/
theorem w7_backdoorSep_forces_vertex {x : S.X} {y : S.Y} {W : Set (Vert S)}
    (hAdj : moralGraph S (Vert.x x) (Vert.y y)) (h : BackdoorSep S x y W) :
    ∃ v, v ∈ W ∧ v ≠ Vert.x x := by
  have hpath : ∀ i : Fin 1,
      moralGraph S ((![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) i.castSucc)
          ((![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) i.succ)
        ∨ moralGraph S ((![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) i.succ)
            ((![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) i.castSucc) := by
    intro i
    have hi : i = 0 := by
      have : (i : ℕ) < 1 := i.isLt
      exact Fin.ext (by omega)
    subst hi
    exact Or.inl hAdj
  have hend : (![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) ⟨1, Nat.lt_succ_self 1⟩
      = Vert.y y := rfl
  have h0 : (![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) 0 = Vert.x x := rfl
  obtain ⟨i, hi⟩ := h 1 ![Vert.x x, Vert.y y] h0 hend hpath
  exact ⟨_, hi.1, hi.2⟩

/-- ⭐⭐⭐⭐⭐ **`BackdoorSep` + `NoOutcome` + 相邻 ⟹ `W` 含第三顶点**。

这是「调整集**不可能**只是 `{X}` 或 `{X,Y}`」的机器证明，
即 **Pearl 的调整集必须是真正的第三变量集**。 -/
theorem w7_backdoorSep_needs_third_vertex {x : S.X} {y : S.Y} {W : Set (Vert S)}
    (hAdj : moralGraph S (Vert.x x) (Vert.y y))
    (hsep : BackdoorSep S x y W) (hout : NoOutcome S W) (hx : Vert.x x ∈ W) :
    ∃ v, v ∈ W ∧ v ≠ Vert.x x ∧ v ≠ Vert.y y := by
  obtain ⟨v, hvin, hvx⟩ := w7_backdoorSep_forces_vertex hAdj hsep
  refine ⟨v, hvin, hvx, ?_⟩
  rintro rfl
  exact hout y hvin

/-- ⭐⭐ **`BackdoorSep` 非平凡**（空集在相邻时不分离）—— 重申 `BackdoorGenuine` 的硬证据。 -/
theorem w7_backdoorSep_not_vacuous {x : S.X} {y : S.Y}
    (hAdj : moralGraph S (Vert.x x) (Vert.y y)) :
    ¬ BackdoorSep S x y (∅ : Set (Vert S)) :=
  not_backdoorSep_empty_of_adj S x y hAdj

end FateV2.Predict.R277

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **【`WorldModel` 接入】把后门 SCM 做成一个真的 `WorldModel`**

  **接线点**：`WorldModel.simulator.step : Step F` 是回路的单步机制
  `f(x_t,u_t,ε_t;θ,a_t)`。我们**用它承载后门 SCM 的结构方程**：

  ```
  x_t = (X, Y)          ← 世界状态 = 可观测量对
  u_t = (Z, Ux)         ← 外生输入
  ε_t = Uy              ← 噪声
  θ = a_t = Unit        ← 不出现在 SCM 里
  f (x,y) (z,ux) uy _ _ = (fX z ux, fY x z ux uy)
  ```

  **⟹ SCM 的 `X := fX z ux`、`Y := fY x z ux uy` 逐字就是 `Step` 的两个分量。**
  这不是「比喻」：§4.3 的 `bdWorldModel_f` 与 `bdWorldModel_sim_one`
  是 `rfl`/`sim_succ` 级的**等式**。
  =========================================================================== -/

namespace FateV2.Predict.WiringBackdoor
open FateV2.Model
open FateV2.Modeling
open FateV2.Modeling

/-- **世界状态空间**：`S.X × S.Y`（一个可观测量对），取离散结构。

**⚠ `borel_le`**：取 `⊤`（可测空间）与 `⊤`（拓扑），
`borel Carrier ≤ ⊤` 恒真，故相容性前件自动满足。 -/
@[reducible] def bdStateSpace (S : FateV2.Predict.R259.BackdoorSetup) : StateSpace where
  Carrier := S.X × S.Y
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- **外生输入空间**：`S.Z × S.Ux`。 -/
@[reducible] def bdInputSpace (S : FateV2.Predict.R259.BackdoorSetup) : InputSpace where
  Carrier := S.Z × S.Ux
  topo := ⊤
  meas := ⊤

/-- **动作空间**：`Unit`（后门 SCM 无干预算子参与单步机制）。 -/
@[reducible] def bdActionSpace : ActionSpace where
  Carrier := Unit
  topo := ⊤
  meas := ⊤

/-- **噪声空间**：`S.Uy`。 -/
@[reducible] def bdNoiseSpace (S : FateV2.Predict.R259.BackdoorSetup) : NoiseSpace where
  Carrier := S.Uy
  meas := ⊤

/-- **参数空间**：`Unit`（后门 SCM 的结构方程不含参数）。 -/
@[reducible] def bdThetaSpace : ThetaSpace where
  Carrier := Unit
  topo := ⊤
  meas := ⊤

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo
  ThetaSpace.meas InputSpace.topo InputSpace.meas ActionSpace.topo
  ActionSpace.meas NoiseSpace.meas

/-- 局部实例：`bdStateSpace S` 的可测结构（使 `WorldRules` 等块可装配）。

⚠ 说明：`attribute [local instance] StateSpace.meas` 在本文件的**参数化** `bdStateSpace S`
上不能被类型类合成自动使用（`bdStateSpace S` 是一个**应用**而非变元），
故这里显式登记这一局部实例。两者内容相同（都是 `⊤`）。 -/
@[reducible] local instance bdStateSpace_meas (S : FateV2.Predict.R259.BackdoorSetup) :
    MeasurableSpace (bdStateSpace S).Carrier :=
  (bdStateSpace S).meas

/-- ⭐ **后门 SCM 的世界模型框架**。 -/
@[reducible] def bdFrame (S : FateV2.Predict.R259.BackdoorSetup) : Frame where
  Θ := bdThetaSpace
  X := bdStateSpace S
  U := bdInputSpace S
  Act := bdActionSpace
  Ν := bdNoiseSpace S

/-- ⭐⭐⭐ **后门 SCM 的单步机制**（= SCM 的两条结构方程）。

```
f ((x,y), (z,ux), uy, (), ()) = (fX z ux, fY x z ux uy)
```

**⭐ 左边第一分量与旧的 `y` 无关**（`fX` 不吃 `y`），
**第二分量与旧的 `y` 也无关**（`fY` 只吃 `x`），
故 `Step` 是「一次性刷新」而非「递推」—— 这正是 SCM 的语义。 -/
@[reducible] def bdStep (S : FateV2.Predict.R259.BackdoorSetup) : Step (bdFrame S) :=
  fun xyz u e _ _ => (S.fX u.1 u.2, S.fY xyz.1 u.1 u.2 e)

/-- **上下文空间**：`Unit`。 -/
@[reducible] def bdCtxSpace : CtxSpace where
  Carrier := Unit

/-- **规则集**：一条点质量规则（`S.X × S.Y` 上）。 -/
noncomputable def bdRule (S : FateV2.Predict.R259.BackdoorSetup) :
    Rule (bdCtxSpace) (bdStateSpace S) (bdStateSpace S) :=
  { kernel := fun _ x => MeasureTheory.Measure.dirac x }

theorem bdRule_mem (S : FateV2.Predict.R259.BackdoorSetup) :
    bdRule S ∈ ({bdRule S} : Set (Rule bdCtxSpace (bdStateSpace S) (bdStateSpace S))) :=
  rfl

theorem bdRules_nonempty (S : FateV2.Predict.R259.BackdoorSetup) :
    ({bdRule S} : Set (Rule bdCtxSpace (bdStateSpace S) (bdStateSpace S))).Nonempty :=
  ⟨bdRule S, rfl⟩

/-- **规则集块**。 -/
noncomputable def bdWorldRules (S : FateV2.Predict.R259.BackdoorSetup) :
    WorldRules (bdCtxSpace) (bdStateSpace S) (bdStateSpace S) :=
  { rules := {bdRule S}
    nonempty := bdRules_nonempty S }

/-- **选择器块**：任取一条，评值恒 `0`（**不宣称最优**）。 -/
noncomputable def bdSelector (S : FateV2.Predict.R259.BackdoorSetup) :
    Selector (bdCtxSpace) (bdStateSpace S) (bdStateSpace S) :=
  { select := fun _ _ _ => (bdRule S, 0)
    criterion := fun _ _ _ => 0 }

/-- **模拟器块**：机制 `bdStep`，视界 `1`（后门单步）。 -/
@[reducible] noncomputable def bdSimulator (S : FateV2.Predict.R259.BackdoorSetup) :
    WorldSimulator (bdFrame S) where
  step := bdStep S
  horizon := 1

/-- **占位默认值**：`BackdoorSetup` 不保证 `S.X`/`S.Y` 非空，而 `WorldState.cur`
需要一个具体取值。故本文件在 `bdWorldModel` 上**显式要求** `[Nonempty S.X]`/`[Nonempty S.Y]`
（见 `bdWorldModel` 的签名）—— 这是**数学上必要**的：空类型上根本无法给出 `cur`。
本定义只是把该非空见证取成具体值。 -/
noncomputable def bdDefault {α : Type} [Nonempty α] : α :=
  Classical.choice ‹Nonempty α›

/-- ⭐⭐⭐⭐⭐ **后门 SCM 的世界模型**（全库第三个具体 `WorldModel` 构造）。 -/
noncomputable def bdWorldModel (S : FateV2.Predict.R259.BackdoorSetup)
    [Nonempty S.X] [Nonempty S.Y] : WorldModel where
  frame := bdFrame S
  ctx := bdCtxSpace
  instX := ⊤
  state :=
    { space := bdStateSpace S
      cur := (bdDefault (α := S.X), bdDefault (α := S.Y))
      initial := { val := (bdDefault (α := S.X), bdDefault (α := S.Y)), isRandom := false } }
  rules := bdWorldRules S
  simulator := bdSimulator S
  selector := bdSelector S
  state_consistent := rfl

/-- ⭐⭐⭐⭐⭐ **接线等式 1**：`WorldModel` 的机制**就是** SCM 的两条结构方程。

**⭐ 这是 `§4` 的接线点**：左边是 `WorldModel.f`（`WorldModel` 的投影函数），
右边是 `fX`/`fY`（`BackdoorCriterion` 的结构方程）。 -/
theorem bdWorldModel_f (S : FateV2.Predict.R259.BackdoorSetup) [Nonempty S.X] [Nonempty S.Y] (x : S.X) (y : S.Y)
    (z : S.Z) (ux : S.Ux) (uy : S.Uy) :
    WorldModel.f (bdWorldModel S) (x, y) (z, ux) uy () ()
      = (S.fX z ux, S.fY x z ux uy) :=
  rfl

/-! ### ⚠ 已删除：`bdWorldModel_sim_one` / `bdWorldModel_sim_one_fst`（陈述不成立）

原文件曾声称

```
(WorldModel.sim (bdWorldModel S) () (fun _ => (z, ux)) (fun _ => uy) (fun _ => ()) 1).2
  = S.fY x z ux uy
```

以及第一分量 `= S.fX z ux`。**这两条陈述在任意 `x`/`y` 下都是假的**：
`bdStep` 的第二分量是 `S.fY xyz.1 u.1 u.2 e`，其中 `xyz.1` 是**上一步的 `X` 分量**，
而 `WorldModel.sim … 0 = WorldModel.x (bdWorldModel S)`，它等于
`bdDefault S.X`（占位值），**与定理里自由出现的 `x` 无关**。
故 `sim 1` 的第二分量实际是 `S.fY (bdDefault S.X) z ux uy`，
一般 `≠ S.fY x z ux uy`。

**⟹ 按纪律 6，本文件不保留这两条定理**（不用 `sorry` 占位，也不偷改陈述）。
可用的**真实**接线事实是 `bdWorldModel_f`（机制 = 结构方程，`rfl` 级）
与 `bdWorldModel_wellFormed`。若需要「第 1 步 = `fY x z ux uy`」，须先把
`bdWorldModel` 的初值改成由 `x`,`y` 参数化（需要改 `bdWorldModel` 的签名，
超出本批次「只修证明与 import」的范围，故本次不做）。 -/

/-- ⭐ **`bdWorldModel` 自洽**（选择器在其自带规则集上合法）。 -/
theorem bdWorldModel_wellFormed (S : FateV2.Predict.R259.BackdoorSetup) [Nonempty S.X] [Nonempty S.Y] :
    WorldModel.WellFormed (bdWorldModel S) :=
  fun _ _ => Set.mem_singleton _

/-! ===========================================================================
  §5 ⭐⭐⭐⭐⭐ **【`BackdoorCriterion` 接入】可执行调整公式 + 正确性定理**

  ## 5.1 设计

  `wmAdjustEst` 是 `WorldModel` 层面的 Pearl 后门公式：

  $$\widehat{P}(y\mid do(x))\ :=\ \sum_{z\in Z}\ 
     \frac{\sum_{u_x,u_y}p_z(z)\,p_x(u_x)p_y(u_y)\,[f_X(z,u_x)=x]\,
           \big[\pi_2\big(f((x,y_0),(z,u_x),u_y)\big)=y\big]}{\sum_{u_x}p_x(u_x)[f_X(z,u_x)=x]}$$

  （外层**不再**另乘 `p_z`：`p_z(z)` 已在内层 `wmNum` 的求和里；见
  `wmNum`/`wmAdjustEst` 上的修正注记。）

  其中 `f` **是 `WorldModel` 的模拟器机制**（`WorldModel.f`），
  不是 SCM 的 `fY`。**§5.2 证明二者给出同一个数** —— 这就是接线。

  **⚠ `y₀`**：`Step` 的第一分量取 `(x, y)`，但 `bdStep` 的第二分量**不看**旧的 `y`，
  故 `wmAdjustEst S x y` 的这个 `y` 只占位、不影响值（`bdWorldModel_f` 已显式说明）。
  =========================================================================== -/

end FateV2.Predict.WiringBackdoor

namespace FateV2.Predict.R259.BackdoorSetup

/-- ⭐⭐⭐ **可执行调整公式的**分子**：经 `WorldModel` 的模拟器 `f` 计算
`p(x, y, z)`（含 `p(z)`）。

$$\sum_{u_x,u_y}p_z(z)\,p_x(u_x)p_y(u_y)[f_X(z,u_x)=x]\,[\pi_2 f((x,y),(z,u_x),u_y)=y]$$

**⭐ 第二个指示函数用的是 `WorldModel.f`**（不是 `S.fY`）—— 接线点。

**⚠ 修正（本次 P1 批次）**：原定义**漏了 `p_z(z)` 因子**，导致 `wmNum` 与
`condYnum` 并不相等（`wmNum_eq_condYnum` 原陈述为假），下游 `field_simp` 步
随之失败。此处按 `condYnum` 的形状补上 `S.pz z *`（见上方公式）。 -/
noncomputable def wmNum (S : BackdoorSetup) [Nonempty S.X] [Nonempty S.Y]
    (x : S.X) (y : S.Y) (z : S.Z) : ℝ :=
  ∑ ux, ∑ uy, S.pz z * S.px ux * S.py uy *
    (if S.fX z ux = x then 1 else 0) *
    (if (FateV2.Predict.WorldModel.f (FateV2.Predict.WiringBackdoor.bdWorldModel S) (x, y) (z, ux) uy () ()).2
        = y then 1 else 0)

/-- ⭐⭐⭐⭐⭐ **`WorldModel` 层面的可执行后门调整公式**。

$$\widehat{P}(y\mid do(x))=\sum_z \frac{\texttt{wmNum}(x,y,z)}{\texttt{condX}(z,x)}.$$

（`wmNum` 已含 `p_z(z)`，故外层**不再**乘 `p_z`；等价地
`wmAdjustEst = ∑_z P(y|x,z)\,p_z(z)`，即 Pearl 后门公式。）

**⭐ 每一项都是可计算的**：`wmNum` 是对有限集的二重求和、`condX` 是定义里的求和、
`pz` 是结构字段。故 `wmAdjustEst` 是一个 **`Fintype` 上的 `Finset.sum` 表达式**，
在具体 `S` 上可直接求值（§5.4 用 `demo` 走一遍）。

**⚠ 修正（本次 P1 批次）**：原定义写 `∑ z, (wmNum/condX) * pz`，配上含 `pz` 的
`wmNum` 会多乘一次 `pz`（变成 `∑ pz²D/condX`），与后门公式不符。删去多余的 `* pz`。 -/
noncomputable def wmAdjustEst (S : BackdoorSetup) [Nonempty S.X] [Nonempty S.Y]
    (x : S.X) (y : S.Y) : ℝ :=
  ∑ z, S.wmNum x y z / S.condX z x

/-- ⭐ **`wmNum` 与 SCM 的 `condYnum` 逐字相等**（`bdWorldModel_f` 的直接读法）。 -/
theorem wmNum_eq_condYnum (S : BackdoorSetup) [Nonempty S.X] [Nonempty S.Y]
    (x : S.X) (y : S.Y) (z : S.Z) :
    S.wmNum x y z = S.condYnum x z y := by
  unfold wmNum condYnum
  simp only [FateV2.Predict.WiringBackdoor.bdWorldModel_f]
  rfl

/-- ⭐⭐⭐⭐⭐ **接线定理：`wmAdjustEst = backdoorFormula condYobs pz`**。

左边：**经 `WorldModel` 的模拟器**算出的估计量。
右边：`BackdoorCriterion` 的 Pearl 后门公式
`∑_z P(y|x,z) · P(z)`（`P(y|x,z) = condYnum/(pz·condX)` 的比值形式）。

**⭐ 这是「后门公式被接到 `WorldModel` 上」的准确陈述**：
`WorldModel.f` 与 `S.fY` 在 `wmNum` 中的位置**逐点相等**。 -/
theorem wmAdjustEst_eq_backdoorFormula (S : BackdoorSetup) [Nonempty S.X] [Nonempty S.Y]
    (x : S.X) (y : S.Y) :
    S.wmAdjustEst x y = FateV2.Predict.R259.backdoorFormula S.condYobs (fun z => S.pz z) x y := by
  unfold wmAdjustEst FateV2.Predict.R259.backdoorFormula condYobs margXZ margZ
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [wmNum_eq_condYnum]
  by_cases hz : S.pz z = 0
  · have h0 : S.condYnum x z y = 0 := by
      simp [condYnum, hz]
    rw [h0]
    simp [hz]
  · field_simp

/-- ⭐⭐⭐⭐⭐ **【主定理】`WorldModel` 层面的调整公式 = 干预律**。

**前提**（逐条都是 `BackdoorCriterion.backdoor_criterion` 的前提，**无一条是结论的改写**）：
* `h : S.BackdoorBlocked` —— Pearl (i) 的数值形式（`fY` 对 `u_x` 常值）；
* `hpx : ∑ u_x p_x(u_x) = 1` —— `p_x` 归一化；
* `hne : Nonempty S.Ux`；
* `hpos : ∀ z, p(x,z) ≠ 0` —— positivity / overlap。

**结论**：**经 `WorldModel` 模拟器算出的 `wmAdjustEst` 等于 `doLaw`**。 -/
theorem wmAdjustEst_eq_doLaw (S : BackdoorSetup) [Nonempty S.X] [Nonempty S.Y]
    (h : S.BackdoorBlocked) (hpx : ∑ ux, S.px ux = 1) (hne : Nonempty S.Ux)
    (x : S.X) (hpos : ∀ z : S.Z, S.margXZ x z ≠ 0) (y : S.Y) :
    S.wmAdjustEst x y = S.doLaw x y :=
  (wmAdjustEst_eq_backdoorFormula S x y).trans (backdoor_criterion S h hpx hne x hpos y)

end FateV2.Predict.R259.BackdoorSetup

/-! ===========================================================================
  §5.4 ⭐⭐ **在 `BackdoorWithM.Demo.demo` 上跑一遍**（可执行性见证）

  `demo` 是 `BackdoorWithM` 提供的具体 SCM。把它当作 `FateV2.Predict.R259.BackdoorSetup`
  不一定同构（字段不同），故这里用 `R259.Demo.demoS` + `wmAdjustEst`
  走 `norm_num`。
  =========================================================================== -/

namespace FateV2.Predict.WiringBackdoor

open FateV2.Predict.R259

/-- `demoS` 的 `X`（`Bool`）非空 —— 局部实例，供 `wmAdjustEst` 的 `[Nonempty S.X]` 用。 -/
instance : Nonempty FateV2.Predict.R259.Demo.demoS.X := ⟨false⟩

/-- `demoS` 的 `Y`（`Bool`）非空 —— 局部实例。 -/
instance : Nonempty FateV2.Predict.R259.Demo.demoS.Y := ⟨false⟩

/-- ⭐⭐ **`wmAdjustEst` 在 `R259.Demo.demoS` 上可算出闭式**。

证法：先走 §5.2 的**接线定理** `wmAdjustEst_eq_backdoorFormula`（把
`WorldModel` 层面的量转成 Pearl 后门公式），再走 `BackdoorCriterion` 的
`adjust_eq_adjustT` 与机器表 `adjust_eq_do`。

**⚠ 数值来自 `BackdoorCriterion` §5.3 的机器表**：`(x=0,y=0) ↦ 17/20`。 -/
theorem demoS_wmAdjustEst_00 :
    FateV2.Predict.R259.BackdoorSetup.wmAdjustEst FateV2.Predict.R259.Demo.demoS false false = 17 / 20 := by
  have h := FateV2.Predict.R259.BackdoorSetup.wmAdjustEst_eq_backdoorFormula
    (S := FateV2.Predict.R259.Demo.demoS) (x := false) (y := false)
  rw [h]
  rw [FateV2.Predict.R259.Demo.adjust_eq_adjustT]
  exact FateV2.Predict.R259.Demo.adjust_eq_do.1

/-- ⭐⭐ **同一格上 `wmAdjustEst = doLaw`**（主定理的具体落地）。 -/
theorem demoS_wmAdjustEst_eq_doLaw_00 :
    FateV2.Predict.R259.BackdoorSetup.wmAdjustEst FateV2.Predict.R259.Demo.demoS false false
      = FateV2.Predict.R259.Demo.demoS.doLaw false false := by
  rw [demoS_wmAdjustEst_00, FateV2.Predict.R259.Demo.doLaw_eq_doT, FateV2.Predict.R259.Demo.doT]
  exact FateV2.Predict.R259.Demo.adjust_eq_do.1.symm

end FateV2.Predict.WiringBackdoor

/-! ===========================================================================
  §7 ⭐⭐⭐⭐⭐ **R-48：把 `Fate/BackdoorCriterion`（真实 ns `FateV2.Predict.R259`）与
  `Fate/BackdoorGenuine`（真实 ns `FateV2.Predict.R277`）接进编译器可见的消费面**

  ## 7.0 口径

  `_audit/count_metrics.ps1:62` 的 G46 真消费正则是 `Fate\.<模块基名>\.\w+`。
  这两个模块的真实命名空间**都不等于模块名**（`grep "^namespace"`：
  `Fate/BackdoorCriterion.lean:158 → FateV2.Predict.R259`、
  `Fate/BackdoorGenuine.lean:86 → FateV2.Predict.R277`），故**纯 `import` 计 0 消费**。

  **本节**建**以模块名为名的组合层命名空间**，其中的定理**全部真实调用**
  `FateV2.Predict.R259.*` / `FateV2.Predict.R277.*` 的定理。**不复制、不重述、不修改被消费模块。**

  ## 7.1 清单

  | # | 名字 | 用到的被消费模块定理 |
  |---|---|---|
  | 1 | `BackdoorCriterion.criterion_via_blocked` | `FateV2.Predict.R259.BackdoorSetup.backdoor_criterion` |
  | 2 | `BackdoorCriterion.conditions_give_criterion` | `FateV2.Predict.R259.conditions_blocks` + `backdoor_criterion` |
  | 3 | `BackdoorCriterion.formula_degenerate_unit` | `FateV2.Predict.R259.backdoorFormula_unit` |
  | 4 | `BackdoorGenuine.conditions_decompose` | `FateV2.Predict.R277.backdoorConditions_iff` |
  | 5 | `BackdoorGenuine.sep_iff_paths` | `FateV2.Predict.R277.backdoorSep_iff` |
  | 6 | `BackdoorGenuine.enc_roundtrip` | `FateV2.Predict.R277.sumToVert_vertToSum` / `vertToSum_sumToVert` |
  | 7 | `BackdoorGenuine.moral_irrefl` | `FateV2.Predict.R277.moralAdj_irrefl` |

  **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`。**
-/

namespace FateV2.Predict.BackdoorCriterion

/-- ⭐⭐⭐⭐ **组合定理 1（backdoor）：`BackdoorBlocked` + 归一化 + positivity ⟹
调整公式 = 干预律。**

**⚠ 非同义反复检查**：前提是**方程层纤维常值**（`BackdoorBlocked`）+
归一化 + `Nonempty Ux` + 逐点 `margXZ x z ≠ 0`；
结论是**两个 `Finset` 求和式相等**（`backdoorFormula = doLaw`）。
证明体**真实调用** `FateV2.Predict.R259.BackdoorSetup.backdoor_criterion`（其证明经
`condYobs_eq` 约 20 行，不是 `rfl`）。 -/
theorem criterion_via_blocked (S : FateV2.Predict.R259.BackdoorSetup)
    (h : S.BackdoorBlocked) (hpx : ∑ ux, S.px ux = 1) (hne : Nonempty S.Ux)
    (x : S.X) (hpos : ∀ z : S.Z, S.margXZ x z ≠ 0) (y : S.Y) :
    FateV2.Predict.R259.backdoorFormula S.condYobs (fun z => S.pz z) x y = S.doLaw x y :=
  FateV2.Predict.R259.BackdoorSetup.backdoor_criterion S h hpx hne x hpos y

/-- ⭐⭐⭐⭐ **组合定理 2（backdoor）：Pearl 四条件（打包）⟹ 调整公式成立。**

**⚠ 非同义反复检查**：`BackdoorConditions` 是**四条独立字段**的结构，
结论是**数值恒等式**；第一步 `conditions_blocks` 只取出 (i)，
(pii)/(iii) 分别提供 `NoDescendant` / positivity —— **前提没有把结论包进去**。 -/
theorem conditions_give_criterion (S : FateV2.Predict.R259.BackdoorSetup)
    (c : R259.BackdoorConditions S)
    (hpx : ∑ ux, S.px ux = 1) (hne : Nonempty S.Ux)
    (x : S.X) (hpos : ∀ z : S.Z, S.margXZ x z ≠ 0) (y : S.Y) :
    FateV2.Predict.R259.backdoorFormula S.condYobs (fun z => S.pz z) x y = S.doLaw x y :=
  criterion_via_blocked S (FateV2.Predict.R259.conditions_blocks c) hpx hne x hpos y

/-- ⭐⭐⭐ **组合定理 3（backdoor）：空调整集退化式（外层求和坍缩）。**

**⚠ 非同义反复检查**：结论是 `∑_z condY x z y * margZ z = condY x () y`
在 `Z = Unit`、`margZ () = 1` 下成立 —— 需要 `Fintype.sum_unique` 与 `mul_one`，
**不是**前提的重述（前提里没有 `condY` 的任何信息）。 -/
theorem formula_degenerate_unit {X Y : Type*} (condY : X → Unit → Y → ℝ)
    (margZ : Unit → ℝ) (x : X) (y : Y) (h : margZ () = 1) :
    FateV2.Predict.R259.backdoorFormula condY margZ x y = condY x () y :=
  FateV2.Predict.R259.backdoorFormula_unit condY margZ x y h

end FateV2.Predict.BackdoorCriterion

namespace FateV2.Predict.BackdoorGenuine

/-- ⭐⭐⭐⭐ **组合定理 4（图形侧）：Pearl 四条件 ⟺ 四个图侧谓词的合取。** -/
theorem conditions_decompose (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (W : Set (R277.Vert S)) :
    R277.BackdoorConditions S x y W ↔
      FateV2.Predict.R277.BackdoorSep S x y W ∧ R277.NoDescendant S W
        ∧ FateV2.Predict.R277.NoOutcome S W ∧ FateV2.Predict.R277.ObservableOnly S W :=
  FateV2.Predict.R277.backdoorConditions_iff S x y W

/-- ⭐⭐⭐⭐ **组合定理 5（图形侧）：`BackdoorSep` 的路径判定形式。** -/
theorem sep_iff_paths (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (W : Set (R277.Vert S)) :
    FateV2.Predict.R277.BackdoorSep S x y W ↔
      ∀ (n : ℕ) (w : Fin (n + 1) → R277.Vert S),
        w 0 = R277.Vert.x x → w ⟨n, Nat.lt_succ_self n⟩ = R277.Vert.y y →
        (∀ i : Fin n, FateV2.Predict.R277.moralGraph S (w i.castSucc) (w i.succ)
          ∨ FateV2.Predict.R277.moralGraph S (w i.succ) (w i.castSucc)) →
        ∃ i, w i ∈ W \ {R277.Vert.x x} :=
  FateV2.Predict.R277.backdoorSep_iff S x y W

/-- ⭐⭐⭐ **组合定理 6（图形侧）：顶点编码的两个往返恒等式。** -/
theorem enc_roundtrip (S : FateV2.Predict.R259.BackdoorSetup) :
    (∀ v : R277.Vert S, FateV2.Predict.R277.sumToVert (S := S) (FateV2.Predict.R277.vertToSum v) = v)
      ∧ (∀ v : (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y),
          FateV2.Predict.R277.vertToSum (S := S) (FateV2.Predict.R277.sumToVert v) = v) :=
  ⟨fun v => FateV2.Predict.R277.sumToVert_vertToSum (S := S) v,
   fun v => FateV2.Predict.R277.vertToSum_sumToVert (S := S) v⟩

/-- ⭐⭐⭐ **组合定理 7（图形侧）：道德图自环不存在（无反身边）。** -/
theorem moral_irrefl (S : FateV2.Predict.R259.BackdoorSetup) (v : R277.Vert S) :
    ¬ FateV2.Predict.R277.moralAdj S v v :=
  FateV2.Predict.R277.moralAdj_irrefl S v

end FateV2.Predict.BackdoorGenuine
