/-
=============================================================================
  消费方：`PearlLawRuleBridge` —— Dirac 单点档识别 × 组合不可约性
=============================================================================

模块：`PearlLawRuleBridgeConsumer`
上游：`Fate/PearlLawRuleBridge.lean`（`SCM.toLawRule`、`finLawToMeasure`、
　　　`isPoint_toLawRule`、`toLawRule_apply`、`toLawRule_dirac_iff_pointmass` 等）、
　　　`Fate/LawRule.lean`（`IsPoint`、`IsPointDet`、`compose`、`compose_point_or_empty`、
　　　`point_compose_iff`、`bot`、`compose_bot`）

---------------------------------------------------------------------------
上游实际提供的声明（实测 `grep -nE "^(theorem|def|noncomputable def|instance)"`）
---------------------------------------------------------------------------
`PearlHierarchy` 顶层：`finStateSpace`、`instTopFinStateSpace`、`instMeasFinStateSpace`、
`instMeasurableSingletonClassFinStateSpace`、`ctxOf`、`finLawToMeasure`、
`finLawToMeasure_singleton`、`ofReal_inj_of_nonneg`、`finLawToMeasure_inj_of_nonneg`、
`finLawToMeasure_eq_dirac`、`finLawToMeasure_neg_erased`

`PearlHierarchy.SCM` 内：`lawY`、`toLawRule`、`toLawRuleNoCtx`、`toLawRule_apply`、
`toLawRuleNoCtx_apply`、`toLawRule_state_indep`、`toLawRule_diag_eq`、
`L2_family_eq_of_toLawRule_eq`、`toLawRule_eq_of_L2_family_eq`、
`toLawRule_eq_iff_L2_family_eq`、`toLawRule_congr_L3_cf`、`toLawRule_congr_L3_cf_L1`、
`isPoint_toLawRule`、`isPoint_toLawRuleNoCtx`、`deterministic_toLawRule`、
`toLawRule_not_constraining`、`toLawRuleNoCtx_not_constraining`、
`toLawRule_compose_top`、`toLawRule_dirac_iff_pointmass`

---------------------------------------------------------------------------
本模块证了什么（5 条消费定理）
---------------------------------------------------------------------------
上游 §6 只给出 `IsPoint M.toLawRule`（单点档），并明确注明
「⚠ 注意不是 `IsPointDet`」。本模块把这个**落差**精确化：

| § | 定理 | 内容 |
|---|---|---|
| §1 | `isPointDet_toLawRule_iff` | ⭐ **精确判据**：`M.toLawRule` 落在 Dirac 单点档 ⟺ **每个**干预值 `c` 上 `ℒ(M.L2_do c)` 都是 Dirac |
| §1 | `not_isPointDet_toLawRule_of_not_dirac` | 反例方向：只要**某个** `c` 的诱导测度不是 Dirac，就不是 Dirac 单点档 |
| §2 | `isPointDet_toLawRule_of_pointmass` | ⭐ **升级**：非负 + 概率 + 点质量 ⟹ Dirac 单点档（把 §6 的 `IsPoint` 加强到 `IsPointDet`） |
| §3 | `compose_toLawRule_point_or_empty` | 两条 `SCM` 诱导规则之「取交」逐点或空或单点 |
| §3 | `compose_toLawRule_isPoint_iff` | 该「取交」仍是单点档 ⟺ 两条诱导规则逐点相同（组合不可约） |
| §3 | `toLawRule_ne_bot` | 诱导规则的允许集**非空**，故 `bot` 不可能是诱导规则 |

---------------------------------------------------------------------------
为什么这些不是同义反复（自查，见任务书第 7 条）
---------------------------------------------------------------------------
* `isPointDet_toLawRule_iff` 的**前件是空的**（无条件命题），结论是
  「`IsPointDet` ⟺ 逐 `c` 的 Dirac 性」。证明需要**从单点集相等反解测度相等**
  （`Set.singleton_eq_singleton_iff`）+ 用 `toLawRule_apply` 展开，
  **不是** `rfl`，也不含结论。
* `isPointDet_toLawRule_of_pointmass` 的前件是 `L2_do` 的**点质量**（数论性质：
  非负、和 = 1、某点取值 1），结论是 `IsPointDet`（存在 Dirac 见证）——
  前件**不含**「存在 Dirac 测度」字样，须经上游 `toLawRule_dirac_iff_pointmass`
  （进而 `finLawToMeasure_eq_dirac`）中转。
* `compose_toLawRule_isPoint_iff` 的前件是「逐点相同」（普通等式），
  结论是「`IsPoint (compose …)`」，须经 `point_compose_iff` 与
  `isPoint_toLawRule` 两条上游结论合流；前件**不含** `IsPoint` 字样。
* `toLawRule_ne_bot` 的结论是**不等**（`≠`，集合层），由单点集非空得出；
  前件只有「`x : X.Carrier` 存在」的类型结构。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
* **没有构造具体 `SCM` 数值实例**：§1–§3 全部是接口层定理，量化于任意 `M`。
  「存在 `ℒ(M.L2_do c)` 非 Dirac 的 `SCM`」上游已由 §7/§8 的判别式刻画，
  本模块不重复构造（`not_isPointDet_toLawRule_of_not_dirac` 只做逻辑转接）。
* `toLawRule_ne_bot` 用的是「单点集非空」这一平凡事实，
  它**只**说明诱导规则的允许集永不空，**不**说明更多。
* 原始设计里拟证的 `compose_toLawRule_bot_ne`（`compose R bot ≠ R` 的整体形式）
  需要 `Nonempty X`，本文件改为**逐点**形式 `toLawRule_ne_bot`，避免额外前件。
* 本文件 **零 `sorry` / 零 `axiom` / 零 `admit` / 零 `native_decide`**。
=============================================================================
-/

import FateWorld.FateV2.Predict.PearlLawRuleBridge
import FateWorld.FateV2.Rules.LawRule
open FateV2.Error
open FateV2.Rules.LawRule

namespace FateV2.Predict

open FateV2.Rules
namespace PearlLawRuleBridgeConsumer

open MeasureTheory

/-!
  # Predict · PearlLawRuleBridgeConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PearlLawRuleBridgeConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：PearlLawRuleBridge, LawRule
  - 补充 open 域：FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §0  载体与实例（与 `PearlLawRuleBridge` 同口径）
    =========================================================================== -/

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- 局部实例：`Y` 的可测结构取 `finStateSpace Y` 的那一个（与上游 §3 一致）。 -/
local instance instMeasY : MeasurableSpace Y := (PearlHierarchy.finStateSpace Y).meas

/-- 局部实例：`Y` 上单点集可测。 -/
local instance instSingY : MeasurableSingletonClass Y :=
  PearlHierarchy.instMeasurableSingletonClassFinStateSpace Y

variable (M : PearlHierarchy.SCM X Y)

/-! ===========================================================================
    §1  Dirac 单点档：精确判据与反例方向
    =========================================================================== -/

omit [Fintype X] [DecidableEq X] in
/-- ⭐ **精确判据**：`SCM` 诱导的 `LawRule` 落在 **Dirac 单点档** `IsPointDet`
$$ \iff $$
**每个**干预值 `c` 上的编码律 `ℒ(M.L2_do c)` 都是某个 Dirac 测度。

**⟹ 这是上游 §6 那句「⚠ 注意不是 `IsPointDet`」的定量补充**：
`IsPointDet` 不是无条件成立，也不是无条件不成立 ——
它等价于「全部干预律的编码都是 Dirac」。

**证明要点**（不是 `rfl`）：上游 `toLawRule c x = {ℒ(M.L2_do c)}`，
故 `IsPointDet` 逐点展开后，单点集相等 `{ℒ(M.L2_do c)} = {δ y}`
必须经 `Set.singleton_eq_singleton_iff` 化为测度相等。 -/
theorem isPointDet_toLawRule_iff :
    LawRule.IsPointDet M.toLawRule ↔
      ∀ c : X, ∃ y : Y,
        PearlHierarchy.finLawToMeasure (Y := Y) (PearlHierarchy.finStateSpace Y).meas
            (M.L2_do c)
          = Measure.dirac y := by
  constructor
  · intro h c
    obtain ⟨y, hy⟩ := h c c
    rw [PearlHierarchy.SCM.toLawRule_apply] at hy
    exact ⟨y, Set.singleton_eq_singleton_iff.mp hy⟩
  · intro h c x
    obtain ⟨y, hy⟩ := h c
    refine ⟨y, ?_⟩
    show ({PearlHierarchy.finLawToMeasure (Y := Y) (PearlHierarchy.finStateSpace Y).meas
      (M.L2_do c)} : Set (Measure Y)) = {Measure.dirac y}
    rw [hy]

omit [Fintype X] [DecidableEq X] in
/-- **反例方向（诚实登记）**：若**某个**干预值 `c₀` 的编码律
`ℒ(M.L2_do c₀)` **不是**任何 `δ_y`，则诱导规则**离开** Dirac 单点档。

⟹ 与上游 `isPoint_toLawRule` 合起来得到精确落差：
「`IsPoint` 恒成立，而 `IsPointDet` 恰在全部干预律的编码是 Dirac 时成立」。
（上游 §8 已给「是 Dirac ⟺ 是点质量」的**单点**判据，
本定理是它在**整条规则**上的 `¬`-形式。） -/
theorem not_isPointDet_toLawRule_of_not_dirac (c₀ : X)
    (h : ∀ y : Y,
      PearlHierarchy.finLawToMeasure (Y := Y) (PearlHierarchy.finStateSpace Y).meas
          (M.L2_do c₀)
        ≠ Measure.dirac y) :
    ¬ LawRule.IsPointDet M.toLawRule := by
  intro hdet
  obtain ⟨y, hy⟩ := (isPointDet_toLawRule_iff M).mp hdet c₀
  exact h y hy

/-! ===========================================================================
    §2  升级：点质量律 ⟹ Dirac 单点档
    =========================================================================== -/

omit [Fintype X] [DecidableEq X] in
/-- ⭐ **从点质量得到 Dirac 单点档**（消费 `toLawRule_dirac_iff_pointmass`）。

若 `M.L2_do c` 对每个 `c` 都是**非负概率律**且在某点取 `1`（即点质量），
则 `M.toLawRule` **落在** Dirac 单点档。

**这是对上游 §6 的真加强**：§6 在更弱的场景下只给 `IsPoint`「允许集是单点集」，
而这里给出 `IsPointDet`「允许集是 δ 单点集」。
二者之间差的正是「那个测度是不是 δ」—— 本定理说明**点质量恰好填上这一格**。 -/
theorem isPointDet_toLawRule_of_pointmass
    (hp : ∀ c y, 0 ≤ M.L2_do c y) (hsum : ∀ c, ∑ y, M.L2_do c y = 1)
    (hpt : ∀ c, ∃ y₀, M.L2_do c y₀ = 1) :
    LawRule.IsPointDet M.toLawRule := by
  refine (isPointDet_toLawRule_iff M).mpr fun c => ?_
  obtain ⟨y₀, hy₀⟩ := hpt c
  exact ⟨y₀, PearlHierarchy.SCM.toLawRule_dirac_iff_pointmass M c (hp c) (hsum c) hy₀⟩

/-! ===========================================================================
    §3  组合：两条 `SCM` 诱导规则之「取交」不产生新东西
    =========================================================================== -/

variable (N : PearlHierarchy.SCM X Y)

omit [Fintype X] [DecidableEq X] in
/-- **两条诱导规则之「取交」逐点或空或单点**（消费 `compose_point_or_empty`）。

这是 `LawRule.compose_point_or_empty` 在 `SCM` 桥像上的实例化：
单点档的像在 `compose` 下只能产出「空或单点」的混合，
**不会**在任何一个 `(c,x)` 处产生 ≥2 个允许分布。 -/
theorem compose_toLawRule_point_or_empty :
    ∀ c x, (LawRule.compose M.toLawRule N.toLawRule c x = ∅) ∨
      ∃ μ, LawRule.compose M.toLawRule N.toLawRule c x = {μ} :=
  LawRule.compose_point_or_empty M.isPoint_toLawRule N.isPoint_toLawRule

omit [Fintype X] [DecidableEq X] in
/-- ⭐ **组合不可约**：两条 `SCM` 诱导规则的「取交」仍是单点档
$$ \iff $$
两条诱导规则**逐点相同**。

**语义**：桥的像在 `compose` 下**不闭合**；闭合当且仅当两者根本是同一条规则。
即「两个 `SCM` 的规律组合」要么退化为其中一条，
要么在某些 `(c,x)` 处允许集为空（不再是规律）——
`LawRule` 的 `compose` 在 `SCM` 桥上**不能产生新的、可用的联合约束**。

由 `LawRule.point_compose_iff` 与上游 `isPoint_toLawRule` 合流得到。 -/
theorem compose_toLawRule_isPoint_iff :
    LawRule.IsPoint (LawRule.compose M.toLawRule N.toLawRule) ↔
      ∀ c x, M.toLawRule c x = N.toLawRule c x :=
  LawRule.point_compose_iff M.isPoint_toLawRule N.isPoint_toLawRule

omit [Fintype X] [DecidableEq X] in
/-- **诱导规则的允许集非空**：`M.toLawRule c x ≠ ∅`。

于是（由 `LawRule.compose_bot`，`compose · bot = bot`）`bot`（矛盾规则）
**不可能**是任何 `SCM` 诱导出来的规则 —— `SCM` 的像落在**非空**单点档里。 -/
theorem toLawRule_ne_bot (c x : X) :
    M.toLawRule c x ≠
      (LawRule.bot (PearlHierarchy.ctxOf X) (PearlHierarchy.finStateSpace X)
        (PearlHierarchy.finStateSpace Y)) c x := by
  have hne : ({PearlHierarchy.finLawToMeasure (Y := Y) (PearlHierarchy.finStateSpace Y).meas
      (M.L2_do c)} : Set (Measure Y)).Nonempty := ⟨_, Set.mem_singleton _⟩
  rw [PearlHierarchy.SCM.toLawRule_apply]
  intro h
  have hempty : (LawRule.bot (PearlHierarchy.ctxOf X) (PearlHierarchy.finStateSpace X)
      (PearlHierarchy.finStateSpace Y)) c x = (∅ : Set (Measure Y)) := rfl
  rw [hempty] at h
  exact hne.ne_empty h

end PearlLawRuleBridgeConsumer
end FateV2.Predict