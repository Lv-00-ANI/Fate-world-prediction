import FateWorld.FateV2.Error.CfNecessity
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false

/-!
  # Predict · CfPartialIdent

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CfPartialIdent.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CfNecessity
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/CfPartialIdent` —— **O3 弱档：外生 `u` 完全不可观测 ⟹ 反事实的部分识别**

  ## 0 定位

  `O3-外生不可观测三档.md` 把「外生变量 `u` 的可观测程度」分成三档：

  | 档 | 条件 | 后果 | 状态 |
  |---|---|---|---|
  | **强** | `u` 完全可观测 | 反事实**可算**（点值） | `Fate/T43Abduction.lean`（`cfWithAbduction`） |
  | **中** | `u` 部分可观测 | 需代理变量 + 后验 | 未做 |
  | **弱** | **`u` 完全不可观测** | **只能部分识别（给界）** | ⬅ **本文件** |

  依据：**arXiv:2301.09031** —— 「即便无未观测混杂、因果结构已知，
  反事实推断仍**不可识别**」。本文把这个「不可识别」**精确化**为
  **一个可算的区间**（上下界），并给出**可点识别的充要条件**。

  ## 1 本文件的**观点切换**（关键）

  强档 `cfWithAbduction M x y x' y'` **把 `M` 当输入**：
  它假定 `U`、`pU`、`sg` 全部已知 —— 这正是「`u` 可观测」的数学化身。

  **弱档的正确读法**：`u` 不可观测 ⟹ **`M` 本身不可知**，
  我们只知道 `M` 落在某个**与观测数据相容的模型类** `𝔐` 里。

  ⟹ 把 `cfWithAbduction` 看成 `M` 的函数：

  $$\mathrm{cfWithAbduction}(\cdot, x, y, x', y') : \mathfrak M \to \mathbb R$$

  它在 `𝔐` 上的**像**就是「所有可能的反事实值」。

  **⚠ 这一步不是修辞**：见 §5 —— `𝔐open = {famOpen false, famOpen true}`
  的两个成员**相容于同一观测**（证据截面都是 `univ`，即 `P(X=0,Y=0)=1`）
  却给出**不同**反事实值（`0` 与 `1`）。**这正是 arXiv:2301.09031 的不可识别性。**

  ## 2 交付清单

  | # | 内容 | 名字 |
  |---|---|---|
  | 1 | **部分识别集** = 相容模型类上 `cfWithAbduction` 的像 | `cfIdentSet` |
  | 2 | **下界** / **上界**（`sInf` / `sSup`） | `cfLower` / `cfUpper` |
  | 3 | **每个可达值都落在 `[下界, 上界]` 内** | `cf_mem_Icc` / `cfIdentSet_subset_Icc` |
  | 4 | ⭐ **非空性**：`𝔐 ≠ ∅ ⟹ 识别集非空**，且 `下界 ≤ 上界` | `cfIdentSet_nonempty` / `cfLower_le_cfUpper` |
  | 5 | ⭐ **点识别 ⟺ 上界 = 下界** | `pointIdent_iff_lower_eq_upper` |
  | 6 | ⭐ **点识别 ⟺ 一切相容模型同值** | `pointIdent_iff_all_eq` |
  | 7 | **充分条件**：`𝔐` 单点 ⟹ 点识别（强档的数学内容） | `pointIdent_of_singleton` |
  | 8 | ⭐⭐ **具体族 `𝔐open`**：识别集恰为 `{0,1}`，`cfLower=0 < 1=cfUpper` | `famOpen` / `𝔐open` / `cfIdentSet_open_eq` / `open_Lower` / `open_Upper` |
  | 9 | ⭐⭐⭐ **弱档不可点识别** | `weak_no_point_ident` / `weak_lower_lt_upper` |

  ## 3 诚实边界（**先读**）

  * 本文件**不**构造「数据 → `𝔐`」这一步（那是**统计**问题）。
    这里的 `𝔐` 是**给定的**相容模型类。
  * 本文件**不**声称这个区间是**紧的**（sharp）。sharpness 依赖于 `𝔐` 的具体刻画；
    本文证明的是「**界对一切可达值成立**」+「**非空性**」+「**上下界相等 ⟺ 点识别**」，
    以及 §5 的**一个**具体族上「界可达」（`cfLower`/`cfUpper` 本身都可达）。
  * **不虚构**：不引用任何未在 Lean 中落地的文献结论；
    §5 的每个数值都由 `norm_num`/`rfl` 算出，**不是注释里的断言**。

  ## 4 与 A14 的同构（见 `A14-三档关系分析.md`）

  | A14（观测状态 `x_t`） | O3 弱档（本文件） |
  |---|---|
  | `h` 非单射 ⟹ 观测给的是**等价类** | 观测给的是**相容模型类** `𝔐` |
  | 等价类上的值集 | `cfIdentSet`（`cfWithAbduction` 的像） |
  | 「类退化到单点时状态可识别」 | `pointIdent_iff_lower_eq_upper` |
  | 「类大小」度量不确定性 | `cfUpper − cfLower` 度量反事实不确定性 |

  ⟹ **同一个纲领的两条实例**：不可观测 ⟹ 等价类 ⟹ 区间。
=========================================================================== -/

namespace FateV2.Predict
namespace CfPartialIdent

open FateV2.Modeling.PearlHierarchy FateV2.Modeling.SCMSemantics Set

-- `obsSet` / `postZ` / `cfWithAbduction` 定义在 `Fate.T43` 命名空间内。
open FateV2.Predict.T43

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ===========================================================================
  §1  部分识别集：定义
  =========================================================================== -/

/-- ⭐ **部分识别集**（弱档的**核心定义**，对应任务 1）。

给定：

* `𝔐 : Set (SCM X Y)` —— **相容模型类**（与已观测数据相容的全部 SCM）；
* 证据 `(x, y)` —— 观测到的 `(X, Y)`；
* 反事实查询 `(x', y')` —— 「若当初 `X := x'`，`Y = y'` 的概率」。

**部分识别集** := 强档反事实泛函 `cfWithAbduction (·, x, y, x', y')`
在 `𝔐` 上的**像**：

$$\mathrm{cfIdentSet}\,\mathfrak M\,(x,y)\,(x',y')
  := \{\, \mathrm{cfWithAbduction}\,M\,x\,y\,x'\,y' \;|\; M \in \mathfrak M \,\}$$

**⚠ 这在语义上正是「`u` 完全不可观测」**：不可观测 ⟹ 无法把 `M` 收窄到单点
⟹ 反事实不再是**数**，而是**集合**。 -/
def cfIdentSet (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y) : Set ℝ :=
  (fun M => cfWithAbduction M x y x' y') '' 𝔐

/-- 成员刻画（**定义展开**，供后续改写用）。 -/
theorem mem_cfIdentSet (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y) (v : ℝ) :
    v ∈ cfIdentSet 𝔐 x y x' y' ↔ ∃ M ∈ 𝔐, cfWithAbduction M x y x' y' = v :=
  Iff.rfl

/-- ⭐ **下界**：识别集的下确界。 -/
noncomputable def cfLower (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y) : ℝ :=
  sInf (cfIdentSet 𝔐 x y x' y')

/-- ⭐ **上界**：识别集的上确界。 -/
noncomputable def cfUpper (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y) : ℝ :=
  sSup (cfIdentSet 𝔐 x y x' y')

/-! ===========================================================================
  §2  ⭐⭐ 主界定理：每个可达值都落在 `[cfLower, cfUpper]`（任务 2）
  =========================================================================== -/

section Bounds

/-- ⭐ **`cfLower` 是下界**：识别集中**每一个**值都 `≥ cfLower`。

（`csInf_le` 需要 `BddBelow`；识别集非空时由像中有界性给出。
这里**不假设** `𝔐` 非空：空像时陈述为真空真，见 `cfLower_le`。） -/
theorem cfLower_le_of_ne (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y)
    (hb : BddBelow (cfIdentSet 𝔐 x y x' y')) :
    ∀ v ∈ cfIdentSet 𝔐 x y x' y', cfLower 𝔐 x y x' y' ≤ v :=
  fun _ hv => csInf_le hb hv

/-- ⭐ **`cfUpper` 是上界**。 -/
theorem le_cfUpper_of_ne (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y)
    (hb : BddAbove (cfIdentSet 𝔐 x y x' y')) :
    ∀ v ∈ cfIdentSet 𝔐 x y x' y', v ≤ cfUpper 𝔐 x y x' y' :=
  fun _ hv => le_csSup hb hv

/-- ⭐⭐⭐ **主界定理（任务 2 的直接答案）**：对**一切**相容模型 `M ∈ 𝔐`，

$$\mathrm{cfLower}\ \le\ \mathrm{cfWithAbduction}\,M\,x\,y\,x'\,y'\ \le\ \mathrm{cfUpper}.$$

**⚠ 这就是「部分识别的界」的字面形式**：
无论 `u` 的实际取值如何（即无论真实 `M` 是 `𝔐` 里的哪一个），
在观测 `(x, y)` 下，反事实 `P(Y_{x'} = y')` **一定落在这个区间内**。

**证明**：`M ∈ 𝔐` ⟹ 值 `v` 在像里 ⟹ `sInf ≤ v ≤ sSup`。
（模型类非空时像非空，故 `BddBelow`/`BddAbove` 对有限类自动成立；
这里**显式**取它们作前提，以免对无限 `𝔐` 撒谎。） -/
theorem cf_mem_Icc (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y)
    (hbdd : BddBelow (cfIdentSet 𝔐 x y x' y') ∧ BddAbove (cfIdentSet 𝔐 x y x' y'))
    {M : SCM X Y} (hM : M ∈ 𝔐) :
    cfLower 𝔐 x y x' y' ≤ cfWithAbduction M x y x' y'
      ∧ cfWithAbduction M x y x' y' ≤ cfUpper 𝔐 x y x' y' :=
  ⟨cfLower_le_of_ne 𝔐 x y x' y' hbdd.1 _ ⟨M, hM, rfl⟩,
   le_cfUpper_of_ne 𝔐 x y x' y' hbdd.2 _ ⟨M, hM, rfl⟩⟩

/-- 识别集落在闭区间内（**集合版**，与 `cf_mem_Icc` 同一内容）。 -/
theorem cfIdentSet_subset_Icc (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y)
    (hbdd : BddBelow (cfIdentSet 𝔐 x y x' y') ∧ BddAbove (cfIdentSet 𝔐 x y x' y')) :
    cfIdentSet 𝔐 x y x' y' ⊆ Icc (cfLower 𝔐 x y x' y') (cfUpper 𝔐 x y x' y') :=
  fun _ hv => ⟨cfLower_le_of_ne 𝔐 x y x' y' hbdd.1 _ hv,
    le_cfUpper_of_ne 𝔐 x y x' y' hbdd.2 _ hv⟩

end Bounds

/-! ===========================================================================
  §3  ⭐⭐⭐ 非空性与 `下界 ≤ 上界`（任务 3）
  =========================================================================== -/

section Nonempty

/-- ⭐⭐⭐ **`cfIdentSet_nonempty`（任务 3 的第一半）**：

**只要相容模型类 `𝔐` 非空，部分识别集就非空。**

证明：取 `M ∈ 𝔐`，则 `cfWithAbduction M x y x' y'` 就是像中的一个元素。 -/
theorem cfIdentSet_nonempty (𝔐 : Set (SCM X Y)) (h : 𝔐.Nonempty)
    (x : X) (y : Y) (x' : X) (y' : Y) : (cfIdentSet 𝔐 x y x' y').Nonempty := by
  obtain ⟨M, hM⟩ := h
  exact ⟨cfWithAbduction M x y x' y', M, hM, rfl⟩

/-- ⭐⭐⭐ **`cfLower_le_cfUpper`（任务 3 的第二半）**：

**`𝔐` 非空 ⟹ `cfLower ≤ cfUpper`** —— 区间**不退化成空**。

**证明**：取 `v₀ ∈ cfIdentSet 𝔐 x y x' y'`（非空性）。
像中的每个元素都等于某个 `cfWithAbduction M`，而**反事实是非负概率**（当 `pU ≥ 0`、
`postZ > 0` 时），故 `0` 是下界；同时 `∑ pU / postZ` 是上界。
于是 `BddBelow`/`BddAbove` 齐备，`csInf_le_csSup` 给出结论。

**⚠ 为使本定理不依赖任何概率公理**，有界性以**显式参数** `hbdd` 传入；
§5 的具体族里我们**直接算出**有界性（`𝔐open_bounds_attained`）。 -/
theorem cfLower_le_cfUpper_of_bdd (𝔐 : Set (SCM X Y)) (h : 𝔐.Nonempty)
    (x : X) (y : Y) (x' : X) (y' : Y)
    (hbdd : BddBelow (cfIdentSet 𝔐 x y x' y') ∧ BddAbove (cfIdentSet 𝔐 x y x' y')) :
    cfLower 𝔐 x y x' y' ≤ cfUpper 𝔐 x y x' y' :=
  csInf_le_csSup (cfIdentSet_nonempty 𝔐 h x y x' y') hbdd.1 hbdd.2

/-- **界可达（有限模型类）**：`𝔐` 有限且非空 ⟹ `cfLower` **本身就在识别集里**。

⟹ 下界不是「逼近值」，而是**真的有一个模型达到它**。 -/
theorem sInf_mem_of_finite (𝔐 : Set (SCM X Y)) (hne : 𝔐.Nonempty) (hfin : 𝔐.Finite)
    (x : X) (y : Y) (x' : X) (y' : Y) :
    cfLower 𝔐 x y x' y' ∈ cfIdentSet 𝔐 x y x' y' := by
  have himg : (cfIdentSet 𝔐 x y x' y').Finite := hfin.image _
  exact (cfIdentSet_nonempty 𝔐 hne x y x' y').csInf_mem himg

/-- **界可达（有限模型类）**：`cfUpper` **本身就在识别集里**。 -/
theorem sSup_mem_of_finite (𝔐 : Set (SCM X Y)) (hne : 𝔐.Nonempty) (hfin : 𝔐.Finite)
    (x : X) (y : Y) (x' : X) (y' : Y) :
    cfUpper 𝔐 x y x' y' ∈ cfIdentSet 𝔐 x y x' y' := by
  have himg : (cfIdentSet 𝔐 x y x' y').Finite := hfin.image _
  exact (cfIdentSet_nonempty 𝔐 hne x y x' y').csSup_mem himg

end Nonempty

/-! ===========================================================================
  §4  ⭐⭐⭐⭐ 何时**点识别**（任务 4）
  =========================================================================== -/

section PointIdent

/-- ⭐ **点识别**：识别集**至多单点** —— 即「反事实的取值不依赖 `M`」，
从而**是一个数**，可以当作点值报告。 -/
def PointIdent (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y) : Prop :=
  (cfIdentSet 𝔐 x y x' y').Subsingleton

/-- ⭐⭐ **点识别 ⟺ 一切相容模型给出同一个值**（把 `Subsingleton` 展开成可用形式）。 -/
theorem pointIdent_iff_all_eq (𝔐 : Set (SCM X Y)) (x : X) (y : Y) (x' : X) (y' : Y) :
    PointIdent 𝔐 x y x' y' ↔
      ∀ M₁ ∈ 𝔐, ∀ M₂ ∈ 𝔐,
        cfWithAbduction M₁ x y x' y' = cfWithAbduction M₂ x y x' y' := by
  constructor
  · intro h M₁ h₁ M₂ h₂
    exact h ⟨M₁, h₁, rfl⟩ ⟨M₂, h₂, rfl⟩
  · intro h v hv w hw
    obtain ⟨M₁, h₁, hv'⟩ := hv
    obtain ⟨M₂, h₂, hw'⟩ := hw
    rw [← hv', ← hw']
    exact h M₁ h₁ M₂ h₂

/-- ⭐⭐⭐ **`lower_eq_upper_of_pointIdent`（任务 4 的 ⟹ 方向）**：

**可点识别 ⟹ 上下界相等。**

识别集至多单点 ⟹ 至多一个元素 ⟹ `sInf` 与 `sSup` 只能是那个值。
（不需要有界性：单点集/空集上 `sInf = sSup` 恒成立。） -/
theorem lower_eq_upper_of_pointIdent (𝔐 : Set (SCM X Y))
    (x : X) (y : Y) (x' : X) (y' : Y) (hp : PointIdent 𝔐 x y x' y') :
    cfLower 𝔐 x y x' y' = cfUpper 𝔐 x y x' y' := by
  -- `Subsingleton s` ⟹ `s ⊆ {v}`（对任一 `v`）；故 `sSup s = sInf s`
  have hsub : ∀ v w : ℝ, v ∈ cfIdentSet 𝔐 x y x' y' → w ∈ cfIdentSet 𝔐 x y x' y' → v = w :=
    fun v w hv hw => hp hv hw
  rcases (Set.eq_empty_or_nonempty (cfIdentSet 𝔐 x y x' y') :
      cfIdentSet 𝔐 x y x' y' = ∅ ∨ (cfIdentSet 𝔐 x y x' y').Nonempty) with hemp | hne
  · rw [cfLower, cfUpper, hemp, Real.sInf_empty, Real.sSup_empty]
  · obtain ⟨v, hv⟩ := hne
    -- 像 = {v}
    have hset : cfIdentSet 𝔐 x y x' y' = {v} := by
      ext w
      constructor
      · intro hw
        rw [Set.mem_singleton_iff]
        exact hsub w v hw hv
      · intro hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact hv
    rw [cfLower, cfUpper, hset, csInf_singleton, csSup_singleton]

/-- ⭐⭐⭐ **`pointIdent_of_lower_eq_upper`（任务 4 的 ⟸ 方向）**：

**上下界相等 + 有界 ⟹ 可点识别。**

所有可达值都被 `cf_mem_Icc` 夹在 `[cfLower, cfUpper]` 中；
若两端相等，则夹在同一个点上。 -/
theorem pointIdent_of_lower_eq_upper (𝔐 : Set (SCM X Y))
    (x : X) (y : Y) (x' : X) (y' : Y)
    (hbdd : BddBelow (cfIdentSet 𝔐 x y x' y') ∧ BddAbove (cfIdentSet 𝔐 x y x' y'))
    (heq : cfLower 𝔐 x y x' y' = cfUpper 𝔐 x y x' y') :
    PointIdent 𝔐 x y x' y' := by
  intro v hv w hw
  have hv' : v ∈ Icc (cfLower 𝔐 x y x' y') (cfUpper 𝔐 x y x' y') :=
    cfIdentSet_subset_Icc 𝔐 x y x' y' hbdd hv
  have hw' : w ∈ Icc (cfLower 𝔐 x y x' y') (cfUpper 𝔐 x y x' y') :=
    cfIdentSet_subset_Icc 𝔐 x y x' y' hbdd hw
  rw [Set.mem_Icc] at hv' hw'
  rw [← heq] at hv' hw'
  -- 两者都等于 `cfLower`（因为 `cfLower = cfUpper`）
  have hv2 : v = cfLower 𝔐 x y x' y' := le_antisymm hv'.2 hv'.1
  have hw2 : w = cfLower 𝔐 x y x' y' := le_antisymm hw'.2 hw'.1
  rw [hv2, hw2]

/-- ⭐⭐⭐ **`pointIdent_iff_lower_eq_upper`（任务 4 的直接答案）**：

**反事实可点识别 ⟺ 上下界相等**（在识别集有界的前提下）。

| 方向 | 定理 |
|---|---|
| (⟹) | `lower_eq_upper_of_pointIdent` |
| (⟸) | `pointIdent_of_lower_eq_upper` |

**⚠ 点识别的语义**：`下界 = 上界` 意味着**观测数据把反事实钉死了** ——
即使 `u` 不可观测，不同 `M ∈ 𝔐` 也给出**同一个**反事实值。

**⚠ 「有界」是必要的形式前提**：`ℝ` 的 `sInf`/`sSup` 对无界集取 `0`（`Real.sSup_def`），
故无界集上 `sInf = sSup = 0` 是**约定**而非事实。§5 的具体族里我们**证明**有界性。 -/
theorem pointIdent_iff_lower_eq_upper (𝔐 : Set (SCM X Y))
    (x : X) (y : Y) (x' : X) (y' : Y)
    (hbdd : BddBelow (cfIdentSet 𝔐 x y x' y') ∧ BddAbove (cfIdentSet 𝔐 x y x' y')) :
    PointIdent 𝔐 x y x' y' ↔ cfLower 𝔐 x y x' y' = cfUpper 𝔐 x y x' y' :=
  ⟨lower_eq_upper_of_pointIdent 𝔐 x y x' y',
   pointIdent_of_lower_eq_upper 𝔐 x y x' y' hbdd⟩

/-- ⭐ **充分条件（强档的数学内容）**：若相容模型类 `𝔐` 只含**一个**模型，
则**一切**反事实都点识别。

⟹ 「`u` 完全可观测」的最强特例就是「模型唯一」——
**这正是 `T43` 强档 `cfWithAbduction` 能给出数值的原因**。 -/
theorem pointIdent_of_singleton (M : SCM X Y) (x : X) (y : Y) (x' : X) (y' : Y) :
    PointIdent ({M} : Set (SCM X Y)) x y x' y' := by
  refine pointIdent_iff_all_eq _ _ _ _ _ |>.2 ?_
  intro M₁ h₁ M₂ h₂
  rw [Set.mem_singleton_iff] at h₁ h₂
  rw [h₁, h₂]

/-- ⭐ **单集合上的上下界恰好相等**（与 `pointIdent_of_singleton` 配套）。 -/
theorem singleton_lower_eq_upper (M : SCM X Y) (x : X) (y : Y) (x' : X) (y' : Y) :
    cfLower ({M} : Set (SCM X Y)) x y x' y' = cfUpper ({M} : Set (SCM X Y)) x y x' y' :=
  lower_eq_upper_of_pointIdent _ x y x' y' (pointIdent_of_singleton M x y x' y')


/-! ## §5 具体族 -/

/-! ## §5 ⭐⭐⭐⭐ 具体族 `𝔐open`：「弱档真的不可点识别」（任务 1–4 的端到端实例）

### 5.1 构造

取 `X = Y = U = Bool`，`pU ≡ 1/2`。两个 SCM：

| 模型 | `sg u` | 含义 | `obsSet (0,0)` |
|---|---|---|---|
| `M0` | `(false, id)` | `X := 0`、`Y := X` | `univ` |
| `M1` | `(false, const false)` | `X := 0`、`Y := 0` | `univ` |

**两者都给出同一观测** `P(X=0, Y=0) = 1`（证据截面 `univ`）。

但对反事实「若 `X := 1`，则 `Y = 0`」：

| 查询 | `M0` | `M1` |
|---|---|---|
| `cfWithAbduction · (0,0) (1,0)` | **0** | **1** |

`M0` 中 `Y := X = 1 ≠ 0`；`M1` 中 `Y ≡ 0`。

⟹ **同一观测数据无法区分 `M0` 与 `M1`，而它们给出相反的反事实值。**
**这就是 `arXiv:2301.09031` 的不可识别性在有限 SCM 上的字面见证。**

### 5.2 族

`𝔐open := {M0, M1}`（`famOpen false = M0`、`famOpen true = M1`）。 -/

noncomputable def M0 : SCM Bool Bool where
  U := Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1/2
  sg := fun _ => (false, id)

theorem M0_mem (u : M0.U) : u ∈ obsSet M0 false false := by
  have hm := mem_obsSet M0 false false u
  rw [hm]
  have h : M0.sg u = (false, id) := rfl
  constructor
  · rw [h]
  · rw [h]
    change (id : Bool → Bool) false = false
    rfl

theorem M0_obsSet : obsSet M0 false false = Finset.univ := by
  ext u; exact iff_of_true (M0_mem u) (Finset.mem_univ u)

theorem M0_pU_sum : (∑ u : M0.U, M0.pU u) = 1 := by
  rw [show (∑ u : M0.U, M0.pU u) = (∑ u : Bool, (1:ℝ)/2) from
    Finset.sum_congr rfl (fun u _ => rfl)]
  rw [Fintype.sum_bool]; norm_num

theorem M0_postZ : postZ M0 false false = 1 := by
  rw [postZ, obsEventMass_eq_sum_obsSet, M0_obsSet, M0_pU_sum]

theorem M0_cf (x' y' : Bool) :
    cfWithAbduction M0 false false x' y' = if x' = y' then 1 else 0 := by
  rw [cfWithAbduction_eq_obsSet, M0_obsSet]
  have hterm : ∀ u : M0.U,
      (M0.pU u / postZ M0 false false) * (if (M0.sg u).2 x' = y' then (1:ℝ) else 0)
        = (1/2 : ℝ) * (if x' = y' then (1:ℝ) else 0) := by
    intro u
    rw [M0_postZ]
    have hsg : M0.sg u = (false, id) := rfl
    rw [hsg]
    show (1/2 : ℝ) / 1 * (if (id : Bool → Bool) x' = y' then (1:ℝ) else 0)
      = (1/2 : ℝ) * (if x' = y' then (1:ℝ) else 0)
    change (1/2 : ℝ) / 1 * (if x' = y' then (1:ℝ) else 0)
      = (1/2 : ℝ) * (if x' = y' then (1:ℝ) else 0)
    by_cases hxy : x' = y'
    · rw [if_pos hxy]; norm_num
    · rw [if_neg hxy]; norm_num
  rw [Finset.sum_congr rfl (fun u _ => hterm u)]
  rw [Finset.sum_const, Finset.card_univ]
  rw [show Fintype.card M0.U = 2 from rfl]
  norm_num

noncomputable def M1 : SCM Bool Bool where
  U := Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1/2
  sg := fun _ => (false, fun _ => false)

theorem M1_mem (u : M1.U) : u ∈ obsSet M1 false false := by
  have hm := mem_obsSet M1 false false u
  rw [hm]
  have h : M1.sg u = (false, fun _ => false) := rfl
  constructor
  · rw [h]
  · rw [h]

theorem M1_obsSet : obsSet M1 false false = Finset.univ := by
  ext u; exact iff_of_true (M1_mem u) (Finset.mem_univ u)

theorem M1_pU_sum : (∑ u : M1.U, M1.pU u) = 1 := by
  rw [show (∑ u : M1.U, M1.pU u) = (∑ u : Bool, (1:ℝ)/2) from
    Finset.sum_congr rfl (fun u _ => rfl)]
  rw [Fintype.sum_bool]; norm_num

theorem M1_postZ : postZ M1 false false = 1 := by
  rw [postZ, obsEventMass_eq_sum_obsSet, M1_obsSet, M1_pU_sum]

theorem M1_cf (x' y' : Bool) :
    cfWithAbduction M1 false false x' y' = if y' = false then 1 else 0 := by
  rw [cfWithAbduction_eq_obsSet, M1_obsSet]
  have hterm : ∀ u : M1.U,
      (M1.pU u / postZ M1 false false) * (if (M1.sg u).2 x' = y' then (1:ℝ) else 0)
        = (1/2 : ℝ) * (if y' = false then (1:ℝ) else 0) := by
    intro u
    rw [M1_postZ]
    have hsg : M1.sg u = (false, fun _ => false) := rfl
    rw [hsg]
    show (1/2 : ℝ) / 1 * (if (fun _ => false) x' = y' then (1:ℝ) else 0)
      = (1/2 : ℝ) * (if y' = false then (1:ℝ) else 0)
    change (1/2 : ℝ) / 1 * (if (false : Bool) = y' then (1:ℝ) else 0)
      = (1/2 : ℝ) * (if y' = false then (1:ℝ) else 0)
    by_cases h : y' = false
    · rw [if_pos h, if_pos h.symm]; norm_num
    · rw [if_neg h]; rw [if_neg (fun hh : (false : Bool) = y' => h hh.symm)]; norm_num
  rw [Finset.sum_congr rfl (fun u _ => hterm u)]
  rw [Finset.sum_const, Finset.card_univ]
  rw [show Fintype.card M1.U = 2 from rfl]
  norm_num

/-- 族 -/
noncomputable def famOpen (b : Bool) : SCM Bool Bool := if b then M1 else M0

theorem famOpen_zero : famOpen false = M0 := rfl
theorem famOpen_one : famOpen true = M1 := rfl

noncomputable def 𝔐open : Set (SCM Bool Bool) := {M0, M1}

theorem M0_mem_open : M0 ∈ 𝔐open := by
  unfold 𝔐open; exact Set.mem_insert _ _

theorem M1_mem_open : M1 ∈ 𝔐open := by
  unfold 𝔐open
  exact Set.mem_insert_of_mem _ rfl

theorem open_nonempty : 𝔐open.Nonempty := ⟨M0, M0_mem_open⟩

theorem open_finite : 𝔐open.Finite := by
  unfold 𝔐open
  exact Set.toFinite _

theorem open_shape (M : SCM Bool Bool) (hM : M ∈ 𝔐open) : M = M0 ∨ M = M1 := by
  unfold 𝔐open at hM
  rcases Set.mem_insert_iff.1 hM with h1 | h1
  · exact Or.inl h1
  · rcases Set.mem_singleton_iff.1 h1 with h2
    exact Or.inr h2

theorem cf_open_cases (M : SCM Bool Bool) (hM : M ∈ 𝔐open) (y' : Bool) :
    cfWithAbduction M false false true y'
      = (if (true:Bool) = y' then (1:ℝ) else 0) ∨
      cfWithAbduction M false false true y' = (if y' = false then (1:ℝ) else 0) := by
  rcases open_shape M hM with rfl | rfl
  · left; rw [M0_cf]
  · right; rw [M1_cf]

theorem cf_M0_true_false : cfWithAbduction M0 false false true false = 0 := by
  rw [M0_cf]; norm_num

theorem cf_M1_true_false : cfWithAbduction M1 false false true false = 1 := by
  rw [M1_cf]; norm_num

theorem mem_cfIdentSet_open_0 : (0:ℝ) ∈ cfIdentSet 𝔐open false false true false :=
  ⟨M0, M0_mem_open, cf_M0_true_false⟩

theorem mem_cfIdentSet_open_1 : (1:ℝ) ∈ cfIdentSet 𝔐open false false true false :=
  ⟨M1, M1_mem_open, cf_M1_true_false⟩

theorem cfIdentSet_open_eq :
    cfIdentSet 𝔐open false false true false = ({0, 1} : Set ℝ) := by
  ext v
  rw [mem_cfIdentSet]
  constructor
  · rintro ⟨M, hM, hv⟩
    rcases open_shape M hM with rfl | rfl
    · rw [cf_M0_true_false] at hv
      rw [hv]
      exact Or.inl rfl
    · rw [cf_M1_true_false] at hv
      rw [hv]
      exact Or.inr rfl
  · intro hv
    rcases Set.mem_insert_iff.1 hv with hv | hv
    · exact ⟨M0, M0_mem_open, by rw [cf_M0_true_false, hv]⟩
    · rw [Set.mem_singleton_iff] at hv
      exact ⟨M1, M1_mem_open, by rw [cf_M1_true_false, hv]⟩

theorem open_bounds : BddBelow (cfIdentSet 𝔐open false false true false) ∧
    BddAbove (cfIdentSet 𝔐open false false true false) := by
  constructor
  · refine ⟨0, ?_⟩
    rintro v hv
    rw [cfIdentSet_open_eq] at hv
    rcases hv with rfl | rfl <;> norm_num
  · refine ⟨1, ?_⟩
    rintro v hv
    rw [cfIdentSet_open_eq] at hv
    rcases hv with rfl | rfl <;> norm_num

theorem open_Lower : cfLower 𝔐open false false true false = 0 := by
  have hb : BddBelow (cfIdentSet 𝔐open false false true false) := open_bounds.1
  have hne : (cfIdentSet 𝔐open false false true false).Nonempty :=
    ⟨0, mem_cfIdentSet_open_0⟩
  rw [cfLower]
  refine le_antisymm ?_ ?_
  · -- 0 是下界且属于识别集
    exact csInf_le hb mem_cfIdentSet_open_0
  · exact le_csInf hne (fun v hv => by
      rw [cfIdentSet_open_eq] at hv
      rcases hv with rfl | rfl <;> norm_num)

theorem open_Upper : cfUpper 𝔐open false false true false = 1 := by
  have hb : BddAbove (cfIdentSet 𝔐open false false true false) := open_bounds.2
  have hne : (cfIdentSet 𝔐open false false true false).Nonempty :=
    ⟨0, mem_cfIdentSet_open_0⟩
  rw [cfUpper]
  refine le_antisymm ?_ ?_
  · exact csSup_le hne (fun v hv => by
      rw [cfIdentSet_open_eq] at hv
      rcases hv with rfl | rfl <;> norm_num)
  · exact le_csSup hb mem_cfIdentSet_open_1

theorem weak_no_point_ident :
    ¬ PointIdent 𝔐open false false true false := by
  intro hp
  have h01 : (0:ℝ) = 1 := hp mem_cfIdentSet_open_0 mem_cfIdentSet_open_1
  norm_num at h01

theorem weak_lower_lt_upper : cfLower 𝔐open false false true false
    < cfUpper 𝔐open false false true false := by
  rw [open_Lower, open_Upper]; norm_num

/-! ### 5.3 与一般定理的**一致性核查**（任务 2/3/4 在具体族上的落地） -/

/-- ⭐ **主界定理在 `𝔐open` 上的具体版**：两个模型的反事实值都被夹在 `[0, 1]` 内。

（对 `M0` 得 `0`，对 `M1` 得 `1`，两端都可达。） -/
theorem open_mem_Icc_M0 : cfLower 𝔐open false false true false
    ≤ cfWithAbduction M0 false false true false
    ∧ cfWithAbduction M0 false false true false ≤ cfUpper 𝔐open false false true false := by
  rw [open_Lower, open_Upper, cf_M0_true_false]
  norm_num

theorem open_mem_Icc_M1 : cfLower 𝔐open false false true false
    ≤ cfWithAbduction M1 false false true false
    ∧ cfWithAbduction M1 false false true false ≤ cfUpper 𝔐open false false true false := by
  rw [open_Lower, open_Upper, cf_M1_true_false]
  norm_num

/-- ⭐ **任务 3 在具体族上的落地**：`𝔐open` 非空，故识别集非空且上下界齐备。 -/
theorem open_lower_le_upper : cfLower 𝔐open false false true false
    ≤ cfUpper 𝔐open false false true false :=
  cfLower_le_cfUpper_of_bdd 𝔐open open_nonempty _ _ _ _ open_bounds

/-- ⭐ **任务 4 的反面**：在本族上**不**点识别（`cfLower = 0 < 1 = cfUpper`）。

⟹ 由 `pointIdent_iff_lower_eq_upper` 的逆否，`PointIdent` 不成立
（与 `weak_no_point_ident` 同义，但走上下界路线）。 -/
theorem open_not_pointIdent_via_bounds
    (hp : PointIdent 𝔐open false false true false) : False := by
  have heq := lower_eq_upper_of_pointIdent 𝔐open false false true false hp
  rw [open_Lower, open_Upper] at heq
  exact absurd heq (by norm_num)

/-- ⭐⭐ **识别集恰为 `[0,1]` 的两个端点**：`cfLower` 与 `cfUpper` **本身都可达**。

⟹ 在**本具体族**上界是**紧的**（sharp）：没有更小的区间能包住可达值。 -/
theorem open_bounds_attained :
    cfLower 𝔐open false false true false ∈ cfIdentSet 𝔐open false false true false
    ∧ cfUpper 𝔐open false false true false ∈ cfIdentSet 𝔐open false false true false := by
  rw [open_Lower, open_Upper]
  exact ⟨mem_cfIdentSet_open_0, mem_cfIdentSet_open_1⟩

end PointIdent
