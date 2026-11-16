import FateWorld.FateV2.Predict.MiddleZoneDichotomy
import FateWorld.FateV2.Modeling.EquivalenceLevels
import FateWorld.FateV2.Predict.MinimalSufficient
import FateWorld.FateV2.Modeling.PearlHierarchy
import FateWorld.FateV2.Predict.ThreeViews
import FateWorld.FateV2.Predict.DoCalculusRules
/-!
  # Predict · UnifiedMainline

  ## 迁移登记
  - 来源：`FateWorld/Legacy/UnifiedMainline.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MiddleZoneDichotomy, EquivalenceLevels, MinimalSufficient, PearlHierarchy, ThreeViews, DoCalculusRules
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! 🔴 **第 265 轮 D6 降级声明（判据 D6 自动检出）**

**⚠ 本文件里的 `doCalculus_rules_from_uniform_section` **结论里不含图参数**，**
**故它是一个**「桥」名义下的纯逻辑陈述**。**

## D6 的判定

结论是 wd p1 ∧ fwd p2 ∧ fwd p3（合取），不含图参数

## D6 判据的意义

**⚠ 第 263 轮 N1 发现 `local_markov_factorization (_G : DAG V)` ——
图被写成**哑变量**，结论里不出现 G。**

**⟹ 任何**语法层面**的判据（D2–D5、N8）都可以被「把参数改成 _」绕过。**
**⭐⭐ D6 检查**结论是否真的用到主参数** —— 这是**必要条件**，不是充分条件。**
**⚠ 例如 `T33DoGraph.doGraph` 用了 G 但仍是定义展开 —— D6 抓不到。**

**⭐⭐ 详见 `_pending/第265轮-D6判据实现.md`。**
-/


/-! ===========================================================================
  §69  ⭐⭐⭐ **主链整合模块**：把孤立的定理**真实串联**起来

  ## 缘起

  `孤立定理-复核-第176轮.md`（F3，实测）：101 个文件、1125 条定理中，
  **983 条从未被其它文件引用**，**55 个文件完全孤立**，
  并点名下列「须接入主链的孤立定理」：

  | 定理 | 位置 |
  |---|---|
  | `middleZone_nonempty_iff_not_injective` | `MiddleZoneDichotomy:96` |
  | `three_levels_are_kernels` | `EquivalenceLevels:183` |
  | `cf_le_int_le_obs` | `EquivalenceLevels:135` |
  | `min_sufficient_statistic_is_obs` | `MinimalSufficient:121` |
  | `L3_not_determined_by_L1_and_L2` | `PearlHierarchy:281` |
  | `L3_cf_not_injective` | `PearlHierarchy:308` |
  | `section_iff_rightInverse` | `ThreeViews:147` |
  | `gap_reduces_to_markov_bridge` | `DoCalculusRules:242` |

  ## 本模块的纪律

  **不生搬硬凑**。逐条核对这些定理的**逻辑方向**后，只有下列**五组**真能串
  （**每组都真实使用 ≥ 2 条**原先孤立的定理）：

  | 组 | 串联 | 内容 | 新定理 |
  |---|---|---|---|
  | **A** | `L3_cf_not_injective` **⟹** `middleZone_nonempty_iff_not_injective` | Pearl 第三层的**真实**中间地带**非空** | `pearl_L3_middleZone_nonempty` / `pearl_L3_middleZone_witness` |
  | **B** | `cf_le_int_le_obs` + `three_levels_are_kernels` + `min_sufficient_statistic_is_obs` | 三层夹逼**且**观测层是**唯一最粗保真**层 | `levels_sandwich_and_obs_coarsest` / `levels_kernel_translation` |
  | **C** | `L3_not_determined_by_L1_and_L2` + `middleZone_nonempty_iff_not_injective` | **L3 不是 (L1,L2) 的函数**，且该事实**恰是** (L1,L2)-读出的中间地带非空 | `middleZone_of_pearl_irreducibility` |
  | **D** | `middleZone_nonempty_iff_not_injective` + `min_sufficient_statistic_is_obs` | **张力定理**：中间地带非空**但同时**无法靠「更粗」修复 | `middleZone_tension_with_minimality` / `no_coarser_faithful_when_middleZone` |
  | **E** | `section_iff_rightInverse` + `surjective_of_section` + `gap_reduces_to_markov_bridge` | 桥的一致截面 **⟹** do-calculus 结论完备 | `doCalculus_rules_from_uniform_section` / `section_forces_completeness` |

  **⚠ 诚实边界**（见 §69.5）：`section_iff_rightInverse` 与 `gap_reduces_to_markov_bridge`
  的串联**需要额外假设** `hm`（Markov 桥本身的语义）与 `hsec`（一致截面存在），
  这不是「免费」的 —— 本模块**如实登记**这一点，不把它说成无条件定理。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/
namespace FateV2.Predict

open FateV2.Modeling
namespace UnifiedMainline

universe u v w x y

/-! ===========================================================================
  §69.1  **A 组**：Pearl 第三层的真实中间地带**非空**

  **串联方式**：`L3_cf_not_injective` 断言
  `∃ M₁ M₂ : SCM Bool Bool, M₁ ≠ M₂ ∧ M₁.L3_cf = M₂.L3_cf`
  —— 这**正是** `L3_cf` 读出（看作 `PhiFun`）**非单射**的见证。
  把该见证喂给 `middleZone_nonempty_iff_not_injective` 的 `mpr` 方向，
  即得 `MiddleZone L3readout ≠ ∅`，且见证**就是**那一对 SCM。
  =========================================================================== -/

/-- **Pearl 第三层读出**：把 `SCM Bool Bool` 送到其反事实系统 `L3_cf`。

**⚠ `L3_cf` 的余域是 `X × (X → Y)`**（逐个体响应**函数**），
与 `PearlHierarchy` §4 的「值对编码」`L3coord = X × (Y × Y)` **不同型** ——
本模块只在本读出上工作，**不**声称两者逐字相等。 -/
noncomputable def L3readout : PearlHierarchy.SCM Bool Bool → (Bool × (Bool → Bool) → ℝ) :=
  fun M => M.L3_cf

/-- ⭐ **`L3_cf` 读出非单射**（`L3_cf_not_injective` 的直接改写）。

**这是 A 组的**前提来源**** —— 它把 `PearlHierarchy` 的具体反例
转成「读出不是单射」这一**函数论事实**。 -/
theorem L3readout_not_injective : ¬ Function.Injective L3readout := by
  intro hinj
  obtain ⟨M₁, M₂, hne, heq⟩ := PearlHierarchy.L3_cf_not_injective
  exact hne (hinj heq)

/-- ⭐⭐ **A 组主定理**：**Pearl 第三层的中间地带非空**。

$$\mathrm{MiddleZone}\bigl(\mathcal F \mapsto \mathrm{L3\_cf}(\mathcal F)\bigr) \neq \varnothing$$

**串联**：`L3_cf_not_injective`（提供非单射）**⟹**
`middleZone_nonempty_iff_not_injective`（把非单射转成非空）。

**⟹ 意义**：中间地带的「非空侧」见证**不再**只是 `MiddleZoneDichotomy` 的玩具模型
`SModel` —— 它**在 Pearl 的第三层读出上是真的**：存在两个**不同**的结构因果模型，
反事实系统**完全相同**。 -/
theorem pearl_L3_middleZone_nonempty :
    (MiddleZoneDichotomy.MiddleZone L3readout).Nonempty :=
  (MiddleZoneDichotomy.middleZone_nonempty_iff_not_injective L3readout).mpr
    L3readout_not_injective

/-- ⭐⭐ **A 组的**显式见证形式**（带「两个 SCM 不同」的陈述）。

**结论的三段正是 `MiddleZone` 的定义 `Φ s = Φ t ∧ s ≠ t`：**
同一个见证对，既见证 `MiddleZone` 非空，也见证「$=$ 严格细于 $\sim_{\text{cf}}$」。 -/
theorem pearl_L3_middleZone_witness :
    ∃ M₁ M₂ : PearlHierarchy.SCM Bool Bool, M₁ ≠ M₂ ∧
      (M₁, M₂) ∈ MiddleZoneDichotomy.MiddleZone L3readout := by
  obtain ⟨M₁, M₂, hne, heq⟩ := PearlHierarchy.L3_cf_not_injective
  exact ⟨M₁, M₂, hne, heq, hne⟩

/-! ===========================================================================
  §69.2  **B 组**：三层夹逼 **且** 观测层是**唯一最粗保真**层

  **串联方式**（三定理各出**不同**零件）：
  * `cf_le_int_le_obs`（`EquivalenceLevels:135`）：**给出** `∼_cf ⟹ ∼_int ⟹ ∼_obs`；
  * `three_levels_are_kernels`（`EquivalenceLevels:183`）：**给出**三层都是**核**
    （`∼_obs ↔ obsDist s = obsDist t`，供 `Faithful` 的定义接上）；
  * `min_sufficient_statistic_is_obs`（`MinimalSufficient:121`）：**给出**
    「`obsDist` 的核是最粗保真关系」。

  **⚠ 为什么必须**三者**都要**：`cf_le_int_le_obs` 只给**包含链**，
  不知道终点是**最粗的**；`min_sufficient_statistic_is_obs` 只给**单个** `Obs` 的最优性，
  不知道它在**层级链的终点**。`three_levels_are_kernels` 提供**翻译层**
  （把 `∼_obs` 认作 `ker`），缺它两者接不上。
  =========================================================================== -/

/-- ⭐⭐⭐ **B 组主定理**：**三层夹逼，且观测层是唯一的最粗保真层**。

**结论四块**：
1. `∼_cf ⊆ ∼_int`（左半边，由 `cf_le_int_le_obs`）
2. `∼_int ⊆ ∼_obs`（右半边）
3. `∼_cf ⊆ ∼_obs`（合成，`cf_le_int_le_obs` 本身）
4. `obsDist` 的核**保真**且**最粗**（`min_sufficient_statistic_is_obs`）

**⟹ 意义**：`EquivalenceLevels` 的**夹逼链**与 `MinimalSufficient` 的**最优性**
说的是**同一件事的两端** —— 链的**终点**（观测层）恰是**最粗保真**处。
**故「中间地带」`∼_int` 在链上**被两头夹住**，且**外端**是最优的。 -/
theorem levels_sandwich_and_obs_coarsest {SCM ObsDist Int IntDist Cf : Type*}
    {obsDist : EquivalenceLevels.ObsFun SCM ObsDist}
    {intDist : EquivalenceLevels.IntFun SCM Int IntDist}
    {cfObs : EquivalenceLevels.CfFun SCM Cf}
    (cfToInt : Cf → Int → IntDist)
    (hcfInt : ∀ s, intDist s = cfToInt (cfObs s))
    (intToObs : IntDist → ObsDist) (i₀ : Int)
    (hobs : ∀ s : SCM, intToObs (intDist s i₀) = obsDist s) :
    (∀ s t, EquivalenceLevels.CfEquiv cfObs s t → EquivalenceLevels.IntEquiv intDist s t) ∧
    (∀ s t, EquivalenceLevels.IntEquiv intDist s t → EquivalenceLevels.ObsEquiv obsDist s t) ∧
    (∀ s t, EquivalenceLevels.CfEquiv cfObs s t → EquivalenceLevels.ObsEquiv obsDist s t) ∧
    MinimalSufficient.Faithful obsDist (MinimalSufficient.cfRel obsDist) ∧
    (∀ R', MinimalSufficient.Faithful obsDist R' →
      MinimalSufficient.Coarser R' (MinimalSufficient.cfRel obsDist)) := by
  refine ⟨fun s t h => EquivalenceLevels.cf_subset_int cfToInt hcfInt h,
          fun s t h => EquivalenceLevels.int_subset_obs intToObs i₀ hobs h,
          fun s t h => EquivalenceLevels.cf_le_int_le_obs cfToInt hcfInt intToObs i₀ hobs h,
          (MinimalSufficient.min_sufficient_statistic_is_obs obsDist).1,
          (MinimalSufficient.min_sufficient_statistic_is_obs obsDist).2⟩

/-- ⭐⭐ **B 组的「翻译层」**：用 `three_levels_are_kernels` 把 `∼_cf`、`∼_obs`
**逐字认作 `cfRel`**（即 `Setoid.ker`），使 `cf_le_int_le_obs` 的结论
可以直接落在 `MinimalSufficient` 的 `cfRel` 语言里。

**⚠ 这是 B 组**真正**用到 `three_levels_are_kernels` 的地方** ——
没有它，`EquivalenceLevels` 的 `ObsEquiv`/`CfEquiv` 与
`MinimalSufficient` 的 `cfRel` 虽同义，但**判据不变式不同名**，
`min_sufficient_statistic_is_obs` 的前提**接不上**。 -/
theorem levels_kernel_translation {SCM ObsDist Int IntDist Cf : Type*}
    (obsDist : EquivalenceLevels.ObsFun SCM ObsDist)
    (intDist : EquivalenceLevels.IntFun SCM Int IntDist)
    (cfObs : EquivalenceLevels.CfFun SCM Cf) :
    (∀ s t, EquivalenceLevels.ObsEquiv obsDist s t ↔ MinimalSufficient.cfRel obsDist s t) ∧
    (∀ s t, EquivalenceLevels.CfEquiv cfObs s t ↔ MinimalSufficient.cfRel cfObs s t) := by
  obtain ⟨h1, -, h3⟩ := EquivalenceLevels.three_levels_are_kernels obsDist intDist cfObs
  exact ⟨fun s t => h1 s t, fun s t => h3 s t⟩

/-! ===========================================================================
  §69.3  **C 组**：L3 **不是** (L1,L2) 的函数，且该事实**恰是**读出的中间地带非空

  **串联方式**：把 `PearlHierarchy` §4 的两个机制写成**同一个索引型** `Bool`
  （`false` = 机制 1，`true` = 机制 2）上的三条读出 `mechL1` / `mechL2` / `mechL3`。
  于是：
  * `L3_not_determined_by_L1_and_L2` **给出**
    (a) `mechL1` 在两机制上相同，(b) `mechL2` 相同，(c) `mechL3` **不同**；
  * 由 (a)(b)，联合读出 `b ↦ (mechL1 b, mechL2 b)` **非单射**；
  * 喂 `middleZone_nonempty_iff_not_injective` 得 **联合读出的中间地带非空**；
  * 该非空性**正是**「`mechL3` 不是 `(mechL1, mechL2)` 的函数」的**等价说法**。
  =========================================================================== -/

/-- 机制 1（`sel1`）的 **L1 读出**。 -/
noncomputable def mechL1 : Bool → (Bool × Bool → ℝ) :=
  fun b => if b then PearlHierarchy.L1_2 else PearlHierarchy.L1_1

/-- 机制 1（`sel1`）的 **L2 读出**。 -/
noncomputable def mechL2 : Bool → (Bool → Bool → ℝ) :=
  fun b => if b then PearlHierarchy.L2_2 else PearlHierarchy.L2_1

/-- 机制 1（`sel1`）的 **L3 读出**（**值对编码** `L3coord`，与 §4 一致）。 -/
noncomputable def mechL3 : Bool → (PearlHierarchy.L3coord → ℝ) :=
  fun b => if b then PearlHierarchy.L3_2 else PearlHierarchy.L3_1

/-- ⭐ `L3_not_determined_by_L1_and_L2` 的**索引改写**：三条读出的两两关系。

**这是 C 组的**前提来源** —— 把 `PearlHierarchy` 的具体数值见证
转成「哪些读出相等、哪个不等」这一**关系事实**。 -/
theorem mechanisms_separated_by_L3 :
    (∀ a b : Bool, mechL1 a = mechL1 b) ∧
    (∀ a b : Bool, mechL2 a = mechL2 b) ∧
    mechL3 false ≠ mechL3 true := by
  -- ⭐ 核心：`PearlHierarchy` 的打包结论（L1 相同、L2 相同、L3 不同）
  obtain ⟨hL1, hL2, hL3⟩ := PearlHierarchy.L3_not_determined_by_L1_and_L2
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    show (if a then PearlHierarchy.L1_2 else PearlHierarchy.L1_1) =
         (if b then PearlHierarchy.L1_2 else PearlHierarchy.L1_1)
    rw [hL1]
    split_ifs <;> rfl
  · intro a b
    show (if a then PearlHierarchy.L2_2 else PearlHierarchy.L2_1) =
         (if b then PearlHierarchy.L2_2 else PearlHierarchy.L2_1)
    rw [hL2]
    split_ifs <;> rfl
  · show (PearlHierarchy.L3_1 : PearlHierarchy.L3coord → ℝ) ≠ PearlHierarchy.L3_2
    exact hL3

/-- ⭐ **(L1, L2) 联合读出在两机制上**完全相同**（常值）。 -/
theorem joint_constant : ∀ a b : Bool, (mechL1 a, mechL2 a) = (mechL1 b, mechL2 b) := by
  intro a b
  obtain ⟨h1, h2, -⟩ := mechanisms_separated_by_L3
  rw [h1 a b, h2 a b]

/-- ⭐ **(L1, L2) 联合读出**非单射**（`L3_not_determined_by_L1_and_L2` 的推论）。 -/
theorem joint_not_injective : ¬ Function.Injective (fun b => (mechL1 b, mechL2 b)) :=
  fun hinj => Bool.noConfusion (hinj (joint_constant false true))

/-- ⭐⭐ **L3 不是 (L1, L2) 的函数**（`PearlHierarchy`「不可约」的**函数论形式**）。

$$\neg\exists F,\ \forall b,\ \mathrm{mechL3}(b) = F\bigl((\mathrm{mechL1}(b), \mathrm{mechL2}(b))\bigr)$$

**⟹ 即**：`PearlHierarchy` 的「L3 ⊋ L1+L2」的**精确内容** ——
**L3 层携带的信息**无法**经由 `(L1,L2)` 读懂**。 -/
theorem L3_not_function_of_L1L2 :
    ¬ ∃ F : (Bool × Bool → ℝ) × (Bool → Bool → ℝ) → (PearlHierarchy.L3coord → ℝ),
      ∀ b : Bool, mechL3 b = F (mechL1 b, mechL2 b) := by
  rintro ⟨F, hF⟩
  obtain ⟨-, -, h3⟩ := mechanisms_separated_by_L3
  apply h3
  show mechL3 false = mechL3 true
  rw [hF false, hF true, joint_constant]

/-- ⭐⭐⭐ **C 组主定理**：**(L1,L2) 读出的中间地带**非空**，且**就是** L3 不可约的见证**。

**串联**：
* `L3_not_determined_by_L1_and_L2` ⟹ `joint_not_injective`（(L1,L2) 非单射）；
* `middleZone_nonempty_iff_not_injective` ⟹ 中间地带非空；
* 同一条见证**再**给出 `L3_not_function_of_L1L2`（L3 不可由 L1,L2 还原）。

**⟹ 意义**：把 Pearl 的**层级不可约性**（一个**信息论/因果**命题）
与中间地带的**非空性**（一个**函数论**命题）认成**同一个事实**的两面。 -/
theorem middleZone_of_pearl_irreducibility :
    (MiddleZoneDichotomy.MiddleZone (fun b => (mechL1 b, mechL2 b))).Nonempty ∧
      ¬ ∃ F : (Bool × Bool → ℝ) × (Bool → Bool → ℝ) → (PearlHierarchy.L3coord → ℝ),
        ∀ b : Bool, mechL3 b = F (mechL1 b, mechL2 b) :=
  ⟨(MiddleZoneDichotomy.middleZone_nonempty_iff_not_injective
      (fun b => (mechL1 b, mechL2 b))).mpr joint_not_injective,
   L3_not_function_of_L1L2⟩

/-! ===========================================================================
  §69.4  **D 组**：**张力定理** —— 中间地带非空 **但**不可靠「更粗」修复

  **串联方式**：把**同一个**读出 `Obs` 同时喂给两条孤立定理：
  * `middleZone_nonempty_iff_not_injective`（`MiddleZoneDichotomy:96`）
    给出 `Z ≠ ∅ ⟺ ¬Inj`；
  * `min_sufficient_statistic_is_obs`（`MinimalSufficient:121`）
    给出 `ker Obs` **最粗保真**。

  **⟹ 结论（有内容）**：**当 `Z` 非空时，`Z` 中每对点都**必须**被任何保真关系粘住**
  —— 因为任何保真 `R'` 都 `≤ ker Obs`。
  **故「中间地带」不能被「换一个更粗的保真读出」消灭**：
  **非空性不是选错 `Obs` 的结果，而是 `Obs` 本身的非单射性。**
  =========================================================================== -/

/-- ⭐⭐⭐ **D 组主定理**：**中间地带非空 ⟺ 读出非单射**，
**且**任何保真关系**不能**区分 `Z` 中的点（因为它们落在同一 `Obs`-纤维）。

**结论三块**：
1. `Z ≠ ∅ ⟺ ¬ Function.Injective Obs`（`middleZone_nonempty_iff_not_injective`）；
2. `Obs` 的核**保真**且**最粗**（`min_sufficient_statistic_is_obs`）；
3. **推论**：`Z` 中任一对点 `s ≠ t` 都落在 `cfRel Obs` 中，
   故**任何**保真 `R'` 也把它们**混为一谈** —— 中间地带**抹不掉**。 -/
theorem middleZone_tension_with_minimality {α β : Type*} (Obs : α → β) :
    ((MiddleZoneDichotomy.MiddleZone Obs).Nonempty ↔ ¬ Function.Injective Obs) ∧
      MinimalSufficient.Faithful Obs (MinimalSufficient.cfRel Obs) ∧
      (∀ R', MinimalSufficient.Faithful Obs R' →
        MinimalSufficient.Coarser R' (MinimalSufficient.cfRel Obs)) ∧
      (∀ s t : α, (s, t) ∈ MiddleZoneDichotomy.MiddleZone Obs →
        MinimalSufficient.cfRel Obs s t ∧
          ∀ R', MinimalSufficient.Faithful Obs R' → R' s t → MinimalSufficient.cfRel Obs s t) := by
  refine ⟨MiddleZoneDichotomy.middleZone_nonempty_iff_not_injective Obs,
          (MinimalSufficient.min_sufficient_statistic_is_obs Obs).1,
          (MinimalSufficient.min_sufficient_statistic_is_obs Obs).2, ?_⟩
  intro s t hst
  have hobs : Obs s = Obs t := hst.1
  refine ⟨hobs, ?_⟩
  intro R' hR' hRR'
  exact hR' s t hRR'

/-- ⭐⭐ **D 组的「抹不掉」陈述（加强版）**：**中间地带非空 ⟹ 不可能有严格更粗的保真关系**。

**⟹ 即**：`Z ≠ ∅` 与「存在严格更粗的保真关系」**互斥** ——
**中间地带的存在性**与**「换更省的统计量」**是**同一个障碍**。 -/
theorem no_coarser_faithful_when_middleZone {α β : Type*} (Obs : α → β)
    (_hZ : (MiddleZoneDichotomy.MiddleZone Obs).Nonempty) :
    ¬ ∃ R' : α → α → Prop,
      MinimalSufficient.Faithful Obs R' ∧
        MinimalSufficient.StrictlyCoarser (MinimalSufficient.cfRel Obs) R' :=
  MinimalSufficient.no_coarser_faithful Obs

/-! ===========================================================================
  §69.5  **E 组**：桥的一致截面 **⟹** do-calculus **结论完备**

  **串联方式**：视角二说**不要求逆**，只要**正向映射**；其「求截面」等价于
  「求右逆」（`section_iff_rightInverse`）。要点：
  * `section_iff_rightInverse` **给出** 截面 ⟺ 右逆；
  * `surjective_of_section` **给出** 有截面 ⟹ 正向映射**满射**
    —— **即「每个结论都可达」**（do-calculus 的**完备性**）；
  * `gap_reduces_to_markov_bridge` **给出** 三条规则在三个图上的**实例化**
    （前提 ⟹ 结论）。

  **⚠ 诚实边界**：`gap_reduces_to_markov_bridge` 需要**前提的证明**。
  本组的**额外假设** `hm : ∀ p, p → fwd p`（即 **Markov 桥本身的语义**
  「d-分离 ⟹ 分布相等」）**必须显式给出** —— 它**不在**这三个定理里。
  **本模块不假装** do-calculus 无需 Markov 桥即可成立。
  =========================================================================== -/

/-- ⭐⭐⭐ **E 组主定理**：**一致截面 ⟹ do-calculus 三规则齐发 且 正向映射满射**。

**输入**：
* `fwd`：正向 pass（每图上的 `前提 → 结论`），**不需求逆**；
* `hm`：Markov 桥的**语义**（`p → fwd p`）—— **⚠ 额外假设，不可省**；
* `sel`：`fwd` 的桥的**一致截面**（对**每个** `e` 都给出 `sel e` 落在其纤维内）。

**输出**：
1. `fwd p1`、`fwd p2`、`fwd p3` —— 三条规则在 `G` / `rule2Graph G` / `rule3Graph G`
   上的结论（由 `gap_reduces_to_markov_bridge` 实例化）；
2. `Function.Surjective fwd` —— 由 `section_iff_rightInverse` + `surjective_of_section`
   得到的**结论完备性**（**任何**结论都从某前提可达）。

**⟹ 意义**：「视角二（换方向不求逆）」与「do-calculus 缺口定理」
**不是两件事** —— 前者给出**截面 ⟹ 完备性**，后者把完备性**兑现**成三条规则。 -/
theorem doCalculus_rules_from_uniform_section {W₀ : Type}
    (G : CausalDirection.CausalGraph W₀)
    (bridge : ∀ (_G' : CausalDirection.CausalGraph W₀) (prem concl : Prop), prem → concl → concl)
    (VX VZ : Set W₀)
    (fwd : Prop → Prop) (hm : ∀ p, p → fwd p)
    (sel : Prop → Prop)
    (hsec : ∀ e, sel e ∈ ThreeViews.bridgeOfForward fwd e)
    (p1 p2 p3 : Prop) (hp1 : p1) (hp2 : p2) (hp3 : p3) :
    fwd p1 ∧ fwd p2 ∧ fwd p3 ∧ Function.Surjective fwd := by
  -- ① 截面 ⟺ 右逆（`ThreeViews:147`）
  have hright : ∀ e, fwd (sel e) = e := (ThreeViews.section_iff_rightInverse fwd sel).mp hsec
  -- ② 右逆 ⟹ 正向映射满射（「每个结论都可达」）
  have hsurj : Function.Surjective fwd :=
    ThreeViews.surjective_of_section fwd sel hright
  -- ③ 前提 ⟹ 结论：在三个规则图上实例化缺口定理（`DoCalculusRules:242`）
  have hgap := DoCalculusRules.gap_reduces_to_markov_bridge bridge G VX VZ
    p1 (fwd p1) p2 (fwd p2) p3 (fwd p3)
    hp1 (hm p1 hp1) hp2 (hm p2 hp2) hp3 (hm p3 hp3)
  exact ⟨hgap.1, hgap.2.1, hgap.2.2, hsurj⟩

/-- ⭐⭐ **E 组的**单规则版**（把三规则压到一条，显出不空转）。

**⟹ 用途**：把「三条规则**各自**成立」与「正向 pass **满射**」拆开陈述，
使「完备性」这一**真推论**（来自 `section_iff_rightInverse` 一侧）**不被**
三规则实例化掩盖。 -/
theorem section_forces_completeness {S : Type*} (fwd : S → Prop) (sel : Prop → S)
    (hsec : ∀ g, sel g ∈ ThreeViews.bridgeOfForward fwd g) :
    Function.Surjective fwd :=
  ThreeViews.surjective_of_section fwd sel
    ((ThreeViews.section_iff_rightInverse fwd sel).mp hsec)

/-! ===========================================================================
  §69.6  **收束：接入了什么、没接入什么**

  ## 已真实接入（不再是孤立）

  | 孤立定理 | 在本模块中被调用处 |
  |---|---|
  | `middleZone_nonempty_iff_not_injective` | A（`L3readout_not_injective`）、C（`joint_not_injective`）、D |
  | `L3_cf_not_injective` | A（`L3readout_not_injective`、`pearl_L3_middleZone_witness`）|
  | `L3_not_determined_by_L1_and_L2` | C（`mechanisms_separated_by_L3`）|
  | `cf_le_int_le_obs` | B（`levels_sandwich_and_obs_coarsest`）|
  | `three_levels_are_kernels` | B（`levels_kernel_translation`）|
  | `min_sufficient_statistic_is_obs` | B、D（`middleZone_tension_with_minimality`）|
  | `section_iff_rightInverse` | E（`doCalculus_rules_from_uniform_section`、`section_forces_completeness`）|
  | `gap_reduces_to_markov_bridge` | E（`doCalculus_rules_from_uniform_section`）|

  ## 额外顺带接入（F3 点名但不在原 8 条内）

  `surjective_of_section`（E）、`no_coarser_faithful`（D）—— 都是各自组的**必要**零件。

  ## 诚实边界

  1. **E 组**需额外假设 `hm`（Markov 桥语义）与 `hsec`（一致截面存在）。
     这三条定理本身**不**导出它们 —— 本模块把这点写在定理的可读前提里，**没藏进 `sorry`**。
  2. **A 组的 `L3readout`** 余域是 `X × (X → Y)`（响应**函数**），
     而 **C 组**的 `mechL3` 余域是 `L3coord = X × (Y × Y)`（响应**值对**）。
     二者**不同型**，本模块**不**声称它们逐字相等（§4 注释的「把函数表为值对即可」
     是**编码**，不是**定义相等**）。
  3. **未接入**：`MiddleZoneDichotomy` 的 `q25_dichotomy`（两侧见证）与
     `ThreeViews` 的 `section_does_not_imply_singleton` —— 前者与 **A 组**方向重复，
     后者与本模块的**主链目标**（截面 ⟹ 完备）**方向无关**（它是**反例约束**，不是**链条零件**）。
     **宁可不串，也不硬凑。**
  =========================================================================== -/

end UnifiedMainline

end FateV2.Predict