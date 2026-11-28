/-
  `Fate/NonemptyFree2` —— **DOWN-1 A 类扩展（第二批）：再找 4+ 条可去的 `[Nonempty]`**

  ## 本文件做什么

  上一批 `Fate/NonemptyFree.lean` 只实测了 3 条。本文件**再**对下面 6 条具体定理
  给出**无 `[Nonempty]` 版本**（原定理**原样保留、未改动**）。

  | # | 原定理（**未改动**） | 所在模块 | 原 `[Nonempty]` | 结论 |
  |---|---|---|---|---|
  | 1 | `FateV2.Predict.T35Rule1Split.rule1_of_separable` | `T35Rule1Split` | `[Nonempty Ux] [Nonempty Uy]` | ✅ 可去 |
  | 2 | `FateV2.Predict.T35Rule1Split.rule1_of_fullNoConfounding` | `T35Rule1Split` | 同上 | ✅ 可去 |
  | 3 | `FateV2.Predict.T35Rule1Split.noConfounding_of_fullNoConfounding` | `T35Rule1Split` | 同上 | ✅ 可去 |
  | 4 | `FateV2.Predict.T35Rule1Split.rule1_normalized` | `T35Rule1Split` | 同上 | ✅ 可去 |
  | 5 | `SCMIdentifiability.scmThetaSubsingleton_pred_eq` | `SCMIdentifiability` | `[Nonempty Y]` | ✅ 可去（**完全未用**）|
  | 6 | `LawRule.PointDecidabilityConsumer.isPoint_genRule_of_finset_card_one` | `LawRulePointDecidabilityConsumer` | `[Nonempty C.Carrier] [Nonempty X.Carrier]` | ✅ 可去（空型时空真）|
  | 7 | `FateV2.Predict.Strategy11.peel_lower` | `Strategy11TopoPrefix` | `[Nonempty V]` | ✅ 可去（**空积与 `hfac` 同时给 `1`**）|
  | 8 | `FateV2.Predict.Strategy11.peel_lower_univ_minus` | `Strategy11TopoPrefix` | 同上 | ✅ 可去（转调 7）|
  | 9 | `FateV2.Predict.Strategy11.peel_top_vertex` | `Strategy11TopoPrefix` | 同上 | ✅ 可去（转调 7）|
  | 10 | `FateV2.Predict.NonemptyFree2.Strategy11Fiber.mass_prefix` | `Strategy11FiberPinned` | 同上 | ✅ 可去（转调 7）|

  ⚠ **本文件共交 10 条**（任务要求 ≥4 条）。

  ## 逐条理由（判据 1/2/3 的核对）

  ### 1–4：`T35Rule1Split` 的四条（同一来源、四种不同结论形式）

  四条共享前件 `SeparablePU M e`，其定义为
  ```
  SeparablePU M e := ∃ pX pY, (∀ u v, p_U(u,v) = pX u * pY v)
                                ∧ (∑ u, pX u) = 1 ∧ (∑ v, pY v) = 1
  ```
  **`Ux` 为空**时 `∑ u : Ux, pX u = 0`（空和），故 `hpX : 0 = 1` **矛盾**
  ⟹ `hsep` 在 `Ux` 空时**不可满足** ⟹ 定理**空真**。
  **`Uy` 为空**时同理（`hpY : 0 = 1`）。
  ⟹ 原证用 `obtain ⟨u₀⟩ := ‹Nonempty Ux›` / `obtain ⟨v₀⟩ := ‹Nonempty Uy›`
  只是**取代表元**构造 `Au`/`Bv`；**空型下根本走不到那一步**（前件已矛盾）。
  ⟹ 满足判据 2「该假设只用于构造默认值/代表元」且判据 3「A 与 Nonempty 无关」。

  **四条结论形式各不相同**（不是同一条换名）：
  - (1) `condY = marginalX * doLaw`（逐点等式，需 `hx`/`hy`）
  - (2) 同一等式，但前件换成打包的 `FullNoConfounding`
  - (3) `NC M`（谓词全称化，`Rule1Semantic` 的语义式）
  - (4) `condY / marginalX = doLaw`（归一化形式，多一个 `hpos`）

  ### 5：`scmThetaSubsingleton_pred_eq` —— `[Nonempty Y]` **完全未用**

  结论 `(M.sg θ₁ u).2 a = (M.sg θ₂ u).2 a` 与 `Y` **是否非空无关**：
  类型 `(M.sg θ u).2 a : Y` 的比较由 `Subsingleton.elim θ₁ θ₂` 直接给出，
  证明体 `rw [Subsingleton.elim θ₁ θ₂]` **一次都没读 `‹Nonempty Y›`**。
  ⟹ 判据 1（结论不用 `Classical.arbitrary`/`Nonempty.some`）✅、
  判据 2（只作默认值——这里是**连默认值都没用**）✅、
  判据 3（A 与 Nonempty 无关：A 是 `Subsingleton M.Th`）✅。

  **⚠ 与之相对**：同文件的 `prediction_eq`（`Prediction M θ u ε a x = (M.sg θ u).2 a`）
  **不可去** —— `Prediction` 的定义体内是 `paramScmWorldModel M`，而
  `paramScmWorldModel` 的 `state.cur` 需要一个具体 `Y` 值。这是**结构需要**（B 类），
  见文末 §7 反向记录。

  ### 6：`isPoint_genRule_of_finset_card_one` —— 空型时结论**空真**

  `IsPoint R := ∀ c x, ∃ μ, R c x = {μ}`，其量化域是 `C.Carrier × X.Carrier`。
  `C.Carrier` 或 `X.Carrier` 为空 ⟹ 全称量化域为空 ⟹ **结论空真**。
  而原证的 `(isPoint_genRule_iff_search G g).mpr ⟨i₀, hi₀, hcard, hsub⟩`
  显示：结论**实际上由搜索条件**（`hi₀`/`hcard`/`hsub`）决定，与 `C`/`X` 无关。
  ⟹ 空型分支给空真见证、非空分支复用原定理。

  **⚠ 与上一批 §4 第 3 条的关系**：上一批记录了
  `LawRule.isPoint_genRule_iff`（同文件的 **iff** 版本）**不可去** ——
  那是正确的，因为 iff 的右边（`∃ i₀ ... ∧ g i₀ = ⋃ ...`）**与 `C`/`X` 无关**，
  在空型下 `True ↔ (可能为假的右边)` 不成立。
  **本条的 `⟸` 方向（`isPoint_genRule_of_finset_card_one`）不同**：
  它的前件 `hi₀/hcard/hsub` **已经是**右边的见证，故不踩那个坑。

  ## ⚠ 不变式

  **本文件不修改任何已有模块**（原定理原样保留），只**新增**定理。
  零 `sorry` / `admit` / `axiom` / `native_decide`。

  ## ⚠ 前件检查（纪律 7：前件是否已把结论包进去）

  | 定理 | 前件 | 结论 | 是否同义反复 |
  |---|---|---|---|
  | 1 | `XReadsOnlyUx`、`YReadsOnlyUy`、`SeparablePU` | `condY = marginalX * doLaw` | **否**：前件是「读集/可分离/归一」，结论是**数值恒等式**，中间隔 `fac_general` 的代数 |
  | 2 | `FullNoConfounding`（= 上面三条的合取） | 同上 | **否**（同上；只看前件的**投影**） |
  | 3 | 同上 | `NC M`（= `∀ x y, condY = marginalX * doLaw`） | **否**：这是 (2) 的全称化，前件里没有 `NC` 字段 |
  | 4 | 同上 + `hpos` | `condY / marginalX = doLaw` | **否**：除以 `marginalX` 是**新的**代数步骤 |
  | 5 | `Subsingleton M.Th` | `(sg θ₁ u).2 a = (sg θ₂ u).2 a` | **否**：前件只说 `θ₁ = θ₂`，结论说 `sg` 逐点相等 |
  | 6 | `hi₀`、`hcard`、`hsub` | `IsPoint (genRule G g)` | **否**：前件用 `Finset.card`/成员关系，结论是**单点集**的存在性 |

  **`grep` 双模式核对**：本文件对每条无实例版都用
  `grep -c "Nonempty"` 与 `grep -c "\[Nonempty"` 两种模式核对（见交付说明），
  确认签名中**不含** `[Nonempty]`。
-/

import FateWorld.FateV2.Predict.T35Rule1Split
import FateWorld.FateV2.Loop.SCMIdentifiability
import FateWorld.FateV2.Predict.LawRulePointDecidabilityConsumer
import FateWorld.FateV2.Predict.Strategy11TopoPrefix
import FateWorld.FateV2.Predict.Strategy11FiberPinned
open MeasureTheory

namespace FateV2.Predict.NonemptyFree2

open FateV2.Loop
open FateV2.Modeling

universe u

/-!
  # Predict · NonemptyFree2

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NonemptyFree2.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T35Rule1Split, SCMIdentifiability, LawRulePointDecidabilityConsumer, Strategy11TopoPrefix, Strategy11FiberPinned
  - 补充 open 域：FateV2.Loop, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  `rule1_of_separable` 的无 `[Nonempty]` 版本（判据：前件排除空型）
  =========================================================================== -/

namespace T35Rule1Split

open FateV2.Modeling.PearlHierarchy FateV2.Modeling.SCMSemantics

/-- ⭐ **【无 `[Nonempty Ux] [Nonempty Uy]` 版】**：
`FateV2.Predict.T35Rule1Split.rule1_of_separable` 去掉 `[Nonempty Ux] [Nonempty Uy]` 后**仍然成立**。

**证明策略**：`Ux` 空 ⟹ `SeparablePU` 的 `∑ pX = 1` 变成 `0 = 1`（矛盾）；
`Uy` 空同理。两情形都**复用原证**（原定理由 `hsep` 保证 `Nonempty`）。 -/
theorem rule1_of_separable_noNonempty {X Y Ux Uy : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux] [Fintype Uy]
    [DecidableEq Uy]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (e : M.U ≃ Ux × Uy)
    (hx : FateV2.Predict.T35Rule1Split.XReadsOnlyUx M e)
    (hy : FateV2.Predict.T35Rule1Split.YReadsOnlyUy M e)
    (hsep : FateV2.Predict.T35Rule1Split.SeparablePU M e) (x : X) (y : Y) :
    FateV2.Modeling.SCMSemantics.condY M x y
      = FateV2.Modeling.SCMSemantics.marginalX M x * FateV2.Modeling.SCMSemantics.doLaw M x y := by
  classical
  by_cases hUx : Nonempty Ux
  · by_cases hUy : Nonempty Uy
    · exact FateV2.Predict.T35Rule1Split.rule1_of_separable M e hx hy hsep x y
    · -- `Uy` 空 ⟹ `∑ v, pY v = 0 ≠ 1` ⟹ `hsep` 不可满足
      obtain ⟨pX, pY, -, -, hpY⟩ := hsep
      haveI : IsEmpty Uy := not_nonempty_iff.mp hUy
      simp at hpY
  · -- `Ux` 空 ⟹ `∑ u, pX u = 0 ≠ 1` ⟹ `hsep` 不可满足
    obtain ⟨pX, pY, -, hpX, -⟩ := hsep
    haveI : IsEmpty Ux := not_nonempty_iff.mp hUx
    simp at hpX

/-- ⭐ **【无 `[Nonempty Ux] [Nonempty Uy]` 版】**：
`FateV2.Predict.T35Rule1Split.rule1_of_fullNoConfounding` 的无实例形式。

前件换成打包的 `FullNoConfounding`，直接转调 §1.1。 -/
theorem rule1_of_fullNoConfounding_noNonempty {X Y Ux Uy : Type} [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux]
    [Fintype Uy] [DecidableEq Uy]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (e : M.U ≃ Ux × Uy)
    (h : FateV2.Predict.T35Rule1Split.FullNoConfounding M e) (x : X) (y : Y) :
    FateV2.Modeling.SCMSemantics.condY M x y
      = FateV2.Modeling.SCMSemantics.marginalX M x * FateV2.Modeling.SCMSemantics.doLaw M x y :=
  rule1_of_separable_noNonempty M e h.1.1 h.1.2 h.2 x y

/-- ⭐ **【无 `[Nonempty Ux] [Nonempty Uy]` 版】**：
`FateV2.Predict.T35Rule1Split.noConfounding_of_fullNoConfounding` 的无实例形式。

结论是**谓词** `NC M = ∀ x y, condY M x y = marginalX M x * doLaw M x y`，
由 §1.2 全称化即得。 -/
theorem noConfounding_of_fullNoConfounding_noNonempty {X Y Ux Uy : Type} [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux]
    [Fintype Uy] [DecidableEq Uy]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (e : M.U ≃ Ux × Uy)
    (h : FateV2.Predict.T35Rule1Split.FullNoConfounding M e) :
    FateV2.Predict.T35Rule1Split.NC M :=
  fun x y => rule1_of_fullNoConfounding_noNonempty M e h x y

/-- ⭐ **【无 `[Nonempty Ux] [Nonempty Uy]` 版】**：
`FateV2.Predict.T35Rule1Split.rule1_normalized` 的无实例形式（归一化形式，多一个 `hpos`）。

先在无实例的 §1.1 上 `mul_div_cancel_left₀`，只用到 `hpos`，与 `Nonempty` 无关。 -/
theorem rule1_normalized_noNonempty {X Y Ux Uy : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Ux] [DecidableEq Ux] [Fintype Uy]
    [DecidableEq Uy]
    (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (e : M.U ≃ Ux × Uy)
    (hx : FateV2.Predict.T35Rule1Split.XReadsOnlyUx M e)
    (hy : FateV2.Predict.T35Rule1Split.YReadsOnlyUy M e)
    (hsep : FateV2.Predict.T35Rule1Split.SeparablePU M e)
    (hpos : ∀ x, FateV2.Modeling.SCMSemantics.marginalX M x ≠ 0) (x : X) (y : Y) :
    FateV2.Modeling.SCMSemantics.condY M x y / FateV2.Modeling.SCMSemantics.marginalX M x
      = FateV2.Modeling.SCMSemantics.doLaw M x y := by
  rw [rule1_of_separable_noNonempty M e hx hy hsep x y]
  exact mul_div_cancel_left₀ _ (hpos x)

end T35Rule1Split

/-! ===========================================================================
  §2  `scmThetaSubsingleton_pred_eq` 的无 `[Nonempty Y]` 版本
  =========================================================================== -/

namespace SCMIdentifiability

open FateV2.Predict.ParamSCM

/-- ⭐ **【无 `[Nonempty Y]` 版】**：
`SCMIdentifiability.scmThetaSubsingleton_pred_eq` 去掉 `[Nonempty Y]` 后
**仍然成立**。

**为什么可去**：原证的证明体是 `rw [Subsingleton.elim θ₁ θ₂]`，
`‹Nonempty Y›` **一次都没被读**。`(M.sg θ u).2 a : Y` 的比较与 `Y` 是否非空无关。

**⚠ 这不是同义反复**：前件 `Subsingleton M.Th` 只说 `θ₁ = θ₂`，
结论说 `sg` 在两点上的**第二分量**相等——中间隔 `sg` 的应用。 -/
theorem scmThetaSubsingleton_pred_eq_noNonempty {X Y : Type}
    (M : FateV2.Predict.ParamSCM.ParamSCM X Y) [Subsingleton M.Th]
    (θ₁ θ₂ : M.Th) (u : M.U) (a : X) :
    (M.sg θ₁ u).2 a = (M.sg θ₂ u).2 a := by
  rw [Subsingleton.elim θ₁ θ₂]

end SCMIdentifiability

/-! ===========================================================================
  §3  `isPoint_genRule_of_finset_card_one` 的无 `[Nonempty]` 版本
  =========================================================================== -/

namespace LawRulePointDecidabilityConsumer

/-- ⭐ **【无 `[Nonempty C.Carrier] [Nonempty X.Carrier]` 版】**：
`LawRule.PointDecidabilityConsumer.isPoint_genRule_of_finset_card_one`
去掉两个 `Nonempty` 后**仍然成立**。

**为什么可去**：`IsPoint R := ∀ c x, ∃ μ, R c x = {μ}` 的量化域是
`C.Carrier × X.Carrier`；任一为空时量化域为空 ⟹ **结论空真**。
非空分支**复用原定理**（原证只用搜索条件 `hi₀`/`hcard`/`hsub`）。 -/
theorem isPoint_genRule_of_finset_card_one_noNonempty
    {C : FateV2.Model.CtxSpace} {X : FateV2.Modeling.StateSpace} {Y : FateV2.Model.OutSpace}
    [MeasurableSpace Y.Carrier] {ι : Type}
    [DecidableEq ι] [DecidableEq (MeasureTheory.Measure Y.Carrier)]
    {G : Finset ι} {g : ι → Finset (MeasureTheory.Measure Y.Carrier)} {i₀ : ι}
    (hi₀ : i₀ ∈ G) (hcard : (g i₀).card = 1)
    (hsub : ∀ i ∈ G, ∀ ν ∈ g i, ν ∈ g i₀) :
    FateV2.Rules.LawRule.IsPoint (FateV2.Rules.LawRule.genRule (C := C) (X := X) (Y := Y) G
      (fun i => (g i : Set (MeasureTheory.Measure Y.Carrier)))) := by
  classical
  by_cases hC : Nonempty C.Carrier
  · by_cases hX : Nonempty X.Carrier
    · exact FateV2.Predict.LawRule.PointDecidabilityConsumer.isPoint_genRule_of_finset_card_one
        hi₀ hcard hsub
    · -- `X` 空 ⟹ 量化域空 ⟹ 空真
      intro c x
      exact absurd ⟨x⟩ hX
  · -- `C` 空 ⟹ 量化域空 ⟹ 空真
    intro c _x
    exact absurd ⟨c⟩ hC

end LawRulePointDecidabilityConsumer

/-! ===========================================================================
  §4  `Strategy11` 拓扑前缀引擎家族的 `[Nonempty V]`（**4 条，均可去**）

  ⚠ **本节的来历（如实说明）**：本文件**第一版**曾把
  `Strategy11.peel_lower` 记入「不可去」（原 §4 第 1 条），**那条判断是错的**。
  复核发现：空 `V` 时虽然 `mass ∅ p x = ∑ w, p w`（因 `V → α` 是单点集而等于
  `p (空函数)`），**但** `hfac x : p x = ∏ v, f v x = 1`（空积）**同时**成立，
  故两边**都**等于 `1`。**⟹ `peel_lower` 真的可去。**
  本节给出机检见证（4 条定理），并**保留**更正记录（见 §5 第 1 条）。
  =========================================================================== -/

namespace Strategy11

open FateV2.Predict.NonemptyFree2.Strategy11 FateV2.Predict.FactorMarkov

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : FateV2.Modeling.Graph.DAG V}

set_option linter.unusedSectionVars false

/-- 空 `V` 时 `lowerSet G k` 为空（`lowerSet` 是 `univ.filter`）。 -/
theorem lowerSet_eq_empty_of_not_nonempty (hV : ¬ Nonempty V) (k : ℕ) :
    lowerSet G k = ∅ := by
  unfold lowerSet
  exact Finset.filter_eq_empty_iff.mpr (fun v _ => by
    intro _
    exact hV ⟨v⟩)

/-- 空 `V` 时 `mass ∅ p x = p x`（因 `V → α` 是单点集，求和只剩 `p x`）。 -/
theorem mass_empty_of_not_nonempty (hV : ¬ Nonempty V)
    (p : (V → α) → ℝ) (x : V → α) :
    FateV2.Predict.DAGFactorization.mass (∅ : Finset V) p x = p x := by
  rw [FateV2.Predict.DAGFactorization.mass_empty]
  have hsub : Subsingleton (V → α) := ⟨fun a b => funext fun v => (hV ⟨v⟩).elim⟩
  rw [Finset.sum_eq_single x]
  · intro b _ hb
    exact absurd (Subsingleton.elim b x) hb
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- ⭐ **【无 `[Nonempty V]` 版】顶层引擎**：
`FateV2.Predict.Strategy11.peel_lower` 去掉 `[Nonempty V]` 后**仍然成立**。

**证明策略**：非空分支**复用原证**；空分支用 `lowerSet = ∅` + `mass ∅ p x = p x`
+ `hfac x : p x = ∏ v, f v x = 1`（空积）**两边同时归 `1`**。 -/
theorem peel_lower_noNonempty {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FactorNorm f) :
    ∀ k : ℕ, ∀ x : V → α,
      FateV2.Predict.DAGFactorization.mass (lowerSet G k) p x = ∏ v ∈ lowerSet G k, f v x := by
  classical
  by_cases hV : Nonempty V
  · haveI := hV
    exact peel_lower hloc hfac hnorm
  · intro k x
    rw [lowerSet_eq_empty_of_not_nonempty hV]
    rw [mass_empty_of_not_nonempty hV, Finset.prod_empty]
    rw [hfac x]
    exact Finset.prod_eq_one (fun v _ => absurd ⟨v⟩ hV)

/-- ⭐ **【无 `[Nonempty V]` 版】**：`FateV2.Predict.Strategy11.peel_lower_univ_minus`
去掉 `[Nonempty V]` 后**仍然成立**（直接由上面转调）。 -/
theorem peel_lower_univ_minus_noNonempty {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FactorNorm f) (k : ℕ) (x : V → α) :
    FateV2.Predict.DAGFactorization.mass (lowerSet G k) p x = ∏ v ∈ lowerSet G k, f v x :=
  peel_lower_noNonempty hloc hfac hnorm k x

/-- ⭐ **【无 `[Nonempty V]` 版】**：`FateV2.Predict.Strategy11.peel_top_vertex`
去掉 `[Nonempty V]` 后**仍然成立**（`htop` 把 `univ \ {s}` 换成 `lowerSet`，再转调）。 -/
theorem peel_top_vertex_noNonempty {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FactorNorm f) (s : V)
    (htop : lowerSet G (G.topoOrder s) = (Finset.univ \ {s})) (x : V → α) :
    FateV2.Predict.DAGFactorization.mass (Finset.univ \ {s}) p x
      = ∏ v ∈ (Finset.univ \ {s}), f v x := by
  rw [← htop]
  exact peel_lower_noNonempty hloc hfac hnorm (G.topoOrder s) x

end Strategy11

/-! ===========================================================================
  §4b  `Strategy11Fiber.mass_prefix` 的无 `[Nonempty V]` 版本
  =========================================================================== -/

namespace Strategy11Fiber

open FateV2.Predict.NonemptyFree2.Strategy11 FateV2.Predict.FactorMarkov

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : FateV2.Modeling.Graph.DAG V}

set_option linter.unusedSectionVars false

/-- ⭐ **【无 `[Nonempty V]` 版】**：`FateV2.Predict.NonemptyFree2.Strategy11Fiber.mass_prefix`
去掉 `[Nonempty V]` 后**仍然成立**。

原式只是 `S = lowerSet k` 的包装，故**直接转调** §4 的
`peel_lower_noNonempty`。 -/
theorem mass_prefix_noNonempty {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FactorNorm f) {S : Finset V} (hS : FateV2.Predict.NonemptyFree2.Strategy11Fiber.isPrefix G S) :
    ∀ x, FateV2.Predict.DAGFactorization.mass S p x = ∏ v ∈ S, f v x := by
  obtain ⟨k, rfl⟩ := hS
  exact FateV2.Predict.Strategy11.peel_lower_noNonempty hloc hfac hnorm k

end Strategy11Fiber

/-! ===========================================================================
  §5  ⚠ **反向记录：本轮实测「不可去」的候选**（不写定理，只写结论与理由）
  ===========================================================================

  1. ⚠⚠ **更正**：本文件**第一版**在此处记录了
     `FateV2.Predict.Strategy11.peel_lower` / `peel_lower_univ_minus` 为**不可去**，
     理由是「空 `V` 时 `mass ∅ p x = p (空函数)` 而右边 `= 1`，二者一般不等」。
     **该理由是错的**：`hfac x` 在空 `V` 时给出 `p x = ∏ v : V, f v x = 1`（空积），
     **所以左边也等于 `1`**。见 §4 的 `peel_lower_noNonempty`（机检通过）。
     同理 `peel_top_vertex`、`mass_prefix` **也可去**（§4 / §4b）。
     **⟹ 本条从「不可去名单」移入「已去名单」，保留记录以示更正。**

  2. `FateV2.Predict.optimalPolicy_score` / `optimalPolicy_choose_mem` /
     `InterventionTight.optimalPolicy_isLUB` / `optimalPolicy_sharp`
     （`[Nonempty A] [Nonempty X]`）—— **不可去**。
     `optimalPolicy` 的 `choose : Set (Scenario A X) → Scenario A X` 是**全函数**，
     必须对**空集**也给值；`optimalChoose` 的 else 分支正是
     `⟨Classical.arbitrary A, Classical.arbitrary X⟩`。这是**结构需要**（B 类）。
     上一批的 `optimalChoose_mem` 之所以可去，是因为它的前件 `hne : tree.Nonempty`
     让 `dif_pos hne` 分支**不可达**、故绕开了 else；而 `optimalPolicy` 本身
     **必须构造出来**，else 分支无法绕过。

  3. `FateV2.Predict.WiringBackdoor.wmNum_eq_condYnum` / `wc_wmNum_is_condYnum`
     （`[Nonempty S.X] [Nonempty S.Y]`）—— **不可去**（同上 B 类）。
     `wmNum` 的定义体是 `FateV2.Predict.f (bdWorldModel S) ...`，
     而 `bdWorldModel` 的 `state.cur : S.X × S.Y` 需要一个**具体取值**。
     机制 `f` 虽不读 `cur`，但 `WorldModel` 这个**结构**必须被构造出来。

  4. `FateV2.Modeling.chooseEstimator_apply_of` / `chooseEstimator_of_exists`
     / `EndToEnd.observe_apply_of` / `WorldModelPipeline.pipelineObserve_estimate`
     （`[Nonempty X]`）—— **不可去**（B 类，**不是**「只作默认值」）。
     `chooseEstimator : Y → X` 是**全函数**；若 `X` 空而 `Y` 非空，
     `Y → X` **本身不存在**。故 `[Nonempty X]` 是该**定义**的存在性前提，
     与结论是否读 `‹Nonempty X›`（后者确实不读 else 分支）是两回事。
     **⚠ 诚实标注**：能写出一条「绕过 `chooseEstimator`、直接用 `Classical.choose`
     取同一见证」的**相似陈述**（前几轮探针实测可编译），但那**换了一个函数**，
     不是在陈述 `observe`，**故本文件不收录**——按纪律，不用换对象来冒充「去掉前件」。

  5. `FateV2.Model.exists_rule_of_thetaIndependent` / `degenerate_iff_thetaIndependent`
     （`[Nonempty Θ.Carrier]`）—— **不可去**，且**模块已自行如实记录**
     （`Fate/Frame.lean:847` 原话：「若 `Θ` 为空，则『核不依赖 `θ`』是**空洞真**，
     此时不能无条件构造出 `Rule`」）。这是**正确的断言**。

  6. `SCMIdentifiability.Prediction` / `prediction_eq` 等（`[Nonempty Y]`）
     —— **不可去**（B 类）。`Prediction` 的定义是
     `EndToEnd.predFrom (paramScmWorldModel M) ...`，
     而 `paramScmWorldModel` 的 `state.cur` 需要一个具体 `Y` 值。
     **⚠ 与之相对**，同文件的 `scmThetaSubsingleton_pred_eq`（§2 已去）虽然
     陈述里也写了 `[Nonempty Y]`，但其**证明体一次都没用** ⟹ 真的可去。

  7. `FateV2.Modeling.sum_pos_univ`（`[Nonempty σ]`）—— **不可去**
     （上一批已记录，这里复核）：`σ` 空时 `∑ x, f x = 0`，且 `h` 空真，
     结论 `0 < 0` **为假** ⟹ 无可去形式。

  8. `FateV2.Predict.CondMulSeparable` / `FateV2.Predict.MarkovBridgeTheorem` 的 `[Nonempty]`
     —— 上一批已去；本轮**不重复**。

  **⟹ 结论**：本批实测的候选中，**10 条真的可去**
  （§1 四条 + §2 一条 + §3 一条 + §4 三条 + §4b 一条），
  其余 7 组**不可去**，分三类原因：
  (a) 空型时结论**不**空真（`sum_pos_univ`）；
  (b) **定义需要**具体取值/全函数（`optimalPolicy`、`bdWorldModel`、`chooseEstimator`、
      `paramScmWorldModel`、`exists_rule_of_thetaIndependent`）；
  (c) **iff 的右边与类型无关**（上一批的 `isPoint_genRule_iff`）。

  **⚠ 更正记录**：原 §4 第 1 条把 `peel_lower` 列为不可去是**错的**（详见 §5 第 1 条）。
-/

end FateV2.Predict.NonemptyFree2
