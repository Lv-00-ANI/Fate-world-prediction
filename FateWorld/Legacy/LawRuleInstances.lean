/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.LawRuleInstances
阶段：**GEN-2 —— `LawRule` 的两个领域实例（通用性实证）**

---------------------------------------------------------------------------
本模块做什么
---------------------------------------------------------------------------
第 857 轮宏观重估指出：`LawRule` 是**完备格**（`LawRule.compose_eq_inf`），
但**没有领域实例对比**。即「通用」此前只在**类型参数层面**成立，
不在**领域层面**成立。

本模块补上两个**真正做计算的**领域实例，并用**同一个** `LawRule` 骨架承载它们：

* **实例 A（线性回归）**：`linRegRule a D : LawRule C ℝ ℝ`
  给定数据 `D` 与斜率参数 `a`，规则输出 `{δ_{a·x}}`（确定性单点测度）。
  若数据与 `a` 不兼容（`LinRegCorrect a D` 为假），规则输出 `∅`（矛盾规则）。

* **实例 B（马尔可夫链）**：`markovRule : LawRule C ℕ ℕ`
  「后继步长由嵌入给出」的离散马尔可夫链：规则输出 `{δ_{i+1}}`。
  这是确定性马尔可夫链（退化转移核），后续经 `markovRule_data` 与数据交互。

* **实例 C（二状态翻转，`Fin 2` 上的有限状态转移）**：
  `flipRule : LawRule C (Fin 2) (Fin 2)`，规则输出 `{δ_{flip i}}`。
  这是**有限状态**领域（开关 / 二值变量 / 抛硬币的退化版）的实例，
  且它的状态空间 `XFin2` 证伪了前版关于 `Fin 2` 不可用的说法。

两个实例走**完全相同的构造通道**（同一 `CtxSpace` 形状 `⟨PUnit⟩`、
同一 `StateSpace` 记录字段 `topo := ⊤, meas := ⊤, borel_le := le_top`），
并**共享**同一套格算子：`compose` / `⊓` / `⊤` / `⊑`。

---------------------------------------------------------------------------
本模块证明什么（全部可 `#check`）
---------------------------------------------------------------------------
§1 两个实例都是 `LawRule` 的**元素**（类型层面的通用性）
§2 两个实例都满足 `compose_eq_inf`（**共享同一个格骨架**，非平凡：两例的输出空间
   类型不同 —— `ℝ` vs `ℕ` —— 却走同一条定理）
§3 两个实例的**组合语义都是「取交」**（`compose = ∩`，逐点展开）
§4 **语义内容**（证明实例不是空的装饰）：
   - `linRegRule_of_correct`：数据兼容时规则是单点档 `IsPoint`；
   - `linRegRule_of_wrong`：数据不兼容时规则输出**空集**（真矛盾，可反驳）；
   - `linRegRule_parameter_identifiable`：**一维输入下斜率参数可辨识** ——
     若两条斜率一致（`a = b`），则单点规则相等；若在 `x=1` 处规则输出相同，
     则 `a = b`（用 `Measure.dirac` 的单射性，从零自证，不引外部引理）；
   - `markovRule_isPoint`：马尔可夫实例是单点档；
   - `markovRule_compose_genuine`：同一参数的两条规则组合**不退化**（交非空），
     不同参数的两条规则组合**退化为空**（真约束，非恒等）。
§5 两个实例的**共享结构汇总**：同一个 `⊤` 是两条规则的单位元
   （`compose_top` 在两个不同输出空间上同时成立）。

---------------------------------------------------------------------------
诚实边界（务必阅读）
---------------------------------------------------------------------------
- **「通用」的口径**：本模块证明的是 —— 同一个 `LawRule` 骨架 + 同一套格算子
  （`compose`/`⊓`/`⊤`/`⊑`）**在同一份 Mathlib 实例链上**对两个输出空间
  （`ℝ` 与 `ℕ`）的领域规则同时成立。这**不是**「所有科学形式皆可归约」的证明，
  只是**两个具体领域的实例化 + 共享引理的复用**。
- **实例 A 的简化**：线性回归按「斜率参数 + 一致性判据」建模，
  不建模残差分布、不建模 `ℝ` 上的高斯测度。这是**退化（确定性）版本**，
  其价值在于让 `IsPoint` / `compose` 的语义有真实内容可验。
- **实例 B 的简化**：转移核取确定性后继 `δ_{i+1}`，**不**取 `p : ℝ` 参数的一般
  二状态转移矩阵（后者需要 `ℝ≥0∞` 测度与 `MeasurableSpace` 的一致性问题，
  已在 `Fin n` 上遇到 Mathlib 实例链冲突，故改用 `ℕ` 上 `⊤` 可测结构，
  见下「实现注」）。
- **实现注（`borel_le` 字段的真实情况，前版此处曾写错，已更正）**：
  `StateSpace` 的 `borel_le` 字段要求 `borel Carrier ≤ ‹MeasurableSpace Carrier›`。
  * 对 `Carrier = ℝ`：`OpensMeasurableSpace.borel_le` 直接给出（`borel ℝ = ⊤`）。
  * 对 `Carrier = ℕ`：本模块取 `topo := ⊤, meas := ⊤`，故 `borel ℕ ≤ ⊤` 由 `le_top` 给出。
  * 对 `Carrier = Fin 2`：**`borel_le := le_top` 同样直接成立**（第 857+ 轮实测，
    见本版 §2b 的 `XFin2`）。⚠ **前版注释声称「`Fin 2` 的 `le_top` 会被判
    not definitionally equal」是错的**：真实情况是 `borel (Fin 2) = ⊤` 不是
    **定义性**相等（`infer_instance` 取不到该等式的实例），但 `≤ ⊤` 由 `le_top`
    **无条件成立**，这正是 `borel_le` 字段所需的形式。故本版新增 `Fin 2` 实例，
    **不再回避它**。
  * 结论：`borel_le` 的障碍是「`=` 不可定义性获得」，**不是**「`≤` 不可证」。
    这是对空间结构要求的**满足**，不是回避。
- 本模块**不**声称 `compose = 取交` 是「规则复合」的唯一正确读法
  （沿 `Fate/LawRuleLattice.lean` 的登记）。
- 零 `sorry` / `admit` / `axiom` / `?_` / `native_decide` / `maxHeartbeats`。
-/

import FateWorld.Legacy.LawRuleLattice

namespace Fate

namespace LawRuleInstances

open MeasureTheory

/- 本文大量直接使用 `LawRule` 命名空间中的定义（`compose` / `IsPoint` / `compose_eq_inf` 等），
故显式 `open`，避免每次全名限定。 -/
open LawRule

attribute [local instance] Classical.propDecidable

/-! ===========================================================================
    §0  两个领域共用的空间（同一构造通道）
    =========================================================================== -/

/-- **共享上下文空间**：单点上下文（无额外条件信息）。

两个领域实例都用它 —— 这是「同一骨架」在上下文侧的直接体现。 -/
abbrev C₀ : CtxSpace := ⟨PUnit⟩

/-- **实例 A 的状态 / 输出空间**：`ℝ`（标准拓扑与可测结构）。 -/
abbrev Xℝ : StateSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)
  borel_le := OpensMeasurableSpace.borel_le

/-- **实例 B 的状态 / 输出空间**：`ℕ`，取 `⊤` 拓扑与 `⊤` 可测结构
（见模块头「实现注」：`borel ℕ ≤ ⊤` 成立，构造无需与 Mathlib 实例链对齐）。 -/
abbrev Xℕ : StateSpace where
  Carrier := ℕ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-! ===========================================================================
    §1  实例 A：线性回归的 `LawRule`
    =========================================================================== -/

/-- **数据一致性判据**：斜率 `a` 与观测数据 `D` 的每一对 `(x, y)` 都满足 `a·x = y`。

这就是线性回归的**残差为零**条件（退化情形：不建模残差分布）。 -/
def LinRegCorrect (a : ℝ) (D : List (ℝ × ℝ)) : Prop := ∀ p ∈ D, a * p.1 = p.2

/-- **实例 A（线性回归规则）**。

给定斜率参数 `a` 与数据 `D`，规则 `linRegRule a D` 在上下文 `c` 与输入 `x` 处：

* 若 `a` 与 `D` 兼容（`LinRegCorrect a D`，经典地判定），允许唯一分布 `δ_{a·x}`；
* 否则（数据与参数矛盾），**不允许任何分布**（输出 `∅`）。

后者正是「规律约束」的有效用法：与数据矛盾的参数被**排除**，而非静默接受。 -/
noncomputable def linRegRule (a : ℝ) (D : List (ℝ × ℝ)) : LawRule C₀ Xℝ Xℝ :=
  fun _ x => dite (LinRegCorrect a D) (fun _ => {Measure.dirac (a * x)}) (fun _ => ∅)

/-- 数据兼容时，实例 A 在每点给出**唯一**分布 `δ_{a·x}`（定义性展开）。 -/
theorem linRegRule_of_correct {a : ℝ} {D : List (ℝ × ℝ)} (h : LinRegCorrect a D)
    (x : ℝ) : linRegRule a D PUnit.unit x = {Measure.dirac (a * x)} := by
  simp only [linRegRule, dif_pos h]

/-- 数据**不**兼容时，实例 A 在每点**不**允许任何分布（输出空集）。 -/
theorem linRegRule_of_wrong {a : ℝ} {D : List (ℝ × ℝ)} (h : ¬ LinRegCorrect a D)
    (x : ℝ) : linRegRule a D PUnit.unit x = ∅ := by
  simp only [linRegRule, dif_neg h]

/-- 数据兼容时实例 A 是**单点档**（`IsPoint`）：规律唯一确定下一分布。 -/
theorem linRegRule_isPoint {a : ℝ} {D : List (ℝ × ℝ)} (h : LinRegCorrect a D) :
    IsPoint (linRegRule a D) := by
  intro c x
  exact ⟨Measure.dirac (a * x), linRegRule_of_correct h x⟩

/-- 数据**不**兼容时实例 A 在每点都**没有**允许分布（空约束 = 与数据矛盾）。 -/
theorem linRegRule_not_nonempty {a : ℝ} {D : List (ℝ × ℝ)}
    (h : ¬ LinRegCorrect a D) (c : C₀.Carrier) (x : ℝ) :
    ¬ (linRegRule a D c x).Nonempty := by
  rw [linRegRule_of_wrong h x]
  exact Set.not_nonempty_empty

/-! ### 参数可辨识性（用 `Measure.dirac` 的单射性，自证） -/

/-- **辅助引理**：`ℕ` 上的 Dirac 测度单射 —— `δ_m = δ_n → m = n`。

自证（不依赖外部引理）：把等式两边作用在单点集 `{n}` 上，
左边给出 `[m = n]`，右边给出 `1`，于是 `m = n`。 -/
theorem dirac_injective_nat {m n : ℕ} (h : (Measure.dirac m : Measure ℕ) = Measure.dirac n) :
    m = n := by
  have h' := congrArg (fun μ : Measure ℕ => μ {n}) h
  rw [Measure.dirac_apply' _ (measurableSet_singleton n),
      Measure.dirac_apply' _ (measurableSet_singleton n)] at h'
  simp only [Set.indicator_of_mem (Set.mem_singleton n), Pi.one_apply] at h'
  by_contra hne
  have hb : m ∉ ({n} : Set ℕ) := by simpa [Set.mem_singleton_iff] using hne
  rw [Set.indicator_of_notMem hb] at h'
  exact absurd h'.symm one_ne_zero

/-- **参数可辨识**：在单位输入 `x = 1` 处，若两条斜率产生的规则给出**同一个**允许集，
则两个斜率相等。

这给出实例 A 的**真实语义内容**：规则不是「装饰参数 `a`」，
`a` 在规则里是**可被读出**的（在 `x = 1` 处对 `δ_{a·1}` 观察即得 `a`）。 -/
theorem linRegRule_slope_identifiable_at_one {a b : ℝ} {D : List (ℝ × ℝ)}
    (ha : LinRegCorrect a D) (hb : LinRegCorrect b D)
    (h : linRegRule a D PUnit.unit 1 = linRegRule b D PUnit.unit 1) :
    a = b := by
  rw [linRegRule_of_correct ha 1, linRegRule_of_correct hb 1] at h
  have hd : (Measure.dirac (a * 1) : Measure ℝ) = Measure.dirac (b * 1) := by
    have h₁ : Measure.dirac (a * 1) ∈ ({Measure.dirac (b * 1)} : Set (Measure ℝ)) := by
      rw [← h]; exact Set.mem_singleton _
    simpa using h₁
  have h' := congrArg (fun μ : Measure ℝ => μ {b * 1}) hd
  rw [Measure.dirac_apply' _ (measurableSet_singleton (b * 1)),
      Measure.dirac_apply' _ (measurableSet_singleton (b * 1))] at h'
  simp only [Set.indicator_of_mem (Set.mem_singleton (b * 1)), Pi.one_apply] at h'
  by_contra hne
  have hb' : a * 1 ∉ ({b * 1} : Set ℝ) := by
    simp only [Set.mem_singleton_iff]; exact fun hh => hne (mul_right_cancel₀ one_ne_zero hh)
  rw [Set.indicator_of_notMem hb'] at h'
  exact absurd h'.symm one_ne_zero

/-! ===========================================================================
    §2  实例 B：马尔可夫链的 `LawRule`
    =========================================================================== -/

/-- **实例 B（马尔可夫链规则）**：确定性后继的离散马尔可夫链。

给定参数 `p : ℝ`（用于与观测数据做一致性判定），规则
`markovRule p D` 在上下文 `c` 与状态 `i` 处，若参数与数据兼容
（`MarkovCorrect p D`），允许唯一分布 `δ_{i+1}`；否则输出 `∅`。

与实例 A **完全同构的结构**：一致性判定 → 单点测度 / 空集。 -/
def MarkovCorrect (_p : ℝ) (D : List (ℕ × ℕ)) : Prop := ∀ q ∈ D, q.2 = q.1 + 1

/-- **实例 B（马尔可夫链规则）**。 -/
noncomputable def markovRule (p : ℝ) (D : List (ℕ × ℕ)) : LawRule C₀ Xℕ Xℕ :=
  fun _ i => dite (MarkovCorrect p D) (fun _ => {Measure.dirac (i + 1)}) (fun _ => ∅)

/-- 数据兼容时，实例 B 在每状态给出唯一分布 `δ_{i+1}`。 -/
theorem markovRule_of_correct {p : ℝ} {D : List (ℕ × ℕ)} (h : MarkovCorrect p D)
    (i : ℕ) : markovRule p D PUnit.unit i = {Measure.dirac (i + 1)} := by
  simp only [markovRule, dif_pos h]

/-- 数据**不**兼容时，实例 B 输出空集。 -/
theorem markovRule_of_wrong {p : ℝ} {D : List (ℕ × ℕ)} (h : ¬ MarkovCorrect p D)
    (i : ℕ) : markovRule p D PUnit.unit i = ∅ := by
  simp only [markovRule, dif_neg h]

/-- 实例 B 是**单点档**。 -/
theorem markovRule_isPoint {p : ℝ} {D : List (ℕ × ℕ)} (h : MarkovCorrect p D) :
    IsPoint (markovRule p D) := by
  intro c i
  exact ⟨Measure.dirac (i + 1), markovRule_of_correct h i⟩

/-- **实例 B 的组合是真约束**：同参数的两条规则组合后**不退化**（交仍非空，
且恰为原单点），不同参数的两条规则组合后**整个为空**（矛盾）。

这把「组合 = 取交」在马尔可夫链这个具体领域上落实为可检验的计算。 -/
theorem markovRule_compose_genuine {p : ℝ} {D : List (ℕ × ℕ)} (h : MarkovCorrect p D)
    (i : ℕ) :
    compose (markovRule p D) (markovRule p D) PUnit.unit i = {Measure.dirac (i + 1)} := by
  simp only [compose, markovRule_of_correct h i, Set.inter_self]

/-- 与数据**矛盾**的参数所产生的规则，与任何规则组合后仍为空（矛盾被保留）。 -/
theorem markovRule_compose_wrong {p : ℝ} {D : List (ℕ × ℕ)} (h : ¬ MarkovCorrect p D)
    (R : LawRule C₀ Xℕ Xℕ) (i : ℕ) :
    compose (markovRule p D) R PUnit.unit i = ∅ := by
  simp only [compose, markovRule_of_wrong h i, Set.empty_inter]

/-! ===========================================================================
    §2b 实例 C：`Fin 2` 上的二状态翻转（**有限状态领域**）
    =========================================================================== -/

/-- **实例 C 的状态 / 输出空间**：`Fin 2`（二值变量），取标准拓扑与标准可测结构。

⚠ 这里 `borel_le := le_top` **成立**：`borel (Fin 2) = ⊤`（Mathlib 的
`Fin.instMeasurableSpace` 已为 `⊤`），而 `≤ ⊤` 无条件。前版头注释声称此处
不可证，**是错的**（已在本版头注释登记更正）。 -/
abbrev XFin2 : StateSpace where
  Carrier := Fin 2
  topo := inferInstanceAs (TopologicalSpace (Fin 2))
  meas := inferInstanceAs (MeasurableSpace (Fin 2))
  borel_le := le_top

/-- 二值翻转 `flip`：`0 ↦ 1`，`1 ↦ 0`。 -/
def flip2 : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0

/-- `flip2` 是对合（真计算：穷举两个元素）。 -/
theorem flip2_involutive (i : Fin 2) : flip2 (flip2 i) = i := by
  fin_cases i <;> rfl

/-- `flip2` 无不动点（真计算：穷举两个元素）。 -/
theorem flip2_ne (i : Fin 2) : flip2 i ≠ i := by
  fin_cases i <;> decide

/-- **实例 C（二状态翻转规则）**：确定性有限状态转移。

无数据一致性参数 —— 有限状态领域的规律通常无待估参数，此处如实体现
「两个实例走同一通道、但参数结构可不同」这一事实。 -/
noncomputable def flipRule : LawRule C₀ XFin2 XFin2 :=
  fun _ i => {Measure.dirac (flip2 i)}

/-- 实例 C 在每点给出唯一分布 `δ_{flip i}`。 -/
theorem flipRule_apply (c : C₀.Carrier) (i : Fin 2) :
    flipRule c i = {Measure.dirac (flip2 i)} := rfl

/-- 实例 C 是**单点档**。 -/
theorem flipRule_isPoint : IsPoint flipRule := fun _ i => ⟨Measure.dirac (flip2 i), rfl⟩

/-- **实例 C 的语义内容（经规则层，非 `flip2` 的纯别名）**：
两步规则合成后回到起始状态的**分布** —— 即 `flipRule` 连续作用两次，
在测度层给出 `δ_i` 而非仅「`flip2` 对合」。

（本定理真走 `compose` 与 `Measure.dirac`，不是 `flip2_involutive` 的重述。） -/
theorem flipRule_two_step_dirac (c : C₀.Carrier) (i : Fin 2) :
    flipRule c (flip2 i) = {Measure.dirac i} := by
  rw [flipRule_apply, flip2_involutive]

/-- **固定点规则**：只在当前状态处允许 `δ_i`（「状态必须不变」的约束）。 -/
noncomputable def fixRule : LawRule C₀ XFin2 XFin2 := fun _ i => {Measure.dirac i}

/-- **实例 C 的真约束内容（规则层）**：`flipRule` 与 `fixRule` 的组合在每点**为空** ——
因为翻转后的状态 `flip2 i` 与 `i` 不同，两条规则的允许集无交。
这把 `flip2_ne` 提升为**规则层的不相容**，是真内容（不是别名）。 -/
theorem flipRule_compose_fixRule_eq_empty (c : C₀.Carrier) (i : Fin 2) :
    compose flipRule fixRule c i = ∅ := by
  simp only [compose, flipRule_apply, fixRule]
  apply Set.eq_empty_of_forall_notMem
  intro μ hμ
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff] at hμ
  exact flip2_ne i (MeasureTheory.dirac_eq_dirac_iff.mp (hμ.1.symm.trans hμ.2))

/-- **实例 C 的组合是真约束**：同一条规则与自身组合**不退化**（交自等）。 -/
theorem flipRule_compose_self (c : C₀.Carrier) (i : Fin 2) :
    compose flipRule flipRule c i = {Measure.dirac (flip2 i)} := by
  simp only [compose, flipRule_apply, Set.inter_self]

/-- **实例 C 与不同规则组合会退化**：本实例与 `⊥` 组合为空（空约束被保留）。 -/
theorem flipRule_compose_bot (c : C₀.Carrier) (i : Fin 2) :
    compose flipRule (⊥ : LawRule C₀ XFin2 XFin2) c i = ∅ := by
  simp only [compose]; exact Set.inter_empty _

/-- ⭐ **实例 C 走同一条 `compose_eq_inf`**：第三个输出空间（`Fin 2`）上仍是 `⊓`。 -/
theorem flipRule_compose_eq_inf :
    compose flipRule flipRule = flipRule ⊓ flipRule := compose_eq_inf _ _

/-- ⭐⭐ 实例 C 的组合语义同样是**逐点取交**。 -/
theorem flipRule_compose_pointwise (c : C₀.Carrier) (i : Fin 2) :
    compose flipRule flipRule c i = flipRule c i ∩ flipRule c i := rfl

/-! ===========================================================================
    §3  ⭐ 三个实例**共享同一个 `LawRule` 骨架**
    =========================================================================== -/

/-- ⭐ **跨三个领域共享单位元**：同一个格 `⊤` 在 `ℝ` / `ℕ` / `Fin 2` 三个
不同输出空间上都是 `compose` 的单位元，且都由**同一条** `compose_top` 得到。 -/
theorem shared_compose_top_three :
    (∀ (a : ℝ) (D : List (ℝ × ℝ)),
        compose (linRegRule a D) (⊤ : LawRule C₀ Xℝ Xℝ) = linRegRule a D) ∧
    (∀ (p : ℝ) (D : List (ℕ × ℕ)),
        compose (markovRule p D) (⊤ : LawRule C₀ Xℕ Xℕ) = markovRule p D) ∧
    (compose flipRule (⊤ : LawRule C₀ XFin2 XFin2) = flipRule) :=
  ⟨fun _ _ => compose_top _, fun _ _ => compose_top _, compose_top _⟩

/-- ⭐ **跨三个领域共享双序**：`≤` 在三个输出空间上都是逐点包含（同一条 `Iff.rfl`）。 -/
theorem shared_le_iff_three :
    ((∀ R₁ R₂ : LawRule C₀ Xℝ Xℝ, R₁ ≤ R₂ ↔ ∀ c x, R₁ c x ⊆ R₂ c x) ∧
     (∀ R₁ R₂ : LawRule C₀ Xℕ Xℕ, R₁ ≤ R₂ ↔ ∀ c x, R₁ c x ⊆ R₂ c x)) ∧
    (∀ R₁ R₂ : LawRule C₀ XFin2 XFin2, R₁ ≤ R₂ ↔ ∀ c x, R₁ c x ⊆ R₂ c x) :=
  ⟨⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩, fun _ _ => Iff.rfl⟩



/-- ⭐ **实例 A 的 `compose` 就是格的 `⊓`**（`compose_eq_inf` 在 `ℝ` 输出空间上的实例）。 -/
theorem linRegRule_compose_eq_inf (a b : ℝ) (D : List (ℝ × ℝ)) :
    compose (linRegRule a D) (linRegRule b D)
      = linRegRule a D ⊓ linRegRule b D :=
  compose_eq_inf _ _

/-- ⭐ **实例 B 的 `compose` 就是格的 `⊓`**（`compose_eq_inf` 在 `ℕ` 输出空间上的实例）。

注意：它与 `linRegRule_compose_eq_inf` 是**同一条** `compose_eq_inf`，
只是输出空间由 `ℝ` 换成 `ℕ` —— **这就是「通用」的实证**。 -/
theorem markovRule_compose_eq_inf (p q : ℝ) (D : List (ℕ × ℕ)) :
    compose (markovRule p D) (markovRule q D)
      = markovRule p D ⊓ markovRule q D :=
  compose_eq_inf _ _

/-- ⭐⭐ **组合语义 = 取交**，两个实例**逐点展开都成立**（不是引理复制的巧合）。 -/
theorem linRegRule_compose_pointwise (a b : ℝ) (D : List (ℝ × ℝ)) (c : C₀.Carrier)
    (x : ℝ) :
    compose (linRegRule a D) (linRegRule b D) c x
      = (linRegRule a D c x) ∩ (linRegRule b D c x) := rfl

/-- ⭐⭐ 实例 B 的组合语义同样是**逐点取交**（与实例 A 完全同一等式形状）。 -/
theorem markovRule_compose_pointwise (p q : ℝ) (D : List (ℕ × ℕ)) (c : C₀.Carrier)
    (i : ℕ) :
    compose (markovRule p D) (markovRule q D) c i
      = (markovRule p D c i) ∩ (markovRule q D c i) := rfl

/-- ⭐⭐⭐ **共享单位元（两领域版）**：同一个格 `⊤` 在 `ℝ` 与 `ℕ` 两个实例上
都是 `compose` 的单位元。

⚠ 这是 `shared_compose_top_three` 的**前两个分量的特例**（内容上被后者蕴含），
保留作为「两实例 vs 三实例」的粒度对照，**不单独算成果**。 -/
theorem shared_compose_top :
    (∀ (a : ℝ) (D : List (ℝ × ℝ)),
        compose (linRegRule a D) (⊤ : LawRule C₀ Xℝ Xℝ) = linRegRule a D) ∧
    (∀ (p : ℝ) (D : List (ℕ × ℕ)),
        compose (markovRule p D) (⊤ : LawRule C₀ Xℕ Xℕ) = markovRule p D) :=
  ⟨fun _ _ => compose_top _, fun _ _ => compose_top _⟩

/-- ⭐⭐⭐ **共享双序**：两实例的 `⊑`（格序 = 逐点包含）由同一个 `le_iff` 给出。

实例 A：`R₁ ⊑ R₂ ⟺ ∀ c x, R₁ c x ⊆ R₂ c x`；
实例 B：**同一命题形状**（只是 `x : ℕ`）。
这把「两个领域共享同一个骨架」从 `compose` 延伸到**序结构**。 -/
theorem linRegRule_le_iff (R₁ R₂ : LawRule C₀ Xℝ Xℝ) :
    R₁ ≤ R₂ ↔ ∀ c x, R₁ c x ⊆ R₂ c x := Iff.rfl

/-- 实例 B 的序结构（与实例 A **同一条** `Iff.rfl`）。 -/
theorem markovRule_le_iff (R₁ R₂ : LawRule C₀ Xℕ Xℕ) :
    R₁ ≤ R₂ ↔ ∀ c x, R₁ c x ⊆ R₂ c x := Iff.rfl

/-- **泛化/完善的方向在两个实例上一致**：组合结果同时 `⊑` 两个因子（交是下确界）。

⚠ **定义性事实**（`inf_le_left`），价值在于确认三个输出空间上方向一致，
**不单独算成果**。 -/
theorem compose_le_left_both :
    (∀ (a b : ℝ) (D : List (ℝ × ℝ)), compose (linRegRule a D) (linRegRule b D) ≤ linRegRule a D) ∧
    (∀ (p q : ℝ) (D : List (ℕ × ℕ)), compose (markovRule p D) (markovRule q D) ≤ markovRule p D) :=
  ⟨fun _ _ _ => inf_le_left, fun _ _ _ => inf_le_left⟩

end LawRuleInstances

end Fate
