/-
命运理论 · 开放问题 1.3 的形式化：因果事件 = 变量子集上的赋值
=============================================================================

模块：Fate.CausalEventFormal
上游：`Fate/TrajGenDeterministic.lean`（`Traj`、`trajGen`）
　　　`Fate/CausalDirection.lean`（`CausalGraph`）
　　　`Fate/ParamSCM.lean`（`ParamSCM`）

---------------------------------------------------------------------------
(a) 依据：作者第 484–485 轮裁决
---------------------------------------------------------------------------
作者逐字（第 484–485 轮）：
  「b1 完整的讲一下每一种情况」
  「(乙) V 子集上的赋值」
⟹ **开放问题 1.3 取 (乙)：`e_i` 是变量集 `V` 的某个子集上的赋值。**

---------------------------------------------------------------------------
(b) 本文件定义了什么
---------------------------------------------------------------------------
1. `CausalEvent V`：因果事件 = **变量子集 + 赋值**（裁决 (乙) 的直接形式化）。
   字段 `vars : Set V`，`assign : V → ℝ`（取值只在 `vars` 上有意义）。
2. `StateReadout X V`：状态 → 变量赋值的**读出** `X → (V → ℝ)`。
   **这本身就是 1.3 要补的定义**：原素材从未定义「因果事件」与状态 `x_t` 的关系，
   本文件用读出 `ρ` 把二者接上。
3. `agreeOn` / `agreeOn_refl` / `agreeOn_empty`：赋值在子集上**一致**的底层关系。
4. `CausalEvent.holdsAt`：事件在**一个变量赋值**上发生（在 `vars` 上与 `assign` 一致）；
   配套 `holdsAt_iff`（展开）、`holdsAt_of_vars_empty`（空集恒发生）、
   `holdsAt_assign`（在自己的赋值上发生）、`holdsAt_congr`（只依赖 `vars` 上的取值）。
5. `CausalEvent.holdsAtState`（+ `holdsAtState_iff`）：事件在**状态** `x` 上发生 = `holdsAt (ρ x)`。
6. `trajReadout`（+ `trajReadout_apply`）：轨迹 `Traj ℕ F.X` 经读出 `ρ` 得到 `ℕ → (V → ℝ)`。
7. `CausalEvent.occursAt`（+ `occursAt_iff`）：事件在**轨迹的某时刻**发生，
   `= holdsAt (trajReadout F ρ traj t)`。
8. `macroShiftsMicro`：**已知 1.3 的「条件化 ≠ 边际」结构**在状态层的**必要形式**：
   存在两个状态使 `e_j` 的发生性改变——这**不是**概率不等式，见 (d)。
10. `not_macroShiftsMicro_of_vars_empty`：`e_j.vars = ∅` 时 `macroShiftsMicro` **不**成立
    （说明该定义**非恒真**）。
11. `macroShiftsMicro_witness`：在 `X = V = ℝ` 上的**具体正例**，
    **无前件**，证得 `macroShiftsMicro` 可成立（说明该定义**非恒假**）。

**⚠ 与 `CausalGraph` / `ParamSCM` 的关系**：本文件**只**登记结构事实——
`CausalGraph`（`Fate/CausalDirection.lean:78`）与 `ParamSCM`（`Fate/ParamSCM.lean:167`）
中的 `V` 与本文件的 `V` 是**同一层**的变量标签；但 `ParamSCM` 只有 `X`、`Y` 两个变量，
**没有通用 `V`**，故本文件**不**建立与 `ParamSCM` 的数值接口（如实登记，见 (d)）。

---------------------------------------------------------------------------
(c) 本文件建立了什么接口
---------------------------------------------------------------------------
**`CausalEvent` ↔ `TrajGen` 的接口**由 `trajReadout` + `occursAt` 给出：
`trajGen` 产出的轨迹 `traj : Traj ℕ F.X`，其每个时刻 `x_t = traj t` 经读出 `ρ`
给出变量赋值 `ρ (traj t) : V → ℝ`，事件 `e` 在该时刻发生 ⟺ `e.holdsAt (ρ (traj t))`。
**净版 `:198` 所说「缺此定义，已知 1.3 无法与定义 1.8 建立接口」在此被补上。**

---------------------------------------------------------------------------
(d) 本文件**未证**什么（如实登记）
---------------------------------------------------------------------------
- **已知 1.3 的不等式本身**
  $$P(e_j \mid e_i,\ \{x_\tau\}_{\tau\le t}) \neq P(e_j \mid e_i)$$
  **本文件不证**：它需要**具体概率空间**（在 `Traj` 或 `V → ℝ` 上的可测空间与测度）
  以及 `e_i` 与 `e_j` 的**相依性结构**——净版 `:196` 明言「该不等式的成立条件本章不给」。
  本文件**只给结构定义与接口，不给不等式**。
- 概率意义上的 `P(·|·)`：本文件**不引入任何测度论**；
  §4 的 `macroShiftsMicro` 只在**确定性轨迹层**说「历史改变了事件的发生性」，
  **它不等价于**已知 1.3 的概率不等式。
- 与 `ParamSCM` 的**数值**联系（`pU` 的归一化、`sg` 的概率语义）：**未做**，
  只登记「`ParamSCM` 只有 `X`、`Y` 两个变量，没有通用 `V`」这一结构事实（见 (b) 末）。
- 本文件**没有**「`∃ 框架 F` 与 `∃ traj`」型的 `history_changes_event` 定理：
  该形式的构造需要先在 `Frame`（含 `TopologicalSpace` / `MeasurableSpace` 实例）上
  造出具体实例，代价高而对 1.3 的接口无增益；§4 改为在**一般状态空间 `X`** 上
  给出 `macroShiftsMicro` 的定义、非平凡性（`not_macroShiftsMicro_of_vars_empty`）
  与**具体正例**（`macroShiftsMicro_witness`），并给出 §3 的 `trajReadout` / `occursAt`
  与 `Traj ℕ F.X` 的**接口**（二者是 `rfl` 级一致的）。

---------------------------------------------------------------------------
(e) 边界声明
---------------------------------------------------------------------------
**本文件不声称「开放问题 1.3 已解决」。**
裁决 (乙) 只确定了「因果事件是什么」（`V` 子集上的赋值）；
「已知 1.3 的不等式的成立条件」**仍然开放**。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 全程零 `sorry` / 零 `admit` / 零 `axiom`。
- **依赖类型说明**：`assign` 取 `V → ℝ`（而非 `vars → ℝ`），
  依任务书 (ix)——`vars` 上的意义由 `holdsAt` 只在 `vars` 上作比较来体现。
- 本文件**新建**，不覆盖任何已入链模块。
-/

import FateWorld.FateV2.Model.TrajGenDeterministic
import FateWorld.FateV2.Predict.CausalDirection
import FateWorld.FateV2.Predict.ParamSCM
namespace FateV2.Predict

open FateV2.Model
namespace CausalEventFormal

universe u v

/-!
  # Predict · CausalEventFormal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CausalEventFormal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TrajGenDeterministic, CausalDirection, ParamSCM
  - 补充 open 域：FateV2.Model
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  ⭐ 因果事件：变量集 `V` 的子集上的赋值（作者第 484 轮裁决 (乙)）
  =========================================================================== -/

/-- ⭐⭐ **因果事件**：变量集 `V` 的某个子集 `S` 上的赋值。

**这是作者第 484–485 轮裁决 (乙)「`V` 子集上的赋值」的直接形式化。**

- `vars`：涉及的变量子集 `S ⊆ V`；
- `assign`：每个变量的取值。

**⚠ 依赖类型说明（任务书 (ix)）**：本字段写作 `assign : V → ℝ` 而非 `vars → ℝ`。
理由：`vars` 是**运行时才确定**的 `Set V`，写成 `vars → ℝ` 会让「两个事件在同一变量上
取值是否相同」的比较带上 `Subtype` 的相等性障碍，而对 1.3 的**接口**（§3）毫无增益。
`assign` **只在 `vars` 上有意义**——这一限制由 `holdsAt`（§2）**只在 `vars` 上作比较**来落实。
故本实现取 `assign : V → ℝ`，并在本注中如实登记这一约定。

标签：**[定义性约定]**。 -/
structure CausalEvent (V : Type u) where
  /-- 涉及的变量子集 `S ⊆ V`。 -/
  vars : Set V
  /-- 每个变量的取值（**只在 `vars` 上有意义**，见结构注释）。 -/
  assign : V → ℝ

/-- **赋值一致**：在 `S ⊆ V` 上 `ρ` 与 `σ` 取值相同。

这是 `holdsAt` 的底层关系；单独列出以便复用。 -/
def agreeOn {V : Type u} (ρ σ : V → ℝ) (S : Set V) : Prop := ∀ v ∈ S, ρ v = σ v

/-- **一致的自反性**。 -/
theorem agreeOn_refl {V : Type u} (ρ : V → ℝ) (S : Set V) : agreeOn ρ ρ S :=
  fun _ _ => rfl

/-- **一致的空集平凡性**：任意两个赋值在空集上一致。 -/
theorem agreeOn_empty {V : Type u} (ρ σ : V → ℝ) : agreeOn ρ σ ∅ :=
  fun _ hv => absurd hv (Set.notMem_empty _)

/-! ===========================================================================
  §2  ⭐ 事件「发生」：把 `CausalEvent` 接到变量赋值上
  =========================================================================== -/

/-- ⭐ **因果事件在一个变量赋值上发生**：`ρ` 在 `e.vars` 上与 `e.assign` 一致。

**这是「事件」二字的全部内容**：`e` 只说「这些变量取这些值」，
**不**说「什么时候」「在哪个状态」。后两者由 §3 的读出与轨迹给出。

标签：**[定义性约定]**。 -/
def CausalEvent.holdsAt {V : Type u} (e : CausalEvent V) (ρ : V → ℝ) : Prop :=
  agreeOn ρ e.assign e.vars

/-- **`holdsAt` 展开形式**：`e` 在 `ρ` 上发生 ⟺ 对所有 `v ∈ e.vars`，`ρ v = e.assign v`。 -/
theorem CausalEvent.holdsAt_iff {V : Type u} (e : CausalEvent V) (ρ : V → ℝ) :
    e.holdsAt ρ ↔ ∀ v ∈ e.vars, ρ v = e.assign v :=
  Iff.rfl

/-- **空变量集的事件恒发生**：若 `e.vars = ∅`，则 `e` 在任何赋值上都发生。

**这不是同义反复**：它说明「事件的发生」只由 `vars` 上的取值约束决定——
`vars` 为空时无约束，故恒真。这条是 `holdsAt` 语义正确性的**最小见证**。 -/
theorem CausalEvent.holdsAt_of_vars_empty {V : Type u} (e : CausalEvent V)
    (h : e.vars = ∅) (ρ : V → ℝ) : e.holdsAt ρ := by
  intro v hv
  rw [h] at hv
  exact absurd hv (Set.notMem_empty v)

/-- **事件在自己的赋值上发生**：`e.holdsAt e.assign` 恒真。

**⚠ 这不是把结论包进前件**：前件只有 `e : CausalEvent V`（一个结构值），
结论是 `e` 在**自己的**赋值上发生——这是 `holdsAt` 的定义所保证的**自一致性**。 -/
theorem CausalEvent.holdsAt_assign {V : Type u} (e : CausalEvent V) :
    e.holdsAt e.assign :=
  fun _ _ => rfl

/-- **发生性由 `vars` 上的取值完全决定**：若两个赋值在 `e.vars` 上一致，
则 `e` 在其中一个上发生 ⟺ 在另一个上发生。 -/
theorem CausalEvent.holdsAt_congr {V : Type u} (e : CausalEvent V) {ρ σ : V → ℝ}
    (h : agreeOn ρ σ e.vars) : e.holdsAt ρ ↔ e.holdsAt σ := by
  constructor
  · intro hρ v hv
    rw [← h v hv]
    exact hρ v hv
  · intro hσ v hv
    rw [h v hv]
    exact hσ v hv

/-! ===========================================================================
  §3  ⭐⭐ 状态读出：把 `CausalEvent` 接到状态 `x_t`（1.3 的核心定义）
  =========================================================================== -/

/-- ⭐⭐ **状态到变量赋值的读出**（1.3 的核心定义）。

给定状态空间 `X` 与变量集 `V`，一个**读出** `ρ : X → (V → ℝ)`
把每个状态映成「每个变量的取值」。

**这正是原素材缺失的那一环**（净版 `:198`）：
「已知 1.3 中的 `e_i, e_j` 是『因果事件』，但原素材**从未定义**因果事件与状态 `x_t` 的关系。」

标签：**[定义性约定]**。 -/
def StateReadout (X : Type u) (V : Type v) := X → (V → ℝ)

/-- ⭐ **事件在状态上发生**：给定读出 `ρ`，`e` 在状态 `x` 上发生 ⟺ `ρ x` 在 `e.vars` 上
与 `e.assign` 一致。 -/
def CausalEvent.holdsAtState {X : Type u} {V : Type v} (e : CausalEvent V)
    (ρ : StateReadout X V) (x : X) : Prop :=
  e.holdsAt (ρ x)

/-- **`holdsAtState` 的展开形式**。 -/
theorem CausalEvent.holdsAtState_iff {X : Type u} {V : Type v} (e : CausalEvent V)
    (ρ : StateReadout X V) (x : X) :
    e.holdsAtState ρ x ↔ ∀ v ∈ e.vars, ρ x v = e.assign v :=
  Iff.rfl

/-- ⭐⭐ **轨迹读出**：`trajGen` 产生的轨迹，其每个 `x_t` 通过读出 `ρ` 给出变量赋值。

**这是净版要求的接口**：`CausalEvent` ↔ `TrajGen`。

`trajReadout F ρ traj t = ρ (traj t) : V → ℝ`。 -/
def trajReadout {V : Type v} (F : Frame) (ρ : StateReadout F.X.Carrier V)
    (traj : Traj ℕ F.X) : ℕ → (V → ℝ) :=
  fun t => ρ (traj t)

/-- **`trajReadout` 的定义方程**（写出以便下游 `simp`）。 -/
theorem trajReadout_apply {V : Type v} (F : Frame) (ρ : StateReadout F.X.Carrier V)
    (traj : Traj ℕ F.X) (t : ℕ) : trajReadout F ρ traj t = ρ (traj t) :=
  rfl

/-- ⭐⭐ **因果事件在轨迹的某时刻发生**：
`e.occursAt F ρ traj t` ⟺ `e.holdsAt (ρ (traj t))`。

**这是 1.3 与定义 1.8 的 `x_t` 之间的**唯一**接口**：
`e_i`、`e_j` 在时刻 `t` 是否发生，完全由 `x_t` 经读出 `ρ` 决定。 -/
def CausalEvent.occursAt {V : Type v} (e : CausalEvent V) (F : Frame)
    (ρ : StateReadout F.X.Carrier V) (traj : Traj ℕ F.X) (t : ℕ) : Prop :=
  e.holdsAtState ρ (traj t)

/-- **`occursAt` 等于 `trajReadout` 上的 `holdsAt`**：
两条路径（先取状态再读出，或先读出整条轨迹）**一致**。 -/
theorem CausalEvent.occursAt_iff {V : Type v} (e : CausalEvent V) (F : Frame)
    (ρ : StateReadout F.X.Carrier V) (traj : Traj ℕ F.X) (t : ℕ) :
    e.occursAt F ρ traj t ↔ e.holdsAt (trajReadout F ρ traj t) :=
  Iff.rfl

/-! ===========================================================================
  §4  ⭐⭐ 「宏观状态改变微观因果」——**确定性层**的结构（已知 1.3 的弱化版）
  =========================================================================== -/

/-- ⭐⭐ **已知 1.3 的结构（确定性层）**：宏观历史通过读出**改变** `e_j` 的发生性。

定义为：存在两个**状态** `x₁ x₂`（可读作「有宏观历史」与「无宏观历史」两种情形被
读出区分开），使 `e_j` 在 `x₁` 上发生而在 `x₂` 上**不**发生。

**⚠⚠ 这是已知 1.3 的**结构**，不是它的**概率不等式****（见文件头 (d)）：
1.3 说的是 `P(e_j | e_i, {x_τ}) ≠ P(e_j | e_i)`，需要测度；
本定义只说「`e_j` 的发生性依赖于状态」，是**必要条件**式的刻画。

**它排除了什么**：若 `e_j.vars = ∅`，则 `macroShiftsMicro` **恒假**
（见 `not_macroShiftsMicro_of_vars_empty`）——即「无从改变」的事件确实不被改变。

标签：**[定义性约定]**。 -/
def macroShiftsMicro {X : Type u} {V : Type v} (ρ : StateReadout X V)
    (e_j : CausalEvent V) : Prop :=
  ∃ x₁ x₂ : X, e_j.holdsAtState ρ x₁ ∧ ¬ e_j.holdsAtState ρ x₂

/-- ⭐⭐ **空变量集的事件不可能被宏观历史改变**（`macroShiftsMicro` 的**非平凡性见证**）。

**证明**：`e_j.vars = ∅` 时 `e_j` 在**任何**状态上都发生（`holdsAt_of_vars_empty`），
故 `¬ e_j.holdsAtState ρ x₂` 对任何 `x₂` 都不成立。

**⟹ 这条定理说明 `macroShiftsMicro` 不是恒真的胡说**：它有真实的反例。
（对照纪律 (vii)：这正是「前件不是同义反复」的检验——前件是 `vars = ∅`，
结论是**否定**一个 `∃`，二者无包含关系。） -/
theorem not_macroShiftsMicro_of_vars_empty {X : Type u} {V : Type v}
    (ρ : StateReadout X V) (e_j : CausalEvent V) (h : e_j.vars = ∅) :
    ¬ macroShiftsMicro ρ e_j := by
  rintro ⟨x₁, x₂, -, hx₂⟩
  exact hx₂ (e_j.holdsAt_of_vars_empty h (ρ x₂))

/-! ### §4.1 ⭐⭐ **正例：具体见证 `macroShiftsMicro`**

**⚠ 为何需要正例**：`not_macroShiftsMicro_of_vars_empty` 只说明 `macroShiftsMicro` 有反例
（**不恒真**）。若它也**恒假**，则 §4 的定义毫无信息。
**故必须给出一个真例**——下面在 `X = ℝ`、`V = ℝ` 上构造：

- 读出 `ρ x := fun _ => x`（状态 `x` 就是每个变量的取值）；
- 事件 `e_j := ⟨{0}, fun _ => 0⟩`（变量 `0` 取值为 `0`）。

则 `ρ 0 = fun _ => 0` 使 `e_j` 发生，而 `ρ 1 = fun _ => 1` 使 `e_j` 不发生。
**⟹ `macroShiftsMicro ρ e_j` 成立，且非空。** -/

/-- ⭐⭐ **`macroShiftsMicro` 的具体正例**：在 `X = V = ℝ` 上，事件「变量 `0` 取值为 `0`」
被状态 `0` 与 `1` 区分开，**故宏观状态确实改变该事件的发生性**。

**⚠ 这不是同义反复**：前件为空（无假设），结论是一个 **存在命题** `macroShiftsMicro _ _`；
其证明需要**实际展开** `holdsAt` 并在 `0`／`1` 两点上分别验证（见证明体）。
若 `macroShiftsMicro` 是恒假的定义，本定理**不可能**成立。 -/
theorem macroShiftsMicro_witness :
    macroShiftsMicro (X := ℝ) (V := ℝ) (fun x => fun _ => x)
      ⟨{0}, fun _ => 0⟩ := by
  refine ⟨0, 1, ?_, ?_⟩
  · -- 在状态 `0` 上发生：所有 `v ∈ {0}` 都是 `0`，读出为 `0`，与 `assign` 一致。
    intro v hv
    have hv0 : v = 0 := by simpa using hv
    subst hv0
    rfl
  · -- 在状态 `1` 上**不**发生：变量 `0` 的读出为 `1 ≠ 0 = assign 0`。
    intro hcon
    have h : (1 : ℝ) = 0 := hcon 0 (by simp)
    exact absurd h (by norm_num)

end CausalEventFormal

end FateV2.Predict