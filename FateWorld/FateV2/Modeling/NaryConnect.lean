import FateWorld.FateV2.Modeling.NaryFinal
import FateWorld.FateV2.Modeling.NaryAlgebra
/-!
  # Modeling · NaryConnect

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryConnect.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryFinal, NaryAlgebra
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNConnect ⭐⭐⭐⭐ **N 元的代数层 ↔ 测度层连接**（**第 187 轮**）

  ## ⚠⚠ 问题（对抗性审核 J4，第 186 轮）

  > **「`CondIndepN.lean` 中 `GenN` 出现 **0 次**」** ——
  > 即**代数层（`CondIndepN`）与测度层（`weightedCountN`）**没有任何连接**。

  ## ⭐ 本轮建立的连接

  `coordSet i S`：「第 `i` 个坐标落在 `S` 中」，
  以及它的**可测性判据**（需显式前提 `proj_i` 可测）。

  ## ⭐⭐ 关键事实（本轮查明）

  **项目里的 `MeasurableSpace ((∀ i, fam i) × γ)` 是**独立声明的实例****
  —— 它**不等于** `Prod.instMeasurableSpace`
  ⟹ **`proj_i : (∀ i, fam i) × γ → fam i` 的可测性需要**显式前提****
  （二元情形它是 `FinCondIndepMeasure.measurable_projX`）。

  ## ⚠ 语义前提

  **必须有 `hp : ∀ w, 0 ≤ p w`** ——
  否则 `weightedCountN` 的 `ofReal` **截断负值**（第 177 轮 `GuardNecessary` 的反例）。
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section Def

variable {ι : Type*} {fam : ι → Type*} {γ : Type*}

/-- ⭐ **第 `i` 个坐标落在 `S` 中**的集合。 -/
def coordSet (i : ι) (S : Set (fam i)) : Set ((∀ j, fam j) × γ) := {w | w.1 i ∈ S}

end Def

section Measurable

variable {ι : Type*} {fam : ι → Type*} {γ : Type*}
variable [MeasurableSpace ((∀ j, fam j) × γ)]

/-- ⭐⭐ **`coordSet i S` 的可测性**（**显式前提**：`proj_i` 可测）。

**⚠ 因为项目的乘积 σ-代数是**独立声明的实例**，
`proj_i` 的可测性**不能自动得到**（这是与二元的 `measurable_projX` 的差别）。 -/
theorem coordSet_measurableSet
    (i : ι) (S : Set (fam i)) [MeasurableSpace (fam i)]
    (hS : MeasurableSet S)
    (hproj : Measurable (fun w : (∀ j, fam j) × γ => w.1 i)) :
    MeasurableSet (coordSet i S : Set ((∀ j, fam j) × γ)) :=
  hproj hS

end Measurable


section Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
  [∀ i, MeasurableSpace (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]
variable [StandardBorelSpace ((∀ j, fam j) × γ)]

/-- ⭐ **把 `NJoint`（柯里化）转成 `(Pair) → ℝ`**（与 `weightedCountN` 的输入一致）。 -/
def uncurryN (p : FateV2.Modeling.GenC3.NJoint (ι := ι) fam γ) :
    ((∀ j, fam j) × γ) → ℝ := fun w => p w.1 w.2

/-- ⚠⚠ **N 元桥的**真正缺口**（**显式登记**）。

**目标**（尚未证明）：
$$\kappa_a(t_1 \cap t_2) \cdot M = \kappa_a(t_1) \cdot \kappa_a(t_2)$$
其中 $t_i = \mathrm{coordSet}\ i\ S_i$，$M = \mu.\mathrm{real}(\mathrm{fiberN}\ a_2)$。

**⚠ 为什么没做**（对抗性审核 J4 指出，第 186 轮）：
`CondIndepN`（**代数层**，纯 `Finset`）与 `weightedCountN`（**测度层**）
之间**没有任何连接引理**。要把两者连起来需要：
1. `condIndepN_sum_factorize`（代数）—— ✅ 已有（`NaryAlgebra`）
2. `bridgeKernelValue_mul_fiberN`（测度）—— ✅ 已有（`NaryFinal`）
3. ⚠ **`weightedCountN_apply` 在 `coordSet` 上的显式求值** —— **缺**
4. ⚠ **把 1 与 2 在 `S_i` 上对齐** —— **缺**

**⭐ 本 `def` 只是把这个缺口**结构化地记下来**，
使它出现在 `#check` 的输出里，防止被误认为已完成。 -/
def naryBridgeTarget : Prop :=
  ∀ (_p : FateV2.Modeling.GenC3.NJoint (ι := ι) fam γ), True

end Bridge
