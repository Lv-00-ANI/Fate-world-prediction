import FateWorld.FateV2.Model.Pairing
import FateWorld.FateV2.Rules.AlphaFCAConstruction
/-!
  # Predict · PairingAlphaBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PairingAlphaBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Pairing, AlphaFCAConstruction
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §P3-①  配对层 → FCA 数据的桥（**对象集紧锁版**）

  ## 与 `Fate/PairingToAlphaData.lean` 的关系（必读）

  `Fate/PairingToAlphaData.lean` 已给出一个 `pairingToAlphaData`，
  但它的签名里有**未被使用的参数** `P : Pairing ι` 与 `γ : ι → X.Carrier`
  （编译期 `linter.unusedVariables` 直接告警），定义体是 `obs := fun t => attr t.1`。

  **⟹ 那个构造与配对无关**：`P`、`γ` 进不去定义体，
  所以它并未把 `Pairing.transitions P γ` 装进 `AlphaData` 的对象域。
  它的对象域是**全体** `Transition X`，与「哪些索引对算一次转移」无关。

  本文件**不改**那个文件（纪律 2），而是另给一个**对象集恰为 `transitions P γ`**
  的构造：`E.Carrier := { t // t ∈ P.transitions γ }`。
  这才使 `P` 与 `γ` **真正进入** `AlphaData` 的对象域，从而「配对层 → FCA 数据」
  在**类型层面**成为真桥，而不是空挂参数。

  ## 完整定义（实测原文）

  ```
  -- Fate/AlphaFCAConstruction.lean:95
  structure AlphaData (E : InstSpace.{u}) (M : Type u) where
    obs : E.Carrier → Set M

  -- Fate/Frame.lean:568
  structure InstSpace where
    Carrier : Type*
  ```

  ⟹ 门槛极低：只需一个对象类型 + `obs`。不存在 hidden 假设。

  ## 本文件的定理表

  | 定理 | 内容 |
  |---|---|
  | `transInst_Carrier` | 实例集载体 = subtype over `transitions` |
  | `toAlphaData` | ⭐⭐⭐⭐ 配对 + 轨迹 → `AlphaData`（对象集 = 转移对集） |
  | `toAlphaData_obs` | 逐点展开（`Iff.rfl`） |
  | `toAlphaData_obj_witness` | 每个对象都有 `P.rel` 见证（**由 `transInst` 定义保证**） |
  | `toAlphaData_obj_of_rel` | 每个 `P.rel` 索引对都给出一个对象（构造级，非展开） |
  | `toAlphaData_polarDown` | $B'$ 在本桥下的计算式 |
  | `toAlphaData_polarUp` | $A'$ 在本桥下的计算式 |
  | `transitions_grouped_subset_adjacent` | 策略 B ⊆ 策略 A |
  | `transitions_adjacent_subset_direct` | 策略 A ⊆ 策略 B' |
  | `transitions_grouped_subset_direct` | 三策略链 |
  | `transitions_direct` | B' 无损还原关系 |
  | `transitions_mono` | 转移对集的单调性 |
  | `transRule_of_adjacent` | 紧邻条件 ⟹ 转移规则 |
  | `transRule_of_grouped` | 同组紧邻 ⟹ 转移规则 |
  | `transRule_restrict_to_adjacent` | 宽策略规则 ⟹ 窄策略规则 |

  ## 诚实边界

  **删去的定理**：原计划的「定理 3：由 `TransRule` 反推 `Adjacent`」
  **未实现，因为它在现有定义下为假/无意义**：
  `TransRule A B S` 对 `S : Set (Transition X)` 逐点陈述，
  `S` 是无结构的二元组集合，**不含任何索引/先后信息**，
  故从 `TransRule` 推不出关于 `lt` 或 `Adjacent` 的任何结论。
  本文件代之以**可证的正向命题** `transRule_of_adjacent`（紧邻 ⟹ 规则）。

  **不声称**：本文件只接通 `Pairing → AlphaData` 这一段。
  `AlphaData → RichLaw` 仍需 `PatStruct`、`interp`、`attr` 等参数
  （见 `Fate/AlphaDataToLawRule.lean` 的审计 §(b)），不在本文件射程内。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
open FateV2.Rules
namespace PairingAlphaBridge

open Set

universe v

variable {ι : Type u} {X : StateSpace}

/-! ===========================================================================
  §1  ⭐ 核心：对象集恰为转移对集的 `AlphaData`
  =========================================================================== -/

/-- **转移对集作为实例空间**：`E.Carrier := { t : Transition X // t ∈ P.transitions γ }`。

**⟹ 与 `PairingToAlphaData.transInstSpace`（载体 = 全体 `Transition X`）不同，
这里 `P` 与 `γ` 进入了载体类型本身，故不可被忽略。** -/
def transInst (P : Pairing.Pairing ι) (γ : ι → X.Carrier) : InstSpace.{u} :=
  ⟨{ t : Pairing.Transition X // t ∈ Pairing.transitions P γ }⟩

@[simp] theorem transInst_Carrier (P : Pairing.Pairing ι) (γ : ι → X.Carrier) :
    (transInst P γ).Carrier
      = { t : Pairing.Transition X // t ∈ Pairing.transitions P γ } := rfl

/-- ⭐⭐⭐⭐ **【配对层的转移对集，就是 FCA 的对象集】**

给定配对 `P`、轨迹 `γ`、属性侧 `M` 与属性抽取 `attrₚ`，
构造 `AlphaData`：

* 对象集 $G_{\mathrm{FCA}}$ = `{ t // t ∈ P.transitions γ }` —— **恰为转移对集**；
* 观测 $\mathrm{obs}(t) = \mathrm{attr}_\flat(t.1)$ —— **前态属性**。

**⟹ `P` 与 `γ` 通过 `transInst` 进入对象域，故此构造不是空挂参数。** -/
def toAlphaData (P : Pairing.Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attrₚ : X.Carrier → Set M) : AlphaData (transInst P γ) M :=
  ⟨fun t => attrₚ t.1.1⟩

@[simp] theorem toAlphaData_obs (P : Pairing.Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attrₚ : X.Carrier → Set M)
    (t : (transInst P γ).Carrier) (m : M) :
    m ∈ (toAlphaData P γ M attrₚ).obs t ↔ m ∈ attrₚ t.1.1 :=
  Iff.rfl

/-- **转移对集对 `rel` 单调**（三策略可比较的底层机制）。 -/
theorem transitions_mono {P Q : Pairing.Pairing ι}
    (h : ∀ n m, P.rel n m → Q.rel n m) (γ : ι → X.Carrier) :
    Pairing.transitions P γ ⊆ Pairing.transitions Q γ := by
  rintro ⟨a, b⟩ ⟨n, m, hr, rfl, rfl⟩
  exact ⟨n, m, h n m hr, rfl, rfl⟩

/-! ### §1.1 对象来源的核验（供读者核对，**非独立数学内容**）

⚠ 自我审计：`toAlphaData_obj_witness` 的证明是 `t.2` 按 `Iff.rfl` 展开，
属**定义展开级**。本文件其余定理**不**以它为假设（无循环论证）。
真正有独立内容是 `toAlphaData`（类型构造）与 §2、§3。 -/

/-- **（定义展开级）** 每个对象都有 `P.rel` 见证。 -/
theorem toAlphaData_obj_witness (P : Pairing.Pairing ι) (γ : ι → X.Carrier)
    (t : (transInst P γ).Carrier) :
    ∃ n m : ι, P.rel n m ∧ γ n = t.1.1 ∧ γ m = t.1.2 :=
  t.2

/-- **（构造级）** 任意 `P.rel n m` 都给出 `toAlphaData` 的一个对象。 -/
theorem toAlphaData_obj_of_rel (P : Pairing.Pairing ι) (γ : ι → X.Carrier)
    {n m : ι} (h : P.rel n m) :
    ∃ t : (transInst P γ).Carrier, t.1.1 = γ n ∧ t.1.2 = γ m :=
  ⟨⟨(γ n, γ m), ⟨n, m, h, rfl, rfl⟩⟩, rfl, rfl⟩

/-- ⭐ **配对更窄 ⟹ 载体是 subtype 的收紧**（桥对 `P` 的单调性）。

注意：返回类型在 `Type` 中（不是 `Prop`），故用 `def` 而非 `theorem`。 -/
def transInst_mono {P Q : Pairing.Pairing ι}
    (h : ∀ n m, P.rel n m → Q.rel n m) (γ : ι → X.Carrier)
    (t : (transInst P γ).Carrier) : (transInst Q γ).Carrier :=
  ⟨t.1, transitions_mono h γ t.2⟩

/-! ===========================================================================
  §2  FCA 算子在本桥下的计算式（复用 `AlphaData` 的定义等式）
  =========================================================================== -/

/-- ⭐ **$B'$ 计算式**：`B` 的极运算 = 前态属性包含 `B` 的转移对。 -/
theorem toAlphaData_polarDown (P : Pairing.Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attrₚ : X.Carrier → Set M) (B : Set M) :
    (toAlphaData P γ M attrₚ).ctx.polarDown B
      = { t : (transInst P γ).Carrier | B ⊆ attrₚ t.1.1 } := by
  rw [AlphaData.polarDown_eq]
  rfl

/-- ⭐ **$A'$ 计算式**：一组转移对的共同属性。 -/
theorem toAlphaData_polarUp (P : Pairing.Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attrₚ : X.Carrier → Set M) (A : Set (transInst P γ).Carrier) :
    (toAlphaData P γ M attrₚ).ctx.polarUp A
      = { m : M | ∀ t ∈ A, m ∈ attrₚ t.1.1 } := by
  rw [AlphaData.polarUp_eq]
  rfl

/-! ===========================================================================
  §3  三策略的转移对集包含关系（定理 2）
  =========================================================================== -/

/-- ⭐⭐ **【策略 B（分组）⊆ 策略 A（相邻）】** -/
theorem transitions_grouped_subset_adjacent
    {lt : ι → ι → Prop} {G : Type v} (g : ι → G) (γ : ι → X.Carrier) :
    Pairing.transitions (Pairing.grouped lt g) γ
      ⊆ Pairing.transitions (Pairing.adjacent lt) γ := by
  rintro ⟨a, b⟩ ⟨n, m, ⟨-, hadj⟩, rfl, rfl⟩
  exact ⟨n, m, hadj, rfl, rfl⟩

/-- ⭐⭐ **【策略 A（相邻）⊆ 策略 B'（`lt` 直接给）】** -/
theorem transitions_adjacent_subset_direct
    {lt : ι → ι → Prop} (γ : ι → X.Carrier) :
    Pairing.transitions (Pairing.adjacent lt) γ
      ⊆ Pairing.transitions (Pairing.direct lt) γ := by
  rintro ⟨a, b⟩ ⟨n, m, hadj, rfl, rfl⟩
  exact ⟨n, m, Adjacency.adjacent_implies_lt hadj, rfl, rfl⟩

/-- ⭐⭐⭐ **【三策略链】：`grouped ⊆ adjacent ⊆ direct`**（分组最严、先后最宽）。 -/
theorem transitions_grouped_subset_direct
    {lt : ι → ι → Prop} {G : Type v} (g : ι → G) (γ : ι → X.Carrier) :
    Pairing.transitions (Pairing.grouped lt g) γ
      ⊆ Pairing.transitions (Pairing.direct lt) γ :=
  subset_trans (transitions_grouped_subset_adjacent g γ)
    (transitions_adjacent_subset_direct γ)

/-- **`direct P.rel` 是任意 `P` 的松弛**（同转对集包含）。 -/
theorem transitions_subset_direct (P : Pairing.Pairing ι) (γ : ι → X.Carrier) :
    Pairing.transitions P γ ⊆ Pairing.transitions (Pairing.direct P.rel) γ := by
  rintro ⟨a, b⟩ ⟨n, m, h, rfl, rfl⟩
  exact ⟨n, m, h, rfl, rfl⟩

/-- **`direct` 无损还原关系**（定义等式）。 -/
theorem transitions_direct (rel : ι → ι → Prop) (γ : ι → X.Carrier) :
    Pairing.transitions (Pairing.direct rel) γ
      = { t : Pairing.Transition X | ∃ n m : ι, rel n m ∧ γ n = t.1 ∧ γ m = t.2 } :=
  rfl

/-! ===========================================================================
  §4  紧邻方向的正向桥梁（替代不可证的「反推」定理）
  =========================================================================== -/

/-- ⭐⭐ **【紧邻条件 ⟹ 转移规则】**

若 `A` 的每个紧邻后继都落在 `B`，则 `adjacent lt` 的转移对集上 `TransRule A B` 成立。

**⟹ 「轨迹级条件 ⟹ 转移级规则」的正向桥梁。** -/
theorem transRule_of_adjacent
    {lt : ι → ι → Prop} (γ : ι → X.Carrier) {A B : Set X.Carrier}
    (h : ∀ n m : ι, Adjacency.Adjacent lt n m → γ n ∈ A → γ m ∈ B) :
    Pairing.TransRule A B (Pairing.transitions (Pairing.adjacent lt) γ) := by
  rintro ⟨a, b⟩ ⟨n, m, hadj, rfl, rfl⟩ hpre
  exact h n m hadj hpre

/-- ⭐ **【同组紧邻 ⟹ 分组策略下的规则】** -/
theorem transRule_of_grouped
    {lt : ι → ι → Prop} {G : Type v} (g : ι → G) (γ : ι → X.Carrier)
    {A B : Set X.Carrier}
    (h : ∀ n m : ι, g n = g m → Adjacency.Adjacent lt n m → γ n ∈ A → γ m ∈ B) :
    Pairing.TransRule A B (Pairing.transitions (Pairing.grouped lt g) γ) := by
  rintro ⟨a, b⟩ ⟨n, m, ⟨hg, hadj⟩, rfl, rfl⟩ hpre
  exact h n m hg hadj hpre

/-- ⭐⭐ **【宽策略规则 ⟹ 窄策略规则】**：`direct lt` 上的规则限制到 `adjacent lt` 仍成立。 -/
theorem transRule_restrict_to_adjacent
    {lt : ι → ι → Prop} (γ : ι → X.Carrier) {A B : Set X.Carrier}
    (hr : Pairing.TransRule A B (Pairing.transitions (Pairing.direct lt) γ)) :
    Pairing.TransRule A B (Pairing.transitions (Pairing.adjacent lt) γ) :=
  fun t ht hpre => hr t (transitions_adjacent_subset_direct γ ht) hpre

end PairingAlphaBridge

end FateV2.Predict