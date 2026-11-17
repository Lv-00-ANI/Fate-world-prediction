import FateWorld.FateV2.Model.Pairing
import FateWorld.FateV2.Rules.AlphaFCAConstruction
import FateWorld.FateV2.Model.Frame
/-!
  # Predict · PairingToAlphaData

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PairingToAlphaData.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Pairing, AlphaFCAConstruction, Frame
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
============================================================================
  规则核心链 · 断点① · **配对层 → FCA 数据**
  ## 本模块做什么
  把 `Pairing`（配对策略，策略 A/B/C 均可）与一条轨迹 `γ` 产生的**转移对集合**
  `Pairing.transitions P γ : Set (Transition X)`，变成 FCA 可以吃的 `AlphaData`。
  ## 关键事实（实测原文）
  ```lean
  -- Fate/AlphaFCAConstruction.lean:95
  structure AlphaData (E : InstSpace.{u}) (M : Type u) where
    obs : E.Carrier → Set M

  -- Fate/Frame.lean
  structure InstSpace where
    Carrier : Type*

  -- Fate/Pairing.lean:74
  abbrev Transition (X : StateSpace) : Type _ := X.Carrier × X.Carrier

  -- Fate/Pairing.lean:79
  def transitions (P : Pairing ι) (γ : ι → X.Carrier) : Set (Transition X) :=
    { t | ∃ n m : ι, P.rel n m ∧ γ n = t.1 ∧ γ m = t.2 }
  ```
  **⟹ `AlphaData` 只有一个字段 `obs`，`InstSpace` 只有一个字段 `Carrier`。**
  **⟹ 所以「配对 → FCA 数据」只需：对象是转移对，`obs` 取前态（或后态 / 两者）的属性。**
  ## 本模块的定理
  | # | 声明 | 内容 |
  |---|---|---|
  | 1 | `transInstSpace` | 转移对作为 `InstSpace` |
  | 2 | `pairingToAlphaData` | ⭐⭐⭐⭐ 配对 + 轨迹 → `AlphaData`（取前态属性） |
  | 3 | `pairingToAlphaData_obs` | 逐点展开（`rfl`） |
  | 4 | `pairingToAlphaData_post` | 变体：取后态属性 |
  | 5 | `pairingToAlphaData_both` | 变体：取前后态联合属性 |
  | 6 | `mem_transitions_iff'` | 转移对集合的成员判定（复用 Pairing 的） |
  ## 诚实边界
  - 本模块**只做类型构造**，不涉及 FCA 的蕴含抽取（那在 `AlphaFCAConstruction`）；
  - **不涉及配对三策略的语义差异**（那在 `Pairing.lean` 已由 `adjacent` / `grouped` / `direct` 给出）。
============================================================================
-/

namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
open FateV2.Rules
namespace PairingToAlphaData

open Pairing

noncomputable section

universe u

variable {ι : Type u} {X : StateSpace}

/-- **转移对构成的实例空间**：`InstSpace` 只有 `Carrier` 一个字段。 -/
def transInstSpace (X : StateSpace) : InstSpace.{u} := ⟨Transition X⟩

@[simp] theorem transInstSpace_carrier (X : StateSpace) :
    (transInstSpace X).Carrier = Transition X := rfl

/-- ⭐⭐⭐⭐ **【配对 + 轨迹 ⟹ FCA 数据（取前态属性）】**

给定：
- `P : Pairing ι`（配对策略，A/B/C 均可）
- `γ : ι → X.Carrier`（一条轨迹）
- `M` 与 `attr : X.Carrier → Set M`（状态 ↦ 属性集）

构造 `AlphaData`：
- 对象 = `Transition X`（转移对）
- 属性 = 前态的 `attr t.1`

**⟹ 这是断点① 的最后一块：配对层产生的转移对，直接就是 FCA 的对象集。** -/
def pairingToAlphaData (P : Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attr : X.Carrier → Set M) : AlphaData (transInstSpace X) M :=
  { obs := fun t => attr t.1 }

/-- ⭐ **`pairingToAlphaData` 的逐点展开**（`rfl` 级）。 -/
@[simp] theorem pairingToAlphaData_obs (P : Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attr : X.Carrier → Set M) (t : Transition X) :
    (pairingToAlphaData P γ M attr).obs t = attr t.1 := rfl

/-- ⭐⭐ **【取后态属性】** —— 「向前看」的读法。 -/
def pairingToAlphaDataPost (P : Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attr : X.Carrier → Set M) : AlphaData (transInstSpace X) M :=
  { obs := fun t => attr t.2 }

@[simp] theorem pairingToAlphaDataPost_obs (P : Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attr : X.Carrier → Set M) (t : Transition X) :
    (pairingToAlphaDataPost P γ M attr).obs t = attr t.2 := rfl

/-- ⭐⭐⭐ **【取前后态联合属性】** —— 转移规则 `A ⇒ B` 的载体。

**⟹ 这条对应 FCA 里的「转移规则」：前态满足 `A`、后态满足 `B`。** -/
def pairingToAlphaDataBoth (P : Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attr : X.Carrier → Set M) : AlphaData (transInstSpace X) (M × Bool) :=
  { obs := fun t => (attr t.1 ×ˢ {false}) ∪ (attr t.2 ×ˢ {true}) }

/-- **前态属性是联合属性的子集**（`Bool.dite` 无关的干净读法）。 -/
theorem pairingToAlphaDataBoth_pre_subset (P : Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attr : X.Carrier → Set M) (t : Transition X) :
    attr t.1 ×ˢ ({false} : Set Bool) ⊆
      (pairingToAlphaDataBoth P γ M attr).obs t := by
  intro m hm
  simp only [pairingToAlphaDataBoth, Set.mem_union, Set.mem_prod]
  exact Or.inl hm

/-- **后态属性也是子集。** -/
theorem pairingToAlphaDataBoth_post_subset (P : Pairing ι) (γ : ι → X.Carrier)
    (M : Type u) (attr : X.Carrier → Set M) (t : Transition X) :
    attr t.2 ×ˢ ({true} : Set Bool) ⊆
      (pairingToAlphaDataBoth P γ M attr).obs t := by
  intro m hm
  simp only [pairingToAlphaDataBoth, Set.mem_union, Set.mem_prod]
  exact Or.inr hm

/-- ⭐ **【转移对集合的成员判定】**（复用 `Pairing.mem_transitions_iff` 的精神）。 -/
theorem mem_transitions_of_rel (P : Pairing ι) (γ : ι → X.Carrier) {n m : ι}
    (h : P.rel n m) : (γ n, γ m) ∈ Pairing.transitions P γ :=
  ⟨n, m, h, rfl, rfl⟩

end
end PairingToAlphaData
end FateV2.Predict