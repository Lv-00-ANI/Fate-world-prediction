import FateWorld.Legacy.RuleLevel

/-! ===========================================================================
  §0  轨迹级规律：谓词为主，属性集为构造方式（作者确认）

  **裁决来源**：作者原话「谓词为主，属性集为构造方式」

  ## 设计

  **「轨迹级规律」的核心是一个关于整条轨迹的谓词**：
  $$\text{TrajPattern} := \text{Traj}\ \iota\ X \to \text{Prop}$$

  **属性集不是定义，而是构造谓词的一种方式**：
  「出现过属性幂 A」是一位谓词，「A 后出现 B」是另一位。

  ## 为什么这样更好（对比草案的 `Set (Set X)`）

  草案 `pre post : Set (Set X.Carrier)` **有歧义**：
  * 读法 1：`pre` 是**属性的集合**（每个属性是状态子集）
  * 读法 2：`pre` 是**属性集的集合**（组合）
  * 读法 3：`pre` 是**状态集的集合**

  **改用谓词后，这些歧义全部消失** —— 谓词直接说「轨迹满足什么」。

  ## 诚实边界

  * 谓词形式**失去了 FCA 的闭包结构**（不能直接谈「闭集」「蕴含基」）。
  * 补偿：提供「属性集 → 谓词」的构造函数，**FCA 结构在构造这一侧保留**。
  =========================================================================== -/

namespace Fate

namespace TrajPattern

/-- **轨迹级规律**：一个关于整条轨迹的谓词。

**这是本项目「轨迹级规律」的核心载体** —— 只关心轨迹满足什么，
不预设它从哪种数据类型来。 -/
def TrajPattern (ι : Type u) (X : StateSpace) : Type _ :=
  Traj ι X → Prop

variable {ι : Type u} {X : StateSpace}

/-! ### §0.1 ⭐ 属性集 → 谓词的构造（FCA 结构保留在这里） -/

/-- **「出现过属性幂 `A`」**：存在某时刻的状态落在 `A` 里。

`A : Set X.Carrier` 是一个属性（状态子集）。 -/
def occurs (A : Set X.Carrier) : TrajPattern ι X :=
  fun γ => ∃ n : ι, γ n ∈ A

/-- **「出现过 `A` 后出现 `B`」**（不要求相邻）。

⚠ **这需要 `ι` 上有一个「先于」关系** —— 故以参数传入。 -/
def occursBefore (lt : ι → ι → Prop) (A B : Set X.Carrier) : TrajPattern ι X :=
  fun γ => ∃ n m : ι, lt n m ∧ γ n ∈ A ∧ γ m ∈ B

/-- **「出现过 `A` 后立即出现 `B`」**（紧邻）。

⚠ 需 `succ : ι → ι`（后继）—— 这是「紧邻性」的形式化。 -/
def occursNext (succ : ι → ι) (A B : Set X.Carrier) : TrajPattern ι X :=
  fun γ => ∃ n : ι, γ n ∈ A ∧ γ (succ n) ∈ B

/-! ### §0.2 组合：多个属性集 -/

/-- **「出现过某个 `A ∈ As`」**（`As` 是一族属性）。 -/
def occursAny (As : Set (Set X.Carrier)) : TrajPattern ι X :=
  fun γ => ∃ A ∈ As, ∃ n : ι, γ n ∈ A

/-- **「先出现过某个 `A ∈ As`，再出现过某个 `B ∈ Bs`」**。

**这是「属性集为构造方式」的主力构造函数** ——
对应「轨迹级规律：若轨迹中出现过 As 中的某个，则也会出现 Bs 中的某个」。 -/
def occursAnyBefore (lt : ι → ι → Prop) (As Bs : Set (Set X.Carrier)) : TrajPattern ι X :=
  fun γ => ∃ A ∈ As, ∃ B ∈ Bs, ∃ n m : ι,
    lt n m ∧ γ n ∈ A ∧ γ m ∈ B

/-! ### §0.3 轨迹级规律的相等与蕴含 -/

/-- **轨迹级蕴含**：`P` 蕴含 `Q`（在一切轨迹上）。 -/
def TrajImplies (P Q : TrajPattern ι X) : Prop :=
  ∀ γ : Traj ι X, P γ → Q γ

/-- **轨迹级蕴含的自反性**。 -/
theorem trajImplies_refl (P : TrajPattern ι X) : TrajImplies P P :=
  fun _ h => h

/-- **轨迹级蕴含的传递性**。 -/
theorem trajImplies_trans {P Q R : TrajPattern ι X}
    (h₁ : TrajImplies P Q) (h₂ : TrajImplies Q R) : TrajImplies P R :=
  fun γ hp => h₂ γ (h₁ γ hp)

/-! ### §0.4 ⚠ 从轨迹级到转移级（紧邻性条件） -/

/-! **⚠ 不能无条件细化**（反例记录）。

设轨迹为 `A, C, B`（中间隔着 `C`），则：
* 「出现过 `A` 后出现 `B`」**成立**
* 「`A` 之后**立即** `B`」**不成立**

**⟹ 从轨迹级细化到转移级，必须加紧邻条件。**

本节**不给出**这个细化定理 —— 因为它需要 `succ` 与 `lt` 的相容性假设，
且需要证明「轨迹级规律 + 紧邻性 ⟹ 转移级规律」，**该定理尚未构造**。 -/

/-- **紧邻性条件（缺口登记）**：`succ` 与 `lt` 相容（`succ n` 是 `n` 的「紧后继」）。

**这是缺口，不是定理** —— 不进任何下游证明。 -/
structure AdjacencyAxiom (succ : ι → ι) (lt : ι → ι → Prop) : Prop where
  step : ∀ n, lt n (succ n)
  minimal : ∀ n m, lt n m → ¬ (m = succ n) → ∃ k, lt n k ∧ lt k m

end TrajPattern

end Fate
