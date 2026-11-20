import FateWorld.FateV2.Rules.FcaToRuleTerm
import Mathlib.Data.Finset.Lattice.Fold

/-!
  # Rules · MVFCAFinset

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MVFCAFinset.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FcaToRuleTerm
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  MVFCA · **`minClosed` / `attrClosure` 的 Finset 版（可枚举算法）**

  COMPLEX-1 §5 第 9、10 条：
  * 第 10 条：`minClosed`（`Fate/FateV2.Predict.AlphaMVFCA.lean`，`K.cl {g}`，`Set` 层）
    只有「`Set` 层 ⋂₀ / `down` 定义」，**没有 Finset 计算版**；
  * 第 9 条：`attrClosure`（`Fate/FcaToRuleTerm.lean`，`∃` 定义）同理。

  本模块在 `[Fintype G]` + `[DecidableEq L]` 下给出**只需枚举 `G` 全部元素**
  的计算版，并证明它与 `Set` 版**逐点一致**。

  ---------------------------------------------------------------------------
  §0  `Set` 版定义（原文，逐字引用）
  ---------------------------------------------------------------------------

  `Fate/MVFCAPositive.lean`：
  ```lean
  def up   (K) (A : Set G) : L     := ⨅ g ∈ A, K.desc g
  def down (K) (B : L) : Set G     := {g | B ≤ K.desc g}
  def cl   (K) (A : Set G) : Set G := K.down (K.up A)
  ```

  `Fate/FateV2.Predict.AlphaMVFCA.lean:67`：
  ```lean
  def minClosed (K : PatStruct G L) (g : G) : Set G := K.cl {g}
  ```
  ⟹ 展开：`minClosed K x = {y | (⨅ z ∈ ({x} : Set G), K.desc z) ≤ K.desc y}`

  `Fate/FcaToRuleTerm.lean:164`：
  ```lean
  def attrClosure (K) (attr) (x) : Set M := {m | ∃ y ∈ minClosed K x, m ∈ attr y}
  ```

  ---------------------------------------------------------------------------
  §1  ⭐ 关键观察：`minClosed K x` 里的 `⨅` **退化成一个单点**
  ---------------------------------------------------------------------------

  `⨅ z ∈ ({x} : Set G), K.desc z` —— 索引集是单点集，因此
  （`CompleteLattice` 的 `iInf` 语义，**不需要** `Fintype` 或任何可判定性）

  $$\bigsqcap_{z \in \{x\}} \delta z \;=\; \delta x$$

  于是 `minClosed K x = {y | δ x ≤ δ y}` —— **只依赖 `δ x` 与 `δ y`**。
  有 Decidable 的 `≤` 就能对 `G` 的每个元素判一次，得到有限集合。

  ⟹ 计算版的**全部内容**是：`Finset.univ.filter (fun y => K.desc x ≤ K.desc y)`。
  这个「算法」的代价是 `|G|` 次 `L` 上的可判定比较 —— 没有任何隐藏的无穷搜索。

  ---------------------------------------------------------------------------
  §2  诚实边界
  ---------------------------------------------------------------------------

  * **[Fintype G] 是真实假设**：主链（`AlphaMVFCA` / `FcaToRuleTerm`）都是
    **任意 `G` / 任意 `X.Carrier`**（不假定有限）。Finset 版必须有 `Fintype G`
    才能`univ`枚举。⟹ 本模块给出的是**在有限对象域上的可执行版本**，
    并证明它与主链的 `Set` 版在**同一 `K`、同一 `x`** 上相等；
    它**不**对无穷 `G` 给出算法（那是另一回事，且事实上不存在这种枚举）。
  * **[DecidableEq L] 只用于让 `filter` 可计算**。`Prop` 层的一致性定理
    甚至不需要它（见 `minClosedFinset_coe`，其陈述里 `DecidableEq L` 只用来
    让定义体通过 elaboration；数学内容是纯 `Iff`）。
    更精确地：一致性**不**依赖 `DecidableEq L` 的选择（`filter` 的结果
    与 Decidable 实例无关，见 `Finset.filter_congr_decidable`）。
  * 本模块**不**声称 `attrClosure` 的 M 侧可枚举 —— `attrClosure` 的量词
    `∃ y ∈ minClosed K x, m ∈ attr y` 中 `y` 现在可枚举，但 `attr y : Set M`
    仍是任意集合，需要 `[Fintype M]` 才能给出 `Finset M` 版；
    这里给出 `attrClosureFinset : Finset M` 及一致性定理
    `attrClosureFinset_coe`（COMPLEX-1 §5 第 9 条）。
  * 无 `sorry` / `admit` / `axiom`；不修改任何既有模块。
  =========================================================================== -/

namespace FateV2.Rules

open FateV2.Modeling
open FateV2.Predict.AlphaMVFCA
namespace AlphaMVFCA

open FateV2.Rules.MVFCA4

universe u v w

variable {G : Type u} {L : Type v} [CompleteLattice L]

/-! ### §1.0 ⭐ 单点 `⨅` 退化引理（`Set` 层，无任何有限性假设） -/

/-- ⭐ **单点索引的下确界就是该点**：`⨅ z ∈ ({x} : Set G), δ z = δ x`。

**这是本模块的核引理** —— 它把 `minClosed` 里的 `⨅` 消掉，
使整个闭包变成**逐点比较** `δ x ≤ δ y`，从而可被 `Finset.filter` 枚举。

证明只用 `le_iInf_iff` / `iInf_le_of_le`（`CompleteLattice` 的一般性质），
**不需要 `Fintype G`、不需要 `DecidableEq L`、不需要 `Nonempty G`**。 -/
theorem up_singleton (K : PatStruct G L) (x : G) : K.up ({x} : Set G) = K.desc x := by
  show (⨅ z ∈ ({x} : Set G), K.desc z) = K.desc x
  apply le_antisymm
  · exact le_trans (iInf_le (fun z => ⨅ (_ : z ∈ ({x} : Set G)), K.desc z) x)
      (iInf_le (fun (_ : x ∈ ({x} : Set G)) => K.desc x) (Set.mem_singleton x))
  · exact le_iInf fun z => le_iInf fun hz => by subst hz; exact le_rfl

/-- ⭐ **`minClosed` 的显式形式**：`minClosed K x = {y | δ x ≤ δ y}`。

由 `up_singleton` 直接代入 `minClosed` / `cl` / `down` 的定义即得。 -/
theorem minClosed_eq_setOf (K : PatStruct G L) (x : G) :
    minClosed K x = {y : G | K.desc x ≤ K.desc y} := by
  show K.down (K.up ({x} : Set G)) = {y : G | K.desc x ≤ K.desc y}
  rw [up_singleton]
  rfl

/-- **`minClosed` 的成员判定（定义性展开）**：`y ∈ minClosed K x ↔ δ x ≤ δ y`。 -/
theorem mem_minClosed_iff (K : PatStruct G L) (x y : G) :
    y ∈ minClosed K x ↔ K.desc x ≤ K.desc y := by
  rw [minClosed_eq_setOf]
  exact Iff.rfl

/-! ### §1.1 ⭐⭐ Finset 版 `minClosed` -/

/-- ⭐⭐ **`minClosed` 的 Finset 版（可枚举算法）**。

算法：枚举 `G` 的全部元素（`Finset.univ`），保留满足 `δ x ≤ δ y` 的那些。
代价 `|G|` 次 `L` 上的可判定比较。

**定义的选择**：用 `filter` 而非「先算 `⨅` 再筛」——两者给出同一个集合
（`up_singleton`），但 `filter` 形式**完全绕开**了对 `Set` 层 `⨅` 的任何
计算性依赖，也就不需要 `L` 的 `sInf` 可计算（`CompleteLattice` 只有 `Prop`
层的 `iInf`，不保证可计算）。 -/
def minClosedFinset [Fintype G] [DecidableRel (fun a b : L => a ≤ b)]
    (K : PatStruct G L) (x : G) : Finset G :=
  Finset.univ.filter (fun y => K.desc x ≤ K.desc y)

/-- **成员判定（定义性展开）**：`y ∈ minClosedFinset K x ↔ δ x ≤ δ y`。

（不需要！任何 `Set` 层的闭包推理 —— 这是 Finset 版「真的在算」的证据。） -/
theorem mem_minClosedFinset [Fintype G] [DecidableRel (fun a b : L => a ≤ b)]
    (K : PatStruct G L) (x y : G) :
    y ∈ minClosedFinset K x ↔ K.desc x ≤ K.desc y := by
  unfold minClosedFinset
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ y, h⟩⟩

/-- ⭐ **`x` 自己在自己的 Finset 最小闭集里**（`≤` 自反）。 -/
theorem self_mem_minClosedFinset [Fintype G] [DecidableRel (fun a b : L => a ≤ b)]
    (K : PatStruct G L) (x : G) : x ∈ minClosedFinset K x := by
  rw [mem_minClosedFinset]

/-- ⭐⭐ **【Finset 版与 Set 版一致】**（COMPLEX-1 §5 第 10 条的核心交付）。

`(minClosedFinset K x : Set G) = minClosed K x` —— 逐点 `Iff`，
两侧都由 `mem_minClosedFinset` / `mem_minClosed_iff` 给出 `δ x ≤ δ y`。

⚠ **前件检查（纪律 7）**：前件只有类型类 `[Fintype G]`（枚举所需）与
`[DecidableRel (· ≤ ·)]`（判定所需）。**没有任何前件提到 `minClosed`、
`minClosedFinset`、`cl` 或它们的相等性** —— 结论不是前件的重述。 -/
theorem minClosedFinset_coe [Fintype G] [DecidableRel (fun a b : L => a ≤ b)]
    (K : PatStruct G L) (x : G) :
    (minClosedFinset K x : Set G) = minClosed K x := by
  ext y
  rw [Finset.mem_coe, mem_minClosedFinset, mem_minClosed_iff]

/-! ### §1.2 ⭐ 一致性不依赖 `Decidable` 实例的选择 -/

/-- ⭐ **`Decidable` 实例无关**：换一个 `≤` 上的 `Decidable` 实例，
`minClosedFinset` 作为**集合**不变。

（`Finset.filter_congr_decidable`：`Finset` 的 `filter` 结果与实例无关，
因为 `Finset` 的子集性质是 `Prop` 层的。⟹ §1.1 的「算法」在数学上是
良定义的，不是一个「凑巧可跑」的实现。） -/
theorem minClosedFinset_decidable_irrel [Fintype G]
    (K : PatStruct G L) (x : G)
    (d₁ : (a b : L) → Decidable (a ≤ b)) (d₂ : (a b : L) → Decidable (a ≤ b)) :
    @minClosedFinset G L _ _ (fun a b => d₁ a b) K x
      = @minClosedFinset G L _ _ (fun a b => d₂ a b) K x := by
  show @Finset.filter G _ (fun y => d₁ (K.desc x) (K.desc y)) Finset.univ
      = @Finset.filter G _ (fun y => d₂ (K.desc x) (K.desc y)) Finset.univ
  exact Finset.filter_congr_decidable _ _ _

/-! ### §1.3 闭集性在 Finset 版的对应 -/

/-- ⭐ **Finset 版仍是最小闭集**：`minClosedFinset_coe` 与 `minClosed_isClosed`
合起来说明 Finset 版算出的**正是**一个闭集。 -/
theorem minClosedFinset_isClosed [Fintype G] [DecidableRel (fun a b : L => a ≤ b)]
    (K : PatStruct G L) (x : G) : K.IsClosed (minClosedFinset K x : Set G) := by
  rw [minClosedFinset_coe]
  exact minClosed_isClosed K x

end AlphaMVFCA

/-! ===========================================================================
  §2  ⭐ `attrClosure` 的 Finset 版（COMPLEX-1 §5 第 9 条）

  `attrClosure` 原有定义是纯 `∃`（`Fate/FcaToRuleTerm.lean:164`）：
  ```lean
  def attrClosure (K) (attr : X.Carrier → Set M) (x) : Set M :=
    {m | ∃ y ∈ FateV2.Predict.AlphaMVFCA.minClosed K x, m ∈ attr y}
  ```
  两个量词都可枚举后即为 Finset 版：
  * `y` 由 `minClosedFinset` 枚举（`[Fintype X.Carrier]`）；
  * `m` 由 `attr y : Set M` 筛出（`[Fintype M]` + 属性侧可判定）。

  本节放在 `FcaToRuleTerm` 命名空间下（`attrClosure` 所在处），
  保证下游 `import FateV2.Rules` 后能直接替换 `Set` 版。
  =========================================================================== -/

namespace FcaToRuleTerm

open FateV2.Rules.MVFCA4

universe u₁ u₂ v₁

variable {X : StateSpace} {M : Type u₁} {L : Type v₁} [CompleteLattice L]

/-! ### §2.1 ⭐⭐ Finset 版 `attrClosure` -/

/-- ⭐⭐ **`attrClosure` 的 Finset 版（可枚举算法）**。

算法：
1. `minClosedFinset K x` 枚举局部域里的对象 `y`（代价 `|X.Carrier|` 次比较）；
2. 对每个 `y`，用 `Finset.univ.filter (attr y)` 取出 `attr y` 里的属性 `m`
   （代价 `|M|` 次成员判定）；
3. 取并（`Finset.biUnion`）。

总代价 `|X.Carrier| · |M|` —— 有限、无搜索、无 `∃` 的不可判定成分。

**与 `Set` 版的关系**：量词 `∃ y ∈ minClosed K x, m ∈ attr y` 中
`y` 由 `minClosedFinset` 枚举、`m` 由 `univ.filter` 枚举，
故两者逐点等价（`mem_attrClosureFinset`）。 -/
def attrClosureFinset [Fintype X.Carrier] [Fintype M]
    [DecidableRel (fun a b : L => a ≤ b)] [DecidableEq M]
    (K : PatStruct X.Carrier L) (attr : X.Carrier → Set M)
    (dattr : ∀ y : X.Carrier, DecidablePred (fun m : M => m ∈ attr y))
    (x : X.Carrier) : Finset M :=
  (FateV2.Rules.AlphaMVFCA.minClosedFinset K x).biUnion
    (fun y => @Finset.filter M (fun m => m ∈ attr y) (dattr y) Finset.univ)

/-- **成员判定**：`m ∈ attrClosureFinset K attr x ↔ ∃ y ∈ minClosedFinset K x, m ∈ attr y`。

（`Finset.mem_biUnion` + `Finset.mem_filter` + `Finset.mem_univ` 的纯组合，
**不需要**任何 `Set` 层的闭包推理。） -/
theorem mem_attrClosureFinset [Fintype X.Carrier] [Fintype M]
    [DecidableRel (fun a b : L => a ≤ b)] [DecidableEq M]
    (K : PatStruct X.Carrier L) (attr : X.Carrier → Set M)
    (dattr : ∀ y : X.Carrier, DecidablePred (fun m : M => m ∈ attr y)) (x : X.Carrier) (m : M) :
    m ∈ attrClosureFinset K attr dattr x
      ↔ ∃ y ∈ FateV2.Rules.AlphaMVFCA.minClosedFinset K x, m ∈ attr y := by
  unfold attrClosureFinset
  rw [Finset.mem_biUnion]
  refine exists_congr fun y => ?_
  rw [and_congr_right_iff]
  intro _hy
  show (m ∈ @Finset.filter M (fun m => m ∈ attr y) (dattr y) Finset.univ) ↔ m ∈ attr y
  rw [@Finset.mem_filter M (fun m => m ∈ attr y) (dattr y) Finset.univ m]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ m, h⟩⟩

/-- ⭐⭐⭐ **【Finset 版与 Set 版一致】**（COMPLEX-1 §5 第 9 条的核心交付）。

`(attrClosureFinset K attr x : Set M) = attrClosure K attr x`。

证明：两侧都归约到「`∃ y, δ x ≤ δ y ∧ m ∈ attr y`」——
左侧用 `mem_attrClosureFinset` + `FateV2.Rules.AlphaMVFCA.mem_minClosedFinset`，
右侧用 `attrClosure` 的定义 + `FateV2.Rules.AlphaMVFCA.mem_minClosed_iff`。

⚠ **前件检查（纪律 7）**：前件只有 `[Fintype X.Carrier]` / `[Fintype M]`
（枚举所需）与 `[DecidableRel (· ≤ ·)]` / `[DecidableEq M]`（判定所需）。
**没有任何前件提到 `attrClosure` 或 `attrClosureFinset`** —— 非重述。 -/
theorem attrClosureFinset_coe [Fintype X.Carrier] [Fintype M]
    [DecidableRel (fun a b : L => a ≤ b)] [DecidableEq M]
    (K : PatStruct X.Carrier L) (attr : X.Carrier → Set M)
    (dattr : ∀ y : X.Carrier, DecidablePred (fun m : M => m ∈ attr y)) (x : X.Carrier) :
    (attrClosureFinset K attr dattr x : Set M) = attrClosure K attr x := by
  ext m
  rw [Finset.mem_coe, mem_attrClosureFinset]
  unfold attrClosure
  refine exists_congr fun y => ?_
  rw [FateV2.Rules.AlphaMVFCA.mem_minClosedFinset, FateV2.Rules.AlphaMVFCA.mem_minClosed_iff]

/-- ⭐ **Finset 版与 `attrClosure_eq_sUnion` 的连接**：
Finset 版算出的集合就是 `AlphaData.dgToLawRule` 中族 `attr '' minClosed K x` 的并。 -/
theorem attrClosureFinset_coe_eq_sUnion [Fintype X.Carrier] [Fintype M]
    [DecidableRel (fun a b : L => a ≤ b)] [DecidableEq M]
    (K : PatStruct X.Carrier L) (attr : X.Carrier → Set M)
    (dattr : ∀ y : X.Carrier, DecidablePred (fun m : M => m ∈ attr y)) (x : X.Carrier) :
    (attrClosureFinset K attr dattr x : Set M) = ⋃₀ (attr '' FateV2.Predict.AlphaMVFCA.minClosed K x) := by
  rw [attrClosureFinset_coe, attrClosure_eq_sUnion]

/-- ⚠ **诚实登记：属性侧可枚举性是真实假设**。

若 `M` 不可枚举（无 `Fintype M`），`attrClosureFinset` **无法给出**——
具体地说，`attr y : Set M` 是任意集合，没有 `Fintype M` 就无从列出其元素
（映射到 `Finset M` 一般不可计算）。故本节的 Finset 版
**只在 `[Fintype M]` 下成立**，与主链 `FcaToRuleTerm.attrClosure` 的
「任意 `M`」口径有实质差距，如实记录。 -/
theorem attrClosureFinset_definitional (K : PatStruct X.Carrier L)
    (attr : X.Carrier → Set M) (x : X.Carrier) :
    attrClosure K attr x = {m | ∃ y ∈ FateV2.Predict.AlphaMVFCA.minClosed K x, m ∈ attr y} :=
  rfl

end FcaToRuleTerm

end FateV2.Rules
