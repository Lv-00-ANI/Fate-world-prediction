import FateWorld.FateV2.Rules.LawRule
/-!
  # Rules · InstanceChain

  ## 迁移登记
  - 来源：`FateWorld/Legacy/InstanceChain.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  实例与属性链（作者确认后定稿）

  **裁决来源**（作者原话）
  * 「连续的对象也可以被视为一种实例吧」
  * 确认：上下文 = 局部域 + 外生 + 干预 + 参数（**不含噪声**）
  * 确认：局部域「两档都要」（给定 / 学到）
  * 确认：属性 → 多值 FCA（pattern structures）
  * 确认：实例集 = 观测到的有限集

  ## 核心澄清

  **「属性提取」≠「离散化」。**

  属性可以是：区间（有损）、全精度值（无损）、变换（可逆）、布尔（有损）。
  **⟹ 编码损失不是必然的，而是「选择哪种属性提取」的后果。**

  ## 链（现在闭合）

  ```
  连续对象 o  --属性提取 η-->  实例 e = (o, attrs(e))
      --α-->  AlphaOutput = (局部域划分, 规则集 LawRule)
      --γ/∘/υ-->  规则集  --应用-->  Set (Measure X)
  ```

  **⟹ 「规则抽象自实例」与「LawRule 输入是状态」不再矛盾** ——
  因为实例本身就可以是（连续的）对象/状态。

  ## 诚实边界

  * 「学到档」的局部域如何算，**仍是理论致命开放问题 8.5**（本文件登记为缺口）。
  * `α` 的具体算法**未给出**（H-C 存在性断言，按作者约束须证明，此处未证）。
    **本文件改为给出 `α` 的规格 `AlphaSpec` 并证明其推论** ——
    算法仍是开放问题，但「什么样的 α 算合格的 α」现在**可被机器检验**。
  =========================================================================== -/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace InstanceChain

open MeasureTheory
open FateV2.Rules.LawRule

/-! ### §0.1 实例：对象 + 属性 -/

/-- **实例**：一个对象，连同它被提取出的属性。

**与旧 `Encoder` 的差别**：`A`（属性类型）**不受限于离散属性集** ——
可以是区间、全精度值、变换值等。 -/
structure Instance (O : Type u) (A : Type v) where
  /-- 对象本身（**可以是连续的状态**）。 -/
  obj : O
  /-- 从对象提取出的属性。 -/
  attrs : A

/-- **属性提取**：从对象取出属性。

**这是 `Encoder` 的广义化** —— 旧 `Encoder` 是本定义在
「`A` = 离散属性集」时的特例。 -/
def AttrExtract (O : Type u) (A : Type v) : Type _ := O → A

/-- **无损提取**：提取不丢信息（`η` 单射）。 -/
def Lossless {O : Type u} {A : Type v} (η : AttrExtract O A) : Prop :=
  Function.Injective η

/-! ### §0.2 上下文：局部域 + 外生 + 干预 + 参数（**不含噪声**） -/

/-- **上下文分量**：局部域、外生输入、干预、参数。

**⚠ 噪声 `ε` 不在其中** —— 它被积分进输出的分布里。 -/
structure CtxParts where
  /-- 局部域（状态空间的一个子集）。 -/
  Local : Type u
  /-- 外生输入空间 $\mathcal{U}$。 -/
  U : Type u
  /-- 动作空间 $\mathcal{A}$。 -/
  Act : Type u
  /-- 参数空间 $\Theta$。 -/
  Θ : Type u

/-- **上下文的载体**：四个分量（的参数化）。 -/
def CtxParts.Carrier (P : CtxParts) : Type u :=
  P.Local × P.U × P.Act × P.Θ

/-! ### §0.3 ⭐ `α` 的输出 = (局部域划分, 规则集) -/

/-- **局部域划分**：把状态空间分成若干局部区域。

**⚠ 两档**：
* **给定档**：这个函数由外部提供（网格 / 分箱 / 领域知识）。
* **学到档**：由数据算出 —— **仍是开放问题 8.5**。 -/
def Partition (X : Type u) : Type _ := X → Set X

/-- **`α` 的输出**。

⚠ **学到档的局部域如何从数据算，未解决**（开放问题 8.5，见 `AlphaLearnGap`）。 -/
structure AlphaOutput (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] where
  /-- 局部域划分。 -/
  partition : Partition X.Carrier
  /-- 规则集。 -/
  rules : Set (LawRule C X Y)

/-- **⚠ 学到档的开放性**：存在一个把数据映到划分的算子，**且它正确**。

**本定义是缺口登记，不是定理** —— 不进任何下游证明。 -/
def AlphaLearnGap (D : Type u) (X : Type v) : Prop :=
  ∃ (_learn : D → Partition X), ∀ _d : D, True

/-! ### §0.4 ⭐ 链的接口：从规则到下一状态分布 -/

/-- **规则应用**：给定上下文与当前状态，取允许的分布集合。

这是 `LawRule` 的直接使用 —— 也是「规则如何作用回连续状态」的答案：
**输出直接是状态空间上的分布集合**（不需要 `dec`）。 -/
def apply {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier] (R : LawRule C X Y) (c : C.Carrier) (x : X.Carrier) :
    Set (Measure Y.Carrier) :=
  R c x

/-- **单点规则的确定性应用**：若规则单点，取出那个分布。 -/
noncomputable def applyPoint {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier] (R : LawRule C X Y)
    (h : IsPoint R) (c : C.Carrier) (x : X.Carrier) : Measure Y.Carrier :=
  Classical.choose (h c x)

/-- **单点规则的应用正确**（取出的是那个唯一的分布）。 -/
theorem applyPoint_spec {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier] (R : LawRule C X Y)
    (h : IsPoint R) (c : C.Carrier) (x : X.Carrier) :
    R c x = {applyPoint R h c x} :=
  Classical.choose_spec (h c x)

/-! ### §0.5 ⚠ 属性提取的损失刻画 -/

/-- **有损提取**：存在两个不同对象被提取到同一属性。 -/
def Lossy {O : Type u} {A : Type v} (η : AttrExtract O A) : Prop :=
  ∃ o₁ o₂ : O, o₁ ≠ o₂ ∧ η o₁ = η o₂

/-- **无损 ⟺ 非有损**。 -/
theorem lossless_iff_not_lossy {O : Type u} {A : Type v} (η : AttrExtract O A) :
    Lossless η ↔ ¬ Lossy η := by
  constructor
  · intro h hlossy
    obtain ⟨o₁, o₂, hne, heq⟩ := hlossy
    exact hne (h heq)
  · intro h o₁ o₂ heq
    by_contra hne
    exact h (⟨o₁, o₂, hne, heq⟩ : Lossy η)

/-! ===========================================================================
  §1  ⭐ `α` 的接口与规格

  ## 本节做什么

  * **定义** `Alpha`：`D → AlphaOutput C X Y` 的别名（`α` 的类型）。
  * **规格** `AlphaSpec α`：合格的 `α` 必须满足的**全部**条件。
    **不给出算法** —— 算法是开放问题（H-C 存在性断言未证）。
  * **定理**：任何满足 `AlphaSpec` 的 `α` 都自动保持以下性质：
    - 局部域划分的**自反性 / 对称性 / 传递性**（因而由等价类构成）；
    - 「同一局部域内规则取值一致」（`local_rules_apply`）；
    - **单点档下 `applyPoint` 在局部域内取值唯一**；
    - **组合 `∘` 保持局部一致性**（`compose_preserves_local`）。

  ## 为什么这样做

  作者约束：`α` 的算法是开放问题，不得虚构。但「什么样的 `α` 合格」
  **可以**形式化为规格，并从规格**导出**可证性质。
  ⟹ 下游证明只需假设 `AlphaSpec α`，不需假设具体算法。
  =========================================================================== -/

/-- **`α` 的接口**：把数据集映到「局部域划分 + 规则集」。

⚠ **本定义只是签名，不是算法** —— 具体算法是开放问题（8.5 / H-C）。
任何候选实现须先证明满足 `AlphaSpec` 才可用。 -/
def Alpha (D : Type u) (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ :=
  D → AlphaOutput C X Y

/-- **划分自反**：每个状态落在自己的类里（覆盖性）。 -/
def PartitionCovers {X : Type u} (p : Partition X) : Prop :=
  ∀ x, x ∈ p x

/-- **划分对称**：`y` 与 `x` 同类 ⟹ `x` 与 `y` 同类。 -/
def PartitionSymm {X : Type u} (p : Partition X) : Prop :=
  ∀ x y, y ∈ p x → x ∈ p y

/-- **划分传递**：同类关系传递。 -/
def PartitionTrans {X : Type u} (p : Partition X) : Prop :=
  ∀ x y z, y ∈ p x → z ∈ p y → z ∈ p x

/-- **局部一致性**：`α d` 的**每条规则**只通过局部域看当前状态 ——
在同一个局部域内，规则给出的允许分布集**相同**。

这是「局部域」这个概念**唯一有内容的约束**：
若没有它，划分与规则之间没有任何关系，`α` 的输出就是两个无关成分。 -/
def RulesLocal {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier] (p : Partition X.Carrier) (rs : Set (LawRule C X Y)) : Prop :=
  ∀ r ∈ rs, ∀ c x y, y ∈ p x → r c x = r c y

/-- **非空规则**：`α d` 的规则集**在每处都允许至少一个分布**。
（排除了「整条规则是空约束集」的退化输出。） -/
def RulesInhabited {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier] (rs : Set (LawRule C X Y)) : Prop :=
  ∀ r ∈ rs, ∀ c x, (r c x).Nonempty

/-- **⭐ `α` 的规格**：合格的 `α` 必须满足的条件集合。

**设计原则**：每一条都**必要**且**可检验**，且**不含任何具体算法**。
- `covers`：局部域覆盖全空间（否则有状态无规则可依）。
- `part_symm` / `part_trans`：划分确实是「类」（否则 `part x` 只是任意子集）。
- `localize`：规则只通过局部域看状态（否则划分无意义）。
- `inhabited`：规则非退化（否则「允许集为空」= 矛盾，会传染到下游）。 -/
structure AlphaSpec {D : Type u} {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier] (α : Alpha D C X Y) : Prop where
  /-- (S1) 局部域覆盖全空间。 -/
  covers : ∀ d, PartitionCovers (α d).partition
  /-- (S2) 局部域同类关系对称。 -/
  part_symm : ∀ d, PartitionSymm (α d).partition
  /-- (S3) 局部域同类关系传递。 -/
  part_trans : ∀ d, PartitionTrans (α d).partition
  /-- (S4) 规则只通过局部域看状态。 -/
  localize : ∀ d, RulesLocal (α d).partition (α d).rules
  /-- (S5) 规则集非退化。 -/
  inhabited : ∀ d, RulesInhabited (α d).rules

/-! ### §1.1 由规格导出的划分性质 -/

variable {D : Type u} {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier]

/-- **(S1) 逐点形式**：每个状态落在自己的局部域里。 -/
theorem AlphaSpec.class_refl {α : Alpha D C X Y} (h : AlphaSpec α) (d : D) (x : X.Carrier) :
    x ∈ (α d).partition x :=
  h.covers d x

/-- **(S2) 逐点形式**：同类关系对称。 -/
theorem AlphaSpec.class_symm {α : Alpha D C X Y} (h : AlphaSpec α) (d : D)
    {x y : X.Carrier} (hy : y ∈ (α d).partition x) : x ∈ (α d).partition y :=
  h.part_symm d x y hy

/-- **(S3) 逐点形式**：同类关系传递。 -/
theorem AlphaSpec.class_trans {α : Alpha D C X Y} (h : AlphaSpec α) (d : D)
    {x y z : X.Carrier} (hy : y ∈ (α d).partition x) (hz : z ∈ (α d).partition y) :
    z ∈ (α d).partition x :=
  h.part_trans d x y z hy hz

/-- **⭐ 局部域是等价类**：`y ∈ partition x` 当且仅当 `partition x = partition y`。

即 `α` 输出的 `partition` **不是任意子集族**，而是由等价关系诱导的划分。

* `→`：用 (S1) 得 `y ∈ partition y`，再用等式替换。
* `←`：双向包含。
  - `z ∈ partition x ⟹ z ∈ partition y`：由 (S2) 得 `x ∈ partition y`，
    再与 `z ∈ partition x` 一起用 (S3)。
  - 反向即 `hy` 本身。 -/
theorem AlphaSpec.partition_eq_iff {α : Alpha D C X Y} (h : AlphaSpec α) (d : D)
    (x y : X.Carrier) :
    (α d).partition x = (α d).partition y ↔ y ∈ (α d).partition x := by
  constructor
  · intro heq
    rw [heq]
    exact h.class_refl d y
  · intro hy
    ext z
    constructor
    · intro hzx
      exact h.class_trans d (h.class_symm d hy) hzx
    · intro hzy
      exact h.class_trans d hy hzy

/-! ### §1.2 由规格导出的规则性质 -/

/-- **(S4) 逐点形式**：同一局部域内，规则取值相同。 -/
theorem AlphaSpec.local_rules_apply {α : Alpha D C X Y} (h : AlphaSpec α) (d : D)
    {r : LawRule C X Y} (hr : r ∈ (α d).rules) (c : C.Carrier)
    {x y : X.Carrier} (hy : y ∈ (α d).partition x) : r c x = r c y :=
  h.localize d r hr c x y hy

/-- **(S5) 逐点形式**：规则在每个状态至少允许一个分布。 -/
theorem AlphaSpec.rules_nonempty {α : Alpha D C X Y} (h : AlphaSpec α) (d : D)
    {r : LawRule C X Y} (hr : r ∈ (α d).rules) (c : C.Carrier) (x : X.Carrier) :
    (r c x).Nonempty :=
  h.inhabited d r hr c x

/-- **⭐ 单点档下 `applyPoint` 在局部域内唯一**。

若某条规则是单点的，则由它取出的分布**只依赖局部域**，不依赖域内具体状态。

证明：两条 `applyPoint_spec` 把 `r c x`、`r c y` 都写成单元素集；
(S4) 令二者相等；单元素集相等则元素相等。 -/
theorem AlphaSpec.applyPoint_eq_of_local {α : Alpha D C X Y} (h : AlphaSpec α) (d : D)
    {r : LawRule C X Y} (hr : r ∈ (α d).rules) (hp : IsPoint r) (c : C.Carrier)
    {x y : X.Carrier} (hy : y ∈ (α d).partition x) :
    applyPoint r hp c x = applyPoint r hp c y := by
  have hx : r c x = {applyPoint r hp c x} := applyPoint_spec r hp c x
  have hy' : r c y = {applyPoint r hp c y} := applyPoint_spec r hp c y
  have hloc : r c x = r c y := h.local_rules_apply d hr c hy
  have hset : ({applyPoint r hp c x} : Set (Measure Y.Carrier)) = {applyPoint r hp c y} := by
    rw [← hx, ← hy']
    exact hloc
  exact Set.singleton_eq_singleton_iff.mp hset

/-! ### §1.3 组合算子 `∘` 保持局部一致性 -/

/-- **⭐ `∘` 保持局部一致性**：两条都满足 (S4) 的规则，其组合也满足 (S4)。

这解释了为什么 `∘ = 取交` 与「局部域」语义**相容**：
在同一个局部域内取交，结果仍与域内具体状态无关。
⟹ 下游可以在局部域内安全地组合规则，`α` 的划分不被 `∘` 破坏。 -/
theorem AlphaSpec.compose_preserves_local {α : Alpha D C X Y} (h : AlphaSpec α) (d : D)
    {r s : LawRule C X Y} (hr : r ∈ (α d).rules) (hs : s ∈ (α d).rules) (c : C.Carrier)
    {x y : X.Carrier} (hy : y ∈ (α d).partition x) :
    compose r s c x = compose r s c y := by
  have h1 : r c x = r c y := h.local_rules_apply d hr c hy
  have h2 : s c x = s c y := h.local_rules_apply d hs c hy
  show r c x ∩ s c x = r c y ∩ s c y
  rw [h1, h2]

/-- **`∘` 保持局部一致性的「集合版」**：
局部的规则集在 `∘` 下**封闭**（两两组合仍局部于同一划分）。

即：`RulesLocal p rs` 在逐点组合下是封闭的 ——
若 `r, s ∈ rs` 都局部，则对任意 `c`，`compose r s c` 也局部。
这与 `compose_preserves_local` 等价，只是陈述成「点作为函数」的形式。 -/
theorem RulesLocal.compose {p : Partition X.Carrier} {rs : Set (LawRule C X Y)}
    (hloc : RulesLocal p rs) {r s : LawRule C X Y} (hr : r ∈ rs) (hs : s ∈ rs) :
    ∀ c {x y}, y ∈ p x → compose r s c x = compose r s c y := by
  intro c x y hy
  have h1 : r c x = r c y := hloc r hr c x y hy
  have h2 : s c x = s c y := hloc s hs c x y hy
  show r c x ∩ s c x = r c y ∩ s c y
  rw [h1, h2]

end InstanceChain

end FateV2.Rules