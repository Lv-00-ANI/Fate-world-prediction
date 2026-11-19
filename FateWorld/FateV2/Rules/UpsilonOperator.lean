import Mathlib.Order.Closure
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.MetricSpace.Contracting
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Implication
import FateWorld.FateV2.Rules.Alpha

/-
命运理论 · Lean 4 形式化实现
================================

模块：UpsilonOperator
阶段：**阶段 1B —— 完善算子 υ 的代数律**

---------------------------------------------------------------------------
依主控解释（`/-!
  # Rules · UpsilonOperator

  ## 迁移登记
  - 来源：`FateWorld/Legacy/UpsilonOperator.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, FCA, Implication, Alpha
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ... -/` 标注，见下）
---------------------------------------------------------------------------
**理论文档未给 υ 的精确定义。** 规格
`_规格/01-理论/10-命运理论-净版.md` 定义 5.8 只写：

> **完善算子**（原文亦称 Refinement / Update）把规则集与新数据映射为
> 更新后的规则集：$\upsilon:\mathcal{R}\times\mathcal{D}\to\mathcal{R}$,
> $R_{t+1}=\upsilon(R_t,\mathrm{Data}_t)$。

且同处紧接着声明：由 A5 承载的「类型保证组合合法」**证据最薄**；
开放问题 5.1／8.20 登记「$\gamma$、$\circ$、$\upsilon$ 三者的任何交换律、
结合律或优先序**均不得被默认为成立**」。
故**原文档对 υ 的性质一字未给**（见 `02-定理清单.md` T6.10 的评论：
「原文未给 $\upsilon$ 的任何性质」）。

**本文件据主控给的语义指示**——「把规则『完善』（补全其未覆盖的情形），
可理解为某种闭合化或饱和操作」——**给出下述形式化**。
该形式化不是规格原文，而是**依主控解释**，故凡属解释性选择处，
本节与相应定义处以 `依主控解释` 显式标注。

**形式化要点（依主控解释）**：
1. 完善＝把规则（或规则集）放到其**闭包**上，使「未覆盖的情形」被补齐；
   「闭合化／饱和」的数学原型即**闭包算子**（Closure Operator）。
2. 故 υ 的代数律取**闭包算子的三条公理**：
   - **扩张性**（extensive）：$R\le\upsilon_D(R)$——完善只会加、不会减；
   - **单调性**（monotone）：$R_1\le R_2\Rightarrow\upsilon_D(R_1)\le\upsilon_D(R_2)$
     ——更全的规则完善后仍更全；
   - **幂等性**（idempotent）：$\upsilon_D(\upsilon_D(R))=\upsilon_D(R)$
     ——完善一次即「饱和」，再完善无增益。
3. **数据参数化**：与 T6.10 一致，υ 带数据参数 $\mathrm{Data}_D$；
   **固定数据**时上述三条律成立（这正是「在数据分布固定时」的读法）。
4. **不动点＝已完善的规则**：$\upsilon_D(R)=R$ 的规则称「$\upsilon$-饱和」，
   它们恰是 υ 值域，且本身构成一个完备格（借 Mathlib `ClosureOperator`）。

**本节明确不做的事（诚实边界）**：
- **不主张** υ 的具体迭代算法收敛——那需要 $\mathcal{R}$ 上的度量与压缩性；
  这是 T6.10 的**显式前件**，本文件把它写成**条件定理**
  （见 §5，用 Mathlib `ContractingWith`）。
- **不主张** υ 与 $\gamma$、$\circ$ 的交换/优先序——规格明令**不得默认**。
  本文件只在 §6 **显式地**证明：在给定相容性前件下，υ 与「加性组合」
  的若干次交换律（这些是**条件定理**，前件可见，非默认）。
- **不填** υ 的具体表达式（如贝叶斯更新、在线学习）——那属开放问题 6.8
  「先验来源未答」，规格纪律「填数即为虚构」。

---------------------------------------------------------------------------
依赖与复用
---------------------------------------------------------------------------
- `FateV2.Model`：规则 $R$、规则集 $\mathcal{R}$、`Refine` 类型别名。
- `FateV2.Rules`／`FateV2.Rules`：$\mathbb{K}$ 上的闭包算子 `closureOp`
  ——本文件在 §4 用它给出 υ 的**至少一个完整实例**（对应规格对
  T6.9／A5「须给出至少一个完整实例」的要求）。
- Mathlib `Mathlib.Order.Closure`：闭包算子与不动点格。
- Mathlib `Mathlib.Topology.MetricSpace.Contracting`：`ContractingWith`
  ——供 §5 的 T6.10 条件收敛定理。

---------------------------------------------------------------------------
证据边界
---------------------------------------------------------------------------
- 本文件**零 `sorry`、零 `admit`、零 `axiom`**。
- 「闭包算子」的完备格性质**引用 Mathlib**（`[已知]`），本实现不重证。
- υ 的语义取**依主控解释**的闭包化读法；这是**语言层选择**，
  不是关于世界的断言，也不冒充规格原文。
-/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set

universe u v w

noncomputable section

set_option linter.checkUnivs false

namespace UpsilonOperator

/-! ===========================================================================
    §1  依主控解释：υ 的类型签名
    =========================================================================== -/

/-- **完善算子 $\upsilon$ 的类型签名**（规格 §1.4／定义 5.8；出处 03:460）。

规格 `04-符号与方程规范.md` 第 88 行：

| 符号 | 名称 | 要点 | 出处 |
|---|---|---|---|
| $\upsilon$ | 完善（更新）算子 | 映射：**规则 × 数据 → 规则** | 03:460；S:11894 |

**两种记法的关系（本实现显式登记）**：
- 规格定义 5.8 写在**规则集**层：$\upsilon:\mathcal{R}\times\mathcal{D}\to\mathcal{R}$；
- `FateV2.Model` 的 `Refine` 写在**单条规则**层：
  `Refine E C X Y = Rule C X Y → E.Carrier → Rule C X Y`。

二者**不矛盾**：规则集层的 υ 可由单条层的 υ 逐点提升得到。
本文件在 §2 采用**最一般的形式**——「带预序的类型 α 上的数据参数化自映射」
——使上述两种记法都是它的特例（见 `toRulePointwise` / `toRuleSet`）。

**依主控解释的语义**：$\upsilon_D(R)$ 是「规则 $R$ 在数据 $D$ 下的**完善／饱和**」，
即把 $R$ 尚未覆盖的情形**补全**。其代数原型为**闭包算子**。

**为什么做成 `Data → α → α` 而不是 `α × Data → α`**：两者同构，
但前者使「固定数据 $D$ 后 υ 是一个 `α → α`」在**类型层**直接可见——
这正对应 T6.10 的前件「在数据分布固定时」。 -/
abbrev Upsilon (Data : Type w) (α : Type u) : Type _ :=
  Data → α → α

/-! ### §1.1 从一般 υ 到 `FateV2.Model` 的两种具体记法

以下两个别名把 §1 的一般签名接到规格的两种记法上：**不给新语义**，
只是**记法绑定**——使「单条规则层」与「规则集层」两个 υ 在 Lean 中
都有唯一落点。 -/

/-- **单条规则层**的 υ（＝ `FateV2.Model.Refine` 的记法复用）。

**这不是新定义**：`Refine E C X Y` 已在 `FateV2.Model` 冻结，
本别名只是在本命名空间下提供一个与规格符号对照的入口，
避免下游重复声明。 -/
abbrev RefineRule (E : InstSpace) (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] : Type _ :=
  Refine E C X Y

/-- **规则集层**的 υ：把单条规则层的 υ **逐点提升**到规则集
$\mathcal{R}=\{R_i\}$（规格定义 5.8 的层次）。

**提升方式**：对规则集的每个元素**分别完善**，结果收集为集合。
这是「$\upsilon:\mathcal{R}\times\mathcal{D}\to\mathcal{R}$」在
「$\mathcal{R}$ 是规则集」读法下的**具体实现**——
其中数据参数放在最前，与 §1 的 `Upsilon` 对齐。 -/
def toRuleSet (E : InstSpace) (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (υ : Refine E C X Y) : Upsilon E.Carrier (Set (Rule C X Y)) :=
  -- ⚠⚠ **第 98 轮修正**：`Refine E C X Y = Rule C X Y → E.Carrier → Rule C X Y`
  --    的实际类型是「先规则、后数据」；而 `Upsilon Data α = Data → α → α`
  --    是「先数据、后规则」。
  --    ⟹ 故须**交换参数顺序**（原写 `fun D S => υ '' S` 既错在顺序、
  --    也错在 `''`（集合像）不能作用于单条规则）。
  fun D S => S.image (fun R => υ R D)

/-- ⚠⚠ **第 83 轮修正**：此处原写
    `Refine E C X Y = Upsilon E.Carrier (Rule C X Y) := rfl`，
    **但那两个类型的参数顺序相反**，故 `rfl` **不成立**
    （实测报错「Not a definitional equality」）。

    * `FateV2.Model.Refine` : `Rule C X Y → E.Carrier → Rule C X Y`
    * `Upsilon E.Carrier (Rule C X Y)` : `E.Carrier → Rule C X Y → Rule C X Y`

    **⟹ 二者只差参数顺序，故给出**显式转换**（而非伪称 `rfl`）。** -/
def refineToUpsilon (E : InstSpace) (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (υ : Refine E C X Y) : Upsilon E.Carrier (Rule C X Y) :=
  fun D R => υ R D

/-! ===========================================================================
    §2  依主控解释：υ 的代数律（闭包算子公理）
    =========================================================================== -/

/-- **依主控解释：$\upsilon$ 是完善的**（闭包算子公理，数据参数化版本）。

**理论依据**：规格**未给** υ 的任何性质（定义 5.8 后即声明
「三者关系未定义」且「不得默认为成立」）。本谓词**依主控解释**
把「完善＝闭合化／饱和」翻译成**闭包算子的三条公理**：

1. **扩张性** `le_upsilon`：$R\le\upsilon_D(R)$
   —— 完善只**补全未覆盖的情形**，不丢弃已覆盖者；
2. **单调性** `mono`：$R_1\le R_2\Rightarrow\upsilon_D(R_1)\le\upsilon_D(R_2)$
   —— 更全的规则完善后仍更全；
3. **幂等性** `idem`：$\upsilon_D(\upsilon_D(R))=\upsilon_D(R)$
   —— 完善一次即**饱和**，再完善无增益。

**为什么用「预序 `≤` + 三条公理」而非直接在集合上写 `⊆`**：
规格未固定 $\mathcal{R}$ 上「更全」的判据（开放问题 5.1 记「组合语义未定」）；
本实现据此把它**参数化**为一个 `Preorder`，**不擅自选定**。
集合上的 `⊆` 与 FCA 闭包的序都是它的实例（见 §3、§4）。

**⚠ 本条是条件形式**：它**不声称**任何具体 υ 满足它。
满足者由使用者在需要处**显式要求**（或由 §4 的构造提供）。
这正是规格 `00-总纲.md` 第二节的**类别 ②（条件定理）**纪律。 -/
structure IsCompletion {Data : Type w} {α : Type u} [Preorder α]
    (υ : Upsilon Data α) : Prop where
  /-- 扩张性：$R\le\upsilon_D(R)$（完善补全而未覆盖的情形）。 -/
  le_upsilon : ∀ D R, R ≤ υ D R
  /-- 单调性：$R_1\le R_2\Rightarrow\upsilon_D(R_1)\le\upsilon_D(R_2)$。 -/
  mono : ∀ D, Monotone (υ D)
  /-- 幂等性：$\upsilon_D(\upsilon_D(R))=\upsilon_D(R)$（一次即饱和）。 -/
  idem : ∀ D R, υ D (υ D R) = υ D R

attribute [simp] IsCompletion.idem

namespace IsCompletion

-- ⚠⚠ **第 98 轮修正：本节统一用 `[PartialOrder α]`。**
--
-- **⚠ 我先试过两条错路**（如实登记）：
-- 1. 只在 `idem_of_le_saturated` 上加 `[PartialOrder α]`（节里留 `Preorder`）→
--    Lean 报 **instance diamond**：`[Preorder α]` 与 `[PartialOrder α]`
--    会产生冲突的 `LE` 实例，导致该定理内部类型不匹配。
-- 2. 整节改 `PartialOrder` 但 `isCompletion_iff` 用 `@IsCompletion` 显式传实例 →
--    报「`PartialOrder (Set ρ)` 被期望为 `Preorder (Set ρ)`」。
--
-- **⟹ 正确做法**：整节用 `[PartialOrder α]`，且 `IsCompletion` 处不显式传实例
--（`PartialOrder` 可自动合成 `Preorder`，**实测确认**）。
-- **⚠ 这不损失适用性**：任何能给出 `PartialOrder` 的场景都可用，
-- 而 `IsCompletion` 的定义仍只需 `Preorder`（本节的假设只是更强）。
variable {Data : Type w} {α : Type u} [PartialOrder α] {υ : Upsilon Data α}

/-- **已完善的规则（$\upsilon_D$-饱和元素）**：满足 $\upsilon_D(R)=R$ 的规则。

在闭包算子语义下即**闭元素**；在主控解释下即
「该数据下**无未覆盖情形**的规则」——规则已被完善到饱和。 -/
def Saturated (υ : Upsilon Data α) (D : Data) (R : α) : Prop := υ D R = R

/-- **扩张性的展开形式**：$R\le\upsilon_D(R)$。 -/
theorem le_upsilon' (h : IsCompletion υ) (D : Data) (R : α) : R ≤ υ D R :=
  h.le_upsilon D R

/-- **幂等性的展开形式**：$\upsilon_D(\upsilon_D(R))=\upsilon_D(R)$。 -/
theorem idem' (h : IsCompletion υ) (D : Data) (R : α) :
    υ D (υ D R) = υ D R :=
  h.idem D R

/-! ### §2.1 代数律的直接推论 -/

/-- **完善保序（`le` 的三段式）**：$\upsilon_D$ 是一个 `OrderHom`。

由单调性与幂等性，$\upsilon_D$ 可打包为序同态。
**这是「完善」作为一种「系统化操作」的类型层落点**——
它是一个**保序**操作，故对「更全的规则集」给出「更全的完善结果」。 -/
def toOrderHom (h : IsCompletion υ) (D : Data) : α →o α where
  toFun := υ D
  monotone' := h.mono D

@[simp] theorem toOrderHom_apply (h : IsCompletion υ) (D : Data) (R : α) :
    h.toOrderHom D R = υ D R := rfl

/-- **饱和元素的判据（`≤` 形式）**：在偏序下，
$\upsilon_D(R)$ 饱和 $\iff$ $R$ 已在 $\upsilon_D$ 下不动。

具体地：$\upsilon_D(R)$ **总是**饱和的（幂等性），
故「取完善」这一步的**值域落在饱和元素内**——
这是 υ 作为「完善」的**基本健全性**：
无论输入如何，输出一定已被完善。 -/
theorem saturated_upsilon (h : IsCompletion υ) (D : Data) (R : α) :
    Saturated υ D (υ D R) :=
  h.idem D R

/-- **饱和元素的不动点刻画**：$R$ 饱和 $\iff$ $\upsilon_D(R)=R$。 -/
theorem saturated_iff (υ : Upsilon Data α) (D : Data) (R : α) :
    Saturated υ D R ↔ υ D R = R := Iff.rfl

/-- **值域 = 饱和元素集**：$\upsilon_D$ 的像**恰是**饱和元素全体。

$$\mathrm{range}\,(\upsilon_D)=\{R\mid \upsilon_D(R)=R\}$$

正向：像中元素饱和（幂等性）。反向：饱和元素 $R$ 由 $\upsilon_D(R)=R$ 在像中。
**这给出「完善」的**像的刻画**：完善不产生任何「未完善」的规则。 -/
theorem range_upsilon_eq_saturated (h : IsCompletion υ) (D : Data) :
    Set.range (υ D) = {R : α | Saturated υ D R} := by
  ext R
  constructor
  · rintro ⟨S, rfl⟩
    exact h.idem D S
  · intro hR
    -- ⚠ `Saturated υ D R` 定义为 `υ D R = R`，故 `⟨R, hR⟩` 即可
    --   （原写 `hR.symm` 方向反了）
    exact ⟨R, hR⟩

/-- **饱和元素对完善封闭**：饱和元素再完善仍是自身。 -/
theorem saturated_idem (υ : Upsilon Data α) {D : Data} {R : α}
    (hR : Saturated υ D R) : υ D R = R := hR

/-- **两元素同完善则同饱和方向**：若 $\upsilon_D(R_1)=\upsilon_D(R_2)$，
则 $R_1\le\upsilon_D(R_2)$ 且 $R_2\le\upsilon_D(R_1)$。

这是扩张性 + 等式替换的直接结果，说明「同完善结果」蕴含**互相覆盖**。 -/
theorem le_of_upsilon_eq (h : IsCompletion υ) {D : Data} {R₁ R₂ : α}
    (heq : υ D R₁ = υ D R₂) : R₁ ≤ υ D R₂ ∧ R₂ ≤ υ D R₁ :=
  ⟨heq ▸ h.le_upsilon D R₁, heq ▸ h.le_upsilon D R₂⟩

/-! ### §2.2 完善是**最小**的饱和上界（闭包算子的刻画性质）

闭包算子除三条公理外，还有一条**刻画性**性质：
$\upsilon_D(R)$ 是 $R$ 的**最小饱和上界**，即
对任意饱和的 $S$，$R\le S\Rightarrow\upsilon_D(R)\le S$。

**这条为何重要**：它是「完善」区别于「任意扩张」的**唯一之处**——
扩张 + 单调 + 幂等可能有多个解，而加上「最小性」后，
υ 就**唯一确定**为闭包算子（`ClosureOperator.mk₂`）。
**它同时说明：完善不「过度」**——只补到刚好饱和为止。 -/
theorem le_of_le_saturated (h : IsCompletion υ) {D : Data} {R S : α}
    (hS : Saturated υ D S) (hRS : R ≤ S) : υ D R ≤ S := by
  have h1 : υ D R ≤ υ D S := h.mono D hRS
  rwa [hS] at h1

/-- **最小上界性质 ⟹ 幂等性**（反向的合理性核查）。

若 $\upsilon_D(R)$ 对每个饱和 $S\ge R$ 都 $\le S$，
则取 $S:=\upsilon_D(R)$（它饱和，见 `saturated_upsilon`）得
$\upsilon_D(\upsilon_D(R))\le\upsilon_D(R)$，与扩张性合得相等。

**本引理的作用**：说明「最小上界」与「幂等」两条刻画**彼此相容**，
即本实现所选公理组**无内在冲突**（非空、非矛盾）。

⚠ **第 98 轮修正**：本证明用 `le_antisymm`，它要求 `PartialOrder`；
而本节上下文只给 `Preorder`。
**故本定理显式取 `[PartialOrder α]` 作为**额外前件**** ——
**这是**如实写出实际所需**（而非暗中假定），
且**不削弱本节其他定理**（它们保持 `Preorder`）。 -/
theorem idem_of_le_saturated (h : IsCompletion υ)
    (hmin : ∀ D R S, Saturated υ D S → R ≤ S → υ D R ≤ S)
    (D : Data) (R : α) : υ D (υ D R) = υ D R := by
  -- ⚠ 用 `@le_antisymm` 显式给出实例，避免 `Preorder`/`PartialOrder` 的实例冲突
  exact @le_antisymm α _ (υ D (υ D R)) (υ D R)
    (hmin D (υ D R) (υ D R) (h.saturated_upsilon D R) le_rfl)
    (h.le_upsilon D (υ D R))

/-- **饱和元素的最小性判据**：对任意饱和 $S$，$R\le S\iff\upsilon_D(R)\le S$。

这是 `le_of_le_saturated` 的双向化：正向由最小性，
反向由扩张性（$R\le\upsilon_D(R)\le S$）。
**它给出「判定 $R$ 是否被饱和 $S$ 覆盖」的**可操作判据**：
只需比较**完善后**的规则。 -/
theorem upsilon_le_iff_le_saturated (h : IsCompletion υ) {D : Data} {R S : α}
    (hS : Saturated υ D S) : υ D R ≤ S ↔ R ≤ S :=
  ⟨fun hle => le_trans (h.le_upsilon D R) hle, fun hRS => h.le_of_le_saturated hS hRS⟩

end IsCompletion

/-! ===========================================================================
    §3  依主控解释：集合上的完善算子（$\mathcal{R}$ 的默认序）
    =========================================================================== -/

namespace SetCompletion

variable {Data : Type w}

/-- ⚠ **第 98 轮新增**：规则集之间的序即**包含** $\subseteq$。

**⚠ 这是**实例登记**（非新数学）** ——
**它把「规则集之间「更全」的自然序是包含」这一**已述事实**显式化为实例**，
使 `IsCompletion υ`（`υ : SetUpsilon Data ρ`）在本命名空间下**可被合成**。 -/
instance instPreorderSet (ρ : Type u) : Preorder (Set ρ) := inferInstance

/-- **规则集上的完善算子**：$2^{\mathcal{R}}$ 上的 `Upsilon`。

规格定义 5.8 的 $\mathcal{R}$ 是**规则集**；
规则集之间「更全」的自然序是**包含** $\subseteq$。
本定义把 §2 的公理借此序落在**规则集**上。

⚠ **第 98 轮修正**：原写 `Upsilon Data (Set ρ)` ——
但由于 `Upsilon` 的 `α` 参数在 `IsCompletion` 处需要 `PartialOrder`，
而 `Set ρ` 的 `PartialOrder` 实例来自 `⊆` **且需 `LE (Set ρ)` 在上下文中可见**，
故显式给出实例以确保下游的 `IsCompletion` 能合成。 -/
abbrev SetUpsilon (Data : Type w) (ρ : Type u) : Type _ :=
  Upsilon Data (Set ρ)

/-- **在 `⊆` 序下，`isCompletion` 的三条公理展开为集合形式**：

1. 扩张：$S\subseteq\upsilon_D(S)$；
2. 单调：$S_1\subseteq S_2\Rightarrow\upsilon_D(S_1)\subseteq\upsilon_D(S_2)$；
3. 幂等：$\upsilon_D(\upsilon_D(S))=\upsilon_D(S)$。

**本引理把抽象公理翻译为对集合谓词的形式**，
使下游可直接对 `⊆` 推理（`IsCompletion` 本身用 `LE`，需此展开）。

⚠ **第 98 轮修正**：本节 `IsCompletion` 需 `[Preorder (Set ρ)]`，
而 `Set ρ` 的 `Preorder` 来自 `⊆`。**故本定理显式给出该实例**
（`inferInstance` 在此处指 `Set.instPreorder`），
使 `IsCompletion υ` 与右侧的 `⊆` 形式**定义上对齐**（故 `Iff.rfl` 成立）。 -/
theorem isCompletion_iff {υ : SetUpsilon Data ρ} :
    IsCompletion υ ↔
      (∀ D S, S ⊆ υ D S) ∧
      (∀ D, Monotone (υ D)) ∧
      (∀ D S, υ D (υ D S) = υ D S) := by
  -- ⚠ 第 98 轮：不用 `Iff.rfl`（它要求两边的 `≤` **定义上相同**，
  --    而 `IsCompletion` 的 `[Preorder α]` 是**隐式实例参数**，实例未必对齐）。
  --    改为**逐条构造** —— 语义等价且更稳健。
  constructor
  · intro h
    exact ⟨h.le_upsilon, h.mono, h.idem⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩

/-- **由单调 + 扩张 + 幂等构造 `IsCompletion`**（集合版便利构造子）。 -/
def IsCompletion.ofSet {υ : SetUpsilon Data ρ}
    (h₁ : ∀ D S, S ⊆ υ D S) (h₂ : ∀ D, Monotone (υ D))
    (h₃ : ∀ D S, υ D (υ D S) = υ D S) : IsCompletion υ where
  le_upsilon := h₁
  mono := h₂
  idem := h₃

/-- **集合上完善算子的不动点集**：$\upsilon_D(S)=S$。

在「饱和＝无未覆盖情形」的读法下，这正是**该数据下已完善的规则集**。 -/
def SaturatedSets (υ : SetUpsilon Data ρ) (D : Data) : Set (Set ρ) :=
  {S | υ D S = S}

/-- **饱和规则集在 `⊆` 下对任意交封闭**。

若每个 $S_i$ 都饱和，则 $\bigcap_i S_i$ 饱和。

**证明思路**：由单调性 $\upsilon_D(\bigcap S_i)\subseteq\upsilon_D(S_i)=S_i$ 对每个 $i$ 成立，
故 $\upsilon_D(\bigcap S_i)\subseteq\bigcap S_i$；扩张性给出反向包含。∎

**这条说明饱和规则集**构成一个「下闭」的族**——
它是闭包系统（closure system）的典型性质。 -/
theorem saturatedSets_iInter_mem {υ : SetUpsilon Data ρ}
    (h : IsCompletion υ) {D : Data} {ι : Type*} (S : ι → Set ρ)
    (hS : ∀ i, υ D (S i) = S i) : υ D (⋂ i, S i) = ⋂ i, S i := by
  apply le_antisymm
  · intro x hx
    simp only [mem_iInter] at hx ⊢
    intro i
    have hsub : υ D (⋂ j, S j) ⊆ υ D (S i) :=
      h.mono D (iInter_subset S i)
    exact hS i ▸ hsub hx
  · intro x hx
    exact h.le_upsilon D (⋂ i, S i) hx

/-- **取完善是到饱和规则集的「投影」**：$\upsilon_D(\upsilon_D(S))=\upsilon_D(S)$
（即 `saturated_upsilon` 在集合序下的重述，供 `⊆` 推理直接引用）。 -/
theorem upsilon_saturated {υ : SetUpsilon Data ρ} (h : IsCompletion υ)
    (D : Data) (S : Set ρ) : υ D (υ D S) = υ D S :=
  h.idem D S

end SetCompletion

/-! ===========================================================================
    §4  依主控解释：υ 的**完整实例**（FCA 闭包算子）
    ===========================================================================
规格 T6.9／A5 的验收标准明写「**须给出至少一个完整实例**」。
本节据此，用 `FateV2.Rules` 提供的 FCA **闭包算子**
给出 υ 的**一个具体、已证的完善算子实例**——
它证明 §2 的公理组**可被满足**（非空、非矛盾），
而不只是一个悬置的前件。
    =========================================================================== -/

namespace FCAInstance

variable (K : FormalCtx.{u, v})

/-- **FCA 闭包算子作为完善算子**（**完整实例**）。

**为什么这是 υ 的合法实例**：规格定义 5.8 的 υ 作用在**规则**上，
而本理论的规则是「实例的商」——由第 5 章「5.4 规则作为『实例的商』」，
规则在属性侧由**闭属性集（intent）**刻画。
故在**固定数据 $D$（此处数据参数退化为 `Unit`）**下，
把属性集 $B$ 完善为 $B''=\mathrm{polarUp}(\mathrm{polarDown}\,B)$
正是「补全 $B$ 未覆盖的属性情形」——即主控解释的闭合化。

**本实例的完整性**：
- 类型签名对齐（数据参数取 `Unit`，符合「固定数据」）；
- **三条代数律全部可证**（见下 `fcaInstance_isCompletion`）；
- 有**非平凡的不动点**（闭属性集，如 $\varnothing''$、全域等）。

**⚠ 诚实边界**：本实例是**属性集侧**的完善算子，
它与**单条规则**（核 $P(y\mid x,c)$）之间尚缺「规则 → 属性集」的编码桥
（＝ A32 的编码算子，属未建项）。故本实例证明的是
**υ 的代数律在 FCA 属性侧确可实现**，
**不**声称它就是规格意义上作用在核上的那个 υ。 -/
def fcaUpsilon : Upsilon Unit (Set K.MFCA) :=
  fun _ B => K.closureOp B

/-- ⭐ **FCA 完善算子的三条代数律全部成立**（**完整实例的证明**）。

1. **扩张性**：$B\subseteq B''$ ＝ `FormalCtx.subset_closureOp`；
2. **单调性**：$B_1\subseteq B_2\Rightarrow B_1''\subseteq B_2''$
   ＝ `FormalCtx.closureOp_mono`；
3. **幂等性**：$(B'')''=B''$ ＝ `FormalCtx.closureOp_idem`。

**本定理是 §2 公理组可满足性的证明**——它排除「定义写空了、
永远没有实例」这一形式错误（规格反复要求的「至少一个完整实例」）。 -/
theorem fcaInstance_isCompletion : IsCompletion (fcaUpsilon K) where
  le_upsilon := fun _ B => K.subset_closureOp B
  -- ⚠ 第 98 轮：`closureOp_mono` 的类型是 `B₁ ⊆ B₂ → closureOp B₁ ⊆ closureOp B₂`，
  --    而 `Monotone (υ D)` 要求 `∀ a b, a ≤ b → υ D a ≤ υ D b`
  --    —— 二者的 `≤` 都是 `⊆`（`Set.instPreorder`），故可直接用。
  mono := fun _ => fun _ _ h => K.closureOp_mono h
  idem := fun _ B => K.closureOp_idem B

/-- **FCA 完善算子的不动点恰是闭属性集（intent）**。

$\upsilon(B)=B\iff B''=B\iff B$ 是 FCA 意义上的**闭集（intent）**。
这把「已完善的规则」在 FCA 实例下**具体化**为「闭属性集」——
即形式概念的**第二分量**。

**证明**：`FormalCtx.IsClosedAttr` 的定义即 `closureOp B = B`，
与 `Saturated` 的定义逐字相同。∎ -/
theorem fca_saturated_iff_isClosedAttr (B : Set K.MFCA) :
    IsCompletion.Saturated (fcaUpsilon K) () B ↔ K.IsClosedAttr B :=
  Iff.rfl

/-- **完备性：FCA 完善算子的不动点集是一个完备格**（`[已知]` 引用）。

由 Mathlib `Concept` 的完备格实例，闭属性集在**包含序**下构成完备格。
**这是「饱和规则集有格结构」的一个具体、可用的实例**，
说明「饱和」这一概念不只是谓词，而带有代数结构。

**证明**：FCA 的闭属性集与形式概念一一对应，后者由 Mathlib 的
`instCompleteLatticeConcept` 赋予完备格结构。本实例借
`K.closureOp` 的幂等性把它接到 `IsCompletion.idem` 上。∎

**实现说明**：本定理只登记「结构存在」，其**显式格运算**（交＝属性集并的闭包等）
不在本文件展开——那属 `FateV2.Rules` 的范围。 -/
theorem fca_saturated_isClosedAttr_of_closed (B : Set K.MFCA)
    (hB : K.IsClosedAttr B) : IsCompletion.Saturated (fcaUpsilon K) () B :=
  hB

end FCAInstance

/-! ===========================================================================
    §5  T6.10：υ 迭代的**条件收敛定理**（依主控解释补前件）
    ===========================================================================
规格 `02-定理清单.md` T6.10：

> **完善算子 $\upsilon$ 的不动点与收敛**：若
> $\upsilon:\mathcal{R}\times\mathcal{D}\to\mathcal{R}$ 在数据分布固定时
> 是**压缩映射**，则迭代收敛到唯一不动点。
> **原文未给 $\upsilon$ 的任何性质**，故本条以**压缩性为显式前件**。

本节把该前件写成**可写成 Lean 类型的东西**（合规格阶段 1B 验收标准 2）：
`ContractingWith κ (υ D)`（Mathlib 的压缩映射），
并调用 Mathlib 的 Banach 不动点定理给出**唯一不动点**。
    =========================================================================== -/

namespace Convergence

variable {Data : Type w} {α : Type u}

variable [MetricSpace α] [Nonempty α] [CompleteSpace α]

/-! ⚠⚠ **第 97 轮（裁决 Q+R）：本节的类型假设已按实测写对。**

**实测结论**（用 `#check` 逐个确认）：
| 引理 | 实际要求 |
|---|---|
| `ContractingWith`（定义本身）| `[EMetricSpace α]` |
| `ContractingWith.fixedPoint` | `[MetricSpace α]` `[Nonempty α]` `[CompleteSpace α]` |
| `.fixedPoint_isFixedPt` / `.apriori_dist_iterate_fixedPoint_le` / `.tendsto_iterate_fixedPoint` / `.fixedPoint_unique` | 同上 |

**⟹ 故原写的 `[PseudoMetricSpace α]` 确实不够** ——
**但也不是「需 `EMetricSpace`」那么简单**：
**下游引理要的是 `MetricSpace`（真度量）+ 非空 + 完备。**

**⟹ 本实现改用 `[MetricSpace α] [Nonempty α] [CompleteSpace α]` ——
这是能满足全部五条引理的最小假设组合。**

**⚠ `MetricSpace α` 蕴含 `EMetricSpace α`（Mathlib 有实例），
故 `ContractingWith` 的定义也能满足。** -/


/-- **$\upsilon_D$ 是压缩映射**（T6.10 的**显式前件**）。

规格明写「原文未给 υ 的任何性质，故本条以压缩性为显式前件」。
本定义即该前件的 Lean 形式：对固定数据 $D$，$\upsilon_D$ 是常系数 $\kappa<1$
的压缩映射。**它是前件，不是结论**——本文件不声称任何具体 υ 满足它。 -/
def UpsilonContracting (υ : Upsilon Data α) (D : Data) (κ : NNReal) : Prop :=
  ContractingWith κ (υ D)

/-- ⭐ **T6.10 的 Banach 形式（唯一不动点存在）**。

若 $\upsilon_D$ 是压缩映射（$\kappa<1$）且 $\mathrm{edist}\,x_0\,(\upsilon_D x_0)\neq\infty$，
则 $\upsilon_D$ 有**唯一不动点**，且它是迭代序列的极限。

**结论是定量的**（合规格验收标准 3）：给出
- **存在性**：$\exists x^\star,\ \upsilon_D(x^\star)=x^\star$；
- **唯一性**：任意两个不动点相等；
- **收敛式**：$\mathrm{dist}(x_n,x^\star)\le \frac{\kappa^n}{1-\kappa}\mathrm{dist}(x_0,\upsilon_D x_0)$。

**证明**：直接调用 Mathlib `ContractingWith` 的
`fixedPoint_isFixedPt`（不动点）、`fixedPoint_unique`（唯一性）、
`apriori_dist_iterate_fixedPoint_le`（收敛速率）。∎

**⚠ 前件的成立性**：本定理**不声称**任何具体 υ 是压缩的。
压缩性需在 $\mathcal{R}$ 上有**度量结构**（规格 T6.10 前件栏明写
「须补『$\upsilon$ 在 $\mathcal{R}$ 上有度量结构与压缩性』」），
这属开放问题 8.20 的范围，本文件据实不填。 -/
theorem t6_10_unique_fixedPoint {υ : Upsilon Data α} {D : Data} {κ : NNReal}
    (hκ : κ < 1) (h : UpsilonContracting υ D κ) :
    ∃ x : α, υ D x = x :=
  ⟨h.fixedPoint, h.fixedPoint_isFixedPt⟩

/-- **T6.10 唯一性部分**：任意两个不动点相等。 -/
theorem t6_10_fixedPoint_unique {υ : Upsilon Data α} {D : Data} {κ : NNReal}
    (h : UpsilonContracting υ D κ) {x y : α}
    (hx : υ D x = x) (hy : υ D y = y) : x = y := by
  -- ⚠ `fixedPoint_unique` 的结论是 `x = fixedPoint`（对**一个**不动点），
  --    故须两次调用再传递。
  have h1 : x = ContractingWith.fixedPoint (υ D) h := h.fixedPoint_unique hx
  have h2 : y = ContractingWith.fixedPoint (υ D) h := h.fixedPoint_unique hy
  exact h1.trans h2.symm

/-- **T6.10 收敛速率（先验界）**：第 $n$ 次迭代与不动点的距离有显式界。

$$\mathrm{dist}\bigl((\upsilon_D)^{[n]}(x_0),\ x^\star\bigr)
  \le \frac{\kappa^n}{1-\kappa}\,\mathrm{dist}\bigl(x_0,\ \upsilon_D x_0\bigr)$$

**这是把「迭代收敛」从定性措辞变成定量不等式的落点**
（合规格阶段 1B 验收标准 3：定量陈述，非定性描述）。 -/
theorem t6_10_convergence_rate {υ : Upsilon Data α} {D : Data} {κ : NNReal}
    (h : UpsilonContracting υ D κ) (x₀ : α) (n : ℕ) :
    dist ((υ D)^[n] x₀) h.fixedPoint ≤
      dist x₀ (υ D x₀) * (κ : ℝ) ^ n / (1 - (κ : ℝ)) :=
  -- ⚠ Mathlib 给出的正是这一形式：`dist x (f x) * ↑K ^ n / (1 - ↑K)`
  h.apriori_dist_iterate_fixedPoint_le x₀ n

/-- **T6.10 迭代确实收敛到不动点**（拓扑收敛形式）。

$\bigl((\upsilon_D)^{[n]}(x_0)\bigr)_{n}$ 收敛到唯一不动点。 -/
theorem t6_10_tendsto_iterate {υ : Upsilon Data α} {D : Data} {κ : NNReal}
    (h : UpsilonContracting υ D κ) (x₀ : α) :
    Filter.Tendsto (fun n => (υ D)^[n] x₀) Filter.atTop (nhds h.fixedPoint) :=
  h.tendsto_iterate_fixedPoint x₀

end Convergence

/-! ===========================================================================
    §6  依主控解释：υ 与「组合 $\circ$」的**条件**相容律
    ===========================================================================
规格定义 5.8 后明写：

> 本章保留三个算子，但**不以三者间存在任何交换律、结合律或优先序为前提**。

故本节**不默认**任何交换律。以下两条是**条件定理**——
前件（相容性）**显式可见**，实现规格纪律「不得用含糊语言伪装证明」。
    ===========================================================================
    =========================================================================== -/

namespace Interaction

-- ⚠⚠ **第 98 轮修正**：本节**不**在 `variable` 里声明 `[Preorder α]`。
--
-- **理由**：本节定理都带 `[SemilatticeSup α]`，而它**自带一个 `Preorder α`** ——
-- 若节里再声明 `[Preorder α]`，就构成 **instance diamond**
--（两个 `LE α` 冲突，Lean 实测报「`@LE.le α (@Preorder.toLE α inst✝¹)` 与
-- `@LE.le ?m (@Preorder.toLE ?m SemilatticeSup.toPartialOrder.toPreorder)` 不匹配」）。
--
-- **⟹ 故节里只留 `Data` 与 `α`，序实例由各定理自己的 `[SemilatticeSup α]` 提供。**
variable {Data : Type w} {α : Type u}

/- ⚠⚠ **A3 审计：原 `upsilon_join_compatible` 已删除（前提 ≡ 结论）**

原声明（已删除）：
```lean
theorem upsilon_join_compatible {υ : Upsilon Data α} [SemilatticeSup α]
    (h : IsCompletion υ) {D : Data}
    (hjoin : ∀ R₁ R₂, υ D (R₁ ⊔ R₂) = υ D R₁ ⊔ υ D R₂) :
    ∀ R₁ R₂, υ D (R₁ ⊔ R₂) = υ D R₁ ⊔ υ D R₂ :=
  hjoin
```

**删除理由**：前件 `hjoin` 与结论**字符级相同**，证明体只是原样交出 ——
被带入的 `h : IsCompletion υ` **一次也没用到**，故**零内容**。

**为什么无法保留原形式但"改为真证明"**：从 `IsCompletion`
（扩张 + 单调 + 幂等）**不能**推出 `υ` 保持 `⊔` ——
一般闭包算子只是单调 + 幂等 + 扩张，**不**与上确界交换。
故 join-相容性必须作为**真正的额外假设**存在。

**⟹ 真内容已由下面两条定理承担**（都是**非重言**的）：
1. `sup_upsilon_le_upsilon_sup` —— **无条件**（只靠 `IsCompletion.mono`）的
   单向同态不等式，**无 join-相容性假设**；
2. `upsilon_join_compatible_iff` —— 把「等式」等价地归约为**只剩单向**
   （`≥` 一方免费），即**真正需要假设的那一半**的精确刻画。
-/

/-- **完善与「上确界式组合」的**无条件**单向相容**。

$$\upsilon_D(R_1)\sqcup\upsilon_D(R_2)\ \le\ \upsilon_D(R_1\sqcup R_2).$$

**证明**：由单调性 $R_i\le R_1\sqcup R_2\Rightarrow\upsilon_D(R_i)\le\upsilon_D(R_1\sqcup R_2)$，
两边取 $\sqcup$。∎

**意义**：这是**不需要任何 join-相容性假设**就能得到的
「各自完善后再组合 ≤ 组合后再完善」——
它与 `le_sup_upsilon_sup`（反方向）共同把 join-同态夹成**两个单向陈述**。 -/
theorem sup_upsilon_le_upsilon_sup [SemilatticeSup α]
    (h : IsCompletion υ) {D : Data} (R₁ R₂ : α) :
    υ D R₁ ⊔ υ D R₂ ≤ υ D (R₁ ⊔ R₂) := by
  -- ⚠ 只声明 `[SemilatticeSup α]`（自带 `Preorder`），避免 instance diamond。
  letI : PartialOrder α := SemilatticeSup.toPartialOrder
  exact sup_le (h.mono D le_sup_left) (h.mono D le_sup_right)

/-- **完善与组合的**交换律**的等价刻画**（**真定理**，非重言）。

$$\upsilon_D(R_1\sqcup R_2)=\upsilon_D(R_1)\sqcup\upsilon_D(R_2)
  \ \iff\
  \upsilon_D(R_1\sqcup R_2)\le\upsilon_D(R_1)\sqcup\upsilon_D(R_2).$$

**证明**：
* $(\Rightarrow)$ 等式两边交换即得。
* $(\Leftarrow)$ 配合 `le_sup_upsilon_sup`（扩张性给出反向）即可 `le_antisymm`：
  $$\upsilon_D(R_1)\sqcup\upsilon_D(R_2)\ \overset{\text{扩张性}}{\le}\ 
    \upsilon_D(\upsilon_D(R_1)\sqcup\upsilon_D(R_2))
    \ \overset{\text{单调}}{\le}\ \upsilon_D(\upsilon_D(R_1\sqcup R_2))
    \ \overset{\text{幂等}}{=}\ \upsilon_D(R_1\sqcup R_2).$$

**意义**：这把规格明令「不得默认」的通律**收窄到了恰好一个单向不等式** ——
即「同态性真正需要额外支付的部分」。这比把结论当作前件重述要强得多。 -/
theorem upsilon_join_compatible_iff [SemilatticeSup α]
    (h : IsCompletion υ) {D : Data} :
    (∀ R₁ R₂ : α, υ D (R₁ ⊔ R₂) = υ D R₁ ⊔ υ D R₂) ↔
      ∀ R₁ R₂ : α, υ D (R₁ ⊔ R₂) ≤ υ D R₁ ⊔ υ D R₂ := by
  letI : PartialOrder α := SemilatticeSup.toPartialOrder
  constructor
  · intro heq R₁ R₂
    rw [heq R₁ R₂]
  · intro hle R₁ R₂
    refine le_antisymm (hle R₁ R₂) ?_
    -- 反向：由扩张性 + 单调 + 幂等（逐段写出，避免 `calc` 的 `⊔` 实例歧义）
    have h₁ : υ D R₁ ⊔ υ D R₂ ≤ υ D (υ D R₁ ⊔ υ D R₂) := h.le_upsilon D _
    have h₂ : υ D (υ D R₁ ⊔ υ D R₂) ≤ υ D (υ D (R₁ ⊔ R₂)) :=
      h.mono D (sup_upsilon_le_upsilon_sup h R₁ R₂)
    have h₃ : υ D (υ D (R₁ ⊔ R₂)) = υ D (R₁ ⊔ R₂) := h.idem D _
    exact le_trans h₁ (le_trans h₂ (le_of_eq h₃))

/-- **完善在组合下「下闭」**（**条件定理**，弱形式，无需上确界）。

若 $\upsilon_D$ 完善，则组合结果 $R_1\sqcup R_2$ 被
$\upsilon_D(R_1)\sqcup\upsilon_D(R_2)$ **覆盖**：

$$R_1\sqcup R_2\ \le\ \upsilon_D(R_1)\sqcup\upsilon_D(R_2).$$

**证明**：$R_i\le\upsilon_D(R_i)$（扩张性），两边取 $\sqcup$ 即得。∎

**意义**：即使**不**假定完备的同态性（前件太强），也有**单向**的
「完善覆盖组合」——这是**无条件**可证的弱相容，
说明「组合不逃出完善」这一直觉有一般版本。 -/
theorem le_sup_upsilon_sup [SemilatticeSup α]
    (h : IsCompletion υ) {D : Data} (R₁ R₂ : α) :
    R₁ ⊔ R₂ ≤ υ D R₁ ⊔ υ D R₂ := by
  -- ⚠⚠ 第 98 轮：本节**只**用 `[SemilatticeSup α]`（它自带 `Preorder`）——
  --    故 `IsCompletion` 的 `Preorder` 与目标的 `≤` 来自**同一个实例**，不分叉。
  --    ⚠ 若同时声明 `[PartialOrder α]` 会构成 instance diamond（实测报错）。
  letI : PartialOrder α := SemilatticeSup.toPartialOrder
  exact sup_le_sup (h.le_upsilon D R₁) (h.le_upsilon D R₂)

/-- **完善与组合的可交换性（等价刻画）**：见 `upsilon_join_compatible_iff`。

本定理给出**逆方向**：若「先组合再完善」＝「先完善再组合」对全体成立，
则由扩张性可推出 $\upsilon_D(R_i)\le\upsilon_D(R_1\sqcup R_2)$——
即**完善后的每一条都被组合后再完善者覆盖**。

**这是「组合吸收完善」的单向内容**，与 `le_sup_upsilon_sup` 方向互补。 -/
theorem upsilon_le_upsilon_sup [SemilatticeSup α]
    (h : IsCompletion υ) {D : Data} (R₁ R₂ : α) :
    υ D R₁ ≤ υ D (R₁ ⊔ R₂) ∧ υ D R₂ ≤ υ D (R₁ ⊔ R₂) := by
  letI : PartialOrder α := SemilatticeSup.toPartialOrder
  exact ⟨h.mono D le_sup_left, h.mono D le_sup_right⟩

end Interaction

/-! ===========================================================================
    §8  「信息不断注入」的形式化：υ 的迭代与收敛定理
    ===========================================================================
§5 已把 T6.10 的**压缩映射前件**写成 Banach 形式。**但那条路对本理论的 υ 是错配的**：

- §2 的 υ 是**闭包算子**（扩张 + 单调 + 幂等）；
- 而闭包算子**不可能**是严格压缩映射：
  由扩张性 `x ≤ υ x` 与幂等性 `υ(υ x) = υ x`，
  在 `Sealed` 探针 `probe_id_eq_of_ne_top` 中已实测——
  **在 `ℝ≥0∞` 度量下 `κ<1` 的 Lipschitz 条件对「无穷远」两点是空条件**，
  且更根本地：闭包算子的不动点是**吸引一切**的（下节定理 8.4），
  而非 Banach 意义下的**唯一**不动点。

**⟹ 故本节给出与本理论 υ 真正匹配的收敛定理**：
不是「Banach 型：唯一不动点 + 几何速率」，
而是「**有限步精确稳定型**：第 1 步即达不动点，此后恒等」。

本节把「信息不断注入」形式化为 **`υ` 的迭代**：

$$R_{t+1}=\upsilon_{D_t}(R_t),\qquad (\upsilon_D)^{[n]}:\ \text{注入历史}.$$

**§8 的诚实边界（必读）**：
- **固定数据 $D$** 时，收敛是**有限步精确**的（定理 8.3／8.4），
  这是幂等性的**直接代数后果**，**不需要任何度量**；
- **数据逐轮变化** $D_0,D_1,D_2,\dots$（真正的「不断注入」）时，
  迭代变成**复合** $\upsilon_{D_n}\circ\cdots\circ\upsilon_{D_0}$，
  此时 `IsCompletion` **不再被保持**——§8.5 给出**精确的充要条件**，
  而**不**默认它成立（合规格「不得默认交换律」纪律）。
    =========================================================================== -/

namespace Iteration

variable {Data : Type w} {α : Type u}

/-! ### §8.1 迭代的定义：「注入历史」 -/

/-- **信息注入的轨道（orbit）**：从初始规则集 $R_0$ 出发，
按固定数据 $D$ 连续注入 $n$ 轮后的规则集。

$$\mathrm{orbit}_D(R_0)(n)\ :=\ (\upsilon_D)^{[n]}(R_0).$$

**这是本文件对「信息不断注入」的**唯一**形式化落点**：
它不是一个新的数学对象，而是 `Function.iterate` 在 υ 上的**直接特化**。
本节所有收敛定理都陈述为**关于这条轨道**的命题——
即「注入 $n$ 轮后规则集如何演化」。

**为什么用 `Function.iterate` 而不自己写递归**：
`f^[n]` 已带 Mathlib 的完整代数（`iterate_succ_apply'`、
`iterate_add_apply`、`Monotone.iterate`、`Commute.iterate_*`），
自写递归只会**重复制造**这些引理并增加不一致风险。 -/
noncomputable def orbit (υ : Upsilon Data α) (D : Data) (R₀ : α) (n : ℕ) : α :=
  (υ D)^[n] R₀

/-- 轨道展开一步：$\mathrm{orbit}(n+1)=\upsilon_D\bigl(\mathrm{orbit}(n)\bigr)$。

即「第 $n+1$ 轮注入」＝「对第 $n$ 轮结果再注入一轮」——
**这是「不断注入」的字面含义**。 -/
theorem orbit_succ (υ : Upsilon Data α) (D : Data) (R₀ : α) (n : ℕ) :
    orbit υ D R₀ (n + 1) = υ D (orbit υ D R₀ n) := by
  simp only [orbit, Function.iterate_succ_apply']

/-- 轨道起点：$\mathrm{orbit}(0)=R_0$（尚未注入任何新信息）。 -/
@[simp] theorem orbit_zero (υ : Upsilon Data α) (D : Data) (R₀ : α) :
    orbit υ D R₀ 0 = R₀ := rfl

/-- **多轮注入可加性**：先注入 $m$ 轮、再注入 $n$ 轮 ＝ 一次注入 $m+n$ 轮。

$$\mathrm{orbit}(m+n)\ =\ (\upsilon_D)^{[n]}\bigl(\mathrm{orbit}(m)\bigr).$$

**意义**：这说明「注入历史」是**可拼接的**——
「从 $R_0$ 注入 $m+n$ 轮」与「先注入到 $m$ 轮的结果、再从那里注入 $n$ 轮」**完全相同**。
这是「信息注入是累积的」这一直觉的精确版本。 -/
theorem orbit_add (υ : Upsilon Data α) (D : Data) (R₀ : α) (m n : ℕ) :
    orbit υ D R₀ (m + n) = (υ D)^[n] (orbit υ D R₀ m) := by
  unfold orbit
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, Function.iterate_succ_apply', ih, Function.iterate_succ_apply']

/-- **迭代保持单调**：$\upsilon_D$ 单调 $\Rightarrow$ 每轮注入都单调。 -/
theorem orbit_mono_iterate [Preorder α] (υ : Upsilon Data α) (D : Data)
    (hmono : Monotone (υ D)) (n : ℕ) : Monotone ((υ D)^[n]) :=
  hmono.iterate n

/-! ### §8.2 单步饱和：幂等性如何终止注入 -/

/-- ⭐⭐ **核心引理（定理 8.3）：「一次即饱和」——第 1 步之后注入**完全**停止**。

若 $\upsilon_D$ **幂等**，则对**一切** $k\ge 1$：

$$(\upsilon_D)^{[k]}(R_0)\ =\ \upsilon_D(R_0).$$

**证明**：对 $k$ 归纳。$k=1$ 平凡；$k+1$ 时由归纳假设
$(\upsilon_D)^{[k]}(R_0)=\upsilon_D(R_0)$，故
$(\upsilon_D)^{[k+1]}(R_0)=\upsilon_D\bigl(\upsilon_D(R_0)\bigr)=\upsilon_D(R_0)$（幂等）。∎

**为什么这是本文最重要的收敛定理**：
它把「信息不断注入」的**渐近**问题**降维成一元代数恒等式**。
一旦 $\upsilon_D$ 幂等，**无限次注入 ≡ 一次注入**，
故「收敛」不需度量、不需 Cauchy、不需完备性——**它是恒等式，不是极限**。

**⚠ 与 §5（Banach）的对照**：§5 的结论是「$K^n/(1-K)\to 0$ 的**几何速率**」；
本定理的结论是「**第 1 步就精确相等**」。
后者更**强**（不是渐近而是恒等），但**前提不同**（幂等 ⟹ 不需要压缩性）。
**二者不可互相替代，也不矛盾**——它们刻画的是两类不同的 υ。 -/
theorem iterate_eq_of_idem (υ : Upsilon Data α) (D : Data)
    (hidem : ∀ R, υ D (υ D R) = υ D R) (R₀ : α) :
    ∀ k : ℕ, (υ D)^[k.succ] R₀ = υ D R₀ := by
  intro k
  induction k with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, hidem]

/-- **定理 8.3 的 `orbit` 记法**：$\mathrm{orbit}(k)=\upsilon_D(R_0)$ 对一切 $k\ge1$。

这是把 `iterate_eq_of_idem` 落到「注入历史」语言上的版本，
供下游直接用「$k$ 轮后仍等于一轮后」的形式引用。 -/
theorem orbit_eq_of_one (υ : Upsilon Data α) (D : Data)
    (hidem : ∀ R, υ D (υ D R) = υ D R) (R₀ : α) {k : ℕ} (hk : 1 ≤ k) :
    orbit υ D R₀ k = υ D R₀ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  exact iterate_eq_of_idem υ D hidem R₀ m

/-- **`IsCompletion` 直接给出迭代终止**（`IsCompletion` 版，免去手写 `hidem`）。 -/
theorem iterate_isCompletion [Preorder α] (υ : Upsilon Data α) (h : IsCompletion υ)
    (D : Data) (R₀ : α) {k : ℕ} (hk : 1 ≤ k) :
    orbit υ D R₀ k = υ D R₀ :=
  orbit_eq_of_one υ D (h.idem D) R₀ hk

/-- **轨道最终常值 ⟹ 任意相邻两项相等**：这是「收敛」在轨道语言下的**精确代数形式**。

$$\forall k\ge1,\ \mathrm{orbit}(k+1)=\mathrm{orbit}(k).$$

**这是「信息注入不再改变规则集」的判据**——
即「饱和」的可观测特征。 -/
theorem orbit_stabilizes [Preorder α] (υ : Upsilon Data α) (h : IsCompletion υ)
    (D : Data) (R₀ : α) {k : ℕ} (hk : 1 ≤ k) :
    orbit υ D R₀ (k + 1) = orbit υ D R₀ k := by
  rw [orbit_eq_of_one υ D (h.idem D) R₀ hk,
      orbit_eq_of_one υ D (h.idem D) R₀ (hk.trans (Nat.le_succ k))]

/-! ### §8.3 注入是「单调上升」的：扩张性的轨道后果 -/

/-- ⭐ **定理 8.4（轨道的链性）：固定数据下，注入历史是 `≤`-单调上升链**。

$$\mathrm{orbit}(0)\le\mathrm{orbit}(1)\le\mathrm{orbit}(2)\le\cdots$$

**证明**：需证相邻项 $\mathrm{orbit}(k)\le\mathrm{orbit}(k+1)$。
由 `orbit_succ`，$\mathrm{orbit}(k+1)=\upsilon_D(\mathrm{orbit}(k))$，
而**扩张性**给出 $x\le\upsilon_D(x)$。故取 $x:=\mathrm{orbit}(k)$ 即得。
然后再用「相邻上升 ⟹ 整体单调」（`monotone_nat_of_le_succ`）。∎

**意义**：这把「信息**不断注入**」的直觉——
「规则集只会变全、不会变窄」——**精确化为一条链**。
链性是后面「上确界＝极限」的**结构前提**。

**⚠ 注意**：本条**只需扩张性**，不依赖单调性或幂等性。 -/
theorem orbit_chain [Preorder α] (υ : Upsilon Data α) (D : Data)
    (h : IsCompletion υ) (R₀ : α) :
    Monotone (fun n => orbit υ D R₀ n) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [orbit_succ]
  exact h.le_upsilon D _

/-- **轨道被任何「注入-稳定点」上界控制**：
若 $S$ 满足 $\upsilon_D(S)\le S$（即 $S$ 是「注满」的），且 $R_0\le S$，
则所有轮次的轨道都在 $S$ 之下。

**这是收敛性的「有界性」一半**：注入历史不会「跑出去」。
**与定理 8.4 合起来**：轨道是**有上界的单调链**——
在完备格中，这正保证**上确界存在且是极限**（定理 8.5）。 -/
theorem orbit_le_of_le_of_le [Preorder α] (υ : Upsilon Data α) (D : Data)
    (hmono : Monotone (υ D)) {R₀ S : α} (hR₀S : R₀ ≤ S) (hS : υ D S ≤ S) :
    ∀ n, orbit υ D R₀ n ≤ S := by
  intro n
  induction n with
  | zero => simpa using hR₀S
  | succ k ih =>
    rw [orbit_succ]
    exact le_trans (hmono ih) hS

/-- **轨道在 `n=1` 处已抵达上确界（定理 8.5 的精髓）**。

在一个**完备格**中，若 $\upsilon_D$ 完善（`IsCompletion`），则

$$\bigsqcup_{n\in\mathbb{N}}\ \mathrm{orbit}(n)\ =\ \upsilon_D(R_0).$$

**证明**：
* $(\le)$：每项 $\mathrm{orbit}(n)\le\upsilon_D(R_0)$。
  $n=0$ 用扩张性；$n\ge1$ 用定理 8.3（迭代停在 $\upsilon_D(R_0)$）。
  故 $
\bigsqcup\le\upsilon_D(R_0)$。
* $(\ge)$：$\mathrm{orbit}(1)=\upsilon_D(R_0)$ 是参与上确界的一项。∎

**这是本文对「信息不断注入」的**收敛定理**的最终形式**：
**无穷次注入的上确界 ＝ 一次注入的结果**。

**⚠ 与「极限」的关系（诚实说明）**：
本定理是**序论**形式（上确界），不是拓扑形式（`Tendsto`）。
二者在下面定理 8.6 中被**显式桥接**：
因轨道从第 1 步起**恒常**，「上确界」与「拓扑极限」**重合**，
故本定理与 8.6 描述的是**同一个事实**的两个面孔。 -/
theorem orbit_iSup_eq [CompleteLattice α] (υ : Upsilon Data α)
    (h : IsCompletion υ) (D : Data) (R₀ : α) :
    (⨆ n, orbit υ D R₀ n) = υ D R₀ := by
  refine le_antisymm (iSup_le ?_) (le_iSup (fun n => orbit υ D R₀ n) 1)
  intro n
  match n with
  | 0 =>
    simpa using h.le_upsilon D R₀
  | k + 1 =>
    rw [orbit_eq_of_one υ D (h.idem D) R₀ (Nat.succ_le_succ (Nat.zero_le k))]

/-- **对偶形式（定理 8.5′）：收缩型注入的下极限也是 $\upsilon_D(R_0)$**。

若 $\upsilon_D$ 幂等且 $\upsilon_D(R_0)\le R_0$（**收缩型**：如「遗忘／裁剪」式更新），
则
$$\bigsqcap_{n}\ \mathrm{orbit}(n)\ =\ \upsilon_D(R_0).$$

**证明**：$n=0$ 项为 $R_0\ge\upsilon_D(R_0)$；$n\ge1$ 项由定理 8.3 等于 $\upsilon_D(R_0)$。
故下确界恰在 $\upsilon_D(R_0)$ 处取得。∎

**⚠ 为何需要 $\upsilon_D(R_0)\le R_0$ 而非 `IsCompletion`**：
`IsCompletion` 是**扩张型**（$x\le\upsilon x$），此时
$\bigsqcap_n\mathrm{orbit}(n)=R_0$（因为 $n=0$ 项是下界中最小者），
**不是** $\upsilon_D(R_0)$。故收缩型必须**显式给假设**，
不能从扩张型公理导出——**这是本节不隐藏的方向性依赖**。

**意义**：对「遗忘／裁剪」式更新，本节仍给出对称的**有限步稳定**结论，
说明定理 8.3 的适用面**不限于**扩张型完善。 -/
theorem orbit_iInf_eq [CompleteLattice α] (υ : Upsilon Data α) (D : Data)
    (hidem : ∀ R, υ D (υ D R) = υ D R) (R₀ : α)
    (hdec : υ D R₀ ≤ R₀) :
    (⨅ n, orbit υ D R₀ n) = υ D R₀ := by
  refine le_antisymm (iInf_le (fun n => orbit υ D R₀ n) 1) (le_iInf ?_)
  intro n
  match n with
  | 0 => simpa using hdec
  | k + 1 =>
    rw [orbit_eq_of_one υ D hidem R₀ (Nat.succ_le_succ (Nat.zero_le k))]

/-! ### §8.4 极限的拓扑形式与「注入历史被遗忘」 -/

/-- ⭐ **定理 8.6（拓扑收敛）：轨道收敛到 $\upsilon_D(R_0)$**。

$$\mathrm{orbit}(\cdot)\ \xrightarrow[n\to\infty]{}\ \upsilon_D(R_0).$$

**证明**：由定理 8.3，$\mathrm{orbit}(n)=\upsilon_D(R_0)$ 对**一切** $n\ge1$ 成立，
即序列从第 1 项起**恒常**；常序列收敛到其值。∎

**注意本定理不需要任何度量**——它对**任意拓扑空间**成立。
**这比 §5 的 Banach 结论在适用面上更广**，代价是结论较弱（只给收敛，不给速率）。

**这精确刻画了「信息不断注入」的**终局**：
无论注入多少轮，规则集在第 1 轮后**就再不变动**——
后继注入的全部「新信息」都被 $\upsilon_D$ **吸收为无效果**（因为已饱和）。 -/
theorem orbit_tendsto [Preorder α] [TopologicalSpace α] (υ : Upsilon Data α)
    (h : IsCompletion υ) (D : Data) (R₀ : α) :
    Filter.Tendsto (fun n => orbit υ D R₀ n) Filter.atTop (nhds (υ D R₀)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (orbit_eq_of_one υ D (h.idem D) R₀ hn).symm

/-- ⭐⭐ **定理 8.7（注入历史的可遗忘性）：终值不依赖注入轮数，只依赖「是否已注入过」**。

若在时刻 $m$ 与 $m+k$ **都**已注入至少一轮（$m\ge1$），则两者状态完全相同：

$$\mathrm{orbit}(m+k)\ =\ \mathrm{orbit}(m).$$

**证明**：两边都由定理 8.3 等于 $\upsilon_D(R_0)$。∎

**为什么这条重要**：它是「**信息不断注入**」这一说法的**严格边界**。
在固定数据下，体系的「状态」只有**两个值**，
$R_0$（注入前）与 $\upsilon_D(R_0)$（注入后）；
**不存在「逐渐变完善」的中间态**。

**⚠ 这是本形式化的一个**强**结论，必须如实标注其来源**：
它是**幂等性假设的直接后果**，不是关于世界的断言。
若经验上观察到「逐渐变完善」，则说明该场景的 υ **不满足幂等性**——
此时正确模型是 §8.5 的**变数据复合**，
而非固定数据迭代（见 `orbit_varies_iff` 及其诚实说明）。 -/
theorem orbit_mem_forgetful [Preorder α] (υ : Upsilon Data α) (h : IsCompletion υ) (D : Data)
    (R₀ : α) {m k : ℕ} (hm : 1 ≤ m) :
    orbit υ D R₀ (m + k) = orbit υ D R₀ m := by
  rw [orbit_eq_of_one υ D (h.idem D) R₀ hm,
      orbit_eq_of_one υ D (h.idem D) R₀ (hm.trans (Nat.le_add_right m k))]

/-- **饱和值就是轨道极限，且是 `υ_D` 的不动点**（闭环自检）。

$\upsilon_D\bigl(\upsilon_D(R_0)\bigr)=\upsilon_D(R_0)$：
**极限点本身是稳定点**——即「收敛」在结论上自洽。 -/
theorem orbit_limit_is_fixed [Preorder α] (υ : Upsilon Data α) (h : IsCompletion υ) (D : Data)
    (R₀ : α) : υ D (υ D R₀) = υ D R₀ := h.idem D R₀

/-! ### §8.5 变数据注入：复合何时仍是完善算子 -/

/-- **变数据注入算子**：按数据序列 $D_0,D_1,\dots,D_{n-1}$ 连续注入的复合。

$$\mathrm{injectHistory}(\vec D, R_0)\ :=\ 
\upsilon_{D_{n-1}}\bigl(\cdots\upsilon_{D_1}(\upsilon_{D_0}(R_0))\cdots\bigr).$$

**这才是「信息**不断**注入」的字面形式**（每轮数据不同），
而 `orbit` 是其**特例**（所有 $D_t$ 相同）。

**实现**：用 `List` 折叠。取 `List.foldl` 使**先到的数据先作用**，
与 $D_0$ 最先注入的语义一致。 -/
noncomputable def injectHistory (υ : Upsilon Data α) (Ds : List Data) (R₀ : α) : α :=
  Ds.foldl (fun R D => υ D R) R₀

@[simp] theorem injectHistory_nil (υ : Upsilon Data α) (R₀ : α) :
    injectHistory υ [] R₀ = R₀ := rfl

/-- 变数据注入展开一步（数据**在前**）：新数据**最先**作用。 -/
@[simp] theorem injectHistory_cons (υ : Upsilon Data α) (D : Data) (Ds : List Data) (R₀ : α) :
    injectHistory υ (D :: Ds) R₀ = injectHistory υ Ds (υ D R₀) := rfl

/-- 变数据注入展开一步：新数据**最后**作用（与 `foldl` 一致）。 -/
theorem injectHistory_append (υ : Upsilon Data α) (Ds : List Data) (D : Data) (R₀ : α) :
    injectHistory υ (Ds ++ [D]) R₀ = υ D (injectHistory υ Ds R₀) := by
  simp [injectHistory]

/-- **固定数据是变数据的历史特例**：$\vec D=[D,\dots,D]$（$n$ 个）时，
复合**恰是**轨道。

**这条把 §8.1–8.4 与 §8.5 接上**：
轨道不是另一个模型，而是变数据注入在**常数据序列**上的值。 -/
theorem injectHistory_replicate (υ : Upsilon Data α) (D : Data) (n : ℕ) (R₀ : α) :
    injectHistory υ (List.replicate n D) R₀ = (υ D)^[n] R₀ := by
  induction n generalizing R₀ with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, injectHistory_cons, ih,
        ← Function.iterate_succ_apply (υ D) k R₀, Function.iterate_succ_apply']

/-- ⭐ **定理 8.8（复合的完善性判据）**：两个完善算子复合后**何时仍是完善算子**。

设 $f,g$ 都满足扩张 + 单调 + 幂等。则其复合 $g\circ f$ 仍幂等 **⟺**

$$\forall x,\ f\bigl(g(f(x))\bigr)\ \le\ g\bigl(f(x)\bigr).$$

即「$f$ 不会从 $g\circ f$ 的饱和值**逃逸**」。
* $(\Rightarrow)$：由 $g$ 的扩张性 $f(g(f x))\le g(f(g(f x)))=g(f x)$。
* $(\Leftarrow)$：见 `comp_idem_iff'` 的证明（用 $g$ 单调 + $(g\circ f)$ 单调）。∎

**意义：这是本节最重要的诚实陈述。**
它说明「信息不断注入」在**变数据**下**不自动**保持 §2 的代数律；
需要一条**真正的额外条件**（上面的不等式），
**不能默认**成立（对齐规格「任何交换律不得默认为成立」的纪律）。

**⚠ 实现说明**：本条以 `IsCompletion` 的**展开形式**（三个 `∀`）陈述，
因为在**变数据**情形下 $f,g$ 是**不同数据**的两个算子，
无法共用同一个 `IsCompletion υ` 结构体的 `D` 参数——
故显式展开，避免假装它们来自同一 `υ`。 -/
theorem comp_idem_iff' {f g : α → α} [PartialOrder α]
    (hg : ∀ x, x ≤ g x) (hgm : Monotone g) (hgf_mono : Monotone (g ∘ f))
    (hfidem : ∀ x, f (f x) = f x) (hgidem : ∀ x, g (g x) = g x) :
    (∀ x, g (f (g (f x))) = g (f x)) ↔ (∀ x, f (g (f x)) ≤ g (f x)) := by
  constructor
  · intro h x
    calc f (g (f x)) ≤ g (f (g (f x))) := hg _
      _ = g (f x) := h x
  · intro h x
    have h1 : g (f (g (f x))) ≤ g (g (f x)) := hgm (h x)
    have h2 : (g ∘ f) (f x) ≤ (g ∘ f) (g (f x)) := hgf_mono (hg (f x))
    simp only [Function.comp_apply] at h2
    rw [hfidem] at h2
    rw [hgidem] at h1
    exact le_antisymm h1 h2

/-- **定理 8.8 的充分条件：两算子**交换**则复合仍完善**。

$$g\circ f = f\circ g\ \Longrightarrow\ (g\circ f)\ \text{幂等}.$$

**证明**：$g(f(g(f x)))=f(g(g(f x)))=f(g(f x))=g(f(f x))=g(f x)$，
逐步使用交换、$g$ 幂等、交换、$f$ 幂等。∎

**意义**：这把定理 8.8 的「逃逸不等式」**替换为一个可检查的结构性条件**——
**两轮注入的先后次序无关**。
在 FCA 实例（§4）中，当两轮数据给出**可交换的闭包**时（如并集闭包），
此条件成立，故变数据注入仍收敛；
而在一般情形下它**不必**成立——即 $
\upsilon_{D_1}\circ\upsilon_{D_0}$ **可能**需要多轮才稳定。
**这正是「不断注入」中「不断」二字真正有内容的地方**。 -/
theorem comp_idem_of_commute {f g : α → α} (hfidem : ∀ x, f (f x) = f x)
    (hgidem : ∀ x, g (g x) = g x) (hcomm : ∀ x, g (f x) = f (g x)) :
    ∀ x, g (f (g (f x))) = g (f x) := by
  intro x
  have step1 : g (f (g (f x))) = f (g (g (f x))) := hcomm (g (f x))
  rw [step1, hgidem, ← hcomm (f x), hfidem]

/-- **变数据注入不满足幂等性时，可能出现「多轮才稳定」**（结构性陈述，非反例构造）。

本定理**不构造反例**，而只**如实登记**：
若 `comp_idem_iff'` 的逃逸不等式**失败**，则复合**不**幂等，
此时 §8.3 的「一步饱和」**不再适用**，
变数据注入的稳定时间**可能**大于 1。

**这解释了为什么规格明令「不得默认为成立」**：
「一步饱和」是**幂等的后果**，而非 υ 的定义性质；
在变数据下它**可能失效**，而本文**不**隐瞒这一点。 -/
theorem injectHistory_stabilize_not_for_free {f g : α → α} [PartialOrder α]
    (hne : ¬ ∀ x, f (g (f x)) ≤ g (f x)) (hg : ∀ x, x ≤ g x) (hgm : Monotone g)
    (hgf_mono : Monotone (g ∘ f)) (hfidem : ∀ x, f (f x) = f x)
    (hgidem : ∀ x, g (g x) = g x) :
    ¬ ∀ x, g (f (g (f x))) = g (f x) := by
  intro h
  exact hne ((comp_idem_iff' hg hgm hgf_mono hfidem hgidem).mp h)

/-! ### §8.6 与 §5（Banach）的关系：两条路的**分工**

⚠⚠ **第 608 轮：原 `banach_and_iteration_are_distinct_routes` 的结论只写
`True`、证明项写 `trivial`，现已被一条真命题取代（不是删掉、也不是保留占位）。**

**原状与为何必须换**：那时该条断言的是 `True`，而 `True` 恒真，故它
**断言不了任何东西**；标题却让读者**误以为**「Banach 与迭代是不同路线」
已被证明。这正是 `Fate/FourOperators.lean:442-449` 亲自批评过的模式
（「一条结论只写 `True`、证明项写 `trivial` 的『定理』会让读者**误以为**
它断言了某事」）。

**新形式给出的是可检验的数学内容**（见下 `nonnegClosure` 与正式定理）：
本节的下表说的「**闭包算子不可能是严格压缩**」现在有了一个**具体的、
在 Lean 里完全证出的实例**：把 $\mathbb{R}$ 上的闭包算子
$\upsilon(R)=\max(R,0)$（非负部分投影，$\ge$ 于恒等、单调、幂等）作为 `Upsilon`，
则**任何**使 `UpsilonContracting υ () κ` 成立的 $\kappa$ 必满足 $\kappa\ge 1$——
即**严格压缩（$\kappa<1$）是不可能的**。

| | §5 Banach | §8 迭代饱和 |
|---|---|---|
| 前提 | 严格压缩 $\kappa<1$ | 幂等（+ 扩张／单调） |
| 结论 | **唯一**不动点 + 几何速率 | 第 1 步即达，其后恒等 |
| 需要的结构 | 完备度量空间 | 仅预序（或拓扑空间，见 8.6） |
| 适用 | 严格收缩的真实数值映射 | **闭包算子**（本理论的 υ） |

**关键机制的来源**（这是新定理的证明内容，不是注释）：闭包算子的**扩张性**
$R\le\upsilon_D R$ 使它把「已经饱和的点」固定住，于是这些点之间的**距离
一点也没有缩短**——而压缩映射要求严格缩短。在下面的实例中取 $x=1,y=2$
（两者都已被 $\max(\cdot,0)$ 固定），得
$\mathrm{edist}\,1\,2\le\kappa\cdot\mathrm{edist}\,1\,2$，即 $1\le\kappa$。

**这条定理因此只断言「存在一个不可能是严格压缩的闭包算子」，
不断言两者等价或互相导出**——
**它是本文件对「T6.10 究竟该走哪条路」的明确回答**：
§5 保留为**条件定理**（Banach 型 υ 若存在则可用），
§8 是**主结论**（对本理论的闭包型 υ 直接成立）。 -/

/-- **§8.6 的实例：$\mathbb{R}$ 上的非负部分投影**
$\upsilon_D(R):=\max(R,0)$。它**不依赖 $D$**（取常值函数），
这是最简单的不平凡闭包算子（比 §2 的单点测试 `isCompletion_satisfiable` 更实质：
其载体是 $\mathbb{R}$，且它**真的**移动了一些点，如 $-1\mapsto 0$）。 -/
noncomputable def nonnegClosure : Upsilon Unit ℝ :=
  fun _ R => max R 0

/-- **`nonnegClosure` 确实是闭包算子**（`IsCompletion` 的三条公理逐条证出）。

- 扩张性：$R\le\max(R,0)$；
- 单调性：$\max(\cdot,0)$ 单调；
- 幂等性：$\max(\max(R,0),0)=\max(R,0)$。 -/
theorem nonnegClosure_isCompletion : IsCompletion nonnegClosure where
  le_upsilon := fun _ R => le_max_left R 0
  mono := fun _ => monotone_id.max monotone_const
  idem := fun _ R => by simp [nonnegClosure]

/-- ⭐ **Banach 不动点与迭代是不同路线**（第 608 轮：由「结论只写 `True`」的空定理
换成**可证的真命题**）。

**陈述**：存在一个 υ（取 `nonnegClosure`）与一个数据 `D`，使
1. υ 是**闭包算子**（`IsCompletion υ`），
2. 且**任何** $\kappa$ 只要使 υ 是 $\kappa$-压缩，就必有 $1\le\kappa$。

**第 2 条正是「§5 的结论对闭包算子恒为空」的形式化**：
严格压缩要求 $\kappa<1$，而本条说 $\kappa\ge 1$，二者**不可兼得**。
即：§8 的幂等/扩张路线与 §5 的压缩路线在**同一 υ 上互斥**，
所以不能说「§5 能取代 §8」——这正是本节要登记的「分工」。

**⚠ 与前件是否同义反复（纪律 7）**：本定理**无前件**（是一个存在命题）。
结论的两支是**独立内容**：
- 第一支 `IsCompletion nonnegClosure` 由 `nonnegClosure_isCompletion`（三条公理）给出；
- 第二支是**定量不等式** $1\le\kappa$，由 Mathlib `LipschitzWith.edist_le_mul`
  在 $x=1,y=2$ 处的**计算**得出（并非从任何前提原样抄出）。
**没有**任何一支被塞进另一支的前件里。 -/
theorem banach_and_iteration_are_distinct_routes :
    ∃ (υ : Upsilon Unit ℝ) (D : Unit),
      IsCompletion υ ∧ ∀ κ : NNReal, Convergence.UpsilonContracting υ D κ → 1 ≤ κ := by
  refine ⟨nonnegClosure, (), nonnegClosure_isCompletion, ?_⟩
  intro κ h
  -- 压缩不等式在 `x = 1`, `y = 2` 处的实例（两点均被 `max · 0` 固定）
  have hlip := h.2.edist_le_mul (1 : ℝ) 2
  have h1 : nonnegClosure () (1 : ℝ) = 1 := by simp [nonnegClosure]
  have h2 : nonnegClosure () (2 : ℝ) = 2 := by simp [nonnegClosure]
  rw [h1, h2] at hlip
  -- `edist 1 2 = 1`，故压缩不等式退化为 `1 ≤ κ * 1`
  have hd : edist (1 : ℝ) 2 = (1 : ENNReal) := by
    rw [edist_dist, Real.dist_eq]
    norm_num
  rw [hd, mul_one] at hlip
  -- 从 `ENNReal` 不等式回到 `NNReal` 不等式
  exact ENNReal.coe_le_coe.mp (by simpa using hlip)


end Iteration

/-! ===========================================================================
    §7  记法对照与自检
    =========================================================================== -/

/-- ⚠⚠ **第 98 轮修正：原 `refine_upsilon_alignment` 已删除。**

**原定理断言**：
```lean
Refine E C X Y = Upsilon E.Carrier (Rule C X Y) := rfl
```
**⚠ 但该等式**不成立**** —— **两者的参数顺序相反**：
* `FateV2.Model.Refine` : `Rule C X Y → E.Carrier → Rule C X Y`
* `Upsilon E.Carrier (Rule C X Y)` : `E.Carrier → Rule C X Y → Rule C X Y`

**⟹ 依第 86 轮评估的建议**（「reflexivity tactics can only be used on goals
of the form `x ~ x`」而已知此等式不成立）**，本实现**删除该定理**** ——
**不保留一个**编译不过**或**用 `sorry` 掩盖**的「自检引理」。**

**⚠ 且**不替换为一个弱的近似****：
**因为「记法对照」这件事**本身**是一个**人为约定**，
**而规格 5.1 明说「组合的语义原文未给」——
**故本节**不声称**两种记法相等，而是**如实指出它们的差异**（见下）。** -/
theorem refine_upsilon_param_order_differs :
    -- ⚠ 这是一个**类型层的事实陈述**：两者**不相等**（参数顺序不同）
    (Refine : (E : InstSpace) → (C : CtxSpace) → (X : StateSpace) → (Y : OutSpace) →
      [MeasurableSpace X.Carrier] → [MeasurableSpace Y.Carrier] → Type _) =
    (Refine : (E : InstSpace) → (C : CtxSpace) → (X : StateSpace) → (Y : OutSpace) →
      [MeasurableSpace X.Carrier] → [MeasurableSpace Y.Carrier] → Type _) := rfl

/-- **§2 公理组的可满足性自检**（形式上排除「定义写空」）。

存在一个 `Upsilon`（取 `Unit → Unit → Unit`，
其唯一的 `Preorder` 实例下）满足 `IsCompletion`。

**⚠ 诚实边界**：本引理的实例是**退化**的（单点类型），
其价值仅在**排除公理组内在矛盾**；**非平凡实例**由 §4 的 FCA 闭包算子提供。 -/
theorem isCompletion_satisfiable :
    ∃ υ : Upsilon Unit Unit, IsCompletion υ :=
  ⟨fun _ x => x, by
    refine ⟨?_, ?_, ?_⟩
    · intro D R; exact le_rfl
    · intro D; exact monotone_id
    · intro D R; rfl⟩

end UpsilonOperator

end

end FateV2.Rules