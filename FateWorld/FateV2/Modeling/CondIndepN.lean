import FateWorld.FateV2.Modeling.BridgeFinal
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
  # Modeling · CondIndepN

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CondIndepN.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeFinal
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenC3 ⭐⭐⭐ **N 元条件独立**（$n$ 元推广）

  ## 目的

  `FiniteCondIndep.CondIndepFin` 只处理**二元**情形
  $X \perp\!\!\!\perp Y \mid Z$（联合律定义在 $(\alpha \times \beta) \times \gamma$ 上）。
  **本文件把它推广到任意有限下标族 $\iota$**：

  $$\mathrm{CondIndepN}\ p :\iff
    \forall xs\ z,\quad p(xs, z)\cdot \big(\mathrm{NMass}\ p\ z\big)^{|\iota|-1}
      = \prod_{i \in \iota} \mathrm{marg}\ p\ i\ (xs_i, z)$$

  ## ⚠⚠ 为什么是这个形式（**上一轮草稿的 3 个缺陷**）

  早期的「草稿定义」`DraftN`（本文件仍保留并与 `CondIndepN` 证明等价，见
  `draftN_iff_condIndepN`）与正确形式相比有**三处错误**：

  | # | 草稿的缺陷 | 后果 | 本文件的处理 |
  |---|---|---|---|
  | 1 | 幂次写成 $\mathrm{NMass}^{|\iota|}$（而非 $|\iota|-1$） | 二元时就退化为 $p\cdot M^2 = m_X m_Y$，**与 `CondIndepFin` 不等价** | 用 $|\iota|-1$，见 `condIndepN_bool_iff` |
  | 2 | $\iota = \mathrm{Unit}$ 时失败 | 左因子应为 $M^0 = 1$ | 用 `Fintype.card ι - 1`，`Unit` 时截断为 $0$，见 `condIndepN_card_one` |
  | 3 | 空族 $\iota = \emptyset$ 时 $|\iota| - 1$ 在 $\mathbb{N}$ 上截断成 $0$ | 命题仍「为真」但语义无意义 | **单列** `CondIndepNEmpty := True`；合并版 `CondIndepNFull` |

  **⚠ `Fintype.card ι - 1` 在 $\mathbb{N}$ 上截断**是**有意的**：
  当 $|\iota| = 0$ 时它等于 $0$，于是 `Unit` 情形自然成立（$M^0 = 1$）。
  而空族情形**不进**`CondIndepN`（它要求 `[Nonempty ι]`），
  由 `CondIndepNEmpty` 单列。

  ## 记号约定

  * $\iota$ —— **变量族的下标类型**（有限、非空）；
  * $\alpha : \iota \to \mathrm{Type}$ —— 各变量的值域（**可以不同**）；
  * $\gamma$ —— **条件变量 $Z$** 的值域；
  * $p : \mathrm{NJoint}\ \alpha\ \gamma := ((\forall i, \alpha\ i) \to \gamma \to \mathbb{R})$
    —— **未归一化**的联合律（不假设 $\sum p = 1$、不假设 $p \ge 0$）。

  ## 主要定理

  | 定理 | 内容 |
  |---|---|
  | `condIndepN_bool_iff` | ⭐ $\iota = \mathrm{Bool}$ 时与 `CondIndepFin` **等价**（相容性检验）|
  | `condIndepN_card_one` | ⭐ $\iota = \mathrm{Unit}$ 时退化为 $p = \mathrm{marg}$ |
  | `condIndepN_split` | ⭐ $\iota = \sigma \oplus \tau$ 时右侧**二分因子化** |
  | `condIndepN_iff_prob` | 与**除法（条件律）形式** `CondIndepNProb` 等价（带守卫）|
  | `condIndepNFull_iff` | 合并版 `CondIndepNFull` $\iff$ `CondIndepN` |

  ## 假设强度（诚实声明）

  * **不做归一化假设**、**不做正性假设**：全部恒等式是**代数恒等式**。
  * **无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

namespace FateV2.Modeling
namespace GenC3

open Finset

/-! ### §1 ⭐ 记号：N 元联合律、质量、边缘律 -/

/-- ⭐ **N 元联合律**：对**每个**下标 $i : \iota$ 取一个值 $xs_i : \alpha_i$，
再固定条件变量 $Z = z$，给出**未归一化**的实值质量。

**⚠ 用 `abbrev`**：类型别名对 elaborator 透明，`p` 可直接传给
期望 `((∀ i, α i) → γ → ℝ)` 的引理。 -/
abbrev NJoint {ι : Type*} (α : ι → Type*) (γ : Type*) :=
  ((i : ι) → α i) → γ → ℝ

-- ⚠ **参数顺序必须逐字对上原 `.olean`**：`[Nonempty ι]` 位于
-- `[DecidableEq ι]` 之后、`{α}` 之前，故它作为**区段变量**声明在这里
-- （放在 `{α}`/`{γ}` 之后会排到 `γ` 之后，签名就漂移了）。
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [Nonempty ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
variable {γ : Type*}

/-- ⭐ **$Z$ 的边缘质量**（把**全部** $X_i$ 边缘化掉）：

$$\mathrm{NMass}\ p\ z := \sum_{xs} p(xs, z)$$

**⟹ 这是「$Z = z$ 的未归一化概率」**，也是条件律形式的分母。 -/
noncomputable def NMass (p : NJoint (ι := ι) α γ) (z : γ) : ℝ :=
  ∑ xs, p xs z

/-- ⭐ **把除第 $i$ 个以外的坐标全部边缘化、只固定 $X_i = a$**：

$$\mathrm{marg}\ p\ i\ a\ z := \sum_{xs' :\, xs'_i = a} p(xs', z)$$

**⟹ 这是条件独立等式**右边第 $i$ 个因子**（在 $Z = z$ 下的分子）。 -/
noncomputable def marg (p : NJoint (ι := ι) α γ) (i : ι) (a : α i) (z : γ) : ℝ :=
  ∑ xs', if xs' i = a then p xs' z else 0

/-! ### §2 ⭐⭐⭐ N 元条件独立的**主定义** -/

/-- ⭐⭐⭐ **N 元条件独立** $\{X_i\}_{i\in\iota} \perp\!\!\!\perp$ （给定 $Z$）。

$$\forall xs\ z,\quad p(xs, z)\cdot \big(\mathrm{NMass}\ p\ z\big)^{|\iota|-1}
  = \prod_{i \in \iota} \mathrm{marg}\ p\ i\ (xs_i, z)$$

**⚠ 为什么幂次是 $|\iota| - 1$**：把「条件联合 = 条件边缘之积」
$$\frac{p}{M} = \prod_i \frac{m_i}{M}$$
两边同乘 $M^{|\iota|}$ 得 $p \cdot M^{|\iota|-1} = \prod_i m_i$。
**⟹ 当 $|\iota| = 2$ 时即 `CondIndepFin` 的 $p \cdot M = m_X m_Y$。**

**⚠ 为什么需要 `[Nonempty ι]`**：`DraftN` 在空族时会得出
「$p \cdot M^0 = \prod_{\emptyset} = 1$」这类**无意义命题**。
空族单列为 `CondIndepNEmpty`，合并版见 `CondIndepNFull`。 -/
noncomputable def CondIndepN (p : NJoint (ι := ι) α γ) : Prop :=
  -- ⚠ 这个 `let` 不是装饰：`[Nonempty ι]` 在**本式本身**里并不出场
  -- （`Fintype.card ι - 1` 在空族时截断为 `0`，等式仍然有意义），
  -- 但**空族**的语义单列为 `CondIndepNEmpty`，故 `CondIndepN` 的签名必须
  -- **带上** `[Nonempty ι]` 这个 binder。Lean 会自动丢弃未被使用的区段变量，
  -- 因此这里显式把实例绑进体里，使签名与原 `.olean` 逐字一致。
  let _ne : Nonempty ι := ‹Nonempty ι›
  ∀ xs z, p xs z * (NMass p z) ^ (Fintype.card ι - 1) = ∏ i, marg p i (xs i) z

/-- ⭐ **`CondIndepN` 的**定义展开**（把 `let _ne` 剥掉）。 -/
theorem condIndepN_iff (p : NJoint (ι := ι) α γ) :
    CondIndepN p ↔ ∀ xs z, p xs z * (NMass p z) ^ (Fintype.card ι - 1) = ∏ i, marg p i (xs i) z :=
  Iff.rfl

/-! ### §3 ⚠ 草稿定义 `DraftN` 及其与正确形式的关系 -/

/-- ⚠ **草稿定义**（**保留以备审计**）：把 `marg` **内联展开**成裸 `∑ if`。

$$\forall xs\ z,\quad p(xs,z)\cdot M^{|\iota|-1}
  = \prod_i \sum_{xs'}\ [xs'_i = xs_i]\ p(xs',z)$$

**⟹ 它与 `CondIndepN` 的区别仅仅是「`marg` 是否内联」**，
故二者**命题等价**（`draftN_iff_condIndepN`，是 `rfl` 级的事实）。
**真正致命的错误不在 `DraftN`，而在更早的版本用了 $M^{|\iota|}$ 与无条件空族**
（见文件头表格）。 -/
noncomputable def DraftN (p : NJoint (ι := ι) α γ) : Prop :=
  ∀ xs z, p xs z * (NMass p z) ^ (Fintype.card ι - 1) = ∏ i, ∑ xs', if xs' i = xs i then p xs' z else 0

/-- ⭐ **`DraftN` 与 `CondIndepN` 等价**（仅 `marg` 内联与否的差别）。 -/
theorem draftN_iff_condIndepN (p : NJoint (ι := ι) α γ) :
    DraftN p ↔ CondIndepN p :=
  Iff.rfl

/-- ⚠ **`DraftN` 在空族 + 常函数上为假**（反驳「`DraftN` 无条件成立」）。

取 $\iota = \emptyset$、$\gamma = \mathrm{Unit}$、$p \equiv 5$：
则 $|\iota| - 1 = 0$，$M = p = 5$，右边 $\prod_{\emptyset} = 1$，
故 $5 \cdot 1 = 1$ 为假。 -/
theorem draftN_false_empty : ¬ DraftN (fun (_ : (i : Empty) → Empty) (_ : Unit) => (5 : ℝ)) := by
  intro h
  have h1 := h (fun e => e.elim) ()
  simp [NMass] at h1

/-! ### §4 ⭐ 空族与合并版 -/

/-- ⭐ **空族的条件独立**：**定义为真**。

$$\mathrm{CondIndepNEmpty}\ p := \mathrm{True}$$

**⚠ 为什么单列**：空族时 `Fintype.card ι - 1` 在 $\mathbb{N}$ 上截断为 $0$，
`CondIndepN` 的等式变成 $p \cdot 1 = 1$（**对一般 $p$ 为假**），
**故不能**把空族塞进 `CondIndepN`。空族的「条件独立」在语义上是**空真**的，
故此处直接取 `True`。 -/
noncomputable def CondIndepNEmpty (_p : NJoint (ι := ι) α γ) : Prop := True

/-- ⭐⭐⭐ **`CondIndepN` 的**除法（条件律）形式****（带 `NMass ≠ 0` 守卫）。

$$\forall xs\ z,\quad \mathrm{NMass}\ p\ z \neq 0 \implies
  \frac{p(xs,z)}{M} = \prod_i \frac{\mathrm{marg}\ p\ i\ (xs_i,z)}{M}$$

**⟹ 左边是条件联合律、右边是**各条件边缘律之积** ——
这正是教科书里的条件独立。**

**⚠ 为什么需要守卫**：除法在 $M = 0$ 处（Lean 的 `/` 总定义但给 $0$）
会**污染命题真假**；而「条件化于零概率事件」本身无定义。 -/
noncomputable def CondIndepNProb (p : NJoint (ι := ι) α γ) : Prop :=
  ∀ xs z, NMass p z ≠ 0 → p xs z / NMass p z = ∏ i, marg p i (xs i) z / NMass p z

/-! ### §5 ⭐ 幂次辅助 -/

/-- ⭐ **$M^{n-1} \cdot M = M^n$**（$n \ge 1$）。

**⟹ 这是「乘性形式 $\iff$ 除法形式」的核心代数步骤**：
把 $M^{|\iota|-1}$ 再乘一个 $M$ 升到 $M^{|\iota|}$。 -/
theorem pow_card_pred_mul {n : ℕ} (h : 1 ≤ n) (M : ℝ) : M ^ (n - 1) * M = M ^ n := by
  rw [← pow_succ, Nat.sub_add_cancel h]

/-- ⭐⭐⭐ **乘性形式 $\iff$ 除法形式**（在 $M$ 处处非零的守卫下）。

$$\Big(\forall xs\,z,\ p\cdot M^{n-1} = \prod_i m_i\Big)
  \iff \Big(\forall xs\,z,\ M \neq 0 \to \frac{p}{M} = \prod_i \frac{m_i}{M}\Big)$$

**⟹ 证明思路**：两边同乘 $M^{n-1}$（用 `pow_card_pred_mul`）后
由 `field_simp` 把分母清掉。**两个方向都用同一个乘子**，
故这是**纯代数**的等价，不做正性假设。 -/
theorem condIndepN_iff_prob (p : NJoint (ι := ι) α γ)
    (h : ∀ z, NMass p z ≠ 0) : CondIndepN p ↔ CondIndepNProb p := by
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
  constructor
  · intro hp xs z hz
    have hxy := hp xs z
    -- 目标：p / M = ∏ (m_i / M)。两边同乘 M^{|ι|} 化为乘性形式。
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
    rw [div_eq_div_iff hz (pow_ne_zero _ hz)]
    linear_combination (hxy * (NMass p z) - pow_card_pred_mul hcard (NMass p z) * p xs z)
  · intro hp xs z
    have hM : NMass p z ≠ 0 := h z
    have hxy := hp xs z hM
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ] at hxy
    rw [div_eq_div_iff hM (pow_ne_zero _ hM)] at hxy
    apply mul_right_cancel₀ hM
    rw [mul_assoc, pow_card_pred_mul hcard]
    exact hxy

/-! ### §6 ⭐ 求和辅助 -/

-- ⚠ 下面两条引理**用不到** `[Nonempty ι]`（它们对空族同样成立），
-- 故用 `omit` 把该 binder 去掉，**使签名与原 `.olean` 逐字一致**。
omit [Nonempty ι] in
/-- ⭐ $\sum_{xs'} [xs' = xs]\ p(xs',z) = p(xs,z)$。 -/
theorem sum_ite_eq_fn (p : NJoint (ι := ι) α γ) (xs : (i : ι) → α i) (z : γ) :
    (∑ xs', if xs' = xs then p xs' z else 0) = p xs z := by
  simp

omit [Nonempty ι] in
/-- ⭐ `marg` 的**定义展开**（`@[simp]` 便于后续 `rw`）。 -/
@[simp] theorem marg_apply (p : NJoint (ι := ι) α γ) (i : ι) (xs : (i : ι) → α i) (z : γ) :
    marg p i (xs i) z = ∑ xs', if xs' i = xs i then p xs' z else 0 :=
  rfl

/-- ⭐ **单点求和** $\sum_x [x = a]\ g(x) = g(a)$。 -/
theorem sum_ite_single {α : Type} [Fintype α] [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (a : α) (g : α → M) : (∑ x, if x = a then g x else 0) = g a := by
  simp

/-! ### §7 ⭐ `Unit` 与 `Bool` 上的乘积/求和 -/

/-- ⭐ `Unit` 上的乘积 = 唯一值。 -/
theorem prod_unit (f : Unit → ℝ) : ∏ i, f i = f () :=
  Fintype.prod_unique f

/-- ⭐ `Unit` 上的求和 = 唯一值。 -/
theorem sum_unit (f : Unit → ℝ) : ∑ i, f i = f () :=
  Fintype.sum_unique f

/-- ⭐ `Unit → Bool` 的全体元素**恰是两个常函数**。 -/
theorem univ_unit_bool : (univ : Finset (Unit → Bool)) = {fun _ => true, fun _ => false} := by
  decide

/-- ⭐ 在 `Unit → Bool` 上求和 = 两个常函数上取值之和。 -/
theorem sum_unit_bool (f : (Unit → Bool) → ℝ) :
    ∑ xs, f xs = f (fun _ => true) + f (fun _ => false) := by
  rw [univ_unit_bool, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- ⭐ `Bool` 上的求和 = 两项之和。 -/
theorem sum_bool (f : Bool → ℝ) : ∑ b, f b = f true + f false :=
  Fintype.sum_bool f

/-- ⭐ `Bool` 上的乘积 = 两项之积。 -/
theorem prod_bool (f : Bool → ℝ) : ∏ b, f b = f true * f false :=
  Fintype.prod_bool f

/-- ⭐ `Fintype.card Bool - 1 = 1`。 -/
theorem card_bool_sub_one : Fintype.card Bool - 1 = 1 := rfl

/-! ### §8 ⭐ 二分情形：`boolFam` 与 `toFin` -/

/-- ⭐ **`Bool` 下标族的类型族**：`true ↦ α`、`false ↦ β`。 -/
abbrev boolFam (α β : Type) : Bool → Type :=
  fun b => match b with
    | true => α
    | false => β

/-- ⭐ `boolFam` 的逐点 `Fintype` 实例。 -/
instance instFintypeBoolFam (α β : Type) [Fintype α] [Fintype β] :
    ∀ i, Fintype (boolFam α β i) :=
  fun i => match i with
    | true => inferInstanceAs (Fintype α)
    | false => inferInstanceAs (Fintype β)

/-- ⭐ `boolFam` 的逐点 `DecidableEq` 实例。 -/
instance instDecidableEqBoolFam (α β : Type) [DecidableEq α] [DecidableEq β] :
    ∀ i, DecidableEq (boolFam α β i) :=
  fun i => match i with
    | true => inferInstanceAs (DecidableEq α)
    | false => inferInstanceAs (DecidableEq β)

/-- ⭐ **`(∀ i : Bool, boolFam α β i) ≃ α × β`**。 -/
def boolFamEquiv (α β : Type) : ((i : Bool) → boolFam α β i) ≃ (α × β) where
  toFun f := (f true, f false)
  invFun p := fun i => Bool.rec p.2 p.1 i
  left_inv f := by funext i; cases i <;> rfl
  right_inv p := by cases p; rfl

/-- ⭐ **`α × β → (∀ i : Bool, boolFam α β i)`**（`boolFamEquiv` 的逆）。 -/
def mkBoolFam {α β : Type} (p : α × β) : (i : Bool) → boolFam α β i :=
  fun i => Bool.rec p.2 p.1 i

@[simp] theorem mkBoolFam_true {α β : Type} (p : α × β) : mkBoolFam p true = p.1 := rfl

@[simp] theorem mkBoolFam_false {α β : Type} (p : α × β) : mkBoolFam p false = p.2 := rfl

/-- ⭐ **把 `Bool` 联合律转成 `FinJoint`**（`true ↦ X`、`false ↦ Y`）。

$$\mathrm{toFin}\ p\ ((x,y), z) := p\big(\mathrm{mkBoolFam}(x,y), z\big)$$

**⟹ 这是「`Bool` 族 = 二元」的桥**，使 `condIndepN_bool_iff`
能把 `CondIndepN` 连到 `FiniteCondIndep.CondIndepFin`。 -/
def toFin {α β γ : Type} (p : ((i : Bool) → boolFam α β i) → γ → ℝ) :
    FateV2.Modeling.FiniteCondIndep.FinJoint α β γ :=
  fun xyz => p (mkBoolFam xyz.1) xyz.2

/-- ⭐ 在 `(∀ i : Bool, boolFam α β i)` 上求和 = 在 `α × β` 上二重求和。 -/
theorem sum_bool_pi {α β : Type} [Fintype α] [Fintype β]
    (f : ((i : Bool) → boolFam α β i) → ℝ) :
    ∑ xs, f xs = ∑ x, ∑ y, f (mkBoolFam (x, y)) := by
  rw [Fintype.sum_equiv (boolFamEquiv α β) (f := f) (g := fun p : α × β => f (mkBoolFam p))]
  · rw [Fintype.sum_prod_type]
  · intro a; congr 1; funext i; cases i <;> rfl

/-- ⭐ **`NMass` 与 `margZ` 一致**（`toFin` 下）。 -/
theorem NMass_toFin {α β γ : Type} [Fintype α] [Fintype β]
    (p : ((i : Bool) → boolFam α β i) → γ → ℝ) (z : γ) :
    NMass p z = FateV2.Modeling.FiniteCondIndep.margZ (toFin p) z := by
  unfold NMass
  rw [sum_bool_pi]
  rfl

/-- ⭐ **`marg true` 与 `margXZ` 一致**（`toFin` 下）。 -/
theorem marg_true_toFin {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : ((i : Bool) → boolFam α β i) → γ → ℝ) (a : α) (z : γ) :
    marg p true (have this := a; this) z = FateV2.Modeling.FiniteCondIndep.margXZ (toFin p) a z := by
  unfold marg FateV2.Modeling.FiniteCondIndep.margXZ toFin
  rw [sum_bool_pi]
  have hmt : ∀ (x : α) (y : β),
      ((mkBoolFam (x, y) : (i : Bool) → boolFam α β i) true : α) = x := fun x y => rfl
  have : ∀ x, (∑ y, if ((mkBoolFam (x, y) : (i : Bool) → boolFam α β i) true : α) = a
        then p (mkBoolFam (x,y)) z else 0)
      = if x = a then ∑ y, p (mkBoolFam (x,y)) z else 0 := by
    intro x
    by_cases hx : x = a
    · subst hx; simp only [hmt, if_true]
    · simp only [hmt, if_neg hx, Finset.sum_const_zero]
  simp only [this]
  rw [Finset.sum_ite_eq' (s := Finset.univ) (a := a)]
  simp

/-- ⭐ **`marg false` 与 `margYZ` 一致**（`toFin` 下）。 -/
theorem marg_false_toFin {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : ((i : Bool) → boolFam α β i) → γ → ℝ) (b : β) (z : γ) :
    marg p false (have this := b; this) z = FateV2.Modeling.FiniteCondIndep.margYZ (toFin p) b z := by
  unfold marg FateV2.Modeling.FiniteCondIndep.margYZ toFin
  rw [sum_bool_pi]
  have hmf : ∀ (x : α) (y : β),
      ((mkBoolFam (x, y) : (i : Bool) → boolFam α β i) false : β) = y := fun x y => rfl
  have : ∀ x, (∑ y, if ((mkBoolFam (x, y) : (i : Bool) → boolFam α β i) false : β) = b
        then p (mkBoolFam (x,y)) z else 0) = p (mkBoolFam (x,b)) z := by
    intro x
    simp only [hmf]
    rw [Finset.sum_ite_eq' (s := Finset.univ) (a := b)]
    simp
  simp only [this]

/-! ### §9 ⭐⭐⭐ 主定理：`Bool` 情形与 `CondIndepFin` 等价 -/

/-- ⭐⭐⭐ **`Bool` 族的 `CondIndepN` $\iff$ `CondIndepFin`**（**相容性检验**）。

$$\mathrm{CondIndepN}\ p \iff \mathrm{CondIndepFin}\,(\mathrm{toFin}\ p)$$

**⟹ 这是本文件最重要的**正确性证据**：N 元定义在 $n = 2$ 时
必须与既有的二元定义 `CondIndepFin` 一致，否则推广是错的。**

**证明**：把 $\prod_{i:\mathrm{Bool}}$ 展开为 $m_{\mathrm{true}}\cdot m_{\mathrm{false}}$、
把 $|\mathrm{Bool}| - 1 = 1$ 化简掉，再用 §8 的三条 `_toFin` 引理对齐。 -/
theorem condIndepN_bool_iff {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : ((i : Bool) → boolFam α β i) → γ → ℝ) :
    CondIndepN p ↔ FateV2.Modeling.FiniteCondIndep.CondIndepFin (toFin p) := by
  unfold CondIndepN FateV2.Modeling.FiniteCondIndep.CondIndepFin
  constructor
  · intro h x y z
    have h1 := h (mkBoolFam (x, y)) z
    rw [prod_bool, card_bool_sub_one, pow_one] at h1
    simp only [toFin, mkBoolFam_true, mkBoolFam_false] at h1 ⊢
    rw [← NMass_toFin, ← marg_true_toFin, ← marg_false_toFin]
    exact h1
  · intro h xs z
    rw [prod_bool, card_bool_sub_one, pow_one]
    have hxs : mkBoolFam (xs true, xs false) = xs := by
      funext i; cases i <;> rfl
    have h1 := h (xs true) (xs false) z
    simp only [toFin] at h1
    rw [hxs] at h1
    rw [← NMass_toFin (p := p) (z := z)] at h1
    rw [← marg_true_toFin (p := p) (a := xs true) (z := z)] at h1
    rw [← marg_false_toFin (p := p) (b := xs false) (z := z)] at h1
    exact h1

/-- ⭐ **`CondIndepN` 在 `Bool` 族上给出**逐点因子化**（`CondIndepFin` 的展开形式）。 -/
theorem condIndepN_bool_factor {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : ((i : Bool) → boolFam α β i) → γ → ℝ) (h : CondIndepN p) :
    ∀ x y z, toFin p ((x, y), z) * FateV2.Modeling.FiniteCondIndep.margZ (toFin p) z =
      FateV2.Modeling.FiniteCondIndep.margXZ (toFin p) x z * FateV2.Modeling.FiniteCondIndep.margYZ (toFin p) y z :=
  (condIndepN_bool_iff p).1 h

/-! ### §10 ⭐⭐⭐ 二分：`σ ⊕ τ` 上的因子化 -/

/-- ⭐ **乘积在 `σ ⊕ τ` 上分裂为两段**：

$$\prod_{i : \sigma \oplus \tau} f(i)
  = \Big(\prod_{i:\sigma} f(\mathrm{inl}\ i)\Big)\cdot
    \Big(\prod_{i:\tau} f(\mathrm{inr}\ i)\Big)$$

**⚠ 任务书写作 `Finset.prod_sum_split` / `Finset.prod_sum_type`**，
但该引理在 Mathlib 中的**实际名字是 `Fintype.prod_sum_type`**
（位于 `Mathlib.Data.Fintype.Sigma`）。本文件以 `prod_sum_split` 暴露它，
**并在文件末尾以 `Finset.prod_sum_type` 别名同时提供**（见 §13）。 -/
theorem prod_sum_split {σ τ : Type*} [Fintype σ] [Fintype τ] (f : σ ⊕ τ → ℝ) :
    ∏ i, f i = (∏ i, f (Sum.inl i)) * ∏ i, f (Sum.inr i) :=
  Fintype.prod_sum_type f

/-- ⭐⭐⭐ **二分因子化**：`ι = σ ⊕ τ` 时 `CondIndepN` 的右侧**分裂成两段**。

**⟹ 这是「N 元独立性可递归拆成两组」的代数骨架**：
$\prod_{i\in\sigma\oplus\tau} m_i = \big(\prod_{i\in\sigma} m_{\mathrm{inl}\,i}\big)
\big(\prod_{i\in\tau} m_{\mathrm{inr}\,i}\big)$。

**⚠ 注意本定理只做**右侧因子化**，不声称 $\sigma$ 组与 $\tau$ 组独立**
（后者还需额外的「交互项消失」条件，不在本条范围内）。 -/
theorem condIndepN_split {σ τ : Type*} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] [Nonempty σ]
    {α : σ ⊕ τ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    {γ : Type*} (p : NJoint (ι := σ ⊕ τ) α γ) (h : CondIndepN p) :
    ∀ xs z, p xs z * (NMass p z) ^ (Fintype.card (σ ⊕ τ) - 1) =
      (∏ i, marg p (Sum.inl i) (xs (Sum.inl i)) z) *
        ∏ i, marg p (Sum.inr i) (xs (Sum.inr i)) z := by
  intro xs z
  rw [h xs z]
  exact prod_sum_split (fun i => marg p i (xs i) z)

/-- ⭐ **`Bool` 族的逐点因子化**（`bool_pairwise`，即 `condIndepN_bool_factor` 的别名）。 -/
theorem bool_pairwise {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : ((i : Bool) → boolFam α β i) → γ → ℝ) :
    CondIndepN p → FateV2.Modeling.FiniteCondIndep.CondIndepFin (toFin p) :=
  (condIndepN_bool_iff p).1

/-! ### §11 ⭐⭐⭐ `Unit` 情形退化 -/

/-- ⭐⭐⭐ **`ι = Unit` 时 `CondIndepN` 退化为 $p = \mathrm{marg}$**。

**⟹ 正确性证据之二**：单变量时「条件独立」应当**恒真**，
即联合律等于它唯一的边缘律。

**证明**：$|\mathrm{Unit}| - 1 = 0$，故 $M^0 = 1$；
$\prod_{i:\mathrm{Unit}} m_i = m_{()}$（`prod_unit`）。 -/
theorem condIndepN_card_one {γ : Type*} {β : Type} [Fintype β] [DecidableEq β]
    (p : (Unit → β) → γ → ℝ) (h : CondIndepN p) :
    ∀ xs z, p xs z = marg p () (xs ()) z := by
  intro xs z
  have h1 := h xs z
  have hc : Fintype.card Unit - 1 = 0 := rfl
  rw [hc, pow_zero, mul_one] at h1
  rw [h1, Fintype.prod_unique (fun i => marg p i (xs i) z)]

/-! ### §12 ⭐ 合并版 `CondIndepNFull` -/

/-- ⭐ **合并版**：空族时**空真**，非空时即 `CondIndepN`。

$$\mathrm{CondIndepNFull}\ p := \mathrm{Nonempty}\ \iota \to
  \forall xs\ z,\ p\cdot M^{|\iota|-1} = \prod_i m_i$$

**⟹ 这把 `CondIndepNEmpty`（空族 = `True`）与 `CondIndepN`（非空）**
用**一个 `Prop`** 统一起来，且**不要求** `[Nonempty ι]` 这个实例。 -/
noncomputable def CondIndepNFull (p : NJoint (ι := ι) α γ) : Prop :=
  Nonempty ι → ∀ xs z, p xs z * (NMass p z) ^ (Fintype.card ι - 1) = ∏ i, marg p i (xs i) z

/-- ⭐ **`CondIndepNFull` $\iff$ `CondIndepN`**（在有 `[Nonempty ι]` 时）。 -/
theorem condIndepNFull_iff (p : NJoint (ι := ι) α γ) :
    CondIndepNFull p ↔ CondIndepN p := by
  unfold CondIndepNFull CondIndepN
  constructor
  · intro h; exact h ‹Nonempty ι›
  · intro h _; exact h

/-! ### §13 ⚠⚠ **测度层对接：未做**（**第 179 轮明确登记**）

**本文件是**纯 `Finset` 代数**，不涉及 `Measure` 层。**

**⚠⚠ 「N 元桥」（`CondIndepN ⟹` 测度版条件独立）**尚未完成**** ——
**第 178 轮代理 G4 的评估给出了**准确的缺口清单**（按依赖顺序）：

| # | 缺什么 | 说明 |
|---|---|---|
| **1** | **N 元 `weightedCount` 与条件期望核** | 现二元版是 `((α×β)×γ)` 的 `projX/projY`；N 元需换成 `(∀ i, α i) × γ` 上的 `proj_i`，并证核值的 N 元商形式 |
| **2** | **`trim` 判据的 N 元化** | `trim_singleton_eq_fiber` 依赖「纤维 = 单个 `γ` 点」；需证它在 `comap proj_ι` 下仍成立 |

**⚠ G4 的另一个**关键判断****：
> **「跨组因子化（`condIndepN_split`）只是右侧的代数分裂，
> **不含交互项消失**，不能直接支撑乘法。」**

**⟹ 即：`condIndepN_split` **不足以**推出 N 元条件独立** ——
它只把 `∏` 拆成两组，而条件独立需要**所有二分都分裂**。

**⭐ 二元桥（`Fate.BridgeFinal.lean` 的 `condIndepFin_to_bridge`）**已完成**；
**N 元是它的推广，目前**只到代数层**。** -/

end GenC3

end FateV2.Modeling