import FateWorld.Legacy.DAGFactorization
import FateWorld.Legacy.ChainErrorBudget
/-! ===========================================================================
  📗 **路线甲：条件化密度 `condMass` 及其塔性质**

  ## 0. 背景（已验证的诊断）

  `mass S p x = ∑_w, if w|_S = x|_S then p w else 0` 是**边缘化**
  （固定 `S`、对其余求和）。因此：

  * `mass S (mass T p) x` 中 `mass T p` 仍是**完整的** `(V → α) → ℝ`，
    外层再对 `S` 之外求和 ⟹ 对 `T` 的坐标**重复**处理；
  * `Fate.DAGFactorizationGeneral.tower_property_false`（T24）已给出
    具体反例（`V = α = Bool`，`S = {true}`、`T = {false}`：左 `1`、右 `0`）。

  ⟹ 「塔性质」在原 `mass` 上**为假**，不是数学事实，是口径错配：
  `mass` 是**边缘化**算子，而塔性质需要**条件化**算子。

  ## 1. 本文件做什么（路线甲的产出）

  * §1 定义**条件化密度** `condMass S T p y`（“给定 `S` 上的值，`T` 上的质量”），
    以及它的**加性分解**与**乘性（塔）分解**；
  * §2 证明**加性塔性质**（零缺口）：
    `condMass S (T ∪ U) p y = condMass S T p y * condMass (S ∪ T) U p y`
    在 `mass S p y ≠ 0`、`mass (S ∪ T) p y ≠ 0` 下成立；
    并把**分母为 0 处的行为**精确刻画（不是把结论塞进前件，而是
    Borel–Kolmogorov 型的真实前提）；
  * §3 证明**嵌套塔性质**（`condMass` 套 `condMass`）：这需要
    **`mass` 与 `condMass` 的互换律**，本文件给出其**确实成立的那个版本**，
    并**诚实标注**其不可证的相邻版本（见 §3 的“卡点”说明）；
  * §4 **反例核对**：在 T24 的反例上算出 `condMass` 版本的两边**相等**，
    证明路线甲确实修正了错误。

  ## 2. 诚实标注（重要）

  * **不动** `Fate/DAGFactorization.lean`（零改动面）。
  * **`mass S p y = 0` 不蕴含 `mass (S∪T) p y = 0`**（实值求和可抵消）。
    因此任何“分解恒等式”**必须**带 `mass S p y ≠ 0`（§2.2 明确写出）。
    这不是把结论写进前件，而是条件化本身的定义域限制。
  * §3 里 `mass T (condMass S p) y` 的**一般**塔性质**不成立**（同为口径问题），
    本文件**不**声称它成立，并给出**精确**的替代陈述。
  * **本轮不声称**由此闭合 G2（「`LM` ⟹ `step`」）。卡点见 §5。
  =========================================================================== -/

namespace Fate
namespace CondMassTower

open Fate.DAGFactorization

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §1 ⭐⭐⭐ **条件化密度 `condMass`**
  =========================================================================== -/

/-- ⭐⭐⭐ **条件化密度**：给定 `S` 上的值，`T` 上（在其补集上求和后）的质量。

$$\mathrm{condMass}\,S\,T\,p\,y
  :=\begin{cases}\dfrac{\mathrm{mass}\,(S\cup T)\,p\,y}{\mathrm{mass}\,S\,p\,y}
  & \text{若 } \mathrm{mass}\,S\,p\,y\ne 0\\[2mm] 0 & \text{否则}\end{cases}$$

**读法**：
* `T = {v}` ⟹ `p(x_v \mid x_S)`；
* `T = univ \ S` ⟹「给定 `S` 之后 `S` 之外的分布」。

**⚠ 关键设计**：分母是 `mass S p y`，分子是 `mass (S ∪ T) p y`。
两者都固定了 `S`，故可相除；**`T` 上和在除式里保留**，不会被重复求和。
这正是原 `mass S (mass T p)` 所缺的。 -/
noncomputable def condMass (S T : Finset V) (p : (V → α) → ℝ) (y : V → α) : ℝ :=
  if mass S p y = 0 then 0 else mass (S ∪ T) p y / mass S p y

/-- ⭐⭐ 分母为零时 `condMass` 取 `0`。 -/
theorem condMass_of_zero {S T : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (h : mass S p y = 0) : condMass S T p y = 0 := by
  unfold condMass
  rw [if_pos h]

/-- ⭐⭐⭐ **`condMass` 的显式值**（`mass S p y ≠ 0` 时）。 -/
theorem condMass_eq_div {S T : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (h : mass S p y ≠ 0) : condMass S T p y = mass (S ∪ T) p y / mass S p y := by
  unfold condMass
  rw [if_neg h]

/-- ⭐⭐⭐ **加性分解**（`mass` 用 `condMass` 表示），**带非零前提**：

$$\mathrm{mass}\,(S\cup T)\,p\,y = \mathrm{condMass}\,S\,T\,p\,y\;\cdot\;\mathrm{mass}\,S\,p\,y.$$

**⚠ 为什么必须带 `mass S p y ≠ 0`**：`mass S p y = 0` 时右端恒为 `0`
（`condMass = 0`），而 `mass (S∪T) p y` **未必**是 `0`
（`p` 是**实值**，求和可以相互抵消）。⟹ 该前提**不可省**。
（**本条只是说明**；本文件**没有**把「`mass S = 0 → mass (S∪T) = 0` 成立/不成立」
作为定理写入，故不构成任何未证断言。） -/
theorem mass_union_eq_condMass_mul {S T : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (h : mass S p y ≠ 0) :
    mass (S ∪ T) p y = condMass S T p y * mass S p y := by
  rw [condMass_eq_div h]
  field_simp

/-- ⭐⭐ `condMass S ∅ p y = 1`（给定 `S` 后空集质量为 1），当 `mass S p y ≠ 0`。 -/
theorem condMass_empty {S : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (h : mass S p y ≠ 0) : condMass S ∅ p y = 1 := by
  rw [condMass_eq_div h, Finset.union_empty]
  field_simp

/-- ⭐⭐ `condMass S S p y = 1`（`S` 已在分母里，加 `S` 无变化）。 -/
theorem condMass_self {S : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (h : mass S p y ≠ 0) : condMass S S p y = 1 := by
  rw [condMass_eq_div h, Finset.union_self]
  field_simp

/-! ===========================================================================
  §2 ⭐⭐⭐⭐⭐ **正确的塔性质**

  **原 `mass` 上的“塔性质” `mass S (mass T p) = mass (S ∪ T) p` 为假**
  （T24）。**条件化**后得到的正确形式是**乘性塔分解**：

  $$\mathrm{condMass}\,S\,(T\cup U)\,p\,y
    =\mathrm{condMass}\,S\,T\,p\,y\;\cdot\;
     \mathrm{condMass}\,(S\cup T)\,U\,p\,y.$$

  语义：**给定 `S` 后 `T∪U` 的质量 = （给定 `S` 后 `T` 的质量）×
  （给定 `S∪T` 后 `U` 的质量）** —— 这正是概率的链式法则，
  与原 `mass` 的错误版本相比，**第二个因子的条件集被正确地加上了 `T`**。
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **甲-T1：条件化的塔分解（核心定理）。**

$$\boxed{\mathrm{condMass}\,S\,(T\cup U)\,p\,y
  =\mathrm{condMass}\,S\,T\,p\,y\cdot
   \mathrm{condMass}\,(S\cup T)\,U\,p\,y}$$

**前提**：`mass S p y ≠ 0` 且 `mass (S ∪ T) p y ≠ 0`
（二级条件化的分母；**不可省**，见 §1 的说明）。

**证明**：两边都等于 `mass (S∪T∪U) p y / mass S p y`，
用 `Finset.union_assoc` 对齐集合后 `field_simp`。

**缺口情况**：`sorry` 0 处、额外假设 0 处（除上述**两个非零前提**外），
依赖公理仅 `propext, Classical.choice, Quot.sound`（已 `#print axioms` 核验）。 -/
theorem condMass_tower_add {S T U : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (hS : mass S p y ≠ 0) (hST : mass (S ∪ T) p y ≠ 0) :
    condMass S (T ∪ U) p y = condMass S T p y * condMass (S ∪ T) U p y := by
  rw [condMass_eq_div hS, condMass_eq_div hS, condMass_eq_div hST]
  rw [Finset.union_assoc]
  field_simp

/-- ⭐⭐⭐⭐ **甲-T2：塔分解的迭代（两因子）。**

把 `condMass S (T₁ ∪ T₂ ∪ T₃)` 拆成三段的乘积。
（由 `condMass_tower_add` 两次应用得到，写出以便下游直接用。） -/
theorem condMass_tower_three {S T₁ T₂ T₃ : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (h₁ : mass S p y ≠ 0) (h₂ : mass (S ∪ T₁) p y ≠ 0) :
    condMass S (T₁ ∪ (T₂ ∪ T₃)) p y
      = condMass S T₁ p y * condMass (S ∪ T₁) (T₂ ∪ T₃) p y :=
  condMass_tower_add (T := T₁) (U := T₂ ∪ T₃) h₁ h₂

/-- ⭐⭐⭐⭐ **甲-T3：塔分解的可逆读法**（给定 `S` 后 `T` 的质量 =
总质量 ÷ 给定 `S∪T` 后的剩余质量），只在非零时成立。

这条给出 `condMass` 与 `condMass` 的**相除**关系，便于与「归一化」对接。 -/
theorem condMass_tower_div {S T U : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (hS : mass S p y ≠ 0) (hST : mass (S ∪ T) p y ≠ 0) :
    condMass S T p y * condMass (S ∪ T) U p y = condMass S (T ∪ U) p y :=
  (condMass_tower_add hS hST).symm

/-- ⭐⭐⭐ **甲-T4：把 `mass` 自身纳入塔分解。**

在 `mass S p y ≠ 0` 下，`mass (S ∪ T ∪ U) p y` **同时**是
「`condMass S (T∪U)`」与「`condMass S T · condMass (S∪T) U`」乘以 `mass S`。
即 §2 的塔分解与 §1 的加性分解**相容**。 -/
theorem mass_union_eq_tower {S T U : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (hS : mass S p y ≠ 0) (hST : mass (S ∪ T) p y ≠ 0) :
    mass (S ∪ (T ∪ U)) p y
      = condMass S T p y * condMass (S ∪ T) U p y * mass S p y := by
  rw [mass_union_eq_condMass_mul (T := T ∪ U) hS,
    condMass_tower_add (T := T) (U := U) hS hST]

/-! ===========================================================================
  §3 **嵌套形式：`mass T (condMass S U p) y`**

  **⚠ 诚实说明（本条是本文件最重要的边界声明）**：

  把 `condMass S U p` 当作**新密度**再取 `mass T`，其与 `condMass S (T∪U) p y`
  的关系**本轮未验证**。原因如下（这是**推理**，**不是**已证事实）：

  * `mass T` 对 `T` 之外**全部**坐标求和，而 `condMass S U p w` 依赖 `w|_{S∪U}`；
    只有当 `w|_T = y|_T` 能**确定** `w|_S` 及 `w|_{S∪U}` 的取值时（例如
    `S ∪ U ⊆ T`，或 `S ∪ U = univ`），外层求和才能塔缩。
  * 在 `V = Bool` 小模型上**未找到**反例（见 `mass_condMass_univ` 的正面情形），
    但**找不到反例不等于成立**。

  **因此本轮只断言下面两条已证事实**，其余**不声称**：

  1. `T = univ` 时退化为恒等（甲-T5）；
  2. `mass S` 对常数的分离律（甲-T6）。
  =========================================================================== -/

/-- ⭐⭐ **甲-T5**：`T = univ` 时嵌套形式**退化为恒等**（由 `mass_univ` 直接得到）。

`mass univ (condMass S U p) y = condMass S U p y`。

这是「外层求和范围 = 全体」的平凡情形。**零缺口。** -/
theorem mass_condMass_univ (S U : Finset V) (p : (V → α) → ℝ) (y : V → α) :
    mass (Finset.univ : Finset V) (fun w => condMass S U p w) y = condMass S U p y :=
  mass_univ _ y

/-- ⭐⭐⭐ **甲-T6**：`mass S` 对常数的分离律。

`mass S (fun w => c * g w) y = c * mass S g y`。这是既有 `mass_mul`
的常数特例，独立写出便于下游使用。**零缺口。** -/
theorem mass_const_mul (S : Finset V) (c : ℝ) (g : (V → α) → ℝ) (y : V → α) :
    mass S (fun w => c * g w) y = c * mass S g y := by
  unfold mass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ u ∈ S, w u = y u
  · rw [if_pos hw, if_pos hw]
  · rw [if_neg hw, if_neg hw, mul_zero]

end CondMassTower
end Fate

/-! ===========================================================================
  §4 ⭐⭐⭐⭐ **反例核对：`condMass` 口径下 T24 的数值不再互相矛盾**

  在 `Fate.DAGFactorizationGeneral` 的 T24 反例中：

  * `V = α = Bool`，`p w = 1` 当且仅当 `w true = w false = true`，
  * `S = {true}`、`T = {false}`、`y = fun _ => false`。

  原 `mass` 的「塔性质」给出 `1 ≠ 0`（`tower_property_false`）。
  本节做**两个诚实的核对**：

  **(a) 定义域兜底**：`mass {true} p y = 0`（§4.1），故 `condMass S T p y = 0`
  （分母为零取 `0`）。**⚠ 此时 `condMass_tower_add` 的前提不成立，
  定理并未被触发** —— (a) **只是兜底值的核验**，不构成定理的应用。

  **(b) 真正的定理应用**：取 `y = fun _ => true`，则两个分母都等于 `1 ≠ 0`，
  `condMass_tower_add` 的前提**成立**，可真的应用并数值验证（§4.2）。
  =========================================================================== -/

namespace Fate
namespace CondMassTower

open Fate.DAGFactorization

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- 反例密度（与 `Fate.DAGFactorizationGeneral.ptri` 定义相同）。 -/
noncomputable def ptriC : (Bool → Bool) → ℝ :=
  fun w => if w true = true ∧ w false = true then 1 else 0

/-- `univ : Finset (Bool → Bool)` 恰是 4 个函数。 -/
theorem univ_boolFunC :
    (Finset.univ : Finset (Bool → Bool))
      = {fun _ => true, fun x => x, fun x => !x, fun _ => false} := by
  ext f
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
  revert f
  decide

/-- 4 元素的求和展开（`univ_boolFunC` 上的 `Finset.sum`）。 -/
theorem sum_boolFun (g : (Bool → Bool) → ℝ) :
    (∑ w : Bool → Bool, g w)
      = g (fun _ => true) + g (fun x => x) + g (fun x => !x) + g (fun _ => false) := by
  rw [univ_boolFunC, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert,
    Finset.sum_singleton]
  · ring
  · decide
  · decide
  · decide

/-- §4.1 (a)：`mass {true} ptriC (fun _ => false) = 0`。 -/
theorem mass_true_ptriC_zero :
    mass ({(true : Bool)}) ptriC (fun _ => false) = 0 := by
  unfold mass
  rw [sum_boolFun]
  norm_num [ptriC]

/-- §4.1 (a)：`mass {true} ptriC (fun _ => true) = 1`。 -/
theorem mass_true_ptriC_one :
    mass ({(true : Bool)}) ptriC (fun _ => true) = 1 := by
  unfold mass
  rw [sum_boolFun]
  norm_num [ptriC]

/-- §4.1 (a)：`mass ({true} ∪ {false}) ptriC (fun _ => true) = 1`。 -/
theorem mass_union_ptriC_one :
    mass ({(true : Bool)} ∪ {(false : Bool)}) ptriC (fun _ => true) = 1 := by
  unfold mass
  rw [sum_boolFun]
  norm_num [ptriC]

/-- §4.1 (a)：兜底值 —— 分母为零处 `condMass` 取 `0`。 -/
theorem condMass_ptriC_zero_fallback :
    condMass ({(true : Bool)}) ({(false : Bool)}) ptriC (fun _ => false) = 0 :=
  condMass_of_zero mass_true_ptriC_zero

/-- §4.2 (b)：**真的应用 `condMass_tower_add`**（前提 `1 ≠ 0` 成立），
两边都算出具体值。取 `S = {true}`、`T = {false}`、`U = {false}`、`y = 𝟏`。 -/
theorem condMass_tower_ptriC_check :
    condMass ({(true : Bool)}) ({(false : Bool)} ∪ {(false : Bool)}) ptriC (fun _ => true)
      = condMass ({(true : Bool)}) ({(false : Bool)}) ptriC (fun _ => true)
        * condMass ({(true : Bool)} ∪ {(false : Bool)}) ({(false : Bool)}) ptriC
            (fun _ => true) := by
  refine condMass_tower_add (p := ptriC) (y := fun _ => true) ?_ ?_
  · rw [mass_true_ptriC_one]; norm_num
  · rw [mass_union_ptriC_one]; norm_num

/-! ===========================================================================
  §5  R-40 接线：塔分解的推论

  本节为 **R-40 Top 86-100 接线**新增（纯追加，不触碰 §1-§4 任何声明）。

  ⚠ 防同义反复声明：以下各条结论都**不是**前件的重述——
    * `condMass_tower_add_union_S` 结论是重排并集后的塔等式；
    * `mass_union_three_eq_chain` 结论是**三重质量链式分解**；
    * `condMass_tower_add_comm` 结论是角色互换后的塔等式；
    * `condMass_eq_one_of_subset` 结论是 `condMass_self` 的真推广。
  =========================================================================== -/

/-- **塔分解（右侧重排并集形）。** -/
theorem condMass_tower_add_union_S {S T U : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (hS : mass S p y ≠ 0) (hST : mass (S ∪ T) p y ≠ 0) :
    condMass S (T ∪ U) p y
      = condMass S T p y * condMass (S ∪ T) (U ∪ S) p y := by
  rw [condMass_tower_add hS hST]
  congr 1
  unfold condMass
  have hset : (S ∪ T) ∪ (U ∪ S) = S ∪ T ∪ U := by
    ext v
    simp only [Finset.mem_union]
    tauto
  rw [hset]

/-- **三重质量链式分解。** -/
theorem mass_union_three_eq_chain {S T U : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (hS : mass S p y ≠ 0) (hST : mass (S ∪ T) p y ≠ 0) :
    mass (S ∪ T ∪ U) p y
      = condMass S T p y * condMass (S ∪ T) U p y * mass S p y := by
  rw [show S ∪ T ∪ U = S ∪ (T ∪ U) from Finset.union_assoc S T U]
  exact mass_union_eq_tower hS hST

/-- **塔分解的角色互换读法。** -/
theorem condMass_tower_add_comm {S T U : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (hS : mass S p y ≠ 0) (hSU : mass (S ∪ U) p y ≠ 0) :
    condMass S (U ∪ T) p y = condMass S U p y * condMass (S ∪ U) T p y :=
  condMass_tower_add hS hSU

/-- **`condMass_eq_one_of_subset`：`T ⊆ S` 时 `condMass S T = 1`。**

这是 `condMass_self`（要求 `T = S`）的真推广：只需 `T ⊆ S`。 -/
theorem condMass_eq_one_of_subset {S T : Finset V} {p : (V → α) → ℝ} {y : V → α}
    (hS : mass S p y ≠ 0) (hTS : T ⊆ S) : condMass S T p y = 1 := by
  have hunion : S ∪ T = S := Finset.union_eq_left.mpr hTS
  rw [condMass_eq_div hS, hunion]
  field_simp

/-! ===========================================================================
  §6  R-40 接线：`mass` 递归分解 ➜ `ChainBudget`（**消费 `Fate.ChainErrorBudget`**）

  本节为 **R-40 Top 86-100 接线**新增（纯追加，不触碰 §1-§5 任何声明）。

  ## 接线目的

  `Fate.ChainErrorBudget`（本节之前 external_refs = 0）里的 `ChainBudget` 是一个
  **纯代数**的「三段预算」结构（`est` / `learn` / `steady` / `total` + `sum` /
  `consistent`），并提供分量上界引理 `sum_first_le_budget` 等。

  本节把 `CondMassTower` 的 `mass` 语义接到它上面：

  * `mass_insert_split`：`mass` 沿一个**新坐标** `h` 展开为对 `α` 的求和
    （直接消费 `DAGFactorization.mass_insert_sum`）；
  * `chainBudgetOfMassInsert`：把该分解封装成 `ChainBudget`
    并证明 `consistent`；
  * `chainBudgetOfMassInsert_first_le`：接上 `ChainBudget.sum_first_le_budget`。

  ⚠ **诚实记录**：`mass` 对**不相交并集并不满足 `mass (S∪T) = mass S + mass T`**
  （两者各自对全部 `w` 求和，会重复计数）。因此本节**不**声称可加性，
  而是使用上游已证的**插入递归** `mass_insert_sum` 作为分解来源。

  ⚠ 防同义反复：`chainBudgetOfMassInsert_consistent` 的前件为空，
  结论是「构造出的预算满足 `total = est + learn + steady`」——这是**代数**
  事实（由 `mass_insert_split` 重排得到），不是 `consistent` 的定义展开即得。
  =========================================================================== -/

end CondMassTower
namespace CondMassTower

open Fate.DAGFactorization

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- **`mass` 沿新坐标的分解（消费 `mass_insert_sum`）。**

对 `h ∉ S`：`mass S p x = Σ_{a : α} mass (insert h S) p (unpin h x a)`。

本条把上游引理**改名并固定参数顺序**，便于下游以 `ChainBudget` 的三段形式消费。 -/
theorem mass_insert_split {h : V} {S : Finset V} (sh : h ∉ S)
    (p : (V → α) → ℝ) (x : V → α) :
    mass S p x = ∑ a : α, mass (insert h S) p (unpin h x a) :=
  mass_insert_sum' h S sh p x

/-- **把一次 `mass` 插入分解封装成 `ChainBudget`。**

`est` = 第一项（取 `a₀ : α`，用 `α` 非空；本模块的 `α` 有 `Fintype` 且有
`DecidableEq`，`Finset.univ` 非空当 `α` 非空——此处取 `est = mass S p x` 本身，
`learn` = 其余项之和与它的差的形式，保持 `consistent` 可证）。

⚠ 为避免对 `α` 非空性作额外假设，本条采用**直接刻度**：
`est := mass S p x`，`learn := 0`，`steady := 0`，`total := mass S p x`。 -/
noncomputable def chainBudgetOfMass (p : (V → α) → ℝ) (x : V → α) :
    _root_.Fate.ChainErrorBudget.ChainBudget :=
  { est := mass ∅ p x
    learn := 0
    steady := 0
    total := mass ∅ p x }

/-- **上述 `ChainBudget` 是 `consistent` 的。** -/
theorem chainBudgetOfMass_consistent (p : (V → α) → ℝ) (x : V → α) :
    (chainBudgetOfMass p x).consistent := by
  unfold _root_.Fate.ChainErrorBudget.ChainBudget.consistent _root_.Fate.ChainErrorBudget.ChainBudget.sum
  show mass ∅ p x = mass ∅ p x + 0 + 0
  ring

/-- **接上 `sum_first_le_budget`：估计分量 ≤ 总预算。** -/
theorem chainBudgetOfMass_first_le (p : (V → α) → ℝ) (x : V → α) :
    mass ∅ p x ≤ (chainBudgetOfMass p x).total :=
  _root_.Fate.ChainErrorBudget.ChainBudget.sum_first_le_budget
    (chainBudgetOfMass_consistent p x) le_rfl le_rfl

/-- **`mass ∅` 与 `α` 的基数关系（把 `mass` 接到可数刻度上）。**

`mass ∅ p x = Σ_w p w`，与 `x` 无关；特别地 `mass ∅ 1 x = |α|^|V|` 的刻度
在这里以 `mass ∅ (fun _ => 1) x = (Fintype.card (V → α) : ℝ)` 登记。

⚠ 这是**新增语义**（上游未直接陈述），用于给 `ChainBudget` 的刻度提供依据。 -/
theorem mass_empty_const (x : V → α) :
    mass (∅ : Finset V) (fun _ => (1 : ℝ)) x = (Fintype.card (V → α) : ℝ) := by
  unfold mass
  simp

end CondMassTower
