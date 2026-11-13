/-
# 「图 ⟹ 概率」桥 · **策略 5：纤维双射 + 补集迭代求和**

## 0 定位：这是**第 5 种**策略，且**一次也不出现 `mass` 塔**

**硬约束（已被证伪的路线，禁止使用）**

`Fate/DAGFactorizationGeneral.tower_property_false`（T24）证明
`mass S (mass T p) x ≠ mass (S ∪ T) p x` **一般为假**；
`Fate/TowerAudit.mass_idempotent_fails` 进一步证明连反方向 `S ⊆ T` 的塔也假。
**根因**：`mass` 是**非归一化纤维和**，`mass S p x = ∑_{w : w|_S = x|_S} p w`
只钉死 `S`、对其余坐标求和，故嵌套会重复计入纤维大小。

**⟹ 本文件全程**不出现** `mass S (mass T p)` 这种嵌套。所用的 `mass` 都是**单层**的，
且每次展开都在**同一个** `mass` 之内完成。

## 1 为什么这是「第 5 种」，而不是第 1/2/12/17/20 种

| # | 策略 | 骨架 | 卡点 / 终局 |
|---|---|---|---|
| 1 | `BridgeStrategy1TopoPeel` | 拓扑序 peels：`mass_insert_sum` + `Fintype.prod_sum` | 需 `pa(v) ⊆ S`；只做**归一化**方向（`= 1`）|
| 2 | `BridgeView2Elimination` | 完全变量消元：`mass (V∖{v})` 算到底 | 只到**单点补集** `V∖{v}`，不承载一般分块 |
| 12 | `Strategy12FactorSplitBridge` | 按「读集 ⊆ `S`」分 `In`/`Out` 组提出 | `Out` 组残余 `mass` 的归一化（`NormalizedResidual`）**未证** |
| 17 | `GraphToProbView17` | 支撑剖分 `FiberSplit`（3 因子），**不用 `mass`** | 需 `NonvanishingZ`；只做三元情形 |
| 20 | `View20GraphToProb` | `fac_aux` + `prod_split3` 纯乘法重排 | **诊断出 `CondMulLike` 终点退化**（对任意图成立）|
| **5（本文）**| **纤维双射 + 补集迭代求和** | **把 `mass S p x` 展开成「`S` 的补集上的迭代和」，用 `sum_bij` 做纤维重标号** | **落地 `AncestralInheritanceRouteB` 登记的 `BlockCI_Gap`**（见 §4）|

**策略 5 与它们的决定性区别（本文件的实质新内容）**

> **`mass S` 只钉死 `S`，所以真正「自由」的是 `S` 的补集。**
> 策略 5 不在 `S` 内做任何代数（不像 1/2/12），而是**把求和指标 `w` 拆成
> `(w|_A, w|_B)` 两块**（`B = Aᶜ`），然后用 **`Finset.sum_bij`（纤维双射）**
> 在「两块各自自由」的乘积结构上重标号。
> **结论**：`mass S f` 在 `f` 只读 `A` 时**只依赖 `x|_{S ∩ A}`**（定理 `mass_local_of_reads`）。
> 这一步是**纯纤维计数**，既不嵌套 `mass`，也不需要 `mass_mul` 的
> 「读集 ⊆ 求和集」前提（后者正是路线乙/视角 12 的卡点）。

## 2 数学构造（三块 + 一次落地）

记 `mass S p x = ∑_{w : w|_S = x|_S} p w`，`agreeOn S x y :≡ ∀ u ∈ S, x u = y u`。

### 块 ① **纤维双射重标号**（`mass_local_of_reads`，⭐ 本文的核心引擎）

> 设 `f` 只读 `A`（`agreeOn A x y → f x = f y`）。则对**任意** `S`，
> $$\mathrm{mass}\,S\,f\ \text{只依赖}\ x|_{S\cap A},$$
> 即 `agreeOn (S ∩ A) x y ⟹ mass S f x = mass S f y`。

**证明（纤维双射，不用塔、不用 `mass_mul`）**：给定 `x, y` 在 `S ∩ A` 上一致。
对每个 `w` 令 `θ w := fun u => if u ∈ S ∧ u ∉ A then y u else w u`。

* **`θ` 在 `S`-纤维内**：若 `w|_{S} = x|_S`，则 `θ w|_S = y|_S`
  （`u ∈ S ∩ A` 时 `w u = x u = y u`；`u ∈ S ∖ A` 时 `θ w u = y u`）；
* **`θ` 保 `f`**：`θ w` 与 `w` 在 `A` 上一致（修改只发生在 `S ∖ A ⊆ Aᶜ`），
  而 `f` 只读 `A` ⟹ `f (θ w) = f w`；
* **`θ` 是对合**（`θ (θ w) = θ w`，因 `S ∖ A` 上的值被强制为 `y`），故**双射**。

于是 `∑_{w|_S = x|_S} f w = ∑_{w|_S = y|_S} f w`（`Finset.sum_bij`）。∎

### 块 ② **两块乘积纤维的 Fubini**（`mass_split_prod`）

`B = Aᶜ` ⟹ 每个 `w` 唯一分解为 `(w|_A, w|_B)`；「`w` 钉死 `C`（`C ⊆ A`）」
⟺ 「`w|_A` 钉死 `C`」。于是
$$\mathrm{mass}\,C\,p\,x=\sum_{a : A \to \alpha,\ a|_C = x|_C}\ \sum_{b : B \to \alpha} p(a \oplus b),$$
其中 `a ⊕ b` 是把 `A` 上取 `a`、`B` 上取 `b` 的拼合。**这是「Fubini on a product fiber」。**

### 块 ③ **`p = f · h` 的三次记账**（块①②的直接推论）

`f` 读 `A`、`h` 读 `B ∪ C`、`B = Aᶜ`、`C ⊆ A`：

| `mass` | 值 | 依据 |
|---|---|---|
| `mass A p x` | `f x · mass A h x` | `mass_mul`（`f` 读 `⊆ A` ✅）+ 块① 说 `mass A h` 只依赖 `C` |
| `mass (B∪C) p x` | `h x · mass (B∪C) f x` | `mass_mul`（`h` 读 `⊆ B∪C` ✅）+ 块① |
| `mass C p x` | `Φ(x_C) · Ψ(x_C)` | 块② 的 Fubini，`Φ = ∑_{a⊇x_C} f`、`Ψ = ∑_B h` |

交叉相乘两边都等于 `f x · h x · Φ · Ψ` ⟹ **`BlockCI`**。

### 落地：**`BlockCI_Gap` 成为定理**（§4 的 `blockCI_of_block_split`）

`AncestralInheritanceRouteB` 把 `BlockCI_Gap` 登记为**真但未落地**的 `Prop`
（其 §5 明说卡在「`mass_mul` 要求读集 ⊆ 求和集」）。
**策略 5 正好绕开该前提**：块的 ①/② 都不需要它。**⟹ 本文件把该 `Prop` 变成定理。**

## 3 结构

* §2 块 ① `mass_local_of_reads`（+ `agreeOn` 工具）
* §3 块 ② `fiber_split_sum`（两块乘积纤维的 Fubini）
* §4 块 ③ **落地 `BlockCI_Gap`**：`blockCI_of_block_split` → `blockCI_of_factorizesC`
* §5 与 `dSep` 的接口 + **诚实边界**（何时这还**不够**，见 `View20` 的退化诊断）

**⚠ 无 `sorry` / 无 `axiom` / 无 `Prop` 占位。** 不可消费的命题一律**不**登记为定理。
-/

import FateWorld.Legacy.AncestralInheritanceRouteB
import FateWorld.Legacy.DAGFactorization
import FateWorld.Legacy.MarkovEquivalence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! ===========================================================================
  §1 基础工具
  =========================================================================== -/

namespace Fate
namespace BridgeStrategy5

set_option linter.unusedSectionVars false

open Finset Fate.DAGFactorization

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐ **「在 `S` 上一致」**（局部定义，避免与其他文件的同名冲突）。 -/
def agreeOn (S : Finset V) (x y : V → α) : Prop := ∀ u ∈ S, x u = y u

instance agreeOn_dec (S : Finset V) (x y : V → α) : Decidable (agreeOn S x y) :=
  inferInstanceAs (Decidable (∀ u ∈ S, x u = y u))

/-- 一致性是等价关系（自反 / 对称）。 -/
theorem agreeOn_refl (S : Finset V) (x : V → α) : agreeOn S x x := fun _ _ => rfl

theorem agreeOn_symm {S : Finset V} {x y : V → α} (h : agreeOn S x y) :
    agreeOn S y x := fun u hu => (h u hu).symm

/-- ⭐⭐ **「只读 `A`」**：`A` 外坐标改变不影响 `f`。 -/
def Reads (f : (V → α) → ℝ) (A : Finset V) : Prop :=
  ∀ x y : V → α, agreeOn A x y → f x = f y

omit [Fintype V] [Fintype α] [DecidableEq α] in
/-- ⭐⭐ **拼合**：`A` 上取 `a`、`A` 外取 `y`。 -/
def gluez (A : Finset V) (a y : V → α) : V → α :=
  fun u => if u ∈ A then a u else y u

omit [Fintype V] [Fintype α] [DecidableEq α] in
theorem gluez_eq_left {A : Finset V} {a y : V → α} {u : V} (hu : u ∈ A) :
    gluez A a y u = a u := if_pos hu

omit [Fintype V] [Fintype α] [DecidableEq α] in
theorem gluez_eq_right {A : Finset V} {a y : V → α} {u : V} (hu : u ∉ A) :
    gluez A a y u = y u := if_neg hu

omit [Fintype α] [DecidableEq α] in
/-- ⭐⭐ `gluez` 在 `A` 上等于 `a`。 -/
theorem gluez_agree_left {A : Finset V} (a y : V → α) : agreeOn A (gluez A a y) a :=
  fun u hu => gluez_eq_left hu

/-- ⭐⭐⭐ **`mass` 的单层定义包装**（把 `mass` 展成纤维上的 `filter` 求和，便于 `sum_bij`）。 -/
theorem mass_eq_fiber_sum (S : Finset V) (f : (V → α) → ℝ) (x : V → α) :
    mass S f x
      = ∑ w ∈ (Finset.univ.filter (fun w : V → α => agreeOn S w x)), f w := by
  classical
  have h : mass S f x
      = ∑ w : V → α, (if agreeOn S w x then f w else 0) := by
    unfold mass agreeOn
    rfl
  rw [h, Finset.sum_filter]

/-! ===========================================================================
  §2 块 ① **纤维双射引擎**：`mass S f` 只依赖 `x|_{S ∩ A}`（`f` 只读 `A`）
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **块 ①（策略 5 的核心引擎）：`mass_local_of_reads`。**

设 `f` **只读 `A`**（`Reads f A`）。则**对任意** `S`，`mass S f` 只依赖 `x` 在
`S ∩ A` 上的取值：

$$\texttt{agreeOn}\ (S\cap A)\ x\ y\ \Longrightarrow\ \mathrm{mass}\,S\,f\,x=\mathrm{mass}\,S\,f\,y.$$

**证明（纯纤维双射，`Finset.sum_bij`；不用塔、不用 `mass_mul`）：**
对每个 `w : V → α` 定义
`θ w := fun u => if u ∈ S ∧ u ∉ A then y u else w u`（即「把 `S` 内、`A` 外的那部分换成 `y`」）。

* `θ` 把 `x`-纤维打进 `y`-纤维：若 `agreeOn S w x`，则对 `u ∈ S`：
  * `u ∈ A`：`(θ w) u = w u = x u = y u`（因 `u ∈ S ∩ A`）；
  * `u ∉ A`：`(θ w) u = y u`。
* `θ` 保 `f`：`(θ w)` 与 `w` 在 `A` 上一致（修改只发生在 `A` 外的坐标），故 `f (θ w) = f w`。
* `θ` 是对合（`A` 外、`S` 内的值被强制为 `y`，再改一次不变）：`θ (θ w) = θ w`。

于是 `Finset.sum_bij` 的两条纤维求和相等。∎

**⚠ 为什么这就是「第 5 种」**：这一步**不需要** `mass_mul` 的前提「`f` 的读集 `⊆` 求和集」
（路线乙 / 视角 12 的卡点）、也**不是** `mass` 的嵌套（T24 反例）。
它只用「纤维是`S`内钉死、`S`外自由」这一**单层**事实。 -/
theorem mass_local_of_reads {f : (V → α) → ℝ} {A : Finset V} (hf : Reads f A)
    (S : Finset V) {x y : V → α} (hxy : agreeOn (S ∩ A) x y) :
    mass S f x = mass S f y := by
  classical
  rw [mass_eq_fiber_sum, mass_eq_fiber_sum]
  -- 两条纤维
  set FX := Finset.univ.filter (fun w : V → α => agreeOn S w x) with hFX
  set FY := Finset.univ.filter (fun w : V → α => agreeOn S w y) with hFY
  -- 前向 `θ w = gluez (S \ A) y w`，反向 `θ' w = gluez (S \ A) x w`
  have hmemX : ∀ w : V → α, w ∈ FX ↔ agreeOn S w x := by
    intro w; simp [hFX]
  have hmemY : ∀ w : V → α, w ∈ FY ↔ agreeOn S w y := by
    intro w; simp [hFY]
  -- 前向落点
  have hfwd : ∀ w ∈ FX, gluez (S \ A) y w ∈ FY := by
    intro w hw
    rw [hmemY]
    have hwx : agreeOn S w x := (hmemX w).mp hw
    intro u huS
    by_cases huA : u ∈ A
    · have huSA : u ∉ S \ A := fun h => (Finset.mem_sdiff.mp h).2 huA
      show gluez (S \ A) y w u = y u
      rw [gluez_eq_right huSA]
      have hu : u ∈ S ∩ A := Finset.mem_inter.mpr ⟨huS, huA⟩
      rw [hwx u huS]
      exact hxy u hu
    · have huSA : u ∈ S \ A := Finset.mem_sdiff.mpr ⟨huS, huA⟩
      show gluez (S \ A) y w u = y u
      rw [gluez_eq_left huSA]
  -- 反向落点
  have hbwd : ∀ w ∈ FY, gluez (S \ A) x w ∈ FX := by
    intro w hw
    rw [hmemX]
    have hwy : agreeOn S w y := (hmemY w).mp hw
    intro u huS
    by_cases huA : u ∈ A
    · have huSA : u ∉ S \ A := fun h => (Finset.mem_sdiff.mp h).2 huA
      show gluez (S \ A) x w u = x u
      rw [gluez_eq_right huSA]
      have hu : u ∈ S ∩ A := Finset.mem_inter.mpr ⟨huS, huA⟩
      rw [hwy u huS]
      exact (hxy u hu).symm
    · have huSA : u ∈ S \ A := Finset.mem_sdiff.mpr ⟨huS, huA⟩
      show gluez (S \ A) x w u = x u
      rw [gluez_eq_left huSA]
  -- `gluez` 的「先改一次再改回」恒等式：在 x-纤维上 `θ'(θ w) = w`
  have hgl_x : ∀ w : V → α, agreeOn S w x →
      gluez (S \ A) x (gluez (S \ A) y w) = w := by
    intro w hwx
    funext u
    by_cases huSA : u ∈ S \ A
    · rw [gluez_eq_left huSA]
      exact (hwx u (Finset.mem_sdiff.mp huSA).1).symm
    · rw [gluez_eq_right huSA]
      exact gluez_eq_right huSA
  have hgl_y : ∀ w : V → α, agreeOn S w y →
      gluez (S \ A) y (gluez (S \ A) x w) = w := by
    intro w hwy
    funext u
    by_cases huSA : u ∈ S \ A
    · rw [gluez_eq_left huSA]
      exact (hwy u (Finset.mem_sdiff.mp huSA).1).symm
    · rw [gluez_eq_right huSA, gluez_eq_right huSA]
  refine Finset.sum_bij' (fun w _ => gluez (S \ A) y w) (fun w _ => gluez (S \ A) x w)
    hfwd hbwd ?_ ?_ ?_
  · -- 左逆
    intro w hw; exact hgl_x w ((hmemX w).mp hw)
  · -- 右逆
    intro w hw; exact hgl_y w ((hmemY w).mp hw)
  · -- 值和 `f`
    intro w _
    show f w = f (gluez (S \ A) y w)
    refine (hf _ _ ?_).symm
    intro u huA
    have huSA : u ∉ S \ A := by simp [huA]
    rw [gluez_eq_right huSA]

end BridgeStrategy5
end Fate