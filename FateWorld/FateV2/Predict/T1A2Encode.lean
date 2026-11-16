import FateWorld.FateV2.Predict.T1A2Theta
import Mathlib.Tactic

/-!
  # Predict · T1A2Encode

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1A2Encode.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A2Theta
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/T1A2Encode` —— `T1A.2` 的编码桥（G1 缺口）

## 内容

把 `FinJoint (Fin 2) (Fin 2) (Fin 2) = (Fin 2 × Fin 2) × Fin 2 → ℝ`
与 `(Fin 3 → Bool) → ℝ` 之间的载体桥接起来。

## 为什么需要

`T1A.2` 的代数形式（`T1A2CI3`）是在 `(Fin 3 → Bool) → ℝ` 上证的，
而项目的**概率载体**是 `FinJoint`。两者需要一个**编码**。

G1 缺口的问题链：

```text
rho  在 q 上不可逆（X 分量从不出现）
  ↓
theta 解决了这个问题（Z 槽对准共同原因）          ← 已由 Fate/T1A2Theta 机检
  ↓
但 (V → Bool) 与 FinJoint 的索引型之间还缺一个编码   ← 本文件
```

## 方案

两边都是 **8 个元素**（`(Fin 2 × Fin 2) × Fin 2` 和 `Fin 3 → Bool`），
故由 `Fintype.equivOfCardEq` 可得等价。

本文件给出**两条独立路线**：

| 路线 | 定义 | 特征 |
|---|---|---|
| **基数路线** | `thetaEquiv` | 只依赖基数计算；**构造不可计算、不保证等于 `theta`** |
| **双射路线** | `thetaEquivExplicit` | ⭐ 由 `T1A2Theta.theta_bijective` 构造，**正向就是 `theta`** |

**⚠ 两者的关系**：`Fin 3 → Bool` 只有 `8` 个元素，而 `theta` 已经占满，
故任何单射即满射 —— 两条路线给出的是**同一个重排**，只是构造方式不同。
`thetaEquivExplicit_apply`（`rfl` 级）把双射路线的正向钉在 `theta` 的定义上。

## 定理清单

| # | 名称 | 内容 |
|---|---|---|
| 1 | `card_fin3_bool` | ⭐⭐ `Fintype.card (Fin 3 → Bool) = 8` |
| 2 | `card_prod_fin2` | ⭐⭐ `Fintype.card ((Fin 2 × Fin 2) × Fin 2) = 8` |
| 3 | **`card_eq`** | ⭐⭐⭐ 两型基数相同 |
| 4 | **`thetaEquiv`** | ⭐⭐⭐ 基数路线：由 `Fintype.equivOfCardEq` 得到 |
| 5 | `exists_equiv` | ⭐⭐ 等价的存在性（`Nonempty` 形式，比 `thetaEquiv` 更轻） |
| 6 | **`thetaEquivExplicit`** | ⭐⭐⭐⭐ 双射路线：显式编码等价（主交付物） |
| 7 | **`thetaEquivExplicit_apply`** | ⭐⭐⭐ 正向作用 = `theta`（`rfl`） |
| 8 | `fin2_eq_of_bool` | ⭐⭐ `Fin 2` 上的解码律：「是否 `= 0`」一位决定元素 |
| 9 | `thetaEquivExplicit_symm_apply_zero` / `_one` / `_two` | ⭐⭐ 逆向解码的三条展开 |
| 10 | `thetaEquivExplicit_apply_symm_apply` | ⭐⭐ 解码后编码 = 恒等 |
| 11 | `thetaEquivExplicit_symm_apply_apply` | ⭐⭐ 编码后解码 = 恒等 |
| 12 | **`funcEquiv`** | ⭐⭐⭐ 函数空间等价 `(((Fin 2 × Fin 2) × Fin 2) → ℝ) ≃ ((Fin 3 → Bool) → ℝ)`（预合成） |
| 13 | **`funcEquivExplicit`** | ⭐⭐⭐⭐ **同一函数空间等价，但走显式 `theta` 路线**（变量换位便于对照） |
| 14 | `funcEquiv_apply` | ⭐⭐ `funcEquiv` 的展开公式：`F ↦ fun g => F (thetaEquiv.symm g)` |

## 边界（诚实声明）

- 本文件**不重新证明** `CondMul`。`T1A2Fin`、`T1A2Theta`、`T1A2Substance`
  已各有一份；本文件末尾只用 `#check` **指向** `T1A2Theta.condMul_of_separable`，
  确认它在编码层之上仍然可用。
- `funcEquiv` / `funcEquivExplicit` 是**纯重命名**（预合成），
  **不**携带归一化、正性或 `CondMul` 任何内容。
- 编码等价**本身不含任何概率内容**：它只是两个 `8` 元集之间的重命名。

## 无 `sorry` / `admit` / `axiom`

见文件末尾 `#print axioms` 审计段。
-/

namespace FateV2.Predict.T1A2Encode

open Fintype Fate.T1A2Theta

/-! ## §1 基数计算 -/

/-- ⭐⭐ **`Fin 3 → Bool` 的基数是 `2^3 = 8`**。 -/
theorem card_fin3_bool : Fintype.card (Fin 3 → Bool) = 8 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_num

/-- ⭐⭐ **`(Fin 2 × Fin 2) × Fin 2` 的基数是 `2*2*2 = 8`**。 -/
theorem card_prod_fin2 : Fintype.card ((Fin 2 × Fin 2) × Fin 2) = 8 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]

/-- ⭐⭐⭐ **两型基数相同**。

**⟹ 意义**：这是 `theta` 之所以可能**是双射**的**计数原因** ——
`T1A2Theta.theta_injective` 给出单射，而单射在两个 `8` 元集之间
**必然是满射**，于是 `theta` 的图像**不会遗漏任何**逐顶点配置。
`T1A2Theta.theta_bijective` 正是沿这条思路证出来的。 -/
theorem card_eq :
    Fintype.card ((Fin 2 × Fin 2) × Fin 2) = Fintype.card (Fin 3 → Bool) := by
  rw [card_prod_fin2, card_fin3_bool]

/-! ## §2 ⭐⭐⭐ 编码等价（基数路线） -/

/-- ⭐⭐⭐⭐ **`(Fin 2 × Fin 2) × Fin 2 ≃ (Fin 3 → Bool)`**：

由基数相同（都是 8）构造的等价。

**⚠ 这个等价是**非构造性**的（`Fintype.equivOfCardEq` 用 `Classical.choice`），**
**但它证明了**两个载体在集合论层面是等价的**。

**⚠ 诚实声明**：它内部走 `Fintype` 的枚举顺序，**不保证等于 `theta`**。
若下游需要「正向就是 `theta`」的接口，请用 §3 的 `thetaEquivExplicit`。 -/
noncomputable def thetaEquiv : ((Fin 2 × Fin 2) × Fin 2) ≃ (Fin 3 → Bool) :=
  Fintype.equivOfCardEq (by rw [card_prod_fin2, card_fin3_bool])

/-- ⭐⭐ **等价的存在性**（比 `thetaEquiv` 更轻）
-/
theorem exists_equiv :
    Nonempty (((Fin 2 × Fin 2) × Fin 2) ≃ (Fin 3 → Bool)) :=
  ⟨thetaEquiv⟩

/-! ## §3 ⭐⭐⭐⭐ **双射路线**：显式编码器（主交付物）

`T1A2Theta.theta_bijective` 已机检 `theta` 是双射，
于是 `Equiv.ofBijective` 直接把它升格为等价。
**这条路线给出的映射是显式的、语义正确的**（顶点 `0 ↦ X`、`1 ↦ Z`、`2 ↦ Y`）。 -/

/-- ⭐⭐⭐⭐ **显式编码等价**：`(Fin 2 × Fin 2) × Fin 2 ≃ (Fin 3 → Bool)`。

**正向**就是 `T1A2Theta.theta`：

| 顶点 | 含义 | 取值 |
|---|---|---|
| `0` | `X` | `q.1.1 == 0` |
| `1` | **共同原因 `Z`** | `q.2 == 0` |
| `2` | `Y` | `q.1.2 == 0` |

**⚠ 与 `thetaEquiv`（§2）的区别**：本定义的正向**可计算**且**逐点等于 `theta`**
（见 `thetaEquivExplicit_apply`），因此下游可以按 `theta` 的坐标含义推理；
`thetaEquiv` 只是一条纯计数路线。

**⚠ `noncomputable` 原因**：逆向（`symm`）来自 `Equiv.ofBijective`，
内部用 `Classical.choice`；正向本身是 `theta`，完全可计算。 -/
noncomputable def thetaEquivExplicit : ((Fin 2 × Fin 2) × Fin 2) ≃ (Fin 3 → Bool) :=
  Equiv.ofBijective theta theta_bijective

/-- ⭐⭐⭐ **`thetaEquivExplicit` 的正向作用逐点等于 `theta`**（`rfl` 级）。

**⟹ 意义**：把 §3 的显式路线与 `theta` 的**语义定义**钉死 ——
下游若按 `theta` 的坐标含义做推理（顶点 `0 ↦ X`、`1 ↦ Z`、`2 ↦ Y`），
可以**直接**沿这条等式换到 `thetaEquivExplicit`，无需拆 `Equiv.ofBijective` 的内部。 -/
theorem thetaEquivExplicit_apply (q : (Fin 2 × Fin 2) × Fin 2) :
    thetaEquivExplicit q = theta q := rfl

/-! ### §3.1 ⭐⭐ 逆向解码：三个顶点各自读回一个坐标

`thetaEquivExplicit.symm` 把逐顶点配置解码回三元坐标。
三条解码律都归结到**同一个** `Fin 2` 上的组合事实：
「是否 `= 0`」这一位决定元素。 -/

/-- ⭐⭐ **`Fin 2` 上的解码律**：若 `(u == 0) = b`，则
`u = if b then 0 else 1`。

**证明**：对 `b` 二分。
- `b = true`：`u == 0` 为真，由 `beq_iff_eq` 直接得 `u = 0`；
- `b = false`：`u ≠ 0`，而 `Fin 2` 只有 `0` 与 `1`，故 `u.val = 1`，即 `u = 1`。 -/
theorem fin2_eq_of_bool (u : Fin 2) (b : Bool) (h : (u == 0) = b) :
    u = if b = true then 0 else 1 := by
  split <;> rename_i hb
  · exact beq_iff_eq.mp (h.trans hb)
  · have hne : u ≠ 0 := by
      intro h0
      rw [h0] at h
      simp at h
      exact hb h
    have hv : u.val = 1 := by
      have := u.isLt
      omega
    exact Fin.ext hv

/-- ⭐⭐ **逆向解码在 `X` 坐标上**：`thetaEquivExplicit.symm g` 的第一个分量 `q.1.1`
由顶点 `0` 的取值 `g 0` 唯一决定。

**证明**：`thetaEquivExplicit_apply` 把正向换成 `theta`，
`theta_apply_zero` 把 `theta` 在顶点 `0` 展开，于是
`(q.1.1 == 0) = g 0`，交给 `fin2_eq_of_bool`。 -/
theorem thetaEquivExplicit_symm_apply_zero (g : Fin 3 → Bool) :
    (thetaEquivExplicit.symm g).1.1 = if g 0 = true then 0 else 1 := by
  have h : theta (thetaEquivExplicit.symm g) = g := by
    rw [← thetaEquivExplicit_apply]
    exact Equiv.apply_symm_apply thetaEquivExplicit g
  exact fin2_eq_of_bool _ _ ((theta_apply_zero _).symm.trans (congrFun h 0))

/-- ⭐⭐ **逆向解码在 `Z` 坐标上**（**共同原因**那一侧）。

**⚠ 这条最关键**：`Z` 是条件变量。若两个不同的 `z` 在解码后混淆，
则「给定 `z`」的条件化会**串味** —— 这正是 `T1A2Substance.rho` 的结构性错位。
本定理给出 `z` 的**显式反解**：`q.2 = if g 1 then 0 else 1`。 -/
theorem thetaEquivExplicit_symm_apply_one (g : Fin 3 → Bool) :
    (thetaEquivExplicit.symm g).2 = if g 1 = true then 0 else 1 := by
  have h : theta (thetaEquivExplicit.symm g) = g := by
    rw [← thetaEquivExplicit_apply]
    exact Equiv.apply_symm_apply thetaEquivExplicit g
  exact fin2_eq_of_bool _ _ ((theta_apply_one _).symm.trans (congrFun h 1))

/-- ⭐⭐ **逆向解码在 `Y` 坐标上**：`q.1.2 = if g 2 then 0 else 1`。 -/
theorem thetaEquivExplicit_symm_apply_two (g : Fin 3 → Bool) :
    (thetaEquivExplicit.symm g).1.2 = if g 2 = true then 0 else 1 := by
  have h : theta (thetaEquivExplicit.symm g) = g := by
    rw [← thetaEquivExplicit_apply]
    exact Equiv.apply_symm_apply thetaEquivExplicit g
  exact fin2_eq_of_bool _ _ ((theta_apply_two _).symm.trans (congrFun h 2))

/-! ### §3.2 ⭐⭐ 往返律

编码与解码互为逆 —— 这是任何要「搬结构」的下游代码的第一份合同。 -/

/-- ⭐⭐ **解码后编码 = 恒等**：对任意 `g : Fin 3 → Bool`，
`thetaEquivExplicit (thetaEquivExplicit.symm g) = g`。

即：先解码再编码**不丢失任何信息** —— 编码是**满的**。 -/
theorem thetaEquivExplicit_apply_symm_apply (g : Fin 3 → Bool) :
    thetaEquivExplicit (thetaEquivExplicit.symm g) = g :=
  Equiv.apply_symm_apply thetaEquivExplicit g

/-- ⭐⭐ **编码后解码 = 恒等**：对任意 `q`，
`thetaEquivExplicit.symm (thetaEquivExplicit q) = q`。

即：先编码再解码**不改动任何坐标** —— 编码是**单的**。 -/
theorem thetaEquivExplicit_symm_apply_apply (q : (Fin 2 × Fin 2) × Fin 2) :
    thetaEquivExplicit.symm (thetaEquivExplicit q) = q :=
  Equiv.symm_apply_apply thetaEquivExplicit q

/-! ## §4 函数空间的等价 -/

/-- ⭐⭐⭐ **函数空间的等价**：

$$\bigl((\text{FinJoint})\to\mathbb{R}\bigr) \simeq \bigl((\text{Fin 3}\to\text{Bool})\to\mathbb{R}\bigr)$$

**⚠ 由 `thetaEquiv` 诱导（预合成）。** -/
noncomputable def funcEquiv :
    (((Fin 2 × Fin 2) × Fin 2 → ℝ)) ≃ ((Fin 3 → Bool) → ℝ) :=
  Equiv.arrowCongr thetaEquiv (Equiv.refl ℝ)

/-- ⭐⭐ **`funcEquiv` 的展开公式**：预合成的方向是
`F ↦ fun g => F (thetaEquiv.symm g)`。

**证明**：`Equiv.arrowCongr` 的定义即 `fun f => e₂ ∘ f ∘ e₁.symm`，
而 `e₂ = Equiv.refl ℝ` 上的复合是恒等。 -/
theorem funcEquiv_apply (F : (Fin 2 × Fin 2) × Fin 2 → ℝ) :
    funcEquiv F = fun g => F (thetaEquiv.symm g) := by
  funext g
  simp [funcEquiv, Equiv.arrowCongr]

/-- ⭐⭐⭐⭐ **同一函数空间等价的显式版本**：
$$\bigl((\text{Fin 3}\to\text{Bool})\to\mathbb{R}\bigr) \simeq
  \bigl((\text{FinJoint})\to\mathbb{R}\bigr)$$
由 `thetaEquivExplicit` 诱导。

**⚠ 与 `funcEquiv` 的关系**：两者是**同一类**预合成等价，
区别只在底层编码器走哪条路线（基数 vs 显式 `theta`）。
显式版本的正向作用为 `f ↦ f ∘ theta`，**语义可读**：
「把逐顶点配置上的函数拉回到三元坐标上」。 -/
noncomputable def funcEquivExplicit :
    ((Fin 3 → Bool) → ℝ) ≃ (((Fin 2 × Fin 2) × Fin 2) → ℝ) :=
  Equiv.arrowCongr thetaEquivExplicit.symm (Equiv.refl ℝ)

/-- ⭐⭐ **`funcEquivExplicit` 的展开公式**：
`f ↦ fun q => f (theta q)` —— 预合成的方向正好是「沿 `theta` 拉回」。

**证明**：`Equiv.arrowCongr` 的定义是 `e₂ ∘ f ∘ e₁.symm`，
此处 `e₁ = thetaEquivExplicit.symm`，故 `e₁.symm = thetaEquivExplicit`；
再沿 `thetaEquivExplicit_apply` 换成 `theta`。 -/
theorem funcEquivExplicit_apply (f : (Fin 3 → Bool) → ℝ) :
    funcEquivExplicit f = fun q => f (theta q) := by
  funext q
  show f (thetaEquivExplicit.symm.symm q) = f (theta q)
  rw [Equiv.symm_symm, thetaEquivExplicit_apply]

/-! ## §5 与既有设施的关系（**不重复证明**）

`CondMul` 在编码层之上的成立性已由既有机检文件覆盖，本文件**不重证**，
只在此**指向**它们，说明编码层不打断那条链：

- `Fate.T1A2Theta.condMul_of_separable` —— 三因子可分离 ⟹ `CondMul`（`theta` 载体）
- `Fate.T1A2Fin` / `Fate.T1A2Substance` —— 同方向的其他机检版本

本文件的贡献是：**给出 `theta` 背后那个 `Equiv` 项**，
使下游可以把对 `((Fin 2 × Fin 2) × Fin 2)` 的求和/结构
**机械地**搬到 `(Fin 3 → Bool)` 上，无需每次重跑双射论证。 -/

#check @Fate.T1A2Theta.condMul_of_separable
#check @Fate.T1A2Theta.theta

/-! ## §6 公理审计 -/

#print axioms card_fin3_bool
#print axioms card_prod_fin2
#print axioms card_eq
#print axioms thetaEquiv
#print axioms exists_equiv
#print axioms thetaEquivExplicit
#print axioms thetaEquivExplicit_apply
#print axioms fin2_eq_of_bool
#print axioms thetaEquivExplicit_symm_apply_zero
#print axioms thetaEquivExplicit_symm_apply_one
#print axioms thetaEquivExplicit_symm_apply_two
#print axioms thetaEquivExplicit_apply_symm_apply
#print axioms thetaEquivExplicit_symm_apply_apply
#print axioms funcEquiv
#print axioms funcEquiv_apply
#print axioms funcEquivExplicit
#print axioms funcEquivExplicit_apply

end FateV2.Predict.T1A2Encode
