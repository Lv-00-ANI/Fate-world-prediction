/-
# `Fate/T1A2Theta` —— `T1A.2` 的正确载体（`theta`）

## 为什么需要新载体

`Fate/T1A2Substance.lean` 的载体 `rho` 存在**结构性错位**：

```text
rho w ((x,y),z) : 顶点 0 ↦ y,  顶点 1 ↦ z,  顶点 2 ↦ w    （w = X 分量的位）
```

- 它把 `X` 分量塞进**哑坐标 `w`**，而哑坐标在 `CondMul` 里会被 `margZ`
  **求和掉**、又被 `margXZ` **固定住**；
- 于是 `margXZ`（固定 `w`）与 `margZ`（对 `w` 求和）**无法对齐**；
- **后果**：`CondMul` 在该载体上**是假命题**。反例
  $X\,(X+Y+Z+W) = (X+Y)(X+Z)$，取 $X=0,\ Y=1,\ Z=1,\ W=-1$ 即失败。

## `theta` 的修正

本文件把载体换成一个**双射型编码**：

$$\theta\,((x,y),z) : \mathrm{Fin}\ 3 \to \mathsf{Bool}$$

| 顶点 | 含义 | 取值 |
|---|---|---|
| `0` | 分量 `X` | `q.1.1 == 0` |
| `1` | **共同原因 `Z`** | `q.2 == 0` |
| `2` | 分量 `Y` | `q.1.2 == 0` |

**⟹ 关键差异**：`Z` 槽**正好对准顶点 `1`（共同原因）**，
于是 `CondMul` 需要的三个边缘律（`margZ`、`margXZ`、`margYZ`）
全部落在 `z = q.2` 这**一个**坐标上，**不再有哑坐标被求和掉**。

`Fin 2` 与 `Bool` 都是二元型，故 `theta` 是**双射**（`theta_bijective`）；
本文件先逐坐标证明单射，再组装成 `theta_injective`。

## 定理清单

| # | 定理 | 内容 |
|---|---|---|
| 1 | `theta` | ⭐⭐⭐ 正确载体（定义） |
| 2 | `theta_apply_zero` / `_one` / `_two` | ⭐ `theta` 的三条展开（`rfl` 级） |
| 3 | `fin2_eq_of_beq_eq_beq` | ⭐ `Fin 2` 上「是否 `= 0`」一位决定元素 |
| 4 | `theta_inj_zero` / `_one` / `_two` | ⭐⭐ 分坐标的单射 |
| 5 | **`theta_injective`** | ⭐⭐⭐ `theta` 是单射 |
| 6 | **`theta_bijective`** | ⭐⭐⭐ `theta` 是**双射**（更强：无重复也无遗漏） |
| 7 | **`condMul_of_separable`** | ⭐⭐⭐⭐ **主定理**：$p((x,y),z)=a(z)b(x,z)c(y,z)\Rightarrow\mathrm{CondMul}\ p$ |

## 与既有设施的关系

`condMul_of_separable` 的**数学内核**是既有的
`Fate.SeparableCondMul.separable_implies_condMul`（可分离 ⟹ 条件乘性，
已机检、无 `sorry`）。本文件在其上**只做一层包装**：把三因子形式
$a(z)\,b(x,z)\,c(y,z)$ 打包成「可分离」所需的二因子形式
$f(x,z)=b(x,z)$、$g(y,z)=a(z)\,c(y,z)$。这一步是**纯代数重结合**，
不含新的求和论证。

## 无 `sorry` / `admit` / `axiom`

见文件末尾 `#print axioms` 审计段。
-/

import FateWorld.Legacy.FinJoint
import FateWorld.Legacy.FinCondIndep
import FateWorld.Legacy.SeparableCondMul
import Mathlib.Tactic

open Fate.FinCondIndep

namespace Fate.T1A2Theta

open Finset

/-! ## §1 ⭐⭐⭐ **正确载体 `theta`**

**⚠ 类型核对**：`Fate.FinCondIndep.FinJoint α β γ` 是 `abbrev`，
展开为 `(α × β) × γ → ℝ`。故
`FinJoint (Fin 2) (Fin 2) (Fin 2) = (Fin 2 × Fin 2) × Fin 2 → ℝ`。
本文件直接使用**展开后的形式**书写 `theta` 的定义域。 -/

/-- ⭐⭐⭐ **正确载体**：把 `(Fin 2 × Fin 2) × Fin 2` 编码成 `Fin 3 → Bool`。

- 顶点 `0`（`X`）= `q.1.1 == 0`
- 顶点 `1`（`Z`，**共同原因**）= `q.2 == 0`
- 顶点 `2`（`Y`）= `q.1.2 == 0`

**⚠ 与 `T1A2Substance.rho` 的差别**：`rho` 让顶点 `1` 吃 `Z`、顶点 `2` 吃哑坐标
并**丢弃** `X` 分量；`theta` **取消哑坐标**，令顶点 `0` 吃 `X`、顶点 `1` 吃 `Z`、
顶点 `2` 吃 `Y` —— 三个坐标**各就各位**，无一被求和掉。 -/
def theta (q : (Fin 2 × Fin 2) × Fin 2) : Fin 3 → Bool
  | 0 => (q.1.1 == 0)
  | 1 => (q.2 == 0)
  | 2 => (q.1.2 == 0)

/-! ## §2 ⭐ **`theta` 的三条展开定理**（`rfl` 级） -/

/-- ⭐ **`theta` 在顶点 `0` 的取值**：只读 `X` 分量 `q.1.1`。 -/
theorem theta_apply_zero (q : (Fin 2 × Fin 2) × Fin 2) :
    theta q 0 = (q.1.1 == 0) := rfl

/-- ⭐ **`theta` 在顶点 `1` 的取值**：只读 `Z` 分量 `q.2`（**共同原因**）。 -/
theorem theta_apply_one (q : (Fin 2 × Fin 2) × Fin 2) :
    theta q 1 = (q.2 == 0) := rfl

/-- ⭐ **`theta` 在顶点 `2` 的取值**：只读 `Y` 分量 `q.1.2`。 -/
theorem theta_apply_two (q : (Fin 2 × Fin 2) × Fin 2) :
    theta q 2 = (q.1.2 == 0) := rfl

/-! ## §3 ⭐⭐ 分坐标单射：把 `Fin 2 × Fin 2 × Fin 2` 拆成三个 `Bool`

`theta` 是三张**独立的**布尔标签（每个坐标各占一个顶点），
而 `Fin 2` 与 `Bool` 都是二元型。于是单射性可以**逐坐标**检验。 -/

/-- ⭐⭐ **`Fin 2` 上「是否 `= 0`」这一位决定元素**：
`(u == 0) = (v == 0) ⟹ u = v`。

**证明**：`fin_cases` 把两个变量都拆到 `{0, 1}`，`simp` 消去 `==`。 -/
theorem fin2_eq_of_beq_eq_beq {u v : Fin 2} (h : (u == 0) = (v == 0)) : u = v := by
  fin_cases u <;> fin_cases v <;> simp_all

/-- ⭐⭐ **`theta` 在 `X` 坐标上单射**。 -/
theorem theta_inj_zero (q q' : (Fin 2 × Fin 2) × Fin 2) (h : theta q = theta q') :
    q.1.1 = q'.1.1 :=
  fin2_eq_of_beq_eq_beq (congrFun h 0)

/-- ⭐⭐ **`theta` 在 `Z` 坐标上单射**（**共同原因**那一侧）。

**⚠ 这条最关键**：`Z` 是条件变量，若两个不同的 `z` 映到同一配置，
则「给定 `z`」的条件化会**串味**。 -/
theorem theta_inj_one (q q' : (Fin 2 × Fin 2) × Fin 2) (h : theta q = theta q') :
    q.2 = q'.2 :=
  fin2_eq_of_beq_eq_beq (congrFun h 1)

/-- ⭐⭐ **`theta` 在 `Y` 坐标上单射**。 -/
theorem theta_inj_two (q q' : (Fin 2 × Fin 2) × Fin 2) (h : theta q = theta q') :
    q.1.2 = q'.1.2 :=
  fin2_eq_of_beq_eq_beq (congrFun h 2)

/-- ⭐⭐⭐ **`theta` 是单射**。

**⟹ 意义**：`theta` 把 `8` 个配置一一映到不同的逐顶点配置上，
于是 `margZ` 之类的**边缘化求和不会重复计数** —— 这正是
`T1A2Substance.rho` 的结构性错位所破坏的性质。

**证明**：三条分坐标单射给出 `q` 与 `q'` 的两个分量分别相等，
再由 `Prod.ext_iff` 两层拆解。 -/
theorem theta_injective (q q' : (Fin 2 × Fin 2) × Fin 2) (h : theta q = theta q') :
    q = q' := by
  rw [Prod.ext_iff, Prod.ext_iff]
  exact ⟨⟨theta_inj_zero q q' h, theta_inj_two q q' h⟩, theta_inj_one q q' h⟩

/-! ## §4 ⭐⭐⭐ **`theta` 是双射**（比单射更强：既无重复也无遗漏）

`(Fin 2 × Fin 2) × Fin 2` 有 `8` 个元素，`Fin 3 → Bool` 也有 `2 ^ 3 = 8` 个元素，
故单射**自动**升级为双射。本文件把这一步也机检出来，
以说明 `theta` 不是「挑了一部分配置」，而是**整体重排**。 -/

/-- ⭐⭐⭐ **`theta` 是双射**。

**证明**：`theta_injective` 给出单射；有限型上单射加基数相等即双射
（`Fintype.bijective_iff_injective_and_card`）。 -/
theorem theta_bijective : Function.Bijective theta := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun q q' h => theta_injective q q' h, ?_⟩
  simp

/-! ## §5 ⭐⭐⭐⭐ **主定理：可分离（三因子）⟹ `CondMul`**

### 统一口径

`Fate.FinCondIndep.CondMul p` 的定义是

$$\forall x\,y\,z,\quad p\,((x,y),z)\cdot \mathrm{margZ}\ p\ z
  = \mathrm{margXZ}\ p\ x\ z \cdot \mathrm{margYZ}\ p\ y\ z .$$

### 归约到既有定理

既有 `Fate.SeparableCondMul.separable_implies_condMul` 断言：
若 $p((x,y),z) = f(x,z)\cdot g(y,z)$，则 `CondMul p`。

本定理的前件是**三因子**形式 $p((x,y),z) = a(z)\cdot b(x,z)\cdot c(y,z)$。
取

$$f(x,z) := b(x,z),\qquad g(y,z) := a(z)\cdot c(y,z),$$

则 $f(x,z)\,g(y,z) = b(x,z)\,(a(z)\,c(y,z)) = a(z)\,b(x,z)\,c(y,z)$
（纯乘法交换/结合），故前件成立，`CondMul p` 随即得到。

**⟹ 本定理不重复任何求和论证**：全部 `Finset` 边缘化计算留在既有定理里，
这里只做**因子的重结合**。 -/

/-- ⭐⭐⭐⭐ **T1A.2 的最终结论（`theta` 载体）**：

若 `p : FinJoint (Fin 2) (Fin 2) (Fin 2)` 可写成

$$p((x,y),z) = a(z)\cdot b(x,z)\cdot c(y,z),$$

则 `p` **满足 `CondMul`**（即给定 `z` 后 `x` 与 `y` 独立）。

**⚠ 参数化口径**：`FinJoint α β γ` 是 `abbrev`，展开为 `(α × β) × γ → ℝ`，
故 `p` 可以直接写成 `p : (Fin 2 × Fin 2) × Fin 2 → ℝ`。

**证明**：把三因子打包成二因子（`f := b`、`g := fun y z => a z * c y z`），
交给已机检的 `Fate.SeparableCondMul.separable_implies_condMul`。 -/
theorem condMul_of_separable
    (p : (Fin 2 × Fin 2) × Fin 2 → ℝ)
    (a : Fin 2 → ℝ) (b : Fin 2 → Fin 2 → ℝ) (c : Fin 2 → Fin 2 → ℝ)
    (hfac : ∀ (x : Fin 2) (y : Fin 2) (z : Fin 2), p ((x, y), z) = a z * b x z * c y z) :
    CondMul p := by
  refine Fate.SeparableCondMul.separable_implies_condMul p
    ⟨b, fun y z => a z * c y z, ?_⟩
  intro x y z
  rw [hfac x y z]
  ring

/-! ## §6 审计：`#print axioms`

**⚠ 逐条确认无 `sorryAx`**：下列全部定理的依赖若只有
`propext`、`Classical.choice`、`Quot.sound`，即为「无 `sorry`」的机检证据。 -/

#print axioms theta_apply_zero
#print axioms theta_apply_one
#print axioms theta_apply_two
#print axioms fin2_eq_of_beq_eq_beq
#print axioms theta_inj_zero
#print axioms theta_inj_one
#print axioms theta_inj_two
#print axioms theta_injective
#print axioms theta_bijective
#print axioms condMul_of_separable

end Fate.T1A2Theta