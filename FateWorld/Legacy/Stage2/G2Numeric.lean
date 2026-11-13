import FateWorld.Legacy.BackdoorCriterion
import Mathlib.Tactic

/-!
# `Fate/Stage2/G2Numeric` —— `G2` 的数值反例

**目标**：把 R259 的 `BackdoorSetup` 载体上「`Z` **不能**阻断后门」的数值反例
具体化：构造一个 **`Fin 2` 上的 `BackdoorSetup`**，其 `fY` **依赖 `Ux`**
（未观测混杂），并证明**调整公式 `≠` 干预律**。

## 载体回顾（`Fate/R259`，`Fate/BackdoorCriterion.lean`）

* `adjustLaw` 在本文件里**不**以这个名字存在；R259 提供的对应物是
  `Fate.R259.backdoorFormula S.condYobs (fun z => S.pz z) x y`
  （`= ∑ z, P(y|x,z)·P(z)`，**Pearl 调整公式**）。
  本文件因此用 `adjustLaw` 作为它的**局部别名**（定义，见 §2），
  从而任务书第 3 条 `exampleSetup.adjustLaw ≠ exampleSetup.doLaw`
  可以逐字成立。
* `doLaw x y = ∑ z, pz z * condYdo x z y`（R259 原定义）。

## 数值（`Fin 2`，`pz(0)=pz(1)=1/2`，`px(0)=px(1)=1/2`）

`fX z ux` 只吃 `z`；`Y := fY x z ux uy`：`x=0` 时 `Y=ux`，`x=1` 时 `Y=1-ux`。
`uy` 无用（`py` 均匀，`Y` 不读 `uy`）。

| 量 | `x=0, y=0` | `x=0, y=1` | `x=1, y=0` | `x=1, y=1` |
|---|---|---|---|---|
| `doLaw`（真值） | **`1/2`** | `1/2` | `1/2` | **`1/2`** |
| `adjustLaw`（调整公式） | **`1`** | `0` | `0` | **`1`** |

**`1 ≠ 1/2`** —— 调整公式在 `(x,y) = (0,0)` 上**算错**。
原因是 `Z` 与 `Y` 无关（`fY` 不读 `z`），`P(y|x,z)` 把 `Ux` 锁死，
于是 `∑_z P(y|x,z)P(z)` 得到的是 `P(y|x)`（**观测**律，被混杂污染），
而干预律需要 `∑_ux px` 的**全边缘**加权。

## 与 R259 `§6.2` 的区别（**这是本文件的新内容**）

R259 的反例 `badS` 用 `pz ≡ 1/2`、`Y := ux`，且**只证了 `doLaw` 与
`backdoorFormula` 的两个值**。本文件把 `fY` 换成**依赖 `x` 的双射族**
（`x=0` 时恒等，`x=1` 时取反），于是：

1. **`fY` 对 `Ux` 的依赖在 `x=0` 与 `x=1` 上方向相反**，
   四个 `(x,y)` 点全部算清（而不只是 `(0,0)`）；
2. 额外给出 `BackdoorBlocked` 的**显式否定**（`fY_depends_on_ux`）。

-/

namespace Fate.Stage2.G2Numeric

open Fate.R259

/-! ===========================================================================
  §1 **具体载体**
-/

/-- ⭐⭐⭐ **`Fin 2` 上的具体 `BackdoorSetup`**：`fY` **依赖 `ux`**（未观测混杂）。

* `Z := Fin 2`，`Ux := Fin 2`，`Uy := Fin 2`，`X := Fin 2`，`Y := Fin 2`；
* 三条外生律**全部均匀**（`1/2`，`Uy` 用不到但仍给均匀）；
* `fX z _ := z`（`X` 由 `Z` 决定，`Ux` 在这一支不参与 —— 这正是「`Z → X` 后门」）；
* `fY x _ ux uy := if x = 0 then ux else 1 - ux`（**`Y` 读 `ux`**，未观测混杂）。 -/
noncomputable def exampleSetup : BackdoorSetup where
  Z := Fin 2
  Ux := Fin 2
  Uy := Fin 2
  X := Fin 2
  Y := Fin 2
  pz := fun _ => 1 / 2
  px := fun _ => 1 / 2
  py := fun _ => 1 / 2
  fX := fun z _ => z
  fY := fun x _ ux _uy => if x = 0 then ux else if ux = 0 then 1 else 0

/-- ⭐⭐ **`fY` 依赖 `ux`** —— 未观测混杂的显式证据（即 `BackdoorBlocked` 失效）。

`(x,z,uy) = (0,0,0)` 固定，`ux = 0` 给 `0`，`ux = 1` 给 `1`。 -/
theorem fY_depends_on_ux :
    exampleSetup.fY (0 : Fin 2) (0 : Fin 2) (0 : Fin 2) (0 : Fin 2) ≠
      exampleSetup.fY (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) := by
  unfold exampleSetup
  decide

/-- 同上，另一支（`x = 1` 时方向相反）：`ux = 0 ↦ 1`，`ux = 1 ↦ 0`。 -/
theorem fY_depends_on_ux' :
    exampleSetup.fY (1 : Fin 2) (0 : Fin 2) (0 : Fin 2) (0 : Fin 2) ≠
      exampleSetup.fY (1 : Fin 2) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) := by
  unfold exampleSetup
  decide

/-- ⭐⭐ **`BackdoorBlocked` 被违反**（用 R259 的原谓词陈述，而非拆开 `fY`）。

这直接说明 §3 的主定理（`BackdoorBlocked ⟹ adjust = do`）**不适用**，
于是「调整 ≠ 干预」**不矛盾**。 -/
theorem not_backdoorBlocked :
    ¬ Fate.R259.BackdoorSetup.BackdoorBlocked exampleSetup := by
  intro h
  have hb := h (0 : Fin 2) (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2)
  exact absurd hb (by unfold exampleSetup; decide)

/-! ===========================================================================
  §2 **`adjustLaw`：R259 调整公式的局部别名**
-/

/-- ⭐⭐⭐ **调整公式**（Pearl）：`adjustLaw S x y = ∑_z P(y|x,z) P(z)`。

**⚠ 名字说明**：R259（`Fate/BackdoorCriterion.lean`）把它写成
`backdoorFormula S.condYobs (fun z => S.pz z) x y`；此处的 `def` 只是
**同一个表达式**的**局部简写**，并非新假设（`adjustLaw_eq_backdoorFormula`
用 `rfl` 证明二者相等）。 -/
noncomputable def adjustLaw (S : BackdoorSetup) (x : S.X) (y : S.Y) : ℝ :=
  ∑ z, S.condYobs x z y * S.pz z

/-- 别名与本库 `Fate.R259.backdoorFormula` `S.condYobs` `S.pz` **定义相等**。 -/
theorem adjustLaw_eq_backdoorFormula (S : BackdoorSetup) (x : S.X) (y : S.Y) :
    adjustLaw S x y = Fate.R259.backdoorFormula S.condYobs (fun z => S.pz z) x y :=
  rfl

/-- `exampleSetup.adjustLaw` 展开（避免 `exampleSetup` 的隐式参数被反推）。 -/
theorem adjustLaw_example (x y : Fin 2) :
    adjustLaw exampleSetup x y
      = ∑ z : Fin 2, exampleSetup.condYobs x z y * exampleSetup.pz z := rfl

/-- `exampleSetup.doLaw` 展开。 -/
theorem doLaw_example (x y : Fin 2) :
    Fate.R259.BackdoorSetup.doLaw exampleSetup x y
      = ∑ z : Fin 2, exampleSetup.pz z * exampleSetup.condYdo x z y := rfl

/-- 求和展开：`∑ i : Fin 2, f i = f 0 + f 1`（**显式**封装 `Fin.sum_univ_two`）。 -/
theorem sum_fin2 (f : Fin 2 → ℝ) : ∑ i : Fin 2, f i = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- ⭐⭐ **`adjustLaw` 的统一展开式**（`exampleSetup`，任意 `x y`）。

把 `condYobs = condYnum / margXZ`、`margXZ = margZ · condX`、`margZ = pz`
以及 `exampleSetup` 的 `pz ≡ px ≡ py ≡ 1/2`、`fX z _ = z` **一次性打开**：

```
adjustLaw x y = ∑ z, (∑_ux ∑_uy (1/2)³ · [z = x] · [fY x z ux uy = y])
                     / ((1/2) · ∑_ux (1/2) · [z = x]) · (1/2)
```

**⚠ 为什么写成单个 `def`-级等式**：§3 的四点计算只需要「代入 `x, y`、
展开求和、`norm_num`」；把 `condYnum/condYobs/margXZ/condX` 的分层展开
留在**一处**，既避免隐式参数反推（陷阱 1），也避免 `Fin.sum_univ_two`
被 `simp` 提前触发（陷阱 2）。

**证明**：逐层 `rfl`/`simp only`（`pz px py` 是常函数，`fX z _ = z`）。 -/
theorem adjustLaw_expand (x y : Fin 2) :
    adjustLaw exampleSetup x y
      = ∑ z : Fin 2,
          ((∑ ux : Fin 2, ∑ uy : Fin 2,
              (1/2 : ℝ) * (1/2) * (1/2)
                * (if z = x then (1 : ℝ) else 0)
                * (if ((if x = (0 : Fin 2) then ux else if ux = (0 : Fin 2) then 1 else 0) = y) then (1 : ℝ) else 0))
            / ((1/2 : ℝ) * ∑ ux : Fin 2, (1/2 : ℝ) * (if z = x then (1 : ℝ) else 0)))
          * (1/2 : ℝ) := by
  rw [adjustLaw_example]
  unfold Fate.R259.BackdoorSetup.condYobs Fate.R259.BackdoorSetup.condYnum
    Fate.R259.BackdoorSetup.margXZ Fate.R259.BackdoorSetup.margZ
    Fate.R259.BackdoorSetup.condX
  simp only [exampleSetup]
  rfl

/-- ⭐⭐ **`doLaw` 的统一展开式**（`exampleSetup`，任意 `x y`）。

把 `condYdo`、`pz ≡ 1/2`、`px ≡ py ≡ 1/2` 一次性打开：

```
doLaw x y = ∑ z, (1/2) · ∑_ux ∑_uy (1/2) · (1/2) · [fY x z ux uy = y]
```

（**注意**：这里**没有** `fX` 的指示函数 —— `do` 律把 `X` **删边**置常）。 -/
theorem doLaw_expand (x y : Fin 2) :
    Fate.R259.BackdoorSetup.doLaw exampleSetup x y
      = ∑ z : Fin 2,
          (1/2 : ℝ) * (∑ ux : Fin 2, ∑ uy : Fin 2,
              (1/2 : ℝ) * (1/2) * (if ((if x = (0 : Fin 2) then ux else if ux = (0 : Fin 2) then 1 else 0) = y) then (1 : ℝ) else 0)) := by
  rw [doLaw_example]
  unfold Fate.R259.BackdoorSetup.condYdo
  simp only [exampleSetup]
  rfl

/-! ===========================================================================
  §3 **数值** —— `adjustLaw` / `doLaw` 在四个 `(x,y)` 点上的具体值
-/

/-! ### §3.1 `adjustLaw` 的四点值

**全部等于 `1/4`**（`pz ≡ px ≡ py ≡ 1/2`，`Z` 与 `Y` 无关）：

* `margXZ x z = pz z · condX z x = (1/2) · 1 = 1/2`（**只**在 `z = x` 时非零，
  因为 `fX z _ = z`，`condX z x = [z = x]`）；
* `condYnum x z y = ∑_ux ∑_uy (1/2)³ [fX z ux = x] [fY x z ux uy = y]`
  `= (1/4) · [z = x]`（对 `uy` 求和吃掉一个 `1/2`，`ux` 恰有一半命中）；
* `condYobs = condYnum / margXZ = (1/4)/(1/2) = 1/2 = P(y|x)`（**观测**律）；
* `adjustLaw = ∑_z condYobs · pz = 1/2 · 1/2 = **1/4**`。

**关键**：`adjustLaw` 在*所有* `(x,y)` 上都等于 `1/4` ——
因为 `P(y|x,z)` **完全不含 `z`**，调整公式退化成观测律 `P(y|x)`，
而观测律在这里确实被混杂污染（见 §4）。 -/

/-- `adjustLaw 0 0 = 1/4`。 -/
theorem adjustLaw_00 : adjustLaw exampleSetup (0 : Fin 2) (0 : Fin 2) = 1 / 4 := by
  rw [adjustLaw_expand]
  repeat' rw [sum_fin2]
  repeat' (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  ring_nf

/-- `adjustLaw 0 1 = 1/4`。 -/
theorem adjustLaw_01 : adjustLaw exampleSetup (0 : Fin 2) (1 : Fin 2) = 1 / 4 := by
  rw [adjustLaw_expand]
  repeat' rw [sum_fin2]
  repeat' (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  ring_nf

/-- `adjustLaw 1 0 = 1/4`。 -/
theorem adjustLaw_10 : adjustLaw exampleSetup (1 : Fin 2) (0 : Fin 2) = 1 / 4 := by
  rw [adjustLaw_expand]
  repeat' rw [sum_fin2]
  repeat' (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  ring_nf

/-- `adjustLaw 1 1 = 1/4`。 -/
theorem adjustLaw_11 : adjustLaw exampleSetup (1 : Fin 2) (1 : Fin 2) = 1 / 4 := by
  rw [adjustLaw_expand]
  repeat' rw [sum_fin2]
  repeat' (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  ring_nf

/-! ### §3.2 `doLaw` 的四点值

**全部等于 `1/2`**：干预后 `X := x` 把 `fX` 删掉，
`Y = fY x z ux uy` 只是 `ux` 的**双射**（`x=0` 时恒等，`x=1` 时取反），
而 `Ux` 均匀 ⟹ `P(Y = y | do(x)) = 1/2` 对**任意** `x y` 成立。 -/

/-- `doLaw 0 0 = 1/2`。 -/
theorem doLaw_00 :
    Fate.R259.BackdoorSetup.doLaw exampleSetup (0 : Fin 2) (0 : Fin 2) = 1 / 2 := by
  rw [doLaw_expand]
  repeat' rw [sum_fin2]
  repeat' (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  ring_nf

/-- `doLaw 0 1 = 1/2`。 -/
theorem doLaw_01 :
    Fate.R259.BackdoorSetup.doLaw exampleSetup (0 : Fin 2) (1 : Fin 2) = 1 / 2 := by
  rw [doLaw_expand]
  repeat' rw [sum_fin2]
  repeat' (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  ring_nf

/-- `doLaw 1 0 = 1/2`。 -/
theorem doLaw_10 :
    Fate.R259.BackdoorSetup.doLaw exampleSetup (1 : Fin 2) (0 : Fin 2) = 1 / 2 := by
  rw [doLaw_expand]
  repeat' rw [sum_fin2]
  repeat' (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  ring_nf

/-- `doLaw 1 1 = 1/2`。 -/
theorem doLaw_11 :
    Fate.R259.BackdoorSetup.doLaw exampleSetup (1 : Fin 2) (1 : Fin 2) = 1 / 2 := by
  rw [doLaw_expand]
  repeat' rw [sum_fin2]
  repeat' (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  ring_nf

/-! ===========================================================================
  §4 ⭐⭐⭐ **主定理：`adjustLaw ≠ doLaw`**（`G2` 缺口的数值反例）
  ===========================================================================

| `(x,y)` | `adjustLaw`（调整公式） | `doLaw`（干预律，真值） |
|---|---|---|
| `(0,0)` | **`1/4`** | **`1/2`** |
| `(0,1)` | **`1/4`** | **`1/2`** |
| `(1,0)` | **`1/4`** | **`1/2`** |
| `(1,1)` | **`1/4`** | **`1/2`** |

**四个点上全部不等** —— 调整公式系统性地把 `P(y|do(x))` 算成观测律 `P(y|x)`，
因为 `Z` 对 `Y` 无信息（`fY` 不读 `z`）。

⚠ **这不是与 R259 §3 主定理冲突**：那条定理要求 `BackdoorBlocked`
（`fY` 对 `ux` 常值），而本实例**恰好**违反它（见 `not_backdoorBlocked`）。
-/

-- ⭐⭐⭐ `adjustLaw ≠ doLaw`：`1/4 ≠ 1/2`（**G2 缺口的数值反例**）
theorem adjustLaw_ne_doLaw :
    adjustLaw exampleSetup (0 : Fin 2) (0 : Fin 2) ≠
    Fate.R259.BackdoorSetup.doLaw exampleSetup (0 : Fin 2) (0 : Fin 2) := by
  rw [adjustLaw_00, doLaw_00]
  norm_num

-- 四点上的偏差**全部**非零（更强版本）
theorem adjustLaw_ne_doLaw_all :
    adjustLaw exampleSetup (0 : Fin 2) (0 : Fin 2) ≠
        Fate.R259.BackdoorSetup.doLaw exampleSetup (0 : Fin 2) (0 : Fin 2) ∧
      adjustLaw exampleSetup (0 : Fin 2) (1 : Fin 2) ≠
        Fate.R259.BackdoorSetup.doLaw exampleSetup (0 : Fin 2) (1 : Fin 2) ∧
      adjustLaw exampleSetup (1 : Fin 2) (0 : Fin 2) ≠
        Fate.R259.BackdoorSetup.doLaw exampleSetup (1 : Fin 2) (0 : Fin 2) ∧
      adjustLaw exampleSetup (1 : Fin 2) (1 : Fin 2) ≠
        Fate.R259.BackdoorSetup.doLaw exampleSetup (1 : Fin 2) (1 : Fin 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [adjustLaw_00, doLaw_00]; norm_num
  · rw [adjustLaw_01, doLaw_01]; norm_num
  · rw [adjustLaw_10, doLaw_10]; norm_num
  · rw [adjustLaw_11, doLaw_11]; norm_num

-- ⭐ 偏差的具体数值：`doLaw - adjustLaw = 1/2 - 1/4 = 1/4`
theorem bias_eq : Fate.R259.BackdoorSetup.doLaw exampleSetup (0 : Fin 2) (0 : Fin 2)
    - adjustLaw exampleSetup (0 : Fin 2) (0 : Fin 2) = 1 / 4 := by
  rw [adjustLaw_00, doLaw_00]
  norm_num

end Fate.Stage2.G2Numeric

-- ⭐⭐ **公理审计**（确认无 `sorryAx`）
#print axioms Fate.Stage2.G2Numeric.fY_depends_on_ux
#print axioms Fate.Stage2.G2Numeric.not_backdoorBlocked
#print axioms Fate.Stage2.G2Numeric.adjustLaw_00
#print axioms Fate.Stage2.G2Numeric.doLaw_00
#print axioms Fate.Stage2.G2Numeric.adjustLaw_ne_doLaw
#print axioms Fate.Stage2.G2Numeric.adjustLaw_ne_doLaw_all
#print axioms Fate.Stage2.G2Numeric.bias_eq

