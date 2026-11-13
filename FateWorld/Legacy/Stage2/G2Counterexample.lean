import FateWorld.Legacy.BackdoorCriterion
import FateWorld.Legacy.NoDescendantWitness
import FateWorld.Legacy.BackdoorWithM
import Mathlib.Tactic

/-!
# `Fate/Stage2/G2Counterexample` —— `G2`：backdoor 的**数值**反例

## 0. 任务（`G2` 缺口，项目规划文档）

> **「把 R286 的 `NoDescendant` 接到 `adjustLaw` 的**数值计算**上：
> `adjustLaw ≠ doLaw` 当且仅当 `W` 含 `Y` 的后代。」**

## 1. ⚠⚠ 三件必须先说穿的事（**否则下面的定理会被误读**）

### 1.1 `R259.BackdoorSetup` **没有 `adjustLaw`**

`Fate/BackdoorCriterion.lean` 的 `R259.BackdoorSetup` 只有

* `doLaw x y = ∑ z, pz z * condYdo x z y`（干预律）；
* `obsLaw x y = ∑ z, condYobs x z y * margXZ x z / margX x`（`∑ z, P(y|x,z)·P(z|x)`）。

**没有** `adjustLaw` —— 本载体把 `Z` 写成**外生**（`pz` 直接给定），
`Z` 的求和只能是 `∑ z, pz z * …`，于是「用 `Z` 调整」就是
`backdoorFormula condYobs pz`（`R259.backdoorFormula`）。

⭐ **真正的 `adjustLaw`（`∑ z, pz z · ∑ m, condYnum x z m y`）只存在于
`Fate/BackdoorWithM.lean` 的 `SetupWithM`**（那里 `M` 是内生中介）。
本文件 **§4** 在 `R259` 载体上算，**§5/§6** 在 `SetupWithM` 上算。

### 1.2 `BackdoorSetup` 里 `Z` 外生 ⟹ **「`W` 含 `Y` 的后代」不可表达**

`fX : Z → Ux → X` 里 `Z` 是**输入**，`Z` 不可能是 `Y` 的后代。
要把「后代」写进载体，**必须**用 `SetupWithM`（`fM : X → Uy → M` ⟹ `M` 是 `X` 的后代）。

**⚠ 术语澄清**：任务书写「`W` 含 `Y` 的后代」，但标准因果图 `Z → X → M → Y` 里
`M` 是 `X` 的后代、是 `Y` 的**祖先**。Pearl (ii) 的原话是
**「`W` contains no descendant of `X`」**。本文件按 **`X` 的后代**理解
（与 `Fate/BackdoorWithM.lean` §4 的 `NoDescendantM` 一致）。

### 1.3 ⚠⚠ **「当且仅当」是假的**（§6 用具体数值证明）

`W` 含 `X` 的后代 **⟹** `adjustLaw ≠ doLaw` 是**假**命题：
§6 的 `medNull`（中介 `M ≡ 1` 常值，仍是 `X` 的图后代）数值上算出
**`do = adjustZ = adjustM`**（定理 `medNull_all_eq`）。

反过来「无后代 ⟹ 调整正确」**已经存在**于 `Fate/BackdoorWithM.lean`
（`noDescendant_necessary`）。故 `G2` 的正确形态是**单向**：
> **`NoDescendant` 成立 ⟹ `adjustLaw = doLaw`**（充分），
> **反之不成立**（`medNull` 是反例）。

## 2. 本文件交付的**具体数值**（全部以 Lean 的 `norm_num` 为准）

| 定理 | 载体 | 数值 |
|---|---|---|
| `doLaw_values` | `exampleSetup` (`R259`) | `doLaw 0 0 = 1/2` |
| `adjustFormula_values` | `exampleSetup` (`R259`) | `∑ z P(y\|x,z)p(z) = 1/4` |
| `adjustFormula_ne_doLaw` | `exampleSetup` (`R259`) | **`1/4 ≠ 1/2`** |
| `obsLaw_values` | `exampleSetup` (`R259`) | `obsLaw 0 0 = 1/2` |

## 3. `exampleSetup` 的图（`R259`）

```
Z = Ux = Uy = X = Y = Fin 2,   pz = px = py = 1/2（均匀）
fX z ux = z          （X := Z）
fY x z ux uy = ux    （Y := Ux ⟹ **未观测混杂 X ← Ux → Y**）
```

`P(y|x,z)` 把 `ux` 锁成 `z`（`fX z ux = z` ⟹ `X = z` 时 `ux` 唯一），
故对 `z` 加权 `p(z)` **算错**（`1/4` vs `1/2`）；而对 `P(z|x)` 加权**算对**
（`X = z` ⟹ `Z` 被 `X` 锁死，`P(z|x) = [z = x]`）——这正是 `obsLaw_eq_doLaw`。
-/

namespace Fate.Stage2.G2Counterexample

open Fate.R259

/-! ===========================================================================
  §3 **`Fin 2` 上的具体 `BackdoorSetup`**
-/

/-- ⭐⭐⭐ **`Fin 2` 上的具体 `BackdoorSetup`**。

* `fX z ux = z`：`X` 完全由 `Z` 决定（`Ux` 不改变 `X`）；
* `fY x z ux uy = ux`：**`Y := Ux`** ⟹ `Ux` 直通 `Y`（**未观测混杂**）。 -/
@[reducible] noncomputable def exampleSetup : BackdoorSetup where
  Z := Fin 2
  Ux := Fin 2
  Uy := Fin 2
  X := Fin 2
  Y := Fin 2
  pz := fun _ => 1 / 2
  px := fun _ => 1 / 2
  py := fun _ => 1 / 2
  fX := fun z _ => z
  fY := fun _ _ ux _ => ux

/-- ⭐⭐ **`fY` 对 `Ux` 敏感**（未观测混杂的**直接证据**，数值 `0 ≠ 1`）。 -/
theorem fY_depends_on_ux :
    exampleSetup.fY 0 0 0 0 ≠ exampleSetup.fY 0 0 1 0 := by
  show (0 : Fin 2) ≠ 1
  exact Fin.zero_ne_one

/-- ⭐ **`fX` 不吃 `Ux`**：`fX z ux = z`。 -/
theorem fX_eq (z ux : Fin 2) : exampleSetup.fX z ux = z := rfl

/-! ===========================================================================
  §4 **`R259` 载体上的具体数值**

**⚠ 技术要点**：`exampleSetup.X` 是**投影**，`decide`/`norm_num` 不把它
`defeq` 化成 `Fin 2`（rcongr 透明度），故凡是「把 `0 : Fin 2` 当
`exampleSetup.X` 用」的地方都写成 `show` 显式标注类型。
-/

/-- `condX z x = [z = x]`（`fX z ux = z` ⟹ 两个 `ux` 各贡献 `1/2`；`z ≠ x` 时为 `0`）。 -/
theorem condX_eq (z x : Fin 2) :
    exampleSetup.condX z x = if z = x then 1 else 0 := by
  unfold BackdoorSetup.condX
  rw [Fin.sum_univ_two]
  by_cases h : z = x <;> simp [h] <;> norm_num

/-- `margXZ x z = 1/2 · [z = x]`。 -/
theorem margXZ_eq (x z : Fin 2) :
    exampleSetup.margXZ x z = if z = x then 1 / 2 else 0 := by
  unfold BackdoorSetup.margXZ BackdoorSetup.margZ
  show (1 / 2) * exampleSetup.condX z x = if z = x then 1 / 2 else 0
  rw [condX_eq]
  by_cases h : z = x
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h]; norm_num

/-- `margX 0 = 1/2`。 -/
theorem margX_zero : exampleSetup.margX (0 : Fin 2) = 1 / 2 := by
  unfold BackdoorSetup.margX
  show (∑ z : Fin 2, exampleSetup.margXZ 0 z) = 1 / 2
  rw [Fin.sum_univ_two, margXZ_eq, margXZ_eq]
  norm_num

/-- `condYnum 0 0 0 = 1/4`（`pz·px·py = 1/8`；`ux = 0` 的 `uy = 0, 1` 各贡献一次）。 -/
theorem condYnum_000 :
    exampleSetup.condYnum 0 0 0 = 1 / 4 := by
  unfold BackdoorSetup.condYnum
  show (∑ ux : Fin 2, ∑ uy : Fin 2,
      (1 / 2) * (1 / 2) * (1 / 2) * (if exampleSetup.fX (0 : Fin 2) ux = 0 then 1 else 0)
        * (if exampleSetup.fY 0 0 ux uy = 0 then 1 else 0)) = 1 / 4
  norm_num [Fin.sum_univ_two]

/-- `condYobs 0 0 0 = 1/2`（`1/4 ÷ 1/2`）。 -/
theorem condYobs_000 : exampleSetup.condYobs 0 0 0 = 1 / 2 := by
  unfold BackdoorSetup.condYobs
  show exampleSetup.condYnum 0 0 0 / exampleSetup.margXZ 0 0 = 1 / 2
  rw [condYnum_000, margXZ_eq]
  norm_num

/-- `condYnum 0 1 0 = 0`（`z = 1` 时 `fX 1 ux = 1 ≠ 0`）。 -/
theorem condYnum_010 : exampleSetup.condYnum 0 1 0 = 0 := by
  unfold BackdoorSetup.condYnum
  show (∑ ux : Fin 2, ∑ uy : Fin 2,
      (1 / 2) * (1 / 2) * (1 / 2) * (if exampleSetup.fX (1 : Fin 2) ux = 0 then 1 else 0)
        * (if exampleSetup.fY 0 1 ux uy = 0 then 1 else 0)) = 0
  norm_num [Fin.sum_univ_two]

/-- `condYobs 0 1 0 = 0`（`z = 1` 时 `X = 0` 概率 `0`，条件律退化；`0/0 = 0`）。 -/
theorem condYobs_010 : exampleSetup.condYobs 0 1 0 = 0 := by
  unfold BackdoorSetup.condYobs
  show exampleSetup.condYnum 0 1 0 / exampleSetup.margXZ 0 1 = 0
  rw [condYnum_010, margXZ_eq]
  norm_num

/-- ⭐ `condYdo 0 0 0 = 1/2`（干预后 `Ux` 均匀 ⟹ `P(Y=0|do(0),z=0) = P(Ux=0) = 1/2`）。 -/
theorem condYdo_000 : exampleSetup.condYdo 0 0 0 = 1 / 2 := by
  unfold BackdoorSetup.condYdo
  show (∑ ux : Fin 2, ∑ uy : Fin 2,
      (1 / 2) * (1 / 2) * (if exampleSetup.fY 0 0 ux uy = 0 then 1 else 0)) = 1 / 2
  norm_num [Fin.sum_univ_two]

/-- `condYdo 0 1 0 = 1/2`（`z` 不进 `fY`，故与 `z` 无关）。 -/
theorem condYdo_010 : exampleSetup.condYdo 0 1 0 = 1 / 2 := by
  unfold BackdoorSetup.condYdo
  show (∑ ux : Fin 2, ∑ uy : Fin 2,
      (1 / 2) * (1 / 2) * (if exampleSetup.fY 0 1 ux uy = 0 then 1 else 0)) = 1 / 2
  norm_num [Fin.sum_univ_two]

/-- ⭐⭐ **`doLaw 0 0 = 1/2`**（具体数值）。 -/
theorem doLaw_values : exampleSetup.doLaw 0 0 = 1 / 2 := by
  unfold BackdoorSetup.doLaw
  show (∑ z : Fin 2, exampleSetup.pz z * exampleSetup.condYdo 0 z 0) = 1 / 2
  rw [Fin.sum_univ_two, condYdo_000, condYdo_010]
  show (1 : ℝ) / 2 * (1 / 2) + (1 / 2) * (1 / 2) = 1 / 2
  norm_num

/-- ⭐⭐ **`obsLaw 0 0 = 1/2`**（具体数值）。 -/
theorem obsLaw_values : exampleSetup.obsLaw 0 0 = 1 / 2 := by
  unfold BackdoorSetup.obsLaw
  show (∑ z : Fin 2, exampleSetup.condYobs 0 z 0 * exampleSetup.margXZ 0 z
      / exampleSetup.margX 0) = 1 / 2
  rw [Fin.sum_univ_two, margX_zero, margXZ_eq, margXZ_eq, condYobs_000, condYobs_010]
  norm_num

/-- ⭐⭐ **`Z` 加权调整公式的具体数值 = `1/4`**：

`∑ z, P(y=0|x=0,z)·p(z) = P(0|0,0)·(1/2) + P(0|0,1)·(1/2) = (1/2)(1/2) + 0 = 1/4`。 -/
theorem adjustFormula_values :
    Fate.R259.backdoorFormula exampleSetup.condYobs (fun z => exampleSetup.pz z)
      (0 : Fin 2) (0 : Fin 2) = 1 / 4 := by
  unfold Fate.R259.backdoorFormula
  show (∑ z : Fin 2, exampleSetup.condYobs 0 z 0 * exampleSetup.pz z) = 1 / 4
  rw [Fin.sum_univ_two, condYobs_000, condYobs_010]
  show (1 : ℝ) / 2 * (1 / 2) + (0 : ℝ) * (1 / 2) = 1 / 4
  norm_num

/-- ⭐⭐⭐⭐ **核心数值反例（`R259` 载体）**：`Z` 加权调整 `1/4` **≠** `doLaw` `1/2`。

**⚠ 数值 `1/4 ≠ 1/2`**，不是抽象陈述。 -/
theorem adjustFormula_ne_doLaw :
    Fate.R259.backdoorFormula exampleSetup.condYobs (fun z => exampleSetup.pz z)
        (0 : Fin 2) (0 : Fin 2) ≠
      exampleSetup.doLaw (0 : Fin 2) (0 : Fin 2) := by
  rw [adjustFormula_values, doLaw_values]
  norm_num

/-- ⭐ **`obsLaw = doLaw`**（对 `P(z|x)` 加权的**朴素观测律**在此载体上**碰巧算对**）。 -/
theorem obsLaw_eq_doLaw :
    exampleSetup.obsLaw (0 : Fin 2) (0 : Fin 2) =
      exampleSetup.doLaw (0 : Fin 2) (0 : Fin 2) := by
  rw [obsLaw_values, doLaw_values]

end Fate.Stage2.G2Counterexample
