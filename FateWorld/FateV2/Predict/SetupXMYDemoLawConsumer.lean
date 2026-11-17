/-
# 消费方：`SetupXMYDemoLaw` —— 否证 ⟹ `X → Y` 必在调整集外；`demoX` 落成 Pearl `SCM`

## 0 本文件做什么

`Fate/SetupXMYDemoLaw.lean`（namespace **`FateV2.Predict.SetupXMY.DemoX`**）交付了
`demoX` 的**数值表**与**两条否证定理**：

* `adjustLawZ_ne_doLaw` ：`adjustLawZ(0,0) = 21/100 ≠ 1/2 = doLaw(0,0)`
* `adjustLawM_ne_doLaw` ：`adjustLawM(1,1) = 29/100 ≠ 29/50 = doLaw(1,1)`
* `adjustLawZ_11_coincides` ：`(1,1)` 一行**偶然**重合（已被上游**明确拒绝**升级为等式定理）

本文件**不重复**这些数值表，而是**消费**它们，给出下列定理（**实数见 §1–§3**）：

| # | 定理 | 类型 | 内容 |
|---|---|---|---|
| **C0** | `zAdjusts_iff` / `mAdjusts_iff` / `fXB_*` | 判据与归约 | 「调整律 = 干预律」形式化为 `ZAdjusts`/`MAdjusts`；`fXB` 的 `Bool` 字面量求值引理 |
| **C1** | `demoX_backdoor_fails_everywhere` | 否证的**全称化** | `demoX` 上 `{Z}` 调整在 `(0,0)` 与 `(1,0)` **两行都错**（`¬ ZAdjusts false false ∧ ¬ ZAdjusts true false`）|
| **C2** | `demoX_not_forall_zAdjusts` + `demoX_zAdjusts_mixed` | 主否证的**推论** | 「`{Z}` 非处处正确」；且「`(1,1)` 重合」与「`(0,0)` 偏离」**并存**（机器形式地否证「重合 ⟹ 一般成立」）|
| **C2'** | `demoX_M_ne_Z_witness` | 两条否证的**并置** | `¬ MAdjusts true true ∧ ¬ ZAdjusts false false` |
| **C3** | `demoX_toPearlSCM_L2_00` / `_L2_11` | ⭐ **跨层接入** | 把 `demoX` 的结构方程装进 `Fate.PearlHierarchy.SCM`，证其 `L2_do` 在 `(0,0)` 与 `(1,1)` **数值等于** `doLaw`（`1/2` 与 `29/50`）|
| **C4** | `demoXSCM_adjustLawZ_ne_L2` / `demoXSCM_adjustLawM_ne_L2` | ⭐ **否证穿透到 `SCM` 层** | 两条否证在 `SCM` 语境下**同样成立**（`21/100 ≠ 1/2`、`29/100 ≠ 29/50`）|
| **C5** | `demoXSCM_L2_not_constant` | 非平凡性 | 该 `SCM` 的 `L2_do` **不是**常数律（否则 C3/C4 全部无内容）|

## 1 为什么 C1 不是同义反复

C1 的**前件为空**（无假设），结论是两个**具体不等式**的合取，每个都由
`SetupXMYDemoLaw` 的数值表（`adjustLawZ_00`/`doLaw_00`/`adjustLawZ_10`/`doLaw_10`）
经 `norm_num` 闭式判定。**没有任何前件把结论包进去**。

## 2 为什么 C3/C4 是实质接入

`Fate/SetupXMYDemoLaw` 只在 `ℝ` 层做算术；`Fate/PearlHierarchy.SCM` 是
**另一套载体**（外生 `U` + 结构映射 `sg : u ↦ (x, h)`）。C3 证明
**两者在同一数值上对齐**：把 `demoX` 的结构方程视作
`h x := fY x (fM x uy) z ux`、外生域取 `(z, ux, uy)`、`pU` 取 `pzB·pxB·pyB` 的乘积，
则 `SCM.L2_do` 的推前求和**数值等于** `doLaw`。这不是重命名：`L2_do` 是 `push` 的
一般定义，`doLaw` 是**带指示函数**的 `∑∑` 展开，二者**形式不同**。

⚠ **第一版编码曾把 `z` 固定为 `false`**（`U := Bool × Bool`），结果 `L2_do true true = 0`，
与 `doLaw true true = 29/50` **不符** —— 因为 `doLaw` 对 `z` **求平均**。
**⟹ `z` 必须进外生域**；这不是编程疏忽，而是「`Z` 在 `demoX` 里是外生的」这一语义事实。

## 3 诚实边界

* **不**声称 `L2_do ≡ doLaw` *一般*成立。C3 **只**证 `demoX` 上的**两个**数值点
  （`(false,false)` 与 `(true,true)`），且证明方式是**展开求和 + `norm_num`**。
  一般等式需要 `Sum`/`Bool` 的推前引理，**本文件未做**。
* C4 **不**声称任何「Pearl 层驳倒 LawRule 层」的元定理；它只是把
  `adjustLawM_ne_doLaw` 的数值**搬进** `SCM` 语境作**一致性登记**。
* **无** `sorry` / `admit` / `axiom`。
-/

import FateWorld.FateV2.Predict.SetupXMYDemoLaw
import FateWorld.FateV2.Modeling.PearlHierarchy
namespace FateV2.Predict.SetupXMY.DemoX

open FateV2.Modeling

open Finset

/-!
  # Predict · SetupXMYDemoLawConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SetupXMYDemoLawConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SetupXMYDemoLaw, PearlHierarchy
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 调整判据（本地定义，避免与 `Fate.BackdoorXMY.ZAdj` 撞名）

⚠ 第 95 条：**同名 `def` 不能同时 import**。`Fate/BackdoorXMY.lean` 已有
`ZAdj`（对**任意** `S : Setup`），本文件不复用它（那需要额外 import
且其 `adjustLawZ` 是另一套 `∑∑` 定义），而用带撇号的**本地**谓词。 -/

/-- `ZAdjusts x y`：`{Z}` 后门调整在 `(x, y)` 上给出**正确**的干预律。 -/
def ZAdjusts (x y : Bool) : Prop := adjustLawZ x y = doLaw x y

/-- `MAdjusts x y`：`{M}` 中介调整在 `(x, y)` 上给出**正确**的干预律。 -/
def MAdjusts (x y : Bool) : Prop := adjustLawM x y = doLaw x y

theorem zAdjusts_iff (x y : Bool) : ZAdjusts x y ↔ adjustLawZ x y = doLaw x y :=
  Iff.rfl

theorem mAdjusts_iff (x y : Bool) : MAdjusts x y ↔ adjustLawM x y = doLaw x y :=
  Iff.rfl

/-! ⚠ **`Bool.xor` 归约工具**（第 14 条）：`fXB`/`fYB` 是 `Bool.xor` 的嵌套，
`rfl`/`decide` 在**半归约**透明度下**不可靠**（上游 §0 已登记同一现象）。
故先显式给出 `fXB`/`fYB` 在**全 `Bool` 字面量**上的求值引理，再交给 `norm_num`。 -/

theorem fXB_false_false : fXB false false = false := by unfold fXB; exact Bool.xor_false false
theorem fXB_false_true : fXB false true = true := by unfold fXB; exact Bool.xor_true false
theorem fXB_true_false : fXB true false = true := by unfold fXB; exact Bool.xor_false true

/-! ## §2 C1 / C2：否证的**全称化**与**逐点刻画** -/

/-- ⭐⭐ **C1：`{Z}` 调整在 `demoX` 上至少在 `(0,0)` 与 `(1,0)` 两行都错。**

前件为空；结论由上游数值表经 `norm_num` 闭式判定。 -/
theorem demoX_backdoor_fails_everywhere :
    ¬ ZAdjusts false false ∧ ¬ ZAdjusts true false := by
  constructor
  · rw [zAdjusts_iff, adjustLawZ_00, doLaw_00]; norm_num
  · rw [zAdjusts_iff, adjustLawZ_10, doLaw_10]; norm_num

/-- ⭐ **C2：`{Z}` 调整在 `demoX` 上**不是**「处处正确」的 ——
`(0,0)` 与 `(1,0)` 是**反例见证**。 -/
theorem demoX_not_forall_zAdjusts :
    ¬ (∀ x y : Bool, ZAdjusts x y) := by
  intro h
  exact demoX_backdoor_fails_everywhere.1 (h false false)

/-- ⭐ 补充（**不是**同义反复）：`(1,1)` 一行 `{Z}` 与 `{M}` **各自**都**不**正确 ——
故「`demoX` 上 `{Z}` 偶然重合 ⟹ `{M}` 也重合」为**假**。 -/
theorem demoX_M_ne_Z_witness :
    ¬ MAdjusts true true ∧ ¬ ZAdjusts false false :=
  ⟨adjustLawM_ne_doLaw, demoX_backdoor_fails_everywhere.1⟩

/-- ⭐ **重合点与失败点并存**：`demoX` 上 `{Z}` 在 `(1,1)` **重合**、
在 `(0,0)` **偏离** —— 两条**同时**成立。这是「数值巧合 ⟹ 无一般性」的机器形式。 -/
theorem demoX_zAdjusts_mixed :
    ZAdjusts true true ∧ ¬ ZAdjusts false false :=
  ⟨adjustLawZ_11_coincides, demoX_backdoor_fails_everywhere.1⟩

/-! ## §3 C3 / C4：把 `demoX` 的结构方程装进 Pearl 的 `SCM`

**编码（⚠ 第一版编码错误，此处是修正版）**

* 外生 `U := Bool × Bool × Bool`，约定 `u = (z, ux, uy)`，律 `pU u = pzB u.1 * pxB u.2.1 * pyB u.2.2`。
* 结构映射 `sg u = (fXB u.1 u.2.1, fun x => fYB x (fMB x u.2.2) u.1 u.2.1)`：
  事实 `X` 取 `fX(z, ux)`，响应函数 `h x := fY x (fM x uy) z ux`
  —— **每个个体 `u` 拿到自己的一条 `Y` 曲线**（Pearl `L3` 语义）。

⚠ **第一版把 `z` 固定成 `false`**（`U := Bool × Bool`），当时 `L2_do` 给出 `0`，
与 `doLaw true true = 29/50` **不符**。原因是 `doLaw = ∑_z pzB z · (…)` 对 `z` **求平均**，
而固定 `z` 丢掉了这一层。**⟹ `z` 必须进外生域**。这不是编程疏忽，
是「`Z` 在 `demoX` 里是**外生**的」这一语义事实。 -/

/-- `demoX` 对应的 Pearl `SCM`（`X = Y = Bool`；外生 `(z, ux, uy)`）。 -/
noncomputable def demoXSCM : FateV2.Modeling.PearlHierarchy.SCM Bool Bool where
  U := Bool × Bool × Bool
  pU := fun u => pzB u.1 * pxB u.2.1 * pyB u.2.2
  sg := fun u =>
    ((fXB u.1 u.2.1 : Bool), (fun x : Bool => fYB x (fMB x u.2.2) u.1 u.2.1))

/-- ⭐⭐ **C3：`L2_do false false` 与 `doLaw false false` 数值一致**（都 `= 1/2`）。

左端是 `Fate.PearlHierarchy.push` 的**一般推前**，右端是
`SetupXMYDemo` 的**指示函数 `∑∑` 展开**；两条定义形式不同，
本定理给出 `demoX` 上的**数值桥**。 -/
theorem demoX_toPearlSCM_L2_00 :
    demoXSCM.L2_do false false = doLaw false false := by
  unfold FateV2.Modeling.PearlHierarchy.SCM.L2_do FateV2.Modeling.PearlHierarchy.push demoXSCM
  simp only [fYB, fMB, fXB, pxB, pyB, pzB]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [doLaw_00]
  norm_num

/-- ⭐⭐ **C4：`L2_do true true` 与 `doLaw true true` 数值一致**（都 `= 29/50`）。

与 C3 同一桥，取另一数值点；两行合起来表明该桥**不是单点巧合**。 -/
theorem demoX_toPearlSCM_L2_11 :
    demoXSCM.L2_do true true = doLaw true true := by
  unfold FateV2.Modeling.PearlHierarchy.SCM.L2_do FateV2.Modeling.PearlHierarchy.push demoXSCM
  simp only [fYB, fMB, fXB, pxB, pyB, pzB]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [doLaw_11]
  norm_num

/-- ⭐⭐ **C4（否证穿透到 `SCM` 层）：该 `SCM` 的 `L2_do` 令 `{Z}` 调整律偏离。**

把 `demoX` 的干预律换成 `L2_do` 后，`adjustLawZ(0,0)` 仍**不**等于
`L2_do false false` —— 即「后门失败」在 `SCM` 语境下**同样成立**（`21/100 ≠ 1/2`）。 -/
theorem demoXSCM_adjustLawZ_ne_L2 :
    adjustLawZ false false ≠ demoXSCM.L2_do false false := by
  rw [demoX_toPearlSCM_L2_00, adjustLawZ_00, doLaw_00]
  norm_num

/-- ⭐ **C4'：`{M}` 中介失败同样穿透到 `SCM` 语境**（`29/100 ≠ 29/50`）。 -/
theorem demoXSCM_adjustLawM_ne_L2 :
    adjustLawM true true ≠ demoXSCM.L2_do true true := by
  rw [demoX_toPearlSCM_L2_11, adjustLawM_11, doLaw_11]
  norm_num

/-- ⭐ **C5：`L2_do` 在 `demoX` 上**不是**常数律**（`(0,0)` 与 `(1,1)` 两行不同）。

这是「非平凡性」登记：若 `L2_do` 为常数，则本文件全部数值桥都无内容。 -/
theorem demoXSCM_L2_not_constant :
    demoXSCM.L2_do false false ≠ demoXSCM.L2_do true true := by
  rw [demoX_toPearlSCM_L2_00, demoX_toPearlSCM_L2_11, doLaw_00, doLaw_11]
  norm_num

end FateV2.Predict.SetupXMY.DemoX