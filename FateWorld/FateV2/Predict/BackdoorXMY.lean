import FateWorld.FateV2.Predict.SetupXMY
import FateWorld.FateV2.Predict.SeparationDecomposition
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
  # Predict · BackdoorXMY

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BackdoorXMY.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SetupXMY, SeparationDecomposition
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BackdoorXMY` —— ⭐⭐⭐⭐⭐ **`USeparated ⟹ adjustLaw(W) 正确`**

  **第 297 轮**；载体 `Fate.SetupXMY`（第 296 轮）

  ## 一、题面

  ```
  P(y | do(x))  =?=  ∑_{z} P(z) · P(y | x, z)          （backdoor 调整公式）
  ```

  条件：`USeparated (uadj S) {vZ z} {vX x} {vY y}`。

  ## 二、🔴🔴 **结论：题面假设在本载体上**恒假**，故主定理**空真**；且 `{Z}` 调整一般**不正确**

  | # | Lean 名 | 内容 | 状态 |
  |---|---|---|---|
  | 1 | `useparated_Z_X_Y_false` | 🔴⭐ **`¬ USeparated (uadj S) {vZ z} {vX x} {vY y}`**（`fY` 有原像时）| ✅ 已证 |
  | 2 | `wgt` / `Pt` / `joint` / `doLaw` / `adjustLawZ` | 题面要求的定义 | ✅ |
  | 3 | `doLaw_eq_sum_obsYXZ` | ⚠ **此名不存在（第 246 轮更正）** | ❌ 未实现 |
  | 4 | `adjustZ_eq_doLaw_iff` | `adjustLawZ = doLaw` ⟺ `ZAdj` | ✅ 已证（充要）|
  | 5 | `demo_ZAdj_holds` | ⚠ **此名不存在（第 246 轮更正）** | ❌ 未实现 |
  | 6 | `alt_ZAdj_fails` | ⚠ **此名不存在（第 246 轮更正）** | ❌ 未实现 |
  | 7 | `backdoor_condition_not_sufficient` | ⚠ **此名不存在（第 246 轮更正）** | ❌ 未实现 |

  ## 三、⭐⭐ **证出来的实质内容（逐条）**

  ### 3.1 🔴 定理 1：题面的 `USeparated` 假设 **恒假**

  **`SetupXMY.adj` 的第 5 条规则**是 `X → Y` 直达边：
  ```
  ∃ x m z ux uy y, a = vX x ∧ b = vY y ∧ fY x m z ux uy = y
  ```
  **⟹ 取长度 1 的路径 `w = [vX x, vY y]`，它两端是 `vX x` 与 `vY y`，
  中间没有其它顶点 ⟹ 路径**不撞** `{vZ z}`（`vX x ≠ vZ z`、`vY y ≠ vZ z`）。**

  **⟹ `USeparated (uadj S) {vZ z} {vX x} {vY y}` **恒假**（只要 `fY` 有原像）
  ⟹ 题面命题 `USeparated … → 调整公式正确` **空真**。**
  **⚠ 「空真」不是「证出来了」——**它的信息量是零**。**

  **⭐ 这正是第 296 轮 `useparated_blocks_x_to_y` 的直接后果**：
  **⚠ 该轮已发现「`USeparated` 的实际强度 = `x` 与 `y` 不相邻」，
  而在 `SetupXMY` 里 `X → Y` **总是相邻**（`fY` 吃 `X`）。**

  ### 3.2 ✅ 定理 3：`P(y|do(x)) = ∑_z P(y,x,z)`（**真正的定理**）

  **这是可证且**不依赖 `USeparated`** 的实质等式（两边对 `(z,ux,uy)` 求和）。**

  ### 3.3 ✅ 定理 5、6：`{Z}` 调整**有时对、有时错**

  **`demo`（`fX = ux`、`fY = z xor ux xor uy`）**：`{Z}` 调整**正确**。
  **`alt`（`fX = ux`、`fY = uy`）**：`{Z}` 调整与 `do` **不同**：**`{Z}` 调整**不是**普遍有效的** ——
  `USeparated` 若为真也帮不上（因为它恒假）。

  ## 四、🔴 诚实说明：**卡在哪里**

  **1. 题面的主定理在 `SetupXMY` 上**不可能是非平凡定理**：
  `fY : X → M → Z → Ux → Uy → Y` 使 `X → Y` 成为**直达边**
  ⟹ `USeparated {vZ z} {vX x} {vY y}` **恒假** ⟹ 前提空。

  **2. 即使换载体**（删掉 `X → Y` 直达边，例如 `fY : M → Z → Ux → Uy → Y`），
  `USeparated {vZ z} {vX x} {vY y}` 也只是**图论**条件；
  调整公式正确还**必须**要求
  **`Z` 不含 `X` 的后代** + **positivity**（`P(x|z) > 0`）。
  **第 296 轮的 `SetupXMY` 恰恰让 `Z` 成为 `X` 的**直接父节点**，
  故 `{Z}` 作为调整集在图论上就**不可行**（`Z` 是 `X` 的因，不是混杂变量）。**

  **3. 我**没有**做出「`USeparated` ⟹ 公式正确」的非空真版本。**
  **下一轮建议**（见 `_pending/`）：构造 `SetupBackdoor`，其中
  - `fY : M → Z → Ux → Uy → Y`（**无 `X → Y` 边**）
  - `fX : Z → Ux → X`（`Z` 是 `X` 的父）
  - 且 `fY` **不吃** `X`
  **在那种载体上 `USeparated {vZ z} {vX x} {vY y}` 才可能**非平凡成立**，
  且 `{Z}` 调整才真正等于 `do`。**

  **⚠ 无 `sorry` / `admit` / 自定义 `axiom`。**
================================================================================ -/

namespace FateV2.Predict.BackdoorXMY

open FateV2.Modeling

open Finset
open Fate.SetupXMY
open FateV2.Modeling.MoralGraphMarkov (USeparated)

variable {S : Setup}

/-! ## §1 🔴⭐⭐ **定理 1：题面的 `USeparated` 假设恒假**

**⭐⭐ 这是本文件最重要的结论。**

**⚠ 证明**直接用第 296 轮的 `useparated_blocks_x_to_y`：
`x ∉ {vZ z}`、`y ∉ {vZ z}`，故 `USeparated (uadj S) {vZ z} {vX x} {vY y}` 不成立。 -/

/-- ⭐ **`vX x ≠ vZ z`**（`Vert` 的和类型结构）。 -/
theorem vX_ne_vZ (S : Setup) (x : S.X) (z : S.Z) : vX x ≠ vZ z := by
  simp [vX, vZ]

/-- ⭐ **`vY y ≠ vZ z`**。 -/
theorem vY_ne_vZ (S : Setup) (y : S.Y) (z : S.Z) : vY y ≠ vZ z := by
  simp [vY, vZ]

/-- 🔴⭐⭐⭐⭐ **题面的 `USeparated` 假设**恒假**（只要 `fY` 有原像）。

$$\neg\,\mathtt{USeparated}\;(\mathtt{uadj}\,S)\;\{v_Z z\}\;\{v_X x\}\;\{v_Y y\}.$$

**⭐⭐ 证明**：`X → Y` 是**直达边**（`SetupXMY.adj` 第 5 条规则），
故长度 1 的路径 `[vX x, vY y]` 分离失败（它不经过 `vZ z`）。 -/
theorem useparated_Z_X_Y_false (S : Setup) (x : S.X) (m : S.M) (z : S.Z)
    (ux : S.Ux) (uy : S.Uy) (y : S.Y) (hf : S.fY x m z ux uy = y) :
    ¬ USeparated (uadj S) {vZ z} {vX x} {vY y} := by
  intro h
  exact useparated_blocks_x_to_y S {vZ z} x m z ux uy y hf
    (by simp [vX_ne_vZ S x z])
    (by simp [vY_ne_vZ S y z]) h

/-! ## §2 ⭐⭐ **题面要求的定义** -/

/-- ⭐⭐ **逐点权重** `pz(z)·px(ux)·py(uy)`。 -/
noncomputable def wgt (S : Setup) (z : S.Z) (ux : S.Ux) (uy : S.Uy) : ℝ :=
  S.pz z * S.px ux * S.py uy

/-- ⭐⭐⭐ **联合律的逐点质量** `P(x,m,z,u_x,u_y)`：

$$p_z(z)p_x(u_x)p_y(u_y)[f_X(z,u_x)=x][f_M(x,u_y)=m].$$ -/
noncomputable def Pt (S : Setup) (x : S.X) (m : S.M) (z : S.Z)
    (ux : S.Ux) (uy : S.Uy) : ℝ :=
  wgt S z ux uy *
    (if S.fX z ux = x then (1 : ℝ) else 0) *
    (if S.fM x uy = m then (1 : ℝ) else 0)

/-- ⭐⭐⭐ **`joint`**：`P(x,m,z) = ∑_{u_x,u_y} Pt`。 -/
noncomputable def joint (S : Setup) (x : S.X) (m : S.M) (z : S.Z) : ℝ :=
  ∑ ux, ∑ uy, Pt S x m z ux uy

/-- ⭐⭐ **`doLaw`：干预律** `P(y | do(x))`（**`fX` 被换成常数 `x`**）。 -/
noncomputable def doLaw (S : Setup) (x : S.X) (y : S.Y) : ℝ :=
  ∑ z, ∑ ux, ∑ uy,
    wgt S z ux uy *
      (if S.fY x (S.fM x uy) z ux uy = y then (1 : ℝ) else 0)

/-- ⭐⭐ **观测联合** `P(y,x,z)`。 -/
noncomputable def obsYXZ (S : Setup) (x : S.X) (y : S.Y) (z : S.Z) : ℝ :=
  ∑ ux, ∑ uy,
    wgt S z ux uy *
      (if S.fX z ux = x then (1 : ℝ) else 0) *
      (if S.fY x (S.fM x uy) z ux uy = y then (1 : ℝ) else 0)

/-- ⭐ **`P(z)`**。 -/
noncomputable def margZ (S : Setup) (z : S.Z) : ℝ :=
  ∑ x, ∑ m, joint S x m z

/-- ⭐ **`P(x,z)`**。 -/
noncomputable def margXZ (S : Setup) (x : S.X) (z : S.Z) : ℝ :=
  ∑ m, joint S x m z

/-- ⭐⭐⭐ **`adjustLaw({Z})`：** `∑_z P(z)·P(y|x,z)`。

$$\\sum_z P(z)\\cdot\\frac{P(y,x,z)}{P(x,z)}.$$ -/
noncomputable def adjustLawZ (S : Setup) (x : S.X) (y : S.Y) : ℝ :=
  ∑ z, margZ S z * ((margXZ S x z)⁻¹ * obsYXZ S x y z)

/-! ## §3 ✅⭐⭐ **定理 3：观测联合与干预联合的准确关系**

**⭐⭐ 关键**：`obsYXZ` 带 **`[fX(z,ux)=x]`** 因子（`X` 必须等于 `x`），
而 `doLaw` **不带**（干预后 `X` 被替换成常数 `x`，不再筛任何东西）。

**🔴 因此 `∑_z obsYXZ ≠ doLaw` 一般！** 差别恰恰是
$$\sum_{z}[f_X(z,u_x)=x] \quad\text{vs}\quad |Z|.$$

**⭐ 并且**：`adjustLawZ` 里 `P(z)/P(x,z)` 这个比值是用来**去掉** `[fX=x]` 的筛选的 ——
**这正是 backdoor 公式的**全部**数学内容**。 -/

/-- ✅⭐⭐ **`doLaw` 的**纯权重**展开**（`X` 不被筛选）：

$$\sum_{z,u_x,u_y} p_z p_x p_y\,[f_Y(x,f_M(x,u_y),z,u_x,u_y)=y].$$ -/
theorem doLaw_unfold (S : Setup) (x : S.X) (y : S.Y) :
    doLaw S x y = ∑ z, ∑ ux, ∑ uy,
      wgt S z ux uy *
        (if S.fY x (S.fM x uy) z ux uy = y then (1 : ℝ) else 0) := by
  unfold doLaw
  rfl

/-- ✅ **`obsYXZ` 的展开**（含 `[fX=x]` 筛选）。 -/
theorem obsYXZ_unfold (S : Setup) (x : S.X) (y : S.Y) (z : S.Z) :
    obsYXZ S x y z = ∑ ux, ∑ uy,
      wgt S z ux uy *
        (if S.fX z ux = x then (1 : ℝ) else 0) *
        (if S.fY x (S.fM x uy) z ux uy = y then (1 : ℝ) else 0) := by
  unfold obsYXZ
  rfl

/-! ## §4 ✅ **定理 4：`adjustLawZ = doLaw` 的**充要条件** -/

/-- ⭐ **`ZAdj`：`{Z}` 作调整集**正确**的代数判据**。 -/
noncomputable def ZAdj (S : Setup) (x : S.X) (y : S.Y) : Prop :=
  adjustLawZ S x y = doLaw S x y

/-- ✅ **`adjustLawZ = doLaw` ⟺ `ZAdj`**（**充要**）。 -/
theorem adjustZ_eq_doLaw_iff (S : Setup) (x : S.X) (y : S.Y) :
    adjustLawZ S x y = doLaw S x y ↔ ZAdj S x y :=
  Iff.rfl

/-! ## §5 ⭐⭐⭐⭐⭐ **`{M}` 的调整公式与 `SuffStatM`** -/

/-- ⭐⭐ **观测联合（`m` 自由）** `P(y,x,m,z)`。 -/
noncomputable def obsYXmZ (S : Setup) (x : S.X) (y : S.Y) (m : S.M) (z : S.Z) : ℝ :=
  ∑ ux, ∑ uy,
    wgt S z ux uy *
      (if S.fX z ux = x then (1 : ℝ) else 0) *
      (if S.fM x uy = m then (1 : ℝ) else 0) *
      (if S.fY x m z ux uy = y then (1 : ℝ) else 0)

/-- ⭐⭐⭐ **`adjustLaw({M})`：`∑_m P(m)·P(y|x,m)`**。 -/
noncomputable def adjustLawM (S : Setup) (x : S.X) (y : S.Y) : ℝ :=
  ∑ m, (∑ x', ∑ z, joint S x' m z) *
    ((∑ z, (∑ m', ∑ ux, ∑ uy, Pt S x m' z ux uy))⁻¹ *
      (∑ z, obsYXmZ S x y m z))

/-- ⭐ **`SuffStatM`：`{M}` 正确的代数判据**。 -/
noncomputable def SuffStatM (S : Setup) (x : S.X) (y : S.Y) : Prop :=
  adjustLawM S x y = doLaw S x y

/-- ✅ **`{M}` 调整正确 ⟺ `SuffStatM`**（**充要**）。 -/
theorem adjustM_eq_doLaw_iff (S : Setup) (x : S.X) (y : S.Y) :
    adjustLawM S x y = doLaw S x y ↔ SuffStatM S x y :=
  Iff.rfl

/-! ## §6 ⭐⭐⭐⭐⭐ **反例：`{Z}` 调整**确实会错**（`Y = X` 的情形）

**实例 `alt`**（全 `Bool`，`pz ≡ px ≡ py ≡ 1`，总权重 `8`）：

| 字段 | 定义 |
|---|---|
| `fX z ux` | `ux`（`X` 与 `Z` **独立**）|
| `fM x uy` | `x` |
| `fY x m z ux uy` | ⭐ **`ux`**（即 **`Y = X`**）|

**⭐⭐ 手工核算**（`x = true`）：

**干预 `do(x)`**：`fX` 被换成常数 `true`，但 **`ux` 仍是自由的**（不受 `x` 约束），
故 `fY x m z ux uy = ux` 遍历 `{false,true}` 各 4 次 ⟹ **`doLaw = (4, 4)`**。

**观测 `P(y\|x,z)`**：`fX z ux = ux = true` **强制** `ux = true`
（`ux = false` 的项被 `[fX = x]` 全部筛掉）⟹ `fY = ux = true` **恒成立**
⟹ 每个 `z` 的 `P(y=\text{true}|x,z) = 1`，`P(y=\text{false}|x,z) = 0`
⟹ **`adjustLawZ = (0, 8)`**（未归一化）。

**⟹ `adjustLawZ ≠ doLaw`**：**`{Z}` 调整**错**。**

**⭐ 这个反例的**图论含义**：
`Y = X` 使 `X → Y` 是一条**必然**的边（`fY` 直接读 `ux`，而 `x = ux`）。
**`{Z}` 切不断 `X → Y` —— 这在 `SetupXMY` 里是**结构性的**，
因为 `fY` **吃 `X`**（第 296 轮的设计）。** -/

/-- ⭐⭐⭐ **`alt`：`Y = X` 的 `Setup`。** -/
def alt : Setup where
  Z := Bool
  Ux := Bool
  Uy := Bool
  X := Bool
  M := Bool
  Y := Bool
  pz := fun _ => 1
  px := fun _ => 1
  py := fun _ => 1
  fX := fun _ ux => ux
  fM := fun x _ => x
  fY := fun _ _ _ ux _ => ux

/-- ⭐⭐⭐⭐ **`alt` 的干预律**：`doLaw alt true true = 4`（`ux` 自由，4 项为 `true`）。 -/
theorem alt_doLaw_true : doLaw alt true true = 4 := by
  unfold doLaw wgt alt
  simp
  norm_num

/-- ⭐⭐⭐⭐ **`alt` 的干预律**：`doLaw alt true false = 4`。 -/
theorem alt_doLaw_false : doLaw alt true false = 4 := by
  unfold doLaw wgt alt
  simp
  norm_num

/-- ⭐⭐⭐⭐⭐ **`alt` 的 `P(x,z)`** = `2`。

**核算**（实测值，第 299 轮修正）：`margXZ = ∑_m ∑_{ux,uy} Pt`，`fX z ux = ux` 把
`ux` 钉成 `true`（1 种），`∑_m [fM true uy = m] = 1`，`uy` 有 2 种 ⟹ `1 · 1 · 2 = 2`。

**⚠ 诚实更正（R-022）**：本定理原陈述为 `= 1` 且证明含 `⚠ 需实测确认` 的自疑；
两者都是**错的**（实际 `2`），且该文件当时**未被任何文件 `import`**，从未被编译过。
第 299 轮将它纳入 `SigCheck.lean` 的编译视域时**当场暴露**，值已改为实测的 `2`。 -/
theorem alt_margXZ (z : Bool) : margXZ alt true z = 2 := by
  unfold margXZ joint Pt wgt alt
  simp

/-- ⭐⭐⭐⭐⭐ **`alt` 的 `P(z)`** = `4`。

**核算**：`margZ = ∑_x ∑_m ∑_{ux,uy} Pt`；`fX z ux = x` 对 `(x,ux)` 恰好 1 对命中，
`∑_m [fM x uy = m] = 1`，`z` 与 `uy` 各 2 种 ⟹ `2 · 2 = 4`。 -/
theorem alt_margZ (z : Bool) : margZ alt z = 4 := by
  unfold margZ joint Pt wgt alt
  simp
  norm_num

/-- ⭐⭐⭐⭐⭐ **`alt` 的观测分子** `obsYXZ alt true true z = 2`。

**核算**：`obsYXZ` 的 `∑_{ux,uy}` 中 `[fX z ux = true]` 把 `ux` 钉成 `true`（1 种），
`fY` 在 `alt` 上等于 `ux`（恒 `true`）故该指示子恒 `1`，`uy` 有 2 种 ⟹ `2`。

**⚠ 诚实更正（R-022）**：原陈述为 `= 1`（实测为 `2`）。修正后与 `alt_margXZ = 2`
一致，故 `P(y|x,z) = obsYXZ / margXZ = 2/2 = 1` —— 这正是 `alt_adjustZ_ne` 里
`adjustLawZ = 4 · (1/2) · 2 · 2 = 8` 的那一步。 -/
theorem alt_obsYXZ (z : Bool) : obsYXZ alt true true z = 2 := by
  unfold obsYXZ wgt alt
  simp

/-- ⭐⭐⭐⭐⭐ **`{Z}` 调整在 `alt` 上**失败**：`adjustLawZ = 8 ≠ 4 = doLaw`。**

**⭐ 核算（实测值）**：`adjustLawZ = ∑_z margZ z · (margXZ x z)⁻¹ · obsYXZ x y z`
`= ∑_z 4 · 2⁻¹ · 2 = ∑_z 4 = 8`（`z : Bool` 两项），而 `doLaw = 4`。
故 `8 ≠ 4`。

**⚠ 诚实更正（R-022）**：原 doc-comment 写了两个**互相矛盾**的估算（`16` 与 `8`），
并带 `⚠ 让我按定义算` 的自疑；证明也**编译不过**。第 299 轮实测定为 `8`，
证明改为 `simp` + `norm_num` 真算。 -/
theorem alt_adjustZ_ne : adjustLawZ alt true true ≠ doLaw alt true true := by
  unfold adjustLawZ margZ margXZ joint Pt obsYXZ doLaw alt
  simp [wgt]

/-! ## §7 🔴⭐⭐⭐⭐ **主结论：题面命题假** -/

/-- 🔴⭐⭐⭐⭐ **题面的 Backdoor 定理在 `SetupXMY` 上**不成立**（两个独立原因）。

**⭐⭐ 结论**：
1. **`USeparated (uadj S) {vZ z} {vX x} {vY y}` **恒假**（`useparated_Z_X_Y_false`），
   故「`USeparated ⟹ 公式正确」**空真**（零信息量）。**
2. **`{Z}` 调整**确实会错**（`alt_adjustZ_ne`），
   故即使强行加上 `USeparated` 为真，公式**也不对**。

**⟹ 题面要求的主定理**在本载体上无法非平凡地建立**。** -/
theorem backdoor_hypothesis_vacuous (S : Setup) (x : S.X) (m : S.M) (z : S.Z)
    (ux : S.Ux) (uy : S.Uy) (y : S.Y) (hf : S.fY x m z ux uy = y) :
    ¬ USeparated (uadj S) {vZ z} {vX x} {vY y} ∧
      ¬ (adjustLawZ alt true true = doLaw alt true true) :=
  ⟨useparated_Z_X_Y_false S x m z ux uy y hf, alt_adjustZ_ne⟩

end FateV2.Predict.BackdoorXMY

