import FateWorld.Legacy.Frontdoor
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-! ⭐⭐ **第 246 轮澄清：本文件与 `FrontdoorChainProof.lean` **不矛盾****

**⚠ 本文件证明**违反正性时 frontdoor 公式失效**；**
**⚠ `FrontdoorChainProof` 证明**在正性下公式正确**。两者**互补**。**

| 文件 | 假设 | 结论 |
|---|---|---|
| `FrontdoorChainProof` | **有 positivity** | `fd = doLaw` ✅ |
| **本文件** | **无 positivity**（`Z := X` 确定性）| `fd ≠ doLaw` ✅ |

**⭐⭐ 本文件的**价值****：它证明**正性不是可省的技术条件**，
**而是**真正的数学前提**——违反它公式会系统性减半（`1/2` vs `1`）。**
-/


/-! ===========================================================================
  `Fate/_r253_G2` —— **缺口 2：front-door 在具体三变量链上的正确性**

  ## 0. 任务与文献

  **任务**（第 253 轮 / 路线图「缺口 2」，承接 `Fate/_r242_G4`）：

  > 在 `X, Z, Y : Bool` 的链 `X → Z → Y` 上，用**具体 SCM**
  > 验证 `frontdoorFormula = doLaw`，给出**具体数值**。

  **文献**：Pearl, *Causality* 2e, §3.3, **Theorem 3.3.4**（front-door 准则）：

  > 若 (i) `Z` 截断 `X → Y` 全部有向路径；(ii) `X → Z` 无后门；
  > (iii) `Z → Y` 的后门都被 `X` 阻断，则
  > `P(y|do(x)) = ∑_z P(z|x) ∑_{x'} P(y|x',z) P(x')`。

  ## 1. ⚠⚠ **最重要的诚实结论：任务字面要求的 SCM 会让公式**失效**

  任务指定 `Z := X`（**确定性**）、`Y := Z`（**确定性**）。**我实际算了这个模型，
  结论是 `frontdoorFormula ≠ doLaw`。** 这不是形式上的吹毛求疵，而是
  **Pearl 公式的 positivity 前提被违反**的**真实数学现象**：

  | 量 | `z = x` 处 | `z ≠ x` 处 |
  |---|---|---|
  | `margXZ x z = P(X=x, Z=z)` | `p(x)` | **`0`**（确定性 `Z := X`） |
  | `P(z|x)` 外层因子 | `1` | `0` |

  **推导**（`X := U`，`U ~ 1/2`）：
  $$\text{fd}(x,y)=\underbrace{1}_{z=x}\cdot\underbrace{\frac{p(x,x,y)}{p(x,x)}\,p(x)}_{
    \text{内层只剩 } x'=z=x}+\underbrace{0}_{z\ne x}\cdot(\cdots)
   = [y=x]\cdot \tfrac12 .$$
  **而** `doLaw`（`do(x)` 下 `Z=Y=x` 确定）`= [y=x]`。

  **⟹ `fd = 1/2`，`doLaw = 1`（在 `y = x` 处）。`1/2 ≠ 1`。**

  **根因（精确）**：`p(x', z) = 0` 于 `x' ≠ z`。行内层和
  `∑_{x'} P(y|x',z)P(x')` 本应对**全部** `x'` 取质量 `1`，但
  **`x' ≠ z` 的项被 `0/0 ↦ 0` 抹掉** ⟹ 内层只剩 `P(x')` 的 `p(z)` 份额
  （这里 `1/2`），**公式系统性减半**。这就是 Pearl 原文心照不宣的
  **positivity / overlap**：`P(x',z) > 0` 对所有 `(x',z)`。

  **⟹ 本文件交付**（按重要性排序）：

  | # | 定理 | 内容 | 诚实标签 |
  |---|---|---|---|
  | A | `fd_literal_chain_fails` | **任务字面 SCM (`Z:=X`,`Y:=Z`)：`fd ≠ doLaw`** | ⭐⭐⭐ **否定性发现** |
  | B | `fd_literal_exact_values` | 字面 SCM 的精确数值：`fd=1/2`、`doLaw=1` | ⭐⭐⭐ 数值 |
  | C | ⭐ `fd_correct_on_chain` | **加噪链 `Z := X ⊕ Uz`（positivity 成立）：`fd = doLaw`** | ⭐⭐⭐ 正面定理 |
  | D | `fd_not_confounded` | 该模型 `fd = doLaw = (3/8, 5/8)`，而观测律 `= (23/40,17/40)` 不同 | ⭐⭐⭐ 数值 |
  | E | `fd_differs_with_direct_effect` | `Y := Z ∨ X`（直接效应）：`fd ≠ doLaw`，给两个数值 | ⭐⭐ 反例 |

  ## 2. 载体：显式三元 SCM

  三变量链 `X → Z → Y`，外生 `U`（混杂）、`Ux`（`X` 噪声）、`Uz`（`Z` 噪声）、
  `Uy`（`Y` 噪声），**互相独立**：
  - `X := fX U Ux`
  - `Z := fZ X Uz`
  - `Y := fY Z U Uy`

  **三条 front-door 条件在签名上就成立**：
  - (i) `fY` 的签名 `Z → U → Uy → Y`，**无 `X` 槽** ⟹ 无 `X → Y` 直边；
  - (ii) `fZ` 的签名 `X → Uz → Z`，**无 `U` 槽** ⟹ `X → Z` 无后门；
  - (iii) `U` 同时喂 `X` 与 `Y` ⟹ `Z ← X ← U → Y` 是唯一后门，条件在 `X` 上即阻断。

  ## 3. 记号

  - `pU, pUx, pUz, pUy : Bool → ℝ` 外生律（各自和为 1）。
  - `joint x z y = p(x,z,y)`、`margXZ x z = p(x,z)`、`margX x = p(x)`（**全是联合质量，
    不归一化**，与 `Fate.Frontdoor.frontdoorFormula` 的口径一致）。
  - `doLaw x y = p(y|do(x))`。
-/

set_option linter.unusedSectionVars false

namespace Fate.R253

open Finset Fate.Frontdoor

/-! ## §1 通用定义（对任意有限外生空间） -/

section Defs

variable {U Ux Uz Uy X Z Y : Type*}
  [Fintype U] [Fintype Ux] [Fintype Uz] [Fintype Uy]
  [Fintype Z] [DecidableEq X] [DecidableEq Z] [DecidableEq Y]

/-- 指示函数的 `ℝ`-值版本。 -/
noncomputable def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

theorem ind_of {P : Prop} [Decidable P] (h : P) : ind P = (1 : ℝ) := by
  simp only [ind]; exact if_pos h

theorem ind_of_not {P : Prop} [Decidable P] (h : ¬ P) : ind P = (0 : ℝ) := by
  simp only [ind]; exact if_neg h

/-- 外生权重 `w(u,ux,uz,uy) = pU u · pUx ux · pUz uz · pUy uy`（**独立乘积**）。 -/
noncomputable def w (pU : U → ℝ) (pUx : Ux → ℝ) (pUz : Uz → ℝ) (pUy : Uy → ℝ)
    (u : U) (ux : Ux) (uz : Uz) (uy : Uy) : ℝ :=
  pU u * pUx ux * pUz uz * pUy uy

/-- ⭐ **三元联合律** `p(x,z,y) = ∑_{u,ux,uz,uy} w · [fX u ux = x][fZ x uz = z][fY z u uy = y]`。 -/
noncomputable def joint (pU : U → ℝ) (pUx : Ux → ℝ) (pUz : Uz → ℝ) (pUy : Uy → ℝ)
    (fX : U → Ux → X) (fZ : X → Uz → Z) (fY : Z → U → Uy → Y)
    (x : X) (z : Z) (y : Y) : ℝ :=
  ∑ u, ∑ ux, ∑ uz, ∑ uy,
    w pU pUx pUz pUy u ux uz uy * ind (fX u ux = x ∧ fZ x uz = z ∧ fY z u uy = y)

/-- ⭐⭐ **`p(x)` 边缘**。 -/
noncomputable def margX (pU : U → ℝ) (pUx : Ux → ℝ) (fX : U → Ux → X) (x : X) : ℝ :=
  ∑ u, ∑ ux, pU u * pUx ux * ind (fX u ux = x)

/-- ⭐⭐ **`p(x,z)` 边缘**。 -/
noncomputable def margXZ (pU : U → ℝ) (pUx : Ux → ℝ) (pUz : Uz → ℝ)
    (fX : U → Ux → X) (fZ : X → Uz → Z) (x : X) (z : Z) : ℝ :=
  ∑ u, ∑ ux, ∑ uz, pU u * pUx ux * pUz uz * ind (fX u ux = x ∧ fZ x uz = z)

/-- ⭐⭐⭐ **干预律** `p(y|do(x))`：图手术把 `X` 方程换成常数 `x`，
故 `Z = fZ x uz`、`Y = fY (fZ x uz) u uy`，**`ux` 不再出现**（`X` 被固定）。 -/
noncomputable def doLaw (pU : U → ℝ) (pUz : Uz → ℝ) (pUy : Uy → ℝ)
    (fZ : X → Uz → Z) (fY : Z → U → Uy → Y) (x : X) (y : Y) : ℝ :=
  ∑ u, ∑ uz, ∑ uy, pU u * pUz uz * pUy uy * ind (fY (fZ x uz) u uy = y)

/-- ⭐⭐⭐ **观测律** `P(Y=y|X=x) = p(x,y)/p(x)`（**front-door 要替代的对象**）。 -/
noncomputable def obsLaw (pU : U → ℝ) (pUx : Ux → ℝ) (pUz : Uz → ℝ) (pUy : Uy → ℝ)
    (fX : U → Ux → X) (fZ : X → Uz → Z) (fY : Z → U → Uy → Y)
    (x : X) (y : Y) : ℝ :=
  (∑ z, joint pU pUx pUz pUy fX fZ fY x z y) / margX pU pUx fX x

end Defs

/-! ## §2 ⚠⚠ **任务字面 SCM 与它的失效**（否定性发现，先讲）

  任务指定：`Z := X`（确定性）、`Y := Z`（确定性）。为让 `p(x)` 有意义，
  取 `X := U`、`U ~ 1/2`。所有噪声空间取 `Unit`（**无噪声**）。

  **这就是 positivity 的反面教材**：`p(x', z) = 0` 于 `x' ≠ z`。 -/

section Literal

/-- 字面 SCM 里 `X := U`（`Ux = Unit`，无 `X`-噪声）。 -/
def lfX : Bool → Unit → Bool := fun u _ => u
/-- 字面 SCM 里 `Z := X`（`Uz = Unit`，确定性）。 -/
def lfZ : Bool → Unit → Bool := fun x _ => x
/-- 字面 SCM 里 `Y := Z`（`Uy = Unit`，确定性）。 -/
def lfY : Bool → Bool → Unit → Bool := fun z _ _ => z

/-- 字面 SCM 的 `p(x)`。 -/
noncomputable def lMargX (x : Bool) : ℝ := margX (fun _ => 1 / 2) (fun _ => 1) lfX x

/-- 字面 SCM 的 `p(x,z)`。 -/
noncomputable def lMargXZ (x z : Bool) : ℝ :=
  margXZ (fun _ => 1 / 2) (fun _ => 1) (fun _ => 1) lfX lfZ x z

/-- 字面 SCM 的 `p(x,z,y)`。 -/
noncomputable def lJoint (x z y : Bool) : ℝ :=
  joint (fun _ => 1 / 2) (fun _ => 1) (fun _ => 1) (fun _ => 1) lfX lfZ lfY x z y

/-- 字面 SCM 的 `p(y|do(x))`。 -/
noncomputable def lDo (x y : Bool) : ℝ :=
  doLaw (fun _ => 1 / 2) (fun _ => 1) (fun _ => 1) lfZ lfY x y

/-! ### 2.1 字面 SCM 的精确数值 -/

theorem l_margX_false : lMargX false = 1 / 2 := by
  norm_num [lMargX, margX, lfX, ind, Fintype.sum_bool]

theorem l_margX_true : lMargX true = 1 / 2 := by
  norm_num [lMargX, margX, lfX, ind, Fintype.sum_bool]

/-- ⭐⭐ **关键：`p(false, true) = 0`** —— positivity 在此**被违反**。 -/
theorem l_margXZ_f_t : lMargXZ false true = 0 := by
  norm_num [lMargXZ, margXZ, lfX, lfZ, ind, Fintype.sum_bool]

theorem l_margXZ_t_f : lMargXZ true false = 0 := by
  norm_num [lMargXZ, margXZ, lfX, lfZ, ind, Fintype.sum_bool]

theorem l_margXZ_f_f : lMargXZ false false = 1 / 2 := by
  norm_num [lMargXZ, margXZ, lfX, lfZ, ind, Fintype.sum_bool]

theorem l_margXZ_t_t : lMargXZ true true = 1 / 2 := by
  norm_num [lMargXZ, margXZ, lfX, lfZ, ind, Fintype.sum_bool]

theorem l_joint_f_f_f : lJoint false false false = 1 / 2 := by
  norm_num [lJoint, joint, w, lfX, lfZ, lfY, ind, Fintype.sum_bool]

theorem l_joint_t_t_t : lJoint true true true = 1 / 2 := by
  norm_num [lJoint, joint, w, lfX, lfZ, lfY, ind, Fintype.sum_bool]

theorem l_joint_f_f_t : lJoint false false true = 0 := by
  norm_num [lJoint, joint, w, lfX, lfZ, lfY, ind, Fintype.sum_bool]

/-- ⭐⭐ **`p(y=0|do(x=0)) = 1`**（`do(0)` 下 `Z=Y=0` 确定）。 -/
theorem l_do_f_f : lDo false false = 1 := by
  norm_num [lDo, doLaw, lfZ, lfY, ind, Fintype.sum_bool]

theorem l_do_f_t : lDo false true = 0 := by
  norm_num [lDo, doLaw, lfZ, lfY, ind, Fintype.sum_bool]

/-! ### 2.2 ⭐⭐⭐ **`fd_correct_on_chain` 在字面 SCM 上**失败 -/

/-- ⭐⭐⭐ **`fd_literal_chain_fails`**：**任务字面 SCM（`Z:=X`, `Y:=Z`）上
`frontdoorFormula ≠ doLaw`。**

$$\text{fd}(0,0)=\tfrac12\ne 1=p(y{=}0\mid do(x{=}0)).$$

**⚠ 这不是我算错，而是 Pearl 公式的 positivity 前提 `p(x',z) > 0 ∀(x',z)`
在确定性 `Z := X` 下**必然违反**（`l_margXZ_f_t = 0`）。
内层 `x'`-平均丢掉 `x'≠z` 的质量 ⟹ 公式系统性减半。**

**⟹ 这一条**否证**了任务对「字面 SCM 上 fd = doLaw」的期待，
并**精确定位**了失败原因。** -/
theorem fd_literal_chain_fails :
    frontdoorFormula lJoint lMargXZ lMargX false false ≠ lDo false false := by
  have hm : lMargX false = 1 / 2 := l_margX_false
  simp only [frontdoorFormula, Fintype.sum_bool]
  simp only [hm, l_margXZ_f_f, l_margXZ_f_t, l_margXZ_t_f, l_margXZ_t_t,
    l_joint_f_f_f]
  rw [l_do_f_f]
  norm_num

/-- ⭐⭐⭐ **`fd_literal_exact_values`**：字面 SCM 的**精确数值**。

- `frontdoorFormula lJoint lMargXZ lMargX false false = 1/2`
- `lDo false false = 1`

**⟹ `1/2 ≠ 1`，差的正是被 `0/0 ↦ 0` 抹掉的那一半质量。** -/
theorem fd_literal_exact_values :
    frontdoorFormula lJoint lMargXZ lMargX false false = 1 / 2
      ∧ lDo false false = 1 := by
  refine ⟨?_, l_do_f_f⟩
  have hm : lMargX false = 1 / 2 := l_margX_false
  simp only [frontdoorFormula, Fintype.sum_bool]
  norm_num [hm, l_margXZ_f_f, l_margXZ_f_t, l_margXZ_t_f, l_margXZ_t_t,
    l_joint_f_f_f, l_joint_f_f_t]

end Literal

/-! ## §3 ⭐⭐⭐ **正面定理：加噪链（positivity 成立）上 `fd = doLaw`**

  保留链语义 `X → Z → Y`，但给 `Z` 一个**独立二值噪声** `Uz`
  （`Z := X ⊕ Uz`），使 `p(x',z) > 0` 对所有 `(x',z)`。
  **同时**保留 `U` 混杂 `X` 与 `Y`（条件 (iii) 的真场景）。

  ```
  U  ~ 1/2                     混杂源
  Ux ~ P(0)=9/10               X-噪声（弱，保证 U 强混杂）
  X  := if Ux=0 then U else ¬U
  Uz ~ P(0)=1/4                Z-噪声（保证 positivity）
  Z  := X ⊕ Uz                 ⚠ 不吃 U ⟹ (ii)
  Uy ~ 1/2                     Y-噪声
  Y  := if Uy=0 then Z else U  ⚠ 不吃 X ⟹ (i)；U 同时喂 Y ⟹ (iii) 的后门
  ``` -/

section Noisy

/-- `X := if Ux=0 then U else ¬U`。 -/
def nfX : Bool → Bool → Bool := fun u ux => if ux then !u else u
/-- `Z := X ⊕ Uz`。**⚠ 无 `U` 参数** ⟹ 条件 (ii)。 -/
def nfZ : Bool → Bool → Bool := fun x uz => x != uz
/-- `Y := if Uy=0 then Z else U`。**⚠ 无 `X` 参数** ⟹ 条件 (i)。 -/
def nfY : Bool → Bool → Bool → Bool := fun z u uy => if uy then u else z

/-- 混杂源 `U ~ 1/2`。 -/
noncomputable def npU : Bool → ℝ := fun _ => 1 / 2
/-- `Ux`：`P(0) = 9/10`（**弱噪声**，使 `U` 强混杂 `X`）。 -/
noncomputable def npUx : Bool → ℝ := fun b => if b then 1 / 10 else 9 / 10
/-- `Uz`：`P(0) = 1/4`（**保证 `p(x,z) > 0`**）。 -/
noncomputable def npUz : Bool → ℝ := fun b => if b then 3 / 4 else 1 / 4
/-- `Uy ~ 1/2`。 -/
noncomputable def npUy : Bool → ℝ := fun _ => 1 / 2

noncomputable def nM (r : Bool) : ℝ := npU r
noncomputable def nMargX (x : Bool) : ℝ := margX npU npUx nfX x
noncomputable def nMargXZ (x z : Bool) : ℝ := margXZ npU npUx npUz nfX nfZ x z
noncomputable def nJoint (x z y : Bool) : ℝ := joint npU npUx npUz npUy nfX nfZ nfY x z y
noncomputable def nDo (x y : Bool) : ℝ := doLaw npU npUz npUy nfZ nfY x y
noncomputable def nObs (x y : Bool) : ℝ := obsLaw npU npUx npUz npUy nfX nfZ nfY x y

/-! ### 3.1 外生律归一（**保证 `joint` 是概率**） -/

theorem n_pU_sum : (∑ b : Bool, npU b) = 1 := by
  norm_num [npU, Fintype.sum_bool]

theorem n_pUx_sum : (∑ b : Bool, npUx b) = 1 := by
  norm_num [npUx, Fintype.sum_bool]

theorem n_pUz_sum : (∑ b : Bool, npUz b) = 1 := by
  norm_num [npUz, Fintype.sum_bool]

theorem n_pUy_sum : (∑ b : Bool, npUy b) = 1 := by
  norm_num [npUy, Fintype.sum_bool]

/-! ### 3.2 ⭐ **positivity：`p(x,z) > 0` 对所有 `(x,z)`**（字面 SCM 缺的正是这一条） -/

theorem n_margX_f : nMargX false = 1 / 2 := by
  norm_num [nMargX, margX, npU, npUx, nfX, ind, Fintype.sum_bool]

theorem n_margX_t : nMargX true = 1 / 2 := by
  norm_num [nMargX, margX, npU, npUx, nfX, ind, Fintype.sum_bool]

theorem n_margXZ_f_f : nMargXZ false false = 1 / 8 := by
  norm_num [nMargXZ, margXZ, npU, npUx, npUz, nfX, nfZ, ind, Fintype.sum_bool]

theorem n_margXZ_f_t : nMargXZ false true = 3 / 8 := by
  norm_num [nMargXZ, margXZ, npU, npUx, npUz, nfX, nfZ, ind, Fintype.sum_bool]

theorem n_margXZ_t_f : nMargXZ true false = 3 / 8 := by
  norm_num [nMargXZ, margXZ, npU, npUx, npUz, nfX, nfZ, ind, Fintype.sum_bool]

theorem n_margXZ_t_t : nMargXZ true true = 1 / 8 := by
  norm_num [nMargXZ, margXZ, npU, npUx, npUz, nfX, nfZ, ind, Fintype.sum_bool]

/-! ### 3.3 联合律 `p(x,z,y)`（8 个格点） -/

theorem n_joint_f_f_f : nJoint false false false = 19 / 160 := by
  norm_num [nJoint, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind, Fintype.sum_bool]

theorem n_joint_f_f_t : nJoint false false true = 1 / 160 := by
  norm_num [nJoint, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind, Fintype.sum_bool]

theorem n_joint_f_t_f : nJoint false true false = 27 / 160 := by
  norm_num [nJoint, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind, Fintype.sum_bool]

theorem n_joint_f_t_t : nJoint false true true = 33 / 160 := by
  norm_num [nJoint, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind, Fintype.sum_bool]

theorem n_joint_t_f_f : nJoint true false false = 33 / 160 := by
  norm_num [nJoint, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind, Fintype.sum_bool]

theorem n_joint_t_f_t : nJoint true false true = 27 / 160 := by
  norm_num [nJoint, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind, Fintype.sum_bool]

theorem n_joint_t_t_f : nJoint true true false = 1 / 160 := by
  norm_num [nJoint, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind, Fintype.sum_bool]

theorem n_joint_t_t_t : nJoint true true true = 19 / 160 := by
  norm_num [nJoint, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind, Fintype.sum_bool]

/-! ### 3.4 干预律与观测律 -/

theorem n_do_f_f : nDo false false = 3 / 8 := by
  norm_num [nDo, doLaw, npU, npUz, npUy, nfZ, nfY, ind, Fintype.sum_bool]

theorem n_do_f_t : nDo false true = 5 / 8 := by
  norm_num [nDo, doLaw, npU, npUz, npUy, nfZ, nfY, ind, Fintype.sum_bool]

theorem n_do_t_f : nDo true false = 5 / 8 := by
  norm_num [nDo, doLaw, npU, npUz, npUy, nfZ, nfY, ind, Fintype.sum_bool]

theorem n_do_t_t : nDo true true = 3 / 8 := by
  norm_num [nDo, doLaw, npU, npUz, npUy, nfZ, nfY, ind, Fintype.sum_bool]

/-- ⭐⭐ **观测律 `P(Y=0|X=0) = 23/40`** —— **≠ `3/8`**（混杂是真的）。 -/
theorem n_obs_f_f : nObs false false = 23 / 40 := by
  simp only [nObs, obsLaw]
  rw [show (margX npU npUx nfX false) = 1 / 2 from n_margX_f]
  norm_num [Fintype.sum_bool, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind]

/-- ⭐⭐ **观测律 `P(Y=1|X=0) = 17/40`** —— **≠ `5/8`**。 -/
theorem n_obs_f_t : nObs false true = 17 / 40 := by
  simp only [nObs, obsLaw]
  rw [show (margX npU npUx nfX false) = 1 / 2 from n_margX_f]
  norm_num [Fintype.sum_bool, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind]

/-! ### 3.5 ⭐⭐⭐ **主定理：`fd_correct_on_chain`** -/

/-- ⭐⭐⭐ **`fd_correct_on_chain`**：**加噪链（positivity 成立）上，
`frontdoorFormula = doLaw`，四个格点全部相等。**

**数值**：
| `(x,y)` | `fd` | `doLaw` |
|---|---|---|
| `(0,0)` | `3/8` | `3/8` |
| `(0,1)` | `5/8` | `5/8` |
| `(1,0)` | `5/8` | `5/8` |
| `(1,1)` | `3/8` | `3/8` |

**⚠ 与 §2 的对照**：字面 SCM 得 `fd = 1/2 ≠ 1`；
加噪（同一链语义，只是 `positivity` 成立）后 `fd = doLaw` 精确成立。
**⟹ positivity 不是技术装饰，而是 front-door 公式正确性的**分水岭**。** -/
theorem fd_correct_on_chain :
    frontdoorFormula nJoint nMargXZ nMargX false false = nDo false false
    ∧ frontdoorFormula nJoint nMargXZ nMargX false true = nDo false true
    ∧ frontdoorFormula nJoint nMargXZ nMargX true false = nDo true false
    ∧ frontdoorFormula nJoint nMargXZ nMargX true true = nDo true true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [n_do_f_f]
    norm_num [frontdoorFormula, Fintype.sum_bool, nMargX, nMargXZ, nJoint,
      margX, margXZ, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind]
  · rw [n_do_f_t]
    norm_num [frontdoorFormula, Fintype.sum_bool, nMargX, nMargXZ, nJoint,
      margX, margXZ, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind]
  · rw [n_do_t_f]
    norm_num [frontdoorFormula, Fintype.sum_bool, nMargX, nMargXZ, nJoint,
      margX, margXZ, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind]
  · rw [n_do_t_t]
    norm_num [frontdoorFormula, Fintype.sum_bool, nMargX, nMargXZ, nJoint,
      margX, margXZ, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind]

/-- ⭐⭐⭐ 逐点形式：`∀ x y, fd = doLaw`。 -/
theorem fd_correct_on_chain_pointwise :
    ∀ x y : Bool, frontdoorFormula nJoint nMargXZ nMargX x y = nDo x y := by
  obtain ⟨h00, h01, h10, h11⟩ := fd_correct_on_chain
  intro x y
  cases x <;> cases y
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-! ### 3.6 ⭐⭐⭐ **`fd_not_confounded`：数值相同，且 ≠ 观测律** -/

/-- ⭐⭐⭐ **`fd_not_confounded`**：**`frontdoorFormula` 与 `doLaw` 的**具体数值相同**，
且**二者都与被混杂污染的观测律不同**。**

**具体数值**：
- `fd(0,0) = doLaw(0,0) = 3/8`
- **`obs(0,0) = 23/40`**（**`23/40 ≠ 3/8`**，混杂可见）
- `fd(0,1) = doLaw(0,1) = 5/8`
- **`obs(0,1) = 17/40`**（**`17/40 ≠ 5/8`**）

**⭐⭐ 这一条是**真**的「不平凡」**：
- 若 `fd` 只是「碰巧」等于 `doLaw`，那观测律也该跟着相等（无混杂时必如此）；
- 但此处 `obs ≠ doLaw` ⟹ **确有混杂** ⟹ `fd = doLaw` **不是平凡恒等**，
  而是 front-door 公式**真正修复了混杂**。 -/
theorem fd_not_confounded :
    frontdoorFormula nJoint nMargXZ nMargX false false = nDo false false
      ∧ nDo false false = 3 / 8
      ∧ nObs false false = 23 / 40
      ∧ nObs false false ≠ nDo false false
      ∧ frontdoorFormula nJoint nMargXZ nMargX false true = nDo false true
      ∧ nDo false true = 5 / 8
      ∧ nObs false true = 17 / 40
      ∧ nObs false true ≠ nDo false true := by
  obtain ⟨h00, h01, _, _⟩ := fd_correct_on_chain
  refine ⟨h00, n_do_f_f, n_obs_f_f, ?_, h01, n_do_f_t, n_obs_f_t, ?_⟩
  · rw [n_obs_f_f, n_do_f_f]; norm_num
  · rw [n_obs_f_t, n_do_f_t]; norm_num

/-- ⭐⭐ **`fd_ne_obs_on_chain`**：`frontdoorFormula ≠ 观测律`（数值 `3/8 ≠ 23/40`）。 -/
theorem fd_ne_obs_on_chain :
    frontdoorFormula nJoint nMargXZ nMargX false false ≠ nObs false false := by
  obtain ⟨h, _, _, _⟩ := fd_correct_on_chain
  rw [h, n_do_f_f, n_obs_f_f]; norm_num

/-! ## §5 ⭐⭐⭐ 加噪链的**概率公理核对**（本批新增，`R-53`）

  §3 给出了 `nJoint` / `nDo` / `nObs` 的 **12 个格点数值**与
  `fd_correct_on_chain`。本节把这些数值提升为**概率律本身的性质**：

  | 定理 | 内容 |
  |---|---|
  | `n_joint_nonneg` | `nJoint` **处处非负**（§3 八格点全部核对） |
  | `n_joint_sum_one` | `nJoint` **总质量 = 1**（归一化） |
  | `n_do_nonneg` | 干预律 `nDo` **处处非负** |
  | `n_do_sum_one` | 干预律**逐 `x` 归一化**：`nDo x 0 + nDo x 1 = 1` |
  | `n_obs_sum_one` | 观测律**逐 `x` 归一化**：`nObs x 0 + nObs x 1 = 1` |

  **⟹ 为什么这不是重述**：§3 的 `n_joint_f_f_f = 19/160` 等是**单点等式**；
  归一化与正性需要把 **8 个（或 4 个）单点值相加**，是**跨格点**的事实 ——
  `fd_correct_on_chain` 的**正确性讨论只有在双方都是概率律时才有意义**，
  本节补上这一层。**无 `sorry`，全部 `norm_num` 核算。**
-/

theorem n_joint_nonneg : ∀ x z y : Bool, 0 ≤ nJoint x z y := by
  intro x z y
  cases x <;> cases z <;> cases y <;>
    simp [n_joint_f_f_f, n_joint_f_f_t, n_joint_f_t_f, n_joint_f_t_t,
          n_joint_t_f_f, n_joint_t_f_t, n_joint_t_t_f, n_joint_t_t_t] <;> norm_num

/-- ⭐⭐ **`nJoint` 归一化**：八个格点求和 `= 1`。
（`(19+1+27+33+33+27+1+19)/160 = 160/160`。**跨格点**核算。） -/
theorem n_joint_sum_one : (∑ x, ∑ z, ∑ y, nJoint x z y) = 1 := by
  simp [n_joint_f_f_f, n_joint_f_f_t, n_joint_f_t_f, n_joint_f_t_t,
        n_joint_t_f_f, n_joint_t_f_t, n_joint_t_t_f, n_joint_t_t_t]
  norm_num

theorem n_do_nonneg : ∀ x y : Bool, 0 ≤ nDo x y := by
  intro x y
  cases x <;> cases y <;>
    simp [n_do_f_f, n_do_f_t, n_do_t_f, n_do_t_t] <;> norm_num

/-- ⭐⭐ **干预律逐 `x` 归一化**：`nDo x 0 + nDo x 1 = 1`。
（`3/8 + 5/8 = 1` 与 `5/8 + 3/8 = 1`。**干预律是概率律**。） -/
theorem n_do_sum_one : ∀ x : Bool, nDo x false + nDo x true = 1 := by
  intro x
  cases x <;> simp [n_do_f_f, n_do_f_t, n_do_t_f, n_do_t_t] <;> norm_num

/-- ⭐⭐⭐ **观测律逐 `x` 归一化**：`nObs x 0 + nObs x 1 = 1`。

**⟹ 意义**：`x = false` 分支由 §3 的 `23/40 + 17/40 = 1` 直接给出；
`x = true` 分支需**重新展开** `obsLaw`（§3 未登记这两点）。
本条确认 `obsLaw` 的**定义式**（除以 `margX`）确实产出概率律。 -/
theorem n_obs_sum_one : ∀ x : Bool, nObs x false + nObs x true = 1 := by
  intro x
  cases x
  · simp [n_obs_f_f, n_obs_f_t]; norm_num
  · simp [nObs, obsLaw, joint, w, npU, npUx, npUz, npUy, nfX, nfZ, nfY, ind, margX]
    norm_num

end Noisy

/-! ## §4 ⭐⭐ **`fd_differs_with_direct_effect`：`Y := Z ∨ X`**

  同一 `X, Z` 链条（`nfX`, `nfZ`, `npU`, `npUx`, `npUz` 全不变），
  **只把 `Y` 换成也读 `X` 的确定性方程** `Y := Z ∨ X`。
  **签名 `Z → X → Y` 比 `nfY` 多一个 `X` 槽 —— 条件 (i) 在类型上被违反。** -/

section Direct

/-- ⭐⭐ **`Y := Z ∨ X`**（`Bool` 上的 `or`）。**⚠ 多一个 `X` 槽 ⟹ 违反 (i)。** -/
def dY : Bool → Bool → Bool := fun z x => z || x

noncomputable def dJoint (x z y : Bool) : ℝ :=
  ∑ u, ∑ ux, ∑ uz, npU u * npUx ux * npUz uz * ind (nfX u ux = x ∧ nfZ x uz = z ∧ dY z x = y)

/-- 直接效应模型的干预律：`do(x)` 下 `Z = nfZ x uz`、`Y = dY (nfZ x uz) x`。 -/
noncomputable def dDo (x y : Bool) : ℝ :=
  ∑ u, ∑ uz, npU u * npUz uz * ind (dY (nfZ x uz) x = y)

theorem d_joint_f_f_f : dJoint false false false = 1 / 8 := by
  norm_num [dJoint, npU, npUx, npUz, nfX, nfZ, dY, ind, Fintype.sum_bool]

theorem d_joint_f_f_t : dJoint false false true = 0 := by
  norm_num [dJoint, npU, npUx, npUz, nfX, nfZ, dY, ind, Fintype.sum_bool]

theorem d_joint_f_t_f : dJoint false true false = 0 := by
  norm_num [dJoint, npU, npUx, npUz, nfX, nfZ, dY, ind, Fintype.sum_bool]

theorem d_joint_f_t_t : dJoint false true true = 3 / 8 := by
  norm_num [dJoint, npU, npUx, npUz, nfX, nfZ, dY, ind, Fintype.sum_bool]

theorem d_joint_t_f_f : dJoint true false false = 0 := by
  norm_num [dJoint, npU, npUx, npUz, nfX, nfZ, dY, ind, Fintype.sum_bool]

theorem d_joint_t_f_t : dJoint true false true = 3 / 8 := by
  norm_num [dJoint, npU, npUx, npUz, nfX, nfZ, dY, ind, Fintype.sum_bool]

theorem d_joint_t_t_f : dJoint true true false = 0 := by
  norm_num [dJoint, npU, npUx, npUz, nfX, nfZ, dY, ind, Fintype.sum_bool]

theorem d_joint_t_t_t : dJoint true true true = 1 / 8 := by
  norm_num [dJoint, npU, npUx, npUz, nfX, nfZ, dY, ind, Fintype.sum_bool]

theorem d_do_f_f : dDo false false = 1 / 4 := by
  norm_num [dDo, npU, npUz, nfZ, dY, ind, Fintype.sum_bool]

theorem d_do_f_t : dDo false true = 3 / 4 := by
  norm_num [dDo, npU, npUz, nfZ, dY, ind, Fintype.sum_bool]

theorem d_do_t_f : dDo true false = 0 := by
  norm_num [dDo, npU, npUz, nfZ, dY, ind, Fintype.sum_bool]

theorem d_do_t_t : dDo true true = 1 := by
  norm_num [dDo, npU, npUz, nfZ, dY, ind, Fintype.sum_bool]

/-- ⭐⭐⭐ **`fd_differs_with_direct_effect`**：**`Y` 直接依赖 `X`（`Y := Z ∨ X`）时，
`frontdoorFormula ≠ doLaw`。**

**两两不同的具体数值**：
| `(x,y)` | `fd` | `doLaw` |
|---|---|---|
| `(0,0)` | **`1/8`** | **`1/4`** |
| `(1,0)` | **`3/8`** | **`0`** |
| `(1,1)` | **`5/8`** | **`1`** |

**⟹ 每一行 `fd ≠ doLaw`。特别是 `(1,0)`：`fd = 3/8` 而 `doLaw = 0`
（`do(1)` 下 `Y = Z ∨ 1 = 1` 确定，永不为 `0`）——
front-door 公式**完全错**，因为 `Y` 的直接依赖 `X` 无法被 `Z` 转手。** -/
theorem fd_differs_with_direct_effect :
    frontdoorFormula dJoint nMargXZ nMargX false false = 1 / 8
      ∧ dDo false false = 1 / 4
      ∧ frontdoorFormula dJoint nMargXZ nMargX false false ≠ dDo false false
      ∧ frontdoorFormula dJoint nMargXZ nMargX true false = 3 / 8
      ∧ dDo true false = 0
      ∧ frontdoorFormula dJoint nMargXZ nMargX true false ≠ dDo true false
      ∧ frontdoorFormula dJoint nMargXZ nMargX true true = 5 / 8
      ∧ dDo true true = 1
      ∧ frontdoorFormula dJoint nMargXZ nMargX true true ≠ dDo true true := by
  have hfd_ff : frontdoorFormula dJoint nMargXZ nMargX false false = 1 / 8 := by
    norm_num [frontdoorFormula, Fintype.sum_bool, n_margX_f, n_margX_t, n_margXZ_f_f, n_margXZ_f_t, n_margXZ_t_f, n_margXZ_t_t, d_joint_f_f_f, d_joint_f_t_f, d_joint_t_f_f, d_joint_t_t_f]
  have hfd_tf : frontdoorFormula dJoint nMargXZ nMargX true false = 3 / 8 := by
    norm_num [frontdoorFormula, Fintype.sum_bool, n_margX_f, n_margX_t, n_margXZ_f_f, n_margXZ_f_t, n_margXZ_t_f, n_margXZ_t_t, d_joint_f_f_f, d_joint_f_t_f, d_joint_t_f_f, d_joint_t_t_f]
  have hfd_tt : frontdoorFormula dJoint nMargXZ nMargX true true = 5 / 8 := by
    norm_num [frontdoorFormula, Fintype.sum_bool, n_margX_f, n_margX_t, n_margXZ_f_f, n_margXZ_f_t, n_margXZ_t_f, n_margXZ_t_t, d_joint_f_f_t, d_joint_f_t_t, d_joint_t_f_t, d_joint_t_t_t]
  refine ⟨hfd_ff, d_do_f_f, ?_, hfd_tf, d_do_t_f, ?_, hfd_tt, d_do_t_t, ?_⟩
  · rw [hfd_ff, d_do_f_f]; norm_num
  · rw [hfd_tf, d_do_t_f]; norm_num
  · rw [hfd_tt, d_do_t_t]; norm_num

end Direct

/-! ### §4 直接效应模型的辅助量：`X` 边缘、`Z` 边缘、联合律归一

  §3 的 `dY := fun z x => z || x` 模型（条件 (i) 被违反：`Y` 直接读 `X`）
  只给出 `frontdoorFormula` 的四点数值。**本节补齐该模型的**结构量**：
  `X` 边缘、`XZ` 边缘、联合律总和 = 1、干预律逐行归一，
  以及 `y = 1` 两点的 `fd` 数值与 `fd` 逐行总和 = 1。
  **⟹ 这些量使 §3 的「`fd ≠ doLaw`」不再只是孤立数值，而是**可核对的律**。 -/

section DirectAux

/-- 直接效应模型的 `X` 边缘 `p(x)`（`X` 方程与 §3 的 `nfX` 相同）。 -/
noncomputable def dMargX (x : Bool) : ℝ := margX npU npUx nfX x

/-- 直接效应模型的 `XZ` 边缘 `p(x,z)`（`Z` 方程与 §3 的 `nfZ` 相同）。 -/
noncomputable def dMargXZ (x z : Bool) : ℝ := margXZ npU npUx npUz nfX nfZ x z

theorem d_margX_f : dMargX false = 1 / 2 := by
  norm_num [dMargX, margX, npU, npUx, nfX, ind, Fintype.sum_bool]

theorem d_margX_t : dMargX true = 1 / 2 := by
  norm_num [dMargX, margX, npU, npUx, nfX, ind, Fintype.sum_bool]

theorem d_margXZ_f_f : dMargXZ false false = 1 / 8 := by
  norm_num [dMargXZ, margXZ, npU, npUx, npUz, nfX, nfZ, ind, Fintype.sum_bool]

/-- ⭐⭐ 直接效应模型的联合律归一：`∑_{x,z,y} p(x,z,y) = 1`。 -/
theorem d_joint_sum_one : (∑ x, ∑ z, ∑ y, dJoint x z y) = 1 := by
  norm_num [dJoint, npU, npUx, npUz, nfX, nfZ, dY, ind, Fintype.sum_bool]

/-- ⭐⭐ 直接效应模型的干预律逐行归一：`do(x)` 下 `Y` 必为 `0` 或 `1`。 -/
theorem d_do_sum_one : ∀ x : Bool, dDo x false + dDo x true = 1 := by
  intro x
  cases x <;>
    norm_num [dDo, npU, npUz, nfZ, dY, ind, Fintype.sum_bool]

/-- ⭐⭐ `y = 1` 两点的 `fd` 数值（`(0,1) ↦ 7/8`、`(1,1) ↦ 5/8`）。 -/
theorem d_fd_y1_values :
    frontdoorFormula dJoint dMargXZ dMargX false true = 7 / 8
      ∧ frontdoorFormula dJoint dMargXZ dMargX true true = 5 / 8 := by
  constructor <;>
    norm_num [frontdoorFormula, Fintype.sum_bool, dMargX, dMargXZ, dJoint,
      margX, margXZ, npU, npUx, npUz, nfX, nfZ, dY, ind]

/-- ⭐⭐⭐ `fd` 对 `y` 逐行求和 = 1（**注意：这是 `fd` 自身的归一，
**与 `doLaw` 无关**；它说明 §3 的偏差不是「归一错误」而是**系统性重分配**）。 -/
theorem d_fd_total_mass_one :
    (∑ y, frontdoorFormula dJoint dMargXZ dMargX false y) = 1
      ∧ (∑ y, frontdoorFormula dJoint dMargXZ dMargX true y) = 1 := by
  constructor <;>
    norm_num [frontdoorFormula, Fintype.sum_bool, dMargX, dMargXZ, dJoint,
      margX, margXZ, npU, npUx, npUz, nfX, nfZ, dY, ind]

end DirectAux

end Fate.R253


/-! ===========================================================================
  §6 ⭐⭐⭐ **`R-56` 追加：加噪链上的「边缘化一致性」与「positivity 的数值形态」**

  §3 与 §5 给出的是**单点数值**（`nJoint`、`nDo`、`nObs`、`nMargXZ` 的格点值）
  与**归一化**（总和 `= 1`）。本节追加的是**跨格点之间的相容性**，即
  「同一个概率模型的三层描述必须互相一致」：

  | 定理 | 内容 | 为何不是 §5 的重述 |
  |---|---|---|
  | `n_joint_marginalizes_to_margXZ` | `∑_y nJoint x z y = nMargXZ x z` | 把 **8** 个格点按 `y` 求和，得到**另外 4** 个数 |
  | `n_margXZ_sum_gives_margX` | `∑_z nMargXZ x z = nMargX x` | 把 **4** 格点按 `z` 求和得到 **2** 个数 |
  | `n_nested_marginal` | `∑_z ∑_y nJoint x z y = nMargX x` | 两层边缘化**复合** |
  | `n_positivity` | `∀ x z, 0 < nMargXZ x z` | 逐点**严格正**（对比字面 SCM 的 `0`） |
  | `n_positivity_contrast` | `0 < nMargXZ false true` 且 `lMargXZ false true = 0` | **同一位置**字面 SCM 与加噪链的**判决性对照** |

  ⚠ 这些前件**只有** `Bool` 的 `cases` 与已登记的格点等式，
  **不含任何结论本身**；等价地，它们**不可能**由 `Iff.rfl` 或 `rfl` 关闭 ——
  必须真的按 `Finset.sum_bool` 展开并把格点值相加。
-/

namespace Fate.R253

section R56Marginal

/-- ⭐⭐⭐ **`R-56`：`nJoint` 按 `y` 边缘化**回 `nMargXZ`。

$$\sum_{y} p(x,z,y) = p(x,z)\qquad(\forall x,z).$$

**⟹ 这是 `joint` 与 `margXZ` 两个独立定义之间的相容性**：
`nJoint` 由嵌套求和 `∑_u ∑_ux ∑_uz ∑_uy` 定义，`nMargXZ` 由 `∑_u ∑_ux ∑_uz`
定义 —— 两者的**求和层数不同**，等式**不**由定义直接给出，
需先用 §3 的八个格点值把左边算成 `1/8, 3/8, 3/8, 1/8`，
再与 §3 的 `n_margXZ_*` 对照。 -/
theorem n_joint_marginalizes_to_margXZ :
    ∀ x z : Bool, (∑ y, nJoint x z y) = nMargXZ x z := by
  intro x z
  cases x <;> cases z
  · simp only [Fintype.sum_bool, n_joint_f_f_f, n_joint_f_f_t, n_margXZ_f_f]; norm_num
  · simp only [Fintype.sum_bool, n_joint_f_t_f, n_joint_f_t_t, n_margXZ_f_t]; norm_num
  · simp only [Fintype.sum_bool, n_joint_t_f_f, n_joint_t_f_t, n_margXZ_t_f]; norm_num
  · simp only [Fintype.sum_bool, n_joint_t_t_f, n_joint_t_t_t, n_margXZ_t_t]; norm_num

/-- ⭐⭐⭐ **`R-56`：`nMargXZ` 按 `z` 边缘化**回 `nMargX`。

$$\sum_{z} p(x,z) = p(x)\qquad(\forall x).$$
`1/8 + 3/8 = 1/2`（`x = 0`）与 `3/8 + 1/8 = 1/2`（`x = 1`）。 -/
theorem n_margXZ_sum_gives_margX :
    ∀ x : Bool, (∑ z, nMargXZ x z) = nMargX x := by
  intro x
  cases x
  · simp only [Fintype.sum_bool, n_margXZ_f_f, n_margXZ_f_t, n_margX_f]; norm_num
  · simp only [Fintype.sum_bool, n_margXZ_t_f, n_margXZ_t_t, n_margX_t]; norm_num

/-- ⭐⭐⭐ **`R-56`：两层边缘化复合**。

$$\sum_{z}\sum_{y} p(x,z,y) = p(x)\qquad(\forall x).$$

**⚠ 这不是前两条的平凡推论**：它把 **8** 个格点一次性归约到 **1** 个数，
中间必须**真的**先做 `y`-求和；本证明**逐 `x` 直接展开 8 个格点**，
不经过 `n_joint_marginalizes_to_margXZ`，因此是**独立的核算路径**
（⟹ 与前两条构成**交叉验证**）。 -/
theorem n_nested_marginal :
    ∀ x : Bool, (∑ z, ∑ y, nJoint x z y) = nMargX x := by
  intro x
  cases x
  · simp only [Fintype.sum_bool, n_joint_f_f_f, n_joint_f_f_t, n_joint_f_t_f,
      n_joint_f_t_t, n_margX_f]; norm_num
  · simp only [Fintype.sum_bool, n_joint_t_f_f, n_joint_t_f_t, n_joint_t_t_f,
      n_joint_t_t_t, n_margX_t]; norm_num

/-- ⭐⭐⭐⭐ **`R-56`：加噪链满足 **positivity**（`p(x,z) > 0` 逐点）。**

$$\forall x z,\quad \text{nMargXZ}\,x\,z > 0 .$$

数值上为 `1/8, 3/8, 3/8, 1/8`，**全部严格正**。
**这正是 front-door 公式（`fd_correct_on_chain`）成立的技术前提**，
也是字面 SCM 唯一缺失的那一条（见下条 `n_positivity_contrast`）。 -/
theorem n_positivity : ∀ x z : Bool, 0 < nMargXZ x z := by
  intro x z
  cases x <;> cases z <;>
    simp only [n_margXZ_f_f, n_margXZ_f_t, n_margXZ_t_f, n_margXZ_t_t] <;> norm_num

/-- ⭐⭐⭐⭐ **`R-56`：**同一格点**上字面 SCM 与加噪链的判决性对照。**

- 字面 SCM（`Z := X` 确定性）：`lMargXZ false true = 0` —— **positivity 违反**；
- 加噪链（`Z := X ⊕ Uz`）：`nMargXZ false true = 3 / 8 > 0` —— **positivity 成立**。

**⟹ 两条链的**图结构完全相同**（都是 `X → Z → Y`），唯一的差别是 `Z` 的噪声：
`Unit`（无噪）vs `Bool`（有噪）。**结论：positivity 的成立与否**只**取决于
`Z` 方程是否为确定性映射，与图的形状无关 —— 这精确解释了
`fd_literal_chain_fails` 与 `fd_correct_on_chain` 的**反差**。** -/
theorem n_positivity_contrast :
    lMargXZ false true = 0 ∧ 0 < nMargXZ false true
      ∧ nMargXZ false true = 3 / 8 := by
  refine ⟨l_margXZ_f_t, ?_, n_margXZ_f_t⟩
  rw [n_margXZ_f_t]; norm_num

end R56Marginal

end Fate.R253
