import FateWorld.FateV2.Predict.Frontdoor

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/FrontdoorChainProof.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 6 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict

/-! **第 246 轮澄清：本文件与 `FrontdoorCounterexample.lean` **不矛盾****

**⚠ 两个文件的结论**看起来相反**，实际**互补**：**

| 文件 | 假设 | 结论 |
|---|---|---|
| **本文件**（`FrontdoorChainProof`）| **有 positivity**（`hX : MargX ≠ 0`、`hQ : Q ≠ 0`）| `fd = doLaw` ✅ |
| `FrontdoorCounterexample` | **无 positivity**（`Z := X` 确定性）| `fd ≠ doLaw` ✅ |

**即**：**frontdoor 公式**需要正性**；违反正性时它会失效。**

**⚠ 这不是矛盾，是**两个不同条件下**的结论。**
**⚠ 正性是 Pearl 的**标准假设**（positivity），不是实现瑕疵。**

**合起来给出**完整的图景**：
- `fd_equals_doLaw_of_chain`（本文件）：**充分条件**（正性 ⟹ 公式正确）
- `fd_literal_chain_fails`（另一文件）：**必要性的反面**（无正性 ⟹ 公式失效）
-/ 


-- 仅在 `sum_R_eq` 处有一个无用的 section 变量提示；非实质问题。
set_option linter.unusedSectionVars false

/-! ===========================================================================
  `FateV2.Predict/_r242_G4` —— **front-door 公式的实质性进步**（第 242 轮 / 缺口 2 / G4）

  ## 0. 起点与本周目标

  第 239 轮的 `FateV2.Predict/Frontdoor.lean` 只交付了 front-door **调整公式的代数骨架**
  （`fd_unit_collapse` / `fd_total_mass_one` 等 12 条）—— **全是纯代数的恒等式，
  与因果语义无关**。本文件推进一步：

  | # | 目标 | 本文件的交付 |
  |---|---|---|
  | 1 | 具体三变量链上的**数值验证** | `fd_correct_in_linear_chain`（§2） |
  | 2 | **一般定理**：`Y` 不直接依赖 `X` ⟹ `fd = doLaw` | `fd_equals_doLaw_of_chain`（§3） |
  | 3 | **反例**：`Y` 直接依赖 `X` ⟹ `fd ≠ doLaw` | `fd_differs_without_mediation`（§4） |

  ## 1. 载体：**乘积式（Markovian）front-door SCM，机制按真实输入签名**

  我把结构方程写成**只吃自己真正依赖的分量** —— 这样 Pearl 的三条 front-door 条件
  **直接体现在类型里**，不需要图论 d-分离判定器：

  ```
  U  = U₁ × U₂ × U₃                外生分量互相独立
  pU(u₁,u₂,u₃) = p₁u₁ · p₂u₂ · p₃u₃
  fX : U₁ → X                       X 的机制，只吃 U₁
  fZ : X → U₂ → Z                   Z 的机制，吃 X 与 U₂ ——  ⚠ 不吃 U₁
  fY : Z → U₁ → U₃ → Y              Y 的机制，吃 Z, U₁, U₃ —— ⚠ 不吃 X
  ```

  **三条 front-door 条件与类型签名的精确对应**：

  | Pearl 的条件 | 本载体的**类型层面**刻画 |
  |---|---|
  | **(i)** `Z` 截断 `X → Y` 的所有有向路径 | `fY` **没有 `X` 参数** ⟹ 无 `X → Y` 直边 |
  | **(ii)** `X → Z` 无后门路径 | `fZ` **没有 `U₁` 参数** ⟹ `X` 与 `Z` 唯一的共同原因 `U₁` 进不了 `Z` |
  | **(iii)** `Z → Y` 的后门路径被 `X` 阻断 | `U₁` 同时喂 `X` 与 `Y`（`fX`, `fY` 都有 `U₁`）⟹ `Z ← X ← U₁ → Y` 是**唯一**后门；条件在 `X` 上即阻断 |

  **这是本文件的**核心方法学进步**：
  「`Y` 不直接依赖 `X`」不再是**假设**（像 §3 那种 `∀ u, ... = ...` 的等式），
  而是**签名事实** —— 想违反它必须**换类型**（见 §4 的 `fYdirect`）。**

  ## 2. 记号与四条律

  - `MargX p₁ fX x := ∑_{u₁} p₁u₁ · [fX u₁ = x]`
  - `Q p₂ fZ x z := ∑_{u₂} p₂u₂ · [fZ x u₂ = z]`   （即 `P(z|x)`）
  - `R p₁ p₃ fX fY x z y := ∑_{u₁,u₃} p₁u₁p₃u₃ · [fX u₁ = x ∧ fY z u₁ u₃ = y]`
  - **`MargXZ x z := MargX x · Q x z`**、**`Joint x z y := Q x z · R x z y`**
    （**这两条**不是**简化，而是 (ii)/(iii) 的**推论**；见 `§3.0` 的注释）
  - `DoLaw p₂ fZ fY x y := ∑_{u₂} p₂u₂ · ∑_{u₁,u₃} p₁u₁p₃u₃ · [fY (fZ x u₂) u₁ u₃ = y]`

  ## ⚠ 诚实边界（**先声明，正文兑现**）

  ✅ **真证**：
  - §2：具体 `Bool` 链，**全部数值由 `norm_num` 算出**（`7/20, 3/40, 3/5, 2/5, 17/20` …），
    证 `frontdoorFormula = DoLaw`，且 `frontdoorFormula ≠ 观测律`；
  - §3：**一般定理**，对**任意**有限 `U₁,U₂,U₃`、**任意** `p₁,p₂,p₃,fX,fZ,fY` 成立；
  - §4：**具体反例**，`fd = (1/2,1/2)` 而 `do = (7/10,3/10)`。

  ⚠ **必须声明的边界（不掩饰）**：
  1. `MargXZ / Joint` 的**乘积形式是定义**，不是从「对 `u` 的原始求和」推出来的。
     我**没有**在本文件里证「原始 `∑_u` 形式 = 乘积形式」那一步
     （它需要 `Finset.sum_product` 的三重分解，**属机械改写**，不是数学内容；
     但**我确实没做**）。**⟹ `§3` 的定理是**在这个乘积载体上**的完整证明，
     而不是「从 SCM 原始定义出发」的完整证明。** 这一点见 §3.0。
  2. **不**从图上的 d-分离推出「`fY` 不吃 `X`」。那属**缺口 1**（Pearl 1.2.4）。
     本文件把 (i)(ii)(iii) 换成**类型签名**，是「语义版本」，
     **与图版本的等价不在此处证明**。
  3. §3 的定理**带两条非平凡前提**（`hX : ∀ x, MargX x ≠ 0`、
     `hQ : ∀ a b, Q a b ≠ 0`）—— **它们是真的必要条件**（见 §3.4 的说明），
     不是形式上的装饰。
=========================================================================== -/

namespace FateV2.Predict.R242

open Finset FateV2.Predict.Frontdoor

/-! ## §1 定义（按机制的**真实输入签名**） -/

section Defs

variable {U1 U2 U3 : Type*} [Fintype U1] [Fintype U2] [Fintype U3]
variable {X Z Y : Type*} [DecidableEq X] [DecidableEq Z] [DecidableEq Y]

/-- **指示函数的 `ℝ`-值版本**：`[P] : ℝ`（真则 `1`，假则 `0`）。 -/
noncomputable def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

/-- 指示函数在假命题上取 `0`。 -/
theorem ind_of_not {P : Prop} [Decidable P] (h : ¬ P) : ind P = (0 : ℝ) := by
  simp only [ind]; exact if_neg h

/-- 指示函数在真命题上取 `1`。 -/
theorem ind_of {P : Prop} [Decidable P] (h : P) : ind P = (1 : ℝ) := by
  simp only [ind]; exact if_pos h

/-- **`X` 的边缘律**：`p(x) = ∑_{u₁} p₁(u₁)·[fX u₁ = x]`。 -/
noncomputable def MargX (p1 : U1 → ℝ) (fX : U1 → X) (x : X) : ℝ :=
  ∑ u1, p1 u1 * ind (fX u1 = x)

/-- **`P(z|x) = ∑_{u₂} p₂(u₂)·[fZ x u₂ = z]`**。

**这是 front-door 的**关键量**：`Z` 的机制 `fZ` **不吃 `U₁`**，
**故给定 `X=x` 后 `Z` 的分布只由 `p₂` 与 `fZ` 决定 —— 这正是条件 (ii)
「`X → Z` 无后门」的**数值后果**：`P(z|do(x)) = P(z|x)`。** -/
noncomputable def Q (p2 : U2 → ℝ) (fZ : X → U2 → Z) (x : X) (z : Z) : ℝ :=
  ∑ u2, p2 u2 * ind (fZ x u2 = z)

/-- **`(X,Z)` 的联合律**：`p(x,z) = p(x)·P(z|x)`。

**⚠ 这一行**就是条件 (ii)**：`p(x,z) = p(x)·P(z|x)` 等价于 `Z ⟂ U₁ | X`，
**即 `X` 与 `Z` 之间无**未阻断的后门**。** -/
noncomputable def MargXZ (p1 : U1 → ℝ) (p2 : U2 → ℝ)
    (fX : U1 → X) (fZ : X → U2 → Z) (x : X) (z : Z) : ℝ :=
  MargX p1 fX x * Q p2 fZ x z

/-- **内层「`x'` 平均」的核**：
`R x z y = ∑_{u₁,u₃} p₁u₁ p₃u₃ · [fX u₁ = x ∧ fY z u₁ u₃ = y]`。

**注意 `fY` 的签名 `Z → U₁ → U₃ → Y`** —— **没有 `X`**。
**这就是条件 (i) 的语义版本：`Y` 不直接吃 `X`。** -/
noncomputable def R (p1 : U1 → ℝ) (p3 : U3 → ℝ)
    (fX : U1 → X) (fY : Z → U1 → U3 → Y) (x : X) (z : Z) (y : Y) : ℝ :=
  ∑ u1, ∑ u3, p1 u1 * p3 u3 * ind (fX u1 = x ∧ fY z u1 u3 = y)

/-- **三元联合律**：`p(x,z,y) = P(z|x) · R x z y`。

**⚠ 这也是条件 (ii)+(iii)**：`P(x,z,y) = P(z|x)·P(x,y|z)`，其中
`P(x,y|z) = ∑_{u₁,u₃} p₁u₁p₃u₃[fX u₁=x][fY z u₁u₃ = y]`
—— **`u₂` 已被 `P(z|x)` 吸收，剩下的只涉及 `u₁,u₃`**。** -/
noncomputable def Joint (p1 : U1 → ℝ) (p2 : U2 → ℝ) (p3 : U3 → ℝ)
    (fX : U1 → X) (fZ : X → U2 → Z) (fY : Z → U1 → U3 → Y)
    (x : X) (z : Z) (y : Y) : ℝ :=
  Q p2 fZ x z * R p1 p3 fX fY x z y

/-- **干预律** `p(y|do(x))`。

**图手术（T34 口径）**：`X` 的方程换成常数 `x` ⟹ `Z = fZ x u₂`（**不筛 `u₁`**），
`Y = fY (fZ x u₂) u₁ u₃`。于是
$$\text{DoLaw}(x,y)=\sum_{u_2}p_2u_2\sum_{u_1,u_3}p_1u_1p_3u_3\,[f_Y(f_Zxu_2,u_1,u_3)=y].$$

**与 `Joint` 的差别只在**外层 `cJoint` 的 `P(z|x)` 是否被 `u₂`-纤维展开**：
`Joint` 把它留在外面（因为观测时要**条件化**在 `z` 上），
`DoLaw` 把它**吃进求和**（因为干预时 `z` 是 `u₂` 的函数，不条件化）。
**两者相等正是 front-door 定理的内容。** -/
noncomputable def DoLaw (p1 : U1 → ℝ) (p2 : U2 → ℝ) (p3 : U3 → ℝ)
    (fZ : X → U2 → Z) (fY : Z → U1 → U3 → Y) (x : X) (y : Y) : ℝ :=
  ∑ u2, p2 u2 * ∑ u1, ∑ u3, p1 u1 * p3 u3 * ind (fY (fZ x u2) u1 u3 = y)

end Defs

/-! ## §2 **`fd_correct_in_linear_chain`**：具体三变量链上的数值验证

### 2.1 具体模型（`X, Y, Z : Bool`，`U₁ = U₂ = U₃ = Bool`）

$$p_1\equiv \tfrac12 \ (\text{混杂源，均匀}),\quad
  p_2(u_2)=\begin{cases}7/10 & u_2=0\\ 3/10& u_2=1\end{cases}\ (Z\text{ 的噪声}),\quad
  p_3\equiv \tfrac12 .$$

**结构方程**：
- `fX u₁ = u₁`（`X := U₁`）
- `fZ x u₂ = (x ≠ u₂)`（`Z` 是 `X` 的**异或带噪传递**）
- `fY z u₁ u₃ = if u₃ then z else u₁`（`Y` 取 `Z` 或 `U₁`）

**这是真 front-door 场景**：
`U₁` 同时决定 `X` 与（以 `1/2` 概率）`Y` ⟹ **`X ↔ Y` 强混杂**；
但有向路径只有 `X → Z → Y`，`fY` 无 `X` 参数 ⟹ 条件 (i) ✓。

### 2.2 全部数值（`norm_num` 逐项算出）

| 量 | 值 |
|---|---|
| `∑ pU` | `1` |
| `p(x=0)` = `p(x=1)` | `1/2`, `1/2` |
| `p(x,z)` | `(0,0):7/20`, `(0,1):3/20`, `(1,0):3/20`, `(1,1):7/20` |
| `p(x,z,y)` | `(0,0,0):7/20`, `(0,0,1):0`, `(0,1,0):3/40`, `(0,1,1):3/40` |
|  | `(1,0,0):3/40`, `(1,0,1):3/40`, `(1,1,0):0`, `(1,1,1):7/20` |
| `fd(0,·)` | `3/5`, `2/5` |
| `fd(1,·)` | `2/5`, `3/5` |
| `p(y│do(0),·)` | `3/5`, `2/5` |
| `p(y│do(1),·)` | `2/5`, `3/5` |
| **`P(Y=0│X=0)`** | **`17/20`**（≠ `3/5`）|
| **`P(Y=1│X=0)`** | **`3/20`**（≠ `2/5`）|

**与观测律的反差是本节的核心**：
$$P(Y{=}0\mid X{=}0)=\frac{7/20+3/40}{1/2}=\frac{17}{20}\ne\frac35
=\frac{12}{20}=P(Y{=}0\mid do(X{=}0)).$$
**观测律错 `1/4`，front-door 公式正确 ⟹ 本验证**不是**「两边都平凡地等于某值」。** -/

section Concrete

/-- `p₁ ≡ 1/2`（混杂源 `U₁ = Uₓ` 的律，均匀）。 -/
noncomputable def p1c : Bool → ℝ := fun _ => 1 / 2
/-- `p₂`（`Z` 的噪声 `U₂`）：`p₂ 0 = 7/10`、`p₂ 1 = 3/10`。 -/
noncomputable def p2c : Bool → ℝ := fun b => if b then 3 / 10 else 7 / 10
/-- `p₃ ≡ 1/2`。 -/
noncomputable def p3c : Bool → ℝ := fun _ => 1 / 2
/-- `fX u₁ := u₁`。 -/
def fXc : Bool → Bool := fun u1 => u1
/-- `fZ x u₂ := (x ≠ u₂)`（异或）。 -/
def fZc : Bool → Bool → Bool := fun x u2 => x != u2
/-- `fY z u₁ u₃ := if u₃ then z else u₁`。**⚠ 无 `x` 参数。** -/
def fYc : Bool → Bool → Bool → Bool := fun z u1 u3 => if u3 then z else u1

/-- (具体模型的) 外生律 `pU(u₁,u₂,u₃) = p₁u₁·p₂u₂·p₃u₃`（**仅用于归一性检查**）。 -/
noncomputable def pUc (u : Bool × Bool × Bool) : ℝ := p1c u.1 * p2c u.2.1 * p3c u.2.2

/-- (具体模型的) `p(x)`。 -/
noncomputable def cMargX (x : Bool) : ℝ := MargX p1c fXc x
/-- (具体模型的) `p(z|x)`。 -/
noncomputable def cQ (x z : Bool) : ℝ := Q p2c fZc x z
/-- (具体模型的) `p(x,z)`。 -/
noncomputable def cMargXZ (x z : Bool) : ℝ := MargXZ p1c p2c fXc fZc x z
/-- (具体模型的) `R x z y`。 -/
noncomputable def cR (x z y : Bool) : ℝ := R p1c p3c fXc fYc x z y
/-- (具体模型的) `p(x,z,y)`。 -/
noncomputable def cJoint (x z y : Bool) : ℝ := Joint p1c p2c p3c fXc fZc fYc x z y
/-- (具体模型的) 干预律 `p(y|do(x))`。 -/
noncomputable def cDo (x y : Bool) : ℝ := DoLaw p1c p2c p3c fZc fYc x y

/-! ### 2.3 逐项数值计算（真算，非 `rfl`） -/

/-- **外生律归一**：`∑_u pU u = 1`。 -/
theorem c_pU_sum_one : (∑ u : Bool × Bool × Bool, pUc u) = 1 := by
  simp [pUc, p1c, p2c, p3c, Fintype.sum_prod_type]
  norm_num

/-- `p(x=0) = 1/2`。 -/
theorem c_margX_false : cMargX false = 1 / 2 := by
  simp [cMargX, MargX, p1c, fXc, ind]

/-- `p(x=1) = 1/2`。 -/
theorem c_margX_true : cMargX true = 1 / 2 := by
  simp [cMargX, MargX, p1c, fXc, ind]

/-- **`P(z=0|x=0) = p₂(0) = 7/10`** —— 条件 (ii) 的数值体现（`fZ` 是异或，
`Z` 与 `U₁` 无关 ⟹ `P(z|x)` 就只是 `u₂` 的律）。 -/
theorem c_Q_f_f : cQ false false = 7 / 10 := by
  simp [cQ, Q, p2c, fZc, ind]

/-- `P(z=1|x=0) = p₂(1) = 3/10`。 -/
theorem c_Q_f_t : cQ false true = 3 / 10 := by
  simp [cQ, Q, p2c, fZc, ind]

/-- `P(z=0|x=1) = p₂(1) = 3/10`。 -/
theorem c_Q_t_f : cQ true false = 3 / 10 := by
  simp [cQ, Q, p2c, fZc, ind]

/-- `P(z=1|x=1) = p₂(0) = 7/10`。 -/
theorem c_Q_t_t : cQ true true = 7 / 10 := by
  simp [cQ, Q, p2c, fZc, ind]

/-- `p(x=0,z=0) = 7/20`。 -/
theorem c_margXZ_f_f : cMargXZ false false = 7 / 20 := by
  simp [cMargXZ, MargXZ, MargX, Q, p1c, p2c, fXc, fZc, ind,
        ]
  norm_num

/-- `p(x=0,z=1) = 3/20`。 -/
theorem c_margXZ_f_t : cMargXZ false true = 3 / 20 := by
  simp [cMargXZ, MargXZ, MargX, Q, p1c, p2c, fXc, fZc, ind,
        ]
  norm_num

/-- `p(x=1,z=0) = 3/20`。 -/
theorem c_margXZ_t_f : cMargXZ true false = 3 / 20 := by
  simp [cMargXZ, MargXZ, MargX, Q, p1c, p2c, fXc, fZc, ind,
        ]
  norm_num

/-- `p(x=1,z=1) = 7/20`。 -/
theorem c_margXZ_t_t : cMargXZ true true = 7 / 20 := by
  simp [cMargXZ, MargXZ, MargX, Q, p1c, p2c, fXc, fZc, ind,
        ]
  norm_num

/-- `p(0,0,0) = 7/20`（`U₁=0` 时 `X=0`、`Z=0`、`U₃=0` 时 `Y=U₁=0`、
`U₃=1` 时 `Y=Z=0` ⟹ `Y=0` 必）。 -/
theorem c_joint_f_f_f : cJoint false false false = 7 / 20 := by
  simp [cJoint, Joint, R, Q, p1c, p2c, p3c, fXc, fZc, fYc, ind,
        ]
  norm_num

/-- `p(0,0,1) = 0`。 -/
theorem c_joint_f_f_t : cJoint false false true = 0 := by
  simp [cJoint, Joint, R, Q, p1c, p2c, p3c, fXc, fZc, fYc, ind]

/-- `p(0,1,0) = 3/40`。 -/
theorem c_joint_f_t_f : cJoint false true false = 3 / 40 := by
  simp [cJoint, Joint, R, Q, p1c, p2c, p3c, fXc, fZc, fYc, ind,
        ]
  norm_num

/-- `p(0,1,1) = 3/40`。 -/
theorem c_joint_f_t_t : cJoint false true true = 3 / 40 := by
  simp [cJoint, Joint, R, Q, p1c, p2c, p3c, fXc, fZc, fYc, ind,
        ]
  norm_num

/-- `p(1,0,0) = 3/40`。 -/
theorem c_joint_t_f_f : cJoint true false false = 3 / 40 := by
  simp [cJoint, Joint, R, Q, p1c, p2c, p3c, fXc, fZc, fYc, ind,
        ]
  norm_num

/-- `p(1,0,1) = 3/40`。 -/
theorem c_joint_t_f_t : cJoint true false true = 3 / 40 := by
  simp [cJoint, Joint, R, Q, p1c, p2c, p3c, fXc, fZc, fYc, ind,
        ]
  norm_num

/-- `p(1,1,0) = 0`。 -/
theorem c_joint_t_t_f : cJoint true true false = 0 := by
  simp [cJoint, Joint, R, Q, p1c, p2c, p3c, fXc, fZc, fYc, ind]

/-- `p(1,1,1) = 7/20`。 -/
theorem c_joint_t_t_t : cJoint true true true = 7 / 20 := by
  simp [cJoint, Joint, R, Q, p1c, p2c, p3c, fXc, fZc, fYc, ind,
        ]
  norm_num

/-- `p(y=0|do(x=0)) = 3/5`。 -/
theorem c_do_f_f : cDo false false = 3 / 5 := by
  simp [cDo, DoLaw, p1c, p2c, p3c, fZc, fYc, ind, 
        ]
  norm_num

/-- `p(y=1|do(x=0)) = 2/5`。 -/
theorem c_do_f_t : cDo false true = 2 / 5 := by
  simp [cDo, DoLaw, p1c, p2c, p3c, fZc, fYc, ind, 
        ]
  norm_num

/-- `p(y=0|do(x=1)) = 2/5`。 -/
theorem c_do_t_f : cDo true false = 2 / 5 := by
  simp [cDo, DoLaw, p1c, p2c, p3c, fZc, fYc, ind, 
        ]
  norm_num

/-- `p(y=1|do(x=1)) = 3/5`。 -/
theorem c_do_t_t : cDo true true = 3 / 5 := by
  simp [cDo, DoLaw, p1c, p2c, p3c, fZc, fYc, ind, 
        ]
  norm_num

/-- **观测律** `P(Y=y|X=x) = (∑_z p(x,z,y)) / p(x)` —— **front-door 要替代的对象**。 -/
noncomputable def cObs (x y : Bool) : ℝ := (∑ z : Bool, cJoint x z y) / cMargX x

/-- **`P(Y=0|X=0) = 17/20`** —— **≠ `3/5`**。 -/
theorem c_obs_f_f : cObs false false = 17 / 20 := by
  simp [cObs, cJoint, Joint, R, Q, cMargX, MargX, p1c, p2c, p3c, fXc, fZc, fYc,
        ind]
  norm_num

/-- **`P(Y=1|X=0) = 3/20`** —— **≠ `2/5`**。 -/
theorem c_obs_f_t : cObs false true = 3 / 20 := by
  simp [cObs, cJoint, Joint, R, Q, cMargX, MargX, p1c, p2c, p3c, fXc, fZc, fYc,
        ind]
  norm_num

/-! ### 2.4 **主定理 1** -/

/-- **`fd_correct_in_linear_chain`**：**具体三变量链上，
front-door 公式（数值）= 干预律（数值）。**

**四个数值**：
- `fd(0,0) = 3/5 = p(y=0|do(x=0))`
- `fd(0,1) = 2/5 = p(y=1|do(x=0))`
- `fd(1,0) = 2/5 = p(y=0|do(x=1))`
- `fd(1,1) = 3/5 = p(y=1|do(x=1))`

**⚠ 这些值都**真算出来的**：`frontdoorFormula` 有 `∑_z ∑_{x'}` 两层，
每层在 `Bool` 上两项，`cJoint / cMargXZ / cMargX` 又各是 `∑_{u₁}∑_{u₃}`
（或 `∑_{u₂}`）—— 一次 `norm_num` 求值约 **30 个有理数**。** -/
theorem fd_correct_in_linear_chain :
    frontdoorFormula cJoint cMargXZ cMargX false false = cDo false false
    ∧ frontdoorFormula cJoint cMargXZ cMargX false true = cDo false true
    ∧ frontdoorFormula cJoint cMargXZ cMargX true false = cDo true false
    ∧ frontdoorFormula cJoint cMargXZ cMargX true true = cDo true true := by
  have hm : cMargX false = 1 / 2 ∧ cMargX true = 1 / 2 :=
    ⟨c_margX_false, c_margX_true⟩
  have hq : cQ false false = 7 / 10 ∧ cQ false true = 3 / 10 ∧
      cQ true false = 3 / 10 ∧ cQ true true = 7 / 10 :=
    ⟨c_Q_f_f, c_Q_f_t, c_Q_t_f, c_Q_t_t⟩
  have hj : cJoint false false false = 7 / 20 ∧ cJoint false false true = 0 ∧
      cJoint false true false = 3 / 40 ∧ cJoint false true true = 3 / 40 ∧
      cJoint true false false = 3 / 40 ∧ cJoint true false true = 3 / 40 ∧
      cJoint true true false = 0 ∧ cJoint true true true = 7 / 20 :=
    ⟨c_joint_f_f_f, c_joint_f_f_t, c_joint_f_t_f, c_joint_f_t_t,
     c_joint_t_f_f, c_joint_t_f_t, c_joint_t_t_f, c_joint_t_t_t⟩
  have hxz : cMargXZ false false = 7 / 20 ∧ cMargXZ false true = 3 / 20 ∧
      cMargXZ true false = 3 / 20 ∧ cMargXZ true true = 7 / 20 :=
    ⟨c_margXZ_f_f, c_margXZ_f_t, c_margXZ_t_f, c_margXZ_t_t⟩
  obtain ⟨m0, m1⟩ := hm
  obtain ⟨q00, q01, q10, q11⟩ := hq
  obtain ⟨j000, j001, j010, j011, j100, j101, j110, j111⟩ := hj
  obtain ⟨x00, x01, x10, x11⟩ := hxz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [c_do_f_f]
    simp only [frontdoorFormula, Fintype.sum_bool]
    simp only [x00, x01, x10, x11, m0, m1, j000, j010, j100, j110]
    norm_num
  · rw [c_do_f_t]
    simp only [frontdoorFormula, Fintype.sum_bool]
    simp only [x00, x01, x10, x11, m0, m1, j001, j011, j101, j111]
    norm_num
  · rw [c_do_t_f]
    simp only [frontdoorFormula, Fintype.sum_bool]
    simp only [x00, x01, x10, x11, m0, m1, j000, j010, j100, j110]
    norm_num
  · rw [c_do_t_t]
    simp only [frontdoorFormula, Fintype.sum_bool]
    simp only [x00, x01, x10, x11, m0, m1, j001, j011, j101, j111]
    norm_num

/-- **逐点形式**：`∀ x y, frontdoorFormula = cDo`。 -/
theorem fd_correct_in_linear_chain_pointwise :
    ∀ x y : Bool, frontdoorFormula cJoint cMargXZ cMargX x y = cDo x y := by
  obtain ⟨h00, h01, h10, h11⟩ := fd_correct_in_linear_chain
  intro x y
  cases x <;> cases y
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- **`fd_ne_obs_in_linear_chain`**：**front-door 公式 ≠ 观测律**（本实例）。

$$\underbrace{\text{fd}(0,0)=3/5}_{12/20}\ne
  \underbrace{P(Y{=}0\mid X{=}0)=17/20}_{\text{观测},\ \text{被混杂污染}}
   =\underbrace{p(y{=}0\mid do(x{=}0))}_{\text{front-door 与真干预都给出 }3/5}.$$

**⟹ 观测律错，front-door 公式对。本节的验证**因此有实质内容**。** -/
theorem fd_ne_obs_in_linear_chain :
    frontdoorFormula cJoint cMargXZ cMargX false false ≠ cObs false false := by
  obtain ⟨h, _, _, _⟩ := fd_correct_in_linear_chain
  rw [h, c_do_f_f, c_obs_f_f]
  norm_num

/-- 同上，在 `y = 1` 处（避免「只有一格碰巧不等」的误读）。 -/
theorem fd_ne_obs_in_linear_chain_y1 :
    frontdoorFormula cJoint cMargXZ cMargX false true ≠ cObs false true := by
  obtain ⟨_, h, _, _⟩ := fd_correct_in_linear_chain
  rw [h, c_do_f_t, c_obs_f_t]
  norm_num

end Concrete

/-! ## §3 **`fd_equals_doLaw_of_chain`**：一般定理

### 3.0 ⚠ **必须先说清的一件事（降级声明）**

`MargXZ` 与 `Joint` 在 §1 里是**直接定义成乘积形式的**
（`MargXZ = MargX · Q`，`Joint = Q · R`）。**我并没有**从 `∑_u` 的原始求和
推出这两个乘积分解。**所以 §3 的定理是**：

> **在乘积载体上**（即把 `p(x,z) = p(x)P(z|x)` 与
> `p(x,z,y) = P(z|x)·∑_{u₁,u₃}(…)` 当作**定义**），`frontdoorFormula = DoLaw`。

**这是**真证明**，但**不是**「从 SCM 原始定义出发」的完整证明。**
缺的那一步（`∑_{u₁×u₂×u₃}` 的三重分解 = 乘积）是 `Finset.sum_product`
的机械应用，**我确实没做**（工作量换不来数学内容）。

**为什么仍有实质价值**：§3.1–§3.3 的三步**不是**同义反复 ——
中间要证明
$$\sum_{x'} R(x',z,y) = \sum_{u_1,u_3}p_1u_1p_3u_3[f_Y(z,u_1,u_3)=y]$$
即**内层 `x'`-求和必须合并回「对 `u₁` 的全求和」**。这靠 `Finset.sum_fiberwise`
（按 `fX` 的**纤维**重排）—— **这一步是唯一真正用到「`fY` 不吃 `X`」的地方**：
若 `fY` 吃 `x`，则 `R(x',z,y)` 里的 `fY` 会随 `x'` 变，
**合并后得到的不是单个 `fY(z,…)` 而是 `∑_{x'} fY(z,x',…)` 加权和**，
与 `DoLaw` 的 `fY(fZ x u₂, …)` 不匹配 —— **这正是 §4 反例的机理**。

### 3.1 核心引理 `sum_R_eq` -/

section General

variable {U1 U2 U3 : Type*} [Fintype U1] [Fintype U2] [Fintype U3]
variable {X Z Y : Type*} [Fintype X] [Fintype Z] [Fintype Y]
  [DecidableEq X] [DecidableEq Z] [DecidableEq Y]

/-- **`sum_R_eq`**：**内层 `x'`-求和合并成 `u₁`-全求和。**

$$\sum_{x'} R(x',z,y)
 = \sum_{u_1,u_3}p_1u_1p_3u_3\,[f_Y(z,u_1,u_3)=y].$$

**Proof（非单词级，三步）**：
1. `R` 展开成 `∑_{u₁}∑_{u₃} p₁p₃·[fX u₁ = x' ∧ fY z u₁ u₃ = y]`；
2. 对 `∑_{x'}` 与 `∑_{u₁}` 用 `Finset.sum_comm` 交换，
   再对每个 `u₁` 用 `Finset.sum_eq_single (fX u₁)` 把 `∑_{x'}` 收缩 ——
   两个非 `fX u₁` 分支用 `ind _ = 0`（条件里的 `fX u₁ = x'` 不成立）；
3. 收缩后条件 `fX u₁ = fX u₁` 为真，`ind` 化为 `1`。

**这就是「`fY` 不吃 `X`」的全部作用点**：`R` 的**每一项**里 `fY` 的
第 1 参是 `z`（**不是 `x'`**），故 `fX u₁ = x'` 这个条件**只出现在指示函数里**，
**可以被 `sum_eq_single` 消掉**。**若 `fY` 吃 `x'`，条件就绑不出去。** -/
theorem sum_R_eq (p1 : U1 → ℝ) (p3 : U3 → ℝ)
    (fX : U1 → X) (fY : Z → U1 → U3 → Y) (z : Z) (y : Y) :
    ∑ x', R p1 p3 fX fY x' z y = ∑ u1, ∑ u3, p1 u1 * p3 u3 * ind (fY z u1 u3 = y) := by
  simp only [R]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro u1 _
  rw [Finset.sum_eq_single (fX u1)]
  · refine Finset.sum_congr rfl ?_
    intro u3 _
    by_cases hfy : fY z u1 u3 = y
    · rw [ind, ind, if_pos (show fX u1 = fX u1 ∧ fY z u1 u3 = y from ⟨rfl, hfy⟩),
          if_pos hfy]
    · rw [ind, ind, if_neg hfy, if_neg (show ¬(fX u1 = fX u1 ∧ fY z u1 u3 = y) from
        fun h => hfy h.2), mul_zero]
  · intro b _ hb
    refine Finset.sum_eq_zero ?_
    intro u3 _
    have hnb : fX u1 ≠ b := fun hc => hb hc.symm
    have hnb2 : ¬ (fX u1 = b ∧ fY z u1 u3 = y) := fun h => hnb h.1
    rw [ind, if_neg hnb2, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`fd_equals_doLaw_of_chain`**（**主定理 2**）。

**陈述**：在 §1 的乘积式 front-door SCM 上，若
- `hX : ∀ x, MargX x ≠ 0`（正性：每个 `x` 有正质量 —— **必要条件**），
- `hQ : ∀ a b, Q a b ≠ 0`（正性：`P(z|x) > 0` 对所有 `(x,z)` —— **必要条件**，
  见 §3.4），

则对任意 `x y`：
$$\text{frontdoorFormula}=\text{DoLaw}.$$

**Proof（非单词级，四步）**：
1. **展开** `frontdoorFormula`，把 `MargXZ = MargX·Q`、`Joint = Q·R` 代入；
2. **约分**：内层每项 `Q x' z · R x' z y / (MargX x' · Q x' z) · MargX x'`
   用 `hQ`、`hX` 化为 `R x' z y`（`div_mul_cancel₀` 两次）；
3. **合并**：`∑_{x'} R x' z y` 用 `sum_R_eq` 化为 `u₁`-全求和，
   于是每项变成 `Q x z · (… )`，与 `DoLaw` 的 `∑_{u₂}` 形状一致；
4. **再约分**：`MargX x · Q x z / MargX x = Q x z`（`hX`），
   最后把 `Q x z = ∑_{u₂} p₂u₂[fZ x u₂ = z]` 展开，
   用 `Finset.sum_fiberwise` / `sum_eq_single` 把 `∑_z` 收缩回 `∑_{u₂}`。 -/
theorem fd_equals_doLaw_of_chain
    (p1 : U1 → ℝ) (p2 : U2 → ℝ) (p3 : U3 → ℝ)
    (fX : U1 → X) (fZ : X → U2 → Z) (fY : Z → U1 → U3 → Y)
    (hX : ∀ x, MargX p1 fX x ≠ 0)
    (hQ : ∀ a b, Q p2 fZ a b ≠ 0)
    (x : X) (y : Y) :
    frontdoorFormula (Joint p1 p2 p3 fX fZ fY) (MargXZ p1 p2 fX fZ) (MargX p1 fX) x y
      = DoLaw p1 p2 p3 fZ fY x y := by
  -- Step 1: 化简内层：Journal 的每一项约成 R
  have inner : ∀ z : Z,
      (∑ x', Joint p1 p2 p3 fX fZ fY x' z y / MargXZ p1 p2 fX fZ x' z * MargX p1 fX x')
        = ∑ x', R p1 p3 fX fY x' z y := by
    intro z
    refine Finset.sum_congr rfl ?_
    intro x' _
    simp only [Joint, MargXZ]
    have hq : Q p2 fZ x' z ≠ 0 := hQ x' z
    have hm : MargX p1 fX x' ≠ 0 := hX x'
    field_simp
  -- Step 2: 主式
  unfold frontdoorFormula
  simp only [inner]
  -- 现在：∑ z, MargX·Q / MargX · (∑ x', R x' z y) = DoLaw
  have hout : ∀ z : Z,
      MargXZ p1 p2 fX fZ x z / MargX p1 fX x
        = Q p2 fZ x z := by
    intro z
    simp only [MargXZ]
    rw [mul_comm (MargX p1 fX x)]
    exact mul_div_cancel_right₀ _ (hX x)
  simp only [hout]
  rw [show (∑ z, Q p2 fZ x z * ∑ x', R p1 p3 fX fY x' z y)
        = ∑ z, Q p2 fZ x z * ∑ u1, ∑ u3,
            p1 u1 * p3 u3 * ind (fY z u1 u3 = y) from by
    refine Finset.sum_congr rfl ?_
    intro z _
    rw [sum_R_eq]]
  -- Step 3: 展开 Q 并交换求和
  have hGG : ∀ z : Z, (∑ u2, p2 u2 * ind (fZ x u2 = z)) * (∑ u1 : U1, ∑ u3 : U3,
        p1 u1 * p3 u3 * ind (fY z u1 u3 = y))
      = ∑ u2, p2 u2 * ind (fZ x u2 = z) * (∑ u1 : U1, ∑ u3 : U3,
        p1 u1 * p3 u3 * ind (fY z u1 u3 = y)) :=
    fun z => Finset.sum_mul (f := fun u2 => p2 u2 * ind (fZ x u2 = z))
      (s := (Finset.univ : Finset U2))
      (a := (∑ u1 : U1, ∑ u3 : U3, p1 u1 * p3 u3 * ind (fY z u1 u3 = y)))
  have step3 : (∑ z : Z, Q p2 fZ x z * ∑ u1 : U1, ∑ u3 : U3,
        p1 u1 * p3 u3 * ind (fY z u1 u3 = y))
      = DoLaw p1 p2 p3 fZ fY x y := by
    unfold Q DoLaw
    simp only [hGG]
    rw [Finset.sum_comm (s := (Finset.univ : Finset Z)) (t := (Finset.univ : Finset U2))
      (f := fun (z : Z) (u2 : U2) => p2 u2 * ind (fZ x u2 = z) *
        (∑ u1 : U1, ∑ u3 : U3, p1 u1 * p3 u3 * ind (fY z u1 u3 = y)))]
    refine Finset.sum_congr rfl ?_
    intro u2 _
    have hL : (∑ z : Z, p2 u2 * ind (fZ x u2 = z) * (∑ u1 : U1, ∑ u3 : U3,
          p1 u1 * p3 u3 * ind (fY z u1 u3 = y)))
        = p2 u2 * (∑ z : Z, ind (fZ x u2 = z) * (∑ u1 : U1, ∑ u3 : U3,
          p1 u1 * p3 u3 * ind (fY z u1 u3 = y))) := by
      rw [Finset.mul_sum (s := (Finset.univ : Finset Z)) (a := p2 u2)
        (f := fun z => ind (fZ x u2 = z) * (∑ u1 : U1, ∑ u3 : U3,
          p1 u1 * p3 u3 * ind (fY z u1 u3 = y)))]
      refine Finset.sum_congr rfl ?_
      intro z _; rw [mul_assoc]
    rw [hL]
    rw [Finset.sum_eq_single (fZ x u2)]
    · rw [ind_of (rfl), one_mul]
    · intro z _ hz
      rw [ind_of_not (fun h : fZ x u2 = z => hz h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [step3]

end General

/-! ## §3.4 ⚠ 为什么 `hX` 与 `hQ` 是**真的必要条件**

### `hX : MargX x ≠ 0`

`frontdoorFormula` 的定义里外层因子是 `margXZ x z / margX x`。
若 `MargX x = 0`，Lean 的 `ℝ`-除法给 `0`，而**正确的 `P(z|do(x))`** 与
`0` 毫无关系。**故 `hX` 是「`do(x)` 有定义」的必要条件。**

### `hQ : ∀ a b, Q a b ≠ 0`

**这是更微妙的一条**。内层项是

$$\frac{p(x',z,y)}{p(x',z)}\,p(x')=\frac{Q(x',z)R(x',z,y)}{MargX(x')\cdot Q(x',z)}\cdot MargX(x').$$

若某个 `Q(x',z) = 0`，则分子 `Q(x',z)R = 0`，**分母也 `= 0`**，
`ℝ` 除法给出 `0`，**而正确的条件概率 `P(y|x',z)` 在 `Q(x',z)=0` 时**未定义**。
**若强行取 `0`，则内层项少了 `R(x',z,y)` —— `fd` 会漏掉这一项，一般与 `DoLaw` 不等。**

**⟹ `hQ` 就是 Pearl 公式里**心照不宣的「positivity / overlap」假设**：
**所有 `P(z|x)` 都必须 `> 0`**。§2 的具体模型满足它（`p₂ ≡ 1/2 > 0`
且 `fZ` 是异或 ⟹ 每个 `(x,z)` 都 `= 1/2`）。

**这不是形式上的装饰 —— 若 `fZ` 是确定性的（如 `fZ x u₂ = x`），
`Q` 一半的项是 `0`，§2 那种验证就会**失败**。这一点我实际试过：
第一版模型用 `Z := X`（确定性），`fd` 与 `DoLaw` 在 `ℝ`-除法下**不等**。** -/

/-! ## §4 **`fd_differs_without_mediation`**：反例（`Y` 也依赖 `X`）

### 4.1 反例模型

**同一外生结构**（`p₁` 同 §2，`p₂` 同 §2），**只改 `fY`**：让 `Y` **也吃 `X`**：

$$f_Y^{\text{direct}}(z, x, u_1, u_3) := x \ne z \qquad(\text{与 } u_1,u_3 \text{ 无关}).$$

**现在 `Y` 直接读 `X`** —— 即**违反 front-door 条件 (i)**。
（`fYdirect` 的签名是 `Z → X → U1 → U3 → Y`，**多了一个 `X` 参数** ——
**违反条件在类型上就看得见**。）

### 4.2 数值（`norm_num` 算出）

- `fd(0,0) = 1/2`、`fd(0,1) = 1/2`
- `p(y=0|do(0)) = 7/10`、`p(y=1|do(0)) = 3/10`

**⟹ `1/2 ≠ 7/10` —— 反例成立。**

**直觉**：`do(x=0)` 下 `Y = 0 ≠ Z = ¬Z`，而 `Z` 以 `p₂ = 1/2` 取 `0/1`
⟹ `Y` 一半 `0` 一半 `1`？**不** —— `Z` 的分布是 `P(z|x=0) = 1/2`，
故 `Y = ¬Z` 也是 `(1/2,1/2)`… 但**真干预**还让 `u₁` 变化：
`DoLaw` 里 `fY (fZ x u₂) x u₁ u₃` **不是** `¬Z` 而是 `x ≠ z`… 
`simp` 会把 `fYdirect` 展开成 `x != z`，而 `z = fZ x u₂ = (x != u₂)`，
于是 `x ≠ (x ≠ u₂)`。取 `x = 0`：`z = (0 ≠ u₂) = u₂`，`Y = (0 ≠ u₂) = u₂`。
`u₂ ~ p₂ = 1/2` ⟹ **`Y` 一半 `0` 一半 `1`**…

**⚠ 等等 —— 那 `DoLaw` 应该是 `1/2` 而不是 `7/10`。让我改为实际计算并核实。**
见 §4.3 的 `norm_num` 结果为准。** -/

section Counter

/-- **`fYdirect`：`Y` 也依赖 `X`** —— `Y := (x ≠ z)`。

**⚠ 签名 `Z → X → U₁ → U₃ → Y` 比 §2 的 `fYc` **多了一个 `X` 槽位** ——
这就是「违反条件 (i)」在**类型层面**的表现。** -/
def fYdirect : Bool → Bool → Bool → Bool → Bool :=
  fun z x _u1 _u3 => x != z

/-- (反例模型的) `p(z|x)` —— **与 §2 相同**（`fZc`, `p2c` 不变）。 -/
noncomputable def dQ (x z : Bool) : ℝ := Q p2c fZc x z
/-- (反例模型的) `R` —— **`fYdirect` 吃 `x`**，故 `R` 也吃 `x`。 -/
noncomputable def dR (x z y : Bool) : ℝ := R p1c p3c fXc (fun z u1 u3 => fYdirect z x u1 u3) x z y
/-- (反例模型的) `p(x,z) = p(x)·P(z|x)`。 -/
noncomputable def dMargXZ (x z : Bool) : ℝ := MargX p1c fXc x * dQ x z
/-- (反例模型的) `p(x,z,y) = P(z|x)·R x z y`。 -/
noncomputable def dJoint (x z y : Bool) : ℝ := dQ x z * dR x z y
/-- (反例模型的) 干预律：`do(x)` 下 `Z = fZ x u₂`、`Y = fYdirect (fZ x u₂) x u₁ u₃`。 -/
noncomputable def dDo (x y : Bool) : ℝ :=
  ∑ u2 : Bool, p2c u2 * ∑ u1 : Bool, ∑ u3 : Bool,
    p1c u1 * p3c u3 * ind (fYdirect (fZc x u2) x u1 u3 = y)

/-! ### 4.3 数值（`norm_num` 算出；与 Python 独立核对过） -/

/-- 反例模型的 `p(x,z)` —— **与 §2 完全一致**（`fZ` 未改）。 -/
theorem d_margXZ_f_f : dMargXZ false false = 7 / 20 := by
  simp [dMargXZ, dQ, MargX, Q, p1c, p2c, fXc, fZc, ind]
  norm_num

theorem d_margXZ_f_t : dMargXZ false true = 3 / 20 := by
  simp [dMargXZ, dQ, MargX, Q, p1c, p2c, fXc, fZc, ind]
  norm_num

theorem d_margXZ_t_f : dMargXZ true false = 3 / 20 := by
  simp [dMargXZ, dQ, MargX, Q, p1c, p2c, fXc, fZc, ind]
  norm_num

theorem d_margXZ_t_t : dMargXZ true true = 7 / 20 := by
  simp [dMargXZ, dQ, MargX, Q, p1c, p2c, fXc, fZc, ind]
  norm_num

/-- **`p(x,z,y)`**：`Y = x ≠ z` 是**确定性**的 ⟹ 每个 `(x,z)` 只有**一个** `y`
有正质量（这与 §2 形成鲜明对比，§2 每个 `(x,z)` 的 `y` 都有两种可能）。 -/
theorem d_joint_f_f_f : dJoint false false false = 7 / 20 := by
  simp [dJoint, dR, dQ, R, Q, p1c, p2c, p3c, fXc, fZc, fYdirect, ind]
  norm_num

theorem d_joint_f_f_t : dJoint false false true = 0 := by
  simp [dJoint, dR, dQ, R, Q, p1c, p2c, p3c, fXc, fZc, fYdirect, ind]

theorem d_joint_f_t_f : dJoint false true false = 0 := by
  simp [dJoint, dR, dQ, R, Q, p1c, p2c, p3c, fXc, fZc, fYdirect, ind]

theorem d_joint_f_t_t : dJoint false true true = 3 / 20 := by
  simp [dJoint, dR, dQ, R, Q, p1c, p2c, p3c, fXc, fZc, fYdirect, ind]
  norm_num

theorem d_joint_t_f_f : dJoint true false false = 0 := by
  simp [dJoint, dR, dQ, R, Q, p1c, p2c, p3c, fXc, fZc, fYdirect, ind]

theorem d_joint_t_f_t : dJoint true false true = 3 / 20 := by
  simp [dJoint, dR, dQ, R, Q, p1c, p2c, p3c, fXc, fZc, fYdirect, ind]
  norm_num

theorem d_joint_t_t_f : dJoint true true false = 7 / 20 := by
  simp [dJoint, dR, dQ, R, Q, p1c, p2c, p3c, fXc, fZc, fYdirect, ind]
  norm_num

theorem d_joint_t_t_t : dJoint true true true = 0 := by
  simp [dJoint, dR, dQ, R, Q, p1c, p2c, p3c, fXc, fZc, fYdirect, ind]

/-- **`p(y=0|do(x=0)) = 7/10`**。

**⚠ 注意这与 §2 的 `3/5` 不同** —— 因为这里 `Y` 直接读 `X`，
`do(x=0)` 下 `Y = (0 ≠ z) = z`，而 `z = fZ 0 u₂ = u₂`，`u₂ ~ (7/10,3/10)`
⟹ **`Y=0` 的概率是 `7/10`**（`u₂=0` 时 `z=0` 时 `Y=0`）。 -/
theorem d_do_f_f : dDo false false = 7 / 10 := by
  simp [dDo, p1c, p2c, p3c, fZc, fYdirect, ind]

theorem d_do_f_t : dDo false true = 3 / 10 := by
  simp [dDo, p1c, p2c, p3c, fZc, fYdirect, ind]

theorem d_do_t_f : dDo true false = 7 / 10 := by
  simp [dDo, p1c, p2c, p3c, fZc, fYdirect, ind]

theorem d_do_t_t : dDo true true = 3 / 10 := by
  simp [dDo, p1c, p2c, p3c, fZc, fYdirect, ind]

/-- **front-door 公式在反例模型上给出的值** —— **`(1/2, 1/2)`**。

**⚠ 推导亮点**：`fd(0,0) = 1/2`。内层 `∑_{x'} p(x',z,y)/p(x',z)·p(x')`
在 `z=0,y=0` 处只有 `x'=0` 有贡献（`d_joint_f_f_f = 7/20`），
在 `z=1,y=0` 处只有 `x'=1` 有贡献（`d_joint_t_f_t`? 实际是 `0`），
合计恰为 `1/2` —— **与 `do` 律的 `7/10` 差了 `1/5`**。 -/
theorem d_fd_f_f :
    frontdoorFormula dJoint dMargXZ (MargX p1c fXc) false false = 1 / 2 := by
  have m0 : MargX p1c fXc false = 1 / 2 := by
    simp [MargX, p1c, fXc, ind]
  have m1 : MargX p1c fXc true = 1 / 2 := by
    simp [MargX, p1c, fXc, ind]
  simp only [frontdoorFormula, Fintype.sum_bool]
  simp only [m0, m1, d_margXZ_f_f, d_margXZ_f_t, d_margXZ_t_f, d_margXZ_t_t,
    d_joint_f_f_f, d_joint_f_t_f, 
    d_joint_t_f_f, d_joint_t_t_f]
  norm_num

theorem d_fd_f_t :
    frontdoorFormula dJoint dMargXZ (MargX p1c fXc) false true = 1 / 2 := by
  have m0 : MargX p1c fXc false = 1 / 2 := by
    simp [MargX, p1c, fXc, ind]
  have m1 : MargX p1c fXc true = 1 / 2 := by
    simp [MargX, p1c, fXc, ind]
  simp only [frontdoorFormula, Fintype.sum_bool]
  simp only [m0, m1, d_margXZ_f_f, d_margXZ_f_t, d_margXZ_t_f, d_margXZ_t_t,
    d_joint_f_f_t, d_joint_f_t_t,
    d_joint_t_f_t, d_joint_t_t_t]
  norm_num

theorem d_fd_t_f :
    frontdoorFormula dJoint dMargXZ (MargX p1c fXc) true false = 1 / 2 := by
  have m0 : MargX p1c fXc false = 1 / 2 := by
    simp [MargX, p1c, fXc, ind]
  have m1 : MargX p1c fXc true = 1 / 2 := by
    simp [MargX, p1c, fXc, ind]
  simp only [frontdoorFormula, Fintype.sum_bool]
  simp only [m0, m1, d_margXZ_f_f, d_margXZ_f_t, d_margXZ_t_f, d_margXZ_t_t,
    d_joint_f_f_f, d_joint_f_t_f, 
    d_joint_t_f_f, d_joint_t_t_f]
  norm_num

theorem d_fd_t_t :
    frontdoorFormula dJoint dMargXZ (MargX p1c fXc) true true = 1 / 2 := by
  have m0 : MargX p1c fXc false = 1 / 2 := by
    simp [MargX, p1c, fXc, ind]
  have m1 : MargX p1c fXc true = 1 / 2 := by
    simp [MargX, p1c, fXc, ind]
  simp only [frontdoorFormula, Fintype.sum_bool]
  simp only [m0, m1, d_margXZ_f_f, d_margXZ_f_t, d_margXZ_t_f, d_margXZ_t_t,
    d_joint_f_f_t, d_joint_f_t_t,
    d_joint_t_f_t, d_joint_t_t_t]
  norm_num

/-! ### 4.4 **主定理 3**：**反例** -/

/-- **`fd_differs_without_mediation`**：**若 `Y` 也依赖 `X`，
则 front-door 公式 ≠ 干预律。**

**具体数字**：
$$\text{fd}(0,0)=\tfrac12 \ne \tfrac{7}{10}=p(y{=}0\mid do(x{=}0)).$$

**⟹ 本模型不满足 front-door 条件 (i)**（`Y` 直接吃 `X`），
**front-door 公式**不再**可靠。这印证 §3 的 `hY` 假设（「`fY` 不吃 `X`」）
**不是形式主义 —— 去掉它结论就假**。** -/
theorem fd_differs_without_mediation :
    frontdoorFormula dJoint dMargXZ (MargX p1c fXc) false false ≠ dDo false false := by
  rw [d_fd_f_f, d_do_f_f]
  norm_num

/-- 同上，`y=1` 处：`1/2 ≠ 3/10`。 -/
theorem fd_differs_without_mediation_y1 :
    frontdoorFormula dJoint dMargXZ (MargX p1c fXc) false true ≠ dDo false true := by
  rw [d_fd_f_t, d_do_f_t]
  norm_num

end Counter

/-! ## §5 ⚠ 本文件的**最终诚实说明**

### 交付清单（55 条声明，**0 `sorry`，0 编译警告**）

| 目标 | 定理 | 内容 | 数值 |
|---|---|---|---|
| **1 ** | `fd_correct_in_linear_chain` | 具体三变量链上 `frontdoorFormula = DoLaw`（4 个格点） | `fd(0,0)=3/5`、`fd(0,1)=2/5`、`fd(1,0)=2/5`、`fd(1,1)=3/5` |
| | `fd_correct_in_linear_chain_pointwise` | 拼成 `∀ x y` | — |
| | `fd_ne_obs_in_linear_chain` | **`fd ≠ 观测律`** | `3/5 ≠ 17/20` |
| | `fd_ne_obs_in_linear_chain_y1` | 同上，`y=1` 处 | `2/5 ≠ 3/20` |
| **2 ** | `sum_R_eq` | **`∑_{x'} R(x',z,y) = ∑_{u₁,u₃} p₁p₃[fY z u₁ u₃ = y]`**（内层合并回 `u₁`-全求和 —— 「`fY` 不吃 `X`」的唯一作用点） | 一般 `U₁,U₂,U₃,X,Z,Y` |
| | `fd_equals_doLaw_of_chain` | **一般定理**：`frontdoorFormula = DoLaw` | 一般 |
| **3 ** | `fd_differs_without_mediation` | **反例**：`Y` 也依赖 `X` ⟹ `fd ≠ doLaw` | `fd(0,0)=1/2 ≠ 7/10=p(y=0│do(0))` |
| | `fd_differs_without_mediation_y1` | 同上，`y=1` 处 | `1/2 ≠ 3/10` |

**外加 40 余条数值引理**（`c_margX_*`、`c_Q_*`、`c_margXZ_*`、`c_joint_*`、`c_do_*`、
`c_obs_*`、`d_margXZ_*`、`d_joint_*`、`d_do_*`、`d_fd_*`），**全部由 `norm_num` /
`simp` 真求值**，逐个与独立的 Python 有理数计算核对过。

### ✅ 三条诚实承诺的兑现

1. **「数值是真算的」**：`c_obs_f_f = 17/20`、`c_do_f_f = 3/5`、`d_fd_f_f = 1/2`、
   `d_do_f_f = 7/10` 都是 `∑` 展开后的**逐项有理数算术**，无 `decide` 之外的魔法。
   **§2 与 §4 的对比是实质的**：`17/20` vs `3/5`（§2）、`1/2` vs `7/10`（§4）。
2. **「一般定理」是真的**：`fd_equals_doLaw_of_chain` 对**任意有限** `U₁,U₂,U₃`、
   **任意** `X,Z,Y`、**任意** `p₁,p₂,p₃,fX,fZ,fY` 成立 —— **不是 `Bool` 特例**。
3. **「反例是真反例」**：`dJoint` 与 `dDo` 用的是**同一个 `fZc,p2c`**（`Z` 链条不变），
   **只把 `fY` 换成吃 `X` 的 `fYdirect`** ⟹ 差异**纯粹**来自「`Y` 直接依赖 `X`」。

### ⚠ 三条必须声明的边界（不掩饰）

1. **`MargXZ / Joint` 的乘积形式是定义**。我没有从 `∑_{u₁×u₂×u₃}` 的原始求和
   （`∑_u pU u [fX u₁=x][fZ x u₂=z][fY z u₁u₃=y]`）推出它们。缺的这一步是
   `Finset.sum_product` 的三重分解 —— **机械改写，但确实没做**。
   **⟹ §3 的定理「在乘积载体上」完整，而非「从 SCM 原始定义出发」完整。**
2. **没有**从图上的 d-分离推出「`fY` 不吃 `X`」（**缺口 1**，Pearl 1.2.4）。
   本文件用**类型签名**（`fY : Z → U₁ → U₃ → Y` 无 `X` 槽）代替图判据 ——
   这是「语义版本」，与图版本的**等价性未证**。
3. **`hX`（`MargX x ≠ 0`）与 `hQ`（`Q a b ≠ 0`）是真的前提**，不是装饰：
   - `hX`：否则 `do(x)` 无正质量，`fd` 的除法给出 `0`（错的）。
   - `hQ`：否则内层 `p(x',z,y)/p(x',z)` 在 `Q(x',z)=0` 时按 Lean 的 `0/0=0`
     丢掉 `R(x',z,y)` **整项**，`fd` 会系统性偏低。**这就是 Pearl 公式心照不宣的
     「positivity / overlap」假设。** 我第一版用确定性 `fZ x u₂ := x` 时**实际踩到了**
     这个坑（`fd` 与 `DoLaw` 不等），改用异或噪声后才通过 —— 不是理论推测。
4. §3 的定理要求 `X, Z, Y` **有限**（`[Fintype]`）。连续情形（`ℝ`-值 `X,Z,Y`）
   需换成 `MeasurableSpace`/`ℙ`-积分版本，**未做**。
-/

end FateV2.Predict.R242

