/-
# R254 · positivity **必要性**：第二个、结构上**不**同的反例

## 背景（R245–R246 的结论，本文件直接续用）

* `FrontdoorChainProof`：在 **positivity 成立**（`p(x) ≠ 0`、`p(x,z) ≠ 0`
  对所有 `(x,z)`）并且前置条件 (i)(ii)(iii) 成立时，
  `frontdoorFormula = doLaw`（**正确性**）。
* `FrontdoorCounterexample`：在 **`Z := X`（确定性）** 时 positivity **必然**失效，
  且 `frontdoorFormula ≠ doLaw`（`1/2 ≠ 1`）。

本轮回答的问题是：

> **positivity 是不是「必要」的？换句话说，能不能再给出一个
> *不同的* 违反 positivity 的 SCM，其 front-door 公式仍然算错？**

## 本文件给出的答案（第二个反例）

### §1 数值事实（全部由 Lean 机器证出，不是手算）

SCM（`Z := X ∨ Uz`，即 **OR** 门，而非上轮的 AND / 恒等）：

```
U  ~ P(0)=1/5, P(1)=4/5   混杂源
Ux = Unit                 X 无噪声：X := U
X  = U
Uz ~ P(0)=1/10, P(1)=9/10  Z 噪声
Z  := X ∨ Uz   ← 注意是逻辑「或」
Uy = Unit
Y  := Z                    （确定性）
```

则（`x` 用 `false`/`true` 表示 0/1）：

| 量 | 值 |
|---|---|
| `p(X=0)` | `1/5` |
| `p(X=1)` | `4/5` |
| `p(x=0, z=0)` | `1/50` |
| `p(x=0, z=1)` | `9/50` |
| `p(x=1, z=0)` | **`0`** ← positivity 失效处 |
| `p(x=1, z=1)` | `4/5` |
| **`fd(x=0, y=0)`** | **`1/50`** |
| **`p(y=0 \| do(x=0))`** | **`1/10`** |

$$\boxed{\ \text{fd}(0,0)=\frac{1}{50}\ \ne\ \frac{1}{10}=p(y{=}0\mid do(x{=}0))\ }$$

### §2 与上轮 `Z := X` 反例的**结构对照**（诚实比较）

| | 上轮 `Z := X` | 本轮 `Z := X ∨ Uz` |
|---|---|---|
| `Z` 的方程 | `Z := X` | `Z := X ∨ Uz` |
| `Uz` | `Unit`（**无**噪声） | **二值**（有噪声，`1/10, 9/10`） |
| `p(x,z)=0` 的位置 | `(0,1)` **和** `(1,0)`（两格） | **只有** `(1,0)`（一格） |
| 失效的 `(x,y)` | `(0,0)`：`1/2 ≠ 1` | `(0,0)`：`1/50 ≠ 1/10` |
| 出错方向 | `fd` **偏小** | `fd` **偏小** |
| 偏差量 | `1/2` | `2/25` |

**⚠ 诚实说明（必须讲清）**：

1. **结构上确实不同**：`Z` 的方程由「恒等」变成「OR」，`Uz` 由 `Unit` 变成真噪声，
   零支撑格由两格变一格。所以**不是把上轮 SCM 换个名字**。
2. **但机制是同一个**：两者都因 **`p(x', z) = 0` 对某个 `(x',z)`**
   而使 front-door 的内层
   `∑_{x'} p(y|z,x')·p(x')` **丢掉 `x'` 的整块质量**，
   于是 `fd` 系统性偏小。**本文件的贡献是证明这个机制不是 `Z := X` 独有的**，
   而是任何「门窄」的 `Z` 都有的。**我没有找到「机制上根本不同」的第二种失效方式**，
   这一点也如实记录。
3. §2 再给出**均匀分布**的 OR 版本（零支撑同样只在 `(1,0)`），
   §3 的 AND 版本（零支撑在 `(0,1)`）作为镜像对照，
   让「零支撑位置」和「失效点」的对应关系一目了然。

### §3 与前置条件 (i)(ii)(iii) 的关系

本 SCM 满足 front-door 的**图条件**：
* (i) `Y` 不吃 `X`：`oY : Z → Bool → Unit → Bool` 的签名里没有 `X`；
* (ii) `Z` 不吃 `U`：`oZ : X → Bool → Z` 的签名里没有 `U`；
* (iii) 后门通路被 `Z` 挡住（本文件里 `Y := Z` 直接确定）。

**⟹ 图条件全满足、却仍然算错 ⟹ 图条件 + Pearl 公式还不够，positivity 不可省。**
-/

import FateWorld.Legacy.FrontdoorCounterexample

namespace Fate.R254

open Finset Fate.Frontdoor Fate.R253

/-! ## §0 记号说明

`Fate.R253`（`FrontdoorCounterexample.lean`）已给出：

* `ind P = if P then 1 else 0`（`ℝ` 值指示函数）；
* `joint pU pUx pUz pUy fX fZ fY x z y`
  `= ∑ u ux uz uy, pU u · pUx ux · pUz uz · pUy uy · [fX u ux = x ∧ fZ x uz = z ∧ fY z u uy = y]`；
* `margX`、`margXZ`、`doLaw`；
* `frontdoorFormula joint margXZ margX x y`
  `= ∑ z, margXZ x z / margX x · (∑ x', joint x' z y / margXZ x' z · margX x')`
  （**`0/0 ↦ 0`** 是 Lean 实数除法的默认行为：`div_zero` 给出 `x / 0 = 0`，
   不需要额外约定）。

**本文件的 SCM 全部取 `Ux = Uy = Unit`**（无 `X`/`Y` 噪声），
故 `pUx ≡ 1`、`pUy ≡ 1`，且 `Ux`、`Uy` 的求和只剩一项。
-/

/-! ## §1 主反例：`Z := X ∨ Uz`（OR 门） -/

section OrGate

/-- `X := U`（`Ux = Unit`，无噪声）。 -/
def oX : Bool → Unit → Bool := fun u _ => u

/-- ⭐ **`Z := X ∨ Uz`** —— 逻辑「或」。 -/
def oZ : Bool → Bool → Bool := fun x uz => x || uz

/-- `Y := Z`（确定）。**签名里没有 `X`** ⟹ 图条件 (i)。 -/
def oY : Bool → Bool → Unit → Bool := fun z _ _ => z

/-- 混杂源 `U ~ P(0)=1/5, P(1)=4/5`。 -/
noncomputable def opU : Bool → ℝ
  | false => 1 / 5
  | true => 4 / 5

/-- `Z` 的噪声：`P(Uz=0) = 1/10`，`P(Uz=1) = 9/10`。 -/
noncomputable def opUz : Bool → ℝ
  | false => 1 / 10
  | true => 9 / 10

/-- ⭐ `p(x)`。 -/
noncomputable def oMargX (x : Bool) : ℝ :=
  margX opU (fun _ => 1) oX x

/-- ⭐ `p(x,z)`。 -/
noncomputable def oMargXZ (x z : Bool) : ℝ :=
  margXZ opU (fun _ => 1) opUz oX oZ x z

/-- ⭐ `p(x,z,y)`。 -/
noncomputable def oJoint (x z y : Bool) : ℝ :=
  joint opU (fun _ => 1) opUz (fun _ => 1) oX oZ oY x z y

/-- ⭐ `p(y|do(x))`。 -/
noncomputable def oDo (x y : Bool) : ℝ :=
  doLaw opU opUz (fun _ => 1) oZ oY x y

/-! ### 1.1 精确数值 -/

theorem o_margX_false : oMargX false = 1 / 5 := by
  norm_num [oMargX, margX, oX, opU, ind, Fintype.sum_bool]

theorem o_margX_true : oMargX true = 4 / 5 := by
  norm_num [oMargX, margX, oX, opU, ind, Fintype.sum_bool]

theorem o_margXZ_f_f : oMargXZ false false = 1 / 50 := by
  norm_num [oMargXZ, margXZ, oX, oZ, opU, opUz, ind, Fintype.sum_bool]

theorem o_margXZ_f_t : oMargXZ false true = 9 / 50 := by
  norm_num [oMargXZ, margXZ, oX, oZ, opU, opUz, ind, Fintype.sum_bool]

/-- ⭐⭐ **positivity 失效处**：`p(x=1, z=0) = 0`（`Z := X ∨ Uz` 在 `X=1` 时恒为 `1`）。 -/
theorem o_margXZ_t_f : oMargXZ true false = 0 := by
  norm_num [oMargXZ, margXZ, oX, oZ, opU, opUz, ind, Fintype.sum_bool]

theorem o_margXZ_t_t : oMargXZ true true = 4 / 5 := by
  norm_num [oMargXZ, margXZ, oX, oZ, opU, opUz, ind, Fintype.sum_bool]

theorem o_joint_f_f_f : oJoint false false false = 1 / 50 := by
  norm_num [oJoint, joint, w, oX, oZ, oY, opU, opUz, ind, Fintype.sum_bool]

theorem o_joint_f_t_t : oJoint false true true = 9 / 50 := by
  norm_num [oJoint, joint, w, oX, oZ, oY, opU, opUz, ind, Fintype.sum_bool]

theorem o_joint_t_t_t : oJoint true true true = 4 / 5 := by
  norm_num [oJoint, joint, w, oX, oZ, oY, opU, opUz, ind, Fintype.sum_bool]

theorem o_do_f_f : oDo false false = 1 / 10 := by
  norm_num [oDo, doLaw, oZ, oY, opU, opUz, ind, Fintype.sum_bool]

theorem o_do_f_t : oDo false true = 9 / 10 := by
  norm_num [oDo, doLaw, oZ, oY, opU, opUz, ind, Fintype.sum_bool]

theorem o_do_t_f : oDo true false = 0 := by
  norm_num [oDo, doLaw, oZ, oY, opU, opUz, ind, Fintype.sum_bool]

theorem o_do_t_t : oDo true true = 1 := by
  norm_num [oDo, doLaw, oZ, oY, opU, opUz, ind, Fintype.sum_bool]

/-! ### 1.2 一致性核对 -/

/-- ⭐ `p(x,z)` 的 `x=1` 行加起来回到 `p(x=1) = 4/5`。 -/
theorem o_margXZ_row_one :
    oMargXZ true false + oMargXZ true true = 4 / 5 := by
  rw [o_margXZ_t_f, o_margXZ_t_t]; norm_num

/-- ⭐ `p(y|do(0))` 归一化。 -/
theorem o_do_f_sum : oDo false false + oDo false true = 1 := by
  rw [o_do_f_f, o_do_f_t]; norm_num

/-- ⭐ `p(x,z)` 全体加起来 = 1。 -/
theorem o_margXZ_total :
    oMargXZ false false + oMargXZ false true
      + oMargXZ true false + oMargXZ true true = 1 := by
  rw [o_margXZ_f_f, o_margXZ_f_t, o_margXZ_t_f, o_margXZ_t_t]; norm_num

/-! ### 1.3 ⭐⭐⭐ 主定理：OR 门 SCM 上 `fd ≠ doLaw` -/

/-- ⭐⭐⭐ **`fd_or_exact`**：`Z := X ∨ Uz` 上
$$\text{fd}(0,0)=\frac{1}{50}.$$
**注意它等于 `p(x=0,z=0)/p(x=0) · p(x=0) = 1/50`，
即 `z=0` 一枝只剩 `x'=0` 的贡献** —— `x'=1` 的整块质量被 `p(1,0)=0` 吞掉。 -/
theorem fd_or_exact :
    frontdoorFormula oJoint oMargXZ oMargX false false = 1 / 50 := by
  simp only [frontdoorFormula, Fintype.sum_bool]
  norm_num [oJoint, joint, w, oX, oZ, oY, oMargXZ, margXZ, oMargX, margX,
    opU, opUz, ind, Fintype.sum_bool]

/-- ⭐⭐⭐ **`fd_or_gate_fails_on_0_0`**：

$$\text{fd}(0,0)=\frac{1}{50}\ \ne\ \frac{1}{10}=p(y{=}0\mid do(x{=}0)).$$

**这是第二个（结构上不同于 `Z := X`）的 positivity 违反反例。** -/
theorem fd_or_gate_fails_on_0_0 :
    frontdoorFormula oJoint oMargXZ oMargX false false ≠ oDo false false := by
  rw [fd_or_exact, o_do_f_f]
  norm_num

/-- ⭐⭐⭐ 主定理：**`fd(0,0) = 1/50` 且 `p(y=0|do(0)) = 1/10`，两者不等。** -/
theorem fd_or_gate_exact_pair :
    frontdoorFormula oJoint oMargXZ oMargX false false = 1 / 50
      ∧ oDo false false = 1 / 10 := by
  exact ⟨fd_or_exact, o_do_f_f⟩

/-! ### 1.4 偏差的**来源**（可核算）

`frontdoorFormula` 在 `x=0, y=0` 处展开：

```
∑_z  p(x=0,z)/p(x=0) · ( ∑_{x'} p(y=0|z,x')·p(x') )
```

* `z = 0`：外层因子 `p(0,0)/p(0) = (1/50)/(1/5) = 1/10`；
  内层因 `p(x'=1, z=0) = 0` 而**只剩 `x'=0`**：
  `p(0,0,0)/p(0,0)·p(0) = 1·(1/5) = 1/5`；
  贡献 `(1/10)·(1/5) = 1/50`。
* `z = 1`：外层 `p(0,1)/p(0) = 9/10`；因 `y=0` 需要 `y=z`，
  故 `p(0,1,0)=0` 且 `p(1,1,0)=0` ⟹ 内层 `= 0`；贡献 `0`。
* 合计 `1/50`。

而真实 `p(y=0|do(0)) = P(Z=0 | do(X=0)) = P(Uz=0) = 1/10`。

**`z=0` 一枝的内层是 `1/5 = p(x=0)` 而不是 `1`：`x'=1` 的质量没了。
`Z := X` 反例里是「减半」，这里是「乘以 `p(x=0)`」——同一个机制的定量表现。** -/
theorem fd_or_z0_outer_factor :
    oMargXZ false false / oMargX false = 1 / 10 := by
  rw [o_margXZ_f_f, o_margX_false]; norm_num

end OrGate

/-! ## §2 对照 A：同一个 OR 门，改成**均匀**噪声（零支撑位置不变） -/

section OrGateUniform

/-- 均匀 `Uz`：`P(Uz=0) = P(Uz=1) = 1/2`。 -/
noncomputable def o2Uz : Bool → ℝ := fun _ => 1 / 2

/-- 均匀 `U ~ 1/2`。 -/
noncomputable def o2U : Bool → ℝ := fun _ => 1 / 2

noncomputable def o2MargX (x : Bool) : ℝ := margX o2U (fun _ => 1) oX x
noncomputable def o2MargXZ (x z : Bool) : ℝ :=
  margXZ o2U (fun _ => 1) o2Uz oX oZ x z
noncomputable def o2Joint (x z y : Bool) : ℝ :=
  joint o2U (fun _ => 1) o2Uz (fun _ => 1) oX oZ oY x z y
noncomputable def o2Do (x y : Bool) : ℝ :=
  doLaw o2U o2Uz (fun _ => 1) oZ oY x y

/-- ⭐ 零支撑位置**不变**（仍在 `(1,0)`）。 -/
theorem o2_margXZ_t_f : o2MargXZ true false = 0 := by
  norm_num [o2MargXZ, margXZ, oX, oZ, o2U, o2Uz, ind, Fintype.sum_bool]

theorem o2_do_f_f : o2Do false false = 1 / 2 := by
  norm_num [o2Do, doLaw, oZ, oY, o2U, o2Uz, ind, Fintype.sum_bool]

/-- ⭐ `fd(0,0) = 1/4`（均匀噪声版）。 -/
theorem fd_or_uniform_exact :
    frontdoorFormula o2Joint o2MargXZ o2MargX false false = 1 / 4 := by
  simp only [frontdoorFormula, Fintype.sum_bool]
  norm_num [o2Joint, joint, w, oX, oZ, oY, o2MargXZ, margXZ, o2MargX, margX,
    o2U, o2Uz, ind, Fintype.sum_bool]

/-- ⭐⭐ 均匀噪声版反例：`fd(0,0) = 1/4 ≠ 1/2 = do(0,0)`。
**失效与具体概率数值无关，只与「有零支撑格」有关。** -/
theorem fd_or_uniform_fails :
    frontdoorFormula o2Joint o2MargXZ o2MargX false false ≠ o2Do false false := by
  rw [fd_or_uniform_exact, o2_do_f_f]
  norm_num

end OrGateUniform

/-! ## §3 对照 B：`Z := X ∧ Uz`（AND 门，零支撑在 `(0,1)`）

  与 §1 的 OR 门**镜像对称**：`¬(X ∧ Uz) = ¬X ∨ ¬Uz`，
  所以 OR 与 AND 在「把 `X`/`Uz` 同时取反」下互换。
  **本节的数值不是新机制，只是 §1 的变量重命名**（见 §4 的诚实说明）。
  列出来是为了让「零支撑位置 ↔ 失效点」的对应关系完全显式。 -/

section AndGate

/-- ⭐ **`Z := X ∧ Uz`** —— 逻辑「与」。 -/
def aZ : Bool → Bool → Bool := fun x uz => x && uz

noncomputable def aMargX (x : Bool) : ℝ := margX o2U (fun _ => 1) oX x
noncomputable def aMargXZ (x z : Bool) : ℝ :=
  margXZ o2U (fun _ => 1) o2Uz oX aZ x z
noncomputable def aJoint (x z y : Bool) : ℝ :=
  joint o2U (fun _ => 1) o2Uz (fun _ => 1) oX aZ oY x z y
noncomputable def aDo (x y : Bool) : ℝ :=
  doLaw o2U o2Uz (fun _ => 1) aZ oY x y

/-- ⭐⭐ **positivity 失效处**：`p(x=0, z=1) = 0`（`Z := X ∧ Uz` 在 `X=0` 时恒为 `0`）。 -/
theorem a_margXZ_f_t : aMargXZ false true = 0 := by
  norm_num [aMargXZ, margXZ, oX, aZ, o2U, o2Uz, ind, Fintype.sum_bool]

theorem a_do_t_f : aDo true false = 1 / 2 := by
  norm_num [aDo, doLaw, aZ, oY, o2U, o2Uz, ind, Fintype.sum_bool]

theorem a_do_t_t : aDo true true = 1 / 2 := by
  norm_num [aDo, doLaw, aZ, oY, o2U, o2Uz, ind, Fintype.sum_bool]

/-- ⭐⭐ AND 门版：`fd(1,1) = 1/4`。 -/
theorem fd_and_gate_exact :
    frontdoorFormula aJoint aMargXZ aMargX true true = 1 / 4 := by
  simp only [frontdoorFormula, Fintype.sum_bool]
  norm_num [aJoint, joint, w, oX, aZ, oY, aMargXZ, margXZ, aMargX, margX,
    o2U, o2Uz, ind, Fintype.sum_bool]

/-- ⭐⭐ AND 门版反例：`fd(1,1) = 1/4 ≠ 1/2 = p(y=1|do(1))`。 -/
theorem fd_and_gate_fails :
    frontdoorFormula aJoint aMargXZ aMargX true true ≠ aDo true true := by
  rw [fd_and_gate_exact, a_do_t_t]
  norm_num

end AndGate

/-! ## §4 结论与诚实记录

### 4.1 本文件证明了什么

1. **`fd_or_gate_exact_pair`**（§1.3）：在 `Z := X ∨ Uz` 的 SCM 上，
   `frontdoorFormula(0,0) = 1/50` 而 `p(y=0|do(0)) = 1/10`。
   **positivity 在此失效（`p(1,0) = 0`）且公式确实算错。**
2. **`fd_or_uniform_fails`**（§2）：同一个 OR 门换成均匀噪声，
   零支撑位置不变（仍在 `(1,0)`），公式仍错（`1/4 ≠ 1/2`）。
   **说明失效与具体概率数值无关，只与「有零支撑格」有关。**
3. **`fd_and_gate_fails`**（§3）：AND 门（零支撑在 `(0,1)`）给出镜像的失效
   （`1/4 ≠ 1/2`，在 `x=1,y=1` 处）。

### 4.2 ⚠ 诚实的自我批评

1. **这三个 SCM 的失效机制是同一个。** 上轮的 `Z := X`、§1 的 `Z := X ∨ Uz`、
   §3 的 `Z := X ∧ Uz`，都是因为「`Z` 在某处被 `X` 完全决定」
   ⟹ 某个 `p(x',z) = 0` ⟹ `frontdoorFormula` 的内层
   `∑_{x'} p(y|z,x')·p(x')` 用 `0/0 ↦ 0` 丢掉整个 `x'` 分支的质量
   ⟹ 公式系统性偏小。
   **我没有找到「机制上不同」的第二种 positivity 失效方式**
   （比如 `fd` 偏**大**的例子）。
   **如实记录为未解决问题。**
2. **OR 与 AND 互为变量取反。** 若把 §3 的 `X ↦ ¬X`、`Uz ↦ ¬Uz`、`y ↦ ¬y`，
   得到的就是 §1 的 OR 门结构。所以 §1 和 §3 在**对称意义下是同一个反例**；
   §2 只是 §1 换数值。
   **唯一真正「新」的是：`Z := X ∨ Uz` 这个方程本身在上一轮里没出现过，
   且自由度（`Uz` 有噪声、只有一格零支撑）与 `Z := X` 不同。**
3. **`0/0 ↦ 0` 这个约定是 Lean 实数除法的默认行为**（`div_zero`），
   不是我们为凑出反例额外引入的。若改用 `fd(x,y) := ⊥`（未定义）或
   其它约定，反例的**具体数值**会变，但「positivity 失效 ⟹ 公式可能错」
   这一结论不受影响。

### 4.3 建议的下一步

* 若要**正面**回答「positivity 必要性」，可证：
  `positivity 成立 ∧ 图条件 ⟹ fd = doLaw`（R245 已证），
  以及 `¬positivity ⟹ ∃ SCM, fd ≠ doLaw`（本文件 + R246 已给三个实例）。
  两者合起来就是「positivity 是**必要且充分**（在图条件下）」。
  **但「⟹ ∃ SCM」这一支目前只是「举出实例」，不是全称定理**；
  要成为定理需要量化「哪些零模式必然导致失效」——这仍需工作。
-/

end Fate.R254
