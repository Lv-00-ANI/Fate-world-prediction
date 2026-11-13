import FateWorld.Legacy.SCMSemantics
import FateWorld.Legacy.DoCalculus
import FateWorld.Legacy.PearlHierarchy
import FateWorld.Legacy.T34DoPushforward
import FateWorld.Legacy.T35Confounding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! ===========================================================================
  `Fate/CausalRouteDo` —— **因果路线 A：直接用 do-calculus 语义定义干预律**
  （agent 交付，零 `sorry` / 零 `admit` / 零 `axiom`）

  ## 〇、先做盘点（**避免第 16 次追已死路线**）

  **任务书原假设**：「现有 do 算子已有代数律，但**没有把图连到概率**」——
  **这句话**需要逐项核验**，因为它是本路线的**立项前提**。
  逐项盘点结果（全部在本仓库中实名可查）：

  | 任务书的假设 | 实际状态 | 位置 |
  |---|---|---|
  | 「do 算子只有代数律」 | ⚠ **不准确**：`SCMSemantics.doLaw` 已把干预律定义成**显式 `Finset` 求和**（**不经过任何图**）| `Fate/SCMSemantics.lean` §68.2 |
  | 「没把图连到概率」 | ⚠ **部分已做**：`T34` 已证 `doLaw − condY = 混杂质量`、质量守恒、`L¹` 范数判据；`Rule1Genuine` 已把**结构条件** `NoiseReadsX` 接进数值层 | `Fate/T34DoPushforward.lean`、`Fate/Rule1Genuine.lean` |
  | 「dSep ⟹ CI 走不通」 | ✅ **已 machine-check 证伪**（`gap_false_in_general`），**本文件不碰** | `Fate/BridgeFullFixed.lean` |
  | 「`do` 与图的关系」 | ✅ **已证**：`graphOf(doMap M) = doInGraph(graphOf M)`（`T3.3`）| `Fate/T33DoGraph.lean` |

  **⟹ 盘点结论（决定了本路线**能做什么、不能做什么**）**：

  1. **「定义 doLaw 而不经过 dSep」这件事**，仓库里**已经做了** ——
     `SCMSemantics.doLaw` 就是**直接由结构方程算出**的干预律，
     **它的定义里没有图、没有 dSep、没有 Bayes-Ball**。
     **⟹ 本路线不是「补一个新定义」，而是把已有的 `doLaw` 放进 do-calculus 语义的框架里，
     证出它**确实满足 do-算子的应有性质** —— 这正是任务第 2、3、4 点的要求。**

  2. **本文件真正的增量**（相对 `SCMSemantics` / `T34` 的已有内容）：
     * **§2 `doLaw_is_law_after_do`**（⭐ **核心，非 `rfl`**）：
       证明「`doLaw` = 干预模型的**观测律在 `(x, y)` 处的读出**」——
       即 **`doX`（模型变换算子）与 `L1_obs`（观测读出）的复合恰好给出 `doLaw`**。
       **这是 do-calculus 语义的**闭环**：干预 → 新模型 → 新观测律 = `doLaw`。**
       **`SCMSemantics` 与 `T34` 都**没有**证这条闭环**（它们从 `doLaw` 的定义出发，
       没有把它接回 `DoCalculus.doX` 这个**模型变换算子**）。
     * **§3 `doLaw_stable_under_do`**（⭐）：**在 `doLaw` 层面，`do` 是"后写者胜"且幂等** ——
       **这是 `DoCalculus.do_idempotent` / `do_comp` 的**分布层对应物**。**
     * **§4 `L3_determines_doLaw`**（⭐⭐⭐，**非 `rfl`，真用 `push_push`**）：
       **反事实系统（L3）决定全部干预律（L2/`doLaw`）** ——
       **把 Pearl 三层级与 `doLaw` 接起来**，回答任务第 3 点。
     * **§5 层级分离的**归一化**版本**：在 `T35` 的完全混杂模型上，
       **`doLaw` 归一化后是均匀分布，`condY` 归一化后是点质量** ——
       **这是「观测 ≠ 干预」在**概率律**层的精确体现**，与 dSep 无关。

  ## 一、本文件的**假设清单**（任务第 3 点）

  `doLaw` 由结构方程直接算出，**不需要**：
  * **无环性**（`doLaw` 不读图，故不需要 DAG）；
  * **d-分离**（这正是本路线**绕开**的东西）；
  * **因果充分性 / 无隐变量**（`SCM X Y` 的 `U` 就是全部外生，本载体下无隐藏混杂，
    但 `doLaw` 的**定义**本身也不假设这一点 —— 它的定义只是「沿 `u ↦ f_u(x)` 的推前」）。

  `doLaw` **只需要**：
  * **一个结构方程族** `f_u : X → Y`（`SCM.sg` 的第二分量）；
  * **一个外生律** `pU`（干预**不改变** `pU` —— 这是 Pearl 的「干预只动结构不动外生」，见 `do_pU`）。

  ## 二、与 Pearl 三层级的对应（任务第 3 点）

  | 层 | Pearl | 本文件术语 | 关系（本文件所证）|
  |---|---|---|---|
  | **L1** | 观测律 `P(X,Y)` | `SCM.L1_obs` | **`doLaw` 是干预模型的 `L1` 读出**（§2 闭环）|
  | **L2** | 干预律 `P(Y|do(x))` | `SCMSemantics.doLaw` | **由 `L3` 唯一决定**（§4）|
  | **L3** | 反事实系统 | `SCM.L3_cf` | **决定 `L2`（§4）；`L1` 是 `L2` 沿 `x` 的进一步读出** |

  ## 三、诚实边界（**本文件不做什么**）

  * **不做**「`doLaw` 与 Pearl 图条件（`G_{\overline X}` 上的 d-分离）等价」——
    那需要 `W ≠ ∅` 与 Mathlib 的 `CondIndepFun` 嵌入，且**本载体没有 `W` 的位置**
    （`Rule1Genuine` §10 / `Rule2Genuine` §7.3 已登记同一局限）。
  * **不做**「`dSep ⟹ CI`」——`gap_false_in_general` 已证伪，**本文件不尝试**。
  * `doLaw` 的**质量守恒**与**范数判据**已在 `T34` 证过，**本文件引用而不重复**。
  =========================================================================== -/

namespace Fate

namespace CausalRouteDo

open PearlHierarchy

set_option autoImplicit false

universe u

/-! ===========================================================================
  §1 ⭐⭐⭐ 干预律 `doLaw` 的**语义定位**：它是「先做 do、再观测」的读出

  本节把 `SCMSemantics.doLaw` 与 `DoCalculus.doX`（模型变换算子）**接起来**。

  **⚠ 关键观察**（定义层面）：
  `SCMSemantics.doLaw M x y = ∑ u, pU u · [ (sg u).2 x = y ]`，
  而 `DoCalculus.doX M x` 把 `sg` 的第一分量换成常数 `x`，**第二分量不变**。
  **⟹ `doLaw` 只读到 `sg` 的第二分量**，因此**对「事实 `X` 的方程」不敏感** ——
  **这正是 do-算子的本质：干预无视 `X` 的实际取值。**
  =========================================================================== -/

/-- ⭐⭐ **`doLaw` 只是结构方程族的推前**（把定义整理成 `push` 形式，供 §4 使用）。

**⭐ 这不是新内容，而是把 `SCMSemantics.doLaw` 的显式求和式**
**对齐到 `PearlHierarchy.push`** —— 两者定义上相等（`rfl`）。 -/
theorem doLaw_eq_push {X Y : Type} [Fintype X] [DecidableEq Y]
    (M : SCM X Y) (x : X) :
    SCMSemantics.doLaw M x = push M.pU (fun u => (M.sg u).2 x) := by
  funext y
  rfl

/-! ===========================================================================
  §2 ⭐⭐⭐⭐ **核心闭环**：`doLaw` = 干预模型的观测律读出

  **陈述**：对干预后的模型 `doX M x`，其**观测律**在 `(x, y)` 处的值
  **恰好等于** `doLaw M x y`。

  $$\bigl(\mathrm{doX}(M, x)\bigr).\mathrm{L1\_obs}\,(x, y) \;=\; \mathrm{doLaw}\,M\,x\,y$$

  **⭐⭐ 这条把三样东西接成一个交换图**：

  ```
        M  ──── doX x ────►  doX M x
        │                      │
        │ doLaw x              │ L1_obs
        ▼                      ▼
   P(Y|do(x))  ════════  观测律在 (x, y) 处
  ```

  **⟹ 语义上**：「干预 `do(X:=x)`」≡「把 `X` 的方程换成常数 `x`，再看新模型的观测律」——
  **这正是 do-calculus 的**操作语义**，而它**完全不经过图**。**

  **⚠ 这**不是 `rfl`**：`L1_obs` 用 `push`（沿 `u ↦ (x_u, f_u(x_u))`），
  `doLaw` 用显式 `Finset` 求和，需要对齐两边并**消掉「`X` 分量 = `x`」的过滤因子**。 -/
theorem doLaw_is_law_after_do {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (M : SCM X Y) (x : X) (y : Y) :
    (DoCalculus.doX M x).L1_obs (x, y) = SCMSemantics.doLaw M x y := by
  unfold SCM.L1_obs SCMSemantics.doLaw DoCalculus.doX push
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : (M.sg u).2 x = y
  · simp [h]
  · simp [h]

/-- ⭐⭐⭐⭐ **闭环的**一般形式**（任意观测读数 `(x', y)`）。**

**陈述**：干预模型的观测律，在**任意** `(x', y)` 处：
$$\bigl(\mathrm{doX}(M, x)\bigr).\mathrm{L1\_obs}\,(x', y)
  = [x' = x] \cdot \mathrm{doLaw}\,M\,x\,y.$$

**⭐ 读法**：干预后 `X` 是**点质量** `δ_x`（第一分量为常数 `x`），
故除 `x' = x` 外观测律**全为零**；在 `x' = x` 处即 `doLaw`。
**⟹ 这刻画了整个 `L1` 读出，而不只是对角线。** -/
theorem doLaw_is_law_after_do_general {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (M : SCM X Y) (x x' : X) (y : Y) :
    (DoCalculus.doX M x).L1_obs (x', y)
      = (if x' = x then SCMSemantics.doLaw M x y else 0) := by
  unfold SCM.L1_obs SCMSemantics.doLaw DoCalculus.doX push
  by_cases hx : x' = x
  · rw [if_pos hx, hx]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : (M.sg u).2 x = y
    · simp [h]
    · simp [h]
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro u _
    have hne : ((x, (M.sg u).2 x) : X × Y) ≠ (x', y) := by
      intro h; exact hx (congrArg Prod.fst h).symm
    simp [hne]

/-! ===========================================================================
  §3 ⭐⭐⭐ 分布层的 do 代数律：`do` 对 `doLaw` 的作用

  **任务对应**：`DoCalculus` 只有**模型层**的 `do_idempotent` / `do_comp`，
  **本节给出它们的**分布层对应物**：
  在 `doLaw` 上，再套一层 `do` **不改变干预律**。

  **⭐⭐ 意义**：**「干预的干预 = 干预」在**概率律**上成立** ——
  这是 do-calculus 第一、二条规则共同的**语义地基**（那两条规则的操作都是
  「在 `do(x)` 已经发生的前提下再加/减条件」）。
  =========================================================================== -/

/-- ⭐⭐⭐ **分布层幂等性**：`doLaw` 对**干预后的模型**等同原模型。

$$\mathrm{doLaw}\bigl(\mathrm{doX}(M, x)\bigr)\,x' \;=\; \mathrm{doLaw}\,M\,x'$$

**⭐ 读法**：干预只改 `sg` 的第一分量，而 `doLaw` **只读第二分量** ⟹
**在 `doLaw` 上再 `do` 一次是恒等**。

**⚠ 与 `DoCalculus.do_idempotent` 的关系**：
后者是**模型等式** `doX(doX M x) x = doX M x`；
**本条是它沿 `doLaw` 读出的推论**（故**在律层面幂等**），
但**本条的证明不经过 `do_idempotent`** —— 它直接看 `doLaw` 的依赖集，
**这也说明「律层幂等」比「模型层幂等」**更强**：对**任意** `x'` 都成立。** -/
theorem doLaw_stable_under_do {X Y : Type} [Fintype X] [DecidableEq Y]
    (M : SCM X Y) (x x' : X) :
    SCMSemantics.doLaw (DoCalculus.doX M x) x' = SCMSemantics.doLaw M x' := by
  funext y
  rfl

/-- ⭐⭐ **分布层"后写者胜"**：连续两次干预，律只看**最后一次**。

$$\mathrm{doLaw}\bigl(\mathrm{doX}(\mathrm{doX}(M, x), x')\bigr)\,x''
  \;=\; \mathrm{doLaw}\,M\,x''$$

**⭐ 这是 `do_comp` 的分布层对应物。** -/
theorem doLaw_comp {X Y : Type} [Fintype X] [DecidableEq Y]
    (M : SCM X Y) (x x' x'' : X) :
    SCMSemantics.doLaw (DoCalculus.doX (DoCalculus.doX M x) x') x''
      = SCMSemantics.doLaw M x'' := by
  funext y
  rfl

/-- ⭐⭐ **干预不改变外生律**（分布层重述 `DoCalculus.do_pU`）：
`doLaw` 的总质量由 `pU` 决定，`do` 不动 `pU`，故**总质量守恒**。

**⚠ 本条的**数值内容**（`∑ y, doLaw M x y = ∑ u, pU u`）已在
`T34.doLaw_mass` 证明，**本文件引用不重复**；
此处只重述「`do` 不动 `pU`」这一**前提在律层的可读形式**。 -/
theorem doLaw_pU_preserved {X Y : Type} [Fintype X] [DecidableEq Y]
    (M : SCM X Y) (x : X) :
    (DoCalculus.doX M x).pU = M.pU :=
  DoCalculus.do_pU M x

/-! ===========================================================================
  §4 ⭐⭐⭐⭐ **层级对应**：反事实系统（L3）决定一切干预律（L2 = `doLaw`）

  **任务第 3 点**：把 `doLaw` 放进 Pearl 三层级。

  **陈述**：若两个 SCM 有**相同的反事实系统**，则它们的**每一个** `doLaw` 相同。

  $$\mathrm{L3}(M_1) = \mathrm{L3}(M_2) \;\Longrightarrow\;
    \forall x,\ \mathrm{doLaw}\,M_1\,x = \mathrm{doLaw}\,M_2\,x.$$

  **⭐⭐ 证明思路**：`doLaw` 是**推前的推前** ——
  `L3_cf` 是 `pU` 沿 `u ↦ (x_u, f_u)` 的推前，
  `doLaw` 是 `pU` 沿 `u ↦ f_u(x)` 的推前，
  而 `u ↦ f_u(x)` = `(u ↦ (x_u, f_u))` 再 `(x, f) ↦ f x`。
  **⟹ 由 `push_push`（推前复合律），`doLaw` 是 `L3_cf` 的推前**，
  **故 `L3_cf` 相等 ⟹ `doLaw` 相等。**

  **⚠ 这**不是 `rfl`**：需要 `push_push` 的复合律对齐两个不同层次的推前。** -/
theorem L3_determines_doLaw {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [DecidableEq (X → Y)]
    (M N : SCM X Y) (h : M.L3_cf = N.L3_cf) :
    SCMSemantics.doLaw M = SCMSemantics.doLaw N := by
  funext x y
  have key : ∀ M : SCM X Y,
      SCMSemantics.doLaw M x = push M.L3_cf (fun p : X × (X → Y) => p.2 x) := by
    intro M
    rw [doLaw_eq_push, SCM.L3_cf]
    exact (push_push M.pU (fun u => ((M.sg u).1, (M.sg u).2))
        (fun p : X × (X → Y) => p.2 x)).symm
  rw [key M, key N, h]

/-- ⭐⭐⭐ **L3 ⟹ L2 ⟹ L1 全链**（把 `PearlHierarchy` 的
`L3_determines_L2` / `L3_determines_L1` 与 `doLaw` 串起来）。

**陈述**：`L3_cf` 相等的两个 SCM，其**观测律** `L1_obs` **与全部干预律 `doLaw` 都相等**。

**⭐ 这条把本文件的 `doLaw` 与 `PearlHierarchy` 已有的层间蕴含
（`L3_determines_L2`、`L3_determines_L1`）**组合成一个统一陈述**，
**并说明 `doLaw` 就是 `L2_do` 在同一载体上的**另一写法**（数值上逐点相等，见 §4.3）。** -/
theorem L3_determines_L1_and_doLaw {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [DecidableEq (X → Y)]
    (M N : SCM X Y) (h : M.L3_cf = N.L3_cf) :
    M.L1_obs = N.L1_obs ∧ SCMSemantics.doLaw M = SCMSemantics.doLaw N :=
  ⟨PearlHierarchy.L3_determines_L1 h, L3_determines_doLaw M N h⟩

/-- ⭐⭐ **`doLaw` 与 `PearlHierarchy.L2_do` 逐点一致**（同一干预律的两种写法）。

**⭐ 读法**：`SCMSemantics.doLaw` 是**显式求和**形式，
`SCM.L2_do` 是**`push` 推前**形式，**二者定义上相等**。
**⟹ 本文件的 `doLaw` 就是 Pearl 层级表里的 L2。** -/
theorem doLaw_eq_L2_do {X Y : Type} [Fintype X] [DecidableEq Y]
    (M : SCM X Y) (x : X) :
    SCMSemantics.doLaw M x = M.L2_do x := by
  funext y
  rfl

/-! ===========================================================================
  §5 ⭐⭐⭐⭐ **层级分离的归一化版本**（不经过 dSep）

  任务第 3 点要求把 `doLaw` 与三层级对应。**最直接的一层是「观测 ≠ 干预」** ——
  **本文件在**概率律（归一化）层面**给出它的精确见证**，
  用的正是 `T35` 的完全混杂模型（不引入任何新构造，**避免重复 15 轮的错误**）。

  **⚠ 之所以要归一化版**：`condY` 与 `doLaw` 都是**联合质量**，
  直接相减的比较会被 `marginalX` 因子干扰（这是 `T34` §4 已经处理过的）。
  **本节把两者**都除以各自的质量**，得到**真正的条件概率**再比较。**
  =========================================================================== -/

/-- ⭐⭐ **归一化的干预律** `P(Y = y | do(x))`。

$$\mathrm{doProb}\,M\,x\,y := \frac{\mathrm{doLaw}\,M\,x\,y}{\sum_{y'} \mathrm{doLaw}\,M\,x\,y'}$$

**⚠ 分母 `∑_{y'} doLaw M x y' = ∑_u pU u`**，与 `x` 无关（`T34.doLaw_mass`）。 -/
noncomputable def doProb {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    (M : SCM X Y) (x : X) (y : Y) : ℝ :=
  SCMSemantics.doLaw M x y / ∑ y', SCMSemantics.doLaw M x y'

/-- ⭐⭐ **归一化的观测律** `P(Y = y | X = x)`。

$$\mathrm{obsProb}\,M\,x\,y := \frac{\mathrm{condY}\,M\,x\,y}{\sum_{y'} \mathrm{condY}\,M\,x\,y'}$$

**⚠ 分母 `∑_{y'} condY M x y' = marginalX M x = P(X = x)`**（`T34.condY_mass`）。 -/
noncomputable def obsProb {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (M : SCM X Y) (x : X) (y : Y) : ℝ :=
  SCMSemantics.condY M x y / ∑ y', SCMSemantics.condY M x y'

/-- ⭐⭐⭐⭐ **层级分离（归一化见证）**：在 `T35` 完全混杂模型上，
**观测律与干预律作为概率律不相等**（且给出具体数值）。

**陈述**：
* `doProb M 0 1 = 1/2`（干预下 `Y` 仍随机：`1/2`）；
* `obsProb M 0 1 = 0`（观测到 `X = 0` 后 `Y` 必为 `0`，故 `Y = 1` 概率 `0`）；
* **`1/2 ≠ 0`** ⟹ **`P(Y|do(x)) ≠ P(Y|X=x)`**。

**⭐ 读法**：**干预无视 `X` 的实际取值**（外生 `U` 仍在动），
**观测被 `X = x` 筛死**（`Y` 被 `X` 完全决定）。
**这正是「因果层级分离」—— 与 d-分离无关，是 `doLaw` 定义的直接数值后果。** -/
theorem layer_separation_normalized :
    doProb Fate.T35.M 0 1 = (1 : ℝ) / 2
    ∧ obsProb Fate.T35.M 0 1 = 0
    ∧ doProb Fate.T35.M 0 1 ≠ obsProb Fate.T35.M 0 1 := by
  have hdoMass : ∑ y' : Fin 2, SCMSemantics.doLaw Fate.T35.M (0 : Fin 2) y' = 1 := by
    rw [Fin.sum_univ_two]
    rw [Fate.T35.doLaw_M, Fate.T35.doLaw_M]
    norm_num
  have hobsMass : ∑ y' : Fin 2, SCMSemantics.condY Fate.T35.M (0 : Fin 2) y' = (1 : ℝ) / 2 := by
    rw [Fin.sum_univ_two]
    -- condY_M 0 0 = 1/2 (since x = y), condY_M 0 1 = 0
    have h00 : SCMSemantics.condY Fate.T35.M (0 : Fin 2) (0 : Fin 2) = 1 / 2 := by
      rw [Fate.T35.condY_M]; simp
    have h01 : SCMSemantics.condY Fate.T35.M (0 : Fin 2) (1 : Fin 2) = 0 := by
      rw [Fate.T35.condY_M]; norm_num
    rw [h00, h01]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · unfold doProb
    rw [hdoMass, Fate.T35.doLaw_M]
    norm_num
  · unfold obsProb
    rw [hobsMass]
    have h01 : SCMSemantics.condY Fate.T35.M (0 : Fin 2) (1 : Fin 2) = 0 := by
      rw [Fate.T35.condY_M]; norm_num
    rw [h01]; norm_num
  · intro h
    have h1 : doProb Fate.T35.M 0 1 = (1 : ℝ) / 2 := by
      unfold doProb; rw [hdoMass, Fate.T35.doLaw_M]; norm_num
    have h2 : obsProb Fate.T35.M 0 1 = 0 := by
      unfold obsProb; rw [hobsMass]
      have h01 : SCMSemantics.condY Fate.T35.M (0 : Fin 2) (1 : Fin 2) = 0 := by
        rw [Fate.T35.condY_M]; norm_num
      rw [h01]; norm_num
    rw [h1, h2] at h
    norm_num at h

/-! ===========================================================================
  §6 ⭐⭐⭐ **汇总**：路线 A 的**结论清单**

  | # | 结论 | 定理 |
  |---|---|---|
  | 1 | **`doLaw` 定义不经过图/dSep**（盘点 + `doLaw_eq_push`）| `doLaw_eq_push` |
  | 2 | **`doLaw` = 干预模型的观测律读出**（⭐ 闭环，非 `rfl`）| `doLaw_is_law_after_do` |
  | 3 | **闭环的一般（非对角）形式** | `doLaw_is_law_after_do_general` |
  | 4 | **分布层幂等**（`do` 对 `doLaw` 是恒等）| `doLaw_stable_under_do` |
  | 5 | **分布层后写者胜** | `doLaw_comp` |
  | 6 | **`do` 不动外生律**（律层读出）| `doLaw_pU_preserved` |
  | 7 | ⭐ **L3（反事实）决定全部 `doLaw`**（层级对应）| `L3_determines_doLaw` |
  | 8 | **L3 ⟹ L1 ∧ doLaw 统一陈述** | `L3_determines_L1_and_doLaw` |
  | 9 | **`doLaw` = Pearl 层级的 `L2_do`** | `doLaw_eq_L2_do` |
  | 10 | ⭐⭐⭐ **层级分离（归一化概率律见证）** | `layer_separation_normalized` |

  **⭐⭐ 路线 A 的**判定**（如实）**：

  * **「能否直接定义 doLaw 而不经过 dSep？」** —— **能，且仓库已做过了**
    （`SCMSemantics.doLaw`）。**本文件的贡献不是重造它，而是证明它满足 do-calculus 语义的
    闭环（§2）、分布层代数律（§3）、与三层级的对应（§4–§5）。**
  * **「需要什么假设？」** —— **只需结构方程族 `f_u` 与外生律 `pU`**（§1 末）；
    **不需要无环性、不需要 d-分离、不需要无隐变量。**
  * **「与三层级如何对应？」** —— **见图表**：`doLaw` 就是 L2，
    **L3 唯一决定它（§4 `L3_determines_doLaw`），干预后的 L1 恰好是 `doLaw` 的读出（§2）**。
  * **「能否绕开 dSep？」** —— **本文件的所有定理都不引用 `DSeparation` / `BridgeFullFixed`**，
    **`doLaw` 的每个性质都从结构方程直接算出** —— **这正是路线 A 的可行性证据。**
  =========================================================================== -/

end CausalRouteDo

end Fate
