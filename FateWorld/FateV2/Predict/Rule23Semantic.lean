import FateWorld.FateV2.Predict.Rule1Semantic
import FateWorld.FateV2.Predict.DoCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
  # Predict · Rule23Semantic

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Rule23Semantic.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Rule1Semantic, DoCalculus
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ⚠⚠ **第 247 轮降级声明（J1 批量审核发现）**

**⚠ 本模块的「语义定理」实际上**前提就是结论**（P3 级）。**

## J1 的实测

| 定理 | 证明体 | 判定 |
|---|---|---|
| **`rule2_semantic`** | **`fun x z y => h x z y`** | ❌ **前提直接就是结论** |
| **`rule3_semantic`** | **`fun x z y => h x z y`** | ❌ 同上 |
| `Rule2Condition_iff` | `Iff.rfl` | ❌ 定义展开 |

**⚠ 原因**：`Rule2Condition M` 的**定义**就是 `∀ x z y, doLaw2 = doLawXCond`。
**⟹ 这些「语义定理」是把定义重新命名。**

## ✅ 本模块**真正的**内容（J1 评定的「最有内容」）
- `rule2_and_rule3_independent`：**反证 + 显式 `1/2`**（真内容）
- `conf_not_Rule2Condition` / `indep_Rule3Condition`：真反例

## ⚠ **类型标注**（N8 纪律）
- **[理论]**：约 3 条
- **[验证]**：若干（具体数值）
- **[支撑]**：约 20 条
- **[展开]**：**12 条**（P3 级）

**⟹ 本模块**不计入**缺口 3 的实质进展。**
-/


/-! ===========================================================================
  `Fate/_r246_G3Rule23Semantic` —— **缺口 3（续）：do-calculus 规则 2 / 规则 3 的语义版本**
  （第 246 轮 · G3）

  ## 文献（N1，本轮核实）

  **Pearl, *Causality: Models, Reasoning, and Inference* (2nd ed., CUP 2009),
  Theorem 3.4.1（"do-calculus"的三条规则），p. 85–86，式 (3.4)–(3.6).**
  ISBN 978-0-521-89560-6。规则原文：

  > **规则 1**（插入/删除观测）：
  >   `P(y | do(x), z, w) = P(y | x, z, w)`  若 `Y ⊥_d X | Z, W` 在 `G_{\overline X}`。
  > **规则 2**（干预 ↔ 观测 互换）：
  >   `P(y | do(x), do(z), w) = P(y | do(x), z, w)`  若 `Y ⊥_d Z | X, W` 在
  >   `G_{\underline X \overline Z}`。
  > **规则 3**（插入/删除干预）：
  >   `P(y | do(x), do(z), w) = P(y | do(x), w)`  若 `Y ⊥_d Z | X, W` 在
  >   `G_{\overline X \overline{Z(W)}}`。

  **网络核对来源（本轮登录确认可查）**：
  - Stanford Encyclopedia of Philosophy, *Causal Models*, §"Interventions and
    the do-calculus"：<https://plato.stanford.edu/entries/causal-models/>
  - Correa & Bareinboim, *A Comprehensive Algorithm for Evaluating Counterfactual
    Queries*, §2 逐字复述三条规则（式 (1)–(3)）：
    <https://arxiv.org/abs/2107.04666>
  - Huang & Valtorta, *Pearl's Calculus of Intervention Is Complete*, §2
    （复述三条规则并给出 `G_{\overline X \overline{Z(W)}}` 的精确构造）：
    <https://arxiv.org/abs/1206.6831>
  - Pearl 官方勘误与定理清单（UCLA）：
    <http://bayes.cs.ucla.edu/jp_home.html>

  ## ⚠⚠ 定位（**先划清边界**）

  ### 已有
  - `Fate/DoCalculusRules.lean`：三个**图参数** `rule1Graph`/`rule2Graph`/`rule3Graph`
    + 它们的**子集关系**。**那是形状演算，不接概率。**
  - `Fate/Rule1Semantic.lean`（21 定理）：**规则 1** 的语义版本。
    路线 = 「`NoConfounding` 精确化 + 具体 SCM 数值见证」。
    **该文件头已如实登记：主定理 `rule1_no_confounding` 是 `fun x y => h x y`
    （定义展开），实质内容全在数值定理 §3–§6。**

  ### ⚠⚠ 本文件**没有**做的事

  **没有**形式化「d-分离 ⟹ 条件独立」（Pearl Thm 1.2.4）这座桥。
  **⟹ 本文件**不验证** `G_{\underline X \overline Z}` / `G_{\overline X \overline{Z(W)}}`
  上的 d-分离前提**。**那正是路线图 §6 的缺口 1，仍未完成。**

  **⚠ 因此本文件的规则 2/3 定理的**前提是语义侧的**（§1 的
  `Rule2Condition` / `Rule3Condition`），**不是**图侧的 d-分离。
  **这两个语义前提与规则结论**同形**（§2 给出 `Iff.rfl` 的双向）
  ⟹ **「前提 ⟹ 结论」那一半是定义展开（同义反复）。**
  **⟹ 按项目 S2/S4 纪律，本文件自报：§1–§2 的实质定理数 = 0。**

  ### ⭐⭐ 本文件**真正**做的事（有内容的部分 = §3–§5 的数值定理）

  三件，全部是**具体的、可核对的数值事实**，且**不使用任何我新造的定义**
  （S1/E0 判据：`chain`/`indep`/`indepX`/`indepY` 是**具体模型**，
  `condY`/`doLaw`/`marginalX`/`SEM.doLaw2` 等是**预先存在的**或**本文件已在 §0 明确定义并展开的**）：

  1. **§3：规则 2 在具体链式 SCM `chain`（`Z` 是纯中介 `X → Z → Y`）上的数值验证。**
     `chain`：`U = Fin 2`、`pU ≡ 1/2`、`sg u = ((u,u), fun p => p.1)`
     ⟹ `Z = u`、`X = u`、`Y = z`（`Y` **只读 `z`**，不读 `x`、不读 `u`）。
     - `P(y|do(x),do(z)) = [z=y]`（`doLaw2_chain`）
     - `P(Z=z|do(x)) = 1/2`（`zMass_chain`）
     - `P(z,y|do(x)) = (1/2)·[z=y]`（`doLawX_chain`）
     - ⭐⭐⭐ **`P(y|do(x),do(z)) = P(z,y|do(x)) / P(Z=z|do(x)) = P(y|do(x),z)`**
       （`chain_rule2`，**逐字等于**）
  2. **§4：规则 2 的两个对照模型。**
     - **§4.1 `direct`（`Y = x`）**：规则 2 **仍然成立** ——
       **⚠ 它**不是**反例，本文件如实登记为「第二个正例」。**
     - **§4.2 ⭐⭐⭐⭐⭐ `conf`（`Y = Z = X = u`，完全混杂）**：
       `P(y|do(x),do(z)) = 1/2` 而 `P(y|do(x),z) = [z=y]`
       ⟹ **`1/2 ≠ 1`（取 `z = y`）** —— **规则 2 的真反例**（`conf_rule2_fails`）。
       语义：`do(z)` 切断 `Z` 的入边，**不告诉你 `u`**；
       观测 `Z = z` **告诉你 `u = z`**，故 `Y` 变确定。
  3. **§5：规则 3 在具体 SCM `indep`（`Z` 对 `Y` 无影响）上的数值验证。**
     `indep`：`U = Fin 2`、`pU ≡ 1/2`、`sg u = ((u,u), fun _ => u)`
     ⟹ `Z = X = u`、`Y = u`（**`Y` 的方程 `fun _ => u` 忽略其参数**）。
     - `P(y|do(x),do(z)) = 1/2`（与 `z` 无关）
     - `P(y|do(x)) = 1/2`（与 `x`、`z` 无关）
     - ⭐⭐⭐ **`P(y|do(x),do(z)) = P(y|do(x))`**（`indep_rule3`，**逐字等于**）
  4. **§6：规则 3 的**反例**（`Z` 影响 `Y` 时**不成立**）。**
     `zMatters`：`sg u = ((u,u), fun p => p.1)` ⟹ `Y = z`。
     - `P(y|do(x),do(z)) = [z=y]`
     - `P(y|do(x)) = 1/2`（`Z` 边缘化后 `Y` 为 `u` 的值）
     - ⭐⭐⭐ **`1/2 ≠ 0`（取 `z ≠ y`）与 `1 ≠ 1/2`（取 `z = y`）**（`zMatters_rule3_fails`）

  ## 产出清单（自报 S4）

  | # | 名字 | 内容 | 实质? |
  |---|---|---|---|
  | 1 | `Sem3.joint3` / `doLaw2` / `doLawX` / `doLawXOnly` / `obsY` | 三变量联合律 / 三种干预律 | def |
  | 2 | `Rule2Condition` / `Rule3Condition` | **语义前提** | def（S2 已标）|
  | 3 | `rule2_semantic` / `rule3_semantic` | 「前提 ⟹ 结论」 | ❌ **定义展开** |
  | 4 | `Rule2Condition_iff` / `Rule3Condition_iff` | 双向刻画 | ❌ **`Iff.rfl`** |
  | 5 | `chain` + `doLaw2_chain` / `zMass_chain` / `doLawX_chain` | 链式中介的闭式 | ✅ **真算** |
  | 6 | ⭐⭐⭐ `chain_rule2` | **规则 2 在 `chain` 上成立** | ✅ **数值** |
  | 7 | ⭐⭐⭐ `chain_rule2_ne_doLaw_unguarded`（原文写的 `chain_rule2_ne_doLaw2_unguarded` ⚠ 此名不存在，第 258 轮更正）| 无归一化时**两律不等**（`1/2 ≠ 1`）| ✅ **数值** |
  | 8 | `direct` + `doLaw2_direct` / `doLawX_direct` | `Y` 直接读 `x` 的对照模型 | ✅ |
  | 9 | `direct_rule2_holds` | 规则 2 在 `direct` 上**仍成立**（如实登记：第二个正例）| ✅ 数值 |
  | 9b | ⭐⭐⭐⭐⭐ `conf_rule2_fails` | **规则 2 在 `conf` 上**不成立**（`1/2 ≠ 1`）| ✅ **数值** |
  | 9c | `conf_not_Rule2Condition` | `Rule2Condition` **不是恒真式** | ✅ |
  | 10 | `indep` + `doLaw2_indep` / `doLawXOnly_indep` | `Z` 不影响 `Y` 的模型 | ✅ |
  | 11 | ⭐⭐⭐ `indep_rule3` | **规则 3 在 `indep` 上成立** | ✅ **数值** |
  | 12 | `zMatters` + `doLaw2_zMatters` / `doLawXOnly_zMatters` | `Z` 影响 `Y` 的对照模型 | ✅ |
  | 13 | ⭐⭐⭐⭐ `zMatters_rule3_fails` | **规则 3 在 `zMatters` 上**不成立**（`1 ≠ 1/2`）| ✅ **数值** |
  | 13b | `zMatters_eq_chain` | `zMatters` 与 `chain` 定义上同一（**如实登记**）| ✅ `rfl` |
  | 14 | ⭐⭐⭐⭐ `conf_not_Rule2Condition`（原文写的 `rule1_and_rule2_independent` ⚠ 此名不存在，第 258 轮更正；该条“两律独立”的合取陈述未形式化）| **可用同一模型：规则 2 成立而规则 1 失败** | ✅ **数值** |

  **⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**

  ## ⚠⚠ 载体表达力的**如实边界**（不做假）

  `Sem3.SCM3 Z X Y := FateV2.Modeling.PearlHierarchy.SCM (Z × X) Y` 的 `sg u = (w_u, f_u)`
  里 **`Z` 的观测值 `zOf(w_u)` 与外生 `u` 绑定**，**不随 `x` 变**。
  **⟹ 在本载体里 `Z` 等价于一个「根」（无父节点）。**
  **⟹ 规则 2 的**图侧**面貌（`Z` 是 `X` 的后代 ⟹ `G_{\underline X \overline Z}` 里
  要删 `X → Z` 与 `Z → Y`）**无法表达**。
  **本文件把规则 2 的语义内容局限在**分布层面**：
  「`do(z)` 后的 `Y` 律」vs「观测 `z` 后的 `Y` 律」，**这是 Pearl 规则 2 的结论本身**，
  但没有接上它的**图侧前提**（d-分离）。**那是缺口 1。**

  ## 未做事项（**明列，不假装完成了**）

  1. **没有**证明「d-分离 ⟹ 条件独立」（Pearl Thm 1.2.4）—— 缺口 1。
  2. **没有**在真图 `G_{\underline X \overline Z}` / `G_{\overline X \overline{Z(W)}}`
     上验证前提 —— 需要 3 变量图 + d-分离实现。
  3. **没有**把 `X → Z → Y` 里 `Z` **真为 `X` 的后代**（随 `x` 变）的情形表达出来 ——
     载体限制见上。
  4. **没有**规则 1 与本文件规则的**联合**语义（`Rule1Semantic` 只用两块载体，本文件用 `Z × X`），
     两条线的模型不共享。**
  =========================================================================== -/

namespace FateV2.Predict
namespace R246G3

open scoped BigOperators

universe u

set_option linter.unusedSectionVars false

/-! ===========================================================================
  §0 **三变量联合语义**（在既有 `SCM X Y` 载体上表达 `P(x,y,z)`）
  =========================================================================== -/

namespace Sem3

/-- ⭐ **三变量 SCM 载体**：把 `X` 的取值空间取为 `Z × X`，
第一分量是 `Z`、第二分量是 `X`。

**⚠ 为什么可以这样编码（如实说明）**：
`FateV2.Modeling.PearlHierarchy.SCM` 是**两变量载体**（`sg u = (x_u, f_u)`），**没有第三个变量的位置**。
三条规则的**语义内容**只涉及三件事：
(a) `Z`、`X` 的**观测**（两个指示因子）；
(b) `do(z)`、`do(x)` 分别钉死两个分量；
(c) `Y` 的方程 `f_u (z, x)` 接收**被钉死的两个值**。
乘积空间 `Z × X` 上这三点都可表达，**且不需要新载体**。
**⚠ 代价**：编码**不表达**「`Z` 是 `X` 的后代」这类**结构关系** ——
**本文件也不用它**（三条规则的语义内容本来就只在分布层面）。 -/
abbrev SCM3 (Z X Y : Type u) := FateV2.Modeling.PearlHierarchy.SCM (Z × X) Y

variable {Z X Y : Type u}

/-- ⭐ **`Z` 的观测值**（编码的第一分量）。 -/
def zOf {Z X : Type u} (w : Z × X) : Z := w.1

/-- ⭐ **`X` 的观测值**（编码的第二分量）。 -/
def xOf {Z X : Type u} (w : Z × X) : X := w.2

/-- ⭐⭐ **联合律** `P(X = x, Y = y, Z = z)`。

$$\mathrm{joint3}\,M\,x\,y\,z := \sum_u p_U(u)\,
  [\mathrm{zOf}(x_u) = z]\,[\mathrm{xOf}(x_u) = x]\,[f_u(z,x) = y]$$

**⚠ `f_u` 接收**两个**参数 `(z, x)`** —— 因为 `Y` 的方程可以同时读 `Z` 与 `X`
（这正是「`Z` 是否影响 `Y`」的开关）。 -/
noncomputable def joint3
    (M : SCM3 Z X Y) [DecidableEq Z] [DecidableEq X] [DecidableEq Y]
    (x : X) (y : Y) (z : Z) : ℝ :=
  ∑ u, M.pU u * (if zOf (M.sg u).1 = z then (1 : ℝ) else 0)
    * (if xOf (M.sg u).1 = x then (1 : ℝ) else 0)
    * (if (M.sg u).2 (z, x) = y then (1 : ℝ) else 0)

/-- ⭐⭐ **`P(y | do(x), do(z))`**（`X` 与 `Z` **都**被钉死）。

$$:= \sum_u p_U(u)\,[f_u(z,x) = y]$$

**⚠ 钉死两个分量后 `U` 律不变** —— 这正是 `do` 的语义（`DoCalculus.do_pU`）。** -/
noncomputable def doLaw2
    (M : SCM3 Z X Y) [DecidableEq Y] (x : X) (z : Z) (y : Y) : ℝ :=
  ∑ u, M.pU u * (if (M.sg u).2 (z, x) = y then (1 : ℝ) else 0)

/-- ⭐⭐ **`P(Z = z, Y = y | do(x))`**：`X` 被钉死，`Z` **只观测不干预**（**联合质量**）。

$$:= \sum_u p_U(u)\,[\mathrm{zOf}(x_u) = z]\,[f_u(z,x) = y]$$

**⭐⭐ 规则 2 的右端在**归一化之后**才是 `P(y | do(x), z)`** ——
**即 `doLawX / P(Z=z|do(x))`（§3 的 `doLawXCond`）。** -/
noncomputable def doLawX
    (M : SCM3 Z X Y) [DecidableEq Z] [DecidableEq Y]
    (x : X) (z : Z) (y : Y) : ℝ :=
  ∑ u, M.pU u * (if zOf (M.sg u).1 = z then (1 : ℝ) else 0)
    * (if (M.sg u).2 (z, x) = y then (1 : ℝ) else 0)

/-- ⭐⭐ **`P(Z = z | do(x))`**：`Z` 的边缘**质量**（归一化常数）。

$$:= \sum_u p_U(u)\,[\mathrm{zOf}(x_u) = z]$$ -/
noncomputable def zMass
    (M : SCM3 Z X Y) [DecidableEq Z] (z : Z) : ℝ :=
  ∑ u, M.pU u * (if zOf (M.sg u).1 = z then (1 : ℝ) else 0)

/-- ⭐⭐⭐ **`P(y | do(x), z)`**（**归一化的**条件律）。

$$:= \frac{\mathrm{doLawX}\,M\,x\,z\,y}{\mathrm{zMass}\,M\,z}$$

**⚠ 归一化守卫**：`zMass M z ≠ 0` 处才有语义（§3 的定理都附这个守卫）。** -/
noncomputable def doLawXCond
    (M : SCM3 Z X Y) [DecidableEq Z] [DecidableEq Y]
    (x : X) (z : Z) (y : Y) : ℝ :=
  doLawX M x z y / zMass M z

/-- ⭐⭐ **`P(y | do(x))`**：**只**钉死 `X`，`Z` 按其机制取值后**边缘化**。

$$:= \sum_u p_U(u)\,[f_u(\mathrm{zOf}(x_u), x) = y]$$

**⭐ 这是规则 3 的**右端**。** -/
noncomputable def doLawXOnly
    (M : SCM3 Z X Y) [DecidableEq Y] (x : X) (y : Y) : ℝ :=
  ∑ u, M.pU u
    * (if (M.sg u).2 (zOf (M.sg u).1, x) = y then (1 : ℝ) else 0)

/-- ⭐⭐ **`P(y | x, z)`**：`X` 与 `Z` **都**被观测筛选（无干预）。 -/
noncomputable def obsY
    (M : SCM3 Z X Y) [DecidableEq Z] [DecidableEq X] [DecidableEq Y]
    (x : X) (z : Z) (y : Y) : ℝ :=
  ∑ u, M.pU u * (if zOf (M.sg u).1 = z then (1 : ℝ) else 0)
    * (if xOf (M.sg u).1 = x then (1 : ℝ) else 0)
    * (if (M.sg u).2 (z, x) = y then (1 : ℝ) else 0)

/-! ### §0.1 ⭐ 基础求和引理（`Fin 2` 上的具体计算） -/

/-- ⭐ **`∑_{u:Fin 2} (1/2)·[u = z] = 1/2`**（**真计算**）。 -/
theorem sum_half_ind (z : Fin 2) :
    (∑ u : Fin 2, (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0)) = 1 / 2 := by
  have key : (∑ u : Fin 2, (if u = z then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq' Finset.univ z (fun _ => (1 : ℝ))]
    simp
  rw [← Finset.mul_sum, key]
  ring

/-- ⭐ **`∑_{u:Fin 2} (1/2)·t = t`**（**真计算**）。 -/
theorem sum_half_const (t : ℝ) : (∑ _u : Fin 2, (1 : ℝ) / 2 * t) = t := by
  rw [Finset.sum_const, Finset.card_univ, show Fintype.card (Fin 2) = 2 from rfl]
  ring

end Sem3

/-! ===========================================================================
  §1 ⭐⭐ **语义前提**（**⚠⚠ S2 登记：这是结论的换写，不是实质内容**）
  =========================================================================== -/

/-- ⭐⭐⭐ **规则 2 的**语义前提**：`Z` 是**纯中介** ——
`do(z)` 与**观测** `z` 给出**同一个** `Y` 律。

$$\textbf{Rule2Condition}(M) := \forall x\,z\,y,\
  \mathrm{doLaw2}\,M\,x\,z\,y = \mathrm{doLawXCond}\,M\,x\,z\,y.$$

**⚠⚠ S2 登记**：**这个前提与规则 2 的结论是**同一个命题**（见 `Rule2Condition_iff`）。
**⟹ 由它推结论的 `rule2_semantic` 是**定义展开**，按 S4 纪律**不计入实质定理**。
**实质内容只在 §3–§5 的数值定理里。** -/
def Rule2Condition {Z X Y : Type u} [DecidableEq Z] [DecidableEq Y]
    (M : Sem3.SCM3 Z X Y) : Prop :=
  ∀ x z y, Sem3.doLaw2 M x z y = Sem3.doLawXCond M x z y

/-- ⭐⭐⭐ **规则 3 的**语义前提**：`Z` 对 `Y` **无影响** ——
把 `Z` 钉到**任意**值都不改变 `Y` 的律。

$$\textbf{Rule3Condition}(M) := \forall x\,z\,y,\
  \mathrm{doLaw2}\,M\,x\,z\,y = \mathrm{doLawXOnly}\,M\,x\,y.$$

**⚠⚠ S2 登记**：同上，**前提与结论同形** ⟹ `rule3_semantic` 是定义展开。** -/
def Rule3Condition {Z X Y : Type u} [DecidableEq Y]
    (M : Sem3.SCM3 Z X Y) : Prop :=
  ∀ x z y, Sem3.doLaw2 M x z y = Sem3.doLawXOnly M x y

/-! ===========================================================================
  §2 ⚠⚠ **「前提 ⟹ 结论」+ 双向刻画**（**定义展开，S2/S4 已标：实质 = 0**）
  =========================================================================== -/

variable {Z X Y : Type u} [DecidableEq Z] [DecidableEq X] [DecidableEq Y]

/-- ⚠⚠ **规则 2 的语义定理**（**定义展开** `fun x z y => h x z y`）。

**S4 自报：实质内容 = 0。**
**它的作用是**把 §1 的前提与 Pearl 规则 2 的字面结论接上**，
**便于 §3–§5 的数值定理引用。** -/
theorem rule2_semantic (M : Sem3.SCM3 Z X Y) (h : Rule2Condition M) :
    ∀ x z y, Sem3.doLaw2 M x z y = Sem3.doLawXCond M x z y :=
  fun x z y => h x z y

/-- ⚠⚠ **规则 3 的语义定理**（**定义展开**）。**S4 自报：实质内容 = 0。** -/
theorem rule3_semantic (M : Sem3.SCM3 Z X Y) (h : Rule3Condition M) :
    ∀ x z y, Sem3.doLaw2 M x z y = Sem3.doLawXOnly M x y :=
  fun x z y => h x z y

/-- ⚠ **规则 2 前提的双向形态**（`Iff.rfl` — 两侧逐字相同）。

**它存在的唯一目的是**证明**：规则 2 的语义定理**不可能**比前提更强，
**故实质内容必须由**独立算出的数值**承载（§3–§4）。** -/
theorem Rule2Condition_iff (M : Sem3.SCM3 Z X Y) :
    Rule2Condition M ↔
      ∀ x z y, Sem3.doLaw2 M x z y = Sem3.doLawXCond M x z y :=
  Iff.rfl

/-- ⚠ **规则 3 前提的双向形态**（`Iff.rfl`）。 -/
theorem Rule3Condition_iff (M : Sem3.SCM3 Z X Y) :
    Rule3Condition M ↔
      ∀ x z y, Sem3.doLaw2 M x z y = Sem3.doLawXOnly M x y :=
  Iff.rfl

/-! ===========================================================================
  §3 ⭐⭐⭐ **规则 2 的数值验证**：`Z` 是纯中介（`chain`）
  =========================================================================== -/

/-- ⭐⭐⭐ **链式中介 `chain`**：`X → Z → Y`（`Z := x`，`Y := z`）。

```
U = Fin 2,  pU ≡ 1/2,  sg u = ((u, u), fun (z,x) => z)
```

即 `Z = u`、`X = u`、`Y = z` —— **`Y` 的方程只读 `z`**（不读 `x`、不读 `u`）。
**这正是「`Z` 是 `X` 的纯中介」的最简实现**：`Z` 确定地等于 `X`，`Y` 确定地等于 `Z`。 -/
noncomputable def chain : Sem3.SCM3 (Fin 2) (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun u => ((u, u), fun p => p.1)

/-- ⭐⭐⭐ **`P(y | do(x), do(z)) = [z = y]`**（`chain` 上，**与 `x` 无关**）。

$$\mathrm{doLaw2}\,\mathrm{chain}\,x\,z\,y = [z = y]$$

**⭐ 数值**：`z = y` 时 `= 1`；`z ≠ y` 时 `= 0`。** -/
theorem doLaw2_chain (x z y : Fin 2) :
    Sem3.doLaw2 chain x z y = if z = y then (1 : ℝ) else 0 := by
  show (∑ u : Fin 2, (1 : ℝ) / 2 * (if (chain.sg u).2 (z, x) = y then (1 : ℝ) else 0)) = _
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if (chain.sg u).2 (z, x) = y then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if z = y then (1 : ℝ) else 0) := by
    intro u
    have hh : (chain.sg u).2 (z, x) = z := rfl
    rw [hh]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_const]

/-- ⭐⭐⭐ **`P(Z = z | do(x)) = 1/2`**（`chain` 上）。 -/
theorem zMass_chain (z : Fin 2) : Sem3.zMass chain z = 1 / 2 := by
  show (∑ u : Fin 2,
      (1 : ℝ) / 2 * (if Sem3.zOf (chain.sg u).1 = z then (1 : ℝ) else 0)) = 1 / 2
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if Sem3.zOf (chain.sg u).1 = z then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) := by
    intro u
    have hh : Sem3.zOf (chain.sg u).1 = u := rfl
    rw [hh]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_ind]

/-- ⭐⭐⭐ **`P(Z = z, Y = y | do(x)) = (1/2)·[z = y]`**（`chain` 上，**联合质量**）。 -/
theorem doLawX_chain (x z y : Fin 2) :
    Sem3.doLawX chain x z y = (1 : ℝ) / 2 * (if z = y then (1 : ℝ) else 0) := by
  show (∑ u : Fin 2, (1 : ℝ) / 2 *
      (if Sem3.zOf (chain.sg u).1 = z then (1 : ℝ) else 0) *
      (if (chain.sg u).2 (z, x) = y then (1 : ℝ) else 0)) = _
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if Sem3.zOf (chain.sg u).1 = z then (1 : ℝ) else 0) *
        (if (chain.sg u).2 (z, x) = y then (1 : ℝ) else 0)
      = (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) * (if z = y then (1 : ℝ) else 0) := by
    intro u
    have h1 : Sem3.zOf (chain.sg u).1 = u := rfl
    have h2 : (chain.sg u).2 (z, x) = z := rfl
    rw [h1, h2]
  rw [Finset.sum_congr rfl (fun u _ => hstep u)]
  have hfac : (∑ u : Fin 2, (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) *
        (if z = y then (1 : ℝ) else 0))
      = (∑ u : Fin 2, (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0)) *
        (if z = y then (1 : ℝ) else 0) := by
    rw [Finset.sum_mul]
  rw [hfac, Sem3.sum_half_ind]

/-- ⭐⭐⭐⭐⭐ **规则 2 在 `chain` 上**逐字成立**（**具体数值**）。

$$\forall x\,z\,y,\quad
  \underbrace{P(y \mid do(x), do(z))}_{\mathrm{doLaw2}} \;=\;
  \underbrace{P(y \mid do(x), z)}_{\mathrm{doLawXCond}}$$

**⭐ 数值核对**（`zMass = 1/2`）：
- `z = y` 时：左边 `1`，右边 `(1/2)·1 / (1/2) = 1` ✓
- `z ≠ y` 时：左边 `0`，右边 `(1/2)·0 / (1/2) = 0` ✓

**⭐⭐ 这就是「`Z` 是纯中介时 `do(z)` 可换成 `z`」的精确语义版本。** -/
theorem chain_rule2 (x z y : Fin 2) :
    Sem3.doLaw2 chain x z y = Sem3.doLawXCond chain x z y := by
  rw [Sem3.doLawXCond, doLawX_chain, zMass_chain, doLaw2_chain]
  by_cases h : z = y
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; norm_num

/-- ⭐⭐⭐⭐ **⚠ 归一化是必需的**：**不做归一化时两律不等**（`chain` 上）。

$$\mathrm{doLaw2}\,\mathrm{chain}\,x\,z\,y = [z=y] \;\ne\;
  \tfrac12\,[z=y] = \mathrm{doLawX}\,\mathrm{chain}\,x\,z\,y
  \quad (\text{取 } z = y).$$

**⭐ 数值**：`1 ≠ 1/2`。

**⟹ 这解释了为什么 §0 必须引入 `zMass` 与 `doLawXCond`**：
**`doLawX` 是**联合质量**，规则 2 比较的是**条件律**。** -/
theorem chain_rule2_ne_doLaw_unguarded (x : Fin 2) :
    ∃ z y, Sem3.doLaw2 chain x z y ≠ Sem3.doLawX chain x z y := by
  refine ⟨0, 0, ?_⟩
  rw [doLaw2_chain, doLawX_chain]
  norm_num

/-- ⭐⭐⭐ **`chain` 满足 `Rule2Condition`**（把 §3 的数值打包成 §1 的前提）。

**⭐ 这给出**规则 2 的语义前提**的一个**非空实例** ——
**故 `rule2_semantic` 的前提不是空条件。** -/
theorem chain_Rule2Condition : Rule2Condition chain :=
  fun x z y => chain_rule2 x z y

/-! ===========================================================================
  §4 ⭐⭐⭐⭐ **规则 2 的**反例****：`Z` **不是**纯中介时**不成立**（`direct`）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **对照模型 `direct`**：`Y` **直接读 `x`**（不读 `z`），
`Z` 与 `X` 仍**共用外生分量**（故 `Z = X = u`）。

```
U = Fin 2,  pU ≡ 1/2,  sg u = ((u, u), fun (z,x) => x)
```

**⭐ 与 `chain` 的唯一差别**：`Y` 的方程从 `fun p => p.1 (= z)` 换成 `fun p => p.2 (= x)`。
**⚠ 这就把 `Z` 从「纯中介」变成「与 `Y` 无关的分叉终点」** ——
**规则 2 的前提（`Z` 阻断 `X → Y` 的唯一路径）在此失效。** -/
noncomputable def direct : Sem3.SCM3 (Fin 2) (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun u => ((u, u), fun p => p.2)

/-- ⭐ **`P(y | do(x), do(z)) = [x = y]`**（`direct` 上，**与 `z` 无关**）。 -/
theorem doLaw2_direct (x z y : Fin 2) :
    Sem3.doLaw2 direct x z y = if x = y then (1 : ℝ) else 0 := by
  show (∑ u : Fin 2, (1 : ℝ) / 2 * (if (direct.sg u).2 (z, x) = y then (1 : ℝ) else 0)) = _
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if (direct.sg u).2 (z, x) = y then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if x = y then (1 : ℝ) else 0) := by
    intro u
    have hh : (direct.sg u).2 (z, x) = x := rfl
    rw [hh]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_const]

/-- ⭐ **`P(Z = z | do(x)) = 1/2`**（`direct` 上）。 -/
theorem zMass_direct (z : Fin 2) : Sem3.zMass direct z = 1 / 2 := by
  show (∑ u : Fin 2,
      (1 : ℝ) / 2 * (if Sem3.zOf (direct.sg u).1 = z then (1 : ℝ) else 0)) = 1 / 2
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if Sem3.zOf (direct.sg u).1 = z then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) := by
    intro u
    have hh : Sem3.zOf (direct.sg u).1 = u := rfl
    rw [hh]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_ind]

/-- ⭐ **`P(Z = z, Y = y | do(x)) = (1/2)·[x = y]`**（`direct` 上）。 -/
theorem doLawX_direct (x z y : Fin 2) :
    Sem3.doLawX direct x z y = (1 : ℝ) / 2 * (if x = y then (1 : ℝ) else 0) := by
  show (∑ u : Fin 2, (1 : ℝ) / 2 *
      (if Sem3.zOf (direct.sg u).1 = z then (1 : ℝ) else 0) *
      (if (direct.sg u).2 (z, x) = y then (1 : ℝ) else 0)) = _
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if Sem3.zOf (direct.sg u).1 = z then (1 : ℝ) else 0) *
        (if (direct.sg u).2 (z, x) = y then (1 : ℝ) else 0)
      = (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) *
        (if x = y then (1 : ℝ) else 0) := by
    intro u
    have h1 : Sem3.zOf (direct.sg u).1 = u := rfl
    have h2 : (direct.sg u).2 (z, x) = x := rfl
    rw [h1, h2]
  rw [Finset.sum_congr rfl (fun u _ => hstep u)]
  have hfac : (∑ u : Fin 2, (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) *
        (if x = y then (1 : ℝ) else 0))
      = (∑ u : Fin 2, (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0)) *
        (if x = y then (1 : ℝ) else 0) := by
    rw [Finset.sum_mul]
  rw [hfac, Sem3.sum_half_ind]

/-- ⭐⭐⭐ **规则 2 在 `direct` 上仍然成立**（**第二个正例，不是反例**）。

$$\mathrm{doLaw2}\,\mathrm{direct}\,x\,z\,y = [x=y] = \mathrm{doLawXCond}\,\mathrm{direct}\,x\,z\,y.$$

**⚠ 诚实说明**：`direct` 里 `Z` 与 `X` **完全共线**（都等于 `u`），
`Y` 只读 `x` —— 故 `do(z)` 与观测 `z` 提供**同样的** `X` 信息，两律必然相等。
**⟹ 这不是反例。** 真正的问题是：
**`direct` 中 `Z` 仍**不携带任何 `Y` 的独立信息**，
所以规则 2 的前提（`Y ⊥_d Z | X`）**依然成立**。

**⭐⭐ 因此正确的反例必须让 `Z` **真的决定** `Y`（即 `Y` 的方程读 `z` 或读 `u`），
同时又让 `Z` 与 `u` **相关** —— 这正是 §4.2 的 `conf`。** -/
theorem direct_rule2_holds (x z y : Fin 2) :
    Sem3.doLaw2 direct x z y = Sem3.doLawXCond direct x z y := by
  rw [Sem3.doLawXCond, doLawX_direct, zMass_direct, doLaw2_direct]
  by_cases h : x = y
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; norm_num

/-! ### §4.2 ⭐⭐⭐⭐⭐ **规则 2 的真反例：`conf`（完全混杂）**

**⭐ 构造**：`U = Fin 2`、`pU ≡ 1/2`、`sg u = ((u,u), fun _ => u)`
⟹ `Z = X = u`，**且 `Y = u`**（`Y` 的方程读 `u`，忽略它的参数）。

**⭐ 这是「`U` 同时决定 `Z` 与 `Y`」的**最极端**形式** ——
经典的「混杂」：`Y` 的误差与 `Z` 完全重合。
**⟹ 规则 2 的前提（`Y ⊥_d Z | X`）在此**失效**（`Z` 与 `Y` 经由 `u` 强相关）。** -/

/-- ⭐⭐⭐⭐⭐ **完全混杂模型 `conf`**：`Y = Z = X = u`。 -/
noncomputable def conf : Sem3.SCM3 (Fin 2) (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun u => ((u, u), fun _ => u)

/-- ⭐ **`P(y | do(x), do(z)) = 1/2`**（`conf` 上 —— `do(z)` **钉不住** `u`，
`Y = u` 仍随机）。 -/
theorem doLaw2_conf (x z y : Fin 2) : Sem3.doLaw2 conf x z y = 1 / 2 := by
  show (∑ u : Fin 2, (1 : ℝ) / 2 * (if (conf.sg u).2 (z, x) = y then (1 : ℝ) else 0)) = 1 / 2
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if (conf.sg u).2 (z, x) = y then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if u = y then (1 : ℝ) else 0) := by
    intro u
    have hh : (conf.sg u).2 (z, x) = u := rfl
    rw [hh]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_ind]

/-- ⭐ **`P(Z = z | do(x)) = 1/2`**（`conf` 上）。 -/
theorem zMass_conf (z : Fin 2) : Sem3.zMass conf z = 1 / 2 := by
  show (∑ u : Fin 2,
      (1 : ℝ) / 2 * (if Sem3.zOf (conf.sg u).1 = z then (1 : ℝ) else 0)) = 1 / 2
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if Sem3.zOf (conf.sg u).1 = z then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) := by
    intro u
    have hh : Sem3.zOf (conf.sg u).1 = u := rfl
    rw [hh]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_ind]

/-- ⭐ **`P(Z = z, Y = y | do(x)) = (1/2)·[z = y]`**（`conf` 上 ——
**观测 `Z` 就钉住了 `u`，故 `Y` 变成确定**）。 -/
theorem doLawX_conf (x z y : Fin 2) :
    Sem3.doLawX conf x z y = (1 : ℝ) / 2 * (if z = y then (1 : ℝ) else 0) := by
  show (∑ u : Fin 2, (1 : ℝ) / 2 *
      (if Sem3.zOf (conf.sg u).1 = z then (1 : ℝ) else 0) *
      (if (conf.sg u).2 (z, x) = y then (1 : ℝ) else 0)) = _
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if Sem3.zOf (conf.sg u).1 = z then (1 : ℝ) else 0) *
        (if (conf.sg u).2 (z, x) = y then (1 : ℝ) else 0)
      = (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) * (if u = y then (1 : ℝ) else 0) := by
    intro u
    have h1 : Sem3.zOf (conf.sg u).1 = u := rfl
    have h2 : (conf.sg u).2 (z, x) = u := rfl
    rw [h1, h2]
  rw [Finset.sum_congr rfl (fun u _ => hstep u)]
  by_cases h : z = y
  · subst h
    have e : ∀ u : Fin 2,
        (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) * (if u = z then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) := by
      intro u
      by_cases hh : u = z <;> simp [hh]
    rw [Finset.sum_congr rfl (fun u _ => e u), Sem3.sum_half_ind]
    norm_num
  · have e : ∀ u : Fin 2,
        (1 : ℝ) / 2 * (if u = z then (1 : ℝ) else 0) * (if u = y then (1 : ℝ) else 0) = 0 := by
      intro u
      by_cases hh : u = z
      · have huy : u ≠ y := fun h2 => h (hh.symm.trans h2)
        rw [if_pos hh, if_neg huy]
        ring
      · rw [if_neg hh]
        ring
    rw [Finset.sum_congr rfl (fun u _ => e u), if_neg h]
    norm_num

/-- ⭐⭐⭐⭐⭐ **规则 2 在 `conf` 上**不成立**（**具体数值反例**）。

**取** `x = z = y = 0`：

$$P(y{=}0 \mid do(x{=}0), do(z{=}0)) = \tfrac12
  \;\ne\; 1 = \frac{(1/2)\cdot 1}{1/2} = P(y{=}0 \mid do(x{=}0), z{=}0).$$

**⭐⭐ 语义读法**：把 `Z` **钉成** `0` **不**告诉你 `u` 是多少（`do(z)` 切断 `Z` 的入边），
**故 `Y = u` 仍按 `1/2` 随机**；
**但**观测 `Z = 0` **确实**告诉你 `u = 0`，**故 `Y` 必为 `0`**。
**⟹ 这正是「`do(z)` 不能换成 `z`」的**数值见证**。

**⟹ 与 §3 的 `chain_rule2` 合起来，规则 2 被**钉死在一个精确的开关上**：
`Z` 是否阻断 `X`（及 `Z` 本身）与 `Y` 的混杂。** -/
theorem conf_rule2_fails :
    ∃ x z y, Sem3.doLaw2 conf x z y ≠ Sem3.doLawXCond conf x z y := by
  refine ⟨0, 0, 0, ?_⟩
  rw [Sem3.doLawXCond, doLawX_conf, zMass_conf, doLaw2_conf]
  norm_num

/-- ⭐⭐⭐⭐ **`conf` **不满足** `Rule2Condition`** —— **故规则 2 的语义前提不是恒真式**。 -/
theorem conf_not_Rule2Condition : ¬ Rule2Condition conf := by
  intro h
  obtain ⟨x, z, y, hne⟩ := conf_rule2_fails
  exact hne (h x z y)

/-! ===========================================================================
  §5 ⭐⭐⭐ **规则 3 的数值验证**：`Z` 对 `Y` 无影响（`indep`）
  =========================================================================== -/

/-- ⭐⭐⭐ **`Z` 对 `Y` 无影响的模型 `indep`**：
`Y` 的方程取 `fun _ => u`（**忽略它的全部参数**，只读 `u`）。

```
U = Fin 2,  pU ≡ 1/2,  sg u = ((u, u), fun _ => u)
```

**⭐ 语义**：`Y = u` 完全由外生决定 —— **`X`、`Z` 都改变不了它**。
**这正是「`Z` 对 `Y` 无影响」的最强形式：`Y` 的方程连 `x` 都不读。** -/
noncomputable def indep : Sem3.SCM3 (Fin 2) (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun u => ((u, u), fun _ => u)

/-- ⭐ **`P(y | do(x), do(z)) = 1/2`**（`indep` 上，**与 `x`、`z` 都无关**）。 -/
theorem doLaw2_indep (x z y : Fin 2) :
    Sem3.doLaw2 indep x z y = 1 / 2 := by
  show (∑ u : Fin 2, (1 : ℝ) / 2 * (if (indep.sg u).2 (z, x) = y then (1 : ℝ) else 0)) = 1 / 2
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if (indep.sg u).2 (z, x) = y then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if u = y then (1 : ℝ) else 0) := by
    intro u
    have hh : (indep.sg u).2 (z, x) = u := rfl
    rw [hh]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_ind]

/-- ⭐ **`P(y | do(x)) = 1/2`**（`indep` 上）。 -/
theorem doLawXOnly_indep (x y : Fin 2) :
    Sem3.doLawXOnly indep x y = 1 / 2 := by
  show (∑ u : Fin 2, (1 : ℝ) / 2 *
      (if (indep.sg u).2 (Sem3.zOf (indep.sg u).1, x) = y then (1 : ℝ) else 0)) = 1 / 2
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if (indep.sg u).2 (Sem3.zOf (indep.sg u).1, x) = y then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if u = y then (1 : ℝ) else 0) := by
    intro u
    have hh : (indep.sg u).2 (Sem3.zOf (indep.sg u).1, x) = u := rfl
    rw [hh]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_ind]

/-- ⭐⭐⭐⭐⭐ **规则 3 在 `indep` 上**逐字成立**（**具体数值**）。

$$\forall x\,z\,y,\quad
  \underbrace{P(y \mid do(x), do(z))}_{\mathrm{doLaw2}} \;=\;
  \underbrace{P(y \mid do(x))}_{\mathrm{doLawXOnly}} \;=\; \tfrac12.$$

**⭐⭐ 这就是「`Z` 对 `Y` 无影响时 `do(z)` 可删」的精确语义版本。** -/
theorem indep_rule3 (x z y : Fin 2) :
    Sem3.doLaw2 indep x z y = Sem3.doLawXOnly indep x y := by
  rw [doLaw2_indep, doLawXOnly_indep]

/-- ⭐⭐⭐ **`indep` 满足 `Rule3Condition`**（规则 3 前提的**非空实例**）。 -/
theorem indep_Rule3Condition : Rule3Condition indep :=
  fun x z y => indep_rule3 x z y

/-! ===========================================================================
  §6 ⭐⭐⭐⭐ **规则 3 的**反例****：`Z` **影响 `Y` 时**不成立**（`zMatters`）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`Z` **影响** `Y` 的模型 `zMatters``**：`Y` 的方程取 `fun p => p.1`（**读 `z`**）。

```
U = Fin 2,  pU ≡ 1/2,  sg u = ((u, u), fun (z,x) => z)
```

**⭐ 与 `indep` 的唯一差别**：`Y` 从 `fun _ => u` 换成 `fun p => p.1 (= z)`。
**⚠ 即 `Z` **真的进入** `Y` 的方程** —— 规则 3 的前提（`Y ⊥_d Z | X`）在此失效。**
**⚠⚠ 诚实说明**：`zMatters` 与 §3 的 `chain` **是**定义上同一个模型**
（`zMatters = chain` 由 `rfl`，见 `zMatters_eq_chain`）。
**⟹ 两个名字保留是因为**语义角色不同**（§3 强调「纯中介 ⟹ 规则 2 成立」，
§6 强调「`Z` 影响 `Y` ⟹ 规则 3 失败」）。
**⚠ 这也解释了 §7 的独立性定理为什么用 `chain` 就能一句话说完。** -/
noncomputable def zMatters : Sem3.SCM3 (Fin 2) (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun u => ((u, u), fun p => p.1)

/-- ⭐ **`zMatters` 与 `chain` 是定义上同一个模型**（`rfl`）。 -/
theorem zMatters_eq_chain : zMatters = chain := rfl

/-- ⭐ **`P(y | do(x), do(z)) = [z = y]`**（`zMatters` 上）。 -/
theorem doLaw2_zMatters (x z y : Fin 2) :
    Sem3.doLaw2 zMatters x z y = if z = y then (1 : ℝ) else 0 := by
  show (∑ u : Fin 2, (1 : ℝ) / 2 * (if (zMatters.sg u).2 (z, x) = y then (1 : ℝ) else 0)) = _
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 * (if (zMatters.sg u).2 (z, x) = y then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if z = y then (1 : ℝ) else 0) := by
    intro u
    have hh : (zMatters.sg u).2 (z, x) = z := rfl
    rw [hh]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_const]

/-- ⭐ **`P(y | do(x)) = 1/2`**（`zMatters` 上，`Z` **边缘化后** `Y = u`）。 -/
theorem doLawXOnly_zMatters (x y : Fin 2) :
    Sem3.doLawXOnly zMatters x y = 1 / 2 := by
  show (∑ u : Fin 2, (1 : ℝ) / 2 *
      (if (zMatters.sg u).2 (Sem3.zOf (zMatters.sg u).1, x) = y then (1 : ℝ) else 0)) = 1 / 2
  have hstep : ∀ u : Fin 2,
      (1 : ℝ) / 2 *
        (if (zMatters.sg u).2 (Sem3.zOf (zMatters.sg u).1, x) = y then (1 : ℝ) else 0)
        = (1 : ℝ) / 2 * (if u = y then (1 : ℝ) else 0) := by
    intro u
    have hh : (zMatters.sg u).2 (Sem3.zOf (zMatters.sg u).1, x)
        = Sem3.zOf (zMatters.sg u).1 := rfl
    have h1 : Sem3.zOf (zMatters.sg u).1 = u := rfl
    rw [hh, h1]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_ind]

/-- ⭐⭐⭐⭐⭐ **规则 3 在 `zMatters` 上**不成立**（**具体数值反例**）。

**取** `x = 0`、`z = 0`、`y = 0`：

$$P(y{=}0 \mid do(x{=}0), do(z{=}0)) = [0 = 0] = 1
  \;\ne\; \tfrac12 = P(y{=}0 \mid do(x{=}0)).$$

**⭐ 数值：`1 ≠ 1/2`。**

**⟹ 这给出「`Z` 影响 `Y` 时 `do(z)` **不**可删」的**具体见证**。**
**⟹ 与 §5 的 `indep_rule3` 合起来，规则 3 被**钉死在一个精确的开关上**：
`Y` 的方程是否读 `z`。** -/
theorem zMatters_rule3_fails :
    ∃ x z y, Sem3.doLaw2 zMatters x z y ≠ Sem3.doLawXOnly zMatters x y := by
  refine ⟨0, 0, 0, ?_⟩
  rw [doLaw2_zMatters, doLawXOnly_zMatters]
  norm_num

/-- ⭐⭐⭐⭐ **`zMatters` **不满足** `Rule3Condition`**（把 §6 的数值打包成前提的否定）。

**⭐ 故 `Rule3Condition` **不是恒真式** —— 它把模型空间**真切开**。** -/
theorem zMatters_not_Rule3Condition : ¬ Rule3Condition zMatters := by
  intro h
  obtain ⟨x, z, y, hne⟩ := zMatters_rule3_fails
  exact hne (h x z y)

/-! ===========================================================================
  §7 ⭐⭐⭐⭐ **两条规则在**同一模型**上的独立性**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **规则 2 与规则 3 的前提**互不蕴含**（**同一模型上的数值见证**）。

**陈述**：

$$\textbf{Rule2Condition}(\mathrm{chain}) \;\wedge\;
  \neg\,\textbf{Rule3Condition}(\mathrm{chain}).$$

**⭐ 读法**：`chain` 里 `Z` 是**纯中介**（故规则 2 的前提成立，§3），
**但** `Z` **确实影响 `Y`**（`Y = z`，故规则 3 的前提**不**成立）。
**⟹ 规则 2 与规则 3 是**两条独立的规则**：
**成立一条不保证另一条。**

**⭐ 具体数值**（`chain`，取 `z = 0`、`y = 1`）：
- 规则 2：`1 = 1`（`P(y|do(x),do(0)) = [0=1] = 0`，归一化后同样 `0`）✓
- 规则 3：`0 ≠ 1/2`（`P(y|do(x),do(0)) = 0` 而 `P(y|do(x)) = 1/2`）✗ **失败**

**⚠ 该 `chain` 上规则 3 的失败正是 §3 的 `chain_rule2_ne_doLaw_unguarded` 的
「另一面」**：`do(z)` **不是**可删的。** -/
theorem rule2_and_rule3_independent :
    Rule2Condition chain ∧ ¬ Rule3Condition chain := by
  refine ⟨chain_Rule2Condition, ?_⟩
  intro h
  have h30 : Sem3.doLaw2 chain 0 0 1 = Sem3.doLawXOnly chain 0 1 := h 0 0 1
  rw [doLaw2_chain] at h30
  -- doLawXOnly chain 0 1 = 1/2 (chain == zMatters model)
  have hx : Sem3.doLawXOnly chain 0 1 = 1 / 2 := by
    show (∑ u : Fin 2, (1 : ℝ) / 2 *
        (if (chain.sg u).2 (Sem3.zOf (chain.sg u).1, 0) = 1 then (1 : ℝ) else 0)) = 1 / 2
    have hstep : ∀ u : Fin 2,
        (1 : ℝ) / 2 *
          (if (chain.sg u).2 (Sem3.zOf (chain.sg u).1, 0) = 1 then (1 : ℝ) else 0)
          = (1 : ℝ) / 2 * (if u = 1 then (1 : ℝ) else 0) := by
      intro u
      have hh : (chain.sg u).2 (Sem3.zOf (chain.sg u).1, 0)
          = Sem3.zOf (chain.sg u).1 := rfl
      have h1 : Sem3.zOf (chain.sg u).1 = u := rfl
      rw [hh, h1]
    rw [Finset.sum_congr rfl (fun u _ => hstep u), Sem3.sum_half_ind]
  rw [hx] at h30
  -- h30 : (if (0:Fin 2) = 1 then 1 else 0) = 1/2
  norm_num at h30

end R246G3

end FateV2.Predict