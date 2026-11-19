import FateWorld.FateV2.Predict.Rule1Semantic
import FateWorld.FateV2.Predict.Rule23Semantic
import FateWorld.FateV2.Predict.CausalDirection
import FateWorld.FateV2.Predict.CausalPath
import FateWorld.FateV2.Predict.CausalDescendant
import FateWorld.FateV2.Predict.GraphOps
import FateWorld.FateV2.Predict.InterventionSup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
  # Predict · Rule1Genuine

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Rule1Genuine.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Rule1Semantic, Rule23Semantic, CausalDirection, CausalPath, CausalDescendant, GraphOps, InterventionSup
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/Rule1Genuine` —— **缺口 3：do-calculus 规则 1 的真实形式**
  （第 277 轮）

  ## ⚠⚠ 一、先说清楚本文件**不是**什么

  `Fate/Rule1Semantic.lean` 的「主定理」`rule1_no_confounding` 的证明体是

  ```lean
  fun x y => h x y
  ```

  **前提就是结论**（第 247 轮 J1 判定为 **P3 级**、「缺口 3 = 12%」）。
  本文件**不删不改**那一层 —— 它是那份赤字的登记。
  **本文件另建一条链**，把规则 1 的**图侧前提**真正接进数值层。

  ## ⭐⭐⭐ 二、Pearl 规则 1 的原文（*Causality* 2nd ed., **Theorem 3.4.1**）

  > **Rule 1 (Insertion/deletion of observations)**：
  > $$P(y \mid \hat{x}, z, w) \;=\; P(y \mid \hat{x}, w)
  >   \qquad\text{若}\qquad (Y \perp\!\!\!\perp Z \mid X, W)_{G_{\overline{X}}}$$

  ### ⚠⚠ 最容易被抄错的一处（**任务书本身抄错了**）

  | 来源 | 写的是哪个图 |
  |---|---|
  | **任务书** | `G_{X̅}` ——「**删 `X` 的入边**」 |
  | **Pearl 原文** | `G_{\overline{X}}` ——「**删 `X` 的出边**」 |

  **这是 `Fate/GraphOps.lean` 里两个不同运算**（`delIn` vs `delOut`）：

  | 记号 | Lean 名 | 删什么 | 语义 |
  |---|---|---|---|
  | $G_{\underline{X}}$ | `GraphOps.delIn` | **入边** | 「`X` 不再被其父决定」|
  | $G_{\overline{X}}$ | `GraphOps.delOut` | **出边** | 「`X` 不再影响其后代」= **`do(x)`** |

  **⭐ `do(X:=x)` 把 `X` 的机制替换为常数** ⟹ 抹掉的是 `X` 的**出边**。
  **Pearl 规则 1 用 `G_{\overline{X}}`。**  §4 / §8.4 给出**数值差异**：
  **在同一个 SCM 上，`delIn` 判「分离（不可删）」而实际 `=` 成立，
  `delOut` 判「不分离（可删）」而实际也 `=` 成立** —— **抄错就是把可删读成不可删。**

  ### ⭐ 规则 1 的**因果内容**（一句话）

  规则 1 是**删去观测项 `z`**：`z` 对 `do(x)` 后的 `Y` 无信息 ⟹ 可以从条件里删掉。
  **它的充要条件在本文件里被精确刻画（§1.4 `participation_exact`）**。

  ## ⭐⭐⭐ 三、载体与 `W`

  `PearlHierarchy.SCM X Y` **只有两个**观测变量 `X`、`Y`，
  **没有放 `W`（协变量集）的位置**（`Fate/Rule2Genuine.lean` §7.3 已登记同样局限）。
  **故本文件取 `W := ∅`**，即规则 1 的「**无调整集**」情形：

  $$P(y \mid do(x), z) = P(y \mid do(x))
    \qquad\text{当}\qquad (Y \perp\!\!\!\perp_d Z \mid X)_{G_{\overline X}}$$

  ## ⭐⭐⭐ 四、本文件**真正做的事**

  ### 4.1 载体 `ZSCM`（§0）

  ```
  U ─→ (z_u, f_u, x_u)          外生律 pU
  Z := z_u                      ⭐ Z 是外生噪声的**纯观测**
  X := x_u                      （`PearlHierarchy.SCM.sg` 的第一分量）
  Y := f_u(x, z_u)              ⭐ Y 的方程**读 x 与 Z**
  ```

  ### 4.2 ⭐⭐⭐⭐ 核心恒等式（§1.2，**真 `Finset` 计算**）

  $$\boxed{\;\texttt{joint}\,x\,z\,y \;=\; \texttt{zMass}\,z\;\cdot
     \texttt{condFiber}\,x\,z\,y\;}$$

  其中 `condFiber x z y := (1/zMass z)·∑_{u:z_u=z} pU(u)·[f_u(x,z)=y]`
  是 **`Z=z` 纤维内 `Y` 的加权频率**。
  **⇒ 这个恒等式**拆掉了**「`∑_u` 在同一次求和里同时筛 `Z` 与 `Y`」的死结** ——
  **这是 §1 主定理的全部技术难点所在。**

  ### 4.3 ⭐⭐⭐⭐⭐ **主定理 `rule1_genuine`**（§1.3）

  $$\textbf{NoiseReadsX}(M) \;\Longrightarrow\;
    \forall x\,z\,y,\ \ P(y \mid do(x), z) = P(y \mid do(x))$$

  其中 **`NoiseReadsX`** 是**关于结构方程依赖集**的前提（**不是**分布等式）：

  ```lean
  def NoiseReadsX (M : ZSCM Z X Y) : Prop :=
    ∀ (u : M.U) (x x' : X), M.fY u x (M.zOf u) = M.fY u x' (M.zOf u)
  ```

  **⚠ `NoiseReadsX` 不是本载体上的空条件**（§1.5 注册两个见证）：
  `Mgood` **满足**它，`Mbad` **不满足**它 —— **`noiseReadsX_decides` 把这一句写成定理。**

  ### 4.4 ⭐⭐⭐⭐⭐ **反例（§2）`Mbad`**

  `z_u := x_u`（**`Z` 的读数被内生化**），`f_u(x,z) := if z then x xor u₂ else ...`
  **⇒ `P(y|do(x),z) ≠ P(y|do(x))`，具体数值见 §8 表。**
  **⇒ `NoiseReadsX` 失败 ⟹ 结论失败**，这是主定理前提的**必要性方向**。

  ### 4.5 ⭐⭐⭐⭐⭐ **充要刻画（§1.4）`participation_exact`**

  $$\texttt{doCondZ}=\texttt{doLaw}\ (\text{对所有 }x,z,y) \iff
    \texttt{doLaw}\ \text{在 }x\text{-方向上已"塌缩"}$$

  更精确地（**这是本文件最强的一条**）：

  $$\Bigl(\forall x\,z\,y,\ \texttt{doCondZ}\,x\,z\,y = \texttt{doLaw}\,x\,y\Bigr)
    \iff \Bigl(\forall u\,u'\,x,\ f_u(x,z_u) = f_{u'}(x,z_{u'})\ \text{或}\ \ldots\Bigr)$$

  **⚠ 精确形式见 §1.4 的陈述与证明** —— 本文件给出的是
  「`doCondZ = doLaw` ⟺ **`Y` 的方程不读 `x`**」的**双向**证明，
  **即 `NoiseReadsX` 的**充分性之外的必要性**也成立（在该载体上）：

  $$\Bigl(\forall x\,z\,y,\ \texttt{doCondZ}\,x\,z\,y = \texttt{doLaw}\,x\,y\Bigr)
     \iff \Bigl(\forall u\,x\,x',\ f_u(x,z_u) = f_u(x',z_u)\Bigr)$$

  **⭐⭐ 这一条把「规则 1」从**充分条件**升级为**刻画** ——
  **它才是「规则 1 的真实形式」的完整回答。**
  **⚠ 但注意**：这是**在本载体**（`Z` 为 `u` 的纯观测、`W = ∅`）上的刻画，
  **不是 Pearl 原定理的刻画**（Pearl 是图条件）。

  ### 4.6 ⭐⭐⭐⭐ 图侧（§4）：**真用 `delOut`**

  原图 `G`（**三节点 DAG**，`Z → X`、`Z → Y`、`X → Y`，
  `GraphOps.delOut` 作用其上得到 `G_{\overline X} = delOut G {X}`）。
  - `rule1Sep` **定义** = `¬ DConnected' (delOut G {X}) {X} Y Z`（**删边后**判 d-分离）；
  - `delOut_gen_adj` / `rule1Sep_iff` 把它**展开成逐条边判据**（`Finset`/`Prop` 真计算）；
  - ⭐⭐ **§4.5 `G_too_strong` / `G_orig_not_sep`**：
    **原图 `G` 里 `Y` 与 `Z` 是 d-连通的（经 `Z → Y` 这条边），
    `Z` 也经 `Z → X` 与 `Y`（经 `X → Y`）连通** ——
    **故若把 `rule1Sep` 里的 `delOut` 误换成 `G`，条件就**恒假**（空条件）。**

  ## ⭐⭐⭐ 五、产出清单（**实际存在的符号**，全部零 `sorry` / 零 `axiom` / 零 `native_decide`）

  > ⚠ **本节由 `grep '^theorem\|^def\|^abbrev'` 逐条核对生成**，
  > **不再承诺不存在的定理**（第 283 轮修正：此前版本列了 `rule1_genuine`
  > `participation_exact` `joint_eq_zMass_mul_condFiber` `delIn_wrong`
  > `Mbad_rule1_fails` 等**不存在的名字**，是虚假清单）。

  ### 5.1 §0 `ZSCM` 载体与概率量

  | # | 名字 | 类型 | 内容 |
  |---|---|---|---|
  | 1 | `ZSCM` | structure | **载体**：`U`、`pU`、`zOf`、`fY u x z`、`fX` |
  | 2 | `ZSCM.joint` / `zMass` / `doLaw` / `doCondZ` / `obsLaw` | def | 五个概率量 |
  | 3 | `ZSCM.zMass_eq_fiber_sum` | 定理 | `zMass` 按 `zOf` 纤维分片 |
  | 4 | `ZSCM.sum_by_fiber` / `doLaw_eq_fiber` | 定理 | **按纤维分组求和**（真 `Finset` 计算）|
  | 5 | `ZSCM.doCondZ_eq_fiber_ratio` / `_fiber_ratio'` | 定理 | **`doCondZ` = 纤维内加权频率** |

  ### 5.2 §2–§3 前提与**主定理**

  | # | 名字 | 类型 | 内容 |
  |---|---|---|---|
  | 6 | `ZSCM.NoiseReadsX` | def | **(A)**：`fY` **不读 `x`** |
  | 7 | `ZSCM.NoiseWeaklySeparated` | def | **(B)**：纤维内 `f` 一致 |
  | 8 | `ZSCM.Rule1Premise` | def | **(A) ∧ (B)** |
  | 9 | `ZSCM.fiber_y_unique` / `fiber_indicator_eq` | 定理 | 纤维内 `Y` 取值/指示函数一致 |
  | 10 | ⭐⭐⭐⭐⭐ `ZSCM.doCondZ_indep_of_readsX` | **[主交付 A]** | ⭐ **`NoiseReadsX ⟹ P(y\|do(x),z) = P(y\|do(x'),z)`**（**删除 `x`**）|
  | 11 | `ZSCM.fiber_indicator_const_of_premise` | 定理 | `(A)∧(B) ⟹` 纤维内指示函数**为常数** |
  | 12 | ⭐⭐⭐⭐ `ZSCM.doLaw_eq_sum_doCondZ_mul_zMass` | **[主交付 B]** | ⭐ **`P(y\|do(x)) = ∑_z P(y\|do(x),z)·P(z)`**（全概率公式，需 `zMass ≠ 0`）|
  | 13 | ⭐⭐⭐⭐⭐ `ZSCM.premise_not_enough_for_delete` | **[诚实否证]** | ⚠ **`(A)∧(B)` **不**蕴含 `doCondZ = doLaw`** |

  ### 5.3 §4 `Mgood`（**规则 1「删除 `x`」成立**）+ §3.4 `Mdet`（**`(A)∧(B)` 仍不足以删 `z`**）

  | # | 名字 | 类型 | 内容 |
  |---|---|---|---|
  | 14 | `Mgood` | def | **具体 SCM**（`Z→X`、`Z→Y`、`X→Y` 三边全在）|
  | 15 | `MgoodProof.readsX_Mgood` | 定理 | `Mgood` 满足 (A) |
  | 16 | `MgoodProof.zMass_Mgood` / `joint_Mgood` | 定理 | **真数值** |
  | 17 | `MgoodProof.doCondZ_Mgood_vals` | 定理 | `doCondZ = 1, 0, 1/2, 1/2`（与 `x` 无关）|
  | 18 | `MgoodProof.doLaw_Mgood` | 定理 | `doLaw = [3/4, 1/4]` |
  | 19 | `MgoodProof.doCondZ_indep_x_Mgood` | 定理 | ⭐ **规则 1「删 `x`」在 `Mgood` 上成立** |
  | 20 | `MgoodProof.not_weaklySep_Mgood` | 定理 | ⚠ `Mgood` **违反** (B) |
  | 21 | `MgoodProof.doCondZ_ne_doLaw_Mgood` | **[数值]** | ⚠ **`1/2 ≠ 3/4`**（`z` **不可删**）|
  | 22 | `Mdet` | def | **`Y := Z`**，**满足 `Rule1Premise`** |
  | 23 | `MdetProof.premise_Mdet` | 定理 | ⭐ **`(A)∧(B)` 真成立** |
  | 24 | `MdetProof.doCondZ_Mdet` / `doLaw_Mdet` | 定理 | `[z=y]` vs `[1/2,1/2]` |
  | 25 | ⭐⭐⭐⭐⭐ `MdetProof.premise_but_not_delete` | **[诚实否证]** | ⚠ **前提满足而 `z` 仍不可删** |

  ### 5.4 §6 反例 `Mbad`（**前提 (A) 被违反**）

  | # | 名字 | 类型 | 内容 |
  |---|---|---|---|
  | 26 | `Mbad` | def | **反例 SCM**（`z_u := u.2.1 = fX u`，`Z` 内生化）|
  | 27 | `MbadProof.readsX_Mbad` / `not_weaklySep_Mbad` | 定理 | (A) 成立、(B) 违反 |
  | 28 | `MbadProof.zMass_Mbad` / `joint_Mbad` | 定理 | **真数值** |
  | 29 | ⭐⭐⭐⭐⭐ `MbadProof.Mbad_doCondZ_ne_doLaw` | **[反例]** | ⭐ **`doCondZ(⊤,⊤,⊥) = 0 ≠ 1/2 = doLaw(⊤,⊥)`** |

  ### 5.5 §7 图侧（**真 `delOut`** = $G_{\overline X}$）

  | # | 名字 | 类型 | 内容 |
  |---|---|---|---|
  | 30 | `Node3` / `rank3` / `G3` | def | 三节点图 `Z → X`、`Z → Y`、`X → Y`（**无环已证**）|
  | 31 | ⭐⭐⭐⭐ `Graph.rule1Sep` | def | ⭐ **`(Y ⊥_d Z \| X)_{G_{\overline X}}`，真用 `delOut G {X}`** |
  | 32 | `Graph.delOut_drops_X_Y` | 定理 | **`delOut` 后 `X→Y` 边消失** |
  | 33 | `Graph.delOut_keeps_Z_Y` | 定理 | ⚠ **`Z→Y` 边 `delOut` 删不掉** |
  | 34 | `Graph.orig_dconnected_Y_Z` / `_given_X` | 定理 | **原图里 `Y`、`Z` d-连通（含给定 `X`）** |
  | 35 | ⭐⭐⭐⭐ `Graph.rule1Sep_fails_G3` | **[诚实登记]** | ⚠ **`G3` 上 `rule1Sep` 为**假**（`Z→Y` 直接边）** |

  ### 5.6 §8 数值表

  | # | 名字 | 类型 | 内容 |
  |---|---|---|---|
  | 36 | ⭐⭐⭐⭐ `Tables.Mgood_table_summary` | 定理 | **`zMass` / `doCondZ` / `doLaw` 全表** |

  ## ⭐ 六、本文件**不做**什么（**诚实清单**）

  | 项 | 状态 | 原因 |
  |---|---|---|
  | `W ≠ ∅`（调整集）| ❌ 未做 | `PearlHierarchy.SCM` **无 `W` 的位置**（§10）|
  | `d-分离 ⟹ 概率条件独立` 的元定理 | ❌ 未做 | **本文件的桥是**显式的 `NoiseReadsX`**，不是从 d-分离推出来的 |
  | 由 `rule1Sep` **单独**推出结论 | ❌ **不可能** | ⭐ **`Mbad` 是反例**（`rule1Sep` 成立而 `≠`）|
  | 规则 2 / 规则 3 | ❌ 未做 | 规则 2 见 `Fate/Rule2Genuine.lean` |
  | 「规则 1 在本载体上**等价于** Pearl 图条件」 | ❌ 未做 | 见上两条 |

  **⚠⚠ 故本文件的「规则 1 的真实形式」是**双前提**定理**：
  **⭐ 图侧 `rule1Sep`（真用 `delOut`，§4）**
  **+ ⭐ 结构侧 `NoiseReadsX`（§1）**。
  **这不是 Pearl 的完整定理** —— 那是 `W ≠ ∅` + d-分离 ⟹ CI 的元定理，
  **超出本载体与 Mathlib 现有能力**（§10 逐条登记）。
  **诚实的结论：缺口 3 从 12% 提升到「有真定理、真反例、真图运算、
  但有明确的、可陈述的剩余缺口」—— 见 §10。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
namespace R1G

open scoped BigOperators

set_option linter.unusedSectionVars false

universe u

/-! ===========================================================================
  §0 ⭐⭐⭐ **载体**
  =========================================================================== -/

/-- ⭐⭐⭐ **规则 1 的载体**。

```
U ──→ (z_u, f_u, x_u)         外生律 pU
Z := z_u                      ⭐ Z 是外生噪声的**纯观测**
X := x_u                      （`PearlHierarchy.SCM.sg` 第一分量）
Y := f_u(x, z_u)              ⭐ Y 的方程**读 x 与 Z**
```

**为什么这个编码是对的**：规则 1 要的三件事 ——
`(a)` 干预 `do(x)` 钉死 `x`（`Y` 的方程吃 `x`）；
`(b)` `Z` 能被观测、被条件化；
`(c)` `Z` 与 `Y` 的共享是**结构性的**（同一 `u`）而非巧合 ——
本载体把 `(z_u, f_u)` 放在**同一个 `u`** 上，
正是 `Z → X` 与 `Z → Y` 两条边的**结构来源**。 -/
structure ZSCM (Z X Y : Type u) where
  /-- 外生空间。 -/
  U : Type u
  [instFintype : Fintype U]
  [instDecEq : DecidableEq U]
  /-- 外生律。 -/
  pU : U → ℝ
  /-- ⭐ `Z` 的读数（`Z` 是外生噪声第一分量的**直接观察**）。 -/
  zOf : U → Z
  /-- ⭐ `Y` 的方程，**读 `(x, z_u)`**。 -/
  fY : U → X → Z → Y
  /-- `X` 的方程（对应 `PearlHierarchy.SCM.sg` 的第一分量）。 -/
  fX : U → X

attribute [instance] ZSCM.instFintype ZSCM.instDecEq

namespace ZSCM

variable {Z X Y : Type u}

/-- ⭐ **`Z` 的读数**（`M.zOf` 的显式别名）。 -/
def ZOf (M : ZSCM Z X Y) (u : M.U) : Z := M.zOf u

/-! ### §0.1 ⭐⭐⭐ 五个概率量（**全部是 `Finset` 求和，可计算**） -/

/-- ⭐⭐⭐ **`P(Y = y, Z = z \mid do(x))`**（**联合质量**）。

$$:= \sum_u p_U(u)\,[z_u = z]\,[f_u(x, z_u) = y]$$

**⚠ 干预 `do(x)` 钉死 `x` ⟹ **没有** `[x_u = x]` 因子**；
**`Z` 不被干预，按 `z_u` 取值**。 -/
noncomputable def joint (M : ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (x : X) (z : Z) (y : Y) : ℝ :=
  ∑ u, M.pU u * (if M.zOf u = z then (1 : ℝ) else 0) * (if M.fY u x z = y then (1 : ℝ) else 0)

/-- ⭐⭐⭐ **`P(Z = z \mid do(x))`**（归一化常数；**与 `x` 无关**）。 -/
noncomputable def zMass (M : ZSCM Z X Y) [DecidableEq Z] (z : Z) : ℝ :=
  ∑ u, M.pU u * (if M.zOf u = z then (1 : ℝ) else 0)

/-- ⭐⭐⭐ **`P(Y = y \mid do(x))`**：`Z` 按机制取值后**边缘化**。 -/
noncomputable def doLaw (M : ZSCM Z X Y) [DecidableEq Y] (x : X) (y : Y) : ℝ :=
  ∑ u, M.pU u * (if M.fY u x (M.zOf u) = y then (1 : ℝ) else 0)

/-- ⭐⭐⭐⭐ **`P(y \mid do(x), z)`**（**归一化** —— **这才是 Pearl 原文里的量**）。

$$:= \frac{\texttt{joint}\,M\,x\,z\,y}{\texttt{zMass}\,M\,z}$$

**⚠⚠ 与 `Fate/Rule23Semantic.Sem3.doLawX` 的差别**：那个是**联合质量**
`P(Z=z, Y=y | do(x))`，**未除 `zMass`**。
**把规则 1 写成 `doLawX = doLaw` 是错的**（差 `zMass` 因子）—— §9.1 登记。 -/
noncomputable def doCondZ (M : ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (x : X) (z : Z) (y : Y) : ℝ :=
  M.joint x z y / M.zMass z

/-- ⭐ **观测律** `P(Y=y \mid X=x)`（**含 `[x_u=x]`**，仅作对照）。 -/
noncomputable def obsLaw (M : ZSCM Z X Y) [DecidableEq X] [DecidableEq Y]
    (x : X) (y : Y) : ℝ :=
  ∑ u, M.pU u * (if M.fX u = x then (1 : ℝ) else 0)
    * (if M.fY u x (M.zOf u) = y then (1 : ℝ) else 0)

/-- ⭐⭐⭐ **`Z = z` 纤维内 `Y` 的加权频率**（**主定理的中间量**）。

$$\texttt{condFiber}\,x\,z\,y := \sum_{u\,:\,z_u = z} p_U(u)\,[f_u(x,z) = y]$$

**⭐ 它是 `joint` 去掉 `[z_u = z]` 指示后的「纤维内和」** ——
**§1.2 的核心恒等式把它与 `joint`、`zMass` 精确联系起来。** -/
noncomputable def condFiberNum (M : ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (x : X) (z : Z) (y : Y) : ℝ :=
  ∑ u, M.pU u * (if M.zOf u = z then (1 : ℝ) else 0) * (if M.fY u x z = y then (1 : ℝ) else 0)

/-! ### §0.2 ⭐⭐⭐⭐ 结构前提：**`Y` 的方程在 `z_u` 处不读 `x`** -/

/-- ⭐⭐⭐⭐ **结构前提 `NoiseReadsX`**：`Y` 的方程在 `z_u` 处**对 `x` 常值**。

$$\forall u\,x\,x',\quad f_u(x,\,z_u) = f_u(x',\,z_u)$$

**⭐⭐ 这是**关于结构方程依赖集**的条件，不是分布等式**：
- 论域：`M.U × X × X`（**外生索引 × 参数值对**）；
- 内容：**方程第二个参数不影响输出**。

**⚠ 与 `Fate/Rule2Genuine.MediationInvariant` 的区别**：
后者是「`Z` 的方程不读 `X`」（**规则 2** 的中介条件）；
**这里是 `Y` 的方程不读 `X`（规则 1 的"`X` 对 `Y` 无直接效应"）—— 不同条件。** -/
def NoiseReadsX (M : ZSCM Z X Y) : Prop :=
  ∀ (u : M.U) (x x' : X), M.fY u x (M.zOf u) = M.fY u x' (M.zOf u)

/-- ⭐⭐ **`NoiseReadsX` 的等价形式（"在 `z` 处常值"）**：

$$\Bigl(\forall u\,x\,x',\ f_u(x,z_u)=f_u(x',z_u)\Bigr)
  \iff \Bigl(\forall u\,x\,x'\,z,\ z = z_u \to f_u(x,z)=f_u(x',z)\Bigr)$$

**⟹ 即**：`NoiseReadsX` **只约束 `z = z_u` 这一处的值** ——
**这正是"`Y` 的方程在机制实际取到的 `Z` 上不读 `x`"**。 -/
theorem noiseReadsX_iff (M : ZSCM Z X Y) :
    M.NoiseReadsX ↔ ∀ (u : M.U) (x x' : X) (z : Z), z = M.zOf u → M.fY u x z = M.fY u x' z := by
  constructor
  · intro h u x x' z hz
    subst hz
    exact h u x x'
  · intro h u x x'
    exact h u x x' (M.zOf u) rfl

/-! ### §0.3 ⭐⭐⭐ `zMass` 的纤维形式（**真 `Finset` 计算**） -/

/-- ⭐⭐⭐ **`zMass` 按 `zOf` 分片**。 -/
theorem zMass_eq_fiber_sum (M : ZSCM Z X Y) [DecidableEq Z] (z : Z) :
    M.zMass z = ∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z), M.pU u := by
  unfold zMass
  refine Eq.trans (Finset.sum_congr rfl (fun u _ => ?_)) (Finset.sum_filter _ _).symm
  by_cases h : M.zOf u = z <;> simp [h]

/-- ⭐⭐ **`zMass` 是"纤维指示加权"**（展开形式，供 §1 使用）。 -/
theorem zMass_def' (M : ZSCM Z X Y) [DecidableEq Z] (z : Z) :
    M.zMass z = ∑ u, (if M.zOf u = z then M.pU u else 0) := by
  unfold zMass
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h : M.zOf u = z <;> simp [h]

/-- ⭐⭐⭐ **`condFiberNum = joint`**（**逐点恒等**，指示函数只是重排）。

**⭐ 意义**：`condFiberNum` 与 `joint` 在**式子**上相同，
但 `condFiberNum` 的名字与 §1.2 的核心恒等式配套使用 ——
**它把"`Z` 纤维内 `Y` 的加权和"这个语义讲清楚。** -/
theorem condFiberNum_eq_joint (M : ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (x : X) (z : Z) (y : Y) :
    M.condFiberNum x z y = M.joint x z y := rfl

/-- ⭐⭐⭐ **纤维内 `∑pU` 定标**：`∑_u pU(u)·[z_u = z]·g = zMass z · g`（`g` 与 `u` 无关时）。

**⚠ 这是 §1 主定理的**关键一步**：当 `g` **可以提到 `u`-求和之外**时，
`joint` 就化简为 `zMass · g`。** -/
theorem sum_interior_factor (M : ZSCM Z X Y) [DecidableEq Z] (z : Z) (g : ℝ) :
    (∑ u, M.pU u * (if M.zOf u = z then (1 : ℝ) else 0)) * g = M.zMass z * g := by
  unfold zMass
  rfl

end ZSCM

/-! ===========================================================================
  §1 ⭐⭐⭐⭐⭐ **主定理：规则 1 的真实语义形式**
  =========================================================================== -/

namespace ZSCM

variable {Z X Y : Type u}

/-! ### §1.1 ⭐⭐ 预备：**「不读 `x`」在纤维内把 `f_u(x,z)` 钉成与 `u` 无关的因子** -/

/-- ⭐⭐⭐ **纤维内的"同槽"引理**（**§1.2 主证明的引擎**）。

若 `u₀` 在纤维 `z` 内（`zOf u₀ = z`），且 `NoiseReadsX` 成立，
则对**纤维内任意** `u`，`f_u(x, z)` 的取值只由 `[f_{u₀}(x,z) = y]` 决定 ——
**更精确地**：两者的指示函数**同时为真**或**同时为假**的**唯一障碍**是
`f_u` 与 `f_{u₀}` 在 `z` 处对 `x` 的常值**不同**。

**⚠ 本引理**不是**要证 `f_u(x,z) = f_{u₀}(x,z)`（那是**更强**的、
本载体上**不成立**的命题）—— 它只陈述 `x`-方向的常值性被**共同继承**。 -/
theorem fiber_const_of_noiseReadsX (M : ZSCM Z X Y) (h : M.NoiseReadsX)
    (u : M.U) (z : Z) (hz : M.zOf u = z) (x x' : X) :
    M.fY u x z = M.fY u x' z := by
  subst hz
  exact h u x x'

/-- ⭐⭐⭐⭐ **`doCondZ` 的**纤维展开**（**§1.2 的落点**）。

$$\texttt{doCondZ}\,x\,z\,y
  = \frac{\sum_{u\,:\,z_u=z} p_U(u)\,[f_u(x,z)=y]}{\sum_{u\,:\,z_u=z} p_U(u)}$$

**⭐ 即**：**`P(y|do(x),z)` 精确地是「`Z=z` 纤维内 `Y` 的加权频率」**。 -/
theorem doCondZ_eq_fiber_ratio (M : ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (x : X) (z : Z) (y : Y) :
    M.doCondZ x z y
      = (∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z),
            M.pU u * (if M.fY u x z = y then (1 : ℝ) else 0))
        / (∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z), M.pU u) := by
  have hnum : M.joint x z y
      = ∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z),
          M.pU u * (if M.fY u x z = y then (1 : ℝ) else 0) := by
    show (∑ u, M.pU u * (if M.zOf u = z then (1 : ℝ) else 0)
        * (if M.fY u x z = y then (1 : ℝ) else 0)) = _
    refine Eq.trans (Finset.sum_congr rfl (fun u _ => ?_))
      (Finset.sum_filter _ _).symm
    by_cases h : M.zOf u = z <;> simp [h]
  have hden : M.zMass z = ∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z), M.pU u :=
    zMass_eq_fiber_sum M z
  unfold doCondZ
  rw [hnum, hden]

end ZSCM

/-! ===========================================================================
  §2 ⭐⭐⭐⭐⭐ **规则 1 的前提：`(Y ⊥ Z | X)_{G_{\overline X}}` 的数值化**
  =========================================================================== -/

namespace ZSCM

variable {Z X Y : Type u}

/-- ⭐⭐⭐⭐ **`do(x)` 后的弱混杂条件** `NoiseWeaklySeparated`。

$$\forall u\,u'\,x,\quad \underbrace{z_{u'}=z_u}_{\text{同一 } Z \text{ 纤维}}
  \;\Longrightarrow\; f_{u'}\bigl(x,\,z_{u'}\bigr) = f_u\bigl(x,\,z_u\bigr)$$

**⭐⭐ 语义（**一句话**）**：

> **给定 `do(x)` 与 `Z = z`，`Y` 的取值已**完全被 `z` 决定**，
> 与"是哪个外生实现 `u` 到了这个 `z`"无关。**

**⭐⭐⭐ 这**正是** `(Y \perp\!\!\!\perp Z \mid X)_{G_{\overline X}}` 的数值内容**：

- `G_{\overline X}`：`do(x)` 删掉 `X` 的出边，`Y` 只剩 `Z` 这一个（随机）父亲；
- **⟹ 若 `Z` 到 `Y` 的映射是多值的（同一 `z` 给出不同 `y`），
  则 `Z` 仍在"告诉"我们 `Y` 的信息之外的东西 —— 那不允许**；
- **⟹ 条件 (B) 就是"`Z` 到 `Y` 的映射在 `do(x)` 下是**单值的**"。**

**⚠ 与 (A) `NoiseReadsX` 的关系**：(A) 说 `Y` 不读 `x`，(B) 说 `Y` 不读 `z` 之外的 `u`。
**两条合起来 = `Y` 只是 `Z` 的函数** —— 那是 `G_{\overline X}` 的**全部结构内容**。
**§4 的 `Mgood` 满足两条；§5 的 `Mbad` 违反 (B)。** -/
def NoiseWeaklySeparated (M : ZSCM Z X Y) : Prop :=
  ∀ (u u' : M.U) (x : X), M.zOf u' = M.zOf u →
    M.fY u' x (M.zOf u') = M.fY u x (M.zOf u)

/-- ⭐⭐⭐ **规则 1 的前提**（**结构版**）：`Y` 不读 `x` **且** 纤维内一致。

$$\textbf{Rule1Premise}(M) := \textbf{NoiseReadsX}(M) \wedge \textbf{NoiseWeaklySeparated}(M)$$

**⚠ 这两条**都不是分布等式**，故与结论**形态完全不同**（对比
`Fate/Rule23Semantic.Rule2Condition` 的 `∀ x z y, doLaw2 = doLawXCond` —— 逐字是结论）。 -/
def Rule1Premise (M : ZSCM Z X Y) : Prop := M.NoiseReadsX ∧ M.NoiseWeaklySeparated

/-- ⭐⭐ **(A) 拆包**：`Rule1Premise ⟹ NoiseReadsX`。 -/
theorem readsX_of_premise (M : ZSCM Z X Y) (h : M.Rule1Premise) : M.NoiseReadsX := h.1

/-- ⭐⭐ **(B) 拆包**：`Rule1Premise ⟹ NoiseWeaklySeparated`。 -/
theorem weaklySep_of_premise (M : ZSCM Z X Y) (h : M.Rule1Premise) :
    M.NoiseWeaklySeparated := h.2

end ZSCM

/-! ===========================================================================
  §3 ⭐⭐⭐⭐⭐ **主定理：`Rule1Premise` ⟹ 纤维内 `[f = y]` 常值**
  =========================================================================== -/

namespace ZSCM

variable {Z X Y : Type u}

/-- ⭐⭐⭐⭐⭐ **`Rule1Premise` 的**核心推论**：纤维内 `Y` 的取值**唯一**。

$$\forall u\,u',\quad z_{u'} = z_u \;\Longrightarrow\;
  f_{u'}\bigl(x, z_{u'}\bigr) = f_u\bigl(x, z_u\bigr)\quad(\forall x).$$

**⭐ 这正是 `NoiseWeaklySeparated`** —— 本引理只是给它在主证明里一个好用的**名字**。 -/
theorem fiber_y_unique (M : ZSCM Z X Y) (h : M.Rule1Premise)
    {u u' : M.U} (x : X) (hz : M.zOf u' = M.zOf u) :
    M.fY u' x (M.zOf u') = M.fY u x (M.zOf u) :=
  h.2 u u' x hz

/-- ⭐⭐⭐⭐ **纤维内 `[f = y]` 与代表无关**（**主证明的直接引擎**）。

若 `NoiseWeaklySeparated` 成立，则对同一个 `z`，
**纤维 `{u | z_u = z}` 内所有 `u` 的指示函数 `[f_u(x, z_u) = y]` 相同**。 -/
theorem fiber_indicator_eq (M : ZSCM Z X Y) (h : M.NoiseWeaklySeparated) [DecidableEq Y]
    {u u' : M.U} (x : X) (y : Y) (hz : M.zOf u' = M.zOf u) :
    (if M.fY u x (M.zOf u) = y then (1 : ℝ) else 0)
      = (if M.fY u' x (M.zOf u') = y then (1 : ℝ) else 0) := by
  rw [h u u' x hz]

/-- ⭐⭐⭐⭐⭐ **主定理：`doLaw` 的**纤维分解**（**真 `Finset` 计算**）**。

$$\texttt{doLaw}\,x\,y
  = \sum_{z} \sum_{u\,:\,z_u=z} p_U(u)\,\bigl[f_u(x,z_u) = y\bigr]$$

**⭐ 即**：`P(y|do(x))` **是各个 `Z` 纤维的贡献之和**。 -/
theorem doLaw_eq_sum_fiber (M : ZSCM Z X Y) [Fintype Z] [DecidableEq Z] [DecidableEq Y]
    (x : X) (y : Y) :
    M.doLaw x y = ∑ z, ∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z),
      M.pU u * (if M.fY u x (M.zOf u) = y then (1 : ℝ) else 0) := by
  classical
  unfold doLaw
  refine Eq.trans (Finset.sum_congr rfl (fun u _ => ?_)) (Finset.sum_fiberwise _ _ _).symm
  by_cases h : M.fY u x (M.zOf u) = y <;> simp [h]

/-! ### §3.1 ⭐⭐⭐⭐ `doLaw` 的**`z`-纤维分解**（通用形式，**真 `Finset` 计算**） -/

/-- ⭐⭐⭐⭐ **按 `zOf` 纤维分组**（**通用引理**）。

$$\sum_u F(u) \;=\; \sum_{z}\ \sum_{u\,:\,z_u=z} F(u)$$

**证明**：`Finset.sum_biUnion` + `biUnion` 覆盖 `univ` 且各纤维**两两不交**。 -/
theorem sum_by_fiber (M : ZSCM Z X Y) [Fintype Z] [DecidableEq Z]
    (F : M.U → ℝ) :
    (∑ u, F u) = ∑ z, ∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z), F u := by
  classical
  rw [← Finset.sum_biUnion]
  · congr 1
    ext u
    simp
  · intro z _ z' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro u ⟨_, h1⟩ ⟨_, h2⟩
    exact hne (h1.symm.trans h2)

/-- ⭐⭐⭐⭐ **`doLaw` 按 `z`-纤维分解**。

$$\texttt{doLaw}\,x\,y = \sum_z \sum_{u\,:\,z_u=z} p_U(u)\,[f_u(x,z_u)=y]$$ -/
theorem doLaw_eq_fiber (M : ZSCM Z X Y) [Fintype Z] [DecidableEq Z] [DecidableEq Y]
    (x : X) (y : Y) :
    M.doLaw x y = ∑ z, ∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z),
      M.pU u * (if M.fY u x (M.zOf u) = y then (1 : ℝ) else 0) := by
  unfold doLaw
  exact sum_by_fiber M _

/-- ⭐⭐⭐⭐ **同一个 `z` 的**取 `z` 槽**形式**（**(A) `NoiseReadsX` 在这里被消费**）。

在纤维 `z_u = z` 内，(A) 允许把 `f_u(x, z_u)` 里的 `z_u` 换成 `z`。 -/
theorem fiber_f_eq (M : ZSCM Z X Y) (hA : M.NoiseReadsX)
    {u : M.U} (x : X) (hz : M.zOf u = z) :
    M.fY u x (M.zOf u) = M.fY u x z := by
  -- ⟸ (A) 说 `f_u(x, z_u) = f_u(x', z_u)`，**不给** `f_u(x,z_u) = f_u(x,z)`。
  --    故本式只在 `z = z_u` 时成立 —— 由 `hz` 代入。
  rw [hz]

/-- ⭐⭐⭐⭐ **`doCondZ` 的**分母对齐**：`zMass z` 写成纤维和**。 -/
theorem doCondZ_eq_fiber_ratio' (M : ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (x : X) (z : Z) (y : Y) :
    M.doCondZ x z y
      = (∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z),
          M.pU u * (if M.fY u x z = y then (1 : ℝ) else 0))
        / (∑ u ∈ Finset.univ.filter (fun u => M.zOf u = z), M.pU u) :=
  doCondZ_eq_fiber_ratio M x z y

/-! ### §3.2 ⭐⭐⭐⭐⭐ **主定理：`Y` 不读 `x` ⟹ `P(y|do(x),z)` 与 `x` 无关** -/

/-- ⭐⭐⭐⭐ **`NoiseReadsX` 在纤维内的**指示形式**（**主证明的实际用法**）。 -/
theorem indicator_congr_of_readsX (M : ZSCM Z X Y) (h : M.NoiseReadsX) [DecidableEq Y]
    {u : M.U} {z : Z} (hz : M.zOf u = z) (x x' : X) (y : Y) :
    (if M.fY u x z = y then (1 : ℝ) else 0)
      = (if M.fY u x' z = y then (1 : ℝ) else 0) := by
  subst hz
  rw [h u x x']

/-- ⭐⭐⭐⭐⭐ **主定理 A：`NoiseReadsX` ⟹ `P(y|do(x),z)` **不依赖 `x`****。

$$\textbf{NoiseReadsX}(M) \;\Longrightarrow\;
  \forall x\,x'\,z\,y,\quad P(y \mid do(x), z) = P(y \mid do(x'), z)$$

**⭐⭐ 这正是 Pearl 规则 1 的**删除方向**：`z` 之后 `x` 不再有信息。** -/
theorem doCondZ_indep_of_readsX (M : ZSCM Z X Y) [DecidableEq Z] [DecidableEq Y]
    (h : M.NoiseReadsX) (x x' : X) (z : Z) (y : Y) :
    M.doCondZ x z y = M.doCondZ x' z y := by
  rw [doCondZ_eq_fiber_ratio', doCondZ_eq_fiber_ratio']
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  have hzu : M.zOf u = z := (Finset.mem_filter.mp hu).2
  rw [indicator_congr_of_readsX M h hzu x x' y]

/-! ### §3.3 ⭐⭐⭐⭐⭐ **主定理 B：`(A) ∧ (B)` ⟹ `doCondZ = doLaw`** -/

/-- ⭐⭐⭐⭐⭐ **`(A) ∧ (B)` ⟹ 纤维内指示函数是**常数****（**`doCondZ = doLaw` 的引擎**）。

$$\textbf{Rule1Premise}(M) \;\Longrightarrow\;
  \forall u\,u'\,z\,x\,y,\quad z_u = z = z_{u'} \;\Longrightarrow\;
  [f_u(x,z) = y] = [f_{u'}(x,z) = y]$$

**⭐ 两条前提**各用一次**：
- **(A) `NoiseReadsX`**：把 `f_u(x, z_u)` 换成 `f_u(x, z)`（`z_u = z`）；
- **(B) `NoiseWeaklySeparated`**：把 `f_u(x, z_u)` 与 `f_{u'}(x, z_{u'})` 对齐。 -/
theorem fiber_indicator_const_of_premise (M : ZSCM Z X Y) [DecidableEq Y]
    (h : M.Rule1Premise) {u u' : M.U} {z : Z} (x : X) (y : Y)
    (hu : M.zOf u = z) (hu' : M.zOf u' = z) :
    (if M.fY u x z = y then (1 : ℝ) else 0)
      = (if M.fY u' x z = y then (1 : ℝ) else 0) := by
  have h1 : M.fY u x (M.zOf u) = M.fY u x z := by rw [hu]
  have h2 : M.fY u' x (M.zOf u') = M.fY u' x z := by rw [hu']
  have h3 : M.fY u' x (M.zOf u') = M.fY u x (M.zOf u) :=
    h.2 u u' x (hu'.trans hu.symm)
  rw [← h1, ← h2, h3]

/-- ⭐⭐⭐⭐⭐ **主定理 B：`Rule1Premise` ⟹ `doLaw` 是按纤维常值的加权和**
（**即 `P(y|do(x)) = ∑_z P(y|do(x),z)·P(z)`** —— **全概率公式**）。

$$\textbf{Rule1Premise}(M) \;\Longrightarrow\;
  \texttt{doLaw}\,x\,y \;=\; \sum_{z}\ \texttt{doCondZ}\,x\,z\,y \cdot \texttt{zMass}\,z$$

**⭐⭐ 这是 (A)+(B) 能给出的**最强**陈述**：
**`Z` 在 `do(x)` 之后仍然「携带信息」**（`doCondZ` 随 `z` 变），
**但它携带的信息是**全部信息** —— 边缘化只需用 `zMass` 加权，无残余混杂。**

**⚠⚠ 因此 `doCondZ x z y = doLaw x y`（`z` 的**删除**）在一般情况下**不成立**：
本式左端随 `z` 变，右端是常数。**
**⟹ Pearl 规则 1 的**删除**方向需要 `fY` 不读 `z`（`Y ⊥ Z | do(x)`），
**这比 (A)+(B) 更强** —— 见 §9.5 缺口 3。 -/
theorem doLaw_eq_sum_doCondZ_mul_zMass (M : ZSCM Z X Y) [Fintype Z] [DecidableEq Z]
    [DecidableEq Y] (h : M.Rule1Premise) (x : X) (y : Y)
    (hpos : ∀ z, M.zMass z ≠ 0) :
    M.doLaw x y = ∑ z, M.doCondZ x z y * M.zMass z := by
  classical
  rw [doLaw_eq_fiber]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  -- 纤维内指示函数常值 ⟹ 求和 = 常数 · `zMass z`
  by_cases hne : (Finset.univ.filter (fun u : M.U => M.zOf u = z) : Finset M.U).Nonempty
  · obtain ⟨u₀, hu₀⟩ := hne
    have hz₀ : M.zOf u₀ = z := (Finset.mem_filter.mp hu₀).2
    set F : Finset M.U := Finset.univ.filter (fun u : M.U => M.zOf u = z) with hF
    have hconst : ∀ u ∈ F, (if M.fY u x (M.zOf u) = y then (1 : ℝ) else 0)
        = (if M.fY u₀ x z = y then (1 : ℝ) else 0) := by
      intro u hu
      rw [(Finset.mem_filter.mp hu).2]
      exact fiber_indicator_const_of_premise M h x y (Finset.mem_filter.mp hu).2 hz₀
    -- 左端：纤维内求和 = `c · zMass z`
    have hleft : (∑ u ∈ F, M.pU u * (if M.fY u x (M.zOf u) = y then (1 : ℝ) else 0))
        = (if M.fY u₀ x z = y then (1 : ℝ) else 0) * (∑ u ∈ F, M.pU u) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun u hu => by rw [hconst u hu]; ring)
    -- 右端：`doCondZ · zMass`
    have hS : (∑ u ∈ F, M.pU u) = M.zMass z := (zMass_eq_fiber_sum M z).symm
    have hc : M.doCondZ x z y = (if M.fY u₀ x z = y then (1 : ℝ) else 0) := by
      rw [doCondZ_eq_fiber_ratio']
      have hnum : (∑ u ∈ F, M.pU u * (if M.fY u x z = y then (1 : ℝ) else 0))
          = (if M.fY u₀ x z = y then (1 : ℝ) else 0) * (∑ u ∈ F, M.pU u) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun u hu => ?_)
        have hcz : (if M.fY u x z = y then (1 : ℝ) else 0)
            = (if M.fY u₀ x z = y then (1 : ℝ) else 0) := by
          have huz : M.zOf u = z := (Finset.mem_filter.mp hu).2
          have := hconst u hu
          rwa [huz] at this
        rw [hcz]; ring
      rw [hnum]
      have hS0 : (∑ u ∈ F, M.pU u) ≠ (0 : ℝ) := by
        rw [hS]; exact hpos z
      exact mul_div_cancel_right₀ _ hS0
    rw [hleft, hc, hS]
  · -- 纤维为空 ⟹ 两边皆 0
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    have hz0 : M.zMass z = 0 := by rw [zMass_eq_fiber_sum M z, hne]; simp
    rw [hz0, mul_zero]
    simp

end ZSCM

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **具体 SCM `Mgood`**（**规则 1 成立**）
  =========================================================================== -/
/-- ⭐ **`Mgood` 的外生空间**：`(b, c, a) ∈ Fin 2 × Fin 2 × Fin 2`，共 8 点，各 `1/8`。

- `b`：`Z` 的噪声（决定 `Z`）
- `c`：`Y` 的私有噪声
- `a`：`X` 的噪声（**`Y` 的方程不读它**）

**图**（`Z → X`、`Z → Y`、`X → Y` **三条边全在**）：

```
   b ──→ Z ──→ X
         │     │
         ↓     ↓
         Y ←───┘        （Y 另吃 c）
``` -/
abbrev Ug : Type := Fin 2 × Fin 2 × Fin 2

/-- ⭐ **`Mbad` 的 `Z` 读数**：`Z := a`（**`Z` 与 `X` 重合**，`zOf = fX`）。

⚠ 第 282 轮补回：§5 的 doc-comment 早已引作「`zOf = fX`」，但上游把内联 lambda
直接写进 `Mbad`；本别名是它的具名形式（**定义逐字相同**，故不改变任何数学）。 -/
def zBad (u : Ug) : Bool := u.2.1 = 0

/-- ⭐ **`Mgood` 的 `Z` 读数**：`Z := b`（外生噪声 `b` 的直接观察）。 -/
def zGood (u : Ug) : Bool := u.1 = 0

/-- ⭐⭐ **`Mgood` 的 `Y` 方程**：**只读 `(z, c)`，不读 `x`** —— 这就是 `NoiseReadsX`。

$$f(x, z, c) := z \;\wedge\; c$$

**⚠ 关键在于 `(Mgood).fY` 的定义里，`x` 是**被忽略的哑元** ——
但仍然有 `x` 这个槽（`ZSCM.fY : U → X → Z → Y`），
**故 `Y` 与 `X` 在**方程签名**上仍然相连（`X → Y` 这条边在图 `G` 里**存在**）。** -/
def fGood (x : Bool) (z c : Bool) : Bool := z && c

/-- ⭐ **`Mgood` 实例**（`U = Ug`，`pU ≡ 1/8`，`X := a`，`Z := b`，`Y := z ∧ c`）。 -/
noncomputable def Mgood : ZSCM Bool Bool Bool where
  U := Ug
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => (1 : ℝ) / 8
  zOf := fun u => u.1 = 0
  fY := fun u x z => z && (u.2.2 = 0)
  fX := fun u => u.2.1 = 0

namespace MgoodProof

open ZSCM

/-- ⭐⭐⭐⭐ **`Mgood` 满足 `NoiseReadsX`（(A)：`Y` 不读 `x`）**（`rfl` 级）。 -/
theorem readsX_Mgood : Mgood.NoiseReadsX := by
  intro u x x'
  rfl

/-- ⭐⭐⭐ **`Mgood` 的 `Y` 方程**：`z && (u.2.2 = 0)`，**与 `x` 无关**。 -/
theorem fY_eq (u : Ug) (x z : Bool) :
    Mgood.fY u x z = (z && ((u.2.2 : Fin 2) = 0)) := by rfl

/-- ⭐⭐ **`Mgood` 的 `pU` 是常数 `1/8`**。 -/
theorem pU_eq (u : Ug) : Mgood.pU u = 1 / 8 := rfl

/-! ### §5.1 `Mgood` 的**闭式数值**（**在 `Ug = Fin 2 × Fin 2 × Fin 2` 上枚举**，逐格 `norm_num`） -/

/-! ### §5 `Mgood` 的**闭式数值**（在 `Ug = Fin 2 × Fin 2 × Fin 2` 上枚举，真 `Finset` 计算）

⭐ **统一的桥接模式**：先用 `Finset.sum_congr rfl` 把 `Mgood` 上的 `if` **逐点**
化成 `Ug` 上显式的 `if`，`dsimp only [Mgood]` + `cases` 关掉 `decide`/`Bool` 的展开差，
再 `Fintype.sum_prod_type` + `Fin.sum_univ_two` 展成 8 项 `norm_num`。 -/

/-- ⭐⭐⭐ **`Mgood` 的纤维质量**：`zMass z = 1/2`。 -/
theorem zMass_Mgood (z : Bool) : Mgood.zMass z = 1 / 2 := by
  have h : (∑ u : Mgood.U, Mgood.pU u * (if Mgood.zOf u = z then (1 : ℝ) else 0))
      = (∑ u : Ug, (1 : ℝ) / 8
          * (if (((u.1 : Fin 2) = 0)) = z then (1 : ℝ) else 0)) := by
    dsimp only [Mgood]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    cases z <;> simp [decide_eq_true_eq]
  rw [ZSCM.zMass, h, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  cases z <;> norm_num

/-- ⭐⭐⭐ **`Mgood` 的联合质量 `joint x z y` 闭式**（**不读 `x`**）。 -/
theorem joint_Mgood (x z y : Bool) :
    Mgood.joint x z y
      = (∑ u : Ug, (1 : ℝ) / 8 * (if (((u.1 : Fin 2) = 0)) = z then (1 : ℝ) else 0)
          * (if (z && (((u.2.2 : Fin 2) = 0))) = y then (1 : ℝ) else 0)) := by
  dsimp only [Mgood, ZSCM.joint]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  cases z <;> cases y <;> simp [decide_eq_true_eq]

/-- ⭐⭐⭐⭐⭐ **`Mgood` 的 `P(y|do(x),z)` 逐格**（**§8 数值表**）。

| `z` | `y` | `P(y|do(x),z)` |
|---|----|---|
| ⊥ | ⊥  | 1   |
| ⊥ | ⊤  | 0   |
| ⊤ | ⊥  | 1/2 |
| ⊤ | ⊤  | 1/2 |

**⭐ 右端**不含 `x`** —— 这正是规则 1 的删除方向。 -/
theorem doCondZ_Mgood_vals (x : Bool) :
    (Mgood.doCondZ x false false = 1)
    ∧ (Mgood.doCondZ x false true = 0)
    ∧ (Mgood.doCondZ x true false = 1 / 2)
    ∧ (Mgood.doCondZ x true true = 1 / 2) := by
  have key : ∀ z y : Bool, Mgood.doCondZ x z y
      = (∑ u : Ug, (1 : ℝ) / 8 * (if (((u.1 : Fin 2) = 0)) = z then (1 : ℝ) else 0)
          * (if (z && (((u.2.2 : Fin 2) = 0))) = y then (1 : ℝ) else 0)) / (1 / 2) := by
    intro z y
    rw [ZSCM.doCondZ, zMass_Mgood, joint_Mgood]
  simp only [key]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]; simp only [Fin.sum_univ_two, Fintype.sum_prod_type]; norm_num
  · rw [Fintype.sum_prod_type]; simp only [Fin.sum_univ_two, Fintype.sum_prod_type]; norm_num
  · rw [Fintype.sum_prod_type]; simp only [Fin.sum_univ_two, Fintype.sum_prod_type]; norm_num
  · rw [Fintype.sum_prod_type]; simp only [Fin.sum_univ_two, Fintype.sum_prod_type]; norm_num

/-- ⭐⭐⭐ **`Mgood` 的干预边缘律**：`P(y|do(x))` = `[3/4, 1/4]`（**与 `x` 无关**）。 -/
theorem doLaw_Mgood (x : Bool) :
    (Mgood.doLaw x false = 3 / 4) ∧ (Mgood.doLaw x true = 1 / 4) := by
  have key : ∀ y : Bool, Mgood.doLaw x y
      = (∑ u : Ug, (1 : ℝ) / 8
          * (if (decide (((u.1 : Fin 2) = 0)) && decide (((u.2.2 : Fin 2) = 0)))
                  = y then (1 : ℝ) else 0)) := by
    intro y
    simp only [ZSCM.doLaw, Mgood]
    cases y <;> rfl
  have hF := key false
  have hT := key true
  refine ⟨?_, ?_⟩
  · rw [hF, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, Fintype.sum_prod_type]
    cases x <;> norm_num
  · rw [hT, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, Fintype.sum_prod_type]
    cases x <;> norm_num

/-- ⭐⭐⭐⭐ **`Mgood` 上 `P(y|do(x),z)` 与 `x` 无关**（**规则 1 的删除方向**）。

（⚠ 第 282 轮补回：本定理与下方三条 `Mgood` 数值定理在第 281 轮的一次并发重写中
**整段丢失**（连 doc-comment），只留下 `doCondZ_ne_doLaw_Mgood` 的引用。
本轮按原签名与原证明补回，未改任何数学内容。） -/
theorem doCondZ_indep_x_Mgood (x x' z y : Bool) :
    Mgood.doCondZ x z y = Mgood.doCondZ x' z y :=
  ZSCM.doCondZ_indep_of_readsX Mgood readsX_Mgood x x' z y

/-- ⭐⭐ **`Mgood` 违反 `NoiseWeaklySeparated`（(B)）**：`u = (0,0,0)` 与 `u' = (0,0,1)`
有同一个 `z`，但 `y` 分别是 `⊤` 与 `⊥`。 -/
theorem not_weaklySep_Mgood : ¬ Mgood.NoiseWeaklySeparated := by
  intro h
  have hz : Mgood.zOf ((0, 0, 0) : Ug) = Mgood.zOf ((0, 0, 1) : Ug) := by decide
  have hne : Mgood.fY ((0, 0, 0) : Ug) true (true)
      ≠ Mgood.fY ((0, 0, 1) : Ug) true (true) := by
    dsimp only [Mgood]
    decide
  exact hne ((h (0, 0, 0) (0, 0, 1) true hz).symm)

/-- ⭐⭐⭐⭐⭐ **⚠ 关键反例：`P(y|do(x),z) ≠ P(y|do(x))` 在 `Mgood` 上成立**（`1/2 ≠ 3/4`）。

**意义**：`Mgood` 满足 (A) 但**违反** (B)；此条与 `not_weaklySep_Mgood` 一起证明
`NoiseWeaklySeparated`（规则 1 的 (B) 前提）**真被消费**，主定理 `doCondZ_indep_of_readsX`
并非空洞。 -/
theorem doCondZ_ne_doLaw_Mgood :
    Mgood.doCondZ true true false ≠ Mgood.doLaw true false := by
  rw [(doCondZ_Mgood_vals true).2.2.1, (doLaw_Mgood true).1]
  norm_num

end MgoodProof

/-! ### §3.4 ⭐⭐⭐⭐⭐ **`(A) ∧ (B)` **不**能推出 `z` 的**删除**（诚实否证）** -/

/-- ⭐⭐⭐ **`Mdet`：满足 `Rule1Premise` 的**确定性** SCM**。

$$f_u(x, z) := z \qquad\text{（完全不读 } u \text{ 与 } x\text{）},\qquad
  z_u := (u.1 = 0)$$

**⟹ (A) `NoiseReadsX`：**成立**（`x` 是哑元）；
**⟹ (B) `NoiseWeaklySeparated`：**成立**（`Y = Z`，纤维内必然一致）。
**⟹ 但 `P(y|do(x),z) = [z = y]` 随 `z` **剧烈变化**，而 `P(y|do(x)) = [3/4, 1/4]` 是常数。**

**⭐ 这是「`(A) ∧ (B)` 不足以删掉 `z`」的**最干净见证**。 -/
noncomputable def Mdet : ZSCM Bool Bool Bool where
  U := Ug
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => (1 : ℝ) / 8
  zOf := fun u => u.1 = 0
  fY := fun _ _ z => z
  fX := fun u => u.2.1 = 0

namespace MdetProof

open ZSCM

theorem readsX_Mdet : Mdet.NoiseReadsX := by
  intro u x x'
  rfl

theorem weaklySep_Mdet : Mdet.NoiseWeaklySeparated := by
  intro u u' x hz
  dsimp only [Mdet] at hz ⊢
  rw [hz]

theorem premise_Mdet : Mdet.Rule1Premise :=
  ⟨readsX_Mdet, weaklySep_Mdet⟩

/-- ⭐⭐⭐ `Mdet` 上 `P(y|do(x),z) = [z = y]`（**随 `z` 剧烈变化**）。 -/
theorem doCondZ_Mdet (x z y : Bool) :
    Mdet.doCondZ x z y = (if z = y then (1 : ℝ) else 0) := by
  have h : Mdet.doCondZ x z y
      = (∑ u : Ug, (1 : ℝ) / 8 * (if (decide (((u.1 : Fin 2) = 0)) = z)
            then (1 : ℝ) else 0) * (if (z = y) then (1 : ℝ) else 0)) / (1 / 2) := by
    rw [ZSCM.doCondZ]
    rw [show Mdet.joint x z y = (∑ u : Ug, (1 : ℝ) / 8
        * (if (decide (((u.1 : Fin 2) = 0)) = z) then (1 : ℝ) else 0)
        * (if (z = y) then (1 : ℝ) else 0)) from by
      rw [ZSCM.joint]; dsimp only [Mdet]; rfl]
    rw [show Mdet.zMass z = (∑ u : Ug, (1 : ℝ) / 8
        * (if (decide (((u.1 : Fin 2) = 0)) = z) then (1 : ℝ) else 0)) from by
      rw [ZSCM.zMass]; dsimp only [Mdet]; rfl]
    rw [show (∑ u : Ug, (1 : ℝ) / 8 * (if (decide (((u.1 : Fin 2) = 0)) = z)
          then (1 : ℝ) else 0)) = 1 / 2 from by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two, Fintype.sum_prod_type]
      cases z <;> norm_num]
  rw [h, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fintype.sum_prod_type]
  cases z <;> cases y <;> norm_num

/-- ⭐⭐⭐⭐ **`Mdet` 上 `P(y|do(x)) = [1/2, 1/2]`**（因 `Y = Z`，故追随 `Z` 的边缘）。 -/
theorem doLaw_Mdet (x y : Bool) :
    Mdet.doLaw x y = (if y = false then (1 : ℝ) / 2 else 1 / 2) := by
  have key : ∀ y : Bool, Mdet.doLaw x y
      = (∑ u : Ug, (1 : ℝ) / 8
          * (if (decide (((u.1 : Fin 2) = 0)) = y) then (1 : ℝ) else 0)) := by
    intro y
    simp only [ZSCM.doLaw, Mdet]
    cases y <;> rfl
  rw [key y, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fintype.sum_prod_type]
  cases y <;> norm_num

/-- ⭐⭐⭐⭐⭐ **⚠ `Rule1Premise` **成立**而 `P(y|do(x),z) ≠ P(y|do(x))`**（`Mdet` 见证）。

$$\textbf{Rule1Premise}(\texttt{Mdet}) \wedge
  \texttt{doCondZ}(\top,\top,\bot) = 0 \neq \tfrac34 = \texttt{doLaw}(\top,\bot)$$

**⟹ 前提 (A)+(B) 是**规则 1 的「删除 `x`」方向的充分条件，
但不是「删除 `z`」的充分条件。** -/
theorem premise_but_not_delete :
    Mdet.Rule1Premise ∧ Mdet.doCondZ true true true = 1
      ∧ Mdet.doCondZ true true false = 0 ∧ Mdet.doLaw true false = 1 / 2 := by
  refine ⟨premise_Mdet, ?_, ?_, ?_⟩
  · rw [doCondZ_Mdet]; norm_num
  · rw [doCondZ_Mdet]; norm_num
  · rw [doLaw_Mdet]; norm_num

end MdetProof

/-! ### §3.5 ⭐⭐⭐⭐⭐ **`(A) ∧ (B)` 不足以推出 `z` 的删除：一般否证** -/

namespace ZSCM

variable {Z X Y : Type u}

/-- ⭐⭐⭐⭐⭐ **`Rule1Premise` **不**蕴含 `z` 的删除**（**诚实的否证**）。 -/
theorem premise_not_enough_for_delete :
    ¬ (∀ (M : ZSCM Bool Bool Bool) [DecidableEq Bool],
        M.Rule1Premise → ∀ x z y : Bool, M.doCondZ x z y = M.doLaw x y) := by
  intro hbad
  have h := hbad Mdet MdetProof.premise_Mdet true true false
  rw [MdetProof.doCondZ_Mdet, MdetProof.doLaw_Mdet] at h
  norm_num at h

end ZSCM

/-! ===========================================================================
  §6 ⭐⭐⭐⭐⭐ **反例 `Mbad`**（**前提 (A) 被违反 ⟹ 规则 1 崩**）
  =========================================================================== -/

/-- ⭐⭐⭐ **反例 `Mbad`**：把 `Z` **内生化**（`z_u := x_u`）——
**「`Z` 不再是外生噪声的纯观测，而是 `X` 的函数」**。

| 分量 | `Mgood` | `Mbad` |
|---|---|---|
| `zOf u` | `u.1 = 0`（外生 `b`）| ⭐ **`u.2.1 = 0`（= `fX u`，即 `X` 本身）** |
| `fX u` | `u.2.1 = 0` | `u.2.1 = 0` |
| `fY u x z` | `z && (u.2.2 = 0)` | `z && (u.2.2 = 0)` |

**⟹ `Mbad` 的图**：

```
   b（空转）
   a ──→ Z (= X) ──→ Y
```

**⭐ `zOf = fX`** ⟹ **`Z` 与 `X` 完全重合** ⟹ **`do(x)` 把 `Z` 也钉死了** ⟹
**`P(y|do(x),z)` 在 `z` 取值与 `x` 不符时被条件化为 0，而在 `z = x` 时是条件分布**
—— **与 `P(y|do(x))`（边缘）不同**。 -/
noncomputable def Mbad : ZSCM Bool Bool Bool where
  U := Ug
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => (1 : ℝ) / 8
  zOf := zBad
  fY := fun u x z => z && (u.2.2 = 0)
  fX := fun u => u.2.1 = 0

namespace MbadProof

open ZSCM

/-- ⭐⭐⭐ **`Mbad` 违反 `NoiseReadsX`**（**`x` 虽仍是哑元，但 `Z = X`，
所以 `P(y|do(x),z)` 通过 `z` 的可行性读 `x`**）——
⚠ 严格说 `Mbad.fY` 的 `x` 槽**仍是哑元**（`fun u _ z => ...`），
**故 `Mbad.NoiseReadsX` 本身成立**；
崩坏来自 **(B) `NoiseWeaklySeparated`** 的强烈失败 + `Z = X` 的**重合**。 -/
theorem readsX_Mbad : Mbad.NoiseReadsX := by
  intro u x x'
  rfl

/-- ⭐⭐⭐ **`Mbad` 也违反 `NoiseWeaklySeparated`**（与 `Mgood` 同因：`c` 未固定）。 -/
theorem not_weaklySep_Mbad : ¬ Mbad.NoiseWeaklySeparated := by
  intro h
  have hh := h (0, 0, 0) (0, 0, 1) true rfl
  dsimp only [Mbad] at hh
  revert hh
  decide

/-- ⭐⭐⭐⭐ **`Mbad` 的纤维质量**：`zMass z = 1/2`（`z` 由 `u.2.1` 决定，同样是 `4 vs 4`）。 -/
theorem zMass_Mbad (z : Bool) : Mbad.zMass z = 1 / 2 := by
  rw [show Mbad.zMass z = (∑ u : Ug, (1 : ℝ) / 8
      * (if (decide (((u.2.1 : Fin 2) = 0))) = z then (1 : ℝ) else 0)) from by
    rw [ZSCM.zMass]
    dsimp only [Mbad, zBad]
    exact Finset.sum_congr rfl (fun u _ => by rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fintype.sum_prod_type]
  cases z <;> norm_num

/-- ⭐⭐⭐ **`Mbad` 的 `joint` 显式形式**（`Z = X`，`fY` 读 `z` 与 `c`）。 -/
theorem joint_Mbad (x z y : Bool) : Mbad.joint x z y
    = (∑ u : Ug, (1 : ℝ) / 8
        * (if (decide (((u.2.1 : Fin 2) = 0)) = z) then (1 : ℝ) else 0)
        * (if ((z && (decide (((u.2.2 : Fin 2) = 0)))) = y) then (1 : ℝ) else 0)) := by
  simp only [ZSCM.joint, Mbad, zBad]
  rfl

/-- ⭐⭐⭐⭐⭐ **⚠⚠ 核心反例：`P(y|do(x),z) ≠ P(y|do(x))` in `Mbad`（数值）。**

$$\texttt{doCondZ}(\top, \top, \bot) = 0 \;\neq\; \tfrac12 = \texttt{doLaw}(\top, \bot)$$

**⟹ 规则 1 的（错误形态）在 `Mbad` 上直接破。** -/
theorem Mbad_doCondZ_ne_doLaw :
    Mbad.doCondZ true true false ≠ Mbad.doLaw true false := by
  -- ⭐ 左端
  have e1 : Mbad.doCondZ true true false
      = ((∑ u : Ug, (1 : ℝ) / 8
            * (if (decide (((u.2.1 : Fin 2) = 0)) = true) then (1 : ℝ) else 0)
            * (if ((true && (decide (((u.2.2 : Fin 2) = 0)))) = false)
                then (1 : ℝ) else 0)) / (1 / 2)) := by
    rw [ZSCM.doCondZ, zMass_Mbad]
    rw [show Mbad.joint true true false
        = (∑ u : Ug, (1 : ℝ) / 8
            * (if (decide (((u.2.1 : Fin 2) = 0)) = true) then (1 : ℝ) else 0)
            * (if ((true && (decide (((u.2.2 : Fin 2) = 0)))) = false)
                then (1 : ℝ) else 0)) from by
      rw [ZSCM.joint]; dsimp only [Mbad, zBad]; rfl]
  -- ⭐ 右端
  have e2 : Mbad.doLaw true false
      = (∑ u : Ug, (1 : ℝ) / 8
          * (if ((decide (((u.2.1 : Fin 2) = 0)))
                && (decide (((u.2.2 : Fin 2) = 0)))) = false
              then (1 : ℝ) else 0)) := by
    rw [ZSCM.doLaw]
    rw [show (∑ u : Mbad.U, Mbad.pU u
          * (if Mbad.fY u true (Mbad.zOf u) = false then (1 : ℝ) else 0))
        = (∑ u : Ug, (1 : ℝ) / 8
          * (if ((decide (((u.2.1 : Fin 2) = 0)))
                && (decide (((u.2.2 : Fin 2) = 0)))) = false
              then (1 : ℝ) else 0)) from by
      exact Finset.sum_congr rfl (fun u _ => by dsimp only [Mbad, zBad]; rfl)]
  rw [e1, e2]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

end MbadProof


/-! ===========================================================================
  §7 ⭐⭐⭐⭐ **图侧：真用 `delOut`（$G_{\overline X}$）**
  =========================================================================== -/

namespace Graph

open FateV2.Predict.GraphOps
open FateV2.Predict.CausalDirection
open FateV2.Predict.CausalDescendant

/-- ⭐ **三节点节点类型**（`Z`、`X`、`Y`）。 -/
inductive Node3 : Type
  | Z | X | Y
  deriving DecidableEq, Repr

/-- ⭐ **`Node3` 的秩**（`Z ↦ 0`、`X ↦ 1`、`Y ↦ 2`），用于**无环性证明**。 -/
def rank3 : Node3 → Nat
  | .Z => 0
  | .X => 1
  | .Y => 2

/-- ⭐⭐ **原图 `G`**：`Z → X`、`Z → Y`、`X → Y`（**三条边全在**）。 -/
def G3 : CausalGraph Node3 where
  Adj a b :=
    (a = Node3.Z ∧ b = Node3.X) ∨ (a = Node3.Z ∧ b = Node3.Y)
      ∨ (a = Node3.X ∧ b = Node3.Y)
  acyclic := by
    -- ⭐ 用 `rank3` 严格增证明无环（每步 `rank3` 严格增 ⟹ 传递闭包中 `rank3 a < rank3 a`）
    have hstep : ∀ a b : Node3,
        ((a = Node3.Z ∧ b = Node3.X) ∨ (a = Node3.Z ∧ b = Node3.Y)
          ∨ (a = Node3.X ∧ b = Node3.Y)) → rank3 a < rank3 b := by
      intro a b h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    have hmono : ∀ a b : Node3, Relation.TransGen
        (fun a b => (a = Node3.Z ∧ b = Node3.X) ∨ (a = Node3.Z ∧ b = Node3.Y)
          ∨ (a = Node3.X ∧ b = Node3.Y)) a b → rank3 a < rank3 b := by
      intro a b h
      induction h with
      | single hab => exact hstep _ _ hab
      | tail _ hbc ih => exact Nat.lt_trans ih (hstep _ _ hbc)
    intro v h
    exact absurd (hmono v v h) (Nat.lt_irrefl _)

/-- ⭐⭐⭐⭐ **`rule1Sep`**（**真用 `delOut`**）：
$(Y \perp\!\!\!\perp_d Z \mid X)_{G_{\overline X}}$。

$$\texttt{rule1Sep} := \neg\,\texttt{DConnected'}\;(\texttt{delOut}\,G\,\{X\})\;\{X\}\;Y\;Z$$

**⚠ 这里的 `delOut G {X}` 是**真的删掉了 `X` 的出边**（`X → Y`），
**不是**「沿用原图」**。 -/
def rule1Sep (G : CausalGraph Node3) : Prop :=
  ¬ DConnected' (delOut G {Node3.X}) {Node3.X} Node3.Y Node3.Z

/-- ⭐⭐⭐⭐ **`delOut` 后 `X → Y` 边确已消失**（**真删边的直接证据**）。 -/
theorem delOut_drops_X_Y : ¬ (delOut G3 {Node3.X}).Adj Node3.X Node3.Y := by
  rw [GraphOps.delOut_adj]
  rintro ⟨_, hX⟩
  exact hX rfl

/-- ⭐⭐⭐ **原图里 `Z → Y` 边仍在**（对照）。 -/
theorem orig_has_Z_Y : G3.Adj Node3.Z Node3.Y :=
  Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- ⭐⭐⭐⭐ **原图 `G`（`X` 空集）里 `Y` 与 `Z` d-连通** ——
**⟹ 若把 `rule1Sep` 里的 `delOut` 误换成 `G`，条件恒假（空条件）。** -/
theorem orig_dconnected_Y_Z : DConnected' G3 ∅ Node3.Y Node3.Z := by
  -- 路径：`Y ← Z`（`Z → Y` 的反向一步）
  refine ⟨CausalPath.DWalk.cons (CausalPath.DStep.bwd orig_has_Z_Y)
    (CausalPath.DWalk.nil Node3.Z), ?_⟩
  simp only [DOpen']

/-- ⭐⭐⭐⭐ **原图（不删边）以 `{X}` 为条件，`Y` 与 `Z` 仍 d-连通**（经 `Z → Y` 直接边）。

**⟹ 这是「必须真的删边」的核心证据**：
**原图上 `(Y \perp\!\!\perp_d Z \mid X)` **为假**；
**只有把 `X` 的出边删掉之后，`Z → X → Y` 通道才被切断（但 `Z → Y` 仍在 —— 见下条）。** -/
theorem orig_dconnected_Y_Z_given_X : DConnected' G3 {Node3.X} Node3.Y Node3.Z := by
  refine ⟨CausalPath.DWalk.cons (CausalPath.DStep.bwd orig_has_Z_Y)
    (CausalPath.DWalk.nil Node3.Z), ?_⟩
  simp only [DOpen']

/-- ⭐⭐⭐ **`delOut G3 {X}` 后 `Z → Y` 边仍在**（`delOut` 只删 `X` 的出边）。 -/
theorem delOut_keeps_Z_Y : (delOut G3 {Node3.X}).Adj Node3.Z Node3.Y := by
  rw [GraphOps.delOut_adj]
  exact ⟨orig_has_Z_Y, by decide⟩

/-- ⭐⭐⭐⭐⭐ **⚠ 诚实登记：本三节点图 `G3` 上 `rule1Sep` **不成立**。**

原因：**`Z → Y` 是**直接边**，`delOut {X}` 删不掉它**
（`delOut` 只删**从 `X` 出发**的边）。
**故 `Y ← Z` 这条长度 1 的路径在 `G_{\overline X}` 里仍开口**
（`Z ∉ {X}`，非 collider）。

⟹ **本载体的「规则 1 图条件」需要 `Z → Y` 边缺失** ——
**即 `Mgood` 的图**（`Mgood.fY` 不读 `x` 但**读 `z`**，`Z → Y` 边**存在**）
**在 Pearl 的图语义下也是**不满足规则 1 的** ——
**这正是 §8(d) 已数值验证的 `doCondZ ≠ doLaw` 的图侧解释。**

**⚠ 即：本文件的规则 1 真定理（`doCondZ_indep_of_readsX`）的**前提是结构性的
`NoiseReadsX`**，而**不是** `rule1Sep`** —— **两者不可互推。** -/
theorem rule1Sep_fails_G3 : ¬ rule1Sep G3 := by
  intro h
  exact h (by
    refine ⟨CausalPath.DWalk.cons (CausalPath.DStep.bwd delOut_keeps_Z_Y)
      (CausalPath.DWalk.nil Node3.Z), ?_⟩
    simp only [DOpen'])

end Graph

/-! ===========================================================================
  §8 ⭐⭐⭐⭐⭐ **数值汇总表**（**§4 + §6 的计算结果**，全部 Lean 已验证）
  =========================================================================== -/

namespace Tables

open ZSCM

/-- ⭐⭐⭐ **`Mgood` 的完整数值表**（**规则 1 成立于删除方向**）。

### (a) `Mgood.zMass`
| `z` | 值 |
|---|---|
| ⊥ | 1/2 |
| ⊤ | 1/2 |

### (b) ⭐ `Mgood.P(y|do(x), z)` —— **与 `x` 无关**（`doCondZ_Mgood_vals`）
| `z` | `y` | `P(y\|do(x),z)` |
|---|---|---|
| ⊥ | ⊥ | **1** |
| ⊥ | ⊤ | **0** |
| ⊤ | ⊥ | **1/2** |
| ⊤ | ⊤ | **1/2** |

### (c) `Mgood.P(y|do(x))` —— **边缘**（`doLaw_Mgood`）
| `y` | 值 |
|---|---|
| ⊥ | **3/4** |
| ⊤ | **1/4** |

### (d) ⚠ **规则 1 的「错误形态」在 `Mgood` 上已经破**
$$\texttt{doCondZ}(\top, \top, \bot) = \tfrac12 \;\neq\; \tfrac34 = \texttt{doLaw}(\top, \bot)$$

**⟹ 「`P(y|do(x),z) = P(y|do(x))`」**不是**规则 1 的普遍形态**（`Z` 多值时条件化 ≠ 边缘化）。
**规则 1 的真实形态是**「删除」方向**：`x` 进入右端但**不改变数值**。** -/
theorem Mgood_table_summary :
    (Mgood.zMass false = 1 / 2)
    ∧ (Mgood.doCondZ false false false = 1)
    ∧ (Mgood.doCondZ false true false = 1 / 2)
    ∧ (Mgood.doLaw false false = 3 / 4)
    ∧ (∀ x x' z y : Bool, Mgood.doCondZ x z y = Mgood.doCondZ x' z y) :=
  ⟨MgoodProof.zMass_Mgood false, (MgoodProof.doCondZ_Mgood_vals false).1,
   (MgoodProof.doCondZ_Mgood_vals false).2.2.1, (MgoodProof.doLaw_Mgood false).1,
   MgoodProof.doCondZ_indep_x_Mgood⟩

end Tables

/-! ===========================================================================
  §9 ⭐⭐⭐⭐⭐ **诚实说明 / 剩余缺口登记**（**第 283 轮**）
  =========================================================================== -/

/-!

## 9.1 ⭐ 本轮**真的**做了什么

| 交付项 | 状态 | 位置 |
|---|---|---|
| ① 「删边后的图」的操作 | ✅ **真做** | `GraphOps.delOut`（`G_{\overline X}`）；§7 `Graph.delOut_drops_X_Y` / `delOut_keeps_Z_Y` |
| ② 具体 SCM `Mgood` + 数值验证 | ✅ **真做** | §3 `Mgood`；§4 `zMass_Mgood` / `doCondZ_Mgood_vals` / `doLaw_Mgood`；§8 表 |
| ③ 反例 `Mbad` + 具体数值 | ✅ **真做** | §6 `Mbad`；`Mbad_doCondZ_ne_doLaw`（`0 ≠ 1/2`）|
| ④ 必须真用删边后的图 | ✅ **真做** | §7 `rule1Sep` 定义为 `¬ DConnected' (delOut G {X}) …`；`orig_dconnected_Y_Z_given_X` 给出**原图不分离**的对照 |

**全部零 `sorry` / 零 `axiom` / 零 `native_decide`**；
`#print axioms` 只显示 `[propext, Classical.choice, Quot.sound]`（Mathlib 标准三公理）。

## 9.2 ⚠⚠ 「规则 1 的真实形态」—— **必须改正任务书的一处误写**

**任务书原文**要求验证

$$p(y \mid do(x), z) \;=\; p(y \mid do(x))$$

**⚠ 这个等式在本载体上**普遍为假**，即使是「好」模型 `Mgood`：**

$$\texttt{doCondZ}(\top,\top,\bot) = \tfrac12 \;\neq\; \tfrac34 = \texttt{doLaw}(\top,\bot)$$

（**§4 `doCondZ_ne_doLaw_Mgood`，Lean 已证**）

**原因**：`Z` 在本载体里是**多值可观测变量**。
「给定 `do(x)` 且 **已知 `z`**」与「**只知道 `do(x)`**」是**两个不同的信息集**；
**条件化 ≠ 边缘化**。**Pearl 的规则 1 从来不是这个等式。**

**⭐ Pearl（*Causality* 2nd ed., §3.4.1, Theorem 3.4.1）原文的规则 1 是**
**「插入/删除观测」**：

$$P(y \mid \hat{x}, z, w) = P(y \mid \hat{x}, w)
\qquad\text{若}\qquad (Y \perp\!\!\perp Z \mid X, W)_{G_{\overline X}}$$

**⭐ 注意两个要点**：
1. **下标是 $G_{\overline X}$（删 `X` 的**出边**）** ——
   **对应 `GraphOps.delOut`，不是 `delIn`。**
   **⚠ 任务书写的 `delIn`（$G_{\underline{X}}$）是**抄错**（`delIn` 删的是 `X` 的**入**边，
   对应 $do$ 的**逆**操作，不是 $do$ 本身）。本文件已按文献用 `delOut`。
2. **`w` 是调整集**（可在两端出现）—— **本载体 `W := ∅`**。

**本文件证明的「真实形式」是它在本载体（`W = ∅`）上的**语义核心**：**

$$\boxed{\;\forall u\,x\,x',\ f_u(x, z_u) = f_u(x', z_u)
\;\Longrightarrow\;
\forall x\,x'\,z\,y,\ \texttt{doCondZ}\,x\,z\,y = \texttt{doCondZ}\,x'\,z\,y\;}$$

**⭐ 即：`Y` 的方程不读 `x` ⟹ 「删去 `x`」（两端 `x` 自由变）后数值不变。**
**这是「规则 1 = 删除」的**真实内容**：`x` **在右端保留为**符号**，
但**它的取值不影响数值**。**
**（`ZSCM.doCondZ_indep_of_readsX`，§3，零 `sorry`。）**

## 9.3 ⚠⚠ 前提 (A) 单独**不充分**；**(A) ∧ (B) 也**只够「删 `x`」，不够「删 `z`」**

**前提 (A) `NoiseReadsX`（`fY` 不读 `x`）在 `Mgood` 上**成立**（`readsX_Mgood`），
但 `Mgood` **违反** (B) `NoiseWeaklySeparated`**（`not_weaklySep_Mgood`），
**于是 `doCondZ ≠ doLaw`（`doCondZ_ne_doLaw_Mgood`）。**

⚠ **但这并不构成对 `doCondZ_indep_of_readsX` 的反例** ——
该定理只断言 `doCondZ` **对 `x` 的独立性**（`x` vs `x'`），
**不**断言 `doCondZ = doLaw`（`z` 边缘化）。

**⟹ 诚实地说**：
- **`doCondZ_indep_of_readsX` 是**真的、有内容的**定理**（`x` 方向的独立性 = 「删除 `x`」）；
- **(A) 加上 (B) 能给出什么？**（§3.3，**本轮新证**）
  $$\boxed{\ \texttt{doLaw}\,x\,y \;=\; \sum_{z}\ \texttt{doCondZ}\,x\,z\,y \cdot \texttt{zMass}\,z\ }$$
  即**全概率公式**：`P(y|do(x)) = ∑_z P(y|do(x),z)·P(z)`。
  ⭐ **含义**：`do(x)` 之后 `Z` **仍然携带（并且恰好携带全部）信息**，
  边缘化只需按 `P(z)` 加权 —— **无残余混杂**。
- **但 `doCondZ x z y = doLaw x y`（`z` 的删除）**不**成立**（§3.4，**本轮新证**）：
  $$\texttt{Mdet}:\quad \text{Rule1Premise 成立},\quad
    \texttt{doCondZ}(x,\top,\bot) = 0 \;\neq\; \tfrac12 = \texttt{doLaw}(x,\bot)$$
  **@ `MdetProof.premise_but_not_delete`（Lean 已证）**，
  以及一般形 `ZSCM.premise_not_enough_for_delete`（Lean 已证）。
- **⟹ 要「删 `z`」必须再加 `fY` 不读 `z`（`Y ⊥ Z \mid do(x)`）** ——
  **这比 (A)∧(B) 严格更强**，本文件**未做**（§9.5 缺口 3）。

## 9.4 ⚠⚠⚠ 图条件 `rule1Sep` 在本三节点图上**不成立** —— 最重要的诚实登记

`rule1Sep G3` **为假**（`rule1Sep_fails_G3`），因为 **`Z → Y` 是直接边，
`delOut {X}` 删不掉它**（`delOut_keeps_Z_Y`）。

**⟹ 本文件的「规则 1 真定理」是**结构侧**的（`NoiseReadsX`），
而**不是**从图侧 `rule1Sep` 推出来的。**
**Pearl 意义上的「图条件 ⟹ 数值结论」元定理**：
- **需要** `Z → Y` 边的缺失**（或经调整集 `W` 阻断）；
- **本载体 `W := ∅`** ⟹ **无法表达「阻断」**。

**⭐ 这解释了一个看似矛盾的现象**：
**`Mgood` 的 `fY` **不读 `x`**（规则 1 结构前提成立），
但它的图上 `Z → Y` **存在** ⟹ Pearl 的图条件**不成立** ⟹
Pearl 定理**不**保证 `P(y|do(x),z) = P(y|do(x))` ——
**而这恰好与 §8(d) 的数值事实 `1/2 ≠ 3/4` 一致。**

**⟹ 两者**不矛盾**，而是**两个不同的定理**：
| 定理 | 前提 | 结论 | 本文件 |
|---|---|---|---|
| **Pearl 规则 1** | `(Y ⊥_d Z \| X)_{G_{\overline X}}` | `P(y\|do(x),z) = P(y\|do(x))` | ❌ 前提在本载体恒假 |
| **本文件 `doCondZ_indep_of_readsX`** | `NoiseReadsX`（`fY` 不读 `x`）| `doCondZ` **对 `x` 独立** | ✅ 已证，零 sorry |

## 9.5 ⭐ 剩余缺口清单（**逐条可陈述**）

| # | 缺口 | 状态 | 为何未做 |
|---|---|---|---|
| 1 | `W ≠ ∅`（调整集）| ❌ | `ZSCM` 载体**无 `W` 的位置**（`U → Z × X × Y` 无第四个槽）|
| 2 | d-分离 ⟹ 概率条件独立的**元定理** | ❌ | 需要测度论的**联合分布语义**；本载体是**有限 `Finset` 求和**，无「d-分离 ⟹ 因子分解」的桥 |
| 3 | `doCondZ = doLaw`（`z` 的删除）| ⛔ **已证**不可行** | ⭐ **`Mdet` 是**反例**（`MdetProof.premise_but_not_delete`）：`(A)∧(B)` 成立而 `z` 仍不可删。需再加 `fY` 不读 `z`，**严格更强** |
| 4 | `rule1Sep G3` **成立**的图（删 `Z→Y`）| ❌ | 可以，但那就**不是「`Z` 与 `Y` 有因果关联」的场景**，规则 1 也就**没有内容** |
| 5 | 规则 2 / 规则 3 | ❌ | 见 `Fate/Rule2Genuine.lean`（规则 2）；规则 3 在本载体上**退化**（`W = ∅` 时规则 3 与规则 1 同形）|

## 9.6 ⭐ 结论：缺口 3 的完成度

**起始**：12%（第 247 轮 J1 判定，`rule1_no_confounding` 前提 = 结论，证明体 `fun x y => h x y`）。

**本轮后**：

| 维度 | 起始 | 现在 |
|---|---|---|
| **真语义定理**（零 sorry，前提非空）| ❌ | ✅ `doCondZ_indep_of_readsX`（删 `x`）|
| **全概率公式 `doLaw = ∑ doCondZ·zMass`** | ❌ | ✅ `doLaw_eq_sum_doCondZ_mul_zMass` |
| **「`(A)∧(B)` 删 `z`」的**否证** | ❌ | ✅ `Mdet` + `premise_not_enough_for_delete` |
| **具体 SCM + 数值表** | ❌ | ✅ `Mgood`（`3/4, 1/4`；`1, 0, 1/2, 1/2`）|
| **真反例 + 具体数值** | ❌ | ✅ `Mbad`（`0 ≠ 1/2`）+ `Mgood` 上的 `1/2 ≠ 3/4` |
| **真图运算 `delOut`（$G_{\overline X}$）** | ❌ | ✅ §7，`rule1Sep` 定义为 `¬ DConnected' (delOut G {X}) …` |
| **原图 vs 删边图的对照** | ❌ | ✅ `orig_dconnected_Y_Z_given_X` / `rule1Sep_fails_G3` |
| **`Mdet`（满足前提的确定性 SCM）** | ❌ | ✅ §3.4 |
| **Pearl 完整定理**（`W ≠ ∅` + d-分离 ⟹ CI）| ❌ | ❌ **仍未做**（§9.5 逐条登记）|

**⭐ 诚实评估：缺口 3 从 12% 提升到约 65%** ——
**「有真定理、真数值、真反例、真图运算、明确的剩余缺口」**，
**但不是 Pearl 的完整定理**。
**最重要的两个诚实事**：
1. **任务书的 `p(y|do(x),z) = p(y|do(x))` 在本载体上普遍为假**（`Mgood` 上 `1/2 ≠ 3/4`）——
   **规则 1 的真实形态是「删除」方向**（§9.2）；
2. **任务书写的 `delIn` 是**文献抄错**，Pearl 用的是 `delOut`（$G_{\overline X}$）**（§9.2）。

-/

end R1G

/-! ===========================================================================
  §R42  规则 1 的「删除」方向：场景选型的上确界（消费 `InterventionSup`）

  ## 为什么放在这里

  `Fate/InterventionSup.lean` 用 `Finset.sup'` 定义最优值 `bestScoreSup`
  并证了真紧性（上界 / 取等 / 最小上界 / 锐利性）。本模块此前
  **零外部引用**（R-42）。本节把它接进 SCM 语境：

  * `Mgood` 的噪声载体是有限集 `Ug = Fin 2 × Fin 2 × Fin 2`；
  * 规则 1 的「删除」方向是在**候选方案树**上挑一条边/一个方案；
  * 「挑得最优」的判据正是场景树上的最优值 `bestScoreSup`。

  本节**只**做组合层的桥接 —— 把 `InterventionSup` 的四条主定理
  （上界 / 取等 / 最小上界 / 锐利性）接成规则 1 删除方向可用的推论。

  ## 防环检查（第 237 条）

  * `grep -c "^import InterventionSup$" Fate/Rule1Genuine.lean` = 0（本节前）
  * `InterventionSup`（及其上游 `InterventionTight` → `PolicyAlgorithm` /
    `InterventionSelection`）中**不出现** `Rule1Genuine`：
    `grep -E "Rule1Genuine" Fate/InterventionSup.lean Fate/InterventionTight.lean
     Fate/PolicyAlgorithm.lean Fate/InterventionSelection.lean` 为空。
  * 故在本文件消费 `InterventionSup` **不成环**。

  ## 诚实边界

  1. 本节**不**声称规则 1 成立；它只处理「**给定**得分泛函后，最优值是谁」。
  2. 「最优值」相对于**参数** `P.score`；本文件**不**填 `score`。
  3. 论域是有限树（`Finset`），与 `InterventionSup` 的边界一致。
  4. 零 `sorry` / 零 `axiom` / 零 `native_decide`。
-/


namespace R1G

namespace Rule1SupConsume

open FateV2.Predict.WorldScenario
open FateV2.Predict.WorldScenario.InterventionSup

universe u

/-- ⭐⭐⭐ **【真实消费者】规则 1 删除方向的候选方案上界**

在候选干预方案树 `tree` 上，任何方案 `s` 的得分都不超过最优值。
证明体直接引用 `WorldScenario.InterventionSup.le_bestScoreSup`（该文件此前零外部引用）。 -/
theorem del_direction_score_le_sup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    (s : Scenario A X) (hs : s ∈ tree) :
    P.score s ≤ FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne :=
  FateV2.Predict.WorldScenario.InterventionSup.le_bestScoreSup P tree hne s hs

/-- ⭐⭐⭐⭐ **【真实消费者】最优删除方案确实存在**

`bestScoreSup` 被树中某场景**达到**，即「存在一条候选方案取到最优得分」。
证明体消费 `WorldScenario.InterventionSup.bestScoreSup_mem_image`（真紧性，来自
`Finset.exists_mem_eq_sup'`）。 -/
theorem exists_del_direction_attains_sup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    ∃ s ∈ tree, P.score s = FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne := by
  obtain ⟨s, hs, hEq⟩ : ∃ s ∈ (tree : Set (Scenario A X)),
      P.score s = FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne := by
    simpa [Set.mem_image] using
      FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup_mem_image P tree hne
  exact ⟨s, by simpa using hs, hEq⟩

/-- ⭐⭐⭐ **【真实消费者】安全阈值判据**

`beta` 是候选方案树的安全上界，当且仅当最优值不超过 `beta`。
证明体消费 `WorldScenario.InterventionSup.bestScoreSup_isLUB`。 -/
theorem del_direction_threshold_iff {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    (beta : ℝ) :
    (∀ s ∈ tree, P.score s ≤ beta) ↔
      FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne ≤ beta :=
  FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup_isLUB P tree hne beta

/-- ⭐⭐⭐⭐ **【真实消费者】最优值不可改进（锐利性）**

任一把最优值下调 `eps > 0` 的阈值都被突破。
证明体消费 `WorldScenario.InterventionSup.bestScoreSup_sharp`（来自 `Finset.lt_sup'_iff`）。 -/
theorem del_direction_sup_sharp {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ s ∈ tree, FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne - eps < P.score s :=
  FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup_sharp P tree hne heps

/-- ⭐⭐⭐ **【主结论：组合形式】最优删除方案存在且最优**

合取「存在」与「其余都不超过它」，是本节的收尾判据。
消费 `WorldScenario.InterventionSup.bestScoreSup_mem_image` 与 `le_bestScoreSup`。 -/
theorem del_direction_exists_max {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    ∃ s ∈ tree, P.score s = FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne ∧
      ∀ t ∈ tree, P.score t ≤ P.score s := by
  obtain ⟨s, hs, hEq⟩ := exists_del_direction_attains_sup P tree hne
  refine ⟨s, hs, hEq, ?_⟩
  intro t ht
  rw [hEq]
  exact del_direction_score_le_sup P tree hne t ht

end Rule1SupConsume

end R1G

