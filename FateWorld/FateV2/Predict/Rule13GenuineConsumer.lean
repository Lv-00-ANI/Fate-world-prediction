import FateWorld.FateV2.Predict.Rule13Genuine
import FateWorld.FateV2.Predict.Rule2Genuine
import FateWorld.FateV2.Predict.PearlLawRuleBridge
import FateWorld.FateV2.Predict.LawRuleSatisfiabilityConsumer
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
  # Predict · Rule13GenuineConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Rule13GenuineConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Rule13Genuine, Rule2Genuine, PearlLawRuleBridge, LawRuleSatisfiabilityConsumer
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/Rule13GenuineConsumer` —— **`Rule13Genuine` 的消费层**
  （P5 并行任务，第 740 轮）

  ## 一、上游模块（实测声明，`Fate/Rule13Genuine.lean`，471 行）

  | 命名空间 | 声明 | 类型 |
  |---|---|---|
  | `R249.Exog` | `XIndependent` | `def`（外生层前提，规则 1）|
  | `R249.Exog` | `MassOne` | `def`（`∑ pU = 1`）|
  | `R249.Rule1` | `XIndependent.disj` | `theorem`（分片引理）|
  | `R249.Rule1` | `rule1_genuine` | `theorem`（**主交付 1**）|
  | `R249.Rule1` | `noConfounding_of_XIndependent` | `theorem`（旧 API 包装）|
  | `R249.Rule3` | `EffNull` | `def`（方程层前提，规则 3）|
  | `R249.Rule3` | `effNull_zOf` | `theorem` |
  | `R249.Rule3` | `rule3_genuine` | `theorem`（**主交付 2**）|
  | `R249.Rule3` | `rule3_z_irrelevant` | `theorem` |
  | `R249.Rule1`（§4）| `M1` / `M1_XIndependent` / `M1_massOne` / `M1_rule1` | `def` + 3 `theorem` |
  | `R249.Rule1`（§4）| `XIndependent_not_necessary` | `theorem`（诚实边界）|
  | `R249.Rule1`（§4）| `MC` / `MC_not_XIndependent` | `def` + `theorem` |
  | `R249.Rule3`（§4）| `conf_effNull` / `conf_rule3` / `chain_not_effNull` | 3 `theorem` |

  （另有 4 条 `private` 引理：`mult_ind` / `mult_ind_zero` / `main_zero` / `main_one`。）

  ## 二、本文件证明的新内容（**不是上游改写**）

  ### §1 规则 1 的两个派生结论

  1. **`condY_eq_doLaw_of_marginalX_one`**：上游 `rule1_genuine` 给
     `condY = μ(x)·doLaw`；本条补出「`μ(x) = 1` ⟹ `condY = doLaw`」
     —— 这是 `T35Rule1Split.MNC_rule1`（除法形式，需 `μ(x) ≠ 0`）的
     **无除版本**。前件在三个**不同论域**上（外生层 / 外生层 / `X` 边缘），
     **不含**结论（`X × Y` 上的等式）。
  2. **`xIndependent_strictly_weaker`**：构造 `MZ`（`pU = [u = 0]`），
     证明 `XIndependent MZ` 成立、`MassOne MZ` 成立、`rule1_genuine` 在 `MZ`
     上跑通，**但 `MZ` 的 `X` 非常值**。
     ⭐ 这是上游定义中 `∨ pU u = 0 ∨ pU v = 0` 分支**不可省**的**见证** ——
     上游只在文档里口头提过，**没有形式化的模型**。

  ### §2 规则 3 的**载体无关性**（上游未做）

  3. **`EffNull` 只约束 `sg.2`**，故对 `Z × X` 分量的任意**重标定不敏感**。
     定义 `rebase M g`（换 `sg.1`、留 `pU` 与 `sg.2`），证明
     `effNull_rebase` / `doLaw2_rebase` / `doLawXOnly_rebase_of_effNull` /
     `rule3_rebase`。
     ⭐ `doLawXOnly_rebase_of_effNull` **不是 `rfl`**：`doLawXOnly` 读
     `zOf(x_u)`（来自被换掉的分量），要靠 `EffNull` 才能换回。

  ### §3 规则 2 与规则 3 的**交叉**（跨模块：`Rule2Genuine` × `Rule13Genuine`）

  4. **`doLaw2_indep_x_of_mediationInvariant`**：`MediationInvariant` ⟹
     `doLaw2` **不读 `x`**；
     **`doLaw2_indep_xz_of_effNull_invariant`**：两个前提合用 ⟹
     `doLaw2` **同时不读 `x` 也不读 `z`**（`doLaw2 x₁ z₁ y = doLaw2 x₂ z₂ y`）。
     ⭐ 后者是**两上游各提供一半**的结论 —— `effNull` 去 `z`、`mediationInvariant`
     去 `x`，**没有任何一条上游定理单独给出它**。

  ### §4 接入 `LawRule` 主链（⚠ **接口层，零新数学**）

  5. `M1_toLawRule_isPoint` / `M1_mem_scmFamily`。

  ## 三、⚠ 诚实边界（**必须读**）

  * **§4 无实质数学内容**：`isPoint_toLawRule` 对**任意** `SCM` 成立。
    它的唯一作用是把 `Rule13Genuine.Rule1.M1` 与 `PearlLawRuleBridge`
    在**类型上**接起来。**不计入实质内容。**
  * **`MZ` 不是反例**：它**满足** `XIndependent`，是「零质量分支真被用到」的
    **见证**，**不是**对上游定理的反驳。
  * **`EffNull` 的逆命题不成立、本文件不声称**：
    `(∀ x z₁ z₂ y, doLaw2 x z₁ y = doLaw2 x z₂ y)` **推不出** `EffNull`
    （权重可互相抵消）。本文件**只**用 `EffNull ⟹ …` 方向。
  * **⚠ 明确放弃的方向**：想用 `R248.Sem.doLaw2_eq_doLawX_of_invariant` 把
    `doLaw2` 接到 `doLawX`（**观测 `Z`** 而非边缘化 `Z`），但它需要
    `R248.Sem.ZIsRoot`，而 `ZIsRoot` 要求 `zOf` 对**所有** `z` 恒定 ——
    `Rule2Genuine.zIsRoot_forces_subsingleton` 表明**只有 `Z` 单点的模型满足它**。
    在 `Fin 2` 等具体模型上 `ZIsRoot` **恒假**，故该方向**在本载体上无用**，
    **本文件不用它、不声称它**。
  * **不构造「带调整集 `W`」的规则 1/3**（上游也未做）。
  * **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`。**
  =========================================================================== -/

namespace FateV2.Predict
namespace R740

universe u

/-! ===========================================================================
  §1 规则 1（`R249.Rule1`）的派生结论
  =========================================================================== -/

namespace R1

open R249.Exog
open FateV2.Rules

/-! ### §1.1 `μ(x) = 1` 时 `condY = doLaw`（上游没有的推论） -/

/-- ⭐⭐⭐⭐ **`rule1_genuine` 的**可消去形态**：`μ(x) = 1` 时 `condY = doLaw`。

上游 `rule1_genuine` 给出 `condY = μ(x) · doLaw`；本条把它化成两条律的**直接相等**。

**⭐ 与 `T35Rule1Split.MNC_rule1` 的关系**：那条是 `condY / μ(x) = doLaw`
（**除法形式**，需 `μ(x) ≠ 0`）。本条是**乘法/无除形式**的一个充分条件版。

**⚠ 非同义反复**：前件 `XIndependent M ∧ MassOne M ∧ marginalX M x = 1`
三项分别在 `M.U × M.U`、`M.U → ℝ` 的和、`X → ℝ` 上；
结论 `∀ y, condY M x y = doLaw M x y` 是 `Y → ℝ` 上的等式族。
论域与形态都不同，且证明体是 `rule1_genuine` + `one_mul`（不是 `fun y => h y`）。 -/
theorem condY_eq_doLaw_of_marginalX_one {X Y : Type u} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (h : XIndependent M) (hm : MassOne M) (x : X)
    (hx : FateV2.Modeling.SCMSemantics.marginalX M x = 1) :
    ∀ y, FateV2.Modeling.SCMSemantics.condY M x y = FateV2.Modeling.SCMSemantics.doLaw M x y := by
  intro y
  rw [R249.Rule1.rule1_genuine M h hm x y, hx, one_mul]

/-- ⭐⭐⭐ **`M1` 上 `μ(0) = 1`**（上游只证了 `M1_XIndependent` / `M1_massOne`，
**未给 `marginalX` 的值**）。

$$\mathrm{marginalX}\,M1\,0 = \sum_{u:\mathrm{Fin}\,2}\ \tfrac12\,[0 = 0] = 1$$ -/
theorem M1_marginalX_zero :
    FateV2.Modeling.SCMSemantics.marginalX R249.Rule1.M1 (⟨0, by decide⟩ : Fin 2) = 1 := by
  show (∑ u : R249.Rule1.M1.U,
      R249.Rule1.M1.pU u
        * (if (R249.Rule1.M1.sg u).1 = (⟨0, by decide⟩ : Fin 2) then (1 : ℝ) else 0)) = 1
  rw [show (∑ u : R249.Rule1.M1.U,
      R249.Rule1.M1.pU u
        * (if (R249.Rule1.M1.sg u).1 = (⟨0, by decide⟩ : Fin 2) then (1 : ℝ) else 0))
      = (∑ _u : Fin 2,
          (1 : ℝ) / 2 * (if (0 : Fin 2) = (⟨0, by decide⟩ : Fin 2) then (1 : ℝ) else 0))
      from rfl]
  rw [Fin.sum_univ_two]
  norm_num

/-- ⭐⭐⭐⭐ **`M1` 上 `condY = doLaw`**（在 `x = 0` 处，`μ(0) = 1` 的直接实例）。

**⭐ 加强形态**：上游 `M1_rule1` 给乘法形式 `condY = marginalX · doLaw`；
本条在 `x = 0` 处**消去因子**。

⚠ **诚实标注**：本条的实质在 `M1_marginalX_zero` 与
`condY_eq_doLaw_of_marginalX_one`；这里只是把两者接起来。 -/
theorem M1_condY_eq_doLaw (y : Fin 2) :
    FateV2.Modeling.SCMSemantics.condY R249.Rule1.M1 (⟨0, by decide⟩ : Fin 2) y
      = FateV2.Modeling.SCMSemantics.doLaw R249.Rule1.M1 (⟨0, by decide⟩ : Fin 2) y :=
  condY_eq_doLaw_of_marginalX_one R249.Rule1.M1 R249.Rule1.M1_XIndependent
    R249.Rule1.M1_massOne (⟨0, by decide⟩ : Fin 2) M1_marginalX_zero y

/-! ### §1.2 ⭐ `XIndependent` **严格弱于**「`X` 常值」（`MZ` 见证） -/

/-- ⭐⭐⭐⭐⭐ **`MZ`：零质量分支的见证模型**。

$$U = \mathrm{Fin}\,2,\quad p_U(u) = [u = 0],\quad \mathrm{sg}\,u = (u,\ \mathrm{id})$$

**⟹ `pU 1 = 0`，故 `XIndependent MZ` 成立（走 `pU u = 0` 分支）；
但 `(sg 0).1 = 0 ≠ 1 = (sg 1).1`，故 `X` **不是常值**。** -/
noncomputable def MZ : FateV2.Modeling.PearlHierarchy.SCM (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun u => if u = 0 then (1 : ℝ) else 0
  sg := fun u => (u, fun x => x)

/-- ⭐⭐⭐ **`MZ` 的质量归一**（`pU ≡ [u = 0]` ⟹ 和 `= 1`）。 -/
theorem MZ_massOne : MassOne MZ := by
  show (∑ u, MZ.pU u) = 1
  rw [show (∑ u : MZ.U, MZ.pU u)
      = (∑ u : Fin 2, if u = 0 then (1 : ℝ) else 0) from rfl]
  rw [Fin.sum_univ_two]
  norm_num

/-- ⭐⭐⭐⭐⭐ **`MZ` 满足 `XIndependent`** —— **走的是零质量分支**。

**⭐ 这是上游 `XIndependent` 定义中 `∨ pU u = 0 ∨ pU v = 0` 分支
**不可省**的直接见证**：`MZ` 的两个外生点 `X` 取值不同，
但其中一点质量为 `0`，故 `XIndependent` **仍成立**。 -/
theorem MZ_XIndependent : XIndependent MZ := by
  intro u v
  by_cases hu : (show Fin 2 from u) = 0
  · by_cases hv : (show Fin 2 from v) = 0
    · left
      show (MZ.sg u).1 = (MZ.sg v).1
      rw [show (MZ.sg u).1 = (show Fin 2 from u) from rfl,
        show (MZ.sg v).1 = (show Fin 2 from v) from rfl, hu, hv]
    · right; right
      show MZ.pU v = 0
      rw [show MZ.pU v = (if (show Fin 2 from v) = 0 then (1 : ℝ) else 0) from rfl,
        if_neg hv]
  · right; left
    show MZ.pU u = 0
    rw [show MZ.pU u = (if (show Fin 2 from u) = 0 then (1 : ℝ) else 0) from rfl,
      if_neg hu]

/-- ⭐⭐⭐⭐ **`MZ` 的 `X` **不是常值**（`(sg 0).1 ≠ (sg 1).1`）。

**⟹ 与 `MZ_XIndependent` 合起来：`XIndependent` **严格弱于**「`X` 常值」。** -/
theorem MZ_sg_not_const :
    ¬ (∀ u v : MZ.U, (MZ.sg u).1 = (MZ.sg v).1) := by
  intro h
  have h01 : (MZ.sg (⟨0, by decide⟩ : Fin 2)).1 = (MZ.sg (⟨1, by decide⟩ : Fin 2)).1 :=
    h ⟨0, by decide⟩ ⟨1, by decide⟩
  exact absurd h01 (by decide)

/-- ⭐⭐⭐⭐⭐ **`rule1_genuine` 在 `MZ` 上跑通**（**零质量分支的真实验证**）。

**⭐ 这是上游没有的实例**：上游只在 `M1`（`X` 常值）上验证过规则 1；
本条验证**`X` 非常值、但正质量上常值**的模型 —— 即 `XIndependent` 的
**全部力量**（不只是「常值」这个特例）。 -/
theorem MZ_rule1 (x y : Fin 2) :
    FateV2.Modeling.SCMSemantics.condY MZ x y
      = FateV2.Modeling.SCMSemantics.marginalX MZ x * FateV2.Modeling.SCMSemantics.doLaw MZ x y :=
  R249.Rule1.rule1_genuine MZ MZ_XIndependent MZ_massOne x y

/-- ⭐⭐⭐⭐⭐ **主结论（§1）：`XIndependent` **严格弱于**「`X` 常值」**。

**陈述**：存在 `SCM`，满足 `XIndependent` **且**质量归一，
**但其 `X` 取值随外生变化**。

**⭐ 意义**：上游 `XIndependent` 定义中的 `∨ pU u = 0 ∨ pU v = 0` 两个分支
**不是装饰** —— 去掉它们（改成「`X` 常值」）会**丢掉真模型**。
本条把这个「不可省性」形式化。 -/
theorem xIndependent_strictly_weaker :
    ∃ (M : FateV2.Modeling.PearlHierarchy.SCM (Fin 2) (Fin 2)),
      XIndependent M ∧ MassOne M ∧ ¬ (∀ u v : M.U, (M.sg u).1 = (M.sg v).1) :=
  ⟨MZ, MZ_XIndependent, MZ_massOne, MZ_sg_not_const⟩

end R1

/-! ===========================================================================
  §2 规则 3（`R249.Rule3`）的**载体无关性**
  =========================================================================== -/

namespace R3

open R246G3.Sem3

/-- ⭐⭐⭐⭐ **重标定**：换掉 `sg` 的第一分量（`Z × X` 的观测机制）、
保留 `pU` 与 `sg` 的第二分量（`Y` 的方程）。

$$\texttt{rebase}\,M\,g := \bigl(U := M.U,\ p_U := M.p_U,\
  \mathrm{sg}\,u := (g\,u,\ (M.\mathrm{sg}\,u).2)\bigr)$$

**⭐ 用途**：`EffNull` **只**约束 `(sg u).2` 的第一个参数，
故重标定后 `EffNull` **不变**（`effNull_rebase`）——
这说明「规则 3」是**关于 `Y` 的方程的性质**，与 `Z`、`X` 如何被决定**无关**。 -/
noncomputable def rebase {Z X Y : Type u} (M : SCM3 Z X Y) (g : M.U → Z × X) :
    SCM3 Z X Y where
  U := M.U
  pU := M.pU
  sg := fun u => (g u, (M.sg u).2)

/-- ⭐ **`rebase` 保留 `Y` 的方程**（`rfl`）。 -/
theorem rebase_sg2 {Z X Y : Type u} (M : SCM3 Z X Y) (g : M.U → Z × X) (u : M.U) :
    ((rebase M g).sg u).2 = (M.sg u).2 := rfl

/-- ⭐⭐⭐⭐⭐ **`EffNull` 对重标定**不变**（**规则 3 的载体无关性**）。

$$\textbf{EffNull}(M) \Longrightarrow \textbf{EffNull}(\texttt{rebase}\,M\,g)$$

**⭐ 这不是技巧性重述**：`rebase` 换掉 `Z`、`X` 的**决定机制**（可为任意 `g`），
而 `EffNull` **依然成立** —— 即「规则 3 的前提完全不看 `Z`、`X` 是怎么来的」。 -/
theorem effNull_rebase {Z X Y : Type u} (M : SCM3 Z X Y) (g : M.U → Z × X)
    (h : R249.Rule3.EffNull M) : R249.Rule3.EffNull (rebase M g) := by
  intro u z₁ z₂ x
  have h2 : ((rebase M g).sg u).2 = (M.sg u).2 := rebase_sg2 M g u
  show ((rebase M g).sg u).2 (z₁, x) = ((rebase M g).sg u).2 (z₂, x)
  rw [h2]
  exact h u z₁ z₂ x

/-- ⭐⭐⭐⭐ **`doLaw2` 对重标定**完全不变**（**逐项相等**）。 -/
theorem doLaw2_rebase {Z X Y : Type u} [DecidableEq Y]
    (M : SCM3 Z X Y) (g : M.U → Z × X) (x : X) (z : Z) (y : Y) :
    R246G3.Sem3.doLaw2 (rebase M g) x z y = R246G3.Sem3.doLaw2 M x z y := by
  unfold R246G3.Sem3.doLaw2
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have h2 : ((rebase M g).sg u).2 = (M.sg u).2 := rebase_sg2 M g u
  show (rebase M g).pU u
        * (if ((rebase M g).sg u).2 (z, x) = y then (1 : ℝ) else 0)
      = M.pU u * (if (M.sg u).2 (z, x) = y then (1 : ℝ) else 0)
  have h1 : (rebase M g).pU u = M.pU u := rfl
  rw [h1, h2]

/-- ⭐⭐⭐⭐⭐ **`doLawXOnly` 对重标定不变** —— ⚠ **这条需要 `EffNull`**。

**⚠ 为什么不是 `rfl`**：`doLawXOnly M x y` 的项是
`pU u · [f_u(zOf(x_u), x) = y]`，其中 `zOf(x_u)` 来自**第一分量** ——
**它被 `rebase` 换掉了**。要用 `EffNull` 才能把
`f_u((g u).1, x)` 换回 `f_u(zOf(x_u), x)`。

**⭐ 这是 `EffNull`（`rule3_genuine` 的引擎：「`f` 不读第一参数」）的**第二次使用**：
上游用它把 `doLaw2` 对齐到 `doLawXOnly`，这里用它把**两个不同载体的**
`doLawXOnly` 对齐。 -/
theorem doLawXOnly_rebase_of_effNull {Z X Y : Type u} [DecidableEq Z] [DecidableEq Y]
    (M : SCM3 Z X Y) (g : M.U → Z × X) (h : R249.Rule3.EffNull M)
    (x : X) (y : Y) :
    R246G3.Sem3.doLawXOnly (rebase M g) x y = R246G3.Sem3.doLawXOnly M x y := by
  unfold R246G3.Sem3.doLawXOnly
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have h2 : ((rebase M g).sg u).2 = (M.sg u).2 := rebase_sg2 M g u
  have h1 : (rebase M g).pU u = M.pU u := rfl
  have hz : R246G3.Sem3.zOf ((rebase M g).sg u).1 = (g u).1 := rfl
  have hkey : (M.sg u).2 ((g u).1, x)
      = (M.sg u).2 (R246G3.Sem3.zOf (M.sg u).1, x) :=
    R249.Rule3.effNull_zOf M h u (g u).1 x
  show (rebase M g).pU u
        * (if ((rebase M g).sg u).2 (R246G3.Sem3.zOf ((rebase M g).sg u).1, x)
            = y then (1 : ℝ) else 0)
      = M.pU u
        * (if (M.sg u).2 (R246G3.Sem3.zOf (M.sg u).1, x) = y then (1 : ℝ) else 0)
  rw [h1, h2, hz, hkey]

/-- ⭐⭐⭐⭐ **`rule3_genuine` 在重标定下的**一致性**：
`rebase` 之后的 `doLaw2` 与 `doLawXOnly` 仍相等**（**前提只需原模型的 `EffNull`**）。

**⭐ 意义**：规则 3 的结论**不是**某个载体的巧合 ——
它对**整个重标定族**（`g` 任意）**一致成立**。 -/
theorem rule3_rebase {Z X Y : Type u} [DecidableEq Z] [DecidableEq Y]
    (M : SCM3 Z X Y) (g : M.U → Z × X) (h : R249.Rule3.EffNull M)
    (x : X) (z : Z) (y : Y) :
    R246G3.Sem3.doLaw2 (rebase M g) x z y
      = R246G3.Sem3.doLawXOnly (rebase M g) x y := by
  rw [doLaw2_rebase, doLawXOnly_rebase_of_effNull M g h]
  exact R249.Rule3.rule3_genuine M h x z y

/-- ⭐⭐⭐⭐ **`rebase` 在完全混杂模型 `conf` 上仍满足规则 3**
（`conf` 的 `sg.2` 读 `u`、忽略参数，故重标定不可能破坏 `EffNull`）。

**⭐ 具体见证**：取 `g u = (u, u)`，即在 `conf` 上重标定并验证规则 3 仍成立。 -/
theorem conf_rebase_rule3 (x z y : Fin 2) :
    R246G3.Sem3.doLaw2 (rebase FateV2.Predict.R246G3.conf (fun u => (u, u))) x z y
      = R246G3.Sem3.doLawXOnly (rebase FateV2.Predict.R246G3.conf (fun u => (u, u))) x y :=
  rule3_rebase FateV2.Predict.R246G3.conf (fun u => (u, u)) R249.Rule3.conf_effNull x z y

/-- ⭐⭐⭐⭐ **⚠ 诚实边界的**载体侧**：重标定**不能**让 `chain` 满足 `EffNull`**。

`chain` 的 `Y` 方程是 `fun p => p.1`（**真读**第一参数），
`rebase` **不碰** `sg.2`，故 `chain_not_effNull` 的理由原样保留。

**⭐ 这条把 §2 的结论定界**：`EffNull` 是**关于 `sg.2`** 的条件，
`rebase` 只改 `sg.1` —— **故重标定既不能造出 `EffNull`，也不能破坏它**。 -/
theorem chain_rebase_not_effNull (g : R246G3.chain.U → Fin 2 × Fin 2) :
    ¬ R249.Rule3.EffNull (rebase R246G3.chain g) := by
  intro h
  apply R249.Rule3.chain_not_effNull
  intro u z₁ z₂ x
  have h2 : ((rebase R246G3.chain g).sg u).2 = (R246G3.chain.sg u).2 :=
    rebase_sg2 R246G3.chain g u
  have hkey := h u z₁ z₂ x
  rw [h2] at hkey
  exact hkey

end R3

/-! ===========================================================================
  §3 规则 2 与规则 3 的**交叉**（跨模块：`Rule2Genuine` × `Rule13Genuine`）
  =========================================================================== -/

namespace Cross

open R246G3.Sem3

/-- ⭐⭐⭐⭐ **`MediationInvariant` ⟹ `doLaw2` **不读 `x`**。

$$P(y \mid do(x), do(z)) \text{ 与 } x \text{ 无关}$$

**⭐ 这是 `Rule2Genuine` 的 `MediationInvariant` 在**方程层**的直接后果**
（`Y` 的方程不看第二参数 `x`），**上游 `Rule2Genuine` 未单独陈述它**
（它只给了 `doLaw2 = doLawX`，那需要额外的 `ZIsRoot`）。 -/
theorem doLaw2_indep_x_of_mediationInvariant {Z X Y : Type u} [DecidableEq Y]
    (M : SCM3 Z X Y) (hI : R248.Sem.MediationInvariant M)
    (x₁ x₂ : X) (z : Z) (y : Y) :
    R246G3.Sem3.doLaw2 M x₁ z y = R246G3.Sem3.doLaw2 M x₂ z y := by
  unfold R246G3.Sem3.doLaw2
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hk : (M.sg u).2 (z, x₁) = (M.sg u).2 (z, x₂) := hI u (z, x₁) (z, x₂) rfl
  rw [hk]

/-- ⭐⭐⭐⭐⭐ **主交叉定理（§3）**：`EffNull ∧ MediationInvariant` ⟹
`doLaw2` **同时不读 `x` 与 `z`**。

$$\mathrm{doLaw2}\,M\,x_1\,z_1\,y = \mathrm{doLaw2}\,M\,x_2\,z_2\,y$$

**⭐ 为什么这是新内容**：两条上游定理**各只给一半** ——
- `Rule13Genuine.Rule3.rule3_z_irrelevant`（`EffNull`）：只给**`z` 无关**；
- §3 的 `doLaw2_indep_x_of_mediationInvariant`（`MediationInvariant`）：只给**`x` 无关**。

**本条的**双参数恒定性**必须两个前提合用**，且**不需要** `ZIsRoot`
（`R248.Sem.doLaw2_eq_doLawX_of_invariant` 需要它，而它在 `Fin 2` 类模型上恒假 ——
见文件头「明确放弃的方向」）。 -/
theorem doLaw2_indep_xz_of_effNull_invariant {Z X Y : Type u}
    [DecidableEq Z] [DecidableEq Y] (M : SCM3 Z X Y)
    (hE : R249.Rule3.EffNull M) (hI : R248.Sem.MediationInvariant M)
    (x₁ x₂ : X) (z₁ z₂ : Z) (y : Y) :
    R246G3.Sem3.doLaw2 M x₁ z₁ y = R246G3.Sem3.doLaw2 M x₂ z₂ y := by
  rw [R249.Rule3.rule3_z_irrelevant M hE x₁ z₁ z₂ y,
    doLaw2_indep_x_of_mediationInvariant M hI x₂ x₁ z₂ y]

/-- ⭐⭐⭐⭐ **`conf` 同时满足两个前提**（`EffNull` 来自上游、`MediationInvariant`
来自 `Rule2Genuine`），**故 §3 的主定理在 `conf` 上跑通**。

**⭐ 这是**非空实例性**的验证**（不是 `conf_effNull_invariant` 的重复：
那条只说前提成立，本条给出**结论**的实例）。 -/
theorem conf_doLaw2_indep_xz (x₁ x₂ z₁ z₂ y : Fin 2) :
    R246G3.Sem3.doLaw2 FateV2.Predict.R246G3.conf x₁ z₁ y = R246G3.Sem3.doLaw2 FateV2.Predict.R246G3.conf x₂ z₂ y :=
  doLaw2_indep_xz_of_effNull_invariant FateV2.Predict.R246G3.conf R249.Rule3.conf_effNull
    R248.Sem.conf_invariant x₁ x₂ z₁ z₂ y

/-- ⭐⭐⭐⭐⭐ **两前提**不互相蕴含**的见证**：`chain` 满足 `MediationInvariant`
（`Rule2Genuine.Sem.chain_invariant`）**但不满足** `EffNull`（`chain_not_effNull`）。

**⟹ §3 主定理的前件**不是恒假**（`chain` 满足一半），也**不是恒真**
（`chain_invariant_not_effNull` 说明两前提不等价）。 -/
theorem chain_invariant_not_effNull :
    R248.Sem.MediationInvariant R246G3.chain
      ∧ ¬ R249.Rule3.EffNull R246G3.chain :=
  ⟨R248.Sem.chain_invariant, R249.Rule3.chain_not_effNull⟩

/-- ⭐⭐⭐ **反面登记**：`chain` **不**满足 §3 主定理的前件，
且它在 `z` 上**真的会变**（`doLaw2 chain x 0 0 = 1 ≠ 0 = doLaw2 chain x 1 0`）。

**⭐ 意义**：这解释了为什么 §3 主定理**必须**要有 `EffNull` ——
去掉它，结论在 `chain` 上**直接假**。 -/
theorem chain_not_indep_z :
    ¬ (∀ (x : Fin 2) (z₁ z₂ y : Fin 2),
        R246G3.Sem3.doLaw2 R246G3.chain x z₁ y = R246G3.Sem3.doLaw2 R246G3.chain x z₂ y) := by
  intro h
  have hkey := h 0 0 1 0
  rw [FateV2.Predict.R246G3.doLaw2_chain, FateV2.Predict.R246G3.doLaw2_chain] at hkey
  norm_num at hkey

end Cross

/-! ===========================================================================
  §4 接入 `LawRule` 主链（⚠ **接口层，零新数学**）
  =========================================================================== -/

namespace Bridge

/-- ⭐⭐⭐ **规则 1 模型 `M1` 诱导的 `LawRule` 落在**单点档**。

**⚠ 诚实标注**：`isPoint_toLawRule` 对**任意** `SCM` 成立
（`PearlLawRuleBridge` §6），**本条不含新数学**。
它的唯一作用是在类型上把 `Rule13Genuine.Rule1.M1`
（本模块的上游，**已验证满足规则 1**）接到 `LawRule` 的 `IsPoint` 判定上。 -/
theorem M1_toLawRule_isPoint : LawRule.IsPoint R249.Rule1.M1.toLawRule :=
  R249.Rule1.M1.isPoint_toLawRule

/-- ⭐⭐ **`M1` 诱导的规则属于 `scmFamily`**（⚠ **同上，接口层**）。 -/
theorem M1_mem_scmFamily :
    R249.Rule1.M1.toLawRule ∈
      LawRuleSatisfiabilityConsumer.scmFamily (Fin 2) (Fin 2) :=
  ⟨R249.Rule1.M1, rfl⟩

end Bridge

end R740

end FateV2.Predict
