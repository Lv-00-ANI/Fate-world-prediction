import FateWorld.FateV2.Modeling.PearlHierarchy
import FateWorld.FateV2.Modeling.SCMGraph
import Mathlib.Probability.Independence.Conditional

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/SCMSemantics.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-007 D-008 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Modeling（正文 4 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Modeling
open FateV2.Predict

/-! ===========================================================================
  §68  **SCM → 概率语义的桥**（第 67 轮审计指出的**真正阻塞点**）

  ## ⚠ 背景：一次**结论的精确化**

  **第 66 轮我写**：
  > 缺的是**一个具体的元定理**：d-分离 $\implies$ 条件独立

  **⚠ 第 67 轮的服务器审计**发现这个说法**不够精确** ——
  **Mathlib **已经有** `ProbabilityTheory.CondIndepFun`
  （`Probability/Independence/Conditional.lean`），
  **且 `condIndepFun_iff` 给出了「条件独立 ⟺ 条件期望可分解」的精确刻画。**

  **⟹ 即**：**桥的**关键构件已存在**；
  **真正缺的是「SCM 语义 → 概率语义」的连接。**

  ## 本轮的任务

  **建这个连接的第一块**：**把有限 SCM **诱导的概率空间**显式构造出来。**

  | 构造 | 内容 |
  |---|---|
  | **`push`**（已有）| 有限律的推前 |
  | **`SCM.jointLaw`** | **SCM 的联合律** $(U, X, Y)$ |
  | **`SCM.marginalY`** | **$Y$ 的边缘律** |
  | **`SCM.condY`** | **$Y$ 关于 $X$ 的条件律** |

  **⚠ 本节的边界**：**只做**有限离散**的语义桥**；
  **不触及 `CondIndepFun` 的测度层**（那需要把有限律嵌入 `Measure`）。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Modeling

namespace SCMSemantics

universe u

variable {X Y : Type u}

/-! ### §68.1 联合律与边缘律 -/

/-- **SCM 的联合律**：外生 $u$ 下的三元组 $(u, x, h\,x)$。

$$\mathrm{jointLaw}\,M\,(u, x, y) :=
  \begin{cases}
    p_U(u) & y = \mathrm{sg}(u).2\ x\\
    0 & \text{否则}
  \end{cases}$$

**⟹ 这是把有限 SCM **显式嵌入概率论**的第一步。** -/
noncomputable def jointLaw (M : PearlHierarchy.SCM X Y) [DecidableEq Y] :
    M.U × X × Y → ℝ :=
  fun p => M.pU p.1 * if (M.sg p.1).2 p.2.1 = p.2.2 then 1 else 0

/-- **$X$ 的边缘律**（把 $Y$ 与 $U$ 边缘化）。

$$\mathrm{marginalX}\,M\,x := \sum_{u}\ p_U(u) \cdot [\mathrm{sg}(u).1 = x]$$ -/
noncomputable def marginalX (M : PearlHierarchy.SCM X Y) [DecidableEq X] : X → ℝ :=
  fun x => ∑ u, M.pU u * (if (M.sg u).1 = x then 1 else 0)

/-- **$Y$ 的边缘律**。 -/
noncomputable def marginalY (M : PearlHierarchy.SCM X Y) [DecidableEq Y] : Y → ℝ :=
  fun y => ∑ u, M.pU u * (if (M.sg u).2 (M.sg u).1 = y then 1 else 0)

/-! ### §68.2 观测条件下的 $Y$ 律 -/

/-- **$Y$ 在观测 $X = x$ 下的条件律**（**观测**口径，非干预）。

$$\mathrm{condY}\,M\,x\,y := \sum_{u}\ p_U(u) \cdot
  [\mathrm{sg}(u).1 = x] \cdot [\mathrm{sg}(u).2\ x = y]$$

**⚠ 与干预的区别**：
- **观测**：**筛选** $X = x$ 的外生实现（本篇）；
- **干预**：**替换** $X$ 为 $x$（第 64 轮的 `doX`）。

**⟹ 两者的差别正是「混杂」的来源** ——
**这是 backdoor 准则的**语义基础**。** -/
noncomputable def condY (M : PearlHierarchy.SCM X Y) [DecidableEq X] [DecidableEq Y] :
    X → Y → ℝ :=
  fun x y => ∑ u, M.pU u *
    (if (M.sg u).1 = x then 1 else 0) * (if (M.sg u).2 x = y then 1 else 0)

/-- **干预律**（第 64 轮 `doX` 的观测律，**重述为显式形式**）。

$$\mathrm{doLaw}\,M\,x\,y := \sum_{u}\ p_U(u) \cdot
  [\mathrm{sg}(u).2\ x = y]$$

**⟹ 与 `condY` 的差别**：**干预**不筛选** $x$**（没有 $[\mathrm{sg}(u).1 = x]$ 因子）。**

**⚠ 这正是「$do(x)$ 切断了 $X$ 的入边」的**数值体现**。** -/
noncomputable def doLaw (M : PearlHierarchy.SCM X Y) [DecidableEq Y] : X → Y → ℝ :=
  fun x y => ∑ u, M.pU u * (if (M.sg u).2 x = y then 1 else 0)

/-! ### §68.3 观测与干预的**分离**（**核心定理**） -/

/-- **观测律与干预律的关系**（**结构定理**）。

**陈述**：**无混杂时（$X$ 与外生 $U$ 独立）两者一致；
有混杂时一般不一致。**

**⚠ 本节给出**可证的部分**：
**当 $\mathrm{sg}$ 的第一分量与外生实现无关（常值）时，
**两条律**相等**** —— **因为此时「筛选 $X=x$」不再改变外生分布。**

**⟹ 即**：**「无混杂 $\implies$ 观测 = 干预」** ——
**这是 backdoor 准则的**最简特例**。** -/
theorem condY_eq_doLaw_of_no_confound (M : PearlHierarchy.SCM X Y)
    [DecidableEq X] [DecidableEq Y] (x₀ : X)
    (hconst : ∀ u, (M.sg u).1 = x₀) (hx : x = x₀) :
    condY M x = doLaw M x := by
  subst hx
  funext y
  unfold condY doLaw
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hconst u]
  simp

/-! ### §68.4 桥的**剩余缺口**（比第 66 轮更精确） -/

/- **剩余缺口的精确陈述**（**第 67 轮审计后更新**）。

**第 66 轮我说**：缺「d-分离 $\implies$ 条件独立」。
**第 67 轮审计后**：**该说法**不精确**** ——

| 构件 | 状态 |
|---|---|
| **`CondIndepFun`**（条件独立的概率定义）| **Mathlib 已有** |
| **`condIndepFun_iff`**（⟺ 条件期望可分解）| **Mathlib 已有** |
| **有限律的推前** | ✅ 本项目已有（`PearlHierarchy.push`）|
| **SCM 的联合/条件/干预律** | ✅ **本轮已建** |
| ⚠ **「有限律 → `Measure`」的嵌入** | ❌ **未做** |
| ⚠ **d-分离 $\implies$ 该嵌入下条件独立** | ❌ **未做** |

**⟹ 即**：**缺的不是「整座桥」，而是「桥的**两端**」**：
1. **把本轮的有限律嵌入 `Measure`**（使其可套用 `CondIndepFun`）；
2. **证明该嵌入下 d-分离蕴含条件独立**（Markov 性质）。

**⚠ 本定理**如实登记**这一点，**不把缺口说得比实际更大或更小**。** -/
/-! ### ⚠ 第 232 轮删除：`gap_precise_after_audit`

**此处原有** `theorem gap_precise_after_audit : (1 : ℕ) = 1 := rfl`，
**第 232 轮删除**，原因是**它不承载任何数学内容**：

* 名字承诺「审计后缺口精确」，**结论却只是 `1 = 1`** —— **名字与类型不符**；
* 它**不陈述**上文 `§68.4` 的缺口表，也**不蕴含**其中任何一项；
* 它**唯一的作用**是**抬高定理计数**（B7 评估代理已指出）。

**⟹ 处置**：**删除该定理**，**保留上方 `§68.4` 的缺口说明**作为模块文档 ——
**缺口本身仍然如实登记，只是不再以一条 `1 = 1` 充当「定理」。**

**⚠ 纪律**：删除**不**等于「缺口消失」；**登记**不**等于**「补上了」**。
本项目的立场是：**缺口该写明就写明，不该用空洞占位充数**。 -/

end SCMSemantics

end FateV2.Modeling
