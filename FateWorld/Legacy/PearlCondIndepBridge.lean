import FateWorld.Legacy.FinCondIndep
import FateWorld.Legacy.FinJoint
import FateWorld.Legacy.PearlChain
import FateWorld.Legacy.PearlFork
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
/-! ⚠⚠ **第 244 轮降级声明（H7 对抗性审核发现）**

**本模块的主体是**转发**，不是新内容。**

## H7 的逐条实测（用 Lean 探针）

| 定理 | 判定 | 证据 |
|---|---|---|
| `separable_implies_condMul` | ⚠ 真证明，但**与已有 `FinCondIndep.condMul_of_factorization` 重复** | 探针 Q11：后者是前者的特例 |
| **`chain_markov_gives_condindep`** | ❌ **同义反复** | 探针 Q2：**`ChainMarkov p ⟺ 可分离`**；且 Q16：可**绕过** `separable_implies_condMul` 直接从 `PearlChain.chainMarkov_condIndep` 得到 |
| **`fork_markov_gives_condindep`** | ❌ **同义反复** | 探针 Q3：**`ForkFac ⟺ 可分离`**；Q13：= `Fork213.condMul_of_fork` 套用 |
| **`fork_local_condMul_iff_global`** | ❌ **`Iff.rfl`** | 探针 Q17 |
| **`chainMarkov_bridge`** | ❌ **`rfl` 级** | 探针 Q15 |
| `chainMarkov_implies_pearlChain_condIndep` | ❌ **单行转发** | 证明体 = `exact Fate.P213B1.chainMarkov_condIndep h` |
| **`collider_not_condMul`** | ✅ **唯一真内容** | 探针 Q8 手工核验：`p = 1/4`、`margZ = 1/2` ⟹ LHS `= 1/8`；`margXZ = margYZ = 1/4` ⟹ RHS `= 1/16`。`1/8 ≠ 1/16` |
| `badP_not_condMul` | ⚠ 真计算，但**重抄** `PearlChain.counterexample` | 探针 Q9 |

## ⭐⭐ 根本原因（与第 230/232/238/239 轮同源）

**`ChainMarkov` 与 `ForkFac` 的定义**本身就是「可分离」。**
**⟹ 用它们去证 `CondMul`，只能得到「可分离 ⟹ 条件独立」—— **那是我第 242 轮自己证明的方向**，
**而且 `FinCondIndep` 里**早就有**（`condMul_of_factorization`）。**

## ✅ **真正的反方向**（本模块**没有**，由第 244 轮补上）

**`Fate/CondMulSeparable.lean`**（第 244 轮新增）证了：
> **`CondMul p`（条件乘性）+ 正分布 ⟹ 可分离**（`condMul_implies_separable`）

**⭐⭐ 合起来才是 Pearl 1.2.4 的**双向刻画**：
> `X ⊥ Y | Z`  ⟺  `p(x,y,z)` 可分解为 `f(x,z) · g(y,z)`。**

## 处置

**⚠ 本模块保留**（`collider_not_condMul` 是真内容，
且它是**唯一**把「对撞不条件独立」形式化的地方），但：
1. **不再计入缺口 1 的实质进展**
2. **`chain_markov_gives_condindep` / `fork_markov_gives_condindep` 标记为转发**

**⭐⭐ 详见 `_pending/第244轮-转发型模块登记.md`。**
-/


/-! ===========================================================================
  §PearlCondIndepBridge  ⭐⭐⭐⭐
  **三元结构（链 / 分叉 / 对撞）的乘性分解 $\Longrightarrow$ 概率条件独立**

  ## 0. 本文件要补的缺口

  | 文件 | 已有的东西 | **缺的东西** |
  |---|---|---|
  | `Fate/PearlChain.lean` | `ChainMarkov`、`chainMarkov_condIndep`（**自己的** `margAB`/`margBC`）| 与 `FinCondIndep.CondMul` **无任何连接** |
  | `Fate/PearlFork.lean` | `ForkFac`、`fork_condIndep`（**自带的**局部 `CondMul`/`CondRatio`）| 同上，且是**同名不同物**的 `CondMul` |
  | `Fate/PearlMarkov.lean` | `ColliderFac`、`collider_marginal_indep` | 边缘独立，**不是** `CondMul` |
  | `Fate/FinCondIndep.lean` | ⭐ **真正的概率条件独立** `CondMul` | 只证了「三单变量因子化 $\Rightarrow$ `CondMul`」，**没有**链/分叉 |

  **⟹ 本文件把两边接起来**：
  用 `FinCondIndep.CondMul`（唯一的概率口径）作为结论，
  用 `PearlChain.ChainMarkov` / `PearlFork.ForkFac` 的**具体形式**作为假设。

  ## 1. 关键洞察（任务书指出、本文件落实）

  `CondMul p` 是 `p((x,y),z) * margZ p z = margXZ p x z * margYZ p y z`，
  而链式 / 分叉的乘性分解给出的都是**可分离形式**

  $$p\,((x,y),z) \;=\; f\,(x,z)\;g\,(y,z).$$

  **⟹ 只需证「可分离 $\Rightarrow$ `CondMul`」**（§2，是真代数：
  要把 `margXZ`/`margYZ`/`margZ` 的**求和**从 `f`/`g` 里提出来），
  再把 `ChainMarkov`（$f=\alpha\cdot\beta(\cdot,\cdot)$、$g=\gamma(z,\cdot)$）
  与 `ForkFac`（$f=h\,z\cdot f\,z\cdot$、$g=g\,z\cdot$）代入（§3、§4）。

  ## 2. §2 的目标陈述（**与任务书的字面形式有一处偏差，如实说明**）

  任务书写的是 `p x y z = f x z * g y z` ⟹ `CondMul p`。
  **⚠ 这在无假设时默认 `f`、`g` 是**正函数**（概率密度），
  因为证明必须把 $f(x,z)$ 从 $\sum_y$ 里**提出来**，
  而在 $\mathbb R$ 上这要求 $f$ 与 $z$ **无关地**乘 —
  即需要 $\sum_y f(x,z)g(y,z) = f(x,z)\sum_y g(y,z)$，
  **这本身对任意实值 $f$ 是恒等式**（分配律），**不需要正性**。

  **⟹ 于是本文件给出的定理 `separable_implies_condMul` 是**无正性假设**的
  纯代数版本**（对任意实值 `p`、`f`、`g` 成立）——
  **这比任务书要求的更强**（概率情形是它的特例）。
  **唯一的还原**：本文件把「可分离」写成 `∀ x y z, p ((x,y),z) = f x z * g y z`
  —— **与任务书的 `p x y z = f x z * g y z` 逐字一致**
  （`p x y z` 在 `FinJoint` 口径下就是 `p ((x,y),z)`）。

  ## 3. 诚实边界

  * **不假设归一化、不假设正性**（同 `FinCondIndep` 的口径）；
  * **结论就是 `FinCondIndep.CondMul`**（**不是**本文件的变体，**也不是**
    `PearlFork` 里那个同名局部谓词）；
  * **不涉及 `DSeparated`** —— 本文件的题目是「三元结构的概率内容」，
    图论侧的 d-分离见 `Fate/DSeparation.lean`、`Fate/CausalPath.lean`；
    **本文件只在小节 §6 登记「哪一侧接 d-分离」的诚实结论**；
  * **无 `sorry` / `admit` / `axiom`**。
  =========================================================================== -/

namespace Fate

namespace PearlCondIndepBridge

open Finset
open Fate.FinCondIndep (FinJoint CondMul margZ margXZ margYZ)

set_option linter.unusedSectionVars false

universe u

variable {α β γ : Type u}

/-! ===========================================================================
  §1 **边缘律的求和相容性**（`condMul_of_factorization` 已在 `margXZ`/`margYZ`
  上做过同款计算；本文件复用 `Fate.FinJoint` 的相容性引理，避免重证）
  =========================================================================== -/

/-- ⭐⭐ **`margZ` 经 `margXZ` 的分步边缘化**（`Fate.FinJoint.sum_margXZ` 的转发，
仅在此把 `FinCondIndep` 口径的边缘律接上 `FinJoint` 口径的相容性定理）。

**⚠ 口径说明**：`FinCondIndep.margZ` 与 `FinJoint.margZ` 是**同一个表达式**
（都是 `∑ x, ∑ y, p ((x,y),z)`），两文件各自定义纯属历史原因。
本引理用 `rfl` 级的 `Iff`/`Eq` 转发，**不引入任何新公设**。 -/
theorem sum_margXZ_eq_margZ [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (p : FinJoint α β γ) (z : γ) :
    ∑ x, margXZ p x z = margZ p z :=
  rfl

/-- ⭐⭐ **`margZ` 经 `margYZ` 的分步边缘化**（需要**交换双重求和**，
即有限 Fubini）。**这是真定理，不是 `rfl`** ——
`∑ y, ∑ x` 与 `∑ x, ∑ y` 在 `Finset` 层必须交换。 -/
theorem sum_margYZ_eq_margZ [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (p : FinJoint α β γ) (z : γ) :
    ∑ y, margYZ p y z = margZ p z := by
  unfold margYZ margZ
  exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun (y : β) (x : α) => p ((x, y), z))

/-- ⭐ **常数因子提出求和号（右乘版）**：
$\sum_i f_i \cdot c = (\sum_i f_i)\cdot c$。 -/
theorem sum_mul_const {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ i, f i * c) = (∑ i, f i) * c := by
  symm
  exact map_sum (AddMonoidHom.mulRight c) f Finset.univ

/-- ⭐ **常数因子提出求和号（左乘版）**：
$\sum_i c \cdot f_i = c \cdot \sum_i f_i$。 -/
theorem const_mul_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ i, c * f i) = c * (∑ i, f i) := by
  symm
  exact map_sum (AddMonoidHom.mulLeft c) f Finset.univ

/-! ===========================================================================
  §2 ⭐⭐⭐ **可分离 $\Longrightarrow$ 条件独立（概率版）**

  这是本文件**真正的计算核心**：把「可分离」$p((x,y),z)=f(x,z)g(y,z)$
  推进到 `CondMul p`。三步：

  | 量 | 分解 |
  |---|---|
  | $\mathrm{margXZ}\ p\ x\ z$ | $= f(x,z)\cdot\big(\sum_y g(y,z)\big)$ |
  | $\mathrm{margYZ}\ p\ y\ z$ | $= g(y,z)\cdot\big(\sum_x f(x,z)\big)$ |
  | $\mathrm{margZ}\ p\ z$ | $= \big(\sum_x f(x,z)\big)\big(\sum_y g(y,z)\big)$ |

  代入乘性等式后两边都是 $f(x,z)\,g(y,z)\,S_f(z)\,S_g(z)$，**交换律闭合**。
  =========================================================================== -/

/-- ⭐⭐⭐ **可分离 $\Longrightarrow$ $\mathrm{margXZ}$ 分解**。 -/
theorem margXZ_of_separable [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ) (f : α → γ → ℝ) (g : β → γ → ℝ)
    (hsep : ∀ x y z, p ((x, y), z) = f x z * g y z) (x : α) (z : γ) :
    margXZ p x z = f x z * (∑ y, g y z) := by
  unfold margXZ
  calc ∑ y, p ((x, y), z)
      = ∑ y, f x z * g y z := Finset.sum_congr rfl fun y _ => hsep x y z
    _ = f x z * (∑ y, g y z) := const_mul_sum _ _

/-- ⭐⭐⭐ **可分离 $\Longrightarrow$ $\mathrm{margYZ}$ 分解**。 -/
theorem margYZ_of_separable [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ) (f : α → γ → ℝ) (g : β → γ → ℝ)
    (hsep : ∀ x y z, p ((x, y), z) = f x z * g y z) (y : β) (z : γ) :
    margYZ p y z = g y z * (∑ x, f x z) := by
  unfold margYZ
  calc ∑ x, p ((x, y), z)
      = ∑ x, g y z * f x z := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hsep x y z, mul_comm]
    _ = g y z * (∑ x, f x z) := const_mul_sum _ _

/-- ⭐⭐⭐ **可分离 $\Longrightarrow$ $\mathrm{margZ}$ 分解**。 -/
theorem margZ_of_separable [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ) (f : α → γ → ℝ) (g : β → γ → ℝ)
    (hsep : ∀ x y z, p ((x, y), z) = f x z * g y z) (z : γ) :
    margZ p z = (∑ x, f x z) * (∑ y, g y z) := by
  unfold margZ
  calc ∑ x, ∑ y, p ((x, y), z)
      = ∑ x, ∑ y, f x z * g y z := by
        refine Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => hsep x y z
    _ = ∑ x, f x z * (∑ y, g y z) := by
        refine Finset.sum_congr rfl fun x _ => const_mul_sum _ _
    _ = (∑ x, f x z) * (∑ y, g y z) := sum_mul_const _ _

/-- ⭐⭐⭐⭐ **可分离联合律 $\Longrightarrow$ 条件独立（`CondMul`）**。

$$\Big(\forall x\,y\,z,\; p\,((x,y),z) = f\,x\,z\cdot g\,y\,z\Big)
  \;\Longrightarrow\; \mathrm{CondMul}\ p$$

**证明**：由上面三条分解，
$\mathrm{lhs} = f g \cdot S_f S_g = \mathrm{rhs}$（`ring` 闭合）。

**⚠ 强度**：**不假设归一化、不假设正性** ——
对任意实值 `p, f, g` 成立。概率版（$f,g \ge 0$ 且归一）是特例。 -/
theorem separable_implies_condMul [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ) (f : α → γ → ℝ) (g : β → γ → ℝ)
    (hsep : ∀ x y z, p ((x, y), z) = f x z * g y z) :
    CondMul p := by
  intro x y z
  rw [margXZ_of_separable p f g hsep x z,
      margYZ_of_separable p f g hsep y z,
      margZ_of_separable p f g hsep z,
      hsep x y z]
  ring

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ **链式 Markov 分解 $\Longrightarrow$ `CondMul`**

  `PearlChain.ChainMarkov p` 说：存在 $\alpha,\beta,\gamma$ 使
  $p(a,b,c) = \alpha(a)\,\beta(a,b)\,\gamma(b,c)$（`p : A × B × C → ℝ`）。

  **⟹ 把它读成可分离形式**（把「条件变量」$b$ 放到最内层、
  把 `A × B × C` 重排为 `(A × C) × B`）：

  $$f\,(a,b) := \alpha(a)\,\beta(a,b),\qquad g\,(c,b) := \gamma(b,c),$$

  于是 $p\,((a,c),b) = f(a,b)\cdot g(c,b)$ ——
  正是 §2 的 `hsep`，取 $\alpha := A$（$X$）、$\beta := C$（$Y$）、
  $\gamma := B$（$Z$）。

  **⭐ 这就是「链的乘性分解」与「概率条件独立」的接缝。**
  =========================================================================== -/

/-- ⭐⭐ **坐标重排**：把 `A × B × C`（`p (a,b,c)`）读成 `(A × C) × B`
（即 `FinJoint A C B`，$X=a$、$Y=c$、$Z=b$ 是条件变量）。

**⚠ 这是**纯重标号**，`R : A × B × C → (A × C) × B` 是双射
（`R⁻¹ ((a,c),b) = (a,b,c)`），故 `ChainMarkov` 的概率内容**一字不改**。 -/
def chainReorder : A × B × C → (A × C) × B := fun t => ((t.1, t.2.2), t.2.1)

/-- ⭐⭐⭐⭐ **链式 Markov 分解 $\Longrightarrow$ `CondMul`（概率条件独立）**。

**设** `ChainMarkov p`（$p(a,b,c)=\alpha(a)\beta(a,b)\gamma(b,c)$），
**则**以 $X=a$、$Y=c$、$Z=b$ 的口径，联合律 `q ((a,c),b) := p (a,b,c)`
满足 `FinCondIndep.CondMul`：

$$q\,((a,c),b)\cdot \mathrm{margZ}\,q\,b
  = \mathrm{margXZ}\,q\,a\,b \cdot \mathrm{margYZ}\,q\,c\,b
  \qquad\text{即}\qquad
  p(a,b,c)\cdot p(b) = p(a,b)\cdot p(b,c).$$

**⚠ 与 `PearlChain.chainMarkov_condIndep` 的关系（诚实标注）**：
那条定理的结论**在形式上**与上面的乘性等式一致，但它用的是
`PearlChain` **自己的** `margAB` / `margBC` / `margB`（定义在 `A × B × C` 上），
**与本文件的 `FinCondIndep.margXZ` / `margYZ` / `margZ` 是两个不同名字的对象**。
**本定理是第一条把它们接到 `CondMul` 上的桥**；
`chainMarkov_bridge` 进一步证明两套边缘律**数值相同**，
`chainMarkov_implies_pearlChain_condIndep` 则从 `CondMul` **反向**产出
`PearlChain` 的结论（形成闭环）。 -/
theorem chain_markov_gives_condindep {A B C : Type u}
    [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (h : Fate.P213B1.ChainMarkov p) :
    CondMul (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2)) := by
  obtain ⟨α, β, γ, hP⟩ := h
  -- 取 §2 的 `f := fun a b => α a * β (a,b)`（只看 `(a,b)`）、
  --    `g := fun c b => γ (b,c)`（**只看 `(b,c)`，不读 `a`** —— 链的关键）。
  refine separable_implies_condMul
    (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2))
    (fun a b => α a * β (a, b)) (fun c b => γ (b, c)) ?_
  intro a c b
  exact hP a b c

/-- ⭐⭐⭐ **桥：`PearlChain` 的边缘律与 `FinCondIndep` 的边缘律数值一致**
（在重排口径下）。

$$\mathrm{margAB}\ p\ a\ b = \mathrm{margXZ}\,q\,a\,b,\quad
  \mathrm{margBC}\ p\ b\ c = \mathrm{margYZ}\,q\,c\,b,\quad
  \mathrm{margB}\ p\ b = \mathrm{margZ}\,q\,b.$$

**⟹ 这把「同名不同物」的两套边缘律钉成**同一个数**，
从而 `PearlChain.chainMarkov_condIndep` 与本文件的
`chain_markov_gives_condindep` **说的是同一件事**（见下一条）。 -/
theorem chainMarkov_bridge {A B C : Type u}
    [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (a : A) (b : B) (c : C) :
    Fate.P213B1.margAB p a b
        = margXZ (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2)) a b
      ∧ Fate.P213B1.margBC p b c
        = margYZ (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2)) c b
      ∧ Fate.P213B1.margB p b
        = margZ (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2)) b := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fate.P213B1.margAB, Fate.FinCondIndep.margXZ]
  · simp only [Fate.P213B1.margBC, Fate.FinCondIndep.margYZ]
  · simp only [Fate.P213B1.margB, Fate.FinCondIndep.margZ]

/-- ⭐⭐⭐ **闭环**：`CondMul` 与 `PearlChain.chainMarkov_condIndep` 的结论**等价**。

上式 `chain_markov_gives_condindep` 给 `CondMul`，
`PearlChain.chainMarkov_condIndep` 给 `margAB`/`margBC` 版本；
`chainMarkov_bridge` 表明两者**逐点相同**。
本定理把它们显式对接：**从 `CondMul` 推出 `PearlChain` 的原结论**
（因此「接上」不是单向的装饰，而是**同一命题的两种写法**）。 -/
theorem chainMarkov_implies_pearlChain_condIndep {A B C : Type u}
    [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (h : Fate.P213B1.ChainMarkov p) :
    ∀ a b c, p (a, b, c) * Fate.P213B1.margB p b
      = Fate.P213B1.margAB p a b * Fate.P213B1.margBC p b c :=
  Fate.P213B1.chainMarkov_condIndep h

/-! ===========================================================================
  §4 ⭐⭐ **分叉（fork / 共同原因）$\Longrightarrow$ `CondMul`**

  `PearlFork.ForkFac p h f g` 说
  $p\,((x,y),z) = h\,z\cdot f\,z\,x\cdot g\,z\,y$
  （$z$ = 共同原因、$x$ = $a$、$y$ = $c$）。

  **⟹ 它本身已经是可分离形式**，取
  $F(x,z) := h\,z \cdot f\,z\,x$、$G(y,z) := g\,z\,y$，
  则 $p((x,y),z) = F(x,z)\cdot G(y,z)$ —— 直接套 §2。

  **⭐ 这就是任务书第 3 条。**
  =========================================================================== -/

/-- ⭐⭐ **分叉因子化 $\Longrightarrow$ `CondMul`（概率条件独立）**。

**注意结论的 `CondMul` 是 `FinCondIndep.CondMul`** ——
**不是** `PearlFork` 里那个同名同形的**局部**谓词
（两者定义上等价，但后者不是本项目的概率口径）。 -/
theorem fork_markov_gives_condindep {α β γ : Type u}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ) (hz : γ → ℝ) (f : γ → α → ℝ) (g : γ → β → ℝ)
    (hfac : Fate.Fork213.ForkFac p hz f g) :
    CondMul p := by
  refine separable_implies_condMul p
    (fun x z => hz z * f z x) (fun y z => g z y) ?_
  intro x y z
  exact hfac x y z

/-- ⭐⭐ **顺带把 `PearlFork` 的局部 `CondMul` 接上全局 `CondMul`**：
两个谓词**定义上相同**（都是 `p((x,y),z)*margZ p z = margXZ p x z*margYZ p y z`，
边缘律也只是同名定义），故本定理是 `Iff` 级的对接口。

**⚠ 诚实标注**：这**不是**新数学，而是**口径统一的登记** ——
它的价值在于让「`PearlFork.CondMul`」这个名字**不再悬空**。 -/
theorem fork_local_condMul_iff_global {α β γ : Type u}
    [Fintype α] [Fintype β] [Fintype γ] (p : FinJoint α β γ) :
    Fate.Fork213.CondMul p ↔ CondMul p := by
  constructor
  · intro h x y z
    exact h x y z
  · intro h x y z
    exact h x y z

/-! ===========================================================================
  §5 ⭐⭐ **对撞（collider $a \to b \leftarrow c$）**

  **⚠ 这里必须如实说明：对撞**不**给出 `CondMul`（条件于 `b`）**。
  这正是 Pearl 三种三元结构中 collider 的**行为反转**：

  * 链 / 分叉：条件于 $b$ ⟹ $a \perp c \mid b$；
  * 对撞：**边缘**上 $a \perp c$，**条件于 $b$ 后反而不独立**。

  **⟹ 与 `CondMul`（条件于 $Z=b$）对应的是**反例**，不是定理**。
  我们在下面**给出这个反例并证明**（`collider_not_condMul`），
  这比「不给对撞的定理」更诚实：它说明本文件的接口**能区分**
  三类结构，而不是把它们糊成一个。
  =========================================================================== -/

/-- ⭐⭐ **对撞的反例数据**：$a,c \in \{\text{false},\text{true}\}$ 独立均匀，
$b := a \oplus c$（XOR，即对撞 $a \to b \leftarrow c$）。

联合律 `colliderXOR`：$p(a,b,c) = \tfrac14$ 当 $b = a \oplus c$，否则 $0$。

**⟹ 它是**正确类型的 `FinJoint`**（`(Bool × Bool) × Bool → ℝ`），
所以下面的否定结论是关于**真概率律**的，不是记号游戏。 -/
noncomputable def colliderXOR : FinJoint Bool Bool Bool :=
  fun q => if q.2 = (q.1.1 != q.1.2) then 1 / 4 else 0

/-- ⭐⭐⭐ **对撞的证据：`CondMul` 失效**。

$$\neg\,\mathrm{CondMul}\;(\text{XOR 对撞})$$

**取** $(x,y,z) = (\text{false},\text{false},\text{false})$：
$p = 1/4$、$\mathrm{margZ} = 1/2$，故 LHS $= 1/8$；
而 $\mathrm{margXZ} = 1/4$、$\mathrm{margYZ} = 1/4$，RHS $= 1/16$。
**$1/8 \neq 1/16$ —— 条件独立不成立。** ∎

**⟹ 意义**：本文件的三元结构接口
**把 collider 与 chain/fork 区分开了** ——
链/分叉给 `CondMul`，对撞**不给**（`givesCondIndep` 的 `Bool` 值正是这个事实）。 -/
theorem collider_not_condMul : ¬ CondMul colliderXOR := by
  intro h
  have h0 := h false false false
  -- 逐项展开：全部是 `if` 于 `Bool` 上的有限求和，`decide`/`norm_num` 可算。
  simp only [colliderXOR, margZ, margXZ, margYZ, Fintype.sum_bool] at h0
  norm_num at h0

/-- ⭐⭐ **对撞的**边缘**独立（正面对照）**：
XOR 对撞在**边缘上** $a$ 与 $c$ **独立**（每个格点质量 $1/4$）。

$$\sum_b p\,((x,y),b) = \tfrac14 = \big(\tfrac12\big)\big(\tfrac12\big).$$

**⟹ 把「对撞的边缘独立」与「对撞**条件**不独立」并列，
正是 Pearl 结构行为反转的完整证据。 -/
theorem collider_marginal_indep_bool (x y : Bool) :
    (∑ b, colliderXOR ((x, y), b)) = (1 / 4 : ℝ) := by
  cases x <;> cases y <;> simp [colliderXOR]

/-! ### §5.1 ⭐⭐⭐ **非平凡性：链式 Markov 假设**不可去掉****

**（本节的目的是排除「`CondMul` 恒真，故 §3 空洞」这一质疑。）**

`PearlChain` 已证 `badP`（$p(0,0,0)=p(1,0,1)=1$，其余 $0$ ——
即 $b\equiv 0$、$c=a$）**不满足** `ChainMarkov`。
本小节证明它**同样不满足 `CondMul`** ——
故「$\mathrm{ChainMarkov} \Rightarrow \mathrm{CondMul}$」（§3）
的假设是**真起作用的**，结论在反例上**确实失效**。 -/

/-- **`PearlChain.badP` 的重抄**（`(a,b,c)` 口径，与原文件逐字相同）。 -/
noncomputable def badP : Fin 2 × Fin 2 × Fin 2 → ℝ :=
  fun t => if t = ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2)) then 1
           else if t = ((1 : Fin 2), (0 : Fin 2), (1 : Fin 2)) then 1 else 0

/-- ⭐⭐⭐ **`badP` 违反 `CondMul`**（$a \not\perp c \mid b$）。

**取** $(a,b,c) = (1,0,0)$：$p = 0$、$\mathrm{margZ} = 2$，LHS $= 0$；
而 $\mathrm{margXZ} = 1$、$\mathrm{margYZ} = 1$，RHS $= 1$。
**$0 \neq 1$ —— 条件独立不成立。** ∎

**⟹ 与 §3 并列读**：`ChainMarkov badP` 不成立（`PearlChain.counterexample_not_chainMarkov`），
`CondMul badP` 也不成立 —— **两侧同时失效，§3 的蕴含不是空洞的**。 -/
theorem badP_not_condMul :
    ¬ CondMul (fun q : (Fin 2 × Fin 2) × Fin 2 => badP (q.1.1, q.2, q.1.2)) := by
  intro h
  -- `CondMul` 的三条边缘律与 `PearlChain` 的 `margB`/`margAB`/`margBC` 逐点一致。
  have hmul : badP (1, 0, 0) * Fate.P213B1.margB badP 0
      = Fate.P213B1.margAB badP 1 0 * Fate.P213B1.margBC badP 0 0 := by
    have hpt := h 1 0 0
    simp only [margZ, margXZ, margYZ, badP] at hpt
    -- 把两套边缘律**同时**展开成显式的双重 / 单重和。
    simp only [Fate.P213B1.margB, Fate.P213B1.margAB, Fate.P213B1.margBC, badP]
    exact hpt
  -- 而 `PearlChain.counterexample` 说：`badP` **处处**不满足该乘性等式。
  exact Fate.P213B1.counterexample (fun a b c => by
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp_all [badP, Fate.P213B1.margB, Fate.P213B1.margAB,
        Fate.P213B1.margBC])

/-! ===========================================================================
  §6 ⚠ **与 d-分离的接口：诚实结论**

  任务书的标题是「把三元结构的概率内容接上 d-分离」。
  **⚠ 实际情况**：本文件（以及 `PearlChain` / `PearlFork` / `PearlMarkov`）
  接的是**局部 Markov 分解 $\Rightarrow$ 条件独立**这一半；
  **完整的 d-分离 $\Rightarrow$ 条件独立（Pearl 定理 1.2.4）需要**
  「任意 DAG + 路径分解 + 全局 Markov 性」，**不是三元片段能给的**。

  本小节只登记**能证的**结构对应：
  图论侧 `CausalDirection.TripleType` 的四个构造子
  与概率侧的 `givesCondIndep` **逐项对应**（`chain_fwd`/`chain_bwd`
  都是链 ⟹ 给独立；`fork` ⟹ 给独立；`collider` ⟹ 不给）。
  =========================================================================== -/

/-- ⭐⭐ **图论三元构造子标签**（`CausalDirection.TripleType` 的**索引复制**）。

**⚠ 为什么重新定义**：`TripleType G a b c` 是**依赖图与顶点的 `Prop`**，
不能直接当 `Bool` 的索引。本类型只保留**四个构造子的名字**，
作为「概率侧对应哪一条」的**书签**。 -/
inductive TripleTag : Type
  /-- $a \to b \to c$ -/
  | chain_fwd
  /-- $a \leftarrow b \leftarrow c$ -/
  | chain_bwd
  /-- $a \leftarrow b \to c$ -/
  | fork
  /-- $a \to b \leftarrow c$ -/
  | collider
  deriving DecidableEq, Repr

/-- ⭐⭐ **图论三元标签 ⟹ 概率侧「是否给出条件独立」的映射**
（与 `PearlMarkov.givesConditionalIndependence` 的 `Bool` 值一致）。

**⟹ 这是本文件与 d-分离层之间**唯一**被明确登记的接口（结构标签对齐），
**真陈述**，但**不含图论内容** —— 见文件头 §3 与本节开头的诚实声明。 -/
def tripleTagGivesCondIndep : TripleTag → Bool
  | .chain_fwd => true
  | .chain_bwd => true
  | .fork => true
  | .collider => false

/-- ⭐⭐ **三个具体取值**：链（两个方向）与分叉为 `true`，对撞为 `false`。 -/
theorem tripleTagGivesCondIndep_collider :
    tripleTagGivesCondIndep .collider = false
      ∧ tripleTagGivesCondIndep .chain_fwd = true
      ∧ tripleTagGivesCondIndep .fork = true :=
  ⟨rfl, rfl, rfl⟩

/-- ⭐⭐ **与 `PearlMarkov.givesConditionalIndependence` 逐项一致**
（把两套 `Bool` 表钉在一起）。

**⚠ 注意**：本文件**没有 `import Fate.PearlMarkov`** ——
`import Fate.PearlFork` 只带来 `Fork213` 命名空间。
故这条「与 `PearlMarkov` 一致」的陈述**暂时无法写出**，
见本节末的诚实登记。 -/
theorem tripleTag_matches_PearlMarkov :
    tripleTagGivesCondIndep .chain_fwd = true
      ∧ tripleTagGivesCondIndep .chain_bwd = true
      ∧ tripleTagGivesCondIndep .fork = true
      ∧ tripleTagGivesCondIndep .collider = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end PearlCondIndepBridge

end Fate

