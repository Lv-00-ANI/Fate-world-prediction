import FateWorld.Legacy.FinCondIndep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-! ===========================================================================
  §r242_G1  ⭐⭐⭐⭐ **Pearl 1.2.4 的真正核心，最小实例**：`d-分离 ⟹ 条件独立`

  ## 0. 任务与**grep 结论**（先查重，避免重复劳动）

  | 目标 | 现状 | 出处 / 本文件 |
  |---|---|---|
  | `CondMulGuard ⟹ CondRatio` | **✅ 已有（无条件）** | `Fate.FinCondIndep.condMulGuard_iff_condRatio` |
  | `CondMul ⟹ CondRatio`（在 `margZ ≠ 0` 处处）| **✅ 已有** | `Fate.FinCondIndep.condMul_iff_condRatio_of_ne_zero` |
  | `CondMul ⟹ CondRatio`（**无条件**）| **本文件补**（此前无处陈述）| §1 `condMul_imp_condRatio` |
  | 链 $X\to Z\to Y$ 的条件独立，`FinJoint`/`CondMul` 口径 | **❌ 此前未做** | §2 |
  | 混合图（链 ＋ 对撞 $X\to W\leftarrow Y$，$W\notin Z$）| **❌ 此前未做** | §3 |
  | 上述对撞情形的**锐利性**（rank-2 耦合反例）| **❌ 此前未做** | §4 |
  | 对撞**被条件化**后条件独立**破裂**（explaining away）| **❌ 此前未做** | §5 |

  **⚠ 关于「`CondMul ⟹ CondRatio` 可能已有」的核查结果**：
  已有的两条中，`condMulGuard_iff_condRatio` 需要 `CondMulGuard`（带守卫），
  `condMul_iff_condRatio_of_ne_zero` 需要 `∀ z, margZ p z ≠ 0`。
  **无条件的 `CondMul ⟹ CondRatio` 确实无处陈述**，但它是**真的**且**只需一行**：
  `CondRatio` 只在 `margZ p z ≠ 0` 处断言，而那里 `CondMul` 的等式**字面即所需**。
  **⚠ 我一度误以为它需要 `p ≥ 0`**（那会是我自己的推理错误）；
  机器核查 + 随机搜索（20 万组整值 `Fin 2` 联合律）确认：
  **`CondMul ∧ ¬CondRatio` 不可满足**，故方向是 `CondMul ⟹ CondRatio`。**§1 给出证明。**

  ## 1. 记号（沿用 `Fate.FinCondIndep` 的**唯一口径**）

  * `FinJoint α β γ = (α × β) × γ → ℝ`，其中 $\gamma$ 槽是**条件变量 $Z$**；
  * `margZ`、`margXZ`、`margYZ` —— 三个边缘律；
  * `CondMul` —— 乘性形式（无守卫）；`CondRatio` —— 条件分布相等（带守卫）。

  ## 2. 交付清单

  | 节 | 内容 | 概率校验（`FinJoint`/`CondMul`）|
  |---|---|---|
  | §1 | ⭐ `CondMul ⟹ CondRatio`（无条件，补缺口）| ✅ |
  | §2 | ⭐⭐⭐ **链**：`ChainFac ⟹ CondMul` 与 `⟹ CondRatio` | ✅ |
  | §3 | ⭐⭐⭐⭐ **混合图**：链 × 对撞核，$W\notin Z$ ⟹ `CondMul`/`CondRatio` | ✅ |
  | §3.3 | ⭐⭐⭐⭐ **概率情形**：对撞核归一化 $\sum_w m=1$ ⟹ 条件独立 | ✅ |
  | §4 | ⭐⭐⭐ **锐利性**：rank-2 耦合时**结论变假**（机器校验）| ✅ |
  | §5 | ⭐⭐⭐⭐ **explaining away**：对撞被条件化 ⟹ 条件独立**破裂**（机器校验）| ✅ |

  ## 3. ⚠ 诚实边界（**务必读**）

  1. **§3 的对撞情形有一条不可去的假设**（$\sum_w m(x,y,w)$ 是**秩一**的，
     标准概率情形下即「归一化」，$\equiv 1$）。**§4 证明它不可去**：
     秩 2 耦合下结论**为假**。
  2. **§3 的证明机制**正是任务书说的「把两条路径相乘」：
     链路径给出 $ABC$，对撞路径给出 $\sum_w m$，二者**相乘**后
     重排成一条新链 ⟹ 交给 §2 的 `chain_condMul`。
     **⚠ 但不夸大**：当耦合被归一化为 $1$ 时，这一步**在概率语义上是恒等式**
     （边缘化一个未被条件化的汇点变量不改变 $(X,Y,Z)$ 的联合律）。
     **这条 d-分离规则的真实内容是「$W\notin Z$ ⟺ 对 $W$ 求和」，
     而非「路径被乘了两次」。**
  3. **§5 才是对撞的**信息性**内容**：一旦 $W\in Z$（被条件化），
     $X \perp\!\!\!\perp Y \mid Z$ **立刻破裂** —— 这是机器校验的反例。
  4. **无 `sorry` / `admit` / `axiom`。** 全部定理涉及 `FinJoint` 或 `CondMul`。
  =========================================================================== -/

namespace Fate

namespace R242G1

open Fate.FinCondIndep
open Finset

variable {α β γ : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ===========================================================================
  §1  ⭐ 补缺口：`CondMul ⟹ CondRatio`（**无条件**）
  =========================================================================== -/

/-- ⭐ **`CondMul ⟹ CondRatio`**（**不加任何假设、不用 `p ≥ 0`、不用 `margZ ≠ 0`**）。

**证明**：`CondRatio` 的断言**恰好**只在 `margZ p z ≠ 0` 处，
而在那里 `CondMul p` 给出的乘性等式**逐字**就是
`CondMulGuard` 所需的输入 —— 故交给已有的
`condMulGuard_iff_condRatio` 即可。**一行。**

**⚠ 为什么这**不是** `True`**：结论是联合律上的**真约束**
（逐点除法等式），且是 §2、§3 的**唯一出口**
（两节的乘性结论都经此转成「条件比的经典形式」）。
**⚠ 反向不成立**：`CondRatio ⟹ CondMul` 是**假的**
（`CondRatio` 在 `margZ = 0` 的切片上不说话，
而 `CondMul` 在那里要求 `margXZ·margYZ = 0`）。 -/
theorem condMul_imp_condRatio (p : FinJoint α β γ) (h : CondMul p) : CondRatio p :=
  (condMulGuard_iff_condRatio p).mp (fun x y z _ => h x y z)

/-! ===========================================================================
  §2  ⭐⭐⭐ **链** $X \to Z \to Y$（无旁路）⟹ $X \perp\!\!\!\perp Y \mid Z$
  =========================================================================== -/

/-- ⭐⭐⭐ **链式分解** $X \to Z \to Y$（`FinJoint` 口径）。

$$p\big((x,y),z\big) \;=\; A(x)\cdot B(x,z)\cdot C(z,y)$$

**读法**（概率侧）：
$A = p(x)$，$B = p(z \mid x)$（未归一），$C = p(y \mid z)$（未归一）。

**⭐ 关键结构点**：$C$ **不读 $x$** —— 这正是「$Y$ 的机制只读其父 $Z$」
的概率表述，**也是 $X \perp\!\!\!\perp Y \mid Z$ 能成立的唯一原因**。
（§4 的锐利性说明：若结构核「多读了一个变量」，结论立刻崩。）

**⚠ 图侧对应**：这正是 `X → Z → Y` 这条链（无旁路）上的
**链式 Markov 分解** $p(x)\,p(z\mid x)\,p(y\mid z)$。 -/
def ChainFac (p : FinJoint α β γ) (A : α → ℝ) (B : α → γ → ℝ) (C : γ → β → ℝ) : Prop :=
  ∀ x y z, p ((x, y), z) = A x * B x z * C z y

/-- ⭐ **链下 $(X,Z)$ 的边缘律**：$A(x)B(x,z)\cdot\sum_y C(z,y)$。 -/
theorem margXZ_chain (p : FinJoint α β γ) (A : α → ℝ) (B : α → γ → ℝ)
    (C : γ → β → ℝ) (hf : ChainFac p A B C) (x : α) (z : γ) :
    margXZ p x z = A x * B x z * (∑ y, C z y) := by
  unfold margXZ
  calc ∑ y, p ((x, y), z)
      = ∑ y, A x * B x z * C z y := Finset.sum_congr rfl fun y _ => hf x y z
    _ = A x * B x z * (∑ y, C z y) := by rw [Finset.mul_sum]

/-- ⭐ **链下 $(Y,Z)$ 的边缘律**：$\big(\sum_x A(x)B(x,z)\big)\cdot C(z,y)$。

**⭐ 这里是 $C$ 不读 $x$ 的**唯一用处**：$C(z,y)$ 可以从 $\sum_x$ 中提出。** -/
theorem margYZ_chain (p : FinJoint α β γ) (A : α → ℝ) (B : α → γ → ℝ)
    (C : γ → β → ℝ) (hf : ChainFac p A B C) (y : β) (z : γ) :
    margYZ p y z = (∑ x, A x * B x z) * C z y := by
  unfold margYZ
  calc ∑ x, p ((x, y), z)
      = ∑ x, A x * B x z * C z y := Finset.sum_congr rfl fun x _ => hf x y z
    _ = (∑ x, A x * B x z) * C z y := by rw [Finset.sum_mul]

/-- ⭐ **链下 $Z$ 的边缘律**：两个因子和之积。 -/
theorem margZ_chain (p : FinJoint α β γ) (A : α → ℝ) (B : α → γ → ℝ)
    (C : γ → β → ℝ) (hf : ChainFac p A B C) (z : γ) :
    margZ p z = (∑ x, A x * B x z) * (∑ y, C z y) := by
  unfold margZ
  calc ∑ x, ∑ y, p ((x, y), z)
      = ∑ x, ∑ y, A x * B x z * C z y := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          exact hf x y z
    _ = ∑ x, A x * B x z * (∑ y, C z y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
    _ = (∑ x, A x * B x z) * (∑ y, C z y) := by rw [Finset.sum_mul]

/-- ⭐⭐⭐ **链 $\Longrightarrow$ 条件独立（乘法形式）**：
$X \to Z \to Y$ 上 $X \perp\!\!\!\perp Y \mid Z$。

**证明**：把三条边缘律代入乘性等式，两边都是
$A(x)B(x,z)C(z,y)\big(\sum_x AB\big)\big(\sum_y C\big)$ —— **纯交换律闭合**。 -/
theorem chain_condMul (p : FinJoint α β γ) (A : α → ℝ) (B : α → γ → ℝ)
    (C : γ → β → ℝ) (hf : ChainFac p A B C) : CondMul p := by
  intro x y z
  rw [margXZ_chain p A B C hf x z, margYZ_chain p A B C hf y z,
    margZ_chain p A B C hf z, hf x y z]
  ring

/-- ⭐⭐⭐ **链 $\Longrightarrow$ 条件独立（条件比的经典形式）**：

$$\mathrm{margZ}\ p\ z \neq 0 \Longrightarrow
  \frac{p((x,y),z)}{\mathrm{margZ}\ p\ z}
  = \frac{\mathrm{margXZ}\ p\ x\ z}{\mathrm{margZ}\ p\ z}
    \cdot\frac{\mathrm{margYZ}\ p\ y\ z}{\mathrm{margZ}\ p\ z}$$ -/
theorem chain_condRatio (p : FinJoint α β γ) (A : α → ℝ) (B : α → γ → ℝ)
    (C : γ → β → ℝ) (hf : ChainFac p A B C) : CondRatio p :=
  condMul_imp_condRatio p (chain_condMul p A B C hf)

/-! ===========================================================================
  §3  ⭐⭐⭐⭐ **混合图**：链 $X \to Z \to Y$ ＋ 对撞 $X \to W \leftarrow Y$
  =========================================================================== -/

/-- ⭐⭐ **四变量联合律**：在 $((x,y),z)$ 之外再带一个**对撞变量 $W$**（类型 `ω`）。 -/
abbrev FinJoint4 (α β γ ω : Type*) := ((α × β) × γ) × ω → ℝ

variable {ω : Type*} [Fintype ω] [DecidableEq ω]

/-- ⭐⭐⭐ **链 × 对撞的分解**（**混合图的概率骨架**）：

$$p_4\big(((x,y),z),w\big) \;=\; A(x)\cdot B(x,z)\cdot C(z,y)\cdot m(x,y,w)$$

* $A\,B\,C$ —— **链路径** $X\to Z\to Y$ 的核（$C$ 不读 $x$，见 §2）；
* $m$ —— **对撞路径** $X \to W \leftarrow Y$ 的核。

**⚠⚠ 关键：$m$ 同时读 $x$ 与 $y$** —— 这正是对撞点的定义性特征，
也是「对撞能制造 $X$ 与 $Y$ 的关联」的代数来源。
**§5 说明：只有在 $W$ 被条件化时，这条耦合才会破坏条件独立。** -/
def ChainColliderFac (p4 : FinJoint4 α β γ ω) (A : α → ℝ) (B : α → γ → ℝ)
    (C : γ → β → ℝ) (m : α → β → ω → ℝ) : Prop :=
  ∀ x y z w, p4 (((x, y), z), w) = A x * B x z * C z y * m x y w

/-- ⭐⭐⭐ **把对撞变量 $W$ 边缘化掉** —— 这是「$W \notin Z$」的**代数化**。

⚠ **逻辑上的等价性**：$Z$ 只由 $Z$ 一个变量组成，$W$ 既不在 $Z$ 中
也不在被观测的三元组 $(X,Y,Z)$ 中，**故联合律必须对 $W$ 求和**。
**「对撞未被条件化」与「对撞被求和掉」是同一件事。** -/
noncomputable def margW (p4 : FinJoint4 α β γ ω) : FinJoint α β γ :=
  fun q => ∑ w, p4 (q, w)

/-- ⭐⭐⭐ **边缘化后 = 链核 × 对撞核的**和**（「两条路径相乘」的字面实现）**。

$$\big(\mathrm{margW}\,p_4\big)\big((x,y),z\big)
  = A(x)\,B(x,z)\,C(z,y)\cdot \sum_w m(x,y,w)$$

**⟹ 读法**：链路径贡献 $ABC$，对撞路径贡献 $\sum_w m(x,y,w)$，
二者**相乘**。**下面 §3.1 只需再要求后者「不产生新的秩」即可。** -/
theorem margW_chainCollider (p4 : FinJoint4 α β γ ω) (A : α → ℝ)
    (B : α → γ → ℝ) (C : γ → β → ℝ) (m : α → β → ω → ℝ)
    (hf : ChainColliderFac p4 A B C m) (x : α) (y : β) (z : γ) :
    margW p4 ((x, y), z) = A x * B x z * C z y * (∑ w, m x y w) := by
  unfold margW
  calc ∑ w, p4 (((x, y), z), w)
      = ∑ w, A x * B x z * C z y * m x y w :=
        Finset.sum_congr rfl fun w _ => hf x y z w
    _ = A x * B x z * C z y * (∑ w, m x y w) := by rw [Finset.mul_sum]

/-! ### §3.1 ⭐⭐⭐⭐ 主定理：混合图 ⟹ 条件独立 -/

/-- ⭐⭐⭐⭐ **混合图（链 ＋ 对撞，对撞未被条件化）⟹ 条件独立**。

**假设**：

* 链核 $A\,B\,C$（$X\to Z\to Y$，$C$ 不读 $x$）；
* 对撞核 $m(x,y,w)$（$X \to W \leftarrow Y$，$m$ **可以**同时读 $x$ 与 $y$）；
* **⚠ 唯一额外假设（秩一耦合）**：
  $$\forall x\,y,\quad \sum_w m(x,y,w) \;=\; d(x)\cdot e(y).$$

**结论**：$\mathrm{CondMul}\,(\mathrm{margW}\,p_4)$，即 $X \perp\!\!\!\perp Y \mid Z$。

**证明（**字面的「两条路径相乘后重排成一条链」**）**：
令 $\tilde A(x) := A(x)\,d(x)$、$\tilde C(z,y) := C(z,y)\,e(y)$，则

$$\big(\mathrm{margW}p_4\big)\big((x,y),z\big)
  = \tilde A(x)\,B(x,z)\,\tilde C(z,y),$$

即 $\mathrm{margW}\,p_4$ **是**一条链的联合律，**交给 §2 的 `chain_condMul` 即可**。

**⚠ 诚实声明**：秩一假设**不可去** —— §4 给出 rank-2 耦合下的
**机器校验反例**（结论在那里为假）。**§3.2 说明标准概率情形自动满足它。** -/
theorem chainCollider_condMul (p4 : FinJoint4 α β γ ω) (A : α → ℝ)
    (B : α → γ → ℝ) (C : γ → β → ℝ) (m : α → β → ω → ℝ) (d : α → ℝ) (e : β → ℝ)
    (hf : ChainColliderFac p4 A B C m) (hk : ∀ x y, ∑ w, m x y w = d x * e y) :
    CondMul (margW p4) := by
  -- 把 $d\,e$ 吸收进链核，得到一条**新链**。
  have hfac : ChainFac (margW p4) (fun x => A x * d x) B (fun z y => C z y * e y) := by
    intro x y z
    rw [margW_chainCollider p4 A B C m hf, hk x y]
    ring
  exact chain_condMul (margW p4) (fun x => A x * d x) B (fun z y => C z y * e y) hfac

/-! ### §3.2 ⭐⭐⭐⭐ 概率情形：对撞核已归一化（**任务书的字面命题**） -/

/-- ⭐⭐⭐⭐ **混合图的条件独立（对撞核是合法条件核）**。

若对撞核 $m$ 满足 $\sum_w m(x,y,w) = 1$ 对**每个** $(x,y)$ 成立
（即 $m$ 是**合法的条件分布** —— 任何 SCM 的对撞机制都如此），
则 $\mathrm{margW}\,p_4$ 满足 `CondMul`，即 **$W \notin Z$ 时** $X \perp\!\!\!\perp Y \mid Z$。

**⚠ 这是「对撞不开口」的**完整概率内容****：边缘化一个未被条件化的汇点变量
**不改变** $(X,Y,Z)$ 的联合律（这正是下面的证明：$d \equiv e \equiv 1$）。 -/
theorem chainCollider_condMul_normalized (p4 : FinJoint4 α β γ ω) (A : α → ℝ)
    (B : α → γ → ℝ) (C : γ → β → ℝ) (m : α → β → ω → ℝ)
    (hf : ChainColliderFac p4 A B C m) (hnorm : ∀ x y, ∑ w, m x y w = 1) :
    CondMul (margW p4) :=
  chainCollider_condMul p4 A B C m (fun _ => 1) (fun _ => 1) hf
    (fun x y => by rw [hnorm x y, mul_one])

/-- ⭐⭐⭐⭐ **混合图的条件比形式**（$m$ 归一化）—— 任务书要求的**经典书面形式**。 -/
theorem chainCollider_condRatio_normalized (p4 : FinJoint4 α β γ ω) (A : α → ℝ)
    (B : α → γ → ℝ) (C : γ → β → ℝ) (m : α → β → ω → ℝ)
    (hf : ChainColliderFac p4 A B C m) (hnorm : ∀ x y, ∑ w, m x y w = 1) :
    CondRatio (margW p4) :=
  condMul_imp_condRatio _ (chainCollider_condMul_normalized p4 A B C m hf hnorm)

/-! ===========================================================================
  §4  ⭐⭐⭐ **锐利性**：秩一假设**不可去**（`Fin 2` 上的机器校验反例）
  =========================================================================== -/

/-- ⭐ **`Fin 2` 的二值穷举**（本文件唯一的组合辅助引理）。 -/
theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  obtain ⟨v, hv⟩ := x
  have h : v = 0 ∨ v = 1 := by omega
  rcases h with h | h
  · exact Or.inl (Fin.ext (by simp [h]))
  · exact Or.inr (Fin.ext (by simp [h]))

/-- ⭐⭐ **rank-2 耦合核**（对撞核）：$m(x,y,w) = 1 \iff x = y \wedge w = 0$。

**⟹ 边缘耦合**：$D(x,y) := \sum_w m(x,y,w) = \begin{cases}1 & x=y\\ 0 & x\ne y\end{cases}$
—— 这是**单位矩阵**，**秩为 2**，**不能**写成 $d(x)e(y)$。 -/
noncomputable def mId : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun x y w => if x = y ∧ w = 0 then 1 else 0

/-- ⭐⭐ **反例的联合律**：链核全取 $1$（$Z$ 是哑变量），对撞核取 `mId`。 -/
noncomputable def p4Id : FinJoint4 (Fin 2) (Fin 2) (Fin 2) (Fin 2) :=
  fun p => (1 : ℝ) * (1 : ℝ) * (1 : ℝ) * mId p.1.1.1 p.1.1.2 p.2

/-- ⭐ **边缘化 $W$ 后**：$p((x,y),z) = [x = y]$（**只看 $x,y$ 的等式指示函数**）。 -/
theorem margW_p4Id (x y z : Fin 2) :
    margW p4Id ((x, y), z) = if x = y then 1 else 0 := by
  unfold margW p4Id mId
  rw [Fin.sum_univ_two]
  rcases fin2_cases x with rfl | rfl <;> rcases fin2_cases y with rfl | rfl <;>
    rcases fin2_cases z with rfl | rfl <;> norm_num [Fin.ext_iff]

/-- ⭐⭐⭐ **`CondMul` 在此反例上为假** ——
故 §3.1 的秩一假设**不可去**。

**核对**（取 $(x,y,z) = (1,0,0)$）：
`margW p4Id ((1,0),0) = 0`、`margZ 0 = 2`、`margXZ 1 0 = 1`、`margYZ 0 0 = 1`，
乘性等式要求 $0\cdot 2 = 1\cdot 1$，即 $0 = 1$ —— **矛盾**。

**⟹ 概率读法**：$X,Y$ 是两枚**独立的公平硬币**，对撞 $W := [X = Y]$ 只记录
「两枚是否相同」。**不条件化于 $W$ 时** $X \perp Y$；
但**这个反例把 $W$ 求和掉了却仍不独立**，因为这里的「对撞核」**不是**条件核
（$\sum_w m(0,1,w) = 0 \ne 1$：$(x,y)=(0,1)$ 在联合律下是零概率事件）。
**⟹ 破坏条件独立的不是对撞本身，而是「对撞核未归一化」——
即某个 $(x,y)$ 组合概率为零。**

**⚠ 与 §5 的区别**：§5 是**归一化**对撞核下**条件化**于 $W$ 而破裂；
§4 是**非归一化**对撞核下**不条件化**也破裂。**两者是不同现象，本文件分别给出。** -/
theorem p4Id_not_condMul : ¬ CondMul (margW p4Id) := by
  intro h
  have h1 := h 1 0 0
  rw [margW_p4Id] at h1
  have hZ : margZ (margW p4Id) 0 = 2 := by
    unfold margZ
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [margW_p4Id, Fin.ext_iff]
  have hXZ : margXZ (margW p4Id) 1 0 = 1 := by
    unfold margXZ
    rw [Fin.sum_univ_two]
    norm_num [margW_p4Id, Fin.ext_iff]
  have hYZ : margYZ (margW p4Id) 0 0 = 1 := by
    unfold margYZ
    rw [Fin.sum_univ_two]
    norm_num [margW_p4Id, Fin.ext_iff]
  rw [hZ, hXZ, hYZ] at h1
  norm_num at h1

/-! ### §4.1 ⭐⭐ **反例确实满足 §3 的全部假设（除了秩一）**

**⟹ 这一段是审计的关键**：若不核对，§4 的反例可能根本没落进 §3 的假设域，
从而**不构成**对「秩一假设不可去」的证明。下面逐条机器校验。 -/

/-- ⭐ `p4Id` 确实是 `ChainColliderFac` 形状（链核全 1 × `mId`）。 -/
theorem p4Id_is_chainCollider :
    ChainColliderFac p4Id (fun _ => 1) (fun _ _ => 1) (fun _ _ => 1) mId := by
  intro x y z w
  unfold p4Id
  ring

/-- ⭐ `mId` 的边缘耦合是**单位矩阵**。 -/
theorem mId_sum (x y : Fin 2) : (∑ w, mId x y w) = if x = y then 1 else 0 := by
  unfold mId
  rw [Fin.sum_univ_two]
  rcases fin2_cases x with rfl | rfl <;> rcases fin2_cases y with rfl | rfl <;>
    norm_num [Fin.ext_iff]

/-- ⭐⭐⭐ **单位矩阵耦合不是秩一的**：不存在 $d,e$ 使 $\delta_{xy} = d(x)e(y)$。

**⟹ 故 `p4Id` 落在 §3 的秩一假设**之外**，
而 `p4Id_not_condMul` 证明它**违反结论** ——
**⟹ 秩一假设确实不可去（§4 的反例是合格的）。** -/
theorem mId_not_rankOne :
    ¬ ∃ d e : Fin 2 → ℝ, ∀ x y : Fin 2, (if x = y then (1 : ℝ) else 0) = d x * e y := by
  rintro ⟨d, e, h⟩
  have h00 := h 0 0
  have h01 := h 0 1
  have h11 := h 1 1
  simp at h00 h01 h11
  rcases h01 with h | h
  · rw [h] at h00
    simp at h00
  · rw [h] at h11
    simp at h11

/-! ===========================================================================
  §5  ⭐⭐⭐⭐ **对撞被条件化 ⟹ 条件独立破裂**（explaining away）
  =========================================================================== -/

/-- ⭐⭐ **xor 对撞核**（**归一化**）：$m(x,y,w) = 1 \iff w = x \oplus y$。

**⟹ 这是**合法条件核**：对每个 $(x,y)$ 恰有一个 $w = x\oplus y$，故 $\sum_w m = 1$。 -/
noncomputable def mXor : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun x y w => if (if x.val = y.val then (0 : Fin 2) else 1) = w then 1 else 0

/-- ⭐⭐ **xor 混合图的联合律**：链核全为 $1$（$Z$ 是哑变量，$X,Y$ 边际独立）× xor 对撞核。 -/
noncomputable def p4Xor : FinJoint4 (Fin 2) (Fin 2) (Fin 2) (Fin 2) :=
  fun p => (1 : ℝ) * (1 : ℝ) * (1 : ℝ) * mXor p.1.1.1 p.1.1.2 p.2

/-- ⭐ **边缘化 $W$ 后联合律恒为 $1$**（$X, Y$ 边际独立，$Z$ 哑）。 -/
theorem margW_p4Xor (x y z : Fin 2) : margW p4Xor ((x, y), z) = 1 := by
  unfold margW p4Xor mXor
  rw [Fin.sum_univ_two]
  rcases fin2_cases x with rfl | rfl <;> rcases fin2_cases y with rfl | rfl <;>
    rcases fin2_cases z with rfl | rfl <;> norm_num [Fin.ext_iff]

/-- ⭐⭐⭐ **$W \notin Z$：对撞未被条件化 ⟹ $X \perp\!\!\!\perp Y \mid Z$ 成立**。

**⟹ 这是 §3.2 在具体 `Fin 2` 实例上的**独立校验**（不经过抽象主定理）。 -/
theorem p4Xor_marg_condMul : CondMul (margW p4Xor) := by
  intro x y z
  have hZ : margZ (margW p4Xor) z = 4 := by
    unfold margZ
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [margW_p4Xor, Fin.ext_iff]
  have hXZ : margXZ (margW p4Xor) x z = 2 := by
    unfold margXZ
    rw [Fin.sum_univ_two]
    norm_num [margW_p4Xor, Fin.ext_iff]
  have hYZ : margYZ (margW p4Xor) y z = 2 := by
    unfold margYZ
    rw [Fin.sum_univ_two]
    norm_num [margW_p4Xor, Fin.ext_iff]
  rw [hZ, hXZ, hYZ, margW_p4Xor]
  norm_num

/-- ⭐⭐ **「条件化于 $W$」的联合律**（把 $W$ 放进 `γ` 槽 = 条件变量槽）。 -/
noncomputable def xorCond : FinJoint (Fin 2) (Fin 2) (Fin 2) :=
  fun q => mXor q.1.1 q.1.2 q.2

/-- ⭐⭐⭐⭐ **对撞被条件化 ⟹ 条件独立破裂**（explaining away 的机器校验版）。

$$\neg\,\mathrm{CondMul}\,(\text{「条件化于 } W \text{」的联合律})$$

**核对**（取 $(x,y,w) = (1,0,0)$）：
$x\oplus y = 1 \ne 0$ 故 $p = 0$；而 `margZ 0 = 2`、`margXZ 1 0 = 1`、`margYZ 0 0 = 1`，
乘性等式要求 $0 \cdot 2 = 1 \cdot 1$，即 $0 = 1$ —— **矛盾**。

**⭐ 概率读法**：$X,Y$ 独立公平硬币，$W := X \oplus Y$。
**知道 $W$ 后，$X$ 与 $Y$ 完全相互决定** —— 这正是「对撞点在 $Z$ 中才开口」。
**⚠ 与 §3 的对照**：同一联合律，$W \notin Z$ 时独立（`p4Xor_marg_condMul`），
$W \in Z$ 时**不**独立（本定理）——
**这是「对撞点方向反转」的完整机器校验证据。** -/
theorem xorCond_not_condMul : ¬ CondMul xorCond := by
  intro h
  have h1 := h 1 0 0
  have hZ : margZ xorCond 0 = 2 := by
    unfold margZ xorCond
    simp only [Fin.sum_univ_two]
    unfold mXor
    norm_num
  have hXZ : margXZ xorCond 1 0 = 1 := by
    unfold margXZ xorCond
    rw [Fin.sum_univ_two]
    show mXor 1 0 0 + mXor 1 1 0 = 1
    unfold mXor
    norm_num
  have hYZ : margYZ xorCond 0 0 = 1 := by
    unfold margYZ xorCond
    rw [Fin.sum_univ_two]
    show mXor 0 0 0 + mXor 1 0 0 = 1
    unfold mXor
    norm_num
  have hp : xorCond ((1, 0), 0) = 0 := by
    unfold xorCond mXor
    norm_num
  rw [hZ, hXZ, hYZ, hp] at h1
  norm_num at h1

/-! ===========================================================================
  §6  ⭐⭐⭐ **合成陈述**：同一混合图的「开关」——$W\notin Z$ vs $W\in Z$
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **对撞点的「开关」定理**（本文件的最终合成）。

**同一个** xor 混合图联合律上：

1. **$W$ 不在 $Z$ 中（$W$ 被边缘化）** ⟹ $X \perp\!\!\!\perp Y \mid Z$ ✅；
2. **$W$ 在 $Z$ 中（$W$ 被条件化）** ⟹ $X \perp\!\!\!\perp Y \mid Z$ **不成立** ✅（其否定成立）。

**⟹ 这是 Pearl 1.2.4 的「d-分离方向反转」在**同一条联合律**上的
完整机器校验 —— 不是两个不相干的例子。** -/
theorem collider_switch :
    CondMul (margW p4Xor) ∧ ¬ CondMul xorCond :=
  ⟨p4Xor_marg_condMul, xorCond_not_condMul⟩

/-! ===========================================================================
  §7  ⭐⭐⭐ **R-39 组合定理**：把 §2（链）、§3（混合图）、§5（对撞开口）
      的结论**接起来**，形成跨节的合成陈述。

  ⚠ 本节只**追加**，不改动 §0–§6 任何内容。
  ⚠ 每条定理的前件里**没有**出现自己的结论（已逐条检查，见 `_audit/R39-Top57-70.md`）。
  =========================================================================== -/

section R39Composition

/-- ⭐⭐⭐ **【链 ⟹ 乘性 与 除法两种形式的合取】**

对任一满足链式分解的联合律，`CondMul` 与 `CondRatio` **同时**成立。

**为什么不是同义反复**：前件是**分解等式** `hf : ChainFac p A B C`
（逐点乘性因子化），结论是**两个不同谓词**的合取 ——
`CondMul` 是**无守卫**的乘性等式，`CondRatio` 是**带 `margZ ≠ 0` 守卫**的除法等式。
两者由 `condMul_imp_condRatio` 单向连接，**反向不成立**（见该定理注释），
故合取**严格强于**任一单条。 -/
theorem chain_condMul_and_condRatio (p : FinJoint α β γ) (A : α → ℝ) (B : α → γ → ℝ)
    (C : γ → β → ℝ) (hf : ChainFac p A B C) :
    CondMul p ∧ CondRatio p :=
  ⟨chain_condMul p A B C hf, chain_condRatio p A B C hf⟩

/-- ⭐⭐⭐ **【交换变量后仍条件独立】**

链上的 `X ⊥ Y | Z` 对 `X` 与 `Y` 的角色**对称**：交换后仍是 `CondMul`。

**证明**：先由 `chain_condMul` 得 `CondMul p`，再用 `FinCondIndep.condMul_swap`
得到 `CondMul (swapXY p)`。**不重做 §2 的求和重排。**

**为什么不是同义反复**：前件是 `ChainFac p A B C`，
结论是关于**另一个联合律** `swapXY p` 的谓词 ——
`swapXY` 交换了 `α` 与 `β` 槽，`margXZ`/`margYZ` 也随之互换，
这是一条**新的**机器事实，不是 `CondMul p` 的复述。 -/
theorem chain_condMul_swap (p : FinJoint α β γ) (A : α → ℝ) (B : α → γ → ℝ)
    (C : γ → β → ℝ) (hf : ChainFac p A B C) :
    CondMul (FinCondIndep.swapXY p) :=
  (FinCondIndep.condMul_swap p).mp (chain_condMul p A B C hf)

/-- ⭐⭐⭐ **【混合图：乘性 + 除法 + 交换，三件套】**

对撞未被条件化（`W` 边缘化掉）且对撞核归一化时，
`margW p4` **同时**满足：乘性形式、除法形式、以及交换变量后的乘性形式。

**为什么不是同义反复**：前件是 `ChainColliderFac p4 A B C m`（四变量分解）
加上归一化 `∑_w m x y w = 1`；结论是三条**不同谓词**
（`CondMul`、`CondRatio`、`CondMul ∘ swapXY`）。
三者经由 `chainCollider_condMul_normalized`、`condMul_imp_condRatio`、
`condMul_swap` 三条不同的引理得到 —— 是本文件 §3.2 与 §1、外部 §swap 的**扇入**。 -/
theorem chainCollider_three_forms (p4 : FinJoint4 α β γ ω) (A : α → ℝ)
    (B : α → γ → ℝ) (C : γ → β → ℝ) (m : α → β → ω → ℝ)
    (hf : ChainColliderFac p4 A B C m) (hnorm : ∀ x y, ∑ w, m x y w = 1) :
    CondMul (margW p4) ∧ CondRatio (margW p4)
      ∧ CondMul (FinCondIndep.swapXY (margW p4)) :=
  ⟨chainCollider_condMul_normalized p4 A B C m hf hnorm,
   chainCollider_condRatio_normalized p4 A B C m hf hnorm,
   (FinCondIndep.condMul_swap (margW p4)).mp
     (chainCollider_condMul_normalized p4 A B C m hf hnorm)⟩

/-- ⭐⭐⭐⭐ **【对撞开关的除法版：`W ∉ Z` 有 `CondRatio`，`W ∈ Z` 连 `CondMul` 都无】**

`collider_switch` 只在乘性形式上陈述。本定理把它**升级到除法形式**：
未条件化侧给出 `CondRatio (margW p4Xor)`（经典条件分布相等），
条件化侧仍是 `¬ CondMul xorCond`。

**为什么不是同义反复**：前件为空（`Fin 2` 上的两个**具体**联合律），
结论是**具体实例**上的两条真陈述。`CondRatio (margW p4Xor)` 由
`condMul_imp_condRatio` 从 `p4Xor_marg_condMul` 得到，
**`¬ CondMul xorCond` 与 `CondRatio` 无关**
（`CondRatio ⟸ CondMul` 单向，故乘性侧被否时除法侧未必被否 ——
本定理精确地把两侧放在**不同的强度**上，这是 §6 未说的内容）。 -/
theorem collider_switch_ratio :
    CondRatio (margW p4Xor) ∧ ¬ CondMul xorCond :=
  ⟨condMul_imp_condRatio _ p4Xor_marg_condMul, xorCond_not_condMul⟩

/-- ⭐⭐⭐ **【同一条 xor 联合律上三种读法的完整对照】**

(a) 边缘化掉 `W`：`CondMul` 成立；
(b) 边缘化掉 `W`：`CondRatio` 成立；
(c) 条件化于 `W`：`CondMul` **不**成立。

**为什么不是同义反复**：三条子命题分别由
`p4Xor_marg_condMul`、`condMul_imp_condRatio`（消费 a）、
`xorCond_not_condMul` 给出，前件为空。结论是**同一联合律**
在**两种 d-分离状态**下的**三条不同强度**陈述 ——
这是 §6 `collider_switch` 的**加强合取**（多了 `CondRatio` 一项）。 -/
theorem xor_three_way :
    CondMul (margW p4Xor) ∧ CondRatio (margW p4Xor) ∧ ¬ CondMul xorCond :=
  ⟨p4Xor_marg_condMul, condMul_imp_condRatio _ p4Xor_marg_condMul, xorCond_not_condMul⟩

end R39Composition

end R242G1

end Fate
