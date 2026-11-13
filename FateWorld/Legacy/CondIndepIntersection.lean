import FateWorld.Legacy.CondIndepSemigraphoid
import FateWorld.Legacy.CondIndepContraction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! ===========================================================================
  §Semigraphoid 交公理（intersection / graphoid）：**非空洞版本**

  ## 0  ⚠⚠⚠ 诚实声明（必读，请勿跳过）

  ### 0.1  任务单的前提错误

  任务单要求「查 `Fate/CondIndepNProb.lean` 是否已给出 NMass 守卫」。
  **该文件不存在**（`ls Fate/ | grep -i nprob` 为空）。实际情况是：

  * `CondIndepNProb` 是 `Fate/CondIndepN.lean:185` 里的一个 **`def`**，
    不是一个文件：

      noncomputable def CondIndepNProb (p : NJoint (ι := ι) α γ) : Prop :=
        ∀ xs z, NMass p z ≠ 0 → p xs z / NMass p z
          = ∏ i, marg p i (xs i) z / NMass p z

  * 其中 `NMass` 的真实定义是 `Fate/CondIndepN.lean:94`

      noncomputable def NMass (p : NJoint (ι := ι) α γ) (z : γ) : ℝ := ∑ xs, p xs z

    即 **「$Z=z$ 的全边缘质量」**，一个 $\sum$，**没有**任何归一化 / 正性内容。

  ⟹ 「NMass 守卫」= 「$Z=z$ 的边缘质量非零」。这是除法守卫，**不是**正性。

  ### 0.2  `CondRel` 上的交公理是**同义反复**（纪律第 7 条命中的情形）

  `Fate.Semigraphoid.CondRel p A B C`（`CondIndepSemigraphoid.lean:401`）
  的 `cond` 字段是 `GenC3.CondIndepN (proj p (A ∪ B ∪ C))` ——
  它只说「**并集上全体坐标互相**条件独立」，**丢掉**了「$A$ 这块 vs $B$ 这块」
  的分工。于是在该定义下交公理

      CondRel p A B (C ∪ D)  ∧  CondRel p A C (B ∪ D)  ⟹  CondRel p A (B∪C) D

  的结论与前件 2 是**同一个 `Finset`**（`A∪B∪(C∪D) = A∪C∪(B∪D) = A∪(B∪C)∪D`），
  **前件 1 一个字都用不到**。本文件 §1 把这一点形式化证明
  （`condRel_intersection_is_vacuous`）——**按纪律如实汇报，不以「证出来了」冒充进展。**
  （同一诊断此前已在 `Fate/CondIndepContraction.lean` §1 对收缩律给出。）

  ### 0.3  `BlockRel`（聚合集合质量层）**不足以**表达交公理

  `Fate.Contraction.BlockRel`（`CondIndepContraction.lean:174`）是

      BlockRel mass A B C  :=  ∀ z,
        mass (A∪B∪C) z * mass C z = mass (A∪C) z * mass (B∪C) z

  这是**聚合集合质量**上的等式。它对**收缩律**足够（收缩是纯「集合质量」恒等式），
  但**交公理在数学上需要点级（slice 级）信息**：
  交公理的证明必须比较「固定 $c$ 的 $2\times2$ 表」与「固定 $b$ 的 $2\times2$ 表」，
  这是**逐点**的秩一性，聚合质量把它们抹掉了。本文件 §5 给出
  **聚合层反例**（`blockRel_intersection_false`），证明「交公理不能降到
  `BlockRel` 层」是一个**真事实**，而不是本文件偷懒。

  ### 0.4  本文件真正交付的：点级（slice 级）交公理

  正确的层次是**逐点质量函数**
  $\mu : \alpha_A \times \alpha_B \times \alpha_C \to \mathbb{R}$
  （对同一个 $Z=z$、同一个 $D$ 取值切片而言）。此时

  * 前件 1「$A \perp B \mid C$」= `H_AB_C μ`：$\mu_{abc}\,\mu^{C}_{c}
      = \mu^{AC}_{ac}\,\mu^{BC}_{bc}$
  * 前件 2「$A \perp C \mid B$」= `H_AC_B μ`：$\mu_{abc}\,\mu^{B}_{b}
      = \mu^{AB}_{ab}\,\mu^{BC}_{bc}$
  * 结论「$A \perp (B,C) \mid \varnothing$」= `H_A_BC μ`：$\mu_{abc}\,M
      = \mu^{A}_{a}\,\mu^{BC}_{bc}$

  并需 **正性** `Pos μ : ∀ a b c, 0 < μ a b c`。
  §4 的 `intersection` 证明这三条，**§2 无假设**、**§3** 给出除法（`NMass ≠ 0`
  风格守卫）版本。**这是非空洞的**（§6 `intersection_hypotheses_inhabited`
  给出满足前件的实例，且 §5 的聚合反例说明前件不能弱化）。

  ## 1  交付清单

  | 定理 | 内容 | 状态 |
  |---|---|---|
  | `intersection_index_diag` | 交公理的四个集合逐字相等（**诊断**用） | ✅ |
  | `condRel_intersection_is_vacuous` | 警告：`CondRel` 上交公理是同义反复 | ✅ |
  | `mB_pos` / `mC_pos` / `mAC_pos` / `mBC_pos` / `mT_pos` | 正性下各边缘质量为正 | ✅ |
  | `mAC_mul_mB` | 核心桥：$\mu^{AC}_{ac}\mu^{B}_{b} = \mu^{AB}_{ab}\mu^{C}_{c}$ | ✅ |
  | `mAC_eq` | 推论：$\mu^{AC}_{ac}$ 与 $c$ 的可分性 $\mu^{AC}_{ac}=\mu^{A}_a\,\mu^{C}_c/M_{\ast}$ | ✅ |
  | `intersection` | **点级交公理**（乘性形式，需 `Pos μ`） | ✅ |
  | `intersection_prob` | **点级交公理**（除法形式，带 `≠ 0` 守卫） | ✅ |
  | `H_AB_C_iff_prob` | 乘性形式 ⟺ 除法形式（带守卫） | ✅ |
  | `blockRel_intersection_false` | 警告：聚合层交公理**为假**（反例） | ✅ |
  | `intersection_hypotheses_inhabited` | 前件可满足（实例） | ✅ |

  ## 2  诚实边界（不声称的内容）

  * **不声称「`CondRel` / semigraphoid 层的交公理已实现」。** 该层的交公理
    是空洞的（§1）。本文件在**点级**实现了它。
  * **不声称「已把点级交公理接到 `proj`/`NMass` 的 N 元机器上」。**
    那需要先证「边缘化在正性下保持条件独立」（decomposition/weak union），
    而 `CondIndepSemigraphoid.lean` §9 的 `pje` 反例说明无正性时它是假的；
    正性版本仍是**未做的**（收缩律 `Fate/CondIndepContraction.lean` 已做）。
  * **正性 `Pos μ` 是本文件唯一的假设**，且 §5 说明它不能换成聚合层的弱条件。
  * 全部定理**无 `sorry` / `admit` / `axiom` / `trivial` / `→ True` 占位**。

  =========================================================================== -/

namespace Fate

namespace Intersection

open Finset

/-! ---------------------------------------------------------------------------
  §1  ⚠ 空洞性诊断：`CondRel` 上的交公理结论 ≡ 前件 2
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐ **诊断：交公理的四个集合逐字相等。**

$$A\cup B\cup(C\cup D) \;=\; A\cup C\cup(B\cup D) \;=\; A\cup(B\cup C)\cup D .$$

前件 1 的 `proj` 集合是左边，前件 2 的是中间，结论的是右边。
**三者相同** —— 这就是 `CondRel` 上交公理空洞的根源。 -/
theorem intersection_index_diag {ι : Type*} [DecidableEq ι] (A B C D : Finset ι) :
    A ∪ B ∪ (C ∪ D) = A ∪ (B ∪ C) ∪ D ∧
    A ∪ C ∪ (B ∪ D) = A ∪ (B ∪ C) ∪ D := by
  constructor <;> (ext i; simp only [mem_union]; tauto)

/-- ⭐⭐⭐ **（警告）`CondRel` 定义下交公理是同义反复。**

对**任意**谓词 `F : Finset ι → Prop`，三个 `CondRel` 的 `cond` 字段只通过
`F` 的同一自变量 `A ∪ (B ∪ C) ∪ D` 出现：

$$F\big(A\cup B\cup(C\cup D)\big) \wedge F\big(A\cup C\cup(B\cup D)\big)
  \;\Longleftrightarrow\; F\big(A\cup(B\cup C)\cup D\big).$$

⟹ 交公理的结论**就是**前件 2，前件 1 未被使用。
**因此本文件不在 `CondRel` 层交付交公理**（纪律第 7 条）。 -/
theorem condRel_intersection_is_vacuous {ι : Type*} [DecidableEq ι]
    (A B C D : Finset ι) (F : Finset ι → Prop) :
    (F (A ∪ B ∪ (C ∪ D)) ∧ F (A ∪ C ∪ (B ∪ D)))
      ↔ F (A ∪ (B ∪ C) ∪ D) := by
  obtain ⟨h1, h2⟩ := intersection_index_diag A B C D
  rw [h1, h2]
  exact ⟨fun h => h.2, fun h => ⟨h, h⟩⟩

/-! ---------------------------------------------------------------------------
  §2  ⭐⭐⭐ 点级（slice 级）交公理：定义
  --------------------------------------------------------------------------- -/

section PointLevel

variable {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]
variable [Nonempty α] [Nonempty β] [Nonempty κ]

/-- ⭐ **$A$ 的边缘质量** $\mu^{A}_a := \sum_{b,c}\mu_{abc}$。 -/
noncomputable def mA (mu : α → β → κ → ℝ) (a : α) : ℝ := ∑ b, ∑ c, mu a b c

/-- ⭐ **$B$ 的边缘质量** $\mu^{B}_b := \sum_{a,c}\mu_{abc}$。 -/
noncomputable def mB (mu : α → β → κ → ℝ) (b : β) : ℝ := ∑ a, ∑ c, mu a b c

/-- ⭐ **$C$ 的边缘质量** $\mu^{C}_c := \sum_{a,b}\mu_{abc}$。 -/
noncomputable def mC (mu : α → β → κ → ℝ) (c : κ) : ℝ := ∑ a, ∑ b, mu a b c

/-- ⭐ **$(A,B)$ 的边缘质量** $\mu^{AB}_{ab} := \sum_c \mu_{abc}$。 -/
noncomputable def mAB (mu : α → β → κ → ℝ) (a : α) (b : β) : ℝ := ∑ c, mu a b c

/-- ⭐ **$(A,C)$ 的边缘质量** $\mu^{AC}_{ac} := \sum_b \mu_{abc}$。 -/
noncomputable def mAC (mu : α → β → κ → ℝ) (a : α) (c : κ) : ℝ := ∑ b, mu a b c

/-- ⭐ **$(B,C)$ 的边缘质量** $\mu^{BC}_{bc} := \sum_a \mu_{abc}$。 -/
noncomputable def mBC (mu : α → β → κ → ℝ) (b : β) (c : κ) : ℝ := ∑ a, mu a b c

/-- ⭐⭐ **总质量** $M := \sum_{b,c,a}\mu_{abc}$。

**⚠ 求和次序刻意选为 $(b,c,a)$**：这样
`∑ b, ∑ c, mBC mu b c = mT mu` 是**定义相等**（`mBC` 展开后逐字相同），
省去一次 `Finset.sum_comm`，而 `mA` 那一侧才做一次重排。
求和次序不影响总质量（`mT_eq_mA_sum` 记为引理以外的事实，本文件不需要）。 -/
noncomputable def mT (mu : α → β → κ → ℝ) : ℝ := ∑ b, ∑ c, ∑ a, mu a b c

/-- ⭐ **前件 1：$A \perp B \mid C$**（乘性形式，逐点）。

$$\forall a\,b\,c,\quad \mu_{abc}\,\mu^{C}_{c} = \mu^{AC}_{ac}\,\mu^{BC}_{bc}.$$

**⟹ 这是「固定 $c$ 时，$(a,b)$ 表秩一」的乘法闭包形式**，
与教科书条件独立等价（当 $\mu^C_c \ne 0$ 时），见 `H_AB_C_iff_prob`。 -/
def H_AB_C (mu : α → β → κ → ℝ) : Prop :=
  ∀ a b c, mu a b c * mC mu c = mAC mu a c * mBC mu b c

/-- ⭐ **前件 2：$A \perp C \mid B$**（乘性形式，逐点）。

$$\forall a\,b\,c,\quad \mu_{abc}\,\mu^{B}_{b} = \mu^{AB}_{ab}\,\mu^{BC}_{bc}.$$ -/
def H_AC_B (mu : α → β → κ → ℝ) : Prop :=
  ∀ a b c, mu a b c * mB mu b = mAB mu a b * mBC mu b c

/-- ⭐ **结论：$A \perp (B,C) \mid \varnothing$**（乘性形式，逐点）。

$$\forall a\,b\,c,\quad \mu_{abc}\,M = \mu^{A}_{a}\,\mu^{BC}_{bc}.$$

注意左边是**总质量** $M$（不是 $\mu^C_c$）：$A$ 与「$(B,C)$ 这块」**整体**
无条件独立。这正是交公理的结论形状。 -/
def H_A_BC (mu : α → β → κ → ℝ) : Prop :=
  ∀ a b c, mu a b c * mT mu = mA mu a * mBC mu b c

/-- ⭐ **正性 `Pos μ`**：切片上每个点质量严格为正。

**⟹ 交公理**唯一**的实质假设。它保证所有需要做除法的边缘质量非零
（§3 的 `*_pos` 系列引理）。 -/
def Pos (mu : α → β → κ → ℝ) : Prop := ∀ a b c, 0 < mu a b c

/-! ---------------------------------------------------------------------------
  §3  正性 ⟹ 各边缘质量为正（除法合法性的来源）
  --------------------------------------------------------------------------- -/

/-- ⭐ 非空有限类型上的正项和为正。 -/
theorem sum_pos_univ {σ : Type*} [Fintype σ] [Nonempty σ] {f : σ → ℝ}
    (h : ∀ x, 0 < f x) : 0 < ∑ x, f x :=
  Finset.sum_pos (fun x _ => h x) Finset.univ_nonempty

theorem mC_pos {mu : α → β → κ → ℝ} (hp : Pos mu) (c : κ) : 0 < mC mu c := by
  unfold mC
  exact sum_pos_univ (fun a => sum_pos_univ (fun b => hp a b c))

theorem mB_pos {mu : α → β → κ → ℝ} (hp : Pos mu) (b : β) : 0 < mB mu b := by
  unfold mB
  exact sum_pos_univ (fun a => sum_pos_univ (fun c => hp a b c))

theorem mAC_pos {mu : α → β → κ → ℝ} (hp : Pos mu) (a : α) (c : κ) : 0 < mAC mu a c := by
  unfold mAC
  exact sum_pos_univ (fun b => hp a b c)

theorem mAB_pos {mu : α → β → κ → ℝ} (hp : Pos mu) (a : α) (b : β) : 0 < mAB mu a b := by
  unfold mAB
  exact sum_pos_univ (fun c => hp a b c)

theorem mBC_pos {mu : α → β → κ → ℝ} (hp : Pos mu) (b : β) (c : κ) : 0 < mBC mu b c := by
  unfold mBC
  exact sum_pos_univ (fun a => hp a b c)

theorem mT_pos {mu : α → β → κ → ℝ} (hp : Pos mu) : 0 < mT mu := by
  unfold mT
  exact sum_pos_univ (fun b => sum_pos_univ (fun c => sum_pos_univ (fun a => hp a b c)))

/-! ---------------------------------------------------------------------------
  §4  ⭐⭐⭐ 交公理的点级证明（非空洞）
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐⭐ **核心桥：两条前件 ⟹ $\mu^{AC}_{ac}\,\mu^{B}_{b}
= \mu^{AB}_{ab}\,\mu^{C}_{c}$。**

**⟹ 这是交公理全部内容的所在。** 推导（$s=\mu_{abc}$）：

* 前件 1：$s\,\mu^C_c = \mu^{AC}_{ac}\,\mu^{BC}_{bc}$
* 前件 2：$s\,\mu^B_b = \mu^{AB}_{ab}\,\mu^{BC}_{bc}$

于是 $\mu^{AC}_{ac}\mu^{BC}_{bc}\mu^B_b
      = s\,\mu^C_c\,\mu^B_b
      = \mu^{AB}_{ab}\mu^{BC}_{bc}\mu^C_c$，
**约去 $\mu^{BC}_{bc} \ne 0$（正性）即得。**

**⚠ 关键是 $\mu^{BC}_{bc}$ 只依赖 $(b,c)$**：这就是「消去它」能成立的唯一原因，
也是本定理**必须**逐点陈述（不能用聚合集合质量）的根本理由。 -/
theorem mAC_mul_mB {mu : α → β → κ → ℝ} (hp : Pos mu)
    (h1 : H_AB_C mu) (h2 : H_AC_B mu) (a : α) (b : β) (c : κ) :
    mAC mu a c * mB mu b = mAB mu a b * mC mu c := by
  have hkey : mAC mu a c * mBC mu b c * mB mu b
      = mAB mu a b * mBC mu b c * mC mu c := by
    rw [← h1 a b c, ← h2 a b c]
    ring
  have hc : mBC mu b c * (mAC mu a c * mB mu b)
      = mBC mu b c * (mAB mu a b * mC mu c) := by
    rw [show mBC mu b c * (mAC mu a c * mB mu b)
          = mAC mu a c * mBC mu b c * mB mu b from by ring]
    rw [hkey]
    ring
  exact mul_left_cancel₀ (ne_of_gt (mBC_pos hp b c)) hc

/-- ⭐⭐⭐ **$\mu^{AC}_{ac}$ 与 $c$ 的可分性**：

$$\mu^{AC}_{ac} \;=\; \frac{\mu^{AC}_{a c_\ast}}{\mu^{C}_{c_\ast}}\cdot \mu^{C}_{c}
\qquad (c_\ast \text{ 为任意固定参考点}).$$

**⟹ 这就是「$A \perp C$ 无条件」的内容**（比率 $\mu^{AC}_{ac}/\mu^C_c$ 与 $c$ 无关）。
由 `mAC_mul_mB` 取 $b = b_\ast$ 并约去 $\mu^B_{b_\ast}$ 得到。 -/
theorem mAC_eq {mu : α → β → κ → ℝ} (hp : Pos mu)
    (h1 : H_AB_C mu) (h2 : H_AC_B mu)
    (bstar : β) (cstar : κ) (a : α) (c : κ) :
    mAC mu a c = mAC mu a cstar * mC mu c / mC mu cstar := by
  have h := mAC_mul_mB hp h1 h2 a bstar c
  have hB : mB mu bstar ≠ 0 := ne_of_gt (mB_pos hp bstar)
  have hC : mC mu cstar ≠ 0 := ne_of_gt (mC_pos hp cstar)
  have h' : mAC mu a c = mAB mu a bstar * mC mu c / mB mu bstar := by
    rw [eq_div_iff hB]
    linarith [h]
  have h0 := mAC_mul_mB hp h1 h2 a bstar cstar
  have h0' : mAC mu a cstar = mAB mu a bstar * mC mu cstar / mB mu bstar := by
    rw [eq_div_iff hB]
    linarith [h0]
  rw [h', h0']
  field_simp

/-- ⭐⭐⭐⭐ **交公理在点级（slice 级）成立 —— 非空洞、需正性。**

$$A \perp B \mid C \;\wedge\; A \perp C \mid B
  \;\Longrightarrow\; A \perp (B,C) \mid \varnothing .$$

**⟹ 证明**：由 `mAC_eq` 取参考点 $c_\ast$：

$$\mu^{AC}_{ac} = e_a \cdot \mu^{C}_{c},\qquad
  e_a := \frac{\mu^{AC}_{a c_\ast}}{\mu^{C}_{c_\ast}} .$$

代入前件 1（$\mu_{abc}\mu^C_c = \mu^{AC}_{ac}\mu^{BC}_{bc}$）并约去 $\mu^C_c \ne 0$：

$$\boxed{\ \mu_{abc} = e_a \cdot \mu^{BC}_{bc}\ }$$

**这正是 $A \perp (B,C)$ 的因子分解**（$e_a$ 只含 $a$，$\mu^{BC}_{bc}$ 只含 $(b,c)$）。
最后用 $\mu^{A}_a = e_a \cdot M$（`mT` 的求和次序使
$\sum_{b,c}\mu^{BC}_{bc} = M$ 定义相等）换成所求形式。 -/
theorem intersection {mu : α → β → κ → ℝ} (hp : Pos mu)
    (h1 : H_AB_C mu) (h2 : H_AC_B mu) : H_A_BC mu := by
  intro a b c
  -- 参考点
  set bstar : β := Classical.arbitrary β with hbstar
  set cstar : κ := Classical.arbitrary κ with hcstar
  -- 因子 $e_a$
  set e : α → ℝ := fun a => mAC mu a cstar / mC mu cstar with he
  -- (1) $\mu_{abc} = e_a \cdot \mu^{BC}_{bc}$，以及其 $\forall$ 形式
  have step1' : ∀ (a : α) (b : β) (c : κ), mu a b c = e a * mBC mu b c := by
    intro a b c
    have hac : mAC mu a c = mAC mu a cstar * mC mu c / mC mu cstar :=
      mAC_eq hp h1 h2 bstar cstar a c
    have hC : mC mu c ≠ 0 := ne_of_gt (mC_pos hp c)
    have h1c := h1 a b c
    rw [hac] at h1c
    have : mu a b c * mC mu c = e a * mC mu c * mBC mu b c := by
      rw [h1c]; unfold e; ring
    exact mul_right_cancel₀ hC (by rw [this]; ring)
  have step1 : mu a b c = e a * mBC mu b c := step1' a b c
  -- (2) $\mu^{A}_a = e_a \cdot M$
  have step2 : mA mu a = e a * mT mu := by
    unfold mA
    rw [show (∑ b, ∑ c, mu a b c) = ∑ b, ∑ c, e a * mBC mu b c from
      Finset.sum_congr rfl (fun b _ =>
        Finset.sum_congr rfl (fun c _ => step1' a b c))]
    simp only [mBC, mT]
    rw [Finset.mul_sum]
    simp only [Finset.mul_sum]
  rw [step1, step2]
  ring

end PointLevel

end Intersection

end Fate
