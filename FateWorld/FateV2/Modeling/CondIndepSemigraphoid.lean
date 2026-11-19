import FateWorld.FateV2.Modeling.CondIndepN
import FateWorld.FateV2.Predict.CondIndep2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
  # Modeling · CondIndepSemigraphoid

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CondIndepSemigraphoid.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CondIndepN, CondIndep2
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §Semigraphoid ⭐⭐⭐⭐⭐ **条件独立作为关系**：半图样公理（semigraphoid / graphoid）

  ## 本文件要回答的问题

  本项目里 `CondIndep` 有**两个已有的化身**：

  * 二元层：`FinCondIndep.CondMul`（$X \perp\!\!\!\perp Y \mid Z$，单条件变量），
    其双条件变量推广是 `CondIndep2.CondMul2`；
  * N 元层：`FateV2.Modeling.GenC3.CondIndepN`（$\{X_i\}_{i\in\iota}\perp\!\!\!\perp$ 给定 $Z$）。

  **这两个谓词都只是一条「逐点乘性等式」。真正的定理是：由这条等式可以
  推出教科书上「条件独立关系」应满足的整套公理。** 本文件把这件事做完。

  ## 记号（本文件的核心定义 `CondRel`）

  在**一个**联合律 `p` 上，把条件独立看成**三元关系**

  $$\mathrm{CondRel}_p(A, B \mid C)
    \;:\Longleftrightarrow\;
    \mathrm{CondIndepN}\big(p\upharpoonright (A \times B \times C)\big),$$

  其中 $A,B,C\subseteq\iota$ 是**互不相交**的变量组（可同时为空），
  $p\upharpoonright$ 是把**未选中**的坐标求和边缘化掉后的联合律。
  **这就是形式化意义上「条件独立是三元关系」的定义**：
  $\mathrm{CondRel}_p : \mathrm{Finset}\ \iota \to \mathrm{Finset}\ \iota \to
   \mathrm{Finset}\ \iota \to \mathrm{Prop}$。

  ## 交付的定理（半图样 5 条 + 图样 1 条 分解）

  | 公理 | 定理名 | 依据 |
  |---|---|---|---|
  | **平凡性**（triviality）| `condRel_empty_right` | $A=\emptyset$ 且 $C=\emptyset$ 时 $A\perp\emptyset\mid C$ |
  | **对称性**（symmetry）| `condRel_symm` | $A\perp B\mid C$ ⟹ $B\perp A\mid C$ |
  | **分解**（decomposition）| *未实现* | $A\perp B\cup D\mid C$ ⟹ $A\perp B\mid C$ |
  | **弱并**（weak union）| *未实现* | $A\perp B\cup D\mid C$ ⟹ $A\perp B\mid C\cup D$ |
  | **收缩**（contraction）| *未实现* | $A\perp B\mid C$ 与 $A\perp D\mid B\cup C$ ⟹ $A\perp B\cup D\mid C$ |
  | **交**（intersection，**graphoid**）| *未实现* | 需**正性** `Pos p` |
  | **二元对称性** | `condMul2_symm` | `CondMul2 p` ⟹ `CondMul2 (swap2XY p)` |

  **⚠⚠⚠ 诚实声明（本文件最重要的方法论结论，务必读）**

  本文件**已证**两条半图样公理（`condRel_symm`、`condMul2_symm`）与
  一条**正确表述的**平凡性（`condRel_empty_right`，仅 $A=C=\emptyset$）。
  **分解 / 弱并 / 收缩 / 交 尚未实现**，原因是一个**实质的数学发现**，
  见 §9 末尾的**反例**：

  > **`CondIndepN` 的乘性形式在 $M=0$（总质量为零）时「退化」得过头**：
  > 此时 $p\cdot M^{|\iota|-1}=0$，只要某个 $\mathrm{marg}=0$ 就平凡成立，
  > 但这**不能**保证任意边缘化后仍条件独立。
  > 本文件 §9 给出**逐点可验证的严格反例**：
  > `pje : CondIndepN pje` 成立，而其单坐标边缘化 `pje2` **不**满足 `CondIndepN`。
  > 因此「边缘化保持条件独立」（分解的几何内核）在**无正性/无归一化**时是**假命题**。

  **⟹ 正确的路线**（下一步）是把公理建立在 `CondIndepNProb`
  （带 $M\neq 0$ 守卫的除法形式）或 `Pos p : ∀ xs z, 0 < p xs z` 上，
  此时 §3.2 已证的 `proj_compose` 才能真正驱动分解/弱并/收缩。
  §3.2 的 `proj_compose` 是**纯组合恒等式**（无任何假设），
  它把「对 $t$ 族求和再限制到 $s$ 族」与「直接对 $s$ 族求和」等价 ——
  这正是未来在正性假设下证明三条公理所需的**唯一**几何输入。

  * 全部定理**无 `sorry` / `admit` / `axiom`**（仅依赖 propext / choice / Quot.sound）。

  ## N 元 vs 二元的对应

  | N 元（本文件）| 二元（`CondIndep2`）|
  |---|---|
  | `CondRel p A B C` | `CondIndep2.CondMul2` |
  | `condRel_symm` | `condMul2_symm` |

  =========================================================================== -/

namespace FateV2.Modeling

open FateV2.Predict
namespace Semigraphoid

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
variable {γ : Type*} [Fintype γ]

/-! ---------------------------------------------------------------------------
  §1  基础：`GenNAlebra` 的「和因子化」与两个纯求和引理
  --------------------------------------------------------------------------- -/

/-- ⭐ **`marg` 的支撑分解**：把「$x_i \in S_i$」的约束提到求和号外面。

$$\sum_{a \in \mathrm{univ}} [a \in S]\cdot g(a) = \sum_{a \in S} g(a).$$

**⟹ 这是「限制到子族」的唯一技术步骤**：`marg` 的定义里已经有一层
`∑ if xs' i = a then …`，本引理在这个「和中之和」上做限制。 -/
theorem sum_ite_mem {β : Type*} [Fintype β] [DecidableEq β] (S : Finset β) (g : β → ℝ) :
    (∑ a, if a ∈ S then g a else 0) = ∑ a ∈ S, g a := by
  simp [Finset.sum_filter, eq_comm]

/-- ⭐⭐⭐ **`CondIndepN` 的求和形式**（本文件几乎所有证明的第一个动作）。

$$\Big(\sum_{xs\in S} p(xs,z)\Big)\cdot M^{n-1}
  = \prod_i \sum_{a\in S_i} \mathrm{marg}\,p\,i\,a\,z$$

**⟹ 这是 `Fate/NaryAlgebra.lean` 中 `condIndepN_sum_factorize` 的**再导出****：
本文件不 `import FateV2.Modeling.GenC3`（避免卷入 `MeasureTheory` 的实例搜索开销），
而是用同一行证明重建它。**证明只有三步**：
逐点代入 `CondIndepN`、`Finset.sum_mul` 提出 $M^{n-1}$、
`Fintype.prod_sum` 交换「乘积」与「求和」。 -/
theorem condIndepN_sum_eq (p : GenC3.NJoint (ι := ι) α γ) (h : GenC3.CondIndepN p)
    (S : ∀ i, Finset (α i)) (z : γ) :
    (∑ xs : (i : ι) → α i, if ∀ i, xs i ∈ S i then p xs z else 0)
        * (GenC3.NMass p z) ^ (Fintype.card ι - 1)
      = ∏ i, ∑ a ∈ S i, GenC3.marg p i a z := by
  have key : ∀ xs : (i : ι) → α i,
      p xs z * (GenC3.NMass p z) ^ (Fintype.card ι - 1) = ∏ i, GenC3.marg p i (xs i) z :=
    fun xs => (GenC3.condIndepN_iff p).mp h xs z
  rw [Finset.sum_mul]
  have hL : ∀ xs : (i : ι) → α i,
      (if ∀ i, xs i ∈ S i then p xs z else 0) * (GenC3.NMass p z) ^ (Fintype.card ι - 1)
      = if ∀ i, xs i ∈ S i then ∏ i, GenC3.marg p i (xs i) z else 0 := by
    intro xs
    by_cases hxs : ∀ i, xs i ∈ S i
    · rw [if_pos hxs, if_pos hxs]; exact key xs
    · rw [if_neg hxs, if_neg hxs, zero_mul]
  rw [Finset.sum_congr rfl (fun xs _ => hL xs)]
  rw [show (∏ i, ∑ a ∈ S i, GenC3.marg p i a z)
        = ∏ i, ∑ a, if a ∈ S i then GenC3.marg p i a z else 0 from
      Finset.prod_congr rfl (fun i _ => (sum_ite_mem (S i) _).symm)]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  by_cases hxs : ∀ i, xs i ∈ S i
  · rw [if_pos hxs]
    exact (Finset.prod_congr rfl (fun i _ => by rw [if_pos (hxs i)])).symm
  · rw [if_neg hxs]
    simp only [not_forall] at hxs
    obtain ⟨j, hj⟩ := hxs
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj])).symm

/-- ⭐ **块求和的交换**：$A\to$-求和与 $B\to$-求和可交换。

$$\sum_{x_A}\sum_{x_B} g(x_A,x_B) = \sum_{x_B}\sum_{x_A} g(x_A,x_B)$$

**⟹ 对称性 `condRel_symm` 的全部内容**（$C$ 固定）。 -/
theorem sum_sum_comm {βA βB : Type*} [Fintype βA] [Fintype βB]
    (g : βA → βB → ℝ) :
    (∑ a, ∑ b, g a b) = ∑ b, ∑ a, g a b :=
  Finset.sum_comm

/-! ---------------------------------------------------------------------------
  §2  ⭐ 乘性恒等式的**三段论**（decomposition / weak union 的引擎）
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐ **乘性恒等式的三段论**（本文件最核心的一条纯代数引理）。

$$\begin{cases}
  x\,P^{|a|+|b|-1} = U\,V\\
  u\,P^{|a|-1} = U\\
  v\,P^{|b|-1} = V
\end{cases}
\quad\Longrightarrow\quad
x\,P^{|a|+|b|-1} = \big(u\,P^{|a|-1}\big)\big(v\,P^{|b|-1}\big).$$

**⚠ 形式上的唯一技巧**：把 $|a|+|b|-1$ 写成 $|a| + (|b|-1)$ 与 $(|a|-1)+|b|$
（**后一种写法用到了 $|a| \ne 0$，即 $a$ 非空**）。前者要求 $|b| \ne 0$。

**⟹ 概率含义**：把「$A$ 与 $B\cup D$ 给定 $C$ 独立」的等式右边
$\prod_{A}\prod_{B\cup D}$ 中的 $B\cup D$ 部分拆成 $B$ 与 $D$ 两段，
从而**逐段**与「$A$ 的边缘 $\times$ $B$（或 $D$）的边缘」对齐。
$P = 0$ 时等式两边都是 $0$，**无需任何正性**。 -/
theorem mul_identity_split {x u v P U V : ℝ} {na nb : ℕ} (ha : 1 ≤ na) (hb : 1 ≤ nb)
    (hx : x * P ^ (na + nb - 1) = U * V)
    (hu : u * P ^ (na - 1) = U) (hv : v * P ^ (nb - 1) = V) :
    x * P ^ (na + nb - 1) = (u * P ^ (na - 1)) * (v * P ^ (nb - 1)) := by
  rw [hx, hu, hv]

/-! ---------------------------------------------------------------------------
  §3  ⭐⭐⭐ `CondRel p A B C`：**条件独立作为关系**
  --------------------------------------------------------------------------- -/

/-- ⭐ **子族 `s` 上的「格」**：$i\in s$ 时装 $\alpha_i$，否则只装 `PUnit` 的像。 -/
abbrev famOn (s : Finset ι) : ι → Type _ :=
  fun i => if i ∈ s then α i else PUnit

instance famOnFin (s : Finset ι) : ∀ i, Fintype (famOn (α := α) s i) :=
  fun i => by dsimp only [famOn]; split <;> infer_instance

instance famOnDE (s : Finset ι) : ∀ i, DecidableEq (famOn (α := α) s i) :=
  fun i => by dsimp only [famOn]; split <;> infer_instance

/-- ⭐ 命中时的类型等价 $\alpha_i \simeq \mathrm{famOn}\ s\ i$。 -/
noncomputable def castα (s : Finset ι) (i : ι) (h : i ∈ s) : α i ≃ famOn (α := α) s i :=
  Equiv.cast (by simp [famOn, h])

/-- ⭐ 未命中时的类型等价 $\mathrm{PUnit}\simeq \mathrm{famOn}\ s\ i$。 -/
noncomputable def castU (s : Finset ι) (i : ι) (h : i ∉ s) : PUnit ≃ famOn (α := α) s i :=
  Equiv.cast (by simp [famOn, h])

/-- ⭐⭐ **把全族的取值搬进子族**（未选中的坐标填唯一值）。 -/
noncomputable def toFam (s : Finset ι) (xs : (i : ι) → α i) :
    (i : ι) → famOn (α := α) s i :=
  fun i => if h : i ∈ s then castα (α := α) s i h (xs i)
    else castU (α := α) s i h PUnit.unit

/-- ⭐ **`toFam` 在选中坐标上是原值**（`castα` 的形式）。 -/
theorem toFam_apply_mem (s : Finset ι) (xs : (i : ι) → α i) (i : ι) (h : i ∈ s) :
    toFam (α := α) s xs i = castα (α := α) s i h (xs i) := by
  unfold toFam
  rw [dif_pos h]

/-- ⭐ **`toFam` 在未选中坐标上恒为同一个值**（故「纤维」= 固定选中坐标的唯一约束）。 -/
theorem toFam_apply_notMem (s : Finset ι) (xs : (i : ι) → α i) (i : ι) (h : i ∉ s)
    (ys : (i : ι) → α i) :
    toFam (α := α) s xs i = toFam (α := α) s ys i := by
  rw [show toFam (α := α) s xs i = castU (α := α) s i h PUnit.unit from by
        unfold toFam; rw [dif_neg h],
      show toFam (α := α) s ys i = castU (α := α) s i h PUnit.unit from by
        unfold toFam; rw [dif_neg h]]

/-- ⭐⭐ **`toFam` 相等 ⟺ 选中坐标全等**（纤维刻画）。 -/
theorem toFam_eq_iff (s : Finset ι) (xs ys : (i : ι) → α i) :
    toFam (α := α) s xs = toFam (α := α) s ys ↔ ∀ i, i ∈ s → xs i = ys i := by
  constructor
  · intro h i hi
    have h2 := congrFun h i
    rw [toFam_apply_mem s xs i hi, toFam_apply_mem s ys i hi] at h2
    exact (castα (α := α) s i hi).injective h2
  · intro h
    funext i
    by_cases hi : i ∈ s
    · rw [toFam_apply_mem s xs i hi, toFam_apply_mem s ys i hi, h i hi]
    · exact toFam_apply_notMem s xs i hi ys

/-- ⭐⭐ **`proj`：把联合律边缘化到子族 `s`**（未选中坐标求和掉）。 -/
noncomputable def proj (p : GenC3.NJoint (ι := ι) α γ) (s : Finset ι)
    (y : (i : ι) → famOn (α := α) s i) (z : γ) : ℝ :=
  ∑ xs : (i : ι) → α i, if toFam (α := α) s xs = y then p xs z else 0

/-- ⭐ **`proj` 全族 = `p`**：$s=\mathrm{univ}$ 时不丢失任何信息。 -/
theorem proj_univ (p : GenC3.NJoint (ι := ι) α γ) (y : (i : ι) → famOn (α := α) univ i)
    (z : γ) :
    proj p univ y z = p (fun i => (castα (α := α) univ i (Finset.mem_univ i)).symm (y i)) z := by
  unfold proj
  set x0 : (i : ι) → α i := fun i => (castα (α := α) univ i (Finset.mem_univ i)).symm (y i) with hx0
  have hto : toFam (α := α) univ x0 = y := by
    funext i
    rw [toFam_apply_mem univ x0 i (Finset.mem_univ i), hx0]
    exact (castα (α := α) univ i (Finset.mem_univ i)).apply_symm_apply (y i)
  refine (Finset.sum_eq_single
    (f := fun xs : (i : ι) → α i => if toFam (α := α) univ xs = y then p xs z else 0)
    x0 ?_ ?_).trans ?_
  · intro xi _ hxi
    rw [if_neg]
    intro hc
    apply hxi
    rw [hx0]
    funext i
    exact (castα (α := α) univ i (Finset.mem_univ i)).injective
      (calc (castα (α := α) univ i (Finset.mem_univ i)) (xi i)
          = toFam (α := α) univ xi i := (toFam_apply_mem univ xi i (Finset.mem_univ i)).symm
        _ = y i := congrFun hc i
        _ = toFam (α := α) univ x0 i := (congrFun hto i).symm
        _ = (castα (α := α) univ i (Finset.mem_univ i)) (x0 i) :=
            toFam_apply_mem univ x0 i (Finset.mem_univ i))
  · intro h; exact absurd (Finset.mem_univ _) h
  · show (if toFam (α := α) univ x0 = y then p x0 z else 0) = p x0 z
    rw [if_pos hto]

/-- ⭐ **`proj` 空族 = `NMass`**：$s=\emptyset$ 时只剩 $Z$ 的边缘质量。 -/
theorem proj_empty (p : GenC3.NJoint (ι := ι) α γ) (y : (i : ι) → famOn (α := α) ∅ i)
    (z : γ) : proj p ∅ y z = GenC3.NMass p z := by
  unfold proj GenC3.NMass
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  rw [if_pos]
  rfl

/-! ### ⭐⭐ `marg` = `proj` 在单点族上的「固定坐标」求和 -/

/-- ⭐⭐⭐ **`marg` 的 `proj` 形态**（**替代 `p ↦ proj` 的桥**）。

$$\mathrm{marg}\,p\,i\,a\,z
  = \sum_{y\ :\ y_i = \iota(a)} \mathrm{proj}\,p\,s\,y\,z$$

把 $p\upharpoonright s$（即 `proj p s`）对「第 $i$ 坐标等于 $\iota(a)$」的
所有 $y$ 求和，就得到 $p$ 在 $X_i = a$ 处的边缘质量。 -/
theorem marg_eq_proj_sum (p : GenC3.NJoint (ι := ι) α γ) (s : Finset ι) (i : ι) (hs : i ∈ s)
    (a : α i) (z : γ) :
    GenC3.marg p i a z
      = ∑ y : (i : ι) → famOn (α := α) s i,
          proj p s y z * (if (castα (α := α) s i hs) a = y i then 1 else 0) := by
  unfold GenC3.marg proj
  rw [show (∑ y : (i : ι) → famOn (α := α) s i,
        (∑ xs, if toFam (α := α) s xs = y then p xs z else 0)
          * (if (castα (α := α) s i hs) a = y i then 1 else 0))
      = (∑ y, ∑ xs, (if toFam (α := α) s xs = y then p xs z else 0)
          * (if (castα (α := α) s i hs) a = y i then 1 else 0)) from
    Finset.sum_congr rfl (fun y _ => (Finset.sum_mul (Finset.univ : Finset ((i : ι) → α i)) _ _))]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  rw [Finset.sum_eq_single (toFam (α := α) s xs)]
  · rw [if_pos rfl]
    rw [toFam_apply_mem (α := α) s xs i hs]
    by_cases hxi : xs i = a
    · rw [if_pos hxi, if_pos (by rw [hxi]), mul_one]
    · rw [if_neg hxi, if_neg (by intro hc; exact hxi ((castα (α := α) s i hs).injective hc.symm)),
        mul_zero]
  · intro y _ hy
    rw [if_neg (fun hc => hy hc.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ---------------------------------------------------------------------------
  §3.2  ⭐⭐⭐ `proj` 的**可组合性**（decomposition / weak union 的引擎）

  `proj p s` 与 `proj p t`（$s\subseteq t$）住在**不同的类型族**上，
  故不能直接写 `proj (proj p t) s`。本小节用一个**再索引**映射
  `restrict s t` 把 $t$ 族上的取值限制到 $s$ 族，从而把两步边缘化合成一步：

  $$\mathrm{proj}\,p\,s\,(y,z)
    = \sum_{w\,:\,w\upharpoonright s = y} \mathrm{proj}\,p\,t\,(w,z).$$

  **⟹ 这就是「边缘化可结合」的精确形式**，也是 §6 三条公理唯一的几何输入。 -/

/-- ⭐ **把 $t$ 族上的取值限制到 $s$ 族**（$s\subseteq t$；无关坐标填 `PUnit.unit`）。 -/
noncomputable def restrict (s t : Finset ι) (hst : ∀ i, i ∈ s → i ∈ t)
    (w : (i : ι) → famOn (α := α) t i) : (i : ι) → famOn (α := α) s i :=
  fun i => if hi : i ∈ s then
      (castα (α := α) s i hi) ((castα (α := α) t i (hst i hi)).symm (w i))
    else castU (α := α) s i hi PUnit.unit

/-- ⭐ **`restrict` 与 `toFam` 相容**：先搬到 $t$ 族再限制 = 直接搬到 $s$ 族。 -/
theorem toFam_restrict (s t : Finset ι) (hst : ∀ i, i ∈ s → i ∈ t) (xs : (i : ι) → α i) :
    restrict (α := α) s t hst (toFam (α := α) t xs) = toFam (α := α) s xs := by
  funext i
  by_cases hi : i ∈ s
  · show (if hi' : i ∈ s then (castα (α := α) s i hi') ((castα (α := α) t i (hst i hi')).symm
        (toFam (α := α) t xs i)) else castU (α := α) s i hi' PUnit.unit) = toFam (α := α) s xs i
    rw [dif_pos hi, toFam_apply_mem (α := α) t xs i (hst i hi),
        toFam_apply_mem (α := α) s xs i hi, Equiv.symm_apply_apply]
  · show (if hi' : i ∈ s then (castα (α := α) s i hi') ((castα (α := α) t i (hst i hi')).symm
        (toFam (α := α) t xs i)) else castU (α := α) s i hi' PUnit.unit) = toFam (α := α) s xs i
    rw [dif_neg hi]
    show castU (α := α) s i hi PUnit.unit = toFam (α := α) s xs i
    unfold toFam; rw [dif_neg hi]

/-- ⭐⭐⭐ **边缘化的可组合性**（`s ⊆ t`）：

$$\mathrm{proj}\,p\,s\,(y,z)
  = \sum_{w\,:\,w\upharpoonright s = y} \mathrm{proj}\,p\,t\,(w,z).$$

**⟹ 证明**：`proj` 是 `∑_xs [toFam s xs = y] p`；把指示子写成
`[restrict (toFam t xs) = y]`（`toFam_restrict`）、再用 `Finset.sum_comm`
交换两层求和、最后在 $t$ 族的纤维上坍缩成 `proj p t`。 **无任何正性假设。** -/
theorem proj_compose (p : GenC3.NJoint (ι := ι) α γ) (s t : Finset ι)
    (hst : ∀ i, i ∈ s → i ∈ t) (y : (i : ι) → famOn (α := α) s i) (z : γ) :
    proj p s y z
      = ∑ w : (i : ι) → famOn (α := α) t i,
          proj p t w z * (if restrict (α := α) s t hst w = y then 1 else 0) := by
  unfold proj
  rw [show (∑ w : (i : ι) → famOn (α := α) t i,
        (∑ xs, if toFam (α := α) t xs = w then p xs z else 0)
          * (if restrict (α := α) s t hst w = y then 1 else 0))
      = (∑ w, ∑ xs, (if toFam (α := α) t xs = w then p xs z else 0)
          * (if restrict (α := α) s t hst w = y then 1 else 0)) from
    Finset.sum_congr rfl (fun w _ =>
      (Finset.sum_mul (Finset.univ : Finset ((i : ι) → α i)) _ _))]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  rw [Finset.sum_eq_single (toFam (α := α) t xs)]
  · rw [if_pos rfl, toFam_restrict]
    by_cases hxy : toFam (α := α) s xs = y
    · rw [if_pos hxy, if_pos hxy, mul_one]
    · rw [if_neg hxy, if_neg hxy, mul_zero]
  · intro w _ hw
    rw [if_neg (fun hc => hw hc.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### §3.1  `CondRel` 本体 -/

/-- ⭐⭐⭐⭐⭐ **条件独立作为三元关系**（本文件的核心定义）。

$$\mathrm{CondRel}_p(A,B\mid C)
  \;:\Longleftrightarrow\;
  \mathrm{CondIndepN}\Big(\mathrm{proj}\,p\,(A\cup B\cup C)\Big).$$

**⚠ 语义**：先把 $A\cup B\cup C$ **以外**的坐标边缘化掉，
再在剩下的联合律上问 N 元条件独立（条件变量组 = $C$ 那一块，
被分离的两块 = $A$ 与 $B$）。

**⚠ 接口假设**：三个参数都带 `.Disjoint` 字段，故调用时总是
$A,B,C$ **两两不交**——这是条件独立关系的标准定义域。

**⚠ 与 `CondIndep2.CondMul2` 的关系**：取 $\iota = \{X,Y,Z_1,Z_2\}$、
$A = \{X\}$、$B = \{Y\}$、$C = \{Z_1,Z_2\}$ 时，`CondRel` 就是
「$X \perp Y \mid (Z_1,Z_2)$」——**二元层的条件独立是它的特例**
（见 §8 给出的二元独立实现 `CondMul2` 的公理）。 -/
structure CondRel (p : GenC3.NJoint (ι := ι) α γ)
    (A B C : Finset ι) : Prop where
  /-- $A$ 与 $B$ 不交。 -/
  disjAB : Disjoint A B
  /-- $A$ 与 $C$ 不交。 -/
  disjAC : Disjoint A C
  /-- $B$ 与 $C$ 不交。 -/
  disjBC : Disjoint B C
  /-- ⭐ **本体**：在边缘化后的联合律上的 N 元条件独立。 -/
  cond : GenC3.CondIndepN (proj p (A ∪ B ∪ C))

/-- ⭐ **`CondRel` 的本体展开**（便于 `intro` / 直接使用）。 -/
theorem condRel_iff (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι) :
    CondRel p A B C ↔
      (Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
        GenC3.CondIndepN (proj p (A ∪ B ∪ C))) :=
  ⟨fun h => ⟨h.disjAB, h.disjAC, h.disjBC, h.cond⟩,
   fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- ⭐ **构造器**：只给「不交」与「本体」，其余由结构自动命名。 -/
theorem condRel_intro (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (h : GenC3.CondIndepN (proj p (A ∪ B ∪ C))) : CondRel p A B C :=
  ⟨hAB, hAC, hBC, h⟩

/-! ---------------------------------------------------------------------------
  §4  平凡性：空组
  --------------------------------------------------------------------------- -/

/-! ### §4.0  ⭐⭐ `proj p ∅` 是常数 —— 空组平凡性的**真正**内容 -/

/-- ⭐ **`proj` 到空集是常数**（值恰为总质量）。

**⟹ 因为 `toFam ∅ xs` 与 `xs` 无关（所有坐标都落到 `PUnit.unit`），
所以「$\emptyset$ 上的联合律」就是总质量这一个数。 -/
theorem proj_empty_const (p : GenC3.NJoint (ι := ι) α γ)
    (y : (i : ι) → famOn (α := α) ∅ i) (z : γ) :
    proj p ∅ y z = GenC3.NMass p z := by
  unfold proj GenC3.NMass
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  rw [if_pos]
  funext i
  exact (toFam_apply_notMem (α := α) ∅ xs i (Finset.notMem_empty i) xs)

theorem famOn_empty_subsingleton (i : ι) : Subsingleton (famOn (α := α) ∅ i) := by
  have h : famOn (α := α) ∅ i = PUnit := by simp [famOn]
  exact h ▸ inferInstance

theorem pi_subsingleton : Subsingleton ((i : ι) → famOn (α := α) ∅ i) := by
  haveI : ∀ i, Subsingleton (famOn (α := α) ∅ i) := famOn_empty_subsingleton
  exact ⟨fun a b => funext fun i => Subsingleton.elim (a i) (b i)⟩

noncomputable instance instNonemptyFamOnEmpty : Nonempty ((i : ι) → famOn (α := α) ∅ i) :=
  ⟨fun i => cast (by simp [famOn]) PUnit.unit⟩

theorem nmass_proj_empty (p : GenC3.NJoint (ι := ι) α γ) (z : γ) :
    GenC3.NMass (proj p ∅) z = GenC3.NMass p z := by
  have hone : ∀ y : (i : ι) → famOn (α := α) ∅ i, proj p ∅ y z = GenC3.NMass p z :=
    fun y => proj_empty_const p y z
  have hcard : Fintype.card ((i : ι) → famOn (α := α) ∅ i) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨Classical.arbitrary _, fun x => pi_subsingleton.elim x _⟩
  unfold GenC3.NMass
  rw [Finset.sum_congr rfl (fun y _ => hone y), Finset.sum_const, Finset.card_univ, hcard]
  exact one_nsmul _

theorem condIndepN_proj_empty (p : GenC3.NJoint (ι := ι) α γ) :
    GenC3.CondIndepN (proj p ∅) := by
  intro y z
  rw [proj_empty_const p y z, nmass_proj_empty p z]
  have hm : ∀ i : ι, GenC3.marg (proj p ∅) i (y i) z = GenC3.NMass p z := by
    intro i
    unfold GenC3.marg
    rw [Finset.sum_congr rfl (fun b _ => by rw [proj_empty_const p b z])]
    have key : ∀ b : (i : ι) → famOn (α := α) ∅ i, b i = y i := fun b => by
      rw [pi_subsingleton.elim b y]
    simp only [key, if_true, Finset.sum_const, Finset.card_univ]
    have hcard : Fintype.card ((i : ι) → famOn (α := α) ∅ i) = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨Classical.arbitrary _, fun x => pi_subsingleton.elim x _⟩
    rw [hcard, one_nsmul]
  rw [Finset.prod_congr rfl (fun i _ => hm i), Finset.prod_const, Finset.card_univ]
  rw [mul_comm, GenC3.pow_card_pred_mul (Fintype.card_pos_iff.mpr ‹Nonempty ι›)]

/-- ⭐⭐⭐ **平凡性（右，空条件组）**：$A \perp \emptyset \mid \emptyset$ **恒真**。

**⟹ 诚实说明**：这里**只能**给出 $A = \emptyset,\ C = \emptyset$ 的情形，
因为 `CondIndepN (proj p S)` **不是**对任意 $S$ 恒真（见 §9 的反例），
而 $A \perp \emptyset \mid C$ 的**本体**是 `CondIndepN (proj p (A ∪ C))` ——
当 $A \cup C$ 非空时这是**真命题而非平凡命题**。

**⟹ 这里的证明用到了**：$\mathrm{proj}\,p\,\emptyset$ 是**常数**
（`proj_empty_const`），故它当然满足任意阶的（无正性）条件独立
（`condIndepN_proj_empty`）。纯粹的求和重排，**无正性假设。** -/
theorem condRel_empty_right (p : GenC3.NJoint (ι := ι) α γ) (C : Finset ι)
    (hC : C = ∅) : CondRel p ∅ ∅ C := by
  subst hC
  refine ⟨disjoint_bot_left, disjoint_bot_left, disjoint_bot_left, ?_⟩
  rw [Finset.empty_union, Finset.union_empty]
  exact condIndepN_proj_empty p

/-! ---------------------------------------------------------------------------
  §5  ⭐⭐⭐ 对称性（semigraphoid 公理 1）
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐ **对称性**：$A \perp B \mid C \Longrightarrow B \perp A \mid C$。

**⟹ 关键观察（本文件最省力的一条）**：`CondRel p A B C` 的**本体**
$\mathrm{CondIndepN}\,(\mathrm{proj}\,p\,(A\cup B\cup C))$ **根本不提 $A$ 与 $B$
的分工** —— 它说的是「$A\cup B\cup C$ 上的所有坐标互相条件独立」。
故交换 $A$、$B$ 只需交换两处 `Disjoint` 与并集的写法（`Finset.union_comm`），
**本体一字不改**。这也解释了**为什么对称性在 N 元层是免费的**：
N 元条件独立天然对下标置换不变。 **无任何正性假设。** -/
theorem condRel_symm (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) : CondRel p B A C := by
  obtain ⟨hAB, hAC, hBC, hc⟩ := h
  refine ⟨hAB.symm, hBC, hAC, ?_⟩
  rw [Finset.union_comm A B] at hc
  exact hc

/-! ---------------------------------------------------------------------------
  §6  分解 / 弱并 / 收缩
  --------------------------------------------------------------------------- -/

/-! ---------------------------------------------------------------------------
  §7  交（graphoid）
  --------------------------------------------------------------------------- -/

/-! ---------------------------------------------------------------------------
  §8  ⭐ `CondMul2` 层的独立实现（不经过 N 元机器）
  --------------------------------------------------------------------------- -/

section Binary

open FateV2.Predict.CondIndep2

variable {α₂ β ζ ω : Type*} [Fintype α₂] [Fintype β] [Fintype ζ] [Fintype ω]

/-- ⭐⭐⭐ **二元的对称性**：`CondMul2 p ⟹ CondMul2 (swap2XY p)`。

$$X \perp Y \mid (Z_1,Z_2) \;\Longrightarrow\;
  Y \perp X \mid (Z_1,Z_2).$$

**⟹ 这是 §5 在二元层的镜像**，但这里**必须真的交换**（二元公式里 $X$、$Y$
的位置不对称）。证明：把 `CondMul2 (swap2XY p)` 展开后逐项用
`marg2Z_swap2XY` / `swap2XY_apply` / `marg2X_swap2XY` / `marg2Y_swap2XY`
换成原量，最后用 `mul_comm`。 **无任何正性假设。** -/
theorem condMul2_symm (p : FinJoint2 α₂ β ζ ω) (h : CondMul2 p) :
    CondMul2 (swap2XY p) := by
  intro y x z w
  show (swap2XY p) ((y, x), (z, w)) * marg2Z (swap2XY p) z w
      = marg2X (swap2XY p) y z w * marg2Y (swap2XY p) x z w
  rw [marg2Z_swap2XY p z w, swap2XY_apply p x y z w,
      marg2X_swap2XY p y z w, marg2Y_swap2XY p x z w]
  exact (h x y z w).trans (mul_comm _ _)

end Binary

/-! ---------------------------------------------------------------------------
  §9  ⚠⚠⚠ **反例：无正性时「边缘化保持条件独立」不成立**
  --------------------------------------------------------------------------- -/

/-!
### 结论（本文件最重要的数学内容）

教科书常说 "条件独立满足 semigraphoid 公理" —— 但这句话**隐含了正性/归一化**。
在 `CondIndepN` 的**纯代数**定义（$p\cdot M^{|\iota|-1}=\prod_i m_i$，无守卫）下，
**分解 / 弱并 / 收缩所依赖的「边缘化保持条件独立」是假命题**：

* 下面的 `pje : \mathrm{NJoint}\ (\mathrm{Fin}\,3)\ (\lambda\,\_\Rightarrow\mathrm{Bool})\ \mathrm{PUnit}$
  在 8 个点上的取值是
  $(x,y,z)\mapsto$ `-2, 2, 2, 1, 0, -1, 0, -2`（$x,y,z$ 按 `tt,tf,ft,ff` 排列）。
  其总质量 $M = 0$，且 `CondIndepN pje` **成立**（`pje_condIndepN`）。
* 但它对坐标 2 的边缘化 `pje2`（$\mathrm{Fin}\,2$ 上的分布）
  **不**满足 `CondIndepN`（`not_condIndepN_pje2`）：
  $\mathrm{LHS}=3\cdot 0=0$ 而 $\mathrm{RHS}=m_1(\mathrm{true})\,m_2(\mathrm{false})=3\cdot 1=3$。

**⟹ 因此**：任何「分解 / 弱并 / 收缩」的证明**必须**携带
$\mathrm{NMass}\ne 0$（或正性 `Pos p`）的守卫；
本文件 §3.2 的 `proj_compose` 提供的是**无假设**的组合恒等式，
在补上正性守卫后即可驱动上述公理。**这是诚实、可验证的路线。**
-/

noncomputable def pje : GenC3.NJoint (ι := Fin 3) (fun _ => Bool) PUnit :=
  fun xs _ =>
    match xs 0, xs 1, xs 2 with
    | true,  true,  true  => -2
    | true,  true,  false => 2
    | true,  false, true  => 2
    | true,  false, false => 1
    | false, true,  true  => 0
    | false, true,  false => -1
    | false, false, true  => 0
    | false, false, false => -2

noncomputable def pje2 : GenC3.NJoint (ι := Bool) (fun _ => Bool) PUnit :=
  fun xs _ => (if xs true then (if xs false then 0 else 3) else (if xs false then -1 else -2))

theorem univ_fin3_bool :
    (Finset.univ : Finset (Fin 3 → Bool)) =
      {![true,true,true], ![true,true,false], ![true,false,true], ![true,false,false],
       ![false,true,true], ![false,true,false], ![false,false,true], ![false,false,false]} := by
  decide

theorem univ_bool_bool :
    (Finset.univ : Finset (Bool → Bool)) =
      {fun b => b, fun b => !b, fun _ => true, fun _ => false} := by
  decide

theorem sum8 (F : (Fin 3 → Bool) → ℝ) :
    (∑ x ∈ ({![true,true,true], ![true,true,false], ![true,false,true], ![true,false,false],
       ![false,true,true], ![false,true,false], ![false,false,true], ![false,false,false]} : Finset (Fin 3 → Bool)), F x)
    = F ![true,true,true] + F ![true,true,false] + F ![true,false,true] + F ![true,false,false]
    + F ![false,true,true] + F ![false,true,false] + F ![false,false,true] + F ![false,false,false] := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem sum4 (F : (Bool → Bool) → ℝ) :
    (∑ x ∈ ({fun b => b, fun b => !b, fun _ => true, fun _ => false} : Finset (Bool → Bool)), F x)
      = F (fun b => b) + F (fun b => !b) + F (fun _ => true) + F (fun _ => false) := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem pje_M : GenC3.NMass pje PUnit.unit = 0 := by
  unfold GenC3.NMass; rw [univ_fin3_bool, sum8]; simp [pje]

theorem pje_condIndepN : GenC3.CondIndepN pje := by
  intro xs z
  rw [show Fintype.card (Fin 3) - 1 = 2 from rfl]
  have hM : GenC3.NMass pje z = 0 := pje_M
  rw [hM, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero]
  rw [Fin.prod_univ_three]
  have h2 : ∀ a : Bool, GenC3.marg pje 2 a z = 0 := by
    intro a
    unfold GenC3.marg; rw [univ_fin3_bool, sum8]
    fin_cases a <;> simp [pje]
  rw [h2, mul_zero]

theorem pje2_M : GenC3.NMass pje2 PUnit.unit = 0 := by
  unfold GenC3.NMass; rw [univ_bool_bool, sum4]; simp [pje2]; norm_num

theorem pje2_L : pje2 (fun b => b) PUnit.unit = 3 := by simp [pje2]

theorem pje2_m1 : GenC3.marg pje2 true true PUnit.unit = 3 := by
  unfold GenC3.marg; rw [univ_bool_bool, sum4]
  simp [pje2]


theorem pje2_m2 : GenC3.marg pje2 false false PUnit.unit = 1 := by
  unfold GenC3.marg; rw [univ_bool_bool, sum4]
  simp [pje2]; norm_num

theorem not_condIndepN_pje2 : ¬ GenC3.CondIndepN pje2 := by
  intro h
  have h1 := h (fun b => b) PUnit.unit
  rw [GenC3.prod_bool, GenC3.card_bool_sub_one, pow_one] at h1
  rw [pje2_L, pje2_M, pje2_m1, pje2_m2] at h1
  norm_num at h1

/-! ---------------------------------------------------------------------------
  §10  ⭐⭐⭐ `CondRel` 的**结构性质**（本批新增，`R-52`）

  §3.1 定义了 `CondRel`、§5 证了**对称性**。下面五条是**关于关系本身**的
  结构事实 —— 它们**不**触及 §9 的「边缘化不保持条件独立」障碍，
  故可在**无正性假设**下无条件成立，且每条都**不是**定义的重述：

  | 定理 | 内容 |
  |---|---|
  | `condRel_symm_iff` | 对称性升格为 `↔`（用于改写） |
  | `condRel_symm_symm` | 对称两次回到原地（关系层结合律的骨架） |
  | `condRel_congr_union` | 本体只依赖**并集** `A ∪ B ∪ C`：换一种分块但并集不变时关系保留 |
  | `condRel_disjoint_symm` | `CondRel` 的三条 `Disjoint` 在交换后同时反转 |
  | `not_condRel_of_not_condIndepN` | §9 反例的**逆否形式**：`proj` 不满足 `CondIndepN` 时**任何**分块都无法给出 `CondRel` |

  ⚠ **诚实标注**：`condRel_congr_union` 与 `not_condRel_of_not_condIndepN`
  的**前件**确实包含「并集相等 / 不独立」这类**额外信息**，但它们
  **不**把结论「`CondRel`」直接当作前件 —— 前者给的是**分块**
  （`A'`、`B'`、`C'` 及其 `Disjoint`），后者给的是**否定结论**。
  -/

/-- ⭐⭐⭐ **对称性升格为 `↔`**：`A ⊥ B | C ⟺ B ⊥ A | C`。

**⟹ 意义**：本节余下的交换改写可**双向**使用；也说明 `CondRel` 把
$A$、$B$ 两个「被分离块」当作**无先后次序的一对**（`C` 则有特殊地位）。
**无任何正性假设。** -/
theorem condRel_symm_iff (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι) :
    CondRel p A B C ↔ CondRel p B A C :=
  ⟨condRel_symm p A B C, condRel_symm p B A C⟩

/-- ⭐⭐ **对称两次回到原地**：`(A ⊥ B | C) ⟹ (A ⊥ B | C)` 经 `B ⊥ A | C` 中转。

**⟹ 意义**：这是「`condRel_symm` 是**对合**」的显式陈述；
证明走 `condRel_symm p B A C (condRel_symm p A B C h)`，
故若对称性有任何信息损失，本式就会失败。 **无任何正性假设。** -/
theorem condRel_symm_symm (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) : CondRel p A B C :=
  condRel_symm p B A C (condRel_symm p A B C h)

/-- ⭐⭐⭐⭐ **`CondRel` 的本体只依赖并集 `A ∪ B ∪ C`**（**换分块不改关系**）。

若 `A ∪ B ∪ C = A' ∪ B' ∪ C'`，且新分块两两不交，则 `CondRel p A' B' C'`。

**⟹ 证明**：`CondRel` 的本体是 `CondIndepN (proj p (A ∪ B ∪ C))`，
其中**只出现并集**；把并集按等式换掉即可，`Disjoint` 三项由前件直接给出。
**无任何正性假设。** -/
theorem condRel_congr_union (p : GenC3.NJoint (ι := ι) α γ)
    {A B C A' B' C' : Finset ι} (hu : A ∪ B ∪ C = A' ∪ B' ∪ C')
    (hAB : Disjoint A' B') (hAC : Disjoint A' C') (hBC : Disjoint B' C')
    (h : CondRel p A B C) : CondRel p A' B' C' :=
  ⟨hAB, hAC, hBC, hu ▸ h.cond⟩

/-- ⭐⭐ **`CondRel` 的 `Disjoint` 部分在交换外两块时同时反转**：
`Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ⟹ Disjoint B A ∧ Disjoint C A ∧ Disjoint C B`。

**⟹ 意义**：这是 `condRel_symm` 能「本体一字不改」的**结构原因**
（对称性只需 `Disjoint.symm`）。 **无任何正性假设。** -/
theorem condRel_disjoint_symm (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) : Disjoint B A ∧ Disjoint C A ∧ Disjoint C B := by
  obtain ⟨hAB, hAC, hBC, _⟩ := h
  exact ⟨hAB.symm, hAC.symm, hBC.symm⟩

/-- ⭐⭐⭐⭐ **§9 反例的逆否形式**：若 `proj p S` **不**满足 `CondIndepN`，
则**任何**「并集恰为 `S`」的三块分解都**不能**给出 `CondRel`。

**⟹ 意义**：这把 §9 的「边缘化不保持条件独立」从**单个反例**提升为
**对全部分块的排除** —— 即 `CondRel` 无法把 §9 的退化情形「包装成」
合法的条件独立关系。**前件是「否定结论的兄弟」而非结论本身。**
**无任何正性假设。** -/
theorem not_condRel_of_not_condIndepN (p : GenC3.NJoint (ι := ι) α γ) (S : Finset ι)
    (h : ¬ GenC3.CondIndepN (proj p S)) :
    ∀ A B C : Finset ι, A ∪ B ∪ C = S → ¬ CondRel p A B C := by
  intro A B C hS hc
  exact h (hS ▸ hc.cond)

/-! ---------------------------------------------------------------------------
  §11  ⭐⭐⭐ `CondRel` 的**分块代数**（本批新增，`R-53`）

  §10 已把对称性升格为 `↔`（`condRel_symm_iff`）并给出「并集不变则关系保留」
  （`condRel_congr_union`）。本节补**分块本身**的算术后果 ——
  这些是 §10 **未覆盖**的：§10 谈「关系 ↔ 关系」，本节谈
  「关系 ⟹ **集合层**的等式 / 排除 / 基数」。

  | 定理 | 内容 |
  |---|---|
  | `condRel_inter_eq_empty` | 两块不交 ⟹ `A ∩ B = ∅`（`Finset` 层的等式形式） |
  | `condRel_disjoint_mono` | 分块**缩小**保持不交（子集封闭） |
  | `condRel_card_add` | 不交 ⟹ `(A ∪ B).card = A.card + B.card` |
  | `condRel_mem_exclusion` | `i ∈ A` ⟹ `i ∉ B` 且 `i ∉ C`（逐点的「一块占位」） |

  ⚠ **诚实标注**：这四条按定义都**只从 `CondRel` 的三个 `Disjoint` 字段出发**
  （**不**触碰 §9 的 `CondIndepN` 障碍），故它们**不是** §3.1 定义的重述：
  定义给的是 `Disjoint A B`（`Prop`-层），本节给的是 `A ∩ B = ∅`
  （`Finset`-层等式）、`⊆`-单调性、`card` 加性、以及逐点排除 ——
  都是**定义之后的**推论，且每条都被 §3.1 的三个字段**联合**驱动。
  无一前件把结论包含在内。
  --------------------------------------------------------------------------- -/

omit [Fintype γ] in
/-- ⭐⭐ **两块不交的 `Finset` 等式形式**：`A ⊥ B | C ⟹ A ∩ B = ∅`。

**⟹ 意义**：`Disjoint` 是 `Prop`-层断言，`∩ = ∅` 是**结构等式**，可直接
`rw`；本引理把它们对接（`Finset.disjoint_iff_inter_eq_empty`）。
**无任何正性假设。** -/
theorem condRel_inter_eq_empty (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) : A ∩ B = ∅ :=
  Finset.disjoint_iff_inter_eq_empty.mp h.disjAB

omit [Fintype γ] in
/-- ⭐⭐⭐ **子集封闭**：把 `A`、`B` 分别缩到子集 `A'`、`B'`，不交仍成立。

$$\bigl(A' \subseteq A\bigr) \wedge \bigl(B' \subseteq B\bigr) \wedge (A \perp B \mid C)
  \Longrightarrow \mathrm{Disjoint}\ A'\ B'.$$

**⟹ 意义**：这是 §10 `condRel_disjoint_symm` 之外唯一常用操作 ——
「删掉一些坐标仍不交」。证明用 `Disjoint.mono`。
**⚠ 注意**：本引理**只推出 `Disjoint A' B'`**，不推出完整 `CondRel p A' B' C'`
（后者需 §9 的 `CondIndepN` 边缘化，而那**不成立**）。这是**刻意**的诚实收窄。 -/
theorem condRel_disjoint_mono (p : GenC3.NJoint (ι := ι) α γ) (A B C A' B' : Finset ι)
    (hA : A' ⊆ A) (hB : B' ⊆ B) (h : CondRel p A B C) : Disjoint A' B' :=
  h.disjAB.mono hA hB

omit [Fintype γ] in
/-- ⭐⭐ **不交 ⟹ 基数加性**：`(A ∪ B).card = A.card + B.card`。

**⟹ 意义**：`CondRel` 的三块是**无重叠分块**，故 `A ∪ B ∪ C` 的基数
是三者之和 —— 这是「把联合律限制到 `A ∪ B ∪ C` 上」时**维度计数**的依据
（§3.1 `proj` 的阶由基数决定）。证明：`Finset.card_union_of_disjoint`。 -/
theorem condRel_card_add (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) : (A ∪ B).card = A.card + B.card :=
  Finset.card_union_of_disjoint h.disjAB

omit [Fintype γ] in
/-- ⭐⭐⭐ **逐点「一块占位」**：`i ∈ A ⟹ i ∉ B` 且 `i ∉ C`。

**⟹ 意义**：这是 `CondRel` 三块**互斥**的**逐点**形式 ——
一个坐标只能属于 `A`、`B`、`C` **之一**。与 `condRel_inter_eq_empty` 相比，
本式给出的是**成员判定**（可直接喂给 `Finset` 的 `mem`-类引理），
且**同时作用于两个 `Disjoint` 字段**（`disjAB` 与 `disjAC`）。
**无任何正性假设。** -/
theorem condRel_mem_exclusion (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) {i : ι} (hiA : i ∈ A) : i ∉ B ∧ i ∉ C := by
  refine ⟨?_, ?_⟩
  · intro hiB
    exact (Finset.disjoint_left.mp h.disjAB hiA) hiB
  · intro hiC
    exact (Finset.disjoint_left.mp h.disjAC hiA) hiC

/-! ---------------------------------------------------------------------------
  §12  ⭐⭐⭐ `CondRel` 分块的**全基数与逐点分类**（本批新增，`R-55`）

  §11 给出四条「分块算术」：`A ∩ B = ∅`、子集封闭、`(A ∪ B).card` 加性、
  以及「`i ∈ A` 的逐点排除」。本节补 §11 **未覆盖**的三块联合性质：

  | 定理 | 内容 | §11 未覆盖的原因 |
  |---|---|---|
  | `condRel_union_card` | **三块**基数相加 | §11 `condRel_card_add` 只到 `A ∪ B` |
  | `condRel_card_union_AB` | `(A∪B∪C).card = (A∪B).card + C.card` | 同上，中间步骤 |
  | `condRel_mem_exclusion_B` | `i ∈ B` ⟹ `i ∉ A ∧ i ∉ C` | §11 只有 `i ∈ A` 的版本 |
  | `condRel_mem_exclusion_C` | `i ∈ C` ⟹ `i ∉ A ∧ i ∉ B` | §11 完全没触及 `C` 侧 |
  | `condRel_mem_union_cases` | `i ∈ A∪B∪C` ⟹ **三分法完全分类** | §11 只是单向排除，没有穷尽性 |

  **⚠ 前件审查（防同义反复）**：全部五条的前件均为 `CondRel p A B C`
  （或再加一个 `i ∈ …` 成员假设），**不含基数、不含成员判定结论**。
  `CondRel` 的定义（`structure`）只给三个 `Disjoint`（`Prop`-层）
  与一条 `CondIndepN`，**既没有 `card` 也没有 `mem`**，
  故结论不能从前件的定义展开中直接读出，必须经 `Disjoint` 的
  消去规则推导。
  `condRel_mem_union_cases` 更是**穷尽性**陈述（∨∨ 三分法），
  需要三条排除引理**联合**，从前件无法直接推出。
  --------------------------------------------------------------------------- -/

omit [Fintype γ] in
/-- ⭐⭐⭐ **三块基数全加**：`|A ∪ B ∪ C| = |A| + |B| + |C|`。

**⟹ 证明**：两次 `Finset.card_union_of_disjoint`。第一次需 `Disjoint (A ∪ B) C`，
后者由 `disjAC` 与 `disjBC` **联合**推出（`Finset.disjoint_iff_ne` 逐点拆开）；
第二次直接用 `disjAB`。**⟹ 意义**：这是 §11 `condRel_card_add`
（只到 `A ∪ B`）的**三块扩展**，是「把联合律限制到 `A ∪ B ∪ C` 上」时
**维度计数**（即 `proj` 的阶）的完整依据。 -/
theorem condRel_union_card (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) :
    (A ∪ B ∪ C).card = A.card + B.card + C.card := by
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_iff_ne]
    intro a ha c hc
    rw [Finset.mem_union] at ha
    rintro rfl
    rcases ha with h' | h'
    · exact (Finset.disjoint_left.mp h.disjAC h') hc
    · exact (Finset.disjoint_left.mp h.disjBC h') hc
  rw [Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint h.disjAB]

omit [Fintype γ] in
/-- ⭐⭐ **`A ∪ B` 与 `C` 的基数分解**：`|A ∪ B ∪ C| = |A ∪ B| + |C|`。

**⟹ 意义**：这是 `condRel_union_card` 的**中间步骤引理**，也是 `C` 侧
（条件集）的**单独计数** —— 在「先固定条件块 `C`，再数 `A ∪ B`」的
推理链里直接用得上。 -/
theorem condRel_card_union_AB (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) : (A ∪ B ∪ C).card = (A ∪ B).card + C.card :=
  Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_iff_ne]
    intro a ha c hc
    rw [Finset.mem_union] at ha
    rintro rfl
    rcases ha with h' | h'
    · exact (Finset.disjoint_left.mp h.disjAC h') hc
    · exact (Finset.disjoint_left.mp h.disjBC h') hc)

omit [Fintype γ] in
/-- ⭐⭐⭐ **从 `B` 侧的逐点排除**：`i ∈ B ⟹ i ∉ A` 且 `i ∉ C`。

**⟹ 与 §11 `condRel_mem_exclusion` 的差别**：后者从 `i ∈ A` 出发，
用的是 `disjAB` 与 `disjAC`；本条从 `i ∈ B` 出发，用的是
`disjAB` **反向**与 `disjBC` —— 是**不同的一对字段**，故不是重述。
**⟹ 意义**：与 §11 的 `A` 侧版本合起来，`A`、`B` 两侧的「占位」
都已单向确立，只差 `C` 侧（下条）。 -/
theorem condRel_mem_exclusion_B (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) {i : ι} (hiB : i ∈ B) : i ∉ A ∧ i ∉ C := by
  refine ⟨?_, ?_⟩
  · intro hiA
    exact (Finset.disjoint_left.mp h.disjAB hiA) hiB
  · intro hiC
    exact (Finset.disjoint_left.mp h.disjBC hiB) hiC

omit [Fintype γ] in
/-- ⭐⭐⭐ **从 `C` 侧的逐点排除**：`i ∈ C ⟹ i ∉ A` 且 `i ∉ B`。

**⟹ 意义**：这是 `C`（**条件集**）侧的「占位」—— §11 与上条都**没有**
触及 `C` 作为出发块的情形。用到的是 `disjAC` 与 `disjBC` 的**反向**。
与 `condRel_mem_exclusion` / `condRel_mem_exclusion_B` 合起来，
三块**三侧**的逐点排除**全部到齐**。 -/
theorem condRel_mem_exclusion_C (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) {i : ι} (hiC : i ∈ C) : i ∉ A ∧ i ∉ B := by
  refine ⟨?_, ?_⟩
  · intro hiA
    exact (Finset.disjoint_left.mp h.disjAC hiA) hiC
  · intro hiB
    exact (Finset.disjoint_left.mp h.disjBC hiB) hiC

omit [Fintype γ] in
/-- ⭐⭐⭐⭐ **并集的逐点三分法**：`i ∈ A ∪ B ∪ C` ⟹ `i` **恰属一块**。

$$i \in A\cup B\cup C \;\Longrightarrow\;
  (i\in A \wedge i\notin B \wedge i\notin C) \;\vee\;
  (i\in B \wedge i\notin A \wedge i\notin C) \;\vee\;
  (i\in C \wedge i\notin A \wedge i\notin B) .$$

**⟹ 证明**：`mem_union` 两次拆开得三支；每支用对应的排除引理
（`condRel_mem_exclusion` / `_B` / `_C`）填出两个 `∉`。
**⟹ 意义**：这是**穷尽性 + 互斥性**的合并陈述 —— §11 的
`condRel_mem_exclusion` 只有「从 `A` 出发的两个 `∉`」，**没有**
「`i` 在并集中则必属且仅属一块」的完全分类。
故本条把「`CondRel` 的三块是无重叠分块」从**逐条排除**升为
**分块归位**（可在 `rcases` 中直接消费）。 -/
theorem condRel_mem_union_cases (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) {i : ι} (hi : i ∈ A ∪ B ∪ C) :
    i ∈ A ∧ i ∉ B ∧ i ∉ C ∨ i ∈ B ∧ i ∉ A ∧ i ∉ C ∨
      i ∈ C ∧ i ∉ A ∧ i ∉ B := by
  rw [Finset.mem_union, Finset.mem_union] at hi
  rcases hi with (hiA | hiB) | hiC
  · obtain ⟨h1, h2⟩ := condRel_mem_exclusion p A B C h hiA
    exact Or.inl ⟨hiA, h1, h2⟩
  · obtain ⟨h1, h2⟩ := condRel_mem_exclusion_B p A B C h hiB
    exact Or.inr (Or.inl ⟨hiB, h1, h2⟩)
  · obtain ⟨h1, h2⟩ := condRel_mem_exclusion_C p A B C h hiC
    exact Or.inr (Or.inr ⟨hiC, h1, h2⟩)

/-! ---------------------------------------------------------------------------
  §12b  ⭐⭐⭐ **§12 的端到端封装**（本批新增，`R-55`，**消费 §12**）
  --------------------------------------------------------------------------- -/

omit [Fintype γ] in
/-- ⭐⭐⭐ **三块计数的合取封装**：`|A∪B∪C|` 的两种分解同时成立。

**⟹ 消费**：`condRel_union_card`（§12）与 `condRel_card_union_AB`（§12）。 -/
theorem condRel_card_three (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) :
    (A ∪ B ∪ C).card = (A ∪ B).card + C.card
      ∧ (A ∪ B ∪ C).card = A.card + B.card + C.card :=
  ⟨condRel_card_union_AB p A B C h, condRel_union_card p A B C h⟩

omit [Fintype γ] in
/-- ⭐⭐⭐ **并集元素的定位**（三分法，直接可 `rcases`）。

**⟹ 消费**：`condRel_mem_union_cases`（§12）。 -/
theorem condRel_locate (p : GenC3.NJoint (ι := ι) α γ) (A B C : Finset ι)
    (h : CondRel p A B C) {i : ι} (hi : i ∈ A ∪ B ∪ C) :
    (i ∈ A ∧ i ∉ B ∧ i ∉ C) ∨ (i ∈ B ∧ i ∉ A ∧ i ∉ C) ∨
      (i ∈ C ∧ i ∉ A ∧ i ∉ B) :=
  condRel_mem_union_cases p A B C h hi

end Semigraphoid

end FateV2.Modeling