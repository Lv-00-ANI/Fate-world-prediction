import FateWorld.FateV2.Predict.Assembly
/-!
  # Predict · NLegAssembly

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NLegAssembly.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Assembly
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §57  ⭐⭐ **n 腿组装的核理论**（推广 `Fate/Assembly.lean` 的 2 腿情形）

  ## 背景

  **`Fate/Assembly.lean`**（§7）处理「四 + 甲」的 **2 腿组装**：
  $$\mathrm{obsJoint}\,f\,g := \lambda s.\ (f\,s, g\,s) : \mathrm{SCM} \to A \times B$$
  并证 $\ker(\mathrm{obsJoint}\,f\,g) = \ker f \sqcap \ker g$。

  **⚠ 但「组装」在实际上可以有**任意多条腿**** ——
  **（方向层 + 函数层 + 观测层 + 干预层 + …）**

  ## 本节的目标

  **把 2 腿推广到**任意有限条腿**（`Fin n`），且**与 2 腿情形完全一致**。

  ## ⭐⭐ 核心结论

  $$\ker(\mathrm{joint}_n\,\mathbf{f}) = \bigsqcap_{i \in \mathrm{Fin}\,n} \ker(f_i)$$

  **即**：**n 腿组装的可识别性 = 各腿可识别性之交** ——
  **「每条腿堵一个自由度，全部合起来就是完全识别」。**

  ## ⭐ 为何这是真正的推广

  | 项 | `Assembly`（2 腿） | 本节（n 腿） |
  |---|---|---|
  | 组装泛函 | `SCM → A × B` | `SCM → (∀ i, F i)` |
  | 核 = 交 | $\ker f \sqcap \ker g$ | $\bigsqcap_i \ker(f_i)$ |
  | **单调性** | 无 | ⭐ **加腿只会更细** |

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace NLegAssembly

universe u v w

variable {SCM : Type u}

/-! ### §57.1 ⭐⭐ n 腿组装泛函 -/

/-- ⭐⭐ **n 腿组装泛函**：把 SCM 送到「全部腿的读数」的元组。

$$\mathrm{joint}_n\,\mathbf{f}\,s := \lambda i.\ f_i\,s$$

**⚠ 这是 `Assembly.obsJoint` 的**任意有限腿**推广**
（取 $n = 2$ 时与 `obsJoint` 同构）。 -/
def joint {n : ℕ} {F : Fin n → Type v} (f : ∀ i, SCM → F i) :
    SCM → (∀ i, F i) :=
  fun s i => f i s

/-- ⭐⭐ **主定理：n 腿组装的核 = 各腿核之交**（`∀` 形式，避免 `iInf` 的展开障碍）。

$$(\mathrm{joint}_n\,\mathbf{f}\,a = \mathrm{joint}_n\,\mathbf{f}\,b) \iff
  \forall i,\ f_i\,a = f_i\,b$$

**⟹ 即**：**「每条腿堵一个自由度，合起来是完全识别」的精确形式。**

**⚠ 这是 `Assembly.joint_kernel_eq_inter` 的**任意有限腿**推广。** -/
theorem joint_kernel_eq_all {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) (a b : SCM) :
    (joint f a = joint f b) ↔ ∀ i, f i a = f i b := by
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

/-- ⭐⭐ **主定理（下界形式）**：n 腿组装的核 $\le$ 每条腿的核。

$$\ker(\mathrm{joint}_n\,\mathbf{f}) \le \ker(f_i) \quad (\forall i)$$

**⟹ 即**：**组装不会比任何单腿更粗** ——
**这是「n 腿核 = 各腿核之交」的一半，且**无需 `iInf`** 即可陈述。** -/
theorem joint_kernel_le_each {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) (i : Fin n) :
    Setoid.ker (joint f) ≤ Setoid.ker (f i) :=
  fun a b hab => (joint_kernel_eq_all f a b).mp hab i

/-- ⭐⭐ **主定理（完整形式）**：n 腿组装的核恰是「全部腿的核之交」。

$$\ker(\mathrm{joint}_n\,\mathbf{f}) = \bigsqcap_i \ker(f_i)$$

**⚠ 实现说明**：`Setoid` 层的 `⨅` 在 `ext` 后不自动展开为 `∀`，
**故本节以「下界 + 上界」两条给出**（合起来即完整等式）：

* **`joint_kernel_le_each`**：$\ker(\mathrm{joint}) \le \ker(f_i)$（对每个 $i$）
* **`joint_kernel_ge_of_all`**：若 $r \le \ker(f_i)$ 对**每个** $i$ 成立，则 $r \le \ker(\mathrm{joint})$

**⟹ 即**：**「核 = 交」的精确内容已完整给出，且不依赖 `iInf` 的展开。** -/
theorem joint_kernel_ge_of_all {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) {r : Setoid SCM}
    (h : ∀ i, r ≤ Setoid.ker (f i)) :
    r ≤ Setoid.ker (joint f) :=
  fun a b hab => (joint_kernel_eq_all f a b).mpr fun i => h i hab

/-! ### §57.2 ⭐⭐ 可识别性的单调性 -/

/-- ⭐⭐ **加腿只会更细**（**新结论，2 腿情形没有**）。

**陈述**：若腿集 $I \subseteq J$，则
$$\ker(\mathrm{joint}_J) \subseteq \ker(\mathrm{joint}_I)$$

**即**：**腿越多，可识别性越强**（等价越细）。

**⟹ 即**：**「组装单调性」** ——
**这是 n 腿推广带来的**实质新内容****
（2 腿情形无法表达「加第三条腿」这件事）。 -/
theorem joint_kernel_mono {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) (I J : Set (Fin n)) (hIJ : I ⊆ J) :
    Setoid.ker (fun s : SCM => fun i : J => f i.1 s) ≤
      Setoid.ker (fun s : SCM => fun i : I => f i.1 s) := by
  intro a b hab
  funext ⟨i, hi⟩
  exact congrFun hab ⟨i, hIJ hi⟩

/-! ### §57.3 ⭐⭐ 完全识别判据 -/

/-- ⭐⭐ **完全识别 = 所有腿的核之交是离散的**。

$$\mathrm{joint}_n\,\mathbf{f}\ \text{单射} \iff
  \bigsqcap_i \ker(f_i) \le \bot$$

**⟹ 即**：**「组装完全识别」的精确判据** ——
**所有腿合起来能把任意两个不同的 SCM 分开。** -/
theorem joint_injective_iff {n : ℕ} {F : Fin n → Type v}
    (f : ∀ i, SCM → F i) :
    Function.Injective (joint f) ↔ ∀ a b, (∀ i, f i a = f i b) → a = b := by
  constructor
  · intro h a b hab
    exact h ((joint_kernel_eq_all f a b).mpr hab)
  · intro h a b hab
    exact h a b ((joint_kernel_eq_all f a b).mp hab)

/-- ⭐⭐ **组装三分法**（推广 `Assembly.assembly_trichotomy`）。

**陈述**：n 腿组装在任意 `F : Set SCM` 上**必居**三情形之一：
塌缩 / 忠实 / 中间。

**⟹ 即**：**`Assembly` 的三分法**无条件**推广到 n 腿。** -/
theorem joint_trichotomy {n : ℕ} {F : Fin n → Type v}
    (obs : ∀ i, SCM → F i) (S : Set SCM) :
    (∀ a ∈ S, ∀ b ∈ S, joint obs a = joint obs b) ∨
      (∀ a ∈ S, ∀ b ∈ S, joint obs a = joint obs b → a = b) ∨
      (¬ (∀ a ∈ S, ∀ b ∈ S, joint obs a = joint obs b) ∧
        ¬ (∀ a ∈ S, ∀ b ∈ S, joint obs a = joint obs b → a = b)) := by
  by_cases hc : ∀ a ∈ S, ∀ b ∈ S, joint obs a = joint obs b
  · exact Or.inl hc
  · by_cases hf : ∀ a ∈ S, ∀ b ∈ S, joint obs a = joint obs b → a = b
    · exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inr ⟨hc, hf⟩)

/-! ### §57.4 ⭐⭐ 两条腿的实例回收（与 `Assembly` 一致） -/

/-- ⭐⭐ **2 腿情形与 `Assembly` 一致**（**推广的正确性验证**）。

**陈述**：取 $n = 2$ 且 $A = B$ 时，本节 `joint` 为 `SCM → Fin 2 → A`，
其核恰是两条腿核之交。

**⟹ 即**：**本推广**真正包含**原情形**（不是另起炉灶）。** -/
theorem two_leg_agrees {A : Type} (f g : SCM → A) :
    Setoid.ker (joint (fun i : Fin 2 => if i = 0 then f else g)) =
      Setoid.ker f ⊓ Setoid.ker g := by
  ext a b
  constructor
  · intro h
    exact ⟨(joint_kernel_eq_all _ a b).mp h 0, (joint_kernel_eq_all _ a b).mp h 1⟩
  · intro ⟨h0, h1⟩
    exact (joint_kernel_eq_all _ a b).mpr (fun i => by
      fin_cases i
      · exact h0
      · exact h1)

end NLegAssembly

end FateV2.Predict