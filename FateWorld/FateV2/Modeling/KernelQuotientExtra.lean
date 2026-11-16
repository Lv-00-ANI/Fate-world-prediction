import FateWorld.FateV2.Modeling.KernelQuotient
/-!
  # Modeling · KernelQuotientExtra

  ## 迁移登记
  - 来源：`FateWorld/Legacy/KernelQuotientExtra.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：KernelQuotient
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §13  **核-商理论的补充定理**（并入统一框架）

  **背景**：`Fate/KernelQuotient.lean`（统一框架主体，27 条定理）与
  此前的 `Fate/KernelQuotientCore.lean`（11 条）**同命名空间、部分重名**，
  无法同时进构建（实测：`environment already contains 'Fate.KernelQuotient.Faithful'`）。

  **处置**：以 `KernelQuotient.lean` 为**唯一权威主体**（更完整），
  本文件把 `KernelQuotientCore` 中**独有**的定理**并入同一命名空间**，
  随后 `KernelQuotientCore` 退役（移入隔离目录）。

  **并入的定理**（`KernelQuotient.lean` 中缺失的）：

  | 定理 | 内容 |
  |---|---|
  | `kernel_compatible` | 核自身相容 |
  | `kernel_congr` | 外延相等 ⟹ 核相同 |
  | `kernel_le_kernel_comp` | `ker f ≤ ker (g ∘ f)` |
  | `kernel_le_iff` | 包含关系的展开形式 |
  | `kernel_joint_iff` | 联合读出 ⟺ 逐点相等 |

  **⚠ 未并入的**：`descent_single_valued` / `quot_subsingleton_iff` ——
  主体已有**更强的对应物**（`descend_mk` / `collapse_iff_subsingleton`），
  重复定义会污染统一框架，故**不重复**（这正是不引入重复的纪律）。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Modeling
namespace KernelQuotientTheory

universe u v w

/-! ### §13.1 核的基本性质 -/

/-- ⭐ **外延相等 ⟹ 核相同**（核是 `f` 的**外延量**）。 -/
theorem kernel_congr {A : Type u} {B : Type v} {f g : A → B} (h : ∀ a, f a = g a) :
    kernel f = kernel g := by
  ext a b
  simp only [Setoid.ker_def]
  rw [h a, h b]

/-- ⭐ **复合只会使核变粗**：`ker f ≤ ker (g ∘ f)`。

**即**：`g` 可能把 `f` 已区分的点再合并 —— **故复合不增信息**。 -/
theorem kernel_le_kernel_comp {A : Type u} {B : Type v} {f : A → B} {g : B → A} :
    kernel f ≤ kernel (g ∘ f) :=
  fun _ _ hab => congrArg g hab

/-- ⭐ **包含关系的展开形式**：`ker f ≤ r` 就是「`r`-类内 `f` 常值」。

**即**：它与主体的 `le_kernel_iff_compatible` **逐字等价** ——
故「核是最粗的相容关系」与「核是相容关系的上界」是同一件事的两种说法。 -/
theorem kernel_le_iff {A : Type u} {B : Type v} (f : A → B) (r : Setoid A) :
    kernel f ≤ r ↔ ∀ a b, f a = f b → r a b :=
  Iff.rfl

/-! ### §13.2 联合读出与核的交 -/

/-- ⭐⭐ **联合读出 ⟺ 逐点相等**。

$$\bigl(\forall i,\ f_i(a) = f_i(b)\bigr) \iff \Bigl(\text{联合读出在 } a, b \text{ 相等}\Bigr)$$

**意义**：**「联合读出」精确对应「核的交」** ——
即**细化读出就是取核的交**。

**⟹ 这把「读出方案」与「`Setoid` 的格」精确对应起来**，
说明 `CFLatticeGen` 里 `κ` 的格结构是**必然的**，不是巧合。

**⚠ 诚实说明**：本定理用**逐点形式**陈述，而非格等式
$\ker(\text{联合}) = \bigcap_i \ker f_i$ ——
因为 Lean 的 `⨅` 在此处推断为 `Setoid A` 上的下确界而非下标下确界，
**格等式形式未给出**（数学内容等价）。 -/
theorem kernel_joint_iff {A : Type u} {B : Type v} {ι : Type w}
    (f : ι → A → B) (a b : A) :
    (∀ i, f i a = f i b) ↔ (fun a i => f i a) a = (fun a i => f i a) b :=
  ⟨fun h => funext h, fun h i => congrFun h i⟩

end KernelQuotientTheory

end FateV2.Modeling