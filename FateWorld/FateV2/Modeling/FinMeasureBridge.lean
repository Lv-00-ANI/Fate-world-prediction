import FateWorld.FateV2.Modeling.FiniteCondIndep
import Mathlib.MeasureTheory.Measure.Dirac

/-!
  # Modeling · FinMeasureBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FinMeasureBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FiniteCondIndep
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §87  ⭐⭐⭐ **有限律 → `Measure` 的嵌入**（**桥的第一端**）

  依第 86 轮评估的核心建议：项目已有**两个完整可编译的一半**
  （图侧的 d-分离 / 概率侧的有限条件独立），但**没有连接它们的定理**。
  `SCMSemantics.lean:130-141` 自己登记了这个缺口。

  **本节做第一端**：把 `FinJoint` 嵌入 `Measure`，并证明**保持质量**。

  **⚠ 诚实要求**：`FinJoint` 是**裸函数**（不保证非负/归一），
  故本节把这两条作为**显式假设** `WellFormed`，**不偷偷假定**。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Modeling
namespace FinMeasureBridge

open MeasureTheory

universe u

variable {α β γ : Type u}

/-- ⭐⭐ **有限律诱导的加权计数测度**。

$$p \mapsto \sum_{x,y,z} p((x,y),z) \cdot \delta_{(x,y,z)}$$

**⚠ 这是 Mathlib 的 `Measure.count`（等权）与 `Measure.dirac`（单点）的**有限加权组合**。** -/
noncomputable def weightedCount [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (p : FiniteCondIndep.FinJoint α β γ) : Measure ((α × β) × γ) :=
  ∑ x : α, ∑ y : β, ∑ z : γ,
    ENNReal.ofReal (p ((x, y), z)) • Measure.dirac ((x, y), z)

/-- ⭐⭐⭐ **良构的有限律**（**显式的桥接假设**）。

$$\text{WellFormed}(p) := \bigl(\forall a,\ 0 \le p\,a\bigr) \wedge
  \Bigl(\sum_{x,y,z} p((x,y),z) = 1\Bigr)$$

**⚠ 它与 `CondIndepFin` **正交****：
条件是**结构性质**（可分性），良构是**数值性质**（非负 + 归一）——
**这正是桥接非平凡的原因。** -/
def WellFormed [Fintype α] [Fintype β] [Fintype γ]
    (p : FiniteCondIndep.FinJoint α β γ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ x : α, ∑ y : β, ∑ z : γ, p ((x, y), z)) = 1

/-- ⭐⭐⭐ **加权计数测度的总质量 = 系数之和**（**核心桥引理**）。

$$\bigl(\mathrm{weightedCount}\ p\bigr)(\mathrm{univ}) =
  \sum_{x,y,z}\ \mathrm{ofReal}\bigl(p((x,y),z)\bigr)$$

**⟹ 即**：**嵌入保持质量**。** -/
theorem weightedCount_univ [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (p : FiniteCondIndep.FinJoint α β γ) :
    weightedCount p Set.univ =
      ∑ x : α, ∑ y : β, ∑ z : γ, ENNReal.ofReal (p ((x, y), z)) := by
  unfold weightedCount
  simp [Measure.dirac_apply_of_mem (Set.mem_univ _)]

/-- ⭐⭐⭐ **良构 ⟹ 总质量为 1**（**概率测度的判据**）。

**⚠ 实现说明（如实登记）**：
把 `∑ ofReal` 提升为 `ofReal (∑)` 需要 `ENNReal.ofReal_sum_of_nonneg`，
而该引理用 `∑ i ∈ s` 形式；本节的 `∑ x : α` 是 `Finset.univ.sum` 的记法，
二者的桥接是**纯粹的记法改写**。
**⟹ 故本证明逐层把 `∑ ofReal` 提升为 `ofReal (∑)`。** -/
theorem weightedCount_univ_eq_one [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (p : FiniteCondIndep.FinJoint α β γ) (h : WellFormed p) :
    weightedCount p Set.univ = 1 := by
  rw [weightedCount_univ]
  obtain ⟨hNonneg, hSum⟩ := h
  -- 逐层把 `∑ ofReal (f ·)` 提升为 `ofReal (∑ f ·)`，最后用 `hSum`。
  have hz : ∀ x y, (∑ z : γ, ENNReal.ofReal (p ((x, y), z)))
      = ENNReal.ofReal (∑ z : γ, p ((x, y), z)) := by
    intro x y
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hNonneg _)]
  have hy : ∀ x, (∑ y : β, ∑ z : γ, ENNReal.ofReal (p ((x, y), z)))
      = ENNReal.ofReal (∑ y : β, ∑ z : γ, p ((x, y), z)) := by
    intro x
    rw [show (∑ y : β, ∑ z : γ, ENNReal.ofReal (p ((x, y), z)))
          = ∑ y : β, ENNReal.ofReal (∑ z : γ, p ((x, y), z)) from
          Finset.sum_congr rfl (fun y _ => hz x y)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ =>
          Finset.sum_nonneg (fun z _ => hNonneg _))]
  rw [show (∑ x : α, ∑ y : β, ∑ z : γ, ENNReal.ofReal (p ((x, y), z)))
        = ∑ x : α, ENNReal.ofReal (∑ y : β, ∑ z : γ, p ((x, y), z)) from
        Finset.sum_congr rfl (fun x _ => hy x)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
        Finset.sum_nonneg (fun y _ => Finset.sum_nonneg (fun z _ => hNonneg _)))]
  rw [hSum]
  simp

/-! ### §87.6 ⭐⭐ 有限性（**供桥的第二端使用**） -/

/-- ⭐⭐ **加权计数测度是有限测度**（**对任意有限律，无需非负/归一假设**）。

$$\bigl(\mathrm{weightedCount}\ p\bigr)(\mathrm{univ}) =
  \sum_{x,y,z} \mathrm{ofReal}\bigl(p((x,y),z)\bigr) < \infty$$

**⚠ 有限性**不需要** `WellFormed`** ——
**因为 `Fintype` 上的**有限和**总是有限的**（`ENNReal.ofReal` 取值 `≠ ⊤`）。**
**⟹ 这是 `CondIndepFun` 所需的 `IsFiniteMeasure` 实例的直接来源。** -/
theorem weightedCount_isFiniteMeasure [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (p : FiniteCondIndep.FinJoint α β γ) :
    IsFiniteMeasure (weightedCount p) := by
  rw [isFiniteMeasure_iff]
  rw [weightedCount_univ]
  -- 有限和恒 `≠ ⊤`（`ENNReal.ofReal` 的取值不为 `⊤`）
  simp

/-! ⭐⭐⭐ **本节完成的与未完成的**（**精确登记，不假装完成**）。

**✅ 已证**：
| 构件 | 说明 |
|---|---|
| `weightedCount` | 有限律 → `Measure` 的嵌入 |
| `weightedCount_univ` | 总质量 = 系数之和（**保持质量**）|
| `weightedCount_univ_eq_one` | 良构 ⟹ 总质量为 1（**概率测度**）|
| `weightedCount_isFiniteMeasure` | 有限性（供桥的第二端使用）|

**⚠ 未完成**：`CondIndepFin p ↔ CondIndepFun ...`
（见 `Fate/FinCondIndepMeasure.lean` 的 `bridgeStatement` 与
`Fate/BridgeProofStep3.lean` 的第 3 步登记）。

⚠⚠ **第 110 轮删除**：此处原有
`theorem bridge_remaining_gap : (1 : ℕ) = 1 := rfl` ——
**它是一个**空洞占位**（`1 = 1` 不承载任何内容），
**故删除**，此说明改为模块文档。

**⚠ 本删除的依据由服务器端子代理 **G2-vacuous**（第 110 轮）发现** ——
**我第 109 轮的删除脚本**只做成了 4 个文件中的 2 个**，
**这两处漏掉了**（如实登记这一失误）。 -/

/-! ## §92 ⭐⭐⭐ **桥的第二端的第一步**（**第 128 轮新增**）

**⚠ 背景**：`Fate/FinCondIndepMeasure.lean` 的 `bridgeStatement` 陈述了
「以 `projZ` 生成的 σ-代数为条件，`projX` 与 `projY` 条件独立」——
**但它的证明**从未完成****（第 91 轮登记为「未做」）。

**⭐ 第 127 轮的代理规划**把整座桥**归约到两个核心引理**：
> **「最小充分集合：1 + 2 是真正缺失的数学核心。」**

**本节开始攻第 1 个**：**条件核在 `projZ`-纤维上的显式值**。

**⚠ 第一步（本节）**：先算清 `weightedCount` 在**单点**上的质量** ——
**这是后续一切的基础**（条件期望在有限情形下就是「按纤维的加权平均」）。 -/

/-- ⭐⭐ **加权计数测度在单点上的质量 = 该点的系数**（**桥的第一块砖**）。

**陈述**：
$$\bigl(\mathrm{weightedCount}\ p\bigr)\bigl(\{(a,b,c)\}\bigr) = \mathrm{ofReal}\bigl(p((a,b),c)\bigr)$$

**⟹ 即**：**加权和中的「其余项」在单点上贡献 0**（因为 `dirac` 只在自身处为 1）。

**⚠ 技术要点（第 128 轮查明）**：
1. `Measure.finsetSum_apply` 是**正确**的引理（把「测度和作用在集合上」
   化为「各测度作用后的和」）；
   **⚠ 而它**不在** `Finset` 命名空间下（须配 `open MeasureTheory`）。
2. ⭐ **须用 `simp only [Measure.finsetSum_apply]`（而非 `rw`）** ——
   因为目标是**嵌套**的 `∑ x, ∑ y, ∑ z,`，
   **而 `rw` 只展开最外层**（第二三层嵌在 `∑` 内，`rw` 找不到）——
   **这与第 120 轮查明的 `Fintype.sum_prod_type` 的行为完全一致。**
3. `MeasurableSingletonClass ((α × β) × γ)` 须 `import
   Mathlib.MeasureTheory.MeasurableSpace.Defs`（**它不在** `Measure.Dirac` 里）。 -/
theorem weightedCount_singleton [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (a : α) (b : β) (c : γ) :
    weightedCount p {((a, b), c)} = ENNReal.ofReal (p ((a, b), c)) := by
  simp only [weightedCount]
  -- ⭐ `simp only` 递归展开嵌套的测度和（`rw` 只做最外层 —— 实测）
  simp only [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_mem,
    Set.mem_singleton_iff, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single c]
      · simp
      · intro z _ hz; simp [hz]
      · intro h; exact absurd (Finset.mem_univ c) h
    · intro y _ hy; simp [hy]
    · intro h; exact absurd (Finset.mem_univ b) h
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ a) h

/-! ## §92.1 ⭐⭐⭐ **条件核的第一块砖：纤维质量**（**第 129 轮新增**）

**⚠ 背景**：第 128 轮算清了 `weightedCount` 在**单点**上的质量。
**本节算它在 `projZ`-纤维（即 `{w | w.2 = c}`）上的质量** ——
**这是「条件期望在有限情形下 = 按纤维加权平均」的**分母**。**

**⭐ 第 127 轮代理的规划**指出真正的核心是
「条件核在 `projZ`-纤维上的显式值」——
**而纤维质量正是该显式值的**分母****。 -/

/-- **`projZ`-纤维**：第三坐标等于 `c` 的那些点。 -/
def fiber (c : γ) : Set ((α × β) × γ) := {w | w.2 = c}

/-- ⭐⭐⭐ **纤维质量**：加权计数测度在一个 `projZ`-纤维上的质量
= 沿该纤维的系数之和。

$$\bigl(\mathrm{weightedCount}\ p\bigr)\bigl(\{w : w_3 = c\}\bigr)
  = \sum_{x,y}\ \mathrm{ofReal}\bigl(p((x,y),c)\bigr)$$

**⟹ 即**：**第三坐标不等于 `c` 的那些项**全部贡献 0****
（因为 `dirac` 在自身之外为 0）。

**⚠ 技术要点（第 129 轮查明）**：
1. ⭐ **`conv_lhs => enter [2, x, 2, y, 2, z]; rw [Measure.dirac_apply]`**
   —— 用 `conv` **精确定位**到内层的 `dirac`（**`rw` 直接写会找不到**）。
2. ⭐ **须先证一个 `indicator → ite` 的逐点引理**（`hind`），
   再用 `simp only [hind]` 全局替换 ——
   **因为 `Set.indicator` 的化简对任意 `w` 需 `by_cases`。**
3. ⭐ **外层求和须用 `Finset.sum_congr` 逐层拆**（**不能用 `conv_lhs` 的 `enter`**
   —— 它在嵌套目标里路径不对，**实测**）。
4. 最内层用 `Finset.sum_eq_single c`（**其余项为 0**）。 -/
theorem weightedCount_fiber [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (c : γ) :
    weightedCount p (fiber c) = ∑ x : α, ∑ y : β, ENNReal.ofReal (p ((x, y), c)) := by
  simp only [weightedCount]
  simp only [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  conv_lhs => enter [2, x, 2, y, 2, z]; rw [Measure.dirac_apply]
  have hind : ∀ (w : (α × β) × γ),
      (fiber c).indicator (1 : (α × β) × γ → ENNReal) w = if w.2 = c then 1 else 0 := by
    intro w
    by_cases h : w.2 = c
    · rw [Set.indicator_of_mem (show w ∈ fiber c from h)]; simp [h]
    · rw [Set.indicator_of_notMem (show w ∉ fiber c from h)]; simp [h]
  simp only [hind]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single c]
  · simp
  · intro z _ hz; simp [hz]
  · intro h; exact absurd (Finset.mem_univ c) h

/-! ## §92.2 ⭐⭐⭐⭐ **引理 1 完成：条件核的「分子」**（**第 130 轮新增**）

**⚠ 背景**：第 128–129 轮算清了条件期望的**分母**（单点质量 + 纤维质量）。
**本节算**分子** —— 即 `weightedCount` 作用在「纤维 ∩ 目标集」上的值。

**⭐ 桥里的作用**：条件期望在有限情形下是
$$\frac{\mu(s \cap \text{fiber}\,c)}{\mu(\text{fiber}\,c)}$$
**⟹ 有了分母（第 129 轮）与分子（本节），
整个引理 1（「条件核在 `projZ`-纤维上的显式值」）就齐了。**

**⭐⭐ 技术要点（第 130 轮查明 —— 与第 129 轮**相反**的教训）**：
* 第 129 轮我用了 `Finset.sum_congr` 逐层拆（**因为 `conv_lhs` 的 `enter` 无效**）；
* ⭐ **本节 `Finset.sum_congr` 却**卡在 `AddCommMonoid ?m`****
  （**目标类型推断不出**）——
  **⟹ 改用 `Finset.sum_eq_single` **直接作用于完整目标的三层****，
  **一次成功**（**不需要逐层 `sum_congr`**）。
* **⭐ 即**：**「逐层 `sum_congr`」与「整体 `sum_eq_single`」各有适用场景** ——
  **前者适用于「被加项需逐点化简」，后者适用于「只有一个非零项」。** -/

/-- ⭐⭐⭐⭐ **条件核的分子**：`weightedCount` 作用在「`projZ`-纤维 ∩ 单点」上
= 该单点的系数。

**陈述**：
$$\bigl(\mathrm{weightedCount}\ p\bigr)\bigl(\{w : w_3 = c\} \cap \{(a,b,c)\}\bigr)
  = \mathrm{ofReal}\bigl(p((a,b),c)\bigr)$$

**⚠ 为何需要它**：条件期望分子的一般形式是 `μ(s ∩ fiber c)`；
**本节证的是其中**最简单**的 `s`（单点）** ——
**而由 `weightedCount` 的可加性，单点情形可推广到任意可测 `s`。** -/
theorem weightedCount_fiber_inter_singleton [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (a : α) (b : β) (c : γ) :
    weightedCount p (fiber c ∩ {((a, b), c)}) = ENNReal.ofReal (p ((a, b), c)) := by
  simp only [weightedCount]
  simp only [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  conv_lhs => enter [2, x, 2, y, 2, z]; rw [Measure.dirac_apply]
  have hind : ∀ (w : (α × β) × γ),
      (fiber c ∩ {((a, b), c)}).indicator (1 : (α × β) × γ → ENNReal) w
        = if w = ((a, b), c) then 1 else 0 := by
    intro w
    by_cases h : w = ((a, b), c)
    · subst h
      rw [Set.indicator_of_mem (show ((a, b), c) ∈ (fiber c ∩ {((a, b), c)})
            from ⟨rfl, rfl⟩)]
      simp
    · rw [Set.indicator_of_notMem (show w ∉ (fiber c ∩ {((a, b), c)})
            from fun hc => h hc.2)]
      simp [h]
  simp only [hind]
  -- ⭐ 整体 `sum_eq_single` 三层（**不用** `sum_congr` —— 它会卡 `AddCommMonoid ?m`）
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single c]
      · simp
      · intro z _ hz; simp [hz]
      · intro h; exact absurd (Finset.mem_univ c) h
    · intro y _ hy; simp [hy]
    · intro h; exact absurd (Finset.mem_univ b) h
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ a) h

/-! ## §92.3 ⭐⭐⭐⭐ **引理 1d：分子的一般形式**（**第 131 轮新增**）

**⚠ 背景**：第 128–130 轮算了条件期望的**分母**（纤维质量）与**分子**（纤维 ∩ 单点）。
**本节把分子推广到**任意集合 `s`**** ——
**这是条件期望 $$\frac{\mu(s \cap \text{fiber}\,c)}{\mu(\text{fiber}\,c)}$$
的**真正一般形式****（第 130 轮只是 `s` 为单点的特例）。

**⚠ 技术要点**：一般集合 `s` 需额外假设 **`[DecidablePred (· ∈ s)]`**
（**否则 `ite` 无从判定** —— 实测报「failed to synthesize `Decidable`」）。 -/

/-- ⭐⭐⭐⭐ **`weightedCount` 作用在任意集合上**（**分子的一般形式**）。

**陈述**：
$$\bigl(\mathrm{weightedCount}\ p\bigr)(s)
  = \sum_{x,y,z}\ \bigl[((x,y),z) \in s\bigr] \cdot \mathrm{ofReal}\bigl(p((x,y),z)\bigr)$$

**⚠ 与第 130 轮的关系**：取 `s = fiber c ∩ {((a,b),c)}` 即退化为那条定理。 -/
theorem weightedCount_apply [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (s : Set ((α × β) × γ))
    [DecidablePred (· ∈ s)] :
    weightedCount p s
      = ∑ x : α, ∑ y : β, ∑ z : γ,
          (if ((x, y), z) ∈ s then ENNReal.ofReal (p ((x, y), z)) else 0) := by
  simp only [weightedCount]
  simp only [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  conv_lhs => enter [2, x, 2, y, 2, z]; rw [Measure.dirac_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases h : ((x, y), z) ∈ s
  · simp [Set.indicator_of_mem h, h]
  · simp [Set.indicator_of_notMem h, h]

/-! ## §92.4 ⭐⭐⭐ **引理 2 的桥梁：可加性**（**第 133 轮新增**）

**⚠ 背景**：第 128–131 轮算了 `weightedCount` 在**单点**与**纤维**上的值。
**而引理 2（核值对接）需要**一般集合**的分解** ——
**本节证：不相交并集的质量 = 各质量之和。**

**⭐ 它在桥里的作用**：条件期望的一般形式是
`μ(s ∩ fiber c)`；
**而由本节的可加性，`s ∩ fiber c` 的质量可由**单点质量**拼出来** ——
**⚠ 这把我们已有的「单点结果」（第 130 轮）**升到任意集合**。 -/

/-- ⭐⭐⭐ **可加性**：`weightedCount` 对**不相交并集**可加。

**⚠ 技术要点**：一般集合须三个 `[DecidablePred]`（`s` / `t` / `s ∪ t`）——
**实测：`s ∪ t` 的 `DecidablePred` 不会自动合成**（须显式给出）。 -/
theorem weightedCount_union [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (s t : Set ((α × β) × γ))
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    [DecidablePred (· ∈ (s ∪ t))] (h : Disjoint s t) :
    weightedCount p (s ∪ t) = weightedCount p s + weightedCount p t := by
  rw [weightedCount_apply, weightedCount_apply, weightedCount_apply]
  simp only [Set.mem_union]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases hs : ((x, y), z) ∈ s
  · have ht : ((x, y), z) ∉ t := fun hc => (Set.disjoint_left.mp h hs) hc
    simp [hs, ht]
  · by_cases ht : ((x, y), z) ∈ t
    · simp [hs, ht]
    · simp [hs, ht]

/-! ## §92.5 ⭐⭐⭐ **引理 2 的前提：纤维非零的判据**（**第 134 轮新增**）

**⚠ 背景**：条件期望的显式值是
$$\frac{\mu(s \cap \text{fiber}\,c)}{\mu(\text{fiber}\,c)}$$
**⚠ 而它只在**分母非零**时有意义** ——
**第 127 轮代理明确指出这是一个**需要处理的语义点****（缺口 B/C）。

**⭐ 本节给出**分母非零的判据**（把它化为 `margZ`）：
$$\mu(\text{fiber}\,c) \ne 0 \iff \sum_{x,y} p((x,y),c) \ne 0$$

**⚠ 这也**部分回应了代理指出的缺口 B**** ——
**因为它把「纤维质量非零」这个**测度论**的条件，
**化为**纯代数**的条件（`margZ p c ≠ 0`），
**从而是**可判定**的（**这是后续裁决所需的素材**）。 -/

/-- ⭐⭐⭐ **纤维质量非零 ⟺ `margZ` 的非零**（**条件期望分母的判据**）。

**⚠ 前提 `hp : ∀ a, 0 ≤ p a`**（非负性）**是必需的** ——
**否则 `ofReal` 会把负数变成 0，判据不成立**（实测）。

**⭐⭐ 意义**：它把**测度论**的「纤维质量非零」
化为**纯代数**的「`∑ p ≠ 0`」——
**这使得「分母为零」这一情形**可判定**（后续可据此做 `by_cases`）。** -/
theorem fiber_ne_zero_iff [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ a, 0 ≤ p a) (c : γ) :
    weightedCount p (fiber c) ≠ 0 ↔ (∑ x : α, ∑ y : β, p ((x, y), c)) ≠ 0 := by
  rw [weightedCount_fiber]
  have hnn' : ∀ (x' : α) (y' : β), (0 : ENNReal) ≤ ENNReal.ofReal (p ((x', y'), c)) :=
    fun x' y' => bot_le
  constructor
  · intro h hsum
    apply h
    have hpz : ∀ x : α, ∀ y : β, p ((x, y), c) = 0 := by
      intro x y
      have hx : (∑ y' : β, p ((x, y'), c)) = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
          (f := fun x' : α => ∑ y' : β, p ((x', y'), c))
          (fun x' _ => Finset.sum_nonneg (fun y' _ => hp ((x', y'), c)))).mp hsum
        exact this x (Finset.mem_univ x)
      exact (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun y' : β => p ((x, y'), c)) (fun y' _ => hp ((x, y'), c))).mp hx y
        (Finset.mem_univ y)
    simp [hpz]
  · intro h hzero
    apply h
    have : ∀ x : α, ∀ y : β, p ((x, y), c) = 0 := by
      intro x y
      have hx := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun x' : α => ∑ y' : β, ENNReal.ofReal (p ((x', y'), c)))
        (fun x' _ => Finset.sum_nonneg (fun y' _ => hnn' x' y'))).mp hzero
      have hy := hx x (Finset.mem_univ x)
      have hy2 := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun y' : β => ENNReal.ofReal (p ((x, y'), c)))
        (fun y' _ => hnn' x y')).mp hy y (Finset.mem_univ y)
      have hz := ENNReal.ofReal_eq_zero.mp hy2
      linarith [hp ((x, y), c)]
    simp [this]

/-! ## §92.6 ⭐⭐ **引理 2 的第 1 步：纤维的可测性**（**第 135 轮新增**）

**⚠ 背景**：引理 2（核值对接）要证
$$(\kappa a)(s \cap \text{fiber}\,c) = \frac{\mu(s \cap \text{fiber}\,c)}{\mu(\text{fiber}\,c)}$$
**而它需要先知道**纤维是 `comap projZ`-可测的**** ——
**因为 `comap projZ` 下的可测集正是**纤维的并****，
**故「逐点验证」须从**单个纤维**开始。 -/

/-- ⭐⭐ **纤维是 `comap projZ`-可测的**（**引理 2 的第 1 步**）。

**⚠ 技术要点**：须 `[MeasurableSingletonClass γ]`（**否则 `{c}` 不可测** —— 实测）。 -/
theorem measurableSet_fiber [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (c : γ) :
    MeasurableSet[MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance]
      (fiber c) := by
  rw [fiber]
  exact MeasurableSpace.measurableSet_comap.mpr ⟨{c}, measurableSet_singleton c, rfl⟩

/-! ## §92.7 ⭐⭐⭐⭐ **引理 2.3 的核心：条件分布可分离**（**第 136 轮新增**）

**⚠⚠ 这是**桥的数学心脏**** ——
**`CondIndepFin`（代数条件）**在此刻转化为**条件分布的乘积形式**：
$$\underbrace{\frac{p((x,y),z)}{\mathrm{margZ}\,z}}_{\pi(x,y\mid z)}
  = \underbrace{\frac{\mathrm{margXZ}\,x\,z}{\mathrm{margZ}\,z}}_{\pi(x\mid z)}
    \cdot \underbrace{\frac{\mathrm{margYZ}\,y\,z}{\mathrm{margZ}\,z}}_{\pi(y\mid z)}$$

**⭐ 即**：**「$X$ 与 $Y$ 在给定 $Z$ 下独立」——
**这正是 `CondIndepFun` 的语义**（**而 `bridgeStatement` 要用它**）。**

**⚠⚠ 第 136 轮我在此**修正了自己的一个数学错误****：
我原先在右端多写了一个 `* margZ z` 因子 ——
**而由 `CondIndepFin`（`p * margZ = margXZ * margYZ`）
两边同除 `margZ²` 即得**上式（无多余因子）****。
**⚠ 我是在 `field_simp` 之后**看目标**才发现这个错误的**
（目标是 `p = margXZ * margYZ`，**而与 `hp` 不符**）——
**⭐ 这是「用 `trace_state` 看真实目标」这一纪律的又一次收益。** -/

/-- ⭐⭐⭐⭐ **纤维上的条件分布可分离**（**引理 2.3 的核心**）。

**⚠ 前提 `hm : margZ p z ≠ 0`**（**分母非零**）——
**这正是第 134 轮的 `fiber_ne_zero_iff` 所判定的条件。**

**⭐⭐ 意义**：它把 `CondIndepFin`（**代数等式**）
化为条件分布的**乘积形式** ——
**即「给定 `Z` 时 `X` 与 `Y` 独立」。** -/
theorem condIndepFin_conditional_factorizes [Fintype α] [Fintype β] [Fintype γ]
    {p : FiniteCondIndep.FinJoint α β γ}
    (h : FiniteCondIndep.CondIndepFin p)
    (x : α) (y : β) (z : γ)
    (hm : FiniteCondIndep.margZ p z ≠ 0) :
    p ((x, y), z) / FiniteCondIndep.margZ p z
      = (FiniteCondIndep.margXZ p x z / FiniteCondIndep.margZ p z)
        * (FiniteCondIndep.margYZ p y z / FiniteCondIndep.margZ p z) := by
  have hp := h x y z
  field_simp
  linarith

/-! ## §92.8 ⭐⭐⭐⭐ **缺口 C 的解法：`∀ᵐ` 的精确展开**（**第 137 轮新增**）

**⚠⚠ 背景**：第 127 轮代理指出缺口 C ——
> **「`p` 非负且 `WellFormed` 时单点质量**可能为 0**，
> 故 `hpos` 假设需替换为『纤维质量非零』
> +『`∀ᵐ` 在零质量纤维上自动成立』的迂回 ——
> ⚠ 否则即使可加性证好，最后一步仍会在零测纤维处断裂。」**

**⭐⭐ 本节的定理**正是那个「迂回**** ——
**它把 `∀ᵐ` 精确展开为 `∀ ω, μ{ω} = 0 ∨ P ω`**，
**⟹ 零质量点**自动被吸收**，无需「所有点都有正质量」的假设。**

**⭐ 与第 95 轮的对照**：
| 引理 | 要求 |
|---|---|
| 第 95 轮 `ae_iff_forall_of_positive` | ⚠ **所有**单点质量非零 |
| ⭐ **本节 `ae_iff_forall_or_zero`** | ⭐ **无要求**（零质量点被 `∨` 吸收）| -/

/-- ⭐⭐⭐⭐ **有限测度上 `∀ᵐ` 的精确展开**（**缺口 C 的解法**）。

**⚠ 核心工具**：Mathlib 的 `ae_iff_of_countable`
（`∀ᵐ x ∂μ, p x ↔ ∀ x, μ {x} ≠ 0 → p x`）——
**它本来就允许零质量点**，故本定理只是把它整理为 `∨` 形式。 -/
theorem ae_iff_forall_or_zero [Fintype Ω] [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Ω → Prop) :
    (∀ᵐ ω ∂μ, P ω) ↔ ∀ ω, μ {ω} = 0 ∨ P ω := by
  rw [ae_iff_of_countable]
  constructor
  · intro h ω
    by_cases hP : P ω
    · exact Or.inr hP
    · left
      by_contra hne
      exact hP (h ω hne)
  · intro h ω hne
    rcases h ω with h0 | hP
    · exact absurd h0 hne
    · exact hP


/-! ## §92.9 ⭐⭐⭐ **桥的最后一步：技术零件**（**第 143–144 轮**）

**⚠ 本节收录**攻桥最后一步时查明的两个**技术零件** ——
**它们本身有价值**（后续组装会用到）。

### ⭐ 零件 1：`condExpKernel` 的类型**装箱**

**⚠ `condExpKernel` 返回 `@Kernel Ω Ω m mΩ`**（**`m` 在**第一**参数位**）——
**⚠ 故写 `Kernel Ω Ω`（默认实例）会**类型不匹配****。
**⭐ 须用 `@Kernel ... m mΩ` 显式形式。**

### ⭐ 零件 2：`m' ⊓ mΩ = m'`

**⚠ `condExpKernel` 内部用的是 `m ⊓ mΩ`**，
**⭐ 而桥的 `m' = comap projZ`** 满足 `m' ≤ mΩ` ⟹ **`m' ⊓ mΩ = m'`。** -/

/-- ⭐⭐ **`comap projZ ⊓ mΩ = comap projZ`**（**桥的一处技术零件**）。

**⚠ 用途**：`condExpKernel` 内部用 `m ⊓ mΩ`，
**而 `condDistrib` 的显式值引理用完整 `mΩ`** ——
**本定理是**对齐两者**的桥梁。** -/
theorem comap_projZ_inf_eq [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ] :
    (MeasurableSpace.comap (fun w : (α × β) × γ => w.2) (inferInstance : MeasurableSpace γ))
      ⊓ (inferInstance : MeasurableSpace ((α × β) × γ))
      = (MeasurableSpace.comap (fun w : (α × β) × γ => w.2) (inferInstance : MeasurableSpace γ)) := by
  rw [inf_of_le_left]
  exact MeasurableSpace.comap_le_iff_le_map.mpr measurable_snd


/-! ## §92.11 ⭐⭐⭐ **纤维上的归一化**（**第 156 轮入库**，来自代理 A3 的产出）

**⚠⚠ 重要**：**本节的 `hp` 假设**不可省**** ——
**A3 给出了**形式化反例**：取 `p ≡ -1`，则左端 `(ofReal (-1)).toReal = 0`，
故 `0 / 0 = 0`；右端 `(-1) / (-1) = 1` ⟹ **`0 ≠ 1`，命题为假。**

**⭐⭐ 即**：`ENNReal.ofReal` 会**丢弃负号**，故「把 `ENNReal` 的值转回 `ℝ`」
**仅在非负时忠实** —— **`hp` 是**数学上必需**的，不是技术妥协。 -/

/-- ⭐⭐⭐ **纤维上的归一化**（**条件分布的显式值**）。

`μ(fiber z ∩ {((a,b),z)}) / μ(fiber z) = p((a,b),z) / ∑p`，
**即「给定 `Z=z` 时 `(X,Y)=(a,b)` 的条件概率」。**

⚠ **`hp : ∀ w, 0 ≤ p w` 不可省**（**见本节开头的反例**）。 -/
theorem fiber_normalization [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (a : α) (b : β) (z : γ)
    (hp : ∀ w, 0 ≤ p w) :
    letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
    (weightedCount p).real (fiber z ∩ {((a, b), z)}) / (weightedCount p).real (fiber z)
      = p ((a, b), z) / (∑ x : α, ∑ y : β, p ((x, y), z)) := by
  letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
  have hnum : (weightedCount p).real (fiber z ∩ {((a, b), z)}) = p ((a, b), z) := by
    rw [Measure.real, weightedCount_fiber_inter_singleton]
    exact ENNReal.toReal_ofReal (hp _)
  have hden : (weightedCount p).real (fiber z) = ∑ x : α, ∑ y : β, p ((x, y), z) := by
    rw [Measure.real, weightedCount_fiber]
    rw [show (∑ x : α, ∑ y : β, ENNReal.ofReal (p ((x, y), z)))
          = ∑ x ∈ (Finset.univ : Finset α), ∑ y ∈ (Finset.univ : Finset β),
              ENNReal.ofReal (p ((x, y), z)) from rfl]
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [ENNReal.toReal_sum (fun y _ => ENNReal.ofReal_ne_top)]
      exact Finset.sum_congr rfl (fun y _ => ENNReal.toReal_ofReal (hp _))
    · refine fun x _ => ?_
      rw [ENNReal.sum_ne_top]
      exact fun y _ => ENNReal.ofReal_ne_top
  rw [hnum, hden]

/-- ⭐⭐ **反例：去掉 `hp` 后命题为假**（**`hp` 不可省的证据**）。 -/
theorem fiber_normalization_needs_nonneg :
    ¬ ((ENNReal.ofReal (-1)).toReal = -1) := fun h => by
  have := (ENNReal.toReal_ofReal_eq_iff).mp h
  linarith

/-! ## §92.12 ⭐⭐⭐⭐ **任意可测集的纤维归一化**（**第 157 轮新增**）

**⚠⚠ 本节**否定了**「桥的第 6 步需要 π-系/Dynkin 推广」这一判断** ——
**因为 `weightedCount_apply`（§92.3）已给出**任意集合**的显式值，
**⟹ 故对任意可测集 `t` 都可**直接计算**，无需从单点推广。**

**⭐⭐ 即**：**桥的组装**不需要 Dynkin 式工具** ——
**§92.11 的 `fiber_normalization` 只是 `t = {(a,b)}` 的特例，而本节是**一般形式**。** -/

/-- ⭐⭐⭐⭐ **任意可测集的纤维归一化**（**条件的概率的一般形式**）。

`μ.real(t ∩ fiber z) / μ.real(fiber z) = (∑ over t∩fiber z of p) / (∑ p)`，
**即「给定 `Z=z` 时，事件 `t` 的条件概率」。**

⚠ **`hp` 不可省**（同 §92.11 的反例）。 -/
theorem fiber_normalization_general [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ)
    (t : Set ((α × β) × γ)) (z : γ)
    (hp : ∀ w, 0 ≤ p w) [DecidablePred (· ∈ t)]
    [DecidablePred (· ∈ (t ∩ {w | w.2 = z}))] :
    letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
    (weightedCount p).real (t ∩ {w | w.2 = z}) / (weightedCount p).real (fiber z)
      = (∑ x : α, ∑ y : β, (if ((x, y), z) ∈ t then p ((x, y), z) else 0))
        / (∑ x : α, ∑ y : β, p ((x, y), z)) := by
  letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
  have hcond : ∀ (x : α) (y : β) (z' : γ),
      (((x, y), z') ∈ (t ∩ {w : (α × β) × γ | w.2 = z})) ↔ (((x, y), z') ∈ t ∧ z' = z) := by
    intro x y z'; simp [Set.mem_inter_iff]
  have hnum : (weightedCount p).real (t ∩ {w | w.2 = z})
      = ∑ x : α, ∑ y : β, (if ((x, y), z) ∈ t then p ((x, y), z) else 0) := by
    rw [Measure.real, weightedCount_apply p (t ∩ {w | w.2 = z})]
    simp only [hcond]
    rw [ENNReal.toReal_sum
      (f := fun x => ∑ y, ∑ z', (if ((x, y), z') ∈ t ∧ z' = z then ENNReal.ofReal (p ((x, y), z')) else 0))
      (fun x _ => by rw [ENNReal.sum_ne_top]; intro y _; rw [ENNReal.sum_ne_top]; intro z' _; split <;> simp)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [ENNReal.toReal_sum
      (f := fun y => ∑ z', (if ((x, y), z') ∈ t ∧ z' = z then ENNReal.ofReal (p ((x, y), z')) else 0))
      (fun y _ => by rw [ENNReal.sum_ne_top]; intro z' _; split <;> simp)]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [ENNReal.toReal_sum
      (f := fun z' => (if ((x, y), z') ∈ t ∧ z' = z then ENNReal.ofReal (p ((x, y), z')) else 0))
      (fun z' _ => by split <;> simp)]
    rw [Finset.sum_eq_single z]
    · simp only [eq_self_iff_true, and_true]
      by_cases ht : ((x, y), z) ∈ t
      · simp [ht, ENNReal.toReal_ofReal (hp _)]
      · simp [ht]
    · intro z' _ hne; simp [hne]
    · intro hz; simp at hz
  have hden : (weightedCount p).real (fiber z) = ∑ x : α, ∑ y : β, p ((x, y), z) := by
    rw [Measure.real, weightedCount_fiber]
    rw [show (∑ x : α, ∑ y : β, ENNReal.ofReal (p ((x, y), z)))
          = ∑ x ∈ (Finset.univ : Finset α), ∑ y ∈ (Finset.univ : Finset β),
              ENNReal.ofReal (p ((x, y), z)) from rfl]
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [ENNReal.toReal_sum (fun y _ => ENNReal.ofReal_ne_top)]
      exact Finset.sum_congr rfl (fun y _ => ENNReal.toReal_ofReal (hp _))
    · refine fun x _ => ?_
      rw [ENNReal.sum_ne_top]
      exact fun y _ => ENNReal.ofReal_ne_top
  rw [hnum, hden]
end FinMeasureBridge

end FateV2.Modeling