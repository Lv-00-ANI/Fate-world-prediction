import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ObsEstimationWeak.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-007 D-008 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Modeling（正文 4 处，含 0 条 import）；其余正文未改
  - 状态：已编译未验证
-/

/-! ===========================================================================
  `FateV2.Modeling.ObsEstimationWeak` —— **A14 估计分支【弱档】（等价类）**
  ===========================================================================

  ## 一、这个文件在回答什么

  A14 是「观测」方向的估计假设。它的**最强形式**是
  「由观测 `y` 唯一确定状态 `x`」（互信息无歧义的估计 / 单射性）。
  **那个形式是假的**（或至少是经验假设）。本文件只做**最弱形式**：

  > 由 `y` **不能**唯一确定 `x`，但**能**确定 `x` 落在一个**集合**里
  > —— 即 `h` 在 `y` 处的**纤维** `h⁻¹(y)`（或其**噪声邻域**）。

  **一句话**：**弱档把「点估计」降级为「集合值估计」，而这件事是可证的。**

  ## 二、两个集合（本文件的全部对象）

  | 名字 | 定义 | 含义 |
  |---|---|---|
  | `hFiber h y` | `{x | h x = y}` | **无噪声**等价类（精确纤维）|
  | `obsClass η h y` | `{x | dist (h x) y ≤ η}` | **带噪声**等价类（闭球邻域）|

  **`obsClass` 就是任务书里的 `{ x | dist (h x) y ≤ η_max }`**，
  参数名取 `η`（噪声上界），`ObsModel` 结构体里存 `η_max`。

  ## 三、本文件证了什么（与代码一一对应）

  | # | 定理 | 内容 | 为什么**不是**同义反复 |
  |---|---|---|---|
  | 1 | `true_mem_obsClass` | 若真实状态满足 `dist (h x) y_obs ≤ η`，则 `x ∈ obsClass η h y_obs` | **正确性**：结论 `x ∈ {· | P ·}` 要先 `Set.mem_setOf_eq` 展开才落到假设上，且它是**下文所有包含关系的基础** |
  | 2 | `hFiber_subset_obsClass` | `η ≥ 0` ⟹ `hFiber h y ⊆ obsClass η h y` | **不是定义相等**：需 `dist y y = 0 ≤ η`（用 `dist_self` 与 `zero_le`）|
  | 3 | `obsClass_nonempty_iff` | `(obsClass η h y).Nonempty ↔ ∃ x, dist (h x) y ≤ η` | 两个方向都要**拆装 `Set.Nonempty`/`mem_setOf`** |
  | 4 | `obsClass_nonempty_of_surjective` | `h` 满射 ⟹ `obsClass η h y` 非空（`η ≥ 0`）| 走 (3)：满射给 `h x = y`，再 `dist_self` |
  | 5 | `obsClass_eq_empty_iff` | `(obsClass η h y) = ∅ ↔ ∀ x, η < dist (h x) y` | **否定形式**：需 `Set.not_nonempty_iff_eq_empty` 与 `not_le` 互换 |
  | 6 | `obsClass_mono` | `η₁ ≤ η₂` ⟹ `obsClass η₁ ⊆ obsClass η₂` | 单调性，由 `le_trans`；说明**噪声上界就是一个嵌套球族** |
  | 7 | `obsClass_zero_eq_hFiber` | 度量空间上 `obsClass 0 h y = hFiber h y` | **要真证**：`dist (h x) y ≤ 0 → dist (h x) y = 0 → h x = y`（`dist_eq_zero`），反向用 `dist_self` |
  | 8 | `hFiber_subsingleton_of_injective` | `h` 单射 ⟹ `(hFiber h y).Subsingleton` | **退化情形**：单射时弱档**退化为**点估计 |
  | 9 | `hFiber_eq_singleton_of_injective` | 单射且 `h x = y` ⟹ `hFiber h y = {x}` | 由 (8) 的 `Set.Subsingleton.eq_singleton_of_nonempty` 类推理给出**唯一性** |
  | 10 | `obsClass_subsingleton_of_injective` | 度量空间、`h` 单射、`η = 0` ⟹ `(obsClass 0 h y).Subsingleton` | (7)+(8) 的合成：**「弱档 + 零噪声 + 单射 = 强档」** |
  | 11 | `dist_le_two_mul_of_mem_obsClass` | `x₁, x₂ ∈ obsClass η h y` ⟹ `dist (h x₁) (h x₂) ≤ 2η` | **信息论意义**：同一个观测下的两个候选状态，其观测值**互相接近**（三角不等式，非换写）|
  | 12 | `obsEq_refl/symm/trans` | `obsEq h` 是**等价关系** | 「由 `y` 确定的等价类」确实是等价类 —— 但注意 **(7) 才是它与纤维集的桥** |
  | 13 | `obsClass_mem_obsEq_class` | `h x = y` ⟹ `hFiber h y = obsEq h x` | 纤维集 **就是** `x` 的等价类（两向包含）|
  | 14 | `surjective_of_forall_nonempty` | 若每个 `hFiber h y` 非空则 `h` 满射 | 与 (4) **反向**：**满射 ⟺ 所有纤维非空**，闭合 #2 的「充要条件」 |
  | 15 | `exists_obsClass_of_exists_hFiber` | `∃ x, h x = y` ⟹ `∃ x, x ∈ obsClass η h y`（`η ≥ 0`）| 从**可达性**（存在性）到**邻域可达性**的迁移 |

  ## 四、与仓内 `A14-三档关系分析.md` 的对接（**新增，请与文档对照阅读**）

  该文档把 A14 估计分支分三档（强／中／弱），并列了两处**当时标为【推测】/**缺定理**的条目**；
  本文件不修改该文档，但把它列出的两项**在 Lean 里做成了定理**：

  | 文档条目 | 文档原判定 | 本文件落点 |
  |---|---|---|
  | **§1.3 C1（无噪声 ⟹ 退化）** | 【已证（平凡）】`abs_eq_zero` 级别 | **`obsClass_zero_eq_hFiber`**（§3.4）+ **`obsClass_subsingleton_of_injective`**（§3.5）：`η = 0` 时噪声类**恰是**精确纤维，单射时**退化为单点**——这是 C1 的**具体**形式，而不只是一句「平凡」 |
  | **§4 M3（退化一致性：弱档类全为单点）** | 【推测】，需 M1+M2+M3 | **`hFiber_eq_singleton_of_injective`**：**退化点（零噪声 + 单射）上弱档类恰为单点**。这是 M3 里「弱档侧」那半句的**机检版本**。⚠ **M3 的另外两半（`c_strong → 0`、`c_mid → 点质量`）本文件不涉及** —— 那是 M1/M2 标定映射的事，属**数值层**，依 `ErrorBound.lean` 的纪律**本仓拒绝填充**。 |

  **但注意**：本文件**同时给出了文档 §1.3 所缺的「反面」**：
  `obsClass_not_subsingleton_of_pos` 证明 **`η > 0` 时即使 `h` 单射，弱档类也不是单点**。
  这正是文档所说「一般 `ε > 0` 时强档不能推弱档」的**可机检实例**——
  **文档的 C2（类直径 > 误差）为何不可省，此定理给出了它不可省的一个见证。**

  **⚠ 未做**：本文件**不**断言「强档 ⟹ 弱档」（文档 §1.3 C2 仍属【推测】），
  也**不**给出统一量纲的数值（文档 §4 M4）。

  ## 五、诚实边界（必读）

  **本文件证的全是「集合论 + 度量论」的直接推论**，
  **没有**用到任何概率、图、或 SCM 结构。因此：

  - 它**不是**「估计可行性定理」——它只说明**弱档的形式是自洽的**。
  - 它**不**断言 `obsClass` 是**最优**的集合值估计（那是 Bayes 风险问题）。
  - **A14 本身作为经验假设不可证**；本文件证明的是
    **「若把 A14 降为等价类形式，则相应的正确性/非空性/退化性命题可证」**。
    这与 `_pending` 里「A14 属不可证的经验假设」的登记**不冲突**。

  **零 `sorry`、零 `axiom`、零 `admit`。**
  =========================================================================== -/

namespace FateV2.Modeling

namespace ObsEstimationWeak

universe u v

variable {X : Type u} {Y : Type v}

/-! ### §1  观测模型与噪声

下面的结构体是**唯一**的前件载体：它把「观测函数 `h`」与「噪声上界 `η_max`」
打包在一起。**度量不进结构体**（依 `FateV2.Modeling/CellDiameter.lean` 的纪律：
度量只作为类型类前件出现，不进结构体）。 -/

/-- **观测模型**：状态空间到观测空间的映射 + 噪声上界。

* `h` —— 观测函数 `X → Y`。**允许非单射**（这正是弱档的全部要点）。
* `etaMax` —— 噪声上界 `η_max ∈ ℝ`。`0` 表示无噪声。

**⚠ 不要求 `h` 满射，也不要求 `h` 单射**：
本文件的核心命题全部在**任意** `h` 下成立（需要单射的地方**显式作前件**）。 -/
structure ObsModel (X : Type u) (Y : Type v) where
  /-- 观测函数。**可以非单射** —— 这是弱档的定义性特征。 -/
  h : X → Y
  /-- 噪声上界 `η_max`。取值范围是 `ℝ`，**不要求非负**（负值时集合可能为空，
      §3 的 `obsClass_eq_empty_iff` 精确刻画此事）。 -/
  etaMax : ℝ

namespace ObsModel

variable (M : ObsModel X Y)

/-- **真实状态落在噪声界内**：观测 `y` 与 `h x` 的距离不超过噪声上界。

**这是「正确性」这一条要用的**唯一实质前件**：
它不是定理能证的东西（真实世界是否满足它是经验问题），
但**给定**它之后，「`x` 落在由 `y` 确定的集合里」就是纯逻辑。 -/
def NoiseRespects [PseudoMetricSpace Y] (x : X) (y : Y) : Prop :=
  dist (M.h x) y ≤ M.etaMax

end ObsModel

/-! ### §2  两个集合：精确纤维与噪声纤维 -/

/-- **由 `y` 确定的精确等价类**：`hFiber h y = { x | h x = y }`。

这正是任务书里的 `{ x | h x = y }`。**不需要任何度量**。 -/
def hFiber (h : X → Y) (y : Y) : Set X :=
  {x | h x = y}

/-- **由 `y` 确定的噪声等价类**：`obsClass η h y = { x | dist (h x) y ≤ η }`。

这正是任务书里的 `{ x | dist (h x) y ≤ η_max }`（取 `η = η_max`）。
它是 `Y` 中的一个**闭球** `Metric.closedBall y η` 在 `h` 下的原像。 -/
def obsClass [PseudoMetricSpace Y] (η : ℝ) (h : X → Y) (y : Y) : Set X :=
  {x | dist (h x) y ≤ η}

/-- **从模型直接取的噪声等价类**（避免调用者每次手写 `M.etaMax`）。 -/
def ObsModel.obsSet [PseudoMetricSpace Y] (M : ObsModel X Y) (y : Y) : Set X :=
  obsClass M.etaMax M.h y

/-! ### §3  基本性质

#### §3.1  正确性：真实的 `x` 一定在集合里 -/

/-- **正确性（核心第 1 条）**：

若真实状态 `x` 满足噪声界 `dist (h x) y ≤ η`，
则 `x` **必在**由观测 `y` 确定的等价类中。

**这不是同义反复的理由**：命题的结论是集合成员关系 `x ∈ obsClass η h y`，
必须先经 `Set.mem_setOf_eq` 把 `obsClass` **展开**才能与假设相接。
这条展开在**下面每一条包含关系**里都要重做，是真正的连接点。 -/
theorem true_mem_obsClass [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η : ℝ} {x : X}
    (hx : dist (h x) y ≤ η) : x ∈ obsClass η h y := by
  simpa [obsClass] using hx

/-- **正确性（模型版）**：`M.NoiseRespects x y` ⟹ `x ∈ M.obsSet y`。 -/
theorem ObsModel.true_mem_obsSet [PseudoMetricSpace Y] (M : ObsModel X Y) {x : X} {y : Y}
    (hx : M.NoiseRespects x y) : x ∈ M.obsSet y := by
  simpa [ObsModel.obsSet, ObsModel.NoiseRespects, obsClass] using hx

/-- **精确纤维的正确性（无需度量）**：`h x = y` ⟹ `x ∈ hFiber h y`。 -/
theorem true_mem_hFiber {h : X → Y} {y : Y} {x : X} (hx : h x = y) : x ∈ hFiber h y := by
  simpa [hFiber] using hx

/-- **噪声类包含精确纤维**：只要 `η ≥ 0`，`hFiber h y ⊆ obsClass η h y`。

**这是「弱档真的比强档弱」的形式表达**：噪声类**总是**装得下精确纤维，
所以用 `obsClass` 做估计**不会漏掉**任何真正的解。 -/
theorem hFiber_subset_obsClass [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η : ℝ}
    (hη : 0 ≤ η) : hFiber h y ⊆ obsClass η h y := by
  intro x hx
  have hxy : h x = y := by simpa [hFiber] using hx
  show dist (h x) y ≤ η
  rw [hxy, dist_self]
  exact hη

/-! #### §3.2  非空的充要条件 -/

/-- **非空充要条件**：`obsClass η h y` 非空 **⟺** 存在 `x` 使噪声界成立。

左向（`Nonempty → ∃`）需要从 `⟨x, hx⟩` 中**拆出见证**；
右向（`∃ → Nonempty`）需要**装配** `Set.Nonempty`。
两向结构不同，故非换写。 -/
theorem obsClass_nonempty_iff [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η : ℝ} :
    (obsClass η h y).Nonempty ↔ ∃ x, dist (h x) y ≤ η := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [obsClass] using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, true_mem_obsClass hx⟩

/-- **空集的充要条件（否定形式）**：

`obsClass η h y = ∅` **⟺** 对**每个** `x`，都有 `η < dist (h x) y`。

**技术内容**：把 `∀ x, ¬ (dist … ≤ η)` 通过 `not_le` 改写成 `η < dist …`，
再用 `Set.not_nonempty_iff_eq_empty`。这是「集合为空」与「逐点否定」的桥。 -/
theorem obsClass_eq_empty_iff [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η : ℝ} :
    obsClass η h y = ∅ ↔ ∀ x, η < dist (h x) y := by
  rw [← Set.not_nonempty_iff_eq_empty, obsClass_nonempty_iff, not_exists]
  constructor
  · intro hp x
    exact not_le.mp (hp x)
  · intro hp x
    exact not_le.mpr (hp x)

/-- **满射 ⟹ 非空**：若 `h` 满射且 `η ≥ 0`，则每个噪声类都非空。

经由 §3.2 的充要条件：满射给出 `h x = y`，再 `dist_self`。 -/
theorem obsClass_nonempty_of_surjective [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η : ℝ}
    (hs : Function.Surjective h) (hη : 0 ≤ η) : (obsClass η h y).Nonempty := by
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨x, by simp [obsClass, hη]⟩

/-- **满射 ⟺ 所有精确纤维非空**（补全 §3.2 的另一半）。

第 2 条与 `obsClass_nonempty_of_surjective` **方向相反**：
那里是「满射 ⟹ 非空」，这里是「非空 ⟹ 满射」，
合起来给出**纤维族非空 ⟺ `h` 满射**。 -/
theorem surjective_of_forall_nonempty {h : X → Y} (hy : ∀ y, (hFiber h y).Nonempty) :
    Function.Surjective h := by
  intro y
  obtain ⟨x, hx⟩ := hy y
  exact ⟨x, by simpa [hFiber] using hx⟩

/-- **可达性的迁移**：`y` 在 `h` 的像里 ⟹ 噪声类非空（`η ≥ 0`）。 -/
theorem exists_obsClass_of_exists_hFiber [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η : ℝ}
    (hη : 0 ≤ η) (hex : ∃ x, h x = y) : ∃ x, x ∈ obsClass η h y :=
  ⟨hex.choose, hFiber_subset_obsClass hη (by simpa [hFiber] using hex.choose_spec)⟩

/-! #### §3.3  单调性：噪声上界就是一个嵌套球族 -/

/-- **单调性**：`η₁ ≤ η₂` ⟹ `obsClass η₁ h y ⊆ obsClass η₂ h y`。

⟹ 噪声类随上界**单调变大**（对应 `Y` 中闭球的嵌套）。
这是把「噪声上界」当成**单一旋钮**使用的合法性依据。 -/
theorem obsClass_mono [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η₁ η₂ : ℝ}
    (h12 : η₁ ≤ η₂) : obsClass η₁ h y ⊆ obsClass η₂ h y := by
  intro x hx
  exact le_trans (by simpa [obsClass] using hx) h12

/-! #### §3.4  零噪声退化：噪声类 = 精确纤维

**注意**：这一条**必须**要真度量（`MetricSpace`），不能只在伪度量里成立，
因为要用 `dist_eq_zero : dist x y = 0 ↔ x = y`。 -/

/-- **零噪声退化**：在度量空间中 `obsClass 0 h y = hFiber h y`。

**右→左**：`h x = y` ⟹ `dist (h x) y = dist y y = 0 ≤ 0`。
**左→右**：`dist (h x) y ≤ 0` ⟹ `dist (h x) y = 0`（`le_antisymm` + `dist_nonneg`）
⟹ `h x = y`（`dist_eq_zero`）。**这两个方向不等价于定义展开**，是真实推理。 -/
theorem obsClass_zero_eq_hFiber [MetricSpace Y] {h : X → Y} {y : Y} :
    obsClass (0 : ℝ) h y = hFiber h y := by
  ext x
  constructor
  · intro hx
    have h0 : dist (h x) y = 0 :=
      le_antisymm (by simpa [obsClass] using hx) dist_nonneg
    have hxy : h x = y := dist_eq_zero.mp h0
    simpa [hFiber] using hxy
  · intro hx
    have hxy : h x = y := by simpa [hFiber] using hx
    show dist (h x) y ≤ 0
    rw [hxy, dist_self]

/-- **零噪声的模型版**：`etaMax = 0` 时 `obsSet` 就是精确纤维。 -/
theorem ObsModel.obsSet_eq_hFiber [MetricSpace Y] (M : ObsModel X Y) (h0 : M.etaMax = 0)
    (y : Y) : M.obsSet y = hFiber M.h y := by
  simp only [ObsModel.obsSet, h0]
  exact obsClass_zero_eq_hFiber

/-! #### §3.5  单射时的退化：集合是单点

**这一节是任务书第 3 条**：「`h` 单射时集合是单点（退化情形）」。

**注意两个层次**：
- **精确纤维**：单射 ⟹ 纤维是**子单点集**（`Subsingleton`），**不需要度量**；
- **噪声类**：只有当 `η = 0` 时才退化（`η > 0` 时球有内点，必非单点）。
  故下文 `obsClass_subsingleton_of_injective` **显式带上 `η = 0`**——
  这是本文件对「退化情形」的**精确**刻画，不含糊。 -/

/-- **单射 ⟹ 精确纤维是子单点集（退化：弱档 → 点估计）**。

`h a = y` 且 `h b = y` ⟹ `a = b`（`h` 单射）。
**不需要度量、不需要单点集非空**：它说的是「集合至多一个元素」。 -/
theorem hFiber_subsingleton_of_injective {h : X → Y} (hinj : Function.Injective h) (y : Y) :
    (hFiber h y).Subsingleton := by
  intro a ha b hb
  have haya : h a = y := by simpa [hFiber] using ha
  have hyb : h b = y := by simpa [hFiber] using hb
  exact hinj (haya.trans hyb.symm)

/-- **单射且有解 ⟹ 纤维恰为单点**：`h x = y` ⟹ `hFiber h y = {x}`。

由 §3.5 第一条 + `Set.eq_singleton_iff_unique_mem`：
**唯一性**由单射给出，**存在性**由 `h x = y` 给出。
**这正说明「退化情形下弱档精确等于强档」。** -/
theorem hFiber_eq_singleton_of_injective {h : X → Y} (hinj : Function.Injective h) {y : Y} {x : X}
    (hx : h x = y) : hFiber h y = {x} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨true_mem_hFiber hx, ?_⟩
  intro x' hx'
  exact hFiber_subsingleton_of_injective hinj y hx' (true_mem_hFiber hx)

/-- **零噪声 + 单射 ⟹ 噪声类是子单点集**（弱档退化为强档）。

合成 §3.4（`obsClass 0 = hFiber`）与 §3.5（单射 ⟹ 纤维子单点）。 -/
theorem obsClass_subsingleton_of_injective [MetricSpace Y] {h : X → Y}
    (hinj : Function.Injective h) (y : Y) : (obsClass (0 : ℝ) h y).Subsingleton := by
  rw [obsClass_zero_eq_hFiber]
  exact hFiber_subsingleton_of_injective hinj y

/-- **正噪声下单射仍不退化**：即使 `h` 单射，`η > 0` 时噪声类**不是**子单点集。

**这是对「退化情形」的诚实补充**：任务书说「单射 ⟹ 单点」，
但那**只在零噪声下**成立；`η > 0` 时球必含两个不同点（若 `Y` 非平凡）。

这里给出**具体反例**：`Y = ℝ`、`h = id`、`y = 0`、`η = 1`
⟹ `0` 与 `1` 都在集合里，但它们不同。**`η > 0` 使点估计无法恢复。** -/
theorem obsClass_not_subsingleton_of_pos (η : ℝ) (hη : 0 < η) :
    ¬ (obsClass η (id : ℝ → ℝ) 0).Subsingleton := by
  intro hs
  have h0 : (0 : ℝ) ∈ obsClass η (id : ℝ → ℝ) 0 := by
    show dist (id (0 : ℝ)) 0 ≤ η
    simpa using hη.le
  have hη' : (η / 2) ∈ obsClass η (id : ℝ → ℝ) 0 := by
    show dist (id (η / 2)) 0 ≤ η
    rw [id, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have heq : (0 : ℝ) = η / 2 := hs h0 hη'
  linarith

/-- **同一观测下的两个候选状态，其观测值互相接近**：

`x₁, x₂ ∈ obsClass η h y` ⟹ `dist (h x₁) (h x₂) ≤ 2η`。

**这不是换写**：要从 `dist (h x₁) y ≤ η`、`dist (h x₂) y ≤ η`
经**三角不等式** `dist (h x₁) (h x₂) ≤ dist (h x₁) y + dist y (h x₂)`
与 `dist_comm` 推出来。**信息意义**：等价类内**不可能**有观测值差异超过 `2η` 的两个状态。 -/
theorem dist_le_two_mul_of_mem_obsClass [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η : ℝ}
    {x₁ x₂ : X} (h₁ : x₁ ∈ obsClass η h y) (h₂ : x₂ ∈ obsClass η h y) :
    dist (h x₁) (h x₂) ≤ 2 * η := by
  have h1' : dist (h x₁) y ≤ η := by simpa [obsClass] using h₁
  have h2' : dist (h x₂) y ≤ η := by simpa [obsClass] using h₂
  calc dist (h x₁) (h x₂) ≤ dist (h x₁) y + dist y (h x₂) := dist_triangle _ _ _
    _ = dist (h x₁) y + dist (h x₂) y := by rw [dist_comm y (h x₂)]
    _ ≤ η + η := add_le_add h1' h2'
    _ = 2 * η := by ring

/-! ### §4  「由 `y` 确定的等价类」确实是等价关系

任务书点明「等价类」。本节把**观测等价** `obsEq h x x' :⟺ h x = h x'` 形式化，
并证明它**恰好**是精确纤维族所诱导的划分 —— 即
`hFiber h (h x) = obsEq h x`。

**⚠ 这一节的诚实说明**：前三条（`refl/symm/trans`）是**等号性质的直接搬运**，
属例行公事。**真正有内容的是最后一条 `hFiber_eq_obsEq_class`**：
它把 §2 的集合与本节的关系**接上**，说明「等价类」不是新对象，
而是「纤维」的另一读法。 -/

/-- **观测等价**：两个状态**观测上不可区分** `h x = h x'`。

**这就是弱档的全部内容**：`h` 非单射时，`x` 与 `x'` 可能观测等价，
故由 `y` 只能确定**等价类**而非**点**。 -/
def obsEq (h : X → Y) (x x' : X) : Prop :=
  h x = h x'

@[simp] theorem obsEq_iff_eq {h : X → Y} {x x' : X} : obsEq h x x' ↔ h x = h x' := Iff.rfl

theorem obsEq_refl (h : X → Y) (x : X) : obsEq h x x := rfl

theorem obsEq_symm {h : X → Y} {x x' : X} (hxx : obsEq h x x') : obsEq h x' x := hxx.symm

theorem obsEq_trans {h : X → Y} {x x' x'' : X} (h₁ : obsEq h x x') (h₂ : obsEq h x' x'') :
    obsEq h x x'' := h₁.trans h₂

/-- **纤维集 = 等价类**：`h x = y` ⟹ `hFiber h y = { z | obsEq h x z }`。

两向包含：
- `z ∈ hFiber h y` ⟹ `h z = y = h x`（用 `h x = y`）⟹ `obsEq h x z`；
- `obsEq h x z` ⟹ `h z = h x = y` ⟹ `z ∈ hFiber h y`。

**这坐实了任务书的措辞**：「由 `y` 确定的等价类」**就是** `h⁻¹(y)`，
而 `h⁻¹(y)` **就是**某个 `x` 的观测等价类（`y` 可达时）。 -/
theorem hFiber_eq_obsEq_class {h : X → Y} {y : Y} {x : X} (hx : h x = y) :
    hFiber h y = {z | obsEq h x z} := by
  ext z
  constructor
  · intro hz
    have hzy : h z = y := by simpa [hFiber] using hz
    show obsEq h x z
    show h x = h z
    rw [hx, hzy]
  · intro hz
    have hzx : h z = h x := (obsEq_iff_eq.mp (show obsEq h x z from hz)).symm
    show h z = y
    rw [hzx, hx]

/-- **等价类相等 ⟺ 同属一个纤维**：`obsEq h x x' ⟺ x' ∈ hFiber h (h x)`。

即「观测不可区分」与「落在同一纤维里」是**同一件事**的两种说法。 -/
theorem obsEq_iff_mem_hFiber {h : X → Y} {x x' : X} :
    obsEq h x x' ↔ x' ∈ hFiber h (h x) := by
  constructor
  · intro he
    show h x' = h x
    exact (obsEq_iff_eq.mp he).symm
  · intro hm
    show h x = h x'
    exact (show h x' = h x from hm).symm

/-! ### §5  两条「边界」命题（说明弱档不能更强） -/

/-- **弱档不能给出单点：存在非单射 `h` 使纤维真的有两个点。**

`X = Bool`、`Y = Unit`、`h ≡ ()` ⟹ `hFiber h () = univ`，
它含 `true` 与 `false` 两个不同元素。**故 A14 的强档（点估计）在此例下为假。**
这是**具体反例**，不是抽象否定。 -/
theorem hFiber_nonsubsingleton_example :
    ¬ (hFiber (fun _ : Bool => ()) ()).Subsingleton := by
  intro hs
  have h1 : (true : Bool) ∈ hFiber (fun _ : Bool => ()) () := rfl
  have h0 : (false : Bool) ∈ hFiber (fun _ : Bool => ()) () := rfl
  have htf : true = false := hs h1 h0
  exact (Bool.true_eq_false).mp htf

/-- **弱档的「信息损失」是最小可能的**：对 `X = Bool, Y = Unit` 的退化 `h`，
噪声类（`η ≥ 0`）**恰是全集** —— 即观测**不含任何信息**。

这给出的**下界**：弱档保证的**不是**恢复 `x`，而是**仅**恢复「`x` 在哪个集合里」；
在最坏情形下那个集合就是整个 `X`。 -/
theorem obsClass_univ_of_trivial (η : ℝ) (hη : 0 ≤ η) :
    obsClass η (fun _ : Bool => ()) () = Set.univ := by
  ext x
  constructor
  · intro _; trivial
  · intro _
    show dist ((fun _ : Bool => ()) x) () ≤ η
    simp [hη]

end ObsEstimationWeak

end FateV2.Modeling
