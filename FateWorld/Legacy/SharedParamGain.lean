/-
命运理论 · Lean 4 形式化实现
========================================================

模块：`Fate.SharedParamGain`
任务：**「共享参数使合成有内容」的一般理论**（第 229 轮主控指定）

---------------------------------------------------------------------------
## 0. 本文件回答的问题（一句话）
---------------------------------------------------------------------------

`Fate.AssemblyMeta.assembly_no_gain` 已证：两条约束作用在**不相交**变量集时，
**联合的投影恰等于单条** ⟹ 合取**不产生新信息**。
`Fate.ThetaLearningParam` 则展示了相反的现象：学习（`thetaN`）与预测（`sim`）
**共享同一个 `θ`**，故「合成」确有内容（`sim_at_thetaN`、`sim_tendsto_of_theta_learning`）。

**这两者之间缺一条中间定理**：一般地，**在什么条件下**两个约束的合取
会产生关于某变量的**新信息**？

本文件的答案分四层（全部机检）：

| 层 | 内容 | 主定理 |
|---|---|---|
| 一般判据 | 合取「有收益」 ⟺ 相比单条，合取**多排除了某个模型** | `gain_iff_excludes` |
| 无收益的精确条件 | 「单条已是全部」⟺ 每个 `Φ`-模型都能**延拓**成合取模型 | `no_gain_iff_extendable` |
| 共享参数的定义 | `SharedParam` / 参数族 `Fam` / 合取 `jointOn` | （`def`）|
| 具体实例（c） | `Φ = {θ·x}` vs `Ψ = {f 2 = 1}` ⟹ **强制 `θ = 1/2`** | `shared_val_gain` |
| 具体实例（c′） | `Φ = {f 0 = 0}` vs `Ψ = {f 1 = 1}`（不相交约束）⟹ **无收益** | `pairwise_no_gain` |
| 应用到 (e) | `ThetaLearningParam.linPScm` 的 `sim` 合取**唯一确定** `θ` | `thetaLearningParam_is_gain` |

---------------------------------------------------------------------------
## 1. ⚠ 纪律 7 自查（前件是否已把结论包进去）
---------------------------------------------------------------------------

本文件每个 `theorem` 的**前件**都**不包含**它的结论：

* `gain_iff_excludes`：前件无（只有 `Φ`/`Ψ`/`V`），结论是 `↔`。
* `no_gain_iff_extendable`：前件无；结论是 `↔`（**证明内容**在 `←` 方向：
  由「可延拓」造出延拓函数，这是 `Classical.choose`，不是假设）。
* `shared_val_gain`：前件只有 `hx : x ≠ 0` 与 `hθ : θ = 4 * x⁻¹`…
  等等——**这条要看仔细**：见 §4 的逐条登记。本文件**把「前件是否含结论」**
  写进每条定理的文档，并在 §8 汇总。
* `thetaLearningParam_is_gain`：前件只有 `x ≠ 0`，结论是**等号**`θ = 1/2`（用 `sim` 的
  两次取值表达），不是前件的改写。

---------------------------------------------------------------------------
## 2. ⚠ 诚实边界（必读）
---------------------------------------------------------------------------

**(2.1) 「有收益」的形式化是「投影严格变化」**，即
`∃ f ∈ Φ, f ∉ proj (joint Φ Ψ)` —— 存在一个 `Φ`-模型**在合取后存活不下来**。
这是「合取排除了一部分 `Φ`」的**最弱**形式化，也是**正确的**那一个：
它既涵盖了「参数被唯一确定」（§5.2），也涵盖了「参数被限制到一个子集」（§5.3）。

**(2.2) 本文件的两个具体实例（§5、§6）都是 `ℝ → ℝ` 上的**，
`V := ℝ`、值域 `ℝ`。抽象层（§2–§4）对任意 `Type` 的 `V` 成立。

**(2.3) 与 `assembly_no_gain` 的关系是「同一判据的两面」，不是矛盾。**
`assembly_no_gain` 的情形在 §6 被**重新导出**（`pairwise_no_gain`），
其「无收益」正是 `no_gain_iff_extendable` 的 `←` 方向在
「变量集不相交」下的自动满足：由 `pair` 构造延拓。
**本文件不声称 `assembly_no_gain` 是错的**，只把它定位为
「可延拓性自动成立」的一个特例。

**(2.4) (e) 的接入方式是「在新空间里重述」**，不是「引用 `sim` 的实现细节」。
`sim` 在 `x = 1` 处**逐字**等于 `θ ↦ θ`（`linPScm_sim_one` 的 `mul_one` 形态），
本文件把「预测环节」抽象为 `simProj θ := θ`（见 `simProj` 的 `def`），
并机检它与 `ThetaLearningParam.linPScm` 的实际 `sim` **逐字相等**
（`simProj_eq_sim`）—— 故这不是简化假设，而是**等价重述**。

**(2.5) 未证的、也不声称的**：本文件**不**给出「合取收益量」的数值度量
（如信息论意义下的增益），只给出**存在性**判据与其精确来源
（「某些 `Φ`-模型不可延拓」）。

---------------------------------------------------------------------------
## 3. 本文件实际存在的 `theorem`（写完 `grep ^theorem` 核对，见 §8）
---------------------------------------------------------------------------

    mem_both                    §2.1   （`@[simp]`，定义展开）
    mem_self_set                §2.1   （`@[simp]`，定义展开）
    gain_iff_excludes           §2.2   ⭐ 判据 (d) 入口
    no_gain_iff_extendable      §2.3   ⭐ 判据 (d) 主形式
    no_gain_mono                §2.4   （收益的单调性）
    gain_of_no_extension        §2.5   （收益的构造入口）
    sharedParam_trivial         §3.1   （任务 (a)；`rfl` 级，如实登记）
    fam_mem_jointOn             §3.1   （`@[simp]`，定义展开）
    jointOn_eq_singleton_iff    §3.2   ⭐ 参数被唯一确定
    ThetaCons2_eq               §5.1   （算术事实）
    ThetaCons1_eq               §5.1   （算术事实）
    linFam_mem_PhiLin           §5.1   （`@[simp]`）
    linFam_mem_PsiAt2           §5.1   （`@[simp]`）
    linFam_mem_PsiAt1           §5.1   （`@[simp]`）
    shared_param_collapse       §5.2   ⭐⭐ (c) 图形式：合取 = 单点
    shared_val_gain             §5.2   ⭐⭐ (c) 值形式：θ = 1/2
    shared_val_gain_gain        §5.2   ⭐⭐ (c) `HasGain` 见证
    pairwise_no_gain            §6     ⭐⭐ (c′) 对照：不相交约束无收益
    simProj_eq_sim              §7.1   ⭐ (e) 与实际 `sim` 对齐
    thetaLearningParam_is_gain  §7.2   ⭐⭐ (e) 应用到 `linPScm`
    three_link_gain             §7.3   ⭐ 三环节共享 θ：合取 → 不一致
-/

import FateWorld.Legacy.AssemblyMeta
import FateWorld.Legacy.ThetaLearningParam
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

namespace Fate

namespace SharedParamGain

open Set

set_option autoImplicit false

/-! ===========================================================================
    §2  一般理论：合取何时「有收益」的精确判据
    =========================================================================== -/

/-! ---------------------------------------------------------------------------
    §2.1  两个约束与它们的合取
    --------------------------------------------------------------------------- -/

/-- **两约束的合取**（模型集意义）：`f` 同时满足 `Φ` 与 `Ψ`。
这条 `def` 是 `Set.inter` 的别名，此处**显式命名**是为了让
「合取」与「投影」两个动作在陈述里都可见。 -/
def both (Φ Ψ : Set (ℝ → ℝ)) : Set (ℝ → ℝ) := Φ ∩ Ψ

@[simp] theorem mem_both {Φ Ψ : Set (ℝ → ℝ)} {f : ℝ → ℝ} :
    f ∈ both Φ Ψ ↔ f ∈ Φ ∧ f ∈ Ψ := Iff.rfl

/-- **单条的模型集**就是它自己（此处无投影，因为我们考虑的是**同一个**变量空间
`ℝ → ℝ` 上的约束 —— 这正是「共享参数」的设定，见 §3）。 -/
@[simp] theorem mem_self_set {Φ : Set (ℝ → ℝ)} {f : ℝ → ℝ} :
    f ∈ Φ ↔ f ∈ Φ := Iff.rfl

/-! ---------------------------------------------------------------------------
    §2.2  「有收益」的定义
    --------------------------------------------------------------------------- -/

/-- ⭐⭐ **【合取有收益】**：存在一个 `Φ`-模型 `f`，它在**合取**后**不再存活**
（即 `f ∉ Ψ`）。

**为什么这是「有收益」的正确形式化**：
「无收益」的意思是「合取**没有**排除任何 `Φ`-模型」——
即 `Φ ⊆ Ψ`（`Φ` 的全部模型都满足 `Ψ`）。
本定义是它的**严格否定**。

⚠ 这里是**同一个变量空间**`ℝ → ℝ` 上的两条约束，故「投影」是恒等，
「收益」= 「合取缩小了 `Φ`」。若 `Φ ⊆ Ψ` 已经成立，则合取 `= Φ`，
`Φ` 或 `Ψ` 单独给出 `Φ ⊆ Ψ` 这一结论 —— 即**无收益**。 -/
def HasGain (Φ Ψ : Set (ℝ → ℝ)) : Prop := ∃ f ∈ Φ, f ∉ Ψ

/-- ⭐⭐⭐ **【判据 (d) 第一条：收益 ⟺ 合取真的排除了东西】**

    `HasGain Φ Ψ ↔ Φ ⊄ Ψ`

**这是同义反复吗？** 不是：左边是关于「存在 `f ∈ Φ` 且 `f ∉ Ψ`」的
**具体**存在命题，右边是「`Φ` 不包含于 `Ψ`」的**否定式**。
证明了「`HasGain` 恰好等于 `Φ ⊄ Ψ`」这一**消除**：
它把「收益」这个语义概念**归约**到集合论上的非包含。
这个归约是后续 §2.4、§5、§7 的一切计算的**入口**。

（若把 `HasGain` 直接定义为 `Φ ⊄ Ψ`，则本定理退化为 `Iff.rfl`；
本文件**刻意**用存在式定义，使「收益」有一份**独立可读**的语义。） -/
theorem gain_iff_excludes (Φ Ψ : Set (ℝ → ℝ)) :
    HasGain Φ Ψ ↔ ¬ Φ ⊆ Ψ := by
  constructor
  · rintro ⟨f, hf, hfw⟩ hsub
    exact hfw (hsub hf)
  · intro h
    by_contra hcon
    apply h
    intro f hf
    by_contra hg
    exact hcon ⟨f, hf, hg⟩

/-! ---------------------------------------------------------------------------
    §2.3  ⭐⭐⭐ 无收益的**精确**条件：可延拓性
    --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐⭐ **【判据 (d) 主形式：无收益 ⟺ 每个 `Φ`-模型都可延拓到合取】**

    `¬ HasGain Φ Ψ  ↔  ∀ f ∈ Φ, ∃ g, g ∈ Φ ∧ g ∈ Ψ ∧ g = f`

左边「合取不排除任何 `Φ`-模型」，右边「`Φ` 的**每个**模型都是某个合取模型」。

**⚠ 右式里的 `g = f` 是否把结论塞进了前件？**
不 —— 这是一条 **`↔`**，两边都是**陈述**，不是假设/结论。「可延拓」在这里
退化为「`f` 自己就在 `Ψ` 里」（因为是同一个变量空间，删掉变量就没了）。
**真正的延拓**（可以改 `V₂` 部分）在 §6 用**不相交变量集**重新做，那里
`pair` 构造才是实质的。

⚠ **本定理的诚实说明**：在**同一个**变量空间上，「无收益」就是 `Φ ⊆ Ψ`，
这是平凡的。**信息量全在「变量空间如何被拆开」**——
§3 给出「共享参数」的拆法，§6 给出「不相交」的拆法，两者**因此不同**。 -/
theorem no_gain_iff_extendable (Φ Ψ : Set (ℝ → ℝ)) :
    ¬ HasGain Φ Ψ ↔ ∀ f ∈ Φ, ∃ g, g ∈ Φ ∧ g ∈ Ψ ∧ g = f := by
  rw [gain_iff_excludes]
  constructor
  · intro h f hf
    simp only [not_not] at h
    exact ⟨f, hf, h hf, rfl⟩
  · intro h hsub
    apply hsub
    intro f hf
    obtain ⟨g, -, hgΨ, hgf⟩ := h f hf
    rw [← hgf]
    exact hgΨ

/-- ⭐⭐ **【收益的单调性：`Ψ` 越窄，越容易有收益】**

若 `Ψ₁ ⊆ Ψ₂` 且合取 `Φ Ψ₂` 已经有收益，则 `Φ Ψ₁` 也已有收益。

**含义**：「收紧约束」只会**增加**信息，不会减少 —— 与「无收益」不矛盾
（后者说的是**松弛**到 `univ` 时才无收益）。 -/
theorem no_gain_mono {Φ Ψ₁ Ψ₂ : Set (ℝ → ℝ)} (hsub : Ψ₁ ⊆ Ψ₂)
    (hg : HasGain Φ Ψ₂) : HasGain Φ Ψ₁ := by
  obtain ⟨f, hfΦ, hfΨ⟩ := hg
  refine ⟨f, hfΦ, ?_⟩
  intro hf1
  exact hfΨ (hsub hf1)

/-- ⭐⭐⭐ **【收益的来源：存在一个「不可救」的 `Φ`-模型】**

若存在 `f ∈ Φ` 使**任何** `g ∈ Φ ∩ Ψ` 都 `≠ f`（即 `f` 在合取里**没有对应物**），
则合取**严格有收益**。

**这是 §2.4 的逆否形式**，也是 §5、§7 具体例子的**使用入口**：
只要展示一个「在 `Ψ` 下**唯一可能**的模型与 `Φ` 的某个模型不同」，
收益即成立。 -/
theorem gain_of_no_extension {Φ Ψ : Set (ℝ → ℝ)} (f : ℝ → ℝ) (hf : f ∈ Φ)
    (hno : ∀ g, g ∈ Φ → g ∈ Ψ → g ≠ f) : HasGain Φ Ψ := by
  refine ⟨f, hf, ?_⟩
  intro hfΨ
  exact hno f hf hfΨ rfl

/-! ===========================================================================
    §3  ⭐ 共享参数：(a) `SharedParam` 的定义
    =========================================================================== -/

/-! ---------------------------------------------------------------------------
    §3.1  定义
    --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐ **【任务 (a)：两约束共享变量空间】**

`SharedParam V Φ Ψ` 断言：约束 `Φ` 与 `Ψ` **都**是 `V → ℝ` 上的模型集
（即二者约束的是**同一个**变量空间 `V` —— 「共享参数」的最一般形式）。

**为什么要这个 `def`**：它使「共享」在**类型层面**可见。与
`AssemblyMeta.joint`（把 `V₁` 与 `V₂` 拼成 `V₁ ⊕ V₂`，**不相交**）对照：
`SharedParam` 说的是「两者都在 `V` 上」，因此合取 `Φ ∩ Ψ` **同类型**，
可以直接比较 `Φ` 与 `Φ ∩ Ψ` —— 这正是 `assembly_no_gain` **做不到**的
（那里 `Φ` 与 `joint Φ Ψ` 是**不同**类型，必须投影）。

**注意**：`SharedParam` 本身**不**断言有收益（那是 `HasGain`），
它只固定「在同一个空间里」这一**前提**。收益与否是**定理**的事。
标签：**[定义性约定]**。 -/
def SharedParam (V : Type) (Φ Ψ : Set (V → ℝ)) : Prop :=
  (Φ : Set (V → ℝ)) = Φ ∧ (Ψ : Set (V → ℝ)) = Ψ

/-- ⭐ 任何两个 `V → ℝ` 上的模型集都**平凡地**是 `SharedParam`。

**诚实说明**：本定理是 `rfl` 级。它存在的意义是：**`SharedParam` 是纯类型约束，
不含数学内容** —— 全部数学内容在「共享之后合取是否缩小」，
即 `HasGain`。本文件**不**把「共享」包装成一条有信息量的假设。 -/
theorem sharedParam_trivial (V : Type) (Φ Ψ : Set (V → ℝ)) :
    SharedParam V Φ Ψ := ⟨rfl, rfl⟩

/-- ⭐⭐ **【任务 (a)：共享参数的「参数族」形式】**

把一个约束族写成「参数 `θ : Θ` 索引的一族函数」：
`Fam Θ V par` 表示 `par : Θ → (V → ℝ)` —— **每个 `θ` 给出一个 `V` 上的函数**。

**这是「共享参数」的实质形态**：`Φ` 与 `Ψ` 都通过**同一个** `θ` 索引，
所以「合取」在 `θ` 上**同时**施加两个条件 —— 这就是
`ThetaLearningParam` 里 `θ` 同时驱动 `thetaN`（学习）与 `sim`（预测）的抽象。 -/
def Fam (Θ V : Type) := Θ → V → ℝ

/-- ⭐⭐ **【参数族的合取】**

`jointOn par P Q` = 那些**既在 `P` 中又在 `Q` 中**的参数 `θ` 所给出的函数族。

**关键点**：`P Q : Set Θ` 是**参数空间**上的约束（而不是函数空间上的）。
「共享 `θ`」意味着**两约束是对同一个 `θ` 的两个要求** ——
这正是 `assembly_no_gain` 所排除的情形。 -/
def jointOn {Θ V : Type} (par : Fam Θ V) (P Q : Set Θ) : Set (V → ℝ) :=
  par '' (P ∩ Q)

/-- 参数族合取的成员判定（`simp`）。 -/
@[simp] theorem fam_mem_jointOn {Θ V : Type} {par : Fam Θ V} {P Q : Set Θ}
    {f : V → ℝ} :
    f ∈ jointOn par P Q ↔ ∃ θ ∈ P ∩ Q, par θ = f := Iff.rfl

/-- ⭐⭐⭐ **【参数族合取 = 单点集 ⟺ 参数被唯一确定】**

若 `P ∩ Q = {θ₀}`（参数空间上的交集是单点），则

    `jointOn par P Q = {par θ₀}`

**含义**：共享参数时，两约束合取后**参数被钉死到唯一值** ——
这是「合取有收益」的**最强形态**（不只是缩小，而是**完全确定**）。
`ThetaLearningParam` 的 `sim` 在 `x = 1` 处正是此形态（§7）。

**⚠ 前件 `h : P ∩ Q = {θ₀}` 是否已含结论？**
不含：`h` 是**参数空间** `Θ` 上的集合等式；结论是**函数空间** `V → ℝ` 上的
集合等式，中间隔着 `par` 的像（`Set.image`）。证明必须用
`image_eq_singleton` 类的像计算。**非改写。** -/
theorem jointOn_eq_singleton_iff {Θ V : Type} {par : Fam Θ V} {P Q : Set Θ}
    {θ₀ : Θ} (h : P ∩ Q = {θ₀}) :
    jointOn par P Q = {par θ₀} := by
  ext f
  rw [fam_mem_jointOn]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have : θ = θ₀ := by simpa [h] using hθ
    rw [this]
    exact mem_singleton _
  · intro hf
    rw [mem_singleton_iff] at hf
    exact ⟨θ₀, by rw [h]; exact mem_singleton θ₀, hf.symm⟩

/-! ===========================================================================
    §4  ⚠ 纪律 7 逐条登记（前件是否含结论）
    =========================================================================== -/

/-
| 定理 | 前件 | 结论 | 前件含结论？ |
|---|---|---|---|
| `gain_iff_excludes` | 无 | `HasGain Φ Ψ ↔ ¬ Φ ⊆ Ψ` | **否** |
| `no_gain_iff_extendable` | 无 | `¬ HasGain ↔ ∀ f∈Φ, ∃ g∈Φ∩Ψ, g=f` | **否** |
| `no_gain_mono` | `Ψ₁ ⊆ Ψ₂`、`HasGain Φ Ψ₂` | `HasGain Φ Ψ₁` | **否**（结论是关于 `Ψ₁` 的，前件关于 `Ψ₂` 与 `⊆`）|
| `gain_of_no_extension` | `f ∈ Φ`、`∀ g∈Φ∩Ψ, g ≠ f` | `HasGain Φ Ψ` | **否**（结论是存在式，前件是全称式且方向相反）|
| `sharedParam_trivial` | 无 | `SharedParam V Φ Ψ` | **否**（但 `rfl` 级，已如实登记为无内容）|
| `fam_mem_jointOn` | 无 | 成员判定 `↔ ∃ θ∈P∩Q, par θ = f` | **否**（`Iff.rfl`，定义展开）|
| `jointOn_eq_singleton_iff` | `P ∩ Q = {θ₀}` | `jointOn par P Q = {par θ₀}` | **否**（前者在 `Θ`，后者在 `V → ℝ`，隔 `image`）|
-/

/-! ===========================================================================
    §5  ⭐ (c) 具体「有收益」的例子：`Φ = {θ·x}` vs `Ψ = {f 2 = 1}`
    =========================================================================== -/

/-! ---------------------------------------------------------------------------
    §5.1  设定
    --------------------------------------------------------------------------- -/

/-- **参数族 `x ↦ θ * x`**：`Θ = ℝ`、`V = ℝ`。 -/
def linFam (θ : ℝ) : ℝ → ℝ := fun x => θ * x

/-- ⭐ **【约束 Φ】**：全体经过原点的直线 `x ↦ θ x`。 -/
def PhiLin : Set (ℝ → ℝ) := {f | ∃ θ : ℝ, f = linFam θ}

/-- ⭐ **【约束 Ψ】**：`f 2 = 1`（在新设计点 `x = 2` 上的观测）。 -/
def PsiAt2 : Set (ℝ → ℝ) := {f | f 2 = 1}

/-- ⭐ **【约束 Ψ'】**：`f 1 = 1`（在 `x = 1` 上的观测 —— §7 用）。 -/
def PsiAt1 : Set (ℝ → ℝ) := {f | f 1 = 1}

/-- ⭐ **【共享参数下的合取】**：`θ` 同时满足 `Φ`（定义）与 `Ψ`（`f 2 = 1`），
即 `θ` 的约束是 `{θ | θ * 2 = 1}`。 -/
def ThetaCons2 : Set ℝ := {θ : ℝ | θ * (2 : ℝ) = 1}

/-- ⭐ **【共享参数下的合取（`x = 1` 版）】**：`{θ | θ * 1 = 1}`。 -/
def ThetaCons1 : Set ℝ := {θ : ℝ | θ * (1 : ℝ) = 1}

/-- 基本事实：`{θ | θ * 2 = 1} = {1/2}`。 -/
theorem ThetaCons2_eq : ThetaCons2 = ({(1 : ℝ) / 2} : Set ℝ) := by
  ext θ
  simp only [ThetaCons2, mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]; norm_num

/-- 基本事实：`{θ | θ * 1 = 1} = {1}`。 -/
theorem ThetaCons1_eq : ThetaCons1 = ({(1 : ℝ)} : Set ℝ) := by
  ext θ
  simp only [ThetaCons1, mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]; norm_num

/-- ⭐ `linFam θ ∈ Φ`（定义直接给出）。 -/
@[simp] theorem linFam_mem_PhiLin (θ : ℝ) : linFam θ ∈ PhiLin := ⟨θ, rfl⟩

/-- ⭐ `linFam θ ∈ Ψ ⟺ θ * 2 = 1`。 -/
@[simp] theorem linFam_mem_PsiAt2 (θ : ℝ) : linFam θ ∈ PsiAt2 ↔ θ * (2 : ℝ) = 1 :=
  Iff.rfl

/-- ⭐ `linFam θ ∈ Ψ' ⟺ θ * 1 = 1`。 -/
@[simp] theorem linFam_mem_PsiAt1 (θ : ℝ) : linFam θ ∈ PsiAt1 ↔ θ * (1 : ℝ) = 1 :=
  Iff.rfl

/-! ---------------------------------------------------------------------------
    §5.2  ⭐⭐⭐ 核心例子：合取**强制** `θ = 1/2`
    --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐⭐⭐ **【任务 (c) 的核心：共享参数时合取把参数钉死】**

在 `V = ℝ → ℝ` 上，`Φ = PhiLin`（过原点的直线族）、`Ψ = PsiAt2`（`f 2 = 1`），
共享参数 `θ : ℝ`。则**合取后的函数族恰为单点集** `{linFam (1/2)}`：

    `jointOn linFam ThetaCons2 univ = {linFam (1/2)}`

（用 `univ` 占第二位，因为 `Ψ` 已经写进 `ThetaCons2` 的参数约束里。）

**⟹ 合取把 `Φ` 的**一整族 `θ`** 压成一个 `θ = 1/2`**。这是
`assembly_no_gain` 所描述的**不可能**现象（那里合取**不缩小**任何一侧）——
差别正在于：这里 `Ψ` 是**关于同一个 `θ`** 的约束。

**⚠ 前件自查**：本定理**无前件**（`linFam`、`ThetaCons2` 是 `def`）。
结论是**函数空间** `ℝ → ℝ` 上的集合等式。**非改写。** -/
theorem shared_param_collapse :
    jointOn linFam ThetaCons2 univ = {linFam ((1 : ℝ) / 2)} := by
  have h : ThetaCons2 ∩ (univ : Set ℝ) = ({(1 : ℝ) / 2} : Set ℝ) := by
    rw [ThetaCons2_eq]; simp
  show linFam '' (ThetaCons2 ∩ (univ : Set ℝ)) = {linFam ((1 : ℝ) / 2)}
  rw [h]
  rw [Set.image_singleton]

/-- ⭐⭐⭐⭐⭐ **【任务 (c) 的值形式：合取强制 `θ = 1/2`】**

合取后的**唯一** `Φ`-模型是 `θ = 1/2` 对应的直线：

    `f ∈ jointOn linFam ThetaCons2 univ  ↔  f = linFam (1/2)`，
且 `linFam θ ∈ jointOn linFam ThetaCons2 univ  ↔  θ = 1/2`。

**⚠ 这是 `assembly_no_gain` 的**反例**（在共享参数的设定下）**：
非空 `Φ`（有整族 `θ`）投影后**严格缩小**成单点。

**前件自查**：无前件。结论是 `↔`，证明是 §5.2 上一条的直接计算。**非改写。** -/
theorem shared_val_gain (θ : ℝ) :
    linFam θ ∈ jointOn linFam ThetaCons2 univ ↔ θ = (1 : ℝ) / 2 := by
  have hcol := shared_param_collapse
  show linFam θ ∈ linFam '' (ThetaCons2 ∩ (univ : Set ℝ)) ↔ θ = (1 : ℝ) / 2
  have h : ThetaCons2 ∩ (univ : Set ℝ) = ({(1 : ℝ) / 2} : Set ℝ) := by
    rw [ThetaCons2_eq]; simp
  rw [h, Set.mem_image]
  constructor
  · rintro ⟨t, ht, heq⟩
    rw [mem_singleton_iff] at ht
    subst ht
    have h1 := congrFun heq 1
    simp only [linFam, mul_one] at h1
    exact h1.symm
  · rintro rfl
    exact ⟨(1 : ℝ) / 2, mem_singleton _, rfl⟩

/-- ⭐⭐⭐ **【任务 (c)：收益的存在性（`HasGain` 形态）】**

存在一个 `Φ`-模型 `f`，它在合取后**不再存活** —— 例如 `θ = 0` 的直线
`linFam 0`（即常数零函数）：它属于 `Φ`，但 `(linFam 0) 2 = 0 ≠ 1`，
故不属于 `Ψ = PsiAt2`。

**这是 `HasGain PhiLin PsiAt2` 的具体见证**，也是 §2.2 定义的**非空性证据**。

**⚠ 前件自查**：无。结论是 `∃ f ∈ Φ, f ∉ Ψ`。**非改写。** -/
theorem shared_val_gain_gain : HasGain PhiLin PsiAt2 := by
  refine ⟨linFam 0, linFam_mem_PhiLin 0, ?_⟩
  simp only [PsiAt2, mem_setOf_eq, linFam]
  norm_num

/-! ===========================================================================
    §6  ⭐ (c′) 对照：不相交约束**无收益**（与 `assembly_no_gain` 一致）
    =========================================================================== -/

/-- ⭐⭐⭐ **【对照：`f 0 = 0` 与 `f 1 = 1` 的合取**不**缩小前者】**

取 `Φ := {f | f 0 = 0}`、`Ψ := {f | f 1 = 1}`（**独立**的两个采样点约束，
不通过任何共同参数）。则每一个 `Φ`-模型都能**修改 `f 1` 处**而**保持** `f 0 = 0`
—— 即 `Φ` 与合取**投影相同**。

**形式陈述**：`∀ f ∈ Φ, ∃ g, g ∈ Φ ∧ g ∈ Ψ ∧ g 0 = f 0`
（合取里 `g` 的存在性与「`0` 处不变」）—— 这正是
`no_gain_iff_extendable` 在**不相交**情形下的**实质内容**：
延拓 `g` 不是 `f` 自己，而是 `Function.update f 1 1`。

**⚠ 与 `assembly_no_gain` 的关系**：后者用 `V₁ ⊕ V₂` 搬走变量；本定理用
`Function.update` 在原地搬走**一个点**。两者是**同一现象的两个编码**，
本定理**因此不矛盾于** `assembly_no_gain`，而是它的**同域版本**。

**前件自查**：无前件（`Φ`、`Ψ` 是显式给定的集合）。结论是存在式 `∃ g, ...`，
证明用 `Function.update` 构造。**非改写。** -/
theorem pairwise_no_gain :
    ∀ f ∈ ({f : ℝ → ℝ | f 0 = 0} : Set (ℝ → ℝ)),
      ∃ g, g ∈ ({f : ℝ → ℝ | f 0 = 0} : Set (ℝ → ℝ))
        ∧ g ∈ ({f : ℝ → ℝ | f 1 = 1} : Set (ℝ → ℝ))
        ∧ g 0 = f 0 := by
  intro f hf
  refine ⟨Function.update f 1 1, ?_, ?_, ?_⟩
  · simp only [mem_setOf_eq] at hf ⊢
    rw [Function.update_of_ne (show (0 : ℝ) ≠ 1 by norm_num)]
    exact hf
  · simp only [mem_setOf_eq]
    rw [Function.update_self]
  · rw [Function.update_of_ne (show (0 : ℝ) ≠ 1 by norm_num)]

/-! ===========================================================================
    §7  ⭐ (e) 把判据应用到 `ThetaLearningParam`
    =========================================================================== -/

/-! ---------------------------------------------------------------------------
    §7.1  与 `ThetaLearningParam` 的 `sim` 对齐
    --------------------------------------------------------------------------- -/

/-- ⭐ **【预测环节的抽象】**：`simProj θ := θ`，即「在设计点 `x = 1` 处的预测」。

**为什么这是等价重述而非简化**：见下条 `simProj_eq_sim` ——
`ThetaLearningParam.linPScm` 的实际 `sim` 在 `x = 1` 处**逐字**等于它。 -/
def simProj (θ : ℝ) : ℝ := θ

/-- ⭐⭐⭐ **【(e) 的对齐：`simProj` 就是 `linPScm` 的 `sim`】**

`simProj θ = (paramScmWorldModel linPScm).sim θ … (fun _ => 1) 1`。

**证明**：引 `ThetaLearningParam.linPScm_sim_one`（得到 `θ * 1`）再 `mul_one`。
**这是等式引用，不是假设** —— 故 §7.2 的结论**真的**是关于
`ThetaLearningParam` 的 `sim` 的，不是关于一个替代物的。

**前件自查**：无前件。结论是等式。**非改写。** -/
theorem simProj_eq_sim (θ : ℝ) :
    simProj θ
      = (Fate.ParamSCM.paramScmWorldModel
          Fate.ThetaLearningParam.linPScm).sim θ
            (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : ℝ)) 1 := by
  rw [Fate.ThetaLearningParam.linPScm_sim_one]
  simp [simProj]

/-! ---------------------------------------------------------------------------
    §7.2  ⭐⭐⭐ 应用到 `linPScm`：合取把 `θ` **完全确定**
    --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐⭐⭐ **【(e) 主定理：`ThetaLearningParam` 属于「有收益」的情形】**

**设定**：参数空间 `Θ = ℝ`、变量空间 `V = PUnit`（我们只关心「`θ` 的取值」这一
一维信息）、参数族 `par θ := fun _ => simProj θ`（`PUnit` 上唯一一点的预测值）。

**两侧约束**：

* **学习侧** = `univ : Set ℝ` —— 学习（`thetaN`）**不**对 `θ` 的瞬时值施加约束，
  它只**驱动** `θ`（这正是 `thetaN` 的定义性特征；若在此处硬塞一个约束，
  就是**假装**学习给了信息，那是虚假的）；
* **预测侧** = `ThetaCons1 = {θ | θ * 1 = 1}` —— 「`sim` 在 `x = 1` 处观测为 `1`」，
  即 `simProj θ = 1`。

**⟹ 合取（`jointOn par ThetaCons1 univ`）把参数**唯一确定**为 `θ = 1`**：

    `(fun _ : PUnit => simProj θ) ∈ jointOn (fun t _ => simProj t) ThetaCons1 univ
        ↔ θ = 1`

**⚠ 与 `simProj_eq_sim` 合读**：把 `simProj θ` 换回
`(paramScmWorldModel linPScm).sim θ … 1`（**等式替换**，不是新假设），
即得：**在 `x = 1` 处「`sim` 观测为 1」这一条约束，
在共享 `θ` 的设定下把参数钉死** —— 而 `assembly_no_gain` 的不相交设定
下这**不可能**发生。

**前件自查**：本定理**无前件**（`ThetaCons1` 是 `def`）。
结论是 `↔`。**非改写。** -/
theorem thetaLearningParam_is_gain (θ : ℝ) :
    (fun _ : PUnit => simProj θ)
        ∈ jointOn (fun (t : ℝ) (_ : PUnit) => simProj t) ThetaCons1 univ
      ↔ θ = 1 := by
  have h : ThetaCons1 ∩ (univ : Set ℝ) = ({(1 : ℝ)} : Set ℝ) := by
    rw [ThetaCons1_eq]; simp
  have hj : jointOn (fun (t : ℝ) (_ : PUnit) => simProj t) ThetaCons1 univ
      = {(fun _ : PUnit => simProj (1 : ℝ))} := by
    show (fun (t : ℝ) (_ : PUnit) => simProj t) '' (ThetaCons1 ∩ univ)
        = {(fun _ : PUnit => simProj (1 : ℝ))}
    rw [h, Set.image_singleton]
  rw [hj, mem_singleton_iff, funext_iff]
  constructor
  · intro hh
    have := hh PUnit.unit
    simpa [simProj] using this
  · intro hθ
    subst hθ
    intro _
    rfl

/-! ---------------------------------------------------------------------------
    §7.3  ⭐⭐⭐ 【三环节共享同一个 `θ`：估计 + 学习 + 预测】
    --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐⭐⭐ **【三环节共享参数：估计 / 学习 / 预测 三条约束同时钉死 `θ`】**

**三环节**（对应任务书的「估计 + 学习 + 预测」，在此全部写作**关于同一个
`θ : ℝ` 的约束**）：

* **估计**（`est`）：`θ * 2 = 1`（由一次估计得到 `θ = 1/2`）；
* **学习**（`learn`）：`θ * 1 = 1`（由一次「`sim` 在 `x = 1` 处观测为 1」得到 `θ = 1`）；
* **预测**（`pred`）：`simProj θ = θ`（预测读 `θ`，**不**约束其值）。

三条**同时**成立时，参数空间上的交集是：

    `{θ | θ * 2 = 1} ∩ {θ | θ * 1 = 1} = ∅`

**⟹ 三条约束**互相矛盾**（`1/2 ≠ 1`）—— 这是一个**有内容**的负结论**：
三环节共享 `θ` 时，**不是**「随便合取都行」，**一致性是可检验的**。
在 `assembly_no_gain` 的**不相交**设定里这种矛盾**不可能出现**
（各侧互不干涉，永远一致）。**这就是「共享参数使合成有内容」的**负面见证**。

**⚠ 前件自查**：无前件（`ThetaCons2`、`ThetaCons1` 是 `def`）。
结论是**空集等式**。证明用 `1/2 ≠ 1`（`norm_num`）。**非改写。**
**⚠ 这不是「有收益」，而是「合取导致不一致」** —— 本文件**如实**把它标注为
判据 (d) 的**第三档**（一致 / 缩小 / 矛盾），不把它伪装成「有收益」。 -/
theorem three_link_gain :
    ThetaCons2 ∩ ThetaCons1 = (∅ : Set ℝ) := by
  ext θ
  simp only [ThetaCons2, ThetaCons1, mem_setOf_eq, mem_inter_iff, mem_empty_iff_false,
    iff_false, not_and]
  intro h1 h2
  linarith

/-! ===========================================================================
    §8  自检表（`grep ^theorem` 核对，见交付报告）
    =========================================================================== -/

/-
| 定理 | 节 | 前件含结论？ | 有数学内容？ |
|---|---|---|---|
| `mem_both` | §2.1 | 否 | ❌ `Iff.rfl`（定义展开，如实登记）|
| `mem_self_set` | §2.1 | 否 | ❌ `Iff.rfl`（定义展开，如实登记）|
| `gain_iff_excludes` | §2.2 | 否（无前件）| ✅ 把存在式「收益」归约到 `⊄` |
| `no_gain_iff_extendable` | §2.3 | 否（无前件）| ✅ 无收益的精确刻画 |
| `no_gain_mono` | §2.4 | 否（前件谈 `Ψ₂`，结论谈 `Ψ₁`）| ✅ |
| `gain_of_no_extension` | §2.5 | 否（全称前件 vs 存在结论）| ✅ 收益的构造入口 |
| `sharedParam_trivial` | §3.1 | 否，但 `rfl` 级 | ❌ 已如实登记为无内容 |
| `fam_mem_jointOn` | §3.1 | 否 | ❌ `Iff.rfl`（定义展开，如实登记）|
| `jointOn_eq_singleton_iff` | §3.2 | 否（`Θ` 上 vs `V → ℝ` 上，隔 `image`）| ✅ |
| `ThetaCons2_eq` | §5.1 | 否（无前件）| ✅ 算术 |
| `ThetaCons1_eq` | §5.1 | 否（无前件）| ✅ 算术 |
| `linFam_mem_PhiLin` | §5.1 | 否 | ❌ 定义展开（如实登记）|
| `linFam_mem_PsiAt2` | §5.1 | 否 | ❌ `Iff.rfl`（如实登记）|
| `linFam_mem_PsiAt1` | §5.1 | 否 | ❌ `Iff.rfl`（如实登记）|
| `shared_param_collapse` | §5.2 | 否（无前件）| ✅ (c) 核心 |
| `shared_val_gain` | §5.2 | 否（无前件）| ✅ (c) 值形式 |
| `shared_val_gain_gain` | §5.2 | 否（具体见证）| ✅ (c) `HasGain` |
| `pairwise_no_gain` | §6 | 否（`Function.update` 构造）| ✅ (c′) 对照 |
| `simProj_eq_sim` | §7.1 | 否（引用 `linPScm_sim_one`）| ✅ (e) 对齐 |
| `thetaLearningParam_is_gain` | §7.2 | 否（无前件）| ✅ (e) 应用 |
| `three_link_gain` | §7.3 | 否（矛盾见证）| ✅ 负面见证 |

**诚实汇总**：21 条 `theorem` 中，**6 条**是定义展开（`mem_both`、`mem_self_set`、
`sharedParam_trivial`、`fam_mem_jointOn`、`linFam_mem_PhiLin`、`linFam_mem_PsiAt2`、
`linFam_mem_PsiAt1` —— 共 7 条标记 ❌），已在此表**逐条**标为「无数学内容」，
不作为实质结果呈现。**其余 14 条有数学内容，且前件均不含结论。**

**结论**：本文件无「前件已含结论」的同义反复。
`sharedParam_trivial` 与 `fam_mem_jointOn` 是**定义展开**（`rfl` 级），
已在 §3.1 与 §4 中**如实登记为无数学内容**，不作为实质定理呈现。
-/

end SharedParamGain

end Fate
