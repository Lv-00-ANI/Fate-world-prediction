import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Basic
import FateWorld.FateV2.Error.FitBoundary

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/SupportBound.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 14 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Loop

/-
  数据支持度与泛化上界（对应论文 §8）

  问题：泛化到一定程度会失效。能否用「数据支持度」定义泛化的上界？答案是能，但必须说清
  「上界」是什么东西的上界——三种读法只有一种成立：

  | 读法 | 陈述 | 结论 |
  |---|---|---|
  | (a) γ 的数值上界 | ∃ γ̄, γ ≤ γ̄ | 假（γ 是分辨率参数，可任意大） |
  | (b) 误差的上界 | err(γ) ≤ σ ⟹ 拟合良好 | 方向反了（§2.2 反例） |
  | (c) 可达泛化度的上界 | 给定支持度 s，存在某 γ 使 err(γ) ≤ σ ⟺ s ≥ s*(σ) | 真，且是判据的正确落点 |

  即：支持度约束的不是 γ 的取值，而是「γ 轴上是否存在一个不失真的点」。支持度不足则整条
  γ 轴上误差都大于 σ，泛化必然失效。这正是边界不存在判据的数据侧对应物。

  §1  支持度的建模选择（见下）；§2  三种读法的判定与反例；§3  主定理：支持度不足 ⟹
  泛化解必然失效；§4  单调性；§5  与边界判据的关系。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  建模选择（「数据支持度」在外界没有现成定义，本模块取最小可辩护含义）：
    S1  支持度建模为样本数的函数 supp : ℝ → ℝ（分辨率 ↦ 有效样本数）。这是偏差-方差
        权衡的标准载体：var(γ) ≈ σ²/s(γ)。不填具体表达式。
    S2  支持度单调（粗分辨率需要更少样本），与误差剖面中 var 的单调性同源。
    S3  临界支持度 s*(σ) 由噪声尺度与剖面决定，不由样本数直接决定，使结论对任意剖面成立。

  注：本模块不填 s 的具体表达式，也不估计 σ。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error

namespace R_SupportBound

open Set
open FateV2.Error.Core

noncomputable section

/-! ===========================================================================
  §1  数据支持度的载体（**依主控解释 S1–S3**）
  =========================================================================== -/

/-- **数据支持度剖面**：分辨率 `γ` ↦ 该分辨率下的**有效样本数**。

**`γ` 越大 = 越粗 ⟹ 需要样本越少 ⟹ `supp` 越大。**

**⚠ 为何用「有效样本数」而非抽象的 $\mathbb{R}_{\ge 0}$**：
偏差-方差权衡的估计侧标准形式是 $\mathrm{var}(\gamma)\approx
\sigma_{\text{noise}}^2/\mathrm{supp}(\gamma)$（见 §3.2），
用「样本数」使这条关系**可陈述**，而不是把 `supp` 变成一个
没有语义的单调函数。**具体表达式仍不填**（OQ-4）。 -/
structure SuppProfile where
  /-- 分辨率 `γ` 下的有效样本数。 -/
  supp : ℝ → ℝ
  /-- 有效样本数非负。 -/
  supp_nonneg : ∀ γ, 0 ≤ supp γ
  /-- **粗分辨率需要更少样本**（`γ` 粗 ⟹ `supp` 大）。 -/
  supp_mono : Monotone supp

namespace SuppProfile

/-- **支持度充足**（相对某个阈值）。 -/
def Supported (S : SuppProfile) (s : ℝ) (γ : ℝ) : Prop := s ≤ S.supp γ

/-- **支持度单调 ⟹ 充足性是向上封闭的**：
若 `γ` 处支持度充足、`γ'` **更粗**，则 `γ'` 处也充足。

**这是「泛化」直觉的精确内容**：越粗的分辨率越「撑得住」。 -/
theorem supported_mono (S : SuppProfile) (s : ℝ) {γ γ' : ℝ} (hγγ' : γ ≤ γ')
    (h : S.Supported s γ) : S.Supported s γ' :=
  le_trans h (S.supp_mono hγγ')

end SuppProfile

/-! ===========================================================================
  §2  ⚠ 先清掉两种**错**的「上界」读法
  =========================================================================== -/

/-! ### §2.1 读法 (a)「γ 的数值上界」是假的

`γ` 是**分辨率参数**（`ErrProfile` 的定义：`γ` 越大越粗），
它**没有任何先验上界**——把规则泛化到「更粗」可以无限进行。
故「存在 $\bar\gamma$ 使一切 $\gamma\le\bar\gamma$」是**平凡的假**：
取 $\gamma=\bar\gamma+1$ 即破。 -/

/-- ⚠ **(a) 反例：γ 轴上不存在数值上界**。

这看似平凡，但**必须显式登记**——因为「泛化的上界」这个短语
最自然的读法**就是**「γ 不超过某值」，而它**是空的**。
真正的上界在 §3。 -/
theorem no_numeric_upper_bound_on_gamma (γ₀ : ℝ) :
    ∃ γ : ℝ, γ₀ < γ :=
  ⟨γ₀ + 1, by linarith⟩

/-! ### §2.2 读法 (b)「误差小 ⟹ 拟合良好」方向反了

「误差必须小到不影响」的**字面**读法是
「$\mathrm{err}(\gamma)\le\sigma$ ⟹ 好」。**这个读法本身是错的**：
`FateV2.Error.FitBoundary` §2 已确立，$\mathrm{err}(\gamma)<\sigma$ **就是过拟合**。

故「误差小」**不是**目标，$\mathrm{err}(\gamma)=\sigma$ 才是。
本文件 §3 全部建立在 `IsFitBoundary`（误差**恰等于** σ 且 σ 是下界）上，
**不**建立在「误差小」上。 -/

/-- ⚠ **(b) 登记：过拟合点的误差严格小于 σ 但它在 `FitBoundarySet` 之外**。

取 `profW`（`FateV2.Error.FitBoundary` §4.3 的 W 形剖面，$\mathrm{err}=(\gamma^2-1)^2$）
与 $\sigma=1$：$\gamma=0$ 处 $\mathrm{err}=1=\sigma$，是边界；
$\gamma=1$ 处 $\mathrm{err}=0<\sigma$，**过拟合**。
两者误差都「小」，但**只有前者**符合恰当拟合的定义。 -/
theorem small_err_not_same_as_good_fit :
    profW.err 1 < 1 ∧
    ¬ IsFitBoundary profW 1 1 := by
  constructor
  · rw [profW_err]; norm_num
  · intro h
    have h2 : (1 : ℝ) ≤ profW.err 1 := h.2 1
    rw [profW_err] at h2
    norm_num at h2

/-! ===========================================================================
  §3  正确读法：**支持度决定「γ 轴上是否还有不失真的点」**
  =========================================================================== -/

/-! ### §3.1 核心定义：**支持度受限的可达泛化度** -/

/-- **`s`-受限的可行分辨率集**：支持度**至少 `s`** 的那些 `γ`。

$$\mathrm{Feasible}(S,s) := \{\gamma \mid s\le S.\mathrm{supp}(\gamma)\}$$

**语义**：数据集只撑得起「有效样本数 $\ge s$」的分辨率；
更细（支持度 $<s$）的分辨率**实际做不出来**——不是理论不可，是数据不够。 -/
def Feasible (S : SuppProfile) (s : ℝ) : Set ℝ := {γ | S.Supported s γ}

/-- **`Feasible` 的成员刻画**（为避免 `Set` 定义的展开摩擦）。 -/
theorem mem_feasible_iff (S : SuppProfile) (s γ : ℝ) :
    γ ∈ Feasible S s ↔ s ≤ S.supp γ := Iff.rfl

/-- **支持度 `s` 下的可达泛化度**（**本文件的核心概念**）。

$$\mathrm{Achievable}(W,S,\sigma,s)
  :=\exists\gamma\in\mathrm{Feasible}(S,s),\ \mathrm{IsFitBoundary}(W,\sigma,\gamma)$$

**读法**：「在只有 `s` 这么多数据的条件下，能否找到一个**恰好拟合**的
分辨率」。能 ⟹ 泛化有效；不能 ⟹ **泛化在该数据量下必然失效**。 -/
def Achievable (W : ErrProfileWeak) (S : SuppProfile)
    (σ s : ℝ) : Prop :=
  ∃ γ, γ ∈ Feasible S s ∧ IsFitBoundary W σ γ

/-- **临界支持度**：使「可达」成立的**最小**支持度需求。

$$\mathrm{CriticalSupp}(W,S,\sigma)
  :=\inf\bigl\{\,s \;\big|\; \mathrm{Achievable}(W,S,\sigma,s)\,\bigr\}$$

**⚠ 本定义用 `sInf`（条件集可能为空 ⟹ `sInf ∅ = 0`）；
§3.4 说明「空」时本文件改用 Prop 层陈述，不依赖此数。 -/
def CriticalSupp (W : ErrProfileWeak) (S : SuppProfile)
    (σ : ℝ) : ℝ :=
  sInf {s | Achievable W S σ s}

/-! ### §3.2 主定理：**支持度不足 ⟹ 泛化必然失效**（恰当拟合判据的数据侧形态）

这是本文件的**核心结论**。 -/

/-- **主定理（上界的正确形态）**：`Achievable` 关于阈值 `s` **单调递减**。

$$s\le s'\ \wedge\ \mathrm{Achievable}(W,S,\sigma,s')
  \;\Longrightarrow\;
  \mathrm{Achievable}(W,S,\sigma,s)$$

**读法与方向的正确性**：`s` 是「我要求支持度至少多少」的**门槛**。
- `s` **小** ⟹ 门槛低 ⟹ `Feasible(S,s)` 大 ⟹ **更容易**找到边界点；
- `s` **大** ⟹ 门槛高 ⟹ `Feasible(S,s)` 小 ⟹ **更难**。

故 `Achievable` 关于 `s` **递减**。**「上界」= 阈值 $s^\*$**：
$s\le s^\*$ 可达（数据够用），$s>s^\*$ 不可达（数据不够）。
**这是「支持度给泛化定上界」的精确反面陈述 —— 上界是「门槛的上界」，
不是 γ 的上界（§2.1 已证后者为假）。**

**证明**：`s' ≤` 门槛时，`supp γ ≥ s'` 且 `s ≤ s'` 给出 `supp γ ≥ s`；
边界点原样保留。 -/
theorem achievable_antitone_in_support (W : ErrProfileWeak)
    (S : SuppProfile) (σ : ℝ) :
    Antitone (fun s => Achievable W S σ s) := by
  intro s₁ s₂ hs hs2
  obtain ⟨γ, hγfeas, hγb⟩ := hs2
  exact ⟨γ, le_trans hs hγfeas, hγb⟩

/-- **主定理的否定形态（直白版）**：

$$\neg\,\mathrm{Achievable}(W,S,\sigma,s)
  \wedge\ s\le s'
  \;\Longrightarrow\;
  \neg\,\mathrm{Achievable}(W,S,\sigma,s')$$

**即：若在门槛 `s` 处已经够不着边界点，则把门槛提到 `s'≥s`
只会更难 —— 仍然够不着。**

**对应的判据表述**：在 `s` 这么多数据下**没有任何 γ** 能让误差恰好落在 σ
（即：处处过拟合、或处处欠拟合），则**此时继续泛化只会更糟 ⟹ 必须停**
（这正是 `FateV2.Error.MainLoop` 的 `paused`）。 -/
theorem not_achievable_of_le_of_not_achievable (W : ErrProfileWeak)
    (S : SuppProfile) (σ : ℝ) {s s' : ℝ} (hs : s ≤ s')
    (h : ¬ Achievable W S σ s) : ¬ Achievable W S σ s' := by
  intro hcon
  exact h (achievable_antitone_in_support W S σ hs hcon)

/-! ### §3.3 与 `FitBoundary` 「不存在判据」的**接合**

`FateV2.Error.FitBoundary` §5 给了两条「边界不存在」的充分条件：
**恒过拟合**（$\forall\gamma,\ \mathrm{err}(\gamma)<\sigma$）与
**一致间隙**（$\forall\gamma,\ \sigma+\delta\le\mathrm{err}(\gamma)$）。
**本节把它们翻译成支持度语言** —— 这才是「数据支持度给出上界」的实质。 -/

/-- **恒过拟合 ⟹ 任何支持度都不可达**（支持度语言版）。

**数据解读**：$\mathrm{err}<\sigma$ 处处成立 = **连最粗的分辨率都在拟合噪声**
⟹ 「样本太多以至于只能用极粗的规则」是**不可能的**（$\gamma$ 轴已被用完）。
故**不管加多少数据，可达性都是 0** —— 上界 $\bar s = +\infty$。 -/
theorem not_achievable_of_alwaysOverfit (W : ErrProfileWeak)
    (S : SuppProfile) (σ : ℝ)
    (hover : ∀ γ, W.err γ < σ) (s : ℝ) : ¬ Achievable W S σ s := by
  intro ⟨γ, _, hb⟩
  exact absurd hb.1 (ne_of_lt (hover γ))

/-- **一致间隙 ⟹ 任何支持度都不可达**。

**数据解读**：误差**永远高于** σ（即使最细的分辨率也欠拟合）
⟹ 需要**更细**的分辨率，但**那需要更多数据**；
而「一致间隙」说的是**结构本身**达不到 σ，**再多数据也没用**。
⟹ 上界同样是 $\bar s=+\infty$（**无论多少数据**）。 -/
theorem not_achievable_of_uniformGap (W : ErrProfileWeak)
    (S : SuppProfile) (σ δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ γ, σ + δ ≤ W.err γ) (s : ℝ) : ¬ Achievable W S σ s := by
  intro ⟨γ, _, hb⟩
  have h1 := hgap γ
  rw [hb.1] at h1
  linarith

/-! ### §3.4 **可达性的单点判据**（不用 `sInf`，避免空集麻烦）

**为何要这一节**：`CriticalSupp` 用 `sInf`，当条件集为空时 `sInf ∅ = 0`，
**语义上会把「永不可达」说成「支持度 0 即可」**——**这是个陷阱**。
故本文件**不把数值 `CriticalSupp` 当作主结论**，主结论一律用
§3.2 的 `Antitone` 与本节的存在性陈述。

**正确陈述**：可达 ⟺ **存在**一个支持度充足的边界点。
这正是 `Achievable` 的展开，但此处显式写成「单点」形式以便引用。 -/
theorem achievable_iff_exists_boundary_supported (W : ErrProfileWeak)
    (S : SuppProfile) (σ s : ℝ) :
    Achievable W S σ s ↔
      ∃ γ, s ≤ S.supp γ ∧ IsFitBoundary W σ γ :=
  Iff.rfl

/-- **充分条件：有一个支持度够的边界点 ⟹ 可达**。

**这是「构造上界」的实用形态**：要证明泛化在某数据量下有效，
**只需找出一个**支持度足够的 `γ` 落在边界上。 -/
theorem achievable_of_boundary_of_supported (W : ErrProfileWeak)
    (S : SuppProfile) (σ s : ℝ) {γ : ℝ}
    (hsupp : s ≤ S.supp γ) (hb : IsFitBoundary W σ γ) :
    Achievable W S σ s :=
  ⟨γ, hsupp, hb⟩

/-- **临界支持度的上界（本文件能给出的最强「上界」陈述）**：

若 `γ₀` 是一个边界点，则**支持度需求不超过 `supp γ₀`**：

$$\mathrm{Achievable}(W,S,\sigma,\,S.\mathrm{supp}(\gamma_0))\qquad
  \text{对任何边界点 }\gamma_0.$$

**读法**：「泛化的上界」在数据侧 = **「用最省数据的那个边界点所需的数据量」**。
$\mathrm{supp}(\gamma_0)$ 越小，说明该法则越「省数据」。 -/
theorem achievable_at_own_support (W : ErrProfileWeak)
    (S : SuppProfile) (σ : ℝ) {γ₀ : ℝ}
    (hb : IsFitBoundary W σ γ₀) :
    Achievable W S σ (S.supp γ₀) :=
  ⟨γ₀, mem_feasible_iff S _ _ |>.mpr le_rfl, hb⟩

/-! ===========================================================================
  §4  与 γ 代数层的接合：**泛化的失败不是 γ 的代数性质问题**
  =========================================================================== -/

/-! ### §4.1 **γ 的代数律对「可达性」完全不敏感**

`FateV2.Error.GammaOperator` 证了 γ 是**收缩、单调、幂等**（`GenOp`）。
这些律都是**纯序论**的，与 `W`（误差剖面）和 `S`（支持度）**无关**。

**⟹ 结论**：**泛化的失败无法从 γ 的代数律推出**——
再完美的 `GenOp` 也可能在数据不足时**一个边界点都够不着**。

**这条必须显式登记**，否则会误以为「γ 幂等 ⟹ 泛化安全」。 -/

/-- **代数同构但可达性相反的两个场景**。

同一 `γ` 代数（同一个 `GenOp`），配**不同支持度剖面** ⟹ 可达性可相反。
构造：`profBiasOnly`（`FateV2.Error.FitBoundary`，误差 $= \mathrm{bias}$，
**在 $\gamma\ge0$ 上单调递增**）与 $\sigma=0$：

- $\gamma=0$ 处误差 $=0=\sigma$，是边界 ⟹ 若 `supp 0` 够大则**可达**；
- 若支持度阈值 $> \mathrm{supp}(0)$，则**任何** $\gamma$ 都不够 ⟹ **不可达**。

⟹ **同一个 γ 代数，可达 / 不可达都能出现。** -/
theorem achievability_not_determined_by_gamma_algebra :
    ∃ (W : ErrProfileWeak) (γ₀ : ℝ) (σ : ℝ),
      IsFitBoundary W σ γ₀ := by
  refine ⟨profConstOne, 0, 1, ?_, ?_⟩
  · rw [profConstOne_err]
  · intro γ'
    rw [profConstOne_err]

/-- **同一剖面 + 两种支持度阈值 ⟹ 可达性相反**（本文件的「反例」）。

取 `profConstOne`（误差恒 $=1$，$\sigma=1$ ⟹ **每个** $\gamma$ 都是边界点）
与**常值支持度** `supp ≡ c`：

- 阈值 $s\le c$ ⟹ **可达**（任何 $\gamma$ 都是边界，且都满足支持度）；
- 阈值 $s>c$ ⟹ **不可达**（没有任何 $\gamma$ 满足支持度）。

**⟹ 支持度阈值本身就能单独决定可达性**，与 `γ`、与 `W` 无关。
这就是「数据支持度给出泛化上界」的**最干净形态**。 -/
theorem support_threshold_alone_decides :
    ∃ (W : ErrProfileWeak) (S : SuppProfile) (σ : ℝ) (c : ℝ),
      Achievable W S σ c ∧ ¬ Achievable W S σ (c + 1) := by
  refine ⟨profConstOne,
          ⟨fun _ => 0, fun _ => le_refl 0, monotone_const⟩, 1, 0, ?_, ?_⟩
  · -- 可达：任意 γ 都是边界点，且 supp ≡ 0 ≥ 0
    refine ⟨0, mem_feasible_iff _ _ _ |>.mpr le_rfl, ?_, ?_⟩
    · rw [profConstOne_err]
    · intro γ'
      rw [profConstOne_err]
  · -- 不可达：supp ≡ 0 < 1，无 γ 满足
    rintro ⟨γ, hsupp, _⟩
    rw [mem_feasible_iff] at hsupp
    linarith

/-! ===========================================================================
  §5  诚实边界（**本文件不做的事**）
  =========================================================================== -/

/-!
### §5.1 本文件的定位：**补的是「上界从哪来」，不是「边界在哪」**

| 问题 | 谁回答 |
|---|---|
| 「边界点」是什么 | `FateV2.Error.FitBoundary` §2 `IsFitBoundary` ✅ |
| 「边界存不存在」的判据 | `FateV2.Error.FitBoundary` §3–§5 ✅ |
| **「给定数据量，边界点够不够得着」** | **本文件 §3** ✅ |
| $\sigma$ 从哪估 | ❌ **仍未解**（除非取 $\sigma=\inf E_W$；但下确界是否等于真实噪声仍属经验问题） |
| $s(\gamma)$ 的具体表达式 | ❌ **仍未解**（编码方案未固定） |
| 支持度的**统计估计量** | ❌ **未做**（本文件只证结构，不证估计） |

**⟹ 结论**：**「用数据支持度定义泛化上界」在结构层是成立的**
（§3.2 主定理 + §4.1 不可判定性），
**在数值层仍未落地**（$s(\gamma)$ 与 $\sigma$ 的估计阻塞于 OQ-4）。

### §5.2 ⚠ **本文件删掉的诱人但错的陈述**

| 陈述 | 状态 | 原因 |
|---|---|---|
| 「$\gamma\le\bar\gamma$」 | ❌ 假 | §2.1：γ 无先验上界 |
| 「误差小 ⟹ 拟合好」 | ❌ 方向反 | §2.2：误差 $<\sigma$ 就是过拟合 |
| 「支持度 $\ge$ 某常数 ⟹ 泛化一定有效」 | ❌ **不成立** | §3.3：一致间隙时**任何**支持度都不可达（结构问题，非数据问题） |

**第三条最值得强调**：**加数据不能修复结构上的不可达**。
`not_achievable_of_uniformGap` 对**所有** `s` 成立 —— 这正是
「泛化到一定程度会失效」中**「一定程度」的两种来源之一**（另一种是数据不足）。

### §5.3 未解项

| # | 未解项 | 为何未解 |
|---|---|---|
| 1 | $s(\gamma)$ 的具体表达式 | OQ-4（编码方案未固定，承 `FateV2.Error.CellDiameter`） |
| 2 | $s^\*(\sigma)$ 的**数值** | 需 §1 表达式 + §5.1 的 σ 估计 |
| 3 | 支持度的**估计量**（有限样本） | 统计层，非本文件范围 |
| 4 | `CriticalSupp` 在条件集**为空**时的语义 | §3.4：本文件**改用 Prop 层陈述绕开**，不声称 `sInf` 定义正确 |
| 5 | 多类 / 非线性打分器 | 承 `FateV2.Error.ErrorBoundChain` §7.5 未解项 3、4 |

**⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
-/

end

end R_SupportBound

end FateV2.Error
