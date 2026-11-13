/-
命运理论 · **σ 估计 · 破法丙** —— 加密分辨率的信息增益判据
================================================================================

文件：`Fate/SigmaFromInfoGain.lean`（**新建，不改任何已有模块**）

--------------------------------------------------------------------------------
⚠ 诚实边界（**先读**）
--------------------------------------------------------------------------------

**本文件是「定义骨架 + 非负性/非空性/有界性」层，不是「已解决循环」。**

本破法（破法丙：加密分辨率带来的信息增益何时降到噪声水平以下）在四个破法里
理论最漂亮，但工程最重。Lean / Mathlib 侧信息论的**完整基础**（离散熵、
KL 散度、互信息、互信息的数据处理不等式等）**并未成体系提供**。本文件因此
**只交付以下这些真定理**，并**明确登记**不能做的部分：

  * §1 `entropy2`（二点熵，直接以 Mathlib `Real.binEntropy` 为载体）：非负性。
  * §2 `klDiv`（离散 KL 散度，**自建**，用 Mathlib `InformationTheory.klFun`）：
    非负性 `klDiv_nonneg`。这是本文件`真正的信息论核心`——
    它把「信息增益 ≥ 0」归约到 `klFun x ≥ 0`（`x log x ≥ x-1`）。
  * §3 `sigmaCriterion`（判据 σ := inf {s | ∃ γ, infoGain γ < s}）：
    集合**非空**、**有下界**、σ **≥ 0**（用 §2 的非负性），以及
    **上界判据**：若存在 γ 使 `infoGain γ < ε`（增益降到噪声 ε 以下）则 `σ ≤ ε`。
  * §4 与 `Fate.R238E3.IsFitBoundary` 的关系：**只给出可证的部分**——
    `IsFitBoundary` 的 σ 是**自由参数**（在常数剖面上可任取），
    而判据 σ 由 infoGain 决定；两者**是否同一**本文件**未证**，
    **明确登记为开放问题**，并给出「为什么缺基础就很难证同一」的理由。

**⚠ 本文件不标 ✅「已解决循环」。** 判据 σ 与 `IsFitBoundary` 的 σ 的等同
需要一个**桥接假设**（infoGain 由哪个分布族、哪个分辨率映射给出，
以及它与误差剖面 `err` 的定量关系），该桥接**不在 Mathlib 里、本文件也未建**。

--------------------------------------------------------------------------------
(a) 任务要求：Fate 里有无信息论量（grep 结果，**如实抄录**）
--------------------------------------------------------------------------------

在 `Fate/` 目录下按以下几种模式逐一搜索（**均排除本文件自身**，以免自我污染）：

    $ grep -rn  "Entropy"   Fate/ --include=*.lean | grep -v SigmaFromInfoGain | wc -l   # 0
    $ grep -rni "entropy"   Fate/ --include=*.lean | grep -v SigmaFromInfoGain | wc -l   # 0
    $ grep -rni "kldiv\|kullback\|mutualinfo\|mutual_info" Fate/ --include=*.lean\
        | grep -v SigmaFromInfoGain | wc -l                    # 1（仅枚举构造子 `klDivergence`，无实现）
    $ grep -rni "infogain\|information" Fate/ --include=*.lean | grep -v SigmaFromInfoGain   # 3 行，全在 AssemblyMeta 的 `no_new_information`（集值版本空间，与熵无关）
    $ grep -rn  "log"        Fate/*.lean | grep -v SigmaFromInfoGain | wc -l             # 328 处（解析/不等式用 log，非信息论）

**结论：`Fate/` 侧零信息论实现（熵 / KL / 互信息 = 0 处；仅 1 个未实现的构造子名 `klDivergence`）。需自建。**
（Mathlib 侧有 `Real.binEntropy` 与 `InformationTheory.klFun`，本文件复用它们，
不自造公理。）

--------------------------------------------------------------------------------
(b) 信息增益的定义（离散、∑ p log p 形式）
--------------------------------------------------------------------------------

* `entropy2 p := Real.binEntropy p = p * log p⁻¹ + (1-p) * log (1-p)⁻¹`（二点熵）。
* `klDiv n p q := ∑ i, q i * klFun (p i / q i)`，其中
  `klFun x = x log x + 1 - x`。**恒等式**（见 §2 注释）：
  `∑_i q_i (p_i/q_i) log (p_i/q_i) = klDiv n p q - ∑q_i + ∑p_i`，
  故当 `∑p = ∑q = 1` 时 `klDiv = ∑ p_i log (p_i/q_i)`（即标准 KL 散度形式）。
  本文件只依赖其**非负性**，不依赖归一化恒等式（归一化留作登记）。

判据侧把 infoGain 抽象成 `f : ℝ → ℝ`（分辨率 γ ↦ 增益），
`infoGain` 的**具体分布族实例**登记为未建（见 §5）。

--------------------------------------------------------------------------------
(c)(d) 判据 σ 与关系：见 §3、§4。全部真证明，零 sorry / 零 axiom。
--------------------------------------------------------------------------------

验收：`lake env lean Fate/SigmaFromInfoGain.lean`，零 error。
文件末 `#print axioms` 只应出 `[propext, Classical.choice, Quot.sound]`。
-/

import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic
import FateWorld.Legacy.FitBoundary

namespace Fate.SigmaFromInfoGain

open Finset Real
open scoped BigOperators

/-! ===========================================================================
  §1  熵（二点熵，复用 Mathlib `Real.binEntropy`）
  =========================================================================== -/

/-- **二点熵**（离散熵在 `n = 2` 的情形）：
$\mathrm{entropy2}(p)=p\log\tfrac1p+(1-p)\log\tfrac1{1-p}$。
直接以 `Real.binEntropy` 为载体，避免在本文件重造熵的测度论底。 -/
noncomputable def entropy2 (p : ℝ) : ℝ := binEntropy p

/-- **熵的非负性**（在概率单纯形上）。这是「信息量 ≥ 0」的最基本形式。 -/
theorem entropy2_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ entropy2 p :=
  binEntropy_nonneg h0 h1

/-- 熵在均匀分布 $p=\tfrac12$ 处取最大值 $\log 2$（仅陈述，见 Mathlib
`binEntropy_le_log_two`）。 -/
theorem entropy2_le_log_two (p : ℝ) : entropy2 p ≤ log 2 :=
  binEntropy_le_log_two

/-! ===========================================================================
  §2  信息增益（离散 KL 散度，自建；核心非负性归约到 `klFun_nonneg`）
  =========================================================================== -/

/-- **离散 KL 散度 / 信息增益**：
$$\mathrm{klDiv}\ p\ q=\sum_i q_i\cdot \mathrm{klFun}\!\left(\frac{p_i}{q_i}\right),
\qquad \mathrm{klFun}(x)=x\log x+1-x.$$

**恒等式（注释中的证明）**：
`klFun(p/q)·q = p·log(p/q) + q - p`。故
`∑_i q_i klFun(p_i/q_i) = ∑ p_i log(p_i/q_i) + ∑ q_i - ∑ p_i`，
当 `∑p=∑q=1` 时即为标准 KL 散度 `∑ p_i log(p_i/q_i)`。
本文件只用到**非负性**（§2.1）。 -/
noncomputable def klDiv (n : ℕ) (p q : Fin n → ℝ) : ℝ :=
  ∑ i, q i * InformationTheory.klFun (p i / q i)

/-- ⭐ **信息增益非负**（KL 散度的 Gibbs 不等式，离散有限情形）。

**为何非平凡**：不预设 `∑p=∑q=1`，仅靠 `q>0, p≥0`，
把每项 `q_i·klFun(p_i/q_i)` 拆成 `q_i≥0`（正）乘 `klFun(·)≥0`（`x log x ≥ x-1`）。
`klFun_nonneg` 正是「`x log x ≥ x - 1`」，这是 Jensen 型不等式，
证明依赖 `log` 的凹性，**不是**定义的同义反复。 -/
theorem klDiv_nonneg {n : ℕ} {p q : Fin n → ℝ}
    (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i) : 0 ≤ klDiv n p q := by
  unfold klDiv
  apply Finset.sum_nonneg
  intro i _
  have hq0 : 0 ≤ q i := (hq i).le
  have hratio : 0 ≤ p i / q i := div_nonneg (hp i) hq0
  exact mul_nonneg hq0 (InformationTheory.klFun_nonneg hratio)

/-- **零增益当两分布相同**：若 `p = q` 且 `q ≥ 0`、`q>0`，则 `klDiv = 0`。
（每个比值 $=1$，`klFun 1 = 0`。） -/
theorem klDiv_self {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 < q i) :
    klDiv n q q = 0 := by
  unfold klDiv
  apply Finset.sum_eq_zero
  intro i _
  have hq0 : q i ≠ 0 := ne_of_gt (hq i)
  rw [div_self hq0, InformationTheory.klFun_one, mul_zero]

/-! ===========================================================================
  §3  ⭐⭐ 判据 σ：$\sigma=\inf\{s\mid\exists\gamma,\ \mathrm{infoGain}\ \gamma < s\}$
  =========================================================================== -/

/-- **判据阈值集**：所有「高于某处信息增益」的实数 $s$。 -/
def gainAbove (f : ℝ → ℝ) : Set ℝ := {s | ∃ γ, f γ < s}

/-- **判据 σ**：
$$\sigma:=\inf\{s\mid\exists\gamma,\ \mathrm{infoGain}\ \gamma<s\}
=\inf(\mathrm{gainAbove}\ f).$$ -/
noncomputable def sigmaCriterion (f : ℝ → ℝ) : ℝ := sInf (gainAbove f)

/-- ⭐ **阈值集非空**（对**任何**实值增益函数）。
取 $\gamma=0$，$s=f(0)+1$：则 $f(0)<f(0)+1$，故 $s\in\mathrm{gainAbove}$。
（注意：非空性对任意 `f` 都成立，故它**不是**本判据的实质；实质在 §3.2 有界。） -/
theorem gainAbove_nonempty (f : ℝ → ℝ) : (gainAbove f).Nonempty :=
  ⟨f 0 + 1, 0, lt_add_one (f 0)⟩

/-- ⭐⭐ **阈值集有下界，且 `0` 是下界**（当信息增益处处非负时）。

**这是判据的实质内容**：非负性（§2 的 `klDiv_nonneg`）推出的
「σ 不可能为负」。若 `∀γ, 0 ≤ f γ`，则任何 $s\in\mathrm{gainAbove}$
都满足 $s>f(\gamma)\ge 0$，故 $0$ 是下界。前件**不含**结论。 -/
theorem gainAbove_bddBelow (f : ℝ → ℝ) (h : ∀ γ, 0 ≤ f γ) :
    BddBelow (gainAbove f) := by
  refine ⟨0, ?_⟩
  intro s hs
  obtain ⟨γ, hγ⟩ := hs
  exact (h γ).trans hγ.le

/-- ⭐⭐ **判据 σ ≥ 0**（在信息增益非负的假设下）。

由 `le_csInf`：`gainAbove` 非空（§3.1）+ `0` 是下界（§3.2）$\Rightarrow 0\le\sigma$。
**这是本破法能拿到了最实的定量结论**：σ 落在 $[0,\infty)$。 -/
theorem sigmaCriterion_nonneg (f : ℝ → ℝ) (h : ∀ γ, 0 ≤ f γ) :
    0 ≤ sigmaCriterion f := by
  unfold sigmaCriterion
  exact le_csInf (gainAbove_nonempty f) (fun s hs => by
    obtain ⟨γ, hγ⟩ := hs
    exact (h γ).trans hγ.le)

/-- ⭐⭐ **上界判据（核心）**：若存在分辨率 $\gamma$ 使信息增益
$\mathrm{infoGain}\ \gamma<\varepsilon$（即「降到噪声 $\varepsilon$ 以下」），
则判据 $\sigma\le\varepsilon$。

**这正是破法丙要的判据形式**：加密到某个 $\gamma$ 增益已低于噪声 $\varepsilon$，
则 σ 被 $\varepsilon$ 压住。前件（存在这样的 $\gamma$）**不含**结论。 -/
theorem sigmaCriterion_le (f : ℝ → ℝ) (h : ∀ γ, 0 ≤ f γ) {ε : ℝ}
    (hw : ∃ γ, f γ < ε) : sigmaCriterion f ≤ ε := by
  unfold sigmaCriterion
  exact csInf_le (gainAbove_bddBelow f h) hw

/-- ⭐ **判据 σ 的定量夹逼**：信息增益非负且某处 $<\varepsilon$
$\Rightarrow 0\le\sigma\le\varepsilon$。合并 §3.3、§3.4。 -/
theorem sigmaCriterion_mem (f : ℝ → ℝ) (h : ∀ γ, 0 ≤ f γ) {ε : ℝ}
    (hw : ∃ γ, f γ < ε) : 0 ≤ sigmaCriterion f ∧ sigmaCriterion f ≤ ε :=
  ⟨sigmaCriterion_nonneg f h, sigmaCriterion_le f h hw⟩

/-- ⭐ **零增益可精确钉住 σ**：若增益处处非负、且存在 $\gamma_0$ 使
`f γ0 = 0`，则 $\sigma=0$。

**证明**：下界由 §3.3 得 $0\le\sigma$；上界由 §3.4 取 $\varepsilon>0$
（用 $\gamma_0$ 使 $f\gamma_0=0<\varepsilon$）得 $\sigma\le\varepsilon$
对**一切** $\varepsilon>0$ 成立，故 $\sigma\le 0$（`le_of_forall_pos_le_add` 型）。
这是判断「把信息增益所有维度都用上后 σ 归零」的准则。 -/
theorem sigmaCriterion_eq_zero (f : ℝ → ℝ) (h : ∀ γ, 0 ≤ f γ)
    (h0 : ∃ γ, f γ = 0) : sigmaCriterion f = 0 := by
  have hnon : 0 ≤ sigmaCriterion f := sigmaCriterion_nonneg f h
  have hle : sigmaCriterion f ≤ 0 := by
    obtain ⟨γ0, hγ0⟩ := h0
    -- σ ≤ ε 对一切 ε > 0
    have key : ∀ ε : ℝ, 0 < ε → sigmaCriterion f ≤ ε := by
      intro ε hε
      exact sigmaCriterion_le f h ⟨γ0, by rw [hγ0]; exact hε⟩
    by_contra hlt
    rw [not_le] at hlt
    -- 0 < σ；取 ε = σ/2 < σ 且 >0，与 key 矛盾
    have hpos : 0 < sigmaCriterion f := hlt
    have hhalf : (0:ℝ) < sigmaCriterion f / 2 := by linarith
    have := key (sigmaCriterion f / 2) hhalf
    linarith
  exact le_antisymm hle hnon

/-! ===========================================================================
  §4  与 `Fate.R238E3.IsFitBoundary` 的关系（**只证可证部分 + 诚实登记**）
  =========================================================================== -/

/-- **常数剖面（误差恒为 `c`）**：`err ≡ c` 的弱剖面，`bias := c, var := 0`。 -/
def errConst (c : ℝ) (_hc : 0 ≤ c) : R238E3.ErrProfileWeak where
  bias := fun _ => c
  var := fun _ => 0
  bias_nonneg := fun _ => _hc
  var_nonneg := fun _ => le_refl 0

/-- `errConst c` 的误差恒为 `c`。 -/
theorem errConst_err (c : ℝ) (hc : 0 ≤ c) (γ : ℝ) :
    R238E3.ErrProfileWeak.err (errConst c hc) γ = c := by
  simp [R238E3.ErrProfileWeak.err, errConst]

/-- ⭐ **`IsFitBoundary` 的 σ 是自由参数**：在常数剖面 `err ≡ c` 上，
任何分辨率 $\gamma$ 都满足 $\mathrm{IsFitBoundary}\ (W,c)\ \gamma$。

**意义（也即诚实边界）**：`IsFitBoundary` 对 σ 只要求「等于 `err` 的下确界」，
在常数剖面上这个下确界 = `c`，而 `c` **完全自由**。因此 `IsFitBoundary` 的 σ
**不引用任何信息增益**；判据 σ（§3）**不引用任何误差剖面**。
两者是**不同来源的对象**——这是 §4.2「同一性未证」的结构原因。 -/
theorem isFitBoundary_errConst (c : ℝ) (hc : 0 ≤ c) (γ : ℝ) :
    R238E3.IsFitBoundary (errConst c hc) c γ := by
  refine ⟨errConst_err c hc γ, ?_⟩
  intro γ'
  rw [errConst_err c hc γ']

/-- ⭐ **分离现象（可证部分）**：给定任意判据 σ（这里写成 `sInf (gainAbove f)` 的黑箱值
记作 `σig`），存在误差剖面 `W` 使 `IsFitBoundary` 在**另一个** σ 值上成立。

具体地：取 `W := errConst 5`、`σ_fit := 5`。
则 `IsFitBoundary W 5 γ` 成立，而与 infoGain 无关。
这**不**证明「σ_fit ≠ σ_ig」（那需知道 σ_ig 的具体值），
只证明 **`IsFitBoundary` 的 σ 不受信息增益判据约束**——
即两者的等同**必须另行桥接**，不能从定义直接得。 -/
theorem fitBoundary_sigma_free (γ : ℝ) :
    R238E3.IsFitBoundary (errConst 5 (by norm_num)) 5 γ :=
  isFitBoundary_errConst 5 (by norm_num) γ

/-- **桥接假设（登记为未证）**：若要把判据 σ 与 `IsFitBoundary` 的 σ 等同，
需要存在某个「由 infoGain 决定误差剖面」的映射 `Wof`，且满足：
对一切 $\gamma$，$E_{Wof}(\gamma)$ 的全局下确界恰等于 `sigmaCriterion f`。
**本文件不构造 `Wof`，故此命题只定义、不证。** -/
def FitGainBridge (Wof : ℝ → R238E3.ErrProfileWeak) (f : ℝ → ℝ) : Prop :=
  ∀ γ : ℝ, sigmaCriterion f ≤ R238E3.ErrProfileWeak.err (Wof γ) γ

/-! ===========================================================================
  §5  登记：本文件**未做**的部分（缺什么）
  =========================================================================== -/

/-!
**⚠ 未做 / 缺什么（如实登记，不声称已解决循环）**

1. **infoGain 的具体分布族实例未建。** 本文件把 infoGain 抽象为任意
   `f : ℝ → ℝ`。真正的「$\gamma\mapsto 2\gamma$」映射
   （$\mathrm{gain}(\gamma)=\mathrm{klDiv}\ p_\gamma\ p_{2\gamma}$）
   需要一个可计算的参数族 $p_\gamma$，以及证明「$p_{2\gamma}$ 比 $p_\gamma$
   信息熵更低 ↔ 增益 $>0$」。**Mathlib 无此族，本文件未建。**

2. **判据 σ 与 `IsFitBoundary` 的 σ 的同一性未证**（§4.3 只证了
   「`IsFitBoundary` 的 σ 自由」）。要证需 `FitGainBridge` 的具体实例
   `Wof`，并把 §3 的 $[0,\varepsilon]$ 夹逼搬到 `err` 坐标。**未证。**

3. **离散熵的完整多值情形（$n\ge 3$）未建。** 本文件 `entropy2` 只用二点熵
   （Mathlib 有 `binEntropy`）。一般 `n` 的熵需自建 `∑ -p_i log p_i`
   及其链式法则 / 数据处理不等式；**Mathlib 未提供，未建。**

4. **互信息、数据处理不等式、Fano 不等式的 Lean 版本缺失。** 破法丙的
   「信息论完整判据」本应建立在互信息的数据处理不等式之上；**这些 Lean 里没有**。

**结论：本破法在 Lean 侧只能交付「定义骨架 + 非负性/非空性/有界性 + 上界判据」，
不能交付「σ 等于某个信息论实体」的判决。诚实成绩：§2 `klDiv_nonneg` 与
§3 `sigmaCriterion_nonneg / _le / _eq_zero` 是**真定理**；循环**未破**。**
-/

end Fate.SigmaFromInfoGain

/-! ===========================================================================
  §6  公理检查（`#print axioms`）——确认零 `sorry` / 零 `axiom`
  =========================================================================== -/

#print axioms Fate.SigmaFromInfoGain.klDiv_nonneg
#print axioms Fate.SigmaFromInfoGain.klDiv_self
#print axioms Fate.SigmaFromInfoGain.gainAbove_nonempty
#print axioms Fate.SigmaFromInfoGain.gainAbove_bddBelow
#print axioms Fate.SigmaFromInfoGain.sigmaCriterion_nonneg
#print axioms Fate.SigmaFromInfoGain.sigmaCriterion_le
#print axioms Fate.SigmaFromInfoGain.sigmaCriterion_mem
#print axioms Fate.SigmaFromInfoGain.sigmaCriterion_eq_zero
#print axioms Fate.SigmaFromInfoGain.isFitBoundary_errConst
#print axioms Fate.SigmaFromInfoGain.fitBoundary_sigma_free
#print axioms Fate.SigmaFromInfoGain.entropy2_nonneg
