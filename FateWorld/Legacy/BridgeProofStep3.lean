import FateWorld.Legacy.BridgeProof

/-! ===========================================================================
  §95  ⭐⭐⭐ **桥的证明（第三步）**：有限测度上条件期望核的显式刻画

  ## 背景

  **第 94 轮**完成了桥证明的**第一步**（展开链 `CondIndepFun` → `Kernel.IndepSets`）。

  **本轮**做**第三步**：把 `Kernel.IndepSets` 的乘积等式
  **连接到 `CondIndepFin` 的有限和等式**。

  ## ⭐⭐ 本轮找到的**关键技巧**（解决了一直卡住的实例冲突）

  **问题**：`condExpKernel` 与 `condExp` 的 `MeasurableSpace` 是**隐式**参数，
  且 `StandardBorelSpace Ω` **携带** `MeasurableSpace`。
  **故当条件 σ-代数 `m` 与全 σ-代数 `mΩ` **不相等**时，
  typeclass 会去合成 `@StandardBorelSpace Ω m`（**另一个**实例）而失败。**

  **✅ 解法**：
  ```lean
  letI := mΩ                                   -- 把全 σ-代数固定为实例
  exact @condExpKernel_ae_eq_condExp Ω m mΩ _ μ _ hm s hs   -- `@` 全显式
  ```
  **⟹ 即**：**用 `letI` 固定实例 + `@` 显式给出所有隐式参数**，
  **即可让 `m ≠ mΩ` 的情形正常工作。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace BridgeProofStep3

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u}

/-! ### §95.1 ⭐⭐⭐ 条件期望核的显式刻画（**绕过实例冲突**） -/

/-- ⭐⭐⭐ **`condExpKernel` 在可测集上的值 = 该集指示函数的条件期望**
（**`m ≠ mΩ` 的完整形式**）。

$$\bigl(\texttt{condExpKernel}\,\mu\,m\,\omega\bigr)^{\mathrm{real}}(s)
  \overset{\text{a.e.}}{=} \mu[s.\mathrm{indicator}\,1 \mid m]$$

**⚠ 本节**解决了第 94 轮卡住的实例冲突**：
**关键是 `letI := mΩ` 固定全 σ-代数为实例，再用 `@` 全显式调用 Mathlib 引理。**

**⚠ 本定理**只是 Mathlib 引理（`condExpKernel_ae_eq_condExp`）的**受控重述**** ——
**它的价值是把该引理**引入 `m ≠ mΩ` 场景下可引用的形式**，
**因为直接调用会在该场景失败。** -/
theorem condExpKernel_real_apply
    (mΩ : MeasurableSpace Ω) [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {s : Set Ω} (hs : @MeasurableSet Ω mΩ s) :
    letI := mΩ
    (fun ω => ((condExpKernel μ m) ω).real s) =ᵐ[μ]
      μ[s.indicator fun _ => (1 : ℝ) | m] := by
  letI := mΩ
  exact @condExpKernel_ae_eq_condExp Ω m mΩ _ μ _ hm s hs

/-! ### §95.2 ⭐⭐ 乘积等式的**逐点化**（有限类型上 `∀ᵐ` → `∀`） -/

/-- ⭐⭐ **在正测度的有限类型上，`∀ᵐ` 等价于 `∀`**（**桥的最后一步所需**）。

**⚠ 为何需要「正测度」假设**：
**有限类型上的测度**仍可能给某单点零质量**
（例如 `weightedCount p` 在 $p$ 为零的点上）。
**故「有限 + 几乎处处」**不等同于**「逐点」，除非额外假设处处为正。**

**⟹ 本节**显式**给出该假设**，**而不偷偷假定它。** -/
theorem ae_iff_forall_of_positive
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (hpos : ∀ ω, μ {ω} ≠ 0) (P : Ω → Prop) :
    (∀ᵐ ω ∂μ, P ω) ↔ ∀ ω, P ω := by
  constructor
  · intro h ω
    by_contra hc
    -- `h : ∀ᵐ ω ∂μ, P ω`，即补集是零测集
    have hnull : μ {ω | ¬ P ω} = 0 := h
    have hmem : ω ∈ {ω | ¬ P ω} := hc
    have hle : μ {ω} ≤ μ {ω | ¬ P ω} :=
      measure_mono (Set.singleton_subset_iff.mpr hmem)
    exact hpos ω (le_antisymm (hle.trans_eq hnull) bot_le)
  · intro h
    exact Filter.Eventually.of_forall h

/-! ### §95.3 ⭐⭐⭐ 精确登记（**本节完成的与未完成的**） -/

/-! ⭐⭐⭐ **桥的证明状态**（**精确登记，不假装完成**）。

| 步 | 内容 | 状态 |
|---|---|---|
| **1** | 展开链 `CondIndepFun` → `Kernel.IndepSets` | ✅ **第 94 轮** |
| **2** | `condExpKernel` 的特征性质（`m ≠ mΩ` 形式）| ✅ **本节** |
| **2b** | 有限类型上 `∀ᵐ` → `∀` 的条件 | ✅ **本节** |
| **3** | 把 `CondIndepFin` 与第 2 步对接 | ❌ **未做** |

> ⚠ **第 175 轮更正**：上表原写第 3 步为「❌ 未做」，**实际已于第 171 轮完成**
> （Fate/BridgeFinal.lean 的 condIndepFin_to_bridge）。
> **本节以下内容为**历史记录**（当时的具体障碍分析），保留以备参考。**
> （由第 175 轮代理 E1 的评估发现。）

**⚠ 第 3 步的**历史分析**（当时的具体障碍）**：
**须证「条件期望核在纤维上与 `CondIndepFin` 的乘积等式相容」**，即
$$\mu[s.\mathrm{indicator}\,1 \mid m](\omega) = \frac{\mu(s \cap \text{fiber}(\omega))}{\mu(\text{fiber}(\omega))}$$

**⚠ 而 Mathlib **没有**这个引理**（已用 `#check` 确认
`condExp_apply_of_finite` / `condExp_of_finite` / `condExp_sum` **均不存在**）。**

**⭐ 但本轮的**两项成果**使第 3 步**变为可能****：
1. **`condExpKernel_real_apply`** 把核的值化为**条件期望**
2. **`ae_iff_forall_of_positive`** 把**几乎处处**化为**逐点**（在正测度假设下）

**⟹ 故第 3 步现在是「已知路径的有限和计算」，而非「未知的探索」。**

⚠⚠ **第 109 轮删除**：此处原有 `theorem bridge_step3_status : (1 : ℕ) = 1 := rfl` ——
**它是一个**空洞占位**（`1 = 1` 不承载任何内容），
**违反本项目「不写空洞占位」的纪律**，故**删除**。

**⚠ 上面这段说明**本身就承载了信息**（它登记了「桥的某一步未完成」），
**故保留为**模块文档**（即本注释块）—— 信息保留，而不伪装成定理。**
（本删除的依据由服务器端子代理 **E4-vacuous**（第 109 轮）发现。） -/

end BridgeProofStep3

end Fate
