import FateWorld.Legacy.FinCondIndepMeasure

/-! ===========================================================================
  §94  ⭐⭐⭐ **桥的证明（第一步）**：展开链 + 关键中间引理

  ## 第 93 轮查明的**完整定义链**（逐层 `#print`）

  `CondIndepFun m' hm' f g μ`
    ≡ `Kernel.IndepFun f g (condExpKernel μ m') (μ.trim hm')`
    ≡ `Kernel.Indep (comap f) (comap g) ...`
    ≡ `Kernel.IndepSets {可测} {可测} ...`
    ≡ `∀ t1 t2 可测, ∀ᵐ a ∂μ, (κ a)(t1∩t2) = (κ a)(t1) * (κ a)(t2)`

  ## 第 94 轮找到的**关键引理**

  `condExpKernel_ae_eq_condExp`：
  `(condExpKernel μ m ω).real s =ᵐ[μ] μ[s.indicator 1 | m]`

  **⟹ 即**：**条件期望核在可测集上的值 = 该集指示函数的条件期望** ——
  **这正是把 `Kernel.IndepSets` 的乘积等式化为条件期望等式的桥梁。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace BridgeProof

open MeasureTheory ProbabilityTheory

universe u

variable {α β γ : Type u}

/-- ⭐⭐⭐ **`Kernel.IndepSets` 展开为逐点的乘积等式**。

这是**定义性展开**（`rfl`），但**有价值**：
它把桥的目标从**不透明的 `CondIndepFun`**
变为**可直接逐点验证的乘积等式**。 -/
theorem kernelIndepSets_iff_pointwise
    [mΩ : MeasurableSpace ((α × β) × γ)]
    (κ : Kernel ((α × β) × γ) ((α × β) × γ))
    (μ : Measure ((α × β) × γ)) :
    Kernel.IndepSets {s | MeasurableSet s} {s | MeasurableSet s} κ μ ↔
      ∀ (t₁ t₂ : Set ((α × β) × γ)), MeasurableSet t₁ → MeasurableSet t₂ →
        ∀ᵐ a ∂μ, (κ a) (t₁ ∩ t₂) = (κ a) t₁ * (κ a) t₂ :=
  Iff.rfl

/-! ### ⚠ 条件期望核的特征性质（**本轮未成功形式化，如实登记**）

Mathlib 有：
`condExpKernel_ae_eq_condExp : m ≤ mΩ → MeasurableSet s →
  (fun ω => ((condExpKernel μ m) ω).real s) =ᵐ[μ] μ[s.indicator fun _ => 1 | m]`

**⚠ 我尝试在本模块中重述它，但遇到**实例不匹配**：
`condExpKernel` 的 `MeasurableSpace` 是**隐式**参数，
而结论中的 `MeasurableSet` 用的是显式的 `mΩ`，二者不一致。

**⟹ 故我**不重述**它，而是**直接引用 Mathlib 的原名**
（下游证明可用 `condExpKernel_ae_eq_condExp`）。**
**这避免了引入一个「重述但不等价」的定理。**

⚠⚠ **第 109 轮删除**：此处原有
`theorem bridge_proof_step3_remaining : (1 : ℕ) = 1 := rfl` ——
**它是一个**空洞占位**（`1 = 1` 不承载任何内容），
**违反本项目「不写空洞占位」的纪律**，故**删除**。

**⚠ 上面这段说明**本身就承载了信息**（它记录了「桥的第 3 步未完成」及其原因），
**故改为**模块文档**（`/-! -/` 而非 `/-- -/`）——
**这样它的信息保留，而不伪装成「定理」。** -/

/-! ### §94.2 ⭐⭐⭐⭐ **`Kernel.Indep` 的**精确**展开**（**第 158 轮新增**）

**⚠⚠ 本节**更正了第 138 轮的一处**重大误判**** ——

> **第 138 轮我曾断言**：「`Kernel.Indep m₁ m₂ κ μ` **完全忽略 `m₁ m₂`**，
> 其定义就是 `IndepSets {可测} {可测}`，**即「用全部可测集」。**

**✅ 实测 `#print Kernel.Indep` 显示**：
```lean
fun (m₁ m₂ : MeasurableSpace Ω) {_mΩ} (κ : @Kernel α Ω _mα _mΩ) (μ : Measure α) =>
  @Kernel.IndepSets α Ω _mα _mΩ
    {s | @MeasurableSet Ω m₁ s}      -- ⭐ **m₁**（而非 `_mΩ`）
    {s | @MeasurableSet Ω m₂ s}      -- ⭐ **m₂**（而非 `_mΩ`）
    κ μ
```

**⭐⭐ 即**：**`m₁ m₂` **确实被使用**** ——
**`IndepSets` 的第一个参数集是「`m₁`-可测集」，第二个是「`m₂`-可测集」。**

**⚠ 第 138 轮的错误源于**只看 `IndepSets {s | MeasurableSet s} {s | MeasurableSet s}` 的简写形式**
（**那是 `MeasurableSet` 用**默认实例** `_mΩ` 时的**特例**）。**

**⭐⭐ 这个更正**对桥是**好消息****：
**因为桥里 `m₁ = comap projX`、`m₂ = comap projY`，
**⟹ 目标**只是**「`comap projX`-可测 × `comap projY`-可测」的乘积等式，
**远弱于**「全可测集」的乘积等式** —— **故桥**更容易证**！** -/

/-- ⭐⭐⭐⭐ **`Kernel.Indep` 的精确展开**（**含 `m₁`/`m₂` 的可测性**）。 -/
theorem kernel_indep_iff_pointwise_any {α β γ : Type*} [MeasurableSpace ((α × β) × γ)]
    (m1 m2 : MeasurableSpace ((α × β) × γ))
    (κ : Kernel ((α × β) × γ) ((α × β) × γ)) (μ : Measure ((α × β) × γ)) :
    Kernel.Indep m1 m2 κ μ ↔
      ∀ (t₁ t₂ : Set ((α × β) × γ)),
        MeasurableSet[m1] t₁ → MeasurableSet[m2] t₂ →
        ∀ᵐ a ∂μ, (κ a) (t₁ ∩ t₂) = (κ a) t₁ * (κ a) t₂ := by
  unfold Kernel.Indep Kernel.IndepSets
  simp only [Set.mem_setOf_eq]

end BridgeProof

end Fate

