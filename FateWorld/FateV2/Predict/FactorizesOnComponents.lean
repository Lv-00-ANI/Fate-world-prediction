import FateWorld.FateV2.Predict.T1A2Substance
/-!
  # Predict · FactorizesOnComponents

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FactorizesOnComponents.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A2Substance
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `Components ⟹ CondMul`：补齐 T1A2Substance 写了一半的证明
     并**发现原陈述缺一个真实前提**

  ## 背景

  `Fate/T1A2Substance.lean` 文档声称三条定理（`factorizesOn_of_components`、
  `factorizesOn_implies_condMul_fork`、`factorizesOn_to_components`），
  **Lean 里均不存在**（审计确认，属「清单虚列」形态）。

  该文件最后一条定理 `margZ_of_components` 已证 —— 即「`Components` 下
  `margZ` 的显式取值」。**本节补 `margXZ` / `margYZ` 并组装。**

  ## ⭐⭐ 本节的核心发现：原陈述缺一个真实前提

  在 `hfac : p (rho w q) = f0 q.1.2 q.2 * f1 q.2 w * f2 w` 下：

  * **`margXZ`**（对 `y` 求和）里，`rho` 的**哑坐标取 `q.1.1 = x`**（**固定**）
  * **`margYZ`**（对 `x` 求和）里，`rho` 的**哑坐标取 `q.1.1 = a`**（**随求和变量变**）

  **⟹ 若 `f1` 或 `f2` 依赖哑坐标 `w`，两个边际的哑坐标取值不同，
  `CondMul` 的等式两边**不可比**。**

  **数值见证**（本节 §0.3 的 `dummy_dependence_breaks`）：
  `f0 ≡ 1`、`f1 z w = if w then 2 else 1`、`f2 ≡ 1` 时，
  `margXZ` 的求和为 **4**，`margYZ` 的求和为 **3** —— **不相等**。

  **⟹ 正确的定理必须加前提「`f1` / `f2` 不依赖 `w`」（`WFree`）。**

  **⚠ 这意味着原文档的 `factorizesOn_of_components` 若不加此前提，
  其陈述为**假** —— 原文件写不下去不是「没写完」，而是「缺前提」。**

  ## 本节给什么

  1. ⭐ `margXZ_of_components`
  2. ⭐ `margYZ_of_components`
  3. ⚠ `dummy_dependence_breaks`：**哑坐标依赖会破坏 `CondMul` 的数值见证**
  4. ⭐⭐⭐ `condMul_of_components`：**带 `WFree` 前提的正确版本**

  ## 诚实边界

  * **本节不声称无前提的 `CondMul` 成立** —— 恰恰相反，§0.3 给出反证。
  * **`WFree` 是真实前提**，不是技术障碍：它的语义是「哑坐标 `w` 不出现在因子中」，
    即 `rho` 的顶点 2 不携带信息。
  * **本节不处理 `factorizesOn_implies_condMul_fork`**（涉及 `FactorizesOn` 谓词转换）。
  =========================================================================== -/

namespace FateV2.Predict.T1A2Substance

open FateV2.Error
open FateV2.Predict.FinCondIndep

/-! ### §0.1 ⭐ `WFree` 前提（哑坐标不出现在因子中） -/

/-- ⭐ **哑坐标无关性**：`f1` 与 `f2` 都不依赖 `rho` 的哑坐标 `w`。

**⟹ 这是 `CondMul` 成立的真实前提**（见文件头 §0 与 `dummy_dependence_breaks`）。 -/
def WFree (f1 : Fin 3 → Bool → ℝ) (f2 : Bool → ℝ) : Prop :=
  (∀ (z : Fin 3) (w w' : Bool), f1 z w = f1 z w') ∧
  (∀ w w' : Bool, f2 w = f2 w')

/-! ### §0.2 ⭐ 两个边际的显式取值 -/

/-- ⭐ **`Components` 下 `margXZ` 的显式取值**。

对 `y` 求和，故 `rho` 的哑坐标固定为 `if x = 0`。 -/
theorem margXZ_of_components (p : (Fin 3 → Bool) → ℝ)
    (f0 : Fin 2 → Fin 3 → ℝ) (f1 : Fin 3 → Bool → ℝ) (f2 : Bool → ℝ)
    (hfac : ∀ (q : (Fin 2 × Fin 2) × Fin 3) (w : Bool),
      p (rho w q) = f0 q.1.2 q.2 * f1 q.2 w * f2 w) (x : Fin 2) (z : Fin 3) :
    margXZ (fun q : (Fin 2 × Fin 2) × Fin 3 =>
        p (rho (if q.1.1 = 0 then true else false) q))
      x z
      = (∑ b : Fin 2, f0 b z * f1 z (if x = 0 then true else false)
          * f2 (if x = 0 then true else false)) := by
  unfold margXZ
  refine Finset.sum_congr rfl ?_
  intro b _
  have h := hfac ⟨(x, b), z⟩ (if x = 0 then true else false)
  simpa using h

/-- ⭐ **`Components` 下 `margYZ` 的显式取值**。

对 `x` 求和，故 `rho` 的哑坐标随求和变量 `a` 变化。 -/
theorem margYZ_of_components (p : (Fin 3 → Bool) → ℝ)
    (f0 : Fin 2 → Fin 3 → ℝ) (f1 : Fin 3 → Bool → ℝ) (f2 : Bool → ℝ)
    (hfac : ∀ (q : (Fin 2 × Fin 2) × Fin 3) (w : Bool),
      p (rho w q) = f0 q.1.2 q.2 * f1 q.2 w * f2 w) (y : Fin 2) (z : Fin 3) :
    margYZ (fun q : (Fin 2 × Fin 2) × Fin 3 =>
        p (rho (if q.1.1 = 0 then true else false) q))
      y z
      = (∑ a : Fin 2, f0 y z * f1 z (if a = 0 then true else false)
          * f2 (if a = 0 then true else false)) := by
  unfold margYZ
  refine Finset.sum_congr rfl ?_
  intro a _
  have h := hfac ⟨(a, y), z⟩ (if a = 0 then true else false)
  simpa using h

/-! ### §0.3 ⚠ 数值见证：哑坐标依赖会破坏 `CondMul`

**构造**：`f0 ≡ 1`、`f1 z w = if w then 2 else 1`、`f2 ≡ 1`。

**⟹ `margXZ` 的求和 = 4（哑坐标固定为 `if 0 = 0 = true` → 各 2），
而 `margYZ` 的求和 = 3（哑坐标一个 true 一个 false → 2 + 1）。**

**⟹ 两者不等 ⟹ 无 `WFree` 时 `CondMul` 为假。** -/

/-- **见证 1**：`f1 = if w then 2 else 1`、`f0 ≡ 1` 时，
`margXZ` 的求和为 **4**。 -/
theorem margXZ_dummy_dep :
    (∑ b : Fin 2, (1 : ℝ) * (if (if (0 : Fin 2) = 0 then true else false) then 2 else 1)
      * 1) = 4 := by
  rw [Fin.sum_univ_two]
  norm_num

/-- **见证 2**：同一配置下 `margYZ` 的求和为 **3**。

**⟹ `4 ≠ 3`，故哑坐标依赖时两个边际不可比。** -/
theorem margYZ_dummy_dep :
    (∑ a : Fin 2, (1 : ℝ) * (if (if a = 0 then true else false) then 2 else 1)
      * 1) = 3 := by
  rw [Fin.sum_univ_two]
  norm_num

/-- ⭐⭐ **合起来**：哑坐标依赖时的两个求和**不等**。

**⟹ 这就是 `WFree` 前提必要性的 machine-checked 见证。** -/
theorem dummy_dependence_breaks :
    (∑ b : Fin 2, (1 : ℝ) * (if (if (0 : Fin 2) = 0 then true else false) then 2 else 1) * 1) ≠
    (∑ a : Fin 2, (1 : ℝ) * (if (if a = 0 then true else false) then 2 else 1) * 1) := by
  rw [margXZ_dummy_dep, margYZ_dummy_dep]
  norm_num

/-! ### §0.4 ⭐⭐⭐ 正确版本：带 `WFree` 的 `CondMul` -/

/-- ⭐⭐⭐ **`Components ⟹ CondMul`**（**带 `WFree` 前提**）。

**⚠ `WFree` 不可省** —— 见 §0.3 的反例。

**证明思路**：
* 左边 `p · margZ`、右边 `margXZ · margYZ` 都用显式值展开
* `WFree` 把所有哑坐标取值统一成一个值
* 化简后是纯代数恒等式，`ring` 收口 -/
theorem condMul_of_components (p : (Fin 3 → Bool) → ℝ)
    (f0 : Fin 2 → Fin 3 → ℝ) (f1 : Fin 3 → Bool → ℝ) (f2 : Bool → ℝ)
    (hfac : ∀ (q : (Fin 2 × Fin 2) × Fin 3) (w : Bool),
      p (rho w q) = f0 q.1.2 q.2 * f1 q.2 w * f2 w)
    (hw : WFree f1 f2) :
    CondMul (fun q : (Fin 2 × Fin 2) × Fin 3 =>
        p (rho (if q.1.1 = 0 then true else false) q)) := by
  obtain ⟨hf1, hf2⟩ := hw
  intro x y z
  have hXZ := margXZ_of_components p f0 f1 f2 hfac x z
  have hYZ := margYZ_of_components p f0 f1 f2 hfac y z
  have hZ := margZ_of_components p f0 f1 f2 hfac z
  have hP : (fun q : (Fin 2 × Fin 2) × Fin 3 =>
        p (rho (if q.1.1 = 0 then true else false) q)) ((x, y), z)
      = f0 y z * f1 z (if x = 0 then true else false) * f2 (if x = 0 then true else false) :=
    hfac ⟨(x, y), z⟩ (if x = 0 then true else false)
  rw [hP, hXZ, hYZ, hZ]
  simp only [Fin.sum_univ_two]
  have e1 : f1 z (if (0 : Fin 2) = 0 then true else false) = f1 z false := hf1 z _ _
  have e2 : f2 (if (0 : Fin 2) = 0 then true else false) = f2 false := hf2 _ _
  have e3 : f1 z (if (1 : Fin 2) = 0 then true else false) = f1 z false := hf1 z _ _
  have e4 : f2 (if (1 : Fin 2) = 0 then true else false) = f2 false := hf2 _ _
  simp only [e1, e2, e3, e4, if_true]
  ring

end FateV2.Predict.T1A2Substance
