import FateWorld.Legacy.BridgeEquiv
open MeasureTheory ProbabilityTheory

/-! ===========================================================================
  §HP  ⭐⭐⭐⭐⭐ **`hp : ∀ w, 0 ≤ p w` 是**必需**的（第 177 轮）

  ## 问题

  桥的最终定理（`Fate/BridgeFinal.lean` 的 `condIndepFin_to_bridge`）带前提
  `hp : ∀ w, 0 ≤ p w`。**这个前提能不能去掉？**

  ## 历史

  - **第 168 轮**代理 Z6 说「`hp` 必需」，理由是 `p ≡ -1` 满足 `CondIndepFin`。
    **⚠ 但这个理由**不成立**** —— 第 176 轮我证明 `weightedCount (p ≡ -1) = 0`
    （因 `ENNReal.ofReal (-1) = 0`），故 `bridgeStatement (p ≡ -1)` 的 `∀ᵐ` **空真**，
    **两边都真**，**不是反例**。
  - **第 177 轮（本节）**给出**真正的反例**。

  ## 反例

  取 `α = β = Bool`、`γ = Unit`，联合律
  $$p = \begin{pmatrix} 4 & -2 \\ -2 & 1 \end{pmatrix}$$
  即 `p((true,true),()) = 4`、`p((true,false),()) = -2`、
  `p((false,true),()) = -2`、`p((false,false),()) = 1`。

  **✅ `p` 有负值**（`pCE_has_negative`）。
  **✅ `CondIndepFin p` **成立****（`pCE_condIndepFin`）：
  `M = 4-2-2+1 = 1`、`A(true)=2, A(false)=-1`、`B(true)=2, B(false)=-1`，
  逐点验证 `p·M = A·B`：`4·1=2·2`、`(-2)·1=2·(-1)`、`(-2)·1=(-1)·2`、`1·1=(-1)·(-1)` ✓

  **❌ 但截断后**（`weightedCount` 用 `ENNReal.ofReal`，**负值变 0**）
  `p⁺ = \begin{pmatrix} 4 & 0 \\ 0 & 1 \end{pmatrix}`，
  **`CondIndepFin p⁺` **不成立****（`pCEpos_not_condIndepFin`）：
  `M⁺ = 5`、`A⁺(true)=4`、`B⁺(true)=4`，
  但 `p⁺(true,true)·M⁺ = 4·5 = 20 ≠ 16 = 4·4 = A⁺·B⁺`。

  ## 结论

  **`weightedCount` 会**丢失**负值信息** ——
  故 `CondIndepFin p`（关于 `p` 的真值）**不能**推出
  `CondIndepFin p⁺`（关于截断后的测度）。
  **⟹ `hp : ∀ w, 0 ≤ p w` **是必需的**。**

  **⭐⭐ 这解释了为何第 171 轮的最终定理必须带 `hp`** ——
  **不是技术妥协，而是**数学上必需**。**
  =========================================================================== -/

namespace Fate

/-- 反例联合律 `(4, -2; -2, 1)`（`α = β = Bool`、`γ = Unit`）。 -/
def pCE : FiniteCondIndep.FinJoint Bool Bool Unit :=
  fun w => if w.1 = (true, true) then 4 else
           if w.1 = (true, false) then -2 else
           if w.1 = (false, true) then -2 else 1

/-- ⭐⭐ **反例有负值**。 -/
theorem pCE_has_negative : ∃ w : (Bool × Bool) × Unit, pCE w < 0 := by
  refine ⟨((true, false), ()), ?_⟩
  simp [pCE]

/-- ⭐⭐⭐⭐ **`CondIndepFin pCE` 成立**（**尽管有负值**）。 -/
theorem pCE_condIndepFin : FiniteCondIndep.CondIndepFin pCE := by
  intro x y z
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [FiniteCondIndep.margXZ, FiniteCondIndep.margYZ,
          FiniteCondIndep.margZ, pCE] <;> norm_num

/-- ⭐⭐ **截断后的联合律** `p⁺ = max(p, 0)`，即 `(4, 0; 0, 1)`。 -/
def pCEpos : FiniteCondIndep.FinJoint Bool Bool Unit :=
  fun w => if w.1 = (true, true) then 4 else
           if w.1 = (true, false) then 0 else
           if w.1 = (false, true) then 0 else 1

/-- ⭐⭐⭐⭐⭐ **截断后 `CondIndepFin` **不成立**（反例的核心）。 -/
theorem pCEpos_not_condIndepFin : ¬ FiniteCondIndep.CondIndepFin pCEpos := by
  intro h
  have hh := h true true ()
  simp [FiniteCondIndep.margXZ, FiniteCondIndep.margYZ,
        FiniteCondIndep.margZ, pCEpos] at hh

end Fate
