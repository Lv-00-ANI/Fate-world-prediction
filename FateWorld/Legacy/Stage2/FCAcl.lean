/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.Stage2.FCAcl
阶段：阶段 2 · 主线 ③（FCA）· 闭包算子（独立文件）

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
在 `Fate.FCA` 已有的 Galois 连接地基上，建立**对象侧闭包算子**
`cl A = A'' = polarDown (polarUp A)` 的两条核心性质：

1. `cl_mono` —— **单调性**：`A ⊆ B ⟹ cl A ⊆ cl B`
2. `cl_idem` —— **幂等性**：`cl (cl A) = cl A`

---------------------------------------------------------------------------
证明要点（回答「为什么之前的写法失败」）
---------------------------------------------------------------------------
`cl` 定义时已写死 `K`（即 `def cl (A) := K.polarDown ...`，以 `variable (K)` 绑定），
故 `cl` 的**完整应用式是 `cl K A`**，而不是 `cl A`。

- `cl_mono`：不需要 `unfold cl`。因为 `cl` 是 `def`（不是 `abbrev`），
  `K.polarDown_antitone (K.polarUp_antitone h)` 的结果类型是
  `K.polarDown (K.polarUp B) ⊆ K.polarDown (K.polarUp A)`，
  与目标 `cl K A ⊆ cl K B`（定义上相等，`reducible`）**应可合对**；
  但**重写更稳**：先 `rw [cl_def K A, cl_def K B]` 把目标铺开成
  `K.polarDown (K.polarUp A) ⊆ K.polarDown (K.polarUp B)`，
  再 `exact K.polarDown_antitone (K.polarUp_antitone h)`。
  ⚠ **之前失败的原因**：`exact` 已关闭目标后仍写了后续 tactic，或
  `unfold cl` 的参数缺 `K`（`cl` 有 2 个显式参数：`K` 与 `A`）。

- `cl_idem`：目标 `cl K (cl K A) = cl K A`。
  铺开后为 `K.polarDown (K.polarUp (K.polarDown (K.polarUp A))) = K.polarDown (K.polarUp A)`。
  这**正是** `polarDown_polarUp_polarDown (K.polarUp A)` 的结论
  （三次复合律 `B''' = B'`，取 `B := K.polarUp A`），**直接 `exact` 即可**，
  无需先 `rw [polarUp_polarDown_polarUp]`。
  ⚠ **之前失败的原因**：用 `polarUp_polarDown_polarUp` 去改**内层**的 `polarDown (polarUp _)`，
  会先把目标变得与 `rfl` 期望的形状不一致（`rw` 重写的是最外层的匹配、且后目标是
  两侧都被改写成中间状态），故 `rfl` 关不掉。正确做法是直接用**下方向**的
  三次复合律 `polarDown_polarUp_polarDown`。

---------------------------------------------------------------------------
廉洁边界
---------------------------------------------------------------------------
- 本文件**无** `sorry` / `admit` / `axiom`。
- 所依赖的 Mathlib 事实（`upperPolar_anti`、`lowerPolar_anti`、
  `lowerPolar_upperPolar_lowerPolar`）在 `Fate/FCA.lean` 中
  已各以其定理名显式暴露（`polarUp_antitone`、`polarDown_antitone`、
  `polarDown_polarUp_polarDown`），本文件只**引用**。
- 本文件**不修改**任何既有文件。
-/

import FateWorld.Legacy.FCA
import Mathlib.Tactic

namespace Fate.Stage2.FCAcl

open Fate

universe u v

set_option linter.checkUnivs false

noncomputable section

variable (K : FormalCtx)

/-- ⭐⭐⭐ **Galois 闭包算子**：`cl A = (A')'`。

对对象集先取属性集 `A'`，再回到对象侧 `A''`。
这是 FCA 导出算子对 `(·)'` 两次复合所得的标准闭包算子。 -/
def cl (A : Set K.GFCA) : Set K.GFCA := K.polarDown (K.polarUp A)

/-- `cl` 的展开式（定义等式），同时说明 `cl` 的完整应用式写作 `cl K A`。 -/
theorem cl_def (A : Set K.GFCA) : cl K A = K.polarDown (K.polarUp A) := rfl

/-- ⭐⭐⭐ **单调性**：`A ⊆ B ⟹ cl A ⊆ cl B`。

`A ⊆ B` ⟹ `B' ⊆ A'`（反单调）⟹ `A''⊆ B''`（再用一次反单调）。
**两次反单调复合成单调**，这是 Galois 连接的机械后果。 -/
theorem cl_mono {A B : Set K.GFCA} (h : A ⊆ B) : cl K A ⊆ cl K B := by
  rw [cl_def K A, cl_def K B]
  exact K.polarDown_antitone (K.polarUp_antitone h)

/-- ⭐⭐⭐⭐ **幂等性**：`cl (cl A) = cl A`。

即 `A'''' = A''`，取自三次复合律 `B''' = B'` 在 `B := A' = K.polarUp A` 处的实例。 -/
theorem cl_idem (A : Set K.GFCA) : cl K (cl K A) = cl K A := by
  rw [cl_def K (cl K A), cl_def K A]
  exact K.polarDown_polarUp_polarDown (K.polarUp A)

-- 公理审计
#print axioms cl_mono
#print axioms cl_idem

end
