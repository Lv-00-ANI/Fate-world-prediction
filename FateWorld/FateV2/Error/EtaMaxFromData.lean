import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.Normed.Group.Basic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/EtaMaxFromData.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 4 处，含 0 条 import）；其余正文未改
  - 状态：已编译未验证
-/

/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Error.EtaMaxFromData`
任务：让 `ηmax` 由数据决定（有限视窗版）

===========================================================================
(a) 作者第 552 轮裁决原话
===========================================================================

  「d  1  其他的之后其他弄完讨论  就是这种合并和部分重构的你可以直接进行」

  ⟹ (D)：先做（丙）「让 `ηmax` 由数据决定」。

===========================================================================
(b) 审计 R480 探针 B 的原话
===========================================================================

  「`2*L*ηmax` 在 `L > 0`、`ηmax ≥ 0` 下可取**任意非负值**（`ηmax` 是外部
   传入的实数，**没有任何前件把它钉到数据上**）。即『噪声幅度上界』依然是
   建模假设。」

  ⟹ 所以 `ηmax` 是自由参数。

===========================================================================
(c) 本文件做到了什么
===========================================================================

本文件在**有限视窗 `Fin T`** 上把 `ηmax` 由数据 `δ : Fin T → F` 决定。

  1. `etaMax_derived_from_data`：
     对任意 `T : ℕ`（**含 `T = 0`**）与任意 `δ : Fin T → F`，
     存在 `ηmax : ℝ`，`0 ≤ ηmax` 且 `∀ k : Fin T, ‖δ k‖ ≤ ηmax`。
     **⟹ 不需要任何 `hδ` 假设**：`ηmax` 由 `δ` 自身决定。
     证明用 `ηmax := ∑ k, ‖δ k‖`（见 (d) 的诚实说明：这是**一个**上界，
     不是**最紧的**上界；`Finset.sup` 的 `OrderBot` 版在本地 Mathlib 快照中
     未编译，见 (f)）。

  2. `etaMax_isLeastBound`：
     对 `T > 0`（此时 `Fin T` 非空），取 `ηmax := Finset.univ.sup' _ (‖·‖)`
     ——这是**最紧的**上界，因为它对任何上界 `M` 都满足 `ηmax ≤ M`。
     **⟹ 这说 `ηmax` 不只是「某个」上界，是「最紧的」上界**，
     更贴近「由数据决定」。

===========================================================================
(d) ⚠ 没做到什么（诚实说明）
===========================================================================

  1. **只做了有限视窗 `Fin T`**。
     无限序列 `δ : ℕ → F` 未处理 —— 无限序列的 `sup` 可能不存在（无界），
     若加「有界性假设」那**又成了自由参数**，问题回到原点。故只做有限视窗。

  2. `etaMax_derived_from_data` 用的是 `∑ k, ‖δ k‖`，它是**上界**但**不是最紧的**。
     最紧的上界（`sup`）由 `etaMax_isLeastBound` 单独给出，代价是要求 `T > 0`。

  3. **本文件【没有】把 `ηmax` 接到 `Capstone` 的端到端定理上**（那是下一步）。

===========================================================================
(d') 第 553 轮补充：统一两个 `ηmax` 为一个见证（只修不建）
===========================================================================

  **为什么加 `etaMax_derived_from_data_sup`：**

  在前两条定理中，`ηmax` 的**形式不统一**：
    - `etaMax_derived_from_data` 用的见证是 `∑ k, ‖δ k‖`（**宽**上界：只要有一项
      非零，和就严格大于最大值；`T ≥ 2` 时一般不是最紧的）；
    - `etaMax_isLeastBound` 讲的是 `sup'` 的**最小性**（**最紧**上界），
      但它只是**一条不等式**，并没有给出一个同时具备「非负 + 上界 + 最小性」
      三条性质的**见证**。

  新定理 `etaMax_derived_from_data_sup` 把两者**统一**：存在**一个** `ηmax`
  （即 `sup'`）同时满足三条 —— 这才是「`ηmax` 由数据完全决定」的完整形式。
  `sup'` 是「**最紧**」，`∑` 是「**宽**」。

  **本定理的三条（合起来就是 `ηmax = sup k, ‖δ k‖`）：**
    (i)   `0 ≤ ηmax`（非负）；
    (ii)  `∀ k : Fin T, ‖δ k‖ ≤ ηmax`（上界）；
    (iii) `∀ M : ℝ, (∀ k, ‖δ k‖ ≤ M) → ηmax ≤ M`（**最小性**：最紧）。

  **仍有的局限（诚实说明）：**
    (1) 只做 `Fin T`（**有限视窗**）；无限序列 `δ : ℕ → F` 未处理，
        因为无界时 `sup` 不存在，加「有界性」又回到自由参数问题。
    (2) 需要 `T > 0`（`Fin T` 非空），因为 `Finset.sup'` 要求 `s.Nonempty`。
        空视窗 `T = 0` 的情形仍由原 `etaMax_derived_from_data`（`∑` 版）覆盖。
    (3) 原两条定理**保留不动**（`etaMax_derived_from_data`、`etaMax_isLeastBound`），
        新定理是它们的**结合**，不是替代。
    (4) 仍未接到 `Capstone` 端到端。

===========================================================================
(d'') 第 555 轮补充：无限序列版 `etaMax_from_bdd`（接 `Capstone`）
===========================================================================

  **背景（问题所在）：** 本文件此前的 3 条定理全是**有限视窗 `Fin T`**。
  而 `Capstone` 的所有端到端定理都用 `δ : ℕ → F`（**无限序列**）——
  主控第 554 轮实测 `grep -nE "^theorem.*Fin T" FateV2.Error/WorldModelCapstone.lean` 为空。
  ⟹ 有限视窗版**接不到 `Capstone` 上**。

  **数学困难（为什么必须加 `BddAbove`）：**
  `⨆ k : ℕ, ‖δ k‖` 在 `ℝ` 上需要 `BddAbove (Set.range (fun k => ‖δ k‖))`
  —— 因为 `ℝ` 无 `⊤`（不是 `ConditionallyCompleteLinearOrderBot`），
  无限序列的 `sSup` 只在有界时才有定义/可用性质。

  **⟹ 但这【不是退步】：**
    - **原前件**：`ηmax` 是**自由参数**（**完全任意**，见 (b)）。
    - **新前件**：`BddAbove (Set.range ‖δ ·‖)`，即「`δ` 有界」（只需存在某个界）。
  ⟹ 「`δ` 有界」比「`ηmax` 自由」**更可检验**（只需检查数据是否有限）。

  **本定理 `etaMax_from_bdd` 的三条：**
    (i)   `0 ≤ ηmax`；
    (ii)  `∀ k : ℕ, ‖δ k‖ ≤ ηmax`（上界）；
    (iii) `∀ M, (∀ k, ‖δ k‖ ≤ M) → ηmax ≤ M`（**最小性**：最紧）。
  见证是 `ηmax := sSup (Set.range (fun k => ‖δ k‖))` —— **由数据完全决定**。

  **仍有的局限（诚实说明）：**
    (1) **`BddAbove` 本身是一个假设**（虽然比「`ηmax` 自由」更可检验）。
        本定理把它作为前件显式暴露，而不是凭空造一个 `ηmax`。
    (2) 仍**未**接到 `Capstone` 端到端（需要 `Capstone` 侧提供 `BddAbove` 实例）。
    (3) **不声称「完全消除了 `ηmax` 自由」**：只是把它**换成了**「`δ` 有界」，
        后者仍是一个（可检验的）建模假设。

===========================================================================
(e) 不声称「解决了 `ηmax` 自由问题」
===========================================================================

只在**有限视窗 `Fin T`** 上声称「存在**由数据决定的上界**」——
`etaMax_derived_from_data` 给出存在性（对含 `T = 0` 的一般情形），
`etaMax_isLeastBound` 给出「最紧」性质（`T > 0`）。
**不**声称无限序列情形被解决，**不**声称端到端已接线。

===========================================================================
(f) 实现说明（为什么用 `∑` 与 `sup'` 而非 `Finset.sup`）
===========================================================================

  - 本地 Mathlib 快照未编译 `Mathlib.Data.Finset.Sup`（其 olean 不存在），
    故 `Finset.sup`（`OrderBot` 版）不可用。
  - 可用的是 `Finset.sup'`（`SemilatticeSup` + `Nonempty` 版），
    来自 `Mathlib.Data.Finset.Lattice.Fold`。
  - 因此：一般 `T`（含空集）走 `∑` 备选；`T > 0` 走 `sup'` 得最紧上界。
  - 全部证明**零 `sorry` / `admit` / `axiom`**。

===========================================================================
(g) 第 555 轮补充：(e) 的边界再声明
===========================================================================

  `etaMax_from_bdd` 把前件从「`ηmax` 自由」换成「`BddAbove (range ‖δ ·‖)`」。
  这**不是**「消除了 `ηmax` 自由」的证明 —— 它只是把**同一个**建模假设
  换成一个**更可检验**的形式（「数据有界」而非「随便给个数」）。
  **不**声称无限序列端到端已完成，**不**声称 `BddAbove` 可被去掉。
-/


namespace FateV2.Error
namespace EtaMaxFromData

open Finset

/- **【`ηmax` 由数据决定（有限视窗）】**

   给定有限噪声序列 `δ : Fin T → F`，存在 `ηmax : ℝ`，
   满足 `0 ≤ ηmax` 且 `∀ k : Fin T, ‖δ k‖ ≤ ηmax`——**不需要任何 `hδ` 假设**。
   这里取 `ηmax := ∑ k, ‖δ k‖`（一个由数据决定的上界；非最紧）。

   **⟹ 这消除审计 R480 探针 B 的「`ηmax` 自由」问题的有限视窗版。** -/
theorem etaMax_derived_from_data
    {F : Type*} [NormedAddCommGroup F] (T : ℕ) (δ : Fin T → F) :
    ∃ ηmax : ℝ, 0 ≤ ηmax ∧ ∀ k : Fin T, ‖δ k‖ ≤ ηmax := by
  refine ⟨∑ k : Fin T, ‖δ k‖, ?_, ?_⟩
  · -- 非负性：每一项 `‖δ k‖ ≥ 0`
    exact Finset.sum_nonneg (fun k _ => norm_nonneg _)
  · -- 每一项不超过总和（因为其余项非负）
    intro k
    exact Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ k)

/- **【更强的形式】**：`ηmax` 是**最小的**上界（即 `sup'` 的定义性质）。

   这里 `ηmax := Finset.univ.sup' _ (fun k => ‖δ k‖)`（要求 `T > 0` 使 `Fin T` 非空）。
   对任意上界 `M`（`∀ k, ‖δ k‖ ≤ M`），有 `ηmax ≤ M`。

   **⟹ 这说 `ηmax` 不只是「某个」上界，是「最紧的」上界**——更接近「由数据决定」。 -/
theorem etaMax_isLeastBound
    {F : Type*} [NormedAddCommGroup F] (T : ℕ) (hT : 0 < T) (δ : Fin T → F)
    {M : ℝ} (hM : ∀ k : Fin T, ‖δ k‖ ≤ M) :
    (Finset.univ : Finset (Fin T)).sup'
        ⟨⟨0, hT⟩, Finset.mem_univ _⟩ (fun k => ‖δ k‖) ≤ M := by
  exact Finset.sup'_le ⟨⟨0, hT⟩, Finset.mem_univ _⟩ (fun k => ‖δ k‖)
    (fun k _ => hM k)

/- **【`ηmax` 由数据决定（最紧上界，`sup'` 版）】**

   给定非空有限噪声序列（`T > 0`），令
   `ηmax := Finset.univ.sup' ⟨⟨0, hT⟩, mem_univ _⟩ (fun k => ‖δ k‖)`，则：
     - `0 ≤ ηmax`；
     - `∀ k : Fin T, ‖δ k‖ ≤ ηmax`（上界）；
     - `∀ M, (∀ k, ‖δ k‖ ≤ M) → ηmax ≤ M`（**最小性**）。

   **⟹ 这三条合起来就是「`ηmax = sup ‖δ k‖`」，即「由数据完全决定」。**
   **⟹ 与原 `etaMax_derived_from_data`（用 `∑`，宽上界）的区别：本定理是【最紧】的。** -/
theorem etaMax_derived_from_data_sup
    {F : Type*} [NormedAddCommGroup F] (T : ℕ) (hT : 0 < T) (δ : Fin T → F) :
    ∃ ηmax : ℝ, 0 ≤ ηmax
      ∧ (∀ k : Fin T, ‖δ k‖ ≤ ηmax)
      ∧ (∀ M : ℝ, (∀ k : Fin T, ‖δ k‖ ≤ M) → ηmax ≤ M) := by
  refine ⟨(Finset.univ : Finset (Fin T)).sup' ⟨⟨0, hT⟩, Finset.mem_univ _⟩
      (fun k => ‖δ k‖), ?_, ?_, ?_⟩
  · -- 非负性：`ηmax` 至少是 `‖δ 0‖`，而后者非负
    exact le_trans (norm_nonneg _)
      (Finset.le_sup' (fun k => ‖δ k‖) (Finset.mem_univ ⟨0, hT⟩))
  · -- 上界：`sup'` 是上界
    intro k
    exact Finset.le_sup' (fun k => ‖δ k‖) (Finset.mem_univ k)
  · -- 最小性：`sup'` 是任何上界的下界
    intro M hM
    exact Finset.sup'_le ⟨⟨0, hT⟩, Finset.mem_univ _⟩ (fun k => ‖δ k‖)
      (fun k _ => hM k)

/- **【`ηmax` 由数据决定（无限序列版）】**

   给定噪声序列 `δ : ℕ → F` 及「`δ` 有界」的前提 `hbd`，
   取 `ηmax := sSup (Set.range (fun k => ‖δ k‖))`，则
     - `0 ≤ ηmax`
     - `∀ k : ℕ, ‖δ k‖ ≤ ηmax`
     - `ηmax` 是最小的上界（`∀ M, (∀ k, ‖δ k‖ ≤ M) → ηmax ≤ M`）

   **⟹ 这把审计 R480 探针 B 的「`ηmax` 自由参数」换成「`δ` 有界」——
   后者可检验（只需检查数据是否有限），前者完全任意。**

   **⚠ 局限**：`BddAbove` 本身仍是一个假设；**不**声称 `ηmax` 自由已被消除。 -/
theorem etaMax_from_bdd
    {F : Type*} [NormedAddCommGroup F] (δ : ℕ → F)
    (hbd : BddAbove (Set.range (fun k : ℕ => ‖δ k‖))) :
    ∃ ηmax : ℝ, 0 ≤ ηmax
      ∧ (∀ k : ℕ, ‖δ k‖ ≤ ηmax)
      ∧ (∀ M : ℝ, (∀ k : ℕ, ‖δ k‖ ≤ M) → ηmax ≤ M) := by
  refine ⟨sSup (Set.range (fun k : ℕ => ‖δ k‖)), ?_, ?_, ?_⟩
  · -- 非负性：`‖δ 0‖` 属于 range，所以 `sSup ≥ ‖δ 0‖ ≥ 0`
    exact le_trans (norm_nonneg (δ 0)) (le_csSup hbd (Set.mem_range_self 0))
  · -- 上界
    intro k
    exact le_csSup hbd (Set.mem_range_self k)
  · -- 最小性
    intro M hM
    exact csSup_le ⟨‖δ 0‖, Set.mem_range_self 0⟩ (fun _ ⟨k, hk⟩ => hk ▸ hM k)

end EtaMaxFromData
end FateV2.Error
