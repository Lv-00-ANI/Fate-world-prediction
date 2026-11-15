import Mathlib

/-!
  # Error · BlockLayerLowerBound

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BlockLayerLowerBound.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Error`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  BlockLayer 网格分块：`maxdiam*` 关于 `nb` 的**下界分析**——可机检核心

  对应文档：`mvfca/LOWERBOUND-analysis.md`
  实证脚本：`mvfca/lowerbound_verify_v3.py`（结果 `mvfca/results/lowerbound_verify_v3.json`）

  ---------------------------------------------------------------------------
  本文件只把文档中**真正成立、无分布假设**的那几条落成可编译引理。
  ρ≈0.79 稠密下界 / nb_collapse≈T^(2/d) / 正地板≈Θ(v) 是**实测经验**结论，
  不在本文件中冒充定理（它们只在文档里以「实测 0 违例 / 比值区间」出现）。

  自包含：只 import Mathlib，不 import 任何 Fate 模块。
  零 sorry / admit / axiom。

  ---------------------------------------------------------------------------
  §0 结论速览
  ---------------------------------------------------------------------------
  (U) **上界（严格）**：块内任意两点的 L∞ 距离 ≤ max_i 块宽。
      `linf_le_coordSpan`：把「块」抽象为逐维区间 `[lo i, hi i]`。

  (F) **题设前提交假**：占位对 `nb` 不构成上界。
      `no_occupancy_bound`：对任意大的 `nb` 都能把两个点放进同一个块——
      「块非空 ⟹ nb^d ≤ T」的推理链断裂。

  (Z) **塌缩判据（纯计数）**：无碰撞 ⟹ 块内集合的逐维极差为 0。
      `range_zero_of_all_eq`：块内所有点相等时，任意两点的逐维差为 0。

  (P) **鸽笼的正确方向**：`T > nb^d ⟹ 必有碰撞块`（保证 `D > 0` 的**存在性**，
      不保证 `D` 的下界）。
      `pigeonhole_collision`：``Fin T ↪ Fin nb`` 存在 ⟹ `T ≤ nb`。
  --------------------------------------------------------------------------- -/

namespace FateV2.Error.BlockLayerLowerBound
open Finset

/-! ## §1 (U) 上界：块内 L∞ 直径 ≤ 每维块宽的最大者 -/

/-- 每维「块宽」的最大者：`max_i (hi i - lo i)`。 -/
noncomputable def coordSpan {ι : Type*} [Fintype ι] [Nonempty ι]
    (hi lo : ι → ℝ) : ℝ :=
  Finset.univ.sup' (by exact ⟨Classical.arbitrary ι, Finset.mem_univ _⟩)
    (fun i => hi i - lo i)

/-- **(U) 核心**：若 `p`、`q` 的每维坐标都夹在同一区间 `[lo i, hi i]` 内，
    则逐维差的绝对值的最大值 ≤ `max_i (hi i - lo i)`。
    这正是 `diam(块) ≤ 块宽`（取 `hi i - lo i = full_range/nb` 即文档的 `full/nb`）。 -/
theorem linf_le_coordSpan {ι : Type*} [Fintype ι] [Nonempty ι]
    {p q : ι → ℝ} {lo hi : ι → ℝ}
    (hp : ∀ i, lo i ≤ p i ∧ p i ≤ hi i)
    (hq : ∀ i, lo i ≤ q i ∧ q i ≤ hi i) :
    (Finset.univ.sup' (by exact ⟨Classical.arbitrary ι, Finset.mem_univ _⟩)
        (fun i => |p i - q i|)) ≤ coordSpan hi lo := by
  classical
  apply Finset.sup'_le
  intro i _
  have h1 : |p i - q i| ≤ hi i - lo i := by
    rw [abs_le]
    exact ⟨by linarith [(hp i).1, (hq i).2], by linarith [(hp i).2, (hq i).1]⟩
  refine le_trans h1 ?_
  unfold coordSpan
  exact Finset.le_sup' (fun i => hi i - lo i) (Finset.mem_univ i)

/-- 「块宽全相等且为 `w`」时，块内 L∞ 直径 ≤ `w`。 -/
theorem linf_le_of_all_widths {ι : Type*} [Fintype ι] [Nonempty ι]
    {p q : ι → ℝ} {lo hi : ι → ℝ} {w : ℝ}
    (hw : ∀ i, hi i - lo i = w)
    (hp : ∀ i, lo i ≤ p i ∧ p i ≤ hi i)
    (hq : ∀ i, lo i ≤ q i ∧ q i ≤ hi i) :
    (Finset.univ.sup' (by exact ⟨Classical.arbitrary ι, Finset.mem_univ _⟩)
        (fun i => |p i - q i|)) ≤ w := by
  classical
  have h := linf_le_coordSpan hp hq
  refine le_trans h ?_
  unfold coordSpan
  apply Finset.sup'_le
  intro i _
  exact le_of_eq (hw i)

/-! ## §2 (F) 题设前提交假：碰撞在 `nb` 任意大时仍可能 -/

/-- **(F)** 对任意块数 `nb > 0`，都能把 2 个点放进**同一块**（`nb = 0` 除外）。
    故「块非空」不给出 `nb` 的上界——题设「`nb^d ≤ T` ⟹ `nb ≤ T^(1/d)`」的前提假。 -/
theorem no_occupancy_bound (nb : ℕ) (h : 0 < nb) :
    ∃ assign : Fin 2 → Fin nb, ∀ a b : Fin 2, assign a = assign b := by
  refine ⟨fun _ => ⟨0, h⟩, ?_⟩
  intro a b
  rfl

/-- 更进一步：两个点在任意大 `nb` 下都能碰撞，且**其余块全空**（空块合法）。 -/
theorem empty_blocks_are_legal (nb : ℕ) (h : 0 < nb) :
    ∃ assign : Fin 2 → Fin nb, assign 0 = assign 1 ∧
      (Finset.image assign Finset.univ).card = 1 := by
  refine ⟨fun _ => ⟨0, h⟩, rfl, ?_⟩
  rw [show Finset.univ.image (fun _ : Fin 2 => (⟨0, h⟩ : Fin nb))
        = {⟨0, h⟩} from by
    ext x; simp [eq_comm]]
  simp

/-! ## §3 (Z) 塌缩判据：无碰撞 ⟹ 块内极差 = 0 -/

/-- **(Z)** 若块内任意两点的每维坐标都相等（极端情形：块内至多 1 点的退化极限），
    则逐维极差为 0，从而 `diam = 0`。
    这是文档 `D = 0 ⟺ q = 0` 的「⟸」方向，纯计数、无分布假设。 -/
theorem range_zero_of_all_eq {ι : Type*} [Fintype ι] [Nonempty ι]
    {p q : ι → ℝ} (h : ∀ i, p i = q i) :
    (Finset.univ.sup' (by exact ⟨Classical.arbitrary ι, Finset.mem_univ _⟩)
        (fun i => |p i - q i|)) = 0 := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rw [h i, sub_self, abs_zero]
  · have hle : |p (Classical.arbitrary ι) - q (Classical.arbitrary ι)|
        ≤ (Finset.univ.sup' (by exact ⟨Classical.arbitrary ι, Finset.mem_univ _⟩)
            (fun i => |p i - q i|)) :=
      Finset.le_sup' (fun i => |p i - q i|) (Finset.mem_univ _)
    linarith [abs_nonneg (p (Classical.arbitrary ι) - q (Classical.arbitrary ι))]

/-! ## §4 (P) 鸽笼的正确方向：`T > nb ⟹ 碰撞存在` -/

/-- **(P)** `T` 个点投进 `nb` 个块、若 `nb < T`，则必有块含 ≥2 点
    （等价地：单射 `Fin T → Fin nb` 不存在）。
    这保证「`D > 0` 的**存在性**」，但**不**给出 `D` 的下界（两点可任意近）。 -/
theorem pigeonhole_collision {T nb : ℕ} (h : nb < T) :
    ¬ ∃ assign : Fin T → Fin nb, Function.Injective assign := by
  intro ⟨assign, hinj⟩
  have hcard : T ≤ nb := by simpa using Fintype.card_le_of_injective assign hinj
  omega

end FateV2.Error.BlockLayerLowerBound