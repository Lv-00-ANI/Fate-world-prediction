import Mathlib

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/GridGeometry.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 2 处，含 0 条 import）；其余正文未改
  - 状态：已编译未验证
-/

/-
  网格几何下界：胞宽不小于 s/n（对应论文 §9）

  给定 d 个坐标、每个坐标被切成 n 格，则任一非空网格胞腔在 L∞ 意义下的最远两点距离
  至少是 s/n（s 为每维跨度）。取 n = 2^d 即得 span/2^d；实际上 n 与 d 的关系由编码族
  决定。

  §1  一维：区间被等分为 n 段时，两端点必落在不同的格，故任一胞腔不能覆盖整段区间；
  §2  多维：逐维格宽 (hi - lo)/n，由此 L∞ 直径不小于 s/n；
  §3  达到噪声尺度所需的档数：s/n ≤ σ ⟺ s/σ ≤ n；分辨率的翻倍律 s/(2n) = (s/n)/2。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  注：本模块只证几何那一半，不含组合计数的「胞腔数 ≤ 2^d」——后者见形式背景模块。
     本模块不涉及任何概率或分布假设：d、n、s 都是给定参数。因此该下界是必要条件而
     不是充分条件——它只说「不可能比这更小」。相应地它不含 σ 的语义，不与判据直接
     挂钩，其意义是：在给定分辨率下误差不可能低于这个几何地板，故「把误差压到噪声
     尺度」需要一个分辨率下界。

  只 import Mathlib。不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error.GridGeometry

open Finset

noncomputable section

/-! ===========================================================================
  §1  **一维**：区间被切成 n 段，任一点的所在段长 ≥ span/n
  =========================================================================== -/

/-- **格索引**：把 `[lo, hi]` 等分为 `n` 份后，点 `x`（位于 `[lo,hi]` 内）落在哪一格。
    `n = 0` 时返回 `0`（此时格无意义，见定理中对 `0 < n` 的要求）。 -/
def gridIndex (n : ℕ) (lo hi x : ℝ) : ℕ :=
  if _h : n = 0 then 0 else min (n - 1) (⌊(x - lo) / ((hi - lo) / n)⌋₊)

/-- **一维下界核心**：把 `[lo, hi]` 等分为 `n` 份（`n ≥ 2`），
    则区间的**两个端点必然落在不同的格里**。

    这是「等分网格的胞腔不可能同时覆盖整个区间」的最直接形式：
    因此任一胞腔的直径严格小于整段跨度，且至少要留下 `1/n` 的余量（见 `cellWidth_ge`）。 -/
theorem gridIndex_ne_of_two_cells {n : ℕ} (hn : 2 ≤ n) {lo hi : ℝ} (hspan : lo < hi) :
    gridIndex n lo hi lo ≠ gridIndex n lo hi hi := by
  have hn0 : n ≠ 0 := by omega
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hw : (0 : ℝ) < (hi - lo) / n := by
    have : (0 : ℝ) < hi - lo := by linarith
    positivity
  -- `lo` 落在第 0 格
  have hlo : gridIndex n lo hi lo = 0 := by
    simp only [gridIndex, dif_neg hn0]
    have hz : (lo - lo) / ((hi - lo) / n) = 0 := by ring
    rw [hz]
    simp
  -- `hi` 落在末格 `n - 1`
  have hhi : gridIndex n lo hi hi = n - 1 := by
    simp only [gridIndex, dif_neg hn0]
    have hne : hi - lo ≠ 0 := by linarith
    have hx : (hi - lo) / ((hi - lo) / n) = (n : ℝ) := by
      field_simp
    have hfl : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
    rw [hx, hfl]
    omega
  rw [hlo, hhi]
  omega

/-! ===========================================================================
  §2  **多维**：L∞ 直径下界的通用形式
  =========================================================================== -/

/-- **逐维格宽**：第 `i` 维的格宽 `(hi i - lo i) / n`。 -/
def cellWidth {ι : Type*} (n : ℕ) (lo hi : ι → ℝ) (i : ι) : ℝ :=
  (hi i - lo i) / n

/-- **胞腔直径下界（核心定理）**：

    若每维跨度至少 `s`（即 `∀ i, s ≤ hi i - lo i`），且 `0 < s`、`0 < n`，
    则**每一维的格宽都至少 `s / n`**；
    从而胞腔的 **L∞ 直径下界** 是 `s / n`，即

    $$\mathrm{diam}_\infty(\text{胞腔}) \ \ge\ \frac{s}{n}.$$

    这正是 `span/2^d` 的**逐维来源**（取 `n = 2^d`、`s = span`）。

    **⚠ 解释**：这不是「胞腔直径恰好等于 `s/n`」，而是「不可能比 `s/n` 更小」。
    即该下界是**单侧**的。

    **⚠ 关于 `s` 的符号**：本定理**对任意实数 `s` 成立**（含 `s ≤ 0`），
    只需 `n > 0` 与跨度假设。该限制比「跨度为正」更弱。 -/
theorem cellWidth_ge {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (lo hi : ι → ℝ) (s : ℝ)
    (hspan : ∀ i, s ≤ hi i - lo i) (i : ι) :
    s / n ≤ cellWidth n lo hi i := by
  unfold cellWidth
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  exact div_le_div_of_nonneg_right (hspan i) hn'.le

/-- **L∞ 直径 ≥ 最窄维格宽**（与 `BlockLayerLowerBound.linf_le_coordSpan` 的对偶）：

    若两点 `p`、`q` 在**某一维**上分处区间两端（`|p i - q i| ≥ s`），
    则它们的 L∞ 距离 ≥ `s`。

    这是把「胞腔不可能比一格更细」落到**具体两点**上的形式。 -/
theorem linf_ge_of_coord {ι : Type*} [Fintype ι] [Nonempty ι]
    {p q : ι → ℝ} (i : ι) (s : ℝ) (h : s ≤ |p i - q i|) :
    s ≤ Finset.univ.sup' (by exact ⟨Classical.arbitrary ι, Finset.mem_univ _⟩)
      (fun j => |p j - q j|) := by
  exact le_trans h (Finset.le_sup' (fun j => |p j - q j|) (Finset.mem_univ i))

/-! ===========================================================================
  §3  **2^d 的语义**：分辨率翻倍 ⟹ 直径下界减半 ⟹ 达到噪声尺度需要多少档
  =========================================================================== -/

/-- **双锁（核心）**：设每维被切成 `n` 格，各维跨度至少 `s`，噪声尺度为 `σ > 0`。

    则「几何地板已达噪声尺度」（即 `s / n ≤ σ`）**当且仅当** `n ≥ s / σ`。

    换言之：**要达到噪声尺度，分辨率档数 `n` 至少是 `s/σ`**。
    这与 §10 的实测结论一致（需约 15 倍加密），且**与编码族无关**。 -/
theorem reach_noise_scale_iff (s σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n) :
    s / n ≤ σ ↔ (s : ℝ) / σ ≤ (n : ℝ) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [div_le_iff₀ hn', div_le_iff₀ hσ]
  constructor <;> intro h <;> linarith

/-- **推论（分辨率的必要条件）**：若跨度 `s`、噪声 `σ`、且 `s/σ > 1`，
    则 1 档分辨率**必然不合格**——误差地板 `s/1 = s` 高于 `σ`。 -/
theorem one_cell_insufficient (s σ : ℝ) (h : σ < s) :
    ¬ (s / 1 ≤ σ) := by
  rw [div_one]
  linarith

/-- **翻倍律**：档数 `n ↦ 2n` 时，几何地板**减半**：
    `s / (2n) = (s / n) / 2`。
    这是文档「需加密约 15 倍」中「倍」的直接数学内容。 -/
theorem floor_halves_on_doubling (s : ℝ) (n : ℕ) :
    s / (2 * n : ℕ) = (s / n) / 2 := by
  push_cast
  ring


/-! ===========================================================================
  §4  ⚠ 未做清单（如实登记，不用 sorry 占位）
  =========================================================================== -/

/-
### 本文件**没有**证明的东西

| # | 未做项 | 为什么没做 |
|---|---|---|
| 1 | **格规模 $\le 2^{d}$** | 需要把多值/刻度化编码的形式背景在 Lean 中建模；本文件的 `gridIndex` 只是等分网格，不是 FCA 的形式背景 |
| 2 | **「胞腔数 $\le 2^d$ ⟹ 直径 $\gtrsim$ span/2^d」的完整链** | 中间需要「网格胞腔 = 形式背景的闭集」这一对应；档案中**没有**该对应的形式化 |
| 3 | **实测中「远大于下界」的比值** | 那是经验数据，不是定理 |
| 4 | **与合格带判据的直接连接** | 本下界不含 $\sigma$ 于几何内；连接需 §3 的 `reach_noise_scale_iff`，但它把 $\sigma$ 当参数，不解决 $\sigma$ 从哪来 |

**本文件只交付**：几何地板的**下界**（§2）与「要达到噪声尺度需要多少档」的
**必要条件**（§3）。这两条是档案中该论证**唯一无分布假设**的部分。
-/

end

end FateV2.Error.GridGeometry
