import Mathlib

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/LipschitzTransfer.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 2 处，含 0 条 import）；其余正文未改
  - 状态：已编译未验证
-/

/-
  从胞腔宽度到误差：Lipschitz 传递及其失效（对应论文 §10.1 与 §11.6）

  几何模块只证明**胞腔宽度 ≥ s/n**（`cellWidth_ge`）。但 §11.2 的不等式
  「s/σ ≤ n」把胞腔宽度直接当成了误差界。这一步需要额外假设：

      f 是 L-Lipschitz 且两点同处一胞腔  →  |f x − f y| ≤ L·(s/n)

  本模块把这一步显式化为定理（§2–§3），并给出**失效的精确形态**（§4）：

      存在有界函数（阶跃）与落点 c，使**任意** n 下该胞腔内的常数预测都至少错 1/2。

  故没有 Lipschitz 时误差不随 1/n 衰减。这正是 §11.6 实测现象的形式对应物。

  只 import Mathlib。不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error.LipschitzTransfer

noncomputable section

/-! ===========================================================================
  §1  宽度受控的划分
  =========================================================================== -/

/-- **宽度受控的划分**：每个点属于一个直径不超过 `w` 的胞腔。

    几何模块给出的是「胞腔宽度 ≥ s/n」的下界；要把宽度变成误差界，
    需要的恰恰是**上界**，故此处单列。 -/
structure WidthCell (w : ℝ) where
  /-- 点所属的胞腔。 -/
  cell : ℝ → Set ℝ
  /-- 每个点在自己胞腔里。 -/
  mem_self : ∀ x, x ∈ cell x
  /-- 胞腔直径不超过 `w`。 -/
  diam_le : ∀ {x y : ℝ}, y ∈ cell x → |x - y| ≤ w

/-! ===========================================================================
  §2  Lipschitz 传递
  =========================================================================== -/

/-- **【主引理】Lipschitz 函数在同胞腔内的变化不超过 `L·w`。**

    这是「胞腔宽度 → 误差」的唯一桥梁，且是一条**条件**定理：
    前件 `hf` 正是 §11.6 所检验的假设。 -/
theorem lipschitz_cell_error {f : ℝ → ℝ} {L w : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|)
    (P : WidthCell w) {x y : ℝ} (hy : y ∈ P.cell x) :
    |f x - f y| ≤ L * w := by
  calc |f x - f y| ≤ L * |x - y| := hf x y
    _ ≤ L * w := mul_le_mul_of_nonneg_left (P.diam_le hy) hL

/-! ===========================================================================
  §3  达到噪声尺度所需的档数
  =========================================================================== -/

/-- **【所需档数】** 若每维跨度 `s`、`n` 档等分、Lipschitz 常数 `L`，且
`L·(s/n) ≤ σ`，则同胞腔内任取代表点造成的误差不超过 `σ`。

    这就是 §11.2 左端 `s/σ ≤ n` 的来历，也说明它只在 Lipschitz 假设下有意义。 -/
theorem cell_error_le_of_lipschitz {f : ℝ → ℝ} {L s σ w : ℝ}
    (hL : 0 ≤ L) (hf : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|)
    (P : WidthCell w) (hw : w ≤ s / n)
    {x y : ℝ} (hy : y ∈ P.cell x) (hσ : L * (s / (n : ℝ)) ≤ σ) :
    |f x - f y| ≤ σ := by
  calc |f x - f y| ≤ L * w := lipschitz_cell_error hL hf P hy
    _ ≤ L * (s / (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hw hL
    _ ≤ σ := hσ

/-- 反过来：若要保证误差不超过 `σ`，档数必须满足 `L·s/σ ≤ n`。 -/
theorem needed_bins {L s σ : ℝ} {n : ℕ}
    (hs : 0 < s) (hσ : 0 < σ) (hn : 0 < n)
    (h : L * (s / (n : ℝ)) ≤ σ) : L * s / σ ≤ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : L * s ≤ σ * n := by
    have heq : L * s = L * (s / (n : ℝ)) * n := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right h (le_of_lt hn')
  rw [div_le_iff₀ hσ]
  linarith

/-! ===========================================================================
  §4  失效：没有 Lipschitz 就不衰减
  =========================================================================== -/

/-- **阶跃函数**：`x ≥ c` 取 1，否则取 0。有界，但不 Lipschitz。 -/
def stepAt (c x : ℝ) : ℝ := if c ≤ x then 1 else 0

@[simp] theorem stepAt_of_ge {c x : ℝ} (h : c ≤ x) : stepAt c x = 1 := if_pos h

theorem stepAt_of_lt {c x : ℝ} (h : x < c) : stepAt c x = 0 := if_neg (not_le.mpr h)

/-- **落点严格落在第 `k` 档内部**：若 `c` 不是任何格点 `k/n`，则存在 `k` 使
`k/n < c < (k+1)/n`。

    这就是「阶跃点永远不会落在网格线上」的精确形式。 -/
theorem exists_strict_bin {c : ℝ} {n : ℕ} (hn : 0 < n)
    (hne : ∀ k : ℤ, (k : ℝ) / (n : ℝ) ≠ c) :
    ∃ k : ℤ, (k : ℝ) / (n : ℝ) < c ∧ c < ((k : ℝ) + 1) / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨⌊c * n⌋, ?_, ?_⟩
  · rw [div_lt_iff₀ hn']
    have h1 : ((⌊c * n⌋ : ℤ) : ℝ) ≤ c * n := by exact_mod_cast Int.floor_le (c * n)
    have hne2 : ((⌊c * n⌋ : ℤ) : ℝ) ≠ c * n := by
      intro h
      apply hne ⌊c * n⌋
      rw [div_eq_iff (ne_of_gt hn')]
      linarith
    exact lt_of_le_of_ne h1 hne2
  · rw [lt_div_iff₀ hn']
    have h2 : c * n < ((⌊c * n⌋ : ℤ) : ℝ) + 1 := by
      exact_mod_cast Int.lt_floor_add_one (c * n)
    linarith

/-- **【失效定理】任何常数预测在跨阶跃的胞腔内至少错 `1/2`。**

    设 `c ∈ (0,1)` 且不是任何格点。取跨 `c` 的那一档，其内既有函数值为 1 的
    点 `c`，也有函数值为 0 的点 `k/n`。常数预测 `v` 至多逼近其中一个，故误差 ≥ 1/2。

    因此胞腔内常数预测的误差**不随 n 衰减**，与 `L·s/n → 0` 的情形相反。 -/
theorem step_no_decay {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (n : ℕ) (hn : 0 < n) (hne : ∀ k : ℤ, (k : ℝ) / (n : ℝ) ≠ c) (v : ℝ) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ 1 / 2 ≤ |stepAt c x - v| := by
  by_cases hv : v ≤ 1 / 2
  · refine ⟨c, le_of_lt hc0, le_of_lt hc1, ?_⟩
    rw [stepAt_of_ge (le_refl c)]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · push_neg at hv
    obtain ⟨k, hk_lt, hk_gt⟩ := exists_strict_bin hn hne
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    -- 由 c < (k+1)/n 与 c > 0 得 k ≥ 0
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by
      have h := hk_gt
      rw [lt_div_iff₀ hn'] at h
      have hcn : (0 : ℝ) < c * n := mul_pos hc0 hn'
      linarith
    have hk0z : (0 : ℤ) ≤ k := by
      have : (0 : ℤ) < k + 1 := by exact_mod_cast hk1
      omega
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0z
    have hxk : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := div_nonneg hk0 (le_of_lt hn')
    refine ⟨(k : ℝ) / (n : ℝ), hxk, le_of_lt (lt_trans hk_lt hc1), ?_⟩
    rw [stepAt_of_lt hk_lt]
    rw [abs_of_neg (by linarith)]
    linarith

/-- **【推论】不存在统一的 `1/n` 衰减**：阶跃函数在每一档数下最优常数预测的误差
都至少 `1/2`，而 Lipschitz 情形给出的是 `L·s/n → 0`。 -/
theorem no_uniform_decay (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (n : ℕ) (hn : 0 < n) (hne : ∀ k : ℤ, (k : ℝ) / (n : ℝ) ≠ c) :
    ∀ v : ℝ, ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ 1 / 2 ≤ |stepAt c x - v| :=
  step_no_decay hc0 hc1 n hn hne

/-- 阶跃函数不 Lipschitz：任意 `L` 下都能找到距离任意小、函数值差为 1 的两点。 -/
theorem step_not_lipschitz (c : ℝ) (L : ℝ) :
    ∃ x y : ℝ, L * |x - y| < |stepAt c x - stepAt c y| := by
  set d : ℝ := 1 / (2 * (|L| + 1)) with hd
  have hdpos : 0 < d := by
    rw [hd]; positivity
  have hdlt : |L| * d < 1 := by
    rw [hd]
    rw [mul_one_div, div_lt_one (by positivity)]
    nlinarith [abs_nonneg L]
  refine ⟨c, c - d, ?_⟩
  have hylt : c - d < c := by linarith
  have hval : |stepAt c c - stepAt c (c - d)| = 1 := by
    rw [stepAt_of_ge (le_refl c), stepAt_of_lt hylt]
    norm_num
  rw [hval]
  have hdist : |c - (c - d)| = d := by
    rw [show c - (c - d) = d by ring, abs_of_pos hdpos]
  rw [hdist]
  have : L * d ≤ |L| * d := by
    have := le_abs_self L
    nlinarith [hdpos]
  linarith

end

end FateV2.Error.LipschitzTransfer
