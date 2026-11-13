import Mathlib

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/TightCells.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 2 处，含 0 条 import）；其余正文未改
  - 状态：已编译未验证
-/

/-
  胞腔数的紧界：`(n+1)^d` 取代 `2^(d·n)`（对应论文 §10.2）

  背景。原结果 `num_cells_le_pow` 给出 `|胞腔| ≤ 2^(d·n)`，其证明只用到「内涵是属性集的
  子集，故至多 2^(属性数) 种」。但该界**远松于实际**：对固定维 `j`，隶属集

      {i : θ_{j,i} ≤ x_j}

  只随 `x_j` 在 `n` 个阈值所划分的 `n+1` 个区间中移动而取**嵌套**的值，故每维至多
  `n+1` 种取值。于是胞腔数至多 `(n+1)^d`。

  比较（数据实测，见论文 §10.2 与相图实验）：
      d=3, n=8 :  2^24 ≈ 1.7e7   而 9^3 = 729   （实测 283）
      d=5, n=16:  2^80 ≈ 1.2e24  而 17^5 ≈ 1.4e6 （实测 400，受样本数封顶）

  本模块给出
    §1 每维的「档位」与其链结构；
    §2 链的基数界：链上基数严格增，故集合数 ≤ n+1；
    §3 胞腔数 ≤ (n+1)^d（主定理）；
    §4 与样本数的合并界 ≤ min((n+1)^d, |S|)。

  只 import Mathlib。不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error.TightCells

open Finset

noncomputable section

/-! ===========================================================================
  §1  每维的档位
  =========================================================================== -/

/-- **档位**：第 `j` 维中，阈值不超过 `x j` 的那些下标。

    这就是「`x` 落在第 `j` 维哪一个阈值区间」的离散化表示。 -/
def level {d n : ℕ} (θ : Fin d → Fin n → ℝ) (x : Fin d → ℝ) (j : Fin d) :
    Finset (Fin n) :=
  univ.filter (fun i => θ j i ≤ x j)

/-- 档位对 `x j` 单调。 -/
theorem level_mono {d n : ℕ} (θ : Fin d → Fin n → ℝ) {x y : Fin d → ℝ}
    (j : Fin d) (h : x j ≤ y j) : level θ x j ⊆ level θ y j := by
  intro i hi
  simp only [level, mem_filter, mem_univ, true_and] at hi ⊢
  exact le_trans hi h

/-- 同维的两个档位总可比较（阈值把实轴切成 `n+1` 段，故档位构成链）。 -/
theorem level_chain {d n : ℕ} (θ : Fin d → Fin n → ℝ) (x y : Fin d → ℝ) (j : Fin d) :
    level θ x j ⊆ level θ y j ∨ level θ y j ⊆ level θ x j := by
  rcases le_total (x j) (y j) with h | h
  · exact Or.inl (level_mono θ j h)
  · exact Or.inr (level_mono θ j h)

/-! ===========================================================================
  §2  链的基数界
  =========================================================================== -/

/-- **链中集合的个数 ≤ 基数的上界 + 1**。

    证明思路：沿链包含关系单调，故基数沿链严格不减；由「包含 + 基数相等 ⟹ 相等」，
    基数在链上**单射**。于是链的大小不超过基数可能的取值个数（`0 … n`），即 `n+1`。 -/
theorem card_le_succ_of_chain {n : ℕ} (C : Finset (Finset (Fin n)))
    (hchain : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) : C.card ≤ n + 1 := by
  -- 基数在 C 上单射
  have hinj : ∀ A ∈ C, ∀ B ∈ C, A.card = B.card → A = B := by
    intro A hA B hB hc
    rcases hchain A hA B hB with h | h
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq hc.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq hc)).symm
  have hcard : (C.image Finset.card).card = C.card := by
    apply Finset.card_image_of_injOn
    intro A hA B hB h
    exact hinj A hA B hB h
  -- 每个基数取值落在 0 … n
  have hsub : C.image Finset.card ⊆ Finset.range (n + 1) := by
    intro k hk
    simp only [mem_image] at hk
    obtain ⟨A, -, rfl⟩ := hk
    simp only [mem_range]
    have h1 : A.card ≤ Fintype.card (Fin n) := Finset.card_le_univ A
    simpa using h1
  calc C.card = (C.image Finset.card).card := hcard.symm
    _ ≤ (Finset.range (n + 1)).card := Finset.card_le_card hsub
    _ = n + 1 := Finset.card_range _

/-- **单维：档位的取值至多 `n+1` 种。** -/
theorem card_level_image_le {d n : ℕ} (θ : Fin d → Fin n → ℝ)
    (S : Finset (Fin d → ℝ)) (j : Fin d) :
    (S.image (fun x => level θ x j)).card ≤ n + 1 := by
  apply card_le_succ_of_chain
  intro A hA B hB
  simp only [mem_image] at hA hB
  obtain ⟨x, -, rfl⟩ := hA
  obtain ⟨y, -, rfl⟩ := hB
  exact level_chain θ x y j

/-! ===========================================================================
  §3  胞腔数 ≤ (n+1)^d
  =========================================================================== -/

/-- 内涵的「抽象版」：由档位元组直接读出。 -/
def intentOf {d n : ℕ} (t : Fin d → Finset (Fin n)) : Finset (Fin d × Fin n) :=
  univ.filter (fun a => a.2 ∈ t a.1)

/-- 内涵只依赖档位元组。 -/
theorem intent_eq_intentOf {d n : ℕ} (θ : Fin d → Fin n → ℝ) (x : Fin d → ℝ) :
    (Finset.univ.filter (fun a : Fin d × Fin n => θ a.1 a.2 ≤ x a.1))
      = intentOf (fun j => level θ x j) := by
  ext a
  simp [intentOf, level]

/-- **【主定理】胞腔数 ≤ (n+1)^d。**

    这是 `num_cells_le_pow`（`≤ 2^(d·n)`）的紧化：每维的档位只能取 `n+1` 种值，
    故档位元组至多 `(n+1)^d` 种，而内涵由档位元组决定。 -/
theorem num_cells_le_succ_pow (d n : ℕ)
    (θ : Fin d → Fin n → ℝ) (S : Finset (Fin d → ℝ)) :
    (S.image (fun x => Finset.univ.filter
        (fun a : Fin d × Fin n => θ a.1 a.2 ≤ x a.1))).card
      ≤ (n + 1) ^ d := by
  set g : (Fin d → ℝ) → (Fin d → Finset (Fin n)) := fun x j => level θ x j with hg
  -- 内涵 = intentOf ∘ g
  have hfac : ∀ x, Finset.univ.filter
      (fun a : Fin d × Fin n => θ a.1 a.2 ≤ x a.1) = intentOf (g x) := by
    intro x
    simpa [hg] using intent_eq_intentOf θ x
  -- 像的大小不超过档位元组像的大小
  have himg : (S.image (fun x => Finset.univ.filter
        (fun a : Fin d × Fin n => θ a.1 a.2 ≤ x a.1)))
      = (S.image g).image intentOf := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact hfac x
  -- 档位元组像的大小不超过逐维像大小之积（函数由其各分量唯一确定）
  have hmem : ∀ (t : ↥(S.image g)) (j : Fin d),
      t.1 j ∈ S.image (fun x => level θ x j) := by
    intro t j
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp t.2
    have htj : t.1 j = level θ x j := by rw [← hxeq]
    rw [htj]
    exact Finset.mem_image_of_mem (fun y => level θ y j) hx
  have hprod : (S.image g).card
      ≤ ∏ j : Fin d, (S.image (fun x => level θ x j)).card := by
    have hinj : Function.Injective
        (fun (t : ↥(S.image g)) (j : Fin d) =>
          (⟨t.1 j, hmem t j⟩ : ↥(S.image (fun x => level θ x j)))) := by
      intro t₁ t₂ h
      apply Subtype.ext
      funext j
      have := congrFun h j
      simpa using congrArg Subtype.val this
    have h1 := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_pi] at h1
    simpa only [Fintype.card_coe] using h1
  calc (S.image (fun x => Finset.univ.filter
        (fun a : Fin d × Fin n => θ a.1 a.2 ≤ x a.1))).card
      = ((S.image g).image intentOf).card := by rw [himg]
    _ ≤ (S.image g).card := Finset.card_image_le
    _ ≤ ∏ j : Fin d, (S.image (fun x => level θ x j)).card := hprod
    _ ≤ ∏ _ : Fin d, (n + 1) :=
        Finset.prod_le_prod (fun j _ => Nat.zero_le _) (fun j _ => card_level_image_le θ S j)
    _ = (n + 1) ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ===========================================================================
  §4  与样本数合并
  =========================================================================== -/

/-- 胞腔数不超过样本数（像的大小不超过定义域大小）。 -/
theorem num_cells_le_card (d n : ℕ)
    (θ : Fin d → Fin n → ℝ) (S : Finset (Fin d → ℝ)) :
    (S.image (fun x => Finset.univ.filter
        (fun a : Fin d × Fin n => θ a.1 a.2 ≤ x a.1))).card ≤ S.card :=
  Finset.card_image_le

/-- **合并界**：胞腔数 ≤ min((n+1)^d, |S|)。

    两项各有独立来源：`(n+1)^d` 来自阈值的每维档位数，`|S|` 来自样本数。
    实测中后者常常先封顶（400 个样本最多占 400 个胞腔）。 -/
theorem num_cells_le_min (d n : ℕ)
    (θ : Fin d → Fin n → ℝ) (S : Finset (Fin d → ℝ)) :
    (S.image (fun x => Finset.univ.filter
        (fun a : Fin d × Fin n => θ a.1 a.2 ≤ x a.1))).card
      ≤ min ((n + 1) ^ d) S.card :=
  le_min (num_cells_le_succ_pow d n θ S) (num_cells_le_card d n θ S)

/-- **与旧界的一致性**：`(n+1)^d ≤ 2^(d·n)`，故新界处处不弱于旧界。 -/
theorem succ_pow_le_two_pow (d n : ℕ) : (n + 1) ^ d ≤ 2 ^ (d * n) := by
  have h : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => simp
    | succ k ih =>
        have : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
        rw [this]
        nlinarith [Nat.succ_le_succ ih, Nat.zero_le (2 ^ k)]
  calc (n + 1) ^ d ≤ (2 ^ n) ^ d := Nat.pow_le_pow_left h d
    _ = 2 ^ (n * d) := by rw [← Nat.pow_mul]
    _ = 2 ^ (d * n) := by rw [Nat.mul_comm]

/-! ===========================================================================
  §5  紧性：界 `(n+1)^d` 可被达到
  =========================================================================== -/

section Sharp

/-- **规范阈值**：第 `j` 维取 `0, 1, …, n-1`。 -/
def θcanon (n : ℕ) : Fin n → ℝ := fun i => (i : ℝ)

/-- **规范点**：由各维的区间编号 `t` 给出，落在第 `j` 维的第 `t j` 个区间。

    由于阈值是 `0,…,n-1`，区间为 `(-∞,0), [0,1), …, [n-1,∞)`，共 `n+1` 个。
    取 `x j = t j - 1/2` 即落在第 `t j` 个区间内。 -/
def xcanon {d n : ℕ} (t : Fin d → Fin (n + 1)) : Fin d → ℝ :=
  fun j => ((t j : ℕ) : ℝ) - 1 / 2

/-- 计数引理：`{i : Fin n | i.val < k}` 的基数为 `k`（当 `k ≤ n`）。 -/
theorem card_filter_val_lt_le {n k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun i : Fin n => i.val < k)).card = k := by
  have himg : (univ.filter (fun i : Fin n => i.val < k))
      = (univ : Finset (Fin k)).image (Fin.castLE hk) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · rintro ⟨a, -, rfl⟩
      exact a.isLt
  rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective hk)]
  simp

/-- 规范点的档位基数恰为其区间编号。 -/
theorem card_level_xcanon {d n : ℕ} (t : Fin d → Fin (n + 1)) (j : Fin d) :
    (level (fun (_ : Fin d) (i : Fin n) => (i : ℝ)) (xcanon t) j).card = (t j).val := by
  have hk : (t j).val ≤ n := Nat.lt_succ_iff.mp (t j).isLt
  have hset : (level (fun (_ : Fin d) (i : Fin n) => (i : ℝ)) (xcanon t) j)
      = univ.filter (fun i : Fin n => i.val < (t j).val) := by
    unfold level xcanon
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h
      have h1 : (i.val : ℝ) ≤ ((t j).val : ℝ) - 1 / 2 := by
        simpa using h
      have h2 : (i.val : ℝ) < ((t j).val : ℝ) := by linarith
      exact_mod_cast h2
    · intro h
      have h2 : (i.val : ℝ) < ((t j).val : ℝ) := by exact_mod_cast h
      have h3 : (i.val : ℝ) + 1 ≤ ((t j).val : ℝ) := by
        have h4 : i.val + 1 ≤ (t j).val := h
        exact_mod_cast h4
      have h5 : (i.val : ℝ) ≤ ((t j : ℕ) : ℝ) - 1 / 2 := by linarith
      simpa using h5
  rw [hset, card_filter_val_lt_le hk]

/-- 规范点族是单射。 -/
theorem xcanon_injective {d n : ℕ} :
    Function.Injective (fun t : Fin d → Fin (n + 1) => xcanon t) := by
  intro t₁ t₂ h
  funext j
  have h' := congrFun h j
  simp only [xcanon] at h'
  have : ((t₁ j : ℕ) : ℝ) = ((t₂ j : ℕ) : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast this)

/-- 不同区间编号给出不同内涵。 -/
theorem intent_xcanon_injective {d n : ℕ} :
    Function.Injective
      (fun t : Fin d → Fin (n + 1) =>
        Finset.univ.filter (fun a : Fin d × Fin n =>
          (fun (_ : Fin d) (i : Fin n) => (i : ℝ)) a.1 a.2 ≤ (xcanon t) a.1)) := by
  intro t₁ t₂ h
  have hlev : ∀ j, level (fun (_ : Fin d) (i : Fin n) => (i : ℝ)) (xcanon t₁) j
      = level (fun (_ : Fin d) (i : Fin n) => (i : ℝ)) (xcanon t₂) j := by
    intro j
    ext i
    have := congrArg (fun (s : Finset (Fin d × Fin n)) => (j, i) ∈ s) h
    simpa [level] using this
  funext j
  have hc := congrArg Finset.card (hlev j)
  rw [card_level_xcanon, card_level_xcanon] at hc
  exact Fin.ext hc

/-- **【紧性】界 `(n+1)^d` 可被达到。**

    取规范阈值与规范点族：`(n+1)^d` 个点各占一个胞腔，故胞腔数恰为 `(n+1)^d`。
    结合 `num_cells_le_succ_pow`，得 `Θ((n+1)^d)`。 -/
theorem num_cells_succ_pow_attained (d n : ℕ) :
    ∃ (θ : Fin d → Fin n → ℝ) (S : Finset (Fin d → ℝ)),
      S.card = (n + 1) ^ d ∧
      (S.image (fun x => Finset.univ.filter
        (fun a : Fin d × Fin n => θ a.1 a.2 ≤ x a.1))).card = (n + 1) ^ d := by
  refine ⟨fun (_ : Fin d) (i : Fin n) => (i : ℝ),
          (univ : Finset (Fin d → Fin (n + 1))).image xcanon, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ xcanon_injective, Finset.card_univ,
      Fintype.card_pi]
    simp [Fintype.card_fin]
  · rw [Finset.image_image]
    have hcomp : Function.Injective
        ((fun x => Finset.univ.filter (fun a : Fin d × Fin n =>
            (fun (_ : Fin d) (i : Fin n) => (i : ℝ)) a.1 a.2 ≤ x a.1)) ∘ xcanon) :=
      intent_xcanon_injective
    rw [Finset.card_image_of_injective _ hcomp, Finset.card_univ, Fintype.card_pi]
    simp [Fintype.card_fin]

end Sharp

end

end FateV2.Error.TightCells
