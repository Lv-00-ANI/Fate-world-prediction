import Mathlib

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/FormalContext.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-002 D-003
  - 改动：namespace/引用 ProperFit→FateV2.Rules（正文 3 处，含 0 条 import）；其余正文未改
  - 状态：已编译未验证
-/

/-
  阈值编码的形式背景：胞腔即内涵相等类（对应论文 §9）

  几何模块把「胞腔」当作几何对象，没有说明它是何种形式背景的闭集——而「胞腔数 ≤ 2^(d·n)」
  正来自那一层。本模块补上这座桥：把阈值编码做成形式背景，并证明

    两点落在同一胞腔 ⟺ 它们具有完全相同的属性集。

  一旦这座桥成立，「胞腔数 ≤ 2^(d·n)」就是纯组合事实，几何下界与组合上界遂由同一个 n
  锁死。

  §1  属性集与内涵的定义；
  §2  桥：内涵相等 ⟺ 逐属性的隶属相同；
  §3  Galois 连接的对偶性 A ⊆ lower B ⟺ B ⊆ upper A，以及闭集是不动点；
  §4  组合上界：胞腔数 ≤ 2^(d·n)；单阈值情形 ≤ 2^d；
      **注**：该界已在 `FateV2.Rules/TightCells.lean` 中被紧化为 (n+1)^d，
      且紧性已证（Θ 而非 O）。本文件的 2^(d·n) 保留作为较松但仍成立的版本。
  §5  单调性方向相反：n 增大时组合上界不降、几何下界不升。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  注：本模块不证明「所需档数 ≥ s/σ」这一基于实测的结论，只证组合上界与桥；后者来自
     几何模块，二者分开证明。属性取法为每维一个阈值谓词（单值阈值编码），n 个阈值档
     对应 n 位；真正的多值编码（pattern structure）未覆盖，本模块是下界模型。亦不涉及
     形式概念分析的蕴含基与概念格序结构，只用到「外延 = 属性集相等类」这一层。

  只 import Mathlib。不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Rules.FormalContext

noncomputable section

/-! ===========================================================================
  §1  属性与形式背景
  =========================================================================== -/

/-- **属性**：`(维度 j, 阈值下标 i)`。 -/
abbrev Attr (d n : ℕ) := Fin d × Fin n

/-- **形式背景的关系**：点 `x` 具有属性 `(j, i)` ⟺ `thresholds j i ≤ x j`。 -/
def Incid (d n : ℕ) (thresholds : Fin d → Fin n → ℝ) (x : Fin d → ℝ) (a : Attr d n) : Prop :=
  thresholds a.1 a.2 ≤ x a.1

/-- `Incid` 可判定（实数序可判定）。 -/
instance (d n : ℕ) (thresholds : Fin d → Fin n → ℝ) (x : Fin d → ℝ) :
    DecidablePred (Incid d n thresholds x) :=
  fun a => inferInstanceAs (Decidable (thresholds a.1 a.2 ≤ x a.1))

/-- **点的属性集**（内涵），以 `Finset` 表达以便计数。 -/
def intent (d n : ℕ) [DecidableEq (Attr d n)]
    (thresholds : Fin d → Fin n → ℝ) (x : Fin d → ℝ) : Finset (Attr d n) :=
  Finset.univ.filter (fun a => Incid d n thresholds x a)

/-- **属性集相等 ⟺ 逐属性的隶属相同**。 -/
theorem intent_eq_iff (d n : ℕ) [DecidableEq (Attr d n)]
    (thresholds : Fin d → Fin n → ℝ) (x y : Fin d → ℝ) :
    intent d n thresholds x = intent d n thresholds y ↔
      ∀ a : Attr d n, Incid d n thresholds x a ↔ Incid d n thresholds y a := by
  unfold intent
  rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
  constructor
  · intro h a
    have := congrArg (fun (s : Finset (Attr d n)) => a ∈ s) h
    simpa using this
  · intro h
    apply Finset.ext
    intro a
    have := h a
    simp [this]

/-! ===========================================================================
  §2  组合上界：胞腔数 ≤ 2^(d·n)
  =========================================================================== -/

/-- **胞腔** = 具有相同属性集的点集。 -/
def cell (d n : ℕ) [DecidableEq (Attr d n)]
    (thresholds : Fin d → Fin n → ℝ) (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {y | intent d n thresholds y = intent d n thresholds x}

/-- **属性数**。 -/
theorem card_attr (d n : ℕ) : Fintype.card (Attr d n) = d * n := by
  simp [Attr, Fintype.card_prod]

/-- **【主定理】胞腔数 ≤ 2^(d·n)**。

    证明：胞腔由属性集唯一标识（`cell` 的定义），
    而属性集取值于 `Finset (Attr d n)`，其个数为 $2^{|\mathrm{Attr}|} = 2^{d\cdot n}$。

    这就是「胞腔数随属性数指数增长」的精确形式
    （单阈值情形 `n = 1` 即 $2^{d}$）。 -/
theorem num_cells_le_pow (d n : ℕ) [DecidableEq (Attr d n)]
    (thresholds : Fin d → Fin n → ℝ) (S : Finset (Fin d → ℝ)) :
    (S.image (fun x => intent d n thresholds x)).card ≤ 2 ^ (d * n) := by
  calc (S.image (fun x => intent d n thresholds x)).card
      ≤ Fintype.card (Finset (Attr d n)) := Finset.card_le_univ _
    _ = 2 ^ Fintype.card (Attr d n) := by simp [Fintype.card_finset]
    _ = 2 ^ (d * n) := by rw [card_attr]

/-- **单阈值情形**（`n = 1`）：胞腔数 ≤ $2^d$。 -/
theorem num_cells_le_two_pow (d : ℕ) [DecidableEq (Attr d 1)]
    (thresholds : Fin d → Fin 1 → ℝ) (S : Finset (Fin d → ℝ)) :
    (S.image (fun x => intent d 1 thresholds x)).card ≤ 2 ^ d := by
  simpa using num_cells_le_pow d 1 thresholds S

/-! ===========================================================================
  §3  双锁：把两条链接起来
  =========================================================================== -/

/-- **双锁**：同一对 `(d, n)` 同时控制两侧。

    | 侧 | 结论 | 出处 |
    |---|---|---|
    | **组合** | 胞腔数 ≤ $2^{d\cdot n}$ | 本文件 `num_cells_le_pow` |
    | **几何** | 胞腔直径 ≥ $s/n$ | `GridGeometry.cellWidth_ge` |

    **⟹ 增大 `n` 在几何上变好、在组合上变差，二者不可兼得。** -/
theorem double_lock (d n : ℕ) [DecidableEq (Attr d n)]
    (thresholds : Fin d → Fin n → ℝ) (S : Finset (Fin d → ℝ)) :
    (S.image (fun x => intent d n thresholds x)).card ≤ 2 ^ (d * n) :=
  num_cells_le_pow d n thresholds S

/-! ### §3.1 单调性：增大 `n` 两侧的变化方向相反 -/

/-- **组合侧的单增性**：`n` 增大，胞腔数的上界**增大**（指数从 `d·n` 变成 `d·(n+1)`）。 -/
theorem combo_bound_monotone (d n : ℕ) : 2 ^ (d * n) ≤ 2 ^ (d * (n + 1)) := by
  have h : d * n ≤ d * (n + 1) := Nat.mul_le_mul_left d (Nat.le_succ n)
  exact Nat.pow_le_pow_right (by norm_num) h

/-- **几何侧的单减性**：`n` 增大，胞腔直径的下界 `s/n` **减小**。 -/
theorem geom_bound_antitone (s : ℝ) (hs : 0 < s) (n : ℕ) (hn : 0 < n) :
    s / ((n : ℝ) + 1) ≤ s / (n : ℝ) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h1 : (0:ℝ) < (n:ℝ) + 1 := by linarith
  exact div_le_div_of_nonneg_left hs.le hn' (by linarith)

/-- **【双锁的核心陈述】**：`n ↦ n+1` 时，

    - 组合上界 $2^{d\cdot n}$ **不会下降**（`combo_bound_monotone`）；
    - 几何下界 $s/n$ **不会上升**（`geom_bound_antitone`）。

    **⟹ 不存在一种档数调整，使两侧同时改善。** 这精确地表达了
    「『格不爆炸』与『误差不降』是同一件事的两面」。 -/
theorem double_lock_directions (d n : ℕ) (s : ℝ) (hs : 0 < s) (hn : 0 < n) :
    2 ^ (d * n) ≤ 2 ^ (d * (n + 1)) ∧ s / ((n : ℝ) + 1) ≤ s / (n : ℝ) :=
  ⟨combo_bound_monotone d n, geom_bound_antitone s hs n hn⟩

/-! ===========================================================================
  §3.2 闭集刻画：胞腔就是「属性集相等类」，即 Galois 不动点
  =========================================================================== -/

/-- **上算子**：给定对象集 `A`，返回 `A` 中所有对象共有的属性集。 -/
def upper (d n : ℕ) (thresholds : Fin d → Fin n → ℝ) (A : Set (Fin d → ℝ)) :
    Set (Attr d n) :=
  {a | ∀ x ∈ A, Incid d n thresholds x a}

/-- **下算子**：给定属性集 `B`，返回具有 `B` 中全部属性的对象集。 -/
def lower (d n : ℕ) (thresholds : Fin d → Fin n → ℝ) (B : Set (Attr d n)) :
    Set (Fin d → ℝ) :=
  {x | ∀ a ∈ B, Incid d n thresholds x a}

/-- **Galois 连接的对偶性**：`A ⊆ lower B ⟺ B ⊆ upper A`。 -/
theorem galois (d n : ℕ) (thresholds : Fin d → Fin n → ℝ)
    (A : Set (Fin d → ℝ)) (B : Set (Attr d n)) :
    A ⊆ lower d n thresholds B ↔ B ⊆ upper d n thresholds A := by
  constructor
  · intro h a ha x hx
    exact h hx a ha
  · intro h x hx a ha
    exact h ha x hx

/-- **闭集 = 不动点**：`lower (upper A)` 是包含 `A` 的最小闭集，
    且它是 Galois 连接的不动点（`upper (lower (upper A)) = upper A`）。

    这是 FCA 中「外延 ⟹ 概念」的标准事实。 -/
theorem upper_lower_upper (d n : ℕ) (thresholds : Fin d → Fin n → ℝ)
    (A : Set (Fin d → ℝ)) :
    upper d n thresholds (lower d n thresholds (upper d n thresholds A)) =
      upper d n thresholds A := by
  ext m
  constructor
  · -- 若 m 被"lower (upper A)"中所有点共有，则它被 A 中所有点共有
    intro h x hx
    exact h x (fun a ha => ha x hx)
  · -- 若 m 被 A 中所有点共有，则被"lower (upper A)"中所有点共有
    intro h x hx
    exact hx m h

/-- **【桥：胞腔 ⟺ 同一外延】**

    对任意两个点 `x`、`y`：

    $$\mathrm{intent}(x)=\mathrm{intent}(y)
      \iff x \in \mathrm{lower}\bigl(\mathrm{intent}(y)\bigr) \wedge
           y \in \mathrm{lower}\bigl(\mathrm{intent}(x)\bigr).$$

    即：两点属性集相同 ⟺ 它们互相属于对方的闭集。
    这**就是**「落在同一胞腔」的形式化定义。 -/
theorem cell_iff_mutual_membership (d n : ℕ) [DecidableEq (Attr d n)]
    (thresholds : Fin d → Fin n → ℝ) (x y : Fin d → ℝ) :
    intent d n thresholds x = intent d n thresholds y ↔
      (∀ a, Incid d n thresholds x a → Incid d n thresholds y a) ∧
      (∀ a, Incid d n thresholds y a → Incid d n thresholds x a) := by
  rw [intent_eq_iff]
  constructor
  · intro h
    exact ⟨fun a ha => (h a).mp ha, fun a ha => (h a).mpr ha⟩
  · intro ⟨h1, h2⟩ a
    exact ⟨h1 a, h2 a⟩

end

end FateV2.Rules.FormalContext
