import FateWorld.FateV2.Predict.TailBlockV4
/-!
  # Predict · TailBlockV4Consumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TailBlockV4Consumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TailBlockV4
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `FateV2.Predict.TailBlockV4Consumer` —— 接入 `TailBlockV4` 的消费层

  ## 0 目标

  `Fate/TailBlockV4.lean`（500 行，零 `sorry`）的核心结论是

  * `massA A S p`（`A` 内的受限求和，**不含**尾块因子 `|α|^(|V|-|A|)`）
  * `mass_tail_const`：`mass S p x = |α|^(|V|-|A|) · massA A S p x`（`S ⊆ A`）
  * `massA_sep_Z`：`massA A Z (F·G) = massA A (X∪Z) G · massA A (Y∪Z) F`
  * `condIndep_tail_block`：主定理 D（尾块版，**不需要** `X∪Y∪Z = univ`）
  * `condIndep_of_cover`：`X∪Y∪Z = univ` 时的退化推论

  本文件把这些结论**接到已入库的消费方**上。使用的已入库 API（实测存在）：

  | 消费方 | 位置 |
  |---|---|
  | `FateV2.Predict.View19.mass_const` | `Fate/View19FactorGraphSplit.lean:150` |
  | `FateV2.Predict.FactorMarkov.CondIndep` | `Fate/FactorMarkov.lean:194` |

  ## 1 本文件的消费定理（9 条，全部机检）

  1. §1 「量纲对照」：`massA_const_self` + `mass_const_eq_tail_mul_massA`
     —— 同一条 `mass A (fun _ => c) x` 被 `View19.mass_const`
     算成 `|α|^(|V|-|A|) · c`，而被 `TailBlockV4` 的 `massA` 算成 `c`；
     二者由 `card_tail` 机检地对上。**这就是「尾块因子」的确切位置。**
  2. §2 「尾块系数的可分离性与非零性」：`tail_factor_ne_zero`
     （`k := |α|^(|V|-|A|) ≠ 0`，**无附加前提**）、
     `mass_eq_tail_factor_mul_massA`（`mass_tail_const` 的分离常数形式）、
     `condIndep_factor_cancel`（`k ≠ 0` 时 `k²` 可约的纯代数骨架）。
  3. §3 「实例化消费」：`condIndep_of_cover_v4`、`condIndep_tail_block_v4`、
     `cover_agrees_with_tail_block` —— 把 `TailBlockV4` 的两条主入口
     在本文件的实例束下**直接消费**，结论是已入库的
     `FateV2.Predict.FactorMarkov.CondIndep p X Y Z`。

  ## 2 诚实声明

  * 零 `sorry` / `admit` / `axiom`。
  * **不**声称「主定理 D 本身是新结果」—— 它已在 `TailBlockV4` 中证明；
    本文件只做消费与量纲桥接。
  * `tail_factor_ne_zero` **无额外前提**：它只用到 `[Nonempty α]`，
    即 `Fintype.card α ≥ 1`，故尾块系数 `|α|^(|V|-|A|)` 恒非零。
    （`V` 与 `A` 的基数差在 `ℕ` 上截断为 `0` 也无妨：`0` 次幂为 `1`。）
  =========================================================================== -/

namespace FateV2.Predict.TailBlockV4Consumer

open FateV2.Modeling
open Finset
open TailBlockV4

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]
  [Nonempty α]

/-! ## §1 `massA` 的量纲（与 `View19.mass_const` 对照） -/

/-- ⭐ `massA A S` 对常值 `c` **精确**等于 `c`（无尾块因子）。

**⚠ 只对 `S = A` 陈述**：此时索引型 `{u // u ∈ A ∧ u ∉ A}` 必空，
求和退化为单点（`card_empty_idx`），故结果恰为 `c`。

对一般 `S` 该等式**不成立**（索引型非空时求和被重复计数 `|α|^|A\S|` 次），
所以本条**不**冒充「`massA` 与 `S` 无关」。这里给出的正是 `TailBlockV4`
里 `massA_self` 的常值实例。 -/
theorem massA_const_self (A : Finset V) (c : ℝ) (x : V → α) :
    massA A A (fun _ => c) x = c := by
  rw [massA_self]

/-- ⭐ 量纲对照：同一条 `mass`，`View19.mass_const` 给出 `|α|^(|V|-|S|) · c`，
而 `massA`（`A` 上的受限求和，`S = A`）给出 `c`。本条把两式**并列**陈述，
机检二者之差正是尾块因子。 -/
theorem mass_const_eq_tail_mul_massA (A : Finset V) (c : ℝ) (x : V → α) :
    FateV2.Predict.DAGFactorization.mass A (fun _ => c) x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) * massA A A (fun _ => c) x := by
  rw [massA_const_self, FateV2.Predict.View19.mass_const, card_tail]
  push_cast
  ring

/-! ## §2 尾块系数的可分离性与非零性 -/

/-- ⭐⭐ 尾块系数 `|α|^(|V|-|A|)` 非零（`Nonempty α` ⟹ `0 < card α`）。 -/
theorem tail_factor_ne_zero (A : Finset V) :
    ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) ≠ 0 := by
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    have h : 0 < Fintype.card α := Fintype.card_pos_iff.mpr (Nonempty.intro (Classical.choice ‹Nonempty α›))
    exact_mod_cast h
  exact pow_ne_zero _ (ne_of_gt hpos)

/-- ⭐⭐ 尾块系数的值：`mass S p x = k · massA A S p x`（`k` 与 `S`、`x` 无关）。

这是 `mass_tail_const` 的「分离出常数」形式，直接用于说明
`CondIndep` 两边的 `k²` 可约。 -/
theorem mass_eq_tail_factor_mul_massA {p : (V → α) → ℝ} {A S : Finset V}
    (hSA : S ⊆ A) (hp : ReadsOn p A) (x : V → α) :
    FateV2.Predict.DAGFactorization.mass S p x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card)) * massA A S p x :=
  mass_tail_const hSA hp x

/-- ⭐⭐ 推论：`CondIndep` 的四个 `mass` 换成 `massA` 后**尾块系数整体约掉**
（需该系数非零）。形式：若 `k ≠ 0` 且 `k*a*k*b = k*c*k*d`，则 `a*b = c*d`。

这就是 `condIndep_tail_block` 里「尾块因子直接约掉、问题退化为 `A` 上无尾情形」
那一步的纯代数骨架。 -/
theorem condIndep_factor_cancel {k a b c d : ℝ} (hk : k ≠ 0)
    (h : (k * a) * (k * b) = (k * c) * (k * d)) : a * b = c * d := by
  have hk2 : k * k ≠ 0 := mul_ne_zero hk hk
  have h' : (k * k) * (a * b) = (k * k) * (c * d) := by
    calc (k * k) * (a * b) = (k * a) * (k * b) := by ring
      _ = (k * c) * (k * d) := h
      _ = (k * k) * (c * d) := by ring
  exact mul_left_cancel₀ hk2 h'

/-! 注：`condIndep_factor_cancel` 的前提 `k*a*k*b = k*c*k*d` 与
`condIndep_tail_block` 的证明**内部**（`TailBlockV4.lean` §3 末的
`rw [...]; ring`）形状一致：四个 `mass` 各带一次 `k`。 -/

/-! ## §3 `condIndep_of_cover` 的实例化消费

⚠ `TailBlockV4` 的 `[Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]
[Nonempty α]` 是在 `namespace` 内的 `variable` 声明，**不导出**为
实例参数以外的任何东西 —— 所以下列 `..._v4` 定理把本文件的同名实例
**显式**传入。`condIndep_of_cover_v4` 能通过类型检查本身即机检证据：
两者签名的实例束**兼容**。 -/

/-- ⭐⭐⭐ `TailBlockV4.condIndep_of_cover` 的直接消费（本文件实例）。

`TailBlockV4` 内部的 `variable` 实例不被其他文件继承，故此处显式传递。
结论是 `FateV2.Predict.FactorMarkov.CondIndep p X Y Z`，与已入库主链同一口径。 -/
theorem condIndep_of_cover_v4 (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hsplit : FateV2.Predict.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  TailBlockV4.condIndep_of_cover ψ p hfac hread hsplit hXY hXZ hYZ hcover

/-- ⭐⭐⭐ 尾块版主定理 D 的直接消费（**不**要求 `X∪Y∪Z = univ`）。 -/
theorem condIndep_tail_block_v4 (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hTail : ∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ Z)
    (hsplit : FateV2.Predict.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  TailBlockV4.condIndep_tail_block ψ p hfac hread hTail hsplit hXY hXZ hYZ

/-- ⭐⭐ 一致性自检：`condIndep_of_cover_v4` 是 `condIndep_tail_block_v4` 的特例
（`hcover` ⟹ `hTail` 空真）。本条把两个入口**接在同一个结论**上，
证明消费层的两条路不冲突。 -/
theorem cover_agrees_with_tail_block (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hsplit : FateV2.Predict.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z ∧ FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  ⟨condIndep_of_cover_v4 ψ p hfac hread hsplit hXY hXZ hYZ hcover,
   condIndep_tail_block_v4 ψ p hfac hread
     (fun v hv => by rw [hcover] at hv; exact absurd (Finset.mem_univ v) hv)
     hsplit hXY hXZ hYZ⟩

end FateV2.Predict.TailBlockV4Consumer