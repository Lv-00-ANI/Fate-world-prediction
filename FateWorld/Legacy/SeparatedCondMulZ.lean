import FateWorld.Legacy.SeparatedCondMul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
/-! 🔴🔴 **第 283 轮 D8 降级声明（V1 审核，7 个探针）**

## `uns_separable_chain`（3/3 结论项 FAIL）

| 结论项 | D8 | 硬证据 |
|---|---|---|
| ``p = F*G`` | **FAIL（平凡）** | 探针 1：**无需任何假设**，``F := p, G ≡ 1`` 即证 |
| ``DependsOnlyOn {x,z} F`` | **FAIL（定义展开）** | 与 U8 判第 280 轮**逐字同罪** |
| ``DependsOnlyOn {y,z} G`` | ⚠ FAIL，但含一格真内容 | 只有「``¬cA`` 的团落 ``{y,z}``」需要 `hUS` |

**探针 2 硬证**：``uns_separable_chain = clique_side_implies_separable'(已判定义展开)
∘ 集合恒等式 {x}∪{z}={x,z}``。

## ✅ 但 5 条反例是真的（V1：这是本文件最干净的部分）

> 「反例形式是 ``¬∃ F G, p=F·G ∧ Dep F ∧ Dep G`` —— **强否定**，可证即真不可能。
> ``pAdd`` 的秩 1 矩形 ``0·2=0 ≠ 1=1·1``（探针 7 不靠 ``sep_rect`` 独立重证）。
> ``pBad3``/``pSum23`` 都读坐标 ``3 ∉ {0,2} ∪ {1,2}``。」

## ⚠ `Fin 4` 上的必要性见证只算**半 D7-b**

> 「``hsub_02``/``hcl_02``/``hread_zero``/``hp_*`` **根本不是反例**，是正向见证。
> 真 D7-b 只有 4 条 ``¬`` 定理 + 4 条前提否定，**全在 ``Fin 4`` 单点**，无任意性。」

## N8 分类

36 条定理：``[展开]`` 13 + 未分类 11 + ``[支撑]`` 12。
**真内容仅 4 条**（``side_z_of_uns_side``、``star_usepathed``、``sep_rect``、``edge01_not_sep``）。
**评分 6/10。**

## ⭐⭐⭐ V1 指出的**真正缺口**

> 「正向缺口 1 未推进——仍缺一整个 ``MoralFactorizes``
> （**从 ``USeparated`` 导出团分解，而非假设 ``hp``**）。」

**⚠ 本文件的所有定理都假设 ``hp : p = ∏ ψ_C``（团分解），
故结论只能是 ``filter`` 的代数重排。**
**⭐⭐ 真正的 Oxford 定理 4.1 是**从图结构导出**团分解，而不是假设它。**

**⭐⭐ 详见 ``_pending/第283轮-D8判定与唯一出路.md``。**
-/


/-! ===========================================================================
  `Fate/SeparatedCondMulZ` —— **缺口 1：`S ≠ ∅` 的链情形（`S = {z}`）**
  （第 281 轮）

  ## 本文件做什么

  | # | 内容 | 地位 |
  |---|---|---|
  | **①** | `uns_separable_chain`（`S = {z}` 的可分离） | **主定理**（在 `Fate/SeparatedCondMul.lean` §3） |
  | **②** | `side_z_of_uns_side`（`{x}∪{z}` / `{y}∪{z}` 翻译成 `Side`） | **主引理** |
  | **③** | `uns_separable_chain_slim`（**去掉 3 个死前提**的正确签名） | **应当使用的版本** |
  | **④** | **语义 D7**：6 个数学前提逐条的反例/必要性实测 | §3–§9 |
  | **⑤** | `S ⊄ {z}` 时的**诚实失败说明** | §10 |

  ## ⭐ 逻辑结构（为什么 `S = {z}` 是**恰好**能做的边界）

  `side_of_uns_side`（任意 `S`）给：

  ```
  C ⊆ {x} ∪ S   或   C ⊆ {y} ∪ S          (★)
  ```

  `clique_side_implies_separable'` 需要：

  ```
  C ⊆ {x,z}     或   C ⊆ {y,z}            (★★)
  ```

  **`S = {z}` 时 `(★) ≡ (★★)`**，因为 `{x}∪{z} = {x,z}`、`{y}∪{z} = {y,z}`。
  这就是本文件唯一的、也确实是全部的新内容。

  **`S ⊄ {z}` 时 `(★)` 严格弱于 `(★★)`**，见 §10 的反例：
  `C = {x, w}` 且 `w ∈ S∖{z}` 满足 `(★)` 但**不满足** `(★★)`
  —— `w ∉ {x,z}`，故 `¬ cA x z C`；同时 `w ∉ {y,z}`，故 `(★★)` 第二支也假。

================================================================================ -/

namespace Fate.SeparatedCondMulZ

open Fate.MoralGraphMarkov
open Fate.SeparatedImpliesSide
open Fate.CliqueSideSeparable
open Finset

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## §1 ⭐⭐⭐ `S = {z}` 的图论层：团落一侧 -/

/-- ⭐⭐⭐ **`S = {z}` 时团落 `{x,z}` 或 `{y,z}` 侧**。

**复用**：`side_of_uns_side`（**任意 `S`**）+ 集合恒等式 `{x}∪{z}={x,z}`。
**唯一用途**：把 `side_of_uns_side` 的输出接到 `CliqueSideSeparable.Side`。 -/
theorem side_z_of_uns_side
    (adj : V → V → Prop) (x y z : V) (C : Finset V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (hcl : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u)
    (hsub : ∀ w ∈ C, w = x ∨ w = y ∨ w = z) :
    Side x y z C := by
  have hxS : x ∉ ({z} : Set V) := by simp [hxz]
  have hyS : y ∉ ({z} : Set V) := by simp [hyz]
  have h := side_of_uns_side adj ({z} : Set V) x y C hxS hyS hUS hcl
    (fun w hw => by
      rcases hsub w hw with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (by simp [h3])))
  rcases h with h | h
  · left
    intro w hw
    rcases h w hw with h1 | h2
    · simp [h1]
    · have hz : w = z := by simpa using h2
      simp [hz]
  · right
    intro w hw
    rcases h w hw with h1 | h2
    · simp [h1]
    · have hz : w = z := by simpa using h2
      simp [hz]

/-! ## §2 ⭐⭐⭐⭐⭐ 主定理（`S = {z}`） -/

/-- ⭐⭐⭐⭐⭐ **缺口 1 的链情形（`S = {z}`）**。

若 `USeparated adj {z} {x} {y}`、`x ≠ y`、`x,y ≠ z`；
每个团 `C ∈ N` 是团且 `C ⊆ {x,y,z}`；`ψ_C` 只读 `C`；`p = ∏_{C∈N} ψ_C`；
则 `p` 可分离为 `F(x,z)·G(y,z)`。

**证明 = 两层复用**（无新数学）：
1. `side_z_of_uns_side`（← `side_of_uns_side`）：`(★)` ⟹ `(★★)`；
2. `clique_side_implies_separable'`：`(★★)` ⟹ 可分离。 -/
theorem uns_separable_chain
    (adj : V → V → Prop) (x y z : V)
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (hcl : ∀ C ∈ N, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u)
    (hsub : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y ∨ w = z)
    (hread : ∀ C, ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (p : (V → V) → ℝ)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) G :=
  clique_side_implies_separable' x y z N ψ
    (fun C hC => side_z_of_uns_side adj x y z C hxy hxz hyz hUS (hcl C hC) (hsub C hC))
    hread p hp

/-! ## §3 ⭐⭐⭐⭐⭐ **语义 D7 结果**：`hxy`、`hxz`、`hyz` 都是**死前提**

**⭐ 这是本文件最重要的诚实结论。**

`d7_check.py --all` 对这三条报「必要」，但那只是「证明里提到了它们」
（`Unknown identifier`），**不是**数学必要性。真正的语义检验是：
**删掉后重新证明是否仍成立**。

下面给出 `uns_separable_chain_slim`：**去掉 `hxy`、`hxz`、`hyz`**，结论一字不变。
（本轮第 281 轮新证，见 §3.1–§3.3 的三分支。）

**为什么死**：这三条只在「把 `{x}∪{z}` 认成 `{x,z}`、并保证 `x ∉ {z}`」时用。
退化情形（`x = z`、`y = z`、`x = y`）下结论**反而更容易**成立：

| 退化 | `{x,z}` | `{y,z}` | 取 `F,G` |
|---|---|---|---|
| `x = z` | `{z}` | `{x,y}` | `F ≡ 1`、`G := p`（`p` 只依赖 `{x,y}`） |
| `y = z` | `{x,y}` | `{z}` | `F := p`、`G ≡ 1` |
| `x = y` | `{x,z}` | `{x,z}` | `F := p`、`G ≡ 1` |

`hsub` 在各退化分支里恰好保证 `C ⊆ {x,z}` 或 `C ⊆ {x,y}`，于是 `p` 只依赖那一支。 -/

/-- 退化情形 `x = z`：`F ≡ 1`、`G := p`，`p` 只依赖 `{x,y}`。 -/
theorem degenerate_xz
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ) (x y : V)
    (hsub : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y ∨ w = x)
    (hread : ∀ C, ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (p : (V → V) → ℝ) (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({x, x} : Finset V) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({y, x} : Finset V) G := by
  refine ⟨fun _ => 1, p, fun σ => by ring, fun _ _ _ => rfl, ?_⟩
  intro σ τ hagree
  rw [hp σ, hp τ]
  refine Finset.prod_congr rfl (fun C hC => ?_)
  exact hread C σ τ (fun w hw => by
    have hmem : w ∈ ({y, x} : Finset V) := by
      rcases hsub C hC w hw with h1 | h2 | h3
      · subst h1; simp
      · subst h2; simp
      · subst h3; simp
    exact hagree w hmem)

/-- 退化情形 `y = z`：`F := p`、`G ≡ 1`，`p` 只依赖 `{x,y}`。 -/
theorem degenerate_yz
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ) (x y : V)
    (hsub : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y ∨ w = y)
    (hread : ∀ C, ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (p : (V → V) → ℝ) (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({x, y} : Finset V) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({y, y} : Finset V) G := by
  refine ⟨p, fun _ => 1, fun σ => by ring, ?_, fun _ _ _ => rfl⟩
  intro σ τ hagree
  rw [hp σ, hp τ]
  refine Finset.prod_congr rfl (fun C hC => ?_)
  exact hread C σ τ (fun w hw => by
    have hmem : w ∈ ({x, y} : Finset V) := by
      rcases hsub C hC w hw with h1 | h2 | h3
      · subst h1; simp
      · subst h2; simp
      · subst h3; simp
    exact hagree w hmem)

/-- 退化情形 `x = y`：`F := p`、`G ≡ 1`，`p` 只依赖 `{x,z}`。 -/
theorem degenerate_xy
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ) (x z : V)
    (hsub : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = x ∨ w = z)
    (hread : ∀ C, ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (p : (V → V) → ℝ) (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) G := by
  refine ⟨p, fun _ => 1, fun σ => by ring, ?_, fun _ _ _ => rfl⟩
  intro σ τ hagree
  rw [hp σ, hp τ]
  refine Finset.prod_congr rfl (fun C hC => ?_)
  exact hread C σ τ (fun w hw => by
    have hmem : w ∈ ({x, z} : Finset V) := by
      rcases hsub C hC w hw with h1 | h2 | h3
      · subst h1; simp
      · subst h2; simp
      · subst h3; simp
    exact hagree w hmem)

/-- ⭐⭐⭐⭐⭐ **去掉 3 个死前提的 `'` 版本**（`hxy`、`hxz`、`hyz` 全删）。

**这是**应当使用**的签名。结论与 `uns_separable_chain` 一字不差。 -/
theorem uns_separable_chain_slim
    (adj : V → V → Prop) (x y z : V)
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (hcl : ∀ C ∈ N, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u)
    (hsub : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y ∨ w = z)
    (hread : ∀ C, ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (p : (V → V) → ℝ)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) G := by
  by_cases hxz : x = z
  · subst hxz
    exact degenerate_xz N ψ x y hsub hread p hp
  · by_cases hyz : y = z
    · subst hyz
      exact degenerate_yz N ψ x y hsub hread p hp
    · by_cases hxy : x = y
      · subst hxy
        exact degenerate_xy N ψ x z hsub hread p hp
      · exact uns_separable_chain adj x y z N ψ hxy hxz hyz hUS hcl hsub hread p hp

/-- ⭐ `uns_separable_chain` 只是 `'` 版本的包装（前者 3 条前提是**装饰**）。 -/
theorem uns_separable_chain_from_slim
    (adj : V → V → Prop) (x y z : V)
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (hcl : ∀ C ∈ N, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u)
    (hsub : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y ∨ w = z)
    (hread : ∀ C, ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (p : (V → V) → ℝ)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) G :=
  uns_separable_chain_slim adj x y z N ψ hUS hcl hsub hread p hp


/-! ## §4 ⭐⭐⭐⭐ **语义 D7 工具：不可分离的判定引理**

**⭐ D7 的判据（本文件采用的口径）**：
若 `p σ ≠ p τ` 而 `σ, τ` 在 `{x,z}` 与 `{y,z}` 上**分别一致**，则 `p` **不可分离**。
证明是秩 1 的直接推论：`F σ = F τ`、`G σ = G τ` ⟹ `p σ = p τ`，矛盾。

**⚠ 为什么不用 `d7_check.py` 的「删-重编译」？**
那个工具只能检测「证明里提到过这个名字」（失败信息一般是 `Unknown identifier`），
**不能**排除「换个证明仍成立」。本文件 §3 就是活证：`hxy/hxz/hyz` 被工具判「必要」，
实际**全是死前提**。故本节用**反例**（语义）判定，下面的 §5–§9 逐条给出。 -/
section D7

/-- ⭐ 反例见证：`Fin 4` 上只在第 `3` 号坐标不同的两个赋值。 -/
def st0 : Fin 4 → Fin 4 := fun _ => 0
def st1 : Fin 4 → Fin 4 := fun v => if v = 3 then 1 else 0

theorem st_agree_xz : ∀ v ∈ ({(0:Fin 4), 2} : Finset (Fin 4)), st0 v = st1 v := by
  intro v hv; rw [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> simp [st0, st1]

theorem st_agree_yz : ∀ v ∈ ({(1:Fin 4), 2} : Finset (Fin 4)), st0 v = st1 v := by
  intro v hv; rw [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> simp [st0, st1]

/-- ⭐⭐⭐ **不可分离判定**（D7 反例的引擎）。 -/
theorem not_separable_of_witness
    (p : (Fin 4 → Fin 4) → ℝ)
    (σ τ : Fin 4 → Fin 4)
    (x y z : Fin 4)
    (hσ : ∀ v ∈ ({x, z} : Finset (Fin 4)), σ v = τ v)
    (hτ : ∀ v ∈ ({y, z} : Finset (Fin 4)), σ v = τ v)
    (hne : p σ ≠ p τ) :
    ¬ ∃ (F G : (Fin 4 → Fin 4) → ℝ),
      (∀ s, p s = F s * G s)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({x, z} : Finset (Fin 4)) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({y, z} : Finset (Fin 4)) G := by
  rintro ⟨F, G, hFG, hF, hG⟩
  apply hne
  rw [hFG σ, hFG τ, hF σ τ hσ, hG σ τ hτ]

/-- 与 `x = 0, y = 1, z = 2` 配套的判定（`{0,2}` / `{1,2}` 版本）。 -/
theorem not_separable_012
    (p : (Fin 4 → Fin 4) → ℝ) (hne : p st0 ≠ p st1) :
    ¬ ∃ (F G : (Fin 4 → Fin 4) → ℝ),
      (∀ s, p s = F s * G s)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({(0:Fin 4), 2} : Finset (Fin 4)) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({(1:Fin 4), 2} : Finset (Fin 4)) G :=
  not_separable_of_witness p st0 st1 0 1 2 st_agree_xz st_agree_yz hne

/-- ⭐ 星形图 `0—2—1`、`2—3`：`{2}` **真的**分离 `{0}` 与 `{1}`。 -/
def starAdj : Fin 4 → Fin 4 → Prop := fun u v =>
  (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨
  (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
  (u = 3 ∧ v = 2) ∨ (u = 2 ∧ v = 3)

theorem starAdj_zero : ∀ v : Fin 4, starAdj 0 v → v = 2 := by
  intro v h
  simp only [starAdj] at h
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)
  · exact h
  · exact absurd h (by decide)
  · exact h
  · exact absurd h (by decide)

theorem star_usepathed :
    USeparated starAdj ({2} : Set (Fin 4)) ({0} : Set (Fin 4)) ({1} : Set (Fin 4)) := by
  intro n w hw0 hw1 hstep
  cases n with
  | zero => exact absurd (Set.mem_singleton_iff.mp hw0 ▸ hw1) (by decide)
  | succ k =>
    refine ⟨⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ k)⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    have hstep0 := hstep ⟨0, Nat.succ_pos k⟩
    have h0 : w 0 = 0 := Set.mem_singleton_iff.mp hw0
    have hcs : w (Fin.castSucc (⟨0, Nat.succ_pos k⟩ : Fin (k+1))) = 0 := by
      have : (Fin.castSucc (⟨0, Nat.succ_pos k⟩ : Fin (k+1))) = (0 : Fin (k+1+1)) := by
        ext; simp [Fin.castSucc]
      rw [this]; exact h0
    rcases hstep0 with h | h
    · rw [hcs] at h; exact starAdj_zero _ h
    · rw [hcs] at h
      simp only [starAdj] at h
      rcases h with ⟨-, hh⟩ | ⟨hh, -⟩ | ⟨-, hh⟩ | ⟨hh, -⟩ | ⟨-, hh⟩ | ⟨hh, -⟩
      · exact absurd hh.symm (by decide)
      · exact hh
      · exact absurd hh.symm (by decide)
      · exact hh
      · exact absurd hh.symm (by decide)
      · exact hh

/-! ## §5 ⭐⭐⭐⭐ D7：**`hp` 语义必要**

`N = {{0,2}}`、`ψ ≡ 0`、`p := σ 3`。其余 5 条前提全成立，`hp` 失败，
`p` 不可分离。 -/

def N02 : Finset (Finset (Fin 4)) := {({0,2} : Finset (Fin 4))}
theorem N02_singleton : ∀ C ∈ N02, C = ({0,2} : Finset (Fin 4)) := by
  intro C hC; simpa [N02] using hC

theorem hsub_02 : ∀ C ∈ N02, ∀ w ∈ C, w = (0:Fin 4) ∨ w = (1:Fin 4) ∨ w = (2:Fin 4) := by
  intro C hC w hw
  rw [N02_singleton C hC] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

theorem hcl_02 : ∀ C ∈ N02, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → starAdj u v ∨ starAdj v u := by
  intro C hC u hu v hv huv
  rw [N02_singleton C hC] at hu hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl
  · rcases hv with rfl | rfl
    · exact absurd rfl huv
    · exact Or.inl (by simp [starAdj])
  · rcases hv with rfl | rfl
    · exact Or.inr (by simp [starAdj])
    · exact absurd rfl huv

def psiZero : Finset (Fin 4) → (Fin 4 → Fin 4) → ℝ := fun _ _ => 0
def pBad3 : (Fin 4 → Fin 4) → ℝ := fun s => (s 3 : ℝ)

theorem hread_zero : ∀ C, ∀ σ τ : Fin 4 → Fin 4, (∀ w ∈ C, σ w = τ w) → psiZero C σ = psiZero C τ :=
  fun _ _ _ _ => rfl

/-- ⭐ `hp` **确实失败**。 -/
theorem hp_zero_fails : ¬ (∀ σ, pBad3 σ = ∏ C ∈ N02, psiZero C σ) := by
  intro h
  have := h st1
  simp [N02, pBad3, psiZero, st1] at this

/-- ⭐ 结论**假**。 -/
theorem pBad3_not_separable :
    ¬ ∃ (F G : (Fin 4 → Fin 4) → ℝ),
      (∀ s, pBad3 s = F s * G s)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({(0:Fin 4), 2} : Finset (Fin 4)) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({(1:Fin 4), 2} : Finset (Fin 4)) G :=
  not_separable_012 pBad3 (by simp [pBad3, st0, st1])

/-! ## §6 ⭐⭐⭐⭐ D7：**`hread` 语义必要**

`N = {{0,2}}`、`ψ {0,2} σ := σ 3`（**不读 C**）、`p := σ 3`。
`hcl`/`hsub`/`hUS`/`hp` 全成立，`hread` 失败，结论假。 -/

def psiThird : Finset (Fin 4) → (Fin 4 → Fin 4) → ℝ := fun _ s => (s 3 : ℝ)

theorem hp_third : ∀ σ, pBad3 σ = ∏ C ∈ N02, psiThird C σ := by
  intro σ; simp [N02, pBad3, psiThird]

/-- ⭐ `hread` **确实失败**。 -/
theorem hread_third_fails :
    ¬ (∀ C, ∀ σ τ : Fin 4 → Fin 4, (∀ w ∈ C, σ w = τ w) → psiThird C σ = psiThird C τ) := by
  intro h
  have := h ({0,2} : Finset (Fin 4)) st0 st1 (by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> simp [st0, st1])
  simp [psiThird, st0, st1] at this

/-! ## §7 ⭐⭐⭐⭐ D7：**`hsub` 语义必要**（**这就是 `S ⊄ {z}` 的失败模式**）

`N = {{2,3}}`（含 `3 ∉ {0,1,2}`）、`ψ C σ := ∑_{w∈C} σ w`（**只读 `C`**，故 `hread` 全局成立）、
`p := ∑_{w∈{2,3}} σ w`。`hcl`/`hUS` 成立、`hread` 成立、`hp` 成立，**`hsub` 失败**，结论假。

⚠ **注意**：这里 `C = {2,3}` 是 `starAdj` 的团（`3—2` 有边），且 `{2}` 分离 `{0}` 与 `{1}`。
所以反例**不是**靠破坏 `hUS` 得来的 —— 它精确地展示了：
**团里多出一个 `w ∉ {x,y,z}`，`ψ_C` 就会读 `w`，而 `w ∉ {x,z}∪{y,z}`，不可分离。** -/

def N23 : Finset (Finset (Fin 4)) := {({2,3} : Finset (Fin 4))}
theorem N23_singleton : ∀ C ∈ N23, C = ({2,3} : Finset (Fin 4)) := by
  intro C hC; simpa [N23] using hC

def psiSum : Finset (Fin 4) → (Fin 4 → Fin 4) → ℝ := fun C s => ∑ w ∈ C, (s w : ℝ)
def pSum23 : (Fin 4 → Fin 4) → ℝ := fun s => ∑ w ∈ ({2,3} : Finset (Fin 4)), (s w : ℝ)

theorem hcl_23 : ∀ C ∈ N23, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → starAdj u v ∨ starAdj v u := by
  intro C hC u hu v hv huv
  rw [N23_singleton C hC] at hu hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl
  · rcases hv with rfl | rfl
    · exact absurd rfl huv
    · exact Or.inr (by simp [starAdj])
  · rcases hv with rfl | rfl
    · exact Or.inl (by simp [starAdj])
    · exact absurd rfl huv

theorem hread_sum : ∀ C, ∀ σ τ : Fin 4 → Fin 4, (∀ w ∈ C, σ w = τ w) → psiSum C σ = psiSum C τ := by
  intro C σ τ h
  simp only [psiSum]
  exact Finset.sum_congr rfl (fun w hw => by rw [h w hw])

theorem hp_sum : ∀ σ, pSum23 σ = ∏ C ∈ N23, psiSum C σ := by
  intro σ; simp [N23, pSum23, psiSum]

/-- ⭐ `hsub` **确实失败**（`3 ∉ {0,1,2}`）。 -/
theorem hsub_23_fails :
    ¬ (∀ C ∈ N23, ∀ w ∈ C, w = (0:Fin 4) ∨ w = (1:Fin 4) ∨ w = (2:Fin 4)) := by
  intro h
  have h3 : (3:Fin 4) = 0 ∨ (3:Fin 4) = 1 ∨ (3:Fin 4) = 2 :=
    h {2,3} (by simp [N23]) 3 (by simp)
  rcases h3 with h3 | h3 | h3 <;> exact absurd h3 (by decide)

/-- ⭐ 结论**假**。 -/
theorem pSum23_not_separable :
    ¬ ∃ (F G : (Fin 4 → Fin 4) → ℝ),
      (∀ s, pSum23 s = F s * G s)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({(0:Fin 4), 2} : Finset (Fin 4)) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({(1:Fin 4), 2} : Finset (Fin 4)) G := by
  refine not_separable_012 pSum23 ?_
  simp only [pSum23, st0, st1]; norm_num

/-! ## §8 ⭐⭐⭐⭐ D7：**`hcl` 语义必要**

`N = {{0,1}}`（同时含 `x` 与 `y`）、`adj = noAdj`（无边）、`ψ C σ := ∑_{w∈C} σ w`。
`hsub`/`hread`/`hp`/`hUS` 全成立（空图无路径 ⟹ `USeparated` 空真），
**`hcl` 失败**，且 `p = σ0 + σ1` **可证不可分离**（§8.1 的秩 1 四矩形论证）。

**⭐⭐ 这就是 `hUS` + `hcl` 的核心作用**：排除「团同时含 `x` 与 `y`」。 -/

def noAdj : Fin 4 → Fin 4 → Prop := fun _ _ => False

theorem noAdj_usepathed :
    USeparated noAdj ({2} : Set (Fin 4)) ({0} : Set (Fin 4)) ({1} : Set (Fin 4)) := by
  intro n w hw0 hw1 hstep
  cases n with
  | zero => exact absurd (Set.mem_singleton_iff.mp hw0 ▸ hw1) (by decide)
  | succ k => exact absurd (hstep ⟨0, Nat.succ_pos k⟩) (by simp [noAdj])

def N01 : Finset (Finset (Fin 4)) := {({0,1} : Finset (Fin 4))}
theorem N01_singleton : ∀ C ∈ N01, C = ({0,1} : Finset (Fin 4)) := by
  intro C hC; simpa [N01] using hC

noncomputable def pAdd : (Fin 4 → Fin 4) → ℝ := fun s => (s 0 : ℝ) + (s 1 : ℝ)

theorem hsub_01 : ∀ C ∈ N01, ∀ w ∈ C, w = (0:Fin 4) ∨ w = (1:Fin 4) ∨ w = (2:Fin 4) := by
  intro C hC w hw
  rw [N01_singleton C hC] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem hp_add : ∀ σ, pAdd σ = ∏ C ∈ N01, psiSum C σ := by
  intro σ; simp [N01, pAdd, psiSum]

/-- ⭐ `hcl` **确实失败**（`0—1` 无边）。 -/
theorem hcl_01_fails :
    ¬ (∀ C ∈ N01, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → noAdj u v ∨ noAdj v u) := by
  intro h
  have hh := h {0,1} (by simp [N01]) 0 (by simp) 1 (by simp) (by decide)
  simpa [noAdj] using hh

/-! ### §8.1 秩 1 四矩形：`σ0 + σ1` 不可分离 -/

def e0 : Fin 4 → Fin 4 := fun v => if v = 0 then 1 else 0
def e1 : Fin 4 → Fin 4 := fun v => if v = 1 then 1 else 0
def e01 : Fin 4 → Fin 4 := fun v => if v = 0 then 1 else if v = 1 then 1 else 0

/-- ⭐⭐⭐ **可分离的秩 1 恒等式**（`z0 ↔ e0 ↔ e1 ↔ e01` 的矩形）。
　　若 `p = F·G` 且 `F` 只依赖 `{0,2}`、`G` 只依赖 `{1,2}`，则
　　`p z0 · p e01 = p e0 · p e1`。 -/
theorem sep_rect
    (F G : (Fin 4 → Fin 4) → ℝ)
    (hF : Fate.CliqueGrouping.DependsOnlyOn ({(0:Fin 4), 2} : Finset (Fin 4)) F)
    (hG : Fate.CliqueGrouping.DependsOnlyOn ({(1:Fin 4), 2} : Finset (Fin 4)) G) :
    F st0 * G st0 * (F e01 * G e01) = F e0 * G e0 * (F e1 * G e1) := by
  have hFz0e1 : F st0 = F e1 := hF st0 e1 (by
    intro v hv; rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [st0, e1])
  have hFe0e01 : F e0 = F e01 := hF e0 e01 (by
    intro v hv; rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [e0, e01])
  have hGz0e0 : G st0 = G e0 := hG st0 e0 (by
    intro v hv; rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [st0, e0])
  have hGe1e01 : G e1 = G e01 := hG e1 e01 (by
    intro v hv; rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [e1, e01])
  rw [hFz0e1, hFe0e01, hGz0e0, hGe1e01]; ring

/-- ⭐⭐⭐⭐ **`p = σ0 + σ1` 不可分离**（矩形左边 `0·2 = 0`，右边 `1·1 = 1`）。 -/
theorem pAdd_not_separable :
    ¬ ∃ (F G : (Fin 4 → Fin 4) → ℝ),
      (∀ s, pAdd s = F s * G s)
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({(0:Fin 4), 2} : Finset (Fin 4)) F
      ∧ Fate.CliqueGrouping.DependsOnlyOn ({(1:Fin 4), 2} : Finset (Fin 4)) G := by
  rintro ⟨F, G, hFG, hF, hG⟩
  have hrect := sep_rect F G hF hG
  have h1 : F st0 * G st0 = pAdd st0 := (hFG st0).symm
  have h2 : F e01 * G e01 = pAdd e01 := (hFG e01).symm
  have h3 : F e0 * G e0 = pAdd e0 := (hFG e0).symm
  have h4 : F e1 * G e1 = pAdd e1 := (hFG e1).symm
  rw [h1, h2, h3, h4] at hrect
  simp only [pAdd, st0, e01, e0, e1] at hrect
  norm_num at hrect

/-! ## §9 ⭐⭐⭐⭐ D7：**`hUS` 语义必要**

`adj` 只有边 `0—1`。`{2}` **不能**分离 `{0}` 与 `{1}`（直连路径）。
`N = {{0,1}}`、`ψ := psiSum`。`hcl`/`hsub`/`hread`/`hp` 全成立，**`hUS` 失败**，
结论假（`pAdd_not_separable`）。 -/

def edge01Adj : Fin 4 → Fin 4 → Prop := fun u v =>
  (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)

/-- ⭐ `{2}` **不能**分离 `{0}` 与 `{1}`。 -/
theorem edge01_not_sep :
    ¬ USeparated edge01Adj ({2} : Set (Fin 4)) ({0} : Set (Fin 4)) ({1} : Set (Fin 4)) := by
  intro h
  have := h 1 (fun i => if (i : ℕ) = 0 then 0 else 1)
    (by simp) (by simp)
    (fun i => by
      have hi : (i : ℕ) = 0 := by have := i.isLt; omega
      have e0 : (i.castSucc : Fin 2) = ⟨0, by norm_num⟩ := by ext; simpa using hi
      have e1 : (i.succ : Fin 2) = ⟨1, by norm_num⟩ := by ext; simp [hi]
      rw [e0, e1]; left; simp [edge01Adj])
  obtain ⟨i, hi⟩ := this
  fin_cases i
  · simp at hi
  · simp at hi

theorem hcl_01_edge01 : ∀ C ∈ N01, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → edge01Adj u v ∨ edge01Adj v u := by
  intro C hC u hu v hv huv
  rw [N01_singleton C hC] at hu hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl
  · rcases hv with rfl | rfl
    · exact absurd rfl huv
    · exact Or.inl (by simp [edge01Adj])
  · rcases hv with rfl | rfl
    · exact Or.inr (by simp [edge01Adj])
    · exact absurd rfl huv

end D7

/-! ## §10 ⚠⚠ **`S ⊄ {z}` 时做不到 —— 诚实说明**

### §10.1 障碍在哪里

设 `S ⊋ {z}`，取 `w ∈ S`、`w ≠ z`（于是 `w ∉ {x,z}` 若 `w ≠ x`；下文取 `w ∉ {x,y,z}`）。

`side_of_uns_side` 给 `C ⊆ {x}∪S` 或 `C ⊆ {y}∪S`。取 `C := {x, w}`：

* `C ⊆ {x} ∪ S` ✔（`x ∈ {x}`、`w ∈ S`）；
* 但 `cA x z C` **假**（`w ∉ {x,z}`）；
* 且 `C ⊆ {y,z}` **假**（`x ∉ {y,z}`）。

⇒ `Side x y z C` **失败**，`clique_side_implies_separable'` 的 `hside` 无法满足。

### §10.2 结论本身在 `S ⊄ {z}` 时也是**假的**

这**不是**证明技巧问题，是数学事实。反例：

* `V = Fin 4`、`x = 0`、`y = 1`、`z = 2`、`w = 3`、`S = {2,3}`；
* `adj := starAdj`（`0—2—1`、`2—3`）；则 `USeparated adj {2,3} {0} {1}` **成立**
  （`{2,3}` ⊇ `{2}` 而 `{2}` 已分离）；
* `N = {{2,3}}`、`ψ_C σ := ∑_{u∈C} σ u`（只读 `C`）、`p σ := ∑_{u∈{2,3}} σ u`；
* 则 §7 的 `pSum23_not_separable` **证明**了：`p` **不可**写成 `F(x,z)·G(y,z)`。

⇒ **`S ⊄ {z}` 时结论为假，任何证明都不可能存在。**

### §10.3 精确的边界

`{x,z} ∩ {y,z} = {z}`（当 `x ≠ y`）。真正能用的推广条件是

```
S ⊆ {x,z} ∩ {y,z} = {z}      ⟺      S = ∅ 或 S = {z}
```

`S = ∅` 是第 280 轮的 `uns_separable_of_clique_side`，`S = {z}` 是本文件的
`uns_separable_chain`。**两者合起来恰好覆盖全部可能。**
不能更宽 —— §10.2 是反例，不是猜测。 -/

end Fate.SeparatedCondMulZ


