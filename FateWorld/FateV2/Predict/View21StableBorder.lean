/-
# View21：稳定边界 / 暴露集（P-006 修复版）

## 0. 修复登记（P-006）

本文件由 `Fate/View21StableBorder.lean` 的旧版（11 error、1 `sorry`）修复而来。
按 `坏模块分诊.md` 第 22 条判定为 **FIX**，故修复而非归档。

### 0.1 已修复的 error（共 11 → 0）

| 原 error | 病因 | 修法 |
|---|---|---|
| `border_eq_empty_iff` ×3 | `Finset.not_mem_empty` / `Finset.eq_empty_iff_forall_not_mem` 在本 mathlib 版本不存在；`rw [h]` 的错误位置 | 全部改写成 `simp` 收尾；核心方向改用 `ancestorRank` 最小元论证（见下） |
| `prod_split_compl` ×2 | `Finset.prod_mul_prod_compl` 的参数名是 `(s) (f)`，且其补集是 `sᶜ` 不是 `univ \ s` | 先 `rw` `sᶜ = univ \ s` 再用引理 |
| `reads_compl` ×1 | `hpa hu ▸ huA ▸ hv` 非法 `▸` 链 | ——（该定理**陈述为假**，已删除，见 §0.2） |
| `pa_subset_exposed` ×2 | 结论里 `exposed` 的参数错位 | ——（该定理**陈述为假**，已删除，见 §0.2） |
| `stableFactorSplit` ×1 真 `sorry` + 其余 | 目标本身推不出 | ——（该定理**陈述为假**，已删除，见 §0.2） |

### 0.2 ⚠ 如实说明：删除的 3 条定理（陈述为假，不是"证不出"）

以下 3 条**陈述本身是假的**，留有反例，因此删除（既不 `sorry` 占位，也不弱化陈述冒充）：

1. **`pa_subset_exposed`**（原陈述）
   `v ∈ A → G.parents v ⊆ A ∪ exposed G A`。
   **反例**：`V = {a, b, c}`，边 `a → b`，`A = {a, c}`，`v = b`。
   则 `v ∉ A`（前提本来就没要求 `v ∈ A`），且 `exposed G A = ∅`
   （`parents a = parents c = ∅ ⊆ A`），于是 `a ∈ parents b` 但
   `a ∉ A ∪ exposed = A`，否证。
   更根本地：`exposed G A ⊆ A`（见 `exposed_subset`），所以任何
   "`A` 外的点落入 `A ∪ exposed`" 的断言都不可能是对的。
   **该直觉的正确陈述是** `AncestorStable G A → v ∉ A → G.parents v ⊆ A`
   （即 `AncestorStable` 的定义本身），以及 `pa_subset_of_mem_not_exposed`（已保留）。

2. **`reads_compl`**（原陈述）
   `AncestorStable G A → v ∉ A → insert v (G.parents v) ⊆ (univ \ A) ∪ exposed G A`。
   **反例**：`V = {a, b, c}`，边 `a → b`，`A = {a, c}`，`v = b`。
   `AncestorStable` 成立（`parents b = {a} ⊆ A`；`parents` 只检查 `A` 外的点，
   `c` 是孤点 `parents c = ∅ ⊆ A`）。
   但 `a ∈ insert b (parents b)`，而 `a ∉ univ \ A` 且 `a ∉ exposed = ∅`，否证。

3. **`stableFactorSplit`**（原陈述，含那 1 处真 `sorry`）
   `Factorizes p G → ∃ f g, (f 只读 A) ∧ (g 只读 exposed) ∧ p = f * g`。
   **反例**：`V = Bool`，边 `false → true`，`A = {true}`，
   `φ true x = if x false then 1 else 2`、`φ false ≡ 1`，`p x = ∏ v, φ v x`。
   则 `Factorizes p G`（`LocalTo` 对 `false` 平凡的、对 `true` 读 `{true, false}`）
   且 `AncestorStable G A` 成立（`parents true = {false} ⊆ A`），
   但任何满足 `p x = f x * g x` 的 `f` 都必须依赖 `x false ∉ A`，
   故"`f` 只读 `A`"不成立。
   根因：`AncestorStable` 只约束 **`A` 外**的点的父代，
   对 `A` **内**的点毫无约束，所以 `∏_{v∈A} φ v` 完全可以读 `pa(A) ⊄ A` 的坐标。
   另外原陈述的 `g` 部分（"`g` 只读 `exposed`"）同样错：`exposed ⊆ A`，
   而 `A` 外的因子恰好读 `A`（正是 `AncestorStable` 说的）。

   **该直觉的正确、可证的表述**已作为 3 条新定理保留/补上：
   - `pa_subset_of_mem_not_exposed`：`A` 内且非暴露的点，其父代全在 `A` 内；
   - `factorSplit_inner_local`：`p = f * g` 且 `f = ∏_{v∈A} φ v` 只读 `A ∪ pa(A)`。

   （另外我**没有**把 `AncestorStable G A → v ∉ A → parents v ⊆ A` 单独写成定理：
   那与 `AncestorStable` 的定义逐字同义，属同义反复，按纪律 7 不写。）

### 0.3 前件是否已把结论包进去（同义反复自查）

逐条检查见各定理 docstring 的 `【非循环】` 标注。总览：
- `stable_border_iff` 用在 `AncestorStable`（讲 `A` **外**的点）证
  `A = univ \ border G A`（讲 `A` 与 `border`，`border ⊆ Aᶜ`）——
  两者不是同一个命题，需要一步 `by_contra` 交换即可，非循环。
- `border_eq_empty_iff` 的前件**没有** `AncestorStable`，结论用的是
  `ancestorRank` 的最小元存在性（依赖 DAG 无环），**不是**把结论塞进前件。
- `exposed_disjoint_border` 不再用 `hS`（原版留着未使用的 `hS`，是冗余前件，
  已删除，避免假前提依赖）。

**零 `sorry` / `admit` / `axiom`。** 两遍 `lake env lean` 均 0 error。
-/

import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.MarkovEquivalence
import Mathlib.Tactic

namespace FateV2.Predict.View21

open FateV2.Modeling

open Finset
open FateV2.Modeling.Graph
open FateV2.Predict.FactorMarkov (Joint LocalTo Factorizes CondIndep)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- **祖先稳定性**：`A` 之外的点的父代全在 `A` 内。 -/
def AncestorStable (G : DAG V) (A : Finset V) : Prop :=
  ∀ c : V, c ∉ A → G.parents c ⊆ A

/-- **边界**：`A` 之外、但父代已全部落入 `A` 的点。 -/
def border (G : DAG V) (A : Finset V) : Finset V :=
  Finset.univ.filter (fun c => c ∉ A ∧ G.parents c ⊆ A)

/-- **暴露集**：`A` 之内、但父代越出 `A` 的点。 -/
def exposed (G : DAG V) (A : Finset V) : Finset V :=
  Finset.univ.filter (fun a => a ∈ A ∧ ¬ G.parents a ⊆ A)

section Basic
variable (G : DAG V) (A : Finset V)

/-- `border` 的成员刻画。 -/
theorem mem_border {c : V} : c ∈ border G A ↔ c ∉ A ∧ G.parents c ⊆ A := by
  simp [border]

/-- `exposed` 的成员刻画。 -/
theorem mem_exposed {a : V} : a ∈ exposed G A ↔ a ∈ A ∧ ¬ G.parents a ⊆ A := by
  simp [exposed]

/-- 【非循环】`border` 落在 `A` 的补集里。 -/
theorem border_subset_compl : border G A ⊆ ((univ : Finset V) \ A) := by
  intro c hc
  rw [mem_border] at hc
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, hc.1⟩

/-- 【非循环】`exposed` 落在 `A` 里。 -/
theorem exposed_subset : exposed G A ⊆ A := by
  intro a ha
  exact ((mem_exposed G A).mp ha).1

/-- 【非循环】`AncestorStable` 下，`A` 恰是 `border` 的补集。

前件 `AncestorStable` 讲的是 `A` **外**的点的父代；结论讲的是
`A` 与 `border ⊆ Aᶜ` 的互补关系，两者不同一，故非循环。 -/
theorem stable_border_iff (hS : AncestorStable G A) :
    A = (univ : Finset V) \ border G A := by
  ext c
  constructor
  · intro hc
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, ?_⟩
    rw [mem_border]
    rintro ⟨h, -⟩
    exact h hc
  · intro hc
    rw [Finset.mem_sdiff] at hc
    by_contra hA
    exact hc.2 ((mem_border G A).mpr ⟨hA, hS c hA⟩)

/-- 【非循环】`exposed` 与 `border` 不相交（一侧在 `A` 内，一侧在 `A` 外）。

原版把这定理挂在冗余前件 `AncestorStable` 上，已删除该前件：
命题不需要它，留着只会让前件虚增。 -/
theorem exposed_disjoint_border :
    Disjoint (exposed G A) (border G A) := by
  rw [Finset.disjoint_left]
  intro c hcE hcB
  exact ((mem_border G A).mp hcB).1 (exposed_subset G A hcE)

/-- 【非循环】`border` 为空 ⟺ `A` 是全集。

**从左到右**这一步是实质内容：它需要"`A` 的补非空 ⟹ 补中存在 `A`-源点"，
即需要在有限 DAG 上的 `ancestorRank` 最小元，`AncestorStable` **不**作为前件出现。 -/
theorem border_eq_empty_iff : border G A = ∅ ↔ A = (univ : Finset V) := by
  constructor
  · intro h
    by_contra hA
    have hne : ((univ : Finset V) \ A).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      apply hA
      ext c
      simp only [Finset.mem_univ, iff_true]
      by_contra hcA
      have : c ∈ (univ : Finset V) \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, hcA⟩
      rw [h0] at this
      exact absurd this (by simp)
    obtain ⟨c, hc, hmin⟩ :=
      Finset.exists_min_image ((univ : Finset V) \ A) (fun v => G.ancestorRank v) hne
    rw [Finset.mem_sdiff] at hc
    have hsub : G.parents c ⊆ A := by
      intro u hu
      by_contra huA
      have hrank : G.ancestorRank u < G.ancestorRank c :=
        DAG.ancestorRank_lt_of_edge G ((DAG.mem_parents G).mp hu)
      have hmem : u ∈ ((univ : Finset V) \ A) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huA⟩
      have := hmin u hmem
      omega
    have hbc : c ∈ border G A := (mem_border G A).mpr ⟨hc.2, hsub⟩
    rw [h] at hbc
    exact absurd hbc (by simp)
  · intro h
    subst h
    ext c
    simp [mem_border]

end Basic

/-!
  # Predict · View21StableBorder

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View21StableBorder.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, DAGFactorization, FactorMarkov, MarkovEquivalence
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## 概率侧（分解形态）

⚠ 本 section 与旧版的差别：`reads_compl` / `pa_subset_exposed` / `stableFactorSplit`
三条**陈述为假**，已删除（反例见文件头 §0.2）。此处只保留可证的真结论。 -/

section FactorSplit
variable (G : DAG V) (A : Finset V)

/-- 【非循环】把整乘积拆成 `A` 内、`A` 外两段。 -/
theorem prod_split_compl (φ : V → (V → α) → ℝ) (x : V → α) :
    (∏ v, φ v x)
      = (∏ v ∈ A, φ v x) * (∏ v ∈ ((univ : Finset V) \ A), φ v x) := by
  have h := (Finset.prod_mul_prod_compl A (fun v => φ v x)).symm
  rw [show (Aᶜ : Finset V) = (univ : Finset V) \ A from by ext v; simp] at h
  exact h

/-- 【非循环】`v ∈ A` 且 `v ∉ exposed` ⟹ `pa v ⊆ A`（`exposed` 定义的直接改写）。 -/
theorem pa_subset_of_mem_not_exposed (v : V) (hvA : v ∈ A) (hvE : v ∉ exposed G A) :
    G.parents v ⊆ A := by
  by_contra h
  exact hvE ((mem_exposed G A).mpr ⟨hvA, h⟩)

/-- 【非循环】乘积拆分 + 局部性：`f = ∏_{v∈A} φ v` 只读 `A ∪ pa(A)`。

旧版 `stableFactorSplit` 声称 `f` 只读 `A`，这是假的（`AncestorStable`
不约束 `A` 内的点）；此处的 `A ∪ pa(A)` 是可证的正确上界，
而 `p = f * g` 的分解本身仍是有内容的。 -/
theorem factorSplit_inner_local (p : Joint V α) (hfac : Factorizes p G) :
    ∃ f g : (V → α) → ℝ,
      (∀ x y : V → α,
        (∀ u, u ∈ A ∨ (∃ v ∈ A, u ∈ G.parents v) → x u = y u) → f x = f y) ∧
      (∀ x, p x = f x * g x) := by
  classical
  obtain ⟨φ, hloc, hprod⟩ := hfac
  refine ⟨fun x => ∏ v ∈ A, φ v x, fun x => ∏ v ∈ ((univ : Finset V) \ A), φ v x,
    ?_, ?_⟩
  · intro x y hxy
    refine Finset.prod_congr rfl fun v hv => hloc v x y ?_
    intro u hu
    rcases hu with rfl | hu
    · exact hxy u (Or.inl hv)
    · exact hxy u (Or.inr ⟨v, hv, hu⟩)
  · intro x
    rw [hprod x]
    have h := (Finset.prod_mul_prod_compl A (fun v => φ v x)).symm
    rw [show (Aᶜ : Finset V) = (univ : Finset V) \ A from by ext v; simp] at h
    exact h

end FactorSplit
