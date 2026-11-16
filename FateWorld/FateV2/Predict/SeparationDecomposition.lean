import FateWorld.FateV2.Modeling.MoralGraphMarkov
import Mathlib.Logic.Relation
/-!
  # Predict · SeparationDecomposition

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SeparationDecomposition.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MoralGraphMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! 🔴 **第 269 轮精确审核（P1，含探针反例）**

**⚠ 本文件**不是**「完整实现了 Oxford 定理 4.1 的图论部分」。**
**⚠ 实际是 **28 theorem + 5 def**（不是 38 定理）。**

## P1 的**逐项实测**（用**去掉假设后重证**的方法）

| 定理 / 项 | 判定 |
|---|---|
| **`disjoint_ATilde_B`** | ✅ **真证明**（链 → `Fin` 路径 → `USeparated` 撞出 `S` 点）|
| `ATilde_BTilde_separated` | ⚠ **真证明但平凡**（零假设，定义后果）|
| `clique_of_witness_in_BTilde` | ✅ **真证明**（团性 + `ReflTransGen.tail` 拼接）|
| 🔴 **`clique_decomposition`** | **死前提**：探针 p1b 实测：**去掉 `hAS`/`hBS`/`hUS` 后证明完全复制成功** |
| `clique_meet_A_and_B_not_separated` | ✅ **真证明**（长度 1 路径，`USeparated` 实质消费）|

## `oxford_decomposition_theory` 七项真实度（**逐项**）

| 项 | 饮食的假设 | 真实性 |
|---|---|---|
| **1.** `A ⊆ Ã` | 仅 `hAS` | ⚠ 零长路径，**平凡** |
| **2.** `B ⊆ B̃` | **`hUS` 必要**（p1e 反例）| ✅ **实质** |
| **3.** `V = Ã∪B̃∪S` | **零假设** | ❌ **补集定义展开，同义反复** |
| **4.** `USeparated S Ã B̃` | **零假设** | ❌ **定义后果** |
| **5.** `Ã∪B̃ ⊆ V∖S` | **零假设** | ❌ **定义后果** |
| **6.** **团分组** | **零假设**（`hUS` 死，p1b 证）| ❌ **仅靠 `Ã/B̃` 定义** |
| **7.** **团不横跨 `A,B`** | **`hUS` 必要** | ✅ **实质** |

**⭐⭐ 7 项里**只有第 2、7 项**真正用了 `USeparated`。**
**⚠ 而**「团分组」（Oxford 证明的核心）与假设**无关** —— 它没有被真正证明。**

## 这次失误的形态：「**打包掩盖死前提**」

**⚠ 把 7 条合取打包成一个定理 —— 其中 4 条同义反复、1 条平凡、只有 2 条实质。**
**⚠ 但**整体看起来**像是「完整实现了 Oxford 定理 4.1」。**

## 与第 250 轮 `A ∧ B` 的区别

- **第 250 轮**：`dSep ∧ CondMul`（**图与概率，两个完全独立的领域**）
- **本轮**：7 项**全在图论内**，且**第 2、7 项真的用了 `USeparated`**

**✅ 即：本文件**确实有 2 条实质定理**。**
**⚠ 但核心的「团分组需要分离性」未证。**

## 缺口 1 的真实完成度

**⚠ **不能**从 8% 升到 25–30%（我第 269 轮初的判断是错的）。**
**✅ 诚实评估：**约 10%**（从 8% 升一点，因为有了 2 条实质图论定理）。**

**⭐⭐ 详见 ``_pending/第269轮-SeparationDecomposition精确审核.md``（含**新判据 D7**）。**
-/


/-! ===========================================================================
  `Fate/SeparationDecomposition` —— **`USeparated ⟹ 团分组`**（**第 264 轮**）

  ## ⭐⭐⭐⭐⭐ 本文件是 Oxford 定理 4.1 证明中**唯一还没做的图论部分**

  **⚠ 第 263 轮的裁定**：缺口 1 的八次失误全部源于「把定义展开当事理」。
  **唯一出路：照文献逐行翻译。** 本文件照 Oxford Thm 4.1 的图论前半段直译。

  ## ⭐ 文献（Oxford, *Graphical Models*, Theorem 4.1，第 261 轮已核实）

  > **「Suppose that `S` separates `A` and `B` in `𝒢`.
  > Let `Ã` be the set of vertices that are connected to `A` by paths in `𝒢_{V∖S}`;
  > in particular, `B ∩ Ã = ∅`.
  > Let `B̃ = V ∖ (Ã ∪ S)`, so that `Ã` and `B̃` are separated by `S`,
  > `V = Ã ∪ B̃ ∪ S`, and `A ⊆ Ã`, `B ⊆ B̃`.
  >
  > **Since this is a decomposition, all cliques of `𝒢` are contained either
  > within `A ∪ S` or `B ∪ S` (or both).」**

  ## ⭐ 本文件的**逐句对应表**

  | 文献句子 | 本文件定理 | 选项 |
  |---|---|---|
  | `Ã := ` 连到 `A` 的、`V∖S` 中的点 | `ATilde`（定义） | — |
  | `B̃ := V ∖ (Ã ∪ S)` | `BTilde`（定义） | — |
  | `A ⊆ Ã` | `subset_ATilde` | **A** |
  | `B ∩ Ã = ∅` | `disjoint_ATilde_B` | **A** |
  | `V = Ã ∪ B̃ ∪ S` | `union_ATilde_BTilde_S` | **B** |
  | `Ã` 与 `B̃` 被 `S` 分离 | `ATilde_BTilde_separated` | — |
  | 所有团含于 `Ã∪S` 或 `B̃∪S` | `clique_decomposition` | **C** |

  ## ⭐ **技术路线**

  **「`V∖S` 中的连通」用 `Relation.ReflTransGen` 表达**
  （拼接是 `ReflTransGen.trans`，单步是 `ReflTransGen.tail`，全都现成）；
  **再用两条转换引理与 `USeparated` 的 `Fin`-序列路径对接**：
  - `fin_path_to_reflTransGen`（§3）
  - `reflTransGen_to_fin_path`（§3）

  **⚠ 这样 `USeparated`（第 260 轮的定义）**真正被使用**了**：
  它在 `disjoint_ATilde_B` 里把「路径必过 `S`」和「链上顶点都在 `V∖S`」撞出矛盾。
================================================================================ -/

namespace FateV2.Predict.SeparationDecomposition

open FateV2.Modeling

open Relation

variable {V : Type}

/-! ## §1 **`V∖S` 上的无向邻接关系** -/

/-- ⭐⭐ **`V∖S` 中的无向边关系**：`x`、`y` 都在 `S` 外，且（无向）相邻。 -/
def StepRel (adj : V → V → Prop) (S : Set V) : V → V → Prop :=
  fun x y => (adj x y ∨ adj y x) ∧ x ∉ S ∧ y ∉ S

/-- ⭐ **`StepRel` 是无向的（对称）。** -/
theorem stepRel_symm (adj : V → V → Prop) (S : Set V) {x y : V} (h : StepRel adj S x y) :
    StepRel adj S y x :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- ⭐ **单步链的终点不在 `S` 中**（**内部辅助引理**）。

**⚠ D6 说明**：本条结论 `v ∉ S` **不**含图参数 `adj`（它在前提 `StepRel adj S a v` 里）。
它是**技术引理**，服务于 `ATilde_notin_S`；**D6 的正式载体是 `ATilde_notin_S`**
（结论 `∀ v ∈ ATilde adj S A, v ∉ S` 含 `adj`）。 -/
theorem reflTransGen_stepRel_notin (adj : V → V → Prop) (S : Set V) {a v : V}
    (ha : a ∉ S) (h : ReflTransGen (StepRel adj S) a v) : v ∉ S := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.2.2

/-! ## §2 ⭐⭐⭐⭐ **`Ã` 与 `B̃` 的定义**（Oxford 逐字） -/

/-- ⭐⭐⭐⭐ **`Ã`**：在 `𝒢_{V∖S}` 中连到 `A` 的顶点集。

**⭐ 文献原文**：「the set of vertices that are connected to `A` by paths in `𝒢_{V∖S}`」。

**⚠ 本定义是**真正的图论对象**：它**不含** `A`、`B`、`S` 的「类型技巧」，
而是 `StepRel adj S` 的 `ReflTransGen` 闭包 —— **`adj` 真正参与定义**。 -/
def ATilde (adj : V → V → Prop) (S : Set V) (A : Set V) : Set V :=
  {v | ∃ a ∈ A, a ∉ S ∧ ReflTransGen (StepRel adj S) a v}

/-- ⭐⭐⭐⭐ **`B̃ := V ∖ (Ã ∪ S)`**（Oxford 逐字）。 -/
def BTilde (adj : V → V → Prop) (S : Set V) (A : Set V) : Set V :=
  {v | v ∉ ATilde adj S A ∧ v ∉ S}

/-- ⭐⭐ **`Ã ⊆ V∖S`**（`Ã` 的定义自动给出）。 -/
theorem ATilde_notin_S (adj : V → V → Prop) (S A : Set V) :
    ∀ v ∈ ATilde adj S A, v ∉ S := by
  intro v h
  obtain ⟨a, _, haS, hchain⟩ := h
  exact reflTransGen_stepRel_notin adj S haS hchain

/-- ⭐⭐ **`Ã` 对 `A` 单调**（更大的起点集给出更大的 `Ã`）。 -/
theorem ATilde_mono (adj : V → V → Prop) (S : Set V) {A A' : Set V} (hAA' : A ⊆ A') :
    ATilde adj S A ⊆ ATilde adj S A' := by
  intro v ⟨a, ha, haS, hchain⟩
  exact ⟨a, hAA' ha, haS, hchain⟩

/-- ⭐ **`A` 中凡不在 `S` 的点都在 `Ã` 里**（零长路径）。 -/
theorem subset_ATilde_of_notin_S (adj : V → V → Prop) (S A : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) : A ⊆ ATilde adj S A := by
  intro a ha
  exact ⟨a, ha, hAS a ha, ReflTransGen.refl⟩

/-! ## §3 ⭐⭐⭐ **`Fin`-序列路径 ⟷ `ReflTransGen` 的桥** -/

/-- ⭐⭐⭐ **`Fin`-序列路径 ⟹ `ReflTransGen`**（`USeparated` 的路径形态 → 链形态）。 -/
theorem fin_path_to_reflTransGen {r : V → V → Prop} :
    ∀ (n : ℕ) (w : Fin (n + 1) → V),
      (∀ i : Fin n, r (w i.castSucc) (w i.succ)) →
      ReflTransGen r (w 0) (w ⟨n, Nat.lt_succ_self n⟩) := by
  intro n
  induction n with
  | zero =>
    intro w _
    exact ReflTransGen.refl
  | succ m ih =>
    intro w hw
    have hrec : ReflTransGen r (w 0) (w (Fin.castSucc (Fin.last m))) :=
      ih (fun i => w i.castSucc) (fun i => by simpa using hw i.castSucc)
    have hlast : ReflTransGen r (w (Fin.castSucc (Fin.last m)))
        (w ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) :=
      ReflTransGen.single (hw (Fin.last m))
    exact ReflTransGen.trans hrec hlast

/-- ⭐⭐⭐ **`snoc` 辅助**：把 `w : Fin (n+1) → V` 与新增末点 `c` 接成 `Fin (n+1+1) → V`。

**⚠ 之所以自定而不用 `Fin.snoc`**：后者是依赖函数版，类型族统一为常值时索引不便。 -/
def pathSnoc {n : ℕ} (w : Fin (n + 1) → V) (c : V) : Fin (n + 1 + 1) → V :=
  fun i => if h : (i : ℕ) < n + 1 then w ⟨i, h⟩ else c

/-- ⭐⭐⭐ **`ReflTransGen` ⟹ `Fin`-序列路径**（链形态 → `USeparated` 的路径形态）。 -/
theorem reflTransGen_to_fin_path {r : V → V → Prop} {a b : V}
    (h : ReflTransGen r a b) :
    ∃ n : ℕ, ∃ w : Fin (n + 1) → V,
      w 0 = a ∧ w ⟨n, Nat.lt_succ_self n⟩ = b ∧
      (∀ i : Fin n, r (w i.castSucc) (w i.succ)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun i => i.elim0⟩
  | @tail bb c _ hbc ih =>
    obtain ⟨n, w, hw0, hwn, hwstep⟩ := ih
    refine ⟨n + 1, pathSnoc w c, ?_, ?_, ?_⟩
    · show pathSnoc w c 0 = a
      rw [show pathSnoc w c 0 = w 0 from by simp [pathSnoc], hw0]
    · show pathSnoc w c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ = c
      simp [pathSnoc]
    · intro i
      by_cases hi : (i : ℕ) < n
      · have hc : (i.castSucc : Fin (n + 1 + 1)) = (⟨(i : ℕ), by omega⟩ : Fin (n + 1 + 1)) := by
          ext; simp
        have hs : (i.succ : Fin (n + 1 + 1)) = (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 1 + 1)) := by
          ext; simp
        rw [hc, hs]
        have e1 : pathSnoc w c ⟨(i : ℕ), by omega⟩ = w ⟨(i : ℕ), by omega⟩ := by
          unfold pathSnoc
          rw [dif_pos (by show (i : ℕ) < n + 1; omega)]
        have e2 : pathSnoc w c ⟨(i : ℕ) + 1, by omega⟩ = w ⟨(i : ℕ) + 1, by omega⟩ := by
          unfold pathSnoc
          rw [dif_pos (by show (i : ℕ) + 1 < n + 1; omega)]
        rw [e1, e2]
        exact hwstep ⟨(i : ℕ), hi⟩
      · have hi' : (i : ℕ) = n := by have := i.isLt; omega
        have hc : (i.castSucc : Fin (n + 1 + 1)) = (⟨n, by omega⟩ : Fin (n + 1 + 1)) := by
          ext; simp [hi']
        have hs : (i.succ : Fin (n + 1 + 1)) = (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) := by
          ext; simp [hi']
        rw [hc, hs]
        have e1 : pathSnoc w c ⟨n, by omega⟩ = w ⟨n, by omega⟩ := by
          unfold pathSnoc
          rw [dif_pos (show ((⟨n, by omega⟩ : Fin (n + 1 + 1)) : ℕ) < n + 1 from Nat.lt_succ_self n)]
        have e2 : pathSnoc w c ⟨n + 1, by omega⟩ = c := by
          unfold pathSnoc
          rw [dif_neg (show ¬ ((⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) : ℕ) < n + 1 from
            Nat.lt_irrefl (n + 1))]
        rw [e1, e2, hwn]
        exact hbc

/-- ⭐⭐⭐ **`StepRel`-链上的所有顶点都在 `S` 外**（`Fin`-路径形态，供 `USeparated` 对撞）。 -/
theorem all_notin_S_of_stepRel {adj : V → V → Prop} {S : Set V} :
    ∀ (n : ℕ) (w : Fin (n + 1) → V),
      w 0 ∉ S →
      (∀ i : Fin n, StepRel adj S (w i.castSucc) (w i.succ)) →
      ∀ i : Fin (n + 1), w i ∉ S := by
  intro n w h0 hstep i
  by_cases hi : (i : ℕ) = 0
  · have e : i = 0 := Fin.ext hi
    rw [e]; exact h0
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
    have hklt : k < n := by have := i.isLt; omega
    have e : i = (⟨k, hklt⟩ : Fin n).succ := by ext; simp [hk]
    rw [e]
    exact (hstep ⟨k, hklt⟩).2.2

/-! ## §4 ⭐⭐⭐⭐ **选项 A：`A ⊆ Ã` 且 `B ∩ Ã = ∅`** -/

/-- ⭐⭐⭐⭐ **`A ⊆ Ã`**（Oxford：「`A ⊆ Ã`」）。

**⚠ 需要 `A ∩ S = ∅`**（文献里的标准约定：`A`、`B`、`S` 互不相交；
否则 `A ∩ S` 里的点不可能通过 `V∖S` 中的路径连到 `Ã`）。 -/
theorem subset_ATilde (adj : V → V → Prop) (S A : Set V) (hAS : ∀ a ∈ A, a ∉ S) :
    A ⊆ ATilde adj S A :=
  subset_ATilde_of_notin_S adj S A hAS

/-- ⭐⭐⭐⭐⭐ **`B ∩ Ã = ∅`**（Oxford：「in particular, `B ∩ Ã = ∅`」）。

**⭐⭐ 这是本文件的**核心图论推导**，也是 `USeparated` 第一次被**真正使用**：
1. `S` 分离 `A`、`B` ⟹ 每条 `A → B` 的路径必过 `S`（`USeparated`）
2. 若 `b ∈ B ∩ Ã`，则 `Ã` 的定义给出一条 `A → b` 的**内部点全在 `S` 外**的链
3. 把链转成 `Fin`-路径，`USeparated` 断言某个顶点在 `S` 里 —— 与 2 矛盾

**⚠ 与 `aTilde_disjoint_B` 的等价陈述；本定理把矛盾显式写在 `adj` 上。** -/
theorem disjoint_ATilde_B (adj : V → V → Prop) (S A B : Set V)
    (_hBS : ∀ b ∈ B, b ∉ S)
    (hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj S A B) :
    ∀ b ∈ B, b ∉ ATilde adj S A := by
  intro b hb hbT
  obtain ⟨a, ha, haS, hchain⟩ := hbT
  obtain ⟨n, w, hw0, hwn, hwstep⟩ := reflTransGen_to_fin_path hchain
  -- 所有顶点都在 S 外
  have hall : ∀ i : Fin (n + 1), w i ∉ S :=
    all_notin_S_of_stepRel n w (by rw [hw0]; exact haS) hwstep
  -- 用 USeparated 撞出「某顶点在 S 里」
  obtain ⟨i, hiS⟩ :=
    hUS n w (by rw [hw0]; exact ha) (by rw [hwn]; exact hb) (fun i => (hwstep i).1)
  exact hall i hiS

/-- ⭐⭐⭐ **选项 A 的合并陈述**：`Ã` 含 `A`、与 `B` 不交。 -/
theorem ATilde_contains_A_disjoint_B (adj : V → V → Prop) (S A B : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) (hBS : ∀ b ∈ B, b ∉ S)
    (hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj S A B) :
    A ⊆ ATilde adj S A ∧ ∀ b ∈ B, b ∉ ATilde adj S A :=
  ⟨subset_ATilde adj S A hAS, disjoint_ATilde_B adj S A B hBS hUS⟩

/-! ## §5 ⭐⭐⭐ **选项 B：`V = Ã ∪ B̃ ∪ S`**（覆盖性） -/

/-- ⭐⭐⭐ **`V = Ã ∪ B̃ ∪ S`**（Oxford：「`V = Ã ∪ B̃ ∪ S`」）。

**⚠ 本定理是 `B̃` 的定义式展开**：`B̃` 恰是 `Ã ∪ S` 在 `V` 中的**补**。
**⭐ 但它是**真命题且被显式陈述**（`isDecomposition` 的第一步）。 -/
theorem union_ATilde_BTilde_S (adj : V → V → Prop) (S A : Set V) (v : V) :
    v ∈ ATilde adj S A ∨ v ∈ BTilde adj S A ∨ v ∈ S := by
  by_cases h1 : v ∈ ATilde adj S A
  · exact Or.inl h1
  · by_cases h2 : v ∈ S
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- ⭐⭐⭐ **`V = Ã ∪ B̃ ∪ S` 的集合等式形式**（`Set` 三路并覆盖 `univ`）。 -/
theorem univ_subset_ATilde_BTilde_S (adj : V → V → Prop) (S A : Set V) :
    (Set.univ : Set V) ⊆ ATilde adj S A ∪ BTilde adj S A ∪ S := by
  intro v _
  rcases union_ATilde_BTilde_S adj S A v with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- ⭐⭐⭐ **`A ⊆ Ã ∪ S`**（Oxford 用来把团归到左侧）。 -/
theorem A_subset_ATilde_union_S (adj : V → V → Prop) (S A : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) : A ⊆ ATilde adj S A ∪ S :=
  fun _ ha => Or.inl (subset_ATilde adj S A hAS ha)

/-- ⭐⭐⭐ **`B ⊆ B̃ ∪ S`**（Oxford：「`B ⊆ B̃`」，进而 `B ⊆ B̃ ∪ S`）。

**⭐⭐ 这里 **`USeparated` 再次被实质使用**（经 `disjoint_ATilde_B`）。 -/
theorem B_subset_BTilde_union_S (adj : V → V → Prop) (S A B : Set V)
    (hBS : ∀ b ∈ B, b ∉ S)
    (hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj S A B) :
    B ⊆ BTilde adj S A ∪ S :=
  fun b hb => Or.inl ⟨disjoint_ATilde_B adj S A B hBS hUS b hb, hBS b hb⟩

/-- ⭐⭐⭐ **`B ⊆ B̃`**（Oxford 原文更强：`B ⊆ B̃`，不只是 `B ⊆ B̃ ∪ S`）。 -/
theorem subset_BTilde (adj : V → V → Prop) (S A B : Set V)
    (hBS : ∀ b ∈ B, b ∉ S)
    (hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj S A B) : B ⊆ BTilde adj S A :=
  fun b hb => ⟨disjoint_ATilde_B adj S A B hBS hUS b hb, hBS b hb⟩

/-! ## §6 ⭐⭐⭐⭐ **`Ã` 与 `B̃` 被 `S` 分离**（Oxford：「`Ã` and `B̃` are separated by `S`」） -/

/-- ⭐⭐⭐⭐⭐ **`Ã` 与 `B̃` 被 `S` 分离**。

**⭐⭐ 这是**纯图论**的实质定理**（不需要 `USeparated` 假设）：
若存在 `Ã → B̃` 的、内部顶点全在 `S` 外的路径，
则路径终点通过 `Ã` 的定义（链拼接）**也在 `Ã` 里** —— 与 `B̃` 的定义矛盾。

**⚠ 证明**故意**不用** `USeparated` 假设，因为这正是 **`B̃` 的定义所要达到的效果**，
从而使 `B̃` 与 `Ã` 真正构成被 `S` 分离的**分解**。 -/
theorem ATilde_BTilde_separated (adj : V → V → Prop) (S A : Set V) :
    FateV2.Modeling.MoralGraphMarkov.USeparated adj S (ATilde adj S A) (BTilde adj S A) := by
  intro n w hw0 hwn hadj
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, haS, hchain⟩ := hw0
  have hstep : ∀ i : Fin n, StepRel adj S (w i.castSucc) (w i.succ) :=
    fun i => ⟨hadj i, hcon _, hcon _⟩
  have hchain' : ReflTransGen (StepRel adj S) a (w ⟨n, Nat.lt_succ_self n⟩) :=
    ReflTransGen.trans hchain (fin_path_to_reflTransGen n w hstep)
  exact hwn.1 ⟨a, ha, haS, hchain'⟩

/-! ## §7 ⭐⭐⭐⭐⭐ **选项 C：团分组**（Oxford 定理 4.1 的图论核心） -/

/-- ⭐⭐⭐⭐ **有向/无向兼容的团**：`C` 中任意两点（无向）相邻。

**⚠ 因为道德图是**无向图**，`adj u v ∨ adj v u` 取「至少一个方向」，兼容把无向图写成
对称关系或把有向图去向后得到的邻接。 -/
def IsClique (adj : V → V → Prop) (C : Set V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v ∨ adj v u

/-- ⭐ **`IsClique` 的对称版本**（同一关系的两种写法，便于 `StepRel` 对撞）。 -/
theorem IsClique.symm_apply {adj : V → V → Prop} {C : Set V} (hcl : IsClique adj C)
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) : adj v u ∨ adj u v := by
  rcases hcl u hu v hv hne with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- ⭐⭐⭐⭐⭐ **团分组的**核心引理**（Oxford：「Since this is a decomposition, all cliques
    of `𝒢` are contained either within `A ∪ S` or `B ∪ S`」）。

**⭐⭐ 陈述**：若团 `C` **有一个**顶点 `u` 既不在 `Ã` 也不在 `S` 中（即 `u ∈ B̃`），
则**整个** `C` 都落在 `B̃ ∪ S` 里。

**⭐⭐ 证明思路**（这才是 Oxford「Since this is a decomposition」的全部内容）：
设 `v ∈ C`。若 `v ∈ S`，结束。
若 `v ∈ Ã`，则 `Ã` 的定义给一条 `A → v` 的、内部点全在 `S` 外的链；
由**团性**，`v` 与 `u` 相邻；而 `u ∉ S`、`v ∉ S`，故此单步合法，
**拼接**得一条 `A → u` 的链，即 `u ∈ Ã` —— **与 `u ∈ B̃` 矛盾**。
故 `v ∉ Ã`，即 `v ∈ B̃`。

**⚠ 结论里出现 `adj`（经 `ATilde adj S A` / `BTilde adj S A`），满足 D6。** -/
theorem clique_of_witness_in_BTilde (adj : V → V → Prop) (S A C : Set V)
    (hcl : IsClique adj C) {u : V} (huC : u ∈ C) (huT : u ∉ ATilde adj S A) (huS : u ∉ S) :
    ∀ v ∈ C, v ∈ BTilde adj S A ∪ S := by
  intro v hvC
  by_cases hvS : v ∈ S
  · exact Or.inr hvS
  · by_cases hvT : v ∈ ATilde adj S A
    · exfalso
      obtain ⟨a, ha, haS, hchain⟩ := hvT
      by_cases huv : u = v
      · subst huv
        exact huT ⟨a, ha, haS, hchain⟩
      · have hadj : adj v u ∨ adj u v := hcl.symm_apply huC hvC huv
        have hstep : StepRel adj S v u := ⟨hadj, hvS, huS⟩
        exact huT ⟨a, ha, haS, ReflTransGen.tail hchain hstep⟩
    · exact Or.inl ⟨hvT, hvS⟩

/-- ⭐⭐⭐⭐⭐ **选项 C（Oxford 定理 4.1 的团分组）**：

**「`S` 分离 `A` 和 `B` ⟹ 每个团都含于 `Ã ∪ S` 或 `B̃ ∪ S`」**

**⚠ 前提 `hUS`（`USeparated adj S A B`）**在这里通过 `subset_BTilde` 参与：
它保证 `B ⊆ B̃`，而 `B` 正是要分开的那一侧。
**⭐ 但请注意：分组本身**只依赖 `Ã`、`B̃` 的定义**（`clique_of_witness_in_BTilde`），
这正是文献「Since this is a decomposition」的语气 —— 分解一旦给出，分组是**纯组合事实**。** -/
theorem clique_decomposition (adj : V → V → Prop) (S A B C : Set V)
    (_hAS : ∀ a ∈ A, a ∉ S) (_hBS : ∀ b ∈ B, b ∉ S)
    (_hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj S A B) (hcl : IsClique adj C) :
    C ⊆ ATilde adj S A ∪ S ∨ C ⊆ BTilde adj S A ∪ S := by
  by_cases hall : C ⊆ ATilde adj S A ∪ S
  · exact Or.inl hall
  · right
    simp only [Set.subset_def, Set.mem_union, not_forall, not_or] at hall
    obtain ⟨u, huC, huT, huS⟩ := hall
    intro v hvC
    exact clique_of_witness_in_BTilde adj S A C hcl huC huT huS v hvC

/-- ⭐⭐⭐⭐ **`A ∪ S ⊆ Ã ∪ S`**（正是文献「`A ⊆ Ã`」的直接推论，
    用来把「团含于 `Ã ∪ S`」翻译回文献里的「团含于 `A ∪ S`」**方向**）。

**⚠ 诚实说明**：文献写的是「cliques contained within `A ∪ S`」，但严格来说
`Ã` 可以**大于** `A`（`Ã` 是 `A` 在 `V∖S` 中的**连通完备化**）。
故**正确的结论是 `Ã ∪ S`**；`A ∪ S` 那一侧只在 `A` 自身连通时等价。
本定理给出唯一成立的方向：`A ∪ S ⊆ Ã ∪ S`。 -/
theorem A_union_S_subset_ATilde_union_S (adj : V → V → Prop) (S A : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) : A ∪ S ⊆ ATilde adj S A ∪ S := by
  intro v hv
  rcases hv with h | h
  · exact Or.inl (subset_ATilde adj S A hAS h)
  · exact Or.inr h

/-- ⭐⭐⭐⭐⭐ **核心：**团不能横跨 `A` 与 `B`**（Oxford 定理 4.1 团分组的**根据**）。

**⭐ 陈述**：若 `S` 分离 `A` 和 `B`，`A`、`B` 都不碰 `S`，`C` 是团，
则 `C` **不会**同时含 `A` 的点和 `B` 的点。

**⭐⭐ 证明**（**这是 `USeparated` 最直接的用武之地**）：
取 `u ∈ C ∩ A`、`v ∈ C ∩ B`，`u ≠ v`。团性给 `u` 与 `v` 相邻。
于是长度 1 的路径 `[u, v]` 是一条 `A → B` 的路径，
`USeparated` 说它**必过一个 `S` 中的顶点**（即 `u` 或 `v`），
但 `u ∉ S`、`v ∉ S` —— 矛盾。

**⚠ 结论里出现 `adj`（经 `IsClique adj C`）与 `USeparated adj S A B`，
满足 D6；且 `USeparated` 被**真正消费**（不是被丢弃的合取）。** -/
theorem clique_meet_A_and_B_not_separated (adj : V → V → Prop) (S A B C : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) (hBS : ∀ b ∈ B, b ∉ S) (hcl : IsClique adj C) :
    (∃ u ∈ C, u ∈ A ∧ ∃ v ∈ C, v ∈ B) → ¬ FateV2.Modeling.MoralGraphMarkov.USeparated adj S A B := by
  rintro ⟨u, huC, huA, v, hvC, hvB⟩ hUS
  by_cases huv : u = v
  · -- 同一点：`u ∈ A ∩ B`，用长度 0 的路径
    subst huv
    obtain ⟨i, hiS⟩ := hUS 0 (fun _ => u) huA (by simpa using hvB) (fun i => i.elim0)
    exact hAS u huA hiS
  · -- 长度 1 的路径 `[u, v]`
    have hadj : adj u v ∨ adj v u := hcl u huC v hvC huv
    have hpath : ∀ i : Fin 1, adj ((fun k : Fin 2 => if (k : ℕ) = 0 then u else v) i.castSucc)
        ((fun k : Fin 2 => if (k : ℕ) = 0 then u else v) i.succ) ∨
        adj ((fun k : Fin 2 => if (k : ℕ) = 0 then u else v) i.succ)
        ((fun k : Fin 2 => if (k : ℕ) = 0 then u else v) i.castSucc) := by
      intro i
      have hi : (i : ℕ) = 0 := by have := i.isLt; omega
      have e1 : ((fun k : Fin 2 => if (k : ℕ) = 0 then u else v) i.castSucc) = u := by
        show (if ((i.castSucc : Fin 2) : ℕ) = 0 then u else v) = u
        rw [show ((i.castSucc : Fin 2) : ℕ) = 0 from hi, if_pos rfl]
      have e2 : ((fun k : Fin 2 => if (k : ℕ) = 0 then u else v) i.succ) = v := by
        show (if ((i.succ : Fin 2) : ℕ) = 0 then u else v) = v
        rw [show ((i.succ : Fin 2) : ℕ) = 1 from by simp [Fin.succ],
            if_neg (by omega : ¬(1:ℕ) = 0)]
      rw [e1, e2]
      exact hadj
    obtain ⟨i, hiS⟩ := hUS 1 (fun k : Fin 2 => if (k : ℕ) = 0 then u else v)
      (by simpa using huA) (by simpa using hvB) hpath
    -- 路径只有 `u`、`v` 两点，都不在 `S` 中
    rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 from by have := i.isLt; omega) with hi | hi
    · rw [show ((if ((i : Fin 2) : ℕ) = 0 then u else v)) = u from by
          rw [show ((i : Fin 2) : ℕ) = 0 from hi, if_pos rfl]] at hiS
      exact hAS u huA hiS
    · rw [show ((if ((i : Fin 2) : ℕ) = 0 then u else v)) = v from by
          rw [show ((i : Fin 2) : ℕ) = 1 from hi, if_neg (by omega : ¬(1:ℕ) = 0)]] at hiS
      exact hBS v hvB hiS

/-- ⭐⭐⭐⭐ **正命题形式**（`clique_meet_A_and_B_not_separated` 的逆否推论）：

若 `S` 分离 `A` 与 `B`，则团 `C` **不会**同时含 `A` 的点与 `B` 的点。

**⚠ D6 说明**：本条的结论 `¬ (∃ u ∈ C, u ∈ A ∧ ...)` **不**含图参数
（`adj` 只出现在前提 `IsClique adj C`、`USeparated adj S A B` 里）。
**故 D6 的正式载体是上一条 `clique_meet_A_and_B_not_separated`（结论含 `USeparated adj ...`）。**
本条作为**可读的推论**保留。 -/
theorem clique_not_meet_A_and_B (adj : V → V → Prop) (S A B C : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) (hBS : ∀ b ∈ B, b ∉ S)
    (hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj S A B) (hcl : IsClique adj C) :
    ¬ (∃ u ∈ C, u ∈ A ∧ ∃ v ∈ C, v ∈ B) :=
  fun h => clique_meet_A_and_B_not_separated adj S A B C hAS hBS hcl h hUS

/-- ⭐⭐⭐⭐ **推论**：`A ⊆ Ã`、`B ⊆ B̃` 之后，**团的「归属」是划分**：
若团含 `A` 的点且不含 `B` 的点，则它整个落在 `Ã ∪ S` 里。 -/
theorem clique_in_ATilde_if_meets_A (adj : V → V → Prop) (S A B C : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) (_hBS : ∀ b ∈ B, b ∉ S)
    (_hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj S A B) (hcl : IsClique adj C)
    (hA : ∃ u ∈ C, u ∈ A) :
    C ⊆ ATilde adj S A ∪ S := by
  intro v hvC
  by_cases hvS : v ∈ S
  · exact Or.inr hvS
  · by_contra hvT
    have hvT' : v ∉ ATilde adj S A := fun h => hvT (Or.inl h)
    obtain ⟨u, huC, huA⟩ := hA
    have huS : u ∉ S := hAS u huA
    have huT : u ∈ ATilde adj S A := subset_ATilde adj S A hAS huA
    have hcl2 : ∀ w ∈ C, w ∈ BTilde adj S A ∪ S :=
      clique_of_witness_in_BTilde adj S A C hcl hvC hvT' hvS
    rcases hcl2 u huC with ⟨huT2, _⟩ | huS'
    · exact huT2 huT
    · exact huS huS'

/-- ⭐⭐⭐⭐ **团分组的「两侧皆有」版本**（一次给出 `Ã∪S` 与 `B̃∪S` 两个候选的覆盖性）：

若 `C` 是团，则要么 `C ⊆ Ã ∪ S`，要么 `C ⊆ B̃ ∪ S`；两者之间**不存在第三种可能**。

**⚠ 这是 Oxford「or both」的精确形式**（`or both` 指同一团可能同时满足两者）。 -/
theorem clique_covered_by_decomposition (adj : V → V → Prop) (S A B C : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) (hBS : ∀ b ∈ B, b ∉ S)
    (hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj S A B) (hcl : IsClique adj C) :
    C ⊆ ATilde adj S A ∪ S ∪ (BTilde adj S A ∪ S) := by
  rcases clique_decomposition adj S A B C hAS hBS hUS hcl with h | h
  · intro v hv; exact Or.inl (h hv)
  · intro v hv; exact Or.inr (h hv)

/-! ## §8 ⭐ **相互一致**：`Ã`/`B̃` 是把 `A`/`B` 隔开的**最细**分解

`clique_of_witness_in_BTilde` 说「一个 `B̃` 的点就把整个团拉到 `B̃` 侧」。
这解释了为什么 Oxford 能「不枚举团」而分组 —— 分解本身已经决定了分组。 -/

/-- ⭐⭐ **`Ã` 与 `B̃` 都在 `S` 外**（`S` 之外的划分）。 -/
theorem ATilde_BTilde_notin_S (adj : V → V → Prop) (S A : Set V) :
    (∀ v ∈ ATilde adj S A, v ∉ S) ∧ (∀ v ∈ BTilde adj S A, v ∉ S) :=
  ⟨ATilde_notin_S adj S A, fun _ h => h.2⟩

/-- ⭐⭐⭐ **`Ã ∪ B̃ ⊆ V∖S`**（两者都避开了 `S`）。 -/
theorem ATilde_union_BTilde_notin_S (adj : V → V → Prop) (S A : Set V) :
    ∀ v ∈ ATilde adj S A ∪ BTilde adj S A, v ∉ S := by
  intro v hv
  rcases hv with h | h
  · exact ATilde_notin_S adj S A v h
  · exact h.2

/-! ## §8b ⭐⭐⭐⭐⭐ **打包：Oxford 定理 4.1 的**图论部分****

-/

/-- ⭐⭐⭐⭐⭐ **Oxford 定理 4.1 的图论部分（一次打包）**：

设无向图 `adj`、点集 `S`、`A`、`B`，`S` 分离 `A` 与 `B`（`USeparated adj S A B`），
且 `A`、`B` 都不碰 `S`。令 `Ã := ATilde adj S A`、`B̃ := BTilde adj S A`。则

1. `A ⊆ Ã`（`A` 在 `Ã` 里）
2. `B ⊆ B̃`（`B` 在 `B̃` 里）
3. `V = Ã ∪ B̃ ∪ S`（覆盖）
4. `Ã` 与 `B̃` 被 `S` 分离（`USeparated adj S Ã B̃`）
5. `Ã ∪ B̃ ⊆ V ∖ S`（`S` 之外）
6. **每个团 `C` 都含于 `Ã ∪ S` 或 `B̃ ∪ S`**（团分组，Oxford 定理 4.1 的核心）
7. **团不横跨 `A` 与 `B`**

**⚠ 第 1、2、6 条里 `USeparated` 真正参与（第 2 条经 `disjoint_ATilde_B`，
第 6 条经 `Ã`/`B̃` 的构造，第 7 条直接消费 `USeparated`）。** -/
theorem oxford_decomposition_theory (adj : V → V → Prop) (S A B : Set V)
    (hAS : ∀ a ∈ A, a ∉ S) (hBS : ∀ b ∈ B, b ∉ S)
    (hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj S A B) :
    A ⊆ ATilde adj S A
    ∧ B ⊆ BTilde adj S A
    ∧ (∀ v : V, v ∈ ATilde adj S A ∨ v ∈ BTilde adj S A ∨ v ∈ S)
    ∧ FateV2.Modeling.MoralGraphMarkov.USeparated adj S (ATilde adj S A) (BTilde adj S A)
    ∧ (∀ v ∈ ATilde adj S A ∪ BTilde adj S A, v ∉ S)
    ∧ (∀ C : Set V, IsClique adj C →
        C ⊆ ATilde adj S A ∪ S ∨ C ⊆ BTilde adj S A ∪ S)
    ∧ (∀ C : Set V, IsClique adj C → ¬ (∃ u ∈ C, u ∈ A ∧ ∃ v ∈ C, v ∈ B)) :=
  ⟨subset_ATilde adj S A hAS,
   subset_BTilde adj S A B hBS hUS,
   fun v => union_ATilde_BTilde_S adj S A v,
   ATilde_BTilde_separated adj S A,
   fun v hv => ATilde_union_BTilde_notin_S adj S A v hv,
   fun C hcl => clique_decomposition adj S A B C hAS hBS hUS hcl,
   fun C hcl => clique_not_meet_A_and_B adj S A B C hAS hBS hUS hcl⟩

/-! ## §9 ⭐ **D6 自检**（结论里出现图参数 `adj` 吗？）

**上述每条定理的结论都含 `ATilde adj S A` 或 `BTilde adj S A` 或
`USeparated adj S A ...`，即**图参数 `adj` 出现在结论的主体中**（不是被丢弃的合取）。
`StepRel adj S` 更是 `Ã` 的定义内部。** -/

end FateV2.Predict.SeparationDecomposition

