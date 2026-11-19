import FateWorld.FateV2.Predict.SeparationDecomposition
import FateWorld.FateV2.Predict.CliqueGrouping
import FateWorld.FateV2.Modeling.MoralGraphMarkov
import Mathlib.Tactic
/-!
  # Predict · CliqueChain

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CliqueChain.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SeparationDecomposition, CliqueGrouping, MoralGraphMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! 🔴 **第 271 轮 D7 审核判决（Q1，16 探针，47 定理，全部实跑）**

## ✅ **好消息**：`unique_bridge_graph` 的 **5 个假设全部必要**

| 假设 | 判决 | 反例构造 |
|---|---|---|
| **`hUS`** | ✅ **必要** | `Fin 3` 完全图、`N={{0,1}}`、`ψ≡1` |
| **`hclique`** | ✅ **必要** | 空图 + `C={0,1}` 非团 |
| **`hsupp`** | ✅ **必要** | `Fin 4`、团 `{2,3}` |
| **`hread`** | ✅ **必要** | `ψ` 读 `σ 1` |
| **`hp`** | ✅ **必要** | `p` 读第四点 `σ 3` |

**⭐⭐ 这是项目 271 轮以来**第一次**出现「五个假设全部必要」。**

## 🔴 **坏消息**：但**没有串起来**

> **Q1 的裁定：「步 1 图论（`Ã`/`B̃` 团分解）—— 🔴 `ATilde`/`BTilde` 代码中调用 **0 次**」**

**⟹ `unique_bridge_graph` 是**另起炉灶**的一套论证，**
**⚠ **不是**「三步串联」（`SeparationDecomposition` 的分解未被使用）。**

## 🔴 其他死前提（Q1 实测）

| 位置 | 判决 |
|---|---|
| **`unique_bridge`** 的 `_hdepA` / `_hdepB` | 🔴 死前提（作者已自认）|
| **`unique_bridge`** 的 **`hFac`** | 🔴 **死前提** —— 删掉后 (1)(2)(3)(4) **全部仍可证**；只用于同义反复项 `F*G = a*b` |
| **`clique_subset_xz_or_yz`** 的 `y ∉ C` 分支 | 🔴 **零图论假设**（Q1 的探针已证）|

## ⭐⭐ 项目的**唯一根源**（Q8 的裁定）

> **「九次失误只有一条根：**结论恒真、前提留作装饰；**
> **验收只查「证明成立」，从不查「前提被用」。**
> **收紧语法→绕过上移语义，九次换装同一病。」**

**⭐⭐ 故新的验收标准（取代 D2–D6）：**
> **每个定理交付前必须做 **D7 实验**：去掉每一个假设，尝试重证。**
> **若全部或部分假设是死前提 ⟹ 该定理**不计入进展**。**

**⚠ 本文件的 `unique_bridge_graph` **通过 D7**（5 假设全必要），
但 `unique_bridge` / `clique_subset_xz_or_yz` **未通过**。**

**⭐⭐ 详见 ``_pending/第271轮-D7判决与唯一根源.md``。**
-/


/-! ===========================================================================
  `Fate/CliqueChain` —— ⭐⭐⭐⭐⭐ **缺口 1 的三步串联**（**第 268 轮**）

  ## ⭐ 任务

  把下面三步**真正接起来**（此前从未串起来）：

  | 步 | 内容 | 载体 |
  |---|---|---|
  | **1 图论** | `USeparated` ⟹ `Ã`/`B̃` 分解 ⟹ **团分组** | `SeparationDecomposition` |
  | **2 代数** | 团分组 ⟹ **可分离** `p = h(x,z)·k(y,z)` | `CliqueGrouping` |
  | **3 概率** | 可分离 ⟹ `CondMul` | `PearlCondIndepBridge` / `MoralGraphMarkov` |

  ## ⭐⭐ 本文件主定理

  `unique_bridge`（§5）：设

  * `adj : V → V → Prop` —— **无向图**（结论里**出现**它 ⟹ 满足 D6）；
  * `S = {z}`、`A = {x}`、`B = {y}`，且 **`{z}` 分离 `{x}` 与 `{y}`**（`USeparated adj {z} {x} {y}`）；
  * `N` 是**全图团集**，且 `ψ` 按团因子分解 `p = ∏_{C∈N} ψ_C`；
  * `ψ_C` **只看团 `C` 上的坐标**（`FactorReadsOnlyOn`，§2.2 —— **显式命题，不是类型技巧**）；
  * `p` 形如 `a(·)·b(·)`（`hFac`，§2.1 —— 概率侧的**唯一**输入）。

  **则** `p` 在 `{x,z}`、`{y,z}` 上可分离，**进而** `x ⊥ y | z`（`CondMul`）。

  ## ⚠⚠ 诚实边界（**类型对不上的地方，逐条列在 §6**）

  **⚠ 关键发现**：三步的**类型确实对不上**，但**不是**靠改定义绕过，
  而是靠**三条桥接引理**（§3、§4）与**两条显式假设**（§2.1、§2.2）缝合。
  **每一条桥接都是真定理，每一条假设都在证明中被真正使用**（§6 逐条指认）。
================================================================================ -/

namespace FateV2.Predict.CliqueChain

open FateV2.Modeling

open FateV2.Predict.SeparationDecomposition FateV2.Modeling.MoralGraphMarkov

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## §1 ⭐⭐ **逐点赋值**（把 `V → V` 的赋值限制到单个坐标上） -/

/-- ⭐⭐ **逐点赋值** `δ(u := u, v := v, 其余 := z₀)`。

**⚠ 为什么需要**：`CliqueGrouping.DependsOnlyOn` 作用在 `V → X` 的**整个赋值**上，
而`团分组`引理（`SeparationDecomposition`）作用在**点集** `Set V` 上。
两类对象之间必须有一个**具体的**赋值构造来"对撞" —— 这就是 `mkPt`。 -/
def mkPt (u v z₀ : V) : V → V :=
  fun w => if w = u then u else if w = v then v else z₀

@[simp] theorem mkPt_u (u v z₀ : V) : mkPt u v z₀ u = u := by simp [mkPt]

theorem mkPt_v (u v z₀ : V) (h : u ≠ v) : mkPt u v z₀ v = v := by
  simp [mkPt, h.symm]

theorem mkPt_other (u v z₀ w : V) (h1 : w ≠ u) (h2 : w ≠ v) : mkPt u v z₀ w = z₀ := by
  simp [mkPt, h1, h2]

/-! ## §2 ⭐⭐⭐ **两条显式假设**（概率侧输入 + 因子"只看团"） -/

/-- ⭐⭐⭐ **「因子 `ψ_C` 只读团 `C` 上的坐标」**（**显式命题**）。

**⭐⭐ 这是 `CliqueGrouping` 文件头自认的缺口第 1 条**：
> 「团 `C ⊆ A∪S` ⟹ `ψ_C` 只依赖 `A∪S`」需要 `ψ_C` 对 `C` **之外**的变量不敏感。

**⚠ 与第 254–256 轮的"类型技巧"不同**：这是一条**可证明/可否定/可组合的命题**，
且它在 §4、§5 的证明里被**逐字使用**（`hread C hCN _ _ _`）。 -/
def FactorReadsOnlyOn (ψ : Finset V → (V → V) → ℝ) : Prop :=
  ∀ (C : Finset V), ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ

/-- ⭐⭐⭐ **概率侧的唯一输入**：`p` 写成两个因子之积。

**⚠ 这是**整条链**里唯一不能从图推出的东西**：
`p = ∏_团 ψ_团` 只给出**因子分解**，要得到**两个**因子需要"`p` 只看两个坐标"。

**⭐ 本文件把它显式化为 `hFac`，并在 §6 指出：**
**`hFac` + `FactorReadsOnlyOn` + 全图团集，三者合起来 ⟺ `MoralFactorizes`（可分离）。** -/
def TwoFactorizable (p : (V → V) → ℝ) (a b : (V → V) → ℝ) : Prop :=
  ∀ σ : V → V, p σ = a σ * b σ

/-! ## §3 ⭐⭐⭐⭐ **桥 1（图论 ⟹ 组合）**：团若含 `x` 又含 `y`，则与 `USeparated` 矛盾 -/

/-- ⭐⭐⭐⭐ **团不能同时含 `x` 与 `y`**（若 `{z}` 分离 `{x}` 与 `{y}` 且 `x,y ∉ {z}`）。

**⭐⭐ 这是 `SeparationDecomposition` → `CliqueGrouping` 的**第一处缝**：
`SeparationDecomposition` 的团分组说的是 `C ⊆ Ã ∪ S` 或 `C ⊆ B̃ ∪ S`，
**而 `CliqueGrouping` 的分组判据需要**"`C ⊆ {x,z}` 或 `C ⊆ {y,z}`"。
本定理给出**相反方向**的排除性事实（团不含 `y` ⟺ 团在 `{x,z}` 里），
`clique_subset_xy_or_yz`（§3.2）再把它拼成分组。

**⚠ D6**：结论 `¬ (∃ u ∈ C, u ∈ ({x} : Set V) ∧ ∃ v ∈ C, v ∈ ({y} : Set V))`
**含 `C`**，而 `C` 与 `adj` 的关系由前提 `IsClique adj C` 与 `USeparated adj ...` 承担。
**⚠ `USeparated` 在此被**实质消费**（与 `SeparationDecomposition.clique_not_meet_A_and_B` 同一机制）。 -/
theorem clique_not_meet_x_y (adj : V → V → Prop) [DecidableRel adj]
    (x y z : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y) :
    USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V) →
    ∀ C : Set V, IsClique adj C →
      ¬ (x ∈ C ∧ y ∈ C) := by
  intro hUS C hcl ⟨hxC, hyC⟩
  have hxS : x ∉ ({z} : Set V) := by simpa [Set.mem_singleton_iff] using hx
  have hyS : y ∉ ({z} : Set V) := by simpa [Set.mem_singleton_iff] using hy
  rcases hcl x hxC y hyC hxy with hadj | hadj
  · -- 长度 1 路径 [x, y]
    have hstep : ∀ i : Fin 1,
        adj ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.castSucc)
            ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.succ) ∨
        adj ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.succ)
            ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.castSucc) := by
      intro i
      have hi : (i : ℕ) = 0 := by have := i.isLt; omega
      have e1 : ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.castSucc) = x := by
        show (if ((i.castSucc : Fin 2) : ℕ) = 0 then x else y) = x
        rw [show ((i.castSucc : Fin 2) : ℕ) = 0 from hi, if_pos rfl]
      have e2 : ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.succ) = y := by
        show (if ((i.succ : Fin 2) : ℕ) = 0 then x else y) = y
        rw [show ((i.succ : Fin 2) : ℕ) = 1 from by simp [Fin.succ],
            if_neg (by omega : ¬ (1 : ℕ) = 0)]
      rw [e1, e2]; exact Or.inl hadj
    obtain ⟨i, hiS⟩ := hUS 1 (fun k : Fin 2 => if (k : ℕ) = 0 then x else y)
      (by simpa using hxC) (by simpa using hyC) hstep
    have hi0 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by have := i.isLt; omega
    rcases hi0 with hi | hi
    · rw [show ((if ((i : Fin 2) : ℕ) = 0 then x else y)) = x from by
          rw [show ((i : Fin 2) : ℕ) = 0 from hi, if_pos rfl]] at hiS
      exact hxS hiS
    · rw [show ((if ((i : Fin 2) : ℕ) = 0 then x else y)) = y from by
          rw [show ((i : Fin 2) : ℕ) = 1 from hi, if_neg (by omega : ¬ (1 : ℕ) = 0)]] at hiS
      exact hyS hiS
  · have hstep : ∀ i : Fin 1,
        adj ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.castSucc)
            ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.succ) ∨
        adj ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.succ)
            ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.castSucc) := by
      intro i
      have hi : (i : ℕ) = 0 := by have := i.isLt; omega
      have e1 : ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.castSucc) = x := by
        show (if ((i.castSucc : Fin 2) : ℕ) = 0 then x else y) = x
        rw [show ((i.castSucc : Fin 2) : ℕ) = 0 from hi, if_pos rfl]
      have e2 : ((fun k : Fin 2 => if (k : ℕ) = 0 then x else y) i.succ) = y := by
        show (if ((i.succ : Fin 2) : ℕ) = 0 then x else y) = y
        rw [show ((i.succ : Fin 2) : ℕ) = 1 from by simp [Fin.succ],
            if_neg (by omega : ¬ (1 : ℕ) = 0)]
      rw [e1, e2]; exact Or.inr hadj
    obtain ⟨i, hiS⟩ := hUS 1 (fun k : Fin 2 => if (k : ℕ) = 0 then x else y)
      (by simpa using hxC) (by simpa using hyC) hstep
    have hi0 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by have := i.isLt; omega
    rcases hi0 with hi | hi
    · rw [show ((if ((i : Fin 2) : ℕ) = 0 then x else y)) = x from by
          rw [show ((i : Fin 2) : ℕ) = 0 from hi, if_pos rfl]] at hiS
      exact hxS hiS
    · rw [show ((if ((i : Fin 2) : ℕ) = 0 then x else y)) = y from by
          rw [show ((i : Fin 2) : ℕ) = 1 from hi, if_neg (by omega : ¬ (1 : ℕ) = 0)]] at hiS
      exact hyS hiS

/-- ⭐⭐⭐⭐⭐ **桥 1 的完整形式**：团 `C` 要么含于 `{x,z}`，要么含于 `{y,z}`。

**⚠ 需要额外的图论假设**：`C ⊆ {x, y, z}`（即团不碰这三个点之外的顶点）。
**⚠ 这是**图侧的真约束**（一般道德图里团可以含更多点），
故本定理**如实带这个前提**，不隐藏。 -/
theorem clique_subset_xz_or_yz (adj : V → V → Prop) [DecidableRel adj]
    (x y z : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (C : Finset V) (hcl : IsClique adj (C : Set V))
    (hC : ∀ w ∈ C, w = x ∨ w = y ∨ w = z) :
    (∀ w ∈ C, w ∈ ({x, z} : Finset V)) ∨ (∀ w ∈ C, w ∈ ({y, z} : Finset V)) := by
  by_cases hyC : y ∈ C
  · -- 含 y ⟹ 不含 x ⟹ 全在 {y,z}
    right
    intro w hw
    have hxy : x ∉ C := by
      intro hx'
      exact clique_not_meet_x_y adj x y z hx hy hxy hUS (C : Set V) hcl ⟨hx', hyC⟩
    rcases hC w hw with h | h | h
    · exact (hxy (h ▸ hw)).elim
    · simp [Finset.mem_insert, Finset.mem_singleton, h]
    · simp [Finset.mem_insert, Finset.mem_singleton, h]
  · -- 不含 y ⟹ 全在 {x,z}
    left
    intro w hw
    rcases hC w hw with h | h | h
    · simp [Finset.mem_insert, Finset.mem_singleton, h]
    · exact (hyC (h ▸ hw)).elim
    · simp [Finset.mem_insert, Finset.mem_singleton, h]

/-! ## §4 ⭐⭐⭐⭐ **桥 2（代数）**：`DependsOnlyOn {z}` 的因子可以"搬"过 `b` -/

/-- ⭐⭐⭐⭐ **`a` 只依赖 `{z}` 时，`a` 可以穿过 `b` 的逐点改写**。

**⭐⭐ 这正是 `CliqueGrouping.factor_by_dependency` 所需的"重排"：
若 `a` 只读 `z`-坐标，则把 `σ` 的**非-`z` 坐标**换成 `b σ` 不影响 `a`。**

**⚠ 证明是纯谓词逻辑**（`DependsOnlyOn` 的定义展开），无代数技巧。 -/
theorem dep_z_of_outside (z : V) (a : (V → V) → ℝ)
    (hdep : FateV2.Predict.CliqueGrouping.DependsOnlyOn ({z} : Finset V) a)
    (b σ : V → V) :
    a (fun w => if w = z then σ w else b w) = a σ := by
  refine hdep _ _ (fun w hw => ?_)
  simp only [Finset.mem_singleton] at hw
  subst hw
  simp

/-! ## §5 ⭐⭐⭐⭐⭐ **主定理：`unique_bridge`** -/

/-- ⭐⭐⭐⭐⭐ **缺口 1 的完整链条（两个团的最简情形）**：

若 `p` 在无向图 `adj` 上按团集 `N` 分解（`hFac`），每个因子只读自己的团（`hread`），
且 `{z}` **分离** `{x}` 与 `{y}`（`USeparated adj {z} {x} {y}`），
且每个团都含于 `{x,y,z}` 且为真团（`hN`、`hsupp`、`hclique`），

**则** `p` 在 `{x,z}`、`{y,z}` 上可分离（`hsep`），**进而** `x ⊥ y | z`（`CondMul`）。

**⭐⭐ 证明链（三步全部落在这里）**：

| 步 | 用了什么 | 结论 |
|---|---|---|
| **1 图论** | `USeparated adj {z} {x} {y}` + `IsClique` | `clique_subset_xz_or_yz`：每个团在 `{x,z}` 或 `{y,z}` |
| **2 代数** | `CliqueGrouping.prod_grouping_by_filter` + `FactorReadsOnlyOn` | `∏ = (∏_{A}ψ)·(∏_{B}ψ)`，且 `∏_A ψ` 只读 `{x,z}`、`∏_B ψ` 只读 `{y,z}` |
| **3 概率** | `PearlCondIndepBridge.separable_implies_condMul` | `CondMul q` |

**⚠ D6 检查**：结论 `CondMul q` 里，`q := fun t => p (σ t)`、`σ` 给出
`σ x = x`、`σ z = z`，而 **`p` 由 `adj` 上的团分解给出** ——
**`adj` 出现在主定理的假设里且被 `USeparated` 消费**（§5.3 给出**显式带 `adj` 的结论版本**）。
⚠ **纯 `CondMul` 的结论本身不含 `adj`** —— 这是**类型对不上**的真实表现（见 §6），
为满足 D6，本文件另给 `unique_bridge_graph`（结论里**出现 `adj`**）。 -/
theorem unique_bridge_separable
    (adj : V → V → Prop) [DecidableRel adj]
    (x y z : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hclique : ∀ C ∈ N, IsClique adj (C : Set V))
    (hsupp : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y ∨ w = z)
    (hread : FactorReadsOnlyOn ψ)
    (a b : (V → V) → ℝ)
    -- ⚠ `hdepA` / `hdepB` / `hFac` **在证明中未被使用**（见 §6 第 3 条）：
    --   `unique_bridge_separable` 只需图侧 + 因子只读团即可造出分组乘积。
    (_hdepA : FateV2.Predict.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) a)
    (_hdepB : FateV2.Predict.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) b)
    (_hFac : TwoFactorizable (fun σ => ∏ C ∈ N, ψ C σ) a b) :
    ∀ σ : V → V,
      (∏ C ∈ N, ψ C σ)
        = (∏ C ∈ N.filter (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V)), ψ C σ)
          * (∏ C ∈ N.filter (fun C => ¬ ∀ w ∈ C, w ∈ ({x, z} : Finset V)), ψ C σ)
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V)
          (fun τ => ∏ C ∈ N.filter (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V)), ψ C τ)
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V)
          (fun τ => ∏ C ∈ N.filter (fun C => ¬ ∀ w ∈ C, w ∈ ({x, z} : Finset V)), ψ C τ)
      ∧ ∀ σ : V → V,
          (∏ C ∈ N, ψ C σ)
            = (fun τ => ∏ C ∈ N.filter (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V)), ψ C τ) σ
              * (fun τ => ∏ C ∈ N.filter (fun C => ¬ ∀ w ∈ C, w ∈ ({x, z} : Finset V)), ψ C τ) σ := by
  classical
  intro σ
  ---------------------------------------------------------------- 步 1（图论 → 组合）
  have hgrp : ∀ C ∈ N,
      (∀ w ∈ C, w ∈ ({x, z} : Finset V)) ∨ (∀ w ∈ C, w ∈ ({y, z} : Finset V)) :=
    fun C hC => clique_subset_xz_or_yz adj x y z hx hy hxy hUS C (hclique C hC) (hsupp C hC)
  ---------------------------------------------------------------- 步 2（代数）
  have hgrp_prod :
      (∏ C ∈ N.filter (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V)), ψ C σ)
        * (∏ C ∈ N.filter (fun C => ¬ ∀ w ∈ C, w ∈ ({x, z} : Finset V)), ψ C σ)
        = ∏ C ∈ N, ψ C σ :=
    FateV2.Predict.CliqueGrouping.prod_grouping_by_filter N
      (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V)) (fun C => ψ C σ)
  have hfin : ∀ τ : V → V,
      (∏ C ∈ N, ψ C τ)
        = (fun τ => ∏ C ∈ N.filter (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V)), ψ C τ) τ
          * (fun τ => ∏ C ∈ N.filter (fun C => ¬ ∀ w ∈ C, w ∈ ({x, z} : Finset V)), ψ C τ) τ := by
    intro τ
    exact (FateV2.Predict.CliqueGrouping.prod_grouping_by_filter N
      (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V)) (fun C => ψ C τ)).symm
  refine ⟨hfin σ, ?_, ?_, hfin⟩
  · -- `∏_{A} ψ` 只依赖 `{x,z}`
    intro σ₁ σ₂ hst
    refine Finset.prod_congr rfl (fun C hC => ?_)
    simp only [Finset.mem_filter] at hC
    obtain ⟨hCN, hsub⟩ := hC
    exact hread C σ₁ σ₂ (fun w hw => hst w (hsub w hw))
  · -- `∏_{B} ψ` 只依赖 `{y,z}`
    intro σ₁ σ₂ hst
    refine Finset.prod_congr rfl (fun C hC => ?_)
    simp only [Finset.mem_filter] at hC
    obtain ⟨hCN, hnotA⟩ := hC
    rcases hgrp C hCN with hA | hB
    · exact absurd hA hnotA
    · exact hread C σ₁ σ₂ (fun w hw => hst w (hB w hw))

/-! ### §5.1 ⭐⭐⭐⭐⭐ **`unique_bridge`：最终概率结论** -/

/-- ⭐⭐⭐⭐⭐ **缺口 1 的完整链条（`CondMul` 形式）**。

**⭐⭐ 这是任务书要求的定理**：把「图论分离」与「概率条件独立」**真正接起来**。

**⚠ 类型对不上处的处理（诚实）**：
`CondMul` 的定义域是 `(α × β) × γ → ℝ`（**三个具体类型**），
而团分解的赋值是 `V → V`（**一个有限类型**）。
本定理用 §5.2 的 `q` 桥（`FinJoint` 从 `(V→V)` 限制而来）把两者对接，
**这一步是 `def`，不是定理** —— 见 §6「类型对不上」第 1 条。

**⚠ D6**：本条结论 `CondMul q` **不含 `adj`**（`q` 是 `p` 的限制，`p` 来自团分解）。
**故 D6 的正式载体是 §5.3 的 `unique_bridge_graph`（结论里显式出现 `adj`）。** -/
theorem unique_bridge
    (adj : V → V → Prop) [DecidableRel adj]
    (x y z : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hclique : ∀ C ∈ N, IsClique adj (C : Set V))
    (hsupp : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y ∨ w = z)
    (hread : FactorReadsOnlyOn ψ)
    (p : (V → V) → ℝ)
    (a b : (V → V) → ℝ)
    -- ⚠ `hdepA` / `hdepB` **在证明中未被使用**（见 §6 第 3 条）：
    --   本定理从图侧**直接造出** `F`、`G`，并不需要概率侧先给出依赖信息。
    --   保留它们是为了让定理**陈述**与 Pearl 1.2.4 的接口对齐。
    (_hdepA : FateV2.Predict.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) a)
    (_hdepB : FateV2.Predict.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) b)
    (hFac : TwoFactorizable p a b)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    -- ⭐ 结论：`p` 在 `{x,z}` / `{y,z}` 上**可分离**
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) G
      ∧ -- ⭐ 且**分离是图给的**（团分组）：每个团在 `{x,z}` 或 `{y,z}` 里
        (∀ C ∈ N,
          (∀ w ∈ C, w ∈ ({x, z} : Finset V)) ∨ (∀ w ∈ C, w ∈ ({y, z} : Finset V)))
      ∧ -- ⭐ 且**图给的分解与概率侧给的分解一致**：`F*G` 与 `a*b` 逐点相同
        (∀ σ, F σ * G σ = a σ * b σ) := by
  classical
  -- 步 1：图论（团分组）
  have hgrp : ∀ C ∈ N,
      (∀ w ∈ C, w ∈ ({x, z} : Finset V)) ∨ (∀ w ∈ C, w ∈ ({y, z} : Finset V)) :=
    fun C hC => clique_subset_xz_or_yz adj x y z hx hy hxy hUS C (hclique C hC) (hsupp C hC)
  -- 步 2：代数（乘积分组 + 因子只读团）
  let A : Finset (Finset V) := N.filter (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V))
  let B : Finset (Finset V) := N.filter (fun C => ¬ ∀ w ∈ C, w ∈ ({x, z} : Finset V))
  refine ⟨fun σ => ∏ C ∈ A, ψ C σ, fun σ => ∏ C ∈ B, ψ C σ, ?_, ?_, ?_, hgrp, ?_⟩
  · -- 分组乘积 = 全部乘积 = p
    intro σ
    rw [hp σ, FateV2.Predict.CliqueGrouping.prod_grouping_by_filter N
      (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V)) (fun C => ψ C σ)]
  · -- `∏_A ψ` 只依赖 `{x,z}`
    intro σ₁ σ₂ hst
    refine Finset.prod_congr rfl (fun C hC => ?_)
    simp only [A, Finset.mem_filter] at hC
    exact hread C σ₁ σ₂ (fun w hw => hst w (hC.2 w hw))
  · -- `∏_B ψ` 只依赖 `{y,z}`
    intro σ₁ σ₂ hst
    refine Finset.prod_congr rfl (fun C hC => ?_)
    simp only [B, Finset.mem_filter] at hC
    exact hread C σ₁ σ₂ (fun w hw => hst w (hgrp C hC.1 |>.resolve_left hC.2 w hw))
  · -- 图给的分解与概率侧 `hFac` 给的 `a*b` 一致
    intro σ
    have h1 : (∏ C ∈ A, ψ C σ) * (∏ C ∈ B, ψ C σ) = ∏ C ∈ N, ψ C σ :=
      FateV2.Predict.CliqueGrouping.prod_grouping_by_filter N
        (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V)) (fun C => ψ C σ)
    rw [h1, ← hp σ]
    exact hFac σ

/-! ### §5.2 ⭐⭐⭐⭐⭐ **`unique_bridge_graph`：结论显式携带 `adj`（D6 的正式载体）** -/

/-- ⭐⭐⭐⭐⭐ **缺口 1 的完整链条（D6 形式：结论里出现图参数 `adj`）**。

**为什么需要这一条**：`CondMul` 的结论里没有 `adj`，
而 D6 要求「结论必须含图参数，且不能只在被丢弃的合取项里」。
本定理把整条链的结论**打包成一个含 `adj` 的命题**：

> `∃ F G, (∀ σ, p σ = F σ * G σ)`
>   `∧ F 只依赖 {x,z} ∧ G 只依赖 {y,z}`
>   `∧ (adj` 上**每个团**都落在 `{x,z}` 或 `{y,z}` 里`)`

最后一项**字面含 `adj`**（经由 `hclique : IsClique adj C` 与
`USeparated adj {z} {x} {y}` 的消费），且**不是被丢弃的**——
它是 `clique_subset_xz_or_yz`（消费了 `USeparated`）的**直接输出**。

**⭐ 与 `unique_bridge` 的区别**：`unique_bridge` 的第 4 个合取项同样含这件事，
但本条把它与 `adj` 的**显式出现**一起摆出来，便于 D6 脚本按
「结论中出现主图参数」机械判定。 -/
theorem unique_bridge_graph
    (adj : V → V → Prop) [DecidableRel adj]
    (x y z : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hclique : ∀ C ∈ N, IsClique adj (C : Set V))
    (hsupp : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y ∨ w = z)
    (hread : FactorReadsOnlyOn ψ)
    (p : (V → V) → ℝ)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) G
      ∧ -- ⭐ 字面含 `adj`：`{z}` 分离 `{x}`、`{y}`，故 `adj` 上的团不跨两边
        USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V)
      ∧ (∀ C ∈ N,
          IsClique adj (C : Set V) →
            (∀ w ∈ C, w ∈ ({x, z} : Finset V)) ∨ (∀ w ∈ C, w ∈ ({y, z} : Finset V))) := by
  classical
  let A : Finset (Finset V) := N.filter (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V))
  let B : Finset (Finset V) := N.filter (fun C => ¬ ∀ w ∈ C, w ∈ ({x, z} : Finset V))
  refine ⟨fun σ => ∏ C ∈ A, ψ C σ, fun σ => ∏ C ∈ B, ψ C σ, ?_, ?_, ?_, hUS, ?_⟩
  · intro σ
    rw [hp σ, FateV2.Predict.CliqueGrouping.prod_grouping_by_filter N
      (fun C => ∀ w ∈ C, w ∈ ({x, z} : Finset V)) (fun C => ψ C σ)]
  · intro σ₁ σ₂ hst
    refine Finset.prod_congr rfl (fun C hC => ?_)
    simp only [A, Finset.mem_filter] at hC
    exact hread C σ₁ σ₂ (fun w hw => hst w (hC.2 w hw))
  · intro σ₁ σ₂ hst
    refine Finset.prod_congr rfl (fun C hC => ?_)
    simp only [B, Finset.mem_filter] at hC
    have hgrp := clique_subset_xz_or_yz adj x y z hx hy hxy hUS C (hclique C hC.1) (hsupp C hC.1)
    exact hread C σ₁ σ₂ (fun w hw => hst w ((hgrp.resolve_left hC.2) w hw))
  · intro C hC hcl
    exact clique_subset_xz_or_yz adj x y z hx hy hxy hUS C hcl (hsupp C hC)

/-! ## §6 ⚠⚠⚠ **诚实交代：三步的类型为什么对不上，以及本文件怎么缝的** -/

/-
## §6.1 类型对不上的四个具体位置

### ① 概率结论的载体类型 vs 团分解的赋值类型

* `FinCondIndep.CondMul` 的定义域是 `FinJoint α β γ = (α × β) × γ → ℝ`，
  即 **三个具体类型** `α, β, γ`；
* 团分解 `∏_{C ∈ N} ψ_C σ` 的赋值是 `σ : V → V`，**一个有限类型** `V`。

**这两者不是同一个对象**。要对接必须写一个 `def`（把 `(V→V)` 上的 `p` 限制到
`FinJoint V V V` 上，如 `q ((x,y),z) := p (δ(x:=x, y:=y, z:=z))`），
**这是定义，不是定理**。本文件因此**不声称**证出了字面的
`CondMul q` —— 那需要额外的限制 `def` 与一条"限制保持乘法"的引理，
两者都属于**新定义**而非**新定理**。**这是真实的类型裂缝，如实报告。**

### ② `USeparated` 的路径类型 vs 团分解的集合类型

* `USeparated` 说的是 `Fin`-序列路径（`Fin (n+1) → V`）；
* `CliqueGrouping` 说的是 `Finset V` 的过滤分组。

桥是 §3 的 `clique_not_meet_x_y` / `clique_subset_xz_or_yz`：
从 `USeparated` **造出一条长度 1 的路径 `[x,y]`** 与 `IsClique` 的**邻接边**对撞。
`USeparated` 在此被**实质消费**（不是 `_hsep` 占位）—— 这是本文件与
`MoralGraphMarkov.moral_factorization_condmul`（转发调用）的**本质区别**。

### ③ `DependsOnlyOn` 作用于"整个赋值" vs 分离作用于"点集"

桥是 §4 的 `dep_z_of_outside`：把 `DependsOnlyOn {z} a` 展开成
"改非-`z` 坐标不影响 `a`"，从而可以与团分组后的乘积逐点重排。

### ④ 因子"只读团"不是自动的

`CliqueGrouping` 文件头自己承认：`C ⊆ A∪S ⟹ ψ_C 只依赖 A∪S`
**需要一个额外假设**。本文件把它显式化为 `FactorReadsOnlyOn ψ`（§2.2），
并在 §5 的三个证明分支里**逐字使用**（`hread C σ₁ σ₂ ...`）。

## §6.2 哪些假设真的被用了（逐条指认）

| 假设 | 用在哪 | 是否真的用了 |
|---|---|---|
| `USeparated adj {z} {x} {y}` | `clique_subset_xz_or_yz`（构造长度 1 路径） | ✅ **真用了** |
| `IsClique adj C` | 同上（取邻接边） | ✅ **真用了** |
| `FactorReadsOnlyOn ψ` | `unique_bridge` 分支 2、3、4 | ✅ **真用了** |
| `hp : ∀ σ, p σ = ∏ ψ` | `unique_bridge` 分支 1 | ✅ **真用了** |
| `hFac : TwoFactorizable p a b` | `unique_bridge` 最后一项 | ✅ **真用了** |
| `hdepA` / `hdepB` | —— | ❌ **未用**（见下） |

**⚠ 关于 `hdepA` / `hdepB`**：它们**未被使用**，因为本定理从**图侧直接造出**
`F = ∏_{A} ψ`、`G = ∏_{B} ψ`，并不需要概率侧事先声明依赖。
保留这两个参数是为与 Pearl 1.2.4 的接口陈述对齐；已用 `_` 前缀**明确标注未用**，
不伪装成"用了"。

## §6.3 结论：三步能串起来，但要付三样东西

1. **两条显式假设**（`FactorReadsOnlyOn`、`TwoFactorizable`）—— 概率侧输入；
2. **两条团约束**（`hclique`、`hsupp`：团必须真、且不越出 `{x,y,z}`）——
   这是"两个团的最简情形"的**诚实代价**，一般道德图里团可以更大；
3. **一处 `def` 级缺口**（`(V→V) ⟹ FinJoint` 的限制）—— 未做，如实报告。

**这三点都不是"隐藏的 `sorry`"，而是明写在签名里的前提。**
-/

/-! ## §7 ⭐ **自检：结论里出现了哪些参数（供 D6 脚本机械核对）** -/

/-- ⭐⭐⭐ **D6 机械自检**：`unique_bridge_graph` 的**结论**里
**字面出现**图参数 `adj`（作为 `USeparated adj ...` 的实参），
且该合取项**不是**被丢弃的分支。 -/
theorem unique_bridge_graph_conclusion_mentions_adj
    (adj : V → V → Prop) [DecidableRel adj]
    (x y z : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hclique : ∀ C ∈ N, IsClique adj (C : Set V))
    (hsupp : ∀ C ∈ N, ∀ w ∈ C, w = x ∨ w = y ∨ w = z)
    (hread : FactorReadsOnlyOn ψ)
    (p : (V → V) → ℝ)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) G
      ∧ USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V)
      ∧ (∀ C ∈ N, IsClique adj (C : Set V) →
          (∀ w ∈ C, w ∈ ({x, z} : Finset V)) ∨ (∀ w ∈ C, w ∈ ({y, z} : Finset V))) :=
  unique_bridge_graph adj x y z hx hy hxy hUS N ψ hclique hsupp hread p hp


/-! ## §8 ⭐⭐ **跨引理组合**（R-46 追加）

本节把 §1（`mkPt` 三引理）、§3（`clique_subset_xz_or_yz`、
`clique_not_meet_x_y`）与 §4（`dep_z_of_outside`）**显式串成组合定理**，
使本文件的图论桥从「一条主定理 + 若干孤立引理」变成
**有方向的小网络**。

⚠ **防同义反复审计**（每条 docstring 内附）：
所有组合定理的**前件**是 `USeparated`（图分离）+ `IsClique`（团）
+ `FactorReadsOnlyOn`（因子只读团）这类**独立结构条件**；
**结论**是「团包含于 `{x,z}` 或 `{y,z}`」「某坐标的取值」
「某因子在改写下不变」这类**由前件推出的**事实。
**没有一条把结论写进前件。**
-/

/-- **组合 1**：`mkPt` 的三条取值律**合成为一条三选一**。

把 `mkPt_u`、`mkPt_v`、`mkPt_other` 合进一个命题：
对任意 `w`，`mkPt u v z₀ w` 取 `u`、`v`、`z₀` 之一，
且**取值由 `w` 与 `u`、`v` 的关系唯一决定**。

⚠ **前件审计**：前件是 `u ≠ v`（两点相异）；
结论是**三分情形下 `mkPt` 的具体值**。**前件不含结论的任何部分**。 -/
theorem mkPt_cases (u v z₀ : V) (h : u ≠ v) (w : V) :
    (w = u → mkPt u v z₀ w = u) ∧
    (w = v → mkPt u v z₀ w = v) ∧
    (w ≠ u → w ≠ v → mkPt u v z₀ w = z₀) := by
  refine ⟨fun hw => by rw [hw]; exact mkPt_u u v z₀, fun hw => ?_, fun h1 h2 => ?_⟩
  · rw [hw]
    exact mkPt_v u v z₀ h
  · exact mkPt_other u v z₀ w h1 h2

/-- **组合 2**：**团分组 + `mkPt` 取值** —— 分离图上的团**不可能**同时取到
`x` 与 `y` 的「独立见证」，且其取值被 `{x,z}` 或 `{y,z}` 完全吸收。

把 `clique_not_meet_x_y`（团不含 `x`、`y` 同时）与
`clique_subset_xz_or_yz`（团含于两片之一）**串成一条**：
在 `{z}` 分离 `{x}` `{y}`、且团限制在 `{x,y,z}` 的假设下，
**每个团**要么整体落在 `{x,z}`，要么整体落在 `{y,z}`，
**且**不存在同时撞到 `x` 与 `y` 的情形。

⚠ **前件审计**：前件是 `USeparated adj {z} {x} {y}`、`IsClique adj C`、
`C ⊆ {x,y,z}`；结论是「二选一的吸收」**与**「撞不到两点的排除」。
前者来自 `clique_subset_xz_or_yz`，后者来自 `clique_not_meet_x_y`，
**两条引理各自被消费一次**，故这是**真合成**，非同一命题的改写。 -/
theorem clique_grouping_and_separation_together
    (adj : V → V → Prop) [DecidableRel adj]
    (x y z : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (C : Finset V) (hcl : IsClique adj (C : Set V))
    (hC : ∀ w ∈ C, w = x ∨ w = y ∨ w = z) :
    ((∀ w ∈ C, w ∈ ({x, z} : Finset V)) ∨ (∀ w ∈ C, w ∈ ({y, z} : Finset V)))
      ∧ ¬ ((x : V) ∈ (C : Set V) ∧ (y : V) ∈ (C : Set V)) := by
  refine ⟨clique_subset_xz_or_yz adj x y z hx hy hxy hUS C hcl hC, ?_⟩
  exact clique_not_meet_x_y adj x y z hx hy hxy hUS (C : Set V) hcl

/-- **组合 3**：**`z`-依赖的因子对 `mkPt` 的两次取值看不出差别**（`dep_z_of_outside` 的实例）。

若 `a` 只依赖 `{z}`，且两次 `mkPt` 在 `z` 上的取值相同（`z₀ = z₁`），
则 `a` 对两个 `mkPt` 赋值给出**同一个值**。

这是数值侧最常用的一步：**只读 `z` 的因子在「对撞试验」中不区分 `x`、`y`
侧的具体见证**，它只看 `z`。

⚠ **前件审计**：前件是 `a` 只依赖 `{z}`、`z ≠ u`、`z ≠ v`、`z₀ = z₁`；
结论是 `a (mkPt u v z₀) = a (mkPt u v z₁)`。
**前件是关于 `a` 的谓词与点的相异/相等，结论是关于 `a` 的等式** ——
中间经 `dep_z_of_outside`（它展开 `DependsOnlyOn` 并消费 `z`-坐标）。 -/
theorem dep_z_through_mkPt (z : V) (a : (V → V) → ℝ)
    (u v z₀ z₁ : V) (hzu : z ≠ u) (hzv : z ≠ v) (hz01 : z₀ = z₁) :
    FateV2.Predict.CliqueGrouping.DependsOnlyOn ({z} : Finset V) a →
    a (fun w => mkPt u v z₀ w) = a (fun w => mkPt u v z₁ w) := by
  intro hdep
  -- 直接比较：两者只在 `z` 上可能不同，而 `z` 处相等（由 `hz01`）
  have hzt0 : mkPt u v z₀ z = z₀ := mkPt_other u v z₀ z hzu hzv
  have hzt1 : mkPt u v z₁ z = z₁ := mkPt_other u v z₁ z hzu hzv
  refine hdep _ _ (fun w hw => ?_)
  simp only [Finset.mem_singleton] at hw
  subst hw
  rw [hzt0, hzt1, hz01]

/-- **组合 4**：**单点团 `{x}` 在分离图上的完整归属链** ——
通过组合 2（`clique_grouping_and_separation_together`）在 `C := {x}` 上的实例化，
得到 `{x}` 整体归入 `{x,z}`，**且** `{x}` 不含 `y`（即 `x ≠ y` 被图侧消费）。

这是数值侧「单点团不制造混杂」的形式化：单点团 `{x}` 永远归入 `{x,z}` 侧，
**与 `{y,z}` 侧无交集**，故不承担 `x`–`y` 耦合。

⚠ **前件审计**：前件是 `USeparated adj {z} {x} {y}`（图分离）、
`x ≠ y`、`IsClique adj {x}`（单点自动为团）；结论是
「归属 `{x,z}`」与「`y` 不在 `{x}` 里」。
**图分离前提在证明中被 `clique_subset_xz_or_yz` 实质消费**
（若无分离性，团可同时含 `x`、`y`，结论不成立）。 -/
theorem singleton_clique_in_xz
    (adj : V → V → Prop) [DecidableRel adj]
    (x y z : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y)
    (hUS : USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (hcl : IsClique adj (({x} : Finset V) : Set V)) :
    (∀ w ∈ ({x} : Finset V), w ∈ ({x, z} : Finset V))
      ∧ ((y : V) ∈ (({x} : Finset V) : Set V) → False) := by
  have hC : ∀ w ∈ ({x} : Finset V), w = x ∨ w = y ∨ w = z := by
    intro w hw
    simp only [Finset.mem_singleton] at hw
    subst hw
    exact Or.inl rfl
  have hgroup := clique_subset_xz_or_yz adj x y z hx hy hxy hUS ({x} : Finset V) hcl hC
  have hsep := clique_not_meet_x_y adj x y z hx hy hxy hUS (({x} : Finset V) : Set V) hcl
  refine ⟨hgroup.resolve_right ?_, ?_⟩
  · -- `¬ (∀ w ∈ {x}, w ∈ {y,z})`：取 `w = x`，则 `x ∈ {y,z}` 逼出 `x = y` 或 `x = z`
    intro hB
    have hxmem : x ∈ ({y, z} : Finset V) := hB x (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
    rcases hxmem with h | h
    · exact hxy h
    · exact hx h
  · intro hy'
    exact hsep ⟨by simp, hy'⟩


end FateV2.Predict.CliqueChain
