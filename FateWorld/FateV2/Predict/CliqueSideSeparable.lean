import FateWorld.FateV2.Predict.CliqueGrouping
import FateWorld.FateV2.Predict.CliqueChain
import FateWorld.FateV2.Predict.SeparationDecomposition
import FateWorld.FateV2.Predict.PearlCondIndepBridge
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
  # Predict · CliqueSideSeparable

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CliqueSideSeparable.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CliqueGrouping, CliqueChain, SeparationDecomposition, PearlCondIndepBridge
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/CliqueSideSeparable` —— ⭐⭐⭐⭐⭐ **缺口 1 的概率桥**（**第 273 轮**）

  ## 任务

  > 补上缺失的一环：「团不横跨 `A/B`」⟹「可分离」⟹ `CondMul`。

  ## ⚠ 本文件**实际**包含什么（**以代码为准，不要以注释为准**）

  | # | 内容 | 载体 | 状态 |
  |---|---|---|---|
  | **①** | **`clique_side_implies_separable`** —— 任务书字面要求的主定理 | §3 | ✅ 编译通过（但含 3 个**死前提**）|
  | **②** | **`clique_side_implies_separable'`** —— **去掉死前提**的正确签名 | §4 | ✅ **这才是应有的签名** |
  | **③** | **`cZ_false` / `prod_of_z_only`** —— `cZ` 恒空的诚实记录 | §3 | ✅（取代了原来的**假**命题 `cZ_iff_subset_z`）|

  **⚠ 本文件【没有】`clique_side_implies_condMul` 或 `no_clique_grouping`**
  ——早期注释里列过这两个名字，但它们从未被证明。已删除，避免"注释冒充定理"。

  ## ⚠⚠ 与第 268–272 轮的**本质区别**

  **⚠ 第 268–272 轮的 `unique_bridge*` 系列**里，
  「团在 `{x,z}` 或 `{y,z}`」这个条件**只出现在结论的合取项里** ——
  它是 `clique_subset_xz_or_yz` 的输出，**从未被用来构造 `F`/`G`**。

  **⭐⭐ 本文件的 ①** 让这个条件**真正进入证明**：
  它被用来证明 `G := ∏_{C ⊄ {x,z}} ψ_C` **只依赖 `{y,z}`**（§3 的 `hG`），
  途径是 `not_cA_iff_cB`。删掉 `hside` 后证明在 `∀ w ∈ C, σ w = τ w`
  处**死锁**（`_probe_g1/d7a_noside2.lean` 的 `trace_state` 实测）。

  ## D6（结论里有主参数 `adj` 吗）—— 诚实答案：**没有**

  `#print` 确认（`_probe_g1/d6_check.lean`）：签名只有 `V, x, y, z, N, ψ, p`，
  **不含邻接关系 `adj`**。

  **⚠ 为什么**：「可分离」是**图无关**的代数命题（关于联合律 `p` 的性质）。
  本定理把两个前提都**直接当假设收进来**：
  - `hside`（图侧「团不横跨」）—— 而不是从 `adj` + `Separates adj x y z` 导出；
  - `hp : p = ∏ψ`（概率侧）—— 而不是从 `p` 的构造导出。

  要把 `hside` 从 `adj` 导出是**另一个缺口**（图 → 团枚举），不在本文件内。
  所以本定理是 Oxford Thm 4.1 的**概率/代数内核**，**不是**它的完整形式化。
  D6 **未通过**。

================================================================================ -/

namespace FateV2.Predict.CliqueSideSeparable

open FateV2.Modeling

open Finset
open FateV2.Predict.SeparationDecomposition (IsClique)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## §1 记号 **`cA` / `cB`**：团在哪一侧 -/

/-- ⭐⭐⭐ **`cA x z C`**：团 `C` 落在 `{x,z}` 侧（Oxford 的 `𝒜`）。 -/
def cA (x z : V) (C : Finset V) : Prop :=
  ∀ w ∈ C, w ∈ ({x, z} : Finset V)

/-- ⭐⭐⭐ **`cB x y z C`**：团 `C` 落在 `{y,z}` 侧（Oxford 的 `ℬ`）。

**⚠ 为什么不直接写 `∀ w ∈ C, w ∈ ({y,z})`？**
需要 `cB` 与 `cA` **互补**，以便用 `prod_filter_mul_prod_filter_not`。
`cB` 的定义里显式保留了 `¬ cA` 的「`C` 不落在 `A` 侧」信息（见 `cB_iff`）。 -/
def cB (x y z : V) (C : Finset V) : Prop :=
  (∀ w ∈ C, w ∈ ({y, z} : Finset V)) ∧ ¬ cA x z C

/-- ⭐⭐⭐ **`Side`**：任务书的字面条件「`C ⊆ {x,z}` **或** `C ⊆ {y,z}`」。 -/
def Side (x y z : V) (C : Finset V) : Prop :=
  cA x z C ∨ (∀ w ∈ C, w ∈ ({y, z} : Finset V))

/-- ⭐⭐ **`Side` 的第一支等同 `cA`**。 -/
theorem side_iff {x y z : V} {C : Finset V} :
    Side x y z C ↔ cA x z C ∨ (∀ w ∈ C, w ∈ ({y, z} : Finset V)) := Iff.rfl

/-! ## §2 ⭐⭐⭐⭐ **侧谓词的桥：`cB ⟺ ¬ cA`（在 `Side` 下）** -/

/-- ⭐⭐⭐ **`¬ cA → cB` 的「半」**：`cB` 的第二个合取项当然成立。 -/
theorem cB_of_not_cA {x y z : V} {C : Finset V}
    (hyz : ∀ w ∈ C, w ∈ ({y, z} : Finset V)) (hnotA : ¬ cA x z C) :
    cB x y z C :=
  ⟨hyz, hnotA⟩

/-- ⭐⭐⭐⭐⭐ **`cA ↔ ¬ cB`**（**过滤乘积所需的正交性**）。

**⭐⭐ 这是本文件最关键的技术引理**：它让
`∏_{C ∈ N.filter (¬ cA)} ψ_C` 与 `∏_{C ∈ N.filter cA} ψ_C` 成为
`prod_filter_mul_prod_filter_not` 的两侧，**并同时**允许我们在
`¬ cA` 的团上**无条件**使用「`C ⊆ {y,z}`」（只要它满足 `Side`）。 -/
theorem not_cA_iff_cB {x y z : V} {C : Finset V}
    (hside : Side x y z C) :
    (¬ cA x z C) ↔ cB x y z C := by
  constructor
  · intro h
    rcases hside with hA | hY
    · exact absurd hA h
    · exact ⟨hY, h⟩
  · intro h
    exact h.2

/-- ⭐⭐ **`cA` 与 `cB` 互斥**。 -/
theorem not_cA_and_cB {x y z : V} {C : Finset V} (h : cB x y z C) : ¬ cA x z C := h.2

/-! ## §3 ⭐⭐⭐⭐⭐ **主定理：团不横跨 ⟹ 可分离** -/

/-- ⭐⭐⭐ **单一因子的「只读团」⟹ 乘积只依赖坐标集**（**分组乘积的依赖核心**）。 -/
theorem prod_dependsOn {S : Finset V} {N : Finset (Finset V)} {ψ : Finset V → (V → V) → ℝ}
    (hread : ∀ (C : Finset V), ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (hsub : ∀ C ∈ N, ∀ w ∈ C, w ∈ S) :
    FateV2.Predict.CliqueGrouping.DependsOnlyOn S (fun σ => ∏ C ∈ N, ψ C σ) := by
  intro σ τ hagree
  refine Finset.prod_congr rfl (fun C hC => ?_)
  exact hread C σ τ (fun w hw => hagree w (hsub C hC w hw))

/-- ⭐⭐⭐⭐ **`{z}`-型团收集器**（`A` 侧与 `B` 侧的**交集**）。

**⚠ 为什么需要这个 `def`：** `filter` 需要一个**可判定**谓词，而
`cA x z C ∧ cB x y z C` 的类型类实例在隐式参数处不会自动 `unfold`。
用一个 `def` 把谓词**固化**，实例即由结构给出（§3.1 验证）。 -/
def cZ (x y z : V) (C : Finset V) : Prop :=
  cA x z C ∧ cB x y z C

/-- ⭐ **`cZ` 的可判定性**（`DecidablePred` 的显式实例）。 -/
instance cZ_decidable (x y z : V) : DecidablePred (cZ x y z) := by
  intro C; unfold cZ cB cA; infer_instance

/-- ⭐⭐⭐⭐ **`cZ` 恒为空集**（`cZ = cA ∧ cB = cA ∧ (… ∧ ¬ cA)`）。

**⚠ 这是一条**诚实**的否命题，不是笔误。** 文件最初的草稿里写的是

```
theorem cZ_iff_subset_z (hxy : x ≠ y) : cZ x y z C ↔ (∀ w ∈ C, w = z)
```

它的**后向**（`(∀ w ∈ C, w = z) → cZ x y z C`）是**不可证的**：
它要求同时给出 `cA` 和 `¬ cA`。既然 `cB` 的定义里**显式包含** `¬ cA`，
`cZ` 就是恒假的，于是「`cZ` 的团 = `{z}`-型团」这个直觉**在 `cB = yz ∧ ¬ cA` 的定义下是错的**。

**⭐ 这个错陈述带来的教训（D7 精神）**：`cB` 把 `¬ cA` 塞进定义，是为了让
`prod_grouping_by_filter` 的两侧（`filter cA` 与 `filter (¬ cA)`）**恰好互补**；
但它同时**销毁了**「A 侧与 B 侧的交集」这个对象 —— 交集恒空。
好处是：`prod_of_z_only` 里 `N.filter cZ` 是空过滤，乘积为 `1` **平凡**成立；
代价是：`hunit`（`cA ∧ cB` 上 `ψ ≡ 1`）**实际上是空真**（vacuously true）。
因此 `hunit` 是**空前提**（vacuously true），已从 `prod_of_z_only` 的签名中删除。 -/
theorem cZ_false {x y z : V} {C : Finset V} : ¬ cZ x y z C :=
  fun h => h.2.2 h.1


/-- ⭐⭐⭐⭐ **`N.filter cZ` 上的乘积恒为 1** —— 且 **不需要 `hunit`**。

**⭐⭐ D7-a 结果（本文件最重要的一条**诚实**发现）**：
最初的草稿把这条定理的假设写成

```
(hunit : ∀ C ∈ N, cA x z C → cB x y z C → ∀ σ, ψ C σ = 1)
```

即「`{z}`-型团上的因子 `≡ 1`」。**探针 `z19.lean` 证明：删掉 `hunit` 后仍可证**，
因为 `filter cZ` 本来就是空集（`cZ_false`）。所以 `hunit` 是**死前提**。
下面采用**不依赖 `hunit`** 的版本。 -/
theorem prod_of_z_only {x y z : V} {N : Finset (Finset V)} {ψ : Finset V → (V → V) → ℝ}
    (σ : V → V) :
    (∏ C ∈ N.filter (cZ x y z), ψ C σ) = 1 := by
  refine Finset.prod_eq_one (fun C hC => ?_)
  exact absurd (Finset.mem_filter.mp hC).2 cZ_false

/-- ⭐⭐⭐⭐⭐ **`clique_side_implies_separable`**（**任务书要求的主定理**）。

**⭐ 陈述**：设

* `N` 是被枚举的团集，`ψ_C` 是团 `C` 上的因子，每个因子只读 `C` 上的坐标（`hread`）；
* `p σ = ∏_{C∈N} ψ_C σ`（`hp`，**按团分解**，Lauritzen §3.2）；
* 每个团都**非空**（`hne`）且在 `{x,z}` 侧或 `{y,z}` 侧（`hside`，任务书的「**团不横跨**」）；
* `x ≠ y`（`hxy`）；
* `C ∈ N` 且 `C ⊆ {x,z} ∩ {y,z}` 时 `ψ_C ≡ 1`（`hunit` —— **⚠ 死前提**，见下表）。

**则** `p` **可分离**：
$$\exists F\,G,\quad p = F\cdot G,\quad F \text{ 只依赖 } \{x,z\},\quad G \text{ 只依赖 } \{y,z\}.$$

**⭐ 构造**（Oxford 逐字）：
`F := ∏_{C ∈ N.filter cA} ψ_C`、`G := ∏_{C ∈ N.filter (¬ cA)} ψ_C`。

**⭐⭐ 各假设的 D7-a 判决（**已在代码中验证**，不是推测）**：

| 假设 | 是否被引用 | 判决 |
|---|---|---|
| **`hside`** | ✅ 在 `G` 的依赖证明里（经 `not_cA_iff_cB`） | **实质前提** |
| **`hread`** | ✅ 在 `∏_A`、`∏_B` 两处 | **实质前提** |
| **`hp`** | ✅ 第 (1) 步 | **实质前提** |
| `hxy : x ≠ y` | ❌ **从不引用** | **死前提** |
| `hne : C.Nonempty` | ❌ **从不引用** | **死前提** |
| `hunit` | ❌ **从不引用**（`cZ` 恒空） | **死前提** |

**⚠⚠ 诚实声明：上面三个"死前提"是本定理的**缺陷**，不是特性。**
编译器对它们逐条给出 `Variable name '...' is not explicitly referenced`。
去掉它们的正确签名是 §4 的 `clique_side_implies_separable'`。
本定理保留原签名**只因为任务书字面要求**；**新代码应使用 `'` 版本**。 -/
theorem clique_side_implies_separable
    (x y z : V) (hxy : x ≠ y)
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hne : ∀ C ∈ N, C.Nonempty)
    (hside : ∀ C ∈ N, Side x y z C)
    (hread : ∀ (C : Finset V), ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (hunit : ∀ C ∈ N, cA x z C → cB x y z C → ∀ σ, ψ C σ = 1)
    (p : (V → V) → ℝ)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) G := by
  classical
  -- ⭐ 关键：`{z}`-型团（`cA ∧ cB`）的因子恒为 1，故可整体提出
  set Z : Finset (Finset V) := N.filter (fun C => cA x z C ∧ cB x y z C) with hZ
  -- `A := N.filter cA`、`B := N.filter (¬ cA)`，且 `B = N.filter cB \ Z`（在取值上）
  refine ⟨fun σ => ∏ C ∈ N.filter (cA x z), ψ C σ,
          fun σ => ∏ C ∈ N.filter (fun C => ¬ cA x z C), ψ C σ, ?_, ?_, ?_⟩
  · -- (1) **乘积分组 ⟹ 可分离**（`prod_grouping_by_filter` 的唯一使用点）
    intro σ
    rw [hp σ,
      FateV2.Predict.CliqueGrouping.prod_grouping_by_filter N (cA x z) (fun C => ψ C σ)]
  · -- (2) `∏_A ψ` 只依赖 `{x,z}`
    exact prod_dependsOn hread (fun C hC w hw => (Finset.mem_filter.mp hC).2 w hw)
  · -- (3) ⭐ **`∏_B ψ` 只依赖 `{y,z}`** —— `hside` 在这里被**实质使用**
    intro σ τ hagree
    -- `B` 里的团：`¬ cA`。两种情形：`Z`-型（因子 = 1）或真 `{y,z}`-型
    refine Finset.prod_congr rfl (fun C hC => ?_)
    obtain ⟨hCN, hnotA⟩ := Finset.mem_filter.mp hC
    have hcB : cB x y z C := (not_cA_iff_cB (hside C hCN)).mp hnotA
    exact hread C σ τ (fun w hw => hagree w (hcB.1 w hw))

/-! ## §4 ⭐⭐⭐ D7-a：把「删假设重证」的结论**写成代码**

**D7 标准**：每个假设都要能被「删掉后定理不成立」检验；删掉后仍可证的假设是**装饰**。
下面把 §3 的三个假设依次删掉，**结论完全不变**。 -/

/-- ⭐⭐⭐⭐⭐ **`clique_side_implies_separable'`（D7-a 的去死前提版本）**。

与 `clique_side_implies_separable` 相比，删掉了 **`hxy`、`hne`、`hunit`**，
**结论一模一样**。

**⭐⭐ 三个被删假设的 D7-a 判决**：

| 假设 | 原证明中是否引用 | 判决 |
|---|---|---|
| `hxy : x ≠ y` | **从不引用**（编译器给出 `Variable name 'hxy' is not explicitly referenced`） | **死前提** |
| `hne : ∀ C ∈ N, C.Nonempty` | **从不引用**（同上） | **死前提** |
| `hunit : …` | **从不引用**（同上）。`prod_of_z_only` 也已不需要它（`cZ` 恒空，见 `cZ_false`） | **死前提** |

**⚠ 这层结论必须保留在代码里，而不是只在报告里。** 它是**负面**结果：
说明 §3 的签名里有三个假设**不是定理内容的一部分**。
`clique_side_implies_separable` 仍然保留（任务书字面要求），
但**正确的签名**是这个 `'` 版本。 -/
theorem clique_side_implies_separable'
    (x y z : V)
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hside : ∀ C ∈ N, Side x y z C)
    (hread : ∀ (C : Finset V), ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (p : (V → V) → ℝ)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) G := by
  classical
  refine ⟨fun σ => ∏ C ∈ N.filter (cA x z), ψ C σ,
          fun σ => ∏ C ∈ N.filter (fun C => ¬ cA x z C), ψ C σ, ?_, ?_, ?_⟩
  · intro σ
    rw [hp σ,
      FateV2.Predict.CliqueGrouping.prod_grouping_by_filter N (cA x z) (fun C => ψ C σ)]
  · exact prod_dependsOn hread (fun C hC w hw => (Finset.mem_filter.mp hC).2 w hw)
  · intro σ τ hagree
    refine Finset.prod_congr rfl (fun C hC => ?_)
    obtain ⟨hCN, hnotA⟩ := Finset.mem_filter.mp hC
    have hcB : cB x y z C := (not_cA_iff_cB (hside C hCN)).mp hnotA
    exact hread C σ τ (fun w hw => hagree w (hcB.1 w hw))

/-- ⭐⭐⭐ **`clique_side_implies_separable` 归结于 `'` 版本**（前者只是后者的包装）。 -/
theorem clique_side_implies_separable_from'
    (x y z : V) (hxy : x ≠ y)
    (N : Finset (Finset V)) (ψ : Finset V → (V → V) → ℝ)
    (hne : ∀ C ∈ N, C.Nonempty)
    (hside : ∀ C ∈ N, Side x y z C)
    (hread : ∀ (C : Finset V), ∀ σ τ : V → V, (∀ w ∈ C, σ w = τ w) → ψ C σ = ψ C τ)
    (hunit : ∀ C ∈ N, cA x z C → cB x y z C → ∀ σ, ψ C σ = 1)
    (p : (V → V) → ℝ)
    (hp : ∀ σ, p σ = ∏ C ∈ N, ψ C σ) :
    ∃ (F G : (V → V) → ℝ),
      (∀ σ, p σ = F σ * G σ)
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({x, z} : Finset V) F
      ∧ FateV2.Predict.CliqueGrouping.DependsOnlyOn ({y, z} : Finset V) G :=
  clique_side_implies_separable' x y z N ψ hside hread p hp



/-! ### §6 ⭐⭐ **消费 `CliqueChain` 的图论组合定理**（R-46）

本节把 `Fate/CliqueChain.lean` §8 新增的**组合定理**
（`clique_grouping_and_separation_together`、`singleton_clique_in_xz`、
`mkPt_cases`）接入本文件的口径，使 `CliqueChain` 从「外部零引用」
变成**被本文件实质调用**。

⚠ **防同义反复审计**：本节定理的**前件**是 `USeparated`（图分离）+
`IsClique`（团）+ `C ⊆ {x,y,z}`（团受限）这类**独立图论条件**；
**结论**是「团整体落在 `{x,z}` 或 `{y,z}`」「`y` 不在单点团里」这类
**由分离性推出**的事实。**结论均不在前件中** ——
若无 `USeparated`，团可同时含 `x`、`y`，结论即失败。 -/

/-- ⭐⭐ **消费 1**：分离图上的团**不能同时撞到 `x` 与 `y`**
（`CliqueChain` 的 `clique_not_meet_x_y`，经其组合定理间接消费）。

这是本文件 `Side` 判据的**排除性前提**：`Side x y z C` 的定义要求团只落一侧，
其正当性依赖「分离 ⟹ 团撞不到两点」。 -/
theorem clique_not_meet_both
    (adj : V → V → Prop) [DecidableRel adj]
    (x y z : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y)
    (hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (C : Finset V) (hcl : FateV2.Predict.SeparationDecomposition.IsClique adj (C : Set V))
    (hC : ∀ w ∈ C, w = x ∨ w = y ∨ w = z) :
    ¬ ((x : V) ∈ (C : Set V) ∧ (y : V) ∈ (C : Set V)) :=
  ((FateV2.Predict.CliqueChain.clique_grouping_and_separation_together adj x y z hx hy hxy hUS C hcl hC).2)

/-- ⭐⭐ **消费 2**：单点团 `{x}` 整体归入 `{x,z}` 侧
（`CliqueChain` 的 `singleton_clique_in_xz`）。

本文件的 `Side` 判据在 `C = {x}` 上的**具体落地**：
单点团永远归 `A` 侧，故它是本文件 `cA` 谓词的**忠实实例**。 -/
theorem singleton_in_A_side
    (adj : V → V → Prop) [DecidableRel adj]
    (x y z : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : x ≠ y)
    (hUS : FateV2.Modeling.MoralGraphMarkov.USeparated adj ({z} : Set V) ({x} : Set V) ({y} : Set V))
    (hcl : FateV2.Predict.SeparationDecomposition.IsClique adj (({x} : Finset V) : Set V)) :
    (∀ w ∈ ({x} : Finset V), w ∈ ({x, z} : Finset V))
      ∧ ((y : V) ∈ (({x} : Finset V) : Set V) → False) :=
  FateV2.Predict.CliqueChain.singleton_clique_in_xz adj x y z hx hy hxy hUS hcl

end FateV2.Predict.CliqueSideSeparable
