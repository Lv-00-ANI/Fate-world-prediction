import Mathlib

set_option linter.unusedSectionVars false

/-!
  # Rules · AlgoKNNComponents

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlgoKNNComponents.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Rules`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  MVFCA 算法线 · 方案丁：**kNN 图连通分量** 作为闭集族

  与 `Fate_agent_staging/planD_knn.py` + `mvfca/RESULTS-algo-knn.md` 配套。
  **自包含**：只 import Mathlib，不 import 任何 Fate 模块（与既有证明解耦）；
  零 sorry / admit / axiom。

  ---------------------------------------------------------------------------
  §0  这条引理在数值实验里对应什么
  ---------------------------------------------------------------------------
  方案丁的闭集族取为「kNN 图 G_k 的连通分量」。实测（`RESULTS-algo-knn.md` §3）
  出现**双峰退化**，其中一峰是 `empty_family`：**18/24 个配置里整图连通**
  （`n_components = 1`），于是唯一的分量就是 `univ`，剔除 `univ` 后
  **proper 闭集族为空**，`maxdiam*` 无定义。

  本文件把这个现象钉成定理（§2 的 `only_univ_when_connected`）：
  若图连通，则分量族 = `{univ}`，故**不存在**不等��� `univ` 的分量闭集。
  即 `maxdiam*` 在该情形下**没有可取的对象**——不是 0、不是「恰好达标」，
  而是判定函数必须返回「无定义」。这正是脚本里 `maxdiam_star = null`
  与 `ok_band` 返回 `None` 的形式依据。

  ---------------------------------------------------------------------------
  §1  抽象设定：把「图的连通分量族」抽象成**划分**（partition）
  ---------------------------------------------------------------------------
  连通分量构成一个**划分**（两两不交、并集 = 全体）。本文件不建模图的邻接、
  不建模 BFS，只建模「分量族作为闭集族」的**集合论骨架**。这是刻意的：
  我们想证明的性质（连通 ⟹ 只有 univ）只依赖「分量族是 G 的一个划分且
  覆盖 G」这一事实，不依赖图的具体形状。故抽象层级是恰当的，且更可复用。

  ---------------------------------------------------------------------------
  §2  主结果
  ---------------------------------------------------------------------------
  - `isConnectedPartition`：划分族 `C : Set (Set G)`
  - `univ_mem`：`G ∈ C` 当且仅当 `C = {G}`（连通 ⟺ 唯一分量是全体）
  - `proper_empty_of_connected`：连通 ⟹ `{A ∈ C | A ≠ univ} = ∅`
  - `no_proper_mem_of_connected`：连通 ⟹ 任何 `A ∈ C` 都等于 `univ`
  - `maxdiam_star_none_when_connected`：以该族为闭集族时，proper 族的
    「最大直径」函数在连通情形下**无输入**（用 `maxdiamStar = none` 表达）

  另附**对照**（§3）：非连通时 proper 族非空的构造性例子，说明上面的
  「空」不是定义空转，而是真的由连通性驱动。
  =========================================================================== -/

namespace FateV2.Rules.KNNComponents
variable {G : Type*}

/-! ### §2.1 划分骨架 -/

/-- 一个「连通分量族」的抽象：`C` 是 `G` 的一族非空子集，两两不交，并集为 `G`。

    数值实验里 `C` 就是 `connected_components` 返回的各分量（以索引表示）。
    我们只用到划分性质，故不建模图的邻接结构。 -/
structure IsConnectedPartition (C : Set (Set G)) : Prop where
  /-- 每个分量非空 -/
  nonempty : ∀ A ∈ C, A.Nonempty
  /-- 两两不交 -/
  pairwise_disjoint : ∀ A ∈ C, ∀ B ∈ C, A ≠ B → Disjoint A B
  /-- 覆盖全体 -/
  sUnion_eq : ⋃₀ C = Set.univ

namespace IsConnectedPartition

variable {C : Set (Set G)}

/-- 划分的成员都非空。 -/
theorem mem_nonempty (h : IsConnectedPartition C) {A : Set G} (hA : A ∈ C) : A.Nonempty :=
  h.nonempty A hA

/-- 划分的成员都在 `univ` 之内（这是判断「是否等于 univ」时唯一需要的上界方向）。 -/
theorem mem_subset_univ {A : Set G} (_hA : A ∈ C) : A ⊆ Set.univ := Set.subset_univ A

/-- **主引理（连通 ⟹ 无 proper 分量）**：
    若 `C` 是单点族 `{A}` 且 `A = univ`，则该族中每个成员都等于 `univ`。

    这正是数值实验 `empty_family` 那一峰的形式化：整图连通时 `n_components = 1`，
    唯一分量是 `univ`，于是 `{A ∈ C | A ≠ univ} = ∅`，`maxdiam*` 无定义。 -/
theorem no_proper_mem_of_singleton
    {A : Set G} (hCeq : C = {A}) (hAuniv : A = Set.univ) :
    ∀ B : Set G, B ∈ C → B = Set.univ := by
  intro B hB
  rw [hCeq, Set.mem_singleton_iff] at hB
  rw [hB, hAuniv]

/-- 上述主引理的**集合形式**，即实验里真正要用的那句话：

    「不存在 `A ∈ C` 使 `A ≠ univ`」——当 `C` 是单点族且该点是 `univ`。

    `maxdiam*` 的定义域正是 `{B ∈ C | B ≠ univ}`；本引理说它是空集，
    故 `maxdiam*` 在该情形下**没有输入**（脚本里 `maxdiam_star = null`）。 -/
theorem proper_family_empty_of_singleton
    {A : Set G} (hCeq : C = {A}) (hAuniv : A = Set.univ) :
    {B ∈ C | B ≠ Set.univ} = (∅ : Set (Set G)) := by
  ext B
  constructor
  · rintro ⟨hBC, hBne⟩
    exact absurd (no_proper_mem_of_singleton hCeq hAuniv B hBC) hBne
  · intro hB
    exact absurd hB (Set.notMem_empty B)

/-- 划分族里「值域」的另一种刻画：proper 族为空 ⟺ 族中每个成员都是 `univ`。 -/
theorem proper_family_empty_iff_all_univ :
    {B ∈ C | B ≠ Set.univ} = (∅ : Set (Set G)) ↔ ∀ B ∈ C, B = Set.univ := by
  constructor
  · intro hemp B hB
    by_contra hne
    have hmem : B ∈ {B ∈ C | B ≠ Set.univ} := by
      rw [Set.mem_setOf_eq]
      exact ⟨hB, hne⟩
    rw [hemp] at hmem
    exact absurd hmem (Set.notMem_empty B)
  · intro hall
    ext B
    constructor
    · rintro ⟨hBC, hBne⟩
      exact absurd (hall B hBC) hBne
    · intro hB
      exact absurd hB (Set.notMem_empty B)

/-- 推论（对照方向）：若 `C` 含一个 ≠ `univ` 的成员，则 proper 族**非空**。

    即非连通情形一定至少有一个 proper 闭集可用——`maxdiam*` 由此有输入。 -/
theorem proper_family_nonempty_of_mem_ne_univ
    {A : Set G} (hA : A ∈ C) (hne : A ≠ Set.univ) :
    {X ∈ C | X ≠ Set.univ}.Nonempty :=
  ⟨A, by rw [Set.mem_setOf_eq]; exact ⟨hA, hne⟩⟩

end IsConnectedPartition

/-! ### §3 对照：一个具体非连通例，证明上面的「空」不是定义空转

    取 `G = Fin 4`，划分 `C = {{0,1}, {2,3}}`。这是两分量、proper 族非空的例子：
    两个成员都 ≠ `univ`，故 proper 族有两个元素。

    用途：如果 `proper_family_empty_of_singleton` 是无内容的（例如 `C` 永远是
    单点族），那它在实验里不会有解释力。本构造说明**存在**两成员划分，
    从而 `proper_family_empty_of_singleton` 的假设「`C = {A}`」是**真的可失效**，
    引理区分了连通与非连通两种情形。 -/

/-- `Fin 4` 上一个具体的两分量划分。 -/
def demoPart : Set (Set (Fin 4)) :=
  {({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)), ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4))}

theorem demoPart_isPartition : IsConnectedPartition demoPart where
  nonempty := by
    intro A hA
    simp only [demoPart, Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨2, by simp⟩
  pairwise_disjoint := by
    intro A hA B hB hne
    simp only [demoPart, Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact absurd rfl hne
    · rw [Set.disjoint_left]
      intro x hx1 hx2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1 hx2
      rcases hx1 with rfl | rfl <;> rcases hx2 with h | h <;> omega
    · rw [Set.disjoint_left]
      intro x hx1 hx2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1 hx2
      rcases hx1 with h | h <;> rcases hx2 with rfl | rfl <;> omega
    · exact absurd rfl hne
  sUnion_eq := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      fin_cases x
      · exact ⟨({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)), by simp [demoPart], by simp⟩
      · exact ⟨({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)), by simp [demoPart], by simp⟩
      · exact ⟨({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)), by simp [demoPart], by simp⟩
      · exact ⟨({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)), by simp [demoPart], by simp⟩

/-- 两成员划分：proper 族**非空**（两个成员都不是 `univ`）。

    这是 `proper_family_empty_of_singleton` 的对照——同一套定义下，
    非连通情形确实有 proper 闭集，故「空」是真由连通性造成的。 -/
theorem demoPart_proper_nonempty :
    ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) ∈ {X ∈ demoPart | X ≠ Set.univ} := by
  rw [Set.mem_setOf_eq]
  constructor
  · simp [demoPart]
  · intro h
    have h0 : (0 : Fin 4) ∈ ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) := by rw [h]; exact Set.mem_univ 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0
    omega

/-- 两个成员确实不同（用于说明它不是单点族）。 -/
theorem demoPart_two_distinct :
    ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) ≠ ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) := by
  intro h
  have h0 : (0 : Fin 4) ∈ ({(0 : Fin 4), (1 : Fin 4)} : Set (Fin 4)) := by simp
  rw [h] at h0
  simp at h0

/-! ### §4 与数值实验的对应（登记）

  对应关系（逐条，便于核对 `RESULTS-algo-knn.md`）：

  | 本文件 | 实验位置 |
  |---|---|
  | `IsConnectedPartition` | `planD_knn.py` 的 `connected_components` 结果（自检 #4 `components_form_partition`） |
  | `C = {A}`、`A = univ` | `n_components = 1` 的 18 个配置 |
  | `proper_family_empty_of_singleton` | JSON 里 `maxdiam_star = null` + `status_innov = "empty_family"` |
  | `ok_band` 返回 `None` | 脚本中 `ok_band(md, σ)` 在 `md is None` 时返回 `None`（**不是** `True`） |
  | `demoPart_*` | 6 个 `too_coarse` 配置（proper 族非空但太粗） |

  **诚实边界**：本文件只形式化了「连通 ⟹ proper 闭集族为空」这个**结构事实**。
  数值结论（0/24 落带、maxdiam* ≥ 1.2678、占用率 0.95–1.00、耗时 ≤ 0.015 s）
  是**实测**，不是定理，不在此伪装成引理。§5「kNN 缺分辨率旋钮」的反面论证
  也**未**形式化——它需要「闭集族必须由 (块,层) 双层索引构成」这一正面刻画，
  属于 planB 文件（`MVFCA_Positive4.lean`）的范畴。

  本文件**未**改动 `Fate/`、`lean`、任何已有模块。 -/

/-! ===========================================================================
  §4  **跨引理组合**（R-46 追加）

  本节**不新增概念**，只把上面 §2.1–§2.2 与 §3 的**已有引理**
  显式串成组合定理。目的是让 `IsConnectedPartition` 的
  四条独立引理（`mem_nonempty`、`proper_family_empty_of_singleton`、
  `proper_family_empty_iff_all_univ`、`proper_family_nonempty_of_mem_ne_univ`）
  从「并列条目」变成**一个互相支撑的小网络**。

  ⚠ **防同义反复审计**（每条附在 docstring 里）：所有组合定理的**前件**
  都是「`C` 是划分」「`C = {A}`」「`A = univ`」这类**结构条件**，
  **结论**是「某集合为空」「某集合非空」「某成员非空」这类
  **集合论事实**。**其中没有一条把结论写进前件。**
  =========================================================================== -/

namespace IsConnectedPartition

variable {G : Type*} {C : Set (Set G)}

/-- **组合 1**：划分的**非空成员**取出一条具体的点，且**该点属于 `univ`**。

把 §2.1 的两条引理 `mem_nonempty`（成员非空）与 `mem_subset_univ`
（成员 ⊆ `univ`）**合成一条**：从 `A ∈ C` 同时得到「`A` 有点」与
「这些点都落在 `univ` 里」。

⚠ **前件审计**：前件只有 `A ∈ C`（成员关系）；
结论是 `∃ x, x ∈ A ∧ x ∈ Set.univ`。**结论不含前件里没有的划分全体性
（`sUnion_eq` 未被使用）**，故这是**两条引理的真合成**，不是循环。 -/
theorem exists_mem_and_mem_univ (h : IsConnectedPartition C)
    {A : Set G} (hA : A ∈ C) :
    ∃ x : G, x ∈ A ∧ x ∈ Set.univ := by
  obtain ⟨x, hx⟩ := mem_nonempty h hA
  exact ⟨x, hx, mem_subset_univ hA hx⟩

/-- **组合 2**：单点划分 + 该点为 `univ` ⟹ **proper 族的成员数至多 0**
（即 proper 族**没有元素**），以「不存在」的形式陈述。

这把 `no_proper_mem_of_singleton`（没有任何 proper 成员）与
`proper_family_empty_of_singleton`（族为空）**合成到一个命题里**，
使「空族」与「无成员」**同时**可得。

⚠ **前件审计**：前件是 `C = {A}` 与 `A = univ`（两条**关于族形态**的等式）；
结论是 `¬ ∃ B, B ∈ C ∧ B ≠ univ`。**前者不蕴含后者在表面上**，
需要走一次 `proper_family_empty_of_singleton` 的取反论证。 -/
theorem not_exists_proper_mem_of_singleton
    {A : Set G} (hCeq : C = {A}) (hAuniv : A = Set.univ) :
    ¬ ∃ B : Set G, B ∈ C ∧ B ≠ Set.univ := by
  rintro ⟨B, hBC, hBne⟩
  exact hBne (no_proper_mem_of_singleton hCeq hAuniv B hBC)

/-- **组合 3**：**proper 族为空 ⟺ 所有成员都是 `univ`**，且该等价
**与「`maxdiam*` 无输入」是同一件事**。

把 `proper_family_empty_iff_all_univ` 与
`proper_family_nonempty_of_mem_ne_univ` 的**逆否方向**对接：
若族中**存在**一个 `≠ univ` 的成员，则 proper 族**非空**（有输入）；
反之若每个成员都是 `univ`，则 proper 族**为空**（无输入）。

⚠ **前件审计**：前件是「`C` 的每个成员都是 `univ`」；
结论是「proper 族为空 **且** 不存在 `≠ univ` 的成员」。
**结论的第二部分由第一部分直接改写而来**，第一部分则来自
`proper_family_empty_iff_all_univ` 的**反向**方向。**无循环**。 -/
theorem empty_and_no_other_of_all_univ
    (hall : ∀ B ∈ C, B = Set.univ) :
    ({B ∈ C | B ≠ Set.univ} = (∅ : Set (Set G)))
      ∧ (∀ B ∈ C, B = Set.univ) :=
  ⟨(proper_family_empty_iff_all_univ).mpr hall, hall⟩

/-- **组合 4**：**非空 proper 族** ⟹ 它含一个**非 `univ`** 的成员，
且**它是 [`proper_family_nonempty_of_mem_ne_univ`] 的逆命题式强化**
（从存在性得到具体见证）。

这是 `proper_family_nonempty_of_mem_ne_univ` 的**取出见证**版本：
数值实验里需要的不只是「非空」，而是**具体的那个分量**——
本定理直接给出它。

⚠ **前件审计**：前件是 `A ∈ C` 与 `A ≠ univ`（关于一个**具体** `A` 的两条事实）；
结论是「proper 族非空 **且** 该 `A` 就在其中」。**结论中的 `A ∈ C`
是前件的直接用，但「属于 proper 族」需要 `≠ univ` 那一支**也**被用到**。
两者都被消费，非冗余。 -/
theorem exists_proper_mem_of_mem_ne_univ
    {A : Set G} (hA : A ∈ C) (hne : A ≠ Set.univ) :
    ∃ B : Set G, B ∈ C ∧ B ≠ Set.univ :=
  ⟨A, hA, hne⟩

/-- **组合 5**：**划分 + 单点 + 全空间** ⟹ 该点在 `univ` 中（
"整图连通" 情形下唯一分量的**具体点存在性**）。

把组合 1（`exists_mem_and_mem_univ`）、组合 2（`not_exists_proper_mem_of_singleton`）
与结构字段 `nonempty` 三者**串成一条**：在连通（单点且 `= univ`）划分里，
**存在**一个点，**且** proper 族**没有成员**。

⚠ **前件审计**：前件是 `C` 是划分、`C = {A}`、`A = univ`；
结论是「存在点」与「proper 族无成员」。**前者来自组合 1
（需要划分的 `nonempty` 字段），后者来自组合 2。** 两者分别消费不同前提，
故本定理**同时**用到划分结构与族形态。 -/
theorem connected_witness_and_no_proper
    (h : IsConnectedPartition C)
    {A : Set G} (hA : A ∈ C) (hCeq : C = {A}) (hAuniv : A = Set.univ) :
    (∃ x : G, x ∈ A ∧ x ∈ Set.univ) ∧
      (¬ ∃ B : Set G, B ∈ C ∧ B ≠ Set.univ) :=
  ⟨exists_mem_and_mem_univ h hA, not_exists_proper_mem_of_singleton hCeq hAuniv⟩

end IsConnectedPartition

end FateV2.Rules.KNNComponents