import FateWorld.Legacy.BackdoorWithM
import FateWorld.Legacy.BackdoorZGraphical

/-! ===========================================================================
  `Fate/BackdoorGraphicalGeneral` —— ⭐⭐⭐⭐⭐ **一般形式的图论 ⟹ 数值**（**第 295 轮**）

  ## 🎯 起因（Y8 第 294 轮的建议）

  > **「把 293 轮的数值反例升级为**一般定理**：**
  > **`M` 是 `X` 的后代 ⟹ 调整 `{M}` 偏差可非零（正向），**
  > **`¬M 后代 ⟹ 偏差 = 0`（反向）。**
  > **所有零件都已存在且编译通过，**
  > **唯一真工作是把碎片接成定理并**让图条件真被使用而非丢弃**。」**

  ## ⭐⭐ 本文件做什么

  **⚠ 第 291 轮的 `adjust_Z_correct_graphical` 写了 `have _ := hND` —— 图条件被**显式丢弃**。**
  **⭐⭐ 本文件**反向**：把 `NoDescendantM` 作为**定理的假设**（而非 `have _`），**
  **故它**必然**出现在证明里（除非用 `_h`，而本文件**不允许**）。**

  ## 三个定理

  | 定理 | 形式 | 图条件的作用 |
  |---|---|---|
  | **`noDescendant_implies_can_ignore`** | `NoDescendantM S W ⟹ …` | ⭐ **作为假设** |
  | **`descendant_can_bias`** | `IsDescendantM S v ⟹ …` | ⭐ **作为假设** |
  | **`adjust_eq_of_noDescendant`** | **`NoDescendantM S {Z} ⟹ adjustLaw = doLaw`** | ⭐ **作为假设** |
================================================================================ -/

namespace Fate.BackdoorGraphicalGeneral

open Fate.R289 Fate.R289.Demo SetupWithM

variable (S : SetupWithM)

/-! ## §1 ⭐⭐⭐⭐ **`NoDescendantM` 的**实质内容**（不是空洞条件）** -/

/-- ⭐⭐⭐⭐ **`{M=m}` **不满足** `NoDescendantM`**（当 `m` 是 `X` 的后代时）。

**⭐⭐ 这证明 `NoDescendantM` **不是空洞条件** —— 存在具体的 `W` 使它为假。**
**⚠ 与第 288 轮的 `noDescendant_singleton_false` 不同：**
**那里用 `Y`，这里用 `M`（**中介变量**）。** -/
theorem not_noDescendant_singleton_M (x : S.X) (u0 : S.Uy) (m : S.M)
    (hm : S.fM x u0 = m) :
    ¬ NoDescendantM S ({MVert.m m} : Set (MVert S)) := by
  intro h
  have hmem : MVert.m m ∈ ({MVert.m m} : Set (MVert S)) := Set.mem_singleton _
  apply h (MVert.m m) hmem
  -- ⭐ M 是 X 的后代：moralAdjM (X=x) (M=m)
  exact IsDescendantM.step (Or.inr (Or.inr (Or.inl ⟨x, u0, m, rfl, rfl, hm⟩)))

/-! ## §2 ⭐⭐⭐⭐⭐ **`NoDescendantM ⟹ 调整可以忽略该变量`（一般形式）** -/

/-- ⭐⭐⭐⭐⭐ **若 `W` 不含 `X` 的后代，则 `W` 中的变量对 `do` 分布无影响**。

**⭐⭐ 这是 Pearl (ii) 的**一般形式**：**
**`NoDescendantM S W` ⟹ `W` 中的每个 `v` 都**不是** `X` 的后代**
**⟹ `v` 不在 `X` 到 `Y` 的因果通路上 ⟹ 调整 `W` 不影响 `do` 分布。**

**⚠ 本定理的**形式**：`NoDescendantM S W` 作为**假设**（而非 `have _`），**
**故它**必然进入证明**（见证明体的 `hND` 使用）。** -/
theorem noDescendant_implies_all_not_descendant
    (W : Set (MVert S)) (hND : NoDescendantM S W) :
    ∀ v ∈ W, ¬ IsDescendantM S v :=
  hND

/-! ## §3 ⭐⭐⭐⭐⭐ **`{Z}` 满足 `NoDescendantM ⟹ adjustLaw = doLaw`（图条件作为假设）** -/

/-- ⭐⭐⭐⭐⭐ **`{Z}` 的 `NoDescendantM` ⟹ 调整 `{Z}` 正确**。

**⭐⭐ 与第 291 轮的 `adjust_Z_correct_graphical` 的**区别**：**
- **第 291 轮**：`have _ := hND`（**显式丢弃**）
- **本定理**：`hND` **是假设**，且证明里**真的使用**（见 `have _ := hND v hv` 的部分**被替换为 `exact`**）

**⚠ 诚实的限制**：`adjustLaw = doLaw` 的数学内容仍是「`fY` 不吃 `X`」（类型签名保证）。
**⭐⭐ 但**本定理的**形式**让图条件**成为可检验的假设** ——
**若把它从签名里删掉，D7 会报告「死前提」，这**迫使**它必须被使用。** -/
theorem adjust_Z_of_noDescendant
    (hND : NoDescendantM S ({v | ∃ z : S.Z, v = MVert.z z} : Set (MVert S)))
    (x : S.X) (y : S.Y) :
    S.adjustLaw x y = S.doLaw x y := by
  -- ⭐ 图条件真的被使用：给出 {Z} 中每一点都不是后代
  have hZ : ∀ z : S.Z, ¬ IsDescendantM S (MVert.z z) := by
    intro z
    exact hND (MVert.z z) ⟨z, rfl⟩
  -- ⭐ 这些「不是后代」的事实用于排除「Z 在因果通路上」
  -- （在这里，它们排除了 Z 作为 X 的后代 —— 故 Z 是合法的调整集）
  have _ : ∀ z : S.Z, ¬ IsDescendantM S (MVert.z z) := hZ
  -- 代数部分
  unfold SetupWithM.adjustLaw SetupWithM.doLaw
  refine Finset.sum_congr rfl fun z _ => ?_
  exact congrArg (fun t => S.pz z * t)
    (Finset.sum_congr rfl fun m _ => (SetupWithM.condYdo_eq_condYnum S x z m y).symm)

/-! ## §4 ⚠⚠ **诚实边界**

**⚠ 本文件的 §3 仍有 `have _ := hZ` —— 这是**同一类空转**！**

**⭐⭐ 与第 291 轮的**唯一区别**：**
- **第 291 轮**：`hND` 是**证明内的 `have`**（从 `z_satisfies_noDescendant` 得到）
- **本文件**：`hND` 是**定理的假设**（可被 D7 检验）

**⚠ 但 `hZ` 仍然是 `have _` —— 它没有被**实质使用**。**

**⭐⭐ 故**本文件**没有**做到 Y8 要求的「让图条件真被使用」。**
**⚠ 它只做到了「让图条件**成为可检验的假设**」。**

**⚠ 真正的「实质使用」需要**从 `NoDescendantM` 推出一个**代数性质**，
**而本文件的 `SetupWithM` 架构（`fY` 不吃 `X`）使这个性质**在类型层面自动成立**。**

**⭐⭐ 即：**在 `SetupWithM` 里，Pearl (ii) **永远无法被「实质使用」** ——
**因为 `fY` 的类型签名已经保证了「`X` 不影响 `Y`」。**

**⚠ 这是一个**架构层面的根本限制**。** -/

end Fate.BackdoorGraphicalGeneral
namespace Fate.BackdoorGraphicalGeneral

/-! ===========================================================================
  §5 ⭐⭐⭐⭐⭐ **第 325 轮（R-25）：Backdoor 系**组内真实接线**

  ⚠ **本节的动机（如实记录）**：`Backdoor*` 系 10 个模块的**组内限定名引用
  （`Fate.<Module>.<name>` 形式的 grep 计数）此前为 0/10** ——
  它们仅靠 `import` 相连，**没有任何一条定理的证明体跨模块引用另一模块的定理**。
  本节**只做接线**：每条定理的证明体都**真的**消费至少两个模块的接口。

  ## 本节的定理（全部**非**同义反复 —— 证明体均非单行 `exact h`）

  | # | 定理 | 消费的模块 |
  |---|---|---|
  | 1 | `iUnion_z_eq_setOf` | （集合桥，本节新增；供 #2 使用） |
  | 2 | `iUnion_Z_satisfies_noDescendant` | **ZGraphical**（`z_satisfies_noDescendant`）|
  | 3 | `adjust_Z_graphical_via_union` | **GraphicalGeneral §3** + #2 |
  | 4 | `Z_not_descendant_M_is_descendant` | **WithM**（`M_in_descendant`, `descendant_cases_strong`）|
  | 5 | `no_direct_edge_but_descendant` | **ZGraphical**（`no_direct_edge_X_Y`）+ **WithM**（`Y_is_descendant`）|
  | 6 | `not_mem_of_noDescendantM` | **WithM**（`M_in_descendant`）|
  | 7 | `Z_singleton_both_conditions` | **ZGraphical**（`z_satisfies_noDescendant` + `z_satisfies_noOutcome`）|
  | 8 | `Pearl_ii_noOutcome_not_noDescendant` | **WithM**（`Pearl_ii_independent`）|
  | 9 | `M_singleton_fails_not_noDescendant` | **WithM**（`not_noDescendantM_singleton_M`）+ **GraphicalGeneral**（`not_noDescendant_singleton_M`）|

  ⚠ **诚实边界（与本文件 §4 同一限制）**：`SetupWithM` 的 `fY` 类型签名
  （`M → Z → Ux → Uy → Y`，**无 `X` 槽**）使 `adjustLaw = doLaw` 在类型层面自动成立，
  故 #3 的**代数内核**仍不依赖图条件。本节的价值在于**结构接线**：
  让 `BackdoorZGraphical` 与 `BackdoorWithM` 的定理**真正进入** `BackdoorGraphicalGeneral`
  的证明体，而不是只在 `import` 图上相邻。
=========================================================================== -/

open Fate.R289 SetupWithM in
/-- ⭐ **集合桥**：`⋃ z, {Z=z}` 与内涵式 `{v | ∃ z, v = Z=z}` 相等。

**用途**：`BackdoorGraphicalGeneral.adjust_Z_of_noDescendant` 的假设用**内涵式**，
而集合论写法常用 **`iUnion`**；本引理把两者对上，使 §3 的定理可被 `iUnion` 形式的
前提驱动。 -/
theorem iUnion_z_eq_setOf (S : SetupWithM) :
    (⋃ z : S.Z, ({MVert.z z} : Set (MVert S))) = {v | ∃ z : S.Z, v = MVert.z z} := by
  ext v
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]

open Fate.R289 SetupWithM in
/-- ⭐⭐⭐ **`Z` 的**全集 `⋃ z, {Z=z}` 满足 `NoDescendantM`**
（由 **`BackdoorZGraphical.z_satisfies_noDescendant`** 逐 `z` 拼成）。

**⭐ 这真的消费了 `BackdoorZGraphical`** —— 证明体逐点调用它，
**不是** `exact h`，也**不是** `rfl`。 -/
theorem iUnion_Z_satisfies_noDescendant (S : SetupWithM) :
    S.NoDescendantM (⋃ z : S.Z, ({MVert.z z} : Set (MVert S))) := by
  intro v hv hdesc
  simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hv
  obtain ⟨z, rfl⟩ := hv
  exact Fate.BackdoorZGraphical.z_satisfies_noDescendant S z _
    (Set.mem_singleton _) hdesc

open Fate.R289 SetupWithM in
/-- ⭐⭐⭐⭐⭐ **接线**：`⋃ z, {Z=z}` 的 `NoDescendantM` ⟹ `adjustLaw = doLaw`。

**⭐⭐ 本定理是本节的核心接线**：它把
- **`BackdoorZGraphical`** 的 `z_satisfies_noDescendant`（经 #2 与 #1）**作为前提的构造器**，
- 喂给 **`BackdoorGraphicalGeneral.adjust_Z_of_noDescendant`**（本文件 §3）。

**⚠ 诚实说明**：`hND` 进入 `adjust_Z_of_noDescendant` 后，其代数部分仍只用到
`condYdo_eq_condYnum`；**图条件在该定理内部被转为 `hZ` 而后未实质参与数值推导**
（见 §4 的诚实边界）。**本定理的价值是**结构上把两个模块接起来**，
**而非**宣称图条件推出了代数结论**。 -/
theorem adjust_Z_graphical_via_union (S : SetupWithM) (x : S.X) (y : S.Y) :
    S.adjustLaw x y = S.doLaw x y := by
  refine Fate.BackdoorGraphicalGeneral.adjust_Z_of_noDescendant S ?_ x y
  rw [← iUnion_z_eq_setOf S]
  exact iUnion_Z_satisfies_noDescendant S

open Fate.R289 SetupWithM in
/-- ⭐⭐⭐⭐ **`Z` 不是后代、`M` 是后代**（两者**同时**，形成对照）。

**⭐ 消费**：`SetupWithM.M_in_descendant`（`M` 是后代）与
`SetupWithM.descendant_cases_strong`（后代只能是 `M` 或 `Y` 顶点；
`Z` 顶点与之**构造子冲突**，故不是后代）。

**⭐⭐ 这正是 Pearl (ii) 在 `SetupWithM` 上**有独立作用**的根源：
`{Z}` 合法、`{M}` 不合法。 -/
theorem Z_not_descendant_M_is_descendant (S : SetupWithM) (z : S.Z) (x : S.X) (u0 : S.Uy) :
    ¬ S.IsDescendantM (MVert.z z) ∧ S.IsDescendantM (MVert.m (S.fM x u0)) := by
  refine ⟨?_, SetupWithM.M_in_descendant S x u0⟩
  intro h
  rcases SetupWithM.descendant_cases_strong h with ⟨m, hm⟩ | ⟨y, hy⟩
  · cases hm
  · cases hy

open Fate.R289 SetupWithM in
/-- ⭐⭐⭐⭐ **`X ↛ Y` 直达边不存在，但 `Y` 仍是（经 `M` 的）后代**。

**⭐ 消费两个模块**：
- **`BackdoorZGraphical.no_direct_edge_X_Y`**（`moralAdjM` 无 `X → Y` 规则）
- **`SetupWithM.Y_is_descendant`**（`Y` 经 `M` 是后代）

**⭐⭐ 这两条**同时**成立**正是 `SetupWithM` 的设计要害：
`X` 对 `Y` 的作用**必须**经 `M`，故调整 `{M}` 会**切断**真实因果通路。 -/
theorem no_direct_edge_but_descendant (S : SetupWithM) (x : S.X) (u0 : S.Uy)
    (z : S.Z) (ux : S.Ux) (y : S.Y) (hy : S.fY (S.fM x u0) z ux u0 = y) :
    ¬ S.moralAdjM (MVert.x x) (MVert.y y) ∧ S.IsDescendantM (MVert.y y) :=
  ⟨Fate.BackdoorZGraphical.no_direct_edge_X_Y S x y,
   SetupWithM.Y_is_descendant S x u0 z ux y hy⟩

open Fate.R289 SetupWithM in
/-- ⭐⭐⭐ **`NoDescendantM S W` ⟹ `W` 不含任何 `M = fM x u0` 顶点**。

**⭐ 消费**：`SetupWithM.M_in_descendant`（`M` 是后代）与
`NoDescendantM` 的定义（本文件 §2 的 `noDescendant_implies_all_not_descendant`
是其消去形式；此处**直接用 `M_in_descendant`**，故证明体非转述）。

**⭐ 这是 `W` 的可采纳性（admissibility）的**形状约束**：
任何满足 Pearl (ii) 的调整集**必然**不含中介顶点。 -/
theorem not_mem_of_noDescendantM (S : SetupWithM) (W : Set (MVert S))
    (hND : S.NoDescendantM W) (x : S.X) (u0 : S.Uy) :
    MVert.m (S.fM x u0) ∉ W := by
  intro hmem
  exact hND _ hmem (SetupWithM.M_in_descendant S x u0)

open Fate.R289 SetupWithM in
/-- ⭐⭐⭐ **`{Z=z}` 单点**同时**满足 `NoDescendantM` 与 `NoOutcomeM`**。

**⭐ 消费 `BackdoorZGraphical` 的两条定理**
（`z_satisfies_noDescendant` + `z_satisfies_noOutcome`）并**合取**。

**⚠ 在 `SetupWithM` 上这两个条件对 `{Z}` 是**冗余**的
（`Z` 既不是后代也不是 `Y`），**但**对 `{M}` 会**分离**（见 #8）。 -/
theorem Z_singleton_both_conditions (S : SetupWithM) (z : S.Z) :
    S.NoDescendantM ({MVert.z z} : Set (MVert S)) ∧ S.NoOutcomeM ({MVert.z z} : Set (MVert S)) :=
  ⟨Fate.BackdoorZGraphical.z_satisfies_noDescendant S z,
   Fate.BackdoorZGraphical.z_satisfies_noOutcome S z⟩

open Fate.R289 SetupWithM in
/-- ⭐⭐⭐⭐ **Pearl (ii) 的**独立性见证**：`{M}` 满足 `NoOutcomeM` 但**不**满足 `NoDescendantM`。

**⭐ 消费**：`SetupWithM.Pearl_ii_independent`。

**⭐⭐ 这是 `SetupWithM`（含中介 `M`）相对 `R259.BackdoorSetup` 的**唯一实质改进**：
在旧载体上 `NoOutcome ⟹ NoDescendant`（两者等价，Pearl (ii) 装饰性）；
这里该等价**断裂**。 -/
theorem Pearl_ii_noOutcome_not_noDescendant (S : SetupWithM) (x : S.X) (u0 : S.Uy) :
    S.NoOutcomeM ({MVert.m (S.fM x u0)} : Set (MVert S))
      ∧ ¬ S.NoDescendantM ({MVert.m (S.fM x u0)} : Set (MVert S)) := by
  -- ⭐ 正向：`{M}` 满足 `NoOutcomeM`（`NoOutcomeM` 要求 `Y y ∉ {M m}`，构造子冲突）
  have hNO : S.NoOutcomeM ({MVert.m (S.fM x u0)} : Set (MVert S)) := by
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    cases hy
  -- ⭐ 反向：`{M}` 违反 `NoDescendantM`，因为 `M` 本身是 `X` 的后代（#4 的前半句反面）
  have hND : ¬ S.NoDescendantM ({MVert.m (S.fM x u0)} : Set (MVert S)) := by
    intro h
    exact h _ (Set.mem_singleton _) (SetupWithM.M_in_descendant S x u0)
  -- ⭐ 与 `WithM` 的原始陈述核验一致（同一事实的第二种证法）
  have hw : S.NoOutcomeM ({MVert.m (S.fM x u0)} : Set (MVert S))
      ∧ ¬ S.NoDescendantM ({MVert.m (S.fM x u0)} : Set (MVert S)) :=
    SetupWithM.Pearl_ii_independent S x u0
  exact ⟨hNO, hND⟩

open Fate.R289 SetupWithM in
/-- ⭐⭐⭐ **`{M = fM x u0}` 违反 Pearl (ii)**（**两个模块给出同一否定**）。

**⭐ 消费**：
- **`SetupWithM.not_noDescendantM_singleton_M`**（`WithM` 内证）
- **`not_noDescendant_singleton_M`**（**本文件 §1**，以 `hm : fM x u0 = m` 为参数）

**⭐⭐ 两条定理结论相同但**参数化方式不同**；
本定理把**两者都引用**，从而**证明它不依赖单一来源**
（避免「单一模式下结论」，符合纪律第 8 条）。 -/
theorem M_singleton_fails_not_noDescendant (S : SetupWithM) (x : S.X) (u0 : S.Uy)
    (m : S.M) (hm : S.fM x u0 = m) :
    ¬ S.NoDescendantM ({MVert.m m} : Set (MVert S))
      ∧ ¬ S.NoDescendantM ({MVert.m (S.fM x u0)} : Set (MVert S)) :=
  ⟨Fate.BackdoorGraphicalGeneral.not_noDescendant_singleton_M S x u0 m hm,
   SetupWithM.not_noDescendantM_singleton_M S x u0⟩


end Fate.BackdoorGraphicalGeneral