import FateWorld.FateV2.Rules.MVFCAClosure
import FateWorld.FateV2.Rules.InstanceChain
/-!
  # Predict · AlphaMVFCA

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaMVFCA.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MVFCAClosure, InstanceChain
  - 补充 open 域：FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  从 MVFCA 闭包到 `α` 的局部域划分（作者裁决 O2 的落实）

  ## 背景

  **作者裁决 O2**：**「局部域 = 读集」**，即「规则依赖的情境就是它所在的局部」。
  **作者裁决 O4**：**降级 = 未证项记录**（中间状态，不是终点）。

  ## 本节做什么（作者裁决「建构的建构」）

  把 `MVFCA4.PatStruct` 的闭包结构接到 `InstanceChain` 的 `AlphaOutput` 上，
  给出**第一个有内容的局部域划分**：

  $$\text{minClosed}(g) := \mathrm{cl}\,\{g\}$$

  **每个对象的最小闭集** —— 它天然诱导一个划分（同类 ⟺ 最小闭集相同）。

  ## ⭐ 为什么这样定义划分

  **`cl {g}` 是「包含 `g` 的最小闭集」** —— 它正是「`g` 所依赖的局部情境」。

  **⟹ 与作者「局部 = 规则依赖的情境」直接对应**：
  * `g` 的局部域 = `cl {g}`
  * 若 `cl {g} = cl {h}`，则 `g` 与 `h` **依赖同一个情境** ⟹ 同类

  ## 本节的可证内容

  1. ⭐ `minClosed` 是闭集（由 `cl_idem`）
  2. ⭐ `minClosed` 诱导的等价关系是**等价关系**（自反/对称/传递）
  3. ⭐ 由此得到 `PartitionCovers` / `PartitionSymm` / `PartitionTrans`
  4. ⚠ **不声称** 已满足完整的 `AlphaSpec`（还需 `RulesLocal` / `RulesInhabited`）

  ## 诚实边界

  * **`RulesLocal` / `RulesInhabited` 不在本文件内证** —— 本文件只提供划分。
    **✅ 二者已由下游 `Fate/AlphaRulesLocal` 证毕**（`theorem rulesLocal`、
    `theorem rulesInhabited`、`theorem alphaStructure`，第 618 轮）：该文件
    `import AlphaMVFCA`，在 `G := X.Carrier` 口径下用
    `localRuleAsLaw` 把 `LawRule` 接到 `PatStruct` 上。
    （注：§0.4 的 `:- True` 占位 `RulesLocalGap` 已在本轮 A-4/A-5 真正删除，
    此前说明段曾错误地声称已删、而定义仍存，见该处说明段。）
    ⚠ **已知签名瑕疵（A-4/A-5 核实）**：`localRuleAsLaw` 的 `c₀ : C.Carrier`
    被 `rulesLocal` / `rulesInhabited` / `alphaStructure` 以**自动隐式**形式带出
    （`#print` 可见 `{c₀ : C.Carrier}` 前缀），即 `c₀` 悬空且始终未被使用。
    不影响命题真值（`c₀` 与规则行为无关），但属签名冗余；因纪律 (i)
    本轮不改 `AlphaRulesLocal`，仅在此记录。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Rules
namespace AlphaMVFCA

open FateV2.Rules.MVFCA4

universe u v

variable {G : Type u} {L : Type v} [CompleteLattice L]

/-! ### §0.1 ⭐ 最小闭集 -/

/-- ⭐ **每个对象的最小闭集** `cl {g}` —— 「`g` 所依赖的局部情境」。

**这是作者裁决 O2「局部 = 规则依赖的情境」的直接形式化。** -/
def minClosed (K : PatStruct G L) (g : G) : Set G := K.cl {g}

/-- ⭐ **最小闭集确实是闭集**（由 `cl_idem`）。 -/
theorem minClosed_isClosed (K : PatStruct G L) (g : G) : K.IsClosed (minClosed K g) := by
  unfold minClosed PatStruct.IsClosed
  rw [PatStruct.cl_idem]

/-- ⭐ **`g` 属于自己的最小闭集**（扩张性）。 -/
theorem mem_minClosed_self (K : PatStruct G L) (g : G) : g ∈ minClosed K g := by
  unfold minClosed
  exact K.cl_extensive ({g} : Set G) (Set.mem_singleton g)

/-! ### §0.2 ⭐⭐ 划分 -/

/-- ⭐⭐ **由最小闭集诱导的划分**：`p x` = 与 `x` 有相同最小闭集的所有对象。 -/
def closedPartition (K : PatStruct G L) (x : G) : Set G :=
  {y | minClosed K y = minClosed K x}

/-- ⭐ **划分覆盖性**：每个点落在自己的类里。 -/
theorem closedPartition_covers (K : PatStruct G L) :
    InstanceChain.PartitionCovers (closedPartition K) := by
  intro x
  show x ∈ closedPartition K x
  unfold closedPartition
  simp only [Set.mem_setOf_eq]

/-- ⭐ **划分对称性**：`y` 与 `x` 同类 ⟹ `x` 与 `y` 同类。 -/
theorem closedPartition_symm (K : PatStruct G L) :
    InstanceChain.PartitionSymm (closedPartition K) := by
  intro x y hxy
  unfold closedPartition at *
  simp only [Set.mem_setOf_eq] at *
  rw [hxy]

/-- ⭐ **划分传递性**：同类关系传递。 -/
theorem closedPartition_trans (K : PatStruct G L) :
    InstanceChain.PartitionTrans (closedPartition K) := by
  intro x y z hxy hyz
  unfold closedPartition at *
  simp only [Set.mem_setOf_eq] at *
  rw [hyz, hxy]

/-! ### §0.3 ⭐ 结论：MVFCA 闭包给出合法划分 -/

/-- ⭐⭐ **MVFCA 闭包给出一个合法的局部域划分**（三性质齐全）。

**⟹ 这是 `AlphaOutput.partition` 的第一个有内容的候选。**

**⚠ 但这只是 `α` 的**一半**：规则那一半（`RulesLocal`）不在本文件证
（**✅ 已由下游 `Fate/AlphaRulesLocal.rulesLocal` 证毕**）。** -/
theorem closedPartition_spec (K : PatStruct G L) :
    InstanceChain.PartitionCovers (closedPartition K) ∧
    InstanceChain.PartitionSymm (closedPartition K) ∧
    InstanceChain.PartitionTrans (closedPartition K) :=
  ⟨closedPartition_covers K, closedPartition_symm K, closedPartition_trans K⟩

/-! ### §0.4 ⚠ 缺口登记（不掩盖）

**`AlphaSpec` 另需两个成分，本文件内未做（但已在**下游**证毕）**：

| 成分 | 本文件 | 下游状态 |
|---|---|---|
| `RulesLocal p rs` | 不证 | ✅ **已证** —— `Fate/AlphaRulesLocal.rulesLocal` |
| `RulesInhabited` | 不证 | ✅ **已证**（需 `target` 处处非空）—— `Fate/AlphaRulesLocal.rulesInhabited` |

**⟹ 本节的贡献是**：证明「局部域划分」这一半是通的，且用的是 MVFCA 的闭集结构。
-/

/-! **【A-4/A-5：`RulesLocalGap` 已真正删除（此前说明段谎称已删，定义仍在）】**

原内容（曾实际存在于本文件 §0.4 处，**现仅为注释中的转录**）：
```
    def RulesLocalGap (_K : PatStruct G L) : Prop := True
```
**问题**：它是**恒真**的 `Prop` 占位（`:= True`），下游可当「已证前提」使用（假定理源）。

**历史**：第 618 轮已在本处写下「已删除」的说明段，但**实际未删定义**——
说明与代码不一致。本轮（A-4/A-5）**真正删除该 `def`**。

**为什么删而不修**：
* `grep -rn "RulesLocalGap" Fate/*.lean` ⟹ **不再有任何 `def` 声明命中**
  （仅本说明段提及该名字），**无任何下游引用**，删掉不影响编译链。
* 真实的 `RulesLocal` / `RulesInhabited` **已由下游 `Fate/AlphaRulesLocal`
  证毕**（`rulesLocal` / `rulesInhabited` / `alphaStructure`），
  无需任何「缺口」占位。
* `AlphaRulesLocal` 是**下游**（`import AlphaMVFCA`），
  故本文件**不能**也**不需要**指向它——直接删除。

若需要这两条定理，请 `import FateV2.Rules`。 -/

end AlphaMVFCA

end FateV2.Predict