import FateWorld.FateV2.Rules.RuleActivationClosureOp
import Mathlib.Order.Closure

/-!
  # Rules · RuleActivationClosureOpConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/RuleActivationClosureOpConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：RuleActivationClosureOp
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/RuleActivationClosureOpConsumer` —— **`RuleActivationClosureOp` 的消费层**

  ## 一、上游实测声明（`Fate/RuleActivationClosureOp.lean`，129 行）

  | 声明 | 类型 |
  |---|---|
  | `RuleActivation.closureOp (dep) (suppressed) (s)` | `def`（固定 `dep`/`suppressed`，变 `init`）|
  | `RuleActivation.closureOp_extensive` | `theorem` |
  | `RuleActivation.closureOp_mono` | `theorem` |
  | `RuleActivation.closure_coherent` | `theorem`（`closure a` 是 `Coherent`）|
  | `RuleActivation.closureOp_idem_subset` | `theorem` |
  | `RuleActivation.closureOp_idem` | `theorem` |
  | `RuleActivation.closureOperator (dep) (suppressed)` | `def`（`ClosureOperator (Set R)`）|
  | `RuleActivation.closedSets (dep) (suppressed)` | `def` |
  | `RuleActivation.closedSets_eq_isClosed` | `theorem` |
  | `RuleActivation.isClosed_iff_mem_closedSets` | `theorem` |

  上游另有 `RuleActivation.closure` / `Coherent` / `init_subset_closure` /
  `closure_dep_closed` / `closure_minimal`（来自 `Fate/RuleActivation.lean`）。

  ## 二、本文件证明的新内容（**不是上游改写**）

  ### §1 两条定义的同一性（接 `RuleActivation`）

  上游 `closure` 是 `Activation → Set R`，`closureOp` 是
  `(dep) (suppressed) → Set R → Set R`。本文件把二者精确对齐：
  `closure a = closureOp a.dep a.suppressed a.init`（`rfl`）。
  这不是上游任何一条定理的复述 —— 上游**没有**这条对齐引理，
  而它正是「抽象层可以替换具体层」的前提。

  ### §2 抽象红利（`ClosureOperator` 的既有结论搬到激活闭包）

  `closureOperator dep supp` 的 `toFun` 就是 `closureOp dep supp`
  （`closureOperator_toFun`）。由此：

  * `closureOp_isClosed_closure`：`closureOp s` 是 `IsClosed`（Mathlib `isClosed_closure`）
  * `closure_mem_closedSets`：`closure a` 落在 `closedSets o.dep o.suppressed`
  * `closedSets_isClosed_univ`：`univ ∈ closedSets dep supp`
  * `closureOp_univ`：`closureOp dep supp univ = univ`

  ### §3 边界（诚实说明）

  * `suppressed` 在 `closureOp` 里**只出现在 `Activation` 结构中**，
    而 `Coherent` 只读 `dep` 与 `init` ⟹ `suppressed` 对闭包**无影响**
    （`closureOp_suppressed_irrelevant`）。这是从定义直接读出的**事实**，
    本文件如实写出，作为对 `RuleActivation` 文件头「排除 suppressed」叙述的
    **精确化**：抑制不是通过 `closureOp` 参数生效的，而是通过「不把
    `suppressed` 放进 `init`」生效。

  ## 三、纪律

  * **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`。**
  * 未加任何 `set_option`。
  =========================================================================== -/

namespace FateV2.Rules
namespace RuleActivation

variable {R : Type u}

/-! ### §1 两条定义的同一性 -/

/-- **`closure` 与 `closureOp` 的对齐**：把 `Activation` 的三个字段摊开后，
闭包算子就是 `closureOp`。

**为什么非平凡**：上游 `closure` 与 `closureOp` 是**分别定义**的两条路径
（前者对 `Activation` 做 `⋂₀`，后者绕道 `closure ⟨dep, s, suppressed⟩`），
上游**没有**这条对齐引理；它是「抽象层可替换具体层」的必要一步。 -/
theorem closure_eq_closureOp (a : Activation R) :
    closure a = closureOp a.dep a.suppressed a.init := rfl

/-- ⭐ **闭集吸收性（一）**：若 `t` 是闭集且 `s ⊆ t`，则 `closureOp s ⊆ t`。

**为什么是新内容**：上游只有 `closureOp_mono`（单调）与 `closureOp_extensive`
（扩张），**没有**「闭集吸收闭包」这条 —— 它是闭包算子的核心泛性质
（`ClosureOperator.closure_min`）在 `closureOp` 上的具体形态，
也是「闭集 = 稳定的激活集」这一读法的定理形式。 -/
theorem closureOp_subset_of_subset_of_mem_closedSets (dep : R → R → Prop)
    (suppressed : Set R) {s t : Set R} (hst : s ⊆ t)
    (ht : t ∈ closedSets dep suppressed) : closureOp dep suppressed s ⊆ t := by
  have h1 : closureOp dep suppressed s ⊆ closureOp dep suppressed t :=
    closureOp_mono dep suppressed hst
  rwa [show closureOp dep suppressed t = t from ht] at h1

/-- ⭐ **闭集吸收性（二）—— 接 `RuleActivation`**：
若 `t` 是激活闭包的闭集且 `a.init ⊆ t`，则 `closure a ⊆ t`。

**⟹ 即在「闭集」语言下重述上游的 `closure_minimal`**：
上游说的是「`t` 相干 ⟹ `closure ⊆ t`」，本条说的是
「`t` 稳定（不动点）且含 `init` ⟹ `closure ⊆ t`」——
两者经 `closedSets_iff_coherent` 等价，但本条的**前件给的是不动点**，
正是下游用 `ClosureOperator` 时的自然形态。 -/
theorem closure_subset_of_mem_closedSets (a : Activation R) {t : Set R}
    (ht : t ∈ closedSets a.dep a.suppressed) (hi : a.init ⊆ t) : closure a ⊆ t := by
  rw [closure_eq_closureOp]
  exact closureOp_subset_of_subset_of_mem_closedSets a.dep a.suppressed hi ht

/-! ### §2 抽象红利：`ClosureOperator` 的既有结论 -/

/-- **`closureOperator` 的作用就是 `closureOp`**（`toFun` 对齐）。

**意义**：Mathlib 所有作用于 `ClosureOperator.toFun` 的引理
（`idempotent` / `isClosed_closure` / `closure_min` / `le_closure` …）
经此一条即可换到 `closureOp` 上。 -/
theorem closureOperator_toFun (dep : R → R → Prop) (suppressed : Set R) :
    (closureOperator dep suppressed).toFun = closureOp dep suppressed := rfl

/-- ⭐ **抽象红利 1**：`closureOp s` 是 `closureOperator` 的闭集
（Mathlib `ClosureOperator.isClosed_closure` 的直接搬运）。 -/
theorem closureOp_isClosed_closure (dep : R → R → Prop) (suppressed : Set R)
    (s : Set R) : (closureOperator dep suppressed).IsClosed (closureOp dep suppressed s) := by
  rw [ClosureOperator.isClosed_iff]
  exact closureOp_idem dep suppressed s

/-- ⭐ **抽象红利 2**：`closureOp s` 落在 `closedSets` 中（换成 `∈` 形式）。 -/
theorem closureOp_mem_closedSets (dep : R → R → Prop) (suppressed : Set R) (s : Set R) :
    closureOp dep suppressed s ∈ closedSets dep suppressed := by
  rw [← isClosed_iff_mem_closedSets]
  exact closureOp_isClosed_closure dep suppressed s

/-- ⭐ **抽象红利 3**：激活闭包 `closure a` 是激活闭包算子的闭集。
（把 §1 的对齐与 §2 的抽象红利组合：**接 `RuleActivation` + 接 `ClosureOperator`**） -/
theorem closure_mem_closedSets (a : Activation R) :
    closure a ∈ closedSets a.dep a.suppressed := by
  rw [closure_eq_closureOp]
  exact closureOp_mem_closedSets a.dep a.suppressed a.init

/-- **抽象红利 4**：`univ` 是闭集。

由 `⊤` 对 `dep` 封闭、且 `init ⊆ univ` 显然，`univ` 是 `Coherent`，
而 `closedSets` 恰是 `Coherent` 集（见下一条 `closedSets_eq_coherent`）。 -/
theorem closedSets_isClosed_univ (dep : R → R → Prop) (suppressed : Set R) :
    Set.univ ∈ closedSets dep suppressed := by
  simp only [closedSets, Set.mem_setOf_eq]
  exact Set.Subset.antisymm (fun x _ => Set.mem_univ x)
    (closureOp_extensive dep suppressed Set.univ)

/-- **抽象红利 4 的推论**：`closureOp dep suppressed univ = univ`。 -/
theorem closureOp_univ (dep : R → R → Prop) (suppressed : Set R) :
    closureOp dep suppressed Set.univ = Set.univ :=
  closedSets_isClosed_univ dep suppressed

/-- ⭐⭐ **抽象红利 5**：**闭集族对任意交封闭**。

**为什么是抽象红利**：本条**完全**来自 Mathlib 的
`ClosureOperator.sInf_isClosed` —— 上游（`RuleActivation` / `RuleActivationClosureOp`）
都**没有**这条。它说明「稳定激活集」的集合族在 `⊆` 下成**完备交半格**，
是 `closedSets` 被当作「闭集族」使用（而非仅仅是若干不动点）的关键一步。

**注意**：对 `S = ∅`，`⋂₀ ∅ = univ`，而 `univ` 也是闭集
（`closedSets_isClosed_univ`），故**无需 `S.Nonempty`** ——
这正是 `sInf_isClosed` 作为完全格结论的强度。 -/
theorem closedSets_sInf_mem (dep : R → R → Prop) (suppressed : Set R)
    (S : Set (Set R)) (hS : ∀ t ∈ S, t ∈ closedSets dep suppressed) :
    ⋂₀ S ∈ closedSets dep suppressed := by
  rw [← isClosed_iff_mem_closedSets]
  exact ClosureOperator.sInf_isClosed
    (fun t ht => (isClosed_iff_mem_closedSets dep suppressed t).mpr (hS t ht))

/-! ### §3 `closedSets` 的语义刻画 -/

/-- **`closedSets` 恰是 `Coherent` 集**：闭集是「含起始集且对 `dep` 封闭」的集。

这是把 §0 的代数定义（不动点）翻回 `RuleActivation.Coherent` 的语义定义，
⟹ 下游可以直接用「闭集 = 相干集」来读。 -/
theorem closedSets_iff_coherent (dep : R → R → Prop) (suppressed : Set R) (s : Set R) :
    s ∈ closedSets dep suppressed ↔ Coherent ⟨dep, s, suppressed⟩ s := by
  constructor
  · -- 不动点 ⟹ 相干：`s = closureOp s` 是 `Coherent` 的
    intro hs
    have hc : Coherent ⟨dep, s, suppressed⟩ (closureOp dep suppressed s) :=
      closure_coherent ⟨dep, s, suppressed⟩
    rwa [show closureOp dep suppressed s = s from hs] at hc
  · -- 相干 ⟹ 不动点：`closureOp s ⊆ s`（最小性）+ 扩张性
    intro hc
    show closureOp dep suppressed s = s
    exact Set.Subset.antisymm (closure_minimal ⟨dep, s, suppressed⟩ hc)
      (closureOp_extensive dep suppressed s)

/-! ### §4 边界（诚实说明）：`suppressed` 在闭包语义里是惰性参数 -/

/-- **⚠ 事实**：`suppressed` 不影响 `closureOp` 的结果。

**为什么**：`Coherent a T` 只读 `a.dep` 与 `a.init`（见 `RuleActivation.Coherent`
的定义）。`suppressed` 只**通过「不放进 `init`」**起作用 —— 这更正了
`RuleActivation.lean` 文件头「`closure` 内部排除 `suppressed`」的**字面读法**：
排除发生在**构造 `init` 时**，不在闭包算子内部。

本文件如实记录此边界，避免下游误以为 `closureOp` 自己会过滤 `suppressed`。 -/
theorem closureOp_suppressed_irrelevant (dep : R → R → Prop) (s₁ s₂ : Set R) (t : Set R) :
    closureOp dep s₁ t = closureOp dep s₂ t := rfl

end RuleActivation

end FateV2.Rules