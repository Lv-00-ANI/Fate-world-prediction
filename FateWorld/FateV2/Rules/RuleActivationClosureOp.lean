import FateWorld.FateV2.Rules.RuleActivation
import Mathlib.Order.Closure
import FateWorld.FateV2.Rules.RuleReadSet
/-!
  # Rules · RuleActivationClosureOp

  ## 迁移登记
  - 来源：`FateWorld/Legacy/RuleActivationClosureOp.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：RuleActivation, RuleReadSet
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  激活闭包的抽象化：`ClosureOperator` 实例

  ## 背景

  `Fate/RuleActivation.lean` 已定义：
  ```lean
  def Coherent (a : Activation R) (T : Set R) : Prop :=
    a.init ⊆ T ∧ ∀ r ∈ T, ∀ s, a.dep r s → s ∈ T

  def closure (a : Activation R) : Set R := ⋂₀ {T | Coherent a T}
  ```
  并证了 `init_subset_closure` / `closure_dep_closed` / `closure_minimal` / 单调性。

  ## 本节做什么（作者裁决「抽象的抽象」）

  把它提升为 Mathlib 的 `ClosureOperator (Set R)` 实例。这样可接入 Mathlib 的
  闭包算子理论：不动点集自动成完全格，且与 FCA 的 `attrClosureOperator`、
  因果层的祖先闭包在同一框架内可比。

  ## 关键观察

  `closure` 是 `Activation → Set R`（含 `init` 与 `suppressed`），
  **不是** `Set R → Set R`。故需固定 `dep` 与 `suppressed`、只变 `init`。
  =========================================================================== -/

namespace FateV2.Rules

open FateV2.Modeling
namespace RuleActivation

variable {R : Type u}

/-- **固定 `dep` 与 `suppressed`，只变 `init` 的闭包算子**。 -/
def closureOp (dep : R → R → Prop) (suppressed : Set R) (s : Set R) : Set R :=
  RuleActivation.closure ⟨dep, s, suppressed⟩

/-! ### §0.1 扩张性 -/

/-- **扩张性**：`s ⊆ closureOp dep suppressed s`。 -/
theorem closureOp_extensive (dep : R → R → Prop) (suppressed : Set R) (s : Set R) :
    s ⊆ closureOp dep suppressed s := by
  intro x hx
  unfold closureOp
  exact RuleActivation.init_subset_closure ⟨dep, s, suppressed⟩ hx

/-! ### §0.2 单调性 -/

/-- **单调性**：`s ⊆ t ⟹ closureOp s ⊆ closureOp t`。 -/
theorem closureOp_mono (dep : R → R → Prop) (suppressed : Set R) {s t : Set R}
    (hst : s ⊆ t) : closureOp dep suppressed s ⊆ closureOp dep suppressed t := by
  intro x hx
  unfold closureOp at *
  exact RuleActivation.closure_mono_init
    (a := ⟨dep, s, suppressed⟩) (b := ⟨dep, t, suppressed⟩) rfl hst hx

/-! ### §0.3 ⭐ 幂等性 -/

/-- ⭐ **`closure a` 是 `Coherent` 的**：既含 `init`，又对 `dep` 封闭。 -/
theorem closure_coherent (a : Activation R) : Coherent a (closure a) :=
  ⟨RuleActivation.init_subset_closure a,
   fun r hr s hrs => RuleActivation.closure_dep_closed a hr hrs⟩

/-- ⭐ **幂等性**：`closureOp (closureOp s) ⊆ closureOp s`。

**证明**：由 `closure_coherent`，`closureOp s` 是 `Coherent` 的；
再由 `closure_minimal`（`closure` 是最小 Coherent 集），
`closure (closureOp s) ⊆ closureOp s`。 -/
theorem closureOp_idem_subset (dep : R → R → Prop) (suppressed : Set R) (s : Set R) :
    closureOp dep suppressed (closureOp dep suppressed s) ⊆ closureOp dep suppressed s := by
  -- 记 c := closureOp dep suppressed s
  -- 要证 closure ⟨dep, c, supp⟩ ⊆ c
  -- 而 c 是 Coherent ⟨dep, s, supp⟩ 的（closure_coherent）
  -- 且 c 含 s（extensive）
  -- 故 c 是 Coherent ⟨dep, c, supp⟩：它含 c，且对 dep 封闭
  have hcoh : RuleActivation.Coherent ⟨dep, closureOp dep suppressed s, suppressed⟩
      (closureOp dep suppressed s) := by
    refine ⟨subset_rfl, ?_⟩
    intro r hr sg hd
    exact (closure_coherent ⟨dep, s, suppressed⟩).2 r hr sg hd
  exact RuleActivation.closure_minimal ⟨dep, closureOp dep suppressed s, suppressed⟩ hcoh

/-- ⭐ **幂等性（等式形式）**：`closureOp (closureOp s) = closureOp s`。

反向由扩张性给出（`closureOp s ⊆ closureOp (closureOp s)`）。 -/
theorem closureOp_idem (dep : R → R → Prop) (suppressed : Set R) (s : Set R) :
    closureOp dep suppressed (closureOp dep suppressed s) = closureOp dep suppressed s := by
  apply Set.Subset.antisymm
  · exact closureOp_idem_subset dep suppressed s
  · exact closureOp_extensive dep suppressed (closureOp dep suppressed s)

/-! ### §0.4 ⭐ `ClosureOperator` 实例 -/

/-- ⭐⭐ **激活闭包是 `ClosureOperator`**（Mathlib 的标准类型类）。

**⟹ 由此自动获得**：
* 不动点集 `{s | closureOp s = s}` 成完全格
* 与 FCA 的 `attrClosureOperator`、因果的祖先闭包在同一框架内可比
-/
def closureOperator (dep : R → R → Prop) (suppressed : Set R) : ClosureOperator (Set R) where
  toFun := closureOp dep suppressed
  monotone' := fun {_ _} h => closureOp_mono dep suppressed h
  le_closure' := fun s => closureOp_extensive dep suppressed s
  idempotent' := fun s => closureOp_idem dep suppressed s

/-! ### §0.5 推论：闭集族成完全格（自动获得） -/

/-- **闭集族**（`closureOperator` 的不动点）。 -/
def closedSets (dep : R → R → Prop) (suppressed : Set R) : Set (Set R) :=
  {s | closureOp dep suppressed s = s}

/-- ⭐ **闭集族正是 `closureOperator` 的 `IsClosed` 集**（定义展开）。

**⟹ 由此直接接入 Mathlib 的 `ClosureOperator` 理论**：
不动点（闭集）之间的关系、完全格结构等自动可用。 -/
theorem closedSets_eq_isClosed (dep : R → R → Prop) (suppressed : Set R) :
    closedSets dep suppressed = {s | (closureOperator dep suppressed).IsClosed s} := rfl

/-- ⭐ **抽象化的直接收益**：任何 `IsClosed` 集都是闭包的不动点。 -/
theorem isClosed_iff_mem_closedSets (dep : R → R → Prop) (suppressed : Set R)
    (s : Set R) : (closureOperator dep suppressed).IsClosed s ↔ s ∈ closedSets dep suppressed :=
  Iff.rfl

end RuleActivation

end FateV2.Rules
/-! ===========================================================================
  §3  **与 `RuleReadSet` 激活闭包的等价桥**（R-12 真接线）

  ## 背景：「同一个概念的两条独立实现」

  规则层的「激活闭包」在全库被**独立**实现过两次，此前**从未**通信：

  | 实现 | 定义方式 | 位于 |
  |---|---|---|
  | `RuleActivation.closure a` | **交**：`⋂₀ {T \| Coherent a T}`（相干集之交）| `Fate/RuleActivation` |
  | `RuleReadSet.Activation.closure dep I` | **传**：`{s \| ∃ r ∈ I, ReflTransGen dep r s}`（可达集）| `Fate/RuleReadSet` |

  前者**不需要** `R` 有限、不需要选择公理，最小性由交的定义直接给出；
  后者**带显式的依赖链见证**（`closure_member_has_chain`），适合做「按需重激活」
  的构造性论证。二者语义相同但形式不同。

  ## 本节产出（8 条，全部零占位符）

  | # | 定理 | 内容 |
  |---|---|---|
  | **1** | `closure_eq_readSet_closure` | ⭐ 主桥：两种闭包**逐点相等** |
  | **2** | `closureOp_eq_readSet_closure` | `closureOp` 版本的主桥（接 `ClosureOperator`）|
  | **3** | `closure_mem_readSet_closure` | ⋂₀ 闭包成员 ⟹ 可达闭包成员 |
  | **4** | `mem_readSet_closure_exists_chain` | 可达闭包成员 ⟹ **显式依赖链见证**（`RuleReadSet` 的额外信息，⋂₀ 闭包自身给不出）|
  | **5** | `closure_eq_readSet_closure_self` | ⋂₀ 闭包是其自身可达闭包的**不动点**（两侧幂等性兼容）|
  | **6** | `fromData_closure_eq_readSet_closure` | 数据接入场景 `fromData dep S` 的桥 |
  | **7** | `closure_mem_has_chain` | ⋂₀ 闭包成员 ⟹ 存在 `r ∈ init` 沿 `dep` 可达（**跨实现导出**）|
  | **8** | `readSet_closure_subset_closure_of_dep_weaker` | 依赖变强 ⟹ `RuleReadSet` 闭包含于 `RuleActivation` 闭包（两模块单调性对接）|

  **⚠ 注意（防同义反复）**：主桥 `closure_eq_readSet_closure` 的两个**不共边**，
  故其前件只有 `dep`、`init`、`suppressed` 三个自由参数 —— **不预设结论**。
  =========================================================================== -/

namespace FateV2.Rules
namespace RuleActivation

universe u

variable {R : Type u}

/-! ### §3.1 ⭐ 主桥：两条闭包路线相等 -/

/-- ⭐⭐⭐ **规则层激活闭包的两种实现一致**。

$$\bigcap \{T \mid \mathrm{init} \subseteq T \wedge T \text{ 对 } dep \text{ 封闭}\}
  \;=\; \{s \mid \exists r \in \mathrm{init},\ r \xrightarrow{dep*} s\}$$

**证明**：两个包含各用一条最小性定理 ——
`RuleActivation.closure_minimal`（交侧最小）与
`RuleReadSet.Activation.closure_minimal`（可达侧最小）。

**⟹ 由此，凡在任一侧证得的性质都可免费搬到另一侧**（见 §3.2–§3.4）。 -/
theorem closure_eq_readSet_closure (dep : R → R → Prop) (I S : Set R) :
    RuleActivation.closure (⟨dep, I, S⟩ : Activation R)
      = RuleReadSet.Activation.closure dep I := by
  apply Set.Subset.antisymm
  · -- 方向 A：⋂₀ 闭包 ⊆ 可达闭包。可达闭包本身相干。
    apply closure_minimal
    exact ⟨fun x hx => RuleReadSet.Activation.closure_extensive dep I hx,
           fun r hr s h => RuleReadSet.Activation.closure_closed dep hr h⟩
  · -- 方向 B：可达闭包 ⊆ ⋂₀ 闭包。⋂₀ 闭包含 init 且对 dep 封闭。
    intro x hx
    exact RuleReadSet.Activation.closure_minimal dep
      (fun y hy => init_subset_closure _ hy)
      (fun a ha b h => closure_dep_closed _ ha h) hx

/-- **`closureOp` 版本的主桥**：把 `Fate/RuleActivationClosureOp` 的抽象闭包算子
`closureOp dep suppressed I` 直接等同于 `RuleReadSet` 的可达闭包。

**⟹ 于是 Mathlib `ClosureOperator`（`closureOperator`）的一切结果，
对 `RuleReadSet.Activation.closure` 自动成立。** -/
theorem closureOp_eq_readSet_closure (dep : R → R → Prop) (S : Set R) (I : Set R) :
    closureOp dep S I = RuleReadSet.Activation.closure dep I := by
  unfold closureOp
  exact closure_eq_readSet_closure dep I S

/-! ### §3.2 两个方向分别可取用 -/

/-- **⋂₀ 闭包成员 ⟹ 可达闭包成员**（把 `RuleActivation` 的成员资格交给 `RuleReadSet`）。 -/
theorem closure_mem_readSet_closure (dep : R → R → Prop) (I S : Set R) {r s : R}
    (hr : r ∈ RuleActivation.closure (⟨dep, I, S⟩ : Activation R)) (hd : dep r s) :
    s ∈ RuleReadSet.Activation.closure dep I := by
  rw [closure_eq_readSet_closure dep I S] at hr
  exact RuleReadSet.Activation.closure_closed dep hr hd

/-- ⭐ **可达闭包成员 ⟹ 显式依赖链见证**。

这是 `RuleReadSet` 侧**比 ⋂₀ 定义更强的信息**：闭包里的每个规则都能给出
`∃ r ∈ init, r \xrightarrow{dep*} s` 的构造性证据 ——
⋂₀ 闭包自身（交的定义）给不出这样的链。 -/
theorem mem_readSet_closure_exists_chain (dep : R → R → Prop) (I _S : Set R) {s : R}
    (hs : s ∈ RuleReadSet.Activation.closure dep I) :
    ∃ r ∈ I, Relation.ReflTransGen dep r s :=
  RuleReadSet.Activation.closure_member_has_chain dep hs

/-! ### §3.3 幂等性与不动点 -/

/-- ⭐ **两侧幂等性兼容**：⋂₀ 闭包恰是其**自身可达闭包**的不动点。

**⟹ 语义**：「对闭包再取一次按需重激活，激活集不变」——
即「数据停用 + 重激活」已达**稳定态**。 -/
theorem closure_eq_readSet_closure_self (dep : R → R → Prop) (I S : Set R) :
    RuleActivation.closure (⟨dep, I, S⟩ : Activation R)
      = RuleReadSet.Activation.closure dep
          (RuleActivation.closure (⟨dep, I, S⟩ : Activation R)) := by
  rw [closure_eq_readSet_closure dep I S]
  exact (RuleReadSet.Activation.closure_idempotent dep I).symm

/-! ### §3.4 与外模块既有构造（`fromData`）的对接 -/

/-- ⭐ **数据接入场景的桥**：`fromData dep S`（「开始全部激活，数据抑制 `S`」）
的闭包 = 从 `univ \ S` 出发的可达闭包。

**⟹ 这条把 `RuleActivation.fromData` 的语义（数据判决 = 从种子里去掉）
翻译成 `RuleReadSet` 的显式种子集，两模块的「数据接入」口径统一。** -/
theorem fromData_closure_eq_readSet_closure (dep : R → R → Prop) (S : Set R) :
    RuleActivation.closure (RuleActivation.fromData dep S)
      = RuleReadSet.Activation.closure dep (Set.univ \ S) :=
  closure_eq_readSet_closure dep (Set.univ \ S) S

/-- ⭐ **跨实现导出依赖链**：⋂₀ 闭包里的每个成员，都有从 `init` 出发的依赖链。

**⟹ 这是「交定义」白拿不到、经桥从「可达定义」借来的信息**，
是本次接线的直接收益之一。 -/
theorem closure_mem_has_chain (dep : R → R → Prop) (I S : Set R) {s : R}
    (hs : s ∈ RuleActivation.closure (⟨dep, I, S⟩ : Activation R)) :
    ∃ r ∈ I, Relation.ReflTransGen dep r s := by
  rw [closure_eq_readSet_closure dep I S] at hs
  exact RuleReadSet.Activation.closure_member_has_chain dep hs

/-! ### §3.5 两侧单调性对接 -/

/-- ⭐ **依赖变强 ⟹ `RuleReadSet` 闭包含于 `RuleActivation` 闭包**（换 `dep` 版本）。

**⟹ 把 `RuleReadSet.Activation.closure_mono_dep`（左侧单调）
与主桥（右端的 ⋂₀ 表示）复合，得到两模块间**唯一的跨关系搬移定理**。 -/
theorem readSet_closure_subset_closure_of_dep_weaker {dep dep' : R → R → Prop}
    (I _S : Set R) (S' : Set R) (h : ∀ {a b : R}, dep a b → dep' a b) :
    RuleReadSet.Activation.closure dep I
      ⊆ RuleActivation.closure (⟨dep', I, S'⟩ : Activation R) := by
  rw [closure_eq_readSet_closure dep' I S']
  exact RuleReadSet.Activation.closure_mono_dep h

end RuleActivation

end FateV2.Rules
/-! ### §3.6 全限定路径别名（供跨模块检索） -/

namespace RuleReadSetBridge

/-- **全限定路径写法的主桥**：与 `RuleActivation.closure_eq_readSet_closure` 同一命题，
但两侧均以 `Fate.` 全限定路径书写，便于跨模块静态检索（`grep 'Fate\.RuleXYZ\.'`）。

**⟹ 命题内容与 §3.1 完全相同，不含新数学；仅为接线可检出性而设的显式别名。** -/
theorem closure_eq_readSet_closure' (dep : R → R → Prop) (I S : Set R) :
    FateV2.Rules.RuleActivation.closure (⟨dep, I, S⟩ : FateV2.Rules.RuleActivation.Activation R)
      = FateV2.Rules.RuleReadSet.Activation.closure dep I :=
  FateV2.Rules.RuleActivation.closure_eq_readSet_closure dep I S

/-- **依赖链见证的全限定别名**（⋂₀ 闭包成员 ⟹ 存在 `init` 出发的 `dep` 链）。 -/
theorem closure_mem_has_chain' (dep : R → R → Prop) (I S : Set R) {s : R}
    (hs : s ∈ FateV2.Rules.RuleActivation.closure (⟨dep, I, S⟩ : FateV2.Rules.RuleActivation.Activation R)) :
    ∃ r ∈ I, Relation.ReflTransGen dep r s :=
  FateV2.Rules.RuleActivation.closure_mem_has_chain dep I S hs

end RuleReadSetBridge

/-! ===========================================================================
  §4  ⭐⭐ **闭包算子不动点视角 ⟹ 因果层祖先闭包**（R-41 接线）

  ## 背景（真实缺口，实测）

  §0 已把激活闭包提升为 Mathlib 的 `ClosureOperator (Set R)` 实例，
  并定义了 `closedSets`（不动点族）。
  §3 又把 `RuleActivation.closure` 与 `RuleReadSet.Activation.closure` 接起来，
  而 `Fate/RuleReadSet.lean` 的 §4（`AncestralIso`）已证
  **`AncestralSet G S = Activation.closure revAnc S`**。

  **⚠ 缺口**：`AncestralIso` 的三条推论（`ancestralSet_idem_via_closure` 等）
  全部只在 **`Activation.closure`** 侧陈述；
  **没有任何定理把因果层祖先闭包接到 §0 的 `closureOperator` / `closedSets`
  （即 Mathlib `ClosureOperator.IsClosed`）这一侧。**

  ## 本节做什么

  把 `revAnc G := fun x y => Ancestor G y x`（反向祖先关系）作为依赖关系，
  证明**祖先闭包恰是 §0 闭包算子的不动点**，并给出闭集的**完整刻画**：

  | # | 名称 | 内容 |
  |---|---|---|
  | **R1** | `ancestralSet_eq_closureOp` | `AncestralSet G S = closureOp revAnc S S` |
  | **R2** | `ancestralSet_mem_closedSets` | `AncestralSet G S ∈ closedSets revAnc S` |
  | **R3** | `ancestralSet_isClosed` | `(closureOperator revAnc S).IsClosed (AncestralSet G S)` |
  | **R4** | `ancestralSet_subset_of_mem_closedSets` | 闭集超集 `T ⊇ S` ⟹ `AncestralSet G S ⊆ T` |
  | **R5** | `mem_closedSets_iff_ancestralSet_eq` | ⭐ `S ∈ closedSets revAnc S ↔ AncestralSet G S = S` |

  **⚠ 防同义反复检查（逐条）**：
  * R1 的前件只有 `G`、`S`（无假设）；两边的**定义来源不同**（§0 的 `closureOp`
    vs `RuleReadSet`/`Ancestral` 的 `AncestralSet`）。
  * R2/R3 的前件只有 `G`、`S`；结论由 R1 + `closure_idempotent` 推出，
    **不是**由 `closedSets` 的定义直接搬。
  * R4 的前件是 `S ⊆ T` 与 `T ∈ closedSets revAnc S`（后者是 `T` 侧的条件），
    结论是**关于 `AncestralSet G S`** 的包含 —— `T` 与 `AncestralSet G S`
    是两个不同的集合，故不循环。
  * R5 是 R2 与 R4 的**双向合成**；两个方向分别用不同的引理，
    且 R5 的左侧（`closedSets` 成员）与右侧（祖先闭包等于自身）**定义不同**。
  =========================================================================== -/

namespace FateV2.Rules
namespace RuleActivation

universe v

variable {V : Type v}

/-- **`revAnc`（反向祖先关系）**：`revAnc G x y` 表示「`x` 是 `y` 的祖先」的反向边，
即把 `dep` 取作 `fun x y => Ancestor G y x`（正是 `RuleReadSet.ancestralSet_eq_closure`
所用的依赖关系）。 -/
abbrev revAnc {G : FateV2.Predict.CausalDirection.CausalGraph V} : V → V → Prop :=
  fun x y => FateV2.Predict.Ancestral.Ancestor G y x

/-- **R1**：⭐⭐ **祖先闭包 = §0 闭包算子在种子 `S` 上的取值**。

把 §3 的主桥（`closureOp_eq_readSet_closure`）与
`RuleReadSet.ancestralSet_eq_closure` 复合，
得到「因果层祖先闭包」在**规则层闭包算子**中的表示。 -/
theorem ancestralSet_eq_closureOp {G : FateV2.Predict.CausalDirection.CausalGraph V} (S : Set V) :
    FateV2.Predict.Ancestral.AncestralSet G S = closureOp (revAnc (G := G)) S S := by
  rw [closureOp_eq_readSet_closure, RuleReadSet.ancestralSet_eq_closure]

/-- **R2**：⭐⭐ **祖先闭包是 `closedSets` 的元素**（闭包算子的不动点）。

**证明**：由 R1 把目标化为 `closureOp revAnc S (closureOp revAnc S S) = closureOp revAnc S S`，
再经 §3 的主桥换成 `RuleReadSet` 侧，用 `closure_idempotent`。 -/
theorem ancestralSet_mem_closedSets {G : FateV2.Predict.CausalDirection.CausalGraph V} (S : Set V) :
    FateV2.Predict.Ancestral.AncestralSet G S ∈ closedSets (revAnc (G := G)) S := by
  unfold closedSets
  simp only [Set.mem_setOf_eq]
  rw [ancestralSet_eq_closureOp]
  rw [closureOp_eq_readSet_closure, closureOp_eq_readSet_closure,
      RuleReadSet.Activation.closure_idempotent]

/-- **R3**：⭐⭐ **祖先闭包是 Mathlib `ClosureOperator.IsClosed` 的成员**。

这是 R2 在 `closedSets_eq_isClosed` 下的直接翻译，
使祖先闭包**接入 Mathlib 的闭包算子理论**（完全格结构等）。 -/
theorem ancestralSet_isClosed {G : FateV2.Predict.CausalDirection.CausalGraph V} (S : Set V) :
    (closureOperator (revAnc (G := G)) S).IsClosed (FateV2.Predict.Ancestral.AncestralSet G S) :=
  (isClosed_iff_mem_closedSets _ _ _).mpr (ancestralSet_mem_closedSets S)

/-- **R4**：⭐⭐ **闭集超集 ⟹ 含祖先闭包**（最小性的闭集形式）。

若 `T` 是闭包算子的不动点（`T ∈ closedSets revAnc S`）且 `S ⊆ T`，
则 `AncestralSet G S ⊆ T`。

**⚠ 非循环**：前件说的是 **`T`** 的性质（`T` 是闭集、`T` 包含 `S`），
结论说的是 **`AncestralSet G S`** 被 `T` 包含 —— 两者是不同的集合对象。 -/
theorem ancestralSet_subset_of_mem_closedSets {G : FateV2.Predict.CausalDirection.CausalGraph V}
    {S T : Set V} (hST : S ⊆ T) (hT : T ∈ closedSets (revAnc (G := G)) S) :
    FateV2.Predict.Ancestral.AncestralSet G S ⊆ T := by
  have hcl : closureOp (revAnc (G := G)) S T = T := hT
  rw [closureOp_eq_readSet_closure] at hcl
  have hsub : RuleReadSet.Activation.closure (revAnc (G := G)) S
      ⊆ RuleReadSet.Activation.closure (revAnc (G := G)) T :=
    RuleReadSet.Activation.closure_mono_I (revAnc (G := G)) hST
  rw [hcl] at hsub
  intro x hx
  have hx' : x ∈ RuleReadSet.Activation.closure (revAnc (G := G)) S := by
    have heq := RuleReadSet.ancestralSet_eq_closure (G := G) S
    exact heq ▸ hx
  exact hsub hx'

/-- **R5**：⭐⭐⭐ **闭集的完整刻画**：`S` 是闭集 ⟺ 其祖先闭包等于自身。

**⟹ 这是本节的主结论**：它把「`S` 对反向祖先关系封闭」（因果层语言）
与「`S` 是闭包算子的不动点」（Mathlib `ClosureOperator` 语言）**完全等同**。
* 方向 `→`：R4（取 `T = S`，需要 `S ⊆ S`）给出 `AncestralSet G S ⊆ S`，
  与 `subset_ancestralSet_via_closure`（`S ⊆ AncestralSet G S`）合成等号。
* 方向 `←`：R2（`AncestralSet G S` 是闭集）加上结论中的等式即可。 -/
theorem mem_closedSets_iff_ancestralSet_eq {G : FateV2.Predict.CausalDirection.CausalGraph V} (S : Set V) :
    S ∈ closedSets (revAnc (G := G)) S ↔ FateV2.Predict.Ancestral.AncestralSet G S = S := by
  constructor
  · intro hS
    have h := ancestralSet_subset_of_mem_closedSets (S := S) (T := S) (fun _ hx => hx) hS
    exact Set.Subset.antisymm h (RuleReadSet.subset_ancestralSet_via_closure G S)
  · intro hEq
    have hmem := ancestralSet_mem_closedSets (G := G) S
    rw [hEq] at hmem
    exact hmem

end RuleActivation

end FateV2.Rules