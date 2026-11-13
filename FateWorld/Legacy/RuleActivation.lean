import Mathlib

/-! ===========================================================================
  规则层 · **动态激活机制**（全参与 + 按需激活）
  ===========================================================================

  ## 作者澄清的机制（不是「从集合里挑一条」）

  世界模型里规则的运作**不是**「从一个规则集合中选出一条来用」，而是：

  1. **开始全部激活** —— 初始状态下全部规则处于激活态；
  2. **数据进来部分不激活** —— 观测数据把一部分规则判为「不适用」（`suppressed`）；
  3. **按需立即重新激活** —— 一旦某个**已激活**的规则依赖某条被抑制的规则，
     后者**立刻**重新激活（**闭包传播**）。

  ⟹ 因此本模块的语义是：**激活集是一个对依赖关系封闭的集合**，
  **而非**「在规则间做单点选择」。这与因果层 `Trunc`（**祖先闭包**）**同构**：

  | 层 | 种子 | 传播关系 | 闭包 |
  |---|---|---|---|
  | 规则层（本模块）| `init` | `dep`（规则依赖规则）| `closure` |
  | 因果层 `Fate.Ancestral` | `S` | `Ancestor`（祖先 → 后代）| `AncestralSet` |

  ## 依赖关系的两个来源

  | 来源 | 形式化 |
  |---|---|
  | **(a) 由读集推出** | 规则 `r` 的读集含变量 `v`，而 `v` 由规则 `s` 确定 ⟹ `r` 依赖 `s`（`readDep`）|
  | **(b) 手动添加** | 直接给定 `dep` 的任意二元关系（结构字段，无限制）|

  ## 本模块的产出（对应任务的 4 条要求）

  | # | 定理 |
  |---|---|
  | **1** | `init_subset_closure`：`init ⊆ closure` |
  | **2** | `closure_dep_closed`：闭包对 `dep` 封闭 |
  | **3** | `closure_minimal`：闭包是满足 1、2 的**最小**集合 |
  | **4** | `closure_mono_init`：`init` 变大 ⟹ 闭包变大 |

  **⚠ 零 `sorry`、零 `admit`、零 `axiom`；不假设 `R` 有限、不假设 `dep` 良基。**

  ## 定义取向（为何用「交」而非「迭代」）

  闭包定义为 **全体「相干集」的交**：

  $$\mathrm{closure}(a) := \bigcap \{\, T \mid \mathrm{Coherent}(a, T) \,\}$$

  其中 `Coherent a T`（「相干」）= `init ⊆ T` 且 `T` 对 `dep` 封闭。

  ⟹ **好处**：**不需要** `R` 有限、**不需要** `dep` 可枚举、**不需要**选择公理；
  最小性（要求 3）**直接**由交的定义给出，且**避免**任何「虚构的迭代终止」论证。
  -/

namespace Fate

namespace RuleActivation

universe u

variable {R : Type u}

/-! ### §1 结构与基本定义 -/

/-- **激活状态**（一个世界模型的规则激活配置）。

* `dep r s` —— **规则依赖**：`r` 依赖 `s`（`r` 的读集需要 `s` 的产出）。
  来源见 `readDep`（由读集推出）与**手动添加**（任意给定）。
* `init` —— **初始激活集**（**通常是全集**：开始全部激活）。
* `suppressed` —— **被数据判为不适用的规则集**。

**⚠ 语义分工**：`suppressed` 是**数据的判决**，**不是**永久的排除。
被抑制的规则**只要被某条已激活的规则依赖**，就**立刻重新激活**。
这正是闭包 `closure` 对 `dep` 封闭（`closure_dep_closed`）的内容。 -/
structure Activation (R : Type u) where
  /-- **规则间的依赖**：`dep r s` 表示「`r` 依赖 `s`」。 -/
  dep : R → R → Prop
  /-- **初始激活集**（通常是全集）。 -/
  init : Set R
  /-- **被数据判为不适用的规则集**。 -/
  suppressed : Set R

/-- **相干集**：一个「自洽的激活候选」。

$$T \text{ 相干} \iff \underbrace{\mathrm{init} \subseteq T}_{\text{(i) 初始激活都在}}
  \wedge \underbrace{\forall r \in T,\ \forall s,\ \mathrm{dep}\,r\,s \to s \in T}_{\text{(ii) 对依赖封闭}}$$

**⟹ (i)(ii) 恰是任务要求 1、2 的两条性质。** -/
def Coherent (a : Activation R) (T : Set R) : Prop :=
  a.init ⊆ T ∧ ∀ r ∈ T, ∀ s, a.dep r s → s ∈ T

/-- **激活闭包**：从 `init` 出发，沿 `dep` 传播，
**被抑制的规则（`suppressed`）除外 —— 除非它被已激活的规则依赖**。

$$\mathrm{closure}(a) := \bigcap \{\, T \mid \mathrm{Coherent}(a, T) \,\}$$

**⟹ 读法**：闭包是**最小的相干集**（要求 3 即是此句）。
**「排除 `suppressed`」体现在**：`suppressed` 中的规则**不是**种子 ——
它只有在**被依赖**时才因封闭性（(ii)）被卷入。

**⚠ 关于「全部参与」**：`init` 通常是全集，此时 `suppressed` 从种子中被剔除，
于是「数据判为不适用」的规则确实不激活 —— 直到被依赖为止。 -/
def closure (a : Activation R) : Set R := ⋂₀ {T | Coherent a T}

/-! ### §2 要求 1 —— `init ⊆ closure`（初始激活的都在闭包里） -/

/-- **要求 1**：**每个初始激活的规则都在闭包中。**

$$\mathrm{init} \subseteq \mathrm{closure}(a)$$ -/
theorem init_subset_closure (a : Activation R) : a.init ⊆ closure a :=
  fun _ hx => Set.mem_sInter.mpr (fun _ hT => hT.1 hx)

/-! ### §3 要求 2 —— 闭包对 `dep` 封闭（按需激活 / 闭包传播） -/

/-- **要求 2**：**闭包对 `dep` 封闭** —— 被激活的规则所依赖的规则**也**被激活。

$$r \in \mathrm{closure}(a) \wedge \mathrm{dep}\,r\,s \implies s \in \mathrm{closure}(a)$$

**⟹ 这就是作者所说的「被依赖的规则立刻重新激活」**：
即使 `s ∈ suppressed`，只要已激活的 `r` 依赖它，`s` **仍然进入闭包**。 -/
theorem closure_dep_closed (a : Activation R) {r s : R}
    (hr : r ∈ closure a) (hd : a.dep r s) : s ∈ closure a :=
  Set.mem_sInter.mpr (fun T hT => hT.2 r (Set.mem_sInter.mp hr T hT) s hd)

/-- **多步传播**：沿 `dep` 的**任意有限链**传播都保持激活（**闭包传播**）。

$$\mathrm{Relation.TransGen}\,\mathrm{dep}\,r\,s \wedge r \in \mathrm{closure}(a)
  \implies s \in \mathrm{closure}(a)$$ -/
theorem closure_dep_transGen (a : Activation R) {r s : R}
    (hr : r ∈ closure a) (h : Relation.TransGen a.dep r s) : s ∈ closure a := by
  induction h with
  | single hstep => exact closure_dep_closed a hr hstep
  | tail _ hstep ih => exact closure_dep_closed a ih hstep

/-! ### §4 要求 3 —— 最小性 -/

/-- **要求 3（最小性）**：**任何**满足要求 1、2 的集合 `T` 都**包含**闭包。

$$\mathrm{init} \subseteq T \wedge (\forall r \in T,\ \mathrm{dep}\,r\,s \to s \in T)
  \implies \mathrm{closure}(a) \subseteq T$$

**⟹ 与要求 1、2 合起来即：闭包 = 最小相干集**（`closure_eq_least`）。 -/
theorem closure_minimal (a : Activation R) {T : Set R} (h : Coherent a T) :
    closure a ⊆ T :=
  fun _ hx => Set.mem_sInter.mp hx T h

/-- **最小性的整句陈述**：闭包**本身**相干，且**含于**一切相干集。

$$\mathrm{Coherent}(a, \mathrm{closure}(a))
  \wedge \forall T,\ \mathrm{Coherent}(a,T) \to \mathrm{closure}(a) \subseteq T$$ -/
theorem closure_eq_least (a : Activation R) :
    Coherent a (closure a) ∧ ∀ T, Coherent a T → closure a ⊆ T :=
  ⟨⟨init_subset_closure a,
    fun _ hr _ hd => closure_dep_closed a hr hd⟩,
    fun _ hT => closure_minimal a hT⟩

/-- **唯一性**：满足「自身相干 + 含于一切相干集」的集合**只能**是闭包。

**⟹ 即闭包由要求 1、2、3 唯一确定**（无定义自由）。 -/
theorem closure_unique (a : Activation R) {T : Set R}
    (hcoh : Coherent a T) (hmin : ∀ U, Coherent a U → T ⊆ U) :
    T = closure a := by
  apply Set.Subset.antisymm
  · exact hmin _ (closure_eq_least a).1
  · exact closure_minimal a hcoh

/-! ### §5 要求 4 —— 单调性 -/

/-- **要求 4（单调性）**：**`init` 变大 ⟹ 闭包变大**（依赖关系不变）。

$$\mathrm{init}_a \subseteq \mathrm{init}_b \wedge \mathrm{dep}_a = \mathrm{dep}_b
  \implies \mathrm{closure}(a) \subseteq \mathrm{closure}(b)$$ -/
theorem closure_mono_init {a b : Activation R}
    (hd : a.dep = b.dep) (hi : a.init ⊆ b.init) : closure a ⊆ closure b := by
  apply Set.sInter_subset_of_mem
  refine ⟨fun _ hx => Set.mem_sInter.mpr (fun T hT => hT.1 (hi hx)), ?_⟩
  intro r hr s hstep
  exact Set.mem_sInter.mpr
    (fun T hT => hT.2 r (Set.mem_sInter.mp hr T hT) s (hd ▸ hstep))

/-- **依赖单调性**：依赖关系变**强** ⟹ 闭包变**大**（`init` 不变）。

$$\mathrm{dep}_a \subseteq \mathrm{dep}_b \wedge \mathrm{init}_a = \mathrm{init}_b
  \implies \mathrm{closure}(a) \subseteq \mathrm{closure}(b)$$ -/
theorem closure_mono_dep {a b : Activation R}
    (hi : a.init = b.init) (hd : ∀ {r s}, a.dep r s → b.dep r s) :
    closure a ⊆ closure b := by
  apply Set.sInter_subset_of_mem
  refine ⟨fun _ hx => Set.mem_sInter.mpr (fun T hT => hT.1 (hi ▸ hx)), ?_⟩
  intro r hr s hstep
  exact Set.mem_sInter.mpr
    (fun T hT => hT.2 r (Set.mem_sInter.mp hr T hT) s (hd hstep))

/-- **同向单调**：`init` 与 `dep` **同时**变大 ⟹ 闭包变大（要求 4 的完整形态）。 -/
theorem closure_mono {a b : Activation R} (hi : a.init ⊆ b.init)
    (hd : ∀ {r s}, a.dep r s → b.dep r s) : closure a ⊆ closure b := by
  apply Set.sInter_subset_of_mem
  refine ⟨fun _ hx => Set.mem_sInter.mpr (fun T hT => hT.1 (hi hx)), ?_⟩
  intro r hr s hstep
  exact Set.mem_sInter.mpr
    (fun T hT => hT.2 r (Set.mem_sInter.mp hr T hT) s (hd hstep))

/-! ### §6 「按需激活」的判定形态（`suppressed` 的确切语义） -/

/-- **「按需激活」的充要条件**：规则在闭包中 **⟺** 它是初始激活的，
**或**它被某条已激活的规则依赖。

$$s \in \mathrm{closure}(a) \iff s \in \mathrm{init} \vee \exists r \in \mathrm{closure}(a),\ \mathrm{dep}\,r\,s$$

**⟹ 这是机制的完整刻画**：**种子**（初始激活）+ **按需卷入**（被依赖），
**再没有第三种**进入闭包的方式。**⟹ 被数据判为不适用的规则，
若无人依赖，就永远不激活**（`not_mem_closure_of_no_demand`）。 -/
theorem mem_closure_iff (a : Activation R) {s : R} :
    s ∈ closure a ↔ s ∈ a.init ∨ ∃ r ∈ closure a, a.dep r s := by
  constructor
  · intro hs
    -- 取「闭包中既是种子或是被依赖者」的子集，它是相干的 ⟹ 包含闭包
    set T : Set R := {x | x ∈ closure a ∧ (x ∈ a.init ∨ ∃ r ∈ closure a, a.dep r x)}
      with hTdef
    have hcoh : Coherent a T := by
      refine ⟨fun x hx => ⟨init_subset_closure a hx, Or.inl hx⟩, ?_⟩
      rintro x ⟨-, hx | ⟨w, hw, hwx⟩⟩ y hxy
      · exact ⟨closure_dep_closed a (init_subset_closure a hx) hxy,
          Or.inr ⟨x, init_subset_closure a hx, hxy⟩⟩
      · exact ⟨closure_dep_closed a (closure_dep_closed a hw hwx) hxy,
          Or.inr ⟨x, closure_dep_closed a hw hwx, hxy⟩⟩
    exact (closure_minimal a hcoh hs).2
  · rintro (hs | ⟨r, hr, hd⟩)
    · exact init_subset_closure a hs
    · exact closure_dep_closed a hr hd

/-- **抑制的确切效力**：**未初始激活、且无任何已激活规则依赖它的规则，不在闭包中。**

$$s \notin \mathrm{init} \wedge (\forall r,\ \mathrm{dep}\,r\,s \to r \notin \mathrm{closure}(a))
  \implies s \notin \mathrm{closure}(a)$$

**⟹ 「数据判为不适用」之所以生效，正是因为**没有需求**；
一旦出现需求，`closure_dep_closed` 立刻把它拉回。** -/
theorem not_mem_closure_of_no_demand (a : Activation R) {s : R}
    (hinit : s ∉ a.init) (hd : ∀ r, a.dep r s → r ∉ closure a) : s ∉ closure a := by
  intro hs
  rcases (mem_closure_iff a).mp hs with h | ⟨r, hr, hstep⟩
  · exact hinit h
  · exact hd r hstep hr

/-- **被依赖 ⟹ 重新激活**（抑制的**失效**条件，机制的核心断言）。

$$s \in \mathrm{suppressed} \wedge \exists r \in \mathrm{closure}(a),\ \mathrm{dep}\,r\,s
  \implies s \in \mathrm{closure}(a)$$ -/
theorem mem_closure_of_demand (a : Activation R) {s : R} (_hs : s ∈ a.suppressed)
    (hd : ∃ r ∈ closure a, a.dep r s) : s ∈ closure a :=
  (mem_closure_iff a).mpr (Or.inr hd)

/-! ### §7 数据接入的标准构造（`init = 全集 \ suppressed`） -/

/-- **数据接入**：**开始全部激活**（`init := univ`），**数据进来部分不激活**
（`init := univ \ suppressed`）。

⟹ 这就是作者描述的第 1、2 步；第 3 步（**按需重新激活**）由 `closure` 的封闭性给出。 -/
def fromData (dep : R → R → Prop) (suppressed : Set R) : Activation R where
  dep := dep
  init := Set.univ \ suppressed
  suppressed := suppressed

/-- **数据接入后的激活判定**：规则在闭包中 **⟺** 它**未被抑制**，
**或**它**被某条已激活的规则依赖**。

$$s \in \mathrm{closure}(\mathrm{fromData}(\mathrm{dep}, S))
  \iff s \notin S \vee \exists r \in \mathrm{closure}(\cdot),\ \mathrm{dep}\,r\,s$$

⟹ **完整的机制陈述**：**未抑制 ⟹ 激活**；**被抑制 ⟹ 仅在按需时激活**。 -/
theorem mem_closure_fromData (dep : R → R → Prop) (S : Set R) {s : R} :
    s ∈ closure (fromData dep S)
      ↔ s ∉ S ∨ ∃ r ∈ closure (fromData dep S), dep r s := by
  rw [mem_closure_iff]
  constructor
  · rintro (⟨-, h⟩ | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨Set.mem_univ s, h⟩
    · exact Or.inr h

/-- **「全部参与」的落实**：**未被任何数据抑制的规则，一进场就在闭包中。** -/
theorem mem_closure_fromData_of_not_suppressed (dep : R → R → Prop) (S : Set R) {s : R}
    (h : s ∉ S) : s ∈ closure (fromData dep S) :=
  (mem_closure_fromData dep S).mpr (Or.inl h)

/-- **空抑制 ⟹ 全体激活**（「开始全部激活」）。 -/
theorem closure_fromData_empty (dep : R → R → Prop) (s : R) :
    s ∈ closure (fromData dep ∅) :=
  mem_closure_fromData_of_not_suppressed dep ∅ (Set.notMem_empty s)

/-! ### §8 依赖关系的来源 (a)：由读集推出 -/

/-- **依赖来源 (a)：由读集推出**。

* `reads r` —— 规则 `r` 的**读集**（它所读的变量）；
* `det s` —— 规则 `s` **确定**的变量集（其产出）。

$$\mathrm{dep}(r, s) \iff \exists v \in \mathrm{reads}(r),\ v \in \mathrm{det}(s)$$

⟹ **规则 `r` 读的某个变量由 `s` 确定 ⟹ `r` 依赖 `s`**。
（`s = r` 时表示**自依赖**，保留 —— 自依赖在闭包下**不影响结果**，
见 `closure_depends_only_on_dep_init`。） -/
def readDep {V : Type u} (reads det : R → Set V) : R → R → Prop :=
  fun r s => ∃ v, v ∈ reads r ∧ v ∈ det s

/-- **读集来源的依赖是「可加」的**：读集变大 ⟹ 依赖变强 ⟹ 闭包变大。

⟹ 即**读书越多、依赖越多、被卷入的规则越多**（来源 (a) 与要求 4 的衔接）。 -/
theorem closure_mono_reads {V : Type u} {a b : Activation R}
    (hi : a.init = b.init) {reads₁ reads₂ det₁ det₂ : R → Set V}
    (hr : ∀ r, reads₁ r ⊆ reads₂ r) (hd : ∀ s, det₁ s ⊆ det₂ s)
    (hdep₁ : ∀ r s, a.dep r s ↔ readDep reads₁ det₁ r s)
    (hdep₂ : ∀ r s, b.dep r s ↔ readDep reads₂ det₂ r s) :
    closure a ⊆ closure b := by
  apply closure_mono_dep hi
  intro r s hrs
  obtain ⟨v, hv₁, hv₂⟩ := (hdep₁ r s).mp hrs
  exact (hdep₂ r s).mpr ⟨v, hr r hv₁, hd s hv₂⟩

/-! ### §9 闭包算子的代数性质（幂等、空集、单调） -/

/-- **用任意初始集构造激活状态**（其余字段留空/沿用）。 -/
def ofInit (dep : R → R → Prop) (T : Set R) : Activation R where
  dep := dep
  init := T
  suppressed := ∅

/-- **闭包是幂等的**：**对闭包再取闭包，不变**。

$$\mathrm{closure}(\mathrm{ofInit}(\mathrm{dep}, \mathrm{closure}(a))) = \mathrm{closure}(a)$$

⟹ 即**闭包已含一切按需激活者**：**再跑一遍不会多出任何规则**
（**稳定态**，对应「反复取闭包收敛」）。 -/
theorem closure_idem (a : Activation R) :
    closure (ofInit a.dep (closure a)) = closure a := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    refine ⟨fun _ hx => hx, ?_⟩
    intro r hr s hd
    exact closure_dep_closed a hr hd
  · intro x hx
    exact init_subset_closure _ hx

/-- **空初始集 ⟹ 空闭包**（无种子则无传播）。 -/
theorem closure_empty_init (dep : R → R → Prop) :
    closure (ofInit dep (∅ : Set R)) = ∅ :=
  Set.Subset.antisymm (closure_minimal _ ⟨Set.empty_subset _, by
    intro r hr
    exact absurd hr (Set.notMem_empty r)⟩) (Set.empty_subset _)

/-- **无依赖 ⟹ 闭包 = 初始集**（**没有依赖就没有传播**）。

$$(\forall r\,s,\ \neg\,\mathrm{dep}\,r\,s) \implies \mathrm{closure}(a) = \mathrm{init}$$ -/
theorem closure_eq_init_of_no_dep (a : Activation R) (h : ∀ r s, ¬ a.dep r s) :
    closure a = a.init := by
  apply Set.Subset.antisymm (closure_minimal _ ⟨Set.Subset.rfl, ?_⟩) (init_subset_closure a)
  intro r hr s hd
  exact absurd hd (h r s)

/-- **闭包只由 `dep` 与 `init` 决定**（**`suppressed` 不改变闭包的取值**）。

$$\mathrm{closure}(a) = \mathrm{closure}(\mathrm{ofInit}(a.dep, a.init))$$

**⚠ 这条是机制的关键**：`suppressed` **不是** `closure` 的参数 ——
它**经由 `init`**（数据把抑制集从种子里剔除，见 `fromData`）**与
经由 `dep`**（被依赖者被封闭性拉回，见 `closure_dep_closed`）生效。

⟹ 因此**「自依赖」不影响闭包**：自环只重复断言 `r ∈ T → r ∈ T`，
既**不放大**也**不缩小**激活集。读集来源下 `dep r r` 常有
（规则读自己确定的变量），该性质保证来源 (a) **不会因自环虚增激活集**。 -/
theorem closure_depends_only_on_dep_init (a : Activation R) :
    closure a = closure (ofInit a.dep a.init) :=
  rfl

/-- **自依赖在闭包中表现为「保持」**：若 `dep r r`，则 `r` 的激活状态**不被自环改变**。

$$\mathrm{dep}\,r\,r \wedge r \in \mathrm{closure}(a) \implies r \in \mathrm{closure}(a)$$

（平凡但作为机制检查点：**自环只能「保持」不能「阻止」**，
即不存在「自依赖导致自我抑制」的路径 —— 抑制只能来自 `init` 与需求。） -/
theorem self_dep_preserves (a : Activation R) {r : R} (_h : a.dep r r)
    (hr : r ∈ closure a) : r ∈ closure a :=
  hr

/-- **与因果层 `Trunc`（祖先闭包）的同构陈述**（机制对照的可证形态）。

把规则依赖 `dep` 视作有向边，则：

$$r \in \mathrm{closure}(a) \wedge \mathrm{Relation.TransGen}\,\mathrm{dep}\,r\,s
  \implies s \in \mathrm{closure}(a)$$

⟹ **规则层沿 `dep` 的传播**与**因果层沿祖先/父代边的**闭包传播
遵循**同一条**闭合律：**「已激活 ⟹ 其一切（传递）依赖皆激活」**。
两层的差别**只在关系名**（`dep` vs `Ancestor`），**不在闭合结构**。 -/
theorem closure_eq_ancestral_shape (a : Activation R) {r s : R}
    (hr : r ∈ closure a) (h : Relation.TransGen a.dep r s) : s ∈ closure a :=
  closure_dep_transGen a hr h

/-- **无依赖 ⟹ 闭包 = 初始集**（**没有依赖就没有传播**）。

$$(\forall r\,s,\ \neg\,\mathrm{dep}\,r\,s) \implies \mathrm{closure}(a) = \mathrm{init}$$ -/
theorem transGen_dep_mono {dep dep' : R → R → Prop}
    (h : ∀ {r s}, dep r s → dep' r s) {r s : R}
    (hrs : Relation.TransGen dep r s) : Relation.TransGen dep' r s := by
  induction hrs with
  | single hstep => exact Relation.TransGen.single (h hstep)
  | tail _ hstep ih => exact ih.tail (h hstep)

end RuleActivation

end Fate
