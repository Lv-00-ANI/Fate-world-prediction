import FateWorld.Legacy.LawRule
import FateWorld.Legacy.CliqueGrouping
import FateWorld.Legacy.Ancestral

/-! ===========================================================================
  `Fate/RuleReadSet` —— **规则读集与规则间依赖**（含激活闭包）

  ## 背景（作者澄清）

  世界模型里规则是 **「全参与 + 按需激活」**，**不是**从集合里挑一条。
  机制：**开始全部激活 → 数据进来部分不激活 → 但被依赖的规则立刻重新激活
  （闭包传播）**。

  规则间依赖有两个来源：

  | 来源 | 内容 |
  |---|---|
  | **(a) 由读集推出** | 规则 `r` 的读集含变量 `v`，而 `v` 由规则 `s` 确定，则 `r` 依赖 `s` |
  | **(b) 可手动添加** | `manual : ι → ι → Prop`（显式参数，不虚构任何具体内容） |

  **⟹ 这与因果层的祖先闭包（`Ancestral.AncestralSet`，即「Trunc」）同构**：
  两者都是**同一 `Relation.ReflTransGen` 闭包结构**的实例，
  本文件把这一同构证成**定理**（`ancestralSet_eq_closure`、`ancestralSet_idem_via_closure`），
  而非仅作类比。

  ## 本文件的产出

  | # | 内容 | 性质 |
  |---|---|---|
  | §1 | `ReadsAt` / `readSet` / `DeterminesAt` / `detSet` | 定义（语义，非填数） |
  | §1 | `DependsOn`（与 `CliqueGrouping.DependsOnlyOn` 同构） | 定义 |
  | §1 | `readSet_subset_of_dependsOn` | ⭐ **实质**：读集含于任一「只依赖」集 |
  | §1 | `dependsOn_mono` | 与 `dependsOnlyOn_mono` 同构 |
  | §2 | `ruleDep`：`readSet r ∩ detSet s ≠ ∅` | 定义（依赖来源 (a)） |
  | §2 | `ruleDep_imp_inter` | ⭐ **实质**：依赖必落在「只依赖」集与确定集之交 |
  | §2 | `ruleDepWith`（(a) ∪ (b)） | 定义（依赖来源 (a)+(b)） |
  | §3 | `Activation.closure` | ⭐⭐ **激活闭包**（全参与 + 按需激活） |
  | §3 | `closure_closed` / `closure_minimal` / `closure_idempotent` | ⭐⭐ 闭包三律 |
  | §3 | `reactivate` | ⭐⭐ **被依赖的规则立刻重新激活**（作者原话的定理形式） |
  | §4 | `ancestralSet_eq_closure` | ⭐⭐⭐ **与因果层 Trunc 同构** |
  | §4 | `ancestralSet_idem_via_closure` | ⭐⭐ 祖先闭包幂等性**由闭包幂等性复用得到** |

  ## 诚实边界

  1. **`Activation` 命名空间是本文件新建的** —— 全库原无 `Activation` 模块
     （已 grep 确认）。本文件不修改 `Fate.lean`、不修改任何既有文件。
  2. **`readSet` 是「单变量扰动敏感」的语义定义**：`v ∈ readSet R i` 当且仅当
     存在一对**仅在 `v` 上不同**的输入赋值使规则 `i` 输出不同。
     多变量**联合**扰动的不敏感性由 `DependsOn`（定义 §1.2）承担；
     两者关系是 `readSet_subset_of_dependsOn`（单向，且这是正确方向）。
  3. **变量空间 `V` 与取值 `A` 是参数**：本文件不指定变量是什么、有多少个
     （不填数即不虚构）。
  4. **依赖关系 (b)（手动添加）只给参数位**，不主张任何具体手工依赖成立。
  5. **零 `sorry` / 零 `admit` / 零 `axiom`**。
  =========================================================================== -/

namespace Fate

namespace RuleReadSet

/-! ===========================================================================
  §1  **规则读集**：`LawRule` 依赖哪些变量
  =========================================================================== -/

section ReadSet

variable {V A ι : Type*}

/-- **规则族**：由索引 `ι` 标号的 `LawRule` 族，
且每条规则的输入是**变量赋值** `σ : V → A`。

**为什么要把输入写成赋值**：`LawRule C X Y` 的输入是 `(c, x)`，本身不带「变量」标签；
「读哪些变量」只有在**输入被赋值族参数化**时才有意义。
本结构把「输入如何由变量决定」做成**参数** `R : (V → A) → ι → LawRule C X Y` ——
`σ` 是变量赋值，`R σ i` 是「给定赋值 `σ` 时第 `i` 条规则」。

标签：**[定义性约定]**（不填数：`V`、`A`、`ι` 全是参数）。 -/
abbrev RuleFam (V A ι : Type*) (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ :=
  (V → A) → ι → LawRule.LawRule C X Y

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
variable {R : RuleFam V A ι C X Y}

/-! ### §1.1 ⭐⭐ **读集**（单变量扰动敏感） -/

/-- ⭐⭐ **规则 `i` 在变量 `v` 上「读」**（单变量扰动敏感）。

$$\mathrm{ReadsAt}\,R\,i\,v \;:=\;
  \exists \sigma \tau,\; \sigma v \ne \tau v \wedge
  (\forall w \ne v,\; \sigma w = \tau w) \wedge R\,\sigma\,i \ne R\,\tau\,i$$

**直读**：**只动变量 `v`，规则 `i` 的输出就变了** —— 故 `i` **确实读了 `v`**。

**⚠ 这是「充分」判据**：反向不成立（一组变量的**联合**扰动可能改变输出，
而每个单变量扰动都不改变 —— 那由 `DependsOn` 承担，见 §1.2）。

标签：**[定义]**（语义定义，非填数）。 -/
def ReadsAt (R : RuleFam V A ι C X Y) (i : ι) (v : V) : Prop :=
  ∃ σ τ : V → A, σ v ≠ τ v ∧ (∀ w, w ≠ v → σ w = τ w) ∧ R σ i ≠ R τ i

/-- ⭐⭐ **规则 `i` 的读集**：它读的全部变量。

$$\mathrm{readSet}\,R\,i := \{v \mid \mathrm{ReadsAt}\,R\,i\,v\}$$

用 `Set V` 而非 `Finset V`：**不预设 `V` 有限或可判定**
（`RuleDep` 的「交非空」不需要可判定性）。 -/
def readSet (R : RuleFam V A ι C X Y) (i : ι) : Set V :=
  {v | ReadsAt R i v}

/-- 读集成员判定（定义展开）。 -/
theorem mem_readSet_iff {v : V} :
    v ∈ readSet R i ↔ ∃ σ τ : V → A,
      σ v ≠ τ v ∧ (∀ w, w ≠ v → σ w = τ w) ∧ R σ i ≠ R τ i :=
  Iff.rfl

/-! ### §1.2 ⭐⭐ **「只依赖」**（与 `CliqueGrouping.DependsOnlyOn` 同构） -/

/-- ⭐⭐ **规则 `i` 只依赖变量集 `S`**。

$$\mathrm{DependsOn}\,R\,i\,S \;:=\;
  \forall \sigma \tau,\; (\forall v \in S,\; \sigma v = \tau v) \Rightarrow R\,\sigma\,i = R\,\tau\,i$$

**⟹ 这就是 `CliqueGrouping.DependsOnlyOn S f` 的逐变量推广**：
那里 `f : (V → X) → ℝ`，这里 `R · i : (V → A) → LawRule C X Y`；
那边 `S : Finset V`，这边 `S : Set V`。**结构完全相同**。 -/
def DependsOn (R : RuleFam V A ι C X Y) (i : ι) (S : Set V) : Prop :=
  ∀ σ τ : V → A, (∀ v ∈ S, σ v = τ v) → R σ i = R τ i

/-- ⭐⭐ **`DependsOn` 对子集单调**（与 `dependsOnlyOn_mono` **同构**）。

$$S \subseteq T \Rightarrow \mathrm{DependsOn}\,R\,i\,S \Rightarrow \mathrm{DependsOn}\,R\,i\,T$$ -/
theorem dependsOn_mono {S T : Set V} (hST : S ⊆ T)
    (h : DependsOn R i S) : DependsOn R i T :=
  fun σ τ hagree => h σ τ (fun v hvT => hagree v (hST hvT))

/-- **任何规则都只依赖全集**（最弱说法；`DependsOn` 非空）。 -/
theorem dependsOn_univ (R : RuleFam V A ι C X Y) (i : ι) : DependsOn R i Set.univ := by
  intro σ τ hagree
  have hστ : σ = τ := funext fun v => hagree v (Set.mem_univ v)
  rw [hστ]

/-- ⭐⭐⭐ **读集含于任一「只依赖」集**（本节的实质定理）。

$$\mathrm{DependsOn}\,R\,i\,S \;\Longrightarrow\; \mathrm{readSet}\,R\,i \subseteq S$$

**证明**：设 `v ∈ readSet R i`，取仅在 `v` 上不同的 `σ, τ` 使 `R σ i ≠ R τ i`。
若 `v ∉ S`，则 `σ, τ` 在 `S` 上**处处一致**（它们只在 `v` 上不同），
`DependsOn` 于是给出 `R σ i = R τ i` —— 矛盾。

**⟹ 这条定理把「扰动的语义」与「`DependsOnlyOn` 式的命题」接上了**：
凡规则声称只依赖 `S`，它的读集**必须**落在 `S` 里。 -/
theorem readSet_subset_of_dependsOn {S : Set V}
    (h : DependsOn R i S) : readSet R i ⊆ S := by
  rintro v ⟨σ, τ, hne, hagree, hRne⟩
  by_contra hvS
  apply hRne
  exact h σ τ (fun w hwS => by
    rcases eq_or_ne w v with rfl | hwv
    · exact absurd hwS hvS
    · exact hagree w hwv)

/-- 读集非空时，「只依赖」集必非空（`readSet_subset_of_dependsOn` 的直接读法）。 -/
theorem dependsOn_set_nonempty_of_readsAt {S : Set V} {v : V}
    (h : DependsOn R i S) (hv : v ∈ readSet R i) : S.Nonempty :=
  ⟨v, readSet_subset_of_dependsOn h hv⟩

/-- 若规则 `i` 输出常值（对一切赋值相同），则它什么也不读（**读集为空**）。

**注意**：不敏感 ⟹ 空读集；反之**不成立**
（可能多变量联合扰动才变，单变量扰动都不变）。 -/
theorem readSet_empty_of_const (h : ∀ σ τ : V → A, R σ i = R τ i) :
    readSet R i = ∅ := by
  ext v
  constructor
  · rintro ⟨σ, τ, _, _, hRne⟩
    exact absurd (h σ τ) hRne
  · intro hv; exact absurd hv (Set.notMem_empty v)

/-! ### §1.3 ⭐⭐ **确定集**（规则 `i` 能确定哪些变量） -/

/-- ⭐⭐ **规则 `i` 确定变量 `v`**：`i` 的输出相同 ⟹ 两赋值在 `v` 上相同。

$$\mathrm{DeterminesAt}\,R\,i\,v \;:=\;
  \forall \sigma \tau,\; R\,\sigma\,i = R\,\tau\,i \Rightarrow \sigma v = \tau v$$

**⟹ 这是「读集」的**对偶**：读集说「动 `v` 则输出变」，
确定集说「输出同则 `v` 同」。** -/
def DeterminesAt (R : RuleFam V A ι C X Y) (i : ι) (v : V) : Prop :=
  ∀ σ τ : V → A, R σ i = R τ i → σ v = τ v

/-- ⭐⭐ **规则 `i` 的确定集**：它能确定的全部变量。 -/
def detSet (R : RuleFam V A ι C X Y) (i : ι) : Set V :=
  {v | DeterminesAt R i v}

/-- 确定集成员判定（定义展开）。 -/
theorem mem_detSet_iff {v : V} :
    v ∈ detSet R i ↔ ∀ σ τ : V → A, R σ i = R τ i → σ v = τ v :=
  Iff.rfl

/-- ⭐⭐ **若规则族在 `i` 处「分离赋值」，则 `i` 确定一切变量**。

「分离」：`R · i` 单射（不同赋值 ⟹ 不同规则集）。
此时 `R σ i = R τ i` 迫使 `σ = τ`，故每个变量都被确定。 -/
theorem determinesAt_of_separates
    (hsep : ∀ σ τ : V → A, R σ i = R τ i → σ = τ) : DeterminesAt R i v :=
  fun σ τ heq => by rw [hsep σ τ heq]

/-- 推论：**分离 ⟹ 确定集 = 全集**。 -/
theorem detSet_eq_univ_of_separates
    (hsep : ∀ σ τ : V → A, R σ i = R τ i → σ = τ) : detSet R i = Set.univ := by
  ext v
  exact ⟨fun _ => Set.mem_univ v, fun _ => determinesAt_of_separates hsep⟩

end ReadSet

/-! ===========================================================================
  §2  **规则间依赖**：`ruleDep r s := readSet r ∩ detSet s ≠ ∅`
  =========================================================================== -/

section RuleDep

variable {V A ι : Type*}
variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
variable {R : RuleFam V A ι C X Y}

/-- ⭐⭐⭐ **规则间依赖（来源 (a)：由读集推出）**。

$$\mathrm{ruleDep}\,R\,r\,s \;:=\;
  \exists v,\; v \in \mathrm{readSet}\,R\,r \wedge v \in \mathrm{detSet}\,R\,s$$

即 **`readSet r ∩ detSet s ≠ ∅`**：规则 `r` **读**某个变量 `v`，
而该变量**由**规则 `s` **确定** ⟹ **`r` 依赖 `s`**。

**⟹ 这正是作者所述依赖来源 (a)。** -/
def ruleDep (R : RuleFam V A ι C X Y) (r s : ι) : Prop :=
  (readSet R r ∩ detSet R s).Nonempty

/-- 依赖的「存在变量」形式（与 `∩` 非空等价）。 -/
theorem ruleDep_iff {r s : ι} :
    ruleDep R r s ↔ ∃ v, ReadsAt R r v ∧ DeterminesAt R s v :=
  Iff.rfl

/-- 依赖的「交非空」形式（题目要求的 `≠ ∅` 写法）。 -/
theorem ruleDep_iff_ne_empty {r s : ι} :
    ruleDep R r s ↔ readSet R r ∩ detSet R s ≠ ∅ :=
  Set.nonempty_iff_ne_empty

/-- ⭐ **确定集变大 ⟹ 依赖变多**（依赖对确定集单调）。 -/
theorem ruleDep_mono_det {r s s' : ι} (h : detSet R s ⊆ detSet R s') :
    ruleDep R r s → ruleDep R r s' :=
  fun ⟨v, hr, hs⟩ => ⟨v, hr, h hs⟩

/-- ⭐ **读集变大 ⟹ 依赖变多**（依赖对读集单调）。 -/
theorem ruleDep_mono_read {r r' s : ι} (h : readSet R r ⊆ readSet R r') :
    ruleDep R r s → ruleDep R r' s :=
  fun ⟨v, hr, hs⟩ => ⟨v, h hr, hs⟩

/-- ⭐⭐⭐ **依赖必落在「只依赖」集与确定集之交**（关键实质引理）。

若规则 `r` **只依赖** `S`（`DependsOn R r S`），且 `r` 依赖 `s`，
则 `S ∩ detSet s` **非空**：

$$\mathrm{DependsOn}\,R\,r\,S \Rightarrow \mathrm{ruleDep}\,R\,r\,s
  \Rightarrow (S \cap \mathrm{detSet}\,R\,s).\mathrm{Nonempty}$$

**证明**：依赖给见证 `v ∈ readSet r ∩ detSet s`；由 `readSet_subset_of_dependsOn`
得 `v ∈ S`。**⟹ 这是 §1 与 §2 的接口：读集是「隐藏的实际读变量」，
`DependsOn` 给的 `S` 是「声明的依赖范围」，两者由包含关系相容。** -/
theorem ruleDep_imp_inter {r s : ι} {S : Set V}
    (hdep : DependsOn R r S) (hd : ruleDep R r s) :
    (S ∩ detSet R s).Nonempty :=
  hd.imp fun _ hv => ⟨readSet_subset_of_dependsOn hdep hv.1, hv.2⟩

/-- ⭐⭐ **规则间依赖（来源 (a) ∪ 来源 (b)）**。

`manual` 是**显式参数**：手工添加的依赖对。
本文件**不填充**任何手工依赖（不虚构），只把它作为可接入的位。 -/
def ruleDepWith (R : RuleFam V A ι C X Y) (manual : ι → ι → Prop) (r s : ι) : Prop :=
  ruleDep R r s ∨ manual r s

/-- 由读集推出的依赖**含于**「读集 + 手工」依赖（来源 (a) ⊆ (a)∪(b)）。 -/
theorem ruleDep_subset_ruleDepWith (manual : ι → ι → Prop) {r s : ι} :
    ruleDep R r s → ruleDepWith R manual r s :=
  Or.inl

end RuleDep

/-! ===========================================================================
  §3  **激活闭包**：`Activation.closure`

  作者原话：「**开始全部激活 → 数据进来部分不激活 → 但被依赖的规则立刻重新激活
  （闭包传播）**」。

  ⚠ **诚实标注**：全库原无 `Activation` 模块，本命名空间为**本文件新建**。
  `closure` 对**任意**依赖关系 `dep : ι → ι → Prop` 定义 ——
  故它同时覆盖来源 (a)、来源 (b) 与二者之并。
  =========================================================================== -/

namespace Activation

variable {ι : Type*}

/-- ⭐⭐⭐ **激活闭包**：从「仍被数据支持（已激活）的规则集 `I`」出发，
沿依赖方向 `dep` **传播重激活**。

$$\mathrm{closure}\,dep\,I \;:=\;
  \{s \mid \exists r \in I,\; r \xrightarrow{dep*} s\}$$

**语义**：`dep r s` 读作「`r` 依赖 `s`」。若 `r` 仍激活，而 `r` 依赖 `s`，
则 `s` **必须重新激活**（「被依赖的规则立刻重新激活」）。
故最终激活集 = 从 `I` 沿 `dep` **前进**可达的一切规则。 -/
def closure (dep : ι → ι → Prop) (I : Set ι) : Set ι :=
  {s | ∃ r ∈ I, Relation.ReflTransGen dep r s}

/-- ⭐⭐ **闭包扩张**：`I ⊆ closure dep I`（每条形如「自己依赖自己」的 0 步传播）。 -/
theorem closure_extensive (dep : ι → ι → Prop) (I : Set ι) : I ⊆ closure dep I :=
  fun r hr => ⟨r, hr, Relation.ReflTransGen.refl⟩

/-- ⭐⭐⭐ **闭包对依赖封闭**（**「被依赖的规则立刻重新激活」的定理形式**）。

$$r \in \mathrm{closure}\,dep\,I \;\wedge\; dep\,r\,s
  \;\Longrightarrow\; s \in \mathrm{closure}\,dep\,I$$ -/
theorem closure_closed (dep : ι → ι → Prop) {I : Set ι} {r s : ι}
    (hr : r ∈ closure dep I) (h : dep r s) : s ∈ closure dep I := by
  obtain ⟨r₀, hr₀, hrt⟩ := hr
  exact ⟨r₀, hr₀, Relation.ReflTransGen.tail hrt h⟩

/-- 简称：`reactivate` —— **被依赖的规则重激活**（作者原话的定理形态）。 -/
theorem reactivate (dep : ι → ι → Prop) {I : Set ι} {r s : ι}
    (hr : r ∈ closure dep I) (h : dep r s) : s ∈ closure dep I :=
  closure_closed dep hr h

/-- 已知 `I` 中的规则沿依赖链可达 ⟹ 在闭包中。 -/
theorem mem_closure_of_reflTransGen (dep : ι → ι → Prop) {I : Set ι} {r s : ι}
    (hr : r ∈ I) (h : Relation.ReflTransGen dep r s) : s ∈ closure dep I :=
  ⟨r, hr, h⟩

/-- ⭐⭐ **两步传播**（依赖链 `r → s → t` 只用一次传播即得 `t` 激活）。 -/
theorem mem_closure_of_chain (dep : ι → ι → Prop) {I : Set ι} {r s t : ι}
    (hr : r ∈ I) (h₁ : dep r s) (h₂ : dep s t) : t ∈ closure dep I :=
  ⟨r, hr, Relation.ReflTransGen.tail (Relation.ReflTransGen.single h₁) h₂⟩

/-- ⭐⭐⭐ **闭包最小性**：闭包是**包含 `I` 且对 `dep` 封闭的最小集合**。

$$\Big(I \subseteq S \;\wedge\; \forall r \in S,\ \forall s,\ dep\,r\,s \to s \in S\Big)
  \;\Longrightarrow\; \mathrm{closure}\,dep\,I \subseteq S$$

**⟹ 这条定理给「最终激活集」一个**唯一刻画**：
任何合法（对依赖封闭）的激活集都包含闭包，而闭包本身合法（`closure_closed`）——
故 **合法激活集 ⊆ 闭包 且 闭包 ⊆ 合法激活集** 的最小者是闭包。 -/
theorem closure_minimal (dep : ι → ι → Prop) {I S : Set ι}
    (hI : I ⊆ S) (hS : ∀ a ∈ S, ∀ b, dep a b → b ∈ S) :
    closure dep I ⊆ S := by
  rintro s ⟨r, hr, hrt⟩
  have key : ∀ t, Relation.ReflTransGen dep r t → t ∈ S := by
    intro t hrt'
    induction hrt' with
    | refl => exact hI hr
    | tail _ hstep ih => exact hS _ ih _ hstep
  exact key s hrt

/-- ⭐⭐ **闭包单调**（`I ⊆ J ⟹ closure I ⊆ closure J`）。 -/
theorem closure_mono_I (dep : ι → ι → Prop) {I J : Set ι} (h : I ⊆ J) :
    closure dep I ⊆ closure dep J :=
  fun _ ⟨r, hr, hrt⟩ => ⟨r, h hr, hrt⟩

/-- ⭐⭐ **闭包幂等**：`closure (closure I) = closure I`（**闭包算子的核心性质**）。 -/
theorem closure_idempotent (dep : ι → ι → Prop) (I : Set ι) :
    closure dep (closure dep I) = closure dep I := by
  apply Set.Subset.antisymm
  · rintro s ⟨r, ⟨r₀, hr₀, h₁⟩, h₂⟩
    exact ⟨r₀, hr₀, Relation.ReflTransGen.trans h₁ h₂⟩
  · exact closure_mono_I dep (closure_extensive dep I)

/-- **全激活态**：若初始激活集为全集，则闭包仍是全集。

「开始全部激活」的语义：`I = univ` 时任何传播都不会缩小激活集。 -/
theorem closure_univ (dep : ι → ι → Prop) :
    closure dep (Set.univ : Set ι) = Set.univ := by
  apply Set.Subset.antisymm
  · intro s _; exact Set.mem_univ s
  · intro s _; exact ⟨s, Set.mem_univ s, Relation.ReflTransGen.refl⟩

/-- ⭐⭐ **固定点刻画**：若 `I` 已对 `dep` 封闭，则 `closure I = I`。

**⟹ 这是「数据停用 + 重激活」达到稳定态的条件：
稳定态就是「对依赖封闭的激活集」。** -/
theorem closure_eq_self_of_closed (dep : ι → ι → Prop) {I : Set ι}
    (h : ∀ a ∈ I, ∀ b, dep a b → b ∈ I) : closure dep I = I := by
  apply Set.Subset.antisymm
  · exact closure_minimal dep (Set.Subset.refl I) h
  · exact closure_extensive dep I

/-- ⭐⭐ **激活集的结构**：最终激活集 = 一些依赖链的并集。

若 `S` 是任一「包含 `I` 且对 `dep` 封闭」的集合，则 `closure I` 与 `S` 的
关系是：闭包最小、`S` 是任一合法候选。此处给出**链表示**：
每个闭包成员都有一条从 `I` 出发的显式依赖链。 -/
theorem closure_member_has_chain (dep : ι → ι → Prop) {I : Set ι} {s : ι}
    (hs : s ∈ closure dep I) :
    ∃ r ∈ I, Relation.ReflTransGen dep r s := hs

/-- 来源 **(a)∪(b)** 的闭包**包含**来源 **(a)** 的闭包（`manual` 只会加依赖）。 -/
theorem closure_mono_dep {dep dep' : ι → ι → Prop}
    (h : ∀ {a b : ι}, dep a b → dep' a b) {I : Set ι} :
    closure dep I ⊆ closure dep' I := by
  rintro s ⟨r, hr, hrt⟩
  have key : ∀ t, Relation.ReflTransGen dep r t → Relation.ReflTransGen dep' r t := by
    intro t hrt'
    induction hrt' with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (h hstep)
  exact ⟨r, hr, key s hrt⟩

end Activation

/-! ### §3.1 规则层实例：`ruleDep` 的激活闭包 -/

section ActivationRuleDep

variable {V A ι : Type*}
variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
variable {R : RuleFam V A ι C X Y}

/-- 规则层的激活闭包（由读集推出的依赖）。 -/
abbrev ruleActivation (R : RuleFam V A ι C X Y) (I : Set ι) : Set ι :=
  Activation.closure (ruleDep R) I

/-- 规则层的激活闭包（读集依赖 + 手工依赖）。 -/
abbrev ruleActivationWith (R : RuleFam V A ι C X Y) (manual : ι → ι → Prop)
    (I : Set ι) : Set ι :=
  Activation.closure (ruleDepWith R manual) I

/-- ⭐⭐ **(a) 的激活闭包含于 (a)∪(b) 的激活闭包**：
手工添加依赖只会让更多规则被重激活。 -/
theorem ruleActivation_subset_with (manual : ι → ι → Prop) (I : Set ι) :
    ruleActivation R I ⊆ ruleActivationWith R manual I :=
  Activation.closure_mono_dep (fun h => Or.inl h)

/-- ⭐⭐⭐ **规则层的「重激活」定理**：
若 `r` 在激活闭包中且 `r` 依赖 `s`（`r` 读的某变量由 `s` 确定），
则 `s` 也在激活闭包中。 -/
theorem rule_reactivate {I : Set ι} {r s : ι}
    (hr : ruleActivation R I r)
    (hdep : ∃ v, ReadsAt R r v ∧ DeterminesAt R s v) :
    ruleActivation R I s :=
  Activation.reactivate (ruleDep R) hr hdep

/-- ⭐⭐ **规则层的闭包最小性**：任何「对 `ruleDep` 封闭」的规则集都包含激活闭包。 -/
theorem ruleActivation_minimal {I S : Set ι}
    (hI : I ⊆ S) (hS : ∀ a ∈ S, ∀ b, ruleDep R a b → b ∈ S) :
    ruleActivation R I ⊆ S :=
  Activation.closure_minimal (ruleDep R) hI hS

end ActivationRuleDep

/-! ===========================================================================
  §4  **与因果层祖先闭包（Trunc）同构**

  `Ancestral.AncestralSet G S` = `S` 及其**全体祖先**，用 `Ancestor G v s`
  （`v` 是 `s` 的祖先）定义。它与 §3 的 `Activation.closure` **是同一结构的两个方向**：

  $$\mathrm{AncestralSet}\,G\,S \;=\;
    \mathrm{closure}\,\big(\lambda x\,y.\ \mathrm{Ancestor}\,G\,y\,x\big)\,S$$

  即：把 `dep` 取作「反向祖先关系」，激活闭包**恰是**祖先闭包。
  **⟹ 「规则层依赖传播」与「因果层 Trunc」同构 —— 本节证成。**
  =========================================================================== -/

section AncestralIso

open CausalDirection (CausalGraph)

/-- ⭐⭐ **可达 ⟹ 反向传递闭包**（`Reach` 到 `ReflTransGen` 的翻译）。

若 `b` 是 `a` 的后代（`Reach G a b`），则**反向关系**上 `a` 由 `b` 可达。 -/
theorem reach_imp_reflTransGen_rev {G : CausalGraph V} {a b : V}
    (h : CausalDescendant.Reach G a b) :
    Relation.ReflTransGen (fun x y => Ancestral.Ancestor G y x) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | step hadj _ ih =>
      exact Relation.ReflTransGen.tail ih
        (CausalDescendant.Reach.step hadj (CausalDescendant.Reach.refl _))

/-- ⭐⭐ **反向传递闭包 ⟹ 祖先集合成员**（`ReflTransGen` 回流到 `AncestralSet`）。 -/
theorem mem_ancestralSet_of_reflTransGen_rev {G : CausalGraph V} {S : Set V} {r s : V}
    (hr : r ∈ S)
    (h : Relation.ReflTransGen (fun x y => Ancestral.Ancestor G y x) r s) :
    s ∈ Ancestral.AncestralSet G S := by
  have key : ∀ t, Relation.ReflTransGen (fun x y => Ancestral.Ancestor G y x) r t →
      t ∈ Ancestral.AncestralSet G S := by
    intro t hrt
    induction hrt with
    | refl => exact Ancestral.subset_ancestralSet G S hr
    | tail _ hstep ih => exact Ancestral.ancestor_mem_ancestralSet G ih hstep
  exact key s h

/-- ⭐⭐⭐ **主定理：祖先闭包 = 激活闭包**（**与因果层 Trunc 的同构**）。

$$\mathrm{AncestralSet}\,G\,S \;=\;
  \mathrm{Activation.closure}\,(\lambda x\,y.\ \mathrm{Ancestor}\,G\,y\,x)\,S$$

**⟹ 规则层的「按需激活」与因果层的「祖先闭包」不是类比，而是同一个闭包算子**：
只需把依赖关系取作「反向祖先关系」即可。 -/
theorem ancestralSet_eq_closure (G : CausalGraph V) (S : Set V) :
    Ancestral.AncestralSet G S =
      Activation.closure (fun x y => Ancestral.Ancestor G y x) S := by
  ext v
  constructor
  · rintro (hv | ⟨s, hs, hvs⟩)
    · exact ⟨v, hv, Relation.ReflTransGen.refl⟩
    · exact ⟨s, hs, reach_imp_reflTransGen_rev hvs⟩
  · rintro ⟨r, hr, hrt⟩
    exact mem_ancestralSet_of_reflTransGen_rev hr hrt

/-- ⭐⭐ **祖先闭包幂等性由激活闭包幂等性复用得到**（同构的实际收益）。

`Ancestral.ancestralSet_idem` 在原文件里是**单独归纳证明**的；
这里它作为 `Activation.closure_idempotent` 的**推论**出现 ——
两个层的闭包律是**同一条**。 -/
theorem ancestralSet_idem_via_closure (G : CausalGraph V) (S : Set V) :
    Ancestral.AncestralSet G (Ancestral.AncestralSet G S) =
      Ancestral.AncestralSet G S := by
  calc Ancestral.AncestralSet G (Ancestral.AncestralSet G S)
      = Activation.closure (fun x y => Ancestral.Ancestor G y x)
          (Ancestral.AncestralSet G S) := ancestralSet_eq_closure G _
    _ = Activation.closure (fun x y => Ancestral.Ancestor G y x)
          (Activation.closure (fun x y => Ancestral.Ancestor G y x) S) :=
        congrArg (Activation.closure (fun x y => Ancestral.Ancestor G y x))
          (ancestralSet_eq_closure G S)
    _ = Activation.closure (fun x y => Ancestral.Ancestor G y x) S :=
        Activation.closure_idempotent _ S
    _ = Ancestral.AncestralSet G S := (ancestralSet_eq_closure G S).symm

/-- ⭐⭐ **祖先闭包扩张性由激活闭包扩张性复用得到**。 -/
theorem subset_ancestralSet_via_closure (G : CausalGraph V) (S : Set V) :
    S ⊆ Ancestral.AncestralSet G S := by
  intro v hv
  exact (congrArg (fun T => v ∈ T) (ancestralSet_eq_closure G S)).mpr
    (Activation.closure_extensive (fun x y => Ancestral.Ancestor G y x) S hv)

/-- ⭐⭐ **祖先闭包最小性由激活闭包最小性复用得到**。 -/
theorem ancestralSet_minimal_via_closure (G : CausalGraph V) {S T : Set V}
    (hST : S ⊆ T)
    (hT : ∀ a ∈ T, ∀ b, Ancestral.Ancestor G b a → b ∈ T) :
    Ancestral.AncestralSet G S ⊆ T := by
  intro v hv
  exact Activation.closure_minimal (fun x y => Ancestral.Ancestor G y x) hST hT
    ((congrArg (fun T => v ∈ T) (ancestralSet_eq_closure G S)).mp hv)

end AncestralIso

/-! ===========================================================================
  §5  **诚实边界**
  =========================================================================== -/

/-
**本文件完成了什么**

| # | 内容 | 状态 |
|---|---|---|
| 1 | 给 `LawRule` 定义读集 `readSet`（语义扰动的单变量形式） | 定义 + 判定引理 |
| 2 | 「只依赖」`DependsOn`（与 `CliqueGrouping.DependsOnlyOn` 同构） | 定义 + 单调性 |
| 3 | `readSet ⊆ S`（只要规则只依赖 `S`） | **实质定理** |
| 4 | 规则间依赖 `ruleDep r s := readSet r ∩ detSet s ≠ ∅` | 定义 + 单调性 |
| 5 | 依赖必落在 `S ∩ detSet s`（§1 与 §2 的接口） | **实质定理** |
| 6 | 依赖来源 (b)：`ruleDepWith`（读集依赖 ∪ 手工依赖） | 定义（参数位，不填数） |
| 7 | 激活闭包 `Activation.closure` | 定义 |
| 8 | 闭包扩张 / 封闭 / 最小 / 幂等 / 单调 | **全部证明** |
| 9 | 「被依赖的规则立刻重新激活」= `reactivate` | **定理** |
| 10 | 与因果层祖先闭包同构（`ancestralSet_eq_closure`） | **主定理** |
| 11 | 祖先闭包的幂等性由激活闭包幂等性**复用**得到 | **定理** |

**本文件没有完成什么（诚实标注）**

1. **`Activation` 是本文件新建的命名空间**：全库原无 `Activation` 模块。
   若后续另有 `Activation.closure` 定义，需要与本文件的 `closure` 对齐
   （本文件的定义是最一般的 `dep : ι → ι → Prop` 形式）。
2. **`readSet` 只是「单变量扰动敏感」**：多变量联合扰动的不敏感性由
   `DependsOn` 承担。**「不敏感 ⟺ 空读集」不成立**（只有 ⟸ 成立：
   `readSet_empty_of_const`）。这是有意的诚实标注 —— 若不预设变量的有限性与
   可判定性，联合扰动无法从单变量扰动合成。
3. **`V` 的有限性、可判定性未被使用**：本文件全用 `Set V`，
   故 `ruleDep` 的「交非空」不需要任何可判定假设。
4. **依赖来源 (b)（手动添加）只给参数位** `manual`，
   **不主张**任何具体手工依赖成立（不虚构）。
5. **未触及**：规则的**时间演化**（`Step` / `trajGen`）、
   激活集与 `LawRule.compose` 的交互、读集在**具体实例**上的取值。
-/

end RuleReadSet

end Fate
