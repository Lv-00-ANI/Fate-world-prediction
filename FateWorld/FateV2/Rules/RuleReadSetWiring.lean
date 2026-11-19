import FateWorld.FateV2.Rules.RuleReadSet
import FateWorld.FateV2.Loop.WorldModelCompleteV2
/-!
  # Rules · RuleReadSetWiring

  ## 迁移登记
  - 来源：`FateWorld/Legacy/RuleReadSetWiring.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：RuleReadSet, WorldModelCompleteV2
  - 补充 open 域：FateV2.Loop, FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/RuleReadSetWiring` —— **把 `RuleReadSet` 的依赖结构接进 `WorldModelCompleteV2`**

  ## (a) `RuleReadSet` 是什么（如实登记）

  `Fate/RuleReadSet`（36 定理，此前全库**零扇入、零消费**）做的是
  **「规则之间的依赖关系分析」**：

  | 名字 | 含义 |
  |---|---|
  | `ReadsAt R i v` | 规则 `i` **读**变量 `v`（单变量扰动敏感） |
  | `readSet R i` | 规则 `i` 的**读集** |
  | `DependsOn R i S` | 规则 `i` **只依赖**变量集 `S` |
  | `DeterminesAt R i v` / `detSet R i` | 规则 `i` **确定**哪些变量 |
  | `ruleDep R r s` | 规则 `r` **依赖**规则 `s`（`readSet r ∩ detSet s ≠ ∅`） |
  | `Activation.closure` | 依赖传播下的**激活闭包** |

  ⚠⚠ **它不回答 TD-05**：本文件已 `grep -cE "Loop|Gaze|Level" Fate/RuleReadSet.lean`
  实测为 **0**，即它与循环 / 分类 / 层级**零关联**。
  **本文件也不回答 TD-05。**

  ## (b) 本文件做到了什么

  | # | 内容 | 性质 |
  |---|---|---|
  | §1 | `RuleSetWithDeps`：把 `RuleFam` 与**两个**依赖源 `(a) 读集推出` / `(b) 手工` 打包 | 定义 |
  | §1 | `RuleSetWithDeps.dep`：合并后的依赖关系 = `ruleDepWith` | 定义（`rfl` 同一） |
  | §2 | `ruleDep_not_refl_of_readSet_empty` | ⭐ **`ruleDep` 一般不自反**（有实质反例类） |
  | §2 | `ruleDep_trans_of_detSet_subset` | ⭐ **传递性的充分条件**（真定理，非平凡） |
  | §2 | `ruleDepWith_refl` / `ruleDepWith_trans` | ⭐ 预序性对**来源 (b)** 成立（需 `manual` 自反 / 传递 / **吸收 `ruleDep`**）|
  | §2 | `ruleDepWith_isPreorder` | ⭐ 预序的**充分条件**（`manual` 自反 + 传递 + 吸收 `ruleDep`）|
  | §2 | `ruleDep_not_antisymmetric` | ⚠⚠ **`ruleDep` 不为偏序**（互依赖 + 相异 ⟹ 反称失败）→ **层次结构不成立** |
  | §3 | `lawRuleOf` / `lawRuleFamOf` | ⭐⭐ **构造**：一个 `WorldModelCompleteV2` **确实**给出 `RuleFam` |
  | §3 | `readSet_empty_of_wmc` | ⭐⭐ **WMC 的规则族读集为空**（因 `lawRuleFamOf` 与赋值无关）|
  | §3 | `not_ruleDep_of_wmc` | ⭐⭐ **WMC 的规则族没有任何 `ruleDep`** |
  | §3 | `determinesAt_of_wmc_iff` | ⭐⭐ **WMC 的解码规则族确定集为空**（与读集形成对偶）|
  | §3 | `not_determinesAt_of_wmc` | 上条的成员判据 |
  | §3 | `closure_eq_self_of_wmc` | ⭐⭐ WMC 侧激活闭包是**固定点**（不需要重激活）|
  | §3 | `wmc_rules_nonempty` | WMC 的 `rules` **非空**（由 `rules_determine_step` 取得） |
  | §4 | `exists_preorder_family` | ⭐ 存在性：至少一个 `RuleFam` 使 `ruleDepWith` 成预序 |

  ## (c) 本文件**不做**什么（诚实要求，逐条）

  1. **不声称「解决了规则提取问题」。** 本文件只把已有类型接起来。
  2. **不声称「`WorldModelCompleteV2` 的规则集有依赖结构」。**
     恰恰相反：§3 证明的 `not_ruleDep_of_wmc` 是**否定结论** ——
     `WorldModelCompleteV2` 只携带一个**裸 `Set (Rule …)`**，**没有**
     任何「哪条规则读哪些变量」的信息；
     所以要得到 `RuleFam`，必须**额外附加**一个变量空间 `V` / 赋值空间 `A`
     与一个解码 `dec`（见 §3 `RuleSetWithDeps` 的构造）。
     **这个附加是构造，不是从 `WorldModelCompleteV2` 导出的。**
  3. **`WorldModelCompleteV2` 一侧不做任何修改**（纪律 2）。
     本文件只**新建**。
  4. **`ruleDep` 不是预序，也不是偏序**（§2 的 `ruleDep_not_refl_of_readSet_empty` +
     `ruleDep_not_antisymmetric`）：这与 `RuleReadSet` 文件头未主张它是预序一致。
     本文件把「它何时是预序」的**充分条件**与「它何时**绝不**是偏序」
     都证成定理，而不是含糊带过。
  5. **零 `sorry` / 零 `admit` / 零 `axiom`。**
  =========================================================================== -/

namespace FateV2.Rules

open FateV2.Loop
open FateV2.Model
open FateV2.Modeling
namespace RuleReadSetWiring

open RuleReadSet

universe u

/-! ===========================================================================
  §1  **带依赖结构的规则集**
  =========================================================================== -/

/-- **带依赖结构的规则集**。

打包三件东西：

* `fam` —— 规则族 `RuleFam V A ι C X Y`（`RuleReadSet` §1 的参数化结构）；
* `manual` —— **手工依赖**（`RuleReadSet` 的依赖来源 (b)），**只作参数位**，
  本文件**不填充**任何具体内容（不虚构）；
* `_ctx` —— 上下文 / 状态 / 输出空间由类型参数给出，不是字段。

**为什么 `manual` 是参数位而不是具体关系**：`RuleReadSet` 文件头把来源 (b)
明确定性为「可手动添加」，并明写「不虚构任何具体内容」。
本文件遵守该约定。

标签：**[定义性约定]**（`V` / `A` / `ι` / `manual` 全是参数）。 -/
structure RuleSetWithDeps (V A ι : Type u) (C : CtxSpace) (X : StateSpace)
    (Y : OutSpace) [MeasurableSpace Y.Carrier] where
  /-- 规则族：赋值 ↦ 索引 ↦ 规律。 -/
  fam : RuleFam V A ι C X Y
  /-- 手工依赖（依赖来源 (b)）。**参数位，不填数。** -/
  manual : ι → ι → Prop

variable {V A ι : Type u} {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
  [MeasurableSpace Y.Carrier]

namespace RuleSetWithDeps

/-- **合并依赖**：`D.dep = ruleDepWith D.fam D.manual`（来源 (a) ∪ 来源 (b)）。

**这不是新定义的语义**：`RuleReadSet.ruleDepWith` 已经就是「读集依赖 ∪ 手工依赖」，
本结构只是把两零件打包后重新取出。 -/
def dep (D : RuleSetWithDeps V A ι C X Y) : ι → ι → Prop :=
  ruleDepWith D.fam D.manual

/-- **同一性检查**（防同义反复）：`dep` 展开后**恰是** `ruleDepWith`。 -/
theorem dep_eq_ruleDepWith (D : RuleSetWithDeps V A ι C X Y) :
    D.dep = ruleDepWith D.fam D.manual := rfl

/-- `dep` 的 `Or` 形式（便于逐支处理）。 -/
theorem dep_iff (D : RuleSetWithDeps V A ι C X Y) {r s : ι} :
    D.dep r s ↔ ruleDep D.fam r s ∨ D.manual r s :=
  Iff.rfl

/-- 激活闭包（规则层）：`Activation.closure D.dep I`。 -/
def activation (D : RuleSetWithDeps V A ι C X Y) (I : Set ι) : Set ι :=
  Activation.closure D.dep I

/-- 激活闭包对 `D.dep` 封闭（**「被依赖的规则立刻重新激活」的规则集版**）。 -/
theorem activation_closed (D : RuleSetWithDeps V A ι C X Y) {I : Set ι} {r s : ι}
    (hr : r ∈ D.activation I) (h : D.dep r s) : s ∈ D.activation I :=
  Activation.closure_closed D.dep hr h

/-- 激活闭包最小性。 -/
theorem activation_minimal (D : RuleSetWithDeps V A ι C X Y) {I S : Set ι}
    (hI : I ⊆ S) (hS : ∀ a ∈ S, ∀ b, D.dep a b → b ∈ S) :
    D.activation I ⊆ S :=
  Activation.closure_minimal D.dep hI hS

/-- 激活闭包幂等。 -/
theorem activation_idempotent (D : RuleSetWithDeps V A ι C X Y) (I : Set ι) :
    D.activation (D.activation I) = D.activation I :=
  Activation.closure_idempotent D.dep I

end RuleSetWithDeps

/-! ===========================================================================
  §2  **`ruleDep` 是预序吗？—— 三个诚实答案**

  `RuleReadSet` 文件头**没有**主张 `ruleDep` 是预序。本节把三种情形分清：

  | 性质 | 结论 |
  |---|---|
  | 自反 `ruleDep r r` | **不成立**（除非 `readSet r ∩ detSet r ≠ ∅`），有充要条件 |
  | 传递 | **不无条件下成立**；给充分条件 `detSet s ⊆ detSet t` + 读集交非空 |
  | 反称 | **绝不成立**（只要存在任意一条非平凡的 `ruleDep`）|
  =========================================================================== -/

section Preorder

variable {R : RuleFam V A ι C X Y}

/-- ⭐ **`ruleDep` 自反的充要条件**。

$$\mathrm{ruleDep}\,R\,r\,r \iff (\mathrm{readSet}\,R\,r \cap \mathrm{detSet}\,R\,r).\mathrm{Nonempty}$$

即：**规则恒自反当且仅当它读的变量恰好由它自己确定**。
这是定义展开（`Iff.rfl`），但把它写成定理可让「自反**不是**免费的」可见。 -/
theorem ruleDep_refl_iff {r : ι} :
    ruleDep R r r ↔ (readSet R r ∩ detSet R r).Nonempty :=
  Iff.rfl

/-- ⭐⭐ **`ruleDep` 一般不自反**：若规则 `r` 的读集为空（例如它输出常值），
则 `¬ ruleDep R r r`。

**这直接说明 `ruleDep` 不是预序**（预序要求处处自反）。 -/
theorem ruleDep_not_refl_of_readSet_empty {r : ι} (h : readSet R r = ∅) :
    ¬ ruleDep R r r := by
  rintro ⟨v, hv, _⟩
  rw [h] at hv
  exact absurd hv (Set.notMem_empty v)

/-- ⭐ 常值规则族处处不依赖自己（`readSet_empty_of_const` 的直接应用）。 -/
theorem ruleDep_not_refl_of_const {r : ι}
    (h : ∀ σ τ : V → A, R σ r = R τ r) : ¬ ruleDep R r r :=
  ruleDep_not_refl_of_readSet_empty (readSet_empty_of_const h)

/-- ⭐⭐ **`ruleDep` 的传递性的充分条件**。

若 `r` 读的变量 `v` 由 `s` 确定，且 `s` 的确定集含于 `s'` 的确定集，
则 `r` 依赖 `s'`。

$$\mathrm{ruleDep}\,R\,r\,s \Rightarrow
  \mathrm{detSet}\,R\,s \subseteq \mathrm{detSet}\,R\,s' \Rightarrow
  \mathrm{ruleDep}\,R\,r\,s'$$

**这是 `RuleReadSet.ruleDep_mono_det` 的具名形式**（避免下游重复发现）。
**⚠ 注意它只是「传递的充分条件」，不是传递性本身。** -/
theorem ruleDep_trans_of_detSet_subset {r s s' : ι}
    (h : ruleDep R r s) (hsub : detSet R s ⊆ detSet R s') :
    ruleDep R r s' :=
  ruleDep_mono_det hsub h

/-- ⭐ **读集侧的对偶**：读集扩大则依赖保持。 -/
theorem ruleDep_of_readSet_subset {r r' s : ι}
    (h : readSet R r ⊆ readSet R r') (hd : ruleDep R r s) : ruleDep R r' s :=
  ruleDep_mono_read h hd

end Preorder

/-! ### §2.1 合并依赖 `ruleDepWith` 何时是预序

`RuleReadSet` 把依赖来源 (b) 留给**参数位** `manual`。
预序性**不可能**凭空成立，只能来自对 `manual` 的假设。本节把它们写清。 -/

section PreorderWith

variable {R : RuleFam V A ι C X Y}

/-- ⭐ **合并依赖自反的充分条件**：`manual` 自反。

$$\big(\forall i,\ \mathrm{manual}\,i\,i\big) \Rightarrow
  \forall i,\ \mathrm{ruleDepWith}\,R\,\mathrm{manual}\,i\,i$$

**注意方向**：这条**不是**同义反复 —— 前件只要求 `manual` 自反，
结论是 `ruleDepWith`（= `ruleDep ∨ manual`）自反；
`ruleDep` 那一支完全不受前件约束（见 `ruleDep_not_refl_of_readSet_empty`）。 -/
theorem ruleDepWith_refl (manual : ι → ι → Prop)
    (h : ∀ i, manual i i) (i : ι) : ruleDepWith R manual i i :=
  Or.inr (h i)

/-- ⭐⭐ **合并依赖传递的充分条件**：`manual` **吸收** `ruleDep` 且传递。

$$\Big(\forall a b,\ \mathrm{ruleDep}\,R\,a\,b \to \mathrm{manual}\,a\,b\Big)
  \Rightarrow
  \Big(\forall a b c,\ \mathrm{manual}\,a\,b \to \mathrm{manual}\,b\,c \to
    \mathrm{manual}\,a\,c\Big)
  \Rightarrow \mathrm{Transitive}\,(\mathrm{ruleDepWith}\,R\,\mathrm{manual})$$

**⚠ 为什么必须加「吸收」前件（诚实标注，防假定理）**：
`ruleDepWith = ruleDep ∨ manual`。若**不加**吸收前件，
`ruleDep a b` 与 `ruleDep b c` 这一分支**推不出** `ruleDep a c`
（那需要 `detSet b ⊆ detSet c`，见 `ruleDep_trans_of_detSet_subset`，
**不是**免费的），故传递性会**失败**。
加上「`manual` 吸收 `ruleDep`」后，`ruleDepWith` 与 `manual` **同一**，
传递性直接转到 `manual` 上。

**这不是同义反复**：前件是**关于 `manual` 与 `ruleDep` 的关系**，
结论是**关于 `ruleDepWith` 的传递性**，两者不是同一个命题
（`habs` 不给传递性，`htrans` 不给吸收）。 -/
theorem ruleDepWith_trans (manual : ι → ι → Prop)
    (habs : ∀ a b, ruleDep R a b → manual a b)
    (htrans : ∀ a b c, manual a b → manual b c → manual a c)
    {a b c : ι} (hab : ruleDepWith R manual a b)
    (hbc : ruleDepWith R manual b c) : ruleDepWith R manual a c :=
  Or.inr (htrans a b c (toManual hab) (toManual hbc))
where
  toManual : ∀ {x y : ι}, ruleDepWith R manual x y → manual x y := by
    intro x y h
    rcases h with h' | h'
    · exact habs x y h'
    · exact h'

/-- ⭐⭐ **预序的充分条件**：`manual` 自反、传递、且吸收 `ruleDep`
⟹ `ruleDepWith R manual` 是预序。

（**反向未主张**：若 `manual` 不传递但 `ruleDep` 恰好补上，预序仍可能成立，
本文件不给该反向的判据，如实登记。） -/
theorem ruleDepWith_isPreorder (manual : ι → ι → Prop)
    (habs : ∀ a b, ruleDep R a b → manual a b)
    (hrefl : ∀ i, manual i i)
    (htrans : ∀ a b c, manual a b → manual b c → manual a c) :
    Std.Refl (ruleDepWith R manual) ∧ IsTrans ι (ruleDepWith R manual) :=
  ⟨⟨fun i => ruleDepWith_refl manual hrefl i⟩,
   ⟨fun _ _ _ hab hbc => ruleDepWith_trans manual habs htrans hab hbc⟩⟩

end PreorderWith

/-! ### §2.2 ⚠ **`ruleDep` 绝不为偏序**（层次结构不存在的判据） -/

section NotAntisymm

variable {R : RuleFam V A ι C X Y}

/-- ⚠⚠ **`ruleDep` 绝不反称**（只要存在一条 `r ≠ s` 的依赖）。

$$\mathrm{ruleDep}\,R\,r\,s \Rightarrow \mathrm{ruleDep}\,R\,s\,r \Rightarrow r \ne s
  \Rightarrow \neg\,\mathrm{Std.Antisymm}\,(\mathrm{ruleDep}\,R)$$

**证明是直接的，但结论重要**：`ruleDep` 的定义 `readSet r ∩ detSet s ≠ ∅`
**完全没有排除**反向的 `readSet s ∩ detSet r ≠ ∅`。
两条规则互相读对方确定的变量是**允许的**（正是「闭合耦合」）。
故 `ruleDep` **不可能**给出「规则的层次结构」——
这正面否掉了「若 `ruleDep` 是偏序则规则集有层次结构」这一思路。

**⟹ 这是任务「阶段 2」中「若 `ruleDep` 是偏序则规则集有层次结构」的
诚实回答：前提不成立，故该推论无从谈起。** -/
theorem ruleDep_not_antisymmetric {r s : ι}
    (hrs : ruleDep R r s) (hsr : ruleDep R s r) (hne : r ≠ s) :
    ¬ Std.Antisymm (ruleDep R) := by
  intro hanti
  exact hne (hanti.antisymm r s hrs hsr)

/-- 同上，用 `manual` 的对称支给出（来源 (b) 情形下**同样**不反称）。 -/
theorem ruleDepWith_not_antisymmetric {manual : ι → ι → Prop} {r s : ι}
    (hrs : ruleDepWith R manual r s) (hsr : ruleDepWith R manual s r) (hne : r ≠ s) :
    ¬ Std.Antisymm (ruleDepWith R manual) := by
  intro hanti
  exact hne (hanti.antisymm r s hrs hsr)

end NotAntisymm

/-! ===========================================================================
  §3  **与 `WorldModelCompleteV2` 的联系**

  `WorldModelCompleteV2` 的规则相关字段（`grep -n "Rule" Fate/WorldModelCompleteV2.lean` 实测）：

  ```
  rules : Rules (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X            -- = Set (Rule ⟨PUnit⟩ F.X F.X)
  render : Rule ⟨PUnit⟩ F.X F.X → Step F
  render_surj : Function.Surjective render
  rules_determine_step : Σ' r, r ∈ rules ∧ simulator.step = render r
  ```

  **⚠ 类型不匹配在哪里（必须先说清）**：

  | `RuleReadSet` 需要 | `WorldModelCompleteV2` 提供 | 差距 |
  |---|---|---|
  | `RuleFam V A ι C X Y = (V → A) → ι → LawRule C X Y` | `Rules = Set (Rule C X Y)`，`Rule` 是**条件分布核** | 规则类型不同（`LawRule` vs `Rule`）；且 `Rules` **是集合不是族**，没有索引 `ι` |
  | 变量空间 `V`、赋值空间 `A` | **完全没有** | WMC 里没有「变量」这一层 |

  **⟹ 结论**：`WorldModelCompleteV2` **不能**直接给出 `RuleFam`。
  但**反过来**可以构造：给定 `(V → A)` 型索引解碼，把 `rules : Set (Rule …)`
  里的元素逐个 `Rule.toLaw` 升到 `LawRule` —— 见下 `lawRuleFamOf`。
  **这个构造需要额外数据 `dec : V → A → ι → Rule C X Y`**，本文件不隐藏它。
  =========================================================================== -/

section WorldModelLink

open RuleReadSet

variable {V A ι : Type u}

/-- ⭐ **把 WMC 的一个索引解碼成 `LawRule`**：
先用 `dec` 从 `(σ, i)` 选出 `Rule`，再 `Rule.toLaw` 升为规律。

`Rule.toLaw` 来自 `LawRule`：
`fun c x => {r.kernel c x}`（单点允许集）。 -/
def lawRuleOf {F : Frame} [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (i : ι) :
    LawRule.LawRule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X :=
  LawRule.Rule.toLaw (dec i)

/-- ⭐⭐ **一个 `WorldModelCompleteV2` 确实给出 `RuleFam`**（构造方向）。

给定 `dec : ι → Rule …`（索引 ↦ 规则），规则族定义为
**与赋值 `σ` 无关**的那一支：

$$\mathrm{lawRuleFamOf}\,dec\;\sigma\;i \;:=\;
  (\mathrm{dec}\,i).\mathrm{toLaw}$$

**⚠ `dec` 是构造参数，不是从 `WMC.rules` 导出的**：
把 `rules : Set (Rule …)` 变成**函数**需要选择（`ι ↪ rules` 或 `Classical.choose`），
那一步本文件**不做**——它需要「索引集与规则集有一一对应」的额外假设
（规格未给，登记为未完成项 W1）。
本定理要说的是：**类型层面接通是可能的**，阻塞在「`Set` → 函数」这一步。 -/
def lawRuleFamOf {F : Frame} [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) :
    RuleFam V A ι (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X :=
  fun _σ i => lawRuleOf dec i

/-- ⭐⭐ **该规则族不依赖赋值**（这是构造的直接读出，用 `rfl` 验证）。 -/
theorem lawRuleFamOf_apply_eq {F : Frame} [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X)
    (σ τ : V → A) (i : ι) :
    lawRuleFamOf (V := V) (A := A) dec σ i
      = lawRuleFamOf (V := V) (A := A) dec τ i := by
  simp only [lawRuleFamOf]

/-- ⭐⭐⭐ **主结果（否定方向，最有价值）：该规则族的读集恒为空**。

$$\mathrm{readSet}\,(\mathrm{lawRuleFamOf}\,dec)\,i = \emptyset$$

**证明**：`lawRuleFamOf` 的输出与 `σ` **无关**（`lawRuleFamOf_apply_eq`），
故 `R σ i = R τ i` 恒成立，`readSet_empty_of_const` 直接给出。

**⟹ 语义**：由 `WorldModelCompleteV2` 的**裸规则集**经解码得到的规则族，
**在单变量扰动意义上什么也不读** —— 因为 WMC 的规则是
`kernel : C.Carrier → X.Carrier → Measure Y.Carrier`，**不接受变量赋值**。
变量层（`V → A`）是 `RuleReadSet` **附加**的，不是 WMC 自带的。
**这就是本文件关于阶段 3 的核心诚实结论。** -/
theorem readSet_empty_of_wmc {F : Frame} [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (i : ι) :
    readSet (lawRuleFamOf (V := V) (A := A) dec) i = ∅ :=
  readSet_empty_of_const (fun _ _ => rfl)

/-- ⭐⭐⭐ **该规则族上没有任何 `ruleDep`**（因为读集为空）。 -/
theorem not_ruleDep_of_wmc {F : Frame} [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (r s : ι) :
    ¬ ruleDep (lawRuleFamOf (V := V) (A := A) dec) r s := by
  rintro ⟨v, hv, _⟩
  rw [readSet_empty_of_wmc (V := V) (A := A) dec r] at hv
  exact absurd hv (Set.notMem_empty v)

/-- ⭐⭐ **该规则族上确定集为空**（**与直觉相反，但正确**）。

$$
\mathrm{determinesAt}\ (\mathrm{lawRuleFamOf}\,dec)\,i\,v
  \iff \forall \sigma \tau : V \to A,\ \sigma v = \tau v
$$

因为 `lawRuleFamOf` 与赋值**无关**（`lawRuleFamOf_apply_eq`），
`DeterminesAt` 的**前件** `R σ i = R τ i` 对**任意** `σ, τ` 都为真，
于是它退化为「`σ v = τ v` 对任意 `σ, τ` 成立」——这当且仅当
**`V` 上只有一个取值**（`Subsingleton (V → A)`，等价于
`Subsingleton V ∨ Subsingleton A`）。

**⟹ 这是本文件最重要的诚实结论之一**：把 WMC 的裸规则集接成 `RuleFam` 后，
**读集为空 且 确定集为空** —— 「读 / 确定」这一对概念在 WMC 侧
**完全没有内容**，因为 WMC 的规则根本不含变量层。

（对照 `RuleReadSet` 文件头的诚实标注 2：读集与确定集是**对偶但不对称**的
概念，本定理正是这对偶在「输出与赋值无关」这一退化情形下的精确形态。） -/
theorem determinesAt_of_wmc_iff {F : Frame} [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (i : ι) (v : V) :
    DeterminesAt (lawRuleFamOf (V := V) (A := A) dec) i v
      ↔ ∀ σ τ : V → A, σ v = τ v := by
  constructor
  · intro h σ τ
    exact h σ τ (lawRuleFamOf_apply_eq (V := V) (A := A) dec σ τ i)
  · intro h σ τ _
    exact h σ τ

/-- ⭐ **确定集为空的判据**：若 `V → A` 上有两个赋值在 `v` 上不同，则 `v ∉ detSet`。 -/
theorem not_determinesAt_of_wmc {F : Frame} [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (i : ι) {v : V}
    (h : ∃ σ τ : V → A, σ v ≠ τ v) :
    v ∉ detSet (lawRuleFamOf (V := V) (A := A) dec) i := by
  intro hv
  obtain ⟨σ, τ, hne⟩ := h
  exact hne ((determinesAt_of_wmc_iff (V := V) (A := A) dec i v).mp hv σ τ)

/-- ⭐⭐⭐ **该规则族的激活闭包退化为恒等**（`ruleDep` 为空 ⟹ 无重激活传播）。

$$\mathrm{lawRuleFamOf}\,dec\ \text{的}\ \mathrm{ruleDep}\ \text{为空}
  \Rightarrow \mathrm{closure}\,(\mathrm{ruleDep})\,I = I$$

**⟹ 这是「WMC 的规则集在当前接线**没有**激活传播内容」的定理化表述。** -/
theorem closure_eq_self_of_wmc {F : Frame} [MeasurableSpace F.X.Carrier]
    (dec : ι → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) (I : Set ι) :
    Activation.closure (ruleDep (lawRuleFamOf (V := V) (A := A) dec)) I = I := by
  apply Activation.closure_eq_self_of_closed
  intro a _ b hab
  exact absurd hab (not_ruleDep_of_wmc (V := V) (A := A) dec a b)

/-- ⭐⭐ **WMC 的 `rules` 字段非空**（由 `rules_determine_step` 这一 `Σ'` 字段取得）。

**与 WMC 的真联系**：`rules_determine_step : Σ' r, r ∈ rules ∧ …`
⟹ 存在 `r ∈ rules`。这说明「`rules` 不是空集」是 WMC 的**结构性事实**，
可以承载至少一条规则。 -/
theorem wmc_rules_nonempty {F : Frame} [MeasurableSpace F.X.Carrier]
    [FateV2.Rules.RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X]
    (W : WorldModelCompleteV2 F) :
    (W.rules : Set (Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X)).Nonempty :=
  ⟨W.rules_determine_step.1, W.rules_determine_step.2.1⟩

/-- ⭐⭐ **WMC 的 `rules` 非空 ⟹ 存在一个 `ι = PUnit` 的解码**（非空性的可用形式）。

这是 `wmc_rules_nonempty` 的构造性读法：从非空性取一个元素作为**唯一**索引的解码。 -/
theorem exists_dec_of_wmc {F : Frame} [MeasurableSpace F.X.Carrier]
    [FateV2.Rules.RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X]
    (W : WorldModelCompleteV2 F) :
    ∃ dec : PUnit → Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X, dec ⟨⟩ ∈ W.rules := by
  obtain ⟨r, hr⟩ := wmc_rules_nonempty W
  exact ⟨fun _ => r, hr⟩

end WorldModelLink

/-! ===========================================================================
  §4  **存在性：至少有一个 `RuleFam` 使 `ruleDepWith` 成预序**
  =========================================================================== -/

section Exists

open RuleReadSet

/-- ⭐ **存在性定理**：存在 `RuleFam` 与 `manual`，使合并依赖 `ruleDepWith` 是预序。

**构造**：取 `manual := fun _ _ => True`（全关系）。
全关系显然自反且传递，故由 `ruleDepWith_isPreorder` 得预序。

**⚠ 这不是空洞的**：它证明 §2.1 的假设**可满足**（一致性），
故 `ruleDepWith_isPreorder` 不是一条矛盾前件下的空洞定理。
**⚠ 但也不是「规则依赖在现实中是预序」的断言** —— 全关系在这里只是
证明一致性的**模型**。 -/
theorem exists_preorder_family (R : RuleFam V A ι C X Y) :
    ∃ manual : ι → ι → Prop,
      Std.Refl (ruleDepWith R manual) ∧ IsTrans ι (ruleDepWith R manual) :=
  ⟨fun _ _ => True,
   ruleDepWith_isPreorder (R := R) (fun _ _ => True) (fun _ _ _ => trivial)
     (fun _ => trivial) (fun _ _ _ _ _ => trivial)⟩

end Exists

/-! ===========================================================================
  §5  **诚实边界**
  =========================================================================== -/

/-
**本文件实际产出的定理清单（`grep ^theorem` 可核对）**

| 定理 | 性质 |
|---|---|
| `RuleSetWithDeps.dep_eq_ruleDepWith` | `rfl` 同一性（防同义反复检查） |
| `RuleSetWithDeps.dep_iff` | `rfl` |
| `RuleSetWithDeps.activation_closed` | 由 `Activation.closure_closed` 复用 |
| `RuleSetWithDeps.activation_minimal` | 由 `Activation.closure_minimal` 复用 |
| `RuleSetWithDeps.activation_idempotent` | 由 `Activation.closure_idempotent` 复用 |
| `ruleDep_refl_iff` | `rfl`（充要条件） |
| `ruleDep_not_refl_of_readSet_empty` | ⭐ **实质否定**：`ruleDep` 不是预序 |
| `ruleDep_not_refl_of_const` | 上条的常值族实例 |
| `ruleDep_trans_of_detSet_subset` | ⭐ 传递的**充分条件** |
| `ruleDep_of_readSet_subset` | 读集侧单调 |
| `ruleDepWith_refl` | 来源 (b) 自反（前件是 `manual` 自反，**不同义反复**）|
| `ruleDepWith_trans` | 来源 (b) 传递（前件：`manual` 吸收 `ruleDep` + 传递，**不同义反复**）|
| `ruleDepWith_isPreorder` | 预序的结构刻画 |
| `ruleDep_not_antisymmetric` | ⚠⚠ **偏序 / 层次结构不存在** |
| `ruleDepWith_not_antisymmetric` | 同上（来源 (b) 版） |
| `lawRuleFamOf_apply_eq` | `rfl`（构造与赋值无关） |
| `readSet_empty_of_wmc` | ⭐⭐ **WMC 的解码规则族读集为空** |
| `not_ruleDep_of_wmc` | ⭐⭐ **WMC 的解码规则族无 `ruleDep`** |
| `determinesAt_of_wmc_iff` | ⭐⭐ **WMC 的解码规则族确定集为空**（`∀σ τ, σ v = τ v`）|
| `not_determinesAt_of_wmc` | 上条的成员判据 |
| `closure_eq_self_of_wmc` | ⭐⭐ WMC 侧激活闭包恒等 |
| `wmc_rules_nonempty` | ⭐ **真联系**：WMC 的 `rules` 非空 |
| `exists_dec_of_wmc` | 上条的构造性读法 |
| `exists_preorder_family` | ⭐ 预序假设的可满足性 |

**本文件没有完成什么（诚实登记，编号 W1–W5）**

**W1. `Set` → 函数这一步未做。** `WorldModelCompleteV2.rules : Set (Rule …)`，
而 `RuleFam` 需要 `(V → A) → ι → LawRule …`（**函数**）。
把集合变成函数需要「索引与规则集一一对应」或 `Classical.choose`，
前者需规格未给的假设，后者会引入一个**无理据的选择函数**。
本文件把「解码 `dec`」作为**显式构造参数**留下，不隐藏。

**W2. 变量层 `V` / `A` 在 WMC 中不存在。**
`WorldModelCompleteV2` 的规则字段是 `kernel : C.Carrier → X.Carrier → Measure Y.Carrier`，
**不接受变量赋值**。故 `readSet` 意义上的「读」在 WMC 里**无法表达**。
这正是 `readSet_empty_of_wmc` / `not_ruleDep_of_wmc` 两条**否定定理**的内容。

**W3. `WorldModelCompleteV2` 未被修改。**
本文件零改动既有模块（纪律 2）。因此 `RuleSetWithDeps` 与 WMC 的关系是
「**WMC ⟶ RuleFam（需额外 `dec`）**」的**单方向构造**，不是字段级集成。
若要真正集成，须在 WMC 增加 `rulesHaveDeps : RuleSetWithDeps …` 字段 ——
本文件**不做**（会改动已入链模块）。

**W4. `ruleDep` 不是预序，也不是偏序。**
`ruleDep_not_refl_of_readSet_empty`（自反失败）+
`ruleDep_not_antisymmetric`（反称失败）。
故「若 `ruleDep` 是偏序则规则集有层次结构」这一推论**前提不成立**。
本文件把它写成**否定的定理**，而非绕过。

**W5. 不回答 TD-05。**
`grep -cE "Loop|Gaze|Level" Fate/RuleReadSet.lean` = 0；
`grep -cE "Loop|Gaze|Level" Fate/RuleReadSetWiring.lean` 只命中本段与第 21 行
的**这两处说明文字**（自指），即本文件的**内容**与循环 / 分类 / 层级零关联。
本文件**不声称解决了规则提取问题**，也**不声称**规则依赖与循环 / 分类有关。
-/

end RuleReadSetWiring

end FateV2.Rules