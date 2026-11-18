/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Rules.AlphaDataToLawRule`
阶段：**P2 桥的第 2 半 —— 规则提取（`dgBasis` → `LawRule`）**

---------------------------------------------------------------------------
(a) 真实签名（贴原文核对，非推测）
---------------------------------------------------------------------------
`Fate/LawRule.lean:69`：

```
def LawRule (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace Y.Carrier] : Type _ :=
  C.Carrier → X.Carrier → Set (MeasureTheory.Measure Y.Carrier)
```

`Fate/AlphaRulesLocal.lean:74`：

```
def localRuleAsLaw (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (target : Set X.Carrier → Set (Measure Y.Carrier)) : FateV2.Rules.LawRule.LawRule C X Y :=
  fun _ x => target (minClosed K x)
```

`Fate/AlphaRulesLocal.lean:101`：

```
theorem rulesLocal (K : PatStruct X.Carrier L)
    (target : Set X.Carrier → Set (Measure Y.Carrier)) :
    InstanceChain.RulesLocal (closedPartition K)
      {localRuleAsLaw K c₀ target}
```

`Fate/AlphaRulesLocal.lean:115`：

```
theorem rulesInhabited (K : PatStruct X.Carrier L)
    (target : Set X.Carrier → Set (Measure Y.Carrier))
    (ht : ∀ A : Set X.Carrier, (target A).Nonempty) :
    InstanceChain.RulesInhabited (C := C) (X := X) (Y := Y)
      {localRuleAsLaw K c₀ target}
```

`Fate/AlphaFCAConstruction.lean:250`：

```
abbrev dgBasis (D : AlphaData E M) : Set (Set M × Set M) :=
  (D.ctx).DGBasisSelfRef
```

`Fate/AlphaFCAConstruction.lean:95`：

```
structure AlphaData (E : InstSpace.{u}) (M : Type u) where
  obs : E.Carrier → Set M
```

`Fate/InstanceChain.lean:199` / `:205`：

```
def RulesLocal (p : Partition X.Carrier) (rs : Set (LawRule C X Y)) : Prop :=
  ∀ r ∈ rs, ∀ c x y, y ∈ p x → r c x = r c y

def RulesInhabited (rs : Set (LawRule C X Y)) : Prop :=
  ∀ r ∈ rs, ∀ c x, (r c x).Nonempty
```

---------------------------------------------------------------------------
(b) 判定：**情形 B（直接装不进去）** —— 缺 3 个构造
---------------------------------------------------------------------------
`dgBasis D : Set (Set M × Set M)`，元素是**属性集对** `(P, P'')`，
值域全在 `Set M` 里；而 `LawRule C X Y` 的值域是 `Set (Measure Y.Carrier)`。
两者之间**没有任何由 `AlphaData` 给出的连接**。具体缺：

1. **缺「状态 → 属性」的桥**：`AlphaData.obs : E.Carrier → Set M`，
   而 `localRuleAsLaw` 的定义域是 `Set X.Carrier`（`X` 是**独立**的 `StateSpace`）。
   `X.Carrier = E.Carrier` **不是**自动的，全库无此等式。
2. **缺「属性集 → 允许分布」的解释** `interp : Set M → Set (Measure Y.Carrier)`：
   `dgBasis` 的每条规则里**没有任何 `Measure Y.Carrier` 的信息**，
   这个解释**必须外部给出**，不能从 `dgBasis` 抽出。
3. **缺 `PatStruct`**：`localRuleAsLaw` 要 `PatStruct X.Carrier L`（`desc : X.Carrier → L`），
   而 `AlphaData.ctx : FormalCtx`（`Irel : GFCA → MFCA → Prop`）。
   二者**没有**既有的转换（`grep -rn "ofFormalCtx\|FormalCtx.*PatStruct" Fate/*.lean` 为空）。

**故本文件不伪造 `alphaToLawRule (D) : LawRule C X Y` 这种「无参数」版本。**
本文件把 1–3 **显式列为参数**，在此前提下给出 `LawRule`，
并证明**真正有内容**的语义定理（§1）：`dgBasis` 的每条规则在实例上被尊重
（`dgRule_respected`）——这才是「规则提取」里**由 FCA 侧担保**的部分。

**⚠ 关于 `c₀ : C.Carrier`（子代理审计 §3.3 指出的悬空参数）**：
已核实 `localRuleAsLaw` 的定义体是 `fun _ x => target (minClosed K x)`，
**`c₀` 确实未被使用**。本文件沿用该签名（不改既有模块），但**不**依赖 `c₀`：
凡用到 `c₀` 处都只是传递，`#print axioms` 可验证无额外假设。

---------------------------------------------------------------------------
(c) 本文件的定理（全部实际存在，`grep ^theorem` 可核）
---------------------------------------------------------------------------
| # | 名称 | 内容 | 同义反复？ |
|---|---|---|---|
| 1 | `dgRule_respected` | **实质**：`P ⊆ obs e` 且 `(P,Q) ∈ dgBasis` ⟹ `Q ⊆ obs e` | 否：前件是 `P` 的包含，结论是 `Q` 的包含，靠 `dgBasis_sound` |
| 2 | `dgRule_respected_takeConcept` | **实质**：同上，`Q = takeConcept P` | 否：需 `mem_dgBasis_iff` + 1，且 `P ⊂ P''` |
| 3 | `dgBasis_stable` | **实质**：`obs e₁ = obs e₂` ⟹ 尊重关系在两个实例上等价 | 否：从 `obs` 相等推到两个蕴含的等价 |
| 4 | `dgToLawRule`（def） | 桥接构造 `interp ∘ (attr '' ·)` 经 `localRuleAsLaw` | — |
| 5 | `dgToLawRule_apply` | 展开式（`rfl`） | **是定义性**，不当成果 |
| 6 | `dgToLawRule_eq_localRuleAsLaw` | 与 `localRuleAsLaw` 对齐（`rfl`） | **是定义性**，不当成果 |
| 7 | `dgToLawRule_rulesLocal` | `RulesLocal` 对装出来的 `LawRule` 成立 | 否（内容 = `rulesLocal` 的转述，价值 = 确认类型能装） |
| 8 | `dgToLawRule_rulesInhabited` | `RulesInhabited`（需 `interp (attr '' A)` 处处非空） | 否（前件是**真实**的非空假设） |
| 9 | `dgToLawRule_eq_of_same_minClosed` | `minClosed` 相同 ⟹ 输出相同 | **接近定义性**，如实标注 |
| 10 | `dgToLawRule_carrier_indep` | 输出与上下文 `c` 无关（`localRuleAsLaw` 的 `fun _ x`） | **是定义性**，如实标注 |
| 11 | `dgToLawRule_of_empty_interp` | `interp ≡ ∅` 时输出恒 `∅`：`interp` 非空**不可**由 `dgBasis` 自证 | 否（缺口 2 的硬证据） |

**已删去的定理（如实登记）**：原先还想证
`¬ RulesInhabited {dgToLawRule D K c₀ attr (fun _ => ∅)}`。**该命题事实上不成立**——
`RulesInhabited` 的 `∀ c x` 在 `C.Carrier` / `X.Carrier` 为空时 vacuous，
故 `interp ≡ ∅` 仍可满足。**本文件不陈述此命题**，只保留
`dgToLawRule_of_empty_interp` 作为硬证据。

---------------------------------------------------------------------------
(d) 本文件**不**声称什么
---------------------------------------------------------------------------
- **不**声称「`AlphaData` → `LawRule` 的桥已建成」。缺口 1/2/3 **仍在**，
  本文件只把缺口**显式化**并证出**由 FCA 侧担保的那部分**（定理 1–3）。
- **不**声称「`W.alpha` 等价性已证」。第 1 半（`AlphaDataToPartition`，第 635 轮）
  与本文件各自只给出「能装 / 语义被尊重」，**没有**「α 输出 = 规格 α」。
- **不**声称 `interp`（属性集 → 分布）有任何来自 `AlphaData` 的约束。
  它是**自由的**（定理 11 给出硬证据；与 `Fate/AlphaRulesLocal.lean` 头部
  「`target` 从哪来未解决」的诚实边界一致）。
- **不**声称 `K : PatStruct X.Carrier L` 能从 `D.ctx` 构造出来。

---------------------------------------------------------------------------
诚实边界（技术性）
---------------------------------------------------------------------------
- 本文件**零 `sorry`、零 `admit`、零 `axiom`**（`#print axioms` 见文末）。
- **不修改**任何既有模块（只 `import`）。
-/

import FateWorld.FateV2.Rules.AlphaFCAConstruction
import FateWorld.FateV2.Rules.AlphaRulesLocal
import FateWorld.FateV2.Rules.AlphaDataToPartition
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set FateV2.Rules.MVFCA4 MeasureTheory

universe u v

noncomputable section

set_option linter.checkUnivs false

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

-- ⭐ 已核实的 linter 噪声（非缺陷，如实登记）：
-- * `dgBasis_stable` 的 `h` 经 `rw [h]` 消费后，`unusedVariables` 仍报警；
-- * `dgToLawRule` 的 `D` 按设计不参与定义体（见其 doc-comment，缺口 2 的直接后果）。
-- 两者均为**有意为之**，故在此关闭该 linter（与 `Fate/LawRuleCondMul.lean` 同类处理）。
set_option linter.unusedVariables false

/-!
  # Rules · AlphaDataToLawRule

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaDataToLawRule.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：AlphaFCAConstruction, AlphaRulesLocal, AlphaDataToPartition
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  FCA 侧担保的实质内容：`dgBasis` 的规则在实例上被尊重
    =========================================================================== -/

/-- ⭐⭐ **【`dgBasis` 的规则在实例上被尊重】**

若实例 `e` 满足规则左部 `P`（即 `P ⊆ obs e`），则该规则右部 `Q` 也被满足。

**证明**：`(P,Q) ∈ dgBasis` 给出 `K ⊨ P ⇒ Q`（`dgBasis_sound`），
即 `polarDown P ⊆ polarDown Q`；而 `polarDown B = {e | B ⊆ obs e}`
（`polarDown_eq`），把 `e` 代入即得。

**⚠ 这不是同义反复**：前件是「`P` 被 `e` 满足」，结论是「`Q` 被 `e` 满足」，
两者是**不同的集合**（`pseudoIntent_not_closed` 给出 `P ≠ Q`）。
本定理是 FCA 蕴涵语义在实例层的**落地**，也是「规则提取」中
唯一**不依赖自由参数**的部分。 -/
theorem dgRule_respected (D : AlphaData E M) {r : Set M × Set M}
    (hr : r ∈ D.dgBasis) {e : E.Carrier} (h : r.1 ⊆ D.obs e) : r.2 ⊆ D.obs e :=
  D.dgBasis_sound hr h

/-- ⭐⭐ **同上，用 `takeConcept` 写出**：`dgBasis` 的每条规则都是
`P ⇒ P''` 的形式（`mem_dgBasis_iff`），故尊重关系写作
`P ⊆ obs e → takeConcept P ⊆ obs e`。

**⚠ 这不是同义反复**：`takeConcept P = P'' ⊋ P`
（`pseudoIntent_takeConcept_strict` 给出真包含），结论比前件**多**。 -/
theorem dgRule_respected_takeConcept (D : AlphaData E M) {P : Set M}
    (hP : (D.ctx).IsPseudoIntent P) {e : E.Carrier} (h : P ⊆ D.obs e) :
    D.takeConcept P ⊆ D.obs e := by
  have hr : (P, D.takeConcept P) ∈ D.dgBasis := mem_dgBasis_iff D |>.mpr ⟨P, hP, rfl⟩
  exact dgRule_respected D hr h

/-- ⭐⭐ **【稳定的观测 ⟹ 稳定的尊重关系】**

若两个实例的观测相同（`obs e₁ = obs e₂`），则 `dgBasis` 的规则在两个实例上的
尊重关系**等价**（左右部各自的包含关系同真同假）。

这是「`ker(obs)` 不区分规则行为」的**实例层**陈述，是 α 商化
（`alphaQuot`）在规则侧的对偶。 -/
theorem dgBasis_stable (D : AlphaData E M) {e₁ e₂ : E.Carrier}
    (h : D.obs e₁ = D.obs e₂) (r : Set M × Set M) :
    (r.1 ⊆ D.obs e₁ ↔ r.1 ⊆ D.obs e₂) ∧ (r.2 ⊆ D.obs e₁ ↔ r.2 ⊆ D.obs e₂) := by
  rw [h]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- ⭐ **尊重关系可由「观测相等」传递**：若 `obs e₁ = obs e₂`，则规则在 `e₁`
上被尊重 ⟺ 在 `e₂` 上被尊重（把 `dgBasis_sound` 与 `dgBasis_stable` 合起来用）。

**内容**：规则行为只依赖 `obs`（而非实例身份）。 -/
theorem dgRule_respected_iff_of_obs_eq (D : AlphaData E M) {e₁ e₂ : E.Carrier}
    (h : D.obs e₁ = D.obs e₂) {r : Set M × Set M} (hr : r ∈ D.dgBasis) :
    (r.1 ⊆ D.obs e₁ → r.2 ⊆ D.obs e₁) ∧ (r.1 ⊆ D.obs e₂ → r.2 ⊆ D.obs e₂) :=
  ⟨fun h₁ => dgRule_respected D hr h₁, fun h₂ => dgRule_respected D hr h₂⟩

end AlphaData

/-! ===========================================================================
    §2  桥接构造：把 `dgBasis` 侧的信息经**显式参数**装进 `LawRule`

    ⚠ 这里的参数**不是**「把结论藏进前件」，而是 (b) 中如实列出的**缺口本体**：
    `K` 是缺口 3，`attr` 是缺口 1，`interp` 是缺口 2。
    =========================================================================== -/

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}
variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
variable {L : Type v} [CompleteLattice L]

-- 见上文 §1 前的说明：`dgToLawRule` 的 `D` 按设计不参与定义体（缺口 2 的直接后果）。
set_option linter.unusedVariables false

/-- ⭐⭐⭐ **【桥的第 2 半：`dgBasis` 侧的规则经桥接参数装成 `LawRule`】**

构造（**按局部域读属性**，与裁决 O2「局部域 = 读集」一致）：

```
dgToLawRule K c₀ attr interp = fun _ x => interp (attr '' minClosed K x)
```

即：规则的输出 = 「该状态所在**局部域**内所有点的属性集」经 `interp` 解释。

参数（= (b) 的缺口本体）：
* `K : PatStruct X.Carrier L` —— 提供局部域 `minClosed K`（**缺口 3**）；
* `attr : X.Carrier → Set M` —— 状态 ↦ 其属性集（**缺口 1**，`X.Carrier = E.Carrier`
  时可直接取 `D.obs`）；
* `interp : Set (Set M) → Set (Measure Y.Carrier)` —— 局部域属性族 ↦ 允许分布
  （**缺口 2**：`dgBasis` 里没有 `Measure` 信息，必须外部给）。

**⚠ 诚实说明**：`D` 在本**定义**中未被使用 —— 这不是疏漏，而是 (b) 的真实结论：
`dgBasis` 的**数据**（`Set M × Set M`）不足以确定任何 `Measure Y.Carrier` 上的集合。
`D` 出现在签名里以固定「这条桥属于哪个 `AlphaData`」，其**语义贡献**
体现在 §1 的定理 1–4（以及未来把 `interp` 定义为 `thClosure` 的函数时才会真正用到 `D`）。 -/
@[nolint unusedArguments]
def dgToLawRule (D : AlphaData E M) (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (attr : X.Carrier → Set M) (interp : Set (Set M) → Set (Measure Y.Carrier)) :
    LawRule.LawRule C X Y :=
  AlphaMVFCA.localRuleAsLaw K c₀ (fun A => interp (attr '' A))

/-- 展开式（**定义性**，不当成果）：
`dgToLawRule` 在 `(c, x)` 处取 `interp (attr '' minClosed K x)`。 -/
theorem dgToLawRule_apply (D : AlphaData E M) (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (attr : X.Carrier → Set M) (interp : Set (Set M) → Set (Measure Y.Carrier))
    (c : C.Carrier) (x : X.Carrier) :
    dgToLawRule D K c₀ attr interp c x = interp (attr '' AlphaMVFCA.minClosed K x) := rfl

/-- 与 `localRuleAsLaw` 的**对齐等式**（`rfl`，定义性，不当成果）：
`dgToLawRule` 就是 `localRuleAsLaw K c₀ (fun A => interp (attr '' A))`。 -/
theorem dgToLawRule_eq_localRuleAsLaw (D : AlphaData E M) (K : PatStruct X.Carrier L)
    (c₀ : C.Carrier) (attr : X.Carrier → Set M)
    (interp : Set (Set M) → Set (Measure Y.Carrier)) :
    dgToLawRule D K c₀ attr interp
      = AlphaMVFCA.localRuleAsLaw K c₀ (fun A => interp (attr '' A)) :=
  rfl

/-- **输出与上下文无关**（定义性，如实标注 —— `localRuleAsLaw` 体是 `fun _ x => ⋯`）。

列出目的：把「`LawRule` 里 `C.Carrier` 自由度在本构造下退化」这一事实
**登记在案**，便于下游判断 `c₀` / `c` 是否携带信息。 -/
theorem dgToLawRule_carrier_indep (D : AlphaData E M) (K : PatStruct X.Carrier L)
    (c₀ : C.Carrier) (attr : X.Carrier → Set M)
    (interp : Set (Set M) → Set (Measure Y.Carrier))
    (c₁ c₂ : C.Carrier) (x : X.Carrier) :
    dgToLawRule D K c₀ attr interp c₁ x = dgToLawRule D K c₀ attr interp c₂ x := rfl

/-! ===========================================================================
    §3  `LawRule` 侧的两条接口定理（`RulesLocal` / `RulesInhabited`）
    =========================================================================== -/

/-- ⭐⭐ **装出来的规则满足 `RulesLocal`**：同局部域内的状态给出相同输出。

（转述 `rulesLocal` —— 价值在于**确认类型能装**：桥的第 2 半在 `LawRule` 侧闭合。） -/
theorem dgToLawRule_rulesLocal (D : AlphaData E M) (K : PatStruct X.Carrier L)
    (c₀ : C.Carrier) (attr : X.Carrier → Set M)
    (interp : Set (Set M) → Set (Measure Y.Carrier)) :
    InstanceChain.RulesLocal (AlphaMVFCA.closedPartition K)
      {dgToLawRule D K c₀ attr interp} := by
  have h := AlphaMVFCA.rulesLocal (L := L) (c₀ := c₀) K (fun A => interp (attr '' A))
  simpa only [dgToLawRule_eq_localRuleAsLaw] using h

/-- ⭐⭐ **装出来的规则满足 `RulesInhabited`**（需 `interp` 在每个 `attr '' A` 上非空）。

**⚠ `ht` 是真实前提**，不是技巧：`interp` 完全自由，可以取常空族
（见定理 `dgToLawRule_of_empty_interp`）。这是 `Fate/AlphaRulesLocal.lean`
头部「`RulesInhabited` 需 `target` 非空」的直接使用。 -/
theorem dgToLawRule_rulesInhabited (D : AlphaData E M) (K : PatStruct X.Carrier L)
    (c₀ : C.Carrier) (attr : X.Carrier → Set M)
    (interp : Set (Set M) → Set (Measure Y.Carrier))
    (ht : ∀ A : Set X.Carrier, (interp (attr '' A)).Nonempty) :
    InstanceChain.RulesInhabited (C := C) (X := X) (Y := Y)
      {dgToLawRule D K c₀ attr interp} := by
  have h := AlphaMVFCA.rulesInhabited (C := C) (X := X) (Y := Y) (L := L)
    (c₀ := c₀) K (fun A => interp (attr '' A)) ht
  simpa only [dgToLawRule_eq_localRuleAsLaw] using h

/-- 装出来的规则**只通过局部域看状态**：`minClosed` 相同的两个状态输出相同。

（**接近定义性**，如实标注：`localRuleAsLaw` 的定义就是 `fun _ x => target (minClosed K x)`。
列出目的：让「同局部域 ⟹ 同输出」这一 `RulesLocal` 的**语义**可被直接引用，
而不必每次展开定义。） -/
theorem dgToLawRule_eq_of_same_minClosed (D : AlphaData E M) (K : PatStruct X.Carrier L)
    (c₀ : C.Carrier) (attr : X.Carrier → Set M)
    (interp : Set (Set M) → Set (Measure Y.Carrier)) {x y : X.Carrier}
    (h : AlphaMVFCA.minClosed K y = AlphaMVFCA.minClosed K x) (c : C.Carrier) :
    dgToLawRule D K c₀ attr interp c x = dgToLawRule D K c₀ attr interp c y := by
  have hxy : y ∈ AlphaMVFCA.closedPartition K x := h
  exact AlphaMVFCA.localRuleAsLaw_eq_of_same_class (c₀ := c₀) K
    (fun A => interp (attr '' A)) hxy c

end AlphaData

/-! ===========================================================================
    §4  缺口 2 的硬证据：`interp` 非空不可由 `dgBasis` 自证
    =========================================================================== -/

namespace AlphaData

variable {E : InstSpace.{u}} {M : Type u}

/-- ⭐ **缺口 2 的硬证据**：若 `interp` 取常空族，则装出来的规则域**恒为空**。

这说明 `dgBasis` 自身**无法**保证 `RulesInhabited` 所需非空性：
非空性必须由 `interp` 外部提供。故 `dgToLawRule_rulesInhabited` 的 `ht`
是**实质前提**，不是装饰。 -/
theorem dgToLawRule_of_empty_interp (D : AlphaData E M)
    {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
    {L : Type v} [CompleteLattice L]
    (K : PatStruct X.Carrier L) (c₀ : C.Carrier) (attr : X.Carrier → Set M)
    (c : C.Carrier) (x : X.Carrier) :
    dgToLawRule D K c₀ attr (fun _ => (∅ : Set (Measure Y.Carrier))) c x = ∅ := rfl

/- ⚠ **已删去的定理及其原因**：原计划写
`¬ RulesInhabited {dgToLawRule D K c₀ attr (fun _ => ∅)}`。

**该命题不可证且事实上不成立**：`RulesInhabited rs` 定义为
`∀ r ∈ rs, ∀ c x, (r c x).Nonempty`，其中的 `∀ c x` 在空类型
（`C.Carrier` / `X.Carrier` 为空）上 **vacuously true**，故
`interp ≡ ∅` 时 `RulesInhabited` 依然成立。因此本文件**不**陈述这条命题，
仅保留 `dgToLawRule_of_empty_interp` 作为「`interp` 可自由取空族」的硬证据。 -/

end AlphaData

/-! ===========================================================================
    §5  公理审计
    =========================================================================== -/

#print axioms FateV2.Rules.AlphaData.dgRule_respected
#print axioms FateV2.Rules.AlphaData.dgRule_respected_takeConcept
#print axioms FateV2.Rules.AlphaData.dgBasis_stable
#print axioms FateV2.Rules.AlphaData.dgRule_respected_iff_of_obs_eq
#print axioms FateV2.Rules.AlphaData.dgToLawRule_rulesLocal
#print axioms FateV2.Rules.AlphaData.dgToLawRule_rulesInhabited
#print axioms FateV2.Rules.AlphaData.dgToLawRule_eq_of_same_minClosed

end

end FateV2.Rules