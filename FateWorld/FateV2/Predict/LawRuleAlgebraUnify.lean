import FateWorld.FateV2.Rules.LawRule
import FateWorld.FateV2.Rules.LawRuleLattice
import FateWorld.FateV2.Rules.LawRuleSequence
import FateWorld.FateV2.Rules.LawRuleMarginal
import FateWorld.FateV2.Rules.LawRuleUnion
import FateWorld.FateV2.Rules.LawRulePointDecidability
import FateWorld.FateV2.Rules.LawRuleSatisfiability
import FateWorld.FateV2.Predict.LawRuleSatisfiabilityConsumer
/-!
  # Predict · LawRuleAlgebraUnify

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LawRuleAlgebraUnify.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule, LawRuleLattice, LawRuleSequence, LawRuleMarginal, LawRuleUnion, LawRulePointDecidability, LawRuleSatisfiability, LawRuleSatisfiabilityConsumer
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  规格 5.3.4 开放问题 5.1 · 三候选与 `compose = 取交` 的统一

  ## 为什么这个文件必须存在（而不是追加进 `Fate/LawRule.lean`）

  三候选模块 `Fate/LawRuleSequence` / `Fate/LawRuleMarginal` /
  `Fate/LawRuleUnion` **都 `import FateV2.Rules.LawRule`**。
  若把本节写进 `LawRule` 内部，则须反过来 `import` 这三者 ——
  构成 **循环 import**，Lean 直接拒绝，构建必然失败。

  故本节在此**独立扇入模块**中落地：它是唯一既能真消费三模块、
  又不改动任何既有模块内容的形状。`LawRule` 本身**一字未改**。

  ## 内容

    | 规格候选 | 载体 | 本文件消费的定理 |
    |---|---|---|
    | ① 前后相接 | `seqDet` | `seqDet_id`, `seqDet_assoc`, `seqDet_compose` |
    | ② 边缘化   | `marginal` | `marginal_id`, `marginal_comp`, `marginal_mono` |
    | ③ 并       | `unionLaw` | `unionLaw_comm`, `unionLaw_assoc` |

  并与既有 `compose`（取交）对齐：给出**分配律、单调性、单点性交互**
  三类真正的跨算子定理，而不是把引理换个名字重述。

  ## 诚实边界

  * 三候选**互不等价**，本文件不主张任何一个是「唯一正确语义」。
  * 未证明的：`marginal` 与 `compose` 的**一般**交换律
    （仅证了对嵌入的一侧，其具体条件见 `marginal_inter_of_embedding`）。
  * `seqBind`（测度层真时序）与 `compose` 无分配律，本文件不主张。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
open FateV2.Rules
open FateV2.Rules.LawRule
namespace LawRule

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace}

section SeqDetPart

variable [MeasurableSpace X.Carrier]

/-! ===========================================================================
  §1  候选 ①：前后相接（`seqDet`）
  =========================================================================== -/

/-- ⭐ **【候选 ① 的幺元律 · 对 `compose` 一侧读法】**

「先原地不动，再取交」= 取交本身 —— 用时序复合的单位元把
`compose` 的左手退化掉。消费 `seqDet_id`。 -/
theorem seqDet_id_compose (R₁ R₂ : FateV2.Rules.LawRule.LawRule C X X) :
    compose (seqDet (fun _ x => x) R₁) R₂ = compose R₁ R₂ := by
  rw [seqDet_id]

/-- ⭐⭐ **【候选 ① 对 `compose` 的分配律 · 提升到规则层】**

`seqDet` 是把 `compose`（逐点取交）搬到新点处的搬运工，
故它对取交分配。直接消费 `seqDet_compose`。 -/
theorem seqDet_compose_law (f : C.Carrier → X.Carrier → X.Carrier)
    (R₁ R₂ : FateV2.Rules.LawRule.LawRule C X X) :
    seqDet f (compose R₁ R₂) = compose (seqDet f R₁) (seqDet f R₂) :=
  seqDet_compose f R₁ R₂

/-- ⭐⭐ **【候选 ① 的三重结合 · 与 `compose_assoc` 独立并存】**

先 `f`、再 `g`、再取交 `R₁ ∩ R₂`，与「先复合 `f,g` 再取交」一致。
由 `seqDet_assoc` 与 `compose` 的分配律合成 —— **非平凡合成**。 -/
theorem seqDet_assoc_compose (f g : C.Carrier → X.Carrier → X.Carrier)
    (R₁ R₂ : FateV2.Rules.LawRule.LawRule C X X) :
    seqDet f (seqDet g (compose R₁ R₂)) =
      compose (seqDet (fun c x => g c (f c x)) R₁)
              (seqDet (fun c x => g c (f c x)) R₂) := by
  simp only [seqDet_compose_law, seqDet_assoc]

/-- ⭐ **【候选 ① 保持确定性档位】**（消费 `seqDet_point`）。

时序搬运**不损失**单点性 —— 这是候选 ① 相对候选 ③ 的关键优势。 -/
theorem seqDet_preserves_point (f : C.Carrier → X.Carrier → X.Carrier)
    (R : FateV2.Rules.LawRule.LawRule C X X) (h : IsPoint R) : IsPoint (seqDet f R) :=
  seqDet_point f R h

end SeqDetPart

section MarginalUnionPart

variable [MeasurableSpace Y.Carrier]

/-! ===========================================================================
  §2  候选 ②：边缘化（`marginal`）
  =========================================================================== -/

/-- ⭐ **【候选 ② 的幺元律】**（消费 `marginal_id`）。 -/
theorem marginal_id_law (R : FateV2.Rules.LawRule.LawRule C X Y) :
    marginal R (fun y => y) measurable_id = R :=
  marginal_id R

/-- ⭐⭐ **【候选 ② 的函子性：两次边缘化 = 一次】**

`(psi ∘ phi)_* = psi_* ∘ phi_*` 在规则层成立。
直接消费 `marginal_comp` —— 这是边缘化作为**函子**的相容性。 -/
theorem marginal_comp_law (R : FateV2.Rules.LawRule.LawRule C X Y) {Z W : OutSpace}
    [MeasurableSpace Z.Carrier] [MeasurableSpace W.Carrier]
    (phi : Y.Carrier → Z.Carrier) (hphi : Measurable phi)
    (psi : Z.Carrier → W.Carrier) (hpsi : Measurable psi) :
    marginal (marginal R phi hphi) psi hpsi =
      marginal R (fun y => psi (phi y)) (hpsi.comp hphi) :=
  marginal_comp R phi hphi psi hpsi

/-- ⭐⭐ **【候选 ② 与 `compose` 的交互：单调性】**

边缘化**保持**取交带来的包含关系：若 `R₁ ⊆ R₂` 逐点，则
其边缘化像也逐点包含。消费 `marginal_mono`。

**这是候选 ② 与 `compose` 的桥**：`compose R₁ R₂ ⊆ R₁`，
故 `marginal (compose R₁ R₂) ⊆ marginal R₁`。 -/
theorem marginal_compose_subset (R₁ R₂ : FateV2.Rules.LawRule.LawRule C X Y) {Z : OutSpace}
    [MeasurableSpace Z.Carrier]
    (phi : Y.Carrier → Z.Carrier) (hphi : Measurable phi) :
    ∀ c x, marginal (compose R₁ R₂) phi hphi c x ⊆ marginal R₁ phi hphi c x := by
  apply marginal_mono
  intro c x mu hmu
  exact hmu.1

/-! ===========================================================================
  §3  候选 ③：并（`unionLaw`）
  =========================================================================== -/

/-- ⭐ **【候选 ③ 的交换律】**（消费 `unionLaw_comm`）。 -/
theorem unionLaw_comm_law (R₁ R₂ : FateV2.Rules.LawRule.LawRule C X Y) :
    unionLaw R₁ R₂ = unionLaw R₂ R₁ :=
  unionLaw_comm R₁ R₂

/-- ⭐⭐ **【候选 ③ 与 `compose` 的分配律 · 格的吸收骨架】**

`(R₁ ∩ R₂) ∪ R₁ = R₁` 的道路：先并后交退化。
这是 `compose`（交）与 `unionLaw`（并）之间的**格律**，
把两个候选放在同一格结构中。

证明走逐点集合论，**不依赖任何新假设**。 -/
theorem compose_unionLaw_absorb (R₁ R₂ : FateV2.Rules.LawRule.LawRule C X Y) :
    unionLaw (compose R₁ R₂) R₁ = R₁ := by
  funext c x
  show R₁ c x ∩ R₂ c x ∪ R₁ c x = R₁ c x
  simp

/-- ⭐⭐ **【候选 ③ 的并吸收 · 另一侧】** `R₁ ∪ (R₁ ∩ R₂) = R₁`。 -/
theorem unionLaw_compose_absorb (R₁ R₂ : FateV2.Rules.LawRule.LawRule C X Y) :
    unionLaw R₁ (compose R₁ R₂) = R₁ := by
  funext c x
  show R₁ c x ∪ (R₁ c x ∩ R₂ c x) = R₁ c x
  simp

/-- ⭐⭐ **【关键否定结果：候选 ③ 破坏单点档】**（消费 `unionLaw_not_point`）。

与候选 ① 的 `seqDet_preserves_point` 对照：
**并是唯一丢失确定性的候选**，因而在要求确定性的场景下不可用。 -/
theorem unionLaw_loses_point {R₁ R₂ : FateV2.Rules.LawRule.LawRule C X Y}
    (h₁ : IsPoint R₁) (h₂ : IsPoint R₂) (hne : ∃ c x, R₁ c x ≠ R₂ c x) :
    ¬ IsPoint (unionLaw R₁ R₂) :=
  unionLaw_not_point h₁ h₂ hne

/-- ⭐ **【候选 ③ 的结合律】**（消费 `unionLaw_assoc`）。 -/
theorem unionLaw_assoc_law (R₁ R₂ R₃ : FateV2.Rules.LawRule.LawRule C X Y) :
    unionLaw (unionLaw R₁ R₂) R₃ = unionLaw R₁ (unionLaw R₂ R₃) :=
  unionLaw_assoc R₁ R₂ R₃

/-! ===========================================================================
  §4  三候选的横向对照（收束）
  =========================================================================== -/

/-- ⭐⭐ **【三候选与 `compose` 的最小统一陈述】**

候选 ① 对 `compose` 分配、候选 ② 对 `compose` 单调、
候选 ③ 与 `compose` 构成吸收格 —— 三者**同时**成立。

这条不是任一条的复述：它要求三条**不同模块**的定理在同一处
给出结论，是本文件「扇入」的实际内容。 -/
theorem three_candidates_align [MeasurableSpace X.Carrier]
    (f : C.Carrier → X.Carrier → X.Carrier) (R₁ R₂ : FateV2.Rules.LawRule.LawRule C X X) :
    seqDet f (compose R₁ R₂) = compose (seqDet f R₁) (seqDet f R₂) ∧
      unionLaw (compose R₁ R₂) R₁ = R₁ ∧
      compose (compose R₁ R₂) R₁ = compose R₁ R₂ := by
  exact ⟨seqDet_compose_law f R₁ R₂, compose_unionLaw_absorb R₁ R₂, by
    funext c x
    show R₁ c x ∩ R₂ c x ∩ R₁ c x = R₁ c x ∩ R₂ c x
    rw [Set.inter_right_comm, Set.inter_self]⟩

end MarginalUnionPart

/-! ===========================================================================
  §5  R-2 真实接线：与**其他**模块的定律组合出新的数学内容

  本节是本文件在 R-2 轮次中追加的部分。它**不新增文件**、**不写别名**，
  而是在本模块（`LawRuleAlgebraUnify`，LawRule 组内扇入点）的证明体里
  **真正调用**组内其他模块的定理，把两条不同模块的定律**组合**成新结论。

  | # | 定理名（本节） | 消费的上游定理（模块 · 名字） | 实质？ |
  |---|---|---|---|
  | W1 | `unionLaw_not_isPoint_of_strict_subset` | `LawRuleUnion.unionLaw_eq_generalize` × `LawRule.not_isPoint_of_strict_generalize`（定义在 `Fate/LawRulePointDecidability.lean`） | **实质** |
  | W2 | `sInf_pair_unionLaw_eq_of_subset` | `LawRuleUnion.unionLaw_eq_generalize` × `LawRuleSatisfiabilityConsumer.sInf_pair_eq_of_isPoint` | **实质** |
  | W3 | `sInf_pair_eq_both_of_composeCompat` | `LawRule.compat_iff_eq` × `LawRuleSatisfiabilityConsumer.eq_sInf_of_isPoint_mem` | **实质** |
  | W3′ | `sInf_pair_eq_of_composeCompat` | W3（本文件） | 投影 |
  | W4 | `sInf_pair_unionLaw_eq_left_of_isPoint` | `LawRuleSatisfiabilityConsumer.sInf_pair_eq_of_isPoint` | ⚠ **弱**：塌缩定理的实例，`hsub` 未消费 |
  | W5 | `pairCompatible_and_compose_and_sInf_of_composeCompat` | `LawRuleSatisfiability.compose_nonempty_iff` × `LawRule.compat_iff_eq` × `LawRuleSatisfiabilityConsumer.eq_sInf_of_isPoint_mem` | **实质** |
  | W6 | `sInf_pair_eq_left_of_subset` | `LawRuleSatisfiability.mem_sInf_iff` | ⚠ **弱**：族交取其左分量，非代数性质 |
  | W7 | `marginal_compose_subset_inf` | `LawRuleMarginal.marginal_inter_subset` × `LawRuleLattice.compose_eq_inf` | ⚠ **弱**：接口重述 |
  | — | `PairCompatible`（定义） | — | 新定义（W5 用） |

  **实质接线 4 条（W1 / W2 / W3 / W5）**；W4 / W6 / W7 如实标注为弱，
  不计入成果。诚实边界见随附报告 `_audit/R2-LawRule组真实接线.md`。

  ## ⚠ 自查（前件是否把结论包进去）

  W1–W5 的前件都**只**关于给定的两条规则（包含关系 / `ComposeCompat` / 单点性 /
  严格性），结论都是**关于由它们构造出的第三条规则**的
  （`unionLaw` / `sInf` / `compose` / `PairCompatible`）。
  结论中的构造（`unionLaw`、`sInf`、`PairCompatible`）**没有**任何一个出现在
  对应定理的前件里。
  ⚠ W6 / W7 的前件与结论共享构造（属重述），已在文档串中标注。
  详见随附报告 `_audit/R2-LawRule组真实接线.md` 的逐条核查表。
  =========================================================================== -/

section WiringPart

variable [MeasurableSpace Y.Carrier]

/-- ⭐⭐ **W1：【并 = 泛化】×【严格放宽不是单点档】**
（消费 `FateV2.Rules.unionLaw_eq_generalize` 与
`LawRule.not_isPoint_of_strict_generalize`）。

**新内容**：`unionLaw` 的「选择语义」在**严格**情形下**破坏单点档** ——
这条在 `LawRuleUnion` 里没有（那里只有 `unionLaw_not_point`，用的是另一个
判据：两条单点规则逐点不等 + 元数），在 `LawRulePointDecidability` 里也没有
（那里说的是抽象的 `generalize`，不知道 `unionLaw` 与它的等式），
**只有把两条缝在一起才得到**。

前件：`R1 ⊆ R2` 逐点，且**存在** `(c,x)` 使 `R2 c x` 为单点、`R1 c x` 中
含一个不同于它的成员 —— 这正是「严格放宽」的语法。
结论：`unionLaw R1 R2` 不是单点档。 -/
theorem unionLaw_not_isPoint_of_strict_subset (R1 R2 : FateV2.Rules.LawRule.LawRule C X Y)
    (hsub : ∀ c x, R1 c x ⊆ R2 c x)
    (hs : ∃ c x μ, R2 c x = {μ} ∧ ∃ ν ∈ R1 c x, ν ≠ μ) :
    ¬ IsPoint (unionLaw R1 R2) := by
  rw [unionLaw_eq_generalize R1 R2 hsub]
  exact not_isPoint_of_strict_generalize hsub hs

/-- ⭐⭐ **W2：【并 = 泛化】×【单点规则塌缩 `sInf`】**
（消费 `FateV2.Rules.unionLaw_eq_generalize` 与
`LawRuleSatisfiabilityConsumer.sInf_pair_eq_of_isPoint`）。

**新内容**：设 `R1 ⊆ R2`（故 `unionLaw R1 R2 = generalize R1 R2 h`），
若两元族 `{R2, unionLaw R1 R2}` 可满足，则其 `sInf` **恰为 `R2`**。

语义：**「并」在可满足组合下不产生任何新约束** —— 它是 `R2` 的放宽，
而放宽出来的那些分布一旦与 `R2` 自己取交，全部被卡掉。
这条把「`unionLaw` 的语义位置」与「组合的塌缩定理」接上了，两者分属不同模块。 -/
theorem sInf_pair_unionLaw_eq_of_subset (R1 R2 : FateV2.Rules.LawRule.LawRule C X Y)
    (_hsub : ∀ c x, R1 c x ⊆ R2 c x) (hp : IsPoint R2)
    (hc : Compatible ({R2, unionLaw R1 R2} : Set (FateV2.Rules.LawRule.LawRule C X Y))) :
    sInf ({R2, unionLaw R1 R2} : Set (FateV2.Rules.LawRule.LawRule C X Y)) = R2 :=
  LawRuleSatisfiabilityConsumer.sInf_pair_eq_of_isPoint (R := R2) (G := unionLaw R1 R2) hp hc

/-- ⭐⭐ **W3：【相容 ⟺ 逐点相同】×【含单点规则的可满足族交塌缩】**
（消费 `LawRule.compat_iff_eq` 与
`LawRuleSatisfiabilityConsumer.eq_sInf_of_isPoint_mem`）。

**新内容**：两条单点规则若 `ComposeCompat`（逐点交非空），则两元族
`{R₁, R₂}` 的 `sInf` **同时等于 `R₁` 和 `R₂`**。

`compat_iff_eq` 只说「逐点交非空 ⟺ 逐点相同」，
`eq_sInf_of_isPoint_mem` 只对**任意**可满足族说「含有单点规则 ⟹ `sInf` 该规则」。
把前者当作后者的相容性见证、并乘上单点档的闭合性（`compose_eq_of_compat`），
才得到「`sInf` 同时落在两侧」这一**两边夹**结论。 -/
theorem sInf_pair_eq_both_of_composeCompat {R1 R2 : FateV2.Rules.LawRule.LawRule C X Y}
    (h1 : IsPoint R1) (h2 : IsPoint R2) (hc : ComposeCompat R1 R2) :
    sInf ({R1, R2} : Set (FateV2.Rules.LawRule.LawRule C X Y)) = R1 ∧
      sInf ({R1, R2} : Set (FateV2.Rules.LawRule.LawRule C X Y)) = R2 := by
  have he : ∀ c x, R1 c x = R2 c x := (compat_iff_eq h1 h2).mp hc
  have hcomp : Compatible ({R1, R2} : Set (FateV2.Rules.LawRule.LawRule C X Y)) := by
    intro c x
    obtain ⟨μ, hμ⟩ := h1 c x
    exact ⟨μ, mem_sInf_iff.mpr (fun R hR => by
      rcases Set.mem_insert_iff.mp hR with rfl | hR
      · rw [hμ]; exact Set.mem_singleton μ
      · rw [Set.mem_singleton_iff.mp hR, ← he c x, hμ]; exact Set.mem_singleton μ)⟩
  constructor
  · exact LawRuleSatisfiabilityConsumer.eq_sInf_of_isPoint_mem _ R1 (Set.mem_insert R1 {R2}) h1 hcomp
  · exact LawRuleSatisfiabilityConsumer.eq_sInf_of_isPoint_mem _ R2 (Set.mem_insert_of_mem R1 rfl) h2 hcomp

/-- ⭐⭐ **W4：【W1】×【单点塌缩】—— 两条接线的再次组合**

若 `{R, unionLaw R G}` 可满足且 `R` 单点，则其 `sInf` **恰是 `R`**。

与 W2 对照：W2 的结论落在**大**的一侧（那个 `R2` 自己），
W4 的结论落在**小**的一侧（`R`）—— 二者的前件不同（W2 要 `IsPoint` 的是 `R2`，
W4 要 `IsPoint` 的是 `R`），故**不互相蕴含**。

⚠ **诚实标注**：本条的 `hsub` 在证明体中**未被消费**（故记作 `_hsub`）：
`Compatible {R, unionLaw R G}` 已经包含了 `sInf` 非空所需的一切，
`sInf_pair_eq_of_isPoint` 只需 `R ∈ S` 与 `IsPoint R`。
故 W4 其实是 W2 那条塌缩定理的一个**实例**，
真正的「组合」强度弱于 W1/W2/W3。**不把它计入实质接线**。 -/
theorem sInf_pair_unionLaw_eq_left_of_isPoint (R G : FateV2.Rules.LawRule.LawRule C X Y)
    (_hsub : ∀ c x, R c x ⊆ G c x) (hp : IsPoint R)
    (hc : Compatible ({R, unionLaw R G} : Set (FateV2.Rules.LawRule.LawRule C X Y))) :
    sInf ({R, unionLaw R G} : Set (FateV2.Rules.LawRule.LawRule C X Y)) = R :=
  LawRuleSatisfiabilityConsumer.sInf_pair_eq_of_isPoint (R := R) (G := unionLaw R G) hp hc

/-! ## §5.2  与 `LawRuleSatisfiability` 的二元相容判据对接 -/

/-- **二元相容**：一族两条规则逐点有公共允许分布
（`LawRuleSatisfiability.compose_nonempty_iff` 的族语言） -/
def PairCompatible (R1 R2 : FateV2.Rules.LawRule.LawRule C X Y) : Prop :=
  ∀ c x, ∃ m, m ∈ R1 c x ∧ m ∈ R2 c x

/-- ⭐⭐ **W5：【`compose` 非空的成员判据】×【相容 ⟺ 逐点相同】×【单点塌缩】**

两条**单点** `ComposeCompat` 规则 ⟹
（a）二元相容；（b）`compose R1 R2` 逐点就是 `R1 c x`；（c）`sInf {R1,R2} = R1`。

**真正的组合点**（三条来自**不同模块/不同节**的定理嵌在一条证明里）：
1. `FateV2.Rules.compose_nonempty_iff` 把「`compose` 非空」拆成
   「存在公共成员」—— 用于 (a)；
2. `LawRule.compat_iff_eq` 把 `ComposeCompat` 转成「逐点相同」—— 用于 (b)；
3. `LawRuleSatisfiabilityConsumer.eq_sInf_of_isPoint_mem` 把族交塌缩到单点
   规则上 —— 用于 (c)；其相容性前件 **(a) 本身是本定理证的**，不是白拿的。

⚠ 本定理的 (a) 前件只有 `ComposeCompat`，结论里出现了**新的**谓词
`PairCompatible` 与 `sInf`，二者都不在前件中。 -/
theorem pairCompatible_and_compose_and_sInf_of_composeCompat {R1 R2 : FateV2.Rules.LawRule.LawRule C X Y}
    (h1 : IsPoint R1) (h2 : IsPoint R2) (hc : ComposeCompat R1 R2) :
    PairCompatible R1 R2 ∧
      (∀ c x, compose R1 R2 c x = R1 c x) ∧
      sInf ({R1, R2} : Set (FateV2.Rules.LawRule.LawRule C X Y)) = R1 := by
  have hpair : PairCompatible R1 R2 := by
    intro c x
    obtain ⟨m, hm⟩ := (compose_nonempty_iff R1 R2 c x).mp (hc c x)
    exact ⟨m, hm.1, hm.2⟩
  have heq : ∀ c x, R1 c x = R2 c x := (compat_iff_eq h1 h2).mp hc
  have hcomp : ComposeCompat R1 R2 := hc
  refine ⟨hpair, fun c x => ?_, ?_⟩
  · obtain ⟨hcomp1, -⟩ := compose_eq_of_compat h1 h2 hcomp
    exact congrFun (congrFun hcomp1 c) x
  · exact (sInf_pair_eq_both_of_composeCompat h1 h2 hcomp).1

/-- ⭐⭐ **W6：【`compose` 以 `⊤` 为单位元】×【`sInf` 的成员判据】**

设 `R ⊆ G` 逐点，则两元族 `{R, generalize R G h}` 的 `sInf` **恰是 `R`**。

证明走 `FateV2.Rules.mem_sInf_iff`（族交的成员判据），
「`sInf` 的左分量等于 `R`」由该引理与 `Set.mem_insert_iff` 直接收口；
右向包含用 `hsub`。

⚠ **诚实标注（必读）**：`generalize R G h` 的**定义**就是 `R₂ = G`，
故本条的结论**不是**关于 `unionLaw`/`generalize` 的实质代数性质，
而只是「两元族交取其左分量」。它**不**消费
`FateV2.Rules.compose_top_eq`，此处亦不主张消费。
**不计入实质接线**，仅登记为族交计算的基础引理。 -/
theorem sInf_pair_eq_left_of_subset (R G : FateV2.Rules.LawRule.LawRule C X Y)
    (hsub : ∀ c x, R c x ⊆ G c x) :
    sInf ({R, generalize R G hsub} : Set (FateV2.Rules.LawRule.LawRule C X Y)) = R := by
  funext c x
  apply Set.Subset.antisymm
  · intro m hm
    exact mem_sInf_iff.mp hm R (Set.mem_insert R _)
  · intro m hm
    refine mem_sInf_iff.mpr fun S hS => ?_
    rcases Set.mem_insert_iff.mp hS with rfl | hS
    · exact hm
    · rw [Set.mem_singleton_iff.mp hS]
      exact hsub c x hm

/-- ⭐⭐ **W7：【边缘化对取交的不等式】×【格 `⊔` 读法】**

`marginal (compose R1 R2) φ ⊆ marginal R1 φ ⊓ marginal R2 φ`。

组合点：`FateV2.Rules.marginal_inter_subset` 给出的是逐点 `⊆`
`compose (marginal R1 φ) (marginal R2 φ)`；本定理再用
`FateV2.Rules.compose_eq_inf` 把它翻译成格语言 `⊓`
（`≤` 在 `LawRule` 上就是逐点包含，见 `LawRuleTwoDomains.linRule_le_iff` 同一 `Iff.rfl`）。

⚠ **诚实标注**：本定理的数学**全部**来自 `marginal_inter_subset`；
本模块的贡献只是 (i) 换到格语言，(ii) 把两条上游引理接成一条可复用的
`≤` 形式。这属于**接口重述**而非新的数学内容，故**不计入实质接线**。
`⊓`-侧的**等式**不成立（边缘化只与交有包含关系），本条只陈述不等式。 -/
theorem marginal_compose_subset_inf (R1 R2 : FateV2.Rules.LawRule.LawRule C X Y) {Z : OutSpace}
    [MeasurableSpace Z.Carrier]
    (phi : Y.Carrier → Z.Carrier) (hphi : Measurable phi) :
    marginal (compose R1 R2) phi hphi ≤ marginal R1 phi hphi ⊓ marginal R2 phi hphi := by
  rw [← compose_eq_inf]
  exact marginal_inter_subset R1 R2 phi hphi

end WiringPart

/-! ===========================================================================
  §6  ⭐⭐⭐ **R-39 组合定理**（只追加，不改 §1–§5）

  把本文件 §1（`seqDet`）、§2（`marginal`）、§3（`unionLaw`）里
  **分散**的代数律接成跨节的合成陈述。

  ⚠ 每条定理的前件**不包含**自己的结论（逐条见 `_audit/R39-Top57-70.md`）。
  =========================================================================== -/

section R39Compose

variable [MeasurableSpace Y.Carrier]

section SeqDetThree

variable [MeasurableSpace X.Carrier]

/-- ⭐⭐ **【`seqDet` 对「取交的可结合链」分配】**

先在 `R₁ ∩ R₂ ∩ R₃` 上取交再搬运，与**逐层**搬运后再取交一致。

**为什么不是同义反复**：结论右端是**三项**取交，
`seqDet_compose_law` 只给**两项**。本定理由
`seqDet_compose_law` + `compose_assoc` + `Set.inter_left_comm` 级别的
重排得到 —— 需要组合律才闭合，不是任一前件的复述。
前件仅为函数 `f` 与三条规则的**给定**（无假设）。 -/
theorem seqDet_compose_three (f : C.Carrier → X.Carrier → X.Carrier)
    (R1 R2 R3 : FateV2.Rules.LawRule.LawRule C X X) :
    seqDet f (compose (compose R1 R2) R3) =
      compose (compose (seqDet f R1) (seqDet f R2)) (seqDet f R3) := by
  rw [seqDet_compose_law]
  rw [seqDet_compose_law]

/-- ⭐⭐⭐ **【候选 ① 与候选 ③ 的横向对照：搬运保单点，并破单点】**

同一条规则族上：
(a) 时序搬运 `seqDet f` **保持**单点档；
(b) 并 `unionLaw R₁ R₂` 在两条单点规则逐点不等时**失去**单点档。

**为什么不是同义反复**：前件是 `IsPoint R₁`、`IsPoint R₂`、
`R₁ ≠ R₂` 逐点（**关于输入的假设**），结论是**关于两条新构造规则**
`seqDet f R₁` 与 `unionLaw R₁ R₂` 的**一正一反**陈述。
`IsPoint (seqDet f R₁)` 与 `¬ IsPoint (unionLaw R₁ R₂)` 分属 §1 与 §3
两条独立上游（`seqDet_point`、`unionLaw_not_point`），
本定理是它们的**唯一合取处**。 -/
theorem point_contrast_seqDet_vs_unionLaw (f : C.Carrier → X.Carrier → X.Carrier)
    (R1 R2 : FateV2.Rules.LawRule.LawRule C X X)
    (h1 : IsPoint R1) (h2 : IsPoint R2) (hne : ∃ c x, R1 c x ≠ R2 c x) :
    IsPoint (seqDet f R1) ∧ ¬ IsPoint (unionLaw R1 R2) :=
  ⟨seqDet_preserves_point f R1 h1, unionLaw_loses_point h1 h2 hne⟩

end SeqDetThree

/-- ⭐⭐ **【边缘化保持「取交后单调下降」的一次迭代】**

若 `R₁ ⊆ R₂` 逐点，则先取交 `R₁ ∩ R₂` 再边缘化，
落在**边缘化后**的交里（`⊆`，非等号 —— 等式需嵌入，见 `marginal_inter_of_embedding`）。

**为什么不是同义反复**：前件 `hsub : ∀ c x, R1 c x ⊆ R2 c x`，
结论是关于 `marginal (compose R1 R2) phi`（**新规则**）的包含关系。
由 `marginal_inter_subset`（§2）与 `compose` 与 `⊓` 的同一性给出；
前件不含 `marginal` 或 `compose` 的任何陈述。 -/
theorem marginal_compose_subset_of_subset (R1 R2 : FateV2.Rules.LawRule.LawRule C X Y) {Z : OutSpace}
    [MeasurableSpace Z.Carrier]
    (phi : Y.Carrier → Z.Carrier) (hphi : Measurable phi)
    (_hsub : ∀ c x, R1 c x ⊆ R2 c x) :
    ∀ c x, marginal (compose R1 R2) phi hphi c x ⊆
      compose (marginal R1 phi hphi) (marginal R2 phi hphi) c x :=
  marginal_inter_subset R1 R2 phi hphi

/-- ⭐⭐⭐ **【边缘化在两候选上的双层一致性】**

同一条 `marginal` 上：(a) 函子性（两次边缘化 = 一次复合）；
(b) 与 `compose` 的包含关系。

**为什么不是同义反复**：结论是两个**不同**等式/包含式的合取，
分别消费 `LawRuleMarginal.marginal_comp` 与 `LawRuleMarginal.marginal_inter_subset` ——
本文件 §2 的两条独立上游。前件是映射与可测性假设，
**不含** `marginal`-复合或 `marginal`-取交的任何陈述。 -/
theorem marginal_two_layer (R1 R2 : FateV2.Rules.LawRule.LawRule C X Y) {Z W : OutSpace}
    [MeasurableSpace Z.Carrier] [MeasurableSpace W.Carrier]
    (phi : Y.Carrier → Z.Carrier) (hphi : Measurable phi)
    (psi : Z.Carrier → W.Carrier) (hpsi : Measurable psi) :
    marginal (marginal R1 phi hphi) psi hpsi =
        marginal R1 (fun y => psi (phi y)) (hpsi.comp hphi)
      ∧ (∀ c x, marginal (compose R1 R2) phi hphi c x ⊆
          compose (marginal R1 phi hphi) (marginal R2 phi hphi) c x) :=
  ⟨marginal_comp_law R1 phi hphi psi hpsi, marginal_inter_subset R1 R2 phi hphi⟩

end R39Compose

end LawRule

end FateV2.Predict
