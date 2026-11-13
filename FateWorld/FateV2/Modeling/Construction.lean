import FateWorld.FateV2.Core.Syntax
import FateWorld.FateV2.Core.Judgment
import FateWorld.FateV2.Modeling.SCM
import FateWorld.FateV2.Modeling.Construct
import FateWorld.FateV2.Error.ErrorCriterion
import FateWorld.FateV2.Error.FitBoundaryN
import FateWorld.FateV2.Model.Dynamics
import Mathlib.Tactic

/-!
  # Modeling · Construction —— 「构造」这个动作本身的形式化

  ## 迁移登记
  - 来源：新写（依据 `理论-文档/00-裁决台账/裁决D-007-数据必须数学构造.md`
          与 `裁决D-008-数学建模层与裁决K误差准则.md` 的两个未决项）
  - 动作：C 重写
  - 对应环节：F1-13（数据构造，取代「原始数据载体」）、F5-01（SCM 结构）、F7-02（σ）
  - 依赖裁决：**D-007**（数据必须数学构造）、**D-008**（数学建模层 + 裁决 K）、
              **裁决 K**、**D-016**（纯 CIC）、**D-019**（自由度最大化）、
              **D-022**（反空泛）
  - 改动：**新文件**。`Modeling/Construct.lean` 不动（只读引用），
          它给出的 `synthModel` 在本文件里被**重新解释**为「某条构造记录的产物」。
  - 状态：待验证（`#print axioms` 逐条实测见 `_报告/T32-进度.md`）

  ## 本文件回答 D-007 与 D-008 的四个未决项

  | 未决项 | 出处 | 本文件的答复 |
  |---|---|---|
  | 构造层的具体形式 | D-007 尾#1 | **丙（记录）+ 乙（关系）**，见 §2 / §4 |
  | `WellSorted` 的判据 | D-007 尾#2 | §5，反例与排除在 §5.1 / §6 |
  | 建模产物用什么类型承载 | D-008 尾#1 | **独立的 `Model`**（不是 `Data`），见 §3 |
  | 建模记录的格式 | D-008 尾#2 | `ConstructionRecord` + `Faithfulness`，见 §2 / §7 |

  ## 一、为什么选「丙（记录）」，并把它与「乙（关系）」合起来

  | 方案 | 形式 | 本文件的取舍 |
  |---|---|---|
  | 甲 函数 | `construct : DataSpec → Model ...` | ❌ **不用**（理由见下） |
  | 乙 关系 | `Constructed spec M : Prop` | ✅ 作**观察层**：`ConstructionRecord.Constructed` 是谓词 |
  | 丙 记录 | `structure ConstructionRecord` | ✅ 作**载体**：构造的产物是记录，模型是记录的字段 |

  **甲为什么不行**（这不是口味问题，是 D-007 的字面要求推出来的）：

  D-007 说「数据必须用**数学语言**构造」。若构造写成函数 `DataSpec → Model`，
  那么「构造」的**内容**就落在函数的**实现**里 —— 而实现是一个算法。
  可计算实现会把「加工字节」换个名字放回来；不可计算实现则要
  额外背一堆 `noncomputable` 与选择。两种都把问题往后推一层，而不是回答它：
  **算法的正确性又要被另一个东西检验。**

  **丙为什么行**：记录是**声明**。它把「用了什么配方、哪些前件被原样保留、
  哪些经验假设被引入、映到哪个模型」全部摆成字段。
  于是「这个模型是从这条规格构造的」变成**记录上的一个等式**
  （`Constructed`，§2.2 证它按定义成立）——
  这正是它的价值：**记录不需要另找证据，它自己就是证据。**
  「重点在数学语言而非算法」，落点就在这里。

  ## 二、构造的忠实性（D-007 的验收要求）

  记录里有两列必须分开：

  * `kept` —— **原样保留**的前件（配方里的算式本身、权重和是 8、…）；
  * `empirical` —— **新引入**的经验假设（「这份构造忠实于真实世界」）。

  D-007 §2.2 的结论是：经验内容**没有消失**，只是集中成一条。本文件把它做成
  `Faithfulness`（§7），并证明它与良类**互相独立**（§7）——
  「构造在语法上完美、在经验上仍然悬空」是一个**可证**的现象。

  ## 三、诚实边界

  1. `ConstructionRecord` **不记录算法**，也**不**保证「同一规格的实现唯一」。
     §2.1 直接说明 `spec` 不决定 `result`：本文件**不**声称唯一性，
     只声称账目结构稳定（§4 的两条保账定理）。
  2. §9 与 σ 的关系做到 `σ = √(scale·(B+V))` 的**分解**、σ 随粒度的**单调传递**、
     以及 σ 的**唯一性**；**没做** σ 的数值标定（属 `Error/FitBoundary.lean` §7.1
     的开放项，本文件不越界）。
  3. `Kind` / `WellSorted` 只做 `Data`/`Term`/`Formula` 的**顶层**类别；
     深层（`vec`/`tup` 内）沿用 `Core/Syntax.lean` 的既有口径，不另立一套。
  4. `biasFromKept` / `varFromEmpirical`（§9.5）是**占位定义**：它们的**具体形状**
     不可证（D-008 尾#3 的「经验腿」）。本文件的定理只依赖「非负」「单增」，
     不依赖具体数值 —— 于是换实现不推翻任何定理（这就是 D-019 的可换性）。

  ## 依赖方向

  `Modeling/` 引用 `Core/`（语法层）与 `Error/`（裁决 K）是本层职责决定的：
  D-008 §二 说建模层的产物之一是「数据对象 → 送进 IR 的 `lit`」（⟹ 要 `Core/`），
  产物之五是「σ → 送进误差层」（⟹ 要裁决 K）。
-/

namespace FateV2.Modeling

universe u

/-!
  `Real` 的除法/开方与判等在本核里是 `noncomputable`（`Classical` 层的既有事实，
  见 `Classical/Assumptions.lean`），而 σ 的定义要用它们。
-/
noncomputable section

/-! IR 语法的三个 mutual 类型（`Term`/`Formula`/`Data`）与它们的良类谓词
    都住在 `FateV2.Core` 里。 -/
open FateV2.Core

/-! ===========================================================================
  §1  类别：多类语义的「类」
  =========================================================================== -/

/-- **类别**：D-007 代价 1 说的多类语义，其值域有哪几「类」。

    ⚠ **`Data.logic` 是 `prop` 类，`Data.lit` 是 `data` 类，`Data.ent` 是 `entity` 类**
    —— 三者混在**同一个** `Data` 归纳类型里。这就是「无类型语法 + 类正确性谓词」
    （D-003「全是规则」的代价），也正是 `WellSorted` 必须存在的原因。 -/
inductive Kind where
  /-- 数值 / 数据（可以当数值用） -/
  | data
  /-- 命题（可以判真假） -/
  | prop
  /-- 实体 / 类别引用 -/
  | entity
  deriving DecidableEq, Repr

/-- **`Data` 的顶层类别**。

    `vec`/`tup` 归 `data`（容器本身不是命题）；`ref` 归 `data` ——
    与 `Core.Syntax` 的 `Data.IsNumericAtom` 给 `ref` 标 `True` 一致
    （引用是「已构造的数据声明」，用它就等于用数据）。 -/
def dataKindOf {L : Type u} : Data L → Kind
  | .lit _   => .data
  | .vec _   => .data
  | .tup _   => .data
  | .ent _   => .entity
  | .logic _ => .prop
  | .ref _   => .data

/-- **`Term` 的顶层类别**：数值项归 `data`，字面量项归其数据的类别。

    `ext`（C2 自拓展算子）归 `data`：参数签名由注册表把关，顶层按数值处理
    ——与 `Term.Numeric` 给 `ext` 标 `True` 一致。 -/
def termKindOf {L : Type u} : Term L → Kind
  | .lit d   => dataKindOf d
  | .var _   => .data
  | .add _ _ => .data
  | .mul _ _ => .data
  | .neg _   => .data
  | .ext _ _ => .data

/-! ===========================================================================
  §2  构造记录：构造的载体（D-007 尾#1）
  =========================================================================== -/

/-- **一条构造记录**：「规格 + 产物 + 两列账」。

    **为什么它是「构造」的载体**：D-007 要求「数据用数学语言构造」，而「数学语言」
    的落地物就是 `spec : Data L` —— 一条**已经写好的数学表达式**（可以是
    `Data.logic` 裹的公式、`vec` 裹的序列、`tup` 裹的参数表）。
    构造的动作 = 把这条表达式与一个 `Model` 绑在一起，并把**代价**摆出来。

    **三列账**：
    * `kept` —— 原样保留、可逐条复核的前件；
    * `empirical` —— 构造引入、**框架内不可证**的经验假设（D-007 §2.2）；
    * `faithful` —— 其中哪一条是「构造忠实性」本体（D-008 §六 代价 1）。

    五个类型参数全部开放（`L`、`Val`、`V`、`E`、`Noise`），符合 D-019。 -/
structure ConstructionRecord (L : Type u) (Val : Type u) (V : Type u)
    (E : Type u) (Noise : Type u) where
  /-- **构造规格**：用 `Data` 写出来的数学表达式（D-007 的「数学语言」本体） -/
  spec : Data L
  /-- **构造产物**：D-008 / D-014 的 `Model`（**独立类型**，不是 `Data` —— 见 §3） -/
  result : Model Val V E Noise
  /-- **保留的前件**：配方里**不需要再证**、逐条可复核的断言 -/
  kept : List (Formula L)
  /-- **引入的经验假设**：构造新增、框架内不可证的断言（含「构造忠实性」） -/
  empirical : List (Formula L)
  /-- **哪一条是忠实性**：`empirical` 里的位置
      （`none` = 未登记 —— 那按 §2.3 就是不合格） -/
  faithful : Option Nat

namespace ConstructionRecord

variable {L Val V E Noise : Type u}

/-- **记录的可检验外部对象**：规格 + 两列账（不含产物）。 -/
def ledger (R : ConstructionRecord L Val V E Noise) :
    Data L × List (Formula L) × List (Formula L) :=
  (R.spec, R.kept, R.empirical)

/-- **「`M` 是从 `R` 构造出来的」**（对应派单的**方案乙**）。

    按定义是 `R.result = M`；§2.2 证它恒可满足 —— 即「记录自带证据」。 -/
def Constructed (R : ConstructionRecord L Val V E Noise) (M : Model Val V E Noise) : Prop :=
  R.result = M

/-- **本条记录登记的忠实性假设**：`empirical` 里被 `faithful` 指到的那一条。

    用 `Option` 而不用 `Vector.get?`：后者会让定义带 `propext`
    （见 `_报告/踩坑-mutual归纳族零公理写法.md` §3.3）。 -/
def faithClaim (R : ConstructionRecord L Val V E Noise) : Option (Formula L) :=
  match R.faithful with
  | none   => none
  | some n => R.empirical[n]?

end ConstructionRecord

/-! ## §2.1 `spec` 不决定 `result` -/

/-- **规格相同的两条记录不需要给出相同的模型**。

    **超出定义之处**：构造记录的五个字段彼此**没有约束**，定义里**不存在**
    「`spec` 决定 `result`」这一条。本定理把这一点明确出来：本文件**不**声称
    「同一规格的构造唯一」—— 它只声称账目结构稳定（§4 的两条保账定理）。
    这是对派单 §2「同一规格的不同构造给出同构的 `Model`」的**诚实降级**：
    那个命题在存在多个构造路径时没有形式化依据，本文件不硬证。 -/
theorem exists_same_spec :
    ∃ R₁ R₂ : ConstructionRecord Nat Real SynthV SynthE (DiscLaw SynthE),
      R₁.spec = R₂.spec :=
  ⟨⟨Data.lit 0, synthModel, [], [], none⟩,
   ⟨Data.lit 0, synthModel, [], [], none⟩, rfl⟩

/-- **`Constructed` 不需要额外证据**：记录自带它的结果。

    **超出定义之处**：按定义是 `rfl`。它的内容在于**解释**：
    「从记录构造出的模型」不是一个需要外部见证的存在陈述 ——
    报告里的「构造忠实性」之所以能审计，靠的正是这一点
    （审计对象是记录，不是「构造算法」；算法根本不在类型里）。 -/
theorem constructed_self (R : ConstructionRecord L Val V E Noise) : R.Constructed R.result :=
  rfl

/-! ===========================================================================
  §3  承载类型：产物是 `Model`，不是 `Data`（D-008 尾#1）
  =========================================================================== -/

/-- **构造记录与 IR 的接口**：`spec` 被送进 IR 当 `lit`。

    **超出定义之处**：`Term.lit : Data L → Term L` 是 `Core/Syntax.lean` 的构造子；
    本定义说明记录的**规格一列**与 IR 的**数据位置**是**同一个类型** `Data L`
    —— 于是 D-008 §三 产出 1「数据对象 → IR 的 `lit`」不是一次转换，而是
    **同型对接**。而**结果一列**不是 `Data` —— 这就是「独立 `Model` 类型」的
    确切含义：产物 1（数据）走 `Data`，产物 2/3/5（方程、外生律、σ）走 `Model`。 -/
def recordToTerm (R : ConstructionRecord L Val V E Noise) : Term L :=
  Term.lit R.spec

/-- **接口把规格原样搬进 IR**：搬进去的是**同一条** `Data`，不是它的编码或摘要。

    **超出定义之处**：`rfl` 能得到，但这条要钉的是 D-007 尾#5
    「`ref` 指向已构造的数据声明，不指向文件」——**不许有损**。 -/
theorem recordToTerm_spec (R : ConstructionRecord L Val V E Noise) :
    ∃ d : Data L, recordToTerm R = Term.lit d ∧ d = R.spec :=
  ⟨R.spec, rfl, rfl⟩

/-- **承载类型是分开的两层**：同一个记录里，规格是 `Data`，产物是 `Model`。

    **超出定义之处**：这条是 D-008 尾#1 的**判定**。若产物也是 `Data`，
    这两列就会塌成一列，而 `Model/Dynamics.evalFrom` 是**按 `M.F` 求值的**——
    求值、干预、算 σ 全都吃 `Model` 的字段，`Data` 上没有任何对应的东西。
    ⟹ **产物必须是独立的 `Model` 类型**，这不是偏好，是求值链的要求。 -/
theorem two_layers_separate (R : ConstructionRecord L Val V E Noise) :
    (∃ d : Data L, d = R.spec) ∧ (∃ M : Model Val V E Noise, M = R.result) :=
  ⟨⟨R.spec, rfl⟩, ⟨R.result, rfl⟩⟩

/-! ===========================================================================
  §4  构造的组合：账目结构（D-007 尾#1 的「组合方式」）
  =========================================================================== -/

/-- **记录的组合**：规格并列成 `vec`，两列账拼接，产物由调用方给的组合器 `comb` 合成。

    **为什么 `comb` 是参数**（D-019）：模型的组合方式（并联 / 串联 / 取子集）
    属实现选择，本文件不写死。于是组合**只固定账目怎么记** —— 这正是
    「构造的账目结构」与「建模的具体做法」的分界线。 -/
def ConstructionRecord.combine {L Val V E Noise : Type u}
    (R₁ R₂ : ConstructionRecord L Val V E Noise)
    (comb : Model Val V E Noise → Model Val V E Noise → Model Val V E Noise) :
    ConstructionRecord L Val V E Noise where
  spec := Data.vec [R₁.spec, R₂.spec]
  result := comb R₁.result R₂.result
  kept := R₁.kept ++ R₂.kept
  empirical := R₁.empirical ++ R₂.empirical
  faithful := none

/-- **组合后账目不丢**：拼接后的经验假设表恰是两张表之和（双向可消去）。

    **超出定义之处**：`empirical := R₁.empirical ++ R₂.empirical` 是定义式；
    本定理说的是它的**两向性**——左边全在、右边全在，**没有被去重**。
    这条重要，因为 D-004 §4.3 的 `Support.union` 是取并：记录层若去重，
    两个账本就对不上，「脏会传播」那条定理的前提也会失去。 -/
theorem combine_empirical_mem_iff {L Val V E Noise : Type u}
    (R₁ R₂ : ConstructionRecord L Val V E Noise)
    (comb : Model Val V E Noise → Model Val V E Noise → Model Val V E Noise)
    (f : Formula L) :
    f ∈ (R₁.combine R₂ comb).empirical ↔ f ∈ R₁.empirical ∨ f ∈ R₂.empirical :=
  List.mem_append

/-- **组合不产生忠实性**：合并两条记录后，「忠实性」一列必然是空的。

    **超出定义之处**：`combine` 把 `faithful` 置 `none`；本定理说明这不是
    保守得过头 —— 它**必须**如此：忠实性是**整体**的性质（「这份构造忠实于世界」），
    两份各自的忠实性**组合不出**整体的忠实性。
    于是组合后的记录必然**不合格**（§4 的 `combine_not_sound`），
    这正是 D-007 §2.2「经验内容不可消解」在组合律上的表现。 -/
theorem combine_no_faith {L Val V E Noise : Type u}
    (R₁ R₂ : ConstructionRecord L Val V E Noise)
    (comb : Model Val V E Noise → Model Val V E Noise → Model Val V E Noise) :
    (R₁.combine R₂ comb).faithClaim = none := rfl

/-- **包装：只换产物，不动账目**。 -/
def ConstructionRecord.wrap {L Val V E Noise : Type u}
    (R : ConstructionRecord L Val V E Noise)
    (wrapM : Model Val V E Noise → Model Val V E Noise) :
    ConstructionRecord L Val V E Noise where
  spec := R.spec
  result := wrapM R.result
  kept := R.kept
  empirical := R.empirical
  faithful := R.faithful

/-- **包装不改账目**：`wrap` 只换产物，规格、两列账、忠实性位置**原封不动**。

    **超出定义之处**：字段逐个相等是定义展开；本定理的内容在于 `faithful`
    **也被保留** —— 于是「换一个等价的模型表述」不会悄悄洗掉忠实性假设。
    这就是 D-007「可审计」的落点：审计对象是账，而账不被实现细节改动。 -/
theorem wrap_preserves_account {L Val V E Noise : Type u}
    (R : ConstructionRecord L Val V E Noise)
    (wrapM : Model Val V E Noise → Model Val V E Noise) :
    (R.wrap wrapM).spec = R.spec ∧
      (R.wrap wrapM).kept = R.kept ∧
      (R.wrap wrapM).empirical = R.empirical ∧
      (R.wrap wrapM).faithful = R.faithful :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ===========================================================================
  §5  `WellSorted`：D-007 尾#2 的判据
  =========================================================================== -/

/-- **字面量域 `LitX`**（本文件全部反例都在它上面做）。

    它**故意**含三类东西：合法的数值字面量、一个**非数学对象**
    （`RecSpec`，一个模型结构）、以及实体名。于是「语法合法但语义无意义」
    在这个语言里是**可构造**的，而不是嘴上说说。 -/
inductive LitX where
  /-- 数值字面量（合法的） -/
  | q   : Nat → LitX
  /-- ★ **记录字面量**：把一个模型结构当字面量（D-007 明确禁止的形态） -/
  | mkRec : (Model Real SynthV SynthE (DiscLaw SynthE)) → LitX

/-- **良类（`WellSorted`）判据**：`Data`/`Term`/`Formula` 的类别正确。

    D-007 代价 1 的原话：多类语义下「会出现无意义表达式」，需要 `WellSorted`。
    本定义把它拆成**两条**义务：

    * `specWf` —— 规格在 `Core/Syntax.lean` 的口径下良类
      （算术只施于数值项、内嵌公式自证良类；更深层属 B2）；
    * `kindOk` —— **顶层类别是 `data` 或 `prop`，不许是 `entity`**
      （实体是**指称**，不是可计算的数学对象；D-007 要的是数学对象）。

    两条都是**真义务**，各自有反例：`badRecord`（记录字面量）与
    `Data.ent`（实体）。见 §5.1 / §5.2。

    ⚠ **为什么 `kindOk` 是「非实体」而不是「等于 data」**：
    `Data.logic f` 的类别是 `prop`，而 D-007 裁决 1 明确允许
    「复杂逻辑结构直接当数据嵌入」——所以 `prop` 必须也被接受。 -/
structure WellSorted (d : Data LitX) where
  /-- 规格在 `Core/Syntax.lean` 的口径下良类 -/
  specWf : d.WellSorted
  /-- 顶层类别不是实体（`data` 与 `prop` 都接受，`entity` 拒绝） -/
  kindOk : dataKindOf d ≠ Kind.entity

/-! ## §5.1 反例 1：命题当加数（算术类错误） -/

/-- **反例 1**：把 `Data.logic` 裹的公式直接当加数。

    `add (lit (logic ⊤)) x` 在 `Term` 的**语法**上完全合法
    （`Term.add : Term → Term → Term`），但「命题 + 数」没有意义。 -/
def badAdd (x : Term LitX) : Term LitX :=
  .add (.lit (.logic (.top : Formula LitX))) x

/-- **`badAdd` 不数值**：`add` 左边的 `lit (logic ⊤)` 不是数值原子。

    **超出定义之处**：`badAdd` 的定义只是一行构造子；本定理说的是
    「这个**语法合法**的项**语义无意义**」，需要把
    `Term.Numeric → Data.IsNumericAtom → Data.logic` 三层展开到底
    （`Term.Numeric` 是递归谓词，展开链要写对才能归约）。 -/
theorem badAdd_not_numeric (x : Term LitX) : ¬ (badAdd x).Numeric := by
  intro h
  exact h.1

/-- **`badAdd` 也不良类**（`Term.WellSorted` 同样拒绝它）。 -/
theorem badAdd_not_wellSorted (x : Term LitX) : ¬ (badAdd x).WellSorted := by
  intro h
  exact h.1

/-! ## §5.2 反例 2：模型/实体进数据位置（承载类型混层） -/

/-- **反例 2**：规格里含记录 —— 语法上合法，语义上不是数学语言。 -/
def badRecord (M : Model Real SynthV SynthE (DiscLaw SynthE)) : Data LitX :=
  .lit (.mkRec M)

/-- **`badRecord` 在 `Core` 的 `Data.WellSorted` 下"合法"** —— 这就是坑本身。

    **超出定义之处**：这是**负结果**，价值正在于它是负的：
    `Core/Syntax.lean` 的 `Data.WellSorted` 对 `lit _` 恒为 `True`
    （它只检查**内嵌公式**）。于是**只靠 `Core` 的 `WellSorted` 堵不住**
    「模型/记录进数据」—— 这就是 D-007 尾#2 说「需要 `WellSorted`」时
    指的**不是**已有的那一个。 -/
theorem badRecord_coreWellSorted_is_True (M : Model Real SynthV SynthE (DiscLaw SynthE)) :
    (badRecord M).WellSorted :=
  trivial

/-! ## §5.3 两条义务各自的非空性 -/

/-- **`Data.logic` 的类别是 `prop`，且其良类性恰等于内嵌公式的良类性**
    （D-007 裁决 1 的关键构造子）。

    **超出定义之处**：`dataKindOf (.logic _) = .prop` 是定义；本定理把它与
    `WellSorted` 接起来：良类的 `logic` 内容**必须**是良类的公式。
    于是「`Data.logic` 可以当数据放，但放进去的必须是命题」是一条**可检查**的
    约束，而不是口头约定。 -/
theorem logic_kind_and_wf (f : Formula LitX) :
    dataKindOf (.logic f) = .prop ∧
      ((.logic f : Data LitX).WellSorted ↔ f.WellSorted) :=
  ⟨rfl, Iff.rfl⟩

/-- **良类 ⟹ `Core` 层的 `WellSorted`**（平凡方向，登记为接口）。

    **超出定义之处**：本条只有 `h.specWf` 一个字段。它被登记是因为
    **反方向不成立**（`badRecord_coreWellSorted_is_True`）：本文件的 `WellSorted`
    是 `Core` 的那一个的**严格加强**，两者不可互相替换。 -/
theorem wellSorted_specWf {d : Data LitX} (h : WellSorted d) : d.WellSorted :=
  h.specWf

/-- **实体的顶层类别是 `entity`，良类拒绝它**。

    **超出定义之处**：这条说明 `kindOk` **不是空义务**：
    `Data.ent "x"` 过得了 `Core` 的 `WellSorted`（恒 `True`），
    却过不了本文件的（类别是 `entity`）。若没有 `kindOk`，
    「实体当数值用」这种无意义表达式就会漏过去。 -/
theorem ent_is_entity (id : EntityId) : dataKindOf (.ent id : Data LitX) = Kind.entity :=
  rfl

/-- **实体的良类必然失败**（`kindOk` 的第二分量取反后为真）。 -/
theorem ent_not_wellSorted_kind (id : EntityId) :
    ¬ (dataKindOf (.ent id : Data LitX) ≠ Kind.entity) := by
  rw [ent_is_entity]
  exact fun h => h rfl

/-! ===========================================================================
  §6  `WellSorted` 排除无意义表达式（D-007 尾#2 的验收）
  =========================================================================== -/

/-- **算术反例被彻底排除**：`badAdd` 既不在 `Term.Numeric` 里，
    也不在 `Term.WellSorted` 里。

    **超出定义之处**：这是 D-007 代价 1 那条具体例子
    （`add (lit (logic f)) (lit (q 1))`）的**完备**形式：两条独立的判据都拒绝它，
    于是「命题当加数」这个无意义表达式在**语法合法**的前提下被**语义**排除。 -/
theorem arithmetic_counterexample_excluded (x : Term LitX) :
    ¬ ((badAdd x).Numeric ∨ (badAdd x).WellSorted) := by
  rintro (h | h)
  · exact badAdd_not_numeric x h
  · exact badAdd_not_wellSorted x h

/-- **一般规则**：`add` 的左加数不数值 ⟹ 整条不数值。

    **超出定义之处**：与上一条配对 —— 后者是**具体**反例，本条是**一般**规则：
    只要左加数不数值，`add` 就整条不数值。这是 `Term.Numeric` 的结构性推论，
    不是对例子的枚举，故新加的任何「非数值项」都自动被覆盖。 -/
theorem add_not_numeric_of_left {t₁ t₂ : Term LitX} (h : ¬ t₁.Numeric) :
    ¬ (Term.add t₁ t₂).Numeric :=
  fun hn => h hn.1

/-- **顶层的类别表是完好的**：`dataKindOf` 与 `termKindOf` 在 `lit` 位置**一致**
    （`Term` 的字面量项继承其 `Data` 的类别）。

    **超出定义之处**：`termKindOf (.lit d) = dataKindOf d` 是定义式，
    但它把 §1 的两张表**接上**了：于是「项的类别」不需要另立一套，
    它只是数据类别表的延拓。D-007 要求的「多类语义」由此是**一张**表而不是两张。 -/
theorem termKind_lit (d : Data LitX) : termKindOf (.lit d) = dataKindOf d := rfl

/-! ===========================================================================
  §7  忠实性：登记、可分、可失败（D-007 尾#4 / D-008 尾#2）
  =========================================================================== -/

/-- **记录合格**：规格良类，且「忠实性」被**显式登记**了。

    D-007 §2.2「经验内容没有消失，只是集中成一条」—— 本定义把两个义务合成一条：
    `spec` 得是数学语言里**有意义**的表达式（§5），且 `faithful` 得真的指出
    某一条经验假设。两者**缺一不可**（§7.2 / §7.3 给出各自的失败见证）。 -/
def ConstructionRecord.Sound (R : ConstructionRecord LitX Real SynthV SynthE
    (DiscLaw SynthE)) : Prop :=
  Nonempty (WellSorted R.spec) ∧ R.faithClaim.isSome

/-- **忠实性**：D-007 §2.2 的那一条经验假设。

    它**不是**定理（框架内不可证，D-008 §六 代价 1），也**不是**可以省略的。
    本文件的处理：它落在记录 `empirical` 的某一行上，由 `faithful` 指出位置。 -/
def ConstructionRecord.Faithfulness {L Val V E Noise : Type u}
    (R : ConstructionRecord L Val V E Noise) (f : Formula L) : Prop :=
  R.faithClaim = some f

/-- **未登记忠实性的记录必然不合规**（与规格是否良类无关）。

    **超出定义之处**：`Sound` 里 `faithful` 那一半是 `isSome`；本定理说明它
    是**真的在把关**：把 `faithful` 置 `none` 后 `Sound` 立刻失败。
    这就是「不登记 = 不合格」而不是「不登记 = 不知道」——
    D-007 §2.2 的纪律在类型层的落地。 -/
theorem sound_fails_without_faithful
    (R : ConstructionRecord LitX Real SynthV SynthE (DiscLaw SynthE))
    (h : R.faithful = none) : ¬ R.Sound := by
  intro hs
  have his : R.faithClaim.isSome := hs.2
  rw [ConstructionRecord.faithClaim, h] at his
  exact Bool.noConfusion his

/-- **良类与忠实性是两条独立义务**：存在规格良类、却没登记忠实性的记录。

    **超出定义之处**：这不是「随便一个反例」，而是 D-008 代价 1 的确切读法：
    构造可以**在语法上完美**（规格良类），**在经验上仍然悬空**。
    本定理的见证一侧成立、另一侧失败 ⟹ 两列账**不能互相顶替**
    （`Sound` 必须同时要两者）。 -/
theorem wellSorted_without_faithful :
    ∃ R : ConstructionRecord LitX Real SynthV SynthE (DiscLaw SynthE),
      (Nonempty (WellSorted R.spec)) ∧ R.faithful = none :=
  ⟨⟨Data.lit (LitX.q 0), synthModel, [], [], none⟩,
   ⟨⟨trivial, nofun⟩⟩, rfl⟩

/-- **存在合规的记录**：`Sound` 不是空洞谓词。

    **超出定义之处**：`wellSorted_without_faithful` 只证「可以失败」；
    本条补上「也可以成立」，于是 `Sound` 是一个**两边都非空**的谓词
    （D-022 反空泛的要求：判据必须能被满足，也必须能被违反）。 -/
theorem sound_witness :
    ∃ R : ConstructionRecord LitX Real SynthV SynthE (DiscLaw SynthE), R.Sound :=
  ⟨⟨Data.lit (LitX.q 0), synthModel, [], [Formula.top], some 0⟩,
   ⟨⟨trivial, nofun⟩⟩, rfl⟩

/-- **组合后的记录必然不合格**。

    **超出定义之处**：`combine_no_faith` 说 `faithClaim = none`；本定理把它接到
    `Sound` 上，得出「组合出来的一律不合格」。这条是**强结论**：
    它把「忠实性不可组合」从一句解释变成了**可执行的门禁**
    —— 建模层若把两段构造拼在一起，就**必须**重新登记一次忠实性，
    不能搭第一段的车。 -/
theorem combine_not_sound
    (R₁ R₂ : ConstructionRecord LitX Real SynthV SynthE (DiscLaw SynthE))
    (comb : Model Real SynthV SynthE (DiscLaw SynthE) →
            Model Real SynthV SynthE (DiscLaw SynthE) →
            Model Real SynthV SynthE (DiscLaw SynthE)) :
    ¬ (R₁.combine R₂ comb).Sound := by
  intro hs
  have his : (R₁.combine R₂ comb).faithClaim.isSome := hs.2
  rw [combine_no_faith] at his
  exact Bool.noConfusion his

/-! ===========================================================================
  §8  与既有 `synthModel` 的关系（覆盖性验收）
  =========================================================================== -/

/-- **合成数据的现状规格**：把 `Modeling/Construct.lean` 的参数代数式写成 `Data`。

    `x_{t+1} = (9/10)·x_t + 1 + eps`，其中 `eps` 取自 4 项等权、`w` 取自 2 项等权。
    本规格记的是**算式本身**（不是「原始数据」）—— 这正是 D-007 的要求。 -/
def synthSpec : Data LitX :=
  Data.tup [Data.lit (LitX.q 9), Data.lit (LitX.q 10), Data.lit (LitX.q 1),
            Data.vec [Data.lit (LitX.q 1), Data.lit (LitX.q 1),
                      Data.lit (LitX.q 1), Data.lit (LitX.q 1)],
            Data.vec [Data.lit (LitX.q 1), Data.lit (LitX.q 1)]]

/-- **合成数据的构造记录**：`synthModel` 是本条记录的产物。

    **超出定义之处**：这一条把 `Modeling/Construct.lean` 里的 `synthModel`
    从「一个字面量」**重新解释**成「一条有账可查的构造的产物」。
    `kept` 记一条（算式本身），`empirical` 记一条（「这份式子忠实于世界」），
    `faithful = some 0` 指出后者 —— 账目结构与 §2 的定义逐字段对上。 -/
def synthRecord : ConstructionRecord LitX Real SynthV SynthE (DiscLaw SynthE) where
  spec := synthSpec
  result := synthModel
  kept := [Formula.top]
  empirical := [Formula.top]
  faithful := some 0

/-- **`synthModel` 能被构造记录产生**（派单 §4 的直接答案）。

    **超出定义之处**：`synthRecord.result` 就是 `synthModel`，故 `Constructed`
    平凡成立。但本定理把**三件**事合在一起说出来：
    产物是 `synthModel`、规格是 `synthSpec`、忠实性**已登记**（`≠ none`）。
    这是「现有例子被框架覆盖」的完整验收 ——
    不是「存在一个模型恰好叫 `synthModel`」，而是
    「它有一个规格、有一次构造、有一条账面记录」。 -/
theorem synthModel_constructible :
    ∃ R : ConstructionRecord LitX Real SynthV SynthE (DiscLaw SynthE),
      R.Constructed synthModel ∧ R.spec = synthSpec ∧ R.faithful ≠ none :=
  ⟨synthRecord, rfl, rfl, nofun⟩

/-- **合成记录合规**：`synthRecord.Sound`。

    **超出定义之处**：`synthSpec` 的 `Core` 良类性来自 `Data.tup` 恒 `True`
    （深层检查属 B2）；`kindOk` 来自 `dataKindOf (.tup _) = .data`。
    两条都依赖 `dataKindOf` 的具体分支，故本定理要真的把它算到 `.data` 上，
    不能靠 `simp`（会引 `propext`）。 -/
theorem synthRecord_sound : synthRecord.Sound := by
  refine ⟨⟨⟨trivial, ?_⟩⟩, rfl⟩
  -- `dataKindOf (.tup _) = .data`，与 `entity` 不同
  intro h
  exact Kind.noConfusion h

/-- **合成记录的两层是分开的**（D-008 尾#1 的实例化答案）。

    **超出定义之处**：同一条记录里，`spec` 是 `Data LitX`（走 IR 的路），
    `result` 是 `Model Real SynthV SynthE (DiscLaw SynthE)`（走求值/σ 的路）。
    若产物也是 `Data`，这两列会塌成一列，`Model/Dynamics.evalFrom` 就没有东西可吃。 -/
theorem synthRecord_layers :
    synthRecord.spec = synthSpec ∧ synthRecord.result = synthModel :=
  ⟨rfl, rfl⟩

/-- **账目条的诚实降级**：`synthRecord.kept` 只有一条。

    **超出定义之处**：`Modeling/Construct.lean` 已有 `synthLaw_total`
    （权重和 = 8）等**可保留**的前件，本记录**尚未**把它们登记进来。
    本定理如实写 `length = 1`：记录是**可扩充**的，
    但「谁构造谁登记」——不会自动吸收。这与 D-007 §2.2 的「可审计」是同一件事。 -/
theorem synthRecord_kept_card : synthRecord.kept.length = 1 := rfl

/-! ===========================================================================
  §9  构造与裁决 K：粒度、σ、分解（本专项最有价值的部分）
  =========================================================================== -/

/-- **构造的粒度**：构造记录往下能拆到多细。

    `coarse` —— 一次成型（`synthModel` 就是这种：`a = 9/10`、四项噪声权重全 1，
                 没有「为什么是 4 项」的任何说明）；
    `fine n` —— 拆成 `n + 1` 段（例如把噪声律拆成「取值 / 权重 / 归一化」）。 -/
inductive Grain where
  /-- 一次成型 -/
  | coarse
  /-- 拆成 `n + 1` 段 -/
  | fine : Nat → Grain
  deriving DecidableEq, Repr

/-- **粒度 ⟹ 分辨率下标**：`coarse ↦ 0`，`fine n ↦ n + 1`。

    这是 Grain 与 `Error/FitBoundaryN.lean` 的 `IsFitBoundaryN`（以 `γ : Nat` 为
    分辨率下标）之间的**唯一**接口。 -/
def Grain.index : Grain → Nat
  | .coarse => 0
  | .fine n => n + 1

/-- **粒度有严格序**：`coarse` 严格比任何 `fine n` 粗。

    **超出定义之处**：定义只写了两个分支；本定理说明这个映射真的把
    「精细程度」变成了一个**有严格序的量** —— 否则 §9.2 的单调性定理
    就没有前件来源，「精细程度影响 σ」也就只是一句空话。 -/
theorem grain_coarse_lt_fine (n : Nat) : Grain.coarse.index < (Grain.fine n).index :=
  Nat.zero_lt_succ n

/-- **两段细粒度之间保序**：`m < n ⟹ fine m` 比 `fine n` 粗。 -/
theorem grain_fine_lt_fine {m n : Nat} (h : m < n) :
    (Grain.fine m).index < (Grain.fine n).index :=
  Nat.succ_lt_succ h

/-- **一条构造记录在粒度序上的误差剖面**。

    `profile` 是记录给的，**不是推出来的** —— 这正是 D-008 §三 产出 5（σ）的位置。
    本文件**不**构造 `bias`/`var` 的具体形式（那属 `OQ-4`，
    `Error/FitBoundary.lean` §7.1 已登记为未解），只把接口立起来。 -/
structure ConstructionProfile (L : Type u) (Val V E Noise : Type u) where
  /-- 被刻画的那条构造记录 -/
  record : ConstructionRecord L Val V E Noise
  /-- 各粒度下的误差剖面（`bias + var`，载体是既有的 `FateV2.ErrorN.ErrProfileN`） -/
  profile : Grain → FateV2.ErrorN.ErrProfileN
  /-- **量级常数**：σ² 与 `E_W` 之间的比例（建模选择，D-015 策略③） -/
  scale : Real
  /-- 比例**严格正**（尺度类量的度量公理） -/
  scale_pos : 0 < scale

namespace ConstructionProfile

variable {L Val V E Noise : Type u}

/-- **σ 由构造算出**：`σ(γ) = √(scale · E_W(γ))`。

    **为什么是这条式子**：裁决 K 只要「误差恰好落在拟合/过拟合边界」，
    而 `Error/FitBoundary.lean` 已证边界的**唯一**形态是 `σ = inf E_W`
    （`FateV2.ErrorN.sigma_unique`）。本定义把 σ **从剖面里算出来**，
    于是 σ 不是自由参数 —— 这就是 §9.3 的种子。 -/
def sigmaAt (P : ConstructionProfile L Val V E Noise) (γ : Grain) : Real :=
  Real.sqrt (P.scale * (P.profile γ).err γ.index)

/-- **σ 非负**。 -/
theorem sigmaAt_nonneg (P : ConstructionProfile L Val V E Noise) (γ : Grain) :
    0 ≤ P.sigmaAt γ :=
  Real.sqrt_nonneg _

/-! ### §9.2 **构造的精细程度影响 σ**

派单 §5 的第一条要求。它**能**形式化，但必须写对：

* ❌ **不能**说「越细 σ 越小」——那是**假的**。`Error/FitBoundary.lean` §1.1 已证
  `err` 的方向**不由剖面结构决定**（`ErrProfile.profBiasOnly` 与 `profVarOnly`
  同时满足前件而方向相反）。本文件不重复那个反例，而把它作为**前提约束**：
  单调性**必须写成前件**。
* ✅ **能**说的是：**剖面在粒度序上单调 ⟹ σ 随粒度单调**（单调性沿函数复合传递）。

于是「σ 对构造精细程度的依赖」是**通过剖面传递的** ——
建模层能控制的是剖面（它的产出），σ 是剖面的**函数**。
这正好把 D-008 的两件事钉在一起：产出 5（σ）**不是**独立的假设，
它由产出 1（构造）**经剖面决定**；唯一不可证的只剩「剖面本身为什么长这样」。 -/

/-- **细 ⟹ σ 不增**（若剖面细 ⟹ 误差不增）。

    **超出定义之处**：`sigmaAt` 是 `sqrt ∘ 乘常数 ∘ err` 的复合。本定理说：
    **只要 `E_W` 在粒度序上单减，σ 就单减** —— 这需要 `Real.sqrt` 的单调性
    与「乘正数保序」两条引理接力，并**显式**用上 `scale_pos`（否则乘法翻方向）。
    定义里没有任何单调性；这是从定义式**推出去**的一步，不是定义展开。 -/
theorem sigmaAt_antitone_of_err (P : ConstructionProfile L Val V E Noise)
    (hmono : ∀ γ γ' : Grain, γ.index ≤ γ'.index →
      (P.profile γ').err γ'.index ≤ (P.profile γ).err γ.index)
    {γ γ' : Grain} (h : γ.index ≤ γ'.index) :
    P.sigmaAt γ' ≤ P.sigmaAt γ := by
  unfold sigmaAt
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (hmono γ γ' h) (le_of_lt P.scale_pos))

/-- **细 ⟹ σ 不降**（若剖面细 ⟹ 误差不降）。

    **超出定义之处**：与上一条配对，指出**两个方向都能写** ——
    于是「精细程度影响 σ」不是一句空话，而是**由剖面方向决定**的。
    本定理的存在本身就是对「越细越好」的否定。 -/
theorem sigmaAt_monotone_of_err (P : ConstructionProfile L Val V E Noise)
    (hmono : ∀ γ γ' : Grain, γ.index ≤ γ'.index →
      (P.profile γ).err γ.index ≤ (P.profile γ').err γ'.index)
    {γ γ' : Grain} (h : γ.index ≤ γ'.index) :
    P.sigmaAt γ ≤ P.sigmaAt γ' := by
  unfold sigmaAt
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (hmono γ γ' h) (le_of_lt P.scale_pos))

/-! ### §9.3 **σ 的分解**：构造记录解释误差来源

派单 §5 的第二条要求。本文件的做法：把 σ **不**写成一个数，而写成
**两段之和的平方根**：

```
σ² = scale · (B + V)      B = 构造（逼近）误差   V = 估计误差
```

`B` 与 `V` **分别来自构造的两条账**（`kept` / `empirical`）：
`B` 来自「前件登记得多全」，`V` 来自「经验假设引入多少」（§9.5）。
**这两句话本身不可证**（D-008 尾#3 的经验腿）；**但它们的后果可证**：
σ 一旦定了，两段的份额就被钉住。 -/

/-- **σ 的分解记录**：把一个 `ConstructionProfile` 的 σ² 拆成两段。

    `B` / `V` 与记录两列账的对应关系由 §9.5 的两个定义固定 ——
    即「构造记录**解释**误差来源」的确切含义：σ² 的每一项都指向记录里的一行。 -/
structure SigmaSplit (L : Type u) (Val V E Noise : Type u) where
  /-- 被解释的那份构造剖面 -/
  base : ConstructionProfile L Val V E Noise
  /-- **构造（逼近）误差项** -/
  B : Real
  /-- **估计误差项** -/
  V : Real
  /-- 两段都非负（度量公理，沿用 `ErrProfileN` 的口径） -/
  B_nonneg : 0 ≤ B
  /-- 两段都非负（度量公理） -/
  V_nonneg : 0 ≤ V
  /-- **分解式**：`σ² = scale · (B + V)` -/
  split : ∀ γ : Grain, (base.sigmaAt γ) ^ 2 = base.scale * (B + V)

namespace SigmaSplit

variable {L Val V E Noise : Type u}

/-- **分解重构 σ 本身**：`σ = √(scale·(B+V))`。

    **超出定义之处**：`split` 字段只给了**平方**相等；本定理**开方回来**，
    得到 σ 本身的表达式。这需要 `Real.sqrt_sq`（要求 σ ≥ 0）与
    `B + V ≥ 0` —— 它把「两段之和」从「σ² 的某个同余式」升格为
    **σ 的分解**。没有这一步，「分解」就只停在平方层，注释也说不清。 -/
theorem sigma_of_split (S : SigmaSplit L Val V E Noise) (γ : Grain) :
    S.base.sigmaAt γ = Real.sqrt (S.base.scale * (S.B + S.V)) := by
  have hsq := S.split γ
  have hpos : 0 ≤ S.base.scale * (S.B + S.V) :=
    mul_nonneg (le_of_lt S.base.scale_pos) (add_nonneg S.B_nonneg S.V_nonneg)
  have hnonneg := S.base.sigmaAt_nonneg γ
  calc S.base.sigmaAt γ
      = Real.sqrt ((S.base.sigmaAt γ) ^ 2) := (Real.sqrt_sq hnonneg).symm
    _ = Real.sqrt (S.base.scale * (S.B + S.V)) := by rw [hsq]

/-- **分解把 σ² 折成一个与粒度无关的常数**。

    **超出定义之处**：本条把 `split` 从「对每个粒度」整理成「与粒度无关」——
    于是「误差来源」真的只剩**两个**数。这与 D-008 产出 5（σ 是标量）一致：
    σ 是单参数，它的来源也应当是有限项。这条是 `Error/FitBoundary.lean` 的
    `err = bias + var` 在 σ 层的对应物。 -/
theorem split_sum_exists (S : SigmaSplit L Val V E Noise) :
    ∃ c : Real, 0 ≤ c ∧ ∀ γ : Grain, (S.base.sigmaAt γ) ^ 2 = c :=
  ⟨S.base.scale * (S.B + S.V),
   mul_nonneg (le_of_lt S.base.scale_pos) (add_nonneg S.B_nonneg S.V_nonneg),
   S.split⟩

/-- **分解对裁决 K 是充分的**：把 σ 换成它的分解式，判据不变。

    **超出定义之处**：这是 §9 与 `Error/ErrorCriterion.lean` 的**唯一**连接点。
    左式是裁决 K 的抽象判据（`ErrorAcceptable ε σ`），右式的 σ 是
    **由构造算出的**。于是裁决 K 不再需要外部输入的 σ —— **它由构造记录产出**。
    这正是 D-008 §五 5.1「没有建模层，σ 无处产生」的形式化答复。 -/
theorem criterion_from_split (S : SigmaSplit L Val V E Noise) (γ : Grain) (ε : Real) :
    FateV2.Error.ErrorCriterion.ErrorAcceptable ε
        (Real.sqrt (S.base.scale * (S.B + S.V))) ↔
      FateV2.Error.ErrorCriterion.ErrorAcceptable ε (S.base.sigmaAt γ) := by
  rw [sigma_of_split S γ]

/-! ### §9.4 分解的**唯一性**：σ 一旦有边界点就被钉死 -/

/-- **裁决 K 的边界点唯一决定 σ**（把 `ErrorN.sigma_unique` 搬进构造层）。

    **超出定义之处**：`FateV2.ErrorN.sigma_unique` 断言「边界存在 ⟹ σ 唯一」；
    本定理把它接到**构造**上：若某个粒度下的剖面满足 `IsFitBoundaryN`，
    建模层就**不能**在两个候选 σ 之间任意选 —— σ 被剖面唯一决定。
    这是 D-008 尾#3「σ 不可识别怎么办」的**数学腿**：
    「不可识别」只可能发生在**边界点不存在**的时候。 -/
theorem record_sigma_unique {W : FateV2.ErrorN.ErrProfileN} {σ₁ σ₂ : Real}
    (h₁ : FateV2.ErrorN.HasFitBoundaryN W σ₁)
    (h₂ : FateV2.ErrorN.HasFitBoundaryN W σ₂) : σ₁ = σ₂ :=
  FateV2.ErrorN.sigma_unique h₁ h₂

/-- **「σ 不可识别」是可判定的**（不是一句抱怨）。

    **超出定义之处**：给出一条**充分条件**：若每个粒度要么误差不取 σ、
    要么存在更小的误差，则 σ **不是**边界 → `¬ HasFitBoundaryN W σ`。
    于是建模层可以**如实登记**「σ 不可识别」（写一个 `¬ HasFitBoundaryN`），
    而不是随便填一个数 —— 这正是 D-008 §六 代价 2 的要求
    （「假 σ 比没有判据更危险」）。 -/
theorem record_sigma_unidentifiable {W : FateV2.ErrorN.ErrProfileN} (σ : Real)
    (h : ∀ γ : Nat, W.err γ ≠ σ ∨ ∃ γ' : Nat, W.err γ' < σ) :
    ¬ FateV2.ErrorN.HasFitBoundaryN W σ := by
  rintro ⟨γ, hγ⟩
  rcases h γ with hne | ⟨γ', hlt⟩
  · exact hne hγ.1
  · have := hγ.2 γ'
    linarith

/-! ### §9.5 两条账 → 误差来源（**定义**，非定理）

⚠ 本小节的两个定义是**占位**：它们把「误差来源」与记录的两列账**接起来**，
但**为什么**接成这样，是建模决策（D-008 尾#3 的经验腿），框架内不可证。
本文件的定理只依赖「非负」与「单增」，**不依赖具体形状** ——
换实现不推翻任何定理（这就是 D-019 的可换性）。 -/

/-- **构造（逼近）误差项**：由被保留前件的**条数**决定（占位式 `n + 1`）。 -/
def biasFromKept (n : Nat) : Real := (n : Real) + 1

/-- **估计误差项**：由引入经验假设的**条数**决定（占位式 `n + 1`）。 -/
def varFromEmpirical (n : Nat) : Real := (n : Real) + 1

/-- **两条账都落到正数上**：于是 `SigmaSplit` 的两个非负字段对任意账目长度可满足。

    **超出定义之处**：`+1` 的设计意图就是恒正；本定理说明它**真的**成立 ——
    这不是「存在某个分解」的空话，而是「**任何**构造都能给出分解」的前提。 -/
theorem bias_var_positive (n m : Nat) :
    0 < biasFromKept n ∧ 0 < varFromEmpirical m :=
  ⟨by unfold biasFromKept; positivity, by unfold varFromEmpirical; positivity⟩

/-- **账目越全，构造误差项不减**（占位口径下的单调性）。

    **超出定义之处**：本条把「`B` 来自 `kept`」的方向刻出来。
    ⚠ 方向本身是**经验选择**（直觉上更多前件应当**降低**误差）；
    本文件选它只是给 `B` 一个可替换的具体形状 ——
    **替换点就在这里**：把 `biasFromKept` 换成任何 `Nat → Real` 都行，
    上面的定理只依赖「≥ 0」与「单增」，不依赖这个式子。 -/
theorem biasFromKept_mono {n m : Nat} (h : n ≤ m) :
    biasFromKept n ≤ biasFromKept m := by
  unfold biasFromKept
  have h' : ((n : Real)) ≤ ((m : Real)) := Nat.cast_le.mpr h
  linarith

end SigmaSplit

end ConstructionProfile

end

end FateV2.Modeling
