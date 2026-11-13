/-
命运理论 · **规则评价框架**（科学哲学驱动的半启发式框架）
================================================================

模块：`Fate.RuleEvaluation`

---------------------------------------------------------------------------
(a) 作者第 537 轮裁决的原话
---------------------------------------------------------------------------
> 「**规则的评价这个属于半启发式  你按照科学哲学的相关处理方法来就行了
>   各种科学观啊  剃刀啊  什么的   主要是很启发式吧   所以我认为净版这个不完整
>   而且这个属于启发式辅助  需要加一个抽象  因为后续可能会有增删改**」

**⟹ 核心要求**（逐条落实，见下方「本文件做了什么」）：
1. **半启发式**，**不是「真/假」判断**；
2. **用科学哲学**（奥卡姆剃刀、波普尔、拉卡托斯、库恩）；
3. **净版不完整**（只有 supp/conf/lift 三公式 + 三个空名）；
4. ⭐ **需要加一个【抽象】** —— 不是给三个公式，而是**可扩展的评价框架**；
5. ⭐ **后续可能增删改** —— 框架要能容纳新评价量。

---------------------------------------------------------------------------
(b) 净版 5.7 的原始状态（`:1828-1837`）
---------------------------------------------------------------------------
**定义 5.4（规则的六个评价量）**：
- **三个已给公式**：`supp(R) = P(antecedent)`、`conf(R) = P(consequent | antecedent)`、
  `lift(R) = conf / P(consequent)`；
- **三个只给名称**：`coverage(R)`、`accuracy(R)`、`简洁度（以规则长度度量）`；
- `:1837` 明写：「覆盖率、准确率原文只给名称未给公式，简洁度未给『长度』的度量方式
  （字符长度？前件文字数？描述长度？）」⟹ 登记为开放问题 5.7。

**⚠ 关于那三个「已给公式」的本仓库状态**（必须先说清，否则会造出虚假接口）：
主控给出的 `#check` 探针（`Fate.ScoreK.bandLoss`、`Fate.FitBoundary.IsFitBoundary`）
**本仓库不存在**；`supp` / `conf` / `lift` 在 `Fate/` 下也**只有同名但不相关的对象**
（`Fate.R_SupportBound.supp : ℝ → ℝ` 是**分辨率 ↦ 有效样本数**的支持度剖面，
`Fate.R246G3.conf` 是一个**具体的 SCM 实例**，`Fate.liftFun` / `Fate.liftRule` /
`Fate.liftPred` / `Fate.liftH` 等都是别的构造）。
**⟹ 净版的 `supp/conf/lift` 在 Lean 里不存在**（净版只是符号）。
**⟹ 按任务书的兜底条款**：本文件**不做那四个 `def`**（`simplicity` /
`falsifiability` / `coverage` / `consistency`），**只做核心抽象**，
四个科学哲学评价量**留作 §2 的注释草案**。

**为什么不做**：`Rule` 只有一个字段 `kernel : C.Carrier → X.Carrier → Measure Y.Carrier`
——**里面没有「前件」、没有「后件」、没有概率空间 `P`**。
在这个结构上硬写「前件大小」、「`1 - conf`」只能是**凭空编造的类型**，
或者引入一堆**不可证的前件**（那正是本项目的同义反复高发区）。
**故本文件选择如实登记为开放问题，而不是伪造。**

---------------------------------------------------------------------------
(c) 本文件做了什么抽象
---------------------------------------------------------------------------
1. `class RuleEvaluation C X Y`：**五个字段**
   `Eval` / `eval` / `le` / `le_refl` / `le_trans`
   ⟹ 评价量的**注册表** + 评价量上的**偏序**（不是全序：不同量纲不可比）；
2. `def Better r₁ r₂`：在偏序下**严格更大**（`le` 且非反向 `le`）；
3. `theorem better_irrefl`：`Better` **不自反**；
4. `theorem better_trans`：`Better` **传递**；
5. `theorem better_asymm`：`Better` **不对称**（额外，代价为零）；
6. `theorem better_of_scalar`：若标量函数 `f : Eval → ℝ` 是 `le` 到 `(· ≤ ·)` 的
   **序嵌入**（双向 `↔`），则 `f e₂ < f e₁ ⟹ Better r₁ r₂`；
7. `noncomputable def realEval` + `theorem realEval_better_iff` + `theorem better_lt_real`
   ：**非空实例**（`Eval := ℝ`），并证明该实例下 `Better` **恰等于** `<`；
8. `theorem better_of_scalar_realEval`：在 `realEval` 上**真的调用**
   `better_of_scalar`，证明标量化桥与框架**不冲突**。

**「可增删改」的实现**：`Eval : Type` 是**任意**的。新评价量放进 `Eval` 即可，
不改框架。删掉某个量 = 换一个小一点的 `Eval`（例如从 `ℝ × ℝ` 到 `ℝ`）。
改权重 = 换 `le`（或换 `f`）。**框架本身不用改。**

**⚠ 反退化/非平凡性证据**（防「同义反复」自查，逐条可核）：
- `better_irrefl`：**不是** `Iff.rfl`。它**真的用** `le_refl`（否则无法
  从 `¬ le e e` 得到矛盾）。
- `better_trans`：**不是** `Iff.rfl`。它**真的用** `le_trans` **两次**；
  若把 `le_trans` 字段删掉，本定理**证不出**。
- `better_asymm`：只用 `Better` 的定义展开（`rintro` + `h.2 h21`），
  把**两个不同的 `eval` 项**联系起来，不是 `rfl` 能得到的。
- `realEval_better_iff`：**真的用**了 `ℝ` 上 `≤` 的线性序
  （`lt_of_le_of_ne`）。它在实数实例上把 `Better` **降到** `<`，
  因此 `Better` **既非空也非全**。
- `better_lt_real` / `better_of_scalar_realEval`：**真的构造出**具体的 `Better`。

**⚠「前件是否已包结论」自查（本项目最高频问题）**：
- `RuleEvaluation` 的五个字段中，**没有任何一条**直接断言 `Better` 的任何性质
  （`Eval`/`eval` 只是数据，`le`/`le_refl`/`le_trans` 只是偏序公理）。
- `better_trans` 的前件是「`r₁` 优于 `r₂`」+「`r₂` 优于 `r₃`」，
  结论是「`r₁` 优于 `r₃`」——**三者是三个不同对象**，不是同义反复。
- `better_of_scalar` 的前件是**标量不等式** `f e₂ < f e₁` + **序嵌入** `↔`，
  结论是**两个评价量上的偏序 + 否定式**——**类型不同**，不是同义反复。
  （这也解释了为何前件必须是 `↔` 而非单向 `→`：单向弱到结论不可达。）

---------------------------------------------------------------------------
(d) 四个科学哲学评价量做到了什么
---------------------------------------------------------------------------
**只留 §2 的注释草案，未形式化**（理由见 (b)）。
**⟹ 明说：本文件对 `simplicity` / `falsifiability` / `coverage` / `consistency`
的贡献是「指出它们应当填在 `Eval` 的哪个位置」，不是「给出了它们的 Lean 定义」。**

---------------------------------------------------------------------------
(e) 不声称什么
---------------------------------------------------------------------------
**⚠ 本文件不声称「解决了开放问题 5.7」。**
**只声称：「提供了一个可扩展的规则评价框架（注册表 + 偏序），
并证明该偏序上的严格序是良定义的、可传递的、非对称的」——仅此而已。**
具体评价量的公式、权重、阈值，**全部留给使用者**。

**⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
-/

import Mathlib.Order.Basic
import FateWorld.Legacy.Frame
import FateWorld.Legacy.Basic

namespace Fate

namespace RuleEval

/-! ===========================================================================
  §1  ⭐⭐⭐ 规则评价框架（**核心抽象**，科学哲学驱动，可增删改）
  =========================================================================== -/

/-- ⭐⭐⭐ **规则评价框架**（科学哲学驱动，可增删改）。

**核心思想**：规则评价**不是「真值」**，是**多维排序**。
每个评价量是一个从规则到 `Eval` 的函数，
且**量纲不同、方向可能不同**，所以**不能简单相加**。

**科学哲学的四个来源**（每个对应一个评价量，见 §2 注释草案）：
- **奥卡姆剃刀**（简洁性）：更少的假设更好；
- **波普尔**（可证伪性）：更易被否证的规则更好；
- **拉卡托斯**（研究纲领）：能解释更多已有现象更好；
- **库恩**（范式）：与当前理论的相容性更好。

**⚠ 本框架不裁决「哪个权重更好」**——那是使用者的选择，
本框架只提供「评价量的注册表」+「**偏序**」（不是全序：不同量纲不可比）。

**⟹ 「可增删改」的实现**：`Eval : Type` 是**任意**的，
新评价量放进 `Eval` 即可，不改框架。 -/
class RuleEvaluation (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- **评价量的载体**（可增删改：用一个 `Type` 表示所有评价量）。 -/
  Eval : Type
  /-- **每个规则给出一组评价量**。 -/
  eval : Rule C X Y → Eval
  /-- **评价量上的偏序**（不是全序：不同量纲不可比）。 -/
  le : Eval → Eval → Prop
  /-- 偏序的自反性。 -/
  le_refl : ∀ e, le e e
  /-- 偏序的传递性。 -/
  le_trans : ∀ a b c, le a b → le b c → le a c

/-- ⭐ **「更好的规则」的定义**：在偏序下**严格更大**。

**⚠ 注意这里 `Better r₁ r₂` 读作「`r₁` 严格优于 `r₂`」**：
即 `eval r₂ ≤ eval r₁` 且**并非** `eval r₁ ≤ eval r₂`。
（若把方向读反，`better_irrefl` / `better_trans` 依然成立，但语义会错。） -/
def Better {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [RuleEvaluation C X Y] (r₁ r₂ : Rule C X Y) : Prop :=
  RuleEvaluation.le (RuleEvaluation.eval r₂) (RuleEvaluation.eval r₁)
    ∧ ¬ RuleEvaluation.le (RuleEvaluation.eval r₁) (RuleEvaluation.eval r₂)

/-- ⭐ **`Better` 是严格偏序**（不自反）。

**证明真的用了 `le` 的反自反性**（从 `le_refl` 之外无从得到）：
假设 `Better r r`，则第二分量为 `¬ le e e`，与 `le_refl e` 冲突。 -/
theorem better_irrefl {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [RuleEvaluation C X Y] (r : Rule C X Y) : ¬ Better r r := by
  rintro ⟨_, h2⟩
  exact h2 (RuleEvaluation.le_refl _)

/-- ⭐ **`Better` 传递**。

**证明真的用了 `le_trans`**（两次）：`r₁` 优于 `r₂`、`r₂` 优于 `r₃`
⟹ `eval r₃ ≤ eval r₁`；若非 `eval r₁ ≤ eval r₃` 不成立，
则由 `le_trans` 得 `eval r₁ ≤ eval r₂`，与 `r₁` 优于 `r₂` 冲突。 -/
theorem better_trans {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [RuleEvaluation C X Y] (r₁ r₂ r₃ : Rule C X Y)
    (h12 : Better r₁ r₂) (h23 : Better r₂ r₃) : Better r₁ r₃ := by
  refine ⟨RuleEvaluation.le_trans _ _ _ h23.1 h12.1, ?_⟩
  intro h
  exact h12.2 (RuleEvaluation.le_trans _ _ _ h h23.1)

/-- ⭐ **`Better` 不对称**（严格偏序的另一半）。

**证明结构**：`h : Better r₁ r₂` 展开为 `e₂ ≤ e₁ ∧ ¬ e₁ ≤ e₂`；
`Better r₂ r₁` 展开为 `e₁ ≤ e₂ ∧ ¬ e₂ ≤ e₁`。
把后者的第一分量代入前者的第二分量即得矛盾。
**（不需 `le_trans`，也不需 `le_refl`——只用定义。
但**不是** `Iff.rfl`：它把两个**不同**的 `eval` 项联系起来。）** -/
theorem better_asymm {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [RuleEvaluation C X Y] {r₁ r₂ : Rule C X Y}
    (h : Better r₁ r₂) : ¬ Better r₂ r₁ := by
  rintro ⟨h21, -⟩
  exact h.2 h21

/-! ===========================================================================
  §1.1  ⭐ **「半启发式」的显式通道**：标量化的序嵌入桥

**作者裁决说「规则的评价属于半启发式」**。半启发式的典型做法是
「把若干个量**加权求和**成一个标量再比较」。**本框架不内建**这种做法
（因为量纲不可比，加权求和是不可辩护的），而是提供**显式的桥**：
使用者给出一个标量函数 `f : Eval → ℝ`，若 `f` 是**序嵌入**，
则 `f e₂ < f e₁ ⟹ Better r₁ r₂`。

⟹ **加权求和仍然可用**，但它是**使用者的 `f`**，不是框架的隐含假设。
这正是「半启发式辅助」在本框架中的**唯一合法入口**。
  =========================================================================== -/

/-- ⭐ **标量化桥**：若 `f` 是 `le` 到 `(· ≤ ·)` 的**序嵌入**（双向），
则 `f e₂ < f e₁ ⟹ Better r₁ r₂`。

**⚠ 为何需要双向（`↔`）而非单向**：`Better` 的第二分量是**否定式**
`¬ le e₁ e₂`，要从 `f e₁ ≤ f e₂` 的反面得到它，就必须能**反向**从 `f` 的序
回到 `le` 的序。单向单调**不足以**推出否定式（这正是初稿失败的原因）。

注意方向：`f e₂ < f e₁`（`f` **大**的更好）⟺ `r₁` 严格优于 `r₂`。 -/
theorem better_of_scalar {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [RuleEvaluation C X Y] (f : RuleEvaluation.Eval (C := C) (X := X) (Y := Y) → ℝ)
    (hf : ∀ a b, RuleEvaluation.le (C := C) (X := X) (Y := Y) a b ↔ f a ≤ f b)
    (r₁ r₂ : Rule C X Y)
    (hlt : f (RuleEvaluation.eval r₂) < f (RuleEvaluation.eval r₁)) :
    Better r₁ r₂ := by
  refine ⟨(hf _ _).mpr (le_of_lt hlt), ?_⟩
  intro h
  exact absurd ((hf _ _).mp h) (not_le.mpr hlt)

/-! **（此处初稿有一个 `... : True := trivial` 的「非空性见证」引理，已删除）**

**为何删除**：那是**空命题**，正是本项目禁止的「假定理」。
本文件**不保留**任何空命题。
`better_of_scalar` 的**可应用性**已由下面的 `better_of_scalar_realEval`
**真实见证**（它在 `realEval` 上真的用到 `better_of_scalar` 造出一个 `Better`）。 -/


/-! ===========================================================================
  §1.2  ⭐ **现存实例**：`Eval := ℝ`、`le := (· ≤ ·)`、`eval` 任意

**这一节存在的唯一目的**：证明 §1 的框架**不是空框架**
（否则「可增删改」是空话，`Better` 可能是空关系）。 -/

/-- ⭐ **实数实例**：`Eval := ℝ`、`le := (· ≤ ·)`、`eval := u`。

`u : Rule C X Y → ℝ` 是使用者给的任意标量评价量
（**例如**某个加权求和，**例如** docs 里说的「半启发式」组合）。 -/
@[instance_reducible]
noncomputable def realEval {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (u : Rule C X Y → ℝ) : RuleEvaluation C X Y where
  Eval := ℝ
  eval := u
  le := (· ≤ ·)
  le_refl := fun _ => le_refl _
  le_trans := fun _ _ _ hab hbc => le_trans hab hbc

/-- ⭐ **实数实例上的 `Better` 就是 `<`**（这是「不退化」的**判定性证据**：
`Better` 在实数实例上**恰等于** `u r₂ < u r₁`，既非空也非全）。 -/
theorem realEval_better_iff {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (u : Rule C X Y → ℝ) (r₁ r₂ : Rule C X Y) :
    @Better C X Y _ _ (realEval u) r₁ r₂ ↔ u r₂ < u r₁ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact lt_of_le_of_ne h1 (fun hh => h2 (le_of_eq hh.symm))
  · intro h
    exact ⟨le_of_lt h, not_le.mpr h⟩

/-- **推论**：实数实例下 `Better` **确实能取到**（举一个具体例子）。 -/
theorem better_lt_real {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (u : Rule C X Y → ℝ) (r₁ r₂ : Rule C X Y) (h : u r₂ < u r₁) :
    @Better C X Y _ _ (realEval u) r₁ r₂ :=
  (realEval_better_iff u r₁ r₂).mpr h

/-- ⭐ **`better_of_scalar` 在实数实例上的真实应用**（非空性见证）。

取 `f := id`（在 `realEval u` 下 `Eval` 就是 `ℝ`，`le` 就是 `(· ≤ ·)`），
序嵌入前件 `∀ a b, a ≤ b ↔ id a ≤ id b` 由 `Iff.rfl` 给出，
于是 `better_of_scalar` **真的跑起来了**并给出 `Better`。

**⚠ 这条与 `better_lt_real` 结论相同但**路径不同**：
`better_lt_real` 走 `realEval_better_iff`（`Better` 的展开），
本条走 `better_of_scalar`（§1.1 的标量化桥）。
**两者一致** ⟹ 标量化桥与框架本身**不冲突**。 -/
theorem better_of_scalar_realEval {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (u : Rule C X Y → ℝ) (r₁ r₂ : Rule C X Y) (h : u r₂ < u r₁) :
    @Better C X Y _ _ (realEval u) r₁ r₂ :=
  have hf : ∀ a b : @RuleEvaluation.Eval C X Y _ _ (realEval u),
      @RuleEvaluation.le C X Y _ _ (realEval u) a b ↔ (id a : ℝ) ≤ id b := fun _ _ => Iff.rfl
  @better_of_scalar C X Y _ _ (realEval u) id hf r₁ r₂ h

/-! ===========================================================================
  §2  四个科学哲学评价量（**注释草案，未形式化**，可增删改）

**⚠ 下面四条是注释，不是 Lean 定义。**

**为什么不做**：`Rule` 只有 `kernel`，**没有前件、没有后件、没有概率空间 `P`**。
硬写只能伪造类型或引入不可证前件。**如实登记为开放问题 5.7 的一部分。**

```lean
/-- **奥卡姆剃刀**（简洁性）：前件越少越好。
    `simplicity(R) := 1 / (|R.antecedent| + 1)` —— 越大越简洁。
    ⚠ 需要 `Rule` 有前件及其大小 —— **本仓库的 `Rule` 没有前件**。 -/
-- noncomputable def simplicity {C X Y} (r : Rule C X Y) : ℝ := ...

/-- **波普尔**（可证伪性）：越不自信越好（越易被否证）。
    `falsifiability(R) := 1 - conf(R)` —— 越大越可证伪。
    ⚠ 需要 `conf` —— **本仓库无 `Rule` 上的 `conf`**。 -/
-- noncomputable def falsifiability {C X Y} (r : Rule C X Y) : ℝ := ...

/-- **拉卡托斯**（覆盖率）：`coverage(R) := supp(R)`。
    净版 `:1839` 已明说「覆盖度 = 满足前件的样本比例」与 `supp` 同义。
    ⚠ 需要 `supp` —— **本仓库无 `Rule` 上的 `supp`**。 -/
-- noncomputable def coverage {C X Y} (r : Rule C X Y) : ℝ := ...

/-- **库恩**（一致性）：`consistency(R) := lift(R)`（与现有理论的相容）。
    ⚠ 需要 `lift` —— **本仓库无 `Rule` 上的 `lift`**。 -/
-- noncomputable def consistency {C X Y} (r : Rule C X Y) : ℝ := ...
```

**若日后 `supp` / `conf` / `lift` 被形式化**，按下面的方式**不改框架**地接入：

```lean
-- 只需换一个 `Eval` 类型，框架代码一行不改：
noncomputable def fourQuantities {C X Y} [...] : RuleEvaluation C X Y where
  Eval := ℝ × ℝ × ℝ × ℝ
  eval r := (simplicity r, falsifiability r, coverage r, consistency r)
  le := fun a b => a.1 ≤ b.1 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2.1 ≤ b.2.2.1 ∧ a.2.2.2 ≤ b.2.2.2
  le_refl := ...
  le_trans := ...
```
**⟹ 这正是「后续可能增删改」的具体含义**：新量进 `Eval`，框架不变。
  =========================================================================== -/

end RuleEval

end Fate
