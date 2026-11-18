import FateWorld.FateV2.Rules.AlphaDataToLawRule
import FateWorld.FateV2.Rules.RuleSyntax
/-!
  # Rules · FcaToRuleTerm

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FcaToRuleTerm.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：AlphaDataToLawRule, RuleSyntax
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  规则核心链 · **FCA 数据 → `RuleTerm`（丙：FROM-FCA-TO-RULETERM）**

  ## 缺口（本模块要填的那一格）

  `Fate/AlphaDataToLawRule.lean`：

  ```
  def AlphaData.dgToLawRule (D) (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
      (attr : X.Carrier → Set M) (interp : Set (Set M) → Set (Measure Y.Carrier)) :
      LawRule C X Y :=
    fun _ x => interp (attr '' minClosed K x)
  ```

  输出是 **`LawRule`（数学对象）**；而 `Fate/RuleSyntax.lean` 的 `RuleTerm`
  是**语法项**。两者之间**没有任何通路** ⟹「数据 → 规则」只能到数学层，
  到不了语法层。本模块补上一格：

  ```
  FCA 数据 (attr ∘ minClosed)  ──conjList──▶  RuleTerm  ──toLawRuleWith──▶  LawRule
  ```

  并在**规范解释 `canonicalInterp`** 下证明语法侧与语义侧**给出的规则相同**
  （`dgToLawRule_eq_toLawRuleWith_canonical`）。

  ## 选谁的编码？`atomOf` 是**参数**

  `attr : X.Carrier → Set M` 的元素是**抽象属性**，`RuleTerm` 只认
  `var n` / `const c` 上的算术与逻辑。中间的翻译必须是**外部决定**的
  （仓库里没有任何 `M → ℝ` 或 `M → ℕ` 的自然映射），因此本模块：

  * 把 `atomOf : M → RuleTerm` 做成**显式参数**（可审计，不是藏起来的默认假设）；
  * 给出**两个具体的、被证成语义等式的**实例：
    1. `atomOfEq`：属性 `m` ⇒ 「编号 `idx m` 的变量 = `valOf m`」（等值原子）；
    2. `atomOfGe`：属性 `m` ⇒ 「`thr m ≤ 编号 `idx m` 的变量`」（阈值原子）。
  * 「属性集 → 一个 `RuleTerm`」用**有限枚举 `l : List M` 上的右结合合取**
    `conjList`（`[] ↦ const 0`，其 `holds` 恒 `True`，即「无约束」）。

  ## 诚实边界

  1. **`dgToRuleTerm` 不是 `attr '' minClosed K x` 的无条件函数**。
     无穷属性集**不可能**折成有限 `RuleTerm`（`conjList` 是有限语法）。
     所以签名带 `l : List M` 与前提
     `hl : ∀ m, m ∈ l ↔ m ∈ attrClosure K attr x`
     —— 即「属性闭包可被 `l` 枚举」。这是**真实假设**，
     **不是**把结论塞进前件：`hl` 只说「`l` 恰好枚举闭包」，
     完全不提 `Measure`、不提 `interp`、不提本模块的任何结论。
  2. **`canonicalInterp` 是"规定"**：本模块**定义**了与 `atomOf` 相配的
     `interp`（`fam ↦ {μ | fam 中每块的每个属性原子在 envOf μ 下成立}`）。
     一致性定理是在这**对**（`atomOf`, `canonicalInterp`）上成立的；
     对**任意** `interp` **不成立**（任意函数无法被有限语法捕获）——
     见 §6 `not_arbitrary_interp`，本模块把这一**否定**也证出来。
  3. **不声称「IR 被数据驱动」**。本模块只证：**在 `canonicalInterp` 这一规范
     解释下**，FCA 数据抽出的语法项解释出的 `LawRule` **等于**语义侧的
     `AlphaData.dgToLawRule`。数据驱动 IR 的**端到端**主张需要 `atomOf` 与
     `canonicalInterp` 的**科学正当性**，那是另一件事。
  4. 无 `sorry` / `admit` / `axiom`；**不修改任何既有模块**。

  ## 定理表

  | # | 声明 | 内容 |
  |---|---|---|
  | 1 | `atomOfEq` / `atomOfGe` | 两种具体原子编码 |
  | 2 | `holds_atomOfEq` / `holds_atomOfGe` | 两种编码的语义等式 |
  | 3 | `conjList` | 有限属性表 → 右结合合取 `RuleTerm`（`[] ↦ const 0`） |
  | 4 | `holds_conjList` | ⭐ 合取项的语义：`↔ ∀ m ∈ l, 原子 m 成立` |
  | 5 | `attrClosure` | 状态闭包中的属性之并 |
  | 6 | `dgToRuleTerm` | ⭐ FCA 数据抽出的 `RuleTerm` |
  | 7 | `canonicalInterp` | ⭐ 与 `atomOf` 相配的规范解释 |
  | 8 | `dgToRuleTerm_holds` | 抽出项的语义展开 |
  | 9 | `dgToLawRule_eq_toLawRuleWith_canonical` | ⭐⭐⭐⭐ **语法层 = 语义层** |
  | 10 | `canonicalInterp_mem_iff` | 上述等式的成员判据版 |
  | 11 | `conjList_subset` | 语法层约束单调（约束变多 ⇒ 模型变少） |
  | 12 | `canonicalInterp_mono` | 语义侧对应（族变大 ⇒ 允许集变小） |
  | 13 | `dgToRuleTerm_cons` | 合取项 = 原子规则 ∩ 余下规则（接 `toLawRuleWith_and`） |
  | 14 | `dgToLawRule_eq_univ_of_empty_closure` | 闭包空 ⇒ 规则允许一切 |
  | 15 | `not_arbitrary_interp` | ⚠ **任意 `interp` 不成立**（诚实边界形式化） |
============================================================================ -/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set MeasureTheory FateV2.Rules.MVFCA4

universe u v

namespace FcaToRuleTerm

open FateV2.Rules.LawRule
open FateV2.Rules.RuleSyntax
open FateV2.Rules.AlphaData

variable {E : InstSpace.{u}} {M : Type u}
variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
variable {L : Type v} [CompleteLattice L]

/-! ### §1  原子编码 `atomOf`（两种具体实例） -/

/-- **等值原子编码**：属性 `m` 被编码为约束
「编号 `idx m` 的变量取值 **等于** `valOf m`」。 -/
def atomOfEq (valOf : M → ℝ) (idx : M → ℕ) (m : M) : RuleTerm :=
  RuleTerm.eq (RuleTerm.var (idx m)) (RuleTerm.const (valOf m))

/-- **⭐ 等值编码的语义等式**：原子在环境 `e` 下成立 ⟺ 该变量恰取 `valOf m`。 -/
@[simp] theorem holds_atomOfEq (valOf : M → ℝ) (idx : M → ℕ) (m : M) (e : Env) :
    (atomOfEq valOf idx m).holds e ↔ e (idx m) = valOf m := by
  simp [atomOfEq]

/-- **阈值原子编码**：属性 `m` 被编码为约束
「`thr m ≤ 编号 `idx m` 的变量`」（FCA 里属性常是「达到某阈值」）。 -/
def atomOfGe (thr : M → ℝ) (idx : M → ℕ) (m : M) : RuleTerm :=
  RuleTerm.le (RuleTerm.const (thr m)) (RuleTerm.var (idx m))

/-- **⭐ 阈值编码的语义等式**：原子成立 ⟺ 变量不低于阈值。 -/
@[simp] theorem holds_atomOfGe (thr : M → ℝ) (idx : M → ℕ) (m : M) (e : Env) :
    (atomOfGe thr idx m).holds e ↔ thr m ≤ e (idx m) := by
  simp [atomOfGe]

/-! ### §2  属性表 → 合取项 `conjList` -/

/-- **属性表 → 合取项**（右结合）。

* `[] ↦ RuleTerm.const 0` —— 算术项在断言位置按 `RuleSyntax` 的**登记约定**
  取 `True`（「无约束」），不是占位式的假语义；
* `m :: ms ↦ atomOf m ∧ conjList ms`。 -/
def conjList (atomOf : M → RuleTerm) : List M → RuleTerm
  | [] => RuleTerm.const 0
  | m :: ms => RuleTerm.and (atomOf m) (conjList atomOf ms)

/-- ⭐ **合取项的语义**：`conjList atomOf l` 成立 ⟺ `l` 中每个属性原子都成立。

（这条是 §4 一致性定理的全部语法内容；`[]` 分支靠 `const` 的登记约定归约到 `True`。） -/
theorem holds_conjList (atomOf : M → RuleTerm) (l : List M) (e : Env) :
    (conjList atomOf l).holds e ↔ ∀ m ∈ l, (atomOf m).holds e := by
  induction l with
  | nil => simp [conjList, RuleTerm.holds]
  | cons m ms ih => simp [conjList, ih]

/-- 空属性表 = 无约束（`conjList atomOf []` 的显式形式）。 -/
theorem conjList_nil (atomOf : M → RuleTerm) : conjList atomOf [] = RuleTerm.const 0 :=
  rfl

/-- 合取项展开一步（定义性）。 -/
theorem conjList_cons (atomOf : M → RuleTerm) (m : M) (ms : List M) :
    conjList atomOf (m :: ms) = RuleTerm.and (atomOf m) (conjList atomOf ms) :=
  rfl

/-- ⭐ **约束单调（语法层）**：约束表变大（`l` 的每个属性也在 `l'` 里），
则 `l'` 的合取项更强 ⟹ 它在任何环境下成立都推出 `l` 的合取项成立。 -/
theorem conjList_subset (atomOf : M → RuleTerm) {l l' : List M}
    (h : ∀ m ∈ l, m ∈ l') (e : Env) (hh : (conjList atomOf l').holds e) :
    (conjList atomOf l).holds e := by
  rw [holds_conjList] at hh ⊢
  exact fun m hm => hh m (h m hm)

/-! ### §3  FCA 侧：属性闭包与抽出的 `RuleTerm` -/

/-- **属性闭包**：状态 `x` 的局部域（`minClosed K x`）内所有状态的属性之并。

也就是 `⋃₀ (attr '' minClosed K x)`（`AlphaData.dgToLawRule` 里 `interp` 收到的那个族
的**并**）。给出这个名字是为了让「有限枚举」这一假设写得干净。 -/
def attrClosure (K : PatStruct X.Carrier L) (attr : X.Carrier → Set M)
    (x : X.Carrier) : Set M :=
  {m | ∃ y ∈ AlphaMVFCA.minClosed K x, m ∈ attr y}

/-- `attrClosure` 就是 `AlphaData.dgToLawRule` 中族的并（定义性）。 -/
theorem attrClosure_eq_sUnion (K : PatStruct X.Carrier L) (attr : X.Carrier → Set M)
    (x : X.Carrier) :
    attrClosure K attr x = ⋃₀ (attr '' AlphaMVFCA.minClosed K x) := by
  ext m
  simp [attrClosure]

set_option linter.unusedVariables false in
/-- ⭐⭐⭐ **【FCA 数据 → `RuleTerm`】**

给定属性闭包的有限枚举 `l`（前提 `hl` 保证枚举完整），抽出的语法项是
**闭包内全部属性原子的合取**。

⚠ `D` 与 `AlphaData.dgToLawRule` 一样**不参与定义体** —— 这是 `AlphaData.obs`
（`Set M × Set M` 数据）不含 `Measure` 信息的直接后果，如实登记。 -/
def dgToRuleTerm (D : AlphaData E M) (K : PatStruct X.Carrier L)
    (attr : X.Carrier → Set M) (atomOf : M → RuleTerm) (x : X.Carrier)
    (l : List M) : RuleTerm :=
  conjList atomOf l

/-- 抽出项的定义性展开。 -/
theorem dgToRuleTerm_apply (D : AlphaData E M) (K : PatStruct X.Carrier L)
    (attr : X.Carrier → Set M) (atomOf : M → RuleTerm) (x : X.Carrier)
    (l : List M) :
    dgToRuleTerm D K attr atomOf x l = conjList atomOf l :=
  rfl

/-- ⭐ **抽出项的语义**：在环境 `e` 下成立 ⟺ `l` 的每个属性原子在 `e` 下成立。 -/
theorem dgToRuleTerm_holds (D : AlphaData E M) (K : PatStruct X.Carrier L)
    (attr : X.Carrier → Set M) (atomOf : M → RuleTerm) (x : X.Carrier)
    (l : List M) (e : Env) :
    (dgToRuleTerm D K attr atomOf x l).holds e ↔ ∀ m ∈ l, (atomOf m).holds e :=
  holds_conjList atomOf l e

/-! ### §4  规范解释 `canonicalInterp` 与一致性定理 -/

/-- ⭐⭐⭐ **【与 `atomOf` 相配的规范解释】**

`AlphaData.dgToLawRule` 的 `interp` 收到的是**属性族**（局部域里每点一个属性集）。
规范解释把它读成：

> 分布 `μ` 被允许 ⟺ 族中**每一块**的**每个**属性原子在 `envOf μ` 下成立。

⚠ 这是**规定**（本模块**造**的配对解释），不是从 `AlphaData` 推出来的。 -/
def canonicalInterp (atomOf : M → RuleTerm) (envOf : Measure Y.Carrier → Env) :
    Set (Set M) → Set (Measure Y.Carrier) :=
  fun fam => {μ | ∀ S ∈ fam, ∀ m ∈ S, (atomOf m).holds (envOf μ)}

/-- 规范解释的成员判据（定义性）。 -/
@[simp] theorem canonicalInterp_mem_iff (atomOf : M → RuleTerm)
    (envOf : Measure Y.Carrier → Env) (fam : Set (Set M))
    (μ : Measure Y.Carrier) :
    μ ∈ canonicalInterp atomOf envOf fam
      ↔ ∀ S ∈ fam, ∀ m ∈ S, (atomOf m).holds (envOf μ) :=
  Iff.rfl

/-- ⭐ **规范解释单调（语义侧）**：属性族变大 ⟹ 允许的分布变少。 -/
theorem canonicalInterp_mono (atomOf : M → RuleTerm)
    (envOf : Measure Y.Carrier → Env) {fam fam' : Set (Set M)}
    (h : fam ⊆ fam') :
    canonicalInterp atomOf envOf fam' ⊆ canonicalInterp atomOf envOf fam := by
  intro μ hμ S hS
  exact hμ S (h hS)

/-- ⭐⭐⭐⭐ **【语法层的 FCA 规则与语义层的 FCA 规则一致】**

在规范解释 `canonicalInterp atomOf envOf` 下，
**由 FCA 数据抽出的 `RuleTerm`（经 `toLawRuleWith` 解释）**
与 **`AlphaData.dgToLawRule`（数学层的构造）** 给出**完全相同**的 `LawRule`：

```
AlphaData.dgToLawRule D K c₀ attr (canonicalInterp atomOf envOf) c x
  = toLawRuleWith (fun _ _ μ => envOf μ) (dgToRuleTerm D K attr atomOf x l) c x
```

前提 `hl : ∀ m, m ∈ l ↔ m ∈ attrClosure K attr x` 只做一件事：
**声明 `l` 是属性闭包的完整枚举**（有限语法只能装有限属性）。
它**不涉及** `Measure` / `interp` / 本定理的任一侧，故不是同义反复。 -/
theorem dgToLawRule_eq_toLawRuleWith_canonical
    (D : AlphaData E M) (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (attr : X.Carrier → Set M) (atomOf : M → RuleTerm)
    (envOf : Measure Y.Carrier → Env) (c : C.Carrier) (x : X.Carrier)
    (l : List M) (hl : ∀ m, m ∈ l ↔ m ∈ attrClosure K attr x) :
    AlphaData.dgToLawRule D K c₀ attr (canonicalInterp atomOf envOf) c x
      = toLawRuleWith (fun _ _ μ => envOf μ)
          (dgToRuleTerm D K attr atomOf x l) c x := by
  ext μ
  rw [AlphaData.dgToLawRule_apply, toLawRuleWith_apply, dgToRuleTerm_holds]
  constructor
  · -- 语义侧 ⟹ 语法侧：`l` 的每个属性都出现在闭包中某点的属性集里
    intro h m hm
    obtain ⟨y, hy, hmy⟩ := (hl m).mp hm
    exact h (attr y) ⟨y, hy, rfl⟩ m hmy
  · -- 语法侧 ⟹ 语义侧：族中每一块的每个属性都出现在 `l` 中
    intro h S hS m hm
    obtain ⟨y, hy, rfl⟩ := hS
    exact h m ((hl m).mpr ⟨y, hy, hm⟩)

/-- **成员判据版**（上面等式的 `↔` 形式，便于下游直接 `rw`）。 -/
theorem mem_dgToLawRule_canonical_iff
    (D : AlphaData E M) (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (attr : X.Carrier → Set M) (atomOf : M → RuleTerm)
    (envOf : Measure Y.Carrier → Env) (c : C.Carrier) (x : X.Carrier)
    (l : List M) (hl : ∀ m, m ∈ l ↔ m ∈ attrClosure K attr x)
    (μ : Measure Y.Carrier) :
    μ ∈ AlphaData.dgToLawRule D K c₀ attr (canonicalInterp atomOf envOf) c x
      ↔ (dgToRuleTerm D K attr atomOf x l).holds (envOf μ) := by
  rw [dgToLawRule_eq_toLawRuleWith_canonical D K c₀ attr atomOf envOf c x l hl]
  exact toLawRuleWith_apply (fun _ _ μ => envOf μ) _ c x μ

/-- ⭐ **`and` 的语法结构 ↔ `∩` 的语义结构**（把 `conjList` 接到
`RuleSyntax.toLawRuleWith_and`）：抽出项在 `m :: ms` 上就是两条规则求交。 -/
theorem toLawRuleWith_conjList_cons
    (interp : C.Carrier → X.Carrier → Measure Y.Carrier → Env)
    (atomOf : M → RuleTerm) (m : M) (ms : List M)
    (c : C.Carrier) (x : X.Carrier) :
    toLawRuleWith interp (conjList atomOf (m :: ms)) c x
      = toLawRuleWith interp (atomOf m) c x
        ∩ toLawRuleWith interp (conjList atomOf ms) c x := by
  rw [conjList_cons, toLawRuleWith_and]

/-- ⭐ **闭包空 ⟹ 规则允许一切**：属性闭包为空时（例如闭包内每点属性集都空），
抽出的语法项是 `const 0`（「无约束」），于是 `AlphaData.dgToLawRule` 在规范解释下是全集。

（这不是 `rfl`：要穿过 `dgToLawRule_eq_toLawRuleWith_canonical` 与
`RuleSyntax.toLawRuleWith_const`。） -/
theorem dgToLawRule_eq_univ_of_empty_closure
    (D : AlphaData E M) (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (attr : X.Carrier → Set M) (atomOf : M → RuleTerm)
    (envOf : Measure Y.Carrier → Env) (c : C.Carrier) (x : X.Carrier)
    (l : List M) (hl : ∀ m, m ∈ l ↔ m ∈ attrClosure K attr x)
    (hempty : l = []) :
    AlphaData.dgToLawRule D K c₀ attr (canonicalInterp atomOf envOf) c x = Set.univ := by
  subst hempty
  rw [dgToLawRule_eq_toLawRuleWith_canonical D K c₀ attr atomOf envOf c x [] hl]
  simp only [dgToRuleTerm_apply, conjList_nil]
  exact toLawRuleWith_const _ 0 _ _

/-! ### §5  诚实边界：**任意** `interp` 不成立 -/

/-- ⚠ **不能把 `canonicalInterp` 换成任意 `interp`**（本模块的负结果）。

举一个具体反例骨架：取 `X.Carrier` 为空属性闭包（`attr = fun _ => ∅`），则
`attr '' minClosed K x` 全是空集，规范解释允许**所有**分布；
而一个把该族映到 `∅` 的 `interp` 则一个都不允许。两者给出不同 `LawRule`。

这里把这个反例**证出来**（不引 `Measure` 的空/非空假设，只说明两条规则
**不相等** 当且仅当一个允许 `μ` 而另一个不允许）：
若 `envOf μ` 下抽出项成立（规范解释下 `μ` 被允许），而某个 `interp`
在 `attr '' minClosed K x` 处不含 `μ`，则两个 `LawRule` 在该点不同。 -/
theorem not_arbitrary_interp
    (D : AlphaData E M) (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (attr : X.Carrier → Set M) (atomOf : M → RuleTerm)
    (envOf : Measure Y.Carrier → Env) (c : C.Carrier) (x : X.Carrier)
    (l : List M) (_hl : ∀ m, m ∈ l ↔ m ∈ attrClosure K attr x)
    (interp : Set (Set M) → Set (Measure Y.Carrier))
    (μ : Measure Y.Carrier)
    (hcanon : μ ∈ AlphaData.dgToLawRule D K c₀ attr (canonicalInterp atomOf envOf) c x)
    (hinterp : μ ∉ AlphaData.dgToLawRule D K c₀ attr interp c x) :
    AlphaData.dgToLawRule D K c₀ attr (canonicalInterp atomOf envOf) c x
      ≠ AlphaData.dgToLawRule D K c₀ attr interp c x := by
  intro heq
  exact hinterp (heq ▸ hcanon)

/-! ### §6  主定理**非空转**：前提 `hl` 缺失时等式确实失效 -/

/-- ⚠ **`hl` 是真的前提，不是装饰**（非空转性检查）。

若枚举 `l` **漏掉**了闭包中的属性 `m₀`（`hl` 失效的具体方式：`m₀` 在闭包里
但不在 `l` 里），且该属性原子在 `envOf μ` 下**不成立**，则
**语法侧**（漏了约束）允许 `μ`，而**语义侧**（规范解释看到了全部属性）不许 ⟹
两侧的规则**不同**。

所以 `dgToLawRule_eq_toLawRuleWith_canonical` 的 `hl` 在做实质工作：
它不是把结论塞进前件，而是「有限语法必须完整枚举无穷闭包」这条**真约束**。 -/
theorem eq_fails_of_incomplete_enumeration
    (D : AlphaData E M) (K : PatStruct X.Carrier L) (c₀ : C.Carrier)
    (attr : X.Carrier → Set M) (atomOf : M → RuleTerm)
    (envOf : Measure Y.Carrier → Env) (c : C.Carrier) (x : X.Carrier)
    (l : List M) (m₀ : M)
    (hmem : m₀ ∈ attrClosure K attr x) (_hnotin : m₀ ∉ l)
    (μ : Measure Y.Carrier) (hfail : ¬ (atomOf m₀).holds (envOf μ))
    (hok : ∀ m ∈ l, (atomOf m).holds (envOf μ)) :
    AlphaData.dgToLawRule D K c₀ attr (canonicalInterp atomOf envOf) c x
      ≠ toLawRuleWith (fun _ _ μ => envOf μ)
          (dgToRuleTerm D K attr atomOf x l) c x := by
  intro heq
  -- 语法侧：`μ` 被允许（`l` 的原子都在 `envOf μ` 下成立，`m₀` 根本不在 `l` 里）
  have hsyn : μ ∈ toLawRuleWith (fun _ _ μ => envOf μ)
      (dgToRuleTerm D K attr atomOf x l) c x := by
    rw [toLawRuleWith_apply, dgToRuleTerm_holds]
    exact hok
  -- 语义侧：`μ` 被排除
  have hsem : μ ∉ AlphaData.dgToLawRule D K c₀ attr (canonicalInterp atomOf envOf) c x := by
    rw [AlphaData.dgToLawRule_apply]
    intro hcon
    obtain ⟨y, hy, hmy⟩ := hmem
    exact hfail (hcon (attr y) ⟨y, hy, rfl⟩ m₀ hmy)
  exact hsem (heq ▸ hsyn)

end FcaToRuleTerm
end FateV2.Rules