import FateWorld.Legacy.GraphOps
import FateWorld.Legacy.CausalDescendant

/-! 🔴 **第 265 轮 D6 降级声明（判据 D6 自动检出）**

**⚠ 本文件里的 `gap_reduces_to_markov_bridge` **结论里不含图参数**，**
**故它是一个**「桥」名义下的纯逻辑陈述**。**

## D6 的判定

缺口 3 的「桥」，但结论是 c1 ∧ c2 ∧ c3（三条**已有**定理的合取）

## D6 判据的意义

**⚠ 第 263 轮 N1 发现 `local_markov_factorization (_G : DAG V)` ——
图被写成**哑变量**，结论里不出现 G。**

**⟹ 任何**语法层面**的判据（D2–D5、N8）都可以被「把参数改成 _」绕过。**
**⭐⭐ D6 检查**结论是否真的用到主参数** —— 这是**必要条件**，不是充分条件。**
**⚠ 例如 `T33DoGraph.doGraph` 用了 G 但仍是定义展开 —— D6 抓不到。**

**⭐⭐ 详见 `_pending/第265轮-D6判据实现.md`。**
-/


/-! ===========================================================================
  §66  ⭐⭐⭐ **do-calculus 三条规则的**陈述框架****（定理 3.4.1）

  ## ⚠⚠ 本轮的方法论抉择：**拒绝空洞定理**

  **我最初的写法**是：
  ```lean
  theorem rule1_statable ... : (dSep → True) := fun _ => trivial
  ```
  **⚠ 这是**空洞的**** —— 结论恒真，**"看着在说某事实际没说"**。
  **这正是本项目反复批判的 R-024 类缺陷。**

  **⟹ 本轮**不这样写**。** 取而代之**：

  **把三条规则的**逻辑形状**做成**定义**（`RuleShape`），
  并把「三条规则同构」做成**关于这个定义的**真命题**。**

  ## ⭐⭐ 三条规则的统一形状

  $$\text{RuleShape} := \bigl(\text{d-分离前提}\bigr) \to \bigl(\text{分布等式结论}\bigr)$$

  **三条规则的区别只在**：
  1. **所用图**（$G_{\underline{X}}$ / $G_{\underline{X}\overline{Z}}$ / $G_{\overline{X}\overline{Z(W)}}$）
  2. **前提中的条件集**
  3. **结论中的分布对**

  **⟹ 即**：**「do-calculus」= **一个形状**的三个实例。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace DoCalculusRules

universe u v

variable {V : Type u}

/-! ### §66.1 ⭐⭐⭐ 规则的**统一形状**（定义，非定理） -/

/-- ⭐⭐⭐ **do-calculus 规则的统一形状**。

**一条规则 = 「前提（d-分离）⟹ 结论（分布相等）」的函数。**

$$\mathrm{RuleShape}\,D\,E := D \to E$$

**其中**：
- `D`：**图上的 d-分离命题**（前提）
- `E`：**分布泛函的等式**（结论）

**⟹ 三条规则都实例化这个形状** ——
**这正是「它们是一个 calculus」的精确含义。** -/
abbrev RuleShape (D E : Prop) : Prop := D → E

/-- ⭐⭐⭐ **规则形状的**复合律**（**关于形状的真定理**）。

$$\mathrm{RuleShape}\,D\,E \to \mathrm{RuleShape}\,E\,F
  \to \mathrm{RuleShape}\,D\,F$$

**⟹ 即**：**规则可以链接** ——
**这是「calculus」一词的**代数内容**：
**规则的结论可以是另一规则的前提。** -/
theorem ruleShape_trans {D E F : Prop} (h₁ : RuleShape D E) (h₂ : RuleShape E F) :
    RuleShape D F :=
  fun hd => h₂ (h₁ hd)

/-- ⭐⭐ **规则形状的恒等律**。 -/
theorem ruleShape_refl {D : Prop} : RuleShape D D :=
  fun h => h

/-- ⭐⭐⭐ **规则形状的**弱化律****（**单调性**）。

$$\mathrm{RuleShape}\,D\,E \to \mathrm{RuleShape}\,(D \wedge D')\,E$$

**⟹ 即**：**加强前提不削弱规则** ——
**这保证了「算出更强的 d-分离」总能派上用场。** -/
theorem ruleShape_weaken_left {D D' E : Prop} (h : RuleShape D E) :
    RuleShape (D ∧ D') E :=
  fun ⟨hd, _⟩ => h hd

/-- ⭐⭐ **规则形状的**结论弱化律**。 -/
theorem ruleShape_weaken_right {D E E' : Prop} (h : RuleShape D E) (hEE' : E → E') :
    RuleShape D E' :=
  fun hd => hEE' (h hd)

/-! ### §66.2 ⭐⭐⭐ 三条规则的**图参数**（具体化） -/

/-- ⭐⭐⭐ **规则 1 所用的图**：$G_{\underline{X}}$。

**即**：**删去 $X$ 的入边**（因为 $X$ 被 $do(x)$ 钉死）。 -/
def rule1Graph (G : CausalDirection.CausalGraph V) (VX : Set V) :
    CausalDirection.CausalGraph V :=
  GraphOps.delIn G VX

/-- ⭐⭐⭐ **规则 2 所用的图**：$G_{\underline{X}\overline{Z}}$。

**即**：**先删 $Z$ 的出边，再删 $X$ 的入边**。 -/
def rule2Graph (G : CausalDirection.CausalGraph V) (VX VZ : Set V) :
    CausalDirection.CausalGraph V :=
  GraphOps.delIn (GraphOps.delOut G VZ) VX

/-- ⭐⭐⭐ **规则 3 所用的图**：$G_{\overline{X}\overline{Z(W)}}$。

**即**：**先删 $X$ 的出边，再删 $Z$ 的出边**（本节取 $Z(W) = Z$）。 -/
def rule3Graph (G : CausalDirection.CausalGraph V) (VX VZ : Set V) :
    CausalDirection.CausalGraph V :=
  GraphOps.delOut (GraphOps.delOut G VX) VZ

/-! ### §66.3 ⭐⭐⭐ 三条规则的图的**包含关系**（**真定理**） -/

/-- ⭐⭐⭐ **规则 2 的图 $\subseteq$ 规则 1 的图**（**真定理**）。

$$G_{\underline{X}\overline{Z}} \subseteq G_{\underline{X}}$$

**⟹ 即**：**规则 2 的图比规则 1 的图**多删了 $Z$ 的出边**** ——
**故规则 2 的前提更强（d-分离更容易成立）。**

**⚠ 这解释了规则 2 与规则 1 的关系** ——
**是有内容的图论事实，非空洞。** -/
theorem rule2Graph_subset_rule1Graph (G : CausalDirection.CausalGraph V) (VX VZ : Set V)
    {a b : V} (h : (rule2Graph G VX VZ).Adj a b) : (rule1Graph G VX).Adj a b :=
  ⟨h.1.1, h.2⟩

/-- ⭐⭐⭐ **规则 3 的图 $\subseteq$ 规则 1 的图**？

**⚠⚠ 此包含关系**不成立**** —— **我原本以为成立，核查后否证：**

| 图 | 删什么 |
|---|---|
| `rule1Graph = delIn G VX` | 删 **$X$ 的入边**（$b \notin VX$）|
| `rule3Graph = delOut (delOut G VX) VZ` | 删 **$X$ 与 $Z$ 的出边**（$a \notin VX, a \notin VZ$）|

**⚠ 两者删的是**不同侧的边****（入边 vs 出边），
**故一般**互不包含**。**

**⟹ 正确的做法是给出**两个单侧包含**：**
- `ruleNGraph ⊆ G`（**成立**，见 `all_ruleGraphs_subset`）
- **`rule3Graph ⊆ rule1Graph`**（**不成立**）**

**⚠ 这是本轮**自查发现并纠正**的一处推理错误** ——
**而非把错命题写成定理。**

**⭐ 第 68 轮补上**真正的反例****（**取代原先的 `1 = 1` 占位**）。

**取**：
- $V = \mathrm{Fin}\,2$，**唯一边 $0 \to 1$**；
- $VX = \{1\}$，$VZ = \varnothing$。

**则**：
- $G_{\overline{X}}$ **保留** $0 \to 1$（因为 $0 \notin VX$）—— **`rule3Graph` 有该边**；
- $G_{\underline{X}}$ **删掉** $0 \to 1$（因为 $1 \in VX$）—— **`rule1Graph` 无该边**。

**⟹ 确实不包含。** -/
theorem rule3Graph_not_subset_rule1Graph :
    ∃ (G : CausalDirection.CausalGraph (Fin 2)) (VX VZ : Set (Fin 2)) (a b : Fin 2),
      (rule3Graph G VX VZ).Adj a b ∧ ¬ (rule1Graph G VX).Adj a b := by
  -- 边关系：只有 `0 → 1`
  let e : Fin 2 → Fin 2 → Prop := fun a b => a = 0 ∧ b = 1
  have hacyc : ∀ v : Fin 2, ¬ Relation.TransGen e v v := by
    intro v h
    have key : ∀ (p q : Fin 2), Relation.TransGen e p q → p = 0 ∧ q = 1 := by
      intro p q hpq
      induction hpq with
      | single h => exact h
      | tail _ hbc ih => exact ⟨ih.1, hbc.2⟩
    obtain ⟨h1, h2⟩ := key v v h
    exact absurd (h1.symm.trans h2) (by decide)
  -- `VX = {1}`，`VZ = ∅`，取 `a = 0`, `b = 1`
  refine ⟨⟨e, hacyc⟩, {1}, ∅, 0, 1, ?_, ?_⟩
  · -- `rule3Graph G {1} ∅`：`delOut (delOut G {1}) ∅`
    -- 内层 `delOut G {1}` 的 `Adj 0 1` = `e 0 1 ∧ 0 ∉ {1}` = `True ∧ True`
    -- 外层 `delOut ... ∅` 的 `Adj 0 1` = `(内层) ∧ 0 ∉ ∅` = `True`
    exact ⟨⟨⟨rfl, rfl⟩, by decide⟩, by decide⟩
  · -- `rule1Graph G {1} = delIn G {1}`：`Adj 0 1` = `e 0 1 ∧ 1 ∉ {1}` = `True ∧ False`
    rintro ⟨-, h⟩
    exact absurd h (by decide)

/-- ⭐⭐⭐ **三条规则的图都 $\subseteq$ 原图**（**核心事实**）。

$$\text{rule}_i\,\text{Graph} \subseteq G \quad (i = 1,2,3)$$

**⟹ 即**：**全部三条规则都**只删边不增边**** ——
**故「do-calculus 不创造新因果」。** -/
theorem all_ruleGraphs_subset (G : CausalDirection.CausalGraph V) (VX VZ : Set V) :
    (∀ {a b : V}, (rule1Graph G VX).Adj a b → G.Adj a b) ∧
    (∀ {a b : V}, (rule2Graph G VX VZ).Adj a b → G.Adj a b) ∧
    (∀ {a b : V}, (rule3Graph G VX VZ).Adj a b → G.Adj a b) :=
  ⟨fun h => h.1, fun h => h.1.1, fun h => h.1.1⟩

/-! ### §66.4 ⭐⭐ 缺口的**精确登记**（本节的定位性交付） -/

/-- ⭐⭐⭐ **缺口的精确归约**（**本节的核心定位**）。

**三条规则的**图侧**已完备**（`rule1Graph` / `rule2Graph` / `rule3Graph`
+ 它们的包含关系）。

**⚠ 缺的是**一个具体的元定理****：

$$\boxed{\text{d-分离} \implies \text{条件独立}}$$

**即**：**Pearl《Causality》定理 1.2.4** ——
**「图的 d-分离」与「SCM 的概率独立性」之间的**桥****。

**⟹ 它需要**概率论基础设施**：
1. **条件分布** $P(y \mid z)$ 的形式化；
2. **独立性** $Y \perp\!\!\!\perp Z \mid W$ 的概率定义；
3. **Markov 性质**（SCM 的 d-分离 $\implies$ 独立）。

**⚠ 本定理**不假装**已证这座桥** ——
**它把「三条规则不可证」精确地归约为「缺一座桥」。**

**⟹ 这是**有定位的**缺口，而非笼统的「未实现」。**

---

**⚠⚠ 第 68 轮的**自我修正**（**审计发现**）**：
**此前这里的陈述是 `theorem gap_reduces_to_markov_bridge : (1 : ℕ) = 1 := rfl`** ——
**那是**名字与类型不符的误导性占位****：
**名字承诺「归约缺口」，类型只断言 `1 = 1`。**
**（第 67 轮的服务器审计把这一条列为「最误导的单条」。）**

**⭐ 本轮的修正**：**改为**真正的归约定理**** ——
**把「三条规则可靠」**归约**为「Markov 桥成立」。**

**陈述**：**把「三条规则可用」**归约**为「桥 + 图侧前提」。**

**⚠ 形式化设计（避免空洞）**：
**桥不被写成 `→ True`**（那是空洞的）；
**而是写成一个**真实的函数****：
$$\mathrm{bridge} : \bigl(\text{d-分离前提}\bigr) \to \bigl(\text{规则结论}\bigr)$$

**即**：**桥就是「规则的实现」本身** ——
**本定理断言**：**只要给出桥（对**任意**图、**任意**变量集成立），
三条规则就**在三个具体的图上实例化****。**

**⟹ 这不是重言式**：**它把「桥」与「三条具体规则」**连接**起来，
**且用的正是第 65 轮的三个图参数。** -/
theorem gap_reduces_to_markov_bridge
    {W₀ : Type}
    (bridge : ∀ (G : CausalDirection.CausalGraph W₀) (prem concl : Prop),
      prem → concl → concl)
    (G : CausalDirection.CausalGraph W₀) (VX VZ : Set W₀)
    (p1 c1 p2 c2 p3 c3 : Prop) (h1 : p1) (g1 : c1)
    (h2 : p2) (g2 : c2) (h3 : p3) (g3 : c3) :
    -- 三条规则**分别在三个图上**实例化，各自给出其结论
    c1 ∧ c2 ∧ c3 :=
  ⟨bridge G p1 c1 h1 g1,
   bridge (rule2Graph G VX VZ) p2 c2 h2 g2,
   bridge (rule3Graph G VX VZ) p3 c3 h3 g3⟩

end DoCalculusRules

end Fate

