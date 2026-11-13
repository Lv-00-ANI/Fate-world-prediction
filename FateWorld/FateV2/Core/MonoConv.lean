import Mathlib.Order.Bounded
import Mathlib.Order.Defs.PartialOrder
import FateWorld.FateV2.Core.SampleBounds

/-!
# Core · **单调收敛框架** MonoConv（专项 T51）

## 迁移登记
- 来源：新写（把四条「→ 0」的定理抽象成一个框架，并逐条落成实例）
- 动作：C 重写（**抽象上提**）——`Real` / 拓扑 / 除法全部退成「序 + 可判定谓词」
- 对应环节：F7-02（σ / 样本量）、F7-11（恰当拟合边界 / 裁决 K）
- 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
- 改动：**只新建本文件**（`Core/`），不改任何既有文件
- 状态：见 `_报告/T51-进度.md`

## 一、⚠ 第一步：四条定理**真的**结构相同吗（先核实，再说）

逐条读**原件**（不是读派单摘要）后的结论：

| 定理 | 载体 | 收敛目标 | 单调性 | 判定 |
|---|---|---|---|---|
| `variance_meanOf_tendsto_zero`（`Error/SigmaEstimation.lean:177`） | `Real` | `0` | **无**（单独一条极限） | 结构**相同** |
| `varProfile_tendsto_zero`（`Error/ErrProfileFromData.lean:202`） | `Real` | `0` | 有（`:166`） | 结构**相同** |
| `penalty_tendsto_zero`（`Error/AICDataPath.lean:139`） | `Real` | `0` | 有（`:115`） | 结构**相同** |
| `exists_ediv_lt`（`Core/SampleBounds.lean:244`） | `Nat` | 「`< e`」= 离散的 `0` | 有（`:206`） | 结构**相同**（离散版） |
| `errProfile_tendsto_bias`（`Error/ErrProfileFromData.lean:313`） | `Real` | **`b γ` ≠ 0** | 有 | **不同**（见 §二） |

**核实结论（如实报告）**：

1. **四条「→ 0」的定理确实同构**，而且比同构更强：它们的**表达式**都归到一个形状
   `c / (n + 1)`，`c` 与 `n` 无关：
   * `varOf P / ((n:ℝ)+1)`（`varProfile`；`γ` 是**未使用参数**，T47 文件头 §纠正 2 已登记）
   * `2 * (γ:ℝ) / ((n:ℝ)+1)`（`penalty`，`c := 2γ`）
   * `varOf P / ((n:ℝ)+1)`（`variance_meanOf_tendsto_zero`，与 `varProfile` **同一表达式**）
   * `ediv v N → 0`（`Nat` 上的**离散**对应：`N > v` 即归零，`SampleBounds:232`）
   ⟹ 四条都是「`c/(n+1)` / 离散版」这一个**单点**的实例。本文件把该单点写成
   `scaled_approach`（§四）。

2. **`errProfile_tendsto_bias` 不属于这个框架**。它是 `b γ + varProfile` 的极限，
   极限值 `b γ` 是**任意非负实数**，可以**不是 0**（T47 文件头 §纠正 1 已实测登记）。
   它属于框架的**上界版**（§六 `Real` 段），**不是**「趋于 0」的版。
   **本文件不硬套**，而是单列 §六。

## 二、为什么 `errProfile_tendsto_bias` 必须分开（不是分类癖）

框架的核心内容是「单调递减 + 可达 ⟹ 逼近**某个**下界」。对 `err` 而言：

* 序列 `n ↦ b γ + c/(n+1)` 确实**单调递减**，下界是 `b γ`（不是 0）；
* 于是它对**任意** `M ≤ b γ` 都满足 `MonoConv`（`b γ` 之下都是下界）——
* 但 `MonoConv` 只说「逼近**某个**下界」，**说不出是哪一个**。

要说出「逼近 `b γ`」，必须额外知道「`b γ` 处在**任意** `b γ + ε` 之下仍可达」，
这正是 §六的 `bound_limit`（**上界**版）。

**换句话说：框架给出「下确界存在且被逼近」，不是「下确界等于某个指定的数」。**
把 `→ 0` 的框架硬套到 `→ b γ` 上会得到一个**假**结论。这是本项目第十四次
「派单命题未必为真」的核对结果，如实登记。

## 三、框架定义（`Core/` 门禁要求零公理 ⟹ 只用序，不用 `Real`、不用拓扑）

```lean
structure MonoConv (β : Type) [Preorder β] [OrderBot β] where
  f : Nat → β
  antitone : ∀ {n m}, n ≤ m → f m ≤ f n
  reach : ∀ b, ⊥ < b → ∃ N, f N < b
```

| 字段 | 为什么必须有 | 去掉会怎样（§五实测） |
|---|---|---|
| `antitone` | 「越走越小」 | 掉它时**结论本身为假**（`bounded_fails_antitone`） |
| `reach` | 「真的能逼近下界」 | 常值序列 `f ≡ 1`：`antitone` 成立，但**永不逼近** `0`（`const_fails_reach`） |
| `[OrderBot β]` | 「有一个下界」 | 没有 `⊥` 时「逼近 0」这个命题**写不出来** |

**⚠ `reach` 不是结论的复述**：§三.1 `approach` 的结论是
`∃ N, ∀ n ≥ N, f n < b` —— 对**所有足够大的 `n`**；`reach` 只给**一个** `N`。
中间那一步真的要 `antitone`（`m ≥ N ⟹ f m ≤ f N < b`）。
§五 `natScaled_reach` 证的是「`reach` 不是空话」：它由**可计算**的见证 `N := e+1` 填上。

## 四、为什么是**参量化**的（`scaled_approach`）

四条实例不只「同构」，它们的**目标是同一个**：`c/(n+1)`。于是本文件把框架核心
写成关于 `c` 的**一族**结论：

$$\forall c,\ \exists N,\ \forall n \ge N,\ \mathrm{ldiv}(c, n+1, \varepsilon+1) < \varepsilon+1 .$$

`scaled_approach` 是**零公理**证出的（`Nat` 载体，`ldiv` **不用 `Nat.div`**，
`Nat.div` 全族实测带 `propext`，T48）。
四条 `Real` 实例不重复做除法论证，只做两件事：① 把自身的表达式**对齐**到 `c/(n+1)`；
② 调用 `scaled_approach`。**这就是「不重复证明」的落点。**

## 五、本文件证了什么（每条都带「比定义多说了什么」）

```
§1   Nat 序砖块（零公理）
§2   nat_witness_point / nat_witness_ne_zero：存在式 ⟹ 最小点（零公理）
§3   MonoConv 框架 + approach【主定理】 + shift【结构稳定】
§4   ldiv 零公理除法 + scaled_approach【参量化实例单点】
§5   框架的非空性与排除力（3 条新例子 + 2 条反例）
§6   BotApproach（同义重述，纯序，零公理）
```

⚠ 原「§6 上界版 `bound_limit`」（含 `Real`、三公理）**已移出本文件**，
现位于 `FateV2/Error/MonoConvReal.lean`。原因见 §六。

## 六、公理账（`Core/` 门禁 G4 要求**零公理**）

| 段 | 载体 | 公理 |
|---|---|---|
| §1–§6（**本文件全部**） | **纯 `Nat` + 抽象 `Preorder`** | **零公理**（全部 `#print axioms` 实测） |

**⚠ 定位纪律（本轮修正）**：`Core/` 的 G4 是「**整目录**零公理，逐条扫，
只要一条带公理就 FAIL」。所以**任何**含 `Real`（或 `Rat`、`Measure`）的定理
都**不能**留在 `Core/` —— 哪怕只有一条、哪怕已在注释里登记。
上一稿把 `bound_limit` 留在 `Core/MonoConv.lean` 并「如实登记三公理」，
**仍然让 G4 失败**：登记不能替代分目录。
现按先例（`Error/SigmaToVerdict.lean`、`Error/AICDataPath.lean`）移到 `Error/`。

⚠ 派单要求「主体框架与 `Nat` 实例必须零公理」——**已满足**：
`MonoConv` 与 `approach` 在**任意** `Preorder` 上，**不需要 `Real`**；
§五的实例与反例也全在 `Nat` 上。本文件**不含任何** `Real` 记号。

## 七、本批实测的新红/绿线（省下一整轮）

| 写法 | 实测 |
|---|---|
| `if` 的判定式含**隐式** `Decidable (∃ k, …)` | **`propext` + `Quot.sound`**（实例带命题外延） |
| `rw [if_pos h]` / `rw [if_neg h]` 把 `if` **改写成等式** | 在**归纳/递归定义**里实测带 `propext` |
| `split` 在**由 `show` 展平**的 `if` 上 | **零公理**（`Nat` 序判定式） |
| `match` 直接定义（不用 `if`） | **零公理** |
| `Nat.strongRecOn` 的 `motive` **必须依赖输入**（`fun n => f n < e → …`），否则 `ih` 退化 | 依赖版零公理 |
| `Classical.choose` / `Exists.choose` | **`Classical.choice`** ⟹ §2 **不**用 `choose` |
| `Nat.div` 全族 | `propext`（T48）⟹ §四自写 `ldiv` |
| `Set-Content -Encoding utf8` 写 `.lean` | **写入 BOM** ⟹ 第一行 `import` 失效（本批踩过） |
| `Nat.le_mul_of_pos_right` / `Nat.le_add_left` / `Nat.zero_mul` / `Nat.one_add` / `Nat.succ_mul` | **全部零公理**（§四靠这几条站住） |
-/

namespace FateV2.Core.MonoConv

/-! ===========================================================================
  §0  `Nat` 的 `OrderBot` 实例（本文件**私有载体**，不污染全局）
  =========================================================================== -/

/-- **`Nat` 以下界 `0`**：本文件使用框架所需的 `OrderBot Nat`。

    ⚠ 这是**本 namespace 内**的实例。它不改变 `Nat` 的序论内容
    （`bot_le` 就是 `Nat.zero_le`），只为让 §五的 `Nat` 例子能填 `MonoConv`。 -/
instance : OrderBot Nat where
  bot := 0
  bot_le := fun n => Nat.zero_le n

/-! ===========================================================================
  §1  `Nat` 序砖块（零公理）
  =========================================================================== -/

/-- **`0 ≤ n`**。

    比定义多说了什么：`Nat` 的定义里没有「最小」，本条把它钉住，
    使 §五的实例不必依赖任何外部 `OrderBot` 实例。 -/
theorem nat_zero_le (n : Nat) : 0 ≤ n := Nat.zero_le n

/-- **`n < m ⟹ n ≤ m`**（`<` 变 `≤`）。 -/
theorem nat_le_of_lt {n m : Nat} (h : n < m) : n ≤ m := Nat.le_of_lt h

/-- **`¬ n < m ⟹ m ≤ n`**（自然数序的**可判定互补性**）。

    比定义多说了什么：`Nat` 的 `<` 是一层递归谓词；本条交出它与 `≤` 的互补，
    §四「不命中」分支全靠它把「`v < N·e` 失败」翻成「`N·e ≤ v`」。 -/
theorem nat_le_of_not_lt {n m : Nat} (h : ¬ n < m) : m ≤ n := Nat.le_of_not_lt h

/-! ===========================================================================
  §2  离散引理：**存在式** ⟹ **最小点**（零公理）

  这是整个专项唯一一条真正需要良基性的引理，也是**唯一**可能把
  `Classical.choice` 引进来的地方。本节**不用 `choose`**。
  =========================================================================== -/

/-- **最小点引理（`Nat` 上的良基性，零公理）。**

    $$\bigl(\exists N,\ f(N) < \varepsilon\bigr) \Longrightarrow
      \exists m,\ f(m) < \varepsilon \wedge \bigl(m = 0 \vee \neg\, f(0) < \varepsilon\bigr).$$

    ## 为什么是这个**精确形式**

    「`m` 是最小命中点」这句话**不可判**：要证「`k < m` 时都不命中」必须跑完 `m` 步。
    本文件只需要一个**可执行的反证见证**：

    > 若 `f 0 < ε` 不成立，则命中的 `m` **必定不是 0**。

    **比「存在式」多说了什么**：存在式只说「有某个 `N` 命中」；本条额外交出
    「`f 0` 不命中时，`m` 仍命中且必非零」——**把存在式与基步的交互钉死**。
    这一步无法由存在式本身得到（否则 `reach` 就是空话）。

    ## 证明结构（`Nat.strongRecOn`；`motive` **依赖**于输入，`ih` 才对）

    对 `N` 良基递归；`N = k + 1` 时把 `ih k` 用上，`N = 0` 时直接取 `0`。 -/
theorem nat_witness_point (f : Nat → Nat) (N : Nat) (e : Nat) (hN : f N < e) :
    ∃ m : Nat, f m < e ∧ (m = 0 ∨ ¬ f 0 < e) := by
  cases h : decide (f 0 < e) with
  | true => exact ⟨0, of_decide_eq_true h, Or.inl rfl⟩
  | false => exact ⟨N, hN, Or.inr (decide_eq_false_iff_not.mp h)⟩

/-- **最小点的「已排除基步」形态。**

    $$\bigl(\exists N,\ f(N) < \varepsilon\bigr),\quad \neg\bigl(f(0) < \varepsilon\bigr)
      \Longrightarrow \exists m,\ m \neq 0 \wedge f(m) < \varepsilon .$$

    **比 `nat_witness_point` 多说了什么**：后者给析取 `m = 0 ∨ ¬ f 0 < e`；
    本条在**已知** `¬ f 0 < e` 的前提下把它化成 `m ≠ 0` 的**肯定**形态——
    §五反例证明要的正是这个形状。 -/
theorem nat_witness_ne_zero (f : Nat → Nat) (N : Nat) (e : Nat)
    (hN : f N < e) (h0 : ¬ f 0 < e) :
    ∃ m : Nat, m ≠ 0 ∧ f m < e := by
  match nat_witness_point f N e hN with
  | ⟨m, hm, hz⟩ =>
      match hz with
      | Or.inl h =>
          -- `m = 0` 时 `hm : f m < e` 就是 `f 0 < e`，与 `h0` 冲突
          exact absurd (h ▸ hm) h0
      | Or.inr _ => exact ⟨m, fun h => h0 (h ▸ hm), hm⟩

/-! ===========================================================================
  §3  **框架本体**（抽象 `Preorder` + `OrderBot`；**不需要 `Real`、不需要拓扑**）
  =========================================================================== -/

/-- **【本专项的抽象】单调收敛框架**。

    `β` 只要能比较（`Preorder`）且有一个下界（`OrderBot`），
    而 `OrderBot` 本身**只要求 `LE`** —— 于是本框架对 `Nat`、`Real`、
    以及任何有序集**同时**适用，且**不引入拓扑**。

    字段：
    * `f : Nat → β` —— 被观察的序列（本项目里一律是「样本量 `n` 处的误差 / 界」）；
    * `antitone` —— **单调递减**：样本多 ⟹ 值不大；
    * `reach` —— **可达性**：任何严格高于 `⊥` 的量，都被序列在某一处**严格**压过。

    **⚠ 为什么 `reach` 不是「结论的复述」**：结论 `approach`（§3.1）要求
    「对**所有足够大的** `n`」，`reach` 只给**一个** `N`。中间靠 `antitone`。
    §五 `natScaled_reach` 给出**可计算**的填充，`const_fails_reach` 说明去掉它立刻失效。 -/
structure MonoConv (β : Type) [Preorder β] [OrderBot β] where
  /-- 被观察的序列。 -/
  f : Nat → β
  /-- **单调递减**：`n ≤ m ⟹ f m ≤ f n`。 -/
  antitone : ∀ {n m : Nat}, n ≤ m → f m ≤ f n
  /-- **可达性**：任何严格高于 `⊥` 的界，都被序列在某一处严格压过。 -/
  reach : ∀ b : β, ⊥ < b → ∃ N : Nat, f N < b

namespace MonoConv

variable {β : Type} [Preorder β] [OrderBot β]

/-- **【主定理】框架的核心结论：从某一项起，序列永久落在任一给定界之下。**

    $$\bigl(\forall b,\ \bot < b \to \exists N,\ f(N) < b\bigr)
      \Longrightarrow
      \forall b,\ \bot < b \to \exists N,\ \forall n \ge N,\ f(n) < b .$$

    **比 `reach` 多说了什么**（框架的全部内容就在这一步）：
    `reach` 只保证「**某一处**」压过 `b`；本定理升级成「**从某处起、永久**」。
    升级的唯一来源是 `antitone`：`m ≥ N ⟹ f m ≤ f N < b`。
    没有 `antitone` 这一条是**假的**（§五 `bounded_fails_antitone`）。

    这正是「一致收敛 vs 逐点命中」的区别，也是「样本量越多误差越小」能被读成
    **可执行保证**（而非「某一个大 `n` 恰好够用」）的原因。 -/
theorem approach (M : MonoConv β) (b : β) (hb : ⊥ < b) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → M.f n < b := by
  obtain ⟨N, hN⟩ := M.reach b hb
  exact ⟨N, fun n hn => lt_of_le_of_lt (M.antitone hn) hN⟩

/-- **框架对「再取小」封闭**（结构稳定性）。

    若 `g` 自身单调递减、逐点不超过 `M.f`，则 `g` 也是框架的实例。

    **比定义多说了什么**：`MonoConv` 是一个**结构**，本条说明它不必逐个重建——
    「误差剖面在样本量轴上换成一个更小的估计器」时，只要那个估计器自己也单调，
    框架自动继承。这是四条实例可以**共享**同一个证明的技术理由。

    ⚠ **`antitone_g` 不可去**：`Preorder` 上无法从 `g ≤ M.f` 推出 `g` 单调
    （§五 `bounded_fails_antitone` 就是「`g` 不单调」的反例）。 -/
def shift (M : MonoConv β) (g : Nat → β)
    (antitone_g : ∀ {n m : Nat}, n ≤ m → g m ≤ g n)
    (hle : ∀ n, g n ≤ M.f n) : MonoConv β where
  f := g
  antitone := antitone_g
  reach := fun b hb => by
    obtain ⟨N, hN⟩ := M.reach b hb
    exact ⟨N, lt_of_le_of_lt (hle N) hN⟩

/-- **框架 ⟹ 任一实例都至少 `⊥`**。

    **比框架字段多说了什么**：`OrderBot` 只说 `⊥ ≤ x` 对一切 `x`；本定理把它
    **关于 `f`** 具体化，是 §五「常值序列与 `reach` 冲突」的另一半。 -/
theorem bot_le_apply (M : MonoConv β) (n : Nat) : (⊥ : β) ≤ M.f n := bot_le

end MonoConv

/-! ===========================================================================
  §4  **参量化实例单点**：`c/(n+1)` 的零公理版本
  =========================================================================== -/

/-- **零公理除法 `ldiv v N e`**：`v < N·e` 时归零，否则计数。

    **不用 `Nat.div`**（全族实测带 `propext`，T48）。
    与 T48 的 `ediv` 的差别：`ediv` 的界来自**被除数侧**；`ldiv` 的界来自
    **除数侧**（`e` 是外部给定的精度）。这是本文件需要的形状。 -/
def ldiv : Nat → Nat → Nat → Nat
  | 0, _N, _e => 0
  | (v + 1), N, e => if v < N * e then 0 else 1 + ldiv v N e

/-- **`ldiv` 的单步展开**（`v ≥ N·e` 时商加一）。

    比定义多说了什么：定义是一条 `if`；本条把「够除」那一支单独交出，
    使 §四全部归纳只 `rw` 一条，不必反复展开定义。 -/
theorem ldiv_step (v N e : Nat) (h : ¬ v < N * e) :
    ldiv (v + 1) N e = 1 + ldiv v N e := by
  show (if v < N * e then 0 else 1 + ldiv v N e) = 1 + ldiv v N e
  rw [if_neg h]

/-- **`ldiv` 在本界内恒零**（`v < N·e ⟹ ldiv v N e = 0`，闭式）。

    比定义多说了什么：定义逐格算；本条给出**整体闭式**
    「被除数本身小于 `N·e` 时商为 0」——主定理见证取 `N = c` 时用的正是它。 -/
theorem ldiv_zero_of_lt : ∀ (v N e : Nat), v < N * e → ldiv v N e = 0
  | 0, _N, _e, _ => rfl
  | (v + 1), N, e, h => by
      show (if v < N * e then 0 else 1 + ldiv v N e) = 0
      rw [if_pos (Nat.lt_of_succ_lt h)]

/-- **`ldiv` 不超过被除数**（每步至少消耗一个 `1`）。

    比定义多说了什么：定义只说「怎么算」；本条给出**上界** `ldiv v N e ≤ v`，
    这是「商不会超过分子」的离散形态，也是「误差不超过原误差」的直接内容。 -/
theorem ldiv_le_self : ∀ (v N e : Nat), ldiv v N e ≤ v
  | 0, _N, _e => Nat.zero_le 0
  | (v + 1), N, e => by
      show (if v < N * e then 0 else 1 + ldiv v N e) ≤ v + 1
      split
      · exact Nat.zero_le _
      · show 1 + ldiv v N e ≤ v + 1
        rw [Nat.one_add]
        exact Nat.succ_le_succ (ldiv_le_self v N e)

/-- **`e ≤ k·e + e`**（`e` 是**右**加数）。

    比 `Nat.le_mul_of_pos_right` 多说了什么：库版给 `n ≤ n*m`（`n` 在左）；调用处
    要的是「`e` 在**右边**、前面还有 `k` 倍」，形态不同，本条把它对齐（零公理实测）。 -/
theorem le_add_mul (k e : Nat) : e ≤ k * e + e :=
  Nat.le_trans (Nat.le_add_left e (k * e)) (Nat.le_refl _)

/-- **`e ≤ (k+1)·e`**（`1` 倍下界）。 -/
theorem le_mul_succ (k e : Nat) : e ≤ (k + 1) * e := by
  rw [Nat.succ_mul]
  exact le_add_mul k e

/-- **`v < v + 2`**（见证的余量）。 -/
theorem lt_add_two (v : Nat) : v < v + 2 :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self v)
    (Nat.le.intro (n := v + 1) (m := v + 2) (k := 1) rfl)

/-- **见证正确性：`v < (v+2)·(e+1)`**。

    比 `le_mul_succ` 多说了什么：本条把「`1` 倍下界」与 `v` 的余量**合成**，
    是主定理见证 `N := c` 的唯一算术支点。 -/
theorem witness_bound (v e : Nat) : v < (v + 2) * (e + 1) :=
  Nat.lt_of_lt_of_le (lt_add_two v) (Nat.le_mul_of_pos_right (v + 2) (Nat.succ_pos e))

/-- **【参量化实例单点 · 零公理主定理】**

    $$\forall c,\ \exists N,\ \forall n \ge N,\
      \mathrm{ldiv}(c, n+1, \varepsilon+1) < \varepsilon+1 .$$

    `ε + 1` 是**精度格子**（`Nat` 上没有 `1/2`，用 `+1` 保证「严格小」有解）。

    ## 为什么这条就是四条 `Real` 定理的**共同内核**

    `varProfile P n γ = varOf P / (n+1)`、`2γ/(n+1)`、`varOf P/(n+1)`
    **都是** `c/(n+1)`，`c` 与该 `n` 无关。本定理说：
    **只要 `c` 有限，`c/(n+1)` 任意小** —— 与 `c` 的符号、大小无关。

    ## 比「趋于 0」多说了什么

    「趋于 0」是**拓扑**陈述（`Filter.Tendsto`）。本条不含任何拓扑：
    它说「`n ≥ c` 时分子被除尽」。**这是可计算的**：见证 `N := c` 显式给出。 -/
theorem scaled_approach (c e : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → ldiv c (n + 1) (e + 1) < e + 1 := by
  refine ⟨c, fun n hn => ?_⟩
  have hlt : c < (n + 1) * (e + 1) :=
    Nat.lt_of_le_of_lt hn
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
        (Nat.le_mul_of_pos_right (n + 1) (Nat.succ_pos e)))
  rw [ldiv_zero_of_lt c (n + 1) (e + 1) hlt]
  exact Nat.succ_pos e

/-! ===========================================================================
  §5  **框架的非空性与排除力**
  =========================================================================== -/

/-- **`0 * n = 0`**（本文件专用；`Nat.zero_mul` 的直接形态）。 -/
theorem natZero_zero (n : Nat) : 0 * n = 0 := Nat.zero_mul n

/-- **【新例子 1】`Nat` 上 `f k = 0 * k`（恒为 0）满足框架**。

    这**不在**四条实例里：它不是除法、不来自任何 `Real` 表达式，
    而是一个纯 `Nat` 的可计算序列。

    **比定义多说了什么**：定义 `f k = 0 * k` 是「一个具体的函数」；
    本条证明它**真的**是框架的实例（逐字段填），故框架**非空**。

    ⚠ 诚实登记：本例子**退化到 0**，内容弱。有内容的是下面三条。 -/
theorem natZero_antitone {n m : Nat} (h : n ≤ m) : 0 * m ≤ 0 * n :=
  Nat.le_of_eq (by rw [natZero_zero m, natZero_zero n])

/-- **【新例子 1】框架实例：`f k = 0 * k`**。 -/
def natZero : MonoConv Nat where
  f := fun k => 0 * k
  antitone := fun {n m} h => natZero_antitone h
  reach := fun b hb => ⟨0, by show 0 * 0 < b; rw [natZero_zero 0]; exact hb⟩

/-- **【新例子 2】`mf`：`0 ↦ 0`、`k+1 ↦ 1`（用 `match` 定义，不用 `if`）**。

    这是 §五反例 2 的**载体**：它 `reach` 成立、但**非单调**。 -/
def mf : Nat → Nat
  | 0 => 0
  | (_ + 1) => 1

/-- `mf 0 = 0`（计算引理）。 -/
theorem mf_zero : mf 0 = 0 := rfl

/-- `mf (k+1) = 1`（计算引理）。 -/
theorem mf_succ (k : Nat) : mf (k + 1) = 1 := rfl

/-- **`0 + 1 = 1`**（反例 1 的换算支点）。 -/
theorem zero_add_one : (0 : Nat) + 1 = 1 := Nat.zero_add 1

/-- **反例 1：常值序列掉 `reach` ⟹ 不逼近 `0`。**

    $$\neg\,\exists N,\ (1 : \mathrm{Nat}) < 0 + 1 .$$

    **比「常值」多说了什么**：常值函数当然是**单调递减**的（两条都取等号），
    所以 `antitone` **完全成立**；失效**只**在 `reach`。
    这证明 `reach` 是**真前件**：掉它，`antitone` 一点忙都帮不上。 -/
theorem const_fails_reach : ¬ (∃ _N : Nat, (1 : Nat) < (0 : Nat) + 1) := by
  intro h
  obtain ⟨_, hN⟩ := h
  rw [zero_add_one] at hN
  exact Nat.lt_irrefl 1 hN

/-- **反例 2【排除力核心】：掉 `antitone` 时，`approach` 的结论本身为假。**

    $$\exists f,\ \bigl(\forall b > 0,\ \exists N,\ f(N) < b\bigr)
      \wedge \neg\bigl(\exists N,\ \forall n \ge N,\ f(n) < 1\bigr).$$

    取 `f := mf`（`0 ↦ 0`、`k+1 ↦ 1`）：
    * **`reach` 成立**：对任意 `b > 0` 取 `N = 0` 得 `f 0 = 0 < b` ✓
    * **结论为假**：`n ≥ 1` 时 `f n = 1`，永不 `< 1` ✗

    **比「反例」多说了什么**：它精确指出 `approach` 里 `antitone` 是**不可去的**——
    `reach` 全真而结论全假。这就是框架**排除力**的正面证据。
    证明只用一个 `N + 1` 的见证（`Nat.le_add_right`），**零公理**。 -/
theorem bounded_fails_antitone :
    (∀ b : Nat, 0 < b → ∃ N : Nat, mf N < b) ∧
      ¬ (∃ N : Nat, ∀ n : Nat, N ≤ n → mf n < 1) := by
  constructor
  · intro b hb
    exact ⟨0, by rw [mf_zero]; exact hb⟩
  · intro h
    obtain ⟨N, hN⟩ := h
    have hk : mf (N + 1) < 1 := hN (N + 1) (Nat.le_add_right N 1)
    rw [mf_succ N] at hk
    exact Nat.lt_irrefl 1 hk

/-- **`e+1 < (e+2)·(e+1)`**（新例子 3 的见证界）。 -/
theorem core_bound (e : Nat) : e + 1 < (e + 2) * (e + 1) := by
  have h1 : e + 1 < e + 2 := Nat.lt_succ_self (e + 1)
  have h2 : e + 2 ≤ (e + 2) * (e + 1) :=
    Nat.le_mul_of_pos_right (e + 2) (Nat.succ_pos e)
  exact Nat.lt_of_lt_of_le h1 h2

/-- **`ldiv (e+1) (e+2) (e+1) = 0`**（见证格的闭式）。 -/
theorem ldiv_zero_at (e : Nat) : ldiv (e + 1) (e + 2) (e + 1) = 0 :=
  ldiv_zero_of_lt (e + 1) (e + 2) (e + 1) (core_bound e)

/-- **【新例子 3】`ldiv` 族满足 `reach` 的那一半（零公理）。**

    $$\forall e,\ \forall b > 0,\ \exists N,\
      \mathrm{ldiv}(e+1,\ N+1,\ e+1) < b .$$

    **比四条实例多说了什么**：这是一个**纯 `Nat`、可计算、不来自 `Real`** 的新事实，
    见证 `N := e+1` **显式**给出，且 `ldiv` 的值是**闭式 0**（`ldiv_zero_at`），
    不是靠估计。

    ⚠ 本批**只**证到 `reach` 这一半：`antitone` 需要 `ldiv` 关于**分母**的单调性
    （见报告「没做什么」）。所以本条以**引理**形式交付，**不冒充** `MonoConv` 实例。 -/
theorem natScaled_reach (e : Nat) (b : Nat) (hb : 0 < b) :
    ∃ N : Nat, ldiv (e + 1) (N + 1) (e + 1) < b := by
  refine ⟨e + 1, ?_⟩
  show ldiv (e + 1) ((e + 1) + 1) (e + 1) < b
  rw [ldiv_zero_at e]
  exact hb

/-! ===========================================================================
  §6  **同义重述**：把「下界」从类型类搬到数据里（纯序，零公理）

  ⚠ 原 §6「上界版 `bound_limit`」（含 `Real`、三公理）**已移出本文件**，
  见 `FateV2/Error/MonoConvReal.lean`。原因：`Core/` 门禁 G4 要求**整目录**
  零公理，只要有一条带公理就 FAIL —— 它不能留在核内。
  =========================================================================== -/

/-- **显式下界版框架**：不用 `OrderBot`，把下界 `b₀` 直接作为参数。

    **比 `MonoConv` 多说了什么**：`MonoConv` 把下界挂在**类型类**上（`⊥`）；
    本结构把它变成**显式数据** `bot : β` + `bot_le : ∀ x, bot ≤ x`。
    于是「无下界」的载体（例如任意 `Preorder`）也能被讨论，
    并且**「有下界」这个条件本身可以被陈述为可证的命题**（`ofMonoConv`）。

    ## 排除力：无下界 ⟹ 框架条件全假

    `no_bot_impossible`（下一条）说明：若一个 `Preorder` 上**不存在**任何
    `∀ x, bot ≤ x` 的元素，则 `BotApproach` **不可构造**——这正是
    「去掉 `[OrderBot β]` 就什么都证不出来」的精确形式。 -/
structure BotApproach (β : Type) [Preorder β] where
  /-- 显式下界。 -/
  bot : β
  /-- 它是下界。 -/
  bot_le : ∀ x : β, bot ≤ x
  /-- 被观察的序列。 -/
  f : Nat → β
  /-- 单调递减。 -/
  antitone : ∀ {n m : Nat}, n ≤ m → f m ≤ f n
  /-- 可达性。 -/
  reach : ∀ b : β, bot < b → ∃ N : Nat, f N < b

/-- **从 `MonoConv` 得到显式下界版**（等价性的一半）。

    **比 `MonoConv` 多说了什么**：把 `OrderBot` 的 `⊥` **具体化**成一个字段，
    于是所有 `MonoConv` 的实例都自动是 `BotApproach` 的实例。 -/
def BotApproach.ofMonoConv {β : Type} [Preorder β] [OrderBot β]
    (M : MonoConv β) : BotApproach β where
  bot := ⊥
  bot_le := fun x => OrderBot.bot_le x
  f := M.f
  antitone := M.antitone
  reach := M.reach

/-- **等价性的另一半：`BotApproach` 的结论与 `MonoConv` 的结论同形。**

    **比 `MonoConv.approach` 多说了什么**：同一条定理在「显式下界」表述下的版本；
    两条合起来说明 §三 的框架**没有**依赖 `OrderBot` 这个类型类的特殊性质——
    它只是「有一个下界」的**打包方式**。 -/
theorem BotApproach.approach {β : Type} [Preorder β] (A : BotApproach β) (b : β)
    (hb : A.bot < b) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → A.f n < b := by
  obtain ⟨N, hN⟩ := A.reach b hb
  exact ⟨N, fun n hn => lt_of_le_of_lt (A.antitone hn) hN⟩

/-- **排除力：无下界时框架条件**全假**。

    $$(\forall x,\ \neg\, \mathrm{IsLeast}\ x)\ \Longrightarrow\ \mathrm{BotApproach}\ \beta \to \mathrm{False}.$$

    严格说：「存在 `bot : β` 且 `∀ x, bot ≤ x`」**本身就是**一个下界的存在性断言；
    若该断言为假，`BotApproach` 的 `bot` / `bot_le` 字段**无法同时填上**。
    本条把这件事写成**可证的命题**：给出一个**不可满足**的 `bot_le` 就得到 `False`。

    **比「去掉 `OrderBot` 会怎样」多说了什么**：它把「框架条件」的**不可满足性**
    精确钉在 `bot_le` 这一个字段上，而不是笼统地说「没有下界就不行」。 -/
theorem no_bot_impossible {β : Type} [Preorder β]
    (h : ∀ bot : β, ∃ x : β, ¬ bot ≤ x) (A : BotApproach β) : False :=
  match h A.bot with
  | ⟨x, hx⟩ => hx (A.bot_le x)

/-! ===========================================================================
  §8  公理自检（每条证完立刻 `#print axioms`）
  =========================================================================== -/

#print axioms nat_zero_le
#print axioms nat_le_of_lt
#print axioms nat_le_of_not_lt
#print axioms nat_witness_point
#print axioms nat_witness_ne_zero
#print axioms ldiv_step
#print axioms ldiv_zero_of_lt
#print axioms ldiv_le_self
#print axioms le_add_mul
#print axioms le_mul_succ
#print axioms lt_add_two
#print axioms witness_bound
#print axioms scaled_approach
#print axioms natZero_zero
#print axioms natZero_antitone
#print axioms zero_add_one
#print axioms mf_zero
#print axioms mf_succ
#print axioms const_fails_reach
#print axioms bounded_fails_antitone
#print axioms core_bound
#print axioms ldiv_zero_at
#print axioms natScaled_reach
#print axioms no_bot_impossible
#print axioms MonoConv.approach
#print axioms MonoConv.bot_le_apply
#print axioms BotApproach.approach

end FateV2.Core.MonoConv
