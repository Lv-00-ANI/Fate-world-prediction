import Mathlib.Data.List.Basic

/-!
  # Model · 序（拓扑序与可达）

  ## 本文件回答什么

  `Modeling/SCM.lean` 的文件头写着「必须按图拓扑序逐步求值」，却从未证明拓扑序存在。
  本文件把「无环 ⟹ 拓扑序存在」这条链补上，并如实登记未能零公理证出的那一环。

  ## 为什么不计算传递闭包

  传递闭包（在 `Finset`/`Fintype` 上迭代去重）需要可判定性，在核内会经
  `Finset`/`decide` 引入 `propext`。这里改用 **`Prop` 级归纳关系 `Reachable`**：
  不可判定，但**传递性免费**（就是归纳子本身），且「拓扑序 ⟹ 所有间接依赖」
  靠 `topo_order_reachable_before` 一次归纳拿到，根本不需要构造闭包。

  ## 公理纪律：实测踩过的坑（每条都用 `#print axioms` 验证过）

  | 写法 | 实测结果 |
  |---|---|
  | `List.mem_cons`（把 `∈` 化成 `∨`） | `propext` |
  | `List.countP` / `List.count`（内部 `if` + `decide`） | `propext` |
  | `List.filter` 的长度（`if h : ...`） | `propext` |
  | `decide (x ∈ xs)` 转 `Bool` | `propext` |
  | `em (x ∈ xs)`（经典排中） | `propext;Classical.choice;Quot.sound` |
  | `Fintype.card` 的任何等式（含 `Fintype.card (Fin n) = n`） | `propext;Classical.choice;Quot.sound` |
  | `List.Nodup.length_le_card`（鸽笼） | `propext;Classical.choice;Quot.sound` |
  | `subst` / 依赖消去 | 视上下文带 `propext` |
  | `omega` | 本工具链未预编译该模块 |

  **本文件全篇采用的零公理姿势**：
  * 消去 `∈` 用 `cases h with | head => ... | tail _ h' => ...`，**不用** `List.mem_cons`；
  * 列表遍历手写（`nth`），不用 `map` / `filter` / `count`；
  * 大小比较走 `Nat` 的构造性引理（`Nat.lt_trans` 等）。

  ## 达成的与未达成的（诚实登记）

  * `Reachable` 传递性、无环下两端不等、无自环 —— **零公理**
  * 拓扑序 ⟹ 直接依赖在用户之前 —— **零公理**
  * 拓扑序 ⟹ **所有间接依赖**在用户之前（免算传递闭包）—— **零公理**
  * **条件版存在性**：源点 + 覆盖 + 子序 ⟹ 拓扑序 —— **零公理**
  * **无条件存在性**（`[Fintype V]` 上无环 ⟹ 存在源点）**未证出**。
    它等价于鸽笼原则（`Fin n` 上 `Nodup` 列表长度 ≤ n）；
    而本项目工具链里鸽笼的所有可用形态都带公理（见上表最后两行）。
    最小复现见文末 `SourceExists` 的注释。
-/

namespace FateV2.Model

universe u

variable {V : Type u}

/-! ## 图

    只**引用** `Modeling.Graph` 的形状，不修改它（该文件不归本专项所有）。
    按同样字段重新声明，使 `FateV2.Model` 与 `FateV2.Modeling` **不建立 import 边**，
    避免破坏 G11（依赖图无环）。 -/

/-- **图**：每个节点的父节点列表（与 `Modeling.Graph` 同构）。 -/
structure Graph (V : Type u) where
  /-- 父节点列表 -/
  pa : V → List V

/-! ## 可达（`Prop` 级）

    不加 `[Fintype]`、不加 `[DecidableEq]`：这是纯逻辑关系。 -/

/-- **可达**：沿父边反向走若干步（正步数）。

    比「一步父边」多说了：允许任意正步数的路径，且步数是**存在性**的，
    不需要可判定、不需要去重。`Reachable g a b` 读作「`b` 是 `a` 的祖先」。 -/
inductive Reachable (g : Graph V) : V → V → Prop
  /-- 一步：`b` 是 `a` 的父。 -/
  | step {a b : V} : b ∈ g.pa a → Reachable g a b
  /-- 拼接两段路径。 -/
  | trans {a b c : V} : Reachable g a b → Reachable g b c → Reachable g a c

/-- **无环**：没有顶点能沿父边回到自己。

    比「列表里没有 `v ∈ pa v`」多说了：**任意长度的回路**都被排除，
    不只是自环。`pa v = [v]`、`pa v = [w] ∧ pa w = [v]` 都被排除。 -/
def Acyclic (g : Graph V) : Prop := ∀ v, ¬ Reachable g v v

/-- **有源点**：存在一个没有父的点（`pa` 为空）。

    这是拓扑序存在的**关键砖块**：源点没有父，可以直接排第一；
    删掉它之后剩余部分仍是同构的子问题。（无条件存在性见文末登记。） -/
def HasSource (g : Graph V) : Prop := ∃ v, g.pa v = []

/-! ## 可达的基本性质 -/

/-- **`Reachable` 的传递性**。

    比定义多说了：`Reachable` 的 `trans` 构造子对应的**命题**在这里独立成立，
    于是「祖先的祖先是祖先」成为一步引理，不必再展开归纳。 -/
theorem reachable_trans {g : Graph V} {a b c : V}
    (h₁ : Reachable g a b) (h₂ : Reachable g b c) : Reachable g a c :=
  Reachable.trans h₁ h₂

/-- **无环 ⟹ 可达两端不同**。

    比 `Acyclic` 的定义多说了：把「不能回到自己」升级为
    「沿边走上正数步一定换点」。这是拓扑序里「严格小于」的来源。 -/
theorem reachable_ne {g : Graph V} (h : Acyclic g) {a b : V}
    (hr : Reachable g a b) : a ≠ b := by
  intro hab
  subst hab
  exact h a hr

/-- **无环 ⟹ 没有自环**。

    比 `reachable_ne` 多说了：把「可达两端不同」特化到**一步**可达，
    得到「父列表里不含自己」—— 这是最容易核验的那条推论。 -/
theorem acyclic_no_self {g : Graph V} (h : Acyclic g) (v : V) : v ∉ g.pa v := by
  intro hmem
  exact reachable_ne h (Reachable.step hmem) rfl

/-! ## 拓扑序 -/

/-- 列表第 `k` 位（手写，只有三条定义性等式）。 -/
def nth : List V → Nat → Option V
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => nth xs k

/-- **拓扑序**：列表含全部顶点，且父（依赖）排在子（用户）**前面**。

    `a` 在位置 `i`、它的父 `b` 在位置 `j`，则要求 `j < i`。

    比 `Reachable` 多说了：把「祖先关系」翻译成「列表位置的自然数序」，
    于是图论问题变成 `Nat` 上的算术问题。 -/
def IsTopoOrder (g : Graph V) (order : List V) : Prop :=
  (∀ v, v ∈ order) ∧
  ∀ a b, b ∈ g.pa a → ∀ i j, nth order i = some a → nth order j = some b → j < i

/-- `Option.some` 的单射性（手写，避免依赖消去的公理开销）。 -/
theorem some_inj {a b : V} (h : (some a : Option V) = some b) : a = b := by
  cases h
  rfl

/-- 把 `b ∈ g.pa a` 沿 `src = a` 搬到 `b ∈ g.pa src`。

    比 `Eq.rec` 多说了：给重写方向起个名字，避免 `▸` 的重写方向反掉。 -/
theorem mem_pa_congr {g : Graph V} {a src b : V} (h : src = a)
    (hb : b ∈ g.pa a) : b ∈ g.pa src := by
  rw [h]
  exact hb

/-- **列表成员都有位置**。

    比 `nth` 的定义多说了：`∈` 与「存在下标」互为逆，
    于是「覆盖全部顶点」可以翻译成「每个点都有位置」。
    `∈` 用 `cases` 消去，避开 `List.mem_cons` 的 `propext`。 -/
theorem exists_nth_of_mem {l : List V} {v : V} (h : v ∈ l) : ∃ i, nth l i = some v := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons x xs ih =>
      cases h with
      | head => exact ⟨0, rfl⟩
      | tail _ h' =>
          obtain ⟨i, hi⟩ := ih h'
          exact ⟨i + 1, hi⟩

/-- **拓扑序 ⟹ 每个依赖在用户之前**（直接父边）。

    比 `IsTopoOrder` 的定义多说了：把定义里的量词顺序重排成
    「拿到 `a` 和父 `b` 就立刻能用」的形态，不必现场拆 `∧`。 -/
theorem topo_order_before {g : Graph V} {order : List V}
    (h : IsTopoOrder g order) {a b : V} (hb : b ∈ g.pa a)
    {i j : Nat} (hi : nth order i = some a) (hj : nth order j = some b) : j < i :=
  h.2 a b hb i j hi hj

/-- **拓扑序 ⟹ 每个（间接）祖先也在用户之前**。

    比 `topo_order_before` 多说了：从「一步」推到「任意步」。
    若 `b` 是 `a` 的祖先，则 `b` 的位置严格小于 `a` 的位置。
    这条**消掉了计算传递闭包的需求**：拓扑序只要对直接父边成立，
    归纳一步就自动满足所有间接依赖。 -/
theorem topo_order_reachable_before {g : Graph V} {order : List V}
    (h : IsTopoOrder g order) {a₀ b₀ : V} (hr : Reachable g a₀ b₀) :
    ∀ {i j : Nat}, nth order i = some a₀ → nth order j = some b₀ → j < i := by
  induction hr with
  | @step x y hb => intro i j hi hj; exact h.2 x y hb i j hi hj
  | @trans x y z hxy hyz ihxy ihyz =>
      intro i j hi hj
      -- 中间点 `y` 的位置由覆盖性取出，再用两段各一次
      obtain ⟨m, hm⟩ := exists_nth_of_mem (h.1 y)
      exact Nat.lt_trans (ihyz (i := m) (j := j) hm hj) (ihxy (i := i) (j := m) hi hm)

/-- **有源点时的拓扑序拼接**（条件版存在性）。

    比「无条件存在性」少说了：多三个前提。但这条把「把源点放最前」
    这步单独钉死，且**穷尽了归纳步骤的全部内容**：
    若 `src` 没有入边、`rest` 覆盖其余顶点、且 `rest` 已排好其余父边，
    那么 `src :: rest` 就是整个图的拓扑序。

    「`rest` 已排好其余父边」这一前提在归纳里由「删掉源点后的子图问题」
    提供 —— 而那要求子问题**仍然有源点**，正是无条件存在性缺的那块。 -/
theorem topo_cons_of_source [DecidableEq V] {g : Graph V} {src : V} {rest : List V}
    (hsrc : g.pa src = [])
    (hcover : ∀ v, v ≠ src → v ∈ rest)
    (hedge : ∀ a b, b ∈ g.pa a → a ≠ src → ∀ i j,
        nth rest i = some a → nth rest j = some b → j < i) :
    IsTopoOrder g (src :: rest) := by
  have hsrcempty : ∀ b, b ∉ g.pa src := by
    intro b hb
    rw [hsrc] at hb
    exact List.not_mem_nil hb
  constructor
  · intro v
    by_cases hv : v = src
    · subst hv
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem src (hcover v hv)
  · intro a b hb i j hi hj
    -- 记 `hsrcPa : g.pa src = []`（源点没有父）。
    -- 若 `a = src` 则 `hb : b ∈ g.pa src`，与空列表矛盾。
    cases i with
    | zero =>
        rw [nth] at hi
        have ha : src = a := some_inj hi
        exact absurd (mem_pa_congr ha hb) (hsrcempty b)
    | succ i' =>
        cases j with
        | zero =>
            exact Nat.zero_lt_succ i'
        | succ j' =>
            have hi' : nth rest i' = some a := by rw [nth] at hi; exact hi
            have hj' : nth rest j' = some b := by rw [nth] at hj; exact hj
            have ha : a ≠ src := by
              intro he
              exact absurd (mem_pa_congr he.symm hb) (hsrcempty b)
            exact Nat.succ_lt_succ (hedge a b hb ha i' j' hi' hj')

/-! ## 未证部分的最小登记

    下面 `SourceExists` 是整条链唯一的缺口。它陈述「无环 ⟹ 有源点」，
    在 `Fintype` 上等价于鸽笼。

    **最小复现**（不需要本项目任何东西，任意 Lean 项目里都能复现）：

    ```lean
    import Mathlib.Data.List.Nodup
    import Mathlib.Data.Fintype.Card
    import Mathlib.Data.Fintype.EquivFin

    example (n : Nat) (l : List (Fin n)) (h : l.Nodup) : l.length ≤ n := by
      have := List.Nodup.length_le_card (α := Fin n) h
      rwa [Fintype.card_fin] at this
    -- #print axioms 结果：propext, Classical.choice, Quot.sound
    ```

    **为什么绕不开**：
    1. 直接算传递闭包 / 判重 → 需要 `decide`/`filter`/`count` → `propext`；
    2. 用 `Finset` 的 `card` → `Fintype.card` → `Classical.choice` + `Quot.sound`；
    3. 用经典排中 `em` 做「有没有源点」的二分 → 全套三个公理；
    4. 纯手写递归（本文件的做法）能拿到**无限父链**（零公理），
       但「无限链在有限类型里必重复」这一步就是鸽笼本身。

    零公理的「无限父链」构造（已实测零公理）：

    ```lean
    def chain (pa : V → List V) (h : ∀ v, pa v ≠ []) (s : V) : Nat → V
      | 0 => s
      | k + 1 => (pa (chain pa h s k)).head (h _)
    -- chain_step : chain pa h s (k+1) ∈ pa (chain pa h s k)   — 零公理
    ```

    因此缺口精确定位为：**`Fintype` 上的鸽笼**。
    在这套工具链里，它要么带公理，要么不可得。
-/

/-- **待证 Proposition**（无环 ⟹ 有源点，`Fintype` 上）。

    **未证明、也未作为公理引入**：只以 `Prop` 陈述存在，
    不被任何已证定理依赖。证明它等于证明鸽笼，见上面的最小复现。 -/
def SourceExists (g : Graph V) : Prop := Acyclic g → HasSource g

end FateV2.Model
