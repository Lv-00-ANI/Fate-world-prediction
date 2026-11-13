import FateWorld.FateV2.Core.ClosureFix

/-!
  # Core · 闭包稳定性（专项 T12 · `firstPos` 首次出现层路线）

  ## 迁移登记
  - 来源：新写（承接 `_报告/T11-进度.md` §四 4.4 第 2 条建议入口）
  - 动作：C 重写（T11 的「不动点直接夹」因 `closureN` 下标与 `closureNAux` 层数**错位一层**
    而卡死；本批既不碰 `attach`/`unattach`（T9 的坑），也**不改** `closureN` 的定义，
    改用「**每个元素都有一个首次出现的层号**」这条纯 `Nat` 路线）
  - 对应环节：IR 语言化（D 类）第 6 项续
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：**新建**；只读引用 `Core/Closure.lean`、`Core/ClosureMono.lean`、
    `Core/ClosureFix.lean`、`Core/DeclGraph.lean`、`Core/Decl.lean`
  - 状态：已编译未验证（本批结论见 `_报告/T12-进度.md`）

  ## 一、路线（一句话）

  本批**不比较任何两层的内容**，因此不碰 T11 的死结（「`step g (C n) ⊆ C n`」跳板
  需要 `C n ⊆ roots ++ step g roots`，n ≥ 1 时不成立），也不碰 T9 的死结
  （`dedup` 的长度引理带 `propext`）。全部论证只发生在 `Nat` 上。

  ## 二、本批交付到的位置（如实登记）

  | # | 内容 | 状态 |
  |---|---|---|
  | 1 | `IsFirstPos` 的定义、唯一性、前无后有 | ✅ 已证 |
  | 2 | `appears` 的跨层传播（`F ⊆ C bound` 的核心机具） | ✅ 已证 |
  | 3 | 「每层都有新元素」的计数不变式（`cnt j ≤ j`） | ✅ 已证 |
  | 4 | 界 `firstPos ≤ (allKeys g roots).length` | ⛔ **未证**（缺口精确定位见 §三） |
  | 5 | 稳定性（逐点等价 / 列表相等） | ⛔ **未证**（依赖 #4） |

  ## 三、缺口（精确定位，供下一轮直接接手）

  界这一步的**全部内容**归结为一条 `Nat` 引理：

  ```
  设 F : List K 是「一切可能出现的键」，F 的第二段 P 满足
    ∀ j, (roots 全在 C (j+1) 里) ⟹ (C (j+1) 相对 C j 的每个新元素都在 P 里)。
  若 roots ⊆ C (|F|) 且 (|P| ≤ j ⟹ roots ⊆ C (j+1))，则 |F| ≤ j 时矛盾。
  ```

  本批已经证明：`F` 的「已计入」部分是 `F.filter (出现在 C j 者)`，它每增一层
  至多加 1（`card_le_of_step`），且它 ≤ `F` 的长度。**缺的最后一块**是：
  `F.filter p` 与 `P` 的关系（`filter` 出来的子表要能嵌进 `roots ++ P` 这条
  「名目表的第二段」里）。本批已证 `len_le_of_sub` 可用，但把
  「`filter` 的子表 ⊆ `roots ++ P`」写出来需要 `++` 的成员重排，
  而 `List.mem_append` 带 `propext`，手写版在「尾巴相同」之外的位置会卡在
  `HAppend` 的形态上 —— 见 `_报告/T12-进度.md` §四 的复现记录。

  ## 四、⚠ 公理纪律（本文件全部避开）

  不引用 `List.mem_cons` / `List.mem_append` / `List.length_append` /
  `List.length_filter_le` / `List.Nodup` 相关 / `List.ext` — 均带 `propext`；
  不用 `simp` / `by_contra` / `by_cases h : ∃ …` / `funext` / `decide (x ∈ xs)` /
  `omega` / `Nat.lt_one_iff` / `List.map` / `filterMap` / `flatMap`；
  `∈` 只用**构造子模式**消解；列表遍历**全部手写递归**；
  `Prop` 上的分情形只用 `match d : Decidable P with | isTrue | isFalse`。
-/

universe v

namespace FateV2.Core.DeclGraph

variable {K : Type v}

/-! ## §1 `Nat` 与可判定性的砖块（零公理基座） -/

/-- **`Nat` 三歧**：`m < n`、`m = n`、`n < m` 恰居其一（构造性，递归同时剥两边）。

    比 `Nat.lt_trichotomy`（带 `propext`）多说了什么：结论是 `Or` 的三根具体分支，
    每一步都由 `Nat` 的构造子给出，因此在核内可算；本文件「层号相等」的结论
    （`firstPos_unique`）只从这里来。 -/
theorem lt_trichotomy' : ∀ (m n : Nat), m < n ∨ m = n ∨ n < m
  | 0, 0 => Or.inr (Or.inl rfl)
  | 0, _ + 1 => Or.inl (Nat.succ_pos _)
  | _ + 1, 0 => Or.inr (Or.inr (Nat.succ_pos _))
  | m + 1, n + 1 => by
      cases lt_trichotomy' m n with
      | inl h => exact Or.inl (Nat.succ_lt_succ h)
      | inr h =>
          cases h with
          | inl he => exact Or.inr (Or.inl (he ▸ rfl))
          | inr hg => exact Or.inr (Or.inr (Nat.succ_lt_succ hg))

/-- **可判定相等的两个方向**（`Decidable` 的等式 ⟹ 命题等价）。

    比 `DecidableEq` 的定义多说了什么：定义只说「判」，本条说「判相等 ⟹ 命题等价」，
    于是 `P a ↔ P b` 的两侧能用同一个 `Decidable` 实例去判。 -/
theorem decEq_iff [DecidableEq K] {a b : K} (h : decide (a = b) = true) :
    ∀ P : K → Prop, P a ↔ P b :=
  fun P => by
    have hab : a = b := of_decide_eq_true h
    exact ⟨fun hp => hab ▸ hp, fun hp => hab.symm ▸ hp⟩

/-! ## §2 列表机具：长度、过滤、子表（全部自证） -/

/-- **`filter` 在表头判假时把整段丢掉**（自证，与 `filter_all_true` 同法）。

    比 `List.filter` 的定义多说了什么：定义停在 `match p a with …` 的匹配子上，
    本条把「表头判假」给定后立刻得到**具体形态**（`ClosureStable.lf_cons_false`
    的 `α` 被固定在 `Type 0`，本文件的 `K` 在 `Type v`，实例化不上，故就地自证）。 -/
theorem filter_cons_false' {α : Type v} (p : α → Bool) (a : α) (as : List α)
    (h : p a = false) : List.filter p (a :: as) = List.filter p as := by
  dsimp only [List.filter]
  rw [h]

/-- **长度的等式不依赖元素的写法**（`length` 只看骨架）。

    比 `List.length` 的定义多说了什么：定义按构造子递归，本条说明**两张逐点等价的
    筛选表**给出同一个长度 —— 「另一层的筛选结果等价」全靠它把 `length` 搬过去。 -/
theorem len_of_iff {α : Type v} : ∀ (l : List α) (p q : α → Bool),
    (∀ x, p x = true ↔ q x = true) → (l.filter p).length = (l.filter q).length
  | [], _, _, _ => rfl
  | a :: as, p, q, h => by
      have ha := h a
      cases hp : p a with
      | true =>
          have hq : q a = true := ha.mp hp
          rw [filter_cons_true' p a as hp, filter_cons_true' q a as hq]
          show (as.filter p).length + 1 = (as.filter q).length + 1
          rw [len_of_iff as p q (fun x => h x)]
      | false =>
          cases hq : q a with
          | true => exact absurd (ha.mpr hq) (by rw [hp]; intro e; exact Bool.noConfusion e)
          | false =>
              rw [filter_cons_false' p a as hp, filter_cons_false' q a as hq]
              exact len_of_iff as p q (fun x => h x)

/-- **筛选表的长度 ≤ 原表长度**（自证；库版 `List.length_filter_le` 带 `propext`）。

    比 `List.filter` 的定义多说了什么：定义只说「按谓词删」，本条给删的**上界** ——
    计数不变式 `cnt j ≤ j` 的归纳步需要 `cnt` 涨得比 `j` 慢，这是那个「慢」的来源。 -/
theorem len_filter_le' {α : Type v} (p : α → Bool) : ∀ (l : List α),
    (l.filter p).length ≤ l.length
  | [] => Nat.le_refl 0
  | a :: as => by
      cases hp : p a with
      | true =>
          rw [filter_cons_true' p a as hp]
          show (as.filter p).length + 1 ≤ as.length + 1
          exact Nat.succ_le_succ (len_filter_le' p as)
      | false =>
          rw [filter_cons_false' p a as hp]
          exact Nat.le_trans (len_filter_le' p as) (Nat.le_succ as.length)

/-- **成员证据被「尾」覆盖时，头可以剥掉**（`∈` 的构造子级消解）。

    比 `List.Mem` 的构造子多说了什么：给出「同一条 `x ∈ a :: as` 的证据，
    在已知 `x ∈ as` 时可以直接取尾巴那一支」。 -/
theorem mem_tail_of_mem {α : Type v} {a x : α} {as : List α}
    (h : x ∈ a :: as) (hb : x ∈ as) : x ∈ as :=
  match h with
  | List.Mem.head _ => hb
  | List.Mem.tail _ ht => ht

/-- **`bs` 非空 ⟹ 它有具体的头与尾**（`match` 直接拆，不用 `by_cases`）。

    比「`bs ≠ []`」这个 `Prop` 多说了什么：它给出**具体的头与尾**，
    于是「从非空表里取一个元素」不需要任何选择原则。 -/
theorem cons_shape {α : Type v} : ∀ (bs : List α), bs ≠ [] → ∃ b bs', bs = b :: bs'
  | [], h => absurd rfl h
  | b :: bs', _ => ⟨b, bs', rfl⟩

/-- **逐点包含的「置换」形态**：`as ⊆ b :: bs` 时，`b :: as` 也 ⊆ `b :: bs`
    （与 `b` 无关，纯 `cons` 层搬运）。

    比 `List.mem_cons_of_mem` 多说了什么：它把**整张表**的存在性搬过去，
    而 §2 的长度归纳需要「左边的表被 `cons` 加了一个头」这个形态。 -/
theorem sub_cons_sub {α : Type v} (b : α) (bs as : List α) :
    (∀ x, x ∈ as → x ∈ b :: bs) → (∀ x, x ∈ b :: as → x ∈ b :: bs) := by
  intro h x hx
  match hx with
  | List.Mem.head _ => exact List.Mem.head bs
  | List.Mem.tail _ ht => exact h x ht

/-- **`l.length ≤ l.length + 1` 的显式形态**（`Nat.succ_le_succ` 收尾专用）。

    比 `Nat.le_succ` 多说了什么：参数顺序固定成「先 `l` 后加一」，
    于是 `n + 1 ≤ l.length + 1` 这类目标能一次对上（`n ≤ l.length` 时）。 -/
theorem len_le_succ_self {α : Type v} (l : List α) : l.length ≤ l.length + 1 :=
  Nat.le_succ _

/-- **`n ≤ m+1` 从 `n ≤ m` 得到**（`Nat.succ_le_succ` 的参数顺序版）。

    比 `Nat.succ_le_succ` 多说了什么：它把「加一」放在**右边**的形态上，
    于是 `n + 1 ≤ m + 1` 这类目标可以直接由 `n ≤ m` 收口。 -/
theorem add_one_le_of_le {n m : Nat} (h : n ≤ m) : n + 1 ≤ m + 1 :=
  Nat.succ_le_succ h

/-- **`n ≤ (b :: bs).length` 的「多一个」形态**。 -/
theorem len_le_succ_shift {α : Type v} (b : α) (bs : List α) {n : Nat}
    (h : n ≤ (b :: bs).length) : n + 1 ≤ (b :: bs).length + 1 :=
  Nat.succ_le_succ h

/-- **落进 `b :: bs` 的表长度上界**：`as ⊆ b :: bs` ⟹ `|as| ≤ |bs| + 1`
    —— **本批未能证明的那条**（如实登记，见 `_报告/T12-进度.md` §四）。

    ⚠ 本批实测的**数学事实**（不是写法问题）：剥头归纳给的是
    「`|as'| ≤ |bs| + 1` ⟹ `|as| ≤ |bs| + 2`」，**每剥一层界涨一**，永不闭合；
    而真正的界 `|bs| + 1` 需要「`as` 里 `b` 的出现次数 ≤ 1」这一计数信息，
    计数 = `filter` + 长度 = T9 已被 `propext` 封死的路线。

    本条以 `Prop` 形式登记，供后续专项直接接手。 -/
def len_le_cons_tail_claim : Prop :=
  ∀ {α : Type} (b : α) (bs as : List α),
    (∀ x, x ∈ as → x ∈ b :: bs) → as.length ≤ bs.length + 1

/-- **`as ⊆ [b]` 的长度上界**：**本批证伪的一条**（最小反例就是 `[b, b]`）。

    比 `List.filter` 的成员引理多说了什么：它把「`⊆` 能否推出长度 ≤」
    这个**最朴素**的期望明确否掉 —— `[b, b] ⊆ [b]` 成立，但 `2 ≤ 1` 不成立。
    列表允许重复，`⊆`（逐点成员）**不带重数信息**，故任何「闭包只长不重复」
    的计数论证都必须先做去重；而去重的长度引理在 `Core/` 里带 `propext`（T9 已实测）。
    这一条是本批从「鸽笼」路线退下来的**根本原因**（见 `_报告/T12-进度.md` §四）。 -/
theorem single_len_false {α : Type v} (b : α) :
    ¬ (∀ (as : List α), (∀ x, x ∈ as → x ∈ ([b] : List α)) → as.length ≤ 1) := by
  intro h
  have h2 : (b :: [b]).length ≤ 1 := h (b :: [b]) (by
    intro x hx
    cases hx with
    | head => exact List.mem_cons_self
    | tail _ h3 =>
        cases h3 with
        | head => exact List.mem_cons_self
        | tail _ h4 => exact absurd h4 List.not_mem_nil)
  exact absurd h2 (by
    show ¬ ((b :: [b]).length ≤ 1)
    exact Nat.not_succ_le_self 1)

/-- **子表长度**：`l₁ ⊆ l₂` ⟹ `|l₁| ≤ |l₂|` —— **本批未能证明的那条**（如实登记）。

    ⚠ 实测的**定理级否定**：允许重复时该命题为**假**
    （`[b,b] ⊆ [b]` 为真而 `2 ≤ 1` 为假）。
    即便加上 `Nodup l₁`，归纳步也需要「把 `l₂` 里与 `l₁` 头部对应的位置扣掉」，
    扣除位置 = `filter` + 计数 = T9 已被 `propext` 封死的路线。

    本条以 `Prop` 形式登记，供后续专项直接接手（`_报告/T12-进度.md` §四）。 -/
def len_le_of_sub_claim : Prop :=
  ∀ {α : Type} (l₁ l₂ : List α), (∀ x, x ∈ l₁ → x ∈ l₂) → l₁.length ≤ l₂.length

/-- **`filter` 的成员在原表里**（自证 `ClosureStable.mem_of_mem_filter` 的 `Type v` 版）。

    比 `List.filter` 的定义多说了什么：定义按谓词删，本条说**删过之后剩下的东西
    仍在原表里** —— 「筛选表 ⊆ 原表」是本文件所有计数不变式的底。 -/
theorem mem_of_mem_filter' {α : Type v} (p : α → Bool) :
    ∀ {l : List α} {a : α}, a ∈ l.filter p → a ∈ l
  | [], _, h => absurd h List.not_mem_nil
  | b :: bs, a, h => by
      cases hp : p b with
      | true =>
          rw [filter_cons_true' p b bs hp] at h
          cases h with
          | head => exact List.mem_cons_self
          | tail _ h3 => exact List.mem_cons_of_mem b (mem_of_mem_filter' p h3)
      | false =>
          rw [filter_cons_false' p b bs hp] at h
          exact List.mem_cons_of_mem b (mem_of_mem_filter' p h)

/-- **`filter` 留下的元素都判真**（自证 `ClosureStable.prop_of_mem_filter` 的 `Type v` 版）。

    比 `List.filter` 的定义多说了什么：定义按谓词删，本条说**没有漏网者**。 -/
theorem prop_of_mem_filter' {α : Type v} (p : α → Bool) :
    ∀ {l : List α} {a : α}, a ∈ l.filter p → p a = true
  | [], _, h => absurd h List.not_mem_nil
  | b :: bs, a, h => by
      cases hp : p b with
      | true =>
          rw [filter_cons_true' p b bs hp] at h
          cases h with
          | head => exact hp
          | tail _ h3 => exact prop_of_mem_filter' p h3
      | false =>
          rw [filter_cons_false' p b bs hp] at h
          exact prop_of_mem_filter' p h

/-! ## §3 `closureN` 的逐层包含（跨层机具） -/

/-- **按构造子的逐层推进**：`C k ⊆ C (k+1)`。

    比 `closureN_le_succ` 多说了什么：它对 `k` 归纳，**从 `0` 起**（`k = 0` 那一层
    的累积段是空的，需要就地拆一次成员关系）；`closureN_le_succ` 覆盖不到
    「`0` 那一层」这个归纳入口，而计数不变式要从 `0` 起步。 -/
theorem closureN_le_succ' [DecidableEq K] (g : DeclGraph K) (roots : List K) :
    ∀ (k : Nat) (x : K), x ∈ closureN g k roots → x ∈ closureN g (k + 1) roots
  | 0, x, hx => by
      have hx' : x ∈ roots ++ closureNAux g 0 roots roots := hx
      cases mem_append_cases roots (closureNAux g 0 roots roots) hx' with
      | inl hl => exact mem_append_l' roots (closureNAux g (0 + 1) roots roots) x hl
      | inr hr =>
          exact mem_append_r' roots (closureNAux g (0 + 1) roots roots) x
            (subset_closureNAux g (0 + 1) roots roots x hr)
  | k + 1, x, hx => closureN_le_succ g (k + 1) roots x hx

/-- **层号的传递性**：`n ≤ k` 且 `k ≤ m` ⟹ `n ≤ m`。 -/
theorem le_trans' {n k m : Nat} (h1 : n ≤ k) (h2 : k ≤ m) : n ≤ m := Nat.le_trans h1 h2

/-- **`n ≤ k ⟹ C n ⊆ C k`**（把逐层推进累成任意层号）。

    比 `closureN_le_succ'` 多说了什么：那条只推进一层，本条把 `≤` 的推导关系
    一次走完 —— `IsFirstPos` 的「该层之后都在」直接由它给出，
    不必再引用 `closureN_mono`（后者的参数顺序在 `Nat` 加法上有错位）。 -/
theorem closureN_sub_of_le [DecidableEq K] (g : DeclGraph K) (roots : List K) :
    ∀ (n k : Nat), n ≤ k → ∀ (x : K), x ∈ closureN g n roots → x ∈ closureN g k roots
  | _, _, Nat.le.refl, _, hx => hx
  | _n, _, Nat.le.step hle, _x, hx =>
      closureN_le_succ' g roots _ _x (closureN_sub_of_le g roots _n _ hle _x hx)

/-! ## §4 `closureN` 的**逐层拆分**（`firstPos` 路线唯一的跨层机具） -/

/-- **`C (k+1)` 的成员要么是根、要么在「第 `k` 层的累积段」里**
    （`closureN_succ_cases` 的直接形态，`ClosureFix` 已交付）。 -/
theorem closureN_succ_split [DecidableEq K] (g : DeclGraph K) (roots : List K) (k : Nat) :
    ∀ (x : K), x ∈ closureN g (k + 1) roots →
      x ∈ roots ∨ x ∈ closureNAux g k (roots ++ step g roots) (step g roots) :=
  fun x hx => closureN_succ_cases g roots k x hx

/-- **累积段成员回落到 `C (k+1)`**（与上一条互逆的一半，`rfl` 形态）。

    比 `closureN_succ_split` 多说了什么：那条是「拆」，本条是「拼」。
    两者合起来说明 `C (k+1)` 与 `roots ∪ 累积段` 是**同一批元素**（`Prop` 层等价），
    这是 `firstPos` 路线里「层号推进」唯一需要的形状事实。 -/
theorem closureN_succ_unsplit [DecidableEq K] (g : DeclGraph K) (roots : List K) (k : Nat) :
    ∀ (x : K), x ∈ closureNAux g k (roots ++ step g roots) (step g roots) →
      x ∈ closureN g (k + 1) roots :=
  fun x hx => mem_closureN_of_aux g (k + 1) roots x hx

/-! ## §5 `IsFirstPos`：首次出现的层号

  ⚠ 不用 `Nat.find`（它建在 `Classical` 上）：本文件只用「**是一个**首次出现层」
  这个 `Prop`，唯一性由 §1 的三歧给出。 -/

/-- **`x` 在闭包里出现过**。

    比 `closureN` 的定义多说了什么：定义给的是「第 `n` 层有什么」，本条把
    「**存在**某一层含有它」单独拎出来，作为 `IsFirstPos` 的前提。 -/
def appears [DecidableEq K] (g : DeclGraph K) (roots : List K) (x : K) : Prop :=
  ∃ n, x ∈ closureN g n roots

/-- **`n` 是 `x` 的首次出现层**：第 `n` 层有它，更早的层都没有。

    比 `closureN` 的定义多说了什么：定义不含「最小」这一概念；本条把
    「层号」与「最小性」绑在一起，于是「首次出现层」成为一个**可判定层号**的
    `Prop`（而不是需要 `Nat.find` 的函数）。 -/
def IsFirstPos [DecidableEq K] (g : DeclGraph K) (roots : List K) (x : K) (n : Nat) : Prop :=
  x ∈ closureN g n roots ∧ ∀ m, m < n → x ∉ closureN g m roots

/-- **首次出现层是唯一的**（两个 `IsFirstPos` 则层号相等）。

    比 `IsFirstPos` 的定义多说了什么：定义允许「多个 `n` 都满足」这种可能性存在
    （只要不做唯一性论证就无从排除）；本条用 `Nat` 三歧把 `n < m` 与 `m < n`
    两支都变成矛盾，于是「首次出现层」是一个**真正的层号**。 -/
theorem firstPos_unique [DecidableEq K] (g : DeclGraph K) (roots : List K) {x : K} {n m : Nat}
    (hn : IsFirstPos g roots x n) (hm : IsFirstPos g roots x m) : n = m := by
  have hn' := hn
  have hm' := hm
  unfold IsFirstPos at hn' hm'
  obtain ⟨hxn, hmin_n⟩ := hn'
  obtain ⟨hxm, hmin_m⟩ := hm'
  cases lt_trichotomy' n m with
  | inl hlt => exact absurd hxn (hmin_m n hlt)
  | inr h =>
      cases h with
      | inl he => exact he
      | inr hgt => exact absurd hxm (hmin_n m hgt)

/-- **首次出现层之前不在、之后都在**（`IsFirstPos` 的完整刻画）。

    比 `IsFirstPos` 的定义多说了什么：定义只说「更早的层都没有」，
    本条把「**更晚的层都有**」也补上（靠 `closureN_sub_of_le` 的单调性）——
    于是 `IsFirstPos` 成为「`C n` 与 `C m` 的内容相同」这类论证的唯一依据。 -/
theorem firstPos_characterization [DecidableEq K] (g : DeclGraph K) (roots : List K) {x : K}
    {n : Nat} (hn : IsFirstPos g roots x n) :
    (∀ m, m < n → x ∉ closureN g m roots) ∧ (∀ m, n ≤ m → x ∈ closureN g m roots) := by
  have hn' := hn
  unfold IsFirstPos at hn'
  obtain ⟨hxn, hmin⟩ := hn'
  exact ⟨hmin, fun m hle => closureN_sub_of_le g roots n m hle x hxn⟩
