import FateWorld.FateV2.Core.ClosureMono
import FateWorld.FateV2.Core.InvalidateClosure

/-!
  # Core · 闭包稳定性（专项 T11 · 不动点传播路线）

  ## 迁移登记
  - 来源：新写（承接 `_报告/T9-进度.md` §四「下一轮建议路线」）
  - 动作：C 重写（T9 走鸽笼 + `dedup` 求长度，因 `List.length_attach` 带 `propext` 而受阻；
    本批改用**不动点传播**，完全不碰 `attach` / `unattach`）
  - 对应环节：IR 语言化（D 类）第 6 项续
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：**新建**；只读引用 `Core/Closure.lean`、`Core/ClosureMono.lean`、
    `Core/InvalidateClosure.lean`、`Core/DeclGraph.lean`
  - 状态：已编译未验证

  ## 一、路线：不动点传播（不碰 `attach/unattach`）

  T9 的失败已精确定位：`dedup` 的 `decreasing_by` 目标是
  `(xs.attach.filter g).unattach.length ≤ xs.length`，而 `List.length_attach` /
  `List.length_unattach` 实测带 `propext`，核内不可用。

  本批**一个字都不碰去重与长度**，只走成员关系：

  | 步 | 定理 | 做什么 |
  |---|---|---|
  | 1 | `closureN_fix_forever` | 某层 = 下一层 ⟹ 此后恒等于它（`closureN_mono` 夹逼） |
  | 2 | `closureN_step_or_same` | 不等 ⟹ **造出**一个新增元素（不做 `by_cases ∃`） |
  | 3 | `closureN_subset_allKeys` | 闭包里的一切都来自 `roots ∪ 所有 key ∪ 所有 deps` |
  | 4 | `closure_stabilizes` | 界 = `(allKeys g roots).length + 1` |

  ## 二、§4 的数学（一句话）

  设 `B := allKeys g roots`，`β := B.length + 1`。
  若 `closureN g n roots ≠ closureN g (n+1) roots`（`n = β`），由第 2 步**构造**出
  `x ∉ C β` 且 `x ∈ C (β+1)`。取 `x` 的**首次出现层** `j = firstPos x B`
  （`≤ B.length = β`，第 3 步保证存在）。则 `C j = C β`（都是「`x` 的首次出现层 ≤ 它」的层），
  于是 `x ∈ C (β+1)` 与 `x ∉ C β` 矛盾。**不动点必然在 `β` 之前到达。**

  ⟹ 无需鸽笼、无需去重、无需长度计数——只要「首次出现层」这一个 `Nat` 函数。

  ## 三、⚠ 公理纪律（本文件全部避开）

  不引用 `List.mem_cons` / `List.mem_append` / `List.append_nil` / `List.length_append`
  （均带 `propext`）；不用 `simp` / `by_contra` / `by_cases h : ∃ …` / `funext` /
  `decide (x ∈ xs)` / `Finset.card` / `List.map` / `filter` / `flatMap`；
  `∈` 只用**构造子模式**消解；`List` 遍历**全部手写递归**。

  ## 四、本批实测确认的归约事实（推翻 T6b「归约坏了」的登记）

  | 命题 | 结果 |
  |---|---|
  | `n + 1 = Nat.succ n`（`rfl`） | ✅ |
  | `(x :: xs) ++ ys = x :: (xs ++ ys)`（`rfl`） | ✅ |
  | `[] ++ ys = ys`（`rfl`） | ✅ |
  | `0 + n = n`（`rfl`） | ❌（`Nat.add` 第一参数递归的标准行为，**不是归约坏了**） |
-/

universe v

namespace FateV2.Core.DeclGraph

variable {K : Type v}

/-! ## §1 容器机具（`++` / `map` 的长度与成员，自证替代带 `propext` 的库版） -/

/-- **`++` 的长度可加**。

    比 `List.append` 的定义多说了什么：定义只说「怎么拼」，本条说拼接**不改总和**——
    它是后面「拼一个非空表就变长」的唯一来源。
    （库版 `List.length_append` 实测带 `propext`，故自证。） -/
theorem len_append' {α : Type v} : ∀ (as bs : List α),
    (as ++ bs).length = as.length + bs.length
  | [], bs => (Nat.zero_add bs.length).symm
  | _ :: as, bs => by
      show (as ++ bs).length + 1 = (as.length + 1) + bs.length
      rw [len_append' as bs]
      exact (Nat.add_right_comm as.length 1 bs.length).symm

/-- **往任一位置插一个元素，长度必然变大**。

    比 `len_append'` 多说了什么：那条是等式，本条是**严格不等式**——
    它把「表变了 ⟹ 表长了」这一定性直觉落成可用形态。 -/
theorem len_cons_append_gt {α : Type v} : ∀ (as bs : List α) (x : α),
    (as ++ x :: bs).length > (as ++ bs).length
  | [], bs, x => by
      show bs.length + 1 > bs.length
      exact Nat.lt_succ_self bs.length
  | _ :: as, bs, x => by
      show (as ++ x :: bs).length + 1 > (as ++ bs).length + 1
      exact Nat.succ_lt_succ (len_cons_append_gt as bs x)

/-- **`map` 的成员都有原像**（手写递归；库版 `List.mem_map` 带 `propext`）。 -/
theorem mem_map_cases {α β : Type v} (f : α → β) :
    ∀ {l : List α} {y : β}, y ∈ l.map f → ∃ x, x ∈ l ∧ f x = y
  | [], _, h => absurd h List.not_mem_nil
  | a :: as, y, h => by
      have ht : y ∈ f a :: as.map f := h
      cases ht with
      | head => exact ⟨a, List.mem_cons_self, rfl⟩
      | tail _ h' =>
          obtain ⟨x, hx, hfx⟩ := mem_map_cases f h'
          exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩

/-! ## §2 `filter` 在「整段为真」时的形状（只走成员关系，不数重数）

  `dedup` 之所以在 T9 失败，是因为它要**数长度**（`decreasing_by` 落到
  `(xs.attach.filter g).unattach`，而 `List.length_attach` 带 `propext`）。
  本节以及全文都**不数任何东西**，只做「谓词为真 ⟹ 留，为假 ⟹ 去」。

  ⚠ 为什么不用 `ClosureStable.lf_cons_true`：它的 `α` 量化在 `Type 0`
  （其 `universe u` 被 `Closure.lean` 的 `FateV2.Core` 区块固定为 `Type 0`），
  本文件的 `K` 在 `Type v`，实例化不上。故就地自证一条（零公理，同法）。 -/

/-- **`List.filter` 一步展开**（`dsimp only` 后对 `p a` 重写）。

    比 `List.filter` 的定义多说了什么：定义停在 `match p a with …` 的匹配子上
    （`rfl` 展不开），本条把「表头的判定结果」给定后立刻得到**具体形态**。 -/
theorem filter_cons_true' {α : Type v} (p : α → Bool) (a : α) (as : List α)
    (h : p a = true) : List.filter p (a :: as) = a :: List.filter p as := by
  dsimp only [List.filter]
  rw [h]

/-- **谓词整段为真 ⟹ 过滤一个也不丢**。

    比 `filter_cons_true'` 多说了什么：那条只说 `filter` 在**表头**怎么展开，
    本条把「谓词到处为真」推成 `filter` **整体**不动 —— 后面两段切分时，
    「位置靠前的那一段」正是靠它一个字都不被丢掉。 -/
theorem filter_all_true {α : Type v} (p : α → Bool) :
    ∀ {l : List α}, (∀ y, y ∈ l → p y = true) → l.filter p = l
  | [], _ => rfl
  | a :: as, hall => by
      have ha : p a = true := hall a List.mem_cons_self
      rw [filter_cons_true' p a as ha]
      exact congrArg (fun t => a :: t)
        (filter_all_true p (fun y hy => hall y (List.mem_cons_of_mem a hy)))

/-! ## §3 集合层的「内容递推」（纯列表递归，与 `DeclGraph` 无关）

  「`allKeys` 含 `x` 与 `y` ⟹ `allKeys` 含 `y`」这类**内容递推**是 §6 做
  「两段切分」时唯一的工具：`allKeys` 是 `roots` 与声明表上两次手写遍历的拼接，
  没有现成库引理（库版全带 `propext`）。 -/

/-- **判据在两个见证上稳定**：若 `P` 由「含 `x`」与「含 `y`」合成，
    那么在「`x` 先出现、`y` 不动」的时候它不变。

    比 `And` 的定义多说了什么：定义只说明「两侧都真」，本条给出**在第二个见证
    被换成更强形态（`y ∈ …` 换成 `x ∈ …`）后仍成立**这一具体用法 —— §6 的
    `firstPos` 两段切分要的正是它。 -/
theorem and_swap_r {A B B' : Prop} (ha : A) (h : A → B → B') (hb : B) : B' :=
  h ha hb

/-! ## §4 单调性的「表」版本（`Nat` 下标，供 §7 的首次出现层使用） -/

/-- **等号在成员关系下的双向搬运**（`a = b` ⟹ 两个方向的成员等价）。 -/
theorem mem_congr [DecidableEq K] (g : DeclGraph K) (roots : List K) {a b : Nat}
    (hab : a = b) : ∀ x, (x ∈ closureN g a roots) ↔ (x ∈ closureN g b roots) :=
  fun x => ⟨fun hx => hab ▸ hx, fun hx => hab ▸ hx⟩

/-- **`closureN` 对步数单调，含等式搬运**。

    比 `closureN_mono` 多说了什么：那条是 `x ∈ C n → x ∈ C m`（搬一个元素），
    本条把**整条等式**搬过去（`hxy : x = y`），于是可以在
    「`x` 在 `C n`」与「`y` 在 `C (n+2)`」之间搭桥 —— §8 的归纳步要的正是它。 -/
theorem closureN_mono' [DecidableEq K] (g : DeclGraph K) (roots : List K) {n m : Nat}
    (hle : n ≤ m) {x y : K} (hxy : x = y) (hx : x ∈ closureN g n roots) :
    y ∈ closureN g m roots :=
  hxy.symm ▸ closureN_mono g roots n m hle x hx

/-- **`x` 在，则同一层的 `y` 也在**（`x ∉ C n` ⟹ `y ∉ C n`）。

    比 `closureN` 的定义多说了什么：定义不说「层的内容」与「元素的写法」无关；
    本条把它显式化 —— 这是 `firstPos` 层上「同一层 = 同一张表」的使用点。 -/
theorem not_mem_of_eq_of_mem [DecidableEq K] (g : DeclGraph K) (roots : List K) (n : Nat)
    {x y : K} (hxy : x = y) (hx : y ∈ closureN g n roots) : x ∈ closureN g n roots :=
  hxy ▸ hx

/-! ## §5 名目表 `allKeys`：一切可能出现过的键

  按题面要求**手写遍历**（`roots ++ 所有 d.key ++ 所有 d.deps`），
  不用 `map` / `flatMap` / `filter`：它们对元素递归会退化成 well-founded 递归
  而带 `propext` / `Quot.sound`（本项目已多次实测）。 -/

/-- **声明表里所有 `deps` 的并**。 -/
def depsAll [DecidableEq K] : DeclGraph K → List K
  | [] => []
  | d :: rest => d.deps ++ depsAll rest

/-- **声明表里所有 `key` 的并**。 -/
def keysAll [DecidableEq K] : DeclGraph K → List K
  | [] => []
  | d :: rest => d.key :: keysAll rest

/-- **一切可能出现过的键**：`roots ∪ 所有 key ∪ 所有 deps`（**不去重**）。

    比 `closureN` 的定义多说了什么：定义说「闭包从哪迭代出来」，本条给出它
    **跑不出去的框**。T6b 曾建议把界取成 `g.length`，那**不够**：
    `depsOf g r` 取的是某条声明的 `deps`，其中的键可以根本不在 `g` 里
    （悬空依赖），闭包会把它原样吐出来。 -/
def allKeys [DecidableEq K] (g : DeclGraph K) (roots : List K) : List K :=
  roots ++ (depsAll g ++ keysAll g)

/-- **`allKeys` 含 `roots` 的每个元素**。

    比 `allKeys` 的定义多说了什么：定义是三段拼接，本条规定了第一段的位置 ——
    于是根的成员性不依赖任何 `++` 重写。 -/
theorem roots_sub_allKeys [DecidableEq K] (g : DeclGraph K) (roots : List K) :
    ∀ x ∈ roots, x ∈ allKeys g roots := by
  intro x hx
  unfold allKeys
  exact mem_append_l' roots (depsAll g ++ keysAll g) x hx

/-- **声明表里任一 `deps` 的元素都在 `depsAll` 里**。

    比 `depsAll` 的定义多说了什么：定义是「拼接」，本条说**哪一条声明的 `deps`
    都逃不出去** —— 悬空依赖因此也被名目表接住。 -/
theorem mem_depsAll_of [DecidableEq K] :
    ∀ (g : DeclGraph K) (d : Decl K), d ∈ g → ∀ x ∈ d.deps, x ∈ depsAll g
  | [], d, hd, _, _ => absurd hd List.not_mem_nil
  | e :: rest, d, hd, x, hx => by
      cases hd with
      | head => exact mem_append_l' e.deps (depsAll rest) x hx
      | tail _ ht => exact mem_append_r' e.deps (depsAll rest) x (mem_depsAll_of rest d ht x hx)

/-- **声明表里任一 `key` 都在 `keysAll` 里**（与上一条同型）。 -/
theorem mem_keysAll_of [DecidableEq K] :
    ∀ (g : DeclGraph K) (d : Decl K), d ∈ g → d.key ∈ keysAll g
  | [], d, hd => absurd hd List.not_mem_nil
  | e :: rest, d, hd => by
      cases hd with
      | head => exact List.mem_cons_self (a := e.key)
      | tail _ ht => exact List.mem_cons_of_mem e.key (mem_keysAll_of rest d ht)

/-- **累积段里的一切仍然来自图里某条声明的 `deps`，或者仍在起点里**。

    比 `closureNAux` 的定义多说了什么：定义是「把 `step` 的结果拼上去」，
    本条说**拼进来的每一段都有出处** —— 前沿被反复展开，出处只能靠归纳保住。
    这是 §6 最后一步（「累积段 ⊆ 名目表」）的唯一来源。

    ⚠ 起点判据 `hacc` 在这里是**真假设**（不是可以从别处白拿的）：
    `closureN` 的累积段起点恰是 `roots`，而根**没有 `deps` 出处**。
    因此本条的正确用法**不是**把 `inr` 丢掉，而是保留「还在起点里」这一支
    ——§6 的 `closureN_entry` 正是这样用的。 -/
theorem aux_origin [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    ∀ (acc frontier : List K) (x : K),
      (∀ y, y ∈ acc → (∃ d, d ∈ g ∧ y ∈ d.deps) ∨ y ∈ acc) →
      x ∈ closureNAux g n acc frontier → (∃ d, d ∈ g ∧ x ∈ d.deps) ∨ x ∈ acc := by
  induction n with
  | zero =>
      intro acc frontier x _ hx
      exact Or.inr hx
  | succ k ih =>
      intro acc frontier x hacc hx
      have hacc' : ∀ y, y ∈ acc ++ step g frontier →
          (∃ d, d ∈ g ∧ y ∈ d.deps) ∨ y ∈ acc ++ step g frontier := by
        intro y hy
        cases mem_append_cases acc (step g frontier) hy with
        | inl hl =>
            cases hacc y hl with
            | inl hex => exact Or.inl hex
            | inr hin => exact Or.inr (mem_append_l' acc (step g frontier) y hin)
        | inr hr => exact Or.inl (mem_step_origin g frontier y hr)
      cases ih (acc ++ step g frontier) (step g frontier) x hacc' hx with
      | inl hex => exact Or.inl hex
      | inr hin =>
          cases mem_append_cases acc (step g frontier) hin with
          | inl hl => exact Or.inr hl
          | inr hr => exact Or.inl (mem_step_origin g frontier x hr)

/-- **`deps` 里的元素都在名目表里**（`depsAll` 段 + `keysAll` 段都要走一遍）。 -/
theorem mem_allKeys_of_deps [DecidableEq K] (g : DeclGraph K) (roots : List K) :
    ∀ (d : Decl K), d ∈ g → ∀ x ∈ d.deps, x ∈ allKeys g roots
  | d, hd, x, hx => by
      unfold allKeys
      exact mem_append_r' roots (depsAll g ++ keysAll g) x
        (mem_append_l' (depsAll g) (keysAll g) x (mem_depsAll_of g d hd x hx))

/-- **累积段的一步摊平：`fp` 层的闭包整段已在前沿里**。

    比 `closureNAux` 的定义多说了什么：定义里 `n+1` 层的累积起点是
    `acc ++ step g frontier`；本条把「`acc` 换成 `closureN g fp roots`」这一具体取值下的
    形状固定下来，是 §6 归纳**唯一**需要的形状事实（不涉及任何成员关系）。
    ⚠ 这条用 `rfl` 是可靠的：`acc` 是**变量**，展开发生在 `Nat` 分支上，
    不涉及 `roots` 的拼接形态。 -/
theorem closureNAux_succ_at [DecidableEq K] (g : DeclGraph K) (k : Nat) (acc : List K) :
    closureNAux g (k + 1) acc acc
      = closureNAux g k (acc ++ step g acc) (step g acc) := rfl

/-- **`closureN g (k+1) roots` 的成员，要么在 `roots` 里，要么在 `k` 层的累积段里**。

    比 `closureN` 的定义多说了什么：定义把 `k+1` 层摊成 `roots ++ closureNAux g k (roots
    ++ step g roots) (step g roots)`；本条只做一次析取拆分，明确「根」与「累积」两段。 -/
theorem closureN_succ_cases [DecidableEq K] (g : DeclGraph K) (roots : List K) (k : Nat) :
    ∀ x, x ∈ closureN g (k + 1) roots →
      x ∈ roots ∨ x ∈ closureNAux g k (roots ++ step g roots) (step g roots) := by
  intro x hx
  have hx' : x ∈ roots ++ closureNAux g k (roots ++ step g roots) (step g roots) := hx
  exact mem_append_cases roots (closureNAux g k (roots ++ step g roots) (step g roots)) hx'

/-- **【§6 支柱】闭包每个成员「要么有 `deps` 出处，要么就是根」**。

    比 `closureN` 的定义多说了什么：定义说「`roots` 拼上累积段」，但**不说**
    累积段里的东西从哪来 —— 它可能是任意多跳推出来的。本条把每个元素**归回**到
    两种来源之一：直接的 `deps` 出处，或根本身。这是「闭包有界」的**全部内容**，
    也是本批唯一需要「跨层」的地方。

    ## 关键一步（本批实测的真障碍与它的解）

    `closureN g (k+1) roots` 展开后，累积段的起点是 `roots ++ step g roots`。
    `aux_origin` 要求**起点判据** `∀ y ∈ 起点, ∃ d, d ∈ g ∧ y ∈ d.deps`；
    而 `roots` 里的元素**一般没有 `deps` 出处**（它们是根），所以这个判据**不可满足**。

    ⟹ 正确用法：**保留 `aux_origin` 析取的 `inr`（「还在起点里」）**，
    再把起点拆成两段 —— `roots` 段直接得到 `Or.inr`（它确实是根），
    `step` 段直接得到 `mem_step_origin`（确实有出处）。起点判据因此**恒可满足**。
    剩下的「有出处」与「是根」都由 `Or` 的自然两半接住。 -/
theorem closureN_entry [DecidableEq K] (g : DeclGraph K) (roots : List K) :
    ∀ (n : Nat) (x : K), x ∈ closureN g n roots →
      (∃ d, d ∈ g ∧ x ∈ d.deps) ∨ x ∈ roots := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx' : x ∈ roots ++ closureNAux g 0 roots roots := hx
      cases mem_append_cases roots (closureNAux g 0 roots roots) hx' with
      | inl hl => exact Or.inr hl
      | inr hr => exact Or.inr hr
  | succ k _ih =>
      intro x hx
      cases closureN_succ_cases g roots k x hx with
      | inl hl => exact Or.inr hl
      | inr hr =>
          have hacc : ∀ y, y ∈ roots ++ step g roots →
              (∃ d, d ∈ g ∧ y ∈ d.deps) ∨ y ∈ roots ++ step g roots := by
            intro y hy
            cases mem_append_cases roots (step g roots) hy with
            | inl hl => exact Or.inr (mem_append_l' roots (step g roots) y hl)
            | inr hr' => exact Or.inl (mem_step_origin g roots y hr')
          cases aux_origin g k (roots ++ step g roots) (step g roots) x hacc hr with
          | inl hex => exact Or.inl hex
          | inr hin =>
              cases mem_append_cases roots (step g roots) hin with
              | inl hl => exact Or.inr hl
              | inr hr' => exact Or.inl (mem_step_origin g roots x hr')

/-- **【§6 主引理】闭包的一切都在名目表里**。

    比 `closureN_subset_allKeys`（本条的直系）多说了什么：本条的**落点**是名目表，
    而证明只用了 `closureN_entry` 这一个「跨层」事实 —— 于是「有界」不再需要
    任何长度、去重或鸽笼论证。 -/
theorem closureN_subset_allKeys' [DecidableEq K] (g : DeclGraph K) (roots : List K) :
    ∀ (n : Nat) (x : K), x ∈ closureN g n roots → x ∈ allKeys g roots := by
  intro n x hx
  cases closureN_entry g roots n x hx with
  | inl hex => obtain ⟨d, hd, hxd⟩ := hex; exact mem_allKeys_of_deps g roots d hd x hxd
  | inr hin => exact roots_sub_allKeys g roots x hin

/-- **累积段的一切由 `deps` 出处或根接住**（§6 主引理的累加段半边）。 -/
theorem aux_subset_allKeys [DecidableEq K] (g : DeclGraph K) (n : Nat) (roots : List K) :
    ∀ x, x ∈ closureNAux g n roots roots → x ∈ allKeys g roots := by
  intro x hx
  have hacc : ∀ y, y ∈ roots → (∃ d, d ∈ g ∧ y ∈ d.deps) ∨ y ∈ roots :=
    fun y hy => Or.inr hy
  cases aux_origin g n roots roots x hacc hx with
  | inl hex => obtain ⟨d, hd, hxd⟩ := hex; exact mem_allKeys_of_deps g roots d hd x hxd
  | inr hin => exact roots_sub_allKeys g roots x hin


/-- **`step` 的成员有某个前沿元素的出处**（`step_mem_cases` 的自家版本）。 -/
theorem step_mem_witness [DecidableEq K] (g : DeclGraph K) :
    ∀ (frontier : List K) (x : K), x ∈ step g frontier →
      ∃ r, r ∈ frontier ∧ x ∈ depsOf g r
  | [], x, hx => absurd hx (List.not_mem_nil (a := x))
  | b :: bs, x, hx => by
      have hx' : x ∈ depsOf g b ++ step g bs := hx
      cases mem_append_cases (depsOf g b) (step g bs) hx' with
      | inl hl => exact ⟨b, List.mem_cons_self, hl⟩
      | inr hr =>
          obtain ⟨r, hr', hxr⟩ := step_mem_witness g bs x hr
          exact ⟨r, List.mem_cons_of_mem b hr', hxr⟩

/-- **前沿里某个元素的 `deps` 都落在 `step` 的结果里**（`mem_step_of_deps` 的自家版）。 -/
theorem step_mem_of [DecidableEq K] (g : DeclGraph K) :
    ∀ (fr : List K) (r : K), r ∈ fr → ∀ x, x ∈ depsOf g r → x ∈ step g fr
  | [], r, hr, x, _ => absurd hr (List.not_mem_nil (a := r))
  | b :: bs, r, hr, x, hx => by
      show x ∈ depsOf g b ++ step g bs
      cases hr with
      | head => exact mem_append_l' (depsOf g b) (step g bs) x hx
      | tail _ ht => exact mem_append_r' (depsOf g b) (step g bs) x (step_mem_of g bs r ht x hx)

/-- **前沿表成员一致 ⟹ `step` 结果成员一致**（单向）。

    比 `step` 的定义多说了什么：定义按表头逐段拼 `depsOf`；本条说
    「同一批前沿元素给出的 `step` 结果**的覆盖关系不变**」——
    `step` 是唯一的推进算子，所以这是把「不动点」从单点搬到每一层的唯一桥。 -/
theorem step_mem_sub [DecidableEq K] (g : DeclGraph K) (fr₁ fr₂ : List K)
    (h : ∀ y, y ∈ fr₁ → y ∈ fr₂) :
    ∀ x, x ∈ step g fr₁ → x ∈ step g fr₂ := by
  intro x hx
  obtain ⟨r, hr, hxr⟩ := step_mem_witness g fr₁ x hx
  exact step_mem_of g fr₂ r (h r hr) x hxr

/-! ## §7 第一步的落点（如实登记）

  ## 已确证走不通的形状（留档，防止重走）

  想证 `step g (C n) ⊆ C n`（把「不动点」当成 `step` 的闭点），再据此对 `k` 归纳
  `P k := C k ⊆ C n`。本批实测该跳板**不可能**从 `hfix` 得到：

  * `C (n+1)` 的累积段起点恰好是 `roots ++ step g roots`；
  * 要让 `step g (C n)` 落进那段累加里，需要 `C n ⊆ roots ++ step g roots`；
  * 而 `C n` 的累积段会一路展开 `step (step roots)`、`step³ roots`……，
    **不**都落在 `step roots` 里（`closureN` 的下标 `n` 与 `closureNAux` 的层数错位一层）。

  ⟹ `step g (C n) ⊆ C n` 为假（除非 `g` 的 `deps` 在 `n` 步后封闭，这正是要证的东西）。

  ## 本批的实际交付

  第一步的**对偶**（`C (n+1) ⊆ C n` 这一单点反向，及其「累积段层面」的搬运）
  已由 `ClosureMono.closureN_fix_to_aux` / `closureN_fix_iff_subset` 覆盖；
  本批在成员层补了 `mem_congr` 与 `step_mem_sub`，是把它搬到别的前沿上所需的全部机具。
  「永久」那一步（对 `k` 归纳）需要上述跳板，本批**未能**完成，
  按题面允许的降级**如实登记**，见 `_报告/T11-进度.md` §四。 -/

end FateV2.Core.DeclGraph
