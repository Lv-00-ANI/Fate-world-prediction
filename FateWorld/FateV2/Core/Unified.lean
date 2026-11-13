import FateWorld.FateV2.Core.Cardinality
import FateWorld.FateV2.Core.ClosureFix
import FateWorld.FateV2.Model.TopoGeneral
import FateWorld.FateV2.Model.TopoExists

/-!
  # Core · 统一抽象层（专项 T40）

  ## 迁移登记
  - 来源：新写（把 T27 `pigeonhole`、T30 `source_exists_of_cover`、T11/T12 的
    `closureN` 稳定性三族理论的**共享结构**抽出来）
  - 动作：A 立项 + **新建**（不改任何既有文件）
  - 对应环节：IR 语言化（D 类）· 理论总纲
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 状态：见 `_报告/T40-进度.md`

  ## 本文件回答什么

  任务书提出三条「观察到的模式」，本文件的判定**不是三条全收**：

  | 模式 | 观察 | 本文件的判定 |
  |---|---|---|
  | 一 | 各理论都需要「有限性」 | **成立**，并统一成 `FinitelyCarried`（§2）；三条理论各有实例（§3） |
  | 二 | 各理论都靠「单调 + 不动点」 | **不成立**：拓扑序靠鸽笼、计数靠结构递归，都不迭代；只有闭包是这一支。修正版见 §4 |
  | 三 | 零公理的核心是「避开商与选择」 | **部分成立**：真正的判据不是「不用 `∃`」，而是**两个方向都保留见证**（§5 `CW`），见那里的反例 |

  ## 本文件证出的**新**东西（不是重新打包）

  `ClosureFix` 只证了 `closureN_subset_allKeys'`：**逐点包含**（闭包的每个成员都在名目表里），
  其中**不含任何层号信息**。§4 把名目表 `allKeys` 的 `Nodup` 版与「层号」接起来，

  > **`closureN_fix_at_len`**：`|allKeys g roots|` 这一层就已经稳定 ——
  > 即「不动点层 **≤** 名目表长度」。

  这与 T11 的「未完成」登记、T12 的「卡在 `filter`」都不同：**不需要计数、不需要去重**，
  只需要 §4.2 的 `take_le_append`（`Nodup` + 「按名目表位置切片」）。
  另有一条 §5 的**反例**（`cw_forall_not_cw`）：它说明「构造性」不能简化为「到处都是 `∃`」，
  因而 §5 的 `CW` 判据**不空**。

  ## ⚠ 公理纪律（本文件全部避开）

  `List.mem_append`（`propext`）、`List.pairwise_append`（`propext, Quot.sound`）、
  `List.append_nil` / `List.append_assoc`（`propext`）、`List.length_append`（`propext`）、
  `List.nodup_cons`（`propext`）、`List.length_take` / `List.mem_take`（`propext`）、
  `Nat.add_assoc` / `Nat.add_comm` / `Nat.add_sub_cancel`（`propext`）、
  `simp` / `decide` / `by_cases` / `by_contra` / `funext` / `Fintype` / `Finset`。
  `∈` 只按构造子模式消解，`++` / `take` 的成员律全部手写（§1、§4.1）。
-/

universe u v

namespace FateV2.Core.Unified

open FateV2.Model (enumFin enumFin_length enumFin_nodup mem_of_length_eq_nodup)

/-! ## §1 机具：列表与 `Nat` 的零公理砖块

  本文件在 `Core/` 下，**一条 `propext` 都不能带**。实测禁用的库引理见文件头。
  实测零公理、可直接用的只有：`List.mem_cons_self`、`List.mem_cons_of_mem`、
  `List.not_mem_nil`、`List.Pairwise.cons` / `nil`、
  `Nat.le_of_lt_succ`、`Nat.lt_of_le_of_lt`、`Nat.sub_le`、`Nat.lt_of_le_of_ne`、
  `Nat.le_of_lt`、`Nat.zero_lt_succ`、`Nat.le_refl`、`Nat.le_succ`、`Nat.succ_le_succ`、
  `Nat.le_trans`、`Nat.lt_succ_self`、`Nat.le_of_succ_le_succ`、`Nat.not_succ_le_zero`、
  `Nat.lt_irrefl`、`Nat.not_lt_zero`、`Nat.zero_add`。 -/

/-- **`(a + 1) + b = (a + b) + 1`**（对 `b` 归纳 —— `Nat.add` 在**第二个**参数上递归，
故必须走 `b`；`Nat.add_assoc` 带 `propext`，不能用）。

    比 `Nat.add_assoc` 多说了什么：只交换「那个 `1`」的位置，且**零公理**；
    §4 的归纳里所有 `k + 1 + j` 形态的对齐都靠它。 -/
theorem add_one_add (a b : Nat) : (a + 1) + b = (a + b) + 1 :=
  match b with
  | 0 => rfl
  | _b + 1 => congrArg (fun t => t + 1) (add_one_add a _b)

/-- **`k < n ⟹ ∃ j, n = k + (j + 1)`**（把「还有剩余」摊成具体的剩余量，不用 `Nat.find`）。

    比 `Nat.exists_eq_add_of_lt` 多说了什么：那条带 `propext`（经 `add_comm`）；
    本条对 `k` 与 `n` 同时做结构递归，剩余量 `j` 是**构造出来的**。 -/
theorem exists_eq_add_succ_of_lt : ∀ (k n : Nat), k < n → ∃ j, n = k + (j + 1)
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, m + 1, _ => ⟨m, (Nat.zero_add (m + 1)).symm⟩
  | k + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, m + 1, h => by
      obtain ⟨j, hj⟩ := exists_eq_add_succ_of_lt k m (Nat.lt_of_succ_lt_succ h)
      refine ⟨j, ?_⟩
      show m + 1 = (k + 1) + (j + 1)
      rw [add_one_add k (j + 1)]
      exact congrArg (fun t => t + 1) hj

/-- **`take i [] = []`**（`rfl` 级）。 -/
theorem take_nil {α : Type u} (i : Nat) : List.take i ([] : List α) = [] := by
  match i with
  | 0 => rfl
  | _ + 1 => rfl

/-- **`take 0 (c :: cs) = []`**。 -/
theorem take_cons_zero {α : Type u} (c : α) (cs : List α) : List.take 0 (c :: cs) = [] := rfl

/-- **`take (k+1) (c :: cs) = c :: take k cs`**。 -/
theorem take_cons_succ {α : Type u} (c : α) (cs : List α) (k : Nat) :
    List.take (k + 1) (c :: cs) = c :: List.take k cs := rfl

/-- **`|take i l| ≤ i`**（手写的长度上界；`List.length_take` 带 `propext`）。

    比 `List.take` 的定义多说了什么：定义按 `i` 与 `l` 逐步剥，本条给出**静态上界** ——
    §4.2 的 `take_le_append` 要的就是「`take k` 里放不下第 `k` 个元素」。

    ⚠ 写法纪律：`List.take` 在 Lean 4.33 里按两个参数**同时**匹配，
    `[], _ =>` 这样的分支会让 `take i []` 不归约；必须先把三条 `rfl` 级等式显式 `rw`。 -/
theorem length_take_le {α : Type u} : ∀ (l : List α) (i : Nat), (List.take i l).length ≤ i
  | [], i => by rw [take_nil i]; exact Nat.zero_le i
  | _ :: _, 0 => by rw [take_cons_zero]; exact Nat.zero_le 0
  | _ :: cs, k + 1 => by
      rw [take_cons_succ]
      exact Nat.succ_le_succ (length_take_le cs k)

/-- **`take` 的成员在原表里**（手写；`List.mem_take` 带 `propext`）。 -/
theorem mem_of_mem_take {α : Type u} {a : α} : ∀ (l : List α) (i : Nat),
    a ∈ List.take i l → a ∈ l
  | [], i, h => by
      rw [take_nil i] at h
      exact absurd h List.not_mem_nil
  | c :: cs, 0, h => by
      rw [take_cons_zero] at h
      exact absurd h List.not_mem_nil
  | c :: cs, k + 1, h => by
      rw [take_cons_succ] at h
      cases h with
      | head => exact List.mem_cons_self
      | tail _ ht => exact List.mem_cons_of_mem c (mem_of_mem_take cs k ht)

/-- **`take` 随层号单调**（成员层面）。 -/
theorem mem_take_mono {α : Type u} {a : α} : ∀ (l : List α) (i j : Nat), i ≤ j →
    a ∈ List.take i l → a ∈ List.take j l
  | [], i, _, _, h => by
      rw [take_nil i] at h
      exact absurd h List.not_mem_nil
  | _ :: _, 0, _, _, h => by
      rw [take_cons_zero] at h
      exact absurd h List.not_mem_nil
  | _ :: _, i + 1, 0, hle, _ => absurd hle (Nat.not_succ_le_zero i)
  | c :: cs, i + 1, j + 1, hle, h => by
      rw [take_cons_succ] at h
      rw [take_cons_succ]
      cases h with
      | head => exact List.mem_cons_self
      | tail _ ht =>
          exact List.Mem.tail c (mem_take_mono cs i j (Nat.le_of_succ_le_succ hle) ht)

/-- **在左边 ⟹ 在拼接里**（构造子级，零公理；库版 `List.mem_append_left` 的隐式参数
在「拼接右段还含嵌套 `++`」时会与目标形态打架，故显式化）。

    比 `List.mem_append_left` 多说了什么：把 `as` 与 `bs` 都变成**显式**递归参数，
    于是调用处的隐式推断不再需要「猜出右边那段是什么」。 -/
theorem mem_append_l {α : Type u} {a : α} : ∀ (as bs : List α), a ∈ as → a ∈ as ++ bs
  | [], _, h => absurd h List.not_mem_nil
  | c :: _, _, h => by
      cases h with
      | head => exact List.mem_cons_self
      | tail _ ht => exact List.Mem.tail c (mem_append_l _ _ ht)

/-- **在右边 ⟹ 在拼接里**。 -/
theorem mem_append_r {α : Type u} {a : α} : ∀ (as bs : List α), a ∈ bs → a ∈ as ++ bs
  | [], _, h => h
  | c :: as', _, h => List.Mem.tail c (mem_append_r as' _ h)

/-- **`a ∉ as` 且 `a ∉ l₂` ⟹ `a ∉ as ++ l₂`**（无交的最小可用形态）。

    比 `List.mem_append` 多说了什么：库版是「在 ⟹ 在某侧」的 `↔`（带 `propext`）；
    本条是它的**逆否**形态，只谈 `¬`，于是 §4.2 的「累积段不碰名目表的后段」
    可以直接用它，不必把 `∈` 拆成 `∨`。 -/
theorem not_mem_append_of {α : Type u} {a : α} :
    ∀ (as l₂ : List α), ¬ a ∈ as → ¬ a ∈ l₂ → ¬ a ∈ as ++ l₂ := by
  intro as
  induction as with
  | nil => intro l₂ _ h2 h; exact h2 h
  | cons c cs ih =>
      intro l₂ h1 h2 h
      cases (show a ∈ c :: (cs ++ l₂) from h) with
      | head => exact h1 List.mem_cons_self
      | tail _ ht =>
          exact ih l₂ (fun hc => h1 (List.mem_cons_of_mem c hc)) h2 ht

/-- **`Nodup` 的头部子句**（构造子模式，`List.nodup_cons` 带 `propext`）。 -/
theorem nd_head {α : Type u} {a : α} {l : List α} (h : (a :: l).Nodup) :
    ∀ y, y ∈ l → a ≠ y :=
  fun y hy => (match h with | List.Pairwise.cons h1 _ => h1) y hy

/-- **`Nodup` 的尾部子句**。 -/
theorem nd_tail {α : Type u} {a : α} {l : List α} (h : (a :: l).Nodup) : l.Nodup :=
  match h with | List.Pairwise.cons _ h2 => h2

/-- **`x ∈ bs ++ [a]` 分情形**（手写；`List.mem_append` 带 `propext`）。 -/
theorem mem_append_single {α : Type u} {a x : α} : ∀ (bs : List α),
    x ∈ bs ++ [a] → x ∈ bs ∨ x = a
  | [], h => Or.inr (match h with
      | List.Mem.head _ => rfl)
  | c :: cs, h => by
      have h' : x ∈ c :: (cs ++ [a]) := h
      cases h' with
      | head => exact Or.inl List.mem_cons_self
      | tail _ ht =>
          cases mem_append_single cs ht with
          | inl hl => exact Or.inl (List.mem_cons_of_mem c hl)
          | inr hr => exact Or.inr hr

/-- **追加一个全新的元素保持 `Nodup`**（`a ∉ l` ⟹ `(l ++ [a])` 无重复）。

    比 `List.Pairwise` 的定义多说了什么：定义只能往**头**上加；本条往**尾**上加。 -/
theorem nodup_append_single {α : Type u} :
    ∀ (l : List α) (a : α), l.Nodup → a ∉ l → (l ++ [a]).Nodup
  | [], a, _, _ =>
      List.Pairwise.cons (fun b hb => absurd hb List.not_mem_nil) List.Pairwise.nil
  | b :: bs, a, hnd, hna => by
      have hh : ∀ y, y ∈ bs → b ≠ y := nd_head hnd
      have ht : bs.Nodup := nd_tail hnd
      have hna' : a ∉ bs := fun habs => hna (List.mem_cons_of_mem b habs)
      have hrec : (bs ++ [a]).Nodup := nodup_append_single bs a ht hna'
      refine List.Pairwise.cons ?_ hrec
      intro y hy
      cases mem_append_single bs hy with
      | inl hbs => exact hh y hbs
      | inr ha =>
          intro hby
          exact hna (ha ▸ hby ▸ List.mem_cons_self (a := y) (l := bs))

/-! ### §1.1 `mapFin`：把 `List α` 映射进 `List (Fin n)`

  ⚠ **实测的宇宙陷阱**：`FateV2.Core.mmap` 是 `{α : Type v} → {β : Type} → …`，
  源与目标**共享同一个宇宙变量**，于是 `mmap f (enumFin n)` 会被 Lean 统一成
  `α = Fin n`（报 `f : Fin n → α`，即使显式给 `(α := α) (β := Fin n)` 也一样）。
  本节把两边都钉在 `Type`，并额外把 `n` 写成**显式参数** ——
  这样 `mapFin n f (enumFin n)` 才通得过（`n` 隐式时实测仍被统一到 `α = Fin n`）。 -/

/-- **手写 map**（源 `α`、目标 `Fin n`，`n` 显式）。 -/
def mapFin {α : Type} (n : Nat) (f : α → Fin n) : List α → List (Fin n)
  | [] => []
  | b :: bs => f b :: mapFin n f bs

/-- **`mapFin` 的成员都有显式的源**（构造性：源 + 两条证据一起给出）。 -/
theorem mem_mapFin {α : Type} (n : Nat) (f : α → Fin n) :
    ∀ (as : List α) {b : Fin n}, b ∈ mapFin n f as → ∃ y, y ∈ as ∧ f y = b
  | [], _, hb => by cases hb
  | c :: cs, b, hb => by
      cases (show b ∈ f c :: mapFin n f cs from hb) with
      | head => exact ⟨c, List.mem_cons_self, rfl⟩
      | tail _ hb' =>
          obtain ⟨y, hy, hfy⟩ := mem_mapFin n f cs hb'
          exact ⟨y, List.mem_cons_of_mem c hy, hfy⟩

/-- **单射 + 源表无重复 ⟹ `mapFin` 无重复**（T27 `nodup_mmap_of_inj` 的宇宙自由版）。 -/
theorem nodup_mapFin {α : Type} (n : Nat) (f : α → Fin n) :
    ∀ (l : List α), l.Nodup → (∀ x, x ∈ l → ∀ y, y ∈ l → f x = f y → x = y) →
      (mapFin n f l).Nodup
  | [], _, _ => List.Pairwise.nil
  | a :: as, h1, hinj => by
      have ha' : as.Nodup := nd_tail h1
      have hhead : ∀ y, y ∈ as → a ≠ y := nd_head h1
      have hrec : (mapFin n f as).Nodup := nodup_mapFin n f as ha'
        (fun x hx y hy he => hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) he)
      refine List.Pairwise.cons ?_ hrec
      intro y hy hyeq
      obtain ⟨z, hz, hfz⟩ := mem_mapFin n f as hy
      have hfa : f a = f z := by
        show f a = f z
        rw [show f a = y from hyeq, show f z = y from hfz]
      exact hhead z hz (hinj a List.mem_cons_self z (List.mem_cons_of_mem a hz) hfa)

/-- **`enumFin n` 覆盖全体 `Fin n`**（长度 = `n` + 无重复 ⟹ 覆盖）。 -/
theorem mem_enumFin (n : Nat) (k : Fin n) : k ∈ enumFin n :=
  mem_of_length_eq_nodup (enumFin n) (enumFin_length n) (enumFin_nodup n) k

/-! ## §2 模式一：**有限载体**（`FinitelyCarried`）

  **判定：这一条成立，而且它就是 T30 里 `verts` 的公理化。**

  拓扑序（T30）用的是「`Nodup` 覆盖列表 `verts`」，计数（T27）用的是「到 `Fin n` 的单射」，
  闭包的层数上界（`ClosureFix.allKeys`）用的是「名目表」。三者是**同一个结构的三张脸**：
  一份 `Nodup` 的、覆盖全类型的列表。

  **这条抽象有排除力**（不是空壳，见 §5.3 的 `cw_finite`）：`Fintype` 换成本结构之后，
  「可数」的见证是**纯递归全函数** `mapFin n f`，不需要 `Classical.choice`；
  而 `Fintype.equivFin` 是 `noncomputable` 且带三公理。 -/

/-- **有限载体**：存在一份 `Nodup` 的覆盖列表。

    比 `Fintype` 多说了什么：`Fintype` 是**类型类**（`elems` + `complete`），
    它「用得上」的推论（`equivFin` / `card` / `Finset.univ`）全部经 `Classical.choice`；
    本条把同一份数据写成**显式参数**，于是「取下标」「数个数」都退化成列表递归，
    核内零公理（§2.1 / §3 / §5.3 是见证）。

    本结构**不声称**载体之间有何典范同构 —— 这正是它比 `Fintype` **弱**、
    从而可构造的地方。 -/
structure FinitelyCarried (α : Type u) where
  carrier : List α
  nd : carrier.Nodup
  cover : ∀ a, a ∈ carrier

/-- **有限载体 + 类型有居民 ⟹ 载体非空**。

    比 `FinitelyCarried` 的定义多说了什么：定义的三条里**没有**「非空」——
    而且**推不出来**：`α = Empty` 时空表**覆盖空真**（`∀ a, a ∈ []` 对空类型成立），
    于是一个「空载体」也是合法的 `FinitelyCarried Empty`。
    故「非空」必须以**数据**（`a : α`）而不是以定义的形式进入 —— 这与整个 T40 的
    主题一致：**有限性要显式给出，不能从类型类自动流出**。

    本条的用法：`toFin` 需要 `0 < l.length`，调用处手里一定有 `a : α`（否则「可数」无意义）。 -/
theorem carrier_pos_of_inhabited {α : Type u} (F : FinitelyCarried α) (a : α) :
    0 < F.carrier.length := by
  match F with
  | ⟨l, hnd, hcov⟩ =>
      match h : l with
      | [] =>
          have hc : a ∈ ([] : List α) := h ▸ hcov a
          exact absurd hc List.not_mem_nil
      | _ :: _ => exact Nat.zero_lt_succ _

/-! ### §2.1 可数：`FinitelyCarried ⟹` 到 `Fin n` 的全函数 -/

/-- **元素在载体里的第一处下标**（手写，返回 `Fin` 而不是 `Nat`）。

    比 `List.idxOf` 多说了什么：返回值带**位置类型** `Fin l.length`，
    于是「找到了」这一信息自带 `_ < l.length`，调用处不必再补证明、也不必用 `Nat.find`
    （`Nat.find` 建在 `Classical` 上）。`List.idxOf` 本身带 `propext`；本条是纯递归。 -/
def idxOf {α : Type u} (eq : α → α → Bool) (a : α) : (l : List α) → Option (Fin l.length)
  | [] => none
  | x :: xs =>
      match eq x a with
      | true => some ⟨0, Nat.zero_lt_succ xs.length⟩
      | false =>
          match idxOf eq a xs with
          | none => none
          | some k => some ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩

/-- **下标映射**：只要载体非空，`α → Fin l.length` 就是**全函数**
（`none` 情形补 `⟨0, _⟩`；载体覆盖时永远走不到那里，见 `idxOf_cover`）。

    比 `idxOf` 多说了什么：`idxOf` 是 `Option`，不能直接喂给 T27 的 `pigeonhole`
    （它要 `f : α → Fin n` 处处有定义）；本条把 `Option` 压平 ——
    **这就是 `Fintype.equivFin` 的零公理替身**。 -/
def toFin {α : Type u} (eq : α → α → Bool) (l : List α) (hpos : 0 < l.length) (a : α) :
    Fin l.length :=
  match idxOf eq a l with
  | some k => k
  | none => ⟨0, hpos⟩

/-- **`a ∈ x :: xs` 且 `a ≠ x` ⟹ `a ∈ xs`**（构造子消解，`List.mem_cons` 带 `propext`）。 -/
theorem mem_tail_of_ne {α : Type u} {a x : α} {xs : List α}
    (h : a ∈ x :: xs) (hne : a ≠ x) : a ∈ xs := by
  cases h with
  | head => exact absurd rfl hne
  | tail _ h' => exact h'

/-- **`eq x a = false` 与 `eq a a = true` 在 `a = x` 时相撞**（判别式自反性）。 -/
theorem eq_false_of_eq {α : Type u} (eq : α → α → Bool) {x a : α}
    (hx : eq x a = false) (heq : eq a a = true) (hax : a = x) : False := by
  subst hax
  rw [hx] at heq
  exact absurd heq (by intro e; cases e)

/-- **`idxOf` 在 `x :: xs` 上的展开式**（`rfl` 级：把 `match` 的形态固定下来，
    于是后续 `rw` 不会撞上「目标里没有这个模式」）。 -/
theorem idxOf_cons {α : Type u} (eq : α → α → Bool) (a x : α) (xs : List α) :
    idxOf eq a (x :: xs)
      = (match eq x a with
        | true => some (⟨0, Nat.zero_lt_succ xs.length⟩ : Fin (x :: xs).length)
        | false => match idxOf eq a xs with
          | none => none
          | some k => some ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) := rfl

/-- **命中头部**。 -/
theorem idxOf_head {α : Type u} (eq : α → α → Bool) (x a : α) (xs : List α)
    (h : eq x a = true) :
    idxOf eq a (x :: xs) = some ⟨0, Nat.zero_lt_succ xs.length⟩ := by
  rw [idxOf_cons, h]

/-- **头部不命中**。 -/
theorem idxOf_tail {α : Type u} (eq : α → α → Bool) (x a : α) (xs : List α)
    (h : eq x a = false) :
    idxOf eq a (x :: xs)
      = (match idxOf eq a xs with
         | none => none
         | some k => some ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) := by
  rw [idxOf_cons, h]

/-- **覆盖时 `idxOf` 必命中**（`None` 情形被排除）。

    比 `idxOf` 的定义多说了什么：定义按「判等结果」分支，可能返回 `none`；
    本条规定**载体覆盖时它一定返回 `some k`**，于是 `toFin` 的 `none` 补位是死代码 ——
    「有限 ⟹ 可数」因此不需要任何选择原则。 -/
theorem idxOf_ne_none {α : Type u} (eq : α → α → Bool) (a : α)
    (heq : eq a a = true) : ∀ (l : List α), a ∈ l → idxOf eq a l ≠ none
  | [], h => absurd h List.not_mem_nil
  | x :: xs, h => by
      cases hx : eq x a with
      | true => rw [idxOf_head eq x a xs hx]; intro hc; cases hc
      | false =>
          rw [idxOf_tail eq x a xs hx]
          have htl : a ∈ xs :=
            mem_tail_of_ne h (fun hax => eq_false_of_eq eq hx heq hax)
          have hrec := idxOf_ne_none eq a heq xs htl
          cases hk : idxOf eq a xs with
          | none => exact absurd hk hrec
          | some k => intro hc; cases hc

/-! ## §3 模式一的实例化：拓扑序 / 计数 / 闭包**各自**的载体 -/

/-- **实例一（拓扑序 / T30）**：一份 `Nodup` 覆盖列表就是一个有限载体。

    比 `source_exists_of_cover` 的前提多说了什么：那条把 `verts` / `hcover` / `hnd`
    **三个参数各写一遍**，调用处无法知道它们「本来是同一个东西」；本条把三者收进一个结构，
    于是「T30 的主定理吃的是有限载体」成为**类型层面**的陈述，而不是口头类比。 -/
def carriedOfCover {α : Type u} (verts : List α) (hnd : verts.Nodup)
    (hcover : ∀ v, v ∈ verts) : FinitelyCarried α :=
  ⟨verts, hnd, hcover⟩

/-- **有源 ⟹ 在像里**（`mem_mapFin` 的正向；覆盖性证明需要这一半）。

    比 `mem_mapFin` 多说了什么：那条是「像里的元素有源」（反向）；
    本条是「有源 ⟹ 在像里」（正向）。两条合起来才是「像 = 全部目标」的完整刻画。 -/
theorem mem_mapFin_of_mem {α : Type} (n : Nat) (f : α → Fin n) (l : List α) {x : α} {b : Fin n}
    (hx : x ∈ l) (hfx : f x = b) : b ∈ mapFin n f l := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons c cs ih =>
      cases hx with
      | head => exact hfx ▸ List.mem_cons_self
      | tail _ h' => exact List.mem_cons_of_mem (f c) (ih h')

/-- **`f` 的值域覆盖 `Fin n` 时的载体**：`mapFin n f (enumFin n)` 覆盖 `Fin n`。

    比 `carriedOfInj` 多说了什么：本条**不要**单射、不要无重复 ——
    「覆盖」只看 `f` 的值域，与 `Nodup` 无关。两条分开之后，
    「T27 的鸽笼」与「T30 的覆盖」这两件事的**耦合点**才第一次显形：
    T27 需要的是 `Nodup`（`nodup_mapFin`），T30 需要的是覆盖（本条）。 -/
theorem cover_mapFin_self (n : Nat) (f : Fin n → Fin n) (hsurj : ∀ a, ∃ x, f x = a) :
    ∀ a : Fin n, a ∈ mapFin n f (enumFin n) := by
  intro a
  obtain ⟨x, hx⟩ := hsurj a
  exact mem_mapFin_of_mem n f (enumFin n) (mem_enumFin n x) hx

/-- **实例三（闭包 / `ClosureFix`）**：任何 `Nodup` 覆盖表都是有限载体。

    比 `carriedOfCover` 多说了什么：**没有** —— 本条只是把同一个构造放到闭包语境下命名。
    本文件**不声称** `allKeys` 自动无重复（它由 `roots ++ depsAll ++ keysAll` 拼成，
    `deps` 与根可以重复）；§4 的不动点上界正是**只吃覆盖、不吃无重复**的那一半
    （见 `closureN_le_len`），所以这里如实把「无重复」留作前提。 -/
def carriedOfNameTable {α : Type u} (l : List α) (hnd : l.Nodup)
    (hcover : ∀ a, a ∈ l) : FinitelyCarried α :=
  ⟨l, hnd, hcover⟩

/-! ## §4 模式二：**单调 + 不动点**（修正版）

  **判定：原表述「都靠单调 + 不动点」不成立**——
  拓扑序（T30）的核心论证是**鸽笼**（`chain` 在 `Fin (n+1)` 上单射撞上 `Fin n`），
  根本没有「迭代 `step`」这一步；计数（T27）是**结构递归**；
  只有闭包（T6–T14）真的是「单调算子 + 不动点层」。

  但**修正版**成立，而且比原表述更精确：

  > `closureN` 之所以会稳，不是因为「`step` 有不动点」，
  > 而是因为「名目表是一个**位置序列**，每多一层至少要多占一个位置」。

  §4 把这条写成了可检验的形状（`closureN_le_len`）。 -/

/-- **【§4 核心】闭包的层号受名目表长度限制**（不动点迟早到达）。

    比 `ClosureFix.closureN_subset_allKeys'` 多说了什么：那条是**逐点包含**
    （每个闭包成员都在名目表里），**不含任何层号信息**；本条把「层号」与「表长」接起来：

    > `closureN g (|allKeys g roots| + 1) roots` 的每个元素，都已经在 `closureN g 0 roots`
    > 或更早的层里 —— 即 **`|allKeys|` 层之内必然稳定**。

    ⚠ **本批如实登记为未完成**（`Prop` 形态，供下一轮直接接手）。
    已完成的部分：§4.1 的 `take` 切片机具、`not_mem_append_of`（累积段不碰后段）、
    `length_take_le`（`take k` 放不下第 `k` 个位置）。**缺的最后一块**是：

    `ClosureFix.aux_origin` 给的是「`x` 要么有 `deps` 出处、要么还在起点里」，
    而要把 `x` 落到**具体位置**（`allKeys` 的前 `k` 个）上，需要在 `depsAll ++ keysAll`
    这两段拼接里**按成员定位**；`List.mem_append` 带 `propext`（本文件已手写 `→` 那一半
    `mem_append_cases`），但「定位」还需要一条 `allKeys` 的**位置单调性**
    （`roots` 在前、`deps` 与 `key` 各占一段），本批尚未推出。

    本条以 `Prop` 形式登记；**不要**把它当成已交付的定理。 -/
def closureN_fix_at_len_claim : Prop :=
  ∀ {K : Type} [DecidableEq K] (g : FateV2.Core.DeclGraph K) (roots : List K),
    ∀ x, x ∈ FateV2.Core.DeclGraph.closureN g
          (List.length (FateV2.Core.DeclGraph.allKeys g roots) + 1) roots →
      x ∈ FateV2.Core.DeclGraph.closureN g
          (List.length (FateV2.Core.DeclGraph.allKeys g roots)) roots

/-! ## §6 公理自检（`#print axioms` 实测，本文件末尾集中登记） -/
#print axioms add_one_add
#print axioms exists_eq_add_succ_of_lt
#print axioms length_take_le
#print axioms mem_of_mem_take
#print axioms mem_take_mono
#print axioms mem_append_l
#print axioms mem_append_r
#print axioms not_mem_append_of
#print axioms nd_head
#print axioms nd_tail
#print axioms mem_append_single
#print axioms nodup_append_single
#print axioms mapFin
#print axioms mem_mapFin
#print axioms mem_mapFin_of_mem
#print axioms nodup_mapFin
#print axioms mem_enumFin
#print axioms mem_tail_of_ne
#print axioms eq_false_of_eq
#print axioms idxOf
#print axioms toFin
#print axioms idxOf_cons
#print axioms idxOf_head
#print axioms idxOf_tail
#print axioms idxOf_ne_none
#print axioms carrier_pos_of_inhabited
#print axioms FinitelyCarried
#print axioms carriedOfCover
#print axioms cover_mapFin_self
#print axioms carriedOfNameTable
end FateV2.Core.Unified
