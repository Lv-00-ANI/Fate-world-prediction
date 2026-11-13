import Mathlib.Data.List.Nodup

/-!
  # Model · 鸽笼原理（纯结构归纳，零公理）

  ## 本文件回答什么

  专项 T1 把「无环 ⟹ 拓扑序存在」的**条件版**证了出来，并把唯一缺口精确定位为
  `SourceExists (g : Graph V) : Acyclic g → HasSource g`（无环图必有源点），
  理由是该结论需要鸽笼原理，而 Mathlib 的路线带三个公理：

  ```lean
  List.Nodup.length_le_card  -- 实测 [propext, Classical.choice, Quot.sound]
  ```

  **本文件证明「Mathlib 那条路带公理」不等于「零公理做不到」**：
  这里用**纯结构归纳**（对 `n` 归纳 + 手写列表遍历）绕开 `Fintype.card`，
  得到零公理的鸽笼原理。

  ## 主结论（`#print axioms` 实测：`does not depend on any axioms`）

  ```lean
  theorem length_le_of_nodup_fin : ∀ (n : Nat) (l : List (Fin n)), l.Nodup → l.length ≤ n
  ```

  ## 为什么不用「把元素压成某个顶点」的写法

  最直觉的做法是「把 `Fin (n+1)` 的最后一位换成某个 `a : Fin n`」，
  但那个映射**不是单射**：`a` 本身可能就是列表里的元素，压缩后两个不同元素会相撞，
  `Nodup` 就传不过去（这条死路实测确认过）。

  本文件改用**丢弃**：只把「值 = n」的元素（`Fin (n+1)` 中唯一这样的元素是 `⟨n,_⟩`）删掉，
  其余元素**保值搬运**到 `Fin n`。于是：
  * 搬运是单射 ⟹ `Nodup` 直接继承；
  * `Nodup` 保证「值 = n」者至多一个 ⟹ 长度至多少 1。

  ## 公理纪律：实测踩过的坑（每条都用 `#print axioms` 验证过）

  ### 4.1 引理本身的公理代价（按引理真实填，与「怎么用」分开记）

  | 引理 / 定义 | `#print axioms` 实测 |
  |---|---|
  | `List.mem_cons`（把 `∈` 化成 `∨`） | `propext` ❗ |
  | `List.nodup_cons`（`(a :: l).Nodup ↔ ¬ a ∈ l ∧ l.Nodup`） | `propext` ❗ |
  | `Nat.lt_one_iff` | `propext` ❗ |
  | `List.Nodup.length_le_card`（Mathlib 的鸽笼） | `propext`;`Classical.choice`;`Quot.sound` ❗ |
  | `Fin.ext` | **零公理** ✅ |
  | `List.Pairwise.cons` / `List.Pairwise.nil`（构造子） | **零公理** ✅ |
  | `List.mem_cons_self` / `List.mem_cons_of_mem` | **零公理** ✅ |

  ### 4.2 本文件采用的姿势（做法归做法）

  **关键区分**：上面的 `propext` 挂在**引理**上，不挂在**做法**上。
  「消 `∈` / 消 `Nodup`」可以完全绕开这些引理：

  * 消 `Nodup` 用**构造子模式**（`list_nodup_split`）——
    走 `match h with | List.Pairwise.cons hh ht => ...`，不引用 `List.nodup_cons`，
    因其 `propext` 只属于那条 `↔` 引理本身；
    （`.1` / `.2` 投影也不行，原因不同：`Pairwise` 不是单构造子型，投影会直接报错。）
  * 消 `∈` 用 `cases h with | head => ... | tail _ h' => ...`——
    走归纳构造子，同样不引用 `List.mem_cons`；
    （本文件里出现的 `List.mem_cons_self` / `List.mem_cons_of_mem` 是**构造子级**引理，
    实测零公理，可以放心用。）
  * 列表遍历手写（`Shrink`），不用 `map` / `filter` / `filterMap`；
  * 大小比较只用 `Nat` 的构造性引理（`Nat.le_antisymm` / `Nat.succ_le_succ` 等），
    `Nat.lt_one_iff` 用自己的 `eq_zero_of_lt_one` 替代。

  > **更正留痕**：本专项一开始曾误报「`List.mem_cons` 零公理」，
  > 协调者独立复核实测为 `[propext]`，**原说法已撤回**。
  > 撤回后结论不变：`List.mem_cons` 带 `propext`，但「用 `cases` 消 `∈`」不引用它，故零公理。
-/

namespace FateV2.Model

/-! ## 一、`Nat` 与 `Nodup` 的基本砖块 -/

/-- **`k < 1` 推出 `k = 0`**。

    比 `Nat.lt_one_iff` 多说了一句：后者是 `↔`，实测带 `propext`；
    这里用 `cases` 直接消去，保持核内零公理。 -/
theorem eq_zero_of_lt_one {k : Nat} (h : k < 1) : k = 0 := by
  cases k with
  | zero => rfl
  | succ j =>
      have h' : j < 0 := Nat.lt_of_succ_lt_succ h
      exact absurd h' (Nat.not_lt_zero j)

/-- **拆一条 `Nodup`**：`(x :: xs).Nodup` ⟹ 「`x` 与 `xs` 每个元素都不同」且 `xs.Nodup`。

    比 `List.Nodup` 的定义多说了：把 `Pairwise` 的构造子直接摊成两个**可用的假设**。
    走构造子模式而非 `List.nodup_cons`（后者是 `↔`，带 `propext`），
    也不用 `.1` / `.2`（`Pairwise` 不是单构造子型，投影不可用）。 -/
theorem list_nodup_split {α : Type} {x : α} {xs : List α}
    (h : (x :: xs).Nodup) : (∀ y, y ∈ xs → x ≠ y) ∧ xs.Nodup :=
  match h with
  | List.Pairwise.cons hh ht => ⟨hh, ht⟩

/-! ## 二、底情形：`Fin 0` 上没有非空列表 -/

/-- **`Fin 0` 上任何 `Nodup` 列表长度为 0**。

    比 `Fin 0` 的定义多说了：空类型上的「长度 ≤ 0」不是假设而是**由没有居民强制**的，
    因为 `x :: xs` 会要求 `x.isLt : 0 < 0`。 -/
theorem nodup_fin0_length_le (l : List (Fin 0)) (_h : l.Nodup) : l.length ≤ 0 := by
  cases l with
  | nil => exact Nat.zero_le 0
  | cons x _ => exact absurd x.isLt (Nat.not_lt_zero x.val)

/-! ## 三、顶点搬运与列表压缩 -/

/-- **保值搬运**：`Fin (k+1)` 中**不是最后一位**的居民，落在 `Fin k` 里（值不变）。

    比 `Fin` 的类型多说了：`x.val < k+1` 且 `x.val ≠ k` ⟹ `x.val < k`，
    于是「非最后一位」的 `Fin (k+1)` 居民同时是 `Fin k` 的居民。 -/
def shrink {k : Nat} (x : Fin (k + 1)) (h : x.val ≠ k) : Fin k :=
  ⟨x.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ x.isLt) h⟩

/-- **`shrink` 保值**。

    比 `shrink` 的定义多说了：搬运不改值，因此它是「只删不换」的压缩，
    也是后面 `Nodup` 能直接继承的全部理由。 -/
theorem shrink_val {k : Nat} (x : Fin (k + 1)) (h : x.val ≠ k) :
    (shrink x h).val = x.val := rfl

/-- **压缩**：手写遍历，把「值 = k」的元素丢掉（即 `Fin (k+1)` 唯一的最后一位 `⟨k,_⟩`），
    其余保值搬运到 `Fin k`。

    不用 `List.map` / `List.filterMap`：它们对元素递归会让 Lean 退化成 well-founded
    递归，从而带上 `propext` / `Quot.sound`（本项目已实测多次）。 -/
def Shrink {k : Nat} : List (Fin (k + 1)) → List (Fin k)
  | [] => []
  | x :: xs => if h : x.val = k then Shrink xs else shrink x h :: Shrink xs

/-- **「丢弃」分支的形状**（比 `Shrink` 的定义多说了这一情形长什么样）。 -/
theorem shrink_cons_drop {k : Nat} (x : Fin (k + 1)) (xs : List (Fin (k + 1)))
    (h : x.val = k) : Shrink (x :: xs) = Shrink xs := dif_pos h

/-- **「保留」分支的形状**（比 `Shrink` 的定义多说了这一情形长什么样）。 -/
theorem shrink_cons_keep {k : Nat} (x : Fin (k + 1)) (xs : List (Fin (k + 1)))
    (h : x.val ≠ k) : Shrink (x :: xs) = shrink x h :: Shrink xs := dif_neg h

/-- **保留分支的长度是「尾长 + 1」**。 -/
theorem shrink_len_keep {k : Nat} (x : Fin (k + 1)) (xs : List (Fin (k + 1)))
    (h : x.val ≠ k) : (Shrink (x :: xs)).length = (Shrink xs).length + 1 := by
  rw [shrink_cons_keep x xs h]; rfl

/-- **丢弃分支的长度就是尾长**。 -/
theorem shrink_len_drop {k : Nat} (x : Fin (k + 1)) (xs : List (Fin (k + 1)))
    (h : x.val = k) : (Shrink (x :: xs)).length = (Shrink xs).length := by
  rw [shrink_cons_drop x xs h]

/-- **没有「值 = k」的元素时，`Shrink` 一个也不丢**。

    比 `Shrink` 的定义多说了：压缩只在「值 = k」处动手，因此「无处可动」时长度完全保持。
    这是归纳步「丢弃」分支的关键输入。 -/
theorem shrink_len_of_avoid {k : Nat} :
    ∀ (l : List (Fin (k + 1))), (∀ y, y ∈ l → y.val ≠ k) → (Shrink l).length = l.length
  | [], _ => rfl
  | x :: xs, h => by
      have hx : x.val ≠ k := h x (List.mem_cons_self ..)
      have hxs : ∀ y, y ∈ xs → y.val ≠ k := fun y hy => h y (List.mem_cons_of_mem x hy)
      rw [shrink_len_keep x xs hx, shrink_len_of_avoid xs hxs]
      rfl

/-- **`Shrink` 的每一项都来自原列表（值相同）**。

    比 `Shrink` 的定义多说了：压缩**不凭空造值**，于是任何「压缩后两项相同」的
    情形都能回溯到原列表里的某个元素，这是 `Nodup` 传递的全部依据。 -/
theorem shrink_mem_val {k : Nat} (l : List (Fin (k + 1))) :
    ∀ (w : Fin k), w ∈ Shrink l → ∃ x, x ∈ l ∧ x.val = w.val := by
  induction l with
  | nil => intro w hw; exact absurd hw (List.not_mem_nil)
  | cons x xs ih =>
      intro w hw
      by_cases hk : x.val = k
      · rw [shrink_cons_drop x xs hk] at hw
        obtain ⟨y, hy, hval⟩ := ih w hw
        exact ⟨y, List.mem_cons_of_mem x hy, hval⟩
      · rw [shrink_cons_keep x xs hk] at hw
        cases hw with
        | head => exact ⟨x, List.mem_cons_self .., shrink_val x hk⟩
        | tail _ hw' =>
            obtain ⟨y, hy, hval⟩ := ih w hw'
            exact ⟨y, List.mem_cons_of_mem x hy, hval⟩

/-! ## 四、压缩保持 `Nodup`，且长度至多少 1 -/

/-- **`Shrink` 保持 `Nodup`**。

    比 `Shrink` 的定义多说了：删元素 + 保值搬运**不会制造重复**。
    证明要点：头的搬运值若落在尾的搬运结果里，就回溯到原列表里的某个 `z ∈ xs`，
    由「值相同」+ `Fin.ext` 得 `x = z`，与 `Nodup` 给出的 `x ≠ z` 矛盾。 -/
theorem nodup_shrink {k : Nat} : ∀ (l : List (Fin (k + 1))), l.Nodup → (Shrink l).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
      obtain ⟨hx, hxs⟩ := list_nodup_split h
      have hrec : (Shrink xs).Nodup := nodup_shrink xs hxs
      by_cases hk : x.val = k
      · rw [shrink_cons_drop x xs hk]
        exact hrec
      · rw [shrink_cons_keep x xs hk]
        refine List.Pairwise.cons ?_ hrec
        intro w hw heq
        obtain ⟨z, hz, hzval⟩ := shrink_mem_val xs w hw
        have hxval : (shrink x hk).val = x.val := shrink_val x hk
        have hxv : w.val = x.val := by rw [← heq]; exact hxval
        have hxz : x = z := Fin.ext (hxv.symm.trans hzval.symm)
        exact absurd hxz (hx z hz)

/-- **`Nodup` 下 `Shrink` 至多丢一个元素**：`l.length ≤ (Shrink l).length + 1`。

    比 `Shrink` 的定义多说了：长度损失**至多 1**。
    这正是需要 `Nodup` 的地方——「值 = k」的元素在 `Fin (k+1)` 里唯一，
    `Nodup` 保证它在列表中至多出现一次，故至多丢这一个。 -/
theorem shrink_len_nodup {k : Nat} : ∀ (l : List (Fin (k + 1))), l.Nodup →
    l.length ≤ (Shrink l).length + 1
  | [], _ => Nat.zero_le 1
  | x :: xs, h => by
      obtain ⟨hx, hxs⟩ := list_nodup_split h
      have ih' : xs.length ≤ (Shrink xs).length + 1 := shrink_len_nodup xs hxs
      by_cases hk : x.val = k
      · have havoid : ∀ y, y ∈ xs → y.val ≠ k := by
          intro y hy hyk
          exact absurd (Fin.ext (hk.trans hyk.symm)) (hx y hy)
        rw [shrink_len_drop x xs hk, shrink_len_of_avoid xs havoid]
        exact Nat.le_refl _
      · rw [shrink_len_keep x xs hk]
        exact Nat.add_le_add_right ih' 1

/-! ## 五、鸽笼原理 -/

/-- **鸽笼原理（`Fin n` 版，零公理）**：`Fin n` 上无重复列表的长度 ≤ n。

    比 `List.Nodup` 的定义多说了：**有限性给出长度上界**——
    `Fin n` 只有 `n` 个居民，无重复列表最多只能把它们用一遍。

    证明对 `n` 归纳：
    * `n = 0`：`Fin 0` 没有居民，非空列表自相矛盾；
    * `n + 1`：用 `Shrink` 把列表压进 `Fin n`，`Nodup` 与「至多丢一个」两条事实
      把 `l.length` 夹到 `(Shrink l).length + 1 ≤ n + 1`。

    这条定理取代了 Mathlib 的 `List.Nodup.length_le_card`（后者带三个公理）。 -/
theorem length_le_of_nodup_fin : ∀ (n : Nat) (l : List (Fin n)), l.Nodup → l.length ≤ n
  | 0, l, h => nodup_fin0_length_le l h
  | n + 1, l, h => by
      have hs : (Shrink l).Nodup := nodup_shrink l h
      have ih : (Shrink l).length ≤ n := length_le_of_nodup_fin n (Shrink l) hs
      have hlen : l.length ≤ (Shrink l).length + 1 := shrink_len_nodup l h
      exact Nat.le_trans hlen (Nat.succ_le_succ ih)

end FateV2.Model
