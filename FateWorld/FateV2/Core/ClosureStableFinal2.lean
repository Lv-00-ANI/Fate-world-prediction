import FateWorld.FateV2.Core.ClosureStableFinal
import FateWorld.FateV2.Core.Cardinality

/-!
  # Core · 闭包稳定化（专项 T53 · 第四次尝试）

  ## 迁移登记
  - 来源：新写（承接 T41 未完成的 §6/§7；目标命题 `closure_stabilizes`
    自 `_报告/T11-进度.md` 起登记为未证）
  - 动作：A 立项 + **新建**（不改任何既有文件，包括 `ClosureStableFinal.lean`；
    `GroupD.lean` 的 import 由协调者追加）
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 状态：见文末 `#print axioms` 与 `_报告/T53-进度.md`

  ## 一、路线（与 T41 的位置法**不同**）

  T41 想用「位置」把 `x ∈ take (n+1)` 收缩到 `x ∈ take n`，但那需要
  `preKeys`（按**内容**定位）与 `step`（按**位置**输出）单调对应 —— 二者不可比
  （`deps` 为空的声明让 `preKeys` 加一而 `step` 不加）。本批改走**计数**。

  ## 二、⚠ 公理纪律

  不引用 `List.length_append` / `List.mem_append` / `List.nodup_cons` /
  `List.length_map`（均带 `propext`）；不用 `simp` / `decide` / `by_contra` /
  `by_cases` / `funext` / `omega` / `Nat.sub` / `Fintype` / `Finset`；
  `∈` 只用构造子模式消解；`List` 遍历与 `++` 的长度律**全部手写**。
-/

universe v

namespace FateV2.Core.DeclGraph

variable {K : Type v}

/-! ## §1 `Nat` 的零公理砖块 -/

/-- **`a + 0 = a`**（`Nat.add` 在第一个参数上递归，`a + 0` 不按构造子归约）。 -/
theorem nat_add_zero' (a : Nat) : a + 0 = a := by
  show a = a + 0
  induction a with
  | zero => rfl
  | succ k ih => exact congrArg (fun t => t + 1) ih.symm

/-- **`(a + 1) + b = (a + b) + 1`**（把那个 `1` 挪到最右）。 -/
theorem add_one_add' (a b : Nat) : (a + 1) + b = (a + b) + 1 := by
  induction b with
  | zero => rfl
  | succ k ih => exact congrArg (fun t => t + 1) ih

/-- **`n + 1 ≤ n` 为假**（`+1` 写法版；归纳假设内部不会自动统一成 `succ`）。 -/
theorem not_add_one_le_self : ∀ (n : Nat), ¬ (n + 1 ≤ n)
  | 0 => Nat.not_succ_le_zero 0
  | m + 1 => fun h => not_add_one_le_self m (Nat.le_of_succ_le_succ h)

/-- **`n ≤ 0` ⟹ `n = 0`**。 -/
theorem eq_zero_of_le_zero : ∀ (n : Nat), n ≤ 0 → n = 0
  | 0, _ => rfl
  | n + 1, h => absurd h (fun hh => Nat.not_succ_le_zero n hh)

/-- **`n + 1 ≤ 0` 为假**（`+1` 与 `succ` 两种写法在内部对齐）。 -/
theorem not_add_one_le_zero (n : Nat) : ¬ (n + 1 ≤ 0) := by
  intro h
  have h0 : n + 1 = 0 := eq_zero_of_le_zero (n + 1) h
  have hpos : 0 < n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  rw [h0] at hpos
  exact Nat.lt_irrefl 0 hpos

/-- **`n + 2 ≤ 1` 为假**（与 `n+2 = (n+1)+1` 对齐后交给上一条）。 -/
theorem not_add_two_le_one {n : Nat} (h : n + 2 ≤ 1) : False := by
  have h1 : (n + 1) + 1 ≤ 0 + 1 := by
    rw [FateV2.Core.add_assoc' n 1 1]
    exact h
  exact not_add_one_le_zero n (Nat.le_of_succ_le_succ h1)

/-- **`n ≤ 1` 时把 `n` 逼成 `0/1`**（三分的核心）。

    比 `Nat.lt_two_iff`（带 `propext`）多说了什么：把「≤ 1」的来源直接枚举成
    构造性析取 —— 「多一个」的那支交给 `not_add_two_le_one` 沉底。 -/
theorem nat_le_one_cases : ∀ (m : Nat), m ≤ 1 → m = 0 ∨ m = 1
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr rfl
  | j + 2, h => False.elim (not_add_two_le_one (n := j) h)

/-! ## §2 `List` / `++` 的零公理砖块 -/

/-- **`(a :: as).length = as.length + 1`**（`rfl`；统一「加一」的写法）。 -/
theorem length_cons' {α : Type v} (a : α) (as : List α) :
    (a :: as).length = as.length + 1 := rfl

/-- **`++` 的长度可加**（自证；库版 `List.length_append` 带 `propext`）。 -/
theorem len_append'' {α : Type v} : ∀ (as bs : List α),
    (as ++ bs).length = as.length + bs.length
  | [], bs => (Nat.zero_add bs.length).symm
  | a :: as, bs => by
      show (a :: (as ++ bs)).length = (a :: as).length + bs.length
      rw [length_cons', length_cons', len_append'' as bs, add_one_add' as.length bs.length]

/-- **`|as| ≤ |as ++ bs|`**（左段不越界；自证，库版带 `propext`）。 -/
theorem len_le_append_left {α : Type v} : ∀ (as bs : List α), as.length ≤ (as ++ bs).length
  | [], bs => Nat.zero_le bs.length
  | a :: as, bs => by
      show as.length + 1 ≤ (a :: (as ++ bs)).length
      rw [length_cons']
      exact Nat.succ_le_succ (len_le_append_left as bs)

/-- **`x ∈ as ⟹ x ∈ as ++ bs`**（构造子级手写，左向入口）。 -/
theorem mem_append_l2 {α : Type v} {a : α} : ∀ (as bs : List α), a ∈ as → a ∈ as ++ bs
  | [], _, h => absurd h List.not_mem_nil
  | c :: _, _, h => by
      cases h with
      | head => exact List.mem_cons_self
      | tail _ ht => exact List.mem_cons_of_mem c (mem_append_l2 _ _ ht)

/-- **`x ∈ bs ⟹ x ∈ as ++ bs`**（构造子级手写，右向入口）。 -/
theorem mem_append_r2 {α : Type v} {a : α} : ∀ (as bs : List α), a ∈ bs → a ∈ as ++ bs
  | [], _, h => h
  | c :: as', _, h => List.mem_cons_of_mem c (mem_append_r2 as' _ h)

/-! ## §3 `cntNew`：名目表里「没见过」的元素个数 -/

/-- **名目表里「没见过」的元素个数**（手写计数，`filter` 的库版带 `propext`）。 -/
def cntNew [DecidableEq K] (B : List K) : List K → Nat
  | [] => 0
  | y :: ys =>
      match FateV2.Core.inb y B with
      | true => cntNew B ys
      | false => Nat.succ (cntNew B ys)

/-- **`cntNew` 展开（判真：这一格不占）**。 -/
theorem cntNew_true [DecidableEq K] (B : List K) (y : K) (ys : List K)
    (h : FateV2.Core.inb y B = true) : cntNew B (y :: ys) = cntNew B ys := by
  dsimp only [cntNew]
  rw [h]

/-- **`cntNew` 展开（判假：这一格要占）**。 -/
theorem cntNew_false [DecidableEq K] (B : List K) (y : K) (ys : List K)
    (h : FateV2.Core.inb y B = false) : cntNew B (y :: ys) = Nat.succ (cntNew B ys) := by
  dsimp only [cntNew]
  rw [h]

/-- **`cntNew` 不超过表长**（每个元素至多占一格）。 -/
theorem cntNew_le_len [DecidableEq K] (B : List K) :
    ∀ (l : List K), cntNew B l ≤ l.length
  | [] => Nat.le_refl 0
  | y :: ys => by
      rw [length_cons']
      cases hb : FateV2.Core.inb y B with
      | true =>
          rw [cntNew_true B y ys hb]
          exact Nat.le_trans (cntNew_le_len B ys) (Nat.le_succ ys.length)
      | false =>
          rw [cntNew_false B y ys hb]
          exact Nat.succ_le_succ (cntNew_le_len B ys)

/-- **`cntNew` 对拼接次可加**（`cntNew (a ++ b) ≤ cntNew a + cntNew b`）。 -/
theorem cntNew_append_le [DecidableEq K] (B : List K) :
    ∀ (as bs : List K), cntNew B (as ++ bs) ≤ cntNew B as + cntNew B bs
  | [], bs => Nat.le_of_eq (Nat.zero_add (cntNew B bs)).symm
  | y :: ys, bs => by
      show cntNew B (y :: (ys ++ bs)) ≤ cntNew B (y :: ys) + cntNew B bs
      cases hb : FateV2.Core.inb y B with
      | true =>
          rw [cntNew_true B y (ys ++ bs) hb, cntNew_true B y ys hb]
          exact Nat.le_trans (cntNew_append_le B ys bs) (Nat.le_refl _)
      | false =>
          rw [cntNew_false B y (ys ++ bs) hb, cntNew_false B y ys hb]
          have hs : cntNew B (ys ++ bs) ≤ cntNew B ys + cntNew B bs :=
            cntNew_append_le B ys bs
          have hgoal : cntNew B (ys ++ bs) + 1 ≤ (cntNew B ys + 1) + cntNew B bs := by
            rw [add_one_add']
            exact Nat.succ_le_succ hs
          exact hgoal

/-- **长度至多 1 的表里，未见的元素至多一个**。 -/
theorem cntNew_le_of_len_le_one [DecidableEq K] (B : List K) :
    ∀ (l : List K), l.length ≤ 1 → cntNew B l ≤ 1
  | [], _ => Nat.zero_le 1
  | y :: ys, hlen => by
      have hys : ys.length ≤ 0 := by
        rw [length_cons'] at hlen
        exact Nat.le_of_succ_le_succ hlen
      have hnil : ys = [] := by
        match ys with
        | [] => rfl
        | c :: cs =>
            have hpos : (c :: cs).length = cs.length + 1 := rfl
            have hle : cs.length + 1 ≤ cs.length := by
              rw [hpos] at hys
              exact Nat.le_trans hys (Nat.zero_le cs.length)
            exact False.elim (not_add_one_le_self cs.length hle)
      rw [hnil]
      cases hb : FateV2.Core.inb y B with
      | true =>
          rw [cntNew_true B y ([] : List K) hb]
          exact Nat.zero_le 1
      | false =>
          rw [cntNew_false B y ([] : List K) hb]
          exact Nat.succ_le_succ (Nat.zero_le 0)

/-! ## §3.5 名目表的两条成员事实 -/

/-- **根的成员 ⟹ 名目表判真**（`inb` 形式）。 -/
theorem inb_of_mem_roots [DecidableEq K] (g : DeclGraph K) (roots : List K) :
    ∀ x, x ∈ roots → FateV2.Core.inb x (allKeys g roots) = true :=
  fun x hx => FateV2.Core.mem_inb_of_mem x (allKeys g roots) (roots_sub_allKeys g roots x hx)

/-- **`deps` 的成员 ⟹ 名目表判真**（`inb` 形式）。 -/
theorem inb_of_mem_deps [DecidableEq K] (g : DeclGraph K) (roots : List K) :
    ∀ (d : Decl K), d ∈ g → ∀ x ∈ d.deps, FateV2.Core.inb x (allKeys g roots) = true :=
  fun d hd x hx => FateV2.Core.mem_inb_of_mem x (allKeys g roots)
    (mem_allKeys_of_deps g roots d hd x hx)

/-! ## §4 前沿的二分：`step` 要么空、要么由「见过且 `deps ≤ 1`」的元素驱动

  §6 的层级预算（`|acc_m| + |frontier_m| ≤ k + m + 1`）在归纳步里需要：

  * `|step g f_m| ≤ k`（否则预算会多涨）；
  * `cntNew (step g f_m) ≤ cntNew f_m`（新名字只会**变少**，预算因此闭合）。

  两者都由本节的两条定理供给。⚠ **它们的前提是**：
  `f_m` 里每个「名目表判真」的元素，其 `depsOf` 长度 **≤ 1**。
  这不是全局事实，而是**第一层**的结构：`_报告/T53-进度.md` §五 登记了它的
  精确形态与最小反例（`g = [(k1, [k1; k2])]`，`roots = [k1]`）。 -/

/-- **前沿的「可展开」判定**：有一个元素的名目表判真且其 `deps` 非空。

    比 `List` 的库谓词多说了什么：把「能不能再吐东西」落成一个**可计算**的 `Bool`，
    于是归纳步的二分不需要 `by_cases`（实测带公理）。 -/
def expandable [DecidableEq K] (g : DeclGraph K) (B : List K) : List K → Bool
  | [] => false
  | r :: rs =>
      match FateV2.Core.inb r B, (depsOf g r).length with
      | true, 0 => expandable g B rs
      | true, _ => true
      | false, _ => expandable g B rs

/-- **`expandable` 判真 ⟹ 有一个「见过」的前沿元素 `deps` 非空**。 -/
theorem expandable_witness [DecidableEq K] (g : DeclGraph K) (B : List K) :
    ∀ (fr : List K), expandable g B fr = true →
      ∃ r, r ∈ fr ∧ FateV2.Core.inb r B = true ∧ (depsOf g r).length ≠ 0
  | [], h => absurd h (fun e => Bool.noConfusion e)
  | r :: rs, h => by
      have h' : (match FateV2.Core.inb r B, (depsOf g r).length with
                 | true, 0 => expandable g B rs
                 | true, _ => true
                 | false, _ => expandable g B rs) = true := h
      cases hb : FateV2.Core.inb r B with
      | true =>
          cases hl : (depsOf g r).length with
          | zero =>
              rw [hb, hl] at h'
              obtain ⟨x, hx, hbx, hnx⟩ := expandable_witness g B rs h'
              exact ⟨x, List.mem_cons_of_mem r hx, hbx, hnx⟩
          | succ m =>
              exact ⟨r, List.mem_cons_self, hb, by rw [hl]; intro e; exact Nat.noConfusion e⟩
      | false =>
          rw [hb] at h'
          obtain ⟨x, hx, hbx, hnx⟩ := expandable_witness g B rs h'
          exact ⟨x, List.mem_cons_of_mem r hx, hbx, hnx⟩
