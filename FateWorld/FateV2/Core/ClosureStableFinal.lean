import FateWorld.FateV2.Core.Unified
import FateWorld.FateV2.Core.ClosureFirstPos

/-!
  # Core · 闭包稳定化（专项 T41 · 名目表位置路线）

  ## 迁移登记
  - 来源：新写（承接 `_报告/T40-进度.md` §2.4 / §五 的缺口定位）；
    目标命题取自 `ClosureMono.lean` 尾项 #1（自 `_报告/T11-进度.md` 起登记为未证）
  - 动作：A 立项 + **新建**（不改任何既有文件；`GroupD.lean` 的 import 由协调者追加）
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 状态：见文末 `#print axioms`

  ## 一、路线判定

  | 路线 | 判定 |
  |---|---|
  | A（`allKeys` 鸽笼） | **前提为假**：`allKeys = roots ++ depsAll ++ keysAll` 可重复（§5.1 反例） |
  | B（长度有界） | **前提为假**：`(closureN g n [k]).length = 1 + n` 无界（§5.2） |
  | **C（构造不动点）** | ✅ 走这条：位置 < 层号 的不变量 |

  ## 二、本批实测的写法（省下一轮试错）

  1. `rw [List.length_cons]` 必须显式给：`(d :: rest).length` 与 `rest.length + 1` 本机不定义相等。
  2. `dsimp only [f]` + `rw [h]` 展开 `match` 必须在 `f` 自己的命名空间里。
  3. `List.Mem.tail` 的第二字段名**不稳定**（`ht`/`hd`/无名）—— 一律用 `cases h with | head | tail _ ht`。
  4. `(m+1) - (k+1) = m - k` **不是** `rfl`；本文件因此不做长度减法。
  5. `match mem_cons_split h with | Or.inl hxy => …` 在模式变量类型含元变量时会失败 ——
     改用 `cases h with | head | tail` 或 `mem_of_ne_head`。
  6. `.lean` 文件**绝不能用 PowerShell 的 `Set-Content -Encoding utf8` 写**（会加 BOM，
     实测直接导致 `expected token`）；只能走 `write` / `edit` 工具。
-/

universe v

open FateV2.Core.Unified

namespace FateV2.Core

/-! ## §0 `Nat` 的零公理砖块 -/

/-- **加法结合律**（自证；`Nat.add_assoc` 带 `propext`）。

    比 `Nat.add` 的定义多说了什么：定义只看第一个参数，本条说三个数怎么括号都一样 ——
    §5 的三段位置（`roots + (deps + keys)`）全靠它。⚠ 只能对**第三**个参数归纳。 -/
theorem add_assoc' (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ k ih => exact congrArg (fun t => t + 1) ih

/-- **`1 + b = b + 1`**（对 `b` 归纳；`Nat.add_comm` 带 `propext`）。 -/
theorem one_add (b : Nat) : 1 + b = b + 1 := by
  induction b with
  | zero => rfl
  | succ k ih => exact congrArg (fun t => t + 1) ih

/-- **`(a + 1) + b = a + (b + 1)`**（只挪那个 `1`）。 -/
theorem add_one_swap (a b : Nat) : (a + 1) + b = a + (b + 1) := by
  rw [add_assoc']
  show a + (1 + b) = a + (b + 1)
  rw [one_add b]

/-! ## §A 手写 `Bool` 成员判定（`BEq` / `decide` 的库桥带 `propext`） -/

/-- **手写成员判定**（`Bool` 版 `x ∈ l`）。

    比 `List.elem` / `BEq` 多说了什么：纯结构递归，不经实例解析，故下面两条往返回溯零公理。 -/
def inb {α : Type v} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => match decide (x = y) with
    | true => true
    | false => inb x ys

/-- **真的在 ⟹ 判真**。

    比 `inb` 的定义多说了什么：定义只说「怎么算」，本条说它**不漏** ——
    §4 的 `preDeps` 在「表头声明的 `deps` 不含 `x`」那一支要靠它把否定落实。 -/
theorem mem_inb_of_mem {α : Type v} [DecidableEq α] (x : α) :
    ∀ (l : List α), x ∈ l → inb x l = true
  | [], (h : x ∈ ([] : List α)) => absurd h List.not_mem_nil
  | y :: ys, h => by
      rw [inb]
      have hl : x ∈ y :: ys := h
      match hl with
      | List.Mem.head _ => rw [decide_eq_true rfl]
      | List.Mem.tail _ htl =>
          cases hd : decide (x = y) with
          | true => rfl
          | false => exact mem_inb_of_mem x ys htl

/-- **判真 ⟹ 真的在**（另一方向）。 -/
theorem mem_of_mem_inb {α : Type v} [DecidableEq α] (x : α) :
    ∀ (l : List α), inb x l = true → x ∈ l
  | [], (h : inb x ([] : List α) = true) => absurd h (fun e => Bool.noConfusion e)
  | y :: ys, hh => by
      rw [inb] at hh
      cases h1 : decide (x = y) with
      | true => exact (of_decide_eq_true h1) ▸ List.mem_cons_self
      | false =>
          have h2 : inb x ys = true := by
            rw [h1] at hh
            exact hh
          exact List.Mem.tail y (mem_of_mem_inb x ys h2)

/-- **`decide` 判假 ⟹ 不等**。 -/
theorem ne_of_decide_false {α : Type v} [DecidableEq α] {x y : α}
    (h : decide (x = y) = false) : ¬ (x = y) := by
  intro hxy
  rw [hxy] at h
  rw [show decide (y = y) = true from decide_eq_true rfl] at h
  exact Bool.noConfusion h

end FateV2.Core

namespace FateV2.Core.DeclGraph

variable {K : Type v}

/-! ## §1 名目表是一个位置序列（手写，不用 `Nat.find`） -/

/-- **`x ∈ c :: cs` 分情形**（`x = c` 或 `x ∈ cs`）。 -/
theorem mem_cons_split {α : Type} {x y : α} {ys : List α}
    (h : x ∈ y :: ys) : (x = y) ∨ x ∈ ys := by
  cases h with
  | head => exact Or.inl rfl
  | tail => exact Or.inr (by assumption)

/-- **不在头 ⟹ 在尾**。 -/
theorem mem_of_ne_head {α : Type} {x c : α} {cs : List α}
    (h : x ∈ c :: cs) (hne : x ≠ c) : x ∈ cs := by
  match mem_cons_split h with
  | Or.inl h1 => exact absurd h1 hne
  | Or.inr h2 => exact h2

/-- **`x` 在表里 ⟹ 存在位置 `i`，前 `i+1` 个元素里已经有它**。 -/
theorem take_succ_of_mem {α : Type} {x : α} : ∀ (F : List α),
    x ∈ F → ∃ i, i < F.length ∧ x ∈ List.take (i + 1) F
  | [], (h : x ∈ ([] : List α)) => absurd h List.not_mem_nil
  | c :: cs, (h : x ∈ c :: cs) => by
      match mem_cons_split h with
      | Or.inl he => exact ⟨0, Nat.zero_lt_succ cs.length, he ▸ List.mem_cons_self⟩
      | Or.inr ht =>
          obtain ⟨i, hi, htake⟩ := take_succ_of_mem cs ht
          exact ⟨i + 1, Nat.succ_lt_succ hi, List.Mem.tail c htake⟩

/-- **`take` 的区间可以加长**：`take (i+1)` 里有的，`take (i+1+k)` 里也有。 -/
theorem mem_take_add {α : Type} {x : α} : ∀ (F : List α) (i k : Nat),
    x ∈ List.take (i + 1) F → x ∈ List.take (i + 1 + k) F
  | [], i, _, (h : x ∈ List.take (i + 1) ([] : List α)) => absurd h (by
      rw [show List.take (i + 1) ([] : List α) = [] from take_nil (i + 1)]
      exact List.not_mem_nil)
  | c :: cs, i, 0, h => h
  | c :: cs, i, k + 1, h => by
      have h2 : x ∈ List.take (i + 1 + k) (c :: cs) := mem_take_add (c :: cs) i k h
      have h3 : i + 1 + k + 1 = i + 1 + (k + 1) := rfl
      rw [← h3]
      exact mem_take_mono (c :: cs) (i + 1 + k) (i + 1 + k + 1) (Nat.le_succ _) h2

/-- **区间右端单调**：`x ∈ take (a+1) L` 且 `a ≤ b` ⟹ `x ∈ take (b+1) L`。 -/
theorem take_mono_len {α : Type} {x : α} (L : List α) (a b : Nat) (h : a ≤ b) :
    x ∈ List.take (a + 1) L → x ∈ List.take (b + 1) L := by
  intro hx
  exact mem_take_mono L (a + 1) (b + 1) (Nat.succ_le_succ h) hx

/-! ## §2 `depsOf` / `step` 的零公理消去 -/

/-- **`find?` 只有两支**（两支都带等式）。 -/
theorem find_some_or_none [DecidableEq K] (g : DeclGraph K) (r : K) :
    (∃ d, g.find? (fun (e : Decl K) => decide (e.key = r)) = some d)
      ∨ g.find? (fun (e : Decl K) => decide (e.key = r)) = none := by
  cases hf : g.find? (fun (e : Decl K) => decide (e.key = r)) with
  | none => exact Or.inr (Eq.refl _)
  | some d => exact Or.inl ⟨d, Eq.refl _⟩

/-- **`step` 的成员消去**：`a ∈ step g fr` ⟹ 存在前沿元素 `r ∈ fr`。

    比 `ClosureFix.step_mem_witness` 多说了什么：那条给 `∃`；本条做成消去规则
    （返回任意 `P`，前提里拿到 `r`、`fr` 与 `r ∈ fr`）。 -/
theorem step_mem_elim [DecidableEq K] (g : DeclGraph K) (P : Prop)
    (hp : ∀ (r : K) (fr : List K), r ∈ fr → ∀ a, a ∈ depsOf g r → P) :
    ∀ (fr : List K) (a : K), a ∈ step g fr → P
  | [], a, (h : a ∈ step g ([] : List K)) => absurd h (by
      rw [show step g ([] : List K) = [] from step_nil g]
      exact List.not_mem_nil)
  | b :: bs, a, h => by
      have h' : a ∈ depsOf g b ++ step g bs := h
      cases mem_append_cases (depsOf g b) (step g bs) h' with
      | inl hl => exact hp b (b :: bs) List.mem_cons_self a hl
      | inr hr =>
          exact step_mem_elim g P
            (fun r fr hr' a' ha' =>
              hp r (b :: fr) (List.mem_cons_of_mem b hr') a' ha') bs a hr

/-! ## §3 位置函数（手写结构递归） -/

/-- **`x` 在 `roots` 段的序号**（命中即停；`Nat.succ` 形式，便于 `take` 层号对齐）。 -/
def posRoots [DecidableEq K] (x : K) : List K → Nat
  | [] => 0
  | y :: ys =>
      match decide (x = y) with
      | true => 0
      | false => Nat.succ (posRoots x ys)

/-- **`x` 在 `roots` 段的前缀长**：命中与不命中都继续走到尾。

    比 `posRoots` 多说了什么：`posRoots` 停在命中处，本条一直走到尾 ——
    于是「位置 ≤ 前缀长」可以靠 `take` 的单调性一步拿到（§4 的 `mem_take_lenRoots`）。 -/
def lenRoots [DecidableEq K] (x : K) : List K → Nat
  | [] => 0
  | y :: ys =>
      match decide (x = y) with
      | true => ys.length + 1
      | false => Nat.succ (lenRoots x ys)

/-! ## §4 位置函数的展开律与上界 -/

/-- **`posRoots` 展开（命中）**。 -/
theorem posRoots_head [DecidableEq K] (x y : K) (ys : List K)
    (hd : decide (x = y) = true) : posRoots x (y :: ys) = 0 := by
  dsimp only [posRoots]
  rw [hd]

/-- **`posRoots` 展开（不命中）**。 -/
theorem posRoots_tail [DecidableEq K] (x y : K) (ys : List K)
    (hd : decide (x = y) = false) : posRoots x (y :: ys) = Nat.succ (posRoots x ys) := by
  dsimp only [posRoots]
  rw [hd]

/-- **`lenRoots` 展开（命中）**。 -/
theorem lenRoots_head [DecidableEq K] (x y : K) (ys : List K)
    (hd : decide (x = y) = true) : lenRoots x (y :: ys) = ys.length + 1 := by
  dsimp only [lenRoots]
  rw [hd]

/-- **`lenRoots` 展开（不命中）**。 -/
theorem lenRoots_tail [DecidableEq K] (x y : K) (ys : List K)
    (hd : decide (x = y) = false) : lenRoots x (y :: ys) = Nat.succ (lenRoots x ys) := by
  dsimp only [lenRoots]
  rw [hd]

/-- **`lenRoots` 恰好是表长**：不管命中不命中，前缀长都等于 `l.length`。 -/
theorem lenRoots_eq [DecidableEq K] (x : K) : ∀ (l : List K), lenRoots x l = l.length
  | [] => rfl
  | y :: ys => by
      rw [List.length_cons]
      cases hd : decide (x = y) with
      | true => rw [lenRoots_head x y ys hd]
      | false =>
          rw [lenRoots_tail x y ys hd]
          show Nat.succ (lenRoots x ys) = ys.length + 1
          rw [lenRoots_eq x ys]

/-- **`posRoots ≤ lenRoots`**：命中处的序号不超过前缀长。 -/
theorem posRoots_le_lenRoots [DecidableEq K] (x : K) :
    ∀ (l : List K), posRoots x l ≤ lenRoots x l
  | [] => Nat.le_refl 0
  | y :: ys => by
      cases hd : decide (x = y) with
      | true =>
          rw [posRoots_head x y ys hd, lenRoots_head x y ys hd]
          exact Nat.zero_le _
      | false =>
          rw [posRoots_tail x y ys hd, lenRoots_tail x y ys hd]
          exact Nat.succ_le_succ (posRoots_le_lenRoots x ys)

/-- **`posRoots + 1 ≤ lenRoots + 1`**（`Nat.succ` 形态，`take` 的层号对齐直接用）。 -/
theorem posRoots_succ_le_lenRoots_succ [DecidableEq K] (x : K) :
    ∀ (l : List K), Nat.succ (posRoots x l) ≤ Nat.succ (lenRoots x l)
  | [] => Nat.le_refl 1
  | y :: ys => by
      cases hd : decide (x = y) with
      | true =>
          rw [posRoots_head x y ys hd, lenRoots_head x y ys hd]
          exact Nat.succ_le_succ (Nat.zero_le _)
      | false =>
          rw [posRoots_tail x y ys hd, lenRoots_tail x y ys hd]
          exact Nat.succ_le_succ (posRoots_succ_le_lenRoots_succ x ys)

/-- **`posRoots` 覆盖 `x`**：`x ∈ l ⟹ x ∈ take (posRoots x l + 1) l`。 -/
theorem mem_take_posRoots [DecidableEq K] (x : K) :
    ∀ (l : List K), x ∈ l → x ∈ List.take (posRoots x l + 1) l
  | [], (h : x ∈ ([] : List K)) => absurd h List.not_mem_nil
  | y :: ys, h => by
      cases hd : decide (x = y) with
      | true =>
          have hxy : x = y := of_decide_eq_true hd
          rw [posRoots_head x y ys hd]
          show x ∈ List.take (0 + 1) (y :: ys)
          exact hxy ▸ List.mem_cons_self
      | false =>
          have hl : x ∈ y :: ys := h
          cases hl with
          | head =>
              rw [show decide (x = x) = true from decide_eq_true rfl] at hd
              exact absurd hd (fun e => Bool.noConfusion e)
          | tail _ ht =>
              rw [posRoots_tail x y ys hd]
              show x ∈ List.take (posRoots x ys + 1 + 1) (y :: ys)
              exact List.Mem.tail y (mem_take_posRoots x ys ht)

/-- **`posRoots < lenRoots + 1`**（上界的 `<` 形态，`take` 的区间收口用）。 -/
theorem posRoots_lt_lenRoots_succ [DecidableEq K] (x : K) :
    ∀ (l : List K), posRoots x l < lenRoots x l + 1
  | [] => Nat.le_refl 1
  | y :: ys => by
      cases hd : decide (x = y) with
      | true =>
          rw [posRoots_head x y ys hd, lenRoots_head x y ys hd]
          exact Nat.zero_lt_succ _
      | false =>
          rw [posRoots_tail x y ys hd, lenRoots_tail x y ys hd]
          exact Nat.succ_lt_succ (posRoots_lt_lenRoots_succ x ys)

/-- **前缀长再加一给出的区间覆盖 `x`**：`x ∈ take (lenRoots x l + 1) l`。

    比 `mem_take_posRoots` 多说了什么：那条的区间是 `posRoots+1`（跟元素位置走），
    本条的区间只依赖**整段前缀长**（多给一个余量）—— §5 的三段对齐正是靠
    「前缀够长」而不是「位置刚好」，这多出的一个格子让 `+1` 的对齐全部消失。 -/
theorem mem_take_lenRoots [DecidableEq K] (x : K) :
    ∀ (l : List K), x ∈ l → x ∈ List.take (lenRoots x l + 1) l
  | [], (h : x ∈ ([] : List K)) => absurd h List.not_mem_nil
  | y :: ys, h => by
      have h1 : x ∈ List.take (posRoots x (y :: ys) + 1) (y :: ys) :=
        mem_take_posRoots x (y :: ys) h
      have hle : posRoots x (y :: ys) + 1 ≤ lenRoots x (y :: ys) + 1 :=
        Nat.succ_le_succ (posRoots_le_lenRoots x (y :: ys))
      exact mem_take_mono (y :: ys) (posRoots x (y :: ys) + 1) (lenRoots x (y :: ys) + 1) hle h1

/-! ## §5 三段位置的对齐：把「有出处 / 是根」换成「落进名目表前缀」

  `posAll` 没有写成一个函数，而是**逐段**给结论：
  `roots` 段用 `lenRoots`（= `|roots|`），`depsAll` 段用 `preDeps`，`keysAll` 段用 `preKeys`。
  三者的和就是名目表里的位置，而「前缀够长」不需要任何拼接引理（每段各自 ≤ 对应段长）。 -/

/-- **`x` 在 `depsAll` 段的前缀长**：第一条「`deps` 含 `x`」的声明之前，所有声明的 `deps` 长度之和。

    比 `posRoots` 多说了什么：那条算「第几个元素」，本条算**前缀有多长**
    （`deps` 是嵌套列表，位置必须按长度累加）。§5 的对齐要的正是「前缀够长」。 -/
def preDeps [DecidableEq K] (x : K) : DeclGraph K → Nat
  | [] => 0
  | d :: rest =>
      match FateV2.Core.inb x d.deps with
      | true => 0
      | false => d.deps.length + preDeps x rest

/-- **`x` 在 `keysAll` 段的前缀长**（每跳过一个声明就加一）。 -/
def preKeys [DecidableEq K] (x : K) : DeclGraph K → Nat
  | [] => 0
  | d :: rest =>
      match decide (x = d.key) with
      | true => 0
      | false => Nat.succ (preKeys x rest)

/-- **`preDeps` 展开（命中）**。 -/
theorem preDeps_head [DecidableEq K] (x : K) (d : Decl K) (rest : DeclGraph K)
    (hb : FateV2.Core.inb x d.deps = true) : preDeps x (d :: rest) = 0 := by
  dsimp only [preDeps]
  rw [hb]

/-- **`preDeps` 展开（不命中）**。 -/
theorem preDeps_tail [DecidableEq K] (x : K) (d : Decl K) (rest : DeclGraph K)
    (hb : FateV2.Core.inb x d.deps = false) :
    preDeps x (d :: rest) = d.deps.length + preDeps x rest := by
  dsimp only [preDeps]
  rw [hb]

/-- **`preKeys` 展开（命中）**。 -/
theorem preKeys_head [DecidableEq K] (x : K) (d : Decl K) (rest : DeclGraph K)
    (hd : decide (x = d.key) = true) : preKeys x (d :: rest) = 0 := by
  dsimp only [preKeys]
  rw [hd]

/-- **`preKeys` 展开（不命中）**。 -/
theorem preKeys_tail [DecidableEq K] (x : K) (d : Decl K) (rest : DeclGraph K)
    (hd : decide (x = d.key) = false) : preKeys x (d :: rest) = Nat.succ (preKeys x rest) := by
  dsimp only [preKeys]
  rw [hd]

/-- **`preDeps` 不越界**：`preDeps x g ≤ |depsAll g|`。 -/
theorem preDeps_le [DecidableEq K] : ∀ (g : DeclGraph K) (x : K), preDeps x g ≤ (depsAll g).length
  | [], _ => Nat.le_refl 0
  | d :: rest, x => by
      have hrec := preDeps_le rest x
      cases hb : FateV2.Core.inb x d.deps with
      | true =>
          rw [preDeps_head x d rest hb]
          exact Nat.zero_le _
      | false =>
          rw [preDeps_tail x d rest hb]
          show d.deps.length + preDeps x rest ≤ (d.deps ++ depsAll rest).length
          rw [len_append']
          exact Nat.add_le_add_left hrec d.deps.length

/-- **`preKeys` 不越界**：`preKeys x g ≤ |keysAll g|`。 -/
theorem preKeys_le [DecidableEq K] : ∀ (g : DeclGraph K) (x : K), preKeys x g ≤ (keysAll g).length
  | [], _ => Nat.le_refl 0
  | d :: rest, x => by
      cases hd : decide (x = d.key) with
      | true =>
          rw [preKeys_head x d rest hd]
          exact Nat.zero_le _
      | false =>
          rw [preKeys_tail x d rest hd]
          rw [show (keysAll (d :: rest)).length = (keysAll rest).length + 1 from rfl]
          exact Nat.succ_le_succ (preKeys_le rest x)

end FateV2.Core.DeclGraph

#print axioms FateV2.Core.add_assoc'
#print axioms FateV2.Core.one_add
#print axioms FateV2.Core.add_one_swap
#print axioms FateV2.Core.inb
#print axioms FateV2.Core.mem_inb_of_mem
#print axioms FateV2.Core.mem_of_mem_inb
#print axioms FateV2.Core.ne_of_decide_false
#print axioms FateV2.Core.DeclGraph.mem_cons_split
#print axioms FateV2.Core.DeclGraph.mem_of_ne_head
#print axioms FateV2.Core.DeclGraph.take_succ_of_mem
#print axioms FateV2.Core.DeclGraph.mem_take_add
#print axioms FateV2.Core.DeclGraph.take_mono_len
#print axioms FateV2.Core.DeclGraph.find_some_or_none
#print axioms FateV2.Core.DeclGraph.step_mem_elim
#print axioms FateV2.Core.DeclGraph.posRoots
#print axioms FateV2.Core.DeclGraph.lenRoots
#print axioms FateV2.Core.DeclGraph.posRoots_head
#print axioms FateV2.Core.DeclGraph.posRoots_tail
#print axioms FateV2.Core.DeclGraph.lenRoots_head
#print axioms FateV2.Core.DeclGraph.lenRoots_tail
#print axioms FateV2.Core.DeclGraph.lenRoots_eq
#print axioms FateV2.Core.DeclGraph.posRoots_le_lenRoots
#print axioms FateV2.Core.DeclGraph.mem_take_posRoots
#print axioms FateV2.Core.DeclGraph.mem_take_lenRoots
#print axioms FateV2.Core.DeclGraph.preDeps
#print axioms FateV2.Core.DeclGraph.preKeys
#print axioms FateV2.Core.DeclGraph.preDeps_head
#print axioms FateV2.Core.DeclGraph.preDeps_tail
#print axioms FateV2.Core.DeclGraph.preKeys_head
#print axioms FateV2.Core.DeclGraph.preKeys_tail
#print axioms FateV2.Core.DeclGraph.preDeps_le
#print axioms FateV2.Core.DeclGraph.preKeys_le
