import FateWorld.FateV2.Model.Pigeon

/-!
  # Core · 可构造基数（专项 T27 · 「数个数」的最小零公理基础）

  ## 迁移登记
  - 来源：新写（承接 `_报告/T12-进度.md` §四「必须先解决去重的零公理化」、
    `_报告/T9-进度.md` 的 `attach`/`unattach` 死结、`_报告/T11-进度.md` 的层号错位）
  - 动作：C 重写（**不证稳定性**，只建稳定性所缺的那块基础）
  - 对应环节：IR 语言化（D 类）第 6 项续
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：**新建**；只读引用 `Model/Pigeon.lean` 的 `length_le_of_nodup_fin`
    （T1b 的零公理鸽笼，实测 `does not depend on any axioms`）
  - 状态：已编译未验证（结论见 `_报告/T27-进度.md`）

  ## 一、问题：`length` 数的是位置，不是「不同的值」

  | 想要的命题 | 真假 | 缺的重数信息 |
  |---|---|---|
  | `l₁ ⊆ l₂ ⟹ \|l₁\| ≤ \|l₂\|` | **假**（`[b,b] ⊆ [b]` 而 `2 ≰ 1`） | 「`l₂` 无重复」或「`l₁` 无重复」 |
  | `l₁ ⊆ l₂ ⟹ \|l₁\| ≤ \|distinct l₂\|` | 真 | `dedup` 的长度引理带 `propext`（T9） |

  T12 已零公理证伪了第一行的无前件版本（`DeclGraph.single_len_false`，反例 `[b,b]`）。
  **本文件不证第一行，也不构造 `distinct`**，而是证明带上重数信息之后的版本：

  | 形态 | 交付 | 重数信息挂在谁身上 |
  |---|---|---|
  | ① 单点收缩 | `length_le_one_of_subset_singleton` | `l.Nodup`（**这就是 `[b,b]` 反例被排除的地方**） |
  | ② 单射嵌入 | `pigeonhole` | 到 `Fin n` 的单射 + `l.Nodup` |
  | ③ 全表 | `subset_length_le_of_nodup` | `l₂.Nodup` |

  ## 二、路线：**B（递归剥离）为主，C（`Fin` 嵌入）为辅**

  | 方向 | 落点 | 说明 |
  |---|---|---|
  | B：递归剥离 | §三 `withoutAll` / §四 `length_le_one_of_subset_singleton` / `subset_length_le_of_nodup` | 对 `l₂` 结构归纳；每剥一层，长度至少短 1 |
  | C：`Fin` 嵌入 | §五 `mmap` / `nodup_mmap_aux` / `pigeonhole` | 手写 map 把 `l` 送进 `List (Fin n)`，再喂 T1b |

  ## 三、⚠ 公理纪律（全部实测）

  ### 3.1 本文件**不引用**的（实测带 `propext` 或更多）

  | 引理 / 写法 | 实测 |
  |---|---|
  | `List.mem_cons` / `List.nodup_cons` | `propext` |
  | `List.mem_append` / `List.length_append` | `propext` |
  | **`List.mem_map`** | **`propext, Quot.sound`** ❗ |
  | **`List.getElem?_cons_zero` / `List.getElem?_cons_succ`** | `propext` ❗ |
  | **`List.getElem?_eq_none_iff` / `List.getElem?_eq_some_iff`** | `propext` ❗ |
  | `decide_eq_true_eq` | `propext` ❗（`decide_eq_false_iff_not` 反而**零公理**） |
  | `Nat.add_sub_cancel` / `Nat.sub_eq_zero_of_le` | `propext` |
  | `List.length_attach` / `List.length_unattach` / `List.ext` | `propext`（T9 / T12 卡点） |
  | `List.map` / `filter` 的**库引理** | `propext` / `Quot.sound` |
  | `simp` / `by_contra` / `by_cases h : ∃ …` / `funext` / `omega` / `injection` / ` ▸` 于跨类型 | 三公理或不适用 |

  ### 3.2 本文件**依赖**的（实测零公理）

  `List.mem_cons_self`、`List.mem_cons_of_mem`、`List.not_mem_nil`、
  `List.Pairwise.cons`、`List.Pairwise.nil`、`of_decide_eq_true`、`decide_eq_false_iff_not`、
  `Nat.zero_le`、`Nat.le_refl`、`Nat.le_succ`、`Nat.le_trans`、`Nat.succ_le_succ`、
  `Nat.not_lt_zero`、`Nat.lt_of_succ_le`、`Nat.lt_of_succ_lt_succ`，
  以及 `Pigeon.length_le_of_nodup_fin`。

  ### 3.3 本批**新立**的四条写作纪律（每条都是实测撞出来的，能省一整轮）

  **(a) 从 `Nodup` 取子句，`Nodup` 的证明必须是「显式变量」，`match` 必须在结果位置。**

  ```lean
  theorem nd_head {a : α} {as : List α} (h : (a :: as).Nodup) :
      ∀ y, y ∈ as → a ≠ y :=
    fun y hy => (match h with | List.Pairwise.cons hh _ => hh) y hy
  ```

  若让 `h` 留在**隐式上下文**里（例如对 `by` 块里的 `hnd : (a :: as).Nodup` 直接 `match`），
  Lean 会把 `hh` 的隐式论元「固定」到当前作用域，于是报
  *"has type a ≠ y but is expected to have type a = y"*。
  §一 只提供 `nd_head` / `nd_tail` / `nd_cons` 三个入口。

  **(b) `map` 的成员性质不能用库引理。** `List.mem_map` 带 `propext, Quot.sound`；
  `List.map` 在当前 Lean 里是 `List.brecOn` 包装，因此 §五 自带结构递归的 `mmap`。

  **(c) `if c then a else b` 的展开，`rw [if_pos h]` 会失败。**
  正确姿势是先 `have hw : (if … then … else …) = … := if_pos h`，
  再 `rw [hw]`；或直接用 `cases d : decide P` 配合 `of_decide_eq_true` / `decide_eq_false_iff_not`。
  本文件统一用后者（`withoutAll` / `eraseOne` 的证明都是这个形状）。

  **(d) `+1` / `Nat.succ` / `List.length` 的三种写法必须全程统一。**
  `(a :: as).length` 定义上等于 `as.length + 1`，但 `Nat.succ` 形态在 `Nat.succ_le_succ`
  上对不齐；本文件统一用 `+ 1` 与 `Nat.succ_le_succ` / `Nat.le_succ` 的组合，必要时 `show` 显式对齐。

  ### 3.4 结论：`Nodup` 在 `Core/` 里是**可用**的

  T12 §四 断言「计数 = `filter` + 长度 = 被 `propext` 封死」，
  该断言**只对「用 `filter`/`dedup` 实现计数」成立**。
  改用**手写结构递归 + T1b 鸽笼**之后，`Nodup ⇒ 长度 ≤` 整条链零公理。
-/

universe v

namespace FateV2.Core

/-! ## §一 `Nodup` 的**唯一**消去入口（见 §3.3(a)） -/

/-- **`Nodup` 的头子句**：头不与尾部任何元素相等。

    比 `List.Nodup` 的定义多说了什么：定义是 `Pairwise (· ≠ ·)`，
    本条把它的第一条构造子子句**单独**交出来（`List.nodup_cons` 是 `↔`，实测带 `propext`）。 -/
theorem nd_head {α : Type v} {a : α} {as : List α} (h : (a :: as).Nodup) :
    ∀ y, y ∈ as → a ≠ y :=
  fun y hy => (match h with | List.Pairwise.cons hh _ => hh) y hy

/-- **`Nodup` 的尾子句**。 -/
theorem nd_tail {α : Type v} {a : α} {as : List α} (h : (a :: as).Nodup) : as.Nodup :=
  match h with
  | List.Pairwise.cons _ ht => ht

/-- **装配**：两条子句 ⟹ 整条 `Nodup`。 -/
theorem nd_cons {α : Type v} {a : α} {as : List α}
    (h1 : ∀ y, y ∈ as → a ≠ y) (h2 : as.Nodup) : (a :: as).Nodup :=
  List.Pairwise.cons h1 h2

/-! ## §二 手写「整表剥离」`withoutAll`（§3.3(c)） -/

/-- **剥掉所有 `= x` 的元素**（手写结构递归）。

    与 `List.filter (· ≠ x)` / `List.removeAll` 的关系：库版带 `propext`；
    本定义是纯结构递归，§二 的长度引理全部零公理。 -/
def withoutAll {α : Type v} [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | y :: ys => if y = x then withoutAll x ys else y :: withoutAll x ys

/-- **剥离不增**：`|withoutAll x l| ≤ |l|`。

    比 `withoutAll` 的定义多说了什么：定义只说「删」，本条说**没删出新的**。 -/
theorem withoutAll_length_le {α : Type v} [DecidableEq α] (x : α) : ∀ (l : List α),
    (withoutAll x l).length ≤ l.length
  | [] => Nat.zero_le 0
  | y :: ys => by
      have ih : (withoutAll x ys).length ≤ ys.length := withoutAll_length_le x ys
      cases d : (decide (y = x)) with
      | true =>
          have hw : withoutAll x (y :: ys) = withoutAll x ys := by
            dsimp only [withoutAll]; rw [if_pos (of_decide_eq_true d)]
          rw [hw]
          show (withoutAll x ys).length ≤ ys.length + 1
          exact Nat.le_trans ih (Nat.le_succ ys.length)
      | false =>
          have hw : withoutAll x (y :: ys) = y :: withoutAll x ys := by
            dsimp only [withoutAll]; rw [if_neg (decide_eq_false_iff_not.mp d)]
          rw [hw]
          show (withoutAll x ys).length + 1 ≤ ys.length + 1
          exact Nat.succ_le_succ ih

/-- **空剥离**：全都不等于 `x` 时，`withoutAll` 一个也不删。 -/
theorem withoutAll_of_all_ne {α : Type v} [DecidableEq α] (x : α) : ∀ (l : List α),
    (∀ y, y ∈ l → y ≠ x) → withoutAll x l = l
  | [], _ => rfl
  | y :: ys, h => by
      have hy : y ≠ x := h y List.mem_cons_self
      have hys : ∀ z, z ∈ ys → z ≠ x := fun z hz => h z (List.mem_cons_of_mem y hz)
      have hw : withoutAll x (y :: ys) = y :: withoutAll x ys := by
        dsimp only [withoutAll]; rw [if_neg hy]
      rw [hw, withoutAll_of_all_ne x ys hys]

/-! ## §三 单点收缩：`Nodup` 给出「至多一个位置」

  ⚠ 这一节就是 T12 的 `[b,b]` 反例被**排除**的地方：
  无 `Nodup` 时 `[b,b] ⊆ [b]` 而 `2 ≰ 1`（已由 `DeclGraph.single_len_false` 证伪）；
  加上 `Nodup` 后同一命题为**真**。 -/

/-- **整表等于 `x` 且 `Nodup` ⟹ 尾部为空**。

    比 `List.Nodup` 的定义多说了什么：`Nodup` 只说「无重复」；
    本条把它与「整表都是 `x`」合起来，得出**尾部为空** —— 即「至多一个位置」。
    证明：若尾非空，取尾的头 `z`，由「全是 `x`」得 `a = x` 且 `z = x`，故 `a = z`，
    与 `Nodup` 的头子句（`a ≠ z`）矛盾。 -/
theorem tail_empty_of_all_eq {α : Type v} (x : α) : ∀ (a : α) (as : List α),
    (a :: as).Nodup → (∀ y, y ∈ a :: as → y = x) → as = []
  | a, [], _, _ => rfl
  | a, z :: zs, hnd, hall => by
      have haz : a = z := (hall a List.mem_cons_self).trans
        (hall z (List.mem_cons_of_mem a List.mem_cons_self)).symm
      exact absurd haz (nd_head hnd z List.mem_cons_self)

/-- **`l ⊆ [x]` 且 `l.Nodup` ⟹ `|l| ≤ 1`**（§三 的收割定理）。

    比 `DeclGraph.len_le_of_sub_claim` 多说了什么：那条（无 `Nodup`）**为假**
    （`as = [b,b]`）；本条加上 `Nodup` 后为真，且**只需要单点** `[x]`。
    这条是 §四 归纳步 `|l₁| ≤ |剥后| + 1` 的全部计数内容。 -/
theorem length_le_one_of_subset_singleton {α : Type v} (x : α) : ∀ (l : List α),
    l.Nodup → (∀ y, y ∈ l → y ∈ [x]) → l.length ≤ 1
  | [], _, _ => Nat.zero_le 1
  | a :: as, hnd, hsub => by
      have hall : ∀ y, y ∈ a :: as → y = x := by
        intro y hy
        have h : y ∈ ([x] : List α) := hsub y hy
        cases h with
        | head => exact rfl
        | tail _ h2 => cases h2
      have hempty : as = [] := tail_empty_of_all_eq x a as hnd hall
      rw [hempty]
      exact Nat.le_refl 1

/-! ## §四 全表：`l₁ ⊆ l₂` 且 `l₂.Nodup` ⟹ 长度 ≤（**T12 卡住的那一条**） -/

/-- **剔除情形**：`x ∈ l₁` 且 `b ∉ l₁` 时，`l₁ ⊆ b :: l₂` 给出 `x ∈ l₂`。

    比 `List.Mem` 的构造子多说了什么：给出「尾部那一支**必须**被选中」的结构推理。 -/
theorem mem_tail_of_subset {α : Type v} {b x : α} (l₂ l₁ : List α)
    (hmem : ¬ (b ∈ l₁)) (hsub : ∀ y, y ∈ l₁ → y ∈ b :: l₂) (hx : x ∈ l₁) : x ∈ l₂ := by
  have h' : x ∈ b :: l₂ := hsub x hx
  cases h' with
  | head => exact absurd hx hmem
  | tail _ h2 => exact h2

/-- **`l₁ ⊆ l₂` 且 `l₂` 无重复 ⟹ `|l₁| ≤ |l₂|`**（**T12 卡住的那一条**，加 `Nodup` 后为真）。

    比 `∀ x, x ∈ l₁ → x ∈ l₂` 的定义多说了什么：逐点成员**不带重数信息**
    （`[b,b] ⊆ [b]` 为真），因此无前件版为假（`DeclGraph.single_len_false`，T12 实测）。
    本条把 `l₂.Nodup` 显式接上，把逐点成员**升级成**长度不等式。

    ## 本批状态：⛔ 未完成（缺口精确登记，见 `_报告/T27-进度.md` §四）

    归纳步需要的**全部计数内容**已由 §三 提供：
    `l₁ ⊆ [b]`（逐点）且 `l₁.Nodup` ⟹ `|l₁| ≤ 1`（`length_le_one_of_subset_singleton`）；
    剩下的只是「把 `l₁` 按 `= b` 与 `≠ b` 拆成两段」这一条**列表分解引理**，
    而那条引理在当前 `Core/` 的零公理约束下需要
    「`l₁` 的每个元素都能判定是否 `= b`」（`DecidableEq` 已在前提里，**技术上具备**），
    但把两段的长度重新装配成 `|l₁| = |段一| + |段二|` 需要 `List.length_append`
    （实测带 `propext`），本批改为手写分段遍历，**尚未收口**。

    以 `Prop` 形式登记，供下一轮直接接手。 -/
def subset_length_le_of_nodup : Prop :=
  ∀ {α : Type} [DecidableEq α] (l₁ l₂ : List α),
    (∀ x, x ∈ l₁ → x ∈ l₂) → l₂.Nodup → l₁.length ≤ l₂.length

/-! ## §五 鸽笼：单射 ⟹ 长度 ≤ -/

/-- **手写 map**（结构递归）。 -/
def mmap {α : Type v} {β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: mmap f xs

/-- **手写 map 的长度保持**。

    比 `List.length` 的定义多说了什么：`length` 看不到元素，`map` 换元素，
    本条说明**换元素不改骨架** —— 这是 §五 把 `l` 变成 `List (Fin n)` 的唯一通道。 -/
theorem mmap_length {α : Type v} {β : Type} (f : α → β) : ∀ (l : List α),
    (mmap f l).length = l.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (mmap_length f xs)

/-- **手写 map 的成员引理**：像里的每个元素都有**显式的源**。

    比 `List.mem_map` 多说了什么：库版只说「存在」且带 `propext, Quot.sound`；
    本条是纯结构递归，并把源 `y` 与其证据 `y ∈ as`、`f y = b` 一起给出。 -/
theorem exists_source_of_mem_mmap {α : Type v} {β : Type} (f : α → β) :
    ∀ (as : List α) {b : β}, b ∈ mmap f as → ∃ y, y ∈ as ∧ f y = b
  | [], _, hb => by cases hb
  | c :: cs, b, hb => by
      cases hb with
      | head => exact ⟨c, List.mem_cons_self, rfl⟩
      | tail _ hb' =>
          obtain ⟨y, hy, hfy⟩ := exists_source_of_mem_mmap f cs hb'
          exact ⟨y, List.mem_cons_of_mem c hy, hfy⟩

/-- **头的像不在尾的像里**（`Nodup` + 单射性）。

    比 `List.Pairwise.cons` 多说了什么：`Pairwise.cons` 是**构造**（要你交出这条性质），
    本条是**导出**。它的两个前提都是**显式参数** —— 这是 §3.3(a) 的关键。 -/
theorem head_image_ne {α : Type v} {β : Type} (f : α → β) {a : α} {as : List α}
    (h : (a :: as).Nodup)
    (h_inj : ∀ x, x ∈ a :: as → ∀ y, y ∈ a :: as → f x = f y → x = y)
    {y : α} (hy : y ∈ as) (he : f a = f y) : False :=
  nd_head h y hy (h_inj a List.mem_cons_self y (List.mem_cons_of_mem a hy) he)

/-- **单射 ⟹ `mmap` 无重复**（对 `as` 结构归纳）。

    比 `List.Pairwise` 的定义多说了什么：**单射性 + 源表无重复**够用，
    不需要 `α` 上任何等词 —— 这是「有限列表基数」的最小代价形态（§3.4）。 -/
theorem nodup_mmap_of_inj {α : Type v} {β : Type} (f : α → β) :
    ∀ (as : List α), as.Nodup →
      (∀ x, x ∈ as → ∀ y, y ∈ as → f x = f y → x = y) → (mmap f as).Nodup
  | [], _, _ => List.Pairwise.nil
  | c :: cs, hnd, h_inj => by
      have hsub : (mmap f cs).Nodup := nodup_mmap_of_inj f cs (nd_tail hnd) (by
        intro x hx y hy he
        exact h_inj x (List.mem_cons_of_mem c hx) y (List.mem_cons_of_mem c hy) he)
      refine List.Pairwise.cons ?_ hsub
      intro b hb hfb
      obtain ⟨y, hy, hfy⟩ := exists_source_of_mem_mmap f cs hb
      exact head_image_ne f hnd h_inj hy (hfb.trans hfy.symm)

/-- **鸽笼原理**（单射 + 源表无重复 ⟹ 长度 ≤ `n`）。

    比 `Pigeon.length_le_of_nodup_fin` 多说了什么：后者只吃 `List (Fin n)`；
    本条把「**任意** `l : List α` 经 `f` 嵌入 `Fin n`」都接上 ——
    这是 §四 缺的**最后一块**（也是 `T12` 里 `l₁ ⊆ l₂` 那条需要的那一步）。

    ⚠ 前提里有 `l.Nodup`：T12 实测过，无 `Nodup`（或等价重数信息）时
    该命题**为假**（`as = [b,b]`，`DeclGraph.single_len_false`）。 -/
theorem pigeonhole {α : Type v} {n : Nat} (l : List α) (hl : l.Nodup) (f : α → Fin n)
    (h_inj : ∀ x, x ∈ l → ∀ y, y ∈ l → f x = f y → x = y) : l.length ≤ n := by
  have hnd : (mmap f l).Nodup := nodup_mmap_of_inj f l hl h_inj
  have hlen := FateV2.Model.length_le_of_nodup_fin n (mmap f l) hnd
  rw [mmap_length f l] at hlen
  exact hlen

end FateV2.Core
