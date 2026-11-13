import FateWorld.FateV2.Core.Cardinality

/-!
  # Core · `Nodup` 的两个基础形态（专项 **T45**）

  ## 迁移登记
  - 来源：新写（承接 T43 `_报告/T43-进度.md` §五 留下的 `nodup_two_mem` 缺口）
  - 动作：C 重写（**否证 + 重建**）
  - 对应环节：IR 语言化（D 类）· 列表去重基础
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：**新建**；不改任何既有文件。只读引用 `FateV2/Core/Cardinality.lean`
    的 `nd_head` / `nd_tail` / `nd_cons`。
  - 状态：已验证（逐条 `#print axioms` 实测空，见文末 §5）

  ## 〇、结论先行：**派单命题为假**

  ```lean
  theorem nodup_two_mem {α : Type} {x y : α} :
      ∀ (l : List α), x ∈ l → y ∈ l → x ≠ y → ¬ l.Nodup
  ```

  **反例**：`l = [x, y]`，`x ≠ y`。
  `x ∈ l` ✅、`y ∈ l` ✅、`x ≠ y` ✅ —— 三条前提**全部成立**，
  而 `[x, y]` **确实无重复**，所以 `¬ l.Nodup` 为假。

  §1 的 `nodup_two_mem_is_false` 把它做成**零公理**的否证定理。

  > 这是本项目**第七次**派单命题写错。
  > **`nodup_two_mem` 不是「难证」，是不成立** —— T43 撞的是一堵**不存在的墙**。

  ## 一、为什么直觉会错：**「两个成员」≠「两个位置」**

  派单把两件事混成了一件：

  | 说法 | 真假 | 落到本文件的哪条 |
  |---|---|---|
  | 「列表里有两个**不同的值** ⟹ 有重复」 | **假** | §1 反例（`[x, y]`） |
  | 「一个值**占两个位置** ⟹ 有重复」 | **真** | §2.1 `nodup_two_positions` |
  | 「`Nodup` ⟹ 一个值**至多一个位置**」 | **真** | §2.1 的逆否（T43 要的就是它） |

  关键：`x ∈ l` 是**成员资格**证明，它不携带「位置」信息。
  同一个位置可以被 `List.Mem.head` 走两次，得到两条 `x ∈ l` 证明 ——
  那不是重复。要表达「占了两个位置」，**必须**把两个位置显式写出来
  （§2.1 用的是「头部 + 尾部」）。

  ## 二、T43 真正需要的那条

  T43 §五 要证「非单射 ⟹ `rawMap` 的像点表有重复」。
  把这句话拆到 `Nodup` 层面，需要的是：

  > 若 `l.Nodup`，则同一个值**不可能占两个位置**。

  §2.1 `nodup_two_positions` 就是它的最小可写形式（零公理），
  也是 T43「同一个像点不可能占两条记录」的**全部内容**。

  ## 三、⚠ 公理纪律与**实测的写法陷阱**

  本文件在 `Core/` 下，**全部零公理**。

  ### 3.1 修正 T27 §6.2 的记述：不是「隐式上下文」的问题

  T27 把「`≠` 被期望成 `=`」归因为「`Nodup` 的证明留在隐式上下文」。
  **本专项 60+ 次探针证明该归因不准确。** 真实原因有两条：

  **(a) `nd_head` 的 `y` 在返回位置上显式绑定。**

  ```lean
  #print nd_head
  -- theorem nd_head : ∀ {α} {a} {as}, (a :: as).Nodup → ∀ (y : α), y ∈ as → a ≠ y
  ```

  ⟹ `nd_head h y hy` **已经是一个完整的 `a ≠ y` 值**，
  **不能再喂第四个参数**。写成 `nd_head h y hy hne` 会报
  *"`a ≠ y` but expected `a = y`"* —— 看起来像数学错误，
  实际是**多喂了一个参数**。

  **(b) 在目标/绑定位置上，`x ≠ y` 会被具体化成 `x = y`。**

  把 `intro hxy`／`fun hxy => …`／`absurd rfl hne` 用在 `x ≠ y` 上时，
  Lean 把 `hxy` 绑定成 `x = y`（而非 `¬(x = y)`），于是
  `hxy.symm`、`Eq.trans hxy`、`absurd rfl hne` 全部报
  *"has type `x ≠ y` but expected `x = y`"*。

  **规避（本文件用的三条，全部实测零公理）**：

  1. **不要在 `≠` 上做 `intro`／`fun`**；把它做成**外部显式参数**再应用：
     ```lean
     theorem ne_false {a y : α} (h : a ≠ y) (he : a = y) : False := h he   -- ✅ 空
     ```
  2. **把 `≠` 目标换成具体等式冲突**：要证 `¬(a ∈ as)` 时，
     写成 `fun ha => (nd_head h a ha) rfl`（`rfl : a = a` 落在**具体**类型上）。✅ 空
  3. **先 `have` 出显式标注的中间命题**，再喂给下游，不要在现场统一。

  ### 3.2 实测避开的东西

  `simp` / `by_cases` / `by_contra` / `decide` / `List.nodup_cons`（带 `propext`）、
  `List.mem_cons`（`propext`）、`List.Mem` 的 `.1`/`.2` 投影（**不可用**，必须 `cases`）、
  `List.Mem.tail` 的字段名（不稳定，用 `| tail _ h'`）。
-/

universe v

namespace FateV2.Core

/-! ## §1 否证：派单命题为假 -/

/-- **反例**：`l = [x, y]` 且 `x ≠ y` 时，`x`、`y` 都在 `l` 里、二者不同，
    而 `l` **确实无重复**。

    比派单命题多说了什么：派单断言「这种 `l` 必有重复」；
    本条给出**前提全成立、结论为假**的四元组见证。

    证明：`[x, y].Nodup` 由 `nd_cons` 拼两次 ——
    头 `x` 与尾 `[y]` 不相交（`x ≠ y`），尾 `y` 与 `[]` 不相交（空真）。 -/
theorem counterexample {α : Type v} (x y : α) (hne : x ≠ y) :
    x ∈ ([x, y] : List α) ∧ y ∈ ([x, y] : List α) ∧ x ≠ y ∧ ([x, y] : List α).Nodup := by
  refine ⟨List.mem_cons_self, List.mem_cons_of_mem x List.mem_cons_self, hne, ?_⟩
  refine nd_cons ?_ (nd_cons ?_ List.Pairwise.nil)
  · intro z hz
    cases hz with
    | head => exact hne
    | tail _ h2 => exact absurd h2 List.not_mem_nil
  · intro z hz
    exact absurd hz List.not_mem_nil

/-- **★ 派单命题为假**（对整条命题的否定）。

    比 `counterexample` 多说了什么：`counterexample` 只给见证；
    本条把它**用作**反例，直接否定派单的整条量化命题 ——
    于是「T43 卡了 45 分钟的 `nodup_two_mem`」不是难证，而是**不成立**。 -/
theorem nodup_two_mem_is_false {α : Type v} (x y : α) (hne : x ≠ y) :
    ¬ (∀ (l : List α), x ∈ l → y ∈ l → x ≠ y → ¬ l.Nodup) :=
  fun h => (h [x, y] List.mem_cons_self (List.mem_cons_of_mem x List.mem_cons_self) hne)
    (counterexample x y hne).2.2.2

/-! ## §2 真形态：`Nodup` 说「一个值至多一个位置」 -/

/-- **`Nodup` 的头不在尾部**（「一个值至多一个位置」的**归纳步**）。

    比 `nd_head` 多说了什么：`nd_head` 说「头 ≠ 尾部**任意**元素」；
    本条把 `y` 固定成头自己，把「头不出现在尾部」做成**可直接喂的命题** ——
    这是「一个值占两个位置」的最小反命题。

    ⚠ 写法：`fun ha => (nd_head h a ha) rfl` —— 不能写成
    `fun ha => absurd rfl (nd_head h a ha)`（后者触发 §3.1(b) 的具体化）。 -/
theorem nodup_cons_not_mem {α : Type v} {a : α} {as : List α} (h : (a :: as).Nodup) :
    ¬ (a ∈ as) :=
  fun ha => (nd_head h a ha) rfl

/-- **★ 一个值占两个位置 ⟹ 不可能 `Nodup`**（§2.1，`nodup_two_mem` 的**真形态**）。

    比 `nodup_cons_not_mem` 多说了什么：那一条只谈**头** `a`；
    本条允许任意 `y` —— 只要 `y` 在**头部位置**出现一次（`y = a`）、
    又在**尾部位置**再出现一次（`y ∈ as`），`Nodup` 就不成立。
    这是「同一值占两个不同位置」的**最小可写形式**，
    也是 T43「同一个像点不可能占两条记录」的**全部内容**。

    ⚠ 陈述**必须**带两个不同位置。把「两个位置」换成「两次成员资格」
    （`x ∈ l → x ∈ l → ¬ l.Nodup`）是**假**的 —— §1 的反例正是这个原因：
    `List.Mem.head` 可以对同一位置走两次。 -/
theorem nodup_two_positions {α : Type v} {a y : α} {as : List α} (h : (a :: as).Nodup) :
    y = a → y ∈ as → False :=
  fun heq hy => nodup_cons_not_mem h (heq ▸ hy)

end FateV2.Core

/-! ## §5 公理自检（`#print axioms` 实测） -/

#print axioms FateV2.Core.counterexample
#print axioms FateV2.Core.nodup_two_mem_is_false
#print axioms FateV2.Core.nodup_cons_not_mem
#print axioms FateV2.Core.nodup_two_positions
