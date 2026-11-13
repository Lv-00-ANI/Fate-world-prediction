import FateWorld.FateV2.Core.InvalidateClosure

/-!
  # Core · 传递闭包的稳定性（有界性）

  ## 迁移登记
  - 来源：新写（承接 `_报告/T6b-进度.md` §4 的未达成项 `closure_stabilizes`）
  - 动作：C 重写（T6b 卡住的不是数学而是写法；本批换了三条写法纪律）
  - 对应环节：IR 语言化（D 类）第 6 项续 · 专项 T9
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：新建；只读引用 `Core/Closure.lean`、`Core/ClosureMono.lean`、`Core/DeclGraph.lean`
  - 状态：已编译未验证

  ## 一、主定理

  ```lean
  theorem closure_stabilizes [DecidableEq K] (g : DeclGraph K) (roots : List K) :
      ∃ bound, ∀ n ≥ bound, closureN g n roots = closureN g bound roots
  ```

  **界 = `(allKeys g roots).length`**（`allKeys` 把「`roots` 的各键」与「`g` 里每条
  声明的 `key` 与 `deps`」并成一张表，**不去重**）。它的长度 ≤
  `roots.length + g.length * (1 + maxDepsLen)`，但**具体形式不重要**——
  重要的是它只依赖于 `g` 与 `roots`，与 `n` 无关。

  ## 二、为什么界必须收进 `deps`（T6b 的建议里没有这一条）

  T6b 建议界取 `g.length`。**那不够**：`depsOf g r` 取的是某条声明的 `deps`，
  其中的键**可以根本不在 `g` 里**（悬空依赖）。闭包会把这些悬空键原样吐出来，
  所以界必须覆盖「所有可能被吐出的键」，即 `key ∪ deps` 的全集。

  ## 三、T6b「本机归约坏了」的说法：实测复现与更正

  T6b §4.1 声称 `(x :: xs) ++ ys` 与 `n + 1` **不**按构造子归约，并据此说
  有界性这条路「被封死」。**本次实测（`lake env lean`，Lean 4.33.0-rc1）**：

  | 命题 | 结果 |
  |---|---|
  | `example (n : Nat) : n + 1 = Nat.succ n := rfl` | ✅ 通过 |
  | `example (x : Nat) (xs ys : List Nat) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl` | ✅ 通过 |
  | `example (ys : List Nat) : [] ++ ys = ys := rfl` | ✅ 通过 |
  | `example (n : Nat) : 0 + n = n := rfl` | ❌ 失败（**`Nat.add` 在第一个参数上递归，需 `Nat.zero_add`**，与「归约坏了」无关） |

  ⟹ **只有 `0 + n` 不归约**，其余都正常；「归约坏了」的结论撤回。

  本批实测的**真**障碍是另外三条（都不是归约问题，是**引用**问题）：

  | 写法 | 后果 | 本批的对策 |
  |---|---|---|
  | `List.filter` 的 `rfl` 展开 | 停在 `match p a with` 匹配子，`rfl` 失败 | `dsimp only [List.filter]` 后 `rw [p a = true]` |
  | 对 WF 定义用 `rw [f]` / `f.eq_def` | `Quot.sound` | 用 `f.induct` 做归纳（实测零公理） |
  | `List.attach` / `List.unattach` 相关引理 | `propext` | 长度引理对**普通列表**陈述，`decreasing_by` 里就地桥接 |

  ## 四、公理纪律（本文件全部避开）

  不引用 `List.mem_cons` / `List.nodup_cons` / `List.Nodup.length_le_card` / `Finset.card`；
  不用 `simp` / `by_contra` / `by_cases h : ∃ …` / `funext` / `decide` / `omega`；
  `∈` 只用构造子模式（`cases h with | head | tail`）消解。
-/

namespace FateV2.Core.DeclGraph

universe u

variable {K : Type u}

/-! ## §1 `List.filter` 的一步展开（零公理）

  `List.filter` 的定义停在 `match p a with …` 的匹配子上，`rfl` 展不开
  （T6b 把它误记为「`++` 不归约」，实为 `filter` 的匹配子）。
  `dsimp only [List.filter]` 把目标化成 `List.filter.match_1 … (p a) …`，
  此时归约点是 `p a`；再 `rw` 成字面 `true` / `false`，ι 归约才发生。 -/

/-- **`List.filter` 表头为真时走一步**。

    比 `List.filter` 的定义多说了什么：定义只给「怎么算」，本条给出
    **展开所需的前提形态**（`p a = true` 必须显式给出，`rfl` 不够）——
    这是本文件后面每一条过滤引理的唯一入口。 -/
theorem lf_cons_true {α : Type u} (p : α → Bool) (a : α) (as : List α)
    (h : p a = true) : List.filter p (a :: as) = a :: List.filter p as := by
  dsimp only [List.filter]
  rw [h]

/-- **`List.filter` 表头为假时走一步**（`lf_cons_true` 的另一分支）。 -/
theorem lf_cons_false {α : Type u} (p : α → Bool) (a : α) (as : List α)
    (h : p a = false) : List.filter p (a :: as) = List.filter p as := by
  dsimp only [List.filter]
  rw [h]

/-! ## §2 `List.filter` 的四条规格（长度 / 成员 / 谓词 / 反向成员） -/

/-- **过滤不改长**：`(l.filter p).length ≤ l.length`。

    比 `List.filter` 的定义多说了什么：定义只说「删什么」，本条给出
    **删的上界**——删多少不知道，但不会变长。这是 `dedup` 长度引理的唯一来源。 -/
theorem len_filter_le {α : Type u} (p : α → Bool) :
    ∀ (l : List α), (l.filter p).length ≤ l.length
  | [] => Nat.le_refl _
  | b :: bs => by
      cases hp : p b with
      | true =>
          rw [lf_cons_true p b bs hp]
          change (bs.filter p).length + 1 ≤ bs.length + 1
          exact Nat.succ_le_succ (len_filter_le p bs)
      | false =>
          rw [lf_cons_false p b bs hp]
          change (bs.filter p).length ≤ bs.length + 1
          exact Nat.le_trans (len_filter_le p bs) (Nat.le_succ _)

/-- **留下的元素一定在原表里**。

    比 `List.filter` 的定义多说了什么：定义是「跑一遍」，本条说「不漏原表」 ——
    它是「闭包只装图里的东西」这一直觉的列表层对应物。 -/
theorem mem_of_mem_filter {α : Type u} (p : α → Bool) :
    ∀ {l : List α} {a : α}, a ∈ l.filter p → a ∈ l
  | b :: bs, a, h => by
      cases hp : p b with
      | true =>
          rw [lf_cons_true p b bs hp] at h
          cases h with
          | head => exact List.mem_cons_self
          | tail _ h3 => exact List.mem_cons_of_mem b (mem_of_mem_filter p h3)
      | false =>
          rw [lf_cons_false p b bs hp] at h
          exact List.mem_cons_of_mem b (mem_of_mem_filter p h)

/-- **留下的元素谓词必真**。

    比 `List.filter` 的定义多说了什么：定义按谓词删，本条说**删干净了**——
    没有「谓词为假却留在表里」的漏网者。 -/
theorem prop_of_mem_filter {α : Type u} (p : α → Bool) :
    ∀ {l : List α} {a : α}, a ∈ l.filter p → p a = true
  | b :: bs, a, h => by
      cases hp : p b with
      | true =>
          rw [lf_cons_true p b bs hp] at h
          cases h with
          | head => exact hp
          | tail _ h3 => exact prop_of_mem_filter p h3
      | false =>
          rw [lf_cons_false p b bs hp] at h
          exact prop_of_mem_filter p h

/-- **谓词为真且在原表里 ⟹ 一定被留下**（上一条的逆）。

    比 `List.filter` 的定义多说了什么：`prop_of_mem_filter` 只说「留下的都是好的」，
    本条补「好的都留」——两者合起来才是「过滤 = 按谓词精确分拣」。 -/
theorem mem_filter_of_mem {α : Type u} (p : α → Bool) :
    ∀ {l : List α} {a : α}, a ∈ l → p a = true → a ∈ l.filter p
  | b :: bs, a, h, hp => by
      cases hb : p b with
      | true =>
          rw [lf_cons_true p b bs hb]
          cases h with
          | head => exact List.mem_cons_self
          | tail _ h3 => exact List.mem_cons_of_mem b (mem_filter_of_mem p h3 hp)
      | false =>
          rw [lf_cons_false p b bs hb]
          cases h with
          | head =>
              exact absurd hp (by rw [show p b = false from hb]; intro hh; exact Bool.noConfusion hh)
          | tail _ h3 => exact mem_filter_of_mem p h3 hp

/-! ## §3 删重 `dedup`：把「有限集」变成「有限列表」

  鸽笼需要「无重复列表长度 ≤ 键的全集大小」。本项目的 `Decl.deps` 是
  `List DeclKey`，**允许重复**，所以不能直接用；这里先手写一个累积删重
  `dedup`（保留**第一次**出现的那个），把任意表压成 `Nodup` 表。

  ⚠ 三条写法纪律（本批实测）：
  * 对 `dedup` 这种 WF 定义**不能** `rw [dedup]` / 用 `dedup.eq_def`
    （实测 `Quot.sound`）；改用 `dedup.induct`（实测零公理）；
  * `Nodup` 只能「构造出」不能「消掉」：
    `match h with | List.Pairwise.cons hh ht => …` 可用（零公理），
    `List.nodup_cons`（`↔`）带 `propext`；
  * 表头自身的 `decide (y = y)` 不在任何假设里，`rw` 找不到它，
    必须自己在**当前目标**里造一个 `have` 才能重写。 -/

end FateV2.Core.DeclGraph

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | `len_filter_attach` | **未交付**。需要 `(m.attach.filter g).unattach.length ≤ m.length`，
      但 `List.length_attach` / `List.length_unattach` 实测带 `propext`，
      故该引理及其下游 `dedup_length_le` 都**不是零公理**，按 `Core/` 纪律**不予收录**。 |
  | 2 | `dedup` / `dedup_length_le` / `nodup_dedup` | **未交付**。`dedup` 的 WF 递归实参被展开成
      `(xs.attach.filter g).unattach` 形态，与目标里的普通 `filter` 形态不一致；
      要把两者对上就需要 `propext`。**这是本专项未能突破的真实障碍。** |
  | 3 | `closure_stabilizes` | **未证**。原计划靠 `dedup` 得到鸽笼长度界，
      而 `dedup` 因上条无法零公理化，故整条路线受阻。 |
  | 4 | 可行的替代路线（留给下一轮） | 不做「去重求长度」，改做「**不动点传播**」：
      利用 `ClosureMono.closureN_fix_to_aux` + `closureN_mono`，
      证「某层与下一层相同 ⟹ 此后恒等」，再设法在有界层数内找到那个不动点。
      这条路线**完全不碰 `attach/unattach`**，值得优先尝试。 |
-/

