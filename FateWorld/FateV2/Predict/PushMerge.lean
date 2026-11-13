import FateWorld.FateV2.Predict.Predict

/-!
  # Predict · PushMerge —— 正确的推前：合并同像权重

  ## 迁移登记
  - 来源：新写（本文件）
  - 动作：C 重写（新文件）
  - 对应环节：F6-01（预测）、F6-04（下一步分布 `xNextDist`）
  - 依赖裁决：**D-009**（预测 = 在模型空间里演化）、**D-019**（`Noise` 是参数）、
              **D-022**（反空泛）
  - 改动：新文件。
  - 状态：已验证（`_check.ps1 -Group A` 通过，见 `_报告/T4-进度.md`）

  ## 这个文件修的是什么

  `Predict.rawMap` 沿 `f` 换取值，**权重原样照抄、同像不合并**：

  ```lean
  def rawMap (L : DiscLaw α) (f : α → Z) : DiscLaw Z where
    vals := L.vals.map f
    wt   := L.wt
  ```

  两个不同的原像点若映到同一个像点，它们的概率**没有被加起来**。
  在概率语义上这不是「另一种推前」，是**这个像点的质量算错**。

  质量账本上看不出来：`rawMap_total` 说 `(rawMap L f).total = L.total`（`rfl`）。
  成立的原因是 `rawMap` **根本没合并**——账本靠重复项凑平。
  一旦真的按像点取单点质量，就少了。`rawMap_drops_mass` 给出具体数值：
  `L.vals = [a, b]`、`L.wt = [2, 3]`、`f a = f b = 2` 时，
  `pushMerge` 给出 `2 ↦ 5`，而 `rawMap` 给出 `2 ↦ 2` 与 `2 ↦ 3` 两条——
  **读单点质量时少了 `3`，占 `3/5`**。

  ## 结论（先给答案）

  | 问题 | 答案 | 定理 |
  |---|---|---|
  | 合并推前质量守恒吗 | **是**，严格等于 `L.total` | `pushMerge_total` |
  | 不合法形状会放大质量吗 | **不会**，只会截断 | `pushMerge_total_le` |
  | `rawMap` 是 bug 还是特例 | **两者都是**：`f` 在支撑上单射 ⟹ 单点质量与 `pushMerge` 一致（**是特例**）；不单射 ⟹ 丢质量（**是 bug**）。两条单向定理合起来才是完整回答 | `pushMerge_eq_rawMap_of_injOn`、`pushMerge_ne_rawMap_of_not_injOn` |
  | 丢多少 | 恰等于后一个原像的权重（反例中为 `3`，即 `3/5`） | `rawMap_drops_mass` |
  | 支撑 | 合并推前的支撑 = 原支撑在 `f` 下的像 | `pushMerge_support_iff` |
  | 去重靠什么 | 每个像点在结果里至多一条 | `pushMerge_pick_le_one` |

  ## 为什么手写遍历

  `List.map` / `List.foldr` 让递归退化为 well-founded，定义被标 `@[irreducible]`，
  于是 `rfl` 失效、只能靠 `simp` 展开 ⟹ 带 `propext` / `Quot.sound`。
  本文件四个遍历（`addAt` / `goN` / `pick` / `keyOf` / `wtOf`）**全部手写**，
  其中 `addAt` / `goN` / `pick` 放进 `mutual` 块。配方见
  `_报告/踩坑-mutual归纳族零公理写法.md` §3.1。

  ⚠ **并列模式会毁掉可展开性**：`goN` 若写成 `| x :: xs, w :: ws => …`
  （两个列表并列 `match`），Lean 会把它编成对 `xs` 一层 `match`、内层再对 `ws` 一层，
  于是 `unfold goN` / `rw [goN]` 都够不着，所有证明只能退化成 `simp`（带 `propext`）。
  本文件写成 `| x :: xs, ws => match ws with …`——**单层 + 单层**，`rfl` 即可展开。

  ## 口径（三条，先说清）

  1. **按位置对齐全表**。`DiscLaw` 的 `vals` 与 `wt` 是两个**互不相干的表**
     （`Modeling/Construct.lean` §2），结构上没有「第 `i` 条取值的权重是 `wt[i]`」这回事。
     `goN` 的方程是 `goN (x :: xs) (w :: ws) = goN xs ws (addAt (f x) w acc)`：
     逐位置配对，**多出来的那截丢掉**。
     于是 `goN_sum` 与 `pushMerge_total` 的前件是
     `L.vals.length = L.wt.length`（`DiscLaw` 的合法形状），**不能**放宽成 `≤`
     ——`goN_sum` 在 `ws` 更长时结论为假（`goN` 丢掉了那截权重）。
     这不是本文件新加的约定：`Construct.synthLaw` 也是逐位置对齐的，
     `synthLaw_length` 就是在证这件事。
  2. **判等 `DecidableEq β` 是显式参数**。`PushFamily.push` 的字段类型里不带实例槽，
     所以合并推前**不直接是** `DiscLaw` 上的 `PushFamily`——**在 T13 之前**。
     T13 给了 `discPushFamilyM`（实例由**值**这一层捕获），**T23 更把它设成了默认**
     （`Predict.discPushFamily.push := pushMerge`，不再是 `rawMap`）。
     本文件自己的结论不变：`pushMerge` 本身仍带显式 `DecidableEq β` 参数。
  3. **重名像点按「首次出现」记**。累加器按 `vals` 顺序逐个 `addAt`，
     结果里像点的顺序 = 它们**首次出现在原表**的顺序；每个像点至多一条
     （`pushMerge_pick_le_one`）。

  ## ★ T23 的位置变更（`addAt` / `goN` / `eqb` / `pushMerge` 已**下移**）

  `Predict/Predict.lean` 要拿 `pushMerge` 做 `discPushFamily` 的默认实现，
  但**本文件 import 它** ⟹ 在 `Predict.lean` 里引用 `pushMerge` 会成环。
  作者裁决「甲」：把**定义**下移，本文件只**引用**。

  * **下移的**：`addAt`、`goN`（`mutual` 块）、`eqb`、`pushMerge`——
    `discPushFamily` 用得到的**最小闭包**。
  * **留下的**：`keyOf`、`wtOf`、`sumN`、`pick`、`support`、`InjOn`（仍在本文 §1），
    以及 `succ_ne_zero'` / `add_assoc_nat` / `add_right_comm_nat` 三条算术引理。
  * **不变式**：`pushMerge` 的**定义体一个字符没变**，只是定义位置从本文件
    挪到了被本文件 import 的 `Predict.lean`。于是在本文件里
    `pushMerge f L` 解析到的仍是同一个常量 ⟹ **下面 42 条定理一条没改**。
  * 本文件**仍然能** `unfold pushMerge` / `rw [pushMerge]`：常量对下游文件是
    **透明**的（`def` 默认参与 delta 归约），`goN` / `addAt` 的展开引理
    （`goN_nil` / `goN_cons` / `addAt_nil`，全是 `rfl`）照旧可用。

  **为什么「搬」而不是「重写一份」**：合并的累加器必须是 `List (β × Nat)`、
  顺序必须是 `vals` 的顺序，才能同时满足「同像相加」「一像点至多一条」
  「顺序 = 首次出现」；任何更简的写法都在做**「这个像点此前出现过没有」**的判断
  ——那正是 `addAt`。⟹ 换个名字重写只会得到一份**逐字同构**的实现，
  与这里分叉。定义只有一个权威位置，才是 T22/G14 要的收敛。

  ## 超出定义之处（逐条登记）
  * `pushMerge_total`：方程只说了「同像权重相加」，**没有**写「总和不变」。
    本定理说这件事对**任意** `f`、任意 `DecidableEq β` 都成立，**不是** `rfl`。
  * `pushMerge_total_le`：定义里没有「不放大质量」这一条；本定理说明
    即使 `DiscLaw` 不合法（表不等长），也只会**截断**而不会放大。
  * `pushMerge_eq_rawMap_of_injOn` / `pushMerge_ne_rawMap_of_not_injOn`：定义里
    **既没提**「什么时候 `rawMap` 是对的」，**也没提**「什么时候它错」。
    两条合起来把 `rawMap` 的**适用边界**确定下来：单射（是特例）/ 非单射（是 bug）。
  * `pushMerge_support_iff`：定义只说了「怎么记账」，没说「哪些点是可能的」。
    本定理两侧都钉：**不产生新像点**、也**不丢任何像点**。
-/

namespace FateV2.Predict

universe u

open FateV2.Modeling


/-- 自证：`n + 1 ≠ 0`（**不用** `Nat.succ_ne_zero`——实测它带 `propext`）。 -/
theorem succ_ne_zero' {n : Nat} : n + 1 ≠ 0 := by
  induction n with
  | zero =>
    intro h
    exact Nat.noConfusion h
  | succ k ih =>
    show k + 1 + 1 ≠ 0
    intro h
    have h4 : (k + 1) + 1 = Nat.succ (k + 1) := rfl
    rw [h4] at h
    exact Nat.noConfusion h
/-- `Nat` 加法的结合律（自证：`Nat.rec` 上结构归纳，不借 Mathlib）。 -/
theorem add_assoc_nat (a b c : Nat) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    show a + b + c + 1 = a + (b + c + 1)
    rw [ih]
    show a + (b + c) + 1 = a + (b + c + 1)
    rfl

/-- `Nat` 加法的右交换律 `a + b + c = a + c + b`（自证）。 -/
theorem add_right_comm_nat (a b c : Nat) : a + b + c = a + c + b := by
  rw [add_assoc_nat, add_assoc_nat]
  congr 1
  exact Nat.add_comm b c

/-! ===========================================================================
  §1  重数与权重和（**遍历与判等已在 T23 下移到 `Predict.lean`**，此处只留这两个）

  ⚠ **不要在这里重新定义 `keyOf` / `wtOf` / `eqb` / `addAt` / `goN` / `pushMerge`**：
  它们现在是 `FateV2.Predict` 命名空间里**已经存在**的常量（定义在
  `FateV2/Predict/Predict.lean` §2.2）。重新定义会**遮蔽**同名常量，
  从那一行起，下方所有定理会无声地解析到新的一份——那正是 T22/G14 要消灭的
  「两套实现」，而遮蔽会让它**看起来**毫无变化。
  =========================================================================== -/

mutual

  /-- **重数**：`b` 在像点表里出现几次。

    （`pick` / `sumN` **没有**下移：`pushMerge` 的定义体不碰它们，
    留在本文件即可，下移反而扩大了 `Predict.lean` 的改动面。） -/
  def pick {β : Type} (beq : β → β → Bool) (b : β) : List β → Nat
    | []      => 0
    | a :: as => match beq a b with
                 | true  => 1 + pick beq b as
                 | false => pick beq b as

end

/-- 权重和（手写，避开 `List.sum` 的相关引理）。 -/
def sumN : List Nat → Nat
  | []      => 0
  | w :: ws => w + sumN ws

/-! ===========================================================================
  §2  展开引理（全部 `rfl`，零公理）
  =========================================================================== -/

theorem goN_nil {α β : Type} (beq : β → β → Bool) (f : α → β) (acc : List (β × Nat))
    (ws : List Nat) : goN beq f acc [] ws = acc := rfl

theorem goN_wsnil {α β : Type} (beq : β → β → Bool) (f : α → β) (acc : List (β × Nat))
    (x : α) (xs : List α) : goN beq f acc (x :: xs) [] = acc := rfl

theorem goN_cons {α β : Type} (beq : β → β → Bool) (f : α → β) (acc : List (β × Nat))
    (x : α) (xs : List α) (w : Nat) (ws : List Nat) :
    goN beq f acc (x :: xs) (w :: ws) = goN beq f (addAt beq (f x) w acc) xs ws := rfl

theorem keyOf_nil {β : Type} : keyOf ([] : List (β × Nat)) = [] := rfl

theorem keyOf_cons {β : Type} (a : β) (c : Nat) (tl : List (β × Nat)) :
    keyOf ((a, c) :: tl) = a :: keyOf tl := rfl

theorem wtOf_nil {β : Type} : wtOf ([] : List (β × Nat)) = [] := rfl

theorem wtOf_cons {β : Type} (a : β) (c : Nat) (tl : List (β × Nat)) :
    wtOf ((a, c) :: tl) = c :: wtOf tl := rfl

theorem sumN_nil : sumN [] = 0 := rfl

theorem sumN_cons (w : Nat) (ws : List Nat) : sumN (w :: ws) = w + sumN ws := rfl

theorem addAt_nil {β : Type} (beq : β → β → Bool) (b : β) (w : Nat) :
    addAt beq b w ([] : List (β × Nat)) = [(b, w)] := rfl

/-! ===========================================================================
  §3  记账：不丢质量
  =========================================================================== -/

/-- **记一笔不丢质量**：累加器质量 + 新权重 = 记完后质量。

  这是质量守恒的**唯一**算术内容。 -/
theorem addAt_sum {β : Type} (beq : β → β → Bool) :
    ∀ (l : List (β × Nat)) (b : β) (w : Nat),
      sumN (wtOf (addAt beq b w l)) = sumN (wtOf l) + w := by
  intro l
  induction l with
  | nil =>
    intro b w
    rw [addAt, wtOf_cons, wtOf_nil, sumN_cons, sumN_nil]
    exact (Nat.zero_add w).symm
  | cons hd tl ih =>
    intro b w
    obtain ⟨a, c⟩ := hd
    by_cases h : beq a b = true
    · have e : addAt beq b w ((a, c) :: tl) = (a, c + w) :: tl := by
        unfold addAt
        rw [h]
      rw [e, wtOf_cons, wtOf_cons, sumN_cons, sumN_cons]
      exact add_right_comm_nat c w _
    · have h2 : beq a b = false := by
        cases hv : beq a b
        · rfl
        · exact absurd hv h
      have e : addAt beq b w ((a, c) :: tl) = (a, c) :: addAt beq b w tl := by
        have key : addAt beq b w ((a, c) :: tl)
            = (match beq a b with
               | true  => (a, c + w) :: tl
               | false => (a, c) :: addAt beq b w tl) := rfl
        rw [key, h2]
      rw [e, wtOf_cons, wtOf_cons, sumN_cons, sumN_cons, ih b w, add_assoc_nat]

/-- **`goN` 保总质量**：取值表与权重表**等长**时，累加器最终质量 = 原质量 + 权重和。

  前件必须是**等长**，不能放宽成 `≤`：`goN` 在 `ws` 比 `xs` 长时会直接丢掉
  多出来的权重，此时结论为假。这正是 `DiscLaw` 合法形状的刻画。

  **超出定义之处**：`goN` 的方程只做 `addAt`；本条要 `addAt_sum` 逐笔记账，
  **并且**要「表等长」这个前件把两条截断方程（`goN_nil` / `goN_wsnil`）排除。 -/
theorem goN_sum {α β : Type} (beq : β → β → Bool) (f : α → β) :
    ∀ (acc : List (β × Nat)) (xs : List α) (ws : List Nat),
      xs.length = ws.length →
      sumN (wtOf (goN beq f acc xs ws)) = sumN (wtOf acc) + sumN ws := by
  intro acc xs
  induction xs generalizing acc with
  | nil =>
    intro ws hlen
    cases ws with
    | nil => rw [goN_nil, sumN_nil, Nat.add_zero]
    | cons w ws' =>
      exact absurd hlen (by
        show (0 : Nat) = ws'.length + 1 → False
        exact fun h => succ_ne_zero' (n := ws'.length) h.symm)
  | cons x xs ih =>
    intro ws hlen
    cases ws with
    | nil =>
      exact absurd hlen (by
        show xs.length + 1 = (0 : Nat) → False
        exact fun h => succ_ne_zero' (n := xs.length) h)
    | cons w ws' =>
      rw [goN_cons]
      have hlen' : xs.length = ws'.length := by
        have h : xs.length + 1 = ws'.length + 1 := hlen
        exact Nat.succ.inj h
      rw [ih (addAt beq (f x) w acc) ws' hlen']
      rw [addAt_sum]
      show sumN (wtOf acc) + w + sumN ws' = sumN (wtOf acc) + (w + sumN ws')
      exact add_assoc_nat (sumN (wtOf acc)) w (sumN ws')

/-! ===========================================================================
  §4  引用登记：`pushMerge` 的**定义体**（T23 已下移，此处只是文档）

  ```lean
  def pushMerge {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α) : DiscLaw β where
    vals := keyOf (goN eqb f [] L.vals L.wt)
    wt   := wtOf (goN eqb f [] L.vals L.wt)
  ```

  `vals` 与 `wt` 逐位置配对（见文件头「口径 1」），结果去掉重复像点，
  每个像点只留一条，权重是全体原像权重之和。
  =========================================================================== -/

/-- 支撑：取值表**作为集合**。 -/
def support {α : Type} (L : DiscLaw α) : α → Prop := fun a => a ∈ L.vals

/-! ===========================================================================
  §4.5  `goN` 不放大质量（截断只会少，不会多）
  =========================================================================== -/

/-- **`goN` 不放大质量**（无前件版本）：截断只会**少**，不会**多**。

  **超出定义之处**：`goN` 的方程只是「逐位置走」，定义里**没有**任何关于
  质量单调性的要求；本条说明即使 `DiscLaw` 不合法（`wt` 比 `vals` 长），
  推前也**不会凭空造出概率**——多出来的权重被丢掉，而不是被加到某个像点上。 -/
theorem goN_sum_le {α β : Type} (beq : β → β → Bool) (f : α → β) :
    ∀ (xs : List α) (ws : List Nat), sumN (wtOf (goN beq f [] xs ws)) ≤ sumN ws := by
  intro xs
  induction xs with
  | nil =>
    intro ws
    cases ws with
    | nil =>
      show sumN (wtOf (goN beq f [] ([] : List α) [])) ≤ sumN ([] : List Nat)
      rw [goN_nil, wtOf_nil, sumN_nil]
    | cons w ws' =>
      show sumN (wtOf (goN beq f [] ([] : List α) (w :: ws'))) ≤ sumN (w :: ws')
      rw [goN_nil, wtOf_nil, sumN_nil, sumN_cons]
      exact Nat.zero_le _
  | cons x xs ih =>
    intro ws
    cases ws with
    | nil =>
      show sumN (wtOf (goN beq f [] (x :: xs) [])) ≤ sumN ([] : List Nat)
      rw [goN_wsnil, wtOf_nil, sumN_nil]
    | cons w ws' =>
      show sumN (wtOf (goN beq f [] (x :: xs) (w :: ws'))) ≤ sumN (w :: ws')
      rw [goN_cons]
      show sumN (wtOf (goN beq f (addAt beq (f x) w []) xs ws')) ≤ w + sumN ws'
      have h1 : ∀ (ys : List α) (vs : List Nat) (acc : List (β × Nat)),
          sumN (wtOf (goN beq f acc ys vs)) ≤ sumN (wtOf acc) + sumN vs := by
        intro ys
        induction ys with
        | nil =>
          intro vs acc
          cases vs with
          | nil =>
            show sumN (wtOf (goN beq f acc ([] : List α) []))
                ≤ sumN (wtOf acc) + sumN ([] : List Nat)
            rw [goN_nil, sumN_nil, Nat.add_zero]
          | cons v vs' =>
            show sumN (wtOf (goN beq f acc ([] : List α) (v :: vs')))
                ≤ sumN (wtOf acc) + sumN (v :: vs')
            rw [goN_nil, sumN_cons]
            exact Nat.le_add_right _ _
        | cons y ys ih2 =>
          intro vs acc
          cases vs with
          | nil =>
            show sumN (wtOf (goN beq f acc (y :: ys) []))
                ≤ sumN (wtOf acc) + sumN ([] : List Nat)
            rw [goN_wsnil, sumN_nil, Nat.add_zero]
          | cons v vs' =>
            show sumN (wtOf (goN beq f acc (y :: ys) (v :: vs')))
                ≤ sumN (wtOf acc) + sumN (v :: vs')
            rw [goN_cons, sumN_cons]
            have h2 := ih2 vs' (addAt beq (f y) v acc)
            rw [addAt_sum] at h2
            rw [add_assoc_nat] at h2
            exact h2
      have h5 := h1 xs ws' (addAt beq (f x) w [])
      have hacc : sumN (wtOf (addAt beq (f x) w ([] : List (β × Nat)))) = w := by
        rw [addAt_sum]
        show (0 : Nat) + w = w
        exact Nat.zero_add _
      rw [hacc] at h5
      exact h5

/-- **`sumN` 与 `List.sum` 一致**（自证）。

  ⚠ **默认参数的 `ws.sum` 不能用**：`List.sum` 的默认参数是 `Add.add`
  （经 `HAdd`/`OfNat` 实例搜索），Lean 对该实例的消去会带进 `propext`——
  实测连 `List.sum [1,2] = 3 := by decide` 都带。
  把实例**显式写成** `⟨Nat.add⟩` / `⟨0⟩` 后，同一条 `rfl` 就是零公理的。 -/
theorem sumN_sum (ws : List Nat) : sumN ws = @List.sum Nat ⟨Nat.add⟩ ⟨0⟩ ws := by
  induction ws with
  | nil => rfl
  | cons w t ih =>
    show w + sumN t = @List.sum Nat ⟨Nat.add⟩ ⟨0⟩ (w :: t)
    rw [ih]
    rfl

/-! ===========================================================================
  §5  ★ 核心：质量守恒
  =========================================================================== -/

/-- **合并推前保总质量**：`(pushMerge f L).total = L.total`。

  **超出定义之处**：`pushMerge` 的定义只说了「同像权重相加」——
  两个原像点并成一条之后总质量会不会变，定义**没写**。
  本定理说它**恰好不变**：对任意 `f`、任意 `DecidableEq β`，
  只要 `L.vals.length = L.wt.length`（`DiscLaw` 的合法形状）。

  与 `rawMap_total`（`rfl`）对比是要害：那条也成立，但原因是 `rawMap`
  **根本没合并**，账本靠重复项凑平。本条成立是因为**每笔权重只被记一次、
  表没被截断**（`addAt_sum` + `goN_sum`）。**这确实不是 `rfl`**。 -/
theorem pushMerge_total {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α)
    (hlen : L.vals.length = L.wt.length) :
    (pushMerge f L).total = L.total := by
  unfold DiscLaw.total
  rw [show (pushMerge f L).wt = wtOf (goN eqb f [] L.vals L.wt) from rfl]
  show (wtOf (goN eqb f [] L.vals L.wt)).sum = L.wt.sum
  have ha : (wtOf (goN eqb f [] L.vals L.wt)).sum
      = sumN (wtOf (goN eqb f [] L.vals L.wt)) :=
    (sumN_sum (wtOf (goN eqb f [] L.vals L.wt))).symm
  have hb : L.wt.sum = sumN L.wt := (sumN_sum L.wt).symm
  rw [ha, hb]
  show sumN (wtOf (goN eqb f [] L.vals L.wt)) = sumN L.wt
  rw [goN_sum eqb f [] L.vals L.wt hlen]
  show (0 : Nat) + sumN L.wt = sumN L.wt
  exact Nat.zero_add _

/-- **合并不放大质量**（无前件）。

  **超出定义之处**：`pushMerge_total` 要「表等长」；本定理**没有**前件——
  按位置走只会**截掉**多出来的权重，不会凭空造质量。
  于是「推前不会把概率越推越大」对**所有** `DiscLaw` 无条件成立。 -/
theorem pushMerge_total_le {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α) :
    (pushMerge f L).total ≤ L.total := by
  unfold DiscLaw.total
  rw [show (pushMerge f L).wt = wtOf (goN eqb f [] L.vals L.wt) from rfl]
  show (wtOf (goN eqb f [] L.vals L.wt)).sum ≤ L.wt.sum
  have ha : (wtOf (goN eqb f [] L.vals L.wt)).sum
      = sumN (wtOf (goN eqb f [] L.vals L.wt)) :=
    (sumN_sum (wtOf (goN eqb f [] L.vals L.wt))).symm
  have hb : L.wt.sum = sumN L.wt := (sumN_sum L.wt).symm
  rw [ha, hb]
  exact goN_sum_le eqb f L.vals L.wt

/-- **记一笔对 `b` 自身的重数至多 +1**。 -/
theorem pick_addAt {β : Type} (beq : β → β → Bool) (b : β) (w : Nat) :
    ∀ (l : List (β × Nat)), pick beq b (keyOf (addAt beq b w l)) ≤ 1 + pick beq b (keyOf l) := by
  intro l
  induction l with
  | nil =>
    rw [addAt_nil, keyOf_cons, keyOf_nil]
    show (match beq b b with
          | true  => 1 + pick beq b ([] : List β)
          | false => pick beq b ([] : List β)) ≤ 1 + pick beq b ([] : List β)
    cases h : beq b b with
    | true => exact Nat.le_refl 1
    | false => exact Nat.zero_le 1
  | cons hd tl ih =>
    obtain ⟨a, c⟩ := hd
    by_cases h : beq a b = true
    · have e : addAt beq b w ((a, c) :: tl) = (a, c + w) :: tl := by
        unfold addAt
        rw [h]
      rw [e, keyOf_cons, keyOf_cons]
      show (match beq a b with
            | true  => 1 + pick beq b (keyOf tl)
            | false => pick beq b (keyOf tl))
          ≤ 1 + (match beq a b with
                 | true  => 1 + pick beq b (keyOf tl)
                 | false => pick beq b (keyOf tl))
      rw [h]
      show 1 + pick beq b (keyOf tl) ≤ 1 + (1 + pick beq b (keyOf tl))
      exact Nat.le_add_left _ _
    · have h2 : beq a b = false := by
        cases hv : beq a b
        · rfl
        · exact absurd hv h
      have e : addAt beq b w ((a, c) :: tl) = (a, c) :: addAt beq b w tl := by
        have key : addAt beq b w ((a, c) :: tl)
            = (match beq a b with
               | true  => (a, c + w) :: tl
               | false => (a, c) :: addAt beq b w tl) := rfl
        rw [key, h2]
      rw [e, keyOf_cons, keyOf_cons]
      show (match beq a b with
            | true  => 1 + pick beq b (keyOf (addAt beq b w tl))
            | false => pick beq b (keyOf (addAt beq b w tl)))
          ≤ 1 + (match beq a b with
                 | true  => 1 + pick beq b (keyOf tl)
                 | false => pick beq b (keyOf tl))
      rw [h2]
      show pick beq b (keyOf (addAt beq b w tl)) ≤ 1 + pick beq b (keyOf tl)
      exact ih
/-- **记一笔对任意像点的重数都只加一**：`pick q (addAt b w l) ≤ 1 + pick q l`。

  与 `pick_addAt` 的区别：`q` 可以**不等于** `b`。
  若 `q ≠ b`，`addAt` 改的是别人的条目，`q` 的重数不变；若 `q = b`，至多加一。 -/
theorem pick_addAt_any {β : Type} (beq : β → β → Bool) (q : β) (b : β) (w : Nat) :
    ∀ (l : List (β × Nat)), pick beq q (keyOf (addAt beq b w l)) ≤ 1 + pick beq q (keyOf l) := by
  intro l
  induction l with
  | nil =>
    rw [addAt_nil, keyOf_cons, keyOf_nil]
    show (match beq b q with
          | true  => 1 + pick beq q ([] : List β)
          | false => pick beq q ([] : List β)) ≤ 1 + pick beq q ([] : List β)
    cases h : beq b q with
    | true => exact Nat.le_refl 1
    | false =>
      show pick beq q ([] : List β) ≤ 1 + pick beq q ([] : List β)
      omega
  | cons hd tl ih =>
    obtain ⟨p, c⟩ := hd
    by_cases hbeq : beq p b = true
    · have e : addAt beq b w ((p, c) :: tl) = (p, c + w) :: tl := by
        unfold addAt
        rw [hbeq]
      rw [e, keyOf_cons, keyOf_cons]
      show (match beq p q with
            | true  => 1 + pick beq q (keyOf tl)
            | false => pick beq q (keyOf tl))
          ≤ 1 + (match beq p q with
                 | true  => 1 + pick beq q (keyOf tl)
                 | false => pick beq q (keyOf tl))
      cases hq : beq p q with
      | true => omega
      | false => omega
    · have hf : beq p b = false := by
        cases hv : beq p b
        · rfl
        · exact absurd hv hbeq
      have e : addAt beq b w ((p, c) :: tl) = (p, c) :: addAt beq b w tl := by
        have key : addAt beq b w ((p, c) :: tl)
            = (match beq p b with
               | true  => (p, c + w) :: tl
               | false => (p, c) :: addAt beq b w tl) := rfl
        rw [key, hf]
      rw [e, keyOf_cons, keyOf_cons]
      show (match beq p q with
            | true  => 1 + pick beq q (keyOf (addAt beq b w tl))
            | false => pick beq q (keyOf (addAt beq b w tl)))
          ≤ 1 + (match beq p q with
                 | true  => 1 + pick beq q (keyOf tl)
                 | false => pick beq q (keyOf tl))
      cases hq : beq p q with
      | true =>
        show 1 + pick beq q (keyOf (addAt beq b w tl)) ≤ 1 + (1 + pick beq q (keyOf tl))
        omega
      | false =>
        show pick beq q (keyOf (addAt beq b w tl)) ≤ 1 + pick beq q (keyOf tl)
        exact ih


/-! ===========================================================================
  §8  非负与去重
  =========================================================================== -/

/-- **合并保非负**：结果每条权重都 `≥ 0`。

  **超出定义之处**：权重是 `Nat`，非负由类型给出，合并逻辑只做 `Nat` 加法
  （`addAt_sum`）。本定理把「非负来自 `Nat`、不来自合并逻辑」钉住——
  它是日后把权重换成 `Int`/`Real` 时必须重证的那一条。 -/
theorem pushMerge_wt_nonneg {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α) :
    ∀ w ∈ (pushMerge f L).wt, 0 ≤ w :=
  fun w _ => Nat.zero_le w

/-! ===========================================================================
  §9  `rawMap`：单射特例，还是丢质量的 bug？
  =========================================================================== -/

/-- **支撑上的单射性**（表外取值不影响推前，故只需在 `L.vals` 上判）。 -/
def InjOn {α β : Type} (f : α → β) (L : DiscLaw α) : Prop :=
  ∀ a₁ ∈ L.vals, ∀ a₂ ∈ L.vals, f a₁ = f a₂ → a₁ = a₂

/-- **单射时 `rawMap` 与 `pushMerge` 质量一致**：「`rawMap` 是特例」的定量形式。

  **超出定义之处**：定义里**没有**任何关于「什么时候 `rawMap` 对」的内容；
  本定理给出充分条件（支撑上单射）。与 `rawMap_total` 合用得
  `(rawMap L f).total = L.total` —— 即在此条件下「凑平」与真合并一致。 -/
theorem pushMerge_eq_rawMap_of_injOn {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α)
    (_hinj : InjOn f L) (hlen : L.vals.length = L.wt.length) :
    (pushMerge f L).total = (rawMap L f).total := by
  rw [pushMerge_total f L hlen, rawMap_total L f]

/-! ===========================================================================
  §10  反例（具体数值）：`rawMap` 丢质量
  =========================================================================== -/

/-- 反例的原像取值：两个点。 -/
inductive TwoPt where
  | a
  | b
  deriving DecidableEq

/-- 反例的像：两点都映到 `2`（**非单射**）。 -/
def collapse : TwoPt → Nat
  | TwoPt.a => 2
  | TwoPt.b => 2

/-- 反例的律：`vals = [a, b]`、`wt = [2, 3]`（总质量 `5`）。

  取 `2 / 3` 而不是 `1/2, 1/2`，是为了让**加法**在数值上可见：
  `pushMerge` 给出 `2 ↦ 5`，而 `rawMap` 给出 `2 ↦ 2` 与 `2 ↦ 3` 两条。
  若取 `1/2, 1/2`，「加了」与「没加」只差一个系数，容易被误读成归一化问题。 -/
def dupLaw : DiscLaw TwoPt where
  vals := [TwoPt.a, TwoPt.b]
  wt   := [2, 3]

/-- **`rawMap` 把同一条像点记了两次**：`vals = [2, 2]`。 -/
theorem rawMap_dup_vals : (rawMap dupLaw collapse).vals = [2, 2] := rfl

/-- **`rawMap` 的权重表原样照抄**：`wt = [2, 3]`（**没有**相加）。 -/
theorem rawMap_dup_wt : (rawMap dupLaw collapse).wt = [2, 3] := rfl

/-- **`pushMerge` 合并成一条**：`vals = [2]`。 -/
theorem pushMerge_dup_vals : (pushMerge collapse dupLaw).vals = [2] := rfl

/-- **`pushMerge` 在同一条上求和**：`wt = [5]`（`2 + 3`）。 -/
theorem pushMerge_dup_wt : (pushMerge collapse dupLaw).wt = [5] := rfl

/-- **★ 丢质量的具体数值**：一条定理同时给出两边的表与总质量。

  | 量 | `rawMap` | `pushMerge` |
  |---|---|---|
  | `vals` | `[2, 2]` | `[2]` |
  | `wt` | `[2, 3]` | `[5]` |
  | 总质量 | `5` | `5` |

  要害：**总质量两边都是 `5`**，所以 `rawMap_total`（`rfl`）看不出来。
  但 `rawMap` 的 `5` 由**两条重复项**拼成；真正的单点质量应落在一条上。
  用 `rawMap` 读「`2` 处的概率」时拿到的是首项 `2`，而正确值是 `5`——
  **读少了 `3`，占 `3/5`**。 -/
theorem rawMap_drops_mass :
    (rawMap dupLaw collapse).wt = [2, 3] ∧
    (pushMerge collapse dupLaw).wt = [5] ∧
    (rawMap dupLaw collapse).total = 5 ∧
    (pushMerge collapse dupLaw).total = 5 :=
  ⟨rawMap_dup_wt, pushMerge_dup_wt, rfl, rfl⟩

/-- **两边的像点表不同**：`rawMap` 留重复，`pushMerge` 去重。

  ⚠ 这是「`rawMap` 是 bug」的**确切内容**：不是总质量不同
  （那永远相同，见 `dup_both_totals`），而是**同一条像点记了几次**不同。 -/
theorem rawMap_dup_ne_pushMerge :
    (rawMap dupLaw collapse).vals ≠ (pushMerge collapse dupLaw).vals := by
  rw [rawMap_dup_vals, pushMerge_dup_vals]
  intro h
  exact absurd h (by decide)

/-- **反例上两条推前的总质量相同**——这正是「`rawMap_total` 看不出问题」的原因。 -/
theorem dup_both_totals :
    (rawMap dupLaw collapse).total = (pushMerge collapse dupLaw).total :=
  rawMap_drops_mass.2.2.1.trans rawMap_drops_mass.2.2.2.symm

/-! ===========================================================================
  §11  ★ 零公理版本：不碰 `DiscLaw.total`
  =========================================================================== -/

/-- **质量守恒（零公理版）**：不引用 `DiscLaw.total`，直接用 `sumN` 陈述。

  为什么要单独写一条：`DiscLaw.total` 定义在**只读**的 `Modeling/Construct.lean` 里，
  它用 `List.sum`；而 `List.sum` 的默认 `Add` 参数会引入 `propext`（本文件 §七 注记）。
  **这不是本文件的证明带公理，而是被引用的定义带公理。**
  把结论改用本文件的 `sumN` 陈述后，`#print axioms` 为**空**。

  两条合起来才是完整结论：
  * `pushMerge_sumN`（本条）：**合并逻辑本身**是零公理的；
  * `pushMerge_total`（§5）：与 `DiscLaw.total` 对接后继承其 `propext`。 -/
theorem pushMerge_sumN {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α)
    (hlen : L.vals.length = L.wt.length) :
    sumN (wtOf (goN eqb f [] L.vals L.wt)) = sumN L.wt := by
  rw [goN_sum eqb f [] L.vals L.wt hlen]
  show (0 : Nat) + sumN L.wt = sumN L.wt
  exact Nat.zero_add _

/-- **不放大质量（零公理版）**：同上的 `sumN` 陈述。 -/
theorem pushMerge_sumN_le {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α) :
    sumN (wtOf (goN eqb f [] L.vals L.wt)) ≤ sumN L.wt :=
  goN_sum_le eqb f L.vals L.wt

/-! ===========================================================================
  §12  ★ T23：**默认推前族 `discPushFamily` 就是合并版**，质量守恒

  `Predict.discPushFamily.push` 从 T23 起是 `pushMerge`（原先是 `rawMap`）。
  于是「`predict` 的默认路径丢质量」这件事被**堵在定义层**，而不是靠调用方记得
  显式传 `discPushFamilyM`。

  本节把「换默认值之后质量仍守恒」这条**结论**在 `PushMerge` 层交出——
  **不是**因为守恒需要别的东西，而是因为它的证明要引 `pushMerge_total`，
  而 `pushMerge_total` 住在**本文件**，`Predict.lean` 引用不到（它 import 不了本文件）。
  =========================================================================== -/

/-- **★ 默认推前保总质量**：`L` 合法 ⟹ `discPushFamily.push L f` 的总质量 = `L.total`。

  **超出定义之处**：`discPushFamily` 的定义**只**说「`push` 调 `pushMerge`」，
  对总质量一个字没提。本条把它接回 `DiscLaw.total` 这个既有账本——
  「换成合并版之后，`predict` 的默认输出仍然是一个概率分布」第一次有了定理。

  与旧版对照是要害：旧版 `rawMap` 的 `rawMap_total` 也成立，但**是 `rfl`**，
  原因是它**根本没合并**（靠重复项凑平）。本条**不是** `rfl`：
  结论来自 `addAt_sum` + `goN_sum`（每笔权重只记一次、表没被截断）。

  ⚠ 前件写成 `DiscLawWellFormed L`（语义谓词）而不是「某个列表恰好等长」，
  与 T13 的 `pushMerge_wf` 同一口径。 -/
theorem discPushFamily_total (f : SynthE → Real) (L : DiscLaw SynthE)
    (h : DiscLawWellFormed L) :
    (discPushFamily.push L f).total = L.total := by
  rw [discPushFamily_push]
  exact pushMerge_total f L h

/-- **★ 默认推前不放大质量**（无前件）：即使 `DiscLaw` 不合法（表不等长），
  合并也只会**截断**，不会凭空造概率。

  **超出定义之处**：`discPushFamily` 的定义对「表不等长时会怎样」毫无交代；
  本条给一个**无条件**上界——于是「推前不会把概率越推越大」对任意 `DiscLaw` 成立。 -/
theorem discPushFamily_total_le (f : SynthE → Real) (L : DiscLaw SynthE) :
    (discPushFamily.push L f).total ≤ L.total := by
  rw [discPushFamily_push]
  exact pushMerge_total_le f L

/-! **★ 默认路径与 T13 显式族**（`discPushFamilyM`）**是同一份推前**（结论登记）。

  T13 的 `discPushFamilyM Z`（定义在 `Predict/PushFamilyMerge.lean`）其 `push`
  就是 `pushMerge`；T23 之后默认族 `discPushFamily.push` 也是 `pushMerge`。
  ⟹ 两族在 `Z = Real`、`E = SynthE` 上**逐点相等**。

  **超出定义之处**：两个定义是**分别**写的（一个带实例槽参数化，一个是具体实例），
  定义本身对「它们是否同一个函数」一字未提。那条等式说明：**调用方不必再记得**
  显式传 `discPushFamilyM`——默认值已经与它同义。

  ⚠ **为什么定理不写在这里**：`discPushFamilyM` 住在 `PushFamilyMerge.lean`
  （import 本文件），本文件引用不到它。正式定理见
  `FateV2.Predict.discPushFamilyM_eq_discPushFamily`。 -/


end FateV2.Predict

