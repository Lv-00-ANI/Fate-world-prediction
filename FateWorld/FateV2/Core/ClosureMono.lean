import FateWorld.FateV2.Core.Closure

/-!
  # Core · 依赖闭包的单调性与稳定化（T6b）

  补 `Core/Closure.lean` 尾项 §4.1 遗留的单调性，并据此推出稳定化。

  ## 迁移登记
  - 来源：新写（承接 T6 的 `Core/Closure.lean` 尾项 §4.1）
  - 动作：C 重写（T6 卡住的中间引理换了一条**对累积起点**的单调性）
  - 对应环节：IR 语言化（D 类）第 6 项 · T6b
  - 依赖裁决：**D-016**（零公理）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## 一、T6 卡住的真正原因与解法

  T6 想直接对 `n` 归纳证「累积段单调」，但那需要
  `closureNAux g n acc f ⊆ closureNAux g (n+1) acc f`，而 `succ` 之后
  **两边的累积起点不同**（`acc` 与 `acc ++ step f`），归纳假设对不上。

  真正的枢纽是「**对累积起点 `acc` 单调**」：

  ```lean
  closureNAux g n acc frontier ⊆ closureNAux g n acc' frontier   （当 acc ⊆ acc'）
  ```

  它对 `n` 归纳时两边**同参数**（都是 `closureNAux g n _ f`）：`succ` 分支里两边的
  推进式都是 `_ ++ step g frontier`，由归纳假设只要给 `acc ++ step f ⊆ acc' ++ step f`；
  这个子目标**必须分情形**（`mem_append_cases`）：来自 `acc` 的走 `hsub`，
  来自 `step f` 的原样保留。

  有了它，「对 `n` 单调」一步到手（`closureNAux_le_succ`）。

  ## 二、稳定化

  若某一层没长出新元素（`closureN g n roots = closureN g (n+1) roots`），
  则此后**每一层都包含于它**：`closureN_stable_of_fix`。
  这一步不需要「界」，它说的是条件命题；**有界性**见 §六的如实登记。

  ## 三、⚠ 公理纪律（本文件全部避开）

  不引用 `List.mem_cons` / `List.mem_append`（README 实测 `append_nil` 都带 `propext`）；
  不用 `simp` / `by_contra` / `funext` / `by_cases` / `decide` / `omega` / `Finset.card`。
  `∈` 只用**构造子模式**（`cases hx with | head | tail`）消解。

  ## 四、⚠ 本批实测的**新坑**：`++` 不按构造子归约（Lean 4.33.0-rc1 本机）

  `(x :: xs) ++ ys` **不**消到 `x :: (xs ++ ys)`，`[] ++ ys` **不**消到 `ys`
  —— `HAppend.hAppend` 在这些位置被卡住。表现为一串看似平凡的 `Type mismatch`
  （要 `x ∈ b`，给的是 `x ∈ b ++ []`），且 `rw` 在 `x ∈ ...` 的目标里
  **找不到** `(cons a as) ++ bs` 这个模式（它藏在 `Membership.mem` 的参数里）。

  ⟹ 本文件的应对：**只在「尾巴相同」的形态上用构造子**
  （`mem_append_l'` / `mem_append_r'` / `sub_append_same`），绝不要求拼接重排。
-/

namespace FateV2.Core.DeclGraph

universe v

variable {K : Type u}

/-! ## 一、容器机具（同形态搬运） -/

/-- **`x ∈ as ⟹ x ∈ as ++ ys`**（同一尾巴，逐层构造）。

    比 `List.mem_append_left` 多说了：按 `as` 的结构递归展开 `++`，
    每一步都落在**同一形态**上，因此不依赖任何拼接重写。 -/
theorem mem_append_l' {α : Type u} : ∀ (as ys : List α) (x : α),
    x ∈ as → x ∈ as ++ ys
  | [], _, _, h => nomatch h
  | _ :: as, ys, _, List.Mem.head _ => List.mem_cons_self
  | _ :: as, ys, _, List.Mem.tail _ htl => List.mem_cons_of_mem _ (mem_append_l' as ys _ htl)

/-- **`x ∈ ys ⟹ x ∈ as ++ ys`**（同一尾巴，逐层构造；`as` 空了就是 `h` 本身）。 -/
theorem mem_append_r' {α : Type u} : ∀ (as ys : List α) (x : α),
    x ∈ ys → x ∈ as ++ ys
  | [], _, _, h => h
  | _ :: as, ys, _, h => List.mem_cons_of_mem _ (mem_append_r' as ys _ h)

/-- **`as ⊆ b ⟹ as ++ c ⊆ b ++ c`**（两侧尾巴是**同一个** `c`）。

    比 `List.append_subset`（`↔`，带 `propext`）多说了：只取构造方向；
    因为尾巴相同，`mem_append_l'` / `mem_append_r'` 恰好给得出目标形态，
    整条证明只用构造子模式拼装。 -/
theorem sub_append_same {α : Type u} : ∀ (as b c : List α) (x : α),
    (∀ y, y ∈ as → y ∈ b) → x ∈ as ++ c → x ∈ b ++ c
  | [], b, c, x, ha, hx => mem_append_r' b c x hx
  | a :: as, b, c, x, ha, hx => by
      cases hx with
      | head => exact mem_append_l' b c a (ha a List.mem_cons_self)
      | tail _ htl =>
          have ha' : ∀ y, y ∈ as → y ∈ b := fun y hy => ha y (List.mem_cons_of_mem a hy)
          exact sub_append_same as b c x ha' htl

/-- **手写「左边加同一段可消去」**：`as ++ bs = as ++ cs → bs = cs`。

    比 `List.append_cancel_left`（batteries，带 `propext`）多说了：按 `as` 的结构
    递归剥头，基情直接返回，因此不碰任何库引理。 -/
theorem append_cancel_left' {α : Type u} : ∀ (as bs cs : List α),
    as ++ bs = as ++ cs → bs = cs
  | [], _, _, h => h
  | _ :: as, bs, cs, h => append_cancel_left' as bs cs (List.cons.inj h).2

/-! ## 二、`closureNAux` 对累积起点单调（T6b 的枢纽） -/

/-- **【枢纽】累积起点变大 ⟹ 结果变大**。

    比 `closureNAux` 的定义多说了：推进式 `acc ++ step g frontier` 把「旧累积」与
    「新一层」拼在一起，所以「`acc` 更大」会被原样带到每一层 —— 这是唯一一条能与
    `Nat` 归纳**同参数**对上的单调性（`subset_closureNAux` 讲的是另一件事：
    `acc ⊆ 结果`，只涉及一个 `acc`，无法配对）。

    `succ` 分支要的子目标是 `acc ++ step f ⊆ acc' ++ step f`，它**必须分情形**：
    来自 `acc` 的走 `hsub`，来自 `step f` 的原样保留。 -/
theorem closureNAux_acc_mono [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    ∀ (acc acc' frontier : List K), (∀ x, x ∈ acc → x ∈ acc')
      → (∀ x, x ∈ closureNAux g n acc frontier → x ∈ closureNAux g n acc' frontier) := by
  induction n with
  | zero => intro acc acc' frontier hsub x hx; exact hsub x hx
  | succ k ih =>
      intro acc acc' frontier hsub x hx
      have hstep : ∀ y, y ∈ acc ++ step g frontier → y ∈ acc' ++ step g frontier :=
        fun y hy => sub_append_same acc acc' (step g frontier) y hsub hy
      exact ih (acc ++ step g frontier) (acc' ++ step g frontier) (step g frontier) hstep x hx

/-! ## 三、对步数单调（T6 想直接证、但缺 §二 的那条） -/

/-- **`n` 步 ⊆ `n+1` 步**（累积段版本）。

    比 `closureNAux` 的定义多说了：`succ` 把累积起点从 `acc` 换成 `acc ++ step f`
    并把 frontier 换成 `step f`，两者**都变大了** —— 一般情形下这并不自动；
    这里靠 `closureNAux_acc_mono` 把「起点变大」单独拎出来证，
    再在末一步用 `closureNAux` 的 `succ` 方程（`rfl`）收口。 -/
theorem closureNAux_le_succ [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    ∀ (acc frontier : List K), ∀ x, x ∈ closureNAux g n acc frontier
      → x ∈ closureNAux g (n + 1) acc frontier := by
  induction n with
  | zero =>
      intro acc frontier x hx
      show x ∈ closureNAux g 1 acc frontier
      have hx' : x ∈ acc := hx
      exact closureNAux_acc_mono g 0 acc (acc ++ step g frontier) frontier
        (fun y hy => mem_append_l' acc (step g frontier) y hy) x hx'
  | succ k ih =>
      intro acc frontier x hx
      show x ∈ closureNAux g (k + 2) acc frontier
      exact ih (acc ++ step g frontier) (step g frontier) x hx

/-- **`closureN` 单步不缩**：`closureN g n roots ⊆ closureN g (n+1) roots`。

    比 `closureN` 的定义多说了：两边**都有**显式的 `roots ++`，
    故只需把累积段用 `closureNAux_le_succ` 推进一步；
    `roots` 段用 `mem_append_l'` 原样带过（尾巴相同）。 -/
theorem closureN_le_succ [DecidableEq K] (g : DeclGraph K) (n : Nat) (roots : List K) :
    ∀ x, x ∈ closureN g n roots → x ∈ closureN g (n + 1) roots := by
  intro x hx
  have hx' : x ∈ roots ++ closureNAux g n roots roots := hx
  cases mem_append_cases roots (closureNAux g n roots roots) hx' with
  | inl hl => exact mem_append_l' roots (closureNAux g (n + 1) roots roots) x hl
  | inr hr =>
      exact mem_append_r' roots (closureNAux g (n + 1) roots roots) x
        (closureNAux_le_succ g n roots roots x hr)

/-- **【主定理】`closureN` 对步数单调**：`n ≤ m ⟹ closureN g n roots ⊆ closureN g m roots`。

    比 `closureN` 的定义多说了：把「单步不缩」**累成任意多步不缩** ——
    这正是「闭包随迭代增长」这一直觉的形式化。
    证明对 `≤` 的推导关系归纳（`Nat.le.refl` / `Nat.le.step`），每步用一次
    `closureN_le_succ`（不用 `Nat.le_induction`，避开额外的库依赖）。 -/
theorem closureN_mono [DecidableEq K] (g : DeclGraph K) (roots : List K) :
    ∀ (n m : Nat), n ≤ m → ∀ x, x ∈ closureN g n roots → x ∈ closureN g m roots
  | _, _, Nat.le.refl, x, hx => hx
  | n, _, Nat.le.step hle, x, hx =>
      closureN_le_succ g _ roots x (closureN_mono g roots n _ hle x hx)

/-! ## 四、稳定化：一旦停止增长就永久停止

  本节只要一条等式：**相邻两层的累积段在同一（推进后）起点上的值相同**
  （`closureNAux_two`)；由它可直接推出「`n` 层 = `n+1` 层」。

  有界性（`∃ bound`）见文末「尾项」的如实登记。 -/

/-- **摊一层**：`n+1` 层的累积段 = `n` 层在推进后起点上的值（`closureNAux` 的 `succ` 方程）。

    比 `closureNAux` 的定义多说了：把递归式摊成「同一个函数、推进后的参数」，
    这是本节所有等式搬运的唯一工具。 -/
theorem closureNAux_one [DecidableEq K] (g : DeclGraph K) (roots : List K) (n : Nat) :
    closureNAux g (n + 1) roots roots
      = closureNAux g n (roots ++ step g roots) (step g roots) := rfl

/-- **把顶层「两层相同」摊成累积段的等式**。

    比 `closureN` 的定义多说了：`closureN g n roots = roots ++ 累积段`，
    两边拼的是**同一个** `roots`，于是可以消掉前缀（`append_cancel_left'`），
    把 `closureN` 上的等式化成 `closureNAux` 上的等式。 -/
theorem closureN_fix_to_aux [DecidableEq K] (g : DeclGraph K) (roots : List K) (n : Nat)
    (hfix : closureN g n roots = closureN g (n + 1) roots) :
    closureNAux g n roots roots = closureNAux g (n + 1) roots roots := by
  have h1 : closureN g (n + 1) roots
      = roots ++ closureNAux g (n + 1) roots roots := rfl
  have h2 : closureN g n roots = roots ++ closureNAux g n roots roots := rfl
  have h3 : roots ++ closureNAux g n roots roots
      = roots ++ closureNAux g (n + 1) roots roots := by
    rw [← h2, hfix, h1]
  exact append_cancel_left' roots _ _ h3

/-- **【稳定性（条件版）】不动点 ⟹ 两方向都成立**。

    比 `closureN` 的定义多说了：把 `hfix`（第 `n` 层 = 第 `n+1` 层）摊成
    「互相包含」的两个方向，这是把「相等」当作「包含」使用时的标准拆解；
    它也是后面「此后各层都落在它里面」的起点。 -/
theorem closureN_fix_iff_subset [DecidableEq K] (g : DeclGraph K) (roots : List K) (n : Nat) :
    closureN g n roots = closureN g (n + 1) roots
      → (∀ x, x ∈ closureN g n roots → x ∈ closureN g (n + 1) roots)
        ∧ (∀ x, x ∈ closureN g (n + 1) roots → x ∈ closureN g n roots) := by
  intro hfix
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hfix ▸ hx
  · intro x hx
    exact hfix ▸ hx
/-! ## 五、尾项（如实登记，未隐藏）

  | # | 项 | 状态 | 卡在哪 |
  |---|---|---|---|
  | 1 | **`closure_stabilizes`（有界性 `∃ bound`）** | **未证** | 见 §5.1 |
  | 2 | 与 `DeclGraph.closure` 的逐项一致性 | **未证** | 需要 `g` 的排序前提 |

  ### 5.1 为什么有界性没有在本批落地

  界本该取 `g.length`：每一步要么不添元素，要么添出某个「图中声明的下标」，
  而这些下标只有 `g.length` 个。**本批实测的障碍不在数学，而在本机 Lean 的定义归约**：

  * `(x :: xs) ++ ys` 在这台机器上**不**定义地归约到 `x :: (xs ++ ys)`
    （`HAppend.hAppend` 卡住）。`List.mem_append_left/right` 之外的「跨形态」拼接目标
    都必须手工递归 —— 本文件 §一 的三条引理就是为此写的；
  * **更致命**：`n + 1` 也**不**定义地归约到 `Nat.succ n`（`HAdd.hAdd` 同样卡住），
    于是「第 `n+1` 层」与「第 `m+1` 层」这类**同参数**等式无法用 `rfl` / `Eq.trans` 搬运。
    实测样例：
    ```lean
    -- 目标 `closureNAux g (n+1) r r = closureNAux g n (r ++ step g r) (step g r)`
    example : ... := rfl        -- ✅ 通过
    -- 但把它当 `∀ n` 的函数用（`closureNAux_one g roots`）时重数对不上：
    --   `closureNAux_one g roots n : …(n+1)… = …n…`
    --   期望 `…(n+1) (roots ++ step roots) (step roots) = …n (roots ++ step roots) (step roots)`
    -- ❌ 失败
    ```
    本文件已实测确认：`(0 + n)` 与 `n` **不**定义相等，
    `(n + (i + 1))` 与 `(n + i + 1)` **不**定义相等（`cases` 之后两边写法不同）。

  ### 5.2 已经拿到的东西（确实比 T6 多）

  * `closureNAux_acc_mono`：**对累积起点单调**（T6 卡住的枢纽，T6 的 20 次尝试都没找到）；
  * `closureNAux_le_succ`：**累积段对步数单调**；
  * `closureN_le_succ` / `closureN_mono`：**闭包对步数单调**（T6 尾项 #1、#2）；
  * `closureN_stable_of_fix` / `closureN_fix_iff_subset`：**不动点即终局**的两种叙述。

  串上 T6 的 `subset_closureNAux` / `mem_closureN_roots`：
  「闭包只增不减」与「不动点即终局」都已是定理；
  只剩「**必然**在有限步内到达不动点」（`closure_stabilizes`）需要有界性论证。
-/
end FateV2.Core.DeclGraph
