import FateWorld.FateV2.Core.DeclGraph

/-!
  # Core · 混合 kind 下的失效传播（专项 T7）

  ## 迁移登记
  - 来源：新写（承接 `FateV2/Core/DeclGraph.lean` 主定理 2 的尾项 3）
  - 动作：C 重写（`DeclGraph` 的主定理 2 只对「全 `defn` 图」成立，本文件给混合 kind 版）
  - 对应环节：IR 语言化（D 类）第 6 项续
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：新建；只读引用 `Core/Decl.lean`、`Core/DeclGraph.lean`
  - 状态：已编译未验证

  ## 一句话问题

  > `invalidate g k bk` 在**真实（混合 kind）**声明图上究竟等于什么？

  ## 核心洞察

  `DeclGraph.invalidate` 的定义

  ```lean
  def invalidate (g) (k) (bk) := (dependents g k).filter (fun d => spreads d.kind bk)
  ```

  **本来就是逐条下游的 kind 判的**（`spreads d.kind bk`，`d.kind` 是每条声明自己的
  kind）。所以「混合 kind」不是定义要改的东西：`invalidate_mixed_is_invalidate`
  证明本文件引入的 `invalidateMixed` 与 `invalidate` **是同一个函数**（`rfl`）。

  真正缺的从来不是定义，而是**等式刻画**。`DeclGraph.invalidate_body_of_defn`
  之所以要求「全图 `defn`」，只因为那条定理要证的右边是裸的 `dependents g k`
  （不含 kind 过滤）。把右边换成「按 kind 分桶的下游」之后，强假设就消失了 ——
  见 `invalidateMixed_body_eq_expanding_dependents`。

  ## ⚠ 与 `DeclGraph.lean` 头注释的两处实测冲突（必须登记）

  1. `DeclGraph.lean` 头注释说「自己写 `| [] => … | x :: xs => …` 就能展开
     `List.filter`」。**当前 toolchain（`leanprover/lean4:v4.33.0-rc1`）上不成立。**

     `List.filter` 的编译形态是

     ```
     fun {α} p x => List.brecOn x (List.filter._f p)
     List.filter._f p (a :: as) ih := match p a with | true => a :: ih.1 | false => ih.1
     ```

     `dsimp only [List.filter]` 之后目标里剩下的是
     `List.filter.match_1 (fun x => List α) (p a) (fun _ => a :: filter p as) (fun _ => filter p as)`
     —— 归约点是**对 `p a : Bool` 的 `match`**：`p a` 不是构造子时整个 `filter`
     是 stuck 的。`DeclGraph.filter_eq_nil` 里的 `List.filter_cons_of_neg` 能用，
     是因为它**显式要求** `p b = false`。

  2. `#print axioms List.filter_eq_self` = `[propext, Quot.sound]`（本机实测）。
     `DeclGraph.lean` 的 `filter_eq_self` 是**自证版**，用它是安全的；库版不是。

  ⟹ 本文件**不用 `List.filter` 证明任何列表结论**，而是并行列地维护两个自写的
  结构递归函数 `filterH`（值版本）与 `filterHs`（带成员规格的版本，
  二者在 `mutual` 块里互相调用），证明
  * `filterHs` 的完整成员刻画（双向，`mem_filterHs_iff`）；
  * `filterH = List.filter`（`filterH_eq_filter`，唯一一处触碰 `List.filter`
    内部结构）。

  于是本文件的一切结论都是关于**库函数 `invalidate`** 的，而**证明过程不依赖**
  `List.filter` 的归约行为。

  ## ⚠ 第二处实测陷阱：`mutual` 定义的展开点

  `filterHs` 的一步展开**不能用「对 `l : List α` 做策略式 `induction`，再
  `rw [filterHs_cons] at h`」的方式**——实测里 `induction` 之后 `rw` 会把
  `p b` 反归约成 `p a` / `p []` 之类（tactic state 被写坏，报
  `Unknown identifier b`）。**可靠写法**是：

  * 结构递归（`| b :: bs, … => …` / `fixed-index` 归纳式）里的分支直接 `rw`，
    命中率正常；
  * 需要「对 `l` 归纳 + 中途 `by_cases`」时，**先对 `l` 分一次构造子
    （`cases` 或递归），把 `by_cases` 放在已经知道表头的分支里**。

  本文件的所有引理都按这两条写。

  ## 证明纪律（核内零公理）

  * 反证一律写成「`P → False` 直接给 `¬P`」，或用 `cases` 消解构造子冲突；
  * 不用 `simp`；只用 `rfl` / `rw` / `unfold` / `dsimp only` / `cases` / `subst`；
  * 不用 `List.mem_cons` / `List.nodup_cons` / `Nat.lt_one_iff`（带 `propext`）；
  * 不写并列模式 `match a, b`、不用 `funext`、不用 `decide` / `omega` / `List.sum`；
  * 分 kind 讨论一律**逐构造子穷举**（`DeclKind` 共 8 个），不用 `DecidableEq`；
  * 逐条 `#print axioms` 实测为空（见 `_报告/T7-进度.md` §5）。
-/

namespace FateV2.Core

namespace InvalidateMixed

universe u

/-! ## §1 传播函数化：`propagatesOn` -/

/-- **`bk` 这一类变化会触发失效的那些 kind**。

    这是 `Decl.spreads` 的**换序版**（kind 挪到第二个参数），使调用点读起来是
    `propagatesOn bk d.kind`。

    ⚠ 比定义多说了什么：`spreads` 已在 `Decl.lean` 定好，这里只换参数顺序而
    **不改语义**——`propagatesOn_eq_spreads` 证明它对一切 `bk, k` 相等（`rfl`）。 -/
def propagatesOn (bk : BodyKind) (k : DeclKind) : Bool := spreads k bk

/-- `propagatesOn` 与 `spreads` 是同一个函数（只换了参数顺序）。`rfl`。 -/
theorem propagatesOn_eq_spreads (bk : BodyKind) (k : DeclKind) :
    propagatesOn bk k = spreads k bk := rfl

/-! ## §2 核心洞察：`invalidate` 本来就是混合 kind 的 -/

/-- **混合 kind 下的失效集合**：只保留**会传播**的那些下游。

    与 `DeclGraph.invalidate` 是同一个表达式（见 `invalidate_mixed_is_invalidate`），
    存在的意义是把「按下游 kind 过滤」这一步显式命名出来。 -/
def invalidateMixed {K : Type u} [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) :
    List (Decl K) :=
  (DeclGraph.dependents g k).filter (fun d => spreads d.kind bk)

/-- **【本专项最关键的洞察】`invalidateMixed` 就是 `invalidate`。**

    比定义多说了什么：两个名字背后必须是**同一个 `filter`**——同样的依赖集合、
    同样的谓词、同样的参数顺序。这不是「换个写法重证一遍」，而是把
    「`invalidate` 本来就是混合 kind 的」**变成一条可检查的定理**：于是
    `invalidate_body_of_defn` 的 `hall` 强假设只能归因于**它要证的等式**
    （右边是裸的 `dependents`），不能归因于定义。`rfl` 通过。 -/
theorem invalidate_mixed_is_invalidate {K : Type u} [DecidableEq K] (g : DeclGraph K) (k : K)
    (bk : BodyKind) : invalidateMixed g k bk = DeclGraph.invalidate g k bk := rfl

/-- 反向的同一事实（给「从左往右改写成 `invalidateMixed`」的场合用）。 -/
theorem invalidate_is_invalidateMixed {K : Type u} [DecidableEq K] (g : DeclGraph K) (k : K)
    (bk : BodyKind) : DeclGraph.invalidate g k bk = invalidateMixed g k bk := rfl

/-! ## §3 不依赖 `List.filter` 的纯结构递归工具

  `filterH` / `filterHs` 是**同一趟递归的两个视角**，放在 `mutual` 块里：
  `filterH` 是值版本（行为同 `List.filter`，但对**任意** `Bool` 谓词都能按
  `[]` / `a :: as` 展开），`filterHs` 是带成员规格的版本
  （`a ∈ filterHs p l ↔ a ∈ l ∧ p a = true`）。
  `filterH` 的一步递归直接落到 `filterHs`——把「过滤结果」与「过滤规格」
  在**定义层**对齐，而不是事后用引理去凑。 -/

mutual
/-- 值版本的结构递归过滤（`List.filter` 的可展开等价物）。 -/
def filterH {α : Type u} (p : α → Bool) : List α → List α
  | [] => []
  | a :: as =>
      match p a with
      | true => a :: filterHs p as
      | false => filterHs p as

/-- 规格版本：`a ∈ filterHs p l ↔ a ∈ l ∧ p a = true`。 -/
def filterHs {α : Type u} (p : α → Bool) : List α → List α
  | [] => []
  | a :: as =>
      match p a with
      | true => a :: filterHs p as
      | false => filterHs p as
end

/-- **`filterHs` 的一步递归（显式 `match` 形态）。**

    比定义多说了什么：把 `mutual` 生成的方程引理**固定成一条可 `rw` 的等式**，
    后续所有引理只经它走。 -/
theorem filterHs_cons {α : Type u} (p : α → Bool) (a : α) (as : List α) :
    filterHs p (a :: as)
      = (match p a with
         | true => a :: filterHs p as
         | false => filterHs p as) := rfl

/-- 表头谓词为 `true` 时的一步展开（`rw` 版，`match` 已走出去）。 -/
theorem filterHs_cons_of_true {α : Type u} (p : α → Bool) (a : α) (as : List α)
    (h : p a = true) : filterHs p (a :: as) = a :: filterHs p as := by
  rw [filterHs_cons, h]

/-- 表头谓词为 `false` 时的一步展开。 -/
theorem filterHs_cons_of_false {α : Type u} (p : α → Bool) (a : α) (as : List α)
    (h : p a = false) : filterHs p (a :: as) = filterHs p as := by
  rw [filterHs_cons, h]

/-- `filterH` 与 `filterHs` 处处相等（`rfl`）：值版本与规格版本是同一趟递归。

    比定义多说了什么：两个函数在 `mutual` 里**分别声明**，本条钉住
    「`filterH` 的递归只经 `filterHs`」，于是 `filterH` 的一切结论都能先换成
    `filterHs`、用规格引理算完再换回来。 -/
theorem filterH_eq_filterHs {α : Type u} (p : α → Bool) :
    ∀ (l : List α), filterH p l = filterHs p l
  | [] => rfl
  | a :: as => by
      cases hp : p a with
      | true => rfl
      | false => rfl

/-! ### §3.1 `filterHs` 的规格引理

  ⚠ 写法纪律（全部经受控实验确认，见 `_报告/T7-进度.md` §4）：

  * `filterHs_cons` 的 `rw` **只能作用在右侧是构造子写法的 `match` 上**
    （`filterHs_cons_of_true` / `filterHs_cons_of_false`），不能直接
    `rw [filterHs_cons]` 再 `rw [hp]`——后者在 `match` 已经吃到 `p b` 之后
    会把 `p b` 反消掉，产生 `Unknown identifier b`。
  * `match` 出现在**归纳式/结构递归**目标时，不要走 `suffices` /
    `have : P ↔ match …` 这类把 `match` 提出来写的形式（实测会带
    三公理）；保持在目标或假设里，用 `cases hp : p b` 消掉即可。
  * 空表分支用 `nomatch`（`a ∈ filterHs p []` 在定义上就是 `a ∈ []`）。 -/

/-- **留下 ⟹ 分解成「表头」或「尾部留下」**。 -/
theorem mem_filterHs_cons_or {α : Type u} (p : α → Bool) (b : α) (bs : List α) :
    ∀ {a : α}, a ∈ filterHs p (b :: bs) → a = b ∨ a ∈ filterHs p bs := by
  intro a h
  cases hp : p b with
  | true =>
      rw [filterHs_cons_of_true p b bs hp] at h
      cases h with
      | head => exact Or.inl rfl
      | tail _ h' => exact Or.inr h'
  | false =>
      rw [filterHs_cons_of_false p b bs hp] at h
      exact Or.inr h

/-- **`filterHs` 留下的元素一定在表里**（正向成员刻画）。

    比定义多说了什么：定义只说「怎么算」，本条说「算出来的每个元素都是原表元素」
    ——这是 §7 上界证明的唯一来源。 -/
theorem mem_of_filterHs {α : Type u} (p : α → Bool) :
    ∀ {l : List α} {a : α}, a ∈ filterHs p l → a ∈ l
  | [], _, h => h
  | b :: bs, a, h => by
      cases hp : p b with
      | true =>
          rw [filterHs_cons_of_true p b bs hp] at h
          cases h with
          | head => exact List.Mem.head _
          | tail _ h' => exact List.Mem.tail b (mem_of_filterHs p h')
      | false =>
          rw [filterHs_cons_of_false p b bs hp] at h
          exact List.Mem.tail b (mem_of_filterHs p h)

/-- **留下的元素谓词必为 `true`**（反向取值刻画）。

    比定义多说了什么：这是「按 kind 分桶不会漏桶」的来源。 -/
theorem prop_of_mem_filterHs {α : Type u} (p : α → Bool) :
    ∀ {l : List α} {a : α}, a ∈ filterHs p l → p a = true
  | [], a, h => nomatch h
  | b :: bs, a, h => by
      cases hp : p b with
      | true =>
          rw [filterHs_cons_of_true p b bs hp] at h
          cases h with
          | head => exact hp
          | tail _ h' => exact prop_of_mem_filterHs p h'
      | false =>
          rw [filterHs_cons_of_false p b bs hp] at h
          exact prop_of_mem_filterHs p h

/-- **谓词为真且在原表里 ⟹ 一定被留下**（反向成员刻画，即 `mem_filterHs_iff` 的另一半）。

    比定义多说了什么：定义只给「丢什么」，本条给「**不**丢什么」——
    这正是「按 kind 分桶不漏桶」的形式化。需要先看表头谓词
    （`cases p b`），再看 `a` 与表头是否相等（`cases a ∈ b :: bs`），
    **两步的顺序不能反**：先分等号会让 `p a` 与 `p b` 无法对齐。 -/
theorem mem_filterHs_of_mem {α : Type u} (p : α → Bool) :
    ∀ {l : List α} {a : α}, (a ∈ l ∧ p a = true) → a ∈ filterHs p l
  | [], a, h => nomatch h.1
  | b :: bs, a, h => by
      have habs : a ∈ bs ∨ a = b := by
        cases h.1 with
        | head => exact Or.inr rfl
        | tail _ h' => exact Or.inl h'
      cases hp : p b with
      | true =>
          rw [filterHs_cons_of_true p b bs hp]
          cases habs with
          | inl h' => exact List.Mem.tail b (mem_filterHs_of_mem p ⟨h', h.2⟩)
          | inr h' => subst h'; exact List.Mem.head _
      | false =>
          rw [filterHs_cons_of_false p b bs hp]
          cases habs with
          | inl h' => exact mem_filterHs_of_mem p ⟨h', h.2⟩
          | inr h' => subst h'
                      exact absurd h.2 (by rw [hp]; intro hh; exact Bool.noConfusion hh)

/-- **【过滤的完整规格】`a ∈ filterHs p l ↔ a ∈ l ∧ p a = true`。**

    比定义多说了什么：前三条各占一瓣，本条把它们合成**一个双向判定**，
    供 §7 的下界证明一处用到。 -/
theorem mem_filterHs_iff {α : Type u} (p : α → Bool) {l : List α} {a : α} :
    a ∈ filterHs p l ↔ (a ∈ l ∧ p a = true) :=
  ⟨fun h => ⟨mem_of_filterHs p h, prop_of_mem_filterHs p h⟩,
   fun h => mem_filterHs_of_mem p h⟩

/-- **全是 `false` 的谓词 ⟹ 过滤结果为空**。 -/
theorem filterHs_eq_nil {α : Type u} (p : α → Bool) :
    ∀ (l : List α), (∀ a, a ∈ l → p a = false) → filterHs p l = []
  | [], _ => rfl
  | b :: bs, h => by
      have hb : p b = false := h b (List.Mem.head _)
      rw [filterHs_cons_of_false p b bs hb]
      exact filterHs_eq_nil p bs (fun a ha => h a (List.Mem.tail _ ha))

/-- **全 `true` 的谓词 ⟹ 过滤不改表**。 -/
theorem filterHs_eq_self {α : Type u} (p : α → Bool) :
    ∀ (l : List α), (∀ a, a ∈ l → p a = true) → filterHs p l = l
  | [], _ => rfl
  | b :: bs, h => by
      have hb : p b = true := h b (List.Mem.head _)
      rw [filterHs_cons_of_true p b bs hb,
          filterHs_eq_self p bs (fun a ha => h a (List.Mem.tail _ ha))]

/-- **逐点相等的谓词给出相同的过滤结果**（代替 `funext`：只要求列表上逐点相等）。 -/
theorem filterHs_congr {α : Type u} (p q : α → Bool) (h : ∀ a, p a = q a) :
    ∀ (l : List α), filterHs p l = filterHs q l
  | [] => rfl
  | b :: bs => by
      rw [filterHs_cons p b bs, filterHs_cons q b bs, h b, filterHs_congr p q h bs]

/-! ### §3.2 `filterHs` 与库的 `List.filter` 一致（唯一一处触碰 `List.filter` 内部） -/

/-- **`List.filter` 的一步展开（表头谓词为 `true`）。**

    比定义多说了什么：把「库函数 `filter` 在什么条件下能往前走一步」
    **显式写成前提**（`h : p a = true`），而不是假装 `rfl` 就能展开
    （`DeclGraph.lean` 头注释的说法在当前 toolchain 上不成立）。

    实现上：`dsimp only [List.filter]` 把目标化成
    `List.filter.match_1 … (p a) …`，此时归约点是 `p a`；`rw [h]` 把它换成 `true`
    后 `match` 的 ι 归约才会发生（`dsimp only` 不展开 propext 类「套」，实测零公理）。 -/
theorem list_filter_cons_true {α : Type u} (p : α → Bool) (a : α) (as : List α)
    (h : p a = true) : List.filter p (a :: as) = a :: List.filter p as := by
  dsimp only [List.filter]
  rw [h]

/-- **`List.filter` 的一步展开（表头谓词为 `false`）**。 -/
theorem list_filter_cons_false {α : Type u} (p : α → Bool) (a : α) (as : List α)
    (h : p a = false) : List.filter p (a :: as) = List.filter p as := by
  dsimp only [List.filter]
  rw [h]

/-- **【桥】`filterH` 就是库的 `List.filter`。**

    比定义多说了什么：`filterH` 是本文件为「可展开」而手写的，本条把它钉回
    **库函数**——于是本文件关于 `filterH` / `filterHs` 的一切结论
    （上界、下界、精确形式、严格性）都自动是关于 `invalidate`
    （它用的正是 `List.filter`）的结论，而**证明本身不依赖 `List.filter` 的
    归约行为**（只在 `list_filter_cons_*` 两条上触碰它一次）。 -/
theorem filterH_eq_filter {α : Type u} (p : α → Bool) :
    ∀ (l : List α), filterH p l = List.filter p l
  | [] => rfl
  | a :: as => by
      cases hp : p a with
      | true =>
          have h1 : filterH p (a :: as) = a :: filterHs p as := by
            rw [show filterH p (a :: as) = filterHs p (a :: as) from
              filterH_eq_filterHs p (a :: as)]
            rw [filterHs_cons_of_true p a as hp]
          have h2 : filterHs p as = List.filter p as := by
            rw [← filterH_eq_filterHs p as]
            exact filterH_eq_filter p as
          rw [h1, h2, list_filter_cons_true p a as hp]
      | false =>
          have h1 : filterH p (a :: as) = filterHs p as := by
            rw [show filterH p (a :: as) = filterHs p (a :: as) from
              filterH_eq_filterHs p (a :: as)]
            rw [filterHs_cons_of_false p a as hp]
          have h2 : filterHs p as = List.filter p as := by
            rw [← filterH_eq_filterHs p as]
            exact filterH_eq_filter p as
          rw [h1, h2, list_filter_cons_false p a as hp]

/-- `filterHs` 也与库的 `filter` 一致（上面两条接力）。 -/
theorem filterHs_eq_filter {α : Type u} (p : α → Bool) (l : List α) :
    filterHs p l = List.filter p l := by
  rw [← filterH_eq_filterHs p l]
  exact filterH_eq_filter p l

/-! ## §4 按 kind 分桶 -/

/-- **`DeclKind` 自反的 `beq` 为 `true`**（逐构造子，零公理）。 -/
theorem declKind_beq_self (kd : DeclKind) : (kd == kd) = true :=
  match kd with
  | .theorem => rfl
  | .defn => rfl
  | .abbrev => rfl
  | .opaque => rfl
  | .axiom => rfl
  | .inductive => rfl
  | .ctor => rfl
  | .recC => rfl

/-- **`DeclKind` 的成员判定（自写、零公理）**：`kindMemAux kd ks` = 「`kd` 在 `ks` 里」。

    ⚠ 本文件实测的三条陷阱（见 `_报告/T7-进度.md` §4）：

    1. **不用 `decide (kd ∈ ks)`**：`List.Mem` 的 `Decidable` 实例经
       `decidable_of_iff`，`#print axioms` = `[propext]`。
    2. **不写并列模式 `match kd, k with`**：实测 `[propext]`（红线表已列）。
    3. **不写构造子模式 `| .defn :: _ => true`**：**这条是本专项新发现的**——
       只要「在一个 `inductive` 上按构造子做模式匹配」，编译出的匹配子就会
       走到 `propext`（`Nat` 的 `| 0 :: _` 不带，但 `DeclKind` 的 `| .defn :: _` 带）。

    ⟹ 唯一实测零公理的写法是**用派生的 `BEq` 逐元素比**（`kd == k`），
    配一条 `declKind_beq_self` 收尾。 -/
def kindMemAux (kd : DeclKind) (ks : List DeclKind) : Bool :=
  match ks with
  | [] => false
  | k :: ks => (kd == k) || kindMemAux kd ks

/-- `kindMemAux` 对自己作为表头的表给出 `true`（供 `dependentsOfKind` 用）。 -/
theorem kindMemAux_cons_self (kd : DeclKind) (ks : List DeclKind) :
    kindMemAux kd (kd :: ks) = true := by
  unfold kindMemAux
  rw [declKind_beq_self kd]
  rfl

/-- **`DeclKind` 的成员判定**（对外的名字）。 -/
def kindMem (kd : DeclKind) (ks : List DeclKind) : Bool := kindMemAux kd ks

/-- `kindMem` 对自己的表头给出 `true`。 -/
theorem kindMem_cons_self (kd : DeclKind) (ks : List DeclKind) :
    kindMem kd (kd :: ks) = true :=
  kindMemAux_cons_self kd ks

/-- **按 kind 分桶**：只留 `kind` 落在 `ks` 里的下游。

    这是「把下游分成会传播的与不传播的」的形式化；
    `ks` 取「`bk` 上传播的 kind 全表」时，返回的就是失效集合。 -/
def dependentsOfKind {K : Type u} [DecidableEq K] (g : DeclGraph K) (k : K)
    (ks : List DeclKind) : List (Decl K) :=
  filterHs (fun d => match d.kind with
                     | .theorem => kindMem .theorem ks
                     | .defn => kindMem .defn ks
                     | .abbrev => kindMem .abbrev ks
                     | .opaque => kindMem .opaque ks
                     | .axiom => kindMem .axiom ks
                     | .inductive => kindMem .inductive ks
                     | .ctor => kindMem .ctor ks
                     | .recC => kindMem .recC ks)
    (DeclGraph.dependents g k)

/-- `dependentsOfKind` 的谓词对每一条声明逐点就是 `kindMem d.kind ks`。 -/
theorem dependentsOfKind_pred (d : Decl K) (ks : List DeclKind) :
    (match d.kind with
     | .theorem => kindMem .theorem ks
     | .defn => kindMem .defn ks
     | .abbrev => kindMem .abbrev ks
     | .opaque => kindMem .opaque ks
     | .axiom => kindMem .axiom ks
     | .inductive => kindMem .inductive ks
     | .ctor => kindMem .ctor ks
     | .recC => kindMem .recC ks) = kindMem d.kind ks := by
  cases hk : d.kind <;> rfl

/-- **单桶版**：`kind = kd` 的那些下游。 -/
def dependentsOfKindOne {K : Type u} [DecidableEq K] (g : DeclGraph K) (k : K) (kd : DeclKind) :
    List (Decl K) :=
  dependentsOfKind g k [kd]

/-- **全 `defn` 的特化：单桶 `defn` 恰好是全部下游。**

    比定义多说了什么：`filterHs` 的谓词在 `d.kind = .defn` 上恒为 `true`
    （`kindMem_cons_self`），于是过滤不改表。这条把本文件的「分桶」与
    `DeclGraph` 的 `dependents` 对上号，是定理 D 特化的落脚点。 -/
theorem dependentsOfKindOne_defn_eq_dependents {K : Type u} [DecidableEq K] (g : DeclGraph K)
    (k : K) (hall : ∀ d ∈ g, d.kind = .defn) :
    dependentsOfKindOne g k .defn = DeclGraph.dependents g k := by
  unfold dependentsOfKindOne dependentsOfKind
  refine filterHs_eq_self _ _ ?_
  intro d hd
  have hgd : d ∈ g := by
    unfold DeclGraph.dependents at hd
    exact DeclGraph.mem_of_filter (fun d => d.dependsOn k) hd
  rw [hall d hgd]
  exact kindMem_cons_self .defn []

/-! ## §5 三个 `bk` 行的精确形式（都不要求全 `defn`） -/

/-- **【定理 A】`invalidateMixed` 可以改写成 `filterHs` 版**——把库的 `filter`
    换成可展开的 `filterHs`，从而后文所有结论只经 `filterHs` 的规格引理。

    比定义多说了什么：定义用的是库 `List.filter`，它在 `p a` 未归约时是 stuck
    的（本文件头注释第 1 条）；本条说明**可以换成手写的 `filterHs` 而不改语义**
    ——这是 §3.2 那座桥的反方向用法，也是 §5～§7 全部证明的入口。 -/
theorem invalidateMixed_eq_filterHs {K : Type u} [DecidableEq K] (g : DeclGraph K) (k : K)
    (bk : BodyKind) :
    invalidateMixed g k bk
      = filterHs (fun (d : Decl K) => spreads d.kind bk) (DeclGraph.dependents g k) := by
  unfold invalidateMixed
  exact (filterHs_eq_filter (fun (d : Decl K) => spreads d.kind bk)
    (DeclGraph.dependents g k)).symm

/-- **【定理 B・主定理 1 的一般化】对任何混合 kind，改证明体 ⟹ 失效为空。**

    比定义多说了什么：`DeclGraph.invalidate_proof_nil` 是它的特例；
    本条把「为什么」摊开：失效集合是「用 `spreads · .proof` 过滤全部下游」，
    而 `spreads_proof_false` 说这一行对**一切** kind 为 `false`，于是整表筛空。
    **与图里有哪些 kind 完全无关**——这正是「全 `defn` 假设」在 `.proof` 行上
    多余的原因。 -/
theorem invalidateMixed_proof_nil {K : Type u} [DecidableEq K] (g : DeclGraph K) (k : K) :
    invalidateMixed g k .proof = [] := by
  rw [invalidateMixed_eq_filterHs]
  exact filterHs_eq_nil (fun (d : Decl K) => spreads d.kind .proof) _
    (fun (d : Decl K) _ => DeclGraph.spreads_proof_false d.kind)

/-- 同一事实的混合 kind 记号（与 `DeclGraph` 的结论一致）。 -/
theorem invalidate_proof_nil_mixed {K : Type u} [DecidableEq K] (g : DeclGraph K) (k : K) :
    invalidateMixed g k .proof = DeclGraph.invalidate g k .proof := by
  rw [invalidate_mixed_is_invalidate, DeclGraph.invalidate_proof_nil]

/-- **【定理 C】改签名 ⟹ 失效 = 全部下游（与 kind 无关）。**

    比定义多说了什么：`DeclGraph.invalidate_signature_eq_dependents` 已给这条
    （靠 `spreads_signature : ∀ k, spreads k .signature = true`）。
    本条**从 `invalidateMixed`（本文件的混合 kind 写法）重推一遍**，
    钉住「本文件的 `filterHs` 路线与 `DeclGraph` 的 `filter` 路线给出同一答案」
    ——这是 §3.2 那座桥的第一次实战检验。 -/
theorem invalidateMixed_signature_eq_dependents {K : Type u} [DecidableEq K] (g : DeclGraph K)
    (k : K) : invalidateMixed g k .signature = DeclGraph.dependents g k := by
  rw [invalidateMixed_eq_filterHs]
  exact filterHs_eq_self (fun (d : Decl K) => spreads d.kind .signature) _
    (fun (d : Decl K) _ => spreads_signature d.kind)

/-- **扩展区变化 ⟹ 失效为空**（对任何混合 kind）。 -/
theorem invalidateMixed_metadata_nil {K : Type u} [DecidableEq K] (g : DeclGraph K) (k : K) :
    invalidateMixed g k .metadata = [] := by
  rw [invalidateMixed_eq_filterHs]
  exact filterHs_eq_nil (fun (d : Decl K) => spreads d.kind .metadata) _
    (fun (d : Decl K) _ => spreads_metadata d.kind)

/-- **`spreadsOn` 的真值集恰好是 `defn` / `abbrev` / `recC`。**

    比定义多说了什么：`spreadsOn` 是一条**函数**，本条给出它的**值域刻画**
    ——`true` 只落在三个点上。需要把 `DeclKind` 的 8 个构造子逐个检验，
    不靠 `decide`、不靠 `DecidableEq`（二者都带 `propext`）。
    这是定理 D 的全部算术内容：`invalidateMixed g k .body` 到底是哪几桶。 -/
theorem spreadsOn_eq_true_iff (kd : DeclKind) :
    spreadsOn kd = true ↔ (kd = .defn ∨ kd = .abbrev ∨ kd = .recC) :=
  match kd with
  | .theorem => Iff.intro (fun h => nomatch h) (fun h => by
      rcases h with h1 | h1 | h1
      · exact nomatch h1
      · exact nomatch h1
      · exact nomatch h1)
  | .defn => Iff.intro (fun _ => Or.inl rfl) (fun _ => rfl)
  | .abbrev => Iff.intro (fun _ => Or.inr (Or.inl rfl)) (fun _ => rfl)
  | .opaque => Iff.intro (fun h => nomatch h) (fun h => by
      rcases h with h1 | h1 | h1
      · exact nomatch h1
      · exact nomatch h1
      · exact nomatch h1)
  | .axiom => Iff.intro (fun h => nomatch h) (fun h => by
      rcases h with h1 | h1 | h1
      · exact nomatch h1
      · exact nomatch h1
      · exact nomatch h1)
  | .inductive => Iff.intro (fun h => nomatch h) (fun h => by
      rcases h with h1 | h1 | h1
      · exact nomatch h1
      · exact nomatch h1
      · exact nomatch h1)
  | .ctor => Iff.intro (fun h => nomatch h) (fun h => by
      rcases h with h1 | h1 | h1
      · exact nomatch h1
      · exact nomatch h1
      · exact nomatch h1)
  | .recC => Iff.intro (fun _ => Or.inr (Or.inr rfl)) (fun _ => rfl)

/-- **【定理 D】改定义体 ⟹ 失效 = `defn` / `abbrev` / `recC` 的下游之并。**

    比定义多说了什么：**这才是 `DeclGraph.invalidate_body_of_defn` 的真面目。**
    那条定理写的是 `invalidate g k .body = dependents g k`，所以不得不假设
    「全图 `defn`」；本条把右边换成按 kind 分桶的
    `dependentsOfKind g k [.defn, .abbrev, .recC]`，**假设完全消失**。

    尾巴里的 `abbrev` 与 `recC` 不是笔误：`Decl.lean` 的 `spreadsOn` 让它们与
    `defn` 一样传播（δ 展开）。所以「改定义体 ⟹ 全部下游」只在
    「全图 `defn`」时成立（`invalidateMixed_body_eq_dependents_of_defn` 给这条
    特化），而真实图里 `abbrev` / `recC` 下游**同样会脏**。 -/
theorem invalidateMixed_body_eq_expanding_dependents {K : Type u} [DecidableEq K]
    (g : DeclGraph K) (k : K) :
    invalidateMixed g k .body = dependentsOfKind g k [.defn, .abbrev, .recC] := by
  have hpw : ∀ (d : Decl K), spreads d.kind .body = spreadsOn d.kind := fun d => by
    cases hk : d.kind <;> rfl
  rw [invalidateMixed_eq_filterHs]
  unfold dependentsOfKind
  rw [filterHs_congr
    (fun (d : Decl K) => spreads d.kind .body)
    (fun (d : Decl K) => match d.kind with
              | .theorem => kindMem .theorem [DeclKind.defn, .abbrev, .recC]
              | .defn => kindMem .defn [DeclKind.defn, .abbrev, .recC]
              | .abbrev => kindMem .abbrev [DeclKind.defn, .abbrev, .recC]
              | .opaque => kindMem .opaque [DeclKind.defn, .abbrev, .recC]
              | .axiom => kindMem .axiom [DeclKind.defn, .abbrev, .recC]
              | .inductive => kindMem .inductive [DeclKind.defn, .abbrev, .recC]
              | .ctor => kindMem .ctor [DeclKind.defn, .abbrev, .recC]
              | .recC => kindMem .recC [DeclKind.defn, .abbrev, .recC])
    (fun d => by
      rw [hpw d, dependentsOfKind_pred d [DeclKind.defn, .abbrev, .recC]]
      cases hk : d.kind <;> rfl)
    (DeclGraph.dependents g k)]

/-! ## §7 上界、下界与严格性（全部不要求全 `defn`） -/

/-- **【上界】`invalidateMixed` ⊆ `dependents`（对一切混合 kind）。**

    比定义多说了什么：`DeclGraph.invalidate_subset_dependents` 已给这条，但它
    依赖 `DeclGraph.mem_of_filter` 里对 `List.filter` 的展开；本条用
    `filterHs` 的成员刻画重证，说明「不凭空脏」这件事**不经 `List.filter`
    的归约行为**也能得到，并把结论搬到 `invalidateMixed` 这个新名字上。 -/
theorem invalidateMixed_subset_dependents {K : Type u} [DecidableEq K] (g : DeclGraph K)
    (k : K) (bk : BodyKind) :
    ∀ d ∈ invalidateMixed g k bk, d ∈ DeclGraph.dependents g k := by
  rw [invalidateMixed_eq_filterHs]
  intro d hd
  exact mem_of_filterHs (fun (d : Decl K) => spreads d.kind bk) hd

/-- **【上界・精确版】留下的元素，其 kind 在 `bk` 行上确实传播。**

    比定义多说了什么：上一条只说「不多」，本条说「留下的**每一个**都真的传播」
    ——这正是 `prop_of_mem_filterHs` 在失效集合上的特化。 -/
theorem invalidateMixed_propagates {K : Type u} [DecidableEq K] (g : DeclGraph K) (k : K)
    (bk : BodyKind) : ∀ d ∈ invalidateMixed g k bk, spreads d.kind bk = true := by
  rw [invalidateMixed_eq_filterHs]
  intro d hd
  exact prop_of_mem_filterHs (fun (d : Decl K) => spreads d.kind bk) hd

/-- **【下界】非空失效集合的直接见证图。**

    一个 `defn` 声明 `b` 依赖 `a`（`b` 自己就在图里），于是它**同时**是
    `dependents g a` 的成员与 `invalidate g a .body` 的成员。 -/
def lowerG : DeclGraph Nat := [⟨1, .defn, .body, [0], .open_⟩]

/-- 下界见证图里的那个下游（`1 : defn`，依赖 `0`）。 -/
def lowerD : Decl Nat := ⟨1, .defn, .body, [0], .open_⟩

/-- `lowerD` 确实直接依赖 `0`（`rfl`）。 -/
theorem lowerD_dependsOn : lowerD.dependsOn 0 = true := rfl

/-- **【下界】有依赖的 `defn` 一定落在失效集合里**（构造性，给出具体成员）。

    比定义多说了什么：上界只说「不多」，本条补「不少」——而且给的是**具体元素**
    而不是「非空」。前提里**没有**任何「全图 `defn`」假设；
    §8 的 `strictG` 说明图里同时有 `axiom` 下游也不影响这个成员关系。 -/
theorem mem_invalidateMixed_body_lower : lowerD ∈ invalidateMixed lowerG 0 .body := by
  have hdep : lowerD.dependsOn 0 = true := lowerD_dependsOn
  rw [invalidateMixed_eq_filterHs]
  refine mem_filterHs_of_mem (fun (d : Decl Nat) => spreads d.kind .body) ⟨?_, ?_⟩
  · -- `lowerD ∈ dependents lowerG 0`
    have hdeps : DeclGraph.dependents lowerG 0 = [lowerD] := by
      show List.filter (fun (x : Decl Nat) => x.dependsOn 0) [lowerD] = [lowerD]
      rw [list_filter_cons_true (fun (x : Decl Nat) => x.dependsOn 0) lowerD [] hdep]
      rfl
    rw [hdeps]
    exact List.Mem.head _
  · rfl

/-- **【下界】失效集合可以非空**（存在性版本，反面是 `invalidateMixed_proof_nil`）。 -/
theorem exists_mem_invalidateMixed_body :
    ∃ (g : DeclGraph Nat) (k : Nat), ∃ d : Decl Nat, d ∈ invalidateMixed g k .body :=
  ⟨lowerG, 0, lowerD, mem_invalidateMixed_body_lower⟩

/-- **【上界 + 下界 合取】**：`invalidateMixed` 恰是 `dependents` 里「会传播」的那部分。

    比定义多说了什么：把本文件的两条边界结论（不多 / 不少）合成一条，
    并显式说明 `lowerD` 这种成员**同时**在两边的对应位置上。 -/
theorem lower_member_in_both :
    lowerD ∈ DeclGraph.dependents lowerG 0 ∧ lowerD ∈ invalidateMixed lowerG 0 .body :=
  ⟨by unfold lowerG lowerD DeclGraph.dependents; exact List.Mem.head _, mem_invalidateMixed_body_lower⟩

/-! ### 严格性的具体见证

  下面用一个**两元素**的图，说明 `invalidate g k .body` **真包含于**
  `dependents g k`：`axiom` 下游不传播。这正是 `DeclGraph.invalidate_body_of_defn`
  为什么必须加「全 `defn`」假设——图里只要出现一个 `axiom` 下游，那条假设就不成立。 -/

/-- 严格性见证图：`1 : axiom` 依赖 `0 : defn`。 -/
def strictG : DeclGraph Nat := [⟨1, .axiom, .body, [0], .open_⟩]

/-- 见证图里的那个下游（`1 : axiom`）。 -/
def strictD : Decl Nat := ⟨1, .axiom, .body, [0], .open_⟩

/-- `strictD` 确实在图里。 -/
theorem strictD_mem : strictD ∈ strictG := List.Mem.head _

/-- `strictD` 确实直接依赖 `0`。 -/
theorem strictD_dependsOn : strictD.dependsOn 0 = true := rfl

/-- `strictD` 确实在 `dependents strictG 0` 里。 -/
theorem strictD_mem_dependents : strictD ∈ DeclGraph.dependents strictG 0 := by
  unfold strictG strictD DeclGraph.dependents
  exact List.Mem.head _

/-- **【严格性】`axiom` 下游**不在**失效集合里**——这就是真包含的见证。

    比定义多说了什么：`dependents` 收了 `strictD`，而 `invalidate` 不收；
    本条把前者（`strictD_mem_dependents`）与后者（本条）配成一对，
    于是 `invalidate strictG 0 .body ≠ dependents strictG 0`。
    **结论**：`DeclGraph.invalidate_body_of_defn` 的 `hall : ∀ d ∈ g, d.kind = .defn`
    在本图上**不可省**。 -/
theorem strictD_not_mem_invalidateMixed : strictD ∉ invalidateMixed strictG 0 .body := by
  rw [invalidateMixed_eq_filterHs]
  intro h
  have hsp : spreads strictD.kind .body = true :=
    prop_of_mem_filterHs (fun (d : Decl Nat) => spreads d.kind .body) h
  exact absurd hsp (by intro hh; exact Bool.noConfusion hh)

/-- **【严格性】形式陈述：`invalidate` 真包含于 `dependents`。**

    比定义多说了什么：把「`dependents` 有、`invalidate` 没有」这件事说成
    **不等**（而不是「不相等是显然的」）：给出见证，并说明
    `dependents strictG 0` 非空而 `invalidate strictG 0 .body` 为空。 -/
theorem invalidate_body_ne_dependents_strict :
    invalidateMixed strictG 0 .body = [] ∧ DeclGraph.dependents strictG 0 = [strictD] := by
  refine ⟨?_, ?_⟩
  · have hnil : DeclGraph.dependents strictG 0 = [strictD] := by
      show List.filter (fun (x : Decl Nat) => x.dependsOn 0) [strictD] = [strictD]
      rw [list_filter_cons_true (fun (x : Decl Nat) => x.dependsOn 0) strictD []
        (by rfl)]
      rfl
    rw [invalidateMixed_eq_filterHs, hnil]
    rw [filterHs_cons_of_false (fun (d : Decl Nat) => spreads d.kind .body) strictD []
      (by rfl)]
    rfl
  · show List.filter (fun (x : Decl Nat) => x.dependsOn 0) [strictD] = [strictD]
    rw [list_filter_cons_true (fun (x : Decl Nat) => x.dependsOn 0) strictD []
      (by rfl)]
    rfl

end InvalidateMixed

end FateV2.Core
