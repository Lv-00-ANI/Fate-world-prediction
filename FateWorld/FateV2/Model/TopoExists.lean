import FateWorld.FateV2.Model.OrderSource

/-!
  # Model · 拓扑序存在性（收口）

  ## 本文件回答什么

  `Order.lean`（T1）证出了**条件版**（`topo_cons_of_source`），
  `OrderSource.lean`（T1b）证出了唯一缺口（`source_exists_fin`），
  但两者**没有接上** —— T1b 报告 §5.2 把剩下的工作定位为
  `exists_topo_order_on_aux` 里 `hedge` 的 `i ≥ 1` 分支。本文件补上这一口气：

  ```lean
  theorem exists_topo_order_fin (m : Nat) (g : Graph (Fin (m + 1))) (hac : Acyclic g) :
      ∃ order : List (Fin (m + 1)), IsTopoOrder g order
  ```

  ## 与 T1 报告的直接冲突（复核结论）

  T1 报告断言「无条件存在性（`Fintype` 上无环 ⟹ 有源点）未证出」，理由是
  「它等价于鸽笼，而鸽笼的可用形态都带公理」。**后半句已被 T1b 推翻**
  （`Pigeon.length_le_of_nodup_fin` 零公理），因此该断言不成立，
  本文件即为其构造性证据。

  ## 组装路线（为什么不是 T1b 建议的 `IsTopoOrderOn` + 列表归纳）

  T1b 建议的归纳步需要 `a ∈ order'` ⟹ `a ∈ removeOne src vertices`。
  障碍是**类型上的**：`vertices : List (Fin n)` 与 `removeOne src vertices`
  的长度不同，当作同一顶点集使用就必须消去 `(w :: ws).length = ws.length + 1`，
  而 `Fin` 的依赖消去在 `cases vertices with | cons w ws` 之后失败
  （实测：`Dependent elimination failed: Failed to solve equation ws.length + 1 = n`）。

  **本文件的修法**：把顶点列表**本身**当作顶点类型 —— 对
  `vs : List (Fin n)` 使用顶点类型 `Fin vs.length`。这一步之后
  「长度」写进了类型，递归调用 `removeOne` 自动换类型，**依赖一次都不用消**。
  为此需要三条搬运（全部结构递归，零公理）：

  * `nthV`：`Fin vs.length → Fin n`（位置 → 顶点）；
  * `nthV_mem`：`nthV vs i ∈ vs`；
  * `idxOf` / `idxOf_spec`：`Fin n → Option (Fin vs.length)`（顶点 → 位置，互为逆）。

  有了它们，`vs` 上的子图（`indG`）就能直接喂给 `source_exists_fin`：
  `vs = w :: ws` 时 `Fin (w :: ws).length` 与 `Fin (ws.length + 1)` 是
  **定义性**相等（`rfl`），不需要任何改写。

  ## 公理纪律

  | 写法 | `#print axioms` |
  |---|---|
  | `by_cases h : ∃ v, P v` | `propext`;`Classical.choice`;`Quot.sound` ❗ |
  | `simp` / `decide` / `omega` | `propext` ❗ |
  | `List.mem_cons` / `List.nodup_cons` | `propext` ❗ |
  | 策略式 `cases vertices with \| cons w ws`（依赖类型上） | 类型对不齐 ❗ |
  | 结构递归 + `nomatch` | **零公理** ✅ |
  | `Nat.strongRecOn` | **零公理** ✅ |
  | `cases h with \| head => .. \| tail _ h' => ..` | **零公理** ✅ |
-/

namespace FateV2.Model

/-! ## 一、下标 ↔ 顶点的双向搬运 -/

/-- **`vs` 的第 `i` 个元素**（手写，零公理）。

    比 `List.get` 多说了：把**位置**（`Fin vs.length`）翻译成**顶点**（`Fin n`），
    于是 `vs` 可以作为顶点类型 `Fin vs.length` 使用 ——
    这是本文件把「长度写进类型」、从而完全避开 `Fin` 依赖消去的关键。 -/
def nthV {n : Nat} : (vs : List (Fin n)) → Fin vs.length → Fin n
  | [], i => nomatch i
  | w :: _, ⟨0, _⟩ => w
  | _ :: ws, ⟨k + 1, hk⟩ => nthV ws ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- **`nthV vs i` 一定在 `vs` 里**。

    比 `nthV` 的定义多说了：把「位置」交还给「成员」，
    于是索引图的每个下标都对应 `vs` 里的真实顶点。 -/
theorem nthV_mem {n : Nat} : ∀ (vs : List (Fin n)) (i : Fin vs.length), nthV vs i ∈ vs
  | [], i => nomatch i
  | _ :: _, ⟨0, _⟩ => List.mem_cons_self ..
  | _ :: ws, ⟨k + 1, hk⟩ =>
      List.mem_cons_of_mem _ (nthV_mem ws ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

/-- **`y` 在 `vs` 里的第一个下标**（手写，`Option` 包装，零公理）。

    比 `List.idxOf` 多说了：返回 `Option (Fin vs.length)` 而不是 `Option Nat`，
    于是「找到了」这一信息**自带正确的位置类型**，调用处不必再补 `_ < vs.length`。 -/
def idxOf {n : Nat} (y : Fin n) : (vs : List (Fin n)) → Option (Fin vs.length)
  | [] => none
  | w :: ws =>
      if _ : y.val = w.val then some ⟨0, Nat.zero_lt_succ ws.length⟩
      else
        match idxOf y ws with
        | none => none
        | some k => some ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩

/-- **`idxOf` 找回的正是原元素**（`nthV` 与 `idxOf` 互为逆）。

    比 `idxOf` 的定义多说了：让「父在 `vs` 里」这件事既能按下标陈述、
    也能按成员陈述，两者可自由换算 —— 索引图的源点翻译回原图源点的全部依据。 -/
theorem idxOf_spec {n : Nat} (y : Fin n) :
    ∀ (vs : List (Fin n)) (j : Fin vs.length), idxOf y vs = some j → nthV vs j = y
  | [], j, _ => nomatch j
  | w :: ws, j, h => by
      unfold idxOf at h
      by_cases hyw : y.val = w.val
      · rw [dif_pos hyw] at h
        cases h
        exact Fin.eq_of_val_eq hyw.symm
      · rw [dif_neg hyw] at h
        cases hidx : idxOf y ws with
        | none => rw [hidx] at h; exact absurd h (fun e => nomatch e)
        | some k =>
            rw [hidx] at h
            cases h
            exact idxOf_spec y ws k hidx

/-! ## 二、`idxOf` 与 `memFin` 一致 -/

/-- **`idxOf` 成功 ⟺ `memFin` 判真**。

    比 `idxOf` 的定义多说了：把「手写的下标查找」与 T1b 的「手写的成员判定」
    接上，于是「某个父被过滤掉」可以用 `memFin` 的 `Bool` 结果来陈述，
    从而复用 `filterMem` 的一整套引理（`mem_filterMem` / `filterMem_nil`）。 -/
theorem idxOf_isSome_iff {n : Nat} (y : Fin n) :
    ∀ (vs : List (Fin n)), (idxOf y vs).isSome = memFin y vs
  | [] => rfl
  | w :: ws => by
      have ih := idxOf_isSome_iff y ws
      unfold idxOf memFin
      by_cases hyw : y.val = w.val
      · rw [dif_pos hyw]
        rw [dif_pos hyw]
        rfl
      · rw [dif_neg hyw]
        rw [dif_neg hyw]
        cases hidx : idxOf y ws with
        | none =>
            have : memFin y ws = false := by rw [← ih, hidx]; rfl
            rw [this]
            rfl
        | some k =>
            have : memFin y ws = true := by rw [← ih, hidx]; rfl
            rw [this]
            rfl

/-! ## 三、索引限制图与它的无环性 -/

/-- **父列表的索引化**（手写过滤，零公理）。

    比 `filterMem` 多说了：`filterMem` 给出「父里哪些落在 `vs` 里」的**顶点**列表，
    这里给出它们的**下标**列表 —— 于是父边关系被搬到了顶点类型 `Fin vs.length` 上，
    可以直接喂给 `source_exists_fin`。找不到的父（不在 `vs` 里）自动丢弃，
    与 `filterMem` 的语义一致。 -/
def idxList {n : Nat} (vs : List (Fin n)) : List (Fin n) → List (Fin vs.length)
  | [] => []
  | y :: ys =>
      match idxOf y vs with
      | none => idxList vs ys
      | some j => j :: idxList vs ys

/-- **索引化后的列表为空 ⟺ `filterMem` 为空**。

    比 `idxList` 的定义多说了：把两种「限制到 `vs`」的手写实现
    **对齐到同一个谓词**，于是 `source_exists_fin` 在索引图上给出的源点，
    可以直接当作「`filterMem` 为空」的见证使用。 -/
theorem idxList_nil_iff {n : Nat} (vs : List (Fin n)) :
    ∀ (l : List (Fin n)), idxList vs l = [] ↔ filterMem l vs = [] := by
  intro l
  induction l with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons y ys ih =>
      unfold idxList
      cases hidx : idxOf y vs with
      | none =>
          -- `idxOf` 找不到 ⟹ `memFin y vs = false` ⟹ `filterMem` 丢掉 `y`
          have hfalse : memFin y vs = false := by
            rw [← idxOf_isSome_iff y vs, hidx]
            rfl
          have hd : filterMem (y :: ys) vs = filterMem ys vs := by
            show (if memFin y vs then y :: filterMem ys vs else filterMem ys vs) = _
            rw [if_neg (by rw [hfalse]; intro e; exact nomatch e)]
          rw [hd]
          exact ih
      | some j =>
          -- `idxOf` 找到 ⟹ `memFin y vs = true` ⟹ `filterMem` 保留 `y`
          have htrue : memFin y vs = true := by
            rw [← idxOf_isSome_iff y vs, hidx]
            rfl
          have hd : filterMem (y :: ys) vs = y :: filterMem ys vs := by
            show (if memFin y vs then y :: filterMem ys vs else filterMem ys vs) = _
            rw [if_pos htrue]
          rw [hd]
          constructor
          · intro h
            exact absurd h (cons_ne_nil j (idxList vs ys))
          · intro h
            exact absurd h (cons_ne_nil y (filterMem ys vs))

/-- **索引限制图**：顶点类型就是 `Fin vs.length`，父边是 `g.pa` 的索引化。

    比 `restrictTo` 多说了：**顶点类型随 `vs` 的长度变化**。
    这是本文件的核心技巧 —— 因为长度写进了类型，
    `vs = w :: ws` 时 `Fin (w :: ws).length` 与 `Fin (ws.length + 1)` 是
    **定义性**相等（`rfl`），于是 `source_exists_fin` 可以直接作用，
    不需要任何 `Fin` 的依赖消去；而递归删点后顶点类型自动变成
    `Fin (removeOne src vs).length`，也不需要搬运。 -/
def indG {n : Nat} (g : Graph (Fin n)) (vs : List (Fin n)) : Graph (Fin vs.length) where
  pa i := idxList vs (g.pa (nthV vs i))

/-- **索引父列表里的元素，其顶点在原父列表里**。

    比 `idxList` 的定义多说了：它把「下标成员」翻译回「顶点成员」，
    于是索引图确实是原图的子图 —— 无环性可以继承。
    实现按索引后的列表做结构递归，同时保留「它来自哪个父列表」这一信息以便陈述目标。 -/
theorem mem_of_idxList {n : Nat} (g : Graph (Fin n)) (vs : List (Fin n)) (i : Fin vs.length) :
    ∀ (l : List (Fin n)) (y : Fin vs.length), y ∈ idxList vs l → nthV vs y ∈ l
  | [], y, hy => absurd hy (List.not_mem_nil)
  | z :: zs, y, hy => by
      unfold idxList at hy
      cases hidx : idxOf z vs with
      | none =>
          rw [hidx] at hy
          exact List.mem_cons_of_mem z (mem_of_idxList g vs i zs y hy)
      | some j =>
          -- 先把 `j` 与 `hidx` 钉住，再化简 `hy`，否则 `cases hy` 之后 `j` 会被消去
          have hspec : nthV vs j = z := idxOf_spec z vs j hidx
          rw [hidx] at hy
          cases hy with
          | head =>
              rw [← hspec]
              exact List.mem_cons_self ..
          | tail _ htl =>
              exact List.mem_cons_of_mem z (mem_of_idxList g vs i zs y htl)

/-- **索引图的路径可以搬回原图**。

    比 `indG` 的定义多说了：**索引图是原图的子图**，
    于是原图的无环性在这里照搬，得到 `Acyclic g → Acyclic (indG g vs)`。 -/
theorem reachable_indG {n : Nat} {g : Graph (Fin n)} {vs : List (Fin n)}
    {a b : Fin vs.length} (h : Reachable (indG g vs) a b) :
    Reachable g (nthV vs a) (nthV vs b) := by
  induction h with
  | @step x y hmem => exact Reachable.step (mem_of_idxList g vs x _ y hmem)
  | @trans x y z _ _ ihxy ihyz => exact Reachable.trans ihxy ihyz

/-- **索引图保持无环**。

    比 `reachable_indG` 多说了：子图的无环性**自动继承**，
    于是 `source_exists_fin` 可以作用在索引图上，从剩余顶点里取源点。 -/
theorem indG_acyclic {n : Nat} (g : Graph (Fin n)) (vs : List (Fin n))
    (hac : Acyclic g) : Acyclic (indG g vs) :=
  fun v hrv => hac (nthV vs v) (reachable_indG hrv)

/-! ## 四、剩余顶点集里必有一个「无入边」的点 -/

/-- **非空顶点集里必有一个「父都不在里面」的点**（本文件的核心引理）。

    比 `HasSource` 的定义多说了：它在**任意非空子列表**上给出一个
    「在子列表内部无入边」的点 —— 而不只是「全图里有源点」。
    这是拓扑序归纳能推进的那块砖：源点不要求在**全图**无父，
    只要求在**剩余顶点集**内无父即可排到最前。

    证明：索引图 `indG g vs` 的顶点类型恰为 `Fin vs.length`，
    于是 `vs = w :: ws` 时 `Fin (vs.length)` 与 `Fin (ws.length + 1)` 是
    **定义性**相等（`rfl`），`source_exists_fin ws.length` 可以直接作用 ——
    这正是本文件把长度写进类型所换来的好处，**一次 `Fin` 依赖消去都不需要**。
    随后 `idxList_nil_iff` 把「索引父列表为空」翻成「`filterMem` 为空」，
    `nthV_mem` 保证这个点确实在 `vs` 里。 -/
theorem exists_free_in_vertices {n : Nat} (g : Graph (Fin n)) (vs : List (Fin n))
    (hne : vs ≠ []) (hac : Acyclic g) :
    ∃ src, src ∈ vs ∧ filterMem (g.pa src) vs = [] := by
  -- 摊开 `vs` 的形状（`match` 表达式，返回类型随模式替换）
  match vs, hne with
  | [], hne => exact absurd rfl hne
  | w :: ws, _ =>
      -- `Fin (w :: ws).length` 与 `Fin (ws.length + 1)` 在此是**同一个类型**（`rfl`）
      obtain ⟨i, hpa⟩ :=
        source_exists_fin ws.length (indG g (w :: ws)) (indG_acyclic g (w :: ws) hac)
      exact ⟨nthV (w :: ws) i, nthV_mem (w :: ws) i,
             (idxList_nil_iff (w :: ws) (g.pa (nthV (w :: ws) i))).1 hpa⟩

/-! ## 五、主定理 -/

/-- **`removeOne` 保留 `Nodup` 的配套事实：删掉后剩下的点都还在**。

    比 `mem_removeOne` 多说了：`mem_removeOne` 是「过滤后 ⊆ 过滤前」，
    这里补上归纳要用的另一半——删掉 `src` 之后剩下的顶点集
    **恰好是原顶点集除去 `src`**，于是「父都在剩余集之外 ⟹ 父就是 `src`」成立。 -/
theorem mem_or_eq_of_not_mem_removeOne {n : Nat} (v : Fin n) :
    ∀ (l : List (Fin n)) (x : Fin n), x ∈ l → x ∉ removeOne v l → x = v
  | [], x, hx, _ => absurd hx (List.not_mem_nil)
  | y :: ys, x, hx, hnot => by
      by_cases hyv : y.val = v.val
      · -- 命中的是 `y`，于是 `removeOne v (y :: ys) = ys`
        rw [removeOne_hit v y ys hyv] at hnot
        have hye : y = v := Fin.eq_of_val_eq hyv
        cases hx with
        | head => exact hye
        | tail _ htl => exact absurd htl hnot
      · rw [removeOne_miss v y ys hyv] at hnot
        cases hx with
        | head =>
            -- 此处 `x` 已被替换成 `y`，目标是 `y = v`；
            -- 若 `y ≠ v`，则 `y ∈ y :: removeOne v ys`，与 `hnot` 矛盾
            by_contra hyv'
            exact hnot (List.mem_cons_self ..)
        | tail _ htl =>
            exact mem_or_eq_of_not_mem_removeOne v ys x htl (fun hmem => hnot (List.mem_cons_of_mem y hmem))

/-- **`filterMem` 为空 ⟹ 父都不在 `vs` 里**（T1b 的 `filterMem_nil` 的命题化）。 -/
theorem filterMem_nil_mem {n : Nat} (g : Graph (Fin n)) (vs : List (Fin n)) (src : Fin n)
    (h : filterMem (g.pa src) vs = []) : ∀ b, b ∈ g.pa src → b ∉ vs := by
  intro b hb hbv
  exact memFin_false_elim b vs (filterMem_nil (g.pa src) vs b h hb) hbv

/-- **`nth` 有值 ⟹ 该值在列表里**（`exists_nth_of_mem` 的逆）。 -/
theorem mem_of_nth {V : Type u} : ∀ (l : List V) (i : Nat) (v : V), nth l i = some v → v ∈ l
  | [], _, _, h => by cases h
  | x :: xs, 0, v, h => by
      have hvx : x = v := some_inj h
      rw [← hvx]
      exact List.mem_cons_self ..
  | x :: xs, k + 1, v, h => List.mem_cons_of_mem x (mem_of_nth xs k v h)

/-- **拓扑序的「精确型」**：`order` 恰好覆盖 `vs`，且不含 `vs` 之外的点。

    比 `IsTopoOrderOn` 多说了：`IsTopoOrderOn` 只要求 `order` **覆盖** `vs`，
    允许 `order` 多排别处的点；而归纳步要从 `nth order i = some a`
    反推 `a ∈ removeOne src vs`，就必须知道 `order` **不溢出**。
    两条合起来正好是「`order` 的成员集 = `vs` 的成员集」，
    于是「`a` 排在 `order` 里」和「`a ∈ vs`」可以自由换算 ——
    这正是 T1b 报告 §5.2 里卡住的那一步。 -/
def IsTopoOrderExact {V : Type u} (g : Graph V) (vs order : List V) : Prop :=
  IsTopoOrderOn g vs order ∧ ∀ v, v ∈ order → v ∈ vs

/-- **精确型 ⟹ 普通型**。 -/
theorem isTopoOrderOn_of_exact {V : Type u} {g : Graph V} {vs order : List V}
    (h : IsTopoOrderExact g vs order) : IsTopoOrderOn g vs order := h.1

/-- **精确型的成员是双向的**。

    比 `IsTopoOrderOn` 的定义多说了：把「`order` 覆盖 `vs`」与「`order ⊆ vs`」
    合成一条 `↔`，于是任何一侧的成员事实都能换到另一侧。 -/
theorem exact_mem_iff {V : Type u} {g : Graph V} {vs order : List V}
    (h : IsTopoOrderExact g vs order) : ∀ v, v ∈ order ↔ v ∈ vs :=
  fun v => ⟨h.2 v, h.1.1 v⟩

/-- **拓扑序归纳的核心推进：删掉一个「在剩余集内无父」的点**。

    比 `IsTopoOrderOn` 的定义多说了：把「先排的点」从归纳步里**剥离**出来 ——
    只要 `order` 是剩余顶点集 `removeOne src vs` 的拓扑序，
    那么 `src :: order` 就是 `vs` 的拓扑序。

    这是 T1 的 `topo_cons_of_source` 在**子列表**上的版本：差别在于
    「父都在剩余集之外」并不要求「全图无父」，只需要 `mem_or_eq_of_not_mem_removeOne`
    把「父不在剩余集 ⟹ 父 = `src`」翻出来，再与 `hsrc` 相撞。 -/
theorem isTopoOrderOn_removeOne {n : Nat} (g : Graph (Fin n)) (vs : List (Fin n))
    (src : Fin n) (hsrcIn : src ∈ vs) (hsrcOut : filterMem (g.pa src) vs = [])
    (hvs : vs.Nodup) (order : List (Fin n))
    (h : IsTopoOrderExact g (removeOne src vs) order) :
    IsTopoOrderExact g vs (src :: order) := by
  -- `src ∉ removeOne src vs`（`Nodup` 下删除是彻底的）
  have hsrcNotIn : src ∉ removeOne src vs := not_mem_removeOne_self src vs hvs
  -- `order` 的每个成员都在 `removeOne src vs` 里（精确型的反向覆盖），于是都不等于 `src`
  have hneIn : ∀ v, v ∈ order → v ≠ src := by
    intro v hv he
    exact hsrcNotIn (he ▸ h.2 v hv)
  have hneNth : ∀ (x : Fin n) (i : Nat), nth order i = some x → x ≠ src :=
    fun x i hx => hneIn x (mem_of_nth order i x hx)
  constructor
  · -- 覆盖：`src` 排最前，其余按 `mem_removeOne_of_ne` 落进 `order`
    constructor
    · intro v hv
      by_cases hvs : v = src
      · rw [hvs]; exact List.mem_cons_self ..
      · refine List.mem_cons_of_mem src (h.1.1 v ?_)
        exact mem_removeOne_of_ne vs src v hv (fun hval => hvs (Fin.eq_of_val_eq hval))
    · -- 父边条件
      intro a b hb ha hbv i j hi hj
      cases i with
      | zero =>
          have hsa : src = a := some_inj hi
          exact absurd hbv (filterMem_nil_mem g vs src hsrcOut b (mem_pa_congr hsa hb))
      | succ i' =>
          have hi' : nth order i' = some a := hi
          have ha' : a ∈ removeOne src vs :=
            mem_removeOne_of_ne vs src a ha
              (fun hval => hneNth a i' hi' (Fin.eq_of_val_eq hval))
          cases j with
          | zero => exact Nat.zero_lt_succ i'
          | succ j' =>
              have hj' : nth order j' = some b := hj
              have hb' : b ∈ removeOne src vs :=
                mem_removeOne_of_ne vs src b hbv
                  (fun hval => hneNth b j' hj' (Fin.eq_of_val_eq hval))
              exact Nat.succ_lt_succ (h.1.2 a b hb ha' hb' i' j' hi' hj')
  · -- 反向覆盖：`src :: order` 的成员都在 `vs` 里
    intro v hv
    cases hv with
    | head => exact hsrcIn
    | tail _ htl => exact mem_removeOne vs src v (h.2 v htl)

/-! ## 五、`removeOne` 保留 `Nodup` -/

/-- **`removeOne` 保留 `Nodup`**。

    比 `removeOne` 的定义多说了：删元素**不制造重复**，于是「删掉源点后的剩余顶点集」
    仍然可以直接作为递归调用的顶点列表（递归谓词带 `vs.Nodup`）。

    证明：命中分支剩下的就是尾（其 `Nodup` 由 `list_nodup_tail` 给出）；
    未命中分支的头原样保留，它与「已删过的尾」仍两两不同
    —— 因为已删过的尾的每个元素都由 `mem_removeOne` 落回原尾部。 -/
theorem nodup_removeOne {n : Nat} (v : Fin n) :
    ∀ (l : List (Fin n)), l.Nodup → (removeOne v l).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, hnd => by
      by_cases hxv : x.val = v.val
      · rw [removeOne_hit v x xs hxv]
        exact list_nodup_tail hnd
      · rw [removeOne_miss v x xs hxv]
        refine List.Pairwise.cons ?_ (nodup_removeOne v xs (list_nodup_tail hnd))
        intro y hy heq
        -- `heq : x = y`，于是 `x` 也落在已被删过的尾里，落回原尾与 `Nodup` 相撞
        exact list_nodup_head hnd (heq ▸ mem_removeOne xs v y hy)

/-- **`removeOne` 删除后长度严格变小**（元素在列表里时，T1b 已有；此处给需要的形态）。 -/
theorem removeOne_length_lt' {n : Nat} (v : Fin n) :
    ∀ (l : List (Fin n)), v ∈ l → (removeOne v l).length < l.length
  | [], h => absurd h (List.not_mem_nil)
  | x :: xs, h => by
      by_cases hxv : x.val = v.val
      · rw [removeOne_hit v x xs hxv]
        exact Nat.lt_succ_self xs.length
      · rw [removeOne_miss v x xs hxv]
        exact Nat.succ_lt_succ (removeOne_length_lt' v xs (mem_of_mem_tail h hxv))

/-! ## 六、主定理：拓扑序存在 -/

/-- **`Fin n` 上无环 ⟹ 子列表上的精确拓扑序存在**（对长度归纳）。

    比 `exists_free_in_vertices` 多说了：把「选点」与「排序」**循环起来** ——
    每一步取一个「在剩余集内无父」的点排到最前（`isTopoOrderOn_removeOne`），
    再对剩下的更短列表递归。归纳量是列表长度（`Nat` 归纳，零公理），
    缩短性由 `removeOne_length_lt` 提供。

    `vs.Nodup` 这一前提**只用到一处**：让 `not_mem_removeOne_self` 成立，
    从而 `removeOne src vs` 绝不含 `src`，于是「`order` 的成员都不等于 `src`」
    由精确型的反向覆盖自动得到 —— 这正好补上 T1b 报告 §5.2 里
    「`a ∈ order'` 反推 `a ∈ removeOne src vertices`」的缺口。 -/
theorem exists_topo_exact {n : Nat} (g : Graph (Fin n)) (hac : Acyclic g) :
    ∀ (k : Nat) (vs : List (Fin n)), vs.length ≤ k → vs.Nodup →
      ∃ order, IsTopoOrderExact g vs order := by
  intro k
  induction k with
  | zero =>
      intro vs hlen hnd
      have hv : vs = [] := by
        cases vs with
        | nil => rfl
        | cons w ws => exact absurd hlen (Nat.not_succ_le_zero ws.length)
      subst hv
      exact ⟨[], ⟨fun v hv => absurd hv (List.not_mem_nil),
                  fun _ _ _ ha _ => absurd ha (List.not_mem_nil)⟩,
               fun v hv => absurd hv (List.not_mem_nil)⟩
  | succ k ih =>
      intro vs hlen hnd
      by_cases hne : vs = []
      · subst hne
        exact ⟨[], ⟨fun v hv => absurd hv (List.not_mem_nil),
                    fun _ _ _ ha _ => absurd ha (List.not_mem_nil)⟩,
               fun v hv => absurd hv (List.not_mem_nil)⟩
      · obtain ⟨src, hsrcIn, hsrcOut⟩ := exists_free_in_vertices g vs hne hac
        have hlt : (removeOne src vs).length ≤ k :=
          Nat.lt_succ_iff.1 (Nat.lt_of_lt_of_le (removeOne_length_lt src vs hsrcIn) hlen)
        have hnd' : (removeOne src vs).Nodup := nodup_removeOne src vs hnd
        obtain ⟨order, horder⟩ := ih (removeOne src vs) hlt hnd'
        exact ⟨src :: order,
               isTopoOrderOn_removeOne g vs src hsrcIn hsrcOut hnd order horder⟩

/-! ## 七、长度满格的无重复列表取遍全体 -/

/-- **`Fin n` 上列表成员可判定**（手写，不用 `DecidableEq` 实例）。

    比 `memFin` 多说了：`memFin` 给的是 `Bool`，这里把它包装成 `Decidable`，
    于是 `of_not_not_of_decidable` 可以作用在 `v ∈ l` 上，
    **完全绕开 `Classical.choice`**（这也是本文件不用 `by_contra` 的原因：
    `by_contra` 会经 `Classical` 带入 `propext`）。 -/
def decMem {n : Nat} (l : List (Fin n)) (v : Fin n) : Decidable (v ∈ l) :=
  match h : memFin v l with
  | true => isTrue (mem_of_memFin v l h)
  | false => isFalse (fun hm => memFin_false_elim v l h hm)

/-- **长度等于顶点数且无重复 ⟹ 覆盖全体**（鸽笼的另一半）。

    比 `length_le_of_nodup_fin` 多说了：鸽笼给「长度 ≤ n」这条上界，
    这里给**等号情形的覆盖性** —— 长度恰为 `n` 且无重复，则 `Fin n` 的每个居民都在列表里。
    这是「排好一条覆盖全体的序」与「排好一条任意子列表的序」之间的桥。

    证明：若某 `v ∉ l`，把 `v` 接到 `l` 后面得长度 `n+1` 的无重复列表，撞鸽笼。
    收尾走 `of_not_not_of_decidable`（构造性），不用 `by_contra`（后者带 `propext`）。 -/
theorem mem_of_length_eq_nodup {n : Nat} (l : List (Fin n))
    (hlen : l.length = n) (hnd : l.Nodup) (v : Fin n) : v ∈ l := by
  have hnn : ¬ ¬ (v ∈ l) := by
    intro hnot
    have hnd' : (v :: l).Nodup := by
      refine List.Pairwise.cons ?_ hnd
      intro y hy heq
      exact hnot (heq ▸ hy)
    have hle : (v :: l).length ≤ n := length_le_of_nodup_fin n _ hnd'
    rw [List.length_cons, hlen] at hle
    exact absurd hle (Nat.not_succ_le_self n)
  exact @of_not_not_of_decidable (v ∈ l) (decMem l v) hnn

/-! ## 八、`Fin n` 的全体枚举（手写，零公理） -/

/-- **`Fin k` 的列表逐位搬进 `Fin (k+1)`**（值不变，手写遍历）。

    比 `Fin.castSucc` 多说了：它是**手写递归**，不用 `List.map`
    （后者对元素递归会退化成 well-founded 递归而带 `propext`），
    于是「把 `enumFin k` 搬进 `Fin (k+1)`」这一步零公理。 -/
def mapUp {k : Nat} : List (Fin k) → List (Fin (k + 1))
  | [] => []
  | x :: xs => ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ :: mapUp xs

/-- **`mapUp` 保长度**。 -/
theorem mapUp_length {k : Nat} : ∀ (l : List (Fin k)), (mapUp l).length = l.length
  | [] => rfl
  | x :: xs => by
      show (⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ :: mapUp xs).length = xs.length + 1
      rw [List.length_cons, mapUp_length xs]

/-- **`mapUp` 的每个元素都来自原列表（值相同）**。

    比 `mapUp` 的定义多说了：它把「搬运」的方向反过来，
    于是「`enumFin (k+1)` 的尾部元素」可以回溯到「`enumFin k` 的元素」，
    无重复性因此从 `k` 继承到 `k+1`。 -/
theorem mapUp_mem_val {k : Nat} : ∀ (l : List (Fin k)) (y : Fin (k + 1)),
    y ∈ mapUp l → ∃ z, z ∈ l ∧ y.val = z.val
  | [], _, hy => absurd hy (List.not_mem_nil)
  | x :: xs, y, hy => by
      cases hy with
      | head => exact ⟨x, List.mem_cons_self .., rfl⟩
      | tail _ htl =>
          obtain ⟨z, hz, hv⟩ := mapUp_mem_val xs y htl
          exact ⟨z, List.mem_cons_of_mem x hz, hv⟩

/-- **`mapUp` 保无重复**。 -/
theorem mapUp_nodup {k : Nat} : ∀ (l : List (Fin k)), l.Nodup → (mapUp l).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, hnd => by
      obtain ⟨hh, ht⟩ := list_nodup_split hnd
      refine List.Pairwise.cons ?_ (mapUp_nodup xs ht)
      intro y hy heq
      -- `heq : ⟨x.val,_⟩ = y`，于是 `y.val = x.val`；把 `y` 回溯到 `xs` 里的 `z`
      obtain ⟨z, hz, hzv⟩ := mapUp_mem_val xs y hy
      have hxv : x.val = y.val := congrArg Fin.val heq
      exact hh z hz (Fin.eq_of_val_eq (hxv.trans hzv))
/-- **`Fin n` 的全体枚举**（手写原始递归，零公理）。

    比 `List.finRange` 多说了：它完全不用 `Fintype` / `Finset` 机制，
    于是长度、无重复两条性质都能用纯结构归纳证出，不带任何公理。 -/
def enumFin : (n : Nat) → List (Fin n)
  | 0 => []
  | k + 1 => ⟨k, Nat.lt_succ_self k⟩ :: mapUp (enumFin k)

/-- **`enumFin n` 的长度恰为 `n`**。 -/
theorem enumFin_length : ∀ n : Nat, (enumFin n).length = n
  | 0 => rfl
  | k + 1 => by
      show (⟨k, Nat.lt_succ_self k⟩ :: mapUp (enumFin k)).length = k + 1
      rw [List.length_cons, mapUp_length, enumFin_length]

/-- **`enumFin n` 无重复**。 -/
theorem enumFin_nodup : ∀ n : Nat, (enumFin n).Nodup
  | 0 => List.Pairwise.nil
  | k + 1 => by
      show (⟨k, Nat.lt_succ_self k⟩ :: mapUp (enumFin k)).Nodup
      refine List.Pairwise.cons ?_ (mapUp_nodup _ (enumFin_nodup k))
      intro y hy heq
      -- `⟨k,_⟩ = y` 且 `y` 来自 `mapUp (enumFin k)`，故 `y.val < k`，与 `y.val = k` 相撞
      obtain ⟨z, _, hzv⟩ := mapUp_mem_val (enumFin k) y hy
      have hyk : k = y.val := congrArg Fin.val heq
      exact absurd (hyk.trans hzv) (fun hcong => Nat.lt_irrefl z.val (hcong ▸ z.isLt))

/-! ## 九、主定理 -/

/-- **`Fin (m+1)` 上无环 ⟹ 存在拓扑序**（零公理）。

    比 `IsTopoOrder` 的定义多说了：**它一定存在** ——
    T1 的 `topo_cons_of_source` 只说了「给定源点 + 给定子序 ⟹ 是拓扑序」；
    本定理把「源点存在」（T1b 的 `source_exists_fin`，见 `exists_free_in_vertices`）
    与「子序存在」（对剩余点数的递归 `exists_topo_exact`）都补上，
    于是从「无环」这**一个**前提直接得到一条具体的 `order`。

    落点：取 `vs = enumFin (m+1)`（长度恰为 `m+1`、无重复），
    由 `mem_of_length_eq_nodup` 它覆盖全体，
    于是 `IsTopoOrderExact` 的第一半经 `isTopoOrder_of_on` 升级为 `IsTopoOrder`。 -/
theorem exists_topo_order_fin (m : Nat) (g : Graph (Fin (m + 1))) (hac : Acyclic g) :
    ∃ order : List (Fin (m + 1)), IsTopoOrder g order := by
  obtain ⟨order, hExact⟩ :=
    exists_topo_exact g hac (m + 1) (enumFin (m + 1))
      (Nat.le_of_eq (enumFin_length (m + 1))) (enumFin_nodup (m + 1))
  exact ⟨order,
    isTopoOrder_of_on g (enumFin (m + 1)) order
      (fun v => mem_of_length_eq_nodup (enumFin (m + 1)) (enumFin_length (m + 1))
        (enumFin_nodup (m + 1)) v)
      hExact.1⟩

end FateV2.Model

