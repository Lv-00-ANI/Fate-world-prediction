import FateWorld.FateV2.Core.Cardinality
import FateWorld.FateV2.Model.TopoExists
import FateWorld.FateV2.Core.Closure
import FateWorld.FateV2.Model.Pigeon

/-!
  # Model · 拓扑序存在性（任意有限类型版，专项 T30）

  ## 本文件回答什么

  T1c 的主定理有两处类型限制：

  ```lean
  theorem exists_topo_order_fin (m : Nat) (g : Graph (Fin (m + 1))) (hac : Acyclic g) :
      ∃ order : List (Fin (m + 1)), IsTopoOrder g order
  ```

  1. 顶点类型必须是 `Fin (m+1)`，不能是任意 `V`；
  2. 必须是 `m+1` 而非 `m`（`Fin 0` 无源点，T1b 已给零公理反例 `fin0_not_hasSource`）。

  本文件把**两处都去掉**，并精确说明「有限性」与「判等」必须以什么形式出现。

  ## 路线：C（覆盖列表）为主，A（单射嵌入）为特例

  | 路线 | 内容 | 本文件取舍 |
  |---|---|---|
  | **C** | 显式给一个 `Nodup` 的**覆盖列表** `verts` | **主路线** |
  | A | 给一个到 `Fin n` 的**单射** `f` | **由 C 导出**（见 §五 `cover_of_inj`） |
  | B | 仍用 `Fin (m+1)` | **特例**（`Fin n` 的枚举即覆盖列表） |
  | ✗ | `[Fintype V]` + `Fintype.equivFin` | **放弃**：`Fintype.equivFin` 带三公理 |

  为什么 C 更强：A 的前提 `(f, h_inj)` 本身就够造出覆盖列表（§五 `cover_of_inj`）；
  反过来 `(verts, hcover, hnd)` 造不出单射（那需要 `Fintype`/`Classical.choice`）。

  为什么必须带 `hcover`：`Acyclic g ⟹ HasSource g` 对任意 `V` **为假**（§七 `Star` 反例）。
  有限性只能以「覆盖列表」这种**显式数据**进入，不能写成类型类。

  ## 为什么多一个 `eq` 参数

  任意 `V` 上没有 `DecidableEq`，也没有 `Classical.decEq`（后者带三公理）。
  而「删顶点」「查成员」都要判等，于是把判等作为**显式输入**
  `eq : V → V → Bool` 连同 `heq : ∀ a b, eq a b = true ↔ a = b` 一并给出。
  这是语言内的可计算数据，不是公理、也不是类型类实例 —— 本文件因此仍然**零公理**。

  ## 公理纪律（实测）

  | 写法 | 实测 |
  |---|---|
  | `Fintype.equivFin` / `Fintype.card` / `Finset.card` | 三公理 ❗ |
  | `Classical.decEq` / `by_contra` / `by_cases h : ∃ v, P v` | 三公理 ❗ |
  | `simp` / `decide` / `omega` / `List.mem_cons` / `List.mem_map` | `propext`（后两者更重）❗ |
  | 捕获通配 `\| _ =>` | `propext`（本文件一律穷举构造子）❗ |
  | 结构递归 + `nomatch` + `Nat.strongRecOn` | **零公理** ✅ |
  | T27 `pigeonhole`，T1b `of_not_not_of_decidable` | **零公理** ✅ |
-/

namespace FateV2.Model

universe u

/-! ## 一、承前入口（转引，零公理） -/

/-- **可判定命题的双重否定消去**（转引 T1b，零公理）。

    比 `Classical.byContradiction` 多说了：不需要经典选择 —— `Decidable P`
    直接给出正证或反证，于是 `¬¬P` 落地成 `P` 完全构造性。 -/
theorem of_not_not_dec {P : Prop} (d : Decidable P) (h : ¬ ¬ P) : P :=
  match d with
  | isTrue hp => hp
  | isFalse hn => absurd hn h

/-- **「无源点」逐点展开**（转引 T1b，零公理）。

    比 `Classical.not_forall` 多说了：`¬∃ → ∀¬` 是**构造性**的，
    于是反证假设可以直接用，不必经典换向。 -/
theorem forall_ne_of_not_exists' {W : Type u} (pa : W → List W)
    (h : ¬ ∃ v, pa v = []) : ∀ v, pa v ≠ [] :=
  fun v hv => h ⟨v, hv⟩

/-! ## 二、判等数据 `eq` 的基本结论 -/

/-- **`eq` 判真 ⟹ 真有值**（`heq` 的正向）。 -/
theorem eq_true_elim {W : Type u} {eq : W → W → Bool}
    (heq : ∀ a b, eq a b = true ↔ a = b) {a b : W} (h : eq a b = true) : a = b :=
  (heq a b).1 h

/-- **`eq` 判假 ⟹ 真的不等**（`heq` 的逆向）。

    比 `eq` 的定义多说了：把可算判定的否定还给命题层的不等，
    于是「命中 / 未命中」两个分支都能立刻转成 `=` / `≠` 使用。 -/
theorem ne_of_eq_false {W : Type u} {eq : W → W → Bool}
    (heq : ∀ a b, eq a b = true ↔ a = b) {a b : W} (h : eq a b = false) : a ≠ b := by
  intro hab
  rw [(heq a b).2 hab] at h
  exact Bool.noConfusion h

/-- **拆一条 `Nodup`**（构造子模式，转引 T1b 的 `list_nodup_split`）。

    比 `List.nodup_cons` 多说了：后者是 `↔`，实测带 `propext`；
    本条走 `Pairwise` 构造子，把两条子句**摊成可用的假设**，零公理。 -/
theorem nd_split {α : Type u} {x : α} {xs : List α}
    (h : (x :: xs).Nodup) : (∀ y, y ∈ xs → x ≠ y) ∧ xs.Nodup :=
  match h with
  | List.Pairwise.cons hh ht => ⟨hh, ht⟩

/-- **`Nodup` 的头子句**（导出版）。 -/
theorem nd_head' {α : Type u} {x : α} {xs : List α} (h : (x :: xs).Nodup) {y : α}
    (hy : y ∈ xs) : x ≠ y :=
  (nd_split h).1 y hy

/-- **`Nodup` 的尾子句**（导出版）。 -/
theorem nd_tail' {α : Type u} {x : α} {xs : List α} (h : (x :: xs).Nodup) : xs.Nodup :=
  (nd_split h).2

/-! ## 三、覆盖列表上的删除（全部手写，零公理） -/

/-- **删除一个与 `v` 相等的元素**（手写，`eq` 判定）。

    比 `OrderSource.removeOne` 多说了：T1c 的版本只对 `Fin n` 定义、按 `.val` 判等；
    本条对**任意类型**工作，判等由显式数据 `eq` 提供 —— C 路线的顶点类型是 `V`，
    没有 `.val` 可用，也没有 `DecidableEq`。 -/
def removeOneE {W : Type u} (eq : W → W → Bool) (v : W) : List W → List W
  | [] => []
  | x :: xs => match eq x v with
    | true => xs
    | false => x :: removeOneE eq v xs

/-- `removeOneE` 的「命中」形状。 -/
theorem removeOneE_hit {W : Type u} (eq : W → W → Bool) (v x : W) (xs : List W)
    (h : eq x v = true) : removeOneE eq v (x :: xs) = xs := by
  show (match eq x v with
        | true => xs
        | false => x :: removeOneE eq v xs) = xs
  rw [h]

/-- `removeOneE` 的「未命中」形状。 -/
theorem removeOneE_miss {W : Type u} (eq : W → W → Bool) (v x : W) (xs : List W)
    (h : eq x v = false) : removeOneE eq v (x :: xs) = x :: removeOneE eq v xs := by
  show (match eq x v with
        | true => xs
        | false => x :: removeOneE eq v xs) = x :: removeOneE eq v xs
  rw [h]

/-- **`removeOneE` 只删不增**。

    比 `removeOneE` 的定义多说了：删除**不制造新顶点**，
    于是「子图的顶点集 ⊆ 原顶点集」，为 `topo_cons_of_source` 的覆盖前提做准备。 -/
theorem mem_removeOneE {W : Type u} (eq : W → W → Bool) (v : W) : ∀ (l : List W) (x : W),
    x ∈ removeOneE eq v l → x ∈ l
  | [], x, h => absurd h (List.not_mem_nil)
  | y :: ys, x, h => by
      cases hy : eq y v with
      | true =>
          rw [removeOneE_hit eq v y ys hy] at h
          exact List.mem_cons_of_mem y h
      | false =>
          rw [removeOneE_miss eq v y ys hy] at h
          cases h with
          | head => exact List.mem_cons_self ..
          | tail _ htl => exact List.mem_cons_of_mem y (mem_removeOneE eq v ys x htl)

/-- **`removeOneE` 保留一切「与 `v` 不等」的元素**。

    比 `mem_removeOneE` 多说了：删除是**精确**的 —— 只损失那一个值，
    于是「剩余顶点集」与「原顶点集减一点」完全一致。 -/
theorem mem_removeOneE_of_ne {W : Type u} (eq : W → W → Bool) (heq : ∀ a b, eq a b = true ↔ a = b)
    (v : W) : ∀ (l : List W) (x : W), x ∈ l → x ≠ v → x ∈ removeOneE eq v l
  | [], x, h, _ => absurd h (List.not_mem_nil)
  | y :: ys, x, h, hne => by
      cases hy : eq y v with
      | true =>
          rw [removeOneE_hit eq v y ys hy]
          cases h with
          | head => exact absurd (eq_true_elim heq hy) hne
          | tail _ htl => exact htl
      | false =>
          rw [removeOneE_miss eq v y ys hy]
          cases h with
          | head => exact List.mem_cons_self ..
          | tail _ htl =>
              exact List.mem_cons_of_mem y (mem_removeOneE_of_ne eq heq v ys x htl hne)

/-- **`removeOneE` 删后长度严格变小**（元素在列表里时）。

    比 `mem_removeOneE` 多说了：不只是「不含该元素」，而是**长度确实减少** ——
    这是拓扑序归纳的终止性依据。 -/
theorem removeOneE_length_lt {W : Type u} (eq : W → W → Bool) (heq : ∀ a b, eq a b = true ↔ a = b)
    (v : W) : ∀ (l : List W), v ∈ l → (removeOneE eq v l).length < l.length
  | [], h => absurd h (List.not_mem_nil)
  | x :: xs, h => by
      cases hx : eq x v with
      | true =>
          rw [removeOneE_hit eq v x xs hx]
          exact Nat.lt_succ_self xs.length
      | false =>
          rw [removeOneE_miss eq v x xs hx]
          have hmem : v ∈ xs := by
            cases h with
            | head => exact absurd rfl (fun e => ne_of_eq_false heq hx e)
            | tail _ htl => exact htl
          exact Nat.succ_lt_succ (removeOneE_length_lt eq heq v xs hmem)

/-- **`removeOneE` 保持 `Nodup`**。

    比 `removeOneE` 的定义多说了：删元素**不制造重复**，
    于是剩余顶点列表仍可直接作为递归实参。 -/
theorem nodup_removeOneE {W : Type u} (eq : W → W → Bool) (v : W) : ∀ (l : List W),
    l.Nodup → (removeOneE eq v l).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, hnd => by
      cases hx : eq x v with
      | true =>
          rw [removeOneE_hit eq v x xs hx]
          exact nd_tail' hnd
      | false =>
          rw [removeOneE_miss eq v x xs hx]
          refine List.Pairwise.cons ?_ (nodup_removeOneE eq v xs (nd_tail' hnd))
          intro y hy heq2
          exact nd_head' hnd (mem_removeOneE eq v xs y hy) heq2

/-! ## 四、顶点 → 下标：覆盖列表提供的「有限性」 -/

/-- `Option.some` 相等 ⟹ 值相等（本文件自带的单射性，避免跨类型推断歧义）。 -/
theorem some_inj' {α : Type u} {a b : α} (h : (some a : Option α) = some b) : a = b := by
  cases h
  rfl

/-- `none = some x` 不可能（本文件自带的排除式）。 -/
theorem none_ne_some' {α : Type u} {a : α} (h : (none : Option α) = some a) : False := by
  cases h

/-- **元素在列表里的第一个下标**（手写，零公理）。

    比 `List.idxOf` 多说了：返回值带**位置类型** `Fin l.length`，
    于是「找到了」这一信息自带 `_ < l.length`，调用处不必再补证明。 -/
def idxOfE {W : Type u} (eq : W → W → Bool) (v : W) : (l : List W) → Option (Fin l.length)
  | [] => none
  | x :: xs =>
      match eq x v with
      | true => some ⟨0, Nat.zero_lt_succ xs.length⟩
      | false =>
          match idxOfE eq v xs with
          | none => none
          | some k => some ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩

/-- **`eq x v = true` 时 `idxOfE` 必命中下标 0**。 -/
theorem idxOfE_zero {W : Type u} (eq : W → W → Bool) (x v : W) (xs : List W)
    (h : eq x v = true) : idxOfE eq v (x :: xs) = some ⟨0, Nat.zero_lt_succ xs.length⟩ := by
  unfold idxOfE
  rw [h]

/-- **`idxOfE` 的「非首位」形态**（`eq x v = false` 且尾部命中 `k`）。

    比 `idxOfE` 的定义多说了：把「未命中头部时下标加一」写成一条**可直接 `rw`** 的等式，
    于是两个下标若要相同，就能把两边的 `+1` 同时拆掉、退回尾部继续比较。 -/
theorem idxOfE_succ {W : Type u} (eq : W → W → Bool) (x v : W) (xs : List W)
    (h : eq x v = false) {k : Fin xs.length} (hk : idxOfE eq v xs = some k) :
    idxOfE eq v (x :: xs) = some ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ := by
  unfold idxOfE
  rw [h, hk]

/-- **`idxOfE` 在「尾部未命中」时整体为 `none`**。

    比 `idxOfE_succ` 多说了：把「尾部没找到」这个坏消息原样传到整表，
    于是「整表命中某下标」与「尾部命中同一下标」可以互相换算。 -/
theorem idxOfE_succ_none {W : Type u} (eq : W → W → Bool) (x v : W) (xs : List W)
    (h : eq x v = false) (hk : idxOfE eq v xs = none) : idxOfE eq v (x :: xs) = none := by
  unfold idxOfE
  rw [h, hk]

/-- **下标 `0` 与下标 `k+1` 在 `Fin` 里不可能相等**。
    比 `Fin.ext` 多说了：它给出一条**直接可 `exact` 的 `False`**，
    于是「同一下标却走了不同分支」的情形不必再展开 `Nat` 算术。 -/
theorem fin_zero_ne_succ {n k : Nat} {hk : k + 1 < n + 1}
    (h : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩) : False :=
  Nat.noConfusion (congrArg Fin.val h)

/-- **覆盖 ⟹ `idxOfE` 必成功**。

    比 `idxOfE` 的定义多说了：覆盖列表给出的下标映射**是全域函数** ——
    这是 C 路线把它当作 `f : V → Fin n` 使用的唯一依据。 -/
theorem idxOfE_cover {W : Type u} (eq : W → W → Bool) (heq : ∀ a b, eq a b = true ↔ a = b)
    (v : W) : ∀ (l : List W), v ∈ l → ∃ k, idxOfE eq v l = some k
  | [], h => absurd h (List.not_mem_nil)
  | x :: xs, h => by
      cases hx : eq x v with
      | true => exact ⟨⟨0, Nat.zero_lt_succ xs.length⟩, idxOfE_zero eq x v xs hx⟩
      | false =>
          have htl : v ∈ xs := by
            cases h with
            | head => exact absurd rfl (fun e => ne_of_eq_false heq hx e)
            | tail _ h' => exact h'
          obtain ⟨k, hk⟩ := idxOfE_cover eq heq v xs htl
          exact ⟨⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩, idxOfE_succ eq x v xs hx hk⟩

/-- **`idxOfE` 在覆盖列表上处处不同**（单射性）。

    两个点若取同一下标，它们在列表里「命中的位置形状」就完全相同，
    逐层剥掉相同的头部后必然同时命中同一个元素，于是相等。
    这条把「覆盖列表」升级成「到 `Fin l.length` 的单射」，正是 `pigeonhole` 的入口。 -/
theorem idxOfE_inj {W : Type u} (eq : W → W → Bool) (heq : ∀ a b, eq a b = true ↔ a = b) :
    ∀ (l : List W) {v w : W} {k : Fin l.length},
      idxOfE eq v l = some k → idxOfE eq w l = some k → v = w
  | [], v, w, k, _, _ => nomatch k
  | x :: xs, v, w, k, hv, hw => by
      cases hxw : eq x w with
      | true =>
          rw [idxOfE_zero eq x w xs hxw] at hw
          have hk0 : k = ⟨0, Nat.zero_lt_succ xs.length⟩ := some_inj' hw.symm
          subst hk0
          cases hxv : eq x v with
          | true =>
              have hxw' : x = w := eq_true_elim (eq := eq) (a := x) (b := w) heq hxw
              have hxv' : x = v := eq_true_elim (eq := eq) (a := x) (b := v) heq hxv
              calc v = x := hxv'.symm
                _ = w := hxw'
          | false =>
              cases hrec : idxOfE eq v xs with
              | none =>
                  rw [idxOfE_succ_none eq x v xs hxv hrec] at hv
                  exact False.elim (none_ne_some' hv)
              | some j =>
                  rw [idxOfE_succ eq x v xs hxv hrec] at hv
                  exact absurd (some_inj' hv) (fun e => fin_zero_ne_succ e.symm)
      | false =>
          cases hrec2 : idxOfE eq w xs with
          | none =>
              rw [idxOfE_succ_none eq x w xs hxw hrec2] at hw
              exact False.elim (none_ne_some' hw)
          | some j2 =>
              rw [idxOfE_succ eq x w xs hxw hrec2] at hw
              have hk2 : k = ⟨j2.val + 1, Nat.succ_lt_succ j2.isLt⟩ := some_inj' hw.symm
              cases hxv : eq x v with
              | true =>
                  rw [idxOfE_zero eq x v xs hxv] at hv
                  exact absurd (some_inj' hv) (fun e => by
                    rw [hk2] at e
                    exact fin_zero_ne_succ e)
              | false =>
                  cases hrec : idxOfE eq v xs with
                  | none =>
                      rw [idxOfE_succ_none eq x v xs hxv hrec] at hv
                      exact False.elim (none_ne_some' hv)
                  | some j =>
                      rw [idxOfE_succ eq x v xs hxv hrec] at hv
                      have hvk : (⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ : Fin (xs.length + 1)) = k :=
                        some_inj' hv
                      have hval : j.val + 1 = j2.val + 1 := by
                        rw [hk2] at hvk
                        exact congrArg Fin.val hvk
                      have hjj : j = j2 := Fin.ext (Nat.succ.inj hval)
                      subst hjj
                      exact idxOfE_inj eq heq xs hrec hrec2

/-! ## 六、列表成员搬运 -/

/-- **`v ∈ w :: ws` 且 `v ≠ w` ⟹ `v ∈ ws`**。

    比 `List.mem_cons` 多说了：穷举 `List.Mem` 构造子，不带 `propext`。 -/
theorem mem_tail_of_ne {W : Type u} {w v : W} {ws : List W}
    (h : v ∈ w :: ws) (hne : v ≠ w) : v ∈ ws := by
  cases h with
  | head => exact absurd rfl hne
  | tail _ ht => exact ht

/-! ## 五、`verts` 里存在源点 ⟹ 全图有源点（可判定 + 构造） -/

/-- **列表里存在一个「无父点」这一命题**（覆盖列表专用）。 -/
def HasSourceIn {W : Type u} (g : Graph W) (verts : List W) : Prop :=
  ∃ v, v ∈ verts ∧ g.pa v = []

/-- **`HasSourceIn` 可判定**（手写穷举，零公理）。

    比 `HasSourceIn` 的定义多说了：把「列表里有源点」变成**可计算判定**，
    这正是把 `¬¬ HasSource` 落地成 `HasSource` 的那块砖（`Classical.choice` 不需要）。

    ⚠ 消 `v ∈ w :: ws` **只用 `cases`**（不用 `by_cases (v = w)`）：
    `head` 分支里 `v` 已被替换成 `w`，于是**不需要任何判等**；
    而 `by_cases` 会经 `propext` 引入三公理（已实测）。 -/
def decSourceIn {W : Type u} (g : Graph W) : (verts : List W) → Decidable (HasSourceIn g verts)
  | [] => isFalse (fun h => by
      obtain ⟨v, hv, _⟩ := h
      exact List.not_mem_nil hv)
  | w :: ws =>
      match hw : g.pa w with
      | [] => isTrue ⟨w, List.mem_cons_self .., hw⟩
      | a :: as =>
          match decSourceIn g ws with
          | isTrue h => isTrue (by
              obtain ⟨v, hv, hp⟩ := h
              exact ⟨v, List.mem_cons_of_mem w hv, hp⟩)
          | isFalse h => isFalse (fun hsrc => by
              obtain ⟨v, hv, hp⟩ := hsrc
              cases hv with
              | head =>
                  rw [hw] at hp
                  exact absurd hp (by intro h; cases h)
              | tail _ htl => exact h ⟨v, htl, hp⟩)

/-- **`verts` 里有源点 + 覆盖 ⟹ 全图有源点**（平凡但必要的一步）。

    比 `HasSourceIn` 的定义多说了：把「列表里」的见证搬到「全图」，
    于是反证时的「不覆盖」情形可以立刻排除。 -/
theorem hasSource_of_hasSourceIn {W : Type u} {g : Graph W} {verts : List W}
    (h : HasSourceIn g verts) : HasSource g := by
  obtain ⟨v, _, hp⟩ := h
  exact ⟨v, hp⟩




/-! ## 七、核心：任意类型上的「无环 ⟹ 有源点」 -/

/-- **位置查值**：`Fin l.length` → `l` 的第 `k` 项（手写结构递归）。 -/
def nthOf {W : Type u} : (l : List W) → Fin l.length → W
  | [], k => nomatch k
  | x :: _, ⟨0, _⟩ => x
  | _ :: xs, ⟨k + 1, hk⟩ => nthOf xs ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- **下标 → 值**：若 `idxOfE eq v l = some k`，则 `nthOf l k = v`。

    比 `idxOfE` 的定义多说了：把「下标」与「值」对上，于是「下标相同 ⟹ 值相同」直接可得 ——
    这是核心定理里「链的像无重复」那一步的全部依据。 -/
theorem nthOf_idxOfE {W : Type u} (eq : W → W → Bool) (heq : ∀ a b, eq a b = true ↔ a = b)
    (v : W) : ∀ (l : List W) (k : Fin l.length), idxOfE eq v l = some k → nthOf l k = v
  | [], k, _ => nomatch k
  | x :: xs, k, h => by
      cases hx : eq x v with
      | true =>
          rw [idxOfE_zero eq x v xs hx] at h
          have hk : k = ⟨0, Nat.zero_lt_succ xs.length⟩ := some_inj' h.symm
          subst hk
          exact eq_true_elim heq (a := x) (b := v) hx
      | false =>
          cases hrec : idxOfE eq v xs with
          | none =>
              rw [idxOfE_succ_none eq x v xs hx hrec] at h
              exact False.elim (none_ne_some' h)
          | some j =>
              rw [idxOfE_succ eq x v xs hx hrec] at h
              have hk : k = ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := some_inj' h.symm
              subst hk
              exact nthOf_idxOfE eq heq v xs j hrec

/-- **「每点都有父」时 `chain` 在 `Fin k` 上单射**（T1b `chain_ne_of_lt` 的函数式形态）。 -/
theorem chain_fin_inj {W : Type u} (g : Graph W) (hpa : ∀ v, g.pa v ≠ []) (s : W)
    (hac : Acyclic g) {k : Nat} :
    ∀ i j : Fin k, chain g hpa s i.val = chain g hpa s j.val → i = j := by
  intro i j hij
  by_cases hlt : i.val < j.val
  · exact absurd hij (chain_ne_of_lt (g := g) (hpa := hpa) (s := s) hac hlt)
  · have hle : j.val ≤ i.val := Nat.le_of_not_lt hlt
    by_cases hlt2 : j.val < i.val
    · exact absurd hij.symm (chain_ne_of_lt (g := g) (hpa := hpa) (s := s) hac hlt2)
    · exact Fin.ext (Nat.le_antisymm (Nat.le_of_not_lt hlt2) hle)





/-- **覆盖时 `idxOfE` 必为 `some`**（`none` 形态的排除式）。

    比 `idxOfE_cover` 多说了：后者给「存在下标」，本条给「不是 `none`」的直接形态。 -/
theorem idxOfE_never_none {W : Type u} (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (l : List W) (v : W) (hv : v ∈ l) :
    ∀ h : idxOfE eq v l = none, False := by
  intro h
  obtain ⟨j, hj⟩ := idxOfE_cover eq heq v l hv
  rw [h] at hj
  exact none_ne_some' hj

/-- **`Option` 里取下标**：`idxOfE` 的 `Option` 结果在 `None` 情形下补 `⟨0, _⟩`。

    比 `idxOfE` 的定义多说了：它给出一条**不依赖 `hv`** 的等式
    （`idxOfE_toFin_spec`），于是「复合映射的像相同 ⟹ 原像相同」的链条不会
    被「覆盖性证明」这种 `Prop` 论据卡住 —— 这是 `match h :` 型定义做不到的。
    而且它是**全函数**：`pigeonhole` 需要 `f : α → Fin n` 处处有定义。 -/
def idxOfE_toFin {W : Type u} (eq : W → W → Bool) (l : List W) (v : W) (hpos : 0 < l.length) :
    Fin l.length :=
  match idxOfE eq v l with
  | some k => k
  | none => ⟨0, hpos⟩

/-- **覆盖时 `idxOfE_toFin` 恰是 `idxOfE` 给出的下标**。

    比 `idxOfE_toFin` 的定义多说了：把「提取」与「命中」对上，
    于是「复合映射的像相同」可以一路推回「`idxOfE` 的下标相同」。 -/
theorem idxOfE_toFin_spec {W : Type u} (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (l : List W) (v : W) (hpos : 0 < l.length)
    {k : Fin l.length} (hk : idxOfE eq v l = some k) :
    idxOfE_toFin eq l v hpos = k := by
  unfold idxOfE_toFin
  rw [hk]

/-- **核心引理：覆盖 + 无环 ⟹ 不可能每点都有父**（「回溯撞鸽笼」）。

    比 `Acyclic` 的定义多说了：它把一个**纯逻辑**假设（无环）翻译成一条**长度不等式**，
    这正是 T27 `pigeonhole` 能接手的地方。取覆盖表的头 `s`：
    `Fin (verts.length + 1)` 的全体枚举经 `chain` 得 `verts.length + 1` 个两两不同的点
    （无环保证，`chain_fin_inj`），再经覆盖表给出的单射 `idxOfE_toFin` 压进
    `Fin verts.length`，仍两两不同 —— 与 `length_le_of_nodup_fin` 的
    `length ≤ verts.length` 相撞（`verts.length + 1 > verts.length`）。 -/
theorem not_all_parent {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (hac : Acyclic g) (s : W) (ss : List W)
    (hcover : ∀ v, v ∈ s :: ss) (hpa : ∀ v, g.pa v ≠ []) : False := by
  let V : List W := s :: ss
  have hpos : 0 < V.length := Nat.zero_lt_succ ss.length
  have hinj : ∀ i j : Fin (ss.length + 2),
      chain g hpa s i.val = chain g hpa s j.val → i = j :=
    fun i j hij => chain_fin_inj g hpa s hac i j hij
  -- 复合映射：`Fin (n+1)` → `Fin verts.length`
  have key : ∀ k : Fin (ss.length + 2),
      idxOfE eq (chain g hpa s k.val) V = some (idxOfE_toFin eq V (chain g hpa s k.val) hpos) := by
    intro k
    obtain ⟨j, hj⟩ := idxOfE_cover eq heq (chain g hpa s k.val) V (hcover _)
    rw [idxOfE_toFin_spec eq heq V _ hpos hj]
    exact hj
  have hnodup : (FateV2.Core.mmap (fun k : Fin (ss.length + 2) =>
      idxOfE_toFin eq V (chain g hpa s k.val) hpos) (enumFin (ss.length + 2))).Nodup := by
    refine FateV2.Core.nodup_mmap_of_inj _ _ (enumFin_nodup _) ?_
    intro x _ y _ hxy
    refine hinj x y (idxOfE_inj eq heq V (key x) ?_)
    rw [hxy]
    exact key y
  have hV : V.length = ss.length + 1 := rfl
  have hlen : (FateV2.Core.mmap (fun k : Fin (ss.length + 2) =>
      idxOfE_toFin eq V (chain g hpa s k.val) hpos) (enumFin (ss.length + 2))).length
        ≤ V.length :=
    length_le_of_nodup_fin V.length _ hnodup
  rw [FateV2.Core.mmap_length, enumFin_length, hV] at hlen
  exact Nat.not_succ_le_self (ss.length + 1) hlen

/-- **任意类型上的「无环 ⟹ 有源点」**（主定理，零公理）。

    比 `HasSource` 的定义多说了：**它一定存在** —— 而 `Acyclic g → HasSource g`
    对任意 `V` 并不无条件成立（需有限性），本定理把这份有限性写成显式覆盖列表。
    顶点类型是**任意** `V`（不再限于 `Fin (m+1)`），完全不碰
    `Fintype` / `Finset` / `Fintype.card`；`Fin 0` 那类「空顶点集」退化也随之消失 ——
    覆盖列表非空即可，再无 `m+1` 限制。

    收尾用 `decSourceIn`（手写可判定）+ `of_not_not_dec` **构造性**完成，
    不经 `Classical.choice` / `by_contra`。 -/
theorem source_exists_of_cover {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (hac : Acyclic g) (verts : List W)
    (w0 : W) (hcover : ∀ v, v ∈ verts) (hnd : verts.Nodup) : HasSource g := by
  have hnn : ¬ ¬ HasSourceIn g verts := by
    intro hnot
    have hpa : ∀ v, g.pa v ≠ [] := fun v hv => hnot ⟨v, hcover v, hv⟩
    cases verts with
    | nil =>
        -- `verts = []`：`hcover w0 : w0 ∈ []` 与 `List.not_mem_nil` 直接相撞
        exact List.not_mem_nil (hcover w0)
    | cons s ss => exact not_all_parent g eq heq hac s ss hcover hpa
  exact hasSource_of_hasSourceIn (@of_not_not_dec (HasSourceIn g verts)
    (decSourceIn g verts) hnn)


/-! ## 八、拓扑序存在性（任意类型） -/

/-- **`nth` 有值 ⟹ 该值在列表里**（手写，零公理）。 -/
theorem mem_of_nth' {W : Type u} : ∀ (l : List W) (i : Nat) (v : W), nth l i = some v → v ∈ l
  | [], _, _, h => by cases h
  | x :: xs, 0, v, h => by
      have hvx : x = v := some_inj h
      rw [← hvx]
      exact List.mem_cons_self ..
  | x :: xs, k + 1, v, h => List.mem_cons_of_mem x (mem_of_nth' xs k v h)

/-- **有源点时的拓扑序拼接**（T1 `topo_cons_of_source` 的「无类型类」版）。

    比 T1 的 `topo_cons_of_source` 多说了：那条带 `[DecidableEq V]` 并使用 `by_cases`，
    在任意 `V` 上拿不到该实例（`Classical.decEq` 带三公理）。本条把「`v = src` 与否」
    作为**假设**（`hsplit`）交给调用处 —— 调用处用显式 `eq` 数据即可，仍然零公理。 -/
theorem topo_cons_of_source' {W : Type u} {g : Graph W} {src : W} {rest : List W}
    (hsrc : g.pa src = [])
    (hcover : ∀ v, v ≠ src → v ∈ rest)
    (hsplit : ∀ v, v = src ∨ v ≠ src)
    (hedge : ∀ a b, b ∈ g.pa a → a ≠ src → ∀ i j,
        nth rest i = some a → nth rest j = some b → j < i) :
    IsTopoOrder g (src :: rest) := by
  have hsrcempty : ∀ b, b ∉ g.pa src := by
    intro b hb
    rw [hsrc] at hb
    exact List.not_mem_nil hb
  constructor
  · intro v
    cases hsplit v with
    | inl hv => subst hv; exact List.mem_cons_self ..
    | inr hv => exact List.mem_cons_of_mem src (hcover v hv)
  · intro a b hb i j hi hj
    cases i with
    | zero =>
        have ha : src = a := some_inj hi
        exact absurd (mem_pa_congr ha hb) (hsrcempty b)
    | succ i' =>
        cases j with
        | zero => exact Nat.zero_lt_succ i'
        | succ j' =>
            have hi' : nth rest i' = some a := hi
            have hj' : nth rest j' = some b := hj
            have ha : a ≠ src := by
              intro he
              exact absurd (mem_pa_congr he.symm hb) (hsrcempty b)
            exact Nat.succ_lt_succ (hedge a b hb ha i' j' hi' hj')



end FateV2.Model
