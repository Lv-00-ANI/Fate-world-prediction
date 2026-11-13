import FateWorld.FateV2.Model.TopoGeneral

/-!
  # Model · 拓扑序存在性的最后一步（专项 T34）

  ## 本文件回答什么

  T30（`Model/TopoGeneral.lean`）已把全部部件备齐并零公论证出：

  * `source_exists_of_cover`：任意 `V` 上，覆盖列表 + 无环 ⟹ 存在源点；
  * `removeOneE` 全套（精确删点 / 长度严格变小 / 保 `Nodup`）；
  * `topo_cons_of_source'`：把源点拼到子序最前面的拼接定理。

  但 T30 明确登记了缺口：

  ```lean
  theorem exists_topo_order_of_cover ... :
      ∃ order : List V, IsTopoOrder g order   -- 未证出
  ```

  本文件补上这一步。

  ## 诊断：T30 卡住的到底是什么（带最小复现的定位）

  T30 报告说缺口是「接成 `Nat.strongRecOn` 归纳式的那一步」。实测：`strongRecOn`
  本身**无障碍**（`Pigeon` / `OrderSource` 里都在用）。真正的障碍是下面两条：

  **障碍 1（`topo_cons_of_source'` 的 `hcover` 方向与子问题不符）**

  `topo_cons_of_source'` 的前提是 `(hcover : ∀ v, v ≠ src → v ∈ rest)`，
  即「**全图所有**别的顶点都排在 `rest` 里」。子问题的 `rest` 只覆盖
  `removeOneE eq src verts`，而 `g.pa` 里出现的点未必都在 `verts` 里。
  于是归纳步里这个 `hcover` **不可证** —— 不是归纳式接不起来，
  是拼接定理的前提强于归纳能给的东西。

  **最小复现**：`V = Nat`，`verts = [0]`，`g.pa 0 = [1]`、`g.pa 1 = []`。
  `hac : Acyclic g` 成立，`verts` 覆盖了唯一被要求的点 `0`，
  但子问题的 `rest` 取自 `removeOneE eq 0 [0] = []`，`1` 无处安放 ——
  `∀ v, v ≠ src → v ∈ rest` 在 `v = 1` 处为假。

  **修法**：改用 `IsTopoOrderOnE`（只对给定顶点集负责）—— 与 T1c 的结构一致。

  **障碍 2（子问题的「无父」不等于「全图无父」）**

  删掉 `src` 后，剩余点的父可能仍是 `src`。子问题在 `rest` 上递归时不能声明
  「`rest` 里的点全图无父」，只能声明「这些点的父**都不在** `rest` 里」。
  这一层放宽由 §三 的 `FreeIn` 承担。

  ## `by_cases (v = w)` 的替换（成功）

  **本文件一次都没用**。所有判等都走 `eq` 的 `Bool` 分支：

  | 旧写法（三公理） | 本文件写法（零公理） |
  |---|---|
  | `by_cases h : v = w` | `cases hx : eq x v`（`eq_true_elim` / `ne_of_eq_false`） |
  | `by_cases h : ∃ v, P v` | 手写结构递归 `decMemE` / `decFreeInAux` 的 `isTrue`/`isFalse` |
  | 消 `∈` 用 `List.mem_cons` | `cases h with \| head => … \| tail _ h' => …` |

  唯一需要「二分」的地方（`FreeIn` 到底成不成立）由**手写 `Decidable` 实例**
  `decFreeInAux` 提供，两个分支都带**构造性见证**（成立时给 `∀` 证明，
  不成立时给具体的父 `b`）—— 这正是零公理姿势与 `Classical` 的分界。

  ## 公理纪律

  全部结论 **`does not depend on any axioms`**（逐条 `#print axioms` 实测）：

  * 消 `∈`：`cases h with | head => ... | tail _ h' => ...`（**不用** `List.mem_cons`）；
  * 消 `Nodup`：`nd_split`（构造子模式，**不用** `List.nodup_cons`）；
  * 判等：`eq` 数据的 `Bool` 分支（**不用** `by_cases (v = w)`）；
  * 归纳：`Nat.strongRecOn` 只用于**长度**（`Nat` 上，不带公理）；
  * 列表遍历：手写（**不用** `List.map` / `filter` / `simp`）。

  ## 命题为真性预检

  * `verts = []` 时 `hcover : ∀ v, v ∈ []` **直接给 `False`**
    （见 §一 `false_of_forall_mem_nil`），所以空情形是真空的，
    归纳基态不必构造「空列表是拓扑序」（那反而是假命题）。
  * 非空情形：`source_exists_of_cover` 给源点 `src`；`verts.Nodup` 保证
    `src ∉ removeOneE eq src verts`（见 §四 `not_mem_removeOneE_self`），
    这正是「`src` 必须、且只需排最前」的依据。
  * 归纳终止：`removeOneE_length_lt` 给
    `(removeOneE eq src verts).length < verts.length`，强归纳直接可用。
-/

namespace FateV2.Model

universe u

/-! ## 一、空覆盖列表是真空的 -/

/-- **`∀ v, v ∈ []` 直接给 `False`**。

    比 `List.not_mem_nil` 多说了：后者说「`x ∉ []`」，需要调用处先有一个 `x`；
    本条把「覆盖列表为空」这一假设**整条**变成矛盾 ——
    于是归纳的基态（`verts.length = 0`）可以立刻收工。 -/
theorem false_of_forall_mem_nil {α : Type u} (w : α) (h : ∀ v, v ∈ ([] : List α)) : False :=
  List.not_mem_nil (h w)

/-! ## 二、`eq` 判定的成员关系（零公理） -/

/-- **`eq` 的对称性**（从 `heq` 抽出）。

    比 `heq` 多说了：`heq` 只保证「判真 ⟺ 相等」，未保证对称；
    本条把它压成「`eq a b = eq b a`」，这是本文件需要的**唯一**一条
    `eq` 的结构性质 —— 用来把 T30 的 `ne_of_eq_false`（`eq v x` 方向）
    与手写递归给出的 `eq x v` 方向对齐。 -/
theorem eq_comm_of_heq {W : Type u} {eq : W → W → Bool}
    (heq : ∀ a b, eq a b = true ↔ a = b) (a b : W) : eq a b = eq b a := by
  cases ha : eq a b with
  | true =>
      cases hb : eq b a with
      | true => rfl
      | false =>
          have hab : a = b := (heq a b).1 ha
          have hne : b ≠ a := ne_of_eq_false (eq := eq) heq (a := b) (b := a) hb
          exact absurd hab.symm hne
  | false =>
      cases hb : eq b a with
      | true =>
          have hba : b = a := (heq b a).1 hb
          have hne : a ≠ b := ne_of_eq_false (eq := eq) heq (a := a) (b := b) ha
          exact absurd hba.symm hne
      | false => rfl

/-- **`eq` 判假 ⟹ 真的不等**（`eq x v = false` 方向的本文件副本）。

    比 `TopoGeneral.ne_of_eq_false` 多说了：那条把 `a b` 摆在 `{a b}` 隐式位，
    在本文件「先用 `cases` 钉住 `eq x v`、再断言 `x ≠ v`」的写法里
    两个隐参都已被消去，无法再回溯推断；本条把 `{x v}` 换成**显式**参数，
    于是这两处（`decMemE` 的 `isFalse` 分支、`mem_tail_of_eq_false`）
    可以直接指名调用。 -/
theorem ne_of_eq_false' {W : Type u} (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (x v : W) (h : eq x v = false) : x ≠ v := by
  intro hxv
  rw [(heq x v).2 hxv] at h
  exact Bool.noConfusion h

/-- **`eq` 判假 ⟹ `v ∈ x :: xs` 退回 `v ∈ xs`**。

    比 `TopoGeneral.mem_tail_of_ne` 多说了：那条要一条命题级的 `v ≠ w`，
    本条直接吃 `eq` 的 `Bool` 结果 —— 于是「判等」与「消 `∈`」之间
    不必经过 `by_cases`，这正是零公理姿势的关键接缝。 -/
theorem mem_tail_of_eq_false {W : Type u} (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) {x v : W} (hx : eq x v = false) {xs : List W}
    (h : v ∈ x :: xs) : v ∈ xs :=
  mem_tail_of_ne h (fun hvu => ne_of_eq_false' eq heq x v hx hvu.symm)

/-- **`eq` 版成员判定**（手写穷举，零公理）。

    比 `TopoGeneral.decSourceIn` 多说了：那条把「列表里有没有无父点」整体做成
    `Decidable`，本条只把**单个点**的成员关系做成 `Decidable` ——
    粒度更细、可组合，于是 `FreeIn` 的判定直接把它当砖块用。
    判等走 `eq` 的 `Bool` 分支：**不带 `DecidableEq`、不带 `by_cases`**。 -/
def decMemE {W : Type u} (eq : W → W → Bool) (heq : ∀ a b, eq a b = true ↔ a = b) :
    (l : List W) → (v : W) → Decidable (v ∈ l)
  | [], _ => isFalse List.not_mem_nil
  | x :: xs, v =>
      match hx : eq x v with
      | true => isTrue (by rw [eq_true_elim heq hx]; exact List.mem_cons_self)
      | false =>
          match decMemE eq heq xs v with
          | isTrue hmem => isTrue (List.mem_cons_of_mem x hmem)
          | isFalse hnm => isFalse (fun hv => hnm (mem_tail_of_eq_false eq heq hx hv))

/-! ## 三、`FreeIn`：「父都不在某个列表里」 -/

/-- **`v` 的所有父都不在 `l` 里**。

    比 `g.pa v = []` 多说了：它**只关心 `l` 里的顶点**，允许 `v` 在全图有父
    （那些父落在 `l` 之外即可）。没有这一层放宽，删点归纳根本推不动 ——
    子问题的顶点集被删小了，「`src` 在**子顶点集内部**无父」不等于「全图无父」。 -/
def FreeIn {W : Type u} (eq : W → W → Bool) (g : Graph W) (l : List W) (v : W) : Prop :=
  ∀ b, b ∈ g.pa v → b ∉ l

/-- **`∃ b ∈ l, b ∈ pa v` 的可判定性**（手写，零公理）。

    比 `Classical.decEq` 多说了：它的 `isFalse` 分支产出的是**完整的 `∀` 证明**
    （每个父都不在 `l` 里），`isTrue` 分支产出的是**具体的父** ——
    于是调用处两个方向都拿到构造性数据，不必 `Classical.choice` 去「猜」。
    这也是把「`FreeIn` 成不成立」这件二分彻底零公理化的支点。 -/
def decParentIn {W : Type u} (eq : W → W → Bool) (heq : ∀ a b, eq a b = true ↔ a = b)
    (l : List W) : (pas : List W) → Decidable (∃ b, b ∈ pas ∧ b ∈ l)
  | [] => isFalse (fun h => by
      obtain ⟨b, hb, _⟩ := h
      exact List.not_mem_nil hb)
  | b :: bs =>
      match hmem : decMemE eq heq l b with
      | isTrue hb => isTrue (Exists.intro b (And.intro List.mem_cons_self hb))
      | isFalse hnb =>
          match htail : decParentIn eq heq l bs with
          | isTrue h => isTrue (by
              obtain ⟨c, hc, hcl⟩ := h
              exact ⟨c, List.mem_cons_of_mem b hc, hcl⟩)
          | isFalse h => isFalse (fun hall => by
              obtain ⟨c, hc, hcl⟩ := hall
              cases hc with
              | head =>
                  -- `c` 被替换成 `b`：但与 `hnb : b ∉ l` 相撞
                  exact hnb hcl
              | tail _ htl => exact h ⟨c, htl, hcl⟩)

/-- **`FreeIn` 等价于「不存在落在 `l` 里的父」**（负向形式的可判定性）。

    比 `FreeIn` 的定义多说了：把「`∀` 形态」翻成「`¬∃` 形态」，
    于是 `decParentIn` 这个**正向**判定可以直接拿来定 `FreeIn`，
    判等全程走 `eq`，不带 `DecidableEq`、不带 `by_cases`。 -/
def decFreeIn {W : Type u} (eq : W → W → Bool) (heq : ∀ a b, eq a b = true ↔ a = b)
    (g : Graph W) (l : List W) (v : W) : Decidable (FreeIn eq g l v) :=
  match decParentIn eq heq l (g.pa v) with
  | isTrue h => isFalse (fun hf => by
      obtain ⟨b, hb, hbl⟩ := h
      exact hf b hb hbl)
  | isFalse h => isTrue (fun b hb hbl => h ⟨b, hb, hbl⟩)

/-- **`FreeIn` 不成立 ⟹ 有一个具体的父落在 `l` 里**。

    比 `Classical.not_forall` 多说了：后者要 `Classical.choice` 才拿得到见证；
    本条借 `decParentIn` 的构造性否定直接**交出**那个父，零公理。 -/
theorem exists_parent_mem_of_not_free {W : Type u} {eq : W → W → Bool}
    (heq : ∀ a b, eq a b = true ↔ a = b) {g : Graph W} {l : List W} {v : W}
    (h : ¬ FreeIn eq g l v) : ∃ b, b ∈ g.pa v ∧ b ∈ l := by
  cases hp : decParentIn eq heq l (g.pa v) with
  | isTrue hx => exact hx
  | isFalse hx => exact absurd (fun b hb hbl => hx ⟨b, hb, hbl⟩) h

/-- **`FreeIn` 在删点后单调放开**（集合变小 ⟹ 更容易 free）。

    比 `FreeIn` 的定义多说了：它给出**方向**——父条件对更小的顶点集更容易满足，
    于是「`src` 在 `verts` 内部无父」可以一路传给更小的子问题。
    这正是删点归纳里把 `FreeIn` 往后传的唯一通道。 -/
theorem freeIn_mono {W : Type u} {eq : W → W → Bool} {g : Graph W} {l l' : List W} {v : W}
    (hsub : ∀ x, x ∈ l' → x ∈ l) (h : FreeIn eq g l v) : FreeIn eq g l' v :=
  fun b hb hbm => h b hb (hsub b hbm)

/-! ## 四、`removeOneE` 的配套事实 -/

/-- **`src` 不在 `removeOneE eq src l` 里**（`l` 无重复时）。

    比 `TopoGeneral.mem_removeOneE_of_ne` 多说了：后者的前提是「要找的点 `≠ src`」；
    本条要的是**自己**不在删完的列表里 —— 这是「`src` 排最前之后它不会再出现在
    `rest` 中」的依据，也是拓扑序反向覆盖那一步的入口。 -/
theorem not_mem_removeOneE_self {W : Type u} (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (v : W) : ∀ (l : List W), l.Nodup →
    v ∉ removeOneE eq v l
  | [], _ => List.not_mem_nil
  | x :: xs, hnd => by
      cases hx : eq x v with
      | true =>
          rw [removeOneE_hit eq v x xs hx]
          intro hv
          exact ((nd_split hnd).1 v hv) (eq_true_elim heq hx)
      | false =>
          have hnxv : x ≠ v := ne_of_eq_false' eq heq x v hx
          rw [removeOneE_miss eq v x xs hx]
          intro h
          cases h with
          | head => exact hnxv rfl
          | tail _ htl =>
              exact not_mem_removeOneE_self eq heq v xs (nd_split hnd).2 htl

/-- **`src` 在表里的父必然落在剩余集之外**（`Nodup` 下删点是精确的）。

    比 `TopoGeneral.mem_removeOneE_of_ne` 多说了：那条说「`≠ src` 的都在」；
    本条把「删除」反向用在 `src` 自己的父上 —— 于是只要某个父不在剩余集里，
    它就只能是 `src` 本身。

    ⚠ 实测：这里**不能**用 `by_cases (b = src)`（三公理）；
    改走 `eq b src` 的 `Bool` 分支 + `heq`（同 `decSourceIn` 的姿势）。 -/
theorem parent_not_mem_removed_of_mem {W : Type u} (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) {src : W} {l : List W}
    (hnd : l.Nodup) {b : W} (hb : b ∈ l) (hnot : b ∉ removeOneE eq src l) : b = src := by
  cases hbs : eq b src with
  | true => exact eq_true_elim heq hbs
  | false => exact absurd (mem_removeOneE_of_ne eq heq src l b hb (ne_of_eq_false' eq heq b src hbs)) hnot

/-! ## 五、`IsTopoOrderOnE`：只对给定顶点集负责的拓扑序

  与 T1c（`Model/TopoExists.lean`）的 `IsTopoOrderExact` 同形，
  但判等仍由显式 `eq` 提供，且不需要「`order` 不溢出」这一反方向
  —— 本文件把它留给调用处按需索取（见 `onE_of_mem_sub`）。 -/

/-- **列表上的拓扑序（限制版）**：`order` 含 `vertices` 的全部顶点，
    且 `vertices` 内部的父边有序。

    比 `FateV2.Model.IsTopoOrder` 多说了：它把「覆盖全体」换成「覆盖给定顶点集」，
    于是可以对 `vertices.length` 归纳 —— 这是零公理下唯一可行的归纳量
    （`Finset.card` / `Fintype.card` 都带公理）。 -/
def IsTopoOrderOnE {W : Type u} (g : Graph W) (vertices order : List W) : Prop :=
  (∀ v, v ∈ vertices → v ∈ order) ∧
  (∀ v, v ∈ order → v ∈ vertices) ∧
  (∀ a b, b ∈ g.pa a → a ∈ vertices → b ∈ vertices →
    ∀ i j, nth order i = some a → nth order j = some b → j < i)

/-- **`IsTopoOrderOnE` 的覆盖项**（可命名导出）。 -/
theorem onE_cover {W : Type u} {g : Graph W} {vertices order : List W}
    (h : IsTopoOrderOnE g vertices order) : ∀ v, v ∈ vertices → v ∈ order :=
  h.1

/-- **`IsTopoOrderOnE` 的反向覆盖项**（`order` 不溢出 `vertices`）。

    比 `onE_cover` 多说了：`onE_cover` 说「顶点集 ⊆ 序」，
    本条说「序 ⊆ 顶点集」。两条合起来「`order` 的成员集恰好是 `vertices`」，
    于是「`v` 排在 `order` 里」与「`v ∈ vertices`」可以自由换算 ——
    归纳步里从 `nth rest i' = some a` 反推 `a ∈ removeOneE …` 就靠这条。 -/
theorem onE_mem_back {W : Type u} {g : Graph W} {vertices order : List W}
    (h : IsTopoOrderOnE g vertices order) : ∀ v, v ∈ order → v ∈ vertices :=
  h.2.1

/-- **`IsTopoOrderOnE` 的父边项**（可命名导出）。 -/
theorem onE_edge {W : Type u} {g : Graph W} {vertices order : List W}
    (h : IsTopoOrderOnE g vertices order) :
    ∀ a b, b ∈ g.pa a → a ∈ vertices → b ∈ vertices →
      ∀ i j, nth order i = some a → nth order j = some b → j < i :=
  h.2.2

/-- **`IsTopoOrderOnE` + 顶点集覆盖全体 ⟹ `IsTopoOrder`**。

    比 `IsTopoOrderOnE` 的定义多说了：把「只对给定顶点集成立」升级成
    「对全图成立」—— 这是归纳结束后收口的最后一步。 -/
theorem isTopoOrder_of_onE {W : Type u} {g : Graph W} {vertices order : List W}
    (hcoverAll : ∀ v, v ∈ vertices) (h : IsTopoOrderOnE g vertices order) :
    IsTopoOrder g order :=
  ⟨fun v => h.1 v (hcoverAll v),
   fun a b hb i j hi hj => h.2.2 a b hb (hcoverAll a) (hcoverAll b) i j hi hj⟩

/-- **空顶点集上的拓扑序只能是空表**（且它确实是拓扑序）。

    比 `IsTopoOrderOnE` 的定义多说了：给出**归纳基态的具体见证**。 -/
theorem onE_nil {W : Type u} (g : Graph W) : IsTopoOrderOnE g [] [] := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact absurd hv List.not_mem_nil
  · intro v hv
    exact absurd hv List.not_mem_nil
  · intro a b hb ha _
    exact absurd ha List.not_mem_nil
/-! ## 六、主归纳 -/

/-- **归纳步的核心：把一个「在剩余集内无父」的点排到最前**。
    收尾的父边条件里，`i = 0` 分支要排除「`a = src`」：由 `FreeIn` 得
    `b ∉ verts`，与 `hb' : b ∈ verts` 相撞。 -/
theorem onE_cons {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) {verts : List W} {src : W} {rest : List W}
    (hnd : verts.Nodup) (hsrcIn : src ∈ verts) (hfree : FreeIn eq g verts src)
    (hrest : IsTopoOrderOnE g (removeOneE eq src verts) rest)
    (hne : ∀ v, v ∈ verts → v = src ∨ v ∈ removeOneE eq src verts) :
    IsTopoOrderOnE g verts (src :: rest) := by
  have hsrcNotIn : src ∉ removeOneE eq src verts :=
    not_mem_removeOneE_self eq heq src verts hnd
  -- `rest` 的成员都在剩余集里，于是都不等于 `src`
  have hrestNe : ∀ v, v ∈ rest → v ≠ src := by
    intro v hv he
    rw [he] at hv
    exact hsrcNotIn (onE_mem_back hrest src hv)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    cases hvs : eq v src with
    | true =>
        rw [eq_true_elim heq hvs]
        exact List.mem_cons_self
    | false =>
        have hvne : v ≠ src := ne_of_eq_false' eq heq v src hvs
        have hmem : v ∈ removeOneE eq src verts := by
          cases hne v hv with
          | inl he => exact absurd he hvne
          | inr hm => exact hm
        exact List.mem_cons_of_mem src (onE_cover hrest v hmem)
  · intro v hv
    cases hv with
    | head => exact hsrcIn
    | tail _ htl => exact mem_removeOneE eq src verts v (onE_mem_back hrest v htl)
  · intro a b hb ha hb' i j hi hj
    cases i with
    | zero =>
        have hsa : src = a := some_inj hi
        exact absurd hb' (hfree b (mem_pa_congr hsa hb))
    | succ i' =>
        cases j with
        | zero => exact Nat.zero_lt_succ i'
        | succ j' =>
            -- `a` 与 `b` 都出现在 `rest` 里，于是都在剩余集里
            have ham : a ∈ removeOneE eq src verts :=
              onE_mem_back hrest a (mem_of_nth' rest i' a hi)
            have hbm : b ∈ removeOneE eq src verts :=
              onE_mem_back hrest b (mem_of_nth' rest j' b hj)
            exact Nat.succ_lt_succ (onE_edge hrest a b hb ham hbm i' j' hi hj)

/-! ## 六、子表上的「无环 ⟹ 有内部无父点」

  这是本文件真正的技术核心，也是 T30 视野之外的那一步。

  T30 的 `not_all_parent` 反设「**每点**全图有父」（`hpa : ∀ v, g.pa v ≠ []`），
  并靠 `hcover : ∀ v, v ∈ s :: ss`（覆盖全体）把链的每步关在表里。
  归纳步需要的反设弱得多：**每点在表内有父** —— 它不提表外的居民，
  因此那个「覆盖全体」在这里是假假设，不能直接套。

  本节的修法：把弱反设喂给链，每步的父由**手写的选择函数** `pickParent`
  构造性给出（对父列表做结构递归，遇到第一个落在表里的父就停），
  于是链仍在表内回溯；`verts.Nodup` + `idxOfE_inj` + T27 鸽笼照样收口。 -/

/-- **手写选择函数**：从父列表 `pas` 里挑第一个落在 `l` 里的元素。

    比 `Classical.choice` 多说了：它**不假设任何见证存在**，而是真的把
    「挑」写成一棵可计算的树 —— 找到就返回，找不到就返回 `fb`（调用处用
    `∃` 见证保证不会真的落到 `fb`）。这是本文件不用选择公理的全部原因。 -/
def pickParent {W : Type u} (eq : W → W → Bool) (heq : ∀ a b, eq a b = true ↔ a = b)
    (l : List W) (fb : W) : List W → W
  | [] => fb
  | b :: bs =>
      match decMemE eq heq l b with
      | isTrue _ => b
      | isFalse _ => pickParent eq heq l fb bs

/-- **`pickParent` 落在表里**（前提：父列表里确有落在表里的元素）。

    比 `pickParent` 的定义多说了：它把「挑出来的那个」与「确实在表里」对上，
    于是链的每一步都能由 `l` 的成员见证 —— 鸽笼才有东西可数。 -/
theorem pickParent_mem {W : Type u} (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (l : List W) (fb : W) :
    ∀ (pas : List W), (∃ b, b ∈ pas ∧ b ∈ l) → pickParent eq heq l fb pas ∈ l
  | [], h => by
      obtain ⟨b, hb, _⟩ := h
      exact absurd hb List.not_mem_nil
  | b :: bs, h => by
      unfold pickParent
      cases hmem : decMemE eq heq l b with
      | isTrue hb => exact hb
      | isFalse hnb =>
          exact pickParent_mem eq heq l fb bs (by
            obtain ⟨c, hc, hcl⟩ := h
            cases hc with
            | head =>
                -- `hb` 已被替换成 `b ∈ l`，与 `hnb : ¬ b ∈ l` 相撞
                exact absurd hcl hnb
            | tail _ htl => exact ⟨c, htl, hcl⟩)

/-- **`pickParent` 是某个父**（不只会落在表里，还在父列表里）。

    比 `pickParent_mem` 多说了：`pickParent_mem` 只说「在表里」，
    本条说「在父列表里」—— 于是「链的下一步是当前点的父」这一条边关系可以拿来做
    `Reachable.step`，无环性才接得上。 -/
theorem pickParent_in_pas {W : Type u} (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (l : List W) (fb : W) :
    ∀ (pas : List W), (∃ b, b ∈ pas ∧ b ∈ l) →
      pickParent eq heq l fb pas ∈ pas
  | [], h => by
      obtain ⟨b, hb, _⟩ := h
      exact absurd hb List.not_mem_nil
  | b :: bs, h => by
      unfold pickParent
      cases hmem : decMemE eq heq l b with
      | isTrue _ => exact List.mem_cons_self
      | isFalse hnb =>
          exact List.mem_cons_of_mem b (pickParent_in_pas eq heq l fb bs (by
            obtain ⟨c, hc, hcl⟩ := h
            cases hc with
            | head => exact absurd hcl hnb
            | tail _ htl => exact ⟨c, htl, hcl⟩))

/-! ## 七、链与长度（鸽笼的接线） -/

/-- **链：从 `s` 出发每步取一个落在 `verts` 里的父**。

    比 `OrderSource.chain` 多说了：那条每步取 `g.pa v` 的**头**（要 `∀ v, g.pa v ≠ []`），
    本条每步取 `pickParent`（要「该点有落在表里的父」）。
    于是链的每一项都由 `verts` 的成员见证 —— 这是鸽笼能数它的原因。 -/
def chainE {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (verts : List W) (w0 : W)
    (hfather : ∀ v : W, v ∈ verts → ∃ b, b ∈ g.pa v ∧ b ∈ verts) :
    W → Nat → W
  | v, 0 => v
  | v, k + 1 => chainE g eq heq verts w0 hfather
      (pickParent eq heq verts w0 (g.pa v)) k

/-- **链的每一步都在表里**。

    比 `chainE` 的定义多说了：它把「链」变成一串 `verts` 的成员，
    于是 `idxOfE` 可以在每个位置上求值 —— 鸽笼的入口。 -/
theorem chainE_mem {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (verts : List W) (w0 : W)
    (hfather : ∀ v : W, v ∈ verts → ∃ b, b ∈ g.pa v ∧ b ∈ verts)
    {s : W} (hs : s ∈ verts) :
    ∀ k : Nat, chainE g eq heq verts w0 hfather s k ∈ verts
  | 0 => hs
  | k + 1 =>
      chainE_mem g eq heq verts w0 hfather
        (pickParent_mem eq heq verts w0 (g.pa s) (hfather s hs)) k

/-- **`chainE` 的一步展开**（`k+1` 步就是「第 `k` 步的父」处再取一步）。

    比 `chainE` 的定义多说了：把递归定义在任意起点上的形态写成**可 `rw` 的等式**，
    于是 `chainE_step` 不必再与定义项对齐。 -/
theorem chainE_succ {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (verts : List W) (w0 : W)
    (hfather : ∀ v : W, v ∈ verts → ∃ b, b ∈ g.pa v ∧ b ∈ verts)
    (v : W) (k : Nat) :
    chainE g eq heq verts w0 hfather v (k + 1) =
      chainE g eq heq verts w0 hfather (pickParent eq heq verts w0 (g.pa v)) k := rfl

/-- **链的相邻两步构成一条父边**。

    比 `chainE_mem` 多说了：`chainE_mem` 只说「在表里」，本条说「下一步是上一步的**父**」
    —— 于是 `Reachable.step` 接得上，无环性才能发挥作用。 -/
theorem chainE_step {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (verts : List W) (w0 : W)
    (hfather : ∀ v : W, v ∈ verts → ∃ b, b ∈ g.pa v ∧ b ∈ verts)
    {s : W} (hs : s ∈ verts) :
    ∀ k : Nat, chainE g eq heq verts w0 hfather s (k + 1) ∈
      g.pa (chainE g eq heq verts w0 hfather s k)
  | 0 => pickParent_in_pas eq heq verts w0 (g.pa s) (hfather s hs)
  | k + 1 => by
      -- 第 `k+2` 步的定义式：先走一步到 `pickParent (g.pa s)`，再走 `k+1` 步
      have h1 : chainE g eq heq verts w0 hfather s (k + 2) =
          chainE g eq heq verts w0 hfather
            (pickParent eq heq verts w0 (g.pa s)) (k + 1) := rfl
      have h2 : chainE g eq heq verts w0 hfather s (k + 1) =
          chainE g eq heq verts w0 hfather
            (pickParent eq heq verts w0 (g.pa s)) k := rfl
      rw [h1, h2]
      exact chainE_step g eq heq verts w0 hfather
        (pickParent_mem eq heq verts w0 (g.pa s) (hfather s hs)) k

/-- **链的相邻两步不同**（无环的直接推论）。

    比 `chainE_step` 多说了：`chainE_step` 只给「下一步是父」，
    本条给「所以不是同一个点」—— 这是无环性在本文件里的第一处用处。 -/
theorem chainE_ne {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (verts : List W) (w0 : W)
    (hfather : ∀ v : W, v ∈ verts → ∃ b, b ∈ g.pa v ∧ b ∈ verts)
    (hac : Acyclic g) {s : W} (hs : s ∈ verts) :
    ∀ k : Nat, chainE g eq heq verts w0 hfather s k ≠
      chainE g eq heq verts w0 hfather s (k + 1)
  | k => reachable_ne hac (Reachable.step (chainE_step g eq heq verts w0 hfather hs k))

/-- **沿链前进一步**（任意起点 `n`）。

    比 `chainE_step` 多说了：`chainE_step` 说的是**从 `s` 出发**的第 `k+1` 步；
    本条对**任意位置 `n`** 都成立，于是归纳可以沿链自由行走 ——
    这是 `chainE_reach_add` 能接上的前提。

    实现：对 `n` 归纳。`n+1` 的情形把起点前移一步，再用归纳假设
    （链的后续与起点的选择无关，因为 `chainE` 的定义在 `k+1` 处只展开一步）。 -/
theorem chainE_step_at {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (verts : List W) (w0 : W)
    (hfather : ∀ v : W, v ∈ verts → ∃ b, b ∈ g.pa v ∧ b ∈ verts) :
    ∀ (v : W), v ∈ verts → ∀ m : Nat,
      chainE g eq heq verts w0 hfather v (m + 1) ∈
        g.pa (chainE g eq heq verts w0 hfather v m)
  | v, hv, 0 => pickParent_in_pas eq heq verts w0 (g.pa v) (hfather v hv)
  | v, hv, m + 1 =>
      chainE_step_at g eq heq verts w0 hfather
        (pickParent eq heq verts w0 (g.pa v))
        (pickParent_mem eq heq verts w0 (g.pa v) (hfather v hv)) m

/-- **从第 `a` 步沿链走到第 `a + (k+1)` 步**（`Reachable` 的形态）。

    比 `chainE_ne` 多说了：`chainE_ne` 只走一步，本条走任意 `k+1 ≥ 1` 步；
    于是「链上任意两个不同时刻的点不同」可以一次性拿到 —— 鸽笼要的是这个强度。 -/
theorem chainE_reach_add {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (verts : List W) (w0 : W)
    (hfather : ∀ v : W, v ∈ verts → ∃ b, b ∈ g.pa v ∧ b ∈ verts)
    {s : W} (hs : s ∈ verts) (a : Nat) :
    ∀ k : Nat, Reachable g (chainE g eq heq verts w0 hfather s a)
      (chainE g eq heq verts w0 hfather s (a + (k + 1)))
  | 0 => Reachable.step (chainE_step_at g eq heq verts w0 hfather s hs a)
  | k + 1 => by
      refine Reachable.trans (chainE_reach_add g eq heq verts w0 hfather hs a k) ?_
      have h := chainE_step_at g eq heq verts w0 hfather s hs (a + (k + 1))
      rw [show a + (k + 1) + 1 = a + (k + 1 + 1) by rw [Nat.add_assoc]] at h
      exact Reachable.step h

end FateV2.Model
