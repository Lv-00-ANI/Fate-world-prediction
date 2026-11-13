import FateWorld.FateV2.Model.TopoAssembly

/-!
  # Model · 拓扑序存在性的收口（专项 T36）

  ## 本文件回答什么

  T30（`Model/TopoGeneral.lean`）备齐了「判等数据 `eq`」「删点 `removeOneE`」
  「覆盖 ⟹ 源点」；T34（`Model/TopoAssembly.lean`）备齐了「表内回溯链 `chainE`」
  「`FreeIn`」「`IsTopoOrderOnE`」「拼接步 `onE_cons`」。两者差**最后一块砖**：

  ```lean
  theorem not_all_parent_in : ...        -- 子表版鸽笼（T34 卡住处）
  theorem exists_topo_order_of_cover ... -- 主定理（未证出）
  ```

  本文件把这两条都证出，**全部零公理**。

  ## 一、T34 的卡点及其实质（复核结论）

  T34 说：要从 `∃ j, idxOfE … = some j` 里取出 `j` 装成 `Fin verts.length`，
  而 `Exists.casesOn` **不能消到 `Type`**（`propRecLargeElim`），
  于是只想到 `Classical.choice`（三公理）。

  **实质**：T27 的 `pigeonhole` 要的是一个**全函数** `f : W → Fin verts.length`。
  覆盖性 `hcover` 只能证明「这个函数处处取到 `some`」，它本身是 `Prop`，
  不能拿来构造函数的**定义**。T34 用了 `idxOfE_toFin` 之后仍卡住，
  是因为它只想拿到 `some` 那一半的等式，而 `idxOfE_toFin` 在 `none` 分支有兜底值。

  ## 二、解法：把「提取」与「对齐」**分开**

  1. **定义**：函数本体用 T30 已有的 `idxOfE_toFin`（**构造性**，
     `none` 分支给 `⟨0, hpos⟩`）。它是 `Type` 值、处处定义，`∃` 消去一次都不用。
  2. **对齐**：`idxOfE_toFin_spec`（T30）把 `some k` 里的 `k` 与
     `idxOfE_toFin` 的**值**对上 —— 这一条是 `Prop`，但它只服务
     「像相同 ⟹ 下标相同」，不需要构造任何数据。
  3. **单射**：`idxOfE_inj`（T30）把「`idxOfE` 下标相同」翻成「原像相等」。

  合起来：`f x = f y` ⟹ `some (f x) = some (f y)` ⟹
  `idxOfE eq x verts = idxOfE eq y verts` ⟹ `x = y`。
  **全程没有 `∃` 消到 `Type`，也没有 `Classical.choice`。**

  ## 三、归纳不变量（T34 偏差 1 / 2 的正面回答）

  T34 用最小复现指出 `topo_cons_of_source'` 的前提在子问题上为假
  （`verts = [0]`、`pa 0 = [1]`、`pa 1 = []`），**因此递归不能用 `verts` 作为覆盖范围**。
  正确的不变量是三条并列的假设：

  | 分量 | 内容 | 在哪用 |
  |---|---|---|
  | `verts.Nodup` | 顶点表无重复 | 鸽笼（`pigeonhole` 的前提） |
  | `Acyclic g` | 全图无环（**不是**子图无环） | 链的两两不同（`chainE_reach_add` + `reachable_ne`） |
  | `hfather : ∀ v ∈ verts, ∃ b, b ∈ g.pa v ∧ b ∈ verts` | **每个表内点的父也在表内** | 链的推进（`chainE` 的实参） |

  第三条**只对 `verts` 负责**，完全不提表外的居民 —— 这正是 T34 缺的那层放宽。
  它与 T34 已有的 `FreeIn` 互补：`FreeIn eq g verts v` 说「父都不在表内」，
  `hfather` 说「父都在表内」，两者的否定恰好互换（§六 `decFather`）。

  **递归时 `verts` 换成 `removeOneE eq src verts`**：覆盖性由 §四
  `mem_or_mem_removeOneE` 保证（「在表里 ⟹ 是 `src` 或在剩余表里」），
  长度严格变小由 T30 `removeOneE_length_lt` 保证，于是对**长度**归纳终止。
  `topo_cons_of_source'` 的 `∀ v, v ≠ src → v ∈ rest` 从头到尾**不需要** ——
  这正是 T34 偏差 1 指出的那条假前提。

  ## 四、公理纪律（本次实测）

  | 写法 | 实测 |
  |---|---|
  | `idxOfE_toFin` / `idxOfE_toFin_spec` / `idxOfE_inj` / `pigeonhole` | 零公理 ✅ |
  | `chainE_reach_add` / `freeIn_mono` / `onE_cons` | 零公理 ✅ |
  | `by_cases (v = w)` | 三公理 ❗（全文件**零处**，判等一律走 `eq` 的 `Bool` 分支） |
  | `by_contra` | 三公理 ❗（反证只在**已证明可判定**的 `Decidable` 上做，见 `decFather`） |
  | `Exists.casesOn` 消到 `Type` | `propRecLargeElim` ❗（**本文件一次都没用**：`∃` 只消到 `Prop`） |
  | `ac_rfl` / `congr 1` / `simp` | 带 `propext` ❗（本文件改用 `h ▸ …` 与显式 `rw`） |
-/

namespace FateV2.Model

universe u

/-! ## 二、`Nat` 的零公理砖块（替代带 `propext` 的库引理） -/

/-- **`a + 1 + b = (a + b) + 1`**（手写，零公理）。

    比 `Nat.add_assoc` / `Nat.add_comm` 的组合多说了：把「后移一位」写成
    **一条可直接 `rw` 的等式**，两边的形状都是 `Nat` 的构造子（`+ 1` = `succ`），
    于是 `chainE_far` 的位移不需要 `omega` / `simp`（前者不可用，后者带 `propext`）。 -/
theorem add_one_add : ∀ (a b : Nat), a + 1 + b = (a + b) + 1
  | _, 0 => rfl
  | a, b + 1 => congrArg (fun t => t + 1) (add_one_add a b)

/-- **`k < n` ⟹ `∃ j, n = k + (j + 1)`**（零公理，替代带 `propext` 的 `Nat.exists_eq_add_of_lt`）。

    比库引理 `Nat.exists_eq_add_of_lt` 多说了：库版**实测带 `propext`**
    （它经 `Nat.le.dest` 把 `≤` 翻成 `∃`）；本条对 `k` 与 `n` **同时**做构造子递归，
    四路情形全部穷举，零公理。这个 `j` 就是「链上第 `n` 步相对第 `k` 步多走的正步数」，
    是 `chainE_far` 的唯一输入。 -/
theorem exists_eq_add_succ_of_lt : ∀ (k n : Nat), k < n → ∃ j, n = k + (j + 1)
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, m + 1, _ => ⟨m, (Nat.zero_add (m + 1)).symm⟩
  | k + 1, 0, h => absurd h (Nat.not_lt_zero (k + 1))
  | k + 1, m + 1, h => by
      obtain ⟨j, hj⟩ := exists_eq_add_succ_of_lt k m (Nat.lt_of_succ_lt_succ h)
      refine ⟨j, ?_⟩
      show m + 1 = k + 1 + (j + 1)
      rw [add_one_add k (j + 1)]
      exact congrArg (fun t => t + 1) hj

/-- **`Nat.lt_trichotomy` 的「相等」分支排除法**（把 `¬(a<b)` 与 `¬(b<a)` 换成 `a = b`）。

    比 `Nat.lt_trichotomy` 多说了：那条给的是一个三选一的**析取**，本条是与
    「两个否定」配合的落地形态 —— 在 `by_cases f : eq x v` 之后，`Bool` 判等
    已经被用到头了，剩下只需把「不比大也不比小」压成 `=`，且不碰 `propext`。 -/
theorem eq_of_not_lt_not_gt {a b : Nat} : ¬ a < b → ¬ b < a → a = b := by
  intro h1 h2
  cases htri : Nat.lt_trichotomy a b with
  | inl hlt => exact absurd hlt h1
  | inr hrest =>
      cases hrest with
      | inl heqval => exact heqval
      | inr hgt => exact absurd hgt h2

/-! ## 三、鸽笼入口：`idxOfE_toFin` 的单射性（T34 卡住的那一步） -/

/-- **`idxOfE_toFin` 在覆盖表上是单射**（把 T30 的三块砖拼成 `pigeonhole` 的第三种前提）。

    比 `idxOfE_inj` 多说了：那条只处理「两边都命中同一个下标」的情形，还留着
    `some` 等式要调用处自己造；本条把 `idxOfE_toFin` 这个**全函数**（`Type` 值）
    的两边像相等**直接**翻成原像相等 —— 只要两张表覆盖了这两个点。

    这就是 T34 要而没拿到的那条：它绕过 `∃ k, idxOfE … = some k` 的
    `Type` 消去（`propRecLargeElim`），因为 `idxOfE_toFin` 本身已把
    「没找到」这一分支用兜底值 `⟨0, hpos⟩` 填好，不再需要从 `Prop` 里取数据。 -/
theorem idxOfE_toFin_inj {W : Type u} (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (l : List W) (hpos : 0 < l.length)
    {v w : W} (hv : v ∈ l) (hw : w ∈ l)
    (h : idxOfE_toFin eq l v hpos = idxOfE_toFin eq l w hpos) : v = w := by
  -- ① 两边都命中：`idxOf_cover` 给下标（`∃` 只消到 `Prop`，合法）
  obtain ⟨kv, hkv⟩ := idxOfE_cover eq heq v l hv
  obtain ⟨kw, hkw⟩ := idxOfE_cover eq heq w l hw
  -- ② 对齐：`idxOfE_toFin` 的值就是那个下标（`idxOfE_toFin_spec`）
  have hkv' : idxOfE_toFin eq l v hpos = kv := idxOfE_toFin_spec eq heq l v hpos hkv
  have hkw' : idxOfE_toFin eq l w hpos = kw := idxOfE_toFin_spec eq heq l w hpos hkw
  -- ③ 像相同 ⟹ 下标相同（`▸` 只处理 `Eq`，不碰 `Iff`）
  have hkk : kv = kw := by
    rw [hkv', hkw'] at h
    exact h
  -- ④ 下标相同 ⟹ 原像相同（T30 的 `idxOfE_inj`）
  rw [hkk] at hkv
  exact idxOfE_inj eq heq l hkv hkw

/-! ## 三、链的两两不同（鸽笼的「输入表」） -/

/-- **链上「走到更远处」的项必不同于起点**（把 `chainE_reach_add` 与无环性合成一条）。

    比 `chainE_reach_add` 多说了：可达 + 无环 ⟹ **两端不等**，而且是**任意正步数**
    （`k+1 ≥ 1`）的形态 —— 于是「链上两个不同时刻不是同一个点」不必再逐步递推。 -/
theorem chainE_far {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (verts : List W) (w0 : W)
    (hfather : ∀ v : W, v ∈ verts → ∃ b, b ∈ g.pa v ∧ b ∈ verts)
    (hac : Acyclic g) {s : W} (hs : s ∈ verts) (a k : Nat) :
    chainE g eq heq verts w0 hfather s a ≠
      chainE g eq heq verts w0 hfather s (a + (k + 1)) :=
  reachable_ne hac (chainE_reach_add g eq heq verts w0 hfather hs a k)

/-- **表内回溯链在 `Fin (verts.length + 1)` 上单射**。

    比 `chainE_reach_add` 多说了：那条说「沿链走 `k+1` 步可达」，是**逐步**的；
    本条把它抬到**整个 `Fin (verts.length + 1)` 枚举**上 —— 于是「链的前
    `verts.length + 1` 项两两不同」可以一次性拿到，正好够 `pigeonhole` 撞车。

    证明分三段（`Nat.lt_trichotomy` 的三个构造子，按声明顺序穷举）：
    `i < j` 时第 `j` 步就是第 `i` 步走 `(j-i-1)+1` 步；`j < i` 时对称；相等直接收。 -/
theorem chainE_inj {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (verts : List W) (w0 : W)
    (hfather : ∀ v : W, v ∈ verts → ∃ b, b ∈ g.pa v ∧ b ∈ verts)
    (hac : Acyclic g) {s : W} (hs : s ∈ verts) :
    ∀ i j : Fin (verts.length + 1),
      chainE g eq heq verts w0 hfather s i.val =
        chainE g eq heq verts w0 hfather s j.val → i = j := by
  intro i j hij
  have hval : i.val = j.val :=
    eq_of_not_lt_not_gt
      (fun hlt => by
        obtain ⟨k, hk⟩ := exists_eq_add_succ_of_lt i.val j.val hlt
        exact chainE_far g eq heq verts w0 hfather hac hs i.val k (hk ▸ hij))
      (fun hgt => by
        obtain ⟨k, hk⟩ := exists_eq_add_succ_of_lt j.val i.val hgt
        exact chainE_far g eq heq verts w0 hfather hac hs j.val k (hk ▸ hij.symm))
  exact Fin.ext hval

/-! ## 四、子表版鸽笼：`not_all_parent_in`（T34 卡住的那一条） -/

/-- **`verts` 中被 `hfather` 覆盖这件事的可判定性**（手写穷举，零公理）。

    比 T30 的 `decSourceIn` / T34 的 `decFreeIn` 多说了：那两条判的是
    「表内**没有**父」，本条判的是「表内**处处都有**父」——
    也就是 `not_all_parent_in` 的反设。`isTrue` 分支交出**整条** `hfather`
    （不是逐点一个个要），`isFalse` 分支交出**一个具体的反例点**，
    两个方向都带构造性数据，于是「反设不成立 ⟹ 存在内部无父点」不必经典换向。 -/
def decFather {W : Type u} (eq : W → W → Bool) (heq : ∀ a b, eq a b = true ↔ a = b)
    (g : Graph W) (verts : List W) :
    (vs : List W) → Decidable (∀ v, v ∈ vs → ∃ b, b ∈ g.pa v ∧ b ∈ verts)
  | [] => isTrue (fun v hv => absurd hv List.not_mem_nil)
  | v :: vs =>
      match decParentIn eq heq verts (g.pa v) with
      | isTrue hb =>
          match decFather eq heq g verts vs with
          | isTrue hrest =>
              isTrue (fun x hx => by
                cases hx with
                | head => exact hb
                | tail _ htl => exact hrest x htl)
          | isFalse hrest =>
              isFalse (fun hall => hrest (fun x hx => hall x (List.mem_cons_of_mem v hx)))
      | isFalse hb =>
          isFalse (fun hall => hb (hall v List.mem_cons_self))

/-- **`not_all_parent_in`：无环 + 无重复 ⟹ 表内必有一个「父都不在表内」的点**。

    比 T30 的 `not_all_parent` 多说了：那条要求 `verts` **覆盖全图所有点**
    （`hcover : ∀ v, v ∈ s :: ss`），且用全局链 `chain`；本条只要求
    `verts.Nodup`，反设弱化为「**表内每点都在表内有一个父**」——
    这正是删点归纳能用的形态（T34 的偏差 1 指出覆盖全体在子问题上为假）。

    证明（**子表版鸽笼**）：
    1. 反设 `hfather`，用 T34 的 `chainE` 沿表内父回溯 `verts.length + 1` 步；
    2. `chainE_inj` 给出这些点两两不同（`Fin (verts.length + 1)` → `Set` 的单射）；
    3. `chainE_mem` 保证它们都在 `verts` 里，于是 `idxOfE_toFin` 把它们压进
       `Fin verts.length`；
    4. `idxOfE_toFin_inj` 给出压缩后仍单射；
    5. T27 的 `pigeonhole` 给 `verts.length + 1 ≤ verts.length` —— 矛盾。

    `∃` 只消到 `Prop`（`obtain` 在 `Prop` 目标里合法），压缩后的映射
    由 `idxOfE_toFin` 这个 **`Type` 值函数**给出，**没有一次 `propRecLargeElim`**。 -/
theorem not_all_parent_in {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (hac : Acyclic g) {verts : List W}
    (hnd : verts.Nodup) (w0 : W) (hne : verts ≠ []) :
    ¬ ∀ v, v ∈ verts → ∃ b, b ∈ g.pa v ∧ b ∈ verts := by
  intro hfather
  -- 覆盖表非空 ⟹ 长度为正（`pigeonhole` 与 `idxOfE_toFin` 都需要）
  have hpos : 0 < verts.length := by
    cases verts with
    | nil => exact absurd rfl hne
    | cons s ss => exact Nat.zero_lt_succ ss.length
  -- 起点取 `verts` 的头（用 `Exists` 到 `Prop` 的方式取，不消到 `Type`）
  have hex : ∃ s, s ∈ verts := by
    cases verts with
    | nil => exact absurd rfl hne
    | cons s ss => exact ⟨s, List.mem_cons_self⟩
  -- 对每一点，取它在表内的下标（`idxOfE_toFin` 是全函数，无需 witnesses）
  obtain ⟨s, hs⟩ := hex
  -- 压缩映射：`Fin (verts.length + 1) → Fin verts.length`
  let f : Fin (verts.length + 1) → Fin verts.length :=
    fun k => idxOfE_toFin eq verts (chainE g eq heq verts w0 hfather s k.val) hpos
  -- `Fin (verts.length + 1)` 的全体枚举无重复（用 `Fin.ext` 判定，不用 `enumFin`）
  -- `enumFin` 的长度恰为 `verts.length + 1`，于是鸽笼给 `verts.length + 1 ≤ verts.length`
  have hle :=
    FateV2.Core.pigeonhole (enumFin (verts.length + 1)) (enumFin_nodup _) f
      (fun x _ y _ hxy => by
        -- 像相同 ⟹ 原像相同
        have hxv : chainE g eq heq verts w0 hfather s x.val ∈ verts :=
          chainE_mem g eq heq verts w0 hfather hs x.val
        have hyv : chainE g eq heq verts w0 hfather s y.val ∈ verts :=
          chainE_mem g eq heq verts w0 hfather hs y.val
        have hchain : chainE g eq heq verts w0 hfather s x.val =
            chainE g eq heq verts w0 hfather s y.val :=
          idxOfE_toFin_inj eq heq verts hpos hxv hyv hxy
        exact chainE_inj g eq heq verts w0 hfather hac hs x y hchain)
  rw [enumFin_length] at hle
  exact Nat.not_succ_le_self verts.length hle

/-- **`¬∀ v ∈ l, ∃ b ∈ pa v, b ∈ verts` ⟹ 有一个 `v ∈ l` 使父都不在 `verts` 里**。

    比 `Classical.not_forall` 多说了：后者要 `Classical.choice` 才拿得到见证，
    本条对 `l` 做**手写结构递归**，`head` / `tail` 两个构造子各走一步，
    把反例点直接交出来 —— 于是 `exists_free_in_of_acyclic` 的 `isFalse` 分支
    可以零公理落地。 -/
theorem flip_not_forall {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) :
    ∀ (l verts : List W),
      (¬ ∀ v, v ∈ l → ∃ b, b ∈ g.pa v ∧ b ∈ verts) →
      ∃ src, src ∈ l ∧ FreeIn eq g verts src
  | [], _, h => absurd (fun v hv => absurd hv List.not_mem_nil) h
  | v :: vs, verts, h => by
      cases hf : decParentIn eq heq verts (g.pa v) with
      | isTrue hb =>
          -- `v` 有表内父 ⟹ 反例点只能出现在尾部
          obtain ⟨src, hsrc, hfree⟩ :=
            flip_not_forall g eq heq vs verts (fun hall =>
              h (fun x hx => by
                cases hx with
                | head => exact hb
                | tail _ htl => exact hall x htl))
          exact ⟨src, List.mem_cons_of_mem v hsrc, hfree⟩
      | isFalse hb =>
          -- `v` 的父都不在表里 ⟹ 它自己就是反例点
          exact ⟨v, List.mem_cons_self, fun b hbpa hbv => hb ⟨b, hbpa, hbv⟩⟩

/-- **`verts` 中必有一个「父都不在 `verts` 里」的点**（归纳步真正的入口）。

    比 `not_all_parent_in` 多说了：那条只给 `¬∀`，本条把它**落地成一个具体的
    `src : W`、`src ∈ verts`、`FreeIn eq g verts src`** —— 归纳步需要的是这个
    三元组，而不是一条否定。

    为什么不需要 `Classical.choice`：`decFather`（§三）对「表内每点都有表内父」
    给出**构造性判定**，它的 `isFalse` 分支连同 `flip_not_forall` 的尾递归
    直接交出反例点，再把这个点的「表内无父」翻成 `FreeIn`。全程只消到 `Prop`。 -/
theorem exists_free_in_of_acyclic {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (hac : Acyclic g) {verts : List W}
    (hnd : verts.Nodup) (w0 : W) (hne : verts ≠ []) :
    ∃ src, src ∈ verts ∧ FreeIn eq g verts src := by
  cases hv : decFather eq heq g verts verts with
  | isTrue hall =>
      exact absurd hall (not_all_parent_in g eq heq hac hnd w0 hne)
  | isFalse hnot =>
      exact flip_not_forall g eq heq verts verts hnot

/-! ## 六、删点后的覆盖性（T34 偏差 1 的修法） -/

/-- **`v ∈ verts` ⟹ `v = src` 或 `v ∈ removeOneE eq src verts`**。

    比 T30 的 `removeOneE_hit` / `removeOneE_miss` 多说了：那两条只给**删除分支的形状**，
    本条给**成员层面的二分**，而且不需要 `DecidableEq`、不需要 `by_cases`
    （判等走 `eq` 的 `Bool` 分支）——
    这正是 T34 偏差 1 缺的那条：子问题的顶点集是 `removeOneE eq src verts`，
    归纳步只需要「原表成员落进子表（或就是 `src`）」。 -/
theorem mem_or_mem_removeOneE {W : Type u} (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (src : W) :
    ∀ (l : List W) {v : W}, v ∈ l → v = src ∨ v ∈ removeOneE eq src l
  | [], v, h => absurd h List.not_mem_nil
  | x :: xs, v, h => by
      cases hx : eq x src with
      | true =>
          rw [removeOneE_hit eq src x xs hx]
          cases h with
          | head => exact Or.inl (eq_true_elim heq hx)
          | tail _ htl => exact Or.inr htl
      | false =>
          rw [removeOneE_miss eq src x xs hx]
          cases h with
          | head => exact Or.inr List.mem_cons_self
          | tail _ htl =>
              cases mem_or_mem_removeOneE eq heq src xs htl with
              | inl hv => exact Or.inl hv
              | inr hv => exact Or.inr (List.mem_cons_of_mem x hv)

/-! ## 七、主归纳：任意长度上限上的 `IsTopoOrderOnE` -/

/-- **（对长度上限 `k` 归纳）子表上的拓扑序存在**。

    比 T34 的 `onE_cons` 多说了：那条只做**一步**（把 `src` 拼到子序最前），
    本条把这一步与「源点存在」**循环起来**：
    每一步用 `exists_free_in_of_acyclic` 取一个表内无父点 `src`，
    排到 `onE_cons` 的最前面，再对 `removeOneE eq src verts` 递归。

    归纳因子选**长度上限 `k`**（`Nat` 上的原始递归，零公理）：
    `removeOneE_length_lt`（T30）保证 `(removeOneE eq src verts).length < verts.length ≤ k`，
    于是子问题落在 `k` 以内 —— 「`verts` 只减不增」这一步**只需要长度**，
    不需要重述覆盖全体（T34 偏差 2 的修法：不变量里根本没有「覆盖全体」这一条）。 -/
theorem exists_onE_aux {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (hac : Acyclic g) (w0 : W) :
    ∀ (k : Nat) (verts : List W), verts.length ≤ k → verts.Nodup →
      ∃ order, IsTopoOrderOnE g verts order
  | 0, verts, hlen, _ => by
      -- `verts.length ≤ 0` ⟹ `verts = []`
      cases verts with
      | nil => exact ⟨[], onE_nil g⟩
      | cons s ss =>
          exact absurd hlen (Nat.not_succ_le_zero ss.length)
  | k + 1, verts, hlen, hnd => by
      cases hv : verts with
      | nil => exact ⟨[], onE_nil g⟩
      | cons s ss =>
          -- 先把 `verts` 的所有假设都换成 `s :: ss` 的形态（`hv` 只用于这次改写）
          subst hv
          -- 非空：取一个表内无父点
          obtain ⟨src, hsrcIn, hfree⟩ :=
            exists_free_in_of_acyclic g eq heq hac hnd w0 (List.cons_ne_nil s ss)
          -- 子问题：长度严格变小
          have hlt : (removeOneE eq src (s :: ss)).length < (s :: ss).length :=
            removeOneE_length_lt eq heq src (s :: ss) hsrcIn
          have hsub : (removeOneE eq src (s :: ss)).length ≤ k :=
            Nat.lt_succ_iff.1 (Nat.lt_of_lt_of_le hlt hlen)
          have hnd' : (removeOneE eq src (s :: ss)).Nodup := nodup_removeOneE eq src (s :: ss) hnd
          obtain ⟨rest, hrest⟩ :=
            exists_onE_aux g eq heq hac w0 k (removeOneE eq src (s :: ss)) hsub hnd'
          exact ⟨src :: rest,
            onE_cons g eq heq hnd hsrcIn hfree hrest
              (fun v hvmem => mem_or_mem_removeOneE eq heq src (s :: ss) hvmem)⟩

/-! ## 八、主定理：任意类型上的拓扑序存在性 -/

/-- **`exists_topo_order_of_cover`：任意顶点类型上，无环 + 覆盖列表 ⟹ 拓扑序存在**（零公理）。

    比 T30 的 `source_exists_of_cover` 多说了：那条只给**源点存在**（`HasSource`），
    本条给**一整条排好的序** `order`，且 `IsTopoOrder g order` 成立 ——
    也就是 T30/T34 一路缺到最后的那条主定理。

    比 T1c 的 `exists_topo_order_fin` 多说了：那条的顶点类型只能是 `Fin (m+1)`；
    本条对**任意** `W` 工作，有限性以显式覆盖列表 `verts` 进入，
    判等以显式数据 `eq` 进入，全程不碰 `Fintype` / `Finset` / `Classical`。

    组装：
    * `verts = []` 时 `hcover : ∀ v, v ∈ []` 直接给 `False`（T34 `false_of_forall_mem_nil`），真空；
    * 非空时 `exists_onE_aux`（§七）给出 `IsTopoOrderOnE g verts order`；
    * 再用 `isTopoOrder_of_onE`（T34）把「只对 `verts` 负责」升级成「对全图负责」。 -/
theorem exists_topo_order_of_cover {W : Type u} (g : Graph W) (eq : W → W → Bool)
    (heq : ∀ a b, eq a b = true ↔ a = b) (hac : Acyclic g) (verts : List W)
    (w0 : W) (hcover : ∀ v, v ∈ verts) (hnd : verts.Nodup) :
    ∃ order : List W, IsTopoOrder g order := by
  cases hv : verts with
  | nil => exact absurd (hv ▸ hcover w0) List.not_mem_nil
  | cons s ss =>
      subst hv
      obtain ⟨order, horder⟩ :=
        exists_onE_aux g eq heq hac w0 (s :: ss).length (s :: ss) (Nat.le_refl _) hnd
      exact ⟨order, isTopoOrder_of_onE (fun v => hcover v) horder⟩

end FateV2.Model
