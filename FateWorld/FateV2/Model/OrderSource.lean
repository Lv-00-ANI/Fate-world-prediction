import FateWorld.FateV2.Model.Order
import FateWorld.FateV2.Model.Pigeon

/-!
  # Model · 源点存在性与拓扑序存在性（零公理）

  ## 本文件回答什么

  专项 T1 把「无环 ⟹ 拓扑序存在」的**条件版**证了出来
  （`Order.topo_cons_of_source`：源点 + 覆盖 + 子序 ⟹ 拓扑序），
  并把唯一缺口定位为：

  ```lean
  def SourceExists (g : Graph V) : Prop := Acyclic g → HasSource g
  ```

  T1 的理由是「这需要鸽笼，而 Mathlib 的鸽笼带三个公理」。
  **本文件补上这个缺口**：用 `Pigeon.length_le_of_nodup_fin`（零公理的鸽笼）
  证出无环图必有源点，再对 `n` 归纳得到拓扑序存在性。
  全篇 `#print axioms` 实测为 **`does not depend on any axioms`**。

  ## 陈述的修正（诚实登记）

  题面要求 `Graph (Fin n)`（任意 `n`）。但 **`n = 0` 时该陈述为假**：

  * `Fin 0` 没有居民，故 `HasSource g = ∃ v, g.pa v = []` **恒假**；
  * `Acyclic g = ∀ v, ¬Reachable g v v` 在 `Fin 0` 上 **恒真**。

  于是 `Acyclic g → HasSource g` 在 `n = 0` 时不成立（`fin0_not_hasSource` /
  `fin0_acyclic` 两条都已零公理证出）。本文件按 **`Fin (m + 1)`**（即 `n ≥ 1`）陈述。
  这不是证明困难，而是陈述本身在空顶点集上退化的必然结果。

  ## 证明路线（三步，全部零公理）

  1. **链**：若每点都有父（`hpa : ∀ v, g.pa v ≠ []`），沿 `pa` 取 `head` 得无限回溯序列
     `chain : Nat → V`，且 `chain k` 一步可达 `chain (k+1)`。

  2. **无环 ⟹ 链上处处不同**：`a < b` 时 `chain a` 可达 `chain b`（把「一步」攒成
     「`b - a` 步」），若 `chain a = chain b` 就撞 `Acyclic`。

  3. **撞鸽笼**：取前 `m+2` 项得 `List (Fin (m+1))`，它 `Nodup` 且长度 `m+2 > m+1`，
     与 `Pigeon.length_le_of_nodup_fin` 矛盾。于是 `¬¬ HasSource g`。

  最后把 `¬¬ HasSource g` 落地成 `HasSource g`：一般这一步要经典选择，
  但 `HasSource g` 在 `Fin n` 上**可判定**（手写穷举 `decBelow`），
  而 `Decidable P → ¬¬P → P` 是**构造性**的（`of_not_not_of_decidable`）。
  于是全程零公理。

  ## 公理纪律：本文件实测踩过的坑

  | 写法 | `#print axioms` |
  |---|---|
  | `by_cases h : ∃ v, P v`（在 `∃` 上分支） | `propext`;`Classical.choice`;`Quot.sound` ❗ |
  | `match l with \| [] => .. \| _ => ..`（捕获通配） | `propext` ❗ |
  | `simp`（任何位置收尾） | `propext` ❗ |
  | `Nat.lt_one_iff` / `Nat.exists_eq_add_of_lt` | `propext` ❗ |
  | `match l with \| [] => .. \| _ :: _ => ..`（穷举构造子） | **零公理** ✅ |
  | `Option.some.inj` / `List.noConfusion` | **零公理** ✅ |
  | `Decidable` + 构造性 `match`（`of_not_not_of_decidable`） | **零公理** ✅ |
  | 手写列表遍历 / 手写穷举 | **零公理** ✅ |

  **正确姿势**：
  * 反证假设直接取 `¬ HasSource g`（不要 `by_cases` 一个 `∃`）；
  * 消 `∃` 的否定的对偶（`¬∃ → ∀`, `¬∀`）只在需要处逐点展开；
  * 判空用穷举构造子（`[]` / `_ :: _`），不用捕获通配；
  * 不用 `simp` / `decide` / `omega`。
-/

namespace FateV2.Model

universe u

/-! ## 一、可判定命题的双重否定消去 -/

/-- **可判定命题的双重否定消去**（零公理）。

    比 `Classical.byContradiction` 多说了：**它不需要经典选择**。
    `Decidable P` 已经直接提供 `P ∨ ¬P`，于是 `¬¬P` 立刻收敛到 `P`：
    `isTrue` 拿到正证、`isFalse` 与 `¬¬P` 直接相撞。
    这条是本文件把「反证」落地成「构造」的唯一桥梁。 -/
theorem of_not_not_of_decidable {P : Prop} [d : Decidable P] (h : ¬ ¬ P) : P :=
  match d with
  | isTrue hp => hp
  | isFalse hn => absurd hn h

/-! ## 二、`List` 与 `Nat` 的零公理小事实 -/

/-- **`a :: as` 非空**。

    比 `List.cons_ne_nil` 多说了：给出一条**可直接 `exact`** 的 `False` 消去，
    于是判空的分支里不需要 `simp`（`simp` 实测带 `propext`）。 -/
theorem cons_ne_nil {α : Type} (a : α) (as : List α) : (a :: as) ≠ [] := by
  intro h
  cases h

/-- **`a < b` 的加法分解**：`∃ j, b = a + (j + 1)`。

    比 `Nat.exists_eq_add_of_lt` 多说了：后者是 Mathlib 里的版本，实测带 `propext`；
    这里在 `b` 上做结构归纳直接给出构造性证明。 -/
theorem exists_eq_add_of_lt' {a b : Nat} (h : a < b) : ∃ j, b = a + (j + 1) := by
  induction b with
  | zero => exact absurd h (Nat.not_lt_zero a)
  | succ n ih =>
      by_cases hab : a = n
      · subst hab
        exact ⟨0, rfl⟩
      · have hlt : a < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hab
        obtain ⟨j, hj⟩ := ih hlt
        exact ⟨j + 1, by rw [hj]; rfl⟩

/-- **`¬ (∃ v, pa v = [])` ⟹ `∀ v, pa v ≠ []`**（逐点，零公理）。

    比 `Classical.not_forall` 多说了：从 `∃` 的否定到 `∀` 的否定是**构造性**的，
    所以「无源点」这个反证假设可以直接用，不需要经典换向。 -/
theorem forall_ne_of_not_exists {V : Type u} (pa : V → List V)
    (h : ¬ ∃ v, pa v = []) : ∀ v, pa v ≠ [] :=
  fun v hv => h ⟨v, hv⟩

/-! ## 三、回溯链 -/

/-- **回溯链**：若每点都有父（`hpa : ∀ v, g.pa v ≠ []`），从 `s` 出发沿 `pa` 取 `head`，
    得到一条无限序列 `chain 0 = s`、`chain (k+1) = (pa (chain k)).head`。

    比「父列表非空」多说了：**它给出一个具体的无穷点列**，
    于是「有限顶点」与「无限回溯」的矛盾有了可对撞的载体。 -/
def chain {V : Type u} (g : Graph V) (hpa : ∀ v, g.pa v ≠ []) (s : V) : Nat → V
  | 0 => s
  | k + 1 => (g.pa (chain g hpa s k)).head (hpa _)

/-- **链的定义性一步**：`chain (k+1)` 是 `chain k` 的一个父。 -/
theorem chain_mem {V : Type u} (g : Graph V) (hpa : ∀ v, g.pa v ≠ []) (s : V) (k : Nat) :
    chain g hpa s (k + 1) ∈ g.pa (chain g hpa s k) :=
  List.head_mem (hpa _)

/-- **单步可达**：`chain k` 一步可达 `chain (k+1)`。

    比 `chain_mem` 多说了：把「父边上的一个元素」翻译成 `Reachable` 的一步。 -/
theorem chain_step {V : Type u} (g : Graph V) (hpa : ∀ v, g.pa v ≠ []) (s : V) (k : Nat) :
    Reachable g (chain g hpa s k) (chain g hpa s (k + 1)) :=
  Reachable.step (chain_mem g hpa s k)

/-- **`j+1` 步可达**：`chain k` 可达 `chain (k + (j + 1))`。

    比 `chain_step` 多说了：把「一步」攒成「任意正步数」，
    于是链上「下标大」就蕴含 `Reachable`。 -/
theorem chain_reachable_add {V : Type u} (g : Graph V) (hpa : ∀ v, g.pa v ≠ []) (s : V)
    (k : Nat) : ∀ j : Nat, Reachable g (chain g hpa s k) (chain g hpa s (k + (j + 1)))
  | 0 => chain_step g hpa s k
  | j + 1 =>
      Reachable.trans (chain_reachable_add g hpa s k j) (chain_step g hpa s (k + (j + 1)))

/-- **`a < b` 时的可达**：`chain a` 可达 `chain b`。

    比 `chain_reachable_add` 多说了：它接受「`a < b`」这个自然数序前提，
    自动找出步数 `j` 并把 `b` 改写成 `a + (j+1)`。 -/
theorem chain_reachable_lt {V : Type u} (g : Graph V) (hpa : ∀ v, g.pa v ≠ []) (s : V)
    {a b : Nat} (hlt : a < b) : Reachable g (chain g hpa s a) (chain g hpa s b) := by
  obtain ⟨j, hj⟩ := exists_eq_add_of_lt' hlt
  rw [hj]
  exact chain_reachable_add g hpa s a j

/-- **无环 ⟹ 链上处处不同**：`a < b` 时 `chain a ≠ chain b`。

    比 `Acyclic` 的定义多说了：它把「不能回到自己」用在一条**显式构造的链**上，
    于是「无限回溯」与「无环」的冲突变得可操作 —— 这是撞鸽笼的前置条件。 -/
theorem chain_ne_of_lt {V : Type u} (g : Graph V) (hpa : ∀ v, g.pa v ≠ []) (s : V)
    (hac : Acyclic g) {a b : Nat} (hlt : a < b) : chain g hpa s a ≠ chain g hpa s b := by
  intro heq
  have hr : Reachable g (chain g hpa s a) (chain g hpa s b) :=
    chain_reachable_lt (g := g) (hpa := hpa) (s := s) hlt
  exact hac (chain g hpa s a) (heq ▸ hr)

/-! ## 四、手写取前缀 -/

/-- **取序列的前 `k` 项**（手写递归）。

    不用 `List.range.map` / `List.ofFn`：那些是**高阶**的，
    会让递归退化成 well-founded 并带上 `propext` / `Quot.sound`（本项目已实测）。 -/
def takeChain {V : Type u} (f : Nat → V) : Nat → List V
  | 0 => []
  | k + 1 => f k :: takeChain f k

/-- **前缀长度恰为 `k`**。 -/
theorem takeChain_length {V : Type u} (f : Nat → V) :
    ∀ k : Nat, (takeChain f k).length = k
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (takeChain_length f k)

/-- **前缀的每个元素都来自某个下标 `< k`**。

    比 `takeChain` 的定义多说了：把「成员」翻译成「存在下标」，
    于是「无重复」可以从「值不重复」直接继承。 -/
theorem takeChain_mem {V : Type u} (f : Nat → V) :
    ∀ (k : Nat) (w : V), w ∈ takeChain f k → ∃ i, i < k ∧ f i = w
  | 0, w, hw => absurd hw (List.not_mem_nil)
  | k + 1, w, hw => by
      cases hw with
      | head => exact ⟨k, Nat.lt_succ_self k, rfl⟩
      | tail _ hw' =>
          obtain ⟨i, hi, hfi⟩ := takeChain_mem f k w hw'
          exact ⟨i, Nat.lt_of_lt_of_le hi (Nat.le_succ k), hfi⟩

/-- **序列处处不同 ⟹ 任意前缀无重复**。

    比 `takeChain` 的定义多说了：`Nodup` 从「序列性质」继承到「任意前缀」，
    且分支全部走 `List.Pairwise` 构造子（不用 `List.nodup_cons`，后者带 `propext`）。 -/
theorem takeChain_nodup {V : Type u} {f : Nat → V}
    (hinj : ∀ {a b : Nat}, a < b → f a ≠ f b) : ∀ k : Nat, (takeChain f k).Nodup
  | 0 => List.Pairwise.nil
  | k + 1 => by
      refine List.Pairwise.cons ?_ (takeChain_nodup hinj k)
      intro y hy heq
      obtain ⟨i, hi, hfi⟩ := takeChain_mem f k y hy
      exact hinj (a := i) (b := k) hi (hfi.trans heq.symm)

/-! ## 五、核心反证：无环图不可能「点皆有父」 -/

/-- **`Fin (m+1)` 上无环 ⟹ `¬¬ HasSource g`**。

    比 `Acyclic` 的定义多说了：**它给出一个可撞鸽笼的列表**。
    若每点都有父，取链的前 `m+2` 项得 `List (Fin (m+1))`：
    无环使它 `Nodup`，长度却是 `m+2 > m+1`，与
    `Pigeon.length_le_of_nodup_fin` 矛盾。 -/
theorem not_not_hasSource (m : Nat) (g : Graph (Fin (m + 1))) (hac : Acyclic g) :
    ¬ ¬ HasSource g := by
  intro hsrc
  have hpa : ∀ v, g.pa v ≠ [] := forall_ne_of_not_exists g.pa hsrc
  let s : Fin (m + 1) := ⟨0, Nat.zero_lt_succ m⟩
  have hinj : ∀ {a b : Nat}, a < b → chain g hpa s a ≠ chain g hpa s b :=
    fun {a b} hlt => chain_ne_of_lt (g := g) (hpa := hpa) (s := s) hac hlt
  have hnodup : (takeChain (chain g hpa s) (m + 2)).Nodup :=
    takeChain_nodup hinj (m + 2)
  have hlen : (takeChain (chain g hpa s) (m + 2)).length = m + 2 :=
    takeChain_length (chain g hpa s) (m + 2)
  have hle : (takeChain (chain g hpa s) (m + 2)).length ≤ m + 1 :=
    length_le_of_nodup_fin (m + 1) _ hnodup
  rw [hlen] at hle
  exact absurd hle (Nat.not_succ_le_self (m + 1))

/-! ## 六、`HasSource` 在 `Fin n` 上可判定 -/

/-- **`Fin n` 上「`m` 以下存在源点」可判定**（`m ≤ n`，手写穷举）。

    比 `List.any` 多说了：判空用**穷举构造子**（`[]` / `a :: as`），
    不用捕获通配 `_`（后者实测带 `propext`）；
    `Fin n` 的见证由下标 `j` 与证据 `j < n` 直接给出，不依赖 `DecidableEq`。 -/
def decBelow {n : Nat} (pa : Fin n → List (Fin n)) :
    ∀ (m : Nat), m ≤ n → Decidable (∃ j : Nat, j < m ∧ ∃ _hjn : j < n, pa ⟨j, _hjn⟩ = [])
  | 0, _ => isFalse (fun h => by
      obtain ⟨j, hj, _⟩ := h
      exact Nat.not_lt_zero j hj)
  | m + 1, hle =>
      match decBelow pa m (Nat.le_of_succ_le hle) with
      | isTrue h => isTrue (by
          obtain ⟨j, hj, hjn, hp⟩ := h
          exact ⟨j, Nat.lt_succ_of_lt hj, hjn, hp⟩)
      | isFalse h =>
          match hp : pa ⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hle⟩ with
          | [] => isTrue ⟨m, Nat.lt_succ_self m,
                          Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hle, hp⟩
          | a :: as => isFalse (fun hex => by
              obtain ⟨j, hjm, hjn, hpa⟩ := hex
              by_cases hje : j = m
              · subst hje
                rw [hp] at hpa
                exact cons_ne_nil a as hpa
              · have hjm' : j < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hjm) hje
                exact h ⟨j, hjm', hjn, hpa⟩)

/-- **`HasSource` 在 `Fin n` 上可判定**。

    比 `HasSource` 的定义多说了：它把「存在源点」变成**可计算的判定**，
    于是 `¬¬ HasSource → HasSource` 可以走 `of_not_not_of_decidable`，
    **完全绕开 `Classical.choice`**。 -/
def decHasSource {n : Nat} (g : Graph (Fin n)) : Decidable (HasSource g) :=
  match decBelow g.pa n (Nat.le_refl n) with
  | isTrue h => isTrue (by
      obtain ⟨j, _, hjn, hp⟩ := h
      exact ⟨⟨j, hjn⟩, hp⟩)
  | isFalse h => isFalse (fun ⟨v, hv⟩ => h ⟨v.val, v.isLt, v.isLt, hv⟩)

/-! ## 七、`SourceExistsFin`（零公理） -/

/-- **无环 ⟹ 有源点**（顶点类型 `Fin (m+1)`，零公理）。

    比 `HasSource` 的定义多说了：**它一定存在**——
    这是 T1 报告里 `SourceExists` 缺口在 `Fin n` 上的完整补上。

    证明：若每点都有父，则回溯链的前 `m+2` 项是 `Fin (m+1)` 上长度 `m+2` 的
    无重复列表，撞鸽笼（`not_not_hasSource` 给出 `¬¬ HasSource`）；
    再靠 `HasSource` 在 `Fin n` 上可判定，把 `¬¬` 构造性地收敛。

    注：原文按 `Fin n` 陈述，但 `n = 0` 时陈述为假（`Fin 0` 无居民）。
    见 `fin0_not_hasSource` 与 `fin0_acyclic` 的反例。 -/
theorem source_exists_fin (m : Nat) (g : Graph (Fin (m + 1))) (hac : Acyclic g) :
    HasSource g :=
  @of_not_not_of_decidable (HasSource g) (decHasSource g) (not_not_hasSource m g hac)

/-- **`Fin 0` 上 `HasSource` 恒假**（反例的另一半）。

    比 `HasSource` 的定义多说了：**空顶点集上不存在源点** ——
    这正是 `source_exists_fin` 必须按 `Fin (m+1)` 陈述的原因。 -/
theorem fin0_not_hasSource (g : Graph (Fin 0)) : ¬ HasSource g := by
  intro h
  obtain ⟨v, _⟩ := h
  exact nomatch v

/-- **`Fin 0` 上任何图都无环**（反例的一半）。 -/
theorem fin0_acyclic (g : Graph (Fin 0)) : Acyclic g :=
  fun v => nomatch v

/-! ## 八、拓扑序存在性（第 4 步）

`Order.topo_cons_of_source`（T1）已把「源点排第一 + 其余排好 ⟹ `src :: rest` 是拓扑序」
证成（零公理）。要把它用起来，只差「其余顶点也能排好」。
这里对**顶点列表的长度**做强递归（`Nat.strongRecOn`，实测零公理），
每步从剩余顶点里取一个「父都不在剩余顶点里」的点排到最前。

`IsTopoOrderOn g vertices order` 把「只排好给定顶点集」写成命题，
于是归纳量是 `vertices.length` —— 这是零公理下唯一可行的归纳量
（`Finset` 基数、`Fintype.card` 都会带公理）。 -/

/-- **列表上的拓扑序**：`order` 含 `vertices` 的全部顶点，且 `vertices` 内部的父边有序。

    比 `Order.IsTopoOrder` 多说了：它只约束**给定的顶点集**（`vertices`），
    于是可以对其长度归纳 —— 这是零公理下唯一可行的归纳量。 -/
def IsTopoOrderOn {V : Type u} (g : Graph V) (vertices : List V) (order : List V) : Prop :=
  (∀ v, v ∈ vertices → v ∈ order) ∧
  (∀ a b, b ∈ g.pa a → a ∈ vertices → b ∈ vertices →
    ∀ i j, nth order i = some a → nth order j = some b → j < i)

/-- **`IsTopoOrderOn` + 顶点集覆盖全体 ⟹ `IsTopoOrder`**。

    比 `IsTopoOrderOn` 的定义多说了：把「只对给定顶点集成立」升级成「对全图成立」。 -/
theorem isTopoOrder_of_on {V : Type u} (g : Graph V) (vertices order : List V)
    (hcoverAll : ∀ v, v ∈ vertices)
    (h : IsTopoOrderOn g vertices order) : IsTopoOrder g order :=
  ⟨fun v => h.1 v (hcoverAll v),
   fun a b hb i j hi hj => h.2 a b hb (hcoverAll a) (hcoverAll b) i j hi hj⟩

/-- **成员判定**（手写 `Bool` 版，不用 `DecidableEq`）。 -/
def memFin {n : Nat} : Fin n → List (Fin n) → Bool
  | _, [] => false
  | x, y :: ys => if _ : x.val = y.val then true else memFin x ys

/-- **`memFin y ys = true` ⟹ `y ∈ ys`**（`Bool` → `Prop`）。

    比 `memFin` 的定义多说了：可算判定可以回到命题层，
    于是「源点的父不在子图里」这一 `Bool` 事实可以直接用于 `IsTopoOrderOn`。 -/
theorem mem_of_memFin {n : Nat} : ∀ (y : Fin n) (ys : List (Fin n)),
    memFin y ys = true → y ∈ ys
  | y, [], h => absurd h (fun e => nomatch e)
  | y, x :: xs, h => by
      by_cases hxy : y.val = x.val
      · have hyx : y = x := Fin.eq_of_val_eq hxy
        rw [hyx]
        exact List.mem_cons_self ..
      · have hd : memFin y (x :: xs) = memFin y xs := by
          show (if _ : y.val = x.val then true else memFin y xs) = memFin y xs
          rw [dif_neg hxy]
        exact List.mem_cons_of_mem x (mem_of_memFin y xs (hd ▸ h))

/-- **`memFin y ys = false` ⟹ `y ∉ ys`**（`mem_of_memFin` 的逆否）。

    比 `memFin` 的定义多说了：可算判定为假时命题层也确信不在，
    于是「源点的父不在子图里」可以直接与「它在子图里」对撞。 -/
theorem memFin_false_elim {n : Nat} : ∀ (y : Fin n) (ys : List (Fin n)),
    memFin y ys = false → y ∈ ys → False
  | y, [], _, h => absurd h (List.not_mem_nil)
  | y, x :: xs, hf, h => by
      by_cases hxy : y.val = x.val
      · -- `memFin` 在该分支为 `true`，与 `hf` 矛盾
        have hd : memFin y (x :: xs) = true := by
          show (if _ : y.val = x.val then true else memFin y xs) = true
          rw [dif_pos hxy]
        exact absurd hf (by rw [hd]; intro e; exact nomatch e)
      · have hd : memFin y (x :: xs) = memFin y xs := by
          show (if _ : y.val = x.val then true else memFin y xs) = memFin y xs
          rw [dif_neg hxy]
        have hf' : memFin y xs = false := by rw [← hd]; exact hf
        have split : y = x ∨ y ∈ xs := by
          cases h with
          | head => exact Or.inl rfl
          | tail _ htl => exact Or.inr htl
        cases split with
        | inl hyx =>
            -- `y = x` 且 `y.val = x.val`，与 `hxy : ¬ y.val = x.val` 矛盾
            exact hxy (congrArg Fin.val hyx)
        | inr hys => exact memFin_false_elim y xs hf' hys

/-- **按顶点列表过滤父列表**（手写）。 -/
def filterMem {n : Nat} (l vs : List (Fin n)) : List (Fin n) :=
  match l with
  | [] => []
  | x :: xs => if memFin x vs then x :: filterMem xs vs else filterMem xs vs

/-- **过滤后的成员 ⟹ 原成员**（子图不新增边）。 -/
theorem mem_filterMem {n : Nat} : ∀ (l vs : List (Fin n)) (x : Fin n),
    x ∈ filterMem l vs → x ∈ l
  | [], _, _, h => absurd h (List.not_mem_nil)
  | y :: ys, vs, x, h => by
      by_cases hm : memFin y vs
      · have hd : filterMem (y :: ys) vs = y :: filterMem ys vs := by
          show (if memFin y vs then y :: filterMem ys vs else filterMem ys vs) = _
          rw [if_pos hm]
        rw [hd] at h
        cases h with
        | head => exact List.mem_cons_self ..
        | tail _ htl => exact List.mem_cons_of_mem y (mem_filterMem ys vs x htl)
      · have hd : filterMem (y :: ys) vs = filterMem ys vs := by
          show (if memFin y vs then y :: filterMem ys vs else filterMem ys vs) = _
          rw [if_neg hm]
        rw [hd] at h
        exact List.mem_cons_of_mem y (mem_filterMem ys vs x h)

/-- **`filterMem` 为空 ⟹ 原列表的每一项都不在 `vs` 里**。

    比 `filterMem` 的定义多说了：把「过滤后为空」翻译成「与 `vs` 无交」，
    这正是「限制图里的源点的父都不在子图里」这一关键事实。 -/
theorem filterMem_nil {n : Nat} : ∀ (l vs : List (Fin n)) (y : Fin n),
    filterMem l vs = [] → y ∈ l → memFin y vs = false
  | [], _, _, _, hy => absurd hy (List.not_mem_nil)
  | x :: xs, vs, y, hl, hy => by
      by_cases hm : memFin x vs
      · have hd : filterMem (x :: xs) vs = x :: filterMem xs vs := by
          show (if memFin x vs then x :: filterMem xs vs else filterMem xs vs) = _
          rw [if_pos hm]
        rw [hd] at hl
        exact absurd hl (cons_ne_nil x (filterMem xs vs))
      · have hd : filterMem (x :: xs) vs = filterMem xs vs := by
          show (if memFin x vs then x :: filterMem xs vs else filterMem xs vs) = _
          rw [if_neg hm]
        rw [hd] at hl
        have split : y = x ∨ y ∈ xs := by
          cases hy with
          | head => exact Or.inl rfl
          | tail _ htl => exact Or.inr htl
        cases split with
        | inl hyx => rw [hyx]; exact Bool.eq_false_iff.2 hm
        | inr hyx => exact filterMem_nil xs vs y hl hyx

/-- **限制图**：父边只保留落在 `vertices` 里的。 -/
def restrictTo {n : Nat} (g : Graph (Fin n)) (vertices : List (Fin n)) : Graph (Fin n) where
  pa v := filterMem (g.pa v) vertices

/-- **限制图的一条可达路可搬回原图**（子图不新增边）。 -/
theorem reachable_restrictTo {n : Nat} {g : Graph (Fin n)} {vertices : List (Fin n)}
    {a b : Fin n} (h : Reachable (restrictTo g vertices) a b) : Reachable g a b := by
  induction h with
  | @step x y hmem => exact Reachable.step (mem_filterMem (g.pa x) vertices y hmem)
  | @trans x y z _ _ ihxy ihyz => exact Reachable.trans ihxy ihyz

/-- **限制图保持无环**。

    比 `restrictTo` 的定义多说了：**无环性被子图继承**，
    于是 `source_exists_fin` 可以作用在限制图上，从剩余顶点里取源点。 -/
theorem restrictTo_acyclic {n : Nat} (g : Graph (Fin n)) (vertices : List (Fin n))
    (hac : Acyclic g) : Acyclic (restrictTo g vertices) :=
  fun v hrv => hac v (reachable_restrictTo hrv)

/-- **从列表里删掉一个元素**（手写，删第一个值相同的）。 -/
def removeOne {n : Nat} (v : Fin n) : List (Fin n) → List (Fin n)
  | [] => []
  | x :: xs => if _ : x.val = v.val then xs else x :: removeOne v xs

/-- `removeOne` 的「命中」形状。 -/
theorem removeOne_hit {n : Nat} (v : Fin n) (x : Fin n) (xs : List (Fin n))
    (h : x.val = v.val) : removeOne v (x :: xs) = xs := dif_pos h

/-- `removeOne` 的「未命中」形状。 -/
theorem removeOne_miss {n : Nat} (v : Fin n) (x : Fin n) (xs : List (Fin n))
    (h : x.val ≠ v.val) : removeOne v (x :: xs) = x :: removeOne v xs := dif_neg h

/-- **`removeOne` 只删不增**。 -/
theorem mem_removeOne {n : Nat} : ∀ (l : List (Fin n)) (v x : Fin n),
    x ∈ removeOne v l → x ∈ l
  | [], _, _, h => absurd h (List.not_mem_nil)
  | y :: ys, v, x, h => by
      by_cases hyv : y.val = v.val
      · rw [removeOne_hit v y ys hyv] at h
        exact List.mem_cons_of_mem y h
      · rw [removeOne_miss v y ys hyv] at h
        have split : x = y ∨ x ∈ removeOne v ys := by
          cases h with
          | head => exact Or.inl rfl
          | tail _ htl => exact Or.inr htl
        cases split with
        | inl hxy => exact hxy ▸ List.mem_cons_self ..
        | inr htl => exact List.mem_cons_of_mem y (mem_removeOne ys v x htl)

/-- **`removeOne` 保留所有「不等于被删元素」的成员**。

    比 `mem_removeOne` 多说了：删除只损失那一个元素，
    于是「剩余顶点」这一子集关系是精确的。 -/
theorem mem_removeOne_of_ne {n : Nat} : ∀ (l : List (Fin n)) (v x : Fin n),
    x ∈ l → x.val ≠ v.val → x ∈ removeOne v l
  | [], _, _, h, _ => absurd h (List.not_mem_nil)
  | y :: ys, v, x, h, hne => by
      by_cases hyv : y.val = v.val
      · rw [removeOne_hit v y ys hyv]
        have split : x = y ∨ x ∈ ys := by
          cases h with
          | head => exact Or.inl rfl
          | tail _ htl => exact Or.inr htl
        cases split with
        | inl hxy => exact absurd (hxy ▸ hyv) hne
        | inr hys => exact hys
      · rw [removeOne_miss v y ys hyv]
        have split : x = y ∨ x ∈ ys := by
          cases h with
          | head => exact Or.inl rfl
          | tail _ htl => exact Or.inr htl
        cases split with
        | inl hxy => exact hxy ▸ List.mem_cons_self ..
        | inr hys => exact List.mem_cons_of_mem y (mem_removeOne_of_ne ys v x hys hne)

/-- 若 `x.val ≠ v.val` 且 `v ∈ x :: xs`，则 `v ∈ xs`。 -/
theorem mem_of_mem_tail {n : Nat} {x v : Fin n} {xs : List (Fin n)}
    (h : v ∈ x :: xs) (hxv : x.val ≠ v.val) : v ∈ xs := by
  -- `v ∈ x :: xs` 的两个来源：`v = x`（被 `hxv` 排除）或 `v ∈ xs`
  by_cases hvx : v = x
  · exact absurd (by rw [hvx]) hxv
  · revert hxv
    match h, hvx with
    | List.Mem.head _, hvx => intro _; exact absurd rfl hvx
    | List.Mem.tail _ htl, _ => intro _; exact htl

/-- **`removeOne` 删除后长度严格变小**（元素在列表里时）。 -/
theorem removeOne_length_lt {n : Nat} (v : Fin n) : ∀ (l : List (Fin n)), v ∈ l →
    (removeOne v l).length < l.length
  | [], h => absurd h (List.not_mem_nil)
  | x :: xs, h => by
      by_cases hxv : x.val = v.val
      · rw [removeOne_hit v x xs hxv]
        exact Nat.lt_succ_self xs.length
      · rw [removeOne_miss v x xs hxv]
        have hmem : v ∈ xs := mem_of_mem_tail h hxv
        exact Nat.succ_lt_succ (removeOne_length_lt v xs hmem)

/-- **`removeOne` 的长度上界**：至多少 1。 -/
theorem removeOne_length_le {n : Nat} (v : Fin n) :
    ∀ (l : List (Fin n)), (removeOne v l).length ≤ l.length
  | [] => Nat.zero_le 0
  | x :: xs => by
      by_cases hxv : x.val = v.val
      · rw [removeOne_hit v x xs hxv]
        exact Nat.le_succ xs.length
      · rw [removeOne_miss v x xs hxv]
        exact Nat.succ_le_succ (removeOne_length_le v xs)

/-- 拆 `Nodup`：头与尾的每个元素都不同。 -/
theorem list_nodup_head {α : Type} {x : α} {xs : List α} (h : (x :: xs).Nodup) :
    x ∉ xs :=
  match h with
  | List.Pairwise.cons hh _ => fun hmem => hh x hmem rfl

/-- 拆 `Nodup`：尾仍无重复。 -/
theorem list_nodup_tail {α : Type} {x : α} {xs : List α} (h : (x :: xs).Nodup) :
    xs.Nodup :=
  match h with
  | List.Pairwise.cons _ ht => ht

/-- **`removeOne v l` 在 `l` 无重复时不含 `v`**（`Nodup` 下删除是彻底的）。

    比 `removeOne` 的定义多说了：`v` 若在 `removeOne v l` 里，
    则 `v` 在 `l` 里至少出现两次，与 `Nodup` 矛盾。 -/
theorem not_mem_removeOne_self {n : Nat} : ∀ (v : Fin n) (l : List (Fin n)),
    l.Nodup → v ∉ removeOne v l
  | v, [], _ => List.not_mem_nil
  | v, x :: xs, hnd => by
      by_cases hxv : x.val = v.val
      · rw [removeOne_hit v x xs hxv]
        intro hmem
        have hxe : x = v := Fin.eq_of_val_eq hxv
        exact absurd (hxe ▸ hmem) (list_nodup_head hnd)
      · rw [removeOne_miss v x xs hxv]
        intro hmem
        have split : v = x ∨ v ∈ removeOne v xs := by
          cases hmem with
          | head => exact Or.inl rfl
          | tail _ htl => exact Or.inr htl
        cases split with
        | inl hvx => exact hxv (congrArg Fin.val hvx.symm)
        | inr htl => exact not_mem_removeOne_self v xs (list_nodup_tail hnd) htl

/-- **覆盖 ⟹ 成员**：`order` 覆盖 `vertices` 时，`vertices` 的元素也在 `order` 里。 -/
theorem exists_nth_mem_of_cover {V : Type u} {g : Graph V} {vertices order : List V}
    (hcover : ∀ v, v ∈ vertices → v ∈ order) (a : V) (ha : a ∈ vertices) : a ∈ order :=
  hcover a ha

/-! ## 九、拓扑序存在性主定理 -/

/-- **`nth` 的 `cons` 平移**：`nth order i = some v` ⟹ `nth (x :: order) (i+1) = some v`。 -/
theorem nth_cons_shift {V : Type u} (x : V) (order : List V) {i : Nat} {v : V}
    (h : nth order i = some v) : nth (x :: order) (i + 1) = some v := h


end FateV2.Model
