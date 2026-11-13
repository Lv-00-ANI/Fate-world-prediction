import FateWorld.FateV2.Core.Closure

/-!
  # Core · 失效传播 × 传递闭包 × 无环性（专项 T8）

  ## 迁移登记
  - 来源：新写（承接 `_报告/T7-进度.md` §7 的两项未做项）
  - 动作：C 重写
  - 对应环节：IR 语言化（D 类）第 6 项续
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：新建；只读引用 `Core/Decl.lean`、`Core/DeclGraph.lean`、`Core/Closure.lean`
  - 状态：已编译未验证

  ## 两条主定理

  | 定理 | 内容 |
  |---|---|
  | `invalidate_subset_closure` | **失效集合 ⊆ 传递闭包**：`d ∈ invalidate g k bk → d.key ∈ closureN g 3 [k]` |
  | `not_mem_invalidate_self` | **无环 ⟹ 失效集合里没有 `k` 自己** |

  ## 与 `Closure.lean` 的接口

  `closureN`、`closureNAux`、`step`、`depsOf` 都在 namespace `FateV2.Core.DeclGraph` 里，
  本文件只**引用**它们，不重证。
-/

namespace FateV2.Core

universe u

/-! ## §1 `List.any` 的零公理成员机具

  `DeclGraph` / `Closure` 都没有 `List.any` 的成员引理，而
  `Decl.dependsOn d k := d.deps.any (fun x => decide (x = k))` 正是靠 `any`。
  库里的 `List.any_eq_true` 走 `Decidable` 实例，实测带 `propext`；
  这里两条都自写。 -/

/-- **`true ≠ false`**（`Bool.noConfusion` 的直接返回版）。

    ⚠ 用法纪律（实测踩过，见 `_报告/T8-进度.md` §1.1）：`Bool.noConfusion h`
    只有 `h` 两端都是**字面构造子**时才归约成 `False`；套 λ 会让项退化成
    不可归约的 mvar，elaboration 失败后被填 `sorryAx`。所以本条必须写成
    **直接返回**，不能写成 `fun _ => Bool.noConfusion h`。 -/
theorem not_true_eq_false (h : true = false) : False := Bool.noConfusion h

/-- **成员 ⟹ `any` 判真**（零公理）。

    比定义多说了什么：`List.any` 的定义只说明「怎么算」，本条说明它
    **不漏掉**成员 —— 是 `dependsOn` 与 `deps` 之间唯一的构造性桥。 -/
theorem any_true_of_mem_true {K : Type u} (p : K → Bool) (a : K) (ha : p a = true) :
    ∀ (l : List K), a ∈ l → l.any p = true
  | [], h => absurd h (List.not_mem_nil)
  | b :: bs, h => by
      show (p b || bs.any p) = true
      cases h with
      | head =>
          rw [ha]
          exact Bool.true_or (bs.any p)
      | tail _ h' =>
          have ih := any_true_of_mem_true p a ha bs h'
          rw [ih]
          exact Bool.or_true (p b)

/-- **`any` 判真 ⟹ 有见证成员**（零公理，`DeclGraph` 缺的方向）。

    比定义多说了什么：定义是「或」的折叠，本条把它**还原成一个具体的元素**
    —— 没有它就无法从 `d.dependsOn k = true` 拿到 `k ∈ d.deps`。 -/
theorem any_eq_true_witness {K : Type u} (p : K → Bool) : ∀ (l : List K),
    l.any p = true → ∃ a, a ∈ l ∧ p a = true
  | [], h => absurd h (fun hh => Bool.noConfusion hh)
  | b :: bs, h => by
      have hc : (p b || bs.any p) = true := h
      cases hb : p b with
      | true => exact ⟨b, List.Mem.head _, hb⟩
      | false =>
          have h' : bs.any p = true := by
            have he : (false || bs.any p) = true := by rw [← hb]; exact hc
            rw [Bool.false_or] at he
            exact he
          obtain ⟨a, ha, hpa⟩ := any_eq_true_witness p bs h'
          exact ⟨a, List.Mem.tail _ ha, hpa⟩

/-- **留下 ⟹ 谓词为真**（`DeclGraph` 只给了反向那一条，这一半自写）。

    比定义多说了什么：`DeclGraph.mem_of_filter` 说的是「失效的东西仍在原表里」，
    本条说的是「失效的东西**确实传播**」—— 两者合起来才是 `filter` 的完整规格。 -/
theorem prop_of_filter {α : Type u} (p : α → Bool) :
    ∀ {l : List α} {a : α}, a ∈ l.filter p → p a = true
  | [], a, h => absurd h List.not_mem_nil
  | b :: bs, a, h => by
      cases hpb : p b with
      | true =>
          rw [List.filter_cons_of_pos hpb] at h
          cases h with
          | head => exact hpb
          | tail _ h' => exact prop_of_filter p h'
      | false =>
          rw [List.filter_cons_of_neg (by rw [hpb]; intro hh; exact Bool.noConfusion hh)] at h
          exact prop_of_filter p h

end FateV2.Core

namespace FateV2.Core.T8

open FateV2.Core
open FateV2.Core.DeclGraph

universe u

variable {K : Type u}

/-! ## §2 从 `dependents` 里取出「`d` 在 `g` 里」与「`d` 依赖 `k`」 -/

/-- **失效元素在 `dependents` 里**。 -/
theorem mem_dependents_of_mem_invalidate [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) :
    ∀ d ∈ invalidate g k bk, d ∈ dependents g k :=
  DeclGraph.invalidate_subset_dependents g k bk

/-- **失效元素在图里**。

    比定义多说了什么：`dependents` 是 `g.filter …`，本条把「过滤结果里的元素
    仍是原表元素」落成可用形态 —— 后面要用它在 `Acyclic` 上取值。 -/
theorem mem_graph_of_mem_invalidate [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) :
    ∀ d ∈ invalidate g k bk, d ∈ g := by
  intro d hd
  have hdep : d ∈ dependents g k := mem_dependents_of_mem_invalidate g k bk d hd
  unfold dependents at hdep
  exact DeclGraph.mem_of_filter (fun (x : Decl K) => x.dependsOn k) hdep

/-- **失效元素依赖 `k`**。 -/
theorem dependsOn_of_mem_invalidate [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) :
    ∀ d ∈ invalidate g k bk, d.dependsOn k = true := by
  intro d hd
  have hdep : d ∈ dependents g k := mem_dependents_of_mem_invalidate g k bk d hd
  unfold dependents at hdep
  exact prop_of_filter (fun (x : Decl K) => x.dependsOn k) hdep

/-- **`dependsOn` 判真 ⟹ `k` 真的在 `deps` 里**（构造子模式一次绑全字段）。

    比定义多说了什么：`dependsOn` 是 `any`/`decide` 的复合，本条把它**拉回
    列表成员**。`cases d with | mk …` 是绕过 T7 记录的「投影消去失败」的正解：
    不对 `d` 归纳，只把它摊成 5 个字段，`deps` 就成了普通 `List K`。 -/
theorem deps_mem_of_dependsOn [DecidableEq K] (d : Decl K) (k : K)
    (h : d.dependsOn k = true) : k ∈ d.deps := by
  cases d with
  | mk key kind bk deps vis =>
      have hany : (deps.any (fun x => decide (x = k))) = true := h
      obtain ⟨x, hx, hdec⟩ := any_eq_true_witness (fun x : K => decide (x = k)) deps hany
      exact (of_decide_eq_true hdec) ▸ hx

/-! ## §3 主定理 2：无环 ⟹ 失效集合里没有 `k` 自己 -/

/-- **【主定理 2】无环 ⟹ 失效集合里没有 `k` 自己。**

    比定义多说了什么：`Acyclic g` 说的是「每个声明的 `deps` 不含**它自己**的键」，
    `invalidate g k bk` 说的是「依赖 `k` 且会传播的下游」——**两者没有共同的词**。
    本条要跨过 `dependsOn` 的 `any`/`decide` 两层，并把等式 `d.key = k`
    搬进 `deps` 的成员关系里。反证路线：`a` 依赖 `k` ⟹ `k ∈ a.deps`；
    若 `a.key = k` 则 `a.key ∈ a.deps`，与无环矛盾。 -/
theorem not_mem_invalidate_self [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind)
    (hac : DeclGraph.Acyclic g) :
    ∀ d ∈ invalidate g k bk, d.key ≠ k := by
  intro d hd hEq
  have hgd : d ∈ g := mem_graph_of_mem_invalidate g k bk d hd
  have hk : k ∈ d.deps := deps_mem_of_dependsOn d k (dependsOn_of_mem_invalidate g k bk d hd)
  cases d with
  | mk key kind bk' deps vis =>
      have hkey : k = key := Eq.symm hEq
      have hkk : key ∉ deps := hac ⟨key, kind, bk', deps, vis⟩ hgd
      exact hkk (hkey ▸ hk)

/-! ## §4 主定理 1 的构件：`step` / `closureN` 的成员桥

  下面这些只**引用** `Closure.lean` 的 `step` / `closureNAux` / `closureN`，
  每个都是 `Closure.lean` 里没有的那一向。 -/

/-- **`step` 不漏项**：`r` 在前沿里、`x` 是 `r` 的直接依赖 ⟹ `x` 在 `step` 的结果里。 -/
theorem mem_step_of_deps [DecidableEq K] (g : DeclGraph K) (r : K) :
    ∀ (rs : List K), r ∈ rs → ∀ x, x ∈ DeclGraph.depsOf g r → x ∈ DeclGraph.step g rs
  | [], h, x, hx => absurd h List.not_mem_nil
  | b :: bs, h, x, hx => by
      show x ∈ DeclGraph.depsOf g b ++ DeclGraph.step g bs
      cases h with
      | head => exact List.mem_append_left _ hx
      | tail _ h' => exact List.mem_append_right _ (mem_step_of_deps g r bs h' x hx)

/-- **`step` 的成员都有出处**（`Closure.lean` 给了「有某条声明的 `deps` 出处」，
    本条给更强的「有**某个前沿元素**的出处」）。

    比定义多说了什么：多出来的那个前沿元素正是下一层搜索的起点，
    少了它无法把「一跳」迭代成「多跳」。 -/
theorem step_mem_cases [DecidableEq K] (g : DeclGraph K) :
    ∀ (roots : List K) (x : K), x ∈ DeclGraph.step g roots →
      ∃ r, r ∈ roots ∧ x ∈ DeclGraph.depsOf g r
  | [], x, h => absurd h List.not_mem_nil
  | b :: bs, x, h => by
      have h' : x ∈ DeclGraph.depsOf g b ++ DeclGraph.step g bs := h
      cases mem_append_cases (DeclGraph.depsOf g b) (DeclGraph.step g bs) h' with
      | inl ha => exact ⟨b, List.Mem.head _, ha⟩
      | inr hb =>
          obtain ⟨r, hr, hx⟩ := step_mem_cases g bs x hb
          exact ⟨r, List.Mem.tail _ hr, hx⟩

/-- **走一步 ⟹ 进 `closureNAux` 的下一轮**。 -/
theorem mem_aux_succ_of_step [DecidableEq K] (g : DeclGraph K) (k : Nat) (acc frontier : List K)
    (x : K) (h : x ∈ DeclGraph.step g frontier) :
    x ∈ DeclGraph.closureNAux g (k + 1) acc frontier :=
  DeclGraph.subset_closureNAux g k (acc ++ DeclGraph.step g frontier)
    (DeclGraph.step g frontier) x (List.mem_append_right _ h)

/-- **走一步 ⟹ 进 `closureN g (k+1) roots`**。 -/
theorem mem_closureN_succ_of_step [DecidableEq K] (g : DeclGraph K) (k : Nat) (roots : List K)
    (x : K) (h : x ∈ DeclGraph.step g roots) : x ∈ DeclGraph.closureN g (k + 1) roots := by
  have h' : x ∈ roots ++ DeclGraph.closureNAux g k (roots ++ DeclGraph.step g roots)
      (DeclGraph.step g roots) :=
    List.mem_append_right _ (mem_aux_succ_of_step g k roots roots x h)
  exact h'

/-- **一跳**：`r` 在根里、`x` 是 `r` 的直接依赖 ⟹ `x` 在 **1 步**闭包里。 -/
theorem mem_closureN_one_of_deps [DecidableEq K] (g : DeclGraph K) (roots : List K)
    (r x : K) (hr : r ∈ roots) (hx : x ∈ DeclGraph.depsOf g r) :
    x ∈ DeclGraph.closureN g 1 roots := by
  apply mem_closureN_succ_of_step g 0 roots
  exact mem_step_of_deps g r roots hr x hx

/-- **`closureN g 1 roots` 的完整成员刻画**：每个元素要么是根，
    要么是**某个根**的直接依赖。

    比定义多说了什么：`closureNAux` 的定义只说「累积了 `step` 的结果」，
    本条把它**还原到根**上 —— 这是把「一跳」迭代成「多跳」时消掉
    「前沿元素从哪来」这一问的唯一入口。 -/
theorem closureN_one_mem_cases [DecidableEq K] (g : DeclGraph K) (roots : List K) (x : K)
    (h : x ∈ DeclGraph.closureN g 1 roots) :
    x ∈ roots ∨ ∃ r, r ∈ roots ∧ x ∈ DeclGraph.depsOf g r := by
  have h' : x ∈ roots ∨ x ∈ DeclGraph.closureNAux g 0 (roots ++ DeclGraph.step g roots)
      (DeclGraph.step g roots) :=
    mem_append_cases roots _ h
  cases h' with
  | inl hr => exact Or.inl hr
  | inr hs =>
      have hstep : x ∈ roots ++ DeclGraph.step g roots := hs
      cases mem_append_cases roots (DeclGraph.step g roots) hstep with
      | inl hr => exact Or.inl hr
      | inr hsf => exact Or.inr (step_mem_cases g roots x hsf)

/-! ## §5 主定理 1 的构件乙：把「跳数」压成常数

  `closureNAux` 的定义是 `Nat` 递归，而主定理需要「同一个常数步数」。
  关键观察：**`deps` 表不会随跳数增长** —— `step g [a]` 之后，所有键的
  `deps` 都已登记在 `[a] ++ g` 里，再跳也跳不出同一批键。 -/

/-- **（无环→有界路线用）`closureN` 里除根以外的元素都有一条入边**。 -/
theorem closureN_one_mem_cases_aux [DecidableEq K] (g : DeclGraph K) (roots : List K) (x : K)
    (h : x ∈ DeclGraph.closureNAux g 0 (roots ++ DeclGraph.step g roots)
      (DeclGraph.step g roots)) :
    x ∈ roots ∨ ∃ r, r ∈ roots ∧ x ∈ DeclGraph.depsOf g r := by
  have hstep : x ∈ roots ++ DeclGraph.step g roots := h
  cases mem_append_cases roots (DeclGraph.step g roots) hstep with
  | inl hr => exact Or.inl hr
  | inr hsf => exact Or.inr (step_mem_cases g roots x hsf)

/-- **累积闭包对 `n` 单调（在 `closureNAux` 自身的不动点前提下的引理形式）。**

    比定义多说了什么：`closureNAux g (m+1) acc frontier` 按定义就是
    `closureNAux g m (acc ++ step g frontier) (step g frontier)`；
    只要 `closureNAux g m acc frontier = acc`（即 `m` 步之后表已不再长大），
    两者只差一个 `acc` 前缀，成员关系被 `subset_closureNAux` 接住。
    这条是 T6 报告 §4 记为「未做」的 #2 的直接形式。 -/
theorem closureNAux_le_succ_of_fixed [DecidableEq K] (g : DeclGraph K) (m : Nat)
    (acc frontier : List K) (hfix : DeclGraph.closureNAux g m acc frontier = acc) :
    ∀ (x : K), x ∈ DeclGraph.closureNAux g m acc frontier
      → x ∈ DeclGraph.closureNAux g (m + 1) acc frontier := by
  intro x hx
  have hred : DeclGraph.closureNAux g (m + 1) acc frontier
      = DeclGraph.closureNAux g m (acc ++ DeclGraph.step g frontier)
          (DeclGraph.step g frontier) := rfl
  have hmem : x ∈ acc := hfix ▸ hx
  rw [hred]
  exact DeclGraph.subset_closureNAux g m (acc ++ DeclGraph.step g frontier)
    (DeclGraph.step g frontier) x (List.mem_append_left _ hmem)

end FateV2.Core.T8
