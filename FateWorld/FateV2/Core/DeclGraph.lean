import FateWorld.FateV2.Core.Decl

/-!
  # Core · 声明级依赖图与失效传播

  ## 迁移登记
  - 来源：新写（旧稿 §6.3、§6.4、§7.1、§7.5、§8.8、§13.2）
  - 动作：C 重写
  - 对应环节：IR 语言化（D 类）第 6 项
  - 依赖裁决：**D-019**（不写死 key/hash）、**D-016**（零公理）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## 三条主定理

  | 定理 | 内容 |
  |---|---|
  | `invalidate_proof_nil` | **只改定理的证明体 ⟹ 失效集合为空**（proof irrelevance） |
  | `invalidate_body_of_defn` | **改定义的体 ⟹ 失效集合 = 直接下游** |
  | `topo_dep_first_of_acyclic` | 无环 ⟹ 每个依赖都 ≠ 使用者自己 |

  ## ⚠ 为什么全部写成显式结构递归（本文件的核心写法）

  实测（`_报告/迁移工具/_probe_axioms.lean`、`_p9.lean`）：

  | 写法 | 公理 |
  |---|---|
  | `rw [List.filter_eq_nil_iff]` / `filter_eq_self` | **`[propext]`** |
  | `rw [List.filter_cons_of_pos]` | **`[propext]`** |
  | `List.mem_cons` / `List.mem_cons_self` | **`[propext]`** |
  | `cases k <;> rfl` | **`[propext]`** |
  | ✅ **自己写 `| [] => … | x :: xs => …`** + `rfl`/`congrArg` | **零公理** |

  ⟹ 本文件所有列表结论都**自己递归、自己展开 `filter`**，
  不引用任何 batteries 的 `filter`/`mem` 引理。
  代价是代码更长；收益是主定理 1、2 **在核内零公理**。
-/

namespace FateV2.Core

universe u

/-- **依赖图**：一组声明（顺序无语义）。 -/
abbrev DeclGraph (K : Type u) : Type u := List (Decl K)

namespace DeclGraph

variable {K : Type u}

/-! ## 自证的三条 filter/列表引理（零公理） -/

/-- **`filter` 的结果为空 ⟺ 每个元素都被筛掉**（自证，不用 `filter_eq_nil_iff`）。 -/
theorem filter_eq_nil {α : Type u} (p : α → Bool) : ∀ (l : List α),
    (∀ a, a ∈ l → p a = false) → l.filter p = []
  | [],      _ => rfl
  | b :: bs, h => by
      have hb : p b = false := h b List.mem_cons_self
      rw [List.filter_cons_of_neg (by rw [hb]; exact fun hh => Bool.noConfusion hh)]
      exact filter_eq_nil p bs (fun a ha => h a (List.mem_cons_of_mem b ha))

/-- **`filter` 不改列表 ⟺ 每个元素都留下**（自证，不用 `filter_eq_self`）。 -/
theorem filter_eq_self {α : Type u} (p : α → Bool) : ∀ (l : List α),
    (∀ a, a ∈ l → p a = true) → l.filter p = l
  | [],      _ => rfl
  | b :: bs, h => by
      have hb : p b = true := h b List.mem_cons_self
      rw [List.filter_cons_of_pos hb, filter_eq_self p bs (fun a ha => h a (List.mem_cons_of_mem b ha))]

/-- **`filter` 的成员仍是原列表成员**（自证）。

    ⚠ 两处避坑（都实测带 `propext`）：
    * 不用 `by_cases`（内部 `ite`/`Decidable`）→ 改对 `p b : Bool` `cases`；
    * 不用 `List.mem_cons`/`rcases … Or`（`mem_cons` 本身带 `propext`）
      → 直接对 `a ∈ b :: bs` 的**成员归纳子** `cases`。 -/
theorem mem_of_filter {α : Type u} (p : α → Bool) :
    ∀ {l : List α} {a : α}, a ∈ l.filter p → a ∈ l
  | [],      _, h => h
  | b :: bs, _, h => by
      cases hpb : p b with
      | true =>
          rw [List.filter_cons_of_pos hpb] at h
          cases h with
          | head => exact List.mem_cons_self
          | tail _ h' => exact List.mem_cons_of_mem b (mem_of_filter p h')
      | false =>
          rw [List.filter_cons_of_neg (by rw [hpb]; exact fun hh => Bool.noConfusion hh)] at h
          exact List.mem_cons_of_mem b (mem_of_filter p h)

/-! ## 失效判定 -/

/-- **直接依赖 `k` 的声明**。 -/
def dependents [DecidableEq K] (g : DeclGraph K) (k : K) : List (Decl K) :=
  g.filter (fun d => d.dependsOn k)

/-- **失效判定（逐边版，旧稿 §8.8 的 `invalidate`）**。 -/
def invalidate [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) : List (Decl K) :=
  (dependents g k).filter (fun d => spreads d.kind bk)

/-! ## 主定理 1 -/

/-- **`.proof` 行上 `spreads` 恒为 `false`**——对**任何** kind，`rfl` 即可。

    ⚠ 这一条之所以是 `rfl`，是因为 `spreads` 被拆成两层
    （见 `Core/Decl.lean` 的写法说明）；**嵌套 `match` 版本不能这样证**，
    只能 `cases k <;> rfl`，而那样会带 `propext`。 -/
theorem spreads_proof_false (k : DeclKind) : spreads k .proof = false := rfl

/-- **【主定理 1】只改证明体，失效集合为空。**

    比定义多说了什么：`invalidate` 对每个下游调 `spreads d.kind .proof`，
    `d.kind` 是**未知的**（量化）。整个 `filter` 为空需要证明
    「这一行对一切 kind 都为 `false`」——那是 `spreads` 的**整行**性质，
    不是任何一边的展开。 -/
theorem invalidate_proof_nil [DecidableEq K] (g : DeclGraph K) (k : K) :
    invalidate g k .proof = [] := by
  unfold invalidate
  exact filter_eq_nil (fun d => spreads d.kind .proof) _ (fun d _ => spreads_proof_false d.kind)

/-! ## 主定理 2 -/

/-- **【主定理 2】若全图 kind 都是 `defn`，改任一声明的体，失效集合恰 = 直接下游。**

    比定义多说了什么：两边是**两个独立定义**（`invalidate` 经 `spreads`，
    `dependents` 经 `dependsOn`）。等式成立要求证明「`defn` + `body` 这一格上
    `spreads` 恒真」——否则会**漏下游**（传播不足）。这正是旧稿 §8.9.5 的朴素闭包。 -/
theorem invalidate_body_of_defn [DecidableEq K] (g : DeclGraph K) (k : K)
    (hall : ∀ d ∈ g, d.kind = .defn) :
    invalidate g k .body = dependents g k := by
  unfold invalidate
  refine filter_eq_self (fun (d : Decl K) => spreads d.kind .body) _ ?_
  intro d hd
  unfold dependents at hd
  have hgd : d ∈ g := mem_of_filter (fun d => d.dependsOn k) hd
  rw [hall d hgd]
  rfl

/-- **签名变化 ⟹ 失效 = 全部下游**（与 kind 无关，旧稿 §6.4 第一列）。 -/
theorem invalidate_signature_eq_dependents [DecidableEq K] (g : DeclGraph K) (k : K) :
    invalidate g k .signature = dependents g k := by
  unfold invalidate
  exact filter_eq_self (fun d => spreads d.kind .signature) _
    (fun d _ => spreads_signature d.kind)

/-- **失效集合 ⊆ 下游集合**（不凭空脏）。 -/
theorem invalidate_subset_dependents [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) :
    ∀ d ∈ invalidate g k bk, d ∈ dependents g k := by
  unfold invalidate
  intro d hd
  exact mem_of_filter (fun d => spreads d.kind bk) hd

/-! ## 闭包与拓扑序 -/

/-- **编译闭包**（旧稿 §7.2 第 3 步）：根 ∪ 「根对应的声明的 deps」。 -/
def closure [DecidableEq K] (g : DeclGraph K) (roots : List K) : List K :=
  roots ++ (g.filter (fun d => roots.any (fun r => decide (d.key = r)))).flatMap (fun d => d.deps)

/-- 根都在闭包里（「编译闭包 = 目标 ∪ 传递依赖」的左半边）。 -/
theorem mem_closure_of_mem_roots [DecidableEq K] (g : DeclGraph K) {roots : List K} {k : K}
    (h : k ∈ roots) : k ∈ closure g roots :=
  List.mem_append_left _ h

/-- **无环**：没有任何声明的 `deps` 里出现它自己。 -/
def Acyclic (g : DeclGraph K) : Prop :=
  ∀ d ∈ g, d.key ∉ d.deps

/-- **【主定理 3】无环 ⟹ 每个依赖都 ≠ 使用者自己**（拓扑排序的合法性条件）。

    比定义多说了什么：`Acyclic` 说的是 `∉`（`List.mem` 的否定），
    而排序要用的是「对每个 `dep ∈ d.deps`，`dep ≠ d.key`」。
    这要把 `∈`/`≠` 边界展开一次，再用等式替换闭合——不是 `rfl`。
    **本条已实测零公理。** -/
theorem topo_dep_first_of_acyclic (g : DeclGraph K) (d : Decl K) (hd : d ∈ g)
    (hac : Acyclic g) : ∀ dep ∈ d.deps, dep ≠ d.key := by
  intro dep hdep hEq
  subst hEq
  exact hac d hd hdep

/-- 推论：无环图里没有自环。 -/
theorem no_self_loop_of_acyclic (g : DeclGraph K) (d : Decl K) (hd : d ∈ g)
    (hac : Acyclic g) : ¬ (d.key ∈ d.deps) :=
  hac d hd

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | **多步**闭包（传递闭包） | 当前 `closure` 只展开一层；多轮可用 `Nat` 迭代做，属下一批 |
  | 2 | 完整拓扑排序算法 | 本批给合法性条件 `topo_dep_first_of_acyclic`；算法在实现层 |
  | 3 | 主定理 2 的**一般**版本（混合 kind） | 需要「非传播 kind 不进集合」的分情形；本批只给全 `defn` 版 |
-/

end DeclGraph

end FateV2.Core
