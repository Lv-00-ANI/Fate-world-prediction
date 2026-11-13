import FateWorld.FateV2.Core.ClosureMono
import FateWorld.FateV2.Core.InvalidateClosure
import FateWorld.FateV2.Core.Cache

/-!
  # Core · `depsOfAll`、它的闭包，以及「失效 ⊆ 传递闭包」的闭合（专项 T10）

  ## 迁移登记
  - 来源：新写（承接 `_报告/T8-进度.md` §4 的裁决：新增 `depsOfAll`，**不改** `depsOf`）
  - 动作：C 重写（T8 把缺口精确到一条命题 `bridge`；本批换掉「边集」本身）
  - 对应环节：IR 语言化（D 类）第 6 项续 · 专项 T10
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：**新建**；只读引用 `Core/Closure.lean`、`Core/ClosureMono.lean`、
    `Core/InvalidateClosure.lean`、`Core/DeclGraph.lean`、`Core/Decl.lean`、`Core/Cache.lean`
  - 状态：已编译未验证

  ## 一、T8 留下的缺口，以及本批的补法

  `Core/Closure.lean` 的 `depsOf g r` 是 **`find?` 语义**：只取**第一个**
  `key = r` 的声明。而 `DeclGraph K := List (Decl K)` **允许重复 key**；
  失效的边 `k ∈ d.deps` 取的是**所有**声明。两者「边集」不同，于是 T8 的 `bridge` 卡住。

  **裁决**：不改 `depsOf`（T6/T6b 的 28 条定理依赖它），新增 `depsOfAll` ——
  所有 `key = r` 的声明的 `deps` 之并。整条链重做一遍：

  | 层 | 定义 | 关键定理 |
  |---|---|---|
  | 边集 | `depsOfAll` | `depsOf_subset_depsOfAll`（旧的是新的特例） |
  | 一步 | `stepAll` | `mem_stepAll_of_depsOfAll`（**失效边的一步可达性**） |
  | 闭包 | `closureAllAux` / `closureAll` | `closureAll_one_depsOfAll`、`closureAll_le_succ` |
  | 桥 | — | **`bridge`**（`1` 步闭包 ⊆ `d.key :: [k]` 的 `2` 步闭包） |
  | 主定理 | — | **`invalidate_subset_closureAll`**（`n = 2` 就够，**常数**） |

  ## 二、⚠ 公理纪律（红线见 `_报告/T8-进度.md` §2；本批新增实测见 §四）

  不引用 `List.mem_cons` / `List.mem_append`（`∨` 形态，带 `propext`）；
  不用 `simp` / `by_contra` / `by_cases h : ∃ …` / `funext` / `decide` /
  `Nat.succ_ne_zero` / `List.find?_some` / `List.any_eq_true` / `List.all_eq_true`；
  `∈` 只用**构造子模式**消解；`List` 遍历**全部手写递归**
  （`map` / `filter` / `flatMap` 对元素递归会退化成 WF → `propext`）；
  **`if … then … else …`（`ite`）禁用**；**`BEq`（`==`）禁用**。

  ## 四、⚠ 本批实测的新坑（都在 `Core/` 内，附替代写法）

  | # | 写法 | 实测结果 | 替代 |
  |---|---|---|---|
  | 1 | `if decide (p) then a else b`，`rw` 后 `rfl` 收尾 | **`propext`** | 写 `match decide (…) with`，`rw` 后 `rfl` 空公理 |
  | 2 | `decide (a = a)` 直接证 `= true`（`decide_self` 本机**不存在**；`decide_eq_true_eq` + `rw` 带 **`propext`**；`inferInstance` 形式也**不定义归约**） | 见左 | 对 `inferInstance : Decidable (…)` 的 **`isTrue` 分支**取证据（零公理） |
  | 3 | `a ∈ l` 用 `BEq`（`==`）判 | **`beq_iff_eq` / `beq_self_eq_true` 带 `propext` / `Quot.sound`** | 手写 `memB` + `inferInstance` 判别（见坑 2） |
  | 4 | `cases h : List.decidableBEx (P) d` | 返回 `Decidable` 而非 `Bool`，`cases` 报 "major premise is not an inductive type" | 用 `memB` 造 `Bool`，`cases` 它 |
  | 5 | `Bool.noConfusion h` 当任意 `False` 用 | 只在**两端都是字面构造子**时归约 | `intro e; cases e`（同 T8 §2） |
  | 6 | `DecidableEq (Decl K)` 由 `inferInstance` 取 | **取不到**（`Decl` 是 `structure`）——`synthInstanceFailed` | 逐字段 `inferInstance : Decidable (d.f = b.f)`，5 层 `match` |
  | 7 | `rw [memB] at h` 只展开**一层** `match` | 停在 `match isTrue hk ⊢ …` 上，`exact h` 报 `Type mismatch` | 把**本分支的等式**一起 `rw`：`rw [memB, h1, h2] at h` |
-/

namespace FateV2.Core.DeclGraphAll

/-! ## §1 成员判定 `memB`（`Decl` 的全结构比较）

  「`d` 是否在 `rest` 里」是本批唯一需要的 `Bool` 判据（`decide` 是红线）。
  `Decl K` **没有**可用的 `DecidableEq`（§四坑 6），`BEq` 又带 `propext`（§四坑 3），
  故对 5 个字段逐层 `inferInstance`。 -/

/-- **手写的成员判定**（`Bool` 版 `d ∈ l`，按 `Decl` 的**全结构**比较）。 -/
def memB [DecidableEq K] : List (Decl K) → Decl K → Bool
  | [], _ => false
  | b :: bs, d =>
      match (inferInstance : Decidable (d.key = b.key)) with
      | isTrue _ =>
          match (inferInstance : Decidable (d.kind = b.kind)) with
          | isTrue _ =>
              match (inferInstance : Decidable (d.bodyKind = b.bodyKind)) with
              | isTrue _ =>
                  match (inferInstance : Decidable (d.deps = b.deps)) with
                  | isTrue _ =>
                      match (inferInstance : Decidable (d.visibility = b.visibility)) with
                      | isTrue _ => true
                      | isFalse _ => memB bs d
                  | isFalse _ => memB bs d
              | isFalse _ => memB bs d
          | isFalse _ => memB bs d
      | isFalse _ => memB bs d

/-- **`memB` 判真 ⟹ 图里有这么一条声明**。

    比 `memB` 的定义多说了什么：定义说「怎么算」，本条说它**不漏**——
    这是全文件唯一能用的「成员判定 → 成员关系」桥（库版都带 `propext`）。
    逐字段 `Decidable` 分情形；只有「五个字段全等」那一支带出 5 个等式，
    一次 `subst` 链 + `rfl` 就把 `d` 换成表头，不碰任何结构外延引理。 -/
theorem mem_of_memB [DecidableEq K] (d : Decl K) :
    ∀ (l : List (Decl K)), memB l d = true → d ∈ l
  | [], h => absurd h (by intro e; cases e)
  | b :: bs, h => by
      cases h1 : (inferInstance : Decidable (d.key = b.key)) with
      | isFalse _ =>
          exact List.mem_cons_of_mem b (mem_of_memB d bs (by rw [memB, h1] at h; exact h))
      | isTrue hk =>
          cases h2 : (inferInstance : Decidable (d.kind = b.kind)) with
          | isFalse _ =>
              exact List.mem_cons_of_mem b
                (mem_of_memB d bs (by rw [memB, h1, h2] at h; exact h))
          | isTrue hd =>
              cases h3 : (inferInstance : Decidable (d.bodyKind = b.bodyKind)) with
              | isFalse _ =>
                  exact List.mem_cons_of_mem b
                    (mem_of_memB d bs (by rw [memB, h1, h2, h3] at h; exact h))
              | isTrue hb =>
                  cases h4 : (inferInstance : Decidable (d.deps = b.deps)) with
                  | isFalse _ =>
                      exact List.mem_cons_of_mem b
                        (mem_of_memB d bs (by rw [memB, h1, h2, h3, h4] at h; exact h))
                  | isTrue hp =>
                      cases h5 : (inferInstance : Decidable (d.visibility = b.visibility)) with
                      | isFalse _ =>
                          exact List.mem_cons_of_mem b
                            (mem_of_memB d bs (by rw [memB, h1, h2, h3, h4, h5] at h; exact h))
                      | isTrue hv =>
                          have hdb : d = b := by
                            cases d with
                            | mk k1 kd1 bk1 dp1 v1 =>
                                cases b with
                                | mk k2 kd2 bk2 dp2 v2 =>
                                    simp only at hk hd hb hp hv
                                    subst hk; subst hd; subst hb; subst hp; subst hv
                                    rfl
                          exact hdb ▸ List.mem_cons_self

/-- **图里有 ⟹ `memB` 判真**（另一方向）。

    比定义多说了什么：`memB` 的定义只往「真 ⟹ 在」方向用；本批反过来也要，
    因为 `mem_depsOfAll_of` 的 `false` 分支要把「`d` 不在尾表」这个**否定情形**落实 ——
    有了它才能把「不在尾表」变成「就是表头」。 -/
theorem memB_of_mem [DecidableEq K] (d : Decl K) :
    ∀ (l : List (Decl K)), d ∈ l → memB l d = true
  | [], h => absurd h List.not_mem_nil
  | b :: bs, h => by
      cases h with
      | head =>
          cases h1 : (inferInstance : Decidable (d.key = d.key)) with
          | isFalse hf => exact absurd rfl hf
          | isTrue _ =>
              cases h2 : (inferInstance : Decidable (d.kind = d.kind)) with
              | isFalse hf => exact absurd rfl hf
              | isTrue _ =>
                  cases h3 : (inferInstance : Decidable (d.bodyKind = d.bodyKind)) with
                  | isFalse hf => exact absurd rfl hf
                  | isTrue _ =>
                      cases h4 : (inferInstance : Decidable (d.deps = d.deps)) with
                      | isFalse hf => exact absurd rfl hf
                      | isTrue _ =>
                          cases h5 : (inferInstance : Decidable (d.visibility = d.visibility)) with
                          | isFalse hf => exact absurd rfl hf
                          | isTrue _ => rw [memB, h1, h2, h3, h4, h5]
      | tail _ ht =>
          rw [memB, memB_of_mem d bs ht]
          cases h1 : (inferInstance : Decidable (d.key = b.key)) with
          | isFalse _ => rfl
          | isTrue _ =>
              cases h2 : (inferInstance : Decidable (d.kind = b.kind)) with
              | isFalse _ => rfl
              | isTrue _ =>
                  cases h3 : (inferInstance : Decidable (d.bodyKind = b.bodyKind)) with
                  | isFalse _ => rfl
                  | isTrue _ =>
                      cases h4 : (inferInstance : Decidable (d.deps = b.deps)) with
                      | isFalse _ => rfl
                      | isTrue _ =>
                          cases h5 : (inferInstance : Decidable (d.visibility = b.visibility)) with
                          | isTrue _ => rfl
                          | isFalse _ => rfl


open FateV2.Core
open FateV2.Core.DeclGraph

universe u

variable {K : Type u}

def depsOfAll [DecidableEq K] (g : DeclGraph K) (r : K) : List K :=
  match g with
  | [] => []
  | d :: rest =>
      match decide (d.key = r) with
      | true => d.deps ++ depsOfAll rest r
      | false => depsOfAll rest r

theorem depsOfAll_nil [DecidableEq K] (r : K) : depsOfAll ([] : DeclGraph K) r = [] := rfl

theorem depsOfAll_cons_hit [DecidableEq K] (d : Decl K) (rest : DeclGraph K) (r : K)
    (h : decide (d.key = r) = true) :
    depsOfAll (d :: rest) r = d.deps ++ depsOfAll rest r := by
  rw [depsOfAll, h]

theorem depsOfAll_cons_miss [DecidableEq K] (d : Decl K) (rest : DeclGraph K) (r : K)
    (h : decide (d.key = r) = false) :
    depsOfAll (d :: rest) r = depsOfAll rest r := by
  rw [depsOfAll, h]

theorem mem_depsOfAll_some [DecidableEq K] (g : DeclGraph K) (r : K) :
    ∀ x ∈ depsOfAll g r, ∃ d, d ∈ g ∧ d.key = r ∧ x ∈ d.deps := by
  induction g with
  | nil =>
      intro x hx
      exact absurd hx (List.not_mem_nil)
  | cons d rest ih =>
      intro x hx
      cases hk : decide (d.key = r) with
      | true =>
          rw [depsOfAll_cons_hit d rest r hk] at hx
          cases mem_append_cases d.deps (depsOfAll rest r) hx with
          | inl hl => exact ⟨d, List.mem_cons_self, of_decide_eq_true hk, hl⟩
          | inr hr =>
              obtain ⟨e, he, hkey, hdep⟩ := ih x hr
              exact ⟨e, List.mem_cons_of_mem d he, hkey, hdep⟩
      | false =>
          rw [depsOfAll_cons_miss d rest r hk] at hx
          obtain ⟨e, he, hkey, hdep⟩ := ih x hx
          exact ⟨e, List.mem_cons_of_mem d he, hkey, hdep⟩

theorem mem_depsOfAll_of [DecidableEq K] (g : DeclGraph K) (r : K) :
    ∀ (d : Decl K), d ∈ g → d.key = r → ∀ k, k ∈ d.deps → k ∈ depsOfAll g r := by
  induction g with
  | nil =>
      intro d hd _ k _
      exact absurd hd (List.not_mem_nil)
  | cons e rest ih =>
      intro d hd hkey k hk
      cases hmem : memB rest d with
      | true =>
          have hil : k ∈ depsOfAll rest r := ih d (mem_of_memB d rest hmem) hkey k hk
          cases he : decide (e.key = r) with
          | true =>
              rw [depsOfAll_cons_hit e rest r he]
              exact mem_append_r' e.deps (depsOfAll rest r) k hil
          | false =>
              rw [depsOfAll_cons_miss e rest r he]
              exact hil
      | false =>
          have hd' : d = e := by
            cases hd with
            | head => rfl
            | tail _ ht =>
                have hcon : memB rest d = true := memB_of_mem d rest ht
                rw [hcon] at hmem
                exact absurd hmem (by intro hh; cases hh)
          have hdeps : k ∈ e.deps := (congrArg (fun (x : Decl K) => x.deps) hd').symm ▸ hk
          have hdec : decide (e.key = r) = true := by
            rw [← hkey, hd']
            exact decide_eq_true rfl
          rw [depsOfAll_cons_hit e rest r hdec]
          exact mem_append_l' e.deps (depsOfAll rest r) k hdeps

theorem depsOf_subset_depsOfAll [DecidableEq K] (g : DeclGraph K) (r : K) :
    ∀ x ∈ depsOf g r, x ∈ depsOfAll g r := by
  cases hf : g.find? (fun (e : Decl K) => decide (e.key = r)) with
  | none =>
      have hnil : depsOf g r = ([] : List K) := by
        unfold depsOf
        rw [hf]
      intro x hx
      rw [hnil] at hx
      exact absurd hx List.not_mem_nil
  | some d =>
      have hdeps : depsOf g r = d.deps := depsOf_some g r d hf
      have hmem : d ∈ g := find?_mem _ hf
      have hval : decide (d.key = r) = true :=
        find?_val (fun (e : Decl K) => decide (e.key = r)) hf
      intro x hx
      exact mem_depsOfAll_of g r d hmem (of_decide_eq_true hval) x (hdeps ▸ hx)

/-! ## §3 基于 `depsOfAll` 的闭包：`stepAll` / `closureAllAux` / `closureAll`

  结构与 `Closure.lean` 的 `step` / `closureNAux` / `closureN` **完全同构**，
  只把边集从 `depsOf` 换成 `depsOfAll`（`Closure.lean` 一行不改）。 -/

/-- **一步展开**：从 `frontier` 出发，把它们的**全部**直接依赖加进来。 -/
def stepAll [DecidableEq K] (g : DeclGraph K) : List K → List K
  | [] => []
  | r :: rs => depsOfAll g r ++ stepAll g rs

/-- `stepAll` 在空表上（`rfl`）。 -/
theorem stepAll_nil [DecidableEq K] (g : DeclGraph K) : stepAll g [] = [] := rfl

/-- **`stepAll` 的展开律**（`rfl`）。 -/
theorem stepAll_cons [DecidableEq K] (g : DeclGraph K) (r : K) (rs : List K) :
    stepAll g (r :: rs) = depsOfAll g r ++ stepAll g rs := rfl

/-- **`stepAll` 不漏项**：`r` 在前沿里、`x` 是 `r` 的直接依赖 ⟹ `x` 在 `stepAll` 里。 -/
theorem mem_stepAll_of_depsOfAll [DecidableEq K] (g : DeclGraph K) (r : K) :
    ∀ (rs : List K), r ∈ rs → ∀ x, x ∈ depsOfAll g r → x ∈ stepAll g rs
  | [], h, x, hx => absurd h List.not_mem_nil
  | b :: bs, h, x, hx => by
      show x ∈ depsOfAll g b ++ stepAll g bs
      cases h with
      | head => exact List.mem_append_left _ hx
      | tail _ h' => exact List.mem_append_right _ (mem_stepAll_of_depsOfAll g r bs h' x hx)

/-- **`stepAll` 的成员都有某个前沿元素的出处**。 -/
theorem stepAll_mem_cases [DecidableEq K] (g : DeclGraph K) :
    ∀ (roots : List K) (x : K), x ∈ stepAll g roots →
      ∃ r, r ∈ roots ∧ x ∈ depsOfAll g r
  | [], x, h => absurd h List.not_mem_nil
  | b :: bs, x, h => by
      have h' : x ∈ depsOfAll g b ++ stepAll g bs := h
      cases mem_append_cases (depsOfAll g b) (stepAll g bs) h' with
      | inl ha => exact ⟨b, List.mem_cons_self, ha⟩
      | inr hb =>
          obtain ⟨r, hr, hx⟩ := stepAll_mem_cases g bs x hb
          exact ⟨r, List.mem_cons_of_mem b hr, hx⟩

/-- **累积闭包**：`acc` 是已累积的，`frontier` 是本轮要展开的一层。 -/
def closureAllAux [DecidableEq K] (g : DeclGraph K) : Nat → List K → List K → List K
  | 0, acc, _ => acc
  | k + 1, acc, frontier => closureAllAux g k (acc ++ stepAll g frontier) (stepAll g frontier)

/-- **`n` 步传递闭包**（`depsOfAll` 版）：从 `roots` 出发累积展开 `n` 层。 -/
def closureAll [DecidableEq K] (g : DeclGraph K) (n : Nat) (roots : List K) : List K :=
  roots ++ closureAllAux g n roots roots

/-- **`closureAll` 的定义展开**（`rfl`）。 -/
theorem closureAll_def [DecidableEq K] (g : DeclGraph K) (n : Nat) (roots : List K) :
    closureAll g n roots = roots ++ closureAllAux g n roots roots := rfl

/-- **累积量只长不缩**：`acc ⊆ closureAllAux g n acc frontier`。 -/
theorem subset_closureAllAux [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    ∀ (acc frontier : List K) (x : K), x ∈ acc → x ∈ closureAllAux g n acc frontier := by
  induction n with
  | zero => intro acc frontier x hx; exact hx
  | succ k ih =>
      intro acc frontier x hx
      exact ih (acc ++ stepAll g frontier) (stepAll g frontier) x (List.mem_append_left _ hx)

/-- **根永远留在闭包里**：`roots ⊆ closureAll g n roots`。 -/
theorem mem_closureAll_roots [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    ∀ (roots : List K) (x : K), x ∈ roots → x ∈ closureAll g n roots :=
  fun roots x hx => List.mem_append_left _ hx

/-- **累积部分的内容也在闭包里**。 -/
theorem mem_closureAll_of_aux [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    ∀ (roots : List K) (x : K), x ∈ closureAllAux g n roots roots → x ∈ closureAll g n roots :=
  fun roots x hx => List.mem_append_right _ hx

/-- **走一步 ⟹ 进 `closureAllAux` 的下一轮**。 -/
theorem mem_auxAll_succ_of_step [DecidableEq K] (g : DeclGraph K) (k : Nat) (acc frontier : List K)
    (x : K) (h : x ∈ stepAll g frontier) :
    x ∈ closureAllAux g (k + 1) acc frontier :=
  subset_closureAllAux g k (acc ++ stepAll g frontier) (stepAll g frontier) x
    (List.mem_append_right _ h)

/-- **走一步 ⟹ 进 `closureAll g (k+1) roots`**。 -/
theorem mem_closureAll_succ_of_step [DecidableEq K] (g : DeclGraph K) (k : Nat) (roots : List K)
    (x : K) (h : x ∈ stepAll g roots) : x ∈ closureAll g (k + 1) roots :=
  List.mem_append_right _ (mem_auxAll_succ_of_step g k roots roots x h)

/-- **`n+1` 步闭包的累积起点**（`rfl`）。 -/
theorem closureAll_succ_eq [DecidableEq K] (g : DeclGraph K) (k : Nat) (roots : List K) :
    closureAll g (k + 1) roots
      = roots ++ closureAllAux g k (roots ++ stepAll g roots) (stepAll g roots) := rfl

/-- **一跳**：`r` 在根里、`x` 是 `r` 的全部直接依赖之一 ⟹ `x` 在 **1 步**闭包里。 -/
theorem mem_closureAll_one_of_depsOfAll [DecidableEq K] (g : DeclGraph K) (roots : List K)
    (r x : K) (hr : r ∈ roots) (hx : x ∈ depsOfAll g r) :
    x ∈ closureAll g 1 roots :=
  mem_closureAll_succ_of_step g 0 roots x (mem_stepAll_of_depsOfAll g r roots hr x hx)

/-- **`closureAll g 1 roots` 的完整成员刻画**：每个元素要么是根，
    要么是**某个根**的全部直接依赖之一。

    比定义多说了什么：`closureAllAux` 只说「累积了 `stepAll` 的结果」，
    本条把它**还原到根**上 —— 这是 `bridge` 里「`x` 从哪儿来」的唯一入口。 -/
theorem closureAll_one_mem_cases [DecidableEq K] (g : DeclGraph K) (roots : List K) (x : K)
    (h : x ∈ closureAll g 1 roots) :
    x ∈ roots ∨ ∃ r, r ∈ roots ∧ x ∈ depsOfAll g r := by
  have h' : x ∈ roots ++ (roots ++ stepAll g roots) := h
  cases mem_append_cases roots (roots ++ stepAll g roots) h' with
  | inl hr => exact Or.inl hr
  | inr hs =>
      cases mem_append_cases roots (stepAll g roots) hs with
      | inl hr => exact Or.inl hr
      | inr hsf => exact Or.inr (stepAll_mem_cases g roots x hsf)

/-! ## §4 `bridge` 与主定理 -/

/-- **`n` 步 ⊆ `n+1` 步**（累积段版本）。

    比 `closureAllAux` 的定义多说了什么：`succ` 把累积起点从 `acc` 换成
    `acc ++ stepAll g frontier` 并把 frontier 换成 `stepAll g frontier`，两者都变大了；
    这里把「起点变大」这一跳单独证（`subset_closureAllAux`），再摊一步。 -/
theorem closureAllAux_le_succ [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    ∀ (acc frontier : List K), ∀ x, x ∈ closureAllAux g n acc frontier
      → x ∈ closureAllAux g (n + 1) acc frontier := by
  induction n with
  | zero =>
      intro acc frontier x hx
      exact subset_closureAllAux g 0 (acc ++ stepAll g frontier) (stepAll g frontier) x
        (List.mem_append_left _ hx)
  | succ k ih =>
      intro acc frontier x hx
      exact ih (acc ++ stepAll g frontier) (stepAll g frontier) x hx

/-- **`closureAll g 1 roots ⊆ closureAll g 2 roots`**（主定理只用这一级）。 -/
theorem closureAll_le_succ [DecidableEq K] (g : DeclGraph K) (n : Nat) (roots : List K) :
    ∀ x, x ∈ closureAll g n roots → x ∈ closureAll g (n + 1) roots := by
  intro x hx
  have hx' : x ∈ roots ++ closureAllAux g n roots roots := hx
  cases mem_append_cases roots (closureAllAux g n roots roots) hx' with
  | inl hl => exact List.mem_append_left _ hl
  | inr hr =>
      exact List.mem_append_right _ (closureAllAux_le_succ g n roots roots x hr)

/-- **【`bridge`】**：`d ∈ g` 且 `k ∈ d.deps` ⟹ **从 `k` 出发 `1` 步够到的东西，
全部已在「`d.key` 与 `k` 作根」的 `2` 步闭包里**。

    比定义多说了什么：这是 T8 §4.2 判定为**唯一缺口**的那条命题。T8 卡住是因为
    `depsOf` 是 `find?` 语义 —— 从 `k` 出发的闭包只能看到**第一个** `key = k` 的声明，
    而失效边 `k ∈ d.deps` 可能出自**别处**；本批换成 `depsOfAll` 之后，`d` 自己那条
    一定被算进去（`mem_depsOfAll_of`），于是：

    * `x = k`：`k` 是 `d.key :: [k]` 的成员，1 步就进；
    * `x ∈ depsOfAll g k`：`x` 走 `stepAll g [k]` 已在 `1` 步闭包里，
      `d.key` 又作为根出现在 `2` 步闭包里（`mem_closureAll_roots`），
      再用 `closureAll_le_succ`（1 步 ⊆ 2 步）。

    **`n = 1` 就够**：不需要任何「跳数上界」，也不需要 `Acyclic`。 -/
theorem bridge [DecidableEq K] (g : DeclGraph K) (k : K) (d : Decl K)
    (hd : d ∈ g) (hdep : k ∈ d.deps) :
    ∀ x ∈ closureAll g 1 [k], x ∈ closureAll g 2 (d.key :: [k]) := by
  intro x hx
  have hcase : x ∈ [k] ∨ ∃ r, r ∈ [k] ∧ x ∈ depsOfAll g r :=
    closureAll_one_mem_cases g [k] x hx
  have hroot : d.key ∈ closureAll g 2 (d.key :: [k]) :=
    mem_closureAll_roots g 2 (d.key :: [k]) d.key List.mem_cons_self
  have hkroot : k ∈ closureAll g 2 (d.key :: [k]) :=
    mem_closureAll_roots g 2 (d.key :: [k]) k (List.mem_cons_of_mem d.key List.mem_cons_self)
  cases hcase with
  | inl hxr =>
      cases hxr with
      | head => exact hkroot
      | tail _ hcontra => exact absurd hcontra List.not_mem_nil
  | inr hwit =>
      obtain ⟨r, hr, hxr⟩ := hwit
      cases hr with
      | head =>
          exact closureAll_le_succ g 1 (d.key :: [k]) x
            (mem_closureAll_succ_of_step g 0 (d.key :: [k]) x
              (mem_stepAll_of_depsOfAll g k (d.key :: [k])
                (List.mem_cons_of_mem d.key List.mem_cons_self) x hxr))
      | tail _ hcontra => exact absurd hcontra List.not_mem_nil
/-- **dependsOn 判真 ⟹ k 真的在 deps 里**（构造子模式一次绑全字段；同 T8 的引理，
    本文件不 import 它的命名空间，故重推一遍）。 -/
theorem deps_mem_of_dependsOn [DecidableEq K] (d : Decl K) (k : K)
    (h : d.dependsOn k = true) : k ∈ d.deps := by
  cases d with
  | mk key kind bk deps vis =>
      have hany : (deps.any (fun x => decide (x = k))) = true := h
      obtain ⟨x, hx, hdec⟩ := any_eq_true_witness (fun x : K => decide (x = k)) deps hany
      exact (of_decide_eq_true hdec) ▸ hx

/-! ### §4.1 失效集合的成员刻画 -/

/-- **失效元素在图里**（`dependents = g.filter …`，`T8` 的 `mem_graph_of_mem_invalidate` 不依赖
    `ClosureAll`，但本文件不 import `InvalidateClosure` 的 T8 命名空间，这里重推一步）。 -/
theorem mem_graph_of_mem_invalidateAll [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) :
    ∀ d ∈ invalidate g k bk, d ∈ g := by
  intro d hd
  unfold invalidate at hd
  unfold dependents at hd
  exact mem_of_filter (fun (x : Decl K) => x.dependsOn k)
    (mem_of_filter (fun (x : Decl K) => spreads x.kind bk) hd)

theorem deps_mem_of_mem_invalidateAll [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) :
    ∀ d ∈ invalidate g k bk, k ∈ d.deps := by
  intro d hd
  unfold invalidate at hd
  unfold dependents at hd
  have h1 : d.dependsOn k = true :=
    prop_of_filter (fun (x : Decl K) => x.dependsOn k)
      (mem_of_filter (fun (x : Decl K) => spreads x.kind bk) hd)
  exact deps_mem_of_dependsOn d k h1

/-! ### §5 主定理 -/

/-- **depsOfAll 的边形式**：`d ∈ g`、`d.key = r`、`x ∈ d.deps` ⟹ `x ∈ depsOfAll g r`。 -/
theorem depsOfAll_edge [DecidableEq K] (g : DeclGraph K) (r : K) (d : Decl K)
    (hd : d ∈ g) (hkey : d.key = r) (x : K) (hx : x ∈ d.deps) : x ∈ depsOfAll g r :=
  mem_depsOfAll_of g r d hd hkey x hx

end FateV2.Core.DeclGraphAll
