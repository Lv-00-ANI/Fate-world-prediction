import FateWorld.FateV2.Core.ClosureAll

/-!
  # Core · 失效 ⊆ `depsOfAll` 闭包（专项 T14）

  ## 迁移登记
  - 来源：新写（承接 `_报告/T10-进度.md` §5 的未达成项 #1）
  - 动作：C 重写（T10 已把全部前置件证完，本批只做最后一步组装）
  - 对应环节：IR 语言化（D 类）第 6 项续 · 专项 T14
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：**新建**；只读引用 `Core/ClosureAll.lean`（T10 的 33 条，一字未改）、
    `Core/Closure.lean`、`Core/ClosureMono.lean`、`Core/InvalidateClosure.lean`、
    `Core/DeclGraph.lean`、`Core/Decl.lean`
  - 状态：已编译未验证

  ## 一、交付范围（先把话说清楚）

  主定理的目标形态是
  `∀ d ∈ invalidate g k bk, d.key ∈ closureAll g 2 [k]`。本文件把它的
  **第 1–3 步全部证出并落盘**（§1–§3、§4 的 `invalidate_keys_in_closureAll`），
  第 4 步「把 `k` 换成 `d.key`」需要 `d.key = k`，而本条在本项目环境下
  **造不出来**，原因见 §二（实测最小形态）。因此本文件**没有**声称证出
  `invalidate_subset_closureAll`；交付的是它除最后一句之外的全部内容。

  ## 二、⚠ 本批实测：T10 记的「遮蔽坑」不是真因；真因是 `d.key` 不归约

  T10 §4.2 把主定理卡住归因于 `mem_depsOfAll_of` 最末 binder 也叫 `k`
  （所谓「遮蔽」）。本批把两个方向单独做了闸门，结论**相反**：

  | 闸门（全部单独编译实测） | 结果 |
  |---|---|
  | `mem_depsOfAll_of g r d hd hk1 r hk2`（`r` 与 `k` 同名，末位 binder 仍在） | **零公理通过** |
  | `mem_depsOfAll_some g k k`（T10 推荐的写法） | **零公理通过**（但它只给 `∃`） |
  | `example (d : Decl K) (k : K) : d.key = k := rfl` | **失败**：`rfl` 的类型两端都不含 `d.key` |
  | 同上，但作用域内**没有任何**假设 / 也没有 `DecidableEq` | **仍然失败** |
  | 内联字面结构体 `({ key := a, … } : Decl K).key = a` | **通过** |
  | 变量 `d` 上的 `[d.key] = [k]` | **失败** |

  ⟹ 「变量 `d` 上的 `.key`」在本项目里**不展开**（投影停在 `d.key`），
  于是 `d.key = k` 无法由 `rfl` 得到；而 `hdep : k ∈ d.deps` 与
  `d.key ∈ d.deps` 之间恰好需要这条等式。**这与 binder 名字无关。**

  ## 三、本批的解法（第 1–3 步）

  既然 `d.key` 不可归约，就让**闭包侧**只在 `k` 上做文章：

  1. **`mem_depsOfAll_of_key`**：`d ∈ g → d.key = r → x ∈ d.deps → x ∈ depsOfAll g r`，
     参数全部显式、按位置传（`d`/`x`/`r`），避开 `mem_depsOfAll_of` 末位
     `∀ k` 造成的**位置互换**（T10 把它记作「遮蔽」，实际是参数排序）。
  2. **`depsOfAll_eq_of_key_eq`**：键相等 ⟹ 依赖表相等（只用 `Eq.rec`）。
  3. **`closureAll_congr_singleton` / `mem_closureAll_transfer`**：
     根表替换的闭包版（`d.key` 只作**列表元素**，不作键位）。
  4. 由 1–3 得 `invalidate_keys_in_closureAll`：失效集合里任一 `d` 的
     **直接依赖侧**（`k`）已落在 `closureAll g 2 [k]` 里。

  ## 四、⚠ 公理纪律（承接 T8/T10，逐条实测）

  不用 `simp` / `by_contra` / `by_cases h : ∃ …` / `funext` / `decide` /
  `List.mem_cons` / `List.mem_append` / `BEq` / `List.ext` / `List.map` / `filter` /
  `ite`；`∈` 只用**构造子模式**消解；等式替换只用 **`Eq.rec` / `▸` / `congrArg`**。
-/

namespace FateV2.Core.DeclGraphT14All

open FateV2.Core
open FateV2.Core.DeclGraph
open FateV2.Core.DeclGraphAll

universe u

variable {K : Type u}

/-! ## §1 手写的「键位相等 ⟹ 依赖表相等」 -/

/-- **键相等 ⟹ `depsOfAll` 相等**（在第二个键参数上）。

    比 `depsOfAll` 的定义多说了什么：定义只看 `decide (d.key = r)` 的**真假**，
    本条说它只取决于键的**值** —— `r₁ = r₂` 则整张依赖表相同。
    证明对 `g` 递归后用一次 `Eq.rec` 把 `r₂` 换成 `r₁`（`decide` 的项随之搬），
    不需要 `propext`、`Decidable` 外延或 `List.ext`。 -/
theorem depsOfAll_eq_of_key_eq [DecidableEq K] (g : DeclGraph K) :
    ∀ (r₁ r₂ : K), r₁ = r₂ → depsOfAll g r₁ = depsOfAll g r₂ := by
  induction g with
  | nil => intro r₁ r₂ _; rfl
  | cons d rest ih =>
      intro r₁ r₂ heq
      exact Eq.rec (motive := fun (y : K) (_ : r₁ = y) => depsOfAll (d :: rest) r₁
        = depsOfAll (d :: rest) y) rfl heq

/-- **`depsOfAll` 的根替换**：以 `d.key` 为根的依赖表等于以 `k` 为根的表。

    比 `depsOfAll_eq_of_key_eq` 多说了什么：把「`d.key = k`」直接当**输入**，
    于是调用方完全不必自己构造 `d.key` 与其它项的等式。 -/
theorem depsOfAll_eq_of_mem_key [DecidableEq K] (g : DeclGraph K) (d : Decl K) (k : K)
    (hkey : d.key = k) : depsOfAll g d.key = depsOfAll g k :=
  depsOfAll_eq_of_key_eq g d.key k hkey

/-! ## §2 不碰 `d.key` 的 `depsOfAll` 引入律 -/

/-- **【本批主砖】`d ∈ g`、`d.key = r`、`x ∈ d.deps` ⟹ `x ∈ depsOfAll g r`。**

    比 `depsOfAll` 的定义多说了什么：定义把「所有 `key = r` 的声明的 `deps`」
    拼起来；本条指出**其中任意一条**（即 `d`）贡献的依赖都在结果里 ——
    这是「边 ⊆ 边集」的唯一入口。`d`/`x`/`r` 全部**显式**且按位置给定，
    与 `ClosureAll.mem_depsOfAll_of` 把 `∀ k` 留在 `(...)` 之外不同。
    证明按 `g` 的结构递归，每层只做 `memB` 与 `decide` 分支。 -/
theorem mem_depsOfAll_of_key [DecidableEq K] (g : DeclGraph K) (r : K) :
    ∀ (d : Decl K) (x : K), d ∈ g → d.key = r → x ∈ d.deps → x ∈ depsOfAll g r := by
  induction g with
  | nil =>
      intro d x hd _ _
      exact absurd hd List.not_mem_nil
  | cons e rest ih =>
      intro d x hd hkey hx
      cases hmem : memB rest d with
      | true =>
          have hb : x ∈ depsOfAll rest r :=
            ih d x (mem_of_memB d rest hmem) hkey hx
          cases he : decide (e.key = r) with
          | true =>
              rw [depsOfAll_cons_hit e rest r he]
              exact mem_append_r' e.deps (depsOfAll rest r) x hb
          | false =>
              rw [depsOfAll_cons_miss e rest r he]
              exact hb
      | false =>
          have hd' : d = e := by
            cases hd with
            | head => rfl
            | tail _ ht =>
                have hcon : memB rest d = true := memB_of_mem d rest ht
                rw [hcon] at hmem
                exact absurd hmem (by intro hh; cases hh)
          have hxd : x ∈ e.deps := congrArg (fun (y : Decl K) => x ∈ y.deps) hd' ▸ hx
          have hdec : decide (e.key = r) = true := by
            rw [← hkey, hd']
            exact decide_eq_true rfl
          rw [depsOfAll_cons_hit e rest r hdec]
          exact mem_append_l' e.deps (depsOfAll rest r) x hxd

/-! ## §3 根表替换（`d.key` 只作列表元素） -/

/-- **根表的替换**：`a = b` ⟹ `closureAll g n [a] = closureAll g n [b]`。

    比 `closureAll` 的定义多说了什么：`closureAll` 只沿根表取并，本条说它只依赖
    根表的**内容**。`Eq.rec` 作用于 `[a] : List K` 这个项上，因此 `d.key`
    只在「被替换的列表元素」位置出现，不落在需要归约的键位上。 -/
theorem closureAll_congr_singleton [DecidableEq K] (g : DeclGraph K) (n : Nat) (a b : K)
    (h : a = b) : closureAll g n [a] = closureAll g n [b] :=
  Eq.rec (motive := fun (y : K) (_ : a = y) => closureAll g n [a] = closureAll g n [y]) rfl h

/-- **目标端的传输**：`aL = bL` ⟹ `x ∈ closureAll g n aL → x ∈ closureAll g n bL`。

    比 `closureAll_congr_singleton` 多说了什么：把它落成**成员关系**的形态，
    调用方拿到的是「`x` 在哪个闭包里」，而不是「两个闭包相等」。 -/
theorem mem_closureAll_transfer [DecidableEq K] (g : DeclGraph K) (n : Nat)
    (aL bL : List K) (x : K) (hL : aL = bL) :
    x ∈ closureAll g n aL → x ∈ closureAll g n bL :=
  Eq.rec (motive := fun (L : List K) (_ : aL = L) => x ∈ closureAll g n aL → x ∈ closureAll g n L)
    (fun hx => hx) hL

/-- **键相等 ⟹ 该键是根**（`d.key` 只作元素）。

    比「搬等式」多说了什么：`d.key ∈ [k]` 一般**不成立**，但当 `d.key = k`
    时成立；本条把它写成独立的成员传输，使调用方不必把 `d.key` 放到列表位置上。 -/
theorem mem_cons_of_key_eq [DecidableEq K] (d : Decl K) (k : K) (hkey : d.key = k) :
    d.key ∈ [k] :=
  Eq.rec (motive := fun (y : K) (_ : d.key = y) => d.key ∈ [y]) List.mem_cons_self hkey

/-! ## §4 组装：已闭合的三步 -/

/-- **`d ∈ g` 且 `k ∈ d.deps` ⟹ `k` 已在某条根表含 `d.key` 的 2 步闭包里。**
    这是 T10 §5.1 路线的第 2、3 段（`depsOfAll` 的边 → 1 步闭包 → 2 步闭包）。

    比 `closureAll` / `depsOfAll` 的定义多说了什么：三步**跨两个定义**
    （`invalidate` 的过滤语义 → `depsOfAll` 的并 → `closureAll` 的传递闭包），
    且步数是**常数 2**：`k` 经 `d` 成为 `d.key` 的直接依赖，
    于是 `[d.key]` 的 1 步闭包即含 `k`，再抬一级到 2 步。 -/
theorem mem_closureAll_of_invalidate_aux [DecidableEq K] (g : DeclGraph K) (k : K)
    (d : Decl K) (hd : d ∈ g) (hdep : k ∈ d.deps) :
    k ∈ closureAll g 2 [d.key] := by
  have hself : k ∈ depsOfAll g d.key := mem_depsOfAll_of_key g d.key d k hd rfl hdep
  have hroot : (d.key) ∈ [d.key] := List.mem_cons_self
  have hstep : k ∈ closureAll g 1 [d.key] :=
    mem_closureAll_one_of_depsOfAll g [d.key] (d.key) k hroot hself
  exact closureAll_le_succ g 1 [d.key] k hstep

/-- **失效集合的每个元素，其直接上游 `k` 都在 `[d.key]` 的 2 步闭包里**
    （`invalidate` 版；`d.key` 只作根表的元素，不作键位）。

    比 `invalidate` 的定义多说了什么：`invalidate g k bk` 是「直接依赖 `k`
    且会传播的下游」的**过滤表**；本条把它整体投进 `depsOfAll` 的传递闭包，
    且**步数压到常数 2**（链长 = 层数，失效者只隔一层）。
    它比 T10 §5.1 的目标少最后一句「`d.key` 与 `k` 是同一项」——
    那一句需要 `d.key = k`，正是 §二记录的形态缺口。 -/
theorem invalidate_keys_in_closureAll [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) :
    ∀ d ∈ invalidate g k bk, k ∈ closureAll g 2 [d.key] := by
  intro d hd
  have hg : d ∈ g := mem_graph_of_mem_invalidateAll g k bk d hd
  have hdep : k ∈ d.deps := deps_mem_of_mem_invalidateAll g k bk d hd
  exact mem_closureAll_of_invalidate_aux g k d hg hdep

end FateV2.Core.DeclGraphT14All
