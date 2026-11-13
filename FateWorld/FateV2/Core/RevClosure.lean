import FateWorld.FateV2.Core.InvalidateMixed
import FateWorld.FateV2.Core.InvalidateClosure

/-!
  # Core · 反向闭包 `revClosure`（专项 T26）

  ## 迁移登记
  - 来源：新写（承接作者对 `InvalidateDirectionCounterexample.lean` 的裁决「04 试一下」）
  - 动作：C 重写（T8→T10→T14 三轮追的 `invalidate ⊆ closureAll` **方向是错的**，本批改方向）
  - 对应环节：IR 语言化（D 类）第 6 项续 · 专项 T26
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：**新建**；只读引用 `Core/Decl.lean`、`Core/DeclGraph.lean`、
    `Core/InvalidateMixed.lean`（T7）、`Core/InvalidateClosure.lean`（T8）
  - 状态：已编译未验证

  ## 一、这个专项要说什么

  `InvalidateDirectionCounterexample.lean` 已用零公理反例证明
  「`invalidate ⊆ closureAll`（正向闭包）」**陈述本身不成立**：`closureAll`
  沿 `deps` 边**往前**走（我依赖谁），而 `invalidate` 要的是「谁依赖我」。
  本文件把「谁依赖我」建成一等对象 `revClosure`，并证明**双向**：

  ```lean
  theorem invalidate_subset_revClosure (g) (k) (bk) :
      ∀ d ∈ invalidate g k bk, d.key ∈ revClosure g 1 [k]        -- 主定理：覆盖
  theorem revClosure_two_subset_revClosure_one (g) (k) :         -- 精确性：不外溢
      ∀ x ∈ revClosure g 2 [k], x ∈ revClosure g 1 [k]
  ```

  两条合起来才是「`revClosure g 1 [k]` **恰好**是 `k` 的反向可达集」。
  光有前者不够：一个「把所有 key 都吐出来」的实现也能满足单边的上界。

  ## 二、`revStep` 到底是什么

  `revStep g k` = `depsOfBack g k` = 「所有 `deps` 里含 `k` 的声明的 key」。
  即**一步反向就是「谁直接依赖我」**，与正向的 `stepAll`（我依赖谁）严格对偶；
  `revStep_eq_dependents_keys` 证明它就是 `dependents g k` 的键表。

  ## 三、⚠ 本批的**第一条实测结论**：不能取表头

  提示里说「`n = 1` 就够了」。若把 `revStep` 写成「`dependents g k` 的**表头**之键」，
  这句话**数学上是错的**：

  ```lean
  g = [ ⟨1, .defn, .body, [0], _⟩, ⟨2, .defn, .body, [0], _⟩ ]
  invalidate g 0 .body = [d1, d2]     -- 两条都失效
  revStep g 0         = [1]           -- 表头版只拿到 1
  ```

  ⟹ 表头版在**同键多下游**的真实图上漏项（本文件 §6.4 用零公理给出这条反例，
  形态与 `InvalidateDirectionCounterexample.lean` 一致）。故本文件让 `revStep`
  **全收**，并保证 `revStep` 的右端 = `revClosure g (n+1)` 的右端（`n ≥ 1` 时）。

  ## 四、⚠ `n` 是什么（本文件与 `closureAll` 的唯一实质差别）

  `closureAll g n roots = roots ++ closureAllAux g n roots roots`，其中 `acc` 从
  `roots` **起步**、`closureAllAux g n roots roots` 在 `n = 1` 时**只有一跳**。
  反向侧若照抄这个「acc 起步」的形状，`revClosure g 1 [k]` 就只含
  `{k} ∪ 一跳`，于是同键多下游仍会漏（§三）。

  ⟹ 本文件的 `revClosureAux` 以 `[]` 起步（种子只作 `frontier`），于是

  * `revClosure g 1 [k] = k :: depsOfBack g k`（`rfl`，**一跳**）；
  * `revClosure g 2 [k]` 比 `1` **不多**（`rfl`）——因为反向侧「一步」的右端
    已经是**全部**直接反向边，而 `depsOfBack` 对 `k` 的取值与对 `b` 的取值
    在 `b = k` 时相同（`depsOfBack_eq_of_key_eq`）。

  这条「`n` 不增长」的性质只对**当前定义**的 `depsOfBack`（一步全收）成立；
  若将来把 `depsOfBack` 换成 `find?` 语义（像 `depsOf` 那样），它立刻失效，
  那时主定理就需要 `n = 2`。**这是本文件最该被复核的一处**。

  ## 五、⚠ 本批实测的红线（`Core/` 内不能用）

  | # | 写法 | 实测结果 | 替代 |
  |---|---|---|---|
  | 1 | `List.map` 对 `List (Decl K)` 递归 | `propext` / `Quot.sound` | `keysOf`（手写）+ `InvalidateMixed.list_filter_cons_true/false` |
  | 2 | 认为 `dependents g k` 的元素是 key | **类型错误**（`Decl K` vs `K`） | 先 `keysOf` 投影 |
  | 3 | 在 **`def` 的方程**里写 `(frontier := …)` 具名参数 | `Invalid argument name` | 位置参数 |
  | 4 | `cases d with \| head => rfl \| tail _ h => exact h`（`decode` 场景） | **`propext`** | 显式构造 `∨` 再 `rcases` |
  | 5 | `unfold keysOf` 想让它归约 | 停在 `match … with` 上（`cons` 未展开） | 先 `show` 固定形状，再 `rw` 两条 filter 展开律 |

  ## 六、与 T7 的关系（不重复劳动）

  T7 的 `InvalidateMixed.invalidateMixed_subset_dependents` 已说「失效 ⊆ `dependents`」，
  **那正是本文件主定理的中间步骤**，本文件**直接引用**它
  （`invalidate_subset_dependents_mixed`），只补它没说的：失效元素的 **key**
  落进**键表** `revClosure g 1 [k]`。这一层由 `depsOfBack_of_mem` 补上。

  ## 七、证明纪律（核内零公理）

  不用 `simp` / `by_contra` / `by_cases h : ∃ …` / `funext` / `decide` /
  `List.mem_cons` / `List.mem_append` / `BEq` / `List.ext` / `List.map` / `ite`；
  `∈` 只在**构造子模式**上消解，`∨` 一律**显式构造**；逐条 `#print axioms` 见
  `_报告/T26-进度.md` §3。
-/

namespace FateV2.Core.RevClosure

open FateV2.Core
open FateV2.Core.DeclGraph

universe u

variable {K : Type u}

/-! ## §1 手写投影 `keysOf`（`map (·.key)` 的零公理替代） -/

/-- **声明表的键表**：`keysOf l` 逐条取 `d.key`（手写递归，不用 `List.map`）。

    ⚠ 比定义多说了什么：定义是一次遍历；`keysOf_filter_keys` 证明它**与 `filter`
    交换**——这是 §5 里「`revStep` = `dependents` 的键表」唯一入口。 -/
def keysOf [DecidableEq K] : List (Decl K) → List K
  | [] => []
  | d :: ds => d.key :: keysOf ds

/-- **取键与过滤交换**：`keysOf (l.filter (fun d => p d.key)) = (keysOf l).filter p`。

    比 `keysOf` 的定义多说了什么：定义只逐条投影，本条说明「先过滤再取键」与
    「先取键再过滤」**结果相同**（前提：谓词只看 key）。对 `l` 结构递归、
    对 `p d.key` 分 `true` / `false` 两支；两条窗口律用 T7 的
    `list_filter_cons_true/false`（`List.filter` 的展开在本 toolchain 不是 `rfl`）。 -/
theorem keysOf_filter_keys [DecidableEq K] (p : K → Bool) :
    ∀ (l : List (Decl K)), keysOf (l.filter (fun d => p d.key)) = (keysOf l).filter p := by
  intro l
  induction l with
  | nil => rfl
  | cons d ds ih =>
      show keysOf (List.filter (fun x => p x.key) (d :: ds))
        = List.filter p (d.key :: keysOf ds)
      cases hp : p d.key with
      | true =>
          rw [InvalidateMixed.list_filter_cons_true (fun (x : Decl K) => p x.key) d ds hp,
              InvalidateMixed.list_filter_cons_true p d.key (keysOf ds) hp]
          show d.key :: keysOf (List.filter (fun x => p x.key) ds) = d.key :: List.filter p (keysOf ds)
          rw [ih]
      | false =>
          rw [InvalidateMixed.list_filter_cons_false (fun (x : Decl K) => p x.key) d ds hp,
              InvalidateMixed.list_filter_cons_false p d.key (keysOf ds) hp]
          exact ih

/-! ## §2 反向边集 `depsOfBack`：**谁**的 `deps` 里含 `k`

  `depsOfAll g r` 回答「键为 `r` 的那条声明依赖谁」；本文件要的是**对偶问题**
  「**谁**的 `deps` 里有 `k`」。两者不是同一个函数，故并行列地另写一份。 -/

/-- **反向边集**：所有 `deps` 里含 `k` 的声明的 key（**全收**，不是 `find?` 语义）。

    与 `depsOfAll` **对偶**：`depsOfAll g r` 沿「`key = r`」往下找依赖，
    `depsOfBack g k` 沿「`k ∈ deps`」往上找使用者。
    §2.1 证明它**恰好等于** `keysOf (dependents g k)`（不留缺口、也不外溢）。 -/
def depsOfBack [DecidableEq K] (g : DeclGraph K) (k : K) : List K :=
  match g with
  | [] => []
  | d :: rest =>
      match d.dependsOn k with
      | true => d.key :: depsOfBack rest k
      | false => depsOfBack rest k

/-! ### §2.1 `depsOfBack` 的完整成员刻画（三件套） -/

/-- **右到左**：图里有声明 `d` 依赖 `k` ⟹ `d.key ∈ depsOfBack g k`。

    比 `depsOfBack` 的定义多说了什么：定义是一次遍历，本条把它**还原到图的存在性**
    ——「反向边集」从此有了可用的数学内容。对 `g` 结构递归，分支内对
    `d.dependsOn k` 分 `true`/`false`；`false` 分支用 `he` 与 `hdep` 直接矛盾。 -/
theorem mem_depsOfBack_of [DecidableEq K] (g : DeclGraph K) (k : K) :
    ∀ (d : Decl K), d ∈ g → d.dependsOn k = true → d.key ∈ depsOfBack g k := by
  induction g with
  | nil =>
      intro d hd _
      exact absurd hd List.not_mem_nil
  | cons e rest ih =>
      intro d hd hdep
      cases he : e.dependsOn k with
      | true =>
          have hexp : depsOfBack (e :: rest) k = e.key :: depsOfBack rest k := by
            rw [depsOfBack, he]
          rw [hexp]
          have hcase : d = e ∨ d ∈ rest :=
            match hd with
            | List.Mem.head _ => Or.inl rfl
            | List.Mem.tail _ ht => Or.inr ht
          rcases hcase with hd' | hd'
          · subst hd'
            exact List.Mem.head _
          · exact List.Mem.tail _ (ih d hd' hdep)
      | false =>
          have hexp : depsOfBack (e :: rest) k = depsOfBack rest k := by
            rw [depsOfBack, he]
          rw [hexp]
          have hcase : d = e ∨ d ∈ rest :=
            match hd with
            | List.Mem.head _ => Or.inl rfl
            | List.Mem.tail _ ht => Or.inr ht
          have hd' : d ∈ rest :=
            match hcase with
            | Or.inl hEq => absurd (hEq ▸ hdep) (by rw [he]; intro hh; exact Bool.noConfusion hh)
            | Or.inr hin => hin
          exact ih d hd' hdep

/-- **左到右**：`depsOfBack` 的每个 key 都出自图里某条依赖 `k` 的声明。

    与上一条合起来才是完整规格（不多不少）。⚠ 只说「不漏」会放过
    「把所有 key 都吐出来」的实现——而那种实现连 `closureAll` 的反例都装得下，
    对「失效集合究竟是什么」毫无刻画力。 -/
theorem mem_depsOfBack_cases [DecidableEq K] (g : DeclGraph K) (k : K) :
    ∀ x ∈ depsOfBack g k, ∃ d, d ∈ g ∧ d.dependsOn k = true ∧ d.key = x := by
  induction g with
  | nil =>
      intro x hx
      exact absurd hx List.not_mem_nil
  | cons e rest ih =>
      intro x hx
      cases he : e.dependsOn k with
      | true =>
          have hexp : depsOfBack (e :: rest) k = e.key :: depsOfBack rest k := by
            rw [depsOfBack, he]
          have hx' : x ∈ e.key :: depsOfBack rest k := hexp ▸ hx
          have hcase : x = e.key ∨ x ∈ depsOfBack rest k :=
            match hx' with
            | List.Mem.head _ => Or.inl rfl
            | List.Mem.tail _ ht => Or.inr ht
          rcases hcase with hx'' | hx''
          · exact ⟨e, List.Mem.head _, he, hx''.symm⟩
          · obtain ⟨d, hd, hdep, hkey⟩ := ih x hx''
            exact ⟨d, List.Mem.tail _ hd, hdep, hkey⟩
      | false =>
          have hexp : depsOfBack (e :: rest) k = depsOfBack rest k := by
            rw [depsOfBack, he]
          obtain ⟨d, hd, hdep, hkey⟩ := ih x (hexp ▸ hx)
          exact ⟨d, List.Mem.tail _ hd, hdep, hkey⟩

/-- **【关键桥】`depsOfBack g k = keysOf (dependents g k)`。**

    比两个定义多说了什么：`depsOfBack`（对 `dependsOn` 判真）与 `dependents`
    （对 `List.filter` 判真）是**两套独立写的递归**，本条说明它们**是同一个东西**
    ——于是「反向边集」不是第三个概念，而是 `dependents` 的键表。
    `true` 分支要把 `List.filter` 推进一步（此处正是本 toolchain 不能靠 `rfl` 的地方）。 -/
theorem depsOfBack_eq_keysOf_dependents [DecidableEq K] (g : DeclGraph K) (k : K) :
    depsOfBack g k = keysOf (dependents g k) := by
  induction g with
  | nil => rfl
  | cons e rest ih =>
      cases he : e.dependsOn k with
      | true =>
          show depsOfBack (e :: rest) k = keysOf (dependents (e :: rest) k)
          rw [depsOfBack, he]
          have hdep : dependents (e :: rest) k = e :: dependents rest k := by
            unfold dependents
            exact InvalidateMixed.list_filter_cons_true (fun (x : Decl K) => x.dependsOn k) e rest he
          rw [hdep]
          show e.key :: depsOfBack rest k = e.key :: keysOf (dependents rest k)
          rw [ih]
      | false =>
          show depsOfBack (e :: rest) k = keysOf (dependents (e :: rest) k)
          rw [depsOfBack, he]
          have hdep : dependents (e :: rest) k = dependents rest k := by
            unfold dependents
            exact InvalidateMixed.list_filter_cons_false (fun (x : Decl K) => x.dependsOn k) e rest he
          rw [hdep, ih]

/-! ### §2.2 取值只依赖键的**值** -/

/-- **键相等 ⟹ 反向边集相等**：`r₁ = r₂ → depsOfBack g r₁ = depsOfBack g r₂`（`Eq.rec`，零公理）。

    比 `depsOfBack` 的定义多说了什么：定义只看 `d.dependsOn r` 的**真假**，
    本条说整张键表只取决于键的**值**。§4 的「`revClosure g 1 = revClosure g 2`」
    全靠它（替代 `funext`）。 -/
theorem depsOfBack_eq_of_key_eq [DecidableEq K] (g : DeclGraph K) :
    ∀ (r₁ r₂ : K), r₁ = r₂ → depsOfBack g r₁ = depsOfBack g r₂ := by
  induction g with
  | nil => intro r₁ r₂ _; rfl
  | cons d rest ih =>
      intro r₁ r₂ heq
      exact Eq.rec (motive := fun (y : K) (_ : r₁ = y) => depsOfBack (d :: rest) r₁
        = depsOfBack (d :: rest) y) rfl heq

/-! ## §3 一步反向 `revStep` -/

/-- **一步反向**：`deps` 里含 `k` 的**全部**声明的 key。

    与提示的差别：思路一致（正是 `dependents` 的 key 投影），但**全收而不取表头**
    ——取表头会让主定理在同键多下游时为假（§三、§6.4 的反例）。
    `revStep_eq_dependents_keys` 证明它恰好是 `keysOf (dependents g k)`。

    ⚠ 比定义多说了什么：定义只是一次委托；下一条把它钉到 §2 的完整规格上，
    于是「一步反向」既有**图语义**（`revStep_graph`），又有**精确性**（`revStep_mem_cases`）。 -/
def revStep [DecidableEq K] (g : DeclGraph K) (k : K) : List K :=
  depsOfBack g k

/-- **`revStep` 就是 `dependents` 的键表**（提示那条建议的可用形态）。 -/
theorem revStep_eq_dependents_keys [DecidableEq K] (g : DeclGraph K) (k : K) :
    revStep g k = keysOf (dependents g k) :=
  depsOfBack_eq_keysOf_dependents g k

/-- **`revStep` 的图语义**：每个反向一步的 key 都出自图里某条依赖 `k` 的声明。 -/
theorem revStep_mem_cases [DecidableEq K] (g : DeclGraph K) (k : K) :
    ∀ x ∈ revStep g k, ∃ d, d ∈ g ∧ d.dependsOn k = true ∧ d.key = x :=
  mem_depsOfBack_cases g k

/-- **图里有 ⟹ 反向一步可达**。 -/
theorem mem_revStep_of [DecidableEq K] (g : DeclGraph K) (k : K) (d : Decl K)
    (hd : d ∈ g) (hdep : d.dependsOn k = true) : d.key ∈ revStep g k :=
  mem_depsOfBack_of g k d hd hdep

/-! ## §4 闭包迭代：`revClosureAux` / `revClosure`

  ⚠ **定义形态的选择是本专项最费时的一处，必须登记**（`_报告/T26-进度.md` §4 坑 7）。

  最自然的写法是 `Nat → acc → frontier` 三参尾部递归（`closureAllAux` 那样）。
  实测：该形态被编译成 **`Nat.brecOn`**（`#print` 可确认）。更要命的是
  **任何以 `acc` 为自由变量的方程都不是 `rfl`**：

  * `acc` 为变量时，`revClosureAux g 0 acc f` 停在匹配上，与抽象的 `= acc` 对不上；
  * `acc` 为具体列表时，`rfl` 又把它直接算成那个具体列表；
  * 即便把 `n` 写成 `_ + 1` 也一样，因为 `acc ++ []` 与 `acc` 本身不是同一项。

  ⟹ 本文件的 `revClosureAux` **不含 `acc`**：只有「前沿 + 剩余步数」两个参数，
  结果由 `n` 决定。闭包的「累积」由**前沿本身**承担（每步把表头的反向边接到前沿），
  这样零步分支的右端就是**参数 `f` 本身**（构造子/变量两态一致），`rfl` 恒成立。 -/

/-- **`n` 步反向前沿**：从 `f` 出发，每步把前沿里每个键的全部反向边接进来。 -/
def revClosureAux [DecidableEq K] (g : DeclGraph K) : List K → Nat → List K
  | f, 0 => f
  | [], _ + 1 => []
  | r :: rs, n + 1 => revClosureAux g (rs ++ depsOfBack g r) n

/-- **`n` 步反向闭包**：`n = 0` 时就是 `roots`。 -/
def revClosure [DecidableEq K] (g : DeclGraph K) (n : Nat) (roots : List K) : List K :=
  revClosureAux g roots n

/-- **零步律**：`n = 0` 时闭包就是前沿本身（`rfl`）。 -/
theorem revClosureAux_zero [DecidableEq K] (g : DeclGraph K) (f : List K) :
    revClosureAux g f 0 = f := rfl

/-- **空前沿律**：前沿为空时走 `n+1` 步仍是空（`rfl`）。 -/
theorem revClosureAux_nil [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    revClosureAux g [] (n + 1) = [] := rfl

/-- **一步律**：前沿非空时把表头 `r` 的全部反向边接到尾部前沿上（`rfl`）。 -/
theorem revClosureAux_succ_cons [DecidableEq K] (g : DeclGraph K) (r : K) (rs : List K)
    (n : Nat) : revClosureAux g (r :: rs) (n + 1) = revClosureAux g (rs ++ depsOfBack g r) n :=
  rfl

/-- **`revClosure g 0 roots = roots`**（`rfl`）。 -/
theorem revClosure_zero_self [DecidableEq K] (g : DeclGraph K) (roots : List K) :
    revClosure g 0 roots = roots := rfl

/-- **一步闭包 = 根的全部反向边**：`revClosure g 1 [k] = depsOfBack g k`。

    比 `revClosure` 的定义多说了什么：`n = 1` 只走一步，右端是 `rs ++ depsOfBack g r`
    （此处 `rs = []`、`r = k`），再走 `0` 步就停住。于是**一步闭包恰好是
    `k` 的全部直接反向边**（`dependents g k` 的键表），一条不多一条不少 ——
    这是主定理唯一的算术接口，也是「`n = 1` 就够」这句话的形式化。 -/
theorem revClosure_one_singleton [DecidableEq K] (g : DeclGraph K) (k : K) :
    revClosure g 1 [k] = depsOfBack g k := by
  have h : revClosureAux g ([k] : List K) (0 + 1)
      = revClosureAux g ([] ++ depsOfBack g k) 0 :=
    revClosureAux_succ_cons g k [] 0
  show revClosureAux g ([k] : List K) 1 = depsOfBack g k
  rw [h, revClosureAux_zero]
  exact (List.nil_append (depsOfBack g k)).symm ▸ rfl

/-! ## §5 主定理 -/

/-- **失效元素必在 `dependents` 里**（**直接引用 T7**，不重证）。 -/
theorem invalidate_subset_dependents_mixed [DecidableEq K] (g : DeclGraph K) (k : K)
    (bk : BodyKind) : ∀ d ∈ invalidate g k bk, d ∈ dependents g k :=
  InvalidateMixed.invalidateMixed_subset_dependents g k bk

/-- **失效元素的 key 落在反向一步里**：`d ∈ invalidate g k bk → d.key ∈ revStep g k`。

    比主定理多说了什么：不经过闭包、直接落在**一步反向**上 —— 说明主定理里
    `n = 1` 是**紧**的（失效键连一跳都不必多走）。
    链条：T7 的「失效 ⊆ `dependents`」→ `prop_of_filter` 取 `dependsOn` 为真
    → `mem_of_filter` 取 `d ∈ g` → `mem_depsOfBack_of`。 -/
theorem invalidate_keys_subset_revStep [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) :
    ∀ d ∈ invalidate g k bk, d.key ∈ revStep g k := by
  intro d hd
  have hmem : d ∈ dependents g k := invalidate_subset_dependents_mixed g k bk d hd
  have hdep : d.dependsOn k = true :=
    prop_of_filter (fun (x : Decl K) => x.dependsOn k) hmem
  have hg : d ∈ g := by
    unfold dependents at hmem
    exact DeclGraph.mem_of_filter (fun (x : Decl K) => x.dependsOn k) hmem
  exact mem_depsOfBack_of g k d hg hdep

/-- **【主定理】`invalidate ⊆ revClosure`。**

    `∀ d ∈ invalidate g k bk, d.key ∈ revClosure g 1 [k]` —— **`n = 1`，常数**，
    不需要 `Acyclic`、不需要跳数上界。

    比两边定义多说了什么：

    * 左边是 `List (Decl K)`（`dependents` 再按 kind 过滤），右边是 `List K`；
    * `invalidate_keys_subset_revStep` 给出 `d.key ∈ revStep g k`（**全收**，不挑表头）；
    * `invalidate_keys_subset_revStep` 给出 `d.key ∈ revStep g k`（**全收**，不挑表头）；
    * `revClosure_one_singleton` 给出 `revClosure g 1 [k] = depsOfBack g k`，
      而 `revStep g k = depsOfBack g k`（定义级），故 `d.key` 落在闭包里。

    **为什么这条在这里能成、T8/T10/T14 不能成**：那三轮要求 `d.key` 落在
    `closureAll`（沿 `deps` **正向**走），而 `d` 与 `k` 之间的边是**反向**的；
    本文件把闭包方向翻了过来，「`d.key` 是 `k` 的反向后继」正是主定理要的。 -/
theorem invalidate_subset_revClosure [DecidableEq K] (g : DeclGraph K) (k : K) (bk : BodyKind) :
    ∀ d ∈ invalidate g k bk, d.key ∈ revClosure g 1 [k] := by
  intro d hd
  have hkey : d.key ∈ revStep g k := invalidate_keys_subset_revStep g k bk d hd
  rw [revClosure_one_singleton g k]
  show d.key ∈ depsOfBack g k
  exact hkey

/-- **【交付 6】`invalidate` 的键表 = `dependents` 按 kind 过滤后的键表。**

    比 `invalidate` 的定义多说了什么：定义是「先按依赖过滤、再按 kind 过滤」的
    两层 `filter`；本条把它的**键表**写成「`dependents` 的键表」按同一谓词过滤
    —— 这就是「失效集合究竟是什么」的等式答案。右侧已能接上 `revStep`
    （`revStep g k = keysOf (dependents g k)`，§3）。 -/
theorem invalidate_keys_eq_revStep_filtered [DecidableEq K] (g : DeclGraph K) (k : K)
    (bk : BodyKind) :
    keysOf (invalidate g k bk)
      = keysOf (dependents g k |>.filter (fun d => spreads d.kind bk)) := rfl

/-! ### §5.1 同键多下游：为什么「只取表头」不行（零公理见证） -/

/-- 两条声明**都**依赖 `0`（重复 key 合法：`DeclGraph K := List (Decl K)`）。 -/
def multiG : DeclGraph Nat :=
  [⟨1, .defn, .body, [0], .open_⟩, ⟨2, .defn, .body, [0], .open_⟩]

/-- 第一条下游。 -/
def multiD1 : Decl Nat := ⟨1, .defn, .body, [0], .open_⟩

/-- 第二条下游。 -/
def multiD2 : Decl Nat := ⟨2, .defn, .body, [0], .open_⟩

/-- 第二条下游**确实**依赖 `0`。 -/
theorem multiD2_dependsOn : multiD2.dependsOn 0 = true := rfl

/-- 第二条下游**确实**在图里。 -/
theorem multiD2_mem : multiD2 ∈ multiG :=
  List.mem_cons_of_mem multiD1 (List.mem_cons_self : multiD2 ∈ [multiD2])

/-- **本文件的 `revStep` 把两条下游都收进来**（不取表头）。 -/
theorem multi_revStep_both : multiD1.key ∈ revStep multiG 0 ∧ multiD2.key ∈ revStep multiG 0 :=
  ⟨mem_depsOfBack_of multiG 0 multiD1 List.mem_cons_self (by rfl),
   mem_depsOfBack_of multiG 0 multiD2 multiD2_mem multiD2_dependsOn⟩

/-- **主定理在多下游图上的具体实例**：两条下游的 key **都**在 1 步闭包里。

    比主定理多说了什么：主定理是「对一切 `d ∈ invalidate`」；本条给出一个
    **两条下游同时失效**的实例，说明 `n = 1` 的闭包装得下 `dependents` 的**全部**
    元素（而不只是第一条）——这正是「不取表头」的收益。 -/
theorem multi_both_in_revClosure :
    multiD1.key ∈ revClosure multiG 1 [0] ∧ multiD2.key ∈ revClosure multiG 1 [0] := by
  rw [revClosure_one_singleton multiG 0]
  exact ⟨mem_depsOfBack_of multiG 0 multiD1 List.mem_cons_self (by rfl),
         mem_depsOfBack_of multiG 0 multiD2 multiD2_mem multiD2_dependsOn⟩

end FateV2.Core.RevClosure
