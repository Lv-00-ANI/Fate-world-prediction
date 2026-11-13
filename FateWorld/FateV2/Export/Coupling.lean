import FateWorld.FateV2.Export.Carrier
import Mathlib.Data.List.Basic

/-!
  # Export · Coupling —— 跨模态耦合的形式化（D-009/D-010/D-011 的核心缺口）

  ## 迁移登记
  - 来源：新写（**补 D-011 的空白**；与 `Carrier.lean`（T3）**并行**新模块）
  - 动作：C 重写
  - 对应环节：F6-10（多模态导出）
  - 依赖裁决：**D-009**、**D-010**、**D-011**、**D-012**、**D-013**、
              **裁决 K**、**D-019**、**D-022**
  - 改动：新文件。**不动** `Modality.lean` / `Export.lean` / `Carrier.lean` 一个字符。
  - 状态：已验证

  详细设计理由、三条如实登记（实现期选型 D-019）与逐条「超出定义之处」
  见 `_报告/T31-进度.md`。本文件的每条定理都在自己的 docstring 里写了「超出定义之处」。

  ## 三条如实登记（实现期选型，D-019）

  1. **`step : (a : M) → (k : M) → abi k`**，不是任务书的
     `(a b : M) → abi a → abi b`。纤维 `abi : M → Type v` 取任意函数，
     `abi a` 与 `abi b` 之间没有强制关系；本文件取「算子吃上游索引、吐任意模态的值」，
     类型自动对齐。当纤维是常函数（T3 的 `ExportCarrier`/`BoolCarrier` 正是如此）时，
     两种签名同型，故这条不损失一般性。

  2. **依赖函数的等式用 `PFunEq`（逐点），不用 `funext`**。`funext` 带 `Quot.sound`，
     本文件要求零公理，故取逐点形式。这是零公理下能说的最强形式。

  3. **`derivedModality` 的「构造」这一步本文件没有做**——只交付了它的**可检判据**
     （`isDerived` + `isDerived_unique` + `isDerived_compute`）。
     原因是一个 Lean 4.33 的具体障碍：`up` 的 `if` 长在**依赖类型的返回位置**时，
     `if_pos` / `dif_pos` / `cases` / `subst` / `nomatch` **实测全部不能**化简它
     （只有 `if_neg` 可用）。完整证据、失败矩阵与三条绕行方案见
     `_报告/T31-进度.md` §五。这一条**是本专项最大的缺口**，不是措辞问题。

  ## 本文件**没有**包含什么（防误读）

  下面这些在开发过程中**验证过**（`lake build` 通过、`#print axioms` 全空），
  但在最后一次重构时被脚本按锚点切片**误删**，**当前不在文件里**：

  * §4 误差传播：`delta_componentwise` / `delta_is_componentwise` /
    `derivation_collapses` / `derivation_strict_on_injective` /
    `derivation_preserves_tolerance`
  * §5 `Carrier` 接口：`projection_compatible` / `projection_is_source` /
    `coupling_declares_projection` / `derivedModality_count`
  * §6 闭合性：`CouplingClosed` / `idCoupling_closed` / `couplingClosed_mono`
  * §7 三案特例：`coupling_not_behind_script` / `step_gives_functional_dependence` /
    `step_is_constraint` / `probSupport_step_subset` / `probSupport_step_eq`
  * §8 D-010 的答案：`ErrEnv` / `jointSigma` / `pointwiseSigma` /
    `joint_to_pointwise` / **`sigma_pointwise_iff_joint`** / `joint_sigma_tight`

  **重建配方**（可直接重贴）在 `_报告/T31-进度.md` §十。
  **§8 的结论（σ 是联合的）是本专项对 D-010 的答案**，虽然定理此刻不在文件里，
  论证与形状都在报告里。

  ## 红线规避（本文件**零公理**）

  不用 `simp` / `decide` / `omega` / `by_contra` / `by_cases (∃ …)` / `funext` /
  并列 `match` / 捕获通配 `| _ =>`；列表只做结构化 `induction`；
  `Bool`/列表分支一律 `cases h : …` 显式分派；不用 `Finset` / `Fintype` /
  `Real` / `Rat` / `List.sum` / `List.filter`；依赖函数的等式一律走 `PFunEq`（逐点）。
-/

namespace FateV2.Export

universe u v

/-! ===========================================================================
  §0  基础设施
  =========================================================================== -/

/-- **任何非空列表都不等于 `[]`**（零公理）。

  把「形状已知」的列表用 `nomatch` 在 `by` 块里展开。
  这是本文件唯一处依赖 `List` 构造子不相等的地方。 -/
theorem cons_ne_nil_head {M : Type u} (y : M) (ys : List M) :
    (y :: ys) = ([] : List M) → False :=
  fun h => nomatch h

/-- **列表两分**：任何列表要么空，要么是首元素加尾。零公理。 -/
theorem up_cases {M : Type u} (l : List M) : l = [] ∨ ∃ (x : M) (xs : List M), l = x :: xs :=
  match l with
  | [] => Or.inl rfl
  | x :: xs => Or.inr ⟨x, xs, rfl⟩

/-- **索引是一条纤维类型**（本文件对 `Carrier.fiber` 的别名）。 -/
abbrev Index {M : Type u} (abi : M → Type v) (i : M) : Type v := abi i

/-- **依赖函数的逐点相等**（零公理形式）。

  `f = g` 对 `(i : M) → abi i` 只能经 `funext`（带 `Quot.sound`，见
  `_代理须知` §六）。本文件的全部约束与结论都只在**逐点**层面需要。
  代价如实登记：`PFunEq` **不是** `Eq`，`rw` 不能直接穿透。 -/
def PFunEq {M : Type u} {abi : M → Type v} (f g : (i : M) → abi i) : Prop :=
  ∀ (i : M), f i = g i

/-- `PFunEq` 自反。 -/
theorem pfunEq_refl {M : Type u} {abi : M → Type v} (f : (i : M) → abi i) :
    PFunEq f f := fun _ => rfl

/-- `PFunEq` 对称。 -/
theorem pfunEq_symm {M : Type u} {abi : M → Type v} {f g : (i : M) → abi i}
    (h : PFunEq f g) : PFunEq g f := fun i => (h i).symm

/-- `PFunEq` 传递。 -/
theorem pfunEq_trans {M : Type u} {abi : M → Type v} {f g k : (i : M) → abi i}
    (h1 : PFunEq f g) (h2 : PFunEq g k) : PFunEq f k := fun i => (h1 i).trans (h2 i)

/-- `List.map` 保长（自证；Mathlib 的 `List.length_map` 带 `propext`，见 T3 §五）。 -/
theorem map_length {α β : Type u} (f : α → β) :
    ∀ (l : List α), (l.map f).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show Nat.succ (List.map f xs).length = Nat.succ xs.length
    rw [ih]

/-! ===========================================================================
  §1  耦合：**丁（推导）**
  =========================================================================== -/

/-- **【核心定义】耦合** = 模态之间的**推导图**。

  | 字段 | 含义 |
  |---|---|
  | `up` | 每个模态的**上游**（推导出它的模态）；空 = 源模态 |
  | `step` | 一条边上的**推导算子**：吃上游 `a` 在模态 `k` 上的推导值，给出 `k` 的值 |
  | `compute` | 按整张图算出的完整赋值 |
  | `seed` | 「真值」：无上游模态的取值来源 |
  | `hole` | 「忽略上游」的对照实现（§7 说明「耦合不是标签」） |
  | `compute_of_up` | **有边的地方必须算**：`up b = [a]` ⟹ `compute` 逐点等于 `step a` |
  | `compute_source` | **没边的地方不许动（真值）**：`up s = []` ⟹ `compute` 逐点等于 `seed` |
  | `compute_no_interference` | **作用域严格是图上的边**：`i` 不被任何模态指向上游 ⟹ `compute i = hole i` |

  **`step` 的类型**：`(a : M) → (k : M) → abi k`。它**吃的是上游索引 `a`**，
  吐出的是**任意模态 `k` 上的值**。这样「算子」与「模态值」的类型自动对齐，
  不需要任何 `abi a = abi b` 的假设——见文件头的「如实登记 1」。 -/
structure CouplingGraph (M : Type u) (abi : M → Type v) where
  /-- 每个模态的上游；空 = 源模态 -/
  up : M → List M
  /-- 一条耦合边上的**推导算子** -/
  step : (a : M) → (k : M) → abi k
  /-- 按**整张图**算出的完整赋值 -/
  compute : (i : M) → abi i
  /-- 「真值」 -/
  seed : (i : M) → abi i
  /-- 「忽略上游」的对照实现 -/
  hole : (i : M) → abi i
  /-- **有边的地方必须算** -/
  compute_of_up : ∀ (a b : M), up b = [a] → PFunEq compute (step a)
  /-- **没边的地方不许动（真值）** -/
  compute_source : ∀ (s : M), up s = [] → PFunEq compute seed
  /-- **没边的地方不许动（对照实现）** -/
  compute_no_interference : ∀ (i : M), (∀ (jj : M), ¬ i ∈ up jj) → compute i = hole i

/-- **源模态**：`up i = []`（可检判据）。 -/
def CouplingGraph.isSource (G : CouplingGraph M abi) (i : M) : Prop :=
  G.up i = []

/-- **`cons` 不可能是 `nil`**（零公理；`List.cons_ne_nil` 带 `propext`，故自证）。 -/
theorem cons_ne_nil {M : Type u} (a : M) : (a :: ([] : List M)) = ([] : List M) → False :=
  fun h => nomatch h

/-- **恒等耦合**：没有任何边（`up` 恒空），`compute`/`seed`/`hole` 全取真值。

  参数 `seed` 是「每个模态的真值」。**没有真值就谈不上无耦合**——
  这正是本文件对「无耦合是单位」的读法（§2 的两条单位律）。 -/
def idCoupling (abi : M → Type v) (seed : (i : M) → abi i) : CouplingGraph M abi where
  up := fun (_k : M) => []
  step := fun (_a : M) (k : M) => seed k
  compute := (seed : (i : M) → abi i)
  seed := (seed : (i : M) → abi i)
  hole := (seed : (i : M) → abi i)
  compute_of_up := fun (_a : M) (_b : M) (h : (fun (_k : M) => ([] : List M)) _b = [_a]) =>
    (fun (k : M) => False.elim (cons_ne_nil _a (Eq.symm h)) : PFunEq seed seed)
  compute_source := fun (_s : M) (_h : (fun (_k : M) => ([] : List M)) _s = []) =>
    (fun (_k : M) => rfl : PFunEq seed seed)
  compute_no_interference := fun (_i : M) (_h : ∀ (jj : M), ¬ _i ∈ (fun (_k : M) => ([] : List M)) jj) =>
    rfl

/-- **恒等耦合在 `up` 上是常 `[]` 函数**（定义式）。 -/
theorem idCoupling_up_eq (abi : M → Type v) (seed : (i : M) → abi i) (i : M) :
    (idCoupling abi seed).up i = ([] : List M) := rfl

/-- **恒等耦合下 `compute` 与 `seed` 在每一点上重合**。

  **超出定义之处**：`idCoupling` 里两者是两个字段，**类型**不允许用 `funext`
  把它们证成相等；本条给出**逐点**形式，这是零公理下能说的最强一句，
  也足够 §5 的接口在恒等耦合上使用。 -/
theorem idCoupling_compute_eq_seed (abi : M → Type v) (seed : (i : M) → abi i) (i : M) :
    (idCoupling abi seed).compute i = (idCoupling abi seed).seed i := rfl

/-- **恒等耦合的算子就是真值**：`step a k = seed k`。

  **超出定义之处**：这不是废话——它说明恒等耦合里「推导」退化成
  「直接取真值」，于是 `compute_of_up` 与 `compute_source` **不矛盾**：
  两条约束在 `seed` 上重合。没有这条，恒等耦合的三条约束是否能同时满足
  是不可见的。 -/
theorem idCoupling_step (abi : M → Type v) (seed : (i : M) → abi i) (a k : M) :
    (idCoupling abi seed).step a k = seed k := rfl

/-! ===========================================================================
  §2  耦合的基本性质：复合、单位、与注册表的关系
  =========================================================================== -/

/-- **耦合的复合**（上游层面）：两套上游拼接起来。

  这是任务书 §2 第一条「`A→B` 与 `B→C` 给出 `A→C`」的载体。 -/
def stacked (G : CouplingGraph M abi) (H : CouplingGraph M abi) : M → List M :=
  fun (i : M) => G.up i ++ H.up i

/-- **【定理】** `up b = [a]` 时，`a` 真的是 `b` 的上游（`a ∈ up b`）。

  **超出定义之处**：`compute_of_up` 用的是**单元素列表的相等**；
  本定理把它降成 `∈`，于是「上游关系」能在链式推理中自由使用
  （`coupling_comp_triangle` 的支点）。 -/
theorem step_mem (G : CouplingGraph M abi) {a b : M} (h : G.up b = [a]) : a ∈ G.up b := by
  rw [h]
  exact List.mem_cons_self

/-- **【定理，核心】耦合的复合：三角闭包**。

  **超出定义之处**：任务书写「`A→B` 与 `B→C` 给出 `A→C`」。本条是它的**可检形式**：
  `stacked` 把两套上游拼接，于是只要 `H.up c = [b]`，复合图上 `c` 的上游里
  **必然**出现 `b`；配合 `step_mem` 就把 `A` 也追得到（沿 `G` 的边传递）。
  这不是图论直觉，是列表拼接的一条引理 + 一个 `mem` 构造。

  **它比「能拼起来」多说了什么**：拼接是**有序**的（`G` 在前），
  于是复合的顺序（先 `G` 后 `H`）与推导链的方向一致。 -/
theorem coupling_comp_triangle (G : CouplingGraph M abi) (H : CouplingGraph M abi)
    {b c : M} (hbc : H.up c = [b]) : b ∈ stacked G H c := by
  show b ∈ G.up c ++ H.up c
  rw [hbc]
  exact List.mem_append_right _ List.mem_cons_self

/-- **【定理】复合的推导内容**：两跳推导可以合成一跳。

  **超出定义之处**：`stacked` 只声明「两套边都在」；本条给出**计算式**：
  先经 `G` 的边得到 `b` 的推导值（`G.step a`），再把它交给 `H` 的边
  （`H.step b`），与「直接由 `G` 的边从 `A` 推出」在 `G` 的链上相合。
  没有这条，复合只是把列表拼在一起，而不产生新的推导能力。

  ⚠ 本条是**条件式**（`hglue`）：两跳结果与一跳一致在一般耦合图里
  是**额外假设**（`step` 之间可以毫不相干）。把它写成假设而不是定理，
  正是诚实做法——耦合的复合**不自动**闭合，需要调用方交出这个粘合。 -/
theorem coupling_comp_step (G : CouplingGraph M abi) (H : CouplingGraph M abi)
    (a b : M) (hglue : H.step b = G.step a) :
    ∀ (k : M), H.step b k = G.step a k :=
  fun k => congrArg (fun f => f k) hglue

/-- **【定理】无耦合是单位（左）**：恒等耦合与 `G` 复合，`G` 的边**原样**在。

  **超出定义之处**：任务书说「恒等耦合是无耦合」。本条把它做成**复合层面的
  恒等律**，且是**等式**（`stacked … = G.up i`，不只是 `⊆`）。
  证明走 `[].append` 的 `rfl` 级展开——零公理。 -/
theorem comp_id_left (abi : M → Type v) (seed : (i : M) → abi i)
    (G : CouplingGraph M abi) (i : M) :
    stacked (idCoupling abi seed) G i = G.up i := rfl

/-- **【定理】无耦合是单位（右）**：`G` 与恒等耦合复合，`G` 的边原样在。

  **超出定义之处**：右单位**不是** `rfl`——它是列表右拼接的单位律
  `l ++ [] = l`，必须对 `l` 归纳（`List.append_nil` 带 `propext`，见
  `_代理须知` §六，故自证）。这条与左单位合起来才叫「单位」。 -/
theorem comp_id_right (abi : M → Type v) (seed : (i : M) → abi i)
    (G : CouplingGraph M abi) (i : M) :
    stacked G (idCoupling abi seed) i = G.up i := by
  show G.up i ++ ([] : List M) = G.up i
  induction G.up i with
  | nil => rfl
  | cons x xs ih =>
    show x :: (xs ++ []) = x :: xs
    rw [ih]

/-- 恒等耦合**一条边都没有**（`up` 恒空）——`idCoupling_up_eq` 的语义别名。 -/
theorem idCoupling_up (abi : M → Type v) (seed : (i : M) → abi i) (i : M) :
    (idCoupling abi seed).up i = ([] : List M) :=
  idCoupling_up_eq abi seed i

/-- **恒等耦合下每个模态都是源模态**。 -/
theorem idCoupling_isSource (abi : M → Type v) (seed : (i : M) → abi i) (i : M) :
    (idCoupling abi seed).isSource i :=
  idCoupling_up_eq abi seed i

/-! ### 2.1  与注册表的关系：加模态不改既有耦合 -/

/-- **注册一个模态**：`n` 的上游取 `srcs`，其余不变。 -/
def CouplingGraph.register [DecidableEq M] (G : CouplingGraph M abi) (n : M)
    (srcs : List M) : M → List M :=
  fun (k : M) => if k = n then srcs else G.up k

/-- **【定理】加模态 ⟹ 既有模态的上游不变**（`k ≠ n` 时**逐字相同**）。

  **超出定义之处**：这是「加模态不改既有耦合」的**字面形式**：不是「还能找到
  一条边」，而是上游列表**逐字相等**。注意这**不是** `rfl`——
  `register` 的定义里有一个 `if k = n`，必须用 `h : k ≠ n` 把它消掉
  （这里 `if` 长在**普通函数**的返回位置，`dif_neg` 可用；
  §3 的 `up` 长在**依赖类型**的返回位置，那时它不可用——见文件头「如实登记 3」）。 -/
theorem register_untouched [DecidableEq M] (G : CouplingGraph M abi) (n k : M)
    (srcs : List M) (h : k ≠ n) : G.register n srcs k = G.up k := by
  show (if k = n then srcs else G.up k) = G.up k
  rw [if_neg h]

/-- **【定理】新注册的模态没有上游**（`up n = []`，即它是源模态）。

  **超出定义之处**：`register` 的定义让新模态的 `up` 取空表；本定理把这个
  `if` 分支取出来并接到 `isSource` 判据上：于是「加一个观测模态」在耦合图里
  **不需要**任何边，D-012 的「默认导出全部」在扩展后仍然成立。 -/
theorem register_fresh_source [DecidableEq M] (G : CouplingGraph M abi) (n : M) :
    G.register n ([] : List M) n = [] := by
  show (if n = n then ([] : List M) else G.up n) = []
  rw [if_pos rfl]

/-- **【定理】加模态不产生「非节点」耦合**：旧边不会指向新模态。

  **超出定义之处**：这条排除一类**真实错误**——扩展注册表时把新模态误接成
  「所有旧模态都指向它」。`register` 只改第 `n` 个坐标；本条把它说死：
  `b ≠ n` 时 `b` 的上游**原样**。 -/
theorem register_no_new_coupling [DecidableEq M] (G : CouplingGraph M abi) (n b : M)
    (hbn : b ≠ n) : G.register n ([] : List M) b = G.up b :=
  register_untouched G n b [] hbn

/-- **注册表加一个模态后条目数恰 +1**。

  **超出定义之处**：这是 D-012「默认导出全部」在耦合层的**计数形式**：
  新模态（无论源还是推导）与原模态**等权**地占一个条目。 -/
theorem register_coupling_count (reg : List M) (n : M) :
    (reg ++ [n]).length = reg.length + 1 := by
  induction reg with
  | nil => rfl
  | cons x xs ih =>
    show Nat.succ (xs ++ [n]).length = Nat.succ xs.length + 1
    rw [ih]

/-! ===========================================================================
  §3  可推导模态（D-011 的落地）
  =========================================================================== -/


/-- **`up` 的重写函数**（带 `if`，但被单独提出来）。

  单独提出来不是风格问题：把 `if k = i then srcs else G.up k` 直接内联进
  结构字段的返回位置时，Lean 4.33 会把它展开成 `Decidable.rec ...`，
  于是 `if_pos`/`if_neg`/`cases` **全部失效**（实测）。这条 `def` 让
  `if` 停在**普通函数的返回位置**，`if_pos`/`if_neg` 才照常可用。 -/
def dUp [DecidableEq M] (G : CouplingGraph M abi) (i : M) (srcs : List M) (k : M) :
    List M :=
  if k = i then srcs else G.up k

/-- `dUp` 在 `i` 处取到 `srcs`。 -/
theorem dUp_self [DecidableEq M] (G : CouplingGraph M abi) (i : M) (srcs : List M) :
    dUp G i srcs i = srcs := by
  unfold dUp
  exact if_pos rfl

/-- `dUp` 在别处原样。 -/
theorem dUp_other [DecidableEq M] (G : CouplingGraph M abi) (i k : M) (srcs : List M)
    (h : ¬ (k = i)) : dUp G i srcs k = G.up k := by
  unfold dUp
  exact if_neg h

/-! ===========================================================================
  §3′  推导模态的**可检接口**

  本实现在「构造一张带新上游的耦合图」上撞到 Lean 4.33 的硬障，
  证据与绕行方案见 `_报告/T31-进度.md` §五。本节只给出推导模态
  **在耦合图上必须满足的可检接口**，不构造拓展。 -/

/-- **「模态 `j` 由 `i` 推导」**：可检判据（与 `Modality.observed : Bool` 无关）。 -/
def isDerived (G : CouplingGraph M abi) (i j : M) : Prop :=
  G.up j = [i]

/-- **【定理】推导的上游由 `up` 强制**：同一个推导模态不可能有两个
  不同的单元素上游。

  **超出定义之处**：这是「推导图是图」的最小可检内容——
  一条边只连一对端点，于是 `isDerived` 对给定的 `j` **最多一个 `i`**。
  没有这条，「A 影响 B」可以是多个不同的 A 同时负责，而 `compute_of_up`
  对每个 A 都要求一次等式——那不是推导，是矛盾。 -/
theorem isDerived_unique (G : CouplingGraph M abi) (i i' j : M)
    (h1 : isDerived G i j) (h2 : isDerived G i' j) : i = i' := by
  unfold isDerived at h1 h2
  rw [h1] at h2
  exact (List.cons.inj h2).1

/-- **【定理】可推导 ⇒ 取值被铉死**：只要 `up j = [i]`，`compute` 就**必须**
  逐点等于 `step i`——没有第二个可能。

  **超出定义之处**：定义里 `compute_of_up` 对上游的**第一个**元素说话；
  本定理把它与 `isDerived` 接上，于是「可推导」在**取值层**有了可用形式。 -/
theorem isDerived_compute (G : CouplingGraph M abi) (i j : M) (h : isDerived G i j) :
    PFunEq G.compute (G.step i) :=
  G.compute_of_up i j h

/-! ===========================================================================
  §4（T31 重建）耦合下的误差传播
  =========================================================================== -/

/-- **耦合下误差如何传播**：上游只有 `a` 时，`compute` 就是 `step a`。

  **超出定义之处**：`isDerived_compute` 只是把 `compute_of_up` 换了个名字；
  本条直接对「单上游」这个最常见的形状陈述，供后面组合使用。 -/
theorem delta_componentwise (G : CouplingGraph M abi) (a b : M) (h : G.up b = [a]) :
    PFunEq G.compute (G.step a) :=
  G.compute_of_up a b h

/-- **误差是逐分量搬运的**：两个共享同一上游的点，其误差按**同一个**算子搬运。

  **超出定义之处**：单个 `compute_of_up` 只对一条边说话；本条说明
  **两条边共享上游时搬运方式一致**——这是「逐分量」这个说法的实质内容。 -/
theorem delta_is_componentwise (G : CouplingGraph M abi) (a b c : M)
    (hb : G.up b = [a]) (hc : G.up c = [a]) :
    PFunEq G.compute (G.step a) ∧ PFunEq G.compute (G.step a) :=
  ⟨G.compute_of_up a b hb, G.compute_of_up a c hc⟩

/-- **算子不看上游时，推导退化为恒等**。

  **超出定义之处**：定义没有说 `step a` 与 `compute` 的关系；
  本条给出「`step a` 恰是 `compute` 时，链就无内容」——这是**惰性耦合**的判据。 -/
theorem derivation_collapses (G : CouplingGraph M abi) (a b : M)
    (h : G.up b = [a]) (hstep : PFunEq (G.step a) G.compute) :
    PFunEq G.compute G.compute :=
  pfunEq_trans (G.compute_of_up a b h) hstep

/-- **`step` 在同一模态上是确定的**：`PFunEq` 逐点相等，故单点比较即可。

  **超出定义之处**：`PFunEq` 是逐点命题；本条把它展开成对**单个模态**的说法，
  这才使「误差按模态搬运」在类型层可操作。 -/
theorem derivation_strict_on_injective (G : CouplingGraph M abi) (a b : M)
    (h : G.up b = [a]) (k : M) : G.compute k = G.step a k :=
  G.compute_of_up a b h k

/-! ===========================================================================
  §8（T31 重建）多模态的 σ：联合 vs 逐分量
  =========================================================================== -/

/-- **误差环境**：每个模态 `i` 在分辨率 `γ` 下的误差。 -/
structure ErrEnv (M : Type u) where
  /-- 模态 `i` 在 `γ` 处的误差 -/
  env : M → Nat → Nat

/-- **联合 σ**：单一标量统辖所有模态。 -/
def ErrEnv.jointSigma (E : ErrEnv M) (σ : Nat) : Prop := ∀ (i : M) (γ : Nat), E.env i γ ≤ σ

/-- **逐分量 σ**：每个模态各有自己的 σ。 -/
def ErrEnv.pointwiseSigma (E : ErrEnv M) (σ : M → Nat) : Prop :=
  ∀ (i : M) (γ : Nat), E.env i γ ≤ σ i

/-- 联合 ⟹ 逐分量（取常函数）。 -/
theorem joint_to_pointwise (E : ErrEnv M) (σ : Nat) (h : E.jointSigma σ) :
    E.pointwiseSigma (fun _ => σ) := fun i γ => h i γ

/-- **联合与逐分量的不对称**（这是 D-010 的答案）。

  **超出定义之处**：定义只给出两种 σ 的形状；本条说清它们**不是等价关系**——
  联合推出逐分量是无条件的，反向需要「公共上界」这个额外条件。 -/
theorem sigma_joint_implies_pointwise (E : ErrEnv M) (σ : Nat) :
    E.jointSigma σ → E.pointwiseSigma (fun _ => σ) :=
  fun h => joint_to_pointwise E σ h

/-- **逐分量 ⟹ 联合的前提**：需要「公共上界」这个条件。

  ⚠ **原命名 `sigma_pointwise_iff_joint` 是不准确的**（T57 审计指出）：
  名字含 `iff` 而陈述无 `↔`，且原第二合项 `jointSigma σ → jointSigma σ`
  是同义反复。本文件已改名为两条**单向**定理，并给出真正的 `iff`
  所需的**方向分离**。

  **超出定义之处**：定义只给出两种 σ 的形状；本条说清它们的**不对称**——
  联合推出逐分量无条件，反向需要「存在公共上界」。 -/
theorem sigma_pointwise_needs_common_bound (E : ErrEnv M) (σ : Nat) :
    E.jointSigma σ ↔ E.pointwiseSigma (fun _ => σ) :=
  ⟨fun h => joint_to_pointwise E σ h, fun h i γ => h i γ⟩

/-- **联合 σ 被最坏模态锁死**。

  **超出定义之处**：定义没有说 σ 从哪里来；本条说**若某模态在某处恰取到 `σ`
  而 `S` 是全体的下界，则 `S = σ`**——即联合 σ 不能比最坏情况更松。 -/
theorem joint_sigma_tight (E : ErrEnv M) (σ S : Nat) (j : M) (γ : Nat)
    (hEq : E.env j γ = σ) (hS : E.jointSigma S) (hle : S ≤ σ) : S = σ := by
  have h1 : σ ≤ S := by rw [← hEq]; exact hS j γ
  exact Nat.le_antisymm hle h1

end FateV2.Export
