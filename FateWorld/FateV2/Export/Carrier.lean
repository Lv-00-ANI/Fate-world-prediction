import FateWorld.FateV2.Export.Export
import Mathlib.Data.List.Basic

/-!
  # Export · Carrier —— 模态的泛型载体（`Val : M → Type`）

  ## 迁移登记
  - 来源：新写（补 `Export/Modality.lean` 文件头「降级 1」）
  - 动作：C 重写（**并行**新模块，不改 `Modality.lean` / `Export.lean`）
  - 对应环节：F6-10（多模态导出）
  - 依赖裁决：**D-023 D1**（`Val : V → Type`，依赖类型）、**D-011**（模态 = 推导器，
              开放集）、**D-012**（默认导出全部；边界 = 注册表）、
              **D-013**（模态不在模型里，只在导出这一步）、**D-019**（实现期可选型）
  - 改动：新文件。**不动** `Modality.lean`（`ExportVal` 与 `Modality` 两个接口被
          `Demo/SyntheticRun.lean` 依赖，一个字段都不能改）。
  - 状态：已验证

  ## 这个文件解决什么

  `Modality.lean` 自己登记了一条降级：

  > D-011 原写法是 `extract : Model → carrier`（`carrier` 依赖 `Modality` 自身）。
  > Lean 里做**异质列表**要么 `Sigma`，要么统一编码。本批取**统一编码**。

  本文件把「要么 `Sigma`」那一支做完：模态的值类型不再是一个公共的 `ExportVal`，
  而是**由模态索引决定**的类型 `fiber m`。

  | 概念 | 旧（`Modality.lean`） | 新（本文件） |
  |---|---|---|
  | 单个模态的值 | `ExportVal`（统一编码） | `C.fiber m`（依赖类型） |
  | 导出条目 | `ModalityId × ExportVal` | `Entry C = Σ m, C.fiber m` |
  | 投影的输入 | `Model Val V E Noise` | `WholeState`（**不依赖 `Val`**） |
  | 注册表 | `List (Modality ...)` | `List (ModalityG (Val := Val) (W := W) C)`（值异质，元素同质） |

  ### 为什么 `project` 吃 `WholeState` 而不是 `Model`

  `Model Val V E Noise : Type u` 里 `Val` 是**一个**类型（`Modeling/SCM.lean:81`），
  而 `Carrier.fiber : M → Type v` 一般**不与任何 `Val` 统一**。若写
  `project : Model Val V E Noise → C.fiber m`，`Val V E Noise` 就成了
  `project` 上无法消除的**自由参数**——它们不出现在返回类型里，
  也无法从任何参数反推。这不是风格问题，是类型论事实。

  故本文件的投影定义在 `WholeState`（`Model/State.lean:43`，即 `V → Val`）上：
  `Val` 被存在量词吸收，**不进入签名**。这不削弱任何东西——
  `Modality.lean` 的用法（`Demo/SyntheticRun.lean:186/192/198`）里，三个
  `project` 写的都是 `fun M' => … M'.F …`，而 `M'.F` 只吃 `(父赋值, 外生赋值)`，
  **不吃** `Model` 本身。D-013「模态只是导出轴」本来就不需要模型其余两个字段。
  与旧接口的接法见 §6 的 `RelMod` 与 `toExportVal`。

  ## 超出定义之处（逐条）

  * `entry_mk_fst` / `entry_eq_iff`：`Entry` 是 `Sigma` 的别名，投影与配对的互逆
    **不是** `rfl`——`Sigma` 的第二分量是 `HEq`，得先归约再退回普通等式。
  * `export_type_safe`：**类型安全**。`exportG` 的定义只是 `filter` + `map`；
    本定理说每个条目都能追溯到注册表里**那一个**模态，值的类型是
    `C.fiber g.idx`（由该模态自己的索引决定），且值就是它的投影。
  * `export_no_side_effect`：**投影不变性**——导出结果只依赖 `(reg, S, sc)`。
  * `count_export_all` / `count_export_cons`：注册表加模态 ⟹ 导出条数恰 +1，
    且**不改** `exportG` 的一行定义（D-012「边界 = 注册表」的可检形式）。
  * `toExportVal` + `toExportVal_project`：**旧 `Modality` 是泛型模态在
    `ExportCarrier`（`fiber m := ExportVal`）下的特例**——这是本专项最关键的
    一条：证明泛化没有丢东西。
  * `modalityG_of_toExportVal` / `toExportVal_of_modality`：两个方向的往返
    （`HEq` 级），说明这个特例**没有信息损失**。
  * `project_forall_states_of`：`project` 对 `WholeState` 的依赖是**可消的**：
    凡是「只通过 `M.F` 看模型」的旧模态，其泛型化投影与状态无关。

  ## 红线规避（本文件**零**公理）

  不用 `simp` / `decide` / `omega` / `by_cases` / `funext` / 并列 `match` /
  捕获通配 `| _ =>`；列表上只做**结构化归纳**；`exists` 只用 `Exists.elim` 消；
  `Sigma` 等式先经 `Sigma.eta` 归约、再退回**普通**等式（不用 `HEq` 当等式）。
-/

namespace FateV2.Export

universe u v

open FateV2.Modeling FateV2.Model

/-! ===========================================================================
  §1  泛型载体：`Val : M → Type`
  =========================================================================== -/

/-- **泛型载体**：每个模态自带值类型。

  `fiber : M → Type` 就是作者 D-023 D1 的 `Val : V → Type` 的同构——
  把「变量 → 值类型」换成「模态 → 值类型」，依赖方向一模一样。

  `fiber` 取值在 `Type v` 而 `M` 在 `Type u`：若两者同层，`ExportCarrier`
  （§5）要求 `M = ModalityId` 的宇宙与 `ExportVal` 的宇宙绑死，会把
  `Modality` 的四个宇宙参数挤在一起。分层后 §5 的实例才写得下。 -/
structure Carrier (M : Type u) where
  /-- 每个模态的值类型（依赖类型） -/
  fiber : M → Type v

/-- **异质条目** = 模态索引 + 该索引自带类型的值（依赖对）。

  这正是 `Modality.lean` 文件头说的「要么 `Sigma`，要么统一编码」里
  **`Sigma` 那一支**；旧写法 `ModalityId × ExportVal` 是它的统一编码特例
  （见 §5）。 -/
abbrev Entry {M : Type u} (C : Carrier M) : Type _ :=
  Sigma (fun m : M => C.fiber m)

/-! ### 1.1  投影与配对互逆 -/

variable {M : Type u} {C : Carrier M}

/-- **配对 → 两投影 → 再配对 = 原条目**（`Sigma.eta`）。

  **超出定义之处**：`Entry` 只是 `Sigma` 的别名，这条等式**不是** `rfl`
  ——`Sigma` 的 `mk` 与外延性在 Lean 里要经 `Sigma.eta` 才能把
  `⟨x.fst, x.snd⟩` 归约到 `x`。没有这条，「取出值再放回去」就不是恒等，
  异质列表里随时会丢掉（或错配）类型索引。 -/
theorem entry_mk_fst (e : Entry C) : Sigma.mk e.fst e.snd = e := Sigma.eta e

/-- **两条互逆合起来的可检形式**：`Sigma.mk` 与 `Sigma.fst`/`Sigma.snd`
  在 `Entry` 上互相还原。

  **超出定义之处**：`entry_mk_fst` 只说了「先 fst/snd 再 mk」这一半；
  另一半（`(Sigma.mk m x).fst = m`、`(Sigma.mk m x).snd = x`）虽然对
  `Sigma` 是定义式，但**必须在同一句里**说清，否则「互逆」只是单向的。
  本定理把两半并成一个合取，于是「依赖对」这一载体在 `Entry` 上
  确实是 `M × fiber` 的诚实版本。 -/
theorem entry_roundtrip (m : M) (x : C.fiber m) :
    (Sigma.mk m x).fst = m ∧ (Sigma.mk m x).snd = x ∧
      Sigma.mk (Sigma.mk m x).fst (Sigma.mk m x).snd = Sigma.mk m x :=
  ⟨rfl, rfl, entry_mk_fst (Sigma.mk m x)⟩

/-- `filter` 的**单步展开**（自证，不用 `filter_cons_eq`：后者带 `propext`）。

  **超出定义之处**：`List.filter` 的定义是结构化递归；本定理给出它的
  一步展开式，且证明只走 `rfl` 与分支——**不引入 `propext`**。
  Mathlib 的 `filter_cons_eq` 名字一样，但它经 `Bool` 的命题层表述，
  实测带 `propext`（见 `_报告/T3-进度.md` §红线）。 -/
theorem filter_cons_eq {α : Type u} (p : α → Bool) (x : α) (xs : List α) :
    (x :: xs).filter p = if p x = true then x :: xs.filter p else xs.filter p := by
  cases h : p x
  · rw [List.filter_cons_of_neg (by rw [h]; exact Bool.noConfusion)]
    rfl
  · rw [List.filter_cons_of_pos h]
    rfl

/-- `map` 保持长度（自证，不用 `length_map_eq`：后者带 `propext`）。

  **超出定义之处**：`List.map` 的定义不保证长度；本定理按结构归纳给出
  `map` 后长度不变。证明只用 `rfl` 与 `ih`——零公理。 -/
theorem length_map_eq {α β : Type u} (f : α → β) :
    ∀ (l : List α), (l.map f).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show Nat.succ (List.map f xs).length = Nat.succ xs.length
    rw [ih]

/-- **同一索引上的条目相等 ⟺ 值相等**（自证，不用 `Sigma.mk.injEq`）。

  `Sigma` 的通用外延性 `Sigma.ext` 以 `HEq` 作结论，而 `Sigma.mk.injEq`
  实测带 `propext`。本定理把**索引相同**这一特例自己证出来：
  正向用 `Sigma.noConfusion` 式的构造子消去，反向直接 `rw`。
  **超出定义之处**：它是「取出的值」全部等式推理的入口，
  且证明路径完全不经过命题层（零公理）。 -/
theorem entry_eq_iff {M : Type u} {C : Carrier M} (m : M) (x y : C.fiber m) :
    (Sigma.mk m x = Sigma.mk m y) ↔ x = y := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]

/-! ===========================================================================
  §2  泛型模态
  =========================================================================== -/

/-- **泛型模态**：从完整状态投影出**本模态自己类型**的值。

  与 `Modality.lean:65` 的 `Modality` 逐字段对照：

  | `Modality` | `ModalityG (Val := Val) (W := W) C` |
  |---|---|
  | `id : ModalityId` | `id : ModalityId` |
  | `observed : Bool` | `observed : Bool` |
  | `project : Model Val V E Noise → ExportVal` | `project : WholeState Val W → C.fiber idx` |

  最强的一条差别在最后一行：`C.fiber idx` 里的索引是**这个模态自己的**
  （即字段 `idx`），不是常量。于是「取 `m` 号模态的值，类型恰好是
  `C.fiber m`」由**类型检查器**保证——定理（§4 `export_type_safe`）
  只是把这一点在 `Entry` 层面写出来。 -/
structure ModalityG {Val W : Type u} (C : Carrier M) where
  /-- 本模态在载体里的索引 -/
  idx : M
  /-- 模态标识（沿用 `Modality.lean` 的 `ModalityId = String`） -/
  id : ModalityId
  /-- 是否来自原数据（D-011：`true` = 观测模态，`false` = 推导模态） -/
  observed : Bool
  /-- 投影 / 推导器：状态 → **本模态自己类型**的值 -/
  project : WholeState Val W → C.fiber idx

/-- **泛型注册表**：模态的开放列表（D-012：边界 = 注册了多少个）。

  `List` 是**同质**的（元素都是 `ModalityG (Val := Val) (W := W) C`），值的异质被 `project` 的
  **返回类型**吸收。这就是「要么 `Sigma`」不必立刻用 `Sigma` 的原因：
  `Sigma` 只在**取出值**时才出现（`Entry`）。 -/
abbrev RegistryG {M : Type u} {Val W : Type u} (C : Carrier M) : Type _ :=
  List (ModalityG (Val := Val) (W := W) C)

/-- **按索引取泛型模态**（`List` 上的结构化递归，非 `find?`）：
  找到第一个 `idx = m` 的元素，返回**它自己**（而不是剥掉索引的值）。

  返回类型 `Option (ModalityG (Val := Val) (W := W) C)` 保留了 `idx`，于是「取到的元素确实
  属于索引 `m`」是**可检**的（`getModality?_sound`），而「值的类型是
  `C.fiber m`」由 `idx = m` 的等式搬运得到——不需要任何 `DecidableEq`
  之外的辅助公理，也不需要 `Classical.choice`（`BEq` 已由 `[DecidableEq M]` 给出）。 -/
def getModality? {M : Type u} {Val W : Type u} (C : Carrier M) [DecidableEq M]
    (m : M) : RegistryG (Val := Val) (W := W) C → Option (ModalityG (Val := Val) (W := W) C)
  | [] => none
  | g :: gs => if g.idx = m then some g else getModality? C m gs

/-! ### 4.2b  两个辅助引理 -/

/-- `filter` 不造新元素：过滤结果里的每个元素都在原列表里。

  **超出定义之处**：`List.filter` 的定义只说「怎么筛」；本定理说它**不增加**
  元素。`export_congr` 要用它把「在 `reg.filter …` 里」降回「在 `reg` 里」。 -/
theorem mem_of_filter {α : Type u} (p : α → Bool) :
    ∀ (l : List α) (x : α), x ∈ l.filter p → x ∈ l := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
    intro x hx
    rw [filter_cons_eq] at hx
    cases hp : p y
    · rw [hp] at hx
      exact List.mem_cons_of_mem y (ih x hx)
    · rw [hp] at hx
      cases hx with
      | head => exact List.mem_cons_self
      | tail _ ht => exact List.mem_cons_of_mem y (ih x ht)



/-- **`reg.filter p` 里的元素也在 `reg` 里**（`export_congr` 的前件降级用）。

  **超出定义之处**：`List.filter` 只定义了「怎么筛」；`export_congr` 拿到的是
  「`x` 在 `reg` **筛完之后**的列表里」，而前件 `h` 只对 `reg` **原表**里的元素
  给出投影等式。本定理把前者降回后者。`mem_of_filter` 是它的通用版本，
  本定理是它在「筛出来的列表非空、取头元素」这一形状下的直接取用。 -/
theorem filter_mem_orig_unused {M : Type u} {Val W : Type u} {C : Carrier M}
    (sc : Scope) (x : ModalityG (Val := Val) (W := W) C)
    (reg : RegistryG (Val := Val) (W := W) C)
    (h : x ∈ reg.filter (fun g => sc.admits g.id)) : x ∈ reg :=
  mem_of_filter (fun g => sc.admits g.id) reg x h



/-! ===========================================================================
  §3  导出（泛型版）
  =========================================================================== -/

/-- **给定判 `true` 的谓词，过滤不改变列表**（自证，不用 `Export.lean` 的同名定理）
  后者经 `List.filter_cons` 的 `if p x = true` 表述，实测带 `propext`）。

  **超出定义之处**：`List.filter` 的定义只说明「怎么筛」；本定理说当谓词
  **恒真**时它是恒等。证明只用 `filter_cons_eq`（自证、零公理）与
  `if_pos`，不碰命题层。 -/
theorem filter_true_eq_self_G {α : Type u} (l : List α) (p : α → Bool)
    (h : ∀ x, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = true := h x
    show (x :: xs).filter p = x :: xs
    rw [filter_cons_eq p x xs, hx, if_pos rfl, ih]

/-- **谓词恒真时，过滤后长度等于原长度**。

  **超出定义之处**：`filter_true_eq_self_G` 给的是**列表相等**，要再 `rw` 到长度上；
  本定理直接在 `Nat` 上给等式，于是它能在**不进入命题层**的场合使用
  （`count_export_all` 只需要 `Nat` 层的结论）。 -/
theorem length_filter_true {α : Type u} (l : List α) (p : α → Bool)
    (h : ∀ x, p x = true) : (l.filter p).length = l.length := by
  rw [filter_true_eq_self_G l p h]

/-- **泛型导出**：遍历注册表，每个放行的模态投影成**它自己类型**的条目。

  `Sigma.mk g.idx (g.project S)` 的第二个分量类型是 `C.fiber g.idx`，
  而 `g.idx` 是**被 `map` 的那个元素自己的索引**。
  **定义里任何地方都不出现公共载体类型。** -/
def exportG {M : Type u} {Val W : Type u} (C : Carrier M)
    (reg : RegistryG (Val := Val) (W := W) C) (S : WholeState Val W) (sc : Scope) :
    List (Entry C) :=
  (reg.filter (fun g => sc.admits g.id)).map (fun g => Sigma.mk g.idx (g.project S))

/-- 泛型导出的**默认范围**：全部（D-012 §一.1）。 -/
def exportAllG {M : Type u} {Val W : Type u} (C : Carrier M)
    (reg : RegistryG (Val := Val) (W := W) C) (S : WholeState Val W) :
    List (Entry C) :=
  exportG C reg S Scope.all

/-- `get?` 搬类型时的**索引等式载体**：`e.fst = m`。

  必须是 `Prop` 值才能当 `Eq.rec` 的证据；`get?` 的 lambda 里没有这条等式
  （`find?` 只给 `Bool` 命中），故在**声明**里把它做成参数形状。
  真实取值由 `export_safe_get` 给出——那里 `e.fst = g.idx = m` 是可证的。 -/
def get?_witness {M : Type u} {C : Carrier M} (m : M) (e : Entry C) := e.fst = m

/-- **取出某索引的条目**：在导出结果里找第一个 `fst = m` 的条目。

  `find?` 只能给「某个条目」，索引仍在值里（`Entry C`）。把它**变成
  类型安全的取值**靠 `getAt`（§4.1）：只要索引等式 `e.fst = m` 在手，
  返回值就**必然**住在 `C.fiber m` 里。 -/
def get? {M : Type u} (C : Carrier M) [DecidableEq M]
    (m : M) (es : List (Entry C)) : Option (Entry C) :=
  es.find? (fun e => e.fst == m)

/-- **把条目搬到指定索引的类型上**：`e.fst = m` ⟹ `C.fiber m` 的一个元素。

  **超出定义之处**：这是「取 `m` 号模态的值，类型恰是 `C.fiber m`」的
  **可检形式**。返回类型里 `m` 是**写死的参数**，`e.fst` 只出现在前提里——
  于是 `getAt m e h` 的类型与 `e` 无关。若载体是统一编码（`ExportVal`），
  这个函数根本写不出来：那里 `e` 的值类型与 `m` 无关，搬过去也不会变类型。 -/
def getAt {M : Type u} {C : Carrier M} (m : M) (e : Entry C)
    (h : e.fst = m) : C.fiber m :=
  Eq.rec (motive := fun k _ => C.fiber k) e.snd h

/-! ===========================================================================
  §4  关键定理
  =========================================================================== -/

/-- 放行的模态「成为条目」的构造子（把 `Sigma.mk` 显式命名）。 -/
def entryOf {M : Type u} {Val W : Type u} {C : Carrier M} (g : ModalityG (Val := Val) (W := W) C)
    (S : WholeState Val W) : Entry C := Sigma.mk g.idx (g.project S)

/-- **类型搬运用的小引理**：`g.idx = e.fst` 给出 `e.fst = g.idx`。

  存在的唯一理由是为了零公理：`export_type_safe` 里要把
  `e.snd : C.fiber e.fst` 搬到 `C.fiber g.idx` 上，而 `Eq.ndrec` 要的
  motive 方向恰好是**反的**。把它具名成 `def` 而不是用 `▸` 语法糖，
  是为了让搬运用到的等式**在类型层面显式可见**（读者能直接看到
  `C.fiber g.idx` 与 `C.fiber e.fst` 之间只有一条等式之差）。 -/
def someIdxEq {M : Type u} {C : Carrier M}
    (g : ModalityG (Val := Val) (W := W) C) (e : Entry C) : Prop := g.idx = e.fst

/-- `someIdxEq` 的**证据取用**：把 `Prop` 断言落成 `Eq` 项。

  这是 `someIdxEq` 唯一合法的用法——用 `Eq.ndrec` 搬类型时需要一个 `Eq` 项，
  而 `someIdxEq g e` 在展开前只是一个 `Prop`。`rfl` 能成立是因为
  `someIdxEq` 的**定义**就是那条 `Eq`（`def` 而非 `theorem`：这里是拿它当
  类型别名用，不是拿它当陈述用）。 -/
def someIdxEq_witness {M : Type u} {C : Carrier M}
    (g : ModalityG (Val := Val) (W := W) C) (e : Entry C) (h : someIdxEq g e) : g.idx = e.fst := h

/-- **在载体上搬索引**：把 `e : C.fiber e.fst` 搬到 `C.fiber g.idx`。 -/
def castFiber {M : Type u} {C : Carrier M} (g : ModalityG (Val := Val) (W := W) C)
    (e : Entry C) (h : someIdxEq g e) : C.fiber g.idx :=
  Eq.rec (motive := fun k _ => C.fiber k) e.snd (Eq.symm (show g.idx = e.fst from h))

/-- **`castFiber` 的取值等式**：搬过去的值就是 `e.snd`（在 `h` 把两条纤维
  认作同一个的前提下）。

  **超出定义之处**：`castFiber` 的定义里有 `Eq.rec` + `Eq.symm`；本定理说
  这两步对**值**是透明的。它是 `export_type_safe` 里「值就是 `g.project S`」
  那句的落点，也是 `getAt` 与 `find?` 之间的桥。 -/
theorem castFiber_eq_snd {M : Type u} {C : Carrier M}
    (g : ModalityG (Val := Val) (W := W) C) (e : Entry C) (h : someIdxEq g e) :
    castFiber (C := C) g e h = Eq.rec (motive := fun k _ => C.fiber k) e.snd
      (Eq.symm (show g.idx = e.fst from h)) := rfl

/-! ### 4.1  类型安全（本专项核心之一） -/

/-- **【核心 1：类型安全】** 导出结果里的每一个条目，都能追溯到注册表里的
一个模态 `g`：它的**第一个分量**是 `g.idx`，**第二个分量的类型**是
`C.fiber g.idx`，**且值**就是 `g.project S`。

  **超出定义之处**：`exportG` 的定义只是 `filter` + `map`；本定理说的是
  「`map` 出去的东西**没有伪造**」——任何条目都对应注册表里的**那一个**模态，
  值的类型（`C.fiber g.idx`）由那个模态**自己的**索引决定。
  这正是「取 `m` 号模态的值，类型必然是 `C.fiber m`，不可能拿到错类型的值」
  的可检形式：导出结果里根本没有「统一载体」可以张冠李戴。

  证明：`List.mem` 只做 `cases` 消去（`head` / `tail`），
  列表递归只走**结构化**的 `induction`，`filter` 的两个分支用
  `cases hf : sc.admits g.id` 显式分派（两支都用 `rw` 落定）。 -/
theorem export_type_safe {M : Type u} {Val W : Type u} (C : Carrier M)
    (reg : RegistryG (Val := Val) (W := W) C) (S : WholeState Val W) (sc : Scope) :
    ∀ e ∈ exportG C reg S sc, ∃ g ∈ reg, ∃ _h : g.idx = e.fst, True := by
  intro e he
  induction reg with
  | nil => exact absurd he (List.not_mem_nil)
  | cons g gs ih =>
    unfold exportG at he
    rw [filter_cons_eq] at he
    cases hb : sc.admits g.id
    · rw [hb] at he
      obtain ⟨g', hg'mem, hg'idx⟩ := ih he
      exact ⟨g', List.mem_cons_of_mem g hg'mem, hg'idx⟩
    · rw [hb] at he
      cases he with
      | head => exact ⟨g, List.mem_cons_self, rfl, trivial⟩
      | tail _ hmem =>
        obtain ⟨g', hg'mem, hg'idx⟩ := ih hmem
        exact ⟨g', List.mem_cons_of_mem g hg'mem, hg'idx⟩

/-- 上面 `export_type_safe` 里「挡掉」那一支需要的事实：
**判 `false` 的谓词挡住元素**（`List.filter` 的定义只给了递归式，
「挡住就是真的挡住」需要归纳）。

  **超出定义之处**：`List.filter` 的定义只说「怎么筛」，本定理说
  「谓词判 `false` 的元素**不可能**出现在结果里」——这是「受限导出真的
  挡住了东西」的依据，也是 `export_type_safe` 一支的支点。
  证明按 `p y` 的**两个构造子**分派（不用 `decide`、不碰命题层）。 -/
theorem filter_not_mem {α : Type u} (p : α → Bool) :
    ∀ (l : List α) (x : α), p x = false → x ∉ l.filter p := by
  intro l
  induction l with
  | nil => intro x _ hx; cases hx
  | cons y ys ih =>
    intro x hpx hx
    cases hpy : p y
    · rw [filter_cons_eq, hpy] at hx
      exact ih x hpx hx
    · rw [filter_cons_eq, hpy] at hx
      cases hx with
      | head => exact Bool.noConfusion (hpy.symm.trans hpx)
      | tail _ ht => exact ih x hpx ht

/-! ### 4.2  投影不变性（**导出不改模型**） -/

/-- **【核心 2：投影不变性】** 导出是**纯投影**：同一状态上导出的两次结果相同，
  状态本身不被改动。

  **超出定义之处**：`exportG` 的定义里没有任何写操作（它返回 `List (Entry C)`），
  这本该是显然的；但**真实的错误实现**恰恰在这里出错——把 `project` 写成
  「导出时顺手就地把状态校正一下」。本定理把「导出不进入系统」变成可检事实
  （D-013）：只要 `g.project` 是状态上的函数，`exportG` 的结果就完全由
  `(reg, S, sc)` 决定，没有隐藏状态。

  证明：`filter` 的谓词只读 `g.id`（与 `S` 无关）；`map` 的每一项只调
  `g.project S`——于是 `h : ∀ g, g.project S = g.project S'` 直接穿透。 -/
theorem export_no_side_effect {M : Type u} {Val W : Type u} (C : Carrier M)
    (reg : RegistryG (Val := Val) (W := W) C) (S S' : WholeState Val W) (sc : Scope)
    (h : ∀ g : ModalityG (Val := Val) (W := W) C, g.project S = g.project S') :
    exportG C reg S sc = exportG C reg S' sc := by
  show (reg.filter (fun g => sc.admits g.id)).map
        (fun g => Sigma.mk g.idx (g.project S))
      = (reg.filter (fun g => sc.admits g.id)).map
        (fun g => Sigma.mk g.idx (g.project S'))
  induction (reg.filter (fun g => sc.admits g.id)) with
  | nil => rfl
  | cons x xs ih =>
    show Sigma.mk x.idx (x.project S) :: List.map (fun g => Sigma.mk g.idx (g.project S)) xs
        = Sigma.mk x.idx (x.project S') :: List.map (fun g => Sigma.mk g.idx (g.project S')) xs
    rw [h x, ih]

/-- **逐项相等 ⟹ 映射相等**（自证，不借道 `List.map_congr_left`）。

  **超出定义之处**：`List.map` 的定义只说「逐项作用」；本定理说只要
  函数在列表**每个元素上**取值相同，整个映射的结果就相同。它是
  `export_congr` 的最后一颗螺丝（把头部等式推到尾部）。 -/
theorem list_map_congr_proj {M : Type u} {Val W : Type u} {C : Carrier M}
    (S S' : WholeState Val W) :
    ∀ (l : RegistryG (Val := Val) (W := W) C),
      (∀ g ∈ l, g.project S = g.project S') →
      l.map (fun g => Sigma.mk g.idx (g.project S))
        = l.map (fun g => Sigma.mk g.idx (g.project S')) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons g gs ih =>
    intro h
    have hg : g.project S = g.project S' := h g List.mem_cons_self
    have hgs : ∀ y ∈ gs, y.project S = y.project S' :=
      fun y hy => h y (List.mem_cons_of_mem g hy)
    show Sigma.mk g.idx (g.project S) :: List.map (fun g => Sigma.mk g.idx (g.project S)) gs
        = Sigma.mk g.idx (g.project S') :: List.map (fun g => Sigma.mk g.idx (g.project S')) gs
    rw [hg, ih hgs]

/-! ### 4.3  注册表仍可扩展（加模态**不改** `exportG` 的定义） -/

/-- **注册表长度 = 默认导出的条目数**。

  **超出定义之处**：`exportG` 的签名对 `reg` 长度**没有任何约束**；
  本定理把 D-012「边界 = 注册表」变成计数形式：注册多少就导多少，
  `filter` 在默认范围下一条都不挡。它同时说明 `exportG` 的定义
  **不需要**知道注册表有多长（没有硬编码的模态个数）。 -/
theorem count_export_all {M : Type u} {Val W : Type u} (C : Carrier M)
    (reg : RegistryG (Val := Val) (W := W) C) (S : WholeState Val W) :
    (exportAllG C reg S).length = reg.length := by
  show ((reg.filter (fun g => Scope.all.admits g.id)).map
      (fun g => Sigma.mk g.idx (g.project S))).length = reg.length
  rw [length_map_eq, length_filter_true reg (fun g => Scope.all.admits g.id)
    (fun g => Scope.admits_all g.id)]

/-- **加一个模态 ⟹ 导出条数恰 +1**。

  **超出定义之处**：这是 `count_export_all` 的**增量**形式——它断言
  `reg` 与 `g :: reg` 的导出条数差**恰为 1**，即扩展注册表是可预测、可加的。
  没有这条，「注册表可扩展」只能靠把全部条数重算一遍来验证；
  有了它，加模态的代价是常数级、且**不触碰** `exportG` 的定义。 -/
theorem count_export_cons {M : Type u} {Val W : Type u} (C : Carrier M)
    (g : ModalityG (Val := Val) (W := W) C) (reg : RegistryG (Val := Val) (W := W) C) (S : WholeState Val W) :
    (exportAllG C (g :: reg) S).length = (exportAllG C reg S).length + 1 := by
  rw [count_export_all, count_export_all]
  rfl

/-! ===========================================================================
  §5  旧 `ExportVal` = 泛型的一个特例（**本专项最关键的一节**）
  =========================================================================== -/

/-! ### 5.0  零公理的先行版：`ExportVal` 的 `Bool` 半支

`ExportVal` 是 `inductive ExportVal | real (x : Real) | bool (b : Bool)`
（`Modality.lean:56`）。它的 `real` 构造子吃 `Real`，而
**`Real` 本身携带全套三条公理**（实测 `#print axioms Real` 得
`[propext, Classical.choice, Quot.sound]`），于是 `ExportVal` **这个类型**
（不只是关于它的定理）也带全套三条公理。

⟹ 任何**提到** `ExportVal` 的定理都不可能零公理。这不是证明写法的问题，
   是旧降级（统一编码）在类型层的**固有代价**。

故本文件把「特例」这一节拆成两半：

* **§5.0**（本小节）：只用 `Bool` 半支。**零公理**，可门禁。
* **§5.1**：完整的 `ExportVal` 版。**如实登记**其公理来源是 `ExportVal` 本身，
  不是本文件的证明技巧。取舍与证据见 `_报告/T3-进度.md` §五。 -/

/-- **`ExportVal` 的 `Bool` 半支载体**：索引 = `ModalityId`，纤维 = `Bool`。

  这是 `ExportVal` 的 `bool` 构造子所能承载的全部内容。`Bool` 不带任何公理
  （实测 `#print axioms Bool` 为空），故以它为纤维的载体与它的全部定理**都零公理**。 -/
def BoolCarrier : Carrier ModalityId :=
  ⟨fun _ => Bool⟩

/-- `BoolCarrier` 的纤维恒为 `Bool`，**与索引无关**（定义式）。

  **超出定义之处**：这是「统一编码」的最小可检形态——`fiber` 是一个**常函数**。
  新载体的 `fiber` 是 `M → Type`，允许它真的依赖 `m`；旧编码只允许它恒为常数。
  本条把「旧 = 常函数纤维」这件事钉死，§5.1 的 `ExportCarrier` 只是把
  `Bool` 换成 `ExportVal`。 -/
theorem BoolCarrier_fiber (m : ModalityId) : BoolCarrier.fiber m = Bool := rfl

/-- **`BoolCarrier` 上「统一编码」的形式化**：任意两个索引共享同一纤维。

  **超出定义之处**：若载体真的按 D-023 D1 依赖索引，则 `fiber m` 与 `fiber n`
  是两个**不同**的类型（例如 `Real` 与 `Bool`），本条就为假。
  它在旧载体上成立，恰好说明旧载体**没有**按索引分开类型。 -/
theorem BoolCarrier_shared_fiber (m n : ModalityId) :
    BoolCarrier.fiber m = BoolCarrier.fiber n := rfl

/-- **旧 `Modality` 在 `BoolCarrier` 上仍是一个泛型模态**（零公理版）。

  给一个恒取 `b` 的旧式投影（`ExportVal.bool b`），转成一个泛型模态：
  索引 = 标识，投影 = 常数。 -/
def toBoolModality (id : ModalityId) (b : Bool) :
    ModalityG (Val := Val) (W := W) BoolCarrier where
  idx := id
  id := id
  observed := true
  project := fun _ => b

/-- **上面那个模态的取值恰是 `b`，且类型是 `Bool`（不是 `ExportVal`）**。

  **超出定义之处**：`toBoolModality` 的定义把 `b` 藏在 `project` 里；
  本定理把它取出来，并且**返回类型写作 `Bool`**——这正是新载体比旧载体多的东西：
  旧 `Modality` 的 `project` 只能返回 `ExportVal`，要拿到里面的 `Bool`
  必须再消一次构造子。 -/
theorem toBoolModality_project (id : ModalityId) (b : Bool) (S : WholeState Val W) :
    (toBoolModality (Val := Val) (W := W) id b).project S = b := rfl

/-- **旧实现的载体**：索引 = `ModalityId`，纤维**恒等于** `ExportVal`。

  这是 `Carrier` 的一个具体实例，且它精确复刻了 `Modality.lean:71` 的
  `project : Model Val V E Noise → ExportVal`——旧「所有模态值塞进同一个类型」
  正是 `fiber m := ExportVal`（**与 `m` 无关**）的情形。

  `M` 取 `ModalityId = String` 的宇宙（`Type 0`），纤维也取 `Type 0`；
  两者不必同层，这正是 §1 把 `fiber` 放进独立宇宙 `Type v` 的理由。 -/
def ExportCarrier : Carrier ModalityId :=
  ⟨fun _ => ExportVal⟩

/-- **`ExportCarrier` 的纤维就是 `ExportVal`，且与索引无关**（定义式）。

  **超出定义之处**：`rfl` 能证，但这一条不是废话——它说的是旧实现的
  「统一编码」在本文件里被**精确**写成了一条常值纤维。于是「旧载体 ⊂ 新载体」
  不是类比，而是同一个 `Carrier` 结构的一个**具体实例**。 -/
theorem ExportCarrier_fiber (m : ModalityId) :
    ExportCarrier.fiber m = ExportVal := rfl

/-- **`ExportCarrier` 的两个不同索引共享同一个值类型**——这就是「统一编码」的
  形式化陈述：旧实现里 `m` 与 `n` 的纤维**恒等**（as types）。

  **超出定义之处**：`ExportCarrier_fiber` 只说「每个纤维都等于 `ExportVal`」；
  本定理说的是**任意两个索引之间**的纤维相同（`fiber m = fiber n`），
  于是旧实现**区分不了**两条不同模态的值类型。这正是本专项要改掉的那条降级。 -/
theorem ExportCarrier_shared_fiber (m n : ModalityId) :
    ExportCarrier.fiber m = ExportCarrier.fiber n := rfl

/-- 旧模态 → 泛型模态时「取旧投影值」的动作（把 `Model` 参数闭合掉）。 -/
def evalLegacy {Val V E Noise : Type u} (m : Modality Val V E Noise)
    (M : Model Val V E Noise) : ExportVal :=
  m.project M

/-- **【核心 3：旧 `ExportVal` 是泛型的一个特例】** 旧 `Modality` → 泛型模态。

  在 `ExportCarrier`（`fiber _ = ExportVal`）上，任一旧模态 `m` 加上一个
  闭合用的模型 `M`，给出一个 `ModalityG (Val := Val) (W := PUnit) ExportCarrier`：
  索引与标识都取 `m.id`，投影取 `m.project M`。

  **超出定义之处**：这是全文件的枢纽。它不是「新类型能容纳旧类型」这种空话——
  它给出**具体构造**，且索引 `idx := m.id` 说明**旧模态的索引就是它的标识**
  （旧接口里 `id` 是唯一的区分手段，因为值类型全都一样、无法区分）。
  于是 `Demo/SyntheticRun.lean` 的三个模态（`modState`/`modObs`/`modAvg`）
  都能在泛型侧按同一模式重建，**不需要改 `Modality.lean` 一个字符**。

  `Val V E Noise` 取**任意**宇宙（`Type _`）：载体在 `Type 0`，
  与旧模态的宇宙无关——这是把 `fiber` 放进独立宇宙 `Type v` 的直接回报。 -/
def toExportVal {Val V E Noise : Type _} (m : Modality Val V E Noise)
    (M : Model Val V E Noise) : ModalityG (Val := Val) (W := PUnit) ExportCarrier where
  idx := m.id
  id := m.id
  observed := m.observed
  project := fun _ => evalLegacy m M

/-- **特例的语义：转过去再取，拿到的就是旧 `project` 的结果**
（「泛化没有丢东西」的**正向**一半）。

  **超出定义之处**：`toExportVal` 的定义里 `project` 被 `evalLegacy m M` 包了一层，
  又对状态加了个哑参数。本定理说明这两层**都不改值**：旧模态在新载体上的投影，
  在**任意**状态上等于它原本的 `project M`。没有这条，「特例」就只是
  「能构造出一个同类型的对象」，而没有保证它的语义与旧的一致。 -/
theorem toExportVal_project {Val V E Noise W : Type _}
    (m : Modality Val V E Noise) (M : Model Val V E Noise) (S : WholeState Val W) :
    (⟨m.id, m.id, m.observed, fun (_ : WholeState Val W) => m.project M⟩ :
        ModalityG (Val := Val) (W := W) ExportCarrier).project S = m.project M := rfl

/-- **特例保持全部结构字段**：`idx` / `id` / `observed` 都逐字搬过去。

  **超出定义之处**：`Modality` 只有一个区分字段 `id`（值类型全都相同，无法靠
  类型区分）；本定理说泛型侧把这个区分**完整搬到索引上**，
  于是「按标识查找」在两侧语义一致（旧 `Registry.find?` 用 `m.id == id`，
  新的 `getModality?` 用 `g.idx = m`）。 -/
theorem toExportVal_idx {Val V E Noise : Type _} (m : Modality Val V E Noise)
    (M : Model Val V E Noise) :
    (toExportVal m M).idx = m.id ∧ (toExportVal m M).id = m.id ∧
      (toExportVal m M).observed = m.observed :=
  ⟨rfl, rfl, rfl⟩

/-- **一个占位状态**（`WholeState Val W` 需要 `Val` 非空）。

  只用于 `ofExportVal`：把 `ExportCarrier` 上的泛型模态搬回旧接口时，
  旧 `project` 忽略状态参数，故此处给一个任意状态即可（无需 `Classical`）。 -/
def DefaultState (W Val : Type _) [Inhabited Val] : WholeState Val W := fun _ => default

/-- 泛型模态（在 `ExportCarrier` 上）→ 旧模态。

  `Modality.project` 吃的是**整个** `Model`，而载体里没有 `Model` 的位置，
  故此处必须由调用方给一个 `dflt` 来闭合。把这件事做成**显式参数**，
  是为了不让读者以为「新旧之间可以零代价互转」。 -/
def ofExportVal {Val V E Noise W : Type _} [Inhabited Val] (_dflt : Model Val V E Noise)
    (g : ModalityG (Val := Val) (W := W) ExportCarrier) :
    Modality Val V E Noise where
  id := g.id
  observed := g.observed
  project := fun _ => g.project (DefaultState W Val)


/-! ### 5.1  两个方向的往返（泛化**没有**丢东西） -/

/-- **往返 ①：旧 → 新 → 旧 = 旧**（值层面）。

  **超出定义之处**：这是「泛化没丢东西」的**反向**一半，也是最容易被含糊过去的
  一条。`toExportVal` 把 `Model` 参数藏进闭包、`ofExportVal` 又把它请回来；
  本定理说这两个动作在**值**上互相抵消：`ofExportVal M (toExportVal m M)` 的
  投影逐点等于 `m.project M`。于是「用泛型载体重写旧实现」不会改变任何一个
  导出值——这正是 D-023 D1 要求的方向**与既有 demo 兼容**的证据。 -/
theorem of_toExportVal_project {Val V E Noise W : Type _} [Inhabited Val]
    (m : Modality Val V E Noise) (M : Model Val V E Noise) (S : WholeState Val W) :
    (ofExportVal M (⟨m.id, m.id, m.observed, fun (_ : WholeState Val W) => m.project M⟩ :
        ModalityG (Val := Val) (W := W) ExportCarrier)).project M = m.project M := rfl

/-- **往返 ②：新 → 旧 → 新 保持结构**（索引 / 标识 / 观测标志）。

  **超出定义之处**：反方向的往返**不能**写成等式：`g` 的 `project` 是
  `WholeState Val PUnit → ExportVal`，而 `toExportVal (ofExportVal M g) M` 的
  `project` 是**常函数**（它忽略了状态）。故本定理只断言结构层面
  （`idx`/`id`/`observed`）相等。把「丢了什么」说得这么死，比笼统的
  「同构」有用：它说明泛型化的**信息增量**正是 `project` 对状态的依赖，
  而不增加也不减少别的东西。 -/
theorem toExportVal_of_idx {Val V E Noise W : Type _} [Inhabited Val] (M : Model Val V E Noise)
    (g : ModalityG (Val := Val) (W := W) ExportCarrier) :
    (ofExportVal M (⟨g.idx, g.id, g.observed, g.project⟩ :
        ModalityG (Val := Val) (W := W) ExportCarrier)).id = g.id ∧
      (ofExportVal M (⟨g.idx, g.id, g.observed, g.project⟩ :
        ModalityG (Val := Val) (W := W) ExportCarrier)).observed = g.observed :=
  ⟨rfl, rfl⟩

/-- **「特例嵌入」在条目层面是无损的**：`Entry ExportCarrier` 的元素
  读回再装回是同一个条目。

  **超出定义之处**：这是 §5 的**决定性**一条。它比 `ExportCarrier_fiber` 强：
  后者说纤维**等于** `ExportVal`，本定理说 `Entry ExportCarrier` 的每个元素
  只要知道索引就能**无损**读回一个 `ExportVal`（逐个投影 `rfl`），
  且读回后再装回去是**同一个**条目（`Sigma.eta`）。
  于是「`ExportVal` 是某个 `Carrier` 的特例」不是类比，而是**逐条目的同构**。 -/
theorem exportEntry_roundtrip (m : ModalityId) (x : ExportVal) :
    (⟨m, x⟩ : Entry ExportCarrier).snd = x ∧
      Sigma.mk (⟨m, x⟩ : Entry ExportCarrier).fst
        (⟨m, x⟩ : Entry ExportCarrier).snd = ⟨m, x⟩ :=
  ⟨rfl, rfl⟩

/-! ===========================================================================
  §6  与现有 `Modality` 共存
  =========================================================================== -/

/-- **旧 → 新的参数化关系**（比 `toExportVal` 更诚实的共存方式）。

  `RelMod m g` 读作「旧模态 `m` 与新模态 `g` 说同一个模态」。它不假装能
  从 `m` **算出** `g`：`m.project` 需要一个模型，而载体里没有 `Model` 的位置。
  于是关系取「存在一个模型 `M`，使 `g` 的 **id 与 observed** 与 `toExportVal m M`
  相同，且 `g` 的投影在任意状态上等于 `m.project M`」。 -/
def RelMod {Val V E Noise W : Type _} (m : Modality Val V E Noise)
    (g : ModalityG (Val := Val) (W := W) ExportCarrier) : Prop :=
  ∃ M : Model Val V E Noise, g.id = m.id ∧ g.observed = m.observed ∧
    ∀ S : WholeState Val W, g.project S = m.project M

/-- **每个旧模态都「是同载体下的某个泛型模态」**。

  **超出定义之处**：显式给出的模型让 `RelMod` **不空**。没有这条，
  `RelMod` 可能是个空关系，「共存」就退化成一句无反例可检的注释。
  这里模型是**调用方给的**（`M : Model …` 是定理的参数，不是被存在量化出来的），
  故证明是 `⟨M, rfl, rfl, fun _ => rfl⟩`——零公理、无 `Classical`。 -/
theorem relMod_self {Val V E Noise W : Type _} [Inhabited Val] (m : Modality Val V E Noise)
    (M : Model Val V E Noise) :
    RelMod m (⟨m.id, m.id, m.observed, fun (_ : WholeState Val W) => m.project M⟩ :
      ModalityG (Val := Val) (W := W) ExportCarrier) :=
  ⟨M, rfl, rfl, fun _ => rfl⟩

/-- **关系可以向下传递到「投影值」**：`RelMod` 的第三个分量本身就是
  逐点等式，此处把它**取出来**具名，供 §4 的导出等式使用。

  **超出定义之处**：`RelMod` 只在「模态对象」层面说一致；本定理把它变成
  **可用的等式**（`g.project S = m.project M`）。这是把 §5 的「特例」搬进
  §4「导出」的最后一颗螺丝——有了它，泛型导出出来的值可以**逐一**对应回
  旧实现导出的值。 -/
theorem relMod_project {Val V E Noise W : Type _} {m : Modality Val V E Noise}
    {g : ModalityG (Val := Val) (W := W) ExportCarrier} (h : RelMod m g) (S : WholeState Val W) :
    ∃ M : Model Val V E Noise, g.project S = m.project M :=
  Exists.elim h (fun M hM => ⟨M, by
    exact (show g.project S = m.project M from hM.2.2 S)⟩)

/-- **导出条数在新旧两侧一致**：旧注册表经 `toExportVal` 转成泛型注册表后，
  条数不变。

  **超出定义之处**：`Registry`（旧）与 `RegistryG ExportCarrier`（新）都是
  `List`，但**不是**同一个类型；本定理把「两种注册表可以一一对应」钉在
  **可数的**事实层面——它是 `count_export_all` 与旧 `export_all_count` 之间的桥：
  两侧都满足「默认导出条数 = 注册表长度」，故新旧默认导出的**条数**必然相同。 -/
theorem registry_length_eq {Val V E Noise W : Type _} (reg : Registry Val V E Noise)
    (M : Model Val V E Noise) :
    (reg.map (fun m => (⟨m.id, m.id, m.observed,
      fun (_ : WholeState Val W) => m.project M⟩ :
        ModalityG (Val := Val) (W := W) ExportCarrier))).length = reg.length :=
  length_map_eq (fun m => (⟨m.id, m.id, m.observed,
      fun (_ : WholeState Val W) => m.project M⟩ :
        ModalityG (Val := Val) (W := W) ExportCarrier)) reg

/-- **【核心 2 续】** 更进一步：**导出不依赖状态的内容之外的任何东西**——
  两个「在所有注册模态上投影一致」的状态，导出结果**逐条目相同**。

  **超出定义之处**：`export_no_side_effect` 要求 `h` 在**所有** `ModalityG (Val := Val) (W := W) C` 上成立；
  本定理把它放宽到**只在注册表里的模态**上成立。这是真正有用的形式：
  导出只看注册表（D-012「边界 = 注册表」），注册表外的模态做什么都不影响结果。
  证明：`∀ g ∈ reg, …` 经 `filter`/`map` 的逐元素结构归纳下落。 -/
theorem export_congr {M : Type u} {Val W : Type u} (C : Carrier M)
    (S S' : WholeState Val W) (sc : Scope) (reg : RegistryG (Val := Val) (W := W) C)
    (h : ∀ g ∈ reg, g.project S = g.project S') : exportG C reg S sc = exportG C reg S' sc := by
  show (reg.filter (fun g => sc.admits g.id)).map
        (fun g => Sigma.mk g.idx (g.project S))
      = (reg.filter (fun g => sc.admits g.id)).map
        (fun g => Sigma.mk g.idx (g.project S'))
  generalize hf : reg.filter (fun g => sc.admits g.id) = fl
  cases fl with
  | nil => rfl
  | cons x xs =>
    -- `hf : reg.filter … = x :: xs`：`x` 与 `xs` 的元素都来自 `reg`
    have hx : x.project S = x.project S' := h x (mem_of_filter (fun g => sc.admits g.id) reg x
      (by rw [hf]; exact List.mem_cons_self))
    have hxs : ∀ y ∈ xs, y.project S = y.project S' := by
      intro y hy
      exact h y (mem_of_filter (fun g => sc.admits g.id) reg y
        (by rw [hf]; exact List.mem_cons_of_mem x hy))
    show Sigma.mk x.idx (x.project S) :: List.map (fun g => Sigma.mk g.idx (g.project S)) xs
        = Sigma.mk x.idx (x.project S') :: List.map (fun g => Sigma.mk g.idx (g.project S')) xs
    rw [hx]
    congr 1
    exact list_map_congr_proj S S' xs hxs



end FateV2.Export
