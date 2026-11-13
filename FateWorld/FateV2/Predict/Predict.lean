import FateWorld.FateV2.Model.Dynamics
import FateWorld.FateV2.Modeling.Construct

/-!
  # Predict · Predict —— 预测 = 把外生律推前

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F6-01（预测）、F6-04（下一步分布 xNextDist）、F4-19（`Pred`）
  - 依赖裁决：**D-009**（预测 = 在模型空间里演化）、**D-013**（一体化模型）、
              **D-014**（模型 = SCM）、**D-019**（不写死载体：`Noise` 是参数）
  - 改动：原文件空骨架。
  - 状态：已验证（`Demo/SyntheticRun` 端到端调用）

  ## 为什么不用 `Measure`

  D-019 说 `Noise` 是**参数**，`Modeling/SCM.Model` 的 `Noise` 字段就是这么留的。
  预测只需要一件事：**把律沿一个函数推前**（pushforward）。

  本文件因此把「推前」做成 `Noise` 上的一个**操作参数**（`PushFamily`），于是：

  * 取 `Noise = Measure E` 时它是 `Measure.map`（经典侧，`noncomputable`）
  * 取 `Noise = DiscLaw α`（合成数据用的离散律）时它是可计算的、`#eval` 能跑

  ⟹ **同一条 `predict` 定义在两套载体上都成立**，预测层不必钉死在测度上。

  ## 降级
  `PushFamily` 的目标类型 `Z` 是结构参数（固定为 `Real` 的实例 `discPushFamily`）。
  本批只需要实数投影（状态分量 / 观测 / 时间平均都是实数），
  故没做「任意 `Z` 的推前族」。已写进报告。

  ## T13 追加（逐行说明见 `_报告/T13-进度.md` §二）

  **已有声明的类型一个字没动**：`PushFamily.push : T E → (E → Z) → T U` 原样，
  `predict` / `predict_const` / `predict_congr` 的签名原样，
  `rawMap` / `rawMap_total` / `rawMap_length` / `discPushFamily` 的值原样。
  只**新增**了 §2.1 的两个声明：

  * `DiscLawWellFormed`（`def`）：`vals` 与 `wt` 等长——`DiscLaw` 的合法形状；
  * `discPushFamily_wf`（`theorem`）：`synthLaw` 满足它（= `synthLaw_length`）。

  为什么只加这两条：T13 的合并推前族 `discPushFamilyM` 需要 `pushMerge`
  （在 `Predict/PushMerge.lean` 里，而 `PushMerge` **import 本文件**），
  写在本文件会**成环**。故本文件只补「合法形状」这一件 T13 真正缺的既有事实，
  族本身放在新文件 `Predict/PushFamilyMerge.lean`（方案丙：结构不改、只换值）。

  ## T13 追加（2026-11-02，逐行登记见 `_报告/T13-进度.md` §二）

  **已有字段/参数的类型一个字没动**：`PushFamily.push` 仍是
  `T E → (E → Z) → T U`，`predict` / `predict_const` / `predict_congr` 的签名仍是原样，
  `rawMap` / `discPushFamily` 的值仍是原样。只**新增**了 §2.1/§2.2 的声明：

  * `RawPushFamily`（`abbrev`，旧名 `PushFamily` 的别名）+ `rawPushFamily`：
    把「不合并」这一特例**也**升成一个带 `DecidableEq` 槽的结构，
    这样合并版与不合并版可以**并排**陈述同一条守恒定理。
  * `DiscLawWellFormed` / `discPushFamily_wf`：`discPushFamily` 只对「表等长」的律
    是合法的推前（`rawMap` 逐条照抄权重），这一条把它钉住，供 T13 的前件使用。
  * `discPushFamilyM`：**合并同像权重**的推前族，`push` 就是 `PushMerge.pushMerge`。
    **旧名 `discPushFamily` 继续可用**（它是本族的单射特例，见
    `FateV2.Predict.PushFamilyMerge` 的 `discPushFamilyM_eq_discPushFamily`）。
  * `predictM`：用合并族预测。`predictM M eval project = predict M eval project discPushFamilyM`
    —— 即 `predict` **本身无需改一个字符**就能跑合并版（方案丙）。

  这样做的理由（方案丙 vs 甲/乙）：`push` 的字段类型里确实没有实例槽，
  但**实例不必进 `push`**——把 `DecidableEq Z` 挂在整个 `PushFamily` 值上，
  `push` 在结构体内部拿闭包捕获即可。于是
  「换掉 `discPushFamily`」= 换成另一个**值**，不是改结构，也不是并行两套语义。

  ## T23（2026-11-02）：**打破循环依赖，把合并实现下移**（作者裁决「甲」）

  ### 问题

  `discPushFamily` 的值是 `push := fun L f => rawMap L f`——**丢质量的旧版**。
  T4 证出 `rawMap` 在非单射时不合并同像权重（`rawMap_drops_mass`），
  T13 交付了正确的 `discPushFamilyM`（`Predict/PushFamilyMerge.lean`），
  T22 的 G14 又报了 4 处违规。**但 `predict` 的默认路径仍然是错的**：
  调用方要正确必须在手边显式写 `discPushFamilyM`，忘了就退回旧版。

  ### 障碍与解法

  ```text
  Predict.lean  ←——— PushMerge.lean     （PushMerge import Predict ⟹ 本文件不能用 pushMerge）
  ```

  **本专项选的方案：A —— 把 `pushMerge` 的核心实现下移进本文件。**

  * 下移的只有**定义**：`addAt` / `goN` / `pushMerge` / `eqb`。
    `keyOf` / `wtOf` / `sumN` / `pick` / `support` / `InjOn` 仍留在 `PushMerge.lean`
    （`pushMerge` 的定义体不碰它们，下游定理照旧解析）。
  * 本文件**不 import** `PushMerge`，也不 import Mathlib ⟹ 依赖图仍然无环（G11 不变）。
  * `PushMerge.lean` 里那 4 条 `def` 原样保留（其文件头已写明「不再定义」），
    42 条定理**一条没动**——它们引用的仍是同一命名空间下的同一个名字。

  ### 为什么是 A 而不是 B（本例实测决定）

  方案 B 要在本文件里另写一份合并实现。**写不出来**（除非复制 `addAt`/`goN`）：
  合并的累加器必须是 `List (β × Nat)` 且顺序必须是 `vals` 的顺序，才能同时满足
  ①「同像权重相加」②「一个像点至多一条」③「顺序 = 首次出现顺序」。
  任何只保留「像点 → 权重」映射的精简写法（例如只留 `List (Real × Nat)` 的
  累积器）都要做**判断「这个像点此前出现过没有」**——那正是 `addAt` 的定义。
  ⟹ B 的「精简版」与 `goN`/`addAt` **逐字同构**，只是换个名字：
  两套实现**立刻**分叉（`PushMerge` 的 42 条定理证的是 `goN`，新名字一条都用不上）。
  A 把「唯一权威实现」保留在**一个**位置，这才是 T22/G14 要的收敛。

  ### 改了什么

  * `discPushFamily` 的 `push` 从 `rawMap L f` 换成 `pushMerge f L`；
    为此该 `def` 变成 **`noncomputable`**（`Z = Real` 要 `Real.decidableEq`，
    它在 Lean 里是 `noncomputable` 实例——T13 已实测）。
  * `rawMap` / `rawMap_total` / `rawMap_length` **一个字没动**：
    `rawMap` 仍是「不合并」这一分支的显式实现，供对照与 `InjOn` 情形使用。
  * `predict` / `predict_const` / `predict_congr` 的**公开签名逐字未变**。

  ### 代价（如实登记）

  `discPushFamily` 变成 `noncomputable`：`discPushFamily.push` 不能再被 `#eval` 跑。
  这是「合并」本身的代价（要判 `Real` 相等），不是本专项的偷懒——
  同一件事在 T13 的 `discPushFamilyM` 上已经发生。

  ## 超出定义之处
  * `predict_const`：投影是常函数时，预测与「外生律的具体分布」无关——
    即**确定性演化的预测不凭空产生不确定性**。定义本身对 `project ∘ eval`
    是什么毫无要求；这条把它在一个重要情形钉死。
  * `predict_congr`：逐点相等的两个投影给出同一个预测。
-/

namespace FateV2.Predict

universe u

open FateV2.Modeling FateV2.Model

/-! ===========================================================================
  §1  推前族与预测
  =========================================================================== -/

/-- **推前族**：把载体族 `T` 上的律沿 `f : E → Z` 推成同族上的新律。

  三个类型参数各管一件事：

  * `E` —— 外生赋值（`T E` 就是 `Noise`）
  * `Z` —— 投影目标
  * `U` —— 新律的**取值类型**（`T U` 是推前结果）

  把 `U` 与 `Z` 分开，是因为载体族（如 `DiscLaw`）的取值类型与
  投影目标类型不一定同层/同类型。 -/
structure PushFamily (T : Type u → Type u) (E : Type u) (Z : Type u) (U : Type u) where
  /-- 推前 -/
  push : T E → (E → Z) → T U

/-- **预测**：把外生律沿 `project ∘ eval` 推前。

  形式完全对应 D-009 §四的 `Model_t → Measure Model_{t+1}`：
  这里的 `Z` 就是「下一步的模型（或它的一个投影）」。

  参数 `T` 是**载体族**：`Noise = T E`，推前结果 `T Z`。
  （把 `U` 取成 `Z` 就回到最常见的「同族同目标」情形。） -/
def predict {Val V E Z : Type u} {T : Type u → Type u}
    (M : Model Val V E (T E))
    (eval : E → WholeState Val V)
    (project : WholeState Val V → Z)
    (pf : PushFamily T E Z Z) : T Z :=
  pf.push M.P_U (fun e => project (eval e))

/-- **确定性投影 ⟹ 点质量**：若 `project ∘ eval` 恒等于 `z`，
  则预测与「外生律的具体分布」无关——它只是把常数 `z` 推过去。

  **超出定义之处**：`predict` 的定义对 `project ∘ eval` 是什么毫无要求；
  本定理说明当它是常函数时，预测**只**取决于那个常值和推前本身。
  这正是「确定性演化的预测不凭空产生不确定性」——
  D-009 要求「预测在模型空间里演化」，那么确定性演化就不该产生分布。 -/
theorem predict_const {Val V E Z : Type u} {T : Type u → Type u}
    (M : Model Val V E (T E)) (z : Z)
    (pf : PushFamily T E Z Z)
    (eval : E → WholeState Val V) (project : WholeState Val V → Z)
    (h : ∀ e, project (eval e) = z) :
    predict M eval project pf = pf.push M.P_U (fun _ => z) := by
  unfold predict
  congr 1
  funext e
  exact h e

/-- **预测对投影外延**：在两个投影逐点相等时，预测相等。

  **超出定义之处**：`predict` 吃的是**函数**，不是函数的等价类；
  本定理把「只关心逐点值」这一用法合法化——D-011 说模态是**推导器**，
  那么两个推导结果处处相同的推导器必须给出同一个预测。 -/
theorem predict_congr {Val V E Z : Type u} {T : Type u → Type u}
    (M : Model Val V E (T E)) (eval : E → WholeState Val V)
    {project project' : WholeState Val V → Z}
    (h : ∀ s, project s = project' s) (pf : PushFamily T E Z Z) :
    predict M eval project pf = predict M eval project' pf := by
  unfold predict
  congr 1
  funext e
  exact h (eval e)

/-! ===========================================================================
  §2  离散载体上的具体推前（可计算 —— `#eval` 能跑）
  =========================================================================== -/

/-- **离散律的推前**：沿 `f` 映取值，**权重原样保留**。

  为保持**可计算**与「与 `Nat` 权重相容」，同像权重**不合并**——
  于是 `total` 不变，与 demo 里「用权重和做分母」的用法相容。

  ⚠ **降级**：同像权重不合并。合并需要判定 `Real` 相等，
  在本工具链下会把整条链变成 `noncomputable`（`Real.decidableEq` 不可计算）。
  名字上标 `raw` 以示区别。 -/
def rawMap {α Z : Type} (L : DiscLaw α) (f : α → Z) : DiscLaw Z where
  vals := L.vals.map f
  wt   := L.wt

/-- 原始推前**保权重和**。

  **超出定义之处**：`rawMap` 的定义只换了 `vals`、原样保留 `wt`；
  定义本身没写「权重和不变」，本定理把它钉住——这是「推前仍是概率分布」
  的前提，也解释了为什么下游可以直接拿 `total` 当分母。 -/
theorem rawMap_total {α Z : Type} (L : DiscLaw α) (f : α → Z) :
    (rawMap L f).total = L.total := rfl

/-- 原始推前**保条数**。 -/
theorem rawMap_length {α Z : Type} (L : DiscLaw α) (f : α → Z) :
    (rawMap L f).vals.length = L.vals.length := by
  show (L.vals.map f).length = L.vals.length
  rw [List.length_map]

/-! ===========================================================================
  §2.2  T23：合并推前的核心实现（**下移**自 `Predict/PushMerge.lean`）

  `PushMerge.lean` import 本文件，故本文件不能用它里面的东西。
  打破环的办法是把**定义**搬到这里（作者裁决「甲」）：

  * 搬来：`keyOf` / `wtOf` / `eqb` / `addAt` / `goN` / `pushMerge`——
    `discPushFamily` 需要的最小闭包（`pushMerge` 的定义体**逐字**用到前五个）；
  * 留下：`sumN` / `pick` / `support` / `InjOn` 仍在 `PushMerge.lean`
    （`pushMerge` 的定义体不碰它们，搬过来只会扩大改动面）。

  **为什么闭包正好是这六个**：`pushMerge` 的定义体是
  `vals := keyOf (goN eqb f [] L.vals L.wt)`、`wt := wtOf (…)`；
  `goN` 的递归体只用到 `addAt`；`addAt` 只用 `List` 的模式匹配。
  于是闭包就是这六个，一个不多。

  **写法与 `PushMerge.lean` 逐字一致**（含 `mutual` 块与「单层 + 单层」模式），
  理由见该文件头「为什么手写遍历」：`List.map` / `List.foldr` 会让递归退化为
  well-founded，定义被标 `@[irreducible]`，`rfl` 失效而只能 `simp` ⟹ 带 `propext`。
  =========================================================================== -/

/-- 取像点表（对 `Prod` 取分量的结构递归——`List.map Prod.fst` 同样会退化，故手写）。 -/
def keyOf {β : Type} : List (β × Nat) → List β
  | []            => []
  | (a, _) :: tl  => a :: keyOf tl

/-- 取权重表（同上）。 -/
def wtOf {β : Type} : List (β × Nat) → List Nat
  | []            => []
  | (_, c) :: tl  => c :: wtOf tl

/-- 本文件统一用的判等（从 `DecidableEq β` 取 `Bool`）。

  **为什么不用 `==`**：`pushMerge` 的上下文里只有 `DecidableEq β`，没有 `BEq β`；
  判等必须**显式传进来**。 -/
def eqb {β : Type} [DecidableEq β] (a b : β) : Bool := decide (a = b)

mutual

  /-- **往累加器里记一笔**：像点 `b` 已在表里，就把权重加进去；否则在**末尾**追加一条。

    用 `beq : β → β → Bool` 而不是 `== : BEq`：见 `eqb` 的说明。 -/
  def addAt {β : Type} (beq : β → β → Bool) (b : β) (w : Nat) :
      List (β × Nat) → List (β × Nat)
    | []              => [(b, w)]
    | (a, c) :: rest  =>
      match beq a b with
      | true  => (a, c + w) :: rest
      | false => (a, c) :: addAt beq b w rest

  /-- **合并推前的主体**：对 `vals` 与 `wt` 逐位置走，把每一对 `(f x, w)`
    累加进累加器 `acc`。

    外层拆 `xs`、内层拆 `ws`（**不用并列模式**）：并列 `match` 会被编成两层嵌套，
    `unfold goN` 就够不着，所有证明只能退化成 `simp`（带 `propext`）。
    本写法的两条截断方程（`[]` / `ws = []`）都是结构递归，`rfl` 可展开、不带公理。 -/
  def goN {α β : Type} (beq : β → β → Bool) (f : α → β)
      (acc : List (β × Nat)) : List α → List Nat → List (β × Nat)
    | [],       _       => acc
    | x :: xs,  ws      =>
      match ws with
      | []       => acc
      | w :: ws' => goN beq f (addAt beq (f x) w acc) xs ws'

end

/-- **正确的推前：对每个像点，把所有原像点的权重求和。**

  `vals` 与 `wt` 逐位置配对，结果去掉重复像点，每个像点只留一条，
  权重是全体原像权重之和。

  **T23 的位置变更（重要）**：本条原先定义在 `Predict/PushMerge.lean`。
  因 `PushMerge.lean` import 本文件，`discPushFamily` 用不上它 ⟹ 现在**定义在**
  本文件，`PushMerge.lean` 只**引用**。**同一个名字、定义体一个字符没变**，
  故 `PushMerge.lean` 里那 42 条定理一条都不用改（它们解析到的还是这个名字）。 -/
def pushMerge {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α) : DiscLaw β where
  vals := keyOf (goN eqb f [] L.vals L.wt)
  wt   := wtOf (goN eqb f [] L.vals L.wt)

/-! ===========================================================================
  §2.3  T23：**默认推前族 = 合并版**（作者裁决「甲」）
  =========================================================================== -/

/-- **离散律上的推前族**：`E = SynthE` 推到 `Z = Real`。

  载体族 `T X = DiscLaw X`：外生律在 `DiscLaw SynthE` 上，
  推前之后落在 `DiscLaw Real` 上（这正是 `predict` 要的）。

  **T23 起 `push` 是 `pushMerge`，不再是 `rawMap`。**
  旧值 `rawMap` 在非单射时**丢质量**（T4 `rawMap_drops_mass`；
  T13 `discPushFamily_drops_mass` 给出具体数值），而 `predict` 的默认路径
  用的就是这个族 ⟹ 默认路径曾经是错的。现在默认就正确。

  **超出定义之处**：结构体字面量本身只说「`push` 调 `pushMerge`」，
  **没有**任何关于总质量的内容。守恒定理见 `PushMerge.lean` 的 §12
  （`discPushFamily_total`）——**为什么不住在本文件**：它的证明要引
  `pushMerge_total`，而那条定理住在 `PushMerge.lean`（import 本文件），
  本文件引用不到。结论本身对**任意** `f`、任意合法 `L` 成立，与具体实例无关。

  ⚠ `noncomputable`：`Z = Real` 要 `Real.decidableEq`，它在 Lean 里是
  `noncomputable` 实例。这是「合并」的固有代价（要判 `Real` 相等），
  不是本定义额外引入的——T13 的 `discPushFamilyM` 有同一代价。 -/
noncomputable def discPushFamily : PushFamily DiscLaw SynthE Real Real where
  push := fun L f => pushMerge f L

/-- **默认推前的 `push` 就是 `pushMerge`**（`rfl`）。

  **超出定义之处**：`discPushFamily` 是结构体字面量，「它的 `push` 等于 `pushMerge`」
  要展开 `PushFamily.push` 的投影才陈述得成等式。下游若要确认
  「默认族用的是 T4/T22 那份实现、没有偷偷换算法」，引本条即可。 -/
theorem discPushFamily_push (f : SynthE → Real) (L : DiscLaw SynthE) :
    discPushFamily.push L f = pushMerge f L := rfl

/-- **默认推前的取值表 = `pushMerge` 的取值表**（`rfl`）。

  **超出定义之处**：定义只写「`push` 是 `pushMerge`」，对 `vals` 字段一字未提；
  本条把它落成可直接 `rw` 的字段等式，供数值定理使用。 -/
theorem discPushFamily_vals (f : SynthE → Real) (L : DiscLaw SynthE) :
    (discPushFamily.push L f).vals = (pushMerge f L).vals := rfl

/-- **默认推前的权重表 = `pushMerge` 的权重表**（`rfl`）。 -/
theorem discPushFamily_wt (f : SynthE → Real) (L : DiscLaw SynthE) :
    (discPushFamily.push L f).wt = (pushMerge f L).wt := rfl

/-! **★ 默认推前保总质量**（结论登记，正式定理在 `PushMerge.lean` §12）。

  `L` 合法 ⟹ `discPushFamily.push L f` 的总质量 = `L.total`。

  **超出定义之处**：`discPushFamily` 的定义**只**说「`push` 调 `pushMerge`」，
  对总质量一个字没提。那条定理把它接回 `DiscLaw.total` 这个既有账本——
  即「默认路径的预测仍然是一个概率分布」。

  与旧版对照是要害：旧版 `rawMap` 的 `rawMap_total` 也成立，但**是 `rfl`**，
  原因是它**根本没合并**（靠重复项凑平）；那条不是 `rfl`。

  ⚠ **为什么定理不写在这里**：它的证明要引 `pushMerge_total`，而那条住在
  `PushMerge.lean`（import 本文件），**本文件引用不到**。本处只登记结论。 -/

/-! ===========================================================================
  §2.1  T13：`DiscLaw` 的合法形状（**只新增，不动上面任何一行**）
  =========================================================================== -/

/-- **`DiscLaw` 的合法形状**：取值表与权重表等长。

  **超出定义之处**：`DiscLaw` 的 `vals` 与 `wt` 是两个**互不相干**的表
  （`Modeling/Construct.lean` §2），结构上**没有**「第 `i` 条取值的权重是 `wt[i]`」。
  本谓词把「按位置对齐」这一口径钉成**可检验的命题**，
  好让 T13 的守恒定理有前件可写，而不是靠口头约定。 -/
def DiscLawWellFormed {α : Type} (L : DiscLaw α) : Prop :=
  L.vals.length = L.wt.length

/-- **`synthLaw` 合法**：`vals` 与 `wt` **都**是 8 条。

  **超出定义之处**：`rawMap` 的定义与 `rawMap_total` 对表长**毫无要求**；
  本条说明本项目的合成数据恰好落在合法形状里，
  于是「`discPushFamily` 的推前保总质量」在这份数据上**不是空话**。

  ⚠ **为什么不用 `Modeling.synthLaw_length`**：那条定理走 `List.length_flatMap`，
  实测带 **全套三公理**；而 `synthLaw` 的定义里两臂都是**具体列表字面量**，
  `rfl` 直接化到 `8 = 8`。于是本条**不借**那条引理。

  ⚠ **本条自己的 `#print axioms` 仍是三公理**——原因不是证明，而是**类型**：
  `synthLaw : DiscLaw SynthE`，而 `SynthE` 有 `Real` 字段。
  实测 `#print axioms (show (1:Real) = 1 from rfl)` 也是三公理。
  ⟹ 在 Type 版 Lean 里，**任何 `Real` 类型的定理在账面上都是三公理**。
  这不是本专项能修的（`Real` 的定义就是 `Quot`），已写进 `_报告/T13-进度.md` §五。 -/
theorem discPushFamily_wf : DiscLawWellFormed synthLaw := rfl

end FateV2.Predict
