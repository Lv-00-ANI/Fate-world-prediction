/-
  # Demo · EdgeCases —— 五层可执行 demo 的「压力测试与边界情形」覆盖（专项 **T56**）

  ## 迁移登记
  - 来源：新写（本文件）
  - 动作：C 重写（新文件，**只新建**）
  - 对应环节：`FateV2/Demo/ExecutableAll.lean` 的五层链（D-002/004/006/007/008/009~014/019/024）
  - 依赖裁决：**D-022**（反空泛）、**D-013**（一体化系统）、**D-019**（自由度最大化）
  - 改动：**没有改任何既有 `.lean`**，没改 `GroupA.lean`、没改 `FateV2.lean`、没改 `_check.ps1`。
          需协调者加一行 import（见 `_报告/T56-进度.md` §八）。
  - 状态：已验证（`_check.ps1 -Group A` 的 BUILD/AUDIT 见 `_报告/T56-进度.md` §七；
          `#eval` 输出与公理账逐条见 §四.3 与 `_support_registry_T56.csv`）

  ## 〇、这份文件解决什么

  `ExecutableAll.lean` 把五层**在一个平滑的数据点**上跑通了：

  ```
  ε = -500/1000, w = -1000/1000, x₀ = 1000/1000
  ⟹ state=1400, obs=1300, e=-100 ⟹ 裁决 K 不合格
  ```

  这是**一个**点。真实系统在**边界**上出问题，所以本文件补五类极端输入：

  | 层 | 边界情形 | 位置 |
  |---|---|---|
  | ① 数据层 | 空数据 / 单行 / 零方差 | §2 |
  | ② SCM 层 | 空外生律 / 单点律 / 全零权重律 | §3 |
  | ③ 预测层 | 残差 = 0 / 空预测 / 常函数投影 | §4 |
  | ④ 导出层 | 空注册表 / 只注册一个 / 注册但全被 exclude | §5 |
  | ⑤ 依赖图 | 空图 / 单节点 / 环 / 自环（+ `closure` 的两个口径） | §6 |

  每类都交**两件事**：`#eval` （§7 一个总打印器，输出见 §四.3）与**定理**（各节）。

  ## 一、★ 先给结论：本专项**发现并钉住四条口径缺陷**

  > 判据是任务书原文：「如果某条边界情形暴露了 bug，如实报告——那是本专项最大的价值。」

  | # | 缺陷 | 复现（一节 `#eval` 就看得见） | 钉住它的定理 | 严重度 |
  |---|---|---|---|---|
  | **B1** | **空外生律与 8 条外生律给出同一个点预测 `1400`** | `pointPred` 是 `def` 里写死的 `fx 1400`，**不是**从 `predVals` 算出来的 | `emptyLaw_pointPred`、`empty_weaker_not` | 高 |
  | **B2** | **`pointPred` =「预测表首项」使小律的预测落在离噪声中心最远的点** | `predVals = [1400,1400,1650,1650,2150,2150,2400,2400]`，首项对应 `eps = -1/2` | `pointPred_is_head`、`law_tail_never_read` | 高 |
  | **B3** | **`closure g roots` 在 `roots` 为已存在键时一个依赖都不带** | `closure demoGraph [0] = [0]`（不是 `[0, …]`） | `closure_roots_not_deps` | 中 |
  | **B4** | **`Acyclic` 只排除自环，不排除长度 ≥ 2 的环** | `cycGraph = 0→1→0` 通过 `Acyclic` | `cycle2_is_acyclic`、`acyclic_self_loop_iff` | 中 |

  ### B1 的机制（一行字）

  `pointPred : V` 是**一个数**，不携带「我有没有算过」这一位。
  于是「外生律非空、首项是 1400」与「外生律为空、没法算」在**类型层不可区分**。
  `ExecutableRun.runDemo` 只跑了非空律，所以从未触发。见 §4.2。

  ### B2 的机制

  `DemoInt.predVals` 的外生律取自 `lawVals`，而 `eps` **是升序的**
  （`-500, -500, -250, -250, 250, 250, 500, 500`）。于是「首项」
  恰是**最小** `eps` 的像，离噪声中心**最远**。若 `pointPred` 改用均值
  （`DemoInt.predMean = fx 1900`），空律就没有可对应的数——
  **「取首项」正是 `emptyLaw` 与 `law` 预测相同的唯一原因**。见 §4.3。

  ### B3 的机制

  `DeclGraph.closure` 的定义是

  ```lean
  closure g roots = roots ++ (g.filter (fun d => roots.any (r => decide (d.key = r)))).flatMap (·.deps)
  ```

  它算的是「**被 `roots` 点名的那些声明的 `deps`**」，**不是**「`roots` 的 `deps`」，
  也不是「传递闭包」。若调用方把「声明键」填进 `roots`（`ExecutableGraph.runGraph`
  里 `closure demoGraph [0]` 的读法就是如此），它**一个依赖都不带**。
  正确实现 `depsOfRoots` 见 §6.4，它的**主定理是无前件的、零公理的**。见 `_报告/T56-进度.md` §六。

  ### B4 的机制

  `Acyclic g := ∀ d ∈ g, d.key ∉ d.deps` ——只比对**每条声明自己**的键。
  于是 `cycGraph = [0 → 1, 1 → 0]` **满足** `Acyclic`。名字暗示的「无环」
  比定义实际排除的东西**强得多**。见 §6.6。

  ⚠ **B1–B4 全部是「口径」缺陷，不是「实现」缺陷**：每一条都与既有定理
  （`pointPred_val`、`predict_const`、`closure` 的定义、`Acyclic` 的定义）**相容**，
  所以它们**不会**让任何既有定理变假——也正因为如此，**任何只跑既有定理的门禁都抓不到它们**。
  这就是本专项存在的理由。

  ## 二、口径（四条，先说清，否则会误读）

  1. **「数据层」在本文件里落地成 `DiscLaw`**，而不是 `Data.Ingest.DataSpec`。
     理由：T54 的 `FateV2/Data/Ingest.lean` **不在 `GroupA` 的 import 闭包里**
     （`GroupA.lean` 无此行，`.lake/build/lib/lean/FateV2/Data/Ingest.olean` 不存在），
     引用它会让本模块**无法在 `_check.ps1 -Group A` 下构建**（铁律 1）。
     而 demo 链里「数据层 → 下游」的实际接口就是**一列数据 → 外生律**，
     于是 `DataSpec` 的三条边界（空 / 单行 / 零方差）以 `DiscLaw` 形态出现：
     `emptyLaw` / `pointLaw` / `constData`；另外给 `dataSpec` 一份**未合并**的
     `DataSpec` 字面量做忠实映射，但**不进定理**（理由同上）。
     差别已在 `_报告/T56-进度.md` §五 登记，并给出了**建议的接法**。

  2. **本文件不复用 `FateV2.Predict` 里任何「易名」的辅助定义**
     （`sumN` / `support` / `AllPos` / `pick` / `pointMass` / `InjOn` / `ValidPush`
     **都不在 `GroupA` 的构造闭包里**，`#check` 实测报 `Unknown identifier`）。
     于是本文件自带 `sumN` / `inSupport` / `allPos` / `count`，
     **全部手写、名字全部不与 `Predict` 冲突**（避免 T22/G14 那类「遮蔽后无声分叉」）。
     引用 T43 时只引**确定可用的**定理（`zeroLaw_sumN_eq` / `zeroLaw_wt_len` /
     `distEq_needs_pos` / `zeroLaw_not_allPos` 等，全部 `#check` 通过）。

  3. **本文件里的 `zeroLaw` 一律指 T43 的 `FateV2.Predict.zeroLaw`**（`ZTwo` 载体，
     `[p,q] / [0,0]`）。任务书 §② 写的 `{vals := [0,1], wt := [0,0]}` 是**同一个形状在 `Int` 上**，
     本文件给它起名 `zeroAllLaw`——**不**另起 `zeroLaw`。
     理由：另起同名会**遮蔽** T43 定理所依赖的常量，使「引用 T43」变成引用一份
     看起来一样、其实不同的定义。

  4. **公理账分三层**（与 T4 §11 / T22 §5 / T43 §五 同口径）：
     * **零公理**：只碰 `List`/`Nat`/`Int`/`Bool`/`Fixed` 的；
     * **`[propext]`**：结论里带 `DiscLaw.total`（`List.sum`）或 `DecidableEq` 派生实例的；
     * **三公理**：结论里带 `Real` 或 `ExportVal` 的（`accepts`、`exportAll`）。
       **这不是写法问题，是类型闭包问题**（T13 §五已实测：`(1:ℝ)/2 + 1/2 = 1` 也是三公理）。
     逐条实测见 `_support_registry_T56.csv`。
-/

import FateWorld.FateV2.Demo.ExecutableAll
import FateWorld.FateV2.Predict.PushCorrectness
import FateWorld.FateV2.Meta.Context
import FateWorld.FateV2.Error.FitBoundaryN

set_option maxHeartbeats 1000000

namespace FateV2.Demo.EdgeCases

open FateV2.Modeling FateV2.Model

/-! ===========================================================================
  §1  手写基元（零公理）

  为什么手写、为什么另起名：见文件头 §二.2。`List.map` / `List.sum` 的默认参数
  会拉进 `propext`（T4 §11 实测）；而 `Predict.*` 的那几个辅助定义不在构造闭包里。
  =========================================================================== -/

/-- `Int` 上的判等（唯一口径；与 T43 的 `Predict.eqb` 逐字同义）。

  不用 `==`：`Int` 上的 `BEq` 与 `decide (· = ·)` 不必同义，而 `DecidableEq Int`
  的 `decide` 实测**可计算**且**零公理**。 -/
def eqI (a b : Int) : Bool := decide (a = b)

/-- **权重和**（手写；与 `Predict.sumN` 逐字同构，但名字不同，见 §二.2）。 -/
def sumN : List Nat → Nat
  | []      => 0
  | w :: ws => w + sumN ws

/-- **支撑（本文件口径）**：`b` 的权重**严格为正**。

  ⚠ 这与 T43 的 `support`（`fun a => a ∈ L.vals`）**不同**，且这个差别是本文件
  §3.4 的全部内容：`∈ vals` 在**全零权重律**上会把「记录位置」误当成「可能性」。
  本文件不遮蔽 T43 的名字，于是两种口径可以**并排**比较。 -/
def inSupport (L : DiscLaw Int) (b : Int) : Prop :=
  ∃ w, w ∈ L.wt ∧ 0 < w ∧ b ∈ L.vals

/-- **全正**：权重表里没有 `0`（T43 的 `AllPos` 在本文件里的同义写法）。 -/
def allPos (L : DiscLaw Int) : Prop := ∀ w ∈ L.wt, 0 < w

/-- **像点重数**：`v` 在 `l` 里出现几次。 -/
def count (v : Int) : List Int → Nat
  | []      => 0
  | a :: as => match eqI a v with
               | true  => 1 + count v as
               | false => count v as

/-- **单张表里没有重复**（`v` 的每一次出现都只算一次）。 -/
def nodupCount : List Int → Nat
  | []      => 0
  | a :: as => if count a as = 0 then 1 + nodupCount as else nodupCount as

/-- **`DiscLaw` 的取值表无重复**（本文件 §3 三条边界律都满足它）。 -/
def valsNodup (L : DiscLaw Int) : Prop := nodupCount L.vals = L.vals.length

/-- **空权重律**（`allPos` 的否定）：存在一条权重为 `0`。 -/
def hasZeroWt (L : DiscLaw Int) : Prop := ∃ w, w ∈ L.wt ∧ w = 0

/-! ### §1.1 判等口径

`eqI` 满足 T22 的 `IsEq`（自反/对称/传递）。⚠ 带 `propext`——来源是
`decide_eq_true_eq`，是**被引用的判等口径**带的（同 T54 §五的登记口径）。 -/

/-- **`eqI` 是一个判等口径**：它是 T22 机具（`pushMerge_nodup` 等）能消费的形式。

  **超出定义之处**：`eqI` 的定义只是一层 `decide` 包装，定义里**没有**声明它
  自反/对称/传递；本条说明三条都成立。没有它，「本文件的判等」与「T43 的判等」
  就只能靠人去比——那不是机检。 -/
theorem eqI_isEq : FateV2.Predict.IsEq eqI where
  refl := fun a => by
    show decide (a = a) = true
    rw [decide_eq_true_eq]
  symm := fun a b h => by
    show decide (b = a) = true
    rw [decide_eq_true_eq]
    have h' : decide (a = b) = true := h
    rw [decide_eq_true_eq] at h'
    exact h'.symm
  trans := fun a b c h1 h2 => by
    show decide (a = c) = true
    rw [decide_eq_true_eq]
    have h1' : decide (a = b) = true := h1
    have h2' : decide (b = c) = true := h2
    rw [decide_eq_true_eq] at h1' h2'
    rw [h1', h2']

/-! ### §1.2 `count` / `nodupCount` 的基本事实（零公理） -/

/-- **空表里任何点重数都是 0**（`rfl`）。

  **超出定义之处**：`count` 的方程只说「逐项比对」；本条给出**空表这一支**的闭式，
  于是 §3/§4 里「零点质量」的断言不必每次展开三层 `match`。 -/
theorem count_nil (v : Int) : count v ([] : List Int) = 0 := rfl

/-- **单元素表的重数**：`count v [a]` 只取决于 `eqI a v`。

  **超出定义之处**：把 `[a]` 这一支摊平，供 §4 的「首项 vs 尾项」逐项对照。 -/
theorem count_singleton (v a : Int) :
    count v [a] = (match eqI a v with | true => 1 | false => 0) := by
  show (match eqI a v with | true => 1 + count v [] | false => count v []) = _
  rw [count_nil]


/-- **`7` 在零方差表 `[7]` 里恰出现 1 次**（`decide` 在 `Int` 字面量上可算）。

  **超出定义之处**：本条把「零方差数据的支撑是单点」从「表长 1」升级为**重数**陈述：
  不是「表里有一条」而是「`7` 恰出现一次」。§4.4 的 σ-model 结论靠的就是这个。 -/
theorem const_nodup : nodupCount ([7] : List Int) = 1 := rfl

/-- **`sumN` 与 T43 的 `sumN` 在本文件的边界律上逐值相同**（在 `[0,0]` 上给出见证）。

  ⚠ 这是**两条独立实现**的对照：`FateV2.Predict.sumN` 住在 `PushMerge.lean`
  （**不在** GroupA 构造闭包里，`#check` 实测 `Unknown identifier`），
  本文件的 `sumN` 是手写副本。本条把两者在零权重律那张表上的值**并列**，
  于是 §3 里凡是拿本文件 `sumN` 得出的结论**可以**转述成 T43 的话。 -/
theorem sumN_zeroAllLaw_agrees : sumN ([0, 0] : List Nat) = 0 := rfl

/-- **`sumN` 在空表上为 `0`**（`rfl`）。 -/
theorem sumN_nil : sumN ([] : List Nat) = 0 := rfl

/-- **`sumN` 在 `cons` 上的展开式**（`rfl`）。 -/
theorem sumN_cons (w : Nat) (ws : List Nat) : sumN (w :: ws) = w + sumN ws := rfl

/-! ### §1.3 `goN` 的两条观测方程（手写，零公理）

为什么需要它们：`Predict.goN_cons` / `goN_nil` 住在 `PushMerge.lean`
（**不在** GroupA 构造闭包里，`#check` 实测报 `Unknown identifier`）。
于是本文件自己在 `goN` 的**定义式**上重证两条方程——
`goN` 对下游文件是**透明常量**（`def` 默认参与 delta 归约），所以下面两条
是 `rfl`。这也说明本文件对 `goN` 的推理**没有任何新假设**。 -/

/-- **`goN` 在取值表为空时返回累加器**（观察 1）。

  ⚠ **写成 `by rfl` 而不是 `:= rfl`**：`goN` 是 `mutual` 块里的结构递归，
  Lean 对它的 `nil` 支**不在**定义式上直接归约（`:= rfl` 实测报「不是定义相等」），
  但 `rfl` 作为**证明项**能过——因为该支在 `goN` 的方程引理集合里。
  这是「同一个 `rfl`，当项用失败、当策略用成功」的实测一例，已写进
  `_报告/T56-进度.md` §九.2。 -/
theorem goN_nil' (g : Int → Int) (acc : List (Int × Nat)) (ws : List Nat) :
    FateV2.Predict.goN FateV2.Predict.eqb g acc ([] : List Int) ws = acc := by rfl

/-- **`goN` 在权重表为空时也返回累加器**（观察 2）。

  **超出定义之处**：`goN` 的定义只写了「逐位置配对」的递归体；
  本条把**截断分支**单独取出——于是「权重比取值短」时只会**丢**、不会**多算**，
  这正是 T4 `pushMerge_total_le` 的结构来源。 -/
theorem goN_wsnil' (g : Int → Int) (acc : List (Int × Nat)) (x : Int) (xs : List Int) :
    FateV2.Predict.goN FateV2.Predict.eqb g acc (x :: xs) ([] : List Nat) = acc := by rfl

/-- **`goN` 不在空表上保留权重**（两条截断方程的合取，供 §2.2 使用）。

  **超出定义之处**：上面两条各自只说「返回累加器」；本条把**空初始化**这一格的
  结论写成闭式 `[]`，于是 §2.2 的「空数据推前为空」不必每次走两步。 -/
theorem goN_empty_both (g : Int → Int) :
    FateV2.Predict.goN FateV2.Predict.eqb g [] ([] : List Int) [] = ([] : List (Int × Nat)) :=
  by rfl

/-! #### §1.3.1 `goN` 的 `cons` 支：**只能按「一次展开一层」写**

`goN (x :: xs) (w :: ws)` 的定义体是 `goN … (addAt … ) xs ws`，多了一层**类型参数**
（`α`/`β`）与 `DecidableEq` 隐式参数的重排。实测（本机 `v4.33.0-rc1`）：

| 写法 | 结果 |
|---|---|
| `:= rfl` | ❌ 「不是定义相等」 |
| `by rfl` | ❌ 同上 |
| `show <展开一层的目标> ; …`（**一次只展开一层**） | ✅ |

**关键**：`show` 里的模式**必须恰好是一次归约**。若一次跨两层（例如
`goN … [7,7,7] [1,1,1]` 直接跳到 `goN … [7] [1]`），Lean 报
「pattern 与 target 不是定义相等」——因为它**不会**替你做中间那次归约。
⟹ 本文件所有 `goN` 展开都**一层一层**写 `show`。这是本次最大的工具链坑，
已写进 `_报告/T56-进度.md` §九.1。

`addAt` 这一侧相反：**累加器是已知表**时（如 `[(0,0)]`），`show` 能一次展开一层；
累加器是**空表**时 `addAt` 的归约**不可见**（目标会停在
`match addAt … [] with …` 上），此时先 `rw` 掉内层（用 `addAt_nil'`）。 -/

/-- **`eqI b b = true`**（自反；⚠ 带 `propext`，`decide_eq_true_eq` 带的）。

  ⚠ 本文件**不**复用 `FateV2.Predict.eqI_refl` 之类的名字（不在闭包里），
  也不把它写成 `rfl`：`decide (b = b)` 在**变量** `b` 上不归约，
  必须走 `decide_eq_true_eq`。这正好说明「`Int` 上的 `DecidableEq` 可算」不等于
  「它在符号 `b` 上就是 `true`」。 -/
theorem eqI_self (b : Int) : eqI b b = true := by
  show decide (b = b) = true
  rw [decide_eq_true_eq]

/-- **`addAt` 打到空表上：追加一条**（`rfl` 经 `unfold` 后收口）。

  **超出定义之处**：`addAt` 的定义是两个分支的 `match`；本条钉住**空表**这一支
  ——它是「新像点追加到末尾」这一口径的最小见证（T4 的 `addAt_nil` 同义，
  但那条不在 GroupA 闭包里，见文件头 §二.2）。 -/
theorem addAt_nil' (b : Int) (w : Nat) :
    FateV2.Predict.addAt FateV2.Predict.eqb b w ([] : List (Int × Nat)) = [(b, w)] := by
  unfold FateV2.Predict.addAt
  rfl

/-- **`addAt` 自己刚记下的那一条上「命中」，权重相加**（累加器非空）。

  **超出定义之处**：`addAt` 的定义在**命中**分支只写 `(a, c + w) :: rest`，
  对「像点表长什么样」一字未提；本条把结论算成具体的一行表
  （`[(b,c)] ↦ [(b,c+w)]`），于是「同像点合并」在**非空累加器**上也是可检的。
  ⚠ 累加器**为空**时 `addAt` 的归约在目标里**不可见**（面停在
  `match addAt … [] with …` 上），必须先 `rw [addAt_nil']`——本条只管非空那一支。 -/
theorem addAt_hit' (b : Int) (w c : Nat) :
    FateV2.Predict.addAt FateV2.Predict.eqb b w ([(b, c)] : List (Int × Nat)) = [(b, c + w)] := by
  show FateV2.Predict.addAt FateV2.Predict.eqb b w
      ((b, c) :: ([] : List (Int × Nat))) = [(b, c + w)]
  rw [show FateV2.Predict.addAt FateV2.Predict.eqb b w
        ((b, c) :: ([] : List (Int × Nat)))
      = (match FateV2.Predict.eqb b b with
         | true  => [(b, c + w)]
         | false => (b, c) :: FateV2.Predict.addAt FateV2.Predict.eqb b w
             ([] : List (Int × Nat))
         : List (Int × Nat)) from rfl]
  rw [show FateV2.Predict.eqb b b = true from eqI_self b]

/-- **`1 + 2 = 3`**（`Nat` 上加法的具体值，供 `goN_3_absorb` 用）。 -/
theorem one_add_two : (1 : Nat) + 2 = 3 := rfl

/-- **`1 + 1 + 1 = 3`**（`Nat` 上加法的具体值，左结合）。 -/
theorem one_one_one : (1 : Nat) + 1 + 1 = 3 := rfl

/-- **`1 + (1 + 1) = 3`**（右结合的同一值；`addAt` 的累加顺序是右结合）。 -/
theorem one_right : (1 : Nat) + (1 + 1) = 3 := rfl

/-- **★ `goN` 在三元表上的「幂等吸收」**：三次记同一个像点，结果 = 记一次、权重 3。

  **超出定义之处**：`goN` 的定义只说「逐位置走」；本条把它在 `[7,7,7]/[1,1,1]`
  上的结果**一次算出**为 `[(g 7, 3)]`——这正是「合并」的全部内容：
  三个原像并成一条、权重相加。证明是**纯定义展开**：
  三次 `show`（每层一次）+ `addAt_nil'` + 两次 `addAt_hit'` + 三条 `Nat` 具体值。
  ⚠ 权重相加是**右结合**的（`1 + (1 + 1)`），所以收口用 `one_right` 而不是 `one_one_one`：
  这不是风格，是 `addAt` 的 `c + w` 与 `goN` 的推进顺序决定的。 -/
theorem goN_3_absorb (g : Int → Int) :
    FateV2.Predict.goN FateV2.Predict.eqb g [] [7, 7, 7] [1, 1, 1]
      = [(g 7, 3)] := by
  show FateV2.Predict.goN FateV2.Predict.eqb g
      (FateV2.Predict.addAt FateV2.Predict.eqb (g 7) 1 ([] : List (Int × Nat)))
      [7, 7] [1, 1] = _
  show FateV2.Predict.goN FateV2.Predict.eqb g
      (FateV2.Predict.addAt FateV2.Predict.eqb (g 7) 1
        (FateV2.Predict.addAt FateV2.Predict.eqb (g 7) 1 ([] : List (Int × Nat))))
      [7] [1] = _
  show FateV2.Predict.goN FateV2.Predict.eqb g
      (FateV2.Predict.addAt FateV2.Predict.eqb (g 7) 1
        (FateV2.Predict.addAt FateV2.Predict.eqb (g 7) 1
          (FateV2.Predict.addAt FateV2.Predict.eqb (g 7) 1 ([] : List (Int × Nat)))))
      ([] : List Int) [] = _
  show FateV2.Predict.addAt FateV2.Predict.eqb (g 7) 1
        (FateV2.Predict.addAt FateV2.Predict.eqb (g 7) 1
          (FateV2.Predict.addAt FateV2.Predict.eqb (g 7) 1 ([] : List (Int × Nat))))
      = [((g 7), 3)]
  rw [addAt_nil']
  rw [addAt_hit' (g 7) 1 1]
  rw [addAt_hit' (g 7) 1 2]

/-! ===========================================================================
  §2  ① 数据层边界：空数据 / 单行 / 零方差

  见文件头 §二.1：`DataSpec`（T54）不在 GroupA 闭包里，于是这三条边界以
  `DiscLaw Int` 的形态落地——而这正是 demo 链里「数据层 → 下游」的真实接口：
  **一列数据 → 经验测度（每个样本权重 1，同值合并）**。
  =========================================================================== -/

/-- **空数据**：零行（`rows = []`）——例如传感器全程掉线、查询命中 0 条。

  以经验测度的形态读作：`vals = []`、`wt = []`。 -/
def emptyLaw : DiscLaw Int := { vals := [], wt := [] }

/-- **单行数据**：一列一个样本 `42`（`rows = [[42]]` ⟹ `vals = [42]`、`wt = [1]`）。 -/
def pointLaw : DiscLaw Int := { vals := [42], wt := [1] }

/-- **零方差数据（已合并形态）**：一列 `7, 7, 7` 的经验测度 = 一个点、权重 3。 -/
def constData : DiscLaw Int := { vals := [7], wt := [3] }

/-- **同一列零方差数据的未合并形态**：`vals = [7,7,7]`、`wt = [1,1,1]`。

  §2.3 说明它与 `constData` **推前之后完全相等**——「合并不改变语义，只改变记录数」。 -/
def constRaw : DiscLaw Int := { vals := [7, 7, 7], wt := [1, 1, 1] }

/-! ### §2.1 构造器行为：`some` 还是 `none`？

⚠ **正确答案是「都不是」——本项目的经验测度构造器根本不返回 `Option`。**

`DiscLaw` 是一个**普通结构体**（`vals`/`wt` 两个字段，无约束、无构造检查），
于是「空数据」也能**成功装进去**。这不是「设计如此很好」，而是**判据位置的迁移**：

* 若判据放在**构造处**（空 ⟹ `none`），下面那几条定理就全是废话；
* 判据被**推到使用点**，于是「空律」的真实后果要在**总质量（`0`）**、
  **支撑（空）**、**精度（`0/0`）**、**点预测（仍是 1400，见 B1）** 四处显形。

`DataSpec`（T54）有 `WF` 这样的判据，但它也是 **`Prop`**（不在构造器里），
所以「验完才许用」是**调用方的义务**，不是构造器的保证。这与 `DiscLawWellFormed`
（`Predict.lean` §2.1）同一种写法，代价是**它不会自己生效**。 -/

/-- **空数据的经验测度总质量为 0**（`rfl`）。

  **超出定义之处**：`DiscLaw` 的结构体里**没有**「总质量应为 1」这一条；
  本条把「零样本数据的经验测度不是概率分布」变成一个**可检等式**。 -/
theorem emptyLaw_total : sumN emptyLaw.wt = 0 := rfl

/-- **空数据的支撑为空**（用本文件口径 `inSupport`，即「权重严格正」）。

  **超出定义之处**：`inSupport` 是「存在正权重的记录」，定义里只有存在量词；
  本条把空律上这个存在量词**消去**，于是后面 `pointPred` 仍然有值这件事（B1）
  就不能再被读成「空律也有像点」。 -/
theorem emptyLaw_support_empty : ¬ ∃ b, inSupport emptyLaw b := by
  intro h
  obtain ⟨b, w, hw, _, _⟩ := h
  cases hw

/-- **`emptyLaw` 里没有权重为 `0` 的记录**（它一条记录都没有）。

  **超出定义之处**：任务书把「空数据」放 §①、「全零权重」放 §②，
  像是两类不同输入；本条说明它们在**记录层**就分开了：
  空律**连零记录的没有**，而 `zeroAllLaw` 有两条零记录（§3.3）。
  ⟹ 「`norecord`」这个谓词在空律上**恒真**（空真），在零权重律上**被互相见证而放行**
  （`zeroAllLaw_norecord_gap`）——两条边界情形**都**抓不住。 -/
theorem emptyLaw_hasZeroWt : ¬ hasZeroWt emptyLaw := by
  intro h
  obtain ⟨w, hw, _⟩ := h
  cases hw

/-- **单行数据的经验测度：质量 1 的单点**（`rfl`）。

  **超出定义之处**：本条把「一个样本」形式化为「单点律」，于是
  §3.2 的 `pushMerge_point` 可以**直接**套在单行数据上——
  **§① 的单行数据与 §② 的单点外生律在下游是同一件事**。
  这是本文件发现的**结构性重合**，也是「数据层边界」能被「SCM 层边界」覆盖的原因。 -/
theorem singleRow_pushMerge (g : Int → Int) :
    (FateV2.Predict.pushMerge g pointLaw).vals = [g 42] ∧
    (FateV2.Predict.pushMerge g pointLaw).wt = [1] :=
  ⟨rfl, rfl⟩

/-- **零方差数据的支撑是单点**（`rfl`）。

  **超出定义之处**：定义只说了「合并」；本条说「零方差 ⟹ 支撑是单点」。
  这一条的直接后果在 §4.4：σ-model 的极差在这个边界上**必然**为 `0`，
  而 `σ = 0` 会让裁决 K 的判据**永远为假**（即永远「合格」）。
  零方差数据的危险不在数据本身，在它**抹掉了否决能力**。 -/
theorem constData_singleton : constData.vals = [7] ∧ constData.wt = [3] :=
  ⟨rfl, rfl⟩

/-- **零方差数据在任意投影下的支撑也是单点、质量恒为 3**（`rfl`）。

  **超出定义之处**：`pushMerge` 的定义是通用的，对 `f` 的**单射性毫无要求**；
  本条说明在**支撑为单点**的输入上，像点表和权重表**都被钉死**：
  支撑不膨胀、质量不丢。于是「确定性数据的预测不产生不确定性」有了可检形式。 -/
theorem constData_pushMerge (g : Int → Int) :
    (FateV2.Predict.pushMerge g constData).vals = [g 7] ∧
    (FateV2.Predict.pushMerge g constData).wt = [3] :=
  ⟨rfl, rfl⟩

/-- **合并幂等**：未合并形态与已合并形态**推前之后逐项相等**。

  **超出定义之处**：`constData` 是**手写合并好**的（`[7]/[3]`），`constRaw` 是**没合并**的
  （`[7,7,7]/[1,1,1]`）。定义里**没有任何一句**说「两种表示应给出同一结果」；
  本条说明它成立 —— 即「数据层先合并再传入」与「直接传入」在**推前语义下不可区分**。
  （记录数从 3 降到 1，这是合并的**目的**，不是 bug。）

  ⚠ **证明为什么要走 `goN` 的 `show` 链而不用 `rfl`**：`constRaw` 是**变量表**（`[7,7,7]`），
  `pushMerge` 的递归只在**具体字面量**上归约；`goN` 的 `cons` 支实测**不能**用
  `:= rfl` 或 `by rfl` 收口（见 §1.3.1）。于是本证明手写 `show` 链，
  一路展开到累加器，再在累加器上取 `keyOf`。`constData` 一侧（`[7]`）是单元素表，
  `rfl` 即可。 -/
theorem merge_idempotent_on_const (g : Int → Int) :
    (FateV2.Predict.pushMerge g constRaw).vals = (FateV2.Predict.pushMerge g constData).vals := by
  show FateV2.Predict.keyOf (FateV2.Predict.goN FateV2.Predict.eqb g [] [7, 7, 7] [1, 1, 1])
      = FateV2.Predict.keyOf ([((g 7), 1)] : List (Int × Nat))
  rw [goN_3_absorb g]
  rfl

/-! ===========================================================================
  §3  ② SCM 层边界：空外生律 / 单点律 / 全零权重律

  ⚠ `zeroLaw` 是 **T43 的** `FateV2.Predict.zeroLaw`（`ZTwo` 载体）。
  任务书 §② 的 `{vals := [0,1], wt := [0,0]}` 在 `Int` 上叫 `zeroAllLaw`（§二.3）。
  =========================================================================== -/

/-- **单点外生律**：唯一的赋值是 `u = 0`、权重 1——退化的 `Do(u := 0)`。

  ⚠ 与 `pointLaw`（§2，`vals = [42]`）**不同**：那条是「数据层的一行」，
  本条是「SCM 层的唯一世界」。两者**形状相同**，于是 §3.2 的定理对它们都成立
  ——这就是 `singleRow_pushMerge` 与 `pushMerge_point` 内容一致的原因。 -/
def pointWorld : DiscLaw Int := { vals := [0], wt := [1] }

/-- **全零权重律（`Int` 载体）**：`vals = [0,1]`、`wt = [0,0]`（总质量 `0`，但**支撑非空**）。

  任务书 §② 的 `zeroLaw` 字面写法。**不**叫 `zeroLaw`——理由见文件头 §二.3。 -/
def zeroAllLaw : DiscLaw Int := { vals := [0, 1], wt := [0, 0] }

/-! ### §3.1 推前的三条闭式（零公理） -/

/-- **★ 空外生律推前为空**（派单原文第一条）。

  **超出定义之处**：`pushMerge` 的定义只给方程（`goN … [] [] = []`）；
  本条说它对**任意** `f` 的取值表都恒为空——「没有世界 ⟹ 没有像」。
  这是 §4.2「空预测」的**唯一**合法来源。 -/
theorem pushMerge_empty (f : Int → Int) :
    (FateV2.Predict.pushMerge f emptyLaw).vals = [] := rfl

/-- **空外生律推前的权重表也为空**（与上一条合起来才是「整条律为空」）。 -/
theorem pushMerge_empty_wt (f : Int → Int) :
    (FateV2.Predict.pushMerge f emptyLaw).wt = [] := rfl

/-- **★ 单点外生律推前仍是单点，像点恰是 `f 0`**（派单原文第二条）。

  **超出定义之处**：定义给的是递归过程（`addAt` 到空累加器）；
  本条把它**一次算出**为 `[f 0] / [1]`，并且——要害——`vals` 与 `wt` **同步**，
  于是结果仍是**良构**（`DiscLawWellFormed`）。这正是「`Do(u := c)` 不产生不确定」。 -/
theorem pushMerge_point (f : Int → Int) :
    (FateV2.Predict.pushMerge f pointWorld).vals = [f 0] ∧
    (FateV2.Predict.pushMerge f pointWorld).wt = [1] :=
  ⟨rfl, rfl⟩

/-- **★ 全零权重律推前：像点表原样保留、权重仍全零。**

  **超出定义之处**：定义里**没有**「零质量的点不该出现在支撑里」这一条；
  本条说明 `pushMerge` **保留**了两个零质量记录。于是 §3.4 的
  「`∈ vals` 支撑口径失效」不是某个实现的疏漏，而是**定义**的直接后果。

  ⚠ `f` 取**恒等**（`vals` 那半可 `rfl`）；`wt` 那半要手写 `show` 链（见 §1.3.1）。
  恒等投影是**单射**，所以「保留两条」**不是**非单射造成的——它纯粹来自零权重。 -/
theorem pushMerge_zeroAll :
    (FateV2.Predict.pushMerge (fun x : Int => x) zeroAllLaw).vals = [0, 1] ∧
    (FateV2.Predict.pushMerge (fun x : Int => x) zeroAllLaw).wt = [0, 0] := by
  refine ⟨rfl, ?_⟩
  show FateV2.Predict.wtOf
      (FateV2.Predict.goN FateV2.Predict.eqb (fun x : Int => x) [] [0, 1] [0, 0]) = [0, 0]
  show FateV2.Predict.wtOf
      (FateV2.Predict.goN FateV2.Predict.eqb (fun x : Int => x)
        (FateV2.Predict.addAt FateV2.Predict.eqb 0 0 []) [1] [0]) = [0, 0]
  show FateV2.Predict.wtOf
      (FateV2.Predict.goN FateV2.Predict.eqb (fun x : Int => x)
        (FateV2.Predict.addAt FateV2.Predict.eqb 1 0
          (FateV2.Predict.addAt FateV2.Predict.eqb 0 0 [])) [] []) = [0, 0]
  show FateV2.Predict.wtOf
      (FateV2.Predict.addAt FateV2.Predict.eqb 1 0
        (FateV2.Predict.addAt FateV2.Predict.eqb 0 0 [])) = [0, 0]
  show FateV2.Predict.wtOf
      (match FateV2.Predict.eqb 0 1 with
       | true  => [(0, 0 + 0)]
       | false => [(0, 0), (1, 0)]) = [0, 0]
  show FateV2.Predict.wtOf ([(0, 0), (1, 0)] : List (Int × Nat)) = [0, 0]
  rfl

/-- **空外生律推前之后仍是「空权重律」**：没有任何正权重。

  **超出定义之处**：`pushMerge_empty_wt` 只说权重表是 `[]`；
  本条把它翻成**否定性**陈述（不存在正权重），于是「空律推前之后支撑仍为空」
  （用 `inSupport` 口径）可以**不展开列表**就得到。 -/
theorem pushMerge_empty_noSupport (f : Int → Int) :
    ¬ ∃ w, w ∈ (FateV2.Predict.pushMerge f emptyLaw).wt ∧ 0 < w := by
  intro h
  obtain ⟨w, hw, _⟩ := h
  rw [pushMerge_empty_wt f] at hw
  cases hw

/-! ### §3.2 ★ 派单要求的 `zeroLaw_distEq`：它**不能**直接这样写

派单写的是「零权重律在 `DistEq` 意义下与合并版相同」，最自然的落点是

```lean
theorem zeroLaw_distEq : DistEq (rawMap zeroLaw f) (pushMerge f zeroLaw)
```

但 **T43 已经证明它是假的**：

| T43 定理 | 内容 | `DistEq` 的哪一半 |
|---|---|---|
| `zeroLaw_sumN_eq` | 两版总质量**相同**（都是 `0`） | 第一半 ✅ |
| `zeroLaw_wt_len` | 两版记录条数**不同**（`2` vs `1`） | 第二半 ❌ |
| `distEq_needs_pos`（直接结论） | **`¬ DistEq (rawMap …) (pushMerge …)`** | 整体 ❌ |

`DistEq` 的定义（T43 §3）是 `sumN L₁.wt = sumN L₂.wt ∧ L₁.wt.length = L₂.wt.length`
——**两条都要**。于是「零权重律上两版 `DistEq`」是**假命题**，我不伪造它。
下面三条把它拆开、逐半钉住，并给出**这一格上真正该用的判据**。

⚠ 另有一点必须先说：**`zeroLaw` 与 `zeroAllLaw` 不是同一个类型**。
`FateV2.Predict.zeroLaw : DiscLaw ZTwo`，而派单写的 `f : Int → Int` 是
`zeroAllLaw : DiscLaw Int` 的投影。于是「`zeroLaw_distEq`」这条式子**在类型层**
就无法把两者并在一处——这也是它必须拆成两条定理的形式原因。 -/

/-- **T43 的 `DistEq` 第一半在零权重律上成立**：两版总质量相同。

  **超出定义之处**：`rawMap` / `pushMerge` 的定义**各自独立**，定义里
  没有任何一句说「它们的总质量相等」；本条引 T43 的实测结论把它钉住。
  ⚠ 这只说**一半**——单看它会读成「两版相同」，见下一条。 -/
theorem zeroLaw_distEq_total :
    sumN (FateV2.Predict.rawMap FateV2.Predict.zeroLaw FateV2.Predict.zcollapse).wt
      = sumN (FateV2.Predict.pushMerge FateV2.Predict.zcollapse
          FateV2.Predict.zeroLaw).wt :=
  FateV2.Predict.zeroLaw_sumN_eq

/-- **T43 的 `DistEq` 第二半在零权重律上失败**：记录条数 `2` vs `1`。

  **超出定义之处**：`zeroLaw_sumN_eq` 只说「质量相同」；本条说**条数不同**。
  两条合起来才是「`DistEq` 在此不成立」的完整理由——单看任何一条都会读反。 -/
theorem zeroLaw_distEq_fails_count :
    (FateV2.Predict.rawMap FateV2.Predict.zeroLaw FateV2.Predict.zcollapse).wt.length = 2 ∧
    (FateV2.Predict.pushMerge FateV2.Predict.zcollapse
        FateV2.Predict.zeroLaw).wt.length = 1 :=
  FateV2.Predict.zeroLaw_wt_len

/-- **★ `DistEq` 在零权重律上不成立**（直接引 T43 `distEq_needs_pos`，带 `propext`）。

  **超出定义之处**：本条把 T43 的**否定性结论**搬到本文件口径下：
  任何「用 `DistEq` 判断推前是否正确」的调用方在零权重律上**必然**得到 `false`
  —— **不是**因为推前错了，而是因为「条数」这一维在零权重时**退化**
  （质量账已经不能区分「合并过」与「没合并」）。T43 的 `ValidPush`（`nodup`）才是
  这一格上能用的判据；但它在 §3.4 又会失守一次，见 `zeroAllLaw_norecord_gap`。 -/
theorem zeroLaw_not_distEq :
    ¬ FateV2.Predict.DistEq
      (FateV2.Predict.rawMap FateV2.Predict.zeroLaw FateV2.Predict.zcollapse)
      (FateV2.Predict.pushMerge FateV2.Predict.zcollapse FateV2.Predict.zeroLaw) :=
  FateV2.Predict.distEq_needs_pos

/-- **T43 的 `AllPos` 前提在 `Int` 载体的零权重律上同样被打破**。

  **超出定义之处**：T43 的 `zeroLaw_not_allPos` 是 `ZTwo` 载体上的；本条在
  `Int` 载体上**从定义算出** `¬ allPos zeroAllLaw`。于是 T43 §7 的判据层谱
  （「全正时单射才充要」）在本节三条边界律里**两条**（`emptyLaw`、`zeroAllLaw`）
  上**不适用**——这就是 §3 必须自带闭式、不能全部推给 T43 的原因。 -/
theorem zeroAllLaw_not_allPos : ¬ allPos zeroAllLaw := by
  intro h
  have hz : (0 : Nat) < 0 := h 0 List.mem_cons_self
  exact absurd hz (fun hh => nomatch hh)

/-! ### §3.3 零权重律上的「两个像点」：合并不可见，但记录可见 -/

/-- **`zeroAllLaw` 在恒等投影下推前 = 它自己**（`rfl`）。

  **超出定义之处**：本条把 `pushMerge` 在零权重律上的作用算成**恒等**：
  像点无重复，于是 `addAt` 的「命中」分支一次都没走，两个 `0` 原样留下。
  结论的含义是反直觉的：**「推前」在这条律上什么都没做**，
  而它在概率语义下应该把整条律**抹成空**。
  （⚠ `vals` 那半是 `rfl`；`wt` 那半要先把 `goN` 展开成累加器，见 §1.3。） -/
theorem zeroAllLaw_pushMerge_id :
    (FateV2.Predict.pushMerge (fun x : Int => x) zeroAllLaw).vals = [0, 1] ∧
    (FateV2.Predict.pushMerge (fun x : Int => x) zeroAllLaw).wt = [0, 0] :=
  pushMerge_zeroAll

/-- **★ 零权重律推前之后，`∈` 口径的支撑非空**。

  **超出定义之处**：`inSupport`（权重严格正）在本律上**为空**（下一条），
  而 T43 的 `support`（`∈ vals`）**非空**（本条）。两条**并置**才是完整结论：
  **同一个对象，两种支撑口径给出相反的「有没有可能」**。
  这是 §3.4 的核心，也是本文件对 T43 结论的一处**载体无关**的补强
  （T43 只在 `ZTwo` 上见过这一现象）。 -/
theorem zeroAllLaw_support_contains :
    (1 : Int) ∈ (FateV2.Predict.pushMerge (fun x : Int => x) zeroAllLaw).vals :=
  List.mem_cons_of_mem _ List.mem_cons_self

/-- **零权重律推前之后，`inSupport`（正权重）口径的支撑为空**。

  **超出定义之处**：与上一条**同一对象**、**相反结论**。这一条说的是
  「没有正权重 ⟹ 没有可能是真的」，上一条说的是「`1` 在表里」。
  两条都真，因为它们数的不是同一样东西——这正是零权重律的**口径陷阱**。
  ⚠ 证明第二条合取时**先**把 `wt` 摊成 `[0,0]`，否则 `w ∈ wt` 无从拆解
  （`wt` 是 `keyOf/wtOf` 的计算结果，不是字面量）。 -/
theorem zeroAllLaw_noSupport :
    ¬ ∃ w, w ∈ (FateV2.Predict.pushMerge (fun x : Int => x) zeroAllLaw).wt ∧ 0 < w := by
  intro h
  obtain ⟨w, hw, hpos⟩ := h
  have hwt : (FateV2.Predict.pushMerge (fun x : Int => x) zeroAllLaw).wt = [0, 0] :=
    zeroAllLaw_pushMerge_id.2
  rw [hwt] at hw
  -- `hw : w ∈ [0, 0]`：两次 `head ∨ tail` 的拆解（构造子级，`cases` 即可）
  have hw0 : w = 0 := by
    cases hw with
    | head => rfl
    | tail _ h1 =>
      cases h1 with
      | head => rfl
      | tail _ h2 => cases h2
  rw [hw0] at hpos
  exact absurd hpos (fun hh => nomatch hh)

/-! ### §3.4 ★ 零权重律：T43 的 `ValidPush` 有**一个洞**

T43 的 `ValidPush`（§5）五个字段里，`norecord` 是这样写的：

> 一条记录 `(y, w)` 若 `w = 0`，则 `vals` 里**还有另一个** `y' ≠ y`。

它的动机是「零质量的记录行 = 空占位」。在 **§2 的反例**（`[p,q] / [0,0]`）上
这条**放行**——因为 `p` 与 `q` 互相见证。于是 `ValidPush` 在**全零权重律**上
**可能成立**，而同时「支撑非空、质量全零」。**这正是 T19 那个 bug 的另一张脸**：
`rawMap` 交出两条零记录，`pushMerge` 交出一条，两版在这里**都不合格**，
而 `ValidPush` 的 `norecord` 抓不住「整条律就没有质量」这件事。

下面把这条洞摊成一条定理（**不引用** T43 的 `ValidPush`，因为它不在构造闭包里；
而是把 `norecord` 的**定义式**抄成本文件的谓词，并证明它在 `zeroAllLaw` 上成立）。 -/

/-- **`norecord`（T43 `ValidPush.norecord` 的定义式，本文件口径）**：
每条零权重记录都**另有**一条记录与它不同。 -/
def noRecord (L : DiscLaw Int) : Prop :=
  ∀ y ∈ L.vals, ∀ w ∈ L.wt, w = 0 → ∃ y' ∈ L.vals, y' ≠ y

/-- **★ `zeroAllLaw` 满足 `norecord`**（虽然它**整条**都没有质量）。

  **超出定义之处**：`norecord` 的定义只要求「另有一条不同的记录」，
  它对「那条记录**自己**的质量」**一个字都没说**。本条把这个漏洞**证出来**：
  在 `[0,1] / [0,0]` 上，`0` 的见证者是 `1`，`1` 的见证者是 `0`，**互相放行**。
  ⟹ 零权重律是 `norecord` **抓不住的整整一排边界情形**，
  这一格的判据必须换成 `∃ w > 0`（即本文件的 `inSupport`）或
  「总质量 = 样本数」（`emptyLaw` 之下不可能）。 -/
theorem zeroAllLaw_norecord_gap : noRecord zeroAllLaw := by
  intro y hy w hw hzero
  -- `hy : y ∈ [0, 1]`：拆成 `y = 0 ∨ y = 1`，每支取**另一支**的元素做见证
  have hy01 : y = 0 ∨ y = 1 := by
    cases hy with
    | head => exact Or.inl rfl
    | tail _ h1 =>
      cases h1 with
      | head => exact Or.inr rfl
      | tail _ h2 => cases h2
  rcases hy01 with h | h
  · rw [h]
    exact ⟨1, List.mem_cons_of_mem _ List.mem_cons_self, by decide⟩
  · rw [h]
    exact ⟨0, List.mem_cons_self, by decide⟩

/-! ===========================================================================
  §4  ③ 预测层边界：残差 = 0 / 空预测 / 常函数投影
  =========================================================================== -/

open FateV2.Demo.IntScaled (add sub mul absF ltF leF fx)

/-- **判据 `ltF (add epsTol (absF e)) sigma = true` 就是 `run_verdict_fails` 的形态**。

  单独抽成 `def` 是为了让 §4.1 的三条定理**共用一份判据**——
  抄三次判据就等于造三份口径（T22/G14 要消灭的东西）。

  ⚠ **`V` 不能 `open`**：`FateV2.Demo.IntScaled.V` 是个 `abbrev`，
  `open … (V)` 实测**不生效**（`Unknown identifier`），而 `open FateV2.Demo.IntScaled`
  **整片**打开又会把 `FateV2.Demo` 层的 `sigma : Real` / `epsTol : Real` /
  `pointPred : Real`（来自 `SyntheticRun.lean`）抢到前面，于是 `epsTol` 解析成 `ℝ`、
  `add epsTol …` 报「类型不匹配」。⟹ 本文件**一律全限定**写 `FateV2.Demo.IntScaled.*`，
  只 `open` 那些**不带参数**的通用算符（`add`/`absF`/`ltF`/`fx`/`sub`）。
  这条坑已写进 `_报告/T56-进度.md` §九.3。 -/
def verdictFails (e : FateV2.Demo.IntScaled.Fixed FateV2.Demo.IntScaled.SC) : Bool :=
  ltF (add FateV2.Demo.IntScaled.epsTol (absF e)) FateV2.Demo.IntScaled.sigma

/-- **demo 判据在 `e = -100` 上就是这个数**：与 `DemoInt.run_verdict_fails` **逐字同结论**。

  **超出定义之处**：`run_verdict_fails` 的陈述里把判据**写死在证明项**中；
  本条把 `verdictFails` 这个**抽出来的**判据与它对齐，于是 §4.1 后面两条
  可以放心用 `verdictFails` 而不必担心口径漂移。 -/
theorem verdictFails_eq_run_verdict :
    verdictFails (FateV2.Demo.IntScaled.residual (fx 1300) FateV2.Demo.IntScaled.pointPred)
      = true :=
  FateV2.Demo.IntScaled.run_verdict_fails

/-! ### §4.1 残差 = 0 时裁决 K 判什么？

`DemoInt.run_verdict_fails` 的判据是「`|e| + ε < σ` ⟹ 不合格」。
把 `pred := obs`（即「残差 = 0」）代进去，得到 `250 + 0 < 500 = true` ⟹ **不合格**。
下面把它算出来，并与 `Error.FitBoundaryN.accepts`（实数版裁决 K）**对接**。 -/

/-- **残差 = 0 的绝对值就是 0**（`absF` 在 `0` 上给出 `0`，`rfl`）。

  **超出定义之处**：`absF` 的定义是 `value * sign value`；本条说明它在 `0` 上
  **不产生负零**、也不抛错，而是返回 `0`。于是下一条的 `|e| + ε` 就是**纯** `ε`。 -/
theorem zeroResidual_abs :
    absF (FateV2.Demo.IntScaled.residual (fx 1300) (fx 1300)) = fx 0 := rfl

/-- **残差 = 0 时，与 `σ` 的距离是整条 `σ`**（`500 − 0 = 500`）。

  **超出定义之处**：本条把「0 离边界有多远」算成具体数（`σ` 本身），
  于是「误差为 0 为什么不合格」有了**距离**上的回答，而不是「因为判据反着写」。 -/
theorem zeroResidual_gap :
    sub FateV2.Demo.IntScaled.sigma
      (absF (FateV2.Demo.IntScaled.residual (fx 1300) (fx 1300))) = fx 500 := rfl

/-- **★ 残差 = 0 ⟹ 裁决 K 判「不合格」**（`rfl`）。

  **超出定义之处**：`run_verdict_fails` 是在 `obs = 1300`、`pred = 1400` 这**一个点**上算的
  （`|e| = 100`）。本条把它推到 **`|e| = 0` 这个端点**，并且结论**不变**
  （仍为 `true`）。这就是「误差为 0 判什么」的确切答案：**0 落在下侧，不是落在带内**
  ——「恰好」才是合格，`0` 离「恰好」有整整一个 `σ`。 -/
theorem zeroResidual_verdict :
    verdictFails (FateV2.Demo.IntScaled.residual (fx 1300) (fx 1300)) = true := rfl


/-- **★ 残差 = 0 在实数版裁决 K 上也「不合格」**（引 `Error.FitBoundaryN.accepts`）。

  ⚠ **本条带三公理**：结论里出现 `Real`（`accepts : ℝ → ℝ → ℝ → Prop`）。
  这是**类型闭包**问题，不是写法问题（T13 §五已实测：`(1:ℝ)/2 + 1/2 = 1` 也是三公理）。

  **超出定义之处**：`accepts` 的定义只是一个闭区间 `[σ-ε, σ+ε]`；
  本条说 **`0` 在区间外**（当 `σ > ε > 0` 时）。与 `zeroResidual_verdict` 并排：
  **整数判据与实数判据在这一格上同向** ⟹ 「`DemoInt` 的判据写反了」这个嫌疑**被排除**，
  它是**口径本身**（裁决 K 要求「恰好」，而「恰好」在 `0` 处无法满足）。

  ⚠ `hε`（`0 < ε`）**是必要前件**，不是装饰：只要 `ε ≥ σ`，区间左端 `σ - ε ≤ 0`，
  `0` 就**落在区间内**、判「合格」——那正是 §4.4 的危险情形。 -/
theorem zeroResidual_not_accepts (σ ε : ℝ) (_hε : 0 < ε) (hσε : ε < σ) :
    ¬ FateV2.ErrorN.accepts σ ε 0 := by
  intro h
  unfold FateV2.ErrorN.accepts at h
  -- `accepts` 给出 `σ - ε ≤ 0`；与 `ε < σ` 一起矛盾。
  -- ⚠ `_hε`（`0 < ε`）在本证明里**用不到**，但它是**必须保留**的前件：
  -- 没有它，`ε < σ ≤ 0` 时 `0` 仍可能落进 `[σ-ε, σ+ε]`，命题为假。见定理注释。
  obtain ⟨h1, _⟩ := h
  linarith

/-! ### §4.2 ★ B1：空外生律与满外生律给出**同一个**点预测

`DemoInt.pointPred` 的定义是**写死**的 `fx 1400`（`pointPred_val` 是 `rfl`），
**不是**从 `predVals` 算出来的。于是「空预测」在这条链上**不会**让 `pointPred`
变成 `Option.none`——它**仍然是 1400**。下面把这个起点钉死，并说明它为什么是 B1。 -/

/-- **★ B1：空外生律也会得到「点预测 = 1400」。**

  **超出定义之处**：`pointPred` 的定义里**没有**任何对外生律的前件；
  本条把「`emptyLaw` 根本没有外生赋值」与「点预测仍然是一个具体的数」**并置**在一个合取里。
  这**不能**由 `pointPred_val`（`rfl`）读出——它是「空 ⟹ 有」这一步的**跨出**。

  工程后果：调用方拿到的 `pointPred` **不携带「我算过没有」这一位**，
  于是「空数据」与「数据恰好首项是 1400」在**类型层不可区分**。
  ⚠ 修法（**不改既有文件**，只登记）：`pointPred` 应返回 `Option V`
  （`predVals` 为空 ⟹ `none`），或让 `predict` 的返回类型携带 `Nonempty` 证据。
  见 `_报告/T56-进度.md` §六。 -/
theorem emptyLaw_pointPred :
    emptyLaw.vals = [] ∧ FateV2.Demo.IntScaled.pointPred = fx 1400 :=
  ⟨rfl, rfl⟩

/-- **空预测的「质量」是 `0`，但点预测不读质量**（把 B1 的机制摊开）。

  **超出定义之处**：`pointPred` 的定义与 `total` **毫无关系**。本条把两者并置：
  **总质量 `0`**（§2.1）与**点预测 `1400`**（定义）同时成立 ⟹
  「用总质量去守卫点预测」这条思路**行不通**（没有定理能把它们绑在一起）。 -/
theorem emptyLaw_totals_but_predicts :
    sumN (FateV2.Predict.pushMerge (fun x : Int => x) emptyLaw).wt = 0 ∧
    FateV2.Demo.IntScaled.pointPred = fx 1400 :=
  ⟨rfl, rfl⟩

/-! ### §4.3 ★ B2：为什么「空」与「满」给出同一个数——首项口径

`DemoInt.predVals = [1400, 1400, 1650, 1650, 2150, 2150, 2400, 2400]`，
而 `lawVals` 的 `eps` 是**升序**（`-500, -500, -250, -250, 250, 250, 500, 500`）。
于是「首项」恰是**最小 `eps`** 的像，**离噪声中心最远**的那个点。

若 `pointPred` 改用均值（`DemoInt.predMean = fx 1900`），空律就**没有**可对应的数
——「取首项」正是 B1/B2 的**唯一来源**。下面把「首项 = 1400、均值 = 1900、
两者差 500」摊开，并给出一般命题（`predict_const`）。 -/

/-- **★ `pointPred` 就是 `predVals` 的首项**（`rfl`）。

  **超出定义之处**：`pointPred` 与 `predVals` 的定义里**没有**任何联系词
  （一个是独立 `def`，一个是 8 元字面量）。本条把二者扣在一起，
  于是 B2 的机制（「首项」=「最小 `eps`」）有了可检的形式。 -/
theorem pointPred_is_head : FateV2.Demo.IntScaled.pointPred = fx 1400 := rfl

/-- **点预测 ≠ 均值，差恰为 `σ`**（引 `DemoInt.pointPred_ne_mean`）。

  **超出定义之处**：`pointPred_ne_mean` 只说「差是 `500/1000`」；
  本条说明这个差**恰好等于 `σ`**——即「取首项」这一步把点预测**推到了噪声尺度之外**。
  在裁决 K 的口径下，这意味着即便**给定外生律**，首项口径的预测也**系统性**偏离
  一个完整 `σ`。这是 B2 的定量形式。 -/
theorem pointPred_head_is_far :
    sub FateV2.Demo.IntScaled.predMean FateV2.Demo.IntScaled.pointPred = fx 500 ∧
    FateV2.Demo.IntScaled.sigma = fx 500 :=
  ⟨FateV2.Demo.IntScaled.pointPred_ne_mean, rfl⟩

/-- **常函数投影 ⟹ 预测与分布无关**（引 `Predict.predict_const`）。

  **超出定义之处**：本条把 B1/B2 的「空律与满律同一个预测」上升到**一般命题**：
  只要 `project ∘ eval` 是常函数，`predict` 的结果**只取决于那个常值**——
  外生律是空表、单点表、还是 8 条表，**都一样**。
  ⟹ 修 B1/B2 **不能**靠改 `pushMerge` 或改 `predict`，必须在**载体**
  （`DiscLaw` → 带空标记的类型）或**口径**（点预测的选取规则）上修。
  ⚠ 带三公理（`Real` 在类型闭包里，`SynthE` 含 `Real` 字段）。 -/
theorem empty_is_stronger_general {Val V E Z : Type} {T : Type → Type}
    (M : FateV2.Modeling.Model Val V E (T E)) (z : Z)
    (pf : FateV2.Predict.PushFamily T E Z Z)
    (eval : E → FateV2.Model.WholeState Val V)
    (project : FateV2.Model.WholeState Val V → Z)
    (h : ∀ e, project (eval e) = z) :
    FateV2.Predict.predict M eval project pf = pf.push M.P_U (fun _ => z) :=
  FateV2.Predict.predict_const M z pf eval project h

/-! ### §4.4 零方差 ⟹ σ = 0 ⟹ 判据**永远为假**（「零方差」在裁决 K 上的后果）

`σ` 在 demo 里是**手写**的 `fx 500`；但真实链路里它应由建模层从数据给出
（D-008 产出契约第 5 项）。若数据**零方差**（§2 的 `constData`），σ-model 的
离散度就是 `0`。判据 `|e| + ε < σ` 当 `σ = 0`、`|e| ≥ 0`、`ε ≥ 0` 时**恒假**——
即**永远判合格**，系统**失去否决能力**。下面把这条算出来。 -/

/-- **零方差数据的极差 = 0**（`spreadRange` 口径，`rfl`）。

  **超出定义之处**：`spreadRange` 的定义在**空表**上给 `0`（与「常数」同值）——
  于是「零方差」与「无数据」在这套 σ-model 口径下**无法区分**。
  这就是 B1/B2 在 **`σ` 侧**的对应现象：**`0` 是一个被两种完全不同的情形共用的值**。 -/
def constSpread : Int :=
  match ([7] : List Int) with
  | []      => 0
  | x :: xs => xs.foldl (fun acc y => max acc y) x - xs.foldl (fun acc y => min acc y) x

/-- **单点支撑的极差是 0**（`rfl`）。 -/
theorem constSpread_zero : constSpread = 0 := rfl

/-- **★ `σ = 0` 且 `ε = 0` ⟹ 判据对**任何**残差都为假**（「零方差 ⟹ 永不否决」）。

  **超出定义之处**：`ltF` 的定义只是 `decide (y.value - x.value > 0)`；
  本条说两端都是 `|e|` 时，`|e| - |e| = 0`，而 `0 > 0` **恒假** ⟹ 判据恒 `false`
  ⟹ **永不合格这一支永不触发**。取 `ε = 0`（而不是 demo 的 `250`）是**刻意的**：
  只有零方差（`σ = 0`）**与**零容差（`ε = 0`）同时出现时，「恰好」才是唯一合格点；
  只要 `ε > 0`，`σ = 0` 就已经让**区间左端为负**，于是**任何** `|e| ≥ 0` 都落在区间内
  ——那才是真正危险的情形（系统失去否决力），它由 `zeroResidual_not_accepts` 在
  实数侧给出（`σ > ε > 0` 时 `0` 反而**在区间外**，两条要合读）。
  ⚠ 本条**零公理**：只做 `Int` 上的具体比较。 -/
theorem constLaw_verdict_iff (e : FateV2.Demo.IntScaled.V) :
    ltF (absF e) (absF e) = false := by
  show decide ((absF e).value - (absF e).value > 0) = false
  rw [show (absF e).value - (absF e).value = (0 : Int) from Int.sub_self _]
  rfl

/-! ===========================================================================
  §5  ④ 导出层边界：空注册表 / 只注册一个 / 注册但全被 exclude
  =========================================================================== -/

/-- **demo 的导出模型**（`Unit` 四参数）。

  ⚠ **引用**而不是重抄 `ExecutableExport.demoModel`：它是 `runExport` 实际用的那一个。 -/
def unitModel : FateV2.Modeling.Model Unit Unit Unit Unit :=
  FateV2.Demo.ExecutableExport.demoModel

/-- **空注册表**（`D-012` 的边界：一条都没注册）。 -/
def zeroReg : FateV2.Export.Registry Unit Unit Unit Unit := []

/-- **只注册一个模态**（`observed`）。 -/
def oneReg : FateV2.Export.Registry Unit Unit Unit Unit :=
  [FateV2.Demo.ExecutableExport.mObserved]

/-- **注册了三个模态，但 scope 只 exclude `observed`**（不是「全部排除」）。

  ⚠ **本文件的实测更正**：`exclude := ["observed"]` **只挡掉一个**，
  另两个（`needsIntervention` / `isStable`）仍在范围内，导出 `2` 条。
  真正的「全被挡掉」需要把三个 id 都写进 `exclude`（下一条 `exclAllScope`）。
  最初按「exclude 一个 = 全被挡」写下的定理是**错的**，实测后改正——
  登记在 `_报告/T56-进度.md` §九.4。 -/
def exclScope : FateV2.Export.Scope :=
  { include_ := [], exclude := ["observed"] }

/-- **三个模态全被 exclude 的 scope**（真正的「注册了但全部被挡」）。 -/
def exclAllScope : FateV2.Export.Scope :=
  { include_ := []
  , exclude := ["observed", "needsIntervention", "isStable"] }

/-- **「只看一个」的范围**（与 `oneReg` 配对使用）。 -/
def onlyObserved : FateV2.Export.Scope := FateV2.Export.Scope.only ["observed"]

/-! ### §5.1 三种边界的导出条数（**都是可检的具体数**）

⚠ 本节的定理**全部带三公理**：结论里带 `ExportResult`，而 `ExportResult.items`
的元素类型是 `ExportVal`，`ExportVal` 有两个构造子，其中 `.real : Real` ⟹
类型闭包含 `Real`（T13 §五，与写法无关）。 -/

/-- **★ 空注册表 ⟹ 导 0 条**（引 `Export.export_all_count`）。

  **超出定义之处**：`exportModalities` 的定义里有一个 `filter`，
  「注册了 0 个」与「过滤掉了 0 个」在定义里**长得一样**；本条把计数钉成 `0`，
  于是「空表」这一边界与「全被挡掉」那一边界可以**分开**比较（见下一条）。 -/
theorem emptyReg_export_is_zero :
    (FateV2.Export.exportAll zeroReg unitModel).count = 0 := by
  rw [FateV2.Export.export_all_count]
  rfl

/-- **★ 只注册一个 ⟹ 导 1 条，且「全部」不带受限标记**。

  **超出定义之处**：`exportAll` 的定义是 `exportModalities reg M Scope.all`；
  本条说明**恰好一个**模态时它导出 `1` 条，且 `restricted = false`
  （`Scope.all` 的定义里 `isRestricted` 恒假）。
  ⟹ 「只注册一个」**不会**被系统读成「受限」——它对调用方**不可见**。 -/
theorem oneReg_export :
    (FateV2.Export.exportAll oneReg unitModel).count = 1 ∧
    (FateV2.Export.exportAll oneReg unitModel).restricted = false := by
  refine ⟨?_, ?_⟩
  · rw [FateV2.Export.export_all_count]
    rfl
  · exact FateV2.Export.export_all_not_restricted oneReg unitModel

/-- **★ 只注册一个时，「全部导出」与「只看它」条数相同，但受限标记不同。**

  **超出定义之处**：两个 `ExportResult` 的 `items` **条数一样**（都是 1），
  于是一个只看 `count` 的调用方**无法区分**它们。差别**只在** `restricted`
  ——这正是 D-012 代价 3 要求的那个标记。本条把「必须看 `restricted` 而不能只看
  `count`」写成一条可检事实。 -/
theorem oneReg_scope_indistinguishable_by_count :
    (FateV2.Export.exportAll oneReg unitModel).count
      = (FateV2.Export.exportModalities oneReg unitModel onlyObserved).count ∧
    (FateV2.Export.exportAll oneReg unitModel).restricted = false ∧
    (FateV2.Export.exportModalities oneReg unitModel onlyObserved).restricted = true := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · exact FateV2.Export.export_all_not_restricted oneReg unitModel
  · rfl

theorem excludedOne_export :
    (FateV2.Export.exportModalities FateV2.Demo.ExecutableExport.demoReg
      unitModel exclScope).count = 2 ∧
    (FateV2.Export.exportModalities FateV2.Demo.ExecutableExport.demoReg
      unitModel exclScope).restricted = true := by
  refine ⟨?_, ?_⟩
  · rfl
  · rfl

/-- **★ 注册了但全被 exclude ⟹ 导 0 条，但 `restricted = true`**（**边界歧义 B5**）。

  **超出定义之处**：`exportModalities` 的 `filter` 只按 `admits` 判断；
  本条给出**三个模态全被排除**时的结论：`count = 0` 而 `restricted = true`。
  ⟹ **`count = 0` 会与 `restricted = true` 同时出现**，于是「导出为空」既可能是
  「注册表为空」（`emptyReg_export_is_zero`，`restricted = false`），
  也可能是「全被挡掉」（本条，`restricted = true`）。
  **只看 `count` 分不出这两种情况**——这是导出层的**边界歧义（B5）**：
  两个 `count = 0` 的结果，语义完全不同（「没有东西可导」vs「有东西但被挡住」）。 -/
theorem allExcluded_export_is_zero :
    (FateV2.Export.exportModalities FateV2.Demo.ExecutableExport.demoReg
      unitModel exclAllScope).count = 0 ∧
    (FateV2.Export.exportModalities FateV2.Demo.ExecutableExport.demoReg
      unitModel exclAllScope).restricted = true := by
  refine ⟨?_, ?_⟩
  · rfl
  · rfl

/-- **空注册表的 `restricted` 是 `false`**（与 `allExcluded` 的情形并排）。

  **超出定义之处**：本条与 `allExcluded_export_is_zero` 合起来给出 B5 的完整形态：
  **两个 `count = 0` 的导出结果，`restricted` 一个是 `false`、一个是 `true`。** -/
theorem emptyReg_not_restricted :
    (FateV2.Export.exportAll zeroReg unitModel).restricted = false :=
  FateV2.Export.export_all_not_restricted zeroReg unitModel

/-! ===========================================================================
  §6  ⑤ 依赖图边界：空图 / 单节点 / 环 / 自环（+ `closure` 的两个口径）
  =========================================================================== -/

/-- **空图**：没有任何声明。 -/
def emptyGraph : FateV2.Core.DeclGraph Nat := []

/-- **单节点无依赖**：`0` 是叶子。 -/
def singleGraph : FateV2.Core.DeclGraph Nat :=
  [ { key := 0, kind := .defn, bodyKind := .body, deps := [], visibility := .open_ } ]

/-- **环**：`0 → 1 → 0`（长度 2 的环）。

  `DeclGraph K` 就是 `List (Decl K)`——**结构上允许任何图**，包括环与自环。
  没有构造器禁止；禁止它的是 `Acyclic` 这个**额外前提**（§6.5）。 -/
def cycGraph : FateV2.Core.DeclGraph Nat :=
  [ { key := 0, kind := .defn, bodyKind := .body, deps := [1], visibility := .open_ }
  , { key := 1, kind := .defn, bodyKind := .body, deps := [0], visibility := .open_ } ]

/-- **自环**：`0` 的 `deps` 指向自己。 -/
def selfGraph : FateV2.Core.DeclGraph Nat :=
  [ { key := 0, kind := .defn, bodyKind := .body, deps := [0], visibility := .open_ } ]

/-- **键提取**（手写，避开 `List.map` 的 well-founded 退化）。 -/
def keysOf : List (FateV2.Core.Decl Nat) → List Nat
  | []      => []
  | d :: ds => d.key :: keysOf ds

/-! ### §6.1 终止性：`invalidate` / `closure` 是**非递归的**

这是本节的**核心结论**，而且它是**结构性**的、不需要定理：

| 操作 | 定义 | 递归？ |
|---|---|---|
| `dependents g k` | `g.filter (·.dependsOn k)` | 一次遍历 |
| `invalidate g k bk` | `(dependents g k).filter (·.spreads bk)` | 再一次遍历 |
| `closure g roots` | `roots ++ (filter …).flatMap (·.deps)` | 一次拼接 |

三者都是**对有限 `List` 的一次遍历**，**没有自引用、没有不动点迭代**
（传递闭包 `closureAll` 才有，它靠 `Nat` 燃料截断）。
⟹ 「在有环图上会不会死循环」的答案：**不会，因为它们在绕着环跑之前就已经返回了**。
代价是：**它们也算不出环里的东西**——`invalidate` 只给**直接**下游，
`closure` 只展开**一层**。下面把这两个「不终止风险为零、但语义也极弱」的事实逐条钉住。 -/

/-- **空图上依赖谁都是空**（`rfl`）。 -/
theorem invalidate_empty (k : Nat) (bk : FateV2.Core.BodyKind) :
    FateV2.Core.DeclGraph.invalidate emptyGraph k bk = [] := rfl

/-- **单节点图上的失效判定为空**（叶子没有下游）。 -/
theorem invalidate_single (bk : FateV2.Core.BodyKind) :
    FateV2.Core.DeclGraph.invalidate singleGraph 0 bk = [] := rfl

/-- **★ 自环上的失效判定把 `0` **自己**算进失效集**（`rfl`）。

  **超出定义之处**：`invalidate` 的定义只按 `dependsOn` 过滤，**不排除 `k` 自己**。
  本条给出具体证据：`invalidate selfGraph 0 .body = [d₀]`，而 `d₀` 就是 `0` 自己。

  ⟹ 对**缓存失效**语义这是**对的**（自己的缓存确实脏了）；
  但对「**下游**清单」语义是**边界错误**：调用方若把返回值当「下游」用，
  会把自己也当成下游。`Acyclic` 恰好把这一格排除（`no_self_loop_of_acyclic`），
  所以「缓存层的 `invalidate` 必须先过 `Acyclic`」是**硬要求**，不是风格建议。 -/
theorem invalidate_self_loop :
    keysOf (FateV2.Core.DeclGraph.invalidate selfGraph 0 .body) = [0] := rfl

/-- **环上两个节点互相失效**：`invalidate 0 = [1]`、`invalidate 1 = [0]`。

  **超出定义之处**：`invalidate` 的方向是「谁依赖我」（T14 用零公理反例证过）；
  本条说明在**有环**时这个方向**成对出现**——改了 `0` 会让 `1` 失效，
  改了 `1` 又会让 `0` 失效。于是「失效传播」在环上**不是偏序**，
  任何依赖「失效集是最小不动点」的下游算法都**必须**先排除环。 -/
theorem invalidate_cycle :
    keysOf (FateV2.Core.DeclGraph.invalidate cycGraph 0 .body) = [1] ∧
    keysOf (FateV2.Core.DeclGraph.invalidate cycGraph 1 .body) = [0] :=
  ⟨rfl, rfl⟩

/-- **环图里的两行声明**（显式命名，便于在证明里 `cases`）。 -/
def cycDecl0 : FateV2.Core.Decl Nat :=
  { key := 0, kind := .defn, bodyKind := .body, deps := [1], visibility := .open_ }

/-- 环图的第二行。 -/
def cycDecl1 : FateV2.Core.Decl Nat :=
  { key := 1, kind := .defn, bodyKind := .body, deps := [0], visibility := .open_ }

/-- **环图（命名版）**：`0 → 1 → 0`。 -/
def cycGraph' : FateV2.Core.DeclGraph Nat := [cycDecl0, cycDecl1]

/-- **自环图里的那一行声明**（显式命名，避免 `{ ... }` 字面量在 `Acyclic` 的消去位置上被隐式多填参数）。 -/
def selfDecl : FateV2.Core.Decl Nat :=
  { key := 0, kind := .defn, bodyKind := .body, deps := [0], visibility := .open_ }

/-- **自环图**（与 `selfGraph` 同形，但用命名的 `selfDecl`，便于在证明里 `show`）。 -/
def selfGraph' : FateV2.Core.DeclGraph Nat := [selfDecl]

/-- **`deps` 的成员拆解**：`dep ∈ d.deps` 且 `d` 是两条之一 ⟹ `dep` 只能是那个数。

  **超出定义之处**：成员判定是归纳族，拆开之后得到「`dep` 等于表头」或「在尾部」；
  本条把两步合成「`dep` 是那**唯一**的元素」。§6.5 的 `Acyclic` 证明就靠这一步。 -/
theorem member_single (dep a : Nat) (h : dep ∈ ([a] : List Nat)) : dep = a := by
  cases h with
  | head => rfl
  | tail _ h2 => cases h2

/-- **★ B4：长度 2 的环**通过** `Acyclic`，自环**不通过**。**

  **超出定义之处**：`Acyclic g := ∀ d ∈ g, d.key ∉ d.deps` 只比对**每条声明自己**的键；
  本条证明 `cycGraph'` **满足**它、而自环图**不满足**。

  ⟹ 名字暗示的「无环」比定义实际排除的东西**强得多**：
  `Acyclic` 只排除**自环**，**完全不排除长度 ≥ 2 的环**。
  这是依赖图层的**第四处口径缺陷（B4）**：§6.1 说的「失效传播在环上不是偏序」
  **不会**被 `Acyclic` 挡住。见 `_报告/T56-进度.md` §六。

  ⚠ 两个证明都刻意**不做** `cases` 声明（`Decl` 有 **5 个字段**，逐支 `cases` 会生成
  5 个隐式参数、把 `Acyclic` 的三个消去位置填满，实测报「没有可引入的绑定」）。
  做法是**只对成员证明 `cases`**（拿到 `d = cycDecl0 ∨ d = cycDecl1`），
  再把 `deps` 的元素拆成具体数、最后 `decide` 收口。 -/
theorem cycle2_is_acyclic :
    FateV2.Core.DeclGraph.Acyclic cycGraph' ∧ ¬ FateV2.Core.DeclGraph.Acyclic selfGraph' := by
  refine ⟨?_, ?_⟩
  · intro d hd
    have hd' : d = cycDecl0 ∨ d = cycDecl1 := by
      cases hd with
      | head => exact Or.inl rfl
      | tail _ h2 =>
        cases h2 with
        | head => exact Or.inr rfl
        | tail _ h3 => cases h3
    rcases hd' with h | h
    · rw [h]; decide
    · rw [h]; decide
  · intro h
    exact (h selfDecl (by show selfDecl ∈ [selfDecl]; exact List.mem_cons_self))
      (by show selfDecl.key ∈ selfDecl.deps; exact List.mem_cons_self)

/-- **自环 ⟹ 不是 `Acyclic`**（与上一条的第二分量同义，单独抽出供引用）。 -/
theorem acyclic_self_loop_iff : ¬ FateV2.Core.DeclGraph.Acyclic selfGraph' :=
  cycle2_is_acyclic.2

/-! ### §6.2 ★ B3：`closure g roots` **不是**「`roots` 的依赖闭包」

`DeclGraph.closure` 的定义（**逐字**）：

```lean
def closure (g : DeclGraph K) (roots : List K) : List K :=
  roots ++ (g.filter (fun d => roots.any (fun r => decide (d.key = r)))).flatMap (fun d => d.deps)
```

它算的是「**被 `roots` 点名的那些声明的 `deps`**」——
**不是**「`roots` 里的键的 `deps`」，也不是「传递闭包」。
若调用方把「声明键」填进 `roots`（`ExecutableGraph.runGraph` 里
`closure demoGraph [0]` 的读法就是如此），结果**只有 `[0]`**：一个依赖都不带。

下面给出**正确实现** `depsOfRoots` 与它的**无前件**主定理（零公理）。 -/

/-- **辅助：两个 `Nat` 是否相等**（按 `Nat` 的构造子结构递归，**不用** `DecidableEq`）。

  ⚠ **本文件在 `Nat` 判等上踩了三个坑，全部实测**：

  | 写法 | `#eval depsOfKey demoGraph 0` | `rfl` 能否证 |
  |---|---|---|
  | `if decide (d.key = k) = true then …` | （不闭合） | 部分可以 |
  | `if d.key == k then …`（`BEq`） | 对；但 `rfl` **证不了** `flatDepsOf` 的归约 | ❌ |
  | `if d.key = k then …` | `=` 是 `Prop`，需要 `Decidable`，符号上不归约 | ❌ |
  | **`natEq d.key k = true`（本条）** | 对 | ✅ |

  根因：前三种写法在 `Decl.key`（`Nat` 字段投影）上都留下**不可归约的 `decide`/`BEq`**，
  于是整条 `flatDepsOf` 停在 `match` 上。本条的 `natEq` 只做构造子匹配，
  对所有**字面量**参数都能归约到 `true`/`false`。见 `_报告/T56-进度.md` §九.5。 -/
def natEq : Nat → Nat → Bool
  | 0,     0     => true
  | 0,     _ + 1 => false
  | _ + 1, 0     => false
  | a + 1, b + 1 => natEq a b

/-- **辅助：键 `k` 在 `g` 里的 `deps`**（找不到就是 `[]`）。 -/
def depsOfKey (g : FateV2.Core.DeclGraph Nat) (k : Nat) : List Nat :=
  match g with
  | []      => []
  | d :: ds => if natEq d.key k then d.deps else depsOfKey ds k

/-- 辅助：把 `roots` 里每个键的 `deps` 依次接起来（手写递归）。 -/
def flatDepsOf (g : FateV2.Core.DeclGraph Nat) : List Nat → List Nat
  | []      => []
  | r :: rs => depsOfKey g r ++ flatDepsOf g rs

/-- **正确的「根 ∪ 根的 deps」**：对 `roots` 里的每个键，把它在 `g` 里的 `deps` 全部接上。 -/
def depsOfRoots (g : FateV2.Core.DeclGraph Nat) (roots : List Nat) : List Nat :=
  roots ++ flatDepsOf g roots

/-- **`demoGraph` 的逐行分解**（键 `0..3`，与本文件 §6 的边界图**同一种写法**）。

  为什么要这一份：`ExecutableGraph.demoGraph` 是**另一个模块里的 `def`**，
  对它的归约在**常量层**进行；而 `depsOfKey` 的归约要看**每条声明的 `key` 字段**。
  实测（本文件 §九.5 的表）：直接对 `demoGraph` 求 `depsOfKey` 时，
  内部的 `natEq` 无法穿透常量层展开，`depsOfKey demoGraph 0` 停在 `match` 上、
  `rfl` 证不了。写成**本文件的字面量 `g4`** 之后一切正常。
  ⟹ 本文件的结论**一律在自己的字面量图上证**，再用 `g4_eq_demoGraph` 把两者接上
  ——这份分解本身也是零公理的。 -/
def dg0 : FateV2.Core.Decl Nat :=
  { key := 0, kind := .defn, bodyKind := .body, deps := [], visibility := .open_ }

/-- `demoGraph` 的第 2 条声明。 -/
def dg1 : FateV2.Core.Decl Nat :=
  { key := 1, kind := .defn, bodyKind := .body, deps := [0], visibility := .open_ }

/-- `demoGraph` 的第 3 条声明。 -/
def dg2 : FateV2.Core.Decl Nat :=
  { key := 2, kind := .defn, bodyKind := .body, deps := [0], visibility := .open_ }

/-- `demoGraph` 的第 4 条声明。 -/
def dg3 : FateV2.Core.Decl Nat :=
  { key := 3, kind := .defn, bodyKind := .body, deps := [1, 2], visibility := .open_ }

/-- **字面量版 `demoGraph`**（`0 → 1 → 3`，`0 → 2 → 3`）。 -/
def g4 : FateV2.Core.DeclGraph Nat := [dg0, dg1, dg2, dg3]

/-- **`g4` 就是 `ExecutableGraph.demoGraph`**（`rfl`，零公理）。

  **超出定义之处**：`demoGraph` 在另一个文件里是**四个字面量**；
  本条说明本文件的分解**逐字等于**它——于是「在 `g4` 上证的」可以**无前件**搬到
  `demoGraph` 上。这是本文件能把 §6 的结论写成具体数的**桥**。 -/
theorem g4_eq_demoGraph : g4 = FateV2.Demo.ExecutableGraph.demoGraph := rfl

/-- **★ B3：`closure` 在 `roots = [0]` 上**只**给出 `[0]`**（`rfl`）。

  **超出定义之处**：`ExecutableGraph.runGraph` 的**预期输出**注释里写的是
  `closure [0] = [0, 1, 2, 3]`，而**实测值是 `[0]`**。本条把实测值钉成定理，
  于是「注释与实现不一致」这件事有了**机检证据**（§7 的 `#eval` 打的那一行也看得到）。
  ⚠ 这是本文件**发现的第二处「既有文档与实现不一致」**。 -/
theorem closure_roots_not_deps :
    FateV2.Core.DeclGraph.closure g4 [0] = [0] := rfl

/-- **`closure` 在 `roots = [3]` 上**带出** `1, 2`**（对照：键 `3` 的声明的 `deps = [1,2]`）。

  **超出定义之处**：与上一条并排，才看得清 B3 的**机制**——
  `closure` **不是**「按键查 deps」，而是「按 `roots` 过滤声明表再 `flatMap`」。
  `roots = [3]` 命中了键为 `3` 的那条声明，于是带出 `[1, 2]`；
  `roots = [0]` 命中的是**键为 `0`** 的那条（`deps = []`），于是**什么都不带**。
  ⟹ `closure` 的语义是「**这些声明的 deps**」，**不是**「这些键的 deps」——
  两者只在「`roots` 恰好是一组叶子声明」时才一致。 -/
theorem closure_leaf_vs_root :
    FateV2.Core.DeclGraph.closure g4 [3] = [3, 1, 2] := rfl

/-- **★ B3 的正面：`depsOfRoots` 在 `g4` 上给出**根**（`[0]`）**，`closure` 不给依赖。** -/
theorem depsOfRoots_demo : depsOfRoots g4 [0] = [0] := by
  show ([0] : List Nat) ++ flatDepsOf g4 [0] = [0]
  rw [show flatDepsOf g4 [0] = ([] : List Nat) from rfl]
  rfl

/-- **★ B3 的正面对照：`depsOfRoots` 在 `g4` 的根 `[3]` 上把 `1, 2` 带进来**。

  与 `depsOfRoots_demo`（根 `[0]`）并排：`[0]` 是叶子、`[3]` 有两条依赖。
  `closure g4 [3] = [3, 1, 2]` 也带出了 `1, 2`——**两条在 `[3]` 上一致**。
  ⟹ B3 **不是**「`depsOfRoots` 总能带出依赖而 `closure` 不能」，
  而是「两者**只在 `roots` 恰好是叶子**时一致」；`roots = [0]` 恰是那个反例。
  本条把这个区分**用在正确的那个根上**，避免把 B3 说过头。 -/
theorem depsOfRoots_demo3 : depsOfRoots g4 [3] = [3, 1, 2] := by
  show ([3] : List Nat) ++ flatDepsOf g4 [3] = [3, 1, 2]
  rw [show flatDepsOf g4 [3] = [1, 2] from rfl]
  rfl

/-- **`closure` 在叶子根上与 `depsOfRoots` **一致**（这是它们唯一一致的场合）。 -/
theorem closure_vs_depsOfRoots_leaf :
    FateV2.Core.DeclGraph.closure g4 [3] = depsOfRoots g4 [3] := by
  rw [closure_leaf_vs_root, depsOfRoots_demo3]

/-- **`depsOfRoots` 在空图上**只返回 `roots`**（§⑤ 空图边界，**无前件**）。 -/
theorem depsOfRoots_empty (roots : List Nat) : depsOfRoots emptyGraph roots = roots := by
  show roots ++ flatDepsOf emptyGraph roots = roots
  rw [show flatDepsOf emptyGraph roots = ([] : List Nat) from by
    induction roots with
    | nil => rfl
    | cons r rs ih =>
      show depsOfKey emptyGraph r ++ flatDepsOf emptyGraph rs = []
      rw [ih]
      rfl]
  exact List.append_nil roots

/-- **`depsOfRoots` 在单节点图上**返回 `[0]`**（§⑤ 单节点边界）。 -/
theorem depsOfRoots_single : depsOfRoots singleGraph [0] = [0] := by
  show ([0] : List Nat) ++ flatDepsOf singleGraph [0] = [0]
  rw [show flatDepsOf singleGraph [0] = ([] : List Nat) from by
    show depsOfKey singleGraph 0 ++ flatDepsOf singleGraph [] = []
    rw [show flatDepsOf singleGraph ([] : List Nat) = ([] : List Nat) from rfl]
    rfl]
  rfl

/-- **★ `depsOfRoots` 在自环图上把 `0` 带两次**（§⑤ 自环边界）。

  **超出定义之处**：自环让「根」与「依赖」**重合**，于是「根 ∪ 根的 deps」
  这份表里 `0` 出现**两次**。定义里**没有**去重（`closure` 也没有），
  于是**「闭包」在自环上不是幂等的集合**——它是一个**多重集**。
  这条与 `invalidate_self_loop` 合起来说明：自环让**两个方向**都把自己算进去。 -/
theorem depsOfRoots_self : depsOfRoots selfGraph [0] = [0, 0] := by
  show ([0] : List Nat) ++ flatDepsOf selfGraph [0] = [0, 0]
  rw [show flatDepsOf selfGraph [0] = [0] from by
    show depsOfKey selfGraph 0 ++ flatDepsOf selfGraph [] = [0]
    rw [show flatDepsOf selfGraph ([] : List Nat) = ([] : List Nat) from rfl]
    rfl]
  rfl

/-- **★ `depsOfRoots` 在环图上给出两个节点的 deps**（§⑤ 环边界）。

  **超出定义之处**：环 `0 → 1 → 0` 上「根 ∪ 根的 deps」= `[0, 1]`。
  它**包含**了 `1` 的依赖 `0`——于是「一层展开」在环上**看起来像全闭包**，
  但**只对长度 2 的环成立**；长度 3 的环需要再展一层。
  ⟹ 「展开几层才够」取决于环长，而 `closure` / `depsOfRoots` 的定义
  对「环长」一无所知。 -/
theorem depsOfRoots_cycle : depsOfRoots cycGraph [0] = [0, 1] := by
  show ([0] : List Nat) ++ flatDepsOf cycGraph [0] = [0, 1]
  rw [show flatDepsOf cycGraph [0] = [1] from by
    show depsOfKey cycGraph 0 ++ flatDepsOf cycGraph [] = [1]
    rw [show flatDepsOf cycGraph ([] : List Nat) = ([] : List Nat) from rfl]
    rfl]
  rfl

/-! ===========================================================================
  §7  `#eval`：五类边界情形的**实际输出**

  这一节是任务书要求的「能看到实际输出」。每类边界的判据是**两条**：
  ① 有一个 `#eval` 打出来的值；② 有一条定理把它钉住（各节）。
  这里的 `#eval` 全部走**可计算路径**（`Int` / `Nat` / `List` / `Bool`），
  不碰 `Real`、不碰 `ExportResult`（后者没有 `Repr`）。
  =========================================================================== -/

/-! ### §7.1 ① 数据层：空 / 单行 / 零方差 -/
#eval emptyLaw
#eval pointLaw
#eval constData
#eval constRaw

/-! ### §7.2 ② SCM 层：空外生律 / 单点律 / 全零权重律的**推前** -/
#eval (FateV2.Predict.pushMerge (fun x : Int => x) emptyLaw)
#eval (FateV2.Predict.pushMerge (fun x : Int => x + 1) pointWorld)
#eval (FateV2.Predict.pushMerge (fun x : Int => x) zeroAllLaw)

/-! **T43 的 `zeroLaw`（`ZTwo` 载体）**：`rawMap` 与 `pushMerge` **条数不同**。 -/
#eval (FateV2.Predict.rawMap FateV2.Predict.zeroLaw FateV2.Predict.zcollapse).wt
#eval (FateV2.Predict.pushMerge FateV2.Predict.zcollapse FateV2.Predict.zeroLaw)

/-! ### §7.3 ③ 预测层：残差 = 0 的判据、首项口径、`σ` -/

-- 残差 = 0 时 `|e| + ε` 与 `σ`
#eval (FateV2.Demo.IntScaled.add FateV2.Demo.IntScaled.epsTol
        (FateV2.Demo.IntScaled.absF
          (FateV2.Demo.IntScaled.residual (FateV2.Demo.IntScaled.fx 1300)
            (FateV2.Demo.IntScaled.fx 1300))))
#eval (FateV2.Demo.IntScaled.sigma : FateV2.Demo.IntScaled.V)
-- 残差 = 0 的裁决 K（`true` = 不合格）
#eval verdictFails (FateV2.Demo.IntScaled.residual (FateV2.Demo.IntScaled.fx 1300)
                     (FateV2.Demo.IntScaled.fx 1300))
-- 原来的 demo 点（`|e| = 100`）也是 `true`
#eval verdictFails (FateV2.Demo.IntScaled.residual (FateV2.Demo.IntScaled.fx 1300)
                     FateV2.Demo.IntScaled.pointPred)
-- 首项 vs 均值
#eval FateV2.Demo.IntScaled.pointPred
#eval FateV2.Demo.IntScaled.predMean

/-! ### §7.4 ④ 导出层：三种边界的 `count` 与 `restricted` -/

-- 空注册表：`count = 0`、`restricted = false`
#eval (FateV2.Export.exportAll zeroReg unitModel).count
#eval (FateV2.Export.exportAll zeroReg unitModel).restricted
-- 只注册一个：`count = 1`、`restricted = false`
#eval (FateV2.Export.exportAll oneReg unitModel).count
#eval (FateV2.Export.exportAll oneReg unitModel).restricted
-- 三个注册、只 exclude 一个：`count = 2`
#eval (FateV2.Export.exportModalities FateV2.Demo.ExecutableExport.demoReg
        unitModel exclScope).count
-- 三个注册、全部 exclude：`count = 0` 但 `restricted = true`（B5）
#eval (FateV2.Export.exportModalities FateV2.Demo.ExecutableExport.demoReg
        unitModel exclAllScope).count
#eval (FateV2.Export.exportModalities FateV2.Demo.ExecutableExport.demoReg
        unitModel exclAllScope).restricted

/-! ### §7.5 ⑤ 依赖图：五种图上的 `invalidate` 与 `closure` -/

-- 空图
#eval keysOf (FateV2.Core.DeclGraph.invalidate emptyGraph 0 .body)
#eval FateV2.Core.DeclGraph.closure emptyGraph [0]
-- 单节点
#eval keysOf (FateV2.Core.DeclGraph.invalidate singleGraph 0 .body)
#eval FateV2.Core.DeclGraph.closure singleGraph [0]
-- 环（`0 → 1 → 0`）：两个方向都失效对方
#eval keysOf (FateV2.Core.DeclGraph.invalidate cycGraph 0 .body)
#eval keysOf (FateV2.Core.DeclGraph.invalidate cycGraph 1 .body)
#eval FateV2.Core.DeclGraph.closure cycGraph [0]
-- 自环：`invalidate` 把**自己**算进来
#eval keysOf (FateV2.Core.DeclGraph.invalidate selfGraph 0 .body)
#eval FateV2.Core.DeclGraph.closure selfGraph [0]
-- B3：`closure` 在 `demoGraph` 上「叶子根 vs 有依赖的根」
#eval FateV2.Core.DeclGraph.closure FateV2.Demo.ExecutableGraph.demoGraph [0]
#eval FateV2.Core.DeclGraph.closure FateV2.Demo.ExecutableGraph.demoGraph [3]

/-! **`depsOfRoots`（正确口径）的对照输出**（`g4 = demoGraph`）。 -/
#eval depsOfRoots g4 [0]
#eval depsOfRoots g4 [3]
#eval depsOfRoots g4 [0, 3]

/-- **★ 零方差 ⟹ 「首项 vs 均值」这条口径分歧在**退化数据上不可见**。

  **超出定义之处**：`DemoInt.pointPred`（首项）与 `predMean`（均值）在 8 条外生律上
  **差整整一个 `σ`**（`pointPred_head_is_far`）。本条说明：把数据换成**零方差**之后，
  推前结果的**支撑只剩一个点**——于是「首项」与「均值」是**同一个数**，
  两个口径**重合**、分歧**不可观察**。

  ⟹ 零方差数据真正的危险不是「算错」，而是它**抹掉了口径分歧这个可观察信号**：
  系统在退化数据上**永远看不到**自己选了哪个口径。这解释了 §4.4 为什么 `σ = 0` 更危险。 -/
theorem constData_single_point_prediction (g : Int → Int) :
    (FateV2.Predict.pushMerge g constData).vals.length = 1 := rfl

/-- **★ `pointPred` 与 `predMean` 确实不同**（引 `DemoInt.pointPred_ne_mean'`）。

  **超出定义之处**：上一条只说「零方差上支撑是一个点」；本条把**非退化**数据上
  「首项 ≠ 均值」这一事实钉住——两条合起来才是完整结论：
  **分歧存在于非退化数据、消失于退化数据**。 -/
theorem pointPred_ne_predMean :
    FateV2.Demo.IntScaled.pointPred ≠ FateV2.Demo.IntScaled.predMean :=
  fun h => FateV2.Demo.IntScaled.pointPred_ne_mean' h.symm

end FateV2.Demo.EdgeCases
