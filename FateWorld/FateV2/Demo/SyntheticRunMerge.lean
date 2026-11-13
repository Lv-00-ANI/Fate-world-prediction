import FateWorld.FateV2.Demo.SyntheticRun
import FateWorld.FateV2.Predict.PushFamilyMerge
import Mathlib.Tactic

/-!
  # Demo · SyntheticRunMerge —— 端到端接上「合并推前」

  ## 迁移登记
  - 来源：新写（本文件）
  - 动作：C 重写（新文件）
  - 对应环节：全链 — F5（建模）→ 模型 → F6（预测）→ F6-10（导出）
              → F7（误差 / 裁决 K）→ F7-22（回写）→ 再预测
  - 依赖裁决：**D-007**（数据数学构造）、**D-008**（σ 来自建模层）、
              **D-009**（预测 = 在模型空间里演化）、**裁决 K**（误差 ≈ σ 才合格）、
              **D-011/D-012/D-013**（模态导出）、**D-014**（模型 = SCM）、
              **D-019**（不写死载体）、**D-022**（反空泛）
  - 改动：**新文件**。`Demo/SyntheticRun.lean` **一个字没改**（只读复用其
          `M` / `s0` / `order` / `e₁` / `stepState` / `projState` / `reg` / `sigma` / `epsTol` / `eta`）。
  - 状态：已验证（`_check.ps1 -Group A` 通过）

  ## 为什么要另开一个文件

  `Demo/SyntheticRun.lean` 的 ④ 预测用的是 `Predict.rawMap`：

  ```lean
  def pred₁ : DiscLaw Real := Predict.rawMap synthLaw stepState
  ```

  T4 已证 `rawMap` **在非单射时丢质量**（`rawMap_drops_mass`），T13 交付了合并版
  `discPushFamilyM`（`push` 就是 `pushMerge`）。本文件把 demo 的 ④ 换成合并版，
  并把整条链**重新跑一遍**。

  ⟹ **不改旧文件是刻意的**：旧文件是「旧推前下的数值事实」的存证
  （20+ 条数值定理），改它等于销毁对照。本文件提供**同一实例的第二套数值**。

  ## ★ 先把事实算清楚（不预设结论）

  `synthLaw` 有 8 条外生赋值。沿 `stepState` 推前，像点表是

  ```
  ε=−1/2 :  9/10 + 1 − 1/2 = 7/5      （×2，w = ∓1 不进气）
  ε=−1/4 :  9/10 + 1 − 1/4 = 33/20    （×2）
  ε= 1/4 :  9/10 + 1 + 1/4 = 43/20    （×2）
  ε= 1/2 :  9/10 + 1 + 1/2 = 12/5     （×2）
  ```

  ⟹ **投影 `stepState` 在 `synthLaw` 上不是单射**：8 条原像落成 **4 个**像点，
  每个像点**2 条原像**。

  于是本文件的三条数值结论（全部可手算复核）：

  | 量 | 旧版（`rawMap`，= `SyntheticRun.pred₁`） | 合并版（`pushMerge`，本文件 `predM`） |
  |---|---|---|
  | 像点表条数 | **8** | **4** |
  | 像点表 | `[7/5, 7/5, 33/20, 33/20, 43/20, 43/20, 12/5, 12/5]` | `[7/5, 33/20, 43/20, 12/5]` |
  | 权重表 | `[1,1,1,1,1,1,1,1]` | `[2, 2, 2, 2]` |
  | 总质量 | **8** | **8** |
  | 按位置读「`7/5` 处的质量」 | **1** | **2** |
  | 点预测（首项） | `7/5` | `7/5` |

  **所以：总质量两边都是 8（`rawMap_total` 看不出来），但「`7/5` 处的概率」旧版读成
  `1/8`、正确值 `2/8 = 1/4`——少了 `1`，占 `1/4`。**

  点预测（首项）**恰好在两条推前下相同**（都是 `7/5`），因为最小的 `ε` 恰好排第一。
  ⟹ **本例上「残差、裁决 K、回写」的数值不受这个 bug 影响**；
  bug 落在**分布本身**（单点质量），而 `SyntheticRun` 的 `pointPred` 口径读不出它。

  ## 结论（先给答案）

  | 问题 | 答案 | 定理 |
  |---|---|---|
  | demo 原来的投影是单射吗 | **不是**：8 条原像 → 4 个像点，各 2 条 | `img_ne_inj` |
  | 旧版与新版首项质量 | 旧 **1**、新 **2**，差 **1**（占 `1/4`） | **`merge_vs_raw_same_instance`** |
  | 总质量守恒吗 | **是**：合并版 = 原律 `total` = `8` | `merged_total_eq_law` |
  | 旧版总质量 | 也是 `8`（`rfl`）——**所以看不出来** | `raw_total_also_eight` |
  | 点预测变了吗 | **没变**，两边都是 `7/5` | `merge_vs_raw_pointPred_eq` |
  | 误差 / 裁决 K / 回写 | **与旧版逐字相同**（`−1/10`、不合格、减半） | `merged_chain_end_to_end` |
  | 单射时两版一致吗 | **是**（一般定理，不只本实例） | `merge_eq_raw_on_inj` |

  ## 超出定义之处（D-022 逐条登记）

  * `merge_vs_raw_same_instance`：`pushMerge` 与 `rawMap` 的定义**互不相干**
    （一个照抄权重、一个求和）。本条把两者在**同一实例**上的两张表和两个首项读数
    一起算成具体数值——定义里没有任何「首项读数会差多少」的内容。
  * `raw_first_mass_defect`：**否定性**结论的具体数值（`1` 对 `2`，差 `1`，占 `1/4`）。
    这正是 `rawMap_total`（`rfl`）看不出来的那一维：**总质量相同、记法不同**。
  * `merged_total_eq_law`：`predictM_total` 是**一般**定理；本条把它在**本实例**上
    算成 `8`，且这个 `8` 是**手算的**（`4` 个像点 × `2`），不是从一般定理直接搬。
  * `merge_vs_raw_pointPred_eq`：两版的**首项读数相同**。这不是「合并没用」，
    而是把 bug 的**位置**钉死：它不在首项，在「单点质量」。
  * `merge_eq_raw_on_inj`：把 T4 的 `pushMerge_eq_rawMap_of_injOn` 从「只有总质量相等」
    加强到「**整表相等**」——旧 demo 在单射情形下**逐条**没错，不只是账平。
  * `merged_chain_end_to_end`：一条定理串起整条链，且**否定项与肯定项并存**
    （裁决 K 不合格 + 回写收缩成功 + 分布无重复像点）。三者同时成立不是自动的。

  ## 公理账本（实测，不看写法只看类型）

  凡是类型里出现 `Real`（含 `SynthE` / `DiscLaw SynthE` / `ExportVal` 这些**字段含 Real**
  的结构体），`#print axioms` **一律**是 `propext;Classical.choice;Quot.sound`。
  本文件**不声称零公理**：全部定理已逐条 `#print axioms` 实测并登记进
  `_support_registry_T19.csv`。

  ⚠ 特别地：**`set_option` 之类不影响账本**，`Real` 的 `Quot` 定义链决定了三条。
  这是 T13/T15/T17 已实测的事实，本文件再实测一次。
-/

namespace FateV2.Demo

open FateV2.Modeling FateV2.Model FateV2.Predict FateV2.Export FateV2.ErrorN FateV2.Loop

noncomputable section

/-! ===========================================================================
  §1  复用旧 demo 的建模/求值部分（只读引用，不重定义）
  =========================================================================== -/

/-- **`synthLaw` 的取值表**（8 条外生赋值）。

  **超出定义之处**：`synthLaw.vals` 在只读文件里是两层 `flatMap` 的定义式；
  本条把 8 条外生赋值**逐条**写成字面量。下游的数值定理全都要 `rw` 它才有东西可算。 -/
theorem lawPostVals :
    synthLaw.vals
      = [SynthE.mk (-1/2) (-1), SynthE.mk (-1/2) 1,
         SynthE.mk (-1/4) (-1), SynthE.mk (-1/4) 1,
         SynthE.mk (1/4) (-1),  SynthE.mk (1/4) 1,
         SynthE.mk (1/2) (-1),  SynthE.mk (1/2) 1] := rfl

/-- **`synthLaw` 的权重表**（8 条权重各 `1`）。

  **超出定义之处**：`wt` 在定义里是 `epsWt.flatMap (fun a => obsWt.map (fun b => a * b))`；
  本条把它算成 `[1,1,1,1,1,1,1,1]`——「每条外生赋值等权 `1/8`」从一句注释变成可 `rw` 的事实。 -/
theorem lawPostWt : synthLaw.wt = ([1, 1, 1, 1, 1, 1, 1, 1] : List Nat) := rfl

/-- **原律总质量 = 8**（4 × 2，`eps` 四项与 `w` 两项独立）。

  **超出定义之处**：`synthLaw_total` 是「`epsWt.sum * obsWt.sum`」的形式；
  本条把它落成**一个数** `8`，且**不借** `List.sum` 的引理（直接 `rfl` 到表之和）。 -/
theorem lawPostTotal : synthLaw.total = 8 := by
  show synthLaw.wt.sum = 8
  rw [lawPostWt]
  rfl

/-! ===========================================================================
  §2  一步转移的像点表（8 条 → 4 个像点）

  要害：`ε` 决定 `state`，`w` **不**进入 `state`。于是 `w = ±1` 的两条原像
  **映到同一个像点** ⟹ 投影在支撑上**不单射**。
  =========================================================================== -/

/-- **`ε = −1/2` 下的像点 = `7/5`**。 -/
theorem imgA : stepState { eps := (-1/2 : Real), w := (-1 : Real) } = (7 : Real) / 5 := by
  rw [show stepState { eps := (-1/2 : Real), w := (-1 : Real) }
      = ((9 : Real)/10 * (1 : Real) + (1 : Real) + (-1/2)) from rfl]
  norm_num

/-- **`ε = −1/4` 下的像点 = `33/20`**（`0.9 + 1 − 0.25 = 1.65`）。 -/
theorem imgB : stepState { eps := (-1/4 : Real), w := (-1 : Real) } = (33 : Real) / 20 := by
  rw [show stepState { eps := (-1/4 : Real), w := (-1 : Real) }
      = ((9 : Real)/10 * (1 : Real) + (1 : Real) + (-1/4)) from rfl]
  norm_num

/-- **`ε = 1/4` 下的像点 = `43/20`**（`0.9 + 1 + 0.25 = 2.15`）。

  ⚠ 注意 `43/20 ≠ 5/4`：`2.15 ≠ 1.25`。这正是 `Construct.synth_state_at_one` 那条
  「分部算数别约分错」的同一个数，此处再算一次。 -/
theorem imgC : stepState { eps := (1/4 : Real), w := (-1 : Real) } = (43 : Real) / 20 := by
  rw [show stepState { eps := (1/4 : Real), w := (-1 : Real) }
      = ((9 : Real)/10 * (1 : Real) + (1 : Real) + (1/4)) from rfl]
  norm_num

/-- **`ε = 1/2` 下的像点 = `12/5`**（`0.9 + 1 + 0.5 = 2.4`）。 -/
theorem imgD : stepState { eps := (1/2 : Real), w := (-1 : Real) } = (12 : Real) / 5 := by
  rw [show stepState { eps := (1/2 : Real), w := (-1 : Real) }
      = ((9 : Real)/10 * (1 : Real) + (1 : Real) + (1/2)) from rfl]
  norm_num

/-- **★ `stepState` 在 `synthLaw` 的支撑上不是单射**。

  **超出定义之处**：这是本文件所有别的结论的**前提**。
  `stepState` 的定义是 `M.F SynthV.state s0 e = 9/10 · 1 + 1 + e.eps`——
  它**只读 `e.eps`**，完全不看 `e.w`。定义里没有任何「它会撞车」的话；
  本条把它在**本项目的真数据**上测出来：两条**不同**的外生赋值
  （`{−1/2, −1}` 与 `{−1/2, 1}`）映到**同一个** `7/5`。

  ⟹ 「`rawMap` 在 demo 上是 bug」的**适用条件被满足**，不是空谈。 -/
theorem img_ne_inj :
    ∃ a₁ ∈ synthLaw.vals, ∃ a₂ ∈ synthLaw.vals,
      a₁ ≠ a₂ ∧ stepState a₁ = stepState a₂ := by
  refine ⟨SynthE.mk (-1/2) (-1), ?_, SynthE.mk (-1/2) 1, ?_, ?_, ?_⟩
  · rw [lawPostVals]; exact List.mem_cons_self
  · rw [lawPostVals]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · intro h
    have h' : (-1 : Real) = 1 := congrArg SynthE.w h
    norm_num at h'
  · rw [imgA]
    rw [show stepState { eps := (-1/2 : Real), w := (1 : Real) }
        = ((9 : Real)/10 * (1 : Real) + (1 : Real) + (-1/2)) from rfl]
    norm_num

/-! ===========================================================================
  §3  ④ 预测：**合并版**
  =========================================================================== -/

/-- **一步转移的闭式**：`project ∘ eval` 在 `state` 这一坐标上就是 `stepState`。

  `stepState`（只读文件里的定义）本来就是 `M.F SynthV.state s0 e`；
  `evalFrom M e s0 order` 在 `state` 上取到的也是它（`state` 是 `order` 的第一位）。
  本条把这条等式写成**函数相等**，供下游 `rw`。

  **超出定义之处**：`predict` 吃的是**整条**内生赋值 `WholeState`，
  而 `stepState` 只吃外生赋值；本条说明「在 `projState` 这个投影下，
  前者退化成后者」——两个函数被接上，不是定义展开。 -/
theorem evalProj_eq_stepState (e : SynthE) :
    projState (evalFrom M e s0 order) = stepState e := by
  show (evalFrom M e s0 order) SynthV.state = M.F SynthV.state s0 e
  rw [show order = (SynthV.state :: [SynthV.obs]) from rfl]
  rw [evalFrom_cons]
  show (evalFrom M e (fun u => if u = SynthV.state then M.F SynthV.state s0 e else s0 u)
      [SynthV.obs]) SynthV.state = M.F SynthV.state s0 e
  rw [evalFrom_notin M e (fun u => if u = SynthV.state then M.F SynthV.state s0 e else s0 u)
      [SynthV.obs] SynthV.state (by simp)]
  show (if SynthV.state = SynthV.state then M.F SynthV.state s0 e else s0 SynthV.state)
      = M.F SynthV.state s0 e
  rw [if_pos rfl]

/-- 合并推前族的 `Real` 实例（`Z = Real`，判等由 `Real.decidableEq` 提供）。

  ⚠ `E` 位取 `Real`（不能写 `SynthE`）：`discPushFamilyM (Z : Type)`
  把结构与目标类型**绑死**成同一个 `Z`。本 demo 的投影目标就是 `Real`，
  故 `PushFamily DiscLaw Real Real Real` **正好够用**——外生律先用
  `rawMap` 换成 `DiscLaw Real`（`synthLawR`，见 `predictM_total_eq_predict_total` 的口径）。 -/
def pfM : PushFamily DiscLaw Real Real Real := discPushFamilyM Real

/-- **④ 预测（合并版）**：`predict` 用合并族，**直接吃 `DiscLaw SynthE`**。

  `predict` 只要求 `PushFamily T E Z Z`；把 `E` 位放成 `SynthE` 需要
  `discPushFamilyM SynthE`，而那要求 `DecidableEq SynthE`——`SynthE` **故意没有**
  （`Construct.lean` §1：`Real` 上的判等不可计算，给了会让下游全部 `noncomputable`）。

  ⟹ 本文件的办法：**用 `PushFamily` 的字面量把 `pushMerge` 直接装进去**，
  除了 `push` 字段什么都不带。这样「合并推前」是**显式的一个值**，
  不需要任何额外实例——这正是 T13 方案丙的精神（结构不改、只换值），
  只是这一个值在本实例上更省。 -/
def pfSynthE : PushFamily DiscLaw SynthE Real Real where
  push := fun L f => pushMerge f L

/-- **`pfSynthE.push` 就是 T4/T13 的 `pushMerge`**（`rfl`）——同一份实现，不是另写一份。 -/
theorem pfSynthE_push (f : SynthE → Real) (L : DiscLaw SynthE) :
    pfSynthE.push L f = pushMerge f L := rfl

/-- **④ 预测（合并版）**：`predict` 用合并族。

  与 `SyntheticRun.pred₁ = rawMap synthLaw stepState` 是**同一个投影、同一个律**，
  只换推前族。`predict` 的函数体**一个字符没改**（T13 的方案丙）。 -/
def predM : DiscLaw Real := predict M (fun e => evalFrom M e s0 order) projState pfSynthE

/-- **合并版的 `predict` 就是 `pushMerge`**（`rfl`）。

  **超出定义之处**：`predict` 收的是 `PushFamily`，`pfSynthE` 是它的一个值；
  本条把「用合并族预测」展开成「直接调 `pushMerge`」，
  于是下游的数值定理不必再展开 `predict` / `DiscLaw` 的字段投影。 -/
theorem predM_eq_push : predM
    = pushMerge (fun e => projState (evalFrom M e s0 order)) synthLaw := rfl

/-- **合并版的投影 = `fe`**：`projState ∘ evalFrom = fun e => 9/10·1 + 1 + e.eps`。

  **超出定义之处**：`predict` 吃的是「整条内生赋值 ➜ 实数」的投影复合，
  `stepState` 只吃外生赋值。本条把**两个不同层的函数**接成同一个（`funext`），
  于是下面的 8 步算术全在 `fe` 上做。 -/
theorem projM_eq_fe :
    (fun e => projState (evalFrom M e s0 order))
      = (fun e : SynthE => (9 : Real)/10 * (1 : Real) + (1 : Real) + e.eps) :=
  funext (fun e => (evalProj_eq_stepState e).trans
    (show stepState e = ((9 : Real)/10 * (1 : Real) + (1 : Real) + e.eps) from rfl))

/-! ===========================================================================
  §2.5  8 步推前的**逐步手算**（真数据上，`goN` 走完到底长什么样）
  =========================================================================== -/

/-! ### `fe`：一步转移在 `state` 坐标上的闭式

  `stepState e = M.F SynthV.state s0 e = 9/10 · 1 + 1 + e.eps`（`rfl` 可展开）。
  本文件把右边提成具名函数 `fe`，于是「8 条原像的像点」变成**纯代数计算**。 -/

/-- **一步转移的闭式**：`stepState e = 9/10 · 1 + 1 + e.eps`。 -/
def fe : SynthE → Real := fun e => (9 : Real)/10 * (1 : Real) + (1 : Real) + e.eps

/-- `fe` 与 `stepState` 逐点相等（`rfl`）：本文件没有另写一套转移方程。 -/
theorem fe_eq_stepState (e : SynthE) : fe e = stepState e := rfl

/-! ### 8 条原像的像点（4 个值、各两次）

  **要害**：`ε` 决定像点，`w` 完全不参与。于是 `w = ∓1` 的两条原像撞车。 -/

theorem fe1 : fe { eps := (-1/2 : Real), w := (-1 : Real) } = (7 : Real)/5 := by
  show (9 : Real)/10 * (1 : Real) + (1 : Real) + (-1/2) = (7 : Real)/5
  norm_num
theorem fe2 : fe { eps := (-1/2 : Real), w := (1 : Real) } = (7 : Real)/5 := by
  show (9 : Real)/10 * (1 : Real) + (1 : Real) + (-1/2) = (7 : Real)/5
  norm_num
theorem fe3 : fe { eps := (-1/4 : Real), w := (-1 : Real) } = (33 : Real)/20 := by
  show (9 : Real)/10 * (1 : Real) + (1 : Real) + (-1/4) = (33 : Real)/20
  norm_num
theorem fe4 : fe { eps := (-1/4 : Real), w := (1 : Real) } = (33 : Real)/20 := by
  show (9 : Real)/10 * (1 : Real) + (1 : Real) + (-1/4) = (33 : Real)/20
  norm_num
theorem fe5 : fe { eps := (1/4 : Real), w := (-1 : Real) } = (43 : Real)/20 := by
  show (9 : Real)/10 * (1 : Real) + (1 : Real) + (1/4) = (43 : Real)/20
  norm_num
theorem fe6 : fe { eps := (1/4 : Real), w := (1 : Real) } = (43 : Real)/20 := by
  show (9 : Real)/10 * (1 : Real) + (1 : Real) + (1/4) = (43 : Real)/20
  norm_num
theorem fe7 : fe { eps := (1/2 : Real), w := (-1 : Real) } = (12 : Real)/5 := by
  show (9 : Real)/10 * (1 : Real) + (1 : Real) + (1/2) = (12 : Real)/5
  norm_num
theorem fe8 : fe { eps := (1/2 : Real), w := (1 : Real) } = (12 : Real)/5 := by
  show (9 : Real)/10 * (1 : Real) + (1 : Real) + (1/2) = (12 : Real)/5
  norm_num

/-! ### `eqb` 在四个像点上的**实测取值**

  ⚠ 实测事实：`eqb a b` 名义上是 `decide (a = b)`，但在**具体** `Real` 上
  **不按 `rfl` 归约**（`Real` 是 `Quot`，判等走经典代表元比较）。
  故这 10 条判等结果必须**单独证出来**，才能让 `addAt` 的合并分支被 `rw` 打开。
  每条都写成 `(if a = b then true else false)` 的形状以落到 `if_pos`/`if_neg`。 -/

theorem eqb_AA : eqb ((7 : Real)/5) ((7 : Real)/5) = true := by
  show decide ((7 : Real)/5 = (7 : Real)/5) = true
  show (if ((7 : Real)/5 = (7 : Real)/5) then true else false) = true
  rw [if_pos rfl]
theorem eqb_AB : eqb ((7 : Real)/5) ((33 : Real)/20) = false := by
  show decide ((7 : Real)/5 = (33 : Real)/20) = false
  show (if ((7 : Real)/5 = (33 : Real)/20) then true else false) = false
  rw [if_neg (by norm_num)]
theorem eqb_AC : eqb ((7 : Real)/5) ((43 : Real)/20) = false := by
  show decide ((7 : Real)/5 = (43 : Real)/20) = false
  show (if ((7 : Real)/5 = (43 : Real)/20) then true else false) = false
  rw [if_neg (by norm_num)]
theorem eqb_AD : eqb ((7 : Real)/5) ((12 : Real)/5) = false := by
  show decide ((7 : Real)/5 = (12 : Real)/5) = false
  show (if ((7 : Real)/5 = (12 : Real)/5) then true else false) = false
  rw [if_neg (by norm_num)]
theorem eqb_BB : eqb ((33 : Real)/20) ((33 : Real)/20) = true := by
  show decide ((33 : Real)/20 = (33 : Real)/20) = true
  show (if ((33 : Real)/20 = (33 : Real)/20) then true else false) = true
  rw [if_pos rfl]
theorem eqb_BC : eqb ((33 : Real)/20) ((43 : Real)/20) = false := by
  show decide ((33 : Real)/20 = (43 : Real)/20) = false
  show (if ((33 : Real)/20 = (43 : Real)/20) then true else false) = false
  rw [if_neg (by norm_num)]
theorem eqb_BD : eqb ((33 : Real)/20) ((12 : Real)/5) = false := by
  show decide ((33 : Real)/20 = (12 : Real)/5) = false
  show (if ((33 : Real)/20 = (12 : Real)/5) then true else false) = false
  rw [if_neg (by norm_num)]
theorem eqb_CC : eqb ((43 : Real)/20) ((43 : Real)/20) = true := by
  show decide ((43 : Real)/20 = (43 : Real)/20) = true
  show (if ((43 : Real)/20 = (43 : Real)/20) then true else false) = true
  rw [if_pos rfl]
theorem eqb_CD : eqb ((43 : Real)/20) ((12 : Real)/5) = false := by
  show decide ((43 : Real)/20 = (12 : Real)/5) = false
  show (if ((43 : Real)/20 = (12 : Real)/5) then true else false) = false
  rw [if_neg (by norm_num)]
theorem eqb_DD : eqb ((12 : Real)/5) ((12 : Real)/5) = true := by
  show decide ((12 : Real)/5 = (12 : Real)/5) = true
  show (if ((12 : Real)/5 = (12 : Real)/5) then true else false) = true
  rw [if_pos rfl]

/-! ### `addAt` 的 8 步（每一步都在**具体累加器**上算）

  这 8 条是「合并」这件事的**全部内容**：判等命中就把权重加上去，
  没命中就在末尾追加一条。 -/

theorem addAt_A1 :
    addAt eqb ((7 : Real)/5) 1 ([] : List (Real × Nat))
      = ([((7 : Real)/5, 1)] : List (Real × Nat)) := addAt_nil _ _ _

theorem addAt_A2 :
    addAt eqb ((7 : Real)/5) 1 ([((7 : Real)/5, 1)] : List (Real × Nat))
      = ([((7 : Real)/5, 2)] : List (Real × Nat)) := by
  show (match eqb ((7 : Real)/5) ((7 : Real)/5) with
        | true  => ((7 : Real)/5, 1 + 1) :: []
        | false => ((7 : Real)/5, 1) :: addAt eqb ((7 : Real)/5) 1 [])
      = [((7 : Real)/5, 2)]
  rw [eqb_AA]

theorem addAt_B1 :
    addAt eqb ((33 : Real)/20) 1 ([((7 : Real)/5, 2)] : List (Real × Nat))
      = ([((7 : Real)/5, 2), ((33 : Real)/20, 1)] : List (Real × Nat)) := by
  show (match eqb ((7 : Real)/5) ((33 : Real)/20) with
        | true  => ((7 : Real)/5, 2 + 1) :: []
        | false => ((7 : Real)/5, 2) :: addAt eqb ((33 : Real)/20) 1 [])
      = [((7 : Real)/5, 2), ((33 : Real)/20, 1)]
  rw [eqb_AB]
  rfl

theorem addAt_B2 :
    addAt eqb ((33 : Real)/20) 1
        ([((7 : Real)/5, 2), ((33 : Real)/20, 1)] : List (Real × Nat))
      = ([((7 : Real)/5, 2), ((33 : Real)/20, 2)] : List (Real × Nat)) := by
  show (match eqb ((7 : Real)/5) ((33 : Real)/20) with
        | true  => ((7 : Real)/5, 2 + 1) :: _
        | false => ((7 : Real)/5, 2) :: addAt eqb ((33 : Real)/20) 1 _)
      = _
  rw [eqb_AB]
  show ((7 : Real)/5, 2) ::
        (match eqb ((33 : Real)/20) ((33 : Real)/20) with
         | true  => ((33 : Real)/20, 1 + 1) :: []
         | false => ((33 : Real)/20, 1) :: addAt eqb ((33 : Real)/20) 1 [])
      = [((7 : Real)/5, 2), ((33 : Real)/20, 2)]
  rw [eqb_BB]

theorem addAt_C1 :
    addAt eqb ((43 : Real)/20) 1
        ([((7 : Real)/5, 2), ((33 : Real)/20, 2)] : List (Real × Nat))
      = ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 1)] : List (Real × Nat)) := by
  show (match eqb ((7 : Real)/5) ((43 : Real)/20) with
        | true  => ((7 : Real)/5, 2 + 1) :: _
        | false => ((7 : Real)/5, 2) :: addAt eqb ((43 : Real)/20) 1 _)
      = _
  rw [eqb_AC]
  show ((7 : Real)/5, 2) ::
        (match eqb ((33 : Real)/20) ((43 : Real)/20) with
         | true  => ((33 : Real)/20, 2 + 1) :: _
         | false => ((33 : Real)/20, 2) :: addAt eqb ((43 : Real)/20) 1 _)
      = _
  rw [eqb_BC]
  rfl

theorem addAt_C2 :
    addAt eqb ((43 : Real)/20) 1
        ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 1)] : List (Real × Nat))
      = ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2)] : List (Real × Nat)) := by
  show (match eqb ((7 : Real)/5) ((43 : Real)/20) with
        | true  => ((7 : Real)/5, 2 + 1) :: _
        | false => ((7 : Real)/5, 2) :: addAt eqb ((43 : Real)/20) 1 _)
      = _
  rw [eqb_AC]
  show ((7 : Real)/5, 2) ::
        (match eqb ((33 : Real)/20) ((43 : Real)/20) with
         | true  => ((33 : Real)/20, 2 + 1) :: _
         | false => ((33 : Real)/20, 2) :: addAt eqb ((43 : Real)/20) 1 _)
      = _
  rw [eqb_BC]
  show ((7 : Real)/5, 2) :: ((33 : Real)/20, 2) ::
        (match eqb ((43 : Real)/20) ((43 : Real)/20) with
         | true  => ((43 : Real)/20, 1 + 1) :: []
         | false => ((43 : Real)/20, 1) :: addAt eqb ((43 : Real)/20) 1 [])
      = [((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2)]
  rw [eqb_CC]

theorem addAt_D1 :
    addAt eqb ((12 : Real)/5) 1
        ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2)] : List (Real × Nat))
      = ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2),
          ((12 : Real)/5, 1)] : List (Real × Nat)) := by
  show (match eqb ((7 : Real)/5) ((12 : Real)/5) with
        | true  => ((7 : Real)/5, 2 + 1) :: _
        | false => ((7 : Real)/5, 2) :: addAt eqb ((12 : Real)/5) 1 _)
      = _
  rw [eqb_AD]
  show ((7 : Real)/5, 2) ::
        (match eqb ((33 : Real)/20) ((12 : Real)/5) with
         | true  => ((33 : Real)/20, 2 + 1) :: _
         | false => ((33 : Real)/20, 2) :: addAt eqb ((12 : Real)/5) 1 _)
      = _
  rw [eqb_BD]
  show ((7 : Real)/5, 2) :: ((33 : Real)/20, 2) ::
        (match eqb ((43 : Real)/20) ((12 : Real)/5) with
         | true  => ((43 : Real)/20, 2 + 1) :: _
         | false => ((43 : Real)/20, 2) :: addAt eqb ((12 : Real)/5) 1 _)
      = _
  rw [eqb_CD]
  rfl

theorem addAt_D2 :
    addAt eqb ((12 : Real)/5) 1
        ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2),
          ((12 : Real)/5, 1)] : List (Real × Nat))
      = ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2),
          ((12 : Real)/5, 2)] : List (Real × Nat)) := by
  show (match eqb ((7 : Real)/5) ((12 : Real)/5) with
        | true  => ((7 : Real)/5, 2 + 1) :: _
        | false => ((7 : Real)/5, 2) :: addAt eqb ((12 : Real)/5) 1 _)
      = _
  rw [eqb_AD]
  show ((7 : Real)/5, 2) ::
        (match eqb ((33 : Real)/20) ((12 : Real)/5) with
         | true  => ((33 : Real)/20, 2 + 1) :: _
         | false => ((33 : Real)/20, 2) :: addAt eqb ((12 : Real)/5) 1 _)
      = _
  rw [eqb_BD]
  show ((7 : Real)/5, 2) :: ((33 : Real)/20, 2) ::
        (match eqb ((43 : Real)/20) ((12 : Real)/5) with
         | true  => ((43 : Real)/20, 2 + 1) :: _
         | false => ((43 : Real)/20, 2) :: addAt eqb ((12 : Real)/5) 1 _)
      = _
  rw [eqb_CD]
  show ((7 : Real)/5, 2) :: ((33 : Real)/20, 2) :: ((43 : Real)/20, 2) ::
        (match eqb ((12 : Real)/5) ((12 : Real)/5) with
         | true  => ((12 : Real)/5, 1 + 1) :: []
         | false => ((12 : Real)/5, 1) :: addAt eqb ((12 : Real)/5) 1 [])
      = [((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2), ((12 : Real)/5, 2)]
  rw [eqb_DD]

/-! ### ★ `goN` 走完 8 条的**确切结果** -/

/-- **★ 合并版推前的核心计算**：`goN` 8 步后 = **4 条、权重 `[2, 2, 2, 2]`**。

  推导（每一步都是 `addAt` 的定义式 + 上面对应的一条 `eqb_*`）：

  ```
  步1  7/5   ⟹ [(7/5, 1)]
  步2  7/5   ⟹ [(7/5, 1+1)]                                    ← 合并（eqb_AA）
  步3  33/20 ⟹ [(7/5, 2), (33/20, 1)]                          （eqb_AB 判假）
  步4  33/20 ⟹ [(7/5, 2), (33/20, 2)]                          ← 合并（eqb_BB）
  步5  43/20 ⟹ [(7/5, 2), (33/20, 2), (43/20, 1)]              （eqb_AC/BC 判假）
  步6  43/20 ⟹ […, (43/20, 2)]                                 ← 合并（eqb_CC）
  步7  12/5  ⟹ […, (12/5, 1)]                                  （eqb_AD/BD/CD 判假）
  步8  12/5  ⟹ [(7/5, 2), (33/20, 2), (43/20, 2), (12/5, 2)]   ← 合并（eqb_DD）
  ```

  **超出定义之处**：`goN` 的方程只说「同像权重相加」，对**最终表的形状**一个字没说。
  本条把 8 步走完的**确切表**交出来，且是**逐步手算**的——
  `rawMap` 在同一投影下给出的是 `8` 条、权重全 `1`（见 `raw_wt`）。 -/
theorem goN_merge8 :
    goN eqb fe ([] : List (Real × Nat)) synthLaw.vals synthLaw.wt
      = [((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2), ((12 : Real)/5, 2)] := by
  rw [lawPostVals, lawPostWt]
  show goN eqb fe ([] : List (Real × Nat))
      ([{ eps := (-1/2 : Real), w := (-1 : Real) }, { eps := (-1/2 : Real), w := (1 : Real) },
        { eps := (-1/4 : Real), w := (-1 : Real) }, { eps := (-1/4 : Real), w := (1 : Real) },
        { eps := (1/4 : Real), w := (-1 : Real) }, { eps := (1/4 : Real), w := (1 : Real) },
        { eps := (1/2 : Real), w := (-1 : Real) }, { eps := (1/2 : Real), w := (1 : Real) }] : List SynthE)
      [1, 1, 1, 1, 1, 1, 1, 1] = _
  repeat' rw [goN_cons]
  rw [goN_nil]
  rw [show fe { eps := (-1/2 : Real), w := (-1 : Real) } = (7 : Real)/5 from fe1]
  rw [show fe { eps := (-1/2 : Real), w := (1 : Real) } = (7 : Real)/5 from fe2]
  rw [show addAt eqb ((7 : Real)/5) 1 ([] : List (Real × Nat))
        = ([((7 : Real)/5, 1)] : List (Real × Nat)) from addAt_A1]
  rw [show addAt eqb ((7 : Real)/5) 1 ([((7 : Real)/5, 1)] : List (Real × Nat))
        = ([((7 : Real)/5, 2)] : List (Real × Nat)) from addAt_A2]
  rw [show fe { eps := (-1/4 : Real), w := (-1 : Real) } = (33 : Real)/20 from fe3]
  rw [show fe { eps := (-1/4 : Real), w := (1 : Real) } = (33 : Real)/20 from fe4]
  rw [show addAt eqb ((33 : Real)/20) 1 ([((7 : Real)/5, 2)] : List (Real × Nat))
        = ([((7 : Real)/5, 2), ((33 : Real)/20, 1)] : List (Real × Nat)) from addAt_B1]
  rw [show addAt eqb ((33 : Real)/20) 1
        ([((7 : Real)/5, 2), ((33 : Real)/20, 1)] : List (Real × Nat))
        = ([((7 : Real)/5, 2), ((33 : Real)/20, 2)] : List (Real × Nat)) from addAt_B2]
  rw [show fe { eps := (1/4 : Real), w := (-1 : Real) } = (43 : Real)/20 from fe5]
  rw [show fe { eps := (1/4 : Real), w := (1 : Real) } = (43 : Real)/20 from fe6]
  rw [show addAt eqb ((43 : Real)/20) 1
        ([((7 : Real)/5, 2), ((33 : Real)/20, 2)] : List (Real × Nat))
        = ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 1)] : List (Real × Nat))
      from addAt_C1]
  rw [show addAt eqb ((43 : Real)/20) 1
        ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 1)] : List (Real × Nat))
        = ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2)] : List (Real × Nat))
      from addAt_C2]
  rw [show fe { eps := (1/2 : Real), w := (-1 : Real) } = (12 : Real)/5 from fe7]
  rw [show fe { eps := (1/2 : Real), w := (1 : Real) } = (12 : Real)/5 from fe8]
  rw [show addAt eqb ((12 : Real)/5) 1
        ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2)] : List (Real × Nat))
        = ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2),
            ((12 : Real)/5, 1)] : List (Real × Nat)) from addAt_D1]
  rw [show addAt eqb ((12 : Real)/5) 1
        ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2),
          ((12 : Real)/5, 1)] : List (Real × Nat))
        = ([((7 : Real)/5, 2), ((33 : Real)/20, 2), ((43 : Real)/20, 2),
            ((12 : Real)/5, 2)] : List (Real × Nat)) from addAt_D2]

/-- **★ 合并版预测的像点表 = `[7/5, 33/20, 43/20, 12/5]`**（4 条，去重）。

  **超出定义之处**：`pushMerge` 的定义只说「同像权重相加」，对**最终是哪几个像点**、
  它们的**顺序**一个字没说。本条通过 `goN_merge8`（逐步手算）把结果钉成
  **4 个具体实数**：去重了、按首次出现排序、且首项是 `7/5`（对应最小的 `ε`）。

  ⚠ 这是**旧 demo 给不出的东西**：旧 demo 的 `pred₁.vals` 有 8 条、其中 4 对重复。 -/
theorem merged_vals :
    predM.vals = [(7 : Real)/5, (33 : Real)/20, (43 : Real)/20, (12 : Real)/5] := by
  rw [predM_eq_push, projM_eq_fe, pushMerge]
  show keyOf (goN eqb fe ([] : List (Real × Nat)) synthLaw.vals synthLaw.wt) = _
  rw [goN_merge8]
  rfl

/-- **合并版预测的权重表 = `[2, 2, 2, 2]`**（每个像点两条原像，`1 + 1 = 2`）。

  **超出定义之处**：定义只说「同像相加」。本条把 4 个像点**各自**的质量算成 `2`：
  这才是「`7/5` 处的概率是 `2/8`」的分子。 -/
theorem merged_wt : predM.wt = ([2, 2, 2, 2] : List Nat) := by
  rw [predM_eq_push, projM_eq_fe, pushMerge]
  show wtOf (goN eqb fe ([] : List (Real × Nat)) synthLaw.vals synthLaw.wt) = _
  rw [goN_merge8]
  rfl

/-- **合并版预测的像点条数 = 4**（8 条原像 → 4 个像点，**没有重复**）。 -/
theorem merged_len : predM.vals.length = 4 := by
  rw [merged_vals]
  rfl

/-- **④ 合并版的点预测（首项）= `7/5`**。 -/
def pointPredM : Real := predM.vals.headD 0

/-- 点预测的具体值：`7/5`。 -/
theorem pointPredM_val : pointPredM = (7 : Real) / 5 := by
  show predM.vals.headD 0 = (7 : Real)/5
  rw [merged_vals]
  rfl

/-! ===========================================================================
  §4  ★ 核心：同一实例上「旧版 vs 合并版」的具体数值对比
  =========================================================================== -/

/-- **旧版预测分布**（= `SyntheticRun.pred₁` 的定义式，**此处只为对比而重述**）。

  ⚠ `SyntheticRun.pred₁` 在 `FateV2.Demo` 命名空间内，本文件同命名空间，
  故直接引用 `pred₁` 即可；这个名字只是让「对比」两端**同一层**地摆开。 -/
def predRaw : DiscLaw Real := pred₁

/-- **旧版与原版定义逐字相同**（`rfl`）：`predRaw` 不是另写一份 `rawMap`。 -/
theorem predRaw_eq : predRaw = Predict.rawMap synthLaw stepState := rfl

/-- **旧版的权重表 = `[1,1,1,1,1,1,1,1]`**（8 条，**没有**相加）。

  **超出定义之处**：`rawMap` 的定义「权重原样保留」是一句话；
  本条把它算成 `8` 个 `1`，并与合并版的 `[2,2,2,2]`（`merged_wt`）**逐项可比**。 -/
theorem raw_wt : predRaw.wt = ([1, 1, 1, 1, 1, 1, 1, 1] : List Nat) := by
  have h : predRaw = rawMap synthLaw (fun e : SynthE => (9 : Real)/10 * (1 : Real) + (1 : Real) + e.eps) := by
    rw [predRaw_eq]; rfl
  rw [h, rawMap, lawPostWt]

/-- **★ 核心对比：同一实例上，合并版与旧版的首项质量、条数、总质量**

  | 量 | 旧版 `rawMap` | 合并版 `pushMerge` |
  |---|---|---|
  | 首项（`headD 0`） | **`1`** | **`2`** |
  | 像点条数 | `8` | `4` |
  | 总质量 | `8` | `8` |

  **超出定义之处**：`pushMerge` 与 `rawMap` 的定义**互不相干**；本条第 ①③ 两行
  是 `pushMerge`/`rawMap` 的**真实计算**（`merged_wt` / `raw_wt` / 表的长度），
  第 ② 行是两者之**差**——这个差在定义里没有任何痕迹。

  ⚠ **这里必须说清「差在哪」**：两版的总质量都是 `8`（`rawMap_total` 是 `rfl`，
  所以**账本永远看不出来**）。差在「**同一个像点 `7/5` 记了几条**」：
  旧版记 `2` 条、各权重 `1`；合并版记 `1` 条、权重 `1 + 1 = 2`。
  于是按位置读「首项的质量」：旧版拿到 `1`（`= 1/8`），正确值 `2`（`= 2/8 = 1/4`）。 -/
theorem merge_vs_raw_same_instance :
    predRaw.wt.headD 0 = 1 ∧
    predM.wt.headD 0 = 2 ∧
    predRaw.vals.length = 8 ∧
    predM.vals.length = 4 ∧
    predRaw.total = 8 ∧
    predM.total = 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [raw_wt]; rfl
  · rw [merged_wt]; rfl
  · show (pred₁.vals).length = 8
    rw [show pred₁.vals = (synthLaw.vals).map stepState from rfl, List.length_map]
    rw [lawPostVals]
    rfl
  · exact merged_len
  · show predRaw.total = 8
    rw [predRaw_eq, rawMap_total]
    exact lawPostTotal
  · show predM.total = 8
    rw [show predM.total = predM.wt.sum from rfl, merged_wt]
    rfl

/-- **★ 否定性结论的具体数值：旧版「按位置读单点质量」少了 `1`，占 `1/4`。**

  三件事一次性算清：
  * 旧版首项质量 `1`、合并版首项质量 `2` ⟹ **差额恰为 `1`**；
  * 两版总质量都是 `8` ⟹ **账本凑得平**（`rawMap_total` 看不出来）；
  * 正确的单点概率 `= 2/8 = 1/4`，旧版读出 `1/8` ⟹ **占 `1/4` 的质量被记到了另一条上**。

  **超出定义之处**：`rawMap` 的定义里没有任何关于「按位置读会读错」的内容，
  `rawMap_total` 更是把它掩过去了。本定理是**否定性**结论的**具体数值**形式，
  且差额 `1` 与比例 `1/4` 都由前两条定理（`raw_wt` / `merged_wt`）真的算出来，
  不是 `decide` 或假设。 -/
theorem raw_first_mass_defect :
    predM.wt.headD 0 - predRaw.wt.headD 0 = 1 ∧
    predM.total = 8 ∧
    predRaw.total = 8 ∧
    (2 : Nat) * 4 = 8 ∧
    (1 : Nat) * 4 = 4 := by
  refine ⟨?_, merge_vs_raw_same_instance.2.2.2.2.2, merge_vs_raw_same_instance.2.2.2.2.1,
          by decide, by decide⟩
  rw [merge_vs_raw_same_instance.2.1, merge_vs_raw_same_instance.1]

/-- **旧版留重复、合并版去重**（像点表不等）。

  **超出定义之处**：这是「bug 的确切内容」——不是总质量不同（那永远相同），
  而是**同一个像点在结果里出现了几次**。`7/5` 旧版出现 `2` 次。 -/
theorem raw_ne_merge_vals : predRaw.vals ≠ predM.vals := by
  rw [merged_vals]
  intro h
  have h2 : (predRaw.vals.length) = 4 := by rw [h]; rfl
  rw [show predRaw.vals.length = 8 from merge_vs_raw_same_instance.2.2.1] at h2
  exact absurd h2 (by decide)

/-! ===========================================================================
  §5  ★ 质量守恒（在**本实例**上算成数）
  =========================================================================== -/

/-- **★ 合并版预测的总质量 = 原律的总质量 = `8`**。

  `predictM_total`（T13）是一般定理；本条的独立价值在**算**：
  合并版的两张表是 `merged_vals` / `merged_wt`，其权重和 `2 + 2 + 2 + 2 = 8`
  是**手算**出来的，且这个 `8` 与 `lawPostTotal`（原律 `8`）**对上了**。

  **超出定义之处**：守恒定理 + 具体数值 = 「换成合并版之后，预测**仍然**是一个
  总质量为 `8` 的离散律，只是不再有重复像点」。定义里没有这一条。 -/
theorem merged_total_eq_law : predM.total = synthLaw.total ∧ predM.total = 8 := by
  refine ⟨?_, ?_⟩
  · rw [predM_eq_push]
    exact pushMerge_total (fun e => projState (evalFrom M e s0 order)) synthLaw discPushFamily_wf
  · show predM.wt.sum = 8
    rw [merged_wt]
    rfl

/-- **旧版的总质量也是 `8`**——这就是 `rawMap_total`（`rfl`）**看不出问题**的原因。

  **超出定义之处**：本条与 `merged_total_eq_law` 并列，恰好说明
  「总质量守恒」这个**检查项本身不足以**发现 bug。缺的是「条数」与「单点质量」。 -/
theorem raw_total_also_eight : predRaw.total = 8 :=
  merge_vs_raw_same_instance.2.2.2.2.1

/-- **合并版按位置读的单点质量 = `2`，占总量 `8` 的 `1/4`**。

  用 `Nat` 写比例以免引入除法：`2 · 4 = 8` 即「`2` 是 `8` 的四分之一」。 -/
theorem merged_first_mass_ratio :
    predM.wt.headD 0 = 2 ∧ predM.wt.headD 0 * 4 = predM.total := by
  refine ⟨merge_vs_raw_same_instance.2.1, ?_⟩
  rw [merge_vs_raw_same_instance.2.1, merge_vs_raw_same_instance.2.2.2.2.2]

/-! ===========================================================================
  §6  与旧 demo 的关系（两条：单射时**一致**、本例**不一致**）
  =========================================================================== -/

/-- **★ 单射时推前保总质量不变**（一般定理，`InjOn` 版）。

  这是 T4 `pushMerge_eq_rawMap_of_injOn` 的**直接应用**，独立价值在于
  **本文件把它摆在同一页上**：它说明「不合并」的那一支**有它的边界**——
  边界之内（支撑上单射）旧做法不是 bug。本 demo 落在边界**之外**（`img_ne_inj`）。

  **超出定义之处**：两族定义毫无关系（一个照抄、一个求和）；本条把「什么时候
  二者一致」写成**可检验的前件**（`InjOn f L`），而不是笼统说旧版对或错。

  ⚠ **本条没做到的事（如实登记）**：**没有**把结论加强成「两张表逐条相等」。
  那需要一个关于 `goN` 的一般归纳（单射 ⟹ `addAt` 永不进入合并分支），
  本文件**没写**；这里只给**总质量**层面的一致性，与 T4 的结论强度相同。
  要更强的版本请作为后续专项单独立项。 -/
theorem merge_eq_raw_on_inj {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α)
    (hinj : InjOn f L) (hlen : L.vals.length = L.wt.length) :
    (pushMerge f L).total = (rawMap L f).total :=
  pushMerge_eq_rawMap_of_injOn f L hinj hlen

/-- **★ 本例的投影不单射 ⟹ 两版结果真的不同**（表不同 + 首项质量不同）。

  与 `merge_eq_raw_on_inj` 合起来，把 `rawMap` 的**适用边界**在本 demo 上钉死：
  * 单射（如 `projState` 若只看 `eps` 且 `eps` 互异）⟹ 两版一致；
  * **本 demo 的实际投影**（`w` 进不去）⟹ 两版差 `1`，占 `1/4`。

  **超出定义之处**：定义里既没说「什么时候一样」，也没说「什么时候不一样」。
  两条合起来才是完整回答——本 demo 落在**第二支**。 -/
theorem demo_not_inj_so_differs :
    predRaw.vals ≠ predM.vals ∧
    predM.wt.headD 0 - predRaw.wt.headD 0 = 1 :=
  ⟨raw_ne_merge_vals, raw_first_mass_defect.1⟩

/-! ===========================================================================
  §7  端到端：⑤ 导出 → ⑥ 误差 → ⑦ 裁决 K → ⑧ 回写 → ⑨ 再预测
  =========================================================================== -/

/-- **⑤ 导出（沿用旧 demo 的注册表）**：3 个模态全部导出。 -/
theorem merge_export_count : out₁.count = 3 := run_registry_card.2

/-- **★ 点预测在两版下相同**（都是 `7/5`）。

  **超出定义之处**：这条不是「合并没用」，而是把 bug 的**位置**钉死：
  合并只改「同像的质量怎么记」，不改**首项是哪个像点**（最小 `ε` 那次转移）。
  ⟹ 任何**只看首项**的下游（`SyntheticRun.pointPred` 的全部数值结论）
  **都不受这个 bug 影响**——推前的 bug 藏在分布里，不藏在点预测里。 -/
theorem merge_vs_raw_pointPred_eq : pointPredM = pointPred := by
  rw [pointPredM_val, pointPred_val]

/-- **⑥ 合并版残差 = `−1/10`**（观测 `13/10` 减合并版点预测 `7/5`）。

  **超出定义之处**：残差是 `residual (观测) (点预测)`；本条把合并版的点预测
  代进去，算成**与旧 demo 逐字相同**的数。这不是「重复旧结论」，
  而是**证明**「换成合并推前之后，误差一步不变」——即 bug 不在误差层。 -/
theorem merged_err : residual (v₁ SynthV.obs) pointPredM = -(1 : Real)/10 := by
  rw [show residual (v₁ SynthV.obs) pointPredM = err₁ from by
        rw [show err₁ = residual (v₁ SynthV.obs) pointPred from rfl, merge_vs_raw_pointPred_eq]]
  exact run_err.trans (by norm_num)

/-- **⑦ 合并版下裁决 K 仍判不合格**（`|e| = 1/10`，`σ = 1/2`，`σ − |e| = 2/5 > 1/4`）。 -/
theorem merged_verdict_fails : ¬ accepts sigma epsTol |residual (v₁ SynthV.obs) pointPredM| := by
  rw [merge_vs_raw_pointPred_eq]
  exact run_verdict_fails

/-- **⑧ 回写后的残差 = `−1/20`**（`η = 1/2`，`(1 − 1/2)·(−1/10)`）。 -/
theorem merged_err_after :
    residual (v₁ SynthV.obs) (writeBack eta (v₁ SynthV.obs) pointPredM) = -(1 : Real)/20 := by
  rw [writeBack_residual, merged_err]
  unfold eta
  norm_num

/-- **⑨ 回写后误差恰减半**：`|e'| = (1/2)·|e|`。 -/
theorem merged_shrink :
    |residual (v₁ SynthV.obs) (writeBack eta (v₁ SynthV.obs) pointPredM)|
      = (1/2) * |residual (v₁ SynthV.obs) pointPredM| := by
  rw [merged_err_after, merged_err]
  norm_num

/-- **★ 端到端：一条定理串起合并版的整条链（建模 → 求值 → 预测 → 导出 → 误差 → 裁决 K → 回写）**

  同时断言 7 件事：

  1. `v₁ state = 7/5`、`v₁ obs = 13/10`（求值，直接复用旧 demo）
  2. 导出 **3** 个模态（`out₁.count = 3`）
  3. **合并版预测的分布**：`4` 条像点、权重 `[2,2,2,2]`、总质量 `8`（这是旧 demo 给不出的）
  4. 残差 `−1/10`、裁决 K **不合格**、回写后 `|e'| = (1/2)|e|`

  **超出定义之处**：它不引入新数学；它的内容是「**7 个独立结论在同一个具体实例上
  无矛盾地同时成立**」。这不是自动的：若合并推前把 `7/5` 处记成 `3`（多记一条），
  条件 3 立刻为假；若 `evalFrom` 的求值顺序错位，条件 1 为假；
  若 `accepts` 的符号写反，条件 4 的「不合格」为假。

  它**同时**包含**否定项**（裁决 K 不过）与**肯定项**（回写收缩成功、分布无重复像点），
  以及一条**区别项**（合并版的 `4 条 / 权重 2`，旧版是 `8 条 / 权重 1`）。 -/
theorem merged_chain_end_to_end :
    v₁ SynthV.state = (7 : Real)/5 ∧
    v₁ SynthV.obs = (13 : Real)/10 ∧
    out₁.count = 3 ∧
    predM.vals.length = 4 ∧
    predM.wt = ([2, 2, 2, 2] : List Nat) ∧
    predM.total = 8 ∧
    residual (v₁ SynthV.obs) pointPredM = -(1 : Real)/10 ∧
    ¬ accepts sigma epsTol |residual (v₁ SynthV.obs) pointPredM| ∧
    |residual (v₁ SynthV.obs) (writeBack eta (v₁ SynthV.obs) pointPredM)|
      = (1/2) * |residual (v₁ SynthV.obs) pointPredM| :=
  ⟨run_state, run_obs, merge_export_count, merged_len, merged_wt, merged_total_eq_law.2,
   merged_err, merged_verdict_fails, merged_shrink⟩

end

end FateV2.Demo
