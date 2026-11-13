import FateWorld.FateV2.Predict.PushMerge
import Mathlib.Tactic

/-!
  # Predict · PushFamilyMerge —— 把 `discPushFamily` 换成**合并同像权重**的版本

  ## 迁移登记
  - 来源：新写（本文件）
  - 动作：C 重写（新文件）
  - 对应环节：F6-01（预测）、F6-04（下一步分布 `xNextDist`）、F4-19（`Pred`）
  - 依赖裁决：**D-009**（预测 = 在模型空间里演化）、**D-019**（`Noise` 是参数）、
              **D-022**（反空泛：每条定理写「比定义多说了什么」）
  - 改动：新文件。**没有改 `PushFamily` 结构、没有改 `predict` 的签名**（见 §一）。
  - 状态：已验证（`_check.ps1 -Group A` 通过，见 `_报告/T13-进度.md`）

  ## 一、方案：为什么选「丙」，以及丙到底指什么

  ### 丙的原始说法不成立（这是本文件的第一条**实测**结论）

  任务书说：*「`T U` 已经能编码合并后的结果，改 `discPushFamily` 的实现即可」*。
  前半句对——`pushMerge` 的返回类型就是 `DiscLaw β`。但后半句**在 Lean 里不成立**：

  ```lean
  def discPushFamily : PushFamily DiscLaw SynthE Real Real where
    push := fun L f => pushMerge f L          -- ← 报错：没有 DecidableEq Real
  ```

  `pushMerge` 的实例参数在**函数体内部**做实例搜索，`Real.decidableEq` 是
  `noncomputable` 实例，**不会**被自动拾取。⟹ 单改函数体、结构不动，写不出来。

  ### 丙的正确版本

  『**实例不必进 `push` 的类型，可以进 `PushFamily` 这个值的上下文。**』

  ```lean
  noncomputable def discPushFamilyM (Z : Type) [DecidableEq Z] :
      PushFamily DiscLaw Real Z Z where
    push := fun L f => pushMerge f L        -- ← 实例由「值」这一层捕获
  ```

  结构**一个字段都没加**，`predict` **一个字符都没改**，`discPushFamily`
  由「另一个值」取代。承诺只加在**要让合并发生的那一个 `Z`** 上，
  不是加在「所有 `Z`」上。

  ### 与甲、乙的对比

  | 方案 | 判定 | 理由 |
  |---|---|---|
  | **甲**：给 `PushFamily` 加 `[DecidableEq Z]` 字段 | ❌ | `Z` 是结构参数，加了等于强迫**所有**投影目标可判等。测度侧（`SCM.ModelOnMeasure`，`Measure.map` 只需 `MeasurableSpace`）就再也建不出 `PushFamily`——为特例牺牲整个参数化，违 D-019 |
  | **乙**：新增 `PushFamilyM` 结构 | ❌ | 会产生**两个** `predict`（同签名、异语义），「默认拿到哪个」变成隐式约定 |
  | **丙**：结构不改、只换值 | ✅ | 改动面 = 本文件 + `Predict.lean` 两条新增；`predict` 公开签名逐字未变；「用哪个推前」变成**显式传参** |

  ### 丙的代价（如实登记）

  1. **`discPushFamilyM` 是 `noncomputable`**：`Z = Real` 时捕获 `Real.decidableEq`，
     实测 `#eval` 报 `depends on 'Real.decidableEq', which is 'noncomputable'`。
     ⟹ **「合并版可以 `#eval`」做不到**。`rawMap` 可计算正因为**它不判等、不合并**。
  2. 于是本文件用**三种载体**分层实证：`Real`（与 `predict` 同型，只做定理层）、
     `ℚ`（可计算）、`Nat`（**零公理**，见 §9）。

  ## 二、结论（先给答案）

  | 问题 | 答案 | 定理 |
  |---|---|---|
  | 合并族的 `push` 是什么 | **就是 T4 的 `pushMerge`** | `discPushFamilyM_push` |
  | 合并推前保总质量吗 | **是** | **`pushMerge_total_wf`** / `pushMerge_total_sumN` |
  | 合并版预测保总质量吗 | **是**，等于原律总质量 | **`predictM_total`** / `predictM_total_sumN` |
  | 旧版是合并版的特例吗 | **是**：支撑上单射 ⟹ 质量一致 | `discPushFamilyM_eq_discPushFamily_total` |
  | 旧版丢质量吗 | **是**：首项读 `2`、正确 `5`、**少 `3`（占 `3/5`）** | **`discPushFamily_drops_mass`** |
  | 零公理版有吗 | **有**（`Nat` 侧全程 `rfl`） | **`nDropsMass`**、`nMergeSumN` |

  ## 三、口径

  1. **`DiscLaw` 按位置对齐全表**（与 `PushMerge` 文件头一致）。守恒定理的前件
     一律写成 `DiscLawWellFormed L`（`Predict.lean` §2.1）。**不收窄成 `≤`**。
  2. **反例沿用 T4 的 `dupLaw` / `collapse`**（`wt = [2, 3]`、非单射塌成一点）。

  ## 四、★ 公理账本的**实测事实**（比红线清单更硬，务必先看）

  **任何类型里含 `Real` 的声明，`#print axioms` 一律报三条公理**——与证明写法无关：

  ```lean
  theorem tSelf : (1 : Real) = 1 := rfl
  -- 'tSelf' depends on axioms: [propext, Classical.choice, Quot.sound]
  theorem tNat : (1 : Nat) = 1 := rfl
  -- 'tNat' does not depend on any axioms
  ```

  `Rat` 亦然（`Q := Rat` 的定义带 `Quot.sound`）。⟹
  **「零公理」只能落在 `Nat` / 自定义 inductive 上**。本文件因此分成三层：
  `Real` 侧（§2–§7，账面三公理）、`ℚ` 侧（§8，账面 `propext;Quot.sound`）、
  `Nat` 侧（§9，**账面为空**）。三层**结论相同**，这本身就是结论：
  **带公理的从来是账本（`List.sum` / `Real` / `Rat`），不是合并算法。**

  ## 五、超出定义之处（D-022）

  * `discPushFamilyM_push`：定义只写「`push` 是 `pushMerge`」，本条把它**作为等式**交出。
  * `pushMerge_wf` / `pushMerge_total_wf` / `predictM_total`：定义只说「同像相加」，
    **没写**「总和不变」。三条把它钉住，且前件只用语义谓词 `DiscLawWellFormed`。
  * `discPushFamilyM_eq_discPushFamily_total`：定义里**没有**「何时不合并是对的」；
    本条给出**充分条件**（支撑上单射），而不是笼统说旧版错。
  * `discPushFamily_drops_mass`：**否定性**结论的具体数值（`2` 对 `5`，差 `3`）。
  * `nDropsMass`：**零公理**的同一结论——把「账带的公理」与「算法的公理」分开。

  ## 六、本文件没做的

  1. **`DiscLaw` 的 `funext` 引理没证**（带 `Quot.sound`）。一律展开成 `vals` / `wt` 字段等式。
  2. **`discPushFamilyM` 的 `#eval` 没做**（见 §一 代价 1）；可计算实证走 `ℚ` / `Nat`。
  3. **没改 `Demo/SyntheticRun.lean`**（只读）：它仍用 `Predict.rawMap`，
     故其 8 条预测里**有 4 对重复像点**。要换需改 `SyntheticRun.lean:133`
     为 `discPushFamilyM Real |>.push synthLaw stepState`。
  4. **没做 `DiscLaw` 意义上的归一化**（`DiscLaw` 没有除法），一律用「总质量」与「条数」两种账。
-/

namespace FateV2.Predict

open FateV2.Modeling FateV2.Model

/-! ===========================================================================
  §0  记号：可计算的目标类型
  =========================================================================== -/

/-- 反例用的「目标类型」：取 `ℚ`。

  `Real.decidableEq` 不可计算，故 `discPushFamilyM Real` 的 `push` 跑不起来。
  `ℚ` 判等可计算，本文件的具体数值实证放在 `ℚ`（§8）与 `Nat`（§9）上。
  （⚠ `Rat` 的定义本身带 `Quot.sound`，故 §8 的账面不是零；零公理在 §9。） -/
abbrev Q : Type := Rat

/-! ===========================================================================
  §1  合并推前族
  =========================================================================== -/

/-- **合并同像权重的推前族**：`DiscLaw` 上**正确**的推前。

  `push` 就是 `PushMerge.pushMerge`——**与 T4 的定义同一份，不是另写一份**。
  `DecidableEq Z` 由**结构体这一层**绑定（`push` 在体内捕获），
  所以 `PushFamily.push` 的字段类型 `T E → (E → Z) → T U` **一个字不用改**。 -/
noncomputable def discPushFamilyM (Z : Type) [DecidableEq Z] :
    PushFamily DiscLaw Real Z Z where
  push := fun L f => pushMerge f L

/-- **合并族的 `push` 就是 T4 的 `pushMerge`**。

  **超出定义之处**：`discPushFamilyM` 是结构体字面量，「它的 `push` 等于 `pushMerge`」
  要展开 `PushFamily.push` 的投影才陈述得成等式。下游若要确认
  「合并族用的是 T4 那份实现、没有偷偷换算法」，引本条即可。 -/
theorem discPushFamilyM_push {Z : Type} [DecidableEq Z]
    (f : Real → Z) (L : DiscLaw Real) :
    (discPushFamilyM Z).push L f = pushMerge f L := rfl

/-- **合并后的取值表 = `pushMerge` 的取值表**。 -/
theorem discPushFamilyM_vals {Z : Type} [DecidableEq Z]
    (f : Real → Z) (L : DiscLaw Real) :
    ((discPushFamilyM Z).push L f).vals = (pushMerge f L).vals := rfl

/-- **合并后的权重表 = `pushMerge` 的权重表**。 -/
theorem discPushFamilyM_wt {Z : Type} [DecidableEq Z]
    (f : Real → Z) (L : DiscLaw Real) :
    ((discPushFamilyM Z).push L f).wt = (pushMerge f L).wt := rfl

/-! ===========================================================================
  §2  ★ 核心 1：合并族的推前保总质量
  =========================================================================== -/

/-- **合并推前保总质量（`DiscLawWellFormed` 版）**。

  与 T4 的 `pushMerge_total` 同一条结论，前件改写成 `Predict.lean` §2.1 的
  语义谓词——于是读法从「表等长 ⟹ 守恒」（实现约束）变成「合法律 ⟹ 守恒」（语义约束）。

  **超出定义之处**：见 `PushMerge.pushMerge_total`。本条的独立价值在**前件的名字**：
  `DiscLawWellFormed` 是 T13 新增的谓词，不是「某个列表恰好等长」。 -/
theorem pushMerge_wf {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α)
    (h : DiscLawWellFormed L) :
    (pushMerge f L).total = L.total :=
  pushMerge_total f L h

/-- **★ 合并族的质量守恒**：`L` 合法 ⟹ `(discPushFamilyM Z).push L f` 的总质量 = `L.total`。

  **超出定义之处**：`discPushFamilyM` 的定义**只**说「`push` 调 `pushMerge`」，
  对总质量一个字没提。本条把它接回 `DiscLaw.total` 这个既有账本，
  于是「换成合并版之后，预测还是一个概率分布」第一次有了定理。
  与 `rawMap_total`（`rfl`）对照：那条也成立，但**原因是它根本没合并**；
  本条成立原因是**每笔权重只记一次、表没被截断**（`addAt_sum` + `goN_sum`）。

  ⚠ 账面含 `propext`——继承自只读定义 `DiscLaw.total := L.wt.sum`。零公理版见 §9。 -/
theorem pushMerge_total_wf {Z : Type} [DecidableEq Z]
    (f : Real → Z) (L : DiscLaw Real) (h : DiscLawWellFormed L) :
    ((discPushFamilyM Z).push L f).total = L.total :=
  pushMerge_total f L h

/-! ===========================================================================
  §3  ★ 核心 2：用合并族 `predict`，总质量守恒
  =========================================================================== -/

/-- **用合并族预测 = 用 `pushMerge` 推前**（`rfl`）。

  **超出定义之处**：`predict` 的签名对推前族无约束；本条把
  `predict … discPushFamilyM` 这**一个**组合展开成 `pushMerge` 的直接调用，
  于是上层定理都不必再展开 `predict`。 -/
theorem predictM_eq
    (M : Model Real Real Real (DiscLaw Real)) (eval : Real → Real → Real)
    (project : (Real → Real) → Real) :
    predict M eval project (discPushFamilyM Real) =
      pushMerge (fun e => project (eval e)) M.P_U := rfl

/-- **★ 核心 2**：`predict` 用**合并族**，总质量 = 外生律总质量。

  前件只有一条：外生律 `M.P_U` 合法。于是「换成合并版后预测仍是合法律」
  对**任意模型、任意投影**成立——与 `eval` / `project` 长什么样**无关**。

  **超出定义之处**：`predict` 的定义只做一件事（把律沿 `project ∘ eval` 推前），
  **没有**任何关于「推前结果总质量」的内容。本条说它**恰好不动总质量**，
  且结论**不依赖投影是什么**——这正是「推前」一词的全部含义
  （D-009：预测在模型空间里演化，不能凭空造/灭概率）。 -/
theorem predictM_total
    (M : Model Real Real Real (DiscLaw Real)) (eval : Real → Real → Real)
    (project : (Real → Real) → Real)
    (h : DiscLawWellFormed M.P_U) :
    (predict M eval project (discPushFamilyM Real)).total = M.P_U.total := by
  rw [predictM_eq]
  exact pushMerge_total (fun e => project (eval e)) M.P_U h

/-- **合并族预测的取值表 = `pushMerge` 的取值表**。 -/
theorem predictM_vals
    (M : Model Real Real Real (DiscLaw Real)) (eval : Real → Real → Real)
    (project : (Real → Real) → Real) :
    (predict M eval project (discPushFamilyM Real)).vals
      = (pushMerge (fun e => project (eval e)) M.P_U).vals := rfl

/-! ===========================================================================
  §4  旧版是合并版的**特例**（支撑上单射时）
  =========================================================================== -/

/-- **单射时两族质量一致**：`discPushFamily` 是 `discPushFamilyM` 的特例。

  **超出定义之处**：两族在**定义**上毫无关系（一个照抄权重、一个求和）。
  本条给出**充分条件**（`f` 在 `L.vals` 上单射）之下总质量一致，
  于是「不合并」在这条边界内**不是 bug，是一个正好的实现**。 -/
theorem discPushFamilyM_eq_discPushFamily_total {Z : Type} [DecidableEq Z]
    (f : Real → Z) (L : DiscLaw Real)
    (hinj : InjOn f L) (h : DiscLawWellFormed L) :
    ((discPushFamilyM Z).push L f).total = (rawMap L f).total := by
  rw [discPushFamilyM_push]
  exact pushMerge_eq_rawMap_of_injOn f L hinj h

/-- **★ 换族不破坏既有结论**（`predict` 层，单射情形）。

  `predict … discPushFamily` 与 `predict … discPushFamilyM` 的总质量相同。

  **超出定义之处**：`predict` 对两个族一视同仁（都只是 `pf.push`）；
  本条说明在**本项目最关心的情形**（投影在支撑上单射）下换族**不影响**质量账。
  这是「升级安全性」的定理，不是「升级必要性」的定理。 -/
theorem predictM_total_eq_predict_total
    (M : Model Real Real Real (DiscLaw Real)) (eval : Real → Real → Real)
    (project : (Real → Real) → Real)
    (hinj : InjOn (fun e => project (eval e)) M.P_U)
    (h : DiscLawWellFormed M.P_U) :
    (predict M eval project (discPushFamilyM Real)).total
      = (predict M eval project
          ({ push := fun L f => rawMap L f } : PushFamily DiscLaw Real Real Real)).total := by
  rw [predictM_eq]
  show (pushMerge (fun e => project (eval e)) M.P_U).total
      = (rawMap M.P_U (fun e => project (eval e))).total
  exact pushMerge_eq_rawMap_of_injOn (fun e => project (eval e)) M.P_U hinj h

/-! ===========================================================================
  §5  ★ 核心 3：旧版**丢质量**（具体数值，与 T4 `rawMap_drops_mass` 对接）
  =========================================================================== -/

/-- **旧版在反例上的族**：`push = rawMap`——这正是 `discPushFamily.push` 在做的事。 -/
noncomputable def colsRaw : PushFamily DiscLaw TwoPt Nat Nat where
  push := fun L f => rawMap L f

/-- **旧版的像点表**：`[2, 2]`（同一条像点记了**两次**）。 -/
theorem colsRaw_vals : (colsRaw.push dupLaw collapse).vals = [2, 2] := rfl

/-- **旧版的权重表**：`[2, 3]`（**没有**相加，原样照抄）。 -/
theorem colsRaw_wt : (colsRaw.push dupLaw collapse).wt = [2, 3] := rfl

/-- **★ 核心 3**：旧版读「像点 `2` 处的质量」= `2`，正确值 `5`，**少了 `3`**。

  「读第一处的质量」用 `wt.headD 0`——正是 `Demo/SyntheticRun.lean` 里
  `pointPred : Real := pred₁.vals.headD 0` 的**点预测口径**。
  要害在此：**点预测取首项**时，`rawMap` 给出的不是 `2` 这个取值的质量，
  而是「第几条原像」的权重。

  | 量 | 旧版（`rawMap`） | 合并版（`pushMerge`） |
  |---|---|---|
  | 首项权重 | **`2`** | **`5`** |
  | 总质量 | `5` | `5` |
  | 像点条数 | `2` | `1` |

  **超出定义之处**：`rawMap` 的定义只说「换取值、照抄权重」，
  **没有**任何关于「按位置读会读少」的内容。本条把差额算成 `Nat`（`3`），
  并把「正确值」一并给出——这是**否定性**结论的具体数值。 -/
theorem discPushFamily_drops_mass :
    (colsRaw.push dupLaw collapse).wt.headD 0 = 2 ∧
    (pushMerge collapse dupLaw).wt.headD 0 = 5 ∧
    (colsRaw.push dupLaw collapse).total = 5 ∧
    (pushMerge collapse dupLaw).total = 5 ∧
    (pushMerge collapse dupLaw).wt.headD 0 - (colsRaw.push dupLaw collapse).wt.headD 0 = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **★ 丢质量（零公理版）**：同一结论，**不碰** `DiscLaw.total`。

  与 `discPushFamily_drops_mass` 要证的东西一样（首项 `2` 对 `5`），
  但 `#print axioms` 为**空**：`TwoPt` 与 `Nat` 都已可判等、可计算。 -/
theorem discPushFamily_drops_mass_sumN :
    (colsRaw.push dupLaw collapse).wt = [2, 3] ∧
    (pushMerge collapse dupLaw).wt = [5] ∧
    sumN (pushMerge collapse dupLaw).wt = sumN (colsRaw.push dupLaw collapse).wt ∧
    (sumN (pushMerge collapse dupLaw).wt, sumN (colsRaw.push dupLaw collapse).wt) = (5, 5) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **两族结果的像点表不同**：旧版留重复，合并版去重。

  **超出定义之处**：这是「旧版是 bug」的**确切内容**——不是总质量不同
  （那永远相同），而是**同一条像点记了几次**不同。 -/
theorem colsRaw_ne_merge_vals :
    (colsRaw.push dupLaw collapse).vals ≠ (pushMerge collapse dupLaw).vals := by
  rw [colsRaw_vals, pushMerge_dup_vals]
  intro h
  exact absurd h (by decide)

/-! ===========================================================================
  §6  ★ 核心 4：旧版预测**把一条像点摊成两条**
  =========================================================================== -/

/-- **反例模型**：外生律 `dupLaw`（总质量 `5`），求值/投影平凡。

  于是 `predict M eval project pf = pf.push dupLaw collapse`——
  预测层的一切行为**逐字**变成「推前族在反例上的行为」。 -/
noncomputable def dupModel : Model Real Real TwoPt (DiscLaw TwoPt) where
  F     := fun _ _ _ => 0
  P_U   := dupLaw
  graph := none

/-- 反例模型上的求值（常函数）。 -/
def dupEval : TwoPt → Real → Real := fun _ _ => 0

/-- 反例模型上的投影（常函数，落点无妨——质量账只与表结构有关）。 -/
def dupProject : (Real → Real) → Nat := fun _ => 2

/-- **`predict` 在反例上的值 = 旧版推前**（`rfl`）。 -/
theorem dupPredict_eq_raw :
    predict dupModel dupEval dupProject (⟨fun L f => rawMap L f⟩ :
      PushFamily DiscLaw TwoPt Nat Nat) = rawMap dupLaw (fun _ => 2) := rfl

/-- **旧版预测的总质量 = `5`**（`rfl`）——**这正是问题看不出来的原因**。 -/
theorem dupPredict_total : (rawMap dupLaw (fun _ => 2)).total = 5 := rfl

/-- **旧版预测的权重表 = `[2, 3]`**：两条重复像点，权重没相加。 -/
theorem rawRaw_wt : (rawMap dupLaw (fun _ => 2)).wt = [2, 3] := rfl

/-- **旧版预测的像点表 = `[2, 2]`**：同一条像点**两次**。 -/
theorem rawRaw_vals : (rawMap dupLaw (fun _ => 2)).vals = [2, 2] := rfl

/-- **合并版的权重表 = `[5]`**：同一条像点只留一条，权重求和。 -/
theorem mergedRaw_wt : (pushMerge (fun _ : TwoPt => 2) dupLaw).wt = [5] := rfl

/-- **合并版的像点表 = `[2]`**：去重后一条。 -/
theorem mergedRaw_vals : (pushMerge (fun _ : TwoPt => 2) dupLaw).vals = [2] := rfl

/-- **★ 核心 4**：旧版把同一条像点的质量**摊成两笔**，合并版记为**一笔**。

  | 量 | 旧版 | 合并版 |
  |---|---|---|
  | `wt` | `[2, 3]` | `[5]` |
  | 像点表 | `[2, 2]`（两次） | `[2]` |
  | `total` | `5` | `5` |
  | 按位置读「`2` 处质量」 | **`2`** | **`5`** |

  **超出定义之处**：`rawMap` 的定义只说「换取值、照抄权重」，
  **没有**任何关于「按位置读会读错」的内容；`rawMap_total`（`rfl`）更是**看不出**
  问题——两边 `total` 都是 `5`。本条的要害是 **`2 + 3 = 5`**：
  质量没丢，但**记法换了**，于是任何按位置读数的人拿到 `2` 而不是 `5`。 -/
theorem dupPredict_ratio_ne :
    (rawMap dupLaw (fun _ => 2)).wt.headD 0 = 2 ∧
    (pushMerge (fun _ : TwoPt => 2) dupLaw).wt.headD 0 = 5 ∧
    (rawMap dupLaw (fun _ => 2)).wt.headD 0 + 3
      = (pushMerge (fun _ : TwoPt => 2) dupLaw).wt.headD 0 :=
  ⟨rfl, rfl, rfl⟩

/-- **合并版预测的总质量 = 外生律总质量**（反例实例）。 -/
theorem mergedRaw_total : (pushMerge (fun _ : TwoPt => 2) dupLaw).total = dupLaw.total :=
  pushMerge_total (fun _ : TwoPt => 2) dupLaw rfl

/-- **旧版预测的总质量 = 外生律总质量**（`rfl`）——账本凑平的确切含义。 -/
theorem rawRaw_total : (rawMap dupLaw (fun _ => 2)).total = dupLaw.total := rfl

/-! ===========================================================================
  §7  ★ 核心 5：在**真数据** `synthLaw` 上把账算到底
  =========================================================================== -/

/-- 合成律上的「推前函数」（常函数，落在 `Real` 上）。

  取常函数是有意的：**常投影时 8 条像点全塌成一点**，
  这正是「合并与不合并差得最多」的极端情形，也最容易看出账不平。 -/
def synthStepR : SynthE → Real := fun _ => 0

/-- **合成律的 `DiscLaw Real` 版**：`rawMap` 把 `SynthE` 换成 `Real`，权重照抄。

  `discPushFamilyM` 要求外生赋值类型是 `Real`；`rawMap` 换完类型后
  **权重表与条数原样**（`rawMap_total` 是 `rfl`、`rawMap_length` 已证），
  故这是「同一份质量账」。 -/
noncomputable def synthLawR : DiscLaw Real := rawMap synthLaw synthStepR

/-- **`synthLawR` 合法**：`rawMap` 不改条数，故等长。

  **超出定义之处**：`rawMap` 的定义只换 `vals`；「换完还合法」要
  `rawMap_length` + `synthLaw_length` **两条**长度事实合起来，不是 `rfl`。 -/
theorem synthLawR_wf : DiscLawWellFormed synthLawR := by
  show (rawMap synthLaw synthStepR).vals.length = (rawMap synthLaw synthStepR).wt.length
  rw [rawMap_length]
  show synthLaw.vals.length = synthLaw.wt.length
  exact synthLaw_length

/-- **★ 合并版在合成律上塌成一条，权重 = `8`**。

  **超出定义之处**：`pushMerge` 的定义只说了「同像相加」；
  本条把「常投影 ⟹ 8 条挤进一条」与「权重和 = 8」**同时**算出来。
  于是「合并版预测仍是一个总质量为 8 的律」在**真数据**上落地，
  且它**恰好**是一条点质量（确定性 ⟹ 点质量，正是常投影应有的语义）。 -/
theorem synthMerge_total : ((discPushFamilyM Q).push synthLawR (fun _ => 0)).total = 8 := by
  rw [discPushFamilyM_push]
  rw [pushMerge_total (fun _ => (0:Q)) synthLawR synthLawR_wf]
  show (rawMap synthLaw synthStepR).total = 8
  rw [rawMap_total]
  exact synthLaw_wellFormed.2

/-- **旧版在合成律上总质量也是 `8`**——「账本凑平」，但**同一条像点记了 8 次**。 -/
theorem synthRaw_total : (rawMap synthLaw synthStepR).total = 8 := by
  rw [rawMap_total]
  exact synthLaw_wellFormed.2

/-- **★ 旧版与合并版在合成律上的差：单点质量 `1` 对 `8`**。

  `rawMap` 在常投影下把 8 条原像**原样**留在结果里，每条权重 `1`；
  按「首项」读单点质量（`SyntheticRun.pointPred` 的口径）拿到 `1`，应该是 `8`。
  **少了 `7`，占 `7/8`**。

  **超出定义之处**：这是把 §5 的反例**推广到本项目的真数据**。
  反例（`2` 对 `5`）可能被当成构造出来的病态；本条说明**合成律上一模一样**。 -/
theorem synthPoint_mass :
    (rawMap synthLaw synthStepR).wt.headD 0 = 1 ∧
    ((discPushFamilyM Q).push synthLawR (fun _ => 0)).wt.headD 0 = 8 :=
  ⟨rfl, rfl⟩

/-! ===========================================================================
  §8  `ℚ` 侧实证：显式 `Bool` 判等，把「合并」与「不合并」并排摊开
  =========================================================================== -/

/-- **恒 `false` 的判等**：模拟「任意两点**不同像**」。 -/
def beq0 {β : Type} : β → β → Bool := fun _ _ => false

/-- **恒 `true` 的判等**：模拟「任意两点**同像**」。 -/
def beq1 {β : Type} : β → β → Bool := fun _ _ => true

/-- **`ℚ` 上的律**：`vals = [0, 1]`、`wt = [2, 3]`（与 T4 的 `dupLaw` 同一组权重）。 -/
def qLaw : DiscLaw Q where
  vals := [(0 : Q), 1]
  wt   := [2, 3]

/-- **不同像（`beq0`）**：`goN` 原样留下两条，权重照抄。 -/
theorem qNoMergeTables :
    keyOf (goN beq0 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3]) = [0, 0] ∧
    wtOf (goN beq0 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3]) = [2, 3] :=
  ⟨rfl, rfl⟩

/-- **同像（`beq1`）**：`goN` 合成**一条**，权重**求和** `2 + 3 = 5`。 -/
theorem qMergeTables :
    keyOf (goN beq1 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3]) = [0] ∧
    wtOf (goN beq1 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3]) = [5] :=
  ⟨rfl, rfl⟩

/-- **★ `ℚ` 侧核心 3**：总质量 `5 = 5` 一分不少，但条数 `2 → 1`。

  **超出定义之处**：`goN` 的定义只说了「同像权重相加」，
  没说「不同像时权重照抄」「同像时首项权重变成总和」。两条表一比即是：**记法换了**。 -/
theorem qDropsMass :
    sumN (wtOf (goN beq0 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3])) = 5 ∧
    sumN (wtOf (goN beq1 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3])) = 5 ∧
    (wtOf (goN beq0 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3])).headD 0 = 2 ∧
    (wtOf (goN beq1 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3])).headD 0 = 5 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **两边总质量相同、条数不同**——把 `rawMap_total` 看不出问题这件事钉住。 -/
theorem qTotalsEq :
    sumN (wtOf (goN beq0 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3])) = 5 ∧
    sumN (wtOf (goN beq1 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3])) = 5 ∧
    (keyOf (goN beq0 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3])).length = 2 ∧
    (keyOf (goN beq1 (fun _ => (0:Q)) [] [(0:Q), 1] [2, 3])).length = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ===========================================================================
  §9  ★ 零公理侧（`Nat`）：合并算法本身不带任何经典成分
  =========================================================================== -/

/-- **`Nat` 上的反例律**：`vals = [0, 1]`、`wt = [2, 3]`。 -/
def nLaw : DiscLaw Nat where
  vals := [0, 1]
  wt   := [2, 3]

/-- **`nLaw` 合法**（`rfl`，零公理）。 -/
theorem nLaw_wf : DiscLawWellFormed nLaw := rfl

/-- **不同像**：`goN` 留下 **2 条**，权重照抄 `[2, 3]`。 -/
theorem nNoMerge :
    keyOf (goN beq0 (fun x => x) [] [0, 1] [2, 3]) = [0, 1] ∧
    wtOf (goN beq0 (fun x => x) [] [0, 1] [2, 3]) = [2, 3] :=
  ⟨rfl, rfl⟩

/-- **同像**：`goN` 合成 **1 条**，权重**相加** `[5]`。 -/
theorem nMerge :
    keyOf (goN beq1 (fun x => x) [] [0, 1] [2, 3]) = [0] ∧
    wtOf (goN beq1 (fun x => x) [] [0, 1] [2, 3]) = [5] :=
  ⟨rfl, rfl⟩

/-- **★ 零公理核心：同像合并把「两条」变「一条」，总质量一点没少。**

  六条并列：不合并 `sumN = 5`、合并 `sumN = 5`、
  条数 `2` 对 `1`、首项 `2` 对 `5`。
  与 §5 的 `discPushFamily_drops_mass` 和 §8 的 `qDropsMass` **结论相同**，
  而本条 `#print axioms` **为空**。

  ⟹ 「合并逻辑本身零公理」在 T13 里第一次由**实测**钉住：
  带公理的从来是**账本**（`List.sum` / `Real` / `Rat`），不是算法。

  **超出定义之处**：`goN` 的定义只说「同像相加」；本条把
  「条数降 1」「`sumN` 不变」「不合并时权重照抄」「首项读数不同」四件事一并钉住，
  这正是「`rawMap` 是 bug」的精确形式：**不是总质量错，是记法错**。 -/
theorem nDropsMass :
    sumN (wtOf (goN beq0 (fun x => x) [] [0, 1] [2, 3])) = 5 ∧
    sumN (wtOf (goN beq1 (fun x => x) [] [0, 1] [2, 3])) = 5 ∧
    (keyOf (goN beq0 (fun x => x) [] [0, 1] [2, 3])).length = 2 ∧
    (keyOf (goN beq1 (fun x => x) [] [0, 1] [2, 3])).length = 1 ∧
    (wtOf (goN beq0 (fun x => x) [] [0, 1] [2, 3])).headD 0 = 2 ∧
    (wtOf (goN beq1 (fun x => x) [] [0, 1] [2, 3])).headD 0 = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **占 `3/5`**：`3 · 5 = 5 · 3`（「首项少读 `3`、占总量 `5` 的 `3/5`」的比例形式）。 -/
theorem nWt_ratio : (3 : Nat) * 5 = 5 * 3 := by decide

/-- **合并版在 `nLaw` 上的总质量 = 原权重和**（零公理版守恒）。 -/
theorem nMergeSumN :
    sumN (wtOf (goN beq1 (fun x => x) [] [0, 1] [2, 3])) = sumN [2, 3] :=
  goN_sum beq1 (fun x => x) [] [0, 1] [2, 3] rfl

/-- **合并后权重就是 `[5]`**（供账本逐条登记）。 -/
theorem nMergeWt : wtOf (goN beq1 (fun x => x) [] [0, 1] [2, 3]) = [5] := rfl



end FateV2.Predict
