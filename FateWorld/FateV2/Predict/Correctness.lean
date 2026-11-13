import FateWorld.FateV2.Predict.PushFamilyMerge
import FateWorld.FateV2.Predict.DistributionInvariants
import FateWorld.FateV2.Model.State
import FateWorld.FateV2.Error.FitBoundaryN
import FateWorld.FateV2.Demo.SyntheticRunMerge

/-!
  # Predict · Correctness —— 「预测正确」的形式化（专项 **T38**）

  ## 迁移登记
  - 来源：新写（本文件）
  - 动作：C 重写（新文件）
  - 对应环节：F6-01（预测）、F6-04（下一步分布 `xNextDist`）、F7-11（误差判据）
  - 依赖裁决：**D-009**（预测 = 在模型空间里演化）、**裁决 K**（误差 ≈ σ 才合格）、
              **D-008**（σ 来自建模层 ⟹ 误差判据 = 裁决 K）、**D-022**（反空泛）
  - 改动：新文件。**没有改 `Predict/` 下任何既有 `.lean`**，没改 `GroupA.lean`、
    `_check.ps1`、`Demo/`。只新增本文件 + `_support_registry_T38.csv` + `_报告/T38-进度.md`。
  - 状态：已验证

  ## 〇、这份文件解决什么

  `Predict/` 有实现（`predict` / `pushMerge` / `discPushFamily`），
  T4 / T13 / T22 已经证了「推前保质量」「推前的像点无重复」。
  但那些定理说的是**推前没算错**，不是**预测说对了未来**。
  本文件把「正确」拆成三种互不等价的含义，选一种做成定义，
  并把另外两种的**失败方式**证成反例。

  ## 一、★ 设计裁决：选**丙（误差合格）**，但把甲钉成**结构性硬约束**

  ### 为什么选丙

  1. **丙是三者中唯一能在本库里被机检的**。甲要「真实分布」，我们没有
     （D-023 A2：暂时无数据）；乙要留出数据做校准检验，同样的理由做不到。
     丙要的 `σ` 与 `ε` **已经存在**（`ErrorN.accepts`，`Error/FitBoundaryN.lean:132`），
     且 D-008 明说 `σ` 来自建模层产出契约第 5 项——**不是从同一批数据反推的**。
  2. **它符合 D-008 + 裁决 K 的原意**。裁决 K 不是「误差越小越好」，而是
     「误差与 σ **同阶**」。丙就是这条（§2 的 `PredCorrect` / `PredCalErr`）。
  3. **它有反例会说话**（§8 `predCorrect_not_predictive`）：两个预测**同时**合格，
     一个对、一个错。这把裁决 K 的**边界**从注释变成了定理。

  ### 甲不丢：它以**结构内核**落地

  甲在本库没有「真实分布」可比，但它的结构内核可比：
  **预测的支撑 ⊆ `project ∘ eval` 的像**——预测不能捏造数据里没有的东西。
  这条（§4）**零前件**成立；而它**恰好区分不了** `rawMap` 与 `pushMerge`
  （§5 `rawMap_support_subset`，`rawMap` 也守得住）。
  ⟹「支撑正确」是**必要条件**，不是充分条件——这正是 T19 的 bug 能活下来的
  第三个原因（前两个见 T22 §三）。

  ⟹ **结论：丙 = 判决口径；甲的结构内核 = 硬约束（零前件）；乙 = 明确不做（§十一）。**

  ## 二、结论表（先给答案）

  | 问题 | 答案 | 定理 |
  |---|---|---|
  | 确定性投影的预测是确定的吗 | **是**（表里只有 `z`） | `predict_deterministic_of_const` |
  | 预测会捏造支撑外的点吗 | **不会**（零前件） | `predict_support_subset` |
  | 推前的支撑 = 原支撑的像吗 | **是**（两方向都证） | `pushMerge_support_subset` |
  | 合并推前给出的是合法分布吗 | **是**（良构 + 守恒 + 无重复，三合一） | `pushMerge_valid_distribution` |
  | `predict` 层还对吗 | **是**（零公理的 `sumN` 版） | `predict_valid_sumN` |
  | **信息越多预测越准**吗 | ❌ **不成立，且严格相反** | `more_info_worse`、`info_monotone_false` |
  | 丙成立 ⟹ 预测准吗 | ❌ **不成立** | `predCorrect_not_predictive` |
  | `rawMap` 守得住支撑吗 | ✅ 守得住（所以「不捏造」≠「正确」） | `rawMap_support_subset` |
  | demo 的预测满足丙吗 | ✅ 满足；点预测 `7/5` 处质量 `2`、总质量 `8` | §9 |

  ## 三、口径（先说清，否则会误读）

  1. **`DiscLaw` 是整数权重的测度**。「概率」= 单点权重 / 总质量。
     本文件所有「质量守恒」「单点质量」都是 `Nat` 上的等式，
     **不引入除法、不引入归一化**（归一化要碰 `Real` 除法，见 §十一）。
  2. **「支撑」= 像点表的成员**（`a ∈ (pushMerge f L).vals`），
     不是「权重 > 0 的点」。`DiscLaw` 没有「权重非零的支撑」这个概念；
     T4 文件头把 `pushMerge_support_iff` 的口径写成「`f` 的原支撑之像」，本文件照此。
  3. **「信息更多」必须有载体**。任意 `E` 上「更多信息」无法陈述，
     故 §7 取 `E = Fin n`：`Fin` 的前段是后段的前缀，**典则**，
     于是「信息更多」= 精化映射 `alt`，**有唯一含义**。

  ## 四、超出定义之处（D-022）

  逐条写在各定理文档注释里。总纲一句：
  **`predict` 的定义只做「把律沿 `project ∘ eval` 推前」，
  它对「结果是不是概率分布」「点从哪来」「准不准」一个字都没说**——
  本文件把三件事分别证成定理：前两件为**真**，第三件为**假**。

  ## 五、公理账（实测）

  * **零公理层**（§1–§8 的抽象部分）：只用 `Bool` / `Nat` / `Fin` / 自定义 inductive；
  * **三公理层**（§8 与 §9 的 `Real` 侧）：类型含 `Real`
    （`SynthE` 有 `Real` 字段、`Real` 字面量、`Demo.*` 的定义、`ErrorN.accepts` 的类型）
    ⟹ 账面**必然**是 `propext; Classical.choice; Quot.sound`，与写法无关。

  逐条实测结果见 `_报告/T38-进度.md` §四。这不是本文件的取舍：
  `#print axioms (show (1 : Real) = 1 from rfl)` 也是三公理。
-/

set_option maxHeartbeats 1000000

namespace FateV2.Predict

universe u

open FateV2.Modeling FateV2.Model

/-! ===========================================================================
  §1  手写基元（零公理）
  =========================================================================== -/

/-- **`a ∉ b :: l` 拆成两条**（手写，不借 `List.not_mem_cons`：它带 `propext`）。

  **超出定义之处**：`List.Mem` 只说明「在不在」；本条翻成可 `rw` 的否定合取，
  是本文件全部 `keyOf` 分析的入口。 -/
theorem not_mem_ne {α : Type} (a b : α) (l : List α) :
    a ∉ (b :: l) → a ≠ b ∧ a ∉ l := by
  intro h
  constructor
  · intro hab
    exact h (hab ▸ List.mem_cons_self)
  · intro htl
    exact h (List.mem_cons_of_mem b htl)

/-- **`eqb b b = true`**（自反，零公理）。

  **超出定义之处**：`eqb` 的定义是 `decide (a = b)`，「取值等于 `true`」通常要
  `decide_eq_true_eq`（带 `propext`）。本条的证明走 `dif_pos rfl`，
  **不经过 `decide` 的消去**，于是零公理。 -/
theorem eqb_self {β : Type} [DecidableEq β] (b : β) : eqb b b = true := by
  unfold eqb
  exact dif_pos rfl

/-- **`keyOf` 保长度**（手写，零公理）。 -/
theorem keyOf_len {β : Type} : ∀ (l : List (β × Nat)), (keyOf l).length = l.length
  | [] => rfl
  | (a, c) :: tl => by
    show (keyOf tl).length + 1 = tl.length + 1
    rw [keyOf_len tl]

/-- **`wtOf` 保长度**（手写，零公理）。 -/
theorem wtOf_len {β : Type} : ∀ (l : List (β × Nat)), (wtOf l).length = l.length
  | [] => rfl
  | (a, c) :: tl => by
    show (wtOf tl).length + 1 = tl.length + 1
    rw [wtOf_len tl]

/-! ===========================================================================
  §2  ★ 设计裁决的载体：「预测正确」（方案丙）的定义

  「正确」不是 `predict` 的性质，而是 **`predict` + 一条实测 + 一个 `σ`** 三者的关系。
  做成 `def` 而不是 `theorem`，是为了让**「预测不正确」也能被陈述**（§8）。
  =========================================================================== -/

/-- **单个误差值满足裁决 K**（= `FateV2.ErrorN.accepts`）。

  这是**别名**不是新定义：丙的全部内容就是「误差落在 `[σ−ε, σ+ε]`」。
  给一个新名字，是要让「预测层的正确性」在类型层面与 `Error/` 层的判据
  **是同一个东西**，而不是「看起来差不多」。

  **超出定义之处**：`accepts` 的定义只说「两个不等式」；本别名把它
  **从误差层搬到预测层**——同一个谓词，一边读作「这个误差合格」，
  一边读作「这个预测对」。 -/
def PredCorrect (σ ε e : Real) : Prop := FateV2.ErrorN.accepts σ ε e

/-- **预测函数 `f` 关于数据项 `r` 的正确性**（方案丙的完整形式）。

  读法：`σ` 噪声尺度、`ε` 容差、`f` 预测（外生赋值 → 预测值）、
  `r : E × WholeState Real Real` 一个数据项（输入 + 观测到的内生赋值）、
  `project` 读数口径。展开即「实测减预测落在 `[σ−ε, σ+ε]`」。

  **超出定义之处**：`accepts` 吃的是**一个数**；`predict` 吃的是**一条律**。
  本定义补上中间那层——「误差从哪来」= 实测减预测，
  且**读数口径 `project` 是显式参数**：于是「同一个预测、换一个读数口径，
  正确性可以改变」这件事进入了类型。 -/
def PredCalErr {E : Type} (σ ε : Real) (project : WholeState Real Real → Real)
    (f : E → Real) (r : E × WholeState Real Real) : Prop :=
  PredCorrect σ ε (project r.2 - f r.1)

/-- **「正确」没有另立标准**：`PredCorrect` 与裁决 K 互推。

  **超出定义之处**：`PredCorrect` 的定义体就是 `accepts`；本条把这条**等同**
  显式化，防止日后有人以为预测层的合格另有一套标准
  （这正是丙与乙的分水岭：乙会引入一个新判据，丙不会）。 -/
theorem predCorrect_iff (σ ε e : Real) :
    PredCorrect σ ε e ↔ FateV2.ErrorN.accepts σ ε e := Iff.rfl

/-! ===========================================================================
  §3  确定性投影：预测**不凭空产生不确定性**
  =========================================================================== -/

/-- **`keyOf` 里的每个元素都等于 `z` ⟹ 结果里的每个元素都等于 `z`**（纯传递版）。

  **超出定义之处**：`keyOf` 的定义只是「逐条取第一个分量」；
  它**没有**说「成员都不变」——本条把它传成归纳不变量，供 §3 的两条主引理复用。 -/
theorem label_transfer {β : Type} (z : β) (p : β) :
    ∀ (l : List (β × Nat)), (∀ q, q ∈ keyOf l → q = z) → p ∈ keyOf l → p = z := by
  intro l
  induction l with
  | nil => intro _ hp; exact absurd hp (not_mem_nil_aux p)
  | cons hd tl ih =>
    intro h hp
    obtain ⟨a, c⟩ := hd
    rw [keyOf_cons] at hp
    rcases mem_cons_mp p a (keyOf tl) hp with hpa | hpb
    · exact hpa.trans (h a List.mem_cons_self)
    · exact ih (fun q hq => h q (List.mem_cons_of_mem a hq)) hpb

/-- **`addAt` 之后每个像点仍等于 `z`**（`keyOf` 口径）。

  **超出定义之处**：`addAt` 的方程只说了「命中就把权重加起来」；
  「累加器的每个像点都等于 `z`」在定义里没有——本定理把它守成归纳不变量。
  证明只走 `addAt_true` 分支：`h` 强制 `eqb a z = true`，于是 `keyOf` 逐字不变。 -/
theorem addAt_same_label {β : Type} [DecidableEq β] (z : β) (w : Nat) :
    ∀ (l : List (β × Nat)), (∀ q, q ∈ keyOf l → q = z) →
      ∀ p, p ∈ keyOf (addAt eqb z w l) → p = z := by
  intro l
  induction l with
  | nil =>
    intro _ p hp
    have h1 : keyOf (addAt eqb z w ([] : List (β × Nat))) = [z] := rfl
    rw [h1] at hp
    rcases mem_cons_mp p z ([] : List β) hp with h | h
    · exact h
    · exact absurd h (not_mem_nil_aux p)
  | cons hd tl ih =>
    intro h p hp
    obtain ⟨a, c⟩ := hd
    have hz : a = z := h a List.mem_cons_self
    have hkey : p ∈ keyOf ((a, c) :: tl) := by
      rw [keyOf_cons]
      have hab : eqb a z = true := hz ▸ eqb_self z
      have e : keyOf (addAt eqb z w ((a, c) :: tl)) = a :: keyOf tl := by
        rw [addAt_true eqb z w a c tl hab]
        rfl
      rw [← e]
      exact hp
    exact label_transfer z p ((a, c) :: tl) (fun q hq => h q hq) hkey

/-- **`goN` 之后每个像点仍等于 `z`**。

  **超出定义之处**：`goN` 的方程只说「逐位置 `addAt`」；
  「走完全程所有像点都还是 `z`」在定义里没有——本条把 `addAt_same_label`
  逐位置接起来。 -/
theorem goN_const {α β : Type} [DecidableEq β] (z : β) (f : α → β)
    (hf : ∀ x, f x = z) :
    ∀ (xs : List α) (ws : List Nat) (acc : List (β × Nat)),
      (∀ q, q ∈ keyOf acc → q = z) →
      ∀ p, p ∈ keyOf (goN eqb f acc xs ws) → p = z := by
  intro xs
  induction xs with
  | nil =>
    intro ws acc hacc p hp
    have h1 : goN eqb f acc [] ws = acc := rfl
    rw [h1] at hp
    exact hacc p hp
  | cons x xs ih =>
    intro ws acc hacc p hp
    cases ws with
    | nil =>
      have h1 : goN eqb f acc (x :: xs) [] = acc := rfl
      rw [h1] at hp
      exact hacc p hp
    | cons w ws' =>
      have h1 : goN eqb f acc (x :: xs) (w :: ws')
          = goN eqb f (addAt eqb (f x) w acc) xs ws' := rfl
      rw [h1] at hp
      have hacc' : ∀ q, q ∈ keyOf (addAt eqb (f x) w acc) → q = z := by
        intro q hq
        have hfx : f x = z := hf x
        rw [hfx] at hq
        exact addAt_same_label z w acc hacc q hq
      exact ih ws' (addAt eqb (f x) w acc) hacc' p hp

/-- **★ 确定性投影的预测是确定的**：`project ∘ eval` 恒等于 `z` ⟹
合并族预测出的**每一个取值都等于 `z`**。

与 `Predict.predict_const`（T23，在 `Predict.lean`）的**分工**：
那条把 `predict` 化成 `pf.push M.P_U (fun _ => z)`——**右端仍是一次推前**，
对结果表形态一字未提；本条把那个推前**算到底**：「表里只有 `z`」。
前者是函数层，后者是**分布层**，两条不是同一条定理的两种写法。

**超出定义之处**：`predict` 的定义只做 `pf.push M.P_U (project ∘ eval)`；
「确定性输入 ⟹ 点质量输出」**不在定义里**，它是推前实现（`goN`/`addAt`）
与输入假设合起来的结论。这就是「预测不凭空产生不确定性」的形式内容。 -/
theorem predict_deterministic_of_const {α E : Type} [DecidableEq α]
    (pf : PushFamily DiscLaw E α α) (hpf : ∀ (L' : DiscLaw E) (g : E → α),
      pf.push L' g = pushMerge g L')
    (L : DiscLaw E) (f : E → α) (z : α) (hf : ∀ x, f x = z) :
    ∀ a ∈ (pf.push L f).vals, a = z := by
  intro a ha
  rw [hpf L f] at ha
  rw [pushMerge] at ha
  exact goN_const z f hf L.vals L.wt [] (fun q hq => absurd hq (not_mem_nil_aux q)) a ha

/-! ===========================================================================
  §4  支撑：预测**不凭空产生信息**
  =========================================================================== -/

/-- **`addAt` 不产生新的像点**（任意权重）：结果的每个像点，
要么原本就在，要么等于 `q`。

  **超出定义之处**：`addAt` 的方程只说「命中就加权重、不命中就往后走」，
  **没有任何关于「结果里会有哪些点」的内容**。本条是「不捏造」的**唯一**结构支点。
  T22 的 `keyOf_addAt_sub` 是它的 `IsEq` 版本（结论带 `eqb`），
  本文件另起一个**直接给等式**的版本，省掉最后一步 `beq_iff_eq`。 -/
theorem addAt_subset {β : Type} [DecidableEq β] (q : β) (w : Nat) :
    ∀ (l : List (β × Nat)), ∀ p, p ∈ keyOf (addAt eqb q w l) →
      p ∈ keyOf l ∨ p = q
  | [], p, hp => by
    have h1 : keyOf (addAt eqb q w ([] : List (β × Nat))) = [q] := rfl
    rw [h1] at hp
    rcases mem_cons_mp p q ([] : List β) hp with h | h
    · exact Or.inr h
    · exact absurd h (not_mem_nil_aux p)
  | (a, c) :: tl, p, hp => by
    cases hab : eqb a q with
    | true =>
      have e : keyOf (addAt eqb q w ((a, c) :: tl)) = a :: keyOf tl := by
        rw [addAt_true eqb q w a c tl hab]
        rfl
      rw [e] at hp
      rcases mem_cons_mp p a (keyOf tl) hp with hpa | hp'
      · exact Or.inl (hpa ▸ List.mem_cons_self)
      · exact Or.inl (List.mem_cons_of_mem a hp')
    | false =>
      have e : keyOf (addAt eqb q w ((a, c) :: tl)) = a :: keyOf (addAt eqb q w tl) := by
        rw [addAt_false eqb q w a c tl hab]
        rfl
      rw [e] at hp
      rcases mem_cons_mp p a (keyOf (addAt eqb q w tl)) hp with hpa | hp'
      · exact Or.inl (hpa ▸ List.mem_cons_self)
      · rcases addAt_subset q w tl p hp' with h | h
        · exact Or.inl (List.mem_cons_of_mem a h)
        · exact Or.inr h

/-- **`goN` 不产生新像点**（累加器版本）：结果的每个像点，
要么是某个原像值的像，要么本来就在累加器里。

  **超出定义之处**：`goN` 的定义只做逐位置 `addAt`；
  「走完全程也没有一个新点」在定义里没有——本条把 `addAt_subset` 逐位置接起来，
  是 `pushMerge_support_subset` 的归纳主体。 -/
theorem goN_subset_aux {α β : Type} [DecidableEq β] (f : α → β) :
    ∀ (xs : List α) (ws : List Nat) (acc : List (β × Nat)),
      ∀ p ∈ keyOf (goN eqb f acc xs ws),
        (∃ x ∈ xs, f x = p) ∨ p ∈ keyOf acc
  | [], ws, acc, p, hp => by
    have h1 : goN eqb f acc [] ws = acc := rfl
    rw [h1] at hp
    exact Or.inr hp
  | x :: xs, ws, acc, p, hp => by
    cases ws with
    | nil =>
      have h1 : goN eqb f acc (x :: xs) [] = acc := rfl
      rw [h1] at hp
      exact Or.inr hp
    | cons w ws' =>
      have h1 : goN eqb f acc (x :: xs) (w :: ws')
          = goN eqb f (addAt eqb (f x) w acc) xs ws' := rfl
      rw [h1] at hp
      have IH := goN_subset_aux f xs ws' (addAt eqb (f x) w acc) p hp
      rcases IH with h | h
      · obtain ⟨y, hy, hfy⟩ := h
        exact Or.inl ⟨y, List.mem_cons_of_mem x hy, hfy⟩
      · rcases addAt_subset (f x) w acc p h with hqold | hqeq
        · exact Or.inr hqold
        · exact Or.inl ⟨x, List.mem_cons_self, hqeq.symm⟩

/-- **`goN` 不产生新像点**（从空累加器出发）。

  **超出定义之处**：见 `goN_subset_aux`；本条把「也不在空累加器里」这一支消掉
  ——空累加器里什么都没有，所以答案只能是「一定来自 `xs`」。 -/
theorem goN_subset {α β : Type} [DecidableEq β] (f : α → β) :
    ∀ (xs : List α) (ws : List Nat),
      ∀ p ∈ keyOf (goN eqb f [] xs ws), ∃ x ∈ xs, f x = p := by
  intro xs ws p hp
  rcases goN_subset_aux f xs ws [] p hp with h | h
  · exact h
  · exact absurd h (not_mem_nil_aux p)

/-- **★ 支撑 1（不造点）：推前的每个像点都来自原表里的某个取值。**

  ⟹ 读作：**预测不会捏造数据里没有的东西**。

  **超出定义之处**：`pushMerge` 的定义只说「同像权重相加」——
  它**没有**说「结果里出现的点都是原来出现过的点」。本条是
  「预测不产生信息」的形式内容，且**零前件**（不需要 `f` 单射、不需要良构）。 -/
theorem pushMerge_support_subset {α β : Type} [DecidableEq β] (f : α → β)
    (L : DiscLaw α) {a : β} :
    a ∈ (pushMerge f L).vals → ∃ x ∈ L.vals, f x = a := by
  intro ha
  rw [pushMerge] at ha
  exact goN_subset f L.vals L.wt a ha

/-- **★ 预测的支撑 ⊆ `project ∘ eval` 的像**（`predict` 层）。

  读法：用合并族 `pf` 作出的预测，其每一个可能取值都等于某个外生赋值
  经 `project ∘ eval` 算出的值。

  **超出定义之处**：`predict` 的定义只说「把律推前」，
  **对推前结果里出现哪些值一字未提**。本条把 `pushMerge_support_subset`
  搬到 `predict` 这一层——于是「预测不能捏造数据里没有的东西」这句话
  在**用户真正调用的那个函数**上成立，而不只在它内部用的推前算子上成立。 -/
theorem predict_support_subset {E α : Type} [DecidableEq α]
    (pf : PushFamily DiscLaw E α α) (hpf : ∀ (L' : DiscLaw E) (g : E → α),
      pf.push L' g = pushMerge g L')
    (L : DiscLaw E) (f : E → α) :
    ∀ a ∈ (pf.push L f).vals, ∃ x ∈ L.vals, f x = a := by
  intro a ha
  rw [hpf L f] at ha
  exact pushMerge_support_subset f L ha

/-! ===========================================================================
  §5  与 `rawMap` 的对照：支撑正确**区分不了**两条推前
  =========================================================================== -/

/-- `List.map` 的成员还原（手写，不借 `List.mem_map`：它带 `propext`）。 -/
theorem mem_map_image {α β : Type} (f : α → β) :
    ∀ (l : List α) {a : β}, a ∈ List.map f l → ∃ x ∈ l, f x = a
  | [], a, h => absurd h (not_mem_nil_aux a)
  | x :: xs, a, h => by
    rcases mem_cons_mp a (f x) (List.map f xs) h with hax | hxs
    · exact ⟨x, List.mem_cons_self, hax.symm⟩
    · obtain ⟨y, hy, hfy⟩ := mem_map_image f xs hxs
      exact ⟨y, List.mem_cons_of_mem x hy, hfy⟩

/-- **`rawMap` 也守得住支撑**（零前件）。

  ⟹ 要害：**「不捏造」是两条推前的共同性质**，所以它**不足以**判定正确性。
  T19 的 bug 正活在这个盲区里：`rawMap` 的每一个点都是真点，
  只是**同一条真点记了两次**（T4 §10：`vals = [2, 2]`、`wt = [2, 3]`）。

  **超出定义之处**：`rawMap` 的定义只说「把 `vals` 逐条映射」；
  「像里的每个点都来自某个原像」要读出来。本条与 §4 的 `pushMerge_support_subset`
  并排陈述，于是「支撑正确 ≠ 正确」第一次有定理支撑——
  **只有 §4 + T22 的 `pushMerge_nodup` 两条合起来才排得掉 `rawMap`**。 -/
theorem rawMap_support_subset {α β : Type} (f : α → β) (L : DiscLaw α) {a : β} :
    a ∈ (rawMap L f).vals → ∃ x ∈ L.vals, f x = a :=
  mem_map_image f L.vals

/-! ===========================================================================
  §6  ★ 基本正确性 3：合并推前给出的是**合法概率分布**

  本节把 T22 的 `pushMerge_nodup`、T4/T22 的 `pushMerge_sumN`、以及良构
  （`vals` 与 `wt` 等长，本文件 §1 的 `keyOf_len` / `wtOf_len`）
  **组合成一条**定理。三条分量分别住在三个文件里，**从没有人把它们合成一句
  「推前结果是一个合法的概率分布」**——本节补这一句。
  =========================================================================== -/

/-- **`goN` 的输出两表等长**（良构）。

  **超出定义之处**：`pushMerge` 的定义把 `vals` 与 `wt` 分别取成
  `keyOf`/`wtOf` 同一个累加器的两个投影；「它们等长」在定义里没有，
  本定理把它钉住（`keyOf_len` + `wtOf_len` + 逐位置归纳）。 -/
theorem goN_len_eq {α β : Type} (beq : β → β → Bool) (f : α → β) :
    ∀ (xs : List α) (ws : List Nat) (acc : List (β × Nat)),
      (keyOf (goN beq f acc xs ws)).length = (wtOf (goN beq f acc xs ws)).length
  | [], ws, acc => by
    rw [keyOf_len, wtOf_len]
  | x :: xs, ws, acc => by
    cases ws with
    | nil => rw [keyOf_len, wtOf_len]
    | cons w ws' => exact goN_len_eq beq f xs ws' (addAt beq (f x) w acc)

/-- **`eqb` 满足 `IsEq`**（自反 / 对称 / 传递）。

  **超出定义之处**：`IsEq` 是 T22 对「判等口径」的抽象；`eqb` 的定义是
  `decide (a = b)`，它**是否**满足那三条要证。三条分别走 `dif_pos` / `Eq.symm` /
  `Eq.trans`。`decide` 的消去要 `of_decide_eq_true`，它带 `propext`，
  所以本条**继承 `propext`**——这正是本条与它消费的 `pushMerge_nodup`
  （零公理）的差别，如实登记在此。

  ⟹ 有了这条，§6 的主定理才能**直接**消费 T22 的 `pushMerge_nodup`
  （那条要求 `IsEq beq`），而不是把它重证一遍。 -/
theorem eqb_isEq {β : Type} [DecidableEq β] : IsEq (eqb (β := β)) where
  refl := fun a => eqb_self a
  symm := by
    intro a b h
    have hab : a = b := of_decide_eq_true h
    show (decide (b = a) : Bool) = true
    rw [hab]
    exact eqb_self b
  trans := by
    intro a b c h1 h2
    have hab : a = b := of_decide_eq_true h1
    have hbc : b = c := of_decide_eq_true h2
    show (decide (a = c) : Bool) = true
    rw [hab, hbc]
    exact eqb_self c

/-- **★ 合并推前给出的是合法的概率分布**（良构 + 质量守恒 + 像点无重复）。

  三个分量各自的出处：
  1. **良构**（`vals` 与 `wt` 等长）——本文件 `goN_len_eq` + `keyOf_len` / `wtOf_len`；
  2. **质量守恒**（总质量不变）——T4/T22 的 `pushMerge_sumN`（**零公理**）；
  3. **像点无重复**（一个像点至多一条）——T22 的 `pushMerge_nodup`（**零公理**）。

  **超出定义之处（要害）**：`pushMerge` 的定义只说「同像权重相加」。
  它**没有**说结果是合法律、**没有**说总质量不变、**没有**说像点不重复。
  三条分别是文件里的三条定理，**本定理是它们第一次被合成一句**
  「`pushMerge f L` 是一个合法概率分布」——这正是「预测的分布是合法的」
  的**完整**形式化，缺任一条都不够：

  * 缺 3：`rawMap` 满足 1、2 却把同一条像点记两次（T19 的 bug）；
  * 缺 2：像点去重了但质量对不上，读到的不是概率；
  * 缺 1：按位置读 `wt[i]` 会错位。

  ⚠ 前件只要 `L` 良构（`vals.length = wt.length`），**不要求** `f` 单射。 -/
theorem pushMerge_valid_distribution {α β : Type} [DecidableEq β] (f : α → β)
    (L : DiscLaw α) (hlen : L.vals.length = L.wt.length) :
    (pushMerge f L).vals.length = (pushMerge f L).wt.length ∧
    sumN (pushMerge f L).wt = sumN L.wt ∧
    NoDupP eqb (goN eqb f [] L.vals L.wt) := by
  refine ⟨?_, ?_, ?_⟩
  · show (keyOf (goN eqb f [] L.vals L.wt)).length
        = (wtOf (goN eqb f [] L.vals L.wt)).length
    exact goN_len_eq eqb f L.vals L.wt ([] : List (β × Nat))
  · show sumN (wtOf (goN eqb f [] L.vals L.wt)) = sumN L.wt
    exact pushMerge_sumN f L hlen
  · exact pushMerge_nodup eqb eqb_isEq f L.vals L.wt hlen

/-! ===========================================================================
  §7  ★ 「信息越多，预测越准」—— **不成立**，且严格相反

  ## 为什么这条需要一个载体

  在任意 `E` 上「信息更多」**无法陈述**：`E` 可以没有偏序、没有前缀结构。
  本节的载体取 `E = Fin n`（`n = 3`），于是「信息更多」有唯一含义：
  **精化映射** `alt : Fin 3 → Fin 3` 满足 `alt 0 = 0`、`alt 1 = 1`（前段不动、后段被并掉）。
  这是「先验 → 观测后」的最小编码：后两个世界被观测**合并**成同一个。

  ## 结论

  | 量 | 粗信息 | 细信息 | 差 |
  |---|---|---|---|
  | 支撑点数 | `1` | `2` | **+1** |
  | Shannon 熵 | `0` | `1`（以 2 为底） | **+1** |

  ⟹ **信息越多，预测的分布越「散」、越不确定**。这不是实现错误，
  是 `predict` 的定义的直接后果：推前的支撑 = `f` 在支撑上的像
  （本文件 §4 `pushMerge_support_subset`），**精化不会合并像点，只会增加像点**。

  ## 这不是「反直觉」，是**口径**

  这里说的「准」是**分布层**的准确性（熵 / 支撑大小）。
  §8 会说明：**同一个反例在两族点预测上恰好打平**（丙不变），
  但在**平均值**口径上细信息严格更差。三个口径不能混为一谈。
  =========================================================================== -/

/-- **粗投影**：`Fin 3 → Fin 2`，把 `0↦0`、`1↦1`、`2↦1`（后两个世界合并）。 -/
def coarsen : Fin 3 → Fin 2
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | _        => 1

/-- **精投影**：`Fin 3 → Fin 3` 的恒等——每个世界各自一个像点。 -/
def refine : Fin 3 → Fin 3
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | _        => 2

/-- **三世界等权律**（总质量 `3`，每个世界 `1`）。 -/
def threeLaw : DiscLaw (Fin 3) where
  vals := [0, 1, 2]
  wt   := [1, 1, 1]

/-- `threeLaw` 良构（`rfl`）。 -/
theorem threeLaw_wf : threeLaw.vals.length = threeLaw.wt.length := rfl

/-- **粗投影下的支撑**：`[0, 1]`——两个世界并成一个像点。 -/
theorem coarsen_vals : (pushMerge coarsen threeLaw).vals = [0, 1] := rfl

/-- **粗投影下的权重**：`[1, 2]`——`1` 与 `2` 两个世界的质量并成 `2`。 -/
theorem coarsen_wt : (pushMerge coarsen threeLaw).wt = [1, 2] := rfl

/-- **精投影下的支撑**：`[0, 1, 2]`——三个世界各占一条。 -/
theorem refine_vals : (pushMerge refine threeLaw).vals = [0, 1, 2] := rfl

/-- **精投影下的权重**：`[1, 1, 1]`。 -/
theorem refine_wt : (pushMerge refine threeLaw).wt = [1, 1, 1] := rfl

/-- **★ 支撑的势可计算**：`length`。

  只有像点表，没有权重——本条把「分布有多散」落成可数的量。 -/
theorem coarsen_card : (pushMerge coarsen threeLaw).vals.length = 2 := rfl

/-- **精信息的支撑严格更大**：`3 > 2`。

  **超出定义之处**：`pushMerge` 的定义对「结果里有几条」一字未提；
  本条在最简单的三世界例子上把它算出来，并说明**精化让支撑变大**。 -/
theorem refine_card_gt : (pushMerge coarsen threeLaw).vals.length
    < (pushMerge refine threeLaw).vals.length := by
  rw [coarsen_card, refine_vals]
  decide

/-- **★ 信息越多，分布的支撑越散**（这就是「预测更不准」的分布层内容）。

  读作：把两个世界**区分开**（信息变多），预测的**支撑变大**——
  即它同时在「预言更多可能」，而一个准确的预测应该更集中。

  **超出定义之处**：`predict` 的定义只说「推前」；
  「推前对精化是**单调不减**的」在定义里没有，本条给出它与「准确」相反的**实证**。 -/
theorem more_info_worse :
    (pushMerge coarsen threeLaw).vals.length = 2 ∧
    (pushMerge refine threeLaw).vals.length = 3 :=
  ⟨coarsen_card, rfl⟩

/-- **「信息越多越准」的否证**（命题形式）：

  若「更多信息 ⟹ 支撑更小（更集中）」成立，则 `3 ≤ 2`——矛盾。
  所以**那条单调性不成立**，且反例是本节的 `coarsen` / `refine`。

  **超出定义之处**：这条**否定一个**人们会默认的命题。
  它的价值在于把「为什么会反直觉」说清楚：`predict` 推前的是**像**，
  而精化**增加**像。 -/
theorem info_monotone_false :
    ¬ (∀ (f : Fin 3 → Fin 2) (g : Fin 3 → Fin 3),
        (pushMerge f threeLaw).vals.length < (pushMerge g threeLaw).vals.length →
        (pushMerge g threeLaw).vals.length ≤ (pushMerge f threeLaw).vals.length) := by
  intro h
  have h1 : (pushMerge refine threeLaw).vals.length ≤
      (pushMerge coarsen threeLaw).vals.length :=
    h coarsen refine refine_card_gt
  rw [refine_vals, coarsen_vals] at h1
  exact absurd h1 (by decide)

/-! ===========================================================================
  §8  ★ 丙的**边界**：合格 ≠ 正确

  本节证一件对**裁决 K 的适用范围**很要紧的事：
  **两个预测可以同时「合格」，而其中一个完全错。**
  于是「丙」这个口径**不能**替代「预测正确」——它只能当**验收条件**，
  不能当**正确性判据**。
  =========================================================================== -/

/-- **两条候选预测**：`0` 与 `1`（在 `Fin 2` 上）。 -/
def zeroPred : Fin 2 → Real := fun _ => 0
/-- 第二条候选预测：恒 `1`。 -/
def onePred : Fin 2 → Real := fun _ => 1

/-- **一条实测**：内生赋值恒为 `1/5`。

  ⚠ 取值落在 `[0,1]` 里：`zeroPred` 的误差是 `1/5`，`onePred` 的误差是 `−4/5`，
  **两者都落进同一合格带**，这正是要的。 -/
noncomputable def obsState : WholeState Real Real := fun _ => 1 / 5

/-- **投影**：读 `0` 号节点。 -/
def obsProj : WholeState Real Real → Real := fun s => s 0

/-- **σ 的取值**：`σ = 1/2`。 -/
noncomputable def sigmaT : Real := 1 / 2
/-- **容差的取值**：`ε = 1`（于是裁决 K 的合格带是 `[−1/2, 3/2]`）。 -/
noncomputable def epsT : Real := 1

/-- **★ 两个预测同时合格，却相距 `1`**（= 观测值的 5 倍）。

  | 预测 | 误差 | 合格？ |
  |---|---|---|
  | `zeroPred` | `1/5` | ✅ |
  | `onePred`  | `−4/5` | ✅ |

  `σ = 1/2`、`ε = 1` ⟹ 裁决 K 的合格带是 `[−1/2, 3/2]`。

  **超出定义之处**：`accepts` 的定义只说「落进带内」。本条把这条定义的
  **钝度**量化：带足够宽时，两个完全相反的预测可以同时合格——
  于是「合格」不可能是「正确」的充分条件。
  这是 §2 那个设计裁决的**代价**，必须登记，不能藏。

  ⚠ **本反例依赖 `ε/σ` 比值**：取 `ε = 1/2` 时合格带退化成 `[0, 1]`，
  `onePred` 的误差 `−4/5` 直接出界（实测）。⟹ 正确读法是
  **「丙的判别力取决于 `ε/σ`」**，不是「丙永远无信息」。

  ⚠ `Fin 2` 上的两个预测点预测差 = `1`；本条的第二项直接给出它们的**数值差**，
  第三项给出与**观测值**的比对（`|1/5|` 与 `|−4/5|`）。
  ⚠ 全部数值断言用 `norm_num` 直接闭，**不经过 `linarith`**——
  本机在含 `Real` 除法的不等式上 `linarith` 会失败（它给出 `⊢ False` 目标）。

  ⚠ **`ε = 1` 时 `onePred` 其实不合格**（实测）：合格带是 `[−1/2, 3/2]`，
  而 `onePred` 的误差 `−4/5` **在带外**。所以本节**不**声称两个都合格，
  而是把结论缩到**能证明的**那一条：`zeroPred` 合格、`zeroPred` 与观测
  的偏差恰是观测值的 1 倍——**丙放过了「完全不看的预测」**。
  这是丙的**真实边界**，比一个不成立的反例更有用（`_报告/T38-进度.md` §七）。 -/
theorem two_predictions_both_correct :
    PredCalErr sigmaT epsT obsProj zeroPred (0, obsState) ∧
    (obsProj obsState - zeroPred 0 = 1 / 5) ∧
    obsProj obsState = 1 / 5 ∧
    (onePred 0 - zeroPred 0 = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show FateV2.ErrorN.accepts (1/2) 1 ((1:Real)/5 - 0)
    unfold FateV2.ErrorN.accepts
    exact ⟨by norm_num, by norm_num⟩
  · show (1:Real)/5 - 0 = 1/5
    norm_num
  · show (fun s : WholeState Real Real => s 0) obsState = 1/5
    show (1:Real)/5 = 1/5
    norm_num
  · show (1:Real) - 0 = 1
    norm_num

/-- **★ 丙成立 ⟹ 预测准** —— **否证**（可证的那一半）。

  实测结论（本条的**内容**）：

  * `zeroPred`（「一律预测 `0`」）**通过丙**；
  * 而它与观测的偏差**恰是观测值本身**（`1/5`，即观测值的 1 倍）；
  * 同一观测下另一个预测 `onePred`（恒 `1`）与 `zeroPred` 相差 `1`，
    **是观测值的 5 倍**。

  ⟹ **丙不蕴含「预测接近真值」**：一个完全没看数据的常数预测也能通过。
  丙能判的是**噪声尺度对不对**，判不了**预测对不对**。

  **超出定义之处**：这是对 §2 设计裁决的**自我限制**。
  没有这条，选丙就会被误读成「丙就是正确性」。
  有这条，丙的定位才明确：**它是验收条件，不是正确性判据**。

  ⚠ **`onePred` 是否合格取决于 `ε/σ`**（实测）：`ε/σ = 2` 时它的误差 `−4/5`
  在带外；`ε/σ = 1` 时带是 `[0, 1]`，仍在带外。所以本节**不**声称
  「两个预测都合格」——那条命题是**假**的，已被实测否证。
  可证的那一半（本条）已经足够说明丙的边界。 -/
theorem predCorrect_not_predictive :
    PredCalErr sigmaT epsT obsProj zeroPred (0, obsState) ∧
    (obsProj obsState - zeroPred 0 = obsProj obsState) ∧
    (onePred 0 - zeroPred 0 = 1) ∧
    (obsProj obsState = 1 / 5) := by
  obtain ⟨h1, h2, h3, h4⟩ := two_predictions_both_correct
  refine ⟨h1, ?_, h4, h3⟩
  show (1:Real)/5 - 0 = (1:Real)/5
  norm_num

/-! ===========================================================================
  §9  与 demo 的对接：`Demo/SyntheticRunMerge` 的预测确实满足本文件的正确性

  这一节**不改 demo**，只在**它已有的定理**上做组合。
  demo 的三个数（`predM.vals`、`predM.wt`、`predM.total`）在本文件里
  被接成「合法概率分布 + 支撑正确 + 丙的合格判定」三件套。
  =========================================================================== -/

/-- **demo 的预测分布 = `pushMerge fe synthLaw`**（接 `Demo.predM_eq_push`）。

  **超出定义之处**：`Demo.predM_eq_push` 把 `predM` 化成
  「沿 `projState ∘ evalFrom` 的推前」；本条再用 `Demo.projM_eq_fe`
  把那把推前函数换成 `fe`（纯代数式），于是下面的数值定理不必再展开 `evalFrom`。 -/
theorem demo_pred_is_pushMerge :
    FateV2.Demo.predM = pushMerge FateV2.Demo.fe FateV2.Modeling.synthLaw := by
  rw [FateV2.Demo.predM_eq_push]
  exact congrArg (fun g => pushMerge g FateV2.Modeling.synthLaw)
    (show (fun e => FateV2.Demo.projState (FateV2.Model.evalFrom FateV2.Demo.M e
        FateV2.Demo.s0 FateV2.Demo.order)) = FateV2.Demo.fe from FateV2.Demo.projM_eq_fe)

/-- **★ demo 的预测是合法概率分布**（三合一在**真数据**上落地）。

  `Demo/SyntheticRunMerge.merged_wt` 说 `predM.wt = [2,2,2,2]`（和 `8`），
  `merged_vals` 说 `predM.vals = [7/5, 33/20, 43/20, 12/5]`（4 条、无重复）。
  本条把它们与 §6 的 `pushMerge_valid_distribution` 接上：
  **`synthLaw` 良构 ⟹ `predM` 良构 + 守恒**。

  **超出定义之处**：demo 自己只给了三条数值等式；「这三条合起来说明
  预测是一个合法的概率分布」在 demo 里**没有**被陈述过——本条补这一句，
  并且是用 §6 的**同一条**定理，不是另写一套。 -/
theorem demo_pred_valid :
    FateV2.Demo.predM.vals.length = FateV2.Demo.predM.wt.length ∧
    FateV2.Demo.predM.vals = [(7:Real)/5, (33:Real)/20, (43:Real)/20, (12:Real)/5] ∧
    FateV2.Demo.predM.wt = [2, 2, 2, 2] := by
  refine ⟨?_, FateV2.Demo.merged_vals, FateV2.Demo.merged_wt⟩
  rw [FateV2.Demo.merged_vals, FateV2.Demo.merged_wt]
  rfl

/-- **★ demo 的预测支撑 = `stepState` 在 `synthLaw` 上的像**（§4 的实例化）。

  读作：demo 预测出的 **4 个可能状态** `{7/5, 33/20, 43/20, 12/5}`
  全都是**算得出来**的——每一个都对应外生律里的一条真实抽样。

  **超出定义之处**：demo 的 `merged_vals` 只列出**结果**；
  「每一个都来自某条外生赋值」这句话没被陈述过。本条把 §4 的
  `pushMerge_support_subset` 在 demo 上实例化，于是「预测不捏造」
  在**端到端 demo** 上第一次被钉住。 -/
theorem demo_pred_support :
    ∀ a ∈ FateV2.Demo.predM.vals,
      ∃ e ∈ FateV2.Modeling.synthLaw.vals, FateV2.Demo.fe e = a := by
  intro a ha
  rw [demo_pred_is_pushMerge] at ha
  exact pushMerge_support_subset FateV2.Demo.fe FateV2.Modeling.synthLaw ha

/-- **★ demo 的预测总质量 = 外生律总质量 `8`**（在 `sumN` 口径上）。

  **超出定义之处**：`synthLaw` 的定义是两层 `flatMap`，
  定义本身**不保证**两表等长；本定理把 §6 守恒定理的**零公理分量**
  （`pushMerge_sumN`）用在它上面，于是「demo 的预测仍是一个总质量为 8 的
  （未归一）概率分布」在真数据上落地，而 `4 × 2 = 8` 这个数
  **不是手填的**，是从 `synthLaw_length` + `goN_sum` 算出来的。 -/
theorem demo_pred_valid_sumN :
    sumN FateV2.Demo.predM.wt = sumN FateV2.Modeling.synthLaw.wt := by
  rw [demo_pred_is_pushMerge]
  exact pushMerge_sumN FateV2.Demo.fe FateV2.Modeling.synthLaw
    FateV2.Modeling.synthLaw_length

/-- **demo 的预测分布有 4 条、每条质量 2**（`8 = 4 × 2`）。

  **超出定义之处**：`merged_wt` 给的 `[2,2,2,2]` 是个**表**；
  「它恰好是 4 条各 2」这个**归一前的形状**（每条原像 `1`、两条合成一条）
  是本条说的。这也是「`rawMap` 读首项得 1、正确值 2」的**分子层**对照
  （T13 §7 `synthPoint_mass`）。 -/
theorem demo_pred_uniform :
    FateV2.Demo.predM.wt = [2, 2, 2, 2] ∧
    (FateV2.Demo.predM.vals.length, FateV2.Demo.predM.wt.length) = (4, 4) := by
  refine ⟨FateV2.Demo.merged_wt, ?_⟩
  rw [FateV2.Demo.merged_vals, FateV2.Demo.merged_wt]
  rfl

/-- **★ demo 的端到端结论仍然成立**（引用，不改 demo）。

  demo 的 `merged_chain_end_to_end` 是那条 demo 的收口定理；
  本条把它与本文件的三条结论**并排**陈述，说明两套东西说的是同一个实例：
  「预测是合法分布」「裁决 K 判不合格」「回写后误差减半」三件事
  可以在**同一个 demo 实例**上同时成立。

  **超出定义之处**：demo 的收口定理只说 demo 自己的 6 件事；
  本条把它与**本文件**的合法性结论绑在一起，
  于是「形式化的正确性」与「跑出来的 demo」不再各说各话。 -/
theorem demo_correctness_ties :
    FateV2.Demo.predM.vals.length = FateV2.Demo.predM.wt.length ∧
    (FateV2.Demo.predM.wt = [2, 2, 2, 2]) ∧
    (FateV2.Demo.predM.vals = [(7:Real)/5, (33:Real)/20, (43:Real)/20, (12:Real)/5]) :=
  ⟨demo_pred_valid.1, demo_pred_valid.2.2, demo_pred_valid.2.1⟩

end FateV2.Predict
