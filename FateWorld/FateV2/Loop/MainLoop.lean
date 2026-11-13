import FateWorld.FateV2.Rules.FCA

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/MainLoop.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 4 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Rules
open FateV2.Model
open FateV2.Modeling

/-! ✅✅✅ **第 276 轮修复声明：`step` 不再是常值函数**

## 旧缺陷（第 275 轮 S6 发现，已确认）

```lean
noncomputable def step (info : InfoLevel) (noise : NoiseScale) : LoopState → LoopState
  | _ => if noise < info then .running else .paused
    ↑
  丢弃状态
```

**⚠ `step info noise s` 不依赖于 `s`** ⟹ 旧的 `step_running_iff` / `step_paused_iff`
虽然写成「对任意 `s`」，实质只是「常值函数的值」，`s` 是哑参数。
**⟹ 这与「主线循环」的语义相反**（循环的定义特征是下一步依赖当前状态）。

## 新设计（本轮，依裁决 O）

```lean
noncomputable def step (info : InfoLevel) (noise : NoiseScale) (margin : ℝ) :
    LoopState → LoopState
  | .running => if noise < info then .running else .paused
  | .paused  => if noise + margin < info then .running else .paused
```

| 当前状态 | 判定 | 语义 |
|---|---|---|
| `.running` | `noise < info` | 信息**严格多于**噪声 ⟹ 继续；否则暂停 |
| `.paused` | `noise + margin < info` | 恢复需**严格更足**的信息（余量 `margin`）|

**关键判决（本轮 D7 结论）**：

| `margin` | `step` 是否依赖状态 | 是否符合裁决 O |
|---|---|---|
| `margin = 0` | ❌ **不依赖**（退化为第 275 轮的常值缺陷）| ✅ |
| `0 < margin` | ✅ **依赖** | ✅ **唯一正确区间** |
| `margin < 0` | ✅ 依赖，但**方向反了** | ❌ 暂停态在信息**更少**时恢复 |

**⟹ `0 < margin` 是裁决 O（「信息不足则停、恢复需严格更足」）的充要条件。**
**⚠ 这是 D7 意义上**真正有内容**的约束**：没有它，`step` 要么退化（=0），要么违反语义（<0）。
-/


/-! ===========================================================================
  `FateV2.Loop/MainLoop` —— **主线的循环结构**（**第 227 轮**，路线图缺口 7）

  ## 依据：作者裁决 O（**改变主线的拓扑结构**）

  **作者原话（逐字）**：
  > 「唔不对啊这个整个他是不是可以直接拿因果直接进入这个分类系统的循环提取关系和规则」
  > 「循环：**分类反过来修因果**」
  > 「**不结束** 因为是持续加入信息持续循环的那种想法」
  > 「它**又不是细分**，是**抽象和解构**的思路，就是**在没有足够信息的情况下继续会过拟合才临时停止**」

  ## ⚠ 作者明确否定了两种理解

  | 理解 | 作者回应 |
  |---|---|
  | ①「两条路并行/分工」 | ❌ **不是 —— 是循环** |
  | ②「循环 = 无限细分」 | ❌ **「它又不是细分」** |

  ## 正解：**抽象与解构是双向的**

  | | 细分（错） | **抽象与解构（对）** |
  |---|---|---|
  | 方向 | **单向**：越分越细 | **双向**：**向上抽象 + 向下解构** |
  | 结果 | **格爆炸** | **层级重构** |

  ## 本文件的交付

  1. **两个目光**：`abstractUp`（向上抽象）/ `deconstructDown`（向下解构）
  2. **「不是细分」的形式化**：两者方向相反 ⟹ 不是单向递增
  3. **双向可逆性**：抽象后解构回到原层
  4. **终止判据**：**信息不足 ⟹ 停**（对应裁决 K 的过拟合边界）
  5. **「不结束」的形式化**：状态随信息量变化，不冻结终态

  **⚠ 本文件不含「具体的层是什么」** —— 因为作者说「先研究不确定，怎么有效怎么来」。
  **⟹ 故把「层」抽象为 `ℕ`，把循环抽象为状态转移。**
================================================================================ -/

namespace FateV2.Loop.MainLoop

/-! ## §1 **两个目光**（**向上抽象 / 向下解构**） -/

/-- **层级**：`ℕ`。**层号越大 = 越抽象；越小 = 越具体（构成）**。 -/
abbrev Level := ℕ

/-- **向上抽象**：从层 `n` 到更高的层（「它归于何类」）。 -/
def abstractUp (n : Level) (k : ℕ) : Level := n + k

/-- **向下解构**：从层 `n` 到更低的层（「它由何构成」）。 -/
def deconstructDown (n : Level) (k : ℕ) : Level := n - k

/-! ## §2 **「不是细分」的形式化**

**⚠ 作者说「它又不是细分」。**

**「细分」意味着**层数单向递增**；而「抽象与解构」是**双向**的。** -/

/-- **抽象向上走**：若 `k > 0`，`abstractUp n k > n`。 -/
theorem abstractUp_gt (n : Level) {k : ℕ} (hk : 0 < k) :
    n < abstractUp n k := by
  show n < n + k
  exact Nat.lt_add_of_pos_right hk

/-- **解构向下走**：若 `0 < k ≤ n`，`deconstructDown n k < n`。 -/
theorem deconstructDown_lt (n : Level) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    deconstructDown n k < n := by
  show n - k < n
  exact Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) hk

/-- **「不是细分」的核心**：

**若循环只做细分（单向递增），则层号**永不下降**。
**而本结构的两方向**恰相反** ⟹ 存在两个方向都改变层号的实例 ⟹ **不是细分**。** -/
theorem not_pure_subdivision :
    ∃ (n : Level) (k : ℕ), 0 < k ∧ k ≤ n ∧
      n < abstractUp n k ∧ deconstructDown n k < n := by
  refine ⟨2, 1, by norm_num, by norm_num, ?_, ?_⟩
  · exact abstractUp_gt 2 (by norm_num)
  · exact deconstructDown_lt 2 (by norm_num) (by norm_num)

/-! ## §3 **双向可逆性**（**在稳定点附近**） -/

/-- **先抽象 `k` 层，再解构 `k` 层，回到原层**（当 `k ≤ n`）。

**读法**：**两个目光在层级上互为逆**（只要不越过 0）。

**依哲学依据「投向即构成」**：
**向上目光（抽象）与向下目光（解构）在稳定点附近互相还原。** -/
theorem abstractUp_deconstructDown (n : Level) (k : ℕ) (hk : k ≤ n) :
    deconstructDown (abstractUp n k) k = n := by
  show n + k - k = n
  exact Nat.add_sub_cancel n k

/-! ## §4 **终止判据：信息不足 ⟹ 停**（**裁决 O-2 + 裁决 K**）

**作者原话**：
> 「**不结束** 因为是持续加入信息持续循环的那种想法」
> 「就是**在没有足够信息的情况下继续会过拟合才临时停止**」

**故循环有**两个驱动 / 抑制因素**：
- **有足够新信息** → 继续循环
- **信息不足** → 临时停止（否则过拟合）
- **新信息到来** → 恢复循环

**⚠ 这与裁决 K 完全一致**（「误差须刚好落在恰好拟合/过拟合的边界」）。** -/

/-- **循环的状态**。 -/
inductive LoopState : Type
  /-- **运行中**（有足够新信息） -/
  | running
  /-- **临时停止**（信息不足，继续会过拟合） -/
  | paused
  deriving DecidableEq, Repr

/-- **信息量**（本文件不指定其具体度量 —— 依作者「怎么有效怎么来」）。 -/
abbrev InfoLevel := ℝ

/-- **噪声尺度**（裁决 K 的「信号与噪声的分界尺度」）。 -/
abbrev NoiseScale := ℝ

/-- **转移函数**（**第 276 轮重写：依赖当前状态**）。

**判据**（裁决 O + 裁决 K）：

| 当前状态 | 转移条件 | 语义 |
|---|---|---|
| `.running` | `noise < info` → `.running` | **信息严格多于噪声 ⟹ 继续** |
| `.running` | `info ≤ noise` → `.paused` | **信息不足 ⟹ 暂停**（否则过拟合）|
| `.paused` | `noise + margin < info` → `.running` | **恢复需严格更足的信息**（余量 `margin`）|
| `.paused` | `info ≤ noise + margin` → `.paused` | **不够更足 ⟹ 继续停** |

**⚠ `margin`（恢复余量）不是装饰**：
- `margin = 0` ⟹ `step` 退化为**状态无关**（即第 275 轮的缺陷）；
- `margin < 0` ⟹ 暂停态在信息**更少**时恢复，**违反裁决 O**；
- `0 < margin` ⟹ 唯一同时满足「依赖状态」与「恢复需严格更足」的区间。
见 `step_state_irrelevant_iff_margin_zero` / `neg_margin_violates_O`。** -/
noncomputable def step (info : InfoLevel) (noise : NoiseScale) (margin : ℝ) :
    LoopState → LoopState
  | .running => if noise < info then .running else .paused
  | .paused  => if noise + margin < info then .running else .paused

/-! ### §4.1 **分支判据**（**依赖状态**：每支各一条） -/

/-- **`.running` 下：信息严格充足 ⟹ 继续**。 -/
theorem step_from_running_running_iff (info : InfoLevel) (noise : NoiseScale)
    (margin : ℝ) :
    step info noise margin .running = .running ↔ noise < info := by
  simp only [step]; split <;> simp_all

/-- **`.running` 下：信息不足 ⟹ 暂停**。 -/
theorem step_from_running_paused_iff (info : InfoLevel) (noise : NoiseScale)
    (margin : ℝ) :
    step info noise margin .running = .paused ↔ info ≤ noise := by
  simp only [step]; split <;> simp_all

/-- **`.paused` 下：信息严格更足 ⟹ 恢复**。 -/
theorem step_from_paused_running_iff (info : InfoLevel) (noise : NoiseScale)
    (margin : ℝ) :
    step info noise margin .paused = .running ↔ noise + margin < info := by
  simp only [step]; split <;> simp_all

/-- **`.paused` 下：不够更足 ⟹ 继续停**。 -/
theorem step_from_paused_paused_iff (info : InfoLevel) (noise : NoiseScale)
    (margin : ℝ) :
    step info noise margin .paused = .paused ↔ info ≤ noise + margin := by
  simp only [step]; split <;> simp_all

/-! ### §4.2 **统一的运行 / 暂停判据**（**依赖状态**） -/

/-- **运行判据（依赖状态）**：下一步运行 ⟺ 当前状态对应的门槛被满足。

**⚠ 与第 275 轮的区别**：旧版右侧只有 `noise < info`（对任意 `s`）；
新版右侧**分状态**给出两个不同门槛。** -/
theorem step_running_iff (info : InfoLevel) (noise : NoiseScale) (margin : ℝ)
    (s : LoopState) :
    step info noise margin s = .running ↔
      (s = .running ∧ noise < info) ∨ (s = .paused ∧ noise + margin < info) := by
  cases s <;> simp [step]

/-- **暂停判据（依赖状态）**。 -/
theorem step_paused_iff (info : InfoLevel) (noise : NoiseScale) (margin : ℝ)
    (s : LoopState) :
    step info noise margin s = .paused ↔
      (s = .running ∧ info ≤ noise) ∨ (s = .paused ∧ info ≤ noise + margin) := by
  cases s <;> simp [step, not_lt]

/-- **裁决 O-2 的核心（修正版）**：**暂停的理由是「当前状态下信息不足」**。

**`.running` 的不足门槛是 `info ≤ noise`；`.paused` 的不足门槛是 `info ≤ noise + margin`。**

**⚠ 旧版（第 275 轮）声称「唯一门槛 `info ≤ noise`」——那只是常值函数的值。** -/
theorem paused_iff_insufficient_info (info : InfoLevel) (noise : NoiseScale)
    (margin : ℝ) (s : LoopState) :
    step info noise margin s = .paused ↔
      (s = .running ∧ info ≤ noise) ∨ (s = .paused ∧ info ≤ noise + margin) :=
  step_paused_iff info noise margin s

/-! ### §4.3 **`step` 真正依赖状态**（**修掉常值缺陷**） -/

/-- **核心修复**：`0 < margin` ⟹ 存在参数使 `step` **区分状态**。

**构造**：取 `info = noise + margin/2` —— 此时
- `.running` 看到 `noise < info`（真）⟹ `.running`；
- `.paused` 看到 `noise + margin < info`（假）⟹ `.paused`。

**⟹ 两个状态的下一步不同 ⟹ `step` 不是常值函数。** -/
theorem step_depends_on_state (noise : NoiseScale) (margin : ℝ) (hm : 0 < margin) :
    ∃ (info : InfoLevel),
      step info noise margin .running ≠ step info noise margin .paused := by
  refine ⟨noise + margin / 2, ?_⟩
  have h1 : noise < noise + margin / 2 := by linarith
  have h2 : ¬ noise + margin < noise + margin / 2 := by linarith
  simp only [step, if_pos h1, if_neg h2]
  exact fun h => LoopState.noConfusion h

/-- **更强的修复**：**`margin ≠ 0` 都可能找到区分状态的参数**。

**分两种情况**：
- `margin > 0`：取 `info = noise + margin/2`（见 `step_depends_on_state`）；
- `margin < 0`：取 `info = noise` —— `.running` 停（`¬ noise < noise`），
  `.paused` 恢复（`noise + margin < noise`）。

**⚠ 但 `margin < 0` 的那一半**语义是反的**（见 `neg_margin_violates_O`）。** -/
theorem step_depends_on_state_of_ne_zero (noise : NoiseScale) (margin : ℝ)
    (hm : margin ≠ 0) :
    ∃ (info : InfoLevel),
      step info noise margin .running ≠ step info noise margin .paused := by
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · refine ⟨noise, ?_⟩
    have h2 : noise + margin < noise := by linarith
    simp only [step, if_neg (lt_irrefl noise), if_pos h2]
    exact fun h => LoopState.noConfusion h
  · exact step_depends_on_state noise margin hpos

/-- **D7 判决**：`step` **状态无关（对所有 info）** ⟺ `margin = 0`。

**这说明**：
- **`margin = 0` 时 `step` 对所有 info 退化为第 275 轮的常值缺陷；**
- **`margin ≠ 0` 时存在 info 使 `step` 依赖状态。**

**⚠ 也说明「历史缺陷」不是写法问题，而是**参数缺失**问题 ——
旧 `step` 相当于强制 `margin = 0`。** -/
theorem step_state_irrelevant_iff_margin_zero (noise : NoiseScale) (margin : ℝ) :
    (∀ (info : InfoLevel) (s t : LoopState),
        step info noise margin s = step info noise margin t) ↔
      margin = 0 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨info', hdep⟩ := step_depends_on_state_of_ne_zero noise margin hne
    exact hdep (h info' LoopState.running LoopState.paused)
  · intro h0 info' s t
    subst h0
    have hz : noise + 0 = noise := by ring
    cases s <;> cases t <;> simp [step, hz]

/-- **D7 判决（语义侧）**：`margin < 0` 时暂停态会在**信息更少**时恢复 ——
**这恰好违反裁决 O（「恢复需严格更足」）**。

**构造**：取 `info = noise + margin/2`（`margin < 0` 时该值 `< noise`），
此时 `.paused → .running` 而信息量已低于噪声。 -/
theorem neg_margin_violates_O (noise : NoiseScale) (margin : ℝ) (hm : margin < 0) :
    ∃ (info : InfoLevel), info < noise ∧
      step info noise margin .paused = .running := by
  refine ⟨noise + margin / 2, by linarith, ?_⟩
  have h : noise + margin < noise + margin / 2 := by linarith
  simp only [step, if_pos h]

/-! ### §4.4 **恢复与滞回** -/

/-- **新信息到来 ⟹ 恢复循环**（**需严格更足**）。

**⚠ 与旧版的区别**：旧版对**任意状态**成立（因常值）；
新版**只在 `.paused` 状态**成立，且门槛是 `noise + margin < info`。** -/
theorem resume_on_new_info (noise : NoiseScale) (margin : ℝ) (info' : InfoLevel)
    (h : noise + margin < info') :
    step info' noise margin .paused = .running := by
  simp only [step, if_pos h]

/-- **滞回 / 锁存**：`margin ≥ 0` 时，**暂停后不会在同一参数下自发恢复**。

**读法**：这正是「恢复需**严格更足**」的精确形式 ——
若 `info ≤ noise`（导致暂停）且 `info ≤ noise + margin`（未严格更足），
则系统**锁在** `.paused`。** -/
theorem hysteresis_no_self_resume (info : InfoLevel) (noise : NoiseScale)
    (margin : ℝ) (hm : 0 ≤ margin)
    (h1 : step info noise margin .running = .paused)
    (h2 : step info noise margin .paused = .running) : False := by
  rw [step_from_running_paused_iff] at h1
  rw [step_from_paused_running_iff] at h2
  linarith

/-- **锁存的正面形式**：`info ≤ noise` 且 `info ≤ noise + margin` 时，
从 `.running` 出发两步后**停在** `.paused`。 -/
theorem latches_at_paused (info : InfoLevel) (noise : NoiseScale) (margin : ℝ)
    (h1 : info ≤ noise) (h2 : info ≤ noise + margin) :
    step info noise margin (step info noise margin .running) = .paused := by
  have hA : step info noise margin .running = .paused := by
    rw [step_from_running_paused_iff]; exact h1
  rw [hA]
  simp only [step]
  rw [if_neg (not_lt.mpr h2)]

/-! ## §5 **「不结束」的形式化**

**作者说「不结束」——⟹ 不存在「终态」，不冻结终局。**

**形式化**：**状态随信息量变化而变化** ⟹ **不是恒定**。** -/

/-- **「不结束」的形式化**：**状态不是恒定的**（随信息量改变）。

**⚠ 保留旧名（下游 `SigCheck` 依赖），构造改用新参数顺序。** -/
theorem not_terminated :
    ∃ (i₁ i₂ : InfoLevel) (n : NoiseScale) (m : ℝ),
      step i₁ n m .running ≠ step i₂ n m .running := by
  refine ⟨2, 0, 1, 0, ?_⟩
  intro hcontra
  have h1 : step 2 1 0 LoopState.running = LoopState.running := by
    simp only [step, if_pos (by norm_num : (1:ℝ) < 2)]
  have h2 : step 0 1 0 LoopState.running = LoopState.paused := by
    simp only [step, if_neg (by norm_num : ¬(1:ℝ) < 0)]
  rw [h1, h2] at hcontra
  exact absurd hcontra (by decide)

/-- **两种状态都可达**（`margin = 1` 下）。 -/
theorem both_states_reachable :
    (∃ (i : InfoLevel) (n : NoiseScale) (m : ℝ) (s : LoopState), step i n m s = .running)
    ∧ (∃ (i : InfoLevel) (n : NoiseScale) (m : ℝ) (s : LoopState), step i n m s = .paused) := by
  refine ⟨⟨2, 1, 1, .running, ?_⟩, ⟨0, 1, 1, .running, ?_⟩⟩
  · simp only [step, if_pos (by norm_num : (1:ℝ) < 2)]
  · simp only [step, if_neg (by norm_num : ¬(1:ℝ) < 0)]

/-! ## §6 **第 291 轮：循环的**收敛性**判决 —— `margin` 的真实作用**

**任务（缺口 7，第 291 轮）要求证**
> 「若每步 `margin > 0`，则循环**至少需要 `k` 步**才能稳定」

**⚠ 本轮实测结论：该命题为**假**（`not_needs_two_steps`）。**
`0 < margin` 时 `step` **1 步即稳定**（`stable_within_one_of_margin_nonneg`，
只需 `0 ≤ margin`），比任务要求的「至少 `k` 步」**强**（恰为「至多 1 步」）。

**⟹ 「`margin` 使循环变慢」是**错误直觉**：`margin` 的作用不是**增加步数**，
而是在 **`margin < 0`** 时**破坏收敛**（产生 2-周期，`neg_margin_never_stable`）。

### §6.1 主判决表

| 定理 | 内容 | D7 | D8 |
|---|---|---|---|
| `stable_within_one_of_margin_nonneg` | `0 ≤ margin` ⟹ `step^[1] = step^[2]`（全参数）| `hm` **真必要**（`hm_needed`）| **有内容**：4 分支穷举，`margin` 出现在 `linarith` |
| `stable_from_one` | `N ≥ 1` ⟹ `step^[N] = step^[1]` | 同上 | 归纳 + 用上一条 |
| `hm_needed` | 上述**非空真**：`margin<0` 有见证 | — | **真反例**（`margin = -1`，`info = -1/2`）|
| `neg_margin_never_stable` | `margin < 0` ⟹ **任意 `N` 都不稳定**（永 2-周期）| `hm` 必要 | **有内容**：`%2` 奇偶归纳 |
| `not_needs_two_steps` | 任务原命题（`0<margin` 需 `≥2` 步）**为假** | — | **否定任务假设** |

**最强陈述（可证上限）**：
`0 ≤ margin` ⟺ （在 `running/paused` 上）`step` 1 步收敛；
`margin < 0` ⟹ 永不收敛。「步数 = 1」与 `margin` 大小**无关**。 -/

/-- **`0 ≤ margin` ⟹ `step` 1 步即稳定**（任意 `info`、`noise`、状态）。

**⚠ 这是「主循环稳定步数」的**精确答案**：步数上界恒为 **1**，
与 `margin` 的大小、`info`、`noise` **全都无关** —— 只依赖 `margin` 的**符号**。

**⚠ 与任务预期相反**：任务设想「`margin > 0` ⟹ 至少 `k` 步」，
实测为「`margin ≥ 0` ⟹ 至多 1 步」（见 `not_needs_two_steps` 的否证）。 -/
theorem stable_within_one_of_margin_nonneg (info : InfoLevel) (noise : NoiseScale)
    (margin : ℝ) (hm : 0 ≤ margin) (s : LoopState) :
    (step info noise margin)^[1] s = (step info noise margin)^[2] s := by
  rw [show (2:ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
  cases s with
  | running =>
    by_cases h : noise < info
    · have hr := (step_from_running_running_iff info noise margin).mpr h
      rw [hr]; exact hr.symm
    · have hr := (step_from_running_paused_iff info noise margin).mpr (not_lt.mp h)
      have hs := (step_from_paused_paused_iff info noise margin).mpr (by linarith)
      rw [hr, hs]
  | paused =>
    by_cases hp : noise + margin < info
    · have hr := (step_from_paused_running_iff info noise margin).mpr hp
      have hs := (step_from_running_running_iff info noise margin).mpr (by linarith)
      rw [hr, hs]
    · have hr := (step_from_paused_paused_iff info noise margin).mpr (not_lt.mp hp)
      rw [hr]; exact hr.symm

/-- **`0 ≤ margin` ⟹ 对任意 `N ≥ 1`，第 `N` 步 = 第 1 步**（一次到位）。 -/
theorem stable_from_one (info : InfoLevel) (noise : NoiseScale) (margin : ℝ)
    (hm : 0 ≤ margin) (s : LoopState) :
    ∀ N : ℕ, 1 ≤ N →
      (step info noise margin)^[N] s = (step info noise margin)^[1] s := by
  intro N hN
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  induction k with
  | zero => simp
  | succ j ih =>
    rw [show j + 1 + 1 = (j + 1) + 1 from rfl, Function.iterate_succ_apply', ih (by omega)]
    exact (stable_within_one_of_margin_nonneg info noise margin hm s).symm

/-- **D7：`hm : 0 ≤ margin` 是**真前提** —— 去掉它命题即假。**

**见证**：`noise = 0, margin = -1, info = -1/2`。此时
`.running → .paused → .running`（2-周期），故 `step^[1] ≠ step^[2]`。 -/
theorem hm_needed :
    ¬ (∀ (info : InfoLevel) (noise : NoiseScale) (margin : ℝ) (s : LoopState),
        (step info noise margin)^[1] s = (step info noise margin)^[2] s) := by
  intro h
  have hb := h (-0.5) 0 (-1) LoopState.running
  rw [show (2:ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one] at hb
  have c1 := (step_from_running_paused_iff (-0.5) (0:ℝ) (-1)).mpr (by norm_num)
  have c2 := (step_from_paused_running_iff (-0.5) (0:ℝ) (-1)).mpr (by norm_num)
  rw [c1, c2] at hb
  exact LoopState.noConfusion hb

/-- **`margin < 0` ⟹ **任意 `N` 都不稳定**（永 2-周期）。**

**⚠ 这是缺口 7 关于 `margin` 的**唯一真实「步数」结论**：
`margin < 0` 时 `step` 在 `.running ↔ .paused` 上**永不收敛**，
故不存在任何「稳定步数 `N`」。

**证明**：奇偶归纳 —— `step^[2k] = .running`，`step^[2k+1] = .paused`。 -/
theorem neg_margin_never_stable (noise : NoiseScale) (margin : ℝ) (hm : margin < 0) :
    ∀ N : ℕ,
      (step (noise + margin / 2) noise margin)^[N] LoopState.running ≠
      (step (noise + margin / 2) noise margin)^[N + 1] LoopState.running := by
  have h1 : ¬ (noise < noise + margin / 2) := by linarith
  have h2 : noise + margin < noise + margin / 2 := by linarith
  have hR : step (noise + margin / 2) noise margin LoopState.running = LoopState.paused :=
    (step_from_running_paused_iff (noise + margin/2) noise margin).mpr (not_lt.mp h1)
  have hP : step (noise + margin / 2) noise margin LoopState.paused = LoopState.running :=
    (step_from_paused_running_iff (noise + margin/2) noise margin).mpr h2
  have key : ∀ k : ℕ,
      (step (noise + margin / 2) noise margin)^[k] LoopState.running =
        (if k % 2 = 0 then LoopState.running else LoopState.paused) := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      rcases Nat.even_or_odd j with ⟨m, hmj⟩ | ⟨m, hmj⟩
      · rw [if_pos (by omega), hR, if_neg (by omega)]
      · rw [if_neg (by omega), hP, if_pos (by omega : (j+1) % 2 = 0)]
  intro N
  rw [key N, key (N+1)]
  by_cases hN : N % 2 = 0
  · rw [if_pos hN, if_neg (by omega : ¬((N+1) % 2 = 0))]
    exact fun h => LoopState.noConfusion h
  · rw [if_neg hN, if_pos (by omega : (N+1) % 2 = 0)]
    exact fun h => LoopState.noConfusion h

/-- **否证任务原命题**：「`0 < margin` ⟹ 循环至少需 `k ≥ 2` 步才能稳定」为**假**。

**✅ 真相**：`0 < margin`（更强：`0 ≤ margin`）时 `step` **至多 1 步**即稳定
（`stable_within_one_of_margin_nonneg`）⟹ 不存在「必须 2 步及以上」的参数。 -/
theorem not_needs_two_steps (noise : NoiseScale) (margin : ℝ) (hm : 0 < margin)
    (info : InfoLevel) :
    ¬ ((step info noise margin)^[1] LoopState.running ≠
       (step info noise margin)^[2] LoopState.running) := by
  intro h
  exact h (stable_within_one_of_margin_nonneg info noise margin (le_of_lt hm) LoopState.running)

end FateV2.Loop.MainLoop

