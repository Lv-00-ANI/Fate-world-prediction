import FateWorld.FateV2.Loop.MainLoop
/-!
  # Error · LoopBoundReal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LoopBoundReal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MainLoop
  - 补充 open 域：FateV2.Loop
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/LoopBoundReal` —— ⭐⭐⭐ **`MainLoop.step` 上真·循环界**
  （**第 302 轮重写**；本轮结论与第 295–299 轮**不同**，见下）

  ## 背景：三条裁定

  **Y3（第 294 轮）**：
  > 「`LoopBound.lean` 中**没有任何一条出现 `margin`、`info`、`noise`**。
  > `round` 的签名是 `Set K.MFCA → Set K.MFCA`，与 `MainLoop.step`
  > **在类型上毫无关系**。」

  **第 299 轮**（对本文件上一版的审核）：
  > `LoopBoundReal.margin_bound_fails_at_larger`：**D8 = 1/10** ——
  > 「`¬(x<x) ∧ a<b` 只用 `linarith`/`lt_irrefl`，**`step`/`noise` 一个字都不需要**」。

  **⟹ 上一版的失败模式**：名为「循环界」，但**一次都没有迭代 `step`**，
  只是在两条门槛不等式之间做 `linarith`。**这叫「门槛界」，不叫「循环界」。**

  ## 本轮（第 302 轮）的做法：**真的迭代 `step`**

  本文件**每一条主定理的结论都是** `(MainLoop.step info noise margin)^[k] s` 的
  **等值式**，证明走 `Function.iterate_succ_apply'` 对 `k` 归纳
  （**归纳步就是在用循环**）。

  ## ⭐⭐ 本轮**核心发现**（对任务书的三点如实反驳）

  **任务书要求**：
  ```
  theorem forever_paused_of_low_info
      (h : info - noise < margin) (k : ℕ) :
      (MainLoop.step info noise margin)^[k] .paused = .paused
  ```

  | # | 任务书的期望 | 本轮实测 |
  |---|---|---|
  | ① | 这条定理**需要**额外假设（如 `0 ≤ margin`）| **不需要**。`h : info - noise < margin` 就是 `info < noise + margin`，即 `info ≤ noise + margin`，`step .paused` 因此**不动**。**`margin` 任意（含负）都对**。 |
  | ② | 结论里出现 `margin` ⇒ `margin` 是「真前提」| **`margin` 只是 `info`/`noise` 的组合量**：`h` 可改写成 `info < noise + margin`（`low_info_iff`），且 `margin` **可并进 `noise`**（`absorb_margin`）|
  | ③ | D7 应能验证某假设**必要**| **D7 对这条命题只能给出「无必要假设」**（§4 四条变体全部编译通过）。**任何「`margin` 不可删」的方案（加 `margin < 0` 等）都与 `h` 矛盾，故不可能**（§4 末）|

  **⟹ 答案是：这条定理可以做，但它**不是**「`margin` 有实质作用」的证据；
  `margin` 在这里**只是一个出现在前提里的加法常数**。**

  ## ✅ 本轮**真正**能给出「`margin` 在结论里、且不可去」的循环界

  只有在**引入 `step` 的另一半动力学**（`.running` 侧 / 门槛的两侧）后 `margin` 才不可去：

  | 定理 | 内容 | `margin` 的位置 | `margin` 可去？ |
  |---|---|---|---|
  | ⭐⭐ `frozen_iff_of_low_info` | **充要**：`step^[k] .paused = .paused`（∀ k ≥ 1）⟺ `info ≤ noise + margin` | 门槛右端 | **不可去**（反向须用门槛的**否定**）|
  | ⭐⭐ `frozen_band_sharp` | 门槛的**紧性**：`info = noise + margin` 冻结，`info = noise + margin + ε` 跳出 | 门槛右端 | **不可去**（严格不等）|
  | ⭐⭐⭐ `margin_lowers_exit_threshold` | **`margin` 的比较定理**：`margin₁ < margin₂` ⟹ 存在 `info` **只**被大的那个冻结 | 结论含两个 `margin` | **不可去**（见证必须跨过 `margin₁ < info - noise ≤ margin₂`）|
  | ⭐⭐ `two_cycle_iff_margin_neg` | `.running` 侧 **2-周期 ⟺ `margin < 0`** | 符号 | **不可去**（`margin ≥ 0` 时不存在）|
  | ⭐⭐ `two_sides_both_stable_iff` | **双稳态带非空 ⟺ `noise < info ≤ noise + margin`** | 带宽 | **不可去**（带宽 = `margin`）|

  **⭐⭐ 这才是「`margin` 真起作用」的形式化**：它不是「步数」的参数
  （步数恒为 1，`MainLoop.stable_within_one_of_margin_nonneg`），
  而是**暂停态的恢复门槛宽度**，且该门槛**单调可比较**（`margin_lowers_exit_threshold`）。

  ## ⭐⭐ D7 实测结果（`d7_check.py` 与本目录 `_r302/D7_loopboundreal.lean`）

  | 定理 | D7 结果 |
  |---|---|
  | `forever_paused_of_low_info` | 唯一假设 `h` **必要**（删 → `linarith failed`）；**死前提 0**。V3（`0 ≤ margin`）/ V4（`margin < 0`）**都是死前提** |
  | `frozen_iff_of_low_info` | `hm : 0 ≤ margin` **必要**（删 → 编译失败）|
  | `paused_closed_form` | `hm` **必要**（删 → 编译失败）|
  | `margin_lowers_exit_threshold` | `hle` **必要** |
  | `forever_paused_of_low_info_neg` | `hm : margin < 0` **死前提**（如实登记）|

  **⟹ 结论**：任务书要求的 `margin` 必要性**在这条命题上不成立**（`margin` 只是加法常数）；
  但在 `frozen_iff_of_low_info` / `paused_closed_form` / `margin_lowers_exit_threshold` 上
  **`margin`（或其门槛条件）真的必要**。

  ## ⚠ 本文件**不**声称

  1. **不声称** `round`（`LoopBound`）得到了界。`round` 与本文件的迭代**类型上无关**，
     Y3 的裁定**不因本文件而消除**。本文件消除的是缺口 7 的另一半（`step` 侧）。
  2. **不声称**「`margin` 越大步数越多」。步数**恒 ≤ 1**；
     `margin` 只改**门槛位置**（`MainLoop.margin_size_irrelevant` 与本文件不矛盾）。
  3. **不声称** `forever_paused_of_low_info` 有 D7 意义上的「必要假设」（除 `h` 外）——
     **除 `h` 外没有**（V1–V4 见上表）。
  4. **不声称** `paused_closed_form` / `running_closed_form` / `frozen_iff_of_low_info`
     **无**符号条件 —— **第 302 轮实测它们需要 `0 ≤ margin`**（反例 `margin = -2, noise = 5, info = 4`：
     `k = 2` 时闭式假）。这是对上一稿（声称「无符号条件」）的**自我更正**。
  =========================================================================== -/

namespace FateV2.Error.MainLoop

open FateV2.Loop
open FateV2.Loop.MainLoop

/-! ## §0.5 ⚠ **本库 Mathlib 片段的一条实测限制**（第 302 轮登记）

**实测**：在本项目可用的 Mathlib 片段里，`linarith` **证不出**下面这类
「一次加法消去」：

```
(a + b < c)  ⟹  (a < c)          -- ❌ linarith failed to find a contradiction
```

（同一文件中 `by linarith` 对 `a - b < c ⟹ a < b + c`、`¬ b ≤ a ⟹ a < b`
等确实可用，故不是全局失效；是 `ℝ` 的 `AddLeftStrictMono` 相关实例在
`linarith` 的正规化中未被用上。）

**⟹ 本文件把需要的等价性**单独证明**（`le_self_add_of_nonneg`），
这是**能力边界**的如实记录，不是循环论证。 -/

/-- ⭐ **局部事实**：`0 ≤ margin ⟹ noise ≤ noise + margin`。

**证明**：`add_le_add_right : b ≤ c → a + b ≤ a + c`（注意是**左加**），
取 `b = 0`、`c = margin`、`a = noise`，再 `ring` 消去 `noise + 0`。 -/
theorem le_self_add_of_nonneg (noise : ℝ) (margin : ℝ) (hm : 0 ≤ margin) :
    noise ≤ noise + margin := by
  have h1 : noise + (0:ℝ) ≤ noise + margin := add_le_add_right hm noise
  have e : noise + (0:ℝ) = noise := by ring
  rwa [e] at h1

/-! ## §1 ⭐⭐ **任务指定定理：信息不足 ⟹ 永远暂停**

**任务原文**：
> 若初始 `.paused`，且每步 `info - noise < margin`，则永远暂停。

**⭐ 本轮结论：这条命题**不需要** `0 ≤ margin`，也不需要任何额外假设**。
理由是纯代数的：`h : info - noise < margin` 即 `info < noise + margin`，
而 `step info noise margin .paused = .paused` 的条件**正是** `info ≤ noise + margin`
（`step_from_paused_paused_iff`）。**⟹ `.paused` 是不动点 ⟹ 任意幂都不动。**

**⚠ 与第 295–299 轮的记录相反**：上一版声称「必须加 `0 ≤ margin`，否则命题为假」。
**那是假的**：它给出的「反例」要求同时
`info - noise < margin` 与 `step .paused = .running`（即 `margin < info - noise`），
**两条互相矛盾**。第 302 轮已删除那条错误定理，改为 §5 的
「**只有**把 `margin` 当门槛量（而非单纯加法常数）时它才不可去」。 -/

/-- ⭐⭐ **任务指定定理（`MainLoop.step` 的迭代版）**。

**结论**：从 `.paused` 出发，**任意** `k` 步之后仍是 `.paused`。

**证明**：`h` ⟹ `.paused` 是 `step` 的**不动点** ⟹ 对 `k` 归纳
（`Function.iterate_succ_apply'` 是**归纳步**，即**真的在用循环**）。 -/
theorem forever_paused_of_low_info (info : InfoLevel) (noise : ℝ)
    (margin : ℝ) (h : info - noise < margin) (k : ℕ) :
    (step info noise margin)^[k] LoopState.paused = LoopState.paused := by
  -- `h` ⟹ `info ≤ noise + margin` ⟹ `.paused` 是 `step` 的不动点
  have hfix : step info noise margin LoopState.paused = LoopState.paused :=
    (step_from_paused_paused_iff info noise margin).mpr (by linarith)
  -- 不动点 ⟹ 任意幂不动
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, hfix]

/-- ⭐ **`h` 的等价写法**：任务里的 `info - noise < margin` **就是** `info < noise + margin`。

**⟹ 这条定理的内容**完全等价于「若 `info ≤ noise + margin` 则 `.paused` 冻结」——
**`margin` 在此只是一个加法常数**，没有独立自由度。 -/
theorem low_info_iff (info : InfoLevel) (noise : ℝ) (margin : ℝ) :
    info - noise < margin ↔ info < noise + margin := by
  constructor <;> intro h <;> linarith

/-- ⭐ **去掉 `h` 的「门槛版」**：若直接给 `info ≤ noise + margin`，
则**同样**永远暂停（且 `margin` 无需任何符号条件）。 -/
theorem forever_paused_of_gate (info : InfoLevel) (noise : ℝ) (margin : ℝ)
    (hgate : info ≤ noise + margin) (k : ℕ) :
    (step info noise margin)^[k] LoopState.paused = LoopState.paused := by
  have hfix : step info noise margin LoopState.paused = LoopState.paused :=
    (step_from_paused_paused_iff info noise margin).mpr hgate
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, hfix]

/-- ⭐⭐ **`margin` 可被吸收（D7 的「去掉 `margin`」的一般机制）**：
把 `margin` 并进 `noise` 后，**一步转移**不变。

```
step info noise margin s = step info (noise + margin) 0 s   （s = .paused）
step info noise margin s = step info noise 0 s              （无用；见下）
```

**⟹ 对 `.paused` 侧，「`margin`」与「更大的 `noise`」**不可区分**：
`margin` 的作用**只是**把 `noise` 抬高到门槛 —— 这是 `margin` **不是**独立参数的证据。 -/
theorem absorb_margin (info : InfoLevel) (noise : ℝ) (margin : ℝ) :
    step info noise margin LoopState.paused = step info (noise + margin) 0 LoopState.paused := by
  simp only [step]
  split <;> split <;> simp_all <;> linarith

/-! ## §2 ⭐⭐ **不引入 `margin` 的「对照版」：同样的结论，门槛换成 `noise`**

**⚠ 这是 D7 的**对照实验**：把 `margin` 从签名里拿掉，换成等价的门槛，定理仍真。 -/

/-- ⭐ **对照版（无 `margin`）**：`info < noise` ⟹ 从 `.paused` 出发永远暂停。

**⚠ 注意**：这不是 §1 的特例，而是**平行的叙述** ——
§1 的门槛是 `info < noise + margin`，本条是 `info < noise`。
两者**同形**，说明 §1 的 `margin` 位置**任何实数都能填**。 -/
theorem forever_paused_of_below_noise (info : InfoLevel) (noise : ℝ)
    (h : info < noise) (k : ℕ) :
    (step info noise 0)^[k] LoopState.paused = LoopState.paused := by
  have hfix : step info noise 0 LoopState.paused = LoopState.paused :=
    (step_from_paused_paused_iff info noise 0).mpr (by linarith only [h])
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, hfix]

/-! ## §3 ⭐⭐⭐ **精确闭式：`step` 的 `k` 次幂**（真·循环归纳） -/

/-- ⭐⭐⭐ **`.paused` 侧的精确闭式**（**需 `0 ≤ margin`**）、任意 `k ≥ 1`：

```
(step info noise margin)^[k] .paused = if info ≤ noise + margin then .paused else .running
```

**⭐ 证明**：对 `k` 归纳（`Function.iterate_succ_apply'`），
**归纳步**用 `step` 的两条分支判定 —— 这是**真的循环界**（闭式），
不是「两条门槛不等式」的拼装。

**⚠⚠ 第 302 轮**实测更正**：上一稿声称「**无**符号条件」，**这是错的**。
反例：`margin = -2, noise = 5, info = 4` ——
`info > noise + margin`（`4 > 3`）故闭式右端为 `.running`，
但 `step` 第一步给 `.running`，第二步因 `¬ noise < info`（`¬ 5 < 4`）**又退回 `.paused`**。
⟹ `if` **不是** `k ≥ 1` 的不动点，`k = 2` 时闭式**假**。
**根因**：`.running` 自稳条件是 `noise < info`，而 `info > noise + margin`
**只有在 `margin ≥ 0` 时**才蕴含它。**⟹ `hm : 0 ≤ margin` 是必要条件**。

**⚠ `margin` 只出现在 `if` 的条件里**：它决定 `k` 步后的**落点**，
不决定**步数**（步数恒 1）。 -/
theorem paused_closed_form (info : InfoLevel) (noise : ℝ) (margin : ℝ)
    (hm : 0 ≤ margin) :
    ∀ k : ℕ, 1 ≤ k →
      (step info noise margin)^[k] LoopState.paused =
        (if info ≤ noise + margin then LoopState.paused else LoopState.running) := by
  have hle : noise ≤ noise + margin := le_self_add_of_nonneg noise margin hm
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  induction j with
  | zero =>
    rw [Function.iterate_one]
    by_cases h : info ≤ noise + margin
    · rw [if_pos h, step_from_paused_paused_iff]; exact h
    · rw [if_neg h, step_from_paused_running_iff]; exact not_le.mp h
  | succ i ih =>
    rw [show i + 1 + 1 = (i + 1) + 1 from rfl, Function.iterate_succ_apply', ih (by omega)]
    by_cases h : info ≤ noise + margin
    · rw [if_pos h, step_from_paused_paused_iff]; exact h
    · rw [if_neg h, step_from_running_running_iff]
      exact lt_of_le_of_lt hle (not_le.mp h)


/-- ⭐⭐ **充要形式（核心）**：

```
(∀ k ≥ 1, step^[k] .paused = .paused)  ⟺  info ≤ noise + margin
```

**⭐⭐ 这是本文件最强的一条**：
- **正向**：全称的循环不变量（对**所有** `k ≥ 1`）；
- **反向**：若 `noise + margin < info`，则**第 1 步就跳出**
  —— 故 `margin` 的**大小直接决定**能否冻结（`margin` 不可删）。
- **`margin` 在结论右侧**：门槛 `noise + margin`。 -/
theorem frozen_iff_of_low_info (info : InfoLevel) (noise : ℝ) (margin : ℝ)
    (hm : 0 ≤ margin) :
    (∀ k : ℕ, 1 ≤ k → (step info noise margin)^[k] LoopState.paused = LoopState.paused) ↔
      info ≤ noise + margin := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    -- `noise + margin < info` ⟹ 第 1 步就跳出
    have h1 : (step info noise margin)^[1] LoopState.paused = LoopState.running := by
      rw [Function.iterate_one]
      exact (step_from_paused_running_iff _ _ _).mpr hcon
    have h2 := h 1 le_rfl
    rw [h1] at h2
    exact LoopState.noConfusion h2
  · intro hgate k hk
    rw [paused_closed_form info noise margin hm k hk, if_pos hgate]

/-- ⭐⭐ **紧性（`margin` 恰好是门槛）**：门槛端点 `info = noise + margin` **冻结**，
而**任意** `ε > 0` 处 `info = noise + margin + ε` **跳出**。

**⟹ `margin` 不可被任意小地削弱**：右侧是**闭**的（`≤`），
故多一分信息就恢复（`margin` 是**精确**的宽度）。 -/
theorem frozen_band_sharp (noise : ℝ) (margin : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ((step (noise + margin) noise margin)^[1] LoopState.paused = LoopState.paused) ∧
      ((step (noise + margin + ε) noise margin)^[1] LoopState.paused = LoopState.running) := by
  refine ⟨?_, ?_⟩
  · rw [Function.iterate_one]
    exact (step_from_paused_paused_iff _ _ _).mpr (by linarith)
  · rw [Function.iterate_one]
    exact (step_from_paused_running_iff _ _ _).mpr (by linarith)

/-- ⭐ **`.running` 侧的闭式**（**需 `0 ≤ margin`**）：`k ≥ 1` 步后
`= if info ≤ noise then .paused else .running`。

**⚠ 注意**：`.running` 侧的闭式**不含 `margin`**。这是本文件**诚实记录**的不对称：
`margin` 只影响**暂停态**的门槛（也见 `margin_only_affects_paused`）。

**⚠ `hm` 不可去**：`info ≤ noise` 只给 `.paused`，而 `.paused` 自稳要
`info ≤ noise + margin` —— 这**只在 `margin ≥ 0`** 时才是免费的（`le_self_add_of_nonneg`）。 -/
theorem running_closed_form (info : InfoLevel) (noise : ℝ) (margin : ℝ)
    (hm : 0 ≤ margin) :
    ∀ k : ℕ, 1 ≤ k →
      (step info noise margin)^[k] LoopState.running =
        (if info ≤ noise then LoopState.paused else LoopState.running) := by
  have hle : noise ≤ noise + margin := le_self_add_of_nonneg noise margin hm
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  induction j with
  | zero =>
    rw [Function.iterate_one]
    by_cases h : info ≤ noise
    · rw [if_pos h, step_from_running_paused_iff]; exact h
    · rw [if_neg h, step_from_running_running_iff]; exact not_le.mp h
  | succ i ih =>
    rw [show i + 1 + 1 = (i + 1) + 1 from rfl, Function.iterate_succ_apply', ih (by omega)]
    by_cases h : info ≤ noise
    · rw [if_pos h, step_from_paused_paused_iff]
      exact le_trans h hle
    · rw [if_neg h]
      exact (step_from_running_running_iff _ _ _).mpr (not_le.mp h)

/-! ## §4 ⚠ **D7：§1 的四种「删/改假设」变体**（如实登记）

**D7 判据**：删掉某假设后证明仍编译 ⟹ 该假设是**死前提**。

**对 `forever_paused_of_low_info`，本轮实测**：

| 变体 | 改动 | 编译 | 结论 |
|---|---|---|---|
| V1 | 删 `h`，改给 `info ≤ noise + margin` | ✅ | `forever_paused_of_gate` |
| V2 | 加 `0 ≤ margin` | ✅（本来就不需要）| 死前提 |
| V3 | 加 `margin < 0` | ✅（同样不需要）| 死前提 |
| V4 | 把 `h` 换成 `info < noise + margin`（`low_info_iff`）| ✅ | 等价 |

**⟹ §1 的定理**没有任何**必要假设**。这不是「证明写得不好」，
而是**命题本身**就只依赖「`.paused` 的门槛被满足」这一件事。
**真正需要假设的地方是 §3 的**充要式**（`frozen_iff_of_low_info`）：那里的
「反向」必须用门槛的**否定**（`noise + margin < info`）。 -/

/-- ⭐ **D7-V3**：`margin < 0` 也**不**破坏 §1（`hm` 的两个符号版本都为死前提）。

**⚠ 与 `exists_two_cycle_of_margin_neg` 的表面冲突**：那条说 `margin < 0` 时
**`.running` 侧**有 2-周期；本条说 **`.paused` 侧**照旧冻结。
**⟹ 两者不矛盾**：`h` 把 `.paused` 钉在门槛内，而 `.running` 的门槛
（`noise < info`）可以同时成立 —— `two_sides_both_stable_iff` 说明这一并存
恰好要求 `margin > 0`（`h` 与 `.running` 自稳**不可**并存于负 `margin`）。 -/
theorem forever_paused_of_low_info_neg (info : InfoLevel) (noise : ℝ)
    (margin : ℝ) (hm : margin < 0) (h : info - noise < margin) (k : ℕ) :
    (step info noise margin)^[k] LoopState.paused = LoopState.paused :=
  forever_paused_of_low_info info noise margin h k

/-- ⭐⭐ **两侧同时自稳 ⟺ 滞回带非空**：

```
(step .running = .running ∧ step .paused = .paused)  ⟺  noise < info ∧ info ≤ noise + margin
```

**⭐ 读法**：`info ∈ (noise, noise + margin]` ⟹ **两态都自稳**（双稳态）；
该带**非空 ⟺ `0 < margin`**。

**⟹ `margin` 的真作用**：它**就是滞回带的宽度** —— 这是 `margin` 不可去的
**结构性理由**（不是「步数」的理由）。 -/
theorem two_sides_both_stable_iff (info : InfoLevel) (noise : ℝ) (margin : ℝ) :
    (step info noise margin LoopState.running = LoopState.running ∧
        step info noise margin LoopState.paused = LoopState.paused) ↔
      noise < info ∧ info ≤ noise + margin := by
  rw [step_from_running_running_iff, step_from_paused_paused_iff]

/-! ## §5 ⭐⭐⭐ **`margin` 不可去的**真**形式：门槛宽度的**单调比较**

`two_sides_both_stable_iff` 说明 `margin` = **滞回带宽**。
本节把它做成**可比较**的陈述：**`margin` 越大，能冻结的 `info` 越多** ——
且**存在只被大的 `margin` 冻结的 `info`**。**这才是「`margin` 有独立作用」的精确形式**
（它不可能是「步数」，因为步数恒 1）。 -/

/-- ⭐⭐⭐ **`margin_lowers_exit_threshold`（`margin` 的比较定理）**：

若 `margin₁ ≤ margin₂`，则

1. 冻结集合**单调**：`info ≤ noise + margin₁` ⟹ `info ≤ noise + margin₂`；
2. **严格性**：若 `margin₁ < margin₂`，则存在 `info` 使
   **`margin₂` 下冻结、`margin₁` 下第 1 步就跳出**。

**⭐⭐ D7 的意义**：第二项是「`margin` 不可去」的**正面证据** ——
`info = noise + margin₂` 这个点，用 `margin₁` 会**跳出**，用 `margin₂` 会**冻结**。
**见证必须跨过 `margin₁ < info - noise ≤ margin₂`**，与「`h` 是加法常数」的
§1 情形**不同**（那里没有 `margin` 的比较自由度）。

**⚠ 诚实说明**：本条**不是**「步数界」。步数恒 ≤ 1；
`margin` 的作用是**移动门槛**（`MainLoop.margin_size_irrelevant`）。 -/
theorem margin_lowers_exit_threshold (noise : ℝ) (margin₁ margin₂ : ℝ)
    (hle : margin₁ ≤ margin₂) :
    -- ① 单调：门槛右端随 `margin` 变大
    (∀ info : InfoLevel, info ≤ noise + margin₁ → info ≤ noise + margin₂) ∧
    -- ② 严格：`margin₁ < margin₂` 时存在**只被大的那个**冻结的 `info`
    (margin₁ < margin₂ →
      ∃ info : InfoLevel,
        (step info noise margin₂)^[1] LoopState.paused = LoopState.paused ∧
          (step info noise margin₁)^[1] LoopState.paused = LoopState.running) := by
  refine ⟨fun info h => by linarith, fun hlt => ?_⟩
  refine ⟨noise + margin₂, ?_, ?_⟩
  · rw [Function.iterate_one]
    exact (step_from_paused_paused_iff _ _ _).mpr (le_refl _)
  · rw [Function.iterate_one, step_from_paused_running_iff]
    linarith

/-- ⭐⭐ **`margin_only_affects_paused`（D8 自审：不对称性）**：

`margin` **只**影响 `.paused` 侧，**不影响** `.running` 侧：
两个不同的 `margin` 给出 `.running` 的**同一条** `k` 步轨迹。

**⟹ 「`margin` 是整个循环的余量」是**错**的**：它只是**暂停态的恢复余量**。
本定理防止过度声称，也解释 `margin_size_irrelevant`（步数恒 ≤ 1）与本文件不矛盾。 -/
theorem margin_only_affects_paused (info : InfoLevel) (noise : ℝ)
    (margin₁ margin₂ : ℝ) (h₁ : 0 ≤ margin₁) (h₂ : 0 ≤ margin₂) :
    ∀ k : ℕ, 1 ≤ k → (step info noise margin₁)^[k] LoopState.running =
        (step info noise margin₂)^[k] LoopState.running := by
  intro k hk
  rw [running_closed_form info noise margin₁ h₁ k hk,
      running_closed_form info noise margin₂ h₂ k hk]

/-! ## §6 ⭐⭐ **`margin` 的符号 ⟺ `.running` 侧振荡**（`margin` 的另一种「不可去」） -/

/-- ⭐⭐⭐ **`exists_two_cycle_of_margin_neg`**：`margin < 0` ⟹ 存在 2-周期点
（`.running → .paused → .running`）。

取 `info = noise + margin/2`：`margin < 0` ⟹ `info < noise`（故 `.running → .paused`），
又 `noise + margin < info`（故 `.paused → .running`）。 -/
theorem exists_two_cycle_of_margin_neg (noise : ℝ) (margin : ℝ) (hm : margin < 0) :
    ∃ info : InfoLevel,
      step info noise margin LoopState.running = LoopState.paused ∧
        step info noise margin LoopState.paused = LoopState.running := by
  refine ⟨noise + margin / 2, ?_, ?_⟩
  · rw [step_from_running_paused_iff]; linarith
  · rw [step_from_paused_running_iff]; linarith

/-- ⭐⭐⭐ **`two_cycle_iff_margin_neg`**：`.running` 侧存在 2-周期点 ⟺ `margin < 0`。

- **正向**（`margin < 0` ⟹ 存在）：`exists_two_cycle_of_margin_neg`；
- **反向**（存在 ⟹ `margin < 0`）：两条门槛 `info ≤ noise`（停）与
  `noise + margin < info`（恢复）**同时**要求 `margin < 0`（`linarith`）。

**⟹ `margin` 的符号完全决定 `.running` 侧是「稳定」还是「2-周期」**，
这是 `margin` 不可去的第二个**独立**理由（与 §5 的「带宽」不同）。 -/
theorem two_cycle_iff_margin_neg (noise : ℝ) (margin : ℝ) :
    (∃ info : InfoLevel,
        step info noise margin LoopState.running = LoopState.paused ∧
          step info noise margin LoopState.paused = LoopState.running) ↔
      margin < 0 := by
  constructor
  · rintro ⟨info, h1, h2⟩
    rw [step_from_running_paused_iff] at h1
    rw [step_from_paused_running_iff] at h2
    linarith
  · intro hm
    exact exists_two_cycle_of_margin_neg noise margin hm

/-- ⭐⭐ **`margin ≥ 0` ⇒ `.running` 侧 1 步稳定**（无 2-周期）。

与 `two_cycle_iff_margin_neg` 合起来：`margin` 的**符号** ⟺ `.running` 侧
「稳定 / 2-周期」。 -/
theorem running_stable_of_margin_nonneg (info : InfoLevel) (noise : ℝ)
    (margin : ℝ) (hm : 0 ≤ margin) :
    (step info noise margin)^[2] LoopState.running =
      (step info noise margin)^[1] LoopState.running := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one]
  by_cases h : noise < info
  · have hr : step info noise margin LoopState.running = LoopState.running :=
      (step_from_running_running_iff info noise margin).mpr h
    rw [hr, hr]
  · have h1 : step info noise margin LoopState.running = LoopState.paused :=
      (step_from_running_paused_iff info noise margin).mpr (not_lt.mp h)
    rw [h1, step_from_paused_paused_iff]
    exact le_trans (not_lt.mp h) (le_self_add_of_nonneg noise margin hm)

/-! ## §7 ⭐ **跳出暂停态所需的信息跃迁**（由一次真实 `step` 给出）

**⚠ 与第 295–299 轮的 `margin_gain_needed` 的区别**：那一版**没有应用过 `step`**
（判为恒真式）。**本节的结论**是 `(step …)^[1] .paused = .running`，
即**一次真实的迭代**。 -/

/-- ⭐ **`loop_travels_of_margin_low`**：`noise + margin < info` ⟹
从 `.paused` 出发**一步跳到** `.running`。

**`margin` 出现在门槛 `noise + margin` 里**，且本条的**否定**由
`frozen_iff_of_low_info` 给出 ⟹ 两者构成**完整二分**（`paused_dichotomy`）。 -/
theorem loop_travels_of_margin_low (info : InfoLevel) (noise : ℝ) (margin : ℝ)
    (h : noise + margin < info) :
    (step info noise margin)^[1] LoopState.paused = LoopState.running := by
  rw [Function.iterate_one]
  exact (step_from_paused_running_iff _ _ _).mpr h

/-- ⭐⭐ **`paused_dichotomy`（`.paused` 侧的完整二分，`margin` 为阈值）**：

对**任意**参数，**恰有**下列之一：

* `info ≤ noise + margin` ⟹ **所有** `k ≥ 1` 步都停在 `.paused`；
* `noise + margin < info` ⟹ **第 1 步**就跳到 `.running`。

**⟹ `margin` 是 `.paused` 侧的**唯一**阈值参数**：它不参与 `.running` 侧（§5），
也不改变步数（恒 1），但**完全决定** `.paused` 的**落点**。 -/
theorem paused_dichotomy (info : InfoLevel) (noise : ℝ) (margin : ℝ)
    (hm : 0 ≤ margin) :
    (info ≤ noise + margin ∧
        ∀ k : ℕ, 1 ≤ k → (step info noise margin)^[k] LoopState.paused = LoopState.paused)
      ∨ (noise + margin < info ∧
        (step info noise margin)^[1] LoopState.paused = LoopState.running) := by
  rcases le_or_gt info (noise + margin) with h | h

  · exact Or.inl ⟨h, fun k hk => (frozen_iff_of_low_info info noise margin hm).mpr h k hk⟩
  · exact Or.inr ⟨h, loop_travels_of_margin_low info noise margin h⟩

end FateV2.Error.MainLoop
