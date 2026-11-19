import FateWorld.FateV2.Rules.Completeness
/-!
  # Error · LoopBound

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LoopBound.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Completeness
  - 补充 open 域：FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §34  ⭐⭐ **从存在性到定量**：循环的**单调性与严格性**

  **动机**（依作者裁决 R「不设上限加强」）：
  已有的 `Completeness.loop_stabilizes` 只给出**存在性**：
  $$\exists N,\ (\mathrm{oneRound})^N B = (\mathrm{oneRound})^{N+1} B$$

  ## 本节的目标

  **把结构性质拆成可复用的**定量组件**** ——
  这些组件是「稳定步数有界」的直接依据。

  ## ⭐ 已证的三条

  | 定理 | 内容 |
  |---|---|
  | ⭐ **`iterate_subset_succ`** | **每一轮都扩张**（$\subseteq$）|
  | ⭐⭐ **`ncard_lt_of_not_stable`** | ⭐ **非稳定 ⟹ 基数严格增加** |
  | ⭐ **`ncard_mono_iterate`** | 迭代基数单调不减 |

  ## ⭐⭐ 核心（`ncard_lt_of_not_stable`）

  **若一轮不稳定，则基数严格增加** ——
  **这是「每一步都消耗基数」的精确形式。**

  **⟹ 由此可直接推出**「稳定步数 $\le |M| - |B|$」**
  （见 `stabilize_step_bound`）。

  **⚠ 无硬编码**（依作者裁决 Q-1）：界**由基数算出**，非任选常数。

  ## ⚠⚠⚠ 第 277 轮 D7 审核结论（**降级声明**）

  **本节标题所说的「从存在性到定量」不成立。**
  经 `_d7/D7s_loopbound.lean` 与 `_d7/D7s2_loopbound_split.lean` 实测：

  | 事实 | 探针 | 结论 |
  |---|---|---|
  | `round` **幂等**（`= closureOp`，`closureOp_idem`）| D7-A1/A2 | 迭代**从第 1 步起恒定** |
  | ⚠ **「稳定」对任意 `N ≥ 1` 成立** | D7-B / `part2_stable_any_N` | **`stabilize_step_bound` 的等式部分与 `N` 无关** |
  | 「稳定」**不需要** `[K.FiniteAttrs]` | D7-C / `part2_stable_any_N` | `FiniteAttrs` 在等式部分**是死前提** |
  | 「界 `N + \|B\| ≤ \|M\|`」**不含循环** | D7-D / `part1_card_bound` | 纯集合基数性质 |
  | 「每步消耗基数」图景**假** | D7-E | `round^[2]` 与 `round^[3]` 基数**相等** |
  | `Completeness.loop_stabilizes_within_one` **已覆盖** | D7-F | `N = 1` 且无 `FiniteAttrs` |

  **⟹ `stabilize_step_bound` 的诚实内容** =
  「幂等性（②，平凡）+ 集合基数（①，与循环无关）」的**拼装**，
  **不是**「稳定所需步数的定量界」。

  **⚠ 正确的定量陈述是 `N ≤ 1`**（见 `Completeness.loop_stabilizes_within_one`，
  该定理**无需** `FiniteAttrs`）；
  本节的原定理因断言「`∃ N` 且**附带**基数不等式」而在**最强陈述**意义上是弱的：
  它把「平凡幂等」与「无关的基数界」捆在一起，看起来像有内容。

  **⚠ `ncard_lt_of_not_stable` 正确但只在 `n = 0` 时有意义** ——
  `round` 只「消耗」一次基数，之后不动（D7-E）。

  ## ⚠⚠⚠ 第 291 轮追加判决（**缺口 7 的最终状态**）

  **⚠ 本节 6 条定理中**没有一条**含 `margin` / `info` / `noise`** ——
  「主循环」的语义在 `Fate/MainLoop.lean`，本节与之**类型上无关**。

  **⭐⭐ 第 291 轮在 `MainLoop` 侧给出了 `margin` 的**真实收敛判决**
  （`FateV2.Error.MainLoop` §6）：**

  | 定理 | 内容 |
  |---|---|
  | `stable_within_one_of_margin_nonneg` | `0 ≤ margin` ⟹ `step` **1 步即稳定**（任意 `info/noise`）|
  | `stable_from_one` | `N ≥ 1` ⟹ `step^[N] = step^[1]` |
  | `hm_needed` | 去掉 `0 ≤ margin` 命题即假（`margin=-1` 的 2-周期见证）|
  | `neg_margin_never_stable` | `margin < 0` ⟹ **任意 `N` 都不稳定**（永 2-周期）|
  | `not_needs_two_steps` | ⚠ **任务原命题「`0<margin` ⟹ 至少 `k≥2` 步」为假** |

  **⟹ 缺口 7 的真实可证结论**：
  「稳定步数 = **1**（`margin ≥ 0`）或 **∞**（`margin < 0`）」——
  即 `margin` 的**符号决定是否收敛**，其**大小不影响步数**。
  **任何「`margin` 越大步数越多」的陈述都是假的。**
  =========================================================================== -/

namespace FateV2.Error

open FateV2.Rules
namespace LoopBound

open FateV2.Rules.FormalCtx

universe u v

variable (K : FormalCtx.{u, v})

/-- **一轮循环**（显式函数形式）。 -/
def round (B : Set K.MFCA) : Set K.MFCA := K.polarUp (K.polarDown B)

/-! ### §34.1 ⭐ 迭代的单调性 -/

/-- ⭐ **迭代单调（$\subseteq$）**：每一轮都扩张。

**⟹ 这是「信息只增不减」的精确形式。** -/
theorem iterate_subset_succ (B : Set K.MFCA) :
    ∀ n : ℕ, ((round K)^[n] B) ⊆ ((round K)^[n + 1] B) := by
  intro n
  induction n with
  | zero => exact K.subset_closureOp B
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact K.closureOp_mono ih

/-- ⭐ **一轮使基数不减**。 -/
theorem ncard_mono_oneRound [K.FiniteAttrs] (B : Set K.MFCA) :
    B.ncard ≤ (round K B).ncard :=
  Set.ncard_le_ncard (K.subset_closureOp B) (FiniteAttrs.finite_set (K := K) _)

/-- ⭐ **迭代使基数单调不减**。 -/
theorem ncard_mono_iterate [K.FiniteAttrs] (B : Set K.MFCA) :
    ∀ n : ℕ, ((round K)^[n] B).ncard ≤ ((round K)^[n + 1] B).ncard :=
  fun n => Set.ncard_le_ncard (iterate_subset_succ K B n) (FiniteAttrs.finite_set (K := K) _)

/-! ### §34.2 ⭐⭐ 严格递增（非稳定时） -/

/-- ⭐⭐ **非稳定 ⟹ 基数严格增加**。

⚠ **【第 277 轮降级】** 定理正确，但**不能**读作「每一步都消耗基数」：
`round = closureOp` **幂等**，故「非稳定」**只可能发生在 `round` 的第一轮**
（`_d7/D7s_loopbound.lean` 的 `ncard_nonincreasing_from_two`：
`round^[2] B` 与 `round^[3] B` 的基数**相等**）。
**⟹ 它只能被用一次，不能用于「链式」界步数。** -/
theorem ncard_lt_of_not_stable [K.FiniteAttrs] (B : Set K.MFCA)
    (h : round K B ≠ B) :
    B.ncard < (round K B).ncard :=
  Set.ncard_lt_ncard
    ((Set.ssubset_iff_subset_ne).2 ⟨K.subset_closureOp B, fun heq => h heq.symm⟩)
    (FiniteAttrs.finite_set (K := K) _)

/-- ⭐⭐ **迭代版：非稳定 ⟹ 基数严格增加**。

⚠ **【第 277 轮降级】** 同 `ncard_lt_of_not_stable`：
该「严格增加」对 `n ≥ 1` **恒不可能发生**（迭代恒定）。
它对 `n = 0` 正确且有用，但不足以支撑循环论证。 -/
theorem ncard_lt_iterate_of_not_stable [K.FiniteAttrs] (B : Set K.MFCA) (n : ℕ)
    (h : ((round K)^[n] B) ≠ ((round K)^[n + 1] B)) :
    ((round K)^[n] B).ncard < ((round K)^[n + 1] B).ncard :=
  Set.ncard_lt_ncard
    ((Set.ssubset_iff_subset_ne).2 ⟨iterate_subset_succ K B n, h⟩)
    (FiniteAttrs.finite_set (K := K) _)

/-! ### §34.3 ⭐⭐ 定量结论：稳定步数的界 -/

/-- ⚠⚠ **【第 277 轮降级】原标注为「核心定量结论」，实为平凡拼装。**

**D7 实测（`_d7/D7s_loopbound.lean` + `_d7/D7s2_loopbound_split.lean`）**：

- 结论的**等式部分**（`round^[N] B = round^[N+1] B`）**对任意 `N ≥ 1` 成立**
  （因 `round = closureOp` 幂等），且**不需要** `[K.FiniteAttrs]`；
- 结论的**界部分**（`N + B.ncard ≤ |univ|`）是**纯集合基数**性质，
  证明中 `round` / `Function.iterate` **一次都没出现**；
- 若能取 `N = 1`，则「定量」= 「`N ≤ 1`」，而该陈述已在
  `FateV2.Export.loop_stabilizes_within_one` 中**无条件**给出。

**⟹ 本定理不是「存在性 → 定量」的进步，而是「幂等性 + 集合论」的拼装。**
**⚠ 不应以它作为「稳定步数有界」的证据。**

以下保留原始陈述与证明（证明本身正确，可编译）。

（原始陈述）
$\exists N,\quad N + |B| \le |M| \ \wedge\
  (\mathrm{round})^N B = (\mathrm{round})^{N+1} B$

**⚠ 与 `loop_stabilizes` 的差别的真实情况**：
少者说「存在 $N$」；本定理额外附带 $N + |B| \le |M|$ ——
**但该附带项与「稳定」无关（见上方 D7 判决），故不是加强。**

（原证明思路，已不成立）由 `ncard_lt_iterate_of_not_stable`
声称「每一步（若未稳定）使基数严格增加」——
**⚠ 该图景只在第一步成立**（`round` 幂等），见 D7-E。 -/
theorem stabilize_step_bound [K.FiniteAttrs] (B : Set K.MFCA) :
    ∃ N, N + B.ncard ≤ (Set.univ : Set K.MFCA).ncard ∧
      ((round K)^[N] B) = ((round K)^[N + 1] B) := by
  classical
  -- 稳定步数存在（同 `loop_stabilizes` 的论证）
  have hex : ∃ N, ((round K)^[N] B) = ((round K)^[N + 1] B) := by
    by_contra h
    push Not at h
    have hlt : ∀ n, ((round K)^[n] B).ncard < ((round K)^[n + 1] B).ncard :=
      fun n => ncard_lt_iterate_of_not_stable K B n (h n)
    have hchain : ∀ n, B.ncard + n ≤ ((round K)^[n] B).ncard := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have hk := hlt k
        rw [Function.iterate_succ_apply'] at hk
        rw [Function.iterate_succ_apply']
        omega
    have h1 := hchain ((Set.univ : Set K.MFCA).ncard + 1)
    have hfin : ((round K)^[(Set.univ : Set K.MFCA).ncard + 1] B).ncard ≤
        (Set.univ : Set K.MFCA).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (FiniteAttrs.finite (K := K))
    omega
  -- 取最小稳定步
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  by_contra hbad
  push Not at hbad
  -- 所有 `k < Nat.find hex` 都不稳定
  have hnotstab : ∀ k < Nat.find hex, ((round K)^[k] B) ≠ ((round K)^[k + 1] B) :=
    fun k hk => Nat.find_min hex hk
  have hlt : ∀ k < Nat.find hex, ((round K)^[k] B).ncard < ((round K)^[k + 1] B).ncard :=
    fun k hk => ncard_lt_iterate_of_not_stable K B k (hnotstab k hk)
  have hchain : ∀ k ≤ Nat.find hex, B.ncard + k ≤ ((round K)^[k] B).ncard := by
    intro k hk
    induction k with
    | zero => simp
    | succ j ih =>
      have hj : j < Nat.find hex := by omega
      have ih' := ih (by omega)
      have hstep := hlt j hj
      rw [Function.iterate_succ_apply'] at hstep
      rw [Function.iterate_succ_apply']
      omega
  have hfin : ((round K)^[Nat.find hex] B).ncard ≤ (Set.univ : Set K.MFCA).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _) (FiniteAttrs.finite (K := K))
  have hbig := hchain (Nat.find hex) le_rfl
  omega

end LoopBound

end FateV2.Error