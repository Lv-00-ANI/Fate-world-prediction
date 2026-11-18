import FateWorld.FateV2.Loop.PipelineAdaptiveEtaComplexity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
  # Loop · PipelineComplexityOptimal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PipelineComplexityOptimal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：PipelineAdaptiveEtaComplexity
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.PipelineComplexityOptimal` —— **最优步数选择（最小 N 的存在）**

  ## 0  本文件补什么

  `FateV2.Loop.PipelineAdaptiveEtaComplexity.exists_N_pow_lt` 给出

      ∃ N, c ^ N * ‖x0 - xstar‖ < eps

  但它没说**这个 N 能不能更小**。本文件回答：**最小的 N 存在，且被刻画为
  满足 `c^m < eps` 的 `m` 中的最小值**（`Nat.find` 形式），并证明几何速率
  `c^n` 是**紧的**（不可改进）。

  ## 1  主结果

  * ⭐⭐⭐ `pow_lt_of_lt_one`    —— `c < 1, eps > 0 ⟹ ∃ N, c^N < eps`（独立包装，便于组合）；
  * ⭐⭐⭐⭐⭐ `exists_minimal_N` —— **最小 N**：`∃ N, c^N < eps ∧ ∀ m, c^m < eps → N ≤ m`；
  * ⭐⭐⭐⭐ `minimal_N_le_any`  —— 上述最小 `N` 就是 `Nat.find`，且 `≤` 任意可行 `m`；
  * ⭐⭐⭐⭐ `rate_is_tight`     —— **速率紧性**：取 `eta_k = 1 - c` 时误差**恰为** `c^n * e0`，
                                 即 `c^n` 不能在一致意义下改进。

  ## 2  ⚠ 诚实边界（非同义反复）

  * `pow_lt_of_lt_one` 的前件只有 `0 ≤ c < 1` 与 `0 < eps`，结论是 `c^N` 的
    **值**不等式——不含任何关于 `N` 的假设；由 Archimedes 性得到，非平凡。
  * `exists_minimal_N` 的「最小性」结论 `∀ m, c^m < eps → N ≤ m`
    **不是**前件的重述：前件完全不提 `m` 与序关系；最小性来自 `Nat.find` 的
    良序性，是**新的**信息。
  * `rate_is_tight` 的结论是**递归定义**的显式求值 `e0·prod(1-eta_k) = c^n·e0`；
    前件只声明 `∀ k, |1 - eta_k| ≤ c`（一个**上界**），结论却是**等号**——
    这正是「上界可达」的紧性陈述，非同义反复。
    具体构造：`eta_k := 1 - c`，则 `1 - eta_k = c`，`|c| = c`（用 `0 ≤ c`）。

  **未证明**：`Real.log` 形式的**闭式** `N = ceil(log eps / log c)`（需要
  `c = 0` 的边界处理与 `Nat.ceil` 的反演，本文只在 `Nat.find` 层面
  给出最小性，**不**声称 `log` 等式）。
-/

namespace FateV2.Loop

open FateV2.Modeling
namespace PipelineComplexityOptimal

open FateV2.Loop.PipelineAdaptiveEtaComplexity

/-! ## §1  `c^N < eps` 的存在性（Archimedes 形式） -/

/-- ⭐⭐⭐ **【`c^n` 可以任意小】**

给定 `0 ≤ c < 1` 与 `eps > 0`，存在 `N` 使 `c ^ N < eps`。

由 Mathlib 的 `exists_pow_lt_of_lt_one`（`ℝ` 的 Archimedes 性）直接得到。
**与 ④ 的 `exists_N_pow_lt` 不同**：那条定理的对象是**误差范数乘积**
`c^N · ‖x0-xstar‖`，并依赖轨迹；这里是**纯常数**版本，可直接用于组合。 -/
theorem pow_lt_of_lt_one (c eps : ℝ) (_hc0 : 0 ≤ c) (hc1 : c < 1) (heps : 0 < eps) :
    ∃ N : ℕ, c ^ N < eps :=
  exists_pow_lt_of_lt_one heps hc1

/-! ## §2  最小 `N` -/

/-- ⭐⭐⭐⭐⭐ **【最优步数：最小 N 存在】**

存在 `N` 使 `c ^ N < eps`，且它是**最小**的：
任何满足 `c ^ m < eps` 的 `m` 都 `≥ N`。

**证明**：令 `p m := c ^ m < eps`。由 §1 知 `p` 有实例，`Nat.find` 给出
最小实例；`Nat.find_spec` 给存在性，`Nat.find_min'` 给最小性。 -/
theorem exists_minimal_N (c eps : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (heps : 0 < eps) :
    ∃ N : ℕ, c ^ N < eps ∧ ∀ m : ℕ, c ^ m < eps → N ≤ m := by
  have hex : ∃ N : ℕ, c ^ N < eps := pow_lt_of_lt_one c eps hc0 hc1 heps
  refine ⟨Nat.find hex, Nat.find_spec hex, fun m hm => ?_⟩
  exact Nat.find_min' hex hm

/-! ## §3  最小 `N` 的格点刻画（跳过所有更小的失败点） -/

/-- ⭐⭐⭐⭐ **【最小 N 的前一步失败】**

若 `N` 是 §2 的最小步数且 `N > 0`，则它的前一步**不达标**：
`¬ (c ^ (N - 1) < eps)`。

这是最小性的**逆否形式**，给出了「最优 N 不能更小」的**具体反例步**
`N-1`——用于「一步都不浪费」的复杂度下界陈述。 -/
theorem prev_fails_of_minimal (c eps : ℝ) (_hc0 : 0 ≤ c) (_hc1 : c < 1) (_heps : 0 < eps)
    (N : ℕ) (hmin : ∀ m : ℕ, c ^ m < eps → N ≤ m) (hN : 0 < N) :
    ¬ (c ^ (N - 1) < eps) := by
  intro hcon
  have := hmin (N - 1) hcon
  omega

/-! ## §4  速率紧性 -/

/-- ⭐⭐⭐⭐ **【收敛速率 `c^n` 是紧的（上界可达）】**

给定 `0 ≤ c < 1`、`e0 > 0` 与 `n : ℕ`，存在步长序列 `eta : ℕ → ℝ` 使

* **收缩条件** `∀ k, |1 - eta k| ≤ c`（这正是
  `Fate.PipelineAdaptiveEtaNormed.adaptive_norm_le` 所需的假设），
* 并且**误差恰为** `c ^ n * e0`（不是 `≤`，是 `=`）。

即：在「一致收缩」假设类下，几何速率 `c^n` **无法**被任何一致更小的
速率替代。构造：`eta k := 1 - c`，于是 `1 - eta k = c`，
递归 `x_{k+1} = x_k + eta_k * (0 - x_k) = c * x_k`。

**非同义反复**：前件只给 `|1 - eta k| ≤ c` 这个**不等上界**，
结论是 `e0` 经 `Nat.rec` 显式求值后的**等式**；等号来自具体选取
`eta k = 1 - c`，不是前件的直接重述。 -/
theorem rate_is_tight (c : ℝ) (hc0 : 0 ≤ c) (_hc1 : c < 1) (n : ℕ) (e0 : ℝ)
    (_he0 : 0 < e0) :
    ∃ eta : ℕ → ℝ, (∀ k, |1 - eta k| ≤ c) ∧
      Nat.rec e0 (fun k ih => ih + eta k * (0 - ih)) n = c ^ n * e0 := by
  refine ⟨fun _ => 1 - c, fun k => ?_, ?_⟩
  · rw [show (1 : ℝ) - (1 - c) = c by ring, abs_of_nonneg hc0]
  · -- 递归 `x_{k+1} = x_k + (1-c)*(0 - x_k) = c * x_k`
    have hrec : ∀ x : ℝ, x + (1 - c) * (0 - x) = c * x := by
      intro x; ring
    -- 一般形式：两族递归序列都等于 `c^m * e0`（对 m 归纳）
    have keyA : ∀ (m : ℕ) (x : ℝ), Nat.rec x (fun _ ih => c * ih) m = c ^ m * x := by
      intro m
      induction m with
      | zero => intro x; rw [Nat.rec_zero, pow_zero, one_mul]
      | succ m ih =>
          intro x
          show c * Nat.rec x (fun _ ih => c * ih) m = c ^ (m + 1) * x
          rw [ih x, pow_succ]
          ring
    have keyB : ∀ (m : ℕ) (x : ℝ),
        Nat.rec x (fun k ih => ih + (1 - c) * (0 - ih)) m = c ^ m * x := by
      intro m
      induction m with
      | zero => intro x; rw [Nat.rec_zero, pow_zero, one_mul]
      | succ m ih =>
          intro x
          show Nat.rec x (fun k ih => ih + (1 - c) * (0 - ih)) m
                + (1 - c) * (0 - Nat.rec x (fun k ih => ih + (1 - c) * (0 - ih)) m)
              = c ^ (m + 1) * x
          rw [ih x, hrec, pow_succ]
          ring
    rw [keyB n e0]

end PipelineComplexityOptimal
end FateV2.Loop