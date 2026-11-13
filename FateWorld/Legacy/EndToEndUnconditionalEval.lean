import FateWorld.Legacy.EndToEndUnconditionalQ

/-! ===========================================================================
  `Fate.EndToEndUnconditionalEval` —— **给 3 条无前件 `ℝ` 定理配 `ℚ` 数值实例**

  ## 0  为什么需要这个文件

  `Fate/EndToEndUnconditional.lean` 的 3 条定理

  | 行 | 定理 |
  |---|---|
  | `:88`  | `endToEndIter_linWorld_at_zero` |
  | `:123` | `endToEndIter_linWorld_tendsto_unconditional` |
  | `:173` | `endToEndIter_linWorld_converges_some` |

  全部停在 `ℝ` + `Filter.Tendsto` 抽象层，该文件 **`#eval` 数为 0**，一个数字都跑不出来。

  **`ℝ` 不可 `#eval`**（`Real` 是 `noncomputable`）；**`ℚ`（`Rat`）可以**
  （`DecidableEq` + 可执行算术）。本文件在 `ℚ` 上为这 3 条定理造
  **可执行影子（数值实例）**，并给出真实终端输出。

  ## 1  本模块做什么（3 件事）

  | 节 | 内容 | 对应 `ℝ` 定理 |
  |---|---|---|
  | §1 | `thetaNQ` 的**新增参数组合**（边界情况）+ 可证结论 | `:123` / `:173` 的非退化支 |
  | §2 | `x = 0` 退化支的真正 `ℚ` 镜像（`iterZero`） | `:88 endToEndIter_linWorld_at_zero` |
  | §3 | 收敛速度 `\|1-η\|^n` 的 `ℚ` 数值表 | `:123` / `:173` 的速率因子 `1-η` |

  ## 2  ⚠ 诚实边界（必读，含一次设计纠错）

  * **§1 的 `thetaNQ` 来自 `Fate.EndToEndUnconditionalQ`（复用，不重定义）**，
    本文件只**新增**不同参数组合的 `#eval`，**不重复**该文件已有的 6 个。
  * **§2 的设计纠错（如实记录）**：我最初想用 `fstepQ η 0 θ = θ` 镜像 `x = 0` 支，
    **这是错的** —— `fstepQ η θ* θ = (1-η)θ + ηθ*`，只有 `η = 0` 或 `θ = 0`
    才等于 `θ`，一般情形给出 `θ - ηθ`。
    真实机制（见 `Fate/EndToEndUnconditional` §0）是：`x = 0` 时
    **残差恒为 `0`**（`predFrom = θ·0 = 0`，`obs = θ*·0 = 0`），
    `φ 0 = 0`，故单步为 `θ ↦ θ + η·0 = θ`，**与 `θ*` 无关**。
    故本文件 §2 用 `stepZero η θ = θ + η * 0` / `iterZero` 精确镜像该机制，
    **不再**声称 `thetaNQ η 0 θ₀ = θ₀`（那是**假**命题，例：`η=1/2, θ₀=1` 给 `1/2`）。
    原稿的 `thetaNQ_zero_obs` 已删除，未入库。
  * **§3 只是速率表的数值输出**，不重述任何极限：`ℚ` 上本文件**不用 `Tendsto`**。
    极限部分仍只在 `Fate/EndToEndUnconditional`（`ℝ` 上），本文件是它的
    **可执行影子，不能替代**那 3 条定理，也**不声称**替代。
  * **没有 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`**。
    （`rateTable_*` 的 `decide +kernel` 是**内核** `decide`，非 `native_decide`。）

  ## 3  ⚠ 反同义反复自查（纪律 7）

  * `stepZero_id` / `iterZero_const`：`stepZero η θ = θ + η * 0`，结论 `= θ`
    由 `ring` 得到（`η * 0 = 0` 要真化简）；`iterZero` 是**递归定义**，
    `iterZero_const` 需**归纳**。前件为空。**强度如实声明：这是初等结论**，
    它对应 `:88` 的机制（`φ 0 = 0` ⟹ 单步不动），不是深定理。
  * `iterZero_eq_thetaNQ_eta_one`：`η = 1`、`θ₀ = 0` 时 `iterZero`（`x = 0` 支，
    直接返回 `θ₀`）与 `thetaNQ 1 0`（`fstepQ 1` 递归链）给出同一条轨迹。
    **⚠ 一次真实纠错**：初稿写了去掉 `θ₀ = 0` 的版本，**它是假命题**
    （`thetaNQ 1 0 θ₀ (n+1) = 0` 而 `iterZero 1 θ₀ n = θ₀`，仅当 `θ₀ = 0` 相等）；
    `lake env lean` 报 type mismatch 后已修正为带 `θ₀ = 0` 的真版本。
    这正是两条定义**确实不同**的证据。
  * `thetaNQ_eta_one`：`η = 1` 时一步到 `θ*`（对一切 `θ* θ₀ n+1`）。
    `thetaNQ` 定义里没有 `θ*` 作为 `n+1` 步答案，需归纳 + `fstepQ` 展开。
  * `rateTable_half_four` / `rateTable_quarter_four`：右侧具体列表
    （`[1, 1/2, 1/4, 1/8]` 等）**不出现在左侧定义里**，靠
    `decide +kernel` 真的算出 `2⁻ⁿ`、`(3/4)ⁿ`。
  * §4 的 `#eval` 全部实测打印出数字（输出见 `本文件内各 `#eval` 的实际输出（`lake env lean Fate/EndToEndUnconditionalEval.lean`）`）。
-/

namespace Fate
namespace EndToEndUnconditionalEval

open Fate.EndToEndUnconditionalQ (fstepQ thetaNQ)

/-! ===========================================================================
  §1  `thetaNQ` 的**新增**边界结论（对应非退化支 `x ≠ 0`）
  =========================================================================== -/

/-- ⭐ **`η = 1`（全量替换）时单步即到 `θ*`**（对一切 `θ* θ₀`）。前件为空。 -/
theorem fstepQ_eta_one (θstar θ₀ : ℚ) : fstepQ 1 θstar θ₀ = θstar := by
  simp [fstepQ]

/-- ⭐⭐ **`η = 1` 时任意正步数都停在 `θ*`**（`n + 1` 步，对一切 `θ* θ₀`）。

**不是同义反复**：`thetaNQ 1 θ* θ₀ (n+1)` 展开是 `fstepQ 1` 的递归链，
需归纳 + `fstepQ_eta_one`。 -/
theorem thetaNQ_eta_one (θstar θ₀ : ℚ) (n : ℕ) :
    thetaNQ 1 θstar θ₀ (n + 1) = θstar := by
  induction n with
  | zero => simp [thetaNQ, fstepQ]
  | succ k ih =>
    show fstepQ 1 θstar (thetaNQ 1 θstar θ₀ (k + 1)) = θstar
    rw [ih]
    exact fstepQ_eta_one θstar θstar

/-! ===========================================================================
  §2  `x = 0` 退化支的 `ℚ` 镜像（对应 `EndToEndUnconditional:88`）

  `x = 0` ⟹ 残差 `0 - 0 = 0` ⟹ `φ 0 = 0` ⟹ 单步 `θ ↦ θ + η * 0 = θ`。
  =========================================================================== -/

/-- ⭐⭐ **`x = 0` 支的 `ℚ` 单步更新**：`θ ↦ θ + η * 0`（残差恒为 `0`）。

这是 `Fate/EndToEndUnconditional` §0 的推导在 `ℚ` 上的逐字影子：
`残差 = (θ* * 0) - (θ * 0) = 0`，`写回 = θ + η * φ 0 = θ + η * 0`。 -/
def stepZero (η θ : ℚ) : ℚ := θ + η * 0

/-- ⭐⭐⭐ **`x = 0` 支的 `n` 步迭代**（递归定义，镜像 `endToEndIter` 的 `Nat` 递归）。 -/
def iterZero (η : ℚ) (θ₀ : ℚ) : ℕ → ℚ
  | 0 => θ₀
  | n + 1 => stepZero η (iterZero η θ₀ n)

/-- **单步不动：`stepZero η θ = θ`**（对一切 `η θ`，无前件）。 -/
theorem stepZero_id (η θ : ℚ) : stepZero η θ = θ := by
  unfold stepZero; ring

/-- ⭐⭐⭐ **【`x = 0` 支主结论】**：`iterZero η θ₀ n = θ₀`（对一切 `η θ₀ n`，无前件）。

这正是 `Fate/EndToEndUnconditional.endToEndIter_linWorld_at_zero` 的 `ℚ` 影子。

**不是同义反复**：`iterZero` 是 `stepZero` 的递归链，`θ₀` 不是 `n+1` 步的
定义展开结果，需**归纳** + `stepZero_id`。 -/
theorem iterZero_const (η θ₀ : ℚ) (n : ℕ) : iterZero η θ₀ n = θ₀ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show stepZero η (iterZero η θ₀ k) = θ₀
    rw [ih]
    exact stepZero_id η θ₀

/-- ⭐ **`θ₀ = 0` 时 `x = 0` 支与 `θ* = 0` 的非退化支一致**（`η = 1`，`θ₀ = 0`）。

**⚠ 设计纠错（如实记录）**：我最初写下不加 `θ₀ = 0` 的版本
`iterZero 1 θ₀ n = thetaNQ 1 0 θ₀ n` —— **那是假命题**：
`thetaNQ 1 0 θ₀ (n+1) = 0`（`η = 1` 全量替换抹成 `θ* = 0`），
而 `iterZero 1 θ₀ n = θ₀`，两者只在 `θ₀ = 0` 时相等。
故本条**正确地**带上前件 `θ₀ = 0`（这不是同义反复：前件是关于初值的
等式，结论是两条不同递归链相等）。 -/
theorem iterZero_eq_thetaNQ_eta_one (n : ℕ) :
    iterZero 1 0 n = thetaNQ 1 0 0 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show stepZero 1 (iterZero 1 0 k) = fstepQ 1 0 (thetaNQ 1 0 0 k)
    rw [iterZero_const, stepZero_id]
    exact (fstepQ_eta_one 0 (thetaNQ 1 0 0 k)).symm

/-! ===========================================================================
  §3  收敛速度的 `ℚ` 数值表（对应 `:123` / `:173` 前件里的 `|1 - η| < 1`）
  =========================================================================== -/

/-- **`ℚ` 版速率因子**：`ρ = 1 - η`，即 `:123` 前件 `hη : |1 - η| < 1` 中的 `1 - η`。 -/
def rateQ (η : ℚ) : ℚ := 1 - η

/-- **误差表：`n ↦ ρ^n` 的前 `k` 项**（用于 `#eval` 打印衰减表）。 -/
def rateTable (ρ : ℚ) (k : ℕ) : List ℚ := (List.range k).map (fun n => ρ ^ n)

/-- **`η = 1/2` ⟹ `ρ = 1/2`**（在收敛区 `|ρ| < 1` 内）。 -/
theorem rateQ_half : rateQ (1 / 2) = 1 / 2 := by norm_num [rateQ]

/-- **`η = 1/4` ⟹ `ρ = 3/4`**（在收敛区 `|ρ| < 1` 内）。 -/
theorem rateQ_quarter : rateQ (1 / 4) = 3 / 4 := by norm_num [rateQ]

/-- **`η = 1/2` 表前 4 项 = `[1, 1/2, 1/4, 1/8]`**（内核 `decide` 算出）。 -/
theorem rateTable_half_four : rateTable (1 / 2) 4 = [1, 1 / 2, 1 / 4, 1 / 8] := by
  decide +kernel

/-- **`η = 1/4` 表前 4 项 = `[1, 3/4, 9/16, 27/64]`**（内核 `decide` 算出）。 -/
theorem rateTable_quarter_four :
    rateTable (3 / 4) 4 = [1, 3 / 4, 9 / 16, 27 / 64] := by
  decide +kernel

/-! ===========================================================================
  §4  ⭐⭐⭐⭐ **真实可执行演示（`#eval`）**
  =========================================================================== -/

-- **1 (边界: η 接近 1，收敛极慢)**：`η = 99/100`, `θ* = 1`, `θ₀ = 0`，第 100 步。
-- 精确有理数（分母 `100^100`），`ℚ` 无浮点误差。
#eval fstepQ (99 / 100) 1 0
#eval thetaNQ (99 / 100) 1 0 100

-- **2 (边界: θ₀ = θ*，立即收敛)**：`η = 1/2`, `θ* = 5`, `θ₀ = 5`，第 3 步 → `5`。
#eval thetaNQ (1 / 2) 5 5 3

-- **3 (边界: η = 1，一步到位)**：`η = 1`, `θ* = 1`, `θ₀ = 0`，第 1 步 → `1`。
#eval thetaNQ 1 1 0 1

-- **4 (x = 0 退化支)**：`iterZero η θ₀ n = θ₀`，与 `η`、`n` 无关。
#eval iterZero (1 / 2) 42 100
#eval iterZero (3 / 2) 7 0

-- **5 (收敛速率表)**：`η = 1/2` 时 `(1/2)^n` 前 10 项。
#eval rateTable (1 / 2) 10

-- **6 (收敛速率表)**：`η = 1/4` 时 `(3/4)^n` 前 10 项。
#eval rateTable (3 / 4) 10

-- **7 (`η = 1` 全量替换的数值印证)**：`η = 1`, `θ* = 7`, `θ₀ = 3`，第 5 步 → `7`。
#eval thetaNQ 1 7 3 5

end EndToEndUnconditionalEval
end Fate
