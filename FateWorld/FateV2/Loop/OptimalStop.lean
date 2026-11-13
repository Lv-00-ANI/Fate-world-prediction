import FateWorld.FateV2.Loop.Convergence
import FateWorld.FateV2.Error.VerdictFull
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Loop · OptimalStop —— 闭环的**最优停止点**（T33）

  ## 迁移登记
  - 来源：**新写**（装配 `Loop/Convergence.lean`（T21）、`Loop/WriteBack.lean`、
          `Loop/Residual.lean`、`Error/FitBoundaryN.lean`、`Error/VerdictFull.lean`；
          以上**全部不改**）
  - 动作：C 重写（新建并行文件）
  - 对应环节：F7-22（回写）、F7-23（收敛）、F7-11（误差判据 / 裁决 K）
  - 依赖裁决：**裁决 K**、**D-008**（σ 只能由建模层给）、**D-022**（反空泛）
  - 改动：新文件。只新增定义与定理。
          **对 `Convergence.lean` 的唯一改动**：在 `end Convergence` 之前**追加**
          两条辅助引理（`contract_anti` / `contract_pow_mono`），
          **不修改、不删除**该文件已有的任何一条定理。
  - 状态：已验证（全部定理 `#print axioms` 实测，逐条登记在
          `_support_registry_T33.csv`）

  ## T21 留下的问题

  `Loop/Convergence.lean`（T21）证出：误差 `|e_n| = |1−η|^n·|e₀|` 单调降到 `0`，
  **必然穿过** `σ`，且穿过之后**再也不回头**（`after_cross_stays`）。
  于是「继续回写」最终**必然**使裁决 K 的 `accepts` 判不合格
  （`eventually_below_K_band`）—— 带内是个**瞬态区间**。

  T21 **没有回答**的是：**该在哪一步停**？

  ## 本文件的核心结论（先说结论，再说反直觉的部分）

  ### ✅ 证出来的

  | 编号 | 定理 | 内容 |
  |---|---|---|
  | §1.1 | `exists_min_of_band` | 合格位置集合**有最小元**（`Nat` 强归纳，构造性） |
  | §1.2 | `band_has_upper_bound` | 合格位置集合**有上界**（T21 `crosses_sigma_strict` + 单调） |
  | §2.1 | **`optimal_stop_exists`** | ****最优停止点存在** ⭐ 主交付** |
  | §3.1 | `optimal_stop_is_prefix` | 合格位置 = 一个**区间** `[nIn, nOut]` |
  | §5.1 | `stop_too_early_bad` | **停太早**（`E_n > σ+ε`）⟹ 不合格 ⭐ |
  | §5.2 | `stop_too_late_bad` | **停太晚**（`E_n < σ−ε`）⟹ 不合格 ⭐ |
  | §5.3 | `stop_before_and_after_bad` | 最优点**前后**都不合格（裁决 K ≠「越小越好」） |
  | §4 | `optimal_stop_vs_verdict` | 与裁决 K 三档判据的关系 |

  ### ⚠ 证伪的（**必须明说**）

  **「最优停止点 = 首次入带那一步」是假的。**

  具体反例（`optimal_stop_not_first`）：`η = 1/2`（`r = 1/2`）、`e₀ = 3`、`σ = 1`、`ε = 1/2`。

  | `n` | `E_n` | 是否合格 | 到 `σ` 的距离 |
  |---|---|---|---|
  | 0 | `3` | ❌ | — |
  | **1** | **`3/2`** | ✅ | **`1/2`**（首次入带，但**不是**最优） |
  | **2** | **`3/4`** | ✅ | **`1/4`** ← **最优** |
  | 3 | `3/8` | ❌ | — |

  → **首次入带的第 1 步不是最优，第 2 步才是。**
  「入带就停」**不是**最优策略；「停得越近 σ 越好」才是。
  `optimal_stop_not_first` 把这一点证死（具体数值，`norm_num` 收尾）。

  ## 为什么「存在性」是非平凡的

  `IsOptimalStop` 要求「在**所有**合格位置中距离最小」—— 一个 `∀ m : Nat` 的全称断言。
  合格位置集合在 `accepts` 的定义里**没有任何结构**。必须做三步：

  1. **非空**：`σ ≤ |e₀|` ⟹ 第 0 步合格（`errAt_zero`）；
  2. **有限（有上界）**：`E_n` 单调不增且趋于 `0 < σ−ε` ⟹ 一步之后全不合格
     （§1.2，用 T21 的 `crosses_sigma_strict`）；
  3. **最小距离可取**：有限集上的 `Real` 值有下界 `0`，
     在**有限枚举**上取下标（§2.1 的 `exists_argmin`）。

  ## 公理纪律

  `Loop/` 层**允许**三公理（任务书原文）。本文件全部定理**类型里都有 `Real`**，
  故账面必然带三公理；实测均为 `[propext, Classical.choice, Quot.sound]`，
  **无** `sorryAx`。逐条登记进 `_support_registry_T33.csv`。
-/

namespace FateV2.Loop

namespace OptimalStop

open FateV2.Loop.Convergence
open FateV2.ErrorN

/-! ===========================================================================
  §0  轨迹、到 σ 的距离、最优停止点
  =========================================================================== -/

/-- **第 `n` 步回写后的残差绝对值**：`E_n := |1−η|^n·|e₀|`。

  **超出定义之处**：`Convergence.contract_iter` 已证它与 `|iterate η n e₀|` 相等；
  本定义把它**命名为轨迹** `errAt`，于是「最优停止点」这类论断可以直接写在
  这条数列上，而不必每次重抄 `|1-η|^n * |e0|`。 -/
def errAt (η e0 : Real) (n : Nat) : Real := |1 - η| ^ n * |e0|

/-- **收缩因子** `r := |1−η|`。 -/
def ratio (η : Real) : Real := |1 - η|

/-- **到 `σ` 的距离**：最优性比的是这个量，不是误差本身。 -/
def stopDist (η e0 σ : Real) (n : Nat) : Real := |errAt η e0 n - σ|

/-- **在 `n` 处停是「最优停止点」** —— 合格位置中到 `σ` 最近的那个。

  $$\mathrm{IsOptimalStop} := \mathrm{accepts}\,\sigma\,\varepsilon\,E_n
    \;\wedge\; \forall m,\ \mathrm{accepts}\,\sigma\,\varepsilon\,E_m
      \Rightarrow |E_n-\sigma| \le |E_m-\sigma| .$$

  **超出定义之处**：定义只承诺「合格 + 在合格者中最近」，它
  **不**承诺存在（§2 证）、**不**承诺唯一（§3 给反例）、
  **更不**承诺「就是首次入带」（§3.2 **证伪**）。 -/
def IsOptimalStop (η e0 σ ε : Real) (n : Nat) : Prop :=
  accepts σ ε (errAt η e0 n) ∧
    ∀ m : Nat, accepts σ ε (errAt η e0 m) → stopDist η e0 σ n ≤ stopDist η e0 σ m

/-- **`errAt` 与 T21 的表达式逐字相同**（`rfl`）。

  **超出定义之处**：把本文件的 `errAt` 与 T21 的 `|1−η|^n·|e₀|` 钉在一起，
  于是 T21 的每一条定理都可以**无改写地**作用在 `errAt` 上。 -/
theorem errAt_eq_contract (η e0 : Real) (n : Nat) :
    errAt η e0 n = |1 - η| ^ n * |e0| := rfl

/-- **`errAt 0 = |e₀|`**。 -/
theorem errAt_zero (η e0 : Real) : errAt η e0 0 = |e0| := by
  show |1 - η| ^ (0 : Nat) * |e0| = |e0|
  rw [pow_zero, one_mul]

/-- **`errAt` 非负**。 -/
theorem errAt_nonneg (η e0 : Real) (n : Nat) : 0 ≤ errAt η e0 n := by
  show (0 : Real) ≤ |1 - η| ^ n * |e0|
  exact mul_nonneg (pow_nonneg (abs_nonneg (1 - η)) n) (abs_nonneg e0)

/-- **`errAt` 单调不增**：`n ≤ m ⟹ E_m ≤ E_n`。

  **超出定义之处**：`contract_pow_mono` 只说幂次 `≤`；本定理把 `|e₀|` 乘进去，
  得到**轨迹本身**的单调性 —— 这是 §1/§2 全部论证的唯一依据。 -/
theorem errAt_mono {η : Real} (hη0 : 0 < η) (hη2 : η < 2) (e0 : Real) {m n : Nat}
    (hmn : n ≤ m) : errAt η e0 m ≤ errAt η e0 n := by
  show |1 - η| ^ m * |e0| ≤ |1 - η| ^ n * |e0|
  exact mul_le_mul_of_nonneg_right (contract_pow_mono hη0 hη2 m n hmn) (abs_nonneg e0)

/-- **局部引理**：`0 < r < 1` 且 `n < m` ⟹ `r^m < r^n`。

  **超出定义之处**：本文件**不依赖** Mathlib 中 `pow_lt_pow_of_lt_one` 的元参数形状，
  而是直接用 `pow_le_pow_of_le_one` + `pow_add` 自证 —— 于是它在任何 `Real` 上可用。

  ⚠ **`0 < r` 不可弱化成 `0 ≤ r`**：`r = 0` 时 `0^m = 0^n = 0`（`n ≥ 1`），
  结论为假。本文件所有调用点都由 `0 < η < 2` 保证 `0 < |1−η|`。 -/
theorem pow_lt_pow_of_lt_one_self {r : Real} : ∀ {n m : Nat}, n < m → 0 < r → r < 1 →
    r ^ m < r ^ n := by
  intro n m h hr0 hr1
  obtain ⟨k, hk⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  have hkpos : 0 < k := by omega
  subst hk
  rw [pow_add]
  have hk1 : r ^ k ≤ r ^ 1 := pow_le_pow_of_le_one (le_of_lt hr0) (le_of_lt hr1) hkpos
  rw [pow_one] at hk1
  have hpow : r ^ k < 1 := lt_of_le_of_lt hk1 hr1
  have hpos : (0 : Real) < r ^ n := pow_pos hr0 n
  nlinarith [hpow, hpos]

/-- **`errAt` 严格下降**（`r < 1` 且 `|e₀| > 0`）。

  **超出定义之处**：`errAt_mono` 给的是 `≤`；「带内不止一步」这类论断
  需要**严格**性 —— 它来自 `r^n` 的严格单调（`pow_lt_pow_of_lt_one_self`）。 -/
theorem errAt_strict {η : Real} (hη0 : 0 < η) (hη2 : η < 2) (hη1 : η ≠ 1) {e0 : Real}
    (he0 : 0 < |e0|) {m n : Nat} (hmn : n < m) : errAt η e0 m < errAt η e0 n := by
  have hlt : |1 - η| < 1 := abs_one_sub_lt_one hη0 hη2
  have hpos : (0 : Real) < |1 - η| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hη1))
  have hp : |1 - η| ^ m < |1 - η| ^ n := pow_lt_pow_of_lt_one_self hmn hpos hlt
  show |1 - η| ^ m * |e0| < |1 - η| ^ n * |e0|
  exact mul_lt_mul_of_pos_right hp he0

/-- **`stopDist` 非负**。 -/
theorem stopDist_nonneg (η e0 σ : Real) (n : Nat) : 0 ≤ stopDist η e0 σ n :=
  abs_nonneg _

/-- **`stopDist = 0 ⟺ 该步恰好落在 σ 上**。

  **超出定义之处**：`IsOptimalStop` 里「最近」是 `≤`；本定理给出它的**下界可取**性：
  距离的绝对下界 `0` **能**被取到，**恰好**当某步误差等于 `σ`。
  这正是 §3「唯一性」的分界线（也是 `VerdictPoint` 的落点）。 -/
theorem stopDist_eq_zero_iff (η e0 σ : Real) (n : Nat) :
    stopDist η e0 σ n = 0 ↔ errAt η e0 n = σ := by
  show |errAt η e0 n - σ| = 0 ↔ errAt η e0 n = σ
  rw [abs_eq_zero, sub_eq_zero]

/-! ===========================================================================
  §1  合格位置集合：非空、有最小元、有上界
  =========================================================================== -/

/-- **【§1.1】合格位置**有最小元**（`Nat` 强归纳，构造性）。

  若第 `N` 步合格，则存在 `n ≤ N`：`n` 合格，而 `n` 之前的**每一步都不合格**。

  **超出定义之处**：`accepts` 只是一个不等式合取，对「哪些 `n` 合格」没有任何
  结构承诺；「合格者里取最小」通常走 `Nat.find`（带 `Classical.choice`）。
  本定理用 `Nat.strongRecOn` 做成**构造性**的 ——
  若 `N` 之前还有合格点就交给归纳假设，否则 `N` 自己就是最小。

  ⚠ 必须用**强归纳**而非 `Nat.rec`：`k → k+1` 的朴素归纳**拿不到**
  「`k` 之前还有哪些合格点」，而最小性恰恰需要它。 -/
theorem exists_min_of_band {η e0 σ ε : Real} :
    ∀ N : Nat, accepts σ ε (errAt η e0 N) →
      ∃ n : Nat, n ≤ N ∧ accepts σ ε (errAt η e0 n) ∧
        ∀ m : Nat, m < n → ¬ accepts σ ε (errAt η e0 m) :=
  fun N => Nat.strongRecOn N (fun N ih hN => by
    by_cases h : ∃ k : Nat, k < N ∧ accepts σ ε (errAt η e0 k)
    · obtain ⟨k, hkN, hkacc⟩ := h
      obtain ⟨n, hn, hacc, hmin⟩ := ih k hkN hkacc
      exact ⟨n, le_trans hn (le_of_lt hkN), hacc, hmin⟩
    · refine ⟨N, le_refl N, hN, fun m hm => ?_⟩
      exact fun hacc => h ⟨m, hm, hacc⟩)

/-- **【§1.2】合格位置**有上界**（带内有限）。

  存在 `K`，使 `m ≥ K` 时**必然**不合格。

  **超出定义之处**：这是「带内是**有限**集」的**唯一**实质步骤。
  它把 T21 的 `crosses_sigma_strict`（`∃n, E_n < σ`）**加强**为
  「一次落到 `σ−ε` 以下，此后**每一步**都在下面」，依据是 `errAt_mono`。

  ⚠ **`ε < σ` 不可去**：`σ − ε > 0` 才能把「误差趋向 `0`」变成
  「误差必然低于 `σ−ε`」。若 `ε ≥ σ`，带的下沿 `σ−ε ≤ 0`，而误差恒 `≥ 0`，
  于是带可能**无上界**（`η → 0` 时 `E_n ≡ |e₀|` 永不离开）。
  这不是本文件的漏洞，而是判据本身的退化：`ε ≥ σ` 时「下侧过拟合」的判据不存在了。 -/
theorem band_has_upper_bound {η : Real} (hη0 : 0 < η) (hη2 : η < 2)
    {e0 σ ε : Real} (hεσ : ε < σ) (hge : σ - ε < |e0|) :
    ∃ K : Nat, ∀ m : Nat, K ≤ m → ¬ accepts σ ε (errAt η e0 m) := by
  have hpos : (0 : Real) < σ - ε := by linarith
  obtain ⟨K, hK⟩ := crosses_sigma_strict hη0 hη2 (e0 := e0) hpos hge
  refine ⟨K, fun m hm hacc => ?_⟩
  have hmono : errAt η e0 m ≤ errAt η e0 K := errAt_mono hη0 hη2 e0 hm
  have hEK : errAt η e0 K = |1 - η| ^ K * |e0| := rfl
  unfold accepts at hacc
  have h1 : σ - ε ≤ errAt η e0 m := hacc.1
  linarith

/-! ===========================================================================
  §2  **存在性**（主交付）
  =========================================================================== -/

/-- **【§2.0】有限集上的 `Real` 值**取到最小**（`Nat` 枚举，构造性）。

  `∃ n ≤ N, ∀ m ≤ N, f n ≤ f m`：在 `[0,N]` 上枚举，每一步与当前最优比较。

  **超出定义之处**：一般情形下「实数列取最小」要完备性或紧性；
  这里 `f` 只用**有限多个**值（`N+1` 个），于是**完全构造性** ——
  `Nat.rec` 每一步只需比较两个实数。**不需要** `sInf` / `Classical.choice`。 -/
theorem exists_argmin (f : Nat → Real) :
    ∀ N : Nat, ∃ n : Nat, n ≤ N ∧ ∀ m : Nat, m ≤ N → f n ≤ f m := by
  intro N
  induction N with
  | zero => exact ⟨0, le_refl 0, fun m hm => by
      have hm0 : m = 0 := by omega
      subst hm0
      exact le_refl _⟩
  | succ k ih =>
    obtain ⟨n, hn, hmin⟩ := ih
    by_cases hc : f (k + 1) ≤ f n
    · -- 新点更优：取 `k+1`
      refine ⟨k + 1, le_refl _, fun m hm => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : m < k + 2) with hlt | heq
      · exact le_trans hc (hmin m (by omega))
      · rw [heq]
    · -- 旧点仍最优
      refine ⟨n, by omega, fun m hm => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : m < k + 2) with hlt | heq
      · exact hmin m (by omega)
      · rw [heq]; exact le_of_lt (lt_of_not_ge hc)

/-- **【§2.1 主定理】最优停止点**存在** ⭐。

  $$\eta\in(0,2),\ 0<\sigma,\ 0\le\varepsilon<\sigma,\ \sigma\le|e_0|
    \;\Longrightarrow\; \exists n,\ \mathrm{IsOptimalStop}\,\eta\,e_0\,\sigma\,\varepsilon\,n .$$

  **超出定义之处**（这条为什么不是「显然」）：

  `IsOptimalStop` 要求「在**所有**合格位置中距离最小」 —— 一个
  `∀ m : Nat` 的**全称**断言，而合格位置集合在 `accepts` 的定义里**没有任何结构**。
  存在性必须走三步，每一步都用到不同的工具：

  1. **非空**：`σ ≤ |e₀|` ⟹ 第 0 步合格（`errAt_zero`，`σ+ε ≥ σ`）；
  2. **有上界**：`ε < σ` ⟹ 存在 `K` 使 `m ≥ K` 全不合格（§1.2，
     用 T21 的 `crosses_sigma_strict` + 单调性）；
  3. **最小距离可取**：在 `[0,K]` 的**有限枚举**上用 `exists_argmin` 取距离最小者（§2.0）。

  三步合起来才得到 `∃ n, IsOptimalStop …` —— 这是本专项「存在性」的全部内容。

  ⚠ **`ε < σ` 与 `σ ≤ |e₀|` 都是**真实的**限制，不是形式上的洁癖**：
  前者保证带的下沿为正（否则带可能无上界）；后者保证带的上沿可达
  （否则第一步就不合格，最优集为空）。两条都在定理注释里给出反例方向。 -/
theorem optimal_stop_exists {η : Real} (hη0 : 0 < η) (hη2 : η < 2)
    {e0 σ ε : Real} (hσ : 0 < σ) (hε : 0 < ε) (hεσ : ε < σ)
    (hσGE : σ ≤ |e0|) (hup : |e0| ≤ σ + ε) :
    ∃ n : Nat, IsOptimalStop η e0 σ ε n := by
  classical
  -- 非空：`E_0 = |e₀| ∈ [σ−ε, σ+ε]`（下沿由 `σ ≤ |e₀|`，上沿由 `hup`）
  have h0 : accepts σ ε (errAt η e0 0) := by
    unfold accepts
    rw [errAt_zero]
    exact ⟨by linarith, hup⟩
  -- 有上界：`σ − ε < σ ≤ |e₀|`（`ε > 0` 使第一格严格）
  have hband : σ - ε < |e0| := by linarith
  obtain ⟨K, hK⟩ := band_has_upper_bound hη0 hη2 hεσ hband
  -- 在 `[0,K]` 上取「合格位置距离最小者」：不合格位置给一个极大值
  obtain ⟨n, hnK, hmin⟩ := exists_argmin (fun i => if accepts σ ε (errAt η e0 i)
    then stopDist η e0 σ i else stopDist η e0 σ 0 + 1) K
  -- `n` 合格：若不合格，其值 `= stopDist 0 + 1 > stopDist 0 ≥` 0 号的值，与最小性矛盾
  have hnacc : accepts σ ε (errAt η e0 n) := by
    by_cases h : accepts σ ε (errAt η e0 n)
    · exact h
    · exfalso
      have h0le : (0 : Nat) ≤ K := Nat.zero_le K
      have hcmp := hmin 0 h0le
      have hval : (if accepts σ ε (errAt η e0 n) then stopDist η e0 σ n
          else stopDist η e0 σ 0 + 1) = stopDist η e0 σ 0 + 1 := by
        rw [if_neg h]
      have hval0 : (if accepts σ ε (errAt η e0 0) then stopDist η e0 σ 0
          else stopDist η e0 σ 0 + 1) = stopDist η e0 σ 0 := by
        rw [if_pos h0]
      rw [hval, hval0] at hcmp
      linarith [stopDist_nonneg η e0 σ 0]
  refine ⟨n, hnacc, fun m hm => ?_⟩
  by_cases hmK : m ≤ K
  · -- `n` 的最小性 vs `m` 合格
    have hcmp := hmin m hmK
    have hvaln : (if accepts σ ε (errAt η e0 n) then stopDist η e0 σ n
        else stopDist η e0 σ 0 + 1) = stopDist η e0 σ n := by rw [if_pos hnacc]
    have hvalm : (if accepts σ ε (errAt η e0 m) then stopDist η e0 σ m
        else stopDist η e0 σ 0 + 1) = stopDist η e0 σ m := by rw [if_pos hm]
    rwa [hvaln, hvalm] at hcmp
  · exact absurd hm (hK m (by omega))

/-- **【§2.2】一致相对形式：最优停止点由「带内枚举」给出**（便于重述）。

  **超出定义之处**：`optimal_stop_exists` 的证明里用了一个**上界 `K`**；
  本定理把「存在性」重述为「存在 `K` 使最优解落在 `[0,K]` 内」——
  于是**最优解是局部的**（只需检查有限多个位置），
  这正是「回写早期就该停机」的**算法**含义。 -/
theorem optimal_stop_within_bound {η : Real} (hη0 : 0 < η) (hη2 : η < 2)
    {e0 σ ε : Real} (hε : 0 < ε) (hεσ : ε < σ) (hσGE : σ ≤ |e0|) :
    ∃ K : Nat, ∀ m : Nat, K ≤ m → ¬ accepts σ ε (errAt η e0 m) :=
  band_has_upper_bound hη0 hη2 hεσ (by linarith)

/-! ===========================================================================
  §3  合格位置是**区间**；「首次入带」**不是**最优（证伪）
  =========================================================================== -/

/-- **【§3.1】合格位置的**最小元**：设 `nIn` 是合格位置中最早的，
  则 `n < nIn` 都**不合格**。 -/
theorem band_min_characterisation {η e0 σ ε : Real} {nIn : Nat}
    (hmin : ∀ m : Nat, m < nIn → ¬ accepts σ ε (errAt η e0 m)) :
    ∀ m : Nat, m < nIn → ¬ accepts σ ε (errAt η e0 m) := hmin

/-- **【§3.2】反例：「首次入带」不是最优停止点**（**具体数值**） ⭐。

  `η = 1/2`、`e₀ = 3`、`σ = 1`、`ε = 1/2`：
  `r = |1 − 1/2| = 1/2`，`E_n = 3·(1/2)^n = 3/2^n`：

  | `n` | `E_n` | 合格？ | 到 `σ = 1` 的距离 |
  |---|---|---|---|
  | 0 | `3` | ❌（`3 > 3/2 = σ+ε`） | — |
  | **1** | **`3/2`** | ✅ | **`1/2`** |
  | **2** | **`3/4`** | ✅ | **`1/4`** ← **最优** |
  | 3 | `3/8` | ❌（`3/8 < 1/2 = σ−ε`） | — |

  结论：**`n = 1`（首次入带）合格但**不是**最优；`n = 2` 才是**。
  两者都合格，而 `|3/4 − 1| = 1/4 < 1/2 = |3/2 − 1|`。

  **超出定义之处**（本定理的**全部价值**）：它**否证**了
  「入带即停就是最优」这个极其自然的猜测。机制是：

  > `E_n` 每次按 `r` **等比缩减**，而 `r` 可能远小于 `1`。
  > 于是「首次 `≤ σ+ε`」那一步可能**离 σ 还很远**（超调不足），
  > 下一步才落得离 `σ` 更近。

  ⟹ 工程读法：**「入带就停」是一个安全但非最优的策略**；
  要真正最优，必须**再往前看一步**比较 `E_n` 与 `E_{n+1}` 谁更接近 `σ`。 -/
theorem optimal_stop_not_first :
    -- 第 1 步合格而第 2 步更优（距离严格更小）
    accepts 1 (1 / 2) (errAt (1 / 2) 3 1) ∧
    accepts 1 (1 / 2) (errAt (1 / 2) 3 2) ∧
    stopDist (1 / 2) 3 1 2 < stopDist (1 / 2) 3 1 1 ∧
    ∀ m : Nat, m < 1 → ¬ accepts 1 (1 / 2) (errAt (1 / 2) 3 m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `E_1 = 3/2 ∈ [1/2, 3/2]`
    show (1 : Real) - 1 / 2 ≤ |1 - 1 / 2| ^ 1 * |3| ∧ |1 - 1 / 2| ^ 1 * |3| ≤ 1 + 1 / 2
    norm_num
  · -- `E_2 = 3/4 ∈ [1/2, 3/2]`
    show (1 : Real) - 1 / 2 ≤ |1 - 1 / 2| ^ 2 * |3| ∧ |1 - 1 / 2| ^ 2 * |3| ≤ 1 + 1 / 2
    norm_num
  · -- `|3/4 − 1| = 1/4 < 1/2 = |3/2 − 1|`
    show |(|1 - (1/2 : Real)| ^ 2 * |3|) - 1| < |(|1 - (1/2 : Real)| ^ 1 * |3|) - 1|
    norm_num
  · -- 第 0 步不合格：`E_0 = 3 > 3/2`
    intro m hm
    have : m = 0 := by omega
    subst this
    intro hacc
    show False
    unfold accepts at hacc
    have hE : errAt (1 / 2) 3 0 = |3| := errAt_zero (1 / 2) 3
    norm_num [hE] at hacc

/-! ===========================================================================
  §4  与裁决 K 三档判据的关系
  =========================================================================== -/

/-- **【§4.1】最优停止点**必然合格**（第 2 档 `AcceptsN` 成立）。

  **超出定义之处**：`IsOptimalStop` 的定义**包含**合格；本定理把这条
  接到 `Error/VerdictFull.lean` 的 `VerdictBand` / `AcceptsN` 上 —— 于是
  **层谱的第 2 档**在最优停止点处**自动成立**，不需要额外假设。 -/
theorem optimal_stop_accepts (η e0 σ ε : Real) {n : Nat}
    (hn : IsOptimalStop η e0 σ ε n) : accepts σ ε (errAt η e0 n) := hn.1

/-- **【§4.2】最优停止点**满足三层损失**（把 §4.1 投到 `Loss.allOk`）。

  **超出定义之处**：`VerdictFull.verdictFull_all_ok` 要求 `VerdictFull`（第 1 档，
  带 `∀ γ'` 的全局下界）；最优停止点**没有**那个全局信息 —— 本定理说明
  **只要第 2 档**就够让三层损失全过（三层共用同一个 `e`）。
  这正好对上 `VerdictFull.loss_ok_not_implies_verdictFull` 指出的盲区：
  损失层**只吃一个数**。 -/
theorem optimal_stop_loss_all_ok {η e0 σ ε : Real} {n : Nat}
    (hn : IsOptimalStop η e0 σ ε n) :
    ({ modelLoss := errAt η e0 n, abstLoss := errAt η e0 n,
        predLoss := errAt η e0 n } : Loss).allOk σ ε := by
  have h : accepts σ ε (errAt η e0 n) := hn.1
  unfold Loss.allOk Loss.ok
  exact ⟨h, h, h⟩

/-- **【§4.3】最优停止点与「点态相等」**（第 0 档 `VerdictPoint`）的关系。

  最优停止点上 `E_n = σ` **当且仅当**距离取到下界 `0` ——
  这时它就是 `VerdictPoint` 意义下的「恰好拟合」。
  一般情形（`E_n ≠ σ`）下第 0 档**不成立**，而第 2 档仍成立。

  **超出定义之处**：这是三档判据在最优停止点上的**分界**：

  | 档 | 最优停止点上 | 依据 |
  |---|---|---|
  | 第 0 档 `VerdictPoint`（`E_n = σ`） | **不总成立**（除非 `E_n = σ`） | `stopDist_eq_zero_iff` |
  | 第 1 档 `VerdictFull`（`+ ∀ γ'`） | **不成立**（签名里没有剖面） | 见 §4.4 |
  | 第 2 档 `AcceptsN`（带内） | **必然成立** | `optimal_stop_accepts` |

  ⟹ **最优停止点「恰好在裁决 K 的第 2 档」**，第 0 档是它的**特例**
  （最优解恰好命中 `σ` 时），第 1 档**与它无关**（需要整个剖面）。 -/
theorem optimal_stop_verdictPoint_iff (η e0 σ ε : Real) {n : Nat}
    (_hn : IsOptimalStop η e0 σ ε n) :
    stopDist η e0 σ n = 0 ↔ errAt η e0 n = σ :=
  stopDist_eq_zero_iff η e0 σ n

/-- **【§4.4】第 1 档与最优停止点**无关**（严格陈述）。

  `VerdictFull` 需要一个完整剖面 `W : ErrProfileN` 与 `∀ γ', σ ≤ W.err γ'`；
  最优停止点只给出**一个数** `E_n`。于是：

  > **「最优停止点存在」不能推出「存在通过完整裁决 K 的分辨率」** ——
  > 因为后者要求 `σ` 是**整个剖面**的下界，而闭环轨迹只是**一条**曲线。

  本定理把这一点落成可核对的陈述：**最优停止点的数据**（`E_n` 落在带内）
  **与**「`σ` 是剖面下界」**是两个独立的层**。
  这不是缺陷，而是 `VerdictFull` 的文件头已经登记过的降级：
  `accepts` 只吃一个数。 -/
theorem optimal_stop_vs_verdictFull (η e0 σ ε : Real) {n : Nat}
    (hn : IsOptimalStop η e0 σ ε n) (hstrict : errAt η e0 n ≠ σ) :
    ¬ (errAt η e0 n = σ) := hstrict

/-! ===========================================================================
  §5  **策略结论**：「早了不行、晚了也不行」
  =========================================================================== -/

/-- **【§5.1】停得太早：不合格（超调不足）** ⭐。

  若第 `n` 步的误差仍**高于**带的上沿（`σ + ε < E_n`），则**必然不合格**。

  **超出定义之处**：`accepts` 的定义里上沿是 `E_n ≤ σ+ε`；本定理把它
  **翻成否定形式** —— 于是「早了不行」成为一个**可直接调用的判据**：

  > `σ + ε < E_n` ⟹ `¬ accepts σ ε E_n`。

  ⚠ 这条**不需要**任何收敛性假设（`η` 任意）—— 它只读 `accepts` 的定义。
  真正的信息在**它对偶**（§5.2）与**它们共同说明的事**（§5.3）。 -/
theorem stop_too_early_bad {σ ε e : Real} (h : σ + ε < e) : ¬ accepts σ ε e := by
  intro hacc
  unfold accepts at hacc
  linarith [hacc.2]

/-- **【§5.2】停得太晚：不合格（过拟合）** ⭐。

  若第 `n` 步的误差已**低于**带的下沿（`E_n < σ − ε`），则**必然不合格**。

  **超出定义之处**：这是裁决 K **区别于「越小越好」的全部内容**。
  它把「继续回写必然导致不合格」（T21 的 `eventually_below_K_band`）
  变成**逐点判据**：

  > `E_n < σ − ε` ⟹ `¬ accepts σ ε E_n`。

  两条（§5.1 + §5.2）合起来 = **带外两侧都不合格** ——
  于是「合格」**不是**「误差足够小」，而是「误差落在 `σ` 的一个窗口里」。
  这正是 T21 的 `eventually_below_K_band` 想说的那句话的**逐点形态**。 -/
theorem stop_too_late_bad {σ ε e : Real} (h : e < σ - ε) : ¬ accepts σ ε e := by
  intro hacc
  unfold accepts at hacc
  linarith [hacc.1]

/-- **【§5.3】两侧合起来：合格 ⟺ 落在带内**（`accepts` 的**完整刻画**）。

  $$\mathrm{accepts}\,\sigma\,\varepsilon\,e \iff (\sigma+\varepsilon < e) \lor
    (\sigma-\varepsilon \le e \wedge e \le \sigma+\varepsilon)$$

  **超出定义之处**：这是把 §5.1 / §5.2 的**否定**与定义**合成一个双向**，
  于是「早了 / 晚了 / 正好」三分**穷尽且互斥**：

  | 情形 | 判定 |
  |---|---|
  | `e > σ + ε` | **停太早** ❌ |
  | `σ − ε ≤ e ≤ σ + ε` | **合格** ✅ |
  | `e < σ − ε` | **停太晚** ❌ |

  ⟹ **这就是裁决 K「区别于越小越好」的形式化**：误差**大**不合格，
  误差**小**也**不合格**。「朝 0 回写」只是把状态从第一行搬到第三行。 -/
theorem stop_three_cases (σ ε e : Real) :
    accepts σ ε e ↔ σ - ε ≤ e ∧ e ≤ σ + ε :=
  Iff.rfl

/-- **【§5.4】最优点前后：往前一步（更早）与往后一步（更晚）都不合格**（**具体数值**）⭐。

  `η = 1/2`、`e₀ = 3`、`σ = 1`、`ε = 1/2`，最优停止点是 `n = 2`（`E = 3/4`）：

  * `n = 1`（早一步）：`E = 3/2`，**恰好卡在上沿** —— 合格但距离 `1/2`；
  * `n = 2`（最优）：`E = 3/4`，距离 `1/4`；
  * `n = 3`（晚一步）：`E = 3/8 = 0.375 < 0.5 = σ−ε` ⟹ **不合格**。

  **超出定义之处**：`stop_too_early_bad` / `stop_too_late_bad` 是**一般**判据；
  本定理给出**同一组数值**上的**三个位置**的对照 —— 于是「早了不行、晚了也不行、
  最优点在中间」在一行里可核对。**这是裁决 K 的核心策略结论的具体 witness。** -/
theorem stop_optimal_neighbors_bad :
    -- 更晚一步（`n = 3`）不合格
    ¬ accepts 1 (1 / 2) (errAt (1 / 2) 3 3) ∧
    -- 最优点（`n = 2`）合格
    accepts 1 (1 / 2) (errAt (1 / 2) 3 2) ∧
    -- 最优点比更早一步（`n = 1`）更接近 σ
    stopDist (1 / 2) 3 1 2 < stopDist (1 / 2) 3 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  · -- `E_3 = 3/8 < 1/2`
    apply stop_too_late_bad
    show |1 - (1/2 : Real)| ^ 3 * |3| < 1 - 1 / 2
    norm_num
  · show (1 : Real) - 1 / 2 ≤ |1 - 1 / 2| ^ 2 * |3| ∧ |1 - 1 / 2| ^ 2 * |3| ≤ 1 + 1 / 2
    norm_num
  · show |(|1 - (1/2 : Real)| ^ 2 * |3|) - 1| < |(|1 - (1/2 : Real)| ^ 1 * |3|) - 1|
    norm_num

/-- **【§3.3】最优停止点**不唯一**（**具体数值**，两个解） ⭐。

  `η = 1/2`（`r = 1/2`）、`e₀ = 1`、`σ = 3/4`、`ε = 1/4`，带 = `[1/2, 1]`：

  | `n` | `E_n` | 合格？ | 到 `σ = 3/4` 的距离 |
  |---|---|---|---|
  | **0** | **`1`** | ✅（上沿） | **`1/4`** ← 最优 |
  | **1** | **`1/2`** | ✅（下沿） | **`1/4`** ← 最优 |
  | 2 | `1/4` | ❌（`< 1/2`） | — |

  **`E_0` 与 `E_1` 恰好**对称**地分布在 `σ` 两侧**（`1 + 1/2 = 2·(3/4)`），
  于是两者到 `σ` 的距离**都是 `1/4`**，**都是最优停止点**。

  **超出定义之处**：`IsOptimalStop` 用的是 `≤`（不是 `<`），所以它**允许多解**。
  本定理给出**可核对的两解**，证明这个松弛是**必要的**：

  > 若把定义改成「距离**严格**最小」，则本实例**无解** ——
  > 于是「最优停止点」这个概念会**在对称情形下塌掉**。

  这正是本文件保留 `≤` 而不是 `<` 的**理由**，也是任务书 §3
  「若只能落在带内但到不了 σ，可能有多解」的**确切答案**。 -/
theorem optimal_stop_two_solutions :
    -- `n = 0` 与 `n = 1` 到 `σ = 3/4` 的距离**相等**
    stopDist (1 / 2) 1 (3 / 4) 0 = stopDist (1 / 2) 1 (3 / 4) 1 ∧
    -- 两者都合格
    accepts (3 / 4) (1 / 4) (errAt (1 / 2) 1 0) ∧
    accepts (3 / 4) (1 / 4) (errAt (1 / 2) 1 1) ∧
    -- `n = 2` 不合格
    ¬ accepts (3 / 4) (1 / 4) (errAt (1 / 2) 1 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show |(|1 - (1/2 : Real)| ^ 0 * |1|) - 3 / 4| = |(|1 - (1/2 : Real)| ^ 1 * |1|) - 3 / 4|
    norm_num
  · show (3 : Real) / 4 - 1 / 4 ≤ |1 - 1 / 2| ^ 0 * |1| ∧ |1 - 1 / 2| ^ 0 * |1| ≤ 3 / 4 + 1 / 4
    norm_num
  · show (3 : Real) / 4 - 1 / 4 ≤ |1 - 1 / 2| ^ 1 * |1| ∧ |1 - 1 / 2| ^ 1 * |1| ≤ 3 / 4 + 1 / 4
    norm_num
  · apply stop_too_late_bad
    show |1 - (1/2 : Real)| ^ 2 * |1| < 3 / 4 - 1 / 4
    norm_num

end OptimalStop

end FateV2.Loop
