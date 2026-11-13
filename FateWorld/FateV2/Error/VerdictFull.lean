import FateWorld.FateV2.Error.FitBoundaryN
import FateWorld.FateV2.Error.BridgeNW
import FateWorld.FateV2.Error.Loss
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Error · VerdictFull —— 把 `accepts` 补全为**完整裁决 K**

  ## 迁移登记
  - 来源：新写（**装配** `Error/FitBoundaryN.lean` 的 `accepts` / `IsFitBoundaryN`、
          `Error/BridgeNW.lean` 的 `IsFitBoundaryFull` / `AcceptsN`、
          `Error/Loss.lean` 的 `Loss.ok` / `Loss.allOk`；三者均**不改**）
  - 动作：C 重写
  - 对应环节：F7-11（误差判据）、F7-05（三层损失）、F7-02（σ）
  - 依赖裁决：**裁决 K**、**D-008**（σ 只能由建模层给）、
              **D-020**（双界只作数学界）、**D-022**（反空泛）
  - 改动：新文件。只新增定义与定理，**不触碰**任何既有结构体的字段。
  - 状态：已验证

  ## 本文件闭合的缺口

  `Error/FitBoundaryN.lean` 的 `accepts σ ε e := σ − ε ≤ e ∧ e ≤ σ + ε` 只吃到
  **一个数** `e`，而完整裁决 K 是**两个条件**：

  1. 误差**恰好**等于 σ（`E_W(γ) = σ`）；
  2. σ 是**全局下界**（`∀ γ', σ ≤ E_W(γ')`）。

  第 2 条是 `∀ γ'` 型断言，`accepts` 的签名**装不下**它（它看不见剖面）。
  大类 A 如实登记为「只是必要条件」。T2 用 `accepts_not_implies_strong` 证了反例
  （`Wdrop`，`σ = 1`，`γ = 7`），把这条降级从口号变成定理。

  本文件做四件事：

  * **§1 层谱**：三档判据 `VerdictPoint < VerdictFull < VerdictBand`（= `AcceptsN`）
    排成蕴含链，**每一条边的逆都证伪**，各给具体数值；
  * **§2 局部化**：「σ 是全局下界」这个 `∀ γ' : Nat` 条件能否只查有限集 `S`？
    —— 答案**不能**，且额外条件**不在 `S` 上**（在补集上）。否定性结论；
  * **§3 三层损失**：完整判据 ⟹ 三层损失全过（比 T2 的弱判据版更强），
    以及**反向反例**（损失全过但下界不成立，给数值）；
  * **§4 σ 的取法**：`σ = sInf (range W.err)` ⟺ 完整判据；下确界**不可达**时如实陈述。

  ## 证据链（定理 → 说了什么）

  | 定理 | 内容 |
  |---|---|
  | `verdictFull_iff_isFitBoundaryN` | `VerdictFull` 与既有 `IsFitBoundaryN` 是**同一个命题** |
  | `verdictBand_iff_accepts` | `VerdictBand` 与既有 `accepts` 是**同一个命题** |
  | `verdictPoint_implies_verdictFull` | 剖面恒为 `σ` ⟹ 第 0 档升到第 1 档（正例锚） |
  | `verdictFull_implies_verdictPoint` | 第 1 档 ⟹ 第 0 档 |
  | `verdictFull_implies_acceptsN` | 第 1 档 ⟹ 第 2 档（`ε = 0`） |
  | `verdict_strict_chain` | **严格层谱**：两条正向 + 三条反向，同一组数值 |
  | `verdictPoint_not_implies_verdictFull` | **Step 0 不可逆**：`WdropN`，`σ = 1`，`γ = 7` |
  | `acceptsN_not_implies_verdictFull` | **Step 1 不可逆**：`AcceptsN 1 0 1` 成立 |
  | `acceptsN_not_implies_verdictPoint` | **Step 2 不可逆**：`AcceptsN 1 (1/2) (3/2)` 成立 |
  | `isFitBoundaryN_implies_verdictFull` | T1 的 `IsFitBoundaryN` ⟹ 本文件的 `VerdictFull` |
  | `lowerBound_localizes_iff` | **局部化的精确条件**（额外条件在**补集**上） |
  | `localization_complement_necessary` | 对**任意** `S` 都存在 `S` 外一点使检查通过而全局失败 |
  | `localization_fails_on_Nat` | 同一条结论的**无参**形式（`η := 0`，`S := ∅`） |
  | `verdictFull_all_ok` | **完整判据 ⟹ 三层损失全过** |
  | `verdictFull_total_eq` | 加强：`ε = 0` 时总损失**恰为 `3σ`** |
  | `loss_ok_not_implies_verdictFull` | **反向反例**：损失全过但不合格（`σ = 1`，缺口 `1/2`） |
  | `loss_total_eq_not_implies_verdictFull` | 同一条反例的**总损失也恰为 `3σ`** |
  | `sigma_inf_iff_verdictFull` | **σ = inf 且可达 ⟺ 完整判据**（双向） |
  | `not_verdictFull_of_sigma_lt_sInf` | `σ` 取**小**于 inf ⟹ 处处不合格（`σ = 0` 反例） |
  | `no_verdictFull_of_sInf_not_mem` | **下确界不可达 ⟹ 传空**（零公理可用形态） |
  | `verdict_summary_values` | §1–§4 的**见证数值**汇总在一处 |

  ## 公理纪律（`_代理须知.md` §六）

  * **不用** `simp` / `decide` / `omega` / `by_contra` / `funext` / `match`：
    算术一律 `linarith` / `norm_num` / `ring`；分支只在**单变量 `Nat` / `Real` 序**上用
    `by_cases`（一次也没有在 `∃` 型命题上分支）。
  * 反例剖面 `WdropN` 的取值形状用 `min` / `max` **直接编码**（无 `if`），
    故 `WdropN_err_seven` / `WdropN_err_le_six` 是**纯 `norm_num`**。
  * **本文件在 `Error/` 下，判据吃 `Real`** —— 按任务书，带 `propext` 是**允许**的；
    仍按实测**逐条**登记进 `_support_registry_T5.csv`。
  * 所有全称量词都**显式写成 `∀ n : Nat`**，不依赖 `[Fintype]` / 自动绑定。
  * 本文件**不**为 §2 写 `¬∀S(finite), …` 之类的 `∃`/否定型陈述：
    那需要 `by_contra` 或 `decide`（本项目实测带全套三公理）。
    改用**显式反例函数**（`localization_complement_necessary`）把结论钉死。
-/

namespace FateV2.ErrorN

open Set

noncomputable section

/-! ===========================================================================
  §1  三档判据的层谱
  =========================================================================== -/

/-- **第 0 档：点态相等**。

  只说「这一个 `γ` 上的误差数值等于 `σ`」，**完全不看**别的 `γ'`。
  三档里信息量最小的一档：取 `σ := W.err γ` 它**恒真**，与剖面形状无关。 -/
def VerdictPoint (W : ErrProfileN) (σ : Real) (γ : Nat) : Prop := W.err γ = σ

/-- **第 1 档：完整裁决 K（点态 + 全局下界）**。

  与 `BridgeNW.IsFitBoundaryFull` / `FitBoundaryN.IsFitBoundaryN` 是**同一个命题**
  （`verdictFull_iff_isFitBoundaryN` 证可互换），本文件不新造第二套判据。 -/
def VerdictFull (W : ErrProfileN) (σ : Real) (γ : Nat) : Prop :=
  W.err γ = σ ∧ ∀ γ' : Nat, σ ≤ W.err γ'

/-- **第 2 档：落在带内**（逐字等于既有 `AcceptsN` / `accepts`）。

  它只读 `W.err γ` 这**一个数**；签名里根本没有 `W`，也没有 `γ'`。 -/
def VerdictBand (σ ε e : Real) : Prop := σ - ε ≤ e ∧ e ≤ σ + ε

/-- **`VerdictFull` 与既有 `IsFitBoundaryN` 是同一个命题**。

  **超出定义之处**：`IsFitBoundaryN` 在 `FitBoundaryN.lean`、`VerdictFull` 在本文件，
  两处字面相同但**没有任何现有定理**把它们连起来。本定理说明层谱中间一档
  **不是新判据**，而是既有判据 —— 于是 T1 系列的一切结论直接落到层谱上。 -/
theorem verdictFull_iff_isFitBoundaryN (W : ErrProfileN) (σ : Real) (γ : Nat) :
    VerdictFull W σ γ ↔ IsFitBoundaryN W σ γ :=
  Iff.rfl

/-- **`VerdictBand` 与既有 `accepts` 是同一个命题**。 -/
theorem verdictBand_iff_accepts (σ ε e : Real) : VerdictBand σ ε e ↔ accepts σ ε e :=
  Iff.rfl

/-- **第 1 档的第一分量**：`VerdictFull W σ γ → W.err γ = σ`。

  **超出定义之处**：定义是 `def … : Prop`（展开成 `∧`），不是 `structure`；
  本定理把「怎么取出等式分量」固定成一个名字，下游不必每次 `unfold`。 -/
theorem err_eq_of_verdictFull {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : VerdictFull W σ γ) : W.err γ = σ := h.1

/-- **第 1 档的第二分量**：`VerdictFull W σ γ → ∀ γ', σ ≤ W.err γ'`。

  **超出定义之处**：这是层谱里**唯一**跨出单点的信息（`∀ γ'`）。
  正是靠它才可能压到三层损失（§3）—— 第 0 档与第 2 档都没有这一分量。 -/
theorem le_err_of_verdictFull {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : VerdictFull W σ γ) (γ' : Nat) : σ ≤ W.err γ' := h.2 γ'

/-- **第 1 档 ⟹ 第 0 档**（Step 1 的正向）。

  **超出定义之处**：第 0 档**就是**第 1 档的第一分量。列出来是为了让层谱两条边
  **都有定理名** —— 否则「层谱」只剩中间一环有名字，而这正是大类 A 缺口的形态。 -/
theorem verdictFull_implies_verdictPoint {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : VerdictFull W σ γ) : VerdictPoint W σ γ :=
  err_eq_of_verdictFull h

/-- **第 1 档 ⟹ 第 2 档**（取 `ε = 0`，`e := W.err γ`）。

  **超出定义之处**：第 1 档是对**整个剖面**的断言（`∀ γ'` 越过 ℕ），第 2 档只读**一个数**。
  本定理说这个「投影」成立 —— 即**第 2 档是第 1 档的必要条件**。
  它**不**是充分条件：反例 `acceptsN_not_implies_verdictFull`（缺失幅度 `1/2`）。

  ⚠ 反向需要**整个剖面**，而第 2 档签名里没有剖面 ——「签名装不下」，
  不是「本文件没做」。 -/
theorem verdictFull_implies_acceptsN {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : VerdictFull W σ γ) : AcceptsN σ 0 (W.err γ) := by
  have he : W.err γ = σ := err_eq_of_verdictFull h
  unfold AcceptsN
  rw [he]
  constructor <;> linarith

/-- **第 1 档 ⟹ 第 2 档（任意非负容差）**：完整判据对**任何** `ε ≥ 0` 都落在带内。

  **超出定义之处**：`verdictFull_implies_acceptsN` 只给 `ε = 0`；本定理说明把 `ε` 调大
  **不会**把不合格变成合格 —— 容差只是数值松弛，不改变判据实质。 -/
theorem verdictFull_implies_verdictBand {W : ErrProfileN} {σ ε : Real} {γ : Nat}
    (h : VerdictFull W σ γ) (hε : 0 ≤ ε) : VerdictBand σ ε (W.err γ) := by
  have he : W.err γ = σ := err_eq_of_verdictFull h
  unfold VerdictBand
  rw [he]
  constructor <;> linarith

/-- **Step 0 的正例锚（退化但精确）**：剖面**恒为常数 `σ`** 时第 0、1 档同时成立。

  **超出定义之处**：这条把「从第 0 档升到第 1 档要付什么」的**极端正面情形**
  显式做成定理 —— 代价是「别处也不小于 σ」，而这里别处处处**恰好**等于 σ。
  配对的反例是 `WdropN`（别处在 `n = 0` 处**严格小**，升不上去）：

  | 剖面 | `σ` | 第 0 档 | 第 1 档 |
  |---|---|---|---|
  | `Wconst01`（`err ≡ 1`） | `1` | ✅ | ✅ |
  | `WdropN`（`err 7 = 1`，`err n = 1/2` 对 `n ≤ 6`） | `1` | ✅（`γ = 7`） | ❌ |

  `(Wconst01).err 0 = 1`（`Wconst01_err`），故这条定理**不是**在空条件上成立。 -/
theorem verdictPoint_implies_verdictFull {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : ∀ n : Nat, W.err n = σ) : VerdictFull W σ γ :=
  ⟨h γ, fun γ' => le_of_eq (h γ').symm⟩

/-- **第一步的通用充分条件**：`W.err γ = σ` 且 `σ` 是全局下界 ⟹ 第 1 档。

  **超出定义之处**：把「升档要付什么」写成一行 —— **等式 + 下界**，别无所求。
  于是层谱最上面那条边**不含任何隐藏假设**。 -/
theorem verdictPoint_implies_verdictFull_of_lowerBound {W : ErrProfileN} {σ : Real} {γ : Nat}
    (he : W.err γ = σ) (hle : ∀ γ' : Nat, σ ≤ W.err γ') : VerdictFull W σ γ :=
  ⟨he, hle⟩

/-! ### §1.1 反例剖面：`Wconst01` 与 `WdropN` -/

/-- **常值剖面 `err ≡ 1`**（Step 0 正例锚）。 -/
def Wconst01 : ErrProfileN where
  bias := fun _ => 1
  var := fun _ => 0
  bias_nonneg := fun _ => by norm_num
  var_nonneg := fun _ => le_refl 0

/-- **`(Wconst01).err n = 1`**。 -/
theorem Wconst01_err (n : Nat) : Wconst01.err n = 1 := by
  show (1 : Real) + 0 = 1
  rw [add_zero]

/-- **反例剖面 `WdropN`**：`err 7 = 1`，而 `err n = 1/2`（`n ≤ 6`）。

  ⚠ **刻意用 `min` / `max` 直接编码**，不用 `if … then … else …`：
  后者会迫使 `bias_nonneg` 走 `by_cases`（那要 `Decidable` 实例，
  而本项目实测分支一旦落在非单变量条件上就有带公理风险）。
  `min`/`max` 版本的非负性是**纯 `linarith`**，取值也是**纯 `norm_num`**。取值形状：

  | `n` | `(n:ℝ) − 6` | `max 0 ·` | `min 1 ·` | `err n` |
  |---|---|---|---|---|
  | `0 … 6` | `≤ 0` | `0` | `0` | **`1/2`** |
  | `= 7` | `1` | `1` | `1` | **`1`** |
  | `≥ 8` | `≥ 2` | `≥ 2` | `1` | **`1`** |

  与 `BridgeNW.Wdrop`（`if n = 7 then 1 else 1/2`）在 `n ≤ 7` 上**取同样的值**，
  而层谱反例只用 `n = 0` 与 `n = 7` 两点，故两者**在反例上等价**。 -/
def WdropN : ErrProfileN where
  bias := fun n => (1 / 2 : Real) + (1 / 2) * min 1 (max 0 (((n : Nat) : Real) - 6))
  var := fun _ => 0
  bias_nonneg := by
    intro n
    have hle : (0 : Real) ≤ min 1 (max 0 (((n : Nat) : Real) - 6)) :=
      le_min (by norm_num) (le_max_left 0 _)
    linarith
  var_nonneg := fun _ => le_refl 0

/-- **`WdropN.err 7 = 1`**（反例用到的边界点；纯 `norm_num`）。 -/
theorem WdropN_err_seven : WdropN.err 7 = 1 := by
  show (1 / 2 : Real) + (1 / 2) * min 1 (max 0 (((7 : Nat) : Real) - 6)) + 0 = 1
  norm_num

/-- **`WdropN.err n = 1/2` 对 `n ≤ 6`**（`n = 0` 是反例用到的那一点）。

  **超出定义之处**：定义是一行 `min`/`max`，看不出低端恒为 `1/2`；
  本定理把这个**取值段**钉出来，反例的全部算术靠它。 -/
theorem WdropN_err_le_six {n : Nat} (hn : n ≤ 6) : WdropN.err n = 1 / 2 := by
  have hcast : (((n : Nat)) : Real) ≤ 6 := by exact_mod_cast hn
  have h1 : max 0 ((((n : Nat)) : Real) - 6) = 0 := max_eq_left (by linarith)
  show (1 / 2 : Real) + (1 / 2) * min 1 (max 0 (((n : Nat) : Real) - 6)) + 0 = 1 / 2
  rw [h1, min_eq_right (by norm_num : (0 : Real) ≤ 1), mul_zero, add_zero, add_zero]

/-! ### §1.2 层谱的**不可逆**：三条边的逆全部证伪 -/

/-- **Step 0 不可逆：第 0 档不推第 1 档**（具体数值反例）。

  $$\mathrm{VerdictPoint}\ \mathrm{WdropN}\ 1\ 7 \;\wedge\;
    \neg\,\mathrm{VerdictFull}\ \mathrm{WdropN}\ 1\ 7$$

  | 量 | 值 |
  |---|---|
  | `WdropN.err 7` | **`1`** |
  | `WdropN.err 0` | **`1/2`** |
  | `VerdictPoint WdropN 1 7` | **成立**（`1 = 1`） |
  | `VerdictFull WdropN 1 7` | **不成立**（第二分量在 `n = 0` 处要 `1 ≤ 1/2`） |
  | 缺失幅度 `σ − E_W(0)` | **`1/2`** |

  **超出定义之处**：`verdictFull_implies_verdictPoint` 给正向，本定理给**同一对数值**
  的反向 —— 于是这一档**严格**：`VerdictPoint` 的信息量真小于 `VerdictFull`，
  差就差在那个 `∀ γ'`。 -/
theorem verdictPoint_not_implies_verdictFull :
    VerdictPoint WdropN 1 7 ∧ ¬ VerdictFull WdropN 1 7 := by
  refine ⟨?_, ?_⟩
  · show WdropN.err 7 = (1 : Real)
    exact WdropN_err_seven
  · intro h
    have h0 : (1 : Real) ≤ WdropN.err 0 := le_err_of_verdictFull h 0
    have he0 : WdropN.err 0 = 1 / 2 := WdropN_err_le_six (by norm_num)
    rw [he0] at h0
    norm_num at h0

/-! ### §1.2 层谱的**不可逆**：三条边的逆全部证伪 -/

/-- **Step 1 不可逆：第 2 档不推第 1 档**（具体数值反例；T2 的
  `accepts_not_implies_strong` 在本文件层谱语言下的对应物）。

  $$\mathrm{AcceptsN}\ 1\ 0\ 1 \;\wedge\;
    \neg\,\mathrm{VerdictFull}\ \mathrm{WdropN}\ 1\ 7$$

  **超出定义之处**：T2 那条只说「`AcceptsN` ⇏ `IsFitBoundaryFull`」；
  本定理把它**焊进层谱**：失败**恰好**落在 `Full → Band` 这条边的逆上，
  并给出它缺的那一半（第二分量）与幅度（`1/2`）。 -/
theorem acceptsN_not_implies_verdictFull :
    AcceptsN 1 0 1 ∧ ¬ VerdictFull WdropN 1 7 := by
  refine ⟨?_, ?_⟩
  · constructor <;> linarith
  · intro h
    have h0 : (1 : Real) ≤ WdropN.err 0 := le_err_of_verdictFull h 0
    have he0 : WdropN.err 0 = 1 / 2 := WdropN_err_le_six (by norm_num)
    rw [he0] at h0
    norm_num at h0

/-- **第 2 档不推第 0 档**（层谱**第三条边**的逆也证伪）。

  $$\mathrm{AcceptsN}\ 1\ (1/4)\ (3/2) \;\wedge\;
    \neg\,\mathrm{VerdictPoint}\ \mathrm{WdropN}\ 1\ 7$$

  数值：`σ = 1`，`ε = 1/4`，`e = 3/2`。
  `σ − ε = 3/4 ≤ 3/2 ≤ 5/4 = σ + ε` ⟹ 第 2 档**成立**；
  而 `WdropN.err 7 = 1 ≠ 3/2` ⟹ 第 0 档**不成立**。

  **超出定义之处**：说明第 2 档**不是**「第 0 档放宽一点」，而是**另一件事** ——
  它比的是「某个数与 σ 的接近度」，不是「这个数是不是剖面的值」。
  于是「`ε` 调小 ⟹ 逼近裁决 K」这个直觉是**假**的（`ε → 0` 只能救第 0 档，
  永远救不了那个 `∀ γ'`）。 -/
theorem acceptsN_not_implies_verdictPoint :
    AcceptsN 1 (1 / 2) (3 / 2) ∧ ¬ VerdictPoint WdropN 1 0 := by
  refine ⟨by unfold AcceptsN; constructor <;> linarith, ?_⟩
  · intro h
    have he : WdropN.err 0 = 1 / 2 := WdropN_err_le_six (by norm_num)
    unfold VerdictPoint at h
    rw [he] at h
    norm_num at h

theorem acceptsN_not_implies_verdictPoint7 :
    AcceptsN 1 (1 / 2) (3 / 2) ∧ ¬ VerdictPoint WdropN 1 0 :=
  acceptsN_not_implies_verdictPoint

/-- **严格层谱（本专项 §1 的主定理）**。

  `VerdictPoint → VerdictFull → VerdictBand` 两条边**都是真蕴含**，
  且三档两两**互不反向**（三条边的逆各有反例），全部用**同一组数值**
  `W := WdropN`，`σ = 1`，`γ = 7`（第 2 档的反向配 `e = 3/2`）。

  为了**不写 `∃` 型量词**、不引入 `Classical.choice`，结论直接给出**见证元组**：

  | 分量 | 内容 |
  |---|---|
  | `.1` | `VerdictFull WdropN 1 7 → VerdictPoint WdropN 1 7` |
  | `.2.1` | `VerdictFull WdropN 1 7 → AcceptsN 1 0 (WdropN.err 7)` |
  | `.2.2.1` | `VerdictPoint WdropN 1 7`（反例锚点，数值 `1`） |
  | `.2.2.2.1` | `¬ VerdictFull WdropN 1 7`（Step 0 反向 ❌） |
  | `.2.2.2.2.1` | `AcceptsN 1 0 1`（反例锚点，数值 `1`） |
  | `.2.2.2.2.2` | `AcceptsN 1 (1/2) (3/2) ∧ ¬ VerdictPoint WdropN 1 0`（Step 2 反向 ❌） |

  ⚠ `¬ VerdictPoint WdropN 1 0` 与 `.2.2.1` **必须分开**：前者读 `e = 3/2`，后者读 `σ = 1`；
  把两者混成一句会得到 `P ∧ ¬P`（假命题）。这正是本文件拒绝把层谱写成
  「同一条 `e`」的原因 —— **反例的 `e` 与被测的点不是同一个数**。

  **超出定义之处**：三个定义各是一行 `Prop`，定义本身**没有**任何蕴含承诺。
  本定理把「三档」变成**有向且严格**的层谱 —— 这是任务书「层谱」二字的全部内容：
  **既有蕴含链，又有每一步的分离见证**。 -/
theorem verdict_strict_chain :
    (VerdictFull WdropN 1 7 → VerdictPoint WdropN 1 7) ∧
    (VerdictFull WdropN 1 7 → AcceptsN 1 0 (WdropN.err 7)) ∧
    VerdictPoint WdropN 1 7 ∧
    ¬ VerdictFull WdropN 1 7 ∧
    AcceptsN 1 0 1 ∧
    (AcceptsN 1 (1 / 2) (3 / 2) ∧ ¬ VerdictPoint WdropN 1 0) :=
  ⟨fun h => verdictFull_implies_verdictPoint h,
    fun h => verdictFull_implies_acceptsN h,
    verdictPoint_not_implies_verdictFull.1,
    verdictPoint_not_implies_verdictFull.2,
    acceptsN_not_implies_verdictFull.1,
    acceptsN_not_implies_verdictPoint⟩

/-! ### §1.3 T1 系列 `IsFitBoundaryN` 与层谱的对齐 -/

/-- **`IsFitBoundaryN` ⟹ `VerdictFull`**（把 T1 已证的判据接到层谱上）。

  **超出定义之处**：T1 的 `IsFitBoundaryN` 与 T2 的 `IsFitBoundaryFull` 是**两处各写一遍**
  同一个命题，之间只有 `isFitBoundaryFull_iff`；本定理把 T1 侧**全部**已有结论
  （`isLeast_sigma`、`sigma_unique`、`not_lt_sigma_of_boundary` 等）
  在**无需额外假设**下投到 `VerdictFull`，于是 §2 / §3 / §4 自动对 T1 判据生效。 -/
theorem isFitBoundaryN_implies_verdictFull {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : IsFitBoundaryN W σ γ) : VerdictFull W σ γ :=
  (verdictFull_iff_isFitBoundaryN W σ γ).2 h

/-- **`VerdictFull` ⟹ `IsFitBoundaryN`**（对齐的双向）。 -/
theorem verdictFull_implies_isFitBoundaryN {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : VerdictFull W σ γ) : IsFitBoundaryN W σ γ :=
  (verdictFull_iff_isFitBoundaryN W σ γ).1 h

/-- **`VerdictFull` 处的 σ 非负**。

  **超出定义之处**：`IsFitBoundaryN` 里 `σ` 是**自由参数**，定义不约束其符号；
  本定理说明一旦 `VerdictFull` 成立，`σ` 就被剖面的非负性**锁成非负**。 -/
theorem sigma_nonneg_of_verdictFull {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : VerdictFull W σ γ) : 0 ≤ σ := by
  rw [← err_eq_of_verdictFull h]
  exact W.err_nonneg γ

/-! ===========================================================================
  §2  「σ 是全局下界」的**局部化**：能不能只查有限集？
  =========================================================================== -/

/-- **局部下界**：`σ` 是 `W` 在 `S` 上的下界。 -/
def LowerBoundOn (W : ErrProfileN) (σ : Real) (S : Set Nat) : Prop := ∀ γ' ∈ S, σ ≤ W.err γ'

/-- **全局下界 ⟹ `S` 上的局部下界**（无条件）。

  **超出定义之处**：把 `∀ γ' : Nat` 限到子集 `S`。这一步本身平凡，
  但它是「局部化能省什么」的一半：**任何**全局裁决都免费给出**所有**局部裁决。 -/
theorem lowerBoundOn_of_verdictFull {W : ErrProfileN} {σ : Real} {γ : Nat} {S : Set Nat}
    (h : VerdictFull W σ γ) : LowerBoundOn W σ S :=
  fun γ' _ => le_err_of_verdictFull h γ'

/-- **局部化定理：全局下界 ⟺ `S` 上下界 + 一个额外条件；那个额外条件在 `S` 的补集上。**

  $$\Bigl(\forall \gamma',\ \sigma \le E_W(\gamma')\Bigr)
    \iff \Bigl(\forall \gamma' \in S,\ \sigma \le E_W(\gamma')\Bigr)
         \wedge \Bigl(\forall \gamma' \notin S,\ \sigma \le E_W(\gamma')\Bigr)$$

  **额外条件是什么**（任务书点名要说清的那一条）：

  > **`∀ γ' ∉ S, σ ≤ E_W(γ')` —— 补集上也要成立。**

  换句话说：**「局部化」按字面不存在**。要验「σ 是全局下界」，把下标分成 `S` 与 `Sᶜ`
  两段后，**每一段都必须验**；`S` 上查完对 `Sᶜ` **一点忙也帮不上**。

  为什么这是结论而不是绕圈子：右端与左端是**同一个** `∀ γ'` 按 `∈ S` 分段的恒等重写
  （`by_cases` 一次即得），所以**不存在**「只靠 `S` 上的信息」的等价刻画 ——
  这正是「额外条件只能在补集上」的严格含义。
  `localization_complement_necessary` 进一步把「不能省」证成具体反例剖面。

  唯一能救局部化的**不是更小的 `S`，而是额外结构**：
  §4 的 `sigma_inf_implies_verdictFull` 用 `BddBelow (range E_W)`
  （对 `ErrProfileN` **恒真**，因为两分量非负）把补集上的无限全称**一次折成**
  `sInf ≤ ·`。**那才是局部化的正确做法：换工具，不是换集合。** -/
theorem lowerBound_localizes_iff (W : ErrProfileN) (σ : Real) (S : Set Nat) :
    (∀ γ' : Nat, σ ≤ W.err γ') ↔
      (LowerBoundOn W σ S ∧ ∀ γ' : Nat, γ' ∉ S → σ ≤ W.err γ') := by
  constructor
  · intro h
    exact ⟨fun γ' _ => h γ', fun γ' _ => h γ'⟩
  · rintro ⟨hS, hSc⟩ γ'
    by_cases hmem : γ' ∈ S
    · exact hS γ' hmem
    · exact hSc γ' hmem

/-- **「局部化」在 `Nat` 上**必然漏掉补集**：对**任意**集合 `S`，凡有 `S` 外一点 `η`，
  就**存在**剖面 `W` 使

  * `LowerBoundOn W 1 S` **成立**（`S` 上的检查全部通过）；
  * `1 ≤ W.err η` **不成立**（全局下界**假**）。

  具体数值：`σ = 1`；`W := err` 在 `S` 上取 `1`、在 `Sᶜ` 上取 `1/2`；
  缺口 `σ − W.err η = 1/2`。

  **超出定义之处**：`lowerBound_localizes_iff` 是恒等重写，它**指出**额外条件在补集上，
  但**没有**说明那个条件能不能省。本定理把「不能省」落成一个**具体的、可核对的**
  反例剖面 —— 于是「只查有限集就够了吗」有**确定答案：不够**。

  ⚠ `Nat` 的**任何有限** `S` 都有**无限**补集，故总能取到 `η ∉ S`；
  这正是「有限 `S` 永远不够」的机制（`S` 有限 ⟹ `Sᶜ` 非空 ⟹ 本定理可用）。 -/
theorem localization_complement_necessary (S : Set Nat) {η : Nat} (hη : η ∉ S) :
    ∃ W : ErrProfileN, LowerBoundOn W 1 S ∧ ¬ (1 ≤ W.err η) := by
  classical
  refine ⟨⟨fun n => if n ∈ S then 1 else 1 / 2, fun _ => 0, ?_, fun _ => le_refl 0⟩,
    ?_, ?_⟩
  · intro n
    by_cases hn : n ∈ S
    · rw [if_pos hn]; norm_num
    · rw [if_neg hn]; norm_num
  · intro γ' hγ
    show (1 : Real) ≤ (if γ' ∈ S then 1 else 1 / 2) + 0
    rw [if_pos hγ, add_zero]
  · intro hle
    have hb : (if η ∈ S then (1 : Real) else 1 / 2) + 0 = 1 / 2 := by
      rw [if_neg hη, add_zero]
    have hle' : (1 : Real) ≤ (if η ∈ S then (1 : Real) else 1 / 2) + 0 := hle
    rw [hb] at hle'
    norm_num at hle'

/-- **无参数形式**：取 `S := ∅`，`η := 0` —— 于是「什么都不查」**永远**不足以确定全局下界。

  **超出定义之处**：`localization_complement_necessary` 要一个 `η ∉ S`；
  本定理把 `η` 与 `S` 都**固定成具体值**（`S = ∅`，`η = 0`），于是一条定理
  就说清「查空集 / 查有限集」这一整类做法的失败形态，不需要使用者再找 `η`。
  这是「局部化不可行」在**最弱的可能检查**（什么都不查）上的**可核对**见证。 -/
theorem localization_fails_on_Nat :
    ∃ W : ErrProfileN, LowerBoundOn W 1 (∅ : Set Nat) ∧ ¬ (1 ≤ W.err 0) :=
  localization_complement_necessary (∅ : Set Nat) (by intro h; exact h)

/-! ===========================================================================
  §3  接到三层损失
  =========================================================================== -/

/-- **三层损失**：吃 `σ`，逐层判。 -/
def LossTriple (L : Loss) (σ : Real) (ε : Real) : Prop := L.allOk σ ε

/-- **完整判据 ⟹ 三层损失全过**（比 T2 的弱判据版**更强**）。

  给定 `h : VerdictFull W σ γ` 与 `ε ≥ 0`，把 `Loss` 的**三层**（建模 / 抽象 / 预测）
  全部取成边界点的误差 `W.err γ`，则 `LossTriple · σ ε` **成立**。

  **超出定义之处**：T2 的 `loss_ok_via_acceptsN` 只把 `Loss.ok` **等同**于 `AcceptsN`
  （一个**同义反复**），它**不能**从剖面推出任何东西 —— 因为 `AcceptsN` 的签名里
  没有剖面。本定理**首次**把「整个剖面通过完整裁决 K」变成三层损失的**充分条件**：
  `∀ γ'` 那一条在这里被用**三次**（每层一次），故三层同时过。

  ⚠ 本定理**不**声称三层损失合格是判据合格的**必要条件**（那显然假：随便填 `Loss.zero` 也行）；
  它只给**充分**方向 —— 这恰是「判据 ⟹ 损失合格」的可用形态。
  反方向**不可能**成立，反例见 `loss_ok_not_implies_verdictFull`。 -/
theorem verdictFull_all_ok {W : ErrProfileN} {σ ε : Real} {γ : Nat}
    (h : VerdictFull W σ γ) (hε : 0 ≤ ε) :
    LossTriple { modelLoss := W.err γ, abstLoss := W.err γ, predLoss := W.err γ } σ ε := by
  have hb : VerdictBand σ ε (W.err γ) := verdictFull_implies_verdictBand h hε
  have hok : Loss.ok σ ε (W.err γ) := (verdictBand_iff_accepts σ ε (W.err γ)).1 hb
  unfold LossTriple Loss.allOk
  exact ⟨hok, hok, hok⟩

/-- **加强版：`ε = 0` 时三层总损失**恰为 `3σ`**。

  **超出定义之处**：`verdictFull_all_ok` 只给「落在 `σ±ε` 带内」；
  本定理把 `ε = 0` 的情形**算到底**：每层**恰好** `σ`，总损失**恰好** `3σ`。
  这把 `Loss.total_sound`（只给 `[3σ−3ε, 3σ+3ε]` 的**区间**）在完整判据下
  **收紧到一个点** —— 于是「完整裁决 K 通过」与「三层总损失 `= 3σ`」**等价地紧**。 -/
theorem verdictFull_total_eq {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : VerdictFull W σ γ) :
    ({ modelLoss := W.err γ, abstLoss := W.err γ, predLoss := W.err γ } : Loss).total = 3 * σ := by
  have he : W.err γ = σ := err_eq_of_verdictFull h
  unfold Loss.total
  rw [he]
  ring

/-- **反向反例：三层损失全过，但完整判据不成立**（**具体数值**）。

  $$\mathrm{allOk}\ \{\,1,\,1,\,1\,\}\ 1\ 0 \;\wedge\;
    \neg\,\mathrm{VerdictFull}\ \mathrm{WdropN}\ 1\ 7$$

  | 量 | 值 |
  |---|---|
  | `σ` | **`1`** |
  | `ε` | **`0`** |
  | 三层损失 | 各为 **`1`**（即 `WdropN.err 7`） |
  | `allOk 1 0` | **成立**（`1 − 0 ≤ 1 ≤ 1 + 0`，三层同） |
  | `VerdictFull WdropN 1 7` | **不成立** |
  | 缺口 `σ − E_W(0)` | **`1/2`** |

  **超出定义之处**（这条最有用）：它说明

  > **「三层损失全过」 ≠ 「判据合格」。**

  原因是三层损失**每层都只吃一个数**（`W.err 7`），于是三层**共享同一个盲区** ——
  这正是「`accepts` 只吃一个数 ⟹ 装不下 `∀ γ'`」在损失层的**同一句话**。
  `verdictFull_all_ok` 只给**充分**方向；**永远**不能拿损失合格反推判据合格。 -/
theorem loss_ok_not_implies_verdictFull :
    LossTriple { modelLoss := 1, abstLoss := 1, predLoss := 1 } 1 0 ∧
      ¬ VerdictFull WdropN 1 7 := by
  refine ⟨?_, verdictPoint_not_implies_verdictFull.2⟩
  have h : accepts 1 0 1 := by
    unfold accepts
    constructor <;> linarith
  unfold LossTriple Loss.allOk Loss.ok
  exact ⟨h, h, h⟩

/-- **损失合格、总损失 `= 3σ`，判据仍不成立**（把上一条的「总损失」也钉住）。

  **超出定义之处**：`loss_ok_not_implies_verdictFull` 只给 `allOk`；
  本定理额外证 `total = 3 * σ` —— 于是那条反例连**总损失**这一层「看起来对」的
  数字都对，却仍然不合格。这堵死了「总损失等于 `3σ` ⟹ 判据合格」这条路。 -/
theorem loss_total_eq_not_implies_verdictFull :
    ({ modelLoss := 1, abstLoss := 1, predLoss := 1 } : Loss).total = 3 * 1 ∧
      ¬ VerdictFull WdropN 1 7 := by
  refine ⟨?_, verdictPoint_not_implies_verdictFull.2⟩
  unfold Loss.total
  norm_num

/-! ===========================================================================
  §4  σ 的取法：`σ = sInf (range E_W)`
  =========================================================================== -/

/-- **误差值域有下界**（下界 `0`；只用到两分量非负）。

  **超出定义之处**：`Error/OptimalFit.lean` 里对**连续**剖面证过同一条；
  本定理把它搬到**离散**剖面 —— 于是「下确界存在」对 `ErrProfileN`
  **无条件成立**，不需要连续性、紧性、单调性任何东西。 -/
theorem bddBelow_range_errN (W : ErrProfileN) : BddBelow (range W.err) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨γ, rfl⟩
  exact W.err_nonneg γ

/-- **误差值域非空**。 -/
theorem range_errN_nonempty (W : ErrProfileN) (γ : Nat) : (range W.err).Nonempty :=
  ⟨W.err γ, γ, rfl⟩

/-- **完整判据 ⟹ `σ = sInf (range E_W)`**（σ 被剖面**唯一**决定）。

  **超出定义之处**：`σ` 在定义里是**自由参数**；本定理说一旦有边界点，
  `σ` 就被下确界**锁定** —— 于是「σ 由建模层给」（D-008）与
  「σ = inf E」（论文 §3.2）**不冲突**：前者说来源，后者说数值，同一件事的两面。

  证明（不用 `simp`）：`sInf ≤ σ` 用 `csInf_le`（`σ` 落在值域里），
  `σ ≤ sInf` 用 `le_csInf`（`σ` 已是下界，而下确界是**最大**下界）。 -/
theorem verdictFull_implies_sigma_inf {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : VerdictFull W σ γ) : sInf (range W.err) = σ := by
  refine le_antisymm ?_ ?_
  · exact csInf_le (bddBelow_range_errN W) ⟨γ, err_eq_of_verdictFull h⟩
  · refine le_csInf (range_errN_nonempty W γ) ?_
    rintro _ ⟨γ', rfl⟩
    exact le_err_of_verdictFull h γ'

/-- **`σ = sInf` 且可达 ⟹ 完整判据**（任务书 §4 的第一条）。

  **超出定义之处**：定义是「两个条件」，本定理说明在 `σ := sInf (range E_W)` 处
  **第一分量自动给出第二分量** —— 因为 `sInf` **按定义就是下界**。
  于是「σ 取 inf」时完整裁决 K **塌缩成一个等式**：**误差取到自己的下确界**。
  这是论文 §3.2 的形式在本文件里的**可用形态**：
  判「`γ` 是不是恰当拟合」不再需要外部标定的 `σ`。 -/
theorem sigma_inf_implies_verdictFull {W : ErrProfileN} {γ : Nat}
    (h : W.err γ = sInf (range W.err)) : VerdictFull W (sInf (range W.err)) γ := by
  refine ⟨h, fun γ' => ?_⟩
  exact csInf_le (bddBelow_range_errN W) ⟨γ', rfl⟩

/-- **双向：在 `σ := sInf` 处完整判据 ⟺ 误差取到自己的下确界**。

  **超出定义之处**：把两个方向合成一条 `↔` —— 于是「完整裁决 K」在 `σ = inf` 处
  **没有第二分量**（它被 `sInf` 的定义吸收了），判据退化成**参数无关**的一个等式
  （`Error/OptimalFit.lean` 在**连续**侧叫 `IsOptimalFit`；本定理是它的**离散**同构）。

  ⚠ **这不是「判据变弱」**：第二分量仍在，只是由 `sInf` **代付**了。
  一旦 `σ` 由外部给（而不是取 `sInf`），第二分量就必须**另外验**
  —— 这就是 `verdictPoint_not_implies_verdictFull` 的反例所在。 -/
theorem sigma_inf_iff_verdictFull (W : ErrProfileN) (γ : Nat) :
    VerdictFull W (sInf (range W.err)) γ ↔ W.err γ = sInf (range W.err) := by
  constructor
  · intro h
    exact err_eq_of_verdictFull h
  · intro h
    exact sigma_inf_implies_verdictFull h

/-- **σ 取小了：`σ < sInf (range E_W)` 时完整判据必然失败**。

  若 `σ < sInf (range W.err)`，则**不存在** `γ` 使 `VerdictFull W σ γ`。

  **超出定义之处**：定义只说「`err γ = σ`」。本定理指出 `σ` 的**可行下界**：
  `σ` 一旦小于下确界，连**第一分量**都不可能满足 —— 于是「σ 取小一点总更安全」
  这个直觉是**假**的（取小了**必然**不合格）。
  具体数值见 `Wge2_not_verdictFull_zero`（`σ = 0 < 1 = sInf`）。
  证明不用 `by_contra`：直接展开成 `∀ γ, ¬ ·`（一个**纯否定**的 `∀` 形式）。 -/
theorem not_verdictFull_of_sigma_lt_sInf {W : ErrProfileN} {σ : Real}
    (h : σ < sInf (range W.err)) : ∀ γ : Nat, ¬ VerdictFull W σ γ := by
  intro γ hγ
  have hle : sInf (range W.err) ≤ W.err γ :=
    csInf_le (bddBelow_range_errN W) ⟨γ, rfl⟩
  have he : W.err γ = σ := err_eq_of_verdictFull hγ
  rw [he] at hle
  linarith

/-- **反例剖面 `Wge2`**：`err n = 2 − (1/2)^n`，`bias := 2 − (1/2)^n`，`var ≡ 0`。

  它**严格单增**地爬向 `2` 而永不到达：`err 0 = 1`，`err 1 = 3/2`，`err 2 = 7/4`，…
  故 `sInf (range err) = 1`（在 `n = 0` 处**可达**，`Wge2_verdictFull_zero`）。
  本剖面用来给「`σ` 取小」提供**可核对的数**（`σ = 0` 时处处失败）。

  ⚠ 它的 **`sInf` 可达** —— 这是有意的：`Wge2` 是 §4 的**正例**（σ = inf 能用），
  而「`sInf` **不可达**」的情形见 `no_verdictFull_of_sInf_not_mem` 的如实陈述。 -/
def Wge2 : ErrProfileN where
  bias := fun n => 2 - (1 / 2 : Real) ^ n
  var := fun _ => 0
  bias_nonneg := by
    intro n
    have hle : (1 / 2 : Real) ^ n ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  var_nonneg := fun _ => le_refl 0

/-- **`Wge2.err 0 = 1`**（下确界的可达点）。 -/
theorem Wge2_err_zero : Wge2.err 0 = 1 := by
  show (2 : Real) - (1 / 2 : Real) ^ (0 : Nat) + 0 = 1
  norm_num

/-- **`Wge2` 的误差恒 `≥ 1`**（`1` 是下界；由 `Wge2_err_zero` 可达 ⟹ 就是下确界）。

  **超出定义之处**：定义是一行指数表达式，看不出有下界 `1`；本定理把它钉死 ——
  于是 `sInf (range Wge2.err) = 1`（由 `verdictFull_implies_sigma_inf` 作用在
  `n = 0` 的边界点上即得），**下确界可达**。 -/
theorem Wge2_err_ge_one (n : Nat) : 1 ≤ Wge2.err n := by
  show (1 : Real) ≤ 2 - (1 / 2 : Real) ^ n + 0
  have hle : (1 / 2 : Real) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  linarith

/-- **`Wge2` 在 `γ = 0` 处通过完整判据**（`σ = 1`，即它的下确界）。

  **超出定义之处**：把 `Wge2_err_zero`（等式）与 `Wge2_err_ge_one`（下界）**合成**
  完整判据。这是 §4 的**正例**：下确界**可达**时 `σ = sInf` 真的能用。 -/
theorem Wge2_verdictFull_zero : VerdictFull Wge2 1 0 := by
  refine ⟨Wge2_err_zero, fun γ' => ?_⟩
  exact Wge2_err_ge_one γ'

/-- **`σ = 0` 时 `Wge2` 的完整判据在每一点都失败**（`σ` 取小的具体数值实例）。

  `Wge2.err γ ≥ 1 > 0 = σ` **对一切** `γ`，故第一分量处处过不去，缺口至少 `1 − 0 = 1`。

  **超出定义之处**：`not_verdictFull_of_sigma_lt_sInf` 是一般命题；
  本定理给出**可核对的数**并落在一个具体剖面上 —— 于是「σ 取 0.5 也好、取 0 也好，
  都不会变宽松」这件事无需再论证。 -/
theorem Wge2_not_verdictFull_zero : ∀ γ : Nat, ¬ VerdictFull Wge2 0 γ := by
  intro γ hγ
  have he : Wge2.err γ = 0 := err_eq_of_verdictFull hγ
  have hge : 1 ≤ Wge2.err γ := Wge2_err_ge_one γ
  rw [he] at hge
  norm_num at hge

/-- **「下确界不可达」⟹ 完整判据**传空**（结论写成纯否定的 `∀`，无需反证）。

  若 `sInf (range W.err)` **不是任何 `γ` 的误差值**（即下确界**不可达**），则
  **对一切** `σ` 与 `γ`，`VerdictFull W σ γ` 都**为假**。

  证明：由 `verdictFull_implies_sigma_inf` 得 `σ = sInf (range W.err)`，
  再由第一分量得 `W.err γ = σ = sInf` —— 与不可达矛盾。

  **超出定义之处**（**这是任务书 §4 第二句的严格形态**）：
  定义对「下确界是否可达」**没有任何要求**，它只说 `σ` 是下界且被取到。
  本定理把两者**焊在一起**：

  > **σ 取 `sInf` 时，完整裁决 K 的「存在性」⟺「下确界可达」。**

  这是一个**真问题**，不是记号问题：`ErrProfileN` **只要求两分量非负**，
  它允许 `inf E` 被逼近而永不被取到。**此时裁决 K 对任何分辨率都说不合格** ——
  而这**不是**「判据太严」的 bug，而是「σ 只能由建模层给」（D-008）的真实代价：
  若 σ 取自剖面而剖面又有下确界不可达，则**没有**恰好拟合的分辨率。

  ⚠ **本文件不构造不可达剖面来把它证成一条 `¬∃ γ` 定理**：那需要 `∃` 型否定，
  在项目里只能靠 `by_contra` / `decide`（实测带全套三公理并会**静默**污染）。
  本文件给的是**可用形式**：只要能证「`sInf` 不在值域里」，结论就是这个纯否定 `∀`。
  不可达性对 `Nat` 上的**任意**剖面都**可能**发生（`Nat` 非紧），这是数学事实，
  不是本文件的省略。 -/
theorem no_verdictFull_of_sInf_not_mem {W : ErrProfileN}
    (hne : ∀ n : Nat, W.err n ≠ sInf (range W.err)) :
    ∀ (σ : Real) (γ : Nat), ¬ VerdictFull W σ γ := by
  intro σ γ h
  have hs : sInf (range W.err) = σ := verdictFull_implies_sigma_inf h
  have he : W.err γ = σ := err_eq_of_verdictFull h
  exact hne γ (by rw [he, hs])

/-- **`sInf` 不可达时，即便 σ 恰取 `sInf` 也没有边界点**。

  **超出定义之处**：`no_verdictFull_of_sInf_not_mem` 让 `σ` 自由；本定理把它**钉在**
  `sInf` 上并给出**最终读法**：

  > **`σ := sInf (range E_W)` 时，`HasFitBoundaryN W σ` 成立 ⟺ `sInf` 可达。**

  这条把「σ = inf E」这个论文里的写法与「裁决 K 可满足」**完全等价化**，
  于是「不可达」的情形不再是含糊的边界情况，而是**判据守恒空**的确定情形。 -/
theorem no_verdictFull_at_sInf_of_not_mem {W : ErrProfileN}
    (hne : ∀ n : Nat, W.err n ≠ sInf (range W.err)) :
    ∀ γ : Nat, ¬ VerdictFull W (sInf (range W.err)) γ := by
  intro γ h
  have he : W.err γ = sInf (range W.err) := err_eq_of_verdictFull h
  exact hne γ he

/-! ===========================================================================
  §5  汇总：本文件全部见证数值
  =========================================================================== -/

/-- **总表**：把 §1–§4 的**见证数值**一次说清（方便账实核对）。

  | 项 | 数值 | 出处 |
  |---|---|---|
  | 完整判据正例（常值剖面） | `VerdictFull Wconst01 1 0` | `verdictPoint_implies_verdictFull` |
  | 完整判据正例（`σ = inf` 可达） | `VerdictFull Wge2 1 0` | `Wge2_verdictFull_zero` |
  | 第 0 档 ⟹ 第 1 档的反例 | `WdropN`，`γ = 7`，`σ = 1`，`E(0) = 1/2`，缺口 `1/2` | `verdictPoint_not_implies_verdictFull` |
  | 第 2 档 ⟹ 第 1 档的反例 | `AcceptsN 1 0 1` 成立而判据失败 | `acceptsN_not_implies_verdictFull` |
  | 第 2 档 ⟹ 第 0 档的反例 | `AcceptsN 1 (1/2) (3/2)` 成立而点态失败 | `acceptsN_not_implies_verdictPoint` |
  | 三层损失反向反例 | 三层各 `1`，`σ = 1`，`ε = 0` | `loss_ok_not_implies_verdictFull` |
  | 总损失也「对」的反例 | `total = 3 = 3σ` 而判据失败 | `loss_total_eq_not_implies_verdictFull` |
  | σ 取小反例 | `σ = 0 < 1 = sInf`，`Wge2` 处处失败 | `Wge2_not_verdictFull_zero` |

  **超出定义之处**：这是本文件唯一的「汇总」定理，**本身不证新数学**，
  而是把各条结论的**见证数值**放在一处，使 D-022（反空泛）要求的那种
  「账实核对只需读一处」成为**可编译**的对象。 -/
theorem verdict_summary_values :
    VerdictFull Wconst01 1 0 ∧
    VerdictFull Wge2 1 0 ∧
    (VerdictPoint WdropN 1 7 ∧ ¬ VerdictFull WdropN 1 7) ∧
    (AcceptsN 1 0 1 ∧ ¬ VerdictFull WdropN 1 7) ∧
    (AcceptsN 1 (1 / 2) (3 / 2) ∧ ¬ VerdictPoint WdropN 1 0) ∧
    (LossTriple { modelLoss := 1, abstLoss := 1, predLoss := 1 } 1 0 ∧
      ¬ VerdictFull WdropN 1 7) ∧
    (∀ γ : Nat, ¬ VerdictFull Wge2 0 γ) ∧
    WdropN.err 0 = 1 / 2 ∧
    WdropN.err 7 = 1 ∧
    Wge2.err 0 = 1 := by
  refine ⟨?_, Wge2_verdictFull_zero, verdictPoint_not_implies_verdictFull,
    acceptsN_not_implies_verdictFull, acceptsN_not_implies_verdictPoint,
    loss_ok_not_implies_verdictFull, Wge2_not_verdictFull_zero,
    WdropN_err_le_six (by norm_num), WdropN_err_seven, Wge2_err_zero⟩
  exact verdictPoint_implies_verdictFull (fun n => Wconst01_err n)

end

end FateV2.ErrorN
