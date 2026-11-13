import FateWorld.Legacy.WorldModel

/-! ===========================================================================
  `Fate.ResidualLoop` —— **残差回写闭环**（P2-1）

  ## 本文件要解决的问题（报告指出的缺陷）

  报告：`Fate/MainLoop.lean` 的 `step`
  （签名 `InfoLevel → NoiseScale → ℝ → LoopState → LoopState`）
  **不读状态参数**（其值域是 `LoopState`，输入只有 `info` / `noise` / `margin`），因此：

  - **不读残差** $r_t = x_t - \hat x_t$；
  - **不写 θ**（`step` 的值域根本不是 `Θ.Carrier`）。

  ⟹ 第 `t+1` 步的参数 `θ` 与第 `t` 步的预测误差**毫无关系**，
  即「闭环」在类型层根本没有闭合。

  ## 本文件做什么（一句话）

  定义一个**真正消费残差**的更新算子
  $$\mathrm{writeBack} : \mathrm{Residual}\ X \to Θ \to Θ,$$
  并证明两条基本性质：

  | 定理 | 内容 | 语义 |
  |---|---|---|
  | `writeBack_zero` | $r = 0 \Rightarrow \mathrm{writeBack}\, r\, θ = θ$ | **正确性判据**：无误差 ⟹ 不动 |
  | `writeBack_ne` | $r \ne 0 \Rightarrow \mathrm{writeBack}\, r\, θ \ne θ$ | **非平凡性**：有误差 ⟹ 必动 |

  ## ⚠ 诚实边界（必须写清，不得含糊）

  **1. 本文件不实现「学习率取何值」的算法。**
  `writeBack` 带一个**显式**的步长参数 `η` 与一个方向映射 `φ`，
  二者**都是输入**，不是本文件的结论
  （对应纪律「凡规格未给出结构的位，做成参数、不填数」）。

  **2. 两条性质各自需要一条**真前提**，本文件证明它们**不可去掉**：**

  | 定理 | 所需前提 | 去掉后为假 |
  |---|---|---|
  | `writeBack_zero` | `φ` 满足 `φ 0 = 0` | `phi_zero_needed` ✅ |
  | `writeBack_ne` | `η ≠ 0`、`φ r ≠ 0`、`NoZeroDivisors` | `phi_zero_direction_kills_nontrivial` ✅ |

  **⭐ 故本文件**不**声称「任何 `ThetaSpace` 上非平凡性自动成立」**：
  反例 `nonTrivial_needs_readsResidual`（参数空间无表达力）见 §4.2。

  **3. 残差的两位来源：**
  - $x_t$（观测）：直接给出 `X.Carrier`（`residual` 的第一个参数）；
  - $\hat x_t$（预测）：`Fate.WorldModel.WorldModel.f` 的一步
    `W.f x u ε θ a`（本文件**复用**既有模拟器，**不重写**它，见 §5）。

  ## 结构

  | 节 | 内容 |
  |---|---|
  | §1 | 残差 $r_t$ 的定义（`Residual`、`residual`、`residual_eq_zero_iff`） |
  | §2 | 更新算子 `writeBack`（**真正读 `r`、真正写 `θ`**） |
  | §3 | ⭐ **正确性**：`r = 0 ⟹ θ` 不变（+ 前提必要性） |
  | §4 | ⭐⭐ **非平凡性**：`r ≠ 0 ⟹ θ` 改变（+ 前提必要性 + 反例） |
  | §5 | ⭐⭐⭐ **闭环接线**：从 `WorldModel` 的一步预测取出 `r`，再接回 `θ` |

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`；**本文件只读 `Fate/`，不动它**。
  =========================================================================== -/

namespace Fate
namespace ResidualLoop

universe u

/-! ===========================================================================
    §1  残差 $r_t := x_t - \hat x_t$
    =========================================================================== -/

/-- ⭐ **残差的载体**（报告第 1 项）。

$$r_t := x_t - \hat x_t \in \mathrm{Residual}\ X .$$

**⚠ 为什么必须要求 `AddCommGroup X.Carrier`**：
「$x_t - \hat x_t$」蕴含两个算术前提 ——（i）两个状态**可相减**；
（ii）有**零元**（否则「残差为零」无意义）。`StateSpace`（拓扑 + 可测）
本身**不提供**任何一条。故本文件**显式**把加法群结构作为参数，
而**不**把它塞进 `StateSpace`（那会改动既有签名，违反加法式纪律）。

**标签**：[定义性约定]（本文件补定项，非规格原文）。 -/
abbrev Residual (X : StateSpace) [AddCommGroup X.Carrier] : Type u := X.Carrier

/-- ⭐⭐ **残差的定义**：`r_t = x_t - x̂_t`。

$$\mathrm{residual}\ x\ \hat x := x - \hat x .$$

**这是「残差 $r_t := x_t - \hat x_t$」的逐字形式化**（报告第 1 项）。

**标签**：[定义性约定]。 -/
def residual {X : StateSpace} [AddCommGroup X.Carrier]
    (x xhat : X.Carrier) : Residual X :=
  x - xhat

/-- ⭐ **`residual` 展开为减法的显式等式**（供下游避免展开 `def`）。 -/
theorem residual_def {X : StateSpace} [AddCommGroup X.Carrier]
    (x xhat : X.Carrier) : residual x xhat = x - xhat := rfl

/-- ⭐⭐ **残差为零 ⟺ 观测 = 预测**。

$$\bigl(\mathrm{residual}\ x\ \hat x = 0\bigr) \iff x = \hat x .$$

**这是「残差为零」的语义判据**，也是 §3 正确性定理的主要输入。 -/
theorem residual_eq_zero_iff {X : StateSpace} [AddCommGroup X.Carrier]
    (x xhat : X.Carrier) :
    residual x xhat = 0 ↔ x = xhat := by
  simp [residual, sub_eq_zero]

/-- ⭐ **残差非零 ⟺ 观测 ≠ 预测**（`residual_eq_zero_iff` 的否命题形式）。 -/
theorem residual_ne_zero_iff {X : StateSpace} [AddCommGroup X.Carrier]
    (x xhat : X.Carrier) :
    residual x xhat ≠ 0 ↔ x ≠ xhat :=
  not_congr (residual_eq_zero_iff x xhat)

/-! ===========================================================================
    §2  更新算子 `writeBack`：**真正读残差，真正写 θ**

    报告要求的第 2 项：`step : Residual → Θ → Θ`。

    ## 设计（为什么是这个形状）

    $$\mathrm{writeBack}\ \eta\ \varphi\ r\ θ := θ + \eta \bullet \varphi(r)$$

    | 位 | 名 | 类型 | 作用 |
    |---|---|---|---|
    | `η` | 步长 | `Θ.Carrier` | **参数**（不填数） |
    | `φ` | 残差 → 参数方向 | `X.Carrier →+ Θ.Carrier` | **参数**（结构映射） |
    | `r` | 残差 | `Residual X` | ⭐ **被读**（出现在结果中） |
    | `θ` | 当前参数 | `Θ.Carrier` | ⭐ **被写**（也在结果中） |

    ## ⭐ 与 `MainLoop.step` 的本质区别（这是修复的**检验点**）

    | | `MainLoop.step` | 本文件 `writeBack` |
    |---|---|---|
    | 输入含残差？ | ❌ 无 | ✅ `r : Residual X` |
    | 输出是 θ？ | ❌ `LoopState` | ✅ `Θ.Carrier` |
    | 换 `r` 会改结果？ | （无 `r` 可换） | ✅ §4 `writeBack_ne` |

    ## ⚠ 为什么 `φ` 取 `AddMonoidHom` 而非任意函数

    因为 §3 的正确性判据需要 `φ 0 = 0`。
    取 `AddMonoidHom` 使该条件是**结构免费给的**（`map_zero`），
    从而把「残差为零 ⟹ 不动」变成**定义性事实**而非额外假设。
    §3.2 证明：放弃该结构（退回任意函数）则命题为假。

    ## ⚠ 为什么 `Θ.Carrier` 取 `Ring`

    需要 `η * φ r` 这个乘法。`AddCommGroup` 只给加法，
    而 §4 的非平凡性（`η ≠ 0` 且 `φ r ≠ 0` ⟹ 积非零）需要乘法 + `NoZeroDivisors`。
    `Ring` 是**容纳这两者的最小标准结构**；它不是本文件的隐藏假设，
    而是**显式**出现在 `writeBack` 的签名里。
    若日后需要非交换情形，须换 `NonUnitalNonAssocRing` 等并**显式登记**。 -/

/-- ⭐⭐⭐ **更新算子**：`θ' = θ + η * φ(r)`。

**⚠ `η` 与 `φ` 都是参数，不是结论**（本文件不声称任何具体步长最优）。 -/
def writeBack {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) :
    Residual X → Θ.Carrier → Θ.Carrier :=
  fun r θ => θ + η * φ r

/-- ⭐⭐⭐ **`writeBack` 的逐位读法**：`θ' = θ + η * φ(r)`（定义性展开）。 -/
theorem writeBack_apply {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) (r : Residual X)
    (θ : Θ.Carrier) :
    writeBack Θ η φ r θ = θ + η * φ r := rfl

/-- ⭐ **`writeBack` 的签名正是报告要求的 `Residual → Θ → Θ`**。

**本定理是一句「类型声明」**：它把 `Residual X → Θ.Carrier → Θ.Carrier`
写成显式类型，使「残差是输入、θ 是输入也是输出」在编译期可见。
若有人把 `writeBack` 改成不读 `r`（如 `fun _ θ => θ`），
本签名仍成立，但 §4 的 `writeBack_ne` **立即失败** ⟹ 两条定理共同钉住形状。 -/
example {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) :
    Residual X → Θ.Carrier → Θ.Carrier :=
  writeBack Θ η φ

/-! ===========================================================================
    §3  ⭐ **正确性判据**：残差为零 ⟹ θ 不变（报告第 3 项）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **正确性判据（报告第 3 项的核心）**：

$$\mathrm{residual}\ x\ \hat x = 0 \;\Longrightarrow\;
  \mathrm{writeBack}\ \eta\ \varphi\ \bigl(\mathrm{residual}\ x\ \hat x\bigr)\ θ = θ .$$

**读法**：**预测完全命中（$x_t = \hat x_t$）时，参数 `θ` 一点不动。**

**⭐ 这是闭环的「不伤害」判据**：若模型本已正确，回写**不得**引入漂移。
没有它，「无论误差多少都乱动参数」的更新算子同样满足 §4，
但那样的闭环是**破坏性**的。

**⭐ 本定理对任意 `η`、任意可加 `φ` 成立** —— 不需要 `η = 0`，
也不需要 `NoZeroDivisors`。原因：`φ` 是 `AddMonoidHom`，故 `φ 0 = 0`（`map_zero`），
而 `η * 0 = 0` 在 `Ring` 中由 `mul_zero` 给出。 -/
theorem writeBack_zero {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier)
    (x : X.Carrier) (θ : Θ.Carrier) :
    writeBack Θ η φ (residual x x) θ = θ := by
  have hr : residual x x = 0 := (residual_eq_zero_iff x x).mpr rfl
  rw [writeBack_apply, hr, map_zero, mul_zero, add_zero]

/-- ⭐⭐ **正确性判据的纯参数形式**：`writeBack` 在输入 `r = 0` 时是**恒等**。

**这是「`r = 0 ⟹ 不动`」最强也最干净的陈述**（不涉及 `residual` 的具体来源）。 -/
theorem writeBack_zero_eq_id {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) :
    writeBack Θ η φ 0 = id := by
  funext θ
  rw [writeBack_apply, map_zero, mul_zero, add_zero]
  rfl

/-! ### §3.1 正确性判据的**特例**（`η = 0` 的平凡情形，仅作对照）

**⚠ 这不是本文件的主路线**（主路线是上面 `writeBack_zero`），
但它说明：正确性判据**不能**区分「好更新」与「恒等更新」——
一个 `η = 0` 的哑更新算子满足一切「不动」要求（见 §4.1 的 `eta_zero_kills_nontrivial`）。
**⟹ 故必须另有 §4 的非平凡性。** -/
theorem writeBack_zero_of_eta_eq_zero {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (φ : X.Carrier →+ Θ.Carrier) (r : Residual X) (θ : Θ.Carrier) :
    writeBack Θ 0 φ r θ = θ := by
  rw [writeBack_apply, zero_mul, add_zero]

/-! ### §3.2 ⭐ `φ` 过零（`φ 0 = 0`）是**真前提**（D7 必要性）

**上面 §3 之所以无条件成立，是因为 `φ` 被取成 `AddMonoidHom`。**
若退回**任意函数** `ψ : X.Carrier → Θ.Carrier`，则「`r = 0` ⟹ 不动」**为假**。

**⭐ 见证**：取 `ψ ≡ 1`（恒为 `1`）。此时 `r = 0` 仍写 `θ + η * 1 ≠ θ`（若 `η ≠ 0`）。
故「`φ` 过零」是**真前提**，不是装饰。 -/

/-- 一个共享的具体载体：`ℤ`。 -/
abbrev intCarrier : Type := ℤ

/-- 一个具体的状态空间：`ℤ`（离散拓扑 / 离散可测）。 -/
def intStateSpace : StateSpace where
  Carrier := intCarrier
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 一个具体的参数空间：`ℤ`。 -/
def intThetaSpace : ThetaSpace where
  Carrier := intCarrier
  topo := ⊤
  meas := ⊤

instance : Ring intThetaSpace.Carrier := inferInstanceAs (Ring intCarrier)

instance : Ring intStateSpace.Carrier := inferInstanceAs (Ring ℤ)

/-- ⭐⭐⭐ **`φ 0 = 0` 的必要性**：退回任意函数则「零残差 ⟹ 不动」为假。 -/
theorem phi_zero_needed :
    ¬ (∀ (X : StateSpace.{0}) [AddCommGroup X.Carrier] (Θ : ThetaSpace.{0})
        [Ring Θ.Carrier] (η : Θ.Carrier) (ψ : X.Carrier → Θ.Carrier)
        (r : Residual X) (θ : Θ.Carrier),
        r = 0 → θ + η * ψ r = θ) := by
  intro h
  -- `Θ.Carrier = ℤ`、`η = 1`、`ψ ≡ 1`、`θ = 0`：则 `0 + 1 * 1 = 1 ≠ 0`。
  have hz := h (X := intStateSpace) (Θ := intThetaSpace) (η := 1)
    (ψ := fun _ => (1 : ℤ)) (r := 0) (θ := 0) rfl
  simp only [intThetaSpace] at hz
  exact absurd hz (by norm_num : ¬((0 : intCarrier) + 1 * 1 = 0))

/-! ===========================================================================
    §4  ⭐⭐ **非平凡性**：残差非零 ⟹ θ 必改变（报告第 4 项）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **非平凡性（报告第 4 项的核心）**：

若
- `η ≠ 0`（步长非零），
- `Θ.Carrier` 无零因子（`NoZeroDivisors`），
- `φ r ≠ 0`（残差在参数空间上**有方向**），

则
$$\mathrm{writeBack}\ \eta\ \varphi\ r\ θ \ne θ .$$

**⭐ 读法**：**残差一旦非零，参数必被改写 ⟹ 闭环真的闭合。**

**⚠ 三个前提都是必要的，见 §4.1 与 §4.2 的必要性定理。** -/
theorem writeBack_ne {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier] [NoZeroDivisors Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) (r : Residual X)
    (θ : Θ.Carrier) (hη : η ≠ 0) (hφ : φ r ≠ 0) :
    writeBack Θ η φ r θ ≠ θ := by
  rw [writeBack_apply]
  intro hcontra
  have hzero : η * φ r = 0 := by
    have h2 : η * φ r + θ = 0 + θ := by
      rw [zero_add, add_comm (η * φ r) θ]
      exact hcontra
    exact add_right_cancel h2
  exact (mul_ne_zero hη hφ) hzero

/-- ⭐⭐ **非平凡性的「残差侧」形式**：把 `φ r ≠ 0` 归结为 `r ≠ 0` 加 `φ` 单射。

**这是 §4 主定理在「`φ` 是单射」这一常见情形下的读法**：
`φ` 单射 ⟹ `r ≠ 0 ⟹ φ r ≠ φ 0 = 0`。 -/
theorem writeBack_ne_of_injective {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier] [NoZeroDivisors Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) (hinj : Function.Injective φ)
    (r : Residual X) (θ : Θ.Carrier) (hη : η ≠ 0) (hr : r ≠ 0) :
    writeBack Θ η φ r θ ≠ θ := by
  refine writeBack_ne Θ η φ r θ hη ?_
  intro hφ
  exact hr (hinj (by rw [hφ, map_zero]))

/-- ⭐⭐⭐ **非平凡性的**直接**形式（从观测与预测出发）**：

$$x \ne \hat x \;\Longrightarrow\; \mathrm{writeBack}\ \eta\ \varphi\
  \bigl(\mathrm{residual}\ x\ \hat x\bigr)\ θ \ne θ,$$

前提：`η ≠ 0`、`φ` 单射、`NoZeroDivisors`。

**⭐ 这是报告第 4 项「若残差非零，θ 应改变」的**最直接形式化**。** -/
theorem writeBack_ne_of_ne {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier] [NoZeroDivisors Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) (hinj : Function.Injective φ)
    (x xhat : X.Carrier) (θ : Θ.Carrier) (hη : η ≠ 0) (hne : x ≠ xhat) :
    writeBack Θ η φ (residual x xhat) θ ≠ θ := by
  refine writeBack_ne_of_injective Θ η φ hinj _ θ hη ?_
  intro hr
  exact hne ((residual_eq_zero_iff x xhat).mp hr)

/-! ### §4.1 两条前提的**必要性**（D7：去掉即假） -/

/-- ⭐⭐ **`η ≠ 0` 必要**：`η = 0` 时 `writeBack` 退化为**恒等**（无论残差多大）。

**⭐ 这是「哑更新算子」**：它满足 §3 的一切「不动」要求，
且**完全无视残差** —— 正是报告批评的 `MainLoop.step` 缺陷的另一种形态。
**⟹ 没有 `η ≠ 0`，非平凡性就是假的。** -/
theorem eta_zero_kills_nontrivial {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (φ : X.Carrier →+ Θ.Carrier) (r : Residual X) (θ : Θ.Carrier) :
    writeBack Θ 0 φ r θ = θ :=
  writeBack_zero_of_eta_eq_zero Θ φ r θ

/-- ⭐⭐⭐ **`φ r ≠ 0` 必要**：`φ r = 0` 时 `writeBack` 不动 θ（即使 `η ≠ 0`、`r ≠ 0`）。

**⭐ 语义**：`φ r = 0` 表示「残差 `r` 在参数空间上**没有方向**」
（该方向的误差**无法被 θ 表达**）。此时写回**必然**无效果 ——
这不是写法的缺陷，而是**参数空间的表达力边界**。
**⟹ 它必须是显式前件（`ReadsResidual`），而不能假装自动成立。** -/
theorem phi_zero_direction_kills_nontrivial {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) (r : Residual X) (θ : Θ.Carrier)
    (hφ : φ r = 0) :
    writeBack Θ η φ r θ = θ := by
  rw [writeBack_apply, hφ, mul_zero, add_zero]

/-! ### §4.2 ⭐ `ReadsResidual`：非平凡性的**统一判据**（非「假设清单」） -/

/-- ⭐⭐⭐ **`ReadsResidual`**：参数空间**感受得到**残差。

$$\mathrm{ReadsResidual}\ \eta\ \varphi \iff
  \forall r \ne 0,\ \eta * \varphi r \ne 0 .$$

**⭐ 这是 §4 的**唯一**非平凡性判据**（`η ≠ 0`、`NoZeroDivisors`、`φ r ≠ 0`
三者合并后的**语义**）。把它单列的目的：

1. 使「参数空间是否有表达力」成为**一个可陈述的名称**，而非散落的三个前提；
2. 它是可**检验**的（§4.3 给出一个满足它的具体实例，§4.4 给出反例）。 -/
def ReadsResidual {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) : Prop :=
  ∀ r : Residual X, r ≠ 0 → η * φ r ≠ 0

/-- ⭐⭐⭐ **主定理（统一形式）**：`ReadsResidual` ⟹ 非零残差必改 θ。

**这是 §4 的最终形态**，也是本文件对报告第 4 项的**完整回答**。 -/
theorem writeBack_ne_of_readsResidual {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) (hR : ReadsResidual Θ η φ)
    (r : Residual X) (θ : Θ.Carrier) (hr : r ≠ 0) :
    writeBack Θ η φ r θ ≠ θ := by
  rw [writeBack_apply]
  intro hcontra
  have hzero : η * φ r = 0 := by
    have h2 : η * φ r + θ = 0 + θ := by
      rw [zero_add, add_comm (η * φ r) θ]
      exact hcontra
    exact add_right_cancel h2
  exact hR r hr hzero

/-- ⭐ **`NoZeroDivisors` + `η ≠ 0` + `φ` 单射 ⟹ `ReadsResidual`**（充分条件）。 -/
theorem readsResidual_of_injective {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier] [NoZeroDivisors Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) (hinj : Function.Injective φ)
    (hη : η ≠ 0) :
    ReadsResidual Θ η φ := by
  intro r hr
  exact mul_ne_zero hη (by
    intro hφ
    exact hr (hinj (by rw [hφ, map_zero])))

/-! ### §4.3 ⭐ **具体实例：`ReadsResidual` 可被满足**（非空真）

**⚠ §4.1 只说明「不能省」；本节说明「不是不可满足」——
否则 §4 的主定理就是**空真**的。**

**具体实例**：`Θ = ℤ`，`η = 1`，`φ = id`。 -/

/-- ⭐⭐⭐ **`ℤ` 上 `ReadsResidual` 成立**（`η = 1`，`φ = id`）。 -/
theorem realThetaReads :
    ReadsResidual (X := intStateSpace) intThetaSpace (1 : intThetaSpace.Carrier)
      (AddMonoidHom.id ℤ) := by
  intro r hr
  rw [one_mul]
  exact hr

/-- ⭐⭐⭐ **实例上的非平凡性**（把 `realThetaReads` 接到主定理）。

**⭐ 读法**：`Θ = ℤ`、`η = 1`、`φ = id` 时，**残差非零 ⟹ θ 必改**。
这是报告第 4 项在**一个具体参数空间**上的完整兑现。 -/
theorem writeBack_ne_concrete (r : Residual intStateSpace)
    (θ : intThetaSpace.Carrier) (hr : r ≠ 0) :
    writeBack intThetaSpace (1 : intThetaSpace.Carrier)
      (AddMonoidHom.id intThetaSpace.Carrier) r θ ≠ θ :=
  writeBack_ne_of_readsResidual (X := intStateSpace) intThetaSpace
    (1 : intThetaSpace.Carrier) (AddMonoidHom.id intThetaSpace.Carrier)
    realThetaReads r θ hr

/-! ### §4.4 ⭐ 反例：参数空间**无表达力**时非平凡性**不可能**（`ReadsResidual` 不能省）

**构造**：`Θ.Carrier = Unit`（有 `Ring`，且 `NoZeroDivisors`）。
此时 `writeBack` 的值恒为 `()`，故**任何**残差都不动 θ。

**⭐ 语义**：若参数空间「感知不到残差」，闭环**在数学上不可能**闭合。
**⟹ `ReadsResidual` 不是可省的假设。** -/

/-- `Unit` 是 `NoZeroDivisors`（`Subsingleton` 使它免费）。 -/
instance : NoZeroDivisors Unit :=
  ⟨fun _ => Or.inl (Subsingleton.elim _ 0)⟩

/-- 一个「无表达力」的参数空间：`Unit`。 -/
def unitThetaSpace : ThetaSpace where
  Carrier := Unit
  topo := ⊤
  meas := ⊤

instance : Ring unitThetaSpace.Carrier := inferInstanceAs (Ring Unit)

instance : Subsingleton unitThetaSpace.Carrier :=
  inferInstanceAs (Subsingleton Unit)

/-- ⭐⭐⭐ **反例**：单点参数空间上「非零残差 ⟹ 必动」**为假**。 -/
theorem nonTrivial_needs_readsResidual :
    ¬ (∀ (X : StateSpace.{0}) [AddCommGroup X.Carrier] (Θ : ThetaSpace.{0})
        [Ring Θ.Carrier] [NoZeroDivisors Θ.Carrier]
        (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) (r : Residual X)
        (θ : Θ.Carrier), r ≠ 0 → writeBack Θ η φ r θ ≠ θ) := by
  intro h
  have hne := h (X := intStateSpace) (Θ := unitThetaSpace) (η := 0)
    (φ := 0) (r := 1) (θ := ()) (by norm_num : (1 : ℤ) ≠ 0)
  exact hne (Subsingleton.elim _ _)

/-! ===========================================================================
    §5  ⭐⭐⭐ **闭环的接线**：从 `WorldModel` 的一步预测取出残差，接回 θ

    ## 这一步做什么

    §1–§4 的对象是抽象的 `x` / `x̂`。本节把它们**接到既有的**
    `Fate.WorldModel.WorldModel` 上：

    $$\hat x_t := W.f\, x_t\, u_t\, \varepsilon_t\, θ\, a_t
      \quad(\text{即} \ W.\mathrm{sim} \ \text{的一步}),$$
    $$r_t := x_t - \hat x_t,$$
    $$θ_{t+1} := \mathrm{writeBack}\ \eta\ \varphi\ r_t\ θ_t .$$

    **⟹ 这是「残差回写闭环」的完整一步。**

    ## ⚠ 诚实边界

    本节的 `θ_{t+1}` 依赖 `η` / `φ`（**参数，不是结论**）。
    本文件**不**声称该闭环**收敛**（那需要额外的收敛判据，
    如 `Fate/RealConvergence.lean` 的框架；本文件**不**引用它，
    以免把未证内容伪装成已证）。 -/

open Fate.WorldModel in
/-- ⭐⭐⭐ **世界模型的一步预测**（复用既有 `W.sim`，**不重写**递归）。

$$\hat x_t = W.\mathrm{sim}\ (\theta,u,\varepsilon,a)\ (n+1).$$

即 `W.f (W.sim ... n) (u n) (ε n) θ (a n)`（`WorldModel.sim_succ` 的逐字读法）。 -/
noncomputable def predicted (W : WorldModel)
    (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (ε : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) (n : ℕ) :
    W.frame.X.Carrier :=
  W.sim θ u ε a (n + 1)

/-- ⭐⭐ **`predicted` 就是 `f` 的一步**（`WorldModel.sim_succ` 的直接转录）。 -/
theorem predicted_eq (W : WorldModel)
    (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (ε : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) (n : ℕ) :
    predicted W θ u ε a n = W.f (W.sim θ u ε a n) (u n) (ε n) θ (a n) :=
  WorldModel.sim_succ W θ u ε a n

/-- ⭐⭐⭐ **闭环一步（残差回写）**：`θ_{t+1} = writeBack η φ r_t θ_t`，
其中 `r_t = x_t - x̂_t`，`x̂_t` 由 `WorldModel` 的一步预测给出。

**⚠ 只对「框架状态空间带加法群、参数空间带环」的世界模型可定义**
（因为要做减法与标量乘法；见 §1 / §2 的设计理由）。 -/
noncomputable def closedLoopStep (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (u : ℕ → W.frame.U.Carrier) (ε : ℕ → W.frame.Ν.Carrier)
    (a : ℕ → W.frame.Act.Carrier) (n : ℕ) :
    W.frame.X.Carrier → W.frame.Θ.Carrier → W.frame.Θ.Carrier :=
  fun (x : W.frame.X.Carrier) (θ : W.frame.Θ.Carrier) =>
    writeBack W.frame.Θ η φ (residual x (predicted W θ u ε a n)) θ

/-- ⭐⭐⭐⭐ **闭环的正确性（在 `WorldModel` 上）**：

若观测 `x_t` **恰等于** 一步预测 `x̂_t`，则闭环一步**不动** `θ`。

**⭐ 这是 §3 在真实世界模型上的落地**：把 `writeBack_zero` 与
`predicted` 的定义接起来，**无需任何关于 `W` 的额外假设**
（除加法群 / 环结构，那是残差与步长的定义条件）。 -/
theorem closedLoopStep_fixed (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (u : ℕ → W.frame.U.Carrier) (ε : ℕ → W.frame.Ν.Carrier)
    (a : ℕ → W.frame.Act.Carrier) (n : ℕ) (θ : W.frame.Θ.Carrier) :
    closedLoopStep W η φ u ε a n (predicted W θ u ε a n) θ = θ :=
  writeBack_zero W.frame.Θ η φ _ θ

/-- ⭐⭐⭐⭐ **闭环的非平凡性（在 `WorldModel` 上）**：

若观测 `x_t` **不等于**一步预测 `x̂_t`，且 `ReadsResidual` 成立，
则闭环一步**必改** `θ`。

**⭐ 这是 §4 在真实世界模型上的落地** —— 即报告第 4 项要求的完整兑现：
**残差非零 ⟹ `θ` 改变**，且 `θ` 是 `W.frame.Θ.Carrier` 中的真实参数。 -/
theorem closedLoopStep_moves (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (hR : ReadsResidual W.frame.Θ η φ)
    (u : ℕ → W.frame.U.Carrier) (ε : ℕ → W.frame.Ν.Carrier)
    (a : ℕ → W.frame.Act.Carrier) (n : ℕ) (x : W.frame.X.Carrier)
    (θ : W.frame.Θ.Carrier) (hne : x ≠ predicted W θ u ε a n) :
    closedLoopStep W η φ u ε a n x θ ≠ θ := by
  refine writeBack_ne_of_readsResidual W.frame.Θ η φ hR _ θ ?_
  intro hr
  exact hne ((residual_eq_zero_iff x (predicted W θ u ε a n)).mp hr)

/-! ===========================================================================
    §6  自检清单（本文件的验收点，逐条可编译）
    =========================================================================== -/

/-- **自检 1**：残差的定义式是减法（`r = x - x̂`）。 -/
example {X : StateSpace} [AddCommGroup X.Carrier] (x xhat : X.Carrier) :
    residual x xhat = x - xhat := rfl

/-- **自检 2**：`writeBack` 的类型是 `Residual → Θ → Θ`。 -/
example {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) :
    Residual X → Θ.Carrier → Θ.Carrier := writeBack Θ η φ

/-- **自检 3**：零残差 ⟹ 恒等（正确性）。 -/
example {X : StateSpace} [AddCommGroup X.Carrier]
    (Θ : ThetaSpace) [Ring Θ.Carrier]
    (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier) :
    writeBack Θ η φ 0 = id := writeBack_zero_eq_id Θ η φ

/-- **自检 4**：非零残差 ⟹ 必动（非平凡性，`Θ = ℤ` 具体实例）。 -/
example (r : Residual intStateSpace) (θ : intThetaSpace.Carrier) (hr : r ≠ 0) :
    writeBack intThetaSpace (1 : intThetaSpace.Carrier)
      (AddMonoidHom.id intThetaSpace.Carrier) r θ ≠ θ :=
  writeBack_ne_concrete r θ hr

/-- **自检 5**：两条判据**同时**成立且**不冲突**（同一 `writeBack` 上）。 -/
example : (∀ (X : StateSpace) [AddCommGroup X.Carrier] (Θ : ThetaSpace)
      [Ring Θ.Carrier] (η : Θ.Carrier) (φ : X.Carrier →+ Θ.Carrier)
      (x : X.Carrier) (θ : Θ.Carrier), writeBack Θ η φ (residual x x) θ = θ)
    ∧ (∀ (r : Residual intStateSpace) (θ : intThetaSpace.Carrier) ,
        r ≠ 0 → writeBack intThetaSpace (1 : intThetaSpace.Carrier)
          (AddMonoidHom.id intThetaSpace.Carrier) r θ ≠ θ) :=
  ⟨fun X _ Θ _ η φ x θ => writeBack_zero Θ η φ x θ,
   fun r θ hr => writeBack_ne_concrete r θ hr⟩

end ResidualLoop
end Fate
