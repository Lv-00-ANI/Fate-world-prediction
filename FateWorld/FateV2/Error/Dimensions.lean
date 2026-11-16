import Mathlib
import FateWorld.FateV2.Error.FitBoundary

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/Dimensions.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 6 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Modeling
/-
  量纲：把「σ 与 ε 同量纲」做成类型层约束（对应论文 §12.1）

  判据写作 err γ = σ ∧ ∀ γ', σ ≤ err γ'，其中 err γ 与 σ 都是 ℝ。但 ℝ 不携带量纲信息：
  若 err γ 的单位是距离、σ 的单位是标准差，等式在 Lean 里照样可写可证，尽管它在物理上
  无意义。本模块把量纲做成类型层的约束，使「量纲不同的两个量相减」直接类型错误，无需
  人工检查。Mathlib 没有量纲系统，故给出一个最小自足模型：

    量纲 = 指数向量 Fin n → ℤ（Dim n），乘法 = 逐分量相加；
    带量纲的量 Qty n := { v : ℝ, d : Dim n }；
    加法 / 减法 / 比较必须显式携带 d₁ = d₂ 的证明。

  §1  Dim 与 Qty 及其运算；
  §2  带量纲的判据：把「同量纲」写成显式前件；
  §3  判据成立 ⟹ σ 的量纲等于误差曲线的量纲；量纲不一致 ⟹ 判据不可满足；
  §4  新旧判据只差一条显式等式。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  注：本模块没有改造边界主模块的判据——那会波及数百处引用与十余个文件，属架构级改动。
     这里提供的是可用的工具与桥接定理，证明「若要改造，做法如此，且代价可精确度量」。
     量纲的具体选取是建模选择：给出长 / 时二维的默认模型并对一般维数给出通用形式，但
     哪几维、各自指数是多少属领域约定，不是定理。本模块不声称「原判据是错的」，只说明
     原判据缺少一道可在类型层执行的检查，而这道检查的缺失可修补。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error.Dimensions

noncomputable section

/-! ===========================================================================
  §1  量纲：指数向量 `Fin n → ℤ`
  =========================================================================== -/

/-- **一般量纲**：`n` 个基本单位的指数向量。
    例如 `n = 2` 时可取 `0 ↦ 长度 L`、`1 ↦ 时间 T`。 -/
def Dim (n : ℕ) := Fin n → ℤ

namespace Dim

/-- **量纲乘法** = 指数相加。 -/
def mul {n : ℕ} (a b : Dim n) : Dim n := fun i => a i + b i

/-- **无量纲** = 全零指数。 -/
def one {n : ℕ} : Dim n := fun _ => 0

theorem mul_comm {n : ℕ} (a b : Dim n) : mul a b = mul b a := by
  funext i; simp only [mul]; omega

theorem one_mul {n : ℕ} (a : Dim n) : mul one a = a := by
  funext i; simp only [mul, one]; omega

theorem mul_assoc {n : ℕ} (a b c : Dim n) : mul (mul a b) c = mul a (mul b c) := by
  funext i; simp only [mul]; omega

end Dim

/-! ===========================================================================
  §2  带量纲的量
  =========================================================================== -/

/-- **带量纲的实数量**：一个数值 + 它的量纲。 -/
structure Qty (n : ℕ) where
  v : ℝ
  d : Dim n

namespace Qty

/-- **加法**：**必须**提供 `d₁ = d₂`，否则类型错误。 -/
def add {n : ℕ} (a b : Qty n) (_h : a.d = b.d) : Qty n := ⟨a.v + b.v, a.d⟩

/-- **减法**：同上，量纲必须一致。这是「σ 与 ε 相减」的合法形式。 -/
def sub {n : ℕ} (a b : Qty n) (_h : a.d = b.d) : Qty n := ⟨a.v - b.v, a.d⟩

/-- **乘法**：量纲相乘。 -/
def mul {n : ℕ} (a b : Qty n) : Qty n := ⟨a.v * b.v, Dim.mul a.d b.d⟩

/-- **比较（≤）**：**同样**必须量纲一致。 -/
def le {n : ℕ} (a b : Qty n) (_h : a.d = b.d) : Prop := a.v ≤ b.v

theorem add_d {n : ℕ} (a b : Qty n) (h : a.d = b.d) : (add a b h).d = a.d := rfl

theorem sub_d {n : ℕ} (a b : Qty n) (h : a.d = b.d) : (sub a b h).d = a.d := rfl

theorem le_refl_q {n : ℕ} (a : Qty n) : le a a rfl := le_refl a.v

end Qty

/-! ===========================================================================
  §3  桥接：判据的量纲检查
  =========================================================================== -/

/-- **带量纲的误差剖面**：给 `ErrProfileWeak` 的每个数值配一个量纲。
    `errDim` 是「误差的量纲」，它必须与噪声尺度的量纲**相同**才能在 §3.2 中相减。 -/
structure DimProfile (n : ℕ) where
  W : FateV2.Error.Core.ErrProfileWeak
  /-- 误差曲线的量纲。 -/
  errDim : Dim n

/-- **量纲一致的判据（核心）**：把 `IsFitBoundary` 的 `σ` 与 `E_W` 都放进 `Qty`，
    **要求二者的量纲相等**——这个等式是**前件**，不是默认成立的。

    $$\mathrm{IsFitBoundaryDim}(P,\sigma_d,\gamma) :=
      (\sigma_d = P.\mathrm{errDim}) \wedge
      (P.W.\mathrm{err}(\gamma) = \sigma.v) \wedge
      (\forall\gamma',\ \sigma.v \le P.W.\mathrm{err}(\gamma'))$$ -/
def IsFitBoundaryDim {n : ℕ} (P : DimProfile n) (sigma : Qty n) (gamma : ℝ) : Prop :=
  sigma.d = P.errDim ∧
    P.W.err gamma = sigma.v ∧
    ∀ gamma', sigma.v ≤ P.W.err gamma'

/-- **判据 ⟹ 量纲一致**：若 `IsFitBoundaryDim P sigma γ` 成立，
    则 `sigma` 的量纲**必须等于**误差曲线的量纲。

    这是本文要的结论：**「同量纲」不是需要额外证明的猜测，而是判据成立的必要条件**——
    只不过在原来的 `IsFitBoundary` 里，它因为 `σ : ℝ` 而被**静默省略**了。 -/
theorem dim_consistent_of_boundary {n : ℕ} {P : DimProfile n} {sigma : Qty n} {gamma : ℝ}
    (h : IsFitBoundaryDim P sigma gamma) : sigma.d = P.errDim :=
  h.1

/-- **与原始判据的等价（去掉量纲部分）**：
    `IsFitBoundaryDim P sigma γ` 等价于「量纲一致 ∧ 原判据成立」。

    这把新判据**精确地**写成「原判据 + 一条显式的量纲等式」，
    证明二者**只差这一条**，不多不少。 -/
theorem isFitBoundaryDim_iff {n : ℕ} (P : DimProfile n) (sigma : Qty n) (gamma : ℝ) :
    IsFitBoundaryDim P sigma gamma ↔
      (sigma.d = P.errDim ∧ FateV2.Error.Core.IsFitBoundary P.W sigma.v gamma) := by
  unfold IsFitBoundaryDim FateV2.Error.Core.IsFitBoundary
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩

/-- **量纲不一致则判据无意义（可证形式）**：
    若 `sigma` 与误差曲线量纲不同，则 **不存在** `gamma` 使 `IsFitBoundaryDim` 成立。

    这精确刻画了「量纲不同时，判据不是一个可满足的谓词」。 -/
theorem no_boundary_of_dim_mismatch {n : ℕ} (P : DimProfile n) (sigma : Qty n)
    (h : sigma.d ≠ P.errDim) : ∀ gamma, ¬ IsFitBoundaryDim P sigma gamma := by
  intro gamma hb
  exact h (dim_consistent_of_boundary hb)

/-! ===========================================================================
  §4  ⚠ 未做：改造 `FitBoundary.lean` 本身
  =========================================================================== -/

/-
本文件**没有**把 `FitBoundary.lean` 里的 `σ : ℝ` 改成 `Qty n`，原因有二：

1. **波及面**：`IsFitBoundary` 有 269 处引用、跨 10 个文件。
   改造会使全部下游（`Decomposition`、`InfoCompleteness`、
   `FitBoundaryLowerBound`、`SigmaFromAIC` 等）全部需要适配。
2. **语义未定**：量纲的**具体选取**（哪几维、指数多少）属领域约定；
   若选错，改造后所有定理仍然「编译通过」，但语义可能更糟。
   ⟹ 须先确定量纲模型，再改造；而这一步是建模决策，不是定理。

**本文件提供的过渡方案**：
- 新判据 `IsFitBoundaryDim` 与旧判据**只差一条显式等式**（定理 `isFitBoundaryDim_iff`）；
- 因此改造是**机械的**：把每条涉及 `IsFitBoundary` 的定理前件里加一条 `sigma.d = P.errDim` 即可。
- 定理 `no_boundary_of_dim_mismatch` 说明：**量纲不一致时，判据不可满足**，
  故这不是「多此一举的检查」，而是**判据良定义性的必要条件**。
-/

end

end FateV2.Error.Dimensions
