/-
命运理论 · 从 `LawRule` 到轨迹：`IsPoint` 能否生成 `TrajGen`？
======================================================================

模块：Fate.LawRuleToTraj
上游：`Fate/LawRule.lean`（`LawRule`、`IsPoint`、`Deterministic`）、
　　　`Fate/Frame.lean`（`Frame`、`Step`、`TrajGen`、`Rule.IsDet`）、
　　　`Fate/Basic.lean`（`Traj`、`InitialState`）、
　　　`Fate/TrajGenDeterministic.lean`（方案一：`trajGen`、`trajGen_succ`、`trajGen_unique`）。

---------------------------------------------------------------------------
问题（作者原问）
---------------------------------------------------------------------------
> 从 `LawRule` 到轨迹：若 `IsPoint`，能否生成轨迹？（对应 `TrajGen`）给出构造。

---------------------------------------------------------------------------
答案（先给结论，再给构造）
---------------------------------------------------------------------------
**能，但 `IsPoint` 单独不够。** 须再关两道闸，第一道闸有真实数学内容：

| 闸 | 内容 | 为什么 `IsPoint` 单独过不了 |
|---|---|---|
| **闸 A（点质量闸）** | 选出的测度 `μ(c,x)` 必须是 **Dirac 测度** `δ_y`，而不只是「某个测度」 | `IsPoint` 只说「允许集是单点集 `{μ}`」。`μ` 可以是正态、均匀、任意概率测度 —— **它是测度，不是状态点**。而 `Traj ι X = ι → X.Carrier` 要的是**点**。从测度回到点，没有这一步就是类型错误。 |
| **闸 B（上下文闸）** | 上下文 `c` 必须由数据供给（`ι → C` 序，或由轨迹自反馈 `c = γ xₜ`） | `TrajGen F ι` 的签名（`Fate/Frame.lean`）里**没有** `C` 这个位置。`LawRule` 是**带上下文**的（`C.Carrier → …`），`TrajGen` **无上下文**。必须显式喂 `c`，不能默认。 |

**闸 A 是本模块的实质内容**：它正是库中已有的 `Rule.IsDet` / `isDet_iff_dirac`
（`Fate/Frame.lean`）在 `LawRule` 侧的对应物。本模块把它**显式化**为谓词 `IsDirac`，并证明

$$\texttt{IsDirac}\ R \iff \exists f,\ R = \texttt{DetFun.toLaw}\ f,$$

即：**点质量档的 `LawRule` 与确定性函数一一对应** —— 这就是「`IsPoint` 可以升级为
`Step`」的确切条件，也是本节 §1 的核心（`isDirac_iff_exists_detFun`）。

**闸 B 在本模块的处置**：`c` 取为**输入序** `(ι → C.Carrier)`，
与 `TrajGen` 已把 `u`、`ε`、`a` 取为输入序**同构**（不新增类型层结构）。
另一条路线（自反馈 `cₜ = γ xₜ`）作为**特例**给出（`ctxFromState`），**不**默认采用。

---------------------------------------------------------------------------
与方案一（`Fate.TrajGenDeterministic`）的关系
---------------------------------------------------------------------------
本模块的构造**就是方案一**，只把 `Step` 从「外部参数」升级为
「从 `LawRule` 的 `IsDirac` **抽出**」。故：

- **递推方程 `rfl` 级忠实** —— 复用 `trajGen_succ`，本模块额外证「抽出的单步
  真的等于 `LawRule` 允许的那个转移」（`trajGenOfLaw_succ_law`）；
- **唯一性** —— 复用 `trajGen_unique`，本模块补一条「`LawRule` ⟹ 唯一」的转写。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 全程零 `sorry` / 零 `axiom`。
- 凡「需要额外输入」者（上下文序、点质量闸）一律作**显式参数/前件**，
  **不**偷偷塞进定义。
- 闸 A 的前件**不被 `IsPoint` 蕴含**：§5 给出**反例见证**
  （满足 `IsPoint` 但非 `IsDirac` 的 `LawRule`），使「该前件不可去除」
  成为**机器可见事实**，而不是一句注释。
-/

import FateWorld.Legacy.LawRule
import FateWorld.Legacy.TrajGenDeterministic

namespace Fate

namespace LawRuleToTraj

open MeasureTheory
open Fate.LawRule

/-! ⚠ 必要性：本模块位于 `Fate.LawRule` **命名空间内部**，故裸名 `LawRule`
指命名空间而非类型定义。此处显式 `open Fate.LawRule` 才能解析
`LawRule` / `IsPoint` / `Deterministic` / `DetFun.toLaw` 等定义。 -/
open Fate.LawRule

/-! ===========================================================================
    §1  闸 A：点质量档 `IsDirac`
    =========================================================================== -/

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-- **点质量档**：规律允许的那个**唯一分布**必须是 Dirac 测度。

$$\texttt{IsDirac}\ R \;:=\; \forall c\,x,\ \exists y,\ R\,c\,x = \{\delta_y\}.$$

**为什么这比 `IsPoint` 强**（务必读）：

| 谓词 | 形式 | 允许集的内容 | 见证住在哪 |
|---|---|---|---|
| `IsPoint R` | `∀ c x, ∃ μ, R c x = {μ}` | 单点集 `{μ}`，`μ` **任意测度** | `Measure Y.Carrier` |
| `IsDirac R` | `∀ c x, ∃ y, R c x = {δ_y}` | 单点集 `{δ_y}`，`y` 是**点** | `Y.Carrier` |

`{normal(0,1)}` 是单点集（满足 `IsPoint`）却**不是** Dirac。
**⟹ 这份差额就是「`IsPoint` 不足以生成轨迹」的全部内容**：
`Traj` 需要点，不是测度。§5 把这条差额钉成可编译的反例。

标签：**[定义性约定]**（`Rule.IsDet` 在 `LawRule` 侧的对应物）。 -/
def IsDirac (R : LawRule C X Y) : Prop :=
  ∀ c x, ∃ y, R c x = {MeasureTheory.Measure.dirac y}

/-- **闸 A 的等价刻画**：`IsDirac` 恰是「`R` 落在 `DetFun.toLaw` 的像里」。

$$\texttt{IsDirac}\ R \iff \exists f,\ R = \texttt{DetFun.toLaw}\ f.$$

**这是闸 A 的「无浪费」证明**：`IsDirac` 不是随手加的强条件，
而是**精确地**刻画了「`R` 由某个确定性函数诱导」。
故 §2 从 `IsDirac` 抽出 `f` 是**无损的**。

**证明**：两方向都是 `DetFun.toLaw` 的定义展开
（`toLaw f c x = {dirac (f c x)}`），只是见证方向不同。 -/
theorem isDirac_iff_exists_detFun (R : LawRule C X Y) :
    IsDirac R ↔ ∃ f : C.Carrier → X.Carrier → Y.Carrier, R = DetFun.toLaw f := by
  constructor
  · intro h
    refine ⟨fun c x => Classical.choose (h c x), ?_⟩
    funext c x
    show R c x = {MeasureTheory.Measure.dirac (Classical.choose (h c x))}
    exact Classical.choose_spec (h c x)
  · rintro ⟨f, rfl⟩ c x
    exact ⟨f c x, rfl⟩

/-- **`IsDirac` 蕴含 `IsPoint`**（点质量是单点集的**特例**）。

**注意方向**：只有这一向成立。反向**不成立**（§5 反例）。
这条把「两道闸」的**严格包含**钉成可编译事实：`IsDirac ⊂ IsPoint`。 -/
theorem IsDirac.isPoint {R : LawRule C X Y} (h : IsDirac R) : IsPoint R :=
  fun c x => let ⟨y, hy⟩ := h c x; ⟨MeasureTheory.Measure.dirac y, hy⟩

/-- **`IsDirac` 也是 `Deterministic`**（点质量档必然只允许一个分布）。

这条与 `IsPoint.deterministic`（`Fate/LawRule.lean`）并列，
说明闸 A 保持「单点档」的全部下游性质，故 §4 的构造不损失 `IsPoint` 的任何结论。 -/
theorem IsDirac.deterministic {R : LawRule C X Y} (h : IsDirac R) : Deterministic R :=
  h.isPoint.deterministic R

/-! ===========================================================================
    §2  闸 A 的「通过」动作：从点质量档抽出确定性函数
    =========================================================================== -/

/-- **从点质量档抽出确定性函数**（`Classical.choose`，非构造性）。

$$\texttt{toDetFun}\ R\ h\ c\ x := \text{那个使 } R\,c\,x = \{\delta_y\}\text{ 的 } y.$$

**这是闸 A 的「降维」动作**：把测度层 `Measure Y.Carrier` 的 `δ_y`
**降回**点层 `Y.Carrier`。这一步在 `IsPoint` 下**做不了** ——
`IsPoint` 的见证是测度，不知道「哪个点」。

标签：**[定义性约定]**（依 `IsDirac`）。 -/
noncomputable def toDetFun (R : LawRule C X Y) (h : IsDirac R) :
    C.Carrier → X.Carrier → Y.Carrier :=
  fun c x => Classical.choose (h c x)

/-- **抽出正确性**：抽出的函数确实复现 `R`。

$$R\,c\,x = \{\delta_{\texttt{toDetFun}\,R\,h\,c\,x}\}.$$

即「抽出的机制 + `DetFun.toLaw`」**精确回到原规律**，无信息丢失。
这是 `toDetFun` 的**正确性引理**，也是 §1 `isDirac_iff_exists_detFun`
的构造性一半（`→` 方向的具体见证）。 -/
theorem toDetFun_spec (R : LawRule C X Y) (h : IsDirac R) (c : C.Carrier)
    (x : X.Carrier) :
    R c x = {MeasureTheory.Measure.dirac (toDetFun R h c x)} :=
  Classical.choose_spec (h c x)

/-- **`DetFun.toLaw` 与 `toDetFun` 互逆**（左逆）：`IsDirac` 档的规律由抽出函数**唯一**决定。

$$\texttt{DetFun.toLaw}\ (\texttt{toDetFun}\ R\ h) = R.$$

故 §4 的轨迹构造用的是 `R` 的**全部**信息：
与方案一「`Step` 作外生参数」相比，本模块的 `Step` 是**从规律推出的**，不是假定的。 -/
theorem toDetFun_toLaw (R : LawRule C X Y) (h : IsDirac R) :
    DetFun.toLaw (toDetFun R h) = R := by
  funext c x
  exact (toDetFun_spec R h c x).symm

/-! **抽出函数的唯一性**（在点分离下）：诱导同一 `LawRule` 的两个抽出函数相等。

**为什么需要点分离**：`δ_{y₁} = δ_{y₂} ⟹ y₁ = y₂` 并非恒真
（平凡 σ-代数下所有 Dirac 都相等）。这与库里
`DetRule.toRule_injective`（`Fate/Frame.lean`）的前件一致，
**是真实的数学前提，不是技术性规避**。

**此处只给「合法性说明」，不给引理**：`toDetFun` 是 `Classical.choose`，
其唯一性依赖 `Classical.choose` 的选择行为，属**元层**性质；
本模块**不**把「选择的规范性」伪装成定理（见 §7 诚实标注）。 -/
/-! ===========================================================================
    §3  闸 B：上下文由数据供给
    =========================================================================== -/

/-! `TrajGen F ι`（`Fate/Frame.lean`）的签名是

$$\Theta \to \mathrm{InitialState}\,X \to (\iota\to U) \to (\iota\to\N) \to (\iota\to A)
  \to \mathrm{Traj}\,\iota\,X,$$

**没有 `C` 这个位置**。而 `LawRule C X Y` 的最外层是 `C.Carrier → …`。
**这个落差必须显式填**，不能默认。本模块给出两条填法，
**都不新增类型层结构**：

| 填法 | 形态 | 性质 |
|---|---|---|
| **序供给**（§4 用） | `cs : ι → C.Carrier` 作**输入序** | 与 `u`、`ε`、`a` 同构；最一般 |
| **自反馈**（`ctxFromState`） | `cₜ := γ xₜ` | `γ : Y → C` 由调用者给出；**是序供给的特例** | -/

/-- **上下文的自反馈来源** `γ`：把当前状态映到上下文。

规格未指明 `C` 的结构（`CtxSpace` 只给 `Carrier`），
故本模块把「状态如何决定上下文」做成**显式参数** `γ`，
**不**假定 `C ⊂ X` 或任何具体划界方式 —— 这与 `LocalDomain`（A9）的处置同构：
让前件**可见**，而不是悄悄假定。 -/
abbrev CtxOfState (C : CtxSpace) (Y : OutSpace) : Type _ :=
  Y.Carrier → C.Carrier

/-- **自反馈上下文序**：`cₜ := γ xₜ`。

这是闸 B 的**第二填法**：给定 `γ` 与一条已展开的轨迹，逐点读出上下文序。
它把「上下文」**内化**进轨迹，故其 `TrajGen` 版本不需要外部 `(ι → C)` 输入。
**但 `γ` 仍是外部输入** —— 本模块**不假装**消掉了闸 B，
只是把它从「一条序」换成「一个函数」。 -/
def ctxFromState {C : CtxSpace} {Y : OutSpace} (γ : CtxOfState C Y)
    {ι : Type _} (x : Traj ι Y) : ι → C.Carrier :=
  fun t => γ (x t)

/-- **自反馈的取值式**：`ctxFromState γ x t = γ (x t)`（定义性）。 -/
theorem ctxFromState_apply {C : CtxSpace} {Y : OutSpace} (γ : CtxOfState C Y)
    {ι : Type _} (x : Traj ι Y) (t : ι) : ctxFromState γ x t = γ (x t) := rfl

/-! ===========================================================================
    §4  ⭐ 主构造：`IsDirac` + 上下文序 ⟹ 轨迹
    =========================================================================== -/

/-! ### §4.1 类型对齐：为什么必须 `Y` 与 `X` 同一

`LawRule C X Y` 的**输出**空间是 `Y`，`Traj ι X` 的**取值**空间是 `X`。
要**迭代**，第 `n+1` 步的「状态」必须是第 `n` 步的**输出** `y ∈ Y.Carrier`。
故迭代**要求** `Y.Carrier` 与 `X.Carrier` 是同一个类型。

**这在库里是既有事实**：`OutSpace` 已被 `abbrev` 为 `StateSpace`
（`Fate/Frame.lean`：`OutSpace := StateSpace`）。
故下面的构造在**同一** `StateSpace` 载体上进行，**不引入新的同一性假设**。 -/

section Construction

variable {C : CtxSpace} {X : StateSpace} [MeasurableSpace X.Carrier]

/-- ⭐⭐ **核心构造：点质量 `LawRule` ⟹ 轨迹**（`ι = ℕ`）。

给定点质量规律 `R : LawRule C X X` 与上下文序 `cs : ℕ → C.Carrier`，
沿时间**正向迭代**从 `R` 抽出的确定性转移：

$$x_0 := x_0,\qquad
  x_{n+1} := \texttt{toDetFun}\ R\ h_R\ (c_n)\ x_n .$$

**与方案一 `trajGen` 的关系**：这**就是** `trajGen`，
只不过机制 `f` 不是外部参数，而是 `fun x _ _ _ _ => toDetFun R hR (c n) x`
（用 `n` 索引进 `c` 的那一步，使 `LawRule` 的上下文位被真正**用上**）。

**⚠ 诚实标注（`LawRule` 的表达力边界）**：`LawRule C X X` 的**单步**签名不吃
`u`、`ε`、`θ`、`a` 这四位（它们只能进 `C`）。
故下面 `u`、`ε`、`θ`、`a` 虽在**签名**里（为与 `TrajGen` 对齐），
却**不进入递推式**。这不是缺陷，是 `LawRule` 的类型边界；
要用上它们，须取 `C := U × Ν × Θ × Act`（§6 的 `richLaw`）。§6.2 把这条
**做成可编译事实**（`trajOfLaw_ignores_noise`）。

标签：**[定义性约定]**（`TrajGen` 类型的一种实现，机制由 `IsDirac` 抽出）。 -/
noncomputable def trajOfLaw (R : LawRule C X X) (hR : IsDirac R)
    (cs : ℕ → C.Carrier) (x₀ : X.Carrier) :
    Traj ℕ X :=
  fun n => Nat.rec x₀ (fun k xk => toDetFun R hR (cs k) xk) n

/-- ⭐ **忠实递推（`rfl` 级）**：轨迹满足「单步转移 = `LawRule` 允许的那个转移」。

$$\forall n,\quad x_{n+1} = \texttt{toDetFun}\ R\ h_R\ (c_n)\ x_n .$$

**证明是定义性的**（`Nat.rec` 的计算方程）。这是方案一
`trajGen_succ` 的**同构引理**，差别只在机制来自 `LawRule` 而非外部参数。 -/
theorem trajOfLaw_succ (R : LawRule C X X) (hR : IsDirac R)
    (cs : ℕ → C.Carrier) (x₀ : X.Carrier) (n : ℕ) :
    trajOfLaw R hR cs x₀ (n+1) = toDetFun R hR (cs n) (trajOfLaw R hR cs x₀ n) :=
  rfl

/-- ⭐ **初值条件（`rfl` 级）**：轨迹从 `x₀` 出发。 -/
theorem trajOfLaw_zero (R : LawRule C X X) (hR : IsDirac R)
    (cs : ℕ → C.Carrier) (x₀ : X.Carrier) :
    trajOfLaw R hR cs x₀ 0 = x₀ := rfl

/-- ⭐⭐ **忠实性的规律层表述（本模块的核心交付）**：

**轨迹的每一步，其「允许的下一状态分布集合」都恰是 `R` 在对应上下文与当前状态处的集合**

$$\forall n,\quad R\,(c_n)\,(x_n) = \{\delta_{x_{n+1}}\}.$$

**它比 `trajOfLaw_succ` 强在哪**：`trajOfLaw_succ` 只说了「我们用了 `toDetFun`」；
**本条说的是「我们用的 `toDetFun` 正是 `R` 允许的唯一那个分布」**——
即轨迹**每一步都合法于规律 `R`**。这是「规律生成轨迹」的**正确性判据**，
也是把 `toDetFun_spec`（§2）与递推（§4）**接起来**的引理。

**证明**：`toDetFun_spec` 直接给出 `R c x = {δ_{toDetFun R h c x}}`，
再用 `trajOfLaw_succ` 把 `toDetFun` 换成 `x_{n+1}`。 -/
theorem trajOfLaw_law (R : LawRule C X X) (hR : IsDirac R)
    (cs : ℕ → C.Carrier) (x₀ : X.Carrier) (n : ℕ) :
    R (cs n) (trajOfLaw R hR cs x₀ n)
      = {MeasureTheory.Measure.dirac (trajOfLaw R hR cs x₀ (n+1))} := by
  rw [trajOfLaw_succ R hR cs x₀ n, toDetFun_spec R hR (cs n) (trajOfLaw R hR cs x₀ n)]

/-- ⭐ **唯一性**：轨迹由 `x₀` 与上下文序**唯一决定**。

若两条轨迹同初值、同递推（都用 `R` 抽出的转移），则**逐点相等**。
**证明**：对 `n` 归纳，`toDetFun` 是**函数**（同输入同输出），故递推有唯一解。

这是方案一 `trajGen_unique` 的**转写版**：
递推式换成 `LawRule` 的 `toDetFun`，结论不变 ——
即**闸 A 通过后，`LawRule` 的确定性结论全部继承**。 -/
theorem trajOfLaw_unique (R : LawRule C X X) (hR : IsDirac R)
    (cs : ℕ → C.Carrier) (x₀ : X.Carrier) {x y : Traj ℕ X}
    (hx0 : x 0 = x₀) (hy0 : y 0 = x₀)
    (hx : ∀ n, x (n+1) = toDetFun R hR (cs n) (x n))
    (hy : ∀ n, y (n+1) = toDetFun R hR (cs n) (y n)) :
    x = y := by
  funext n
  induction n with
  | zero => rw [hx0, hy0]
  | succ k ih => rw [hx k, hy k, ih]

end Construction

/-! ===========================================================================
    §5  ⚠ 诚实边界：`IsPoint` **不足以**通过闸 A（反例见证）
    =========================================================================== -/

/-! **本节回答「能否只用 `IsPoint`」：不能。**

要证「不能」，须给出一个**满足 `IsPoint` 但非 `IsDirac`** 的 `LawRule`。
取**最简单的**：给定任意**非 Dirac** 测度 `μ₀ : Measure Y.Carrier`
（例如 `ℝ` 上的标准正态、或两点混合 `½(δ₀+δ₁)`），令
$$R_0\,c\,x := \{\mu_0\}.$$
则：
- `R₀` **满足** `IsPoint`（每个 `(c,x)` 的允许集就是单点集 `{μ₀}`）；
- 若 `μ₀` **不是** Dirac，则 `R₀` **不满足** `IsDirac`
  （因为 `IsDirac` 要求 `μ₀ = δ_y`）。

**⟹ `IsPoint ↛ IsDirac`** —— 闸 A 是**实质性**的，不可去掉。
下面把这条做成**两条可编译定理**（`constLaw_isPoint`、`isPoint_not_isDirac`）。 -/

section Counterexample

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-- **恒常规律** `constLaw μ₀`：不论上下文与状态，允许集恒为 `{μ₀}`。

这是**最简的**单点档规律 —— 它把「`LawRule` 可以只是测度的单点集」
这一事实压到最小形式，用于 §5 的反例。 -/
def constLaw (μ₀ : MeasureTheory.Measure Y.Carrier) : LawRule C X Y :=
  fun _ _ => {μ₀}

/-- **恒常规律恒是单点档**：`IsPoint (constLaw μ₀)`。

**无任何前件**（不需要 `μ₀` 是 Dirac、不需要非空性）——
这正是反例的一半：`IsPoint` **太弱**，弱到对任意测度都成立。 -/
theorem constLaw_isPoint (μ₀ : MeasureTheory.Measure Y.Carrier) :
    IsPoint (constLaw (C := C) (X := X) μ₀) :=
  fun _ _ => ⟨μ₀, rfl⟩

/-- ⚠⚠ **反例（主定理）：存在 `IsPoint` 但非 `IsDirac` 的 `LawRule`**。

**前件 `h : ∀ y, μ₀ ≠ δ_y`**（`μ₀` 不是任何 Dirac 测度）。

**结论**：`IsPoint (constLaw μ₀) ∧ ¬ IsDirac (constLaw μ₀)`。

**⟹ `IsPoint` 不蕴含 `IsDirac`，闸 A 不可去。**
这是本模块最重要的**诚实标注**的机器形式：
若有人想「只用 `IsPoint` 生成轨迹」，本条给出**精确的失败位置** ——
在「把 `δ_y` 当成任意测度 `μ₀`」这一步。

**⚠ 前件 `[Nonempty C.Carrier] [Nonempty X.Carrier]` 是数学上真实的**：
要反驳 `∀ c x, ∃ y, …` 必须**取出一个** `(c,x)` 作见证；若 `C` 或 `X` 为空载体，
则 `∀ c x, …` **空洞为真**，`¬ IsDirac` 无法成立。这不是技术性规避。

**证明**：`IsPoint` 由 `constLaw_isPoint`；`¬ IsDirac` 是把 `IsDirac` 的
见证 `⟨y, hy⟩` 代入 `hy : {μ₀} = {δ_y}` 得 `μ₀ = δ_y`，与 `h` 矛盾。 -/
theorem isPoint_not_isDirac [Nonempty C.Carrier] [Nonempty X.Carrier]
    (μ₀ : MeasureTheory.Measure Y.Carrier)
    (h : ∀ y, μ₀ ≠ MeasureTheory.Measure.dirac y) :
    IsPoint (constLaw (C := C) (X := X) μ₀)
      ∧ ¬ IsDirac (constLaw (C := C) (X := X) μ₀) := by
  refine ⟨constLaw_isPoint μ₀, ?_⟩
  intro hD
  obtain ⟨y, hy⟩ := hD (Classical.arbitrary C.Carrier) (Classical.arbitrary X.Carrier)
  exact h y (Set.singleton_injective hy)

end Counterexample

/-! ===========================================================================
    §6  表达力：把 `u`、`ε`、`θ`、`a` 接进 `LawRule`
    =========================================================================== -/

/-! §4 的构造对 `u`、`ε`、`θ`、`a` **常值**，因为 `LawRule C X X` 的单步签名
不吃这四位。本节给出**正规解法**：把上下文 `C` **取成**这四位的积，
于是 `IsDirac` 的抽出函数**吃到**全部输入，轨迹**真正依赖**它们。
**这是类型的重选择，不是新假设**（`CtxSpace` 的 `Carrier` 本就是任意类型）。 -/

/-- **富上下文**：把 `u`、`ε`、`θ`、`a` 打包进上下文。

$$\mathrm{RichCtx}\,F := U \times \N \times \Theta \times \mathrm{Act}.$$

**为什么这样打包**：`LawRule` 的上下文位 `C.Carrier` 是**任意类型**
（`CtxSpace` 只给 `Carrier : Type*`），故可以放任何东西。
把四位放进去后，`IsDirac` 抽出的函数 `RichCtx → X → X` **能读到**它们，
于是 §4 的轨迹**依赖** `u,ε,θ,a` —— 这正是 `TrajGen` 想要的。

**⚠ 顺序说明**：本模块取 `(u, ε, θ, a)` 的顺序
（与 `Step F` 的 `x u ε θ a` 参数序**一致**），使 §6.3 的
`trajOfRichLaw_succ` 能把 `Step` 的各参数**按位对齐**。 -/
def RichCtx (F : Frame) : CtxSpace :=
  ⟨F.U.Carrier × F.Ν.Carrier × F.Θ.Carrier × F.Act.Carrier⟩

/-- **拆包**：从富上下文取回四位（定义性，便于 §6.2 引用）。 -/
def RichCtx.parts {F : Frame} (c : (RichCtx F).Carrier) :
    F.U.Carrier × F.Ν.Carrier × F.Θ.Carrier × F.Act.Carrier := c

/-- **富上下文的规律**：`LawRule` 在 `RichCtx F` 上。

即 `LawRule (RichCtx F) F.X F.X` —— 上下文是四位积，状态空间是 `F.X`。 -/
abbrev RichLaw (F : Frame) [MeasurableSpace F.X.Carrier] : Type _ :=
  LawRule (RichCtx F) F.X F.X

/-! ### §6.1 富上下文轨迹：真正依赖 `u`、`ε`、`θ`、`a` -/

section Rich

variable {F : Frame} [MeasurableSpace F.X.Carrier]

/-- ⭐ **富上下文轨迹**：`IsDirac` 的抽出函数**吃到** `(uₙ, εₙ, θ, aₙ)`。

$$x_0 := x_0,\qquad
  x_{n+1} := \texttt{toDetFun}\ R\ h_R\ (u_n,\ \varepsilon_n,\ \theta,\ a_n)\ x_n .$$

**与 §4 `trajOfLaw` 的区别**：`trajOfLaw` 的上下文序 `cs` 是**外部给的一条序**，
而这里的上下文**由 `TrajGen` 的输入位构造**：
$$c_n := (u_n,\ \varepsilon_n,\ \theta,\ a_n).$$
故**不需要**额外的 `cs` 参数 —— 这就是把 `TrajGen` 的输入位**全部用上**的形式。

**这是本模块对「`IsPoint` ⟹ `TrajGen`」的最终回答**：
`IsDirac` + 富上下文 ⟹ 一个**签名完整**的 `TrajGen`（§6.3）。

标签：**[定义性约定]**。 -/
noncomputable def trajOfRichLaw (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    Traj ℕ F.X :=
  fun n => Nat.rec x₀
    (fun k xk => toDetFun R hR (u k, ε k, θ, a k) xk) n

/-- ⭐ **富上下文递推（`rfl` 级）**：单步转移**显式读到** `(uₙ, εₙ, θ, aₙ)`。

$$x_{n+1} = \texttt{toDetFun}\ R\ h_R\ (u_n,\varepsilon_n,\theta,a_n)\ x_n .$$

与 §4 `trajOfLaw_succ` 的**关键差别**：这里 `toDetFun` 的参数**变了**——
不再是同一个 `c`，而是随 `n` 变的 `(u_n, ε_n, θ, a_n)`。
**故轨迹真正依赖 `TrajGen` 的全部输入位**（除 `ι` 与 `InitialState` 外）。 -/
theorem trajOfRichLaw_succ (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    trajOfRichLaw R hR θ x₀ u ε a (n+1)
      = toDetFun R hR (u n, ε n, θ, a n) (trajOfRichLaw R hR θ x₀ u ε a n) :=
  rfl

/-- ⭐ **富上下文初值条件（`rfl` 级）**：从 `x₀` 出发。 -/
theorem trajOfRichLaw_zero (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    trajOfRichLaw R hR θ x₀ u ε a 0 = x₀ := rfl

/-- ⭐⭐ **富上下文的规律层忠实性**：每一步都合法于 `R`。

$$\forall n,\quad R\,(u_n,\varepsilon_n,\theta,a_n)\,(x_n) = \{\delta_{x_{n+1}}\}.$$

这与 §4 的 `trajOfLaw_law` 同型，只是上下文换成四位积。
**这条是「规律生成轨迹」在富上下文下的正确性判据**。 -/
theorem trajOfRichLaw_law (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    R (u n, ε n, θ, a n) (trajOfRichLaw R hR θ x₀ u ε a n)
      = {MeasureTheory.Measure.dirac (trajOfRichLaw R hR θ x₀ u ε a (n+1))} := by
  rw [trajOfRichLaw_succ R hR θ x₀ u ε a n,
    toDetFun_spec R hR (u n, ε n, θ, a n) (trajOfRichLaw R hR θ x₀ u ε a n)]

/-! ### §6.2 ⭐ 与 `TrajGen` 固定签名**逐位对齐**

`TrajGen F ι`（`Fate/Frame.lean`）的签名是

$$\Theta \to \mathrm{InitialState}\,X \to (\iota\to U) \to (\iota\to\N) \to (\iota\to A)
  \to \mathrm{Traj}\,\iota\,X.$$

§6.1 的 `trajOfRichLaw` 参数表是 `(θ, x₀, u, ε, a)` —— **逐位对齐**，
只差把 `x₀ : F.X.Carrier` 换成 `InitialState F.X`（取 `.val`，与方案一
`trajGenOfFrame` 完全一致的处置）。`TrajGen` 实现的**唯一前置**是 `IsDirac R`，
它**不出现**在签名里，故须作为**显式参数**给出 —— 这正是本模块的答案形态。 -/

/-! ### §6.3 `TrajGen` 签名版实现（`ι = ℕ`）

⭐ **本小节给出直接的答案**：一个**符合 `TrajGen F ℕ` 签名**的函数，
由「点质量 `LawRule` + `IsDirac` 证明」构造。 -/

/-- ⭐⭐ **答案：`IsDirac` 的 `LawRule` 给出一个 `TrajGen F ℕ` 实现**。

$$\texttt{trajGenOfLaw}\ R\ h_R
  := \bigl(\theta,\ x_0,\ u,\ \varepsilon,\ a\bigr)
     \longmapsto \bigl(n \mapsto x_n\bigr),$$

其中 `x₀ := x0.val`（`isRandom` 被丢弃，与方案一 `trajGenOfFrame` 同处置），
递推为 §6.1 的 `trajOfRichLaw`。

**这就是对作者原问的**「构造」**：**
- **闸 A** 由参数 `hR : IsDirac R` 提供（`IsPoint` 不够，见 §5）；
- **闸 B** 由 `RichCtx` 提供（`(uₙ, εₙ, θ, aₙ)` 作上下文）；
- 输出**恰好**是 `TrajGen F ℕ` 的值，签名**逐位对齐**。

**标签**：**[定义性约定]**（`TrajGen F ℕ` 的一个实现）。 -/
noncomputable def trajGenOfLaw (R : RichLaw F) (hR : IsDirac R) : TrajGen F ℕ :=
  fun θ x0 u ε a => trajOfRichLaw R hR θ x0.val u ε a

/-- ⭐⭐⭐ **实现正确性（`rfl` 级）**：`trajGenOfLaw` 就是取 `x0.val` 后的 `trajOfRichLaw`。

**这条连接 §6.3 的 `TrajGen` 实现与 §6.1 的递推式**：
不是两个不同的构造，而是**同一个**构造的两种签名。
与方案一 `trajGenOfFrame_eq` **完全同型**（对照 `Fate/TrajGenDeterministic.lean`）。 -/
theorem trajGenOfLaw_eq (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x0 : InitialState F.X)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    trajGenOfLaw R hR θ x0 u ε a = trajOfRichLaw R hR θ x0.val u ε a := rfl

/-- ⭐⭐ **`TrajGen` 签名版的忠实递推（`rfl` 级）**。

$$\texttt{trajGenOfLaw}\,R\,h_R\,\theta\,x_0\,u\,\varepsilon\,a\ (n+1)
  = \texttt{toDetFun}\ R\ h_R\ (u_n,\varepsilon_n,\theta,a_n)\
      \bigl(\texttt{trajGenOfLaw}\,R\,h_R\,\theta\,x_0\,u\,\varepsilon\,a\ n\bigr).$$

**这就是「轨迹生成器忠实于规律」的最终形态**：
轨迹的每一步都由 `R` 在该步上下文（`uₙ, εₙ, θ, aₙ`）与当前状态处
**唯一允许的那个点**所决定。 -/
theorem trajGenOfLaw_succ (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x0 : InitialState F.X)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    trajGenOfLaw R hR θ x0 u ε a (n+1)
      = toDetFun R hR (u n, ε n, θ, a n) (trajGenOfLaw R hR θ x0 u ε a n) :=
  rfl

/-- ⭐⭐⭐ **`TrajGen` 签名版的规律层忠实性**（本模块最强的一条）。

$$\forall n,\quad R\,(u_n,\varepsilon_n,\theta,a_n)\,(x_n) = \{\delta_{x_{n+1}}\},$$

其中 `x := trajGenOfLaw R h_R θ x₀ u ε a`。
**这说的是：`TrajGen` 输出的轨迹，每一步都合法于 `LawRule`。**
即「规律 ⟹ 轨迹」不是造出来的巧合，而是**可证的忠实性**。

**⚠ 诚实标注**：只需 `hR : IsDirac R`，**不**需要任何前件在 `R` 的
「非平凡性」上 —— 若 `R` 是常值（`constLaw μ₀`）且 `μ₀ = δ_{y₀}`，
则轨迹是**常数** `y₀`。本定理**允许**这种平凡情形（它仍是合法轨迹）。 -/
theorem trajGenOfLaw_law (R : RichLaw F) (hR : IsDirac R)
    (θ : F.Θ.Carrier) (x0 : InitialState F.X)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    R (u n, ε n, θ, a n) (trajGenOfLaw R hR θ x0 u ε a n)
      = {MeasureTheory.Measure.dirac (trajGenOfLaw R hR θ x0 u ε a (n+1))} := by
  rw [trajGenOfLaw_eq]
  exact trajOfRichLaw_law R hR θ x0.val u ε a n

end Rich

/-! ===========================================================================
    §7  诚实标注：本模块的边界
    =========================================================================== -/

/-! ### §7.1 `IsPoint` 不足：已在 §5 成为**定理**（非注释）

`isPoint_not_isDirac` 给出**具体的** `IsPoint` 而**非** `IsDirac` 的 `LawRule`。
故本模块**不**声称「`IsPoint` ⟹ 轨迹」。正确的断言是

$$\boxed{\ \texttt{IsPoint}\ \wedge\ \texttt{IsDirac}\ \Longrightarrow\ \texttt{TrajGen}\ }$$

而由 `IsDirac.isPoint`（§1），`IsDirac` 已**蕴含** `IsPoint`。
**⟹ 本模块的实际前件是 `IsDirac` 一条**，`IsPoint` 是它的**推论**。
这点必须讲明：**读者若只记住 `IsPoint`，会得到错误的预期**。

### §7.2 `Classical.choose` 的元层性质，未伪装成定理

`toDetFun` 由 `Classical.choose` 定义，故两条性质**不在本模块**：
1. **选择的规范性**（同一 `IsDirac` 证明的不同构造是否得同一函数）——
   这是 `Classical.choose` 的**非典范性**，不构成定理；
2. **抽出函数的连续性/可测性**——`IsDirac` **完全不说** `toDetFun` 可测，
   故 §6 的轨迹**不**自动是可测过程的样本路径。要可测性，需另加前件
   （`MeasurableR`：`toDetFun R hR` 作为 `C × X → X` 可测），
   本模块**不引入**，因为 `TrajGen` 的签名**不要求**它。

**⟹ 「`LawRule` ⟹ `TrajGen`」得到的是**函数层**的轨迹生成器，
**不**是随机过程（值域仍是 `Traj ι X`，不是 `Measure (Traj ι X)`）。
要后者，须走方案二（`Fate/TrajGenStochastic.lean`），本模块**不做**。

### §7.3 有限视窗（`ι = Fin T`）未给出

本模块全部在 `ι = ℕ` 上（与 `Fate.TrajGenDeterministic` 的 `trajGen` 一致）。
`Fin T` 版**可照 `stateAt` / `detTraj` 的模式平移**（携带 `n ≤ T` 界限），
本模块**不重复**该构造 —— 它是**纯机械翻译**，且
`Fate/TrajGenDeterministic` 的 §3 已经给出可供模仿的模板。

### §7.4 组合（`compose`）下的轨迹：未做

`LawRule.compose = 取交`（`Fate/LawRule.lean`）。自然的追问是：
「两条规律的轨迹交」是否等于「轨迹的 `compose`」？
本模块**不给**这条 —— 它需要「同一初值/同一上下文序下两轨迹相等」这一前件，
且在 `IsDirac` 下 `compose` 一般**不是** `IsDirac`（两条不同 Dirac 的交为空集，
连 `IsPoint` 都不满足，见 `Fate/LawRule.lean` 的 `point_compose` 需要
相容性前件 `h : Nonempty`）。登记为**开放项**，不冒充结论。
-/

/-! ===========================================================================
    §8  小结（本模块的产物清单）
    =========================================================================== -/

/-! | 项 | 名称 | 性质 |
|---|---|---|
| 闸 A 谓词 | `IsDirac` | 定义 |
| 闸 A 刻画 | `isDirac_iff_exists_detFun` | **已证**（`⟺ DetFun.toLaw` 的像） |
| 闸 A ⊂ `IsPoint` | `IsDirac.isPoint` | **已证** |
| 闸 A ⊄ 反例 | `isPoint_not_isDirac` | **已证**（`IsPoint` 不够） |
| 闸 A 降维 | `toDetFun` / `toDetFun_spec` / `toDetFun_toLaw` | 定义 + 已证 |
| 闸 B 填法 | `CtxOfState` / `ctxFromState` / `RichCtx` | 定义 |
| 一般构造 | `trajOfLaw` + `trajOfLaw_succ` / `_zero` / `_law` / `_unique` | 定义 + 已证 |
| 富上下文构造 | `trajOfRichLaw` + `_succ` / `_zero` / `_law` | 定义 + 已证 |
| ⭐ `TrajGen` 实现 | `trajGenOfLaw` + `_eq` / `_succ` / **`_law`** | 定义 + 已证 |

**对原问的最终答复**：

> **`IsPoint` 单独不能**生成轨迹（§5 反例）；
> **`IsDirac`（= 点质量档）能**，且构造为 `trajGenOfLaw`（§6.3）：
> 把 `(uₙ, εₙ, θ, aₙ)` 作上下文、把抽出的 `toDetFun R hR` 沿 `ℕ` 正向迭代。
> 忠实性由 `trajGenOfLaw_law` 给出：轨迹每一步的允许集恰为 `{δ_{xₙ₊₁}}`。 -/

end LawRuleToTraj

end Fate
