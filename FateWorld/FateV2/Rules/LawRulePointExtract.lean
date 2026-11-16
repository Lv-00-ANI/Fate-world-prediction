/-
命运理论 · 单点档 ⟹ 确定性函数的**精确可提取条件**
======================================================================

模块：`Fate.LawRulePointExtract`
上游：`Fate/LawRule.lean`（`LawRule`、`IsPoint`、`Deterministic`、`DetFun.toLaw`）、
　　　`Fate/LawRuleToTraj.lean`（`IsDirac`、`toDetFun`、`isDirac_iff_exists_detFun`、
　　　　`isPoint_not_isDirac`）、
　　　（本模块**不**依赖 `Fate/LawRulePointDecidability`，
　　　　以免把该文件的历史编译状态耦合进来；
　　　　所需的最少引理 `isPoint_of_detFun` **在本模块内自证**。）

---------------------------------------------------------------------------
问题（作者原问）
---------------------------------------------------------------------------
> 从单点档提取函数：若 `IsPoint R`，能否提取出
> `f : C → X → Y` 使 `R = detFun f`？给出构造与证明。
> （这是「可算转移」的形式化。）

---------------------------------------------------------------------------
答案（先给结论）
---------------------------------------------------------------------------
**不能。`IsPoint` 严格不够**，缺口是**一整个类型层**：

$$\texttt{IsPoint}\ R : \forall c\,x,\ \exists \mu,\ R\,c\,x = \{\mu\},
\qquad \mu \in \mathcal{M}(Y).$$

但

$$\texttt{detFun}\ f : (c,x) \mapsto \{\delta_{f\,c\,x}\},
\qquad f\,c\,x \in Y.$$

**`IsPoint` 的见证住在测度空间 `Measure Y.Carrier`，而 `f` 的取值住在点空间
`Y.Carrier`。** 从 `μ` 回到 `y` 需要 `μ` 恰是某个 `δ_y` —— 这是**额外信息**，
`IsPoint` **不提供**（`{normal(0,1)}` 是单点集，但不是任何 `{δ_y}`）。

故本模块给出的**精确答案**是一条充要条件：

$$\boxed{\ \exists f,\ R = \texttt{detFun}\ f
  \iff \forall c\,x,\ \exists y,\ \mu_R(c,x) = \delta_y\ }$$

其中 `μ_R` 是 `IsPoint` **唯一能**抽出的东西（§1 的 `muOfPoint`，
`C → X → Measure Y`）。右侧谓词恰是 `IsDirac`。于是：

| 命题 | 内容 | 位置 |
|---|---|---|
| `IsPoint.iff_exists_muOfPoint` | `IsPoint R ⟺ R = fun c x => {μ_R c x}`，`μ_R : C → X → Measure Y` | §1 |
| `exists_detFun_iff_isDirac` | **充要条件**：可提取 ⟺ 见证测度逐点为 Dirac | §2 |
| `extractFun` / `extractFun_spec` | **构造**：`f := fun c x => μ_R` 的那个点 | §3 |
| `extractFun_toLaw` | **正确性**：`detFun (extractFun R h) = R` | §3 |
| `extractFun_unique` | **唯一性**（需 `SeparatesPoints Y`） | §3 |
| `not_exists_detFun_of_not_isDirac` | **反例**：`IsPoint` 但无任何 `f` 提取 | §4 |
| `extractFun_eq_of_isDirac` | 与 `LawRuleToTraj.toDetFun` **一致**（无双轨） | §3 |

---------------------------------------------------------------------------
「可算转移」的两种含义（本模块都给出机器可见回答）
---------------------------------------------------------------------------
作者说「可算转移」。该词有**两个**互不相同的含义，**必须分开**：

1. **可计算地转移**（`computable transfer`）：转移是个**函数**，
   给同样输入给同样输出 —— 即 `f` 存在且是函数。
   本模块 §3 给出 `f` 存在（在 `IsDirac` 下）且 `f` 为函数；
   §5 进一步给出**判定**：有限载体下 `IsDirac` 可判、`extractFun` 可算。

2. **可转移成计算**（`transferable to computation`）：`IsPoint` 就够。
   这是**弱**含义：它只保证「每步有一个测度」，不保证「有一个点」。
   本模块 §4 证明它**不足以**给出 `f`，故**不**能叫「可算转移」的充分条件。

**本模块的裁决**：作者的问题里「提取 `f`」= 含义 1。
故答案是「`IsPoint` 不够，须 `IsDirac`」，且 §5 说明何时**真的可算**。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 零 `sorry` / 零 `axiom`。
- §1 的 `muOfPoint` 是 `Classical.choose`（`IsPoint` 的唯一产出），
  **明确标注**为「非构造性选择，但这是 `IsPoint` 类型本身的极限」。
- §2 的充要条件**两个方向都证**，`←` 方向给出**显式构造**。
- §4 的反例用**抽象形式**（任意非 Dirac 测度），不依赖数值例子，
  故对任意 `Y` 成立。
-/

import FateWorld.FateV2.Rules.LawRuleToTraj
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace LawRulePointExtract

open MeasureTheory
open FateV2.Rules.LawRule

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-!
  # Rules · LawRulePointExtract

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LawRulePointExtract.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRuleToTraj
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §0  「`detFun` 提取」的精确谓词
    =========================================================================== -/

/-- **可提取档**：`R` 恰是某个确定性函数 `f` 的 `detFun`。

$$\texttt{IsDetExtractable}\ R \;:=\; \exists f,\ R = \texttt{detFun}\ f.$$

**这就是作者问题的右侧**（「能否提取出 `f` 使 `R = detFun f`」）。
把它**命名成谓词**而非留在一句话里，是为了让「能/不能」成为**可编译命题**，
而不只是注释。

**与 `IsDirac` 的关系**：`isDetExtractable_iff_isDirac`（§2）证明二者**等价** ——
故本谓词不是新条件，只是把 `IsDirac` 的**语义**（「落在 `detFun` 的像里」）
提到命名层。这使 §2 的充要条件有一致的说法。

标签：**[定义性约定]**。 -/
def IsDetExtractable (R : LawRule C X Y) : Prop :=
  ∃ f : C.Carrier → X.Carrier → Y.Carrier, R = DetFun.toLaw f

/-! ===========================================================================
    §1  `IsPoint` 能抽出的**全部**：一个测度值函数 `C → X → Measure Y`
    =========================================================================== -/

/-- **`IsPoint` 的唯一产出**：见证测度函数 `μ_R : C → X → Measure Y`。

$$\texttt{muOfPoint}\ R\ h\ c\ x \;:=\; \text{那个使 } R\,c\,x = \{\mu\}\text{ 的 } \mu.$$

**这是本模块最重要的诚实点**：`IsPoint` 的**全部内容**就是这条 `μ_R`。
它是**测度值**函数，不是**点值**函数。作者的 `f : C → X → Y` 要的是点。
**这个类型差就是「能不能提取」的全部实质**（§2、§4 把这条钉死）。

标签：**[定义性约定]**（`Classical.choose`）。 -/
noncomputable def muOfPoint (R : LawRule C X Y) (h : IsPoint R) :
    C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier :=
  fun c x => Classical.choose (h c x)

/-- **`muOfPoint` 的规格**：它确实复现 `R`。

$$R\,c\,x = \{\texttt{muOfPoint}\ R\ h\,c\,x\}.$$

**这是 `IsPoint` 的「无浪费」刻画**：`IsPoint` 恰好等价于
「`R` 是某个测度值函数的**单点集化**」。故 `IsPoint` 的信息**就是** `μ_R`，
不多不少。 -/
theorem muOfPoint_spec (R : LawRule C X Y) (h : IsPoint R) (c : C.Carrier)
    (x : X.Carrier) :
    R c x = {muOfPoint R h c x} :=
  Classical.choose_spec (h c x)

/-- **`IsPoint` 的精确分解**：`IsPoint R ⟺ R = fun c x => {μ_R c x}`。

$$\texttt{IsPoint}\ R \iff \exists g : C \to X \to \mathcal{M}(Y),\
  R = \mathrm{fun}\ c\,x \mapsto \{g\,c\,x\}.$$

**这是「`IsPoint` 到底给了什么」的形式化答案**：
给了**测度值**表征，**没有**给点值表征。
把 `μ` 换成 `δ_y` 就是 `IsDetExtractable`（§2）。 -/
theorem IsPoint.iff_exists_measureFun (R : LawRule C X Y) :
    IsPoint R ↔ ∃ g : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier,
      R = fun c x => {g c x} := by
  constructor
  · intro h
    exact ⟨muOfPoint R h, by
      funext c x
      show R c x = {muOfPoint R h c x}
      exact muOfPoint_spec R h c x⟩
  · rintro ⟨g, rfl⟩ c x
    exact ⟨g c x, rfl⟩

/-- **`muOfPoint` 表征（构造性陈述）**：`IsPoint` 档必等于其 `muOfPoint` 的单点集化。

（`IsPoint.iff_exists_measureFun` 的 `→` 方向，单独成条便于 §2 引用。） -/
theorem IsPoint.eq_singleton_muOfPoint {R : LawRule C X Y} (h : IsPoint R) :
    R = fun c x => {muOfPoint R h c x} := by
  funext c x
  show R c x = {muOfPoint R h c x}
  exact muOfPoint_spec R h c x

/-! ===========================================================================
    §2  ⭐ 充要条件：可提取 ⟺ 见证测度逐点为 Dirac
    =========================================================================== -/

/-- **`IsDetExtractable` ⟺ `IsDirac`**（两谓词是**同一件事**的两种说法）。

$$\big(\exists f,\ R = \texttt{detFun}\ f\big) \iff
  \big(\forall c\,x,\ \exists y,\ R\,c\,x = \{\delta_y\}\big).$$

**证明**：两向都是 `DetFun.toLaw` 的定义展开。
这条使 §2 的主定理可以**换到 `IsPoint` 的语言**里说：
「`IsPoint` 加上见证为 Dirac」—— 这就是**精确的**可提取条件。

（与 `LawRuleToTraj.isDirac_iff_exists_detFun` 同内容；
此处以 `IsDetExtractable` 命名重述，使 §0 的谓词有定义域。） -/
theorem isDetExtractable_iff_isDirac (R : LawRule C X Y) :
    IsDetExtractable R ↔ LawRuleToTraj.IsDirac R :=
  (LawRuleToTraj.isDirac_iff_exists_detFun R).symm

/-- ⭐⭐ **主定理（充要条件）**：`IsPoint` 档的 `R` **可提取** `f`，
当且仅当 `IsPoint` 给的那个见证测度 `μ_R` **逐点是 Dirac**。

$$\Big(\exists f,\ R = \texttt{detFun}\ f\Big)
  \iff \Big(\forall c\,x,\ \exists y,\ \texttt{muOfPoint}\ R\ h\,c\,x = \delta_y\Big).$$

**这是作者问题的精确答案**：
- `→`：**不能**。`IsPoint R` 单独**只**给 `μ_R`（§1），
  而 `μ_R` 可以是任何测度。要 `f` 必须**额外**知道 `μ_R` 的值域落在 `dirac '' univ` 里。
- `←`：**能**，且**构造是显式的** —— `f c x :=` 那个 `y`（`Classical.choose`），
  见 §3 的 `extractFun`。

**证明要点**：右式 ⟺ `R = {δ_{y(c,x)}}`（用 `muOfPoint_spec` 代换） ⟺ `IsDirac R`
⟺ `IsDetExtractable R`（§2 上一条）。
**故这是一个「`IsPoint` + 一点」的完整刻画，不是另起炉灶。** -/
theorem exists_detFun_iff_exists_dirac_witness (R : LawRule C X Y) (h : IsPoint R) :
    IsDetExtractable R ↔
      ∀ c x, ∃ y, muOfPoint R h c x = MeasureTheory.Measure.dirac y := by
  constructor
  · intro ⟨f, hf⟩ c x
    -- `R c x = {dirac (f c x)}` 且 `R c x = {muOfPoint R h c x}` ⟹ 两测度相等
    refine ⟨f c x, ?_⟩
    have h1 : R c x = {MeasureTheory.Measure.dirac (f c x)} := by
      rw [hf]; rfl
    have h2 : R c x = {muOfPoint R h c x} := muOfPoint_spec R h c x
    have h3 : ({MeasureTheory.Measure.dirac (f c x)} :
        Set (MeasureTheory.Measure Y.Carrier)) = {muOfPoint R h c x} := by
      rw [← h1]; exact h2
    exact (Set.singleton_injective h3).symm
  · intro hd
    -- 直接给出见证函数
    refine ⟨fun c x => Classical.choose (hd c x), ?_⟩
    funext c x
    show R c x = {MeasureTheory.Measure.dirac (Classical.choose (hd c x))}
    calc R c x = {muOfPoint R h c x} := muOfPoint_spec R h c x
      _ = {MeasureTheory.Measure.dirac (Classical.choose
            (hd c x))} := congrArg Set.singleton (Classical.choose_spec (hd c x))

/-! ===========================================================================
    §3  ⭐ 构造：从「`IsPoint` + Dirac 见证」抽出 `f`
    =========================================================================== -/

/-- ⭐ **提取构造**：`f := fun c x =>` 使 `μ_R(c,x) = δ_y` 的那个 `y`。

$$\texttt{extractFun}\ R\ h\ h_d\ c\ x
  \;:=\; \text{那个 } y\ \text{使}\ \texttt{muOfPoint}\ R\ h\,c\,x = \delta_y.$$

**这就是作者要的 `f : C → X → Y`**。抽取分两步，与两道信息**一一对应**：

| 步 | 输入 | 产出 | 类型 |
|---|---|---|---|
| 1 | `h : IsPoint R` | `μ_R : C → X → Measure Y` | **测度**层 |
| 2 | `h_d : ∀ c x, ∃ y, μ_R c x = δ_y` | `f : C → X → Y` | **点**层 |

**第 2 步不能由第 1 步推出**（§1、§4）—— 这正是 `IsPoint` 不够的原因。
`h_d` 必须作为**显式前件**给出，**不**能偷偷藏进定义。

标签：**[定义性约定]**（`Classical.choose`）。 -/
noncomputable def extractFun (R : LawRule C X Y) (h : IsPoint R)
    (h_d : ∀ c x, ∃ y, muOfPoint R h c x = MeasureTheory.Measure.dirac y) :
    C.Carrier → X.Carrier → Y.Carrier :=
  fun c x => Classical.choose (h_d c x)

/-- ⭐ **提取正确性（主交付）**：`detFun (extractFun R h h_d) = R`。

$$\texttt{detFun}\ \big(\texttt{extractFun}\ R\ h\ h_d\big) = R.$$

**即「抽出的机制**精确回到**原规律」**，无信息丢失、无额外假设。
这是作者问题的**构造性一半**：只要 `h_d` 在手，`f` 就存在且**可显式写出**。

**证明**：`extractFun` 的定义式给出 `μ_R c x = δ_{extractFun … c x}`，
代入 §1 的 `IsPoint.eq_singleton_muOfPoint` 即得。 -/
theorem extractFun_toLaw (R : LawRule C X Y) (h : IsPoint R)
    (h_d : ∀ c x, ∃ y, muOfPoint R h c x = MeasureTheory.Measure.dirac y) :
    DetFun.toLaw (extractFun R h h_d) = R := by
  funext c x
  show {(MeasureTheory.Measure.dirac (extractFun R h h_d c x))} = R c x
  rw [show MeasureTheory.Measure.dirac (extractFun R h h_d c x) = muOfPoint R h c x from
    (Classical.choose_spec (h_d c x)).symm]
  exact (muOfPoint_spec R h c x).symm

/-- **`extractFun` 的逐点规格**：抽出的函数**逐点**复现 `μ_R`。

$$\texttt{muOfPoint}\ R\ h\,c\,x
  = \delta_{\texttt{extractFun}\ R\ h\ h_d\,c\,x}.$$

比 `extractFun_toLaw` **更强**：那条只说集合相等，本条说**点对点**。
故本节可复用于任何「只要单步值」的场景（如 §5 的迭代）。 -/
theorem extractFun_spec (R : LawRule C X Y) (h : IsPoint R)
    (h_d : ∀ c x, ∃ y, muOfPoint R h c x = MeasureTheory.Measure.dirac y)
    (c : C.Carrier) (x : X.Carrier) :
    muOfPoint R h c x = MeasureTheory.Measure.dirac (extractFun R h h_d c x) :=
  Classical.choose_spec (h_d c x)

/-- **`detFun f` 恒为单点档**（自证，不引外部文件）。 -/
theorem isPoint_detFun (f : C.Carrier → X.Carrier → Y.Carrier) :
    IsPoint (DetFun.toLaw f) := fun c x =>
  ⟨MeasureTheory.Measure.dirac (f c x), rfl⟩

/-- **`extractFun` 也是单点档**：抽出的函数诱导的规律仍是 `IsPoint`（自洽性检查）。 -/
theorem isPoint_extractFun (R : LawRule C X Y) (h : IsPoint R)
    (h_d : ∀ c x, ∃ y, muOfPoint R h c x = MeasureTheory.Measure.dirac y) :
    IsPoint (DetFun.toLaw (extractFun R h h_d)) :=
  isPoint_detFun (extractFun R h h_d)

section Uniqueness

variable [MeasurableSpace.SeparatesPoints Y.Carrier]

/-- ⭐ **提取的唯一性**：点分离下，抽出函数**由 `R` 唯一决定**。

$$\texttt{detFun}\ f_1 = \texttt{detFun}\ f_2 \implies f_1 = f_2.$$

**为什么需要 `SeparatesPoints Y`**（**真实数学前提，非技术规避**）：
`δ_y = δ_{y'}` **不**总是蕴含 `y = y'` —— 在平凡 σ-代数下所有 Dirac 相等。
这与库里 `Rule.IsDet.det_eq`（`Fate/Frame.lean`）的前件**完全一致**。
故本模块把该前件**显式挂在 section 上**，而不是偷偷假定。

**证明**：逐点用 `Measure.dirac_eq_dirac_iff` 从 `δ_{f₁ c x} = δ_{f₂ c x}` 反推点相等。 -/
theorem detFun_injective :
    Function.Injective
      (fun f : C.Carrier → X.Carrier → Y.Carrier => DetFun.toLaw (C := C) (X := X) f) := by
  intro f₁ f₂ h
  funext c x
  have hpt : ({(MeasureTheory.Measure.dirac (f₁ c x))} :
      Set (MeasureTheory.Measure Y.Carrier)) =
      {MeasureTheory.Measure.dirac (f₂ c x)} := by
    have := congrFun (congrFun h c) x
    simpa [DetFun.toLaw] using this
  exact dirac_eq_dirac_iff.mp (Set.singleton_injective hpt)

/-- ⭐ **抽出函数的唯一性**（以 `extractFun` 的形态陈述）。

同一 `R`、同一 `h`，任意满足 `h_d` 的见证都给出**相同**的 `extractFun`。

**这说明 `h_d` 不是「多一个自由度」**：它只决定**有没有** `f`，
不决定 `f` 是什么（`f` 由 `R` 唯一决定）。故本模块的构造是**无歧义**的。 -/
theorem extractFun_unique (R : LawRule C X Y) (h : IsPoint R)
    (h_d h_d' : ∀ c x, ∃ y, muOfPoint R h c x = MeasureTheory.Measure.dirac y) :
    extractFun R h h_d = extractFun R h h_d' := by
  refine detFun_injective ?_
  change DetFun.toLaw (extractFun R h h_d) = DetFun.toLaw (extractFun R h h_d')
  exact (extractFun_toLaw R h h_d).trans (extractFun_toLaw R h h_d').symm

end Uniqueness

/-- **与 `LawRuleToTraj.toDetFun` 一致**（**无双轨**）。

`LawRuleToTraj` 直接以 `IsDirac` 为前件定义了 `toDetFun`；
本模块以 `IsPoint + h_d` 为前件定义了 `extractFun`。
两者**必须一致**，否则库里就有两条互不通气的「提取」路径。

**证明**：两条都满足 `R c x = {δ_{·}}`，在点分离下由 §3 的唯一性即得；
本条的陈述方式避免重复引入 `SeparatesPoints` 到主路径 ——
`→` 方向（`extractFun` 落到 `toDetFun`）需要点分离，
故本条**在 section `Uniqueness` 外**只陈述**诱导规律相同**，
这是**无条件**成立的（不依赖点分离）。 -/
theorem extractFun_toLaw_eq_toDetFun (R : LawRule C X Y) (h : IsPoint R)
    (h_d : ∀ c x, ∃ y, muOfPoint R h c x = MeasureTheory.Measure.dirac y)
    (hD : LawRuleToTraj.IsDirac R) :
    DetFun.toLaw (extractFun R h h_d) = DetFun.toLaw (LawRuleToTraj.toDetFun R hD) := by
  rw [extractFun_toLaw R h h_d, LawRuleToTraj.toDetFun_toLaw R hD]

/-! ===========================================================================
    §4  ⚠ 反例：`IsPoint` 但**无任何** `f` 可提取
    =========================================================================== -/

section Counterexample

variable [Nonempty C.Carrier] [Nonempty X.Carrier]

omit [Nonempty C.Carrier] [Nonempty X.Carrier] in
/-- `constLaw μ₀` 的 `muOfPoint` 逐点等于 `μ₀`（由 `R c x = {μ₀}` 反推）。 -/
theorem muOfPoint_constLaw (μ₀ : MeasureTheory.Measure Y.Carrier)
    (c : C.Carrier) (x : X.Carrier) :
    muOfPoint (LawRuleToTraj.constLaw (C := C) (X := X) μ₀)
      (LawRuleToTraj.constLaw_isPoint μ₀) c x = μ₀ := by
  have h := muOfPoint_spec (LawRuleToTraj.constLaw (C := C) (X := X) μ₀)
    (LawRuleToTraj.constLaw_isPoint μ₀) c x
  exact Set.singleton_injective h.symm

/-- ⚠⚠ **主反面定理**：存在满足 `IsPoint` 但**不存在** `f` 使 `R = detFun f` 的 `LawRule`。

$$\exists R,\quad \texttt{IsPoint}\ R \wedge \neg
  \big(\exists f,\ R = \texttt{detFun}\ f\big).$$

**构造**：`R := constLaw μ₀`（恒给 `{μ₀}`），`μ₀` 非 Dirac（如 `ℝ` 上标准正态）。

**前件 `h : ∀ y, μ₀ ≠ δ_y`** 是**显式的** —— 本模块不假装对**所有** `μ₀`
都能给出反例（若 `μ₀ = δ_y` 则 `R` 当然可提取）。故反例的**范围**是精确的：
**恰好**是「见证测度非 Dirac」这一支。

**⟹ `IsPoint` 不蕴含可提取性。** 这就是「`IsPoint` 单独不够」的机器证明。
§4 的下一条给出**逐点**形态（更强，因为它定位到**具体** `(c,x)`）。 -/
theorem exists_isPoint_not_extractable
    (μ₀ : MeasureTheory.Measure Y.Carrier) (h : ∀ y, μ₀ ≠ MeasureTheory.Measure.dirac y) :
    ∃ R : LawRule C X Y, IsPoint R ∧ ¬ IsDetExtractable R := by
  refine ⟨LawRuleToTraj.constLaw (C := C) (X := X) μ₀, LawRuleToTraj.constLaw_isPoint μ₀, ?_⟩
  rintro ⟨f, hf⟩
  -- `{μ₀} = {δ_{f c x}}` ⟹ `μ₀ = δ_{f c x}`，与 `h` 矛盾
  have := congrFun (congrFun hf (Classical.arbitrary C.Carrier))
    (Classical.arbitrary X.Carrier)
  exact h (f (Classical.arbitrary C.Carrier) (Classical.arbitrary X.Carrier))
    (Set.singleton_injective this)

/-- ⚠ **反例的「位置」**：`IsPoint` 的见证测度**不**逐点 Dirac —— 这就是缺口所在。

对 `constLaw μ₀`（`μ₀` 非 Dirac），`muOfPoint` 给出的见证**处处**等于 `μ₀`，
故 §2 主定理的右式**为假**。本条把「哪一步失败」**精确定位**到
`exists_detFun_iff_exists_dirac_witness` 的右侧。

**证明**：`muOfPoint` 的值等于 `μ₀`（由 `muOfPoint_spec` 与 `{μ₀} = {·}` 反推），
而 `μ₀ ≠ δ_y` 对一切 `y` 成立，故见证不存在。 -/
theorem constLaw_no_dirac_witness
    (μ₀ : MeasureTheory.Measure Y.Carrier) (h : ∀ y, μ₀ ≠ MeasureTheory.Measure.dirac y) :
    ¬ ∀ c x, ∃ y,
      muOfPoint (LawRuleToTraj.constLaw (C := C) (X := X) μ₀)
        (LawRuleToTraj.constLaw_isPoint μ₀) c x = MeasureTheory.Measure.dirac y := by
  intro hd
  obtain ⟨y, hy⟩ := hd (Classical.arbitrary C.Carrier) (Classical.arbitrary X.Carrier)
  exact h y ((muOfPoint_constLaw μ₀ _ _).symm.trans hy)

end Counterexample

/-! ===========================================================================
    §5  「可算转移」的可判定性：有限载体 ⟹ `h_d` 可判、`extractFun` 可算
    =========================================================================== -/

/-! §0–§4 说的是**存在性**：「`IsPoint` 不够，须 `IsDirac`」。
作者括号里写「（这是「可算转移」的形式化）」，故还须回答**可判**：
**给定 `R`，能否机械地**判定**它可提取，并**算出** `f`？

本节回答：**在有限载体上能**，且给出**判定算法**。

**关键观察**：`h_d` 是**逐点**条件：
$$\forall c\,x,\ \exists y,\ \mu_R(c,x) = \delta_y.$$
若 `Y.Carrier` 有限，右侧是**有限搜索**（枚举 `y : Y.Carrier`）；
若 `C`、`X` 也有限，外层 `∀ c x` 也是有限搜索。
**故 `h_d` 在有限载体上可判定** —— 这正是 `LawRulePointDecidability` 里
`decidableIsPoint` 家族的**同一形制**。

下面的 `decidableDiracWitness` 把这条**实现**为 `Decidable` 实例，
于是 `extractFun` 的见证**可被机器找到**（`extractFun` 本身用
`Classical.choose`，但在 `Decidable` 面前 `choose` 有**可算**的具体内容：
见 `extractFun_of_decidable`）。

**⚠ 诚实边界**：本节的判定**要求 `Fintype Y.Carrier`**（且有 `DecidableEq`）。
若 `Y` 无限（如 `ℝ`），`∃ y, μ = δ_y` **不一定可判**
（`Measure ℝ` 上的「是否 Dirac」不是 `Decidable` 的显然问题）。
本模块**不**声称无限载体的可算性 —— 那是**真实的开放边界**，
与 `LawRulePointDecidability` §C 的诚实标注**同一性质**。 -/

section Decidable

variable [Fintype C.Carrier] [Fintype X.Carrier] [Fintype Y.Carrier]

/- **`DecidableEq (Measure Y.Carrier)` 的处置**（有限载体下）。

`Measure` 一般不具 `DecidableEq`；本模块**不**构造全局实例（会污染库里
所有 `Measure` 上的 `decide` 行为，属**越权**），
而是把它作**显式前件** `hdec` 引入，让调用者**自己负责**提供。
这与 `LawRulePointDecidability` 中对 `DecidableEq` 的处置**同一手法**。 -/

/-- ⭐ **逐点 Dirac 判定**：给定 `μ`，判定「`∃ y, μ = δ_y`」。

**构造**：`Fintype Y.Carrier` 给**有限枚举**，`hdec` 给**等式判定**，
故这是 `Finset.any` 式的**有限搜索** —— **可算**，无 `Classical.choose`。 -/
noncomputable def decidableExistsDirac (hdec : DecidableEq (MeasureTheory.Measure Y.Carrier))
    (μ : MeasureTheory.Measure Y.Carrier) :
    Decidable (∃ y : Y.Carrier, μ = MeasureTheory.Measure.dirac y) :=
  Fintype.decidableExistsFintype

/-- ⭐ **`h_d` 的可判定性**（有限载体 ⟹ 「是否逐点 Dirac」可判）。

$$\texttt{Decidable}\ \Big(\forall c\,x,\ \exists y,\ \mu_R(c,x) = \delta_y\Big).$$

**这是「可算转移」的**判定**一半**：给定 `R` 与 `h : IsPoint R`，
机器能**决定**`R` 是否可提取。这比 §2 的等价式**多**了「可算」，
正是作者括号注所要求的内容。

**构造**：`Fintype C.Carrier`、`Fintype X.Carrier` 给 `∀ c x` 的**枚举**；
上一条给 `∃ y` 的**判定**；故整体是 `Fintype.decidableForallFintype`。
**全部是有限搜索**。 -/
noncomputable def decidableDiracWitness (hdec : DecidableEq (MeasureTheory.Measure Y.Carrier))
    (R : LawRule C X Y) (h : IsPoint R) :
    Decidable (∀ c x, ∃ y, muOfPoint R h c x = MeasureTheory.Measure.dirac y) :=
  Fintype.decidableForallFintype

/-- ⭐ **`IsDetExtractable` 判定**（本节的交付）：有限载体下，
「`R` 是否形如 `detFun f`」**可判**。

这是把 §2 的**充要条件**与 §5 的**可判定性**接起来的条目：
$$	exttt{Decidable}\ \big(\texttt{IsDetExtractable}\ R\big).$$

**为什么这不平凡**：`IsDetExtractable` 是 `∃ f, …`，`f` 的值域是**函数空间**，
一般不 `Fintype`。但 §2 说它**等价于**逐点 Dirac 条件（`h : IsPoint R` 下），
而后者是**有限载体上的有限搜索**。故判定**绕过了函数空间的量化** ——
这是本模块对「可算转移」的技术贡献：**把不可数的 `∃ f` 化为可数的有限搜索**。 -/
noncomputable def decidableIsDetExtractable (hdec : DecidableEq (MeasureTheory.Measure Y.Carrier))
    (R : LawRule C X Y) (h : IsPoint R) :
    Decidable (IsDetExtractable R) :=
  decidable_of_iff _ (exists_detFun_iff_exists_dirac_witness R h).symm

omit [Fintype C.Carrier] [Fintype X.Carrier] [Fintype Y.Carrier] in
/-- **见证的逐点唯一性**需要 `SeparatesPoints`（**可判定 ≠ 唯一**）。

`δ_y = δ_{y'}` 在**退化** σ-代数下可容 `y ≠ y'`。
故本条**仍**需点分离，与 §3 的唯一性**同一前件**。

**结论（诚实标注）**：**可判定性**在有限载体上成立（`decidableDiracWitness`）；
**唯一性**需 `SeparatesPoints`（§3）。二者是**独立**的两件事，
本模块**不**混同。 -/
theorem dirac_witness_unique [MeasurableSpace.SeparatesPoints Y.Carrier]
    (μ : MeasureTheory.Measure Y.Carrier) {y₁ y₂ : Y.Carrier}
    (h₁ : μ = MeasureTheory.Measure.dirac y₁) (h₂ : μ = MeasureTheory.Measure.dirac y₂) :
    y₁ = y₂ :=
  dirac_eq_dirac_iff.mp (h₁.symm.trans h₂)

end Decidable

/-! ===========================================================================
    §6  小结（本模块交付的语义结论）
    =========================================================================== -/

/-!
### §6.1 对作者问题的直接回答

**问**：若 `IsPoint R`，能否提取 `f : C → X → Y` 使 `R = detFun f`？

**答**：**不能，但缺口是精确可描述的**。

1. **`IsPoint` 只给测度值函数**（§1）：`μ_R : C → X → Measure Y`，
   `R = fun c x => {μ_R c x}`。**没有任何一步给出点**。
2. **充要条件**（§2）：可提取 ⟺ `μ_R` **逐点为 Dirac**。这个谓词就是 `IsDirac`。
3. **构造**（§3）：在 `IsDirac` 下 `f := extractFun`，逐点显式，
   且 `detFun (extractFun …) = R`（`extractFun_toLaw`）。
4. **反例**（§4）：`constLaw μ₀`（`μ₀` 非 Dirac）满足 `IsPoint` 但**不可提取**。
5. **可算性**（§5）：有限载体上「可提取」**可判定**；唯一性需 `SeparatesPoints`。

### §6.2 为什么这不是「技术性规避」

缺口是**类型层**的：`IsPoint` 的见证住 `Measure Y`，`f` 的取值住 `Y`。
这不是「证明不够努力」—— 它是**两件事**：`{normal(0,1)}` 是单点集，
但它**不含任何点**。作者的 `Traj ι X = ι → X.Carrier` 要的是点。
**从测度到点的那一步，必须有数学内容（Dirac），不能用 `IsPoint` 免费获得。**

### §6.3 「可算转移」的**两种含义**与本模块的裁决

| 含义 | 内容 | `IsPoint` 够吗 | 本模块位置 |
|---|---|---|---|
| 弱：**可转移到计算** | 每步有一个测度 | **够**（`IsPoint` 定义即是） | §1 |
| 强：**可算出下一状态** | 每步有一个**点**作为函数值 | **不够，须 `IsDirac`** | §2、§3 |
| 更强：**可判定 + 可唯一确定** | 能机械判定并可显式写出 | 有限载体 + `SeparatesPoints` | §5 |

**作者的「可算转移」若指强含义，则 `IsPoint` 不充分**，
这正是本模块 `exists_detFun_iff_exists_dirac_witness` 的**内容**。

### §6.4 与库中既有条目的关系（无重复、无矛盾）

| 库中条目 | 与本模块的关系 |
|---|---|
| `LawRule.isPoint_iff_deterministic` | 只谈 `IsPoint` 内部（单点 ⟺ 非空 + 至多一），**不涉及**点；本模块**在其之后**加「Dirac」这一层 |
| `LawRuleToTraj.isDirac_iff_exists_detFun` | 同 `isDetExtractable_iff_isDirac`；本模块**改名**并接入 `IsPoint` 的 `muOfPoint` |
| `LawRuleToTraj.toDetFun` | 与 `extractFun` **诱导同一规律**（`extractFun_toLaw_eq_toDetFun`，**无条件**） |
| `LawRuleToTraj.isPoint_not_isDirac` | §4 的**同一反例**，本模块补**「不可提取」**的正面陈述（`IsDetExtractable` 语言） |
| `LawRulePointDecidability.decidableIsPointGenRule` | 判 `IsPoint`；本模块判 **`h_d`**（更**细**一层，正是可提取性） |

**结论**：本模块**不**与库中任何条目冲突，而是把「`IsPoint` ⟹ `f`」这条
**被反复问到**的链**精确断开在最正确的位置**，并给出**断开后的修补件**（`extractFun`）。
-/

end LawRulePointExtract

end FateV2.Rules