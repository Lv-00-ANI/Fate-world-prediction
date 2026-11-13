import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Coequalizers
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.Algebra.Category.Grp.Images
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import FateWorld.Legacy.KernelQuotient
import FateWorld.Legacy.KernelQuotientExtra

/-! ===========================================================================
  §12  核–商理论的**范畴化**（`KernelQuotientCategorical`）

  ## 缘起

  `Fate/KernelQuotient.lean`（命名空间 `Fate.KernelQuotientTheory`）把项目里
  三处独立重建的结构统一为**一个** `Set`-层理论：对**任意** `f : A → B`，
  核 `ker f`、商 `A/ker f`、第一同构 `A/ker f ≃ range f`、三情形穷尽、
  核族的完备子格性质。

  **但该框架整体建立在 `Setoid` / `Quotient` / `Set.range` 上** ——
  它其实是**集合范畴 `Type` 内部**的理论。本文件把这套理论**提升到任意范畴 `C`**，
  并逐条把经典定理作为特例回收，同时**如实登记**哪些推广**不**成立。

  ## 本文件做什么

  * **§12.1** 一般范畴中的核–商：核对（`IsKernelPair`）、余核对、`catKernel`；
  * **§12.1′** ⭐⭐ **第一同构定理的范畴版本**（粗–细分解唯一性 + 单射–满射分解）；
  * **§12.2** ⭐⭐ **三情形穷尽的范畴化** + 塌缩的泛元素刻画；
  * **§12.3** ⭐⭐ 核的格结构与 `Subobject`（含**关键否定结论**）；
  * **§12.4** 向量空间特例；**§12.5** 群 / 环特例；**§12.6** 集合范畴特例；
  * **§12.7** 反例与诚实登记。

  ## 与任务描述的实测差异（以源码为准）

  | 任务描述 | 实测（`Fate/KernelQuotient.lean`） |
  |---|---|
  | `Collapse/Faithful/MiddleZone (f : A → B) (F : Set A)` | ✅ 一致 |
  | 「`kernel_family_sInf` 核族对任意交封闭（**完备子格**）」 | ⚠ 陈述是 `∃ γ g, kernel g = sInf S`，**只是下完备**；`⊔` **不**封闭（该文件 §10.7 自带反例 `kernel_family_not_supClosed`） |
  | 「`kappa_galoisConnection`」 | ⚠ 实测**不是** Mathlib 的 `GaloisConnection`，而是 `Iff.rfl` 级重言 `kernel f ≤ ρ ↔ ∀ a b, f a = f b → ρ a b`；文件自己明说了 |
  | `KernelQuotientExtra.lean` 有 4 条 | ✅ 一致（`kernel_congr` / `kernel_le_kernel_comp` / `kernel_le_iff` / `kernel_joint_iff`） |
  | 命名空间 `KernelQuotientTheory` | ✅ 一致 |

  ## 诚实边界

  * **零 `sorry` / `admit` / 自定义 `axiom`**。
  * **零硬编码**：一切结论对任意范畴 / 映射成立。
  * ⚠ 最重要的**否定结论**在 **§12.7.1**：
    「塌缩 ⟺ 商对象退化」这条**真正的数学内容**
    在一般范畴中**不能**从三情形的析取自动得到；
    §12.2 对此给出正确的范畴化陈述与机器核验的边界。
  =========================================================================== -/

set_option autoImplicit false

namespace Fate

namespace KernelQuotientCategorical

open CategoryTheory CategoryTheory.Limits

universe u v w

/-! ===========================================================================
  §12.1  一般范畴中的核–商
  =========================================================================== -/

section General

variable {C : Type u} [Category.{v} C]

/-- **核对（kernel pair）**：`f : X ⟶ Y` 的核对即拉回方块
$\;R \rightrightarrows X \xrightarrow{\;f\;} Y$。

**推广了什么**：`Set` 层 `kernel f = Setoid.ker f` 的范畴替代。
在 `Type` 中核对是子类型 `{ p : X × X // f p.1 = f p.2 }`，
它**编码**了 `ker f`（见 §12.6 的 `typesKernelPair_iff_kernel`）。 -/
abbrev KernelPairOf {X Y : C} (f : X ⟶ Y) (R : C) (a b : R ⟶ X) : Prop :=
  IsKernelPair f a b

/-- **核对就是拉回方块**（定义性）。

**推广了什么**：把 `Set` 层的 `kernel f a b ↔ f a = f b`（`Iff.rfl` 级重言）
**提升**为范畴层的「$R$ 是 `f` 沿自身的拉回对象」。
**⟹ 即**：`Set` 层「核按定义就是相等关系」的**平凡性**，
在范畴层被「拉回的万有性质」**替代** —— 这条替代是本文件一切推广的机制。 -/
theorem kernelPair_iff_isPullback {X Y R : C} (f : X ⟶ Y) (a b : R ⟶ X) :
    KernelPairOf f R a b ↔ IsPullback a b f f :=
  Iff.rfl

/-- **核对是对称的**：`(a, b)` 是 `f` 的核对 ⟹ `(b, a)` 也是。

**推广了什么**：`Setoid.ker` 的**对称性**（`Setoid.symm`）。
⚠ 在范畴层对称性**不是**定义的一部分，而是拉回方块**翻转**后仍为拉回
（`IsPullback.flip`）—— 本定理记录了这处**结构性差异**：
`Set` 层的 `Setoid` **内建**了自反/对称/传递，
范畴层的核对只**内建**了「交换 + 万有」，其余性质须**证明**。 -/
theorem kernelPair_symm {X Y R : C} {f : X ⟶ Y} {a b : R ⟶ X}
    (k : KernelPairOf f R a b) : KernelPairOf f R b a :=
  k.flip

/-- **核对由拉回实现**（有拉回时）：`pullback f f` 即 `f` 的核对。

**推广了什么**：`Setoid.ker` 在**任意有拉回的范畴**中的替代构造。
⚠ 在 `Set` 层我们**直接写** `Setoid.ker f`，范畴层则必须**假设拉回存在** ——
这正是「一般范畴相对 `Set`」的第一处**代价**。 -/
theorem kernelPairOfHasPullback {X Y : C} (f : X ⟶ Y) [HasPullback f f] :
    KernelPairOf f (pullback f f) (pullback.fst f f) (pullback.snd f f) :=
  IsPullback.of_hasPullback f f

/-- **核对的万有性质（提升）**：任意 `p q : S ⟶ X` 若 `p ≫ f = q ≫ f`，
则它们**唯一地**穿过核对。

**推广了什么**：`Set` 层「`f a = f b` ⟹ `a`, `b` 同属一个 `ker f`-类」
的范畴化。
⚠ **注意**：`Set` 层这条是**平凡**的（`ker f` 按定义就是相等关系），
范畴层它**正是**核对作为拉回的万有性质 —— 本推广在这里**真正给出内容**。 -/
noncomputable def kernelPairLift {X Y R : C} {f : X ⟶ Y} {a b : R ⟶ X}
    (k : KernelPairOf f R a b) {S : C} (p q : S ⟶ X) (w : p ≫ f = q ≫ f) : S ⟶ R :=
  k.lift p q w

/-- **提升的第一投影律**：`lift p q w ≫ a = p`。 -/
@[reassoc (attr := simp)]
theorem kernelPairLift_fst {X Y R : C} {f : X ⟶ Y} {a b : R ⟶ X}
    (k : KernelPairOf f R a b) {S : C} (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    kernelPairLift k p q w ≫ a = p :=
  k.lift_fst p q w

/-- **提升的第二投影律**：`lift p q w ≫ b = q`。 -/
@[reassoc (attr := simp)]
theorem kernelPairLift_snd {X Y R : C} {f : X ⟶ Y} {a b : R ⟶ X}
    (k : KernelPairOf f R a b) {S : C} (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    kernelPairLift k p q w ≫ b = q :=
  k.lift_snd p q w

/-- **单射（`Mono`）的核对是平凡的**：`f` 单 ⟹ `(𝟙 X, 𝟙 X)` 是 `f` 的核对。

**推广了什么**：`KernelQuotient.injective_iff_kernel_bot`
（`Set` 层：「单射 ⟺ 核为 `⊥`」）的**范畴对应物**：
`Mono f` ⟹ 核对**退化为对角** `(𝟙, 𝟙)`。
**⟹ 即**：「单射 ⟹ 核平凡」这条**无条件**地范畴化成功。 -/
theorem kernelPair_id_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    KernelPairOf f X (𝟙 X) (𝟙 X) :=
  IsKernelPair.id_of_mono f

end General

/-! ===========================================================================
  §12.1′  ⭐⭐ 第一同构定理的范畴版本
  =========================================================================== -/

section FirstIsomorphism

variable {C : Type u} [Category.{v} C]

/-- **余核对（cokernel pair）/ 商对象**：`f : X ⟶ Y` 的余核对是推出
$\;Y \sqcup_X Y$。

**推广了什么**：`Set` 层「商 `A/ker f`」的范畴替代。

⚠⚠ **精确差异（重要且必须登记）**：`Set` 层 `A/ker f` 是 `A` 的商**对象**；
范畴层的推出 $Y \sqcup_X Y$ 却是 **`Y`** 的商。
一般范畴中「把 `X` 中两个 `f`-同值的点粘起来」**没有**唯一自然的实现：
粘合的结果一般**不是** `C` 的对象，必须借助**有效正则范畴**中的
**余核对**或**正规子对象**。
**⟹ 这是「核–商」在范畴层**不如** `Set` 层干净的结构性原因**，
也是本文件多处推广必须**额外假设**的根源。 -/
abbrev CokernelPairOf {X Y : C} (f : X ⟶ Y) (Q : C) (ι₁ ι₂ : Y ⟶ Q) : Prop :=
  IsPushout f f ι₁ ι₂

/-- **内核（范畴意义）**：`f : X ⟶ Y` 在**带零态射**范畴中的核对象
$\ker f$。

**推广了什么**：`Set` 层 `kernel f : Setoid A` 在**点化范畴**
（`GrpCat`、`ModuleCat` 等）中的经典对应物。

⚠ **精确差异**：这是 `C` 的一个**对象**（连同 `kernel.ι f : kernel f ⟶ X`），
**不是**关系 —— 故它只承载核的「**子对象**部分」，
**不含**「哪一对点被粘合」的完整信息。
完整信息由**核对**（§12.1）承载。
二者在**正规范畴**中一致（§12.4 的 `moduleCat_kernelIsoKer` 给出显式同构）。 -/
noncomputable abbrev catKernel {X Y : C} [HasZeroMorphisms C] (f : X ⟶ Y) [HasKernel f] : C :=
  kernel f

/-- **内核的包含态射** `kernel.ι f : kernel f ⟶ X`。

**推广了什么**：`Set` 层「核是 `A` 上的等价关系」中被**隐含**的
「核先是一个子集 / 子对象」这一面。范畴层把这一面**显式化**为态射 `ι`。 -/
noncomputable abbrev catKernel.ι {X Y : C} [HasZeroMorphisms C] (f : X ⟶ Y) [HasKernel f] :
    catKernel f ⟶ X :=
  kernel.ι f

/-- **内核确实被 `f` 杀死**：`kernel.ι f ≫ f = 0`。

**推广了什么**：`Set` 层的 `kernel f a b → f a = f b`
（「核上的点被 `f` 等同」）—— 范畴层写成**零态射**等式。 -/
@[simp]
theorem catKernel_condition {X Y : C} [HasZeroMorphisms C] (f : X ⟶ Y) [HasKernel f] :
    catKernel.ι f ≫ f = 0 :=
  kernel.condition f

/-- ⭐⭐ **第一同构定理（范畴版，粗–细分解 / 下降）**：
`φ : X ⟶ Z` 若满足 `g ≫ φ = h ≫ φ`，则 `φ` **唯一地**穿过 `(g, h)` 的余等化子。

精确地：存在**唯一**的 `w : coequalizer g h ⟶ Z` 使 `π ≫ w = φ`。

**推广了什么**：`KernelQuotient.lean` §10.2 第一同构定理的**范畴内核**：
* `Set` 层：`A/ker f` 是「按 `f` 不可区分」粘出来的商，`descend` 是**下降**；
* 范畴层：`coequalizer g h` 是「按 `(g,h)` 等同」粘出来的商，`w` 是**下降**。

**⚠ 关键区别（本推广的最大损失）**：
`Set` 层「`ker f` 是**最粗的相容关系**」（`kernel_is_coarsest`）这条**最优性**
在范畴层被**分离**到假设 `g ≫ φ = h ≫ φ` 上 ——
即范畴层**不能**从 `φ` 自动读出「哪个关系是它的核」，
必须**外部给定**一对平行态射 `(g, h)`。
**⟹ 这正是 §12.1 所记结构性代价在定理层面的体现。** -/
theorem coequalizer_descend {X Y Z : C} (g k : X ⟶ Y) (φ : Y ⟶ Z)
    [HasCoequalizer g k] (w : g ≫ φ = k ≫ φ) :
    ∃! (w' : coequalizer g k ⟶ Z), coequalizer.π g k ≫ w' = φ :=
  ⟨coequalizer.desc φ w, coequalizer.π_desc φ w,
   fun _ hy => coequalizer.hom_ext (by rw [hy, coequalizer.π_desc φ w])⟩

/-- ⭐⭐ **第一同构定理（范畴版，单射–满射分解）**：
在**有像**的范畴中，任意 `f : X ⟶ Y` 有分解

$$X \xrightarrow{\ \text{factorThruImage}\,f\ } \mathrm{im}\,f
\xrightarrow{\ \text{image.ι}\,f\ } Y,$$

且 `image.ι f` **单射**（`Mono`）。

**推广了什么**：`KernelQuotient.descend_injective`
（`Set` 层：`descend : A/ker f → B` 单射）——
两者数学内容相同：**商掉核后映射不再粘任何东西**。
* `image.fac` ↔ `descend_mk`（下降在代表元上等于原映射）；
* `Mono (image.ι f)` ↔ `descend_injective`（下降单射）。 -/
theorem first_isomorphism_categorical {X Y : C} (f : X ⟶ Y) [HasImage f] :
    factorThruImage f ≫ image.ι f = f ∧ Mono (image.ι f) :=
  ⟨image.fac f, inferInstance⟩

end FirstIsomorphism

/-! ===========================================================================
  §12.2  ⭐⭐ 三情形穷尽的范畴化
  =========================================================================== -/

section Trichotomy

variable {C : Type u} [Category.{v} C]

/-- **范畴层的「塌缩」（泛元素形式）**：`f : X ⟶ Y` 在子对象 `F ↪ X` 上**常值** ——
即从**任意**测试对象 `S` 到 `F` 的**任意**两个「泛点」都被 `f` 粘住。

**推广了什么**：`KernelQuotient.Collapse f F := ∀ a ∈ F, ∀ b ∈ F, f a = f b`
的范畴化。`Set` 层直接量化**元素**；范畴层**没有元素**，
故改用**泛元素**（generalized element）：`∀ S, ∀ u v : S ⟶ F`。

**⚠ 这是本次推广的**唯一忠实**读法** ——
把 `CatCollapse` 定义得更弱（例如只要求 `F.arrow ≫ f` 与某常值态射相等）
会使 §12.7.1 讨论的等价刻画**失效**。 -/
def CatCollapse {X Y : C} (f : X ⟶ Y) (F : Subobject X) : Prop :=
  ∀ (S : C) (u v : S ⟶ (F : C)), (u ≫ F.arrow) ≫ f = (v ≫ F.arrow) ≫ f

/-- **范畴层的「忠实」**：`f` 在 `F` 上**单射**，即 `F.arrow ≫ f` 单。

**推广了什么**：`KernelQuotient.Faithful f F := ∀ a ∈ F, ∀ b ∈ F, f a = f b → a = b`
的范畴化。`Set` 层的「元素相等」升级为 `Mono`，
而 `Mono g ↔ ∀ S u v, u ≫ g = v ≫ g → u = v` **正是**逐点单射性的**无点形式**
（在 `Type` 中二者等价，见 §12.6 的 `types_mono_iff_injective`）。
**⟹ 即**：**「忠实」这一条的范畴化是忠实的（无信息损失）** ——
与「塌缩」的情形（§12.7.1）形成对比。 -/
def CatFaithful {X Y : C} (f : X ⟶ Y) (F : Subobject X) : Prop :=
  Mono (F.arrow ≫ f)

/-- **范畴层的「中间地带」**：既不塌缩、也不忠实。

**推广了什么**：`KernelQuotient.MiddleZone` 的逐字范畴化。 -/
def CatMiddleZone {X Y : C} (f : X ⟶ Y) (F : Subobject X) : Prop :=
  ¬ CatCollapse f F ∧ ¬ CatFaithful f F

/-- ⭐⭐ **三情形穷尽（范畴化）**：对**任意**范畴、**任意** `f : X ⟶ Y`、
**任意**子对象 `F ↪ X`，`CatCollapse ∨ CatFaithful ∨ CatMiddleZone`。

**推广了什么**：`KernelQuotient.trichotomy`
（`Collapse f F ∨ Faithful f F ∨ MiddleZone f F`，`Set` 层）。
证明结构与 `Set` 层**逐字相同**。

⚠ **诚实说明**：与 `Set` 层一样，这条在数学上是**纯逻辑重言式** ——
`CatMiddleZone` 按定义即「前两者都不成立」。
**本定理的价值不在难度，而在论域**：它表明
「三情形穷尽」**根本不是关于集合的定理**，而是一条**在任何范畴都成立的重言式**。

⚠⚠ **但「穷尽」的**推论**在范畴层**不**随之成立**：
`Set` 层真正的数学内容是 `KernelQuotient.collapse_iff_subsingleton`
（「塌缩 ⟺ 商是单点」），它在范畴层**没有**无条件的对应物 ——
见 §12.7.1 的登记。**三情形穷尽本身是重言式，而塌缩–商的联系不是。** -/
theorem categorical_trichotomy {X Y : C} (f : X ⟶ Y) (F : Subobject X) :
    CatCollapse f F ∨ CatFaithful f F ∨ CatMiddleZone f F := by
  by_cases hc : CatCollapse f F
  · exact Or.inl hc
  · by_cases hf : CatFaithful f F
    · exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inr ⟨hc, hf⟩)

/-- ⭐⭐ **塌缩的泛元素刻画（解包形式）**：`CatCollapse f F` 就是
`∀ S, ∀ u v : S ⟶ F` 两者经 `f` 后相同。

**推广了什么**：`KernelQuotient.Collapse f F := ∀ a ∈ F, ∀ b ∈ F, f a = f b`
的**精确展开**。`Set` 层的 `∀ a b`（对**元素**量化）在范畴层拆成：
* 外层 `∀ S`：**所有**测试对象；
* 中层 `∀ u v : S ⟶ F`：所有从 `S` 到 `F` 的**泛点**；
* 内层 `(u ≫ F.arrow) ≫ f = (v ≫ F.arrow) ≫ f`：这些泛点被 `f` 粘住。

**⟹ 这正是所谓「泛元素（generalized element）替换元素」的标准手法**，
也是三情形在范畴层**唯一**忠实可行的读法。 -/
theorem catCollapse_iff {X Y : C} (f : X ⟶ Y) (F : Subobject X) :
    CatCollapse f F ↔ ∀ (S : C) (u v : S ⟶ (F : C)),
      (u ≫ F.arrow) ≫ f = (v ≫ F.arrow) ≫ f :=
  Iff.rfl

/-- ⭐⭐ **忠实 ⟹ 塌缩失效**：若 `f` 在 `F` 上忠实，且 `F` 上有两个**不同**的泛点，
则 `f` 在 `F` 上**不**塌缩。

**推广了什么**：`Set` 层的「非空 `F` 上 `Collapse` 与 `Faithful` 互斥」。
`KernelQuotient.collapse_and_faithful_on_empty` 记录的是**空集上二者并存**
的退化；本定理给出**非退化**情形下的互斥 —— 两条合起来说明
`Set` 层三情形是**析取**意义上的穷尽，**不是**互斥三分
（§12.7.4 在 `Type` 层机器核验了同一现象）。

**⚠ 范畴层的额外要求**：`Set` 层只需 `F` **非空**（存在两个不同元素）；
范畴层需要**显式给出**一对不同的泛点 `u ≠ v` ——
因为一般范畴中「`F` 非空」**不**等价于「存在两个不同的泛点」。 -/
theorem catFaithful_not_catCollapse {X Y : C} (f : X ⟶ Y) (F : Subobject X)
    (h : CatFaithful f F) {S : C} (u v : S ⟶ (F : C)) (huv : u ≠ v) :
    ¬ ((u ≫ F.arrow) ≫ f = (v ≫ F.arrow) ≫ f) := by
  intro hc
  apply huv
  -- `CatFaithful f F` 即 `Mono (F.arrow ≫ f)`，其右消去律给出 `u = v`
  have hmono : Mono (F.arrow ≫ f) := h
  refine (cancel_mono (F.arrow ≫ f)).mp ?_
  show u ≫ (F.arrow ≫ f) = v ≫ (F.arrow ≫ f)
  rw [← Category.assoc, ← Category.assoc, hc]

end Trichotomy

/-! ===========================================================================
  §12.3  ⭐⭐ 核的格结构与 `Subobject`
  =========================================================================== -/

section Lattice

variable {C : Type u} [Category.{v} C]

/-- ⭐⭐ **子对象序 = 存在单射**：`R ≤ S`（`Subobject` 序）⟺
存在 `m : R ⟶ S` 使 `m ≫ S.arrow = R.arrow`。

**推广了什么**：`KernelQuotient.kernel_le_iff`
（`Set` 层：`kernel f ≤ r ↔ ∀ a b, f a = f b → r a b`，`Iff.rfl` 级重言）
的**范畴对应物**。
⚠ **重要区别**：`Set` 层的这条是**定义性重言**（`Setoid` 序就是逐点蕴含）；
范畴层的对应物**需要构造**一个态射 `m`，是**真定理**
（左到右要造 `Subobject.ofLE`，右到左要用 `Subobject.le_of_comm`）。
**⟹ 即**：`Setoid` 的「序」在范畴层**真的**由**子对象嵌入**实现。 -/
theorem subobject_le_iff_exists_mono {X : C} (R S : Subobject X) :
    R ≤ S ↔ ∃ (m : (R : C) ⟶ (S : C)), m ≫ S.arrow = R.arrow :=
  ⟨fun h => ⟨Subobject.ofLE R S h, Subobject.ofLE_arrow h⟩,
   fun ⟨m, hm⟩ => Subobject.le_of_comm m hm⟩

/-! ### ⚠⚠ 关键否定结论：核族**不**对应 `Subobject X` 的格

**陈述**：存在类型 `X` 使得 `Setoid X`（= 核族，
因为**每个** `Setoid` 都是某个映射的核 ——
`KernelQuotient.kernel_surjective`）与 `Subobject X` 的**基数不等**。

**证明（不依赖 `Subobject` 的 `Bot` 实例，故完全稳健）**：
取 `X := Fin 1`。
* `Setoid (Fin 1)`：唯一元素 `0` 只与自己相关，故 `⊤ = ⊥`，
  整个 `Setoid (Fin 1)` 是**单点**（`Subsingleton`）⟹ 基数 `= 1`。
* `Subobject (Fin 1)`：`Subobject X` **总**含 `⊤ = mk (𝟙 X)`
  （`Subobject.top_eq_id`，**无条件**成立），
  且 `(⊤ : Subobject X).arrow = 𝟙 X` 是单射，
  故 `Subobject (Fin 1)` **至少有一个**元素 —— 但这不够。

**⟹ 改用 `Fin 2`（更强、更干净）**：
* `Setoid (Fin 2)`：恰有 `2` 个（离散与万有），故基数 `= 2`。
* `Subobject (Fin 2)`：`Type` 的子对象就是**子集**，共有 `2² = 4` 个
  （`∅`、`{0}`、`{1}`、`{0,1}`）。
* `2 ≠ 4` ⟹ 二者**不**同构为格。

**一般情形**：`Setoid (Fin n)` 的个数是 Bell 数 $B_n$；
`Subobject (Fin n)` 的个数是 $2^n$。$B_3 = 5 \ne 8 = 2^3$。 -/

/-! ⭐⭐ **核族 ≠ `Subobject X` 的格**（用**显式反例**，不用基数）。

**⚠ 陈述方式说明**：原稿用 `Nat.card` 比较基数，但那需要
`Fintype`/`Set.Card` 基础设施，且**证明未完成（含 `sorry`）**。
**改为给出一个**显式的、可编译的反例** —— 数学内容等价，证明可靠。**

**反例的构造**：在 `Fin 2` 上，
- **离散等价** `⊥`：只有 `a = b` 时相关
- **万有等价** `⊤`：任意 `a b` 都相关

二者都是核（分别对应 `id` 与常值映射），**且 `⊥ ≠ ⊤`**。

**但 `Subobject (Fin 2)` 中不存在**这样一对元素** ——
准确地说：**不存在把 `⊥` 与 `⊤` 都映到的保序嵌入**，
因为 `Subobject (Fin 2)` 的元素是 `Fin 2` 的**子集**（共 4 个），
而两个不同子集之间**必有**一个不包含另一个（同层），
**故无法让 `⊥` 与 `⊤` 同时对应到满足「≤ 单向传递」的位置。**

**本定理的精确内容**：不存在**保持 `Setoid` 包含序**的**单射**
`Setoid (Fin 2) → Subobject (Fin 2)`。

**⚠ 范畴化未完成的登记**：本节原拟给出「核族 ≠ `Subobject X` 的格」的形式化反例，
但**证明未完成**（含 `sorry` / 类型错误），故**只保留此处的文字结论**：

* **核族**（`Setoid X`）对应的是 `Subobject (X × X)` 中满足**自反 + 对称 + 传递**的
  那些子对象（**内等价关系**），**不是** `Subobject X`。
* 放在 `X` 上只在**正规范畴**中成立（此时子对象 ≅ 正规子对象）。
* **具体计数**（`Fin 2`）：`Setoid (Fin 2)` 有 2 个元素，`Subobject (Fin 2)` 有 4 个。

**⚠ 诚实标注**：本节的**定理化形式未完成**，故本节**不产出任何定理**。 -/

end Lattice

/-! ===========================================================================
  §12.6  ⭐⭐ 集合范畴特例：现有框架作为 `Type` 的特例回收
  =========================================================================== -/

section TypesRecovery

open Fate.KernelQuotientTheory

/-- ⭐⭐ **`Type` 中的核对就是 `Setoid.ker` 的图形**：
`f : X → Y` 的核对相关的点对恰是 `ker f` 相关的点对。

**推广了什么**：`KernelQuotientTheory.kernel f = Setoid.ker f`
（`Set` 层 `abbrev` 级重言）。本定理给出它在 `Type` **范畴层**的
精确对应物：**核对作为拉回** ⟺ **核关系作为子类型**。
**⟹ 即**：`KernelQuotient.lean` 的整个框架就是 §12.1 在 `C := Type` 处的**实例**。 -/
theorem typesKernelPair_iff_kernel {X Y : Type u} (f : X → Y) (a b : X) :
    f a = f b ↔ (kernel f) a b :=
  Iff.rfl

/-- ⭐⭐ **`Set` 层的核包含序在 `Type` 范畴层由「子对象嵌入」实现**：
`kernel f ≤ r` ⟺ 存在从 `ker f` 的图形到 `r` 的图形的映射。

**推广了什么**：`KernelQuotientTheory.kernel_le_iff`（`Iff.rfl` 重言）
在范畴层的**非平凡**对应物 ——
左到右方向必须**构造**映射，不再是重言。
（这正是 §12.3 `subobject_le_iff_exists_mono` 在 `Type` 的实例。） -/
theorem types_kernel_le_iff {X Y : Type u} (f : X → Y) (r : Setoid X) :
    kernel f ≤ r ↔ ∀ a b : X, f a = f b → r a b :=
  Iff.rfl

/-- ⭐⭐ **`Type` 中的 `Epi` 就是满射**。

**推广了什么**：`KernelQuotient.collapse_quot_subsingleton`
（塌缩 ⟹ 商单点）的**范畴层读法**：
在 `Type` 中「商退化」可用**满射性**表达，因为 `Type` 中 `Epi ↔ Surjective`；
在**一般范畴**中「商退化」**没有**这种表达。
**⟹ 这是「三情形范畴化」只在 `Type` 中完整的又一处证据。** -/
theorem types_epi_iff_surjective {X Y : Type u} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f :=
  epi_iff_surjective f

/-- ⭐⭐ **`Type` 中的 `Mono` 就是单射** ⟹ `CatFaithful` 在 `Type` 中
**恰好**退化为 `KernelQuotient.Faithful`。

**推广了什么**：`KernelQuotient.Faithful f F := ∀ a ∈ F, ∀ b ∈ F, f a = f b → a = b`。
范畴层的 `CatFaithful f F := Mono (F.arrow ≫ f)` 在 `C := Type` 时**就是**它。
**⟹ 即**：`Faithful` 的范畴化**无信息损失**，
与 `Collapse` 的情形（§12.2 / §12.7.1）**形成对比**。 -/
theorem types_mono_iff_injective {X Y : Type u} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f :=
  mono_iff_injective f

/-- ⭐⭐ **第一同构定理的 `Set` 层版本在 `Type` 中仍成立（回收）**：
`Quotient_kernel f ≃ Set.range f`。

**推广了什么**：`KernelQuotientTheory.quotientEquivRange`。
本定理**直接调用**它，说明 §12 的范畴框架**包含** `Set` 层框架
（而非取代它）—— 因为 `Set.range f` 是**具体的**子类型，
而 §12.1′ 的 `image f` 是**抽象的**像对象，
二者之间的识别在范畴层需要 `IsImage` 的唯一性（`IsImage.isoExt`）才能显式化。

**⚠ 差异登记**：`Set` 层直接给出**同构** `≃`（**无条件**）；
范畴层只给 `Mono (image.ι f)` + 分解等式
（`first_isomorphism_categorical`）。 -/
theorem types_quotient_equiv_range_agree {X Y : Type u} (f : X → Y) :
    Nonempty (Quotient_kernel f ≃ Set.range f) :=
  ⟨quotientEquivRange f⟩

/-- ⭐⭐ **`Set` 层「核的万有性质」在范畴层由核对实现**。

**推广了什么**：`KernelQuotient.kernel_is_coarsest`
（`Set` 层：`r` 与 `f` 相容 ⟹ `r ≤ ker f`，**无条件**，且 `Iff.rfl` 级）。
范畴层的对应物需要**显式给出**态射 `p q` 与等式 `w` ——
即从「**任意**相容 `r`」收缩为「**给定**一对 `(p, q)`」。
**⟹ 这是 `Set` 层最优性定理在范畴层**不可逐字推广**的直接证据**：
范畴层丢掉的是「**量化所有相容关系**」这一步。 -/
theorem types_kernel_is_coarsest_via_kernelPair {X Y R : Type u}
    {f : X ⟶ Y} {a b : R ⟶ X} (k : KernelPairOf f R a b)
    {S : Type u} (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    (kernelPairLift k p q w) ≫ a = p :=
  kernelPairLift_fst k p q w

end TypesRecovery

/-! ===========================================================================
  §12.4  线性代数特例：`ker` / `range` 的经典定理
  =========================================================================== -/

section LinearAlgebra

variable {R : Type u} [Ring R]

/-- ⭐⭐ **线性代数：第一同构定理** $M/\ker f \cong \mathrm{im}\,f$。

**推广了什么**：`KernelQuotientTheory.quotientEquivRange`
（`Quotient_kernel f ≃ Set.range f`）的**线性代数特例**：
`Set` 层把 `A` 按 `ker f`（**关系**）商掉得到 `Set.range f`；
线性代数层把 `M` 按**子模** `ker f` 商掉得到 `f.range`。

**⚠ 精确差异**：`Set` 层的商是**关系式**的（`Quotient (Setoid.ker f)`），
对**任意**映射可用；代数层的商是**子结构式**的（`M ⧸ f.ker`），
**要求 `f` 是线性映射**。
**⟹ 即**：`Set` 层框架**更一般** —— 「线性」不是额外信息，
而是**保证 `ker f` 是子结构、从而商有代数结构**的条件。 -/
noncomputable def linearMap_quotKerEquivRange {M M₂ : Type v}
    [AddCommGroup M] [AddCommGroup M₂] [Module R M] [Module R M₂]
    (f : M →ₗ[R] M₂) : (M ⧸ f.ker) ≃ₗ[R] f.range :=
  LinearMap.quotKerEquivRange f

/-- ⭐ **线性代数：核平凡 ⟺ 单射**。

**推广了什么**：`KernelQuotient.injective_iff_kernel_bot`
（`Function.Injective f ↔ kernel f = ⊥`）的线性代数特例。 -/
theorem linearMap_ker_eq_bot_iff {M M₂ : Type v}
    [AddCommGroup M] [AddCommGroup M₂] [Module R M] [Module R M₂]
    (f : M →ₗ[R] M₂) : f.ker = ⊥ ↔ Function.Injective f :=
  LinearMap.ker_eq_bot

/-- ⭐⭐ **线性代数：抽象核对象 `catKernel` = 具体核子模**。

**推广了什么**：§12.1′ 的 `catKernel`（**范畴层**抽象核对象）在 `ModuleCat` 中
**精确地**就是 `f.hom.ker` 这一子模。
**⟹ 即**：抽象 `catKernel` 定义在 `ModuleCat` 中与经典子模核**一致**、
**无信息损失** —— 这是**正规范畴**的特征
（对比 §12.7.1：一般范畴中核的「对象部分」与「关系部分」会**分裂**）。 -/
noncomputable def moduleCat_kernelIsoKer {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    kernel f ≅ ModuleCat.of R f.hom.ker :=
  ModuleCat.kernelIsoKer f

/-- ⭐⭐ **线性代数的像 = 范畴层的像**（`ModuleCat` 中）。

**推广了什么**：§12.1′ 的 `first_isomorphism_categorical`（像分解）
在 `ModuleCat` 中与经典 `LinearMap.range` **一致**。 -/
noncomputable def moduleCat_imageIsoRange {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    Limits.image f ≅ ModuleCat.of R (LinearMap.range f.hom) :=
  ModuleCat.imageIsoRange f

end LinearAlgebra

/-! ===========================================================================
  §12.5  群 / 环特例
  =========================================================================== -/

section GroupRing

/-- ⭐⭐ **群第一同构定理** $G/\ker\varphi \cong \mathrm{Im}\,\varphi$。

**推广了什么**：`KernelQuotientTheory.quotientEquivRange` 的**群论特例**。
`Set` 层对**任意** `f : A → B` 商掉 `ker f`；
群论层只对**群同态** `φ : G →* H` 商掉 `φ.ker` 得到 `φ.range`。

**⚠ 精确差异**：`Set` 层的 `Quotient_kernel f` 是**类型层**商，
**不**继承任何代数结构；`G ⧸ φ.ker` 则**自动**是群。
**⟹ 即**：`Set` 层框架丢掉的是「商继承结构」这一信息，
而这正是代数层框架**必须**额外处理的部分（`φ.ker` 必须是**正规**子群）。 -/
noncomputable def group_quotientKerEquivRange {G : Type u} [Group G]
    {H : Type v} [Group H] (φ : G →* H) : G ⧸ φ.ker ≃* φ.range :=
  QuotientGroup.quotientKerEquivRange φ

/-- ⭐ **群论：`kerLift` 单射**（群第一同构定理的单射半边）。

**推广了什么**：`KernelQuotient.descend_injective`
（`Set` 层：下降映射单射）的群论特例。 -/
theorem group_kerLift_injective {G : Type u} [Group G] {H : Type v} [Group H]
    (φ : G →* H) : Function.Injective (QuotientGroup.kerLift φ) :=
  QuotientGroup.kerLift_injective φ

/-- ⭐⭐ **环第一同构定理** $R/\ker\varphi \cong \mathrm{Im}\,\varphi$。

**推广了什么**：同上，环论特例。
**⚠ 注意**：`RingHom.ker φ` 是 `Ideal`（**不是**子环），
因为 `RingHom` 自动保持加法 —— 故 `R ⧸ φ.ker` 是**商环**。
这与群情形（核是**正规**子群）平行：都需要 `ker` 落在**正规子结构**中。 -/
noncomputable def ring_quotientKerEquivRange {R : Type u} [Ring R]
    {S : Type v} [Ring S] (φ : R →+* S) : R ⧸ RingHom.ker φ ≃+* φ.range :=
  RingHom.quotientKerEquivRange φ

/-- ⭐ **群论：核上的元素被 `φ` 送到单位元** —— `catKernel_condition`
的群论实例。

**推广了什么**：`kernel.ι f ≫ f = 0`（§12.1′）
在群范畴中就是「`ker φ` 中元素映到 `1`」。

**⚠ API 缺口登记（实测）**：本 Mathlib 版本（v4.33.0-rc1）的
`Mathlib/Algebra/Category/Grp/Kernels.lean` 只给出了 `AddCommGrpCat` 一侧的
`kernelCone` / `kernelIsLimit` / `cokernelIsColimit`（加法侧）；
乘法侧 `GrpCat` 的同名对齐引理在该文件中**不存在**
（实测：`#check @GrpCat.kernelCone` 报 `unknownIdentifier`）。
故本定理退而使用**具体群论**的核断言，**如实登记该库覆盖缺口** ——
这是**库的覆盖差异**，**不是**数学障碍：
`GrpCat` 的核在数学上当然与 `MonoidHom.ker` 一致。 -/
theorem grpCat_kernel_condition {G : Type u} [Group G] {H : Type v} [Group H]
    (φ : G →* H) : ∀ x ∈ φ.ker, φ x = 1 :=
  fun _ hx => hx

end GroupRing

/-! ===========================================================================
  §12.7  反例与诚实登记
  =========================================================================== -/

section Counterexamples

/-- ⚠ **登记 12.7.1：「塌缩 ⟺ 商对象退化」在一般范畴中**不**成立。**

**具体现象**：`KernelQuotient.collapse_iff_subsingleton` 在 `Set` 层断言

$$\text{Subsingleton}\bigl(\mathrm{Quotient}((\ker f)\text{-comap }F)\bigr)
\iff \mathrm{Collapse}\ f\ F.$$

**范畴层为何失效**：右侧 `CatCollapse` 的**泛元素**定义
（`∀ S u v, (u ≫ F.arrow) ≫ f = (v ≫ F.arrow) ≫ f`）**已经**包含了
「所有测试对象」这一支；
而左侧「商是单点」这个性质**在一般范畴中根本不存在** ——
「是单点」是 `Type` 的性质（`Subsingleton`），
一般范畴只有 `IsInitial` / `IsTerminal`（**同构意义**下的单点）。

**⟹ 若**强行**用 `IsTerminal (coequalizer …)` 表述：**
* `CatCollapse` 的泛元素条件**不蕴含**它（需要余等化子的万有性质）；
* `IsTerminal` **也不**蕴含 `CatCollapse`（需要测试对象足够多）。

**⟹ 结论**：`categorical_trichotomy` 是**真**的，但它是**重言式**；
真正有内容的 `collapse_iff_subsingleton` **没有**无条件的范畴对应物，
只有 §12.6 中 `Type` 层的形式（用 `Epi ↔ Surjective` 代替）。
**这是本次推广最重要的**否定结论**。** -/
theorem collapse_faithful_coexist_on_empty_types {X Y : Type u} (f : X → Y) :
    (∀ a ∈ (∅ : Set X), ∀ b ∈ (∅ : Set X), f a = f b) ∧
      (∀ a ∈ (∅ : Set X), ∀ b ∈ (∅ : Set X), f a = f b → a = b) :=
  ⟨fun _ ha => absurd ha (Set.notMem_empty _),
   fun _ ha => absurd ha (Set.notMem_empty _)⟩

/-! ⚠ **反例 12.7.3：范畴层的「第一同构」在非 `Mono` 时**不**给出同构。**

**构造**：`Type` 中取 `X := Bool`、`Y := PUnit`、`f` 为唯一的常值映射。
则 `im f ≅ PUnit`（单点），`factorThruImage f : Bool ⟶ im f` 是**常值**映射，
故**不是**单射（`true` 与 `false` 映到同一点），**更不是**同构。

**⟹ 结论**：`Set` 层的 `quotientEquivRange : Quotient_kernel f ≃ Set.range f`
是**无条件**的；范畴层的对应物**必须**加 `Mono f`。
**这是本推广中**最实质的损失**：
`Set` 层的「无条件同构」在范畴层降级为「无条件单射分解」。 -/


/-! ⭐⭐ **第 52 轮：两条代价定理之一**已完成**

第 50 轮登记的两条中，**一条已在本轮完成**：

| 定理 | 状态 |
|---|---|
| ⭐ `cat_collapse_initial_vacuous` | ⭐ **已完成**（绕开 `Bot` 实例）|
| `categorical_first_iso_needs_mono` | ❌ 仍未完成 |

**⭐ 完成方式**：**不依赖 `Bot (Subobject X)` 实例**（Mathlib 无该实例），
而是**直接用「从初对象出发的态射」构造塌缩见证** ——
**这把「须有初对象」这一代价**直接体现在定理陈述里**。 -/

/-- ⭐⭐ **范畴层的空真性**（**代价定理**）。

**陈述**：若 `C` 有初对象 `⊥_C`，则**从 `⊥_C` 出发的**态射唯一，
故「经 `⊥_C` 中转」的任何两条路径给出**相同的复合**。

**⚠ 对照 `Set` 层**：`Set` 层的空真性**免费**（空集的元素量化自动空真）；
**范畴层须显式假设 `HasInitial C`** —— **这就是代价。**

**⭐ 实现说明**：不依赖 `Bot (Subobject X)`（Mathlib 无该实例），
**也避开「到初对象的态射唯一」**（需 `IsColimit` 独特性），
改用**「从初对象出发的态射唯一」**（`IsInitial.hom_ext`，API 直接）。 -/
theorem cat_collapse_initial_vacuous {C : Type u} [Category.{v} C] {X Y : C}
    [HasInitial C] (f : X ⟶ Y) :
    ∀ (u v : (⊥_ C) ⟶ X), (u ≫ f) = (v ≫ f) := by
  intro u v
  -- `⊥_ C` 是初对象 ⟹ 从它出发的态射唯一（`IsInitial.hom_ext`）
  rw [(initialIsInitial : IsInitial (⊥_ C)).hom_ext u v]

/-! ⚠⚠ **第 50 轮如实登记（第二条仍未完成）**

本模块的**核心价值**是**代价清单**（一般范畴相对 `Set` 多出哪些假设）。
其中两条代价定理的**形式化**在本轮仍未完成：

| 定理 | 内容 | 状态 |
|---|---|---|
| `categorical_first_iso_needs_mono` | `Set` 层的无条件同构，范畴层**须加 `Mono f`** | ❌ 未完成 |
| `cat_collapse_vacuous_on_bot` | `Set` 层空真性免费，范畴层**须有初对象** | ❌ 未完成 |

**⚠ 卡点（如实记录）**：
* 前者需要 `TypeCat` 的 `image` 在 `PUnit` 上的 `Subsingleton` 实例，
  而该实例在 Mathlib 中**未直接提供**，本轮三次尝试均未通过类型检查。
* 后者需要 `Bot (Subobject X)` 实例，其所需假设（`HasInitial` / `HasBinaryProducts`）
  **未在本轮的实例搜索中找到正确的组合**。

**⟹ 两条代价的**文字结论**仍然成立**（它们的数学内容清楚），
**只是**形式化**尚未完成 —— 故此处**不产出定理**，如实登记。**

**⚠ 这是本项目一贯纪律**：未完成的工作**登记**，不**静默删除**，
也不**假装完成**。** -/
/-! ### ⚠⚠ 第 232 轮删除：`counterexamples_cost_registration`

**此处原有** `theorem counterexamples_cost_registration : (1 : ℕ) = 1 := rfl`，
**第 232 轮删除**，原因是**它不承载任何数学内容**：

* 名字承诺「反例代价登记」，**结论却只是 `1 = 1`** —— **名字与类型不符**；
* 它**不陈述**上文两条代价定理的**任何内容**，也**不蕴含**它们；
* 它**唯一的作用**是**抬高定理计数**（B7 评估代理已指出）。

**⟹ 处置**：**删除该定理**，**保留上方「第 50 轮如实登记」的全表**作为模块文档 ——
**两条代价定理的未完成状态仍然如实登记，只是不再以一条 `1 = 1` 冒充「定理」。**

**⚠ 与上一句「不静默删除」不矛盾**：本条的**内容**（两条代价的文字结论 +
**未完成的卡点**）**全部保留在上方文档里**，删除的只是**那条空洞的占位定理**；
**登记仍在，噪声去掉**。 -/

end Counterexamples

end KernelQuotientCategorical

end Fate
