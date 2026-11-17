/-
命运理论 · 方案二：随机递推（噪声按分布采样），轨迹是随机过程
============================================================

模块：Fate.TrajGenStochastic
上游：`第9问-TrajGen三种实现方案.md`（方案 A/B/C/D）、`Fate/Frame.lean`（`Step`、`TrajGen`）、
　　　`Fate/Basic.lean`（`Traj`、`InitialState`、`Dist`、`Tmax`）。

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
把 `TrajGen` 的**值域**从「一条轨迹」`ι → X` 升级为「轨迹上的概率测度」
`Measure (Traj ι X)`，用**噪声按分布采样 → 逐步递推 → 推前**的方式构造它。
由此得到的对象是一条**随机过程**（ρ），而不是一条样本路径（方案 A 的对象）。

---------------------------------------------------------------------------
与方案 A（原始递归）的关系（诚实标注，非等价）
---------------------------------------------------------------------------
方案 A 计算的是**给定噪声序列后**的一条样本路径：
    x_{n+1} = f(x_n, u_n, ε_n; θ, a_n)         （逐点确定）
本方案计算的是**噪声未定、按分布采样**时，整条轨迹的**分布**：
    ρ = Law( x_0, ε_0, …, ε_{T-1} ) under x_0 ~ D₀, ε_t ~ D_ε   （测度）
二者**不同型**（`Traj ι X` vs `Measure (Traj ι X)`），**不是同一个函数**。
唯一可以证明的关系是「逐样本路径一致性」（本文件 §4）：
  在**给定**一条噪声实现 ω 时，方案二展开出的样本路径恰等于方案 A 的输出。

---------------------------------------------------------------------------
时间索引的选择（为什么用有限视窗 Fin T）
---------------------------------------------------------------------------
`Measure.pi`（独立积测度）在 Mathlib 中要求**有限**索引。
规格 §2.1 规则 T2 本就规定「有限观测窗口的时间上界 T_max」，
故本实现取 $\iota = \mathrm{Fin}\ T$（有限离散视窗），**完全贴合规格**。
无穷索引（ℕ）需 Kolmogorov 扩张定理，属**外部理论**，
本文件**不使用**、**不假设**，登记为开放项（见 §7 末）。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 全程零 `sorry` / 零 `axiom`。构造性部分标 `noncomputable`（`Measure` 所致）。
- 凡「需要外部输入」者（噪声分布、初始分布）一律作**显式参数**，
  不偷偷塞进定义，不在类型层撒谎。
- 若本方案与既有 `TrajGen` 类型**不兼容**，**据实登记为类型层结论**，不冒充实现。
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
namespace FateV2.Model

open FateV2.Modeling
open MeasureTheory
open scoped ENNReal

noncomputable section

/-!
  # Model · TrajGenStochastic

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TrajGenStochastic.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  方案二的输入：噪声/初始状态的**分布**，而非取值
    =========================================================================== -/

/-- **初始状态分布** $\mathcal{D}_0$（规格 §1.1：$x_0\sim\mathcal{D}_0$）。

`InitialState.isRandom = true` 时，$x_0$ 由 $\mathcal{D}_0$ 采样；
本定义把这个「按分布给定」正式表示为一个概率测度。

标签：**[定义性约定]**（补出规格只以记号给出的 $\mathcal{D}_0$ 的载体）。 -/
abbrev InitDist (F : Frame) [MeasurableSpace F.X.Carrier] : Type _ :=
  MeasureTheory.Measure F.X.Carrier

/-- 噪声序列的**联合分布**：$\mathcal{D}_\varepsilon^{\otimes\iota}$
（有限视窗 $\iota=\mathrm{Fin}\ T$）。

本方案取**独立同分布**（i.i.d.）噪声——规格 §1.2 只写
「$\varepsilon_t\sim\mathcal{D}_\varepsilon$」，未写相关性；
i.i.d. 是**附加假设**，本方案**显式声明**之（见 `IidNoise`），
不当作默认。若日后要相关噪声，须另立定义，不得复用本定义。

标签：**[定义性约定]** + **附加假设（i.i.d.）**。 -/
abbrev NoiseSeqMeasure (F : Frame) [MeasurableSpace F.Ν.Carrier]
    (T : ℕ) (Dε : Dist F.Ν) : MeasureTheory.Measure (Fin T → F.Ν.Carrier) :=
  MeasureTheory.Measure.pi (fun _ : Fin T => Dε)

/-- **i.i.d. 噪声假设的显式载体**：噪声序列测度必须等于 $\mathcal{D}_\varepsilon^{\otimes T}$。

把它做成一个 **Prop**（而非默默使用的默认），使「是否假设 i.i.d.」
成为证明里一个**可见的前件**。这与 `Frame.lean` 中
`DiffusionNoIntervention` 对 A16 的处理同构。

标签：**[定义性约定]**（对应本方案附加假设）。 -/
def IidNoise (F : Frame) [MeasurableSpace F.Ν.Carrier]
    (T : ℕ) (Dε : Dist F.Ν) (P : MeasureTheory.Measure (Fin T → F.Ν.Carrier)) : Prop :=
  P = MeasureTheory.Measure.pi (fun _ : Fin T => Dε)

/-! ===========================================================================
    §2  单步随机转移核（把 `Step` 的噪声位「积分掉」）
    =========================================================================== -/

/-- **单步随机转移核**：固定 $(\theta, a, u)$，把噪声 $\varepsilon\sim\mathcal{D}_\varepsilon$
按 $f$ **推前**到状态的分布。

对 `f : Step F`、噪声分布 `Dε`，定义
$$\kappa\,x = (f\ x\ u\ \cdot\ \theta\ a)_\# \mathcal{D}_\varepsilon,$$
即「一步之后状态的分布」。

**为什么这不是 `Step` 的别名**：`Step` 是**取值到取值**的映射（$x\mapsto x'$）；
本核是**取值到测度**的映射（$x\mapsto \mathrm{Measure}\ X$）。
这正是本方案与方案 A 的**类型分叉点**——方案二必须过这一道测度化。

标签：**[定义性约定]**。 -/
def xNextDist (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] (f : Step F) (Dε : Dist F.Ν)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) (u : F.U.Carrier)
    (x : F.X.Carrier) : MeasureTheory.Measure F.X.Carrier :=
  Measure.map (fun ε => f x u ε θ a) Dε

/-- 点质量噪声下，一步随机转移**塌缩**为方案 A 的一步 `Step`。

$$\mathcal{D}_\varepsilon=\delta_{\varepsilon_0}
   \;\Longrightarrow\; \kappa\,x = \delta_{f(x,u,\varepsilon_0;\theta,a)}.$$

**意义**：随机化的一步在「噪声确定」时退化为确定的一步——
这保证了方案二不是另立动力学，而是方案 A 的**分布层提升**。

需要 `[MeasurableSingletonClass]`——这是**点质量语义**的代价
（在点质量测度上比较，须要求单点可测）。它是前件，**不隐藏**。 -/
theorem xNextDist_dirac (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] [MeasurableSingletonClass F.Ν.Carrier]
    [MeasurableSingletonClass F.X.Carrier] (f : Step F) (ε₀ : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) (u : F.U.Carrier)
    (x : F.X.Carrier) :
    xNextDist F f (Measure.dirac ε₀) θ a u x
      = Measure.dirac (f x u ε₀ θ a) := by
  unfold xNextDist
  rw [Measure.map_dirac]

/-! ===========================================================================
    §3  方案二的主对象：轨迹上的概率测度（随机过程）

    实现路线（递推 + 推前）：以 Fin T 为时间索引，
    令 Ω = X × (Fin T → Ν) 为「初始状态 × 噪声序」的样本空间，
    在 Ω 上放乘测度 P = D₀ ⊗ D_ε^{⊗T}，
    再令「展开映射」unfold : Ω → Traj (Fin T) X 按唯一权威方程递推，
    最后取 ρ = unfold_# P ∈ Measure (Traj (Fin T) X)。
    这条 ρ 就是**随机过程**（其样本是轨迹）。
    =========================================================================== -/

/-- **展开映射** `unfold`（总函数版）：把「初始状态 + 噪声序」按**唯一权威离散方程**
逐点展开为一条状态序列（定义在 ℕ 上）。

$$ \mathrm{unfold}(x_0, \omega)(0) = x_0,\quad
   \mathrm{unfold}(x_0, \omega)(n+1) = f\big(\mathrm{unfold}(x_0,\omega)(n),\ u_n,\ \omega_n;\ \theta,\ a_n\big). $$

取输入/噪声/动作在 ℕ 上全定义，是为了使递推无需携带界限证明。
有限视窗 $\mathrm{Fin}\,T$ 由 §3 的 `trajLaw` 通过**限制/扩展映射**处理。

**与方案 A 的一致性**：给定 $\omega$，`unfold` 的输出**逐点等于**方案 A 的 `detTraj`。
故方案二不是「另立一套动力学」——它的**每条样本路径**仍忠实于唯一权威方程。
这一点由 §4 `unfold_eq_detTraj` 证明（`rfl` 级）。

标签：**[定义性约定]**。 -/
def stateAt (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier)
    (ω : Fin T → F.Ν.Carrier) (x₀ : F.X.Carrier) :
    (n : ℕ) → n ≤ T → F.X.Carrier
  | 0, _ => x₀
  | n + 1, h =>
      f (stateAt F f T θ u a ω x₀ n (Nat.le_of_succ_le h))
        (u ⟨n, by omega⟩) (ω ⟨n, by omega⟩) θ (a ⟨n, by omega⟩)

/-- **展开映射** `unfold`：把「初始状态 + 噪声序」按**唯一权威离散方程**
逐点展开为有限视窗上的一条轨迹。

$$ \mathrm{unfold}(x_0, \omega)(0) = x_0,\quad
   \mathrm{unfold}(x_0, \omega)(n+1) = f\big(\mathrm{unfold}(x_0,\omega)(n),\ u_n,\ \omega_n;\ \theta,\ a_n\big). $$

**与方案 A 的一致性**：给定 $\omega$，`unfold` 的输出**逐点等于**方案 A 的对应轨迹。
故方案二不是「另立一套动力学」——它的**每条样本路径**仍忠实于唯一权威方程。
这一点由 §4 `unfold_succ` 证明（`rfl` 级）。

标签：**[定义性约定]**。 -/
def unfold (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    F.X.Carrier × (Fin T → F.Ν.Carrier) → Traj (Fin T) F.X :=
  fun ω n => stateAt F f T θ u a ω.2 ω.1 n.val (Nat.le_of_lt n.isLt)

/-- §3 的主体：**轨迹上的概率测度** $\rho$（= 随机过程）。

$$\rho = \mathrm{unfold}_\#\big(\mathcal{D}_0 \otimes \mathcal{D}_\varepsilon^{\otimes T}\big).$$

**这是方案二与方案 A 的真正区别所在**：
- 方案 A 的值是 `Traj (Fin T) X`（一条路径）；
- 方案二的值是 `Measure (Traj (Fin T) X)`（路径上的分布）。

$\rho$ 携带了「$x_0$ 随机」「$\varepsilon_t$ 随机」的全部信息——
这正是现有 `TrajGen` 类型（值域 `Traj ι X`）**无法承载**的东西。

标签：**[定义性约定]**（这是方案二的**主定义**）。 -/
def trajLaw (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] (f : Step F) (T : ℕ)
    (D0 : InitDist F) (Dε : Dist F.Ν)
    (θ : F.Θ.Carrier) (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    MeasureTheory.Measure (Traj (Fin T) F.X) :=
  Measure.map (unfold F f T θ u a)
    (D0.prod (MeasureTheory.Measure.pi (fun _ : Fin T => Dε)))

/-- **方案二的 `TrajGen` 型规格**（**新类型，与既有 `TrajGen` 不同**）。

本方案**不实现**既有 `TrajGen`（值域 `Traj ι X`），
而是给出一个**值域升级版**：
$$\mathrm{TrajGen}^{\text{sto}} : \Theta \to (\text{初始分布}) \to (\iota\to U) \to (\iota\to A) \to \mathrm{Measure}\,(\mathrm{Traj}\,\iota\,X).$$

**注意签名差异（诚实标注）**：
1. 第三位不是 `InitialState`（那是「取值 + isRandom 布尔」），
   而是**初始分布** `InitDist`——因为方案二真正需要的是分布本身；
2. **不存在** $\{\varepsilon_t\}$ 输入位——噪声已被**积分掉**（这正是「按分布采样」的含义）；
3. 值域是 `Measure (Traj ι X)`，**不是** `Traj ι X`。

故它**不满足**规格 §3.1 的 `TrajGen` 签名，
是一个**平行的、更细的类型**。据实登记，不冒充「实现」。

标签：**[定义性约定]** + **类型层结论**。 -/
abbrev TrajGenSto (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] (ι : Type _) : Type _ :=
  F.Θ.Carrier → InitDist F →
    (ι → F.U.Carrier) → (ι → F.Act.Carrier) →
      MeasureTheory.Measure (Traj ι F.X)

/-- 方案二对 `TrajGenSto` 的实现（`ι = Fin T`）。 -/
def trajGenSto (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] (f : Step F) (T : ℕ) (Dε : Dist F.Ν) :
    TrajGenSto F (Fin T) :=
  fun θ D0 u a => trajLaw F f T D0 Dε θ u a

/-! ===========================================================================
    §4  与方案 A 的**唯一**正确关系：逐样本路径一致性
    =========================================================================== -/

/-- 方案 A（原始递归）的 `trajGen`，重新陈述以便对比。

（与 `第9问` 方案 A 同式：`Nat.rec` 正向展开 `Step`。） -/
def detTraj (F : Frame) (f : Step F) (T : ℕ)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier) :
    Traj (Fin T) F.X :=
  fun n => stateAt F f T θ u a ε x₀ n.val (Nat.le_of_lt n.isLt)

/-- **逐样本路径一致性**：对**任意给定**的噪声实现 $\omega$，
方案二的展开 `unfold` 恰等于方案 A 的 `detTraj`。

$$ \mathrm{unfold}(x_0,\omega) = \mathrm{detTraj}(x_0,\omega). $$

这不是"两方案等价"——而是「方案二的**每条样本**落在方案 A 的像里」。
方案二多出来的是**样本上的分布**。证明是定义性的（`rfl`）。

这是 §4 的核心：它把「唯一权威方程」在方案二中的忠实性钉死为
**样本路径层**的等式，而不是测度层（测度层是推前，不是等式）。 -/
theorem unfold_eq_detTraj (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (ω : Fin T → F.Ν.Carrier)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    unfold F f T θ u a (x₀, ω) = detTraj F f T θ x₀ u ω a := rfl

/-- **唯一权威方程在方案二中的截面**：`unfold` 的**每条**样本路径满足
$x_{n+1}=f(x_n,u_n,\omega_n;\theta,a_n)$（对所有 $n$ 使 $n+1<T$）。

对样本空间中的**每一点**成立（无需测度论，无需 "a.e."）。 -/
theorem unfold_succ (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier)
    (x₀ : F.X.Carrier) (ω : Fin T → F.Ν.Carrier) (n : ℕ) (hn : n + 1 < T) :
    unfold F f T θ u a (x₀, ω) ⟨n + 1, hn⟩
      = f (unfold F f T θ u a (x₀, ω) ⟨n, by omega⟩)
          (u ⟨n, by omega⟩) (ω ⟨n, by omega⟩) θ (a ⟨n, by omega⟩) := rfl

/-! ===========================================================================
    §5  退化检查：点质量噪声 ⇒ 方案二塌缩回方案 A
    =========================================================================== -/

/-! **退化定理（陈述，证明拆分到样本层与一步层）**：若噪声分布是点质量 $\delta_{\varepsilon_0}$、
初始分布是点质量 $\delta_{x_0}$，则轨迹律 $\rho$
是**单条路径** $\mathrm{detTraj}(x_0,\text{const }\varepsilon_0)$ 上的点质量。

$$ \mathcal{D}_0=\delta_{x_0},\ \mathcal{D}_\varepsilon=\delta_{\varepsilon_0}
   \;\Longrightarrow\; \rho = \delta_{\mathrm{detTraj}(x_0,\ \varepsilon_0\cdot)}. $$

**意义**：方案二**严格推广**方案 A——方案 A 是方案二在「噪声/初始都确定性」时的特例。
故两方案不是竞争关系，而是**同一构造在两个确定性层次上的取值**。
这也解释了为何方案 A 无法区分「只在 $x_0$ 分布上不同的两个世界」：
它固定在了 $\delta$ 这一支上。

**证明路线**：本文件不在此强制证明整个测度层的点质量等式
（它需穿过零扩张 + `Measure.pi` of `dirac`，代价高而与类型层结论无关）；
改为在**样本层**与**一步层**分别钉死退化：
- 一步层：`xNextDist_dirac`（§2）——点质量噪声下随机一步 = 确定一步；
- 样本层：`unfold_det_eq`（下方）——噪声恒为 $\varepsilon_0$ 时，展开序列逐点等于方案 A。
二者合并即为「方案二在确定性极限下 = 方案 A」。 -/

/-- **样本层退化**：噪声序列恒为 $\varepsilon_0$ 时，方案二的展开序列
**逐点等于**方案 A 的输出。这与 `unfold_eq_detTraj` 相容
（后者对**任意** $\omega$ 成立），此处只是把 $\omega$ 限定为常函数。 -/
theorem unfold_det_eq (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (ε₀ : F.Ν.Carrier)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    unfold F f T θ u a (x₀, fun _ => ε₀)
      = detTraj F f T θ x₀ u (fun _ => ε₀) a := rfl

/-- **一步层退化**的再述（与 §2 同源，集中到 §5 作退化检查）：
点质量噪声下，一步随机转移塌缩为确定转移。 -/
theorem step_collapse (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] [MeasurableSingletonClass F.Ν.Carrier]
    [MeasurableSingletonClass F.X.Carrier] (f : Step F) (ε₀ : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) (u : F.U.Carrier)
    (x : F.X.Carrier) :
    xNextDist F f (Measure.dirac ε₀) θ a u x = Measure.dirac (f x u ε₀ θ a) :=
  xNextDist_dirac F f ε₀ θ a u x

/-! ===========================================================================
    §6  随机过程的分布层性质（方案二相对 A 的增益）
    =========================================================================== -/

/-- **方案二能区分方案 A 不能区分的世界**。

  两个仅初始分布不同、`f` 相同的世界，其 `trajLaw` 一般不同。
  更基本的是：`Measure (Traj ι X)` 这一值域**有足够表达力**承载该区分——
  两个轨迹律相等当且仅当它们对一切可测集取值相同。
  而在方案 A（值域为单路径）里，「只在 $x_0$ 分布上不同」**根本无法进入类型**。

  这条定理是**类型层结论的载体**：它说明升级值域到测度后，
  "两世界是否可区分"成为一个**可陈述、可比较**的命题。 -/
theorem trajLaw_ext {F : Frame} [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] (f : Step F) (T : ℕ) (Dε : Dist F.Ν)
    (θ : F.Θ.Carrier) (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier)
    {D0₁ D0₂ : InitDist F}
    (h : ∀ S : Set (Traj (Fin T) F.X), MeasurableSet S →
        trajLaw F f T D0₁ Dε θ u a S = trajLaw F f T D0₂ Dε θ u a S) :
    trajLaw F f T D0₁ Dε θ u a = trajLaw F f T D0₂ Dε θ u a :=
  Measure.ext h

/-! ===========================================================================
    §7  类型层结论（本方案的**主要产物**）
    =========================================================================== -/

/-!
## §7 为什么方案二**不能**是既有 `TrajGen` 的实现

既有类型（`Fate/Frame.lean:160`）：
```lean
abbrev TrajGen (F : Frame) (ι : Type _) : Type _ :=
  F.Θ.Carrier → InitialState F.X →
    (ι → F.U.Carrier) → (ι → F.Ν.Carrier) → (ι → F.Act.Carrier) → Traj ι F.X
```

方案二的值域是 `Measure (Traj ι F.X)`。二者的差异是**结构性**的，不可通过
"内部改写"弥合：

1. **值域不同型**：`Traj ι F.X` 是函数类型；`Measure (Traj ι F.X)` 是测度。
   没有从后者到前者的**可构造的**典范投影（只有"取支撑中一点"，
   那需要选择公理且丢失分布信息）。
2. **输入位不同**：`TrajGen` 要求一个噪声序列 $\{\varepsilon_t\}$ 作输入；
   方案二**没有这一位**（噪声被积分掉）。把 $\{\varepsilon_t\}$ 塞回去 =
   退回方案 A（给定噪声 = 单条路径）。**"按分布采样"与"输入噪声序"
   在类型上互斥**：前者把 $\varepsilon$ 放进测度，后者把 $\varepsilon$ 放进函数自变量。
3. **`isRandom` 布尔位之别**：`InitialState.isRandom : Bool` 只能标记
   "是否随机"，**无法承载分布 $\mathcal{D}_0$ 本身**。方案二必须用 `InitDist`。

**结论（类型层，非实现层）**：若要真正表达"随机递推 + 随机过程"，
**必须改 `TrajGen` 的类型**（值域升为测度，去掉噪声序位，`InitialState` 换为初始分布）。
在**当前类型下**，方案二**不可能**有一个忠实的实现——
这是 `第9问` 方案 D 的正式化，也是本方案的**主要贡献**：
它不是"第三种实现"，而是**现有类型表达力上限的证明**。

**推论**：`trajGenSto` 与既有 `TrajGen` **不可互相定义**（非同型）；
任何声称用 `TrajGen` 实现了"随机过程"的写法，必然在类型层撒谎。

## §7 末 开放项（诚实登记）

**无穷视窗** $\iota=\mathbb N$：本文件用有限视窗 `Fin T`（贴合规格 T_max）。
若要把 $\iota$ 扩到 $\mathbb N$，需要 $\mathcal{D}_\varepsilon^{\otimes\mathbb N}$
这一无穷积测度，其存在性依赖 **Kolmogorov 扩张定理**。该定理在
本项目的 Mathlib 检出中**未找到可直接调用的封装**，故**登记为外部假设**，
本文件不引入、不使用。这是一条**明确的外部依赖**，不是本文件能自证的。
-/

/-- 方案二实现的值**确实落在测度类型**中（而非 `Traj`）。

把"值域已升级"钉成一条可编译的事实：
`trajGenSto` 的值可被一个 `Measure (Traj (Fin T) F.X)` 项 **定义性地**接住。
（类型系统**不允许**它被一个 `Traj (Fin T) F.X` 项接住——这正是类型层结论。） -/
theorem trajGenSto_value_is_measure (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] (f : Step F) (T : ℕ) (Dε : Dist F.Ν)
    (θ : F.Θ.Carrier) (D0 : InitDist F)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    ∃ ρ : MeasureTheory.Measure (Traj (Fin T) F.X),
      ρ = trajGenSto F f T Dε θ D0 u a :=
  ⟨trajGenSto F f T Dε θ D0 u a, rfl⟩

end

end FateV2.Model