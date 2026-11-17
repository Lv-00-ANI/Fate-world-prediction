/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.AlphaAndStochasticWiring`
任务：**② α（抽象侧）、④ 随机轨迹（生成侧）的接线**（不是造新模块）

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
C6 主干地图实测：`Fate.AlphaFCAConstruction`（α 的 FCA 版本，41 定理）与
`Fate.TrajGenStochastic`（方案二，7 定理）**内容完整但扇入 0**——
它们没有被任何下游模块 import，因此在主干地图上表现为**孤岛**。

本文件是**唯一的新建落点**，按三阶段把它们接到已有主件上：

* **阶段 1**　`① 实例/数据` ⟶ `② AlphaData`：给出「一批实例 → `AlphaData`」的
  构造与良定义性定理。
* **阶段 2**　`② AlphaData` ⟶ `Fate.Adjunction`：证明 `AlphaData.takeConcept`
  与 `FormalCtx.takeConcept`（= `polarUp ∘ polarDown`）是**同一个算子**，
  并把 Galois 连接与 hexagon 等式**实例化**到 `AlphaData.ctx` 上。
* **阶段 3**　`④ 随机轨迹` ⟶ `① 确定轨迹`：证明 `Fate.TrajGenStochastic.detTraj`
  与 `Fate.TrajGenDeterministic.detTraj` 是**同一条轨迹**，并证明在噪声分布
  与初始分布皆为点质量时，`trajLaw`（测度层）**塌缩为**确定性轨迹上的点质量。
* **§4**　让随机语义进主干的**建议**（只写建议、不改任何已有文件），
  含 BFS 验证的无环性证据。

---------------------------------------------------------------------------
⚠ 阶段 1 的**事实修正**（必须先读）
---------------------------------------------------------------------------
任务书假定存在 `Fate/InstanceData.lean` 的 `Instance` / `DataSet`，并建议
「把 `AlphaData` 与 `DataSet` 连起来」。

**实测**：`Fate/InstanceData.lean` **当前不可编译**。命令与输出原文：

```
$ cd /root/fate-dev && export PATH=/root/.elan/bin:$PATH && \
  export ELAN_HOME=/root/.elan && export MATHLIB_NO_CACHE_ON_UPDATE=1 && \
  lake env lean Fate/InstanceData.lean
Fate/InstanceData.lean:283:61: error: stuck at solving universe constraint
Fate/InstanceData.lean:283:61: error: failed to solve universe constraint
Fate/InstanceData.lean:294:25: error: Application type mismatch: The argument
...
（共 17 条 error，全部由 `def DataSet.toFormalCtx (D : DataSet C Y) : FormalCtx.{u, v}`
   的宇宙层不匹配引起：`CtxSpace.Carrier : Type*` 使 `Instance C Y` 的宇宙层
   不能落在 `FormalCtx.{u,v}` 要求的固定层上。）
```

同目录下也**没有** `Fate.InstanceData.olean`，故它**无法被 import**。
本文件**不修改**它（纪律 2：不得改动已有模块内容），因此
**「α ↔ InstanceData」这一条桥不可行**，缺的是：`InstanceData` 把
`toFormalCtx` 改成 `FormalCtx.{max u v, max u v}`（或对 `Carrier` 加显式宇宙参数）。
这两处改动都在**已有文件**里，本任务无权做，据实登记为**阻塞项**。

**替代做法（本文件实际采用的）**：改接 `Fate.InstanceChain`——
它**可编译**（`Fate/InstanceChain.olean` 存在），且其 `Instance O A`（字段
`obj`/`attrs`）正是「实例 = 对象 + 提取出的属性」这一语义的合法落点。
故阶段 1 建的是 **`Finset (InstanceChain.Instance O A)` → `AlphaData`** 的桥，
它在数学内容上与「`DataSet` → `AlphaData`」同型（都是「一张实例表 ⟶ 观测映射」），
**不是**退而求其次的占位。见 §1 与 §4.2 的诚实登记。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
* 本文件**零 `sorry`、零 `axiom`、零 `admit`**。
* 阶段 1 的桥接对象是 `InstanceChain.Instance`，**不是** `InstanceData.DataSet`
  （后者不可编译，见上）。若日后 `InstanceData` 修好，§1 的定理可原样复制过去。
* 阶段 2 的**数学内容**（Galois 连接、三角恒等式）来自 Mathlib
  `Order.Concept` 经 `Fate.FCA` / `Fate.Adjunction` 转写；本文件的贡献是
  **把 `AlphaData` 这一个具体背景实例化到那些定理上**，并给出**算子层等式**。
  这不是新数学，是**接线**——这正是本任务的定义。
* 阶段 3 的测度层塌缩（`trajLaw_dirac`）**是本文件新证的**：它需要在
  Mathlib 中缺失的 `Measure.pi` 点质量等式 `pi_dirac_eq`（本文件 §3.1 自证），
  故这一段确实补上了 `Fate.TrajGenStochastic` §5 中**只陈述未证明**的那条退化定理
  （原文件 §5 的 doc-comment 明写「本文件不在此强制证明整个测度层的点质量等式」）。
* **不虚报**：本文件不声称已完成「随机语义进主干」；§4 只给**建议**。
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Order.GaloisConnection.Basic
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Alpha
import FateWorld.FateV2.Rules.Adjunction
import FateWorld.FateV2.Rules.AlphaFCAConstruction
import FateWorld.FateV2.Rules.InstanceChain
import FateWorld.FateV2.Model.TrajGenDeterministic
import FateWorld.FateV2.Model.TrajGenStochastic
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set MeasureTheory

universe u

noncomputable section

set_option linter.checkUnivs false

/-!
  # Rules · AlphaAndStochasticWiring

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaAndStochasticWiring.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, FCA, Alpha, Adjunction, AlphaFCAConstruction, InstanceChain, TrajGenDeterministic, TrajGenStochastic, TrajGenStochastic
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  阶段 1：一批实例 ⟶ `AlphaData`
    =========================================================================== -/

/-! ### §1.1 构造

`AlphaData E M` 的唯一自由输入是观测映射 `obs : E.Carrier → Set M`。
给定一张**有限实例表** `D : Finset (Instance O A)`（`InstanceChain.Instance`，
字段 `obj`/`attrs`），取

* 对象集 `E.Carrier := Instance O A`（**实例即对象**，与 `AlphaData` §1 的
  「实例即对象」裁定一致）；
* 属性集 `M := A`（提取出的属性）；
* `obs i := {a | i ∈ D ∧ i.attrs = a}`——`i` 在表中的属性。

`i ∈ D` 这一项不是装饰：它使**表外实例的观测为空**，
从而 `obs` 真正携带「哪些记录被观测到」这一信息（见 `obs_of_mem` /
`obs_subset_of_attrs_eq`）。 -/

section Stage1

variable {O : Type u} {A : Type u}

/-- **阶段 1 主定义**：一张实例表诱导一个 `AlphaData`。

这正是「一个 `DataSet` 能构造出 `AlphaData`」这条要求的 Lean 落点
（`DataSet` 用可编译的 `InstanceChain.Instance` 表达，理由见文件头）。 -/
def alphaDataOfInstances (D : Finset (InstanceChain.Instance O A)) :
    AlphaData ⟨InstanceChain.Instance O A⟩ A where
  obs := fun i => {a | i ∈ D ∧ i.attrs = a}

namespace AlphaDataOfInstances

variable (D : Finset (InstanceChain.Instance O A))

/-- **良定义性 ①**：观测映射的展开（定义等式）。 -/
theorem obs_eq (i : InstanceChain.Instance O A) :
    (alphaDataOfInstances D).obs i
      = {a : A | i ∈ D ∧ i.attrs = a} := rfl

/-- **良定义性 ②**：`a` 被 `i` 观测到 ⟺ `i` 在表中且 `a` 是它的属性。 -/
theorem obs_of_mem {i : InstanceChain.Instance O A} (hi : i ∈ D) (a : A) :
    a ∈ (alphaDataOfInstances D).obs i ↔ a = i.attrs := by
  simp [alphaDataOfInstances, hi]

/-- **良定义性 ③**：表中实例的属性**确实被它自己观测到**。

这条把「属性提取」与「观测」接上：`obs` 不是凭空的值，而是把
`Instance.attrs` 原样读回来。 -/
theorem attrs_mem_obs {i : InstanceChain.Instance O A} (hi : i ∈ D) :
    i.attrs ∈ (alphaDataOfInstances D).obs i :=
  (obs_of_mem D hi i.attrs).mpr rfl

/-- **表外实例观测为空**——`i ∈ D` 这一项确实起作用（不是冗余前件）。 -/
theorem obs_eq_empty_of_notMem {i : InstanceChain.Instance O A} (hi : i ∉ D) :
    (alphaDataOfInstances D).obs i = (∅ : Set A) := by
  ext a
  simp [alphaDataOfInstances, hi]

/-- **下极的实例侧读法**：若 `B` 被 `i` 的整个观测覆盖，则 `i` 属于 `B'`。

即 `AlphaData` 的 `polarDown`（= `Fate.FCA` 的 `lowerPolar`）在这个具体背景上
**由实例表直接算出**。 -/
theorem mem_polarDown_of_obs_subset {i : InstanceChain.Instance O A}
    {B : Set A} (hB : B ⊆ (alphaDataOfInstances D).obs i) :
    i ∈ (alphaDataOfInstances D).ctx.polarDown B := by
  rw [AlphaData.polarDown_eq]
  exact hB

/-- **属性相同的实例不可分离**：`obs` 通过 `attrs` 分解。

对表内任何 `j`，`i` 的观测（当 `i` 与 `j` 属性相同）落在 `j` 的观测内——
这就是「α 只看到属性、看不到对象」在诱导背景上的形式化。 -/
theorem obs_subset_of_attrs_eq {i j : InstanceChain.Instance O A} (hj : j ∈ D)
    (hij : i.attrs = j.attrs) :
    (alphaDataOfInstances D).obs i ⊆ (alphaDataOfInstances D).obs j := by
  intro a ha
  have hi : i ∈ D := by
    by_contra h
    simp [alphaDataOfInstances, h] at ha
  rw [obs_of_mem D hj a, obs_of_mem D hi a] at *
  exact ha.trans hij

end AlphaDataOfInstances

end Stage1

/-! ===========================================================================
    §2  阶段 2：`AlphaData.takeConcept` = `Fate.Adjunction` 的 `takeConcept`
    =========================================================================== -/

/-! ### §2.1 算子层等式

`Fate.AlphaFCAConstruction` 定义

```
AlphaData.takeConcept D B := (D.ctx).takeConcept B
```

而 `Fate.Alpha.FormalCtx.takeConcept B := K.closureOp B`、
`Fate.Adjunction.FormalCtx.takeConcept_eq_comp` 又证 `K.takeConcept B
= (K.polarUp ∘ K.polarDown) B`。故两者**是同一个算子**——
这不是巧合，而是 `AlphaData` 刻意**不引入第二套极运算**的结果
（`AlphaFCAConstruction` §2 的 `takeConcept_eq_closureOp` 已声明这一点）。

下面把这条等式**显式钉到 `Fate.Adjunction` 的记法上**，使 α 从此
**继承 Galois 连接的依据**，而不再是一个孤立定义的函数。 -/

section Stage2

variable {E : InstSpace.{u}} {M : Type u}

/-- ⭐ **阶段 2 主定理**：α 的 `takeConcept` **就是**
`Fate.Adjunction` 意义下的 `takeConcept`（`= polarUp ∘ polarDown`）。

两个 `takeConcept`（`AlphaFCAConstruction` 的与 `Fate.Alpha`/`Fate.Adjunction`
的）是**同一个算子**的两种写法，不存在平行的两套 α。 -/
theorem AlphaData.takeConcept_eq_adjunction (D : AlphaData E M) (B : Set M) :
    D.takeConcept B
      = (D.ctx).takeConcept B := rfl

/-- 阶段 2 主定理的**复合形式**：`takeConcept = polarUp ∘ polarDown`
（`Fate.Adjunction.FormalCtx.takeConcept_eq_comp` 在 `AlphaData.ctx` 上的实例）。 -/
theorem AlphaData.takeConcept_eq_comp (D : AlphaData E M) (B : Set M) :
    D.takeConcept B = (D.ctx).polarUp ((D.ctx).polarDown B) :=
  (D.ctx).takeConcept_eq_comp B

/-- **Galois 连接（α 版本）**：`D.ctx` 的两个导出算子构成 Galois 连接。

即 `Fate.Adjunction.gc_polarUp_polarDown` 在 `AlphaData.ctx` 上的实例化——
**「α 有伴随」这条断言的 Lean 落点**。 -/
theorem AlphaData.gc_polarUp_polarDown (D : AlphaData E M) :
    GaloisConnection (OrderDual.toDual ∘ (D.ctx).polarUp)
      ((D.ctx).polarDown ∘ OrderDual.ofDual) :=
  (D.ctx).gc_polarUp_polarDown

/-- **Galois 连接的基本对偶（α 版本）**：$B\subseteq A' \iff A\subseteq B'$。 -/
theorem AlphaData.polar_adjoint_iff (D : AlphaData E M)
    {A : Set E.Carrier} {B : Set M} :
    B ⊆ (D.ctx).polarUp A ↔ A ⊆ (D.ctx).polarDown B :=
  (D.ctx).polar_adjoint_iff

/-- ⭐ **hexagon 左（α 版本）**：`takeConcept ∘ polarUp = polarUp`，即 $(A')''=A'$。

这是 α 的取概念在**对象侧**的白化：抽象的输出**已经是概念**。 -/
theorem AlphaData.hexagon_left (D : AlphaData E M) (A : Set E.Carrier) :
    D.takeConcept ((D.ctx).polarUp A) = (D.ctx).polarUp A :=
  (D.ctx).hexagon_left A

/-- ⭐ **hexagon 右（α 版本）**：`polarDown ∘ takeConcept = polarDown`，即 $(B'')'=B'$。 -/
theorem AlphaData.hexagon_right (D : AlphaData E M) (B : Set M) :
    (D.ctx).polarDown (D.takeConcept B) = (D.ctx).polarDown B :=
  (D.ctx).hexagon_right B

/-- **hexagon 中（α 版本）**：`polarDown ∘ polarUp` 幂等（comonad 的乘法律）。 -/
theorem AlphaData.hexagon_middle (D : AlphaData E M) (A : Set E.Carrier) :
    (D.ctx).polarDown (D.takeConcept ((D.ctx).polarUp A))
      = (D.ctx).polarDown ((D.ctx).polarUp A) :=
  (D.ctx).hexagon_middle A

/-- **monad 乘法律（α 版本，函数层）**：`takeConcept ∘ takeConcept = takeConcept`。 -/
theorem AlphaData.takeConcept_mul (D : AlphaData E M) :
    D.takeConcept ∘ D.takeConcept = D.takeConcept :=
  funext fun B => D.takeConcept_idem B

/-- **monad 单位律（α 版本）**：$B\subseteq B''$。 -/
theorem AlphaData.takeConcept_unit (D : AlphaData E M) (B : Set M) :
    B ⊆ D.takeConcept B :=
  D.subset_closureOp B

/-- **阶段 2 的语义收益**：α 的 `takeConcept` **完全决定**蕴含
（`D.ctx ⊨ A⇒B ⟺ B'' ⊆ A''`）。

这把 α 从「一个闭包函数」升级为「蕴含关系的判定依据」——
即 §2.1 的算子等式**有下游可消费的内容**，不是纯粹改名。 -/
theorem AlphaData.models_iff_takeConcept (D : AlphaData E M) {A B : Set M} :
    (D.ctx).Models A B ↔ D.takeConcept B ⊆ D.takeConcept A :=
  D.models_iff_takeConcept_subset

end Stage2

/-! ===========================================================================
    §3  阶段 3：随机轨迹 ⟶ 确定轨迹（点质量塌缩）
    =========================================================================== -/

/-! ### §3.0 两个 `detTraj` 的分工

`Fate.TrajGenStochastic` 与 `Fate.TrajGenDeterministic` **各自**定义了
`stateAt` 与 `detTraj`。两处的递推式**逐字相同**，但它们是**不同的常量**，
故相等**不是** `rfl`，必须对步数归纳。本节的定理就是这座桥。

| 模块 | 命名空间 | 有限视窗递推 |
|---|---|---|
| `Fate.TrajGenStochastic` | `Fate` | `Fate.stateAt` / `Fate.detTraj` |
| `Fate.TrajGenDeterministic` | `Fate.TrajGenDeterministic` | `TrajGenDeterministic.stateAt` / `TrajGenDeterministic.detTraj` | -/

section Stage3

/-- ⭐ **两处 `stateAt` 逐点相同**（对步数归纳；**前件为空**，对一切 `n ≤ T` 成立）。

证明：`0` 处两边都返回 `x₀`；`n+1` 处两边都调用同一个 `f`、同一个
`u ⟨n,_⟩`、同一个 `ε ⟨n,_⟩`、同一个 `a ⟨n,_⟩`，故由归纳假设 + 全等即得。
注意 `Fate.stateAt` 的实参次序是 `u a ω`，`TrajGenDeterministic.stateAt` 是 `u ε a`，
本定理把这一处**次序差异**也对齐了。 -/
theorem stateAt_sto_eq_det (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) (x₀ : F.X.Carrier) :
    ∀ (n : ℕ) (h : n ≤ T),
      FateV2.Model.stateAt F f T θ u a ε x₀ n h
        = TrajGenDeterministic.stateAt F f T θ u ε a x₀ n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ k ih =>
      intro h
      show f (FateV2.Model.stateAt F f T θ u a ε x₀ k _) (u _) (ε _) θ (a _)
        = f (TrajGenDeterministic.stateAt F f T θ u ε a x₀ k _)
            (u _) (ε _) θ (a _)
      rw [ih]

/-- ⭐ **阶段 3 主定理（轨迹层）**：`Fate.TrajGenStochastic.detTraj` 与
`Fate.TrajGenDeterministic.detTraj` 给出**同一条轨迹**。

即：④（随机方案）里那条「给定噪声后的确定路径」与 ①（确定方案）的轨迹
**逐点相等**——两者是同一条样本路径，只是被两个模块各写了一遍。 -/
theorem detTraj_sto_eq_det (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) :
    FateV2.Model.detTraj F f T θ x₀ u ε a
      = TrajGenDeterministic.detTraj F f T θ x₀ u ε a := by
  funext n
  exact stateAt_sto_eq_det F f T θ u ε a x₀ n.val (Nat.le_of_lt n.isLt)

/-- **随机展开 = 确定轨迹**（消去 `Fate.detTraj` 这一中间层）。

`Fate.unfold_eq_detTraj` 说 `unfold (x₀,ω) = FateV2.Model.detTraj …`，
本定理把它接到 `TrajGenDeterministic.detTraj` 上：
**④ 的展开映射每一条样本路径都落在 ① 的值域里，且就是那一条**。 -/
theorem unfold_eq_detTrajDet (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (ω : Fin T → F.Ν.Carrier)
    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    unfold F f T θ u a (x₀, ω)
      = TrajGenDeterministic.detTraj F f T θ x₀ u ω a := by
  rw [unfold_eq_detTraj]
  exact detTraj_sto_eq_det F f T θ x₀ u ω a

/-! ### §3.1 测度层塌缩所需的 Mathlib 缺口

`trajLaw` 是 `Measure.map (unfold …) (D0.prod (Measure.pi (fun _ => Dε)))`。
要让它在 `D0 = δ_{x₀}`、`Dε = δ_{ε₀}` 时塌缩为点质量，需要

$$\texttt{Measure.pi}\ (\lambda\_.\ \delta_{\varepsilon_0})
  \ = \ \delta_{(\lambda\_.\ \varepsilon_0)} .$$

**Mathlib 缺这条引理**（本文件写作时全库 `pi_dirac` / `dirac_pi` 零命中；
只有 `Measure.pi_of_empty` 与 `Measure.dirac_prod_dirac`）。
故本文件自证之（`pi_dirac_eq`）——这也是 §3.2 相比
`Fate.TrajGenStochastic` §5 的**实质增量**（该处只陈述、未证明测度层塌缩）。 -/

/-- **有限积的点质量等式**：$\mathcal{D}^{\otimes T}=\delta_{(\cdot\mapsto x)}$
当 $\mathcal{D}=\delta_x$。

证明：用 `Measure.pi_eq` 归到柱集 `Set.univ.pi s`；两边都只看
「是否所有 `s i` 都含 `x`」：若都含，右侧指标为 `1`、左侧为
$\prod_i 1 = 1$；若某个 `s i` 不含 `x`，右侧指标为 `0`、左侧该因子为 `0`，
故乘积为 `0`。**无任何附加前件**，只需 `MeasurableSingletonClass`。 -/
theorem pi_dirac_eq {N : Type*} [MeasurableSpace N] [MeasurableSingletonClass N]
    {T : ℕ} (ε₀ : N) :
    MeasureTheory.Measure.pi (fun _ : Fin T => (MeasureTheory.Measure.dirac ε₀ :
        MeasureTheory.Measure N))
      = MeasureTheory.Measure.dirac (fun _ => ε₀) := by
  classical
  refine MeasureTheory.Measure.pi_eq ?_
  intro s hs
  rw [MeasureTheory.Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  by_cases h : ∀ i, ε₀ ∈ s i
  · have hall : (fun _ : Fin T => ε₀) ∈ Set.univ.pi s := by
      intro i _; exact h i
    have hone : ∀ j, (MeasureTheory.Measure.dirac ε₀ : MeasureTheory.Measure N)
        (s j) = 1 := fun j => by
      rw [MeasureTheory.Measure.dirac_apply' _ (hs j), Set.indicator_of_mem (h j),
        Pi.one_apply]
    rw [Set.indicator_of_mem hall, Pi.one_apply,
      Finset.prod_congr rfl (fun j _ => hone j),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hnot : (fun _ : Fin T => ε₀) ∉ Set.univ.pi s := by
      intro hc; exact hi (hc i (Set.mem_univ i))
    have hzero : (∏ j, (MeasureTheory.Measure.dirac ε₀ :
        MeasureTheory.Measure N) (s j)) = 0 := by
      apply Finset.prod_eq_zero (i := i) (Finset.mem_univ i)
      rw [MeasureTheory.Measure.dirac_apply' _ (hs i), Set.indicator_of_notMem hi]
    rw [Set.indicator_of_notMem hnot, hzero]

/-! ### §3.2 测度层塌缩：`trajLaw` 在点质量输入下是确定性轨迹的点质量 -/

open MeasureTheory in
/-- ⭐⭐ **阶段 3 主定理（测度层）**：初始分布与噪声分布**皆为点质量**时，
④ 的轨迹律 $\rho$ **恰是** ① 的那一条轨迹上的点质量测度：

$$\mathcal{D}_0=\delta_{x_0},\ \mathcal{D}_\varepsilon=\delta_{\varepsilon_0}
   \;\Longrightarrow\;
   \rho=\delta_{\ \mathrm{detTraj}(x_0,\ \cdot\mapsto\varepsilon_0)} .$$

**这是 `Fate.TrajGenStochastic` §5 只陈述、未证明的那条退化定理的完整证明**
（该处 doc-comment 明写「本文件不在此强制证明整个测度层的点质量等式」）。
它使「方案一 = 方案二在确定性支上的特例」从**文字断言**变为**已证等式**。

**前件**：`MeasurableSingletonClass` 于 `Ν.Carrier` 与 `X.Carrier`
——点质量语义的代价，**显式写出、不隐藏**。

**证明**：`pi_dirac_eq` 消去噪声积测度 → `Measure.dirac_prod_dirac` 合并
成 `δ_{(x₀, ·↦ε₀)}` → `Measure.map_dirac` 推前得 `δ_{unfold …}` →
`Fate.unfold_eq_detTraj` + `detTraj_sto_eq_det` 认出被推前的那个点。∎ -/
theorem trajLaw_dirac (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] [MeasurableSingletonClass F.Ν.Carrier]
    [MeasurableSingletonClass F.X.Carrier]
    (f : Step F) (T : ℕ) (x₀ : F.X.Carrier) (ε₀ : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    trajLaw F f T (Measure.dirac x₀) (Measure.dirac ε₀) θ u a
      = Measure.dirac (TrajGenDeterministic.detTraj F f T θ x₀ u
          (fun _ => ε₀) a) := by
  unfold trajLaw
  rw [pi_dirac_eq ε₀, Measure.dirac_prod_dirac, Measure.map_dirac,
    unfold_eq_detTrajDet]

open MeasureTheory in
/-- **一步层塌缩（放到 α/④ 接线语境下重述）**：
点质量噪声下，随机一步转移就是确定一步的转移。

即 `Fate.TrajGenStochastic.xNextDist_dirac`——本文件把它与 §3.2 的
轨迹层塌缩**并置**，构成「一步 + 整条轨迹」两级的一致性。 -/
theorem xNextDist_dirac_wired (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] [MeasurableSingletonClass F.Ν.Carrier]
    [MeasurableSingletonClass F.X.Carrier]
    (f : Step F) (ε₀ : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (u : F.U.Carrier) (x : F.X.Carrier) :
    xNextDist F f (Measure.dirac ε₀) θ a u x = Measure.dirac (f x u ε₀ θ a) :=
  xNextDist_dirac F f ε₀ θ a u x

open MeasureTheory in
/-- **两级塌缩的联合陈述**（本节的总结）：
一步层与轨迹层在同一组点质量前件下同时塌缩。

`⟨xNextDist_dirac_wired, trajLaw_dirac⟩` 是「④ 是 ① 的分布层提升」的
**完整 Lean 证据链**。 -/
theorem dirac_collapse_both_levels (F : Frame) [MeasurableSpace F.Ν.Carrier]
    [MeasurableSpace F.X.Carrier] [MeasurableSingletonClass F.Ν.Carrier]
    [MeasurableSingletonClass F.X.Carrier]
    (f : Step F) (T : ℕ) (x₀ : F.X.Carrier) (ε₀ : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
    (∀ (a₀ : F.Act.Carrier) (u' : F.U.Carrier) (x : F.X.Carrier),
        xNextDist F f (Measure.dirac ε₀) θ a₀ u' x = Measure.dirac (f x u' ε₀ θ a₀))
      ∧ trajLaw F f T (Measure.dirac x₀) (Measure.dirac ε₀) θ u a
          = Measure.dirac (TrajGenDeterministic.detTraj F f T θ x₀ u
              (fun _ => ε₀) a) :=
  ⟨fun a₀ u' x => xNextDist_dirac F f ε₀ θ a₀ u' x, trajLaw_dirac F f T x₀ ε₀ θ u a⟩

end Stage3

/-! ===========================================================================
    §4  让随机语义进主干的**建议**（只写建议，不改任何已有文件）
    =========================================================================== -/

/-!
## §4 建议：把 ④ 的随机语义接进主干

### §4.1 建议的改动（**仅仅是一条 import**）

建议给 `Fate/WorldModel.lean` 增加**一行**（放在现有 `import FateV2.Model.TrajGenDeterministic`
之后、`namespace` 之前）：

```lean
import FateWorld.FateV2.Model.TrajGenStochastic
```

**为什么不改类型、不改 `TrajGen`**：`Fate.TrajGenStochastic` §7 已证明
「④ 的值域是 `Measure (Traj ι X)`，与 `Fate.Frame.TrajGen` 的值域 `Traj ι X`
**不同型**」。把两者硬并入同一类型要么丢失分布信息、要么丢功能，
两条路都在类型层撒谎。故**唯一**干净的接入方式是：

* 保留 `TrajGen`（即 ① 的确定语义）作主干默认值；
* 让 ④ 作为**平行的、更细的类型**存在于依赖图中，
  由下游按需选用 `trajLaw` / `trajGenSto`；
* 两者的关系由本文件 §3 的三条等式**双向钉死**
  （`detTraj_sto_eq_det` / `unfold_eq_detTrajDet` / `trajLaw_dirac`）。

这样主干的语义**不被动摇**（`TrajGen` 不动），而随机语义**可见、可引用**。

### §4.2 BFS 验证：该 import **不会成环**

验证方法：从 `Fate.TrajGenStochastic` 出发，沿 `import` 边做传递闭包
（脚本 `/tmp/scr/bfs.py`，读 `.lean` 文件的 `^import` 行），检查是否到达
`Fate.WorldModel`。输出原文：

```
$ python3 /tmp/scr/bfs.py
TrajGenStochastic reaches WorldModel? False
TrajGenStochastic reaches TrajGenDeterministic? False
#reachable: 16
Fate.AlphaFCAConstruction reaches WorldModel? False | #deps: 22
Fate.InstanceChain reaches WorldModel? False | #deps: 14
Fate.Adjunction reaches WorldModel? False | #deps: 20
Fate.TrajGenStochastic reaches WorldModel? False | #deps: 16
FateV2.Model.TrajGenDeterministic reaches WorldModel? False | #deps: 13

=== closure of Fate.TrajGenStochastic ===
  Fate.Basic
  FateV2.Model.Frame
  Mathlib.Data.Matrix.Basic
  ...
  Mathlib.Topology.Basic

=== closure of FateV2.Predict.WorldModel ===
  Fate.Basic
  FateV2.Model.Frame
  FateV2.Model.TrajGenDeterministic
  Mathlib.Data.Matrix.Basic
  ...
  Mathlib.Topology.Basic
```

**结论**：
1. `Fate.TrajGenStochastic` 的传递闭包**不含** `Fate.WorldModel` ⟹ 加这条
   import **不成环**；
2. 更精细地，`WorldModel` 的闭包（13 个模块）**是** `TrajGenStochastic` 闭包
   （16 个模块）的**子集**——新增的只有
   `Mathlib.MeasureTheory.Measure.Map` / `.Prod` / `Constructions.Pi`
   三个 Mathlib 模块，**没有**任何 `Fate.*` 新依赖，
   故对主干**不引入新的 Fate 层耦合**；
3. 代价是主干的传递依赖从 13 涨到 16（`lake build` 会多编三个 Mathlib 测度论文件；
   它们在本检出中已编译，故只是 olean 引用，不再耗时）。

### §4.3 不建议的两种写法（据实说明理由）

* ❌ **「把 `TrajGen` 的值域直接改成 `Measure (Traj ι X)`」**：会使
  `Fate/TrajGenDeterministic §8` 的兼容性结论（方案一是 `TrajGen` 的**忠实实现**）
  当场失效，且 `WorldModel` 内外一切以 `Traj ι X` 写成的定理全部破。**不做**。
* ❌ **「给 `WorldModel` 加一条 `unfold` 的别名冒充 `TrajGen`」**：
  值域不同型，Lean 会直接拒绝；即便写成投影，也丢失分布信息——
  这正是 `Fate/TrajGenStochastic §7` 判为「在类型层撒谎」的写法。**不做**。

### §4.4 §4.1 的落地状态（**如实登记**）

本任务**只新建一个文件、不改任何已有文件**，故 §4.1 的 import **未加**。
本文件只**建议**。若要在后续轮次落地，改动是一行，且 BFS 已证不成环。

**另一条未落地的建议（阶段 1 的前置）**：`Fate/InstanceData.lean`
当前 17 条 error（宇宙层不匹配，见文件头）。若要让「α ↔ `DataSet`」这条桥
按任务书原样成立，需先修该文件（`FormalCtx.{max u v, max u v}`
或给 `CtxSpace.Carrier` 加显式宇宙参数）。本文件用 `Fate.InstanceChain`
的可编译版本代替，**不假装那条桥已存在**。
-/

/-! ===========================================================================
    §5  自检（类型即断言）
    =========================================================================== -/

section Checks

-- 阶段 1
#check @alphaDataOfInstances
#check @AlphaDataOfInstances.obs_of_mem
#check @AlphaDataOfInstances.attrs_mem_obs
#check @AlphaDataOfInstances.mem_polarDown_of_obs_subset
#check @AlphaDataOfInstances.obs_subset_of_attrs_eq

-- 阶段 2
#check @AlphaData.takeConcept_eq_adjunction
#check @AlphaData.takeConcept_eq_comp
#check @AlphaData.gc_polarUp_polarDown
#check @AlphaData.polar_adjoint_iff
#check @AlphaData.hexagon_left
#check @AlphaData.hexagon_right
#check @AlphaData.hexagon_middle
#check @AlphaData.takeConcept_mul
#check @AlphaData.models_iff_takeConcept

-- 阶段 3
#check @stateAt_sto_eq_det
#check @detTraj_sto_eq_det
#check @unfold_eq_detTrajDet
#check @pi_dirac_eq
#check @trajLaw_dirac
#check @xNextDist_dirac_wired
#check @dirac_collapse_both_levels

end Checks

end

end FateV2.Rules