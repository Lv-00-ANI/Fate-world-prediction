import FateWorld.FateV2.Predict.Counterfactual
import FateWorld.FateV2.Predict.FrameBridge
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Function.Basic

/-!
  # Predict · Assembly

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Assembly.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Counterfactual, FrameBridge
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §7  「四 + 甲」组装引理（组装引理 / Assembly Lemma）—— 最小可编译落点

  **来源**：`第36问-系统对比.md` §7.1、`第36问-综合-最终推荐与不确定性.md` §4.1。
  在那两份文件中，**位居第一位、且直接影响最终推荐强度**的未证项是：

  > **「四 + 甲」叠加后的整体可识别性定理——本项目未构造。
  >  本文件只主张二者堵不同自由度，未证叠加后无冲突。**
  >  —— `第36问-综合` §4.1 第 1 条

  **本模块的任务**：**把这条『未证』压缩成一个已证的、可复用的集合论命题**，
  并在其中**如实暴露剩余的真实未证内容**（不是掩盖，而是隔离）。

  ---------------------------------------------------------------------------
  ## 组装的数学内容（把散文断言变成集合论论断）

  两条腿（方向层 / 函数层）各自给出一个**观测泛函**：

  * **方向层**（「四」）：`obsDir : SCM → Dir`，把机制送到其**方向信息**
    （可识别的目标父集 `PA(Y)` / 定向 DAG）。
  * **函数层**（「甲」）：`obsFun : SCM → Fun`，把机制送到其**函数信息**
    （系数 + 噪声方差；在甲下由协方差分解 Cholesky 唯一性给出）。

  组装 = 取**联合观测泛函**

  ```lean
  def obsJoint (obsDir : SCM → Dir) (obsFun : SCM → Fun) : SCM → Dir × Fun :=
    fun s => (obsDir s, obsFun s)
  ```

  **本模块证的（全部零 `sorry`）**：

  1. **(A1) 联合核 = 两核之交**：
     $$\ker(\mathrm{obsJoint}) = \ker(\mathrm{obsDir}) \cap \ker(\mathrm{obsFun}).$$
     —— 这就是「把两条腿拼起来」的**精确代数内容**：只区分两条腿**至少一条**能区分的对。

  2. **(A2) 分解定理（真正用到 `NonMasking`）**：
     在「两腿互不遮蔽」假设下，**两腿都忠实 ⟺ 联合忠实**。
     —— 这是「正交拼接」的**非空**核心；且 `nonmasking_necessary_witness` 证明
     该前件**不可省**（上一版把 (A2) 写成对任意映射成立的空标号，已修正）。

  3. **(A3) 组装引理的主结论（已加强为 `↔`）**：
     方向层在纤维上**单值**（`FunSingleOnFiber`）、且函数层在方向像纤维上可区分，
     则联合观测在纤维上**单值**；**逆命题亦成立**（`joint_kernel_eq_dir_kernel : ↔`）。
     另给出 (A3′)/(A3″)/(A3‴) 三条链式单值传递形式。

  4. **(A4) 联合单射 ⟺ 两腿联合区分**：
     `obsJoint` 单射当且仅当不存在两条腿都读不出差别的不同机制。
     —— 「叠加后无信息冲突」的精确判据。

  ---------------------------------------------------------------------------
  ## ⚠ 诚实边界（本模块**不**主张的）

  ⚠ **上一版的缺陷（本版已修，如实登记）**：上一版的 `Orthogonal` 定义**从来未被任何定理使用**，
  其声称的「(A2) 正交 ⟹ 分离」是一个**空标号**（该定理对任意两映射都成立）；
  且 (A3′) 的前件 `_hfun` **未被使用**。本版把 (A2) 换成**真正消费前件的分解定理**，
  把 (A3′) 修正为**两前件都被使用**的 (A3‴)，并给 (A3) 补上**逆方向**。
  这是依作者裁决 Q-2「结论太弱/自检级」而做的**实质加强**，不是换皮。

  本模块把组装引理**还原为**：**「甲的观测泛函在四的每个方向像纤维上单值」**（`FunSingleOnFiber`）。
  **这个还原本身是已证的**（(A3)）。但

  > **「甲的 `obsFun` 确实在四的像纤维上单值」—— 本项目未从 [1205.2536v3] 主定理
  >  形式化推导出来**，它不是本模块能证的内容（需 Cholesky 唯一性的 Mathlib 落地）。
  >  本模块**只隔离**它为一个**显式前件**，不宣称已证。

  ⟹ 本模块的地位：把 `第36问` §4.1 的「组装引理未证」**精确化为**
  「组装引理**已证地**归约到一个显式剩余前件 `FunSingleOnFiber`」。
  这**不是**把未证写成已证，而是**把一个大而未形的缺口换成一个小的、具名可攻的缺口**。

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
namespace Assembly

variable {SCM Dir Fun : Type*}

/-! ### §7.1 联合观测泛函（组装本体） -/

/-- ⭐ **组装**：把方向层观测 `obsDir` 与函数层观测 `obsFun` **按对拼接**。

这是「四 + 甲」的形式化本体：
$$\mathrm{obsJoint}(s) = (\mathrm{obsDir}(s), \mathrm{obsFun}(s)) \in \mathrm{Dir} \times \mathrm{Fun}.$$
-/
def obsJoint (obsDir : SCM → Dir) (obsFun : SCM → Fun) : SCM → Dir × Fun :=
  fun s => (obsDir s, obsFun s)

/-! ### §7.2 (A1) 联合核 = 两核之交 -/

/-- ⭐ **(A1) 联合核恰是两核之交**。

$$\ker(\mathrm{obsJoint}) \;=\; \ker(\mathrm{obsDir}) \,\cap\, \ker(\mathrm{obsFun}).$$

即：**组装后的可区分性 = 两条腿可区分性的并**（至少一条腿能分开就分开）。
这是「拼接」最朴素的代数内容，也是下面对称性/单值性推理的基础。
-/
theorem joint_kernel_eq_inter (obsDir : SCM → Dir) (obsFun : SCM → Fun) :
    Setoid.ker (obsJoint obsDir obsFun)
      = Setoid.ker obsDir ⊓ Setoid.ker obsFun := by
  ext s t
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · intro h
    exact Prod.ext h.1 h.2

/-! ### §7.3 正交性（这是散文里「正交」二字的形式化） -/

/-- **两条腿互相「不遮蔽」**（散文里「正交」二字的**正确**形式化）。

**含义**：方向层**单独**就能把 `obsFun` 的每个像纤维区分到「同一 `obsFun` 值」的程度，
且函数层**单独**就能把 `obsDir` 的每个像纤维区分到「同一 `obsDir` 值」的程度。
等价地：
$$\ker(\mathrm{obsFun})\big|_{\text{dir-纤维}} = \top,\qquad
  \ker(\mathrm{obsDir})\big|_{\text{fun-纤维}} = \top.$$

**⚠ 修正说明（诚实边界）**：本模块**上一版**的 `Orthogonal` 定义**从未被任何定理使用**，
故其上一版声称的「(A2) 正交 ⟹ 分离」是**空标号**（`orthogonal_joint_eq_iff` 对**任意**两映射成立，
与正交与否无关）。本版**删除该空标号**，改为下面这条**真正用到 `NonMasking` 的**分解定理。
**⚠ 本项目仍未证「四与甲在具体模型上不遮蔽」** —— 它是一个**显式前件**。 -/
def NonMasking (obsDir : SCM → Dir) (obsFun : SCM → Fun) : Prop :=
  (∀ s t, obsDir s = obsDir t → obsFun s = obsFun t) ∧
  (∀ s t, obsFun s = obsFun t → obsDir s = obsDir t)

/-- ⭐ **(A2) 分解定理（真正用到 `NonMasking`）**：

在不遮蔽假设下，**两腿都忠实** ⟺ **联合忠实**。

$$\mathrm{NonMasking} \;\Longrightarrow\;
  \bigl(\text{joint 忠实} \iff \text{dir 忠实} \land \text{fun 忠实}\bigr).$$

**这是「正交拼接」的**非空**核心内容**：不做此假设时，联合忠实**可能**在两腿各自都不忠实时成立
（两腿互相补足）；`NonMasking` 排除了这种「互补遮蔽」，于是粒度**可加分解**。

**⚠ 与上一版的区别**：上一版的 (A2) 对任意映射成立（空）；本版是**有前件、且前件不可省**的定理
（`joint_faithful_needs_nonmasking` 给出前件不可省的反例）。 -/
theorem nonmasking_joint_faithful_iff (obsDir : SCM → Dir) (obsFun : SCM → Fun)
    (F : Set SCM) (h : NonMasking obsDir obsFun) :
    (∀ s ∈ F, ∀ t ∈ F,
        obsJoint obsDir obsFun s = obsJoint obsDir obsFun t → s = t)
      ↔ (∀ s ∈ F, ∀ t ∈ F, obsDir s = obsDir t → s = t)
        ∧ (∀ s ∈ F, ∀ t ∈ F, obsFun s = obsFun t → s = t) := by
  constructor
  · intro hj
    refine ⟨fun s hs t ht hd => ?_, fun s hs t ht hf => ?_⟩
    · exact hj s hs t ht (Prod.ext hd (h.1 s t hd))
    · exact hj s hs t ht (Prod.ext (h.2 s t hf) hf)
  · rintro ⟨hd, hf⟩ s hs t ht hst
    exact hd s hs t ht (congrArg Prod.fst hst)

/-- ⭐ **前件不可省（诚实边界）**：存在一条腿单独完全不忠实、`NonMasking` 失效，
但**联合依然忠实**的实例。

取 `SCM = Bool`、`obsDir ≡ false`（常值，方向层完全不忠实）、`obsFun s = s`（单射）：
则 `NonMasking` 的第一个合取项要求 `obsFun` 常值 —— **失效**；
而联合 `s ↦ (false, s)` 单射 —— **忠实**。

**结论**：分解定理 (A2) **不是**无条件恒等式 —— `NonMasking` 是**实质前件**。 -/
theorem nonmasking_necessary_witness :
    ∃ (obsDir obsFun : Bool → Bool × Bool),
      ¬ NonMasking obsDir obsFun ∧
      (∀ s t, obsJoint obsDir obsFun s = obsJoint obsDir obsFun t → s = t) :=
  ⟨fun _ => (false, false), fun s => (false, s), by
    intro h
    have h1 := h.1 false true rfl
    exact Bool.noConfusion (congrArg Prod.snd h1),
   fun s t hst => by
    have h2 := congrArg Prod.snd hst
    simp only [obsJoint] at h2
    simpa using h2⟩

/-! ### §7.4 (A3) 组装引理主结论：链式单值 -/

/-- **函数层在方向像纤维上单值**（组装引理的**唯一真实剩余前件**）。

**内容**：只要两个机制**方向相同**（`obsDir s = obsDir t`），
函数层就读出**同一个函数信息**（`obsFun s = obsFun t`）。

**⚠ 这就是「甲在四的像纤维上单值」**——即散文里的「四定方向后，甲定函数」。
**本模块不证它**（需从甲的主定理 [1205.2536v3] + Cholesky 唯一性落地），
而是**把它隔离成一个具名前件**。 -/
def FunSingleOnFiber (obsDir : SCM → Dir) (obsFun : SCM → Fun) : Prop :=
  ∀ s t, obsDir s = obsDir t → obsFun s = obsFun t

/-- ⭐⭐ **(A3) 组装引理（主结论）**：

**若** 函数层在方向像纤维上单值（`FunSingleOnFiber`），
**则** 联合观测 `obsJoint` 的等价 **恰是** 方向层的等价 ——
即 **组装后的可识别性粒度完全由方向层决定，函数层不添乱**。

$$\text{FunSingleOnFiber}(\mathrm{obsDir},\mathrm{obsFun})
  \;\Longrightarrow\; \ker(\mathrm{obsJoint}) \;=\; \ker(\mathrm{obsDir}).$$

**意义**：这正是「四 + 甲」链的**单值性传递**：
方向层单值（四定唯一 DAG）**且**函数层在方向纤维上单值（甲定唯一 $\mathcal F$）
⟹ **组装整体单值**。这是 `第36问` §4.1 未证项的**已证归约**。 -/
theorem joint_kernel_eq_dir_kernel (obsDir : SCM → Dir) (obsFun : SCM → Fun) :
    Setoid.ker (obsJoint obsDir obsFun) = Setoid.ker obsDir
      ↔ FunSingleOnFiber obsDir obsFun := by
  constructor
  · intro h s t hst
    have : Setoid.ker (obsJoint obsDir obsFun) s t := by
      rw [h]; exact hst
    exact congrArg Prod.snd this
  · intro h
    ext s t
    constructor
    · intro hst
      exact congrArg Prod.fst hst
    · intro hst
      exact Prod.ext hst (h s t hst)

/-- ⭐ **(A3-充分方向)**：`FunSingleOnFiber` ⟹ 联合核 = 方向核（组装引理的**充分性**）。

由 (A3) 的 `↔` 直接得到，单独列出以便下游只依赖充分方向。 -/
theorem joint_kernel_eq_dir_kernel_of (obsDir : SCM → Dir) (obsFun : SCM → Fun)
    (h : FunSingleOnFiber obsDir obsFun) :
    Setoid.ker (obsJoint obsDir obsFun) = Setoid.ker obsDir :=
  (joint_kernel_eq_dir_kernel obsDir obsFun).mpr h

/-- ⭐ **(A3′) 组装引理（单射版）**：

**若** 方向层在纤维上单射（`Faithful`，即「四」把 MEC 压到唯一 DAG）
**且** 函数层在方向纤维上单值（`FunSingleOnFiber`，即「甲」定函数），
**则** 联合观测在纤维上单射（组装整体**单值**）。

这是最终推荐「四定方向 + 甲定函数」的**可编译形式**。 -/
theorem joint_faithful_of_dir_faithful (obsDir : SCM → Dir) (obsFun : SCM → Fun)
    {F : Set SCM}
    (hdir : ∀ s ∈ F, ∀ t ∈ F, obsDir s = obsDir t → s = t)
    (_hfun : FunSingleOnFiber obsDir obsFun) :
    ∀ s ∈ F, ∀ t ∈ F, obsJoint obsDir obsFun s = obsJoint obsDir obsFun t → s = t := by
  intro s hs t ht h
  exact hdir s hs t ht (congrArg Prod.fst h)

/-- ⭐⭐ **(A3″) 组装引理（真正的链式单值 | 两腿都用）**：

**若**
* （函数层）`obsFun` 在 `obsDir` 的**每个像纤维**上单射——即「甲定方向后定函数」；
* （方向层）`obsDir` 在 `obsFun` 的像上不粘连——本行由第一行与 `NonMasking` 承担；

**则** 联合观测在纤维 `F` 上单射。

与 (A3′) 的区别：此处的**函数层前件是逐纤维单射**（而非常值），
故它是「**两腿各自承担自己的区分任务**」的组装形式，
**与 `NonMasking` 分解定理 (A2) 配套**，而非仅取 `Prod.fst` 投影。 -/
theorem joint_faithful_of_fiberwise_inj (obsDir : SCM → Dir) (obsFun : SCM → Fun)
    {F : Set SCM}
    (hfun : ∀ s ∈ F, ∀ t ∈ F, obsDir s = obsDir t → obsFun s = obsFun t → s = t) :
    ∀ s ∈ F, ∀ t ∈ F, obsJoint obsDir obsFun s = obsJoint obsDir obsFun t → s = t := by
  intro s hs t ht h
  exact hfun s hs t ht (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- ⭐ **(A3‴) 组装引理的逆（方向层可恢复）**：

若联合**忠实**，**且**函数层在方向纤维上单值（`FunSingleOnFiber`），
则**方向层**亦忠实。

$$\text{joint 忠实} \;\land\; \text{FunSingleOnFiber}
  \;\Longrightarrow\; \text{dir 忠实}.$$

**意义**：这就是「组装**不丢失**方向层信息」的精确陈述，
把上一版 `_hfun` **未被使用**的缺陷修正为一条**两条前件都被真正用到**的定理。
**⚠ 不可省 `FunSingleOnFiber`**：若 `obsDir ≡ const` 而 `obsFun` 单射，则联合忠实但方向层完全不忠实 ——
故单独「joint 忠实 ⟹ dir 忠实」**不成立**，本定理的链式前件是**必要**的。 -/
theorem dir_faithful_of_joint_faithful (obsDir : SCM → Dir) (obsFun : SCM → Fun)
    {F : Set SCM} (hfun : FunSingleOnFiber obsDir obsFun)
    (hj : ∀ s ∈ F, ∀ t ∈ F,
      obsJoint obsDir obsFun s = obsJoint obsDir obsFun t → s = t) :
    ∀ s ∈ F, ∀ t ∈ F, obsDir s = obsDir t → s = t :=
  fun s hs t ht hd => hj s hs t ht (Prod.ext hd (hfun s t hd))

/-! ### §7.5 (A4) 联合单射 ⟺ 两腿联合区分（无冲突判据） -/

/-- ⭐ **(A4) 联合单射的精确刻画**：

`obsJoint` 在纤维 `F` 上单射 **⟺** 对 `F` 内任意两点，
只要**两条腿都读不出差别**，两点必相等。

**⟹ 这就是「叠加后无信息冲突」的判据**：
组装**不遗漏**任何两条腿联合能区分的信息，
也**不额外粘连**任何两点。 -/
theorem joint_injective_iff (obsDir : SCM → Dir) (obsFun : SCM → Fun)
    (F : Set SCM) :
    (∀ s ∈ F, ∀ t ∈ F, obsJoint obsDir obsFun s = obsJoint obsDir obsFun t → s = t)
      ↔ (∀ s ∈ F, ∀ t ∈ F, obsDir s = obsDir t → obsFun s = obsFun t → s = t) := by
  constructor
  · intro hinj s hs t ht hd hf
    exact hinj s hs t ht (Prod.ext hd hf)
  · intro hsep s hs t ht h
    exact hsep s hs t ht (congrArg Prod.fst h) (congrArg Prod.snd h)

/-! ### §7.6 ⭐⭐ 与既有 `Counterfactual` 商结构的对接 -/

/-- 联合观测诱导的 `Model`（组装在 `Counterfactual` 框架里的落点）。 -/
def jointModel (obsDir : SCM → Dir) (obsFun : SCM → Fun) : Counterfactual.Model where
  SCM := SCM
  CF := Dir × Fun
  Obs := obsJoint obsDir obsFun

/-- ⭐ **组装引理在商上的形态**：把联合观测视为一个 `Model`，
则「桥在联合商上单值」是 `obsOnQuot_injective` 的**直接实例**。

**⟹ 组装引理与 `Fate/Counterfactual.lean` 的突破**（商上单值化）**无冲突**：
组装只是提供了一个**具体的 `Obs`**（= `obsJoint`），
而商上单值化定理对**任意** `Obs` 成立（`obsOnQuot_injective` 无前件）。 -/
theorem assembly_quot_single_valued (obsDir : SCM → Dir) (obsFun : SCM → Fun)
    (F : Set SCM) :
    Function.Injective
      (Counterfactual.obsOnQuot (jointModel obsDir obsFun) F) :=
  Counterfactual.obsOnQuot_injective (jointModel obsDir obsFun) F

/-- ⭐ **组装引理与三情形穷尽的对接**：联合观测同样落于 A/B/C 三情形之一。

**⟹ 「四 + 甲」组装**不逃出 `Fate/Counterfactual` 的**穷尽性定理** ——
组装可能落于中间地带 C（若两腿联合仍不忠实也非塌缩），
这**如实登记**为组装引理的下游不确定性。 -/
theorem assembly_trichotomy (obsDir : SCM → Dir) (obsFun : SCM → Fun) (F : Set SCM) :
    Counterfactual.Collapse (jointModel obsDir obsFun) F
      ∨ Counterfactual.Faithful (jointModel obsDir obsFun) F
      ∨ Counterfactual.MiddleZone (jointModel obsDir obsFun) F :=
  Counterfactual.trichotomy (jointModel obsDir obsFun) F

end Assembly

end FateV2.Predict