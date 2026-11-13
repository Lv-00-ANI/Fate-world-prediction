import FateWorld.Legacy.Assembly
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-! ===========================================================================
  §8  「四 + 甲」组装引理的**非空实例**（Assembly Instance）—— 最小可编译落点

  **来源**：`第36问-系统对比.md` §7.1、`第36问-综合-最终推荐与不确定性.md` §4.1 第 1 条。

  ## 这一步在填什么缺口

  `Fate/Assembly.lean` 已经把「四 + 甲」组装引理**已证地**归约为**一个显式前件**：

  > `FunSingleOnFiber obsDir obsFun` —— 「甲的函数观测在四的方向像纤维上单值」。

  但 `Assembly.lean` 的诚实边界写明：
  > **「甲的 `obsFun` 确实在四的像纤维上单值」—— 本项目未从 [1205.2536v3] 主定理
  >  形式化推导出来**，它不是本模块能证的内容（需 Cholesky 唯一性的 Mathlib 落地）。

  **⟹ 结果是：组装引理的全部定理都对任意 `obsDir/obsFun` 成立，但项目里**
  **从未给出一个 `FunSingleOnFiber` 实际成立的模型** —— 即**组装链可能空转**。

  ## 本模块的任务（最小、可编译、非空）

  构造一个**具体的线性机制类型** `LinSEM`，在其上**定义** `obsDir` / `obsFun`，
  并**证明** `FunSingleOnFiber` **确实成立**，从而让 `Fate.Assembly` 的全部定理
  **有一个非真空的实例**。

  ### 关键设计：`obsFun` 是 `obsDir` 的函数（在这次参数化里）

  在甲（线性 + 高斯 + 等方差）的**语义**里：

  * **方向层信息** = 结构矩阵 `B` 的**结构零模式**（哪些 `B i j ≠ 0`，即 DAG 的边集）。
  * **函数层信息** = 完整参数 `(B, ω)`（系数 + 噪声方差）。

  **线性代数事实**：完整参数 `(B, ω)` **蕴含**其零模式（`B i j = 0` 可直接读出），
  故 `obsFun` 的**第一分量**（`B`）**决定** `obsDir`（零模式）。
  **⟹ 若两个机制的 `obsFun` 相等，则 `obsDir` 相等。**

  **⚠ 这里的诚实边界（不得省略）**：
  本模块证的 `FunSingleOnFiber` 是**「方向层的像纤维由方向层自身的构造坍缩」**，
  **不是**「从观测数据 `P(X,Y)` 唯一恢复 `(B, ω)`」。
  **前者是集合论/线性代数恒等式（本模块证），后者才是 [1205.2536v3] 主定理的内容（未证）。**

  **⟹ 本模块把组装链从「无实例」推进到「有一个集合论层实例」；
  观测数据 → 参数的识别那一步仍为未证的显式前件**（见 §8.5 的 `DataRecoversParams`）。

  **⚠ 无硬编码**（依作者裁决 Q-1）：全程无具体常数、无 `sorry`/`axiom`。
  =========================================================================== -/

namespace Fate

namespace AssemblyInstance

open Assembly

set_option autoImplicit false

/-! ### §8.1 线性机制类型（甲的本体，参数化子）

一个**线性结构方程模型**在甲语义下由两部分决定：
* `B : Matrix n n ℝ` —— 结构系数矩阵（`B i j ≠ 0` 表示 `j → i` 有一条边）；
* `ω : n → ℝ` —— 各节点的噪声方差（甲假设**等方差**时它们相等，此处保留一般形式，
  等方差作为**可选前件**在 §8.4 使用）。

**⚠ 索引取任意有限类型 `n`**，不使用固定基数。 -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **甲的本体：线性结构方程模型**（参数级）。

`B` 是结构系数矩阵，`ω` 是各节点噪声方差。
甲的主定理 [1205.2536v3] 断言（在等方差 + 高斯下）该参数由 `P(X,Y)` 唯一识别——
**该断言本模块不证**（见 §8.5）。 -/
structure LinSEM (n : Type*) where
  /-- 结构系数矩阵（`B i j` = 边 `j → i` 的系数）。 -/
  B : Matrix n n ℝ
  /-- 各节点噪声方差。 -/
  ω : n → ℝ

/-! ### §8.2 方向层观测（「四」的语义内容）与函数层观测（「甲」的语义内容） -/

/-- **方向层观测 `obsDir`**：读出结构矩阵的**零模式**（即 DAG 的边集）。

`obsDir s` 是「`s.B` 在哪一格非零」的真值表 —— 它就是**方向信息**
（要知道 `j → i` 有无边，看 `B i j` 是否为零）。 -/
noncomputable def obsDir (s : LinSEM n) : Matrix n n Bool :=
  fun i j => s.B i j ≠ 0

/-- **函数层观测 `obsFun`**：读出完整参数 `(B, ω)`。

甲的语义内容（系数 + 噪声方差）就是它 —— `FunSingleOnFiber` 要证的正是
「方向层定住后，函数层不再有自由度」。 -/
def obsFun (s : LinSEM n) : Matrix n n ℝ × (n → ℝ) :=
  (s.B, s.ω)

/-! ### §8.3 ⭐ 核心：`FunSingleOnFiber` 在 `LinSEM` 上**确实成立** -/

/-- ⭐⭐ **`FunSingleOnFiber` 的非空见证（本模块的主结论）**：

$$\text{FunSingleOnFiber}(\mathrm{obsDir}, \mathrm{obsFun}) \quad \text{在 } \mathrm{LinSEM}\text{ 上成立}.$$

**证明**：`obsFun s = obsFun t` 直接给出 `s.B = t.B`，
而 `obsDir` 只依赖 `B`，故 `obsDir s = obsDir t`（更强：`←` 方向）。
这里我们证的是所需的 `→` 方向：若 `obsDir s = obsDir t` 则 `obsFun s = obsFun t`
—— **注意这并非由 `B` 的零模式唯一确定 `B`**（零模式弱于具体数值）。

**⚠ 修正（诚实边界）**：上面这句揭示了本模块的**真实内容**：
`FunSingleOnFiber` 要求「方向相同 ⟹ 函数相同」，
但在 `LinSEM` 里**方向是 `B` 的零模式、函数是 `B` 本身**，
**零模式不唯一决定矩阵**（`1` 与 `2` 都是非零）。

**⟹ 因此 `obsDir` / `obsFun` 的朴素选取使 `FunSingleOnFiber` **不成立**！
这正是本模块要**暴露**的事实：
`Assembly.lean` 的剩余前件**不是**集合论自动成立的，它**必须由模型构造承担**。

**修法**：让 `obsDir` 携带**足够**的方向信息 —— 即把「方向层」定义为
**包含系数在内的完整 DAG 语义**（这与「四」的文献表述一致：四识别的是
`PA(Y)` 的**结构**，而在甲下方向层与函数层共用同一份协方差）。见 §8.3′。 -/
theorem funSingleOnFiber_zeroPattern_fails :
    ∃ s t : LinSEM (Fin 1),
      obsDir s = obsDir t ∧ obsFun s ≠ obsFun t := by
  refine ⟨(⟨fun _ _ => 1, fun _ => 1⟩ : LinSEM (Fin 1)),
          (⟨fun _ _ => 2, fun _ => 1⟩ : LinSEM (Fin 1)), ?_, ?_⟩
  · -- 零模式相同（两矩阵全非零）
    ext i j
    simp [obsDir]
  · -- 但函数不同（B 为 1 vs 2），提取 0-0 分量即得矛盾
    intro h
    have h00 : (1 : ℝ) = 2 :=
      congrFun (congrFun (congrArg Prod.fst h) 0) 0
    norm_num at h00

/-! ### §8.3′ 正确的方向层：包含系数数值的「机制方向」

上一条定理说明：若方向层只读**支撑（零模式）**，则函数层仍有数值自由度，
`FunSingleOnFiber` **不成立**。

**这正是「四」在文献里的真实内容**：多环境/不变性识别的是 **完整结构方程的方向与形式**
（[1501.01332]）——方向层与函数层在甲下是**同一个协方差的两个分解面**，
不是「支撑 vs 数值」的粗分割。

**故正确的 `obsDir`（对组装引理而言）应取「完整参数化的商」**：
下面我们取 `obsDir := obsFun`（方向层即完整机制），
这在**组装引理的意义下是合法的**（引理只要求「方向定则函数定」，不强求方向弱于函数）。

**⚠ 但这会让三份文档里「四只买方向、甲只买函数」的**分工**陈述失效** ——
**如实登记为：组装引理在参数化层面可被满足，但满足它的 `obsDir` 必须已经包含函数信息；
这与「两腿独立」的直觉**不同**，是本模块暴露的**真实结构发现**。见 §8.6。 -/

/-- **方向层 = 完整机制**（满足组装引理的选取）。 -/
noncomputable def obsDirFull (s : LinSEM n) : Matrix n n ℝ × (n → ℝ) :=
  obsFun s

omit [Fintype n] [DecidableEq n] in
/-- ⭐⭐ **`FunSingleOnFiber` 在 `obsDirFull` 上成立**（组装引理的非空实例）。

**平凡但非真空**：`obsDirFull = obsFun` 时前件「方向同 ⟹ 函数同」自动成立。
**这正暴露了组装引理的一个**结构性事实**：它**不区分**方向层是否**真的弱于**函数层。 -/
theorem funSingleOnFiber_full : FunSingleOnFiber (obsDirFull (n := n)) obsFun :=
  fun _ _ h => h

/-! ### §8.4 把组装链的全部结论实例化到 `LinSEM` -/

omit [Fintype n] [DecidableEq n] in
/-- ⭐ **组装引理 (A3) 在 `LinSEM` 上的实例**：联合核 = 方向核。 -/
theorem linSem_joint_kernel_eq_dir_kernel :
    Setoid.ker (obsJoint (obsDirFull (n := n)) obsFun)
      = Setoid.ker (obsDirFull (n := n)) :=
  joint_kernel_eq_dir_kernel_of _ _ funSingleOnFiber_full

omit [Fintype n] [DecidableEq n] in
/-- ⭐ **组装忠实 (A3″) 在 `LinSEM` 上的实例**（**真正的证明，前件不重复结论**）。

**陈述**：在 `LinSEM` 上，`obsDirFull` 与 `obsFun` 的联合读出 `obsJoint`
在**任意**纤维 `F` 上单射 —— 即「联合读出区分两点 ⟹ 两点相等」。

**证明**（**无前件，直接从构造推出**）：
`obsDirFull s = obsFun s`，故
`obsJoint obsDirFull obsFun s = (obsFun s, obsFun t)`。
于是 `obsJoint … s = obsJoint … t` 的第一分量给出 `obsFun s = obsFun t`，
即 `(s.B, s.ω) = (t.B, t.ω)`，逐分量拆开即 `s = t`。∎

**⚠ 与旧版的区别**：旧版把结论逐字当作前件 `h` 再原样交出（零内容）。
本版**没有任何假设**，内容全部来自 `obsDirFull := obsFun` 这一构造 ——
这也正是 `funSingleOnFiber_full` 所揭示的结构性事实（方向层已含函数信息）。 -/
theorem linSem_joint_faithful {F : Set (LinSEM n)} :
    ∀ s ∈ F, ∀ t ∈ F,
      obsJoint (obsDirFull (n := n)) obsFun s =
      obsJoint (obsDirFull (n := n)) obsFun t → s = t := by
  intro s _ t _ h
  -- 第一分量即 `obsFun s = obsFun t`（因为 `obsDirFull = obsFun`）
  have hf : obsFun s = obsFun t := congrArg Prod.fst h
  have hB : s.B = t.B := congrArg Prod.fst hf
  have hω : s.ω = t.ω := congrArg Prod.snd hf
  cases s
  cases t
  simp_all

omit [Fintype n] [DecidableEq n] in
/-- ⭐ **组装落于 `Fate.Counterfactual` 三情形**（穷尽性的实例化）。 -/
theorem linSem_trichotomy (F : Set (LinSEM n)) :
    Counterfactual.Collapse
        (Assembly.jointModel (obsDirFull (n := n)) obsFun) F
      ∨ Counterfactual.Faithful
        (Assembly.jointModel (obsDirFull (n := n)) obsFun) F
      ∨ Counterfactual.MiddleZone
        (Assembly.jointModel (obsDirFull (n := n)) obsFun) F :=
  assembly_trichotomy _ _ F

omit [Fintype n] [DecidableEq n] in
/-- ⭐ **组装在商上单值**（`obsOnQuot_injective` 的实例化）。 -/
theorem linSem_quot_single_valued (F : Set (LinSEM n)) :
    Function.Injective
      (Counterfactual.obsOnQuot
        (Assembly.jointModel (obsDirFull (n := n)) obsFun) F) :=
  assembly_quot_single_valued _ _ F

/-! ### §8.5 ⭐ 观测数据 → 参数：**未证的显式前件**（把真实缺口具名化） -/

/-- **`DataRecoversParams`（未证的显式前件）**：

「观测分布 `P` 唯一决定线性参数 `(B, ω)`」。

**这正是 [1205.2536v3] 主定理在等方差 + 高斯下的内容**，
**本模块不证** —— 需 Cholesky 唯一性的 Mathlib 落地。
本模块只把它**隔离为一个具名前件**，与 `Assembly.lean` 隔离 `FunSingleOnFiber` 的做法一致。 -/
def DataRecoversParams {Obs : Type*} (read : LinSEM n → Obs) : Prop :=
  ∀ s t, read s = read t → s = t

omit [Fintype n] [DecidableEq n] in
/-- ⭐ **缺口链的最后一段（如实登记，不冒充定理）**：

**若** 观测读出 `read` 满足 `DataRecoversParams`（= 甲的主定理），
**则** 该读出在参数层**单值**——即桥在甲下**单值**。

**本模块只证「`DataRecoversParams` ⟹ 单值」这条恒等式的**逻辑部分**；
`DataRecoversParams` 本身在具体 `read` 下是否成立——**未证**（§4.1 缺口本体）。 -/
theorem single_valued_of_dataRecoversParams
    {Obs : Type*} (read : LinSEM n → Obs) (h : DataRecoversParams read) :
    ∀ s t : LinSEM n, read s = read t → s = t :=
  h

/-! ### §8.6 诚实边界（本模块**不**主张的） -/

/-!
⚠ **1. 本模块没有证 [1205.2536v3] 主定理。**
   §8.3′ 的 `funSingleOnFiber_full` 是**平凡的**（`obsDirFull = obsFun`），
   它的价值**不是**证明了组装，而是**证明了组装引理需要一个「方向层已含函数信息」
   的 `obsDir`**** —— 这与三份文档里「四只买方向、甲只买函数」的**分工叙事**不一致。

⚠ **2. 本模块最重要的发现是 §8.3 的反例** `funSingleOnFiber_zeroPattern_fails`：
   在「方向 = 支撑 / 函数 = 数值」的**朴素参数化**下，`FunSingleOnFiber` **不成立**。
   **⟹ 组装引理不是集合论恒等式，它对模型的 `obsDir` 选取是**实质约束**。**
   上一版把组装说成「两腿正交、自动拼接」的印象，**在此被反例纠正**。

⚠ **3. 剩余真实缺口（必须与结论同时交付）**：
   - `DataRecoversParams`（观测 → 参数）——**未证**，= [1205.2536v3] 主定理。
   - 一个 `obsDir` **真弱于** `obsFun` 却仍满足 `FunSingleOnFiber` 的**非平凡实例** ——**未构造**。
     （这才是「四买方向、甲买函数、二者真独立」的正当形式化；本模块只证它**存在**需要更多构造，
     并给出朴素选取**失败**的反例。）
   - 等方差 + 高斯 + Cholesky 唯一性的 Mathlib 落地 ——**未做**（Mathlib 仅有 `LDL`，无打包 Cholesky 唯一性）。

⚠ **4. 全部结论仍为参数/集合论层**；「可识别 ⟹ 可用」的样本层**另计**（裁决 K）。
-/

end AssemblyInstance

end Fate
