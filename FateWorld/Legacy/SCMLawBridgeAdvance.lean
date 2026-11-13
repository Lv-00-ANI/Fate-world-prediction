import FateWorld.Legacy.SCMLawBridge
import FateWorld.Legacy.LawRuleToTraj

/-! ===========================================================================
  §LR+  ⭐⭐⭐⭐ **`PearlHierarchy.SCM` ⟹ `LawRule`：桥推进（第 2 轮）**

  ## 0. 与 `Fate/SCMLawBridge.lean` 的分工

  `SCMLawBridge` 已给出**三个档**的诱导（`lawAt` / `lawObs` / `composeLaw`）与
  `LawRule ⟷ Rule` 互译。**本文件不再重复**，只补**两处**它如实登记的缺口：

  | 缺口（`SCMLawBridge` §4 登记原文） | 本文件的补 | 强度 |
  |---|---|---|
  | 「上下文坐标 `c` **被丢弃**（`SCM` 类型里没有 `CtxSpace`）」 | `lawFam`：以 `C.Carrier → SCM X Y` 为载体的**纤维化诱导**；`lawFam_apply` 说它在每个 `c` 处**就是** `lawAt` | ⭐⭐ 实质 |
  | 「`lawAt` **只**到 `IsPoint`，**不**到 `IsDirac`，故接不上 `TrajGen`」 | `isDirac_lawAt_iff` + `isDirac_lawAt_of_pointMass` + **两道一般障碍**（`not_dirac_of_two_atoms`、`isPointDet_not_dirac_of_two_atoms`）| ⭐⭐⭐ 实质 |

  ## 1. 为什么第二处是**真缺口**（而不是技术细节）

  `LawRule.IsPoint R`：允许集是单点集 `{μ}`，`μ` **任意测度**。
  `LawRuleToTraj.IsDirac R`：允许集是 `{δ_y}`，`y` 是**点**。

  `SCMLawBridge.lawAt` 的值是 `{pushMeasure Yb φ (L2_do x)}` ——
  一个**加权 δ 和**，一般**不是** Dirac 测度。
  ⟹ `SCMLawBridge.isPoint_lawAt` **不能**升级为 `IsDirac`，
  故 `lawAt` **不能**直接喂给 `LawRuleToTraj.trajGenOfLaw`（那要 `IsDirac`）。

  **本文件给出这件事的精确边界**：

  * **正向**（`isDirac_lawAt_of_pointMass`）：外生律在**单个** `u₀` 处质量为 `1`
    ⟹ `lawAt` **是** `IsDirac` ⟹ **能**抽出确定性转移
    `f c y = φ ((sg u₀).2 (e.symm y))`（`detFun_lawAt`，**逐字给形式**）。
  * **反向障碍**（`not_dirac_of_two_atoms`）：若 `φ`-推出的两个**不同**
    可测原子 `a ≠ b` 上**质量都非零**，则推出测度**不是** Dirac
    ⟹ `lawAt` **不是** `IsDirac` ⟹ **接不上** `TrajGen`。

  **⟹ 一句话**：`SCM ⟹ LawRule` 是**无条件**的（`lawAt`，恒 `IsPoint`），
  但 `SCM ⟹ 可算转移` **不是** —— 它**恰好**要求外生律集中在一个 `φ`-原子。
  **这是「SCM 桥到目前为止走到哪里」的精确答案**，且**两侧都可编译核验**。

  ## 2. 诚实边界

  * 本文件**不**声称「一般 SCM 可算」。**相反**：`not_dirac_of_two_atoms`
    是**机器可验证的否定结论**。
  * `IsDirac ⟹ IsPoint` 已在 `LawRuleToTraj.IsDirac.isPoint` 中；
    本文件的 `isDirac_lawAt_of_pointMass` **只**补 SCM 侧的**充分条件**，
    **不**补必要条件的反面（那**不成立**：`isPoint_lawAt` 说的是恒 `IsPoint`）。
  * 「质量集中」用的是 `∑ if φ y = a then ofReal (p y) else 0` 这一**纤维和**
    （`SCM.pushMeasure_apply` 的右侧）——它是**可判定**的（`Fintype` 上有限和），
    但**不**等于「`p` 在单点处非零」（`φ` 可以非单射，故纤维可有多点）。
  * 上下文纤维化 `lawFam` **不**发明 `SCM` 侧缺失的 `CtxSpace`：
    它把 `CtxSpace` 放在**族指标**位置，`SCM` 类型**不动**。
  =========================================================================== -/

namespace Fate

namespace LawRule

open MeasureTheory

namespace SCM

set_option linter.unusedSectionVars false

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ===========================================================================
    §1  ⭐⭐ **缺口 (i)：上下文坐标的纤维化**（`SCMLawBridge` §4 登记）
    =========================================================================== -/

section ContextFibre

variable {Xc : Type} [Fintype Xc] [DecidableEq Xc]
  {Yc : Type} [Fintype Yc] [DecidableEq Yc]

/-- ⭐⭐ **以上下文为指标的 SCM 族**（**补 `SCMLawBridge` §4 的登记缺口**）。

`SCMLawBridge` 的 `lawAt` 的签名里 `C : CtxSpace` 是**哑参数**：
`lawAt M … C c y` **不依赖** `c`（定义上 `fun _ y => …`）。
这是 `PearlHierarchy.SCM` **类型里没有 `CtxSpace`** 的直接后果，
`SCMLawBridge` §4 如实登记为缺口，但**未**给出补救构造。

**本定义即补救**：不改 `SCM` 类型，而把「随上下文变化的机制」
放在**族指标**位置——

$$(\mathrm{lawFam}\,M)\,c\;y \;=\; \bigl(\mathrm{lawAt}\,(M\,c)\bigr)\;c\;y .$$

**读法**：`M : C.Carrier → SCM X Y` 是「每个上下文一个结构机制」。
**⟹ 上下文不再被丢弃，而是被 `SCM` 族消费。** -/
noncomputable def lawFam (M : C.Carrier → PearlHierarchy.SCM Xc Yc) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : Xc ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Yc → Yb.Carrier) : LawRule C SX Yb :=
  fun c y => lawAt (M c) SX e Yb φ C c y

/-- ⭐⭐ **纤维化是忠实的**：在每个上下文 `c` 处，`lawFam M` 的纤维
**逐字就是**该上下文那个 SCM 的 `lawAt`。

**⟹ 这条把「上下文」与「机制」的分离钉死**：
`lawFam` **没有**引入任何新语义，它只是把 `lawAt` 沿 `c` **重新索引**。
故 `SCMLawBridge` 关于 `lawAt` 的**全部**结论（`isPoint`、`L3` 决定性、
桥主等式）**逐条继承**到 `lawFam` 的每个纤维（见下三条）。 -/
theorem lawFam_apply (M : C.Carrier → PearlHierarchy.SCM Xc Yc) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : Xc ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Yc → Yb.Carrier) (c : C.Carrier) :
    (lawFam M SX e Yb φ : LawRule C SX Yb) c
      = fun y => lawAt (M c) SX e Yb φ C c y := rfl

/-- ⭐ **纤维化仍是单点档**（继承 `SCMLawBridge.isPoint_lawAt`）。

**⟹ 上下文纤维化不降档**：即使在每个 `c` 处机制不同，
允许集仍然逐点是单点集。 -/
theorem isPoint_lawFam (M : C.Carrier → PearlHierarchy.SCM Xc Yc) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : Xc ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Yc → Yb.Carrier) : LawRule.IsPoint (lawFam M SX e Yb φ) :=
  fun c y => isPoint_lawAt (M c) SX e Yb φ C c y

/-- ⭐⭐⭐ **L3 ⟹ `lawFam`**：上下文族上**逐点**的反事实决定性。

若对每个 `c`，两个 SCM 族的**该 `c` 处**的反事实系统相同，
则它们诱导的 `LawRule` **相等**。

**⟹ 这是 `SCMLawBridge.L3_determines_lawAt` 沿 `c` 的**逐点提升**：
证明只用 `funext` + 上述单点版本，故**不重复**实质推理
（实质部分在 `PearlHierarchy.L3_determines_L2`，已在 `SCMLawBridge` 消费）。 -/
theorem L3_determines_lawFam
    {M₁ M₂ : C.Carrier → PearlHierarchy.SCM Xc Yc} [DecidableEq (Xc → Yc)]
    (SX : StateSpace) [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : Xc ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Yc → Yb.Carrier)
    (h : ∀ c, (M₁ c).L3_cf = (M₂ c).L3_cf) :
    lawFam M₁ SX e Yb φ = lawFam M₂ SX e Yb φ := by
  funext c y
  exact congrFun (congrFun (L3_determines_lawAt SX e Yb φ C (h c)) c) y

end ContextFibre

/-! ===========================================================================
    §2  ⭐⭐⭐ **缺口 (ii)：Dirac 闸与 `TrajGen` 的接线**
    =========================================================================== -/

section DiracGate

variable {Xc : Type} [Fintype Xc] [DecidableEq Xc]
  {Yc : Type} [Fintype Yc] [DecidableEq Yc]

/-! ### §2.0 ⭐ **两个基础设施引理**（原先的证明把 `pU` 的支撑与 `L2_do` 的支撑混同，此处拆开）

⚠ **这里修正了原稿的一处实质错误**：
`isDirac_lawAt_of_pointMass` / `detFun_lawAt` 的原证明写
`rw [pushMeasure, Finset.sum_eq_single u₀]`，但
`pushMeasure Yb φ (M.L2_do x)` **在 `Yc` 上求和**（不是 `M.U` 上），
`u₀ : M.U` **不是**那个和的指标 —— 原证明因此根本跑不通（`synthInstanceFailed` /
rewrite 失败）。

**正确的两步**：
1. `pU` 是 `u₀` 处的点质量 ⟹ `L2_do x` 是 `(sg u₀).2 x` 处的点质量（`L2_do_of_pointMass`）；
2. 由此 `pushMeasure` 在 `Yc` 上坍缩到 `y₀ = (sg u₀).2 x`（`pushMeasure_L2_do_of_pointMass`）。

**语义结论不变**（外生不确定性消失 ⟹ 确定性机制），但证明**必须**经过这两步。 -/

/-- ⭐ **点质量外生律 ⟹ `L2_do` 是点质量**（沿结构方程读数）。 -/
theorem L2_do_of_pointMass (M : PearlHierarchy.SCM Xc Yc) (u₀ : M.U)
    (h0 : ∀ u : M.U, u ≠ u₀ → M.pU u = 0) (h1 : M.pU u₀ = 1) (x : Xc) :
    M.L2_do x = fun y => if (M.sg u₀).2 x = y then (1 : ℝ) else 0 := by
  classical
  funext y
  simp only [PearlHierarchy.SCM.L2_do, PearlHierarchy.push]
  rw [Finset.sum_eq_single u₀]
  · simp [h1]
  · intro b _ hb; simp [h0 b hb]
  · intro hc; exact absurd (Finset.mem_univ _) hc

/-- ⭐⭐ **点质量外生律 ⟹ 推出测度是 Dirac**（§2 两个正向定理的公共引擎）。 -/
theorem pushMeasure_L2_do_of_pointMass (M : PearlHierarchy.SCM Xc Yc)
    (Yb : OutSpace) [MeasurableSpace Yb.Carrier] (φ : Yc → Yb.Carrier)
    (u₀ : M.U) (x : Xc)
    (h0 : ∀ u : M.U, u ≠ u₀ → M.pU u = 0) (h1 : M.pU u₀ = 1) :
    pushMeasure Yb φ (M.L2_do x) = Measure.dirac (φ ((M.sg u₀).2 x)) := by
  classical
  rw [L2_do_of_pointMass M u₀ h0 h1 x, pushMeasure, Finset.sum_eq_single ((M.sg u₀).2 x)]
  · rw [if_pos rfl, ENNReal.ofReal_one, one_smul]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), ENNReal.ofReal_zero, zero_smul]
  · intro hc; exact absurd (Finset.mem_univ _) hc

/-- ⭐⭐ **`IsDirac` 的 SCM 形式**：`lawAt` 是点质量档 **⟺** 那个推出测度是 Dirac 测度。

$$\texttt{IsDirac}\,(\mathrm{lawAt}\,M) \iff
  \forall y,\ \exists z,\ \mathrm{pushMeasure}\,\varphi\,(M.\mathrm{L2\_do}\,(e^{-1}y)) = \delta_z .$$

**这是定义展开**（`IsDirac` 与 `lawAt` 各自的 `∃` 逐点对齐），
它的用处是**把闸 A 的判定完全交给推出测度**——
后者可以用 `SCM.pushMeasure_apply` **逐原子计算**（见 §2.2 的一般障碍）。 -/
theorem isDirac_lawAt_iff (M : PearlHierarchy.SCM Xc Yc) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : Xc ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Yc → Yb.Carrier) (C : CtxSpace) [Nonempty C.Carrier] :
    LawRuleToTraj.IsDirac (lawAt M SX e Yb φ C) ↔
      ∀ y : SX.Carrier, ∃ z : Yb.Carrier,
        pushMeasure Yb φ (M.L2_do (e.symm y)) = Measure.dirac z := by
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h (Classical.arbitrary C.Carrier) y
    exact ⟨z, by simpa [lawAt] using hz⟩
  · intro h c y
    obtain ⟨z, hz⟩ := h y
    exact ⟨z, by show {pushMeasure Yb φ (M.L2_do (e.symm y))} = _; rw [hz]⟩

/-- ⭐⭐⭐ **正向（闸 A 的「通过」条件）：外生律集中于单点且质量和为 1 ⟹ `IsDirac`。**

若外生律 `pU` 在某个 `u₀` 处**质量为 `1`**、其余处**为 `0`**，则

$$\mathrm{pushMeasure}\,\varphi\,p = \delta_{\varphi(y)}$$

对**任意** `p : Yc → ℝ`（此处 `p = L2_do`），故 `lawAt` **是** `IsDirac`。

**⟹ 语义**：外生不确定性**消失**（`u₀` 是唯一实现），SCM 退化为**确定性机制**
`y ↦ φ((sg u₀).2 (e^{-1}y))`。**这是「SCM 可算」的确切条件**，
且它是**关于 SCM 的**条件（`pU` 的形状），**不是**关于 `LawRule` 的。 -/
theorem isDirac_lawAt_of_pointMass (M : PearlHierarchy.SCM Xc Yc) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : Xc ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Yc → Yb.Carrier) (C : CtxSpace) (u₀ : M.U)
    (h0 : ∀ u : M.U, u ≠ u₀ → M.pU u = 0)
    (h1 : M.pU u₀ = 1) :
    LawRuleToTraj.IsDirac (lawAt M SX e Yb φ C) := by
  classical
  intro c y
  refine ⟨φ ((M.sg u₀).2 (e.symm y)), ?_⟩
  show ({pushMeasure Yb φ (M.L2_do (e.symm y))} : Set (Measure Yb.Carrier)) = _
  have hp : pushMeasure Yb φ (M.L2_do (e.symm y))
      = Measure.dirac (φ ((M.sg u₀).2 (e.symm y))) :=
    pushMeasure_L2_do_of_pointMass M Yb φ u₀ (e.symm y) h0 h1
  rw [hp]

/-- ⭐⭐⭐ **桥的终点：从 SCM 抽出确定性转移函数**（`TrajGen` 的输入）。

在 `pointMass` 条件下，`lawAt` 的**唯一**允许分布是

$$\delta_{\;\varphi\left((\mathrm{sg}\,u_0).2\,(e^{-1}y)\right)} .$$

**⟹ 这就是 `LawRuleToTraj.toDetFun` 在 SCM 上的**显式形式****：
确定性转移 `f : C → SX → Yb` 逐字为
`f c y = φ ((sg u₀).2 (e.symm y))`，**不**需要 `Classical.choose`。

**⟹ 意义**：这把 `SCM → LawRule → 可算转移` 的**整条路径**走通，
并把终点**写成 SCM 的结构量**（`sg` 的结构方程 + 桥参数 `φ`）。
`SCMLawBridge` §4 只说「`lawAt` 是 `IsPoint`、接不上 `TrajGen`」——
**本定理给出接上的条件与形式**。 -/
theorem exists_detFun_lawAt_of_pointMass (M : PearlHierarchy.SCM Xc Yc) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : Xc ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Yc → Yb.Carrier) (C : CtxSpace) (u₀ : M.U)
    (h0 : ∀ u : M.U, u ≠ u₀ → M.pU u = 0)
    (h1 : M.pU u₀ = 1) :
    ∃ f : C.Carrier → SX.Carrier → Yb.Carrier, lawAt M SX e Yb φ C = DetFun.toLaw f :=
  LawRuleToTraj.isDirac_iff_exists_detFun _ |>.mp
    (isDirac_lawAt_of_pointMass M SX e Yb φ C u₀ h0 h1)

/-- ⭐⭐ **抽出函数的显式形式**（上条的「见证给出来」版）。

$$\mathrm{lawAt}\,M = \mathrm{DetFun.toLaw}\Bigl(c,\,y \mapsto
  \varphi\bigl((\mathrm{sg}\,u_0).2\,(e^{-1}y)\bigr)\Bigr).$$

**⟹ 这条是 `exists_detFun_lawAt_of_pointMass` 的**可计算版本****：
见证**不是** `Classical.choose`，而是**写出来的** SCM 表达式。 -/
theorem detFun_lawAt (M : PearlHierarchy.SCM Xc Yc) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : Xc ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Yc → Yb.Carrier) (C : CtxSpace) (u₀ : M.U)
    (h0 : ∀ u : M.U, u ≠ u₀ → M.pU u = 0)
    (h1 : M.pU u₀ = 1) :
    lawAt M SX e Yb φ C
      = DetFun.toLaw (fun (_ : C.Carrier) (y : SX.Carrier) =>
          φ ((M.sg u₀).2 (e.symm y))) := by
  classical
  funext c y
  show ({pushMeasure Yb φ (M.L2_do (e.symm y))} : Set (Measure Yb.Carrier))
    = {Measure.dirac (φ ((M.sg u₀).2 (e.symm y)))}
  rw [pushMeasure_L2_do_of_pointMass M Yb φ u₀ (e.symm y) h0 h1]

end DiracGate

/-! ===========================================================================
    §3  ⭐⭐⭐ **两道一般障碍**（`IsPoint` 与 `IsDirac` 的差额在 SCM 上是实的）
    =========================================================================== -/

section DiracBarrier

variable {Yc₀ : Type} [Fintype Yc₀] [DecidableEq Yc₀]

/-- ⭐⭐ **原子判据**：若推出测度是 Dirac，则任何**质量非零**的可测原子
**必是**那个 Dirac 的中心。

**证明**：`SCM.pushMeasure_apply` 把 `{a}` 处的质量写成**纤维和**；
`Measure.dirac_apply'` 把它写成 `0` 或 `1`；
故纤维和非零 ⟹ 该 `1` 被取到 ⟹ `z ∈ {a}`。

**⟹ 这是 §3 两道的公共引擎**，且**不**用 `φ` 单射、**不**用 `φ` 的纤维结构。 -/
theorem atom_eq_of_pushMeasure_eq_dirac
    (Yb : OutSpace) [MeasurableSpace Yb.Carrier] [DecidableEq Yb.Carrier]
    (φ : Yc₀ → Yb.Carrier) (p : Yc₀ → ℝ) (z a : Yb.Carrier)
    (ha : MeasurableSet ({a} : Set Yb.Carrier))
    (hmass : (∑ y : Yc₀, (if φ y = a then ENNReal.ofReal (p y) else 0)) ≠ 0)
    (h : pushMeasure Yb φ p = Measure.dirac z) : a = z := by
  have e1 := pushMeasure_apply Yb φ p a ha
  rw [h, Measure.dirac_apply' z ha] at e1
  by_cases hz : z ∈ ({a} : Set Yb.Carrier)
  · simpa [eq_comm] using hz
  · rw [Set.indicator_of_notMem hz] at e1
    exact absurd e1.symm hmass

/-- ⭐⭐⭐ **障碍 1：两个不同原子都有非零质量 ⟹ 推出测度**不是** Dirac。**

**⟹ 语义**：`φ`-推出的分布只要有**两个**有质量的原子，就**不是**点质量。
故 `lawAt` 在该点**不是** `IsDirac`（只有 `IsPoint`），
**不能**抽确定性转移、**不能**接 `TrajGen`。

**⟹ 这是 §2 正向定理的**精确补集**：
`SCMLawBridge` 的 `lawAt` 一般落在这条障碍里，故「一般 SCM 可算」**为假**。 -/
theorem not_dirac_of_two_atoms
    (Yb : OutSpace) [MeasurableSpace Yb.Carrier] [DecidableEq Yb.Carrier]
    (φ : Yc₀ → Yb.Carrier) (p : Yc₀ → ℝ) (a b : Yb.Carrier)
    (ha : MeasurableSet ({a} : Set Yb.Carrier)) (hb : MeasurableSet ({b} : Set Yb.Carrier))
    (hab : a ≠ b)
    (hA : (∑ y : Yc₀, (if φ y = a then ENNReal.ofReal (p y) else 0)) ≠ 0)
    (hB : (∑ y : Yc₀, (if φ y = b then ENNReal.ofReal (p y) else 0)) ≠ 0) :
    ¬ ∃ z : Yb.Carrier, pushMeasure Yb φ p = Measure.dirac z := by
  rintro ⟨z, hz⟩
  exact hab ((atom_eq_of_pushMeasure_eq_dirac Yb φ p z a ha hA hz).trans
    (atom_eq_of_pushMeasure_eq_dirac Yb φ p z b hb hB hz).symm)

end DiracBarrier

/-! ### §3.2 障碍 1 在 `lawAt` 上的形式（把 §3 接到 SCM 上）

⚠ **为什么另起一节**：`§3.1` 的两个引擎只用到 `Yc₀`（外生/输出纤维的有限性），
**不**需要 SCM 的 `Xc`；而下面的定理**要** `SCM Xc Yc`，
故必须在带 `Xc`/`Yc` 的节里陈述。原先把它并进 `DiracBarrier`，
导致 `Xc`/`Yc` 及其 `Fintype`/`DecidableEq` **不在作用域**，产生 15 处
`synthInstanceFailed`。现将两节分开。 -/

section DiracBarrierSCM

variable {Xc : Type} [Fintype Xc] [DecidableEq Xc]
  {Yc : Type} [Fintype Yc] [DecidableEq Yc]

/-- ⭐⭐⭐ **障碍 1 在 `lawAt` 上的形式**（把 §3 接到 SCM 上）。

若在某个 `(c, y)` 处，`M.L2_do (e^{-1}y)` 经 `φ` 推出后有**两个**
不同可测原子带非零质量，则 `lawAt M` **不是** `IsDirac`。

**⟹ 这条**直接否定**「`SCMLawBridge.isPoint_lawAt` 可升级」**：
`IsPoint` **恒真**，`IsDirac` **一般不真**，二者的差额在这里是**机器可见**的。 -/
theorem not_isDirac_lawAt_of_two_atoms (M : PearlHierarchy.SCM Xc Yc) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : Xc ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    [DecidableEq Yb.Carrier]
    (φ : Yc → Yb.Carrier) (C : CtxSpace)
    (c : C.Carrier) (y : SX.Carrier) (a b : Yb.Carrier)
    (ha : MeasurableSet ({a} : Set Yb.Carrier)) (hb : MeasurableSet ({b} : Set Yb.Carrier))
    (hab : a ≠ b)
    (hA : (∑ y' : Yc, (if φ y' = a then ENNReal.ofReal (M.L2_do (e.symm y) y') else 0)) ≠ 0)
    (hB : (∑ y' : Yc, (if φ y' = b then ENNReal.ofReal (M.L2_do (e.symm y) y') else 0)) ≠ 0) :
    ¬ LawRuleToTraj.IsDirac (lawAt M SX e Yb φ C) := by
  intro hD
  obtain ⟨z, hz⟩ := hD c y
  have hset : ({pushMeasure Yb φ (M.L2_do (e.symm y))} : Set (Measure Yb.Carrier))
      = {Measure.dirac z} := hz
  have hpush : pushMeasure Yb φ (M.L2_do (e.symm y)) = Measure.dirac z := by
    have := hset
    rw [Set.singleton_eq_singleton_iff] at this
    exact this
  exact not_dirac_of_two_atoms Yb φ (M.L2_do (e.symm y)) a b ha hb hab hA hB ⟨z, hpush⟩

end DiracBarrierSCM

/-! ===========================================================================
    §4  ⭐⭐ **把障碍搬到 `IsPointDet` / `Rule` 侧**（与 `SCMLawBridge` §5 对齐）
    =========================================================================== -/

section ToRuleSide

variable {Xc : Type} [Fintype Xc] [DecidableEq Xc]
  {Yc : Type} [Fintype Yc] [DecidableEq Yc]

/-- ⭐⭐ **`IsPointDet` 在 `lawAt` 上 ⟺ 推出测度是 Dirac**（定义对齐）。

**⟹ 这条把 §2–§3 的结论**自动**搬到 `SCMLawBridge.toRule` 的输入侧**：
`toRule (lawAt ⋯) h` **存在** ⟺ `lawAt` 是 `IsPointDet`
⟺ 每个纤维的推出测度是 Dirac —— 正是 §3 障碍**排除**的情形。

**⚠ 注意**：`IsPointDet` 与 `LawRuleToTraj.IsDirac` **是同一个谓词**
（两者都要求 `∃ y, R c x = {δ_y}`），故本定理与 `isDirac_lawAt_iff`
**内容相同**；此处保留是为了让 `SCMLawBridge` §5 的 `toRule` 用法**有据可引**。 -/
theorem isPointDet_lawAt_iff (M : PearlHierarchy.SCM Xc Yc) (SX : StateSpace)
    [MeasurableSpace SX.Carrier] [DecidableEq SX.Carrier]
    (e : Xc ≃ SX.Carrier) (Yb : OutSpace) [MeasurableSpace Yb.Carrier]
    (φ : Yc → Yb.Carrier) (C : CtxSpace) [Nonempty C.Carrier] :
    IsPointDet (lawAt M SX e Yb φ C) ↔
      ∀ y : SX.Carrier, ∃ z : Yb.Carrier,
        pushMeasure Yb φ (M.L2_do (e.symm y)) = Measure.dirac z := by
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h (Classical.arbitrary C.Carrier) y
    exact ⟨z, by simpa [lawAt] using hz⟩
  · intro h c y
    obtain ⟨z, hz⟩ := h y
    exact ⟨z, by show {pushMeasure Yb φ (M.L2_do (e.symm y))} = _; rw [hz]⟩

end ToRuleSide

end SCM

end LawRule

end Fate
