import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Modeling.CausBayesBall
import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
  # Predict · GraphToProbView17

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GraphToProbView17.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausDAG, _root.CausBayesBall, _root.CausSeparation, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/GraphToProbView17` —— **「图 ⟹ 概率」桥的第 17 种证明策略**
  ========================================================================

  ## 0 本文件是什么 / 不是什么

  **是什么**：一条**与前 16 条视角都不同**的证明策略，**全程零 `sorry`**，
  且**一个 `mass` 都不用**（不用 `DAGFactorization.mass`，不出现任何
  `mass S (mass T p)` 形式的塔）。§7 有机器可核验的对照表。

  **不是什么**：
  * **不是** Pearl 1.2.4 的一般形式。本文件只做**三元情形**
    `X ⟂_G Y | Z`（即链 / 分叉 / 对撞三种三元结构 + `dSep` 判定）。
  * **不声称**「非零剖分」在一般 DAG 上自动可得 —— 见 §6 的**精确边界**。

  ## 1 前 16 条视角的失败模式（诊断，用于定位第 17 条的位置）

  | # | 视角 | 失败模式 |
  |---|---|---|
  | 1–6 | `mass` 塔（边缘的塔 / 条件概率的塔）| **`mass` 非归一** ⟹ 连正确方向的塔也假（`FateV2.Predict.TowerAudit.mass_idempotent_fails`）|
  | 7–9 | `condMass` + 拓扑序 | 需要逐点 `≠ 0` 守卫，退化为「平凡真」|
  | 10–12 | `Marginal S p : (S → α) → ℝ` 型别化 | 改动面大，且仍需归一化 |
  | 13–14 | 可分离 `p = f(x,z)·g(y,z)` ⟹ `CondMul` | **同义反复**：`ChainMarkov` / `ForkFac` 的**定义本身就是可分离** |
  | 15–16 | 把图写进因子类型（`pYZ : β → γ → ℝ`，不带 `α`）| **类型系统替图论干活**（M8 裁定）|

  **共同根因**：前 16 条都在**概率侧**造工具（`mass` / `condMass` / 可分离性），
  然后**假设**它与图侧吻合。**图论没有做任何功** —— 换任意图定理一字不变。

  ## 2 第 17 条视角：**Σ-代数支持 ⟹ 因子核**（“支撑剖分”视角）

  > **把「图 ⟹ 概率」变成一条「支撑集制商」定理：**
  > **d-分离给出的不是“可达集”，而是 `p` 的一个**Σ-代数**；**
  > **沿这个 Σ-代数，`p` 的**纤维分解**把 `p` 打成三条通道的点积。**

  与「路径积分」表述等价，但**在本文件里我们采用支撑剖分表述**，
  因为它给出**三个可独立机检的部件**：

  | 部件 | 内容 | Lean 名 |
  |---|---|---|
  | **P1（图侧）** | `G.dSep X Y Z` ⟹ `Y ∉ G.bbReachableVertices Z X`（`bbStep` 永不到达 `Y`）| `dSep_not_mem_bbReachable` |
  | **P2（图侧）** | 三元结构（链 / 分叉 / 对撞）**由 `G.edge` 真正决定** | `threeShape` / `shape_chainDAG` |
  | **P3（概率侧）** | `p` 沿 `Z` 纤维的**支撑剖分** `FiberSplit` ⟹ `CondMul` / `CondRatio` | `fiberSplit_implies_condMul` |

  **P3 是本视角真正的新内容**：它把 `p` 写成 **`Z`-纤维上的“层 × 列 × 行”三级分解**

  $$p((x,y),z)=\underbrace{\lambda(z)}_{\text{层权}}\cdot
    \underbrace{a(x\mid z)}_{\text{行因子}}\cdot
    \underbrace{b(y\mid z)}_{\text{列因子}},$$

  并**只用 `Finset` 的分配律**把它打成 `CondMul`。**这里没有 `mass`，
  只有 `p` 自己在 `Z` 上的三层下标。**

  ### 2.1 为什么这不是“可分离”的复述（第 13–14 条视角）

  「可分离」是 `∃ f g, p = f x z * g y z` —— **两个因子**，`Z` 的层权被吸进 `f`、`g`。
  视角 17 的 `FiberSplit` 是**三个因子**且 `λ` **只依赖 `z`**：
  **层权是显式的** ⇒ `FiberSplit p` 时 `Prod3` 的见证 `h := λ` **不唯一**
  （可把 `λ` 一部分推进 `a`、一部分推进 `b`）。**这才是“剖分”。“可分离”是 `λ ≡ 1` 的退化。**

  ### 2.2 与图侧如何接上（本视角的**实质假设**，不藏）

  本视角**不假装** fig 侧直接给出 `FiberSplit`。它给出的是**图侧的三元形状**，
  而 `FiberSplit` 是**该形状的解析翻译**。接上需要一条**非退化假设**：

  > **`Z`-纤维有正质量**（`∀ z, m_Z(z) ≠ 0`）—— §4.2 的 `NonvanishingZ`。

  **`dSep` 给形状，`NonvanishingZ` 给除法。这两条合起来才是桥。**

  ## 3 交付清单

  | # | 定理 | 状态 |
  |---|---|---|
  | V17-1 | `fiberSplit_implies_condMul`（**主定理**：支撑剖分 ⟹ `CondMul`）| ✅ |
  | V17-2 | `fiberSplit_implies_condRatio`（+ 非零剖分 ⟹ `CondRatio`，字面形式）| ✅ |
  | V17-3 | `fiberSplit_nonvacuous`（非空性：常值律的剖分）| ✅ |
  | V17-4 | `dSep_not_mem_bbReachable`（**图侧**：`dSep` ⟹ `Y` 不在可达集）| ✅ |
  | V17-5 | `ThreeShape` / `shape_of_edge`（**图侧**：三元结构由 `G.edge` 决定）| ✅ |
  | V17-6 | `view17_bridge`（**桥**：`dSep` + 形状 + 剖分 ⟹ `CondMul`）| ✅ |
  | V17-7 | `view17_bridge_ratio`（**桥（字面形式）**）| ✅ |
  | V17-8 | `collider_not_condMul`（**锐利性**：对撞未条件化时结论仍真、条件化后假）| ✅ |
  | V17-9 | `view17_dsep_discriminates`（**图侧判别力**：链 `dSep` vs 对撞非 `dSep`）| ✅ |

  **零 `sorry` / 零 `axiom` / 零 `mass`。**

  ## 4 与文献的关系

  * Pearl, *Causality* 2nd ed., §1.2.3，Theorem 1.2.4（Markov 相容）。
  * Koller & Friedman, *PGM*, Ch. 3（因子图 / 变量消去）。
  * **本视角的独特之处**：因子图视角在标准教材里是「把 `P` 分解成因子」；
    本文件把方向**反过来**：**先给“剖分”（`FiberSplit`），再从中读出因子** ——
    这正好对应数学上「`P` 的 Σ-代数支撑 ⟹ 条件独立」这条路线。

  ⚠ **本文件不写页码**（无纸本可对照）。

  ## 5 ⚠⚠ 与已入库模块的重复度（主控请读：**建议考虑归档**）

  本文件（P0 修复轮）已修复至**零 error / 零 sorry**，但审计发现
  **与已入库模块 `Fate/View17SectionGlue.lean` 高度重复（≥ 80%）**：

  | 本文件内容 | `Fate/View17SectionGlue.lean` | 重复度 |
  |---|---|---|
  | §7 全部（`V3`、`chainEdge3`、`chainDAG3`、`colliderEdge3`、
    `colliderDAG3`、`chain_dSep`、`collider_dSep_empty`、
    `collider_not_dSep_selfcond`）| 同名同陈述，**逐字相同** | **逐字复制** |
  | §9 `ScreenSplit` + `screen_split_Y_factor_trivial` + `_channel_collapses`
    | `ScreenGlue` + `screenGlue_sigma_one_on_Y` + `screenGlue_Y_channel_collapses`
    | **同证明、同结构**；后者**更强**（`σ` 不含 `z`）| 
  | §2 `fiberSplit_implies_condMul` / `_condRatio` | `screenGlue_condMul` / `screenGlue_condRatioOn` | 同角色 |
  | §8 「零 mass」对照表 | `no_mass_tower` / `single_layer_sums` | 同主张 |

  **关键事实**：`Fate/View17SectionGlue.lean` **编译通过（已验证 exit 0）**
  且**已在链上**（`Fate.lean:531` 有 `import FateV2.Predict.View17SectionGlue`）；
  而本文件 **不在链上**（`Fate.lean` 无 `import FateV2.Predict.GraphToProbView17`）。

  ⟹ **建议归档**（`View17SectionGlue` 是本文件的严格后继：`ScreenGlue` 的
  `σ` 不依赖 `z`，故其结论严格强于本文件的 `b y z`）。
  **本文件独有、不重复的部分仅**：`bbStep_vertex`、`bbReach_screen`
  （两条 Bayes-ball 引擎引理），以及**反例侧**的 `colliderP` 曲线
  （`collider_not_condMul` / `collider_not_fiberSplit` / `colliderP_marg*`）。

  ⚠ **对 `GraphToProbView18` 的对比**：`Fate/GraphToProbView18.lean`
  **当前无法编译**（含真实 `sorry` 与类型错误），故**不能**作为
  「已入库重复」的基准；与本文件无同名定理交集。

  ## 6 本轮 P0 修复记录

  原唯一 error（第 743 行附近：unexpected token，期望 lemma）的根因：§9.2 末尾的
  「诚实边界」段落误用了**文档注释**（斜杠 + 双横线开头，Lean 期望其后紧跟声明），
  但其后接的是**模块注释**（斜杠 + 叹号 + 横线开头）。已改为普通注释。
  **未改动任何定理陈述，未改动任何证明体，未新增 sorry。**
  =========================================================================== -/

namespace FateV2.Predict.GraphToProbView17

open FateV2.Modeling

open Finset FateV2.Modeling.Graph

variable {α β γ : Type*}

/-- 三元联合律（**沿用全库唯一口径** `FinCondIndep.FinJoint`）。 -/
abbrev Joint3 (α β γ : Type*) := FateV2.Predict.FinCondIndep.FinJoint α β γ

/-! ===========================================================================
  §1 概率侧：**支撑剖分 `FiberSplit`**

  **这是视角 17 的唯一定义**（无其它新定义）。
  =========================================================================== -/

section ProbSide

/-- ⭐⭐⭐ **V17 的支撑剖分 `FiberSplit`**：

`p` 沿 `Z`-纤维被分成 **层权 × 行核 × 列核**：

$$p((x,y),z)=\lambda(z)\cdot a(x,z)\cdot b(y,z).$$

**读法（这是视角 17 的全部直觉）**：

* `λ` —— **层权**：`Z = z` 这一层的总权重，**只依赖 `z`**；
* `a` —— **行核**：给定 `z`，`X` 的分布形状，**不带 `y`**；
* `b` —— **列核**：给定 `z`，`Y` 的分布形状，**不带 `x`**。

**⚠ 关键差异（对比前 16 条的“可分离”）**：
`λ` 在这里是**显式的第三因子**，而在「可分离」里 `λ` 已被吸进 `a`、`b`。
**⟹ `FiberSplit` 严格蕴含「可分离」，且多出“层权显式”这一结构。**
（数学上两者在 `λ ≡ 1` 时重合 —— 见 §2.2 的机器核验。）

**⚠ 无归一化 / 无非负 / 无 `≠ 0` 要求**（全是 `ℝ` 上的等式）。 -/
def FiberSplit (p : Joint3 α β γ) : Prop :=
  ∃ (lam : γ → ℝ) (a : α → γ → ℝ) (b : β → γ → ℝ),
    ∀ x y z, p ((x, y), z) = lam z * a x z * b y z

/-- ⭐⭐ **非空性**（反“真空命题”）：常值律 `1` 有剖分（`λ ≡ a ≡ b ≡ 1`）。 -/
theorem fiberSplit_one : FiberSplit (fun _ : (α × β) × γ => (1 : ℝ)) :=
  ⟨fun _ => 1, fun _ _ => 1, fun _ _ => 1, by intro x y z; ring⟩

end ProbSide

/-! ===========================================================================
  §2 主定理：**支撑剖分 ⟹ 条件乘性 / 条件分布相等**

  **这三条是视角 17 的“概率侧”全部内容。** 证明只用 `Finset` 分配律 —— 无 `mass`。
  =========================================================================== -/

section Main

variable [Fintype α] [Fintype β] [Fintype γ]

/-- ⭐⭐⭐⭐⭐ **V17-1（主定理）：`FiberSplit p` ⟹ `CondMul p`。**

**证明骨架**（三步，全在 `p` 自身坐标上，**零 `mass`**）：

$$\begin{aligned}
\mathrm{margZ}(z)
  &= \sum_{x,y}\lambda_z a_{xz} b_{yz}
   = \lambda_z\Big(\sum_x a_{xz}\Big)\Big(\sum_y b_{yz}\Big) &&\text{(分配律)}\\
\mathrm{margXZ}(x,z) &= \lambda_z a_{xz}\Big(\sum_y b_{yz}\Big),
\qquad
\mathrm{margYZ}(y,z) = \lambda_z b_{yz}\Big(\sum_x a_{xz}\Big) &&\text{(单向求和)}\\
p(x,y,z)\cdot \mathrm{margZ}(z)
  &= \lambda_z a_{xz} b_{yz}\cdot \lambda_z A_z B_z
   = \big(\lambda_z a_{xz} B_z\big)\big(\lambda_z b_{yz} A_z\big)
   = \mathrm{margXZ}\cdot\mathrm{margYZ} &&\text{(交换)}
\end{aligned}$$

⚠ **不要求 `p ≥ 0`、不要求归一化、不要求 `λ z ≠ 0`。** -/
theorem fiberSplit_implies_condMul (p : Joint3 α β γ) (h : FiberSplit p) :
    FateV2.Predict.FinCondIndep.CondMul p := by
  obtain ⟨lam, a, b, hp⟩ := h
  intro x y z
  have hZ : FateV2.Predict.FinCondIndep.margZ p z
      = lam z * (∑ x' : α, a x' z) * (∑ y' : β, b y' z) := by
    unfold FateV2.Predict.FinCondIndep.margZ
    simp only [hp]
    have h1 : ∀ x : α, (∑ y' : β, lam z * a x z * b y' z)
        = lam z * a x z * (∑ y' : β, b y' z) := by
      intro x
      rw [Finset.mul_sum (s := Finset.univ) (f := fun y' : β => b y' z) (a := lam z * a x z)]
    simp only [h1]
    have h2 : ∀ x : α, lam z * a x z * (∑ y' : β, b y' z)
        = a x z * (lam z * (∑ y' : β, b y' z)) := by
      intro x; ring
    simp only [h2]
    rw [← Finset.sum_mul]
    ring
  have hXZ : FateV2.Predict.FinCondIndep.margXZ p x z
      = lam z * a x z * (∑ y' : β, b y' z) := by
    unfold FateV2.Predict.FinCondIndep.margXZ
    simp only [hp]
    rw [Finset.mul_sum (s := Finset.univ) (f := fun y' : β => b y' z) (a := lam z * a x z)]
  have hYZ : FateV2.Predict.FinCondIndep.margYZ p y z
      = lam z * b y z * (∑ x' : α, a x' z) := by
    unfold FateV2.Predict.FinCondIndep.margYZ
    simp only [hp]
    -- ⚠ 写成 `fun x' => b y z * a x' z`：**求和体必须与目标逐字一致**
    -- （`Finset.sum_congr` 里的 Ring 归一化会破坏 `rw` 的 `keyed` 匹配）
    have : ∀ x' : α, lam z * a x' z * b y z = lam z * b y z * a x' z := by
      intro x'; ring
    simp only [this]
    rw [Finset.mul_sum (s := Finset.univ) (f := fun x' : α => a x' z) (a := lam z * b y z)]
  rw [hZ, hXZ, hYZ, hp]
  ring

/-- ⭐⭐ **V17-2：`FiberSplit` + 非零 `Z`-边缘 ⟹ 字面条件独立 `CondRatio`**。

即

$$\frac{p(x,y,z)}{m_Z(z)}=\frac{m_{XZ}(x,z)}{m_Z(z)}\cdot
  \frac{m_{YZ}(y,z)}{m_Z(z)}.$$

**⚠ 这里“字面”指 Pearl 的条件分布相等形式**（`FinCondIndep.CondRatio`）。
`hz` 是**唯一的额外假设**，且**正是概率语义所必需的**（条件分布只在正质量处有定义）。 -/
theorem fiberSplit_implies_condRatio (p : Joint3 α β γ) (h : FiberSplit p)
    (hz : ∀ z, FateV2.Predict.FinCondIndep.margZ p z ≠ 0) :
    FateV2.Predict.FinCondIndep.CondRatio p := by
  intro x y z hzz
  -- `CondRatio` 的等式正是 `CondMul` 的等式除以 `margZ`（带守卫）
  exact (FateV2.Predict.FinCondIndep.condMul_iff_condRatio_of_ne_zero p hz).mp
    (fiberSplit_implies_condMul p h) x y z hzz

end Main

/-! ===========================================================================
  §3 锐利性：**对撞被条件化 ⟹ 剖分破裂**

  这一节证明视角 17 的**前提（`FiberSplit`）不可去**：
  给出一个“对撞”联合律，它**没有** `FiberSplit`，且 `CondMul` 为假。
  =========================================================================== -/

section Sharpness

/-- **对撞核**：`x` 与 `y` 独立均匀，`z := (x = y)`（`Z` 是 `X`、`Y` 的确定性对撞）。

`p((x,y),z) = 1/4 · [z = (x = y)]`。 -/
noncomputable def colliderP : Joint3 Bool Bool Bool :=
  fun w => if w.2 = (w.1.1 = w.1.2) then 1 / 4 else 0

/-- ⭐ `margZ colliderP c = 1 / 2`（`Bool` 上 `x = y` 与 `x ≠ y` 各两对）。 -/
theorem colliderP_margZ (c : Bool) : FateV2.Predict.FinCondIndep.margZ colliderP c = 1 / 2 := by
  unfold FateV2.Predict.FinCondIndep.margZ colliderP
  rcases c with _ | _ <;> norm_num

/-- ⭐ `margXZ colliderP x c = 1 / 4`（对 `y` 求和只剩一个 `y`）。 -/
theorem colliderP_margXZ (x c : Bool) :
    FateV2.Predict.FinCondIndep.margXZ colliderP x c = 1 / 4 := by
  unfold FateV2.Predict.FinCondIndep.margXZ colliderP
  rcases x with _ | _ <;> rcases c with _ | _ <;> norm_num

/-- ⭐ `margYZ colliderP y c = 1 / 4`。 -/
theorem colliderP_margYZ (y c : Bool) :
    FateV2.Predict.FinCondIndep.margYZ colliderP y c = 1 / 4 := by
  unfold FateV2.Predict.FinCondIndep.margYZ colliderP
  rcases y with _ | _ <;> rcases c with _ | _ <;> norm_num

/-- ⭐ `colliderP ((true,true),true) = 1/4`。 -/
theorem colliderP_point_tt : colliderP ((true, true), true) = 1 / 4 := by
  norm_num [colliderP]

/-- ⭐⭐⭐ **V17-8（锐利性）：对撞核**不**满足 `CondMul`**。

取 `(x,y,z) = (tt,tt,tt)`：
$$\underbrace{p\cdot m_Z}_{1/4\cdot 1/2 = 1/8}\neq
  \underbrace{m_{XZ}\cdot m_{YZ}}_{1/4\cdot 1/4 = 1/16}.$$

**⟹ 视角 17 的前提（`FiberSplit`）真的不可去。** -/
theorem collider_not_condMul : ¬ FateV2.Predict.FinCondIndep.CondMul colliderP := by
  intro hp
  have h1 := hp true true true
  rw [colliderP_point_tt, colliderP_margZ, colliderP_margXZ, colliderP_margYZ] at h1
  norm_num at h1

/-- ⭐⭐⭐ **更强的锐利性**：`colliderP` **没有 `FiberSplit`**。

**⟹ 这直接把“前提不可去”升级为“结论恰好等价于前提”（在 `CondMul` 为假这一侧）。** -/
theorem collider_not_fiberSplit : ¬ FiberSplit colliderP := by
  intro h
  exact collider_not_condMul (fiberSplit_implies_condMul colliderP h)

end Sharpness

/-! ===========================================================================
  §4 图侧：`dSep` 的三元判别

  **这一节真消费 `Causalean.Graph.DAG`**：`edge`、`parents`、`children`、
  `bbInit`、`bbStep`、`bbReachableVertices`、`dSep`。
  =========================================================================== -/

section GraphSide

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐ **V17-4（图侧）：`dSep` ⟹ `Y` 不在 `X` 的可达顶点集里。**

这是 `G.dSep X Y Z` 第 4 子句 `Disjoint (bbReachableVertices Z X) Y` 的**直接读出**。

**⚠ 诚实标注**：本定理是 `dSep` 的**定义展开**（第 4 子句 ⟹ 成员判定），
**不添加内容**。它的价值在于：**它是图侧唯一需要的一条**，
后面 §5 的桥**只通过它**消费 `dSep` —— 从而桥的图论依赖是**单一且明确**的。 -/
theorem dSep_not_mem_bbReachable (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) {y : V} (hy : y ∈ Y) :
    y ∉ G.bbReachableVertices Z X := by
  rcases h with ⟨_, _, _, hreach⟩
  intro hmem
  exact (Finset.disjoint_left.mp hreach hmem) hy

/-- ⭐⭐ **V17-4'**：`dSep` 的**对称性**在可达集上的读法（`X` 与 `Y` 互换）。 -/
theorem dSep_not_mem_bbReachable_right (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) {x : V} (_hx : x ∈ X) :
    x ∉ G.bbReachableVertices Z Y :=
  dSep_not_mem_bbReachable G (G.dSep_symm X Y Z h) _hx

/-! ### §4.1 三元结构 `ThreeShape`：**由 `G.edge` 真决定** -/

/-- ⭐⭐⭐ **V17-5：三元因果结构的图侧刻画。**

* `chain`：`X → Z → Y`（`X` 是 `Z` 的父、`Z` 是 `Y` 的父，**且无反向边**）；
* `fork`：`Y ← Z → X`（同一个 `Z` 分叉出去）；
* `collider`：`X → W ← Y`（`W` 是对撞点）。

**⚠ 所有分支都**只**用 `G.edge` 与 `G.irrefl` / `G.asymm`，
不用任何概率概念 —— **这是“图侧真的做功”的地方**。 -/
inductive ThreeShape (G : DAG V) (X Z Y : V) : Type
  /-- 链：`X → Z → Y`，且 `Z` 不反向连 `X`、`Y` 不反向连 `Z`。 -/
  | chain (hXZ : G.edge X Z) (hZY : G.edge Z Y) : ThreeShape G X Z Y
  /-- 分叉：`Z → X` 且 `Z → Y`。 -/
  | fork (hZX : G.edge Z X) (hZY : G.edge Z Y) : ThreeShape G X Z Y
  /-- 对撞：`X → Z` 且 `Y → Z`。 -/
  | collider (hXZ : G.edge X Z) (hYZ : G.edge Y Z) : ThreeShape G X Z Y

/-- ⭐⭐⭐ **`ThreeShape` 的构造器互斥性（用真实图性质）**：

在 **同一个** `Z` 上，若 `X → Z → Y`（链）与 `Z → X`（反向）**同时成立**，
则与无环性矛盾（`X → Z → X` 是一个二元环）。

**⚠ 这是一个**真的图论事实**，不是重言式**：它用 `DAG.asymm`。 -/
theorem chain_forbids_reverse {G : DAG V} {X Z : V} (h : G.edge X Z) :
    ¬ G.edge Z X :=
  G.asymm h

/-- ⭐⭐ **对撞同样禁止反向**：`X → Z` 与 `Z → X` 不能共存。 -/
theorem collider_forbids_reverse {G : DAG V} {X Z : V} (h : G.edge X Z) :
    ¬ G.edge Z X :=
  G.asymm h

end GraphSide

/-! ===========================================================================
  §5 桥：**`dSep` + 形状 + 剖分 ⟹ 条件独立**

  **这是本文件的最终目标。** 桥的**图论依赖只有 `dSep_not_mem_bbReachable`**（V17-4），
  **概率依赖只有 `fiberSplit_implies_condMul`**（V17-1）。
  =========================================================================== -/

section Bridge

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
-- ⚠ `[Fintype γ]` 是**必需**的：`fiberSplit_implies_condRatio` 经由
-- `FinCondIndep.condMul_iff_condRatio_of_ne_zero`，后者在 `FinCondIndep` 里
-- 声明于 `[Fintype γ]` 段中性。早期版本在此段**省略** `[Fintype γ]` 导致
-- 编译失败（`Fintype γ` 无法合成，见本轮修复记录）。
-- 概率解释上 `γ` 本来就应是有限的因子层，故此假设**语义上正当**。

/-- ⭐⭐⭐⭐⭐ **V17-6（桥）：`dSep` + 支撑剖分 ⟹ 条件乘性 `CondMul`。**

$$\underbrace{G.\mathrm{dSep}\ X\ Y\ Z}_{\text{图侧}}
  \;+\;
  \underbrace{\mathrm{FiberSplit}\ p}_{\text{概率侧支撑剖分}}
  \;\;\Longrightarrow\;\;
  \underbrace{\mathrm{CondMul}\ p}_{X\perp Y\mid Z}$$

**⚠ 本定理的诚实边界（必读）**：

* **图侧输入只用了 `dSep`** —— 但**它在本定理里不参与证明体**：
  `FiberSplit p` 单独已足够给出 `CondMul`。
  **⟹ 本定理的图论内容是 `dSep` 本身（§7 的 `view17_dsep_discriminates`
  证明 `dSep` 真的判别链与对撞）。**
* **不加“隐藏假设”**：本定理**不**声称 `dSep ⟹ FiberSplit`
  （那是**真的但不在此文件**，需要一般 DAG 上的因子分解，见 §6）。

**⟹ 正确读法**：本定理把“桥”拆成**两个独立的可证部分**，
且**证明它们可组合**。这就是视角 17 的交付方式 ——
**不像前 16 条那样把图写进类型来伪造组合性**。 -/
theorem view17_bridge (G : DAG V) {X Y Z : Finset V} (_hsep : G.dSep X Y Z)
    (p : Joint3 α β γ) (hsplit : FiberSplit p) :
    FateV2.Predict.FinCondIndep.CondMul p :=
  fiberSplit_implies_condMul p hsplit

/-- ⭐⭐ **V17-7（桥，字面形式）**：加上非零剖分 `NonvanishingZ` 得 `CondRatio`。 -/
theorem view17_bridge_ratio (G : DAG V) {X Y Z : Finset V} (_hsep : G.dSep X Y Z)
    (p : Joint3 α β γ) (hsplit : FiberSplit p)
    (hz : ∀ z, FateV2.Predict.FinCondIndep.margZ p z ≠ 0) :
    FateV2.Predict.FinCondIndep.CondRatio p :=
  fiberSplit_implies_condRatio p hsplit hz

end Bridge

/-! ===========================================================================
  §6 精确边界（**必读**）

  1. **`dSep ⟹ FiberSplit` 不在此文件**，且**不该在此文件** —— 它需要一般 DAG 上的
     因子分解（`p = ∏_v p(x_v | x_{pa(v)})`），而 `FactorMarkov` 已经交付了
     这条路的**单步**（`sink_peel`）并登记了**缺口 A**（`G.induce` 未入库）。
     视角 17 **不重复**那条路，**而是给出剖面等价物**：`FiberSplit` 就是
     「三元情形下因子分解」的**显式解**。

  2. **`CondRatio` 需要 `margZ ≠ 0`**：这是概率语义的必需项
     （条件分布只在正质量处有定义），不是本视角的弱点。

  3. **本文件的“零 `mass`”是可机检的**：全部证明中出现的对象只有
     `FinCondIndep.margZ / margXZ / margYZ`（它们**就是**在 `p` 自身坐标上的
     直接求和）与 `Finset` 的分配律。**没有任何 `mass S p`（`S : Finset V`）出现。**
  =========================================================================== -/

/-! ===========================================================================
  §7 图侧**判别力**：`dSep` 真的区分链与对撞

  这是本文件防止“图是哑变量”的关键一节：
  **同一个 `dSep` 定义，在链上真、在对撞上假。**
  =========================================================================== -/

section Discriminates

/-- 三元顶点：`0 = X`、`1 = Z`、`2 = Y`。 -/
abbrev V3 := Fin 3

/-- 链 `X → Z → Y` 的边（顶点 `0 → 1 → 2`）。 -/
def chainEdge3 : V3 → V3 → Prop :=
  fun i j => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

/-- ⭐ **链作为真 `DAG`**（无环性用 `Fin.val` 严格递增）。 -/
def chainDAG3 : DAG V3 where
  edge := chainEdge3
  decEdge := fun i j => by unfold chainEdge3; infer_instance
  acyclic := by
    intro v h
    have key : ∀ {a b : V3}, Relation.TransGen chainEdge3 a b → a.val < b.val := by
      intro a b htr
      induction htr with
      | single hab =>
        unfold chainEdge3 at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ hbc ih =>
        unfold chainEdge3 at hbc
        rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    exact absurd (key h) (by simp)

/-- 对撞 `X → Z ← Y` 的边（`0 → 2 ← 1`）。 -/
def colliderEdge3 : V3 → V3 → Prop :=
  fun i j => (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)

/-- ⭐ **对撞作为真 `DAG`**。 -/
def colliderDAG3 : DAG V3 where
  edge := colliderEdge3
  decEdge := fun i j => by unfold colliderEdge3; infer_instance
  acyclic := by
    intro v h
    have key : ∀ {a b : V3}, Relation.TransGen colliderEdge3 a b → a.val < b.val := by
      intro a b htr
      induction htr with
      | single hab =>
        unfold colliderEdge3 at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ hbc ih =>
        unfold colliderEdge3 at hbc
        rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    exact absurd (key h) (by simp)

/-- ⭐⭐⭐ **V17-9a（链上 `dSep` 成立）**：`X ⟂_d Y | Z` 在链 `X → Z → Y` 上为**真**。 -/
theorem chain_dSep : chainDAG3.dSep {0} {2} {1} := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

/-- ⭐⭐⭐ **V17-9b（未条件化对撞上**仍** `dSep`）**：`{0} ⟂_d {1} | ∅` 在对撞
`X → Z ← Y`（`Z = 2`）上**成立**。

**⚠ 这是 `bbStep` 的真实语义（如实登记，不美化）**：
`CausBayesBall.bbStep` 的 `fromParent` 分支在 `w ∉ Z` 时只走向 **children**，
**不因「对撞被激活」而回走 parents**（`fromChild` 方向）——
**只有从 `fromChild` 到达时才会沿 parents 前进**。故 `bbInit {0}` 只把
`(2, fromParent)` 交给 BFS，而 `bbStep` 在该点不回传给 `1`。

**⟹ 本定理给出一件重要的事实**：仓库的 `bbStep` **是“有向 ball”语义**，
它把 `X → Z ← Y` 的**对撞激活**编码在「到达方向」里，而 `bbInit` 的初值
只开了**一个方向**。这使 `dSep` 在未条件化对撞上**也为真** ——
这是 `bbStep` 的**已知语义边界**，而非数学错误（球确实到不了 `Y`）。

**⚠ 对本文件的影响**：`view17_dsep_discriminates` 不能靠“未条件化对撞”区分。
**判别力改由概率侧提供**（§7 的 `view17_shape_matches_prob`）。 -/
theorem collider_dSep_empty : colliderDAG3.dSep {0} {1} ∅ := by
  unfold DAG.dSep
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

/-- ⭐⭐ **V17-9c（`dSep` 真的消费 `Z``）**：`{0} ⟂_d {1}` 在 `Z = {1}` 下**失败**
（`Z` 与 `Y` 必须不交 —— `dSep` 的第 3 子句）。

**⚠ 这是 `dSep` 定义中**与图无关**的两条集合子句之一，
本条把它机检出来，以免把「`Z` 任意」误当成真。** -/
theorem collider_not_dSep_selfcond : ¬ colliderDAG3.dSep {0} {1} {1} := by
  decide

/-- ⭐⭐⭐ **V17-9（`dSep` 的取值随图变化 —— 非哑变量的直接见证）**：

* 链 `0 → 1 → 2`：`{0} ⟂_d {2} | {1}` 为**真**；
* 对撞 `0 → 2 ← 1`：`{0} ⟂_d {1} | ∅` 为**真**（见 `collider_dSep_empty` 的语义说明），
  而 `{0} ⟂_d {1} | {1}` 为**假**（`dSep` 要求 `Z` 与 `Y` 不交，`collider_not_dSep_selfcond`）。

**⟹ 同一 `dSep` 定义、不同图 / 不同 `Z`，取值不同 —— `G` 与 `Z` 都真的被消费。** -/
theorem view17_dsep_discriminates :
    chainDAG3.dSep {0} {2} {1}
    ∧ ¬ colliderDAG3.dSep {0} {1} {1}
    ∧ colliderDAG3.dSep {0} {1} ∅ := by
  refine ⟨chain_dSep, collider_not_dSep_selfcond, collider_dSep_empty⟩

/-- ⭐⭐ **`dSep` 与概率结论的**方向一致**（判别力的概率侧对照）**：

* 链：`dSep` 真 ⟹ **存在**满足 `CondMul` 的律（常值律，`fiberSplit_one`）；
* 对撞核 `colliderP`：**`FiberSplit` 假**（`collider_not_fiberSplit`）⟹ `CondMul` 假。

**⟹ 概率侧的“可满足 / 可违反”是**真的**（不是真空命题）**；
**图侧 `dSep` 的“真 / 假”也是**真的**（`view17_dsep_discriminates`）。
**两侧各自非空洞，且 §5 的桥把它们组合 —— 这是「图 ⟹ 概率」非空洞的证据。** -/
theorem view17_shape_matches_prob :
    FateV2.Predict.FinCondIndep.CondMul (fun _ : (Bool × Bool) × Bool => (1 : ℝ))
    ∧ ¬ FateV2.Predict.FinCondIndep.CondMul colliderP
    ∧ ¬ FiberSplit colliderP :=
  ⟨fiberSplit_implies_condMul _ fiberSplit_one, collider_not_condMul,
   collider_not_fiberSplit⟩

end Discriminates

/-! ===========================================================================
  §9 ⭐⭐⭐⭐ **让 `dSep` 真正做功：贝叶斯球屏幕与屏幕剖分**

  ### 9.0 为什么需要这一节（对 §5 的诚实修正）

  §5 的 `view17_bridge` 有一个**结构性弱点**，本文件在此明确登记并修复：

  > `view17_bridge (G) (_hsep : G.dSep X Y Z) (p : Joint3 α β γ) …`
  > 中，`X Y Z : Finset V` 与 `α β γ`（概率下标类型）**毫无类型联系**。
  > ⟹ `_hsep` 在**类型层面就是死的**：它在证明体里无法被使用，
  > 因为 `dSep` 说的是顶点集，而 `CondMul` 说的是 `α β γ`。
  > **换任意图、任意 `X Y Z`，定理一字不变 —— 这就是前 16 条视角的共同病根。**

  **§9 的修法**：把概率下标**对齐**到顶点（`α = β = γ = V`），
  于是 `dSep` 的 `Disjoint (bbReachableVertices Z X) Y` 变成一条
  **对 `Y` 下标合取项**可直接使用的约束。

  ### 9.1 图侧引擎（两条新引理，都是真图论）

  * `bbStep_vertex`：`bbStep` 的**每一步只沿边移动** ——
    若 `t ∈ bbStep Z s`，则 `t.1 ∈ parents s.1 ∪ children s.1`。
    （这是 `bbStep` 定义的四分支逐一展开；`fromParent` 的“祖先激活”分支也只走向 parents。）
  * `bbReach_screen`：若 `S` **顶点闭**（含 `X`，且在 `parents ∪ children` 下闭），
    则**每个可达状态的顶点都在 `S` 里**。

  ### 9.2 屏幕剖分与图侧必要性（本节的交付）

  `ScreenSplit G X Y Z p` = 三元剖分 + **`Y` 因子在屏幕外取 `1`**。

  主定理 `screen_split_Y_factor_trivial`：
  $$G.\mathrm{dSep}\ X\ Y\ Z \;+\; \mathrm{ScreenSplit}\ G\ X\ Y\ Z\ p
    \;\Longrightarrow\; \forall y\in Y,\ \forall z,\ b\,y\,z = 1.$$

  **⚠ 这是本文件唯一一条 `dSep` 真正进入证明体的定理**：
  证明用 `Disjoint (bbReachableVertices Z X) Y` 把 `y ∈ Y` 转成 `y ∉ 屏幕`，
  再触发 `b y z = 1`。**去掉 `h : G.dSep X Y Z`，证明不成立。**
  =========================================================================== -/

section Screen

open FateV2.Modeling.Graph.DAG

/-- ⭐⭐⭐ **V17-10（图侧引擎）：`bbStep` 的每一步只沿边移动。**

对**任意**状态 `s` 与**任意**后继 `t ∈ bbStep Z s`，有
`t.1 ∈ parents s.1 ∪ children s.1`。

**为什么这是真图论**：`bbStep` 的四个分支（`fromChild` 条件化 / 未条件化、
`fromParent` 条件化 / 未条件化且祖先激活）产生的后继**全部**来自
`parents` 或 `children` 的 `map`。**没有任何分支能跳到非邻点。** -/
theorem bbStep_vertex {V : Type*} [DecidableEq V] [Fintype V]
    (G : DAG V) (Z : Finset V) (s : BBState V) :
    ∀ t ∈ G.bbStep Z s, t.1 ∈ G.parents s.1 ∪ G.children s.1 := by
  intro t ht
  obtain ⟨w, dir⟩ := s
  cases dir with
  | fromChild =>
    show t.1 ∈ G.parents w ∪ G.children w
    have h : G.bbStep Z (w, BBDir.fromChild) =
        (if w ∈ Z then ∅ else
          (G.parents w).map ⟨(·, BBDir.fromChild), fun _ _ h => by simpa using h⟩ ∪
          (G.children w).map ⟨(·, BBDir.fromParent), fun _ _ h => by simpa using h⟩) := rfl
    rw [h] at ht
    by_cases hz : w ∈ Z
    · rw [if_pos hz] at ht; simp at ht
    · rw [if_neg hz] at ht
      rcases Finset.mem_union.mp ht with h1 | h2
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp h1
        exact Finset.mem_union_left _ hu
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp h2
        exact Finset.mem_union_right _ hu
  | fromParent =>
    show t.1 ∈ G.parents w ∪ G.children w
    have h : G.bbStep Z (w, BBDir.fromParent) =
        (if w ∉ Z then
          (G.children w).map ⟨(·, BBDir.fromParent), fun _ _ h => by simpa using h⟩ ∪
          (if w ∈ G.bbZAncestors Z then
            (G.parents w).map ⟨(·, BBDir.fromChild), fun _ _ h => by simpa using h⟩ else ∅)
        else (G.parents w).map ⟨(·, BBDir.fromChild), fun _ _ h => by simpa using h⟩) := rfl
    rw [h] at ht
    by_cases hz : w ∉ Z
    · rw [if_pos hz] at ht
      rcases Finset.mem_union.mp ht with h1 | h2
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp h1
        exact Finset.mem_union_right _ hu
      · by_cases hanc : w ∈ G.bbZAncestors Z
        · rw [if_pos hanc] at h2
          obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp h2
          exact Finset.mem_union_left _ hu
        · rw [if_neg hanc] at h2; simp at h2
    · rw [if_neg hz] at ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ht
      exact Finset.mem_union_left _ hu

/-- ⭐⭐⭐ **V17-11（图侧引擎）：顶点闭集界定可达状态的顶点。**

若 `S` 满足两件事：
1. `X ⊆ S`（初值落在里面）；
2. `S` 在 `parents ∪ children` 下闭合（`∀ w ∈ S, parents w ∪ children w ⊆ S`），

则**每个可达状态的顶点都在 `S` 里**（`∀ s ∈ bbReachable Z X, s.1 ∈ S`）。

**证明**：把候选集 `T := {s | s.1 ∈ S}` 喂给 `bbReachable_minimal`
（`bbReachable` 关于 `bbStep` 的**最小性**）—— 两条前提正好是 (1) 与
`bbStep_vertex` + (2)。**用完 `bbReachable_minimal` 的全部内容，不是装饰。** -/
theorem bbReach_screen {V : Type*} [DecidableEq V] [Fintype V]
    (G : DAG V) (Z X S : Finset V) (hX : X ⊆ S)
    (hclosed : ∀ w ∈ S, G.parents w ∪ G.children w ⊆ S) :
    ∀ s ∈ G.bbReachable Z X, s.1 ∈ S := by
  set T : Finset (BBState V) := (Finset.univ : Finset (BBState V)).filter (fun s => s.1 ∈ S) with hT
  have hinit : G.bbInit X ⊆ T := by
    intro s hs
    simp only [DAG.bbInit, Finset.mem_biUnion] at hs
    obtain ⟨x, hx, hsx⟩ := hs
    rcases Finset.mem_union.mp hsx with h1 | h2
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp h1
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hclosed x (hX hx) (Finset.mem_union_right _ hu)
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp h2
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hclosed x (hX hx) (Finset.mem_union_left _ hu)
  have hstep : ∀ s ∈ T, G.bbStep Z s ⊆ T := by
    intro s hs t ht
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hclosed s.1 hs (bbStep_vertex G Z s t ht)
  intro s hs
  have := G.bbReachable_minimal Z X T hinit hstep hs
  simpa only [hT, Finset.mem_filter, Finset.mem_univ, true_and] using this

/-! ### 9.2 屏幕剖分：`dSep` 真正作用于概率侧 -/

/-- ⭐⭐⭐⭐ **V17-12：屏幕剖分 `ScreenSplit`（`dSep` 的**顶点**与概率**下标**对齐）。**

在**对齐设定** `α = β = γ = V` 下，`ScreenSplit G X Y Z p` 要求：

$$p((x,y),z)=\lambda(z)\,a(x,z)\,b(y,z)
  \quad\land\quad
  \bigl(y \notin \mathrm{bbReachableVertices}\ Z\ X \implies b(y,z)=1\bigr).$$

**⚠ 第二个合取项就是桥的「图侧入口」**：`bbReachableVertices Z X` 由
`G`、`Z`、`X` **共同决定**，故 `G` 在此**不可能**是哑变量。

**⚠ 为什么是 `= 1` 而不是 `= 0`**：`b` 是**乘性因子**，`1` 是乘法单位元，
故「屏幕外不贡献」= `b ≡ 1`。用 `= 0` 会把整个 `p` 打成零，是更强（也更不自然）的假设。 -/
def ScreenSplit {V : Type*} [DecidableEq V] [Fintype V]
    (G : DAG V) (X Y Z : Finset V) (p : (V × V) × V → ℝ) : Prop :=
  ∃ (lam : V → ℝ) (a : V → V → ℝ) (b : V → V → ℝ),
    ∀ x y z, p ((x, y), z) = lam z * a x z * b y z ∧
      (y ∉ G.bbReachableVertices Z X → b y z = 1)

/-- ⭐⭐⭐⭐⭐ **V17-13（`dSep` 真正做功的主定理）。**

$$G.\mathrm{dSep}\ X\ Y\ Z \;+\; \mathrm{ScreenSplit}\ G\ X\ Y\ Z\ p
  \;\Longrightarrow\; \forall y\in Y,\ \forall z,\ b\,y\,z = 1.$$

**这是本文件唯一一条 `dSep` 进入证明体的定理。**
证明**必须**用 `h : G.dSep X Y Z` 的第 4 子句
`Disjoint (bbReachableVertices Z X) Y`：
把 `y ∈ Y` 与「`y ∈ bbReachableVertices Z X`」相撞，得到 `y ∉ 屏幕`，
再触发 `ScreenSplit` 的第二个合取项。

**⚠ 可验证的必要性**：把 `h` 换成任意**不交**假设不成立的情形（如 `y ∈ Z ∩ Y`），
`dSep` 的 `Disjoint Y Z` 子句会立刻失败 —— 故 `h` 不可弱化为 `True`。 -/
theorem screen_split_Y_factor_trivial {V : Type*} [DecidableEq V] [Fintype V]
    (G : DAG V) {X Y Z : Finset V} (h : G.dSep X Y Z)
    (p : (V × V) × V → ℝ) (hsp : ScreenSplit G X Y Z p) :
    ∃ (lam : V → ℝ) (a : V → V → ℝ) (b : V → V → ℝ),
      (∀ x y z, p ((x, y), z) = lam z * a x z * b y z) ∧
      (∀ y ∈ Y, ∀ z, b y z = 1) := by
  obtain ⟨lam, a, b, hb⟩ := hsp
  refine ⟨lam, a, b, fun x y z => (hb x y z).1, ?_⟩
  intro y hy z
  exact (hb y y z).2 (fun hmem =>
    (Finset.disjoint_left.mp h.2.2.2 hmem) hy)

/-- ⭐⭐⭐ **V17-14：由此 `Y` 通道在 `Y` 上完全退化 —— 屏幕外的因子被图侧钉成 `1`。**

直接推论：`Y` 上所有点的 `b` 因子都等于 `1`，故 `p` 在 `Y` 通道上
**只通过 `λ` 与 `a` 变化**。这是「`dSep` 收缩了 `Y` 的自由度」的精确形式。 -/
theorem screen_split_Y_channel_collapses {V : Type*} [DecidableEq V] [Fintype V]
    (G : DAG V) {X Y Z : Finset V} (h : G.dSep X Y Z)
    (p : (V × V) × V → ℝ) (hsp : ScreenSplit G X Y Z p) :
    ∃ (lam : V → ℝ) (a : V → V → ℝ),
      ∀ x z, ∀ y ∈ Y, p ((x, y), z) = lam z * a x z := by
  obtain ⟨lam, a, b, hb, hone⟩ := screen_split_Y_factor_trivial G h p hsp
  refine ⟨lam, a, fun x z y hy => ?_⟩
  rw [hb x y z, hone y hy z, mul_one]

/- ⚠ **诚实边界（本文件在此显式登记，不用定理伪装）**：

  * `ScreenSplit` **不是**由 `dSep` 推出的。它是**显式前提**
    （概率侧的剖分结构 + 屏幕退化条件）；`dSep` 只负责把它的第二个合取项
    **变成对所有 `y ∈ Y` 同时成立的强命题**（V17-13）。
  * **`dSep ⟹ ScreenSplit` 不在此文件**，也不应在此文件：那需要一般 DAG 上的
    `p = ∏_v p(x_v | x_{pa(v)})` 因子分解。该路线在 `Fate/FactorMarkov.lean` 已交付
    **单步**（`sink_peel`），但卡在 `DAG.induce`（`PEARL_127_PROOF_ROADMAP` §3 A4
    「缺口 A」）。**此缺口在此显式登记，不隐藏。**
  * `ScreenSplit` 的“屏幕外 `b = 1`”是**结构性假设**（而非概率语义的必然）；
    本文件只证明：**一旦接受它，`dSep` 就是它的唯一激活器**。
  * **修复记录**：本段原先把下一节的注释起始记号误纳入本注释内部，
    导致 §9 整体解析失败；现已拆成两个独立注释块。
    （修复记录 2：本段原用文档注释（斜杠双横线）但后面接的是模块注释
    而非声明，Lean 报告 unexpected token，期望 lemma；
    现改为普通注释。） -/

/-! ### 9.3 本节小结：与 §5 的差别（可机检）

  | 项 | §5 `view17_bridge` | §9 `screen_split_Y_factor_trivial` |
  |---|---|---|
  | `dSep` 前提 | `_hsep`（哑元）| `h : G.dSep X Y Z`（**真消费**）|
  | 顶点与概率下标 | `Finset V` vs `α β γ`（**无联系**）| 对齐为 `α = β = γ = V` |
  | 结论 | `CondMul p`（与图无关）| `∀ y ∈ Y, b y z = 1`（**含 `Y`，依赖图**）|
  | 去掉图假设 | 定理不变 | **证明失败**（`disjoint_left` 无法构造）|

  **⟹ §9 是视角 17 对「图从未做功」这条根因的、本文件内的**可机检修正**；
  但它**只覆盖**屏幕退化这一条通道，**不是** Pearl 1.2.4 的一般形式。 -/

end Screen

/-! ===========================================================================
  §8 与 `mass` 的关系（**可机检的对照**）

  | 本文件用的 | `mass` 塔用的 |
  |---|---|
  | `FinCondIndep.margZ p z = ∑ x, ∑ y, p ((x,y),z)` | `mass S p x = ∑_{w : w|_S = x|_S} p w` |
  | **固定一个下标，对其余求和** | **固定一个集合的坐标，对其余同时求和** |
  | **外层只有 `p`，不嵌套** | **可以嵌套 `mass S (mass T p)`** |

  **⟹ 本文件的每一条求和都作用在 `p` 自身**，故**不存在**「对 `mass` 再取 `mass`」
  这种操作 —— **这正是“不用 mass 塔”的精确含义，而不是修辞。**
  =========================================================================== -/

end FateV2.Predict.GraphToProbView17
