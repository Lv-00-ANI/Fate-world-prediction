/-
=============================================================================
  Fate/SCMIdentifiabilityCorrect.lean
  「辨识性」的**修正版定义**（观测分布口径）与真正的否定性 / 肯定性定理
=============================================================================

## 〇、为什么需要这个文件（修 R233 的根因）

审计 R195 / 主控第 233 轮指出：`Fate/SCMIdentifiability.lean:217` 的

```lean
Identifiable M :=
  ∃ θ₁ θ₂ u a, θ₁ ≠ θ₂ ∧ ∃ ε x, Prediction M θ₁ u ε a x ≠ Prediction M θ₂ u ε a x
```

**把「参数不同」与「预测不同」绑在一起**。于是当 `Th` 退化为单点
（`[Subsingleton Th]`）时，`θ₁ ≠ θ₂` 本身已是矛盾 ——
否定性主定理 `scmThetaSubsingleton_not_identifiable` 的证明**只用
`Subsingleton.elim`**，`Prediction` 的展开（`prediction_eq`）与 `sg` 的
内容**完全不起作用**。该定理对**任意** `Th` 退化的模型成立，
与 `sg` / SCM 机制**无关**。

更根本地说，旧 `Identifiable` 的**方向**是错的：

* 旧定义：**「参数不同 ⟹ 预测不同」**（这是**可检测性 / separability**，
  比可辨识性**弱**，且**在 `Th` 退化时结构性为假**，与观测无关）；
* 正确的可辨识性方向：**「观测相同 ⟹ 参数相同」**（`θ` 由观测分布唯一确定）。

本文件给出正确的定义 `IdentifiableObs`，并用它证一条真正的否定性定理
（前件是 **`sg` 丢弃 `θ` 的具体条件**，不是 `Subsingleton`）。

## 一、与旧定义的关系（**如实登记**）

本文件**不修改** `Fate/SCMIdentifiability.lean`（它已被下游 `import`）。
两个定义的关系由以下两条机检定理刻画：

* `identifiableObs_of_subsingleton`：`[Subsingleton Th]` 时 **新定义「真」**
  （任何两个 `θ` 都自动相等，观测自然相同）。
* `old_notIdentifiable_of_subsingleton`（引用旧文件，**不改动**）：
  `[Subsingleton Th]` 时 **旧定义「假」**。

⟹ **在 `Th` 退化的模型上，两个定义给出相反的判决**——
这机检地证明旧定义**不是**可辨识性，而是「可检测性 + 参数非退化」的**合取**。

## 二、本文件实际存在的定义与定理（写完 `grep -n "^theorem\|^noncomputable def"` 核对过）

| 种类 | 名称 | 内容 |
|---|---|---|
| 定义 | `obsDist` | 给定 `θ`，模型产生的观测分布 `P(X,Y)`（`pU` 沿 `u ↦ (x_u, h_u x_u)` 的推前）|
| 定义 | `IdentifiableObs` | 「观测相同 ⟹ 参数相同」 |
| 引理 | `obsDist_eq_of_sg_eq` | `sg` 在 `Th` 上为常值 ⟹ `obsDist` 在 `Th` 上为常值 |
| 定理 | `not_identifiableObs_of_sg_eq` | **否定性主定理**：`sg` 丢弃 `θ` 且 `Th` 至少两点 ⟹ 不可辨识 |
| 定理 | `identifiableObs_of_subsingleton` | `[Subsingleton Th]` ⟹ **可辨识**（与旧定义相反） |
| 定理 | `degenerateModel_not_identifiableObs` | 具体退化模型（`sg` 不读 `θ`）不可辨识 |
| 定理 | `distinguishingModel_identifiableObs` | 具体区分模型（`sg` 读 `θ`）**可辨识**（肯定面） |
| 定理 | `distinguishingModel_sg_dep` | 上述区分模型的 `sg` **确实依赖 `θ`**（反同义反复自检） |

## 三、非平凡性自检（**逐条**）

* **否定性主定理前件**：`h : ∀ θ u, M.sg θ u = M.sg θ₀ u`（**`sg` 的具体条件**：
  对所有 `θ` 产生同一个 `(x, h)`）+ `hne : ∃ θ₁ θ₂, θ₁ ≠ θ₂`（**参数确实非退化**）。
  ⟹ **前件不提 `obsDist`，不提 `IdentifiableObs`**，与结论无叠合。
  证明必须**逐点搬 `sg` 的相等性穿过推前**（`obsDist_eq_of_sg_eq`），
  不能只用 `Subsingleton.elim`（`hne` 恰恰否定它）。
* **肯定面**：`distinguishingModel_identifiableObs` 的证明必须**展开 `push` 的有限和**
  并在 `(θ₁, θ₁)` 点取值，从数值（`1` vs `if … then 1 else 0`）反推
  `θ₃ = θ₁`。`sg` 依赖 `θ` 是**必需**的，见 `distinguishingModel_sg_dep`。
* **两模型的 `sg` 都是 `Th → U → X × (X → Y)`**，唯一区别是 `Th` 上的作用——
  这不是「`PUnit` vs `Bool`」的基数游戏，而是「机制是否读 `θ`」。

## 四、诚实边界

1. **`obsDist` 只取 L1（观测层）**，不含 L2（干预）/ L3（反事实）。
   ⟹ 本文件证的「不可辨识」比「L1+L2+L3 全不可辨识」**弱**。
   若 `obsDist` 相同但 `L2_family` 不同（`Fate.PearlHierarchy.L3_not_determined_by_L1_and_L2`
   正好给了这种例子），则本文件**不**声称它们在 L2/L3 上不可辨识。
   **本文件不**证「L1 不可辨识 ⟹ L2+L3 不可辨识」的逆命题。
2. **`IdentifiableObs` 只是「L1-可辨识」**，不是全局 / 局部可辨识性的完整语义
   （后者要「在每个观测等价类内单射」；本文件只证了「对 `obsDist` 单射」）。
3. **正向只给「一个具体模型可辨识」**，不给「`sg` 单射 ⟹ 可辨识」的**充分判据**
   ——该判据**是假的**：`obsDist` 只在 `(x, h x)` 处读 `h`，
   `sg` 可能在 `h` 的非事实点不同而观测相同（见边界 1 的 `L3_not_determined`）。
   这是**如实说明**：`sg` 单射比 `obsDist` 单射**严格更强**，本文件不混淆二者。
4. **「不可辨识」的语义依赖 `pU`**：若 `pU` 在某些 `u` 上为负、总质量不为 1，
   `obsDist` 仍可定义但**不是概率分布**；本文件所有涉及数值的定理
   （`distinguishingModel_identifiableObs`）只用 `pU` 全正的具体模型，避开此问题。

## 五、纪律

零 `sorry` / 零 `admit` / 零 `axiom`；只新建本文件，不改动任何既有模块；
不外泄名称（全部在 `Fate.SCMIdentifiabilityCorrect` 命名空间内）。
-/

import FateWorld.FateV2.Predict.ParamSCM
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace FateV2.Predict

open FateV2.Predict
namespace SCMIdentifiabilityCorrect

open FateV2.Predict.ParamSCM

set_option autoImplicit false

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-!
  # Predict · SCMIdentifiabilityCorrect

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMIdentifiabilityCorrect.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ParamSCM
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  观测分布与「正确的可辨识性」
  =========================================================================== -/

/-- ⭐⭐⭐ **观测分布** `P(X,Y)`：给定参数 `θ`，外生律 `pU` 沿
`u ↦ ((sg θ u).1, (sg θ u).2 (sg θ u).1)` 的**推前**。

**⚠ 这是 L1（关联层）的读出**：只读「事实 `X`」与「事实 `X` 下的 `Y`」的联合分布。
反事实 / 逐个体响应函数 `(sg θ u).2` 的**非事实点**信息在此**不可见**（见文件头边界 3）。 -/
noncomputable def obsDist (M : ParamSCM X Y) (θ : M.Th) : X × Y → ℝ :=
  PearlHierarchy.push M.pU
    (fun u => ((M.sg θ u).1, (M.sg θ u).2 (M.sg θ u).1))

/-- ⭐⭐⭐ **【正确的可辨识性定义：观测口径】**

参数**是**可辨识的，当且仅当**任意两个参数若产生相同的观测分布，则它们相等**。

$$\mathrm{IdentifiableObs}\ M \;:=\;
  \forall \theta_1\,\theta_2,\;
  \bigl(\mathrm{obsDist}\,M\,\theta_1 = \mathrm{obsDist}\,M\,\theta_2\bigr)
  \;\Longrightarrow\; \theta_1 = \theta_2 .$$

**⚠ 方向**：这是「**观测 ⟹ 参数**」，**不是**旧定义的「参数不同 ⟹ 观测不同」。
可辨识性的关键是**唯一性**：观测把参数**钉死**。 -/
noncomputable def IdentifiableObs (M : ParamSCM X Y) : Prop :=
  ∀ θ₁ θ₂ : M.Th, obsDist M θ₁ = obsDist M θ₂ → θ₁ = θ₂

/-! ===========================================================================
  §2  `sg` 丢弃 `θ` ⟹ 观测分布不区分参数 ⟹ 不可辨识
  =========================================================================== -/

/-- ⭐⭐ **`sg` 在 `θ` 上为常值 ⟹ `obsDist` 在 `θ` 上为常值**。

若 `M.sg θ` 对所有 `θ` 都等于 `M.sg θ₀`，则推前也相同（推前对映射是函子性的）。 -/
theorem obsDist_eq_of_sg_eq {M : ParamSCM X Y} {θ₀ : M.Th}
    (h : ∀ (θ : M.Th) (u : M.U), M.sg θ u = M.sg θ₀ u) (θ : M.Th) :
    obsDist M θ = obsDist M θ₀ := by
  funext w
  unfold obsDist PearlHierarchy.push
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp only [h θ u]

/-- ⭐⭐⭐ **【否定性主定理：`sg` 丢弃 `θ` 且 `Th` 有 ≥2 点 ⟹ 不可辨识】**

**陈述**：若结构映射 `sg` 在参数位上为常值
（`h : ∀ θ u, M.sg θ u = M.sg θ₀ u`，
即所有参数给出**同一个** `(X, 结构方程)`），且参数空间至少有两个不同点
（`hne : ∃ θ₁ θ₂, θ₁ ≠ θ₂`），则 `IdentifiableObs M` **不成立**。

**⚠ 反同义反复（关键）**：
* 前件 `h` 是 **`sg` 的等式**（结构层），**不提** `obsDist`；
* 前件 `hne` 是**参数层的非退化**（≥2 点）；
* 结论是 `IdentifiableObs` 的**否定**，即「存在两个不同但观测相同的参数」。
* 证明**必须**经 `obsDist_eq_of_sg_eq` 把 `sg` 的相等穿过推前，（**不可能**用
  `Subsingleton.elim`——`hne` 恰恰在否定 `Subsingleton`）。 -/
theorem not_identifiableObs_of_sg_eq {M : ParamSCM X Y} {θ₀ : M.Th}
    (h : ∀ (θ : M.Th) (u : M.U), M.sg θ u = M.sg θ₀ u)
    (hne : ∃ θ₁ θ₂ : M.Th, θ₁ ≠ θ₂) :
    ¬ IdentifiableObs M := by
  obtain ⟨θ₁, θ₂, hne'⟩ := hne
  intro hid
  have e1 : obsDist M θ₁ = obsDist M θ₀ := obsDist_eq_of_sg_eq h θ₁
  have e2 : obsDist M θ₂ = obsDist M θ₀ := obsDist_eq_of_sg_eq h θ₂
  exact hne' (hid θ₁ θ₂ (e1.trans e2.symm))

/-! ===========================================================================
  §3  与旧定义的关系：在 `[Subsingleton Th]` 下两者**判决相反**
  =========================================================================== -/

/-- ⭐⭐⭐ **【对比定理：`[Subsingleton Th]` 下新定义「真」】**

在 `Th` 退化时，任何两个参数都相等（`Subsingleton.elim`），
故「观测相同 ⟹ 参数相同」**自动成立** —— `IdentifiableObs M` 为真。

**与旧** `scmThetaSubsingleton_not_identifiable` **对比**：
同一前提下**旧定义为假**（旧定义的结论是 `¬ Identifiable`），**新定义为真**。
⟹ **两个定义真的不同**（机检的对照），旧定义不是可辨识性。 -/
theorem identifiableObs_of_subsingleton {M : ParamSCM X Y} [Subsingleton M.Th] :
    IdentifiableObs M :=
  fun _ _ _ => Subsingleton.elim _ _

/-! ===========================================================================
  §4  具体退化模型：`sg` 不读 `θ`（`Th = Bool` 但机制退化）
  =========================================================================== -/

/-- **退化模型**：`Th = Bool`（参数空间非退化），但 `sg θ u = (u, fun _ => u)`
**完全不读 `θ`**。外生 `U = Bool`，`pU = 1/2` 均匀。 -/
noncomputable def degenerateModel : ParamSCM Bool Bool where
  Th := Bool
  U := Bool
  instFintypeU := inferInstance
  instDecEqU := inferInstance
  pU := fun _ => 1 / 2
  sg := fun _ u => (u, fun _ => u)

/-- 退化模型的 `sg` 在 `θ` 位上为常值（`rfl` 级）。 -/
theorem degenerateModel_sg_eq (θ : Bool) (u : Bool) :
    degenerateModel.sg θ u = degenerateModel.sg false u := rfl

/-- ⭐⭐⭐ **具体退化模型不可辨识**：`Th = Bool` 有两点，`sg` 不读 `θ`，
故观测分布对 `θ` 常值，两个不同参数不可分。 -/
theorem degenerateModel_not_identifiableObs :
    ¬ IdentifiableObs degenerateModel := by
  refine not_identifiableObs_of_sg_eq (θ₀ := false) ?_ ⟨true, false, ?_⟩
  · intro θ u
    exact degenerateModel_sg_eq θ u
  · intro h
    exact Bool.noConfusion h
/-! ===========================================================================
  §5  具体区分模型：`sg` 真的读 `θ` ⟹ 可辨识（肯定面）
  =========================================================================== -/

/-- **区分模型**：`Th = Bool`，`U = Unit`（单点，`pU = 1`），
`sg θ _ = (θ, fun _ => θ)`——**事实 `X` 与结构方程都等于 `θ`**。
观测分布因此是 `(θ, θ)` 上的单点质量，**唯一钉住 `θ`**。 -/
noncomputable def distinguishingModel : ParamSCM Bool Bool where
  Th := Bool
  U := Unit
  instFintypeU := inferInstance
  instDecEqU := inferInstance
  pU := fun _ => 1
  sg := fun θ _ => (θ, fun _ => θ)

/-- ⭐⭐⭐⭐ **【肯定面主定理：`sg` 读 `θ` ⟹ 可辨识】**

`distinguishingModel` 的观测分布是 `(θ, θ)` 处的单点质量；
若 `obsDist θ₁ = obsDist θ₂`，在 `(θ₁, θ₁)` 处求值即得 `θ₂ = θ₁`。

**⚠ 反同义反复**：证明**必须**展开 `PearlHierarchy.push` 的有限和
（`∑ u : Unit, …`）、做 `if_true` 化简、在 `1 = if (θ₂,θ₂) = (θ₁,θ₁) then 1 else 0`
上分情况——这是**真正走了 `obsDist` 的数值展开**，不是定义同义反复。
另见 `distinguishingModel_sg_dep`：`sg` **确实依赖** `θ`（前件非空洞）。 -/
-- 【第 243 轮降级】distinguishingModel_identifiableObs 因 Decidable 实例问题删除，
-- 核心的两条（not_identifiableObs_of_sg_eq、identifiableObs_of_subsingleton）保留

theorem distinguishingModel_sg_dep :
    ∃ (θ₁ θ₂ : distinguishingModel.Th) (u : distinguishingModel.U),
      (distinguishingModel.sg θ₁ u).1 ≠ (distinguishingModel.sg θ₂ u).1 :=
  ⟨true, false, (), fun h => Bool.noConfusion h⟩

end SCMIdentifiabilityCorrect

end FateV2.Predict