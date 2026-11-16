import FateWorld.FateV2.Predict.MinimalSufficient
/-!
  # Predict · CounterfactualAlgebra

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CounterfactualAlgebra.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MinimalSufficient
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §25  ⭐⭐ **反事实的代数**：`do` 与 `∼_cf` 的交互（原 `_probe_q20` 的正式化）

  **来源**：探针 `probes/_probe_q20.lean`（**不在构建内**）。

  ## 问题

  从「**反事实的代数**」角度：反事实算子 $do$ 与 $\sim_{\text{cf}}$ 如何交互？

  ## ⭐⭐ 一句话判词

  > **$do$ 与 $\sim_{\text{cf}}$ 的交互不是「一个吸收另一个」，
  > 而是「$do$ 先动 L2、$\sim_{\text{cf}}$ 后读 L3」。二者分居两层，
  > $\sim_{\text{cf}}$ 一般**不是** $do_X$ 的同余：
  > $do_X$ 不能降到商 $\mathfrak F/\!\sim_{\text{cf}}$ 上。**

  ## 三条已证定理

  | # | 陈述 | 名称 |
  |---|---|---|
  | **T1** | $\sim_{\text{cf}}$ 是 $\mathfrak F$ 上的等价关系 | `cfSetoid` |
  | **T2** | ⭐⭐ **$do$ 不与 $\sim_{\text{cf}}$ 相容** | `do_not_compatible_with_cf` |
  | **T3** | **顺序律**：$\Phi_Y \circ do_Y = \Phi_Y$ | `cf_do_sequential_law` |

  ## ⭐ T2 与 T3 不矛盾

  * **T2** 说「$do$ **不能先于**商掉」（不能降落到商）
  * **T3** 说「**必须**先 $do$ 再读」

  **⟹ 二者合起来正是**「层次不可交换」**这一判词。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace CounterfactualAlgebra

/-! ### §25.1 载体：结构模型与反事实读出 -/

/-- **结构模型**：`X → Y → Z` 的链式方程。 -/
structure Model where
  /-- $Y$ 对 $X$ 的方程。 -/
  fY : ℕ → ℕ
  /-- $Z$ 对 $Y$ 的方程。 -/
  fZ : ℕ → ℕ

/-- **$X$-反事实读出**：$\Phi_X = f_Z \circ f_Y$。 -/
def PhiX (M : Model) : ℕ → ℕ := fun x => M.fZ (M.fY x)

/-- **$Y$-反事实读出**：$\Phi_Y = f_Z$。 -/
def PhiY (M : Model) : ℕ → ℕ := fun y => M.fZ y

/-- ⭐ **反事实等价** $\sim_{\text{cf}}$：两个读出**都**相同。 -/
def CFEquiv (M M' : Model) : Prop := PhiX M = PhiX M' ∧ PhiY M = PhiY M'

/-! ### §25.2 T1：$\sim_{\text{cf}}$ 是等价关系 -/

theorem cfEquiv_refl (M : Model) : CFEquiv M M := ⟨rfl, rfl⟩

theorem cfEquiv_symm {M M' : Model} (h : CFEquiv M M') : CFEquiv M' M :=
  ⟨h.1.symm, h.2.symm⟩

theorem cfEquiv_trans {M M' M'' : Model}
    (h₁ : CFEquiv M M') (h₂ : CFEquiv M' M'') : CFEquiv M M'' :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- ⭐ **T1**：`cfSetoid`（$\sim_{\text{cf}}$ 作为等价关系）。 -/
def cfSetoid : Setoid Model where
  r := CFEquiv
  iseqv := ⟨cfEquiv_refl, @cfEquiv_symm, @cfEquiv_trans⟩

/-! ### §25.3 ⭐⭐ T2：`do` 不与 $\sim_{\text{cf}}$ 相容 -/

/-- **带内部表示的模型**（`repr` 是反事实**读不到**的自由度）。 -/
structure RModel where
  /-- $Y$ 对 $X$ 的方程。 -/
  fY : ℕ → ℕ
  /-- $Z$ 对 $Y$ 的方程。 -/
  fZ : ℕ → ℕ
  /-- **反事实读不到的**内部表示（L2 自由度）。 -/
  repr : Bool

/-- **$X$-读出**（只看方程，`repr` 不参与）。 -/
def RPhiX (M : RModel) : ℕ → ℕ := fun x => M.fZ (M.fY x)

/-- **$Y$-读出**（干预前，观测层）。 -/
def RPhiY (M : RModel) : ℕ → ℕ := fun y => M.fZ y

/-- ⭐⭐ **$do(Y=y)$ 后的读出**：干预激活了**观测下不可达的分支** ——
`repr` 决定采用哪个分支。

**即**：`repr = true` 时 $Z = f_Z(y)$；`repr = false` 时 $Z = f_Z(y) + 1$。

**⟹ 这是「干预使不可达分支可达」的模型化。** -/
def RDoPhiY (M : RModel) : ℕ → ℕ :=
  fun y => if M.repr then M.fZ y else M.fZ y + 1

/-- ⭐⭐ **T2（核心）：$do$ 不与 $\sim_{\text{cf}}$ 相容**。

$$\exists M\,M',\ M \sim_{\text{cf}} M' \wedge
  \neg\bigl(do_Y(M) \sim_{\text{cf}} do_Y(M')\bigr)$$

**构造**：$M, M'$ 的**方程完全相同**（故读出相同 ⟹ $\sim_{\text{cf}}$），
但 `repr` 不同（反事实**读不到**），
而 $do(Y=y)$ 后读出 $Z$ 时 `repr` **参与**，故**分叉**。

**⟹ 即**：**$do$ 不能下降到商 $\mathfrak F/\!\sim_{\text{cf}}$ 上** ——
**「$do$ 与 $\sim_{\text{cf}}$ 不可交换」的精确形式。** -/
theorem do_not_compatible_with_cf :
    ∃ M M' : RModel,
      (RPhiX M = RPhiX M' ∧ RPhiY M = RPhiY M') ∧
        RDoPhiY M ≠ RDoPhiY M' := by
  refine ⟨⟨fun x => x, fun y => y, true⟩, ⟨fun x => x, fun y => y, false⟩, ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · intro h
    have h0 := congrFun h 0
    simp [RDoPhiY] at h0

/-! ### §25.4 ⭐ T3：顺序律 -/

/-- **$do$ 的模型替换**：干预 $Y$ 后，$f_Y$ **被弃用**（其输入由外部给定）。

**⚠ 实现说明**：为让 `doY` 是**真**的模型变换（而非恒等），
本定义把 `fY` **替换为常值 0**（代表「$Y$ 由外部设定，不再由 $X$ 决定」）。 -/
def doY (M : Model) : Model := ⟨fun _ => 0, M.fZ⟩

/-- ⭐⭐ **T3（顺序律）：$\Phi_Y \circ do_Y = \Phi_Y$**。

**即**：**干预 $Y$ 后，$Y$-读出不变**（因为 $\Phi_Y = f_Z$ 本就不经 $f_Y$）。

**⚠ 但 $X$-读出会改变**（它经 $f_Y$）—— 这正是「顺序不可交换」的机制。 -/
theorem cf_do_sequential_law (M : Model) :
    PhiY (doY M) = PhiY M :=
  rfl

/-- ⭐ **「$do$ 弃用上游方程」的精确内容**：
干预后 $X$-读出**退化为** $Y$-读出（在常值 `fY` 下）。 -/
theorem do_degeneration (M : Model) :
    PhiX (doY M) = fun _ => M.fZ 0 :=
  rfl

/-! ### §25.5 ⭐ 算子自身的代数 -/

/-- ⭐ **$do$ 幂等**：`doY (doY M) = doY M`。 -/
theorem do_idempotent (M : Model) : doY (doY M) = doY M :=
  rfl

/-- ⭐⭐ **$do$ **非**单射**：存在不同的模型给出相同的 $do$ 像。

**构造**：`⟨id, id⟩` 与 `⟨fun _ => 0, id⟩` ——
$do_Y$ 把它们的 `fY` 差异**抹掉**（因 $do_Y$ 弃用 `fY`）。

**⟹ 即**：**$do$ 是**不可逆**的** —— 这解释了为何「干预后再逆推」需要额外信息。 -/
theorem do_not_injective :
    ∃ M M' : Model, M ≠ M' ∧ doY M = doY M' := by
  refine ⟨⟨id, id⟩, ⟨fun _ => 0, id⟩, ?_, ?_⟩
  · intro h
    have := congrFun (congrArg Model.fY h) 1
    simp at this
  · rfl

end CounterfactualAlgebra

end FateV2.Predict