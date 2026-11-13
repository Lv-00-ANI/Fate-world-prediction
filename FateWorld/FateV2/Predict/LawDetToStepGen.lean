import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.LawRule
import FateWorld.FateV2.Rules.LawRuleToTraj
import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Predict.DetFunToStepDraft

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/LawDetToStepGen.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 9 处，含 5 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict
open FateV2.Model
open FateV2.Modeling
open FateV2.Rules

/-
============================================================================
  规则核心链 · 桥路线甲（Dirac 规则 → Step）· **抽象上下文推广**（P0-4）

  ## 本模块做什么

  `FateV2.Predict/DetFunToStepDraft.lean` 的 `lawDetToStep` 把上下文空间写死为静态的
  `ctxPUnit : CtxSpace := ⟨PUnit⟩`（作者裁决「丙：先静态再抽象」中的静态步，
  P0 = `1b481f5`、P1 = `66f20b9` 已完成）。

  本模块完成**抽象步**：把 `lawDetToStep` 推广到**任意** `C : CtxSpace`
  与**任意**上下文注入函数

  $$\texttt{ctxOf} : X \to U \to \N \to \Theta \to A \to C .$$

  即上下文 `c` 由「当前状态 + 四位外部输入」**供给**（这正是
  `FateV2.Predict/LawRuleToTraj.lean` 闸 B 所说的「上下文由数据供给」，此处把该供给
  提升为 `Step` 的一个**显式参数**而非隐藏约定）。

  ## 本模块的定理

  | 编号 | 定理 | 证明 |
  |---|---|---|
  | 定理 1 | `lawDetToStepGen_apply`（推广版定义性展开） | `rfl` |
  | 定理 2 | `lawDetToStepGen_eq_of_ctxOf`（同 `ctxOf` 则同 `Step`） | `rfl` |
  | 定理 3 | `lawDetToStepGen_static`（**静态版是特例**） | `rfl` |
  | 定理 4 | `trajOfLaw_eq_iterate_lawDetToStepGen`（**迭代相容**） | 对 `n` 归纳 |
  | 定理 5 | `lawDetToStepGen_spec`（抽出的 Step 合法于 `R`） | `toDetFun_spec` |
  | 定理 6 | `lawDetToStepGen_isStep`（落在 `Step F` 里） | `⟨_, rfl⟩` |

  ## 前件非循环（自查）

  - `hR : IsDirac R` 是「`R` 允许集是 Dirac 单点」的假设，**不含**任何关于
    `Step` / 轨迹 / 迭代的结论。
  - 定理 3 的结论是「推广版在 `ctxOf := fun _ _ _ _ _ => PUnit.unit` 处
    **等于**静态版 `lawDetToStep`」——这是两个**不同定义**的相等，
    **不是** `X = X`。其右端是草案模块里独立定义的 `lawDetToStep`。
  - 定理 4 的结论是 `trajOfLaw`（`Nat.rec` 定义的轨迹）与
    `Function.iterate` 的相等，需要真正的归纳。

  ## 诚实标注

  - 本模块**只新增文件**，**未修改**任何已有模块。
  - 零 `sorry` / 零 `admit` / 零 `axiom` / 零 `set_option`。
  - **`MeasurableSpace` 显式传 `instX`**：`LawRule` 体系的 `[·]` 类型类位置
    在 `Y := F.X` 时**不会**从 `F.X.meas` 字段自动取，故一律显式传入。
  - 本模块**不**声称「`ctxOf` 可省」：`lawDetToStep`（静态）**不能**由
    `lawDetToStepGen` 以外的更弱形式得到；`ctxOf` 是真实参数。
  - 本模块**不**把 `ctxOf` 与 `trajOfLaw` 的上下文序 `cs` 混同：
    `trajOfLaw` 吃的是**外生序** `ℕ → C.Carrier`，而 `lawDetToStepGen`
    吃的是**自反馈式**供给（由状态决定）。定理 4 在 `ctxOf` **忽略状态**时
    二者对齐，这是两者关系的确切边界。
============================================================================
-/


namespace FateV2.Predict

noncomputable section

/-- **【P0-4：Dirac 规则 → Step（任意上下文空间 C 与任意 ctxOf）】**

给定

* 任意上下文空间 `C : CtxSpace`（**不再是静态的 `⟨PUnit⟩`**），
* 任意上下文注入 `ctxOf : X → U → Ν → Θ → Act → C`，
* `R : LawRule C F.X F.X` 与它的 Dirac 见证 `hR`，

则「把 `ctxOf` 算出的上下文喂给 `toDetFun`」得到一个 `Step F`。

**直读**：机制 = 「当前状态 `x` 与四位输入 `(u, ε, θ, a)` 决定上下文 `c`，
`R` 在 `c` 处的作用是 Dirac，取该 Dirac 的支撑点即为下一状态」。

**与静态版 `lawDetToStep` 的关系**：取 `ctxOf := fun _ _ _ _ _ => PUnit.unit`
即退回静态版（定理 3）。

标签：**[定义性约定]**。 -/
def lawDetToStepGen {C : CtxSpace} (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R) : Step F :=
  fun x u ν θ a => @LawRuleToTraj.toDetFun C F.X F.X instX R hR (ctxOf x u ν θ a) x

/-! ## §1  定理 1：定义性展开

推广版在单点上**就是**「`ctxOf` 算上下文 → `toDetFun`」。这是定义展开，
但单独列出便于下游 `simp`/`rw` 不必展开 `lawDetToStepGen` 的 lambda。 -/

/-- **【定义性展开】** 推广版 `Step` 在 `(x, u, ν, θ, a)` 处的值
即 `toDetFun R hR (ctxOf x u ν θ a) x`。 -/
theorem lawDetToStepGen_apply {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)
    (x : F.X.Carrier) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    lawDetToStepGen F instX ctxOf R hR x u ν θ a
      = @LawRuleToTraj.toDetFun C F.X F.X instX R hR (ctxOf x u ν θ a) x :=
  rfl

/-! ## §2  定理 2：同 `ctxOf` ⟹ 同 `Step`

推广版的**全部**上下文依赖都经过 `ctxOf`。故若两个 `ctxOf` 逐点相等，
抽出的 `Step` 相等。这钉死「机制只由 `ctxOf` 与 `R` 决定」。 -/

/-- **【`Step` 只依赖 `ctxOf` 与 `R`】** -/
theorem lawDetToStepGen_eq_of_ctxOf {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf₁ ctxOf₂ : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (h : ∀ x u ν θ a, ctxOf₁ x u ν θ a = ctxOf₂ x u ν θ a)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R) :
    lawDetToStepGen F instX ctxOf₁ R hR = lawDetToStepGen F instX ctxOf₂ R hR := by
  funext x u ν θ a
  rw [lawDetToStepGen_apply, lawDetToStepGen_apply, h]

/-! ## §3  定理 3：静态版是推广版的**特例**

`DetFunToStepDraft.lawDetToStep` 用写死的 `ctxPUnit = ⟨PUnit⟩` 与
`PUnit.unit`。取

$$\texttt{ctxOf} := \lambda x\,u\,\nu\,\theta\,a.\ \texttt{PUnit.unit}$$

则 `lawDetToStepGen` 在 `C := ctxPUnit` 处**定义上等于** `lawDetToStep`。

**这不是同义反复**：左端是 `LawDetToStepGen` 里的新 `def`，
右端是 `DetFunToStepDraft` 里**独立定义的**旧 `def`；
等式断言「新定义在特例处**复现**旧定义」。 -/

/-- **静态上下文注入**：把 `ctxPUnit` 的上下文恒取 `PUnit.unit`。 -/
def ctxOfStatic (F : Frame) :
    F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → ctxPUnit.Carrier :=
  fun _ _ _ _ _ => PUnit.unit

/-- **【静态版是推广版的确实特例】**

`lawDetToStepGen F instX (ctxOfStatic F) R hR = lawDetToStep F instX R hR`。

**证明**：`rfl` —— 两个定义展开后在 `C := ⟨PUnit⟩`、`ctxOf` 恒为
`PUnit.unit` 处逐点相同。（`lawDetToStep` 的 `PUnit.unit` 与本处
`ctxOfStatic F _ _ _ _ _` 定义上都化简为 `PUnit.unit`。） -/
theorem lawDetToStepGen_static (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (R : LawRule.LawRule ctxPUnit F.X F.X)
    (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R) :
    lawDetToStepGen F instX (ctxOfStatic F) R hR = lawDetToStep F instX R hR :=
  rfl

/-! ## §4  定理 4：迭代相容

若 `ctxOf` **忽略状态**（即上下文由外部输入 `(u, ν, θ, a)` 决定、不依赖 `x`），
则 `lawDetToStepGen` 抽出的 `Step` 逐次迭代，**精确复现**
`trajOfLaw` 在恒定上下文序 `fun _ => ctxOf x u ν θ a` 下的轨迹。

**为什么需要「`ctxOf` 忽略状态」**：`trajOfLaw` 的上下文序 `cs` 是
**外生**的（与状态无关的序）；而 `lawDetToStepGen` 每一步都**重新**用
「当时的状态」算上下文。二者只在 `ctxOf` 不依赖状态时一致。
这是两者关系的**确切边界**，本模块如实登记，不掩盖。

**证明**：对 `n` 归纳；`succ` 步用 `Function.iterate_succ_apply'`
把迭代展开为一次 `Step` 调用，再用归纳假设与 `trajOfLaw_succ`。 -/

/-- **【迭代相容：`trajOfLaw` ≡ `lawDetToStepGen` 迭代】**

在 `ctxOf` 忽略状态下，`trajOfLaw R hR (fun _ => ctxOf x u ν θ a) x₀ n`
与 `(lawDetToStepGen F instX ctxOf R hR · u ν θ a)^[n] x₀` 逐点相等。

**这是 P0-4 的核心**：抽象上下文版抽出的 `Step` 反复迭代，
生成的正是规则 `R` 在相应上下文序下生成的那条轨迹。 -/
theorem trajOfLaw_eq_iterate_lawDetToStepGen {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)
    (x₀ : F.X.Carrier) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (hctx : ∀ x₁ x₂ : F.X.Carrier, ctxOf x₁ u ν θ a = ctxOf x₂ u ν θ a) :
    ∀ n : ℕ,
      LawRuleToTraj.trajOfLaw R hR (fun _ => ctxOf x₀ u ν θ a) x₀ n =
        (lawDetToStepGen F instX ctxOf R hR · u ν θ a)^[n] x₀ := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show @LawRuleToTraj.toDetFun C F.X F.X instX R hR (ctxOf x₀ u ν θ a)
        (LawRuleToTraj.trajOfLaw R hR (fun _ => ctxOf x₀ u ν θ a) x₀ k)
      = lawDetToStepGen F instX ctxOf R hR
          ((fun x => lawDetToStepGen F instX ctxOf R hR x u ν θ a)^[k] x₀) u ν θ a
    rw [ih]
    rw [lawDetToStepGen_apply]
    exact congrArg (fun c => @LawRuleToTraj.toDetFun C F.X F.X instX R hR c _)
      (hctx _ _)

/-! ## §5  定理 5：抽出的 `Step` 合法于 `R`

「合法」的确切含义：`R` 在 `ctxOf` 算出的上下文与当前状态处，
允许的分布集合**恰是**「下一状态的 Dirac 测度」这一单点集。

这条把「我们用了 `toDetFun`」升级为「我们用的正是 `R` 允许的那个分布」，
即轨迹每一步都是 `R` 的**合法步**。 -/

/-- **【抽出的 `Step` 合法于规则 `R`】**

`R (ctxOf x u ν θ a) x = {δ_{lawDetToStepGen … x u ν θ a}}`。 -/
theorem lawDetToStepGen_spec {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)
    (x : F.X.Carrier) (u : F.U.Carrier) (ν : F.Ν.Carrier)
    (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    R (ctxOf x u ν θ a) x
      = {MeasureTheory.Measure.dirac (lawDetToStepGen F instX ctxOf R hR x u ν θ a)} := by
  rw [lawDetToStepGen_apply]
  exact @LawRuleToTraj.toDetFun_spec C F.X F.X instX R hR (ctxOf x u ν θ a) x

/-! ## §6  定理 6：落在 `Step F` 类型里

把「它属于 `Step` 类型」显式写出，便于世界模型以 `∃ f : Step F, …` 使用。 -/

/-- **【推广版抽出的机制是一个合法的 `Step`】** -/
theorem lawDetToStepGen_isStep {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
      F.Act.Carrier → C.Carrier)
    (R : LawRule.LawRule C F.X F.X)
    (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R) :
    ∃ f : Step F, ∀ x u ν θ a,
      f x u ν θ a = lawDetToStepGen F instX ctxOf R hR x u ν θ a :=
  ⟨lawDetToStepGen F instX ctxOf R hR, fun _ _ _ _ _ => rfl⟩

end

end FateV2.Predict
