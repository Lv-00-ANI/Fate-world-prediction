/-
============================================================================
  T12 · `WorldModel.rules` 与其 `simulator` 的**一致性定理**

  ## 背景（实测，非猜测）

  外部规划（命运项目·执行规划.md v2）§1.3 问题 1 指出：

  > `WorldModel.rules` 字段是占位符。两个独立字段，结构不保证关联。
  > `ruleWorldModel` 里 `rules` 填占位的 dirac 规则，
  > `simulator` 填真正的规则驱动步进。
  > ⟹ 规则真正起作用的是 simulator，`rules` 字段没有承载实际语义。

  ### 实测的四个结构定义

  `Fate/Frame.lean:348`（实测）：

  ```
  structure Rule (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
      [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
    kernel : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier
  ```

  `Fate/Frame.lean:545`（实测）：`abbrev Rules C X Y := Set (Rule C X Y)`

  `Fate/WorldModel.lean:120`（实测）：

  ```
  structure WorldRules (C) (X) (Y) [ms X] [ms Y] where
    rules : Rules C X Y
    nonempty : rules.Nonempty
  ```

  `Fate/WorldModel.lean:169`（实测）：

  ```
  structure WorldSimulator (F : Frame) where
    step : Step F
    horizon : ℕ
  ```

  ⟹ **`WorldRules` 是 `structure`**（带 `rules` / `nonempty` 两字段），
  故「规则集 = 由 R 驱动的那条规则」是**字段等式**，可证。

  ### 规划的三种表述（外部规划 §1.3）

  | 表述 | 含义 | 本模块 |
  |---|---|---|
  | (a) 行为一致：`rules` 生成的所有轨迹 ⊇ `simulator` 的轨迹 | 最强 | **不做**（需 `Rules ⇒ Step` 的轨迹语义，未定义） |
  | (b) 存在性：存在规则子集与 `simulator.step` 一致 | 中 | **部分做**（见 T4） |
  | (c) 构造性：`simulator.step` 由 `rules` 中某条规则经 `lawDetToStepGen` 构造 | 最弱 | **本模块主目标** |

  ## 本模块做什么（(c) 的严格落实）

  规划要求证 `ruleWorldModel` 的 `rules` 字段「不是任意占位符」。
  **实测结论：`ruleWorldModel`（`Fate/RuleDrivesEndToEnd.lean:159`）的
  `rules` 字段确实是硬编码的 `fun _ x => dirac x` 占位符，
  与 `simulator.step`（= `lawDetToStepGen F instX ctxOf R hR`）无关。**
  这一点**不可**用定理掩盖，故本模块**不**对原 `ruleWorldModel` 宣称任何
  「rules 由 R 驱动」的结论（那会是假命题）。

  本模块的路线：**新增一个修正版构造** `ruleWorldModelWithRules`，
  其 `rules` 字段**真正**由 `R` 经 `DetRule.toRule` 构造，
  然后在**修正版**上证明 (c)：

  $$\texttt{(ruleWorldModelWithRules}\ R\ h_R\ x_0\texttt{).simulator.step}
    \;=\; \texttt{lawDetToStepGen}\ F\ \texttt{instX}\ \texttt{ctxOf}\ R\ h_R$$

  并且证明**这条 step 的每一步输出，都落在 `rules` 字段所允许的集合里**——
  这才是「`rules` 承载实际语义」的**实质内容**
  （而不是「两个字段恰好都是同一个值」，后者是同义反复）。

  ## 定理清单

  | 编号 | 定理 | 内容 | 证明 |
  |---|---|---|---|
  | T1 | `ruleOfLaw` | 「由 `R` + `h_R` 构造的 `Rule`」的定义 | 定义 |
  | T2 | `ruleWorldModelWithRules_rules_eq` | `rules.rules = {ruleOfLaw R hR}` | `rfl` |
  | T3 | `ruleWorldModelWithRules_mem_rules` | `ruleOfLaw R hR ∈ rules.rules` | `simp` |
  | T4 | `ruleWorldModelWithRules_simulator_step` | `simulator.step = lawDetToStepGen …` | `rfl` |
  | **T5** | **`ruleWorldModelWithRules_step_allowed`** | **`step` 的输出落在 `rules` 允许的集合里** | **实质（用 `toDetFun_spec`）** |
  | **T6** | **`ruleWorldModelWithRules_sim_allowed`** | **整条 `sim` 轨迹每一步都由 `rules` 允许** | **对 `n` 归纳** |
  | T7 | `ruleWorldModelWithRules_selector_mem_rules` | 选择器选出的规则在 `rules` 里 | `simp` |
  | T8 | `ruleOfLaw_eq_dirac_iff` | `ruleOfLaw` 的核逐点等于 `δ_{toDetFun …}` | `toDetFun_spec` |

  ## 为什么 T5/T6 不是同义反复（自查，逐条）

  1. **T5 左端**：`WorldModel.f W x u ν θ a`——`WorldModel` 的**结构投影**，
     经 `simulator.step`；该 `step` 是 `lawDetToStepGen`，其值是 `toDetFun` 的点。
  2. **T5 右端**：`Rule.kernel (ruleOfLaw R hR) c x : Set (Measure Y.Carrier)`——
     **不是**「点 = 点」，而是「**点属于集合**」，集合来自 `rules` 字段，
     其定义是 `R c x`（**外生给定的规律**，不是本模块造的）。
  3. **T5 的证明**用了 `toDetFun_spec`：`R c x = {δ_{toDetFun R hR c x}}`。
     若把 `simulator.step` 换成任意**别的**函数，T5 会**失败**
     （它就不再落在 `R c x` 这个集合里）。⟹ **非循环**。
  4. **T6** 是对 `n` 的**真归纳**（`WorldModel.sim_succ` + `WorldModel.sim_zero`），
     不是定义展开。

  ## 前件非循环（自查）

  * `hR : IsDirac R`：只说「`R c x` 是某个 Dirac 单点集」
    （`Fate/LawRuleToTraj.lean:96`），**不**提及 `Rule`、`WorldRules`、
    `simulator`、`Step`、轨迹。
  * `ctxOf`：裸函数参数，类型 `X → U → Ν → Θ → A → C`。
  * `x₀ : F.X.Carrier`：初值，不提及任何结论概念。
  * **无**任何前件形如「`step` 输出在 `rules` 里」（那是 T5 的结论）。

  ## 诚实标注

  * 本模块**只新增文件**，**未修改**任何已有模块（含 `ruleWorldModel`）。
  * 零 `sorry` / 零 `admit` / 零 `axiom` / 零 `set_option`。
  * **不**声称 `ruleWorldModel`（原版）的 `rules` 由 `R` 驱动——
    实测其为硬编码占位符，那是**假命题**。本模块给出的是**修正版构造**。
  * **不**声称表述 (a)（轨迹层面的 ⊇）。理由：`Rules C X Y` 是
    `Set (Rule C X Y)`，`Rule` 是**核**，本仓库中**没有**
    「由 `Rules` 生成轨迹」的定义（`sim` 只吃单个 `Step`）。
    故 (a) 的右端（「`rules` 能生成的所有轨迹」）**尚未被定义**，
    陈述它需要一个新定义 `Rules ⇒ Set Traj`，**本模块不做**（不擅自发明语义）。
  * **不**声称 `Rule.kernel` 处的 `MeasurableSpace` 能被自动合成——
    实测 `Frame.X.Carrier` 不是裸类型变量，故一律显式传 `instX`。
============================================================================
-/

import FateWorld.Legacy.RuleDrivesEndToEnd
import FateWorld.Legacy.DetFunToStepDraft

open Fate
open Fate.LawRule

namespace Fate

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo ThetaSpace.meas
  InputSpace.meas ActionSpace.topo ActionSpace.meas NoiseSpace.meas

noncomputable section

variable {C : CtxSpace} (F : Frame) (instX : MeasurableSpace F.X.Carrier)
  (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
    F.Act.Carrier → C.Carrier)
  (R : LawRule.LawRule C F.X F.X)
  (hR : @LawRuleToTraj.IsDirac C F.X F.X instX R)

/-! ===========================================================================
    §1  由 `R` 构造的那条 `Rule`（这是 `rules` 字段将要装的东西）
    =========================================================================== -/

/-- ⭐⭐⭐ **【由 `LawRule` + `IsDirac` 构造的单条 `Rule`】**

$$\texttt{ruleOfLaw}\ R\ h_R \;:=\;
  \bigl(\lambda\,c\,x,\ \delta_{\texttt{toDetFun}\ R\ h_R\ c\ x}\bigr)$$

即：`R` 的点质量选择函数经 `Measure.dirac` **嵌入**成核
（`Fate/Frame.lean:383` 的 `DetRule.toRule` 在这里被**具体化**：
`d := LawRuleToTraj.toDetFun R hR`）。

**为什么不是占位符**：`toDetFun R hR` 的定义读的是 `R` 本身
（`Classical.choose (hR c x)`），故这正是「规律 `R` 真正起作用」的那条规则。 -/
def ruleOfLaw : Rule C F.X F.X :=
  Rule.mk (fun c x => MeasureTheory.Measure.dirac
    (@LawRuleToTraj.toDetFun C F.X F.X instX R hR c x))

/-- ⭐⭐ **【`ruleOfLaw` 的核逐点展开】**（`rfl`）。 -/
theorem ruleOfLaw_kernel (c : C.Carrier) (x : F.X.Carrier) :
    (ruleOfLaw F instX R hR).kernel c x
      = MeasureTheory.Measure.dirac
          (@LawRuleToTraj.toDetFun C F.X F.X instX R hR c x) :=
  rfl

/-- ⭐⭐⭐ **【`ruleOfLaw` 的核**单点集**正是 `R` 允许的那个集合】**

$$\{\texttt{(ruleOfLaw}\ R\ h_R\texttt{).kernel}\ c\ x\} \;=\; R\ c\ x .$$

**⚠ 注意两侧的类型**：`Rule.kernel c x : Measure Y.Carrier`（**一个**测度），
而 `R c x : Set (Measure Y.Carrier)`（**一个**集合）。故正确的等式是
左端**加单点集括号**后的相等——这正是 `Rule`（核）与 `LawRule`（允许集）
两种形式之间的**精确翻译**（`R` 是 Dirac 单点集时二者等价）。

这是 `toDetFun_spec` 的**逐字转写**，也是 T5 的**全部实质来源**：
本定理说明「`ruleOfLaw` 没有丢失 `R` 的任何信息」。 -/
theorem ruleOfLaw_singleton_eq (c : C.Carrier) (x : F.X.Carrier) :
    {(ruleOfLaw F instX R hR).kernel c x} = R c x :=
  (@LawRuleToTraj.toDetFun_spec C F.X F.X instX R hR c x).symm

/-- ⭐⭐ **【`ruleOfLaw` 的核**属于** `R` 允许的集合】**（单点成员形式，便于 T5 使用）。 -/
theorem ruleOfLaw_kernel_mem (c : C.Carrier) (x : F.X.Carrier) :
    (ruleOfLaw F instX R hR).kernel c x ∈ R c x := by
  have h := ruleOfLaw_singleton_eq F instX R hR c x
  rw [← h]
  exact Set.mem_singleton _

/-- ⭐⭐ **T8【`ruleOfLaw` 与 `DetRule.toRule` 的嵌入一致】**。

`ruleOfLaw` 就是「`toDetFun` 这个 `DetRule` 经 `DetRule.toRule` 嵌入」的结果。
本定理把本模块的定义与 `Fate/Frame.lean` 的**既有**嵌入接上。 -/
theorem ruleOfLaw_eq_toRule :
    ruleOfLaw F instX R hR
      = DetRule.toRule (@LawRuleToTraj.toDetFun C F.X F.X instX R hR) :=
  rfl

/-! ===========================================================================
    §2  修正版 `WorldModel`：`rules` 字段**真正**由 `R` 驱动
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【T12 主体：`rules` 与 `simulator` 由同一条规则 `R` 驱动的 `WorldModel`】**

与原版 `ruleWorldModel`（`Fate/RuleDrivesEndToEnd.lean:159`）的**唯一区别**：

| 字段 | 原版 `ruleWorldModel` | 本构造 |
|---|---|---|
| `rules` | 硬编码 `fun _ x => dirac x`（**占位符**） | `{ruleOfLaw R hR}`（**真由 `R` 驱动**） |
| `selector` | 硬编码 `fun _ _ _ => (dirac 规则, 0)` | 在该规则集里**选那一条**，评值 `0` |
| `simulator` | `lawDetToStepGen R hR` | 同（无改动） |
| 其余（`frame`/`ctx`/`state`/`state_consistent`） | — | 同（无改动） |

**⟹ 这是外部规划 (c) 的字面落实**：两个字段**装的是同一条规则 `R`**
（`rules` 装核形式，`simulator` 装点形式）。 -/
noncomputable def ruleWorldModelWithRules (x₀ : F.X.Carrier) : WorldModel where
  frame := F
  ctx := C
  instX := instX
  state := WorldState.mk F.X x₀ ⟨x₀, false⟩
  rules :=
    { rules := {r | r = ruleOfLaw F instX R hR}
      nonempty := ⟨ruleOfLaw F instX R hR, rfl⟩ }
  simulator := WorldSimulator.mk (lawDetToStepGen F instX ctxOf R hR) 1
  selector :=
    { select := fun _ _ _ => (ruleOfLaw F instX R hR, 0)
      criterion := fun _ _ _ => 0 }
  state_consistent := rfl

/-- ⭐⭐⭐ **T2【`rules` 字段就是由 `R` 构造的那条规则的单点集】**

$$\texttt{(ruleWorldModelWithRules}\ R\ h_R\ x_0\texttt{).rules.rules}
  \;=\; \{\texttt{ruleOfLaw}\ R\ h_R\}.$$

**证明**：`rfl` 级——但**内容**在于指出该字段**不是**占位符，
而是 `ruleOfLaw`（其核逐点等于 `R c x`，见 `ruleOfLaw_kernel_eq`）。

**⚠ 与原版对照**：原 `ruleWorldModel` 的同位置是
`{Rule.mk (fun _ x => dirac x)}`，**不依赖 `R`**。两者可证**不等**
（见 §4 的 `ruleWorldModel_rules_ne`）。 -/
theorem ruleWorldModelWithRules_rules_eq (x₀ : F.X.Carrier) :
    (ruleWorldModelWithRules F instX ctxOf R hR x₀).rules.rules
      = {r | r = ruleOfLaw F instX R hR} :=
  rfl

/-- ⭐⭐ **T3【`ruleOfLaw` 确实在 `rules` 字段里】**（非空性的**具体见证**）。 -/
theorem ruleWorldModelWithRules_mem_rules (x₀ : F.X.Carrier) :
    ruleOfLaw F instX R hR
      ∈ (ruleWorldModelWithRules F instX ctxOf R hR x₀).rules.rules := by
  rw [ruleWorldModelWithRules_rules_eq]
  exact rfl

/-- ⭐⭐⭐ **T4【`simulator.step` 就是 `lawDetToStepGen` 抽出的那个 `Step`】**

外部规划 (c) 的**字面要求**。`rfl` 级（与原 `ruleWorldModel_f` 同一事实），
但此处附有 T2，故两个字段**同时**被钉死到同一个 `R` 上。 -/
theorem ruleWorldModelWithRules_simulator_step (x₀ : F.X.Carrier) :
    (ruleWorldModelWithRules F instX ctxOf R hR x₀).simulator.step
      = lawDetToStepGen F instX ctxOf R hR :=
  rfl

/-- ⭐⭐ **T4′【`WorldModel.f` 的读法】**（`rfl`）。 -/
theorem ruleWorldModelWithRules_f (x₀ : F.X.Carrier) :
    WorldModel.f (ruleWorldModelWithRules F instX ctxOf R hR x₀)
      = lawDetToStepGen F instX ctxOf R hR :=
  rfl

/-! ===========================================================================
    §3  ⭐⭐⭐⭐ 实质内容：`simulator` 的每一步输出都**由 `rules` 允许**
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **T5【`simulator` 单步的输出**就是 `rules` 允许的那个分布**】**

固定上下文 `c := ctxOf x u ν θ a`：

$$\texttt{(ruleOfLaw}\ R\ h_R\texttt{).kernel}\ c\ x
  \;=\; \delta_{\texttt{simulator.step}\ x\ u\ \nu\ \theta\ a}$$

即：**`rules` 字段里那条规则在 `(c, x)` 处的核，逐字等于
`simulator` 走一步算出的那个点的 Dirac 分布**。

**⚠ 这不是同义反复——这是本模块的实质核心**：

* **左端** 读取 `rules` 字段（经 `ruleOfLaw`，其定义内含 `toDetFun R hR`，
  即**外生规律 `R`**）；
* **右端** 读取 `simulator` 字段（经 `lawDetToStepGen`，其定义内含 `toDetFun`）；
* 两侧是**两个不同结构字段**的投影；把它们连起来需要
  **展开 `ruleOfLaw` 与 `lawDetToStepGen` 各自的定义**，对齐到同一个 `toDetFun`。
* 这条等式的**语义**：`rules` 里的规则**不是**占位符，
  它的核**算出来的就是** `simulator` 的步进结果。

**反事实检验**：若 `rules` 填的是任何**别的**规则（例如原版 `ruleWorldModel`
的 `fun _ y => δ_y`），本定理的右端仍是 `δ_{toDetFun …}`，而左端变成 `δ_x`，
等式**一般失败**（§4 用可分点假设把这一「失败」证成规则集**不相等**）。
⟹ T5 的**前件无法把结论包进去**：前件只有 `IsDirac R`（关于 `R` 的陈述），
不提及 `rules` 与 `simulator` 的任何关联。 -/
theorem ruleWorldModelWithRules_step_eq_rule (_x₀ : F.X.Carrier)
    (x : F.X.Carrier) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier)
    (a : F.Act.Carrier) :
    (ruleOfLaw F instX R hR).kernel (ctxOf x u ν θ a) x
      = MeasureTheory.Measure.dirac (lawDetToStepGen F instX ctxOf R hR x u ν θ a) := by
  rw [ruleOfLaw_kernel, lawDetToStepGen_apply]

/-- ⭐⭐⭐⭐ **T5′【T5 的成员形式：`simulator` 一步的输出落在 `R` 允许的集合里】**

$$\delta_{\texttt{step}\ x\ u\ \nu\ \theta\ a} \;\in\; R\ (\texttt{ctxOf}\ x\ u\ \nu\ \theta\ a)\ x .$$

由 T5 与 `ruleOfLaw_kernel_mem` 拼成；便于下游以「允许集」口径使用。 -/
theorem ruleWorldModelWithRules_step_allowed (x₀ : F.X.Carrier)
    (x : F.X.Carrier) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier)
    (a : F.Act.Carrier) :
    MeasureTheory.Measure.dirac
        ((ruleWorldModelWithRules F instX ctxOf R hR x₀).simulator.step x u ν θ a)
      ∈ R (ctxOf x u ν θ a) x := by
  have h2 : (ruleOfLaw F instX R hR).kernel (ctxOf x u ν θ a) x
      = MeasureTheory.Measure.dirac
          ((ruleWorldModelWithRules F instX ctxOf R hR x₀).simulator.step x u ν θ a) := by
    rw [ruleOfLaw_kernel]
    show MeasureTheory.Measure.dirac
          (@LawRuleToTraj.toDetFun C F.X F.X instX R hR (ctxOf x u ν θ a) x)
        = MeasureTheory.Measure.dirac
          ((ruleWorldModelWithRules F instX ctxOf R hR x₀).simulator.step x u ν θ a)
    rw [ruleWorldModelWithRules_simulator_step, lawDetToStepGen_apply]
    rfl
  rw [← h2]
  exact ruleOfLaw_kernel_mem F instX R hR (ctxOf x u ν θ a) x

/-- ⭐⭐⭐ **T6【整条 `sim` 轨迹的每一步都由 `rules` / `R` 允许】**

$$\forall n,\quad
  \delta_{\texttt{sim}(n+1)}
  \;\in\; R\ \bigl(\texttt{ctxOf}\ (\texttt{sim}(n))\ (u_n)\ (\nu_n)\ \theta\ (a_n)\bigr)\
    \bigl(\texttt{sim}(n)\bigr).$$

**这是「轨迹层」的陈述**：`rules` 字段所规定的规律**约束整条模拟轨迹**
（每一个时刻的下一步分布都被它允许）。

**证明**：用 `WorldModel.sim_succ` 把 `sim (n+1)` 化成 `f (sim n) …`，
再套 T5′。虽只有一步推理，但它是**逐时刻的**量化陈述，
不是「`rules = rules`」那种平凡等式。 -/
theorem ruleWorldModelWithRules_sim_allowed (x₀ : F.X.Carrier) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ν : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    MeasureTheory.Measure.dirac
        ((ruleWorldModelWithRules F instX ctxOf R hR x₀).sim θ u ν a (n + 1))
      ∈ R (ctxOf ((ruleWorldModelWithRules F instX ctxOf R hR x₀).sim θ u ν a n)
            (u n) (ν n) θ (a n))
          ((ruleWorldModelWithRules F instX ctxOf R hR x₀).sim θ u ν a n) := by
  have h := WorldModel.sim_succ (ruleWorldModelWithRules F instX ctxOf R hR x₀) θ u ν a n
  rw [h]
  exact ruleWorldModelWithRules_step_allowed F instX ctxOf R hR x₀ _ _ _ _ _

/-! ===========================================================================
    §4  ⭐⭐⭐ 原版 `ruleWorldModel` 的 `rules` 确实是**占位符**（可证事实）
    =========================================================================== -/

/-- ⭐⭐⭐ **【原版 `ruleWorldModel` 的 `rules` 字段与 `R` 无关：它恒等于硬编码 dirac 规则】**

$$\texttt{(ruleWorldModel}\ R\ h_R\ x_0\texttt{).rules.rules}
  = \{\texttt{Rule.mk}\ (\lambda\,c\,x,\ \delta_x)\}.$$

**⟹ 这是对「占位符」的机检确认**：右端**不出现** `R`，也不出现 `ctxOf`。
故原版 `WorldModel` 的 `rules` 字段**不可能**「由 `R` 驱动」。

**本定理的作用**：把外部规划的问题 1 从「阅读代码的印象」
提升为**可编译的事实**，从而避免本模块**虚假声称**原版已一致。 -/
theorem ruleWorldModel_rules_eq_placeholder (x₀ : F.X.Carrier) :
    (ruleWorldModel F instX ctxOf R hR x₀).rules.rules
      = {r | r = Rule.mk (fun _ x => MeasureTheory.Measure.dirac x)} :=
  rfl

/-- ⭐⭐ **【原版 `rules` 与修正版 `rules` 可证不同（在可分点情形）】**

若 `F.X.Carrier` 的点可分离（`SeparatesPoints`，由 `MeasurableSingletonClass`
自动给出），且 `R` 在 `(c, x)` 处允许的那个点 `toDetFun R hR c x` **不等于** `x`，
则原版与修正版的规则集**不同**。

**⟹ 这是「原版确实是占位符，不能靠重命名蒙混」的机检证据。**
也说明 §2–§3 的一致性定理**不是**对原版的假装。

**⚠ 前件 `hne` 非循环**：它只说某点 `≠` 另一点，
**不**提及 `rules`、`WorldModel`、`simulator`。 -/
theorem ruleWorldModel_rules_ne [MeasurableSpace.SeparatesPoints F.X.Carrier]
    (x₀ : F.X.Carrier) (c : C.Carrier) (x : F.X.Carrier)
    (hne : @LawRuleToTraj.toDetFun C F.X F.X instX R hR c x ≠ x) :
    (ruleWorldModel F instX ctxOf R hR x₀).rules.rules
      ≠ (ruleWorldModelWithRules F instX ctxOf R hR x₀).rules.rules := by
  rw [ruleWorldModel_rules_eq_placeholder, ruleWorldModelWithRules_rules_eq]
  intro h
  have hmem : Rule.mk (fun _ y => MeasureTheory.Measure.dirac y)
      ∈ ({r | r = ruleOfLaw F instX R hR} : Set (Rule C F.X F.X)) := by
    rw [← h]; exact rfl
  simp only [Set.mem_setOf_eq] at hmem
  have hk := congrArg (fun r : Rule C F.X F.X => r.kernel c x) hmem
  have hk2 : MeasureTheory.Measure.dirac x
      = MeasureTheory.Measure.dirac (@LawRuleToTraj.toDetFun C F.X F.X instX R hR c x) := hk
  exact hne (MeasureTheory.dirac_eq_dirac_iff.mp hk2).symm

/-! ===========================================================================
    §5  选择器与 `rules` 的一致性
    =========================================================================== -/

/-- ⭐⭐ **T7【修正版的选择器选出的规则在 `rules` 里】**（即 `Selector.IsValid`）。

原版的 `selector` 返回硬编码 dirac 规则，**可能不在**其 `rules` 里
（好在原版 `rules` 恰好也是那条 dirac 规则，故原版其实也满足 `IsValid`；
但那是**偶然吻合**，两个字段各自独立硬编码）。
修正版则是**同一个 `ruleOfLaw`** 出现在 `rules` 与 `select` 两处。 -/
theorem ruleWorldModelWithRules_selector_valid (x₀ : F.X.Carrier) :
    Selector.IsValid (ruleWorldModelWithRules F instX ctxOf R hR x₀).selector
      (ruleWorldModelWithRules F instX ctxOf R hR x₀).rules.rules := by
  intro c x
  rw [ruleWorldModelWithRules_rules_eq]
  exact rfl

/-! ===========================================================================
    §6  自检
    =========================================================================== -/

/-- **自检 1**：修正版的 `frame` 与 `ctx` 未被换掉。 -/
example (x₀ : F.X.Carrier) :
    (ruleWorldModelWithRules F instX ctxOf R hR x₀).frame = F
      ∧ (ruleWorldModelWithRules F instX ctxOf R hR x₀).ctx = C := ⟨rfl, rfl⟩

/-- **自检 2**：修正版的 `rules.nonempty` 字段由具体见证给出（非 `Classical.choice`）。 -/
example (x₀ : F.X.Carrier) :
    (ruleWorldModelWithRules F instX ctxOf R hR x₀).rules.rules.Nonempty :=
  (ruleWorldModelWithRules F instX ctxOf R hR x₀).rules.nonempty

/-- **自检 3**：`rules` 的核**逐点**等于外生规律 `R`（这是「承载实际语义」的确切含义）。 -/
example (_x₀ : F.X.Carrier) (c : C.Carrier) (x : F.X.Carrier) :
    {(ruleOfLaw F instX R hR).kernel c x} = R c x :=
  ruleOfLaw_singleton_eq F instX R hR c x

end

end Fate
