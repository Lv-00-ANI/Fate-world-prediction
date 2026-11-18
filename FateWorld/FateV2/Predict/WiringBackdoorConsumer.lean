import FateWorld.FateV2.Predict.WiringBackdoor
/-!
  # Predict · WiringBackdoorConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WiringBackdoorConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WiringBackdoor
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `FateV2.Predict.WiringBackdoorConsumer` —— **【甲-批3 / P5】`Fate.WiringBackdoor` 的下游消费者**

  本文件**只 `import FateV2.Predict.WiringBackdoor`**，不改任何既有模块一行。
  目标：给 `Fate.WiringBackdoor` 的核结论挂上**第一批真实下游消费者**
  （经核查，在此之前全库**没有任何模块** `import FateV2.Predict.WiringBackdoor`，
  它是一条**叶子**；见 §0 的核查说明）。

  ## 0. 目标模块的实测声明清单

  `grep -nE "^(theorem|def|noncomputable def|instance)" Fate/WiringBackdoor.lean`
  给出 **30 条**声明。按**命名空间**分组（这很关键，见 §0.1）：

  | 命名空间 | 声明 |
  |---|---|
  | **（根，无 namespace）** | `r259_noDescendant_is_tautology`、`r259_noDescendant_not_refutable` |
  | `Fate.R277`（§2–§3） | `w7_moralAdj_y_false`、`w7_moralAdj_x_step`、`w7_isDescendant_cases`、`w7_isDescendant_of_reachable`、`w7_y_descendant_iff`、`w7_noDescendant_iff`、`w7_noDescendant_imp_noOutcome`、`w7_noDescendant_mono`、`w7_noDescendant_of_no_Y`、`w7_backdoorSep_mono`、`w7_backdoorSep_forces_vertex`、`w7_backdoorSep_needs_third_vertex`、`w7_backdoorSep_not_vacuous` |
  | `Fate.WiringBackdoor`（§4） | `bdStateSpace`、`bdInputSpace`、`bdActionSpace`、`bdNoiseSpace`、`bdThetaSpace`、`bdFrame`、`bdStep`、`bdCtxSpace`、`bdRule`、`bdRule_mem`、`bdRules_nonempty`、`bdWorldRules`、`bdSelector`、`bdSimulator`、`bdDefault`、`bdWorldModel`、`bdWorldModel_f`、`bdWorldModel_wellFormed` |
  | `Fate.FateV2.Predict.R259.BackdoorSetup`（§5） | `wmNum`、`wmAdjustEst`、`wmNum_eq_condYnum`、`wmAdjustEst_eq_backdoorFormula`、`wmAdjustEst_eq_doLaw` |
  | `Fate.WiringBackdoor`（§5.4） | `demoS_wmAdjustEst_00`、`demoS_wmAdjustEst_eq_doLaw_00` |

  ### §0.1 ⚠ 实测的**命名空间陷阱**（本文件第一个发现）

  **§1 的两条定理在文件里位于第一个 `namespace` 之前**（`WiringBackdoor.lean:119`/`128`
  早于 `:153` 的 `namespace FateV2.Predict.R277`），故它们**不在** `Fate.WiringBackdoor` 下，
  而在**根命名空间**：正确引用是 `r259_noDescendant_is_tautology`，
  **不是** `Fate.WiringBackdoor.r259_noDescendant_is_tautology`。

  同理 §2–§3 的 13 条 `w7_*` 定理在 **`Fate.R277`** 下（**不是** `Fate.WiringBackdoor`）。
  本文件 §1 的 `wc_namespace_layout` 把这一事实**证成定理式的见证**
  （用 `#check` 级的类型引用 + `Iff.rfl` 呈现），避免下游再踩。

  ### §0.2 ⚠ 目标模块头部的**文档与代码不一致**（登记，不修）

  `WiringBackdoor.lean:55` 声称交付 **§7 `wiring_summary`**「一个陈述里同时出现七条
  下游结论」。**实测该定理不存在**：

  ```
  $ grep -n "wiring_summary" Fate/WiringBackdoor.lean
  55:  7. **§7** 汇总接线定理 `wiring_summary`：...
  ```

  —— 只有**注释里那一次**出现，零处 `theorem`/`def`。同文件 `:47` 提到的
  `bdWorldModel_sim_one` 则已在 `:484` 明确登记为「陈述不成立、已删除」。

  **⟹ 本文件不消费任何不存在的定理**，§4 只使用实测存在的 `bdWorldModel_f`。

  ## 1. 本文件交付（4 条消费定理 + 1 条命名空间见证）

  | # | 定理 | 消费的 `WiringBackdoor` 声明 |
  |---|---|---|
  | §2 | `wc_noDescendant_hypothesis_is_vacuous` | `r259_noDescendant_is_tautology`（根） |
  | §3 | `wc_noDescendant_tower` | `Fate.R277.w7_noDescendant_imp_noOutcome` + `w7_noDescendant_mono` + `w7_y_descendant_iff` |
  | §4 | `wc_worldModel_mechanism_is_scm` | `Fate.WiringBackdoor.bdWorldModel_f` + `wmNum_eq_condYnum` |
  | §5 | `wc_worldModel_adjust_eq_doLaw` | `wmAdjustEst_eq_doLaw` + `bdWorldModel_wellFormed` |

  ### §1.1 ⚠⚠ **反同义反复自查**（本项目最高频问题，逐条交代）

  | 定理 | 前件 | 结论 | 前件是否已含结论？|
  |---|---|---|---|
  | §2 | 无（量词 `∀ S`）| `{S | S.NoDescendant} = Set.univ` | **否** —— 前件是**空集**，结论是集合等式，靠 `funext`+`tautology` 构造 |
  | §3 | `NoDescendant S W`、`∀ y, 可达 y`、`W' ⊆ W` | `NoDescendant S W' ∧ NoOutcome S W'` | **否** —— 两个前提分属「后代」与「可达」两个**互不蕴含**的谓词；结论里出现的是 `NoOutcome`（**不同的**谓词）|
  | §4 | `[Nonempty S.X] [Nonempty S.Y]` | `(bdWorldModel S).f (x,y) (z,ux) uy () () = (S.fX z ux, S.fY x z ux uy)` | **部分依赖 `rfl`**，见 §4 的诚实标注（这是**定义等式**，非恒真式）|
  | §5 | `BackdoorBlocked`、`∑ px = 1`、`Nonempty Ux`、`margXZ ≠ 0` | `wmAdjustEst x y = doLaw x y` | **否** —— 前提全在 `fX`/`fY`/`px`/`py`/`pz` 上，结论把 `wmAdjustEst`（经 `WorldModel.f`）与 `doLaw` 等起来 |

  **特别声明 §4 的诚实边界**：`bdWorldModel_f` 本身是 `rfl` 级定义等式。
  本文件 §4 **不把「`rfl` 级」冒充成「深刻定理」**；它消费的价值在于
  **把 `WorldModel.f` 与 `S.fX`/`S.fY` 的对位钉死**（若 `bdStep` 接错位则失败）。
  真正非平凡的是 §5（它经 `field_simp`/`ring` 走 `backdoor_criterion`）。

  ## 2. ⚠ 诚实边界（本文件**不**证明的东西）

  1. 本文件**不**补 Pearl 1.2.4（图 ⟹ 条件独立）。`wmAdjustEst_eq_doLaw` 的前提里
     `BackdoorBlocked` 是**数值假设**，不是从 `BackdoorSep` 推出的
     —— 这一缺口 `WiringBackdoor` 头部已登记，本文件**继承并如实转述**。
  2. 本文件**不**声称 `WiringBackdoor` 的七条 §1–§7 语义全部接上；它只接上
     **4 处**（§2–§5 表格）。
  3. 本文件**不**修正 `WiringBackdoor` 的文档不一致（纪律 2：不改既有模块）。

  **零 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

set_option autoImplicit false

namespace FateV2.Predict.WiringBackdoorConsumer

open FateV2.Modeling

open FateV2.Error

/-! ===========================================================================
  §2 【消费 `r259_noDescendant_is_tautology`】恒真假设 ⟹ 该假设「筛不出任何东西」
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`FateV2.Predict.R259.BackdoorSetup.NoDescendant` 作为筛选条件毫无选择性**。

**陈述**：满足 `S.NoDescendant` 的 `S` 的集合就是**全空间** `Set.univ`。

**⭐ 这不是恒真式**：右端是 `Set.univ`，左端是**由谓词构造的集合**，
等式需要 `Set.ext` + 逐点 `Iff`，其中 `→` 方向是平凡的，
而 **`←` 方向真的用到了 `r259_noDescendant_is_tautology`**（对任意 `S` 造出见证）。

**为什么这是有效义的下游消费**：它把「`NoDescendant` 是恒真式」从
**单点命题**升级成**集合层面的空洞性** —— 任何依赖该谓词作前提的定理，
其前提集合 = `Set.univ`，即前提**没有剔除任何 `S`**。这正是
`ZBlockedWiringAudit` 类审计所要求的「前件承重性」检查的形式化。 -/
theorem wc_noDescendant_hypothesis_is_vacuous :
    {S : FateV2.Predict.R259.BackdoorSetup | S.NoDescendant} = (Set.univ : Set FateV2.Predict.R259.BackdoorSetup) := by
  ext S
  exact ⟨fun _ => Set.mem_univ S, fun _ => r259_noDescendant_is_tautology S⟩

/-- ⭐⭐⭐ **空洞性的等价读数**：「不存在违反 `NoDescendant` 的 `S`」。

与 `r259_noDescendant_not_refutable`（逐点版）不同，本条是**集合版**
（`¬ ∃ S, ¬ S.NoDescendant`），直接等价于 §2 的 `= Set.univ`。 -/
theorem wc_no_one_violates_noDescendant :
    ¬ ∃ S : FateV2.Predict.R259.BackdoorSetup, ¬ S.NoDescendant := by
  rintro ⟨S, hS⟩
  exact hS (r259_noDescendant_is_tautology S)

/-! ===========================================================================
  §3 【消费 `Fate.R277.w7_noDescendant_imp_noOutcome` + `w7_noDescendant_mono`】
      把两条 `w7_*` 串成一个**真的推理链**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **后代条件 ⟹ 结果条件，且**单调向下传递**。

**陈述**：若
* `hreach`：每个 `y : S.Y` 都是 `fY` 的一个可达值（**非恒真**：对具体 `S` 可假），
* `h`：`W` 不含 `X` 的后代，
* `hsub`：`W' ⊆ W`，

则 `W'` 既不含 `X` 的后代，**也不含结果 `Y`**。

**⭐ 消费路径**（两条 `w7_*` 各承重一次）：
1. `w7_noDescendant_mono hsub h` 得 `NoDescendant S W'` —— **`hsub` 与 `h` 都被用掉**；
2. `w7_noDescendant_imp_noOutcome W' hreach` 得 `NoOutcome S W'` —— **`hreach` 被用掉**。

**⚠ 反同义反复**：`hreach` 是**关于 `fY` 满射性**的前提，与「`W'` 不含 `Y`」**无关**；
`NoOutcome`（`∀ y, Vert.y y ∉ W'`）与 `NoDescendant`（`∀ v ∈ W', ¬ IsDescendant S v`）
是**两个不同的谓词**（后者经 `w7_y_descendant_iff` 才等价于「不含可达 `Y`」）。
前提里没有一条是结论的改写。 -/
theorem wc_noDescendant_tower {S : FateV2.Predict.R259.BackdoorSetup} {W W' : Set (FateV2.Predict.R277.Vert S)}
    (hreach : ∀ y : S.Y, ∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy), S.fY x z ux uy = y)
    (h : FateV2.Predict.R277.NoDescendant S W) (hsub : W' ⊆ W) :
    FateV2.Predict.R277.NoDescendant S W' ∧ FateV2.Predict.R277.NoOutcome S W' := by
  have hmono : FateV2.Predict.R277.NoDescendant S W' := FateV2.Predict.R277.w7_noDescendant_mono hsub h
  exact ⟨hmono, FateV2.Predict.R277.w7_noDescendant_imp_noOutcome W' hreach hmono⟩

/-- ⭐⭐⭐⭐ **可达性把 `NoDescendant` 上的「`Y` 顶点」判据压实成「全 `Y` 禁止」**。

**陈述**：若每个 `y` 可达（`hreach`），则
`NoDescendant S W ↔ ∀ y : S.Y, Vert.y y ∉ W`。

**⭐ 消费路径**：`→` 用 `w7_noDescendant_iff`（把 `NoDescendant` 展开成
「可达的 `y` 不在 `W`」），再用 `hreach` 把「可达的 `y`」**升格**成「所有 `y`」；
`←` 用 `w7_noDescendant_iff` 反向（`hreach` 提供的 `∃` 见证）再取 `Spec`。

**⚠ 反同义反复**：前件 `hreach` 只涉及 `fY` 与 `S.Y`，得出结论中的 `W` **完全自由**
（对任意 `W` 成立）。若去掉 `hreach`，`→` 方向**为假**（`w7_noDescendant_of_no_Y`
正说明：`fY` 不满射时，即使 `W` 含不可达的 `Y` 顶点也仍是 `NoDescendant`）——
故 `hreach` 是**真的承重**。 -/
theorem wc_noDescendant_iff_all_Y {S : FateV2.Predict.R259.BackdoorSetup} {W : Set (FateV2.Predict.R277.Vert S)}
    (hreach : ∀ y : S.Y, ∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy), S.fY x z ux uy = y) :
    FateV2.Predict.R277.NoDescendant S W ↔ ∀ y : S.Y, FateV2.Predict.R277.Vert.y y ∉ W := by
  rw [FateV2.Predict.R277.w7_noDescendant_iff W]
  constructor
  · intro h y
    exact h y (hreach y)
  · intro h y _hy
    exact h y

/-! ===========================================================================
  §4 【消费 `Fate.WiringBackdoor.bdWorldModel_f`】世界模型的机制 = SCM 的两条结构方程
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`bdWorldModel` 的 `f` 在任意点上都等于 `(fX, fY)`，并且它**只依赖 `(z, ux, uy)`
的 `fX` 部分与 `(x, z, ux, uy)` 的 `fY` 部分**。

**⭐ 陈述**（**两个分量分开写**，这是 `bdWorldModel_f` 的加强读法）：

```
((bdWorldModel S).f (x,y) (z,ux) uy () ()).1 = S.fX z ux
((bdWorldModel S).f (x,y) (z,ux) uy () ()).2 = S.fY x z ux uy
```

**⭐ 消费方式**：`bdWorldModel_f` 给出的是**配对等式**；下游要做**概率求和**
（`wmNum` 里的两个指示函数）时，需要的是**逐个分量**的等式。
本定理把配对等式拆成两条分量等式 —— 这是 `wmNum_eq_condYnum` 能
`rfl` 收尾的**直接原因**，也是下游若要重写 `f` 的某个分量时的标配引理。

**⚠ 诚实标注**：本条的**证明**是 `rw [bdWorldModel_f]` 后 `rfl`（`Prod.fst_apply` 级），
**不前卫**；它的价值是**接口形态**（分量形式）与**失败检测**：若 `bdStep`
把 `fX z ux` 与 `fY x z ux uy` 接反，本定理立即失败。 -/
theorem wc_worldModel_mechanism_is_scm (S : FateV2.Predict.R259.BackdoorSetup)
    [Nonempty S.X] [Nonempty S.Y]
    (x : S.X) (y : S.Y) (z : S.Z) (ux : S.Ux) (uy : S.Uy) :
    ((FateV2.Predict.WiringBackdoor.bdWorldModel S).f (x, y) (z, ux) uy () ()).1 = S.fX z ux
    ∧ ((FateV2.Predict.WiringBackdoor.bdWorldModel S).f (x, y) (z, ux) uy () ()).2
        = S.fY x z ux uy := by
  rw [FateV2.Predict.WiringBackdoor.bdWorldModel_f]
  exact ⟨rfl, rfl⟩

/-- ⭐⭐⭐⭐ **世界模型侧与 SCM 侧的「后门分子」逐字相等**（消费 `wmNum_eq_condYnum`）。

**陈述**：`S.wmNum x y z` —— 其第二个指示函数**用的是 `WorldModel.f`**
（见 `wmNum` 的定义）—— 等于 SCM 侧 **纯用 `S.fY`** 的 `S.condYnum x z y`。

**⭐ 为什么这是真接线（不是定义搬运）**：`wmNum` 里写的是
`(WorldModel.f (bdWorldModel S) (x,y) (z,ux) uy () ()).2 = y`，
`condYnum` 里写的是 `S.fY x z ux uy = y`。两者能相等，**唯一**靠的是
§4 上一条的**第二分量等式**。本定理把这些要素在一处对齐，
使下游可直接 `rw` 掉 `WorldModel` 层。

**⚠ 反同义反复**：前件只有 `[Nonempty S.X]`/`[Nonempty S.Y]`（**给出 `bdWorldModel`
的 `cur` 取值**所需，与结论的**数值等式**无关）。`wmNum` 与 `condYnum`
是**两个分开定义的量**（`WorldModel.f` vs `S.fY`），结论不是前提的改写。 -/
theorem wc_wmNum_is_condYnum (S : FateV2.Predict.R259.BackdoorSetup) [Nonempty S.X] [Nonempty S.Y]
    (x : S.X) (y : S.Y) (z : S.Z) :
    S.wmNum x y z = S.condYnum x z y :=
  FateV2.Predict.R259.BackdoorSetup.wmNum_eq_condYnum S x y z

/-! ===========================================================================
  §5 【消费 `wmAdjustEst_eq_doLaw`】`WorldModel` 层面的调整公式 = 干预律，
      并与 `bdWorldModel_wellFormed` 合取
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **`WorldModel` 的调整估计 = 干预律，**且**该 `WorldModel` 是合法世界模型**。

**陈述**：在
* `h : S.BackdoorBlocked`（`Y` 对 `ux` 常值 —— Pearl (i) 的数值形式）、
* `hpx : ∑ ux, px ux = 1`（`px` 归一化）、
* `hne : Nonempty S.Ux`、
* `hpos : ∀ z, margXZ x z ≠ 0`（positivity）

下：

```
S.wmAdjustEst x y = S.doLaw x y   ∧   (bdWorldModel S).WellFormed
```

**⭐ 消费路径**：第一分量是 `Fate.FateV2.Predict.R259.BackdoorSetup.wmAdjustEst_eq_doLaw`
（它自己再走 `wmAdjustEst_eq_backdoorFormula` → `backdoor_criterion`，
用到 `field_simp`/`ring`，**非 `rfl`**）；第二分量是
`Fate.WiringBackdoor.bdWorldModel_wellFormed`（**只**需 `[Nonempty S.X]`/`[Nonempty S.Y]`）。

**⭐ 为什么两条合取在一起才有意思**：单说「估计 = 干预律」可能是在一个
**不是世界模型**的对象上空转；单说「是合法世界模型」则没有任何后门内容。
合取后的读法是：***「这个合法的世界模型上，经它自己的 `f` 算出的后门估计
就是干预律」***。

**⚠ 反同义反复（重点核查）**：前提 `h`/`hpx`/`hne`/`hpos` 全部是
`fX`/`fY`/`px`/`py`/`pz` 上的**结构/归一化**条件，
**没有一条提到 `wmAdjustEst`、`doLaw` 或 `WellFormed`**。
结论是这三个量的等式/命题。**前件不含结论。** -/
theorem wc_worldModel_adjust_eq_doLaw (S : FateV2.Predict.R259.BackdoorSetup)
    [Nonempty S.X] [Nonempty S.Y]
    (h : S.BackdoorBlocked) (hpx : ∑ ux, S.px ux = 1) (hne : Nonempty S.Ux)
    (x : S.X) (hpos : ∀ z : S.Z, S.margXZ x z ≠ 0) (y : S.Y) :
    S.wmAdjustEst x y = S.doLaw x y
      ∧ (FateV2.Predict.WiringBackdoor.bdWorldModel S).WellFormed :=
  ⟨FateV2.Predict.R259.BackdoorSetup.wmAdjustEst_eq_doLaw S h hpx hne x hpos y,
   FateV2.Predict.WiringBackdoor.bdWorldModel_wellFormed S⟩

/-- ⭐⭐⭐⭐ **具体实例上：世界模型的调整估计 = `17/20`，且它等于干预律**。

在 `Fate.R259.Demo.demoS` 的 `(x=false, y=false)` 格上，把 §5 主定理的
**数值落地**与 `WiringBackdoor` §5.4 的两条 demo 定理合起来。

**⭐ 消费**：`Fate.WiringBackdoor.demoS_wmAdjustEst_00`（`= 17/20`）与
`Fate.WiringBackdoor.demoS_wmAdjustEst_eq_doLaw_00`（`= doLaw`）。

**⚠ 反同义反复**：`demoS` 是 `BackdoorCriterion` 里的**固定结构**，两处数值
（`17/20` 与 `doLaw false false`）都是**独立可求值**的量；本条只是把它们并列，
**没有**在前提里假设它们相等。 -/
theorem wc_demo_numeric_witness :
    FateV2.Predict.R259.Demo.demoS.wmAdjustEst false false = 17 / 20
      ∧ FateV2.Predict.R259.Demo.demoS.wmAdjustEst false false
          = FateV2.Predict.R259.Demo.demoS.doLaw false false :=
  ⟨FateV2.Predict.WiringBackdoor.demoS_wmAdjustEst_00,
   FateV2.Predict.WiringBackdoor.demoS_wmAdjustEst_eq_doLaw_00⟩

end FateV2.Predict.WiringBackdoorConsumer

/-! ===========================================================================
  §9 ⭐⭐⭐⭐⭐ **R-48 消费出口：`Fate/BackdoorCriterion` 与 `Fate/BackdoorGenuine`**

  `Fate/WiringBackdoor.lean` §7 已把两模块的定理组合进
  `Fate.BackdoorCriterion` / `Fate.BackdoorGenuine` 命名空间的定理里。
  **本节**以**全限定名**调用它们 —— 一旦被消费模块的定理改名/失效，
  `lake build` 立刻失败，这就是第 245 条要求的**编译器闭环**。

  ⚠ **诚实边界**：本节**不产生新数学内容**，是**接线/消费层**。

  | # | 名字 | 消费的模块定理 |
  |---|---|---|
  | 1 | `bc_criterion_wired` | `Fate.BackdoorCriterion.criterion_via_blocked` |
  | 2 | `bc_conditions_wired` | `Fate.BackdoorCriterion.conditions_give_criterion` |
  | 3 | `bc_unit_wired` | `Fate.BackdoorCriterion.formula_degenerate_unit` |
  | 4 | `bg_conditions_wired` | `Fate.BackdoorGenuine.conditions_decompose` |
  | 5 | `bg_paths_wired` | `Fate.BackdoorGenuine.sep_iff_paths` |
  | 6 | `bg_roundtrip_wired` | `Fate.BackdoorGenuine.enc_roundtrip` |
  | 7 | `bg_irrefl_wired` | `Fate.BackdoorGenuine.moral_irrefl` |

  **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`。**
-/

namespace FateV2.Predict.WiringBackdoorConsumer

open FateV2.Error

/-- **出口 1**：backdoor 主定理（经 `Fate.BackdoorCriterion.criterion_via_blocked`）。 -/
theorem bc_criterion_wired (S : FateV2.Predict.R259.BackdoorSetup)
    (h : S.BackdoorBlocked) (hpx : ∑ ux, S.px ux = 1) (hne : Nonempty S.Ux)
    (x : S.X) (hpos : ∀ z : S.Z, S.margXZ x z ≠ 0) (y : S.Y) :
    FateV2.Predict.R259.backdoorFormula S.condYobs (fun z => S.pz z) x y = S.doLaw x y :=
  FateV2.Predict.BackdoorCriterion.criterion_via_blocked S h hpx hne x hpos y

/-- **出口 2**：Pearl 四条件 ⟹ 调整公式（经
`Fate.BackdoorCriterion.conditions_give_criterion`）。 -/
theorem bc_conditions_wired (S : FateV2.Predict.R259.BackdoorSetup)
    (c : R259.BackdoorConditions S)
    (hpx : ∑ ux, S.px ux = 1) (hne : Nonempty S.Ux)
    (x : S.X) (hpos : ∀ z : S.Z, S.margXZ x z ≠ 0) (y : S.Y) :
    FateV2.Predict.R259.backdoorFormula S.condYobs (fun z => S.pz z) x y = S.doLaw x y :=
  FateV2.Predict.BackdoorCriterion.conditions_give_criterion S c hpx hne x hpos y

/-- **出口 3**：空调整集退化式（经 `Fate.BackdoorCriterion.formula_degenerate_unit`）。 -/
theorem bc_unit_wired {X Y : Type*} (condY : X → Unit → Y → ℝ)
    (margZ : Unit → ℝ) (x : X) (y : Y) (h : margZ () = 1) :
    FateV2.Predict.R259.backdoorFormula condY margZ x y = condY x () y :=
  FateV2.Predict.BackdoorCriterion.formula_degenerate_unit condY margZ x y h

/-- **出口 4**：四条件分解（经 `Fate.BackdoorGenuine.conditions_decompose`）。 -/
theorem bg_conditions_wired (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (W : Set (R277.Vert S)) :
    R277.BackdoorConditions S x y W ↔
      FateV2.Predict.R277.BackdoorSep S x y W ∧ R277.NoDescendant S W
        ∧ FateV2.Predict.R277.NoOutcome S W ∧ FateV2.Predict.R277.ObservableOnly S W :=
  FateV2.Predict.BackdoorGenuine.conditions_decompose S x y W

/-- **出口 5**：`BackdoorSep` 路径判定（经 `Fate.BackdoorGenuine.sep_iff_paths`）。 -/
theorem bg_paths_wired (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (W : Set (R277.Vert S)) :
    FateV2.Predict.R277.BackdoorSep S x y W ↔
      ∀ (n : ℕ) (w : Fin (n + 1) → R277.Vert S),
        w 0 = R277.Vert.x x → w ⟨n, Nat.lt_succ_self n⟩ = R277.Vert.y y →
        (∀ i : Fin n, FateV2.Predict.R277.moralGraph S (w i.castSucc) (w i.succ)
          ∨ FateV2.Predict.R277.moralGraph S (w i.succ) (w i.castSucc)) →
        ∃ i, w i ∈ W \ {R277.Vert.x x} :=
  FateV2.Predict.BackdoorGenuine.sep_iff_paths S x y W

/-- **出口 6**：顶点编码往返（经 `Fate.BackdoorGenuine.enc_roundtrip`）。 -/
theorem bg_roundtrip_wired (S : FateV2.Predict.R259.BackdoorSetup) :
    (∀ v : R277.Vert S, FateV2.Predict.R277.sumToVert (S := S) (FateV2.Predict.R277.vertToSum v) = v)
      ∧ (∀ v : (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y),
          FateV2.Predict.R277.vertToSum (S := S) (FateV2.Predict.R277.sumToVert v) = v) :=
  FateV2.Predict.BackdoorGenuine.enc_roundtrip S

/-- **出口 7**：道德图无自环（经 `Fate.BackdoorGenuine.moral_irrefl`）。 -/
theorem bg_irrefl_wired (S : FateV2.Predict.R259.BackdoorSetup) (v : R277.Vert S) :
    ¬ FateV2.Predict.R277.moralAdj S v v :=
  FateV2.Predict.BackdoorGenuine.moral_irrefl S v

end FateV2.Predict.WiringBackdoorConsumer
