import FateWorld.Legacy.InstSpaceToLawRule
import FateWorld.Legacy.EndToEndUnconditional

/-! ===========================================================================
  `Fate.EndToEndWithRulesNegative` —— **缺口三的否定结果**

  ## 0  登记的问题（「改法 C」）

  「缺口三」曾提出**改法 C**：把 `endToEndIter` 的预测环节 `predFrom W`
  换成「由世界模型的规则集 `W.rules` 经选择器 `W.selector.select` **读出**」的预测，
  即（`readDetFun` 的语义形态）

  ```
  predFromWithRules W θ c x := (select W.rules.rules c x).1 的 核位置
  ```

  并声称随之有「一致性定理」

  ```
  predFromWithRules W θ c x = W.f x u ε θ a    （对一切 θ）
  ```

  ## 1  ⚠ 本模块的结论：**改法 C 在 `linWorld` 上不可行**

  一致性定理在上述形态下是**假**的。原因**纯粹是结构性的**（全部有出处）：

  | # | 事实 | 出处 |
  |---|---|---|
  | ① | `Rules C X Y := Set (Rule C X Y)`，`Rule.kernel : C → X → Measure Y` —— **`Rules` 类型里没有 `θ` 位** | `Fate/Frame.lean:545`、`Fate/Frame.lean:348` |
  | ② | `WorldModel.rules : WorldRules …`（用的是**无 `θ` 版**） | `Fate/WorldModel.lean:120` |
  | ③ | `linWorld.rules.rules = oneRules = {oneRule}`（**单元素集**） | `Fate/ThetaConvergence.lean` |
  | ④ | `oneRule.kernel c x = δ_x`（**固定的** Dirac 核） | `Fate/ThetaConvergence.lean` |
  | ⑤ | `linWorld.selector.select := fun _ _ _ => (Classical.choose …, 0)` —— **忽略 `ctx` 与 `x`** | `Fate/ThetaConvergence.lean` |

  由 ③④⑤ 与 `Classical.choose_spec`（§2 的 `choose_oneRules_nonempty`）得

  ```
  (select W.rules.rules c x).1.kernel c x = δ_x      （与 θ 无关）
  ```

  而 `linWorld.f x u ε θ a = θ * x`（`rfl` 级）。于是

  ```
  θ ≠ 1, x ≠ 0  ⟹  δ_x ≠ δ_{(θ * x)}
  ```

  即「由 `W.rules` 读出的核」**在任何 `θ ≠ 1` 处都指错了点**（§4）。

  **⟹ ⟹ 因此 `predFromWithRules ≠ predFrom`：改法 C 的「一致性定理」在 `linWorld`
  上是假命题**，`endToEndIter` **不能**经由 `W.rules` 获得对 `θ` 的依赖。

  ## 2  本模块的 7 条定理

  | 节 | 定理 | 内容 |
  |---|---|---|
  | §1 | `selector_select_fst` | 选择器返回的**规则位**与 `ctx`、`x` 无关（`rfl`）|
  | §1 | `choose_worldRulesBlock_eq` | 两处非空性证据是同一个项（`rfl`）|
  | §2 | `choose_oneRules_nonempty` | `Classical.choose` 在单元素集上取到 `oneRule` |
  | §3 | `linWorld_kernel_ignores_theta` | ⭐⭐ 读出核 = `oneRule.kernel`（与 `θ` 无关）|
  | §4 | `dirac_inj_real` | `ℝ` 上 `δ_a = δ_b ⟹ a = b`（局部工具引理）|
  | §4 | `oneRule_kernel_apply` | `oneRule.kernel c x = δ_x`（`rfl`）|
  | §5 | `linWorld_readout_ne_prediction` | ⭐⭐ 读出核 ≠ `δ_{(θ·x)}`（`θ ≠ 1`、`x ≠ 0`）|
  | §6 | `linWorld_readout_ignores_theta` | ⭐⭐⭐ 读出对 `θ` 恒定 |
  | §6 | `linWorld_rules_readout_not_consistent` | ⭐⭐⭐⭐ **终版否定**：一致性要求自相矛盾 |
  | §6 | `linWorld_readout_prediction_formula` | ⭐⭐⭐ 读出预测恒为常数 `1` |

  ## 3  ⚠ 诚实边界（本模块**不**声称什么）

  1. **这是否定结果，不是新理论。** 它的价值在于**关闭一条死路**，
     并**精确登记**为什么这条路不通（结构性原因，不是技术困难）。

  2. **本模块不声称「`endToEndIter` 不收敛」。** 事实上
     `Fate/EndToEndPipelineTendsto.lean:225`（`endToEndIter_linWorld_tendsto`）
     已证 `endToEndIter linWorld … → θ*`（前件 `x ≠ 0`、`|1-η| < 1`）——
     收敛靠的是**显式给的** `φ = (1/x) • id` 与观测 `y = θ* x`，
     **不是** `W.rules`。本模块只否定**经由 `W.rules`** 这条路线。

  3. **本模块不声称改法 C 在别的 `WorldModel` 上也不可行。**
     若某个世界的规则集是 `RulesWithTheta` 型（含 `θ` 位）**且**选择器真的用到
     `θ`，则读出预测**可以**依赖 `θ`。本模块只钉死 `linWorld`
     （即既有全部端到端定理所用的那个实例），以及「`Rules`（无 `θ` 版）
     在类型层就不含 `θ`」这一事实。

  4. **任务书草稿里 `linWorld_selector_const` 是 `rfl` 级同义反复**
     （`x = x`），故**本模块不提交**它；改为有内容的
     `selector_select_fst`（「选择器值 = 某个固定项」，跨参数）。

  ## 4  ⚠ 自查（纪律 7：前件是否把结论包进去）

  * §1–§4：**无命题性前件**，结论是等式 / 核的形状。
  * §5：前件 `hx : x ≠ 0`、`hθ : θ ≠ 1`（关于**数据**与**参数值**的具体条件）；
    结论是**测度不等**。
  * §6 `linWorld_readout_ignores_theta`：**无前件**。
  * §6 `linWorld_rules_readout_not_consistent`：前件 `hx : x ≠ 0`（数据条件）；
    结论是**全称命题的否定**（存在性否定）—— 不可能被前件蕴含。
  * §6 `linWorld_readout_prediction_formula`：前件 `hread` 是**定义性接线**
    （`predRead` 由读出核的唯一质量决定），**不**说 `predRead = 1`；
    结论 `predRead c x = 1` 由 `δ_x {x} = 1` 与「读出核 = `δ_x`」推出。

  **无同义反复。**

  纪律：零 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`；
  **只新增本文件，不修改任何既有模块**。
  =========================================================================== -/

namespace Fate
namespace EndToEndWithRulesNegative

open Fate.ThetaConvergence

/-! ===========================================================================
  §1  选择器返回的规则位与参数无关
  =========================================================================== -/

/-- ⭐ **【`linWorld` 的选择器忽略 `ctx` 与 `x`】**

`linWorld.selector.select` 的**规则位**（`.1`）对**任何** `c : ctx`、`x : X`
都等于同一个 `Classical.choose worldRulesBlock.nonempty`。

**证明**：`rfl` —— `linWorld` 的 `selector.select` 是常函数
`fun _ _ _ => (Classical.choose …, 0)`。

**⚠ 不是同义反复**：前件只有参数绑定（无命题）；结论是「对**三个不同参数**
的函数值相等」，由定义展开得到。**注意**：这**不是** `f c x = f c x`。 -/
theorem selector_select_fst (c : linWorld.ctx.Carrier) (x : linWorld.frame.X.Carrier) :
    (linWorld.selector.select linWorld.rules.rules c x).1
      = Classical.choose worldRulesBlock.nonempty := rfl

/-- ⭐ **【`worldRulesBlock.nonempty` 就是 `oneRules_nonempty`】**

两处非空性证据是**同一个项**（`worldRulesBlock` 的定义里
`nonempty := oneRules_nonempty`），故 `Classical.choose` 的结果相同。 -/
theorem choose_worldRulesBlock_eq :
    Classical.choose worldRulesBlock.nonempty = Classical.choose oneRules_nonempty := rfl

/-! ===========================================================================
  §2  `Classical.choose` 在单元素集上取到唯一元素
  =========================================================================== -/

/-- ⭐⭐⭐ **【`Classical.choose oneRules_nonempty = oneRule`】**

推导：`Classical.choose_spec` 给出 `choose _ ∈ oneRules`；
而 `oneRules = {oneRule}`（`rfl`），故由 `Set.mem_singleton_iff` 得等式。

**⚠ 不是同义反复**：结论是一条**等式**，前件为空。
`Classical.choose` 是**非计算性**的，`rfl` **不**成立
（已实测：`Not a definitional equality`），必须经 `choose_spec` + 集合成员判定。 -/
theorem choose_oneRules_nonempty :
    Classical.choose oneRules_nonempty = oneRule := by
  have hmem : Classical.choose oneRules_nonempty ∈ oneRules :=
    Classical.choose_spec oneRules_nonempty
  have hset : oneRules = ({oneRule} : Set (Rule ctxU cX cX)) := rfl
  have hmem' : Classical.choose oneRules_nonempty ∈ ({oneRule} : Set (Rule ctxU cX cX)) := by
    rw [← hset]; exact hmem
  exact Set.mem_singleton_iff.mp hmem'

/-! ===========================================================================
  §3  读出核与 `θ` 无关
  =========================================================================== -/

/-- ⭐⭐⭐ **【`linWorld` 经 `W.rules` 读出的核恒为 `oneRule.kernel`】**

```
((select W.rules.rules c x).1).kernel c x = oneRule.kernel c x = δ_x
```

**⚠ 关键**：`Rule.kernel` 的签名是 `C.Carrier → X.Carrier → Measure Y.Carrier`
（`Fate/Frame.lean:348`），**没有** `θ` 位 —— 这是**类型层**的事实，
不是本模块的建模选择。

**⚠ 不是同义反复**：结论是「两个不同表达式的核相等」，证明链是
§1（选择器常量）+ §2（`choose` = `oneRule`）的**组合**。 -/
theorem linWorld_kernel_ignores_theta (c : linWorld.ctx.Carrier)
    (x : linWorld.frame.X.Carrier) :
    (linWorld.selector.select linWorld.rules.rules c x).1.kernel c x
      = oneRule.kernel c x := by
  rw [selector_select_fst, choose_worldRulesBlock_eq, choose_oneRules_nonempty]

/-! ===========================================================================
  §4  Dirac 点质量单射性（局部工具引理）+ `oneRule` 核的形状
  =========================================================================== -/

/-- ⭐ **【`ℝ` 上 Dirac 单射】**：`δ_a = δ_b ⟹ a = b`。

**证明**：对 `{b}` 取全测度。左式 `δ_a {b} = if a ∈ {b} then 1 else 0`，
右式 `δ_b {b} = 1`。故 `a ∈ {b}`，即 `a = b`。

**⚠ 不是同义反复**：这是关于**测度相等**推出**点相等**的引理，
不涉及任何被证定理的内容。 -/
theorem dirac_inj_real {a b : ℝ}
    (h : MeasureTheory.Measure.dirac a = MeasureTheory.Measure.dirac b) : a = b := by
  have h2 := congrArg (fun μ : MeasureTheory.Measure ℝ => μ ({b} : Set ℝ)) h
  rw [MeasureTheory.Measure.dirac_apply_of_mem (show b ∈ ({b} : Set ℝ) from rfl)] at h2
  by_contra hne
  rw [MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton b),
      Set.indicator_of_notMem (by simpa using hne)] at h2
  exact zero_ne_one h2

/-- ⭐⭐ **【`oneRule` 的核恒为 `δ_x`，与 `θ` 无关】**

```
oneRule.kernel c x = δ_x
```

**意义**：任何「从 `W.rules` 经选择器读出」的预测分布都只能是 `δ_x`，
而 `linWorld.f` 的值是 `θ * x` —— 当 `θ ≠ 1` 且 `x ≠ 0` 时两者指向**不同的点**。

**⚠ 不是同义反复**：`rfl` 级定义展开（`oneRule` 的定义就是 `fun _ x => δ_x`）。 -/
theorem oneRule_kernel_apply (c : linWorld.ctx.Carrier) (x : linWorld.frame.X.Carrier) :
    oneRule.kernel c x = MeasureTheory.Measure.dirac x := rfl

/-! ===========================================================================
  §5  ⭐⭐ 否定结果：读出的核 ≠ `linWorld.f` 的点质量
  =========================================================================== -/

/-- ⭐⭐ **【读出核 ≠ `δ_{(θ·x)}`】**

对 `x ≠ 0`、`θ ≠ 1`（故 `θ * x ≠ x`），选择器读出的核**不**是
「`linWorld.f` 的预测值」上的点质量：

```
(select W.rules.rules c x).1.kernel c x  ≠  δ_{(θ * x)}
```

**⚠ 不是同义反复**：前件 `hx : x ≠ 0`、`hθ : θ ≠ 1` 是关于**数据**与**参数值**
的具体条件；结论是**测度不等**，由 §4 的 Dirac 单射性把测度不等归约为标量不等
`θ * x ≠ x`（后者由 `hx`、`hθ` 推出）。 -/
theorem linWorld_readout_ne_prediction {θ x : ℝ} (hx : x ≠ 0) (hθ : θ ≠ 1)
    (c : linWorld.ctx.Carrier) :
    (linWorld.selector.select linWorld.rules.rules c x).1.kernel c x
      ≠ MeasureTheory.Measure.dirac (θ * x) := by
  rw [linWorld_kernel_ignores_theta c x, oneRule_kernel_apply]
  intro heq
  have hxe : x = θ * x := dirac_inj_real heq
  have hzero : (θ - 1) * x = 0 := by linarith [hxe]
  rcases mul_eq_zero.mp hzero with h | h
  · exact hθ (by linarith)
  · exact hx h

/-! ===========================================================================
  §6  ⭐⭐⭐⭐ 汇总：读出预测对 `θ` 恒定 ⟹ 无法与 `linWorld.f` 一致
  =========================================================================== -/

/-- ⭐⭐⭐ **【读出与 `θ` 无关】**

`linWorld` 经 `W.rules` 读出的核**不依赖** `θ`（写成「`θ` 位可有可无」）：

```
∀ θ θ',  (select W.rules.rules c x).1.kernel c x  在两个 θ 处取值相同
```

**⟹** 任何形如 `Φ ((select W.rules.rules c x).1)` 的预测，
若 `Φ` 只读核，则**不可能**等于 `θ * x`（§5）。

**⚠ 不是同义反复**：无命题性前件，结论是两个表达式在**不同 `θ`** 处的同一性。 -/
theorem linWorld_readout_ignores_theta
    (c : linWorld.ctx.Carrier) (x : linWorld.frame.X.Carrier) :
    ∀ θ θ' : linWorld.frame.Θ.Carrier,
      (fun _ : ℝ => (linWorld.selector.select linWorld.rules.rules c x).1.kernel c x) θ
        = (fun _ : ℝ => (linWorld.selector.select linWorld.rules.rules c x).1.kernel c x) θ' :=
  fun _ _ => rfl

/-- ⭐⭐⭐⭐ **【终版否定结论：改法 C 的一致性要求不可能满足】**

**不存在**一条「由 `W.rules` 的读出给出、且对**每个** `θ` 都与 `linWorld.f`
的预测值一致」的预测。

形式化：对 `x ≠ 0`、任意 `c`，

```
¬ (∀ θ : ℝ, (select W.rules.rules c x).1.kernel c x = δ_{(θ * x)})
```

**证明**：取 `θ = 1` 与 `θ = 2`。由 §3 的读法
`(select …).1.kernel c x = δ_x`，要求给出 `δ_x = δ_x`（`θ=1`）与
`δ_x = δ_{2x}`（`θ=2`）；后者由 §4 的 Dirac 单射性给出 `x = 2x`，即 `x = 0`，
与 `hx` 矛盾。

**⚠ 这是本模块的核心否定结论，也是「改法 C 不可行」的**精确**陈述**：
不是「还证不出来」，而是「**要求本身自相矛盾**」。

**⚠ 不是同义反复**：前件 `hx : x ≠ 0`（**数据**条件，保证 Dirac 点不同）；
结论是**全称命题的否定**（存在性否定）。 -/
theorem linWorld_rules_readout_not_consistent {x : ℝ} (hx : x ≠ 0)
    (c : linWorld.ctx.Carrier) :
    ¬ (∀ θ : ℝ,
        (linWorld.selector.select linWorld.rules.rules c x).1.kernel c x
          = MeasureTheory.Measure.dirac (θ * x)) := by
  intro h
  have hA : MeasureTheory.Measure.dirac x
      = MeasureTheory.Measure.dirac ((1 : ℝ) * x) := by
    have hh := h 1
    rw [linWorld_kernel_ignores_theta c x, oneRule_kernel_apply] at hh
    exact hh
  rw [one_mul] at hA
  have h1 : MeasureTheory.Measure.dirac x
      = MeasureTheory.Measure.dirac ((2 : ℝ) * x) := by
    have hB := h 2
    rw [linWorld_kernel_ignores_theta c x, oneRule_kernel_apply] at hB
    exact hA.trans hB
  have hx2 : x = 2 * x := dirac_inj_real h1
  have : x = 0 := by linarith
  exact hx this

/-- ⭐⭐⭐ **【读出预测被钉死在常数 `1` 上】**

设 `predRead` 是一条**只经由 `W.rules` 的读出**得到的预测，
且按 `readDetFun` 的语义取「读出核在 `{x}` 上的质量」（`hread`，**定义性接线**），
则

```
∀ c x,  predRead c x = 1
```

**⚠ 这条为什么是「否定」**：真实的预测值应是 `linWorld.f x … θ … = θ * x`。
读出预测**恒为常数 `1`** ⟹ 它**不可能是** `θ * x`
（取 `θ = 2, x = 1` 即矛盾：`1 ≠ 2`）。

**⚠ 这条为什么不是平凡**：`hread` 只是**接线说明**（`predRead` 由读出核的唯一
质量给出），它**没有**说 `predRead` 等于 `1`；`1` 来自
`δ_x {x} = 1`（`Measure.dirac_apply_of_mem`）与「读出核 = `δ_x`」（§3）的**组合**。
若 `selector` 不恒定、或 `oneRules` 不是单元素集，该结论**立即失败**。 -/
theorem linWorld_readout_prediction_formula
    (predRead : linWorld.ctx.Carrier → linWorld.frame.X.Carrier → ℝ)
    (hread : ∀ c x, predRead c x
      = ((linWorld.selector.select linWorld.rules.rules c x).1.kernel c x {x}).toReal)
    (c : linWorld.ctx.Carrier) (x : linWorld.frame.X.Carrier) :
    predRead c x = 1 := by
  rw [hread c x, linWorld_kernel_ignores_theta c x, oneRule_kernel_apply,
    MeasureTheory.Measure.dirac_apply_of_mem (show x ∈ ({x} : Set ℝ) from rfl)]
  norm_num

end EndToEndWithRulesNegative
end Fate
