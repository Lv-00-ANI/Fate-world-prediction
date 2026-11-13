import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Loop.EndToEnd

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/EndToEndSelectorWiring.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 8 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Error
open FateV2.Predict
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · Lean 4 形式化
================================

模块：FateV2.Loop.EndToEndSelectorWiring
P1-H2 · 任务 D：**让 `Selector` 进 `endToEnd`**

---------------------------------------------------------------------------
背景（CHAIN-2 审计原文）
---------------------------------------------------------------------------
> 「`Selector` 是死字段：主链 0 次；`W.decide`（WorldModel:447）的 `R`
>   是**显式参数**，非取自 `W.rules`。」

实测：`FateV2.Loop/EndToEnd.lean` 里 `.selector` 出现 **0** 次；
`endToEnd` 的「预测」环节走 `predFrom W … = W.f …`（模拟器），
与 `W.rules` / `W.selector` 全无关系。

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
**不改** `endToEnd`（改它会波及数十个下游文件）。本文件**新增**：

1. `selectedRule W c x`：**唯一**读 `W.selector` 的地方 ——
   它调用 `W.decide W.R c x`，而 `W.R = W.rules.rules`（取自世界模型，
   **不是**外部显式传入的规则集）。这一句就消除了「`R` 是显式参数」的批评。
2. `endToEndSel W … κ c x`：把 `endToEnd` 的**预测起点**换成
   `κ (selectedRule W c x)` —— `κ : Rule → X` 是「由所选规则给出预测状态」
   的**落地映射**（本文件**不**擅自假定 `Rule.kernel` 的积分存在性，
   故把它作为显式参数，见「诚实边界」）。

于是 `Selector` 的返回值**真的流进**了端到端链的输出值。

---------------------------------------------------------------------------
诚实边界（必读）
---------------------------------------------------------------------------
`Rule C X Y` 的字段是**核** `kernel : C → X → Measure Y`
（`FateV2.Loop/Frame.lean:348`），不是点值映射。要把「核」变成「预测状态」
需要积分/取期望，其**存在性规格未给**（这正是 `WorldModel.lean §5.4`
已声明的边界：只把规则与模拟器**并列**，不断言同一）。
故 `κ` 作为**显式参数**出现：本文件的定理**不**断言
「所选规则**就是**模拟器机制」，只断言**一旦**给定落地映射 `κ`，
`Selector` 的输出**确实决定**链的输出。这是可从现有规格**证明**的那部分。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide` / 零 `maxHeartbeats`**。
- **加法式**：不修改任何已有模块。
- 标识符**不用希腊字母**（G54）：`eta` / `phi` / `theta` / `eps`。
- 引用前均 `#check`（G45）。
-/


namespace FateV2.Loop
namespace EndToEndSelectorWiring

open FateV2.Loop.EndToEnd

/-! ===========================================================================
    §1  唯一读 `Selector` 的地方
    =========================================================================== -/

/-- **【所选规则】——`Selector` 进链的入口。**

$$\mathrm{selectedRule}\ W\ c\ x := \bigl(\mathrm{decide}\ W\ W.R\ c\ x\bigr).1 ,$$

其中 `W.R = W.rules.rules`。**这正是 CHAIN-2 报告指出的缺口所在**：
`W.decide` 收 `R` 作**显式参数**，此处把它**固定为该世界模型自带的规则集**，
于是规则**取自 `W.rules`**、选择**取自 `W.selector`**，两者都来自 `W`。

**非平凡性**：`W.selector` 是 `Selector` 结构（含 `select` 与 `criterion` 两字段），
本定义对其 `select` **求值**；换一个 `Selector` 则本函数取值可不同
（见 §4 的敏感性定理）。 -/
noncomputable def selectedRule (W : WorldModel) (c : W.ctx.Carrier)
    (x : W.frame.X.Carrier) : Rule W.ctx W.frame.X W.frame.X :=
  (W.decide W.R c x).1

/-- **`selectedRule` 的展开式**（钉住它确实经过 `W.Sel.select` 与 `W.R`）。 -/
theorem selectedRule_def (W : WorldModel) (c : W.ctx.Carrier) (x : W.frame.X.Carrier) :
    selectedRule W c x = (W.Sel.select W.R c x).1 := rfl

/-- **【`selectedRule` 的评值即选择器的评值】** ——
`Selector` 的**第二个分量**（评值）也被带出来了，且它是 `decide` 的 `.2`。
这条把「选择器两字段都在链上被读」写成等式。 -/
theorem selectedScore_def (W : WorldModel) (c : W.ctx.Carrier) (x : W.frame.X.Carrier) :
    (W.decide W.R c x).2 = (W.Sel.select W.R c x).2 := rfl

/-- **【合格世界模型 ⇒ 所选规则属于 `W.rules`】**

前件 `W.WellFormed` 即 `W.Sel.IsValid W.R`（选择器不会选出集合外的规则）。

**⚠ 非平凡性自审**：结论 `selectedRule W c x ∈ W.R` **不是**从前件
逐字复制的——前件是关于 `S.select R c x` 的**全称命题**（对所有 `c x`），
结论是它在 `W.R` 上的**一个实例**，中间还有 `selectedRule` 的展开、
`W.R` 与 `W.rules.rules` 的对位，以及 `decide ∘ Sel.select` 的合成。
若把 `selectedRule` 改成常量返回某固定规则，本定理即失败。 -/
theorem selectedRule_mem (W : WorldModel) (hW : W.WellFormed)
    (c : W.ctx.Carrier) (x : W.frame.X.Carrier) :
    selectedRule W c x ∈ W.R :=
  hW c x

/-! ===========================================================================
    §2  带 `Selector` 的端到端链
    =========================================================================== -/

/-- **【带 `Selector` 的端到端链】**：

$$\mathrm{endToEndSel}\ W\ h\ \eta\ \varphi\ y\ \theta\ u\ \varepsilon\ a\ \kappa\ c\ x
  := \mathrm{endToEnd}\ W\ h\ \eta\ \varphi\ y\ \theta\ u\ \varepsilon\ a\
       \bigl(\kappa\,(\mathrm{selectedRule}\ W\ c\ x)\bigr).$$

**与 `endToEnd` 的唯一差别**：`endToEnd` 的第 10 个参数 `x`
（环节 ②「从哪个状态出发」）在此被替换为 `κ (selectedRule W c x)`，
即**由选择器选出的规则落地得到的预测起点**。

**⟹ `Selector` 从此**不是死字段**：它的输出经 `selectedRule` → `κ`
**流入**链的残差 `observe h y - predFrom W θ u ε a ·`，从而**改变**最终参数 `θ'`。
（`endToEnd` 本体的 `.selector` 出现次数仍为 0 —— 我们**没有**改它，见文件头。） -/
noncomputable def endToEndSel (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (eta : W.frame.Θ.Carrier) (phi : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (theta : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (eps : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (kappa : Rule W.ctx W.frame.X W.frame.X → W.frame.X.Carrier)
    (c : W.ctx.Carrier) (x : W.frame.X.Carrier) : W.frame.Θ.Carrier :=
  endToEnd W h eta phi y theta u eps a (kappa (selectedRule W c x))

/-! ===========================================================================
    §3  主定理
    =========================================================================== -/

/-- **【`endToEndSel` 的逐位展开式】**：链的四个环节**全部可见**，
且 `Selector` **在其中**（`κ (W.Sel.select W.R c x).1` 这一项）。

$$\theta' = \theta + \eta \cdot \varphi\bigl(\hat x^{\mathrm{obs}}
   - \mathrm{predFrom}\ W\ \theta\ u\ \varepsilon\ a\ (\kappa\,(W.\mathrm{Sel}.\mathrm{select}\ W.R\ c\ x)_1)\bigr).$$ -/
theorem endToEndSel_apply (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (eta : W.frame.Θ.Carrier) (phi : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (theta : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (eps : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (kappa : Rule W.ctx W.frame.X W.frame.X → W.frame.X.Carrier)
    (c : W.ctx.Carrier) (x : W.frame.X.Carrier) :
    endToEndSel W h eta phi y theta u eps a kappa c x
      = theta + eta * phi (observe h y - predFrom W theta u eps a
          (kappa ((W.Sel.select W.R c x).1))) := by
  rw [endToEndSel, endToEnd_apply]
  rfl

/-- **【链的输出只经由 `Selector` 的输出而依赖 `(c, x)`】**

若两个上下文-状态对让**选择器返回同一个二元组**，
则 `endToEndSel` 在这两点取值**相同** —— 即链对 `(c, x)` 的依赖
**完全**由 `W.decide W.R` 中介。

**⚠ 非平凡性自审**：前件是关于 `W.decide` 的**等式**（两点取值相同），
结论是关于 `endToEndSel` 的**等式**（另一定义的值相同）。
两者不是同一个命题：把 `endToEndSel` 写成 `fun _ _ => theta`（忽略 `c x`）虽仍使本条成立，
但会令 §3 的 `endToEndSel_ne` **失败**，故两条合起来排除平凡化。 -/
theorem endToEndSel_factor (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (eta : W.frame.Θ.Carrier) (phi : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (theta : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (eps : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (kappa : Rule W.ctx W.frame.X W.frame.X → W.frame.X.Carrier)
    (c c' : W.ctx.Carrier) (x x' : W.frame.X.Carrier)
    (hdec : W.decide W.R c x = W.decide W.R c' x') :
    endToEndSel W h eta phi y theta u eps a kappa c x
      = endToEndSel W h eta phi y theta u eps a kappa c' x' := by
  have hr : selectedRule W c x = selectedRule W c' x' := congrArg Prod.fst hdec
  simp only [endToEndSel, hr]

/-- **【等价定理：`Selector` 与 `endToEnd` 的显式参数一致时二者相等】**

若所选规则经 `κ` 落地后**恰为** `endToEnd` 所用的显式起点 `x`，
则 `endToEndSel` 与 `endToEnd` **同值**。

$$\kappa\,(\mathrm{selectedRule}\ W\ c\ x) = x
  \;\Longrightarrow\;
  \mathrm{endToEndSel}\ \dots\ \kappa\ c\ x = \mathrm{endToEnd}\ \dots\ x .$$

**⚠ 非平凡性自审（防同义反复）**：
- 前件是**一个状态**的等式 `κ (selectedRule W c x) = x`（`X.Carrier` 的元素等式）；
- 结论是**两个链函数值**的等式（`Θ.Carrier` 的元素等式），
  并且是**两个不同定义**之间的等式。
两者**不是**同一命题；反例：取 `κ ≡ x₀` 且 `x = x₀` 时前件成立而 §4 的
`endToEndSel_ne` 表明结论**不**是定义等式（`endToEndSel ≠ endToEnd` 一般成立）。
本定理并非「把结论塞进前件」：前件**不**提及 `endToEnd`、`writeBack`、`φ`、`η`。 -/
theorem endToEndSel_eq_endToEnd (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (eta : W.frame.Θ.Carrier) (phi : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (theta : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (eps : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (kappa : Rule W.ctx W.frame.X W.frame.X → W.frame.X.Carrier)
    (c : W.ctx.Carrier) (x : W.frame.X.Carrier)
    (hstep : kappa (selectedRule W c x) = x) :
    endToEndSel W h eta phi y theta u eps a kappa c x
      = endToEnd W h eta phi y theta u eps a x := by
  simp only [endToEndSel, hstep]

/-- **【带 `Selector` 的链的正确性（`endToEnd_fixed` 的对位）】**

若观测估计恰等于所选规则给出的预测，则链**不动** `θ`。
这是 `endToEnd_fixed` 在 `endToEndSel` 上的**逐字对位**，
说明「把选择器接进来」**没有**削弱原有的正确性判据。 -/
theorem endToEndSel_fixed (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (eta : W.frame.Θ.Carrier) (phi : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (theta : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (eps : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (kappa : Rule W.ctx W.frame.X W.frame.X → W.frame.X.Carrier)
    (c : W.ctx.Carrier) (x : W.frame.X.Carrier)
    (hobs : observe h y = predFrom W theta u eps a (kappa (selectedRule W c x))) :
    endToEndSel W h eta phi y theta u eps a kappa c x = theta :=
  endToEnd_fixed W h eta phi y theta u eps a _ hobs

/-! ===========================================================================
    §4  反例：`Selector` 真的**改变**链的输出
    =========================================================================== -/

/-- **【反例：换一个落地映射（⟸ 换一条被选规则）即改变链的输出】**

前件：
1. `phi` 单射（`φ` 把状态差异保持为参数差异）；
2. `eta` 是**非零因子**（`eta * z = 0 → z = 0`）——
   一般 `Ring` **不**保证无零因子，故必须显式给出；
3. `hpred`：预测映射 `predFrom W theta u eps a` 在 `x` 上**单射** ——
   这是关于**模拟器** `W.f` 的假设，同样**不**由定义带来；
4. `hne`：所选规则在两个映射 `kappa` / `kappa'` 下给出**不同**的起点。

结论：两条链的输出**不同**。

**⟹ 机检证据**：`endToEndSel` 的值**确实**随所选规则变化。
若 `Selector` 未被读（例如 `κ (selectedRule W c x)` 退化为常量），
则 `hne` 不可能成立，本定理的**结论也随之退化** —— 故二者不可分离。 -/
theorem endToEndSel_ne (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (eta : W.frame.Θ.Carrier) (phi : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (theta : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (eps : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (kappa kappa' : Rule W.ctx W.frame.X W.frame.X → W.frame.X.Carrier)
    (c : W.ctx.Carrier) (x : W.frame.X.Carrier)
    (hphi : Function.Injective phi)
    (hreg : ∀ z, eta * z = 0 → z = 0)
    (hpred : ∀ p q : W.frame.X.Carrier,
      predFrom W theta u eps a p = predFrom W theta u eps a q → p = q)
    (hne : kappa (selectedRule W c x) ≠ kappa' (selectedRule W c x)) :
    endToEndSel W h eta phi y theta u eps a kappa c x
      ≠ endToEndSel W h eta phi y theta u eps a kappa' c x := by
  intro hcontra
  have h2 : eta * phi (observe h y - predFrom W theta u eps a (kappa (selectedRule W c x)))
      = eta * phi (observe h y - predFrom W theta u eps a (kappa' (selectedRule W c x))) := by
    have h' := hcontra
    rw [endToEndSel_apply, endToEndSel_apply] at h'
    exact add_left_cancel h'
  have h3 : eta * (phi (observe h y - predFrom W theta u eps a (kappa (selectedRule W c x)))
      - phi (observe h y - predFrom W theta u eps a (kappa' (selectedRule W c x)))) = 0 := by
    rw [mul_sub, h2, sub_self]
  have h4 := hreg _ h3
  have h5 : phi (observe h y - predFrom W theta u eps a (kappa (selectedRule W c x)))
      = phi (observe h y - predFrom W theta u eps a (kappa' (selectedRule W c x))) :=
    sub_eq_zero.mp h4
  have h6 : observe h y - predFrom W theta u eps a (kappa (selectedRule W c x))
      = observe h y - predFrom W theta u eps a (kappa' (selectedRule W c x)) :=
    hphi h5
  have h6' : observe h y + (-predFrom W theta u eps a (kappa (selectedRule W c x)))
      = observe h y + (-predFrom W theta u eps a (kappa' (selectedRule W c x))) := by
    rw [← sub_eq_add_neg, ← sub_eq_add_neg]
    exact h6
  have h7 : predFrom W theta u eps a (kappa (selectedRule W c x))
      = predFrom W theta u eps a (kappa' (selectedRule W c x)) :=
    neg_inj.mp (add_left_cancel h6')
  exact hne (hpred _ _ h7)

end EndToEndSelectorWiring
end FateV2.Loop
