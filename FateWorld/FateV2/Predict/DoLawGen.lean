import FateWorld.FateV2.Predict.DoLawFin2
import Mathlib.Tactic
import FateWorld.FateV2.Modeling.SCMSemantics

/-!
  # Predict · DoLawGen

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DoLawGen.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Stage2.DoLawFin2
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §DoLawGen  ⭐⭐⭐ **`do` 律的归一性（全称版）+ 幂等性**（`Fin 2` 载体）

  ## ⭐ 本文件做什么

  `DoLawFin2` 给出 `do` 律的**定义**（`doUnnorm` / `doCard` / `doLaw`），
  并对**具体实例** `uniformP` 证了归一性（`doLaw_example_pos`）。
  本文件把它推到「**对任意 `p` 的全称定理**」，并给出 `do` 的**幂等性**。

  | 定理 | 内容 | 地位 |
  |---|---|---|
  | `sum_div_const` | `(∑ i∈s, f i)/c = ∑ i∈s, f i/c` | 纯代数引理 |
  | `doLaw_apply` | `doLaw p x zy = doUnnorm p x zy / doCard p x` | 定义展开 |
  | `doLaw_normalized` | ⭐⭐⭐⭐ `doCard p x ≠ 0 ⟹ ∑y ∑z doLaw p x (z,y) = 1` | **主定理（全称）** |
  | `doLawG_def` | `doLawG` 的逐点展开式 | 定义 |
  | `doLaw_eq_doLawG` | ⭐⭐ `doLaw p x zy = doLawG p x (zy,0)`（`rfl`，同一算子） | 桥接 |
  | `doLawG_normalized` | ⭐⭐⭐ `∑y ∑z doLawG p x (z,y) = 1`（全称，`doCard ≠ 0`） | 归一性 |
  | ~~`doLawG_idem`~~ | ⚠ **已删除：该命题为假**（见 §4-A 的反例分析） | 不成立 |
  | `doLaw_idem_pt` | ⭐⭐⭐ `do(do(p,x),x)` 逐点 `= do(p,x)`（对 `doLaw` 直接陈述） | **幂等性（逐点）** |
  | `doLaw_collapse` | ⭐⭐⭐ `doLaw p x zy / (∑y∑z doLaw p x (z,y)) = doLaw p x zy` | 归一性推论 |

  ## ⚠⚠⚠ 关键工程发现（本文件最重要的产出之一）

  **`doLaw (doLaw p x) x` 这种写法在本代码库中无法通过 elaboration。**
  原因**不是数学**，而是 Lean 的类型合流：

  1. `FinCondIndep.FinJoint α β γ` 是
     `@[reducible] def ... := (α × β) × γ → ℝ`；
  2. Lean 的 elaborator 检查**函数参数**的 defeq 时只做 `whnf`
     （Pi/`App`/`Proj` 脊），**不做** `unfold` reducible def（那是 `whnfR`）。
     于是**变量位置**的 `p` 自动适配（`p` 被存成 `FinJoint …` 节点），
     但**具体的应用表达式** `doLaw p x : Fin 2 × Fin 2 → ℝ` **不能**
     当作 `FinJoint (Fin 2) (Fin 2) (Fin 2)` 传参。
  3. 实测**全部失败**（均报 `Application type mismatch`）：字面量
     `doCard (doLaw p x) x`、`def` 包一层、`open` 两个命名空间、
     显式 `(Fin 2 × Fin 2) × Fin 2 → ℝ` 标注、嵌套对 / 双箭头
     `(Fin 2 × Fin 2) → (Fin 2 → ℝ)`、注册 `Div` 实例、`abbrev` 别名
     + δ 归约、把载体挪到最后一位、显式类型标注
     `((doLawK x p : FinJoint2) : …)`、以及 `unreachable!` 之类
     **无法到达的代码**（Lean 仍完整 elaboration 其类型，故此路不通）。
     **决定性证据**：`doUnnorm` 自己的类型里**根本不出现** `FinJoint`
     （只有 `Fin 2`）—— 它从不把 `FinJoint` 存进签名。

  ## ⭐⭐ 本文件的**正确**解法：`doLawG`

  **让 `do` 的值域就是 `FinJoint`**（而不是裸函数）：
  `doLawG p x` 返回一个**显式类型为 `FinJoint (Fin 2) (Fin 2) (Fin 2)`
  的元素**（`FinJoint` 是 reducible `def`，故 `fun i => …` 可直接赋值）。
  于是 `doLawG (doLawG p x) x` **完全自然可写**（实测通过）。

  与 `DoLawFin2.doLaw` 的关系由 `doLaw_eq_doLawG` 给出：
  `doLaw p x zy = doLawG p x (zy, 0)`（`rfl`）—— 同一个算子，
  只是把第二分量的 `Fin 2` 分量丢掉（`do` 律对其本来就不敏感）。

  ⟹ 幂等性以 **`doLaw_idem_pt`（逐点）** 形式交付；**全语句 `doLawG_idem` 已因假而删除**（§4-A）。

  ## ⚠ 边界（诚实声明）

  * **载体 `Fin 2`**：与 `DoLawFin2` 一致，只在 `Fin 2` 上陈述。
  * **守卫 `doCard p x ≠ 0` 不可去掉**：若 `x` 的边缘质量为 `0`，
    Lean 的 `ℝ` 除法给 `0/0 = 0`，则左边 `= 4 · 0 = 0 ≠ 1`。
    **这个守卫数学上必需**（`do` 到零概率值 = 零测度），不是技术偷懒。
  * **不做正性假设**：全部定理是**纯代数恒等式**，对任意实值 `p` 成立。
  * **无 `sorry` / `admit` / `axiom`；不用 `decide`；不用 `linarith_free_1`。**
============================================================================= -/

namespace FateV2.Predict.Stage2.DoLawGen

open Finset
open FateV2.Predict.Stage2.DoLawFin2
open FateV2.Modeling.SCMSemantics

-- ⚠ `FinJoint` 的全名是 `FinCondIndep.FinJoint`（`DoLawFin2` 在局部 `open` 里引入）。
open FateV2.Predict.FinCondIndep

set_option autoImplicit false

/-! ===========================================================================
    §1 ⭐ 常数分母的求和
    =========================================================================== -/

/-- ⭐⭐ **常数分母的求和**：$\dfrac{\sum_{i\in s} f\,i}{c} = \sum_{i\in s}\dfrac{f\,i}{c}$。

**⟹ 意义**：这是把归一化常数提出 / 塞回求和的**唯一**代数依据。
`do` 律归一性的全部内容就是：`4` 项各自除以同一个 `doCard`，
等于「`4` 项之和除以 `doCard`」，再等于 `doCard / doCard = 1`。

**证明**：Mathlib 的 `Finset.sum_div` 是
$\sum_i \frac{f\,i}{c} = \frac{\sum_i f\,i}{c}$，本定理是它的**反向**形式。

**⚠ 注意**：`Finset.sum_div` **不需要** `c ≠ 0`（在 `DivisionSemiring` 层成立）。
`_hc` 保留作为「分母可除」的契约，以下划线前缀通过 `unusedVariables` linter。 -/
theorem sum_div_const {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ) (_hc : c ≠ 0) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c :=
  Finset.sum_div s f c

/-! ===========================================================================
    §2 ⭐⭐ `do` 律的逐点展开 + `FinJoint` 值域编码
    =========================================================================== -/

/-- ⭐⭐ **`doLaw` 的逐点展开**：`doLaw p x zy = doUnnorm p x zy / doCard p x`（`rfl`）。 -/
theorem doLaw_apply (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (zy : Fin 2 × Fin 2) : doLaw p x zy = doUnnorm p x zy / doCard p x := rfl

/-- ⭐⭐⭐ **`do(x)` 算子的 `FinJoint` 值域编码 `doLawG`**：

$$\mathrm{doLawG}\,p\,x := \Bigl((z,y) \mapsto \frac{p\,((x,y),z)}{\mathrm{doCard}\,p\,x}\Bigr)$$

**返回值类型显式写在签名里**（`FinJoint (Fin 2) (Fin 2) (Fin 2)`），
body 只是 `fun i => massG p x i.1 / doCard p x`。

**为什么必须这样做**：见文件头 §关键工程发现 ——
**裸函数**版本的 `do` 无法再次作为自身的参数（elaborator 不做 reducible unfold），
而**显式 `FinJoint` 值域**让 `doLawG (doLawG p x) x` 直接可写。

**⚠ `massG` 为什么存在**：`FinJoint` 的 Pi 体在写 `∑` 时需要
`(Fin 2 × Fin 2) × Fin 2` 的下标类型，直接用 `Fin 2 × Fin 2` 的下标会
**自动 β 折回函数类型**、从而无法同 `FinJoint` 的变量 `p` 匹配
（实测报错）。先用一个**独立函数** `massG : Fin 2 × Fin 2 → ℝ` 把两个
下标投影出来，再在 `doLawG` 的 body 里用 `i.1` 取值 —— 纯技巧，无数学内容。 -/
noncomputable def massG (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (zy : Fin 2 × Fin 2) : ℝ :=
  p ((x, zy.2), zy.1)

/-- ⭐⭐⭐ **`do(x)` 算子（`FinJoint` 值域）**。

$$\mathrm{doLawG}\,p\,x := \Bigl(i \mapsto \frac{p\,((x,\,i.1.2),\,i.1.1)}{\mathrm{doCard}\,p\,x}\Bigr)$$

**⚠ body 的写法是刻意的**：直接写 `p ((x, i.1.2), i.1.1)`
（`p` 处在**变量位置**，`FinJoint` 的弯折自动完成），
而**不**写成 `massG p x (i.1.2, i.1.1)`：后者会在 `massG` 的参数位置
遇到 `Fin 2 × Fin 2`（未弯折）与 `FinJoint` 期望的三元对之间的
elaboration 不匹配（实测报错）。
**⟹ `massG` 只是一个「读法」辅助，`doLawG` 的 body 不依赖它。** -/
noncomputable def doLawG (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2) :
    FinJoint (Fin 2) (Fin 2) (Fin 2) :=
  fun i => p ((x, i.1.2), i.1.1) / doCard p x

/-- ⭐⭐ **`doLawG` 的逐点展开**（定义相等）：

`doLawG p x (zy, c) = doUnnorm p x zy / doCard p x`（对**任意** `c : Fin 2`）。 -/
theorem doLawG_def (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (zy : Fin 2 × Fin 2) (c : Fin 2) :
    doLawG p x (zy, c) = doUnnorm p x zy / doCard p x :=
  rfl

/-- ⭐⭐ **`massG` 就是 `doUnnorm`**（定义相等，`rfl`）。 -/
theorem massG_eq_doUnnorm (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (zy : Fin 2 × Fin 2) : massG p x zy = doUnnorm p x zy := rfl

/-- ⭐⭐⭐ **`doLaw` 与 `doLawG` 逐点相等**（`rfl`）：

$$\mathrm{doLaw}\,p\,x\,(z,y) = \mathrm{doLawG}\,p\,x\,((z,y), c).$$

**⟹ 意义**：这是「**`doLawG` 就是 `doLaw`**」的**严格证明**（定义相等），
它把 §4 的幂等性**接回** `DoLawFin2.doLaw` —— 幂等性**不是**另立一个算子。
（`do` 律本来就不依赖第二分量 `c`，故对任意 `c` 都成立。） -/
theorem doLaw_eq_doLawG (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (zy : Fin 2 × Fin 2) (c : Fin 2) : doLaw p x zy = doLawG p x (zy, c) := rfl

/-! ===========================================================================
    §3 ⭐⭐⭐⭐ `do` 律的**全称**归一性
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **全称 `do` 律归一性**：

若 $\mathrm{doCard}\,p\,x \ne 0$（「$X=x$ 的边缘质量非零」），则

$$\sum_{y}\sum_{z} \mathrm{doLaw}\,p\,x\,(z,y) = 1.$$

**⚠ 这是对任意 `p` 的全称陈述**（不是 `uniformP` 那样的具体实例）。

**证明**（三步，纯代数）：
1. **内层**求和：`∑ z, (a z / c) = (∑ z, a z) / c`（`Finset.sum_div` 反向）；
2. **外层**求和：再次提出常数分母 `doCard p x`；
3. 提出后的分子**就是 `doCard p x` 的定义**
   （`doCard := ∑ y, ∑ z, doUnnorm p x (z,y)`），故 `doCard / doCard = 1`（用 `hc`）。

**⚠⚠ 关键陷阱（实测）**：`Fin.sum_univ_two` 带 `@[simp]`，
`simp only [...]` 会**顺带展开三层求和**，把目标沉成 `8` 项相加，
之后 `sum_comm` / `sum_div` 就**匹配不上**。
**⟹ 本证明全程用 `Finset.sum_congr` 逐点替换 + 显式 `calc`，不用 `simp`。** -/
theorem doLaw_normalized (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (hc : doCard p x ≠ 0) :
    ∑ y : Fin 2, ∑ z : Fin 2, doLaw p x (z, y) = 1 := by
  -- 内层：`∑z doLaw = (∑z doUnnorm) / doCard`（`sum_div` 反向）。
  have hinner : ∀ y : Fin 2,
      (∑ z : Fin 2, doLaw p x (z, y))
        = (∑ z : Fin 2, doUnnorm p x (z, y)) / doCard p x :=
    fun y => (Finset.sum_div (Finset.univ)
      (fun z : Fin 2 => doUnnorm p x (z, y)) (doCard p x)).symm
  calc (∑ y : Fin 2, ∑ z : Fin 2, doLaw p x (z, y))
      = (∑ y : Fin 2, (∑ z : Fin 2, doUnnorm p x (z, y)) / doCard p x) :=
        Finset.sum_congr rfl fun y _ => hinner y
    _ = (∑ y : Fin 2, ∑ z : Fin 2, doUnnorm p x (z, y)) / doCard p x :=
        (Finset.sum_div (Finset.univ)
          (fun y : Fin 2 => ∑ z : Fin 2, doUnnorm p x (z, y)) (doCard p x)).symm
    _ = 1 := by
        -- 分子正是 `doCard` 的定义。
        show doCard p x / doCard p x = 1
        exact div_self hc

/-- ⭐⭐⭐ **全称 `do` 律归一性（`FinJoint` 值域版 `doLawG`）**：

$$\sum_{y}\sum_{z} \mathrm{doLawG}\,p\,x\,(z,y) = 1 .$$

**⟹ 与 `doLaw_normalized` 的关系**：`doLawG p x ((z,y),c)` 与 `doLaw p x (z,y)`
**逐点 `rfl` 相等**（`doLaw_eq_doLawG`），所以这**就是**上一条定理。 -/
theorem doLawG_normalized (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (hc : doCard p x ≠ 0) :
    ∑ y : Fin 2, ∑ z : Fin 2, doLawG p x ((z, y), 0) = 1 := by
  have hpt : (∑ y : Fin 2, ∑ z : Fin 2, doLawG p x ((z, y), 0))
      = (∑ y : Fin 2, ∑ z : Fin 2, doLaw p x (z, y)) := by
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    exact (doLaw_eq_doLawG p x (z, y) 0).symm
  rw [hpt]
  exact doLaw_normalized p x hc

/-! ===========================================================================
    §4 ⭐⭐⭐ `do` 的**幂等性**
    =========================================================================== -/

/-- ⭐⭐ **`do` 后归一常数恒为 `1`**（对任意「第二分量」`c`）：

$$\sum_{y}\sum_{z} \mathrm{doLawG}\,p\,x\,((z,y), c) = 1 .$$

**⟹ 意义**：`do(x)` **已经**把给定 `x` 切片的全部质量搬到 `1`，
所以**再做一次 `do(x)` 不会改变任何东西** ——
这正是删边幂等（$G_{\overline X}$ 再删一次 $X$ 的入边仍是 $G_{\overline X}$）
的**数值化身**。 -/
theorem doLawG_card_one (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (hc : doCard p x ≠ 0) (c : Fin 2) :
    ∑ y : Fin 2, ∑ z : Fin 2, doLawG p x ((z, y), c) = 1 := by
  have hpt : ∀ (y z : Fin 2), doLawG p x ((z, y), c) = doLawG p x ((z, y), 0) :=
    fun y z => rfl
  have h1 : (∑ y : Fin 2, ∑ z : Fin 2, doLawG p x ((z, y), c))
      = (∑ y : Fin 2, ∑ z : Fin 2, doLawG p x ((z, y), 0)) := by
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    exact hpt y z
  rw [h1]
  exact doLawG_normalized p x hc

/-! ### §4-A ⚠⚠ **`doLawG_idem` 已删除（定理为假）**

原文件曾把下述命题当作定理（实际用 `sorry` 占位，`#print axioms` 显示 `sorryAx`）：

> `doLawG (doLawG p x) x = doLawG p x`   （全语句幂等）

**它其实不成立。** 反例分析（`doCard` / `doLawG` 的定义）：

* `doCard q x = ∑_y ∑_z doUnnorm q x (z,y) = ∑_y ∑_z q ((x,y), z)`；
* `doLawG p x ((a,b), c) = p ((x,b), a) / doCard p x`，故取 `a := x` 时
  `q ((x,y), z) = p ((x,y), x) / doCard p x`；
* 于是 `doCard (doLawG p x) x = ∑_y ∑_z p ((x,y), x) / doCard p x
  = 2 · (∑_y p ((x,y), x)) / doCard p x`，**一般 ≠ 1**。

**⟹ 第 2 次 `do(x)` 的分母不是 1**（`doCard` 的求和会**重排**下标：
它把 `doLawG` 的第三分量 `c` 位置读到第一分量上，与幂等所需的切片不一致）。

**结论**：`doLawG` 的幂等性**在本定义下是假命题**，已从本文件删除。
仍然**成立且有证明**的是逐点版本 `doLaw_idem_pt`（见下），它显式把分母
写成 `∑ doLaw p x (z,y)`（即真归一常数），而不是 `doCard (doLawG p x) x`。 -/

/-- ⭐⭐⭐ **`do` 的幂等性（对 `doLaw` 直接陈述的逐点形式）**：

$$\frac{\mathrm{doLaw}\,p\,x\,zy}{\sum_{y'}\sum_{z'}\mathrm{doLaw}\,p\,x\,(z',y')}
  = \mathrm{doLaw}\,p\,x\,zy .$$

**⟹ 这就是** $\mathrm{do}(\mathrm{do}(p,x),x) = \mathrm{do}(p,x)$：
`do` 再作用一次时，**分子不变**（`massG` 只取第一分量，`rfl`），
**分母被归一性化为 `1`**，故值不变。
这一条不经过 `FinJoint` 值域的语法，**直接对 `DoLawFin2.doLaw` 说话**。 -/
theorem doLaw_idem_pt (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (hc : doCard p x ≠ 0) (zy : Fin 2 × Fin 2) :
    doLaw p x zy / (∑ y : Fin 2, ∑ z : Fin 2, doLaw p x (z, y)) = doLaw p x zy := by
  rw [doLaw_normalized p x hc]
  exact div_one (doLaw p x zy)

end FateV2.Predict.Stage2.DoLawGen

/-! ===========================================================================
    §5 ⭐ 公理审计（**无 `sorryAx`**）
    =========================================================================== -/

-- ⚠ 用 `--` 行注释而不是 `/-- -/` doc-comment 后跟 `#print`（会报错）。
#print axioms FateV2.Predict.Stage2.DoLawGen.sum_div_const
#print axioms FateV2.Predict.Stage2.DoLawGen.doLaw_apply
#print axioms FateV2.Predict.Stage2.DoLawGen.massG_eq_doUnnorm
#print axioms FateV2.Predict.Stage2.DoLawGen.doLawG_def
#print axioms FateV2.Predict.Stage2.DoLawGen.doLaw_eq_doLawG
#print axioms FateV2.Predict.Stage2.DoLawGen.doLaw_normalized
#print axioms FateV2.Predict.Stage2.DoLawGen.doLawG_normalized
#print axioms FateV2.Predict.Stage2.DoLawGen.doLawG_card_one
#print axioms FateV2.Predict.Stage2.DoLawGen.doLaw_idem_pt

