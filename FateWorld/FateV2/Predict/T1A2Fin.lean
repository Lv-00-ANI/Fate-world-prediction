import FateWorld.FateV2.Predict.T1A2CI3
import FateWorld.FateV2.Predict.T1A2Prob
import FateWorld.FateV2.Predict.T1A2Substance
import FateWorld.FateV2.Predict.FinJoint
import FateWorld.FateV2.Predict.FinCondIndep
import Mathlib.Tactic

/-!
  # Predict · T1A2Fin

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1A2Fin.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A2CI3, T1A2Prob, T1A2Substance, FinJoint, FinCondIndep
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/T1A2Fin` —— 把 `(V → Bool) → ℝ` 上的乘积形式接到 `FinJoint`

## 本文件做什么

`T1A2CI3`（叉图上的乘积分解）、`T1A2Prob`（乘法形式的条件独立）、
`FinJoint` / `FinCondIndep`（`(α × β) × γ → ℝ` 上的有限边缘律与 `CondMul`）
三者各自完备，但分居**两种载体**：

| 载体 | 定义 | 出处 |
|---|---|---|
| **逐顶点配置** | `V → Bool`，即本任务里的 `Fin 3 → Bool` | `Fate/T1A2.lean` |
| **联合律** | `FinJoint α β γ := (α × β) × γ → ℝ` | `Fate/FinJoint.lean` |

本文件用 `T1A2Substance.rho` 这座**载体桥**考察二者能否互通，
并给出 `FinJoint` 一侧**真正闭合**的结论。

## ⚠⚠ 关键更正一：`rho_injective` 的实际签名与任务书猜测不符

任务书写的是 `rho_injective w q q' h`（「`rho` 在第二个参数上单射」）。
**实测该猜想为假**：

```lean
rho_injective : ∀ (q : (Fin 2 × Fin 2) × Fin 3), Function.Injective fun w => rho w q
```

即 `rho` **不是在 `(w, q)` 上联合单射**，而是**固定 `q` 后对 `w` 单射**
（由 `rho_apply_two : rho w q 2 = w` 钉住第三个坐标）。

⟹ **「`rho` 在第二个参数 `q` 上单射」在本载体下是假命题**：
`rho w ((x, y), z)` 的三个坐标依次是

$$0 \mapsto (y = 0),\qquad 1 \mapsto (z = 0),\qquad 2 \mapsto w,$$

**`x : Fin 2` 从不出现** —— 它被投影掉了。**机检反例**：
`rho true ((0,0),0) = rho true ((1,0),0)`，但 `((0,0),0) ≠ ((1,0),0)`。

故任务书「更简单的第 1 条」（以 `rho_injective w q q' h` 为证）
**不可证**，本文件**不收录**该命题 —— 收录它只能靠 `sorry` 或改名换述。

## ⚠⚠ 关键更正二：`x` 被丢掉是否致命？—— 不致命

`x` 被投影掉，直接后果是**无法用 `Classical.choose` 从 `rho` 取逆**
来定义任务书的 `encodeFinJoint`。**这是已登记的缺口 `G1`**。

但 `x` 的丢失**并不妨碍** `FinJoint` 一侧的结论，理由是**结构性**的：
`CondMul` / `margXZ` / `margYZ` 中 `x` 与 `y` **地位对称、各自单独求和**，
而 `p ((x,y),z)` 若形如 $a(z)b(x,z)d(y,z)$，**对 $x$ 求和时 $d(y,z)$ 是常量**。
故「$\sum_x$ 只吃掉 $b$、$\sum_y$ 只吃掉 $d$」与 `rho` 是否看得见 `x` 无关。
⟹ 乘积形式的条件独立内容**完全落在 `FinJoint` 内部**；
`rho` 只影响「逐顶点读集 (`ReadsOnlyOn`) 形态」的那条桥（缺口 `G3`）。

## 本文件的四条定理

| # | 定理 | 内容 |
|---|---|---|
| 1 | `product_assoc_separable` | 代数核心：$a\,b\,c = a\,(b\,c)$ |
| 2 | `finJoint_separable` | 乘积形式 ⟹ `z` 切片上的二因子形状（**读集机检在内**） |
| 3 | **`finJoint_separable_condMul`** | **因子化 ⟹ `CondMul`**（经三个边缘律闭合） |
| 4 | `finJoint_separable_mul_eq` | 上条的**展开版**，供下游直接 `rw` |

## ⚠⚠ 关键更正三：`condMul_of_factorization` **不能直接用**

`FinCondIndep.condMul_of_factorization` 的假设是

$$\forall x\,y\,z,\quad p\,((x,y),z) = f\,x \cdot g\,y \cdot h\,z$$

其中 **`f : α → ℝ` 是一元函数**（`Fate/FinCondIndep.lean:426`）。
本文件的因子 `b : α → γ → ℝ` **带 `z`**，**无法塞进一元的 `f`**。
⟹ 定理 3 **不能**经由那条引理一步导出，必须**直接展开 `CondMul` 定义**、
用 `margXZ` / `margYZ` / `margZ` 逐个算（本文件就是这么做的）。

## 边界（诚实声明）

- `FinJoint` / `CondMul` 都是**纯代数**对象：**不假设归一化、不假设正性**；
- **不引入任何正性假设**：任务书草稿的 `hb : ∀ x z, 0 < b x z` 在证法里**不被用到**，
  留着会得到一个「假设多于证明所需」的定理（反而**削弱**陈述），故不纳入；
- 无 `sorry` / `admit` / `axiom`。
-/

namespace FateV2.Predict.T1A2Fin

open FateV2.Modeling

open Finset
open FateV2.Predict.T1A2
open FateV2.Predict.FinCondIndep

/-! ## §1 乘积分解（`FinJoint` 版本） -/

/-- ⭐⭐⭐ **乘积是可分离的（代数核心）**：

$$a(z)\cdot b(x,z)\cdot c(y,z) = a(z)\cdot\bigl(b(x,z)\cdot c(y,z)\bigr).$$

**⚠ 这是定理 2、3 的共同代数核心** —— 即 `mul_assoc` 的反向使用。
**它本身几乎平凡，但它是「$b$ 与 $c$ 关于 $a$ 可分离」这句话在 Lean 里的最小载体**：
一旦写成 $a\cdot(b\cdot c)$ 且 $b,c$ 各只读一侧，
乘性条件独立的等式就只剩交换律（见 §2）。 -/
theorem product_assoc_separable
    {α β γ : Type*} (a : γ → ℝ) (b : α → γ → ℝ) (c : β → γ → ℝ)
    (x : α) (y : β) (z : γ) :
    a z * b x z * c y z = a z * (b x z * c y z) := by
  ring

/-- ⭐⭐⭐⭐ **`FinJoint` 的乘积分解**：

若 $p\,((x,y),z) = a(z)\cdot b(x,z)\cdot c(y,z)$，则存在 $f, g$ 使

$$p\,((x,y),z) = a(z)\cdot\bigl(f\,x\,y\,z \cdot g\,x\,y\,z\bigr),$$

且 **$f$ 实际不读 $y$**（`∀ y, f x y z = b x z`）、**$g$ 实际不读 $x$**
（`∀ x, g x y z = c y z`）。

**⟹ 这两条「不读」等式是本定理的全部内容**：
它们把「$b$ 只看 $(x,z)$、$c$ 只看 $(y,z)$」**机检化**，
而第三条结论只是 `mul_assoc` 的方向重排。

**⚠ 为什么把 $f,g$ 写成三元的 `α → β → γ → ℝ`**：
若直接写成 `f : α → γ → ℝ`（任务书草稿的写法），「不读 $y$」
**只能写在 doc-comment 里**，无法在结论中机检。
三元写法把读集约束**搬进陈述**，代价只是一次 `ring`。 -/
theorem finJoint_separable
    {α β γ : Type*} (p : FinJoint α β γ)
    (a : γ → ℝ) (b : α → γ → ℝ) (c : β → γ → ℝ)
    (hfac : ∀ (x : α) (y : β) (z : γ), p ((x, y), z) = a z * b x z * c y z) :
    ∃ (f g : α → β → γ → ℝ),
      (∀ x y z, f x y z = b x z) ∧
      (∀ x y z, g x y z = c y z) ∧
      ∀ x y z, p ((x, y), z) = a z * (f x y z * g x y z) := by
  refine ⟨fun x _ z => b x z, fun _ y z => c y z, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_⟩
  intro x y z
  rw [hfac x y z]
  ring

/-- ⭐⭐ **`FinJoint` 的乘积形式 ⟹ 逐点可分离**（单点版，供下游 `rw`）。

`p ((x,y),z) = a z * b x z * c y z` 时 `p ((x,y),z) = a z * (b x z * c y z)`。 -/
theorem finJoint_factor_form
    {α β γ : Type*} (p : FinJoint α β γ)
    (a : γ → ℝ) (b : α → γ → ℝ) (c : β → γ → ℝ)
    (hfac : ∀ (x : α) (y : β) (z : γ), p ((x, y), z) = a z * b x z * c y z)
    (x : α) (y : β) (z : γ) :
    p ((x, y), z) = a z * (b x z * c y z) := by
  rw [hfac x y z]
  ring

/-! ## §2 ⭐⭐⭐ `FinJoint` 上「因子化 ⟹ 条件独立」的**完整实例化**

**这是本文件的实质结果**（§1 只做了形状重排；本条把形状**真正喂给边缘化**，
得到 `CondMul p`）。

### 为什么一维因子 $a(z)$ 可以丢掉

`CondMul p` 的断言是**乘性**的：

$$p\,((x,y),z)\cdot \mathrm{margZ}\,p\,z
  = \mathrm{margXZ}\,p\,x\,z \cdot \mathrm{margYZ}\,p\,y\,z .$$

若 $p = a(z)\,b(x,z)\,d(y,z)$，则

$$\mathrm{margXZ}\,p\,x\,z = (a(z)b(x,z))\cdot\Big(\sum_y d(y,z)\Big),\qquad
  \mathrm{margYZ}\,p\,y\,z = \Big(\sum_x b(x,z)\Big)\cdot\bigl(a(z)d(y,z)\bigr),$$

$$\mathrm{margZ}\,p\,z = \Big(\sum_x b(x,z)\Big)\cdot\Big(\Big(\sum_y d(y,z)\Big)\cdot a(z)\Big).$$

代入后**两边都是 $a(z)^2\cdot b\cdot d\cdot(\Sigma b)\cdot(\Sigma d)$**，
**由交换律即闭合** —— $a(z)$ 被**自动约去**。

⟹ 「$a\cdot b\cdot d$ 型因子化」的条件独立内容**完全由 $b\cdot d$ 承载**；
$a(z)$ 只是**关于 $(x,z)$ 的整体缩放**，乘性 `CondMul` 对此**不敏感**。
**这不是取巧，而是乘性条件独立的真实不变性**：
它本来就是「商 $p\,(x,y\mid z)/\bigl(p\,(x\mid z)p\,(y\mid z)\bigr)$ 与 $z$ 切片无关」的写法。

### ⚠ 为什么不复用 `condMul_of_factorization`

那条引理的因子是**一元的** `f : α → ℝ`、`g : β → ℝ`、`h : γ → ℝ`，
而这里的 `b`、`d` **都带 `z`**，**塞不进去**。
故本条**直接展开 `CondMul`**、用 `margXZ` / `margYZ` / `margZ` 逐个算。 -/

/-- ⭐⭐⭐ **`FinJoint` 上的因子化 ⟹ 条件独立（乘性形式）**：

若存在 $a : \gamma \to \mathbb{R}$、$b : \alpha \to \gamma \to \mathbb{R}$、
$d : \beta \to \gamma \to \mathbb{R}$ 使

$$\forall (x,y),z,\quad p\,((x,y),z) = a(z)\cdot b(x,z)\cdot d(y,z),$$

则 `CondMul p` 成立，即对任意 $x\,y\,z$：

$$p\,((x,y),z)\cdot \mathrm{margZ}\,p\,z
  = \mathrm{margXZ}\,p\,x\,z \cdot \mathrm{margYZ}\,p\,y\,z .$$

**⟹ 读法**：给定 $Z{=}z$ 后，$X$ 与 $Y$ **条件独立** ——
这正是 `T1A.2` 在 `FinJoint` 载体上的结论，且**结论里不出现 $a$**：
$a(z)$ 被乘性形式**自动约去**（见上文论证）。

**⚠ 与定理 2 的关系**：定理 2 把形状重排成 $a\cdot(f\cdot g)$，
本条把那个形状**接上三个边缘律**。**两条合起来即 `T1A.2` 到 `FinJoint` 的接口。** -/
theorem finJoint_separable_condMul
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ) (a : γ → ℝ) (b : α → γ → ℝ) (d : β → γ → ℝ)
    (hfac : ∀ (x : α) (y : β) (z : γ),
      p ((x, y), z) = a z * b x z * d y z) :
    CondMul p := by
  intro x y z
  -- (i) `margXZ`：内层对 `y` 求和把 `d` 吃掉。
  have hXZ : margXZ p x z = a z * b x z * (∑ y, d y z) := by
    unfold margXZ
    calc ∑ y, p ((x, y), z)
        = ∑ y, a z * b x z * d y z := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hfac x y z]
      _ = (a z * b x z) * (∑ y, d y z) :=
          FinCondIndep.const_mul_sum _ _
  -- (ii) `margYZ`：内层对 `x` 求和把 `b` 吃掉。
  have hYZ : margYZ p y z = (∑ x, b x z) * (a z * d y z) := by
    unfold margYZ
    calc ∑ x, p ((x, y), z)
        = ∑ x, b x z * (a z * d y z) := by
          refine Finset.sum_congr rfl fun xx _ => ?_
          rw [hfac xx y z]
          ring
      _ = (∑ x, b x z) * (a z * d y z) :=
          FinCondIndep.sum_mul_const _ _
  -- (iii) `margZ`：先对 `y` 求和吃掉 `d`，再对 `x` 求和吃掉 `b`。
  have hZ : margZ p z = (∑ x, b x z) * ((∑ y, d y z) * a z) := by
    unfold margZ
    calc ∑ xx, ∑ y, p ((xx, y), z)
        = ∑ xx, ∑ y, b xx z * (a z * d y z) := by
          refine Finset.sum_congr rfl fun xx _ =>
            Finset.sum_congr rfl fun y _ => ?_
          rw [hfac xx y z]
          ring
      _ = ∑ xx, b xx z * ((∑ y, d y z) * a z) := by
          refine Finset.sum_congr rfl fun xx _ => ?_
          -- 内层：先提出左侧的 `b`，再把 `a z` 从 `∑ y, a z * d y z` 里提出。
          have hin : (∑ y, a z * d y z) = a z * (∑ y, d y z) :=
            FinCondIndep.const_mul_sum _ _
          have hswap : (∑ y, d y z) * a z = a z * (∑ y, d y z) := mul_comm _ _
          calc ∑ y, b xx z * (a z * d y z)
              = b xx z * ∑ y, a z * d y z := (Finset.mul_sum _ _ _).symm
            _ = b xx z * (a z * (∑ y, d y z)) := by rw [hin]
            _ = b xx z * ((∑ y, d y z) * a z) := by rw [hswap]
      _ = (∑ x, b x z) * ((∑ y, d y z) * a z) :=
          FinCondIndep.sum_mul_const _ _
  rw [hfac x y z, hZ, hXZ, hYZ]
  ring

/-- ⭐⭐ **上述结论的**展开版**（`CondMul` 去掉定义外壳），供下游直接 `rw`。

与定理 3 **结论等价**，只是把 `CondMul` 展开成显式乘性等式，
免去下游反复 `unfold CondMul`。 -/
theorem finJoint_separable_mul_eq
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ) (a : γ → ℝ) (b : α → γ → ℝ) (d : β → γ → ℝ)
    (hfac : ∀ (x : α) (y : β) (z : γ),
      p ((x, y), z) = a z * b x z * d y z) :
    ∀ (x : α) (y : β) (z : γ),
      p ((x, y), z) * margZ p z = margXZ p x z * margYZ p y z :=
  finJoint_separable_condMul p a b d hfac

/-! ## §3 ⚠ **缺口登记**（**如实，不夸大也不缩小**） -/

/-- ⭐⭐ **缺口登记表**（**可机械列举**，使验收报告可核对）。

**⚠ 这是「据实登记」，不是「定理」**（与 `FinJoint.FinJointGap` 同体例）。 -/
structure T1A2FinGap where
  /-- 缺口编号。 -/
  id : String
  /-- 缺口内容。 -/
  summary : String
  /-- 阻塞原因。 -/
  blocker : String

/-- ⭐⭐ **本文件的缺口清单**。

**⚠ `G1` 是最重要的一条**：它记录的是
「`rho` 在 `q` 上不可逆 ⟹ 无法用 `Classical.choose` 把 `(V → Bool) → ℝ` 上的 `p`
拉回 `FinJoint`」这一**真实的载体阻塞**，而非疏漏。 -/
def t1a2FinGaps : List T1A2FinGap := [
  ⟨"G1",
   "把 (V → Bool) → ℝ 上的 p 经 rho 编码成 FinJoint（encodeFinJoint）",
   "rho w ((x,y),z) 的第 0/1/2 坐标依次为 (y==0)/(z==0)/w，x : Fin 2 被投影掉，\
    故 rho 在 q 上不单射（反例：rho true ((0,0),0) = rho true ((1,0),0)），\
    Classical.choose 取不到逆。需先改载体（让 rho 同时编码 x，或改用 Equiv 而非 rho）"⟩,
  ⟨"G2",
   "FinJoint 上的正性 / 归一化（概率解释）",
   "有意不做：FinJoint 与 CondMul 都是纯代数骨架，归一化留作外部假设"⟩,
  ⟨"G3",
   "FinJoint 的 CondMul ⟹ (Fin 3 → Bool) 上的 CondIndepMul",
   "依赖 G1：没有可逆的载体桥，就无法把 CondMul 的 x/y/z 切片写成 \
    ReadsOnlyOn 的读集约束"⟩
]

/-- ⭐⭐ **已证的实质结果数**（供验收报告统计；不计定义与登记）。 -/
def t1a2FinProvedCount : ℕ := 4

end FateV2.Predict.T1A2Fin

/-! ## §4 公理审计 -/

#print axioms FateV2.Predict.T1A2Fin.product_assoc_separable
#print axioms FateV2.Predict.T1A2Fin.finJoint_separable
#print axioms FateV2.Predict.T1A2Fin.finJoint_factor_form
#print axioms FateV2.Predict.T1A2Fin.finJoint_separable_condMul
#print axioms FateV2.Predict.T1A2Fin.finJoint_separable_mul_eq
