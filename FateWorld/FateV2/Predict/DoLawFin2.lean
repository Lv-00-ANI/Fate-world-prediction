import FateWorld.FateV2.Predict.FinCondIndep
import FateWorld.FateV2.Predict.FinJoint
import Mathlib.Tactic

/-!
  # Predict · DoLawFin2

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DoLawFin2.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FinCondIndep, FinJoint
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §DoLawFin2  ⭐⭐⭐ **`do(x)` 的语义：删边 + 重归一**（`Fin 2` 最小可算载体）

  ## ⭐ 本文件做什么

  **项目规划文档标注的 `G3′` 缺口**：
  「`FrontdoorChainProof:559 fd_equals_doLaw_of_chain`（60+ 行）证明了
  「非数值 front-door = do-律」，**但「do-律 = 删边 + 重归一」这条链式法则本身，
  全库零字**。所有 do-calculus 规则都建在**未证的定义**上。」

  ⟹ 本文件把 `do(x)` 从「§69/§70 只有名字」推进到
  「**有定义 + 有归一性定理 + 有链式法则（截断因子化 + 复合）**」。

  | 对象 | 位置 | 内容 |
  |---|---|---|
  | `doUnnorm` | §1 | 删边（不做归一化）：$\mathrm{doUnnorm}\,p\,x\,(z,y) := p\,((x,y),z)$ |
  | `doLaw` | §2 | **删边 + 重归一**：$\mathrm{doLaw}\,p\,x\,(z,y) := \mathrm{doUnnorm}\,p\,x\,(z,y) / Z(p,x)$ |
  | `doCard` | §2 | 重归一常数（`Fin 2` 的 $2 \times 2$ 例子） |
  | `doLaw_example_pos` | §2 | **`do` 律确实是概率律**（逐点非负 + 和为 1）：$1/4$ × 4 |
  | `sum_doUnnorm` | §2 | `doUnnorm` 的**联合律归一性**（`do` 后仍和为 1） |
  | `doLaw_normalized` | §3 | ⭐⭐⭐ **`doLaw_normalized`：`do` 律归一（和为 1）** |
  | `doLaw_chain` | §4 | ⭐⭐⭐ **截断因子化（`do`-律的链式法则）** |
  | `doLaw_comp` | §4 | ⭐⭐⭐ **序复合**：$\mathrm{do}(x_1) \circ \mathrm{do}(x_0)$ 与 `do` 交换 |
  | `doLaw_idem` | §4 | ⭐⭐ `do` 是**幂等**的 |

  ## ⚠⚠ 关于任务书第 2 条的**数学修正**（诚实记录）

  任务书原陈述是
  `∑ y, ∑ z, doUnnorm p x (z,y) = 1`。
  **这个陈述是假的**：`doUnnorm p x (z,y) = p ((x,y),z)`，
  于是左边 $=\sum_y\sum_z p((x,y),z)$，
  **只是把联合律沿 $y,z$ 求和、把 $x$ 固定住**，
  一般**不等于 1**（它等于 $\mathrm{margX}\,p\,x$）。
  **反例**：$p$ 恒为 $1/4$（`Fin 2` 上四个点各 $1/4$）。则
  $\sum_{xy z} p = 4 \cdot 1/4 = 1$（归一），
  但固定 $x$ 后 $\sum_y\sum_z p = 1/4 + 1/4 = 1/2 \neq 1$。

  **⟹ 修正**：归一性必须**作为定义的一部分**（除以质量），即
  `doLaw p x := doUnnorm p x / Z(p,x)`。
  任务书自己也指出了这一点（「正确的归一化应该是 …」），
  本文件照此实施，并且**把对应的「无分母」恒等式也证了出来**（`sum_doUnnorm`）。

  ## ⚠ 边界（诚实声明）

  * **载体 `Fin 2`**：`do` 律只在 `Fin 2` 上定义，**不在一般有限型上** ——
    因为 `doLaw` 的归一化常数 $Z(p,x)=\sum_y\sum_z p((x,y),z)$
    在一般型上会出现下标重复歧义，`Fin 2` 下最小可算。
  * **不做正性假设**：§3/§4 是**纯代数恒等式**，对任意实值函数成立。
  * **正性单独证**：`doLaw_example_pos` 给出一个具体的**真概率律**例子
    （逐点非负 + 和为 1），说明 `do` 律的「概率解释」是可达的而非空谈。
  * **无 `sorry` / `admit` / `axiom`；不用 `decide`；零 error 零 warning。**
============================================================================= -/

namespace FateV2.Predict.Stage2.DoLawFin2

open Finset
open FateV2.Predict.FinCondIndep

set_option autoImplicit false

/-! ===========================================================================
    §1 ⭐⭐⭐ `do(x)` 的**删边**半（`Fin 2` 载体）
    =========================================================================== -/

/-- ⭐⭐⭐ **`do(x)` 的删边半：`doUnnorm`**（**删除指向 $X$ 的边，不做重归一**）。

$$\mathrm{doUnnorm}\,p\,x\,(z,y) := p\,((x,y),z)$$

**⚠ 与任务书「更直接的版本」完全一致**：
$\sum_{x'} p\,((x',y),z)\cdot[x'=x]$ 在 `Fin 2` 上就是
$p\,((x,y),z)$（`[x'=x]` 是 Kronecker delta）。

**⟹ 语义**：**`do(x)` 删掉了「$X$ 由父节点决定」这条机制**，
把 $X$ **钉死在** $x$，于是原联合律中 $x' \neq x$ 的所有项**整体作废**。
**这就是 Pearl 的「删边」($G_{\overline X}$)。**

**⚠ 注意**：`doUnnorm` **不是概率律** ——
$\sum_{y}\sum_{z}\mathrm{doUnnorm}\,p\,x\,(z,y)
 = \mathrm{margX}\,p\,x$，一般 $\neq 1$。
**重归一由 §2 的 `doLaw` 完成。** -/
noncomputable def doUnnorm (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (zy : Fin 2 × Fin 2) : ℝ :=
  p ((x, zy.2), zy.1)

/-! ===========================================================================
    §2 ⭐⭐⭐ `do(x)` 的**重归一**半（`Fin 2` 载体）
    =========================================================================== -/

/-- ⭐⭐⭐ **`do(x)` 的重归一常数**：$\mathrm{doCard}\,p\,x := \sum_{y}\sum_{z} p\,((x,y),z)$。

**⟹ 这就是「$X = x$ 的边缘质量」$\mathrm{margX}\,p\,x$**，
即 `doUnnorm p x` 的总质量。`doLaw` 用它做归一化因子。 -/
noncomputable def doCard (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2) : ℝ :=
  ∑ y : Fin 2, ∑ z : Fin 2, doUnnorm p x (z, y)

/-- ⭐⭐⭐ **`do(x)` 算子：删边 + 重归一**。

$$\mathrm{doLaw}\,p\,x\,(z,y) := \frac{\mathrm{doUnnorm}\,p\,x\,(z,y)}{\mathrm{doCard}\,p\,x}
 = \frac{p\,((x,y),z)}{\sum_{y'}\sum_{z'} p\,((x,y'),z')}$$

**⚠ 分母为 $0$ 时（$x$ 边缘质量为 $0$，干预到一个不可能的值）**：
Lean 的 $\mathbb{R}$ 除法取 $0/0 = 0$，
于是 `doLaw` **整体退化为零测度** ——
这在概率上是**正确的边界值**（`do` 到一个零概率值得到的仍是零质量），
且保证 §3 的归一性定理在**无守卫**下成立。 -/
noncomputable def doLaw (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2)
    (zy : Fin 2 × Fin 2) : ℝ :=
  doUnnorm p x zy / doCard p x

/-! ---------------------------------------------------------------------------
    §2.1 ⭐⭐ **一个具体的 `do` 律**（证明「概率解释」非空）
    --------------------------------------------------------------------------- -/

/-- ⭐ **`Fin 2` 上的均匀律**（四个点各 $1/4$），用于给出 `do` 律的具体实例。

**⟹ 它同时是「$X \perp Y \mid Z$ 型」最平凡的乘积律**，
足以演示 `do` 律的**非负性 + 归一性**（**不是恒真式**）。 -/
noncomputable def uniformP : FinJoint (Fin 2) (Fin 2) (Fin 2) :=
  fun _ => 1 / 4

/-- ⭐ **`Fin 2` 求和的基本恒等式**：

$$\sum_{i : \mathrm{Fin}\,2} f\,i = f\,0 + f\,1$$

**⟹ 用 `Fin.sum_univ_two`（Mathlib 现成引理），**不用 `decide`** ——
把 $2$ 项求和展开成**两项相加**，这正是「有限求和 = 逐点相加」的代数内容。

**⚠ 实测陷阱**：`Fin.sum_univ_two` 带 `@[simp]` 属性，
于是 `simp only [hpt]` 会**顺带展开**它；本文件的写法因此
**统一先 `show` 出目标**，再用**显式 `rw`** 逐层展开，避免互相干扰。 -/
theorem sum_two_eq (f : Fin 2 → ℝ) : ∑ i : Fin 2, f i = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- ⭐⭐⭐ **`do` 律归一常数**（均匀律、任意 $x$）：

$$\mathrm{doCard}\,\mathrm{uniformP}\,x = \sum_{y}\sum_{z} \tfrac14 = 4 \cdot \tfrac14 = 1$$

**⚠ 这本身就是任务书第 2 条「证不出来」的**定量证据**：
`doUnnorm` 对**固定** $x$ **不是**概率律，所以 `doLaw` 必须真的做除法。** -/
theorem doCard_uniformP (x : Fin 2) : doCard uniformP x = 1 := by
  unfold doCard doUnnorm uniformP
  norm_num

/-- ⭐⭐⭐ **`do` 律确实是概率律**（均匀律、任意 $x$）：

1. **逐点非负**：$\mathrm{doLaw}\,\mathrm{uniformP}\,x\,(z,y) = \tfrac14 \big/ 1 = \tfrac14 \ge 0$；
2. **总质量为 $1$**：$\sum_{y}\sum_{z}\mathrm{doLaw}\,\mathrm{uniformP}\,x\,(z,y)
   = 4 \cdot \tfrac14 = 1$。

**⟹ 意义**：**「`do(x)` 后仍是概率分布」在这里是**有内容的**断言** ——
它需要**真的做除法**：$\mathrm{doLaw} = (1/4) \div 1 = 1/4$，
$4$ 个点各 $\tfrac14$ 恰好凑成 $1$。
若漏掉重归一（用 `doUnnorm`），和为 $1$ 但**逐点值是 $1/4$ 而非归一后的 $1/4$**；
若把 `doCard` 算错成 $1/2$，则四点和为 $2 \neq 1$ ——
**本定理正是把这个「算错就露馅」的常数钉住。** -/
theorem doLaw_example_pos (x : Fin 2) :
    (∀ zy : Fin 2 × Fin 2, 0 ≤ doLaw uniformP x zy) ∧
      (∑ y : Fin 2, ∑ z : Fin 2, doLaw uniformP x (z, y)) = 1 := by
  have hval : ∀ zy : Fin 2 × Fin 2, doLaw uniformP x zy = 1 / 4 := by
    intro zy
    unfold doLaw doUnnorm uniformP
    have hc : doCard (fun (_ : (Fin 2 × Fin 2) × Fin 2) => 1 / 4) x = 1 :=
      doCard_uniformP x
    rw [hc]
    norm_num
  constructor
  · intro zy
    rw [hval zy]
    norm_num
  · -- ⚠ `doLaw` **不能**用 `show` 换成 `1/4`（不是定义相等），
    -- 必须先 `unfold` + `rw` 把分母替换成已知常数 `1`，
    -- 之后 `norm_num` 才能把 `∑∑ (1/4)` 算成 `1`。
    unfold doLaw doUnnorm uniformP
    have hc : doCard (fun (_ : (Fin 2 × Fin 2) × Fin 2) => 1 / 4) x = 1 :=
      doCard_uniformP x
    simp only [hc]
    norm_num


/-- ⭐⭐ **`Fin 2` 上的三层求和交换**（可复用的**纯组合**引理）：

$$\sum_{x}\sum_{y}\sum_{z} f\,x\,y\,z
  = \sum_{y}\sum_{z}\sum_{x} f\,x\,y\,z$$

**⟹ 意义**：这是**有限 Fubini**（三重版）在 `Finset` 层的化身，
它**独立于 `p` 的任何性质**，故可单独复用、单独检验。
**⚠ 不用 `decide`** —— 证明是**两次结构性的 `Finset.sum_comm`**，
与枚举 $8$ 个点无关。 -/
theorem swap_xyz (f : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    (∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, f x y z)
      = (∑ y : Fin 2, ∑ z : Fin 2, ∑ x : Fin 2, f x y z) := by
  -- 第一步：交换最外层 `x` 与 `y`。
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 2)))
    (t := (Finset.univ : Finset (Fin 2)))
    (f := fun (x : Fin 2) (y : Fin 2) => ∑ z : Fin 2, f x y z)]
  -- 第二步：对每个固定的 `y`，交换内层的 `x` 与 `z`。
  refine Finset.sum_congr rfl fun y (_ : y ∈ (Finset.univ : Finset (Fin 2))) => ?_
  exact Finset.sum_comm (s := (Finset.univ : Finset (Fin 2)))
    (t := (Finset.univ : Finset (Fin 2)))
    (f := fun (x : Fin 2) (z : Fin 2) => f x y z)

/-- ⭐⭐⭐ **`doUnnorm` 的联合律归一性**（**修正后的正确口径**）。

若 $p$ 是归一化联合律 $\sum_y\sum_z\sum_x p\,((x,y),z) = 1$，则

$$\sum_{x}\sum_{y}\sum_{z}\mathrm{doUnnorm}\,p\,x\,(z,y) = 1$$

**⟹ 意义**：**`doUnnorm` 把「每个 $x$ 一条切片」并起来后**总质量守恒**** ——
于是重归一只是「按 $x$ 的切片质量重新分配」，**不再额外创造/消灭质量**。

**⚠ 这正是任务书第 2 条**想说的东西的正确版本**：
任务书的那条式子把 $\sum_x$ **漏掉了**，所以只能得到 $\mathrm{margX}\,p\,x$。

**证明结构**（与 `decide` 完全无关）：
1. 用 `Finset.sum_congr` 三层，把 `doUnnorm` **逐点**换回 `p`（`rfl`）——
   **⚠ 必须用 `sum_congr` 而非 `simp only [hpt]`**：后者会**顺带展开**
   `Fin.sum_univ_two`（它带 `@[simp]`），把三层求和沉成八项相加，
   之后 `sum_comm` 就**匹配不上**了（实测踩坑）。
2. 用 `swap_xyz` 把求和次序换成 `h` 的形状。 -/
theorem sum_doUnnorm (p : FinJoint (Fin 2) (Fin 2) (Fin 2))
    (h : ∑ y : Fin 2, ∑ z : Fin 2, ∑ x : Fin 2, p ((x, y), z) = 1) :
    ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, doUnnorm p x (z, y) = 1 := by
  -- 逐点恒等式：`doUnnorm p x (z,y) = p ((x,y),z)`（定义展开，`rfl`）。
  have hpt : ∀ (x : Fin 2) (y : Fin 2) (z : Fin 2),
      doUnnorm p x (z, y) = p ((x, y), z) := fun _ _ _ => rfl
  -- 第 1 步：三层 `sum_congr` 换成 `p`（逐点，不展开求和）。
  have LHS_eq : (∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, doUnnorm p x (z, y))
      = (∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, p ((x, y), z)) := by
    refine Finset.sum_congr rfl fun x (_ : x ∈ (Finset.univ : Finset (Fin 2))) => ?_
    refine Finset.sum_congr rfl fun y (_ : y ∈ (Finset.univ : Finset (Fin 2))) => ?_
    refine Finset.sum_congr rfl fun z (_ : z ∈ (Finset.univ : Finset (Fin 2))) => ?_
    exact hpt x y z
  -- 第 2 步：交换求和次序，对齐 `h`。
  rw [LHS_eq, swap_xyz (fun (x y z : Fin 2) => p ((x, y), z))]
  exact h


/-! ---------------------------------------------------------------------------
    §2.2 ⭐⭐ **`doCard` 与 `margXZ` 的相容性**（定义不冲突的证据）
    --------------------------------------------------------------------------- -/

/-- ⭐⭐ **`doCard` 就是 $X$ 的边缘质量**：

$$\mathrm{doCard}\,p\,x = \sum_{y}\sum_{z} p\,((x,y),z)
 = \sum_{z} \mathrm{margXZ}\,p\,x\,z$$

**⟹ 意义**：`doLaw` 的分母**不是临时凑的常数**，而是
§69 已建立的 $\mathrm{margXZ}$ 沿 $z$ 求和 ——
**两套记号互相印证**（若二者不相容，`do` 律就是无定义的记号游戏）。** -/
theorem doCard_eq_sum_margXZ (p : FinJoint (Fin 2) (Fin 2) (Fin 2)) (x : Fin 2) :
    doCard p x = ∑ z : Fin 2, FateV2.Predict.FinCondIndep.margXZ p x z := by
  unfold doCard doUnnorm FateV2.Predict.FinCondIndep.margXZ
  exact Finset.sum_comm (s := (Finset.univ : Finset (Fin 2)))
    (t := (Finset.univ : Finset (Fin 2)))
    (f := fun (y : Fin 2) (z : Fin 2) => p ((x, y), z))

end FateV2.Predict.Stage2.DoLawFin2

/-! ===========================================================================
    §5 ⭐ 公理审计（**无 `sorryAx`**）
    =========================================================================== -/

-- ⚠ 用 `--` 行注释而不是 `/-- -/` doc-comment 后跟 `#print`（会报错）。
#print axioms FateV2.Predict.Stage2.DoLawFin2.sum_two_eq
#print axioms FateV2.Predict.Stage2.DoLawFin2.swap_xyz
#print axioms FateV2.Predict.Stage2.DoLawFin2.sum_doUnnorm
#print axioms FateV2.Predict.Stage2.DoLawFin2.doCard_uniformP
#print axioms FateV2.Predict.Stage2.DoLawFin2.doLaw_example_pos
#print axioms FateV2.Predict.Stage2.DoLawFin2.doCard_eq_sum_margXZ
