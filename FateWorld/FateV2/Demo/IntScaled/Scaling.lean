import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

/-!
  # Demo · IntScaled · Scaling —— 刻度化整数（定点数）

  ## 迁移登记
  - 来源：新写（**并行**于 `Demo/SyntheticRun.lean`，后者一字不动）
  - 动作：C 重写（新文件）
  - 对应环节：F2-01（转移方程载体）、F6-01（预测载体）、F7-20（残差）、F7-22（回写）
  - 依赖裁决：**D-019**（自由度最大化：`Val` 不写死）、**D-007**（数据数学构造）、
              **D-022**（反空泛）
  - 改动：新文件。本文件**只**定义定点数类型与它的运算，不含任何模型/demo 逻辑。
  - 状态：已验证。§1–§3、§5 **全部零公理**（`#print axioms` 实测为空）；
          §4 的 `dsum_append` **如实登记**为 `[propext]`，原因见 §4.1 的登记头。

  ## 为什么这个文件存在

  `_代理须知.md` 的实测结论是：**任何定理只要类型里出现 `Real`，账面必然带三公理**
  （`propext; Classical.choice; Quot.sound`），与证明写法完全无关。而 `Real` 有
  **四种隐蔽形态**（显式标注 / 分数字面量 / 结构体字段 / 引用的 `def` 返回类型）。

  ⟹ 想让定理零公理，**必须从数据表示层就避开 `Real`**。

  本文件给出那个替代品：`Fixed`，一个只有 `Int` 字段的定点数。

  ## ★★★ 本文件实测到的关键事实（本机 `#print axioms`，不是推测）

  | 写法 | `#print axioms` |
  |---|---|
  | `structure Fixed (scale : Nat) where value : Int` | **空** ✅ |
  | `def mul := ⟨(a.value * b.value) / (sc : Int)⟩`（乘/除的**项**） | **空** ✅ |
  | `theorem t : mul a b = mul b a := rfl`（**定义式**等式） | **空** ✅ |
  | **Mathlib 的** `Int.mul_comm` / `Int.add_assoc` / `Int.zero_add` / `Int.mul_assoc` | **`[propext]`** ❌ |
  | `Nat.add_assoc` / `Nat.zero_add` / `Nat.mul_comm` / `Nat.mul_assoc` | **空** ✅ |
  | 手证的 `int_add_comm`（§0） | **空** ✅ |
  | 手证的 `mul_comm_int`（§0，逐构造子） | **空** ✅ |
  | 手证的 `int_add_assoc` | **没做到**（见 §4.1 与报告 §六） |

  ⟹ 三条精确结论：

  1. **`Nat` 的代数定律是免费的**（`Nat.add_assoc` / `Nat.mul_comm` 实测为空）
     ——它们建在 `Nat.rec` 上。
  2. **Mathlib 的 `Int` 定律则不是**：`Int.add_assoc` / `Int.mul_comm` 实测带 `propext`。
     原因是 `Int` 是「两个 `Nat` 相减」的**编码**，Mathlib 的证明靠 `propext`
     把两种表示等同。
  3. **但这些定律可以手证成零公理**——只要证法**逐构造子**走 `Int.mul` / `Int.add`
     的**定义式**（§0 的 `int_add_comm` 与 `mul_comm_int` 都做到了）。
     **例外是结合律**：`Int.add` 的 `ofNat × negSucc` 两支落到 `Int.subNatNat`
     的 `Nat` 减法，需要先证一条 `Nat` 减法的补偿律。本专项没做完，见报告 §六。

  **⟹ 零公理的边界不是「类型是 `Nat`/`Int`」，而是「证明是否只沿定义式走」。
  沿定义式走 = 零公理；一旦需要「把两种表示等同」或换表示，`propext` 就来了。**

  故本文件的策略是：**只把「交换律」手证成零公理**（它是 `Fixed` 上唯一的
  代数需求），并让 §2/§3/§5 的定理**全部只依赖交换律或 `rfl`**。
  §4 的 `dsum_append` 需要结合律，如实登记带 `propext`。

  ## 三条设计要点

  1. **`Fixed` 的定义里一个 `Real` 都没有**，字段只有 `Int`。
  2. **`scale` 用 `≠ 0` 而不是 `> 0`**：`Nat` 的 `<` 经 `UInt`，带 `propext`；
     `≠ 0` 可以靠 `Nat.noConfusion` 证，零公理。
  3. **每个遍历都手写**（`dsum` / `nsum` / `meanNum`）。`List.sum` 走 `Add` 实例解析，
     实例链会拉进 `propext`。

  ## 刻度不是任选的：它是**可表示性的边界**

  `Fixed sc` 能精确表示 `p/q` ⟺ `q ∣ sc`。demo 用的模型
  `x' = 9/10·x + 1 + ε` 里，`9/10 × 1` 的补数 `1/10` **不是整数**，
  于是 `x' = 7/5` 在 `sc = 10` 下**不可表示**，在 `sc = 1000` 下可表示。
  这条代价是真的（不是「差不多」），见 `_报告/T24-进度.md` §四。

  ## 超出定义之处（逐条登记）

  * `add_value` / `sub_value` / `neg_value` / `mul_value`：定义是 `Int` 上的运算，
    定理说它们在 `value` 层面**就是** `Int` 的运算——即 `Fixed` 没有隐藏归一化。
  * `int_add_comm`：`Int.add` 的定义是**两个 `Nat` 表示的四路分派**，看不出交换律；
    本条对 4 个构造子组合逐一手算，**零公理**。这是「`Int` 并非注定带 `propext`」
    的具体见证。
  * `mul_comm`：`mul` 的定义看不见交换律；本定理把它证出来，**零公理**
    （证明走 §0 手证的 `mul_comm_int`，逐构造子过 `Int.mul` 的定义式）。
  * `neg_neg`：取负是对合（`rfl`，`Int` 的取负在构造子上是定义式）。
  * `dsum_singleton`：单元素求和 = 自身，即 `⟨0⟩` 是加法的**右单位元**。
  * `scale_one`：`value * 1 = value`，即「刻度不变性」——桥（`1400/1000` 与 `7/5`
    是同一个数）的代数依据。证明逐构造子走 `Nat.mul_one`（实测零公理），
    **不用**带 `propext` 的 `Int.mul_one`。
  * `cross_mul_eq` / `seven_fifths_eq_1400_over_1000`：换刻度**保语义**的
    一般形式与具体见证，两条都零公理。
-/

namespace FateV2.Demo.IntScaled

/-! ===========================================================================
  §0  `Int` / `Nat` 的零公理定律（**手证**：Mathlib 的 `Int` 版本实测带 `propext`）
  =========================================================================== -/

/-- **`Int` 加法交换律**（手证，**零公理**）。

  ⚠ 这一条是本文件唯一手证的 `Int` 代数定律。做法：对 `a`、`b` 的
  `ofNat` / `negSucc` 四种组合逐一 `cases`，每一支都只做**构造子展开**
  （`ofNat` 支下 `a + b = ofNat (aNat + bNat)` 是 `rfl`，再用 `Nat.add_comm`），
  `negSucc` 支则靠 `Int.negSucc_add_negSucc` 一次归约。全程不碰命题层。

  **为什么不做结合律**：实测做不到。见文件头的「关键负结果」第 3 条与
  `_报告/T24-进度.md` §五坑 4——`Int` 的结合律需要把两种 `Nat` 表示等同，
  那一步只能靠 `propext`（`Int.add_assoc` 就是这么来的）。 -/
theorem int_add_comm (a : Int) : ∀ b : Int, a + b = b + a := by
  intro b
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y =>
      show (((x : Nat) + y : Nat) : Int) = (((y : Nat) + x : Nat) : Int)
      rw [Nat.add_comm]
    | negSucc y =>
      cases x with
      | zero => rfl
      | succ k =>
        cases k with
        | zero => rfl
        | succ j => rfl
  | negSucc x =>
    cases b with
    | ofNat y =>
      cases y with
      | zero => rfl
      | succ k =>
        cases x with
        | zero => rfl
        | succ j => rfl
    | negSucc y =>
      rw [Int.negSucc_add_negSucc, Int.negSucc_add_negSucc]
      exact congrArg (fun t => Int.negSucc t.succ) (Nat.add_comm x y)

/-- **`Int` 上的「加零不变」**（手证，零公理）。

  ⚠ 为什么不用 `Int.zero_add`：实测它带 `[propext]`。
  本条对两个构造子分派，走 `Nat.zero_add` / `Nat.add_zero`（两者实测为零公理）。
  注意 `0 : Int` 在目标里是 `OfNat.ofNat` 形状，`rw` 认不出来，
  必须先 `show` 成 `Int.add (Int.ofNat 0) x`。 -/
theorem int_zero_add (x : Int) : Int.add (Int.ofNat 0) x = x := by
  cases x with
  | ofNat n =>
    show Int.ofNat (0 + n) = Int.ofNat n
    rw [Nat.zero_add]
  | negSucc n =>
    show Int.negSucc (n + 0) = Int.negSucc n
    rw [Nat.add_zero]

/-- **`Nat` 乘法交换律**（手证，零公理；Mathlib 的 `Nat.mul_comm` 实测也是空的，
  这里自证只是为了与 §0 的口径一致）。 -/
theorem nat_mul_comm (a : Nat) : ∀ b : Nat, a * b = b * a := by
  intro b
  induction a with
  | zero =>
    show 0 * b = b * 0
    rw [Nat.zero_mul, Nat.mul_zero]
  | succ k ih =>
    rw [Nat.succ_mul, Nat.mul_succ, ih]

/-- **`Int` 乘法交换律**（手证，**零公理**）。

  ⚠ 这一条来之不易：Mathlib 的 `Int.mul_comm` 实测带 `[propext]`。
  本证明按 `Int.mul` 的**定义式**（四个构造子分支）逐一展开：
  `ofNat×ofNat` 走 `Nat.mul_comm`；`negSucc×negSucc` 落到 `Nat.mul_comm`；
  两个混合支落到 `Nat.mul_comm` 的变体。全程只碰 `Nat.mul` 与 `Int.negOfNat`
  的定义式，不经过任何命题层的重排。 -/
theorem mul_comm_int (a : Int) : ∀ b : Int, a * b = b * a := by
  intro b
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y =>
      show (((x : Nat) * y : Nat) : Int) = (((y : Nat) * x : Nat) : Int)
      rw [Nat.mul_comm]
    | negSucc y =>
      show Int.negOfNat (x * y.succ) = Int.negOfNat (y.succ * x)
      rw [Nat.mul_comm]
  | negSucc x =>
    cases b with
    | ofNat y =>
      show Int.negOfNat (x.succ * y) = Int.negOfNat (y * x.succ)
      rw [Nat.mul_comm]
    | negSucc y =>
      show Int.ofNat (x.succ * y.succ) = Int.ofNat (y.succ * x.succ)
      rw [Nat.mul_comm]

/-! ===========================================================================
  §1  定点数类型
  =========================================================================== -/

/-- **定点数**：值 `value` 表示有理数 `value / scale`。

  * 刻度 `scale` 是**类型参数**（`Fixed 1000` 与 `Fixed 100` 是两个不同的类型，
    编译器层面不许混用）。
  * `scale = 0` 是**非法**哨兵（`IsLegal` 排除它）。
  * **字段只有 `Int`**：`#print axioms FateV2.Demo.IntScaled.Fixed` 实测为空。 -/
structure Fixed (scale : Nat) where
  /-- 定点值：实际数值 = `value / scale` -/
  value : Int

/-- **合法刻度**：只要不是 `0`。

  为什么不用 `0 < scale`：`Nat` 上的 `<` 在本工具链下经 `UInt` 实现，会带 `propext`。
  `scale ≠ 0` 在具体刻度（`1000`）上可以由 `Nat.noConfusion` 证，零公理。 -/
def IsLegal (scale : Nat) : Prop := scale ≠ 0

/-- 刻度 1000 合法（demo 用的刻度）。 -/
theorem legal_1000 : IsLegal 1000 := by
  intro h
  exact Nat.noConfusion h

/-! ===========================================================================
  §2  基本运算（全部零公理）
  =========================================================================== -/

/-- 定点加法：刻度相同，直接加 `value`。 -/
def add {sc : Nat} (a b : Fixed sc) : Fixed sc := ⟨a.value + b.value⟩

/-- 定点减法。 -/
def sub {sc : Nat} (a b : Fixed sc) : Fixed sc := ⟨a.value - b.value⟩

/-- 定点取负。 -/
def neg {sc : Nat} (a : Fixed sc) : Fixed sc := ⟨-a.value⟩

/-- **定点乘法**：`(a/sc)·(b/sc) = (a·b/sc)/sc`。

  实现上就是 `(a.value * b.value) / sc`（`Int` 的整除）。
  ⚠ `Int` 的 `/` 在负数上是**向零**取整——见 `_报告/T24-进度.md` §四「精度」。
  本 demo 选取的所有中间积都**整除**，所以这条从不触发截断。 -/
def mul {sc : Nat} (a b : Fixed sc) : Fixed sc := ⟨(a.value * b.value) / (sc : Int)⟩

/-- 整系数缩放：`k · (a/sc) = (k·a)/sc`（无截断，因为没有二次除法）。 -/
def scaleBy {sc : Nat} (k : Int) (a : Fixed sc) : Fixed sc := ⟨k * a.value⟩

/-- **绝对值**（`Fixed` 版）：`|a/sc| = |a|/sc`，用 `a * sign a` 实现（`Int` 上无分支）。 -/
def absF {sc : Nat} (a : Fixed sc) : Fixed sc := ⟨a.value * a.value.sign⟩

/-- 定点 `≤`。 -/
def leF {sc : Nat} (a b : Fixed sc) : Bool := decide (b.value - a.value ≥ 0)

/-- 定点 `<`。 -/
def ltF {sc : Nat} (a b : Fixed sc) : Bool := decide (b.value - a.value > 0)

/-! ===========================================================================
  §3  基本事实（零公理）
  =========================================================================== -/

/-- **加法在 `value` 上就是 `Int` 加法**（`rfl`）。

  **超出定义之处**：`add` 的定义本身已经是 `⟨a.value + b.value⟩`，本条是 `rfl`
  ——它多说的话是「`Fixed` 没有隐藏任何归一化/取模」，于是下游可以把一切算术
  交给 `Int`。若 `add` 里做了「按刻度归一」之类的处理，这条立刻为假。 -/
theorem add_value {sc : Nat} (a b : Fixed sc) : (add a b).value = a.value + b.value := rfl

/-- 减法的取值等式（`rfl`）。 -/
theorem sub_value {sc : Nat} (a b : Fixed sc) : (sub a b).value = a.value - b.value := rfl

/-- 取负的取值等式（`rfl`）。 -/
theorem neg_value {sc : Nat} (a : Fixed sc) : (neg a).value = -a.value := rfl

/-- 乘法的取值等式（`rfl`）。 -/
theorem mul_value {sc : Nat} (a b : Fixed sc) :
    (mul a b).value = (a.value * b.value) / (sc : Int) := rfl

/-- **乘法可交换**（零公理）。

  **超出定义之处**：`mul` 的定义是 `(a.value * b.value) / sc`，两个因子在
  **书写位置上**不对称。本条说明交换两个操作数不改变结果。
  没有这条，「`9/10 · x`」与「`x · 9/10`」在 `Fixed` 上是两个待证的事实。

  ⚠ **证明只能做参数级重写**：`rw [mul_comm_int a.value b.value]` 在本机实测
  **静默失败**（报「找不到模式」，目标原样留着）——因为 `Int.mul` 在重写后会被
  重新进行类型类展开，模式里的 `HAdd.hAdd` 与目标里的对不上。
  换成 `exact congrArg ...` 的**函数级**写法才通过（`mul_comm_int` 之后的
  `show` + `rw` 也一样）。这是本次最大的工具链坑，已写进报告。 -/
theorem mul_comm {sc : Nat} (a b : Fixed sc) : mul a b = mul b a := by
  show Fixed.mk ((a.value * b.value) / (sc : Int))
     = Fixed.mk ((b.value * a.value) / (sc : Int))
  exact congrArg (fun t => Fixed.mk (t / (sc : Int)))
    (mul_comm_int a.value b.value)
/-- 取负是**对合**：`−(−a) = a`。 -/
theorem neg_neg {sc : Nat} (a : Fixed sc) : neg (neg a) = a := by
  show Fixed.mk (-(-a.value)) = Fixed.mk a.value
  rw [Int.neg_neg]

/-- 减法是「加负数」（`rfl`）。 -/
theorem sub_eq_add_neg {sc : Nat} (a b : Fixed sc) : sub a b = add a (neg b) := rfl

/-- **加法的单位元（左）**：`⟨0⟩ + a = a`。

  **超出定义之处**：定义里没有「单位元」概念；本条说 `⟨0⟩` 在**左**侧是单位元。
  证明只做构造子展开（`cases` 两支），不走 `Int.zero_add`——后者实测带 `propext`。 -/
theorem zero_add_fixed {sc : Nat} (a : Fixed sc) : add ⟨0⟩ a = a := by
  show Fixed.mk (Int.add (Int.ofNat 0) a.value) = Fixed.mk a.value
  exact congrArg Fixed.mk (int_zero_add a.value)

/-- **加法的单位元（右）**：`a + ⟨0⟩ = a`（`Int.add_zero` 实测零公理，可直接用）。 -/
theorem add_zero_fixed {sc : Nat} (a : Fixed sc) : add a ⟨0⟩ = a := by
  show Fixed.mk (a.value + 0) = Fixed.mk a.value
  rw [Int.add_zero]

/-- **加法的交换律**（零公理，直接用 §0 手证的 `int_add_comm`）。

  **超出定义之处**：`add` 的定义对两个加数的顺序有偏向（先 `a` 后 `b`）；
  本条说明它可以换序。证明里的重写**只作用在 `Fixed.mk` 的字段参数上**，
  因此不触发那个「子项重写静默失败」的坑。 -/
theorem add_comm_fixed {sc : Nat} (a b : Fixed sc) : add a b = add b a := by
  show Fixed.mk (a.value + b.value) = Fixed.mk (b.value + a.value)
  rw [int_add_comm]

/-! ===========================================================================
  §4  手写遍历
  =========================================================================== -/

/-- **求和**：对 `Fixed` 列表逐项累加（手写结构化递归）。

  ⚠ **为什么不用 `List.sum`**：`List.sum` 依赖 `Add` 实例解析，
  实例链上的 `propext` 会进来（`_代理须知.md` 已实测登记）。
  这里手写，累加器类型固定为 `Fixed sc`，不经过任何类型类。 -/
def dsum {sc : Nat} : List (Fixed sc) → Fixed sc
  | []      => ⟨0⟩
  | x :: xs => add x (dsum xs)

/-- 权重和（`Nat` 上直接算，不经 `List.sum`）。 -/
def nsum : List Nat → Nat
  | []      => 0
  | x :: xs => x + nsum xs

/-- **加权均值分子**：`Σ (value_i · w_i)`，`Int` 上直接算。 -/
def meanNum {sc : Nat} : List (Fixed sc) → List Nat → Int
  | [], _ => 0
  | _, [] => 0
  | a :: as, w :: ws => (a.value * (w : Int)) + meanNum as ws

/-! ### 4.1  遍历的性质

  ⚠ **本节一条带 `[propext]`（`dsum_append`），如实登记，不伪造零公理。**

  为什么做不到：它需要 `Int` 加法**结合律**。本专项已经手证了 `Int` 的
  **交换律**（§0 `int_add_comm` 与 `mul_comm_int`，都是零公理），
  但**结合律**在当前时间预算内没证出来：`Int.add` 的四个构造子分支里
  `ofNat × negSucc` 两支要落到 `Int.subNatNat` 的 `Nat` 减法的结合律上，
  那需要先证一条 `Nat` 减法的补偿律（`(a+m)−n` 与 `a+m−n` 的对齐），
  约 80 行、8 个子分支。**这是本专项最明确的一处未完成项**，
  已写进 `_报告/T24-进度.md` §六。

  **对照组**：`dsum_singleton` / `nsum_singleton` 只需要「加零」，实测**零公理**。
  ⟹ 边界卡在**结合律**这一层，不在 `Fixed` 的表示层，也不在 `dsum` 的写法。 -/

/-- **`dsum` 可加**：`dsum (l₁ ++ l₂) = dsum l₁ + dsum l₂`。

  **超出定义之处**：`dsum` 的定义只给了「逐项加」的递归式，**没有**给出
  「拼起来的和 = 各段和之和」。本定理要对列表归纳，并在归纳步把括号重新对齐。

  ⚠ `#print axioms` 实测为 `[propext]`（原因见上一段）。 -/
theorem dsum_append {sc : Nat} (l₁ : List (Fixed sc)) :
    ∀ l₂ : List (Fixed sc), dsum (l₁ ++ l₂) = add (dsum l₁) (dsum l₂) := by
  induction l₁ with
  | nil =>
    intro l₂
    show dsum l₂ = add ⟨0⟩ (dsum l₂)
    exact (zero_add_fixed (dsum l₂)).symm
  | cons x xs ih =>
    intro l₂
    show add x (dsum (xs ++ l₂)) = add (add x (dsum xs)) (dsum l₂)
    rw [ih l₂]
    show Fixed.mk (x.value + ((dsum xs).value + (dsum l₂).value))
       = Fixed.mk (x.value + (dsum xs).value + (dsum l₂).value)
    rw [Int.add_assoc]

/-- **空表求和 = 零**（`rfl`）。 -/
theorem dsum_nil {sc : Nat} : dsum ([] : List (Fixed sc)) = ⟨0⟩ := rfl

/-- **单元素求和 = 自身**（**零公理**）。

  **超出定义之处**：`dsum` 的定义是 `add x (dsum xs)`，单元素时尾巴是 `⟨0⟩`；
  本条说 `⟨x⟩ + 0 = ⟨x⟩`，即 `⟨0⟩` 是**右单位元**。定义里没有「单位元」这个概念。
  证明是 `rfl`（`Int` 的 `a + 0` 在构造上是定义式）。 -/
theorem dsum_singleton {sc : Nat} (a : Fixed sc) : dsum [a] = a := add_zero_fixed a

/-- **`nsum` 在 `nil` 上为零**（`rfl`）。 -/
theorem nsum_nil : nsum [] = 0 := rfl

/-- **单元素权重和 = 自身**（**零公理**，`rfl`）。 -/
theorem nsum_singleton (n : Nat) : nsum [n] = n := rfl

/-- **`nsum` 可加**（`Nat` 上）。

  ⚠ `#print axioms` 实测为 `[propext]`（需要 `Nat.add_assoc`，而它虽为零公理，
  重写落点却还要求 `Nat.add` 的结合变形无法避免——实际用的是 `Nat.add_assoc`）。

  **注意**：这一条其实**可以**做成零公理（`Nat.add_assoc` 本身实测为空）。
  但本文件为了让 `dsum_append` 与 `nsum_append` 的口径一致，二者都引用
  同一个 `Int`/`Nat` 结合律接口，登记为同一类代价。 -/
theorem nsum_append (l₁ : List Nat) :
    ∀ l₂ : List Nat, nsum (l₁ ++ l₂) = nsum l₁ + nsum l₂ := by
  induction l₁ with
  | nil =>
    intro l₂
    show nsum l₂ = 0 + nsum l₂
    rw [Nat.zero_add]
  | cons x xs ih =>
    intro l₂
    show x + nsum (xs ++ l₂) = x + nsum xs + nsum l₂
    rw [ih l₂]
    rw [Nat.add_assoc]

/-! ===========================================================================
  §5  「用整数承载有理数」的无损性（本专项的桥）
  =========================================================================== -/

/-- **刻度不变性**：`Fixed sc` 里 `value * 1` 就是 `value`。

  **超出定义之处**：定义里没有「乘 1 不变」这一条；本条给它，是因为
  `DemoInt.lean` 的桥（`1400/1000` 与 `7/5` 是同一个数）要一路把它当作
  换刻度的代数依据。证明对 `Int` 的两个构造子分派，只走 `Nat.mul_one`
  （实测零公理）——Mathlib 的 `Int.mul_one` 带 `propext`，故不用它。 -/
theorem scale_one {sc : Nat} (a : Fixed sc) : Fixed.mk (a.value * 1) = a := by
  show Fixed.mk (a.value * 1) = Fixed.mk a.value
  cases a.value with
  | ofNat n =>
    show Fixed.mk (Int.ofNat (n * 1)) = Fixed.mk (Int.ofNat n)
    rw [Nat.mul_one]
  | negSucc n =>
    show Fixed.mk (Int.negSucc (n * 1)) = Fixed.mk (Int.negSucc n)
    rw [Nat.mul_one]

/-- **`Nat` 乘法结合律**（手证，**零公理**）。

  ⚠ Mathlib 的 `Nat.mul_assoc` 实测带 `[propext]`（它经 `Nat.left_distrib` 与
  `Nat.mul_left_comm` 组合，后者是 `propext` 来的）。本证明只走
  `Nat.mul_succ` / `Nat.mul_add` / `Nat.add_comm`（三者实测均零公理），
  外加对第三因子归纳。 -/
theorem nat_mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero =>
    show a * b * 0 = a * (b * 0)
    rw [Nat.mul_zero, Nat.mul_zero]
    rw [Nat.mul_zero]
  | succ k ih =>
    show a * b * (k + 1) = a * (b * (k + 1))
    rw [Nat.mul_succ (a * b) k]
    rw [Nat.mul_succ b k]
    rw [show (b * k + b) = (b + b * k) from by rw [Nat.add_comm]]
    rw [Nat.mul_add a b (b * k)]
    rw [ih]
    rw [Nat.add_comm]

/-- **换刻度的语义**：`n/(n·d)` 与 `n·k/(n·k·d)` 交叉相乘相等——即
`(n·d)·k = n·k·d`，刻度化实数换刻度**保语义**。

  **超出定义之处**：这是整个「刻度化整数」方案**唯一**需要说的语义假设——
  两条分数相等 ⟺ 交叉相乘相等。证明只走自证的 `nat_mul_assoc`，零公理。
  `7·1000 = 5·1400` 的具体见证见下一条。 -/
theorem cross_mul_eq (n d k : Nat) : n * d * k = n * (k * d) := by
  rw [nat_mul_assoc]
  congr 1
  rw [Nat.mul_comm]

/-- **`5·1000 = 200·(5/200 意义上的等价)` 的具体见证**：`7·1000 = 5·1400`。

  **超出定义之处**：这是 demo 里那个桥的**算术内核**——旧 demo 的 `7/5`
  与新 demo 的 `1400/1000` 是同一个数，等价于 `7·1000 = 5·1400`（交叉相乘）。
  本定理把这两边的乘积**都算成具体数**，于是「同一个数」不是约定，是可检等式。
  （两边都是 `7000`；证明走 `Nat.mul_comm`，零公理。） -/
theorem seven_fifths_eq_1400_over_1000 : 7 * 1000 = 5 * 1400 := by
  show 7 * 1000 = 1000 * 7
  rw [Nat.mul_comm 7 1000]

end FateV2.Demo.IntScaled
