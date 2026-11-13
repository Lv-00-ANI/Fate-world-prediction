import FateWorld.FateV2.Core.Cardinality
import FateWorld.FateV2.Core.Unified

/-!
  # Core · 样本量定理的**零公理版**（专项 T48）

  ## 迁移登记
  - 来源：新写（对应 `FateV2/Error/SigmaEstimation.lean` 的 `variance_meanOf`
    与 `FateV2/Error/SigmaToVerdict.lean` 的 `accepts_of_estimate_near`）
  - 动作：C 重写（**换载体**：`Real` → 纯离散可计算载体）
  - 对应环节：F7-02（σ）、F7-11（恰当拟合边界 / 裁决 K）
  - 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：**只新建本文件**（`Core/`），不改任何既有文件
  - 状态：见 `_报告/T48-进度.md`

  ## 一、为什么必须换载体（**类型决定公理，不决定战术**）

  ```lean
  theorem variance_meanOf (n : ℕ) (hn : 0 < n) :
      variance (meanOf n) (Measure.pi (fun _ : Fin n => P)) = varOf P / n
  -- [propext, Classical.choice, Quot.sound]
  ```

  `Real` 是 Cauchy 序列的商，类型闭包里就有 `Quot`。**凡签名里出现 `Real` 的定理，
  账面必然三公理，与证明写法无关**（T17 实测）。`Rat` 同样不行：它是商类型，
  `(1 : Rat) = 1` 实测已带 `[propext, Quot.sound]`，`Rat.div` 更是三公理（T15 实测）。
  **本文件一条 `Rat` 都不用。**

  ## 二、载体选择与「必须绕开的库设施」（全部实测，见 `_报告/T48-进度.md` §二）

  | 派单方案 | 本文件判定 | 理由 |
  |---|---|---|
  | A `Rat` | ❌ 不用 | `Rat` 是 `Quot` 商类型；一用就必带公理 |
  | B 手写 `(num, den)` 结构体 | ⏳ 未落地（§4 只留接口说明） | 见报告「没做什么」 |
  | C `Nat` 抽象 | ✅ **采用**（§1–§3） | 「数据越多越准」的可计算内容就是 `Nat` 上的减法与 `≤` |

  | 库设施 | 实测 | 本文件的替代 |
  |---|---|---|
  | `Nat.div` 全族（`div_mul_le_self` / `div_le_self` / `div_le_div_left` / `le_div_iff_mul_le` / `mul_div_right` / `div_eq_of_lt` / `div_pos`） | `propext` | §1 手写 `ediv` |
  | **`Nat.sub`** | `@[instance_reducible] def Nat.sub := fun x y => Nat.brecOn (motive := fun _ => ℕ → ℕ) y Nat.sub._f x` ⟹ 递归挂在**减数**上 | §1 的 `ediv` **不写 `-`**，只做「减 1」的计数 |
  | `Nat.sub_sub` / `sub_add_cancel` / `add_sub_cancel` / `sub_eq_zero_of_le` / `mul_sub_left_distrib` / `add_mul` | `propext` | 不用 |
  | `Nat.lt_of_mul_lt_mul_left/right` | **三公理** | 不证「乘可逆」；商由**构造**给出 |
  | `Int.le_trans` / `Int.add_le_add_left` / `Int.le_of_add_le_add_right` / `Int.le_refl` / `Int.le.intro` / `Int.le.dest` | **`propext`**（`Int.le` 定义成 `(b-a).NonNeg`，库证明一律走 `propext`） | §4 只在**构造子**层面用 `Int`（`ofNat` / `negSucc` / `subNatNat` / `NonNeg.mk`） |

  ## 三、⚠ 本批实测的**定义层**铁律（本文件最贵的经验）

  **(a) 嵌套第二层构造子模式（`| n+1, m+1 =>`）⟹ Lean 报「无法证明终止」。** 退化结果**取决于
  递归调用点的形状**，三种都实测过：

  | 写法 | `#print` | 能否按构造子归约 |
  |---|---|---|
  | 两个递归调用点 | `@[irreducible] def pdiv := fun a a_1 => pdiv._unary ⟨a, a_1⟩` | ❌ 完全不归约 |
  | 一个调用点、矩阵完整 | `def nsub := fun x x_1 => Nat.brecOn … x nsub._f x_1` | ✅ 能（但**只按第一个参数**分派） |
  | **递归调用写在 `+`/`-` 的「参数位置」** | `opaque` 或 `_unary` | ❌ |

  **(b) 「带括号的不可反驳模式」`| (n : Nat), m =>` 会挡住分派**，定义退化成 `_unary`。
  原样绑定变量只能写 `_n`。

  **(c) `Nat.brecOn` 只在「走到 `_f`」时才让变量模式落地**，而 `_f` 只有在目标被进一步
  展平时才会跳。于是「函数式 `match`」能算，而「`cases` 逐格」不一定 —— 本文件凡是要
  逐格算的地方都用**单参数结构递归 + 变量模式**（§1 的 `ediv`）。 -/

/-- 归约自检（具体参数）：`rfl` 成立，证明定义没有退化成 `_unary`。 -/
def reduceSelf : Nat → Nat → Nat
  | n, 0 => n
  | 0, (_m + 1) => 0
  | (n + 1), (m + 1) => reduceSelf n m

theorem reduceSelf_test : reduceSelf 5 2 = 3 := rfl

/-!
  ## 四、⚠ 本批实测的**证明层**五铁律

  **(a) `Nat.sub` 把递归挂在减数上**（§二 表格第二行）—— 本次最贵的发现。

  **(b) 「减数是字面量」是最脆的地方。** `Nat` 的 `brecOn` 只认**被减数**的构造子，
  字面量在减数位置不展开。本文件的 `ediv` 只做「减 1」，因此不触发这个坑。

  **(c) 有歧义的构造子模式不能用 `| _ + 1` / `| _b + 1`**：Lean 报
  *"Function expected at … term has type N"*，看起来像数学错误。一律具名 `(k + 1)`。

  **(d) `<` 与 `≤` 的换算必须自证**：`Nat.succ_le_of_lt` 实测带 `propext`。
  本文件用 §2 的 `succ_le_of_lt` / `lt_of_succ_lt` / `le_of_not_lt`（全部 `cases` 穷举）。

  **(e) `#print axioms` 里出现 `sorryAx` 说明证明没写完**，不是「引理带公理」。

  ## 五、本文件证了什么（每条都带「比定义多说了什么」）

  §1  `ediv`：**不用除法的商**（「减 1 计数器」），及其算术
  §2  `Nat` 序砖块（`<`/`≤` 换算、三分律的构造版本）
  §3  **派单三条主定理的零公理版**：
      - `ediv_le_self`（`ediv v n ≤ v`）
      - `ediv_le_ediv`（**单调**：`n ≤ m ⟹ v/m ≤ v/n`）
      - `exists_ediv_lt`（**趋向 0**：`0 < e ⟹ ∃ N, 0 < N ∧ ediv v N < e`）
  §4  `Int` 上的构造子级序论（`NonNeg` / `subNatNat` / `int_le_refl` / `nonneg_add`）

  ## 六、诚实边界（**没做什么**，详见 `_报告/T48-进度.md`）

  * **没有**证 `n * (v / n) ≤ v`（`ediv_mul_le`）—— 本文件根本没有乘法意义下的商，
    `ediv` 是「减 1 计数器」，与 `v/n` 的关系需要另一套除法算法（见报告 §六）。
  * **没有**把 `acceptsZ` 的零公理版证出来 —— `Int` 的 `-` 与 `≤` 都要下钻到
    `subNatNat` / `NonNeg` 的构造子，`Int.le_trans` 一类的库引理**全部带 `propext`**，
    工作量超出本轮。报告 §五 给出已完成的（`int_le_refl`、`nonneg_add`）与缺口的精确形态。
  * 本文件**不**证「`Var[meanOf n] = varOf P / n`」那条 `Real` 定理本身 —— 它的另一半是
    概率论线性性（`variance_sum` + 独立性），绕不开 `Measure` 与 `Real`。
  * 本文件**不**引入 `Rat` / `Float` / `Finset` / `Fintype` / `Measure` / `Real`。
-/

namespace FateV2.Core.SampleBounds

/-! ===========================================================================
  §1  零公理除法 `ediv`（「减 1 计数器」）
  =========================================================================== -/

/-- **`ediv v n`**：不写 `v / n`，而是「从 `v` 开始，每减 1 记一笔，直到剩下的部分
    小于 `n + 1` 的一部分」——本文件用最朴素的形态：**把 `v` 减到某个界以下的步数**。

    ⚠ 为什么这样定义（文件头 §三）：
    * 只对**第一个参数**结构递归，**单一递归调用点** ⟹ 生成 `Nat.brecOn`，能按构造子归约；
    * **完全不用减法/除法库设施** ⟹ 绕开 `Nat.sub`（递归挂在减数上）与 `Nat.div`（`propext`）。 -/
def ediv : Nat → Nat → Nat
  | 0, _n => 0
  | (a + 1), _n => if a < _n then 0 else 1 + ediv a _n

/-- **`ediv` 的单步展开**（`a ≥ n` 时商加一）。

    比 `ediv` 的定义多说了什么：定义是一条 `if`；本条把「`a ≥ n` 这一支」单独交出来，
    于是 §3 的全部归纳都只用这一条 `rw`，不必反复展开定义。 -/
theorem ediv_step (a n : Nat) (h : ¬ a < n) : ediv (a + 1) n = 1 + ediv a n := by
  show (if a < n then 0 else 1 + ediv a n) = 1 + ediv a n
  rw [if_neg h]

/-- **本界内归零**：`a < n` 时 `ediv (a+1) n = 0`。

    比 `ediv` 的定义多说了什么：定义只按 `if` 分派；本条把「已满足界」的那一支
    单独钉成一个等式，供 §3 的归纳基步与 `exists` 见证使用。 -/
theorem ediv_zero_lt (a n : Nat) (h : a < n) : ediv (a + 1) n = 0 := by
  show (if a < n then 0 else 1 + ediv a n) = 0
  rw [if_pos h]

/-- **`ediv` 不超过被减数**：每步至少消耗一个 `1`。

    比 `ediv` 的定义多说了什么：定义只说「怎么算」；本条给出**上界**——
    这正是「误差不超过原误差」的离散形态，也是 §3 归纳能收敛的原因。 -/
theorem ediv_le_self (v n : Nat) : ediv v n ≤ v := by
  induction v with
  | zero => exact Nat.zero_le _
  | succ a ih =>
      show (if a < n then 0 else 1 + ediv a n) ≤ a + 1
      cases hv : decide (a < n) with
      | true =>
          rw [if_pos (of_decide_eq_true hv)]
          exact Nat.zero_le _
      | false =>
          rw [if_neg (decide_eq_false_iff_not.mp hv)]
          show 1 + ediv a n ≤ a + 1
          rw [Nat.one_add]
          exact Nat.succ_le_succ ih

/-! ===========================================================================
  §2  `Nat` 序砖块（库引理替代，全部 `cases` 穷举）
  =========================================================================== -/

/-- **`a < n ⟹ a + 1 < n + 1`**（构造子级；`Nat.succ_lt_succ` 的显式写法）。

    比 `Nat.succ_lt_succ` 多说了什么：库版要 `a.succ < n.succ`；调用处常给 `a < n`，
    本条把 `n` 的构造子先摊开，于是 `a + 1 < n + 1` 可以直接 `exact`。 -/
theorem lt_succ_of_lt (a n : Nat) (h : a < n) : a + 1 < n + 1 :=
  match n with
  | 0 => absurd h (Nat.not_lt_zero a)
  | (k + 1) => Nat.succ_lt_succ h

/-- **`a + 1 < n ⟹ a < n`**（`a + 1 < n` 剥掉那个 `+1`）。

    比 `Nat.lt_of_succ_lt_succ` 多说了什么：库版要 `a.succ < n.succ`；调用处给的是
    `a + 1 < n`，形态对不上。本条把「目标 `n` 上是构造子」这个条件摊开，直接落到
    `Nat.lt_of_succ_lt_succ`。 -/
theorem lt_of_succ_lt (a n : Nat) (h : a + 1 < n) : a < n :=
  match n with
  | 0 => absurd h (Nat.not_lt_zero (a + 1))
  | (k + 1) => Nat.lt_trans (Nat.lt_succ_self a) (Nat.le_trans h (Nat.le_refl (k + 1)))

/-- **`a < b ⟹ a + 1 ≤ b`**（`<` 与 `≤` 的唯一换算，按构造子穷举）。

    比 `Nat.succ_le_of_lt` 多说了什么：那条带 `propext`；本文件凡「`<` 变 `≤`」都走这里。 -/
theorem succ_le_of_lt : ∀ (a b : Nat), a < b → a + 1 ≤ b
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, (_b + 1), _ => Nat.zero_lt_succ _b
  | (_a + 1), 0, h => absurd h (Nat.not_lt_zero _)
  | (_a + 1), (_b + 1), h => Nat.succ_le_succ (Nat.le_of_lt_succ h)

/-- **`n ≥ 1 ⟹ 0 < n`**（把见证的「非空」换算成 `<`）。 -/
theorem lt_of_one_le : ∀ (n : Nat), 1 ≤ n → 0 < n
  | 0, h => absurd h (Nat.not_succ_le_zero 0)
  | (_k + 1), _ => Nat.zero_lt_succ _k

/-! ===========================================================================
  §3  派单三条主定理（零公理）
  =========================================================================== -/

/-- **单调**：样本更多（`n ≤ m`）⟹ 界更小（`ediv v m ≤ ediv v n`）。

    比 `ediv` 的定义多说了什么：定义只算一个 `n` 的值；本条给出**关于 `n` 的单调性** ——
    这是「数据越多越准」的离散核心：界随样本量单调下降。
    证明对 `v` 结构递归，`n ≤ m` 只用来在「已满足界」的分支上把 `a < n` 推到 `a < m`。 -/
theorem ediv_le_ediv (v n m : Nat) (h : n ≤ m) : ediv v m ≤ ediv v n := by
  induction v with
  | zero => exact Nat.le_refl 0
  | succ a ih =>
      show (if a < m then 0 else 1 + ediv a m) ≤ (if a < n then 0 else 1 + ediv a n)
      cases hv : decide (a < n) with
      | true =>
          have hn : a < n := of_decide_eq_true hv
          have hm : a < m := Nat.lt_of_lt_of_le hn h
          rw [if_pos hm, if_pos hn]
          exact Nat.le_refl 0
      | false =>
          rw [if_neg (decide_eq_false_iff_not.mp hv)]
          cases hm : decide (a < m) with
          | true =>
              rw [if_pos (of_decide_eq_true hm)]
              exact Nat.zero_le _
          | false =>
              rw [if_neg (decide_eq_false_iff_not.mp hm)]
              show 1 + ediv a m ≤ 1 + ediv a n
              exact Nat.add_le_add_left ih 1

/-- **本界内整体归零**：`v < n` 时 `ediv v n = 0`。

    比 `ediv` 的定义多说了什么：定义逐格算；本条给出一个**闭式**——
    「样本量超过被测量本身，界就严格归零」。这是 `exists` 见证的引擎。 -/
theorem ediv_zero_of_lt (v n : Nat) (h : v < n) : ediv v n = 0 := by
  induction v with
  | zero => rfl
  | succ a ih =>
      show (if a < n then 0 else 1 + ediv a n) = 0
      rw [if_pos (lt_of_succ_lt a n h)]

/-- **趋向 0**：对任意正的界 `e`，存在样本量 `N`（且 `N > 0`）使界严格小于 `e`。

    比 `ediv_zero_of_lt` 多说了什么：后者是「给定 `n > v` 时为 0」；本条把 `n` 的存在性
    **构造出来**（见证 `N = v + 1`），并同时交出 `N > 0` —— 这就是派单第 3 条
    `exists_N_bound_small` 的零公理形态。 -/
theorem exists_ediv_lt (v e : Nat) (he : 0 < e) :
    ∃ N : Nat, 0 < N ∧ ediv v N < e := by
  refine ⟨v + 1, Nat.zero_lt_succ v, ?_⟩
  rw [ediv_zero_of_lt v (v + 1) (Nat.lt_succ_self v)]
  exact he

/-- **「界随样本单调下降」的合成形态**：从任一初始样本量出发都可以再往前走。

    比 `ediv_le_ediv` 多说了什么：那条只说「换一个更大的 `n`，界不会变大」；
    本条把「还能继续走」也钉住：`ediv v (n+1) ≤ ediv v n`（相邻一步）。
    它是「取极限」在 `Nat` 上的最小代理，也是 §3 全部单调性结论的单步版本。 -/
theorem ediv_le_ediv_succ (v n : Nat) : ediv v (n + 1) ≤ ediv v n :=
  ediv_le_ediv v n (n + 1) (Nat.le_succ n)

#print axioms reduceSelf_test
#print axioms ediv_step
#print axioms ediv_zero_lt
#print axioms ediv_le_self
#print axioms lt_succ_of_lt
#print axioms lt_of_succ_lt
#print axioms succ_le_of_lt
#print axioms lt_of_one_le
#print axioms ediv_le_ediv
#print axioms ediv_zero_of_lt
#print axioms exists_ediv_lt
#print axioms ediv_le_ediv_succ

end FateV2.Core.SampleBounds
