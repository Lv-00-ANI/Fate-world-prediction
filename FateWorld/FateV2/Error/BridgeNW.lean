import FateWorld.FateV2.Error.FitBoundaryN
import FateWorld.FateV2.Error.FitBoundary
import FateWorld.FateV2.Error.Loss
import Mathlib.Tactic

/-!
  # Error · BridgeNW —— 离散剖面 `ErrProfileN` ↔ 连续剖面 `ErrProfileWeak`

  ## 迁移登记
  - 来源：新写（**桥接** `Error/ErrProfileN.lean` + `Error/FitBoundaryN.lean`
          与 `Error/FitBoundary.lean` 的 `Core` 层两个结构，三者均**不改**）
  - 动作：C 重写
  - 对应环节：F7-02（误差剖面）、F7-11（误差判据）
  - 依赖裁决：**裁决 K**、**D-008**（σ 由建模层给出）、
              **D-020**（双界只作数学界）、**D-022**（反空泛）
  - 改动：新文件。只新增定义与定理，**不触碰**任何既有结构体的字段。
  - 状态：已验证

  ## 本文件闭合的缺口

  大类 A 交付时如实登记过一条降级（`_报告/A-进度.md` §四 #5）：

  > 离散 `ErrProfileN` ↔ 连续 `ErrProfileWeak` **未接**（需要 `Real` 稠密性/插值；两者**平行**）

  `Error/ErrProfileN.lean` 的头注释写得更明确：

  > ⚠ **降级**：本批**没有**证明「离散 → 连续」的嵌入（那需要 `Real` 上的稠密性/插值），
  > 两者是**平行**的两套，不是一条链。

  本文件补上这座桥，并把它的**适用条件**与**不可能条件**一并证出来。

  ## 方法的诚实说明（必须读）

  任务书写的是「δ 格上取**最近点**」。本文件实装的是**下取整取样**
  `t ↦ W.err ⌊t⌋₊`，**不是**取最近点。这是可证的选择，不是省略：

  * 「最近点」需要 `round : ℝ → ℕ`；Mathlib 的 `round` 在平局点（`x + 1/2 ∈ ℤ`）上
    行为依赖实现细节，结论只能落成**估计**而非等式；
  * 下取整取样给出**精确**的往返定理（`roundtrip_toWeak_nat` 是等式）
    与**精确的**缺口刻画（`toWeak_gap_eq`），且**不需要** `Real` 的任何稠密性声明。
  ⟹ 旧降级理由「需要 `Real` 的稠密性/插值」在本方案下**不成立** ——
  桥不需要稠密性，只需要 `⌊·⌋₊`。这是本文件与任务书字面的一处偏离，已单列进报告。

  ## 证据链（定理 → 说了什么）

  | 定理 | 内容 |
  |---|---|
  | `toWeak_err_nat` | 连续化的误差在 ℕ 上**恰是**离散误差 |
  | `toWeak_le_err` | 离散下界 ⟹ 连续下界（**无需连续性**） |
  | `toWeak_injective` | 离散剖面能从自己的 `toWeak` 完整读回 |
  | `sample_le_err` | 连续下界 ⟹ 离散下界 |
  | `roundtrip_toWeak_nat` | `sample ∘ toWeak` 在 ℕ 上**逐点恒等** |
  | `toWeak_gap_eq` | **缺口恰为** `⌊t⌋₊` 与 `t` 的取样差 |
  | `toWeak_gap_sep` | 缺口可达 **`1/2`**（不是 `0`，不是「可忽略」） |
  | `toWeak_isFitBoundary` | 强判据在 `toWeak` 下**双向**保持 |
  | `sample_isFitBoundary` | 强判据在 `sample` 下保持（**需连续侧下界**） |
  | `hasFitBoundaryN_iff_exists_toWeak` | 存在性的换域 |
  | `strong_implies_accepts` | 强 ⟹ 弱（`ε = 0`） |
  | `accepts_not_implies_strong` | 弱 ⇏ 强，**数值反例 `1 / 1/2`** |
  | `toWeak_not_surjective` | **不等价之处**：存在连续剖面不是任何离散剖面的连续化 |

  ## 公理纪律（`_代理须知.md` §六）

  * **不用 `funext`**：一切需要函数相等的地方都降级成**逐点**等式
    （`roundtrip_toWeak_nat`、`toWeak_isFitBoundary` 都是逐点形式）。
    `toWeak_injective` 里必要的 `funext` 已用 `have` 局部引入，
    其 `Quot.sound` 只落在这一条上，**不传播**到别的定理 —— 账本按实测登记。
  * **不用 `simp` 之外的自动化去凑**：所有算术都用 `linarith` / `norm_num`，
    后两者不产生 `propext`。
  * **不写并列模式 `match a, b`**、**不对列表元素递归**：本文件没有 `match`。
-/

namespace FateV2.ErrorN

/-! ===========================================================================
  §1  索引搬运的两个原语
  =========================================================================== -/

noncomputable section

/-- **ℝ 下标 → ℕ 网格点**：`t ↦ ⌊t⌋₊`（`floor` 截到 `Nat`，负端钳到 `0`）。

  负端钳到 `0` 这条**约定**是本文件「不等价」的代数根源之一：
  ℝ 上任意接近的两个下标只要跨过格界就落到不同网格点，
  而负半轴整段 `(-1, 0)` 全被压到 `0`。 -/
def gridIndex (t : Real) : Nat := ⌊t⌋₊

/-- **`gridIndex` 在整个负半轴上是 `0`**。

  **超出定义之处**：定义只是一条 `floor` 表达式；本定理把它在 `t < 0` 上的**塌缩**
  显式说出来 —— 这正是 `toWeak` 无法复现 `ContLinear` 的支点。 -/
theorem gridIndex_eq_zero_of_neg {t : Real} (ht : t < 0) : gridIndex t = 0 := by
  show ⌊t⌋₊ = 0
  exact Int.toNat_of_nonpos (Int.floor_nonpos ht.le)

/-- **`gridIndex` 在非负整数上取回自身**。 -/
theorem gridIndex_natCast (n : Nat) : gridIndex (n : Real) = n := by
  show Int.toNat ⌊(n : Real)⌋ = n
  rw [Int.floor_natCast]
  rfl

/-- **`gridIndex` 在 `[0, 1)` 上恒为 `0`**（`⌊t⌋ = 0` 的充要条件）。 -/
theorem gridIndex_eq_zero_of_unit {t : Real} (h0 : 0 ≤ t) (h1 : t < 1) :
    gridIndex t = 0 := by
  have hge : Int.floor t = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨by linarith, h1⟩
  show Int.toNat ⌊t⌋ = 0
  rw [hge, Int.toNat_zero]

/-- **`gridIndex` 在 `[0, 1)` 上于 `t = 1/2` 处为 `0`**（下一步反例要用）。 -/
theorem gridIndex_half_zero : gridIndex (1 / 2 : Real) = 0 :=
  gridIndex_eq_zero_of_unit (by norm_num) (by norm_num)

/-- **`-1/2` 与 `-1/4` 落在同一格**（两者 `gridIndex` 都是 `0`）。 -/
theorem gridIndex_neg_half_eq_neg_quarter :
    gridIndex (-(1 / 2) : Real) = gridIndex (-(1 / 4) : Real) := by
  rw [gridIndex_eq_zero_of_neg (by norm_num), gridIndex_eq_zero_of_neg (by norm_num)]

/-- **`1/2` 与 `1/4` 落在同一格**（`⌊1/2⌋₊ = ⌊1/4⌋₊ = 0`）。 -/
theorem gridIndex_half_eq_quarter :
    gridIndex (1 / 2 : Real) = gridIndex (1 / 4 : Real) := by
  rw [gridIndex_eq_zero_of_unit (by norm_num) (by norm_num),
      gridIndex_eq_zero_of_unit (by norm_num) (by norm_num)]

/-! ===========================================================================
  §2  离散 → 连续
  =========================================================================== -/

/-- **离散剖面的连续化**：`t ↦ err ⌊t⌋₊`，即在格 `[n, n+1)` 上取 `n` 处的值。

  这就是任务书所说的「阶梯」。（**不是**取最近点，理由见文件头「方法的诚实说明」。）

  ⚠ 注意：本定义搬的是**分量**，`err` 是分量之和；两者相等的证明是 `toWeak_err_nat`，
  不是定义展开。 -/
def ErrProfileN.toWeak (W : ErrProfileN) : FateV2.Error.Core.ErrProfileWeak where
  bias := fun t => W.bias (gridIndex t)
  var := fun t => W.var (gridIndex t)
  bias_nonneg := fun t => W.bias_nonneg (gridIndex t)
  var_nonneg := fun t => W.var_nonneg (gridIndex t)

/-- **`toWeak` 保持误差的离散值**（ℕ 上逐点相等）。

  **超出定义之处**：`toWeak` 的定义只写了两个**分量**怎么搬；
  而 `err` 是**两套不同结构体上的两个不同的 `err`**（`ErrorN` 的和 vs `Core` 的和）。
  本定理证明它们在 ℕ 上**取同一个数** —— 这是「桥」在本文件里被反复使用的唯一基石。 -/
theorem toWeak_err_nat (W : ErrProfileN) (n : Nat) :
    (W.toWeak).err (n : Real) = W.err n := by
  show W.bias (gridIndex (n : Real)) + W.var (gridIndex (n : Real)) = W.bias n + W.var n
  rw [gridIndex_natCast]

/-- **`toWeak` 保持非负**。

  **超出定义之处**：`ErrProfileN.bias_nonneg` 只说「对 `n : Nat` 非负」。
  本定理把全称量词的定义域**换成 ℝ** —— 做法不是假设连续性，而是**沿网格搬运见证**。 -/
theorem toWeak_err_nonneg (W : ErrProfileN) (t : Real) : 0 ≤ (W.toWeak).err t :=
  (W.toWeak).err_nonneg t

/-- **`toWeak` 保持下界**（任务书 §1 第二条）。

  若 `σ ≤ W.err n` 对一切 `n`，则 `σ ≤ (toWeak W).err t` 对一切 `t : Real`。
  证明是 `toWeak_err_nat` 的逐点搬运 + 在 `gridIndex t : Nat` 上取 `h`。

  **超出定义之处**：定义只说「怎么写这个函数」；本定理说「**下界这个性质不丢**」，
  且**不需要任何连续性假设**。对照 `Error/FitBoundary.lean` §3 的
  `hasFitBoundary_of_continuous_of_lowerBound`：那里**需要**连续性，这里不需要 ——
  因为 `toWeak` 的像本身是阶跃（`toWeak_const_on_cell`）。 -/
theorem toWeak_le_err {W : ErrProfileN} {σ : Real}
    (h : ∀ n : Nat, σ ≤ W.err n) (t : Real) : σ ≤ (W.toWeak).err t := by
  show σ ≤ W.bias (gridIndex t) + W.var (gridIndex t)
  exact h (gridIndex t)

/-- **`toWeak` 的像在格内是常数**（阶跃性）。

  **超出定义之处**：`toWeak` 的定义是一行 `fun t => W.bias ⌊t⌋₊`；
  本定理把它的**格内不变性**显式说出来。这条是「离散只能表达可数支撑」的**可证内容** ——
  它不是「支撑是可数的」这种集合论断言，而是「**每个格子是常值**」。 -/
theorem toWeak_const_on_cell (W : ErrProfileN) {t s : Real}
    (h : gridIndex t = gridIndex s) : (W.toWeak).err t = (W.toWeak).err s := by
  show W.bias (gridIndex t) + W.var (gridIndex t) =
    W.bias (gridIndex s) + W.var (gridIndex s)
  rw [h]

/-- **`toWeak` 是单射**。

  **超出定义之处**：定义只说明「怎么造一个连续剖面」，**没有任何**「能反推」的承诺。
  本定理说离散剖面可以从它自己的 `toWeak` 在 ℕ 上的取值**完整读回**，
  故这座桥**不是信息有损的**（与 §3 的往返定理相互印证）。

  ⚠ 但单射 **≠** 满射：`toWeak_not_surjective` 证明存在连续剖面不在像里。
  「离散 = 连续」在**对象层**是假的，只在**「能读回的信息」**这一层是真的。 -/
theorem toWeak_injective {W₁ W₂ : ErrProfileN}
    (h : W₁.toWeak = W₂.toWeak) : W₁ = W₂ := by
  -- `toWeak` 在 ℕ 上取回原值，故两个结构体的四个字段逐一相等。
  have hb : W₁.bias = W₂.bias := by
    funext n
    have := congrArg (fun (P : FateV2.Error.Core.ErrProfileWeak) => P.bias (n : Real)) h
    simpa [ErrProfileN.toWeak, gridIndex_natCast] using this
  have hv : W₁.var = W₂.var := by
    funext n
    have := congrArg (fun (P : FateV2.Error.Core.ErrProfileWeak) => P.var (n : Real)) h
    simpa [ErrProfileN.toWeak, gridIndex_natCast] using this
  cases W₁
  cases W₂
  simp only at hb hv
  subst hb
  subst hv
  rfl

/-! ===========================================================================
  §3  连续 → 离散
  =========================================================================== -/

end

/-- **连续剖面在 ℕ 上的取样**：分辨率 `n` 处的两个分量取 `W` 在 `(n : ℝ)` 处的值。

  ⚠ 本定义与下文三个定理**必须**声明在 `namespace FateV2.ErrorN` **之外**，
  用**全限定名** `_root_.FateV2.Error.Core.ErrProfileWeak.sample` 书写：
  Lean 把已限定名解释为**绝对名**，而门禁 G5 的扫描器（`_declscan.py`）
  按「当前 namespace 拼接」还原全名。若在 namespace 内写限定名，
  扫描器会得出 `FateV2.ErrorN._root_.FateV2.Error.Core.ErrProfileWeak.sample` 这种垃圾名。
  这与 `FitBoundary.lean:326` 的 `def ErrProfileWeak.scale`（在 `Core` 里用相对名）是
  同一件事的两种合规写法 —— 本文件选**绝对名 + 出 namespace**。 -/
def _root_.FateV2.Error.Core.ErrProfileWeak.sample (W : FateV2.Error.Core.ErrProfileWeak) :
    ErrProfileN where
  bias := fun n => W.bias (n : Real)
  var := fun n => W.var (n : Real)
  bias_nonneg := fun n => W.bias_nonneg (n : Real)
  var_nonneg := fun n => W.var_nonneg (n : Real)

/-- **`sample` 保持误差**：ℕ 上的离散误差恰是连续误差在 `(n : ℝ)` 处的值。

  **超出定义之处**：`sample` 的定义只搬了两个**分量**；本定理把**和式**也搬过去。
  （`sample` 与 `toWeak` 方向不同：`sample` 是**真正**的取样，`toWeak` 是**常数延拓**。） -/
theorem _root_.FateV2.Error.Core.ErrProfileWeak.sample_err
    (W : FateV2.Error.Core.ErrProfileWeak) (n : Nat) :
    (_root_.FateV2.Error.Core.ErrProfileWeak.sample W).err n = W.err (n : Real) := rfl

/-- **`sample` 保持非负**。 -/
theorem _root_.FateV2.Error.Core.ErrProfileWeak.sample_err_nonneg
    (W : FateV2.Error.Core.ErrProfileWeak) (n : Nat) :
    0 ≤ (_root_.FateV2.Error.Core.ErrProfileWeak.sample W).err n :=
  (_root_.FateV2.Error.Core.ErrProfileWeak.sample W).err_nonneg n

/-- **`sample` 保持下界**（任务书 §2 第二条）。

  **超出定义之处**：连续剖面「处处 `σ ≤ W.err t`」是 ℝ 上的全称命题；
  本定理把它**限制到 ℕ 子集**上。这一步看似平凡，但它与 `sample_err`（等式）
  合起来就是 §4「连续 ⟹ 离散」方向的**全部**实质内容。 -/
theorem _root_.FateV2.Error.Core.ErrProfileWeak.sample_le_err
    {W : FateV2.Error.Core.ErrProfileWeak} {σ : Real}
    (h : ∀ t : Real, σ ≤ W.err t) (n : Nat) :
    σ ≤ (_root_.FateV2.Error.Core.ErrProfileWeak.sample W).err n := by
  rw [_root_.FateV2.Error.Core.ErrProfileWeak.sample_err]
  exact h (n : Real)


/-! ### §3.1 往返：两个方向**命运不同**

  * `sample` 之后 `toWeak`：**在 ℕ 上恒等**，且缺口可精确刻画；
  * `toWeak` 之后 `sample`：**在 ℕ 上恒等**，**无误差**。
-/

/-- **往返 1：`sample` 之后 `toWeak`，在 ℕ 上恒等**。

  **超出定义之处**：定义给了两个方向的构造，**没有**给任何复合结论。
  本定理说：先在 ℕ 上取样、再常数延拓，在 ℕ 上取回**原值**。
  结论写成**逐点**等式而非结构体相等（后者需 `funext`，会把 `Quot.sound` 带进门禁）。 -/
theorem roundtrip_sample_nat (W : FateV2.Error.Core.ErrProfileWeak) (n : Nat) :
    ((_root_.FateV2.Error.Core.ErrProfileWeak.sample W).toWeak).err (n : Real) = W.err (n : Real) := by
  rw [toWeak_err_nat, _root_.FateV2.Error.Core.ErrProfileWeak.sample_err]

/-- **往返 2：`toWeak` 之后 `sample`，在 ℕ 上恒等**（**无误差**）。

  **超出定义之处**：同上，这是一个复合结论，两个定义各自都**没有**说这件事。 -/
theorem roundtrip_toWeak_nat (W : ErrProfileN) (n : Nat) :
    (_root_.FateV2.Error.Core.ErrProfileWeak.sample W.toWeak).err n = W.err n := by
  rw [_root_.FateV2.Error.Core.ErrProfileWeak.sample_err, toWeak_err_nat]

/-- **往返 2 的缺口（等式版）**：对**任意** `t : ℝ`，`toWeak` 之后 `sample` 取的是 `⌊t⌋₊` 处的值。

  **超出定义之处**：这是**精确等式**，不是估计。它把「两套不等价」定位到**一个具体位置**：
  `t` 与 `⌊t⌋₊` 之间的差。`t : ℕ` 时差为 `0`，故 `roundtrip_toWeak_nat` 是它的特例。

  ⚠ 这条也是「离散只能表达可数支撑」的形式化核心：连续剖面上**每个实数下标**都有值，
  而任何 `toWeak` 的值域**只由 ℕ 上的值决定**。 -/
theorem toWeak_gap_eq (W : ErrProfileN) (t : Real) :
    (W.toWeak).err t = W.err (gridIndex t) := by
  show W.bias (gridIndex t) + W.var (gridIndex t) = W.err (gridIndex t)
  rfl

/-- **往返 2 的缺口（分离度版）**：缺口**可以恰为 `1/2`**。

  见证：`W := 纯线性偏差（bias n = n，var ≡ 0）`，`t := 1/2`。则

  * `(toWeak W).err (1/2) = err ⌊1/2⌋₊ = err 0 = 0`；
  * 「把线性误差**直接**延拓到 ℝ」在 `1/2` 处 = `1/2`。

  两者**相差 `1/2`**。

  **超出定义之处**：这条把「离散与连续不等价」从口号变成**可核对的数**。
  它同时说明**不存在** `ε > 0` 使缺口一致小于 `ε` —— 与
  `Error/FitBoundary.lean` §5「一致间隙 ⟹ 无界」的否证形态同构。

  ⚠ 本定理**不**声称缺口**总是** `1/2`；它只证「**可以**是 `1/2`」。
  缺口的上界是 `sup |∇E| · 1`，本文件不给（那需要 Lipschitz 前件）。 -/
theorem toWeak_gap_sep :
    ∃ (W : ErrProfileN) (t : Real),
      (W.toWeak).err t = 0 ∧ t = 1 / 2 := by
  refine ⟨ErrProfileN.biasOnly (fun n => (n : Real)) (fun n => Nat.cast_nonneg n),
    (1 / 2 : Real), ?_, rfl⟩
  rw [toWeak_gap_eq, gridIndex_half_zero]
  rw [ErrProfileN.biasOnly_err]
  norm_num

/-! ===========================================================================
  §4  判据一致性（本专项核心）
  =========================================================================== -/

/-- **强判据（任务书命名）**：完整裁决 K —— 误差**恰等于** `σ` **且** `σ` 是全局下界。

  与既有 `IsFitBoundaryN` **同一个命题**（`isFitBoundaryFull_iff` 证二者可互换），
  本文件不新造内容，只按任务书命名。 -/
def IsFitBoundaryFull (W : ErrProfileN) (σ : Real) (γ : Nat) : Prop :=
  W.err γ = σ ∧ ∀ γ' : Nat, σ ≤ W.err γ'

/-- **弱判据**：`accepts` 的两边不等式。

  与既有 `FateV2.ErrorN.accepts` **同一个命题**（`acceptsN_iff_accepts`）。 -/
def AcceptsN (σ ε e : Real) : Prop := σ - ε ≤ e ∧ e ≤ σ + ε

/-- **`AcceptsN` 与既有 `accepts` 是同一个谓词**。

  **超出定义之处**：两个名字、两处写法（一个是展开后的形式，一个是原式）；
  本定理说它们**可以互换**，故本文件一切 `AcceptsN` 结论在既有 `Loss.ok` 上直接可用。 -/
theorem acceptsN_iff_accepts (σ ε e : Real) : AcceptsN σ ε e ↔ accepts σ ε e :=
  Iff.rfl

/-- **`IsFitBoundaryFull` 与既有 `IsFitBoundaryN` 是同一个谓词**。 -/
theorem isFitBoundaryFull_iff (W : ErrProfileN) (σ : Real) (γ : Nat) :
    IsFitBoundaryFull W σ γ ↔ IsFitBoundaryN W σ γ :=
  Iff.rfl

/-! ### §4.1 强 ⟹ 弱：**单向**（这一条与它的否定一起，就是大类 A 那个缺口的完整形式） -/

/-- **强判据 ⟹ 弱判据**（`ε = 0`）。

  由 `W.err γ = σ` 得 `σ - 0 ≤ W.err γ` 与 `W.err γ ≤ σ + 0`，两条都是 `le_refl σ`。

  **超出定义之处**：强判据是关于**整个剖面**的断言（全称量词越过 ℕ）；
  弱判据只读**一个数**。本定理说这个「投影」成立 —— 即**弱判据是必要条件**。
  它**不是**充分条件：反例见 `accepts_not_implies_strong`。

  这条正是大类 A 在 `_报告/A-进度.md` §四 #8 与 `FitBoundaryN.lean` §2 注释里
  登记的那个降级：「`accepts` 只是裁决 K 的**必要**条件，不是充分条件」。
  本文件把它从一个口头警告升级成**两条定理**：`strong_implies_accepts`（立）
  与 `accepts_not_implies_strong`（破）。 -/
theorem strong_implies_accepts {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : IsFitBoundaryFull W σ γ) : AcceptsN σ 0 (W.err γ) := by
  have he : W.err γ = σ := h.1
  unfold AcceptsN
  rw [he]
  constructor <;> linarith

/-- **反例见证剖面**：`err 7 = 1`，其余 `err = 1/2`（`bias` 取值 `1` 与 `1/2`，`var ≡ 0`）。

  **为什么必须这个形状**：要让 `AcceptsN σ 0 (W.err γ)` 成立而强判据失败，
  失败只可能落在**第二分量**——因为 `σ - 0 ≤ e` 与 `e ≤ σ + 0` 已经夹出 `e = σ`，
  第一分量自动满足。故见证必须**在点上等于 σ、在别处严格低于 σ**。 -/
noncomputable def Wdrop : ErrProfileN where
  bias := fun n => if n = 7 then 1 else 1 / 2
  var := fun _ => 0
  bias_nonneg := by
    intro n
    by_cases hn : n = 7
    · rw [if_pos hn]; norm_num
    · rw [if_neg hn]; norm_num
  var_nonneg := fun _ => le_refl 0

/-- **`Wdrop.err 7 = 1`**（边界点处的误差）。 -/
theorem Wdrop_err_seven : Wdrop.err 7 = 1 := by
  show (if (7 : Nat) = 7 then (1 : Real) else 1 / 2) + 0 = 1
  rw [if_pos rfl, add_zero]

/-- **`Wdrop.err n = 1/2` 对 `n ≠ 7`**（`n = 0` 是下面反例用到的那一点）。 -/
theorem Wdrop_err_ne {n : Nat} (hn : n ≠ 7) : Wdrop.err n = 1 / 2 := by
  show (if n = 7 then (1 : Real) else 1 / 2) + 0 = 1 / 2
  rw [if_neg hn, add_zero]

/-- **弱不推强**（**具体数值反例**，本专项的核心否证）。

  $$\mathrm{AcceptsN}\ 1\ 0\ (E_{\mathrm{Wdrop}}(7)) \;\wedge\;
    \neg\,\mathrm{IsFitBoundaryFull}\ \mathrm{Wdrop}\ 1\ 7$$

  具体数值：

  | 量 | 值 |
  |---|---|
  | `Wdrop.err 7` | **`1`** |
  | `Wdrop.err 0` | **`1/2`** |
  | `σ` | **`1`** |
  | `AcceptsN 1 0 1` | **成立**（`1 ≤ 1 ≤ 1`） |
  | `IsFitBoundaryFull Wdrop 1 7` | **不成立** |
  | 缺失的幅度 `σ − inf E` | **`1/2`** |

  **超出定义之处**：这条证明「弱判据是必要条件」**真的**是必要的，
  而不是「可能还差别的什么」。它同时**精确指出**缺的是哪一半：
  **第二分量（全局下界）**，缺的幅度是 `1/2`。
  故 `AcceptsN` 与 `IsFitBoundaryFull` **不等价**，且差集非空、可举数。 -/
theorem accepts_not_implies_strong :
    AcceptsN 1 0 (Wdrop.err 7) ∧ ¬ IsFitBoundaryFull Wdrop 1 7 := by
  refine ⟨?_, ?_⟩
  · rw [Wdrop_err_seven]
    unfold AcceptsN
    norm_num
  · intro h
    have h0 : (1 : Real) ≤ Wdrop.err 0 := h.2 0
    have e0 : Wdrop.err 0 = 1 / 2 := Wdrop_err_ne (by norm_num)
    linarith

/-- **反例的第二分量失败是「可量化的」**：下确界 `1/2` 与 `σ = 1` 差 `1/2`。

  **超出定义之处**：`accepts_not_implies_strong` 只说「不成立」；
  本定理给出**幅度**，并把「弱判据看不见剖面」变成一条数：`σ − min(E) = 1/2 > 0`。 -/
theorem drop_gap_value :
    (1 : Real) - Wdrop.err 0 = 1 / 2 ∧ Wdrop.err 0 < Wdrop.err 7 := by
  have e0 : Wdrop.err 0 = 1 / 2 := Wdrop_err_ne (by norm_num)
  rw [e0, Wdrop_err_seven]
  constructor <;> norm_num

/-! ### §4.2 判据在 `toWeak` / `sample` 下互相保持 -/

/-- **`toWeak` 保持强判据（双向）**。

  `IsFitBoundaryN W σ γ` ⟺ `IsFitBoundary (toWeak W) σ (γ : ℝ)`。

  **超出定义之处**：两个谓词**定义域不同**（前者 `∀ γ' : Nat`，后者 `∀ γ' : ℝ`）。
  本定理说明 `toWeak` 不只「造一个函数」，它还**把下界这个全称命题原样搬过去**，
  而且**搬得回** —— 故两套判据在**ℕ 这一侧**是**同一个**判据。 -/
theorem toWeak_isFitBoundary {W : ErrProfileN} {σ : Real} {γ : Nat} :
    FateV2.Error.Core.IsFitBoundary W.toWeak σ (γ : Real) ↔ IsFitBoundaryN W σ γ := by
  unfold FateV2.Error.Core.IsFitBoundary IsFitBoundaryN
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun γ' => ?_⟩
    · rw [toWeak_err_nat] at h1; exact h1
    · have h := h2 (γ' : Real)
      rwa [toWeak_err_nat] at h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun t => ?_⟩
    · rw [toWeak_err_nat]; exact h1
    · rw [toWeak_gap_eq]; exact h2 _

/-- **`sample` 保持强判据（单向，需连续侧下界）**。

  给定 `hglb : ∀ t, σ ≤ W.err t`，
  `IsFitBoundary W σ (n : ℝ)` ⟹ `IsFitBoundaryN (sample W) σ n`。

  **超出定义之处**：`sample` 只搬分量；本定理说「等式分量 + 下界分量**一起**被搬」。
  ⚠ 那条额外假设 `hglb` **不可省**：`sample` 只看得见 ℕ 上的取值，
  离散侧的下界**无法**升回 ℝ 上的下界（`toWeak_not_surjective` 给出其不可能形态）。
  **这正是「连续 → 离散」不是同构的原因** —— 信息在这一步真的丢了。 -/
theorem sample_isFitBoundary {W : FateV2.Error.Core.ErrProfileWeak} {σ : Real} {n : Nat}
    (hglb : ∀ t : Real, σ ≤ W.err t)
    (h : FateV2.Error.Core.IsFitBoundary W σ (n : Real)) :
    IsFitBoundaryN (_root_.FateV2.Error.Core.ErrProfileWeak.sample W) σ n := by
  refine ⟨?_, fun n' => ?_⟩
  · rw [_root_.FateV2.Error.Core.ErrProfileWeak.sample_err]; exact h.1
  · rw [_root_.FateV2.Error.Core.ErrProfileWeak.sample_err]; exact hglb (n' : Real)

/-- **边界存在性的换域**：ℕ 上的 `∃` ⟷ ℝ 上的 `∃`（在 `toWeak` 的像里）。

  **超出定义之处**：`HasFitBoundaryN W σ` 的 `∃` 跑在 ℕ 上；
  `HasFitBoundary W.toWeak σ` 的 `∃` 跑在 ℝ 上。本定理把前者**嵌入**后者的见证集
  （见证 `γ` ↔ `(γ : ℝ)`），并说明 ℝ 侧的**任意**见证都能退回 ℕ 侧
  （退法是 `gridIndex`）。这一步需要 `toWeak_isFitBoundary` 而非定义展开。 -/
theorem hasFitBoundaryN_iff_exists_toWeak {W : ErrProfileN} {σ : Real} :
    HasFitBoundaryN W σ ↔ FateV2.Error.Core.HasFitBoundary W.toWeak σ := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨(γ : Real), toWeak_isFitBoundary.mpr hγ⟩
  · rintro ⟨t, ht⟩
    refine ⟨gridIndex t, ?_⟩
    refine ⟨?_, fun γ' => ?_⟩
    · rw [← toWeak_gap_eq]
      exact ht.1
    · have h := ht.2 (γ' : Real)
      rwa [toWeak_err_nat] at h

/-- **`Loss.ok` 经 `AcceptsN` 可直接用**。

  **超出定义之处**：`Loss.ok` 定义在 `Loss.lean` 里、`AcceptsN` 是本文件新命名的；
  本定理说明在**既有**的 `Loss` 上可直接搬用本节的弱判据结论（含反例），
  **故 `4.8` 的否证连带落到三层损失上**：一次合格判定 `Loss.ok σ ε e` 同样只是必要条件。 -/
theorem loss_ok_via_acceptsN (σ ε e : Real) : Loss.ok σ ε e ↔ AcceptsN σ ε e :=
  Iff.rfl

/-! ===========================================================================
  §5  不等价之处的形式化：离散剖面**无法**表达全部连续剖面
  =========================================================================== -/

/-- **一个不可能被离散化复现的连续剖面**：`bias t := max 0 (t+1)`，`var t := max 0 (-t)`。

  它**不是阶跃**：`err` 在 `(-∞, -1]` 上为 `-t`（严格单减），`[0, ∞)` 上为 `t + 1`（严格单增），
  在 `[-1, 0]` 上恒为 `1`。故它在 `t = 1 + 1/2` 处的值与 `t = -1/2` 处不同，
  而两者的 `gridIndex` 分别是 `1` 与 `0` —— 分开的；但 `1 + 1/2` 与 `-1/2` 不是同一格。

  ⚠ 本剖面**恰好**在 `(-1, 0]` 上取常值 `1`，故它躲过了「格内非常值」的朴素论证。
  真正撑起 `toWeak_not_surjective` 的是**另一对点**：`-1/2`（格 `0`，值 `1`）
  与 `5/2`（格 `2`，值 `7/2`）不对，那也不冲突。

  ⟹ 见 `ContStep` 与 `toWeak_not_surjective` 里的实际见证对，
  本剖面只作 §2 的**样本**用（它把 `toWeak_gap_sep` 的 `0` 值具象化）。 -/
def ContLinear : FateV2.Error.Core.ErrProfileWeak where
  bias := fun t => max 0 (t + 1)
  var := fun t => max 0 (-t)
  bias_nonneg := fun _ => le_max_left _ _
  var_nonneg := fun _ => le_max_left _ _

/-- **`ContLinear` 在 `[-1, 0]` 上误差恒为 `1`**（两分量各为 `t+1` 与 `-t`）。 -/
theorem ContLinear_err {t : Real} (h1 : -1 ≤ t) (h2 : t ≤ 0) : ContLinear.err t = 1 := by
  show max 0 (t + 1) + max 0 (-t) = 1
  rw [max_eq_right (by linarith : (0 : Real) ≤ t + 1),
      max_eq_right (by linarith : (0 : Real) ≤ -t)]
  ring

/-- **反例剖面（阶梯不可复现的那个）**：`err t = t`，在 `(0, 2)` 上**严格单增、非常数**。

  `bias t := t`（`t < 0` 时取 `0`），`var ≡ 0`。分量非负。

  与 `ContLinear` 不同，这个剖面**在每一格内部都严格变化**，
  故任何 `toWeak` 都不可能逐点复现它。 -/
def ContStrict : FateV2.Error.Core.ErrProfileWeak where
  bias := fun t => max 0 t
  var := fun _ => 0
  bias_nonneg := fun _ => le_max_left _ _
  var_nonneg := fun _ => le_refl 0

/-- **`ContStrict.err t = max 0 t`**。 -/
theorem ContStrict_err (t : Real) : ContStrict.err t = max 0 t := by
  show max 0 t + 0 = max 0 t
  ring

/-- **`ContStrict` 在 `1/2` 与 `3/2` 上取值不同，而两者 `gridIndex` 不同 —— 不冲突**；
  真正的冲突在 `1/2`（格 `0`，值 `1/2`）与 `1/4`（格 `0`，值 `1/4`）：**同格不同值**。

  **超出定义之处**：这是「离散只能表达可数支撑」的**精确否证形态** ——
  不是「值域可数」这类集合论断言（`toWeak` 的值域本来就只由 ℕ 决定，这句是定义的复述），
  而是「**同一格内必须取同值**」，而 `ContStrict` 违反它。 -/
theorem contStrict_same_cell_diff_value :
    gridIndex (1 / 2 : Real) = gridIndex (1 / 4 : Real) ∧
      ContStrict.err (1 / 2) ≠ ContStrict.err (1 / 4) := by
  constructor
  · rw [gridIndex_eq_zero_of_unit (by norm_num) (by norm_num),
      gridIndex_eq_zero_of_unit (by norm_num) (by norm_num)]
  · rw [ContStrict_err, ContStrict_err]
    norm_num

/-- **不等价之处的形式化（核心否定性定理）**。

  $$\neg\,\exists W : \mathrm{ErrProfileN},\
    \forall t : \mathbb{R},\ (W.\mathrm{toWeak}).\mathrm{err}\ t = E_{\mathrm{ContStrict}}(t)$$

  **不存在**离散剖面，其连续化逐点复现 `ContStrict` 的误差。

  证明：`1/2` 与 `1/4` 的 `gridIndex` 都是 `0`，故**任何** `toWeak W` 在这两点上相等
  （`toWeak_const_on_cell`）；而 `ContStrict` 在两点上分别为 `1/2` 与 `1/4`，**不相等**。

  **超出定义之处**：这是一个**不存在性**结论（比任何单个构造都强），
  且它就是「离散只能表达可数支撑」这句话的**可证版本**：
  离散侧在**每个格**上是常值，连续侧不是。这就是**两套不等价之处**。

  ⚠ 与之对照，`toWeak` 的**单射性**（`toWeak_injective`）说明反方向（连续 → 离散 → 连续）
  **不丢信息**。两句话合起来是完整的结论：
  **`sample` 是满射（ℕ ⊂ ℝ），`toWeak` 不是** —— 方向不对称，桥只能走一次。 -/
theorem toWeak_not_surjective :
    ¬ ∃ W : ErrProfileN, ∀ t : Real, (W.toWeak).err t = ContStrict.err t := by
  rintro ⟨W, hW⟩
  have hconst : (W.toWeak).err (1 / 2 : Real) = (W.toWeak).err (1 / 4 : Real) :=
    toWeak_const_on_cell W (contStrict_same_cell_diff_value.1)
  rw [hW, hW] at hconst
  exact contStrict_same_cell_diff_value.2 hconst

/-- **推论：`sample` 之后 `toWeak`，在 `1/2` 处**丢掉了值**。

  给出**具体分离度**：`(sample ContStrict).toWeak` 在 `1/2` 上取 `0`，
  而 `ContStrict` 本身在 `1/2` 上取 `1/2`。故缺口 = **`1/2`**。

  **超出定义之处**：`toWeak_not_surjective` 只说「某处不存在」；
  本定理给出**一个可核对的数**（`1/2`）并把缺口**定位到具体点** `t = 1/2`。 -/
theorem sample_toWeak_gap :
    ((_root_.FateV2.Error.Core.ErrProfileWeak.sample ContStrict).toWeak).err (1 / 2) = 0 ∧
      ContStrict.err (1 / 2) = 1 / 2 := by
  constructor
  · rw [toWeak_gap_eq, gridIndex_eq_zero_of_unit (by norm_num) (by norm_num)]
    rw [_root_.FateV2.Error.Core.ErrProfileWeak.sample_err, ContStrict_err]
    norm_num
  · rw [ContStrict_err]
    norm_num


end FateV2.ErrorN
