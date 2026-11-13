import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/TrajGenDeterministic.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Model（正文 13 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Model
open FateV2.Modeling

/-
命运理论 · 方案一：确定性递推（用 `Step` 迭代），轨迹由初值与输入唯一决定
=============================================================================

模块：FateV2.Model.TrajGenDeterministic
上游：`第9问-TrajGen三种实现方案.md`（方案 A/B/C/D）、`FateV2.Model/Frame.lean`（`Step`、`TrajGen`）、
　　　`FateV2.Model/Basic.lean`（`Traj`、`InitialState`、`NoiseSpace`、`Tmax`）。

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
把 `TrajGen`（`FateV2.Model/Frame.lean:160` 的固定类型）**正面实现**为
「沿时间正向**迭代** `Step`」—— 即**唯一权威离散方程**
    x_{t+1} = f(x_t, u_t, ε_t; θ, a_t)
在轨迹层的**定义性展开**。其输出是一条**确定性的样本路径** `Traj ι X`：
**给定初值 x₀、参数 θ、输入序 {u_t}、噪声序 {ε_t}、动作序 {a_t}，轨迹唯一。**

---------------------------------------------------------------------------
方案一在整个“实现谱系”中的位置（与方案二/三的关系）
---------------------------------------------------------------------------
  - **方案一（本文件）**：值域 `Traj ι X`，噪声是**输入**（一个取值序），
    输出**唯一确定的**一条路径。忠实于唯一权威方程是**定义性**的（`rfl` 级）。
  - **方案二（`FateV2.Model.TrajGenStochastic`）**：值域 `Measure (Traj ι X)`，
    噪声**按分布采样**并积分掉，输出**分布**（随机过程）。
    它与方案一的**唯一**正确关系是「逐样本路径一致性」：
    在给定一条噪声实现 ω 时，方案二展开出的样本路径恰等于方案一的输出。
  - **方案三（见 `第12问-方案三-连续时间SDE解.md`）**：值域 `Traj ℝ≥0 X`，
    机制从 `Step` 换成 SDE 解算子 `sol(μ,σ,W)`；**不能** `rfl` 级忠实。

故：**方案一是三方案中唯一“本项目可自证、构造性、可计算”的实现**，
且是方案二在「噪声/初值皆确定性（点质量）」这一支上的**退化特例**。

---------------------------------------------------------------------------
纪律（承 `第9问` 与作者裁决 I）
---------------------------------------------------------------------------
- 全程零 `sorry` / 零 `axiom`；本文件**不引入任何测度论**（方案一不需要）。
- 区分〔定义性约定〕/〔已证定理〕/〔诚实标注〕；凡未证不断言。
- `Step` 与 `TrajGen` **不同名、不同签名**（规格 §3.1 明令不得混用）；
  本文件实现的函数**叫 `trajGen`**，它**内部调用** `Step` —— 二者仍是两个函数。
- `InitialState.isRandom` 在方案一中**被丢弃**：本实现取「已抽样后的取值 `x₀.val`」。
  这是**诚实标注**，不是隐瞒：方案一**不建模** `x₀ ~ 𝒟₀`（那是方案二的事）。
-/


namespace FateV2.Model.TrajGenDeterministic

/-! ===========================================================================
    §1  方案一的核心：沿 ℕ 正向迭代 `Step`（原始递归）
    =========================================================================== -/

/-- **方案一的轨迹生成器**（`ι = ℕ`）：把 `Step f` 沿时间正向**迭代**。

**唯一权威离散方程在轨迹层的定义性展开**：
$$\mathrm{trajGen}(x_0)(0)=x_0,\qquad
  \mathrm{trajGen}(x_0)(n+1)=f\big(\mathrm{trajGen}(x_0)(n),\ u_n,\ \varepsilon_n;\ \theta,\ a_n\big).$$

**它到底“由什么唯一决定”**：给定五元组
$(\theta,\ x_0,\ u,\ \varepsilon,\ a)$，输出 `Traj ℕ F.X` 是**唯一**的——
这正是本方案的名字「确定性递推」所指（见 §5 唯一性）。

**与 `Step` 的区别（规格 §3.1 明令）**：`Step` 是**单步**取值到取值；
本函数是**整条轨迹**取值序列。二者**不同签名**——本函数**调用** `Step`，
但**不是** `Step` 的别名（`_名字误导审计.md` 禁止同名异义混用）。

**依赖 `f` 作外生参数**：`trajGen` **不构造**机制 `f`，只把给定机制**迭代**。
这是忠实于「机制 $f$ 是结构方程」的写法（见 `FateV2.Model/FrameBridge.lean`）。

标签：**[定义性约定]**（`TrajGen` 类型的一种实现）。 -/
def trajGen (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    Traj ℕ F.X :=
  fun n => Nat.rec x₀ (fun k xk => f xk (u k) (ε k) θ (a k)) n

/-- **符合 `TrajGen` 固定签名的实现**（`InitialState` 版本，`ι = ℕ`）。

**`isRandom` 的处理（诚实标注）**：本实现取 `x0.val`，**忽略** `x0.isRandom`。
这是**抽样后**的版本——$\mathcal{D}_0$ 的抽样已在 `x0.val` 之外完成。
若 $x_0$ 随机，轨迹的**分布**没有在本方案中建模，
本方案只给出一条**样本路径**。真正的随机语义需方案二（值域升为测度）。

**故本定义是 `TrajGen F ℕ` 的一个忠实实现**——
它遵守固定签名（含 `InitialState` 与 `(ℕ → Ν)` 的噪声序位），
只是把噪声序**当作取值输入**（而非分布），这正是方案一的定义。

标签：**[定义性约定]**。 -/
def trajGenOfFrame (F : Frame) (f : Step F) : TrajGen F ℕ :=
  fun θ x0 u ε a =>
    fun n => Nat.rec x0.val (fun k xk => f xk (u k) (ε k) θ (a k)) n

/-- **两定义相容**：`trajGenOfFrame` 就是取 `x0.val` 后的 `trajGen`（定义性）。 -/
theorem trajGenOfFrame_eq (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x0 : InitialState F.X)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    trajGenOfFrame F f θ x0 u ε a = trajGen F f θ x0.val u ε a := rfl

/-! ===========================================================================
    §2  忠实性：唯一权威方程在轨迹层**定义性成立**（`rfl` 级）
    =========================================================================== -/

/-- **忠实截面（核心定理）**：轨迹满足唯一权威方程，**对一切 `n` 成立**。

$$\forall n,\quad x_{n+1}=f(x_n,\ u_n,\ \varepsilon_n;\ \theta,\ a_n).$$

**证明是定义性的（`rfl`）** —— 这不是“碰巧为真”，而是
`Nat.rec` 的**计算方程本身**。故方案一把唯一权威方程**原样搬到了轨迹层**，
无任何附加假设、无任何前件。

**这是三方案中唯一能做到 `rfl` 级忠实的一处**（方案三只能到积分方程前件）。 -/
theorem trajGen_succ (F : Frame) (f : Step F) θ x₀ u ε a (n : ℕ) :
    trajGen F f θ x₀ u ε a (n+1)
      = f (trajGen F f θ x₀ u ε a n) (u n) (ε n) θ (a n) := rfl

/-- **初值条件**：方案一从 $x_0$ 出发（定义性）。 -/
theorem trajGen_zero (F : Frame) (f : Step F) θ x₀ u ε a :
    trajGen F f θ x₀ u ε a 0 = x₀ := rfl

/-- **`TrajGen` 签名版本**的忠实截面（与 §1 的 `trajGenOfFrame` 同源）。 -/
theorem trajGenOfFrame_succ (F : Frame) (f : Step F) θ x0 u ε a (n : ℕ) :
    trajGenOfFrame F f θ x0 u ε a (n+1)
      = f (trajGenOfFrame F f θ x0 u ε a n) (u n) (ε n) θ (a n) := rfl

/-! ===========================================================================
    §3  有限视窗版本（`ι = Fin T`）：与方案二的 `detTraj` 同物
    =========================================================================== -/

/-- **有限视窗的逐点状态**（`n ≤ T`）：沿 ℕ 正向递推，携带界限证明 `n ≤ T`。

$$\mathrm{stateAt}(0)=x_0,\qquad
  \mathrm{stateAt}(n+1)=f\big(\mathrm{stateAt}(n),\ u_n,\ \varepsilon_n;\ \theta,\ a_n\big).$$

与 `trajGen` **同一递推**（都是唯一权威方程的正向展开）；
差别只在索引被限制在 `Fin T` 的视窗内，故 `stateAt` 携带 `n ≤ T` 的界限证明，
使 `u_n`、`ε_n`、`a_n` 的取值总是合法。

标签：**[定义性约定]**。 -/
def stateAt (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier)
    (x₀ : F.X.Carrier) : (n : ℕ) → n ≤ T → F.X.Carrier
  | 0, _ => x₀
  | n + 1, h =>
      f (stateAt F f T θ u ε a x₀ n (Nat.le_of_succ_le h))
        (u ⟨n, by omega⟩) (ε ⟨n, by omega⟩) θ (a ⟨n, by omega⟩)

/-- **方案一的有限视窗轨迹**（`ι = Fin T`，贴合规格 §2.1 规则 T2）。

$$x_0,\ x_1,\ \dots,\ x_{T-1},\qquad
  x_{n+1}=f(x_n,u_n,\varepsilon_n;\theta,a_n).$$

**与方案二的关系**：这正是 `FateV2.Model.TrajGenStochastic.detTraj` 的同一构造——
方案二的展开映射 `unfold` 对**每一条**噪声实现 ω 的输出恰是本函数（见 §6）。 -/
def detTraj (F : Frame) (f : Step F) (T : ℕ)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier) :
    Traj (Fin T) F.X :=
  fun n => stateAt F f T θ u ε a x₀ n.val (Nat.le_of_lt n.isLt)

/-- **有限视窗的忠实截面（定义性，`rfl`）**：`detTraj` 满足唯一权威方程（对所有 `n+1 < T`）。

这是 §2 的 `trajGen_succ` 在 `Fin T` 上的读法。
具体地，`detTraj` 在 `⟨n+1,_⟩` 处等于 `f` 作用于 `⟨n,_⟩` 处、
以窗口内第 `n` 个输入/噪声/动作为参数。

**证明是定义性的**：`stateAt` 的 `n+1` 分支即是该等式，
只需把 `Fin` 索引的取值与其 `val` 对齐。 -/
theorem stateAt_succ (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier)
    (x₀ : F.X.Carrier) (n : ℕ) (h : n + 1 ≤ T) :
    stateAt F f T θ u ε a x₀ (n+1) h
      = f (stateAt F f T θ u ε a x₀ n (Nat.le_of_succ_le h))
          (u ⟨n, by omega⟩) (ε ⟨n, by omega⟩) θ (a ⟨n, by omega⟩) := rfl

/-- **有限视窗的忠实截面**：`detTraj` 满足唯一权威方程（对所有 `n+1 < T`）。 -/
theorem detTraj_succ (F : Frame) (f : Step F) (T : ℕ)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier)
    (n : ℕ) (hn : n + 1 < T) :
    detTraj F f T θ x₀ u ε a ⟨n + 1, hn⟩
      = f (detTraj F f T θ x₀ u ε a ⟨n, by omega⟩)
          (u ⟨n, by omega⟩) (ε ⟨n, by omega⟩) θ (a ⟨n, by omega⟩) := rfl

/-- **初值条件（有限视窗）**：`detTraj` 在 `0` 处取 $x_0$（定义性）。 -/
theorem detTraj_zero (F : Frame) (f : Step F) (T : ℕ)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier)
    (hT : 0 < T) :
    detTraj F f T θ x₀ u ε a ⟨0, hT⟩ = x₀ := rfl

/-! ===========================================================================
    §4  唯一性：轨迹由初值与输入**唯一决定**（本方案的命名根据）
    =========================================================================== -/

/-- **确定性（唯一性）定理**：两组**相同的**输入序给出**相同的**轨迹。

若 $(\theta,x_0,u,\varepsilon,a)$ 与 $(\theta',x_0',u',\varepsilon',a')$ 在
每个时间点的输入、参数、初值都相同，则两条轨迹**逐点相同**。

**这正是“确定性递推”的严格含义**：轨迹**不是**“一条被选出的路径”，
而是**由初值与输入唯一决定的**那个函数值——
不存在两条不同的轨迹共享全部输入（见下 `trajGen_unique`）。

方案二则**不**满足这条（值域是测度，两个世界可仅在噪声分布上不同）。 -/
theorem trajGen_deterministic (F : Frame) (f : Step F)
    {θ θ' : F.Θ.Carrier} {x₀ x₀' : F.X.Carrier}
    {u u' : ℕ → F.U.Carrier} {ε ε' : ℕ → F.Ν.Carrier} {a a' : ℕ → F.Act.Carrier}
    (hθ : θ = θ') (hx : x₀ = x₀')
    (hu : ∀ n, u n = u' n) (hε : ∀ n, ε n = ε' n) (ha : ∀ n, a n = a' n) :
    trajGen F f θ x₀ u ε a = trajGen F f θ' x₀' u' ε' a' := by
  subst hθ; subst hx
  funext n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [trajGen_succ, trajGen_succ, ih, hu k, hε k, ha k]

/-- **唯一性（“不存在两条不同轨迹共享全部输入”）**：

若两条轨迹都从 `x₀` 出发、都按唯一权威方程演化、且输入序逐点相同，
则它们**逐点相同**。

**证明**：两条轨迹都在每一点满足 `trajGen_succ` 式递推 + 同初值，
故由对 `n` 的归纳逐点相等。这条把 §2 的“忠实”升级为
“忠实 + 初值 ⟹ 唯一”——即**方案一的值确实由初值与输入唯一决定**，无自由度。 -/
theorem trajGen_unique (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    {x y : Traj ℕ F.X}
    (hx0 : x 0 = x₀) (hy0 : y 0 = x₀)
    (hx : ∀ n, x (n+1) = f (x n) (u n) (ε n) θ (a n))
    (hy : ∀ n, y (n+1) = f (y n) (u n) (ε n) θ (a n)) :
    x = y := by
  funext n
  induction n with
  | zero => rw [hx0, hy0]
  | succ k ih => rw [hx k, hy k, ih]

/-- 方案一的轨迹**就是**满足初值条件与递推方程的那**唯一**解。

这是把 `trajGen_unique` 应用到 `trajGen` 自身：
任何满足「同初值 + 同递推」的 `x` 都等于 `trajGen`。 -/
theorem trajGen_is_unique_solution (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    {x : Traj ℕ F.X}
    (hx0 : x 0 = x₀)
    (hx : ∀ n, x (n+1) = f (x n) (u n) (ε n) θ (a n)) :
    x = trajGen F f θ x₀ u ε a := by
  symm
  exact trajGen_unique F f θ x₀ u ε a (trajGen_zero F f θ x₀ u ε a) hx0
    (trajGen_succ F f θ x₀ u ε a) hx

/-! ===========================================================================
    §5  移位（Markov 性）与拼接：方案一的结构性质
    =========================================================================== -/

/-- **移位一致性（Markov 性）**：从时刻 `m` 的状态 `x_m` 出发、
用 `m` 之后的输入继续递推，与“整条轨迹从 `m` 之后的部分”一致。

$$\mathrm{shift}_m(x)(k)=x_{m+k},\qquad
  \mathrm{shift}_m(x)(k+1)=f\big(\mathrm{shift}_m(x)(k),\,u_{m+k},\dots\big).$$

即：**未来只依赖当前状态与未来输入，不依赖过去**（一步 Markov 结构），
这是 `Step` 作为“单步转移”的直接后果，由 `rfl` 给出。 -/
def shift (F : Frame) (m : ℕ)
    (x : Traj ℕ F.X) : Traj ℕ F.X :=
  fun k => x (m + k)

/-- **移位轨迹满足同型递推**：`shift` 之后仍按唯一权威方程演化，
只是初值换成 `x_m`、输入被时间平移了 `m`（参数 `θ` 与机制 `f` 不变）。 -/
theorem shift_succ (F : Frame) (f : Step F) (m : ℕ)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    shift F m (trajGen F f θ x₀ u ε a)
      = trajGen F f θ (trajGen F f θ x₀ u ε a m)
          (fun k => u (m + k)) (fun k => ε (m + k)) (fun k => a (m + k)) := by
  funext k
  induction k with
  | zero => rfl
  | succ j ih =>
      show trajGen F f θ x₀ u ε a (m + (j + 1))
        = f (trajGen F f θ (trajGen F f θ x₀ u ε a m)
              (fun k => u (m + k)) (fun k => ε (m + k)) (fun k => a (m + k)) j)
            (u (m + j)) (ε (m + j)) θ (a (m + j))
      rw [show m + (j + 1) = (m + j) + 1 by omega, trajGen_succ]
      dsimp only [shift] at ih
      rw [ih]

/-- **拼接（前缀 + 后缀 = 全长）**：先递推 `m` 步得到 `x_m`，再从 `x_m` 继续，
得到全长轨迹。这是 `shift_succ` 的另一读法：**无“记忆”被丢弃**，
因为 `Step` 是完备状态转移。 -/
theorem trajGen_split (F : Frame) (f : Step F) (m : ℕ)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    trajGen F f θ x₀ u ε a
      = fun k => if _h : k < m
          then trajGen F f θ x₀ u ε a k
          else trajGen F f θ (trajGen F f θ x₀ u ε a m)
                (fun j => u (m + j)) (fun j => ε (m + j)) (fun j => a (m + j)) (k - m) := by
  funext k
  by_cases h : k < m
  · simp only [h, dif_pos]
  · simp only [h, dif_neg, not_false_iff]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h)
    have hshift := congrFun (shift_succ F f m θ x₀ u ε a) j
    simpa [shift, Nat.add_sub_cancel_left] using hshift

/-! ===========================================================================
    §6  与方案二（`FateV2.Model.TrajGenStochastic`）的关系：逐样本路径一致
    =========================================================================== -/

/-! **诚实标注**：本模块**不** `import FateV2.Model.TrajGenStochastic`（方案一不需要测度论，
反向依赖会使本模块变重）。故此处**不逐字复制**方案二的 `unfold_eq_detTraj`，
而是把该关系**陈述为一条接口引理的形式**，并在文档
`第9问-方案一-确定性递推.md` 中给出它与方案二 `detTraj` 的对照表。

**关系（供文档引用，非本模块定理）**：

> 方案二的展开 `unfold : (X × (Fin T → Ν)) → Traj (Fin T) X` 满足
> $$\forall \omega,\quad \mathrm{unfold}(x_0,\omega)=\mathrm{detTraj}(x_0,\omega),$$
> 其中右端即本模块 §3 的 `detTraj`（方案一的有限视窗轨迹）。
> 这不是“两方案等价”（值域不同型），而是「方案二的**每条样本**落在方案一的像里」。

**本模块给出的、支撑该关系的结构事实**：`detTraj` 满足
`detTraj_succ` / `detTraj_zero`，故由 §4 的 `trajGen_unique`
知它**是唯一**由 `(θ,x₀,u,ε,a)` 决定的 `Fin T` 轨迹——
方案二的 `unfold` 在任意 ω 下同样满足这两条（其 `unfold_succ`/`rfl`），
故二者逐点相同。**这条论证不依赖测度论**，故放在本模块是安全的。 -/

/-! ===========================================================================
    §7  诚实标注与方案一的**表达力上限**
    =========================================================================== -/

/-! ### §7.1 `isRandom` 被丢弃（不是隐瞒，是定义的边界）

方案一取 `x₀.val`，**不建模** $x_0\sim\mathcal{D}_0$。
因此方案一**无法区分**两个「只有初始分布不同」的世界：
若它们的 `x₀.val` 相同，方案一给出**同一条**轨迹。

**这不是 bug，是方案一的表达力上限**——它是 `Traj ι X`（函数值域）这一类型
的固有性质：分布信息**在类型层就已经丢失**。要表达该区分，须升级值域到
`Measure (Traj ι X)`（方案二），或让 $x_0$ 成为**独立输入维**（见 §7.2）。

**机器可见的证据**：`trajGenOfFrame_eq` 显示 `isRandom` **不出现在**右端——
`isRandom` 的两个取值给出**同一个** `trajGen` 输出。 -/

/-- **`isRandom` 不可见（表达力上限的形式证据）**：
两个仅在 `isRandom` 上不同的初值给出**完全相同**的轨迹。

即 `x0₁.isRandom ≠ x0₂.isRandom` 无碍于 `x0₁.val = x0₂.val` 时输出相等。
这条把「方案一丢弃随机性」钉成一条**可编译事实**，而非注释。 -/
theorem trajGenOfFrame_isRandom_invisible (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (v : F.X.Carrier) (b₁ b₂ : Bool)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    trajGenOfFrame F f θ ⟨v, b₁⟩ u ε a = trajGenOfFrame F f θ ⟨v, b₂⟩ u ε a := rfl

/-! ### §7.2 确定性的**可计算性**（`#eval` 可跑）

方案一是**构造性**的：`trajGen` 由 `Nat.rec` 定义，**无 `noncomputable`**、
无 `Classical.choice`。故在**具体**（可计算）的 `Frame` 与 `Step` 上，
`trajGen` 的输出**可被求值**——这是方案二（`noncomputable`，`Measure` 所致）
**不具备**的性质。

方案三则更弱：其输出依赖**外生的**解算子 `sol`，本项目**不提供**构造。 -/

/-- **可计算性接口**：方案一的轨迹在某点 `n` 的取值，
可由「`n` 步折叠 `Step`」**计算**得到。

本引理把 `trajGen` 的值**显式**写成 `List.range n` 上的折叠，
把「逐步展开」写成对**有限列表**的递归 —— 既是 `trajGen_succ` 的 `n` 步推广，
也便利于 `#eval` 与外部脚本对照（`Nat.rec` 的等价算法形式）。 -/
theorem trajGen_eq_foldl (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    trajGen F f θ x₀ u ε a n
      = (List.range n).foldl (fun x k => f x (u k) (ε k) θ (a k)) x₀ := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [trajGen_succ, ih, List.range_succ, List.foldl_append]
      rfl

/-! ===========================================================================
    §8  与固定 `TrajGen` 类型的**兼容性结论**（对比方案二）
    =========================================================================== -/

/-! **结论（与方案二的对照）**：

| 维度 | 方案一（本模块）| 方案二（`TrajGenStochastic`）|
|---|---|---|
| 值域 | `Traj ι X`（函数）| `Measure (Traj ι X)`（测度）|
| 噪声位 | **保留**（`(ι → Ν)` 作**取值**输入）| **删除**（噪声被积分掉）|
| 初始条件 | `InitialState`（取 `val`）| `InitDist`（分布本身）|
| 与既有 `TrajGen` 类型 | ✅ **完全兼容**（就是它的一个实现）| ❌ **不兼容**（值域不同型）|
| 忠实唯一权威方程 | ✅ `rfl` | ✅ 逐样本（`rfl`），非测度层 |
| 可计算 | ✅ 构造性 | ⚠️ `noncomputable`（`Measure`）|
| 表达力 | 单条路径（丢分布）| 路径上的分布（承载随机性）|

**判词**：

> **方案一是既有 `TrajGen` 类型下唯一“完全兼容 + 可计算 + `rfl` 级忠实”的实现。**
> 它的表达力上限（丢 `isRandom`、丢分布）**不是缺陷**，而是该类型的固有边界——
> 这条边界正是方案二存在的理由（逼迫改类型）。
> 二者**不是竞争关系**：方案一是方案二在点质量噪声/初值这一支上的**退化特例**。 -/

end FateV2.Model.TrajGenDeterministic
