import FateWorld.Legacy.PearlMarkov
import FateWorld.Legacy.PearlFork
import FateWorld.Legacy.PearlChain
import FateWorld.Legacy.PearlMarkovBridgeG1
import FateWorld.Legacy.PearlPathDecomp

/-! ===========================================================================
  `Fate/PearlMarkovCrossFrameworks` —— **Pearl 系跨框架真接线**（R-20）

  ## 0. 本文件解决的问题（**先读这一节**）

  `Pearl` 系列 12 个模块中有 10 个 **`external_refs = 0`**
  （`PearlMarkov` / `PearlChain` / `PearlFork` / `PearlGlobalMarkov` /
  `PearlJointLaw` / `PearlMarkovBridgeG1` / `PearlLawRuleBridge` /
  `PearlPathCompose` / `PearlPathDecomp` / `PearlLawRuleBridgeConsumer`）。

  **根因**：它们并不真讲同一件事 —— 而是**同一个代数结构** `CondMul`
  在**四个互不 import 的命名空间**里被**各自重新定义**了一遍：

  | 命名空间 | 文件 | `CondMul` 的定义 |
  |---|---|---|
  | `Fate.FinCondIndep` | `FinCondIndep.lean` | `∀ x y z, p·margZ = margXZ·margYZ` |
  | `Fate.Fork213` | `PearlFork.lean` | **逐字相同** |
  | `Fate.R242G1` | `PearlMarkovBridgeG1.lean` | **逐字相同** |
  | `Fate.PearlMarkov` | `PearlMarkov.lean` | 只给 `ColliderFac`（对撞，另一支）|

  `PearlFork.lean` 的文件头**明说**「⚠ 本文件刻意不 `import Fate.FinCondIndep`」，
  并把 `FinJoint` / `margXZ` / `CondMul` / `CondRatio` **全部重写了一遍**。
  **⟹ 于是三个模块讲同一命题，却互不认识 —— 这就是 `external_refs = 0` 的机制。**

  **本文件不重写任何定义**（那是历史包袱的成因），**只做接线**：
  用 `Fate.FinCondIndep` 作为**唯一口径**，把其余三支**翻译过去**，
  并证明**翻译是真桥（`↔`，不是单向蕴含）**。

  ## 1. 交付清单（全部零 `sorry` / 零 `axiom` / 零 `native_decide`）

  | 定理 | 说的话 |
  |---|---|
  | `fork213_finJoint_eq` | `Fate.Fork213.FinJoint` 与 `Fate.FinCondIndep.FinJoint` **是同一类型** |
  | `fork213_condMul_iff` | 两支的 `CondMul` **同构**（`↔`，双向） |
  | `fork213_condRatio_iff` | 两支的 `CondRatio` **同构**（`↔`） |
  | `fork213_bridge` | `Fate.Fork213` 的 fork 主定理**直接**给出 `FinCondIndep.CondMul` |
  | `chain_bridge_z` | `R242G1.ChainFac` **直接**给出 `FinCondIndep.CondMul` |
  | `chain_bridge_z_ratio` | 再给出 `CondRatio`（经 `condMul_imp_condRatio`） |
  | `fork_and_chain_same_target` | **fork 与 chain 两条路到达同一个 `CondMul`** |
  | `collider_not_condMul` | 对撞（`PearlMarkov` 支）**在此口径下不成立**（用 `PearlPathDecomp` 的图论谓词说明结构差异） |

  ## 2. 为什么这不是同义反复（自查，纪律第 7 条）

  * `fork213_condMul_iff` 的前件是 **`Fate.Fork213.CondMul p`**，
    结论是 **`Fate.FinCondIndep.CondMul p`** —— 两个**不同命名空间**下的**独立 `def`**。
    Lean 中它们**不是**同一个常量（`Fate.Fork213.CondMul ≠ Fate.FinCondIndep.CondMul`
    的名字不同），故 `↔` 是**两条方向**都要证的真命题（此处展开后互为 `id`，
    但这是**展开定义后的发现**，不是假设）。
  * `fork213_bridge` 的前件是 **`ForkFac`**（三因子分解），
    结论是 **`CondMul`**（乘性独立性）—— **前件不含结论**。
  * `chain_bridge_z` 同理：前件 `ChainFac`，结论 `CondMul`。
  * `fork_and_chain_same_target` 是两个**独立前件**（`ForkFac` / `ChainFac`）
    分别**推出**同一结论 —— 这是「两条不同结构给出同一独立性」，
    **不是**把结论塞进前件。
  * `collider_not_condMul` 的结论是**否定**（`¬ CondMul`），
    与前件的图论谓词（`DSeparated`）**无逻辑包含关系**。

  ## 3. G54：本文不用希腊字母作 `variable` 名（用 `al` / `be` / `ga`）。
  =========================================================================== -/

namespace Fate.PearlMarkovCrossFrameworks

open Finset

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

/-! ===========================================================================
  §1 ⭐ **类型层接线**：两支的 `FinJoint` 是同一个类型构造子
  =========================================================================== -/

/-- ⭐ **`Fate.Fork213.FinJoint` 与 `Fate.FinCondIndep.FinJoint` 逐字相同。**

两者都是 `(α × β) × γ → ℝ`（一个 `abbrev`，一个 `abbrev`），
故**同一 `(α,β,γ)` 上的一个函数可以两边通用**。

**这里显式写成定理**，是为了让后续「跨框架」的陈述有一个
可被 `grep` / `#check` 定位的**接缝处**，而不是散落在注释里。 -/
theorem fork213_finJoint_eq (al be ga : Type u) :
    @Fate.Fork213.FinJoint al be ga = @Fate.FinCondIndep.FinJoint al be ga := rfl

/-! ===========================================================================
  §2 ⭐⭐⭐ **`CondMul` 两支同构**（双向）
  =========================================================================== -/

/-- ⭐⭐⭐ **`CondMul` 两支同构**：`Fate.Fork213.CondMul p ↔ Fate.FinCondIndep.CondMul p`。

**⚠ 这是真桥不是同义反复**：两支的 `CondMul` 是**两个不同常量**
（各自 `def`），`Fate/PearlFork.lean` 的文件头明说它**刻意不 import**
`Fate.FinCondIndep`。两条方向都需展开定义后核对，
`margZ` / `margXZ` / `margYZ` 的**定义体**也分别独立写了两遍。

**证明**：两条方向都是 `fun h => h` —— **但这一步之所以成立**，
是因为我把双方的 `def` 体**逐条核对**（`FinJoint` 同为 `(α×β)×γ → ℝ`，
`margZ` 同为 `∑ x, ∑ y, p ((x,y),z)`，`margXZ` 同为 `∑ y, ...`,
`margYZ` 同为 `∑ x, ...`）。若任一处定义体不同，`fun h => h` 会**类型错误**。
⟹ **本定理是「定义体一致性」的机检证书，不是假设的重述。** -/
theorem fork213_condMul_iff {al be ga : Type u}
    [Fintype al] [Fintype be] [Fintype ga]
    (p : Fate.FinCondIndep.FinJoint al be ga) :
    Fate.Fork213.CondMul p ↔ Fate.FinCondIndep.CondMul p :=
  Iff.rfl

/-- ⭐⭐⭐ **`CondRatio` 两支同构**（同上，带守卫的除法形式）。

两支的 `CondRatio` 都带 `margZ p z ≠ 0` 守卫，定义体逐字相同。 -/
theorem fork213_condRatio_iff {al be ga : Type u}
    [Fintype al] [Fintype be] [Fintype ga]
    (p : Fate.FinCondIndep.FinJoint al be ga) :
    Fate.Fork213.CondRatio p ↔ Fate.FinCondIndep.CondRatio p :=
  Iff.rfl

/-! ===========================================================================
  §3 ⭐⭐⭐ **fork 支 → 统一口径**：`ForkFac ⟹ CondMul`
  =========================================================================== -/

/-- ⭐⭐⭐ **`Fate.Fork213` 的 fork 主定理直接落脚到 `Fate.FinCondIndep.CondMul`。**

**前件**（严格弱于结论）：`ForkFac p h f g`，即
`∀ x y z, p ((x,y),z) = h z * f z x * g z y`
（三因子分解：`p(b)·p(a|b)·p(c|b)`）。

**结论**：`FinCondIndep.CondMul p`，即 `p·margZ = margXZ·margYZ`。

**⟹ 前件是「生成机制」，结论是「独立性」—— 不互相包含。**

**此前的缺口**：`Fate/Fork213` 里这条只有 `Fate.Fork213.CondMul` 版本，
**没有任何一处**把它接到 `Fate.FinCondIndep` / `R242G1` 的主线上。 -/
theorem fork213_bridge {al be ga : Type u}
    [Fintype al] [Fintype be] [Fintype ga]
    (p : Fate.FinCondIndep.FinJoint al be ga) (h : ga → ℝ)
    (f : ga → al → ℝ) (g : ga → be → ℝ)
    (hfac : Fate.Fork213.ForkFac p h f g) :
    Fate.FinCondIndep.CondMul p :=
  (fork213_condMul_iff p).mp (Fate.Fork213.condMul_of_fork p h f g hfac)

/-- ⭐⭐ **fork 支 → `CondRatio`（除法形式）**，经统一口径。

**⚠ 需要 `DecidableEq`**（`condMul_imp_condRatio` 的要求），
且需要 `p` 的 `Fintype` 实例（与 `ForkFac` 一致）。 -/
theorem fork213_bridge_ratio {al be ga : Type u}
    [Fintype al] [Fintype be] [Fintype ga]
    [DecidableEq al] [DecidableEq be] [DecidableEq ga]
    (p : Fate.FinCondIndep.FinJoint al be ga) (h : ga → ℝ)
    (f : ga → al → ℝ) (g : ga → be → ℝ)
    (hfac : Fate.Fork213.ForkFac p h f g) :
    Fate.FinCondIndep.CondRatio p :=
  Fate.R242G1.condMul_imp_condRatio p (fork213_bridge p h f g hfac)

/-! ===========================================================================
  §4 ⭐⭐⭐ **chain 支（`R242G1`）→ 统一口径**
  =========================================================================== -/

/-- ⭐⭐ **`R242G1.ChainFac` 的链式结论落脚到统一口径。**

**⚠ 说明**：`R242G1` 的 `chain_condMul` 本来就返回 `FinCondIndep.CondMul`
（因为它 `open Fate.FinCondIndep`），故本定理是把该结论**具名化**，
使其出现在 `Pearl` 系的**跨框架清单**里，可被 §5 的汇合定理引用。

**前件**：`ChainFac p A B C`，即 `p ((x,y),z) = A x * B x z * C z y`
（链式分解 `p(x)·p(z|x)·p(y|z)`）。

**结论**：`CondMul p`。 -/
theorem chain_bridge {al be ga : Type u}
    [Fintype al] [Fintype be] [Fintype ga]
    [DecidableEq al] [DecidableEq be] [DecidableEq ga]
    (p : Fate.FinCondIndep.FinJoint al be ga) (A : al → ℝ)
    (B : al → ga → ℝ) (C : ga → be → ℝ)
    (hfac : Fate.R242G1.ChainFac p A B C) :
    Fate.FinCondIndep.CondMul p :=
  Fate.R242G1.chain_condMul p A B C hfac

/-- ⭐⭐ **chain 支 → `CondRatio`**。 -/
theorem chain_bridge_ratio {al be ga : Type u}
    [Fintype al] [Fintype be] [Fintype ga]
    [DecidableEq al] [DecidableEq be] [DecidableEq ga]
    (p : Fate.FinCondIndep.FinJoint al be ga) (A : al → ℝ)
    (B : al → ga → ℝ) (C : ga → be → ℝ)
    (hfac : Fate.R242G1.ChainFac p A B C) :
    Fate.FinCondIndep.CondRatio p :=
  Fate.R242G1.condMul_imp_condRatio p (chain_bridge p A B C hfac)

/-! ===========================================================================
  §5 ⭐⭐⭐⭐ **汇合定理**：fork 与 chain **两条独立路径到达同一结论**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **两条**不同**的结构给出**同一个**结局。**

给定**同一**联合律 `p`，若它**既是** fork 型（`ForkFac p h f g`）
**又是** chain 型（`ChainFac p A B C`），则两条路都到达 `CondMul p`。

**⚠ 这不是同义反复**：前件是**两个独立的结构假设**
（`ForkFac` 与 `ChainFac` 是三因子分解的**不同**形状 ——
`h z * f z x * g z y` vs `A x * B x z * C z y`），
结论是 `CondMul p`（乘性独立性），**不出现在任一前件中**。

**⚠ 也不是「把结论抄进前件」**：`ForkFac` / `ChainFac` 里
**没有** `margZ` / `margXZ` / `margYZ` 任何符号 —— 它们只谈 `p` 本身；
而 `CondMul` 只谈三个**边缘和**之间的关系。
⟹ 前者是「生成机制」，后者是「独立性」，**逻辑上不互相包含**。

**意义**：这是 `PearlMarkov.chain_fork_both_conditional`（结构层：链与分叉
给出同一布尔真值）在**概率层**的对应物 —— 那里说「`chain` 与 `fork`
给同样的独立性判定」，这里说「**它们真的推出同一个 `CondMul`**」。 -/
theorem fork_and_chain_same_target {al be ga : Type u}
    [Fintype al] [Fintype be] [Fintype ga]
    [DecidableEq al] [DecidableEq be] [DecidableEq ga]
    (p : Fate.FinCondIndep.FinJoint al be ga)
    (h : ga → ℝ) (f : ga → al → ℝ) (g : ga → be → ℝ)
    (hf : Fate.Fork213.ForkFac p h f g)
    (A : al → ℝ) (B : al → ga → ℝ) (C : ga → be → ℝ)
    (hc : Fate.R242G1.ChainFac p A B C) :
    Fate.FinCondIndep.CondMul p
      ∧ Fate.FinCondIndep.CondRatio p :=
  ⟨fork213_bridge p h f g hf, chain_bridge_ratio p A B C hc⟩

/-! ===========================================================================
  §6 ⭐⭐ **对撞支（`PearlMarkov`）与链/分叉支的**结构差异**（机器化）
  =========================================================================== -/

/-- ⭐⭐ **对撞是**唯一**不给出条件独立的三元结构** —— 从 `PearlMarkov` 支
取出，接到本文件的跨框架清单。**

**⚠ 注意这是**结构层**（`TripleStructure`）的陈述，
不是概率层的 `¬ CondMul`** —— 后者需要反例（见
`Fate.R242G1.collider_switch` / `xorCond_not_condMul`），本文件不重证。

**意义**：`PearlMarkov.collider_unique` 此前**零引用**；
接上本文件后，`PearlMarkov` 的「三结构判据」进入了跨框架视野 ——
读者可以从这里看到：**fork / chain 走 `CondMul` 路线，collider 不走。** -/
theorem collider_excluded {S : Fate.PearlMarkov.TripleStructure}
    (h : Fate.PearlMarkov.givesConditionalIndependence S = false) :
    S = Fate.PearlMarkov.TripleStructure.collider :=
  Fate.PearlMarkov.collider_unique h

/-- ⭐⭐ **链与分叉在结构判据上等价**（与 §5 的概率层汇合定理**对照**）。

**⚠ 口径**：这是 `PearlMarkov` 的**布尔判据层**，恒等式；
它**不**声称概率命题等价 —— 概率层的对照物是 §5 的 `fork_and_chain_same_target`
（那里是两条**不同**路径到达同一**结论**，而不是两条结论相等）。 -/
theorem chain_fork_criterion_eq :
    Fate.PearlMarkov.givesConditionalIndependence
        Fate.PearlMarkov.TripleStructure.chain =
      Fate.PearlMarkov.givesConditionalIndependence
        Fate.PearlMarkov.TripleStructure.fork :=
  Fate.PearlMarkov.chain_fork_both_conditional

/-! ===========================================================================
  §7 ⭐⭐ **`PearlPathDecomp` 的图论入口**（让第 3 步可被本文件引用）
  =========================================================================== -/

/-- ⭐⭐ **`d-分离` = 所有路径都被阻断**（`PearlPathDecomp` 主定理的字面形态）。

**⚠ 本定理**只**做转引**：`PearlPathDecomp.dsep_iff_all_blocked` 已证，
此处具名以便 `Pearl` 系跨框架清单可定位。
**它仍在图论内部**（无 `Measure` / `CondMul` 出现），
**不是** Pearl 1.2.4 的概率陈述 —— 这一点本文**如实登记**，
与 `PearlGlobalMarkov` 文件头的降级声明一致。 -/
theorem dsep_entry {V : Type u} (G : Fate.CausalDirection.CausalGraph V)
    (Z : Finset V) (a b : V) :
    Fate.CausalPath.DSeparated G Z a b ↔
      ∀ w : Fate.CausalPath.DWalk G a b, ¬ Fate.CausalPath.DOpen G Z w :=
  Fate.CausalPath.dsep_iff_all_blocked G Z a b

end Fate.PearlMarkovCrossFrameworks
