import FateWorld.Legacy.RuleExec
import FateWorld.Legacy.LawRule
import FateWorld.Legacy.LawRuleInstances

/-! ===========================================================================
  P0-F4 · **全链路可执行演示**（CHAIN-4 判定「可行，难度中」）

  ## 本模块做什么

  把「一张数值表」一路串到「误差数字」，**7 个环节全部可执行**：

  1. **数据**      —— `ℚ` 数值表（`(x, y)` 对的列表）              `DataQ`
  2. **提取规则**  —— 把候选律编码成 `Term`，逐点检验              `ruleLin2` / `holdsAt`
  3. **规则运算**  —— 规则项的合取 / 否定（对应 `LawRule.compose` 的交） `andTerm` / `allTerms`
  4. **Step 函数** —— `θ' = θ + η (θ* − θ)`                         `fstepQ`
  5. **轨迹**      —— 迭代 `N` 步                                    `trajQ`
  6. **预测**      —— 由轨迹给出第 `N` 步预测                        `predQ`
  7. **与真实对比** —— 误差序列                                      `trajErrQ` / `trajDiffQ`

  每个环节都用 `#eval` 打出**具体数值输出**（`Bool` / `ℚ` / `List ℚ`）。

  ## 与语义侧的接线

  `Fate.RuleExec` 是全仓唯一把规则跑成 `Bool` 的纯可执行引擎
  （`Term.check : Term → EnvQ → Bool`，`RuleExec.lean:88`），
  且已有 `Term.check_iff_holds` / `run_iff_holds` 把它钉到
  `RuleTerm.holds`（`ℝ` / `Prop` 语义）。

  本模块的「提取规则」只在 `Term` 子语法内做，故产出**自动**被
  `check_iff_holds` 覆盖：演示里的每个 `Bool` 都是某个
  `RuleTerm.holds` 的忠实判定，无需新增假设。

  ## 缺口 A 的处置（诚实标注）

  CHAIN-4 的缺口 A 说「`RuleTerm.holds` 返回 `Prop` 且内嵌 `ℝ`，
  全仓无 `Decidable` 实例」。本模块**不添加** `Decidable` 实例，
  而是**沿 `RuleExec` 既有的路线**：在 `ℚ` 子语法 `Term` 上用
  `Term.check`（已是 `Bool`）执行，再靠 `check_iff_holds` 上接语义。
  `#eval` 的对象**全部**是 `Term.check` 及其派生物。

  ## 缺口 B 的处置（**未接上**，如实声明）

  CHAIN-4 的缺口 B 是「没有模块把数值表变成 `AlphaData`」。
  本模块**不构造** `AlphaData`（那需要 `PatStruct` / 分区等固定结构，
  超出「演示」范围）。环节 1 → 2 走的是「**表 → `Term`**」，
  **不是**「表 → `AlphaData` → `LawRule`」。这是本演示的**已知缺口**。

  ## 缺口 C 的处置（**已补齐**）

  CHAIN-4 的缺口 C 是「没有预测轨迹 vs 真实轨迹的成对比较函数」。
  本模块新建 `trajErrQ`（绝对误差序列）与 `trajDiffQ`（两轨迹逐点差）补齐。
-/

namespace Fate
namespace FullPipelineDemo

open Fate.RuleSyntax.Exec

/-! ## §1  环节 1：数据（`ℚ` 数值表） -/

/-- **数值表**：观测到的 `(输入, 输出)` 有理数对。 -/
abbrev DataQ := List (ℚ × ℚ)

/-- 演示数据 1：`y = 2x` 的 4 个点（表**完全**满足线性律）。 -/
def dataLinQ : DataQ := [(0, 0), (1, 2), (2, 4), (3, 6)]

/-- 演示数据 2：同上但**最后一点被污染**（`(3, 7)` 而非 `(3, 6)`）。 -/
def dataLinQBad : DataQ := [(0, 0), (1, 2), (2, 4), (3, 7)]

/-- 演示数据 3：`y = x + 1` 的 3 个点。 -/
def dataShiftQ : DataQ := [(0, 1), (1, 2), (2, 3)]

/-- 环境构造：变量 `0` ↦ 「输入」，变量 `1` ↦ 「输出」。 -/
def envOfPair (p : ℚ × ℚ) : EnvQ := fun n => if n = 0 then p.1 else p.2

/-! ## §2  环节 2：提取规则（表 → `Term`）

  「提取」在这里的具体含义：**给定一个候选律**，把它编码成 `Term`，
  然后逐点用 `Term.check` 检验数据表是否满足它。
  这是能做的、诚实的「提取」：律的形式由人来给，**是否成立由执行器判定**。
-/

/-- 候选律 1：`y = 2x`，即 `2 * x₁ = x₂`。 -/
def ruleLin2 : Term :=
  .eq (.mul (.const 2) (.var 0)) (.var 1)

/-- 候选律 2：`y = x + 1`，即 `x₁ + 1 = x₂`。 -/
def ruleShift1 : Term :=
  .eq (.add (.var 0) (.const 1)) (.var 1)

/-- 候选律 3：`y ≤ 2x + 1`。 -/
def ruleLeQ : Term :=
  .le (.var 1) (.add (.mul (.const 2) (.var 0)) (.const 1))

/-! ## §3  环节 3：规则运算（合取「交」/ 否定） -/

/-- **规则运算**：两个 `Term` 的合取（对应 `LawRule.compose` 的交语义）。 -/
def andTerm (a b : Term) : Term := .and a b

/-- **规则运算**：一个 `Term` 的否定（对应排除）。 -/
def notTerm (a : Term) : Term := .not a

/-- **规则运算**：把列表里的项全部合取起来（空表给「无约束」`trueTermExec`）。 -/
def allTerms : List Term → Term
  | [] => trueTermExec
  | t :: ts => andTerm t (allTerms ts)

/-- **`LawRule` 层的规则运算**：交（`LawRule.compose`）。
    这是可执行侧 `andTerm` 的语义对应物（`compose` 在 `LawRule` 上是 `inf`）。 -/
def ruleMeet {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
    (R1 R2 : Fate.LawRule.LawRule C X Y) : Fate.LawRule.LawRule C X Y :=
  Fate.LawRule.compose R1 R2

/-! ## §4  环节 2/3 的执行：逐点判定 + 聚合 -/

/-- 单点判定：`t` 在 `p` 给出的环境下是否成立。 -/
def holdsAt (t : Term) (p : ℚ × ℚ) : Bool := t.check (envOfPair p)

/-- 全表判定：`t` 在**每一个**数据点上是否都成立。 -/
def holdsAll (t : Term) (D : DataQ) : Bool := D.all (holdsAt t)

/-- 通过的点的**个数**（用于「部分匹配」诊断）。 -/
def countSat (t : Term) (D : DataQ) : ℕ := (D.filter (holdsAt t)).length

/-! ## §5  环节 4：Step 函数 -/

/-- **Step**：`θ ↦ θ + η (θ* − θ)`（线性收敛的一步）。 -/
def fstepQ (eta thetaStar : ℚ) : ℚ → ℚ :=
  fun theta => theta + eta * (thetaStar - theta)

/-- **Step 的闭式**：`θ ↦ (1−η) θ + η θ*`（同一函数，便于对拍）。 -/
def fstepQClosed (eta thetaStar : ℚ) : ℚ → ℚ :=
  fun theta => (1 - eta) * theta + eta * thetaStar

/-- 两种写法在 `ℚ` 上一致。 -/
theorem fstepQ_eq_closed (eta thetaStar theta : ℚ) :
    fstepQ eta thetaStar theta = fstepQClosed eta thetaStar theta := by
  unfold fstepQ fstepQClosed; ring

/-! ## §6  环节 5：轨迹 -/

/-- **迭代 `N` 步**。 -/
def iterQ (f : ℚ → ℚ) (theta0 : ℚ) : ℕ → ℚ
  | 0 => theta0
  | n + 1 => f (iterQ f theta0 n)

/-- **轨迹（前 `N` 项，含初值）**。 -/
def trajQ (f : ℚ → ℚ) (theta0 : ℚ) (N : ℕ) : List ℚ :=
  (List.range N).map (iterQ f theta0)

/-! ## §7  环节 6：预测 -/

/-- **预测**：轨迹的第 `N` 步（`N = 0` 为初值）。 -/
def predQ (f : ℚ → ℚ) (theta0 : ℚ) (N : ℕ) : ℚ := iterQ f theta0 N

/-! ## §8  环节 7：与真实对比 → 误差（**缺口 C 的补齐**） -/

/-- **误差序列**：预测轨迹逐点与真实值 `thetaStar` 的**绝对**误差。 -/
def trajErrQ (f : ℚ → ℚ) (theta0 thetaStar : ℚ) (N : ℕ) : List ℚ :=
  (trajQ f theta0 N).map (fun t => Rat.abs (t - thetaStar))

/-- **尾误差**：第 `N` 步的绝对误差。 -/
def tailErrQ (f : ℚ → ℚ) (theta0 thetaStar : ℚ) (N : ℕ) : ℚ :=
  Rat.abs (predQ f theta0 N - thetaStar)

/-- **两条轨迹的逐点差**（预测 vs 另一条参考轨迹）。 -/
def trajDiffQ (f g : ℚ → ℚ) (theta0 : ℚ) (N : ℕ) : List ℚ :=
  (List.zip (trajQ f theta0 N) (trajQ g theta0 N)).map
    (fun p => Rat.abs (p.1 - p.2))

/-! ## §9  `#eval` 演示

  下面每个 `#eval` 都产生**具体数值**输出（`Bool` / `ℚ` / `List ℚ`）。
  真实输出见 `_audit/F4-全链路演示.md`。
-/

/- **演示 1**（环节 2/3）：律 `y = 2x` 在**干净表**上全表成立 → `true`。 -/
#eval holdsAll ruleLin2 dataLinQ

/- **演示 2**（环节 2/3）：同一律在**污染表**上不成立 → `false`。 -/
#eval holdsAll ruleLin2 dataLinQBad

/- **演示 3**（环节 2/3）：污染表上通过的点数 → `3`（共 4 点）。 -/
#eval countSat ruleLin2 dataLinQBad

/- **演示 4**（环节 2/3）：错误律 `y = x + 1` 在 `y = 2x` 表上的通过点数
   → `1`（唯 `(1,2)` 处 `1+1 = 2` 成立）。 -/
#eval countSat ruleShift1 dataLinQ

/- **演示 5**（环节 3）：合取 —— `y = 2x ∧ y ≤ 2x+1` 在干净表上成立 → `true`。 -/
#eval holdsAll (allTerms [ruleLin2, ruleLeQ]) dataLinQ

/- **演示 6**（环节 3）：合取 —— `y = 2x ∧ y = x+1` 在干净表上不成立 → `false`。 -/
#eval holdsAll (allTerms [ruleLin2, ruleShift1]) dataLinQ

/- **演示 7**（环节 3）：否定 —— `¬(y = x+1)` 在 `y = 2x` 表上不全成立
   → `false`（点 `(1,2)` 处 `1+1 = 2` 成立，故 `¬` 为假）。 -/
#eval holdsAll (notTerm ruleShift1) dataLinQ

/- **演示 8**（环节 4/5）：`η = 1/2, θ* = 1, θ₀ = 0` 的 6 步轨迹
   → `[0, 1/2, 3/4, 7/8, 15/16, 31/32]`。 -/
#eval trajQ (fstepQ (1/2) 1) 0 6

/- **演示 9**（环节 6）：第 6 步预测 → `63/64`。 -/
#eval predQ (fstepQ (1/2) 1) 0 6

/- **演示 10**（环节 7）：误差序列 → `[1, 1/2, 1/4, 1/8, 1/16, 1/32]`。 -/
#eval trajErrQ (fstepQ (1/2) 1) 0 1 6

/- **演示 11**（环节 7）：`η = 1/4` 的误差序列
   → `[1, 3/4, 9/16, 27/64, 81/256, 243/1024]`。 -/
#eval trajErrQ (fstepQ (1/4) 1) 0 1 6

/- **演示 12**（环节 7）：两种步长轨迹的逐点差
   → `[0, 1/4, 5/16, 19/64, 65/256, 211/1024]`。 -/
#eval trajDiffQ (fstepQ (1/2) 1) (fstepQ (1/4) 1) 0 6

/- **演示 13**（环节 7）：`η = 1` 极端情形 —— 一步到位，误差全零
   → `[1, 0, 0, 0, 0, 0]`。 -/
#eval trajErrQ (fstepQ 1 1) 0 1 6

/- **演示 14**（跨环节）：从数据表检出的律是 `y = 2x`（斜率 2）；
   用斜率 `2` 当目标 `θ*`，跑 5 步误差 → `[2, 1, 1/2, 1/4, 1/8]`。 -/
#eval trajErrQ (fstepQ (1/2) 2) 0 2 5

/- **演示 15**（环节 6/7 一致性）：`tailErrQ` 是第 `N` 步的尾误差
   （`η = 1/2, N = 6`）；`predQ ... 6 = 63/64`，故尾误差 → `1/64`。 -/
#eval tailErrQ (fstepQ (1/2) 1) 0 1 6

end FullPipelineDemo
end Fate
