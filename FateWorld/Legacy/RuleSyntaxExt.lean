import FateWorld.Legacy.RuleSyntax
import FateWorld.Legacy.RuleSyntaxOps

/-! ===========================================================================
  规则核心链 · **IR 语法扩展层**（乙-2 第 2 件）

  ## 本模块做什么

  乙-1 的 `Fate.RuleSyntax.RuleTerm` 覆盖：变量 / 等式 / 不等式 / 算术 / 复合；
  乙-2 第 1 件 `Fate.RuleSyntaxOps` 在其上给出四算子 `α / γ / υ / ∘`。

  `_audit/IR-1-规则CIC语法层.md` 的对照表登记了三项**未覆盖**要素：

  * **概率声明**（「以概率 ≥ p 成立」）
  * **求导 / 积分**
  * **归纳构造（iter）**

  本模块**不修改** `RuleSyntax.lean` / `RuleSyntaxOps.lean`（那会破坏已完成部分），
  而是另立 **`ExtTerm`**（包裹 `RuleTerm` 的扩展语法项），把上面三项加进来。

  ## 构造子与语义

  | 构造子 | 科学形式 | 语义（**第一版**） |
  |---|---|---|
  | `base t`    | 嵌入基础项             | `t.holds e` |
  | `prob p t`  | 概率声明「以概率 ≥ p 成立」 | **忽略 `p`，等价于 `t`**（诚实占位，见 §6） |
  | `deriv t`   | 求导                   | **占位：等价于 `t`**（不表示导数，见 §6） |
  | `iter n t`  | 归纳构造「重复 `n` 次都成立」 | `t` 的 `n` 重叠加取，即 `∀ i < n, t.holds e` |

  ## 定理（`EXIT=0`，无 `sorry`）

  | # | 声明 | 内容 |
  |---|---|---|
  | 1–3 | `holds_base` / `holds_prob` / `holds_deriv` | 各构造子的语义等式 |
  | 4–5 | `holds_iter_zero` / `holds_iter_succ` | `iter` 的两条方程引理 |
  | 6 | `holds_iter_iff` | ⭐⭐ **迭代 ≡ `n` 次重复合取**：`iter n t` 成立 ⟺ `∀ i < n, t.holds e` |
  | 7 | `holds_iter_mono` | ⭐ **迭代的单调性**：`n ≤ m` ⟹ `iter m` 成立则 `iter n` 成立 |
  | 8 | `holds_iter_one` | ⭐⭐ **迭代 1 次 = 本身** |
  | 9 | `holds_iter_succ_iff` | 前向拆解：`iter (n+1)` 成立 ⟺ `t` 成立且 `iter n` 成立 |
  | 10 | `mem_toLawRuleExt_iff` | `ExtTerm → LawRule` 的成员判据 |
  | 11 | `toLawRuleExt_base` | ⭐⭐ **基础嵌入保语义**：`toLawRuleExt (.base t) = toLawRuleWith t` |
  | 12 | `toLawRuleExt_prob_eq` / `toLawRuleExt_deriv_eq` | `prob` / `deriv` 第一版与 `t` 的 `LawRule` 相同（占位登记） |
  | 13 | `toLawRuleExt_iter_zero` | `iter 0` 的允许集是全集 |
  | 14 | `toLawRuleExt_iter_succ` | `iter (n+1)` 的允许集 = `t` ∩ `iter n` |
  | 15 | `toLawRuleExt_iter_antitone` | `n ≤ m` ⟹ `iter m` 的允许集**包含于** `iter n` 的允许集 |
  | 16 | `toLawRuleExt_iter_one` | `iter 1 t` 的允许集 = `t` 的允许集 |
  | 17 | `toLawRuleExt_iter_one_base` | 两条桥在嵌入项上不冲突 |
  | 18 | `holds_iter_prob_iff` / `toLawRuleExt_iter_prob_eq` | `prob` 与 `iter` 的交互（`Prop` 层 / `LawRule` 层） |

  ⚠ **如实登记**：第 1–3、4–5 条**不是** `rfl`，而是 `by simp [ExtTerm.holds]`。
  原因：`ExtTerm.holds` 含嵌套模式 `| .iter (n+1) t, e`，
  方程编译器对这种定义**只生成命题方程引理**（`RuleTerm.holds` 全用构造子模式，故那边能 `rfl`）。
  这不影响使用——等式照样是 `[simp]` 引理。

  ## ⚠ 诚实边界（务必先读）

  1. **`prob` 是占位**。第一版只登记「概率声明是一个语法构造子」，
     **不解释阈值 `p`**：`prob p t` 的语义**完全等于** `t`。
     「以概率 ≥ p 成立」需要**合适的概率空间 / 测度论外延**
     （对 `Measure` 上的约束，而非对 `Env : ℕ → ℝ` 上的约束），
     那是后续工作；本模块**不声称**已实现概率语义。
     见 `holds_prob` / `toLawRuleExt_prob_eq`——两条定理正是**占位的事实登记**。

  2. **`deriv` 是占位**。`Env := ℕ → ℝ` 只有变量**取值**，没有**函数**，
     故没有可微结构，也没有导数可言：`deriv t` 的语义**完全等于** `t`。
     「求导 / 积分」需要把 `Env` 升级为「变量 ↦ 函数」或引入 Sobolev/微分结构，
     那是后续工作；本模块**不声称**已实现微分语义。

  3. **`iter` 的语义选「重复 `n` 次都成立」（而非「迭代状态」）**。
     理由：`Env` 只有变量、**没有状态值**；「迭代状态」需要状态转移律 `x_{k+1} = f(x_k)`，
     那属于 `Step` / `Traj` 层（见 `Fate/Basic.lean` 的 `Traj`），**不是** `RuleTerm`。
     在约束层的正确对应物是「同一约束重复 `n` 次都成立」，
     即 `n` 重叠加取——这与 `RuleTerm.holds` 的 `and` 语义**一致**
     （`and a b` 的解释就是 `a.holds ∧ b.holds`）。

  4. **`RuleTerm.holds` 对算术子项返回 `True`**（`Fate/RuleSyntax.lean` §3 的
     登记约定）。本模块的 `ExtTerm.holds` **逐字沿用**这一约定：
     `base` 直接委托给 `t.holds`，`iter` 只做 `∧` 合成，
     故不存在与基础语义冲突之处。

  5. **未构造任何具体的 `interp`**（与 `RuleSyntax.lean` 保持同一立场）：
     `toLawRuleExt` 只把它当参数。

  本模块**不修改任何既有模块**，只新建。
============================================================================ -/

namespace Fate
namespace RuleSyntaxExt

open Fate.RuleSyntax
/- `LawRule` 活在下游命名空间 `Fate.LawRule` 内（与 `RuleSyntax.lean:51` 一致）。 -/
open Fate.LawRule

/-! ### §1  扩展语法项 -/

/-- **扩展语法项**：包裹基础 `RuleTerm`，并加三项。

| 构造子 | 科学形式 | 语义（第一版） |
|---|---|---|
| `base t` | 嵌入基础项 | `t.holds e` |
| `prob p t` | 概率声明「以概率 ≥ p 成立」 | **忽略 `p`，等价于 `t`**（诚实占位） |
| `deriv t` | 求导 | **占位：等价于 `t`** |
| `iter n t` | 归纳构造「重复 `n` 次都成立」 | `t` 的 `n` 重叠加取 | -/
inductive ExtTerm : Type
  /-- 嵌入基础项 -/
  | base  (t : RuleTerm)
  /-- 概率声明「以概率 ≥ `p` 成立」（**第一版忽略 `p`**） -/
  | prob  (p : ℚ) (t : ExtTerm)
  /-- 求导（**第一版为占位，语义等价于 `t`**） -/
  | deriv (t : ExtTerm)
  /-- 归纳构造「重复 `n` 次都成立」 -/
  | iter  (n : ℕ) (t : ExtTerm)

/-! ### §2  语义 -/

/-- **扩展项的真值**。

`iter` 的结构递归写作「`n+1` 时 `t` 成立且 `iter n t` 成立」，
故 `iter n t` 恰是 `t` 的 `n` 重叠加取（见 `holds_iter_iff`）。 -/
def ExtTerm.holds : ExtTerm → Env → Prop
  | .base t, e => t.holds e
  | .prob _p t, e => t.holds e          -- 第一版：忽略概率阈值
  | .deriv t, e => t.holds e            -- 第一版：求导占位
  | .iter 0 _t, _e => True
  | .iter (n+1) t, e => t.holds e ∧ (ExtTerm.iter n t).holds e

/-! ### §3  语义等式

⚠ **诚实登记**：下列等式是**命题相等**（`by simp [ExtTerm.holds]`），
**不是** `rfl`。原因：`ExtTerm.holds` 含嵌套模式 `| .iter (n+1) t, e`
（`RuleTerm.holds` 全用构造子模式，故那里能 `rfl`），
方程编译器对这种定义**只生成命题方程引理**，不保留定义性展开。
这不影响使用——等式照样是 `[simp]` 引理。 -/

@[simp] theorem holds_base (t : RuleTerm) (e : Env) :
    (ExtTerm.base t).holds e = t.holds e := by simp [ExtTerm.holds]

@[simp] theorem holds_prob (p : ℚ) (t : ExtTerm) (e : Env) :
    (ExtTerm.prob p t).holds e = t.holds e := by simp [ExtTerm.holds]

@[simp] theorem holds_deriv (t : ExtTerm) (e : Env) :
    (ExtTerm.deriv t).holds e = t.holds e := by simp [ExtTerm.holds]

@[simp] theorem holds_iter_zero (t : ExtTerm) (e : Env) :
    (ExtTerm.iter 0 t).holds e := by simp [ExtTerm.holds]

@[simp] theorem holds_iter_succ (n : ℕ) (t : ExtTerm) (e : Env) :
    (ExtTerm.iter (n+1) t).holds e = (t.holds e ∧ (ExtTerm.iter n t).holds e) := by
  simp [ExtTerm.holds]

/-- 前向拆解（把 `iter (n+1)` 换成「`t` 且 `iter n`」）——
即 `holds_iter_succ` 的 `↔` 形式，便于 `rw`。 -/
theorem holds_iter_succ_iff (n : ℕ) (t : ExtTerm) (e : Env) :
    (ExtTerm.iter (n+1) t).holds e ↔ (t.holds e ∧ (ExtTerm.iter n t).holds e) := by
  rw [holds_iter_succ]

/-! ### §4  ⭐⭐ 迭代 ≡ 重复合取 -/

/-- ⭐⭐ **【迭代 ≡ 重复合取】**：`iter n t` 成立 ⟺ 对每个 `i < n`，`t` 都成立。 -/
theorem holds_iter_iff (n : ℕ) (t : ExtTerm) (e : Env) :
    (ExtTerm.iter n t).holds e ↔ ∀ i : ℕ, i < n → t.holds e := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [holds_iter_succ_iff, ih]
    constructor
    · rintro ⟨h0, hall⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact hall i hlt
      · subst heq; exact h0
    · intro hall
      exact ⟨hall 0 (Nat.zero_lt_succ k),
        fun i hi => hall i (Nat.lt_succ_of_lt hi)⟩

/-- ⭐ **【迭代的单调性】**：`n ≤ m` 且 `iter m t` 成立 ⟹ `iter n t` 成立。 -/
theorem holds_iter_mono {n m : ℕ} (h : n ≤ m) (t : ExtTerm) (e : Env)
    (ht : (ExtTerm.iter m t).holds e) : (ExtTerm.iter n t).holds e := by
  rw [holds_iter_iff] at ht ⊢
  exact fun i hi => ht i (Nat.lt_of_lt_of_le hi h)

/-- ⭐⭐ **【迭代 1 次 = 本身】**。 -/
theorem holds_iter_one (t : ExtTerm) (e : Env) :
    (ExtTerm.iter 1 t).holds e ↔ t.holds e := by
  simp only [holds_iter_succ, holds_iter_zero, and_true]

/-! ### §5  ⭐ 核心桥：`ExtTerm → LawRule` -/

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/- 注：`Y : OutSpace = StateSpace` 已自带 `MeasurableSpace Y.Carrier` 实例字段，
上行的显式绑定**冗余但无害**（触发一条 overlapping-instances 警告）。
这与 `Fate/RuleSyntax.lean:190` 与 `Fate/RuleSyntaxOps.lean:64` 的写法**完全一致**，
为使下游可直接套用既有引理，本模块不偏离该约定。 -/

/-- **扩展项的语义解释**：与 `RuleSyntax.toLawRuleWith` 同一形状，
直接把 `ExtTerm.holds` 送进允许集。 -/
def toLawRuleExt
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : ExtTerm) : LawRule C X Y :=
  fun c x => {μ | t.holds (interp c x μ)}

/-- **逐点展开**：`toLawRuleExt` 的成员判据（定义性）。 -/
@[simp] theorem mem_toLawRuleExt_iff
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : ExtTerm) (c : C.Carrier) (x : X.Carrier)
    (μ : MeasureTheory.Measure Y.Carrier) :
    μ ∈ toLawRuleExt interp t c x ↔ t.holds (interp c x μ) :=
  Iff.rfl

/-- ⭐⭐ **【基础嵌入保语义】**：`base t` 的 `LawRule` **等于** `toLawRuleWith interp t`。 -/
theorem toLawRuleExt_base
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : RuleTerm) :
    toLawRuleExt interp (ExtTerm.base t) = toLawRuleWith interp t := by
  funext c x
  ext μ
  simp [toLawRuleExt, toLawRuleWith]

/-! ### §6  三项扩展构造子在 `LawRule` 层的对应 -/

/-- ⚠ **占位登记**：`prob p t` 的允许集在第一版**等于** `t` 的允许集
（阈值 `p` 未被解释）。 -/
theorem toLawRuleExt_prob_eq
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (p : ℚ) (t : ExtTerm) :
    toLawRuleExt interp (ExtTerm.prob p t) = toLawRuleExt interp t := by
  funext c x
  ext μ
  simp [toLawRuleExt]

/-- ⚠ **占位登记**：`deriv t` 的允许集在第一版**等于** `t` 的允许集
（未引入微分结构）。 -/
theorem toLawRuleExt_deriv_eq
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : ExtTerm) :
    toLawRuleExt interp (ExtTerm.deriv t) = toLawRuleExt interp t := by
  funext c x
  ext μ
  simp [toLawRuleExt]

/-- **`iter 0` 的允许集 = 全集**：零次重复是空合取，无约束。 -/
theorem toLawRuleExt_iter_zero
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : ExtTerm) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleExt interp (ExtTerm.iter 0 t) c x = Set.univ := by
  ext μ
  simp [toLawRuleExt]

/-- **`iter (n+1)` 的允许集 = `t` 的允许集 ∩ `iter n` 的允许集**。 -/
theorem toLawRuleExt_iter_succ
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (n : ℕ) (t : ExtTerm) (c : C.Carrier) (x : X.Carrier) :
    toLawRuleExt interp (ExtTerm.iter (n+1) t) c x
      = toLawRuleExt interp t c x ∩ toLawRuleExt interp (ExtTerm.iter n t) c x := by
  ext μ
  simp [toLawRuleExt]

/-- **迭代次数的反单调性**：`n ≤ m` ⟹ `iter m` 的允许集**包含于** `iter n` 的允许集
（重复更多次 = 约束更强 = 允许的分布更少）。 -/
theorem toLawRuleExt_iter_antitone
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    {n m : ℕ} (h : n ≤ m) (t : ExtTerm) :
    ∀ c x, toLawRuleExt interp (ExtTerm.iter m t) c x
      ⊆ toLawRuleExt interp (ExtTerm.iter n t) c x := by
  intro c x μ hμ
  exact holds_iter_mono h t (interp c x μ) hμ

/-- **`iter 1 t` 的允许集 = `t` 的允许集**。 -/
theorem toLawRuleExt_iter_one
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : ExtTerm) :
    toLawRuleExt interp (ExtTerm.iter 1 t) = toLawRuleExt interp t := by
  funext c x
  ext μ
  simp [toLawRuleExt]

/-- **扩展项与基础项的缝合**：`base` 之下 `iter 1` 与直接 `base` 一致
（说明两条桥在嵌入项上**不冲突**）。 -/
theorem toLawRuleExt_iter_one_base
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : RuleTerm) :
    toLawRuleExt interp (ExtTerm.iter 1 (ExtTerm.base t)) = toLawRuleWith interp t := by
  rw [toLawRuleExt_iter_one, toLawRuleExt_base]

/-- **`prob` 与 `iter` 的交互（`Prop` 层）**：概率化后的项重复 `n` 次，
与未概率化的项重复 `n` 次**真值相同**（阈值仍未被解释）。 -/
theorem holds_iter_prob_iff (p : ℚ) (n : ℕ) (t : ExtTerm) (e : Env) :
    (ExtTerm.iter n (ExtTerm.prob p t)).holds e ↔ (ExtTerm.iter n t).holds e := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [holds_iter_succ, holds_iter_succ, holds_prob, ih]

/-- **`prob` 与 `iter` 的交互（`LawRule` 层）**：概率化后的项重复 `n` 次，
与未概率化的项重复 `n` 次在第一版**给出同一允许集**（阈值仍未被解释）。 -/
theorem toLawRuleExt_iter_prob_eq
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (p : ℚ) (n : ℕ) (t : ExtTerm) :
    toLawRuleExt interp (ExtTerm.iter n (ExtTerm.prob p t))
      = toLawRuleExt interp (ExtTerm.iter n t) := by
  funext c x
  ext μ
  exact holds_iter_prob_iff p n t (interp c x μ)

end RuleSyntaxExt
end Fate
