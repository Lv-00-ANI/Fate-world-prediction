import FateWorld.Legacy.RuleSyntax
import FateWorld.Legacy.RuleSyntaxOps
import FateWorld.Legacy.RuleSyntaxExt

/-! ===========================================================================
  规则核心链 · **IR 提取到可执行**（乙-3）

  ## 本模块做什么

  `RuleSyntax.lean` 的语义层用 `ℝ`（不可计算）与 `Prop`（不可执行）：

  * `RuleTerm.eval  : RuleTerm → Env → ℝ      `
  * `RuleTerm.holds : RuleTerm → Env → Prop   `

  本模块建立**可执行镜像**：

  * `Term`        —— `ℚ` 上的语法项（与 `RuleTerm` 构造子**逐一同构**）
  * `Term.eval    : Term → EnvQ → ℚ     `  （纯可计算）
  * `Term.check   : Term → EnvQ → Bool  `  （纯可执行判定）
  * `Term.toRuleTerm : Term → RuleTerm `  （`ℚ → ℝ` 嵌入，`Rat.cast`，可计算）

  并证明**可执行版本与语义版本一致**（本模块的核心）：

  * `Term.eval_agree`      : 算术侧一致
  * `Term.check_iff_holds` : ⭐ **`check = true ↔ holds`**

  ## ⚠ 方向性说明（诚实标注）

  **`ℝ → ℚ` 没有可计算算法**（实数编码为 Cauchy 序列 / Dedekind 截断，
  无通用可判定相等），所以**不可能**写出可计算的 `RuleTerm → Term`。

  因此正确的架构是**单向嵌入** `Term → RuleTerm`：

  ```
   可执行项 Term（ℚ） ──toRuleTerm──> 语义项 RuleTerm（ℝ）
        │  eval/check                     │  eval/holds
        ↓                                 ↓
       ℚ / Bool  ←──── 一致性定理 ────>  ℝ / Prop
  ```

  即：**先在与可执行层同构的子语法里构造规则，再向上嵌入做语义推理**。
  这覆盖「可提取」的实质：任何 `Term` 都能被 `#eval` 直接跑出 `Bool`，
  且其结果被本模块的定理**严格绑定**到 `RuleTerm.holds`。

  「提取到可执行」在**本模块所覆盖的子语法（`Term`）上**成立；
  对含**非有理数常数**（如 `Real.pi`、`Real.sqrt 2`）的 `RuleTerm`，
  需先证明该常数来自有理数才可下推，本模块**不声称**覆盖该情形。
-/

namespace Fate
namespace RuleSyntax
namespace Exec

/-! ## §1  可计算的环境与语法项 -/

/-- **可计算的环境**：变量 ↦ 有理数（可判定、可执行）。 -/
abbrev EnvQ := ℕ → ℚ

/-- **可计算的规则语法项**。构造子与 `RuleTerm` **逐一对应**
（含 `lt` —— `RuleTerm` 有 `lt`，本镜像同样必须有，否则一致性不可证）。 -/
inductive Term : Type
  | const (c : ℚ) : Term
  | var (n : ℕ) : Term
  | add (a b : Term) : Term
  | mul (a b : Term) : Term
  | eq (a b : Term) : Term
  | le (a b : Term) : Term
  | lt (a b : Term) : Term
  | and (a b : Term) : Term
  | or (a b : Term) : Term
  | not (a : Term) : Term

/-! ## §2  可计算求值与可执行判定 -/

/-- **可计算求值**（`ℚ`，纯可执行）。

约定与 `RuleTerm.eval` **完全相同**：断言类构造子在算术位置给 `0`。 -/
def Term.eval : Term → EnvQ → ℚ
  | .const c, _ => c
  | .var n, e => e n
  | .add a b, e => a.eval e + b.eval e
  | .mul a b, e => a.eval e * b.eval e
  | _, _ => 0

/-- **可执行判定**（`Bool`，纯可执行）。

约定与 `RuleTerm.holds` **完全相同**：算术类构造子在断言位置给 `true`。 -/
def Term.check : Term → EnvQ → Bool
  | .eq a b, e => decide (a.eval e = b.eval e)
  | .le a b, e => decide (a.eval e ≤ b.eval e)
  | .lt a b, e => decide (a.eval e < b.eval e)
  | .and a b, e => a.check e && b.check e
  | .or a b, e => a.check e || b.check e
  | .not a, e => !(a.check e)
  | _, _ => true

/-! ## §3  单向嵌入 `Term → RuleTerm` -/

/-- **嵌入**：`Term`（`ℚ`，可执行）→ `RuleTerm`（`ℝ`，语义）。
只用 `Rat.cast : ℚ → ℝ`，**可计算**。 -/
def Term.toRuleTerm : Term → RuleTerm
  | .const c => .const (c : ℝ)
  | .var n => .var n
  | .add a b => .add a.toRuleTerm b.toRuleTerm
  | .mul a b => .mul a.toRuleTerm b.toRuleTerm
  | .eq a b => .eq a.toRuleTerm b.toRuleTerm
  | .le a b => .le a.toRuleTerm b.toRuleTerm
  | .lt a b => .lt a.toRuleTerm b.toRuleTerm
  | .and a b => .and a.toRuleTerm b.toRuleTerm
  | .or a b => .or a.toRuleTerm b.toRuleTerm
  | .not a => .not a.toRuleTerm

/-! ## §4  一致性：求值 -/

/-- ⭐⭐⭐ **【可执行 ⟷ 语义的一致性：求值】**

`envQ` 与 `envR` 在每个变量上一致（`envR n = (envQ n : ℝ)`），
则 `Term.eval` 与嵌入后的 `RuleTerm.eval` 在 `ℚ` 上一致。 -/
theorem Term.eval_agree (t : Term) (envQ : EnvQ) (envR : Env)
    (h : ∀ n, envR n = (envQ n : ℝ)) :
    t.toRuleTerm.eval envR = (t.eval envQ : ℝ) := by
  induction t with
  | const c => simp [Term.toRuleTerm, Term.eval, RuleTerm.eval]
  | var n => simp [Term.toRuleTerm, Term.eval, RuleTerm.eval, h n]
  | add a b iha ihb =>
      simp only [Term.toRuleTerm, Term.eval, RuleTerm.eval, iha, ihb, Rat.cast_add]
  | mul a b iha ihb =>
      simp only [Term.toRuleTerm, Term.eval, RuleTerm.eval, iha, ihb, Rat.cast_mul]
  | eq a b iha ihb => simp [Term.toRuleTerm, Term.eval, RuleTerm.eval]
  | le a b iha ihb => simp [Term.toRuleTerm, Term.eval, RuleTerm.eval]
  | lt a b iha ihb => simp [Term.toRuleTerm, Term.eval, RuleTerm.eval]
  | and a b iha ihb => simp [Term.toRuleTerm, Term.eval, RuleTerm.eval]
  | or a b iha ihb => simp [Term.toRuleTerm, Term.eval, RuleTerm.eval]
  | not a iha => simp [Term.toRuleTerm, Term.eval, RuleTerm.eval]

/-! ## §5  ⭐ 核心一致性：判定 -/

/-- ⭐⭐⭐⭐⭐ **【可执行 ⟷ 语义的一致性：判定】**

**本模块的核心定理**：可执行的 `check` 返回 `true` **当且仅当**
嵌入后的 `RuleTerm` 在语义下 `holds`。

证明是对语法项的结构归纳；关键在于 `ℚ` 的 `decide` 命题与
`ℝ` 中对应命题经 `Rat.cast`（严格保序、单射）后等价。 -/
theorem Term.check_iff_holds (t : Term) (envQ : EnvQ) (envR : Env)
    (h : ∀ n, envR n = (envQ n : ℝ)) :
    t.check envQ = true ↔ t.toRuleTerm.holds envR := by
  induction t with
  | const c => simp [Term.toRuleTerm, Term.check, RuleTerm.holds]
  | var n => simp [Term.toRuleTerm, Term.check, RuleTerm.holds]
  | add a b iha ihb => simp [Term.toRuleTerm, Term.check, RuleTerm.holds]
  | mul a b iha ihb => simp [Term.toRuleTerm, Term.check, RuleTerm.holds]
  | eq a b iha ihb =>
      simp only [Term.toRuleTerm, Term.check, RuleTerm.holds, RuleTerm.eval,
        Term.eval_agree a envQ envR h, Term.eval_agree b envQ envR h,
        decide_eq_true_eq, Rat.cast_inj]
  | le a b iha ihb =>
      simp only [Term.toRuleTerm, Term.check, RuleTerm.holds, RuleTerm.eval,
        Term.eval_agree a envQ envR h, Term.eval_agree b envQ envR h,
        decide_eq_true_eq, Rat.cast_le]
  | lt a b iha ihb =>
      simp only [Term.toRuleTerm, Term.check, RuleTerm.holds, RuleTerm.eval,
        Term.eval_agree a envQ envR h, Term.eval_agree b envQ envR h,
        decide_eq_true_eq, Rat.cast_lt]
  | and a b iha ihb =>
      simp only [Term.toRuleTerm, Term.check, RuleTerm.holds,
        Bool.and_eq_true, iha, ihb]
  | or a b iha ihb =>
      simp only [Term.toRuleTerm, Term.check, RuleTerm.holds,
        Bool.or_eq_true, iha, ihb]
  | not a iha =>
      simp only [Term.toRuleTerm, Term.check, RuleTerm.holds]
      cases hc : a.check envQ with
      | false =>
          constructor
          · intro _ hh; exact absurd (iha.mpr hh) (by simp [hc])
          · intro _; rfl
      | true =>
          constructor
          · intro hf; exact absurd hf (by simp)
          · intro hh; exact absurd (iha.mp hc) hh

/-! ## §6  执行入口 -/

/-- ⭐⭐⭐ **【执行的入口：给定环境，算出 `Bool`】** -/
def run (t : Term) (envQ : EnvQ) : Bool := t.check envQ

/-- **执行等价于语义**（`run` 只是 `check` 的别名，故为定义性）。 -/
theorem run_iff_holds (t : Term) (envQ : EnvQ) (envR : Env)
    (h : ∀ n, envR n = (envQ n : ℝ)) :
    run t envQ = true ↔ t.toRuleTerm.holds envR :=
  Term.check_iff_holds t envQ envR h

/-- **执行结果 `false` ⟺ 语义不成立**（逆否形式，便于执行侧反证用）。 -/
theorem run_eq_false_iff_not_holds (t : Term) (envQ : EnvQ) (envR : Env)
    (h : ∀ n, envR n = (envQ n : ℝ)) :
    run t envQ = false ↔ ¬ t.toRuleTerm.holds envR := by
  rw [← run_iff_holds t envQ envR h]
  cases run t envQ <;> simp

/-! ## §7  可执行侧的语义等式（全部 `rfl`，证明 `Term` 真的能跑） -/

@[simp] theorem check_eq (a b : Term) (e : EnvQ) :
    (Term.eq a b).check e = decide (a.eval e = b.eval e) := rfl

@[simp] theorem check_le (a b : Term) (e : EnvQ) :
    (Term.le a b).check e = decide (a.eval e ≤ b.eval e) := rfl

@[simp] theorem check_lt (a b : Term) (e : EnvQ) :
    (Term.lt a b).check e = decide (a.eval e < b.eval e) := rfl

@[simp] theorem check_and (a b : Term) (e : EnvQ) :
    (Term.and a b).check e = (a.check e && b.check e) := rfl

@[simp] theorem check_or (a b : Term) (e : EnvQ) :
    (Term.or a b).check e = (a.check e || b.check e) := rfl

@[simp] theorem check_not (a : Term) (e : EnvQ) :
    (Term.not a).check e = !(a.check e) := rfl

/-- **具体执行例**：`1 + 1 = 2` 的可执行判定为 `true`。 -/
theorem check_sample_eq_true :
    (Term.eq (Term.add (Term.const 1) (Term.const 1)) (Term.const 2)).check
      (fun _ => 0) = true := by
  simp [Term.check, Term.eval]
  norm_num

/-- **具体执行例**：`1 < 2` 的可执行判定为 `true`。 -/
theorem check_sample_lt_true :
    (Term.lt (Term.const 1) (Term.const 2)).check (fun _ => 0) = true := by
  simp [Term.check, Term.eval]

/-- **具体执行例**：`2 ≤ 1` 的可执行判定为 `false`（执行侧真的会否定）。 -/
theorem check_sample_false :
    (Term.le (Term.const 2) (Term.const 1)).check (fun _ => 0) = false := by
  simp [Term.check, Term.eval]

/-! ## §8  与 `LawRule` 的执行侧对接

`toRuleTerm` 之后即可直接用 `RuleSyntax.toLawRuleWith` 得到 `LawRule`，
于是「可执行项」与「语义 `LawRule`」之间**无需新增假设**。 -/

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-- ⭐ **可执行项 → `LawRule`**：`interp` 给出环境，`t` 给出约束。

这是「IR 提取到可执行」在 `LawRule` 层的落点：
左侧是完全可计算的 `Term`，右侧是已建立的语义 `LawRule`。 -/
def toLawRuleExec (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : Term) : Fate.LawRule.LawRule C X Y :=
  toLawRuleWith interp t.toRuleTerm

/-- **执行侧落点的成员判据**（定义性）。 -/
@[simp] theorem toLawRuleExec_apply
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : Term) (c : C.Carrier) (x : X.Carrier)
    (μ : MeasureTheory.Measure Y.Carrier) :
    μ ∈ toLawRuleExec interp t c x ↔ t.toRuleTerm.holds (interp c x μ) :=
  Iff.rfl

/-- ⭐⭐⭐ **【端到端：可执行判定 ⟹ 分布被允许】**

若 `interp` 在 `(c, x, μ)` 上给出的环境是某个 `envQ` 的 cast，
且 `t` 的可执行判定为 `true`，则 `μ` 属于该约束给出的 `LawRule`。

这把 `check`（`Bool`）与 `LawRule`（`Set (Measure Y)`）**直接连起来**。 -/
theorem mem_toLawRuleExec_of_check
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : Term) (c : C.Carrier) (x : X.Carrier)
    (μ : MeasureTheory.Measure Y.Carrier) (envQ : EnvQ)
    (henv : ∀ n, interp c x μ n = (envQ n : ℝ))
    (hchk : t.check envQ = true) :
    μ ∈ toLawRuleExec interp t c x :=
  (Term.check_iff_holds t envQ (interp c x μ) henv).mp hchk

/-- ⭐⭐⭐ **【端到端：可执行判定 `false` ⟹ 分布被排除】** -/
theorem not_mem_toLawRuleExec_of_check_false
    (interp : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier → Env)
    (t : Term) (c : C.Carrier) (x : X.Carrier)
    (μ : MeasureTheory.Measure Y.Carrier) (envQ : EnvQ)
    (henv : ∀ n, interp c x μ n = (envQ n : ℝ))
    (hchk : t.check envQ = false) :
    μ ∉ toLawRuleExec interp t c x := by
  simp only [toLawRuleExec_apply]
  exact (run_eq_false_iff_not_holds t envQ (interp c x μ) henv).mp hchk

/-! ## §9  组合子的可执行对应

`RuleSyntaxOps` 的 `trueTerm` 是「无约束」。可执行侧同样存在。 -/

/-- **可执行的无约束项**（算术类构造子在断言位置给 `true`，与语义一致）。 -/
def trueTermExec : Term := .const 0

/-- **无约束项恒真**（可执行侧）。 -/
theorem trueTermExec_check (e : EnvQ) : trueTermExec.check e = true := rfl

/-- **无约束项嵌入后语义上恒真**。 -/
theorem trueTermExec_holds (envR : Env) : trueTermExec.toRuleTerm.holds envR := by
  simp [trueTermExec, Term.toRuleTerm, RuleTerm.holds]

end Exec
end RuleSyntax
end Fate
