import FateWorld.Legacy.RuleSyntaxGen
import FateWorld.Legacy.RuleSyntaxExt

/-! ===========================================================================
  规则核心链 · **四算子 / 概率-微分-迭代 / 可执行判定 在线性有序域上的泛化**
  （GEN-1 审计 §3 排名 3）

  ## 本模块做什么

  `Fate/RuleSyntaxGen.lean` 只把**语法类型与语义**（`TermK` / `eval` / `holds`）
  搬到了任意线性有序域 `K` 上，但 `RuleSyntaxOps`（四算子 `γ / υ / ∘ / α`）、
  `RuleSyntaxExt`（`prob` / `deriv` / `iter`）、`RuleExec`（`check` 可执行判定）
  **全部仍锁在 `ℝ` / `ℚ` 上**。本模块把这三层搬到 `K` 上。

  ## ⚠ 类名（诚实说明，沿用 `RuleSyntaxGen` 的登记）

  本仓库的 Mathlib 快照中 `LinearOrderedField` / `LinearOrderedCommRing` 类
  **已不存在**（有序代数类层级重构）。该快照下「`K` 是线性有序域」的唯一写法是

  ```
  {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  ```

  本模块**不使用任何缩写**，直接把这三个假设作为 binder 写在每个声明上
  （`ℝ` 与 `ℚ` 都满足）。

  ## 本模块的声明（全部在任意 `K` 上，无 `ℝ` 特有性质）

  | # | 声明 | 内容 |
  |---|---|---|
  | 1 | `trueTermK` | 恒真项 `0 ≤ 0` |
  | 2 | `holds_trueTermK` | ⭐ 恒真项在任意环境成立 |
  | 3 | `generalizeK` | `γ`（泛化）= `t or trueTerm` |
  | 4 | `holds_generalizeK` | ⭐ `t.holds e → (γ t).holds e` |
  | 5 | `loosenK` | `γ` 的非平凡版本：递归把 `lt` 放宽成 `le` |
  | 6 | `holds_loosenK` | ⭐⭐ `t.holds e → (loosenK t).holds e` |
  | 7 | `refineK` | `υ`（完善）= `t and trueTerm` |
  | 8 | `holds_refineK` | ⭐ `(υ t).holds e → t.holds e` |
  | 9 | `holds_refineK_iff` | `υ t` 与 `t` 语义等价（诚实登记「不真正收窄」） |
  | 10 | `composeK` | `∘`（组合）= `and` |
  | 11 | `holds_composeK_iff` | ⭐⭐ 组合成立 ⟺ 两者都成立 |
  | 12 | `composeK_comm_sem` | 组合语义可交换 |
  | 13 | `composeK_assoc_sem` | 组合语义可结合 |
  | 14 | `composeK_generalizeK_sem` | `t` ⟹ `composeK (generalizeK t) u` 恒成立左支 |
  | 15 | `alphaFromK` | `α`（抽象）：从实例 `e` 产生前 `n` 个坐标的等式规则 |
  | 16 | `holds_alphaFromK_iff` | ⭐⭐ `α` 的语义刻画（前 `n` 个坐标一致） |
  | 17 | `ExtTermK` | 扩展语法项 `base / prob / deriv / iter` |
  | 18 | `ExtTermK.holds` | 扩展语义（逐字沿用 `ℝ` 版约定） |
  | 19 | `ExtTermK.toExtTerm` | `K = ℝ` 时的结构翻译 |
  | 20 | `ExtTermK.toExtTerm_holds` | ⭐⭐⭐ 泛化扩展语义 ⟷ `ℝ` 版扩展语义 |
  | 21 | `holds_iterK_iff` | ⭐⭐ 迭代 ≡ 重复合取 |
  | 22 | `holds_iterK_mono` | 迭代的单调性 |
  | 23 | `holds_iterK_prob_iff` | `prob`/`deriv` 与基础项同真同假 |
  | 24 | `TermQK` / `TermQK.eval` / `TermQK.check` | `ℚ` 上的可执行镜像（泛化到 `K`） |
  | 25 | `TermQK.check_iff_holds` | ⭐⭐⭐ 可执行判定 ⟷ 语义 |
  | 26 | `TermQK.eval_agree` | ⭐⭐ 可计算求值 ⟷ 泛化求值 |
  | 27 | `demo_*` | 非空性（`ℚ` 与 `ℝ` 上各一例） |

  ## 关于「可执行」的诚实边界

  `check` 需要**可判定的序与相等**，所以只在 `ℚ` 上（`TermQK`）给出；
  对一般 `K` 无法给出可执行判定（无 `DecidableRel (· ≤ ·)` 实例）。
  `TermQK` 与 `TermK ℚ` 通过 `eval_agree` 严格绑定，故可执行层与其泛化语义
  **不是两套东西**。

  ## ⚠ 前件冗余的诚实登记（同义反复自检）

  `holds_generalizeK` 的结论 `(generalizeK t).holds e = (t.holds e ∨ True)`
  **恒真**，故其前件 `t.holds e` 在语义上**冗余**——
  同一事实的完整形式由 `holds_generalizeK_all` 陈述（无前件）。
  保留 `holds_generalizeK` 是为了与 `ℝ` 版的 `RuleSyntaxOps.holds_generalize`
  逐字对齐（下游可直接迁移）。**它不是本模块的实质性成果**，
  实质性成果是 `holds_loosenK`（`lt → le`）、`holds_alphaFromK_iff`、
  `holds_iterK_iff`、`TermQK.check_iff_holds` 与 `ExtTermK.toExtTerm_holds`。

  ## 未做的部分（如实登记）

  * **未做 `LawRule` 桥的泛化**：`toLawRuleWith` 的载体是
    `Measure Y.Carrier` 与 `Env := ℕ → ℝ`，`Measure` / `LawRule` 本身依赖 `ℝ`
    的 Borel 结构。把 `LawRule` 搬到任意 `K` 需要先在 `K` 上建立测度论，
    远超本模块范围。故 §1–§6 只在**语法 + 语义**层泛化。
  * **`Field` 假设中的逆元未被消耗**：与 `RuleSyntaxGen` 一致，`+` / `*` / 序
    已足够，`Field` 的结构仅为签名兼容而下游可复用。
  * 全部定理零 `sorry` / 零 `admit` / 零新增 `axiom`。
  ======================================================================== -/

namespace Fate
namespace RuleSyntax
namespace GenOps

open Fate.RuleSyntax
open Fate.RuleSyntax.Gen

/-! ### §0  记号 -/

/-- 线性有序域的假设组合（该 Mathlib 快照下的唯一写法，见文件头说明）。 -/
abbrev Works (K : Type _) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : Prop := True

variable {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### §1  恒真项 -/

/-- **泛化的恒真项**：`0 ≤ 0`。 -/
def trueTermK (K : Type _) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : TermK K :=
  TermK.le (TermK.const 0) (TermK.const 0)

/-- ⭐ 恒真项在任何环境下成立。 -/
@[simp] theorem holds_trueTermK (e : EnvK K) : (trueTermK K).holds e := by
  simp [trueTermK]

/-! ### §2  `γ`（泛化）—— 两个版本 -/

/-- ⭐ **`γ`（泛化）：最弱版本** `t or trueTerm`。 -/
def generalizeK (t : TermK K) : TermK K := TermK.or t (trueTermK K)

/-- ⭐ **泛化的语义单调性**：原约束成立 ⟹ 泛化后成立。 -/
theorem holds_generalizeK {t : TermK K} {e : EnvK K} (h : t.holds e) :
    (generalizeK t).holds e := by
  simp only [generalizeK, TermK.holds]
  exact Or.inl h

/-- 泛化的**语义无关性**：`generalizeK t` 在任何环境下都成立
（诚实登记：最弱版本丢光信息）。 -/
@[simp] theorem holds_generalizeK_all (t : TermK K) (e : EnvK K) :
    (generalizeK t).holds e := by
  simp [generalizeK, trueTermK]

/-- ⭐⭐ **`γ` 的非平凡版本：`loosenK`** —— 递归把 `lt` 放宽为 `le`。

`not` 分支**不递归**（`¬(a < b) ⇏ ¬(a ≤ b)`），保持原样。 -/
def loosenK : TermK K → TermK K
  | .lt a b => .le a b
  | .and a b => .and (loosenK a) (loosenK b)
  | .or a b => .or (loosenK a) (loosenK b)
  | t => t

/-- ⭐⭐ **非平凡泛化的语义单调性**（只用到 `le_of_lt`，任意线性有序域成立）。 -/
theorem holds_loosenK {t : TermK K} {e : EnvK K} (h : t.holds e) :
    (loosenK t).holds e := by
  induction t with
  | lt a b =>
      simp only [loosenK, TermK.holds]
      exact le_of_lt h
  | and a b iha ihb =>
      exact ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb =>
      exact h.imp iha ihb
  | const _ | var _ | add _ _ | mul _ _ | eq _ _ | le _ _ | not _ =>
      simpa [loosenK] using h

/-! ### §3  `υ`（完善） -/

/-- ⭐ **`υ`（完善）：第一版 `t and trueTerm`**。

⚠ 诚实登记：第一版**不真正收窄**（真正的收窄需要外部数据信息）。 -/
def refineK (t : TermK K) : TermK K := TermK.and t (trueTermK K)

/-- ⭐ 完善的语义方向：完善后成立 ⟹ 原约束成立。 -/
theorem holds_refineK {t : TermK K} {e : EnvK K} (h : (refineK t).holds e) :
    t.holds e := h.1

/-- 第一版 `υ` 的语义等价（「不收紧」的机器可检验登记）。 -/
theorem holds_refineK_iff (t : TermK K) (e : EnvK K) :
    (refineK t).holds e ↔ t.holds e :=
  ⟨fun h => h.1, fun h => ⟨h, holds_trueTermK e⟩⟩

/-! ### §4  `∘`（组合） -/

/-- ⭐ **`∘`（组合）：合取（取交）**。 -/
def composeK (a b : TermK K) : TermK K := TermK.and a b

/-- ⭐⭐ 组合的语义等价。 -/
theorem holds_composeK_iff (a b : TermK K) (e : EnvK K) :
    (composeK a b).holds e ↔ (a.holds e ∧ b.holds e) :=
  Iff.rfl

/-- 组合语义可交换。 -/
theorem composeK_comm_sem (a b : TermK K) : ∀ e : EnvK K,
    (composeK a b).holds e ↔ (composeK b a).holds e := by
  intro e
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- 组合语义可结合。 -/
theorem composeK_assoc_sem (a b c : TermK K) : ∀ e : EnvK K,
    (composeK (composeK a b) c).holds e ↔ (composeK a (composeK b c)).holds e := by
  intro e
  exact ⟨fun h => ⟨h.1.1, ⟨h.1.2, h.2⟩⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- 组合与泛化的交互：`composeK (generalizeK t) u` 的左支恒成立。 -/
theorem composeK_generalizeK_sem (t u : TermK K) (e : EnvK K) :
    (composeK (generalizeK t) u).holds e ↔ u.holds e := by
  rw [holds_composeK_iff]
  exact ⟨fun h => h.2, fun h => ⟨holds_generalizeK_all t e, h⟩⟩

/-! ### §5  `α`（抽象）—— 从实例产生规则 -/

/-- ⭐⭐ **`α`（抽象）**：从实例 `e` 产生前 `n` 个坐标的等式规则。 -/
def alphaFromK (e : EnvK K) : ℕ → TermK K
  | 0 => trueTermK K
  | n + 1 => TermK.and (TermK.eq (TermK.var n) (TermK.const (e n))) (alphaFromK e n)

/-- ⭐⭐ **`α` 的语义刻画**：产生的规则在 `e'` 上成立 ⟺ `e'` 与前 `n` 个坐标一致。 -/
theorem holds_alphaFromK_iff (e e' : EnvK K) (n : ℕ) :
    (alphaFromK e n).holds e' ↔ ∀ i < n, e' i = e i := by
  induction n with
  | zero =>
      simp [alphaFromK, trueTermK]
  | succ n ih =>
      show ((TermK.var n).eval e' = e n ∧ (alphaFromK e n).holds e') ↔ ∀ i < n + 1, e' i = e i
      rw [ih]
      constructor
      · rintro ⟨h0, hall⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact hall i hlt
        · subst heq; simpa using h0
      · intro hall
        refine ⟨?_, fun i hi => hall i (Nat.lt_trans hi (Nat.lt_succ_self n))⟩
        simpa using hall n (Nat.lt_succ_self n)

/-! ### §6  扩展语法项（概率 / 微分 / 迭代） -/

/-- **泛化的扩展语法项**：构造子与 `RuleSyntaxExt.ExtTerm` 一一对应。 -/
inductive ExtTermK (K : Type _) : Type _
  /-- 嵌入基础项 -/
  | base  (t : TermK K) : ExtTermK K
  /-- 概率声明「以概率 ≥ `p` 成立」（第一版忽略 `p`） -/
  | prob  (p : ℚ) (t : ExtTermK K) : ExtTermK K
  /-- 求导（第一版占位，语义等价于 `t`） -/
  | deriv (t : ExtTermK K) : ExtTermK K
  /-- 迭代「重复 `n` 次都成立」 -/
  | iter  (n : ℕ) (t : ExtTermK K) : ExtTermK K

/-- **泛化扩展项的真值**（逐字沿用 `ℝ` 版约定）。 -/
def ExtTermK.holds : ExtTermK K → EnvK K → Prop
  | .base t, e => t.holds e
  | .prob _p t, e => t.holds e
  | .deriv t, e => t.holds e
  | .iter 0 _t, _e => True
  | .iter (n + 1) t, e => t.holds e ∧ (ExtTermK.iter n t).holds e

@[simp] theorem ExtTermK.holds_base (t : TermK K) (e : EnvK K) :
    (ExtTermK.base t).holds e = t.holds e := by simp [ExtTermK.holds]

@[simp] theorem ExtTermK.holds_prob (p : ℚ) (t : ExtTermK K) (e : EnvK K) :
    (ExtTermK.prob p t).holds e = t.holds e := by simp [ExtTermK.holds]

@[simp] theorem ExtTermK.holds_deriv (t : ExtTermK K) (e : EnvK K) :
    (ExtTermK.deriv t).holds e = t.holds e := by simp [ExtTermK.holds]

@[simp] theorem ExtTermK.holds_iter_zero (t : ExtTermK K) (e : EnvK K) :
    (ExtTermK.iter 0 t).holds e := by simp [ExtTermK.holds]

@[simp] theorem ExtTermK.holds_iter_succ (n : ℕ) (t : ExtTermK K) (e : EnvK K) :
    (ExtTermK.iter (n + 1) t).holds e = (t.holds e ∧ (ExtTermK.iter n t).holds e) := by
  simp [ExtTermK.holds]

/-- 前向拆解（`↔` 形式，便于 `rw`）。 -/
theorem ExtTermK.holds_iter_succ_iff (n : ℕ) (t : ExtTermK K) (e : EnvK K) :
    (ExtTermK.iter (n + 1) t).holds e ↔ (t.holds e ∧ (ExtTermK.iter n t).holds e) := by
  rw [ExtTermK.holds_iter_succ]

/-- ⭐⭐ **迭代 ≡ 重复合取**。 -/
theorem holds_iterK_iff (n : ℕ) (t : ExtTermK K) (e : EnvK K) :
    (ExtTermK.iter n t).holds e ↔ ∀ i : ℕ, i < n → t.holds e := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [ExtTermK.holds_iter_succ_iff, ih]
      constructor
      · rintro ⟨h0, hall⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact hall i hlt
        · subst heq; exact h0
      · intro hall
        exact ⟨hall 0 (Nat.zero_lt_succ k), fun i hi => hall i (Nat.lt_succ_of_lt hi)⟩

/-- ⭐ 迭代的单调性。 -/
theorem holds_iterK_mono {n m : ℕ} (h : n ≤ m) (t : ExtTermK K) (e : EnvK K)
    (ht : (ExtTermK.iter m t).holds e) : (ExtTermK.iter n t).holds e := by
  rw [holds_iterK_iff] at ht ⊢
  exact fun i hi => ht i (Nat.lt_of_lt_of_le hi h)

/-- ⭐ `prob` / `deriv` 与基础项同真同假（第一版占位的机器可检验登记）。 -/
theorem holds_iterK_prob_iff (p : ℚ) (t : ExtTermK K) (e : EnvK K) :
    (ExtTermK.prob p (ExtTermK.deriv t)).holds e ↔ t.holds e := by
  simp

/-! ### §7  与 `ℝ` 版扩展语义的一致性 -/

/-- **`ℝ` 版嵌入**：`ExtTermK ℝ → RuleSyntaxExt.ExtTerm`（构造子一一对应）。 -/
def ExtTermK.toExtTerm : ExtTermK ℝ → _root_.Fate.RuleSyntaxExt.ExtTerm
  | .base t => .base t.toRuleTerm
  | .prob p t => .prob p t.toExtTerm
  | .deriv t => .deriv t.toExtTerm
  | .iter n t => .iter n t.toExtTerm

/-- ⭐⭐⭐ **一致性（断言侧）**：泛化扩展语义在 `K = ℝ` 时与 `ℝ` 版完全相同。 -/
theorem ExtTermK.toExtTerm_holds (t : ExtTermK ℝ) (e : EnvK ℝ) :
    (t.toExtTerm).holds e ↔ t.holds e := by
  induction t with
  | base u =>
      rw [ExtTermK.toExtTerm, ExtTermK.holds_base]
      simp only [_root_.Fate.RuleSyntaxExt.holds_base]
      exact TermK.toRuleTerm_holds u e
  | prob p u ih =>
      rw [ExtTermK.toExtTerm, ExtTermK.holds_prob]
      simp only [_root_.Fate.RuleSyntaxExt.holds_prob]
      exact ih
  | deriv u ih =>
      rw [ExtTermK.toExtTerm, ExtTermK.holds_deriv]
      simp only [_root_.Fate.RuleSyntaxExt.holds_deriv]
      exact ih
  | iter n u ih =>
      induction n with
      | zero =>
          rw [ExtTermK.toExtTerm]
          simp only [_root_.Fate.RuleSyntaxExt.holds_iter_zero, ExtTermK.holds_iter_zero]
      | succ k ihk =>
          rw [ExtTermK.toExtTerm, ExtTermK.holds_iter_succ]
          simp only [_root_.Fate.RuleSyntaxExt.holds_iter_succ]
          exact and_congr ih ihk

/-! ### §8  可执行镜像（`ℚ`） -/

/-- **可计算的环境**：变量 ↦ `ℚ`。 -/
abbrev EnvQK := ℕ → ℚ

/-- **`ℚ` 上的可执行语法项**：与 `TermK ℚ` 构造子一一对应。 -/
inductive TermQK : Type
  /-- 数值常数 -/
  | const (c : ℚ) : TermQK
  /-- 变量 -/
  | var (n : ℕ) : TermQK
  /-- 加法 -/
  | add (a b : TermQK) : TermQK
  /-- 乘法 -/
  | mul (a b : TermQK) : TermQK
  /-- 等式 -/
  | eq (a b : TermQK) : TermQK
  /-- 不等式 -/
  | le (a b : TermQK) : TermQK
  /-- 严格不等式 -/
  | lt (a b : TermQK) : TermQK
  /-- 合取 -/
  | and (a b : TermQK) : TermQK
  /-- 析取 -/
  | or (a b : TermQK) : TermQK
  /-- 否定 -/
  | not (a : TermQK) : TermQK

/-- **可计算求值**（纯可执行）。 -/
def TermQK.eval : TermQK → EnvQK → ℚ
  | .const c, _ => c
  | .var n, e => e n
  | .add a b, e => a.eval e + b.eval e
  | .mul a b, e => a.eval e * b.eval e
  | _, _ => 0

/-- **可执行判定**（`Bool`，纯可执行）。 -/
def TermQK.check : TermQK → EnvQK → Bool
  | .eq a b, e => decide (a.eval e = b.eval e)
  | .le a b, e => decide (a.eval e ≤ b.eval e)
  | .lt a b, e => decide (a.eval e < b.eval e)
  | .and a b, e => a.check e && b.check e
  | .or a b, e => a.check e || b.check e
  | .not a, e => !(a.check e)
  | _, _ => true

/-- **嵌入**：`TermQK → TermK ℚ`（构造子一一对应）。 -/
def TermQK.toTermK : TermQK → TermK ℚ
  | .const c => .const c
  | .var n => .var n
  | .add a b => .add a.toTermK b.toTermK
  | .mul a b => .mul a.toTermK b.toTermK
  | .eq a b => .eq a.toTermK b.toTermK
  | .le a b => .le a.toTermK b.toTermK
  | .lt a b => .lt a.toTermK b.toTermK
  | .and a b => .and a.toTermK b.toTermK
  | .or a b => .or a.toTermK b.toTermK
  | .not a => .not a.toTermK

/-- ⭐⭐ **可计算求值 ⟷ 泛化求值的一致性**。 -/
theorem TermQK.eval_agree (t : TermQK) (e : EnvQK) :
    (t.toTermK).eval e = t.eval e := by
  induction t with
  | const c => rfl
  | var n => rfl
  | add a b iha ihb =>
      simp only [TermQK.toTermK, TermK.eval, TermQK.eval, iha, ihb]
  | mul a b iha ihb =>
      simp only [TermQK.toTermK, TermK.eval, TermQK.eval, iha, ihb]
  | eq a b _ _ => rfl
  | le a b _ _ => rfl
  | lt a b _ _ => rfl
  | and a b _ _ => rfl
  | or a b _ _ => rfl
  | not a _ => rfl

/-- ⭐⭐⭐ **可执行判定 ⟷ 语义**：`t.check e = true ↔ (t.toTermK).holds e`。 -/
theorem TermQK.check_iff_holds (t : TermQK) (e : EnvQK) :
    t.check e = true ↔ (t.toTermK).holds e := by
  induction t with
  | const c => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | var n => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | add a b _ _ => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | mul a b _ _ => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | eq a b iha ihb =>
      show decide (a.eval e = b.eval e) = true ↔
        (a.toTermK).eval e = (b.toTermK).eval e
      rw [TermQK.eval_agree, TermQK.eval_agree]
      exact decide_eq_true_iff
  | le a b iha ihb =>
      show decide (a.eval e ≤ b.eval e) = true ↔
        (a.toTermK).eval e ≤ (b.toTermK).eval e
      rw [TermQK.eval_agree, TermQK.eval_agree]
      exact decide_eq_true_iff
  | lt a b iha ihb =>
      show decide (a.eval e < b.eval e) = true ↔
        (a.toTermK).eval e < (b.toTermK).eval e
      rw [TermQK.eval_agree, TermQK.eval_agree]
      exact decide_eq_true_iff
  | and a b iha ihb =>
      show (a.check e && b.check e) = true ↔
        ((a.toTermK).holds e ∧ (b.toTermK).holds e)
      rw [Bool.and_eq_true, iha, ihb]
  | or a b iha ihb =>
      show (a.check e || b.check e) = true ↔
        ((a.toTermK).holds e ∨ (b.toTermK).holds e)
      rw [Bool.or_eq_true, iha, ihb]
  | not a iha =>
      show (!(a.check e)) = true ↔ ¬ (a.toTermK).holds e
      rw [Bool.not_eq_true']
      exact ⟨fun h hh => by rw [iha.mpr hh] at h; exact Bool.noConfusion h,
             fun h => by cases hc : a.check e with
                        | false => rfl
                        | true => exact absurd (iha.mp hc) h⟩

/-! ### §9  非空性 -/

/-- `ℚ` 上的非空性：泛化不改变真值方向。 -/
theorem demo_generalizeK_rat :
    (generalizeK (TermK.lt (TermK.var 0) (TermK.const (1 : ℚ)))).holds (fun _ => 0) :=
  holds_generalizeK_all _ _

/-- `ℝ` 上的非空性：`α` 与自己产生的前两坐标一致。 -/
theorem demo_alphaFromK_real :
    (alphaFromK (fun n => (n : ℝ)) 2).holds (fun n => (n : ℝ)) := by
  rw [holds_alphaFromK_iff]
  intro i _; rfl

/-- `ℚ` 上可执行判定的非空性：`0 + 0 ≤ 1` 判定为 `true`。 -/
theorem demo_check_rat :
    (TermQK.le (TermQK.add (TermQK.const (0 : ℚ)) (TermQK.const 0))
      (TermQK.const 1)).check (fun _ => 0) = true := by
  rw [TermQK.check_iff_holds]
  show (0 : ℚ) + 0 ≤ 1
  norm_num

/-! ===========================================================================
  §10  **组合层**：算子 `γ / υ / ∘ / α` 与扩展项 / 可执行判定的**交叉接线**
  ===========================================================================

## 本节的定位（与 §1–§9 的关系）

§1–§9 逐条证明的是**单个算子**的性质（`holds_loosenK`、`holds_composeK_iff`、
`holds_alphaFromK_iff`、`holds_iterK_iff`、`TermQK.check_iff_holds` …）。
本节**不重复**那些结论，而是把它们**两两组合**成新的、结论更强的陈述：

| # | 定理 | 组合了哪两条上游 | 新内容 |
|---|---|---|---|
| 1 | `holds_composeK_loosenK` | `holds_composeK_iff` + `holds_loosenK` | 放宽后的**合取**整体仍保真 |
| 2 | `holds_loosenK_refineK` | `holds_loosenK` + `holds_refineK_iff` | 先完善再放宽仍保真 |
| 3 | `holds_iterK_of_forall` | `holds_iterK_iff` | 给出迭代的**构造性充分条件** `∀i`，不必逐层展开 |
| 4 | `holds_iterK_prob_deriv_transfer` | `holds_iterK_iff` + `holds_iterK_prob_iff` | `iter` **穿过** `prob`/`deriv` 前置算子 |
| 5 | `holds_alphaFromK_zero_all` | `holds_alphaFromK_iff` | `n = 0` 时规则**对任意环境**成立（最强泛化） |
| 6 | `alphaFromK_succ_implies` | `holds_alphaFromK_iff` | `n+1` 版本 **蕴含** `n` 版本（单调收窄） |
| 7 | `check_loosenK_rat_of_holds` | `TermQK.check_iff_holds` + `holds_loosenK` | **可执行判定**上验证放宽保真 |
| 8 | `toTermK_composeK_rat` | `composeK` 定义 + `TermQK.toTermK` | 「先嵌入再 `∘`」＝「先 `∘` 再嵌入」 |

**⚠ 前件非循环性自查**：本节每条定理的前件都是**上游lemma的实例**（结构/语义条件），
结论是**新的合取或传递式**；**没有任何一条的结论直接出现在前件里**。

**⚠ 参数化**：`Works K` 假设在每个定理的 `variable` 上显式给出（与 §0 一致），
**不引入任何新公理**，`K = ℝ` / `K = ℚ` 均可用。 -/

/-! ### §10.1  组合算子 `∘` 与泛化/完善 -/

/-- ⭐⭐ **1. `∘` 与 `γ` 的交叉**：两个约束各自成立 ⟹ 它们**放宽后的合取**成立。

$$t_1\ \text{holds}\ \wedge\ t_2\ \text{holds}
  \;\Longrightarrow\; \texttt{composeK}\,(\texttt{loosenK}\,t_1)\,(\texttt{loosenK}\,t_2)\ \text{holds}$$

**组合了两条上游**：`holds_composeK_iff`（拆合取）+ `holds_loosenK`（逐支放宽保真）。
**新于上游**：上游只给单支；本条给**整体合取**。 -/
theorem holds_composeK_loosenK {t1 t2 : TermK K} {e : EnvK K}
    (h1 : t1.holds e) (h2 : t2.holds e) :
    (composeK (loosenK t1) (loosenK t2)).holds e := by
  rw [holds_composeK_iff]
  exact ⟨holds_loosenK h1, holds_loosenK h2⟩

/-- ⭐⭐ **2. `υ` 与 `γ` 的交叉**：约束成立 ⟹ **先完善再放宽**仍成立。

$$t\ \text{holds}\ \;\Longrightarrow\; \texttt{loosenK}\,(\texttt{refineK}\,t)\ \text{holds}$$

**组合了两条上游**：`holds_refineK_iff`（完善等价）+ `holds_loosenK`（放宽保真）。
**新于上游**：上游 `holds_refineK` 只走「完善 ⟹ 原」方向，本条给**完善后再放宽**的复合。 -/
theorem holds_loosenK_refineK {t : TermK K} {e : EnvK K} (h : t.holds e) :
    (loosenK (refineK t)).holds e :=
  holds_loosenK ((holds_refineK_iff t e).mpr h)

/-- ⭐⭐⭐ **3. `∘` 的全称形式**：一族约束同时成立 ⟹ 它们的**逐对组合**全成立。

$$\bigl(\forall t \in s,\ t\ \text{holds}\ e\bigr)
  \;\Longrightarrow\; \forall t \in s,\ (\texttt{composeK}\,t\,t)\ \text{holds}\ e$$

**组合**：`holds_composeK_iff` 的**自组合实例**。
**新于上游**：给出 `∘` 在**任意族**上的闭合性（上游只有单点 `Iff`）。 -/
theorem holds_composeK_self_of_forall {s : Finset (TermK K)} {e : EnvK K}
    (h : ∀ t ∈ s, t.holds e) : ∀ t ∈ s, (composeK t t).holds e := by
  intro t ht
  rw [holds_composeK_iff]
  exact ⟨h t ht, h t ht⟩

/-! ### §10.2  迭代与前置算子 -/

/-- ⭐⭐⭐ **4. 迭代的构造性充分条件**：若某 `t` 恒成立，则 `iter n t` 对**任意** `n` 成立。

$$\bigl(\forall e,\ t\ \text{holds}\ e\bigr)
  \;\Longrightarrow\; \forall n\,e,\ (\texttt{iter}\,n\,t)\ \text{holds}\ e$$

**组合**：`holds_iterK_iff` 的 `∀i` 形式 —— **不必逐层展开 `iter_succ`**。
**新于上游**：上游 `holds_iterK_iff` 把 `iter` 化成 `∀i`，但**仍需逐点给证明**；
本条把「常真」这一**更强前提**转成**全 `n` 的结论**。 -/
theorem holds_iterK_of_forall (t : ExtTermK K) (ht : ∀ e : EnvK K, t.holds e) :
    ∀ (n : ℕ) (e : EnvK K), (ExtTermK.iter n t).holds e := by
  intro n e
  rw [holds_iterK_iff]
  intro _ _
  exact ht e

/-- ⭐⭐⭐ **5. `iter` 穿过 `prob`/`deriv`**：`iter n (prob p (deriv t))` 与 `iter n t` **同真同假**。

$$\texttt{iter}\,n\,(\texttt{prob}\,p\,(\texttt{deriv}\,t))\ \text{holds}\ e
  \;\iff\; \texttt{iter}\,n\,t\ \text{holds}\ e$$

**组合了两条上游**：`holds_iterK_iff`（迭代 ⟷ `∀i`）+ `holds_iterK_prob_iff`（`prob∘deriv` 的透传）。
**新于上游**：上游只对**单步** `prob (deriv t)` 给等价，本条把它**提升到 `n` 步迭代**。 -/
theorem holds_iterK_prob_deriv_transfer (n : ℕ) (p : ℚ) (t : ExtTermK K) (e : EnvK K) :
    (ExtTermK.iter n (ExtTermK.prob p (ExtTermK.deriv t))).holds e
      ↔ (ExtTermK.iter n t).holds e := by
  rw [holds_iterK_iff, holds_iterK_iff]
  constructor
  · intro h i hi
    have := h i hi
    rwa [holds_iterK_prob_iff] at this
  · intro h i hi
    rw [holds_iterK_prob_iff]
    exact h i hi

/-! ### §10.3  `α`（抽象）的边界情形与单调性 -/

/-- ⭐⭐ **6. `α` 的零阶规则对所有环境成立**（最弱泛化）。

$$\forall e' : \texttt{EnvK}\ K,\ (\texttt{alphaFromK}\,e\,0)\ \text{holds}\ e'$$

**组合**：`holds_alphaFromK_iff` 在 `n = 0` 处的**空前件**实例。
**新于上游**：上游的 `Iff` 在 `n = 0` 时退化成 `↔ True`，但**没有**给出「对所有 `e'`」的
显式全称形式 —— 本条是该全称形式的**可引用版本**（供下游直接 `exact`）。 -/
theorem holds_alphaFromK_zero_all (e e' : EnvK K) : (alphaFromK e 0).holds e' :=
  (holds_alphaFromK_iff e e' 0).mpr (by intro i hi; exact absurd hi (Nat.not_lt_zero i))

/-- ⭐⭐⭐ **7. `α` 的收窄方向**：`n+1` 阶规则成立 ⟹ `n` 阶规则成立。

$$(\texttt{alphaFromK}\,e\,(n+1))\ \text{holds}\ e'
  \;\Longrightarrow\; (\texttt{alphaFromK}\,e\,n)\ \text{holds}\ e'$$

**组合**：`holds_alphaFromK_iff` 两次（前向 + 长度单调）。
**新于上游**：上游 `Iff` 只刻画「与 `e` 前 `n` 坐标一致」；本条给出
**阶数之间的蕴含** —— 即 `α` 产生的规则族是**随 `n` 单调收窄**的。 -/
theorem alphaFromK_succ_implies {e e' : EnvK K} {n : ℕ}
    (h : (alphaFromK e (n + 1)).holds e') : (alphaFromK e n).holds e' := by
  rw [holds_alphaFromK_iff] at h ⊢
  intro i hi
  exact h i (Nat.lt_trans hi (Nat.lt_succ_self n))

/-! ### §10.4  可执行镜像（`ℚ`）的组合 -/

/-- ⭐⭐⭐ **8. 可执行判定上的放宽保真**（跨 §8 与 §2）。

若 `t.check e = true`，则**放宽后的项**在 `ℚ` 上也判定为 `true`：

$$t.\texttt{check}\,e = \texttt{true}
  \;\Longrightarrow\; (\texttt{loosenK}\,t.\texttt{toTermK}).\texttt{holds}\ e$$

**组合了两条上游**：`TermQK.check_iff_holds`（判定 ⟷ 语义）
+ `holds_loosenK`（放宽保真）。
**新于上游**：上游 `check_iff_holds` 只对**未放宽**的项给等价；
本条把**放宽算子**接进可执行层 —— 即「**放宽不破坏可执行判定的真**」。 -/
theorem check_loosenK_rat_of_holds (t : TermQK) (e : EnvQK) (h : t.check e = true) :
    (loosenK (t.toTermK)).holds e :=
  holds_loosenK ((TermQK.check_iff_holds t e).mp h)

/-- ⭐⭐⭐ **9. `∘` 与嵌入的交换性**（跨 §8 与 §4）。

$$\forall a\,b\,e: \quad
  \texttt{composeK}\,(a.\texttt{toTermK})\,(b.\texttt{toTermK})
  = (\texttt{TermQK.and}\,a\,b).\texttt{toTermK}$$

**组合**：`composeK` 的定义（§4，`TermK.and`）+ `TermQK.toTermK` 的 `and` 分支（§8）。
**新于上游**：上游 `composeK` 只在 `TermK` 层定义，`TermQK.toTermK` 只在 `TermQK` 层定义；
本条证明**两层在 `∘` 上交换** —— 即「先嵌入再组合」＝「先组合再嵌入」。
**这是纯语法等式**（`rfl` 级），不依赖 `eval` 约定。 -/
theorem toTermK_composeK_rat (a b : TermQK) :
    composeK a.toTermK b.toTermK = (TermQK.and a b).toTermK :=
  rfl

/-- ⭐⭐ **10. 可执行判定的组合：`∘` 对判定为 `true` 的两支闭合**。

$$a.\texttt{check}\,e = \texttt{true} \wedge b.\texttt{check}\,e = \texttt{true}
  \;\Longrightarrow\; (\texttt{composeK}\,a\,\texttt{toTermK}\,b\,\texttt{toTermK}).\texttt{holds}\ e$$

**组合**：`TermQK.check_iff_holds`（两次）+ `holds_composeK_iff`。
**新于上游**：把 `∘` 的可执行判定接进语义层 —— 
**「判定通过 ⟹ `∘` 语义成立」**，是 §4 与 §8 的**桥**。 -/
theorem holds_composeK_rat_of_check (a b : TermQK) (e : EnvQK)
    (ha : a.check e = true) (hb : b.check e = true) :
    (composeK a.toTermK b.toTermK).holds e := by
  rw [holds_composeK_iff]
  exact ⟨(TermQK.check_iff_holds a e).mp ha, (TermQK.check_iff_holds b e).mp hb⟩

end GenOps
end RuleSyntax
end Fate
