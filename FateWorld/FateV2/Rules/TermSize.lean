import FateWorld.FateV2.Rules.RuleExec
/-!
  # Rules · TermSize

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TermSize.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：RuleExec
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  规则核心链 · **`Term` 的规模度量与线性复杂度依据**（COMPLEX-1 §5 第 6 条）

  ## 本模块做什么

  `Fate.RuleExec` 定义了可执行语法项 `Term`（10 个构造子）及其

  * `Term.eval  : Term → EnvQ → ℚ`
  * `Term.check : Term → EnvQ → Bool`

  COMPLEX-1 §5 第 6 条声称 `Term.check` 的复杂度是 `O(t)`，其中 `t = Term.size`。
  **Lean 没有复杂度类型系统**，因此本模块**不**形式化 `O(...)` 渐进记号，
  而是形式化该断言**可证的核心内容**：

  1. `Term.size`：语法规模（构造子个数）；
  2. `Term.size_pos`：规模严格为正（空项不存在，递归有下界）；
  3. `Term.size_lt_*`：⭐ 每个**直接子项**的规模**严格小于**父项规模
     —— 这是 `eval`/`check` 的**结构递归必然终止**且**每个子项只被访问一次**
     的形式化依据，也就是「线性」的实质；
  4. `Term.size_lt_of_mem_subterms`：子项列表中每个元素的规模严格小于父项；
  5. `Term.nodes_length`：用 `List` 显式给出的**前序遍历访问序列**长度恰等于 `size`
     ——「总工作量 = 每个节点访问一次」的可计数形式。

  ## ⚠ 诚实标注（方向性）

  * **已形式化**：`size` 的定义、正性、子项严格变小、遍历长度等于 `size`。
  * **未形式化**：`O(·)` 的渐进记号本身（Lean/Mathlib 无此机制），
    以及「单步计算的常数时间」（这属于运行时模型，不在 Lean 的语义之内）。
  * 本模块**不声称**证明了算法复杂度的渐近类；它只证明了线性递归所依赖的
    **结构性质**（终止性 + 访问次数 = 节点数）。
-/

namespace FateV2.Rules
namespace RuleSyntax
namespace Exec

/-! ## §1  规模定义 -/

/-- **语法项的规模**（构造子个数）。 -/
def Term.size : Term → ℕ
  | .const _ => 1
  | .var _ => 1
  | .add a b => Term.size a + Term.size b + 1
  | .mul a b => Term.size a + Term.size b + 1
  | .eq a b => Term.size a + Term.size b + 1
  | .le a b => Term.size a + Term.size b + 1
  | .lt a b => Term.size a + Term.size b + 1
  | .and a b => Term.size a + Term.size b + 1
  | .or a b => Term.size a + Term.size b + 1
  | .not a => Term.size a + 1

@[simp] theorem Term.size_const (c : ℚ) : (Term.const c).size = 1 := rfl
@[simp] theorem Term.size_var (n : ℕ) : (Term.var n).size = 1 := rfl
@[simp] theorem Term.size_add (a b : Term) : (Term.add a b).size = a.size + b.size + 1 := rfl
@[simp] theorem Term.size_mul (a b : Term) : (Term.mul a b).size = a.size + b.size + 1 := rfl
@[simp] theorem Term.size_eq (a b : Term) : (Term.eq a b).size = a.size + b.size + 1 := rfl
@[simp] theorem Term.size_le (a b : Term) : (Term.le a b).size = a.size + b.size + 1 := rfl
@[simp] theorem Term.size_lt (a b : Term) : (Term.lt a b).size = a.size + b.size + 1 := rfl
@[simp] theorem Term.size_and (a b : Term) : (Term.and a b).size = a.size + b.size + 1 := rfl
@[simp] theorem Term.size_or (a b : Term) : (Term.or a b).size = a.size + b.size + 1 := rfl
@[simp] theorem Term.size_not (a : Term) : (Term.not a).size = a.size + 1 := rfl

/-! ## §2  正性 -/

/-- **规模的严格正性**：任何项至少是一个构造子。 -/
theorem Term.size_pos (t : Term) : 0 < t.size := by
  cases t <;> simp

/-- **规模 ≥ 1** 的常用形式。 -/
theorem Term.one_le_size (t : Term) : 1 ≤ t.size := t.size_pos

/-! ## §3  ⭐ 子项规模严格小于父项规模 -/

theorem Term.size_lt_of_add_left (a b : Term) : a.size < (Term.add a b).size := by
  simp only [Term.size_add]; omega

theorem Term.size_lt_of_add_right (a b : Term) : b.size < (Term.add a b).size := by
  simp only [Term.size_add]; omega

theorem Term.size_lt_of_mul_left (a b : Term) : a.size < (Term.mul a b).size := by
  simp only [Term.size_mul]; omega

theorem Term.size_lt_of_mul_right (a b : Term) : b.size < (Term.mul a b).size := by
  simp only [Term.size_mul]; omega

theorem Term.size_lt_of_eq_left (a b : Term) : a.size < (Term.eq a b).size := by
  simp only [Term.size_eq]; omega

theorem Term.size_lt_of_eq_right (a b : Term) : b.size < (Term.eq a b).size := by
  simp only [Term.size_eq]; omega

theorem Term.size_lt_of_le_left (a b : Term) : a.size < (Term.le a b).size := by
  simp only [Term.size_le]; omega

theorem Term.size_lt_of_le_right (a b : Term) : b.size < (Term.le a b).size := by
  simp only [Term.size_le]; omega

theorem Term.size_lt_of_lt_left (a b : Term) : a.size < (Term.lt a b).size := by
  simp only [Term.size_lt]; omega

theorem Term.size_lt_of_lt_right (a b : Term) : b.size < (Term.lt a b).size := by
  simp only [Term.size_lt]; omega

theorem Term.size_lt_of_and_left (a b : Term) : a.size < (Term.and a b).size := by
  simp only [Term.size_and]; omega

theorem Term.size_lt_of_and_right (a b : Term) : b.size < (Term.and a b).size := by
  simp only [Term.size_and]; omega

theorem Term.size_lt_of_or_left (a b : Term) : a.size < (Term.or a b).size := by
  simp only [Term.size_or]; omega

theorem Term.size_lt_of_or_right (a b : Term) : b.size < (Term.or a b).size := by
  simp only [Term.size_or]; omega

theorem Term.size_lt_of_not (a : Term) : a.size < (Term.not a).size := by
  simp only [Term.size_not]; omega

/-! ## §4  子项列表：每个真子项严格小于父项

  对 `Term` 定义「**直接子项列表**」。`size` 沿 `subterms` 关系**严格下降**，
  这是递归下降必然终止的根本原因（即结构递归的秩）。 -/

/-- **直接子项列表**（左侧在前，重复保留）。 -/
def Term.subterms : Term → List Term
  | .const _ => []
  | .var _ => []
  | .add a b => [a, b]
  | .mul a b => [a, b]
  | .eq a b => [a, b]
  | .le a b => [a, b]
  | .lt a b => [a, b]
  | .and a b => [a, b]
  | .or a b => [a, b]
  | .not a => [a]

/-- ⭐ 每个直接子项的规模严格小于父项（`List` 形式）——**线性递归的秩保证**。 -/
theorem Term.size_lt_of_mem_subterms (t s : Term) (h : s ∈ Term.subterms t) :
    Term.size s < Term.size t := by
  cases t with
  | const c => simp [Term.subterms] at h
  | var n => simp [Term.subterms] at h
  | add x y =>
      simp only [Term.subterms, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h1 | h1
      · rw [h1]; exact Term.size_lt_of_add_left x y
      · rw [h1]; exact Term.size_lt_of_add_right x y
  | mul x y =>
      simp only [Term.subterms, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h1 | h1
      · rw [h1]; exact Term.size_lt_of_mul_left x y
      · rw [h1]; exact Term.size_lt_of_mul_right x y
  | eq x y =>
      simp only [Term.subterms, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h1 | h1
      · rw [h1]; exact Term.size_lt_of_eq_left x y
      · rw [h1]; exact Term.size_lt_of_eq_right x y
  | le x y =>
      simp only [Term.subterms, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h1 | h1
      · rw [h1]; exact Term.size_lt_of_le_left x y
      · rw [h1]; exact Term.size_lt_of_le_right x y
  | lt x y =>
      simp only [Term.subterms, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h1 | h1
      · rw [h1]; exact Term.size_lt_of_lt_left x y
      · rw [h1]; exact Term.size_lt_of_lt_right x y
  | and x y =>
      simp only [Term.subterms, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h1 | h1
      · rw [h1]; exact Term.size_lt_of_and_left x y
      · rw [h1]; exact Term.size_lt_of_and_right x y
  | or x y =>
      simp only [Term.subterms, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h1 | h1
      · rw [h1]; exact Term.size_lt_of_or_left x y
      · rw [h1]; exact Term.size_lt_of_or_right x y
  | not x =>
      simp only [Term.subterms, List.mem_cons, List.not_mem_nil, or_false] at h
      exact h.symm ▸ Term.size_lt_of_not x

/-! ## §5  ⭐⭐ 访问序列：遍历长度恰等于 size

  `Term.nodes` 给出**前序遍历**的节点列表。`Term.nodes_length` 说明
  访问序列长度**恰等于** `size`，即「每个节点访问一次」——
  这就是 `eval` / `check` 总递归调用次数 `= size` 的形式化计数版本。 -/

/-- **前序遍历的节点序列**。 -/
def Term.nodes : Term → List Term
  | .const c => [.const c]
  | .var n => [.var n]
  | .add a b => Term.add a b :: (a.nodes ++ b.nodes)
  | .mul a b => Term.mul a b :: (a.nodes ++ b.nodes)
  | .eq a b => Term.eq a b :: (a.nodes ++ b.nodes)
  | .le a b => Term.le a b :: (a.nodes ++ b.nodes)
  | .lt a b => Term.lt a b :: (a.nodes ++ b.nodes)
  | .and a b => Term.and a b :: (a.nodes ++ b.nodes)
  | .or a b => Term.or a b :: (a.nodes ++ b.nodes)
  | .not a => Term.not a :: a.nodes

/-- ⭐⭐ **访问次数 = 规模**：`check`/`eval` 的结构递归恰好调用 `size` 次。 -/
theorem Term.nodes_length (t : Term) : t.nodes.length = t.size := by
  induction t with
  | const c => simp [Term.nodes, Term.size]
  | var n => simp [Term.nodes, Term.size]
  | add a b iha ihb => simp [Term.nodes, Term.size, iha, ihb]
  | mul a b iha ihb => simp [Term.nodes, Term.size, iha, ihb]
  | eq a b iha ihb => simp [Term.nodes, Term.size, iha, ihb]
  | le a b iha ihb => simp [Term.nodes, Term.size, iha, ihb]
  | lt a b iha ihb => simp [Term.nodes, Term.size, iha, ihb]
  | and a b iha ihb => simp [Term.nodes, Term.size, iha, ihb]
  | or a b iha ihb => simp [Term.nodes, Term.size, iha, ihb]
  | not a ih => simp [Term.nodes, Term.size, ih]

/-- `nodes` 中每个元素（含自身）的规模 ≤ `t.size`。 -/
theorem Term.size_le_of_mem_nodes (t s : Term) (h : s ∈ t.nodes) : s.size ≤ t.size := by
  induction t with
  | const c => simp [Term.nodes] at h; subst h; simp
  | var n => simp [Term.nodes] at h; subst h; simp
  | add a b iha ihb =>
      simp only [Term.nodes, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · subst h; simp only [Term.size_add]; omega
      · have := iha h; simp only [Term.size_add] at *; omega
      · have := ihb h; simp only [Term.size_add] at *; omega
  | mul a b iha ihb =>
      simp only [Term.nodes, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · subst h; simp only [Term.size_mul]; omega
      · have := iha h; simp only [Term.size_mul] at *; omega
      · have := ihb h; simp only [Term.size_mul] at *; omega
  | eq a b iha ihb =>
      simp only [Term.nodes, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · subst h; simp only [Term.size_eq]; omega
      · have := iha h; simp only [Term.size_eq] at *; omega
      · have := ihb h; simp only [Term.size_eq] at *; omega
  | le a b iha ihb =>
      simp only [Term.nodes, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · subst h; simp only [Term.size_le]; omega
      · have := iha h; simp only [Term.size_le] at *; omega
      · have := ihb h; simp only [Term.size_le] at *; omega
  | lt a b iha ihb =>
      simp only [Term.nodes, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · subst h; simp only [Term.size_lt]; omega
      · have := iha h; simp only [Term.size_lt] at *; omega
      · have := ihb h; simp only [Term.size_lt] at *; omega
  | and a b iha ihb =>
      simp only [Term.nodes, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · subst h; simp only [Term.size_and]; omega
      · have := iha h; simp only [Term.size_and] at *; omega
      · have := ihb h; simp only [Term.size_and] at *; omega
  | or a b iha ihb =>
      simp only [Term.nodes, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · subst h; simp only [Term.size_or]; omega
      · have := iha h; simp only [Term.size_or] at *; omega
      · have := ihb h; simp only [Term.size_or] at *; omega
  | not a ih =>
      simp only [Term.nodes, List.mem_cons] at h
      rcases h with h | h
      · subst h; simp only [Term.size_not]; omega
      · have := ih h; simp only [Term.size_not] at *; omega

/-! ## §6  ⭐ 递归下降的「规模严格下降」不变量

  对 `Term` 上任意**递归函数**（如 `eval` 需要读值、`check` 需要判定），
  递归调用只发生在**直接子项**上，因此沿调用链规模严格下降。
  下面把这一点打包成「递归深度 ≤ size」的显式陈述：
  `size` 是 `Term` 上的**结构秩**，任何沿 `subterms` 关系下降的序列
  长度不超过起始项的 `size`。 -/

/-- 若 `s` 是 `t` 的直接子项，则 `s.size < t.size`。 -/
theorem Term.size_lt_of_subterm {t s : Term} (h : s ∈ Term.subterms t) : Term.size s < Term.size t :=
  Term.size_lt_of_mem_subterms t s h

/-- **沿 `subterms` 下降的链长度有界**：若 `l` 的头是 `t` 且相邻元素满足
`l[i+1] ∈ subterms l[i]`，则 `l.length ≤ size t`。（「递归深度 ≤ size」。） -/
theorem Term.chain_length_le_size (l : List Term) (t : Term) (hhead : l.head? = some t)
    (hstep : ∀ (i : ℕ) (hi : i + 1 < l.length), l[i + 1] ∈ Term.subterms l[i]) :
    l.length ≤ Term.size t := by
  induction l generalizing t with
  | nil => simp at hhead
  | cons x rest ih =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      cases rest with
      | nil => exact Term.size_pos x
      | cons y rest' =>
          have hmem : y ∈ Term.subterms x := by
            have := hstep 0 (by simp)
            simpa using this
          have hlt : Term.size y < Term.size x := Term.size_lt_of_mem_subterms x y hmem
          have ih' : (y :: rest').length ≤ Term.size y := by
            refine ih y rfl ?_
            intro i hi
            have := hstep (i + 1) (by simpa using hi)
            simpa using this
          simp only [List.length_cons] at ih' ⊢
          omega

end Exec
end RuleSyntax
end FateV2.Rules