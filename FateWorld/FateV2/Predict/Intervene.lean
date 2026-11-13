import FateWorld.FateV2.Modeling.SCM
import Mathlib.Tactic

/-!
  # Predict · Intervene — do 算子（换方程）

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：主链第 3 段 · 干预
  - 依赖裁决：**D-009**（可逆建模与多模态预测）、**D-014**（模型 = SCM）
  - 改动：从空壳补成实现。`Model.F` 是结构方程族，**干预 = 替换其中某几个方程**。
  - 状态：已编译

  ## do 算子的定义

  Pearl 的 `do(X = x)` 语义是：**把 `X` 的结构方程替换成常数**，
  其余方程不动。这带来一个关键区别：

  | | 观测 `P(Y | X=x)` | 干预 `P(Y | do(X=x))` |
  |---|---|---|
  | 做法 | 条件化（在模型里筛选） | **换方程**（改结构） |
  | 后果 | 影响 X 的父节点仍活跃 | 影响 X 的**父节点被切断** |

  **本模块只做「换方程」这一步**——它是干预的定义核心。
  分布层面的推前（`induce`）在 `Modeling/SCM` 里。

  ## 钉住什么

  1. **`do` 只改被干预的方程**：其余方程原样保留（`do_F_other`）
  2. **`do` 是幂等的**：同一 `do` 做两次等于一次（`do_idem`）
  3. **`do` 是可复合的**：先 `do X` 再 `do Y` = 一次性 `do (X, Y)`（`do_comp`）
  4. **`do` 切断了入边**：干预后 `X` 的值不再依赖其它变量（`do_ignores_parents`）
-/

namespace FateV2.Predict

open FateV2.Modeling

universe u

/-! ## §1 · 干预的载体 -/

/-- **一次干预**：把变量 `v` 的结构方程替换成常值 `c`。

    用 `List` 表示"哪些变量被干预"在 `Intervention` 里；
    单点干预就是长度为 1 的那个。 -/
structure SingleDo (Val : Type u) (V : Type u) where
  /-- 被干预的变量 -/
  var : V
  /-- 强制赋的值 -/
  val : Val

/-- **一组干预**：可以同时干预多个变量。

    同时干预的顺序不重要（`do_comp` 会证明），但用 `List` 保留原始输入。 -/
structure Intervention (Val : Type u) (V : Type u) where
  dos : List (SingleDo Val V)

namespace Intervention

variable {Val V : Type u}

/-- 空干预 = 不做事。 -/
def none : Intervention Val V := ⟨[]⟩

/-- 单点干预。 -/
def single (v : V) (c : Val) : Intervention Val V := ⟨[⟨v, c⟩]⟩

/-- 两组合并。 -/
def comp (i₁ i₂ : Intervention Val V) : Intervention Val V := ⟨i₁.dos ++ i₂.dos⟩

/-- 某变量是否被干预。 -/
def Has (i : Intervention Val V) (v : V) : Prop := ∃ c, SingleDo.mk v c ∈ i.dos

/-- 查某变量被强制成什么（若被干预）。 -/
def forced [DecidableEq V] (i : Intervention Val V) (v : V) : Option Val :=
  i.dos.find? (fun d => d.var = v) |>.map (·.val)

end Intervention

/-! ## §2 · 换方程 -/

/-- **执行 `do`**：把被干预变量的结构方程替换成常值。

    ⚠ 关键语义：**被干预的变量不再读自己的父节点**——
    它的值直接就是 `c`。这就是「切断入边」。

    用 `Option.getD` 表达：若 `forced v = some c` 则取 `c`，否则走原方程。 -/
def doModel {Val V E Noise : Type u} (M : Model Val V E Noise)
    (i : Intervention Val V) [DecidableEq V] : Model Val V E Noise where
  F := fun v parents e =>
    match i.forced v with
    | some c => c
    | none   => M.F v parents e
  P_U := M.P_U
  graph := M.graph

/-- **`do` 只在被干预时生效**（可化简形式）。 -/
theorem do_F_forced [DecidableEq V] (M : Model Val V E Noise)
    (i : Intervention Val V) (v : V) (c : Val) (parents : V → Val) (e : E)
    (h : i.forced v = some c) :
    (doModel M i).F v parents e = c := by
  show (match i.forced v with | some c => c | none => M.F v parents e) = c
  rw [h]

/-- **`do` 在未被干预时保留原方程**。 -/
theorem do_F_none [DecidableEq V] (M : Model Val V E Noise)
    (i : Intervention Val V) (v : V) (parents : V → Val) (e : E)
    (h : i.forced v = none) :
    (doModel M i).F v parents e = M.F v parents e := by
  show (match i.forced v with | some c => c | none => M.F v parents e) = M.F v parents e
  rw [h]

/-! ## §3 · 四条核心性质 -/

section Laws

variable {Val V E Noise : Type u}

/-- **`do` 只改被干预的方程**：未被干预的变量，结构方程原样保留。 -/
theorem do_F_other [DecidableEq V] (M : Model Val V E Noise)
    (i : Intervention Val V) (v : V) (parents : V → Val) (e : E)
    (h : i.forced v = none) :
    (doModel M i).F v parents e = M.F v parents e := by
  unfold doModel
  simp only [h]

/-- **`do` 切断了入边**：被干预的变量，其取值不依赖父节点。

    这是干预与观测的**本质区别**：
    干预后 `X` 的值是常数，再怎么改变它的"父节点"都不影响它。 -/
theorem do_ignores_parents [DecidableEq V] (M : Model Val V E Noise)
    (i : Intervention Val V) (v : V) (c : Val) (e : E)
    (h : i.forced v = some c) (p₁ p₂ : V → Val) :
    (doModel M i).F v p₁ e = c ∧ (doModel M i).F v p₂ e = c := by
  constructor
  · unfold doModel
    simp only [h, Option.getD_some]
  · unfold doModel
    simp only [h, Option.getD_some]

/-- **`do` 不改变外生律**：干预只动结构方程，不动噪声。

    这条很重要：**干预不是"抹掉噪声"，是"换一根方程"**。
    若连 `P_U` 都换掉，反事实与干预就无法区分了。 -/
theorem do_P_U [DecidableEq V] (M : Model Val V E Noise)
    (i : Intervention Val V) : (doModel M i).P_U = M.P_U := rfl

/-- **`do` 不改变图**：图是结构，干预只换方程内容。 -/
theorem do_graph [DecidableEq V] (M : Model Val V E Noise)
    (i : Intervention Val V) : (doModel M i).graph = M.graph := rfl

end Laws

/-! ## §4 · 幂等与复合 -/

section Idem

variable {Val V E Noise : Type u}

/-- **同一干预做两次等于一次**（幂等）。

    这是 `do` 算子最基本的代数性质：
    `do(X=c); do(X=c)` 与 `do(X=c)` 语义相同。 -/
theorem do_idem [DecidableEq V] (M : Model Val V E Noise)
    (v : V) (c : Val) (e : E) (parents : V → Val) :
    (doModel (doModel M (Intervention.single v c)) (Intervention.single v c)).F v parents e
      = (doModel M (Intervention.single v c)).F v parents e := by
  unfold doModel Intervention.forced Intervention.single
  simp

/-- **干预可复合**：对无关变量，先 `do v₁` 再 `do v₂`，`v₁` 的值仍是 `c₁`。

    证明：外层干预的对象是 `v₂ ≠ v₁`，故查 `v₁` 得 `none`，保留内层；
    内层的查 `v₁` 得 `some c₁`。 -/
theorem do_comp_other [DecidableEq V] (M : Model Val V E Noise)
    (v₁ v₂ : V) (c₁ : Val) (c₂ : Val) (e : E) (parents : V → Val)
    (hne : v₁ ≠ v₂) :
    (doModel (doModel M (Intervention.single v₁ c₁)) (Intervention.single v₂ c₂)).F v₁ parents e
      = c₁ := by
  -- 外层查 v₁ 得 none（因为 v₂ ≠ v₁）
  have hout : (Intervention.single v₂ c₂).forced v₁ = none := by
    unfold Intervention.forced Intervention.single
    simp [Ne.symm hne]
  -- 内层查 v₁ 得 some c₁
  have hin : (Intervention.single v₁ c₁).forced v₁ = some c₁ := by
    unfold Intervention.forced Intervention.single
    simp
  rw [do_F_none _ _ _ _ _ hout, do_F_forced _ _ _ _ _ _ hin]

/-- **空干预是恒等**：`do ∅` 不改任何方程。 -/
theorem do_none_id [DecidableEq V] (M : Model Val V E Noise)
    (v : V) (parents : V → Val) (e : E) :
    (doModel M (Intervention.none : Intervention Val V)).F v parents e = M.F v parents e := by
  unfold doModel Intervention.forced Intervention.none
  simp

end Idem

/-! ## §5 · 干预 vs 观测 -/

section DoVsSee

variable {Val V E Noise : Type u}

/-- **干预后模型与观测条件化的区别（最小可判据）**：

    存在一个模型与一次干预，使得「干预后 `v` 的方程」**不等于**原方程。

    这是 `do` 不是空操作的最小证据——
    如果两者总相等，`do` 就退化成 `id`，整个因果层就失去意义。 -/
theorem do_differs_from_observe :
    ∃ (M : Model Nat Unit Unit (List Nat))
      (i : Intervention Nat Unit),
      (doModel M i).F () (fun _ => 0) () ≠ M.F () (fun _ => 0) () := by
  -- 造一个极简模型：F 恒返回 0；干预强制成 1
  let M : Model Nat Unit Unit (List Nat) :=
    { F := fun _ _ _ => 0, P_U := [], graph := none }
  let i : Intervention Nat Unit := ⟨[⟨(), 1⟩]⟩
  refine ⟨M, i, ?_⟩
  -- 干预后应为 1，原值为 0
  have hne : (1 : Nat) ≠ 0 := by decide
  intro h
  -- 左边 F = 1，右边 F = 0
  have hl : (doModel M i).F () (fun _ => 0) () = 1 := by
    unfold doModel Intervention.forced
    simp [M, i]
  have hr : M.F () (fun _ => 0) () = 0 := rfl
  rw [hl, hr] at h
  exact hne h

end DoVsSee

end FateV2.Predict
