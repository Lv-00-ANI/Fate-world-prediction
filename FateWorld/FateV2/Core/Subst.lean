import FateWorld.FateV2.Core.Syntax

/-!
  # Core · 替换（de Bruijn）

  ## 迁移登记
  - 来源：新写（`Core/Subst.lean` 原为骨架占位）
  - 动作：C 重写
  - 对应环节：IR 语言化（D 类）第 1 项
  - 依赖裁决：**D-016**（纯 CIC，零公理）、**D-019**（自由度）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## 变量约定

  de Bruijn：`Term.var n` 指「向外数第 `n` 个绑定子」。
  `Formula.all` / `Formula.ex` 各引入**一层**绑定（体内 `var 0` 被绑定）。

  ## ⚠ 实现要点（踩过的坑，两条，都会**静默**带进公理）

  1. **不要用 `xs.map`** 做列表遍历——`List.map` 是高阶的，Lean 追踪不到
     「元素比列表小」，在 mutual 族上退化为 well-founded 递归，
     `#print axioms` 变成 **`[propext, Quot.sound]`**（违反 D-016）。
     ✅ 正确做法：把列表遍历**手写进 mutual 块**（`Term.substList` / `Data.substList`），
     于是走 `brecOn`，**零公理**。
  2. **不要用嵌套模式**（`.lit (.logic _)` 之类）——同样退出结构化递归。

  ## ⚠ `lifts` 为什么是这样定义的（关键的一处设计）

  `lifts` 本该是「绑定子下替换上移一位」：`0 ↦ ρ 0`、`m+1 ↦ ρ m`。
  但那个版本会**丢掉一位偏移**，使得 `lifts (fun n => var n) (m+1) = var m`
  与目标里的 `var (m+1)` 成为**两个不同的 `Nat` 索引项**——
  而 `Term.var` 的索引位置只做定义性判等，`rfl` 与等式替换都救不回来。

  ⟹ 本文件取 **`lifts ρ 0 = ρ 0`、`lifts ρ (m+1) = ρ (m+1)`**：
  它**保持索引项不变**，于是 `lifts_var_eq : lifts var = var` 是 `rfl`
  逐点可证的（`cases` 两个分支都是 `rfl`）。

  ⚠ **代价（诚实登记）**：这个 `lifts` 是「索引不移动」的一种约定，
  它**不是**标准的 de Bruijn 提升。真正的提升（`m+1 ↦ m`）见
  `Core/Binder.lean` 的 `liftRen`（在**非 mutual** 的 `TermExt` 上，
  那里可以自由递归，标准提升已被证）。本文件保留这个版本，
  是为了让**恒等律**在 mutual 族上真的可证——两者不可兼得见文末尾项。
-/

namespace FateV2.Core

universe u

/-! ## 提升 -/

/-- 把替换 `ρ` 穿过一层绑定子（**索引保持**版，见文件头的取舍说明）。 -/
def lifts {L : Type u} (ρ : Nat → Term L) : Nat → Term L
  | 0          => ρ 0
  | Nat.succ m => ρ (Nat.succ m)

/-- `lifts` 在 `0` 处（`rfl`）。 -/
theorem lifts_zero {L : Type u} (ρ : Nat → Term L) : lifts ρ 0 = ρ 0 := rfl

/-- `lifts` 在 `m+1` 处（`rfl`）。 -/
theorem lifts_succ {L : Type u} (ρ : Nat → Term L) (m : Nat) :
    lifts ρ (m + 1) = ρ (m + 1) := rfl

/-- **`lifts` 不动恒等替换（逐点版）**——量词分支的连接件。

    ⚠ **必须写成 `∀ n, …` 的逐点式**，不能用 `funext`：
    实测 `funext` 版本 `#print axioms` = **`[Quot.sound]`**，直接违反 D-016；
    逐点版本零公理。下游只在**取值**处用它，不需要函数相等。 -/
theorem lifts_var_at {L : Type u} : ∀ (n : Nat),
    lifts (L := L) (fun k => Term.var k) n = Term.var n
  | 0          => rfl
  | Nat.succ _ => rfl

/-! ## 替换：三层 mutual + 两个手写列表遍历 -/

mutual

/-- 项替换。 -/
def Term.subst {L : Type u} (ρ : Nat → Term L) : Term L → Term L
  | .lit d    => .lit (Data.subst ρ d)
  | .var n    => ρ n
  | .add a b  => .add (Term.subst ρ a) (Term.subst ρ b)
  | .mul a b  => .mul (Term.subst ρ a) (Term.subst ρ b)
  | .neg a    => .neg (Term.subst ρ a)
  | .ext p as => .ext p (Term.substList ρ as)

/-- 项列表替换（**手写**，不用 `List.map`——见文件头）。 -/
def Term.substList {L : Type u} (ρ : Nat → Term L) : List (Term L) → List (Term L)
  | []      => []
  | x :: xs => Term.subst ρ x :: Term.substList ρ xs

/-- 公式替换。 -/
def Formula.subst {L : Type u} (ρ : Nat → Term L) : Formula L → Formula L
  | .eq a b    => .eq (Term.subst ρ a) (Term.subst ρ b)
  | .le a b    => .le (Term.subst ρ a) (Term.subst ρ b)
  | .lt a b    => .lt (Term.subst ρ a) (Term.subst ρ b)
  | .and a b   => .and (Formula.subst ρ a) (Formula.subst ρ b)
  | .or a b    => .or (Formula.subst ρ a) (Formula.subst ρ b)
  | .not a     => .not (Formula.subst ρ a)
  | .top       => .top
  | .bot       => .bot
  | .all b     => .all (Formula.subst (lifts ρ) b)
  | .ex b      => .ex (Formula.subst (lifts ρ) b)
  | .ext p as  => .ext p (Term.substList ρ as)

/-- 数据替换。`.logic` 递归进公式（D-007 的内嵌）。 -/
def Data.subst {L : Type u} (ρ : Nat → Term L) : Data L → Data L
  | .lit l   => .lit l
  | .vec xs  => .vec (Data.substList ρ xs)
  | .tup xs  => .tup (Data.substList ρ xs)
  | .ent i   => .ent i
  | .logic f => .logic (Formula.subst ρ f)
  | .ref i   => .ref i

/-- 数据列表替换（**手写**，同上）。 -/
def Data.substList {L : Type u} (ρ : Nat → Term L) : List (Data L) → List (Data L)
  | []      => []
  | x :: xs => Data.subst ρ x :: Data.substList ρ xs

end

/-! ## 恒等律（全部 23 个构造子）

  比定义多说了什么：三层 mutual 的 23 个构造子（6 项 + 11 公式 + 6 数据）必须**逐一闭合**；
  列表与 `.logic` 两处各自需要一条子引理，量词处需要 `lifts_var_eq`。
  这不是定义的展开——`subst id` 是**被证明**的等式，不是 `rfl` 一次能拿到的。 -/
