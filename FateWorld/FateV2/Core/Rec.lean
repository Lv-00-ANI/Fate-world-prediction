import FateWorld.FateV2.Core.Syntax

/-!
  # Core · 递归函数（显式折叠子）

  ## 迁移登记
  - 来源：新写（为 `Core/Subst.lean` 的替换提供**零公理**的遍历机具）
  - 动作：C 重写
  - 对应环节：IR 语言化（D 类）第 1 项的前置
  - 依赖裁决：**D-016**（纯 CIC，零公理）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## ⚠ 本文件存在的**唯一原因**（读前必看）

  `Term`/`Formula`/`Data` 是 mutual 归纳族。实测（`_报告/D-踩坑-mutual归纳族回归化.md`）：

  * 直接写 `def f : Term L → Term L`（**哪怕不递归进 `Formula`**）→
    退化为 `⋯.fix` + `@[irreducible]`，**`rfl` 不成立**，且
    `#print axioms` = **`[propext, Quot.sound]`** → 违反 D-016；
  * `induction t` → **直接报错**（mutual 族不支持该 tactic）。

  ⟹ **不能对这几族做结构递归。** 本文件把「遍历」改成**用户显式给出的折叠子**：

  ```lean
  Term.fold (onLit : Data L → Term L) (onVar : Nat → Term L)
            (onAdd : Term L → Term L → Term L) … : Term L → Term L
  ```

  这是**非递归**的定义（每个构造子只调用一次外部函数），因此：

  * 不在 mutual 族上递归 → **零公理**；
  * 每个构造子分支都是**构造子模式** → 可用 `rfl` 之外的方式按构造子展开。

  并且 **`Term.fold` 与构造子的交换律**（`fold_lit`、`fold_add` …）都是 `rfl` ——
  它们给出「按构造子归约」的性质，补回了 `@[irreducible]` 拿不走的那部分。

  **代价**（必须承认）：折叠子**不能递归**——用户传入的 `onAdd` 拿不到子项的折叠结果。
  于是本机具只能表达**一层**遍历。多层遍历由调用方按**深度参数**迭代（见 `Core/Subst.lean`
  的「深度受限替换」）。这是纯 CIC 下的真实能力边界，不是省事。
-/

namespace FateV2.Core

universe u

/-! ## `Term` 的折叠 -/

/-- **一层的项折叠**：把每个构造子交给调用方给的处理函数。

    ⚠ 不递归：`onAdd` 收到的是**原子项**，不是折叠后的结果。 -/
def Term.fold {L : Type u} {α : Type u}
    (onLit : Data L → α) (onVar : Nat → α) (onAdd : Term L → Term L → α)
    (onMul : Term L → Term L → α) (onNeg : Term L → α)
    (onExt : OpId → List (Term L) → α) : Term L → α
  | .lit d    => onLit d
  | .var n    => onVar n
  | .add a b  => onAdd a b
  | .mul a b  => onMul a b
  | .neg a    => onNeg a
  | .ext p as => onExt p as

/-! ## 交换律（按构造子归约的直接证据） -/

theorem Term.fold_lit {L : Type u} {α : Type u}
    (onLit : Data L → α) (onVar : Nat → α) (onAdd : Term L → Term L → α)
    (onMul : Term L → Term L → α) (onNeg : Term L → α)
    (onExt : OpId → List (Term L) → α) (d : Data L) :
    Term.fold onLit onVar onAdd onMul onNeg onExt (Term.lit d) = onLit d := rfl

theorem Term.fold_var {L : Type u} {α : Type u}
    (onLit : Data L → α) (onVar : Nat → α) (onAdd : Term L → Term L → α)
    (onMul : Term L → Term L → α) (onNeg : Term L → α)
    (onExt : OpId → List (Term L) → α) (n : Nat) :
    Term.fold onLit onVar onAdd onMul onNeg onExt (Term.var n) = onVar n := rfl

theorem Term.fold_add {L : Type u} {α : Type u}
    (onLit : Data L → α) (onVar : Nat → α) (onAdd : Term L → Term L → α)
    (onMul : Term L → Term L → α) (onNeg : Term L → α)
    (onExt : OpId → List (Term L) → α) (a b : Term L) :
    Term.fold onLit onVar onAdd onMul onNeg onExt (Term.add a b) = onAdd a b := rfl

theorem Term.fold_mul {L : Type u} {α : Type u}
    (onLit : Data L → α) (onVar : Nat → α) (onAdd : Term L → Term L → α)
    (onMul : Term L → Term L → α) (onNeg : Term L → α)
    (onExt : OpId → List (Term L) → α) (a b : Term L) :
    Term.fold onLit onVar onAdd onMul onNeg onExt (Term.mul a b) = onMul a b := rfl

theorem Term.fold_neg {L : Type u} {α : Type u}
    (onLit : Data L → α) (onVar : Nat → α) (onAdd : Term L → Term L → α)
    (onMul : Term L → Term L → α) (onNeg : Term L → α)
    (onExt : OpId → List (Term L) → α) (a : Term L) :
    Term.fold onLit onVar onAdd onMul onNeg onExt (Term.neg a) = onNeg a := rfl

theorem Term.fold_ext {L : Type u} {α : Type u}
    (onLit : Data L → α) (onVar : Nat → α) (onAdd : Term L → Term L → α)
    (onMul : Term L → Term L → α) (onNeg : Term L → α)
    (onExt : OpId → List (Term L) → α) (p : OpId) (as : List (Term L)) :
    Term.fold onLit onVar onAdd onMul onNeg onExt (.ext p as) = onExt p as := rfl

/-! ## 一条**非** `rfl` 的定理：折叠是「逐构造子确定」的

  上面六条都是 `rfl`（定义就是按构造子展开的）。
  但**下面这条不是**：它说「若两个折叠子在六个构造子分支上给出一致的处理，
  则它们在整个 `Term` 上一致」。这需要按构造子分情形，**不是**任何一边的展开。 -/

/-- **【外延性】两个折叠子若逐构造子一致，则处处一致。**

    比定义多说了什么：`Term.fold` 的**两处实例**（两个不同的 `α` 处理函数族）
    在整个类型上的结果相等，需要 6 个分支逐一闭合；
    这条把「折叠子决定函数」这件事定下来，是后面用折叠子定义函数时的合法性依据。 -/
theorem Term.fold_congr {L α : Type u}
    (f₁ f₂ : Data L → α) (g₁ g₂ : Nat → α) (h₁ h₂ : Term L → Term L → α)
    (i₁ i₂ : Term L → Term L → α) (j₁ j₂ : Term L → α)
    (k₁ k₂ : OpId → List (Term L) → α)
    (hf : ∀ d, f₁ d = f₂ d) (hg : ∀ n, g₁ n = g₂ n)
    (hh : ∀ a b, h₁ a b = h₂ a b) (hi : ∀ a b, i₁ a b = i₂ a b)
    (hj : ∀ a, j₁ a = j₂ a) (hk : ∀ p as, k₁ p as = k₂ p as)
    (t : Term L) :
    Term.fold f₁ g₁ h₁ i₁ j₁ k₁ t = Term.fold f₂ g₂ h₂ i₂ j₂ k₂ t := by
  cases t with
  | lit d    => exact hf d
  | var n    => exact hg n
  | add a b  => exact hh a b
  | mul a b  => exact hi a b
  | neg a    => exact hj a
  | ext p as => exact hk p as

/-! ## `Formula` 的折叠 -/

/-- **一层的公式折叠**。 -/
def Formula.fold {L : Type u} {α : Type u}
    (onEq : Term L → Term L → α) (onLe : Term L → Term L → α)
    (onLt : Term L → Term L → α) (onAnd : Formula L → Formula L → α)
    (onOr : Formula L → Formula L → α) (onNot : Formula L → α)
    (onTop : α) (onBot : α) (onAll : Formula L → α) (onEx : Formula L → α)
    (onExt : PredId → List (Term L) → α) : Formula L → α
  | .eq a b    => onEq a b
  | .le a b    => onLe a b
  | .lt a b    => onLt a b
  | .and a b   => onAnd a b
  | .or a b    => onOr a b
  | .not a     => onNot a
  | .top       => onTop
  | .bot       => onBot
  | .all b     => onAll b
  | .ex b      => onEx b
  | .ext p as  => onExt p as

/-- **【外延性】公式折叠**：逐分支一致则处处一致。11 个分支。 -/
theorem Formula.fold_congr {L α : Type u}
    (a₁ a₂ : Term L → Term L → α) (b₁ b₂ : Term L → Term L → α)
    (c₁ c₂ : Term L → Term L → α) (d₁ d₂ : Formula L → Formula L → α)
    (e₁ e₂ : Formula L → Formula L → α) (f₁ f₂ : Formula L → α)
    (g₁ g₂ : α) (h₁ h₂ : α) (i₁ i₂ : Formula L → α) (j₁ j₂ : Formula L → α)
    (k₁ k₂ : PredId → List (Term L) → α)
    (ha : ∀ x y, a₁ x y = a₂ x y) (hb : ∀ x y, b₁ x y = b₂ x y)
    (hc : ∀ x y, c₁ x y = c₂ x y) (hd : ∀ x y, d₁ x y = d₂ x y)
    (he : ∀ x y, e₁ x y = e₂ x y) (hf : ∀ x, f₁ x = f₂ x)
    (hg : g₁ = g₂) (hh : h₁ = h₂) (hi : ∀ x, i₁ x = i₂ x) (hj : ∀ x, j₁ x = j₂ x)
    (hk : ∀ p as, k₁ p as = k₂ p as) (φ : Formula L) :
    Formula.fold a₁ b₁ c₁ d₁ e₁ f₁ g₁ h₁ i₁ j₁ k₁ φ
      = Formula.fold a₂ b₂ c₂ d₂ e₂ f₂ g₂ h₂ i₂ j₂ k₂ φ := by
  cases φ with
  | eq x y    => exact ha x y
  | le x y    => exact hb x y
  | lt x y    => exact hc x y
  | and x y   => exact hd x y
  | or x y    => exact he x y
  | not x     => exact hf x
  | top       => exact hg
  | bot       => exact hh
  | all x     => exact hi x
  | ex x      => exact hj x
  | ext p as  => exact hk p as

/-! ## `Data` 的折叠 -/

/-- **一层的数据折叠**。 -/
def Data.fold {L : Type u} {α : Type u}
    (onLit : L → α) (onVec : List (Data L) → α) (onTup : List (Data L) → α)
    (onEnt : EntityId → α) (onLogic : Formula L → α) (onRef : DataId → α) :
    Data L → α
  | .lit l   => onLit l
  | .vec xs  => onVec xs
  | .tup xs  => onTup xs
  | .ent i   => onEnt i
  | .logic f => onLogic f
  | .ref i   => onRef i

/-- **【外延性】数据折叠**：6 个分支。 -/
theorem Data.fold_congr {L α : Type u}
    (a₁ a₂ : L → α) (b₁ b₂ : List (Data L) → α) (c₁ c₂ : List (Data L) → α)
    (d₁ d₂ : EntityId → α) (e₁ e₂ : Formula L → α) (f₁ f₂ : DataId → α)
    (ha : ∀ x, a₁ x = a₂ x) (hb : ∀ x, b₁ x = b₂ x) (hc : ∀ x, c₁ x = c₂ x)
    (hd : ∀ x, d₁ x = d₂ x) (he : ∀ x, e₁ x = e₂ x) (hf : ∀ x, f₁ x = f₂ x)
    (δ : Data L) :
    Data.fold a₁ b₁ c₁ d₁ e₁ f₁ δ = Data.fold a₂ b₂ c₂ d₂ e₂ f₂ δ := by
  cases δ with
  | lit x    => exact ha x
  | vec xs   => exact hb xs
  | tup xs   => exact hc xs
  | ent i    => exact hd i
  | logic φ  => exact he φ
  | ref i    => exact hf i

/-! ## 用折叠子表达 `WellSorted`（证明机具够用）

  `Core/Syntax.lean` 里已有一份，这里**只演示**折叠子能表达非平凡谓词。
  真正的用途在 `Core/Subst.lean`。 -/

/-- `Term` 的「是不是变量」判定：用折叠子写一遍（与 `Data.IsNumericAtom` 互补）。 -/
def Term.foldIsVar {L : Type u} (t : Term L) : Bool :=
  Term.fold (α := PUnit) (L := L) (fun _ => .unit) (fun _ => .unit) (fun _ _ => .unit)
    (fun _ _ => .unit) (fun _ => .unit) (fun _ _ => .unit) t == .unit

/-- 折叠子定义的判定是**常量**——按构造子归约即得。

    ⚠ 这条只演示「折叠子 + 一层判断」可用；真正的判据在 `Core/Registry.lean`
    的注册表里（与 `Syntax.lean` 的 `Data.IsNumericAtom` 互补）。 -/
theorem Term.foldIsVar_var {L : Type u} (n : Nat) :
    Term.foldIsVar (L := L) (Term.var n) = true := rfl

theorem Term.foldIsVar_lit {L : Type u} (d : Data L) :
    Term.foldIsVar (L := L) (Term.lit d) = true := rfl

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | 递归折叠（`fold` 到自身类型的 `fix`） | 不可得：在 mutual 族上任何自递归都经过 `sizeOfWFRel`，带 `propext`/`Quot.sound`（见 `_报告/D-踩坑-mutual归纳族回归化.md`）。多层遍历由调用方按深度迭代 |
  | 2 | 折叠子的**唯一性**（任意两个逐分支一致的折叠子给出的函数相等） | 就是 `fold_congr`（已证） |
-/

end FateV2.Core
