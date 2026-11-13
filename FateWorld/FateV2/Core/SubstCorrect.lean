import FateWorld.FateV2.Core.Subst

/-!
  # Core · 替换的恒等律

  ## ⚠ 三条实测出来的红线（本文件就是按它们写的）

  | ❌ 写法 | `#print axioms` |
  |---|---|
  | 恒等律写在一个 `mutual` 块里 | **`[Quot.sound]`**（mutual 归纳子带商） |
  | 用 `funext` 把逐点等式变成函数相等 | **`[Quot.sound]`** |
  | `xs.map` 做列表遍历 | `[propext, Quot.sound]` |

  ✅ 正确做法：
  1. 每条引理**单独**（不进 `mutual`）；
  2. **不用 `funext`**——把「函数相等」换成**逐点**等式（`∀ n, …`）；
  3. 列表遍历**手写**（在 `Core/Subst.lean` 的 mutual 定义里）。

  ## 因此恒等律的形态

  不说 `subst id = id`（那要 `funext`），而说：

  ```
  ∀ (t : Term L), Term.subst (fun n => Term.var n) t = t
  ```

  这正是 Lean 的标准 `Functor` 恒等律形态——**不需要 `funext`**，
  因为 `subst` 的第一参数是替换、第二参数是被替换项，恒等律只在第二参数上陈述。
-/

namespace FateV2.Core

universe u

/-! ## 一层：逐构造子的恒等律（零公理） -/

/-- `subst id` 在 `.var` 上不动。 -/
theorem subst_var_var {L : Type u} (n : Nat) :
    Term.subst (fun k => (Term.var k : Term L)) (Term.var n) = Term.var n := rfl

/-- `subst id` 在 `.add` 上：只需两子项各自的恒等律。 -/
theorem subst_var_add {L : Type u} {a b : Term L}
    (ha : Term.subst (fun k => (Term.var k : Term L)) a = a)
    (hb : Term.subst (fun k => (Term.var k : Term L)) b = b) :
    Term.subst (fun k => (Term.var k : Term L)) (Term.add a b) = Term.add a b := by
  show Term.add (Term.subst (fun k => (Term.var k : Term L)) a)
                (Term.subst (fun k => (Term.var k : Term L)) b) = Term.add a b
  rw [ha, hb]

/-- `subst id` 在 `.mul` 上。 -/
theorem subst_var_mul {L : Type u} {a b : Term L}
    (ha : Term.subst (fun k => (Term.var k : Term L)) a = a)
    (hb : Term.subst (fun k => (Term.var k : Term L)) b = b) :
    Term.subst (fun k => (Term.var k : Term L)) (Term.mul a b) = Term.mul a b := by
  show Term.mul (Term.subst (fun k => (Term.var k : Term L)) a)
                (Term.subst (fun k => (Term.var k : Term L)) b) = Term.mul a b
  rw [ha, hb]

/-- `subst id` 在 `.neg` 上。 -/
theorem subst_var_neg {L : Type u} {a : Term L}
    (ha : Term.subst (fun k => (Term.var k : Term L)) a = a) :
    Term.subst (fun k => (Term.var k : Term L)) (Term.neg a) = Term.neg a := by
  show Term.neg (Term.subst (fun k => (Term.var k : Term L)) a) = Term.neg a
  rw [ha]

/-! ## 列表恒等律（对 `List` 归纳；元素引理作参数，故不与项互递归） -/

/-- **【恒等律 · 项列表】**。 -/
theorem term_substList_id {L : Type u}
    (h : ∀ x : Term L, Term.subst (fun k => (Term.var k : Term L)) x = x) :
    ∀ (ts : List (Term L)), Term.substList (fun k => (Term.var k : Term L)) ts = ts
  | []      => rfl
  | x :: xs => by
      show Term.subst (fun k => (Term.var k : Term L)) x
             :: Term.substList (fun k => (Term.var k : Term L)) xs = x :: xs
      rw [h x, term_substList_id h xs]

/-- **【恒等律 · 数据列表】**。 -/
theorem data_substList_id {L : Type u}
    (h : ∀ x : Data L, Data.subst (fun k => (Term.var k : Term L)) x = x) :
    ∀ (ds : List (Data L)), Data.substList (fun k => (Term.var k : Term L)) ds = ds
  | []      => rfl
  | x :: xs => by
      show Data.subst (fun k => (Term.var k : Term L)) x
             :: Data.substList (fun k => (Term.var k : Term L)) xs = x :: xs
      rw [h x, data_substList_id h xs]

/-! ## `lifts` 逐点恒等

  ⚠ 该引理在 **`Core/Subst.lean`** 里（`lifts_var_at`），不在此处重复定义：
  两处各写一个 `match` 会生成**同名匹配子** `match_1_1`，导致
  `import … failed, environment already contains …`（实测）。 -/

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | `Term.subst_id`（三层互递归的**无前提**恒等律） | **未证**。三层互递归必须 `mutual`，而 `mutual` 归纳子实测带 `Quot.sound`（见文件头）。本文件因此只给**单层**与**列表**两级 |
  | 2 | `Formula.subst` 的 `all`/`ex` 分支所需「两份替换相等」 | 需要 `lifts id = id`（函数相等 → `funext` → `Quot.sound`）。本文件给出**逐点**版 `lifts_var_at`，把它留给下游按点使用（那里只需取值相等，不需要函数相等） |
  | 3 | 单层恒等律（`subst_var_*`）、两个列表恒等律、`lifts_var_at` | **已证且零公理** |
-/

end FateV2.Core
