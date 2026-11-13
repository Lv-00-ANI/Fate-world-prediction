/-!
  # Core · 语法（Term / Formula / Data）

  ## 迁移登记
  - 来源：新写（参考 `命运-素材-原始文件-不可更改/Fate/RuleSyntax.lean`、`RuleSyntaxGenOps.lean`）
  - 动作：C 重写
  - 对应环节：F3-14（规则载体）、F3-17（规则集）、F4-24（语法层四算子）
  - 依赖裁决：D-002（载体=IR）、D-003（全是规则）、**D-007**（数据可嵌复杂逻辑）、
              **D-016**（纯 CIC）、**D-017**（不用 Quot）、**D-019**（自由度最大化）
  - 改动：由单层 `RuleTerm`（项/命题混装、写死 `Env := ℕ → ℝ`）拆为
          `Term L` / `Formula L` / `Data L` 三者 mutual，且**对字面量类型 `L` 参数化**。
          核内不出现 `ℚ`、`ℝ`、`Measure`、`Quot`、任何 `Classical` 依赖。
  - 状态：已编译未验证

  ## 为什么三者互相递归
  `Data.logic : Formula L → Data L`（D-007：数据可直接嵌入复杂逻辑结构），
  而 `Term.lit : Data L → Term L`，`Formula` 又引用 `Term`。
  三者构成一个**严格正向**的 mutual 归纳族（Lean 自己的 `Expr` 亦如此）。

  ## 为什么不写死数值类型
  D-019：`L` 是字面量类型参数。`ℚ` 只是它的一个实例，不是核的一部分。
  语义（`denote`）另行参数化在有序域 `K` 上——见后续 `Core/Semantics`。
-/

namespace FateV2.Core

universe u

/-! ## 标识符 -/

/-- 扩展算子的名字（D-006/§6 的 C2 自拓展用） -/
abbrev OpId : Type := String

/-- 扩展谓词的名字 -/
abbrev PredId : Type := String

/-- 实体 / 类别的标识（D-006 的 `ent`） -/
abbrev EntityId : Type := String

/-- 已构造的数据声明的标识（D-006 的 `ref`） -/
abbrev DataId : Type := String

/-! ## 语法族 -/

mutual

/-- **项**：描述世界上的量。

    注意：`lit` 可以携带 `Data.logic`（即一个公式），因此「项」在语法上
    可以承载非数值内容。类正确性由 `WellSorted` 把关，不由类型系统把关
    （这正是 D-003「全是规则」的代价：IR 是无类型语法 + 类正确性谓词）。 -/
inductive Term (L : Type u) : Type u where
  /-- 数据字面量 / 引用 -/
  | lit  (d : Data L)
  /-- 变量（de Bruijn 索引） -/
  | var  (n : Nat)
  /-- 加法 -/
  | add  (a b : Term L)
  /-- 乘法 -/
  | mul  (a b : Term L)
  /-- 取负 -/
  | neg  (a : Term L)
  /-- 扩展算子（C2：加算子 = 加一条注册，不改本 inductive 的语义） -/
  | ext  (op : OpId) (args : List (Term L))

/-- **公式**：可判真假的命题。 -/
inductive Formula (L : Type u) : Type u where
  | eq   (a b : Term L)
  | le   (a b : Term L)
  | lt   (a b : Term L)
  | and  (a b : Formula L)
  | or   (a b : Formula L)
  | not  (a : Formula L)
  | top
  | bot
  /-- 全称量词：`all body` 表示 `∀ x₀, body`（x₀ 是 de Bruijn 0） -/
  | all  (body : Formula L)
  /-- 存在量词 -/
  | ex   (body : Formula L)
  /-- 扩展谓词 -/
  | ext  (p : PredId) (args : List (Term L))

/-- **数据**：可嵌入定理的内容（D-005/D-006/D-007）。

    三种来源：
    * 字面量（`lit`）—— 精确值，最省
    * 实体与引用（`ent` / `ref`）—— 指称具体对象或数据声明
    * **复杂逻辑结构（`logic`）** —— 把公式原样当数据嵌入（D-007 读法 A）
-/
inductive Data (L : Type u) : Type u where
  /-- 字面量（`ℚ` 是它的一个实例，不是核的一部分） -/
  | lit   (l : L)
  /-- 向量 / 序列 -/
  | vec   (xs : List (Data L))
  /-- 元组 -/
  | tup   (xs : List (Data L))
  /-- 实体 / 类别引用 -/
  | ent   (id : EntityId)
  /-- **复杂逻辑结构**：把公式当数据嵌入 -/
  | logic (f : Formula L)
  /-- 数据声明引用 -/
  | ref   (id : DataId)

end

/-! ## 类正确性（WellSorted）

  IR 是**无类型语法**，所以「`add` 一个公式」这类无意义组合在语法上合法。
  类正确性由下面这组谓词把关。

  ### ⚠ 必须遵守的写法约束（否则会静默引入公理）

  **不要用嵌套模式**（如 `| .lit (.logic _) => …`），
  **不要对列表元素递归**（如 `∀ d ∈ xs, d.P`）。

  两者都会让 Lean 无法走结构化递归，退化为 `WellFounded.fix`，
  定义被标 `@[irreducible]` —— **不按构造子归约**；
  于是 `trivial` / `⟨⟩` 都无法展开目标，只能靠 `simp`，
  而 `simp` 会引入 `propext` 与 `Quot.sound` —— **直接违反 D-016**。

  ### 分工（本文件只做「顶层排序」）

  | 检查 | 在哪 |
  |---|---|
  | 算术只施于数值项（拦 `add (lit (logic f)) x`） | ✅ 本文件 |
  | 内嵌公式自证类正确（`lit (logic f)` 里的 `f`） | ✅ 本文件 |
  | 扩展算子的参数签名 | → **注册表（C2）** 把关 |
  | 向量/元组**深层**类正确性 | → `DeepWellSorted`（**B2**） |

  顶层排序是必须现在就有的一条；深层检查可以后补，且不阻断主路径。

  依赖顺序（DAG，用顺序 `def` 而非 `mutual`）：

      Data.IsNumericAtom  →  Term.Numeric  →  Formula.WellSorted
                          →  Data.WellSorted  →  Term.WellSorted
-/

/-- 数据原子的「数值性」标签：能直接当数值用的为 `True`。 -/
def Data.IsNumericAtom {L : Type u} : Data L → Prop
  | .lit _   => True
  | .vec _   => False
  | .tup _   => False
  | .ent _   => False
  | .logic _ => False
  | .ref _   => True

/-! ### 为什么下面三个定义标了 `@[irreducible]`

**实测（2026-11-01）**：`Term`/`Formula`/`Data` 是 **mutual** 归纳族
（`Data.logic : Formula L → Data L` 与 `Term.lit : Data L → Term L` 互指）。
在这类族上写递归函数，Lean 的**结构化递归**不加分析地放弃，
一律退化为 `WellFounded.fix`，并且 `#print axioms` 实测带
**`[propext, Quot.sound]`** —— 直接违反 D-016（核内零公理）。

⟹ 凡是「沿 mutual 环递归」的函数，本核**一律**：
1. 显式标 `@[irreducible]`（不再假装它能按构造子归约）；
2. **不在它上面使用 `rfl` / `trivial` / 构造子显式展开**；
3. 任何需要「按构造子分开说」的定理，改用**独立函数**
   （见 `Core/Subst.lean`：`Term.sigma` 等是独立函数）；或
4. 结论以 `@[irreducible]` 能接受的方式陈述（等式形式，用已证引理传递）。

这条约束同样是**对外契约**：`Term.Numeric` 之类在既有代码里只被
`unfold …; trivial` 式使用（见本文件 `numeric_var`），那要求**可归约**。
故这三个定义**保持可归约**（它们只递归到直接子项，不走 `Data.logic` 环），
而真正跨环的 `Core/Subst.lean` 里的替换才需要上面四条。 -/

/-- 项是否「数值类」：`add`/`mul`/`neg` 只接受数值类项。 -/
def Term.Numeric {L : Type u} : Term L → Prop
  | .lit d      => d.IsNumericAtom
  | .var _      => True
  | .add a b    => a.Numeric ∧ b.Numeric
  | .mul a b    => a.Numeric ∧ b.Numeric
  | .neg a      => a.Numeric
  | .ext _ _    => True            -- 参数签名由注册表（C2）把关

/-- 公式是否类正确：两侧项都必须是数值项。 -/
def Formula.WellSorted {L : Type u} : Formula L → Prop
  | .eq a b  => a.Numeric ∧ b.Numeric
  | .le a b  => a.Numeric ∧ b.Numeric
  | .lt a b  => a.Numeric ∧ b.Numeric
  | .and a b => a.WellSorted ∧ b.WellSorted
  | .or a b  => a.WellSorted ∧ b.WellSorted
  | .not a   => a.WellSorted
  | .top     => True
  | .bot     => True
  | .all b   => b.WellSorted
  | .ex b    => b.WellSorted
  | .ext _ _ => True               -- 参数签名由注册表（C2）把关

/-- 数据是否类正确：内嵌公式必须类正确。 -/
def Data.WellSorted {L : Type u} : Data L → Prop
  | .lit _   => True
  | .vec _   => True               -- 深层检查见 `DeepWellSorted`（B2）
  | .tup _   => True               -- 同上
  | .ent _   => True
  | .logic f => f.WellSorted
  | .ref _   => True

/-- 项是否类正确。

    非数值字面量（内嵌公式）**允许出现在顶部位置**（作为数据被整体引用），
    但其内部必须类正确；其余一律按数值类检查。 -/
def Term.WellSorted {L : Type u} : Term L → Prop
  | .lit d   => d.WellSorted
  | .var _   => True
  | .add a b => a.Numeric ∧ b.Numeric
  | .mul a b => a.Numeric ∧ b.Numeric
  | .neg a   => a.Numeric
  | .ext _ _ => True

/-! ## 基本事实（构造性，零公理） -/

namespace Term

/-- 变量是数值项——最简单的数值项。 -/
theorem numeric_var {L : Type u} (n : Nat) : (Term.var (L := L) n).Numeric := by
  unfold Term.Numeric
  trivial

/-- 两个数值项相加仍是数值项。 -/
theorem numeric_add {L : Type u} {a b : Term L}
    (ha : a.Numeric) (hb : b.Numeric) : (Term.add a b).Numeric := by
  unfold Term.Numeric
  exact ⟨ha, hb⟩

end Term

end FateV2.Core
