import FateWorld.FateV2.Core.Syntax

/-!
  # Core · 注册表（C2 自拓展）

  ## 迁移登记
  - 来源：新写（`裁决D-006 §6.2` 的 C2 自拓展；`Core/Registry.lean` 原为骨架占位）
  - 动作：C 重写
  - 对应环节：F4-24 之后的扩展通道
  - 依赖裁决：**D-006 §6.2**、**D-016**（零公理）、**D-019**（自由度）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## C2 的准确含义

  `Core/Syntax.lean` 的构造子 `Term.ext (op : OpId) (args : List (Term L))` 已经保证
  「加算子不改 `Term` 的 inductive」。缺的是**语义**：新算子的意义从哪来？
  C2 的答案：**从注册表来**。

  > 加一个算子 = 在表里加一条 `(key, 签名)` 记录；
  > **`evalTerm` 这个语义函数一个字都不改**。

  ## ⚠ 实现要点

  1. 查表用 `match` 而不是 `if`/`ite`——`if` 走 `Decidable`，实测带 `propext`；
  2. 判等作为**参数**传入（`test : Key → Key → Bool`），不依赖 `BEq`
     （`BEq.beq` 在 `String` 上是 opaque 的，其反射律要打开内部表示）。
-/

namespace FateV2.Core

universe u

/-! ## 签名 -/

/-- **算子签名**：参数个数 + 语义（`V` 是解释域，D-019）。 -/
structure Sig (V : Type) where
  /-- 参数个数 -/
  arity : Nat
  /-- 语义：参数值列表 → 结果 -/
  denot : List V → V

/-- **注册表**：名字 → 签名（`List`，可结构归纳，零公理）。 -/
abbrev Registry (Key : Type) (V : Type) : Type := List (Key × Sig V)

namespace Registry

/-- **查表**：取第一条**判定为真**的条目。 -/
def lookup (test : Key → Key → Bool) (ρ : Registry Key V) (k : Key) : Option (Sig V) :=
  match ρ with
  | []            => none
  | (k', s) :: t  =>
      match test k k' with
      | true  => some s
      | false => lookup test t k

/-- 注册一条（放表头）。 -/
def register (ρ : Registry Key V) (k : Key) (s : Sig V) : Registry Key V :=
  (k, s) :: ρ

/-- 空注册表。 -/
def empty : Registry Key V := []

/-- **【扩展：既有条目不受影响】**

    若 `test k' k = false`，则查 `k'` 的结果**穿过**刚加的表头，与原表一致。 -/
theorem lookup_register_ne {K V : Type} (test : K → K → Bool) (ρ : Registry K V)
    (k k' : K) (s : Sig V) (h : test k' k = false) :
    (register ρ k s).lookup test k' = ρ.lookup test k' := by
  show (match test k' k with | true => some s | false => lookup test ρ k')
      = lookup test ρ k'
  rw [h]

/-- **【扩展：新条目立刻可查】** -/
theorem lookup_register_eq {K V : Type} (test : K → K → Bool) (ρ : Registry K V)
    (k : K) (s : Sig V) (h : test k k = true) :
    (register ρ k s).lookup test k = some s := by
  show (match test k k with | true => some s | false => lookup test ρ k) = some s
  rw [h]

end Registry

/-! ## 求值 -/

/-- **求值上下文**：项算子注册表 + 判等。 -/
structure EvalCtx (L : Type) where
  /-- 项算子注册表（Term L 的解释域） -/
  termReg : Registry OpId (Term L)
  /-- 判等 -/
  test : OpId → OpId → Bool

/-- **项求值**（`V = Term L`）：遇到 `ext` 时查注册表并调用其 `denot`；查不到则 `none`。

    ⚠ **这就是「语义函数不改」**：本函数里**没有任何一个算子的名字**。 -/
def evalTerm {L : Type} (c : EvalCtx L) : Term L → Option (Term L)
  | .lit _    => none
  | .var _    => none
  | .add a b  =>
      match evalTerm c a with
      | some x =>
          (match evalTerm c b with
           | some y => some (.add x y)
           | none => none)
      | none => none
  | .mul a b  =>
      match evalTerm c a with
      | some x =>
          (match evalTerm c b with
           | some y => some (.mul x y)
           | none => none)
      | none => none
  | .neg a    => match evalTerm c a with
                 | some x => some (.neg x)
                 | none => none
  | .ext op as =>
      match c.termReg.lookup c.test op with
      | none => none
      | some s => some (s.denot as)

/-- **【无隐式默认语义】**

    若 `op` 在两份注册表里都**查不到**，则 `evalTerm` 对 `ext op args`
    都返回 `none`：注册表扩展**不会**凭空给未注册算子一个语义。

    比定义多说了什么：`evalTerm` 的 `ext` 分支是「查表 → 查不到 → `none`」，
    但本定理要它对**两份不同的表**同时成立，且 `args` 任意。 -/
theorem eval_stable_of_absent {L : Type} (c₁ c₂ : EvalCtx L) (op : OpId)
    (h₁ : c₁.termReg.lookup c₁.test op = none)
    (h₂ : c₂.termReg.lookup c₂.test op = none) (args : List (Term L)) :
    evalTerm c₁ (.ext op args) = none ∧ evalTerm c₂ (.ext op args) = none := by
  constructor
  · unfold evalTerm
    rw [h₁]
  · unfold evalTerm
    rw [h₂]

/-! ## 实例：C2 的实际演示（D-019 原则 2：每个抽象至少一个实例） -/

/-- `neg'`：一元取负。 -/
def sigNeg : Sig (Term L) :=
  ⟨1, fun vs =>
      match vs with
      | [x] => Term.neg x
      | _   => Term.var 0⟩

/-- `sumN`：任意元的合成（元数由注册决定）。 -/
def sigSum (n : Nat) : Sig (Term L) :=
  ⟨n, fun vs => Term.ext "sum" vs⟩

/-- **默认项注册表**（后注册在前）。 -/
def coreTermReg : Registry OpId (Term L) :=
  Registry.register
    (Registry.register
      (Registry.register Registry.empty "neg'" sigNeg)
      "sum2" (sigSum 2))
    "succ" (sigSum 1)

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | 判等用 `BEq` 而非参数 | `BEq.beq` 在 `String` 上 opaque，反射律要打开内部表示；本批把判定作参数，避免 batteries 的 `BEq` 引理（带 `propext`） |
  | 2 | 谓词注册表 | 本批只做项侧；谓词侧形状相同 |
  | 3 | `sigSum` 的语义 | 用 `Term.ext "sum"` 转写，是**占位**（真正语义需数值域，核内没有） |
-/

end FateV2.Core
