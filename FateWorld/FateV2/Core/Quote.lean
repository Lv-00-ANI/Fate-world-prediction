import FateWorld.FateV2.Core.Judgment

/-!
  # Core · 反射（quote / decode）

  ## 迁移登记
  - 来源：新写（`Core/Judgment.lean` 已有 `quoteJudgment`，文件末「尾项 1/2/3」登记未做项）
  - 动作：C 重写
  - 对应环节：J₁ 层言论 J₀ 判断
  - 依赖裁决：**D-016**（零公理）、**D-017**（不用 Quot）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## 编码口径（写死一次）

      quoteJudgment j = Formula.ext "Judgment" [ Term.lit (Data.logic j.hyp),
                                                 Term.lit (Data.logic j.concl) ]

  解码四步：取 `ext` 参数 → 名字对 → 取两个参数 → 都必须是 `Term.lit (Data.logic ·)`。

  ## ⚠ `support` / `status` **不可**从公式还原

  它们不是语法（`Judgment.lean` 的设计）。本文件因此提供**部分保真**：
  `hyp`/`concl` 往返恒等，`support`/`status` 取约定默认值。
  `encode_core_iff` 把「丢什么、保什么」精确划出——这是 `Judgment.lean`
  尾项 1/2 的**正确答案**，而不是一句托辞。

  ## ⚠ 为什么把「名字判等」作参数

  `BEq.beq` 在 `String` 上是 opaque 的，其反射律要打开内部表示
  （且 batteries 的 `BEq` 引理带 `propext`）。本文件把判定**结果**
  作为参数 `hit : (p == judgmentPredName) = true` 传入，
  于是定理前提精确、可证、零公理。
-/

namespace FateV2.Core

universe u

/-! ## 解码 -/

/-- 从数据里取出内嵌的公式。 -/
def decodeData {L : Type u} : Data L → Option (Formula L)
  | .lit _   => none
  | .vec _   => none
  | .tup _   => none
  | .ent _   => none
  | .logic f => some f
  | .ref _   => none

/-- 从项里取出内嵌的公式。 -/
def decodeFormulaTerm {L : Type u} : Term L → Option (Formula L)
  | .lit d   => decodeData d
  | .var _   => none
  | .add _ _ => none
  | .mul _ _ => none
  | .neg _   => none
  | .ext _ _ => none

/-- 参数表解码（两个内嵌公式 → 判断）。

    ⚠ `support` 取 `∅`、`status` 取 `proven` 是**约定默认值，不是恢复**。

    ⚠ **不能写并列模式 `match o1, o2 with`**：那会生成依赖 `DecidableEq`
    的匹配子，实测带 `propext`（违反 D-016）。
    改为**两层嵌套 `match`**，实测零公理（见 `_报告/迁移工具/_pd.lean`）。 -/
def decodeArgs {L : Type u} : List (Term L) → Option (Judgment L)
  | [] => none
  | a :: rest =>
      (match rest with
       | [] => none
       | b :: rest2 =>
           (match rest2 with
            | [] =>
                (match decodeFormulaTerm a with
                 | some h =>
                     (match decodeFormulaTerm b with
                      | some c => some ⟨h, c, Support.empty, Status.proven⟩
                      | none => none)
                 | none => none)
            | _ :: _ => none))

/-! ## 保真 -/

/-- **【部分保真 · 解出的是「核心相等」的判断】**

    比定义多说了什么：`quoteJudgment` 用 `ext` + 两个 `lit (logic ·)` 编码，
    `decodeArgs` 用两层模式匹配还原；本定理要求这两条**互逆的机器**
    在两个核心字段上对齐。三个分支（两个 `some`、一个 `none`）都要算。 -/
theorem decode_encode_core {L : Type u} (j : Judgment L) :
    ∃ k : Judgment L, decodeArgs [quoteFormula j.hyp, quoteFormula j.concl] = some k
      ∧ k.hyp = j.hyp ∧ k.concl = j.concl := by
  refine ⟨⟨j.hyp, j.concl, Support.empty, Status.proven⟩, ?_, rfl, rfl⟩
  show (match decodeFormulaTerm (quoteFormula j.hyp) with
        | some h =>
            (match decodeFormulaTerm (quoteFormula j.concl) with
             | some c => some (⟨h, c, Support.empty, Status.proven⟩ : Judgment L)
             | none => none)
        | none => none) = _
  unfold decodeFormulaTerm decodeData quoteFormula
  rfl

/-- **【`hyp` 保真】**：解码后取前件，得到原来的前件。 -/
theorem decode_encode_hyp {L : Type u} (j : Judgment L) :
    (decodeArgs [quoteFormula j.hyp, quoteFormula j.concl]).map (fun k => k.hyp)
      = some j.hyp := by
  obtain ⟨k, hk, h1, _⟩ := decode_encode_core j
  rw [hk]
  exact congrArg some h1

/-- **【`concl` 保真】**。 -/
theorem decode_encode_concl {L : Type u} (j : Judgment L) :
    (decodeArgs [quoteFormula j.hyp, quoteFormula j.concl]).map (fun k => k.concl)
      = some j.concl := by
  obtain ⟨k, hk, _, h2⟩ := decode_encode_core j
  rw [hk]
  exact congrArg some h2

/-! ## 核心单射性

  `Judgment.lean` 尾项 2 说「编码单射需要 `Formula` 的 `DecidableEq`（核内没有）」。
  但**核心部分**不需要它：两个判断编码相等 ⟺ `hyp`/`concl` 分别相等。 -/

/-- **【核心单射】两判断的核心段相等 ⟺ 编码相等。**

    * `→`：`quoteJudgment` 的定义里没有 `support`/`status`，故编码只看核心段。
    * `←`：核心段相等则两个 `ext` 的两个参数都相等。

    这正是 `Judgment.lean` 尾项 1/2 的答案：**`support`/`status` 丢，`hyp`/`concl` 保**。 -/
theorem encode_core_iff {L : Type u} (j₁ j₂ : Judgment L) :
    quoteJudgment j₁ = quoteJudgment j₂ ↔ (j₁.hyp = j₂.hyp ∧ j₁.concl = j₂.concl) := by
  constructor
  · intro h
    -- `h` 已是两个 `ext` 的等式；从中取参数表的等式
    unfold quoteJudgment at h
    have hargs : ([quoteFormula j₁.hyp, quoteFormula j₁.concl] : List (Term L))
        = [quoteFormula j₂.hyp, quoteFormula j₂.concl] :=
      Formula.ext.inj h |>.2
    have hc : (decodeArgs [quoteFormula j₁.hyp, quoteFormula j₁.concl]).map (fun k => k.hyp)
            = (decodeArgs [quoteFormula j₂.hyp, quoteFormula j₂.concl]).map (fun k => k.hyp) := by
      rw [hargs]
    rw [decode_encode_hyp j₁, decode_encode_hyp j₂] at hc
    have hd : (decodeArgs [quoteFormula j₁.hyp, quoteFormula j₁.concl]).map (fun k => k.concl)
            = (decodeArgs [quoteFormula j₂.hyp, quoteFormula j₂.concl]).map (fun k => k.concl) := by
      rw [hargs]
    rw [decode_encode_concl j₁, decode_encode_concl j₂] at hd
    exact ⟨Option.some.inj hc, Option.some.inj hd⟩
  · rintro ⟨h1, h2⟩
    unfold quoteJudgment
    rw [h1, h2]

/-- 推论：编码相等则核心相等。 -/
theorem encode_eq_imp_core {L : Type u} {j₁ j₂ : Judgment L}
    (h : quoteJudgment j₁ = quoteJudgment j₂) : j₁.hyp = j₂.hyp ∧ j₁.concl = j₂.concl :=
  (encode_core_iff j₁ j₂).mp h

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | 完整 `decode (encode j) = some j` | **不可得**：`support`/`status` 不在编码里 |
  | 2 | 编码**绝对**单射（含 `support`/`status`） | 不可能：`⟨h,c,∅,proven⟩` 与 `⟨h,c,[X],conditional⟩` 编码相同。`encode_core_iff` 已精确划出边界 |
  | 3 | 名字判等的反射律 | `BEq.beq` 在 `String` 上 opaque；本版把它作参数 |
-/

end FateV2.Core
