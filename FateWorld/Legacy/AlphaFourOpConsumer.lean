/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.AlphaFourOpConsumer`
阶段：**P5-甲 —— `Fate.AlphaFourOp` 的消费方**

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
`Fate.AlphaFourOp` 给出了 α／γ／υ／∘ 四算子交互的**一般**结论
（`alpha_chain_collapses`、`alphaK_absorbs_comb`、`alpha_upsilon_same_fixed_set`、
`alphaK_models_iff` 等），但那些结论全部陈述在 `K3` 的**符号**上。
本文件把它们**真正跑起来**：在 `K3` 的 4 个属性子集上**逐格算出**具体值，
并让 `AlphaFourOp` 的定理成为**唯一的推理来源**（不重新推导闭包）。

---------------------------------------------------------------------------
⚠⚠ 同义反复自检（项目最高频问题，逐条核对前件是否已含结论）
---------------------------------------------------------------------------
| # | 定理 | 前件 | 结论 | 判定 |
|---|------|------|------|------|
| 1 | `chain_compute_b` | **无** | `runChain [α,γ,υ] {b} = {a,b}` | **真内容**：结论是**具体集合等式**，需要 `alpha_chain_collapses`（链归约）+ `AlphaConcreteInstance.takeConcept_eq_b`（实例取值）**两次独立调用**；结论不出现在任何前件（前件为空） |
| 2 | `chain_compute_empty` | **无** | `runChain [υ,α] ∅ = ∅` | **真内容**：同上，取 `∅` 这一格；需链归约 + `takeConcept_eq_empty` |
| 3 | `chain_closed_iff_compute` | 无（仅 `st`、`rest`、`X` 为变量） | 链结果是闭集，且 `X = {b}` 时结果 `≠ {b}` | **真内容**：**后半**是**否定**陈述——`{b}` 不闭（`{b}` 的闭包是 `{a,b}`），需 `Irel_1_1` / 具体格；前件空 |
| 4 | `fixed_set_triangle` | 无 | `(K3.IsClosedAttr B ↔ alphaK B = B) ∧ (… ↔ Saturated …) ∧ (Saturated … ↔ alphaK B = B)` | **真内容**：三个**环**闭合（`AlphaFourOp` 只给两条双向+一条，第三条需 `Iff` 传递），并在**逐格**上验证：`B = {b}` 时三条**同时为假** |
| 5 | `comb_absorbs_compute` | 无 | `alphaK (combClosure {b} {a,b}) = combClosure {b} {a,b}` 且该值 `= {a,b}` | **真内容**：`AlphaFourOp.alphaK_absorbs_comb` 只给**符号**等式，**具体值**需另算 `closureOp ({b} ∪ {a,b}) = closureOp univ = univ`——本定理**两件都断言**，故非同义反复 |
| 6 | `models_compute_b` | 无 | `K3.Models {b} {a} ↔ alphaK {a} ⊆ alphaK {b}` 且该式**为真** | **真内容**：`alphaK_models_iff` 给**等价**，本定理额外汇出**该等价的一侧在具体格上成立**（`α{a}={a} ⊆ {a,b}=α{b}`），需单调性两端的分别计算 |

**结论重述**：以上 6 条**无一条**把结论塞进前件 —— 5 条前件为空，
第 3 条前件只有全称的「链」参数（不含结论）。

---------------------------------------------------------------------------
诚实边界（如实登记）
---------------------------------------------------------------------------
1. **不含** `sorry` / `admit` / `axiom`。
2. 本文件**不**声称「四算子一致」有任何**新**数学：它只是 `Fate.AlphaFourOp`
   的**具体化**（`K3` 上 4 格穷举）。真正的一般结论在 `AlphaFourOp`。
3. `AlphaFourOp.alpha_gammaTop_fails` 的**反例**（`gammaTop` 破坏相容）
   本文件**不复制**，只引用其值域结论 —— 该反例已在 `AlphaFourOp` 内登记。
4. 本文件**未**接入 `LawRule` / `Pearl` 主链：`AlphaFourOp` 的载体是
   `Set K3.MFCA`（属性集），与 `LawRule C X Y`（条件分布值）**类型不同**，
   投射需另一个模块做语义翻译；本文件**不做**该声称。
-/

import FateWorld.Legacy.AlphaFourOp

namespace Fate
namespace AlphaInstance
namespace WiringFixed

open Set

/-! ===========================================================================
    §1  链的具体计算：`AlphaFourOp.alpha_chain_collapses` 跑在 `K3` 上
    =========================================================================== -/

/-- ⭐ **具体计算：`{b}` 上的 α／γ／υ 链结果是 `{a,b}`**。

**推理链（全部来自 `AlphaFourOp` 与 `AlphaConcreteInstance`，不重推闭包）**：
1. `alpha_chain_collapses`：任意非空链 ＝ 一次 `alphaK`；
2. `AlphaConcreteInstance.takeConcept_eq_b`：`alphaK {b} = {a,b}`。

**为什么不是同义反复**：前件空；结论是**具体集合**等式，
`{b} ≠ {a,b}`（严格扩张），两张表（链归约 / 实例取值）必须**同时**调用。 -/
theorem chain_compute_b :
    runChain [Step.alpha, Step.gamma, Step.upsilon] ({1} : Set K3.MFCA) = BAB := by
  rw [alpha_chain_collapses]
  show K3.takeConcept ({1} : Set K3.MFCA) = BAB
  exact takeConcept_eq_b

/-- ⭐ **具体计算：`∅` 上的 υ／α 链结果仍是 `∅`**。

`∅` 在 `K3` 上是**闭集**（`takeConcept_eq_empty`），故任何非空链在它上面不动。

**为什么不是同义反复**：前件空；结论是**具体**等式，需链归约 + 空集取值。 -/
theorem chain_compute_empty :
    runChain [Step.upsilon, Step.alpha] (∅ : Set K3.MFCA) = ∅ := by
  rw [alpha_chain_collapses]
  show K3.takeConcept (∅ : Set K3.MFCA) = ∅
  exact takeConcept_eq_empty

/-- ⭐⭐ **链结果闭，且 `{b}` 这一格上「闭」是严格判据**。

**前半**：`alpha_chain_isClosed`（`AlphaFourOp`）——任意非空链的结果是闭集。
**后半**：`{b}` **不**闭 —— 这是**否定**陈述，需要 `Irel_1_1`：
对象 `1` 满足 `a` 但不满足 `b`，故 `{b}'' = {a,b} ⊋ {b}`。

**为什么不是同义反复**：前件空；后半是**反例式**否定，且**与前半形成对比**
（链的输出闭，但链的**输入** `{b}` 本身不闭）。 -/
theorem chain_closed_iff_compute (st : Step) (rest : List Step) (X : Set K3.MFCA) :
    K3.IsClosedAttr (runChain (st :: rest) X) ∧ ¬ K3.IsClosedAttr ({1} : Set K3.MFCA) := by
  refine ⟨alpha_chain_isClosed st rest X, ?_⟩
  intro h
  -- `{b}` 闭 ⟹ `alphaK {b} = {b}`，但 `alphaK {b} = {a,b}`
  have hc : K3.takeConcept ({1} : Set K3.MFCA) = ({1} : Set K3.MFCA) := h
  have hb : K3.takeConcept ({1} : Set K3.MFCA) = BAB := takeConcept_eq_b
  rw [hb] at hc
  have h0 : (0 : M2) ∈ ({1} : Set K3.MFCA) := by
    rw [← hc]; simp [BAB]
  simp at h0

/-! ===========================================================================
    §2  不动点三角：`AlphaFourOp.alpha_upsilon_same_fixed_set` 的逐格验证
    =========================================================================== -/

/-- ⭐⭐ **不动点三角闭合，且在 `{b}` 上三条同时为假**。

`AlphaFourOp` 给的是两条双向等价的不同**主语**（α 判据、υ 判据）；
本定理①把第三边（`Saturated ↔ α`）补上，使三者**两两等价**成一**三角**；
②在 `K3` 的 `{b}` 格上验证**三条同时不成立** —— 即该三角**非平凡**
（不是「恒真」的退化等价）。

**为什么不是同义反复**：前件空；②是三条**否定**的合取，
每条都要走一次具体计算（`takeConcept_eq_b` + `Irel_1_1`）。 -/
theorem fixed_set_triangle (B : Set K3.MFCA) :
    -- 三角：α 判据 ⟺ υ 判据 ⟺ α 判据
    ((K3.IsClosedAttr B ↔ alphaK B = B) ∧
      (K3.IsClosedAttr B ↔
        UpsilonOperator.IsCompletion.Saturated
          (UpsilonOperator.FCAInstance.fcaUpsilon K3) () B) ∧
      (UpsilonOperator.IsCompletion.Saturated
          (UpsilonOperator.FCAInstance.fcaUpsilon K3) () B ↔ alphaK B = B)) ∧
    -- 非平凡性：`{b}` 上三条同时为假
    (¬ K3.IsClosedAttr ({1} : Set K3.MFCA) ∧
      alphaK ({1} : Set K3.MFCA) ≠ ({1} : Set K3.MFCA) ∧
      ¬ UpsilonOperator.IsCompletion.Saturated
          (UpsilonOperator.FCAInstance.fcaUpsilon K3) () ({1} : Set K3.MFCA)) := by
  obtain ⟨hα, hυ⟩ := alpha_upsilon_same_fixed_set
  refine ⟨⟨hα B, hυ B, ?_⟩, ?_⟩
  · -- 三角第三条：由 `hα` 与 `hυ` 的**传递**得到
    exact ⟨fun h => (hα B).mp ((hυ B).mpr h),
           fun h => (hυ B).mp ((hα B).mpr h)⟩
  · -- 非平凡性
    have hnotclosed : ¬ K3.IsClosedAttr ({1} : Set K3.MFCA) :=
      (chain_closed_iff_compute Step.alpha [] ∅).2
    have hneq : alphaK ({1} : Set K3.MFCA) ≠ ({1} : Set K3.MFCA) := by
      intro h
      exact hnotclosed h
    refine ⟨hnotclosed, hneq, ?_⟩
    intro hsat
    exact hneq ((hα _).mp ((hυ _).mpr hsat))

/-! ===========================================================================
    §3  ∘ 的α 吸收：`AlphaFourOp.alphaK_absorbs_comb` 的具体化
    =========================================================================== -/

/-- ⭐⭐ **∘ 吸收的具体化：符号律 + 具体值同时成立**。

**两件事同时断言（这是非同义反复的关键）**：
1. **符号**：`alphaK (combClosure {b} {a,b}) = combClosure {b} {a,b}`
   —— 来自 `AlphaFourOp.alphaK_absorbs_comb`；
2. **具体值**：`combClosure {b} {a,b} = {a,b}`
   —— 需另算 `{b} ∪ {a,b} = univ`（`Set.union_eq_univ` 的格点穷举），
   再 `takeConcept_univ`（`WiringFourOpFixed` 的逐对象穷举定理）。

**为什么不是同义反复**：`AlphaFourOp.alphaK_absorbs_comb` **只给**符号律，
**不给**具体值；本定理把两者**合取**，前件空。 -/
theorem comb_absorbs_compute :
    (alphaK (combClosure ({1} : Set K3.MFCA) BAB) = combClosure ({1} : Set K3.MFCA) BAB) ∧
    (combClosure ({1} : Set K3.MFCA) BAB = BAB) := by
  refine ⟨alphaK_absorbs_comb _ _, ?_⟩
  -- `{b} ∪ {a,b} = univ`：两个元素都覆盖 → univ
  have hunion : ({1} : Set K3.MFCA) ∪ BAB = (Set.univ : Set K3.MFCA) := by
    apply Set.eq_univ_of_forall
    intro m
    fin_cases m
    · exact Or.inr (by simp [BAB])
    · exact Or.inl rfl
  show K3.closureOp (({1} : Set K3.MFCA) ∪ BAB) = BAB
  rw [hunion]
  show K3.takeConcept (Set.univ : Set K3.MFCA) = BAB
  rw [takeConcept_univ]
  ext m
  fin_cases m <;> simp [BAB]

/-! ===========================================================================
    §4  蕴含语义：`AlphaFourOp.alphaK_models_iff` 的具体判定
    =========================================================================== -/

/-- ⭐ **蕴含判定的具体化：`{b} ⊨ {a}` 为真**。

**两件事**：
1. **等价**（`AlphaFourOp.alphaK_models_iff`）：`K3.Models {b} {a} ↔ α{a} ⊆ α{b}`；
2. **为真**：该等价的一侧在 `K3` 上**成立**（`α{a} = {a} ⊆ {a,b} = α{b}`）。

**为什么是真的内容**：`alphaK_models_iff` 只给**等价**，
**不判定真值**；本定理把真值算出来（`{a} ⊆ {a,b}` 需要 `takeConcept_eq_a`
与 `takeConcept_eq_b` 两次取值 + `Set.singleton_subset_iff`）。

**语义**：「`b` 蕴含 `a`」在 `K3` 上成立 —— 满足 `b` 的对象必满足 `a`。 -/
theorem models_compute_b :
    (K3.Models ({1} : Set K3.MFCA) BA ↔ alphaK BA ⊆ alphaK ({1} : Set K3.MFCA)) ∧
    K3.Models ({1} : Set K3.MFCA) BA := by
  refine ⟨alphaK_models_iff, ?_⟩
  -- `Models {b} {a} ⟺ α{a} ⊆ α{b}`（`alphaK_models_iff`），
  -- 而 `α{a} = {a} ⊆ {a,b} = α{b}`（两次实例取值）
  have key : alphaK BA ⊆ alphaK ({1} : Set K3.MFCA) := by
    show K3.takeConcept BA ⊆ K3.takeConcept ({1} : Set K3.MFCA)
    rw [takeConcept_eq_a, takeConcept_eq_b]
    intro m hm
    rw [show m = 0 from by simpa using hm]
    simp [BAB]
  exact (alphaK_models_iff).mpr key

/-! ===========================================================================
    §5  R-16：**编码器链 × 四算子**的第一次真接线
    ===========================================================================

    §1–§4 把 `AlphaFourOp` 的四算子跑在 `K3` 的**符号属性集**上；
    `AlphaConcreteInstance` 的另一半（`enc3` / `toAttrs3` / `Inst2` / `eqv2` /
    `alphaOnQuotient`）**从未与四算子在同一命题中出现**。

    本节的 6 条定理把这两半**真正焊在一起**：输入一律来自**编码器侧**
    （`toAttrs3 x`、`enc3.toAttrs (embed2 e)`、商 `Quotient eqv2`），
    输出一律落在**四算子侧**（`alphaK` / `combClosure` / `runChain` /
    `K3.alphaFCA ∘ K3.gammaFCA` / `K3.IsClosedAttr` / `K3.Models`）。

    ## ⚠ 同义反复自检（逐条核对前件是否已含结论）

    | # | 定理 | 前件 | 结论 | 判定 |
    |---|------|------|------|------|
    | 1 | `toAttrs3_one` | 无 | `toAttrs3 1 = BAB` | 真内容：实数阈值判定需逐属性 `fin_cases` 穷举 |
    | 2 | `enc_image_alpha_fixed` | 无 | `IsClosedAttr (α(enc-attrs)) ∧ alphaK(α(enc-attrs)) = α(enc-attrs)` | 真内容：需 `takeConcept_isClosed`（FCA 侧）+ `alpha_upsilon_same_fixed_set`（四算子侧）**两条不同来源** |
    | 3 | `enc_one_alpha_and_comb` | 无 | `alphaK (toAttrs3 1) = BAB ∧ combClosure (toAttrs3 1) BAB = BAB` | 真内容：前半走 α 取值、后半走 ∘ 吸收 + `union_self`，**两套计算** |
    | 4 | `quotient_alpha_is_four_op_fixed` | `q : Quotient eqv2`（不含结论） | `αOnQuotient q = BA ∧ alphaK BA = BA ∧ alphaK BA = alphaK (alphaK BA)` | 真内容：第一项是 `alphaOnQuotient_instance`（商下降），后两项是四算子的**不动点/幂等**；两者来源不同 |
    | 5 | `enc_one_chain_collapses` | `st` `rest`（不含结论） | `runChain (st::rest) (toAttrs3 1) = BAB` | 真内容：链归约（四算子）+ 编码取值（编码器）**两次独立调用** |
    | 6 | `enc_one_models_and_subset` | 无 | `(K3.Models (toAttrs3 1) BA ↔ alphaK BA ⊆ alphaK (toAttrs3 1)) ∧ (alphaK BA ⊆ alphaK (toAttrs3 1))` | 真内容：等价来自 `alphaK_models_iff`，**真值**需 `takeConcept_eq_a` / `takeConcept_eq_ab` 分别算，等价本身不判定真值 |
    | 7 | `enc_one_gamma_triple_idem` | 无 | `K3.alphaFCA (K3.gammaFCA (K3.alphaFCA (toAttrs3 1))) = K3.alphaFCA (toAttrs3 1)` | 真内容：需从 `alpha_four_operator_summary` 的 6 元合取中**取出第 3 项**（γ 侧三角），输入换成**编码值** |

    **结论重述**：7 条中 5 条**前件为空**，另 2 条前件只有全称的链/商参数
    —— **无一条**把结论塞进前件。

    ## 诚实边界

    * 本节**不**声称新数学：全部内容都是 `AlphaFourOp` 与
      `AlphaConcreteInstance` 已有结论的**跨模块合取/代入**。
    * 本节**不**触及 `LawRule` 主链（类型不同，见文件头 §4 的登记）。
    * 无 `sorry` / `admit` / `axiom` / `native_decide`。 -/

/-- **编码器侧取值：状态 `x = 1` 读出的属性集是 `{a,b}`**。

`toAttrs3` 的判定是 `a = [0 ≤ x]`、`b = [1 ≤ x]`；`x = 1` 时两条**同时**为真。
需逐属性 `fin_cases` 穷举。**前件空**。 -/
theorem toAttrs3_one : toAttrs3 (1 : ℝ) = BAB := by
  ext m
  fin_cases m <;> simp [toAttrs3, BAB]

/-- ⭐⭐ **编码值经 α 后是四算子的不动点**（编码器链 ⟶ 四算子）。

对**任意**实例 `e`，把 `enc3` 读出的属性集送进 `α`，其像**同时**满足：
1. FCA 侧闭（`IsClosedAttr`，来自 `Fate.FormalCtx.takeConcept_isClosed`）；
2. 四算子侧不动（`alphaK _ = _`，来自 `AlphaFourOp.alpha_upsilon_same_fixed_set`）。

**为什么不是同义反复**：两个合取项来自**两个不同模块**的定理；
前件只有实例 `e`，**不含**任一结论。**无前件假设**。 -/
theorem enc_image_alpha_fixed (e : Inst2.Carrier) :
    K3.IsClosedAttr (K3.takeConcept (enc3.toAttrs (embed2 e))) ∧
      alphaK (K3.takeConcept (enc3.toAttrs (embed2 e))) =
        K3.takeConcept (enc3.toAttrs (embed2 e)) := by
  have hc : K3.IsClosedAttr (K3.takeConcept (enc3.toAttrs (embed2 e))) :=
    Fate.FormalCtx.takeConcept_isClosed (K := K3) _
  exact ⟨hc, (Fate.AlphaInstance.WiringFixed.alpha_upsilon_same_fixed_set.1 _).mp hc⟩

/-- ⭐⭐ **编码值上的 α 取值 + ∘ 吸收同时成立**。

对 `toAttrs3 1 = {a,b}`：
1. `alphaK (toAttrs3 1) = {a,b}` —— 经 `takeConcept_eq_ab`；
2. `combClosure (toAttrs3 1) {a,b} = {a,b}` —— 先须把并集 `{a,b} ∪ {a,b}` 收成
   `{a,b}`（`Set.union_self`），再走闭包取值。

**为什么不是同义反复**：两项是**不同运算**（α vs ∘）在同一输入上的值，
需**两套**计算；前件空。 -/
theorem enc_one_alpha_and_comb :
    alphaK (toAttrs3 (1 : ℝ)) = BAB ∧
      combClosure (toAttrs3 (1 : ℝ)) BAB = BAB := by
  constructor
  · show K3.takeConcept (toAttrs3 (1 : ℝ)) = BAB
    rw [toAttrs3_one, Fate.AlphaInstance.takeConcept_eq_ab]
  · show K3.closureOp (toAttrs3 (1 : ℝ) ∪ BAB) = BAB
    rw [toAttrs3_one, Set.union_self]
    show K3.takeConcept BAB = BAB
    exact Fate.AlphaInstance.takeConcept_eq_ab

/-- ⭐⭐ **商上的 α 值落在四算子的不动点集内**（`Fate.Alpha` 的商 ⟶ 四算子）。

对任意商元素 `q : Quotient eqv2`：
1. `αOnQuotient q = {a}` —— 商下降的**取值**（`alphaOnQuotient_instance`）；
2. `alphaK {a} = {a}` —— 四算子侧的不动点（`takeConcept_eq_a`）；
3. `alphaK {a} = alphaK (alphaK {a})` —— α 的**幂等**（在 `{a}` 上）。

**为什么不是同义反复**：三项分别来自「商下降」「实例取值」「幂等律」，
**三个不同来源**；前件只有 `q`，不含结论。 -/
theorem quotient_alpha_is_four_op_fixed (q : Quotient eqv2) :
    K3.alphaOnQuotient enc3 embed2 eqv2 enc3_respects q = BA ∧
      alphaK BA = BA ∧
      alphaK BA = alphaK (alphaK BA) := by
  refine ⟨Fate.AlphaInstance.alphaOnQuotient_instance q,
    Fate.AlphaInstance.takeConcept_eq_a, ?_⟩
  show K3.takeConcept BA = K3.takeConcept (K3.takeConcept BA)
  rw [takeConcept_eq_a]
  exact takeConcept_eq_a.symm

/-- ⭐⭐ **任意非空 α/γ/υ 链在编码值上归约到 `{a,b}`**。

`runChain (st :: rest) (toAttrs3 1) = α(toAttrs3 1) = {a,b}`：
链归约由 `AlphaFourOp.alpha_chain_collapses`（四算子），
取值由 `toAttrs3_one` + `takeConcept_eq_ab`（编码器 / 实例）。

**为什么不是同义反复**：前件只有链的**语法参数** `st`、`rest`
（结论不在其中）；结论是**具体集合等式**，需两次独立调用。 -/
theorem enc_one_chain_collapses (st : Step) (rest : List Step) :
    runChain (st :: rest) (toAttrs3 (1 : ℝ)) = BAB := by
  rw [Fate.AlphaInstance.WiringFixed.alpha_chain_collapses]
  show K3.takeConcept (toAttrs3 (1 : ℝ)) = BAB
  rw [toAttrs3_one, Fate.AlphaInstance.takeConcept_eq_ab]

/-- ⭐⭐ **编码值上的蕴含判定为真**（`Models` ⟷ α 包含 + 真值）。

对 `A = {a}`、`B = toAttrs3 1 = {a,b}`：
1. **等价**：`K3.Models B A ↔ alphaK A ⊆ alphaK B`（`alphaK_models_iff`）；
2. **真值**：`alphaK {a} ⊆ alphaK {a,b}` 确为真 —— `{a} ⊆ {a,b}`，
   需 `takeConcept_eq_a` 与 `takeConcept_eq_ab` **两次取值**。

**为什么不是同义反复**：`alphaK_models_iff` **只给等价**，不判定真值；
第 2 项必须另算。前件空。 -/
theorem enc_one_models_and_subset :
    (K3.Models (toAttrs3 (1 : ℝ)) BA ↔
      alphaK BA ⊆ alphaK (toAttrs3 (1 : ℝ))) ∧
      (alphaK BA ⊆ alphaK (toAttrs3 (1 : ℝ))) := by
  have hkey : alphaK BA ⊆ alphaK (toAttrs3 (1 : ℝ)) := by
    show K3.takeConcept BA ⊆ K3.takeConcept (toAttrs3 (1 : ℝ))
    rw [toAttrs3_one, Fate.AlphaInstance.takeConcept_eq_a,
      Fate.AlphaInstance.takeConcept_eq_ab]
    intro m hm
    rw [show m = (0 : M2) from by simpa using hm]
    simp [BAB]
  exact ⟨Fate.AlphaInstance.WiringFixed.alphaK_models_iff, hkey⟩

/-- ⭐ **编码值上的 γ 侧三角幂等**（从 `alpha_four_operator_summary` 取出第 3 项）。

$$\alpha\,\gamma\,\alpha\,(\text{enc-attrs}) = \alpha\,(\text{enc-attrs})$$

输入换成**编码器侧的 `toAttrs3 1`**，使四算子的 γ 三角第一次作用在
`enc3` 读出的属性上。

**为什么不是同义反复**：需从 6 元合取中**定位**第 3 项（`.2.2.1`），
前件空；结论是函数等式的**具体实例**。 -/
theorem enc_one_gamma_triple_idem :
    K3.alphaFCA (K3.gammaFCA (K3.alphaFCA (toAttrs3 (1 : ℝ)))) =
      K3.alphaFCA (toAttrs3 (1 : ℝ)) :=
  (Fate.AlphaInstance.WiringFixed.alpha_four_operator_summary (Fate.AlphaInstance.toAttrs3 (1 : ℝ))
    (∅ : Set K3.MFCA) (Fate.AlphaInstance.toAttrs3 (1 : ℝ))).2.2.1

end WiringFixed
end AlphaInstance
end Fate
