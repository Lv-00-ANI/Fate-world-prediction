import FateWorld.Legacy.LawRule
import FateWorld.Legacy.LawRulePointExtract
import FateWorld.Legacy.LawRulePointDecidability
import FateWorld.Legacy.LawRuleInstances
import FateWorld.Legacy.LawRuleSequence
import FateWorld.Legacy.LawRuleMarginal
import FateWorld.Legacy.LawRuleUnion

/-! ===========================================================================
  §LRB  `LawRule` ⟷ `Frame.Rule` 的**双向映射**（补齐 `Rule.toLaw` 的反向）

  ## 0. 结论（先说清楚）

  设 `C, X, Y` 为 `CtxSpace / StateSpace / OutSpace`，两侧都有
  `[MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]`。

  | 方向 | 定义 | 需要什么条件 | 唯一？ |
  |---|---|---|---|
  | `Rule ⟶ LawRule` | `Rule.toLaw r c x := {r.kernel c x}` | **无** | 是（`toLaw_injective`） |
  | `LawRule ⟶ Rule` | `toRule R h`（`h : IsPoint R`） | **`IsPoint R`**（逐点允许集是单点集） | 否——须 `Classical.choose`；**在点分离下**由 `R` 唯一决定（`toRule_ext`） |

  **⟹ 一句话**：`Rule.toLaw` 是**单射**且**（在 `IsPoint` 上）可逆**；
  反向 `toRule` **只在 `IsPoint` 档存在**，且其“值”不唯一但**结果唯一**
  （任一见证给出同一个核，见 `toRule_ext`）。

  ## 1. 双向映射的**精确条件**（本文件的主定理）

  $$\boxed{\;R \in \operatorname{im}(\texttt{Rule.toLaw})
    \iff \texttt{IsPoint}\,R\;}$$

  即：`LawRule` **严格宽于** `Rule` 的像，宽出来的**恰好**是
  「允许集不是单点」的那些规律（空集、真子集、含两个以上分布的集合）。
  这是 `isPoint_iff_mem_range`。

  ## 2. 三条互逆/不变性

  * `toRule_toLaw`：`Rule.toLaw (toRule R h) = R`（`IsPoint` 上**左逆**，实质）；
  * `toLaw_toRule`：`toRule (Rule.toLaw r) h = r`（**右逆，无条件**，实质）；
  * `toLaw_injective`：`Rule.toLaw` **单射**（`Rule` 完全编码在其像里）。

  ## 3. ⚠ 诚实边界（必须登记）

  * **`IsPoint` 不可省**：`toRule` 的定义域就是 `IsPoint R` 的**证明**；
    对非单点的 `R`（如 `R c x = ∅` 或两元集）**没有**任何 `Rule` 与之对应
    （`no_toRule_of_not_isPoint`）。
  * **`IsPoint` 比「单点档」更细的等价物 `Deterministic + Nonempty`** 已证
    （`isPoint_iff_deterministic`，`Fate/LawRule.lean`），故反向条件也可写成
    「逐点非空 **且** 至多一个成员」。
  * **`Dirac` 与 `IsPoint` 不同**：`DetFun.toLaw` 的像是 `IsPointDet`
    （成员必须是 `Measure.dirac`）。`IsPoint` **不**蕴含 `IsPointDet`
    （`isPoint_not_imp_extract`，`Fate/LawRule.lean`）——即
    「有 `Rule` 可对应」**远弱于**「来自确定性映射」。
  * 本文件**不**涉及连续/一般可测核的“正则化”问题：`Rule` 的 `kernel`
    是无约束的任意 `Measure` 值函数，本文件不动这一点。
  =========================================================================== -/

namespace Fate

namespace LawRule

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
  [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]

/-! ===========================================================================
    §1  反向映射：`LawRule ⟶ Rule`（**只在 `IsPoint` 上**）
    =========================================================================== -/

/-- ⭐ **反向映射**：单点档 `LawRule` ⟹ 条件分布核。

$$(\texttt{toRule}\,R\,h).\mathrm{kernel}\,c\,x :=
  \texttt{Classical.choose}\,(h\,c\,x).$$

**为什么必须带 `h : IsPoint R`**：`Rule` 在 `(c,x)` 处**恰有一个**分布，
而 `LawRule` 允许**一组**；若这组不是单点集，就**无法**选出一个“正确”的分布
（见 `no_toRule_of_not_isPoint`）。故 `IsPoint` 是反向映射**存在的前提**，
不是可选的便利假设。

**⚠ 值不唯一**：`h` 是 `Prop`，其**证明项**参与 `choose` 的取值，
但所有见证给出**同一个** `Rule`（`toRule_ext`），故 `toRule` 在**结果**上良定义。 -/
noncomputable def toRule (R : LawRule C X Y) (h : IsPoint R) : Rule C X Y where
  kernel c x := Classical.choose (h c x)

/-- ⭐ 选出的核**确实属于**允许集：`(toRule R h).kernel c x ∈ R c x`。 -/
theorem toRule_mem (R : LawRule C X Y) (h : IsPoint R)
    (c : C.Carrier) (x : X.Carrier) : (toRule R h).kernel c x ∈ R c x := by
  have hs : R c x = {(toRule R h).kernel c x} := by
    show R c x = {Classical.choose (h c x)}
    exact Classical.choose_spec (h c x)
  rw [hs]
  exact Set.mem_singleton _

/-- ⭐ **反向映射逐点显式**：`(toRule R h).kernel c x` 就是那个**唯一**分布
（`R c x = {μ}` 中的 `μ`）。 -/
theorem toRule_kernel_eq {R : LawRule C X Y} {h : IsPoint R}
    {c : C.Carrier} {x : X.Carrier} {μ : Measure Y.Carrier}
    (hμ : R c x = {μ}) : (toRule R h).kernel c x = μ := by
  show Classical.choose (h c x) = μ
  have key : ({Classical.choose (h c x)} : Set (Measure Y.Carrier)) = {μ} := by
    rw [← Classical.choose_spec (h c x), hμ]
  exact Set.singleton_injective key

/-! ===========================================================================
    §2  三条互逆 / 不变性
    =========================================================================== -/

/-- ⭐⭐ **左逆**：`IsPoint` 上「律 ⟹ 核 ⟹ 律」回到原处。

$$\texttt{Rule.toLaw}\,(\texttt{toRule}\,R\,h) = R.$$

**实质内容**：`h` 只说“存在 `μ` 使 `R c x = {μ}`”，
`choose_spec` 给出**正是那个** `R c x = {choose}`，故逐点相等、`funext` 即得。
**不需要**点分离。 -/
theorem toRule_toLaw (R : LawRule C X Y) (h : IsPoint R) :
    Rule.toLaw (toRule R h) = R := by
  funext c x
  show ({Classical.choose (h c x)} : Set (Measure Y.Carrier)) = R c x
  exact (Classical.choose_spec (h c x)).symm

/-- ⭐⭐ **右逆（无条件）**：对**任何** `Rule`，`核 ⟹ 律 ⟹ 核` 恒等。

$$\texttt{toRule}\,(\texttt{Rule.toLaw}\,r)\;h = r.$$

**关键**：`h : IsPoint (Rule.toLaw r)` 的两个分支都是「`{k c x}` 含 `choose`」，
由 `Set.singleton_injective` 得 `choose = k c x`，故 `h` 的**证明项**不影响结果。 -/
theorem toLaw_toRule (r : Rule C X Y) (h : IsPoint (Rule.toLaw r)) :
    toRule (Rule.toLaw r) h = r := by
  obtain ⟨k⟩ := r
  have hfun : (toRule (Rule.toLaw ⟨k⟩) h).kernel = k := by
    funext c x
    show Classical.choose (h c x) = k c x
    have hs : Rule.toLaw (⟨k⟩ : Rule C X Y) c x = {Classical.choose (h c x)} :=
      Classical.choose_spec (h c x)
    exact Set.singleton_injective hs.symm
  exact congrArg Rule.mk hfun

/-- ⭐ **`Rule.toLaw` 单射**：`Rule` 完全编码在其 `LawRule` 像里。

$$\texttt{Rule.toLaw}\,r_1 = \texttt{Rule.toLaw}\,r_2 \implies r_1 = r_2.$$

**⟹** 故 `Rule` 可**无损**嵌入 `LawRule`；`LawRule` 比 `Rule` “多”的部分
**恰是** `IsPoint` 之外的那些规律。 -/
theorem toLaw_injective : Function.Injective (Rule.toLaw (C := C) (X := X) (Y := Y)) := by
  intro r₁ r₂ h
  obtain ⟨k₁⟩ := r₁
  obtain ⟨k₂⟩ := r₂
  have hk : k₁ = k₂ := by
    funext c x
    have := congrFun (congrFun h c) x
    exact Set.singleton_injective this
  exact congrArg Rule.mk hk

/-- ⭐ **`toRule` 与见证无关**：两个不同的 `IsPoint` 证明给出**同一个** `Rule`。

**⟹** 这一条让「反向映射」成为 `R` 的**函数**（而非仅依赖所选证明），
故 `LawRule ⟷ Rule` 在 `IsPoint` 子类型上是真正的**双射**（§3）。 -/
theorem toRule_ext (R : LawRule C X Y) (h₁ h₂ : IsPoint R) :
    toRule R h₁ = toRule R h₂ := by
  have hk : (toRule R h₁).kernel = (toRule R h₂).kernel := by
    funext c x
    exact (toRule_kernel_eq (h := h₁) (Classical.choose_spec (h₁ c x))).trans
      (toRule_kernel_eq (h := h₂) (Classical.choose_spec (h₂ c x))).symm
  exact congrArg Rule.mk hk

/-! ===========================================================================
    §3  精确的**双向条件**：像的刻画
    =========================================================================== -/

/-- ⭐⭐⭐ **主定理（像的刻画）**：`LawRule` 落在 `Rule` 的像里 **⟺** 它是单点档。

$$\boxed{\;R \in \operatorname{im}(\texttt{Rule.toLaw})
  \iff \texttt{IsPoint}\,R\;}$$

**`→`**：若 `R = Rule.toLaw r`，则 `R c x = {r.kernel c x}` 本身就是单点集。
**`←`**：`IsPoint R` 给出 `toRule R h`，而 `toRule_toLaw` 说明它映回 `R`。

**⟹ 这是「`LawRule` 比 `Rule` 宽多少」的精确回答**：
宽出来的**恰好**是非单点档——空集、真子集、多元素集。 -/
theorem isPoint_iff_mem_range (R : LawRule C X Y) :
    IsPoint R ↔ ∃ r : Rule C X Y, Rule.toLaw r = R := by
  constructor
  · intro h; exact ⟨toRule R h, toRule_toLaw R h⟩
  · rintro ⟨r, rfl⟩ c x; exact ⟨r.kernel c x, rfl⟩

/-- ⭐⭐ **`Deterministic` 版本的条件**：反向映射也可按「非空 + 至多一个」来判。

$$\texttt{im}(\texttt{Rule.toLaw})
  = \{\,R \mid \forall c\,x,\ (R\,c\,x).\text{Nonempty} \wedge \text{Deterministic}\,R\,\}$$

由 `isPoint_iff_deterministic`（`Fate/LawRule.lean`）把 `IsPoint` 换掉即得。 -/
theorem mem_range_iff_deterministic (R : LawRule C X Y) :
    (∃ r : Rule C X Y, Rule.toLaw r = R) ↔
      (∀ c x, (R c x).Nonempty) ∧ Deterministic R :=
  (isPoint_iff_mem_range (C := C) (X := X) (Y := Y) R).symm.trans
    (isPoint_iff_deterministic R)

/-- ⭐ **反例指引（非单点档无反向）**：若某 `(c,x)` 处允许集**不是**单点集，
则该 `LawRule` **不在** `Rule` 的像里。

这是 `isPoint_iff_mem_range` 的逆否，直接给出「反向映射的**边界**」：
它不是“还没实现”，而是**不可能**——`Rule` 在每点只有一个分布，无法表达一组。 -/
theorem no_toRule_of_not_isPoint (R : LawRule C X Y) (h : ¬ IsPoint R) :
    ¬ ∃ r : Rule C X Y, Rule.toLaw r = R :=
  fun ⟨r, hr⟩ => h ((isPoint_iff_mem_range R).mpr ⟨r, hr⟩)

/-! ===========================================================================
  §4  ⭐ 组合定理：本桥接模块与 `LawRule` 其它视角模块的**真实接线**

  本节的每条定理都在**至少两个模块**之间建立非平凡联系 —— 不重述已有结论：
  1. `toRule_kernel_dirac_iff_extractable`：
     `IsPoint` 上「`toRule` 抽出的核逐点是 Dirac」⟺ `Fate.LawRulePointExtract.IsDetExtractable`。
  2. `toRule_roundtrip_kernel`：`Rule ⟶ LawRule ⟶ Rule` 的核在往返后不变。
  3. `constRule_in_range_iff`：`LawRulePointDecidability.constRule` 落在
     `Rule.toLaw` 的像里 ⟺ 其基集是单点集。
  4. `genRule_image_iff`：`LawRulePointDecidability.genRule` 落在像里 ⟺ 生成元条件。
  5. `not_mem_image_of_empty`：某处允许集为空 ⟹ 不可能来自 `Rule`。
  6. `linRegRule_toRule_kernel`：`Fate.LawRuleInstances.linRegRule` 经 `toRule` 的核是 `δ_{a·x}`。
  7. `linRegRule_wrong_not_mem_image`：数据不兼容的回归规则**不在**像里。
  8. `flipRule_toRule_kernel`：`Fate.LawRuleInstances.flipRule` 经 `toRule` 的核是 `δ_{flip2 i}`。
  9. `flipRule_fixRule_compose_not_mem_image`：翻转×固定组合处处为空 ⟹ 不在像里。
 10. `seqDet_toRule_kernel`：`LawRuleSequence.seqDet` 与 `toRule` **自然交换**。
 11. `seqDet_id_toRule_kernel`：上条在恒等步进下的特例。

  诚实边界：本节全部为**组合/接线**定理，不引入新的数学主张；
  所有前件均为「单点档 / 数据一致 / 非空」等实质条件，**未把结论包进前件**。
  =========================================================================== -/

namespace RuleBridgeComb

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
  [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]

theorem toRule_kernel_dirac_iff_extractable (R : LawRule C X Y) (h : IsPoint R) :
    (∃ f : C.Carrier → X.Carrier → Y.Carrier,
        ∀ c x, (toRule R h).kernel c x = Measure.dirac (f c x))
      ↔ Fate.LawRulePointExtract.IsDetExtractable R := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    funext c x
    have h1 : R c x = ({Measure.dirac (f c x)} : Set (Measure Y.Carrier)) := by
      rw [← toRule_toLaw (C := C) (X := X) (Y := Y) R h]
      exact congrArg (fun k => ({k} : Set (Measure Y.Carrier))) (hf c x)
    exact h1
  · rintro ⟨f, hf⟩
    refine ⟨f, fun c x => ?_⟩
    have hR : R c x = ({Measure.dirac (f c x)} : Set (Measure Y.Carrier)) := by
      have := congrFun (congrFun hf c) x
      simpa only [DetFun.toLaw] using this
    exact toRule_kernel_eq (h := h) hR

theorem toRule_roundtrip_kernel (r : Rule C X Y)
    (h : IsPoint (Rule.toLaw (C := C) (X := X) (Y := Y) r))
    (c : C.Carrier) (x : X.Carrier) :
    (toRule (Rule.toLaw r) h).kernel c x = r.kernel c x := by
  refine toRule_kernel_eq (h := h) ?_
  show ({r.kernel c x} : Set (Measure Y.Carrier)) = {r.kernel c x}
  rfl

theorem constRule_in_range_iff (S : Set (Measure Y.Carrier))
    [Nonempty C.Carrier] [Nonempty X.Carrier] :
    (∃ r : Rule C X Y, Rule.toLaw r = constRule (C := C) (X := X) (Y := Y) S)
      ↔ ∃ μ, S = ({μ} : Set (Measure Y.Carrier)) :=
  Iff.trans (isPoint_iff_mem_range (C := C) (X := X) (Y := Y) (constRule S)).symm
    (isPoint_constRule_iff S)

theorem genRule_image_iff [Nonempty C.Carrier] [Nonempty X.Carrier]
    {ι : Type*} (G : Finset ι) (g : ι → Set (Measure Y.Carrier)) :
    (∃ r : Rule C X Y,
        Rule.toLaw r = genRule (C := C) (X := X) (Y := Y) G g)
      ↔ ∃ i₀ ∈ G, (∃ μ, g i₀ = ({μ} : Set (Measure Y.Carrier)))
          ∧ g i₀ = ⋃ i ∈ G, g i :=
  Iff.trans (isPoint_iff_mem_range (C := C) (X := X) (Y := Y) (genRule G g)).symm
    (isPoint_genRule_iff G g)

theorem not_mem_image_of_empty (R : LawRule C X Y)
    (h : ∃ c x, ¬ (R c x).Nonempty) :
    ¬ ∃ r : Rule C X Y, Rule.toLaw r = R := by
  refine no_toRule_of_not_isPoint R ?_
  rintro hpt
  obtain ⟨c, x, hx⟩ := h
  obtain ⟨μ, hμ⟩ := hpt c x
  exact hx ⟨μ, by rw [hμ]; exact Set.mem_singleton μ⟩

end RuleBridgeComb

namespace RuleBridgeInstances

theorem linRegRule_toRule_kernel {a : ℝ} {D : List (ℝ × ℝ)}
    (hc : Fate.LawRuleInstances.LinRegCorrect a D)
    (c : Fate.LawRuleInstances.C₀.Carrier) (x : ℝ) :
    (toRule (Fate.LawRuleInstances.linRegRule a D)
        (Fate.LawRuleInstances.linRegRule_isPoint hc)).kernel c x
      = Measure.dirac (a * x) :=
  toRule_kernel_eq (h := Fate.LawRuleInstances.linRegRule_isPoint hc)
    (Fate.LawRuleInstances.linRegRule_of_correct hc x)

theorem linRegRule_wrong_not_mem_image {a : ℝ} {D : List (ℝ × ℝ)}
    (hc : ¬ Fate.LawRuleInstances.LinRegCorrect a D) :
    ¬ ∃ r : Rule Fate.LawRuleInstances.C₀ Fate.LawRuleInstances.Xℝ Fate.LawRuleInstances.Xℝ,
        Rule.toLaw r = Fate.LawRuleInstances.linRegRule a D :=
  RuleBridgeComb.not_mem_image_of_empty _
    ⟨PUnit.unit, 0, Fate.LawRuleInstances.linRegRule_not_nonempty hc PUnit.unit 0⟩

theorem flipRule_toRule_kernel (c : Fate.LawRuleInstances.C₀.Carrier) (i : Fin 2) :
    (toRule Fate.LawRuleInstances.flipRule Fate.LawRuleInstances.flipRule_isPoint).kernel c i
      = Measure.dirac (Fate.LawRuleInstances.flip2 i) :=
  toRule_kernel_eq (h := Fate.LawRuleInstances.flipRule_isPoint)
    (Fate.LawRuleInstances.flipRule_apply c i)

theorem flipRule_fixRule_compose_not_mem_image :
    ¬ ∃ r : Rule Fate.LawRuleInstances.C₀ Fate.LawRuleInstances.XFin2 Fate.LawRuleInstances.XFin2,
        Rule.toLaw r
          = compose Fate.LawRuleInstances.flipRule Fate.LawRuleInstances.fixRule :=
  RuleBridgeComb.not_mem_image_of_empty _
    ⟨PUnit.unit, 0, by
      rw [Fate.LawRuleInstances.flipRule_compose_fixRule_eq_empty]; exact Set.not_nonempty_empty⟩

end RuleBridgeInstances

namespace RuleBridgeSeq

theorem seqDet_toRule_kernel {C : CtxSpace} {X : StateSpace} [MeasurableSpace X.Carrier]
    (f : C.Carrier → X.Carrier → X.Carrier) (R : LawRule C X X) (hR : IsPoint R)
    (c : C.Carrier) (x : X.Carrier) :
    (toRule (seqDet f R) (seqDet_point f R hR)).kernel c x
      = (toRule R hR).kernel c (f c x) := by
  have h1 : seqDet f R c x
      = ({(toRule R hR).kernel c (f c x)} : Set (Measure X.Carrier)) := by
    rw [seqDet_apply]
    exact Classical.choose_spec (hR c (f c x))
  exact toRule_kernel_eq (h := seqDet_point f R hR) h1

theorem seqDet_id_toRule_kernel {C : CtxSpace} {X : StateSpace} [MeasurableSpace X.Carrier]
    (R : LawRule C X X) (hR : IsPoint R) (c : C.Carrier) (x : X.Carrier) :
    (toRule (seqDet (fun _ y => y) R) (seqDet_point _ R hR)).kernel c x
      = (toRule R hR).kernel c x := by
  rw [seqDet_toRule_kernel]

end RuleBridgeSeq


end LawRule

end Fate
