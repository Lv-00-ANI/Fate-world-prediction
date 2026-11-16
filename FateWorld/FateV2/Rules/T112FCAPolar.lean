import FateWorld.FateV2.Rules.T112SecondQuotient
/-!
  # Rules · T112FCAPolar

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T112FCAPolar.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T112SecondQuotient
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ⚠ **第 247 轮标注（J1 批量审核）：**本模块是纯格论，非概率****

**J1 的实测**：6 条定理中**概率相关性 = 0**。

## ✅ 有内容的部分
- `id_not_doublePolar_counterexample`：`by_contra`，`Unit` 上的真反例
- `upperPolar_univ_ne_univ`

## ⚠ 规模问题
**只有 6 条定理**，规模跟不上（原计划 30+ 条）。

## ⚠ **类型标注**（N8）
- **[理论]**：2 条
- **[支撑]**：3 条
- **[展开]**：1 条（`polarUp_polarDown_eq_of_isIntent` = `Order.IsIntent.eq hA` 转写）
-/


/-! ===========================================================================
  `Fate/_r244_H8` —— 第 244 轮：处理第 243 轮登记未完成的 2 条 FCA 特有定理

  ## 结果总览

  | # | 定理 | 结果 |
  |---|---|---|
  | 2 | `polarUp_eq_iff_isIntent` | ✅ **已证（零 sorry）**，见 §1 |
  | 1 | `id_not_doublePolar`     | ⛔ **该命题为假**，本文件给出**机器验证的反例**，见 §2 |

  ⚠ **第 1 条不是"没证出来"，而是"证不出来，因为它不成立"。**
  反例见 `id_not_doublePolar_counterexample`（§2.2），`lake build` 通过、零 sorry。
================================================================================ -/

namespace FateV2.Rules
open Set

namespace FormalCtx

variable (K : FormalCtx)

/-!
## §1  第 2 条：`polarUp_eq_iff_isIntent`

### §1.0  任务书给的字面形式是假的（附反例）

任务书原文：

> 闭内涵 `A` 是某对象集之极 ⟺ `S ⊆ A'` 且 `A ⊆ S'`。

**反例（`S := ∅`）**：右端 `∅ ⊆ A'` ✓（空真）、`A ⊆ ∅' = univ` ✓，即**右端恒真**；
左端却要求 `A = univ`，一般**不成立**。⟹ **右端太弱，漏了「`S` 不能太小」。**

**另一处方向也不对**：若 `A = S'`，则 `A' = (S')' = S''`，由**扩张性** `S ⊆ S'' = A'` ——
`S` 只能从**下方**卡住 `A'`；`A' ⊆ S` 一般**不成立**（`S` 不是 extent 时就失败）。

### §1.1  正确的刻画

「`A` 是某对象集之极」与「`A` 是闭内涵」**是同一件事**——
这是 Galois 不动点刻画在 FCA 双侧结构上的体现，也是本条定理的实质内核。
-/

/-- **基本对偶（本轮需要的极性）**：`S ⊆ A'` ⟹ `A ⊆ S'`。

⚠ 工程已有的 `subset_polarUp_iff_subset_polarDown` 是 `B ⊆ A' ↔ A ⊆ B'`
（`A` 在**对象**侧、`B` 在**属性**侧），**极性相反**，不能直接用。
这里要的是 Mathlib `subset_upperPolar_iff_subset_lowerPolar`
在 `s := S`、`t := A` 处的读法：**`A ⊆ S'` ⟺ `S ⊆ A'`**。
**第 243 轮就是绊在这里：极性选错一侧，`rw` 怎么转都转不动。** -/
theorem subset_polarUp_of_subset_polarDown {A : Set K.MFCA} {S : Set K.GFCA}
    (hS : S ⊆ K.polarDown A) : A ⊆ K.polarUp S :=
  (subset_upperPolar_iff_subset_lowerPolar (r := K.Irel) (s := S) (t := A)).mpr hS

/-- ⭐⭐⭐ **(FCA 特有) 第 2 条 · 实质形式**（第 243 轮未完成，**本轮已证，零 sorry**）

> `A` 是某对象集之极 **⟺** `A` 是闭内涵（`A'' = A`）。

* `⟹`：**任何**极都是闭的 —— 幂等性 `polarUp_polarDown_polarUp`，**不需要** `hA`；
* `⟸`：**构造** `S := A'`，则 `S' = (A')' = A'' = A`（此处用 `hA`）。

⟹ 见证 `S := A'` 是**唯一**自然取法，这与 §1.0 的反例一致：`S` 必须"取满"，
否则 `S'` 会过大。 -/
theorem polarUp_eq_iff_isIntent {A : Set K.MFCA} :
    (∃ S : Set K.GFCA, A = K.polarUp S) ↔ Order.IsIntent K.Irel A := by
  constructor
  · rintro ⟨S, rfl⟩
    exact Order.isIntent_iff.mpr (K.polarUp_polarDown_polarUp S)
  · intro hA
    exact ⟨K.polarDown A, (Order.IsIntent.eq hA).symm⟩

/-- ⭐ **第 2 条 · 显式见证**：闭内涵 `A` 就是 `A'` 的极。

「双侧」结构的直接体现：对象侧的 `A'` 与属性侧的 `A` **互为对方的极**。 -/
theorem polarUp_polarDown_eq_of_isIntent {A : Set K.MFCA}
    (hA : Order.IsIntent K.Irel A) :
    K.polarUp (K.polarDown A) = A :=
  Order.IsIntent.eq hA

/-- ⭐ **第 2 条 · 闭性自动成立**：任何 `S'` 都是闭内涵。 -/
theorem isIntent_polarUp (S : Set K.GFCA) :
    Order.IsIntent K.Irel (K.polarUp S) :=
  Order.isIntent_iff.mpr (K.polarUp_polarDown_polarUp S)

end FormalCtx

/-!
## §2  ⛔ 第 1 条：`id_not_doublePolar` —— **该命题为假**

### §2.1  命题复述

```lean
theorem id_not_doublePolar :
    ¬ ∃ r : Unit → Unit → Prop,
      (fun A : Set Unit => A) = (fun A => upperPolar r (lowerPolar r A))
```

### §2.2  ⛔ 反例（**机器验证，零 sorry**）

取 **`r := fun _ _ => False`**（**空关系**）。逐案计算（`Set Unit` 只有 `∅` 与 `univ` 两个元素）：

| `A` | `A' = lowerPolar r A = {a \| ∀ m ∈ A, False}` | `A'' = upperPolar r A' = {b \| ∀ a ∈ A', False}` |
|---|---|---|
| `∅`   | `univ`（空真，无 `m ∈ ∅`） | `∅`（`a := ()` 可取，故 `False`） |
| `univ`| `∅`（`m := ()` 可取，故 `False`） | `univ`（空真，无 `a ∈ ∅`） |

故复合 `upperPolar r ∘ lowerPolar r` **恰好是恒等**，即 `id = polarUp r ∘ polarDown r` 成立。
下面的 `id_not_doublePolar_counterexample` 是它的机器证明。

### §2.3  为什么任务书给的那条思路走不通

任务书说「`∅ = polarUp r (polarDown r ∅) = polarUp r univ = univ`」。
**中间那步 `polarUp r univ = univ` 是错的**：

* `polarUp r univ = upperPolar r univ = { b | ∀ a, r a b }`，
  这是「与**所有**对象都相关」的属性集，**不是** `univ`；
* 取 `r ≡ False` 即得 `upperPolar r univ = ∅`（反例正是如此）。

本轮实测确认：`upperPolar (fun _ _ => False) univ ≠ univ`（见 `upperPolar_univ_ne_univ`，
零 sorry），即 `upperPolar r univ = univ` **对任意 `r` 不成立**。
**故第 243 轮及任务书的这条证明思路从数学上就是断的。**

### §2.4  结论与建议

`id_not_doublePolar` **不能保留为定理**。若仍需要一条「双重极不可能是恒等」的结果，
唯一成立的相邻命题是**限制到非空对象集**或**给 `r` 加条件**（例如 `r` 有左/右全域性）。
本文件**不**擅自改写定理陈述，只如实报告：**该命题被反例击破**。
-/

/-- ⛔ **反例：`id = polarUp r ∘ polarDown r` 在 `Set Unit` 上** 是可满足的。

⚠ 这条定理的存在即意味着第 243 轮登记的 `id_not_doublePolar`（其否定）**为假**。
它同时是本轮「第 1 条无法证出」的**根因**——不是技巧问题，是命题不成立。 -/
theorem id_not_doublePolar_counterexample :
    ∃ r : Unit → Unit → Prop,
      (fun A : Set Unit => A) = (fun A => upperPolar r (lowerPolar r A)) := by
  refine ⟨fun _ _ => False, ?_⟩
  funext A
  ext b
  constructor
  · -- `b ∈ A` ⟹ `b ∈ A''`：`A'' = {b | ∀ a ∈ A', False}`，需对任意 `a ∈ A'` 导出 `False`
    intro hb a ha
    exact ha hb
  · -- `b ∈ A''` ⟹ `b ∈ A`：反证，若 `b ∉ A` 则把 `b` 送进 `A'` 与假设矛盾
    intro h
    by_contra hb
    exact h (a := b) (by
      intro m hm
      have hmb : m = b := Subsingleton.elim m b
      rw [hmb] at hm
      exact hb hm)

/-- ⛔ **§2.3 的技术要点（机器验证）**：`upperPolar r univ` **不是** `univ`。

取 `r ≡ False` 即得空集——这正是任务书证明思路断掉的地方。 -/
theorem upperPolar_univ_ne_univ :
    upperPolar (fun (_ : Unit) (_ : Unit) => False) (Set.univ : Set Unit) ≠
      (Set.univ : Set Unit) := by
  intro h
  have hmem : () ∈ upperPolar (fun (_ : Unit) (_ : Unit) => False) (Set.univ : Set Unit) := by
    rw [h]
    exact trivial
  exact hmem (a := ()) trivial

end FateV2.Rules