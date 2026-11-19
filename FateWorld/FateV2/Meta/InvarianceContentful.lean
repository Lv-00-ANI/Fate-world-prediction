/-
命运理论 · Lean 4 形式化实现
================================

模块：InvarianceContentful
性质：**INV-2 证明尝试**（回应作者第 684 轮裁决「经验假设允许，但是依旧需要尝试证明」）

---------------------------------------------------------------------------
本文件为什么存在
---------------------------------------------------------------------------
`_audit/INV-2-invariance证明尝试方案.md` 指出：`ExtendedDataLayer.invariance`
是 **`Prop` 类型的字段**，不是 `theorem`。故「证明 `invariance`」这一说法
在给定具体实例之前是**类型错误**；正确的执行是
**在具体实例上给 `invariance` 填有内容的命题并证明它**。

`Fate/Adjudication.lean` 已证的两条（`invariance_free`、
`invariance_True_no_content`）穷尽了「关于 `invariance` 这个 `Prop` 字段本身」
能证明的内容。本文件按方案的**可证性顺序**执行 **方案 C** 与 **方案 B**。

---------------------------------------------------------------------------
本文件证明的内容（逐条）
---------------------------------------------------------------------------
| 定理 | 方案 | 内容 |
|---|---|---|
| `invariance_not_automatic` | **C** | 存在 `Fin 2` 上的函数跨两环境**不同** ⟹ 不变性**不自动成立** |
| `invariance_fails_fin2`     | **C** | 上一条的显式反例（具体函数 `if i = 0 then 0 else 1`） |
| `invariance_vacuous_of_subsingleton` | **B** | 环境集为 `Subsingleton` 时不变性**自动成立**（空真） |
| `invariance_vacuous_of_unique`       | **B** | 同上，单环境 `Unique` 版本 |
| `invariance_empty_of_two_envs`       | **B/C** | ⚠ 在**非退化**（`Nontrivial`）环境集上，不变性是**真内容**：
不变 ⟺ 常函数；证实 `environmentsAtLeastTwo` 字段的必要性 |

---------------------------------------------------------------------------
诚实边界（必读）
---------------------------------------------------------------------------
1. **本文件不声称「跨环境不变性」这一经验假设已被形式化。**
   它**没有**，也不应在本质数据层上被形式化（须外部数据支撑）。
2. 本文件证明的是**具体实例上的不变性**——即「不变性」这一*性质*的
   数学性质（非自动、单环境空真、非退化时等价于常函数），
   **不是**「某经验数据满足不变性」。
3. 本文件**无** `sorry` / `admit` / `axiom`；全部定理均已证。
4. 本文件**不修改**任何既有模块；只 `import Fate.Adjudication` 并新增声明。
5. 方案 A（有限环境不变性 ⟺ 常函数）与方案 D（给 `ExtendedDataLayer`
   填有内容的 `invariance` 实例）在本文件中**已部分就绪**：
   `invariance_iff_const`（§3）即方案 A；方案 D 见 `contentfulDataLayer`（§4）。

标记图例沿用主链：**【已证】**= 零 sorry 且经 `lake env lean` 验证。
-/

import FateWorld.FateV2.Meta.Adjudication
namespace FateV2.Meta
namespace InvarianceContentful

/-!
  # Meta · InvarianceContentful

  ## 迁移登记
  - 来源：`FateWorld/Legacy/InvarianceContentful.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Adjudication
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 方案 C：不变性**不是**自动的

「跨环境不变性」若对所有函数自动成立，则 `ExtendedDataLayer.invariance`
作为假设就是**多余**的（任何数据层都满足）。本节的定理否定这一点：
在 `Fin 2`（恰好两个环境）上存在**跨环境不同**的函数。

⚠ **非同义反复核查**：本定理**无前件**，结论是**否定性全称断言**
`¬ ∀ f, ∀ e e', f e = f e'`。它不可能由空前提「直接」给出，
必须显式构造反例函数并算出矛盾。 -/

/-- **【方案 C 主定理 · 已证】不变性不是自动的**。

**内容**：**不存在**「所有 `Fin 2 → ℝ` 的函数都跨环境不变」这件事；
即「`Fin 2` 上跨环境不变」是一个**有鉴别力**的性质。 -/
theorem invariance_not_automatic :
    ¬ ∀ (f : Fin 2 → ℝ), ∀ e e' : Fin 2, f e = f e' := by
  intro h
  have hval : (0 : ℝ) = 1 := h (fun i => if i = 0 then (0 : ℝ) else 1) 0 1
  norm_num at hval

/-- **【方案 C 显式反例 · 已证】**具体函数在两环境上取值不同。

**内容**：`g := fun i => if i = 0 then 0 else 1` 在环境 `0` 与 `1` 上的值
分别为 `0` 与 `1`。这是 `invariance_not_automatic` 的具名反例，
便于下游直接引用。 -/
theorem invariance_fails_fin2 :
    ∃ (f : Fin 2 → ℝ), f 0 ≠ f 1 :=
  ⟨fun i => if i = 0 then (0 : ℝ) else 1, by norm_num⟩

/-! ## §2 方案 B：单环境时不变性**空真**

呼应在 `Adjudication.lean` 中 `environmentsAtLeastTwo : Bool` 字段的**必要性**：
若环境集只有一个元素，「跨环境不变性」无条件成立，因而**无鉴别力**
（[A] §2：$|\mathcal E|=1$ 时对任意 $S^*$ 都有解）。
本节把这件事机械化：**任何**函数在 `Subsingleton` 环境集上都不变。

⚠ **非同义反复核查**：结论 `∀ e e', f e = f e'` **不是**前件的一部分；
前件只给 `[Subsingleton E]`（一个类型类实例：「环境中任意两元素相等」），
结论是关于**任意函数** `f` 的等式。证明必须**使用** `Subsingleton.elim`
把 `e, e'` 化归，再 `rfl`。 -/

/-- **【方案 B 主定理 · 已证】单环境时不变性自动成立（空真）**。

**内容**：若环境类型 `E` 是 `Subsingleton`（至多一个元素），则**任意**
`f : E → ℝ` 跨环境不变。

**意义**：这说明「不变性成立」在单环境下**不携带信息**，
故必须有 `environmentsAtLeastTwo` 这类**非退化条件**，
不变性才成为可证伪的假设。 -/
theorem invariance_vacuous_of_subsingleton
    {E : Type} [Subsingleton E] (f : E → ℝ) : ∀ e e' : E, f e = f e' := by
  intro e e'
  rw [Subsingleton.elim e e']

/-- **【方案 B · 已证】`Unique` 版（唯一环境）**。

**内容**：环境集**恰好一个元素**时，不变性同样空真。
本定理与 `invariance_vacuous_of_subsingleton` 并列，便于对照
`Adjudication.degenerateDataLayer`（`environmentsAtLeastTwo := false`）的语义。 -/
theorem invariance_vacuous_of_unique
    {E : Type} [Unique E] (f : E → ℝ) : ∀ e e' : E, f e = f e' :=
  invariance_vacuous_of_subsingleton f

/-! ## §3 方案 A（就绪部分）：非退化环境下不变性 ⟺ 常函数

方案 B 说「单环境 ⟹ 不变（空真）」。**逆向的实质内容是**：
在**非退化**环境集上，「不变 ⟺ `f` 是常函数」。
即不变性这一假设**恰好等价于**「观测函数不随环境变化」，
它**有内容、可证伪**——这正是 `environmentsAtLeastTwo` 想要的。

`∀ e e', f e = f e'` 与 `∃ c, ∀ e, f e = c` 的等价性对**任意非空**
类型都成立，无需 `Fintype`；故本节给出一般版本，
有限环境（`Fintype`）只是其特例。

⚠ **非同义反复核查**：结论是一个 **`↔`**（两方向都须证），
前件只有 `[Nonempty E]`。若结论被塞进前件，则 `↔` 的某一方向
将不成立（`∃ c, ∀ e, f e = c` 不含 `Nonempty` 信息），故不可能同义反复。 -/

/-- **【方案 A · 已证】跨环境不变 ⟺ 存在公共常值**。

**内容**：在**非空**环境集 `E` 上，`f` 跨所有环境取同值
**当且仅当**存在常数 `c` 使 `f` 处处等于 `c`。

**为何非退化使不变性有内容**：右边是一个关于 `f` 的**实质约束**
（`f` 的像为单点集）；由 §1，该约束**不**对所有 `f` 成立。 -/
theorem invariance_iff_const {E : Type} [Nonempty E] (f : E → ℝ) :
    (∀ e e' : E, f e = f e') ↔ ∃ c : ℝ, ∀ e : E, f e = c := by
  constructor
  · intro h
    exact ⟨f (Classical.arbitrary E), fun e => h e _⟩
  · rintro ⟨c, hc⟩ e e'
    rw [hc e, hc e']

/-- **【方案 A 推论 · 已证】非退化时存在不变性**（即 `∃ c` 形式的存在性）。

**内容**：常值函数总是跨环境不变的。故「不变性」这一性质**非空**，
§1 的「非自动」与本节合起来表明：**不变性既非空真也非自动**，
在非退化环境下是一个真正的二分（真/假都可能）。 -/
theorem invariance_nonempty :
    ∃ (f : Fin 2 → ℝ), ∀ e e' : Fin 2, f e = f e' :=
  ⟨fun _ => (0 : ℝ), fun _ _ => rfl⟩

/-- **【方案 A/B 交汇 · 已证】非退化 ⟹ 不变性可失败**。

**内容**：在 `Fin 2`（非退化，恰好两环境）上，**存在**函数不满足跨环境不变。

**意义**：与 `invariance_vacuous_of_subsingleton` 对照可知：
「不变性是空真」与「不变性可失败」以**环境集是否退化**分界，
这就是 `environmentsAtLeastTwo` 字段不可省的**形式化理由**。 -/
theorem invariance_fails_of_nontrivial_fin2 :
    ∃ (f : Fin 2 → ℝ), ¬ ∀ e e' : Fin 2, f e = f e' := by
  obtain ⟨f, hf⟩ := invariance_fails_fin2
  exact ⟨f, fun hall => hf (hall 0 1)⟩

/-! ## §4 方案 D（新增实例，不改原 `def`）：`invariance` 填**有内容**的命题

`Adjudication.extendedDataLayer` 的 `invariance` 填 `True`（无内容）。
按 `SAFE-1` S1，`extendedDataLayer` 是 `def` 而非定理，**不得修改**；
故本文件**新增**一个有内容的实例作为对照：其 `invariance` 填
「`Fin 2` 上的参考观测函数跨环境不变」这一**实质性** `Prop`。

⚠ 注意 `ExtendedDataLayer` **没有类型参数**（`#print` 实测：0 parameters），
故 `invariance` 只能是**闭命题**，不能直接携带 `E` / `f` 作为结构字段。
本节因此用**具名参考函数** `refObs` 把内容「读入」闭命题。 -/

/-- **参考观测函数**：`Fin 2` 上的非平凡函数（`0 ↦ 0`，`1 ↦ 1`）。 -/
def refObs : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

/-- **参考观测函数本身不变性失败**（`refObs 0 ≠ refObs 1`）。 -/
theorem refObs_not_invariant : refObs 0 ≠ refObs 1 := by
  norm_num [refObs]

/-- **常数观测函数**：处处取 `0`。 -/
def constObs : Fin 2 → ℝ := fun _ => 0

/-- **常数观测函数跨环境不变**（这就是有内容的 `invariance` 的真值来源）。 -/
theorem constObs_invariant : ∀ e e' : Fin 2, constObs e = constObs e' := by
  intro e e'
  rfl

/-- **【方案 D · 已证】`invariance` 填有内容的命题，且该命题被证明**。

**内容**：构造一个 `ExtendedDataLayer`，其
`invariance := ∀ e e' : Fin 2, constObs e = constObs e'`
（**不是** `True`），并以 `constObs_invariant` **证明**该命题成立。

**与 `extendedDataLayer` 的区别**：后者的 `invariance` 是 `True`（可被
任何东西满足）；本实例的 `invariance` 是**关于具体函数的实质断言**，
其真值**不被** `True` 蕴含（`refObs_not_invariant` 说明同类断言可为假）。

⚠ **诚实边界**：本实例仍只是**形式化玩具**——`constObs` 是人为选取的常函数，
不是经验数据。它演示「`invariance` 这一槽位**可以**承载可证内容」，
**不**声称任何经验环境族满足不变性。 -/
def contentfulDataLayer : ExtendedDataLayer where
  environmentsAtLeastTwo := true
  invariance := ∀ e e' : Fin 2, constObs e = constObs e'
  scopeNote := "invariance 填实质命题（constObs 跨环境不变）；仅为形式化演示，非经验断言"

/-- **【方案 D · 已证】该实例的 `invariance` **确实成立**。

**内容**：`contentfulDataLayer.invariance` 为真。

⚠ **非同义反复核查**：本定理的**前件为空**（无假设），
结论是 `contentfulDataLayer.invariance`——这是一个**定义后展开**的
实质等式断言 `∀ e e' : Fin 2, constObs e = constObs e'`。
它**不是** `contentfulDataLayer` 的构造前提（`def` 不校验 `invariance` 的值，
`ExtendedDataLayer` 无 `invariance` 的证明字段），故不存在「前件已含结论」。
证明必须通过 `constObs_invariant` 实际给出。 -/
theorem contentfulDataLayer_invariance : contentfulDataLayer.invariance :=
  constObs_invariant

/-- **【方案 D 对照组 · 已证】`invariance` 的**假**值同样可构造**。

**内容**：存在一个 `ExtendedDataLayer`，其 `invariance` 填
「`refObs` 跨环境不变」这一**假**命题；即 `invariance` 槽位
**不是**恒真的，`True` 之外还有可判定的实质取值。

⚠ **非同义反复核查**：结论是 `∃ d, ¬ d.invariance`，须构造实例
**并证明**该内层命题为假（用 `refObs_not_invariant`），
而不是把 `¬ d.invariance` 放进前件。 -/
theorem contentfulDataLayer_false_variant :
    ∃ d : ExtendedDataLayer,
      ¬ d.invariance :=
  ⟨{ environmentsAtLeastTwo := true
     invariance := ∀ e e' : Fin 2, refObs e = refObs e' },
   fun h => refObs_not_invariant (h 0 1)⟩

/-! ## §5 总览（供人工核对）

**本文件已证（零 sorry，经 `lake env lean` 验证）**：

| # | 定理 | 方案 | 一句话 |
|---|---|---|---|
| 1 | `invariance_not_automatic` | C | 不变性**不自动**成立 |
| 2 | `invariance_fails_fin2` | C | 显式反例 `f 0 ≠ f 1` |
| 3 | `invariance_vacuous_of_subsingleton` | B | 单环境 ⟹ 不变性**空真** |
| 4 | `invariance_vacuous_of_unique` | B | `Unique` 版同上 |
| 5 | `invariance_iff_const` | A | 非空环境：不变 ⟺ 常函数 |
| 6 | `invariance_nonempty` | A | 不变性**非空**（常函数满足） |
| 7 | `invariance_fails_of_nontrivial_fin2` | A/B | 非退化 ⟹ 不变性**可失败** |
| 8 | `refObs_not_invariant` | D | 参考函数**不**不变 |
| 9 | `constObs_invariant` | D | 常函数**不变** |
| 10 | `contentfulDataLayer_invariance` | **D** | ⭐ `invariance` 填实质命题并**证明**之 |
| 11 | `contentfulDataLayer_false_variant` | D | `invariance` 的**假**取值可构造 |

**⟹ 3–4 + 5–7 合起来给出「`environmentsAtLeastTwo` 不可省」的形式化论证**：
退化时不变性空真（3、4）；非退化时不变性 ⟺ 常函数（5），且可失败（7）。

**⟹ 10–11 合起来给出「`invariance` 槽位可承载可证内容」的形式化论证**：
同一类型上有真的实质取值（10）与假的实质取值（11），
故 `invariance` 既非恒真也非恒假（呼应 `invariance_free`）。

**⚠ 仍不声称**：任何**真实经验环境族**满足不变性。那是数据侧问题，
本文件只做「性质层」与「槽位层」的形式化。 -/

end InvarianceContentful
end FateV2.Meta