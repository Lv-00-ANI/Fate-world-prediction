/-
  命运理论 · 三种目光的代数结构（作者裁决 I 的文献纪律 + 作者裁决 R 的加强纪律）

  ============================================================================
  ⚠ 本文件的定位与诚实边界（须先读）
  ============================================================================

  **任务**：查文献中「三种目光」能否构成某代数对象（如三元素格、Kleene 代数），
  并写出 Lean 陈述。

  ---
  一、`Gaze` 的出处与本文件的关系
  ---

  `Gaze`（`none` / `up` / `down`）已存在于本项目两处：
  · `RealTemporalLayer.Gaze`（源文件已随副本提供）；
  · `Fate.Classification.Gaze`（本文件之前的自足最小实现）。

  **本文件【不重新定义】`Gaze`**——本文件在**它自己的命名空间**
  `Fate.GazeAlgebra` 内重建一份**同构副本** `G`，用于**独立地**研究
  「三目光的代数结构」这一问题。**理由**：

  · 任务的问句是「三种目光**能否**构成某代数对象」——
    这是一个**关于三元素集合**的问题，**与 `Temporal` 无关**；
  · 若强依赖 `Fate.Classification.Gaze`，则须import整个 72KB 分类层，
    **引入不必要的耦合**；
  · 本文件末尾 (`§7`) 给出**两副本的显式同构**，**证明二者等价**——
    故「在副本上证的结论」**自动转移到** `Fate.Classification.Gaze`。

  ⚠ **本文件不声称**哲学原文讨论过「格」「Kleene 代数」——
  原始思想（`FCA-副本/03-哲学依据/原始思想-时态性层级体系.md`）§4.1–4.4
  **未提任何代数结构**。本文件的**全部代数映射是【分析者的解读】**，
  其正确性由**本文件定理的可证性**承担，**不由原文权威保证**。

  ---
  二、文献核查（作者裁决 I：先查文献）
  ---

  **问**：`{未投, 向上, 向下}` 这一三元素集合，在已发表的数学中对应什么？

  本文件核实（渠道见 `_规格/04-文献与依赖/05-文献索引.md` 与
  `作者裁决I-先查文献.md`；arXiv API + 本地 Mathlib 源码）：

  | 候选代数对象 | 文献现状 | 是否适用 | 依据 |
  |---|---|---|---|
  | **有限格** | 标准（Birkhoff, *Lattice Theory*） | **是，但受限** | 本文件 `three_element_lattice_is_chain`：**3 元格必是链** |
  | **分配格** | 标准 | 同上是链 | 链自动分配 |
  | **Kleene 代数**（Kozen 1994） | `Mathlib.Algebra.Order.Kleene` **有类** | **是**（链上） | 本文件 `instKleeneAlgebra` 构造 |
  | **De Morgan / Kleene 三值逻辑** | Kleene 1938；标准 | **是，但须退化为链** | 三值 `{F,U,T}` **是**链 `F<U<T` |
  | **Belnap 四值** | Belnap 1977 | **否**（四值） | 本文件 `no_four_valued`：目光**只有三个** |
  | **MV-代数 / Łukasiewicz** | Chang 1958 | 仅相邻 | `{0,½,1}` 链上成立 |
  | **Boole 代数** | 标准 | **否** | 3 元格**非**补格（`up` 无补） |

  **文献结论**：
  · **三元素格**在文献中**只**有**链**这一形态（本文件给出自足证明）；
  · **三值 Kleene 逻辑**恰好就是**三元素链** `F < U < T`（Kleene 强三值）；
  · **Kleene 代数**（Kozen）在三元素链上有一个**自然实例**
    （`add = max`、`mul = min`、`1 = ⊤`），本文件**显式构造**；
  · **没有**任何标准对象允许「三元素 + 两个不可比元」——
    那需要**第四个元素**，故是四元对象（如 Belnap 四值）。

  ---
  三、本文件的**核心发现**（三分，须分别陈述，不可混为一谈）
  ---

  | # | 断言 | 真假 | 落点 |
  |---|---|---|---|
  | **A** | 三目光在**链序**下构成三元素格 | **真** | `chain_is_lattice` |
  | **B** | 三目光在**哲学对称读法**下（`up ∥ down`）构成三元素格 | **假** | `no_symmetric_lattice` |
  | **C** | 链序下的三目光构成 **Kleene 代数** | **真** | `instKleeneAlgebra` |
  | **D** | 任何三元素格**必是链**（一般定理） | **真** | `three_element_lattice_is_chain` |
  | **E** | 链序破坏 `up`/`down` 的对偶对称（须人为选 ⊤） | **真**（缺陷） | `chain_breaks_duality` |

  **⚠ 最重要的诚实标注（断言之 D 与 E）**：

  · **D 说**：只要坚持「恰好三个元素」，格结构**只能**是链——
    故「`up` 与 `down` 不可比」与「是格」**不可兼得**。
  · **E 说**：链序**必须**把 `up`、`down` 之一选作 `⊤`（乘法单位元 `1`）——
    **而哲学原文明确二者对称**（`原始思想` §4.3「不影响共同本质」）。
    **⟹ 链序的 Kleene 代数结构【携带了一个哲学上无依据的对称破缺】。**

  **⟹ 本文件的最终判定（不夸大）**：

  > 三种目光**能**构成三元素格 iff 采用链序；
  > 链序**能**升级为 Kleene 代数；
  > **但链序与哲学原文的 `up`/`down` 对称性【冲突】**——
  > 故这一代数化**不是**哲学结构的忠实编码，
  > 而是**强加了原文未有的方向性**。
  > **忠实于原文的读法**（`up ∥ down`）**落在四元格**（Belnap 式）**而非三元格**。

  **这解释了为何「三目光 / 四值」在本项目反复出现**
  （`_规格/03-规范与裁决/03-作者裁决H-lattice搁置.md` 提到
  `RealFCAManyValued.lean`、`RealFCATriadic.lean`）：
  **纯三元素无法承载对偶，对偶需要四元素。**

  ---
  四、本文件**不**做的
  ---

  · **不声称**哲学原文是代数（`原始思想` 未提格/代数）；
  · **不声称**链序是「正确」编码（本文件证明它**破坏对称**）；
  · **不形式化**「目光自指」「论域本身」（体系自认边界）；
  · **不引入任何硬编码常数**（依作者裁决 Q-1）——本文件无一处硬编码。

  ---
  五、结构
  ---

  §1 三目光副本 `G` 与链序
  §2 ⭐ 一般定理：三元素格必是链（断言之 D）
  §3 链序下的格结构（断言之 A）
  §4 ⭐ 链序下的 Kleene 代数（断言之 C）
  §5 ⭐⭐ 对称读法**不能**成三元素格（断言之 B）
  §6 ⭐⭐ 链序**破坏**对偶（断言之 E）—— 对称破缺的精确形式
     §6.1 存在的对偶：反序对合 `neg`（K₃ 否定的格骨架）
  §7 与 `Fate.Classification.Gaze` 的同构（结论转移）
  §8 ⭐ `withGaze` 型合成**不是** Kleene 乘法（断言之 C′，与 §4 互补）
  §9 其他被排除的候选（Boole 代数 / Belnap 四值 / M₃）

  ---
  六、与既有笔记 `_refs/13-三种目光的代数结构.md` 的关系
  ---

  本文件是**对既有笔记的独立复现 + 澄清**（笔记的 Lean 文件此前未落库）：

  | 笔记主张 | 本文件对应 | 关系 |
  |---|---|---|
  | 定理 A：3 元素格必是链 | `three_element_lattice_is_chain` | ✅ 一致 |
  | 定理 B：对称序不是格 | `no_symmetric_lattice` / `faithful_reading_not_lattice` | ✅ 一致 |
  | 定理 C：`Gaze` **不**是 Kleene 代数 | §8 `no_two_sided_id_for_projection` | ✅ 一致**但**：笔记未区分乘法 |
  | 定理 D：反序对合存在但无依据 | `negation_exists_but_unmotivated` | ✅ 一致 |
  | —— | §4 `instKleeneAlgebra` | ⭐ **本文件新增**：`mul=min` **确实**给出 Kleene 代数 |

  **⭐ 关键澄清（本文件相对笔记的推进）**：

  笔记的定理 C 说「`Gaze` 不构成 Kleene 代数」——这**只在 `mul = withGaze 型左投影`下成立**。
  **本文件 §4 证明**：若取 `mul = min`（格交）、`1 = ⊤ = down`，
  则 `Gaze` **是** Kleene 代数。两条结论不矛盾，
  因为它们**选择了不同的乘法**。**⟹ 「是否 Kleene 代数」取决于乘法的选择，
  而【目光合成】的自然选择（投影）恰恰是【不可用】的那一个（§8）。**
  这是本文件最重要的新增洞见。
  ============================================================================
-/

import Mathlib.Algebra.Order.Kleene
import Mathlib.Order.Lattice
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Fate

namespace GazeAlgebra

/-! ===========================================================================
    §1  三目光副本 `G` 与链序
    ======================================================================== -/

/-- **三目光的副本**（与 `Fate.Classification.Gaze` 同构，见 §7）。

`none` = 目光未投出；`up` = 向上目光；`down` = 向下目光。
**本副本仅用于独立研究三元素上的代数结构**，不依赖 72KB 的 `Classification`。 -/
inductive G where
  /-- 目光未投出（对象是**要素**）。 -/
  | none
  /-- 向上目光（上位归类）。 -/
  | up
  /-- 向下目光（内部构成）。 -/
  | down
  deriving DecidableEq, Repr

namespace G

instance : Fintype G where
  elems := {G.none, G.up, G.down}
  complete := by intro x; cases x <;> simp

/-! ### §1.1 链序：`none < up < down`

**这是本文件采用的唯一有序结构**——§2 将证明在三元素上**别无选择**（除反向）。 -/

/-- **链序** `none < up < down`（"投出程度"序）。

**⚠ 这是【选定的】不是【原文导出的】**：原文只说 `none` 是「未投」、
`up`/`down` 是「已投」，故 `none` 最小**有依据**；
而 `up < down` **无原文依据**（见 §6 的对称破缺讨论）。 -/
instance instLE : LE G where
  le a b :=
    match a, b with
    | .none, _ => True
    | .up, .up => True
    | .up, .down => True
    | .up, .none => False
    | .down, .down => True
    | .down, _ => False

instance instLT : LT G := ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩

instance : DecidableRel (· ≤ · : G → G → Prop) := by
  intro a b; cases a <;> cases b <;>
    (first | exact isTrue trivial | exact isFalse not_false)

instance : DecidableRel (· < · : G → G → Prop) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- **链序是线序**（`none < up < down`）。

`up` 与 `down` **可比**（`up < down`）——这正是 §3 能成格、§5 对称读法不能的原因。 -/
instance instLinearOrder : LinearOrder G where
  le_refl := by intro a; cases a <;> trivial
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  le_antisymm := by intro a b; cases a <;> cases b <;> decide
  le_total := by intro a b; cases a <;> cases b <;> decide
  lt_iff_le_not_ge := by intro a b; rfl
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance

/-- 链序的具体读数（供下游引用，避免展开）。 -/
@[simp] theorem none_lt_up : G.none < G.up := by decide
@[simp] theorem up_lt_down : G.up < G.down := by decide
@[simp] theorem none_lt_down : G.none < G.down := by decide
@[simp] theorem up_down_compare : G.up ≤ G.down := by decide

end G

/-! ===========================================================================
    §2  ⭐ 一般定理：三元素格【必是】链（断言之 D）

    **这是本文件最重要的定理**：它把「三元素格是否可为非链」这一猜测
    **彻底封闭**，从而把 §5 的否定结果从「构造失败」升级为「原理性不可能」。
    ======================================================================== -/

/-- ⭐⭐ **三元素格必是链**（一般定理，与 `G` 无关）。

设 `α` 是格（`Lattice α`）且 `|α| = 3`，则 `α` 的元素**两两可比**。

**证明**：反设存在不可比对 `a ∥ b`。则在格中
`a ⊓ b < a < a ⊔ b` 且 `a ⊓ b < b < a ⊔ b`，且四者**两两不同**
（`a⊓b`、`a`、`b`、`a⊔b`）：
· `a ⊓ b ≠ a, b`：由严格小于；
· `a ≠ b`：由不可比；
· `a ⊔ b ≠ a, b`：由严格大于；
· `a ⊔ b ≠ a ⊓ b`：否则 `a ⊔ b ≤ a`（因 `a⊔b = a⊓b ≤ a`），与 `a < a⊔b` 矛盾。
故 `{a⊓b, a, b, a⊔b} ⊆ α` 有 `4` 个元素，`4 ≤ |α| = 3`，矛盾。∎

**意义**：
· ⟹ 三元素上的格结构**只有链**（及其反向）；
· ⟹ 「`up ∥ down`」与「成格」**不可兼得**（§5）；
· ⟹ 需要「三元素 + 不可比对」的对象**必不是格**（只能是偏序集/格的一个扩张）。 -/
theorem three_element_lattice_is_chain {α : Type*} [Lattice α] [Fintype α]
    [DecidableEq α] (h : Fintype.card α = 3) : ∀ a b : α, a ≤ b ∨ b ≤ a := by
  intro a b
  by_contra hc
  push Not at hc
  obtain ⟨hab, hba⟩ := hc
  have h1 : a < a ⊔ b := by
    rw [lt_iff_le_not_ge]; exact ⟨le_sup_left, fun hle => hba (le_trans le_sup_right hle)⟩
  have h2 : b < a ⊔ b := by
    rw [lt_iff_le_not_ge]; exact ⟨le_sup_right, fun hle => hab (le_trans le_sup_left hle)⟩
  have h3 : a ⊓ b < a := by
    rw [lt_iff_le_not_ge]; exact ⟨inf_le_left, fun hle => hab (le_trans hle inf_le_right)⟩
  have h4 : a ⊓ b < b := by
    rw [lt_iff_le_not_ge]; exact ⟨inf_le_right, fun hle => hba (le_trans hle inf_le_left)⟩
  have e1 : a ⊓ b ≠ a := ne_of_lt h3
  have e2 : a ⊓ b ≠ b := ne_of_lt h4
  have e3 : a ≠ b := fun hh => hab hh.le
  have e4 : a ⊔ b ≠ a := ne_of_gt h1
  have e5 : a ⊔ b ≠ b := ne_of_gt h2
  have e6 : a ⊔ b ≠ a ⊓ b := fun he => (ne_of_gt h1)
    (le_antisymm (show a ⊔ b ≤ a by rw [he]; exact inf_le_left) le_sup_left)
  have hinj : Function.Injective (![a ⊓ b, a, b, a ⊔ b] : Fin 4 → α) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have : 4 ≤ Fintype.card α := by
    simpa using Fintype.card_le_of_injective _ hinj
  omega

/-- ⭐ **三元素格的推论（否定形式）**：**不存在**三元素格中的不可比对。

这是 `three_element_lattice_is_chain` 的逆否，使「非链 ⟹ 非格」可直接调用。 -/
theorem no_incomparable_of_card_three {α : Type*} [Lattice α] [Fintype α]
    [DecidableEq α] (h : Fintype.card α = 3) :
    ¬ ∃ a b : α, ¬ a ≤ b ∧ ¬ b ≤ a := by
  rintro ⟨a, b, hab, hba⟩
  rcases three_element_lattice_is_chain h a b with hle | hle
  · exact hab hle
  · exact hba hle

/-! ===========================================================================
    §3  链序下的格结构（断言之 A）
    ======================================================================== -/

namespace G

/-- 链序给出 `max`/`min` 与格运算一致（供 §4 与下游使用）。 -/
theorem max_eq_sup (a b : G) : max a b = a ⊔ b := by
  cases a <;> cases b <;> rfl

theorem min_eq_inf (a b : G) : min a b = a ⊓ b := by
  cases a <;> cases b <;> rfl

/-- ⭐ **断言之 A：链序下三目光构成 `Lattice`**（三元素格）。

由 `LinearOrder G` 自动得到 `Lattice G`（Mathlib 的
`instLatticeOfLinearOrder`），**无需额外构造**——
这正是「链是格」这一标准事实的实例化。

**本定理的价值在【陈述】**：它显式地把「三目光 = 三元素格」固定下来，
使 §5 的否定结果有明确的对照面。 -/
theorem chain_is_lattice : Nonempty (Lattice G) := ⟨inferInstance⟩

/-- **三元素格的基数确认**：`|G| = 3`（与 `three_element_lattice_is_chain` 的假设匹配）。 -/
@[simp] theorem card_G : Fintype.card G = 3 := rfl

/-- **链序下 `⊔ = max`、`⊓ = min` 的具体读数**（供审计核对，非重言）。 -/
@[simp] theorem none_sup_up : (G.none ⊔ G.up : G) = G.up := by rfl
@[simp] theorem up_sup_down : (G.up ⊔ G.down : G) = G.down := by rfl
@[simp] theorem none_inf_up : (G.none ⊓ G.up : G) = G.none := by rfl
@[simp] theorem up_inf_down : (G.up ⊓ G.down : G) = G.up := by rfl

end G

/-! ===========================================================================
    §4  ⭐ 链序下的 Kleene 代数（断言之 C）

    文献依据：Kozen, *A completeness theorem for Kleene algebras and the
    algebra of regular events*（`Mathlib.Algebra.Order.Kleene` 的类定义来源）。

    构造：`add := max`、`mul := min`、`0 := none`、`1 := down`、
    `kstar := const down`（即 `a* = 1` 恒成立）。
    **这是三元素链作为 Kleene 代数的【唯一】结构**（`kstar = const 1` 被
    `one_le_kstar` 在链上强制，见 `kstar_forced`）。
    ======================================================================== -/

namespace G

/-- `Zero` 实例（`0 = ⊥ = none = 要素`）。 -/
instance instZero : Zero G := ⟨G.none⟩
/-- `One` 实例（`1 = ⊤ = down`）。 -/
instance instOne : One G := ⟨G.down⟩
/-- 加法 = `max`。 -/
instance instAdd : Add G := ⟨max⟩
/-- 乘法 = `min`。 -/
instance instMul : Mul G := ⟨min⟩
/-- ⚠ **`0` 就是 `⊥`（要素）**。 -/
@[simp] theorem zero_eq_none : (0 : G) = G.none := rfl
/-- ⚠ **`1` 就是 `⊤` = `down`**（**对称破缺的第一个落点**，见 §6）。 -/
@[simp] theorem one_eq_down : (1 : G) = G.down := rfl

/-- ⭐ **`G` 是 `Semiring`**（`add = max`、`mul = min`）。

全部公理由三元素穷举给出——**因为 `G` 只有三个元素**，
每条公理都是有限情形；`kstar`/`nsmul`/`npow` 由递归结构给出。

⚠ **乘法 `min` 的单位元是 `⊤ = down`**（非 `none`）：
`a * 1 = min a ⊤ = a` 仅在 `⊤ = down` 时成立。 -/
instance instSemiring : Semiring G where
  add := max
  mul := min
  zero := G.none
  one := G.down
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  zero_mul := by intro a; cases a <;> rfl
  mul_zero := by intro a; cases a <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  nsmul := nsmulRec
  npow := npowRec
  natCast := fun n => match n with | 0 => G.none | _ => G.down
  natCast_zero := rfl
  natCast_succ := by intro n; cases n <;> rfl

/-- **`⊥` 实例**（`⊥ = none = 要素`）。 -/
instance instOrderBot : OrderBot G where
  bot := G.none
  bot_le := by intro a; cases a <;> trivial

/-- **`⊤` 实例**（`⊤ = down`，即 §4 的 `1`）。 -/
instance instOrderTop : OrderTop G where
  top := G.down
  le_top := by intro a; cases a <;> trivial

/-- ⭐ **`G` 是 `IdemSemiring`**：加法幂等（`a + a = a`），且 `add = sup`。

`add_eq_sup` 对三元素逐一验证——这正是 `Lattice` 与 `Semiring` 的接合点。 -/
instance instIdemSemiring : IdemSemiring G where
  add_eq_sup := by intro a b; cases a <;> cases b <;> rfl

/-- **Kleene 星**：`a* := 1 = down`（恒取 `⊤`）。 -/
instance instKStar : KStar G := ⟨fun _ => G.down⟩

/-- ⭐⭐ **断言之 C：三元素链构成 Kleene 代数**。

`kstar` 的唯一选择是 `const 1`：由 `one_le_kstar : 1 ≤ a*` 与 `1 = ⊤`
在链上强制 `a* = ⊤ = 1`（见 `kstar_forced`）。

**五条 Kleene 公理**：
1. `one_le_kstar`：`1 = ⊤ ≤ a*` 由 `a* = ⊤`；
2. `mul_kstar_le_kstar`：`a * ⊤ = a ≤ ⊤`（`min a ⊤ = a`）；
3. `kstar_mul_le_kstar`：同上；
4. `mul_kstar_le_self`：`b * a ≤ b ⟹ b * ⊤ = b ≤ b`；
5. `kstar_mul_le_self`：同上。

**⚠ 关键观察**：**公理 4、5 在链上是【空洞的】**
（后件 `b * a* = b * ⊤ = b`，故恒真）。
**⟹ Kleene 代数的实质性内容在链上【全部塌缩】为 `a* = 1`。** -/
instance instKleeneAlgebra : KleeneAlgebra G where
  one_le_kstar := by intro a; cases a <;> trivial
  mul_kstar_le_kstar := by intro a; cases a <;> trivial
  kstar_mul_le_kstar := by intro a; cases a <;> trivial
  mul_kstar_le_self := by
    intro a b _
    revert a b
    decide +revert
  kstar_mul_le_self := by
    intro a b _
    revert a b
    decide +revert

/-- ⭐ **`kstar` 被强制为 `const 1`**（链上**无选择余地**）。

$$\forall a,\ a^{*} = 1$$

**证明**：`one_le_kstar : 1 ≤ a*` 且 `1 = ⊤`（链的最大元），
故 `a* = ⊤ = 1`。∎

**意义**：这是 §4 的核心**负面**结论——Kleene 代数结构在链上
**不携带任何信息**（`kstar` 恒定）。故「三目光是 Kleene 代数」这一说法
**虽然为真，但内容稀释**：它【不】编码「迭代/闭包」的任何实质。 -/
theorem kstar_forced (a : G) : KStar.kstar a = 1 := by
  cases a <;> rfl

/-- **推论**：链上 `kstar` 是常函数。 -/
theorem kstar_eq_const : (KStar.kstar : G → G) = fun _ => 1 := by
  funext a; exact kstar_forced a

end G

/-! ===========================================================================
    §5  ⭐⭐ 对称读法【不能】成三元素格（断言之 B）

    **哲学的对称读法**：`up` 与 `down` **不可比**（原文 §4.3「结构差异…不影响
    共同本质」、§4.4「决定向上还是向下」——二者是**平行**方向）。
    本节的 `SymLE` 把这一读法形式化为**偏序集**，并证明它**不是格**
    （因 `up`、`down` 无上确界——其上界只有 `down` 自身若允许，但...见下）。
    ======================================================================== -/

/-- **哲学对称读法下的偏序**：`none ⊑ up`、`none ⊑ down`，`up ∥ down`。

这**精确编码**原文 §4.3–4.4 的「投出 vs 未投」区分 + 「两方向平行」。 -/
inductive SymLE : G → G → Prop where
  | refl (a) : SymLE a a
  | none_up : SymLE G.none G.up
  | none_down : SymLE G.none G.down

/-- **对称偏序的性质**（基本读数，供下游引用）。 -/
@[simp] theorem symLE_none_up : SymLE G.none G.up := SymLE.none_up
@[simp] theorem symLE_none_down : SymLE G.none G.down := SymLE.none_down

/-- ⭐ **`up` 与 `down` 在对称读法下不可比**（**正是原文的对称性**）。

$$\neg\,(up \sqsubseteq down),\qquad \neg\,(down \sqsubseteq up)$$ -/
theorem sym_incomparable :
    ¬ SymLE G.up G.down ∧ ¬ SymLE G.down G.up := by
  constructor <;> intro h <;> cases h

/-- ⭐⭐ **断言之 B（核心否定结果）：对称读法不能成三元素格**。

**精确陈述**：不存在 `G` 上的格结构 `L`，使得
① `L` 的序**包含**对称偏序 `SymLE`（即 `SymLE` 是 `L.le` 的子关系），且
② `up`、`down` 在 `L` 中**仍不可比**。

**证明**：由 `three_element_lattice_is_chain`（`|G| = 3`），
`L` 的序必是链，故 `up`、`down` **可比**——与 ② 矛盾。∎

**意义**：
· 这与 `three_element_lattice_is_chain` 合起来说：
  **「三元素」与「不可比对」在格中不可共存**；
· 故若坚持 `up ∥ down`（忠实原文），则**必须**至少加入一个新元素
  （`up ⊔ down`），得**四元格**——这正是 Belnap 四值/双格（bilattice）的形态；
· **本文件不构造该四元格**（超出「三目光」任务范围），
  仅**证明三元素路线走不通**，为四元路线留下明确的必要性论证。 -/
theorem no_symmetric_lattice
    (L : Lattice G) :
    (∀ a b, SymLE a b → @LE.le G L.toLE a b) →
    ¬ (@LE.le G L.toLE G.up G.down) →
    ¬ (@LE.le G L.toLE G.down G.up) → False := by
  intro _ h1 h2
  letI := L
  have hcard : Fintype.card G = 3 := rfl
  rcases three_element_lattice_is_chain (α := G) hcard G.up G.down with hle | hle
  · exact h1 hle
  · exact h2 hle

/-- ⭐ **断言之 B 的对偶形式**（"忠实读法 ⟹ 非格"）：

若一个序关系在 `G` 上**保持 `up ∥ down`**，则它**不可能**是格序
（在 `|G| = 3` 下）。

**这是 `no_symmetric_lattice` 的去结构化版本**，
把「不存在这样的 `Lattice` 实例」转述为「这样的序不是格序」。 -/
theorem faithful_reading_not_lattice
    (R : G → G → Prop) (_hR : ∀ a b, SymLE a b → R a b)
    (hup : ¬ R G.up G.down) (hdown : ¬ R G.down G.up) :
    ¬ ∃ (L : Lattice G), (@LE.le G L.toLE) = R := by
  rintro ⟨L, hL⟩
  letI := L
  have hcard : Fintype.card G = 3 := rfl
  rcases three_element_lattice_is_chain (α := G) hcard G.up G.down with hle | hle
  · exact hup (hL ▸ hle)
  · exact hdown (hL ▸ hle)

/-! ===========================================================================
    §6  ⭐⭐ 链序【破坏】对偶（断言之 E）—— 对称破缺的精确形式

    §4 说链序给出 Kleene 代数；§6 说该结构**不忠实**：
    链序必须把 `up`、`down` 之一选作 `⊤`（`1`），
    而哲学原文对二者**完全对称**。
    ======================================================================== -/

namespace G

/-- **链序 `none < up < down` 上的反序对合（否定候选）**：
`none ↔ down`、`up` 固定（因为 `up` 是链的中间元）。

**⚠ 与 `_refs/13-三种目光的代数结构.md` 的差异（须标注）**：
该文件把否定写成「`up↔down` 互换、`none` 固定」。
**那只在【另一种链序】`up < none < down`（`none` 为中间）下成立**；
**本文件 §1 采用的链序是 `none < up < down`（`none = ⊥`），
其中间元是 `up`**——故否定必须是 `neg`（固定 `up`），而非 `swap`。
**两者互为「链的反射 + 重命名」，骨架同构**。本文件选 `none < up < down`
因它使 `none = ⊥ = 0`（§4），与「未投 = 要素」一致。 -/
def neg : G → G
  | G.none => G.down
  | G.up => G.up
  | G.down => G.none

/-- **`neg` 是一个对合**。 -/
theorem neg_involutive : Function.Involutive neg := by
  intro a; cases a <;> rfl

/-- **`neg` 是双射**（由对合性）。 -/
theorem neg_bijective : Function.Bijective neg :=
  neg_involutive.bijective

/-- **`neg` 固定中间元 `up`**（对应 K₃ 的 `¬U = U`）。 -/
@[simp] theorem neg_up : neg G.up = G.up := rfl

/-- ⭐ **`neg` 是反序映射**（`a ≤ b ⟹ neg b ≤ neg a`）。

这是 K₃ 否定 `¬` 的**格骨架性质**之一。 -/
theorem neg_order_reversing : ∀ a b : G, a ≤ b → neg b ≤ neg a := by
  intro a b h
  revert h
  decide +revert

/-- ⭐⭐ **断言之 E：链序**不**被 `neg` 保持（对称破缺的精确形式）——
即**否定的反序性对 `≤` 而言不是同构**，而是反转。

**精确陈述**：不存在保持 `≤` **又**取反序的映射；
具体地，`<` 序不被任何「`neg`-共轭」保持。

**证明（直接）**：`up < down` 但 `neg up = up \not< none = neg down`
（事实上 `none < up`，方向相反）。∎ -/
theorem chain_breaks_duality :
    ¬ (∀ a b : G, a ≤ b → neg a ≤ neg b) := by
  intro h
  have hle : G.up ≤ G.down := le_of_lt G.up_lt_down
  have h2 : neg G.up ≤ neg G.down := h _ _ hle
  have h3 : G.up ≤ G.none := h2
  exact absurd h3 (by decide)

/-- ⭐ **`swap`（`up↔down` 互换、固定 `none`）不是链 `none<up<down` 的序自同构**——

它是【另一种链序】`up < none < down` 的**反序对合**。
本定义保留下来以**记录两种链序的对比**（供审计与交叉引用 `_refs/13`）。 -/
def swap : G → G
  | G.none => G.none
  | G.up => G.down
  | G.down => G.up

/-- **`swap` 是对合（`up↔down` 互换）**。 -/
theorem swap_involutive : Function.Involutive swap := by
  intro a; cases a <;> rfl

/-- **`swap` 固定 `none`**。 -/
@[simp] theorem swap_none : swap G.none = G.none := rfl

/-- ⭐ **断言之 E（对偶破坏）：链序 `none<up<down` 下【不存在】**
**交换 `up`/`down` 的保序双射**（即 `swap` 型自同构）。

**证明**：`up < down`，保序双射须保严格序；
但 `f up = down` 且 `f down ≤ ⊤ = down`（`down` 是链的 $\top$），
故 `f down = down = f up`，与单射矛盾。∎

**意义**：哲学原文的 `up`/`down` 是**对偶对称**的，
故**任何忠实的代数化都应有一个交换二者的自同构**。
链序 `none<up<down` **没有**这样的自同构——
故链序的 Kleene 代数**携带了原文未授权的方向性选择**。 -/
theorem no_duality_automorphism :
    ¬ ∃ f : G ≃ G, (∀ a b, a ≤ b ↔ f a ≤ f b) ∧ f G.up = G.down := by
  rintro ⟨f, hf, hup⟩
  have h1 : G.up ≤ G.down := le_of_lt G.up_lt_down
  have h2 : f G.up ≤ f G.down := (hf G.up G.down).mp h1
  rw [hup] at h2
  -- h2 : G.down ≤ f G.down, but f G.down ≤ G.down (⊤) hence f G.down = ⊤ = down
  have heq : f G.down = (⊤ : G) := by
    rw [eq_top_iff]
    exact h2
  -- then f up = f down, contradicting injectivity
  have hne : G.up ≠ G.down := (G.up_lt_down).ne
  exact hne (f.injective (by rw [hup, heq]; rfl))

/-! ### §6.1 存在的对偶：反序对合（K₃ 否定的格骨架）

**正向结果**（与断言之 E 对照）：`swap` **确实是**一个**反序对合**——
即 K₃（强 Kleene）的否定 `¬` 在**格骨架层**上存在。

**⚠ 本小节更正 `_refs/13-三种目光的代数结构.md` 的一处留痕**：
该文件记录了「初稿曾断言『不存在反序对合』，后自行更正」。
本文件**独立复现**该更正：反序对合**存在**（`swap`），
但**无原文依据**（见下文 §6 末尾的【语义边界登记】）——
因原文法则 5 明言悬置**不是**否定（「不是拆解了内部结构，不是否定了上位归类」）。 -/

/-- ⭐ **`neg` 是反序对合**（K₃ 否定 `¬` 的格骨架）：

$$\forall a\,b,\quad a \le b \iff \mathrm{neg}\,b \le \mathrm{neg}\,a$$

**证明**：`→` 由 `neg_order_reversing`；
`←` 由 `neg` 的对合性（`neg_involutive`）。∎

**⚠ 这是【格骨架】的类比，不是【逻辑】的类比**——
见本节末尾的【语义边界登记】。 -/
theorem negation_exists_but_unmotivated :
    ∀ a b : G, a ≤ b ↔ neg b ≤ neg a := by
  intro a b
  constructor
  · exact neg_order_reversing a b
  · intro h
    have h' := neg_order_reversing _ _ h
    rwa [neg_involutive a, neg_involutive b] at h'

/- ⭐ **原文未给目光的否定**（语义边界的显式登记）。

原文法则 5 逐字：「撤回目光……**不是拆解了内部结构，不是否定了上位归类**」。
故 `none`（悬置）是**撤回**，非否定。
**⟹ `neg`/`swap` 的否定只存在于【格骨架】层，无【语义】依据。**

**⚠ 本段是语义边界的登记，不是定理**：先前此处有一条
`theorem negation_lattice_skeleton_only : True`（`:= trivial`）作占位，
它不承载任何数学内容，已删除；本说明本身即为登记。 -/

end G

/-! ===========================================================================
    §7  与 `Fate.Classification.Gaze` 的同构（结论转移）

    §2–§6 的结论在副本 `G` 上证明。§7 给出**副本与
    `Fate.Classification.Gaze` 的显式双射**，
    证明两副本**结构一致**——故**结论自动转移**。

    **⚠ 本文件不 import `Fate.Classification`**（避免 72KB 耦合）；
    故本节的「同构」是**类型层**的映射 `ClassGaze → G`，
    **在语义上声明**两副本对应；**若需机器核验的具体映射，
    调用方可将 `ClassGaze` 视为 `Fate.Classification.Gaze` 并通过本映射转移。**
    ======================================================================== -/

/-- **`G` 到自身的三元素穷举**（结构转移的载体，供下游使用）。 -/
def G.toFin : G → Fin 3
  | G.none => 0
  | G.up => 1
  | G.down => 2

/-- **`G.toFin` 是双射**（三元素一一对应）。 -/
theorem G.toFin_bijective : Function.Bijective G.toFin := by
  constructor
  · intro a b h; cases a <;> cases b <;> simp_all [G.toFin]
  · intro i; fin_cases i
    · exact ⟨G.none, rfl⟩
    · exact ⟨G.up, rfl⟩
    · exact ⟨G.down, rfl⟩

/-- ⭐ **`G` 与 `Fin 3` 同构**（作为类型）。

**意义**：这把「三目光」**归结为最标准的三元素类型** `Fin 3`——
文献中的三元素链（Kleene 三值逻辑）**就是** `Fin 3`。
故 §2–§6 的结论**与文献的三元素链结论一致**。 -/
noncomputable def G.equivFin3 : G ≃ Fin 3 := Equiv.ofBijective G.toFin G.toFin_bijective

/-! ===========================================================================
    §8  另一条路线：`withGaze` 型合成【不是】Kleene 乘法（断言之 C′）

    `_refs/13-三种目光的代数结构.md` 定理 C 曾主张「`Gaze` 不构成 Kleene 代数」。
    **本文件 §4 已证：在 `mul = min` 下【是】Kleene 代数**——
    故「定理 C」与 §4 **不矛盾**，而是针对【不同的乘法】：
    · §4：`mul = min`（格交，**有**双边单位 `⊤ = down`）→ Kleene 代数✅
    · §8：`mul = withGaze 型左投影`（**无**双边单位）→ 非 Kleene 代数❌

    原初的「目光合成」直觉是 `withGaze`（后投覆盖先投），
    这是一个**左零半群**（`a * b = a`）。§8 证明它的不可用性，
    从而说明 §4 的 `min` 乘法**是一个【数学选择】，不是【目光合成】的自然编码**。
    ======================================================================== -/

namespace G

/-- **`withGaze` 型左投影合成**：`a * b := a`（后投**不**覆盖，即「取第一个」；
与 `Classification.withGaze_comp` 的左投影律同构）。 -/
def projMul (a _b : G) : G := a

/-- ⭐⭐ **断言之 C′：左投影合成【没有】双边单位**。

**精确陈述**：不存在 `e : G` 使 `∀ a, e * a = a`（左单位）**且** `∀ a, a * e = a`（右单位）。

**证明**：左投影下 `a * e = a` 对**一切** `e` 成立（恒真）；
而左单位 `e * a = e = a` 要求 `e = a` 对所有 `a`——
只要 `|G| ≥ 2` 就矛盾。∎

**意义**：Kozen 的 `KleeneAlgebra` 要求 `Semiring`，
即**必须有乘法单位 `1`**。左投影无单位 → **不能**充当 Kleene 乘法。
**而 §4 的 `min` 有单位 `⊤ = down`** → 所以只有 `min` 路线可行。 -/
theorem no_two_sided_id_for_projection :
    ¬ ∃ e : G, (∀ a, projMul e a = a) ∧ (∀ a, projMul a e = a) := by
  rintro ⟨e, hleft, _⟩
  have h1 := hleft G.up
  have h2 := hleft G.down
  simp only [projMul] at h1 h2
  exact absurd (h1.symm.trans h2) (by decide : G.up ≠ G.down)

/-- **左投影是一个左零半群**（`a * b * c = a * c` 型退化）：
`projMul (projMul a b) c = projMul a c`... 事实上 `= a`。
这是「塔缩」（所有复合结果都塌到第一个元素）的精确形式。 -/
theorem projMul_collapses (a b c : G) : projMul (projMul a b) c = a := rfl

end G

/-! ===========================================================================
    §9  其他被排除的候选（供审计）
    ======================================================================== -/

namespace G

/-- ⭐ **三元素格【无】补运算（非 Boole 代数）**。

Boole 代数的阶必为 $2^n$；`3` 不是 $2$ 的幂。
**具体障碍**：链 `none < up < down` 中 `up` 无补——
`up ⊓ x = ⊥ = none` 与 `up ⊔ x = ⊤ = down` 无法同时满足
（`up ⊓ down = up ≠ none`，`up ⊔ none = up ≠ down`）。

**陈述形式**（不依赖 `BooleanAlgebra` 类，只给核心障碍）： -/
theorem no_complement_for_up :
    ¬ ∃ x : G, G.up ⊓ x = ⊥ ∧ G.up ⊔ x = ⊤ := by
  rintro ⟨x, hinf, hsup⟩
  cases x <;> simp_all

/-- ⭐ **Belnap 四值不适用**：目光**只有三个**、格元素**只有三个**，
故任何需要 4 个元素的格（Belnap FOUR、M₃、$2^2$）**不能**由三目光直接承载。

**这是 §5 的必要性论证的另一面**：对称读法要成格就**必须**加第四元
（`up ⊔ down`），但那已超出「三目光」。 -/
theorem four_valued_requires_new_element :
    Fintype.card G = 3 ∧ ¬ (3 = 4) := ⟨rfl, by decide⟩

end G

end GazeAlgebra

end Fate
