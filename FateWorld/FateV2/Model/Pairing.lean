import FateWorld.FateV2.Rules.Adjacency
import FateWorld.FateV2.Rules.TrajPattern
/-!
  # Model · Pairing

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Pairing.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Adjacency, TrajPattern
  - 补充 open 域：FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  配对接口：唯一与真实数据格式耦合的地方（作者确认）

  **裁决来源**：作者原话
  * 「我不知道哇 这种细节我的确没思考过」（对策略 B 的具体形式）
  * 「可以那就这样」（确认本方案）

  ## 设计原则

  **不为「配对策略 B 到底是什么」做选择** ——
  因为作者明确表示：这类细节**只有遇到真实数据才知道**。

  **故把「配对」抽象成一个接口 `Pairing`**，
  **三种策略（A/B/B'）都是它的实例**：

  | 策略 | 怎么填 `rel` | 需要什么 |
  |---|---|---|
  | **A 相邻** | `Adjacent lt` | `lt` |
  | **B 分组** | `g n = g m ∧ Adjacent lt n m` | `lt` 和 `g` |
  | **B' 直接给** | 直接传入 `rel` | 无 |

  **⟹ `Pairing` 是唯一需要和真实数据打交道的地方。**
  真实数据来了，只需回答一个问题：
  **「这个数据里，哪两个点算一次转移？」**

  **这不是理论的假设，是数据的性质。**

  ## 链

  ```
  数据 --Pairing.rel--> transitions（转移对集）--FCA--> 蕴含 --映射--> 规则
  ```

  ## 诚实边界

  * 本接口**未连接到第一层 FCA**（FCA 实现仍是缺口）。
  * `Pairing.grouped` 中的 `G`（分组标签类型）是参数，未限定。
  =========================================================================== -/

namespace FateV2.Model

open FateV2.Modeling
open FateV2.Rules
namespace Pairing

variable {ι : Type u} {X : StateSpace}

/-- ⭐ **配对接口**：抽象出「哪些索引对算一次转移」。

**⚠ 这是唯一与真实数据格式耦合的地方** ——
不同数据填不同的 `rel`，其余理论部分不变。 -/
structure Pairing (ι : Type u) where
  /-- 配对关系：`rel n m` 表示 `(γ n, γ m)` 算一次转移。 -/
  rel : ι → ι → Prop

/-! ### §0.1 三种策略都是本接口的实例 -/

/-- **策略 A 的配对**：轨迹内部相邻。 -/
def adjacent (lt : ι → ι → Prop) : Pairing ι :=
  ⟨Adjacency.Adjacent lt⟩

/-- **策略 B 的配对**：同组内相邻（`g` 是分组标记）。 -/
def grouped {G : Type v} (lt : ι → ι → Prop) (g : ι → G) : Pairing ι :=
  ⟨fun n m => g n = g m ∧ Adjacency.Adjacent lt n m⟩

/-- **策略 B' 的配对**：直接给定关系。 -/
def direct (rel : ι → ι → Prop) : Pairing ι :=
  ⟨rel⟩

/-! ### §0.2 ⭐ 由配对得到转移对（FCA 的对象集） -/

/-- **转移对**：一个「前状态—后状态」的二元组。 -/
abbrev Transition (X : StateSpace) : Type _ := X.Carrier × X.Carrier

/-- ⭐ **由配对与轨迹，得到转移对的集合**。

**这个集合正是 FCA 的对象集** —— 每个转移对是一个「对象」。 -/
def transitions (P : Pairing ι) (γ : ι → X.Carrier) : Set (Transition X) :=
  { t | ∃ n m : ι, P.rel n m ∧ γ n = t.1 ∧ γ m = t.2 }

/-- **转移对来自配对**（成员性刻画）。 -/
theorem mem_transitions_iff (P : Pairing ι) (γ : ι → X.Carrier) (a b : X.Carrier) :
    (a, b) ∈ transitions P γ ↔ ∃ n m : ι, P.rel n m ∧ γ n = a ∧ γ m = b :=
  Iff.rfl

/-! ### §0.3 转移对的属性（FCA 的属性侧） -/

/-- **前态属性**：转移对的第一个分量落在 `A` 里。 -/
def preAttr (A : Set X.Carrier) : Transition X → Prop :=
  fun t => t.1 ∈ A

/-- **后态属性**：转移对的第二个分量落在 `B` 里。 -/
def postAttr (B : Set X.Carrier) : Transition X → Prop :=
  fun t => t.2 ∈ B

/-- ⭐ **一条转移规则**（FCA 意义上的蕴含）：
**所有前态满足 `A` 的转移，后态都满足 `B`。**

**这是「配对 → FCA → 规则」链上最关键的连接点。** -/
def TransRule (A B : Set X.Carrier) : Set (Transition X) → Prop :=
  fun S => ∀ t ∈ S, preAttr A t → postAttr B t

/-! ### §0.4 基本性质 -/

/-- **全属性规则恒真**（后态满足全空间，平凡）。 -/
theorem transRule_top (A : Set X.Carrier) (S : Set (Transition X)) :
    TransRule A Set.univ S :=
  fun _ _ _ => trivial

/-- **空前件的规则恒真**（没有前态满足 `∅`）。 -/
theorem transRule_empty_pre (B : Set X.Carrier) (S : Set (Transition X)) :
    TransRule ∅ B S :=
  fun _ _ h => absurd h (by simp [preAttr])

/-- **规则的单调性（前件收缩）**：若 `A' ⊆ A` 且 `TransRule A B S`，
则 `TransRule A' B S`。

**即：前件越窄，规则越弱** —— 这对应 `γ`（泛化）的方向。 -/
theorem transRule_mono_pre {A A' B : Set X.Carrier} {S : Set (Transition X)}
    (h : A' ⊆ A) (hr : TransRule A B S) : TransRule A' B S :=
  fun t ht hpre => hr t ht (h hpre)

/-- **规则的单调性（后件扩张）**：若 `B ⊆ B'` 且 `TransRule A B S`，
则 `TransRule A B' S`。

**即：后件越宽，规则越弱** —— 同样对应泛化。 -/
theorem transRule_mono_post {A B B' : Set X.Carrier} {S : Set (Transition X)}
    (h : B ⊆ B') (hr : TransRule A B S) : TransRule A B' S :=
  fun t ht hpre => h (hr t ht hpre)

end Pairing

end FateV2.Model