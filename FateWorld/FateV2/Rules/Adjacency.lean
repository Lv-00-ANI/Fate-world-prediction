import FateWorld.FateV2.Rules.TrajPattern
/-!
  # Rules · Adjacency

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Adjacency.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TrajPattern
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  紧邻性：不预设索引结构，只要求「先于」关系（作者：靠后续实际决定）

  **裁决来源**：作者原话「不知道这个只能靠后续实际情况来」

  ## 设计原则

  **不规定 `ι` 是什么**（是 `ℕ`？稠密序？还是别的），
  **只要求提供一个「先于」关系 `lt : ι → ι → Prop`。**

  **「紧邻」由 `lt` 定义**（不单独引入 `succ`）：
  $$\mathrm{Adjacent}\ n\ m := \mathrm{lt}\ n\ m \wedge \neg\exists k,\ \mathrm{lt}\ n\ k \wedge \mathrm{lt}\ k\ m$$

  ## 为什么这样好

  | 情形 | 填什么 `lt` | `Adjacent` 变成 |
  |---|---|---|
  | `ι = ℕ`（时间） | `(· < ·)` | **`m = n+1`** |
  | 同一试验内的数据 | 只在同试验内成立 | 试验内的相邻 |
  | **稠密序**（`ℚ` 型）| `(· < ·)` | **恒假** |

  ## 一个副产品（重要）

  **稠密序上 `Adjacent` 恒假 ⟹ 「相邻规则」不存在，但「先后规则」仍成立。**

  **⟹ 这不是实现缺陷，是数学必然** ——
  **它解释了为什么某些数据只能抽「先后规律」而不能抽「转移规则」。**

  ## 诚实边界

  * `lt` 是**参数**，不是既定的。填什么取决于实际数据。
  * 本节**不证明**「轨迹级 + 紧邻 ⟹ 转移级」的完整细化定理（仅证 `Adjacent → lt`）。
  =========================================================================== -/

namespace FateV2.Rules
namespace Adjacency

variable {ι : Type u}

/-- **紧邻**：`m` 是 `n` 的紧后继（无中间元）。

**不引入 `succ`** —— 只由「先于」关系 `lt` 定义。 -/
def Adjacent (lt : ι → ι → Prop) (n m : ι) : Prop :=
  lt n m ∧ ¬ ∃ k : ι, lt n k ∧ lt k m

/-- **紧邻蕴含先于**（细化方向：相邻比先后强）。 -/
theorem adjacent_implies_lt {lt : ι → ι → Prop} {n m : ι}
    (h : Adjacent lt n m) : lt n m :=
  h.1

/-- ⭐ **在 `ℕ` 上，紧邻 ⟺ 后继**（验证定义正确性）。

这是关键的正确性检验：我们的抽象定义在标准情形下必须退化正确。 -/
theorem adjacent_nat_iff_succ (n m : ℕ) :
    Adjacent (· < ·) n m ↔ m = n + 1 := by
  constructor
  · intro ⟨hlt, hno⟩
    -- `n < m`，且 `n` 与 `m` 之间无元素 ⟹ `m = n + 1`
    have hnm : n < m := hlt
    by_contra hne
    -- 若 `m ≠ n+1`，则 `n+1 < m`（因为 `n < m` 且 `m ≠ n+1`）
    have h1 : n + 1 < m := by omega
    -- 那么 `n < n+1` 且 `n+1 < m`，与「无中间元」矛盾
    exact hno ⟨n + 1, by omega, h1⟩
  · intro h
    subst h
    refine ⟨by omega, ?_⟩
    -- `n` 与 `n+1` 之间无自然数
    rintro ⟨k, h1, h2⟩
    omega

/-- ⭐ **在稠密序上紧邻恒假**（如 `ℚ`）。

**⟹ 稠密索引的数据抽不出「相邻规则」，只能抽「先后规则」** ——
这是数学必然，不是实现缺陷。 -/
theorem adjacent_rat_false (n m : ℚ) : ¬ Adjacent (· < ·) n m := by
  rintro ⟨hlt, hno⟩
  -- `ℚ` 稠密：`n < m` ⟹ 存在 `k` 严格居中
  have h : ∃ k : ℚ, n < k ∧ k < m := exists_between hlt
  exact hno h

/-- **退化情形：空关系下紧邻恒假**（没有「先于」就没有「相邻」）。 -/
theorem adjacent_empty (n m : ι) : ¬ Adjacent (fun _ _ => False) n m :=
  fun h => h.1

/-- **全关系下紧邻也恒假**（所有东西互相「先于」时，没有紧邻）。 -/
theorem adjacent_universal (n m : ι) [Nonempty ι] :
    ¬ Adjacent (fun _ _ => True) n m := by
  rintro ⟨-, hno⟩
  obtain ⟨k⟩ := ‹Nonempty ι›
  exact hno ⟨k, trivial, trivial⟩

/-! ### §0.1 小结：相邻比先后强 -/

/-! **细化方向总结**（本节的结论）：

* `Adjacent lt` **蕴含** `lt`（`adjacent_implies_lt`）—— 相邻 ⟹ 先后
* 反之**不成立**（稠密序的反例：`adjacent_rat_false`）

**⟹ 这意味着：**
* 若数据能给出「相邻」（如 `ι = ℕ`），**可抽转移规则**
* 若只能给出「先后」（稠密索引），**只能抽轨迹级规律**
* **两种情形都不是缺陷，是索引结构决定的** -/

end Adjacency

end FateV2.Rules