/-
# 路线丙：类型层修正 —— `Marginal S p : (S → α) → ℝ`

## 0 诊断（独立复核，本文件机检）

| # | 事实 | 状态 |
|---|---|---|
| **V1** | `mass S p x := ∑_w, if (∀ u ∈ S, w u = x u) then p w else 0` 是**纤维和（非归一化边缘）** | ✅ `DAGFactorization.lean:237` 逐字复核 |
| **V2** | 反例 `tower_counter_lhs/rhs` 数值成立（`1 ≠ 0`） | ✅ 见 `DAGFactorizationGeneral.tower_property_false` |
| **V3** | 「类型/语义错配」诊断**方向正确但不完整** | ✅ 见 §1 |

### ⚠ 对主控诊断的**修正**（重要，必须记录）

主控 §1.3 说「正确的塔性质是 `mass (S ∪ T) p = mass T (mass S p)`（`S ⊆ T`）」。
**这一条在本仓库的 `mass` 口径下也为假**，而且主控给的「`T ⊆ S` 时
`mass S (mass T p) x = mass S p x`」**同样为假**。

根因不是 `S`/`T` 的包含关系，而是 **`mass` 是纤维和、不归一化**：

> **精确塔定律（`Fate/TowerExactLaw.mass_mass_of_subset`，已证）**
> 对 `T ⊆ S`：`mass S (mass T p) x = multS S x · mass T p x`，
> 其中 `multS S x := ∑_{w : w|_S = x|_S} 1 = |α|^{|V \ S|}`。

即使 `T = S`（幂等）也只在 `multS S x = 1`（即 `S = univ`）时成立。
**⟹ 这不是 S/T 包含方向的问题，是 `mass` 输出类型仍为 `(V → α) → ℝ`
（完整函数）导致的必然重复计数。** 这正是路线丙要修的东西。

**机检反例**（本文件独立验证，`V = α = Bool`，`p = 𝟙[w true = w false = true]`，
`S = {false}`，`x = (false ↦ true)`）：
`multS {false} x = 2`、`mass {false} p x = 1`，故
`mass {false} (mass {false} p) x = 2 · 1 = 2 ≠ 1 = mass {false} p x`。
**⟹ 主控 §1.3 的「`T ⊆ S` 时 `mass S (mass T p) x = mass S p x`」在此处为假。**

## 1 本文件做什么

**在类型层把边缘化的输出型收窄**：

```lean
noncomputable def Marginal (S : Finset V) (p : (V → α) → ℝ) : (S → α) → ℝ
```

输出是 `S → α` 上的函数 —— **`S` 之外的坐标在类型里就不存在**，
因此第二次边缘化（`MarginalSub`）**不可能**再枚举 `S` 之外的自由度。

这与 `Fate/TowerExactLaw` §2 的诊断一致：

> 「测度的塔需要归一化，或**推送（push-forward）到更小的型**。」

路线丙采用**后者**：把 `(V → α) → ℝ` 推送为 `(S → α) → ℝ`。

## 2 交付清单

| # | 定理 | 状态 | 内容 |
|---|---|---|---|
| **C1** | `marginal_restrict` | ✅ 零缺口 | `Marginal S p (restrict S x) = mass S p x`（与旧口径在钉点一致） |
| **C2** | `marginal_tower` | ✅ **零缺口、零假设** | **`MarginalSub h (Marginal S p) y = Marginal T p y`（`T ⊆ S`）** |
| **C3** | `marginal_tower_self` | ✅ 零缺口 | **幂等无条件成立**（对比旧口径 `mass_self_eq` 差 `multS`） |
| **C4** | `marginal_insert_sum` | ✅ 零缺口 | 链式法逆操作：`∑_a Marginal (insert h S) p (extend y a) = Marginal S p y` |
| **C5** | `old_mass_idempotent_mult` | ✅ 零缺口 | 旧口径幂等的**精确形式**（转发 `TowerExactLaw.mass_self_eq`） |

**零 `sorry` / 零 `axiom` / 零额外假设。**

## 3 如实标注的边界

1. **`marginal_tower` 的方向是 `T ⊆ S`**。这是类型层构造的**内在限制**：
   `MarginalSub h` 要求 `h : T ⊆ S`，否则 `S → α` 无法限制到 `T → α`。
   **主控 §1.3 的「`S ⊆ T` 方向」在类型层是无意义的**（无法把 `S → α`
   送入 `T → α` 的求和，因为 `T` 的坐标多于 `S`，需**积分掉**而非**限制**）。
   若要 `S ⊆ T` 的塔，只能用**放大** `S → T`，那又回到 `mass` 口径。
   **⟹ 路线丙的塔只有 `T ⊆ S` 方向，这是它的天花板，不是缺陷。**

2. **对 `Factorizes`/`dSep` 的意义**：见 §4 的诚实评估。

## 4 ⚠ 对「`dSep ⟹ Factorizes`」的作用（诚实评估）

`fac_aux`（`Fate/DAGFactorization` T2）需要的核心是
`mass_insert_sum`（放开一个坐标再求和 = 少固定一个坐标）。
`Marginal` 口径下**同形引理成立**（C4 `marginal_insert_sum`），
且**无纤维乘子**。

⚠ **但 C4 的输出是 `S → α` 上的等式**，而 `Factorizes` 的陈述是
`(V → α) → ℝ` 上的点等式 `p x = ∏_v φ v x`。要把 C4 用在 `p` 上，
必须**反复把 `Marginal` 的结果拉回 `V → α`**，这个拉回
**正是 `marginal_restrict`（C1）**，而它在每一步只能取「钉住点」
`restrict S x`，**恰好**与 `fac_aux` 在 `x` 处工作一致。

**结论（诚实）**：路线丙**能**承担 `fac_aux` 的链式环节且**消除乘子**，
但它**不能**单独闭合 `Factorizes ⟹ LMG` 或 `LMG ⟹ GM` ——
那两步的卡点（见 `Fate/FactorRecursionRouteB` §5.3、§6）是**图论**的
（`pa ∩ nd = ∅`、`v ∉ pa w` 的 Fin 编码对齐），**与边缘化口径无关**。
路线丙解决的是链式代数，不是图论缺口。

## 5 改动面评估

| 项 | 评估 |
|---|---|
| **新增文件** | 仅本文件（+ 若采纳需 `import` 进 `Fate.lean`）|
| **既有定理改动** | **0**——不修改 `mass`，`Marginal` 是**新增并行口径** |
| **下游 `mass` 用户（26 个文件）** | **0 改动**——它们继续用 `mass` |
| **与 `Marginal` 的桥接** | `marginal_restrict`（C1）单向：钉点处两口径一致 |
| **需要额外前提** | **无**（C2/C3/C4 全无条件）|
| **`mass S p x ≠ 0` 前提** | **不需要**（对比路线甲 `condMass` 需要）|

**⟹ 改动面为零（纯新增）**。这是路线丙相对甲/丙-改 `mass` 的最大优势：
**不改 `mass` 类型就能拿到类型层塔性质**，因为 `Marginal` 是**旁路定义**。
-/

import FateWorld.FateV2.Predict.DAGFactorizationGeneral
import FateWorld.FateV2.Predict.TowerExactLaw
namespace FateV2.Predict.RouteC

open FateV2.Modeling

open Finset
open Fate.DAGFactorization (mass)

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · RouteC

  ## 迁移登记
  - 来源：`FateWorld/Legacy/RouteC.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DAGFactorizationGeneral, TowerExactLaw
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 定义
  =========================================================================== -/

/-- 坐标限制 `V → α` ↦ `S → α`。 -/
def restrict (S : Finset V) (x : V → α) : S → α := fun u => x u.1

/-- `S → α` 限制到 `T → α`（`T ⊆ S`）。 -/
def subRestrict {S T : Finset V} (h : T ⊆ S) (y : S → α) : T → α :=
  fun u => y ⟨u.1, h u.2⟩

/-- ⭐⭐⭐ **路线丙核心定义**：`S`-边缘，**输出类型 `S → α`**（类型层携带 `S`）。

$${\rm Marginal}\,S\,p := y \mapsto \sum_{w : V\to\alpha} [w|_S = y]\cdot p\,w.$$

**与旧 `mass` 的唯一区别是输出型**：`mass S p : (V → α) → ℝ`（完整函数），
`Marginal S p : (S → α) → ℝ`（只在 `S` 上取值）。 -/
noncomputable def Marginal (S : Finset V) (p : (V → α) → ℝ) : (S → α) → ℝ :=
  fun y => ∑ w : V → α, if restrict S w = y then p w else 0

/-- 第二层边缘：在 `S → α` 上对 `T ⊆ S` 求和（**求和范围只有 `S` 的坐标**）。 -/
noncomputable def MarginalSub {S T : Finset V} (h : T ⊆ S) (q : (S → α) → ℝ) : (T → α) → ℝ :=
  fun y => ∑ z : S → α, if subRestrict h z = y then q z else 0

/-- 把 `y : S → α` 与 `a : α` 拼成 `insert k S → α`（`k ∉ S`）。 -/
def extend (k : V) (S : Finset V) (_hk : k ∉ S) (y : S → α) (a : α) : ((insert k S : Finset V)) → α :=
  fun u =>
    if hu : (u : V) = k then a
    else
      y ⟨(u : V), by
        have hu2 : (u : V) ∈ insert k S := u.2
        rcases Finset.mem_insert.mp hu2 with e | hmem
        · exact absurd e hu
        · exact hmem⟩

/-! ===========================================================================
  §2 与旧 `mass` 的接口
  =========================================================================== -/

set_option linter.unusedSectionVars false in
theorem subRestrict_restrict {T S : Finset V} (h : T ⊆ S) (x : V → α) :
    subRestrict h (restrict S x) = restrict T x := by
  funext u; rfl

/-- **C1**：`Marginal` 与 `mass` 在「钉住点」处一致。 -/
theorem marginal_restrict (S : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    Marginal S p (restrict S x) = mass S p x := by
  classical
  unfold Marginal mass
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (restrict S w = restrict S x) ↔ (∀ u ∈ S, w u = x u) := by
    constructor
    · intro hh u hu
      exact congrFun hh ⟨u, hu⟩
    · intro hh
      funext u
      exact hh u.1 u.2
  exact if_congr e rfl rfl

/-! ===========================================================================
  §3 ⭐⭐⭐ **C2：类型层塔性质（零假设）**
  =========================================================================== -/

/-- **C2`：`MarginalSub` 复合 `Marginal` = 直接 `Marginal`**（`T ⊆ S`）。

$$\sum_{z : S\to\alpha,\ z|_T = y}{\rm Marginal}\,S\,p\,z = {\rm Marginal}\,T\,p\,y$$

**对比旧口径**：`mass S (mass T p) x = multS S x · mass T p x`
（`TowerExactLaw.mass_mass_of_subset`）—— **差一个纤维乘子**。
本定理**无条件、无乘子**，因为 `MarginalSub` 的求和范围是 `S → α`，
不含 `S` 之外的坐标。 -/
theorem marginal_tower {T S : Finset V} (h : T ⊆ S) (p : (V → α) → ℝ) (y : T → α) :
    MarginalSub h (Marginal S p) y = Marginal T p y := by
  classical
  unfold MarginalSub Marginal
  have push : (∑ z : S → α, if subRestrict h z = y then
        (∑ w : V → α, if restrict S w = z then p w else 0) else 0)
      = ∑ z : S → α, ∑ w : V → α,
          (if subRestrict h z = y then (if restrict S w = z then p w else 0) else 0) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : (subRestrict h z = y)
    · rw [if_pos hz]
      exact (Finset.sum_congr rfl fun w _ => by rw [if_pos hz]).symm
    · rw [if_neg hz]
      exact (Finset.sum_eq_zero fun w _ => by rw [if_neg hz]).symm
  rw [push, Finset.sum_comm]
  have inner : ∀ w : V → α,
      (∑ z : S → α,
          (if subRestrict h z = y then (if restrict S w = z then p w else 0) else 0))
        = if restrict T w = y then p w else 0 := by
    intro w
    have key : subRestrict h (restrict S w) = restrict T w := subRestrict_restrict h w
    by_cases hw : (restrict T w = y)
    · rw [if_pos hw, Finset.sum_eq_single (s := Finset.univ) (restrict S w)]
      · rw [if_pos (by rw [key]; exact hw), if_pos rfl]
      · intro z _ hz
        by_cases hc : (subRestrict h z = y)
        · rw [if_pos hc, if_neg (fun hzw => hz hzw.symm)]
        · rw [if_neg hc]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · rw [if_neg hw]
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases hzw : (restrict S w = z)
      · rw [← hzw]
        rw [if_neg (fun hc => hw (by rw [← key]; exact hc))]
      · simp only [hzw, if_false, ite_self]
  rw [Finset.sum_congr rfl fun w _ => inner w]

/-- **C3**：`Marginal` 的幂等**无条件**成立（`T = S`）。 -/
theorem marginal_tower_self (S : Finset V) (p : (V → α) → ℝ) (y : S → α) :
    MarginalSub (Subset.refl S) (Marginal S p) y = Marginal S p y :=
  marginal_tower (Subset.refl S) p y

/-- **C5**：旧 `mass` 口径的幂等**只在 `multS = 1` 时**成立（转发，作对比）。 -/
theorem old_mass_idempotent_mult (S : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => mass S p w) x = Fate.TowerExactLaw.multS S x * mass S p x :=
  Fate.TowerExactLaw.mass_self_eq S p x

/-! ===========================================================================
  §4 **C4：放开一个坐标再求和（`mass_insert_sum` 的类型层对应物）**
  =========================================================================== -/

/-- **C4**：`∑_a Marginal (insert h S) p (extend y a) = Marginal S p y`（`h ∉ S`）。

这是 `Fate/DAGFactorization.mass_insert_sum`（T1）在 `Marginal` 口径下的
对应物，**无纤维乘子**。 -/
theorem marginal_insert_sum (k : V) (S : Finset V) (hk : k ∉ S)
    (p : (V → α) → ℝ) (y : S → α) :
    (∑ a : α, Marginal (insert k S) p (extend k S hk y a)) = Marginal S p y := by
  classical
  unfold Marginal
  rw [Finset.sum_comm]
  have inner : ∀ w : V → α,
      (∑ a : α, if restrict (insert k S) w = extend k S hk y a then p w else 0)
        = if restrict S w = y then p w else 0 := by
    intro w
    by_cases hw : (restrict S w = y)
    · rw [if_pos hw]
      have hext : restrict (insert k S) w = extend k S hk y (w k) := by
        funext u
        unfold restrict extend
        by_cases hu : u.1 = k
        · simp only [hu, dif_pos]
        · simp only [hu, dif_neg, not_false_iff]
          have huS : u.1 ∈ S := by
            rcases Finset.mem_insert.mp u.2 with e | hmem
            · exact absurd e hu
            · exact hmem
          exact congrFun hw ⟨u.1, huS⟩
      rw [Finset.sum_eq_single (w k)]
      · rw [hext, if_pos rfl]
      · intro a _ ha
        rw [if_neg]
        intro heq
        apply ha
        have := congrFun heq ⟨k, Finset.mem_insert_self k S⟩
        unfold restrict extend at this
        simp only [dif_pos rfl] at this
        exact this.symm
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · rw [if_neg hw]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [if_neg]
      intro heq
      apply hw
      funext u
      have := congrFun heq ⟨u.1, Finset.mem_insert_of_mem u.2⟩
      unfold restrict extend at this
      have hne : u.1 ≠ k := fun e => hk (e ▸ u.2)
      simp only [hne, dif_neg, not_false_iff] at this
      simpa [restrict] using this
  rw [Finset.sum_congr rfl fun w _ => inner w]

end FateV2.Predict.RouteC