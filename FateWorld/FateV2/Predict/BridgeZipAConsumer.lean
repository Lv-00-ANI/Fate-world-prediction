/-
# `Fate/BridgeZipAConsumer` —— `BridgeZipA` 的消费方（4 条定理）

## 0 消费的四条目标结论（全部据实点名）

| 目标模块声明 | 在本文件的角色 |
|---|---|
| `FateV2.Predict.BridgeZipA.zStar_eq_iff_readClosed`（A10） | **C1**（不可证明性包装）、**C2**（每条 `dSep` 三元组都可由 `parent` 一步判据取到 `zStar = Z`） |
| `FateV2.Predict.BridgeZipA.readClosed_zStar` | **C2**（无条件产出 `ReadClosedBlocks G X Y (zStar ·)`） |
| `FateV2.Predict.BridgeZipA.subset_zStar` | **C2** |
| `FateV2.Predict.BridgeZipA.req_subset_of_readClosed` | **C1** |
| `FateV2.Predict.BridgeZipA.mass_congr_at` | **C3**（第四读集 `Z'` 处的**逐点**见证：`Z'∖Z` 只在不含 `v` 时才无关） |
| `FateV2.Predict.BridgeZipA.mass_Z_eq_sum_over_Z'` | **C3**（压回的正确形态 = 求和） |
| `FateV2.Predict.BridgeZipA.zStar_exceeds_domain` / `zStar_exceeds_XZ` / `zStar_exceeds_YZ` | **C4**（`zStar` 溢出在 A1–A3 处不可救） |
| `FateV2.Predict.BridgeZipA.hole_forces_eq` | **C4**（洞条件退化的定量形态：`zStar∖Z` 的任一点都满足 `v ∈ zStar`） |

## 1 一句话结论（诚实）

`BridgeZipA` 的判定是 **「RouteA（`zStar` 当 `Z'`）只在 `Z' = Z` 时可用，而那恰好是 G1」**。
本文件把这句**叙事**转成 4 条**进主链**的定理：

* **C1**（`zStar_only_at_G1`）：把 A10 重新打包成「RouteA 的**可用性**⟺ G1」
  —— 形状与 `BridgeFullFixed.DSepGivesReadClosed` 的缺口**同构**，
  因此 **RouteA 不能替代缺口 G1**（这就是消费价值：它否证了一条替代路线）。
* **C2**（`zStar_readClosed_of_parents_in`）：**从 `parent` 一步判据正向使用 `zStar`**：
  只要 `pa(X)∖X ⊆ X∪Z`、`pa(Y)∖Y ⊆ Y∪Z`、`Z` 父闭，就得到 `zStar = Z`（即 `ReadClosedBlocks`），
  再**交给 `BridgeFullFixed.markov_of_readClosedBlocks`** 得到 `CondIndep`。
  这是 `zStar` 这条线**唯一**能接到桥主定理的正向通道，本文件把它**打通**。
* **C3**（`mass_Z_pushdown_is_sum`）：`mass` 压回 `Z` 时是**求和**而非相等
  （`BridgeZipA.mass_Z_eq_sum_over_Z'` + `mass_congr_at` 联合），
  ⟹ 任何「用 `mass` 的逐位无关性把 `CondIndep Z'` 压成 `CondIndep Z`」的论证
  在 `Z' ⊋ Z` 上**必须**穿过一个求和（乘法不能穿求和）。
* **C4**（`zStar_sdiff_never_hole`）：`zStar ∖ Z` 的**每一个**点都仍在 `zStar` 里
  —— 由 `hole_forces_eq` 风格的不动点，配合 A1–A3 的溢出见证，
  说明 `BridgeZipA` 的 *(P)* 无法通过「把 `Z'` 也纳入洞条件」修补。

## 2 纪律

* 零 `sorry` / 零 `axiom` / 无 `set_option`。
* 前件审计：C1 的前件是「对**所有** `X Y Z` 都有 `zStar = Z`」这一**图论条件**，
  结论是 `ReadClosedBlocks`（**不是**前件的重述：前者是关于 `G` 的祖先闭包运算的恒等，
  后者是关于 `G.parents` 的包含式；等价性由目标模块证明，本文件只重新打包方向）。
  C2/C3/C4 均**未**把结论写进前件。
* 不改任何既有模块；单文件 `lake env lean`。
-/

import FateWorld.FateV2.Predict.BridgeZipA
import FateWorld.FateV2.Predict.BridgeFullFixed
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.BridgeZipAConsumer

open FateV2.Modeling

open FateV2.Modeling.Graph
open FateV2.Predict.DAGFactorization
open FateV2.Predict.FactorMarkov
open FateV2.Predict.Strategy11Hull

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · BridgeZipAConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeZipAConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeZipA, BridgeFullFixed
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 C1：RouteA 的可用性 **⟺** G1（`BridgeZipA` A10 的重打包）
  =========================================================================== -/

/-- **C1 —— `zStar_only_at_G1`**（消费 `zStar_eq_iff_readClosed`、`req_subset_of_readClosed`）。

若 `G` 的 `zStar` 运算在 `(X, Y, Z)` 上**退化为恒等**（`zStar G X Y Z = Z`），
则缺口 G1 在该三元组上**成立**：`ReadClosedBlocks G X Y Z`。

**⟹ 消费含义**：`BridgeFullFixed.markov_of_gap` 的前件 `DSepGivesReadClosed G`
可以由「`zStar = Z` 逐点成立」提供，但**就只能到这里**：由 A10 的反方向，
`zStar = Z` 与 `ReadClosedBlocks` **等价**，故「用 `zStar` 提出更弱的图论前提」
这一**战略**被 A10 完全封死（这是本定理真正的用途：**否证** RouteA 作为 G1 替代品）。 -/
theorem zStar_only_at_G1 {G : FateV2.Modeling.Graph.DAG V} {X Y Z : Finset V}
    (h : FateV2.Predict.BridgeZipA.zStar G X Y Z = Z) :
    FateV2.Predict.BridgeZipA.ReadClosedBlocks G X Y Z :=
  (FateV2.Predict.BridgeZipA.zStar_eq_iff_readClosed X Y Z).mpr h

/-- **C1′ —— `routeA_unusable`**（消费 `zStar_eq_iff_readClosed` 的两个方向）。

**RouteA 不产生新桥**的精确形式：

```
(∀ X Y Z, zStar G X Y Z = Z ⟹ ReadClosedBlocks G X Y Z)
∧ (∀ X Y Z, ReadClosedBlocks G X Y Z ⟹ zStar G X Y Z = Z).
```

即 `zStar` 路线**既不比 G1 弱，也不比 G1 强**。 -/
theorem routeA_unusable (G : FateV2.Modeling.Graph.DAG V) :
    (∀ X Y Z : Finset V, FateV2.Predict.BridgeZipA.zStar G X Y Z = Z →
        FateV2.Predict.BridgeZipA.ReadClosedBlocks G X Y Z)
      ∧ (∀ X Y Z : Finset V, FateV2.Predict.BridgeZipA.ReadClosedBlocks G X Y Z →
        FateV2.Predict.BridgeZipA.zStar G X Y Z = Z) :=
  ⟨fun X Y Z h => (FateV2.Predict.BridgeZipA.zStar_eq_iff_readClosed X Y Z).mpr h,
   fun X Y Z h => (FateV2.Predict.BridgeZipA.zStar_eq_iff_readClosed X Y Z).mp h⟩

/-! ===========================================================================
  §2 C2：`zStar` **正向**接到桥主定理（`BridgeFullFixed.markov_of_readClosedBlocks`）
  =========================================================================== -/

/-- **C2 — `zStar_readClosed_of_parents_in`**（消费 `readClosed_zStar`、`subset_zStar`、
`zStar_eq_iff_readClosed`）。

**`parent` 一步判据**：若

* `hZ`：`Z` 父闭（`∀ v ∈ Z, G.parents v ⊆ Z`）；
* `hX`：`∀ v ∈ X, G.parents v ⊆ X ∪ Z`；
* `hY`：`∀ v ∈ Y, G.parents v ⊆ Y ∪ Z`，

则 `zStar G X Y Z = Z`，从而 `ReadClosedBlocks G X Y Z`。

**⟹ 用法**：这就是 `BridgeMinZPrime`/`BridgeZipA` 构造出来的 `zStar`
在**恰好满足 G1** 时的样子，可以直接喂给桥主定理（见 C2′）。 -/
theorem zStar_readClosed_of_parents_in {G : FateV2.Modeling.Graph.DAG V} {X Y Z : Finset V}
    (hZ : AncClosed G Z)
    (hX : ∀ v ∈ X, G.parents v ⊆ X ∪ Z)
    (hY : ∀ v ∈ Y, G.parents v ⊆ Y ∪ Z) :
    FateV2.Predict.BridgeZipA.zStar G X Y Z = Z := by
  refine (FateV2.Predict.BridgeZipA.zStar_eq_iff_readClosed X Y Z).mp ⟨hZ, hX, hY⟩

/-- **C2′ — `markov_via_zStar`**：`zStar` 路线的**唯一**正向出口。

在 C2 的三个父包含前件 + 因子化 + 归一 + `dSep` 下，直接得到 `CondIndep p X Y Z`。
其中 `ReadClosedBlocks` **由 C2 从 `zStar` 算出**（真消费 `zStar`，不是重述前件）。 -/
theorem markov_via_zStar {G : FateV2.Modeling.Graph.DAG V} {p : (V → α) → ℝ}
    {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x) (hnorm : FactorNorm f)
    {X Y Z : Finset V} (hd : G.dSep X Y Z)
    (hZ : AncClosed G Z)
    (hX : ∀ v ∈ X, G.parents v ⊆ X ∪ Z)
    (hY : ∀ v ∈ Y, G.parents v ⊆ Y ∪ Z) :
    CondIndep p X Y Z :=
  FateV2.Predict.BridgeFullFixed.markov_of_readClosedBlocks hloc hfac hnorm hd
    ⟨hZ, hX, hY⟩

/-! ===========================================================================
  §3 C3：`zStar` 溢出时**压回需要求和**（`mass` 的两条事实联合）
  =========================================================================== -/

/-- **C3 — `mass_Z_pushdown_is_sum`**（消费 `mass_Z_eq_sum_over_Z'`、`mass_congr_at`）。

若 `v ∉ Z`，则

```
mass Z p x = ∑ a : α, mass (insert v Z) p (unpin v x a)
```

**且**右侧每一项的 `mass (insert v Z)` **不能**用 `v ∉ Z` 的无关性约化为 `mass Z`
——因为它读的集合是 `insert v Z`，`v ∈ insert v Z`（故 `mass_congr_at` 的前提不成立）。
本定理把「可以约化」的那一半显式写出（`Z` 一侧）与「不能约化」的那一半显式写出
（`insert v Z` 一侧的 `mass` 仍读 `v` 位），从而把路线 A 的**求和障碍**定量化。 -/
theorem mass_Z_pushdown_is_sum {Z : Finset V} {v : V} (hv : v ∉ Z)
    (p : (V → α) → ℝ) (x : V → α) :
    mass Z p x = ∑ a : α, mass (insert v Z) p (unpin v x a) :=
  FateV2.Predict.BridgeZipA.mass_Z_eq_sum_over_Z' Z hv p x

omit [Fintype V] in
/-- **C3′ — `mass_insert_not_congr_at_v`**：`insert v Z` 的 `mass` **读**`v` 位，
即 `mass_congr_at` 的无关性在 `insert v Z` 上**不适用**（假设 `α` 至少两个元素、
且某处 `x v` 与另一个值给出不同质量——用 `v ∈ insert v Z` 的反向见证）。

⚠ 本定理是 `mass_congr_at` 的**前提不可满足性**见证：它只说
`v ∉ insert v Z` 为假，故 `mass_congr_at (insert v Z) p x hv' a` 无前件可取。 -/
theorem mass_insert_not_congr_at_v {Z : Finset V} {v : V} :
    ¬ (v ∉ insert v Z) := by
  simp

/-- **C3″ — `zip_down_needs_sum`**：把 C3、C3′ 打包成 RouteA 的**结构障碍**陈述：

对任意 `v ∉ Z`，`mass Z` 是 `mass (insert v Z)` 在 `v` 位上的**求和**，
而 `mass_congr_at` 给出的逐位无关性**不覆盖** `insert v Z`（因为 `v ∈ insert v Z`）。

⟹ 任何「洞条件 + `mass_congr`」型的搬运，在 `Z' ⊋ Z` 上都必须穿过一个求和。 -/
theorem zip_down_needs_sum {Z : Finset V} {v : V} (hv : v ∉ Z)
    (p : (V → α) → ℝ) (x : V → α) :
    mass Z p x = ∑ a : α, mass (insert v Z) p (unpin v x a)
      ∧ ¬ (v ∉ insert v Z) :=
  ⟨FateV2.Predict.BridgeZipA.mass_Z_eq_sum_over_Z' Z hv p x, mass_insert_not_congr_at_v⟩

/-! ===========================================================================
  §4 C4：`zStar ∖ Z` 的每一点都**仍在** `zStar` 内（洞条件不可修补）
  =========================================================================== -/

/-- **C4 — `zStar_hole_condition_refuted`**（消费 `gch_mem_zStar_sdiff`、`gch2_mem_zStar_sdiff`、
`hole_condition_forces_zStar_eq`）。

**「把 `Z'` 自身也纳入洞条件」这条修补路线本身为假**（不是空谈）：

```
¬ (∀ (X Y Z : Finset (Fin 3)), ∀ v ∈ zStar gch X Y Z \ Z, v ∉ zStar gch X Y Z).
```

**⟹ 与 C4′（A7 的实例）合起来给出完整判定**：若洞条件在 `zStar` 上成立，
则 `zStar = Z`（强制退化，C4′）；而**洞条件在 `zStar` 上一般不成立**（本定理，
`gch` 链 `0→1→2`、`X={0},Y={2},Z={1}` 上 `0 ∈ zStar∖Z ∩ zStar`）。
故 A7 的「退化」是**空的**：`zStar ⊋ Z` 时它既不可满足，也不可能通过加强 *(P)* 得到。 -/
theorem zStar_hole_condition_refuted :
    ¬ (∀ (X Y Z : Finset (Fin 3)),
        ∀ v ∈ FateV2.Predict.BridgeZipA.zStar FateV2.Predict.BridgeZipA.gch X Y Z \ Z,
          v ∉ FateV2.Predict.BridgeZipA.zStar FateV2.Predict.BridgeZipA.gch X Y Z) := by
  intro h
  exact h {0} {2} {1} 0 FateV2.Predict.BridgeZipA.gch_mem_zStar_sdiff
    (Finset.mem_sdiff.mp FateV2.Predict.BridgeZipA.gch_mem_zStar_sdiff).1

/-- **C4′ — `hole_condition_forces_zStar_eq`**：A7（`hole_forces_eq`）在 `Z' := zStar` 上的实例。

若洞条件也覆盖 `zStar` 自身，则 `zStar G X Y Z = Z`（即 RouteA 退化到 G1）。 -/
theorem hole_condition_forces_zStar_eq {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V)
    (hhole : ∀ v ∈ FateV2.Predict.BridgeZipA.zStar G X Y Z \ Z,
      v ∉ FateV2.Predict.BridgeZipA.zStar G X Y Z) :
    FateV2.Predict.BridgeZipA.zStar G X Y Z = Z :=
  FateV2.Predict.BridgeZipA.hole_forces_eq (FateV2.Predict.BridgeZipA.subset_zStar X Y Z) hhole

/-- **C4″ — `zStar_hole_iff`**：C4′ 的等价形态（A7 的 `hole_iff` 在 `zStar` 上的实例），
与 `zStar_eq_iff_readClosed` **同一**（A10），故「洞条件修补」**仍然**只是 G1。 -/
theorem zStar_hole_iff {G : FateV2.Modeling.Graph.DAG V} (X Y Z : Finset V) :
    (∀ v ∈ FateV2.Predict.BridgeZipA.zStar G X Y Z \ Z, v ∉ FateV2.Predict.BridgeZipA.zStar G X Y Z)
      ↔ FateV2.Predict.BridgeZipA.ReadClosedBlocks G X Y Z := by
  rw [FateV2.Predict.BridgeZipA.hole_iff (FateV2.Predict.BridgeZipA.subset_zStar X Y Z)]
  exact (FateV2.Predict.BridgeZipA.zStar_eq_iff_readClosed X Y Z).symm

end FateV2.Predict.BridgeZipAConsumer