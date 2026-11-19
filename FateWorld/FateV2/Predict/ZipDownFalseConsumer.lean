/-
# `Fate/ZipDownFalseConsumer` —— `ZipDownFalse` 的消费方（3 条真连接）


-/

import FateWorld.FateV2.Predict.ZipDownFalse
import FateWorld.FateV2.Predict.BridgeFullFixed
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.ZipDownFalseConsumer

open FateV2.Modeling

open FateV2.Predict.DAGFactorization
open FateV2.Predict.FactorMarkov
open FateV2.Predict.ZipDownFalseFixed
open FateV2.Predict.BridgeFullFixed
open FateV2.Predict.BridgeZipDown (gempty gempty_parents)
open FateV2.Predict.Strategy11Hull

/-!
  # Predict · ZipDownFalseConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ZipDownFalseConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ZipDownFalse, BridgeFullFixed
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 C1：`PjointB` 在空图上**不**满足全局 Markov 性
  =========================================================================== -/

/-- ⭐⭐ **C1 —— `not_markov_PjointB`**（消费 `not_condIndepB`）。

`gempty`（`BridgeZipDown` 的无边图）上 `{0}` 与 `{1}` 在 `∅` 下 d-分离
（`decide`），而 `PjointB`（`ZipDownFalse` 的混合反例联合律）在该三元组处
**不**满足 `CondIndep`（`not_condIndepB`）。

⟹ `PjointB` 不满足 `gempty` 的全局 Markov 性。

**消费含义**：`FateV2.Predict.FactorMarkov.Markov` 是主链的落点谓词，
`BridgeFullFixed.markov_of_gap_markov` 把它作为**结论**交付。本定理表明该结论
**不能**对 `PjointB` 成立 —— 即 `PjointB` 落在主链前件（归一化联合律）之外，
两边因此**必须**是不同对象，主链的 `hnorm` 前件在这里不可省。 -/
theorem not_markov_PjointB : ¬ Markov PjointB gempty := by
  intro hm
  have hd : gempty.dSep ({(0 : Fin 4)} : Finset (Fin 4)) ({(1 : Fin 4)} : Finset (Fin 4))
      (∅ : Finset (Fin 4)) := by decide
  exact not_condIndepB (hm _ _ _ hd)

/-! ===========================================================================
  §2 C2：`PjointB` 的**总质量不是 1**（`FactorNorm` 口径的排除）
  =========================================================================== -/

/-- ⭐ **C2.1 —— `PjointB_total_mass`**（消费 `mEmpty_val`）。

`∑_w PjointB w = 2`：由 `mass_empty` 把空集边缘化成总质量，
再由 `ZipDownFalse` 的 `mEmpty_val`（`mass ∅ PjointB x = 2`）取值。

（⚠ 该定理只是把两条既有引理接起来；它服务 C2.2 的 `≠ 1` 结论。） -/
theorem PjointB_total_mass : (∑ w : Fin 4 → Bool, PjointB w) = 2 := by
  have h := mEmpty_val (fun _ => true)
  rw [mass_empty] at h
  exact h

/-- ⭐⭐ **C2.2 —— `PjointB_total_mass_ne_one`**（消费 `mEmpty_val`）。

`PjointB` **不是**概率密度：总质量 `2 ≠ 1`。

**消费含义**：主链的 `FactorNorm`（`∀ v x, ∑_a f v (unpin v x a) = 1`）
是「局部归一」，其全局后果是总质量为 1；`PjointB` 总质量 `2` 故被排除。
这是 C2.3 的技术支点。 -/
theorem PjointB_total_mass_ne_one : (∑ w : Fin 4 → Bool, PjointB w) ≠ 1 := by
  rw [PjointB_total_mass]
  norm_num

/-! ===========================================================================
  §3 C3：主链 `markov_of_gap_markov` 在 `(PjointB, gempty)` 上**不可实例化**
  =========================================================================== -/

/-- ⭐ **C3.1 —— `gempty_DSepGivesReadClosed`**（`gempty` 无父代）。

`gempty` 无边 ⟹ `parents v = ∅` ⟹ `ReadClosedBlocks` 的三条**都是空真**，
故缺口 `DSepGivesReadClosed gempty` 成立。 -/
theorem gempty_ancClosed (Z : Finset (Fin 4)) : AncClosed gempty Z :=
  fun v _ => by rw [gempty_parents]; exact Finset.empty_subset _

/-- ⭐ **C3.2**：`gempty` 上 `ReadClosedBlocks` 无条件成立（三条子句全空真）。 -/
theorem gempty_readClosedBlocks (X Y Z : Finset (Fin 4)) :
    ReadClosedBlocks gempty X Y Z := by
  refine ⟨gempty_ancClosed Z, ?_, ?_⟩
  · intro v _
    rw [gempty_parents]
    exact Finset.empty_subset _
  · intro v _
    rw [gempty_parents]
    exact Finset.empty_subset _

/-- ⭐ **C3.3 —— `gempty_gap_holds`**：缺口 `DSepGivesReadClosed gempty` 成立。 -/
theorem gempty_gap_holds : FateV2.Predict.BridgeFullFixed.DSepGivesReadClosed gempty :=
  fun X Y Z _ => gempty_readClosedBlocks X Y Z

/-- ⭐⭐⭐ **C3（主定理）—— `no_factorization_cert_for_PjointB`**。

**不存在**因子族 `f` 同时满足主链 `markov_of_gap` 的三个概率前件
（`LocalTo` / 父节点因子化 / `FactorNorm`），**在 `gempty` 上对 `PjointB`**。

**证明**（三步，全部消费既有定理）：
1. 若存在这样的 `f`，由 C3.3（`DSepGivesReadClosed gempty`）与
   `FateV2.Predict.BridgeFullFixed.markov_of_gap_markov` 得 `Markov PjointB gempty`；
2. 但 C1（`not_markov_PjointB`，消费 `ZipDownFalse.not_condIndepB`）给出其否定；
3. 矛盾。

**⟹ 这是 `ZipDownFalse` 与主链的一次**真**对接**：
`markov_of_gap_markov` 的**结论**在 `PjointB` 上被 `ZipDownFalse` 的反例
直接反驳，因此其**前件**在 `PjointB` 上必有一个假 —— 本定理把「哪个」限定为
「三者至少一个假」，并把「空图 + 缺口成立」这一最有利情形也排除了
（`gempty` 上缺口**成立**，所以矛盾**只能**来自概率前件）。

⚠ 前件审计：本定理**没有**把结论写进前件 —— 前件是「存在 `f` 满足三条**关于 `f`**
的局部性/因子化/归一性条件」，结论是「这样的 `f` 不存在」。两者由
`markov_of_gap_markov`（一条**已证**的定理）加 C1（一条**关于 `PjointB` 的
具体否定**）经反证连接，不存在同义反复。 -/
theorem no_factorization_cert_for_PjointB :
    ¬ ∃ f : Fin 4 → (Fin 4 → Bool) → ℝ,
        LocalTo gempty f ∧
        (∀ x : Fin 4 → Bool, PjointB x = ∏ v, f v x) ∧
        FactorNorm f := by
  rintro ⟨f, hloc, hfac, hnorm⟩
  exact not_markov_PjointB
    (FateV2.Predict.BridgeFullFixed.markov_of_gap_markov hloc hfac hnorm gempty_gap_holds)

/-! ===========================================================================
  §4 C4：`ZipDown` 的失败**不可**由「换更小的 `X ∪ Y`」修补
  =========================================================================== -/

/-- ⭐⭐ **C4 —— `zipDown_false_sharp`**（消费 `zipDown_false` + `zipDown_def`）。

`¬ ZipDown PjointB {0} {1}` 的**展开形态**：存在 `Z ⊆ Z'` 使得
`CondIndep PjointB {0} {1} Z'` 成立而 `CondIndep PjointB {0} {1} Z` 失败。

**消费含义**：这是 `ZipDown` 失败的**见证三元组**，它说明
「把 `Z'` 处的条件独立压回 `Z`」在 `Z' ∖ Z = {2}`（**非空**）时失败。
与 `BridgeFullFixed.ReadClosedBlocks` 对照：那里的第 2/3 条要求
`parents ⊆ 块 ∪ Z`，即 `Z` **不能**随便扩大；`{2}` 恰是 `Y = {1}` 的父代
（在 `gz` 上）所在位置 —— 直接把 `Y` 的父代塞进 `Z'` 再压回 `Z` 的
「策略」被本条否证。

⚠ 前件审计：本定理的**结论**是 `∃ Z Z', … （含 ¬ CondIndep …）`，
**不是** `zipDown_false` 的别名 —— 它把「`¬ ∀`」显式化成「`∃` 见证」，
并**同时**把两个 `CondIndep` 事实取出（`condIndepB`、`not_condIndepB`），
这与 `¬ ZipDown` 的纯否定形式不同。 -/
theorem zipDown_false_sharp :
    ∃ Z Z' : Finset (Fin 4), Z ⊆ Z' ∧
      CondIndep PjointB ({0} : Finset (Fin 4)) ({1} : Finset (Fin 4)) Z' ∧
      ¬ CondIndep PjointB ({0} : Finset (Fin 4)) ({1} : Finset (Fin 4)) Z := by
  refine ⟨∅, {2}, ?_, condIndepB, not_condIndepB⟩
  decide

/-! ===========================================================================
  §5 C5：主链**原始引擎** `markov_of_readClosedBlocks` 在 `(PjointB, gempty)` 上不可实例化
  =========================================================================== -/

/-- ⭐⭐⭐ **C5 —— `no_engine_cert_for_PjointB`**（消费 `not_condIndepB`；接 `FactorMarkov` 引擎）。

**绕过缺口**：`BridgeFullFixed.markov_of_readClosedBlocks` 是主链**未经缺口**的原始引擎
（`hloc` / `hfac` / `hnorm` / `dSep` / `ReadClosedBlocks` ⟹ `CondIndep`）。
在 `gempty` 上 `dSep` 与 `ReadClosedBlocks` **都恒成立**（§3 的 C3.2/C3.3），
故该引擎的**图论**前件在此**完全免费**。

**本定理**：即便如此，`PjointB` 仍**不能**满足引擎的三个概率前件 ——
否则引擎给出 `CondIndep PjointB {0} {1} ∅`，与 `not_condIndepB` 矛盾。

**⟹ 消费价值**：这精确地把 `ZipDownFalse` 的反例**定位到概率前件**（`hloc`/`hfac`/`hnorm`），
而不在图论一侧。它是主链引擎的**非空洞性检查**：引擎的
「图论前件 ⟹ `CondIndep`」蕴含关系**确实**在起作用（在 `PjointB` 上结论为假，
所以前件必有一假），并非 `True → True` 式的空转。

⚠ 前件审计：前件是「存在 `f` 满足三条**关于 `f`** 的条件」；
结论是「不存在」。连接靠引擎（**已证**定理）+ C1（**关于 `PjointB` 的具体否定**），
无同义反复 —— 注意本定理**不**假设 `DSepGivesReadClosed`（**绕过缺口**），
与 C3 严格不同。 -/
theorem no_engine_cert_for_PjointB :
    ¬ ∃ f : Fin 4 → (Fin 4 → Bool) → ℝ,
        LocalTo gempty f ∧
        (∀ x : Fin 4 → Bool, PjointB x = ∏ v, f v x) ∧
        FactorNorm f := by
  rintro ⟨f, hloc, hfac, hnorm⟩
  have hd : gempty.dSep ({(0 : Fin 4)} : Finset (Fin 4)) ({(1 : Fin 4)} : Finset (Fin 4))
      (∅ : Finset (Fin 4)) := by decide
  have hrc : ReadClosedBlocks gempty ({(0 : Fin 4)} : Finset (Fin 4))
      ({(1 : Fin 4)} : Finset (Fin 4)) (∅ : Finset (Fin 4)) :=
    gempty_readClosedBlocks _ _ _
  exact not_condIndepB
    (FateV2.Predict.BridgeFullFixed.markov_of_readClosedBlocks hloc hfac hnorm hd hrc)

end FateV2.Predict.ZipDownFalseConsumer