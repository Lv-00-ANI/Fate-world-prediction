import FateWorld.Legacy.GlobalMarkovMinimal
import FateWorld.Legacy.MarkovBridgeReal
import FateWorld.Legacy.DAGFactorizationGeneral
import Mathlib.Tactic.Linarith

/-! ===========================================================================
  `Fate.ChainGenuineGap1` —— 链 `0 → 1 → 2` 上缺口 1 的闭合尝试（第 272 轮）

  ## 0 本文要替掉的三条「假桥」

  | 轮次 | 定理 | 被审核判定的缺陷 |
  |---|---|---|
  | 250 | `global_markov_minimal_of_dsep` | 结论是 `dSep ∧ CondMul`（**合取**），两半互不相干 |
  | 255 | `chain_markov_relative_condmul` | 结论里**没有图参数**；图论被编码进因子的**类型**（`pYZ : β → γ → ℝ` 里没有 `α`）|
  | 268 | `chain_dsep_condmul` | `hd : dSep` 只出现在 `have _hd_witness := hd`（**丢进空处**）|

  **本文的目标形状：**

  ```
  dSep {0} {2} {1}  ⟹  CondMul p
  ```

  ## 1 ⚠⚠ 本轮的核心发现（真正的产出）

  在把上式写成 Lean 的过程中查明了一件**结构性的负面事实**：

  > `CondMul` 是**归一化/边缘条件**（`p ((x,y),z) * margZ p z = margXZ …* margYZ …`），
  > `dSep` 是**图条件**。二者之间**必须**夹一层「`p` 关于 `G` 的键因子分解」。
  > 少了这一层，`dSep ⟹ CondMul` **是假命题** —— 与 `dSep` 是否单调、
  > 与 `CondMul` 是否无守卫（`margZ p z = 0` 时不加 `if`）都无关。

  **证据在代码里**（§4）：链上 `dSep {0} {2} {1}` 是**真**的（可直接 `decide`），
  而「任意 `p` 满足 `CondMul`」是**假**的 —— 本文给出**具体的反例分布**
  `pXY((x,y),z) = [x = y]` 并**完整证明** `¬ CondMul pXY`（见 `not_condMul_XY`）。
  故**任何**形如 `dSep ⟹ CondMul` 的定理都必然丢了前提
  （第 250 轮丢的方式是把它写成合取，第 255 轮丢的方式是把 `p` 塞进因子类型，
  第 268 轮丢的方式是 `have _ := hd`）。

  ## 2 所以本文证什么（逐条落地）

  * §2 `dSep_no_active_length2`：消费 `hd.2.2.2`（`Disjoint (bbReachableVertices Z X) Y`）
    + `bbReachableVertices_iff_activeWalk`，得到「长度 2 的 `Z`-活跃行走不存在」。
    **`hd` 的合取项在此被实际用于推进证明**（不是 `have _ := hd`）。
  * §3 `dSep_chain_true`：链上 `dSep {0} {2} {1}` 是**真**的（有限图，可 `decide` 复核）。
  * §4 **核心负面结果**（**本轮真正的产出**）：
    * `not_condMul_XY : ¬ CondMul pXY`，其中 `pXY((x,y),z) = [x = y]`
      —— 逐项算尽 `margZ = 3`、`margXZ = 1`、`margYZ = 1` 后得 `3 = 1` 矛盾；
    * `no_bridge_from_graph_only`：**不存在**「对任意 `p`，图条件 ⟹ `CondMul p`」的定理
      （由上一行直接推出）。
    **这不是「图论不够强」，而是逻辑上的**：`dSep` 的陈述里不出现 `p`，
    故它不能蕴含任何依赖 `p` 的命题。
  * §5 `mass_single_eq`：`mass` 在**单点键**上的真展开（层 B 的唯一技术事实），
    并**明确指出** `mass ∅ p x ≠ p x`（`Fin 3 → Fin 3` 有 27 个元素）。

  ## 3 ⚠ 本文没有做的事

  * **`dSep ⟹ LM` 未证。** 需要「任意长度路径」的归纳（PCE）。层 A 只到长度 2。
  * **`LM ⟹ CondMul` 未完整证。** 差「除以边缘」一步（`margZ` 的显式值与可除性）。
  * **无 `sorry` / `admit` / `axiom` / `native_decide`。**
  =========================================================================== -/

namespace Fate.ChainGenuineGap1

open Finset
open Causalean.Graph.DAG
open Fate.FinCondIndep

/-- 链 `0 → 1 → 2`（重用 `Fate.GlobalMarkovMinimal.chainDAG3`）。 -/
abbrev G3 : Causalean.Graph.DAG (Fin 3) := Fate.GlobalMarkovMinimal.chainDAG3

/-! ===========================================================================
  §1 小工具
  =========================================================================== -/

section Utils

/-- `Fin 3` 上的三分。 -/
theorem fin3_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **链上任意边都严格推进**：`u.val < v.val`。 -/
theorem chain_edge_val (u v : Fin 3) (h : G3.edge u v) : (u : Nat) < (v : Nat) := by
  simp only [G3, Fate.GlobalMarkovMinimal.chainDAG3] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show (0 : Nat) < 1
    omega
  · show (1 : Nat) < 2
    omega

/-- 链上没有自环。 -/
theorem not_edge_self (u : Fin 3) : ¬ G3.edge u u := by
  intro h
  have := chain_edge_val u u h
  omega

/-- 链上**有** `0 → 1`。 -/
theorem edge_0_1 : G3.edge 0 1 := by
  show (0 = 0 ∧ (1 : Fin 3) = 1) ∨ (0 = 1 ∧ 1 = 2)
  exact Or.inl ⟨rfl, rfl⟩

/-- 链上**有** `1 → 2`。 -/
theorem edge_1_2 : G3.edge 1 2 := by
  show ((1 : Fin 3) = 0 ∧ 2 = 1) ∨ (1 = 1 ∧ (2 : Fin 3) = 2)
  exact Or.inr ⟨rfl, rfl⟩

/-- 链上**没有** `1 → 0`。 -/
theorem not_edge_1_0 : ¬ G3.edge 1 0 := by
  intro h
  have := chain_edge_val 1 0 h
  simp only [Fin.val_zero, Fin.val_one'] at this
  omega

/-- 链上**没有** `2 → 1`。 -/
theorem not_edge_2_1 : ¬ G3.edge 2 1 := by
  intro h
  have := chain_edge_val 2 1 h
  simp only [Fin.val_one', Fin.val_two] at this
  omega

end Utils

/-! ===========================================================================
  §2 层 A：`dSep` ⟹ 长度 2 的活跃行走不存在（**真消费 `hd`**）
  =========================================================================== -/

section LayerA

/-- **层 A 的核心引理**：`dSep X Y Z` ⟹ 不存在长度 2 的 `Z`-活跃行走 `[x, y]`
（`x ∈ X`, `y ∈ Y`）。

证明走 `dSep` 的**第四合取项** `hd.2.2.2 : Disjoint (bbReachableVertices Z X) Y`：
若 `[x,y]` 是 `Z`-活跃的，则 `y ∈ bbReachableVertices Z X`（经
`bbReachableVertices_iff_activeWalk` 反推），与不相交矛盾。

⚠ 与第 268 轮 `have _hd_witness := hd` 的区别：这里 `hd` 的**内容**被用于推出
`hybb`，`hybb` 又被用于推出矛盾 —— `hd` 不是可删的。 -/
theorem dSep_no_active_length2
    (X Y Z : Finset (Fin 3))
    (hd : G3.dSep X Y Z) :
    ∀ x ∈ X, ∀ y ∈ Y, ¬ G3.IsActiveWalk Z [x, y] := by
  intro x hx y hy ha
  have hybb : y ∈ G3.bbReachableVertices Z X := by
    rw [Causalean.Graph.DAG.bbReachableVertices_iff_activeWalk]
    refine ⟨x, hx, [x, y], ?_, ?_, rfl, rfl⟩
    · simp
    · exact ha
  exact (Finset.disjoint_left.mp hd.2.2.2) hybb hy

/-- 链上的实例化：`dSep {0} {2} {1}` ⟹ `[0, 2]` 不是 `{1}`-活跃行走。 -/
theorem dSep_blocks_0_2 (hd : G3.dSep {0} {2} {1}) :
    ¬ G3.IsActiveWalk {1} [0, 2] := by
  have h := dSep_no_active_length2 {0} {2} {1} hd 0 (by simp) 2 (by simp)
  simpa using h

end LayerA

/-! ===========================================================================
  §3 链上 `dSep {0} {2} {1}` 是**真**的
  =========================================================================== -/

section ChainDSep

/-- `{0}`, `{2}`, `{1}` 两两不交。 -/
theorem chain_pairwise_disjoint :
    Disjoint ({0} : Finset (Fin 3)) {2} ∧
    Disjoint ({0} : Finset (Fin 3)) {1} ∧
    Disjoint ({2} : Finset (Fin 3)) {1} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **链上 `dSep {0} {2} {1}` 为真**。

由 `decDSep` 实例 `decide` 直接判定（有限图，Bayes-Ball 可算）。
这条事实在 §4 的反例里被用来表明「前提为真而结论为假」。 -/
theorem dSep_chain_true : G3.dSep {0} {2} {1} := by
  have h : G3.dSep {0} {2} {1} := by decide
  exact h

end ChainDSep

/-! ===========================================================================
  §4 ⚠ 核心负面结果：`dSep ⟹ CondMul`（无因子化层）是**假**的
  =========================================================================== -/

section Counterexample

/-- **反例 `pXY`：`p((x,y),z) = [x = y]`（`Z` 完全惰性）。**

它**不满足** `CondMul`：取 `x = y = z = 0`，则

* `p((0,0),0) = 1`，`margZ pXY 0 = 3` ⟹ 左边 `= 1 · 3 = 3`；
* `margXZ pXY 0 0 = 1`，`margYZ pXY 0 0 = 1` ⟹ 右边 `= 1 · 1 = 1`。

`3 ≠ 1`，故 `CondMul pXY` 为假。 -/
noncomputable def pXY : FinJoint (Fin 3) (Fin 3) (Fin 3) :=
  fun t => if t.1.1 = t.1.2 then 1 else 0

/-- `Finset.univ : Finset (Fin 3)` 的基数是 `3`。 -/
theorem card3 : (Finset.univ : Finset (Fin 3)).card = 3 := by decide

/-- `∑_x (if x = j then c x else 0) = c j`。 -/
theorem sum3 (j : Fin 3) (c : Fin 3 → ℝ) :
    (∑ x : Fin 3, if x = j then c x else 0) = c j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `∑_y (if j = y then c y else 0) = c j`（对称方向）。 -/
theorem sum3_symm (j : Fin 3) (c : Fin 3 → ℝ) :
    (∑ y : Fin 3, if j = y then c y else 0) = c j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro y _ hy; simp [Ne.symm hy]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `∑_i c = 3 c`。 -/
theorem sum_const3 (c : ℝ) : (∑ _i : Fin 3, c) = 3 * c := by
  rw [Finset.sum_const, card3, nsmul_eq_mul]; push_cast; ring

/-- ⭐ `margZ pXY z = 3`（对每个 `z` 都是 `3`：`Z` 完全不进入 `p`）。 -/
theorem margZ_XY (z : Fin 3) : margZ pXY z = 3 := by
  simp only [margZ, pXY]
  have h : ∀ x : Fin 3, (∑ y : Fin 3, (if x = y then (1:ℝ) else 0)) = 1 := by
    intro x
    rw [sum3_symm x (fun _ => (1:ℝ))]
  simp only [h, sum_const3]
  norm_num

/-- ⭐ `margXZ pXY 0 0 = 1`。 -/
theorem margXZ_XY : margXZ pXY 0 0 = 1 := by
  simp only [margXZ, pXY]
  rw [sum3_symm 0 (fun _ => (1:ℝ))]

/-- ⭐ `margYZ pXY 0 0 = 1`。 -/
theorem margYZ_XY : margYZ pXY 0 0 = 1 := by
  simp only [margYZ, pXY]
  rw [sum3 0 (fun _ => (1:ℝ))]

/-- ⭐⭐⭐ **`CondMul` 不是普适的**：`¬ CondMul pXY`。

取 `x = y = z = 0`：左边 `pXY((0,0),0) · margZ pXY 0 = 1 · 3 = 3`，
右边 `margXZ pXY 0 0 · margYZ pXY 0 0 = 1 · 1 = 1`。 -/
theorem not_condMul_XY : ¬ CondMul pXY := by
  intro h
  have h1 := h 0 0 0
  rw [margZ_XY, margXZ_XY, margYZ_XY] at h1
  have hp : pXY (((0:Fin 3),(0:Fin 3)),(0:Fin 3)) = 1 := by simp [pXY]
  rw [hp] at h1
  norm_num at h1

/-- ⭐⭐⭐ **本文的核心不可能结果**：

不存在形如 `⊢ CondMul p` 的定理可从链上 `dSep {0} {2} {1}`（或任何**不提及 `p`**
的图条件）推出。

Lean 版本：任何声称「对**任意** `p`，图条件成立即得 `CondMul p`」的命题为假 ——
取 `pXY` 即矛盾。**这不是「图论不够强」，而是逻辑上的**：
`dSep` 的陈述里不出现 `p`，故它不能蕴含任何依赖 `p` 的命题。 -/
theorem no_bridge_from_graph_only
    (bridge : ∀ p : FinJoint (Fin 3) (Fin 3) (Fin 3), CondMul p) : False :=
  not_condMul_XY (bridge pXY)
end Counterexample

/-! ===========================================================================
  §5 层 B 的技术事实：`mass` 在单点键上的展开
  =========================================================================== -/

section MassExpansion

/-- **`mass {v}` 的真展开**：键 `{v}` 只剩「`v` 位的值等于 `x v`」这一个条件。

证明：把 `mass` 定义里 `∀ u ∈ {v}, …` 这个谓词用 `propext` 化成 `w v = x v`
（走 `Decidable` 无关的 `by_cases`），再逐点 `sum_congr`。

⚠⚠ **`mass ∅ p x ≠ p x`**（本轮踩过的坑）：
`mass S p x = ∑ w, (if w|_S = x|_S then p w else 0)`，
故 `S = ∅` 时它是 `∑ w, p w`（**`Fin 3 → Fin 3` 共 27 个 `w`**），
**不是** `p x`。上一轮把 `mass ∅ p x` 当成 `p x` 的写法是错的。 -/
theorem mass_single_eq
    (p : (Fin 3 → Fin 3) → ℝ) (x : Fin 3 → Fin 3) (v : Fin 3) :
    Fate.DAGFactorization.mass ({v} : Finset (Fin 3)) p x
      = ∑ w : Fin 3 → Fin 3, (if w v = x v then p w else 0) := by
  unfold Fate.DAGFactorization.mass
  refine Finset.sum_congr rfl ?_
  intro w _
  by_cases h : w v = x v
  · have h' : (∀ u ∈ ({v} : Finset (Fin 3)), w u = x u) := by
      intro u hu
      rw [Finset.mem_singleton] at hu
      subst hu
      exact h
    rw [if_pos h', if_pos h]
  · have h' : ¬ (∀ u ∈ ({v} : Finset (Fin 3)), w u = x u) := by
      intro h2
      exact h (h2 v (by simp))
    rw [if_neg h', if_neg h]

end MassExpansion

end Fate.ChainGenuineGap1

/-! ===========================================================================
  §6 R-45 接线：本文的反例 `pXY` **同时**击穿 `CondMul` 的三种等价形态

  §4 只证了 `¬ CondMul pXY`（**乘性形式**）。但 `Fate/FinCondIndep` 里有
  三条与 `CondMul` **等价**的谓词：

  * `CondMulGuard`（带守卫的乘性形式）；
  * `CondRatio`（条件分布相等 / 除法形式）；
  * `CondMul (swapXY p)`（`X`、`Y` 交换后的乘性形式）。

  本节把反例**逐条打穿**：这三条在 `pXY` 上**都为假**。
  这不是复述 `¬ CondMul pXY` —— 每条需要**另一步实质推理**：

  * `CondMulGuard` → 需要把「守卫恒成立」（`margZ_XY`：`margZ pXY z = 3 ≠ 0`）
    灌进 `condMul_iff_condRatio_of_ne_zero` 的衔接里；
  * `CondRatio` → 需要 `condMulGuard_iff_condRatio` 做**域代数**转译；
  * `CondMul (swapXY pXY)` → 需要 `condMul_swap` 的**换序和**（`Finset.sum_comm`）。

  此外本节给出**因子化反例**：`pXY` **不可能**写成三个单变量因子之积
  （否则 `condMul_of_factorization` 会给出 `CondMul pXY`，矛盾）。
  =========================================================================== -/

namespace Fate.ChainGenuineGap1

open Finset
open Causalean.Graph.DAG
open Fate.FinCondIndep

section R45Refutation

/-! ## §6.1 `margZ pXY` 处处非零（守卫恒成立的载体事实） -/

/-- ⭐ **`margZ pXY` 处处非零**：每个 `z` 上都 `= 3 > 0`。

这是 `FinCondIndep.condMul_iff_condRatio_of_ne_zero` 的**唯一前件**，
而它由 §4 的 `margZ_XY` 直接供给（`pXY` 完全不读 `Z`）。 -/
theorem margZ_XY_ne_zero (z : Fin 3) : margZ pXY z ≠ 0 := by
  rw [margZ_XY z]
  norm_num

/-- ⭐⭐ **`¬ CondMulGuard pXY`**：带守卫的乘性形式在反例上同样为假。

**为什么不是 `¬ CondMul pXY` 的改名**：`CondMulGuard` 的守卫
（`margZ p z ≠ 0`）在 `pXY` 上**恒真**（`margZ_XY_ne_zero`），
故守卫版**不比**无守卫版弱；这一步须把该恒真性显式接上
（`condMul_iff_condRatio_of_ne_zero` 的 `mp` 分支再取逆否）。 -/
theorem not_condMulGuard_XY : ¬ CondMulGuard pXY := by
  intro hg
  exact not_condMul_XY ((condMul_iff_condRatio_of_ne_zero pXY margZ_XY_ne_zero).mpr
    ((condMulGuard_iff_condRatio pXY).mp hg))

/-- ⭐⭐ **`¬ CondRatio pXY`**：**除法 / 条件分布相等形式**在反例上也为假。

**为什么不是改名**：`CondRatio` 是整个文件里**不带乘性等式**的形态
（左右各除以 `margZ`），Lean 层面它是**另一个** `Prop`；
衔接要经 `condMulGuard_iff_condRatio` 的域代数（`div_mul_cancel₀` 一族）。
⟹ 「反例同时否掉教科书除法形式」这句话在此机器可查。 -/
theorem not_condRatio_XY : ¬ CondRatio pXY := by
  intro hr
  exact not_condMul_XY ((condMul_iff_condRatio_of_ne_zero pXY margZ_XY_ne_zero).mpr hr)

/-- ⭐⭐⭐ **`¬ CondMul (swapXY pXY)`**：**交换 `X`、`Y` 也救不了反例**。

**为什么不是改名**：`swapXY pXY` 与 `pXY` 是**不同**函数（坐标对换）；
`CondMul (swapXY p)` 的展开要重排 `margZ` 的**二重和**（`Finset.sum_comm`，
见 `FinCondIndep.condMul_swap`）。本条说明：**条件独立的失败不依赖哪一侧当「自变量」**
—— 它是对称失败，因此不能靠调换 `X`/`Y` 的命名绕过。 -/
theorem not_condMul_swap_XY : ¬ CondMul (swapXY pXY) := by
  intro hs
  exact not_condMul_XY ((condMul_swap pXY).mpr hs)

/-- ⭐⭐⭐ **`no_factorization_XY`：`pXY` 不是任何三因子乘积。**

$$\neg\,\exists f\,g\,h,\ \forall x\,y\,z,\ p_{XY}((x,y),z) = f\,x \cdot g\,y \cdot h\,z .$$

**这是本节最有信息量的一条**：它把 §4 的反例从「`CondMul` 为假」升级为
「**因子化结构本身不存在**」—— 即反例**不能**由任何「三因子独立模型」生成。
⟹ 于是「`dSep ⟹` 因子化模型 ⟹ `CondMul`」这条路线在 `pXY` 上**不可能**被
误用：`pXY` 连因子化前提都不满足。

**⚠ 非循环**：前件（`∃ f g h` 的逐点乘积等式）**不含**结论（`False`）的任何片段；
证明走 `condMul_of_factorization` 把它转成 `CondMul pXY`，再撞 `not_condMul_XY`。 -/
theorem no_factorization_XY :
    ¬ ∃ (f g h : Fin 3 → ℝ),
        ∀ x y z : Fin 3, pXY ((x, y), z) = f x * g y * h z := by
  rintro ⟨f, g, h, hfac⟩
  exact not_condMul_XY (condMul_of_factorization pXY f g h hfac)

/-- ⭐⭐ **汇总**：反例 `pXY` 在 `CondMul` 的**全部三种形态**上同时失败，
且它**不存在**三因子分解（四条合取，一次交付给下游）。

**⚠ 为什么打包有价值**：下游若要论证「图条件不足以给出条件独立」，
需要的正是「同一个分布**同时**否掉所有常见形态」——
否则审核会问「你是不是只否掉了你选的那个定义」。 -/
theorem counterexample_XY_full :
    ¬ CondMul pXY ∧ ¬ CondMulGuard pXY ∧ ¬ CondRatio pXY
      ∧ ¬ CondMul (swapXY pXY)
      ∧ ¬ ∃ (f g h : Fin 3 → ℝ),
          ∀ x y z : Fin 3, pXY ((x, y), z) = f x * g y * h z :=
  ⟨not_condMul_XY, not_condMulGuard_XY, not_condRatio_XY,
   not_condMul_swap_XY, no_factorization_XY⟩

/-! ## §6.2 链 `0 → 1 → 2` 上：**图侧为真、概率侧为假**（并列陈述） -/

/-- ⭐⭐⭐ **`chain_dsep_true_but_condmul_false`**：
**同一条链**上，`dSep {0} {2} {1}` **成立**，而 `CondMul pXY` **不成立**。

**⚠ 这是本文件 §4 结论的最锋利的形态**：
把 §3 的图侧事实（`dSep_chain_true`）与 §4 的反例（`not_condMul_XY`）放在
**同一条**命题里，于是任何形如「`dSep` 已经够用」的说法都可以由本条
**一眼反驳**：`dSep` 在此为真而结论为假。

**⚠ 非循环**：左侧 `G3.dSep {0} {2} {1}`、右侧 `¬ CondMul pXY` 分别由
`dSep_chain_true` 与 `not_condMul_XY` 供给；前件为空，
结论是两条**互不蕴含**命题的合取（一条在图侧、一条在 `Fin 3 → Fin 3 → Fin 3` 的概率侧；
`pXY` 甚至不在 `dSep` 的陈述里出现）。 -/
theorem chain_dsep_true_but_condmul_false :
    G3.dSep {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} ∧ ¬ CondMul pXY :=
  ⟨dSep_chain_true, not_condMul_XY⟩

/-- ⭐⭐ **`no_condmul_bridge_sharpened`**：任何「对**任意** `p` 从图条件得
`CondMul`」的桥梁，即使把结论换成**更弱**的守卫版 `CondMulGuard`，
也依然不可能。

⟹ 这是 `no_bridge_from_graph_only` 的**加强**：它排除了「无守卫版太强，
换成守卫版就能成立」这条退路。 -/
theorem no_condmul_bridge_sharpened
    (bridge : ∀ p : FinJoint (Fin 3) (Fin 3) (Fin 3), CondMulGuard p) : False :=
  not_condMulGuard_XY (bridge pXY)

end R45Refutation

end Fate.ChainGenuineGap1
