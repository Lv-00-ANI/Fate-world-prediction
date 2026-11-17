import FateWorld.FateV2.Predict.ThreeNodeFactorizes
import Mathlib.Tactic

/-!
  # Predict · BridgeThreeNode

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeThreeNode.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ThreeNodeFactorizes
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeThreeNode` —— **C1：三节点图的 `Factorizes` ⟹ `CondMul`，并让 `dSep` 真正上桌**

  ## 与 `Fate/ThreeNodeFactorizes.lean` 的区别（本文件为什么不重复）

  `Fate/ThreeNodeFactorizes.lean`（第 7 路）已经在**链**与**分叉**上逐图证了
  `Factorizes ⟹ CondMul`，但它的**诚实登记**（其 §8）写明：`dSep` **没有**被消费，
  只是与 `CondMul` 并排放进合取（`chain_global_markov : dSep ∧ CondMul`）。

  **本文件（C1）修掉这个缺口**，方法是把「逐图」换成**一条一般判据 + 一次 `dSep` 推导**：

  | # | 名称 | 内容 | 状态 |
  |---|---|---|---|
  | **C1.0** | `reads01` / `reads12` | `pa v ⊆ {0,1}`（或 `{1,2}`）⟹ 因子只读 `x₀,x₁`（`x₁,x₂`）| ✅ |
  | **C1.1** | `separable_of_reads` | ⭐ **一般判据**：若 `∀ v, pa v ⊆ {0,1} ∨ pa v ⊆ {1,2}`，则 `Factorizes ⟹ 可分离` | ✅ |
  | **C1.2** | `dSep_forces_reads` | ⭐⭐ **`dSep {0}{2}{1}` ⟹ 上述判据**（**真消费 `dSep`**）| ✅ |
  | **C1.3** | `factorizes_condMul_of_dSep` | ⭐⭐⭐ **主定理**：`dSep {0}{2}{1}` + `Factorizes ⟹ CondMul` | ✅ |
  | **C1.4** | `chain_condMul_of_dSep` / `fork_condMul_of_dSep` | 链 / 分叉特化（`decide` 出 `dSep`，再走主定理）| ✅ |
  | **C1.5** | `collider_dSep_cond_fails` | 撞子：`dSep {0}{2}{1}` **假** ⟹ 主定理的 `dSep` 前件**真的**排除了撞子 | ✅ |

  **零 `sorry` / `axiom`。不使用 `mass` 塔性质、不使用 `mass`。**

  ---

  ## ⭐ 主定理的两个前件分别用在哪一步（本文件的**核心诚实回答**）

  主定理 `factorizes_condMul_of_dSep p G (hd : G.dSep {0}{2}{1}) (hfac : Factorizes p G)`

  * **`hd`（`dSep` 前件）用在 `dSep_forces_reads`（C1.2）**，且**只**用在那里。
    具体消费的是 `dSep` 定义的第 4 个合取项
    `Disjoint (bbReachableVertices Z X) Y`（**Bayes-ball 不可达**），
    经由 `bbReachableVertices_iff_activeWalk` 把它翻译成「存在主动路径」：
    - `¬ G.edge 2 0`：否则主动路径 `[0, 2]` 打通 `0 → 2`；
    - `¬ G.edge 0 2`：否则主动路径 `[2, 0]`（反向）；
    - `¬ (G.edge 0 1 ∧ G.edge 2 1)`：否则 **1 是撞子**，主动路径 `[0, 1, 2]` 打通
      （条件集 `{1}` 激活撞子）。
    这三条恰好把「`pa v ⊇ {0,2}`」的唯一可能（`v = 1` 处的撞子）排除，
    从而得到 C1.1 的判据。**若把 `hd` 去掉，撞子反例（`colliderP`）就会闯进来
    —— 见 C1.5 与 §4 的机器证据。**

  * **`hfac`（因子分解前件）用在 `separable_of_reads`（C1.1）**：
    取见证 `φ`，用 `φ v` 只读 `pa G v`（`hφ`）把每个 `φ v` 归到
    「只读 `x₀,x₁`」或「只读 `x₁,x₂`」的**其中一类**，再拆乘积。
    **`hfac` 若去掉，可分离性无从谈起**（那是 `p` 的唯一定量信息）。

  * **`CondMul` 的结论由 `Fate.PearlCondIndepBridge.separable_implies_condMul`**
    （纯代数：可分离 ⟹ `CondMul`，无正性假设）给出 —— 它**不含**任何图论前提。

  ⟹ **没有把结论写进前件**，也不存在「`hd` 未被消费」的问题。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeThreeNode

open Finset
open Fate.DAGFactorization
open Fate.FactorRecursionRouteB (Factorizes)
open Fate.ThreeNodeFactorizes (N a b c jointXZ jointXZ_apply)
open FateV2.Predict.FinCondIndep (CondMul)

universe u

set_option linter.unusedSectionVars false

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-! ===========================================================================
  §1 ⭐ 只读约束的「坐标投影」：`pa ⊆ {0,1}` ⟹ 因子只读 `x₀,x₁`
  =========================================================================== -/

/-- **C1.0a**：若 `pa G v ⊆ {0,1}`，则 `φ v` 在 `![x,z,y]` 与 `![x,z,d]` 上相等
（`φ v` 只读顶点 `0`（值 `x`）与顶点 `1`（值 `z`），顶点 `2` 的值被 `y→d` 替换也无影响）。 -/
theorem reads01 {G : FateV2.Modeling.Graph.DAG N} {φ : N → (N → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    {v : N} (hv : pa G v ⊆ ({0, 1} : Finset N)) (x y z d : α) :
    φ v ![x, z, y] = φ v ![x, z, d] := by
  refine hφ v _ _ ?_
  intro u hu
  have hu' := hv hu
  fin_cases u <;> simp_all

/-- **C1.0b**：若 `pa G v ⊆ {1,2}`，则 `φ v` 在 `![x,z,y]` 与 `![d,z,y]` 上相等
（顶点 `2` 的值 `y` 与顶点 `1` 的值 `z` 保留，顶点 `0` 的值 `x→d` 无影响）。 -/
theorem reads12 {G : FateV2.Modeling.Graph.DAG N} {φ : N → (N → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    {v : N} (hv : pa G v ⊆ ({1, 2} : Finset N)) (x y z d : α) :
    φ v ![x, z, y] = φ v ![d, z, y] := by
  refine hφ v _ _ ?_
  intro u hu
  have hu' := hv hu
  fin_cases u <;> simp_all

/-! ===========================================================================
  §2 ⭐⭐ **C1.1 一般判据：每个因子都「不读 `x₂`」或「不读 `x₀`」⟹ 可分离**

  这是链 / 分叉 / 一大类三节点图**共用**的引擎；
  它把「`pa` 的形状」翻译成「乘积可拆成两块」，正是 `Factorizes` 的定义内容。
  =========================================================================== -/

/-- ⭐⭐ **C1.1（可分离判据）**：

设 `Factorizes p G`，且**每个顶点**的父集要么 `⊆ {0,1}`（因子不读 `x₂`），
要么 `⊆ {1,2}`（因子不读 `x₀`）。则 `p` 在 `X=x₀`、`Y=x₂`、`Z=x₁` 口径下**可分离**：
存在 `f g` 使 `∀ x y z, jointXZ p ((x,y),z) = f x z * g y z`。

**证明结构**：
1. 取因子见证 `φ`。把顶点集按 `pa v ⊆ {0,1}` 分成 `A`（含 `1` 侧）与 `B`；
2. 对 `v ∈ A` 用 `reads01` 把 `φ v ![x,z,y]` 换成 `φ v ![x,z,d]`（只依赖 `x,z`）；
3. 对 `v ∈ B`（此时 `pa v ⊆ {1,2}`）用 `reads12` 换成 `φ v ![d,z,y]`（只依赖 `y,z`）；
4. `∏ = ∏A · ∏B` 即为所求分解。

**⚠ `G` 与 `hfac` 均被真使用**：`hread` 是图论前提（`pa` 形状），
`hφ` 来自 `hfac`（因子只读 `pa`）。 -/
theorem separable_of_reads {p : (N → α) → ℝ} {G : FateV2.Modeling.Graph.DAG N}
    (hfac : Factorizes p G)
    (hread : ∀ v : N, pa G v ⊆ ({0, 1} : Finset N) ∨ pa G v ⊆ ({1, 2} : Finset N)) :
    ∃ f g : α → α → ℝ, ∀ x y z : α, jointXZ p ((x, y), z) = f x z * g y z := by
  classical
  obtain ⟨φ, hφ, hprod⟩ := hfac
  obtain ⟨d⟩ := ‹Nonempty α›
  -- A 类：`pa v ⊆ {0,1}`；B 类：其余（此时由 `hread` 必为 `pa v ⊆ {1,2}`）
  set A : Finset N := (univ : Finset N).filter (fun v => pa G v ⊆ ({0, 1} : Finset N)) with hA
  set B : Finset N := (univ : Finset N).filter (fun v => ¬ pa G v ⊆ ({0, 1} : Finset N)) with hB
  refine ⟨fun x z => ∏ v ∈ A, φ v ![x, z, d],
          fun y z => ∏ v ∈ B, φ v ![d, z, y], ?_⟩
  intro x y z
  show p ![x, z, y] = (∏ v ∈ A, φ v ![x, z, d]) * (∏ v ∈ B, φ v ![d, z, y])
  rw [hprod]
  rw [← Finset.prod_filter_mul_prod_filter_not (univ : Finset N)
        (fun v => pa G v ⊆ ({0, 1} : Finset N))]
  congr 1
  · -- A 侧：`φ v ![x,z,y] = φ v ![x,z,d]`
    refine Finset.prod_congr rfl fun v hv => ?_
    exact reads01 hφ (Finset.mem_filter.mp hv).2 x y z d
  · -- B 侧：由 `hread` 得 `pa v ⊆ {1,2}`，于是 `φ v ![x,z,y] = φ v ![d,z,y]`
    refine Finset.prod_congr rfl fun v hv => ?_
    have hnot : ¬ pa G v ⊆ ({0, 1} : Finset N) := (Finset.mem_filter.mp hv).2
    rcases hread v with h01 | h12
    · exact absurd h01 hnot
    · exact reads12 hφ h12 x y z d

/-! ===========================================================================
  §3 ⭐⭐⭐ **C1.2：`dSep` 真的推出判据（`dSep` 在此被消费）**

  消费的是 `dSep` 的**第 4 个合取项**：`Disjoint (bbReachableVertices Z X) Y`。
  经 `bbReachableVertices_iff_activeWalk`，它等价于「`Y` 中无点被 `Z` 下的主动路径到达」。
  下面把三种「破坏判据」的图形逐一用主动路径反驳。
  =========================================================================== -/

/-- 主动路径 `[0,2]`：若 `G.edge 2 0`，则 `0 - 2` 相邻，无中间三元组，恒为主动。 -/
theorem activeWalk_02 {G : FateV2.Modeling.Graph.DAG N} (h : G.edge 2 0) :
    G.IsActiveWalk ({1} : Finset N) [0, 2] := by
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have h0 : i = 0 := by omega
    subst h0
    show G.UAdj 0 2; exact Or.inr h
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    omega

/-- 主动路径 `[0,2]`：只要 `0 - 2` 相邻（任一方向有条边），该长度 2 的路径恒主动
（无中间三元组，条件约束为空）。 -/
theorem activeWalk_02' {G : FateV2.Modeling.Graph.DAG N} (h : G.UAdj 0 2) :
    G.IsActiveWalk ({1} : Finset N) [0, 2] := by
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have h0 : i = 0 := by omega
    subst h0
    show G.UAdj 0 2; exact h
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    omega

/-- 主动路径 `[0,1,2]`：若 `0` 与 `2` **同时**指向 `1`（即 `1` 是**撞子**），
且条件集含 `1`，则该路径被**激活**。 -/
theorem activeWalk_012_collider {G : FateV2.Modeling.Graph.DAG N}
    (h01 : G.edge 0 1) (h21 : G.edge 2 1) :
    G.IsActiveWalk ({1} : Finset N) [0, 1, 2] := by
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have h0 : i = 0 ∨ i = 1 := by omega
    rcases h0 with rfl | rfl
    · show G.UAdj 0 1; exact Or.inl h01
    · show G.UAdj 1 2; exact Or.inr h21
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have h0 : i = 0 := by omega
    subst h0
    show (if G.IsCollider 0 1 2 then (1 : N) ∈ G.bbZAncestors ({1} : Finset N)
          else (1 : N) ∉ ({1} : Finset N))
    rw [if_pos (show G.IsCollider 0 1 2 from ⟨h01, h21⟩)]
    unfold FateV2.Modeling.Graph.DAG.bbZAncestors FateV2.Modeling.Graph.DAG.ancestralSet FateV2.Modeling.Graph.DAG.ancestorsSet
    simp

/-- `dSep` 的**第 4 项**化成「主动路径不存在」：若存在从 `{0}` 到点 `2` 的主动路径，
则 `dSep {0} {2} {1}` 被推翻。 -/
theorem not_dSep_of_walk {G : FateV2.Modeling.Graph.DAG N}
    (q : List N) (hlen : q.length ≥ 2) (hact : G.IsActiveWalk ({1} : Finset N) q)
    (hh : q.head? = some (0 : N)) (hl : q.getLast? = some (2 : N)) :
    ¬ G.dSep {0} {2} {1} := by
  intro hd
  obtain ⟨_, _, _, hR⟩ := hd
  have hmem : (2 : N) ∈ G.bbReachableVertices ({1} : Finset N) ({0} : Finset N) := by
    rw [FateV2.Modeling.Graph.DAG.bbReachableVertices_iff_activeWalk]
    exact ⟨0, by simp, q, hlen, hact, hh, hl⟩
  rw [Finset.disjoint_left] at hR
  exact hR hmem (by simp)

/-- 从 `dSep {0}{2}{1}` 读出「无 `2 → 0` 直边」：否则主动路径 `[0,2]` 打通。 -/
theorem no_edge_20 {G : FateV2.Modeling.Graph.DAG N}
    (hd : G.dSep ({0} : Finset N) ({2} : Finset N) ({1} : Finset N)) :
    ¬ G.edge 2 0 := by
  intro he
  exact not_dSep_of_walk [0, 2] (by simp) (activeWalk_02 he) rfl rfl hd

/-- 从 `dSep {0}{2}{1}` 读出「无 `0 → 2` 直边」：否则反向主动路径 `[2,0]` 打通。 -/
theorem no_edge_02 {G : FateV2.Modeling.Graph.DAG N}
    (hd : G.dSep ({0} : Finset N) ({2} : Finset N) ({1} : Finset N)) :
    ¬ G.edge 0 2 := by
  intro he
  exact not_dSep_of_walk [0, 2] (by simp) (activeWalk_02' (Or.inl he)) rfl rfl hd

/-- 从 `dSep {0}{2}{1}` 读出「`1` 处无撞子（`0→1` 与 `2→1` 不同时成立）」。 -/
theorem no_collider_1 {G : FateV2.Modeling.Graph.DAG N}
    (hd : G.dSep ({0} : Finset N) ({2} : Finset N) ({1} : Finset N)) :
    ¬ (G.edge 0 1 ∧ G.edge 2 1) := by
  rintro ⟨h01, h21⟩
  exact not_dSep_of_walk [0, 1, 2] (by simp) (activeWalk_012_collider h01 h21) rfl rfl hd

/-- ⭐⭐⭐ **C1.2（`dSep ⟹ 判据`，`dSep` 在此被真正消费）**：

在三节点图 `G`（顶点 `0,1,2`）上，若 `G.dSep {0} {2} {1}`，则
$$\forall v,\quad \mathrm{pa}_G(v)\subseteq\{0,1\}\ \lor\ \mathrm{pa}_G(v)\subseteq\{1,2\}.$$

**证明**（按 `v` 分三种情形；`dSep` 在此**被消费三次**）：
* `v = 0`：`pa 0 ⊆ {0,1}`。若 `2 ∈ pa 0` 则 `2 → 0`，被 `no_edge_20` 排除；`0 ∉ pa 0`（无自环）。
* `v = 2`：`pa 2 ⊆ {1,2}`。若 `0 ∈ pa 2` 则 `0 → 2`，被 `no_edge_02` 排除。
* `v = 1`：若 `pa 1` 同时含 `0` 与 `2`，则 `1` 是撞子且条件集含 `1`，
  路径 `[0,1,2]` 被激活，被 `no_collider_1` 排除。故 `0∉pa 1`（得 `⊆{1,2}`）
  或 `2∉pa 1`（得 `⊆{0,1}`）。 -/
theorem dSep_forces_reads {G : FateV2.Modeling.Graph.DAG N}
    (hd : G.dSep ({0} : Finset N) ({2} : Finset N) ({1} : Finset N)) :
    ∀ v : N, pa G v ⊆ ({0, 1} : Finset N) ∨ pa G v ⊆ ({1, 2} : Finset N) := by
  classical
  have h20 : ¬ G.edge 2 0 := no_edge_20 hd
  have h02 : ¬ G.edge 0 2 := no_edge_02 hd
  have hcol : ¬ (G.edge 0 1 ∧ G.edge 2 1) := no_collider_1 hd
  intro v
  fin_cases v
  · -- `v = 0`：`2 ∉ pa 0`
    refine Or.inl ?_
    intro x hx
    have hx2 : x ≠ 2 := by
      intro h; subst h; exact h20 (mem_pa.mp hx)
    fin_cases x
    · simp
    · simp
    · exact absurd rfl hx2
  · -- `v = 1`：无撞子 ⟹ `0 ∉ pa 1` 或 `2 ∉ pa 1`
    by_cases h0 : (0 : N) ∈ pa G 1
    · -- `0 ∈ pa 1` ⟹ `2 ∉ pa 1` ⟹ `pa 1 ⊆ {0,1}`
      refine Or.inl ?_
      intro x hx
      have hx2 : x ≠ 2 := by
        intro h
        exact hcol ⟨mem_pa.mp h0, mem_pa.mp (h ▸ hx)⟩
      fin_cases x
      · simp
      · simp
      · exact absurd rfl hx2
    · -- `0 ∉ pa 1` ⟹ `pa 1 ⊆ {1,2}`
      refine Or.inr ?_
      intro x hx
      have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
      fin_cases x
      · exact absurd rfl hx0
      · simp
      · simp
  · -- `v = 2`：`0 ∉ pa 2`
    refine Or.inr ?_
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h; subst h; exact h02 (mem_pa.mp hx)
    fin_cases x
    · exact absurd rfl hx0
    · simp
    · simp

/-! ===========================================================================
  §4 ⭐⭐⭐ **C1.3 主定理：`dSep` + `Factorizes ⟹ CondMul`（三节点，一般图）**
  =========================================================================== -/

/-- ⭐⭐⭐ **C1.3（主定理 / C1 的核心交付）**：

对**任意**三节点图 `G`（顶点 `0,1,2`）、任意联合律 `p`：
$$\underbrace{G.\texttt{dSep}\ \{0\}\{2\}\{1\}}_{hd}
  \ \wedge\ \underbrace{\texttt{Factorizes}\ p\ G}_{hfac}
  \ \Longrightarrow\ \texttt{CondMul}\ (\texttt{jointXZ}\ p),$$
即 `x₀ ⟂ x₂ | x₁`（乘性、无正性假设）。

**前件的分工**（见文件头「诚实回答」）：
* `hd` ⟹ `dSep_forces_reads`（C1.2）：把撞子（`pa 1 ⊇ {0,2}`）与 `0–2` 直边排除；
* `hfac` ⟹ `separable_of_reads`（C1.1）：用 `pa` 形状拆乘积；
* `separable_implies_condMul`：纯代数收尾。 -/
theorem factorizes_condMul_of_dSep {p : (N → α) → ℝ} {G : FateV2.Modeling.Graph.DAG N}
    (hd : G.dSep ({0} : Finset N) ({2} : Finset N) ({1} : Finset N))
    (hfac : Factorizes p G) :
    CondMul (jointXZ p) := by
  obtain ⟨f, g, hsep⟩ := separable_of_reads hfac (dSep_forces_reads hd)
  exact FateV2.Predict.PearlCondIndepBridge.separable_implies_condMul (jointXZ p) f g hsep

/-! ===========================================================================
  §5 ⭐ **C1.4 链 / 分叉特化：`decide` 出 `dSep`，再走主定理**

  与 `ThreeNodeFactorizes` 的 `chain_factorizes_condMul` 相比，这里**多消费了 `dSep`**：
  证明链是 `dSep → 主定理`，而不是只靠 `pa` 的值。
  =========================================================================== -/

/-- **C1.4a（链）**：`dSep` 由 `decide` 得，`Factorizes ⟹ CondMul` 由主定理得。 -/
theorem chain_condMul_of_dSep {p : (N → α) → ℝ}
    (hfac : Factorizes p Fate.ThreeNodeFactorizes.chainDAG) :
    CondMul (jointXZ p) :=
  factorizes_condMul_of_dSep (G := Fate.ThreeNodeFactorizes.chainDAG) (by decide) hfac

/-- **C1.4b（分叉）**：同上。 -/
theorem fork_condMul_of_dSep {p : (N → α) → ℝ}
    (hfac : Factorizes p Fate.ThreeNodeFactorizes.forkDAG) :
    CondMul (jointXZ p) :=
  factorizes_condMul_of_dSep (G := Fate.ThreeNodeFactorizes.forkDAG) (by decide) hfac

/-! ===========================================================================
  §6 ⭐⭐ **C1.5 撞子：主定理的 `dSep` 前件**真的**排除了撞子（非空洞性）**

  若把主定理的 `hd` 去掉，撞子图会给出反例（`ThreeNodeFactorizes.collider_not_condMul`）。
  下面证 `dSep {0}{2}{1}` 在撞子图上**不成立**：`dSep` 恰好挡住了那个反例。
  =========================================================================== -/

/-- **C1.5（撞子不满足 `dSep {0}{2}{1}`）**：条件化撞子 `1` 会**开启**路径，
故 `0` 与 `2` 不再 d-分离。 -/
theorem collider_not_dSep_cond :
    ¬ Fate.ThreeNodeFactorizes.colliderDAG.dSep
        ({0} : Finset N) ({2} : Finset N) ({1} : Finset N) := by
  decide

/-- **C1.5′（撞子反例确被主定理的前提排除）**：`colliderP` 满足撞子的 `Factorizes`，
但其 `CondMul` 失败；`collider_not_dSep_cond` 说明主定理前件 `hd` 在此**不成立**。
⟹ 主定理**不是**恒真；它的 `dSep` 前件是**必需的**（否则撞子反例会闯进来）。 -/
theorem collider_excluded_consistently :
    (Factorizes (Fate.ThreeNodeFactorizes.colliderP (α := Bool))
        Fate.ThreeNodeFactorizes.colliderDAG)
    ∧ ¬ CondMul (jointXZ (Fate.ThreeNodeFactorizes.colliderP (α := Bool)))
    ∧ ¬ Fate.ThreeNodeFactorizes.colliderDAG.dSep
          ({0} : Finset N) ({2} : Finset N) ({1} : Finset N) :=
  ⟨Fate.ThreeNodeFactorizes.colliderP_factorizes Bool,
   Fate.ThreeNodeFactorizes.collider_not_condMul,
   collider_not_dSep_cond⟩

/-! ===========================================================================
  §7 ⚠ **诚实登记（不进下游）**

  | 项 | 状态 |
  |---|---|
  | 三节点任意图：`dSep {0}{2}{1}` + `Factorizes ⟹ CondMul` | ✅ **已证**（C1.3），零 `sorry` |
  | `dSep` **被真正消费** | ✅ **是**（仅经 C1.2 的 Bayes-ball 不可达项，见文件头）|
  | `hfac` **被真正消费** | ✅ **是**（C1.1 的因子只读约束）|
  | 链 / 分叉特化 | ✅ 已证（C1.4），走「`decide` + 主定理」|
  | 撞子被 `dSep` 排除 | ✅ 已证（C1.5）|
  | **四节点 / 一般 DAG 的对应桥** | ❌ 未做（属 C2 与段 B）|
  | **`mass` 塔性质** | 完全未使用（已证伪，见 `DAGFactorizationGeneral` §10）|

  **本文件边界的准确陈述**：C1.3 对**顶点数恰为 3**的一般图成立，
  结论形式为「`X=x₀`、`Y=x₂`、`Z=x₁` 下的 `CondMul`」。
  它**不**声称一般 DAG 的 `Factorizes ⟹ LMG ⟹ GM`（那是段 A/B 的目标）。
  它的价值在于：**在最小非平凡实例上，第一次把 `dSep` 真正接进 `Factorizes ⟹ CondMul`
  的推理链**，并给出「去掉 `dSep` 则撞子反例闯入」的机器证明（C1.5′）。
  =========================================================================== -/

end BridgeThreeNode

end FateV2.Predict