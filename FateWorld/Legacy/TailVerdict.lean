import FateWorld.Legacy.TailBlockReal

/-! ===========================================================================
  §0  TailVerdict —— 「真正有尾块的 mass 分解」**判决**

  判决任务：mass 分解需要什么前提？我给的两个条件（`∀ v, R v ⊆ A` 与
  `hOut : ∀ v ∉ A, R v \ {v} ⊆ outSet A`）是否都不够？

  ---------------------------------------------------------------------------
  ## 判决（先给结论）

  **题面的怀疑建立在两个误判上。修正后结论是：分解在「`P1` + `hOut`」下成立，
  且这两条既不蕴含 `A = univ`（不坍缩），也不是"A 内因子读 A 外"的障碍来源。**

  ### 误判 1：「`∑_{wA} ∏ v ∈ A, ψ v (merge A wA x_tail)` 依赖 `x_tail`，
  ###          求和不能分离」

  **这个依赖在 `mass S` 内部不存在。**

  `mass S p x` 的定义是 `∑ w, if (∀ u ∈ S, w u = x u) then p w else 0`。
  `x` **只经 `S` 上的值出现**。若 `S ⊆ A`，则 `x` 在 `A` 外的值
  （即 "`x_tail`"）**根本不出现在 `mass` 的任何条件中**——它既不是自由变量，
  也不影响求和范围。见 **V1 / V2**（`mass_ignores_tail_of_S_subset_A`、
  `mass_ignores_out_of_A`）。

  ⟹ 题面担心的那个「求和不能分离」，**不是** mass 分解的障碍。

  ### 误判 2：「若 `∀ v ∈ A, R v ⊆ A`，则 `A` 外因子是常数，`P_out` 无意义」

  **这两件事无关。** `∀ v ∈ A, R v ⊆ A`（下称 `P1`）只约束 **`A` 内**的因子，
  对 `A` 外的因子一个字都没说。`A` 外的因子仍然可以是任意非平凡的函数，
  `∑_{wt} P_out` 仍然可以是非平凡的数。见 **V5'**（`mass_separable_A` 与
  `mass_separable_A_tailgenuine`）。

  **真正**让 `P_out` 变成常数的是另一条假设
  `hTail : ∀ v ∉ A, R v ⊆ Z ⊆ S ⊆ A`——但那条假设**自相矛盾**
  （`readSetOf v ∋ v`，见 `TailTailCollapse.hTail_implies_univ`）。
  所以坍缩是 `hTail` 的错，**不是 `P1` 的错**。

  ---------------------------------------------------------------------------
  ## 真正的障碍在哪里（这才是题面卡点的正解）

  `mass S p x` 在 `S ⊆ A` 时可写成「对 `A \ S` 的求和」。要让这个求和
  **作为公共因子提到 `∑_{wA}` 外面**，必须让 `A` 内乘积在 `mass` 的
  纤维内**不随纤维自由坐标变化**。而 `A` 内乘积 `P_A := ∏ v ∈ A, ψ v`
  若读 `A` 外坐标，就**不会**在纤维内为常数——这正是 **V5**
  （`pA_depends_on_tail_without_P1`）的显式反例。

  ⟹ **`P1` 是必需的，而且它就是题面一直在找的那个"真正的前提"。**

  ---------------------------------------------------------------------------
  ## 结论表

  | 编号 | 陈述 | 是否需坍缩 |
  |---|---|---|
  | **V1** | `mass S p x` 只经 `x\|_S` 依赖 `x`（`S ⊆ A`）| — |
  | **V2** | `mass S p x` 与 `x` 在 `A` 外的取值无关（`S ⊆ A`）| — |
  | **V3** | `hOut` ⟹ `∑_{wt} P_out` 与 `x` **完全无关** | 否 |
  | **V4** | `P1` ⟹ `P_A` 与 `A` 外坐标无关，且在 `A` 上取 `ψ v x` | 否 |
  | **V5** | 无 `P1` ⟹ `P_A` 依赖 `A` 外坐标（显式反例）| — |
  | **V5'** | ⭐ `P1 + hOut` ⟹ `mass A p x = (∏_{v∈A} ψ v x) · (∑_t ∏_{v∉A} ψ v (glue A x t))` | **否** |
  | **V6** | `hOut` 与 `A ≠ univ` 相容（`outSet A` 可非空）| 否 |
  | **V7** | ⚠ `P1` 与 `∅ ≠ outSet A` 相容（`P1` 不管 `A` 外因子）| 否 |

  ---------------------------------------------------------------------------
  ## 对「存在条件 C」的回答

  **存在。** `C := P1 ∧ hOut`（`hRA ∧ hOut`）。
  * **不坍缩**：`V6` + `V7` 说明 `outSet A` 可以非空，`A` 外因子可以非平凡。
  * **分解成立**：`V5'` 给出显式乘法分解 `(A 内乘积) × (A 外求和)`。
  * 与 `mass_dcomp_tail` 的差别：后者的 `hTail` 强制 `Z ⊆ A` 而 `R v ∋ v`
    故坍缩；`hOut` 是 `R v \ {v} ⊆ outSet A`，**允许 `v ∉ A` 出现在 `R v`**，
    因此**不坍缩**。

  ## 题面公式的问题（V8，分析性）

  题面写的
  ```
  mass S p x = (∑_{wA : wA|_S = x|_S} ∏ v ∈ A, ψ v (merge A wA x_tail)) * (∑ wt, ∏ v ∈ outSet A, ψ v (merge A wA wt))
  ```
  **第二个求和里出现自由 `wA`** —— 这不是良定义表达式。
  正确的乘性分离只可能有两种形态：
  1. `mass S p x = (A 内和) * (A 外和)`，其中 `A` 外和**与 `wA` 无关**
     （需 `hOut`，即 V3）——**这就是 V5'**；
  2. 若 `hOut` 不成立，则 `A` 外因子随 `wA` 变，乘积**不能**分离成两个因子，
     只能写成 `∑_t (P_A · P_out)` 的耦合和（V5' 去掉 `hOut` 后的形态，
     此时 `P_out` 依赖 `t` 也依赖读集内的 `A` 内坐标）。

  ---------------------------------------------------------------------------
  ## 诚实边界

  * 本文件给出 V1–V7 的**完整证明**，散在 §1–§6。
  * **零 `sorry` / `admit` / `axiom`。**
  * **`CondIndep` 的最终组装（对四个 `mass` 配平）未做** —— 本任务只判决
    「分解成立的前提」，不含组装。
  * 若要在 `mass_dcomp_tail` 这套工具下做**真正有尾块**的 `CondIndep`，
    需要把 `hTail` 换成 `hOut : ∀ v ∉ A, R v \ {v} ⊆ outSet A` **并加上 `P1`**；
    `mass_dcomp_tail` 本身**不能**直接复用（它的 `hTail`/`hZS` 组合强制坍缩），
    需要一条新的 `mass` 分解引理 —— 那就是本文件的 **V5'**。
  =========================================================================== -/

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19

universe u

set_option linter.unusedSectionVars false

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ===========================================================================
  §1  **V1 / V2**：`mass S` 看不见 `A` 外坐标  ⭐ 推翻题面"卡点"
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **V1：`S ⊆ A`、`x` 与 `x'` 在 `A` 上一致 ⟹ `mass S p x = mass S p x'`。

⟹ `mass S` 只经 `x|_S` 看 `x`；`A` 外（甚至 `A \ S`）的坐标不进入 `mass`。 -/
theorem mass_ignores_tail_of_S_subset_A {A S : Finset V} (hSA : S ⊆ A)
    (p : (V → α) → ℝ) {x x' : V → α} (h : ∀ u ∈ A, x u = x' u) :
    Fate.DAGFactorization.mass S p x = Fate.DAGFactorization.mass S p x' :=
  Fate.DAGFactorization.mass_congr S p fun u hu => h u (hSA hu)

/-- ⭐⭐⭐⭐ **V2：`mass S` 与 `A` 外的取值无关**（`S ⊆ A`）。

⟹ **正面推翻题面卡点**：`mass S p x` 里没有 `x_tail` 这个自由变量。 -/
theorem mass_ignores_out_of_A {A S : Finset V} (hSA : S ⊆ A)
    (p : (V → α) → ℝ) (wA : ↥A → α) (xt xt' : ↥(outSet A) → α) :
    Fate.DAGFactorization.mass S p (merge A wA xt)
      = Fate.DAGFactorization.mass S p (merge A wA xt') := by
  refine Fate.DAGFactorization.mass_congr S p fun u hu => ?_
  have huA : u ∈ A := hSA hu
  rw [merge_mem_A A wA xt ⟨u, huA⟩, merge_mem_A A wA xt' ⟨u, huA⟩]

/-! ===========================================================================
  §2  **V3**：`hOut` ⟹ `A` 外求和与 `x` 完全无关
  =========================================================================== -/

/-- ⭐⭐⭐ **V3：`∑_{t} ∏ v ∈ outSet A, ψ v (glue A x t)` 与 `x` 无关**（需 `hOut`）。

**⟹ 这才是 `hOut` 的真正作用**：它让 `A` 外那部分成为 `x` 的**常数**，
从而能作为公共因子从左端的 `∑_{wA}` 外面**整体提出**。 -/
theorem pout_sum_indep_x {A : Finset V} {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R) (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A)
    (x x' : V → α) :
    (∑ t : ({u : V // u ∉ A} → α), ∏ v ∈ outSet A, ψ v (glue A x t))
      = (∑ t : ({u : V // u ∉ A} → α), ∏ v ∈ outSet A, ψ v (glue A x' t)) := by
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.prod_congr rfl fun v hv => ?_
  refine hread v _ _ fun u hu => ?_
  have hvA : v ∉ A := by
    have h1 : v ∈ Finset.univ.filter (fun x => x ∉ A) := hv
    exact (Finset.mem_filter.mp h1).2
  have huA : u ∉ A := by
    by_cases huv : u = v
    · subst huv; exact hvA
    · have hh := hOut v hvA (Finset.mem_sdiff.mpr ⟨hu, by simpa using huv⟩)
      have h2 : u ∈ Finset.univ.filter (fun x => x ∉ A) := hh
      exact (Finset.mem_filter.mp h2).2
  rw [glue_of_not_mem A x t huA, glue_of_not_mem A x' t huA]

/-! ===========================================================================
  §3  **V4**：`P1` ⟹ `P_A` 与 `A` 外无关、且取值就是 `ψ v x`
  =========================================================================== -/

/-- ⭐⭐⭐ **V4a：`P1` ⟹ `∏ v ∈ A, ψ v (merge A wA wt)` 与 `wt` 无关**。 -/
theorem pA_indep_out {A : Finset V} {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R) (hRA : ∀ v ∈ A, R v ⊆ A)
    (wA : ↥A → α) (wt wt' : ↥(outSet A) → α) :
    (∏ v ∈ A, ψ v (merge A wA wt)) = (∏ v ∈ A, ψ v (merge A wA wt')) := by
  refine Finset.prod_congr rfl fun v hv => ?_
  refine hread v _ _ fun u hu => ?_
  have huA : u ∈ A := hRA v hv hu
  rw [merge_mem_A A wA wt ⟨u, huA⟩, merge_mem_A A wA wt' ⟨u, huA⟩]

/-- ⭐⭐⭐ **V4b：`P1` ⟹ `∏ v ∈ A, ψ v (glue A x t) = ∏ v ∈ A, ψ v x`**。 -/
theorem pA_glue_eq {A : Finset V} {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R) (hRA : ∀ v ∈ A, R v ⊆ A)
    (x : V → α) (t : {u : V // u ∉ A} → α) :
    (∏ v ∈ A, ψ v (glue A x t)) = (∏ v ∈ A, ψ v x) := by
  refine Finset.prod_congr rfl fun v hv => ?_
  exact hread v _ _ fun u hu => glue_of_mem A x t (hRA v hv hu)

/-! ===========================================================================
  §4  **V5**：没有 `P1` 的显式反例  ⭐ "P1 必需"
  =========================================================================== -/

/-- ⚠⚠ **V5：`P1` 是必需的（显式反例）。**

`V = Fin 2`、`A = {0}`、`ψ 0 w := if w 1 then 2 else 1`（因子 `0` 读 `A` 外的坐标 `1`）。
两个在 `A` 上完全相同、在 `A` 外不同的世界给出**不同**的 `∏ v ∈ A, ψ v`。

⟹ 没有 `P1`，`P_A` 在 mass 的纤维内不是常数，`∑_{wA}` **不能**提出公共因子，
分解**失败**。 -/
theorem pA_depends_on_tail_without_P1 :
    ∃ (A : Finset (Fin 2)) (ψ : Fin 2 → (Fin 2 → Bool) → ℝ) (w w' : Fin 2 → Bool),
      (∀ u ∈ A, w u = w' u) ∧
      (∏ v ∈ A, ψ v w) ≠ (∏ v ∈ A, ψ v w') := by
  refine ⟨{0}, fun _ w => if w 1 then 2 else 1, (fun _ => false),
    (fun i => if i = 1 then true else false), ?_, ?_⟩
  · intro u hu
    have hu0 : u = 0 := by simpa using hu
    subst hu0; rfl
  · simp

/-- ⭐ **V5 的对偶（`hOut` 在 `A` 外的必要条件的形式）**：
`v ∈ A` 时 `R v \ {v} ⊆ A` **等价于** `R v ⊆ A`。

⟹ 题面写的 `hOut` 型条件若被错误地用于 `A` 内因子（`v ∈ A`），就**等价于 `P1`**
—— 这解释了为什么两个条件看起来"不够"：它们其实是**同一个引擎**在两个不同的
顶点集上运行，缺一不可，而不是互相替代。 -/
theorem readset_minus_self_sub_A_iff {A : Finset V} {R : V → Finset V} {v : V}
    (hv : v ∈ A) : R v ⊆ A ↔ R v \ {v} ⊆ A := by
  constructor
  · intro h; exact Finset.Subset.trans (Finset.sdiff_subset) h
  · intro h u hu
    by_cases huv : u = v
    · subst huv; exact hv
    · exact h (Finset.mem_sdiff.mpr ⟨hu, by simpa using huv⟩)

/-! ===========================================================================
  §5  **V5' 主结果**：`P1 + hOut` 下的真正可分离 mass 分解
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **V5'：真正有尾块的 `mass` 乘法分解**。

**⚠ 一个重要细节（判决的一部分）**：本条**只用 `P1`**，`hOut` **完全没被用到**
（Lean 的 unused-variable linter 会提示）。这说明：

* 「`mass` 拆成 `A 内乘积 × A 外求和`」**只需要 `P1`**；
* `hOut` 的用处在 **`V5''`** —— 它保证第二个求和**与 `wA` 无关**，
  从而题面那个"自由 `wA`"能被消去、真正**提出**为公共因子。

两者分工明确，**都不可省**（缺 `P1` 见 V5 反例；缺 `hOut` 则 V5'' 不成立）。

**前提**：
* `hread : ReadSet ψ R`；
* `hRA : ∀ v ∈ A, R v ⊆ A`（`P1`，`A` 内因子父闭）；
* `hOut : ∀ v ∉ A, R v \ {v} ⊆ outSet A`（下面主证明不用，见上）。

**结论**：
`mass A (∏ v, ψ v) x = (∏ v ∈ A, ψ v x) * (∑_{t : Aᶜ → α} ∏ v ∈ outSet A, ψ v (glue A x t))`。

**⟹ 「`A` 内和」×「`A` 外和」的真正乘法分离，且 `A` 外和由 `V3` 与 `x` 无关。**
**⟹ 与 `mass_dcomp_tail` 不同，这里 `hOut` 是 `R v \ {v}` 口径，`v ∉ A` 可以
出现在 `R v` 中，因此 `outSet A` 可以非空（真正有尾块），不坍缩。** -/
theorem mass_separable_A {A : Finset V} {ψ : V → (V → α) → ℝ} {R : V → Finset V}
    (hread : ReadSet ψ R) (hRA : ∀ v ∈ A, R v ⊆ A)
    (_hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A) (x : V → α) :
    Fate.DAGFactorization.mass A (fun w => ∏ v, ψ v w) x
      = (∏ v ∈ A, ψ v x)
        * (∑ t : ({u : V // u ∉ A} → α), ∏ v ∈ outSet A, ψ v (glue A x t)) := by
  classical
  rw [Fate.View19.mass_eq_sum_glue A (fun w => ∏ v, ψ v w) x]
  have hstep : ∀ t : ({u : V // u ∉ A} → α),
      (∏ v, ψ v (glue A x t))
        = (∏ v ∈ A, ψ v x) * (∏ v ∈ outSet A, ψ v (glue A x t)) := by
    intro t
    rw [prod_split_in_out ψ A (glue A x t), pA_glue_eq hread hRA x t]
  simp only [hstep]
  rw [Finset.mul_sum]

/-- 辅助：`Aᶜ` 元素映射到 `outSet A` 元素。 -/
def complToOut {A : Finset V} (u : {u : V // u ∉ A}) : ↥(outSet A) :=
  ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ u.1, u.2⟩⟩

/-- 辅助：`outSet A` 元素映射到 `Aᶜ` 元素。 -/
def outToCompl {A : Finset V} (v : ↥(outSet A)) : {u : V // u ∉ A} :=
  ⟨v.1, by
    have hv := v.2
    unfold outSet at hv
    exact (Finset.mem_filter.mp hv).2⟩

theorem complToOut_outToCompl {A : Finset V} (v : ↥(outSet A)) :
    complToOut (outToCompl v) = v := Subtype.ext rfl

theorem outToCompl_complToOut {A : Finset V} (u : {u : V // u ∉ A}) :
    outToCompl (complToOut u) = u := Subtype.ext rfl

/-- ⭐⭐⭐ **V5''：`A` 外和一端也写成 `merge` 形式**（`↥(outSet A)` 索引）。

关键是后者**与 `wA` 无关**（由 `hOut`），于是题面那个"自由 `wA`"被消除。 -/
theorem mass_separable_A_merge_shape {A : Finset V} {ψ : V → (V → α) → ℝ}
    {R : V → Finset V}
    (hread : ReadSet ψ R) (hRA : ∀ v ∈ A, R v ⊆ A)
    (hOut : ∀ v, v ∉ A → R v \ {v} ⊆ outSet A)
    (wA : ↥A → α) (x : V → α) :
    Fate.DAGFactorization.mass A (fun w => ∏ v, ψ v w) x
      = (∏ v ∈ A, ψ v x)
        * (∑ wt : (↥(outSet A) → α), ∏ v ∈ outSet A, ψ v (merge A wA wt)) := by
  classical
  rw [mass_separable_A hread hRA hOut x]
  congr 1
  refine Finset.sum_bij
    (fun (t : ({u : V // u ∉ A} → α)) (_ : t ∈ Finset.univ) =>
      (fun v : ↥(outSet A) => t (outToCompl v)))
    ?_ ?_ ?_ ?_
  · intro t _; exact Finset.mem_univ _
  · intro t _ t' _ h
    funext u
    have := congrFun h (complToOut u)
    simpa [complToOut, outToCompl] using this
  · intro wt _
    refine ⟨(fun u : {u : V // u ∉ A} => wt (complToOut u)), Finset.mem_univ _, ?_⟩
    funext v
    have hstep : (fun u : {u : V // u ∉ A} => wt (complToOut u)) (outToCompl v)
        = wt (complToOut (outToCompl v)) := rfl
    rw [hstep, complToOut_outToCompl]
  · intro t _
    refine Finset.prod_congr rfl fun v hv => ?_
    refine hread v _ _ fun u hu => ?_
    have hvA : v ∉ A := (outToCompl ⟨v, hv⟩).2
    have gov : glue A x t v = t (outToCompl ⟨v, hv⟩) := glue_of_not_mem A x t hvA
    have mov : merge A wA (fun v : ↥(outSet A) => t (outToCompl v)) v
        = t (outToCompl ⟨v, hv⟩) := merge_mem_out A wA _ ⟨v, hv⟩
    have hvv : glue A x t v = merge A wA (fun v : ↥(outSet A) => t (outToCompl v)) v := by
      rw [gov, mov]
    by_cases huv : u = v
    · subst huv; exact hvv
    · have huOut : u ∈ outSet A :=
        hOut v hvA (Finset.mem_sdiff.mpr ⟨hu, by simpa using huv⟩)
      have guu : glue A x t u = t (outToCompl ⟨u, huOut⟩) :=
        glue_of_not_mem A x t (outToCompl ⟨u, huOut⟩).2
      have muu : merge A wA (fun v : ↥(outSet A) => t (outToCompl v)) u
          = t (outToCompl ⟨u, huOut⟩) := merge_mem_out A wA _ ⟨u, huOut⟩
      rw [guu, muu]

/-! ===========================================================================
  §6  **V6 / V7**：`P1` 与 `hOut` **不**导致坍缩
  =========================================================================== -/

/-- ⭐⭐ **V6：`hOut` 与 `A ≠ univ` 相容**（`A` 外因子可以是零读集，且 `outSet A` 非空）。

⟹ `hOut` **不**蕴含 `A = univ` —— 与 `hTail` 关键不同（`hTail_implies_univ`）。 -/
theorem hOut_nontrivial {A : Finset V} (h : A ≠ Finset.univ) :
    ∃ R : V → Finset V, (∀ v, v ∉ A → R v \ {v} ⊆ outSet A) ∧
      (outSet A).Nonempty := by
  classical
  refine ⟨fun _ => (∅ : Finset V), fun v _ => by simp, ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, v ∉ A := by
    by_contra hc
    push Not at hc
    exact h (Finset.eq_univ_of_forall hc)
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩

/-- ⭐⭐ **V7：`P1` 与 `outSet A` 非空相容**（`P1` 对 `A` 外的 `R` 一无所言）。

取 `A ≠ univ`、`A` 内因子零读集、`A` 外因子读 `univ`：`P1` 成立、`outSet A` 非空。 -/
theorem P1_nontrivial {A : Finset V} (h : A ≠ Finset.univ) :
    ∃ R : V → Finset V, (∀ v ∈ A, R v ⊆ A) ∧ (outSet A).Nonempty := by
  classical
  refine ⟨fun v => if v ∈ A then (∅ : Finset V) else {v}, ?_, ?_⟩
  · intro v hv
    show (if v ∈ A then (∅ : Finset V) else {v}) ⊆ A
    rw [if_pos hv]
    simp
  · obtain ⟨v, hv⟩ : ∃ v, v ∉ A := by
      by_contra hc
      push Not at hc
      exact h (Finset.eq_univ_of_forall hc)
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩

/-- ⭐⭐⭐ **V7'：条件 C = `P1 ∧ hOut` 可同时成立且 `A ≠ univ`。**

⟹ **存在不坍缩的条件 C**，且此时 `mass_separable_A` 给出真正的乘法分解。 -/
theorem condC_nontrivial {A : Finset V} (h : A ≠ Finset.univ) :
    ∃ R : V → Finset V,
      (∀ v ∈ A, R v ⊆ A) ∧ (∀ v, v ∉ A → R v \ {v} ⊆ outSet A) ∧
      (outSet A).Nonempty := by
  classical
  refine ⟨fun v => if v ∈ A then (∅ : Finset V) else {v}, ?_, ?_, ?_⟩
  · intro v hv
    show (if v ∈ A then (∅ : Finset V) else {v}) ⊆ A
    rw [if_pos hv]
    simp
  · intro v hv
    show (if v ∈ A then (∅ : Finset V) else {v}) \ {v} ⊆ outSet A
    rw [if_neg hv]
    simp
  · obtain ⟨v, hv⟩ : ∃ v, v ∉ A := by
      by_contra hc
      push Not at hc
      exact h (Finset.eq_univ_of_forall hc)
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩

end Fate.GraphToProbView7
