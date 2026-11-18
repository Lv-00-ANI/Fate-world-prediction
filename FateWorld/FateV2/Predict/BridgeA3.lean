import FateWorld.FateV2.Predict.FactorRecursionRouteB_Obligations
import FateWorld.FateV2.Predict.BridgeA1
import Mathlib.Tactic.LinearCombination

/-!
  # Predict · BridgeA3

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeA3.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorRecursionRouteB_Obligations, BridgeA1
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeA3` —— **清单 A3：乘性 `φ` 的边缘化分离**

  ## 0 一句话结论

  「若 `p x = ∏_v φ_v x`、`φ_v` 只读 `pa(v)`，则对 `S ⊆ nd(v)` 边缘化后仍分解」
  **可以证明——但要对「仍分解」给出正确的口径**：

  * ✅ **可以证的**：以 `T := insert v (nd v)` 为可提出因子集，
    $$ \mathrm{mass}_{\mathrm{nd}(v)}\,p\,x
        = \Bigl(\prod_{w\in T}\varphi_w(x)\Bigr)\cdot
          \mathrm{mass}_{\mathrm{nd}(v)}\Bigl(\prod_{w\notin T}\varphi_w\Bigr)x . $$
    即 `φ_v` **连同全部非后代因子**可以从边缘化中提出，**残余恰为「后代因子」的乘积**。
  * ❌ **不能证的**：把残余 `∏_{w\notin T} φ_w` 也整体提出（那要求
    `∀ w ≠ v, pa(w) ⊆ nd(v)`，`Fate/FactorRecursionRouteB_Obligations`
    已在链 `0→1→2` 上机器证伪）。

  ⟹ A3 的诚实定稿：**A3 是一条已证的「单点（准确说是「非后代块」）剥离」定理
  加上一个精确的残余逃逸刻画**，不是「`Factorizes ⟹ LMG`」的一步。

  ## 1 可交付边界（逐行标状态）

  | 编号 | 陈述 | 状态 | 依赖 |
  |---|---|---|---|
  | **A3.1** | `mass (nd v) p x = φ_v x · mass (nd v) (∏_{w≠v} φ_w) x` | ✅ **零缺口** | `mass_factorizes_single'` + `pa ⊆ nd` |
  | **A3.2** | 同上，`S = insert v (nd v)` | ✅ **零缺口** | 同上 + `mem_insert_of_mem` |
  | **A3.3** | 残余**整体**只读 `S` ⟹ `mass S p = |α|^(|V|−|S|) · p` | ✅ **零缺口** | `mass_prod_reads` |
  | **A3.4** | `f` 只读 `nd v` ⟹ `mass (nd v) f = |α| · mass (insert v (nd v)) f` | ✅ **零缺口** | `mass_of_reads` + 指数算术 |
  | **A3.5** | `(★) ∀ w ≠ v, pa(w) ⊆ nd(v)` | ❌ **假** | 链反例（本文 §8.1）|
  | **A3.6** | `Factorizes ⟹ LMG` | ❌ **假** | 引用 `factorizes_implies_LMG_false` |
  | ⭐ **A3.CORE** | 「非后代块」剥离（§0 的公式），`T = insert v (nd v)` | ✅ **零缺口** | `pa ⊆ nd` + `pa_closed on nd` |
  | ⭐ **A3.RED** | `∏_T φ ≠ 0` 时，`v` 处的 `LMG` 等式 **⟺** 残余上的同一等式 | ✅ **零缺口** | A3.CORE + 代数 |

  **A3.CORE / A3.RED 是本文相对 `Bridge-A3方案修正.md` §3 的增量**：
  修正案只到「剥离 `φ_v`」；本文把「整块非后代因子」一起提出，
  并把 `LMG` 在 `v` 处的失败**精确定位到残余（后代因子）**。

  ## 2 审计：「`hfac` 用在哪一步？」

  **本文没有任何 `dSep` 前件**（A3 本身不含 `dSep`），只有因子分解前件
  `h : Factorizes p G`。它在证明里被消费 **恰好两处**（都在 §3 起头的
  `set φ := Classical.choose h`）：

  | 消费点 | 内容 | 用在哪 |
  |---|---|---|
  | `(Classical.choose_spec h).2` | `p x = ∏_w φ_w x` | 把 `p` 换成乘积（`a3_mass_prod_out` 的入口）|
  | `(Classical.choose_spec h).1` | `φ_v` 只读 `pa G v` | 证明「`∏_{w∈T} φ_w` 在 `S`-纤维上为常数」|

  **没有第三个消费点**，`hfac` 的结论 `LMG` **没有**被写进任何前件；
  本文**不**证明 `Factorizes ⟹ LMG`（§8.2 引用既有证伪）。

  ## 3 与 `Fate/BridgeA4.lean` 的关系（诚实）

  * `BridgeA4` 走的是**修正版定义**（`FactorizesL`：读集 `{v} ∪ pa(v)`；
    `LGMC`），并已证 `factorizesL_implies_LGMc`；
  * 本文走**原有定义**（`FactorRecursionRouteB.Factorizes`：读集 `pa(v)`），
    给出它的**精确能力边界**。二者的差别正是 `φ_v` 是否读 `v` 自身；
  * 本文不依赖 `BridgeA4`（该文件当前另有语法错误，与本文件无关）。

  **纪律**：单文件 `lake env lean Fate/BridgeA3.lean` 验证 · 不改 `Fate.lean` ·
  不改已有模块 · 零 `sorry` · 不用 `mass` 塔性质（`tower_*` 不出现）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeA3

open Finset Fate.DAGFactorization FateV2.Predict.FactorRecursionRouteB

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §1 图论地基（零缺口）

  这两条已经把「`S ⊆ nd v`」所需的全部图论输入备齐：
  **`pa ⊆ nd`（`BridgeA1.pa_subset_nonDescendants`，即被证伪的 A1 的*反面*）
  与「`nd` 对取父封闭」（`BridgeA1.pa_subset_nonDescendants_of_mem`）**。
  =========================================================================== -/

/-- **A3.g0**：`v ∉ nd(v)`（`nonDescendants` 定义里 `w ≠ v` 的那一半）。 -/
theorem a3_not_mem_nd_self (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    v ∉ G.nonDescendants v := by
  rw [FateV2.Modeling.Graph.DAG.nonDescendants, Finset.mem_filter]
  rintro ⟨-, -, hne⟩
  exact hne rfl

/-- ⭐ **A3.g1（A3.CORE 的图论引擎）**：取 `T := insert v (nd v)`，
则 `T` 中**每个**顶点的父集都落在 `nd(v)` 内：

$$\forall w \in \{v\}\cup \mathrm{nd}(v),\ \mathrm{pa}(w) \subseteq \mathrm{nd}(v).$$

两项来源不同，这就是 A1 被证伪的**净收益**：
* `w = v`：用 `pa(v) ⊆ nd(v)`（`BridgeA1.pa_subset_nonDescendants`）；
* `w ∈ nd(v)`：用「`nd` 对取父封闭」（`BridgeA1.pa_subset_nonDescendants_of_mem`）。 -/
theorem a3_pa_subset_nd_of_mem_insert (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    ∀ w ∈ (insert v (G.nonDescendants v) : Finset V), pa G w ⊆ G.nonDescendants v := by
  intro w hw
  rw [Finset.mem_insert] at hw
  rcases hw with h | hw
  · exact h.symm ▸ BridgeA1.pa_subset_nonDescendants G v
  · exact BridgeA1.pa_subset_nonDescendants_of_mem hw

/-! ===========================================================================
  §2 一般分离引擎（零缺口）

  「乘性 `φ` 的边缘化分离」的**唯一**代数内容：乘积按读集分块，
  在 `S`-纤维上为常数的那一块可以提出 `mass`。
  =========================================================================== -/

/-- **A3.e0**：乘积按 `T` / 补集分块。 -/
lemma a3_prod_split (φ : V → (V → α) → ℝ) (T : Finset V) (y : V → α) :
    (∏ w, φ w y) = (∏ w ∈ T, φ w y) * ∏ w ∈ (univ \ T : Finset V), φ w y := by
  rw [← Finset.prod_sdiff (Finset.subset_univ T), mul_comm]

/-- **A3.e1**：若 `T` 中每因子只读 `S`（即 `pa w ⊆ S`），则整块 `∏_{w∈T} φ_w`
在 `S`-纤维上为常数。 -/
lemma a3_reads_of_pa_subset {G : FateV2.Modeling.Graph.DAG V} {φ : V → (V → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    {S T : Finset V} (hT : ∀ w ∈ T, pa G w ⊆ S) :
    ∀ a b : V → α, (∀ u ∈ S, a u = b u) → (∏ w ∈ T, φ w a) = (∏ w ∈ T, φ w b) :=
  fun a b hab => Finset.prod_congr rfl (fun w hw => hφ w a b (fun u hu => hab u (hT w hw hu)))

/-- ⭐⭐ **A3.e2（分离引擎）**：若 `T` 中每因子读集 `pa w ⊆ S`，则

$$\mathrm{mass}_S\Bigl(\prod_{w}\varphi_w\Bigr)x
   =\Bigl(\prod_{w\in T}\varphi_w(x)\Bigr)\cdot
    \mathrm{mass}_S\Bigl(\prod_{w\notin T}\varphi_w\Bigr)x .$$

**证明**：`a3_prod_split` 分块 ⟹ `mass_congr_fun` 代回 ⟹
`DAGFactorization.mass_mul`（`a3_reads_of_pa_subset` 提供只读性）。**零缺口**。 -/
theorem a3_mass_prod_out {φ : V → (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    (S T : Finset V) (hT : ∀ w ∈ T, pa G w ⊆ S) (x : V → α) :
    mass S (fun y => ∏ w, φ w y) x
      = (∏ w ∈ T, φ w x) * mass S (fun y => ∏ w ∈ (univ \ T : Finset V), φ w y) x := by
  have hp : ∀ y, (∏ w, φ w y) = (∏ w ∈ T, φ w y) * ∏ w ∈ (univ \ T : Finset V), φ w y :=
    a3_prod_split φ T
  rw [mass_congr_fun S hp x]
  exact mass_mul S (fun y => ∏ w ∈ T, φ w y) (fun y => ∏ w ∈ (univ \ T), φ w y) x
    (a3_reads_of_pa_subset hφ hT)

/-! ===========================================================================
  §3 **A3.1 / A3.2：单因子剥离**（零缺口）

  这两条是 `Bridge-A3方案修正.md` §3 的 A3.1/A3.2 的正式落地。
  `hS : pa v ⊆ S` 由 `pa ⊆ nd` **免费**提供（A1 被证伪的正面红利）。
  =========================================================================== -/

/-- ⭐ **A3.1**：`S := nd(v)` 时剥离 `φ_v`：

$$\mathrm{mass}_{\mathrm{nd}(v)}\,p\,x
   =\varphi_v(x)\cdot\mathrm{mass}_{\mathrm{nd}(v)}
      \Bigl(\prod_{w\neq v}\varphi_w\Bigr)x .$$

`hS` 由 `BridgeA1.pa_subset_nonDescendants`（A1 的**反面**）提供。 -/
theorem a3_1_peel_nd {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (h : Factorizes p G) (v : V) (x : V → α) :
    mass (G.nonDescendants v) p x
      = (Classical.choose h) v x
        * mass (G.nonDescendants v)
            (fun y => ∏ w ∈ (univ.erase v : Finset V), (Classical.choose h) w y) x :=
  mass_factorizes_single' h v (BridgeA1.pa_subset_nonDescendants G v) x

/-- ⭐ **A3.2**：`S := insert v (nd(v))` 时剥离 `φ_v`。
多钉一维 `v` 后 `pa v ⊆ insert v (nd v)` 仍成立（`pa v ⊆ nd v` 且
`nd v ⊆ insert v (nd v)`）。 -/
theorem a3_2_peel_insert_nd {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (h : Factorizes p G) (v : V) (x : V → α) :
    mass (insert v (G.nonDescendants v)) p x
      = (Classical.choose h) v x
        * mass (insert v (G.nonDescendants v))
            (fun y => ∏ w ∈ (univ.erase v : Finset V), (Classical.choose h) w y) x := by
  refine mass_factorizes_single' h v ?_ x
  intro u hu
  exact Finset.mem_insert_of_mem (BridgeA1.pa_subset_nonDescendants G v hu)

/-! ===========================================================================
  §4 **A3.3：残余整体只读 ⟹ 常数因子化**（零缺口）

  这是「残余**确实**可整体提出」的**充分条件**——它在一般 DAG 上
  **对 `T = insert v (nd v)` 成立**（§1 的 `a3_pa_subset_nd_of_mem_insert`），
  这正是 §5 的 A3.CORE 得以成功的全部原因。
  =========================================================================== -/

/-- ⭐ **A3.3a**：若 `T` 中每因子读集 `pa w ⊆ S`，则残余是整块常数：

$$\mathrm{mass}_S\Bigl(\prod_{w\in T}\varphi_w\Bigr)x
   =|\alpha|^{|V|-|S|}\cdot\prod_{w\in T}\varphi_w(x).$$
（`FactorRecursionRouteB.mass_prod_reads` 的读集版本。） -/
theorem a3_3_residue_reads {G : FateV2.Modeling.Graph.DAG V} {φ : V → (V → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    (S T : Finset V) (hT : ∀ w ∈ T, pa G w ⊆ S) (x : V → α) :
    mass S (fun y => ∏ w ∈ T, φ w y) x
      = (Fintype.card α : ℝ) ^ (Fintype.card V - S.card) * ∏ w ∈ T, φ w x :=
  mass_prod_reads S φ T x (fun w hw a b hab => hφ w a b (fun u hu => hab u (hT w hw hu)))

/-- ⭐⭐ **A3.3b（全剥离）**：若**所有**因子的读集都在 `S` 内，则

$$\mathrm{mass}_S\,p\,x = |\alpha|^{|V|-|S|}\cdot p(x).$$

即「整条乘积链在 `S`-纤维上是常数」。**零缺口**。 -/
theorem a3_3_full_peel {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (h : Factorizes p G) (S : Finset V)
    (hS : ∀ w, pa G w ⊆ S) (x : V → α) :
    mass S p x = (Fintype.card α : ℝ) ^ (Fintype.card V - S.card) * p x := by
  classical
  set φ := Classical.choose h with hφdef
  have hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y :=
    (Classical.choose_spec h).1
  have hp : ∀ y, p y = ∏ w, φ w y := (Classical.choose_spec h).2
  rw [mass_congr_fun S hp x, hp x]
  exact a3_3_residue_reads hφ S univ (fun w _ => hS w) x

/-! ===========================================================================
  §5 **A3.4：`nd(v)` 与 `insert v (nd v)` 之间的步进关系**（零缺口）

  ⚠ **方向警告**（修正案 §3 记录过的踩坑）：多钉一维使纤维**变小**，
  故指数**减 1**，得到
  $$\mathrm{mass}_{\mathrm{nd}(v)}\,f\,x
     =|\alpha|\cdot \mathrm{mass}_{\mathrm{nd}(v)\cup\{v\}}\,f\,x ,$$
  **不是**反过来。前提 `v ∉ nd v`（`a3_not_mem_nd_self`）。
  =========================================================================== -/

/-- ⭐ **A3.4**：`f` 只读 `nd(v)` 时的步进关系。**零缺口**。 -/
theorem a3_4_mass_insert_of_reads_nd (G : FateV2.Modeling.Graph.DAG V)
    (f : (V → α) → ℝ) (v : V) (y : V → α)
    (hf : ∀ a b : V → α, (∀ u ∈ G.nonDescendants v, a u = b u) → f a = f b) :
    mass (G.nonDescendants v) f y
      = (Fintype.card α : ℝ) * mass (insert v (G.nonDescendants v)) f y := by
  classical
  set S := G.nonDescendants v with hS
  have hv : v ∉ S := a3_not_mem_nd_self G v
  have hf' : ∀ a b : V → α, (∀ u ∈ insert v S, a u = b u) → f a = f b :=
    fun a b hab => hf a b (fun u hu => hab u (Finset.mem_insert_of_mem hu))
  rw [mass_of_reads S f y hf, mass_of_reads (insert v S) f y hf',
    Finset.card_insert_of_notMem hv]
  have hlt : S.card < Fintype.card V := by
    have hne : S ≠ (Finset.univ : Finset V) := fun h => hv (h ▸ Finset.mem_univ v)
    have hss : S ⊂ (Finset.univ : Finset V) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hne⟩
    have := Finset.card_lt_card hss
    simpa using this
  rw [show Fintype.card V - S.card = (Fintype.card V - (S.card + 1)) + 1 by omega]
  ring

/-! ===========================================================================
  §6 ⭐⭐⭐ **A3.CORE：非后代块的整体剥离**（本文的增量，零缺口）

  `T := insert v (nd v)` 时 `a3_pa_subset_nd_of_mem_insert` 让 §2 的引擎
  **直接**给出非后代块的整体提出，残余**恰是后代因子**。
  =========================================================================== -/

/-- ⭐⭐⭐ **A3.CORE（主定理）**

$$\boxed{\ \mathrm{mass}_{\mathrm{nd}(v)}\,p\,x
  =\Bigl(\prod_{w\,\in\,\{v\}\cup\mathrm{nd}(v)}\varphi_w(x)\Bigr)\cdot
   \mathrm{mass}_{\mathrm{nd}(v)}
     \Bigl(\prod_{w\,\notin\,\{v\}\cup\mathrm{nd}(v)}\varphi_w\Bigr)x\ }$$

**意义**：
* 左端是 **`LMG` 用的边缘**（`nd ∪ pa = nd`，见 `a3_lmg_reduced_iff`）；
* 中间因子 `∏_{w∈T} φ_w` 是**全部非后代因子**（含 `φ_v` 自己）；
* 残余 `∏_{w∉T}` **只含 `v` 的后代因子**——这就是「逃逸」的确切位置。

⟹ 「边缘化后仍分解」在这一口径下**成立**：剥离后仍是一个「常数块 × 残余乘积的 `mass`」，
乘积结构没有被破坏。

**消费点**：`hfac` 的 `hp`（`p = ∏ φ`）与 `hφ`（只读 `pa`）各一次；
图论用 `a3_pa_subset_nd_of_mem_insert`。**不用塔性质**。 -/
theorem a3_mass_nd_factorizes {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (h : Factorizes p G) (v : V) (x : V → α) :
    mass (G.nonDescendants v) p x
      = (∏ w ∈ (insert v (G.nonDescendants v) : Finset V), (Classical.choose h) w x)
        * mass (G.nonDescendants v)
            (fun y => ∏ w ∈ (univ \ insert v (G.nonDescendants v) : Finset V),
              (Classical.choose h) w y) x := by
  classical
  rw [mass_congr_fun (G.nonDescendants v) (Classical.choose_spec h).2 x]
  exact a3_mass_prod_out (Classical.choose_spec h).1 (G.nonDescendants v) _
    (a3_pa_subset_nd_of_mem_insert G v) x

/-- ⭐⭐ **A3.CORE′**：`A3.CORE` 在 `S := insert v (nd v)` 上的同款分解
（供 `LMG` 右端的 `mass` 对齐用）。 -/
theorem a3_mass_insert_nd_factorizes {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (h : Factorizes p G) (v : V) (x : V → α) :
    mass (insert v (G.nonDescendants v)) p x
      = (∏ w ∈ (insert v (G.nonDescendants v) : Finset V), (Classical.choose h) w x)
        * mass (insert v (G.nonDescendants v))
            (fun y => ∏ w ∈ (univ \ insert v (G.nonDescendants v) : Finset V),
              (Classical.choose h) w y) x := by
  classical
  rw [mass_congr_fun (insert v (G.nonDescendants v)) (Classical.choose_spec h).2 x]
  exact a3_mass_prod_out (Classical.choose_spec h).1 (insert v (G.nonDescendants v)) _
    (fun w hw => Finset.Subset.trans (a3_pa_subset_nd_of_mem_insert G v w hw)
      (Finset.subset_insert v _)) x

/-- ⭐⭐ **A3.CORE″**：三条分解的形式汇总（`p` 本身、`mass nd`、`mass insert nd`）。
三者的**公共常数因子完全相同**，都是 `∏_{w∈T} φ_w x`。 -/
theorem a3_triple {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (h : Factorizes p G) (v : V) (x : V → α) :
    p x = (∏ w ∈ (insert v (G.nonDescendants v) : Finset V), (Classical.choose h) w x)
            * ∏ w ∈ (univ \ insert v (G.nonDescendants v) : Finset V),
                (Classical.choose h) w x
    ∧ mass (G.nonDescendants v) p x
        = (∏ w ∈ (insert v (G.nonDescendants v) : Finset V), (Classical.choose h) w x)
          * mass (G.nonDescendants v)
              (fun y => ∏ w ∈ (univ \ insert v (G.nonDescendants v) : Finset V),
                (Classical.choose h) w y) x
    ∧ mass (insert v (G.nonDescendants v)) p x
        = (∏ w ∈ (insert v (G.nonDescendants v) : Finset V), (Classical.choose h) w x)
          * mass (insert v (G.nonDescendants v))
              (fun y => ∏ w ∈ (univ \ insert v (G.nonDescendants v) : Finset V),
                (Classical.choose h) w y) x := by
  refine ⟨?_, a3_mass_nd_factorizes h v x, a3_mass_insert_nd_factorizes h v x⟩
  rw [(Classical.choose_spec h).2 x]
  exact a3_prod_split (Classical.choose h) _ x

/-- **纯代数**：公共常数因子 `A ≠ 0` 时，`A R · A B = A C · A B ↔ R B = C B`。 -/
lemma a3_algebra_key (A R B C : ℝ) (hA : A ≠ 0) :
    (A * R) * (A * B) = (A * C) * (A * B) ↔ R * B = C * B := by
  constructor
  · intro hh
    have h2 : A * A * (R * B) = A * A * (C * B) := by linear_combination hh
    have hAA : A * A ≠ 0 := mul_ne_zero hA hA
    exact mul_left_cancel₀ hAA h2
  · intro hh
    have h2 : A * A * (R * B) = A * A * (C * B) := by rw [hh]
    linear_combination h2

/-- ⭐⭐⭐ **A3.RED（精确残余归约）**：设 `T := insert v (nd v)`，
`R := ∏_{w∉T} φ_w`（**后代因子**的乘积）。若 `∏_{w∈T} φ_w(x) ≠ 0`，则

$$ \underbrace{p(x)\cdot \mathrm{mass}_{\mathrm{nd}}p\,x
     =\mathrm{mass}_{\{v\}\cup\mathrm{nd}}p\,x\cdot \mathrm{mass}_{\mathrm{nd}}p\,x}
   _{\text{即 }v\text{ 处的 }LMG\text{ 等式}}
 \iff
  R(x)\cdot \mathrm{mass}_{\mathrm{nd}}R\,x
     =\mathrm{mass}_{\{v\}\cup\mathrm{nd}}R\,x\cdot \mathrm{mass}_{\mathrm{nd}}R\,x . $$

**含义（这是 A3 能说的最强的话）**：`Factorizes` 下的 `LMG` 失败**完全**发生在残余
（后代因子）上；非后代块已被 A3.CORE **精确分离掉**。`A3.5`（§8.1）说明
这个残余在一般 DAG 上**非平凡**，故 `Factorizes ⟹ LMG` 假（§8.2）。

**消费点**：`hfac` 的两条见证（经 `A3.CORE″`）+ 图论（经 `A3.CORE″`）。**零缺口**。 -/
theorem a3_lmg_reduced_to_residue {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    (h : Factorizes p G) (v : V) (x : V → α)
    (hne : (∏ w ∈ (insert v (G.nonDescendants v) : Finset V), (Classical.choose h) w x) ≠ 0) :
    ((p x * mass (G.nonDescendants v) p x
        = mass (insert v (G.nonDescendants v)) p x * mass (G.nonDescendants v) p x)
      ↔ ((∏ w ∈ (univ \ insert v (G.nonDescendants v) : Finset V), (Classical.choose h) w x)
            * mass (G.nonDescendants v)
                (fun y => ∏ w ∈ (univ \ insert v (G.nonDescendants v) : Finset V),
                  (Classical.choose h) w y) x
          = mass (insert v (G.nonDescendants v))
              (fun y => ∏ w ∈ (univ \ insert v (G.nonDescendants v) : Finset V),
                (Classical.choose h) w y) x
            * mass (G.nonDescendants v)
                (fun y => ∏ w ∈ (univ \ insert v (G.nonDescendants v) : Finset V),
                  (Classical.choose h) w y) x)) := by
  classical
  obtain ⟨h1, h2, h3⟩ := a3_triple h v x
  rw [h1, h2, h3]
  exact a3_algebra_key _ _ _ _ hne

/-! ===========================================================================
  §7 **A3.5（口径化简）：`LMG` 不含 `pa` 的等价形式**（零缺口）

  由 A1 被证伪得到的 `nd ∪ pa = nd`，`LMG` 定义中的 `nd ∪ pa` 可以整体消掉。
  **注意**：这是 `↔`（真值不变），**不能**救 `Factorizes ⟹ LMG`（§8.2）。
  =========================================================================== -/

/-- ⭐ **A3.5**：`LMG` 与「无 `pa` 形式」等价。 -/
theorem a3_lmg_reduced_iff (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) :
    LMG p G ↔ ∀ v : V, ∀ y : V → α,
      p y * mass (G.nonDescendants v) p y
        = mass (insert v (G.nonDescendants v)) p y * mass (G.nonDescendants v) p y := by
  unfold LMG
  simp only [BridgeA1.nonDescendants_union_pa]

/-! ===========================================================================
  §8 ❌ **两道墙**（都是「假」，不是「未证」）
  =========================================================================== -/

/-- ❌ **A3.6 的第一道墙**：残余因子读集**确实**会逃出 `nd(v)`。

链 `0→1→2` 上取 `v = 1`：`nd(1) = {0}`，而 `pa(2) = {1}`，`1 ∉ {0}`。
故 `(★) ∀ w ≠ v, pa w ⊆ nd v` **假**，残余不能整体提出。 -/
theorem a3_barrier_residue :
    ¬ (∀ w : Fin 3, w ≠ 1 → pa FactorRecursionRouteB.chain3DAG w
        ⊆ FactorRecursionRouteB.chain3DAG.nonDescendants 1) := by
  intro h
  have h2 : (1 : Fin 3) ∈ pa FactorRecursionRouteB.chain3DAG 2 := by
    rw [mem_pa]; right; exact ⟨rfl, rfl⟩
  have := h 2 (by decide) h2
  rw [FactorRecursionRouteB.chain3_nd_one] at this
  rw [Finset.mem_singleton] at this
  exact absurd this (by decide)

/-- ❌❌ **A3.6（主墙）**：`Factorizes ⟹ LMG` **是假命题**（**引用**既有机器证伪，
本文不重证）。反例是链 `0→1→2` 上的常数 `p ≡ 2`。

⟹ A3 **不能**被写成「`Factorizes → LMG` 的中间步骤」；A4 必须改目标陈述
（见 `Fate/BridgeA4.lean` 的修正版 `FactorizesL ⟹ LGMC`）。 -/
theorem a3_barrier_LMG :
    ¬ (∀ (p : (Fin 3 → Bool) → ℝ),
        Factorizes p FactorRecursionRouteB.chain3DAG
          → LMG p FactorRecursionRouteB.chain3DAG) :=
  FactorRecursionRouteB.factorizes_implies_LMG_false

/-! ===========================================================================
  §9 交付清单回顾与「假证」自查

  ## 9.1 每条的「真证」证据

  | 定理 | `hfac` 消费 | 图论消费 | 塔性质 |
  |---|---|---|---|
  | `a3_1_peel_nd` | `mass_factorizes_single'` 内部（`hp`+`hφ`）| `pa ⊆ nd` | ❌ 不用 |
  | `a3_2_peel_insert_nd` | 同上 | `pa ⊆ nd` | ❌ 不用 |
  | `a3_3_full_peel` | `hp`+`hφ` | `hS`（假设）| ❌ 不用 |
  | `a3_4_mass_insert_of_reads_nd` | **无**（与前件无关，纯 `mass` 计算）| `v ∉ nd` | ❌ 不用 |
  | `a3_mass_nd_factorizes` | `hp`+`hφ` | `a3_pa_subset_nd_of_mem_insert` | ❌ 不用 |
  | `a3_mass_insert_nd_factorizes` | `hp`+`hφ` | `a3_pa_subset_nd_of_mem_insert` | ❌ 不用 |
  | `a3_lmg_reduced_to_residue` | 经 `a3_triple`（`hp`+`hφ`）| 经 `a3_triple` | ❌ 不用 |

  ## 9.2 为什么这不是「把结论写进前件」

  * `a3_mass_nd_factorizes` 的结论是**新等式**（非后代块提出 × 后代残余），
    它**不是**任何前件的改写：`Factorizes` 的前件是 `∃ φ, (只读) ∧ (p = ∏ φ)`，
    结论里出现了 `∏_{w∈T} φ_w` 与 `mass (univ \ T)` 这两个前件中**没有**的量；
  * `a3_barrier_LMG` 是**否定**（引用），不是肯定；
  * 文件内**没有**任何形如 `Factorizes → LMG` 的 `theorem` 或 `_Gap` 命名。

  ## 9.3 与清单的对照（A3 的最终定位）

  * 清单 A3 的措辞「乘性 `φ` 的边缘化分离」——**已证**（A3.CORE，§6）；
  * 清单 A3 被期待支撑的 `Factorizes ⟹ LMG`——**假**（§8.2，引用既有证伪）；
  * ⟹ A3 的产物是**有能力上限的正面定理 + 精确的残余归约 + 两道显式墙**，
    它**不进**「`Factorizes ⟹ LMG`」的证明链，而是**界定**了该链条的断点。
  =========================================================================== -/

end BridgeA3
end FateV2.Predict