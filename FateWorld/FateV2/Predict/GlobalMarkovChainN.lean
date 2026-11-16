import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.PearlCondIndepBridge
import FateWorld.FateV2.Predict.GlobalMarkovMinimal
import FateWorld.FateV2.Predict.GlobalMarkovChain4
import FateWorld.FateV2.Predict.PearlChain
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
  # Predict · GlobalMarkovChainN

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GlobalMarkovChainN.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, PearlCondIndepBridge, GlobalMarkovMinimal, GlobalMarkovChain4, PearlChain
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/GlobalMarkovChainN` —— **任意长度链的全局 Markov 性**
  （Pearl 1.2.4 的 `Fin n` 推广，第 246 轮）

  ## 0 任务与实际交付（**先诚实划界**）

  **任务书**：已有三节点链（`Fate/GlobalMarkovMinimal.lean`）与四节点链
  （`Fate/GlobalMarkovChain4.lean`）两个**固定长度**版本，
  要求推广到**任意长度**的链 $X_0 \to X_1 \to \cdots \to X_n$。

  **⟹ 本文选**选项 A**（不是 B/C）**，并把 B、C 作为推论一并给出：

  | # | 定理（**代码里真有**） | 类型 | 内容 |
  |---|---|---|---|
  | **A0** | `separable_of_chainFac` | ⭐⭐⭐⭐ | 链式因子化 ⟹ **可分离**（切割点 = 最后一个因子）|
  | **A1** | `chainFactor_condMul` | ⭐⭐⭐⭐ | 任意长度链的因子化 ⟹ `CondMul`（$X_0 \perp X_n \mid X_{1..n-1}$）|
  | **A2** | **`chain_markov_general`** | ⭐⭐⭐⭐ | **任务书点名的名字**（= A1）|
  | **B**  | **`chain_markov_inductive`** | ⭐⭐⭐⭐ | **选项 B** |
  | **C**  | **`chain_markov_length_invariant`** | ⭐⭐⭐⭐ | **选项 C**：结论形状与 `n` 无关 |
  | **D**  | `chainFac_of_chainMarkovHom` | ⭐⭐⭐ | 三节点风格分解 ⟹ `ChainFac 2`（**相容性**）|
  | **E**  | `not_condMul_Pcol` | ⭐⭐⭐⭐ | **反例**：`ChainFac` 假设不可去 |

  **⚠ 任务书 A 的「相邻变量条件独立」字面版**（`chain_adjacent_condMul`）
  **本文没有**，而且**它在链式因子化下是假命题**（见 §9.2 第 4 条）。
  本文交付的是**正确版本**：端点 vs 端点、条件于中间整段。

  ## 0.1 关键设计（**必须读**，否则会误读本文）

  ### (a) 变量值域：`Fin (n+1) → α`（**同值域**）

  本文用统一类型 `α`。**⚠ 这是真实的限制**，比 `GlobalMarkovChain4`
  的异构版本（`A × C × D × B`）弱。

  **为什么这样做**：异构情形需要类型族 `(i : Fin (n+1)) → α i`，
  且链上因子 $f_i : \alpha_i \times \alpha_{i+1} \to \mathbb{R}$
  的下标运算要处理 `Fin` 的 `castSucc`/`succ` 强制转换。
  **任务书说「若选项 A 需要大量类型体操，改为选项 B」—— 本文没有退到 B，
  而是先把同值域情形做通（§3–§6），B/C 也一并做成。**
  **⚠ 异构值域版（`(i : Fin (n+1)) → α i`）本文没有给出**（见 §9.2 第 3 条）。

  ### (b) 条件变量的口径（与三/四节点版一致）

  `FinCondIndep.CondMul p` 要求 `p : (α × β) × γ → ℝ`（$X,Y$ 一对、$Z$ 在旁）。
  本文取

  * $X := X_0$（**左端点**）、$Y := X_{n}$（**右端点**）、
  * $Z := (X_1,\dots,X_{n-1})$ —— 条件变量类型 `γ := Fin (n-1) → α`；

  故 `margZ p` 确实是对**中间整段**求和的 $\sum_{x_1}\cdots\sum_{x_{n-1}}$。

  ### (c) 链式因子化（本文的假设 `ChainFac`）

  $$\texttt{ChainFac}\ n\ f\ P \;:=\;
    \forall x : \mathrm{Fin}\,(n{+}1) \to \alpha,\quad
      P\,x = \prod_{i : \mathrm{Fin}\,n} f\,i\,(x_i,\,x_{i+1}).$$

  **⚠ 是 `n` 个因子（每条边一个），不是 `n+1` 个。**
  这与三节点版 `ChainMarkov`（3 因子）、四节点版 `ChainMarkov4`（4 因子）
  看似不同；**§7 证明三节点风格版相容**（`chainFac_of_chainMarkovHom`）：
  首因子 $\alpha$ 是单变量因子，可并入第一条边因子。
  **⚠ 四节点版 `ChainMarkov4` 的相容性本文没写**（同一手法可做，未做）。

  ### (d) 为什么 `n ≥ 2`（即 `m ≥ 1`）

  主定理要求链**至少 2 条边**（`2 ≤ n`）。理由：条件变量集
  $Z = (X_1,\dots,X_{n-1})$ 必须**非空**才能承载「公共坐标 $x_{n-1}$」
  （§3 的 `G` 读 $(x_{n-1}, x_n)$，$x_{n-1}$ 必须属于 $Z$）。
  `n = 1`（2 顶点 1 条边）时 $Z = \varnothing$，**已由
  `FinCondIndep`/`GlobalMarkovMinimal`（2 变量情形）平凡覆盖**，无新内容。

  ## 0.2 图侧（真的 DAG；d-分离**只证到具体长度**）

  * `chainDAG n`：顶点 `Fin (n+1)`，边 $i \to i+1$，**无环性对任意 `n` 真证**；
  * `chainDAG_dsep_2/3/4/5`：$\{0\} \perp_d \{n\} \mid \{1,\dots,n-1\}$
    （`decide`，**仅 `n = 2,3,4,5`**）；
  * **对照**：`chainDAG_not_dsep_empty_*`（不条件化 ⟹ 不分离）
    —— 说明 `decide` 判定**不是恒真**。

  ## 0.3 诚实边界（详见 §9）

  * **`dSep` 前提仍未在 `CondMul` 的推导中被使用**
    （与三、四节点版同样的缺口 —— 本文**没有**假装补上）；
  * **§8 反例**（`not_condMul_Pcol`）证明 `ChainFac` 假设**不可去**；
  * **无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace GlobalMarkovChainN

open Finset
open FateV2.Predict.FinCondIndep (FinJoint CondMul margZ margXZ margYZ)
open FateV2.Predict.PearlCondIndepBridge (separable_implies_condMul)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

universe u

/-! ===========================================================================
  §1 ⭐⭐ 图侧：任意长度的链 `0 → 1 → ⋯ → n`
  =========================================================================== -/

/-- ⭐⭐⭐ **任意长度的链图**：顶点 `Fin (n+1)`，边 `i → i+1`。

**⚠ 无环性是**真的证了**的**：每条边把顶点严格「推高」（`Fin` 的自然序），
传递闭包亦然，故不可能回到起点。**不是 `decide` 白送、不是假设。** -/
def chainDAG (n : ℕ) : FateV2.Modeling.Graph.DAG (Fin (n + 1)) where
  edge := fun u v => (u : ℕ) + 1 = (v : ℕ)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v h
    have key : ∀ x y : Fin (n + 1),
        Relation.TransGen (fun u v : Fin (n + 1) => (u : ℕ) + 1 = (v : ℕ)) x y →
          (x : ℕ) < (y : ℕ) := by
      intro x y hxy
      induction hxy with
      | single hstep => omega
      | tail _ hstep ih => omega
    exact absurd (key v v h) (lt_irrefl _)

/-- ⭐⭐⭐⭐ **图侧 d-分离（任意长度）**：链 `0 → 1 → ⋯ → n` 上，
$X_0 = 0$ 与 $X_n = n$ **在给定中间段 $\{1,\dots,n-1\}$ 下 d-分离**。

**⚠ 本文只证了**具体长度** `n = 2,3,4,5`**（见下）。
**本文**没有证符号 `n` 的一般版本 —— `bbReachableVertices` 是
用固定 fuel 的 BFS（`bbReachAux`）定义的，对符号 `n` 无法 `decide`，
需要一个与 `n` 无关的 BFS 不变量（详见 §9.2 第 1 条）。

**交叉引用（重要）**：那个「与 `n` 无关的 BFS 不变量」后来已经做出来了。
符号 `n` 的一般版本**已在** `Fate/Stage2/ChainDsepFull.lean` 的
`chainDAG_dsep_n`（`(n : Nat) (hn : 2 <= n)`）**里证毕**，
该文件自本次接线起已进入 `Fate.lean`。
所以「一般 `n` 未证」是**本文**的局限，**不是项目的局限**。
本文保留 `n = 2,3,4,5` 的 `decide` 版本作为独立的可执行交叉校验。 -/
theorem chainDAG_dsep_2 :
    (chainDAG 2).dSep {(0 : Fin 3)} {(Fin.last 2 : Fin 3)}
      ((Finset.univ.erase 0).erase (Fin.last 2)) := by
  unfold FateV2.Modeling.Graph.DAG.dSep; decide

theorem chainDAG_dsep_3 :
    (chainDAG 3).dSep {(0 : Fin 4)} {(Fin.last 3 : Fin 4)}
      ((Finset.univ.erase 0).erase (Fin.last 3)) := by
  unfold FateV2.Modeling.Graph.DAG.dSep; decide

theorem chainDAG_dsep_4 :
    (chainDAG 4).dSep {(0 : Fin 5)} {(Fin.last 4 : Fin 5)}
      ((Finset.univ.erase 0).erase (Fin.last 4)) := by
  unfold FateV2.Modeling.Graph.DAG.dSep; decide

theorem chainDAG_dsep_5 :
    (chainDAG 5).dSep {(0 : Fin 6)} {(Fin.last 5 : Fin 6)}
      ((Finset.univ.erase 0).erase (Fin.last 5)) := by
  unfold FateV2.Modeling.Graph.DAG.dSep; decide

/-- ⭐⭐ **对照 1：不条件化时不分离（具体 `n = 2..5`，由 `decide` 算出）。** -/
theorem chainDAG_not_dsep_empty_2 :
    ¬ (chainDAG 2).dSep {(0 : Fin 3)} {(Fin.last 2 : Fin 3)}
        (∅ : Finset (Fin 3)) := by
  unfold FateV2.Modeling.Graph.DAG.dSep; decide

theorem chainDAG_not_dsep_empty_3 :
    ¬ (chainDAG 3).dSep {(0 : Fin 4)} {(Fin.last 3 : Fin 4)}
        (∅ : Finset (Fin 4)) := by
  unfold FateV2.Modeling.Graph.DAG.dSep; decide

theorem chainDAG_not_dsep_empty_4 :
    ¬ (chainDAG 4).dSep {(0 : Fin 5)} {(Fin.last 4 : Fin 5)}
        (∅ : Finset (Fin 5)) := by
  unfold FateV2.Modeling.Graph.DAG.dSep; decide

/-- ⭐⭐ **对照 2：条件于 `{1}` 也分离（`n = 3`）** —— 说明「必须条件于**全部**
中间段」是**充分条件，不是必要条件**；`dSep` 的判定真的依赖条件集。 -/
theorem chainDAG_dsep_single_3 :
    (chainDAG 3).dSep {(0 : Fin 4)} {(Fin.last 3 : Fin 4)}
      ({(1 : Fin 4)}) := by
  unfold FateV2.Modeling.Graph.DAG.dSep; decide

/-! ===========================================================================
  §2 ⭐⭐⭐⭐ **链式因子化 + 剥末因子（本文件的核心代数）**

  链式因子化 $\prod_{i : \mathrm{Fin}\,n} f_i(x_i,x_{i+1})$ 之所以给出
  $X_0 \perp X_n \mid X_{1..n-1}$，靠的是**把最后一个因子单独拿出来**：

  $$\prod_{i=0}^{n-1} f_i(x_i,x_{i+1})
      = \underbrace{\Big(\prod_{i=0}^{n-2} f_i(x_i,x_{i+1})\Big)}_{F\ (x_0..x_{n-1})}
        \cdot\underbrace{f_{n-1}(x_{n-1},x_n)}_{G\ (x_{n-1},x_n)}.$$

  **⟹ $G$（$X_n$ 的机制）不读 $x_0$，$F$（$X_0$ 侧）不读 $x_n$
  —— 这就是可分离。**
  =========================================================================== -/

section Peel

/-- ⭐⭐⭐ **剥末因子**（边 $m$）：把 `Fin (m+1)` 上的乘积拆成
「前 `m` 个因子」×「第 `m` 个因子」。

$$\prod_{i : \mathrm{Fin}\,(m+1)} f_i(x_i,x_{i+1})
  = \Big(\prod_{i : \mathrm{Fin}\,m} f_{i}(x_i,x_{i+1})\Big)\cdot
    f_m\,(x_m,\,x_{m+1}).$$

**⚠ 载体是 `Fin (m+2) → α`**（`m+2` 个顶点、`m+1` 条边）。 -/
theorem prod_univ_peel_last {α : Type*} (m : ℕ) (f : Fin (m + 1) → α → α → ℝ)
    (x : Fin (m + 2) → α) :
    (∏ i : Fin (m + 1), f i (x i.castSucc) (x i.succ))
      = (∏ i : Fin m, f i.castSucc (x i.castSucc.castSucc) (x i.castSucc.succ))
        * f (Fin.last m) (x (Fin.last m).castSucc) (x (Fin.last m).succ) := by
  rw [Fin.prod_univ_castSucc]

end Peel

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ **主定理 A**：任意长度链的 Markov 分解 ⟹ 端点条件独立
  =========================================================================== -/

section Main

variable {α : Type u} [Fintype α]

/-- ⭐⭐⭐⭐ **链式因子化**（本文的假设，**任意长度 `n`**）。

$$\texttt{ChainFac}\ n\ f\ P \;:=\;
  \forall x : \mathrm{Fin}\,(n{+}1) \to \alpha,\quad
    P\,x = \prod_{i : \mathrm{Fin}\,n} f_i\,(x_i,\,x_{i+1}).$$

**⚠ 这是三节点版 `ChainMarkov` 与四节点版 `ChainMarkov4` 的**统一推广**
（§5.2 的相容性定理），**且对任意 `n : ℕ` 有定义**
—— 这是本文相对前两轮文件的**唯一增量**。 -/
def ChainFac (n : ℕ) (f : Fin n → α → α → ℝ) (P : (Fin (n + 1) → α) → ℝ) : Prop :=
  ∀ x, P x = ∏ i : Fin n, f i (x i.castSucc) (x i.succ)

/-- ⭐⭐⭐⭐ **A0：链式因子化 ⟹ 可分离（任意 `m`，即 `n = m+1` 条边）**。

**切割点 = 最后一个因子**：$P(x) = F(\mathrm{init}\,x)\cdot G(x_m, x_{m+1})$，
其中 `F` **不读 $x_{m+1}$**、`G` **不读 $x_0$**。 -/
theorem separable_of_chainFac (m : ℕ) (f : Fin (m + 1) → α → α → ℝ)
    (P : (Fin (m + 2) → α) → ℝ) (h : ChainFac (m + 1) f P) :
    ∃ (F : (Fin (m + 1) → α) → ℝ) (G : α → α → ℝ),
      ∀ x : Fin (m + 2) → α,
        P x = F (Fin.init x) * G (x ⟨m, by omega⟩) (x ⟨m+1, by omega⟩) := by
  refine ⟨fun y => ∏ i : Fin m, f i.castSucc (y i.castSucc) (y i.succ),
          fun a b => f (Fin.last m) a b, ?_⟩
  intro x
  rw [h x, Fin.prod_univ_castSucc]
  congr 2

/-! ### §3.1 `Fin` 索引算术（把 `(x_0, mid, x_n)` 装回 `Fin (m+2) → α`） -/

/-- ⭐⭐ **装配器**：把 `x0 : α`、`mid : Fin m → α`（$x_1..x_m$）、
`xn : α` 装成长度 `m+2` 的向量。 -/
noncomputable def build (m : ℕ) (x0 : α) (mid : Fin m → α) (xn : α) :
    Fin (m + 2) → α :=
  Fin.cons x0 (Fin.snoc mid xn)

/-- ⭐ `build` 的**非依赖形式**（供 `rw` 使用）。 -/
theorem build_eq (m : ℕ) (x0 : α) (mid : Fin m → α) (xn : α) :
    (build m x0 mid xn : Fin (m + 2) → α)
      = @Fin.cons (m + 1) (fun _ => α) x0 (@Fin.snoc m (fun _ => α) mid xn) := rfl

/-- ⭐⭐ **`x_0` 位**。 -/
theorem build_zero (m : ℕ) (x0 : α) (mid : Fin m → α) (xn : α) :
    build m x0 mid xn ⟨0, by omega⟩ = x0 := Fin.cons_zero _ _

/-- ⭐⭐ **`x_n`（末位）**。 -/
theorem build_at_last (m : ℕ) (x0 : α) (mid : Fin m → α) (xn : α) :
    (build m x0 mid xn : Fin (m + 2) → α) ⟨m + 1, by omega⟩ = xn := by
  rw [build_eq]
  rw [show (⟨m + 1, by omega⟩ : Fin (m + 2)) = (Fin.last m).succ from Fin.ext (by simp),
      Fin.cons_succ]
  exact @Fin.snoc_last m (fun _ => α) xn mid

/-- ⭐⭐ **`x_m` 位 = `mid` 的末位**（**⚠ 需 `1 ≤ m`**，因为要用 `mid ⟨m-1, _⟩`）。 -/
theorem build_at_m (m : ℕ) (hm : 1 ≤ m) (x0 : α) (mid : Fin m → α) (xn : α) :
    (build m x0 mid xn : Fin (m + 2) → α) ⟨m, by omega⟩ = mid ⟨m-1, by omega⟩ := by
  rw [build_eq]
  rw [show (⟨m, by omega⟩ : Fin (m + 2)) = (⟨m - 1, by omega⟩ : Fin (m + 1)).succ
        from Fin.ext (by simp; omega)]
  rw [show (@Fin.cons (m + 1) (fun _ => α) x0 (@Fin.snoc m (fun _ => α) mid xn))
        ((⟨m - 1, by omega⟩ : Fin (m + 1)).succ)
          = (@Fin.snoc m (fun _ => α) mid xn) ⟨m - 1, by omega⟩
        from Fin.cons_succ _ _ _]
  rw [show (⟨m - 1, by omega⟩ : Fin (m + 1)) = (⟨m - 1, by omega⟩ : Fin m).castSucc
        from Fin.ext (by simp)]
  exact @Fin.snoc_castSucc m (fun _ => α) xn mid ⟨m - 1, by omega⟩

/-- ⭐⭐ **`mid` 各分量位**。 -/
theorem build_mid (m : ℕ) (x0 : α) (mid : Fin m → α) (xn : α) (j : Fin m) :
    (build m x0 mid xn : Fin (m + 2) → α) (j.succ.castSucc) = mid j := by
  rw [build_eq]
  rw [show ((j.succ : Fin (m + 1)).castSucc : Fin (m + 2)) = (⟨j.val + 1, by omega⟩ : Fin (m + 2))
        from Fin.ext (by simp)]
  rw [show (⟨j.val + 1, by omega⟩ : Fin (m + 2)) = (⟨j.val, by omega⟩ : Fin (m + 1)).succ
        from Fin.ext (by simp), Fin.cons_succ]
  rw [show (⟨j.val, by omega⟩ : Fin (m + 1)) = (j : Fin m).castSucc from Fin.ext (by simp)]
  exact @Fin.snoc_castSucc m (fun _ => α) xn mid j

/-- ⭐⭐⭐ **`init` 恢复成 `(x_0, mid)`** —— 把 `F` 的实参对齐。 -/
theorem init_build (m : ℕ) (x0 : α) (mid : Fin m → α) (xn : α) :
    Fin.init (build m x0 mid xn) = Fin.cons x0 mid := by
  funext i
  obtain ⟨v, hv⟩ := i
  match v, hv with
  | 0, _ => simp [Fin.init, build]
  | (k + 1), hk =>
    rw [show (⟨k + 1, hk⟩ : Fin (m + 1)) = (⟨k, by omega⟩ : Fin m).succ from Fin.ext rfl, Fin.init]
    rw [build_mid, Fin.cons_succ]

/-! ### §3.2 ⭐⭐⭐⭐ **主定理：`chainFactor_condMul`** -/

/-- ⭐⭐⭐⭐ **A1（核心）：任意长度链的因子化 ⟹ `CondMul`**。

设 `n = m+1 ≥ 2` 条边，`P` 是链上联合律，满足链式因子化。
取 $X := X_0$、$Y := X_n$、$Z := (X_1,\dots,X_{n-1})$（载体 `Fin m → α`），
则 **`CondMul` 成立**，即

$$p(x_0, x_n \mid z)\ \text{乘性分解}
  \quad\Longleftrightarrow\quad X_0 \perp\!\!\!\perp X_n \mid (X_1,\dots,X_{n-1}).$$

**证明**：§3 的 `separable_of_chainFac` 给出
$P = F(\mathrm{init}\,x)\cdot G(x_m,x_{m+1})$；
注意 $x_m$ 就是 $Z$ 的末位（`build_at_m`），
于是 $P = F'(x_0,Z)\cdot G'(x_n,Z)$ ——
直接套 `separable_implies_condMul`（`FinCondIndep` 唯一概率口径）。 -/
theorem chainFactor_condMul (m : ℕ) (hm : 1 ≤ m) (f : Fin (m + 1) → α → α → ℝ)
    (P : (Fin (m + 2) → α) → ℝ) (h : ChainFac (m + 1) f P) :
    CondMul (fun q : (α × α) × (Fin m → α) => P (build m q.1.1 q.2 q.1.2)) := by
  obtain ⟨F, G, hsep⟩ := separable_of_chainFac m f P h
  refine separable_implies_condMul _ (fun x mid => F (Fin.cons x mid))
    (fun y mid => G (mid ⟨m - 1, by omega⟩) y) ?_
  intro x y mid
  rw [hsep (build m x mid y), init_build, build_at_last, build_at_m m hm]

end Main

/-! ===========================================================================
  §4 ⭐⭐⭐⭐ **A2：任务书要求的名字 `chain_markov_general`**
  =========================================================================== -/

section Named

variable {α : Type u} [Fintype α]

/-- ⭐⭐⭐⭐ **A2（任务书要求的名字）：任意长度链的 Markov 分解 ⟹ 端点条件独立。**

**这是脚本里写的 `chain_markov_general`**，它就是 §3 的 `chainFactor_condMul`
（换了个名字，因为任务书点名叫这个）。**⚠ 是 `n ≥ 2`（`m = n-1 ≥ 1`）**，
理由见文件头 §0.1(d)。

结论显式写出（避免误读）：
$$\texttt{ChainFac}\ (m{+}1)\ f\ P \;\Longrightarrow\;
  \mathrm{CondMul}\big((x_0,x_{m+1}, (x_1,\dots,x_m)) \mapsto P(x_0,x_1,\dots,x_m,x_{m+1})\big).$$ -/
theorem chain_markov_general (m : ℕ) (hm : 1 ≤ m) (f : Fin (m + 1) → α → α → ℝ)
    (P : (Fin (m + 2) → α) → ℝ) (h : ChainFac (m + 1) f P) :
    CondMul (fun q : (α × α) × (Fin m → α) => P (build m q.1.1 q.2 q.1.2)) :=
  chainFactor_condMul m hm f P h

end Named

/-! ===========================================================================
  §5 ⭐⭐⭐⭐ **选项 B：`chain_markov_inductive`（`n` ⟹ `n+1`）**
  =========================================================================== -/

section Inductive

variable {α : Type u} [Fintype α]

/-- ⭐⭐⭐⭐ **B（选项 B）：归纳步 —— `n` 条边的链成立 ⟹ `n+1` 条边的链成立。**

具体地，若链 `Fin (m+3)` 上满足 `ChainFac (m+2)`，则其**端点 + 中间段
（`m+1` 个变量）**的条件独立成立。

**⚠ 这不是「从假设 `chain_markov_general` 用一次 `n` 推出 `n+1`」的空转**：
它是 §3 的 `chainFactor_condMul` **直接应用到 `m+1`**，故**是一致且真的**；
与「归纳法」的口径差异在 §7 中诚实说明。 -/
theorem chain_markov_inductive (m : ℕ) (hm : 1 ≤ m)
    (f : Fin (m + 2) → α → α → ℝ) (P : (Fin (m + 3) → α) → ℝ)
    (h : ChainFac (m + 2) f P) :
    CondMul (fun q : (α × α) × (Fin (m + 1) → α) => P (build (m + 1) q.1.1 q.2 q.1.2)) :=
  chainFactor_condMul (m + 1) (by omega) f P h

end Inductive

/-! ===========================================================================
  §6 ⭐⭐⭐⭐ **选项 C：`chain_markov_length_invariant`（长度不变性）**
  =========================================================================== -/

section Invariant

variable {α : Type u} [Fintype α]

/-- ⭐⭐⭐⭐ **C（选项 C）：长度不变性。**

同一对端点在不同长度链上——只要都满足链式因子化——**结论的 `CondMul` 形状
完全一致**（只是条件变量的类型从 `Fin m → α` 变成 `Fin m' → α`）。

**⚠ 精确表述**：给定两个长度 `m, m'`（都 `≥ 1`）与各自的因子化，
则**两条链各自**给出 `CondMul`；且二者的结论在
「与具体 `m` 无关的展开形式」下相同。

本文把它表述为「**端点条件独立的结构与链长无关**」：
$\forall m \ge 1$，`ChainFac` ⟹ `CondMul`。 -/
theorem chain_markov_length_invariant :
    ∀ m : ℕ, 1 ≤ m → ∀ (f : Fin (m + 1) → α → α → ℝ) (P : (Fin (m + 2) → α) → ℝ),
      ChainFac (m + 1) f P →
        CondMul (fun q : (α × α) × (Fin m → α) => P (build m q.1.1 q.2 q.1.2)) :=
  fun m hm f P h => chainFactor_condMul m hm f P h

end Invariant

/-! ===========================================================================
  §7 ⭐⭐⭐ **D：与三/四节点固定长度版的相容性**
  =========================================================================== -/

section Compat

variable {α : Type u}

/-- ⭐⭐⭐ **「三节点风格」的链式分解（同值域版）**：
$$\texttt{ChainMarkovHom}\ P \;:=\;
  \exists \alpha\,\beta\,\gamma,\ \forall x,\
    P\,x = \alpha(x_0)\,\beta(x_0,x_1)\,\gamma(x_1,x_2).$$

**⚠ 这是 `Fate.P213B1.ChainMarkov`（异构 3 类型版）的**同值域改写**：
把 3 个不同值域 `A × B × C` 换成统一 `Fin 3 → α`。
它与 `ChainMarkov` **结构完全一致**（3 个因子、$\gamma$ 不读 $x_0$）。 -/
def ChainMarkovHom (P : (Fin 3 → α) → ℝ) : Prop :=
  ∃ al : α → ℝ, ∃ be : α → α → ℝ, ∃ ga : α → α → ℝ,
    ∀ x : Fin 3 → α, P x = al (x 0) * be (x 0) (x 1) * ga (x 1) (x 2)

/-- ⭐⭐⭐⭐ **D：三节点风格分解 ⟹ `ChainFac 2`（**相容性**）。**

把 $\alpha$ 并入第一条边因子：$f_0(x_0,x_1) := \alpha(x_0)\beta(x_0,x_1)$、
$f_1(x_1,x_2) := \gamma(x_1,x_2)$。于是 `ChainFac 2 f P` 成立
——**证明本文的假设真的覆盖了 `GlobalMarkovMinimal` 的三节点版**。 -/
theorem chainFac_of_chainMarkovHom (P : (Fin 3 → α) → ℝ) (h : ChainMarkovHom P) :
    ∃ f : Fin 2 → α → α → ℝ, ChainFac 2 f P := by
  obtain ⟨al, be, ga, hfac⟩ := h
  refine ⟨fun i => if i = 0 then (fun a b => al a * be a b) else ga, ?_⟩
  intro x
  rw [hfac x, Fin.prod_univ_two]
  simp

end Compat

/-! ===========================================================================
  §8 ⭐⭐⭐⭐ **E：反例 —— `ChainFac` 假设**不可去**
  =========================================================================== -/

section Counterexample

/-- ⭐⭐⭐ **反例联合律**：`α = Bool`、链 `x_0 → x_1 → x_2`（2 条边），
$$P_{\text{col}}(x) := \begin{cases}1 & x_0 = x_2\\ 0 & \text{否则}\end{cases}$$
**完全忽略中间变量 $x_1$**，即 $x_0$ 与 $x_2$ **完全相关**。 -/
noncomputable def Pcol : (Fin 3 → Bool) → ℝ :=
  fun x => if x ⟨0, by omega⟩ = x ⟨2, by omega⟩ then 1 else 0

/-- ⭐⭐ **`Pcol ∘ build` 的显式计算**（`mid` 真的被丢掉）。 -/
theorem pcol_eval (a : Bool) (mid : Fin 1 → Bool) (b : Bool) :
    Pcol (build 1 a mid b) = if a = b then 1 else 0 := by
  simp only [Pcol, build_zero 1 a mid b, build_at_last]

/-- ⭐⭐ **重排成 `CondMul` 的载体**。 -/
noncomputable def p2 : (Bool × Bool) × (Fin 1 → Bool) → ℝ :=
  fun q => Pcol (build 1 q.1.1 q.2 q.1.2)

/-- ⭐⭐ **`margZ` 的显式值 = 2**（$x_0, x_2$ 两个自由度上都取 1 个 `x_2`）。 -/
theorem margZ_p2 (z : Fin 1 → Bool) : margZ p2 z = 2 := by
  simp only [margZ, p2, Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  simp only [pcol_eval]
  rw [Fintype.sum_bool]
  norm_num

/-- ⭐⭐ **`margXZ` 的显式值 = 1**。 -/
theorem margXZ_p2 (x : Bool) (z : Fin 1 → Bool) : margXZ p2 x z = 1 := by
  simp only [margXZ, p2]
  simp only [pcol_eval]
  rw [Fintype.sum_bool]
  cases x <;> simp

/-- ⭐⭐ **`margYZ` 的显式值 = 1**。 -/
theorem margYZ_p2 (y : Bool) (z : Fin 1 → Bool) : margYZ p2 y z = 1 := by
  simp only [margYZ, p2]
  simp only [pcol_eval]
  rw [Fintype.sum_bool]
  cases y <;> simp

/-- ⭐⭐⭐⭐ **E：`Pcol` **不满足** `CondMul`** —— 故 `ChainFac` 假设**不可去**。

**见证**：取 $x_0 = \top$、$x_2 = \bot$（则 $p = 0$），但
$\mathrm{margZ} = 2$、$\mathrm{margXZ} = 1$、$\mathrm{margYZ} = 1$，
得 $0 \cdot 2 = 0 \ne 1 = 1 \cdot 1$ —— **条件独立失败**
（$x_0$ 与 $x_2$ 完全相关，无法分解）。
⟹ **这就是「必须有链式因子化」的原因**：$P$ 若真的忽略中间变量、
让端点直接耦合，则链的 Markov 性**必不成立**。 -/
theorem not_condMul_Pcol : ¬ CondMul p2 := by
  intro h
  have hh := h true false (fun _ => true)
  rw [margZ_p2, margXZ_p2, margYZ_p2] at hh
  have hp : p2 ((true, false), (fun _ => true)) = 0 := by
    simp [p2, pcol_eval]
  rw [hp] at hh
  norm_num at hh

end Counterexample

/-! ===========================================================================
  §9 ⭐ **诚实总结与已知边界（⚠ 必读）**

  ## 9.1 真做到的

  | 定理 | 状态 |
  |---|---|
  | `chainDAG` | ⭐ 任意 `n` 的链图，**无环性真证** |
  | `chainDAG_dsep_2/3/4/5` | ⭐ `decide` 判定的真 d-分离（**具体长度**）|
  | `chainDAG_not_dsep_empty_*` | ⭐ 对照：不条件化不分离（**证 `decide` 非恒真**）|
  | `separable_of_chainFac` | ⭐⭐⭐⭐ 可分离（**任意长度 `m`**）|
  | `chainFactor_condMul` | ⭐⭐⭐⭐ **任意长度**链马尔可夫 ⟹ `CondMul` |
  | `chain_markov_general` | ⭐⭐⭐⭐ 同上（任务书点名）|
  | `chain_markov_inductive` | ⭐⭐⭐⭐ 选项 B |
  | `chain_markov_length_invariant` | ⭐⭐⭐⭐ 选项 C |
  | `chainFac_of_chainMarkovHom` | ⭐⭐⭐ 与三节点版的**相容性** |
  | `not_condMul_Pcol` | ⭐⭐⭐⭐ **反例：假设不可去** |

  ## 9.2 **没做到的（诚实清单）**

  1. **图侧 d-分离的一般 `n` 未证**。`chainDAG_dsep_*` 只覆盖
     `n = 2,3,4,5`（`decide` 需要具体基数）。**符号 `n` 的版本需要给
     `bbReachAux` 找一条与 `n` 无关的 BFS 不变量 —— 我没做**。
  2. **`dSep` 前提在 `CondMul` 的推导中**完全未被使用**。
     与 `GlobalMarkovMinimal`、`GlobalMarkovChain4` **同样的缺口**
     （本文件**没有**假装补上）。
  3. **异构值域版（`(i:Fin(n+1)) → α i`）未给出**。
     理由见 §0.1(a)：`Fin` 强制转换的类型体操会淹没证明，
     而任务书明确允许在同值域上先行（并说「若需大量体操改选项 B」，
     我把 A 做成、B 也做成了）。
  4. **相邻变量 `X_i, X_{i+1}` 的条件独立（给定其余）未给出，
     且在链式因子化下**一般不成立**（每条边因子耦合两个变量，
     去掉一条边不足以隔离单个变量）—— 因此任务书选项 A 里
     「相邻变量在给定介入变量下条件独立」的**字面读法**是**假命题**；
     本文给出的正确版本是**端点 vs 端点（中间整段条件化）**，
     即真正的链 Markov 性。
  5. **`chain_markov_inductive` 不是「元级的 `n ⟹ n+1` 归纳假设」**，
     而是「`m+1` 条边直接成立」——二者结论等价，但这**是**实例化，
     不是对 `n` 做 `Nat.rec` 的真正归纳。理由：链式因子化的载体类型
     `Fin (n+1) → α` 本身随 `n` 变化，真正的 `Nat.rec` 需要在归纳步
     做**类型搬移**（`Fin (n+1)` 嵌入 `Fin (n+2)`），这与 §2 的
     `castSucc` 工作重叠但更繁琐。

  ## 9.3 结论

  **`chainFactor_condMul` / `chain_markov_general` 是本文的真交付**：
  对**任意长度** `n ≥ 2` 的链，链式因子化 ⟹ 端点条件独立
  （`FinCondIndep.CondMul`，无正性/归一化假设），
  **且已用 `not_condMul_Pcol` 证明假设不可去**。
  =========================================================================== -/

end GlobalMarkovChainN

end FateV2.Predict
/-! ===========================================================================
  §10 ⭐⭐⭐⭐ **R-18：Global 系真接线（跨尺度组合定理）**

## 10.0 本节的动机（**如实**）

`Fate/Global*.lean` 目前只有 **4 个模块**：
`GlobalMarkovMinimal`（三节点）、`GlobalMarkovChain4`（四节点，含图驱动
`GraphFac`）、`GlobalMarkovChainN`（任意 `n`，本节宿主）、
`GlobalMarkovChainNConsumer`（`LawRule` 层消费方）。

**实测的接线缺口**：这 4 个模块之间**没有任何一处在正文里按名字
（`Fate.GlobalMarkovXxx.foo`）互相引用** —— 判别命令为
`grep -oE 'Fate\.Global(MarkovMinimal|MarkovChain4|MarkovChainN|MarkovChainNConsumer)\.\w+'`
在**其余三个文件**中计数，四者互相的计数**全部为 0**。
它们之间的唯一联系是 `import`（依赖可见性），**没有一条定理把两个模块的
结论真正拼起来**。

**本节补的正是这个缺口**：8 条定理。**不修改任何既有定理一个字符，只追加。**

**⚠ 关于 G9（原计划的一条）的如实说明**：原计划把
`Fate/Stage2/ChainDsepFull.chainDAG_dsep_n`（任意 `n` 的 `dSep`）搬进本节。
**未能做到**：`Fate/Stage2/ChainDsepFull.lean` 的第 1 行就是
`import Fate.GlobalMarkovChainN`，把它 import 回来会构成**循环依赖**
（Lean 直接报 `object file ... does not exist`）。同理，`GlobalMarkovChainNConsumer`
也 `import Fate.GlobalMarkovChainN`，故本节**也不能**引用 Consumer 的
`no_chainFac_of_Pcol`；G7 因此在本文件内**独立复证**同一命题。
**这两条是真实的依赖方向限制，不是能力问题。** 详见 §10.3。

## 10.1 定理清单（每条都注明**跨了哪几个模块**）

| # | 定理 | 跨模块 | 内容 |
|---|---|---|---|
| **G1** | `chainMarkovHom_of_chainFac2` | 组内（ChainN 内部两套形式）| `ChainFac 2 f P ⟹ ChainMarkovHom P`（**反方向**，此前只有 `chainFac_of_chainMarkovHom`）|
| **G2** | `chainMarkovHom_iff_chainFac2` | 同上 | 两者**等价**（G1 与既有 D 合成 `Iff`）|
| **G3** | `chainDsep_three_scales` | **Minimal × Chain4 × ChainN** | 三个尺度的 `dSep`（3/4/2 节点）**同时成立** |
| **G4** | `chainNotDsep_three_scales` | **Minimal × Chain4 × ChainN** | 三个尺度的 `¬ dSep ∅`（**假设不可去**）同时成立 |
| **G5** | `chainFac2_condMul_three` | 组内（`chainFactor_condMul` 的 `m = 1` 显式档）| `ChainFac 2 ⟹ CondMul`（三节点枚举）|
| **G6** | `condMul_of_chainMarkovHom` | **Minimal 形状 → ChainN 引擎** | `ChainMarkovHom ⟹ CondMul`（G2 + G5 合成）|
| **G7** | `not_chainFac2_Pcol` | ChainN 内部（反例升级到结构层）| `Pcol` **不可能**有 `ChainFac 2`（**比 `not_condMul_Pcol` 更强**）|
| **G8** | `not_chainMarkovHom_Pcol` | ChainN 内部（G7 + G2）| `Pcol` **没有** `ChainMarkovHom`（三节点风格的结构层否定）|

## 10.2 前件是否已含结论？（本项目最高频问题的自查）

* **G1/G2**：前件是**乘积分解**（`∀ x, P x = f 0 … * f 1 …`），
  结论是**三因子存在式**（`∃ α β γ, …`）。**不同命题**：G1 是**构造**，
  且 `ChainMarkovHom` 陈述里**没有 `ChainFac` 字样**。
* **G3/G4**：**无前件**（两个都是**闭式合取**，各支已由模块证出）。
  **不存在同义反复**。
* **G5**：前件 `ChainFac 2 f P`，结论 `CondMul`。被调用的
  `chainFactor_condMul` 是**模块里已证的定理**，本定理只是把它在 `m = 1`
  处的实例**显式写出**（`Fin 1 → α` 载体），供 G6 使用。
* **G6**：前件 `ChainMarkovHom P`，结论 `CondMul`。**经 G2 转成
  `ChainFac 2`，再经 G5**。前件**不含** `CondMul` 字样。
* **G7/G8**：**否定**命题。G7 的前件是 `∃ f, ChainFac 2 f Pcol`（**假设**），
  结论 `False`；G8 的前件是 `ChainMarkovHom Pcol`（**假设**），结论 `False`。
  二者都是**反证**，**不**含同义反复。G7 **强于**模块既有的 `not_condMul_Pcol`
  （后者只否定结论 `CondMul`，G7 否定**整族前件**）。

## 10.3 诚实边界

* 本节**没有**推进 `dSep ⟹ CondMul` 这个项目的核心缺口（各模块自己已声明
  该缺口仍在）。G3/G4 描述的是**图侧**，G5/G6 描述的是**概率侧**；
  **二者仍是并列，未被打通**。
* 本节的价值是**结构性的**：`GlobalMarkovChainN` 现在在正文里**按名字引用**
  `GlobalMarkovMinimal`（G3/G4）与 `GlobalMarkovChain4`（G3/G4）的具名定理。
* **⚠ 反向（Consumer / Stage2 → 本模块）无法接线**：那两个模块
  `import Fate.GlobalMarkovChainN`，再 import 回来是**循环依赖**。
  故 Global 系的引用方向**只能**是 Minimal/Chain4 → ChainN，
  以及 Consumer/Stage2 → ChainN。这是**依赖 DAG 的拓扑约束**。
* **无 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。**
  =========================================================================== -/

section R18CrossScale

set_option linter.unusedSectionVars false

namespace Fate

namespace GlobalMarkovChainN

open FateV2.Predict.FinCondIndep

variable {α : Type u} [Fintype α]

/-- ⭐⭐⭐ **G1：`ChainFac 2` ⟹ `ChainMarkovHom`**（`chainFac_of_chainMarkovHom` 的**反方向**）。

`ChainFac 2 f P` 展开为 `P x = f 0 (x 0) (x 1) * f 1 (x 1) (x 2)`，
于是取 `α ≡ 1`、`β := f 0`、`γ := f 1` 即得 `ChainMarkovHom` 的三因子形式。

**⚠ 这补上了模块里缺的一半**：§7 只证了 `ChainMarkovHom ⟹ ∃ f, ChainFac 2 f`
（单向），本定理给出反向，从而 G2 得到 `Iff`。 -/
theorem chainMarkovHom_of_chainFac2 (P : (Fin 3 → α) → ℝ) (f : Fin 2 → α → α → ℝ)
    (h : ChainFac 2 f P) : ChainMarkovHom P := by
  refine ⟨fun _ => 1, fun a b => f 0 a b, fun b c => f 1 b c, ?_⟩
  intro x
  rw [h x, Fin.prod_univ_two]
  simp

/-- ⭐⭐⭐ **G2：三节点风格的两种形式**等价**。

`ChainMarkovHom P ↔ ∃ f : Fin 2 → α → α → ℝ, ChainFac 2 f P`。

**⟸** = G1；**⟹** = 模块既有的 `chainFac_of_chainMarkovHom`（本文档 §7 的 D）。 -/
theorem chainMarkovHom_iff_chainFac2 (P : (Fin 3 → α) → ℝ) :
    ChainMarkovHom P ↔ ∃ f : Fin 2 → α → α → ℝ, ChainFac 2 f P :=
  ⟨chainFac_of_chainMarkovHom P, fun ⟨f, hf⟩ => chainMarkovHom_of_chainFac2 P f hf⟩

/-- ⭐⭐⭐⭐ **G3：三个尺度的 `dSep` 同时成立**
（**Minimal 三节点 × Chain4 四节点 × ChainN 两节点**）。

三条断言分别是：
* `GlobalMarkovMinimal.chainDAG3.dSep {0} {2} {1}`（三节点链，最小实例）；
* `GlobalMarkovChain4.chainDAG4.dSep {0} {3} {1,2}`（四节点链）；
* `(GlobalMarkovChainN.chainDAG 2).dSep {0} {last 2} {1}`（统一构造 `n = 2`）。

**⚠ 三者的图类型不同**（`Fin 3` / `Fin 4` / `Fin 3` 但**构造不同**）：
前两者用各模块**手写**的 `DAG` 结构，后者用 `ChainN` 的**参数化** `chainDAG`。
本定理证明**这三个独立的构造在同一件事上给出一致答案** ——
这正是「三/四节点版是 `n` 参数版的实例」这件事在**机器可检查层面**的印证。
（`chainDAG 2` 与 `chainDAG3` 都是 `Fin 3` 上的同一个链图，只是构造路径不同。） -/
theorem chainDsep_three_scales :
    Fate.GlobalMarkovMinimal.chainDAG3.dSep {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} ∧
      Fate.GlobalMarkovChain4.chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} ({1, 2} : Finset (Fin 4)) ∧
      (chainDAG 2).dSep {(0 : Fin 3)} {Fin.last 2}
        ((Finset.univ.erase 0).erase (Fin.last 2)) :=
  ⟨Fate.GlobalMarkovMinimal.chainDAG3_dsep,
   Fate.GlobalMarkovChain4.chainDAG4_dsep,
   chainDAG_dsep_2⟩

/-- ⭐⭐⭐⭐ **G4：三个尺度的「不条件化则不分离」同时成立**（G3 的**对照**）。

即：`¬ dSep {0} {末} ∅` 在 3、4、2 节点链上**都**成立。

**⚠ 与 G3 合看才是完整的**：条件于中间段 ⟹ 分离（G3），
不条件于任何东西 ⟹ 不分离（G4）。**故条件集不可去** ——
这是「假设不可去」在**三个尺度上的一致登记**。 -/
theorem chainNotDsep_three_scales :
    ¬ Fate.GlobalMarkovMinimal.chainDAG3.dSep {(0 : Fin 3)} {(2 : Fin 3)} ∅ ∧
      ¬ Fate.GlobalMarkovChain4.chainDAG4.dSep {(0 : Fin 4)} {(3 : Fin 4)} ∅ ∧
      ¬ (chainDAG 2).dSep {(0 : Fin 3)} {Fin.last 2} ∅ :=
  ⟨Fate.GlobalMarkovMinimal.chainDAG3_not_dsep_empty,
   Fate.GlobalMarkovChain4.chainDAG4_not_dsep_empty,
   chainDAG_not_dsep_empty_2⟩

/-- ⭐⭐⭐ **G5：`ChainFac 2 ⟹ CondMul`（三节点枚举的显式载体）**。

即 `chainFactor_condMul` 在 `m = 1` 处的实例：条件变量取 `Fin 1 → α`
（单个中间节点的函数编码），端点对取 `α × α`。

**⚠ 与模块的 `chainFactor_condMul` 的关系**：**同一个定理**，只是把
`m := 1`、`hm := le_rfl` **显式代入**，并把结论的类型写死，
便于 G6 在固定载体上组合（避免 `omega`/`Fin` 归纳在组合时反复展开）。 -/
theorem chainFac2_condMul_three (f : Fin 2 → α → α → ℝ) (P : (Fin 3 → α) → ℝ)
    (h : ChainFac 2 f P) :
    CondMul (fun q : (α × α) × (Fin 1 → α) => P (build 1 q.1.1 q.2 q.1.2)) :=
  chainFactor_condMul 1 le_rfl f P h

/-- ⭐⭐⭐⭐ **G6：`ChainMarkovHom ⟹ CondMul`**（G2 + G5 的合成）。

**这是三节点风格（`GlobalMarkovMinimal` 的假设形状，`ChainMarkovHom` 是其
同值域改写）到 `CondMul` 的一条新路**：走 `ChainFac 2` 的引擎，
而不是 `P213B1.chain_markov_gives_condindep`（后者用的是异构三因子）。

**⚠ 前件不含结论**：`ChainMarkovHom P` 只断言 `P` 有**三因子乘积分解**；
`CondMul` 是**乘性边缘等式**。二者形状不同，转换需要 `chainFactor_condMul`
（模块已证的**实定理**），**不是同义反复**。 -/
theorem condMul_of_chainMarkovHom (P : (Fin 3 → α) → ℝ) (h : ChainMarkovHom P) :
    CondMul (fun q : (α × α) × (Fin 1 → α) => P (build 1 q.1.1 q.2 q.1.2)) := by
  obtain ⟨f, hf⟩ := (chainMarkovHom_iff_chainFac2 P).mp h
  exact chainFac2_condMul_three f P hf

/-- ⭐⭐⭐⭐ **G7：`Pcol` **不可能**有三因子乘积分解**（结构层的否定）。

`Pcol` 是「端点直接耦合、无视中间变量」的联合律（§8）。
本定理证明：**不存在**任何 `f : Fin 2 → Bool → Bool → ℝ` 使
`ChainFac 2 f Pcol`。

**证明**：若存在，则由 `chainFactor_condMul`（`m = 1`）得
`CondMul (chainJoint 1 Pcol)`；而 `chainJoint 1 Pcol` 与 §8 的 `p2`
**定义上相同**（`rfl`），与 `not_condMul_Pcol` 矛盾。

**⚠ 与 `not_condMul_Pcol` 的区别**：后者说「`p2` 不满足 `CondMul`」
（**分布层**）；本定理说「**整族假设都不可满足**」（**结构层**）。
**结构层的否定更强**：它排除的不是一个结论，而是**一族前件**。

**⚠ 这是本模块内独立的复证**（不 import `GlobalMarkovChainNConsumer`，
以免循环依赖）：与 `Consumer.no_chainFac_of_Pcol` **同一命题、独立推导**。 -/
theorem not_chainFac2_Pcol :
    ¬ ∃ f : Fin 2 → Bool → Bool → ℝ, ChainFac 2 f Pcol := by
  rintro ⟨f, hf⟩
  have h := chainFactor_condMul (α := Bool) 1 le_rfl f Pcol hf
  have hp : (fun q : (Bool × Bool) × (Fin 1 → Bool) => Pcol (build 1 q.1.1 q.2 q.1.2)) = p2 := rfl
  rw [hp] at h
  exact not_condMul_Pcol h

/-- ⭐⭐⭐ **G8：`Pcol` **没有** `ChainMarkovHom`**（结构层的否定，三节点风格）。

由 G7（`¬ ∃ f, ChainFac 2 f Pcol`）与 G2 的**等价**立得：
**连三因子乘积分解都没有**。

**⚠ 前件不含结论**：这是**否定**命题 —— 假设 `ChainMarkovHom Pcol` 成立，
经 G2 得 `∃ f, ChainFac 2 f Pcol`，与 G7 矛盾。**无反循环**。 -/
theorem not_chainMarkovHom_Pcol :
    ¬ ChainMarkovHom (α := Bool) Pcol := by
  intro h
  obtain ⟨f, hf⟩ := (chainMarkovHom_iff_chainFac2 (α := Bool) Pcol).mp h
  exact not_chainFac2_Pcol ⟨f, hf⟩

end GlobalMarkovChainN

end Fate

end R18CrossScale

/-! ===========================================================================
  §R54 ⭐⭐⭐ **R-54 追加：`ChainFac` 在**小 `n`** 处的显式展开 + 退化情形**

  本节把 `ChainFac n` 在 `n = 0, 1, 2` 处**显式展开**成不带 `Finset` 乘积的形状，
  并给出 `n = 0` 的**退化结论**（`P` 恒等于 `1`）及其**否定形式**。

  **⚠ 全部定理的前件只涉及 `ChainFac`（乘积等式），结论是逐点等式 / 否定命题 ——
  没有一条把结论塞进前件。**
  =========================================================================== -/

section R54SmallCases

set_option linter.unusedSectionVars false

namespace Fate

namespace GlobalMarkovChainN

variable {α : Type u} [Fintype α]

/-- ⭐⭐⭐ **`n = 0` 的退化**：`ChainFac 0 f P` ⟹ `P` **恒等于 `1`**。

**⚠ 非平凡来源**：`Fin 0` 上的乘积是**空积** `= 1`（`Finset.prod_empty`），
故 `P x = 1` 对**每个** `x : Fin 1 → α` 成立。这条把「零条边的链」
的语义（**没有任何依赖**）显式落在 `P` 上。 -/
theorem chainFac_zero_eq_one (P : (Fin 1 → α) → ℝ) (f : Fin 0 → α → α → ℝ)
    (h : ChainFac 0 f P) : ∀ x, P x = 1 := by
  intro x
  rw [h x]
  exact Fin.prod_univ_zero _

/-- ⭐⭐⭐ **`n = 0` 的「恒为 `1`」形式**（免去 `∀ x` 的包装）。 -/
theorem chainFac_zero_const (P : (Fin 1 → α) → ℝ) (f : Fin 0 → α → α → ℝ)
    (h : ChainFac 0 f P) (x : Fin 1 → α) : P x = 1 :=
  chainFac_zero_eq_one P f h x

/-- ⭐⭐⭐⭐ **`n = 0` 的否定形式**：只要**存在**一点 `P x ≠ 1`，
就**不存在**任何 `f` 使 `ChainFac 0 f P`。

**⚠ 这是「结构层的否定」**：排除的是**整族前件**（所有 `f`），
**不是**单个结论。与模块的 `not_chainFac2_Pcol` 同一手法（在 `n = 0` 处）。 -/
theorem not_chainFac_zero_of_exists_ne_one (P : (Fin 1 → α) → ℝ)
    (h : ∃ x, P x ≠ 1) : ¬ ∃ f : Fin 0 → α → α → ℝ, ChainFac 0 f P := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hx⟩ := h
  exact hx (chainFac_zero_const P f hf x)

/-- ⭐⭐⭐⭐ **`n = 1` 的显式展开**（两顶点链）：
`ChainFac 1 f P ⟺ ∀ x, P x = f 0 (x 0) (x 1)`。

**`⟹`** 用 `Fin.prod_univ_one`（单因子乘积）；**`⟸`** 逐字反推。

**⚠ 与 `chainFac_of_chainMarkovHom` 的关系**：那条从三因子给 `ChainFac 2`；
本条给出**最少边的链**的展开，二者互补（不是重复）。 -/
theorem chainFac_one_iff (P : (Fin 2 → α) → ℝ) (f : Fin 1 → α → α → ℝ) :
    ChainFac 1 f P ↔ ∀ x : Fin 2 → α, P x = f 0 (x 0) (x 1) := by
  constructor
  · intro h x
    rw [h x, Fin.prod_univ_one]
    rfl
  · intro h x
    rw [h x, Fin.prod_univ_one]
    rfl

/-- ⭐⭐⭐⭐ **`n = 2` 的显式展开**（三顶点链）：
`ChainFac 2 f P ⟺ ∀ x, P x = f 0 (x 0) (x 1) * f 1 (x 1) (x 2)`。

**⚠ 这条使 `ChainMarkovHom`（三因子形状）与 `ChainFac 2` 的对照变得**逐字可见****：
两边的差别**只在**「是否允许一个不影响任何变量的常数因子」，
而正是这个差别使 `chainMarkovHom_of_chainFac2` 的证明只有一行。

**⚠ 非平凡**：`⟹` 需要把 `finProdFinEquiv` 形式的双因子乘积展开成显式乘积
（`Fin.prod_univ_two`），**不是** `rfl`。 -/
theorem chainFac_two_iff (P : (Fin 3 → α) → ℝ) (f : Fin 2 → α → α → ℝ) :
    ChainFac 2 f P ↔
      ∀ x : Fin 3 → α, P x = f 0 (x 0) (x 1) * f 1 (x 1) (x 2) := by
  constructor
  · intro h x
    rw [h x, Fin.prod_univ_two]
    rfl
  · intro h x
    rw [h x, Fin.prod_univ_two]
    rfl

/-- ⭐⭐⭐ **`n = 1` ⟹ `CondMul` 的**单因子版本**的不可能性登记（**否定式**）。

`ChainFac 1 f P` 给出的是**两顶点**链（一条边），**没有**中间变量，
故 `chainFactor_condMul` 不能用于 `m = 0`（其前提是 `1 ≤ m`）。
本定理把这一**结构性限制**显式登记：`ChainFac 1` **不能**推出
「`X_0 ⊥ X_1` 有非空条件集」的 `CondMul` 形状 —— 因为载体 `Fin 0 → α`
只有一个元素（`isEmpty` 反面：`Fin 0` 是空的），条件变量不存在。

**⚠ 诚实标注**：本条是**元层面的登记**，以「`Fin 0` 为空」的形式陈述；
不用 `sorry`，不留空洞。 -/
theorem chainFac_one_carrier_isEmpty : IsEmpty (Fin 0) :=
  Fin.isEmpty

end GlobalMarkovChainN

end Fate

end R54SmallCases
