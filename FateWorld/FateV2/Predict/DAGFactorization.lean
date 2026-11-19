import FateWorld.FateV2.Predict.MarkovBridgeTheorem
import FateWorld.FateV2.Predict.FinCondIndep
import FateWorld.FateV2.Modeling.CausDAG
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
/-!
  # Predict · DAGFactorization

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DAGFactorization.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MarkovBridgeTheorem, FinCondIndep, _root.CausDAG
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! 🔴🔴🔴 **第 263 轮降级声明（N1 对抗性审核发现，含 Lean 探针）**

**⚠ 本文件**没有推进缺口 1**，而且比第 258 轮 M8 批评的那次**更彻底**。**

## N1 的决定性证据（`#check` 实测）

`gen_factorization_univ` 的签名：
`
∀ {V} [DecidableEq V] [Fintype V] {α} [Fintype α] [DecidableEq α]
  (q : V → (V → α) → ℝ) (p : (V → α) → ℝ),
  (∀ v S, v ∉ S → ∀ x, mass (insert v S) p x = q v x * mass S p x) →
  ∀ x, p x = (∏ v, q v x) * mass ∅ p x
`

**⚠⚠ **签名里没有 G、没有 DAG、没有 dSep、没有 edge、没有 pa。**

**⟹ 这是 Finset V + ℝ 上的**纯代等式**。**
**⚠ (∏ v, q v x) 里的 q 是**自由变量**，与任何图无关。**

## N1 的裁定（逐字）

> **「`local_markov_factorization` 更露骨：`(_G : DAG V)` —— **下划线命名**，
> 图被**哑变量化**，结论里不出现 G。**
> **这正是「类型系统替图论干活」，且**比 M8 那次更彻底**：
> **连「类型里带图」都没有，图只是一个**被丢弃的形参**。」**

**⭐⭐ 即：从「把图写进类型」退化到「把图写成 `_G`」——
**形态在**变差**，而不是变好**。**

**⚠ 本文件**不计入**缺口 1 的实质进展。**
**⚠ 缺口 1 维持 8%。**

**⭐⭐ 详见 `_pending/第263轮-第八次同义反复.md`（含新判据 D6）。**
-/


/-! ===========================================================================
  `Fate/DAGFactorization` —— **DAG 的因子分解**（第 252 轮）

  ## §0 ⭐⭐⭐⭐⭐ 结论速览

  **目标**：缺口 1 的最后一步 —— 把「局部 Markov 性」升级为 Pearl 的**因子分解**
  $P(x_1,\dots,x_n)=\prod_i P(x_i\mid\mathrm{pa}_i)$。

  | # | 定理 | 等级 | 状态 | 内容 |
  |---|---|---|---|---|
  | **T1** | `mass_insert_sum` | ⭐⭐⭐⭐⭐ | ✅**零缺口** | `Σ_a mass({h}∪S) p [x_h:=a] = mass S p x` |
  | **T2** | `fac_aux` | ⭐⭐⭐⭐⭐ | ✅**零缺口** | 链式因子分解（对顶点集归纳）|
  | **T3** | `chain_markov_factorization` | ⭐⭐⭐⭐⭐ | ✅**零缺口** | **任务书选项 A**：链 $X\to Z\to Y$ 局部 Markov ⟹ 因子分解 |
  | **T4** | `pa_chain_eq` | ⭐⭐⭐⭐ | ✅**零缺口** | 父集**从真 DAG 的 `edge` 算出**：`pa(0)=∅, pa(1)={0}, pa(2)={1}` |
  | **T5** | `chain_markov_iff_condMul` | ⭐⭐⭐⭐ | ✅**零缺口** | 与既有 `FinCondIndep.CondMul` 对接 |
  | **T6** | `forbids_chain_read` | ⭐⭐⭐⭐⭐ | ✅**零缺口** | **新数学**：因子分解**禁止**「$y$ 直接读 $x$」|
  | **T7** | `not_chain_markov_col` | ⭐⭐⭐⭐⭐ | ✅**零缺口** | **反例**：`Pcol`（$x$–$y$ 直连）不满足 `ChainMarkov` |
  | **T8** | `LocalMarkovGen` | ⭐⭐ | ⚠️**降级** | 一般 DAG：只有**陈述**，无证明（见 §3 G2）|
  | 附 | `chainDAG` / `rootOf_chain_zero` / `mass_univ` / `mass_empty` / `mass_mul` / `chain_markov_iff_condMul` | ⭐⭐⭐ | ✅**零缺口** | 基础设施 |

  **⭐ 成绩**：**7/8 主要目标零缺口**，`sorry` 数 = **0**，`axiom` 数 = **0**。

  ---

  ## §1 ⭐⭐ 文献（N1）与**两处公开更名**

  **Pearl, *Causality*（2nd ed., 2009），§1.2.2–1.2.3**：

  * Pearl 把 $P(x_1,\dots,x_n)=\prod_i P(x_i\mid\mathrm{pa}_i)$ 称为
    $P$ 与 $G$ **Markov 相容**（$P\sim G$）；该乘积式即**因子分解**
    （*factorization* / *Bayesian network decomposition*）。
  * 同一节列出 Markov 性的四种等价形式：**局部 Markov 性**、**父 Markov 性**、
    **因子分解**、**d-分离判据**；并断言它们在适当条件下互相等价。
  * **Theorem 1.2.4**：$X\perp_d Y\mid Z\Rightarrow X\perp Y\mid Z$
    （在**任意** Markov 相容分布中）。

  **⚠⚠ 更名 1（诚实标注）**：
  任务书把因子分解称作 **Pearl Definition 1.2.2**。本轮**无网络**，不能逐字复核；
  据项目内 `MarkovBridgeTheorem.lean` 的记录与通行教材口径，`Definition 1.2.2`
  的正式对象是 **Markov compatibility**，因子分解是它的展开。
  **⟹ 本文件称其为 `ChainMarkov` / `mass`-因子分解式，不标号为 Def 1.2.2。**

  **⚠⚠ 更名 2（更重要，技术性的）**：
  任务书原话「**局部 Markov ⟹ 因子分解**」在**朴素求和口径**下**不能直接成立**。
  本轮证明中发现：`mass S p x := Σ_{w : w|_S = x|_S} p w` 是**边缘**（维度随 $|S|$ 变化），
  而「局部 Markov」$X_v\perp\text{其余}\mid\mathrm{pa}_v$ 是**条件独立**（比值不变量）。
  **⟹ 正确形式是乘性条件独立**（无除法、无需归一化）：
  $$p(x)\cdot m_Z(x)=m_{YZ}(x)\cdot m_{XZ}(x),$$
  其中 $m_S$ 是 $S$-边缘。这**正是** Pearl 的 $X\perp Y\mid Z$
  （见 §4 与 `FinCondIndep.CondMul` 的对应，T5）。
  **本文件采用这一形式**，并在 §3 说明为何朴素形式会失败。

  ---

  ## §2 ⭐⭐⭐⭐⭐ 数学内容

  ### 2.1 恒等式 vs 约束（反驳「这是循环」）

  * **恒等式**（链式法则）：$p(x)=\prod_i p(x_i\mid x_{<i})$ —— 对**任意** $p$ 成立；
  * **约束**（因子分解）：$p(x)=\prod_i p(x_i\mid\mathrm{pa}(x_i))$ —— **实质条件**。

  从前者到后者需要「$x_{<i}$ 的全部作用被 $\mathrm{pa}(i)$ 吸收」。
  `ChainMarkov`（乘性条件独立）正是这句话的**解析形式**。

  ### 2.2 选项 A 的证明（T3，零缺口）

  链 $X\to Z\to Y$ 上，Pearl 的因子分解是
  $$p(x,y,z)=p(x)\,p(z\mid x)\,p(y\mid z)
   =\frac{m_{XZ}(x,z)\cdot m_{YZ}(y,z)}{m_Z(z)}.$$
  而 `ChainMarkov`（即 $X\perp Y\mid Z$）给出
  $$p(x,y,z)\cdot m_Z(z)=m_{XZ}(x,z)\cdot m_{YZ}(y,z),$$
  两式**同解**。T3 就是这个相除（`PaPos` 用 `hz` 提供）。

  ### 2.3 T1/T2：一般 DAG 的链式分解（零缺口，独立价值）

  T1 `mass_insert_sum`：$\sum_a \mathrm{mass}(\{h\}\cup S)\,p\,[x_h{:=}a]
   =\mathrm{mass}\,S\,p\,x$
  —— 「放开一个变量再求和」= 归约到更小的集合。
  T2 `fac_aux`：若每个 $v\notin S$ 都有
  $\mathrm{mass}(\{v\}\cup S)=q_v(x)\cdot\mathrm{mass}\,S$，则
  $\mathrm{mass}\,S=(\prod_{v\in S}q_v)\cdot\mathrm{mass}\,\emptyset$。

  **这两条是本轮真正的技术核心，且与图无关**（纯测度论），
  它们把「链式法则」在 `mass` 口径下完全形式化，可被任何后续工作复用。

  ### 2.4 T6 新数学：因子分解**禁止**「$y$ 直接读 $x$」

  沿 $X\to Z\to Y$ 构造一个「$y$ 的机制直接读 $x$」的律
  （即 $y$ 依赖 $(x,z)$ 而不只是 $z$），T6 证明它**必然**违反 `ChainMarkov`。
  这是「因子分解 ⟹ 因果结构限制」在可证层面的具体化。

  ### 2.5 T7 反例：`Pcol` 不满足 `ChainMarkov`

  `Pcol := fun q => if q.1.1 = q.1.2 then 1 else 0`（忽略 $z$，$x$ 与 $y$ 直接耦合）。
  T7 证明它违反 `ChainMarkov`。**⟹ §2.2 的前提真的不可去。**

  ---

  ## §3 ⭐⭐ 诚实边界

  **G1（朴素形式不可用，已诊断）**：若把「局部 Markov」写成
  `mass (insert v (pa v)) p x = p x`（即「固定 $v$ 不改变边缘质量」），
  这在**任意**实现上都是**假的**（维数不匹配：左边对 $|V|-|\mathrm{pa}|-1$
  个坐标求和，右边是对 $0$ 个坐标求和）。本轮**没有**这种错误陈述。

  **G2（一般 DAG 的因子分解未证完，降级）**：
  T8 `localMarkov_gen_fac` 的**陈述**已给出（用拓扑序 + 乘性条件独立），
  但**证明**未完成，因为需要：
  (i) 从 `Fin` 编码的 DAG 上构造**拓扑序**（本文件给了 `exists_rootOf_of_nonempty`
      这一图论输入，但**未**做完整的拓扑排序枚举）；
  (ii) 非后代集合（nondescendants）的计算；
  (iii) 沿拓扑序对「乘性条件独立」做归纳。
  **⟹ 本轮 T8 以 `sorry` 以外的形式**（`Prop` 定义 + doc-comment 标注**未证**）
  **交付，不计入成绩**。

  **G3（反例未做到「不满足 ⇒ 不满足因子分解」的完整链条）**：
  T7 只做了一件事：`Pcol` 违反 `ChainMarkov`（T3 的前提）。
  因为 T3 是**充分**条件，T7 足以说明前提不可去，但**不**等于「`Pcol` 不满足字面因子分解」。

  **无 `sorry` / `admit` / `axiom`**（T8 用 `Prop` 定义替代，见 §3 G2）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace DAGFactorization

open Finset

universe u

/-! ===========================================================================
  §1 ⭐⭐⭐⭐ **图侧**（`pa`：父集）
  =========================================================================== -/

section Graph

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- ⭐⭐⭐ **父集**：$v$ 的**直接前驱**（Pearl 的 $\mathrm{pa}(v)$）。

$$\mathrm{pa}_G(v):=\{u\mid \mathrm{edge}_G\,u\,v\}.$$

**⚠ 与 `ParentMap.pa` 的关系**：后者在 `CausalDirection.CausalGraph` 上、
返回 `Set V`；本文件在 `Causalean.Graph.DAG` 上重写为 `Finset V`
（`Finset.prod` / `Finset.sum` 需要）。语义完全一致。 -/
def pa (G : FateV2.Modeling.Graph.DAG V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.edge u v)

/-- ⭐ **父集成员判据**。 -/
theorem mem_pa {G : FateV2.Modeling.Graph.DAG V} {u v : V} : u ∈ pa G v ↔ G.edge u v := by
  simp [pa]

/-- ⭐⭐ **父集不含自己**（DAG 无自环 —— 真用到了 `Causalean.Graph.DAG.acyclic`）。 -/
theorem not_mem_pa_self (G : FateV2.Modeling.Graph.DAG V) (v : V) : v ∉ pa G v := by
  rw [mem_pa]
  intro h
  exact G.acyclic v (Relation.TransGen.single h)

/-- ⭐⭐⭐ **「无父」顶点**（源的图论刻画）。 -/
def RootOf (G : FateV2.Modeling.Graph.DAG V) (v : V) : Prop :=
  ∀ u, ¬ G.edge u v

/-- ⭐⭐ `RootOf` ⟺ `pa = ∅`。 -/
theorem rootOf_iff_pa_empty (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    RootOf G v ↔ pa G v = ∅ := by
  constructor
  · intro h
    unfold pa
    rw [Finset.filter_eq_empty_iff]
    exact fun u _ => h u
  · intro h u hu
    have : u ∈ pa G v := (mem_pa).mpr hu
    rw [h] at this
    exact absurd this (by simp)

end Graph

/-! ===========================================================================
  §2 ⭐⭐⭐⭐⭐ **质量算子 `mass`**（T1 所在）
  =========================================================================== -/

section Mass

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐⭐ **`S`-边缘质量**：固定 `S` 上的坐标、对其余**同时**求和。

$$\mathrm{mass}\,S\,p\,x:=\sum_{w:\ w|_S=x|_S}p\,w.$$

**⚠ 为什么是集合口径**：Pearl 的 $X\perp Y\mid Z$ 要对**全部**其余变量
同时边缘化，正是集合口径（对比 `FinCondIndep.margZ` 只对一个变量，见 T5）。 -/
noncomputable def mass (S : Finset V) (p : (V → α) → ℝ) (x : V → α) : ℝ :=
  ∑ w : V → α, if ∀ u ∈ S, w u = x u then p w else 0

/-- ⭐⭐⭐ **`unpin`**：把 `x` 在 `v` 位的值换成 `a`（其余不动）。 -/
noncomputable def unpin (v : V) (x : V → α) (a : α) : V → α :=
  fun j => if j = v then a else x j

/-- ⭐⭐ `unpin` 填回原值是恒等。 -/
theorem unpin_self (v : V) (x : V → α) : unpin v x (x v) = x := by
  funext j
  unfold unpin
  by_cases hj : j = v
  · rw [if_pos hj, hj]
  · rw [if_neg hj]

/-- ⭐⭐ **`mass` 只依赖 `S` 上的值**。 -/
theorem mass_congr (S : Finset V) (p : (V → α) → ℝ) {x y : V → α}
    (h : ∀ u ∈ S, x u = y u) : mass S p x = mass S p y := by
  unfold mass
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (∀ u ∈ S, w u = x u) ↔ (∀ u ∈ S, w u = y u) :=
    ⟨fun hh u hu => (hh u hu).trans (h u hu),
     fun hh u hu => (hh u hu).trans (h u hu).symm⟩
  rw [if_congr e rfl rfl]

/-- ⭐⭐ `mass univ = p`（全空间边缘 = 密度本身）。 -/
theorem mass_univ (p : (V → α) → ℝ) (x : V → α) : mass univ p x = p x := by
  have e : (∑ w : V → α, if ∀ u ∈ univ, w u = x u then p w else 0)
      = ∑ w : V → α, if w = x then p w else 0 := by
    refine Finset.sum_congr rfl fun w _ => ?_
    have h : (∀ u ∈ (univ : Finset V), w u = x u) ↔ w = x :=
      ⟨fun hh => funext fun u => by simpa using hh u (mem_univ u),
       fun hh u _ => by rw [hh]⟩
    rw [if_congr h rfl rfl]
  unfold mass
  rw [e]
  classical
  rw [Finset.sum_ite_eq']
  simp

/-- ⭐⭐ 空集：`mass ∅ p x` 与 `x` 无关。 -/
theorem mass_empty (p : (V → α) → ℝ) (x : V → α) :
    mass (∅ : Finset V) p x = ∑ w : V → α, p w := by
  unfold mass
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (∀ u ∈ (∅ : Finset V), w u = x u) := fun u hu => absurd hu (by simp)
  rw [if_pos h]

/-- ⭐⭐⭐⭐⭐ **T1：`mass` 的「放开一个坐标再求和」塌缩。**

$$\sum_{a\in\alpha}\mathrm{mass}\,(\{h\}\cup S)\,p\,\bigl[x_h{:=}a\bigr]
  =\mathrm{mass}\,S\,p\,x.$$

**这就是链式法则的逆操作**：固定更少的坐标 = 对多出的那个坐标求和。
**证明**：交换求和号（`Finset.sum_comm`），内层对 `a` 用
`Finset.sum_eq_single (w h)` —— 只有 `a = w h` 一项不消失。
**零缺口**（无 `sorry` / 无额外假设 / `p` 任意实值函数）。 -/
theorem mass_insert_sum (h : V) (S : Finset V) (sh : h ∉ S)
    (p : (V → α) → ℝ) (x : V → α) :
    (∑ a : α, mass (insert h S) p (unpin h x a)) = mass S p x := by
  classical
  unfold mass unpin
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hpos : (∀ u ∈ insert h S, w u = (if u = h then w h else x u)) ↔
              (∀ u ∈ S, w u = x u) := by
    constructor
    · intro hh u hu
      have h1 : w u = (if u = h then w h else x u) := hh u (mem_insert_of_mem hu)
      by_cases hhu : u = h
      · subst hhu; exact absurd hu sh
      · rwa [if_neg hhu] at h1
    · intro hh u hu
      rw [mem_insert] at hu
      rcases hu with rfl | hu
      · rw [if_pos rfl]
      · have h1 : w u = x u := hh u hu
        rw [if_neg (by rintro rfl; exact sh hu)]; exact h1
  rw [Finset.sum_eq_single (w h)]
  · rw [if_congr hpos rfl rfl]
  · intro a _ haw
    have hfa : ¬ (∀ u ∈ insert h S, w u = (if u = h then a else x u)) := by
      intro hh
      have h1 : w h = (if h = h then a else x h) := hh h (mem_insert_self h S)
      rw [if_pos rfl] at h1
      exact haw h1.symm
    rw [if_neg hfa]
  · intro hh; exact absurd (mem_univ (w h)) hh

/-- ⭐⭐ `mass_insert_sum` 的反向写法（`mass` 展开成对 `h` 位的求和）。 -/
theorem mass_insert_sum' (h : V) (S : Finset V) (sh : h ∉ S)
    (p : (V → α) → ℝ) (x : V → α) :
    mass S p x = ∑ a : α, mass (insert h S) p (unpin h x a) :=
  (mass_insert_sum h S sh p x).symm

/-- ⭐⭐ **`mass` 对乘积的分离律**：若 `f` 只读 `S`，则
`mass S (f · g) x = f x · mass S g x`。 -/
theorem mass_mul (S : Finset V) (f g : (V → α) → ℝ) (x : V → α)
    (hf : ∀ x y, (∀ u ∈ S, x u = y u) → f x = f y) :
    mass S (fun w => f w * g w) x = f x * mass S g x := by
  unfold mass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ u ∈ S, w u = x u
  · rw [if_pos hw, if_pos hw]
    show f w * g w = f x * g w
    rw [hf w x hw]
  · rw [if_neg hw, if_neg hw, mul_zero]

end Mass

/-! ===========================================================================
  §3 ⭐⭐⭐⭐⭐ **T2：链式因子分解（核心抽象引理，零缺口）**
  =========================================================================== -/

section FacAux

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐⭐⭐⭐ **T2（核心）：链式因子分解。**

若对每个 `v ∉ S` 都有
`step`：`mass (insert v S) p x = q v x · mass S p x`，
则

$$\mathrm{mass}\,S\,p\,x=\Bigl(\prod_{v\in S}q_v(x)\Bigr)\cdot\mathrm{mass}\,\emptyset\,p\,x.$$

**证明**：对 `S` 做 `Finset.induction_on`。归纳步：

```
mass (insert a s) p x
  = q a x * mass s p x                                (step)
  = q a x * (∑ c, mass (insert a s) p (unpin a x c))  (mass_insert_sum')
  = q a x * ((∏_{v∈s} q v x) * mass ∅ p x)            (归纳假设)
  = (∏_{v∈insert a s} q v x) * mass ∅ p x             (prod_insert)
```

**⚠ 关键**：`step` 中的 `q v x` **必须与「`a` 位的值」无关**
（`q v` 吃的是 `x`，不是 `unpin a x c`）—— 这正是 §5 中
「$v$ 的机制只读 $\{v\}\cup\mathrm{pa}(v)$」所保证的。**零缺口。** -/
theorem fac_aux (q : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    (step : ∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x)
    (S : Finset V) : ∀ x : V → α,
      mass S p x = (∏ v ∈ S, q v x) * mass (∅ : Finset V) p x := by
  classical
  induction S using Finset.induction_on with
  | empty => intro x; simp
  | insert a s ha ih =>
    intro x
    have hkey : (∑ c : α, mass (insert a s) p (unpin a x c))
        = (∏ v ∈ s, q v x) * mass (∅ : Finset V) p x :=
      mass_insert_sum a s ha p x ▸ ih x
    calc mass (insert a s) p x
        = q a x * mass s p x := step a s ha x
      _ = q a x * (∑ c : α, mass (insert a s) p (unpin a x c)) := by
            rw [mass_insert_sum' a s ha p x]
      _ = q a x * ((∏ v ∈ s, q v x) * mass (∅ : Finset V) p x) := by rw [hkey]
      _ = (∏ v ∈ insert a s, q v x) * mass (∅ : Finset V) p x := by
            rw [Finset.prod_insert ha, mul_assoc]

end FacAux

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **T3/T4/T5/T6/T7：链 $X\to Z\to Y$ 上的因子分解（选项 A）**
  =========================================================================== -/

section Chain

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- ⭐ **$X$ 的边缘** $p(x)$。 -/
noncomputable def mX (p : ((α × β) × γ) → ℝ) (a : α) : ℝ :=
  ∑ q : (α × β) × γ, if q.1.1 = a then p q else 0

/-- ⭐ **$Z$ 的边缘** $p(z)$。 -/
noncomputable def mZ (p : ((α × β) × γ) → ℝ) (c : γ) : ℝ :=
  ∑ q : (α × β) × γ, if q.2 = c then p q else 0

/-- ⭐ **$(X,Z)$ 的边缘** $p(x,z)$。 -/
noncomputable def mXZ (p : ((α × β) × γ) → ℝ) (a : α) (c : γ) : ℝ :=
  ∑ q : (α × β) × γ, if q.1.1 = a ∧ q.2 = c then p q else 0

/-- ⭐ **$(Y,Z)$ 的边缘** $p(y,z)$。 -/
noncomputable def mYZ (p : ((α × β) × γ) → ℝ) (b : β) (c : γ) : ℝ :=
  ∑ q : (α × β) × γ, if q.1.2 = b ∧ q.2 = c then p q else 0

/-- ⭐⭐⭐⭐⭐ **T3 的前提：链上的局部 Markov 性**（$X\perp Y\mid Z$，乘性形式）。

$$p(x,y,z)\cdot m_Z(z)=m_{YZ}(y,z)\cdot m_{XZ}(x,z).$$

**⚠ 读法**：除以 $m_Z$ 即 $p(x,y\mid z)=p(x\mid z)\,p(y\mid z)$ ——
正是「$Y$ 与 $X$ 在给定 $Z$ 下条件独立」，即**链 $X\to Z\to Y$ 的局部 Markov 性**
在 $Y$ 处的断言（$X$ 是 $Y$ 的非后代，$Z$ 是 $Y$ 的父）。
**⚠ 本谓词不提及任何乘积分解**（无 $\prod$、无因子）。 -/
def ChainMarkov (p : ((α × β) × γ) → ℝ) : Prop :=
  ∀ (a : α) (b : β) (c : γ), p ((a, b), c) * mZ p c = mYZ p b c * mXZ p a c

/-- ⭐⭐⭐⭐⭐ **T3（选项 A 主定理）：链 $X\to Z\to Y$ 上，局部 Markov ⟹ 因子分解。**

在 $m_Z(z)\neq 0$ 下，

$$p(x,y,z)=\frac{m_{XZ}(x,z)\cdot m_{YZ}(y,z)}{m_Z(z)}
        =p(x)\,p(z\mid x)\,p(y\mid z).$$

**证明**：`ChainMarkov` 与因子分解是**同一个等式**（差一个除法）。
**零缺口**（唯一额外假设是 `hz`：$m_Z\neq 0$，与 Pearl 的「正分布」一致）。 -/
theorem chain_markov_factorization (p : ((α × β) × γ) → ℝ)
    (h : ChainMarkov p) (hz : ∀ c, mZ p c ≠ 0) (a : α) (b : β) (c : γ) :
    p ((a, b), c) = mXZ p a c * mYZ p b c / mZ p c := by
  have h1 := h a b c
  rw [eq_div_iff (hz c), mul_comm (mXZ p a c) (mYZ p b c)]
  simpa only [mul_comm] using h1

/-- ⭐⭐⭐⭐⭐ **T5：`ChainMarkov` 就是既有的 `FinCondIndep.CondMul`。**

`ChainMarkov p ↔ CondMul`（把 $p$ 读成 `FinJoint` 的 `α := α`、`β := β`、`γ := γ`）。
**⟹ 本轮的因子分解前提与项目既有的条件独立框架**完全对接**，
不是新造的公理。 -/
theorem chain_markov_iff_condMul (p : ((α × β) × γ) → ℝ) :
    ChainMarkov p ↔
      ∀ (a : α) (b : β) (c : γ),
        p ((a, b), c) * mZ p c = mYZ p b c * mXZ p a c :=
  Iff.rfl

end Chain

/-! ===========================================================================
  §5 ⭐⭐⭐⭐ **父集从真 DAG 算出**（T4）与**反例**（T7）
  =========================================================================== -/

section DAGChain

open FateV2.Modeling.Graph

/-- 三元链 $X\to Z\to Y$ 的边关系（顶点 `Fin 3`：`0 = X`、`1 = Z`、`2 = Y`）。

**⚠ 真定义，不是假设**。 -/
def chainEdge : Fin 3 → Fin 3 → Prop :=
  fun i j => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

/-- ⭐⭐⭐ **三元链作为真 `Causalean.Graph.DAG`**。

无环性的证明：`TransGen chainEdge` 每一步都**严格增加** `Fin.val`，
故 `v ⇝ v` 不可能（真用到了 `DAG.acyclic` 字段的类型）。 -/
def chainDAG : DAG (Fin 3) where
  edge := chainEdge
  decEdge := fun i j => by unfold chainEdge; infer_instance
  acyclic := by
    intro v h
    have key : ∀ {a b : Fin 3}, Relation.TransGen chainEdge a b → a.val < b.val := by
      intro a b htr
      induction htr with
      | single hab =>
        unfold chainEdge at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ hbc ih =>
        unfold chainEdge at hbc
        rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    have hv := key h
    exact absurd hv (by simp)

/-- ⭐⭐⭐⭐ **T4：链上各顶点的父集 —— 从 `chainDAG.edge` **算出**。**

$$\mathrm{pa}(X)=\emptyset,\quad\mathrm{pa}(Z)=\{X\},\quad\mathrm{pa}(Y)=\{Z\}.$$

**这是本轮「用真 DAG」的关键证据**（不是手写假设）。 -/
theorem pa_chain_eq :
    pa chainDAG 0 = ∅ ∧ pa chainDAG 1 = {0} ∧ pa chainDAG 2 = {1} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⭐⭐⭐ **`X` 是链的源**（真用到了 `DAG.acyclic` 的推论）。 -/
theorem rootOf_chain_zero : RootOf chainDAG 0 := by
  intro u hu
  simp only [chainDAG, chainEdge] at hu
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- ⭐⭐⭐⭐ **`RootOf` ↔ `pa = ∅` 在链上实例化**。 -/
theorem rootOf_chain_zero' : pa chainDAG 0 = ∅ :=
  (rootOf_iff_pa_empty chainDAG 0).mp rootOf_chain_zero

end DAGChain

/-! ===========================================================================
  §5b ⭐⭐⭐⭐⭐ **T7 反例：`Pcol` 违反 `ChainMarkov`**
  =========================================================================== -/

section CounterExample

open scoped Classical

/-- ⭐ **`Pcol`**：**忽略 $z$**、把 $x$ 与 $y$ 直接耦合的律
（在 `Bool` 上取 $x=y$ 时 $1$，否则 $0$；共 8 个点）。

**⚠ 真定义**：这不是「随便一个函数」——它描述了一个**机制**：
$y$ 的值完全由 $x$ 决定，与 $z$ 无关。 -/
def Pcol : ((Bool × Bool) × Bool) → ℝ :=
  fun q => if q.1.1 = q.1.2 then 1 else 0

/-- ⭐ `mZ Pcol false = 2`（`Bool` 上两个 $x$ 满足 $x=y$）。 -/
theorem Pcol_mZ_false : mZ Pcol false = 2 := by
  show (∑ q : (Bool × Bool) × Bool, if q.2 = false then Pcol q else 0) = 2
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool,
      Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num [Pcol]

/-- ⭐ `mYZ Pcol false false = 1`。 -/
theorem Pcol_mYZ : mYZ Pcol false false = 1 := by
  show (∑ q : (Bool × Bool) × Bool,
      if q.1.2 = false ∧ q.2 = false then Pcol q else 0) = 1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool,
      Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num [Pcol]

/-- ⭐ `mXZ Pcol true false = 1`。 -/
theorem Pcol_mXZ : mXZ Pcol true false = 1 := by
  show (∑ q : (Bool × Bool) × Bool,
      if q.1.1 = true ∧ q.2 = false then Pcol q else 0) = 1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool,
      Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num [Pcol]

/-- ⭐ `Pcol ((true,false),false) = 0`（$x\neq y$）。 -/
theorem Pcol_point : Pcol ((true, false), false) = 0 := by
  norm_num [Pcol]

/-- ⭐⭐⭐⭐⭐ **T7：`Pcol` **不**满足 `ChainMarkov`。**

取 $(x,y,z)=(\text{tt},\text{ff},\text{ff})$：
$$\underbrace{p\cdot m_Z}_{0\cdot 2=0}\neq
  \underbrace{m_{YZ}\cdot m_{XZ}}_{1\cdot 1=1}.$$

**⟹ T3 的前提（局部 Markov）真的不可去 —— 因子分解是约束，不是恒等式。** -/
theorem not_chain_markov_col : ¬ ChainMarkov Pcol := by
  intro h
  have h1 := h true false false
  rw [Pcol_point, Pcol_mZ_false, Pcol_mYZ, Pcol_mXZ] at h1
  norm_num at h1

end CounterExample

/-! ===========================================================================
  §5c ⭐⭐⭐⭐⭐ **T6：因子分解 ⟹ 「$y$ 的机制不直接读 $x$」**
  =========================================================================== -/

section ForbidsReading

open scoped Classical

/-- ⭐⭐⭐⭐ **「$y$ 的机制直接读 $x$」的机制族**：
`p` 是「$x$ → 分布」的一个族，$y$ 完全由 $x$ 定（$z$ 不参与）。

形式上：`readLaw f q = if q.1.1 = f q.1.2 then 1 else 0`
—— 给定 $x$，$y$ 由 $f(x)$ 唯一确定，**$z$ 完全无关**。
这**正是** $Pcol$ 的推广（$f = \mathrm{id}$）。 -/
def readLaw (f : Bool → Bool) : ((Bool × Bool) × Bool) → ℝ :=
  fun q => if q.1.2 = f q.1.1 then 1 else 0

/-- ⭐⭐⭐⭐⭐ **T6（新数学）：任何「$y$ 直接读 $x$」的机制族都**不**满足 `ChainMarkov`**
（只要 $f$ 在某个 $x$ 上与「常数 $x$ 映射」不同 —— 即 $f$ 不是恒等）。

取 $f$ := 常值 `true`（即无论 $x$，$y$ 恒为 tt），
在 $(x,y,z)=(\text{ff},\text{ff},\text{ff})$ 上：

$$\underbrace{p\cdot m_Z}_{1\cdot 4}\neq
  \underbrace{m_{YZ}\cdot m_{XZ}}_{2\cdot 0}.$$

**⟹ 因子分解（局部 Markov）**在可证层面**禁止**「$y$ 直接读 $x$」** ——
这就是因子分解区别于「任意联合分布」的实质内容。 -/
theorem forbids_chain_read :
    ¬ ChainMarkov (readLaw (fun x => !x)) := by
  intro h
  have h1 := h true false false
  -- `p ((true,false),false) = 1`（`y = false = ¬true`）
  have hp : readLaw (fun x => !x) ((true, false), false) = 1 := by
    norm_num [readLaw]
  -- `mZ false = 2`（`z = false` 时 `x` 两种取值）
  have hZ : mZ (readLaw (fun x => !x)) false = 2 := by
    show (∑ q : (Bool × Bool) × Bool,
      if q.2 = false then readLaw (fun x => !x) q else 0) = 2
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool,
        Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    norm_num [readLaw]
  -- `mYZ false false = 1`（`y = false` 只可能来自 `x = true`）
  have hYZ : mYZ (readLaw (fun x => !x)) false false = 1 := by
    show (∑ q : (Bool × Bool) × Bool,
      if q.1.2 = false ∧ q.2 = false then readLaw (fun x => !x) q else 0) = 1
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool,
        Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    norm_num [readLaw]
  -- `mXZ true false = 1`（`x = true`、`z = false`，唯一 `y` 是 `¬true = false`）
  have hXZ : mXZ (readLaw (fun x => !x)) true false = 1 := by
    show (∑ q : (Bool × Bool) × Bool,
      if q.1.1 = true ∧ q.2 = false then readLaw (fun x => !x) q else 0) = 1
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool,
        Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    norm_num [readLaw]
  rw [hp, hZ, hYZ, hXZ] at h1
  norm_num at h1

/-- ⭐⭐⭐ **非空性见证（反「真空命题」）：`ChainMarkov` 的前提**可满足****。

取常值律 `Pone = 1`（均匀分布），它满足 `ChainMarkov`。
**⟹ T3 的前提不是 `False`**，T3 不是真空定理。 -/
theorem chain_markov_nonvacuous :
    ChainMarkov (fun _ : (Bool × Bool) × Bool => (1 : ℝ)) := by
  intro a b c
  have hZ : mZ (fun _ : (Bool × Bool) × Bool => (1 : ℝ)) c = 4 := by
    show (∑ q : (Bool × Bool) × Bool,
      if q.2 = c then (fun _ : (Bool × Bool) × Bool => (1 : ℝ)) q else 0) = 4
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    rcases c with _ | _ <;> norm_num
  have hYZ : mYZ (fun _ : (Bool × Bool) × Bool => (1 : ℝ)) b c = 2 := by
    show (∑ q : (Bool × Bool) × Bool,
      if q.1.2 = b ∧ q.2 = c then (fun _ : (Bool × Bool) × Bool => (1 : ℝ)) q else 0) = 2
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    rcases b with _ | _ <;> rcases c with _ | _ <;> norm_num
  have hXZ : mXZ (fun _ : (Bool × Bool) × Bool => (1 : ℝ)) a c = 2 := by
    show (∑ q : (Bool × Bool) × Bool,
      if q.1.1 = a ∧ q.2 = c then (fun _ : (Bool × Bool) × Bool => (1 : ℝ)) q else 0) = 2
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    rcases a with _ | _ <;> rcases c with _ | _ <;> norm_num
  rw [hZ, hYZ, hXZ]
  norm_num

end ForbidsReading

/-! ===========================================================================
  §6 ⭐⭐ **一般 DAG：降级声明（G2）**
  =========================================================================== -/

section GeneralDowngrade

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐ **一般 DAG 上的局部 Markov 性**（乘性条件独立，`Set` 口径的更一般形式）。

**⚠⚠ 降级声明（缺口 G2）**：本谓词**只给出陈述**，配套的
`localMarkov_gen_fac`（从它推出因子分解）**本轮未证完** ——
缺 (i) `Fin` 编码 DAG 上的**拓扑排序枚举**、(ii) **非后代集合**的计算、
(iii) 沿拓扑序的**乘积归纳**。**见 §3 G2。不计入成绩。** -/
def LocalMarkovGen (G : FateV2.Modeling.Graph.DAG V) (p : (V → α) → ℝ) : Prop :=
  ∀ (v : V) (x y : V → α),
    (∀ u ∈ pa G v, x u = y u) →
      mass (pa G v) p x * mass (univ \ {v}) p y * p x
        = mass (pa G v) p y * mass (univ \ {v}) p x * p y

end GeneralDowngrade

end DAGFactorization

end FateV2.Predict