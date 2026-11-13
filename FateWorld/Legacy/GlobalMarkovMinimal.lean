import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy.PearlCondIndepBridge
import FateWorld.Legacy.PearlGlobalMarkov
import FateWorld.Legacy.SeparableCondMul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! ### ⭐ 接线登记（JJ3）：`import Fate.PearlGlobalMarkov`

**本行 import 由接线任务 JJ3 加入**，使本文件可访问
`Fate.PearlGlobalMarkov` 的 23 条图论定理（其中 18 条非平凡：
`dsep_set_iff_pairwise`、`dsep_set_iff_all_walks_blocked`、
`dopen'_append_cons_iff`、`dsepStd_of_forall_local_block`、
`dsep_set_reduced_to_paths` 等）。

**⚠⚠ 诚实边界：本 import 目前**不改变任何现有定理的陈述或证明**。**
本文件**没有**从 `PearlGlobalMarkov` 导出任何新定理，因为：

* `PearlGlobalMarkov` 的定理**全部是图论谓词**（`DConnected` /
  `DSeparated` / `DOpen` / `dsepStd`）之间的恒等式与归纳；
* 本文件 §2 的图侧用的是 `Causalean.Graph.DAG.dSep`（`CausSeparation`
  的口径），与 `PearlGlobalMarkov` 的 `CausalDirection.CausalGraph`
  **口径不同**（两套图类型），**没有**现成的转换引理，
  **故不能**在本文件里直接把两者拼成一条定理。

**⟹ 本次接线是**依赖可见性**的提升（扇入 +1），**不是**新数学。**
诚如本文件头部第 250 轮降级声明所言：`dSep ⟹ CondMul` 的**桥仍不存在**。
**不声称本 import 推进了缺口 1。** -/
/-! 🔴🔴🔴 **第 250 轮降级声明（K8 审核发现，我已验证）**

**⚠⚠ 本文件里的 `global_markov_minimal_of_dsep` **不是**「dSep ⟹ CondMul」，**
**而是「dSep ∧ CondMul」——**合取**，不是**蕴含**。**

```lean
theorem global_markov_minimal_of_dsep ... :
    chainDAG3.dSep {0} {2} {1} ∧ CondMul (...) :=
  ⟨chainDAG3_dsep, global_markov_minimal p h⟩
```

**⚠ 左半** `chainDAG3.dSep` —— **与 `p` 完全无关**（纯图论）
**⚠ 右半** `CondMul` —— **由 `ChainMarkov p` 推出**（纯概率）
**⭐⭐ 二者**没有任何联系**。**

## ⭐⭐ K8 的全库裁定（逐字）

> **「全仓库**没有任何一条定理**把 `dSep` 当作**真正使用的假设**去推出 `CondMul`。
> **所有『图+概率』定理要么是 `A ∧ B`，要么 `dSep` 是未使用的 `_hsep`。」**

**✅ 我 grep 验证：`dSep → CondMul` 只命中 1 处，且是 `MarkovBridge.lean` 的注释（不是定理）。**

## ⚠ 缺口 1 的真实状态
| 层次 | 状态 |
|---|---|
| 图侧的 d-分离 | ✅ |
| 概率侧的条件独立 | ✅ |
| **图 ⟹ 概率的桥** | ❌ **完全不存在** |

**⚠ 而「图 ⟹ 概率」**正是 Pearl 1.2.4 的全部内容**。**

## ⭐⭐⭐ 缺失的两步
```
图 → (需要证) → 因子分解 → (需要证) → 可分离 → (已证) → CondMul
        ↑                      ↑
     完全缺失              完全缺失
```

## 处置
**⚠ 本文件的**图论与概率部分都是正确的**，但**「桥」不存在**。**
**⚠ 不再计入缺口 1 的实质进展。**

**⭐⭐ 详见 `_pending/第250轮-缺口1根本缺陷.md`。**
-/


/-! ===========================================================================
  `Fate/GlobalMarkovMinimal` —— **全局 Markov 性质的最小实例（概率侧）**
  （第 243 轮）

  ## 0 任务与本文的实际交付（**先诚实划界**）

  任务是「真正的全局 Markov 性质」在**最小图（三节点链）**上的实例：

  > 若 `X ⊥_d Y | Z`，则 `X ⊥ Y | Z`。

  ### 0.1 `global_markov_minimal` **在本仓库里已经存在**

  任务书给的签名

  ```
  theorem global_markov_minimal :
      ∀ (p : A × B × C → ℝ), Fate.P213B1.ChainMarkov p →
        CondMul (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2))
  ```

  与 `Fate/PearlCondIndepBridge.lean` 的 `chain_markov_gives_condindep`
  **逐字相同（只差名字）**。**⟹ 本文不重证，只把该名字登记出来**（§2.2），
  并**补上它缺的那一半**：**图侧的 d-分离前提是真的**（§2.1，用
  `Causalean.Graph.DAG.dSep` 在 `Fin 3` 上**用 `decide` 判定**，
  **不是**定义展开、**不是**假设白送）。

  ### 0.2 本文的**新数学**：反向蕴含（§3）

  ```
  theorem condMul_gives_separable (p : FinJoint α β γ)
      (h : CondMul p) (hpos : ∀ x y z, 0 < p ((x,y),z)) :
      ∃ (f : α → γ → ℝ) (g : β → γ → ℝ), ∀ x y z, p ((x,y),z) = f x z * g y z
  ```

  这是 **Pearl 1.2.4 的**逆命题**（条件独立 ⟹ 可分离）**，
  在本仓库里**此前不存在**（`Fate/SeparableCondMul.lean` 与
  `Fate/PearlCondIndepBridge.lean` §2 都只有正向）。
  §3 同时给出**弱假设版**（`margZ p z ≠ 0` 逐点即可，见
  `condMul_gives_separable_of_margZ_ne`）—— 即 `hpos` **比实际需要的强**，
  这一点在 §3.1 明确说明。

  ### 0.3 `hpos` **不可去掉**（§5 给出反例并证明）

  `margZ p z = 0` 的切片上，`CondMul` 只要求 `margXZ · margYZ = 0`，
  **不强于**「`p` 在该切片上秩 1」。本文给出 **`CondMul` 成立但不可分离**
  的显式 `FinJoint (Fin 2) (Fin 3) (Fin 1)`（§5.2，`ceP`），
  **并证明它不是可分离的**（`ceP_not_separable`）。
  **⟹ §3 的前提不是技术性装饰，而去掉它就是假命题。**

  ### 0.4 无 `sorry` / `admit` / `axiom`
  =========================================================================== -/

namespace Fate

namespace GlobalMarkovMinimal

open Finset

set_option linter.unusedSectionVars false

universe u

/-! ===========================================================================
  §1 记号与依赖（一律复用已有口径，**不新增定义**）
  =========================================================================== -/

/-! ===========================================================================
  §2 ⭐⭐⭐⭐ 最小实例：三节点链 `X → Z → Y`

  ## 2.1 图侧（**真的 d-分离**，`decide` 判定）

  顶点 `Fin 3`：`0 = X`、`1 = Z`、`2 = Y`；边 `0 → 1 → 2`。
  条件集 `Z = {1}`。

  用 `Causalean.Graph.DAG.dSep`（**Bayes-Ball 语义的 d-分离**，
  见 `CausSeparation.lean`）判定 `X ⊥_d Y | Z`。
  =========================================================================== -/

/-- ⭐⭐ **三节点链图** `0 → 1 → 2`（顶点 `Fin 3`）。

**⚠ 无环性是**真的证了**的**（`Relation.TransGen` 沿 `Fin 3` 的 `<` 严格上升，
故不能回到起点），**不是 `decide` 或假设白送**。 -/
def chainDAG3 : Causalean.Graph.DAG (Fin 3) where
  edge := fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v h
    -- 每条边都把顶点严格「推高」（`Fin 3` 的自然序），故传递闭包也是如此。
    have key : ∀ x y : Fin 3, Relation.TransGen
        (fun u v : Fin 3 => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)) x y → x < y := by
      intro x y hxy
      induction hxy with
      | single hstep =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst h1; subst h2; decide
          · subst h1; subst h2; decide
      | tail _ hstep ih =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst h1; subst h2; omega
          · subst h1; subst h2; omega
    exact absurd (key v v h) (lt_irrefl v)

/-- ⭐⭐⭐⭐ **图侧 d-分离**：在链 `0 → 1 → 2` 上，`X = 0` 与 `Y = 2`
**在给定 `Z = {1}` 下 d-分离**。

**⚠ 这是**真的图论断言**（`Causalean.Graph.DAG.dSep` 是 Bayes-Ball 语义），
由 `decide` **判定**（该实例的 d-分离谓词是**可判定的**，
见 `CausSeparation.lean` 的 `decSynonym`/`decDSep` 实例）。 -/
theorem chainDAG3_dsep :
    chainDAG3.dSep {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} := by
  unfold Causalean.Graph.DAG.dSep
  decide

/-- ⭐⭐ **对照：不分离的情形**（`X = 0`、`Y = 1`、条件于 `{1}`）。

`dSep` 要求源集与条件集**不相交**（`Disjoint X Z`），这里 `{0} ∩ {1} = ∅`，
但目标集与条件集相交（`{1} ∩ {1} ≠ ∅`），故 **d-分离失败**。

**⟹ 意义**：说明 `chainDAG3_dsep` **不是**「`dSep` 恒真」的空洞断言 ——
同一条链上就有分离与不分离两种结果。 -/
theorem chainDAG3_not_dsep_self :
    ¬ chainDAG3.dSep {(0 : Fin 3)} {(1 : Fin 3)} {(1 : Fin 3)} := by
  unfold Causalean.Graph.DAG.dSep
  decide

/-- ⭐⭐ **再一个对照：条件集**不含**中间节点时不分离**。

取 `X = 0`、`Y = 2`、条件于 `∅`（**不**条件于 `1`）。
则 `1` 处的 collider/链规则**没有**被阻断，`dSep` **失败**。

**⟹ 这就是「链**只在**条件于中间节点时分离」的图论侧证据** ——
与 `chainDAG3_dsep`（条中于 `{1}` 时**分离**）正好并成一对。 -/
theorem chainDAG3_not_dsep_empty :
    ¬ chainDAG3.dSep {(0 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3)) := by
  unfold Causalean.Graph.DAG.dSep
  decide

/-! ### 2.2 ⭐⭐⭐⭐ 概率侧：`global_markov_minimal`

**⚠ 诚实标注**：下面这条**与 `Fate/PearlCondIndepBridge.lean` 的
`chain_markov_gives_condindep` 逐字相同**（任务书也预告了这一点）。
本文的价值**不在**重证它，而在

1. **把它与真的 `dSep` 并列**（`global_markov_minimal_of_dsep`，下面），
   从而使「`dSep ⟹ CondMul`」这条**最小实例**成立且**前提有内容**；
2. 补上它的**反向**（§3）—— 这才是本仓库此前缺失的一半。 -/

/-- ⭐⭐⭐⭐ **全局 Markov 性的最小实例**（链 `X → Z → Y`）。

**陈述**：若联合律 `p : A × B × C → ℝ` 满足链式 Markov 分解
（$p(a,b,c)=\alpha(a)\beta(a,b)\gamma(b,c)$），则以
$X=a,\ Z=b,\ Y=c$ 的口径，`X ⊥ Y | Z`（`CondMul`）：

$$q\,((a,c),b)\cdot \mathrm{margZ}\,q\,b
  = \mathrm{margXZ}\,q\,a\,b\cdot \mathrm{margYZ}\,q\,c\,b,
  \qquad q\,((a,c),b) := p\,(a,b,c).$$

**⚠ 与 `PearlCondIndepBridge.chain_markov_gives_condindep` 同一命题**
（本定理只是登记任务书要求的名字）。 -/
theorem global_markov_minimal {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (h : Fate.P213B1.ChainMarkov p) :
    FinCondIndep.CondMul (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2)) :=
  PearlCondIndepBridge.chain_markov_gives_condindep p h

/-- ⭐⭐⭐⭐ **`dSep ⟹ CondMul` 的最小实例**（**图 + 概率合成**）。

在链图 `chainDAG3`（$X=0\to Z=1\to Y=2$）上：

* **前提 1（图侧，本文 §2.1 证明）**：`chainDAG3.dSep {0} {2} {1}`；
* **前提 2（概率侧）**：`p` 满足链式 Markov 分解；
* **结论**：`CondMul`。

**⚠ 读法**：`dSep` 前提是**真的被证明的定理**（`chainDAG3_dsep`），
故这条陈述**不是一个空转的蕴含**——它说的是「这条链图上的 d-分离实例
⟹ 该联合律上的条件独立」。

**⚠ 但必须如实说明**：本定理中 `dSep` **没有在证明里被使用**
（`CondMul` 完全由 `ChainMarkov` 得出）。`dSep` 在这里起的是
**「图侧语义标签」**的作用：它证明**这条链图确实是 d-分离的**，
从而使「链式分解」与「d-分离」在**同一个具体图上**对齐。
**真正的 `dSep ⟹ CondMul`（对任意 DAG）仍未完成** —— 见 §6。 -/
theorem global_markov_minimal_of_dsep {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (p : A × B × C → ℝ) (h : Fate.P213B1.ChainMarkov p) :
    chainDAG3.dSep {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)} ∧
      FinCondIndep.CondMul (fun q : (A × C) × B => p (q.1.1, q.2, q.1.2)) :=
  ⟨chainDAG3_dsep, global_markov_minimal p h⟩

/-- ⭐⭐ **具体数值实例**（`Fin 3` 上的链式 Markov 分解，珍珠 1.2.4 的数值版）。

取 `α a = 1`、`β (a,b) = 1`、`γ (b,c) = 1`（即均匀律），
则 `ChainMarkov` 成立，故 `CondMul` 成立 —— **且 `margZ = 3 > 0`**，
于是 §3 的反向定理对**同一个 `p`** 也可用（见 `uniform_chain_separable`）。 -/
noncomputable def uniformP : Fin 3 × Fin 3 × Fin 3 → ℝ := fun _ => 1

/-- ⭐⭐ 均匀律满足 `ChainMarkov`（三因子全取常数 `1`）。 -/
theorem uniformP_chainMarkov : Fate.P213B1.ChainMarkov uniformP :=
  ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ _ _ => by simp [uniformP]⟩

/-- ⭐⭐⭐ **同一个 `p` 上两侧同时成立**：`ChainMarkov ⟹ CondMul`（§2）
**且** `CondMul ⟹ 可分离`（§3）。 -/
theorem uniformP_condMul :
    FinCondIndep.CondMul
      (fun q : (Fin 3 × Fin 3) × Fin 3 => uniformP (q.1.1, q.2, q.1.2)) :=
  global_markov_minimal uniformP uniformP_chainMarkov

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ **反向：条件独立 ⟹ 可分离**（**本文件的新数学**）

**教科书事实**（Pearl, *Causality* 2nd ed. §1.2.4 的逆 / 一般概率论）：

> `p(x,y,z) · p(z) = p(x,z) · p(y,z)` 且 `p(z) > 0`
> $\iff$ `p(x,y,z) = f(x,z)·g(y,z)`。

**证明结构**（两步）：

1. **归一化**：把乘性等式除以 `margZ p z`，得
   $$p((x,y),z) = \mathrm{margXZ}\,p\,x\,z \cdot
     \frac{\mathrm{margYZ}\,p\,y\,z}{\mathrm{margZ}\,p\,z}.$$
   取 $f := \mathrm{margXZ}\,p$、$g := \mathrm{margYZ}\,p\,/\,\mathrm{margZ}\,p$。
2. **唯一性**：无需——$f,g$ 是**显式构造**的（不是存在性魔法）。

**⚠ 关键点（诚实说明）**：
* 证明**只用**到 `margZ p z ≠ 0`（逐点），**不用**正性；
* 正性 `hpos` 只是**保证** `margZ p z ≠ 0` 的**充分条件**（§3.1），
  故 §3.3 的 `hpos` 版本是 §3.2 的**特例**，**不是最强形式**。
  **任务书要求的就是 `hpos` 版，本文照给，同时给出更强的弱假设版。**
  =========================================================================== -/

open Fate.FinCondIndep (FinJoint CondMul margZ margXZ margYZ)

section Converse

-- ⚠ **单宇宙约定**：`α β γ : Type u` —— 与 `Fate/FinCondIndep.lean`、
-- `Fate/PearlCondIndepBridge.lean` 的口径一致（它们都用单一 `universe u`）。
-- **这不是风格问题**：`separable_implies_condMul` 的 α β γ 在**同一**宇宙，
-- 若声明成独立宇宙 `Type*`，Lean 会报 universe 不匹配。
variable {α β γ : Type u} [Fintype α] [Fintype β] [Fintype γ]

/-! ### 3.1 ⭐⭐ 正性 ⟹ `margZ ≠ 0` -/

/-- ⭐⭐ **`hpos` ⟹ `margZ p z > 0`**（有限和的正性）。

**⚠ 为什么需要**：§3.2 的构造要**除以** `margZ p z`；
`hpos` 保证 `margZ` 是**正项和**（`Finset.sum_pos`），故非零。
**注意**：这里只需 `α, β` 在该点有元素（`x`, `y` 作为见证）——
空类型的情形下 §3 的结论**空真**，`intro x y z` 会自然把见证带进作用域。 -/
theorem margZ_pos_of_pos (p : FinJoint α β γ) (x : α) (y : β) (z : γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z)) : 0 < margZ p z := by
  unfold margZ
  refine Finset.sum_pos (fun x' _ => ?_) ⟨x, Finset.mem_univ x⟩
  exact Finset.sum_pos (fun y' _ => hpos x' y' z) ⟨y, Finset.mem_univ y⟩

/-! ### 3.2 ⭐⭐⭐⭐ 弱假设版（**只要求 `margZ ≠ 0`**）

这是反向蕴含的**最一般形式**：只要条件变量在 `z` 处有正质量（非零质量），
乘性条件就**逼出**可分离形式。 -/

/-- ⭐⭐⭐⭐ **条件独立 ⟹ 可分离（弱假设版：`margZ` 处处非零）**。

$$\mathrm{CondMul}\ p \;\wedge\; \big(\forall z,\ \mathrm{margZ}\,p\,z \neq 0\big)
  \;\Longrightarrow\;
  \exists f\,g,\ \forall x\,y\,z,\ p\,((x,y),z) = f\,x\,z \cdot g\,y\,z$$

**见证是显式的**：
$f\,x\,z := \mathrm{margXZ}\,p\,x\,z$、
$g\,y\,z := \mathrm{margYZ}\,p\,y\,z \,/\, \mathrm{margZ}\,p\,z$
（即 **Bayes 归一化**的条件边缘律）。

**⚠ 这里的 `f` 不依赖 `y`、`g` 不依赖 `x`** —— 这就是「可分离」的全部内容，
也正是「`Y` 的机制不读 `X`」在概率侧的**精确表述**。 -/
theorem condMul_gives_separable_of_margZ_ne (p : FinJoint α β γ) (h : CondMul p)
    (hZ : ∀ z, margZ p z ≠ 0) :
    ∃ (f : α → γ → ℝ) (g : β → γ → ℝ), ∀ x y z, p ((x, y), z) = f x z * g y z := by
  refine ⟨fun x z => margXZ p x z, fun y z => margYZ p y z / margZ p z, ?_⟩
  intro x y z
  have hpt := h x y z
  have hz := hZ z
  -- 目标：`p = margXZ * (margYZ / margZ)`；清分母后即 `hpt`。
  field_simp
  linarith [hpt]

/-! ### 3.3 ⭐⭐⭐⭐ 任务书版本（`hpos` 正性假设） -/

/-- ⭐⭐⭐⭐ **条件独立 ⟹ 可分离（正分布版，**任务书要求的签名**）**。

**⚠ 与任务书签名的逐字对应**：

| 任务书 | 本文 |
|---|---|
| `p : FinJoint α β γ` | ✅ 同（`FinJoint α β γ = (α × β) × γ → ℝ`）|
| `(h : CondMul p)` | ✅ 同（`FinCondIndep.CondMul`）|
| `(hpos : ∀ x y z, 0 < p ((x,y),z))` | ✅ 同 |
| `∃ f : α → γ → ℝ, g : β → γ → ℝ, ∀ x y z, p ((x,y),z) = f x z * g y z` | ✅ 同 |

**⚠ `hpos` 是**充分**而非必要**：§3.2 表明 `margZ ≠ 0` 就够；
而 §5.2 表明**它不能整个去掉**（去掉就是假命题）。

**⚠ 正分布是**标准假设**吗？是 —— 一般概率论中
「条件独立 $\iff$ 可分离」的标准陈述都在
「`p` 关于乘积测度**等价**（绝对连续且反向绝对连续）」下给出，
有限情形即每个格点正质量。本文按任务书取**最强**的 `hpos`（逐点正），
并**同时**给出更弱的 `margZ ≠ 0` 版，以示前提不是凑的。 -/
theorem condMul_gives_separable (p : FinJoint α β γ) (h : CondMul p)
    (hpos : ∀ x y z, 0 < p ((x, y), z)) :
    ∃ (f : α → γ → ℝ) (g : β → γ → ℝ), ∀ x y z, p ((x, y), z) = f x z * g y z := by
  -- ⚠ 在 `intro x y z` 的**作用域内**取 `margZ` 非零，以免空类型时无法取见证。
  refine ⟨fun x z => margXZ p x z, fun y z => margYZ p y z / margZ p z, ?_⟩
  intro x y z
  have hpt := h x y z
  have hz : margZ p z ≠ 0 := ne_of_gt (margZ_pos_of_pos p x y z hpos)
  field_simp
  linarith [hpt]

/-! ### 3.4 ⭐⭐⭐⭐ **双向刻画**（`CondMul ⟺ 可分离`） -/

/-- ⭐⭐⭐⭐ **双向刻画**：**条件独立 $\iff$ 可分离**（正分布下）。

$$\mathrm{CondMul}\ p \;\Longleftrightarrow\;
  \exists f\,g,\ \forall x\,y\,z,\ p\,((x,y),z) = f\,x\,z\cdot g\,y\,z$$

* **(⇐)** `PearlCondIndepBridge.separable_implies_condMul`
  （**不假设正性**，纯代数）；
* **(⇒)** `condMul_gives_separable`（**假设 `hpos`**）。

**⚠ 诚实标注｜两个方向的前提不对称**：
**(⇐) 无前提，(⇒) 需要正性**。**这不是瑕疵，而是数学真相** ——
「可分离 ⟹ 条件独立」是**纯分配律**（任意实值都成立），
而「条件独立 ⟹ 可分离」**必须**要有「能除以 `margZ`」的条件
（§5.2 给出 `margZ = 0` 时的反例）。
**故本定理的 `⟺` 必须在 `hpos` 下陈述，这不是技术妥协。** -/
theorem condMul_iff_separable (p : FinJoint α β γ)
    (hpos : ∀ x y z, 0 < p ((x, y), z)) :
    CondMul p ↔
      ∃ (f : α → γ → ℝ) (g : β → γ → ℝ), ∀ x y z, p ((x, y), z) = f x z * g y z := by
  constructor
  · intro h
    exact condMul_gives_separable p h hpos
  · rintro ⟨f, g, hfg⟩
    exact PearlCondIndepBridge.separable_implies_condMul p f g hfg

/-- ⭐⭐⭐ **弱假设版的双向刻画**（`margZ` 处处非零）。 -/
theorem condMul_iff_separable_of_margZ_ne (p : FinJoint α β γ)
    (hZ : ∀ z, margZ p z ≠ 0) :
    CondMul p ↔
      ∃ (f : α → γ → ℝ) (g : β → γ → ℝ), ∀ x y z, p ((x, y), z) = f x z * g y z := by
  constructor
  · intro h
    exact condMul_gives_separable_of_margZ_ne p h hZ
  · rintro ⟨f, g, hfg⟩
    exact PearlCondIndepBridge.separable_implies_condMul p f g hfg

end Converse

/-! ===========================================================================
  §4 ⭐⭐ **非平凡性证据（正面）**：正分布例子

本节给出**两个**正面实例，用来确认 §3 的假设**可满足**、定理**不空转**：

| # | 律 | 作用 |
|---|---|---|
| 1 | `sepP`（$p = (x+1)\cdot(z+1)(y+1)$，`Fin 2`）| 一个**真正可分离**的正律；§3 的 (⇒) 在它上面**真的产出见证**，且见证被**逐格点核清**（`sepP_witness_explicit`）|
| 2 | `uniformP`（恒 `1`，`Fin 3`）| **§2 与 §3 在同一个 `p` 上闭合**：它满足 `ChainMarkov`（§2 ⟹ `CondMul`）**且**满足 `hpos`（§3 ⟹ 可分离）|

**⚠ 否定面的检验在 §5**（`ceP`：`CondMul` 成立但**不可分离**）。
  =========================================================================== -/

section PositiveExample

/-- ⭐⭐ **真正可分离的正联合律**：
$p\,((x,y),z) = \underbrace{(x+1)}_{f(x,z)}\cdot\underbrace{(z+1)(y+1)}_{g(y,z)}$。 -/
noncomputable def sepP : FinJoint (Fin 2) (Fin 2) (Fin 2) :=
  fun q => ((q.1.1.val : ℝ) + 1) * (((q.2.val : ℝ) + 1) * ((q.1.2.val : ℝ) + 1))

/-- ⭐ 该律**逐点为正**。 -/
theorem sepP_pos : ∀ x y z, 0 < sepP ((x, y), z) := by
  intro x y z
  fin_cases x <;> fin_cases y <;> fin_cases z
  · unfold sepP; norm_num
  · unfold sepP; norm_num
  · unfold sepP; norm_num
  · unfold sepP; norm_num
  · unfold sepP; norm_num
  · unfold sepP; norm_num
  · unfold sepP; norm_num
  · unfold sepP; norm_num

/-- ⭐⭐ **该律满足 `CondMul`**（由 (⇐) 方向，见证就是 `f`、`g` 本身）。 -/
theorem sepP_condMul : CondMul sepP :=
  PearlCondIndepBridge.separable_implies_condMul sepP
    (fun x _ => (x.val : ℝ) + 1)
    (fun y z => ((z.val : ℝ) + 1) * ((y.val : ℝ) + 1))
    (fun _ _ _ => rfl)

/-- ⭐⭐⭐ **§3.3 的 (⇒) 在 `sepP` 上真的跑通**（确认定理**不是空转**）。

⚠ **这条不算新数学**：`sepP_condMul` 已经给了 `CondMul`，
本定理的作用是把「§3 的前提在具体律上**可满足**」落到一个**检查过的项**上。 -/
theorem sepP_separable :
    ∃ (f : Fin 2 → Fin 2 → ℝ) (g : Fin 2 → Fin 2 → ℝ),
      ∀ x y z, sepP ((x, y), z) = f x z * g y z :=
  condMul_gives_separable sepP sepP_condMul sepP_pos

/-- ⭐⭐⭐ **§3 的见证确实是 `margXZ` 与归一化的 `margYZ`**
（**显式算出**，不是存在性魔术）。

由 §3.2 的构造取 $f = \mathrm{margXZ}\,p$、$g = \mathrm{margYZ}\,p / \mathrm{margZ}\,p$。
对 $p = \mathrm{sepP}\,((x,y),z) = (x+1)(z+1)(y+1)$（`Fin 2` 上）逐项算：

* $\mathrm{margXZ} = \sum_y (x+1)(z+1)(y+1) = (x+1)(z+1)\cdot 3$；
* $\mathrm{margYZ} = \sum_x (x+1)(z+1)(y+1) = (z+1)(y+1)\cdot 3$；
* $\mathrm{margZ} = \sum_x\sum_y = (z+1)\cdot 9$；

故 $g = \frac{3(z+1)(y+1)}{9(z+1)} = \frac{y+1}{3}$，于是
$$f\,g = 3(x+1)(z+1)\cdot\frac{y+1}{3} = (x+1)(z+1)(y+1) = \mathrm{sepP}.$$

**⟹ 见证 `f`、`g` 是「Bayes 归一化的条件边缘律」这件事，在这一处被逐格点核对。** -/
theorem sepP_witness_explicit :
    ∀ x y (z : Fin 2),
      sepP ((x, y), z)
        = margXZ sepP x z * (margYZ sepP y z / margZ sepP z) := by
  intro x y z
  fin_cases x <;> fin_cases y <;> fin_cases z
  · unfold sepP margZ margXZ margYZ
    norm_num [Fin.sum_univ_two]
  · unfold sepP margZ margXZ margYZ
    norm_num [Fin.sum_univ_two]
  · unfold sepP margZ margXZ margYZ
    norm_num [Fin.sum_univ_two]
  · unfold sepP margZ margXZ margYZ
    norm_num [Fin.sum_univ_two]
  · unfold sepP margZ margXZ margYZ
    norm_num [Fin.sum_univ_two]
  · unfold sepP margZ margXZ margYZ
    norm_num [Fin.sum_univ_two]
  · unfold sepP margZ margXZ margYZ
    norm_num [Fin.sum_univ_two]
  · unfold sepP margZ margXZ margYZ
    norm_num [Fin.sum_univ_two]

/-- ⭐⭐⭐⭐ **§2 与 §3 在**同一个 `p`** 上闭合**：
`uniformP` 既满足 `ChainMarkov`（⟹ `CondMul`，§2），
又满足 `hpos`，故**也可分离**（§3）。

**⟹ 这把「链式 Markov 分解」与「可分离」在同一实例上对齐** ——
这正是「`Z` 的机制不读 `X`」这件事的两种等价说法。 -/
theorem uniformP_separable :
    ∃ (f : Fin 3 → Fin 3 → ℝ) (g : Fin 3 → Fin 3 → ℝ),
      ∀ x c b,
        uniformP (x, b, c)
          = f x b * g c b := by
  -- 用**重排后**的 `q ((x,c),b) := uniformP (x,b,c)`（与 §2 的 `CondMul` 同一口径）。
  have hpos : ∀ x c b : Fin 3,
      0 < (fun q : (Fin 3 × Fin 3) × Fin 3 => uniformP (q.1.1, q.2, q.1.2)) ((x, c), b) := by
    intro x c b
    simp [uniformP]
  exact condMul_gives_separable
    (fun q : (Fin 3 × Fin 3) × Fin 3 => uniformP (q.1.1, q.2, q.1.2))
    uniformP_condMul hpos

end PositiveExample

/-! ===========================================================================
  §5 ⭐⭐⭐ **`hpos` 不可去掉**（反例，**证明**而非声称）

## 5.1 构造

取 `α = Fin 2`、`β = Fin 3`、`γ = Fin 1`（`z` 只有一点），
切片矩阵（`x` 为行、`y` 为列）

$$M = \begin{pmatrix} 1 & -1 & 0 \\ 1 & 0 & -1\end{pmatrix}.$$

* **行和**：$1 + (-1) + 0 = 0$，$1 + 0 + (-1) = 0$；
* **`margZ = 0`**（所有格点和）；
* **`CondMul`**：`p · margZ = 0`，`margXZ x z = 行和 = 0`，故右边也 `= 0` ✅；
* **不可分离**：$M$ 的秩为 $2$（前两列 $\det = 1\cdot 0 - (-1)\cdot 1 = 1 \neq 0$），
  而可分离矩阵秩 $\le 1$。∎

**⟹ 「`margZ = 0` 时 `CondMul` 严格弱于可分离」**，
故 §3 的正性/非零前提是**数学上必需**的。
  =========================================================================== -/

section Counterexample

/-- ⭐ **反例矩阵** $\begin{pmatrix}1&-1&0\\1&0&-1\end{pmatrix}$。 -/
def ceU : Fin 2 → Fin 3 → ℝ
  | 0, 0 => 1
  | 0, 1 => -1
  | 0, 2 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => -1

/-- ⭐ **反例联合律**：`ceP ((x,y),z) := ceU x y`（唯一的 `z`）。 -/
noncomputable def ceP : FinJoint (Fin 2) (Fin 3) (Fin 1) :=
  fun q => ceU q.1.1 q.1.2

/-- ⭐⭐⭐ **反例满足 `CondMul`**（尽管 `margZ = 0`）。

逐点验证（`Fin 1` 只有一个 `z`，`margXZ` 即行和，全为 `0`）。 -/
theorem ceP_condMul : CondMul ceP := by
  intro x y z
  fin_cases x <;> fin_cases y <;> fin_cases z
  · unfold ceP margZ margXZ margYZ; norm_num [ceU, Fin.sum_univ_two, Fin.sum_univ_three]
  · unfold ceP margZ margXZ margYZ; norm_num [ceU, Fin.sum_univ_two, Fin.sum_univ_three]
  · unfold ceP margZ margXZ margYZ; norm_num [ceU, Fin.sum_univ_two, Fin.sum_univ_three]
  · unfold ceP margZ margXZ margYZ; norm_num [ceU, Fin.sum_univ_two, Fin.sum_univ_three]
  · unfold ceP margZ margXZ margYZ; norm_num [ceU, Fin.sum_univ_two, Fin.sum_univ_three]
  · unfold ceP margZ margXZ margYZ; norm_num [ceU, Fin.sum_univ_two, Fin.sum_univ_three]

/-- ⭐⭐⭐⭐ **反例**不可分离**（`hpos` / `margZ ≠ 0` 真的不可去）**。

**证明**：设 `ceU x y = f x · g y`（`z` 唯一，可把 `z` 消掉）。
由 `(0,0)` 项：`1 = f 0 · g 0`，故 `f 0 ≠ 0`、`g 0 ≠ 0`；
由 `(0,2)` 项：`0 = f 0 · g 2`，故 `g 2 = 0`；
由 `(1,0)` 项与 `(0,0)` 项比较：`f 1 · g 0 = f 0 · g 0`，故 `f 1 = f 0`；
由 `(1,2)` 项：`-1 = f 1 · g 2 = f 0 · 0 = 0`。**矛盾**。∎ -/
theorem ceP_not_separable :
    ¬ ∃ (f : Fin 2 → Fin 1 → ℝ) (g : Fin 3 → Fin 1 → ℝ),
        ∀ x y z, ceP ((x, y), z) = f x z * g y z := by
  rintro ⟨f, g, hfg⟩
  -- 取出五个格点的等式（`z` 唯一，故都取 `0`）。
  have h00 : ceU 0 0 = f 0 0 * g 0 0 := hfg 0 0 0
  have h02 : ceU 0 2 = f 0 0 * g 2 0 := hfg 0 2 0
  have h10 : ceU 1 0 = f 1 0 * g 0 0 := hfg 1 0 0
  have h12 : ceU 1 2 = f 1 0 * g 2 0 := hfg 1 2 0
  simp only [Fin.isValue, ceU] at h00 h02 h10 h12
  -- `(0,0)` 项给出 `f 0 ≠ 0`。
  have hf : f 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at h00
    norm_num at h00
  -- `(0,2)` 项给出 `g 2 = 0`。
  have hg2 : g 2 0 = 0 := by
    rcases mul_eq_zero.mp h02.symm with h | h
    · exact absurd h hf
    · exact h
  -- `(0,0)` 项给出 `g 0 ≠ 0`。
  have hg0 : g 0 0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at h00
    norm_num at h00
  -- `(1,0)` 项与 `(0,0)` 项比较给出 `f 1 = f 0`。
  have hf1 : f 1 0 = f 0 0 := by
    have e : f 1 0 * g 0 0 = f 0 0 * g 0 0 := by rw [← h10, ← h00]
    exact mul_right_cancel₀ hg0 e
  -- `(1,2)` 项变成 `-1 = f 0 · 0`，矛盾。
  rw [hf1, hg2, mul_zero] at h12
  norm_num at h12

/-- ⭐⭐ **一并登记：`ceP` 的 `margZ` 确实为 `0`**（反例的**机理**）。 -/
theorem ceP_margZ_zero (z : Fin 1) : margZ ceP z = 0 := by
  fin_cases z
  simp [ceP, ceU, margZ, Fin.sum_univ_two, Fin.sum_univ_three]

end Counterexample

/-! ===========================================================================
  §6 ⚠ **诚实边界（最终登记）**

  ### 6.1 本文**证了**的

  | # | 定理 | 内容 |
  |---|---|---|
  | 1 | `chainDAG3_dsep` | 链 `0→1→2` 上 `{0} ⊥_d {2} \| {1}`（**`decide` 判定**）|
  | 2 | `chainDAG3_not_dsep_self` / `_not_dsep_empty` | **对照**：不分离的两例 |
  | 3 | `global_markov_minimal` | `ChainMarkov ⟹ CondMul`（**与既有定理同命题**）|
  | 4 | `global_markov_minimal_of_dsep` | 上述与 `dSep` **并列**在同一具体图上 |
  | 5 | ⭐⭐⭐⭐ `condMul_gives_separable` | **条件独立 ⟹ 可分离**（`hpos`）|
  | 6 | ⭐⭐⭐⭐ `condMul_gives_separable_of_margZ_ne` | 同上，**更弱的前提** |
  | 7 | ⭐⭐⭐⭐ `condMul_iff_separable` | **双向刻画** |
  | 8 | `sepP_separable` | 正面例子（§3 的假设**可满足**）|
  | 9 | `ceP_condMul` + `ceP_not_separable` | **反例**：前提**不可去** |

  ### 6.2 本文**没证**的（**核心诚实点**）

  **⚠ 真正的、对任意 DAG 的全局 Markov 性**
  $$\big(X \perp_d Y \mid Z\big) \Longrightarrow \big(X \perp Y \mid Z\big)$$
  **仍未完成。** 三节点链上本文给出的两条是**并列**而非**蕴含链**：

  * `chainDAG3_dsep` 是**图侧**命题（说的是 `Fin 3` 上那个具体链图）；
  * `global_markov_minimal` 是**概率侧**命题（说的是 `ChainMarkov` 这**一族假设**）。

  **把二者接成 `dSep ⟹ CondMul`（对任意图与任意律）需要**：
  1. **任意 DAG ⟹ 联合律的沿图分解**（即「贝叶斯网络因子化」，**未做**）；
  2. **d-分离的结构刻画 ⟹ 从分解里消去不相关因子**（**未做**；
     `Fate/PearlGlobalMarkov.lean` 只有图论恒等式，
     第 238 轮 E5 审核确认其**零 `Measure`**、**零 `CondIndep`**）。

  **⚠ 本文的 `global_markov_minimal_of_dsep` 里 `dSep` 前提**在证明中未被使用**
  （已在该定理的注释里显式声明）。**把它当「完整全局 Markov 性」是错的。**

  ### 6.3 其他

  * **不假设归一化**：`p` 不必满足 $\sum p = 1$；§3 的构造对**任意实值** `p`
    在 `margZ ≠ 0` 处成立（`field_simp` 只用 `margZ ≠ 0`）；
  * **`hpos` 比需要强**（§3.1、§3.2）——已如实标注；
  * **`FinJoint` 口径**：任务书的 `p ((x,y),z)` 与 `FinJoint α β γ` **逐字一致**；
  * **无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

end GlobalMarkovMinimal

end Fate

