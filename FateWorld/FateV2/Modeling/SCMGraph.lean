import FateWorld.FateV2.Modeling.PearlHierarchy
import FateWorld.FateV2.Modeling.CausDAG
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/SCMGraph.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-007 D-008 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Modeling（正文 17 处，含 2 条 import；Causalean.Graph→FateV2.Modeling.Graph 2 处）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Modeling
open FateV2.Predict

/-! ===========================================================================
  `FateV2.Modeling.SCMGraph` —— **从 SCM 的 `sg` 提取「谁依赖谁」，构造 `SCMGraph`**
  ===========================================================================

  ## 0. 这份文件偿还的债务

  `FateV2.Modeling/BackdoorGenuine.lean` 的文件头（第 121 行）把 **D-BD-2** 的还债方案
  写成三件事：

  > | **D-BD-2** | 图侧 `dSep` 与数值层脱钩 |
  > | **§4 `SCMGraph`（从 SCM 造图）** + **§5 真 `dSep` 判定** + **§6 对齐定理** |

  其中 **§4「从 SCM 造图」** 是**唯一缺失**的起点：`BackdoorGenuine` 里的
  `moralAdj` / `moralGraph`（`FateV2.Modeling.R277`）**直接手写**了 `Z → X`、`Ux → X`、
  `X → Y` … 这些边，**没有经过任何 SCM** —— 于是「图是否忠实于模型」
  这件事在该文件里**无法被检验**（这正是 D-BD-2 的实质）。

  **本文件把这一步补上**：从 `FateV2.Modeling.PearlHierarchy.SCM`（载体就是作者点名的
  `sg : U → X × (X → Y)`）**机械地**提取依赖关系，构造真正的有向图
  `SCMGraph M : FateV2.Modeling.Graph.DAG (SV M)`，并把「图的性质」与
  「模型的概率性质」**真的接上**（§4–§5）。

  ## 1. 载体：`sg : U → X × (X → Y)` 究竟说了什么

  ```
  sg u = (x, h)     读作：外生实现 u 下，事实取值 X = x，
                          结构方程 Y := h(X)
  ```

  于是**唯一的依赖来源**是 `sg` 的两个分量：

  | 依赖 | 判据（**从 `sg` 提取**） | § |
  |---|---|---|
  | `U ⟶ X` | `u ↦ (sg u).1` 非常值 | §2.1 `depUX` |
  | `X ⟶ Y` | 某个 `(sg u).2` 非常值 | §2.2 `depXY` |
  | `U ⟶ Y`（**未观测混杂 / 直接效应**） | 存在 `u₁,u₂` **同 `X`** 而 `Y` 值不同 | §2.3 `depUY` |

  **⚠ 第三条是本文件的技术核心**（§2.3 的注释详述）：`sg` 的**第二分量本身是函数**
  （`h : X → Y`），所以「`Y` 依赖 `U`」**不能**写成「`h` 不是常值函数」那种
  显然假的东西；正确的形式是 **「控制住 `X` 之后 `Y` 仍随 `u` 变」**，
  即 **同一个 `X` 值下 `Y` 有两个不同的实现** —— 这正是 Pearl 的
  「未观测混杂」/「`U → Y` 直接边」的定义。

  ## 2. 交付清单

  | # | 内容 | 等级 |
  |---|---|---|
  | 1 | `SV M = U ⊔ X ⊔ Y`（顶点）、`Fintype`/`DecidableEq` | [构造] |
  | 2 | `depUX` / `depXY` / `depUY`（**依赖谓词**，从 `sg` 提取） | [构造] |
  | 3 | `edge`（**结构边**：事实发生的值关系）+ `SCMGraph : DAG` | [构造] |
  | 4 | **`SCMGraph` 真的是 DAG**（势函数 `rank` 证无环，**不是** acyclicity 假设） | [理论] |
  | 5 | `SCMGraph` 的结构定理：`Y` 是叶、`X` 只有 `U` 父、`U` 是源 | [理论] |
  | 6 | **`noConf_iff_det`**：`¬depUY ↔ ∃ g, ∀ u, Y(u) = g(X(u))` | [理论] |
  | 7 | **`L1_obs_eq_zero_of_noConf`**：`¬depUY ⟹ P(x,y) = 0` 对 `y ≠ g x` | [理论] |
  | 8 | **`L2_do_const_of_noDepXY`**：无 `X→Y` 依赖 ⟹ 干预律与 `x` 无关 | [理论] |
  | 9 | 具体实例：`confM`（有混杂）、`pureM`（纯因果）、`constM`（`X` 不依赖 `U`） | [验证] |
  | 10 | 三个实例的**图判定**（`depUY` 真/假、`depUX` 假）**逐条机检** | [验证] |
  | 11 | **`confM_no_det_response`**：`depUY` 真 ⟹ **不存在**回复函数 `g` | [验证] |
  | 12 | **`confM_obs_both`**：同一 `X` 下 `P(x,false) = P(x,true) = 1/4` | [验证] |
  | 13 | **`pureM_obs_on_image`**：`P(true,true) = 1/2`（非「全零律」） | [验证] |

  ## 3. ⚠ 诚实边界（**不掩饰**）

  1. **`SCMGraph` 的边是「事实发生的值关系」，不是「反事实的依赖」**（§3.1 详述）。
     例如 `edge (.x s) (.y v)` 说的是「存在 `u` 使 `X=s` 且 `Y=v`」——
     **不是**「若 `X` 取别的值 `Y` 会变」。**反事实依赖**由 `depXY`（§2.2）承担，
     二者**不等价**（§3.3 给出 `edge` 有边而 `depXY` 假的情形）。
     **这是本文件的**主要局限**，也是它与「`BackdoorGenuine.moralAdj` 直接手写边」
     的分工：`moralAdj` 手写的是**反事实依赖**，本文件的 `SCMGraph` 是
     **值关系图**；§6 说明两者的关系与**尚未打通的接口**。

  2. **不含 `depUY` 对应边的「独立性」，只证了「支撑收缩」**（§5）。
     `L1_obs_eq_zero_of_noConf` 是**硬**的（不依赖 `pU ≥ 0`，因为 `push` 的每项是
     `pU u * 0`），但它的**否定方向**（`depUY ⟹ P` 真的不同）**未证** ——
     那需要「存在 `u` 使 `pU u ≠ 0`」，本文件**不做**这个假设，
     故**不声称**「`depUY` ⟺ 观测到的混杂」。

  3. **`dSep`（`USeparated`）没有在本文件出现。** 本文件交付的是
     `BackdoorGenuine` 头表里 **`§4 SCMGraph` 这一格**；`§5 真 dSep 判定` 与
     `§6 对齐定理` 是**后续**工作（需要 `SG` 图与 `FateV2.Modeling.R277.Vert` 图的**桥接**，
     本文件 §6 只登记缺口，不假称完成）。

  4. **只做有限离散**（`Fintype`），概率是 `ℝ`-值函数，无测度。与 `PearlHierarchy`
     完全同口径。

  5. **`inducedY` 用 `Classical.choice`**（`if h : ∃ u, (sg u).1 = x then ...`），
     它对 `X` 的**不可实现值**给出 `Classical.arbitrary`。故 `noConf_iff_det` 的
     `g` 只在**可实现**的 `x` 上被唯一确定 —— 这正是定理陈述里
     `∀ u, ... = g ((sg u).1)`（只对**实现点**断言）而非 `∀ x` 的原因。
-/

set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option autoImplicit false

namespace FateV2.Modeling.SCMGraph

open FateV2.Modeling.PearlHierarchy

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ===========================================================================
  §1 **顶点**：`U ⊔ X ⊔ Y`
  ===========================================================================

**⚠ 为什么把 `U` 放进顶点集**：Pearl 的因果图**必须**含未观测分量 ——
否则「`U` 存在但只经 `X` 影响 `Y`」与「`U` 还直接进 `Y`」**根本写不出来**
（前者是后门准则的适用前提，后者是混杂）。这一点与
`FateV2.Modeling.R277` 把 `Ux`/`Uy` 放进 `Vert` 的动机**完全一致**。

**⚠ 为什么手写 `Fintype`**：`SV M` 依赖参数 `M : SCM X Y`（其 `U` 字段是 `Type`
且 `Y` 出现在函数空间 `X → Y` 里），Lean 4 的 `deriving` **没有**
`Fintype` handler 能处理这种依赖参数 + 混合 universe 的情形
（`No deriving handlers have been implemented for class 'Fintype'`）。
故显式给编解码 `U ⊕ (X ⊕ Y)`。 -/

/-- **SCM 图的顶点**：外生 `U`、处理 `X`、结果 `Y`。 -/
inductive SV (M : SCM X Y) : Type _ where
  /-- 外生顶点。 -/
  | u (i : M.U) : SV M
  /-- 处理顶点。 -/
  | x (v : X) : SV M
  /-- 结果顶点。 -/
  | y (v : Y) : SV M
  deriving DecidableEq

namespace SV

/-- `SV` → 编码 `U ⊕ (X ⊕ Y)`。 -/
def enc : (M : SCM X Y) → SV M → (M.U ⊕ (X ⊕ Y))
  | _, .u i => Sum.inl i
  | _, .x v => Sum.inr (Sum.inl v)
  | _, .y v => Sum.inr (Sum.inr v)

/-- 编码 → `SV`（`enc` 的逆）。 -/
def dec (M : SCM X Y) : (M.U ⊕ (X ⊕ Y)) → SV M
  | Sum.inl i => .u i
  | Sum.inr (Sum.inl v) => .x v
  | Sum.inr (Sum.inr v) => .y v

theorem dec_enc (M : SCM X Y) (v : SV M) : dec M (enc M v) = v := by
  cases v <;> rfl

theorem enc_dec (M : SCM X Y) (v : M.U ⊕ (X ⊕ Y)) : enc M (dec M v) = v := by
  rcases v with a | (b | c) <;> rfl

/-- `SV M` 的 `Fintype`（经 `U ⊕ (X ⊕ Y)` 搬运）。 -/
instance instFintype (M : SCM X Y) : Fintype (SV M) :=
  Fintype.ofEquiv (M.U ⊕ (X ⊕ Y))
    (Equiv.mk (dec M) (enc M) (enc_dec M) (dec_enc M))

end SV

/-! ===========================================================================
  §2 **谁依赖谁**：从 `sg` 提取的三个依赖谓词
  =========================================================================== -/

/-- **`U ⟶ X` 依赖**：`X` 的取值**真的随 `u` 变**
（即 `u ↦ (sg u).1` 不是常值映射）。

**⚠ 为什么是「不是常值」而不是「存在两个不同的值」**：两者在 `U` 空时都假、
在 `U` 非空时等价；写成「`¬∃ x₀, ∀u`」**不需要 `Nonempty M.U`**，
故更少前提。 -/
def depUX (M : SCM X Y) : Prop :=
  ¬ ∃ x₀ : X, ∀ u : M.U, (M.sg u).1 = x₀

/-- **`X ⟶ Y` 依赖**：**某个**个体的结构方程 `h = (sg u).2` 非常值
（即 `Y` 至少对某个个体**真的随 `X` 变**）。

**⚠ 「某个个体」而不是「所有个体」**：图上的边是**存在性**断言 ——
只要一个个体上 `X` 对 `Y` 有影响，`X → Y` 这条边就在图里。
这也与 `depUX` 的「非常值」形式**同构**（一次量化个体，一次量化被依赖变量的取值）。 -/
def depXY (M : SCM X Y) : Prop :=
  ∃ u : M.U, ¬ ∃ y₀ : Y, ∀ x : X, (M.sg u).2 x = y₀

/-- **`U ⟶ Y` 依赖（未观测混杂 / 直接效应）**：**控制住 `X` 之后
`Y` 仍随 `u` 变**。

```
depUY M := ∃ u₁ u₂, (sg u₁).1 = (sg u₂).1 ∧ Y(u₁) ≠ Y(u₂)
```

**这是本文件的技术核心，也是最容易被写错的一条。** 三件事必须说清：

1. **不能**写成「`(sg u).2` 不是常值函数」—— `sg` 的第二分量**本身是函数**
   `X → Y`，所以「`h` 非常值」说的是「`Y` 依赖 **`X`**」，
   那是 `depXY`，**不是** `Y` 依赖 `U`。
2. **也不能**写成「`u ↦ (sg u).2 (sg u).1` 非常值」—— 那样只能抓到
   「`Y` 随 `u` 变」，**抓不到混杂**：若 `X` 随 `u` 变、`Y = g(X)` 是 `X` 的函数，
   则 `Y` 当然随 `u` 变，但**没有**未观测混杂。
3. **正确形式是「同 `X` 下 `Y` 不同」** —— 即把 `X` **控制住**（fix 住）之后再问
   `Y` 是否还随 `u` 变。这正是 `X` 与 `Y` 共享未观测原因的定义。

**⟹ 这就是 Pearl 图上的直接边 `U → Y`**：它绕开 `X` 直连 `Y`。
`¬ depUY` 就是「**无未观测混杂**」，§4 给出它的**等价刻画**
（`Y` 是 `X` 的一个函数），§5 给出它的**概率后果**（观测律支撑收缩到 `g` 的图像上）。 -/
def depUY (M : SCM X Y) : Prop :=
  ∃ u₁ u₂ : M.U, (M.sg u₁).1 = (M.sg u₂).1 ∧
    (M.sg u₁).2 (M.sg u₁).1 ≠ (M.sg u₂).2 (M.sg u₂).1

/-! ### §2.1 **依赖的等价形式**（把三个谓词翻译成「值域」的陈述） -/

/-- `depUX` 的等价形式：存在两个个体给出不同的 `X` 值（当 `U` 非空时）。 -/
theorem depUX_iff_exists_ne (M : SCM X Y) [Nonempty M.U] :
    depUX M ↔ ∃ u₁ u₂ : M.U, (M.sg u₁).1 ≠ (M.sg u₂).1 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h ⟨(M.sg (Classical.arbitrary M.U)).1, fun u => hc u _⟩
  · rintro ⟨u₁, u₂, hne⟩ ⟨x₀, hx⟩
    exact hne ((hx u₁).trans (hx u₂).symm)

/-- `depXY` 的展开：某个体上存在两个 `X` 值给出不同的 `Y`。 -/
theorem depXY_iff_exists_ne (M : SCM X Y) [Nonempty X] :
    depXY M ↔ ∃ (u : M.U) (x₁ x₂ : X), (M.sg u).2 x₁ ≠ (M.sg u).2 x₂ := by
  constructor
  · rintro ⟨u, hu⟩
    by_contra hc
    push Not at hc
    exact hu ⟨(M.sg u).2 (Classical.arbitrary X),
      fun x => hc u x (Classical.arbitrary X)⟩
  · rintro ⟨u, x₁, x₂, hne⟩
    refine ⟨u, ?_⟩
    rintro ⟨y₀, hy⟩
    exact hne ((hy x₁).trans (hy x₂).symm)

/-! ===========================================================================
  §3 **`SCMGraph`：从 `sg` 机械提取的有向图**
  ===========================================================================

## §3.1 `edge` 的口径：**事实发生的值关系**

```
edge (.u u) (.x v)  ⟺  (sg u).1 = v               -- 个体 u 的 X 确实是 v
edge (.u u) (.y v)  ⟺  (sg u).2 (sg u).1 = v      -- 个体 u 的 Y 确实是 v
edge (.x s) (.y v)  ⟺  ∃ u, X(u) = s ∧ Y(u) = v   -- 存在个体同时取 s 与 v
其余一律 False                                       -- 没有反向边、没有 U→U
```

**⚠ 与「反事实依赖」的区别**（§3.3 有具体反例）：
`edge (.x s) (.y v)` 说的是「`(X,Y) = (s,v)` 在某个个体上**发生了**」，
**不是**「`Y` 对 `X` 敏感」。所以在 `Y` 对 `X` **完全不敏感**的模型里
（例如 `h x = false` 恒成立），`edge (.x true) (.y false)` **仍然成立**。
**依赖**由 §2 的 `depXY` 承担。这个「两张图」的分工是**故意的**：
`edge` 供 `dSep`/祖先/拓扑序使用（§3.2 证明它是 DAG），
`depXY`/`depUY` 供「这是不是一个混杂模型」的判定使用（§4–§5）。 -/

/-- **SCM 的结构边**（事实发生的值关系）。 -/
def edge (M : SCM X Y) : SV M → SV M → Prop
  | .u u, .x v => (M.sg u).1 = v
  | .u u, .y v => (M.sg u).2 (M.sg u).1 = v
  | .x s, .y v => ∃ u : M.U, (M.sg u).1 = s ∧ (M.sg u).2 s = v
  | _, _ => False

/-! ### §3.2 **`SCMGraph` 确实是 DAG**（无环**由构造证明**，不是假设）

**证明手法**：定义**势函数** `rank : SV M → ℕ`（`U ↦ 0`、`X ↦ 1`、`Y ↦ 2`），
证 `edge a b → rank a < rank b`，则 `TransGen edge` 保持严格递增，
故无自环。这比「对 `TransGen` 做归纳」稳健得多（后者的目标含依赖索引 `SV M`，
`induction` 会报 `Invalid target`）。 -/

/-- 势函数：`U ↦ 0`、`X ↦ 1`、`Y ↦ 2`。 -/
def rank {M : SCM X Y} : SV M → ℕ
  | .u _ => 0
  | .x _ => 1
  | .y _ => 2

/-- **每条边都严格增大 `rank`**（因为边只从低层指向高层）。 -/
theorem edge_rank_lt {M : SCM X Y} {a b : SV M} (h : edge M a b) : rank a < rank b := by
  cases a <;> cases b <;> simp_all [edge, rank]

/-- **`SCMGraph` 无环**：`TransGen` 保持严格递增，故不可有自环。 -/
theorem acyclic (M : SCM X Y) (v : SV M) : ¬ Relation.TransGen (edge M) v v := by
  have key : ∀ {a b : SV M}, Relation.TransGen (edge M) a b → rank a < rank b := by
    intro a b hab
    induction hab with
    | single he => exact edge_rank_lt he
    | tail _ he ih => exact lt_trans ih (edge_rank_lt he)
  intro h
  exact absurd (key h) (lt_irrefl _)

/-- **`SCMGraph M`：从 `sg` 提取的有向无环图**。

**⚠ `decEdge := Classical.decRel _`**：判定的内容由 `sg` 决定（`X`/`Y`/`U` 都
`DecidableEq`），但 `edge` 的第三分支含 `∃`,
故走 `Classical.decRel`；使用处须 `classical`。 -/
noncomputable def SCMGraph (M : SCM X Y) : FateV2.Modeling.Graph.DAG (SV M) where
  edge := edge M
  decEdge := Classical.decRel _
  acyclic := acyclic M

/-! ### §3.2.1 **图的结构定理**（`SCMGraph` 的形状：`U → X → Y` 加 `U → Y`） -/

/-- **`Y` 是叶**：没有任何边从 `Y` 出发。 -/
theorem edge_from_y_false (M : SCM X Y) (v : Y) (b : SV M) :
    ¬ edge M (.y v) b := by
  cases b <;> simp [edge]

/-- **`X` 只有 `U` 型的父**：任何指向 `X` 的边都来自 `U`。 -/
theorem edge_to_x (M : SCM X Y) {a : SV M} {s : X} (h : edge M a (.x s)) :
    ∃ u : M.U, a = .u u := by
  cases a with
  | u i => exact ⟨i, rfl⟩
  | x _ => simp [edge] at h
  | y _ => simp [edge] at h

/-- **`U` 是源**：没有边进入 `U`。 -/
theorem edge_to_u_false (M : SCM X Y) (a : SV M) (i : M.U) : ¬ edge M a (.u i) := by
  cases a <;> simp [edge]

/-- **指向 `Y` 的边只来自 `X` 或 `U`**（不存在 `Y → Y`、`X` 内部的边等）。 -/
theorem edge_to_y_cases (M : SCM X Y) {a : SV M} {v : Y} (h : edge M a (.y v)) :
    (∃ s : X, a = .x s) ∨ (∃ u : M.U, a = .u u) := by
  cases a with
  | u i => exact Or.inr ⟨i, rfl⟩
  | x s => exact Or.inl ⟨s, rfl⟩
  | y _ => simp [edge] at h

/-- **`SCMGraph` 的祖先关系完全由 `rank` 层次决定**：
`Y` 的后代为空、`X` 的后代只可能是 `Y`。

（这是 §3.2 势函数的直接应用，也是「`SCMGraph` 忠实于 `U → X → Y` 加 `U → Y`
这一族三层图」的精确陈述。） -/
theorem no_descendant_of_y (M : SCM X Y) (v : Y) (b : SV M) :
    ¬ (SCMGraph M).isAncestor (.y v) b := by
  intro h
  have hlt := (SCMGraph M).isAncestor_iff_transGen.mp h
  have key : ∀ {a b : SV M}, Relation.TransGen (edge M) a b → rank a < rank b := by
    intro a b hab
    induction hab with
    | single he => exact edge_rank_lt he
    | tail _ he ih => exact lt_trans ih (edge_rank_lt he)
  have hlt' : rank (M := M) (SV.y v) < rank (M := M) b := key hlt
  cases b <;> simp [rank] at hlt'

/-! ### §3.3 ⚠ **`edge` 与 `depXY` 不等价**（**具体反例**）

`Y` 对 `X` **完全不敏感**的模型（`h x = false` 恒成立）里：

* `edge (.x true) (.y false)` **成立**（`(X,Y) = (true,false)` 确实发生）；
* `depXY` **假**（`h` 是常值函数）。

**⟹ 「`edge` 有边」不蕴含「`X` 影响 `Y`」。** 这个反例是本文件诚实边界的机检证据。 -/

/-- `X` 不敏感于 `Y` 的实例：`U = Unit`、`X = Bool`、`Y = Bool`、`h ≡ false`。 -/
noncomputable def flatM : SCM Bool Bool where
  U := Unit
  pU := fun _ => 1
  sg := fun _ => (true, fun _ => false)

/-- ⚠ **`edge` 有边到 `Y`**（`(true, false)` 发生了）。 -/
theorem flatM_edge_xy : edge flatM (.x true) (.y false) := by
  refine ⟨(), rfl, rfl⟩

/-- ⚠ **但 `depXY` 为假**（`h` 是常值 `false`）。 -/
theorem flatM_not_depXY : ¬ depXY flatM := by
  rintro ⟨u, hu⟩
  exact hu ⟨false, fun x => by cases x <;> rfl⟩

/-- **`flatM` 同样没有混杂**（唯一实现下 `X` 只有一个值）。 -/
theorem flatM_not_depUY : ¬ depUY flatM := by
  rintro ⟨u₁, u₂, -, hne⟩
  exact hne rfl

/-! ===========================================================================
  §4 **无混杂的等价刻画**：`¬depUY ⟺ Y 是 X 的一个函数**
  ===========================================================================

**这是「图上的 `U → Y` 边缺失」与「模型的结构性质」之间的桥**：

> **没有未观测混杂**（`¬ depUY`）**当且仅当**
> 存在 `g : X → Y` 使 **每个个体的 `Y` 都等于 `g(X)`**。

**⚠ `g` 只在可实现点上被确定**：`sg` 的像可能只覆盖 `X` 的一部分，
故 `inducedY` 在**不可实现**的 `x` 上取 `Classical.arbitrary`。
**定理因此只断言「对每个个体 `u`」**，而**不是** `∀ x : X`。
这正是「无混杂 ⟹ `Y` 是 `X` 的函数」在**有限、非满射**情形下的**精确形式**。 -/

/-- **由 `sg` 诱导的回复函数** `g : X → Y`。

对**可实现**的 `x`（`∃ u, (sg u).1 = x`），取任一实现者的 `Y` 值 ——
**`¬ depUY` 保证这个取值与实现者的选择无关**（§4.1 的 `eq_inducedY_of_noConf`）；
对**不可实现**的 `x`，取 `Classical.arbitrary`。 -/
noncomputable def inducedY [Nonempty Y] (M : SCM X Y) (x : X) : Y :=
  if h : ∃ u : M.U, (M.sg u).1 = x then (M.sg (Classical.choose h)).2 x
  else Classical.arbitrary Y

/-- **`inducedY` 是良定义的**：无混杂时，`Y` 值只由 `X` 值决定。

**证明**：取 `u`，令 `h : ∃ u', (sg u').1 = (sg u).1`（取 `u` 自身）。
`Classical.choose h` 是某个与 `u` 同 `X` 值的个体。若无混杂，
则 `u` 与 `choose h` 的 `Y` 值**必须相同** —— 于是 `inducedY` 的
`dif_pos` 分支给出的正是 `u` 的 `Y` 值。 -/
theorem eq_inducedY_of_noConf [Nonempty Y] (M : SCM X Y) (h : ¬ depUY M)
    (u : M.U) : (M.sg u).2 (M.sg u).1 = inducedY M ((M.sg u).1) := by
  have hex : ∃ u' : M.U, (M.sg u').1 = (M.sg u).1 := ⟨u, rfl⟩
  have hspec : (M.sg (Classical.choose hex)).1 = (M.sg u).1 :=
    Classical.choose_spec hex
  have hc : (M.sg u).2 (M.sg u).1
      = (M.sg (Classical.choose hex)).2 (M.sg (Classical.choose hex)).1 := by
    by_contra hne
    exact h ⟨Classical.choose hex, u, hspec, fun hc2 => hne hc2.symm⟩
  rw [hc, inducedY, dif_pos ⟨Classical.choose hex, hspec⟩, hspec]

/-- **主等价定理（`¬depUY ⟺ 确定性）**：
「图上没有 `U → Y` 边」等价于「`Y` 是 `X` 的一个函数」。

**为什么这算还债**：`BackdoorGenuine` 的 `moralAdj` 把 `Ux → Y` 边**直接手写**在
定义里，于是「这个模型到底有没有未观测混杂」**不由 `sg` 决定**。
本定理说明：**只看 `sg` 就能判定**，且判定结果**恰好是**图侧的「`U → Y` 边缺失」。 -/
theorem noConf_iff_det [Nonempty Y] (M : SCM X Y) :
    ¬ depUY M ↔ ∃ g : X → Y, ∀ u : M.U, (M.sg u).2 (M.sg u).1 = g ((M.sg u).1) := by
  constructor
  · intro hne
    exact ⟨inducedY M, eq_inducedY_of_noConf M hne⟩
  · rintro ⟨g, hg⟩ ⟨u₁, u₂, hx, hne⟩
    rw [hg u₁, hg u₂, hx] at hne
    exact hne rfl

/-! ===========================================================================
  §5 **图 ⟹ 概率**：无混杂 ⟹ 观测律的支撑收缩到 `g` 的图像
  ===========================================================================

**这是 `BackdoorGenuine` 里 D-BD-2 所缺的**一条真连接**（「图侧与数值层脱钩」）：
本节的定理**从图上的一条性质**（`¬ depUY`）**推出观测律的一条定量性质**
（`P(X=x, Y=y) = 0` 对所有 `y ≠ g x`）。

**⚠ 注意**：`L1_obs_eq_zero_of_noConf` **不需要** positivity / 归一化 ——
因为 `push` 的每一项是 `pU u * (if ... then 1 else 0)`，
在 `y ≠ g x` 时那个指示函数**恒为 0**，故整项为 0，**与 `pU` 的符号无关**。
这是本文件**最强的定理**（前提最少、结论最实）。 -/

/-- **无混杂 ⟹ 观测律支撑收缩**：
若 `¬ depUY`，则 `P(X=x, Y=y) = 0` 对**所有** `y ≠ g(x)`。

**读法**：观测分布**住在 `g` 的图像上** —— 即「看到 `X=x` 就能确定 `Y=y`」。
这正是「没有未观测混杂」在**概率层**的样子（`Y` 的随机性**全部**经 `X` 传递，
没有独立于 `X` 的残余来源）。 -/
theorem L1_obs_eq_zero_of_noConf [Nonempty Y] (M : SCM X Y)
    (h : ¬ depUY M) {x : X} {y : Y} (hxy : y ≠ inducedY M x) :
    M.L1_obs (x, y) = 0 := by
  rw [SCM.L1_obs, push]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases h' : ((M.sg u).1, (M.sg u).2 (M.sg u).1) = (x, y)
  · exfalso
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    have h3 := eq_inducedY_of_noConf M h u
    have h4 : (M.sg u).2 (M.sg u).1 = inducedY M x := by
      rw [h1] at h3; rw [h1]; exact h3
    exact hxy (by rw [← h2]; exact h4)
  · rw [if_neg h']; ring

/-- **推论（`g` 的图像外无质量）**：对**任一**回复函数 `g` 若每个个体的
`Y = g(X)` 成立，则观测律在 `g` 的图像外为 0。

**⚠ 与上一条的区别**：这条**直接以 `g` 为前提**（不经过 `¬ depUY`），
故不需要 `Nonempty Y`（`g` 由调用者给出）。 -/
theorem L1_obs_eq_zero_of_det (M : SCM X Y) (g : X → Y)
    (hg : ∀ u : M.U, (M.sg u).2 (M.sg u).1 = g ((M.sg u).1))
    {x : X} {y : Y} (hxy : y ≠ g x) : M.L1_obs (x, y) = 0 := by
  rw [SCM.L1_obs, push]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases h' : ((M.sg u).1, (M.sg u).2 (M.sg u).1) = (x, y)
  · exfalso
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact hxy (by rw [← h2, hg u, h1])
  · rw [if_neg h']; ring

/-! ### §5.1 **无 `X → Y` 依赖 ⟹ 干预律与 `x` 无关**

这是 §2.2 的 `depXY` 在**概率层**的对偶：**图上没有 `X → Y` 边**（对**所有**个体
`h` 都是常值）⟹ **`do(x)` 分布不随 `x` 变**。

**⚠ 这里的「没有 `X → Y` 边」必须理解为「**所有**个体的 `h` 都是常值」** ——
比 `¬ depXY`（「**存在**某个个体的 `h` 非常值」的否定）**更强**，见 §5.2 的说明。
故本定理用显式前提 `hconst` 陈述，**不**用 `¬ depXY`。 -/

/-- **无因果效应 ⟹ 干预律常数**：若每个个体的 `Y` 都与 `X` 的取值无关，
则 `do(x₁)` 与 `do(x₂)` 给出**同一个** `Y` 律。 -/
theorem L2_do_const_of_noDepXY (M : SCM X Y)
    (hconst : ∀ u : M.U, ∃ y₀ : Y, ∀ x : X, (M.sg u).2 x = y₀)
    (x₁ x₂ : X) : M.L2_do x₁ = M.L2_do x₂ := by
  funext y
  rw [SCM.L2_do, SCM.L2_do, push, push]
  refine Finset.sum_congr rfl fun u _ => ?_
  obtain ⟨y₀, hy⟩ := hconst u
  rw [hy x₁, hy x₂]

/-! ### §5.2 ⚠ **`¬depXY` 与 `hconst` 不是一回事**

`depXY M := ∃ u, ¬ ∃ y₀, ∀ x, (sg u).2 x = y₀`，故 `¬ depXY M`
= **所有**个体的 `h` **都是**常值 —— 其实**恰是** `hconst`！
下面把这条**显式化**，因为很容易把 `¬depXY` 误读成「**存在**个体其 `h` 是常值」。 -/

/-- **`¬ depXY` 就是「所有个体的 `h` 都是常值」**。 -/
theorem not_depXY_iff (M : SCM X Y) :
    ¬ depXY M ↔ ∀ u : M.U, ∃ y₀ : Y, ∀ x : X, (M.sg u).2 x = y₀ := by
  constructor
  · intro h u
    by_contra hu
    exact h ⟨u, hu⟩
  · rintro h ⟨u, hu⟩
    exact hu (h u)

/-- **推论**：图上**没有** `X → Y` 边 ⟹ `do` 与 `x` 无关。 -/
theorem L2_do_const_of_not_depXY (M : SCM X Y) (h : ¬ depXY M) (x₁ x₂ : X) :
    M.L2_do x₁ = M.L2_do x₂ :=
  L2_do_const_of_noDepXY M ((not_depXY_iff M).mp h) x₁ x₂

/-! ===========================================================================
  §6 **具体实例：三个 SCM，图判定逐条机检**
  =========================================================================== -/

/-- **混杂实例**：`U = X × Y₀`、`X = u.1`、`Y = u.2`（**`Y` 完全不看 `X`**）。

于是 **同一个 `X` 值可以配不同 `Y` 值** ⟹ `depUY` **真**（有未观测混杂），
而 `depXY` **假**（`h` 是常值）。**这是「混杂」的最简形式**：
`X` 与 `Y` 由两个独立外生分量决定（`U → X`、`U → Y` 两条边，**无** `X → Y` 边）。 -/
noncomputable def confM : SCM Bool Bool where
  U := Bool × Bool
  pU := fun _ => 1 / 4
  sg := fun u => (u.1, fun _ => u.2)

/-- **`confM` 有未观测混杂**（同 `X` 的两个个体 `Y` 不同）。 -/
theorem confM_depUY : depUY confM :=
  ⟨(false, false), (false, true), rfl, by simp [confM]⟩

/-- **`confM` 的 `h` 全是常值**（`Y` 不看 `X`）。 -/
theorem confM_not_depXY : ¬ depXY confM := by
  rw [not_depXY_iff]
  intro u
  exact ⟨u.2, fun _ => rfl⟩

/-- **`confM`：`do` 不随 `x` 变**（因为 `Y` 不看 `X`）—— §5.2 推论的应用。 -/
theorem confM_L2_do_const (x₁ x₂ : Bool) :
    confM.L2_do x₁ = confM.L2_do x₂ :=
  L2_do_const_of_not_depXY confM confM_not_depXY x₁ x₂

/-- **`confM` 没有确定性回复函数**：**不存在** `g` 使每个个体的
`Y = g(X)`。

**这是 `depUY` 非空洞的**最强机检证据**：`confM_depUY` 说「`depUY` 成立」，
本定理说「`noConf_iff_det` 的右端**不成立**」—— 二者由 §4 的主等价定理**必然**
相容，但**分别**由 `simp`/`Bool.noConfusion` **独立**验算，不是循环论证。

**也是「混杂」在结构层的指纹**：两个个体 `(false,false)` 与 `(false,true)`
有**相同的 `X = false`** 但**不同的 `Y`**，故任何 `g : Bool → Bool` 都无法同时
拟合两者。 -/
theorem confM_no_det_response :
    ¬ ∃ g : Bool → Bool, ∀ u : confM.U,
      (confM.sg u).2 (confM.sg u).1 = g ((confM.sg u).1) := by
  rintro ⟨g, hg⟩
  have h1 := hg (false, false)
  have h2 := hg (false, true)
  simp [confM] at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- **`confM` 的概率指纹：同一 `X` 下两个 `Y` 都有质量**。

`P(X=false, Y=false) = 1/4` **且** `P(X=false, Y=true) = 1/4` ——
**同一个 `X = false` 下 `Y` 取了两个不同的值**。这正是「未观测混杂」在观测律上的
可检验征兆（与 `pureM_obs_off_image` 的「图像外为 0」形成对照）。 -/
theorem confM_obs_both : confM.L1_obs (false, false) = 1 / 4 ∧
    confM.L1_obs (false, true) = 1 / 4 := by
  have key : ∀ yy : Bool, confM.L1_obs (false, yy) = 1 / 4 := by
    intro yy
    rw [SCM.L1_obs, FateV2.Modeling.PearlHierarchy.push]
    dsimp only [confM]
    rw [Finset.sum_eq_single (false, yy)]
    · norm_num
    · intro b _ hb
      simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact ⟨key false, key true⟩

/-- **纯因果实例（无混杂）**：`X = u`、`Y = h(X) = X`，`U` 只经 `X` 影响 `Y`。

`U = Bool`、`sg u = (u, fun x => x)` ⟹ `depUY` **假**（同一个 `X` 值下 `Y` 唯一）。 -/
noncomputable def pureM : SCM Bool Bool where
  U := Bool
  pU := fun _ => 1 / 2
  sg := fun u => (u, fun x => x)

/-- **`pureM` 无混杂**。 -/
theorem pureM_not_depUY : ¬ depUY pureM := by
  rintro ⟨u₁, u₂, hx, hne⟩
  simp [pureM] at hx hne
  exact hne hx

/-- **`pureM` 的 `Y` 真的依赖 `X`**（`h = id` 非常值）。 -/
theorem pureM_depXY : depXY pureM := by
  refine ⟨false, ?_⟩
  rintro ⟨y₀, hy⟩
  have h1 := hy false
  have h2 := hy true
  simp [pureM] at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- **`pureM` 的 `X` 依赖 `U`**（`X = u`，两个个体给出不同的 `X`）。 -/
theorem pureM_depUX : depUX pureM := by
  haveI : Nonempty pureM.U := ⟨false⟩
  rw [depUX_iff_exists_ne]
  exact ⟨false, true, by simp [pureM]⟩

/-- **`pureM` 的回复函数是 `id`**（`noConf_iff_det` 的实际见证）。 -/
theorem pureM_exists_g : ∃ g : Bool → Bool, ∀ u : pureM.U,
    (pureM.sg u).2 (pureM.sg u).1 = g ((pureM.sg u).1) :=
  (noConf_iff_det pureM).mp pureM_not_depUY

/-- **`pureM` 的观测律只在图像上**：`P(x, y) = 0` 对 `y ≠ x`。 -/
theorem pureM_obs_off_image {x y : Bool} (hxy : y ≠ x) : pureM.L1_obs (x, y) = 0 :=
  L1_obs_eq_zero_of_det pureM id (fun _ => rfl) hxy


/-- **`pureM` 的图像上**确有质量（`P(true,true) = 1/2`）——
证明 `pureM_obs_off_image` **不是**「全零律」的空洞性质。 -/
theorem pureM_obs_on_image : pureM.L1_obs (true, true) = 1 / 2 := by
  rw [SCM.L1_obs, FateV2.Modeling.PearlHierarchy.push]
  dsimp only [pureM]
  rw [Finset.sum_eq_single true]
  · norm_num
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`constM`：`X` 不依赖 `U`**（`U` 只有一个值，`X` 恒为 `true`）。 -/
noncomputable def constM : SCM Bool Bool where
  U := Unit
  pU := fun _ => 1
  sg := fun _ => (true, fun x => x)

/-- **`constM` 里 `X` 不依赖 `U`**（`u ↦ (sg u).1` 是常值 `true`）。 -/
theorem constM_not_depUX : ¬ depUX constM :=
  fun h => h ⟨true, fun _ => rfl⟩

/-- **`constM` 里 `Y` 仍依赖 `X`**（`h = id`）。 -/
theorem constM_depXY : depXY constM := by
  refine ⟨(), ?_⟩
  rintro ⟨y₀, hy⟩
  have h1 := hy false
  have h2 := hy true
  simp [constM] at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ### §6.1 **`SCMGraph` 在各实例上的形状**（图侧机检） -/

/-- **`confM` 的图里 `U → X` 边存在**。 -/
theorem confM_edge_ux : edge confM (.u (false, false)) (.x false) := rfl

/-- **`confM` 的图里 `U → Y` 边存在**（`Y = u.2` 直接来自外生）。 -/
theorem confM_edge_uy : edge confM (.u (false, true)) (.y true) := rfl

/-- **`pureM` 的图里 `X → Y` 边存在**（`Y = X`）。 -/
theorem pureM_edge_xy : edge pureM (.x true) (.y true) := ⟨true, rfl, rfl⟩

/-- **`pureM` 的图里 `Y` 无出边**（§3.2.1 一般定理的实例）。 -/
theorem pureM_no_out_of_y (v : Bool) (b : SV pureM) : ¬ edge pureM (.y v) b :=
  edge_from_y_false pureM v b

/-- **每个实例的图都是 DAG**（`SCMGraph` 的构造不依赖 `acyclic` 假设）。 -/
example (M : SCM X Y) (v : SV M) : ¬ (SCMGraph M).isAncestor v v :=
  (SCMGraph M).isAncestor_irrefl v

/-! ===========================================================================
  §7 ⚠ **与 `FateV2.Modeling.R277`（`BackdoorGenuine`）的接口：**已做什么、**没做什么**
  ===========================================================================

## §7.1 已做

`BackdoorGenuine` 的 `FateV2.Modeling.R277.moralAdj`（第 458 行附近）**手写**了六组边，
本文件**在 `FateV2.Modeling.PearlHierarchy.SCM` 上机械地重建了它们**：

| `R277.moralAdj` 的分支 | 本文件对应 |
|---|---|
| `Z → X`（`fX z ux = x`） | `edge (.u u) (.x v)`（`sg` 的 `fX` 位置是 `(sg u).1`） |
| `Ux → X` | 同上（`Ux` 在 `PearlHierarchy` 里**并入** `sg` 的第一分量） |
| `X → Y`、`Z → Y`、`Ux → Y`、`Uy → Y`（`fY x z ux uy = y`） | `edge (.x s) (.y v)` 与 `edge (.u u) (.y v)` |
| `moralEdgeY`（父亲的道德边） | **本文件不做**（`SCMGraph` 是**有向**图；道德化见 §7.2） |

**⚠ 这不是「已证等价」**：`R277.moralAdj` 的载体是
`R259.BackdoorSetup`（五个独立 `Type` 字段 + `fX`/`fY` 两槽），
本文件的载体是 `FateV2.Modeling.PearlHierarchy.SCM`（单个 `sg`）。
**两者之间的忠实翻译函子未写** —— 这是**明确的缺口**（§7.2 第 1 条）。

## §7.2 ⚠ 缺口（**逐条登记，不掩饰**）

| # | 缺口 | 需要什么 |
|---|---|---|
| **1** | `R259.BackdoorSetup → FateV2.Modeling.PearlHierarchy.SCM` 的翻译（把 `fX`,`fY` 揉成 `sg`）**未写** | 需要一个把 `fY` 的 `Uy` 槽吸收进 `U := Ux × Uy` 的编码 |
| **2** | **道德化**（`SCMGraph` → 无向邻接）**未写** | 祖先图 + 父亲两两相连；可直接接 `FateV2.Modeling.MoralGraphMarkov.USeparated` |
| **3** | **`dSep` 判定**（`BackdoorGenuine` 头表的「§5」）**未在本文件** | 依赖 §7.2 第 2 条的道德化 |
| **4** | `depUY` 的**否定方向**（有混杂 ⟹ 观测律真的混杂）**未证** | 需要 `∃ u, pU u ≠ 0`（本文件**不作此假设**） |
| **5** | `edge` 与 `depXY` **不等价**（§3.3 反例） | 这是 `edge` 口径的**固有性质**，不是缺陷；若需「依赖图」，须用 `depXY`/`depUY` 建第二张图 |

**本文件**只**交付 `BackdoorGenuine` 头表里 **`§4 SCMGraph` 这一格**：
**「从 SCM 造图」**。它**不**声称完成 §5/§6（`dSep` 判定 + 对齐定理）。
-/

end FateV2.Modeling.SCMGraph
