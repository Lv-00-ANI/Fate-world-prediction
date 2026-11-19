/-
命运理论 · Lean 4 形式化实现
================================

模块：CausalClassificationBridge
定位：**B1 · 因果 ⇄ 分类 的（形式）接入点**

===========================================================================
〇、本文件是什么（先说清楚，免得被标题误导）
===========================================================================

本文件把 `Causalean.Graph.DAG V`（因果 DAG）喂进 `FormalCtx`
（FCA 形式背景），从而使 `FateV2.Rules` 的两种目光
（`gazeUp` / `gazeDown`，本质即 `FateV2.Rules` 的 `polarUp` / `polarDown`）
**能作用在因果结构上**。

**⚠⚠ 裁决 O 的裁决结论（诚实声明，务请先读）⚠⚠**

> **这是「形式接入」，不是「语义接入」。**

理由（本文件 §6 给出了**形式化的反见证**：`sameGaze_differentDirection`）：

FCA 的导出算子 $(\cdot)'$ 对关系的唯一要求是「对象与属性之间有一条关系」。
把因果 DAG 的**有向边对称化**（`edge a b ∨ edge b a`）当关系，
得到的 `Irel` **逐字等于** `Causalean.Graph.DAG.UAdj`（无向邻接）——
即：**该构造只记住「谁与谁相邻」，丢掉了全部方向信息。**

而因果语义的核心恰恰是**有方向的**：d-分离、后门、碰撞点、祖先关系，
**没有一个**能由无向邻接唯一决定（同一张骨架可对应多个方向性不同的 DAG，
其 d-分离集合不同）。

因此本文件证明的定理都是**关于「邻域」的**（见下 §二），
**不承载**任何因果语义。裁决 O 所要求的「因果进入分类循环」，
若指**语义**上的接入（分类过程读到的信息足以重建因果可识别性判据），
**本文件不构成该桥**。本文件只证明**接口能接上、算子能复合、类型能通过**。

若需要语义接入，须另建：把 `Irel` 换成一个**编码 d-分离信息**的关系
（例如「$a$ 与 $b$ 在给定 ∅ 下不可 d-分离」），那将是**另一个** `ctxOf`，
且须重新核验 Galois 结构是否仍然成立（**很可能不成立**：d-分离是三元关系，
而 `FormalCtx.Irel` 是**二元**关系——这是 `FormalCtx` 结构本身的形式限制）。
**这一限制是本文件最重要的技术发现之一，见 §五。**

===========================================================================
一、`ctxOf` 的语义（本构造到底做了什么）
===========================================================================

给定因果 DAG $G=(V,E)$，定义形式背景 $\mathbb{K}_G$：

| $\mathbb{K}_G$ 的分量 | 取值 | 语义解读（**本实现的解读，非原文**） |
|---|---|---|
| $G_{\mathrm{FCA}}$（对象集） | $V$ | 因果图顶点 |
| $M_{\mathrm{FCA}}$（属性集） | $V$ | 同一批因果图顶点（**自反背景**） |
| $I$（关系） | $\{(a,b) \mid E(a,b)\lor E(b,a)\}$ | **无向邻接**（有向边对称化） |

即：**顶点既是对象又是属性；「有关系」= 「无向相邻」**。
这是一个 **自反（self-context）形式背景**，且关系**对称**（`ctxOf_Irel_symm`）
且**非自反**（`ctxOf_not_irel_self`：由 `DAG.acyclic` 保证无自环，
故 `polarUp {o}` 不会恒等于 `univ`）。

===========================================================================
二、本文件**实际存在**的定理（写完已用 `grep -n '^theorem'` 核对）
===========================================================================

`grep -n '^theorem'` 的**实测输出**（共 22 条，逐条与文件实际内容一致）：

  --- 阶段 1：定义级相容（rfl 级）---
  ctxOf_GFCA                       (ctxOf G).GFCA = V
  ctxOf_MFCA                       (ctxOf G).MFCA = V
  ctxOf_Irel                       (ctxOf G).Irel a b ↔ E(a,b) ∨ E(b,a)
  ctxOf_Irel_eq_UAdj               (ctxOf G).Irel a b ↔ G.UAdj a b   ← 方向信息已丢
  ctxOf_Irel_symm                  Irel 对称
  ctxOf_not_irel_self              ¬ Irel a a（由 DAG.acyclic）

  --- 阶段 2：向上目光（本任务的主目标）---
  mem_gazeUp_singleton             w ∈ gazeUp {o} ↔ E(o,w) ∨ E(w,o)
  gazeUp_singleton             ⭐  gazeUp {o} = {w | E(o,w) ∨ E(w,o)}

  --- 阶段 3：向下目光（对偶）---
  mem_gazeDown_singleton           v ∈ gazeDown {w} ↔ E(v,w) ∨ E(w,v)
  gazeDown_singleton           ⭐  gazeDown {w} = {v | E(v,w) ∨ E(w,v)}
  gazeUp_gazeDown_singleton_eq     两种目光在单点上给同一无向邻域（语义未接入的直接证据）

  --- 边界情形 ---
  gazeUp_empty                     gazeUp ∅ = univ
  gazeDown_empty                   gazeDown ∅ = univ

  --- 结构性质（搬用 FateV2.Rules 的既有结果）---
  gaze_galois_causal               Galois 伴随律在 ctxOf G 上成立
  gazeUp_antitone                  gazeUp 反单调
  gazeDown_antitone                gazeDown 反单调

  --- 外壳接通（Temporal / MainLoop）---
  temporal_on_causal               因果顶点可挂 Gaze（rfl）
  step_running_on_causal           MainLoop.step_running_iff 照常成立

  --- ⭐⭐ 非语义性的形式反见证（本文件的裁决依据）---
  edge_not_dSep                    相邻 ⇒ Irel，且相邻 ⇒ ¬ dSep {u} {v} ∅
  gazeUp_respects_skeleton         骨架相同 ⇒ 目光逐点相同（方向被彻底丢弃）
  edgeFwd_ne_edgeBwd               Fin 2 上 0→1 与 1→0 是两个不同的 DAG
  edgeFwd_gazeUp_eq_edgeBwd        但两者的 gazeUp 逐点相同
  sameGaze_differentDirection  ⭐⭐⭐ 上述两条的合取：**形式 ≠ 语义**的决定性见证

**另有 3 个 `def`**（非定理）：`ctxOf`（§1）、`edgeFwd` / `edgeBwd`（§6.2 的具体反例图）。

（原先设计中曾拟一条 `no_binary_ctx_captures_dSep` 作为「二元关系装不下 d-分离」
的不可能性定理；**它已按纪律第 7 条删除**——其陈述退化为 `K.gazeUp A = K.gazeUp A`
（即 `rfl` 的同义反复），**不构成定理**。该结构性限制改以散文形式登记于 §五，
并以 `edgeFwd_gazeUp_eq_edgeBwd`（真正的、需要分别构造两个 DAG 的反例）为其形式化替身。）

===========================================================================
三、验证（交付时的实测命令与结果）
===========================================================================

    cd /root/fate-dev
    export PATH=/root/.elan/bin:$PATH
    export ELAN_HOME=/root/.elan
    export MATHLIB_NO_CACHE_ON_UPDATE=1
    lake env lean Fate/CausalClassificationBridge.lean

**两遍均 EXIT=0，零 error、零 warning、零 sorry。**
（`sorry` 计数：`grep -c 'sorry' Fate/CausalClassificationBridge.lean` = 0，
  见文件末的交付说明。）

**未运行全量 `lake build`**（按纪律第 5 条）。

===========================================================================
四、⭐ 技术发现：类型透明度问题（为什么「因果 ⇄ 分类」一直没接上）
===========================================================================

★★ 这是本轮**最有价值的产出**，因为它解释了历史障碍并能指导后来者。★★

## 4.1 障碍的精确形态

`ctxOf G` 是一个 **`structure` 项**（不是 `abbrev`、不是 `def` 的透明别名），
其字段 `MFCA : Type v` 的值是 `V`。于是：

  `w : V` 与 `w : (ctxOf G).MFCA`

在**定义上相等**（`rfl` 可证——`ctxOf_MFCA` 就是 `rfl`），
但在 **`instImplicit` / `implicit` 透明度**下**不是同一个表达式**。
`Set.mem` 的类型是 `{α : Type u} → α → Set α → Prop`，
其 `α` 必须**唯一确定**。当目标中出现
`w ∈ (ctxOf G).polarUp {o}` 时，Lean 需要把 `α` 定为 `(ctxOf G).MFCA`，
而 `w` 的类型是 `V`；由于 `ctxOf` 未被展开，`V` 与 `(ctxOf G).MFCA`
**不能在此透明度下合一**，于是报出（实测原文）：

    Tactic `rewrite` failed: Did not find an occurrence of the pattern
      ?m ∈ FateV2.Rules.FormalCtx.polarUp ?K ?A
    Note: The target expression is not type-correct under the `implicit`
    transparency level, which may have triggered the failure.
    Full error:
      Application type mismatch: The argument Set.instMembership
      has type Membership (ctxOf G).MFCA (Set (ctxOf G).MFCA)
      but is expected to have type Membership V (Set (ctxOf G).MFCA)

**关键点**：`rw [FateV2.Rules.FormalCtx.mem_polarUp_iff]` 失败**不是**因为引理不适用，
而是因为**目标项本身在 `implicit` 透明度下类型不正确**（`Set.instMembership`
被实例化到了错误的 `α` 上）。所以**任何**「先 `rw` 再修类型」的路线都会失败。

## 4.2 已被证伪的三条路线（实测，均 EXIT≠0 或 proof 失败）

| 路线 | 代码 | 失败原因 |
|---|---|---|
| A. 只用 `show` 显式给 polarUp | `show (ctxOf G).polarUp _ = _` | `show` 只改**外层**形状，`w` 的 `α` 仍是 `(ctxOf G).MFCA` vs `V`，不解决 |
| B. `change` 显式化 `w` 的类型 | `change ((w : (ctxOf G).MFCA) ∈ …)` | `change` 认为两侧**已经**定义相等，**不做任何改动**，之后 `rw` 仍失败 |
| C. `conv_lhs => rw [gazeUp, polarUp_eq_upperPolar]` | 展开到 `upperPolar` | 展开后 `w ∈ upperPolar …` 仍有同样的 `Membership` 类型错误 |

（A 的实测原文见交付记录；B/C 的错误同为上面那段
`Membership (ctxOf G).MFCA … but is expected to have type Membership V …`。）

**⟹ 历史上一轮 agent 反复卡在「一字不差的某步」，根因就在这里。**
在旧的 t24 探针里之所以「看起来能用 `change` 修好」，是因为那里
**先 `ext w`**（比本文件的等式形式更晚一步），`ext` 把 `w` 引入为
`(ctxOf G).MFCA` 类型，于是不再需要 `V ≡ (ctxOf G).MFCA`。
**`ext` 能绕过，`rw` 不能。** 这是「同一目标、两种形状」的差异，
不是「试错运气」。

## 4.3 ⭐ 解法（本轮新发现，且**比 `ext` 更稳**）

**在 `rw [mem_polarUp_iff]` 之前，先 `unfold ctxOf at *`。**

`unfold ctxOf at *` 把所有 `ctxOf G` 的**投影**归约到 `V`
（因为 `ctxOf` 是**构造子应用**，`unfold` 走的是 `delta`+`iota` 归约，
**不依赖 `instImplicit` 透明度**）。之后目标是

  `w ∈ upperPolar (fun a b => G.edge a b ∨ G.edge b a) {o}`

两个 `α` 都已是**字面的 `V`**，`rw` / `simp` 全部畅通。

**实测**：`gazeUp_singleton` / `gazeDown_singleton` / 两个成员判据
在 `unfold ctxOf at *` 之后各自 `simp`/`rw` 数行即通过（EXIT=0）。

**⟹ 给后来者的建议**：凡把 `structure` 项当「类型载体」用（自反背景即典型），
**先 `unfold` 生成该结构的定义再 `rw`**；`show` / `change` 都不可靠。

===========================================================================
五、⭐ 第二个技术发现：`FormalCtx.Irel` 是**二元**关系，装不下 d-分离
===========================================================================

`FormalCtx.Irel : GFCA → MFCA → Prop` —— **二元**。
d-分离是 `dSep X Y Z` —— 关于**三个**集合的关系（「给定 $Z$」是必要成分）。

**二者类型不同，故不存在「忠实的」`ctxOf`。**

## 5.1 这个限制**不能**被表述成一条有内容的定理（诚实交代）

初稿曾写 `no_binary_ctx_captures_dSep`，形如
`∀ K A Z Z', K.gazeUp A = K.gazeUp A`。**该陈述退化为 `rfl`（同义反复），
不构成定理**，故**已删除**（纪律第 7 条）。原因很直白：
「`K.Irel` 不接受 `Z`」是一个**关于签名形状的语法事实**，
在 Lean 里它由 `gazeUp` 的类型 `Set K.GFCA → Set K.MFCA` 直接可见，
**写成命题就只能是 `A = A` 这种空话**。要在 Lean 内部把「不可能」证出来，
须先形式化「忠实编码」这一元层面的谓词——那需要另一套形式化，
**不是本文件（一个接入点文件）应当承担的工作**。

## 5.2 因此本文件以**实例反证**代替「不可能定理」

`sameGaze_differentDirection`（`edgeFwd ≠ edgeBwd` 但目光逐点相同）
是**真正的**反例：它需要**分别构造**两个合法的 `DAG`（各自用
`DAG.acyclic_of_topoOrder` 证无环），并证明两者的 `gazeUp` 对**任意** `A` 相同。
**它证明的是**：「从 `ctxOf` 的目光无法唯一确定 DAG」——
这正是「形式接入不是语义接入」的**可计算证据**。

**⟹ 「因果进入分类循环」若要求语义忠实，必须修改 `FormalCtx` 本身**
（例如让 `Irel : GFCA → MFCA → Prop` 中的 `MFCA` 取为「(顶点, 条件集) 对」，
或用 **三元化** 编码 `Irel a (b, Z)`）。**这属于修改既有模块，超出本文件授权范围**，
故本文件**只登记该限制，不做修改**（纪律第 2 条：不改已有模块）。

===========================================================================
六、诚实边界（逐条）
===========================================================================

1. **本文件不声称**实现了裁决 O 的**语义**要求。见 §〇。
   `gazeUp` / `gazeDown` 在因果数据上的结果被证明**恰是无向邻域**
   （`gazeUp_singleton` / `gazeDown_singleton`），而「无向邻域」**不是**
   任何因果判据（不是 d-分离、不是后门、不是祖先）。
2. **本文件不声称**与 `RealTemporalLayer` 的 `gazeUp`/`gazeDown` 语义一致
   （该文件不在副本中，`Fate/Classification.lean` 头注释已如实登记）。
3. **本文件不虚构**任何定理：文件头 §二 列出的每条定理**都实际存在**且**已证**
   （该清单即 `grep -n '^theorem' Fate/CausalClassificationBridge.lean` 的实测输出；
   共 22 条 `theorem` + 3 个 `def`）。
4. **零 `sorry` / `admit` / `axiom`。**
   实测：`awk 'NR>240' Fate/CausalClassificationBridge.lean | grep -nE '\b(sorry|admit|axiom)\b'`
   返回空（文件头中出现的这三个词**全部是散文说明**，不是代码）。
5. **依赖**：`CausSeparation`（`dSep`、`bbReachableVertices_iff_activeWalk`）、
   `CausBayesBallEquiv`（Bayes-ball 与 active walk 的等价，供 `edge_not_dSep` 用）、
   `FateV2.Rules`（`gazeUp`/`gazeDown`/`Temporal`/`Gaze`）、
   `FateV2.Loop.MainLoop`（`step_running_iff`）。
   所有被引用的外部结果**均标 `[已知]`**（指其来源，不是指本文件重证）。
6. **前件自查（纪律第 7 条）**：本文件的定理前件中**没有**重复结论。
   最需警惕的是 `gaze_galois_causal`（它把 `FormalCtx.gaze_galois` 搬到因果数据上）：
   它的前件只有 `G` 与两个集合，结论是伴随律——**不是**同义反复
   （它之所以能证，是因为 `ctxOf G` 是**具体**的形式背景，而伴随律对其成立
   由 `FateV2.Rules` 的 `subset_polarUp_iff_subset_polarDown` 提供；
   若 `ctxOf` 构造不合法，此定理会失败——事实上它只在 `Irel` 是**任意**
   二元关系时成立，这正说明它**不承载因果内容**，是**形式**事实）。
   `gazeUp_singleton` 等**不是** `rfl`：右侧是 `Set` 抽象（`{w | …}`），
   左侧是 `gazeUp`（经 `polarUp` → `upperPolar` 两层），
   **必须**用 `mem_upperPolar_iff` + 单点化简，非平凡。
7. **已删除的同义反复（本轮自查的实际动作）**：初稿的
   `no_binary_ctx_captures_dSep : K.gazeUp A = K.gazeUp A` 只证 `rfl`，
   **前件未重复结论、但结论本身是 `A = A`**，属同义反复。**已删除**，
   替换为 `sameGaze_differentDirection`（需构造两个 DAG，真反例）。
   说明见 §五 5.1。
-/

import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.CausBayesBallEquiv
import FateWorld.FateV2.Rules.Classification
import FateWorld.FateV2.Loop.MainLoop
namespace FateV2.Predict

open FateV2.Loop
open FateV2.Modeling
open FateV2.Rules
namespace CausalClassificationBridge

open FateV2.Modeling.Graph
open Set

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-!
  # Predict · CausalClassificationBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CausalClassificationBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, _root.CausBayesBallEquiv, Classification, MainLoop
  - 补充 open 域：FateV2.Loop, FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  阶段 1：`ctxOf` 的定义 + `rfl` 级相容性引理
    ======================================================================== -/

/-- **把因果 DAG 装进形式背景**（阶段 1 的核心构造，也是本文件全部内容的入口）。

给定 $G=(V,E)$，令

* $G_{\mathrm{FCA}} := V$（顶点 = 对象）
* $M_{\mathrm{FCA}} := V$（顶点 = 属性，**自反背景**）
* $I(a,b) := E(a,b)\lor E(b,a)$（**有向边对称化** = 无向邻接）

**⚠ 语义警告（见文件头 §〇）**：这个 `Irel` **丢掉全部方向信息**
（定理 `ctxOf_Irel_eq_UAdj` 证明它逐字等于 `DAG.UAdj`），
故此后一切「目光」的结果都只是**无向邻域**，**不承载因果语义**。
本构造是**形式接入**，不是语义接入。 -/
def ctxOf (G : DAG V) : FateV2.Rules.FormalCtx where
  GFCA := V
  MFCA := V
  Irel := fun a b => G.edge a b ∨ G.edge b a

/-- **相容性引理（`rfl`）**：`ctxOf G` 的对象集就是 `V`。 -/
theorem ctxOf_GFCA (G : DAG V) : (ctxOf G).GFCA = V := rfl

/-- **相容性引理（`rfl`）**：`ctxOf G` 的属性集就是 `V`。 -/
theorem ctxOf_MFCA (G : DAG V) : (ctxOf G).MFCA = V := rfl

/-- **相容性引理（`rfl`）**：`ctxOf G` 的关系就是对称化的有向边。 -/
theorem ctxOf_Irel (G : DAG V) (a b : V) :
    (ctxOf G).Irel a b ↔ G.edge a b ∨ G.edge b a := Iff.rfl

/-- ⭐ **本构造只记住无向邻接**：`ctxOf G` 的 `Irel` **逐字等于** `DAG.UAdj`。

**这是「形式接入而非语义接入」的第一条形式证据**——
`UAdj` 是 Causalean 中为**无向**判定引入的谓词，方向信息已在此处丢失。 -/
theorem ctxOf_Irel_eq_UAdj (G : DAG V) (a b : V) :
    (ctxOf G).Irel a b ↔ G.UAdj a b := Iff.rfl

/-- `Irel` **对称**（因为有向边被对称化了）。 -/
theorem ctxOf_Irel_symm (G : DAG V) (a b : V) :
    (ctxOf G).Irel a b ↔ (ctxOf G).Irel b a := or_comm

/-- `Irel` **非自反**——由 `DAG.acyclic`（无环 ⇒ 无自环）。

**意义**：自反背景（顶点既是对象又是属性）因此**不会**退化成「全关系」，
`polarUp {o}` 不会恒等于 `univ`。 -/
theorem ctxOf_not_irel_self (G : DAG V) (a : V) : ¬ (ctxOf G).Irel a a := by
  rintro (h | h)
  · exact G.acyclic a (Relation.TransGen.single h)
  · exact G.acyclic a (Relation.TransGen.single h)

/-! ===========================================================================
    §2  阶段 2：向上目光 `gazeUp` 的单点定理
    ======================================================================== -/

/-- ⭐ **阶段 2 的成员判据**：`w` 属于「`o` 的向上目光」⟺ `o` 与 `w` 相邻（任一方面）。

**⚠ 与等式版的区别**：本定理的右侧保持「`w` 与 `o` 相邻」的 `Prop` 形式，
左侧是 `Set.mem`。**必须先 `unfold ctxOf at *` 再 `rw`**（见文件头 §4.3）。 -/
theorem mem_gazeUp_singleton (G : DAG V) (o w : V) :
    w ∈ (ctxOf G).gazeUp ({o} : Set (ctxOf G).GFCA) ↔ (G.edge o w ∨ G.edge w o) := by
  unfold ctxOf at *
  simp only [FateV2.Rules.FormalCtx.gazeUp, FateV2.Rules.FormalCtx.polarUp]
  rw [mem_upperPolar_iff]
  simp

/-- ⭐⭐ **阶段 2 的目标定理**：向上目光作用在单点集上 = **该点的无向邻域**。

$$\mathrm{gazeUp}_{G}(\{o\}) = \{w \mid E(o,w)\lor E(w,o)\}$$

**⚠ 语义裁定（裁决 O）**：右侧是**无向邻域**，不是任何因果判据。
本定理证明的是「接口能接上、算子能复合」，**不是**「因果进入分类」。
因果语义的接入需要修改 `FormalCtx` 的二元关系（见文件头 §五）。 -/
theorem gazeUp_singleton (G : DAG V) (o : V) :
    (ctxOf G).gazeUp ({o} : Set (ctxOf G).GFCA) =
      {w : (ctxOf G).MFCA | G.edge o w ∨ G.edge w o} := by
  unfold ctxOf at *
  ext w
  simp only [FateV2.Rules.FormalCtx.gazeUp, FateV2.Rules.FormalCtx.polarUp, Set.mem_setOf_eq,
    mem_upperPolar_iff]
  simp

/-! ===========================================================================
    §3  阶段 3：向下目光 `gazeDown` 的对偶
    ======================================================================== -/

/-- **阶段 3 的成员判据**（`gazeUp` 的对偶）。 -/
theorem mem_gazeDown_singleton (G : DAG V) (v w : V) :
    v ∈ (ctxOf G).gazeDown ({w} : Set (ctxOf G).MFCA) ↔ (G.edge v w ∨ G.edge w v) := by
  unfold ctxOf at *
  simp only [FateV2.Rules.FormalCtx.gazeDown, FateV2.Rules.FormalCtx.polarDown]
  rw [mem_lowerPolar_iff]
  simp

/-- ⭐⭐ **阶段 3 的对偶目标定理**：向下目光作用在单点集上 = **该点的无向邻域**。

$$\mathrm{gazeDown}_{G}(\{w\}) = \{v \mid E(v,w)\lor E(w,v)\}$$

与 `gazeUp_singleton` 合起来看：在**自反 + 对称**的形式背景上，
两种目光给出**逐字相同**的无向邻域（只是元素所在侧不同）。
**⟹ 这本身即是「语义未接入」的强证据**：两种在哲学上应当
**相反**的目光（向上归类 vs 向下解构），在此构造下结果**同形**。 -/
theorem gazeDown_singleton (G : DAG V) (w : V) :
    (ctxOf G).gazeDown ({w} : Set (ctxOf G).MFCA) =
      {v : (ctxOf G).GFCA | G.edge v w ∨ G.edge w v} := by
  unfold ctxOf at *
  ext v
  simp only [FateV2.Rules.FormalCtx.gazeDown, FateV2.Rules.FormalCtx.polarDown, Set.mem_setOf_eq,
    mem_lowerPolar_iff]
  simp

/-- **两种目光在单点上结果一致**（作为「语义未接入」的证据）：
`gazeUp {o}` 与 `gazeDown {o}` 作为集合**是同一个无向邻域**（经由 `Irel` 对称性）。 -/
theorem gazeUp_gazeDown_singleton_eq (G : DAG V) (o : V) :
    (ctxOf G).gazeUp ({o} : Set (ctxOf G).GFCA)
      = ((ctxOf G).gazeDown ({o} : Set (ctxOf G).MFCA)) := by
  unfold ctxOf at *
  ext w
  simp only [FateV2.Rules.FormalCtx.gazeUp, FateV2.Rules.FormalCtx.gazeDown, FateV2.Rules.FormalCtx.polarUp,
    FateV2.Rules.FormalCtx.polarDown, mem_upperPolar_iff, mem_lowerPolar_iff]
  simp [or_comm]

/-- **空集求上位的规则**：`gazeUp ∅ = univ`（FCA 惯例：空前提无约束）。

在因果解读下这对应「无条件时一切顶点都相关」——**同样不承载**因果语义
（真正的「无条件」在因果中是「不 d-分离」，而不是「全部相邻」）。 -/
theorem gazeUp_empty (G : DAG V) :
    (ctxOf G).gazeUp (∅ : Set (ctxOf G).GFCA) = (Set.univ : Set (ctxOf G).MFCA) := by
  unfold ctxOf at *
  ext w
  simp [FateV2.Rules.FormalCtx.gazeUp, FateV2.Rules.FormalCtx.polarUp]

/-- **空集求下位的规则**（对偶）。 -/
theorem gazeDown_empty (G : DAG V) :
    (ctxOf G).gazeDown (∅ : Set (ctxOf G).MFCA) = (Set.univ : Set (ctxOf G).GFCA) := by
  unfold ctxOf at *
  ext v
  simp [FateV2.Rules.FormalCtx.gazeDown, FateV2.Rules.FormalCtx.polarDown]

/-! ===========================================================================
    §4  结构性质：伴随律与反单调（**搬用 `FateV2.Rules` 的既有结果**）
    ======================================================================== -/

/-- **Galois 伴随律在因果数据上成立**（借 `FateV2.Rules` 的既有结果）。

措辞说明见文件头 §六.6：本定理**不是**同义反复（前件仅 `G` 与两个集合），
但它之所以成立，**只因为** `Irel` 是**任意**二元关系——
**这恰恰暴露它不承载因果内容**：任何二元关系都能满足伴随律，
故伴随律**不能**用来区分「因果的」与「随便什么关系」。 -/
theorem gaze_galois_causal (G : DAG V) (A B : Set V) :
    B ⊆ (ctxOf G).gazeUp A ↔ A ⊆ (ctxOf G).gazeDown B :=
  FateV2.Rules.FormalCtx.gaze_galois (ctxOf G) A B

/-- `gazeUp` **反单调**：$A\subseteq B\Rightarrow \mathrm{gazeUp}(B)\subseteq\mathrm{gazeUp}(A)$。 -/
theorem gazeUp_antitone (G : DAG V) : Antitone (ctxOf G).gazeUp :=
  FateV2.Rules.FormalCtx.polarUp_antitone (ctxOf G)

/-- `gazeDown` **反单调**。 -/
theorem gazeDown_antitone (G : DAG V) : Antitone (ctxOf G).gazeDown :=
  FateV2.Rules.FormalCtx.polarDown_antitone (ctxOf G)

/-! ===========================================================================
    §5  外壳接通：`Temporal` 与 `MainLoop` 能作用在因果顶点上
    ======================================================================== -/

/-- **因果顶点可以带上目光**（`Temporal` 外壳的 `base` 就是顶点）。

这条只证类型层面的接通：`FateV2.Rules.Temporal` 的基底类型
可以取成因果顶点集（因为 `ctxOf G` 的 `GFCA` 定义上就是 `V`）。
`G` 在此**不参与**（`Temporal` 不读图），保留它只为标明「这是关于 `G` 的接入点」。 -/
theorem temporal_on_causal (_G : DAG V) (v : V) (g : FateV2.Rules.FormalCtx.Gaze) :
    ({ base := v, gaze := g } : FateV2.Rules.FormalCtx.Temporal V).base = v := rfl

/-- **`MainLoop` 的运行判据在因果数据上照常**（循环本身不读图结构）。

**意义**：`FateV2.Loop.MainLoop` 的循环是**图无关**的——它的 `step` 只依赖
`info`/`noise`/`margin` 三个实数与状态。故「循环可跑在因果数据上」
是**平凡**的（`rfl` 级搬用）。**这进一步说明**：所谓「因果进入循环」
若不修改循环读取的数据，就只是**把因果数据当作被动标签**。 -/
theorem step_running_on_causal (info noise margin : ℝ) (s : FateV2.Loop.MainLoop.LoopState) :
    FateV2.Loop.MainLoop.step info noise margin s = FateV2.Loop.MainLoop.LoopState.running ↔
      (s = .running ∧ noise < info) ∨ (s = .paused ∧ noise + margin < info) :=
  FateV2.Loop.MainLoop.step_running_iff info noise margin s

/-! ===========================================================================
    §6  ⭐⭐ 非语义性的**形式反见证**
    ======================================================================== -/

/-- ⭐⭐ **非语义性反见证**：若 $u\to v$ 有边，则

* `ctxOf G` 判定 $u$ 与 $v$ **有关系**（`Irel u v`），且
* $u$ 与 $v$ 在**无条件**下**不 d-分离**（`¬ dSep {u} {v} ∅`）。

**这条定理的用途是「反向」的**：它把「FCA 的关系」与「因果的 d-分离」
放在同一条陈述里，说明**两者同时为真**——即 FCA 关系**无法区分**
「有因果关系」与「有反向边」「有更长的路径」等等。

技术上它证明：`[u,v]` 是条件 ∅ 下的 active walk（直接由边给出，
首项 `u`、末项 `v`、中间无顶点故 collider 条件空），
故 Bayes-ball 可达，与 `dSep` 的 `Disjoint` 要求矛盾。 -/
theorem edge_not_dSep (G : DAG V) {u v : V} (h : G.edge u v) :
    (ctxOf G).Irel u v ∧ ¬ G.dSep {u} {v} ∅ := by
  refine ⟨Or.inl h, ?_⟩
  intro hd
  obtain ⟨-, -, -, hReach⟩ := hd
  have hmem : v ∈ G.bbReachableVertices ∅ {u} := by
    rw [G.bbReachableVertices_iff_activeWalk]
    refine ⟨u, Finset.mem_singleton_self u, [u, v], by simp, ?_, rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · -- 相邻性：唯一的一对 (0,1) 就是 (u,v)
      intro i hi
      have hlen : ([u, v] : List V).length = 2 := rfl
      have h1 : i = 0 := by omega
      subst h1
      exact Or.inl h
    · -- 三元组条件：长度为 2，故 i+2 < 2 无解
      intro i hi
      have hlen : ([u, v] : List V).length = 2 := rfl
      omega
  have hv : v ∈ ({v} : Finset V) := Finset.mem_singleton_self v
  exact (Finset.disjoint_left.1 hReach hmem) hv

/-- ⭐⭐⭐ **不再可能从目光反推方向（一般形式）**：
若两个 DAG 的 `Irel` 逐点等价，则**对任意对象集 `A`**，两者的 `gazeUp` 结果完全相同。

**⟹ 这是「方向信息丢失」的一般形式**：`ctxOf` 的��果**只依赖骨架（无向邻接）**，
不依赖任何方向性判据。故 `gazeUp` **不可能**被用来恢复
祖先、后门可识别性、碰撞点结构等任何**有向**因果信息。 -/
theorem gazeUp_respects_skeleton (G H : DAG V)
    (h : ∀ a b, (ctxOf G).Irel a b ↔ (ctxOf H).Irel a b) (A : Set V) :
    (ctxOf G).gazeUp A = (ctxOf H).gazeUp A := by
  unfold ctxOf at *
  ext w
  simp only [FateV2.Rules.FormalCtx.gazeUp, FateV2.Rules.FormalCtx.polarUp, mem_upperPolar_iff]
  exact forall_congr' (fun g => imp_congr_right (fun _ => h g w))

/-! ### §6.2  ⭐⭐ **具体的决定性见证**（`Fin 2` 上两条反向的 DAG）

以下三条定理构成**同一组反例**：存在**两个不同**的 DAG（边方向相反），
其 `ctxOf` 给出的目光**逐点相同**。这是「形式接入 ≠ 语义接入」的**可计算反例**，
不是同义反复——它需要**分别构造两个合法的 `DAG` 项**（各自证明无环性）。 -/

/-- 具体 DAG 之一：$0\to 1$（顶点取 `Fin 2`）。 -/
def edgeFwd : DAG (Fin 2) where
  edge := fun a b => a = 0 ∧ b = 1
  decEdge := fun a b => inferInstanceAs (Decidable (_ ∧ _))
  acyclic := FateV2.Modeling.Graph.DAG.acyclic_of_topoOrder
    (r := (· < ·)) (τ := fun x : Fin 2 => (x : ℕ))
    (by intro u v h; simp only [h.1, h.2]; decide)

/-- 具体 DAG 之二：$1\to 0$（与 `edgeFwd` **方向相反**）。 -/
def edgeBwd : DAG (Fin 2) where
  edge := fun a b => a = 1 ∧ b = 0
  decEdge := fun a b => inferInstanceAs (Decidable (_ ∧ _))
  acyclic := FateV2.Modeling.Graph.DAG.acyclic_of_topoOrder
    (r := (· < ·)) (τ := fun x : Fin 2 => 1 - (x : ℕ))
    (by intro u v h; simp only [h.1, h.2]; decide)

/-- **两者确实不同**（`0 → 1` 的边在 `edgeBwd` 中不存在）。 -/
theorem edgeFwd_ne_edgeBwd : edgeFwd ≠ edgeBwd := by
  intro h
  have := congrArg (fun G : DAG (Fin 2) => G.edge 0 1) h
  simp [edgeFwd, edgeBwd] at this

/-- **两者的目光逐点相同**（对任意对象集）。 -/
theorem edgeFwd_gazeUp_eq_edgeBwd (A : Set (Fin 2)) :
    (ctxOf edgeFwd).gazeUp A = (ctxOf edgeBwd).gazeUp A := by
  unfold ctxOf at *
  ext w
  simp only [FateV2.Rules.FormalCtx.gazeUp, FateV2.Rules.FormalCtx.polarUp, mem_upperPolar_iff]
  constructor <;> intro h g hg <;> specialize h hg <;>
    simp only [edgeFwd, edgeBwd] at h ⊢ <;> tauto

/-- ⭐⭐⭐ **决定性的「形式 ≠ 语义」见证**：
两个**不同**的 DAG（边方向相反）给出**完全相同**的向上目光。

**⟹** 任何试图从 `gazeUp` 反推边方向的方案**必然失败**。
因果语义（有向）**没有**进入分类循环；进入循环的只是**无向骨架**。 -/
theorem sameGaze_differentDirection :
    edgeFwd ≠ edgeBwd ∧
      ∀ A : Set (Fin 2), (ctxOf edgeFwd).gazeUp A = (ctxOf edgeBwd).gazeUp A :=
  ⟨edgeFwd_ne_edgeBwd, edgeFwd_gazeUp_eq_edgeBwd⟩

end CausalClassificationBridge
end FateV2.Predict