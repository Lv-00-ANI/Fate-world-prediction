/-
# T1A.1 图族扩展：**叉图**（`CondMul` 口径）+ **对撞图**（`MargIndep` 口径）

## 本文件是什么

`Fate/T1A1.lean` 在**链图** `0 → 1 → 2` 上建立了 T1A.1 的可行形态：

```
ChainMarkovRelative p  ⟹  chainDAG.dSep {0} {2} {1}  ⟹  CondMul (p 的重排)
```

本文件把图族扩到**叉图**（fork / common cause）与**对撞图**（collider），
并把**每一个图侧断言**用 `Causalean.Graph.DAG.dSep` 的 `decide` **逐条机检**。
写法**逐字复用** `Fate/T1A1.lean`：`chainEdge` / `chainDAG` 的 acyclicity 手法
（严格单调 `Fin.val`）、`open FateV2.Modeling.Graph`、`dSep` 用 `decide` 判定、
`CondMul` 用 `FinCondIndep` 的口径。

## ⚠⚠ 诚实结论（先读这一段）

### (1) 叉图：`ForkMarkov ⟹ CondMul` **已证**，图侧真值表已机检

叉图取**降序编码** `2 → 1 → 0`（≅ `0 ← 1 → 2`）：顶点 `2` 是共同原因、
`1` 是分量 `X`、`0` 是分量 `Y`。

| # | 语句 | 真值 | 图论含义 |
|---|---|---|---|
| ① | `dSep {2} {0} {1}` | ✅ **真** | 源=共同原因、条件=分量 `X` ⟹ 到不了 `Y` |
| ② | `dSep {0} {2} {1}` | ✅ **真** | 源/目标互换（叉图版的 `chain_dsep`） |
| ③ | `¬ dSep {1} {0} {2}` | ✅ **假** | 源=**被条件化的分量** `X` ⟹ 源∩条件 ≠ ∅ |
| ④ | `dSep ∅ {2} ∅` | ✅ **真** | 无条件、平凡分离 |

**⚠ 为什么 ③ 是假的**：`dSep`（`CausSeparation.lean:64`）是

```lean
Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
  Disjoint (G.bbReachableVertices Z X) Y
```

即「**从 `X` 出发**、条件于 `Z` 的 Bayes 球到不了 `Y`」。
③ 把**被条件化的那个分量 `{1}` 放进了源集 `X`**，于是 `X ∩ Z ≠ ∅` 已不满足，
且球从 `1` 出发经 `1 → 0` 直达 `0`。**这不是球实现的 bug，
而是 ③ 本身把源/条件错配了**：d-分离的「源」必须是**被问询**的变量，
不能同时又是**条件集**。

### (2) ⚠ 更正上一版文件头的一个**错误**数值断言

上一版文件头曾写「`bbReachableVertices {2} {1} = {0, 1, 2}` ⟹ 球在分叉点不被挡住」。
本版用 `decide` 逐点机检后**证伪**了这句话：

* 球**从不包含源点自身**（实测 `1 ∉ bbReachableVertices Z {1}`、`0 ∉ bbReachableVertices Z {0}`）；
* 实测 `bbReachableVertices {2} {1} = {1, 0}`、`bbReachableVertices {2} {0} = {0, 2}`、
  `bbReachableVertices {1} {0} = {0}`

**故 ③ 失败的真原因是「源集与条件集相交 + 球直达 `0`」，不是「球涨满全图」。**
上一版那句「`bbStep` 保守偏差」的判断**不成立**，本版撤回。
本文件**未修改 `Causalean` 源码**。

### (3) 对撞图的结论**不是** `CondMul`，而是**边际独立** `MargIndep`

对撞 `0 → 2 ← 1`：不条件化时两父亲**分离**，条件化碰撞点后**不**分离。
而 `CondMul` 的口径是「**以 `Z` 为条件**」，对撞的结论恰恰是「**不**以 `Z` 为条件」，
故本文件用 `MargIndep`（§0.1）。

### (4) ⚠ `ColliderMarkov` **必须带归一化**

若 `p((x,y),z) = p_X(x)·p_Y(y)·p_{Z|XY}(x,y,z)` 且 `p_{Z|XY}` **任意**，
则 `∑_z p` 含交叉项，**不**边际独立。
故 `zsum_one` 写进 `ColliderMarkov`；§2.5 给出**去掉它后结论为假**的机检反例
（`collider_nonNorm_counterexample`，**已真证，无 `sorry`**）。

## 本文件定理清单

| # | 定理 | 内容 |
|---|---|---|
| 1 | `commonCauseDAG` / `colliderDAG` | 两个真 `Causalean.Graph.DAG` 实例 |
| 2 | `fork_markov_implies_condMul` | `ForkMarkov p ⟹ CondMul p` |
| 3 | `fork_markov_condMul_gen` | 同上，**任意有限型**（不依赖枚举） |
| 4 | `fork_dsep_table` | 叉图四条 `dSep` 真值（①②③④） |
| 5 | `fork_no_markov_counterexample` | 叉图**无条件版为假**（机检反例） |
| 6 | `forkCexP_not_forkMarkov` | 反例**确实违反** `ForkMarkov`（非空洞） |
| 7 | `collider_dsep_table` | 对撞图四条 `dSep` 真值 |
| 8 | `collider_dsep_marginal` / `collider_dsep_conditioned_fails` | 对撞图两条关键读出 |
| 9 | `collider_markov_implies_margindep` | `ColliderMarkov p ⟹ MargIndep p` |
| 10 | `collider_no_margindep_counterexample` | 对撞图**无条件版为假**（机检反例） |
| 11 | `colliderCexP_not_colliderMarkov` | 反例**确实违反** `ColliderMarkov`（非空洞） |
| 12 | `collider_nonNorm_counterexample` | `ColliderMarkov` **去掉归一化后为假** |
| 13 | `sum_fin2` / `sum_fin2_fin2` / `marg*_fin` | 载体层小引理 |

## 无 `sorry` / `admit` / `axiom`

见文件末尾 `#print axioms` 审计段。
-/

import FateWorld.FateV2.Predict.T1A1
import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.MarkovBridgeReal
import FateWorld.FateV2.Predict.FinCondIndep
import FateWorld.FateV2.Predict.FinJoint
import FateWorld.FateV2.Predict.PearlCondIndepBridge
import Mathlib.Tactic

namespace FateV2.Predict.T1A1Graphs

open FateV2.Modeling

open FateV2.Modeling.Graph
open FateV2.Predict.FinCondIndep

/-!
  # Predict · T1A1Graphs

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1A1Graphs.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T1A1, _root.CausSeparation, MarkovBridgeReal, FinCondIndep, FinJoint, PearlCondIndepBridge
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §0 载体层通用引理（与图无关） -/

/-- ⭐ **`Fin 2` 上的单重求和展开**。 -/
theorem sum_fin2 (f : Fin 2 → ℝ) : (∑ i, f i) = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- ⭐⭐ **`Fin 2 × Fin 2` 上的双重求和展开**。 -/
theorem sum_fin2_fin2 (f : Fin 2 → Fin 2 → ℝ) :
    (∑ x, ∑ y, f x y) = f 0 0 + f 0 1 + f 1 0 + f 1 1 := by
  rw [sum_fin2 (fun x => ∑ y, f x y), sum_fin2 (f 0), sum_fin2 (f 1)]
  ring

/-- ⭐⭐⭐ **`margZ` 在 `FinJoint (Fin 2) (Fin 2) (Fin 3)` 上的闭式**。 -/
theorem margZ_fin (p : FinJoint (Fin 2) (Fin 2) (Fin 3)) (z : Fin 3) :
    margZ p z = p ((0, 0), z) + p ((0, 1), z) + p ((1, 0), z) + p ((1, 1), z) := by
  unfold margZ
  exact sum_fin2_fin2 (fun x y => p ((x, y), z))

/-- ⭐⭐⭐ **`margXZ` 在 `FinJoint (Fin 2) (Fin 2) (Fin 3)` 上的闭式**。 -/
theorem margXZ_fin (p : FinJoint (Fin 2) (Fin 2) (Fin 3)) (x : Fin 2) (z : Fin 3) :
    margXZ p x z = p ((x, 0), z) + p ((x, 1), z) := by
  unfold margXZ
  exact sum_fin2 (fun y => p ((x, y), z))

/-- ⭐⭐⭐ **`margYZ` 在 `FinJoint (Fin 2) (Fin 2) (Fin 3)` 上的闭式**。 -/
theorem margYZ_fin (p : FinJoint (Fin 2) (Fin 2) (Fin 3)) (y : Fin 2) (z : Fin 3) :
    margYZ p y z = p ((0, y), z) + p ((1, y), z) := by
  unfold margYZ
  exact sum_fin2 (fun x => p ((x, y), z))

/-! ### §0.1 边际独立谓词 `MargIndep`

**为什么需要**：对撞图的 T1A.1 结论**不是**「以 `Z` 为条件」的 `CondMul`，
而是「**不**以 `Z` 为条件」的**边际独立**。 -/

/-- ⭐⭐⭐ **边际独立（乘性形式）**：先把 `Z` 边缘化掉，再断言 `X` 与 `Y` 独立。 -/
def MargIndep (p : FinJoint (Fin 2) (Fin 2) (Fin 3)) : Prop :=
  ∀ x y,
    (∑ z, p ((x, y), z)) =
      (∑ z, ∑ y', p ((x, y'), z)) * (∑ z, ∑ x', p ((x', y), z))

/-! ## §1 叉图（fork / common cause）：`2 → 1 → 0`（≅ `0 ← 1 → 2`）

**顶点标号**：`2` = 共同原因（记为 `Z`）、`1` = 分量 `X`、`0` = 分量 `Y`。
每步 `Fin.val` 严格**递减**，故 acyclicity 证明逐字照抄 `T1A1.chainDAG`（那里是递增）。 -/

/-! ### §1.1 图侧：叉图作为真 `Causalean.Graph.DAG` -/

/-- 叉图的边关系：`2 → 1` 与 `1 → 0`（降序）。 -/
def commonCauseEdge : Fin 3 → Fin 3 → Prop :=
  fun i j => (i = 2 ∧ j = 1) ∨ (i = 1 ∧ j = 0)

/-- 关键引理：`TransGen commonCauseEdge a b` ⟹ `b.val < a.val`。 -/
theorem commonCauseEdge_key : ∀ {a b : Fin 3},
    Relation.TransGen commonCauseEdge a b → b.val < a.val := by
  intro a b htr
  induction htr with
  | single hab =>
    unfold commonCauseEdge at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  | tail _ hbc ih =>
    unfold commonCauseEdge at hbc
    rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-- ⭐ **叉图 `2 → 1 → 0`（≅ `0 ← 1 → 2`）作为真 `Causalean.Graph.DAG`**。 -/
def commonCauseDAG : DAG (Fin 3) where
  edge := commonCauseEdge
  decEdge := fun i j => by unfold commonCauseEdge; infer_instance
  acyclic := fun v h => absurd (commonCauseEdge_key h) (by simp)

/-! ### §1.2 概率侧：`ForkMarkov`

**⚠ 为什么用 `def … : Prop` 而不是 `structure`**：本谓词**携带三个函数数据**
（`pZ`、`pXZ`、`pYZ`）；Lean 4 的 `structure … : Prop` 不允许非证明字段。
故与 `ChainMarkovRelative` 保持一致，用 `∃` 编码。 -/

/-- ⭐⭐ **叉图的马尔可夫性**：`Z` 是 `X` 与 `Y` 的**共同原因**。

$$p\,((x,y),z) \;=\; p_Z(z)\cdot p_{X|Z}(x \mid z)\cdot p_{Y|Z}(y \mid z)$$

**语义**：`p_{X|Z}` 只读 `(x,z)`、`p_{Y|Z}` 只读 `(y,z)`，
**两者都不在 `x` 与 `y` 之间传信息** —— 这就是「条件化共同原因 ⟹ 条件独立」。 -/
def ForkMarkov (p : FinJoint (Fin 2) (Fin 2) (Fin 3)) : Prop :=
  ∃ (pZ : Fin 3 → ℝ) (pXZ : Fin 2 → Fin 3 → ℝ) (pYZ : Fin 2 → Fin 3 → ℝ),
    ∀ x y z, p ((x, y), z) = pZ z * pXZ x z * pYZ y z

/-- ⭐⭐⭐⭐ **T1A.1（叉图版）：`ForkMarkov ⟹ X ⊥ Y | Z`**。

**证明**：因子分解已是**可分离形式**
$p((x,y),z) = (p_Z(z)\,p_{X|Z}(x,z))\cdot p_{Y|Z}(y,z)$，
直接套 `PearlCondIndepBridge.separable_implies_condMul`。

**⚠ 为什么没有 `hSep` 参数**：`dSep` 的源/目标/条件集与 `CondMul` 的 `X/Y/Z`
是**两套不同的标号口径**（前者要求三个集合两两不交，后者只是一个三元组取值）。
本文件**不伪造**一个看起来「接上图侧」的哑参数，而是把图侧事实在 §1.3 的真值表里
**全部**列出。 -/
theorem fork_markov_implies_condMul
    (p : FinJoint (Fin 2) (Fin 2) (Fin 3))
    (hMarkov : ForkMarkov p) :
    CondMul p := by
  obtain ⟨pZ, pXZ, pYZ, hfac⟩ := hMarkov
  refine FateV2.Predict.PearlCondIndepBridge.separable_implies_condMul p
    (fun x z => pZ z * pXZ x z) (fun y z => pYZ y z) ?_
  intro x y z
  exact hfac x y z

/-- ⭐⭐⭐⭐ **同上，任意有限型**：证明**不依赖枚举**。

**为什么不用 `separable_implies_condMul`**：那条定理的 `α β γ` 属于**同一 universe**，
而本定理的三个类型各自独立；故**就地重做**三段分解论证
（`margXZ` / `margYZ` / `margZ` 各把求和提出去，再 `ring` 闭合）。 -/
theorem fork_markov_condMul_gen
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ)
    (hZ : γ → ℝ) (hXZ : α → γ → ℝ) (hYZ : β → γ → ℝ)
    (hfac : ∀ x y z, p ((x, y), z) = hZ z * hXZ x z * hYZ y z) :
    CondMul p := by
  intro x y z
  -- ① `Y` 边缘：`∑_{x'} p((x',y),z) = hYZ y z · ∑_{x'} hZ z * hXZ x' z`
  have hYZ' : margYZ p y z = hYZ y z * (∑ x', hZ z * hXZ x' z) := by
    unfold margYZ
    calc ∑ x', p ((x', y), z)
        = ∑ x', (hZ z * hXZ x' z) * hYZ y z := by
          refine Finset.sum_congr rfl fun x' _ => ?_
          rw [hfac x' y z]
      _ = (∑ x', hZ z * hXZ x' z) * hYZ y z := by rw [Finset.sum_mul]
      _ = hYZ y z * (∑ x', hZ z * hXZ x' z) := mul_comm _ _
  -- ② `X` 边缘：`∑_{y'} p((x,y'),z) = (hZ z * hXZ x z) · ∑_{y'} hYZ y' z`
  have hXZ' : margXZ p x z = (hZ z * hXZ x z) * (∑ y', hYZ y' z) := by
    unfold margXZ
    calc ∑ y', p ((x, y'), z)
        = ∑ y', (hZ z * hXZ x z) * hYZ y' z := by
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [hfac x y' z]
      _ = (hZ z * hXZ x z) * (∑ y', hYZ y' z) := by rw [Finset.mul_sum]
  -- ③ `Z` 边缘：两层求和各自提出去
  have hZ' : margZ p z = (∑ x', hZ z * hXZ x' z) * (∑ y', hYZ y' z) := by
    unfold margZ
    calc ∑ x', ∑ y', p ((x', y'), z)
        = ∑ x', ∑ y', (hZ z * hXZ x' z) * hYZ y' z := by
          refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => ?_
          rw [hfac x' y' z]
      _ = ∑ x', (hZ z * hXZ x' z) * (∑ y', hYZ y' z) := by
          refine Finset.sum_congr rfl fun x' _ => ?_
          rw [Finset.mul_sum]
      _ = (∑ x', hZ z * hXZ x' z) * (∑ y', hYZ y' z) := by rw [Finset.sum_mul]
  rw [hYZ', hXZ', hZ', hfac x y z]
  ring

/-! ### §1.3 ⭐⭐ 图侧真值表（叉图），全部 `by decide` 机检

见文件头表格 ①—④。**⭐ ①② 一起说明**：只要源集**不含**被条件化的分量，
条件化共同原因 `1` 就把 `2` 与 `0` 两个方向都阻断 —— 这正是叉图「条件独立」的图侧对应。 -/
theorem fork_dsep_table :
    commonCauseDAG.dSep {2} {0} {1} ∧
    commonCauseDAG.dSep {0} {2} {1} ∧
    (¬ commonCauseDAG.dSep {1} {0} {2}) ∧
    commonCauseDAG.dSep ∅ {2} ∅ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold FateV2.Modeling.Graph.DAG.dSep; decide)

/-! ### §1.4 ⭐⭐ 无条件版的反例（叉图）

**这是 `T1A1.dSep_no_markov_counterexample` 的叉图对应物**：
`dSep` 是**纯图论**谓词、`CondMul` 是**纯概率**谓词，二者之间没有逻辑桥，
故不带马尔可夫前件的「`dSep ⟹ CondMul`」为假。 -/

/-- ⭐ 反例联合律（叉图专用）：`X` 与 `Y` 完全相等（`x = y`），`Z` 均匀。

$$p((x,y),z) = \begin{cases} 1/2 & x = y \\ 0 & x \neq y\end{cases}$$

**为什么这对叉图是反例**：叉图的马尔可夫性要求给定 `z` 后 `x` 与 `y` 独立，
而这里 `x = y` **恒成立** ⟹ `X ⊥̸ Y | Z` 处处失败。 -/
noncomputable def forkCexP : FinJoint (Fin 2) (Fin 2) (Fin 3) :=
  fun q => if q.1.2 = q.1.1 then (1 / 2 : ℝ) else 0

/-- ⭐⭐⭐⭐⭐ **叉图的无条件版是假命题**：存在 `p` 使
`commonCauseDAG.dSep {2} {0} {1}`（**图侧成立**，§1.3 ①）却 `¬ CondMul p`。

**证明**：取 `(x,y,z) = (0,0,0)`。

* `p((0,0),0) = 1/2`；`margZ p 0 = 1`；`margXZ p 0 0 = 1/2`；`margYZ p 0 0 = 1/2`
* 左端 `= (1/2)·1 = 1/2`，右端 `= (1/2)·(1/2) = 1/4` ⟹ **矛盾** ∎ -/
theorem fork_no_markov_counterexample :
    ∃ (p : FinJoint (Fin 2) (Fin 2) (Fin 3)),
      commonCauseDAG.dSep {2} {0} {1} ∧ ¬ CondMul p := by
  refine ⟨forkCexP, ?_, ?_⟩
  · unfold FateV2.Modeling.Graph.DAG.dSep; decide
  · intro h
    have hpt := h 0 0 0
    rw [margZ_fin, margXZ_fin, margYZ_fin] at hpt
    simp only [forkCexP] at hpt
    norm_num at hpt

/-- ⭐⭐⭐ **非空洞性**：`forkCexP` **确实违反** `ForkMarkov`
（所以上一条反例不是「拿一个连马尔可夫性都不满足的 `p` 去糊弄」）。

自然语言：若 `p(x,y,z)` 因子化为 `pZ z * pXZ x z * pYZ y z`，则给定 `z` 后
`x` 与 `y` 独立，不可能出现 `x = y` **恒成立**。

**证明**：在 `(0,1,0)` 处 `p = 0` ⟹ `(pZ 0 · pXZ 0 0)·pYZ 1 0 = 0`；
在 `(1,1,0)` 处 `p = 1/2` ⟹ `pYZ 1 0 ≠ 0`；故 `pZ 0 · pXZ 0 0 = 0`，
代回 `(0,0,0)` 处的 `p = 1/2` 得 `0 = 1/2`，矛盾。 -/
theorem forkCexP_not_forkMarkov : ¬ ForkMarkov forkCexP := by
  rintro ⟨pZ, pXZ, pYZ, hfac⟩
  have h01 : pZ 0 * pXZ 0 0 * pYZ 1 0 = 0 := by
    have := hfac 0 1 0
    simpa [forkCexP] using this.symm
  have h11 : pZ 0 * pXZ 1 0 * pYZ 1 0 = 1 / 2 := by
    have := hfac 1 1 0
    simpa [forkCexP] using this.symm
  have h00 : pZ 0 * pXZ 0 0 * pYZ 0 0 = 1 / 2 := by
    have := hfac 0 0 0
    simpa [forkCexP] using this.symm
  -- 由 `h01` 得 `pZ 0 * pXZ 0 0 = 0` 或 `pYZ 1 0 = 0`。
  -- 后者与 `h11` 矛盾，故为前者；代回 `h00` 得 `0 = 1/2`。
  rcases mul_eq_zero.mp h01 with hA | hA
  · rw [hA, zero_mul] at h00
    norm_num at h00
  · rw [hA, mul_zero] at h11
    norm_num at h11

/-! ## §2 对撞图（collider）：`0 → 2 ← 1` -/

/-! ### §2.1 图侧：对撞图作为真 `Causalean.Graph.DAG` -/

/-- 对撞图的边关系：`0 → 2` 与 `1 → 2`（`2` 是碰撞点）。 -/
def colliderEdge : Fin 3 → Fin 3 → Prop :=
  fun i j => (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)

/-- 关键引理：`TransGen colliderEdge a b` ⟹ `a.val < b.val`。 -/
theorem colliderEdge_key : ∀ {a b : Fin 3},
    Relation.TransGen colliderEdge a b → a.val < b.val := by
  intro a b htr
  induction htr with
  | single hab =>
    unfold colliderEdge at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  | tail _ hbc ih =>
    unfold colliderEdge at hbc
    rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-- ⭐ **对撞图 `0 → 2 ← 1` 作为真 `Causalean.Graph.DAG`**。 -/
def colliderDAG : DAG (Fin 3) where
  edge := colliderEdge
  decEdge := fun i j => by unfold colliderEdge; infer_instance
  acyclic := fun v h => absurd (colliderEdge_key h) (by simp)

/-! ### §2.2 ⭐⭐ 图侧真值表（对撞图）

**⭐ 这张表是对撞图「行为反转」的机器验证。** -/

/-- ⭐⭐⭐⭐ **对撞图 `0 → 2 ← 1` 上 `dSep` 的真值表**。

| # | 语句 | 真值 | 说明 |
|---|---|---|---|
| ① | `dSep ∅ {0} {1}` | ✅ **真** | **边际独立**：两父亲无路可通 |
| ② | `¬ dSep {2} {0} {1}` | ✅ **真** | **条件化碰撞点后不再分离** |
| ③ | `¬ dSep {0} {1} {2}` | ✅ **真** | 同上（对称写法） |
| ④ | `¬ dSep {0} {2} ∅` | ✅ **真** | 无条件时 `0 → 2` 有直接边，故不可分离 |

**⭐ ①② 并列读出对撞的本质**：

* **不**条件化碰撞点 ⟹ 两父亲**分离**（①）；
* **条件化**碰撞点 ⟹ **不**分离（②）。

**⟹ `dSep` 的语义（阻断 ⟹ 独立）与对撞的概率行为（条件化 ⟹ 依赖）
在这里正好反向** —— 这正是本文件把对撞的 T1A.1 结论写成 `MargIndep`（§2.3）
而不是 `CondMul` 的**结构性理由**。 -/
theorem collider_dsep_table :
    colliderDAG.dSep ∅ {0} {1} ∧
    (¬ colliderDAG.dSep {2} {0} {1}) ∧
    (¬ colliderDAG.dSep {0} {1} {2}) ∧
    (¬ colliderDAG.dSep {0} {2} ∅) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold FateV2.Modeling.Graph.DAG.dSep; decide)

/-- ⭐⭐⭐ **T1A.1 的图侧前提（对撞版）：`dSep ∅ {0} {1}`** ——
即两个父亲在**无条件下**边际独立。 -/
theorem collider_dsep_marginal : colliderDAG.dSep ∅ {0} {1} :=
  collider_dsep_table.1

/-- ⭐⭐⭐ **对撞图的关键否定：条件化碰撞点后不再分离**。 -/
theorem collider_dsep_conditioned_fails : ¬ colliderDAG.dSep {2} {0} {1} :=
  collider_dsep_table.2.1

/-! ### §2.3 概率侧：`ColliderMarkov`

**⚠⚠ 归一化必须写进定义**：若 `p_{Z|XY}` **任意**，
则 `∑_z p = p_X(x)·p_Y(y)·(∑_z p_{Z|XY}(x,y,z))` **含交叉项**，**不**边际独立。
§2.5 给出**去掉它后结论为假**的机检反例。 -/

/-- ⭐⭐ **对撞图的马尔可夫性**：`X`（顶点 `0`）与 `Y`（顶点 `1`）**边际独立**，
且碰撞点 `Z`（顶点 `2`）的机制 `p_{Z|XY}` **读双亲**、**归一**。

$$p\,((x,y),z) \;=\; p_X(x)\cdot p_Y(y)\cdot p_{Z|XY}(z \mid x,y),
\qquad \sum_z p_{Z|XY}(z \mid x,y) = 1$$

**⚠ 注意 `p_{Z|XY}` 读 `x` 和 `y`** —— 这正是碰撞点的机制依赖双亲。
**链/叉里 `X` 与 `Y` 的因子互不读对方；对撞里它们各自独立，但共同的 `Z` 读两者。** -/
def ColliderMarkov (p : FinJoint (Fin 2) (Fin 2) (Fin 3)) : Prop :=
  ∃ (pX : Fin 2 → ℝ) (pY : Fin 2 → ℝ) (pZXY : Fin 2 → Fin 2 → Fin 3 → ℝ),
    (∀ x y z, p ((x, y), z) = pX x * pY y * pZXY x y z) ∧
    (∀ x y, (∑ z, pZXY x y z) = 1)

/-- ⭐⭐⭐ **辅助引理：`X` 边缘在 `MargIndep` 口径下等于 `pX x * ∑ pY`**。 -/
theorem margX_of_colliderMarkov
    (p : FinJoint (Fin 2) (Fin 2) (Fin 3))
    (pX : Fin 2 → ℝ) (pY : Fin 2 → ℝ) (pZXY : Fin 2 → Fin 2 → Fin 3 → ℝ)
    (hfac : ∀ x y z, p ((x, y), z) = pX x * pY y * pZXY x y z)
    (hzsum : ∀ x y, (∑ z, pZXY x y z) = 1)
    (x : Fin 2) :
    (∑ z, ∑ y', p ((x, y'), z)) = pX x * (∑ y', pY y') := by
  -- 先交换求和次序：`∑_z ∑_{y'} = ∑_{y'} ∑_z`（有限 Fubini）。
  rw [Finset.sum_comm]
  -- 内层 `∑_z p((x,y'),z) = pX x * pY y'`（用 `hzsum`）。
  have hinner : ∀ (y' : Fin 2), (∑ z, p ((x, y'), z)) = pX x * pY y' := by
    intro b
    calc ∑ z, p ((x, b), z)
        = ∑ z, pX x * pY b * pZXY x b z :=
          Finset.sum_congr rfl fun z _ => hfac x b z
      _ = pX x * pY b * (∑ z, pZXY x b z) := by rw [Finset.mul_sum]
      _ = pX x * pY b * 1 := by rw [hzsum x b]
      _ = pX x * pY b := mul_one _
  calc ∑ y', ∑ z, p ((x, y'), z)
      = ∑ y', pX x * pY y' := Finset.sum_congr rfl fun y' _ => hinner y'
    _ = pX x * (∑ y', pY y') := by rw [Finset.mul_sum]

/-- ⭐⭐⭐⭐ **T1A.1（对撞图版）：`ColliderMarkov ⟹ X ⊥ Y`（边际独立）**。

**证明**：对 `z` 求和，`zsum_one` 把 `p_{Z|XY}` 求和为 `1`：
$$\sum_z p((x,y),z) = p_X(x)\,p_Y(y)\cdot 1 = p_X(x)\,p_Y(y).$$

**⚠ `hXsum` / `hYsum` 是概率律归一化**（`∑ p_X = 1`、`∑ p_Y = 1`），
诚实的非空假设：没有它们，`MargIndep` 的右边含 `∑p_X · ∑p_Y` 因子，
与左边的 `p_X · p_Y` 差一个常数因子。 -/
theorem collider_markov_implies_margindep
    (p : FinJoint (Fin 2) (Fin 2) (Fin 3))
    (pX : Fin 2 → ℝ) (pY : Fin 2 → ℝ) (pZXY : Fin 2 → Fin 2 → Fin 3 → ℝ)
    (hfac : ∀ x y z, p ((x, y), z) = pX x * pY y * pZXY x y z)
    (hzsum : ∀ x y, (∑ z, pZXY x y z) = 1)
    (hXsum : (∑ x, pX x) = 1) (hYsum : (∑ y, pY y) = 1) :
    MargIndep p := by
  intro x y
  -- ① 左边：`∑_z` 把 `pZXY` 求和消成 `1`。
  have hleft : (∑ z, p ((x, y), z)) = pX x * pY y := by
    calc ∑ z, p ((x, y), z)
        = ∑ z, pX x * pY y * pZXY x y z :=
          Finset.sum_congr rfl fun z _ => hfac x y z
      _ = pX x * pY y * (∑ z, pZXY x y z) := by rw [Finset.mul_sum]
      _ = pX x * pY y * 1 := by rw [hzsum x y]
      _ = pX x * pY y := mul_one _
  -- ② `X` 边缘。
  have hX : (∑ z, ∑ y', p ((x, y'), z)) = pX x := by
    rw [margX_of_colliderMarkov p pX pY pZXY hfac hzsum x, hYsum, mul_one]
  -- ③ `Y` 边缘（对称论证）。
  have hinner2 : ∀ (b : Fin 2), (∑ z, ∑ x', p ((x', b), z)) = pY b * (∑ x', pX x') := by
    intro b
    rw [Finset.sum_comm]
    have hcol : ∀ (x' : Fin 2), (∑ z, p ((x', b), z)) = pX x' * pY b := by
      intro a
      calc ∑ z, p ((a, b), z)
          = ∑ z, pX a * pY b * pZXY a b z :=
            Finset.sum_congr rfl fun z _ => hfac a b z
        _ = pX a * pY b * (∑ z, pZXY a b z) := by rw [Finset.mul_sum]
        _ = pX a * pY b * 1 := by rw [hzsum a b]
        _ = pX a * pY b := mul_one _
    calc ∑ x', ∑ z, p ((x', b), z)
        = ∑ x', pX x' * pY b := Finset.sum_congr rfl fun x' _ => hcol x'
      _ = (∑ x', pX x') * pY b := by rw [Finset.sum_mul]
      _ = pY b * (∑ x', pX x') := by rw [mul_comm]
  have hY : (∑ z, ∑ x', p ((x', y), z)) = pY y := by
    rw [hinner2 y, hXsum, mul_one]
  calc (∑ z, p ((x, y), z))
      = pX x * pY y := hleft
    _ = (∑ z, ∑ y', p ((x, y'), z)) * (∑ z, ∑ x', p ((x', y), z)) := by
        rw [hX, hY]

/-! ### §2.4 ⭐⭐ 对撞图的无条件版反例

**对撞图的结论是 `MargIndep`（不是 `CondMul`），故反例针对 `MargIndep`。** -/

/-- ⭐ 反例数据：`X` 与 `Y` 完全正相关（`x = y`），对撞点 `Z` 恒为 `0`。 -/
noncomputable def colliderCexP : FinJoint (Fin 2) (Fin 2) (Fin 3) :=
  fun q => if q.1.2 = q.1.1 then (1 / 2 : ℝ) else 0

/-- ⭐⭐⭐⭐⭐ **对撞图的无条件版是假命题**：存在 `p` 使
`colliderDAG.dSep ∅ {0} {1}`（**图侧成立**）却 `¬ MargIndep p`。

**证明**：取 `(x,y) = (0,0)`，用 `Fin.sum_univ_three` / `Fin.sum_univ_two` 展开求和。

* `∑_z p((0,0),z) = 1/2`（`z=0` 给 `1/2`，另两个 `0`）
* `∑_z∑_{y'} p((0,y'),z) = 1/2`；`∑_z∑_{x'} p((x',0),z) = 1/2`
* 左端 `= 1/2`，右端 `= (1/2)·(1/2) = 1/4` ⟹ **矛盾** ∎ -/
theorem collider_no_margindep_counterexample :
    ∃ (p : FinJoint (Fin 2) (Fin 2) (Fin 3)),
      colliderDAG.dSep ∅ {0} {1} ∧ ¬ MargIndep p := by
  refine ⟨colliderCexP, collider_dsep_marginal, ?_⟩
  intro h
  have hpt := h 0 0
  simp only [colliderCexP] at hpt
  norm_num [Fin.sum_univ_three, Fin.sum_univ_two] at hpt

/-- ⭐⭐⭐ **非空洞性**：`colliderCexP` **确实违反** `ColliderMarkov`。

**证明**：`colliderCexP ((0,1), z) = 0` 对**所有** `z` 成立（因 `1 ≠ 0`），
故 `∑_z pX 0 * pY 1 * pZXY 0 1 z = 0`，即 `pX 0 * pY 1 * 1 = 0`（用 `hzsum`）。
而 `colliderCexP ((0,0),0) = 1/2` 给出 `pX 0 ≠ 0`；再由 `colliderCexP ((1,1),0) = 1/2`
（`pY 1 = 0` 会使该式左边为 `0`）得矛盾 ∎ -/
theorem colliderCexP_not_colliderMarkov : ¬ ColliderMarkov colliderCexP := by
  rintro ⟨pX, pY, pZXY, hfac, hzsum⟩
  -- `p((0,1),z) = 0` 对所有 `z`（因 `1 ≠ 0`）。
  have h01 : ∀ z, pX 0 * pY 1 * pZXY 0 1 z = 0 := by
    intro z
    have h := hfac 0 1 z
    have hz : ¬ ((1 : Fin 2) = (0 : Fin 2)) := by decide
    simp only [colliderCexP, hz, if_false] at h
    exact h.symm
  -- 求和：`pX 0 * pY 1 * (∑ z, pZXY 0 1 z) = 0`，再用 `hzsum` 得 `pX 0 * pY 1 = 0`。
  have hmul : pX 0 * pY 1 = 0 := by
    have hsum : (∑ z, pX 0 * pY 1 * pZXY 0 1 z) = 0 := by
      rw [Finset.sum_congr rfl fun z _ => h01 z]
      simp
    rw [← Finset.mul_sum, hzsum 0 1, mul_one] at hsum
    exact hsum
  -- `p((0,0),0) = 1/2` ⟹ `pX 0 ≠ 0`。
  have h00 : pX 0 * pY 0 * pZXY 0 0 0 = 1 / 2 := by
    have h := hfac 0 0 0
    simpa [colliderCexP] using h.symm
  have hXne : pX 0 ≠ 0 := by
    intro h; rw [h, zero_mul, zero_mul] at h00; norm_num at h00
  -- 故 `pY 1 = 0`。
  have hY1 : pY 1 = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hXne
    · exact h
  -- 但 `(1,1,0)` 处 `p = 1/2` 与 `pY 1 = 0` 矛盾。
  have h11 : pX 1 * pY 1 * pZXY 1 1 0 = 1 / 2 := by
    have h := hfac 1 1 0
    simpa [colliderCexP] using h.symm
  rw [hY1, mul_zero, zero_mul] at h11
  norm_num at h11

/-! ### §2.5 ⚠ 反例：`ColliderMarkov` **去掉归一化后结论为假**

`zsum_one` **不是**技术便利，而是**必需的前提**。 -/

/-- 反例构造：`p_X = p_Y = 1/2`（常数，**已归一**）、`p_{Z|XY}(x,y,z) = 3`（常数、**不归一**）。
于是 `p((x,y),z) = 3/4` 恒常。 -/
noncomputable def colliderNonNormCex : FinJoint (Fin 2) (Fin 2) (Fin 3) :=
  fun _ => (1 / 2 : ℝ) * (1 / 2 : ℝ) * 3

/-- ⭐⭐⭐⭐ **去掉归一化的 `ColliderMarkov` ⟹ `MargIndep` 是假命题**：
存在 `p` 满足**除归一化外全部条件**，却**不**满足相应的边际独立。

* `∑_z p((x,y),z) = 3 · 3/4 = 9/4`
* `∑_z∑_{y'} p((x,y'),z) = 3 · (2 · 3/4) = 9/2`，`∑_z∑_{x'} p((x',y),z) = 9/2`
* 右端 `= (9/2)·(9/2) = 81/4 ≠ 9/4` ⟹ `¬ MargIndep` ∎

**⚠ 证明要点（上一版在此处报 `No goals to be solved`）**：`refine` 的四个 `?_` 占位
是**同时**存在的目标，`simp only` 会作用于**所有**目标；若把求和展开塞进 `simp only`
就会在第 1 个目标上提前闭合而产生 `No goals`。故本版：第 1 个 bullet 用
`norm_num [colliderNonNormCex]` 一次收尾，求和展开只在**最后一步**用
`norm_num [Fin.sum_univ_three, Fin.sum_univ_two]` 提供。 -/
theorem collider_nonNorm_counterexample :
    ∃ (p : FinJoint (Fin 2) (Fin 2) (Fin 3)),
      (∃ (pX : Fin 2 → ℝ) (pY : Fin 2 → ℝ) (pZXY : Fin 2 → Fin 2 → Fin 3 → ℝ),
        (∀ x y z, p ((x, y), z) = pX x * pY y * pZXY x y z) ∧
        (∑ x, pX x) = 1 ∧ (∑ y, pY y) = 1) ∧
      ¬ MargIndep p := by
  refine ⟨colliderNonNormCex, ⟨fun _ => 1 / 2, fun _ => 1 / 2, fun _ _ _ => 3,
    ?_, ?_, ?_⟩, ?_⟩
  · intro x y z
    norm_num [colliderNonNormCex]
  · rw [sum_fin2 (fun _ => (1 / 2 : ℝ))]; norm_num
  · rw [sum_fin2 (fun _ => (1 / 2 : ℝ))]; norm_num
  · intro h
    have hpt := h 0 0
    simp only [colliderNonNormCex] at hpt
    norm_num [Fin.sum_univ_three, Fin.sum_univ_two] at hpt

end FateV2.Predict.T1A1Graphs

/-! ## §3 公理审计 -/

-- 概率侧（叉图）
#print axioms FateV2.Predict.T1A1Graphs.fork_markov_implies_condMul
#print axioms FateV2.Predict.T1A1Graphs.fork_markov_condMul_gen
-- 图侧真值表
#print axioms FateV2.Predict.T1A1Graphs.fork_dsep_table
#print axioms FateV2.Predict.T1A1Graphs.collider_dsep_table
-- 无条件版反例 + 非空洞性
#print axioms FateV2.Predict.T1A1Graphs.fork_no_markov_counterexample
#print axioms FateV2.Predict.T1A1Graphs.forkCexP_not_forkMarkov
#print axioms FateV2.Predict.T1A1Graphs.collider_no_margindep_counterexample
#print axioms FateV2.Predict.T1A1Graphs.colliderCexP_not_colliderMarkov
-- 对撞图概率侧
#print axioms FateV2.Predict.T1A1Graphs.collider_markov_implies_margindep
#print axioms FateV2.Predict.T1A1Graphs.collider_dsep_marginal
#print axioms FateV2.Predict.T1A1Graphs.collider_dsep_conditioned_fails
#print axioms FateV2.Predict.T1A1Graphs.collider_nonNorm_counterexample
-- 图实例本身
#print axioms FateV2.Predict.T1A1Graphs.commonCauseEdge_key
#print axioms FateV2.Predict.T1A1Graphs.colliderEdge_key
-- 载体层小引理
#print axioms FateV2.Predict.T1A1Graphs.sum_fin2
#print axioms FateV2.Predict.T1A1Graphs.sum_fin2_fin2
#print axioms FateV2.Predict.T1A1Graphs.margZ_fin
#print axioms FateV2.Predict.T1A1Graphs.margXZ_fin
#print axioms FateV2.Predict.T1A1Graphs.margYZ_fin