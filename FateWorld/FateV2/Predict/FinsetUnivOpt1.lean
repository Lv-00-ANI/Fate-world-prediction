/-
命运理论 · **`Finset.univ` 复杂度压降（第 1 批，3 处真算法）**
================================================================================
模块：`FinsetUnivOpt1`（COMPLEX-1 深化；承 `_audit/FSUNIV-1` 的审查结论）

## 0 背景与判据（先声明口径）

`_audit/FSUNIV-1-Finset.univ复杂度抽样审查.md` 的结论是：
`Finset.univ` 全库 **565 次 / 133 文件**（`Finset.univ` 字面 453 + `univ : Finset`
类型标注并集），其中**绝大多数是数学陈述**，不是算法。
本文件**只做**符合下述判据的「真算法复杂度」处：

> **判据（任务书）**：`Finset.univ.filter` / `.sum` / `.prod` 出现在**循环里**
> （`List.map` / `Finset.biUnion` / 递归 / 迭代 / 每元素调用）。

本文件实测出的候选与处置：

| # | 位置 | 形态 | 处置 |
|---|---|---|---|
| **1** | `Fate/T21FiniteSearch.lean:273` `reachStep` | `S.biUnion (fun u => Finset.univ.filter (G.Adj u))` —— **`univ.filter` 在 `biUnion` 里** | ✅ 本节 §1 |
| **2** | `Fate/T21FiniteSearch.lean:278` `reachIter` | `reachStep` 被**递归**调用（`n` 轮）⟹ 每轮重跑 `|S|` 次 `univ` 扫描 | ✅ 本节 §1（与 1 同一处，随迭代传播）|
| **3** | `CausDAG.lean:349` `nonDescendants` | `univ.filter (fun w => ¬isAncestor v w ∧ w ≠ v)`，而 `descendants`（`:313`）对**同一 `v`** 又扫一次 `univ`、做**同一批 `isAncestor` 查询** | ✅ 本节 §2 |

**实测命令（逐字可复现）**：

```bash
cd /root/fate-dev
export PATH=/root/.elan/bin:$PATH; export ELAN_HOME=/root/.elan; export MATHLIB_NO_CACHE_ON_UPDATE=1

# 候选 ①：univ.filter 在 biUnion / map / fold / iter 里（全库唯一命中）
grep -n "Finset.univ" Fate/*.lean | grep -E "biUnion|\.map |foldr|iterate"
#   → Fate/T21FiniteSearch.lean:275:  S ∪ S.biUnion (fun u => Finset.univ.filter (fun v => G.Adj u v))

# 候选 ②：def 体（1..5 行内）含 univ.filter/sum/prod 的全部（26 处）
#   其中被「每元素/每轮」调用的只有 reachStep / nonDescendants 这一族（见报告 §1）

# 候选 ③：univ.filter 与 ∑ / ∏ 同现（4 族）
grep -rn "Finset.univ.filter" Fate/*.lean | grep -E "∏|∑"
```

**（候选 ③ 的处置：`BackdoorFiber` 的纤维分桶 `∑ z, ∑ u ∈ univ.filter (fz u = z), …`
其实已经是「单趟」的等价刻画，且其等价性定理 `fiber_decomposition` 已在库中；
`CondIndepEmptyZ` / `MainTheoremCFinal` 里的 `∏ v ∈ univ.filter …` 是**数学陈述**
（`mass` 的因子分解），不是被循环调用的算法。⟹ 均不纳入本文件的优化。）**

## 1 优化 1 + 2：`reachStep` / `reachIter` 的后继表

### 问题
`reachStep G S = S ∪ S.biUnion (fun u => Finset.univ.filter (G.Adj u))`。
对 `S` 的**每个** `u` 都重新扫一遍 `univ : Finset V` ⟹ **每步 O(|S|·|V|)**；
`reachIter` 迭代 `n` 轮 ⟹ **总计 O(n·|S|·|V|) = O(n·|V|²)**。
其中 `G.Adj u v` 这一判定被**重复计算**：若 `u` 在多轮里都在 `S` 中，
它的后继集被反复重建。

### 优化
把「每个顶点的后继列表」**预计算一次**成表 `succList G u`（`O(|V|²)` **一次性**，
不看迭代轮数），随后 `stepFast` 只在表上做 `List` 级拼合：
**每步只看 `Σ_{u∈S} |succ(u)| = |E∩(S×V)| ≤ |E|`**，不再扫 `univ`。
`reachIterFast` 把同一张表贯穿 `n` 轮（表建在**循环外**）。

### 等价性（本节的实质交付）
* `stepFast_eq_reachStep`：`stepFast (succList G) S = reachStep G S`（**逐 `S` 等价**）；
* `reachIterFast_eq`：`reachIterFast (succList G) n S = reachIter G n S`（**任意轮数**）。

两条都**不是**前件里塞结论：`stepFast` / `succList` 的定义体里**没有**
`reachStep` / `reachIter`，等价性靠 `List`/`Finset` 桥梁引理证明。

## 2 优化 3：`nonDescendants` 复用 `descendants` 的扫描结果

### 问题
`CausDAG.lean` 里

```
descendants    v = univ.filter (fun w =>     G.isAncestor v w)         -- :313
nonDescendants v = univ.filter (fun w => ¬G.isAncestor v w ∧ w ≠ v)    -- :349
```

两者对**同一 `v`** 各扫一遍 `univ`，并且**做的是同一批** `isAncestor v w` 判定
（后者只是取反再删 `v`）。`isAncestor` 是**传递闭包成员判定**（`mem_ancClosure`），
是全库最贵的单点谓词之一 ⟹ 默认用法下 `isAncestor` 查询次数**翻倍**。
DSep/nd 类推理里 `descendants v` 与 `nonDescendants v` 经常**同时**要
（如 `pa(v) ∩ nd(v)`、`insert v (nd v)ᶜ = desc v \ {v}`）。

### 优化
只算一次 `descendants v`，`nonDescendants v` 由**集合补运算**（`O(|V|)` 的
`Finset` 运算，无任何 `isAncestor` 查询）导出：

```
nonDescendants v = univ \ (descendants v ∪ {v})
```

### 等价性（本节的实质交付）
* `nonDescendants_eq_sdiff_descendants`：上式；
* `nonDescendants_eq_compl_sdiff`：等价形式 `nonDescendants v = (descendants v)ᶜ \ {v}`；
* `nonDescendants_computable_from_descendants`：**成本落点**——
  `nonDescendants v = univ \ ((univ.filter (isAncestor v)) ∪ {v})`，
  即 `isAncestor` 判定**全部集中在一次扫描**里；
* `descendants_eq_filter`：辅助（`rfl` 级，仅把 `descendants` 摊成 `filter` 形式）。

⚠ **本节的诚实说明**：`nonDescendants` / `descendants` 的定义本身是 `filter`，
所以 `nonDescendants_eq_sdiff_descendants` 是**集合层面的补集改写**，
证明量不大（`ext` + `simp`）。它的价值**不在证明难度**，而在
**把「两次 `isAncestor` 全扫」压成「一次 + 集合运算」**，
且该形式在本库内部已被 `Fate/T1A2.lean:89`（`nd`）**独立采用**。

## 3 诚实边界（必须登记）

1. **本文件只做 3 处**（候选 ① ② 同属 `reachStep`/`reachIter`，候选 ③ 是
   `nonDescendants`）。全库符合判据的处**远少于此前的「1377/565」口径**——
   这与 `_audit/FSUNIV-1` 的结论一致（绝大多数 `Finset.univ` 是数学陈述）。
2. **不声称渐近阶已形式化**：Lean 里**没有** `IsBigO` 形式的代价陈述（本库
   唯一带 `IsTheta` 的是 `Classification.lean` 的统计渐近，与本任务无关）。
   本文件给的是**结构性的**「不再重复扫描 / 不再重复查询」等价定理，
   复杂度论断本身（`O(n·|V|²) → O(|V|² + n·|E|)`）**是散文**，由
   `stepFast` 定义体中**不出现 `Finset.univ`** 这一**语法事实**直接支撑
   （见 `stepFast_no_univ_scan`，该定理是 **`rfl` 级**的，只确认 `stepFast`
   展开后只依赖传入的表与 `S`、不出现 `Finset.univ`；
   **它本身不是复杂度定理**，切勿当作阶的证明引用）。
3. **`succList` 用的是 `noncomputable`**：`Finset.toList` 依赖选择
   （`Finset.univ` 的 `toList` 需要 `Classical.choice`）。⟹ 本文件证明的是
   **数学等价**，不是「可 `#eval` 的性能对照」。**这是真实限制**：
   本库的 `Finset.univ` 全部需要 `Fintype`/`Classical`，「跑分」从来不是
   本项目的能力范围。**故本文件不声称有任何实测加速比。**
4. **不改任何既有模块**（`T21FiniteSearch` / `CausDAG` 逐字未动）；
   `lean` 仅**追加**一行 `import FinsetUnivOpt1`（任务书要求）。
6. **本文件中 `rfl` 级（不承重）的定理共 4 条**：`stepFast_no_univ_scan`、
   `reachIterFast_zero`、`reachIterFast_succ`、`descendants_eq_filter`。
   **实质等价性只有 3 条**：`stepFast_eq_reachStep`、`reachIterFast_eq`、
   `nonDescendants_eq_sdiff_descendants`（＋2 条推论
   `reachIterFast_card_singleton_eq` / `mem_reachIterFast_card_iff` 与
   1 条改写 `nonDescendants_eq_compl_sdiff` / 1 条成本落点
   `nonDescendants_computable_from_descendants`）。
   本文件**不**声称「11 条定理都是实质结果」。
5. 根目录存在 `_bf_p5.lean`（**不是 lake 模块根，不可 `import`**）里有一条
   相关但**不同**的命题 `(insert v (nd v))ᶜ = desc v \ {v}`；本文件 §2 的
   `nonDescendants_eq_sdiff_descendants` 在 `Fate/` 与 `CausDAG.lean` 中
   **未出现**（已用 `grep -rn "nonDescendants" --include=*.lean Fate/ CausDAG.lean`
   与 `grep -rn "univ \\\\ (G.descendants" Fate/ CausDAG.lean` 两种模式确认）。
6. 零 `sorry` / `admit` / `axiom` / `native_decide` / `?_` / `set_option maxHeartbeats`。
-/

import FateWorld.FateV2.Predict.T21FiniteSearch
import FateWorld.FateV2.Modeling.CausDAG
namespace FateV2.Predict

open FateV2.Modeling
namespace FinsetUnivOpt1

/-!
  # Predict · FinsetUnivOpt1

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FinsetUnivOpt1.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T21FiniteSearch, _root.CausDAG
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ==========================================================================
  §1  候选 ① + ②：`FateV2.Predict.T21.reachStep` / `reachIter` 的后继表优化
========================================================================== -/

open FateV2.Predict.T21 FateV2.Predict.CausalDirection

universe u

section ReachOpt

variable {V : Type u} [DecidableEq V] [Fintype V]

variable (G : CausalGraph V) [DecidableRel G.Adj]

/-! ### §1.1 预计算的后继表

`succList G u` = **一次**扫描 `univ` 得到的、`u` 的全部后继（作为 `List`）。
此后每步/每轮只在这张表上做 `List` 级操作。 -/
noncomputable def succList (u : V) : List V :=
  (Finset.univ.filter (fun v => G.Adj u v)).toList

omit [DecidableEq V] in
/-- 表的成员刻画：`v ∈ succList G u ↔ G.Adj u v`。 -/
theorem mem_succList {u v : V} : v ∈ succList G u ↔ G.Adj u v := by
  classical
  unfold succList
  simp

/-- 表的 `Finset` 像**就是**那一次 `univ.filter`：表没有丢掉任何信息。 -/
theorem succList_toFinset (u : V) :
    (succList G u).toFinset = Finset.univ.filter (fun v => G.Adj u v) := by
  classical
  unfold succList
  simp

/-! ### §1.2 优化版单步：`stepFast`

**语法事实**：`stepFast` 的定义体里**没有 `Finset.univ`** —— 它只读
传进来的表 `T` 与集合 `S`。这正是「不再重复扫描 `univ`」的形式化落点。 -/
noncomputable def stepFast (T : V → List V) (S : Finset V) : Finset V :=
  S ∪ (S.toList.flatMap T).toFinset

omit [Fintype V] in
/-- ⭐⭐ **`stepFast` 不自行枚举 `univ`**：把它作用在任意函数 `T` 上不需要
`Fintype V` 之外的任何枚举信息，且不调用 `Finset.univ`。
（本定理是 `rfl` 级的**语法**陈述：`stepFast` 展开后只出现 `S` 与 `T`。） -/
theorem stepFast_no_univ_scan (T : V → List V) (S : Finset V) :
    stepFast T S = S ∪ (S.toList.flatMap T).toFinset := rfl

/-- ⭐⭐⭐ **单步等价**（候选 ①）：表版本 `stepFast` **逐 `S` 等于**原 `reachStep`。 -/
theorem stepFast_eq_reachStep (S : Finset V) :
    stepFast (succList G) S = reachStep G S := by
  classical
  unfold stepFast reachStep
  have h : (S.toList.flatMap (succList G)).toFinset
      = S.biUnion (fun u => Finset.univ.filter (fun v => G.Adj u v)) := by
    ext v
    simp only [List.mem_toFinset, List.mem_flatMap, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, hadj⟩
      exact ⟨a, by simpa using ha, (mem_succList (G := G)).mp hadj⟩
    · rintro ⟨a, ha, hadj⟩
      exact ⟨a, by simpa using ha, (mem_succList (G := G)).mpr hadj⟩
  rw [h]

/-! ### §1.3 优化版迭代：`reachIterFast`

表 `T` 是**循环外**的参数：`n` 轮迭代共用手建一次的表。 -/
noncomputable def reachIterFast (T : V → List V) : ℕ → Finset V → Finset V
  | 0, S => S
  | n + 1, S => stepFast T (reachIterFast T n S)

omit [Fintype V] in
theorem reachIterFast_zero (T : V → List V) (S : Finset V) :
    reachIterFast T 0 S = S := rfl

omit [Fintype V] in
theorem reachIterFast_succ (T : V → List V) (n : ℕ) (S : Finset V) :
    reachIterFast T (n + 1) S = stepFast T (reachIterFast T n S) := rfl

/-- ⭐⭐⭐⭐ **迭代等价**（候选 ②）：**任意轮数 `n`** 下，表版本与原 `reachIter`
给出**同一个 `Finset`**。归纳于 `n`，每步用 `stepFast_eq_reachStep`。 -/
theorem reachIterFast_eq (n : ℕ) (S : Finset V) :
    reachIterFast (succList G) n S = reachIter G n S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [reachIterFast_succ, ih, reachIter_succ, stepFast_eq_reachStep]

/-- 推论：把表版本用在原 `reachIter` 的**标准调用点**（`n = card V`，从单点起）上，
结果与库里的主定理载体**同集合**。 -/
theorem reachIterFast_card_singleton_eq (a : V) :
    reachIterFast (succList G) (Fintype.card V) {a}
      = reachIter G (Fintype.card V) {a} :=
  reachIterFast_eq G (Fintype.card V) {a}

/-- 推论（可达判定复用）：`b` 在表版本 `card V` 轮内可达 ⟺ 原 `reachIter` 同上
（故上游 `mem_reachIter_card_iff_reach` 可直接套到表版本）。 -/
theorem mem_reachIterFast_card_iff (a b : V) :
    b ∈ reachIterFast (succList G) (Fintype.card V) {a}
      ↔ b ∈ reachIter G (Fintype.card V) {a} := by
  rw [reachIterFast_eq]

end ReachOpt

/-! ==========================================================================
  §2  候选 ③：`CausDAG.DAG.nonDescendants` 复用 `descendants` 的扫描
========================================================================== -/

open FateV2.Modeling.Graph

section NonDescOpt

variable {V : Type u} [DecidableEq V] [Fintype V]

variable (G : FateV2.Modeling.Graph.DAG V)

/-- 原 `descendants` 的显式形态（**逐字**，用于下方「右端不含 `isAncestor`」的论证）。 -/
theorem descendants_eq_filter (v : V) :
    G.descendants v = Finset.univ.filter (fun w => G.isAncestor v w) := rfl

/-- ⭐⭐⭐ **优化恒等式**（候选 ③）：`nonDescendants v` 由**一次** `descendants v`
扫描 + 集合补运算得出 —— 右端不再对每个 `w` 做 `isAncestor v w` 判定。 -/
theorem nonDescendants_eq_sdiff_descendants (v : V) :
    G.nonDescendants v = Finset.univ \ (G.descendants v ∪ {v}) := by
  ext w
  unfold FateV2.Modeling.Graph.DAG.nonDescendants FateV2.Modeling.Graph.DAG.descendants
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_union, Finset.mem_singleton, not_or]

/-- 等价形式（补集口径）：`nonDescendants v = (descendants v)ᶜ \ {v}`。 -/
theorem nonDescendants_eq_compl_sdiff (v : V) :
    G.nonDescendants v = (G.descendants v)ᶜ \ {v} := by
  ext w
  unfold FateV2.Modeling.Graph.DAG.nonDescendants FateV2.Modeling.Graph.DAG.descendants
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_compl, Finset.mem_singleton]

/-- ⭐⭐ **成本落点**：`nonDescendants v` 的**优化表达式**是
`univ \ (descendants v ∪ {v})`，其中对每个 `w` **只**做集合成员运算；
`isAncestor` 判定**全部集中在 `descendants v` 这一次扫描里**。 -/
theorem nonDescendants_computable_from_descendants (v : V) :
    G.nonDescendants v
      = Finset.univ \ ((Finset.univ.filter (fun w => G.isAncestor v w)) ∪ {v}) := by
  rw [← descendants_eq_filter, nonDescendants_eq_sdiff_descendants]

end NonDescOpt

end FinsetUnivOpt1

end FateV2.Predict