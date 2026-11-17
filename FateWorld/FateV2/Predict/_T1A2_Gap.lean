/-!
  # Predict · _T1A2_Gap

  ## 迁移登记
  - 来源：`FateWorld/Legacy/_T1A2_Gap.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：无
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-
# `T1A.2` 缺口登记（第 93 轮）

## 状态：**未实现**

`T1A.2`（图因子分解 ⟺ 马尔可夫性）**尚未形式化**。
本文件**只有注释、没有代码**，用途是把这个缺口**显式登记**，
避免「文件消失了就当它做完了」的静默遗漏。

## 已消失的草稿

- 曾有 `Fate\T1A2.lean`（348 行，`lake env lean` 报 21 个错误）。
- **第 93 轮实测**：该文件**不存在**；此后再被外部写入，
  内容退化为单行 `import Mathlib`（19 字节，无任何 `T1A2` 内容）；
  对全仓库 grep `T1A2` 在代码层**零命中**（仅本文文件名与注释命中）。
- 结论：它**是某个代理的临时草稿，从未真正交付**。

## 已有的相关定义（**在别处**，非本缺口的一部分）

`Fate\T1A1Graphs.lean` 里有：
- `ForkMarkov`（叉图的概率侧马尔可夫性，第 192 行）
- `ColliderMarkov`（对撞图，第 408 行）

`Fate\CliqueChain.lean` 里有**最接近** `T1A.2` 的既有内容：
- `FactorReadsOnlyOn ψ`（第 116 行）—— 「因子 `ψ_C` 只读团 `C` 上的坐标」，
  即「读集/因子只看团」这一**唯一接缝**的**已落地版本**；
  但它是 `(V → V) → ℝ` 上的**有限域**取代表，且**未与 `DAG` 结构挂钩**。
- `TwoFactorizable p a b`（第 126 行）—— 「`p = a · b`」的乘性形态。

**⚠ 但 `T1A.2` 要求的「图因子分解」定义 `FactorizesOn` 从未落地**：
它不是 `TwoFactorizable`（后者不含 `G`，也不量化团），
也不是 `FactorReadsOnlyOn`（后者不含 `p`，也不含 `DAG` 的团集）。

## 草稿中**有价值、值得保留**的定义（供后续重建）

以下来自那 348 行草稿，**彼此依赖极少、语义清晰**，
是重建 `T1A.2` 时应**优先抢救**的部分（原样记录，未经 Lean 验证）：

```lean
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- 读集：`f` 只依赖 `S` 上的坐标。`S` 是**图侧的顶点集**，这是图⇄概率的唯一接缝。 -/

namespace FateV2.Predict._T1A2_Gap

def ReadsOnlyOn (S : Finset V) (f : (V → ℕ) → ℝ) : Prop :=
  ∀ x y, (∀ u ∈ S, x u = y u) → f x = f y

/-- 团：`C` 中任意两点直连（方向任意）。 -/
def CliqueIn (G : DAG V) (C : Finset V) : Prop :=
  ∀ i ∈ C, ∀ j ∈ C, i ≠ j → (G.edge i j ∨ G.edge j i)

/-- ⭐ 图因子分解（无除法、正权团表形态）。 -/
def FactorizesOn (G : DAG V) (p : (V → ℕ) → ℝ) : Prop :=
  ∃ π : Finset V → (V → ℕ) → ℝ,
    (∀ C, ReadsOnlyOn C (π C)) ∧
    (∀ C, C ≠ ∅ → ∀ x, 0 < π C x) ∧
    (∀ C, π C ≠ 0 → CliqueIn G C) ∧
    ∀ x, p x = ∑ C ∈ (Finset.univ.powerset.filter (CliqueIn G)), ∏ v ∈ C, π C v x

/-- 非后代集：`V \ ({v} ∪ desc(v))`。 -/
def nd (G : DAG V) (v : V) : Finset V :=
  Finset.univ \ (G.descendants v ∪ {v})
```

**关于 `mem_nd`**：草稿声明的
`u ∈ nd G v ↔ ¬ G.isAncestor v u ∧ u ≠ v`
**在其原证明里依赖了 `DAG.mem_descendants`**（`CausDAG.lean` 第 317 行，
现成的），故这条**应当可证**，值得连同 `nd` 一起保留。

**已知在草稿里就写坏、不应直接照抄的部分**：
`pureOn` / `pureTables` / `PureTable` / `ChainSep` / `sum_singleton` /
`fork_elimination` 一段在草稿里引用了 **未定义的 `sumZ_ne_zero`**、
**未定义的 `g_pos`**，并混用了不存在的 `ForkMarkov`/`Fin 2` 语境变量；
这一整段是 21 个错误的来源，**不要在无重新论证的情况下重建**。

## 下一步

若要实现 `T1A.2`，需先定义（按依赖顺序，**每一步单独编译**）：
1. `ReadsOnlyOn S f`（`f` 只看 `S` 上的坐标）—— 纯 `Finset`，无风险；
2. `CliqueIn G C`（`C` 是 `G` 的团）—— 纯图论；
3. `FactorizesOn G p`（`p` 相对 `G` 因子分解）—— 引用 1、2；
4. `nd G v` + `mem_nd` —— 引用 `CausDAG` 的 `descendants` 与其 `mem_descendants`。

**⚠ 战略提醒（第 93 轮教训）**：
`FactorizesOn` 的 `⟺ 马尔可夫性` 方向**不可轻视**。
若 `FactorizesOn` 用 `∃ π`（自由参数）写法，则对**任意** `p`、
**任意** `G` 都成立（把 `π` 选成「只看一个顶点、其余为 1」即可），
于是 `⟺` 的右边若不同样是 `True`，定理就**为假**。
**正确的形态必须把参数钉在图上**（团来自 `G`、读集来自团），
这也是草稿试图用「纯表」修正、但未完成的点。

**结论**：`T1A.2` 目前**只有定义层的思路，没有一行可编译的代码**。
-/

-- 本文件无代码，仅登记缺口。

end FateV2.Predict._T1A2_Gap
