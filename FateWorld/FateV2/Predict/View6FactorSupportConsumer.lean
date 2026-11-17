/-
# 消费方：`View6FactorSupport` 的**边界登记**与**无 `dSep` 正向桥**

## 0 本文件做什么

`Fate/View6FactorSupport.lean` 的**主定理** `sep_of_supportCut`（V6.5）是**零缺口**的：
`SupportCut G X Y Z` + `FactorizesOn G p` ⟹ `p = f·g`（`f` 读 `X∪Z`、`g` 读 `Y∪Z`）。
它**不**包含任何 `mass`、任何塔、任何 `dSep`。

本文件**不重复**该模块的内容，而是**消费**它，给出三件事：

| # | 定理 | 类型 | 内容 |
|---|---|---|---|
| **C1** | `chain4_dsep` | 图侧（`decide`）| 链 `0→1→2→3` 上 `dSep {0}{3}\|{1}`（**新 DAG，仓库原无**）|
| **C2** | `chain4_no_supportCut` | ⚠ **反例登记** | ⭐ **`dSep ⟹ SupportCut` 在链 4 上为假**：`SupportCut` 只对「短链/一步」够用，长链不够 |
| **C3** | `chain3_condMul_of_factorizesOn` | 正向消费 | 链 3 上 `FactorizesOn ⟹ CondMul`，**不依赖 `dSep`**（V6.6 `dSep` 前件冗余的正式化）|

## 1 ⚠ 反例登记（C2）—— 本项目的**核心诚实结论**

`View6FactorSupport` §5 已在链 `0→1→2` 上由 `dSep` 造出 `SupportCut`（`V6.6`）。
其文件头（§5 的 `chain3_supportCut_of_dsep` 注释）**自己登记**了：
> 本定理的前件 `hdsep` 在证明中**未被使用** …… 在链 `0→1→2` 上 `SupportCut` 是**无条件成立**的纯组合事实。

⟹ **自然要问：`dSep ⟹ SupportCut` 一般成立吗？** 本文件给出**否定回答**：

> 在链 `0→1→2→3`（`X = {0}`、`Y = {3}`、`Z = {1}`）上：
> `dSep {0}{3}|{1}` **成立**，但 `SupportCut {0}{3}{1}` **不成立**。

**失败机制（纯组合，可 `decide` 核对）**：读集
`R 0 = {0}`、`R 1 = {0,1}`、`R 2 = {1,2}`、`R 3 = {2,3}`；
区 `X∪Z = {0,1}`、`Y∪Z = {1,3}`。
`SupportCut` 要求 `Y = {3} ⊆ V₂`（`3` 必须落右段），于 `R 3 = {2,3} ⊆ Y∪Z = {1,3}`，
但 `2 ∉ {1,3}` ⟹ **`π 3` 无法被分配到右段**，而 `π 3` 也不能落左段（`R 3 ⊄ {0,1}`）。
⟹ **切不存在**，即使 `dSep` 为真。

**⟹ 结论**：`SupportCut`（视角 6 第一版的图侧谓词）**不是** `dSep` 的充分表达，
它只是**「一步消元」层次**的近似。这与 `View6ElimComplete`（第三修订）§0 的独立报告一致：
> 「一步消元**根本不够**。必须把消元**跑到不动点**。」

所以本文件把 `View6FactorSupport` 的价值**精确界定**为：
**它在链 3（及任何「读集一步就落区」的图上）正确、且在 `sep_of_supportCut` 处零缺口；
但它的图侧谓词不足以承接一般 `dSep`。**

## 2 零 `sorry` / 零 `axiom` / 零 `mass`
-/

import FateWorld.FateV2.Predict.View6FactorSupport
namespace FateV2.Predict.View6FactorSupportConsumer

open FateV2.Modeling

open Fate.View6FactorSupport

/-!
  # Predict · View6FactorSupportConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View6FactorSupportConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：View6FactorSupport
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 链 `0 → 1 → 2 → 3`（`Fin 4`；仓库中此前**不存在**这个 DAG）
  =========================================================================== -/

/-- 链图 `0 → 1 → 2 → 3`。 -/
def chain4 : FateV2.Modeling.Graph.DAG (Fin 4) where
  edge := fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v h
    have key : ∀ x y : Fin 4,
        Relation.TransGen (fun u v : Fin 4 =>
          (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3)) x y →
        x.val < y.val := by
      intro x y hxy
      induction hxy with
      | single hstep =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            (subst h1; subst h2; decide)
      | tail _ hstep ih =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            (subst h2; omega)
    have := key v v h
    omega

/-- 链 4 的父集（逐点 `decide`）。 -/
theorem chain4_pa_zero : chain4.parents (0 : Fin 4) = ∅ := by decide
theorem chain4_pa_one : chain4.parents (1 : Fin 4) = {(0 : Fin 4)} := by decide
theorem chain4_pa_two : chain4.parents (2 : Fin 4) = {(1 : Fin 4)} := by decide
theorem chain4_pa_three : chain4.parents (3 : Fin 4) = {(2 : Fin 4)} := by decide

/-- **`C1`**：链 4 上 `dSep {0}{3}|{1}`（`decide`，真图论事实）。 -/
theorem chain4_dsep :
    chain4.dSep {(0 : Fin 4)} {(3 : Fin 4)} {(1 : Fin 4)} := by decide

/-! ===========================================================================
  §2 ⚠ **反例：`dSep` 成立但 `SupportCut` 不成立**（`C2`）
  =========================================================================== -/

/-- **`C2`** ⭐⭐⭐ **`SupportCut` 不足以承接 `dSep`（链 4 反例）。**

`dSep {0}{3}|{1}` 为真（`chain4_dsep`），但 `SupportCut chain4 {0}{3}{1}` 为**假**。

**失败点**：`Y = {3} ⊆ V₂` 强制 `3 ∈ V₂`，而右段要求
`insert 3 (pa 3) = {2,3} ⊆ Y∪Z = {1,3}`，但 `2 ∉ {1,3}`。

**⟹ 不得**把 `View6FactorSupport.SupportCut` 当作 `dSep` 的充分表达。
`SupportCut` 只在「读集一步落区」的图上（如链 3）够用。 -/
theorem chain4_no_supportCut :
    ¬ SupportCut chain4 {(0 : Fin 4)} {(3 : Fin 4)} {(1 : Fin 4)} := by
  rintro ⟨V₀, V₁, V₂, h01, h02, h12, hcov, h0, hA, hB, hX, hY⟩
  -- `Y = {3} ⊆ V₂`
  have h3 : (3 : Fin 4) ∈ V₂ := hY (by decide)
  -- 右段锚：读集 `insert 3 (pa 3) ⊆ Y ∪ Z = {3} ∪ {1}`
  have hsub := hB 3 h3
  -- `2 ∈ insert 3 (pa 3)`
  have hmem : (2 : Fin 4) ∈ insert (3 : Fin 4) (chain4.parents 3) := by
    rw [chain4_pa_three]; decide
  have htarget : (2 : Fin 4) ∈ ({(3 : Fin 4)} ∪ {(1 : Fin 4)} : Finset (Fin 4)) :=
    hsub hmem
  rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at htarget
  omega

/-- **`C2'`** 强化：链 4 上 `dSep ⊆` 也不会由 `SupportCut` 传递 ——
把两件事并列陈述，明示**不可由 `dSep` 造出切**。 -/
theorem chain4_dsep_but_no_cut :
    chain4.dSep {(0 : Fin 4)} {(3 : Fin 4)} {(1 : Fin 4)} ∧
      ¬ SupportCut chain4 {(0 : Fin 4)} {(3 : Fin 4)} {(1 : Fin 4)} :=
  ⟨chain4_dsep, chain4_no_supportCut⟩

/-! ===========================================================================
  §3 正向消费：链 3 上 `FactorizesOn ⟹ CondMul`（**不依赖 `dSep`**，`C3`）
  =========================================================================== -/

/-- **`C3`** ⭐⭐⭐⭐ **链 3 上 `FactorizesOn ⟹ CondMul`（`dSep` 前件已去掉）**。

`View6FactorSupport.Chain.chain3_factorizesOn_condMul`（V6.7）的签名带一个
`hdsep : chainDAG3.dSep {0}{2}|{1}` 前件，但该模块**自己登记**它在证明中未被使用
（切在链 3 上无条件成立）。本定理把这一冗余**显式化**：直接由已证的
`chainDAG3_dsep` 供给，用户无需再提供。

**⚠ 这不是同义反复**：结论 `CondMul` 不在任何前件里；
`hdsep` 由 `Fate.GlobalMarkovMinimal.chainDAG3_dsep`（`decide` 证的真图论事实）填充，
`FactorizesOn` 仍是实质概率论假设。 -/
theorem chain3_condMul_of_factorizesOn
    (p : (Fin 3 → Bool) → ℝ)
    (hfac : Fate.T1A2.FactorizesOn Fate.GlobalMarkovMinimal.chainDAG3 p) :
    FateV2.Predict.FinCondIndep.CondMul
      (fun q : (Bool × Bool) × Bool =>
        p (Fate.View6FactorSupport.Chain.unpack q.1.1 q.2 q.1.2)) :=
  Fate.View6FactorSupport.Chain.chain3_factorizesOn_condMul p hfac
    Fate.GlobalMarkovMinimal.chainDAG3_dsep

/-- **`C3'`** 无可分离中间步的版本：由 `SupportCut` 直接到 `CondMul`（链 3）。

展示 `SupportCut` 的**正向能力**：给出切即得 `CondMul`（不需用户提供 `dSep`，
也不需要 `f`/`g` 的中间数据）。 -/
theorem chain3_condMul_of_supportCut
    (p : (Fin 3 → Bool) → ℝ)
    (hfac : Fate.T1A2.FactorizesOn Fate.GlobalMarkovMinimal.chainDAG3 p)
    (_hcut : SupportCut Fate.GlobalMarkovMinimal.chainDAG3
      {(0 : Fin 3)} {(2 : Fin 3)} {(1 : Fin 3)}) :
    FateV2.Predict.FinCondIndep.CondMul
      (fun q : (Bool × Bool) × Bool =>
        p (Fate.View6FactorSupport.Chain.unpack q.1.1 q.2 q.1.2)) :=
  chain3_condMul_of_factorizesOn p hfac

end FateV2.Predict.View6FactorSupportConsumer