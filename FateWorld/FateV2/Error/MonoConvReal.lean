import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field

/-!
# Error · **单调收敛的 `Real` 上界版**（专项 T51，从 `Core/` 迁出）

## 迁移登记
- 来源：`FateV2/Core/MonoConv.lean` 原 §6（T51 同批初稿）
- 动作：**D 移出**（同一批证明，**改目录**；证明内容一字未改）
- 理由：`Core/` 门禁 G4 是「**整目录**零公理，逐条扫，一条带公理就 FAIL」。
  `bound_limit` 的类型含 `Real` ⟹ 必然三公理 ⟹ **不能留在核内**。
  「在注释里如实登记三公理」**不能替代分目录** —— 这是本轮修正的定位错误。
- 先例：`Error/SigmaToVerdict.lean`（T46，20 条全带公理）、
  `Error/AICDataPath.lean`（T49，23 条全带公理）均在 `Error/` 下。
- 依赖裁决：**D-016**（核内零公理）、**D-022**（反空泛）
- 改动：**只新建本文件**；`Core/MonoConv.lean` 删去原 §6
- 状态：见 `_报告/T51-进度.md`

## 一、这个文件为什么必须存在（不能并回 `Core/`）

| 段 | 载体 | 公理 |
|---|---|---|
| `Core/MonoConv.lean`（框架主体 + `Nat` 实例 + 反例） | 纯 `Nat` / 抽象 `Preorder` | **零公理**（27 条） |
| **本文件**（`Real` 上界版） | 含 `Real` | **三公理**（类型带来，与写法无关） |

**类型决定公理，不决定战术**：凡签名含 `Real` 的定理，账面必然
`[propext, Classical.choice, Quot.sound]`（T17 实测，与证明写法无关）。
所以本文件的三公理**不是缺陷**，而是「`Real` 上的拓扑结论」的**正确归属**。

## 二、本文件与 `Core/MonoConv.lean` 的关系

```
Core/MonoConv.MonoConv.approach     -- 零公理，目标「逼近 ⊥」，说不出 ⊥ 是哪个值
本文件      .bound_limit            -- 三公理，目标「逼近给定的 M」，双侧
```

**两者不是同一条定理的强弱版，而是两个不同的问题**：

* `approach` 回答「**有没有**极限 / 能不能任意逼近」——**存在性**；
* `bound_limit` 回答「极限**等于哪个具体数**」——**定值性**。

`MonoConv` **说不出**「`⊥` 是 `b γ`」，因为 `MonoConv` 的 `⊥` 是类型类给的、
与序列无关；而 `b γ` 是**这个序列自己的**下确界。要说出「逼近 `b γ`」，
必须把「逼近的是 `M` 本身」写进前件 —— 这正是 `bound_limit` 的前件。

## 三、为什么 T47 的 `errProfile_tendsto_bias` 落在这里

T47（`Error/ErrProfileFromData.lean:313`）证的是

$$\mathrm{err}(n) = b(\gamma) + \mathrm{varProfile}(P,n,\gamma)
  \longrightarrow b(\gamma),$$

**不是** `→ 0`。它的 `f` 是 `b γ + c/(n+1)`、`M` 是 `b γ`：
* `hbound`：`varProfile P n γ ≥ 0` ⟹ `b γ + varProfile ≥ b γ`… 方向反了，
  实际是 `f n` **可能大于** `M`；T47 的极限是**从上方**还是**从下方**取决于 `c` 的符号。
  T47 的 `varProfile_nonneg` 给 `c ≥ 0` ⟹ `f n ≥ M`（**从上方**逼近）。
  本文件的前件写的是 `f n ≤ M`（从下方）——**这是对称的另一支**，
  由 `fun n => -f n` 的对称性覆盖（见 `bound_limit_of_ge`）。
* `hreach`：`varProfile_exists_lt` + 加法平移。

**本文件不含测度、不含 `varOf`** —— 它是那条的**去 `Measure` 化**骨架。

## 四、公理账

本文件**全部**定理带 `[propext, Classical.choice, Quot.sound]`（逐条 `#print axioms` 实测）。
这是 `Error/` 层的**正常账**（该层不要求零公理）。
-/

namespace FateV2.Error.MonoConvReal

open Filter

/-- **【上界版 · 从下方逼近】有上界 + 从下方可达 ⟹ 序列收敛到该上界。**

  $$\bigl(\forall n,\ f(n) \le M\bigr),\quad
    \bigl(\forall \varepsilon > 0,\ \exists N,\ \forall n \ge N,\ M - \varepsilon < f(n)\bigr)
    \Longrightarrow\quad f \longrightarrow M .$$

  **比 `Core/MonoConv.MonoConv.approach` 多说了什么**（两条的差别是本文件的全部内容）：
  * `approach` 的结论是「最终 `f n < b`」——**单侧**、且**不知道**逼近谁；
  * 本条结论是「最终 `|f n - M| < ε`」——**双侧**、且 `M` 是**指定的**那个数。
  * 这一步用到 `Real` 的 `abs_lt` 与 `dist`，**无法**在 `Preorder` 层表达
    （`Preorder` 没有「距离」），故必须落在 `Error/`。

  **比「趋于 `M`」的定义多说了什么**：`Tendsto` 的定义是「对任意邻域，最终落入」；
  本条的**前件是两条可检验的不等式**（常数上界 + 从下方可达），
  结论才是拓扑极限。前件里**没有** `Tendsto`，也没有 `Filter`。

  ⚠ **诚实边界**：本条只给「从**下方**逼近」（`f n ≤ M`）。从上方逼近由
  `bound_limit_of_ge` 对称给出；T47 的 `err` 属于**从上方**那一支。 -/
theorem bound_limit (f : Nat → Real) (M : Real)
    (hbound : ∀ n : Nat, f n ≤ M)
    (hreach : ∀ e : Real, 0 < e → ∃ N : Nat, ∀ n : Nat, N ≤ n → M - e < f n) :
    Tendsto f atTop (nhds M) := by
  rw [Metric.tendsto_atTop]
  intro e he
  obtain ⟨N, hN⟩ := hreach e he
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hN n hn], by linarith [hbound n]⟩⟩

/-- **【上界版 · 从上方逼近】有下界 + 从上方可达 ⟹ 序列收敛到该下界。**

  $$\bigl(\forall n,\ M \le f(n)\bigr),\quad
    \bigl(\forall \varepsilon > 0,\ \exists N,\ \forall n \ge N,\ f(n) < M + \varepsilon\bigr)
    \Longrightarrow\quad f \longrightarrow M .$$

  **比 `bound_limit` 多说了什么**：`bound_limit` 管「从下方逼近」；本条管**对称的那一支**。
  两条合起来覆盖「`M` 是 `f` 的下确界」的两种典型来源。

  **读法（与 T47 直接相关）**：`err(n) = b γ + varProfile P n γ` 里
  `varProfile ≥ 0`（`ErrProfileFromData.varProfile_nonneg`）⟹ `f n ≥ M := b γ`，
  即 `err` **从上方**逼近 `b γ`。**T47 的 `errProfile_tendsto_bias` 正是本条的实例。** -/
theorem bound_limit_of_ge (f : Nat → Real) (M : Real)
    (hbound : ∀ n : Nat, M ≤ f n)
    (hreach : ∀ e : Real, 0 < e → ∃ N : Nat, ∀ n : Nat, N ≤ n → f n < M + e) :
    Tendsto f atTop (nhds M) := by
  rw [Metric.tendsto_atTop]
  intro e he
  obtain ⟨N, hN⟩ := hreach e he
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hbound n], by linarith [hN n hn]⟩⟩

/-- **上界版可以化归到「零极限」**（本文件与 `Core` 的接线）。

  $$M \le f(n) \ \forall n,\quad f(n) < M + \varepsilon \text{ 最终}
    \iff\quad 0 \le f(n) - M,\quad f(n) - M < \varepsilon \text{ 最终}.$$

  **比 `bound_limit_of_ge` 多说了什么**：它把「逼近 `M`」**平移**成「`f - M` 逼近 `0`」，
  于是**任何**在 `Core/` 里证过的「零极限」结论都能自动升级为上界版——
  这是 `Core`（零公理）与 `Error`（三公理）之间**唯一**的通道，且通道本身只做平移。

  ⚠ **诚实边界**：平移后仍然是 `Real` 上的结论（三公理不变）。
  它**不**把公理从 3 降到 0；它只说明「上界版 = 零极限版 + 平移」，**不是新内容**。 -/
theorem bound_limit_of_tendsto_zero (f : Nat → Real) (M : Real)
    (h : Tendsto (fun n => f n - M) atTop (nhds 0)) :
    Tendsto f atTop (nhds M) := by
  have h1 : Tendsto (fun n => (f n - M) + M) atTop (nhds (0 + M)) :=
    h.add_const M
  have h2 : (fun n => (f n - M) + M) = f := by
    funext n
    ring
  rw [h2] at h1
  simpa using h1

/-! ===========================================================================
  §2  公理自检（每条证完立刻 `#print axioms`）
  =========================================================================== -/

#print axioms bound_limit
#print axioms bound_limit_of_ge
#print axioms bound_limit_of_tendsto_zero

end FateV2.Error.MonoConvReal
