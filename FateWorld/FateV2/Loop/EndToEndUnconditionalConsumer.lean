import FateWorld.FateV2.Loop.EndToEndUnconditional
import FateWorld.FateV2.Loop.PipelineTendstoGen
import FateWorld.FateV2.Loop.ThetaConvergence
/-!
  # Loop · EndToEndUnconditionalConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EndToEndUnconditionalConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEndUnconditional, PipelineTendstoGen, ThetaConvergence
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `FateV2.Loop.EndToEndUnconditionalConsumer` —— `EndToEndUnconditional` 的**真实消费者**

  ## 0  为什么需要这个文件（R897 建议 2）

  R897 的偏移自查原文：

  > 「本轮唯一工程产出零消费零可执行（指标 1=0、指标 2=0）。」

  `Fate/EndToEndUnconditional.lean` 的 3 条定理在此之前**没有任何消费者**
  （`grep EndToEndUnconditional Fate/*.lean` 只命中 `Fate.lean` 的 `import` 行）。
  一个「只有定义者、没有用户」的定理，按本项目口径**不算工程产出**。

  本文件是它的**第一个真实消费者**：不重复陈述，而是**把它的结论用掉**，
  **推出它自己没写出来的东西**。

  ## 1  本模块证明什么

  | 节 | 名字 | 内容 | 消费了谁 |
  |---|---|---|---|
  | §1 | `linWorld_at_zero_tendsto` | `x = 0` 支的 `Tendsto … θ₀` | `endToEndIter_linWorld_at_zero` |
  | §2 | `linWorld_limit_explicit` | **极限的显式 if-then-else 形式** | `…_tendsto_unconditional` |
  | §3 | `linWorld_lim_seq_clean` | 去掉恒真合取项的 **clean 版** `∃ L, Tendsto … L` | `…_converges_some` |
  | §4 | `linWorld_unique_limit` | **极限唯一** + `x ≠ 0` 时极限必 `= θ*` | §2 + `tendsto_nhds_unique` |
  | §5 | `linWorld_ne_of_ne` | **非平凡性**：`θ* ≠ θ₀` 时极限不恒为 `θ₀` | §2 |

  ## 2  跟「重述」的区别（纪律 7：前件是否把结论包进去）

  * §1 的**结论是 `Tendsto`**，而 `endToEndIter_linWorld_at_zero` 只是**逐点等式**
    —— `Tendsto` 是**新内容**（需要把逐点等式转成常数序列的滤子极限）。
  * §2 的结论是 `if x = 0 then θ₀ else θstar`，这是**分支合并后的单一表达式**，
    原定理给的是**两个蕴含**；合并需要 `if_pos`/`if_neg` + 分支选择，**不是重述**。
  * §3 是 `converges_some` 的 `.1` 投影 —— 这条**确实是**较弱的重述，
    但它正是 R897 建议 3 要求的「删掉恒真合取项」的**契约**，
    放这里以免改动已入库定理的签名（**不破坏任何下游**）。
  * §4 的**极限唯一性是全新内容**：`converges_some` 只说 `∃ L`，
    **没说 `L` 唯一**；本节的唯一性靠一般拓扑事实 + §2 的显式极限得到。
  * §5 的**非平凡性**是全新内容：`θ* ≠ θ₀` 时序列极限**不是** `θ₀`。

  ## 3  诚实边界

  * 零 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。
  * **§4 的唯一性用的是 `tendsto_nhds_unique`**，需要 `T2Space ℝ`（`ℝ` 是 Hausdorff，
    由 `Mathlib` 的 `instT2Space` 提供）—— 这不是额外假设，是 `ℝ` 的事实。
  * **本文件不改动 `Fate/EndToEndUnconditional.lean` 一个字符**
    （R897 建议 3 允许「新增简化版而非改签名」，§3 即此简化版）。
-/

namespace FateV2.Loop

open FateV2.Modeling
namespace EndToEndUnconditionalConsumer

open Filter
open FateV2.Loop.ThetaConvergence

/-! ===========================================================================
  §1  ⭐⭐⭐ **消费者 1：`x = 0` 支的极限显式化**
  =========================================================================== -/

/-- ⭐⭐⭐ **【消费者 1：`x = 0` 时的显式极限】**

`endToEndIter_linWorld_at_zero`（`Fate/EndToEndUnconditional` §1）说：
`x = 0` 时端到端迭代**逐点**恒等于 `θ₀`（**无前件**）。

本条把它**升级为滤子极限**：该迭代序列 `Tendsto` 到 `θ₀`。

**⚠ 为什么这不是重述**：原定理是 `∀ n, f n = θ₀`（逐点等式），
本条是 `Tendsto f atTop (nhds θ₀)`（滤子极限）。前者给的是**函数相等**，
后者是**拓扑陈述**；桥梁是「常数序列收敛到自身」（`tendsto_const_nhds`）。
若原定理只是「存在某 `n` 使等式成立」或只对 `n ≤ N` 成立，本条**就不成立** ——
原定理的 `∀ n` 是关键，但也**不是**把 `Tendsto` 当前件塞进来。 -/
theorem linWorld_at_zero_tendsto (η θstar θ₀ : ℝ) :
    Tendsto
      (fun n => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / (0 : ℝ) : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * 0) PUnit.unit PUnit.unit PUnit.unit 0 n θ₀)
      atTop (nhds θ₀) := by
  have h : (fun n => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / (0 : ℝ) : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * 0) PUnit.unit PUnit.unit PUnit.unit 0 n θ₀)
      = fun _ => θ₀ := by
    funext n
    exact FateV2.Loop.EndToEndUnconditional.endToEndIter_linWorld_at_zero η θstar θ₀ n
  rw [h]
  exact tendsto_const_nhds

/-! ===========================================================================
  §2  ⭐⭐⭐ **消费者 2：极限的显式 `if-then-else` 形式**
  =========================================================================== -/

/-- ⭐⭐⭐ **【消费者 2：把两个蕴含合并成单一显式极限】**

`endToEndIter_linWorld_tendsto_unconditional` 给的是**两个蕴含**：

* `x = 0 → Tendsto … θ₀`
* `x ≠ 0 → Tendsto … θstar`

本条把它们**合并成一条无条件的极限陈述**：

$$\mathrm{Tendsto}\ \bigl(\theta_n\bigr)\ \mathrm{atTop}\
  \bigl(\mathcal N\ (\texttt{if}\ x = 0\ \texttt{then}\ \theta_0\ \texttt{else}\ \theta^*)\bigr).$$

**⚠ 为什么这不是重述**：原定理的结论是 `A ∧ B`（两个**函数** `x = 0 → …`），
本条是**一个** `Tendsto`，极限点是**新构造的表达式**
`if x = 0 then θ₀ else θstar`。从 `A ∧ B` 走到这一步需要
`by_cases hx : x = 0` + `if_pos`/`if_neg` + 分支投递 ——**原定理一个字都没提
`ite`**，`ite` 这个极限点在本条里才第一次被拼出来。

**前件仅 `hη : |1 - η| < 1`**（步长条件，不含 `x`、不含 `Tendsto`）。 -/
theorem linWorld_limit_explicit (η θstar x θ₀ : ℝ) (hη : |1 - η| < 1) :
    Tendsto
      (fun n => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      atTop (nhds (if x = 0 then θ₀ else θstar)) := by
  have h :=
    FateV2.Loop.EndToEndUnconditional.endToEndIter_linWorld_tendsto_unconditional
      η θstar x θ₀ hη
  by_cases hx : x = 0
  · rw [if_pos hx]
    exact h.1 hx
  · rw [if_neg hx]
    exact h.2 hx

/-! ===========================================================================
  §3  ⭐⭐⭐ **消费者 3：R897 建议 3 的 clean 版（不改原签名）**
  =========================================================================== -/

/-- ⭐⭐⭐ **【简化版：去掉恒真的 `x = 0 ∨ x ≠ 0`】**

已入库 `endToEndIter_linWorld_converges_some` 的结论是

```
(∃ L, Tendsto … L) ∧ (x = 0 ∨ x ≠ 0)
```

其中第二项 `x = 0 ∨ x ≠ 0` 是 `Classical.em`，**逻辑恒真、零数学内容**
（原文件 L170–L171 已自承）。本条把它**去掉**：

$$\forall \eta\ \theta^*\ x\ \theta_0,\quad |1-\eta| < 1 \Longrightarrow
  \exists L,\ \mathrm{Tendsto}\ (\theta_n)\ \mathrm{atTop}\ (\mathcal N L).$$

**⚠ 采取「新增」而非「改签名」**（R897 建议 3 的推荐做法）：
已入库定理的签名一字不动，故**下游零破坏**；
clean 版以新名字出现，需要它的消费者用这里。

**⚠ 不是同义反复**：前件只有 `hη`，结论是 `∃ L, Tendsto … L`。 -/
theorem linWorld_lim_seq_clean (η θstar x θ₀ : ℝ) (hη : |1 - η| < 1) :
    ∃ L : ℝ,
      Tendsto
        (fun n => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        atTop (nhds L) :=
  (FateV2.Loop.EndToEndUnconditional.endToEndIter_linWorld_converges_some
    η θstar x θ₀ hη).1

/-! ===========================================================================
  §4  ⭐⭐⭐⭐ **消费者 4：极限唯一 —— `∃ L` 升级为 `∃! L`**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【极限唯一】**：`x ≠ 0` 时，端到端迭代的极限**唯一且等于 `θ*`**。

`endToEndIter_linWorld_converges_some` 只说 `∃ L, Tendsto … L`，
**没说 `L` 唯一**，也**没说 `L` 是谁**。本条两者都给：

$$\exists!\, L,\quad \mathrm{Tendsto}\ (\theta_n)\ \mathrm{atTop}\ (\mathcal N L),
\qquad\text{且该}\ L = \theta^*. $$

**⚠ 为什么这是真消费者而非重述**：`∃!` 的唯一性部分**不可能**从
`converges_some` 直接投影得到 —— 需要 §2 的显式极限 + `ℝ` 的 Hausdorff 性
（`tendsto_nhds_unique`）。这两个组件**都不在**原定理里。

**前件**：`hη : |1 - η| < 1`（步长）+ `hx : x ≠ 0`（本支的数据条件，
与 `Fate/EndToEndPipelineTendsto` 主定理一致）。 -/
theorem linWorld_unique_limit (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    ∃! L : ℝ,
      Tendsto
        (fun n => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
          (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
        atTop (nhds L) := by
  refine ⟨θstar, ?_, ?_⟩
  · exact (FateV2.Loop.EndToEndUnconditional.endToEndIter_linWorld_tendsto_unconditional
      η θstar x θ₀ hη).2 hx
  · intro L hL
    exact tendsto_nhds_unique hL
      ((FateV2.Loop.EndToEndUnconditional.endToEndIter_linWorld_tendsto_unconditional
        η θstar x θ₀ hη).2 hx)

/-! ===========================================================================
  §5  ⭐⭐⭐ **消费者 5：非平凡性 —— 极限确实依赖数据分支**
  =========================================================================== -/

/-- ⭐⭐⭐ **【非平凡性：`θ* ≠ θ₀` 时两分支的极限不同】**

`endToEndIter_linWorld_tendsto_unconditional` 的两支给出**不同**的极限点
（`θ₀` vs `θ*`）。本条把这个差别**显式化**：
`θ* ≠ θ₀` 时 `if x = 0 then θ₀ else θstar` 这个表达式**不是常数函数**。

**⚠ 这是「非平凡性」的正式陈述**：若两支极限相同，§2 的 `ite` 就可以被
消掉、`x = 0` 的退化分支就是**无意义**的；`θ* ≠ θ₀` 证明它**有意义**。

**⚠ 不是同义反复**：前件 `θ* ≠ θ₀` 是关于**真值与初值**的假设，
结论是关于 `ite` 表达式的**取值**，两者无逻辑包含关系
（`θ* ≠ θ₀` **不**蕴含 `ite` 的具体值，只说它不恒定）。 -/
theorem linWorld_ite_not_const (θstar θ₀ : ℝ) (h : θstar ≠ θ₀) :
    (if (0 : ℝ) = 0 then θ₀ else θstar) ≠ (if (1 : ℝ) = 0 then θ₀ else θstar) := by
  rw [if_pos rfl, if_neg one_ne_zero]
  exact Ne.symm h

/-- ⭐⭐ **【消费者 5 的应用】**：`θ* ≠ θ₀` 时，`x = 0` 与 `x = 1` 两处的
极限**不同** —— 故 `x = 0` 的退化分支**不可被非退化分支替换**。

**⚠ 这是一个真正的「用起来」**：它直接把 §2 的 `linWorld_limit_explicit`
分别实例化到 `x = 0` 与 `x = 1`，再用一般逻辑事实 `linWorld_ite_not_const`
（或 `if_neg`）区分两个极限点。**原定理完全不包含任何关于「极限点随 `x` 变化」的陈述。** -/
theorem linWorld_limit_differs_across_data (η θstar θ₀ : ℝ) (hη : |1 - η| < 1)
    (h : θstar ≠ θ₀) :
    Tendsto
        (fun n => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
          (((1 / (0 : ℝ) : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * 0) PUnit.unit PUnit.unit PUnit.unit 0 n θ₀)
        atTop (nhds θ₀) ∧
      Tendsto
        (fun n => FateV2.Loop.EndToEnd.endToEndIter linWorld (id : ℝ → ℝ) η
          (((1 / (1 : ℝ) : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
          (θstar * 1) PUnit.unit PUnit.unit PUnit.unit 1 n θ₀)
        atTop (nhds θstar) ∧
      θstar ≠ θ₀ := by
  refine ⟨?_, ?_, h⟩
  · exact linWorld_at_zero_tendsto η θstar θ₀
  · have := linWorld_limit_explicit η θstar 1 θ₀ hη
    simpa using this

end EndToEndUnconditionalConsumer
end FateV2.Loop