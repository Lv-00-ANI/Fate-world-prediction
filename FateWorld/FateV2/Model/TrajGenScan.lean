/-
============================================================================
  规则核心链 · COMPLEX-1 第 1 条：`trajGen` 的 O(T²) → O(T)（一次扫描版）
============================================================================

## 问题（为什么原 `trajGen` 取前缀是 O(T²)）

`trajGen : ... → Traj ℕ F.X`，而 `Traj ι X = ι → X.Carrier`（`Fate/Basic.lean:227`），
即**一个函数**，其值由 `Nat.rec` 定义：

  `trajGen F f θ x₀ u ε a n = Nat.rec x₀ (fun k xk => f xk (u k) (ε k) θ (a k)) n`.

于是对**每一项** `trajGen ... k` 求值，`Nat.rec` 各自**从头**迭代 `k` 次。
取整条前缀 `[trajGen ... 0, ..., trajGen ... T]` 的总调用次数为
`0 + 1 + ... + T = T(T+1)/2` ⟹ **O(T²)** 次 `f` 调用。

## 本模块的做法

`trajScan` **不调用 `trajGen`**，而是一次 `List.foldl`（累积器为
`(当前状态, 逆序前缀)`）：

* 每一步做**恰好一次** `f` 调用，并把新状态 `cons` 到逆序前缀
  （`List.cons` 是 O(1)，**不是** `++ [·]`）；
* 结束时做**一次** `List.reverse`（O(T)）。

⟹ **总代价 = 恰好 `T` 次 `f` 调用 + O(T) 的列表操作**（即 O(T)）。
对比原方案取 `T+1` 项的 `T(T+1)/2` 次 `f` 调用。

**为什么不用 `List.map (fun k => trajGen ... k)`**：
那个写法**仍然**对每项调用 `trajGen`，故仍是 O(T²)（任务书 §关键难点 已指出）。
本模块采取的是累积器版，`trajGen` **不出现**在 `trajScan` 的定义中。

**为什么不用 `acc ++ [x']`**：`List` 追加在左参数上是 O(|acc|)，
逐次追加 ⟹ 合计 O(T²)。故累积器存**逆序**前缀，用 O(1) 的 `cons`，
最后统一 `reverse` 一次。

## 不动原定义

本模块**只新增**，不修改 `Fate/TrajGenDeterministic.lean` 的任何内容；
`trajGen` 与其已证定理原样保留，新旧并存。

## 本模块的定理

| 类别 | 声明 | 内容 |
|---|---|---|
| 定义 | `trajStep` | 累积器推进一步，**恰好一次 `f` 调用**，`cons` 为 O(1) |
| 定义 | `trajFold` | `List.range T` 上的折叠，`T` 步 ⟹ `T` 次 `f` 调用 |
| 定义 | `trajScan` | 一次扫描产生长度 `T+1` 的前缀列表（O(T) 次 `f` 调用）|
| 工具 | `range_map_succ` | `(range (n+1)).map g = (range n).map g ++ [g n]` |
| ⭐ 核心 | `trajFold_spec` | 归纳不变量：累积器首分量 = `trajGen ... n`，次分量取逆 = 前缀列表 |
| 对齐 | `trajFold_fst` | 累积器首分量 = `trajGen ... n` |
| 对齐 | `trajScan_eq_map` | `trajScan ... T = (range (T+1)).map (fun k => trajGen ... k)` |
| 长度 | `trajScan_length` | `(trajScan ... T).length = T + 1` |
| ⭐ 核心 | `trajScan_get` | `(trajScan ... T)[k]? = some (trajGen ... k)`（`k ≤ T`）|
| 首项 | `trajScan_get_zero` | `(trajScan ... T)[0]? = some x₀` |
| 末项 | `trajScan_last` | 末项 = `trajGen ... T` |
| 单步 | `trajStep_fst` | `(trajStep ... p k).1 = f p.1 (u k) (ε k) θ (a k)`（`rfl`）|
| 单步 | `trajFold_succ_fst` | 累积器前进一步即得 `trajGen` 的下一步 |
| 汇总 | `trajScan_last_eq` | 累积器首分量 = `trajGen ... T` |
| 汇总 | `trajScan_agrees_on_range` | 逐点一致（`∀ k ≤ T`）|

**关于「O(T)」的严格表述**：`trajScan` 的定义体内对 `f` 的调用次数
**恰为 `T`**（`trajFold_spec` 的证明里 `n+1` 步只消费一次 `trajStep`，
`trajStep` 体内 `f` 出现一次）。列表操作合计 O(T)
（`List.range` O(T) + `cons` T 次 O(1) + `reverse` 一次 O(T)）。
**对比**：逐项取 `[trajGen ... 0, …, trajGen ... T]` 需 `T(T+1)/2` 次 `f` 调用。
本模块**不声称** Lean 具备复杂度分析机制；上述计数是算法层面的手工论证，
`trajStep_fst` / `trajScan_eq_map` 等定理只固定**语义等价**，不固定复杂度。

标签：**[定义性约定]**（新增构造）+ **[推导]**（对齐定理）。

零 `sorry` / `admit` / `axiom`。
============================================================================
-/

import FateWorld.FateV2.Model.TrajGenDeterministic
import FateWorld.FateV2.Model.Frame
namespace FateV2.Model
namespace TrajGenScan

open FateV2.Model.TrajGenDeterministic

/-!
  # Model · TrajGenScan

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TrajGenScan.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TrajGenDeterministic, Frame
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  一次扫描的定义（累积器版，O(T) 次 `f` 调用）
    =========================================================================== -/

/-- **单步**：把累积器 `(x, revPrefix)` 推进一格。
`x` 是当前状态 `x_k`，`revPrefix` 是 `[x_k, …, x₀]`（**逆序**）。
返回新状态 `x_{k+1} = f x_k (u k) (ε k) θ (a k)` 与新的逆序前缀。
**恰好一次 `f` 调用**，`cons` 是 O(1)。 -/
def trajStep (F : Frame) (f : Step F) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    (p : F.X.Carrier × List F.X.Carrier) (k : ℕ) : F.X.Carrier × List F.X.Carrier :=
  let x' := f p.1 (u k) (ε k) θ (a k)
  (x', x' :: p.2)

/-- **折叠累积器**：从 `(x₀, [x₀])` 出发，对 `k = 0, …, T-1` 各走一步。

步数恰为 `T` ⟹ **恰好 `T` 次 `f` 调用**（`trajStep` 内一次），
其余为 `List.range`（O(T)）与 `cons`（O(1)）。
**注意：本定义中不出现 `trajGen`**，故不会重复迭代。 -/
def trajFold (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    (T : ℕ) : F.X.Carrier × List F.X.Carrier :=
  (List.range T).foldl (trajStep F f θ u ε a) (x₀, [x₀])

/-- **一次扫描产生的轨迹前缀**：长度 `T + 1` 的列表

  `[x₀, x₁, …, x_T]`，其中 `x_{k+1} = f x_k (u k) (ε k) θ (a k)`。

由 `trajFold` 的逆序累积器 `reverse` 一次得到（O(T)）。
**⟹ 总代价 = `T` 次 `f` 调用 + O(T) 列表操作。** -/
def trajScan (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    (T : ℕ) : List F.X.Carrier :=
  (trajFold F f θ x₀ u ε a T).2.reverse

/-! ===========================================================================
    §2  折叠的归纳不变量
    =========================================================================== -/

/-- **前缀列表的递推式**：`(range (n+1)).map g = (range n).map g ++ [g n]`。

把 `range_succ` 与 `map_append` 组合一次，供下面的归纳直接使用。 -/
theorem range_map_succ {β : Type _} (g : ℕ → β) (n : ℕ) :
    (List.range (n + 1)).map g = (List.range n).map g ++ [g n] := by
  rw [List.range_succ, List.map_append]
  rfl

/-- **不变量（`n` 步之后）**：

* 首分量 = `trajGen ... n`（当前状态就是第 `n` 个状态）；
* 次分量取逆 = `[(fun k => trajGen ... k) 0, …, (fun k => trajGen ... k) n]`
  = `(List.range (n+1)).map (fun k => trajGen ... k)`。

这是把「扫描的第 `k` 项 = `trajGen` 的第 `k` 项」从累积器结构上固定下来的引理：
证明只需对 `n` 归纳，`n → n+1` 一步**恰好消费 `trajGen_succ`（`rfl` 级）**。 -/
theorem trajFold_spec (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    (trajFold F f θ x₀ u ε a n).1 = trajGen F f θ x₀ u ε a n
      ∧ (trajFold F f θ x₀ u ε a n).2.reverse
          = (List.range (n + 1)).map (fun k => trajGen F f θ x₀ u ε a k) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · show x₀ = trajGen F f θ x₀ u ε a 0
        rw [trajGen_zero]
      · show ([x₀] : List F.X.Carrier).reverse
              = (List.range (0 + 1)).map (fun k => trajGen F f θ x₀ u ε a k)
        rw [range_map_succ]
        show ([x₀] : List F.X.Carrier).reverse
              = (List.range 0).map (fun k => trajGen F f θ x₀ u ε a k)
                  ++ [trajGen F f θ x₀ u ε a 0]
        rw [trajGen_zero]
        rfl
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      have step : trajFold F f θ x₀ u ε a (n + 1)
          = trajStep F f θ u ε a (trajFold F f θ x₀ u ε a n) n := by
        show (List.range (n + 1)).foldl (trajStep F f θ u ε a) (x₀, [x₀]) = _
        rw [List.range_succ, List.foldl_append]
        rfl
      refine ⟨?_, ?_⟩
      · rw [step]
        show (f (trajFold F f θ x₀ u ε a n).1 (u n) (ε n) θ (a n)) = _
        rw [h1, trajGen_succ]
      · rw [step]
        show ((f (trajFold F f θ x₀ u ε a n).1 (u n) (ε n) θ (a n))
                :: (trajFold F f θ x₀ u ε a n).2).reverse = _
        rw [List.reverse_cons, h2, h1]
        show (List.range (n + 1)).map (fun k => trajGen F f θ x₀ u ε a k)
                ++ [f (trajGen F f θ x₀ u ε a n) (u n) (ε n) θ (a n)]
              = (List.range (n + 1 + 1)).map (fun k => trajGen F f θ x₀ u ε a k)
        rw [range_map_succ (fun k => trajGen F f θ x₀ u ε a k) (n + 1)]
        congr 1

/-- **首分量**：累积器走 `n` 步后的当前状态 = `trajGen ... n`。 -/
theorem trajFold_fst (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    (trajFold F f θ x₀ u ε a n).1 = trajGen F f θ x₀ u ε a n :=
  (trajFold_spec F f θ x₀ u ε a n).1

/-- **次分量取逆 = 前缀列表**（与 `trajScan` 的定义同物，故亦即 `trajScan` 的展开式）。 -/
theorem trajScan_eq_map (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (T : ℕ) :
    trajScan F f θ x₀ u ε a T
      = (List.range (T + 1)).map (fun k => trajGen F f θ x₀ u ε a k) :=
  (trajFold_spec F f θ x₀ u ε a T).2

/-! ===========================================================================
    §3  长度与逐点对齐（核心）
    =========================================================================== -/

/-- **长度**：`trajScan ... T` 的长度恰为 `T + 1`（不依赖 `f`）。 -/
theorem trajScan_length (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (T : ℕ) :
    (trajScan F f θ x₀ u ε a T).length = T + 1 := by
  rw [trajScan_eq_map, List.length_map, List.length_range]

/-- ⭐⭐ **【核心：扫描的第 `k` 项 = `trajGen` 的第 `k` 项】**（`k ≤ T`）。

这是把 O(T²) 的「逐项重算」替换成 O(T) 的「一次扫描」的**正确性依据**：
扫描产出的列表与逐项调用 `trajGen` 得到的列表**逐点相同**。 -/
theorem trajScan_get (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    (T k : ℕ) (hk : k ≤ T) :
    (trajScan F f θ x₀ u ε a T)[k]? = some (trajGen F f θ x₀ u ε a k) := by
  rw [trajScan_eq_map, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- **首项 = 初值**：`(trajScan ... T)[0]? = some x₀`（`T` 任意，含 `T = 0`）。 -/
theorem trajScan_get_zero (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (T : ℕ) :
    (trajScan F f θ x₀ u ε a T)[0]? = some x₀ := by
  rw [trajScan_get F f θ x₀ u ε a T 0 (Nat.zero_le T), trajGen_zero]

/-- **末项 = `trajGen ... T`**：扫描列表的最后一个元素就是第 `T` 个状态。 -/
theorem trajScan_last (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (T : ℕ) :
    (trajScan F f θ x₀ u ε a T).getLast? = some (trajGen F f θ x₀ u ε a T) := by
  rw [List.getLast?_eq_getElem?, trajScan_length,
    show T + 1 - 1 = T from by omega]
  exact trajScan_get F f θ x₀ u ε a T T le_rfl

/-! ===========================================================================
    §4  单步方程（说明扫描内 `f` 只被调用一次）
    =========================================================================== -/

/-- ⭐ **扫描内的单步方程**：从 `x_k` 直接一步得到 `x_{k+1}`，
`f` 在 `trajStep` 中**只被调用一次**（这是 O(T) 而非 O(T²) 的算法根据）。

与 `trajGen_succ` 的区别：`trajGen_succ` 把 `trajGen ... (n+1)` 归约到
`trajGen ... n`，而**重新求值** `trajGen ... n` 仍要迭代 `n` 次；
本引理则给出**累积器已持有的**当前状态往前一步，无需回溯。 -/
theorem trajStep_fst (F : Frame) (f : Step F) (θ : F.Θ.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    (p : F.X.Carrier × List F.X.Carrier) (k : ℕ) :
    (trajStep F f θ u ε a p k).1 = f p.1 (u k) (ε k) θ (a k) := rfl

/-- **累积器上前进一步即得 `trajGen` 的下一步**：
`trajFold ... (n+1)` 的首分量 = `f (trajFold ... n 的首分量) (u n) …`。 -/
theorem trajFold_succ_fst (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (n : ℕ) :
    (trajFold F f θ x₀ u ε a (n + 1)).1
      = f (trajFold F f θ x₀ u ε a n).1 (u n) (ε n) θ (a n) := by
  have step : trajFold F f θ x₀ u ε a (n + 1)
      = trajStep F f θ u ε a (trajFold F f θ x₀ u ε a n) n := by
    show (List.range (n + 1)).foldl (trajStep F f θ u ε a) (x₀, [x₀]) = _
    rw [List.range_succ, List.foldl_append]
    rfl
  rw [step]
  exact trajStep_fst F f θ u ε a (trajFold F f θ x₀ u ε a n) n

/-! ===========================================================================
    §5  与 `trajGen` 的等价性总结
    =========================================================================== -/

/-- **扫描的最后状态 = `trajGen ... T`**（`trajFold` 的首分量即 `trajScan` 的末项）。 -/
theorem trajScan_last_eq (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) (T : ℕ) :
    (trajFold F f θ x₀ u ε a T).1 = trajGen F f θ x₀ u ε a T :=
  trajFold_fst F f θ x₀ u ε a T

/-- **两种取值方式一致（逐点）**：
扫描列表的第 `k` 项与 `trajGen ... k` 相同，故扫描**不改变语义**，只改变代价。 -/
theorem trajScan_agrees_on_range (F : Frame) (f : Step F) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier)
    (a : ℕ → F.Act.Carrier) (T : ℕ) :
    ∀ k, k ≤ T →
      (trajScan F f θ x₀ u ε a T)[k]? = some (trajGen F f θ x₀ u ε a k) :=
  fun k hk => trajScan_get F f θ x₀ u ε a T k hk

end TrajGenScan
end FateV2.Model