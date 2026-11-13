/-
============================================================================
  规则核心链 · COMPLEX-1 §5 第 2、3 条：`detTraj` 的 O(T²) → O(T)
============================================================================

## 问题（为什么原 `detTraj` 取整条轨迹是 O(T²)）

`detTraj`（`Fate/TrajGenDeterministic.lean:154`）定义为

  `detTraj F f T θ x₀ u ε a = fun n => stateAt F f T θ u ε a x₀ n.val _`，

而 `stateAt` 是**原始递归**（`TrajGenDeterministic.lean:139`）：

  `stateAt 0 = x₀`,
  `stateAt (n+1) = f (stateAt n) (u ⟨n,_⟩) (ε ⟨n,_⟩) θ (a ⟨n,_⟩)`。

于是对**每一项** `detTraj ... ⟨k,_⟩` 求值，`stateAt` 各自**从头**迭代 `k` 次。
取整条轨迹 `[x₀, …, x_{T-1}]` 的总 `f` 调用次数为 `0 + 1 + … + (T-1) = T(T-1)/2`
⟹ **O(T²)**。

## 本模块的做法（照搬 `Fate/TrajGenScan.lean` 的骨架）

`detTrajScan` **不调用** `stateAt`/`detTraj` 去逐项重算，而是一次 `foldl`
（累积器为「当前状态, 逆序前缀」）：

* 每一步做**恰好一次** `f` 调用，并把新状态 `cons` 到逆序前缀
  （`List.cons` 是 O(1)，**不是** `++ [·]`）；
* 结束时做**一次** `List.reverse`（O(T)）。

⟹ **总代价 = 恰好 `T` 次 `f` 调用 + O(T) 的列表操作**（即 O(T)）。

**为什么不用 `List.map (fun k => detTraj ... ⟨k,_⟩)`**：
那个写法**仍然**对每项重算 `stateAt`，故仍是 O(T²)。
本模块采取累积器版，`detTraj` **不出现**在 `detTrajScan` 的定义中。

**为什么不用 `acc ++ [x']`**：`List` 追加在左参数上是 O(|acc|)，
逐次追加 ⟹ 合计 O(T²)。故累积器存**逆序**前缀，用 O(1) 的 `cons`，
最后统一 `reverse` 一次。

## 与原 `trajGen` / `trajScan` 的关系（★ 诚实说明）

`detTraj` 与 `trajGen` **不是同一个定义**：
`trajGen` 的输入是 `ℕ → U`（总函数），`detTraj` 的输入是 `Fin T → U`（有限视窗），
二者入口不同、签名不同。**但它们满足同一个递推**（`stateAt_succ` / `trajGen_succ`
都是 `rfl` 级），且 `detTraj` 的第 `k` 项**就是** `stateAt ... k`（`rfl` 级）。
因此本模块**不走 `trajScan`**（它跑在 `ℕ → U` 上，无法直接吃 `Fin T` 输入），
而是直接在 `Fin T` 视窗上**复刻** `trajFold` 的累积器骨架；
`detFold_spec` 与 `TrajGenScan.trajFold_spec` 是**同一归纳结构**，
只是把「第 `n` 项 = `trajGen ... n`」换成「第 `n` 项 = `stateAt ... n`」。

## 不动原定义

本模块**只新增**，不修改 `Fate/TrajGenDeterministic.lean` 或
`Fate/TrajGenScan.lean` 的任何内容；原定义与已证定理原样保留，新旧并存。

## 本模块的定理

| 类别 | 声明 | 内容 |
|---|---|---|
| 工具 | `stateAt_proof_irrel` | `stateAt` 对界限证明无关 |
| 工具 | `detSt` | `Fin (n+1) → X` 的索引函数，第 `k` 项 = `stateAt ... k` |
| 工具 | `ofFn_detSt_succ` | `ofFn (detSt (n+1)) = ofFn (detSt n) ++ [stateAt (n+1)]` |
| 定义 | `detStep` | 累积器推进一步，**恰好一次 `f` 调用**，`cons` 为 O(1) |
| 定义 | `detFold` | `List.range n` 上的折叠，`n` 步 ⟹ `n` 次 `f` 调用 |
| 定义 | `detTrajScan` | 一次扫描产生长度 `T+1` 的前缀列表（O(T) 次 `f` 调用）|
| ⭐ 核心 | `detFold_spec` | 归纳不变量：首分量 = `stateAt ... n`，次分量取逆 = `ofFn (detSt n)` |
| 对齐 | `detFold_fst` | 累积器首分量 = `stateAt ... n` |
| 长度 | `detTrajScan_length` | `(detTrajScan ... T).length = T + 1` |
| ⭐ 核心 | `detTrajScan_get` | `(detTrajScan ... T)[k]? = some (detTraj ... ⟨k,_⟩)`（`k < T`）|
| 首项 | `detTrajScan_get_zero` | `(detTrajScan ... T)[0]? = some x₀`（`0 < T`）|
| 一致 | `detTrajScan_agrees` | ⭐⭐ 对一切 `k < T`，扫描第 `k` 项 = `detTraj` 第 `k` 项 |
| 末项 | `detTrajScan_last` | 扫描末项 = `stateAt ... T`（`T+1` 项中的最后一项）|
| 单步 | `detStep_fst` | `(detStep ... p k).1 = f p.1 (u ⟨k,_⟩) …`（`k < T`）|
| 单步 | `detFold_succ_fst` | 累积器前进一步即得 `stateAt` 的下一步 |

**关于「O(T)」的严格表述（诚实标注）**：`detTrajScan` 的定义体内对 `f` 的
调用次数**恰为 `T`**（`detStep` 体内 `f` 出现一次，`List.range T` 有 `T` 个元素）。
列表操作合计 O(T)（`List.range` O(T) + `cons` T 次 O(1) + `reverse` 一次 O(T)）。
**对比**：逐项取 `[detTraj ... ⟨0,_⟩, …, detTraj ... ⟨T-1,_⟩]` 需 `T(T+1)/2` 次
`f` 调用。本模块**不声称** Lean 具备复杂度分析机制（Lean 不做渐近复杂度分析）；
上述计数是**算法层面的手工论证**，本文件的定理只固定**语义等价**
（扫描 = 逐项 `detTraj`，在 `k < T` 上），**不固定**复杂度。
即：本文件证明的是「把逐项重算换成一次扫描**不改变结果**」，
代价论证见上（`f` 调用次数从 `T(T+1)/2` 降到 `T`）。

标签：**[定义性约定]**（新增构造）+ **[推导]**（对齐定理）。

零 `sorry` / `admit` / `axiom`。
============================================================================
-/

import FateWorld.Legacy.TrajGenDeterministic
import FateWorld.Legacy.TrajGenScan
import FateWorld.Legacy.Frame

namespace Fate
namespace DetTrajScan

open TrajGenDeterministic TrajGenScan

/-! ===========================================================================
    §1  工具：`stateAt` 的证明无关性，与 `Fin (n+1)` 索引函数
    =========================================================================== -/

/-- **`stateAt` 对界限证明无关**：同一 `n`、不同 `n ≤ T` 的证明给同一值。

`stateAt` 是原始递归，`n → n+1` 一步只依赖 `stateAt n`（其余参数相同），
故对 `n` 归纳：`n+1` 步用两次 `stateAt_succ`（`rfl` 级）展开，
`Fin` 索引的证明项与 `stateAt` 的界限证明差异由 Lean 的证明无关性自动消去。 -/
theorem stateAt_proof_irrel (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier)
    (x₀ : F.X.Carrier) (n : ℕ) (h1 h2 : n ≤ T) :
    stateAt F f T θ u ε a x₀ n h1 = stateAt F f T θ u ε a x₀ n h2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show stateAt F f T θ u ε a x₀ (n+1) h1 = stateAt F f T θ u ε a x₀ (n+1) h2
    rw [show stateAt F f T θ u ε a x₀ (n+1) h1
          = f (stateAt F f T θ u ε a x₀ n (Nat.le_of_succ_le h1))
              (u ⟨n, by omega⟩) (ε ⟨n, by omega⟩) θ (a ⟨n, by omega⟩) from rfl]

/-- **前缀状态族**：`Fin (n+1) → X`，其第 `k` 项就是 `stateAt ... k`。

`n ≤ T` 是必要的（`Fin (n+1)` 的每个索引都要落在视窗内）。
用途：把「扫描列表 = 逐项状态」写成 `ofFn (detSt ...)`，便于归纳。 -/
def detSt (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier)
    (n : ℕ) (h : n ≤ T) : Fin (n+1) → F.X.Carrier :=
  fun k => stateAt F f T θ u ε a x₀ k.val (Nat.le_trans (Nat.le_of_lt_succ k.isLt) h)

/-- **`ofFn (detSt ...)` 的分解式**：
`ofFn (detSt (n+1)) = ofFn (detSt n) ++ [stateAt ... (n+1)]`。

用 `List.ofFn_succ_last`（`ofFn g = ofFn (g ∘ castSucc) ++ [g (last n)]`）展开；
`castSucc` 保持 `val`，故两项逐点相同（`stateAt` 的证明无关性）。
这是 `detFold_spec` 归纳步骤里「逆序前缀的 `reverse` 对齐」所需的唯一形状引理。 -/
theorem ofFn_detSt_succ (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) (n : ℕ) (h : n+1 ≤ T) :
    List.ofFn (detSt F f T θ x₀ u ε a (n+1) h)
      = List.ofFn (detSt F f T θ x₀ u ε a n (Nat.le_of_succ_le h))
          ++ [stateAt F f T θ u ε a x₀ (n+1) h] := by
  rw [List.ofFn_succ_last]
  congr 1

/-! ===========================================================================
    §2  一次扫描的定义（累积器版，O(T) 次 `f` 调用）
    =========================================================================== -/

/-- **单步**：把累积器 `(x, revPrefix)` 推进一格（视窗内第 `k` 步）。

`x` 是当前状态 `x_k`，`revPrefix` 是 `[x_k, …, x₀]`（**逆序**）。
返回新状态 `x_{k+1} = f x_k (u ⟨k,_⟩) (ε ⟨k,_⟩) θ (a ⟨k,_⟩)` 与新的逆序前缀。
`k < T` 时**恰好一次 `f` 调用**；`k ≥ T`（越界，实际不会发生）时不变。
`cons` 是 O(1)。 -/
def detStep (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier)
    (p : F.X.Carrier × List F.X.Carrier) (k : ℕ) : F.X.Carrier × List F.X.Carrier :=
  if h : k < T then
    let x' := f p.1 (u ⟨k, h⟩) (ε ⟨k, h⟩) θ (a ⟨k, h⟩)
    (x', x' :: p.2)
  else p

/-- **折叠累积器**：从 `(x₀, [x₀])` 出发，对 `k = 0, …, n-1` 各走一步。

步数恰为 `n` ⟹ **恰好 `n` 次 `f` 调用**（`detStep` 内一次），
其余为 `List.range`（O(n)）与 `cons`（O(1)）。
**注意：本定义中不出现 `stateAt` / `detTraj`**，故不会重复迭代。 -/
def detFold (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier)
    (n : ℕ) : F.X.Carrier × List F.X.Carrier :=
  (List.range n).foldl (detStep F f T θ u ε a) (x₀, [x₀])

/-- **一次扫描产生的轨迹前缀**：长度 `T + 1` 的列表

  `[x₀, x₁, …, x_T]`，其中 `x_{k+1} = f x_k (u ⟨k,_⟩) (ε ⟨k,_⟩) θ (a ⟨k,_⟩)`。

由 `detFold` 的逆序累积器 `reverse` 一次得到（O(T)）。
**⟹ 总代价 = `T` 次 `f` 调用 + O(T) 列表操作。** -/
def detTrajScan (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier) :
    List F.X.Carrier :=
  (detFold F f T θ x₀ u ε a T).2.reverse

/-! ===========================================================================
    §3  折叠的归纳不变量
    =========================================================================== -/

/-- ⭐ **不变量（`n` 步之后）**：

* 首分量 = `stateAt ... n`（当前状态就是第 `n` 个状态）；
* 次分量取逆 = `ofFn (detSt ... n)` = `[x₀, …, x_n]`。

证明只需对 `n` 归纳，`n → n+1` 一步**恰好消费一次 `stateAt_succ`（`rfl` 级）**
与 `ofFn_detSt_succ`。 -/
theorem detFold_spec (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) (n : ℕ) (h : n ≤ T) :
    (detFold F f T θ x₀ u ε a n).1 = stateAt F f T θ u ε a x₀ n h
      ∧ (detFold F f T θ x₀ u ε a n).2.reverse
          = List.ofFn (detSt F f T θ x₀ u ε a n h) := by
  induction n with
  | zero =>
      refine ⟨rfl, ?_⟩
      show ([x₀] : List F.X.Carrier).reverse = List.ofFn (detSt F f T θ x₀ u ε a 0 h)
      show ([x₀] : List F.X.Carrier).reverse
        = List.ofFn (fun k : Fin 1 => stateAt F f T θ u ε a x₀ k.val
            (Nat.le_trans (Nat.le_of_lt_succ k.isLt) h))
      rw [List.ofFn_succ]
      rfl
  | succ n ih =>
      have hnT : n < T := by omega
      have hle : n ≤ T := Nat.le_of_succ_le h
      obtain ⟨ih1, ih2⟩ := ih hle
      have stepEq : detFold F f T θ x₀ u ε a (n+1)
          = detStep F f T θ u ε a (detFold F f T θ x₀ u ε a n) n := by
        show (List.range (n+1)).foldl (detStep F f T θ u ε a) (x₀, [x₀]) = _
        rw [List.range_succ, List.foldl_append]
        rfl
      rw [stepEq]
      simp only [detStep, dif_pos hnT]
      refine ⟨?_, ?_⟩
      · show f (detFold F f T θ x₀ u ε a n).1 (u ⟨n, hnT⟩) (ε ⟨n, hnT⟩) θ (a ⟨n, hnT⟩)
          = stateAt F f T θ u ε a x₀ (n+1) h
        rw [ih1]
        rw [show stateAt F f T θ u ε a x₀ (n+1) h
              = f (stateAt F f T θ u ε a x₀ n (Nat.le_of_succ_le h))
                  (u ⟨n, by omega⟩) (ε ⟨n, by omega⟩) θ (a ⟨n, by omega⟩) from rfl]
      · show (f (detFold F f T θ x₀ u ε a n).1 (u ⟨n, hnT⟩) (ε ⟨n, hnT⟩) θ (a ⟨n, hnT⟩)
                :: (detFold F f T θ x₀ u ε a n).2).reverse
            = List.ofFn (detSt F f T θ x₀ u ε a (n+1) h)
        rw [List.reverse_cons, ih2, ih1, ofFn_detSt_succ F f T θ x₀ u ε a n h]
        congr 1

/-- **首分量**：累积器走 `n` 步后的当前状态 = `stateAt ... n`。 -/
theorem detFold_fst (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) (n : ℕ) (h : n ≤ T) :
    (detFold F f T θ x₀ u ε a n).1 = stateAt F f T θ u ε a x₀ n h :=
  (detFold_spec F f T θ x₀ u ε a n h).1

/-- **折叠结果的列表部分**：`(detFold ... n).2.reverse = ofFn (detSt ... n)`。

单独取出以便重写（`detFold_spec` 的结论以 `.2.reverse` 为左端，
先展开 `detTrajScan` 的 `List.getElem?_reverse` 会错位，故先固定此式）。 -/
theorem detFold_rev (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) (n : ℕ) (h : n ≤ T) :
    (detFold F f T θ x₀ u ε a n).2.reverse = List.ofFn (detSt F f T θ x₀ u ε a n h) :=
  (detFold_spec F f T θ x₀ u ε a n h).2

/-! ===========================================================================
    §4  长度与逐点对齐（核心）
    =========================================================================== -/

/-- **长度**：`(detTrajScan ... T).length = T + 1`（不依赖 `f`）。 -/
theorem detTrajScan_length (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) :
    (detTrajScan F f T θ x₀ u ε a).length = T + 1 := by
  unfold detTrajScan
  rw [detFold_rev F f T θ x₀ u ε a T (le_refl T), List.length_ofFn]

/-- ⭐⭐ **【核心：扫描的第 `k` 项 = `detTraj` 的第 `k` 项】**（`k < T`）。

这是把 O(T²) 的「逐项重算」替换成 O(T) 的「一次扫描」的**正确性依据**：
扫描产出的列表的前 `T` 项与逐项调用 `detTraj` 得到的 `T` 项**逐点相同**。

⚠ **诚实说明**：`detTrajScan` 有 `T+1` 项（`x₀..x_T`，与 `trajScan` 同构），
`detTraj` 只有 `Fin T` 的 `T` 项（`x₀..x_{T-1}`）；本定理覆盖 `detTraj` 的**全部**项
（条件 `k < T` 正是 `detTraj` 的定义域）。末项 `x_T` 见 `detTrajScan_last`。 -/
theorem detTrajScan_get (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) (k : ℕ) (hk : k < T) :
    (detTrajScan F f T θ x₀ u ε a)[k]? = some (detTraj F f T θ x₀ u ε a ⟨k, hk⟩) := by
  unfold detTrajScan
  rw [detFold_rev F f T θ x₀ u ε a T (le_refl T), List.getElem?_ofFn]
  rw [dif_pos (by omega : k < T + 1)]
  show some (detSt F f T θ x₀ u ε a T (le_refl T) ⟨k, by omega⟩)
      = some (stateAt F f T θ u ε a x₀ k (Nat.le_of_lt hk))
  congr 1

/-- ⭐⭐ **逐点一致（打包读法）**：对一切 `k < T`，
扫描的第 `k` 项 = `detTraj` 的第 `k` 项。

即 `detTrajScan_get` 的全称形式——扫描**不改变语义**，只改变代价。 -/
theorem detTrajScan_agrees (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) :
    ∀ k : Fin T, (detTrajScan F f T θ x₀ u ε a)[k.val]? = some (detTraj F f T θ x₀ u ε a k) :=
  fun k => detTrajScan_get F f T θ x₀ u ε a k.val k.isLt

/-- **首项 = 初值**：`(detTrajScan ... T)[0]? = some x₀`（`0 < T`）。 -/
theorem detTrajScan_get_zero (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) (hT : 0 < T) :
    (detTrajScan F f T θ x₀ u ε a)[0]? = some x₀ := by
  rw [detTrajScan_get F f T θ x₀ u ε a 0 hT,
    show detTraj F f T θ x₀ u ε a ⟨0, hT⟩ = x₀ from rfl]

/-- **末项 = `stateAt ... T`**（`0 < T`）。

⚠ **诚实说明**：`detTrajScan` 产生 `T + 1` 个状态 `[x₀, …, x_T]`
（与 `TrajGenScan.trajScan` 同构），而 `detTraj` 只有 `Fin T` 的 `T` 个状态
`x₀, …, x_{T-1}`。故扫描的**末项**是 `x_T`，它**不在** `detTraj` 的值域内；
它等于 `stateAt ... T`（即累积器走完 `T` 步后的首分量）。
前 `T` 项与 `detTraj` 的对应关系由 `detTrajScan_get`（`k < T`）给出。 -/
theorem detTrajScan_last (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) :
    (detTrajScan F f T θ x₀ u ε a).getLast?
      = some (stateAt F f T θ u ε a x₀ T le_rfl) := by
  have hlen : (detTrajScan F f T θ x₀ u ε a).length = T + 1 :=
    detTrajScan_length F f T θ x₀ u ε a
  rw [List.getLast?_eq_getElem?, hlen]
  show (detTrajScan F f T θ x₀ u ε a)[T + 1 - 1]? = _
  rw [Nat.add_sub_cancel]
  unfold detTrajScan
  rw [detFold_rev F f T θ x₀ u ε a T (le_refl T), List.getElem?_ofFn,
    dif_pos (by omega : T < T + 1)]
  congr 1

/-! ===========================================================================
    §5  单步方程（说明扫描内 `f` 只被调用一次）
    =========================================================================== -/

/-- ⭐ **扫描内的单步方程**：从 `x_k` 直接一步得到 `x_{k+1}`，
`f` 在 `detStep` 中**只被调用一次**（这是 O(T) 而非 O(T²) 的算法根据）。

与 `detTraj_succ` 的区别：`detTraj_succ` 把 `detTraj ... ⟨n+1,_⟩` 归约到
`stateAt ... n`，而**重新求值** `stateAt ... n` 仍要迭代 `n` 次；
本引理则给出**累积器已持有的**当前状态往前一步，无需回溯。 -/
theorem detStep_fst (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier) (a : Fin T → F.Act.Carrier)
    (p : F.X.Carrier × List F.X.Carrier) (k : ℕ) (hk : k < T) :
    (detStep F f T θ u ε a p k).1 = f p.1 (u ⟨k, hk⟩) (ε ⟨k, hk⟩) θ (a ⟨k, hk⟩) := by
  unfold detStep
  rw [dif_pos hk]

/-- **累积器上前进一步即得 `stateAt` 的下一步**：
`(detFold ... (n+1)).1 = f (detFold ... n 的首分量) (u ⟨n,_⟩) …`。 -/
theorem detFold_succ_fst (F : Frame) (f : Step F) (T : ℕ) (θ : F.Θ.Carrier)
    (x₀ : F.X.Carrier) (u : Fin T → F.U.Carrier) (ε : Fin T → F.Ν.Carrier)
    (a : Fin T → F.Act.Carrier) (n : ℕ) (h : n+1 ≤ T) :
    (detFold F f T θ x₀ u ε a (n+1)).1
      = f (detFold F f T θ x₀ u ε a n).1
          (u ⟨n, by omega⟩) (ε ⟨n, by omega⟩) θ (a ⟨n, by omega⟩) := by
  have hnT : n < T := by omega
  have stepEq : detFold F f T θ x₀ u ε a (n+1)
      = detStep F f T θ u ε a (detFold F f T θ x₀ u ε a n) n := by
    show (List.range (n+1)).foldl (detStep F f T θ u ε a) (x₀, [x₀]) = _
    rw [List.range_succ, List.foldl_append]
    rfl
  rw [stepEq]
  exact detStep_fst F f T θ u ε a _ n hnT

end DetTrajScan
end Fate
