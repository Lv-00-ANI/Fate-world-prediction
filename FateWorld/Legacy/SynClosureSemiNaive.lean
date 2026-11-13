/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.SynClosureSemiNaive
阶段：**COMPLEX-1 §5 第 5 条（`synClosureIter` 单步的半朴素化）**

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
清单第 5 条的优化目标是：`synClosureIter` 的**单步**
`synClosureOne Sig B` 线性扫全部 `Sig`（代价 `O(|Sig|·|B|)`），
半朴素化（semi-naive，Datalog 标准优化）希望只对**新加入元素**重算。

本文件把半朴素化的**正确性前提**形式化并证明：

1. `synClosureOne_mono` —— **一步闭包关于起点单调**（核心，真内容）；
2. `synClosureIter_subset_mono` —— **迭代闭包关于起点单调**（真内容）；
3. `synClosureOne_eq_self_of_satisfies` —— **规则已被满足 ⇒ 一步闭包不动**；
4. `synClosureIter_eq_self_of_satisfies` —— **规则已被满足 ⇒ 迭代可停**；
5. `synClosureOne_subset_synClosureIter_succ` ——
   **旧的一步闭包结果在扩展后仍被新迭代包含**（半朴素化「不丢结论」）。

---------------------------------------------------------------------------
⚠ 对任务给定陈述的诚实裁定（最高频问题排查）
---------------------------------------------------------------------------
任务书要求证：

    theorem satisfies_mono_of_subset {S T} (h : S ⊆ T)
        (hs : Satisfies S sig) : Satisfies T sig

**该陈述为假，不可证**。理由（`Satisfies K S Sig` 的定义见 §1，
即「每条规则左部 ⊆ `S` ⇒ 右部 ⊆ `S`」）：

* 证 `Satisfies T Sig` 要对**所有** `X ⊆ T` 的规则给出 `Y ⊆ T`；
* 但 `hs` 只覆盖 `X ⊆ S` 的那些规则。`X ⊆ T` **推不出** `X ⊆ S`，
  故对「`X ⊆ T` 但 `X ⊄ S`」的规则，`hs` 毫无信息，而这类规则的
  右部**可以**不落在 `T` 里。

**形式化反例**（本文件 §1 的定理 `not_satisfies_mono_of_subset`）：
只要属性集含两个不同元素 `a ≠ b`，取 `Sig = {({a}, {b})}`、
`S = ∅`、`T = {a}`，则 `Satisfies ∅ Sig` 为真而 `Satisfies {a} Sig` 为假。

**故本文件不陈述该定理**（纪律第 6 条：证不出就删除，并在文件头如实说明）。
半朴素化**真正需要**的单调性不是它，而是 §2 的
`synClosureOne_mono`（一步闭包算子对**起点**单调），
它给出「先在小集合上推完，再扩展，旧结论全部保留」。

另：任务给定

    theorem synClosureIter_mono {S T} (h : S ⊆ T) (n) : ...

**与 `Fate/Implication.lean` 已有的同名定理冲突**（该名字已占用为
「关于**步数**单调」`m ≤ n → Sigma^m ⊆ Sigma^n`）。本文件把「关于**起点**
单调」命名为 `synClosureIter_subset_mono`，两者是不同的定理。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
* `Satisfies`（规则族在集合上被满足）在本项目中**此前不存在**
  （`grep -rn "Satisfies" Fate/*.lean` 无命中），本文件给出**新定义**。
* 本文件**零 `sorry` / 零 `axiom` / 零 `admit`**。
-/

import FateWorld.Legacy.Implication
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace Fate

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-! ===========================================================================
    §1  规则族在集合上的满足（语法侧）
    =========================================================================== -/

/-- **规则族在属性集上的满足（语法侧）**。

`Satisfies K S Sig` 意为：`Sig` 中的**每条**蕴含 `X ⇒ Y`，
只要其左部 `X` 已包含于 `S`，其右部 `Y` 也包含于 `S`。

即 `S` 是 `Sig` 的一步闭合点（见 `synClosureOne_eq_self_of_satisfies`）。

**为何用语法侧而非 `K.Models`**：`K.Models A B` 是对**形式背景**的
语义陈述，与集合 `S` 无关，对它谈「扩展后仍满足」是空话。
半朴素化关心的是「一步闭包算子是否把规则用尽」，
这正是关于「规则左部/右部 vs 集合」的包含关系。 -/
def Satisfies (S : Set K.MFCA) (Sig : Set (Set K.MFCA × Set K.MFCA)) : Prop :=
  ∀ X Y : Set K.MFCA, (X, Y) ∈ Sig → X ⊆ S → Y ⊆ S

/-- **满足性的等价刻画（逐元素形式）**：便于与其他引理对接。 -/
theorem satisfies_iff {S : Set K.MFCA} {Sig : Set (Set K.MFCA × Set K.MFCA)} :
    K.Satisfies S Sig ↔
      ∀ X Y : Set K.MFCA, (X, Y) ∈ Sig → X ⊆ S → ∀ m ∈ Y, m ∈ S :=
  Iff.rfl

/-- ⭐⭐⭐ **【反例：`Satisfies` 对集合参数不单调】**

任务书要求证明

    S ⊆ T → Satisfies S Sig → Satisfies T Sig

**该陈述为假**。本定理给出形式化的反例：
只需属性集里有**两个不同**元素 `a ≠ b`，取
`Sig = {({a}, {b})}`、`S = ∅`、`T = {a}`，则
* `Satisfies S Sig` 成立（唯一规则左部 `{a} ⊄ ∅`，前件为空）；
* `Satisfies T Sig` **不**成立（`{a} ⊆ {a}`，但 `{b} ⊄ {a}`）。

**故 `satisfies_mono_of_subset` 不可证，本文件不陈述它**（按纪律）。
唯一需要的单调性在 §2：一步闭包算子对**起点**单调（`synClosureOne_mono`），
它才是半朴素化的正确性前提。

**前件说明**：`a ≠ b` 是不可去除的——若 `K.MFCA` 至多一个元素，
单调性反而平凡成立。故这是一个**条件性不可能性结果**（对任何
含至少两个属性的背景，原陈述都被证伪）。 -/
theorem not_satisfies_mono_of_subset (a b : K.MFCA) (hab : a ≠ b)
    (Sig : Set (Set K.MFCA × Set K.MFCA))
    (hSig : Sig = {(({a} : Set K.MFCA), ({b} : Set K.MFCA))}) :
    K.Satisfies (∅ : Set K.MFCA) Sig ∧ ¬ K.Satisfies ({a} : Set K.MFCA) Sig := by
  have key : ∀ X Y : Set K.MFCA, (X, Y) ∈ Sig → X = {a} ∧ Y = {b} := by
    intro X Y hXY
    rw [hSig] at hXY
    simpa using hXY
  constructor
  · intro X Y hXY hX
    obtain ⟨rfl, _⟩ := key X Y hXY
    exact absurd (hX (Set.mem_singleton a) : a ∈ (∅ : Set K.MFCA)) (Set.notMem_empty a)
  · intro hT
    have hmem : (({a} : Set K.MFCA), ({b} : Set K.MFCA)) ∈ Sig := by rw [hSig]; simp
    have hbT : b ∈ ({a} : Set K.MFCA) :=
      hT {a} {b} hmem (fun m hm => by simpa using hm) (Set.mem_singleton b)
    exact hab (by simpa using hbT.symm)

/-! ===========================================================================
    §2  一步闭包关于起点的单调性（半朴素化的核心正确性引理）
    =========================================================================== -/

/-- ⭐⭐⭐ **【一步闭包关于起点单调】**

$$S\subseteq T\ \Longrightarrow\ \mathrm{synClosureOne}\,\Sigma\,S
  \subseteq\ \mathrm{synClosureOne}\,\Sigma\,T$$

**证明**：`synClosureOne Sig S = S ∪ ⋃{Y | (X,Y)∈Sig, X⊆S}`。
* 旧部分：`m ∈ S ⊆ T ⊆ synClosureOne Sig T`（扩张性）；
* 新部分：`m ∈ Y` 且 `(X,Y) ∈ Sig`、`X ⊆ S`，则 `X ⊆ S ⊆ T`，
  故 `m` 也落在 `synClosureOne Sig T` 的第二项中（同一条规则、更强前件）。

**这是半朴素化的核心**：先在小集合上把规则用完，扩展到更大集合后，
**旧的推导结果一个不少地仍在新的闭包里**——故算法无需重算旧规则。∎ -/
theorem synClosureOne_mono {S T : Set K.MFCA} (h : S ⊆ T)
    (Sig : Set (Set K.MFCA × Set K.MFCA)) :
    K.synClosureOne Sig S ⊆ K.synClosureOne Sig T := by
  rintro m (hm | ⟨X, Y, hXY, hX, hmY⟩)
  · exact Set.mem_union_left _ (h hm)
  · exact Set.mem_union_right _ ⟨X, Y, hXY, fun m' hm' => h (hX hm'), hmY⟩

/-! ===========================================================================
    §3  迭代闭包关于起点的单调性
    =========================================================================== -/

/-- ⭐⭐ **【闭包迭代关于起点单调】**

$$S\subseteq T\ \Longrightarrow\ \forall n,\ \Sigma^n(S)\subseteq\Sigma^n(T)$$

**注意命名**：`Implication.lean` 已有的 `synClosureIter_mono` 是
**关于步数**单调（`m ≤ n → Sigma^m ⊆ Sigma^n`），与本题的
**关于起点**单调（`S ⊆ T → Sigma^n S ⊆ Sigma^n T`）是两条不同定理，
故此处用 `_subset_mono` 以免撞名混淆。

**证明**：对 `n` 归纳。零步即 `h`；步进用 `synClosureOne_mono` 推进。∎ -/
theorem synClosureIter_subset_mono {S T : Set K.MFCA} (h : S ⊆ T)
    (Sig : Set (Set K.MFCA × Set K.MFCA)) :
    ∀ n : ℕ, K.synClosureIter Sig n S ⊆ K.synClosureIter Sig n T := by
  intro n
  induction n with
  | zero => rw [K.synClosureIter_zero, K.synClosureIter_zero]; exact h
  | succ k ih =>
      rw [K.synClosureIter_succ, K.synClosureIter_succ]
      exact K.synClosureOne_mono ih Sig

/-- ⭐⭐ **【旧的一步闭包结果在扩展后仍被新迭代包含】**（半朴素化「不丢结论」）

若 `S ⊆ T`，则 `synClosureOne Sig S ⊆ synClosureIter Sig 1 T`。

**意义**：算法先在 `S` 上算出一步闭包（用掉部分规则），
随后把结果并入工作集 `T`；本引理保证**那一步的结果全部保留在
`T` 的下一轮迭代里**，即「已算过的不会被丢掉」。
**证明**：`synClosureOne_mono h` 给出 `synClosureOne Sig S ⊆ synClosureOne Sig T`，
再用 `synClosureIter_succ` + `synClosureIter_zero` 把右边识别为 `Sigma^1 T`。∎ -/
theorem synClosureOne_subset_synClosureIter_succ {S T : Set K.MFCA} (h : S ⊆ T)
    (Sig : Set (Set K.MFCA × Set K.MFCA)) :
    K.synClosureOne Sig S ⊆ K.synClosureIter Sig 1 T := by
  have h1 : K.synClosureOne Sig S ⊆ K.synClosureOne Sig T :=
    K.synClosureOne_mono h Sig
  have h2 : K.synClosureIter Sig 1 T = K.synClosureOne Sig T := by
    rw [K.synClosureIter_succ, K.synClosureIter_zero]
  rw [h2]
  exact h1

/-! ===========================================================================
    §4  满足性与闭包不动点（半朴素化的「停止」判据）
    =========================================================================== -/

/-- ⭐⭐⭐ **【规则已被满足 ⇒ 一步闭包不动】**

若 `B` 满足 `Sig`，则 `synClosureOne Sig B = B`：一步闭包不再增加元素。

**证明**：`⊆` 方向：`synClosureOne Sig B` 的两项各自落入 `B`
（旧部分平凡；新部分正是 `Satisfies` 的内容）；
`⊇` 方向是 `subset_synClosureOne`。∎ -/
theorem synClosureOne_eq_self_of_satisfies {B : Set K.MFCA}
    {Sig : Set (Set K.MFCA × Set K.MFCA)} (h : K.Satisfies B Sig) :
    K.synClosureOne Sig B = B := by
  refine Set.Subset.antisymm ?_ (K.subset_synClosureOne Sig B)
  rintro m (hm | ⟨X, Y, hXY, hX, hmY⟩)
  · exact hm
  · exact h X Y hXY hX hmY

/-- ⭐⭐⭐ **【规则已被满足 ⇒ 迭代可以停】**

若 `S` 满足 `Sig`，则对一切 `n`，`Sigma^(n+1)(S) = S`：
继续迭代**不会**产生新元素。

**这是半朴素化「停止」的正确性**：一旦算法确认当前集合满足全部规则，
停机是正确的。

**证明**：对 `n` 归纳。零步即 `synClosureOne_eq_self_of_satisfies`；
步进用归纳假设 `Sigma^(k+1) S = S` 把目标换成
`synClosureOne Sig S = S`，再用同一条引理。∎ -/
theorem synClosureIter_eq_self_of_satisfies {S : Set K.MFCA}
    {Sig : Set (Set K.MFCA × Set K.MFCA)} (h : K.Satisfies S Sig) :
    ∀ n : ℕ, K.synClosureIter Sig (n + 1) S = S := by
  intro n
  induction n with
  | zero =>
      rw [K.synClosureIter_succ, K.synClosureIter_zero]
      exact K.synClosureOne_eq_self_of_satisfies h
  | succ k ih =>
      rw [K.synClosureIter_succ, ih]
      exact K.synClosureOne_eq_self_of_satisfies h

/-- **满足性在迭代下自动保持**：`S` 满足 `Sig` ⇒ `Sigma^n S` 也满足。

**证明**：零步即假设；步进时 `Sigma^(k+1) S = Sigma^k S`（由
`synClosureIter_eq_self_of_satisfies` 的形式转换），故仍是 `S`。∎ -/
theorem synClosureIter_satisfies {S : Set K.MFCA}
    {Sig : Set (Set K.MFCA × Set K.MFCA)} (h : K.Satisfies S Sig) :
    ∀ n : ℕ, K.Satisfies (K.synClosureIter Sig n S) Sig := by
  intro n
  induction n with
  | zero => rw [K.synClosureIter_zero]; exact h
  | succ k ih =>
      rw [K.synClosureIter_succ]
      -- Sigma^k S 满足 ⇒ 一步闭包不动 ⇒ Sigma^(k+1) S = Sigma^k S
      have hk : K.Satisfies (K.synClosureIter Sig k S) Sig := ih
      have heq : K.synClosureOne Sig (K.synClosureIter Sig k S)
          = K.synClosureIter Sig k S :=
        K.synClosureOne_eq_self_of_satisfies hk
      rw [heq]
      exact ih

end FormalCtx

end Fate
