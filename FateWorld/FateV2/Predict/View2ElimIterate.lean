/-
# 「图 ⟹ 概率」桥 · **视角 2：完全变量消元（Variable Elimination）**

## 0 定位与本文件的增量

策略 2 的思想：**不比两种 `mass`，而是把 `mass` 算到底**。
库里已有两份策略 2 的资产：

| 文件 | 内容 | 状态 |
|---|---|---|
| `Fate/BridgeView2Elimination.lean` | 单步引擎（`peel` / `sink_elim_law` / `sink_marginal_constant`），`univ ∖ {v}` 口径 | ✅ 编译 |
| `Fate/BridgeStrategy2Elimination.lean` | 单步引擎（`elim_peel`）`insert v S` 口径 + 声称的 `elim_iterate` | ❌ **`elim_iterate` 是 `sorry`，整文件不进构建图** |

**本文件补的正是那一格**：把单步 `elim_peel` **真正迭代完**，得到

$$\mathrm{mass}\,(S\cup L)\Bigl(\prod_u\varphi_u\Bigr)x
  =\Bigl(\prod_{v\in L}\varphi_v(x)\Bigr)\cdot \mathrm{mass}\,S\,\Bigl(\prod_u\varphi_u\Bigr)x
\qquad(\text{任意 } L,\ S\ \text{与 }L\text{ 不交}),$$

并给出**它的图侧实例**：`L` 是一层「上方切片」（`L` 内无边、`L` 到 `L` 外无边）
⟹ 前提全满足。最后把它接到 `LMGc` 与 `dSep` 的分解记账上，**说清策略 2 到底走到了哪一步**。

## 1 硬约束：不用 `mass` 塔（已证伪）

| 事实 | 出处 |
|---|---|
| `mass S (mass T p) x ≠ mass (S∪T) p x` 一般为假 | `Fate.DAGFactorizationGeneral.tower_property_false`（T24）|
| 连 `S ⊆ T` 方向的塔也假（`mass` 非归一化）| `Fate/TowerAudit.lean` A3 `mass_idempotent_fails` |

**本文件一次也不出现 `mass S (mass T p)`**。允许的两条工具：
* `mass_mul`（`f` 只读 `S` ⟹ 可从 `mass S` 里提出来）；
* `mass_insert_sum'`（**一次**求和：`mass S p x = ∑_a mass (insert v S) p (x_v:=a)`）。

## 2 数学内容（三步）

**步 1（单点消元，`elim_peel'`）。** 设 `p = ∏_u φ_u`，`v ∉ S`，
* `φ_v` 在 `insert v S`-纤维上为常数（读集 ⊆ `{v}∪S`）；
* 其余**每一个** `φ_w`（`w ≠ v`）都不读 `x_v`；
* `φ_v` 归一：`∑_a φ_v(x_v{:=}a) = 1`（对一切 `x`）。

则 `mass (insert v S) p x = φ_v(x) · mass S p x`。
（证：`mass_mul` 提出 `φ_v` → 对残因子 `v`-盲用**纤维重指标化** →
`mass_insert_sum'` 一次展开 → `FactorNorm` 塌缩。）

**步 2（迭代，`elim_iterate'`）。** 若 `L` 满足
$$\mathrm{ElimReads}(L,\varphi):=\forall v\in L,\ \forall w\neq v,\ \varphi_w\ \text{不读}\ x_v,$$
则对任意 `Disjoint S L`：
`mass (S ∪ L) p x = (∏_{v∈L} φ_v x) · mass S p x`。
（对 `L` 做 `Finset.induction`：`S ∪ insert v L' = insert v (S ∪ L')`，
`ElimReads L` 恰好给出步 1 的两条读集前提，`ElimReads L'` 由单调性继承。）

**步 3（图侧，`topSlice_elimReads`）。** `ElimReads` 的两半在图上的充分条件：
* `∀ w ≠ v, v ∉ pa_G(w)`（**`v` 的出边只在 `L` 内**）⟹ `φ_w` 不读 `v`（`LocalTo`）；
* `L` 内部无边 ⟹ 对 `v, w ∈ L`（`w ≠ v`）同样成立。

⟹ **`L` = 一层「上方切片」（sink 层）**。这就是策略 2 消费图结构的**唯一位置**：
「谁读 `x_v`」。

## 3 诚实边界（§7 详述）

策略 2 到此为止给出的是**「`mass` 显式化」**，它是 `GlobalMarkov` 的**充分**基础设施，
但**不等于** `dSep ⟹ CondMul`：后者还需要
(a) 把 `dSep` 归约到 `an(X∪Y∪Z)` 上的分解（Bayes-ball 不可达 ⟹ 交叉项恒常性），
(b) 沿拓扑序把 (a) 的交叉项**逐个**用本文件的 `elim_iterate'` 消掉。
(b) 本文件已备；**(a) 未落地**，在 §7 精确登记。

**零 `sorry` / 零 `axiom` / 零 `Prop` 占位。**
-/

import FateWorld.FateV2.Predict.BridgeView2Elimination
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace FateV2.Predict.View2ElimIterate

open FateV2.Modeling

set_option linter.unusedSectionVars false

open Finset Fate.DAGFactorization FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · View2ElimIterate

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View2ElimIterate.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeView2Elimination
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 基底：`unpin` 一致性与「不读」谓词
  =========================================================================== -/

section Substrate

/-- ⭐ **`unpin v x a` 在 `S` 上与 `x` 一致**（`v ∉ S`）。 -/
theorem unpin_agree (v : V) {S : Finset V} (hvS : v ∉ S) (x : V → α) (a : α) :
    ∀ u ∈ S, unpin v x a u = x u := by
  intro u hu
  have hne : u ≠ v := by rintro rfl; exact hvS hu
  simp only [unpin, if_neg hne]

/-- ⭐⭐ **「不读 `v` 位」**：函数的取值不受第 `v` 个坐标影响。

**这是策略 2 中图侧信息的唯一落点**（见 §3 的 `blind_of_not_mem_pa`）。 -/
def BlindAt (v : V) (g : (V → α) → ℝ) : Prop :=
  ∀ a b : V → α, (∀ u ∈ (Finset.univ \ {v} : Finset V), a u = b u) → g a = g b

/-- ⭐ **`BlindAt` 的直接用法**：`g` 不读 `v` ⟹ `g (unpin v x a) = g x`。 -/
theorem BlindAt.apply_unpin (v : V) {g : (V → α) → ℝ} (h : BlindAt v g)
    (x : V → α) (a : α) : g (unpin v x a) = g x :=
  h _ _ (fun u hu => by
    rw [mem_sdiff, mem_singleton] at hu
    simp only [Fate.DAGFactorization.unpin]
    rw [if_neg hu.2])

/-- ⭐ **`mass` 的纤维集写法**（把 `if` 换成 `filter`，便于做双射）。 -/
theorem mass_eq_sum_filter (S : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    mass S p x = ∑ w ∈ (Finset.univ.filter fun w => ∀ u ∈ S, w u = x u), p w := by
  unfold mass
  rw [Finset.sum_filter]

/-- ⭐ **`insert v S`-纤维 = `S`-纤维 ∩ `{· v = y v}`**。 -/
theorem filter_insert_eq (v : V) (S : Finset V) (y : V → α) :
    (Finset.univ.filter fun w : V → α => ∀ u ∈ insert v S, w u = y u)
      = (Finset.univ.filter fun w : V → α => (∀ u ∈ S, w u = y u) ∧ w v = y v) := by
  refine Finset.filter_congr fun w _ => ?_
  constructor
  · intro h; exact ⟨fun u hu => h u (mem_insert_of_mem hu), h v (mem_insert_self v S)⟩
  · intro ⟨h1, h2⟩ u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact h2
    · exact h1 u hu

/-- ⭐⭐⭐ **`mass_insert_of_blind`（纤维重指标化：策略 2 的第二步）**：

$$\mathrm{mass}\,(\mathrm{insert}\,v\,S)\,g\,y=\mathrm{mass}\,(\mathrm{insert}\,v\,S)\,g\,x
\qquad(y|_S = x|_S,\ v\notin S,\ g\ \text{不读}\ v).$$

**⚠ 这是**一次**`mass` 的重指标化，不是塔**：证明把两个纤维都写成
`S`-纤维 `∩ {· v = ·}`，再用 `w ↦ Function.update w v (x v)` 构造双射
（逆 `w ↦ Function.update w v (y v)`）；`g` 在该双射下不变（只改了 `v` 一位）。 -/
theorem mass_insert_of_blind (v : V) {S : Finset V} (hvS : v ∉ S)
    {g : (V → α) → ℝ} (hg : BlindAt v g) {y x : V → α} (hxy : ∀ u ∈ S, y u = x u) :
    mass (insert v S) g y = mass (insert v S) g x := by
  rw [mass_eq_sum_filter, mass_eq_sum_filter, filter_insert_eq, filter_insert_eq]
  refine Finset.sum_nbij' (fun w => Function.update w v (x v))
    (fun w => Function.update w v (y v)) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    refine ⟨fun u hu => ?_, Function.update_self v (x v) w⟩
    rw [Function.update_of_ne (by rintro rfl; exact hvS hu)]
    rw [hw.1 u hu, hxy u hu]
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    refine ⟨fun u hu => ?_, Function.update_self v (y v) w⟩
    rw [Function.update_of_ne (by rintro rfl; exact hvS hu)]
    rw [hw.1 u hu, hxy u hu]
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    ext j
    by_cases hj : j = v
    · subst hj; simp only [Function.update_self]; exact ha.2.symm
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    ext j
    by_cases hj : j = v
    · subst hj; simp only [Function.update_self]; exact hb.2.symm
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  · intro a ha
    exact hg _ _ (fun u hu => by
      rw [mem_sdiff, mem_singleton] at hu
      rw [Function.update_of_ne hu.2])

end Substrate

/-! ===========================================================================
  §2 ⭐⭐⭐⭐⭐ **单点消元与迭代（策略 2 的核心引擎）**
  =========================================================================== -/

section Engine

/-- ⭐⭐⭐⭐ **`elim_peel'`（单点消元，`insert v S` 口径）。**

设 `p = ∏_u φ_u`，`v ∉ S`，且
* `φ_v` 读 `insert v S`；
* 其余每个 `φ_w`（`w ≠ v`）都 `v`-盲；
* `φ_v` 归一：`∑_a φ_v (x_v{:=}a) = 1`；

则 `mass (insert v S) p x = φ_v(x) · mass S p x`。

**证明三步，全程无 `mass` 嵌套：**
1. `mass_mul`：`φ_v` 只读 `insert v S` ⟹ 提到 `mass` 外面；
2. `BlindAt.apply_unpin` + `mass_insert_of_blind`：残因子 `v`-盲 ⟹ 各纤维上质量相同；
3. `mass_insert_sum'` **一次**求和 + 归一常量 `∑_a φ_v = 1` ⟹ 乘子塌缩为 `1`。
-/
theorem elim_peel' (φ : V → (V → α) → ℝ) (v : V) {S : Finset V} (hvS : v ∉ S)
    (hreadv : ∀ a b : V → α, (∀ u ∈ insert v S, a u = b u) → φ v a = φ v b)
    (hblind : ∀ w, w ≠ v → BlindAt v (φ w))
    (hnorm : ∀ x : V → α, (∑ a : α, φ v (unpin v x a)) = 1) (x : V → α) :
    mass (insert v S) (fun z => ∏ u, φ u z) x
      = φ v x * mass S (fun z => ∏ u, φ u z) x := by
  -- 残因子（`v` 之外的全部因子之积）
  set g : (V → α) → ℝ := fun z => ∏ u ∈ (Finset.univ \ {v} : Finset V), φ u z with hg_def
  -- `g` 是 `v`-盲的（每个因子都 `v`-盲）
  have hgb : BlindAt v g := by
    intro a b hab
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [mem_sdiff, mem_singleton] at hw
    exact hblind w hw.2 a b hab
  -- 乘积拆分：`p = φ_v · g`
  have hsplit : ∀ z : V → α, (∏ u, φ u z) = φ v z * g z := by
    intro z
    have h := Finset.prod_erase_mul (Finset.univ : Finset V) (fun u => φ u z)
      (Finset.mem_univ v)
    have hgg : g z = ∏ u ∈ (Finset.univ.erase v : Finset V), φ u z := by
      simp only [hg_def, Finset.sdiff_singleton_eq_erase]
    rw [hgg, ← h, mul_comm]
  -- 第一步：`mass (insert v S) p x = φ_v x · mass (insert v S) g x`
  have hstep1 : mass (insert v S) (fun z => ∏ u, φ u z) x
      = φ v x * mass (insert v S) g x := by
    rw [show (fun z => ∏ u, φ u z) = (fun z => φ v z * g z) from funext hsplit]
    exact mass_mul _ _ _ _ hreadv
  -- 第二步：各纤维质量相同
  have hstep2 : ∀ a : α, mass (insert v S) (fun z => ∏ u, φ u z) (unpin v x a)
      = φ v (unpin v x a) * mass (insert v S) g x := by
    intro a
    rw [show (fun z => ∏ u, φ u z) = (fun z => φ v z * g z) from funext hsplit,
      mass_mul _ _ _ _ hreadv]
    congr 1
    exact mass_insert_of_blind v hvS hgb (unpin_agree v hvS x a)
  -- 第三步：一次求和 + 归一塌缩
  rw [hstep1, mass_insert_sum' v S hvS (fun z => ∏ u, φ u z) x,
    Finset.sum_congr rfl fun a _ => hstep2 a, ← Finset.sum_mul, hnorm x, one_mul]

/-- ⭐⭐⭐ **`ElimReads L φ`：`L` 中的点「只被自己的因子读」。**

$$\mathrm{ElimReads}(L,\varphi):=\forall v\in L,\ \forall w\neq v,\
  \varphi_w\ \text{不读}\ x_v.$$

**这是策略 2 的图侧入口**：§3 证明「`L` 是上方切片」⟹ `ElimReads L φ`。 -/
def ElimReads (L : Finset V) (φ : V → (V → α) → ℝ) : Prop :=
  ∀ (v : V) (hv : v ∈ L) (w : V) (hw : w ≠ v), BlindAt v (φ w)

/-- ⭐ **`ElimReads` 对子集单调**（迭代的继承前提）。 -/
theorem ElimReads.mono {L L' : Finset V} {φ : V → (V → α) → ℝ}
    (hL' : L' ⊆ L) (h : ElimReads L φ) : ElimReads L' φ :=
  fun v hv w hw => h v (hL' hv) w hw

/-- ⭐⭐ **`MutualBlind L φ`：`L` 内的因子**互不读取**对方的坐标。**

$$\mathrm{MutualBlind}(L,\varphi):=\forall v\in L,\ \forall w\in L,\ w\neq v,\
  \varphi_v\ \text{不读}\ x_w.$$

**这是「同时消掉一整层」的精确前提**（与 `ElimReads` 合起来就是：`L` 内每个因子
只读 `{自己} ∪ L` 以外的坐标）。 -/
def MutualBlind (L : Finset V) (φ : V → (V → α) → ℝ) : Prop :=
  ∀ (v : V) (hv : v ∈ L) (w : V) (hw : w ∈ L) (hvw : w ≠ v), BlindAt w (φ v)

/-- ⭐ **`MutualBlind` 对子集单调**。 -/
theorem MutualBlind.mono {L L' : Finset V} {φ : V → (V → α) → ℝ}
    (hL' : L' ⊆ L) (h : MutualBlind L φ) : MutualBlind L' φ :=
  fun v hv w hw hvw => h v (hL' hv) w (hL' hw) hvw

/-- ⭐⭐⭐⭐ **`ReadsSub R g`：`g` 的读集 ⊆ `R`**（对 `R` 外坐标不敏感）。 -/
def ReadsSub (R : Finset V) (g : (V → α) → ℝ) : Prop :=
  ∀ a b : V → α, (∀ u ∈ R, a u = b u) → g a = g b

/-- ⭐⭐ **`BlindAt` 即 `ReadsSub (univ \\ {v})`**（两种口径的接口）。 -/
theorem readsSub_univ_sdiff_iff (v : V) (g : (V → α) → ℝ) :
    ReadsSub (Finset.univ \ {v} : Finset V) g ↔ BlindAt v g := by
  constructor
  · intro h a b hab
    exact h a b (fun u hu => hab u hu)
  · intro h a b hab
    exact h a b (fun u hu => hab u hu)

/-- ⭐⭐⭐⭐⭐ **`readsSub_of_blind`（读集拼装）：逐点盲 ⟹ 读集受限。**

若 `g` 对 `R` 外的**每一个**坐标都盲，则 `g` 的读集 ⊆ `R`。

**证明**：对补集 `D = univ \ R` 做归纳。取 `c ∈ D`，令 `R' = insert c R`。
给定 `u|_{R} = v|_{R}`，取 `u' := Function.update u c (v c)`，
则 `u'|_{R'} = v|_{R'}`（由归纳假设得 `g u' = g v`），
而 `g u = g u'`（由 `BlindAt c g`，两者只在 `c` 位不同）。 -/
theorem readsSub_of_blind {R : Finset V} {g : (V → α) → ℝ}
    (h : ∀ w, w ∉ R → BlindAt w g) : ReadsSub R g := by
  classical
  set D : Finset V := Finset.univ \ R with hD
  have hRD : R = Finset.univ \ D := by
    rw [hD, Finset.sdiff_sdiff_eq_self]
    exact fun u _ => mem_univ u
  have key : ∀ D' : Finset V, D' ⊆ D →
      ReadsSub (Finset.univ \ D') g := by
    intro D'
    induction D' using Finset.induction_on with
    | empty =>
      intro _ a b hab
      have : a = b := by
        funext u; exact hab u (by simp)
      rw [this]
    | insert c T hc ihT =>
      intro hsub a b hab
      have hcD : c ∈ D := hsub (mem_insert_self c T)
      have hcR : c ∉ R := (Finset.mem_sdiff.mp (hD ▸ hcD)).2
      -- `g` 对 `c` 位盲
      have hblind : BlindAt c g := h c hcR
      -- `a'`：把 `a` 的 `c` 位换成 `b c`
      set a' : V → α := Function.update a c (b c) with ha'
      have hstep1 : g a = g a' :=
        hblind a a' (fun u hu => by
          rw [Finset.mem_sdiff, mem_singleton] at hu
          rw [ha', Function.update_of_ne hu.2])
      have hstep2 : g a' = g b := by
        refine ihT (fun x hx => hsub (mem_insert_of_mem hx)) a' b ?_
        intro u hu
        have huT : u ∉ T := (Finset.mem_sdiff.mp hu).2
        rw [ha']
        by_cases huc : u = c
        · subst huc; rw [Function.update_self]
        · rw [Function.update_of_ne huc]
          -- `u ∉ insert c T`，故 `hab` 在此适用
          exact hab u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, by
            intro hmem
            rcases Finset.mem_insert.mp hmem with he | hT
            · exact huc he
            · exact huT hT⟩)
      rw [hstep1, hstep2]
  intro a b hab
  exact key D (fun _ hx => hx) a b (fun u hu => hab u (hRD ▸ hu))

/-- ⭐⭐⭐⭐⭐ **`elim_iterate'`（策略 2 的迭代消元 —— 本文件的主定理）**。

设 `p = ∏_u φ_u`，`L` 是**被消元的一层**（上方切片），`S` 是**底层**，满足

* **`L` 之外全在 `S` 里**：`∀ v ∉ L, v ∈ S`（记作 `Lᶜ ⊆ S`）—— 这就是「`L` 是最上面一层」；
* `ElimReads L φ`：`L` 内每点的坐标，除自己的因子外没有因子读它；
* `MutualBlind L φ`：`L` 内的因子互不读取；
* `hnorm`：`L` 上每个 `φ_v` 归一。

则

$$\boxed{\ \mathrm{mass}\,(S\cup L)\Bigl(\prod_u\varphi_u\Bigr)x
  =\Bigl(\prod_{v\in L}\varphi_v(x)\Bigr)\cdot\mathrm{mass}\,S\,\Bigl(\prod_u\varphi_u\Bigr)x\ }$$

**⟹ 这是「把 `mass` 算到底」的迭代形态**：`mass (S∪L)` 被显式化成
「`L` 上的乘积 × 底层 `mass S`」，`L` 中的点**全部被消掉**。
（`Fate/BridgeStrategy2Elimination.lean` 中同一格的 `elim_iterate` 是 `sorry`；此处补完。）

**⚠ `Lᶜ ⊆ S` 不是废话**：它等价于 `S ⊔ L = univ`，即 `S` 与 `L` 一起覆盖全图。
没有它，「`L` 内因子只读 `{自己} ∪ Lᶜ ⊆ {自己} ∪ S`」不成立，单步前提 `hreada` 无法满足。

**证明**：对 `L` 做 `Finset.induction_on`，取 `v ∈ L`：
1. 令 `T := S ∪ (L ∖ {v})`。由 `Lᶜ ⊆ S` 与 `MutualBlind`，`φ_v` 的读集
   `⊆ {v} ∪ Lᶜ ∪ (L∖{v}) = insert v T`；
2. `ElimReads L` 给出「其余因子 `v`-盲」；
3. `elim_peel'` ⟹ `mass (insert v T) p x = φ_v x · mass T p x`；
4. `L ∖ {v}` 上归纳假设（前提在子集下继承）用完，`prod_insert` 收口。 -/
theorem elim_iterate' (φ : V → (V → α) → ℝ) {S L : Finset V}
    (hSL : Disjoint S L) (hcover : ∀ v, v ∉ L → v ∈ S)
    (hreads : ElimReads L φ) (hmut : MutualBlind L φ)
    (hnorm : ∀ v ∈ L, ∀ x : V → α, (∑ a : α, φ v (unpin v x a)) = 1) :
    ∀ x : V → α,
      mass (S ∪ L) (fun z => ∏ u, φ u z) x
        = (∏ v ∈ L, φ v x) * mass S (fun z => ∏ u, φ u z) x := by
  classical
  induction L using Finset.induction_on generalizing S with
  | empty => simp
  | insert a s ha ih =>
    intro x
    -- `a ∉ S`
    have haS : a ∉ S := fun h =>
      (Finset.disjoint_left.mp hSL h (Finset.mem_insert_self a s))
    -- **`φ a` 的读集 ⊆ `insert a S`**：`s` 内的点由 `MutualBlind` 盲，其余由覆盖 `Lᶜ ⊆ S`
    have hreada : ∀ a' b' : V → α, (∀ u ∈ insert a S, a' u = b' u) →
        φ a a' = φ a b' := by
      refine readsSub_of_blind (R := insert a S) (g := φ a) ?_
      intro w hw
      have hwa : w ≠ a := fun h => hw (h ▸ Finset.mem_insert_self a S)
      have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
      by_cases hws : w ∈ s
      · exact hmut a (Finset.mem_insert_self a s) w (Finset.mem_insert_of_mem hws)
          (fun h => ha (h ▸ hws))
      · refine absurd (hcover w ?_) hwS
        intro hmem
        rcases Finset.mem_insert.mp hmem with he | hT
        · exact hwa he
        · exact hws hT
    have hblinda : ∀ w, w ≠ a → BlindAt a (φ w) :=
      hreads a (Finset.mem_insert_self a s)
    -- `S ∪ insert a s = insert a (S ∪ s)`
    have hset : S ∪ insert a s = insert a (S ∪ s) := by
      ext u; simp only [mem_union, mem_insert]; tauto
    -- **先对 `s` 用归纳假设（底座 `S' := S ∪ {a}`），最后才消掉 `a`（底座 `S`）**
    have hcover' : ∀ v, v ∉ s → v ∈ S ∪ {a} := by
      intro v hv
      rw [mem_union, mem_singleton]
      by_cases hva : v = a
      · exact Or.inr hva
      · exact Or.inl (hcover v (fun h => by
          rcases Finset.mem_insert.mp h with he | hT
          · exact hva he
          · exact hv hT))
    have hSdisj : Disjoint (S ∪ {a}) s := by
      rw [Finset.disjoint_union_left]
      exact ⟨hSL.mono_right (Finset.subset_insert a s),
        Finset.disjoint_singleton_left.mpr ha⟩
    have hih := ih hSdisj hcover'
      (hreads.mono (Finset.subset_insert a s))
      (hmut.mono (Finset.subset_insert a s))
      (fun v hv => hnorm v (Finset.mem_insert_of_mem hv)) x
    have hunion : (S ∪ {a}) ∪ s = insert a (S ∪ s) := by
      ext u; simp only [mem_union, mem_singleton, mem_insert]; tauto
    rw [hunion, ← hset] at hih
    rw [hih]
    -- **最后消掉 `a`**：底座为 `S`
    have hsing : S ∪ {a} = insert a S := by
      ext u; simp only [mem_union, mem_singleton, mem_insert]; tauto
    have hpeel := elim_peel' φ a haS hreada hblinda
      (hnorm a (Finset.mem_insert_self a s)) x
    rw [hsing, hpeel, Finset.prod_insert ha]
    ring

/-- ⭐⭐⭐⭐ **`elim_iterate_reads`（读集口径的迭代消元；不需要 `Lᶜ ⊆ S`）**。

`elim_iterate'` 要 `Lᶜ ⊆ S`，是因为它的单步前提「`φ_a` 的读集 ⊆ `insert a (S ∪ L∖{a})`」
只能靠覆盖条件 `Lᶜ ⊆ S` 拼出来。图侧的 `topSlice_elim` 手上有**直接**的读集信息：
`hreadL : ∀ v ∈ L, ReadsSub (S ∪ L) (φ v)` —— 而
`S ∪ L = insert a (S ∪ (L∖{a}))`，所以单步前提**直接成立**，无需覆盖假设。

（「其余因子 `a`-盲」仍由 `ElimReads L` 提供，与 `elim_iterate'` 一致。） -/
theorem elim_iterate_reads (φ : V → (V → α) → ℝ) {S L : Finset V}
    (hSL : Disjoint S L)
    (hreads : ElimReads L φ)
    (hreadL : ∀ v ∈ L, ReadsSub (S ∪ L) (φ v))
    (hnorm : ∀ v ∈ L, ∀ x : V → α, (∑ a : α, φ v (unpin v x a)) = 1) :
    ∀ x : V → α,
      mass (S ∪ L) (fun z => ∏ u, φ u z) x
        = (∏ v ∈ L, φ v x) * mass S (fun z => ∏ u, φ u z) x := by
  classical
  induction L using Finset.induction_on generalizing S with
  | empty => simp
  | insert a s ha ih =>
    intro x
    have haS : a ∉ S := fun h =>
      (Finset.disjoint_left.mp hSL h (Finset.mem_insert_self a s))
    -- **归纳假设作用在 `S' := S ∪ {a}` 上**；此时读集仍是同一个 `S ∪ insert a s`
    have hSdisj : Disjoint (S ∪ {a}) s := by
      rw [Finset.disjoint_union_left]
      exact ⟨hSL.mono_right (Finset.subset_insert a s),
        Finset.disjoint_singleton_left.mpr ha⟩
    have hunion : (S ∪ {a}) ∪ s = S ∪ insert a s := by
      ext u; simp only [mem_union, mem_singleton, mem_insert]; tauto
    have hread' : ∀ v ∈ s, ReadsSub ((S ∪ {a}) ∪ s) (φ v) := by
      intro v hv; rw [hunion]
      exact hreadL v (Finset.mem_insert_of_mem hv)
    have hih := ih hSdisj
      (hreads.mono (Finset.subset_insert a s)) hread'
      (fun v hv => hnorm v (Finset.mem_insert_of_mem hv)) x
    rw [hunion] at hih
    rw [hih]
    -- **`φ a` 的读集 ⊆ `insert a S`**：
    -- `hreadL` 只给 `ReadsSub (S ∪ insert a s)`，还需 `ElimReads` 给出对 `s` 各点的盲，
    -- 二者拼出「`φ a` 不读 `s`」。
    have hreada : ∀ a' b' : V → α, (∀ u ∈ insert a S, a' u = b' u) →
        φ a a' = φ a b' := by
      refine readsSub_of_blind (R := insert a S) (g := φ a) ?_
      intro w hw
      by_cases hws : w ∈ s
      · -- `φ a` 对 `w ∈ s` 盲（`ElimReads`；`a ∉ s` ⟹ `a ≠ w`）
        exact hreads w (Finset.mem_insert_of_mem hws) a (fun h => ha (h.symm ▸ hws))
      · -- `w ∉ S ∪ insert a s`：`ReadsSub (S ∪ insert a s)` 的两步搬运
        have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
        have hwa : w ≠ a := fun h => hw (h ▸ Finset.mem_insert_self a S)
        have hnotin : w ∉ S ∪ insert a s := by
          simp only [mem_union, mem_insert]
          rintro (h | h | h)
          · exact hwS h
          · exact hwa h
          · exact hws h
        intro a' b' hab
        have hR := hreadL a (Finset.mem_insert_self a s)
        -- 中间函数 `c`：`w` 位上取 `a'`，其余取 `b'`
        set c : V → α := fun u => if u = w then a' u else b' u with hc
        have hab' : ∀ u, u ≠ w → a' u = b' u :=
          fun u hu => hab u (by simp [hu])
        have hac : ∀ u ∈ S ∪ insert a s, a' u = c u := by
          intro u hu
          have huw : u ≠ w := fun h => hnotin (h ▸ hu)
          simp only [hc, if_neg huw]
          exact hab' u huw
        have hcb : ∀ u ∈ S ∪ insert a s, c u = b' u := by
          intro u hu
          have huw : u ≠ w := fun h => hnotin (h ▸ hu)
          simp only [hc, if_neg huw]
        rw [hR a' c hac, hR c b' hcb]
    have hblinda : ∀ w, w ≠ a → BlindAt a (φ w) :=
      hreads a (Finset.mem_insert_self a s)
    -- **最后（而不是最先）消掉 `a`**：底座为 `S`
    have hsing : S ∪ {a} = insert a S := by
      ext u; simp only [mem_union, mem_singleton, mem_insert]; tauto
    have hpeel := elim_peel' φ a haS hreada hblinda
      (hnorm a (Finset.mem_insert_self a s)) x
    rw [hsing, hpeel, Finset.prod_insert ha]
    ring

end Engine

/-! ===========================================================================
  §3 ⭐⭐⭐⭐⭐ **图侧：上方切片 ⟹ `ElimReads`**
  =========================================================================== -/

section GraphSide

variable {G : FateV2.Modeling.Graph.DAG V} {φ : V → (V → α) → ℝ}

/-- ⭐⭐ **图侧之一：`v ∉ pa_G(w)` ⟹ `φ_w` 不读 `x_v`。**

`LocalTo` 的读集是 `{w} ∪ pa_G(w)`；`v ≠ w` 且 `v ∉ pa_G(w)` ⟹ 读集不含 `v`。
**这是策略 2（以及任何基于读集的策略）消费图结构的唯一接口。** -/
theorem blind_of_not_mem_pa
    (hloc : ∀ (t : V) (x y : V → α), (∀ u ∈ insert t (pa G t), x u = y u) → φ t x = φ t y)
    {v w : V} (hw : w ≠ v) (hpa : v ∉ pa G w) : BlindAt v (φ w) := by
  intro a b hab
  refine hloc w a b fun u hu => ?_
  rw [mem_insert] at hu
  rcases hu with rfl | hup
  · exact hab u (by
      rw [mem_sdiff, mem_singleton]
      exact ⟨mem_univ u, hw⟩)
  · exact hab u (by
      rw [mem_sdiff, mem_singleton]
      exact ⟨mem_univ u, fun huv => hpa (huv ▸ hup)⟩)

/-- ⭐⭐⭐ **`LocalTo` ⟹（切片上）`ElimReads`**。

**图侧条件的精确陈述**（两条，缺一不可）：
1. `hout : ∀ v ∈ L, ∀ w ∉ L, ¬ G.edge v w` —— **`L` 到 `L` 外没有出边**；
2. `hin : ∀ v ∈ L, ∀ w ∈ L, w ≠ v → ¬ G.edge v w` —— **`L` 内部无边**（`L` 是反链）。

则 `ElimReads L φ`。

**这就是「上方切片（top slice）」**：`L` 的每个点在图里都是一个「`L` 内的 sink」。
* 条件 1 是**真的图论内容**（不是恒真）：取 `L = {v}` 时它说 `v` 是 sink；
* 条件 2 排除 `L` 内的边，正当：若 `v → w` 且 `v, w ∈ L`，则 `φ_w` 读 `x_v`，
  消元顺序就必须先 `w` 后 `v`，本定理的「同时消」不再成立（见 §4 的顺序版）。 -/
theorem topSlice_elimReads
    (hloc : ∀ (t : V) (x y : V → α), (∀ u ∈ insert t (pa G t), x u = y u) → φ t x = φ t y)
    {L : Finset V} (hout : ∀ v ∈ L, ∀ w ∉ L, ¬ G.edge v w)
    (hin : ∀ v ∈ L, ∀ w ∈ L, w ≠ v → ¬ G.edge v w) :
    ElimReads L φ := by
  intro v hv w hw
  refine blind_of_not_mem_pa hloc hw ?_
  rw [mem_pa]
  by_cases hwL : w ∈ L
  · exact hin v hv w hwL hw
  · exact hout v hv w hwL

/-- ⭐⭐⭐⭐ **单点特例（sink 消元）**：`v` 无出边 ⟹ 除 `φ_v` 外无因子读 `x_v`。 -/
theorem sink_elimReads
    (hloc : ∀ (t : V) (x y : V → α), (∀ u ∈ insert t (pa G t), x u = y u) → φ t x = φ t y)
    {v : V} (hsink : ∀ u, ¬ G.edge v u) : ElimReads {v} φ := by
  intro v' hv' w hw
  rw [mem_singleton] at hv'
  subst hv'
  refine blind_of_not_mem_pa hloc hw ?_
  rw [mem_pa]
  exact hsink w

/-- ⭐⭐⭐⭐⭐ **`topSlice_elim`（图 ⟹ 概率：切片消元定律）**。

设
* `p = ∏_w ψ_w`，`ψ_w` 读 `{w} ∪ pa_G(w)`（`FactorizesC` 的**见证**，`hψ` + `hfac`）；
* `L` 是 `G` 的一层上方切片：`L` 到 `L` 外无出边（`hout`）、`L` 内无边（`hin`）；
* `S` 与 `L` 不交；`ψ` 在 `L` 上归一（`hnorm`）且只读 `S ∪ L`（`hreadL`）；

则

$$\mathrm{mass}\,(S\cup L)\,p\,x=\Bigl(\prod_{v\in L}\psi_v(x)\Bigr)\cdot
  \mathrm{mass}\,S\,p\,x.$$

**这是策略 2 对「图 ⟹ 概率」的完整单层贡献**：左边是概率（`mass`），
右边是「图上这一层的归一化机制」与底层的乘积。全程无 `mass` 塔。

**⚠ 诚实标注**：`hreadL`/`hnorm` 是**关于见证 `ψ` 的额外前提**（`FactorizesC` 只保证读集，
不保证归一化 —— 归一化是「参数化概率模型」才有的内容）。不把结论写进前件：
这两条讲的是因子本身，与要证的 `mass` 恒等式无关。 -/
theorem topSlice_elim {p : (V → α) → ℝ} {ψ : V → (V → α) → ℝ}
    (hψ : ∀ (w : V) (x y : V → α), (∀ u ∈ insert w (pa G w), x u = y u) → ψ w x = ψ w y)
    (hfac : ∀ x, p x = ∏ w, ψ w x)
    {L : Finset V} (hout : ∀ v ∈ L, ∀ w ∉ L, ¬ G.edge v w)
    (hin : ∀ v ∈ L, ∀ w ∈ L, w ≠ v → ¬ G.edge v w)
    {S : Finset V} (hSL : Disjoint S L)
    (hreadL : ∀ v ∈ L, ∀ a b : V → α, (∀ u ∈ S ∪ L, a u = b u) → ψ v a = ψ v b)
    (hnorm : ∀ v ∈ L, ∀ x : V → α, (∑ a : α, ψ v (unpin v x a)) = 1) (x : V → α) :
    mass (S ∪ L) p x = (∏ v ∈ L, ψ v x) * mass S p x := by
  rw [funext hfac]
  exact elim_iterate_reads ψ hSL (topSlice_elimReads hψ hout hin) hreadL hnorm x

end GraphSide

end FateV2.Predict.View2ElimIterate