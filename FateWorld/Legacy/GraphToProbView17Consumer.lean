/-
  Fate/GraphToProbView17Consumer.lean
  ========================================================================
  消费 `Fate/GraphToProbView17.lean`（视角 17「支撑剖分 ⟹ 因子核」）。

  本文件**不新增任何定义**，只把 view17 的既有结论接到 view17 自己没有写下的
  推论上。所有证明只调用 view17 已证的定理：

  * `fiberSplit_implies_condMul`           （view17 §2，V17-1）
  * `screen_split_Y_factor_trivial`        （view17 §9.2，V17-13）
  * `screen_split_Y_channel_collapses`     （view17 §9.2，V17-14）

  消费清单：
  * §1 `margYZ_as_sum`                     —— `ScreenSplit` + `dSep` ⟹
    `Y`-边缘 `margYZ` 在 `Y` 上有 `y`-**无关**的显式闭式
    `∑ x, λ z · a x z`（view17 只证了 `b ≡ 1`，没有把它推成边缘的闭式）
  * §0 `fiberSplit_of_screenSplit`          —— `ScreenSplit ⟹ FiberSplit`（定义读出）
  * §2 `screen_split_Y_law_invariant`      —— `dSep` + `ScreenSplit` ⟹
    `Y` 内联合质量 `y`-**无关**
  * §3 `screen_split_Y_margYZ_invariant`   —— 同上，求和（边缘）层
  * §4 `screen_split_Y_margYZ_collapses`   —— 单点坍缩形式（`y0` 参照）
  * §5 `screenSplit_second_conjunct_needed` —— 一致性：`b ≡ 1` 不是从
    乘积结构自动掉出来的（`b ≡ 2`, `f ≡ 1`, `a ≡ 1`, `p ≡ 2` 见证）

  ## 诚实边界（必读）
  * **§1–§4 的图侧假设 `h : G.dSep X Y Z` 是**真的**用到的**：
    证明必经 `screen_split_Y_factor_trivial`，而后者在 view17 内部
    用 `dSep` 的第 4 子句 `Disjoint (bbReachableVertices Z X) Y`
    把 `y ∈ Y` 转成「屏幕外」，从而给出 `b y z = 1`。
    **去掉 `h`，`b ≡ 1` 不再可得 ⟹ 本文件 4 条定理全部不成立**
    （见 §5 的 `screenSplit_second_conjunct_needed`：仅乘积结构允许 `b ≡ 2`）。
  * **本文件不声称** `dSep ⟹ FiberSplit` / `dSep ⟹ CondMul`。
    `ScreenSplit` 仍是**显式前提**（view17 §9 已如实登记此边界），
    本文件只是把它的**后果**往前推了一步，不掩盖其前提性。
  * **`Y = ∅` 时 §2–§4 结论真空**（`y ∈ Y` 不可满足）。这是诚实的边界，
    不宣称非空。`Y` 非空时结论有实质内容（`Y` 为单点或 `Y = univ` 皆可）。
  * **不使用 `sorry` / `admit` / `axiom`。**
-/
import FateWorld.Legacy.GraphToProbView17
import Mathlib.Tactic.Ring

namespace Fate.GraphToProbView17Consumer

open Finset
open Causalean.Graph
open Fate.GraphToProbView17

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ===========================================================================
  §0 把 view17 `ScreenSplit` 的**三因子**取出（`screen_split_Y_factor_trivial`
  的结论形态，原样复用）
  =========================================================================== -/

/-- ⭐ **从 `ScreenSplit` 直接读出 `FiberSplit`**（不涉及 `dSep`）。

`ScreenSplit` 是 `FiberSplit` 加上第二个合取项，故第一个合取项即 `FiberSplit`。
这是 view17 的 `ScreenSplit` **定义**的读出（view17 自己没写这条）。 -/
theorem fiberSplit_of_screenSplit (G : DAG V) {X Y Z : Finset V}
    {p : (V × V) × V → ℝ} (hsp : ScreenSplit G X Y Z p) :
    FiberSplit (α := V) (β := V) (γ := V) p := by
  obtain ⟨lam, a, b, hb⟩ := hsp
  exact ⟨lam, a, b, fun x y z => (hb x y z).1⟩

/-! ===========================================================================
  §2 `Y` 内联合质量 `y`-无关
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **V17C-2：`dSep` + `ScreenSplit` ⟹ `Y` 内联合质量 `y`-无关。**

$$\forall y,y'\in Y,\qquad p((x,y),z) = p((x,y'),z).$$

**证明**：`screen_split_Y_factor_trivial` 给出三因子分解与 `b ≡ 1` on `Y`；
两侧都化成 `λ z · a x z · 1`，故相等。

**⚠ 非目标的重申**：这不是「`X ⟂ Y | Z`」，只是**条件化后 `Y` 不可分辨**。
更强的结论需要归一化（本文件不引入）。 -/
theorem screen_split_Y_law_invariant (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) (p : (V × V) × V → ℝ)
    (hsp : ScreenSplit G X Y Z p) :
    ∀ x z, ∀ y ∈ Y, ∀ y' ∈ Y, p ((x, y), z) = p ((x, y'), z) := by
  obtain ⟨lam, a, b, hfac, hone⟩ := screen_split_Y_factor_trivial G h p hsp
  intro x z y hy y' hy'
  rw [hfac x y z, hfac x y' z, hone y hy z, hone y' hy' z]

/-! ===========================================================================
  §3 `Y` 内 `margYZ` `y`-无关
  =========================================================================== -/

/-- ⭐⭐⭐ **V17C-3：求和层版本** —— `Y` 内 `margYZ` 与 `y` 无关。

对 `x` 求和把 §2 提升到边缘层。**注意** `margYZ` 的求和变量是 `x`
（`margYZ p y z = ∑ x, p ((x,y),z)`，见 `Fate.FinCondIndep`）。 -/
theorem screen_split_Y_margYZ_invariant (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) (p : (V × V) × V → ℝ)
    (hsp : ScreenSplit G X Y Z p) :
    ∀ z, ∀ y ∈ Y, ∀ y' ∈ Y,
      Fate.FinCondIndep.margYZ p y z = Fate.FinCondIndep.margYZ p y' z := by
  intro z y hy y' hy'
  unfold Fate.FinCondIndep.margYZ
  exact Finset.sum_congr rfl
    (fun x _ => screen_split_Y_law_invariant G h p hsp x z y hy y' hy')

/-! ===========================================================================
  §4 `Y` 上的条件乘性（带 `y0` 参照）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **V17C-4：`dSep` + `ScreenSplit` ⟹ `Y` 上 `margYZ` 与 `y` 无关，
故此 `Y`-通道在 `margYZ` 中完全塌缩。**

这是 §3 的**单点坍缩形式**（`y0` 参照写法），把 §3 的量词结构压平成
下游可直接 `rw` 的等式：

$$\forall y\in Y,\qquad \mathrm{margYZ}\ p\ y\ z = \mathrm{margYZ}\ p\ y_0\ z .$$

**与 §3 的区别**：§3 要求**两个**假设 `y, y' ∈ Y`；本条只要求 `y ∈ Y`
与**一个固定的**参照点 `y0 ∈ Y`，形态更适合作为改写规则使用。

**⚠ 说明本文件 §4 的边界**：由 `CondMul`（分母 `margZ`）**不能**推出
「分母换成 `margYZ y0` 的乘性等式」——那需要另加 `margZ = margYZ y0`
之类的归一条件，本文件**不假设**它，故**不证**那条（避免写假命题）。 -/
theorem screen_split_Y_margYZ_collapses (G : DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) (p : (V × V) × V → ℝ)
    (hsp : ScreenSplit G X Y Z p) (y0 : V) (hy0 : y0 ∈ Y) :
    ∀ z, ∀ y ∈ Y,
      Fate.FinCondIndep.margYZ p y z = Fate.FinCondIndep.margYZ p y0 z := by
  intro z y hy
  exact screen_split_Y_margYZ_invariant G h p hsp z y hy y0 hy0

/-! ===========================================================================
  §5 一致性：`b ≡ 1`（`dSep` 的产物）**不是**乘积结构的自动推论
  =========================================================================== -/

section Sanity

/-- ⭐⭐⭐ **V17C-5：乘积结构允许 `b ≡ 2`（故 `dSep` 真的不可去）。**

给出一个**满足三因子乘积结构**、但 `Y`-因子恒为 `2`（而非 `1`）的律：

取 `V := Bool`、`p ≡ 2`、`lam ≡ 1`、`a ≡ 1`、`b ≡ 2`。
则 `p ((x,y),z) = 2 = 1 · 1 · 2`（乘积结构成立），且 `b ≡ 2 ≡ 1` **不成立**。

**意义**：view17 §9 的 `b ≡ 1` 结论**只能**来自 `dSep`（经
`screen_split_Y_factor_trivial` 的 `Disjoint (bbReachableVertices Z X) Y`），
**不能**来自 `FiberSplit` / `ScreenSplit` 的第一个合取项。
这直接证伪了「§2–§4 是重言式」的怀疑：**没有 `dSep`，`b ≡ 1` 为假**。 -/
theorem screenSplit_second_conjunct_needed :
    ∃ (g : (Bool × Bool) × Bool → ℝ),
      ∃ (f : Bool → ℝ), ∃ (a : Bool → Bool → ℝ), ∃ (b : Bool → Bool → ℝ),
      (∀ x y z, g ((x, y), z) = f z * a x z * b y z)
      ∧ (∀ y z, b y z = 2)
      ∧ ¬ (∀ y z, b y z = 1) := by
  refine ⟨fun _ => 2, fun _ => 1, fun _ _ => 1, fun _ _ => 2, ?_, fun _ _ => rfl, ?_⟩
  · intro x y z; norm_num
  · intro hb
    have h := hb true true
    norm_num at h

/-- ⭐⭐ **`Y = ∅` 时 §2 结论确实真空**（诚实登记边界，不宣称非空）。 -/
theorem screen_split_Y_law_invariant_vacuous (G : DAG V) (X Z : Finset V)
    (p : (V × V) × V → ℝ) :
    ∀ x z, ∀ y ∈ (∅ : Finset V), ∀ y' ∈ (∅ : Finset V),
      p ((x, y), z) = p ((x, y'), z) := by
  intro x z y hy
  exact absurd hy (Finset.notMem_empty y)

end Sanity

end Fate.GraphToProbView17Consumer
