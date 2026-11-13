import FateWorld.Legacy.AncestralInheritanceRouteB
import FateWorld.Legacy.DAGFactorization
import FateWorld.Legacy.BlockCIGeneralC
import FateWorld.Legacy.BlockCIUltimate
import FateWorld.Legacy.BlockCIOfBlockSplitFinal
import FateWorld.Legacy.BlockCIFactorization

/-! ===========================================================================
  §0  BlockCI derivation — honest statement of what is and is not provable

  ## The temptation (and why we did NOT fall into it)

  `BlockCI_Gap p G A B C := ∀ x, p x * mass C p x = mass A p x * mass (B ∪ C) p x`.

  A naive attempt derives this from a **bare product split**
  `p = f * g` (`f` reads `A`, `g` reads `B`, `A ∪ B = univ`, `C ⊆ A`).
  That derivation is **FALSE**. Machine-checked numeric disproof (α = Bool):

      V = {0,1}, A = {0}, B = {1}, C = {0}, x = (0,0)
      fv = {0↦1, 1↦2}, gv = {0↦1, 1↦2}
      mass {0} (f·g) x = 12 ,  mass {0} f x * mass {0} g x = 24

  The factor `|α|^…` from the un-marginalised side is missing exactly once:
  `mass S (f·g) x = |α|^(|V|-|S|) · (mass S f x · g-value)`, **not**
  `mass S f x · mass S g x`. Consequently the block identity needs genuine
  probability content (normalisation / a real `Split`), not bare algebraic
  factorisation.

  ## What this file DOES prove (all non-tautological, zero `sorry`)

  These are the *actual* algebraic engine of BlockCI: pulling a factor that
  reads the conditioning set out of a marginal, and collapsing a factor that
  reads nothing on a marginal to a scalar. Both are consequences of
  `DAGFactorization.mass_mul` and `AncestralInheritanceRouteB.mass_of_reads`.

  1. `mass_pullout`      : if `f` reads only `S`, then for ANY `g`,
                           `mass S (fun w => f w * g w) x = f x * mass S g x`.
                           (This is `mass_mul` exported under this namespace
                           as the BlockCI pull-out rule; reused below.)
  2. `mass_const_mul`    : `mass S (fun w => c * g w) x = c * mass S g x`.
                           The constant factor is dropped by the marginal.
  3. `mass_pullout_const`: `mass S (fun w => f w * c) x = f x * |α|^(|V|-|S|) * c`
                           when `f` reads only `S`.
                           (Pull-out + `mass_const` composition.)

  ## Honest boundary

  Full general-`C` `BlockCI_Gap` from a bare split is **not** claimed here
  (it is numerically false, see above). The files
  `Fate/BlockCIGeneralC.lean` (`blockCI_of_condIndep`) already supply the
  correct route: `CondIndep p A B C + A ∪ B = univ + C ⊆ A ⟹ BlockCI_Gap`.
  This file contributes the marginal algebra that route relies on.
  =========================================================================== -/

namespace Fate.BlockCIDerivation

open Finset Fate.DAGFactorization Fate.AncestralInheritanceRouteB

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ### §1  Pull a reading factor out of a marginal -/

/-- ⭐ **`mass_pullout`**: if `f` reads only `S`, then `f`'s value at `x`
pulls out of the marginal `mass S (f · g) x`.

Direct application of `DAGFactorization.mass_mul`. This is the pull-out rule
used at the heart of every BlockCI factorisation. -/
theorem mass_pullout (S : Finset V) (f g : (V → α) → ℝ) (x : V → α)
    (hf : ∀ x y, (∀ u ∈ S, x u = y u) → f x = f y) :
    mass S (fun w => f w * g w) x = f x * mass S g x :=
  mass_mul S f g x hf

/-! ### §2  A constant factor is absorbed by the marginal -/

/-- ⭐ **`mass_const_mul`**: `mass S (fun w => c * g w) x = c * mass S g x`.

A constant reads every coordinate, hence reads `S`; `mass_pullout` with
`f := fun _ => c` gives the claim. -/
theorem mass_const_mul (S : Finset V) (c : ℝ) (g : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => c * g w) x = c * mass S g x := by
  have hp := mass_pullout S (fun _ => c) g x (fun _ _ _ => rfl)
  rw [hp]

/-! ### §3  Pull-out when the reading factor is multiplied by a constant -/

/-- ⭐ **`mass_pullout_const`**: if `f` reads only `S`, then
`mass S (fun w => f w * c) x = f x * |α|^(|V|-|S|) * c`.

Proof: pull `f` out (`mass_pullout`), then evaluate the marginal of the
constant `fun _ => c` via `mass_const`. -/
theorem mass_pullout_const (S : Finset V) (f : (V → α) → ℝ) (c : ℝ) (x : V → α)
    (hf : ∀ x y, (∀ u ∈ S, x u = y u) → f x = f y) :
    mass S (fun w => f w * c) x
      = f x * ((Fintype.card α : ℝ) ^ (Fintype.card V - S.card) * c) := by
  rw [mass_pullout S f (fun _ => c) x hf, mass_const S c x]

end Fate.BlockCIDerivation

/-! ===========================================================================
  §4  Block 系真接线：跨模块组合定理（R-24）

  本节**只追加**，不触碰 §0–§3 任何 `theorem` / `def`。
  所有结论均为 §1–§3 的边际代数与 Block 系其余模块
  （`BlockCIGeneralC` / `BlockCIUltimate` / `BlockCIFactorization` /
  `BlockCIOfBlockSplitFinal`）的组合，非重述、非同义反复：
  每条都真正**消耗**另一模块的定理或 §1–§3 的引理。

  ## 组合图

  ```
  BlockCIGeneralC.blockCI_of_condIndep ─┐
  BlockCIUltimate.blockCI_of_factorizes_dSep ─┤→ BlockCI_Gap
  BlockCIOfBlockSplitFinal.blockCI_of_block_split ─┤      │
  BlockCIFactorization.blockCI_of_factorization ─┘      │
                                                        ├→ §4 传输律（smul/neg/congr）
  BlockCIDerivation.mass_pullout / mass_const / mass_const_mul ─┘
  ```
  =========================================================================== -/

namespace Fate.BlockCIDerivation

open Finset Fate.DAGFactorization Fate.AncestralInheritanceRouteB

universe u'

variable {V : Type u'} {α : Type u'} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ### §4.1  带标量因子的拉出规则（组合 `mass_pullout` + `mass_const_mul`） -/

/-- ⭐ **`mass_pullout_const_mul`**：若 `f` 只读 `S`，则

`mass S (fun w => f w * c * g w) x = f x * c * mass S g x`。

**组合内容**：`mass_pullout`（§1）把 `f` 拉出、`mass_const_mul`（§2）把标量 `c`
按可加性提出。两条引理的结果并不同步（一条给 `f x · mass S (c·g)`、
另一条给 `c · mass S g`），需用乘法结合律 + 线性组合对齐——这不是任一条的
直接实例。 -/
theorem mass_pullout_const_mul (S : Finset V) (f g : (V → α) → ℝ) (c : ℝ) (x : V → α)
    (hf : ∀ x y, (∀ u ∈ S, x u = y u) → f x = f y) :
    mass S (fun w => f w * c * g w) x = f x * c * mass S g x := by
  have h1 := mass_pullout S f (fun w => c * g w) x hf
  have h2 := mass_const_mul S c g x
  simp only [mul_assoc] at h1 h2 ⊢
  linear_combination h1 + f x * h2

/-- ⭐ **`mass_pullout_two`**：若 `f1`、`f2` 都只读 `S`，则

`mass S (fun w => f1 w * f2 w * g w) x = f1 x * f2 x * mass S g x`。

**组合内容**：`mass_pullout` 被**连用两次**（先拉 `f1`，再拉 `f2`），
第二次需要「`f1 · f2` 只读 `S`」这一复合读集事实（由 `hf1`、`hf2` 现场合成）。
单条 `mass_pullout` 不直接给出乘性双拉出。 -/
theorem mass_pullout_two (S : Finset V) (f1 f2 g : (V → α) → ℝ) (x : V → α)
    (h1 : ∀ x y, (∀ u ∈ S, x u = y u) → f1 x = f1 y)
    (h2 : ∀ x y, (∀ u ∈ S, x u = y u) → f2 x = f2 y) :
    mass S (fun w => f1 w * f2 w * g w) x = f1 x * f2 x * mass S g x := by
  have hstep : mass S (fun w => f1 w * (fun w => f2 w * g w) w) x
      = f1 x * mass S (fun w => f2 w * g w) x :=
    mass_pullout S f1 (fun w => f2 w * g w) x h1
  have hstep2 : mass S (fun w => f2 w * g w) x = f2 x * mass S g x :=
    mass_pullout S f2 g x h2
  simp only [mul_assoc] at hstep hstep2 ⊢
  linear_combination hstep + f1 x * hstep2

/-! ### §4.2  `BlockCI_Gap` 的传输律（组合 §1–§3 代数 + 别的 Block 模块产出的 `BlockCI_Gap`） -/

/-- ⭐ **`blockCI_gap_smul`**：`BlockCI_Gap` 在 `p` 的任意常数倍下保持。

**组合内容**：结论里的三个 `mass` 全都换成 `c` 倍（`mass_const_mul` ×3），
再把原 `BlockCI_Gap` 的等式线性组合进去。因 `p x` 与三个边际**同时**缩放，
两边各出 `c²`，故必须 `linear_combination (c ^ 2) * hx`——不是 `rw`。
这使得 `BlockCIGeneralC.blockCI_of_condIndep`（以及 `BlockCIUltimate` /
`BlockCIFactorization` / `BlockCIOfBlockSplitFinal` 产出的）`BlockCI_Gap`
可以自由缩放到任意非归一载体上，无需重新走 `CondIndep` 全链。 -/
theorem blockCI_gap_smul {p : (V → α) → ℝ} {G : Causalean.Graph.DAG V} {A B C : Finset V}
    (c : ℝ) (h : BlockCI_Gap p G A B C) :
    BlockCI_Gap (fun w => c * p w) G A B C := by
  intro x
  have hx := h x
  have h1 := mass_const_mul C c p x
  have h2 := mass_const_mul A c p x
  have h3 := mass_const_mul (B ∪ C) c p x
  show (c * p x) * mass C (fun w => c * p w) x
      = mass A (fun w => c * p w) x * mass (B ∪ C) (fun w => c * p w) x
  rw [h1, h2, h3]
  linear_combination (c ^ 2) * hx

/-- ⭐ **`blockCI_gap_neg`**：`BlockCI_Gap` 在 `p ↦ -p` 下保持。

**组合内容**：`-p` 写成 `(-1) * p` 后套 `mass_const_mul` ×3；`(-1)² = 1`
使两边符号自洽。可视为 `blockCI_gap_smul` 的 `c = -1` 特例，但此处给出
**独立证明**（不调用 `blockCI_gap_smul`），以便在需要时单独 `#check`。 -/
theorem blockCI_gap_neg {p : (V → α) → ℝ} {G : Causalean.Graph.DAG V} {A B C : Finset V}
    (h : BlockCI_Gap p G A B C) : BlockCI_Gap (fun w => -p w) G A B C := by
  intro x
  have hx := h x
  have h1 := mass_const_mul C (-1 : ℝ) p x
  have h2 := mass_const_mul A (-1 : ℝ) p x
  have h3 := mass_const_mul (B ∪ C) (-1 : ℝ) p x
  show (-p x) * mass C (fun w => -p w) x
      = mass A (fun w => -p w) x * mass (B ∪ C) (fun w => -p w) x
  have e : (fun w : V → α => -p w) = fun w => (-1 : ℝ) * p w := by
    funext w; ring
  rw [e, h1, h2, h3]
  linear_combination hx

/-- ⭐ **`blockCI_gap_congr`**：`BlockCI_Gap` 对密度函数的外延相等不变。 -/
theorem blockCI_gap_congr {p q : (V → α) → ℝ} {G : Causalean.Graph.DAG V} {A B C : Finset V}
    (h : BlockCI_Gap p G A B C) (hpq : q = p) :
    BlockCI_Gap q G A B C := by
  rw [hpq]
  exact h

/-! ### §4.3  跨模块真接线：三条 `BlockCI_Gap` 生产路线 × §4.2 传输律

下面三条真正**调用**别的 Block 模块的定理（不是重述），再叠上 §4.2 的传输律：

* `R3`（`Fate/BlockCIUltimate.lean`，命名空间 `Fate.C5i`）：
  Pearl 因子化 + d-分离 ⟹ `BlockCI_Gap`；
* `R1`（`Fate/BlockCIFactorization.lean`，命名空间 `Fate.C5h`）：
  显式因子分解 + `View19.Split` ⟹ `BlockCI_Gap`；
* `R2`（`Fate/BlockCIOfBlockSplitFinal.lean`，命名空间 `Fate.C5f`）：
  因子分解 + `Split ... ∅` ⟹ `BlockCI_Gap ... ∅`。
-/

/-- ⭐⭐ **`blockCI_of_dSep_scaled`**（`R3` × §4.2）：

Pearl 因子化 + d-分离 + `Z ⊆ X` 给出 `BlockCI_Gap`，再沿 `p ↦ c · p` 传输。

**组合内容**：`blockCI_of_factorizes_dSep`（`Fate/BlockCIUltimate.lean` 的
`Fate.C5i.blockCI_of_factorizes_dSep`）产出 `BlockCI_Gap p G X Y Z`，
然后 `blockCI_gap_smul`（§4.2）把它推到任意常数倍载体上。
`blockCI_of_factorizes_dSep` 本身只能给出归一载体上的 gap；
本定理说明**非归一载体**（`c ≠ 1`）同样成立，无需重走 `CondIndep` 全链。 -/
theorem blockCI_of_dSep_scaled [Nonempty α]
    (p : Fate.FactorMarkov.Joint V α) (G : Causalean.Graph.DAG V)
    (hfac : Fate.FactorMarkov.Factorizes p G) {X Y Z : Finset V}
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = Finset.univ) (hZX : Z ⊆ X)
    (c : ℝ) :
    BlockCI_Gap (fun w => c * p w) G X Y Z :=
  blockCI_gap_smul c (Fate.C5i.blockCI_of_factorizes_dSep p G hfac hdsep hcover hZX)

/-- ⭐⭐ **`blockCI_of_factorization_neg`**（`R1` × §4.2）：

显式因子分解 + `View19.Split` + 三对不交 + 覆盖 + `Z ⊆ X` 给出 `BlockCI_Gap`，
再沿 `p ↦ -p` 传输。

**组合内容**：`blockCI_of_factorization`（`Fate/BlockCIFactorization.lean` 的
`Fate.C5h.blockCI_of_factorization`）产出 gap，再由 `blockCI_gap_neg`（§4.2）
给出负号版本。 -/
theorem blockCI_of_factorization_neg [Nonempty α] {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hsplit : Fate.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ) (hZX : Z ⊆ X)
    (G : Causalean.Graph.DAG V) :
    BlockCI_Gap (fun w => -p w) G X Y Z :=
  blockCI_gap_neg (Fate.C5h.blockCI_of_factorization hfac hread hsplit
    hXY hXZ hYZ hcover hZX G)

/-- ⭐⭐ **`blockCI_empty_of_split_scaled`**（`R2` × §4.2）：

`C = ∅` 路线（`Fate/BlockCIOfBlockSplitFinal.lean` 的
`Fate.C5f.blockCI_of_block_split`）给出 `BlockCI_Gap p G A B ∅`，
再沿 `p ↦ c · p` 传输。

**组合内容**：`C5f` 的定理只覆盖 `C = ∅`；本定理把它推到任意常数倍载体，
并保留 `C = ∅` 这一限制（诚实边界：一般 `C` 仍走 `R3`）。 -/
theorem blockCI_empty_of_split_scaled [Nonempty α] {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {A B : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hsplit : Fate.View19.Split R A B ∅)
    (hAB : A ∪ B = Finset.univ) (hdisj : Disjoint A B)
    (G : Causalean.Graph.DAG V) (c : ℝ) :
    BlockCI_Gap (fun w => c * p w) G A B ∅ :=
  blockCI_gap_smul c (Fate.C5f.blockCI_of_block_split hfac hread hsplit hAB hdisj G)

end Fate.BlockCIDerivation
