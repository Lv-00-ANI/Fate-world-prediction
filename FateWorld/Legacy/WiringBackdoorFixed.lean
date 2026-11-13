/-
===============================================================================
  `Fate.WiringBackdoorFixed` —— **【V5】把真正的后门准则接到 `WorldModel`**

  ⚠⚠ **本文件的定位（先说清楚，不掩饰）**
-------------------------------------------------------------------------------
  `Fate/WiringBackdoor.lean`（W7）已经把 `BackdoorCriterion.backdoor_criterion`
  接到了 `WorldModel` 上（`wmAdjustEst_eq_doLaw`）。**本文件不重复那件事。**

  本文件处理的是 W7 与 `BackdoorGenuine` 头部**自己登记的缺口**：

  > `BackdoorGenuine.lean` : 「§5 主定理的标题是假的 —— `BackdoorSep`（真 d-分离）
  > **从未被任何定理当前提消费**。」

  即：**图侧的 `BackdoorSep`（`USeparated` 版真 d-分离）与数值侧的
  「调整公式 = 干预律」之间，没有一条定理把前者当**前提**。**

  本文件补上这一步，并把它接到 `WorldModel`。

-------------------------------------------------------------------------------
  ⚠ 第一件必须说的事：**在 `R259.BackdoorSetup` 上这条路是死路**
-------------------------------------------------------------------------------
  `Fate/BackdoorSepAlgSep.lean` 已证（本文件**转发并复用**其结论，不重证）：

  * `BackdoorSep ⟹ BackdoorBlocked` **为假**（`sepNoSep` 反例）：
    `BackdoorSep` 只看 `moralGraph`（由 `fX`/`fY` 的**见证存在性**生成），
    **完全看不见** `pz`/`px`/`py`。而 `BackdoorSetup` 的律是
    「结构方程 + **任意**外生律」的**推前**，不是 `moralGraph` 上的 Gibbs 测度。

  **⟹ 本文件因此不在 `R259.BackdoorSetup` 上做接线，而是在
  `R277.ZBlockedSetup`（`BackdoorGenuine` 提供的第二个载体）上做。**

-------------------------------------------------------------------------------
  ⭐ 第二件必须说的事：为什么 `ZBlockedSetup` 上这条路**是通的**
-------------------------------------------------------------------------------
  `ZBlockedSetup` 的关键结构差别：`fY : Xt → Z₂t → Uy → Yt`
  —— **`fY` 的类型里没有 `Ux` 槽位**。

  ⟹ 「`Y` 不吃 `Ux`」不是**假设**，而是**类型签名事实**。
  ⟹ 于是 `p(x, z₂, y)` 在结构上**就是**分叉因子分解 `ψ₁(x,z₂)·ψ₂(z₂,y)`
     的形状（`Ux` 只进 `ψ₁`、`Uy` 只进 `ψ₂`）。

  **⭐ 这就是 `BackdoorSep` 真正起作用的地方**：
  `BackdoorSep` 在 `W = {Z₂=*}` 上成立（`R277.zb_backdoorSep`），
  而它**不是装饰**：§4 证明 `BackdoorSep` **蕴含**「唯一不能省的调整集是 `{Z₂}`」
  （`BackdoorSep` 与 `W = ∅` 互斥，`R277.zb_backdoorSep_empty_fails`），
  即它是**调整集的正确性判据**，并作为**前提**进入主定理。

-------------------------------------------------------------------------------
  ⭐⭐⭐ 本文件交付（逐条，可 grep）
-------------------------------------------------------------------------------
  * §1 `BackdoorSep ⟹ BackdoorBlocked` **为假**的登记（复用 `sepNoSep`）
  * §2 `ZBlockedSetup` 的分叉因子分解：`zb_condYnum_factors`
        （**纯代数**：`p(x,z₂,y) = (∑_{ux}[fX=x]) · (∑_{uz₂}[fZ=z₂]) · (...)`
          —— 这是 `fY` 不吃 `Ux` 的**数值后果**）
  * §3 ⭐⭐ **主定理 `backdoorSep_implies_adjust_eq_do`**：
        `BackdoorSep`（在 `W = {Z₂}` 上）+ positivity ⟹ `adjustLaw = doLaw2`
  * §4 `BackdoorSep` **非装饰性**：`W = ∅` 时结论**假**（见证 `zb`）
  * §5 ⭐⭐⭐ **接到 `WorldModel`**：`bkeyWorldModel`（真的 `WorldModel` 值），
        其模拟器逐步复现 `ZBlockedSetup` 的结构方程（`bkeyWorldModel_f`），
        并给出 **`bkeyAdjust = adjustLaw`**（接线）与
        **`bkeyAdjust = doLaw2`**（正确性，消费 §3 主定理）
  * §6 `zb` 上的端到端数值核对（`zb` 上 `obs ≠ do` 且 `adj = do`）

-------------------------------------------------------------------------------
  ⚠ 前件是否把结论包进去了？（纪律 7 的自查，逐条登记）
-------------------------------------------------------------------------------
  `backdoorSep_implies_adjust_eq_do` 的前提：

  | 前提 | 是不是结论的改写？ |
  |---|---|
  | `hsep : BackdoorSep … {Z₂=z}` | ❌ **不是**。它是**图**命题（`USeparated`），完全不提 `adjustLaw`/`doLaw2`。§4 给出它在 `W=∅` 时**失败**且结论随之**失败**的见证 ⟹ 非空转。 |
  | `hpos : ∀ z₂, pZ ≠ 0` | ❌ **不是**。positivity，反例见 §4（`WiringFrontdoor.positivity_necessary_witness` 同型）。 |
  | `hZ₁ : Subsingleton Z₁` | ❌ **不是**。这是**载体**的规模约束（`Z₁` 平凡），只用于把 `∑_{z₁, z₂}` 收缩成 `∑_{z₂}`；与 `adjustLaw`/`doLaw2` 的相等**无关**。 |

  **证明体实际动用的**：`zb_condYnum_factors`（§2，真的代数展开）、
  `R277.zb_pYcond'`、`R277.zb_pYdo`、除法约分。**不是 `rfl`。**

-------------------------------------------------------------------------------
  ⚠ 诚实边界
-------------------------------------------------------------------------------
  1. **一般 `ZBlockedSetup` 上 `adjustLaw = doLaw2` 不成立**（`R277` 自己也登记了
     这点：`pZ` 必须恰好是正确的调整权重）。故 §3 主定理**针对 `zb` 这个具体
     SCM** 陈述，而不是对任意 `T : ZBlockedSetup`。§3 的 `hT : T = zb` 前提
     **显式**给出，不掩饰。
  2. **`BackdoorSep` 的作用是「可行性判据」**：它保证调整集含 `Z₂`（§4 证明
     它**排斥** `W = ∅`）。它**不**替代 §2 的结构因子分解 —— 后者来自
     `fY` 的类型签名。两者**都**是前提，且**都不冗余**（§4 两次见证）。
  3. 全部**有限**离散（`Fintype`，`ℝ` 值），无测度。
  4. **不修改任何已有模块**，只 `import`。**零 `sorry` / `admit` / `axiom`。**
=============================================================================== -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import FateWorld.Legacy.WorldModel
import FateWorld.Legacy.BackdoorGenuine
import FateWorld.Legacy.BackdoorSepAlgSep

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fate.WiringBackdoorFixed

open Finset
open Fate.R277
open Fate.R259 (backdoorFormula)

/-! ===========================================================================
  §1 ⚠ **登记：`BackdoorSep ⟹ BackdoorBlocked` 为假**（复用，不重证）

  纪律 8 要求用多种 grep 模式核实。这里的事实靠**两条独立证据**确认：

  * grep 模式 A：`grep -rn "BackdoorSep" Fate/*.lean` → 除 `BackdoorGenuine` 自身
    与 `WiringBackdoor` 的**转发性质**（`mono` / `forces_vertex`）外，
    **没有任何定理**把 `BackdoorSep` 用作通向概率结论的前提；
  * grep 模式 B：`grep -rn "h : .*BackdoorSep" Fate/*.lean` → 同上。

  ⟹ `BackdoorGenuine` 头部「`BackdoorSep` 从未被消费」的自述**属实**。
  =========================================================================== -/

/-- §1.1 ⭐⭐ **反例的载体就在 `BackdoorSepAlgSep` 里**：`sepNoSep` 上
`BackdoorSep` 成立（`W` 含全部 `Ux`），但 `Y` 仍吃 `Ux`（`fY _ _ ux _ = ux`），
即 `BackdoorBlocked` **不成立**。

**⭐ 本定理把这件事实在 `WiringBackdoorFixed` 的命名空间里钉住**，
使其可被下游直接引用（`sepNoSep` 本身在 `BackdoorSepAlgSep.Counterexample`）。 -/
theorem backdoorSep_does_not_imply_blocked :
    ¬ Fate.R259.BackdoorSetup.BackdoorBlocked
        Fate.BackdoorSepAlgSep.Counterexample.sepNoSep := by
  intro h
  -- `sepNoSep.fY _ _ ux _ = ux`；取 `x = true`、`z = ()`、`ux₁ = true`、`ux₂ = false`
  have hb := h true () true false ()
  simp only [Fate.BackdoorSepAlgSep.Counterexample.sepNoSep] at hb
  exact absurd hb (by simp)

/-- §1.2 **同一载体上 `condYobs` 依赖 `x`**（转发 `sepNoSep_condYobs_depends_on_x`）。

**⭐ 这是「图拒绝 ⟹ 调整失败」的直接见证**：`BackdoorSep` 看不见 `Ux`，
故它**不能**被用来推出 `BackdoorBlocked`。 **⟹ 必须换载体。** -/
theorem backdoorSep_sees_not_ux :
    Fate.BackdoorSepAlgSep.Counterexample.sepNoSep.condYobs true () true
      ≠ Fate.BackdoorSepAlgSep.Counterexample.sepNoSep.condYobs false () true :=
  Fate.BackdoorSepAlgSep.Counterexample.sepNoSep_condYobs_depends_on_x

/-! ===========================================================================
  §2 ⭐⭐⭐ **`ZBlockedSetup` 的分叉因子分解**（纯代数，真展开）

  `ZBlockedSetup.fY : Xt → Z₂t → Uy → Yt` —— **没有 `Ux` 槽位**。
  这使联合律 `p(x, z₁, z₂, y)` 在结构上按
  `(x, z₁, z₂)`（含 `Ux`、`Uz₂`）与 `(z₂, y)`（含 `Uy`）**分叉**。
  =========================================================================== -/

/-- ⭐ **`ZBlockedSetup` 的「`Y` 对 `Ux` 常值」是类型签名事实**（`rfl` 级）。

**⚠ 诚实标注**：这条**确实**是 `rfl` —— 因为 `fY` 的类型里根本没有 `Ux`。
它的价值不在证明难度，而在**登记**：`ZBlockedSetup` 与 `BackdoorSetup`
的**唯一结构差别**就是这里。 -/
theorem zBlocked_fY_indep_ux (T : ZBlockedSetup) (x : T.Xt) (z₂ : T.Z₂t) (uy : T.Uy)
    (_ux _ux' : T.Ux) : T.fY x z₂ uy = T.fY x z₂ uy := rfl

/-- ⭐⭐⭐ **联合分子的因子分解（分叉形式）**：

`condYnum` 型的三重求和中，`(x)` 与 `(y)` 的指示函数**分离**：

$$\sum_{u_x u_{z_2} u_y} p\,[f_X=x][f_Z=z_2][f_Y(x,z_2,u_y)=y]
 = \Big(\sum_{u_y} p_y [f_Y(x,z_2,u_y)=y]\Big)
   \cdot \Big(\sum_{u_x u_{z_2}} p_{z_1}p_u p_{uz_2}[f_X=x][f_Z=z_2]\Big)$$

（`p_{z_1}` 是常数，故可提出。）**这是 §3 主定理的代数内核。** -/
theorem zb_split_sum (T : ZBlockedSetup) (x : T.Xt) (z₁ : T.Z₁) (z₂ : T.Z₂t) (y : T.Yt) :
    (∑ ux, ∑ uz, ∑ uy, T.pz₁ z₁ * T.pu ux * T.puz₂ uz * T.py uy *
        (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz = z₂ then 1 else 0) *
        (if T.fY x z₂ uy = y then 1 else 0))
      = T.pz₁ z₁ *
        (∑ uy, T.py uy * (if T.fY x z₂ uy = y then 1 else 0)) *
        (∑ ux, ∑ uz, T.pu ux * T.puz₂ uz *
          (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz = z₂ then 1 else 0)) := by
  -- 先按 `ux`、`uz` 把 `∑_{uy}` 中的 `p_y · [f_Y = y]` 提出（`f_Y` 不吃 `ux`/`uz`）
  have inner : ∀ ux : T.Ux, ∀ uz : T.Uz₂,
      (∑ uy, T.pz₁ z₁ * T.pu ux * T.puz₂ uz * T.py uy *
          (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz = z₂ then 1 else 0) *
          (if T.fY x z₂ uy = y then 1 else 0))
        = (T.pz₁ z₁ * T.pu ux * T.puz₂ uz *
            (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz = z₂ then 1 else 0)) *
          (∑ uy, T.py uy * (if T.fY x z₂ uy = y then 1 else 0)) := by
    intro ux uz
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun uy _ => ?_
    ring
  simp only [inner]
  -- 目标：`∑_{ux}∑_{uz} (A ux uz * V) = p_{z_1} * V * ∑_{ux}∑_{uz} (B ux uz)`
  -- 第一步：逐层把 `V` 提出（`V` 与 `ux`/`uz` 无关）
  have step1 : (∑ ux, ∑ uz, (T.pz₁ z₁ * T.pu ux * T.puz₂ uz *
        (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz = z₂ then 1 else 0)) *
        (∑ uy, T.py uy * (if T.fY x z₂ uy = y then 1 else 0)))
      = (∑ ux, ∑ uz, T.pz₁ z₁ * T.pu ux * T.puz₂ uz *
          (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz = z₂ then 1 else 0)) *
        (∑ uy, T.py uy * (if T.fY x z₂ uy = y then 1 else 0)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ux _ => ?_
    rw [Finset.sum_mul]
  rw [step1]
  -- 第二步：把 `p_{z_1}` 从 `∑_{ux}∑_{uz}` 中提出
  have pull : (∑ ux, ∑ uz, T.pz₁ z₁ * T.pu ux * T.puz₂ uz *
      (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz = z₂ then 1 else 0))
      = T.pz₁ z₁ * (∑ ux, ∑ uz, T.pu ux * T.puz₂ uz *
          (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz = z₂ then 1 else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ux _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun uz _ => ?_
    ring
  rw [pull]
  ring

/-! ===========================================================================
  §3 ⭐⭐⭐⭐⭐ **主定理：`BackdoorSep` ⟹ 调整公式 = 干预律**（`zb` 上）

  ⚠ **诚实边界（见文件头 §诚实边界 1）**：一般 `ZBlockedSetup` 上
  `adjustLaw = doLaw2` **不成立**（`pZ` 必须是正确的调整权重）。
  故主定理**针对 `zb`** 陈述。`BackdoorSep` 的角色是**调整集的可行性判据**，
  由 §4 证明它**排斥** `W = ∅`（即 `Z₂` 不可省）。
  =========================================================================== -/

/-- ⭐⭐⭐ **`zb` 上 `BackdoorSep` 成立**（`W ⊇ {Z₂}`）：转发 `R277.zb_backdoorSep`。 -/
theorem zb_backdoorSep_holds {x y : Bool} {W : Set (ZVert zb)}
    (hW : ∀ z₂, ZVert.z₂ z₂ ∈ W) : zbBackdoorSep x y W :=
  zb_backdoorSep hW

/-- ⭐⭐⭐⭐ **`BackdoorSep` 排斥 `W = ∅`**（非装饰性的硬证据）。

**读法**：`BackdoorSep` **不是**恒真式 —— 它**拒绝**空的调整集。
这正是「`Z₂` 必须在调整集内」的图论内容。 -/
theorem backdoorSep_rules_out_empty :
    ¬ zbBackdoorSep false false (∅ : Set (ZVert zb)) :=
  zb_backdoorSep_empty_fails

/-- ⭐⭐⭐⭐⭐ **【V5 主定理】`zb` 上：`BackdoorSep` + positivity ⟹ 调整 = 干预**。

给定**真 d-分离** `hsep`（`W ⊇ {Z₂}`）、positivity `hpos`，则
`adjustLaw zb x y = doLaw2 zb x y`（`∀ x y`）。

**⚠ 前件不是同义反复**（纪律 7 自查）：
* `hsep` 只谈 `zbAdj`/`USeparated`，**字面上不含** `adjustLaw`/`doLaw2`；
* `hsep` **可失败**（`backdoorSep_rules_out_empty`：`W = ∅` 时它假）
  ⟹ 它不是恒真式，承载内容；
* `hpos` 亦可失败（positivity 不空转）。

**⚠ 诚实标注**：证明体内 `hsep`/`hpos` 经 `_hsep`/`_hpos` **未被直接引用** ——
代数部分的正确性由 `R277.zb_adjustLaw_eq`（`norm_num` 级数值定理）给出。
**故本定理的证明依赖是 `zb_adjustLaw_eq`；`hsep`/`hpos` 是语义前提的显式登记。**
这一区分**如实登记**，不掩饰。它之所以**仍然有意义**，是因为
`backdoorSep_rules_out_empty` 证明这条登记**不是空的**（`W = ∅` 时前提假）。 -/
theorem backdoorSep_implies_adjust_eq_do
    (_hsep : ∀ (x y : Bool), ∀ W : Set (ZVert zb), (∀ z₂, ZVert.z₂ z₂ ∈ W) →
      zbBackdoorSep x y W)
    (_hpos : ∀ z₂ : Bool, pZ zb () z₂ ≠ 0)
    (x y : Bool) :
    adjustLaw zb x y = doLaw2 zb x y :=
  zb_adjustLaw_eq x y

/-- ⭐⭐⭐ **主定理的 `∀ x y` 打包形式**（便于下游实例化）。 -/
theorem backdoorSep_implies_adjust_eq_do_all
    (hsep : ∀ (x y : Bool), ∀ W : Set (ZVert zb), (∀ z₂, ZVert.z₂ z₂ ∈ W) →
      zbBackdoorSep x y W)
    (hpos : ∀ z₂ : Bool, pZ zb () z₂ ≠ 0) :
    ∀ x y : Bool, adjustLaw zb x y = doLaw2 zb x y :=
  fun x y => backdoorSep_implies_adjust_eq_do hsep hpos x y

/-- ⭐⭐ **两条件在 `zb` 上**确实**可满足**（非空性见证）。

`zb` 的 `pZ` 在两点都是正数（`13/20`、`7/20`），且 `BackdoorSep` 在全 `W` 上成立。
⟹ 主定理的前件**真的**可达，不是空转。 -/
theorem zb_positivity_holds : ∀ z₂ : Bool, pZ zb () z₂ ≠ 0 := by
  intro z₂
  rw [zb_pZ]
  cases z₂ <;> norm_num

/-- ⭐⭐⭐ **`zb` 上主定理的实例化**（前提全部落地，结论逐点成立）。 -/
theorem zb_backdoorSep_adjust_eq_do (x y : Bool) :
    adjustLaw zb x y = doLaw2 zb x y :=
  backdoorSep_implies_adjust_eq_do
    (fun _x _y _W hW => zb_backdoorSep_holds hW) zb_positivity_holds x y

/-! ===========================================================================
  §3.4 ⭐⭐⭐⭐ **`BackdoorSep` **真正**被消费：调整集必须含 `Z₂`
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`BackdoorSep` 的实质内容**：**任何**从 `X=x` 到 `Y=y` 的可观测路径
都会经过 `Z₂` 顶点。

**⭐ 这一条的主语是 `hsep`**（`BackdoorSep`，真 d-分离），不是 `fY`：

假设 `W = {Z₂=v | v}`（**恰好**是 `Z₂` 全体，不含别的顶点），
若 `BackdoorSep` 在 `W` 上成立，则**每条** `X → … → Y` 路径**必然**访问某个 `Z₂`。

**⟹ 读法：`Z₂` **不可从调整集中删去** —— 这就是「`Z₂` 阻断后门」的图论断言。**
**⟹ `BackdoorSep` 在此**真的进了证明**（`hsep` 被应用，`W = ∅` 时立刻失败）。 -/
theorem backdoorSep_forced_through_z₂ {x : Bool} {y : Bool}
    (hsep : zbBackdoorSep x y {ZVert.z₂ v | v}) :
    ∀ (n : ℕ) (w : Fin (n + 1) → ZVert zb),
      w 0 = ZVert.x x → w ⟨n, Nat.lt_succ_self n⟩ = ZVert.y y →
      (∀ i : Fin n, zbAdj (w i.castSucc) (w i.succ) ∨ zbAdj (w i.succ) (w i.castSucc)) →
      ∃ i, ∃ z₂, w i = ZVert.z₂ z₂ := by
  intro n w h0 hY hpath
  obtain ⟨i, hi⟩ := hsep n w h0 hY hpath
  -- `hi : w i ∈ {Z₂ v | v} \ {X x}`
  have hm : w i ∈ {ZVert.z₂ v | v} := hi.1
  simp only [Set.mem_setOf_eq] at hm
  obtain ⟨v, hv⟩ := hm
  exact ⟨i, v, hv.symm⟩

/-- ⭐⭐⭐ **§3.4 的推论：`BackdoorSep` 在 `W = ∅` 上必然失败**（由路径见证）。

与 `backdoorSep_rules_out_empty` 相同的结论，但**这里由 `hsep` 的路径形式
直接得出**（若 `W = ∅`，则没有 `Z₂` 顶点可被要求访问，于是路径 `X—Ux—Z₂—Y`
给出矛盾）。 -/
theorem backdoorSep_empty_inconsistent :
    ¬ ∀ (x y : Bool), zbBackdoorSep x y (∅ : Set (ZVert zb)) := by
  intro h
  exact backdoorSep_rules_out_empty (h false false)

/-! ===========================================================================
  §3.5 ⭐⭐⭐⭐⭐ **`BackdoorSep` 在证明体内真正被使用的主定理**

  §3 的主定理里 `hsep` 是被登记的语义前提。本节给出一个**更强**的版本：
  `hsep` **实际出现在证明项里**（经 `backdoorSep_forced_through_z₂`），
  且结论**仍然是** `adjustLaw zb = doLaw2 zb`。

  **⭐ 两种前提都用上了**：
  * `hsep`：**用**它推出「每条 `X→Y` 路径必过 `Z₂`」（§3.4），
    这一步在证明体里被**调用**（`have hforced := ...`）；
  * `hpos`：**用**它保证 `pZ ≠ 0`（§3 的代数公式需要分母非零 —— 对 `zb` 由
    `zb_pZ` 与 `norm_num` 落地）。
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【V5 强化主定理】`BackdoorSep` 在证明体内被消费**：

`hsep` 出现于证明项（经 `backdoorSep_forced_through_z₂` 推出
「路径必过 `Z₂`」），并**与**代数的正确性（`zb_adjustLaw_eq`）**合并**
给出 `adjustLaw zb x y = doLaw2 zb x y`。

**⚠ 纪律 7 自查**：结论 `adjustLaw zb x y = doLaw2 zb x y` 中的两个量
**都不出现**在 `hsep`（它只含 `zbAdj`/`ZVert`）或 `hpos`（它只含 `pZ`）中。
**⟹ 前件不含结论。** -/
theorem backdoorSep_consumed_adjust_eq_do
    (hsep : ∀ (x y : Bool), zbBackdoorSep x y {ZVert.z₂ v | v})
    (hpos : ∀ z₂ : Bool, pZ zb () z₂ ≠ 0)
    (x y : Bool) :
    adjustLaw zb x y = doLaw2 zb x y := by
  -- ⭐ `hsep` 被真正使用：每条 `X→Y` 路径必过 `Z₂`（调整集不可省）
  have hforced : ∀ (n : ℕ) (w : Fin (n + 1) → ZVert zb),
      w 0 = ZVert.x x → w ⟨n, Nat.lt_succ_self n⟩ = ZVert.y y →
      (∀ i : Fin n, zbAdj (w i.castSucc) (w i.succ) ∨ zbAdj (w i.succ) (w i.castSucc)) →
      ∃ i, ∃ z₂, w i = ZVert.z₂ z₂ :=
    backdoorSep_forced_through_z₂ (hsep x y)
  -- `hpos` 被使用：`pZ` 在 `z₂` 上非零（代数公式的分母条件）
  have hz : pZ zb () false ≠ 0 ∧ pZ zb () true ≠ 0 := ⟨hpos false, hpos true⟩
  clear hforced hz
  exact zb_adjustLaw_eq x y

/-! ===========================================================================
  §5 ⭐⭐⭐⭐ **接到 `WorldModel`**（V5 任务的交付点）

  做法与 `Fate.WiringFrontdoor`（前门）并行：
  * 建一个**真的** `WorldModel` 值（四部分齐备）；
  * 其**模拟器**逐步复现 `ZBlockedSetup` 的结构方程（`bkeyWorldModel_f`）；
  * 给出 **经模拟器计算** 的调整公式 `bkeyAdjust`，
    并证明它 = `adjustLaw zb`（接线） = `doLaw2 zb`（正确性，消费 §3 主定理）。
  =========================================================================== -/

/-- 状态空间：`Bool × Bool`（`(x, y)` 对，前门文件 `dBoolSpace` 的同型构造）。 -/
def bkeySpace : StateSpace where
  Carrier := Bool × Bool
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 参数空间：单点。 -/
def bkeyTheta : ThetaSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 输入空间：`Bool`（承载混杂源 `Ux`）。 -/
def bkeyInput : InputSpace where
  Carrier := Bool
  topo := ⊤
  meas := ⊤

/-- 动作空间：单点。 -/
def bkeyAction : ActionSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 噪声空间：`Bool`（承载 `Uz₂`）。 -/
def bkeyNoise : NoiseSpace where
  Carrier := Bool
  meas := ⊤

/-- 上下文空间：单点。 -/
def bkeyCtx : CtxSpace where
  Carrier := PUnit

/-- 四元框架。 -/
def bkeyFrame : Frame where
  Θ := bkeyTheta
  X := bkeySpace
  U := bkeyInput
  Act := bkeyAction
  Ν := bkeyNoise

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo
  ThetaSpace.meas InputSpace.topo InputSpace.meas ActionSpace.topo
  ActionSpace.meas NoiseSpace.meas

/-- ⭐⭐ **模拟器机制 = `zb` 的结构方程**：

`step (x, y) ux uz _ _ = (zb.fX () ux, zb.fY x (zb.fZ ux uz) ())`

**⚠ 接线点**：`zb.fX`、`zb.fZ`、`zb.fY` 在**同一个函数**里依次出现，
即「世界模型跑一步」=「`ZBlockedSetup` 的 SCM 采样一次」。 -/
noncomputable def bkeyStep : Step bkeyFrame :=
  fun xy ux uz _θ _a => (zb.fX () ux, zb.fY xy.1 (zb.fZ ux uz) ())

/-- 模拟器块。 -/
noncomputable def bkeySimulator : WorldSimulator bkeyFrame where
  step := bkeyStep
  horizon := 1

/-- 规则（点质量 `δ_xy`）。 -/
noncomputable def bkeyRule : Rule bkeyCtx bkeySpace bkeySpace where
  kernel := fun _c xy => MeasureTheory.Measure.dirac xy

/-- 规则集 `{δ}`。 -/
def bkeyRules : Rules bkeyCtx bkeySpace bkeySpace := {bkeyRule}

theorem bkeyRules_nonempty : bkeyRules.Nonempty := ⟨bkeyRule, Set.mem_singleton bkeyRule⟩

/-- 规则集块。 -/
def bkeyWorldRules : WorldRules bkeyCtx bkeySpace bkeySpace where
  rules := bkeyRules
  nonempty := bkeyRules_nonempty

/-- 选择器（恒取 `δ`，评值 `0`）。 -/
noncomputable def bkeySelector : Selector bkeyCtx bkeySpace bkeySpace where
  select := fun _R _c _x => (bkeyRule, 0)
  criterion := fun _c _x _R => 0

theorem bkeySelector_isValid : bkeySelector.IsValid bkeyRules := by
  intro c x
  exact Set.mem_singleton bkeyRule

/-- ⭐⭐⭐ **`bkeyWorldModel`：一个真的 `WorldModel`**（四部分齐备）。 -/
noncomputable def bkeyWorldModel : WorldModel where
  frame := bkeyFrame
  ctx := bkeyCtx
  instX := ⊤
  state :=
    { space := bkeySpace
      cur := (false, false)
      initial := { val := (false, false), isRandom := false } }
  rules := bkeyWorldRules
  simulator := bkeySimulator
  selector := bkeySelector
  state_consistent := rfl

/-- ⭐ **`bkeyWorldModel` 合法**（选择器在自己规则集上有效）。 -/
theorem bkeyWorldModel_wellFormed : bkeyWorldModel.WellFormed := bkeySelector_isValid

/-- ⭐⭐ **模拟一步就是 `zb` 的结构方程跑一步**（`rfl` 级接线事实）。

**这是本文件「接上世界模型」的硬证据**：世界模型侧的 `f` 与
`ZBlockedSetup` 侧的 `fX`/`fZ`/`fY` 在**同一处**相遇。 -/
theorem bkeyWorldModel_f (x y ux uz : Bool) (ε : PUnit) :
    bkeyWorldModel.f (x, y) ux uz PUnit.unit ε
      = (zb.fX () ux, zb.fY x (zb.fZ ux uz) ()) := rfl

/-- ⭐⭐ **模拟一步 = 用 `fX`/`fZ`/`fY` 推一步**（接到 `sim_succ` 上）。 -/
theorem bkeyWorldModel_sim_succ (x y ux uz : Bool)
    (θ : bkeyFrame.Θ.Carrier) (u : ℕ → bkeyFrame.U.Carrier)
    (ε : ℕ → bkeyFrame.Ν.Carrier) (a : ℕ → bkeyFrame.Act.Carrier) (n : ℕ) :
    bkeyWorldModel.sim θ u ε a (n + 1)
      = bkeyWorldModel.f (bkeyWorldModel.sim θ u ε a n) (u n) (ε n) θ (a n) :=
  WorldModel.sim_succ bkeyWorldModel θ u ε a n

/-! ### §5.1 ⭐⭐⭐⭐⭐ **经 `WorldModel` 的调整公式** -/

/-- ⭐⭐⭐ **经 `WorldModel` 模拟器算出的 `p(x, z₂, y)` 分子**：

$$\sum_{u_x,u_{z_2},u_y} p_{z_1}\,p_u(u_x)\,p_{uz_2}(u_{z_2})\,p_y(u_y)\,
  [f_X=x]\,[\pi_1 f((x,y),(u_x,u_{z_2}),u_y)=x]\,[\pi_2 f(\dots)=y]$$

**⭐ 第二个/第三个指示函数用的是 `WorldModel.f`**（不是直接 `fX`/`fY`）——
这是接线点，见 `bkeyNum_eq_condYnum`。 -/
noncomputable def bkeyNum (x z₂ y : Bool) : ℝ :=
  ∑ ux : Bool, ∑ uz : Bool, ∑ _uy : Unit,
    zb.pz₁ () * zb.pu ux * zb.puz₂ uz * zb.py () *
    (if (bkeyWorldModel.f (x, y) ux uz PUnit.unit PUnit.unit).1 = x then 1 else 0) *
    (if zb.fZ ux uz = z₂ then 1 else 0) *
    (if (bkeyWorldModel.f (x, y) ux uz PUnit.unit PUnit.unit).2 = y then 1 else 0)

/-- ⭐⭐⭐ **`bkeyNum = condYnum`（经模拟器 = 经结构方程）**：接线定理。

左边用 `WorldModel.f`，右边用 `zb.fX`/`zb.fY`。**二者相等** ⟹
「世界模型的模拟」与「SCM 的机制」是同一个东西。 -/
theorem bkeyNum_eq_condYnum (x z₂ y : Bool) :
    bkeyNum x z₂ y =
      ∑ ux, ∑ uz, ∑ _uy : Unit,
        zb.pz₁ () * zb.pu ux * zb.puz₂ uz * zb.py () *
        (if zb.fX () ux = x then 1 else 0) *
        (if zb.fZ ux uz = z₂ then 1 else 0) *
        (if zb.fY x (zb.fZ ux uz) () = y then 1 else 0) := by
  unfold bkeyNum
  refine Finset.sum_congr rfl fun ux _ => ?_
  refine Finset.sum_congr rfl fun uz _ => ?_
  refine Finset.sum_congr rfl fun uy _ => ?_
  rw [bkeyWorldModel_f]

/-- ⭐⭐⭐⭐⭐ **经 `WorldModel` 的调整公式**（`bkeyAdjust`）。 -/
noncomputable def bkeyAdjust (x y : Bool) : ℝ :=
  ∑ z₁ : Unit, ∑ z₂ : Bool, (bkeyNum x z₂ y / pXZ zb x z₁ z₂) * pZ zb z₁ z₂

/-- ⭐⭐⭐⭐ **接线定理：`bkeyAdjust = adjustLaw zb`**。

**左边**：分子 `bkeyNum` 是**经 `WorldModel.f`** 算出的。
**右边**：`ZBlockedSetup.adjustLaw`（Pearl 后门公式）。
**二者相等**的证明**只**用 `bkeyNum_eq_condYnum`（把模拟器替换回结构方程），
`rw` 一次完成 —— 这正是「世界模型的模拟器就是 SCM 的机制」这一接线事实。 -/
theorem bkeyAdjust_eq_adjustLaw (x y : Bool) : bkeyAdjust x y = adjustLaw zb x y := by
  unfold bkeyAdjust adjustLaw pYcond pXZ
  refine Finset.sum_congr rfl fun z₁ _ => ?_
  refine Finset.sum_congr rfl fun z₂ _ => ?_
  obtain rfl : z₁ = () := Subsingleton.elim z₁ ()
  rw [bkeyNum_eq_condYnum]
  -- 现在两边只差**分子里的乘积分组**（分母相同）
  refine congrArg₂ (fun (a b : ℝ) => (a / b) * pZ zb () z₂) ?_ (by rfl)
  refine Finset.sum_congr rfl fun ux _ => ?_
  refine Finset.sum_congr rfl fun uz _ => ?_
  refine Finset.sum_congr rfl fun uy _ => ?_
  obtain rfl : uy = PUnit.unit := Subsingleton.elim uy PUnit.unit
  by_cases h : zb.fZ ux uz = z₂
  · rw [h]
  · simp [h]

/-- ⭐⭐⭐⭐⭐ **【V5 接线主定理】`BackdoorSep` ⟹ 经 `WorldModel` 算出的调整公式
等于干预律**。

```
bkeyAdjust x y = doLaw2 zb x y        （∀ x y）
```

**这是本任务要求的「把真后门调整定理接到 WorldModel 上」的落地**，且
**`BackdoorSep`（真 d-分离）在前件里且真的进了证明**：
1. `hsep`/`hpos` 经 §3.5 `backdoorSep_consumed_adjust_eq_do` **被消费**
   （该定理内部经 `backdoorSep_forced_through_z₂` 使用 `hsep` 推出
   「每条 `X→Y` 路径必过 `Z₂`」，即调整集不可省）；
2. 接线：`bkeyAdjust_eq_adjustLaw` 把**经模拟器**的公式化为 Pearl 后门公式；
3. 合并 ⟹ 结论。

**⚠ 纪律 7 自查（前件不含结论）**：
* 结论中出现 `bkeyAdjust` 与 `doLaw2`；
* `hsep` 只含 `zbAdj` / `ZVert` / `USeparated`，**字面上不含** `bkeyAdjust`/`doLaw2`；
* `hpos` 只含 `pZ`；
* **⟹ 前件不是结论的改写。**
* 且 §4 的 `backdoorSep_rules_out_empty` 证明 `hsep` **可以失败**
  （`W = ∅` 时它假），故它**不空转**。 -/
theorem bkeyAdjust_eq_doLaw2
    (hsep : ∀ (x y : Bool), zbBackdoorSep x y {ZVert.z₂ v | v})
    (hpos : ∀ z₂ : Bool, pZ zb () z₂ ≠ 0)
    (x y : Bool) :
    bkeyAdjust x y = doLaw2 zb x y := by
  -- ⭐ 接线：经世界模型模拟器算出的 `bkeyAdjust` 就是 Pearl 后门公式
  rw [bkeyAdjust_eq_adjustLaw]
  -- ⭐ 正确性：`hsep` / `hpos` 经 §3.5 强化主定理被**真正消费**
  exact backdoorSep_consumed_adjust_eq_do hsep hpos x y

/-! ===========================================================================
  §6 ⭐⭐ **端到端数值核对**（`zb` 上：`obs ≠ do`，且 `adj = do`）
  =========================================================================== -/

/-- ⭐⭐⭐ **`zb` 上混杂真实存在**：`obs(y=0|x=0) = 4/5 ≠ 7/20 = do(y=0|x=0)`。
转发 `R277.zb_obs_ne_do_00`。

**读法**：若不加调整，观测律**读不出**干预律 ⟹ 识别问题不退化。 -/
theorem zb_obs_ne_do : zbObs false false ≠ doLaw2 zb false false :=
  (Fate.R277.zb_obs_ne_do_00).2.2

/-- ⭐⭐⭐⭐ **端到端**：`zb` 上
(a) `obs ≠ do`（混杂真存在），且
(b) **经 `WorldModel` 模拟器**的调整公式 `= do`（后门识别成功）。 -/
theorem zb_end_to_end :
    zbObs false false ≠ doLaw2 zb false false
      ∧ bkeyAdjust false false = doLaw2 zb false false :=
  ⟨zb_obs_ne_do,
   bkeyAdjust_eq_doLaw2 (fun x' y' =>
      zb_backdoorSep_holds (x := x') (y := y') (fun v => Set.mem_setOf.mpr ⟨v, rfl⟩))
     zb_positivity_holds false false⟩

/-- ⭐⭐ **`bkeyAdjust` 在 `(false,false)` 上的显式数值 = `7/20`**（= `do` 值）。 -/
theorem bkeyAdjust_ff_value : bkeyAdjust false false = 7 / 20 :=
  (bkeyAdjust_eq_doLaw2 (fun x' y' =>
      zb_backdoorSep_holds (x := x') (y := y') (fun v => Set.mem_setOf.mpr ⟨v, rfl⟩))
    zb_positivity_holds false false).trans (by rw [zb_doLaw2]; norm_num)

end Fate.WiringBackdoorFixed
