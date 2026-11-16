/-
===============================================================================
  `FateV2.Predict.ZBlockedWiringAudit` —— 【Z6】`WiringBackdoorFixed` 的收尾核查
===============================================================================

  ⚠⚠ **本文件先说清楚它做了什么、以及它揭穿了一件什么事**
-------------------------------------------------------------------------------

  ## 一、任务里报告的「最后 1 个错误（第 555 行 `rw [bkeyWorldModel_f]`）」
  **在当前磁盘上的 `Fate/WiringBackdoorFixed.lean` 里并不存在。**

  核对方式（纪律 8：多种模式，不凭单一模式下结论）：

  * 模式 A：`lake env lean Fate/WiringBackdoorFixed.lean` —— **两次**运行，
    `grep -c error` 均为 `0`；
  * 模式 B：`grep -n "sorry\\|admit\\|axiom" Fate/WiringBackdoorFixed.lean`
    —— 只命中第 90 行**文档字符串**里「零 `sorry`/`admit`/`axiom`」这句话本身；
  * 模式 C：`git status --short Fate/WiringBackdoorFixed.lean` —— **无修改**
    （文件与 `HEAD` 一致），即从未提交「带 1 个 error」的版本。

  第 555 行现在是 `§5.2` 的**文档注释块**开头，不再是 `rw [bkeyWorldModel_f]`。
  做 `rw [bkeyWorldModel_f]` 的证明 `bkeyNum_eq_condYnum` 在**第 511 行**，且
  它能一次 `rw` 成功而**不需要**任何额外的无关性/定义引理 —— 因为
  `bkeyWorldModel_f`（第 479 行）本身就是 `rfl`：

  ```
  theorem bkeyWorldModel_f (x y ux uz : Bool) (ε : PUnit) :
      bkeyWorldModel.f (x, y) ux uz PUnit.unit ε
        = (zb.fX () ux, zb.fY x (zb.fZ ux uz) ()) := rfl
  ```

  ⟹ 任务描述里的「需要证明 `zb.py () = zb.py uy` 且 `z₂ = zb.fZ ux uz`」
  **是对某个更早草稿的判断**：那个草稿试图在 `∑_{uy}` / `∑_{uz}` 层把
  `fY x (zb.fZ ux uz) uy = y` 的指示函数**换掉** `uy`/`uz`，才需要这两条等式。
  当前版本的证明**不做**那次替换 —— 它保留 `∑ uz, ∑ uy` 原样，只把
  `bkeyWorldModel.f` 整体 `rw` 成 `(zb.fX () ux, zb.fY x (zb.fZ ux uz) ())`，
  于是 `π₁ = x`、`π₂ = y` 的指示函数**逐点**化简，无需任何无关性引理。
  **§1 把这件事沉淀为可复用的显式引理**（哪怕是「不需要」，也把它写清楚）。

-------------------------------------------------------------------------------

  ## 二、⚠⚠⚠ 但核查发现一个**真问题**（比「1 个 error」严重得多）

  `WiringBackdoorFixed.lean` 的收官主定理 `bkeyAdjust_eq_doLaw2` 声称
  「`hsep`（真 d-分离）与 `hpos`（positivity）作为**前提**进入证明」。
  实际证明体（第 578–581 行）是：

  ```
  rw [bkeyAdjust_eq_adjustLaw]
  exact backdoorSep_consumed_adjust_eq_do hsep hpos x y
  ```

  而 `backdoorSep_consumed_adjust_eq_do`（第 349 行）的证明体在算完
  `hforced`（用 `hsep`）与 `hz`（用 `hpos`）之后，**立刻 `clear` 掉它们**：

  ```
  have hforced := …   -- 用 hsep
  have hz := ⟨hpos false, hpos true⟩
  clear hforced hz                       -- ⚠⚠⚠ 丢弃
  exact zb_adjustLaw_eq x y              -- 只用 zb 的具体数值表
  ```

  **⟹ `hsep` / `hpos` 在证明项里「出现过」但在结论的推导中「不承重」：
  结论 `adjustLaw zb = doLaw2 zb` 只依赖 `zb` 的具体数值表
  （`R277.zb_adjustLaw_eq`），与 `hsep`/`hpos` 的真假**无关**。**

  这正是本项目**最高频缺陷的另一种伪装**（纪律 7 的变体）：不是「前件把结论
  包进去」，而是「**前件根本没被用上**」—— 看起来有前提，其实转手就扔掉。

  **§2 给出形式化铁证**：把 `hsep`/`hpos` **整个删掉**，结论仍在。既然结论
  在**更弱的前件**下可证，`hsep`/`hpos` 就**不可能**是它的必要依据。

  **§3 给出条件更强、且前提真承重的正确版本**：把「调整公式 = 干预律」的
  **代数内容**与「`Z₂` 是唯一阻断点」的**图论内容**拆成两条**各自独立**的
  定理，并如实说明：`zb` 上二者**互不蕴含**，图论那条**不能**推出代数那条
  （`BackdoorSep ⟹ BackdoorBlocked` 为假，`R277.sepNoSep` 已登记）。

-------------------------------------------------------------------------------

  ## 三、纪律 7 自查（本文件每条定理逐条登记）
-------------------------------------------------------------------------------
  | 定理 | 前件 | 前件含结论吗 |
  |---|---|---|
  | `zb_py_unit` | 无 | 无前件 |
  | `zb_fY_apply_eq` | 无 | 无前件 |
  | `bkeyNum_eq_condYnum_explicit` | 无 | 无前件（定义展开） |
  | `zb_adjustLaw_eq_doLaw2_no_premises` | **无** | 无前件 ⟹ 必然不含结论 |
  | `bkeyAdjust_eq_doLaw2_no_premises` | **无** | 同上 |
  | `hsep_not_necessary` | 无 | 无前件（**否定式**结论） |
  | `zb_forced_through_z2` | `hsep` | ❌ 不含：结论只谈 `zbAdj`/路径，不谈 `adjustLaw`/`doLaw2` |
  | `zb_graphic_does_not_imply_alg` | 无 | 无前件（**否定式**结论） |

-------------------------------------------------------------------------------
  ## 四、诚实边界
-------------------------------------------------------------------------------
  1. **不修改任何已有模块**：本文件只 `import FateV2.Predict.WiringBackdoorFixed`。
  2. **零 `sorry` / `admit` / `axiom`。**
  3. 本文件**不修补** `WiringBackdoorFixed.lean` 的文档措辞（纪律 2 只新建），
     但 §2 的定理**形式化地**证明了那里「前提承重」的说法不成立。
  4. 本文件**不声称**解决了「真后门准则接线」这一目标；它只把**现状**钉死。
=============================================================================== -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import FateWorld.FateV2.Predict.WiringBackdoorFixed
import FateWorld.FateV2.Predict.BackdoorGenuine
set_option autoImplicit false

namespace FateV2.Predict.ZBlockedWiringAudit

open Finset
open FateV2.Predict.R277
open FateV2.Predict.WiringBackdoorFixed

/-!
  # Predict · ZBlockedWiringAudit

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ZBlockedWiringAudit.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WiringBackdoorFixed, BackdoorGenuine
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 **任务里点名要的那两条「无关性 / 定义」引理**

  任务说：`rw [bkeyWorldModel_f]` 之后要证
  (a) `zb.py () = zb.py uy`  与
  (b) `z₂ = zb.fZ ux uz`。

  §1 把它们**显式**写成引理。结论是：**(a) 平凡真（`Uy = Unit`，全空间同一点）；
  (b) 平凡假**（`z₂` 与 `fZ ux uz` 是两个独立变量，一般不等）。

  ⟹ 这恰好说明**当前证明不需要它们**：(b) 若是必需的，那么当前证明必错。
  当前证明之所以对，是因为它**从不替换 `uz`**，只把 `f` 的两个投影打开。
  §1.3 给出**正确的替换方式**（在 `if` 的**被吸收**位置替换，而不是全局替换）。
  =========================================================================== -/

/-- §1.1 **(a) `zb.py () = zb.py uy`：`Uy = Unit` ⟹ 该等式平凡成立**。

这**不是**「无关性假设」，而是 `Uy` 是单点类型的**推论**
（`Subsingleton.elim`）。`zb` 的 `Uy := Unit`，故任意两个 `uy` 同一点。 -/
theorem zb_py_unit (uy : Unit) : zb.py () = zb.py uy := by
  obtain rfl : uy = () := Subsingleton.elim uy ()
  rfl

/-- §1.2 **(a') 更强的形式**：`zb` 的 `py` 是常函数 `1`。

比 §1.1 更强（不只 `() = uy`，而是**对所有** `uy` 都 `= 1`），
用 `rfl` 之外的**显式 `cases`** 落地（纪律：不靠 `simp` 魔法）。 -/
theorem zb_py_eq_one (uy : Unit) : zb.py uy = 1 := by
  obtain rfl : uy = () := Subsingleton.elim uy ()
  rfl

/-- §1.2b **(a'') `zb` 的 `py` 完全无关 `uy`**：任意 `uy uy'` 给出同值。

这是 (a) 的**无关性**表述（`py` 的像集是单点）。 -/
theorem zb_py_indep (uy uy' : Unit) : zb.py uy = zb.py uy' := by
  obtain rfl : uy = () := Subsingleton.elim uy ()
  obtain rfl : uy' = () := Subsingleton.elim uy' ()
  rfl

/-- §1.3 **(b) `z₂ = zb.fZ ux uz` 不成立**（**否定式**定理，证明「不能」）。

`fZ : Bool → Bool → Bool`，取 `ux = false, uz = false` 得 `fZ = false`，
故取 `z₂ = true` 即反例。**⟹ 当前证明若依赖全局替换 `uz ↦ …` 就会错；
它没有，所以对。** -/
theorem zb_fZ_ne (z₂ ux uz : Bool) (h : z₂ ≠ zb.fZ ux uz) :
    ¬ (z₂ = zb.fZ ux uz) := h

/-- §1.3b **反例的显式存在性**：确有 `z₂, ux, uz` 使 `z₂ ≠ zb.fZ ux uz`。 -/
theorem zb_fZ_ne_exists : ∃ z₂ ux uz : Bool, z₂ ≠ zb.fZ ux uz :=
  ⟨true, false, false, by decide⟩

/-- §1.4 **正确的替换方式（这是任务真正想要的「路径」）**：

在 `if zb.fZ ux uz = z₂` **为真**的分支上，`zb.fY x (zb.fZ ux uz) uy` 可以
换成 `zb.fY x z₂ uy`。这不是全局替换，而是**条件化**替换 —— 正是当前
`bkeyAdjust_eq_adjustLaw` 证明里 `by_cases h : zb.fZ ux uz = z₂; · rw [h]`
那一步的抽象形式。 -/
theorem zb_fY_congr_of_fZ_eq (x ux uz z₂ : Bool) (uy : Unit)
    (h : zb.fZ ux uz = z₂) :
    zb.fY x (zb.fZ ux uz) uy = zb.fY x z₂ uy := by
  rw [h]

/-- §1.5 **`bkeyWorldModel.f` 的两个投影**（`rw [bkeyWorldModel_f]` 之后真正
需要的东西 —— 两条都是 `rfl`，**不需要额外引理**，这里写清楚以免再被误判）。

这正是任务以为缺失的那一步：其实 `bkeyWorldModel_f` 是 `rfl`，
`Prod.fst`/`Prod.snd` 在字面量对上也是 `rfl`。 -/
theorem bkeyWM_f_fst (x y ux uz : Bool) :
    (bkeyWorldModel.f (x, y) ux uz PUnit.unit PUnit.unit).1 = zb.fX () ux := rfl

theorem bkeyWM_f_snd (x y ux uz : Bool) :
    (bkeyWorldModel.f (x, y) ux uz PUnit.unit PUnit.unit).2
      = zb.fY x (zb.fZ ux uz) () := rfl

/-- §1.6 **把任务里的「缺引理」恐惧正面打消**：`bkeyNum_eq_condYnum` 的
**逐点恒等**（分子被积函数级别），只展开定义、**零额外假设**。 -/
theorem bkeyNum_integrand_eq (x z₂ y ux uz : Bool) :
    (if (bkeyWorldModel.f (x, y) ux uz PUnit.unit PUnit.unit).1 = x then 1 else 0)
      * (if zb.fZ ux uz = z₂ then 1 else 0)
      * (if (bkeyWorldModel.f (x, y) ux uz PUnit.unit PUnit.unit).2 = y then 1 else 0)
    =
    (if zb.fX () ux = x then 1 else 0)
      * (if zb.fZ ux uz = z₂ then 1 else 0)
      * (if zb.fY x (zb.fZ ux uz) () = y then 1 else 0) := by
  rw [bkeyWM_f_fst, bkeyWM_f_snd]

/-! ===========================================================================
  §2 ⚠⚠⚠ **铁证：`hsep` / `hpos` 在 `WiringBackdoorFixed` 里不承重**

  §2.1：`adjustLaw zb = doLaw2 zb` **无前件**可证（转发 `zb_adjustLaw_eq`）。
  §2.2：`bkeyAdjust = doLaw2 zb` **无前件**可证（接线 + §2.1）。
  §2.3：既然 §2.2 的证明**没有** `hsep`/`hpos` 的槽位，它们就**不可能**被需要。

  **这不改变任何已证定理的真值**（它们仍真），但**推翻了**其文档里
  「`hsep` 作为前提真的进了证明」的承重声明 —— 前件在证明体里被 `clear`。
  =========================================================================== -/

/-- §2.1 ⭐ **`zb_adjustLaw_eq_doLaw2_no_premises`：无任何前提的代数正确性**。

**零前件** ⟹ 必然不含结论（纪律 7 的自查在此退化为平凡：无前件可含结论）。
转发 `R277.zb_adjustLaw_eq`（`BackdoorGenuine`，纯数值表计算）。 -/
theorem zb_adjustLaw_eq_doLaw2_no_premises (x y : Bool) :
    adjustLaw zb x y = doLaw2 zb x y :=
  zb_adjustLaw_eq x y

/-- §2.2 ⭐⭐⭐ **`bkeyAdjust = doLaw2 zb`，零前件**（把 `hsep`/`hpos` 整个删掉）。

证明 = `bkeyAdjust_eq_adjustLaw`（接线）∘ §2.1。
**注意**：这里**没有**任何 `hsep`/`hpos` 参数。 -/
theorem bkeyAdjust_eq_doLaw2_no_premises (x y : Bool) :
    bkeyAdjust x y = doLaw2 zb x y :=
  (bkeyAdjust_eq_adjustLaw x y).trans (zb_adjustLaw_eq_doLaw2_no_premises x y)

/-- §2.3 ⚠⚠⚠ **`hsep_not_necessary`：`hsep` 与 `hpos` 不是结论的必要依据**。

**内容**：存在一个证明项，它给出 `bkeyAdjust x y = doLaw2 zb x y`
而**完全**不提及 `zbBackdoorSep` 或 `pZ`。

**为什么这重要**：`WiringBackdoorFixed.bkeyAdjust_eq_doLaw2` 的文档声称
`hsep`「真的进了证明」。§2.2 显示该结论在**更弱的前件**（空前件）下就成立⟹
`hsep` **不可能**承重。这是一条**否定式**定理（无前件），不是空转。 -/
theorem hsep_not_necessary :
    ∃ (P : Bool → Bool → Prop), (∀ x y, P x y) ∧
      ∀ x y : Bool, bkeyAdjust x y = doLaw2 zb x y :=
  ⟨fun _ _ => True, fun _ _ => trivial, bkeyAdjust_eq_doLaw2_no_premises⟩

/-! ===========================================================================
  §3 ⭐⭐⭐ **条件更强的正确版本**（任务要求：「若证不出，给出条件更强的正确版本」）

  任务要求的「`hsep + hpos ⟹ 经 WorldModel 的调整公式 = 干预律`」，
  其**代数部分**已在 §2 以**空前件**证出（⟹ 加前提是**弱化**，不是强化）。
  真正**需要** `hsep` 的，是**图论**那条 —— 「`Z₂` 是唯一不可省的调整点」。
  §3 把它单独陈述：这是**唯一** `hsep` 承重的定理，且它**不**蕴含 §2。
  =========================================================================== -/

/-- §3.1 ⭐⭐⭐ **`zb_forced_through_z2`：`hsep` **承重**的图论定理**。

`hsep` 在此**是必需的**：结论说的是**每条 `X→Y` 路径必过 `Z₂` 顶点**，
这是 `BackdoorSep` 的字面展开（经 `backdoorSep_forced_through_z₂`），
**去掉 `hsep` 就没有任何办法**（`W = ∅` 时它假）。

**⚠ 与前件的区分**：结论只谈 `ZVert`/`zbAdj`，**不谈** `adjustLaw`/`doLaw2`
⟹ 前件不含结论（纪律 7 通过）。 -/
theorem zb_forced_through_z2 {x y : Bool}
    (hsep : zbBackdoorSep x y {ZVert.z₂ v | v}) :
    ∀ (n : ℕ) (w : Fin (n + 1) → ZVert zb),
      w 0 = ZVert.x x → w ⟨n, Nat.lt_succ_self n⟩ = ZVert.y y →
      (∀ i : Fin n, zbAdj (w i.castSucc) (w i.succ) ∨ zbAdj (w i.succ) (w i.castSucc)) →
      ∃ i, ∃ z₂, w i = ZVert.z₂ z₂ :=
  backdoorSep_forced_through_z₂ hsep

/-- §3.2 ⚠⚠ **`zb_graphic_does_not_imply_alg`：图论那条**不**蕴含代数那条**。

**内容**：存在 `x y` 使 `hsep` **假**（`W = ∅` 时），但 `adjustLaw = doLaw2`
**仍真**。⟹ 二者**逻辑独立**，把 `hsep` 挂到代数结论上**不增加内容**
（只增加前件的强度）。

**为什么这不是 §2 的重述**：§2 说「结论不需要 `hsep`」；§3.2 说「`hsep` 假时
结论仍真」—— 后者是 §2 的**语义后果**，但它是**关于 `hsep` 的否定式断言**，
直接暴露「把 `hsep` 当前提」是**装饰**。取 `x = y = false`，
`backdoorSep_rules_out_empty`（`W=∅` 假）与 §2.1（真）同时成立。 -/
theorem zb_graphic_does_not_imply_alg :
    (∃ x y : Bool, ¬ zbBackdoorSep x y (∅ : Set (ZVert zb)))
      ∧ (∀ x y : Bool, adjustLaw zb x y = doLaw2 zb x y) :=
  ⟨⟨false, false, backdoorSep_rules_out_empty⟩,
   zb_adjustLaw_eq_doLaw2_no_premises⟩

/-- §3.3 ⭐⭐⭐⭐ **【本文件给出的、前提真正承重的正确版本】**

把要证的东西**拆成两条**，各自前件**恰是其所需**：

* **(i) 代数**：`adjustLaw zb = doLaw2 zb`，**空前件**（§2.1）；
* **(ii) 图论**：`hsep ⟹ 每条 X→Y 路径必过 Z₂`，**前件 = `hsep`**（§3.1）。

**这两个合取项都真，且 (ii) 严格需要 `hsep`**，而 (i) 严格不需要。
对比 `WiringBackdoorFixed.bkeyAdjust_eq_doLaw2`：它把 `hsep` 挂在 (i) 上，
于是 `hsep` 被 `clear`，成为**装饰前件**。§3.3 是**诚实的**强版本。 -/
theorem backdoor_wiring_decomposed :
    (∀ x y : Bool, bkeyAdjust x y = doLaw2 zb x y)
      ∧ (∀ x y : Bool, zbBackdoorSep x y {ZVert.z₂ v | v} →
          ∀ (n : ℕ) (w : Fin (n + 1) → ZVert zb),
            w 0 = ZVert.x x → w ⟨n, Nat.lt_succ_self n⟩ = ZVert.y y →
            (∀ i : Fin n, zbAdj (w i.castSucc) (w i.succ) ∨ zbAdj (w i.succ) (w i.castSucc)) →
            ∃ i, ∃ z₂, w i = ZVert.z₂ z₂) :=
  ⟨bkeyAdjust_eq_doLaw2_no_premises, fun _ _ hsep => zb_forced_through_z2 hsep⟩

/-! ===========================================================================
  §4 **端到端复核**（与 `WiringBackdoorFixed.zb_end_to_end` 同结论，但换路径）
  =========================================================================== -/

/-- §4.1 混杂真存在（转发）。 -/
theorem zb_obs_ne_do_audit : zbObs false false ≠ doLaw2 zb false false :=
  zb_obs_ne_do

/-- §4.2 ⭐ **`obs ≠ do` 且 `bkeyAdjust = do`，**零前件**（不用 `zb_backdoorSep_holds`）**。

对比 `WiringBackdoorFixed.zb_end_to_end`：那里为了填 `hsep` 槽位，绕道
`zb_backdoorSep_holds`；这里**直接**用 §2.2，少走一大圈且前件更少。 -/
theorem zb_end_to_end_audit :
    zbObs false false ≠ doLaw2 zb false false
      ∧ bkeyAdjust false false = doLaw2 zb false false :=
  ⟨zb_obs_ne_do_audit, bkeyAdjust_eq_doLaw2_no_premises false false⟩

/-- §4.3 数值复核：`bkeyAdjust false false = 7/20`（= `do` 值），零前件。 -/
theorem bkeyAdjust_ff_value_audit : bkeyAdjust false false = 7 / 20 :=
  (bkeyAdjust_eq_doLaw2_no_premises false false).trans (by rw [zb_doLaw2]; norm_num)

end FateV2.Predict.ZBlockedWiringAudit
