import FateWorld.Legacy.SetupXMYDemo

/-! ===========================================================================
  `Fate/SetupXMYDemoLaw` —— `demoX` 的**数值表**与**两个否证定理**

  ## ⭐ 修定说明（第 302 轮）

  本文件在第 299 轮被创建为一个**不能编译的空壳**：doc-comment 声称交付
  `adjustLawZ_eq_doLaw`（后门正确）与 `adjustLawM_ne_doLaw`（中介偏误），
  但**两条定理都不存在**，且仅有的 4 条 `simp` 引理（`jointDo_val` /
  `doLaw_val` / `doLaw_00` …）**全部编译失败**。本轮的处置：

  1. **删除**那条**假的**闭式 `jointDo x z m y = pxB x * pyB false` ——
     实测反例 `(x,z,m,y) = (false,false,false,true)`：左 `= 9/20`，右 `= 1/20`。
  2. **删除**那条**假的** `doLaw_val : doLaw x y = pxB x` —— 实测
     `doLaw true false = 21/50 ≠ 9/10`。
  3. **删除** doc-comment 里的 `adjustLawZ_eq_doLaw` —— 它在 `demoX` 上
     **为假**（`adjustLawZ false false = 21/100 ≠ 1/2 = doLaw false false`）。
     **这不是编程疏忽，而是数学事实**：`demoX` 在 `SetupXMY` 载体上
     **有 `X → Y` 直达边**，故 `{Z}` 后门调整**不成立**。`SetupXMY`
     的 doc-comment 已经预告「Pearl (i) 在此载体上真起作用」，
     本文件把这句话**变成数值反例**。
  4. **保留并证明**每条数值等式（`norm_num` 在全 `Bool` 字面量上收敛）。

  ## 数值表（§1，机器可验；**与第 299 轮的旧表不同**）

  | `x` `y` | `doLaw` | `adjustLawZ` | `adjustLawM` |
  |---|---|---|---|
  | 0 0 | 1/2 | 21/100 | 21/200 |
  | 0 1 | 1/2 | 21/100 | 21/200 |
  | 1 0 | 21/50 | 0 | 0 |
  | 1 1 | 29/50 | 29/50 | 29/100 |

  ⚠ `adjustLawZ` **只在 `x = 1, y = 1` 一行**与 `doLaw` 重合；
  `(0,0)` / `(0,1)` 偏 `−29/100`，`(1,0)` 偏 `−21/50`。

  ## 主定理（§2）

  * `adjustLawZ_ne_doLaw` —— ⚠⚠ **`{Z}` 后门调整在 `demoX` 上失败**
    （有 `X → Y` 直达边）。这**推翻了**第 299 轮空壳声称的「后门正确」。
  * `adjustLawM_ne_doLaw` —— ⚠ **中介调整失败**（`M` 是 `X` 的后代，
    符合 Pearl (ii) 的警示）。

  ## 诚实边界

  * 本文件**只**做有限 `Bool` 上的**数值**核验，不给出任何一般性定理。
  * `pz`/`px`/`py` 在本 demo 里恰归一（各 `∑ = 1`），但定理不依赖归一性。
  * **无** `sorry` / `admit` / `axiom`。
-/

namespace Fate.SetupXMY
namespace DemoX

open Finset

/-! ### §0 归约工具

⚠ 关于 `⊢ False` 的成因：`Bool.xor` 是 `implicit_reducible`，
`decide`/`rfl` 在**自由变量**下不可靠。故每条数值引理只用
`unfold` + `Fintype.sum_bool`（4 次，对应 `ux, uy, z, m` 的求和）
把求和**展开成 32 项字面量**，再交给 `norm_num`。 -/

/-- `xor` 与「相等」互斥：`(a ⊕ b) = false ⟺ a = b`。 -/
theorem xor_eq_false_iff (a b : Bool) : (Bool.xor a b = false) ↔ (a = b) := by
  cases a <;> cases b <;> simp

/-- `xor` 与「不等」一致：`(a ⊕ b) = true ⟺ a ≠ b`。 -/
theorem xor_eq_true_iff (a b : Bool) : (Bool.xor a b = true) ↔ (a ≠ b) := by
  cases a <;> cases b <;> simp

/-! ### §1 基本求值引理 -/

/-- `pxB false = 1/10`。 -/
theorem pxB_false : pxB false = 1 / 10 := by unfold pxB; rw [if_pos rfl]

/-- `pxB true = 9/10`。 -/
theorem pxB_true : pxB true = 9 / 10 := by
  unfold pxB; rw [if_neg (by decide : ¬ ((true : Bool) = false))]

/-- `pzB false = 3/5`。 -/
theorem pzB_false : pzB false = 3 / 5 := by unfold pzB; rw [if_pos rfl]

/-- `pzB true = 2/5`。 -/
theorem pzB_true : pzB true = 2 / 5 := by
  unfold pzB; rw [if_neg (by decide : ¬ ((true : Bool) = false))]

/-- `pyB` 恒为 `1/2`。 -/
theorem pyB_val (uy : Bool) : pyB uy = 1 / 2 := by unfold pyB; rfl

/-! ### §2 ⭐⭐⭐ 数值表：`doLaw` -/

/-- ⭐ `doLaw(0,0) = 1/2`。 -/
theorem doLaw_00 : doLaw false false = 1 / 2 := by
  unfold doLaw jointDo fMB fYB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-- ⭐ `doLaw(0,1) = 1/2`。 -/
theorem doLaw_01 : doLaw false true = 1 / 2 := by
  unfold doLaw jointDo fMB fYB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-- ⭐ `doLaw(1,0) = 21/50`（⚠ 不是第 299 轮旧表所写的 `1/10`）。 -/
theorem doLaw_10 : doLaw true false = 21 / 50 := by
  unfold doLaw jointDo fMB fYB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-- ⭐ `doLaw(1,1) = 29/50`（⚠ 不是第 299 轮旧表所写的 `9/10`）。 -/
theorem doLaw_11 : doLaw true true = 29 / 50 := by
  unfold doLaw jointDo fMB fYB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-! ### §3 ⭐⭐⭐ 数值表：`adjustLawZ`（`{Z}` 后门调整） -/

/-- `adjustLawZ(0,0) = 21/100`。 -/
theorem adjustLawZ_00 : adjustLawZ false false = 21 / 100 := by
  unfold adjustLawZ jointObs fMB fYB fXB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-- `adjustLawZ(0,1) = 21/100`。 -/
theorem adjustLawZ_01 : adjustLawZ false true = 21 / 100 := by
  unfold adjustLawZ jointObs fMB fYB fXB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-- `adjustLawZ(1,0) = 0`。 -/
theorem adjustLawZ_10 : adjustLawZ true false = 0 := by
  unfold adjustLawZ jointObs fMB fYB fXB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-- `adjustLawZ(1,1) = 29/50`（**唯一**与 `doLaw` 重合的一行）。 -/
theorem adjustLawZ_11 : adjustLawZ true true = 29 / 50 := by
  unfold adjustLawZ jointObs fMB fYB fXB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-! ### §4 ⭐⭐⭐ 数值表：`adjustLawM`（`{M}` 中介调整） -/

/-- `adjustLawM(0,0) = 21/200`。 -/
theorem adjustLawM_00 : adjustLawM false false = 21 / 200 := by
  unfold adjustLawM jointObs fMB fYB fXB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-- `adjustLawM(0,1) = 21/200`。 -/
theorem adjustLawM_01 : adjustLawM false true = 21 / 200 := by
  unfold adjustLawM jointObs fMB fYB fXB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-- `adjustLawM(1,0) = 0`。 -/
theorem adjustLawM_10 : adjustLawM true false = 0 := by
  unfold adjustLawM jointObs fMB fYB fXB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-- `adjustLawM(1,1) = 29/100`。 -/
theorem adjustLawM_11 : adjustLawM true true = 29 / 100 := by
  unfold adjustLawM jointObs fMB fYB fXB pzB pxB pyB
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  norm_num

/-! ### §5 ⭐⭐⭐⭐⭐ 主定理：两条调整律**都失败** -/

/-- ⚠⚠⚠ **`{Z}` 后门调整在 `demoX` 上失败**：`adjustLawZ(0,0) = 21/100 ≠ 1/2 = doLaw(0,0)`。

**⭐ 数学原因**：`demoX` 位于 `SetupXMY` 载体上，**存在 `X → Y` 直达边**
（`SetupXMY.x_to_y_edge`），故 `Z` **不是**合法的后门集 —— Pearl 的后门准则
要求 `Z` 阻断 `X → Y` 的**所有**后向路径且**不含 `X` 的后代**，
而 `demoX` 里 `X → Y` 是**前向直达边**，`{Z}` 调整**必然**给出错误答案。
这正是 `SetupXMY` 相对 `SetupWithM` 的价值：**它让错误暴露出来**。 -/
theorem adjustLawZ_ne_doLaw : adjustLawZ false false ≠ doLaw false false := by
  rw [adjustLawZ_00, doLaw_00]
  norm_num

/-- ⚠ **中介调整 `{M}` 失败**：`adjustLawM(1,1) = 29/100 ≠ 29/50 = doLaw(1,1)`。

**⭐ 数学原因**：`M` 是 `X` 的**后代**（`fM` 吃 `X`），违反 Pearl (ii)。 -/
theorem adjustLawM_ne_doLaw : adjustLawM true true ≠ doLaw true true := by
  rw [adjustLawM_11, doLaw_11]
  norm_num

/-- ⚠ 补充：`{Z}` 调整**也不是**处处失败 —— `(1,1)` 一行恰好重合。
这是**偶然**（数值巧合），**不是**定理；故本文件**不**把它升级为
`adjustLawZ_eq_doLaw`（那将是第 299 轮空壳的**同义反复式错误**）。 -/
theorem adjustLawZ_11_coincides : adjustLawZ true true = doLaw true true := by
  rw [adjustLawZ_11, doLaw_11]

end DemoX
end Fate.SetupXMY
