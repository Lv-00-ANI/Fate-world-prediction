/-
============================================================================
  规则核心链 · 桥路线甲（Dirac 规则 → Step）· **可行性勘察草案**
  （第 720 轮，P0-0）

  ⚠⚠ **本文件不是定理，只有 def 形状试探。**
  目的：确认「`DetFun` 形状 `PUnit → X.Carrier → X.Carrier` 能否机械地
        当作 `Step F` 使用」这一**类型层**问题。
  结论见 `_audit/P0-0-DetFun到Step可行性勘察.md`：
        · `CtxSpace` 只有 `Carrier` 一个字段 ⟹ `⟨PUnit⟩` 合法（Q1 🟢）
        · `DetFun` 只是 namespace，真正的形状是 `C.Carrier → X.Carrier → Y.Carrier`（Q2）
        · `Step F` 的 5 个参数可全忽略 ⟹ 草案 `def` 编译通过（Q3 🟢）
        · `cs : ℕ → PUnit` 平凡给出 `fun _ => PUnit.unit`（Q4 🟢）

  **诚实标注**：
  - 本文件**不含任何 theorem**，故**不声称「桥能过」**；
  - 它只证明「形状对得上」这一件事；
  - 真正的桥引理（`trajOfLaw` 与 `Step` 的相容等式）尚未写，留给 P0-1。
============================================================================
-/

import FateWorld.Legacy.Frame
import FateWorld.Legacy.LawRule
import FateWorld.Legacy.LawRuleToTraj
import FateWorld.Legacy.WorldModel

namespace Fate

noncomputable section

/-! ## §1  静态上下文 `C := ⟨PUnit⟩`

`CtxSpace` 的唯一字段是 `Carrier : Type*`（见 `Fate/Frame.lean:292`），
故 `⟨PUnit⟩` 是最简合法的静态上下文实例。 -/

/-- **静态上下文实例**：`CtxSpace` 以 `PUnit` 为 `Carrier`。 -/
def ctxPUnit : CtxSpace := ⟨PUnit⟩

/-- **静态上下文序**：`ℕ → PUnit` 的唯一（平凡）取值。 -/
def csPUnit : ℕ → PUnit := fun _ => PUnit.unit

/-! ## §2  `DetFun` 形状 → `Step`（**草案，非定理**）

`DetFun` 不是类型，而是 `LawRule` 文件里的一个 namespace；
其真正签名是 `C.Carrier → X.Carrier → Y.Carrier`（见 `DetFun.toLaw`）。
当 `C := ⟨PUnit⟩`、`X = Y = F.X` 时，该形状即 `PUnit → F.X.Carrier → F.X.Carrier`。

`Step F` 是 `F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier →
F.Act.Carrier → F.X.Carrier`（见 `Fate/Frame.lean:146`）。

二者**只差「忽略四个参数」**，故下面的 `def` 在类型层无条件成立：
把 `(u, ε, θ, a)` 全部忽略（`_u _ν _θ _a`），把 `PUnit` 取 `PUnit.unit` 即得。 -/

/-- ⭐ **【Dirac 规则 → Step】草案（静态上下文，非定理）**

`g : PUnit → F.X.Carrier → F.X.Carrier`（即 `DetFun ⟨PUnit⟩ F.X F.X` 的形状）
降维为 `Step F`：忽略上下文 `PUnit.unit`，忽略 `(u, ε, θ, a)`。

**⚠ 这是 def 草案，不是定理；它只声明「形状对得上」，不含任何语义断言。** -/
def detFunToStep (F : Frame)
    (g : PUnit → F.X.Carrier → F.X.Carrier) : Step F :=
  fun x _u _ν _θ _a => g PUnit.unit x

/-- ⭐ **【甲路线完整形状】草案（从 `LawRule` 的 `IsDirac` 抽出 → `Step`）**

给定 `R : LawRule ⟨PUnit⟩ F.X F.X` 与 `IsDirac` 见证，`toDetFun` 抽出确定性机制，
再经 `detFunToStep` 忽略四位参数，得到 `Step F`。

**注意**：`MeasurableSpace F.X.Carrier` 在 `LawRule` 体系的 `[·]` 类型类位置，
当 `X := F.X` 时须**显式传入** `instX`（Lean 不会从 `F.X.meas` 字段自动取），
此处如实登记该 elaboration 细节。 -/
def lawDetToStep (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (R : LawRule.LawRule ctxPUnit F.X F.X)
    (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R) : Step F :=
  fun x _u _ν _θ _a =>
    @LawRuleToTraj.toDetFun ctxPUnit F.X F.X instX R hR PUnit.unit x

end

end Fate
