import FateWorld.Legacy.SetupXMY

/-! ===========================================================================
  `Fate/SetupXMYDemo` —— ⭐⭐⭐⭐⭐ **`demoX`：后门调整 vs 中介调整**

  ## 模型（全 `Bool`）

  ```
  Z = Ux = Uy = X = M = Y = Bool
  pz(0) = 3/5,  pz(1) = 2/5
  px(0) = 1/10, px(1) = 9/10
  py ≡ 1/2
  fX(z, ux)       = z ⊕ ux
  fM(x, uy)       = if uy then true else x
  fY(x, m, z, ux) = x ⊕ m ⊕ z ⊕ ux          ⭐ 吃 X（直达边 X → Y）
  ```

  ## 交付

  * `doLaw` / `adjustLawZ` / `adjustLawM` 的**数值表**（§6，机器可验），
  * ⭐ `adjustLawZ_eq_doLaw : adjustLawZ x y = doLaw x y`（**后门正确**，§7），
  * ⚠ `adjustLawM_ne_doLaw`（**中介偏误**，§7）。

  ## ⚠ 关于 `Decidable`（重要）

  §8 的 `hfY/hfM/hfX` 是 `demoX` **字段层**的求值引理（`conv_lhs => rw [fY_eq]; rfl`），
  它们把 `demoX.fY …` 降到 `fYB …`（`Bool`）。
  §6 的求和**全部**建在 `Bool` 上，故 `Decidable (Bool 等式)` 全部由
  `instDecidableEqBool` 给出；`Bool` 的 `if` 在 `norm_num` 里可以正常归约，
  而 `ℝ` 层的 `if … = … then` 会落到 `Real.decidableEq` / `Classical.choice`
  （`norm_num` 会留下 `⊢ False`）。这就是为什么指示函数写成 `if b then 1 else 0`
  的形式，且 `∑` 一律用 `Fintype.sum_bool` 显式展开。
-/

namespace Fate.SetupXMY
namespace DemoX

open Finset

/-! ### §1 具体 SCM -/

/-- ⭐⭐⭐⭐⭐ **具体 SCM `demoX`**（全 `Bool`，`fY` 吃 `X`）。 -/
noncomputable def demoX : Setup :=
  { Z := Bool
    Ux := Bool
    Uy := Bool
    X := Bool
    M := Bool
    Y := Bool
    pz := fun z => if z = false then (3 : ℝ) / 5 else 2 / 5
    px := fun ux => if ux = false then (1 : ℝ) / 10 else 9 / 10
    py := fun _ => 1 / 2
    fX := fun z ux => Bool.xor z ux
    fM := fun x uy => if uy then true else x
    fY := fun x m z ux _uy => Bool.xor (Bool.xor (Bool.xor x m) z) ux }

/-- `demoX.X = Bool`。 -/
theorem X_eq_bool : demoX.X = Bool := rfl
/-- `demoX.M = Bool`。 -/
theorem M_eq_bool : demoX.M = Bool := rfl
/-- `demoX.Y = Bool`。 -/
theorem Y_eq_bool : demoX.Y = Bool := rfl

/-! ### §2 `Bool` 层的概率与结构函数 -/

/-- `pz` 的 `Bool` 形式。 -/
noncomputable def pzB (z : Bool) : ℝ := if z = false then 3 / 5 else 2 / 5
/-- `px` 的 `Bool` 形式。 -/
noncomputable def pxB (ux : Bool) : ℝ := if ux = false then 1 / 10 else 9 / 10
/-- `py ≡ 1/2`。 -/
noncomputable def pyB (_uy : Bool) : ℝ := 1 / 2
/-- `fX z ux = z ⊕ ux`。 -/
noncomputable def fXB (z ux : Bool) : Bool := Bool.xor z ux
/-- `fM x uy`。 -/
noncomputable def fMB (x uy : Bool) : Bool := if uy then true else x
/-- `fY x m z ux = x ⊕ m ⊕ z ⊕ ux`（⭐ **吃 `X`**）。 -/
noncomputable def fYB (x m z ux : Bool) : Bool := Bool.xor (Bool.xor (Bool.xor x m) z) ux

theorem pz_eq : demoX.pz = pzB := rfl
theorem px_eq : demoX.px = pxB := rfl
theorem py_eq : demoX.py = pyB := rfl
theorem fX_eq : demoX.fX = fun (z ux : Bool) => fXB z ux := rfl
theorem fM_eq : demoX.fM = fun (x uy : Bool) => fMB x uy := rfl

/-- ⭐ `fY` 的 `Bool` 形式。 -/
theorem fY_eq : demoX.fY = fun (x m z ux : Bool) (_uy : Bool) => fYB x m z ux := by
  unfold demoX fYB
  funext x m z ux uy
  rfl

/-! ### §3 ⭐ `Bool` 指示函数的**基本恒等式**

⚠ 这里刻意**不**用 `Bool` 的 `if` 作指示函数，而用
`if b = true then (1:ℝ) else 0`：其 `Decidable` 是 `instDecidableEqBool`，
`norm_num` 能把它归约到 `1`/`0`（见 §6 的用法）。 -/

/-! ### §4 三个「律」 -/

/-- ⭐⭐ **`do` 核** `P(y, m | do(x), z)`。干预下 `X` 被钉成常数，`X → Ux` 边被删。 -/
noncomputable def jointDo (x z m y : Bool) : ℝ :=
  ∑ ux : Bool, ∑ uy : Bool,
    pxB ux * pyB uy * (if fMB x uy = m then (1 : ℝ) else 0) *
      (if fYB x m z ux = y then (1 : ℝ) else 0)

/-- ⭐⭐ **观测核** `P(y, m | x, z)`（多一个 `[fX z ux = x]`）。 -/
noncomputable def jointObs (x z m y : Bool) : ℝ :=
  ∑ ux : Bool, ∑ uy : Bool,
    pxB ux * pyB uy * (if fMB x uy = m then (1 : ℝ) else 0) *
      (if fYB x m z ux = y then (1 : ℝ) else 0) * (if fXB z ux = x then (1 : ℝ) else 0)

/-- ⭐ **`doLaw(x,y) = P(y | do(x))`**。 -/
noncomputable def doLaw (x y : Bool) : ℝ :=
  ∑ z : Bool, pzB z * ∑ m : Bool, jointDo x z m y

/-- ⭐ **`adjustLawZ(x,y) = ∑_z pz(z) ∑_m P(y,m|x,z)`**（`Z` 后门调整）。 -/
noncomputable def adjustLawZ (x y : Bool) : ℝ :=
  ∑ z : Bool, pzB z * ∑ m : Bool, jointObs x z m y

/-- ⚠ **`adjustLawM(x,y) = ∑_m (1/2) ∑_z pz(z) P(y,m|x,z)`**（把**中介** `M` 当调整集）。 -/
noncomputable def adjustLawM (x y : Bool) : ℝ :=
  ∑ m : Bool, (∑ z : Bool, pzB z * jointObs x z m y) / 2

-- 证明在 `Fate/SetupXMYDemoLaw` 中。

end DemoX
end Fate.SetupXMY
