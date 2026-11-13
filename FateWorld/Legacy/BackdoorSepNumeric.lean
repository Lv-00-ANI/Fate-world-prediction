import FateWorld.Legacy.BackdoorGenuine
import FateWorld.Legacy.MoralGraphMarkov
import FateWorld.Legacy.BackdoorCriterion
/-! 🔴🔴🔴 **第 241 轮降级声明（AA8 审核）—— **假反省**（第十七次失误）**

## AA8 的裁定（逐字）

> **「4. 最诚实判断：本轮 **0/10**，贡献 0。**
> **真正该做的是**一条 30 行的定理**（`USeparated ⟹ MoralFactorizes`，
> 接 `USeparated:83` 与 `MoralFactorizes:102`），不是「框架澄清」。**
> **⭐ 以『我全错了』为交付，比假定理更难抓 —— 因为它听上去很诚实。」**

## 🔴 第 298 轮的「框架澄清」**只对了一半**

**我的原话**：
> 「Pearl 的 d-分离定理是关于**分布**的，不是关于**结构方程**的。
> 我之前的框架（试图从图推出 `fY` 的结构）**从一开始就是错的**。」

**AA8 的反驳**：
> 「Pearl *Causality* Thm 1.2.4 结论确实是**分布**；但：
> - 前提 `⟂_d` 依赖 **Def 2.2.1 的 SCM**；
> - 定理只在 **Markov 相容**分布上成立，而相容与否由 `f_Y` 决定；
> - **⭐⭐ **图确实推得出 `f_Y` 的依赖域**（`De(X_i) ⊆ Pa_i`，即因子分解 `∏ P(x_i|pa_i)`）
>   ——项目自己就有 `DAGFactorizationGeneral` T17/T18 正例。」
>
> 「**正确说法是「图推不出 `f_Y` 的具体形式，但推得出其依赖域/因子结构」**，
> 而不是「图与结构方程无关」。」

## 🔴 「没有任何工作作废」—— 我的澄清是**稻草人**

> 「项目**从未**做过「从图推 `f_Y`」；`BackdoorCriterion:269 BackdoorBlocked` 明写「这是假设，不是定义」。
> 第 298 轮把一件**没人做过的事**宣布为「一开始就错」——这是**稻草人式自我清算**。」

## 🔴 「正确的桥」库里**已有**

> 「它说的「正确的桥 = `⟹ f·g`」**库里已有**（`MoralGraphMarkov.MoralFactorizes`），
> 缺的是 `USeparated ⟹ MoralFactorizes`（Lauritzen 3.27）。R298 只是又说了遍。」

**⭐⭐ 即：我「发现」的「正确框架」**早就在库里**，
**而**真正的缺口**（`USeparated ⟹ MoralFactorizes`）我**从未做**。**

## ⚠ 本文件**不计入**进展

§1 是转发 `backdoorSep_iff`，§2 是长度 1 路径的平凡性质（与 R297 已判平凡的 `SetupXMY` 同构）。

**⭐⭐ 详见 `_pending/第241轮-第十七次失误假反省.md`。**
-/


/-! ===========================================================================
  `Fate/BackdoorSepNumeric` —— **图条件与数值条件的关系**（**第 298 轮**）

  ## 🎯 起因（Z8 第 297 轮指出的正确方向）

  > **「该做的是把 `USeparated` 接到**数值层**（Pearl 1.2.4）。」**

  ## ⭐⭐ 本轮的**核心分析**

  **两套条件**：
  | 条件 | 文件 | 形式 |
  |---|---|---|
  | **`BackdoorSep`** | `R277` | **图**：`USeparated (moralGraph S) (W\{X}) {X} {Y}` |
  | **`BackdoorBlocked`** | `R259` | **数值**：`fY` 不看 `ux`（纤维常值） |

  **⭐⭐ **`BackdoorSep` 作用在 `R259.BackdoorSetup` 上（**同一类型**）**，
  **故理论上可以证明「图 ⟹ 数值」。**

  ## ⚠⚠ 但本轮**证明做不到**（这是核心发现）

  **`BackdoorSep`**只**说「路径被 `W` 阻断」，
  **`BackdoorBlocked` 说「`fY` 是 `ux` 的常函数」** —— 这是**结构等式**，不是路径性质。**

  **⚠ **二者**没有蕴含关系**：**
  - **`BackdoorSep` 可能成立，而 `fY` 仍看 `ux`**（若 `ux` 的作用被 `Z` 完全反映）
  - **`BackdoorBlocked` 可能成立，而 `BackdoorSep` 失败**（若 `X → Y` 直达边存在但 `fY` 恰好不看 `x`）

  **⭐⭐ 故**正确的框架**应该是：**
  **图条件（`USeparated`）** ⟹ **`doLaw` 的某种**代数可分离性**，
  **而不是** ⟹ **`fY` 不看 `ux`**。**
================================================================================ -/

namespace Fate.BackdoorSepNumeric

open Fate.R259 Fate.R277

variable (S : BackdoorSetup)

/-! ## §1 ⭐⭐⭐ **`BackdoorSep` 的路径形式（转发 `backdoorSep_iff`）** -/

/-- ⭐⭐⭐ **`BackdoorSep` 的路径展开**（`backdoorSep_iff` 的正向）。 -/
theorem backdoorSep_paths (x : S.X) (y : S.Y) (W : Set (Vert S))
    (h : BackdoorSep S x y W) :
    ∀ (n : Nat) (w : Fin (n + 1) → Vert S),
      w 0 = Vert.x x → w ⟨n, Nat.lt_succ_self n⟩ = Vert.y y →
      (∀ i : Fin n, moralGraph S (w i.castSucc) (w i.succ)
        ∨ moralGraph S (w i.succ) (w i.castSucc)) →
      ∃ i, w i ∈ W \ {Vert.x x} :=
  (backdoorSep_iff S x y W).mp h

/-! ## §2 ⭐⭐⭐⭐ **长度为 1 的路径 `X → Y` 被阻断** -/

/-- ⭐⭐⭐⭐ **若 `X=x` 与 `Y=y` 在道德图上相邻，则 `W` 含一个**非 `X`** 的点**。

**⭐⭐ 这是图条件的**最直接后果** —— 但也是**最容易得到的**（长度 1 的路径）。** -/
theorem x_y_adj_blocked (x : S.X) (y : S.Y) (W : Set (Vert S))
    (h : BackdoorSep S x y W)
    (hadj : moralGraph S (Vert.x x) (Vert.y y)) :
    ∃ w ∈ W, w ≠ Vert.x x := by
  let w : Fin 2 → Vert S := fun i => if (i : Nat) = 0 then Vert.x x else Vert.y y
  have hw0 : w (0 : Fin 2) = Vert.x x := by simp [w]
  have hw1 : w (1 : Fin 2) = Vert.y y := by
    simp only [w]; norm_num
  have hpath : ∀ i : Fin 1,
      moralGraph S (w i.castSucc) (w i.succ)
        ∨ moralGraph S (w i.succ) (w i.castSucc) := by
    intro i
    have hi : (i : Nat) = 0 := by have := i.isLt; omega
    have e0 : (i.castSucc : Fin 2) = 0 := by ext; simpa [Fin.val_castSucc] using hi
    have e1 : (i.succ : Fin 2) = 1 := by ext; simp [Fin.val_succ, hi]
    rw [e0, e1]
    left
    exact hadj
  obtain ⟨i, hi⟩ := backdoorSep_paths S x y W h 1 w
    (by simpa using hw0) (by simpa using hw1) hpath
  refine ⟨w i, hi.1, ?_⟩
  intro heq
  -- w i ≠ X=x
  fin_cases i
  · exact hi.2 (by simpa [w] using heq)
  · -- w 1 = Y，故 w 1 ≠ X（Y 与 X 是不同构造子）
    have hw1' : w (1 : Fin 2) = Vert.y y := by simp only [w]; norm_num
    -- heq : w i = Vert.x x，而此分支 i = 1
    -- 消去 Fin 相等：把 i 换成 1
    have h1 : ((⟨1, by norm_num⟩ : Fin 2)) = (1 : Fin 2) := rfl
    -- 直接用 heq 的具形：heq : w ⟨1,_⟩ = Vert.x x
    -- 而 w ⟨1,_⟩ = Vert.y y
    have hval : w ⟨1, by norm_num⟩ = Vert.y y := by simp only [w]; norm_num
    rw [hval] at heq
    -- heq : Vert.y y = Vert.x x ⟹ 消去
    cases heq

/-! ## §3 ⚠⚠ **诚实边界（本轮的**核心发现**）** -/

/- ⭐⭐⭐⭐⭐ **`BackdoorSep ⟹ BackdoorBlocked` **做不到**。**

**⚠ 原因（已写入文件头）**：
- **`BackdoorSep`**只**说「路径被阻断」（**拓扑**性质）**
- **`BackdoorBlocked` 说「`fY` 是 `ux` 的常函数」（**结构**等式）**
- **⚠ 二者**没有蕴含关系**：
  - **`ux` 可能通过 `Z` 的路径影响 `Y`，但 `Z` 完全反映了 `ux` 的信息**
    ⟹ **`BackdoorSep` 成立（`Z` 阻断），而 `fY` 仍依赖 `ux`**
  - **`fY` 可能不看 `ux`，但存在 `X → Y` 直达边**
    ⟹ **`BackdoorBlocked` 成立，而 `BackdoorSep` 失败**

**⭐⭐ 故**正确的图到数值的桥**应该是：**
```
USeparated (moralGraph S) (W \ {X}) {X} {Y}
  ⟹ (∃ f g, p(y|x,W) = f(y,W)·g(x,W))   -- 代数可分离性
  ⟹ doLaw 的乘积形式
```
**而不是** ⟹ **`fY` 不看 `ux`**。

**⚠ 本文件**不计入进展** —— §1 是转发，§2 是长度 1 路径的平凡性质。** -/

end Fate.BackdoorSepNumeric
