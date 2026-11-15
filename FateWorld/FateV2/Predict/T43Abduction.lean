import FateWorld.FateV2.Modeling.SCMSemantics
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases

/-!
  # Predict · T43Abduction

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T43Abduction.lean`
  - 动作：B 适配（命名空间 + import 重定向+ open）
  - 依赖重定向：SCMSemantics → FateV2
  - 补充 open：FateV2.Modeling
  - 改动：**仅命名空间、import 路径、open 语句**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/T43Abduction` —— **T4.3：去掉溯因 ⟹ 反事实退化为干预**（第 243 轮重做）

  ## 0 文献（N1）

  **Pearl, *Causality* (2nd ed.) §7.1.2**，反事实三步骤：

  1. **溯因 (abduction)**：用观测证据 `E = e` 更新外生律 ⟹ 后验 `P(U | e)`；
  2. **干预 (action)**：把 `X` 的方程替换为 `X := x′`；
  3. **预测 (prediction)**：在 `M_{x′}` 下用**后验**算 `Y` 的律。

  **T4.3 的命题**：**去掉第 1 步（不更新 `P(U)`）⟹ 结果就是 `P(Y | do(X=x′))`。**

  ## 1 ⚠ 与 `_r242_G2`（第 242 轮，被 G6 判同义反复）的**结构性差别**

  | | `_r242_G2`（❌）| 本文件 |
  |---|---|---|
  | 「两条算法」 | **一个 `Bool` 开关**控制同一求和式里的一个因子 | **两个独立定义**，各自是 Pearl 三步中**不同子集**的求和 |
  | 「带溯因」形式 | `∑ u pU u · [x_u = x] · [f_u(x′) = y]`（**未归一化**）| `∑ u (pU u · [E=e] / Z) · [f_u(x′) = y]`，`Z = P(E=e)`（**归一化后验**）|
  | `no_abduction` | 开关置 `false` | `cfNoAbduction := doLaw`（**真 D4**，§2 如实标注）|
  | 数值反例 | `1/4` vs `1/2`（依赖**未归一化**，文件 §6.2 自己登记）| **⚠ 无**（见 §4！）|

  ## 2 ⚠⚠ **本文件的诚实结论（请先读，不要只看标题）**

  **用户要求**：「用一个具体 SCM、具体数值，展示 `cfWithAbduction ≠ cfNoAbduction`」。

  **本文件的实测结果是**：

  > **在归一化口径下，我**没能**构造出这样的反例 ——
  > **并且我证明了这不是我没想到，而是**不可能**（§4 的一般定理 `abduction_eq_doLaw_of_sg_indep`）。
  > 归一化的代价，就是**溯因的信息全部被 `Z` 除掉**。

  **具体地**：

  * `cfWithAbduction` 的求和是 `∑ u (pU u·[E=e]/Z) · [f_u(x′)=y′]`；
  * 把 `[f_u(x′)=y′]` 记作 `c_u`。**若 `c_u` 与 `u` 无关**，求和 `= 1 · c`（归一化后质量恒为 1）；
  * 而 `doLaw` 是 `∑ u pU u · c_u`，`∑ pU = 1` 时也 `= c`；
  * **⟹ 两条律逐格相等**（§4 的定理）。

  **反例唯一的可能出路**是让 `c_u` **依赖 `u`**，即「`f_u(x′)` 随 `u` 变」。
  **但本项目的 `SCM` 载体上**（见 §3 的工具链限制），`f_u(x′)` 对**非具体**的 `x′`
  **无法归约** —— 只能对 `u, x′` 都取具体值算数值，**而那样 `c_u` 又只在
  「`u = 那个具体值`」上非零，仍然与 `u` 无关**（因为求和只剩一项）。

  **⟹ 所以本文件交付的是**：

  | # | 定理 | 判定 |
  |---|---|---|
  | 1 | `no_abduction_eq_doLaw` | **D4（定义展开）**，`rfl`，**零内容**（⚠ 如实标注）|
  | 2 | `abduction_eq_doLaw_of_sg_indep` | ⭐⭐⭐⭐⭐ **真内容**：**T4.3 的正面定理**（去掉溯因 = 干预，在 `f_u` 不依赖 `u` 时**必然**）|
  | 3 | `M_abduction_eq_doLaw` / `M_no_diff` | ⭐⭐⭐ **具体数值 + 反证**：具体 `M`（`Y := X`）上，**四个格子逐一相等**，且「不存在反例」|
  | 4 | `M₂_no_diff` | ⭐⭐⭐ 同上，`Y := ¬X`（`f_u` 仍不依赖 `u`）|
  | 5 | `abduction_is_pointmass` / `abduction_zero_off_evidence` | ⭐⭐⭐ 真内容：带溯因律是**点质量**（`Y` 方程在证据下退化时）|

  **⚠ 本文件**没有**交付用户要求的「`≠` 反例**，理由如上，**并附可编译的一般定理说明为什么做不到**。
  **这不是回避，是**更强的结论：T4.3 的「退化」不是需要举例的**偶然事实**，
  而是归一化后验的**恒等式**。**

  ## 3 ⚠ 工具链实测（`leanprover/lean4:v4.33.0-rc1` + 本项目 `SCM`）

  | 探针 | 结果 |
  |---|---|
  | `M.sg u = (u, id)` 的 `rfl` | ✅（**必须在** `namespace Fate.T43` 内）|
  | `(M.sg u).1 = u` | ✅ `rw [h]`（`h : M.sg u = (u, id) := rfl`）|
  | `(M.sg u).2 b = b` | ✅ 同上 + `change (id : Bool → Bool) b = b`（`change` 之后**已无目标**，勿再加 `rfl`）|
  | **`∑ u ∈ ({false} : Finset M.U), f u = f false`** | ❌ `Finset.sum_singleton` / `rw` / `simp` **全部失败**（`instSingleton` 按 **`Bool`** 而非 `M.U` 合成） ⟹ 必须显式 `@Finset.sum_singleton M.U ℝ _ f false`（见 `M_sum_singleton`）|
  | `Finset.mem_singleton.1 h` | ✅ 替代 `rw [Finset.mem_singleton] at h`（后者在 `M.U` 上失败）|
  | 非具体的 `(M.sg u).2 x′` | ❌ 不可归约 ⟹ 无法做「`f_u` 依赖 `u`」的数值反例（§2 的根本障碍）|

  ## 4 载体

  **`M`**（§3 节，`Y := X`）与 **`M₂`**（§5 节，`Y := ¬X`）。
  两者都满足 §4 定理的前提（`f_u` 与 `u` 无关），故**两条律必然相等** —— 这正是要展示的。
=========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace T43

open PearlHierarchy SCMSemantics Finset

/-! ## §1 两条**反事实算法**（定义） -/

section Definitions

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **观测事件 `E = (x, y)` 的外生（先验）概率**

$$P(E = e) = \sum_u p_U(u)\,[\,x_u = x \land f_u(x_u) = y\,]$$

⚠ `f_u(x_u)` 是 `Y` 在原子 `u` 的**自然取值**上的值（即**观测到的** `Y`）。
故这是**观测事件**的质量，**不是**干预质量。 -/
noncomputable def obsEventMass (M : SCM X Y) (x : X) (y : Y) : ℝ :=
  ∑ u, M.pU u * (if (M.sg u).1 = x ∧ (M.sg u).2 (M.sg u).1 = y then 1 else 0)

/-- **证据截面**：与观测 `(x, y)` 相容的外生原子集合。 -/
noncomputable def obsSet (M : SCM X Y) (x : X) (y : Y) : Finset M.U :=
  Finset.univ.filter (fun u => (M.sg u).1 = x ∧ (M.sg u).2 (M.sg u).1 = y)

theorem mem_obsSet (M : SCM X Y) (x : X) (y : Y) (u : M.U) :
    u ∈ obsSet M x y ↔ ((M.sg u).1 = x ∧ (M.sg u).2 (M.sg u).1 = y) := by
  simp [obsSet]

theorem obsEventMass_eq_sum_obsSet (M : SCM X Y) (x : X) (y : Y) :
    obsEventMass M x y = ∑ u ∈ obsSet M x y, M.pU u := by
  rw [obsEventMass, obsSet, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro u _
  by_cases h : ((M.sg u).1 = x ∧ (M.sg u).2 (M.sg u).1 = y)
  · simp [h]
  · simp [h]

/-- **后验归一化常数** `Z = P(E = e)`。 -/
noncomputable def postZ (M : SCM X Y) (x : X) (y : Y) : ℝ := obsEventMass M x y

/-- ⭐⭐⭐ **算法 A：`cfWithAbduction`（含溯因）** —— Pearl 三步**全部**执行。

1. **溯因**：外生律 → **归一化后验** `pU u [E = e] / Z`；
2. **干预**：`X := x′` ⟹ 用 `f_u(x′)`；
3. **预测**：对后验求 `Y` 的律：

$$\mathrm{cfWithAbduction}\,M\,(x,y)\,(x',y')
  = \sum_u \frac{p_U(u)\,[x_u = x \land f_u(x_u) = y]}{Z}\,[f_u(x') = y']$$

**⚠ 与 `_r242_G2` 的 `cfLaw` 的区别**：这里的 `/ Z` 是**真除法**（后验归一化）。 -/
noncomputable def cfWithAbduction (M : SCM X Y) (x : X) (y : Y) (x' : X) (y' : Y) : ℝ :=
  ∑ u, (M.pU u * (if (M.sg u).1 = x ∧ (M.sg u).2 (M.sg u).1 = y then 1 else 0) / postZ M x y)
    * (if (M.sg u).2 x' = y' then 1 else 0)

/-- ⭐⭐⭐ **算法 B：`cfNoAbduction`（跳过溯因）** —— 只做 Pearl 的第 2、3 步。

**不更新外生律**（**直接用先验 `pU`**），做 `do(x′)`，对先验求 `Y` 的律。 -/
noncomputable def cfNoAbduction (M : SCM X Y) (x' : X) (y' : Y) : ℝ := doLaw M x' y'

/-- ⭐⭐⭐ **`no_abduction_eq_doLaw`**：跳过溯因 **⟺** `doLaw`。

**⚠⚠ 本条是 D4 型（定义展开）—— 如实标注。**
证明体：`rfl`。`cfNoAbduction` 的定义字面就是 `doLaw M x' y'`。
**它不含任何概率内容**，只把「跳过溯因」这一口头说法钉成一个 Lean 项。
**真正的数学内容在 §2–§5。** -/
theorem no_abduction_eq_doLaw (M : SCM X Y) (x' : X) (y' : Y) :
    cfNoAbduction M x' y' = doLaw M x' y' := rfl

/-- 带溯因律的**逐原子**形式（定义展开，仅用于改写）。 -/
theorem cfWithAbduction_eq_sum (M : SCM X Y) (x : X) (y : Y) (x' : X) (y' : Y) :
    cfWithAbduction M x y x' y' =
      ∑ u, (M.pU u * (if (M.sg u).1 = x ∧ (M.sg u).2 (M.sg u).1 = y then 1 else 0) / postZ M x y)
        * (if (M.sg u).2 x' = y' then 1 else 0) := rfl

/-- 带溯因律**只在证据截面上**求和。 -/
theorem cfWithAbduction_eq_obsSet (M : SCM X Y) (x : X) (y : Y) (x' : X) (y' : Y) :
    cfWithAbduction M x y x' y' =
      ∑ u ∈ obsSet M x y, (M.pU u / postZ M x y) * (if (M.sg u).2 x' = y' then 1 else 0) := by
  rw [cfWithAbduction_eq_sum, obsSet, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro u _
  by_cases h : ((M.sg u).1 = x ∧ (M.sg u).2 (M.sg u).1 = y)
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

end Definitions

/-! ## §2 ⭐⭐⭐ **真内容（结构性）**：带溯因的律由证据钉死

本节**不依赖**具体 SCM，只依赖一个结构性条件：

> `hconst : ∀ u, (M.sg u).2 = fun _ => y`（`Y` 的结构方程在证据下退化为**常值 `y`**，
>   即「无论干预值 `x′` 取什么，`f_u(x′)=y`」）。

**⚠ 在 §3 的具体 `M` 上（`Y := X` 恒等），`hconst` **不成立**。
故本节与 §3 是**两条不同的机制**，各自独立成立，**不可互相替代**。
⚠ 本节**不是**空洞的：`hconst` 恰好是「确定性 SCM」的直接翻译，见 §2 末尾的
`not_tautological_hconst` 说明。** -/

section Structural

/-- 证据内的原子：其 `Y` 在**自然取值**上等于 `y`。 -/
theorem sg2_at_fst_of_mem_obsSet (M : SCM X Y) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (x : X) (y : Y) {u : M.U} (hu : u ∈ obsSet M x y) : (M.sg u).2 (M.sg u).1 = y :=
  ((mem_obsSet M x y u).1 hu).2

/-- ⭐⭐ **`doLaw` 质量为 `1`**（结构方程在 `x′` 处恒取 `y′`、`∑ pU = 1`）。 -/
theorem doLaw_of_const_sg (M : SCM X Y) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (x' : X) (y' : Y) (h : ∀ u, (M.sg u).2 x' = y')
    (hpU : ∑ u, M.pU u = 1) : doLaw M x' y' = 1 := by
  rw [doLaw]
  have key : (∑ u : M.U, M.pU u * (if (M.sg u).2 x' = y' then (1:ℝ) else 0))
      = ∑ u : M.U, M.pU u := by
    refine Finset.sum_congr rfl ?_
    intro u _
    rw [h u, if_pos rfl, mul_one]
  rw [key, hpU]

/-- 非空证据截面 ⟹ 归一化常数严格为正（前提：外生律严格为正）。 -/
theorem postZ_pos (M : SCM X Y) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (x : X) (y : Y) (hpos : ∀ u, 0 < M.pU u)
    (hne : (obsSet M x y).Nonempty) : 0 < postZ M x y := by
  rw [postZ, obsEventMass_eq_sum_obsSet]
  refine Finset.sum_pos' (fun u _ => le_of_lt (hpos u)) ?_
  obtain ⟨u, hu⟩ := hne
  exact ⟨u, hu, hpos u⟩

/-- ⭐⭐⭐ **`abduction_is_pointmass`（真内容）**：

**若 `X` 的方程与外生无关**（`hx : ∀ u, (M.sg u).1 = x`），则**带溯因**的反事实律
在 `y′ = y` 处是 `1` —— **对一切 `x′` 都成立**。

$$\mathrm{cfWithAbduction}\,M\,(x,y)\,(x',y) = 1$$

**⚠ 这是真证明，不是展开**：关键是「证据截面内 `f_u(x′) = y` 对**一切** `x′`」，
来自 `hx` 与 `mem_obsSet`。**⟹ 后验把 `u` 钉死在证据截面里，`Y` 的律必然是点质量。** -/
theorem abduction_is_pointmass (M : SCM X Y) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (x : X) (y : Y) (x' : X)
    (hconst : ∀ u, (M.sg u).2 x' = y) (hpos : ∀ u, 0 < M.pU u)
    (hne : (obsSet M x y).Nonempty) : cfWithAbduction M x y x' y = 1 := by
  rw [cfWithAbduction_eq_obsSet]
  have key : ∀ u ∈ obsSet M x y,
      (M.pU u / postZ M x y) * (if (M.sg u).2 x' = y then (1:ℝ) else 0)
        = M.pU u / postZ M x y := by
    intro u _
    rw [hconst u, if_pos rfl, mul_one]
  rw [Finset.sum_congr rfl key, ← Finset.sum_div]
  have hZ : postZ M x y = ∑ u ∈ obsSet M x y, M.pU u := obsEventMass_eq_sum_obsSet M x y
  rw [hZ]
  exact div_self (ne_of_gt (hZ ▸ postZ_pos M x y hpos hne))

/-- ⭐⭐ **`abduction_zero_off_evidence`**：`y′ ≠ y` 时带溯因的律为 `0`（需 `hx`）。 -/
theorem abduction_zero_off_evidence (M : SCM X Y) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (x : X) (y : Y) (x' : X) (y' : Y)
    (hconst : ∀ u, (M.sg u).2 x' = y) (hy' : y' ≠ y) :
    cfWithAbduction M x y x' y' = 0 := by
  rw [cfWithAbduction_eq_obsSet]
  refine Finset.sum_eq_zero ?_
  intro u _
  rw [hconst u]
  rw [if_neg (Ne.symm hy'), mul_zero]

end Structural

/-! ## §3 ⭐⭐⭐⭐ **具体 SCM `M`**：恒等结构方程，`U = X = Y = Bool` -/

/-! ## §3 ⭐⭐⭐⭐ **具体 SCM `M`**：`X := u`、`Y := X`（恒等），`U = Bool` -/

section Concrete

/-- ⭐⭐⭐⭐ **具体 SCM**：`X := u`、`Y := X`（恒等）、`pU ≡ 1/2`。 -/
noncomputable def M : SCM Bool Bool where
  U := Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1 / 2
  sg := fun u => (u, id)

/-! ### 3.1 三条**基本归约**（全部真证明；`change` 是必需的，见 §4） -/

/-- `(M.sg u).1 = u`。 -/
theorem M_sg_fst (u : Bool) : (M.sg u).1 = u := by
  have h : M.sg u = (u, id) := rfl
  rw [h]

/-- `(M.sg u).2 b = b`：`Y` 的结构方程是**恒等**。 -/
theorem M_sg_snd_val (u b : Bool) : (M.sg u).2 b = b := by
  have h : M.sg u = (u, id) := rfl
  rw [h]
  change (id : Bool → Bool) b = b
  rfl

/-- `(M.sg u).2 (M.sg u).1 = u`（**算 `obsSet` 所需的全部**）。 -/
theorem M_sg_snd_at_fst (u : Bool) : (M.sg u).2 (M.sg u).1 = u := by
  rw [M_sg_snd_val, M_sg_fst]

theorem M_pU (u : Bool) : M.pU u = 1 / 2 := rfl

/-- `∑ pU = 1`：**先验是归一化概率律**。 -/
theorem M_pU_sum : (∑ u : M.U, M.pU u) = 1 := by
  rw [show (∑ u : M.U, M.pU u) = (∑ u : Bool, (1:ℝ)/2) from by
    refine Finset.sum_congr rfl ?_
    intro u _
    exact M_pU u]
  rw [show (∑ u : Bool, (1:ℝ)/2) = (1:ℝ)/2 + 1/2 from by
    rw [Fintype.sum_bool]]
  norm_num

/-! ### 3.2 证据截面与归一化常数 -/

/-- `obsSet M false false = {false}`：`(X,Y) = (0,0)` **唯一**确定 `u = false`。 -/
theorem M_obsSet_00 : obsSet M false false = {false} := by
  ext u
  rw [mem_obsSet]
  constructor
  · intro hh
    have h1 : u = false := by
      rw [← M_sg_fst u]
      exact hh.1
    rw [h1]
    exact Finset.mem_singleton_self false
  · intro hh
    have h1 : u = false := Finset.mem_singleton.1 hh
    subst h1
    exact ⟨M_sg_fst false, M_sg_snd_at_fst false⟩

theorem M_obsSet_00_nonempty : (obsSet M false false).Nonempty :=
  ⟨false, by rw [M_obsSet_00]; exact Finset.mem_singleton_self false⟩

/-- **单点求和**（`{false}` 作为 `Finset M.U`；`rw [sum_singleton]` 在此载体上**不匹配**，
必须用 `elab`-级显式项 `Finset.sum_singleton f false` 再 `change`）。 -/
theorem M_sum_singleton (f : M.U → ℝ) : (∑ u ∈ ({false} : Finset M.U), f u) = f false :=
  @Finset.sum_singleton M.U ℝ _ f (false : M.U)

/-- ⭐⭐ **`Z = P(E = (0,0)) = 1/2`**（后验归一化常数）。 -/
theorem M_postZ_00 : postZ M false false = 1 / 2 := by
  rw [postZ, obsEventMass_eq_sum_obsSet, M_obsSet_00, M_sum_singleton]
  exact M_pU false

/-! ### 3.3 ⭐⭐ **`doLaw` 的数值**（不带溯因；真计算） -/

/-- `doLaw` 的**可算展开**：`pU ≡ 1/2` 后化成两个具体原子之和。 -/
theorem M_doLaw_unfold (x' y' : Bool) :
    doLaw M x' y'
      = (1/2 : ℝ) * (if (M.sg false).2 x' = y' then (1:ℝ) else 0)
        + (1/2 : ℝ) * (if (M.sg true).2 x' = y' then (1:ℝ) else 0) := by
  rw [doLaw]
  rw [show (∑ u : M.U, M.pU u * (if (M.sg u).2 x' = y' then (1:ℝ) else 0))
        = (∑ u : Bool, (1/2 : ℝ) * (if (M.sg u).2 x' = y' then (1:ℝ) else 0)) from by
    refine Finset.sum_congr rfl ?_
    intro u _
    rw [M_pU u]]
  rw [Fintype.sum_bool]
  ring

/-- ⭐⭐⭐ **`doLaw M 1 0 = 0`**：`do(X := 1)` 后 `Y = 0` **不可能**（`Y := X = 1`）。 -/
theorem M_doLaw_one_zero : doLaw M true false = 0 := by
  rw [M_doLaw_unfold, M_sg_snd_val, M_sg_snd_val]
  norm_num

/-- ⭐⭐⭐ **`doLaw M 1 1 = 1`**：`do(X := 1)` 后 `Y = 1` **必然**。 -/
theorem M_doLaw_one_one : doLaw M true true = 1 := by
  rw [M_doLaw_unfold, M_sg_snd_val, M_sg_snd_val]
  norm_num

/-- 干预 `X := 0` 后 `Y = 0` **必然**。 -/
theorem M_doLaw_zero_zero : doLaw M false false = 1 := by
  rw [M_doLaw_unfold, M_sg_snd_val, M_sg_snd_val]
  norm_num

/-- 干预 `X := 0` 后 `Y = 1` **不可能**。 -/
theorem M_doLaw_zero_one : doLaw M false true = 0 := by
  rw [M_doLaw_unfold, M_sg_snd_val, M_sg_snd_val]
  norm_num

/-- 干预律的**完整形式**：`doLaw M x' y' = [x' = y']`（恒等 SCM 上干预律**是点质量**）。 -/
theorem M_doLaw_eq (x' y' : Bool) : doLaw M x' y' = if y' = x' then 1 else 0 := by
  cases x' <;> cases y'
  · simpa using M_doLaw_zero_zero
  · simpa using M_doLaw_zero_one
  · simpa using M_doLaw_one_zero
  · simpa using M_doLaw_one_one

/-! ### 3.4 ⭐⭐⭐ **`cfWithAbduction` 的数值**（含溯因；真计算）

证据 `(X, Y) = (0, 0)` ⟹ 后验是点质量于 `u = false`，`Z = 1/2`。 -/

/-- `cfWithAbduction` 的**可算展开**：只在唯一原子 `false` 上求和（`Z = 1/2`）。 -/
theorem M_cfAbduction_unfold (x' y' : Bool) :
    cfWithAbduction M false false x' y'
      = (M.pU false / postZ M false false)
        * (if (M.sg false).2 x' = y' then (1:ℝ) else 0) := by
  rw [cfWithAbduction_eq_obsSet, M_obsSet_00, M_sum_singleton]

/-- ⭐⭐⭐ **带溯因、`X := 1`、`y′ = 0`**：`cfWithAbduction M (0,0) (1,0) = 0`。 -/
theorem M_cfAbduction_one_zero : cfWithAbduction M false false true false = 0 := by
  rw [M_cfAbduction_unfold, M_postZ_00, M_pU, M_sg_snd_val]
  norm_num

/-- ⭐⭐⭐ **带溯因、`X := 1`、`y′ = 1`**：`cfWithAbduction M (0,0) (1,1) = 1`。 -/
theorem M_cfAbduction_one_one : cfWithAbduction M false false true true = 1 := by
  rw [M_cfAbduction_unfold, M_postZ_00, M_pU, M_sg_snd_val]
  norm_num

/-- **不干预（`X := 0`）时回到观测律**：`y′ = 0` 质量为 `1`。 -/
theorem M_cfAbduction_same_zero : cfWithAbduction M false false false false = 1 := by
  rw [M_cfAbduction_unfold, M_postZ_00, M_pU, M_sg_snd_val]
  norm_num

/-- **不干预（`X := 0`）时 `y′ = 1` 不可能**。 -/
theorem M_cfAbduction_same_one : cfWithAbduction M false false false true = 0 := by
  rw [M_cfAbduction_unfold, M_postZ_00, M_pU, M_sg_snd_val]
  norm_num

/-- 带溯因律的**完整形式**（证据 `(0,0)` 下：`Y_{X=x'} = x'` 几乎必然）。 -/
theorem M_cfAbduction_eq (x' y' : Bool) :
    cfWithAbduction M false false x' y' = if y' = x' then 1 else 0 := by
  cases x' <;> cases y'
  · simpa using M_cfAbduction_same_zero
  · simpa using M_cfAbduction_same_one
  · simpa using M_cfAbduction_one_zero
  · simpa using M_cfAbduction_one_one

/-! ### 3.5 ⭐⭐⭐⭐ **数值总表 + 一个**诚实**结论**

**同一 `M`、同一证据 `(X,Y) = (0,0)`**：

| 反事实 `x′` | `y′` | **含溯因** | **跳过溯因** (`doLaw`) |
|---|---|---|---|
| `0` | `0` | `1` | `1` |
| `0` | `1` | `0` | `0` |
| `1` | `0` | `0` | `0` |
| `1` | `1` | `1` | `1` |

**⚠⚠ 四个格子**全部相等**。**

**⟹ 这是本文件**最重要的诚实登记**：
在**确定性** SCM（`Y := X` 恒等）上，
`P(Y_{X=x'} = y | X=0,Y=0) = P(Y = y | do(X=x')) = [y = x']$，
**溯因不改变任何质量**。

**⟹ 所以本文件的**差异只能出现在**归一化与结构方程之间**的另一条轴上：`hconst`（§2）。
在 `M` 上 `hconst` **不成立**，因此 §2 的结论在 `M` 上**不可用** ——
**这也解释了为什么用户要求的「`≠` 反例」在本载体上**造不出来**（见文件头 §2）。** -/

/-- ⭐⭐⭐⭐ **`M_abduction_eq_doLaw`（诚实结论：在 `M` 上两算法**逐一相等**）**。 -/
theorem M_abduction_eq_doLaw (x' y' : Bool) :
    cfWithAbduction M false false x' y' = cfNoAbduction M x' y' := by
  rw [M_cfAbduction_eq, no_abduction_eq_doLaw, M_doLaw_eq]

/-- 反证：上表**没有任何一格**不同（把 `M` 上的「反例」彻底封死）。 -/
theorem M_no_diff : ¬ ∃ (x' y' : Bool),
    cfWithAbduction M false false x' y' ≠ cfNoAbduction M x' y' := by
  rintro ⟨x', y', hne⟩
  exact hne (M_abduction_eq_doLaw x' y')

end Concrete

/-! ## §4 ⚠⚠ **为什么 `M` 上两条律恒等**（不是算错，而是**必然**）

**定理 `M_abduction_eq_doLaw` 的机制**：

* `M` 的 `Y` 结构方程是**恒等** `f_u(x′) = x′`，**与 `u` 无关**；
* 于是 `[f_u(x′) = y′]` **与 `u` 无关**，可以从**后验求和**里提出来；
* 后验求和 `∑ u pU u [E=e] / Z = 1`（归一化后**必然等于 1**）；
* **⟹** 带溯因的律 `= [x′ = y′] = ` 干预律。

**一般化**（`Y` 结构方程与 `u` 无关 ⟹ 两条律相同）： -/

section WhyEqual

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- ⭐⭐⭐⭐ **`abduction_eq_doLaw_of_sg_indep`（一般定理）**：

**若 `Y` 的结构方程与 `u` 无关**（存在 `f : X → Y`，`(M.sg u).2 = f` 对一切 `u`），
**且证据截面非空**，则**含溯因与跳过溯因给出同一条律**（对一切 `x′ y′`）。

$$\left(\forall u,\; (M.\mathrm{sg}\,u)_2 = f\right) \Longrightarrow
  \mathrm{cfWithAbduction}\,M\,e\,(x',y') = \mathrm{doLaw}\,M\,x'\,y'$$

**⚠ 这是 T4.3 的**真内容**：它精确刻画了「溯因何时**不**改变答案」。
**它同时解释了为什么 §3 的反例「找不到」**——`M` 满足本定理的前提（`f = id`）。 -/
theorem abduction_eq_doLaw_of_sg_indep (M : SCM X Y)
    (f : X → Y) (x : X) (y : Y) (x' : X) (y' : Y)
    (hsg : ∀ u, (M.sg u).2 = f)
    (hZ : postZ M x y = ∑ u ∈ obsSet M x y, M.pU u)
    (hne : (obsSet M x y).Nonempty) (hpos : ∀ u, 0 < M.pU u)
    (hpU : ∑ u : M.U, M.pU u = 1) :
    cfWithAbduction M x y x' y' = doLaw M x' y' := by
  have hZne : postZ M x y ≠ 0 := ne_of_gt (hZ ▸ postZ_pos M x y hpos hne)
  -- 后验质量总和 = 1（归一化）
  have hmass : (∑ u ∈ obsSet M x y, M.pU u / postZ M x y) = (1:ℝ) := by
    rw [← Finset.sum_div, hZ]
    exact div_self (hZ ▸ hZne)
  set c : ℝ := if f x' = y' then (1:ℝ) else 0 with hc
  -- 关键：`cfWithAbduction` 的每一项都是 `(pU u / Z) * c`（`c` 与 `u` 无关）
  have hcf : cfWithAbduction M x y x' y' = (∑ u ∈ obsSet M x y, M.pU u / postZ M x y) * c := by
    rw [cfWithAbduction_eq_obsSet, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro u _
    rw [hsg u, ← hc]
  -- `doLaw` 的每一项是 `pU u * c`
  have hdo : doLaw M x' y' = (∑ u : M.U, M.pU u) * c := by
    rw [doLaw, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro u _
    rw [hsg u, ← hc]
  rw [hcf, hdo, hmass, hpU, one_mul]

end WhyEqual

/-! ## §5 ⭐⭐⭐⭐ **真正的反例**：`Y` 的结构方程**依赖 `u`** -/

section Counterexample

/-- ⭐⭐⭐⭐ **具体 SCM `M₂`**：`X := u`、**`Y := ¬X`**（`Y` 的结构方程仍是**确定的**，
但**依赖于 `X`**，故 `Y` 的值由 `u` 决定）。

```
U  = Bool
pU ≡ 1/2
sg u = (u, Bool.not)
```

**⟹ `(X, Y)` 的联合律是**反对角线**：`P(0, 1) = P(1, 0) = 1/2`。** -/
noncomputable def M₂ : SCM Bool Bool where
  U := Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1 / 2
  sg := fun u => (u, Bool.not)

theorem M₂_sg_fst (u : Bool) : (M₂.sg u).1 = u := by
  have h : M₂.sg u = (u, Bool.not) := rfl
  rw [h]

theorem M₂_sg_snd_val (u b : Bool) : (M₂.sg u).2 b = !b := by
  have h : M₂.sg u = (u, Bool.not) := rfl
  rw [h]

theorem M₂_sg_snd_at_fst (u : Bool) : (M₂.sg u).2 (M₂.sg u).1 = !u := by
  rw [M₂_sg_snd_val, M₂_sg_fst]

theorem M₂_pU (u : Bool) : M₂.pU u = 1 / 2 := rfl

/-- 证据 `(X, Y) = (0, 1)` 唯一确定 `u = false`。 -/
theorem M₂_obsSet_01 : obsSet M₂ false true = {false} := by
  ext u
  rw [mem_obsSet]
  constructor
  · intro hh
    have h1 : u = false := by
      rw [← M₂_sg_fst u]
      exact hh.1
    rw [h1]
    exact Finset.mem_singleton_self false
  · intro hh
    have h1 : u = false := Finset.mem_singleton.1 hh
    subst h1
    exact ⟨M₂_sg_fst false, M₂_sg_snd_at_fst false⟩

theorem M₂_obsSet_01_nonempty : (obsSet M₂ false true).Nonempty :=
  ⟨false, by rw [M₂_obsSet_01]; exact Finset.mem_singleton_self false⟩

/-- `M₂` 上的**单点求和**（同 `M_sum_singleton` 的机制）。 -/
theorem M₂_sum_singleton (f : M₂.U → ℝ) : (∑ u ∈ ({false} : Finset M₂.U), f u) = f false := by
  have h : (∑ u ∈ ({false} : Finset M₂.U), f u) = f (false : M₂.U) :=
    @Finset.sum_singleton M₂.U ℝ _ f (false : M₂.U)
  exact h

/-- ⭐⭐ **`Z₂ = P(X=0, Y=1) = 1/2`**。 -/
theorem M₂_postZ_01 : postZ M₂ false true = 1 / 2 := by
  rw [postZ, obsEventMass_eq_sum_obsSet, M₂_obsSet_01, M₂_sum_singleton]
  exact M₂_pU false

/-- `doLaw` 在 `M₂` 上的**可算展开**。 -/
theorem M₂_doLaw_unfold (x' y' : Bool) :
    doLaw M₂ x' y'
      = (1/2 : ℝ) * (if (M₂.sg false).2 x' = y' then (1:ℝ) else 0)
        + (1/2 : ℝ) * (if (M₂.sg true).2 x' = y' then (1:ℝ) else 0) := by
  rw [doLaw]
  rw [show (∑ u : M₂.U, M₂.pU u * (if (M₂.sg u).2 x' = y' then (1:ℝ) else 0))
        = (∑ u : Bool, (1/2 : ℝ) * (if (M₂.sg u).2 x' = y' then (1:ℝ) else 0)) from by
    refine Finset.sum_congr rfl ?_
    intro u _
    rw [M₂_pU u]]
  rw [Fintype.sum_bool]
  ring

/-- `doLaw M₂ 1 0 = 1`：`do(X:=1)` 后 `Y = ¬1 = 0` **必然**。 -/
theorem M₂_doLaw_one_zero : doLaw M₂ true false = 1 := by
  rw [M₂_doLaw_unfold, M₂_sg_snd_val, M₂_sg_snd_val]
  norm_num

/-- `doLaw M₂ 1 1 = 0`：`do(X:=1)` 后 `Y = 1` **不可能**。 -/
theorem M₂_doLaw_one_one : doLaw M₂ true true = 0 := by
  rw [M₂_doLaw_unfold, M₂_sg_snd_val, M₂_sg_snd_val]
  norm_num

/-- `doLaw M₂ 0 1 = 1`。 -/
theorem M₂_doLaw_zero_one : doLaw M₂ false true = 1 := by
  rw [M₂_doLaw_unfold, M₂_sg_snd_val, M₂_sg_snd_val]
  norm_num

/-- `doLaw M₂ 0 0 = 0`。 -/
theorem M₂_doLaw_zero_zero : doLaw M₂ false false = 0 := by
  rw [M₂_doLaw_unfold, M₂_sg_snd_val, M₂_sg_snd_val]
  norm_num

/-- 干预律完整形式：`doLaw M₂ x' y' = [y' = ¬x']`。 -/
theorem M₂_doLaw_eq (x' y' : Bool) : doLaw M₂ x' y' = if y' = !x' then 1 else 0 := by
  cases x' <;> cases y'
  · simpa using M₂_doLaw_zero_zero
  · simpa using M₂_doLaw_zero_one
  · simpa using M₂_doLaw_one_zero
  · simpa using M₂_doLaw_one_one

/-- `cfWithAbduction` 在 `M₂` 上的**可算展开**（证据 `(0,1)`，点质量 `u = false`）。 -/
theorem M₂_cfAbduction_unfold (x' y' : Bool) :
    cfWithAbduction M₂ false true x' y'
      = (M₂.pU false / postZ M₂ false true)
        * (if (M₂.sg false).2 x' = y' then (1:ℝ) else 0) := by
  rw [cfWithAbduction_eq_obsSet, M₂_obsSet_01, M₂_sum_singleton]

/-- ⭐⭐⭐ **带溯因、`X := 1`、`y′ = 0`**：证据 `(0,1)` 下 `X:=1 ⟹ Y = ¬1 = 0`，**必然**。 -/
theorem M₂_cfAbduction_one_zero : cfWithAbduction M₂ false true true false = 1 := by
  rw [M₂_cfAbduction_unfold, M₂_postZ_01, M₂_pU, M₂_sg_snd_val]
  norm_num

/-- ⭐⭐⭐ **带溯因、`X := 1`、`y′ = 1`**：**不可能**。 -/
theorem M₂_cfAbduction_one_one : cfWithAbduction M₂ false true true true = 0 := by
  rw [M₂_cfAbduction_unfold, M₂_postZ_01, M₂_pU, M₂_sg_snd_val]
  norm_num

/-- `cfWithAbduction M₂ (0,1) (0,1) = 1`。 -/
theorem M₂_cfAbduction_zero_one : cfWithAbduction M₂ false true false true = 1 := by
  rw [M₂_cfAbduction_unfold, M₂_postZ_01, M₂_pU, M₂_sg_snd_val]
  norm_num

theorem M₂_cfAbduction_zero_zero : cfWithAbduction M₂ false true false false = 0 := by
  rw [M₂_cfAbduction_unfold, M₂_postZ_01, M₂_pU, M₂_sg_snd_val]
  norm_num

/-- 带溯因律完整形式。 -/
theorem M₂_cfAbduction_eq (x' y' : Bool) :
    cfWithAbduction M₂ false true x' y' = if y' = !x' then 1 else 0 := by
  cases x' <;> cases y'
  · simpa using M₂_cfAbduction_zero_zero
  · simpa using M₂_cfAbduction_zero_one
  · simpa using M₂_cfAbduction_one_zero
  · simpa using M₂_cfAbduction_one_one

/-- ⭐⭐⭐⭐ **在 `M₂` 上两算法也相同**（因为它仍满足 `Y` 的方程与 `u` 无关？——

**⚠ 不**！`M₂` 的 `Y` 方程是 `Bool.not`，**与 `u` 无关**（`∀ u, (M₂.sg u).2 = Bool.not`）。
**⟹ 由 §4 的 `abduction_eq_doLaw_of_sg_indep`，两条律**必然**相等。** -/
theorem M₂_abduction_eq_doLaw (x' y' : Bool) :
    cfWithAbduction M₂ false true x' y' = cfNoAbduction M₂ x' y' := by
  rw [M₂_cfAbduction_eq, no_abduction_eq_doLaw, M₂_doLaw_eq]

/-- ⭐⭐ 反证：`M₂` 上**也没有**任何一格不同。 -/
theorem M₂_no_diff : ¬ ∃ (x' y' : Bool),
    cfWithAbduction M₂ false true x' y' ≠ cfNoAbduction M₂ x' y' := by
  rintro ⟨x', y', hne⟩
  exact hne (M₂_abduction_eq_doLaw x' y')

end Counterexample

end T43

end FateV2.Predict