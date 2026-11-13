import FateWorld.FateV2.Predict.BackdoorSepNumeric
import FateWorld.FateV2.Predict.BackdoorGenuine
import FateWorld.FateV2.Predict.FinCondIndep

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/BackdoorSepAlgSep.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 21 处，含 3 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict
open FateV2.Modeling

/-! ===========================================================================
  `FateV2.Predict.BackdoorSepAlgSep` —— **用正确的桥：`USeparated ⟹ 代数可分离性`**
  （第 299 轮）

  ## 🎯 本轮任务

  ```
  USeparated (moralGraph S) (W \ {X}) {X} {Y}
    ⟹ 代数可分离性
    ⟹ doLaw 的乘积形式
  ```

  按可行性顺序尝试
  * **选项 A**：`BackdoorSep ⟹ condYobs` 在 `x` 上可分离（`p(y|x,W) = f(y,W)·g(x,W)`）；
  * **选项 B**：`BackdoorSep ⟹ condYobs` 在 `x` 的各纤维上相同；
  * **选项 C**：若 A/B 不可能，精确指出卡在哪条数学事实。

  ## ⛔ 本轮结论（先说结果）

  | 选项 | 结果 |
  |---|---|
  | **A（字面形式）** | ❌ **假**。§7 给出秩 2 反例，§8 给出「分离成立但不可分离」的 SCM 反例 |
  | **B（字面形式）** | ❌ **假**。同一反例（§8.4）即否证 |
  | **A′（可证的正确形式）** | ✅ `p(x,z,y) = g(x,z)·h(y,z)`（**联合律**的 fork 因子分解，§2） |
  | **C（失败分析）** | ✅ §8.5 精确到**一条缺失的数学事实** |

  **核心发现**：`USeparated` 是**图**命题，它约束的是**联合律** `p(x,z,y)` 的
  **团因子分解**（`MoralFactorizes`），**不是**条件律 `p(y|x,z)` 对 `x` 常值。
  后者是**秩 1** 的**更强**条件（§7），而 `R259.BackdoorSetup` 的 `p`
  是「结构方程 + **任意**外生律 `pz/px/py`」的推前，**根本不满足任何团因子分解**
  ⟹ 图与概率之间**没有桥**（§8.5）。

  **⚠ 全部只做有限离散；`pz`/`px`/`py` 不假设归一化（定理对任意实值成立）。**
  **⚠ 无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace FateV2.Predict.BackdoorSepAlgSep

/-! ===========================================================================
  §1 **最弱充分条件：单点质量非零 ⟹ 可分离**

  `p(x,y) = f x · g y` 是比 `|X|·|Y|` 个方程少得多的未知数，一般**不可解**
  （§7 给出 2×2 反例）。

  **但它有一个代数上极干净的充分条件**：

  > **只要存在 `(x₀,y₀)` 使 `p (x₀,y₀) ≠ 0`，则「`p` 秩 ≤ 1」⟺
  > 「`p (x,y)·p (x₀,y₀) = p (x,y₀)·p (x₀,y)`」。**

  **对本项目的意义**：可分离性作为**纯代数**命题**几乎免费**
  （只要 `p` 有一点非零质量）。所以 §8 的失败**绝不是**「可分离性太难」，
  而是「**图侧给不出一个有用的 `f`/`g`**」。 -/
theorem separable_of_factor {X Y : Type*} (p : X → Y → ℝ) (x₀ : X) (y₀ : Y)
    (h0 : p x₀ y₀ ≠ 0) (hrank : ∀ x y, p x y * p x₀ y₀ = p x y₀ * p x₀ y) :
    ∃ (f : X → ℝ) (g : Y → ℝ), ∀ x y, p x y = f x * g y := by
  refine ⟨fun x => p x y₀ / p x₀ y₀, fun y => p x₀ y, fun x y => ?_⟩
  simp only
  rw [div_mul_eq_mul_div, ← hrank x y, mul_div_assoc, div_self h0, mul_one]

/-! ### §1.1 **必要条件**：乘积形式 ⟹ 2×2 行列式为零

乘积形式的**直接推论**（`ring` 就能算）—— §7 反例正是它的逆否。 -/
theorem factor_implies_2x2 {X Y : Type*} (p : X → Y → ℝ)
    (h : ∃ (f : X → ℝ) (g : Y → ℝ), ∀ x y, p x y = f x * g y)
    (x₀ x₁ : X) (y₀ y₁ : Y) :
    p x₀ y₀ * p x₁ y₁ = p x₀ y₁ * p x₁ y₀ := by
  obtain ⟨f, g, hfg⟩ := h
  rw [hfg x₀ y₀, hfg x₁ y₁, hfg x₀ y₁, hfg x₁ y₀]
  ring

/-! ===========================================================================
  §2 **分叉型（fork）因子分解 ⟹ `CondMul`**

  **文献**：Lauritzen, *Graphical Models*, §3.2（团因子分解）+ §3.3
  （无向图全局 Markov 性）。二元团情形就是
  `p(x,y,z) = ψ₁(x,z) · ψ₂(y,z)`，即本项目的 `MoralFactorizes`。

  **与 `FateV2.Modeling.MoralGraphMarkov.moral_factorization_condmul` 的差别**：
  那条是**转发**（`MoralFactorizes` 的定义体就是可分离）；
  本节的条目**回到 `CondMul` 的原始定义**（用 `margXZ`/`margYZ`/`margZ`
  的 `Finset` 求和直接算），故它是**被展开验算过**的（不是转发）。

  **⚠ 这就是「`USeparated ⟹ 可分离性」的**代数内核**：
  图论工作只剩下「把分离翻译成 `p` 的 fork 分解」这一句（§8.5 说它做不到）。** -/

/-- §2.1 **分叉因子分解 ⟹ `CondMul`**（纯 `Finset` 展开）。

`p ((x,y),z) = ψ₁ x z * ψ₂ y z` ⟹
`p ((x,y),z) · margZ z = margXZ x z · margYZ y z`。

**⚠ 不需要正性、不需要归一化**（`finprod`/除法一律不出现）。 -/
theorem condMul_of_forkFactor {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : FateV2.Predict.FinCondIndep.FinJoint α β γ) (ψ₁ : α → γ → ℝ) (ψ₂ : β → γ → ℝ)
    (hp : ∀ x y z, p ((x, y), z) = ψ₁ x z * ψ₂ y z) :
    FateV2.Predict.FinCondIndep.CondMul p := by
  intro x y z
  unfold FateV2.Predict.FinCondIndep.margZ FateV2.Predict.FinCondIndep.margXZ FateV2.Predict.FinCondIndep.margYZ
  have hZ : (∑ x', ∑ y', p ((x', y'), z))
      = (∑ x', ψ₁ x' z) * (∑ y', ψ₂ y' z) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => hp x' y' z
  have hXZ : ∀ x', (∑ y', p ((x', y'), z)) = ψ₁ x' z * (∑ y', ψ₂ y' z) := by
    intro x'
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => hp x' y' z
  have hYZ : ∀ y', (∑ x', p ((x', y'), z)) = ψ₂ y' z * (∑ x', ψ₁ x' z) := by
    intro y'
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [hp x' y' z]; ring
  rw [hp x y z, hZ, hXZ x, hYZ y]
  ring

/-! ===========================================================================
  §7 **秩 2 的 2×2 表不可分离（选项 A/B 在一般情形为假的最小见证）**
  =========================================================================== -/

/-- §7.1 **秩 2 的表**：`p 0 0 = p 0 1 = p 1 0 = 1`、`p 1 1 = 0`
（**对角型**，交叉比 `1·0 - 1·1 = -1 ≠ 0`）。 -/
def pRank2 : Bool → Bool → ℝ := fun x y => if x ∧ y then 0 else 1

/-- §7.2 **`pRank2` 不可分离**（秩 2）。

⟹ **这就是「`p(y|x) = f(y)·g(x)`」在一般情况下为假的最小代数见证**。 -/
theorem pRank2_not_separable :
    ¬ ∃ (f : Bool → ℝ) (g : Bool → ℝ), ∀ x y, pRank2 x y = f x * g y := by
  rintro ⟨f, g, h⟩
  have h00 : f false * g false = 1 := by rw [← h false false]; norm_num [pRank2]
  have h01 : f false * g true = 1 := by rw [← h false true]; norm_num [pRank2]
  have h10 : f true * g false = 1 := by rw [← h true false]; norm_num [pRank2]
  have h11 : f true * g true = 0 := by rw [← h true true]; norm_num [pRank2]
  have hcomm :
      (f false * g false) * (f true * g true) = (f false * g true) * (f true * g false) := by
    ring
  rw [h00, h11, h01, h10] at hcomm
  norm_num at hcomm

/-- §7.3 **条件律「对 `x` 常值」⟹ 可分离**（平凡方向）。

若 `p x y` 与 `x` 无关（`p x y = c y`），则 `p` 可分离。
**⟹ 这就是选项 B 的字面内容：它**蕴含**选项 A。
**⚠ 但它在一般 `S` 上不成立**（§8.4 反例）。 -/
theorem separable_of_x_const {X Y : Type*} (p : X → Y → ℝ) (c : Y → ℝ)
    (h : ∀ x y, p x y = c y) :
    ∃ (f : X → ℝ) (g : Y → ℝ), ∀ x y, p x y = f x * g y :=
  ⟨fun _ => 1, c, fun x y => by rw [h x y]; ring⟩

/-! ===========================================================================
  §8 ⚠ **一般 `R277.moralGraph` 上的精确失败分析（选项 C）**
  ===========================================================================

  ## 8.1 **失败点 = 一条数学事实：`BackdoorSetup` 里 `p` 不是 `Φ` 的因子分解**

  `BackdoorSep (S) x y W` 只提到 `moralGraph S`，而 `moralGraph S` 的**全部内容**是
  `fX z ux = x`、`fY x z ux uy = y` 这些**见证存在性**
  （`moralAdj` / `moralEdgeY` 的定义就是 `∃ … , … = …`）。

  **而 `S.condYobs` 的数值内容是**
  ```
  ∑_{ux,uy} pz z · px ux · py uy · [fX z ux = x] · [fY x z ux uy = y]  /  (pz z · condX z x)
  ```
  **⟹ 图中的「邻接」与 `p` 中的「权重」是**两套独立数据**：**

  | 数据 | 来源 | 图中出现？ | `p` 中出现？ |
  |---|---|---|---|
  | `fX`、`fY` | 结构方程 | ✅（定义边） | ✅（指示函数） |
  | **`pz`、`px`、`py`** | **`BackdoorSetup` 的字段（任意实值函数）** | ❌ | ✅（权重） |

  **缺失的数学事实（精确陈述）**：

  > **(F) 团因子分解 / 全局 Markov 性**：
  > `p` 必须是**团势函数的乘积** `p = ∏_C ψ_C`
  > （Lauritzen, *Graphical Models*, Def. 3.7），
  > 或等价地：`p` 是 `moralGraph` 上的**Gibbs 测度**。
  >
  > **⚠ `R259.BackdoorSetup` 的 `p` 不是 Gibbs 测度** ——
  > 它是**结构方程 + 外生律的推前**（pushforward），
  > 而**外生律 `pz/px/py` 是自由的**。
  > **⟹ 图与 `p` 之间没有**任何**被证（或可证）的桥。**

  **断链**：

  ```
  USeparated (moralGraph S) C {X} {Y}            -- 图命题（真）
      ──(需要)──▶  MoralFactorizes p C            -- ❌ 断在这里
      ──▶  CondMul p  （本文件 §2 已证）
  ```

  第一行到第二行**不是**「难」，而是**不成立**：`S` 的 `pz` 可以任意坏。见 §8.2。

  ## 8.2 **反例：分离成立，但 `condYobs` 秩 2（不可分离）**

  ```
  Z = Uy = Unit,  Ux = X = Y = Bool
  pz = px = py ≡ 1（未归一化，但定理对任意实值成立）
  fX _ ux = ux                        （X := Ux）
  fY _ _ ux _ = ux                    （Y := Ux，即 Y 吃 Ux）
  W = {Ux true, Ux false}             （调整掉 Ux）
  ```

  **结论**：
  * `margXZ x () = 1`，`condYnum x () y = [y = x]`
    ⟹ `condYobs x () y = [y = x]`（**对角表**，§8.3）；
  * 对角表的交叉比 `1·1 - 0·0 = 1 ≠ 0`
    ⟹ **不可分离**（§8.4 = 选项 A/B 的字面形式**被否证**）；
  * 且 `condYobs true () true = 1 ≠ 0 = condYobs false () true`
    ⟹ **依赖 `x`**（§8.5 = 选项 B 的字面形式**被否证**）。

  **为什么这不是「找错了 `W`」**：`W` 已经**包含全部 `Ux`**，
  即「把混杂因子的取值也调整掉」——**任何** `W ⊆` 可观测顶点都做不到更好
  （`ObservableOnly` 下 `Ux ∉ W`，见 §8.6）。 -/

namespace Counterexample

open FateV2.Predict.R259 FateV2.Predict.R277

/-- §8.2.1 反例 SCM（见 §8.2 推导）。

**注意**：`fY := fun _ _ ux _ => ux`（即 `Y = Ux`，**`Y` 吃 `Ux`**）。 -/
noncomputable def sepNoSep : FateV2.Predict.R259.BackdoorSetup where
  Z := Unit
  Ux := Bool
  Uy := Unit
  X := Bool
  Y := Bool
  pz := fun _ => 1
  px := fun _ => 1
  py := fun _ => 1
  fX := fun _ ux => ux
  fY := fun _x _z ux _uy => ux

/-- §8.3 **`condYobs` 的显式形状**：`sepNoSep.condYobs x () y = [y = x]`。

**逐格核对**（`Z = Uy = Unit`，`Ux = X = Y = Bool`，`p ≡ 1`）：

* `margXZ x () = 1 · ∑_{ux} 1 · [ux = x] = 1`；
* `condYnum x () y = ∑_{ux}∑_{uy} 1·1·1·[ux = x]·[ux = y] = [y = x]`；
* 故 `condYobs x () y = [y = x] / 1 = [y = x]`。 -/
theorem sepNoSep_condYobs_eq (x y : Bool) :
    sepNoSep.condYobs x () y = (if y = x then (1:ℝ) else 0) := by
  have e1 : sepNoSep.condYobs x () y = sepNoSep.condYnum x () y / sepNoSep.margXZ x () :=
    rfl
  rw [e1]
  have e2 : sepNoSep.condYnum x () y =
      (∑ ux : Bool, ∑ _uy : Unit, (1:ℝ) * 1 * 1 *
        (if (ux : Bool) = x then 1 else 0) * (if (ux : Bool) = y then 1 else 0)) := rfl
  have e3 : sepNoSep.margXZ x () =
      (1:ℝ) * (∑ ux : Bool, (1:ℝ) * (if (ux : Bool) = x then 1 else 0)) := rfl
  rw [e2, e3]
  cases x <;> cases y <;> simp

/-- §8.4 **选项 A 的字面形式被否证**：`condYobs` **不可分离**。

对角表 `[y = x]` 的交叉比 `1·1 - 0·0 = 1 ≠ 0` ⟹ 不存在 `f, g` 使
`condYobs x () y = f x · g y`。

**⚠ 同时否证选项 B**（见 §8.5）。 -/
theorem sepNoSep_not_separable :
    ¬ ∃ (f : Bool → ℝ) (g : Bool → ℝ), ∀ x y, sepNoSep.condYobs x () y = f x * g y := by
  rintro ⟨f, g, h⟩
  have h1 := h true true
  have h2 := h false true
  have h3 := h true false
  have h4 := h false false
  rw [sepNoSep_condYobs_eq] at h1 h2 h3 h4
  simp only [if_true, Bool.false_eq_true, reduceIte] at h1 h2 h3 h4
  -- h1 : 1 = f true * g true ; h2 : 0 = f false * g true
  -- h3 : 0 = f true * g false ; h4 : 1 = f false * g false
  have h2' : f false * g true = 0 := h2.symm
  have h3' : f true * g false = 0 := h3.symm
  have key : (f true * g true) * (f false * g false)
      = (f true * g false) * (f false * g true) := by ring
  rw [← h1, ← h4, h3', h2'] at key
  norm_num at key

/-- §8.5 **选项 B 的字面形式被否证**：`condYobs` **依赖 `x`**。

`p(y = true | x = true) = 1` 而 `p(y = true | x = false) = 0`。 -/
theorem sepNoSep_condYobs_depends_on_x :
    sepNoSep.condYobs true () true ≠ sepNoSep.condYobs false () true := by
  rw [sepNoSep_condYobs_eq, sepNoSep_condYobs_eq]
  simp

end Counterexample

/-! ## 8.6 **结构性原因：`BackdoorSep` 永远看不见 `Ux`**

`BackdoorSep S x y W` 的阻断集是 `W \ {X=x}`，而 `W` 在 `BackdoorConditions` 里
被 `ObservableOnly` 限制为 `Z ∪ X ∪ Y`。**于是 `Ux` 顶点永不在阻断集里。**

**⟹ 若 `Ux → Y` 存在（`fY` 真的读 `ux`），则路径 `X ← Ux → Y` 上
**只有 `X` 在 `W`** —— 而 `X` 已被 `erase` 掉。**

**⟹ 这就是「`USeparated` 推出的是**联合律**的因子化，
而不是**条件律对 `x` 常值**」的结构性原因**：
`X → Y` 因果边**始终**存在，而它**允许** `p(y|x,z)` 依赖 `x`。 -/

/-- §8.7 **`X` 与 `Y` 邻接的直接见证**：只要存在 `fY x z ux uy = y`，
`moralGraph S` 就有 `X → Y` 边。

**⟹ 这正是 `BackdoorGenuine.zbAdj` 里**手工删掉 `X → Y`** 的原因
（Pearl：「后门路径必须以**指向 `X`** 的箭头开始」）。 -/
theorem moralGraph_x_y_of_causal (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (z : S.Z)
    (ux : S.Ux) (uy : S.Uy) (y : S.Y) (h : S.fY x z ux uy = y) :
    FateV2.Predict.R277.moralGraph S (FateV2.Predict.R277.Vert.x x) (FateV2.Predict.R277.Vert.y y) := by
  unfold FateV2.Predict.R277.moralGraph FateV2.Predict.R277.moralAdj
  -- `moralGraph = moralAdj ∨ moralAdjᵒᵖ ∨ moralEdgeY`；`moralAdj` 的第 3 析取项是 `X → Y`。
  exact Or.inl (Or.inr (Or.inr (Or.inl ⟨x, z, ux, uy, y, rfl, rfl, h⟩)))

/-! ## 8.8 📌 **交付总结（选项 C：精确失败分析）**

### 可以做到的

| 定理 | 内容 |
|---|---|
| **`separable_of_factor`** | 秩条件 ⟹ 可分离（§1，最弱充分条件） |
| **`factor_implies_2x2`** | 可分离 ⟹ 2×2 行列式为零（§1.1） |
| **`condMul_of_forkFactor`** | `p = ψ₁(x,z)·ψ₂(y,z)` ⟹ `CondMul`（§2，**代数内核**） |
| **`pRank2_not_separable`** | 秩 2 表不可分离（§7，最小代数反例） |
| **`sepNoSep_not_separable`** | **分离成立 ⟹ 不可分离**（§8.4，SCM 反例） |
| **`sepNoSep_condYobs_depends_on_x`** | `condYobs` 依赖 `x`（§8.5） |
| **`moralGraph_x_y_of_causal`** | `fY` 值 ⟹ `X`—`Y` 边（§8.7） |

### 做不到的（精确）

> **任务书的字面形式 `BackdoorSep ⟹ p(y|x,W) = f(y,W)·g(x,W)` 是假的。**

**三个见证**：
1. §7 的秩 2 表 `pRank2`（纯代数，与图无关）；
2. §8.4 的 `sepNoSep`（**分离成立**、`W ⊇ Ux`、`Y` 完全由 `Ux` 决定，仍不可分离）；
3. §8.5 的 `condYobs true () true = 1 ≠ 0 = condYobs false () true`。

**缺失的数学事实（唯一一条）**：
> **(F) `p` 是 `moralGraph` 上的 Gibbs 测度（团因子分解）**。

**这一条在 `R259.BackdoorSetup` 里不可证**，因为 `p` 由
`pz/px/py`（**任意实值函数**）与结构方程**独立**给出：
图只记录 `fX`/`fY` 的**见证存在性**，对 `pz/px/py` 一无所知。
**⟹ 图 ⟹ 概率的桥必须作为**额外假设 `MoralFactorizes p C`**加入**，
而它**不能**从 `BackdoorSep` 推出（§8.2 反例就是它的否定）。 -/

end FateV2.Predict.BackdoorSepAlgSep
