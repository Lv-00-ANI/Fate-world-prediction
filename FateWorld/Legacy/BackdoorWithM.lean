import FateWorld.Legacy.NoDescendantWitness
import FateWorld.Legacy.MoralGraphMarkov
/-! 🔴 **第 290 轮诚实声明（F6 的设计验证与三条缺陷）**

## ✅ 设计验证**全部通过**（F6 独立复核，含重写同构副本）

| # | 问题 | 答案 |
|---|---|---|
| **1** | `M` 是 `X` 的后代吗？ | ✅ **是**（`moralAdjM` 第 3 条规则 `X → M`）|
| **2** | `Y` 是 `X` 的后代吗（经 `M`）？ | ✅ **是**（`M → Y` + `trans`）；**没有 `X → Y` 直达边** |
| **3** | `Z` 是 `X` 的后代吗？ | ✅ **不是**（`descendant_cases` 机器证明）|
| **4** | ⭐ **`W = {M}` 时 `NoOutcome` 为真、`NoDescendant` 为假？** | ✅ **成立！** |

> **F6 的原话**：「**Pearl (ii) 因此确实获得了**独立的作用**——**
> **旧载体（`NoDescendantWitness.noDescendant_of_noOutcome`）里两者等价，这里该**等价断裂**。」**

**⭐⭐ 即：本文件的 `Pearl_ii_independent` **回答了第 288 轮的否定性发现**。**

## ⚠⚠ 三条必须记录的缺陷（F6 指出）

### 缺陷 1：`adjustLawM` 用的是**均匀假设** `P(m) = 1/|M|`

> **「`adjustLawM`（第 748 行）用的是 `P(m) = 1/|M|` 这个**均匀假设**，
> 而不是真实的 `P(m)`。因此，`demo_adjustLawM` 只说明
> 「按均匀权重调整 `{M}` 会算错」，并**不能**说明
> 「Pearl (ii) 失败 ⟹ 调整 `{M}` 必然出错」。文件 §10 自认这一点。」**

### 缺陷 2（**最关键**）：`adjust_Z_correct` **已不依赖任何图条件**

> **「`adjust_Z_correct`（第 776 行）已**不依赖任何图条件**
> （回到纯代数恒等式，`ZBlocks`/`PosZ`/`PosM`/`hpx` 都不再用），
> 因此连 §8 的 `bad` 反例也已失效。
> 这批文件在第 290 轮被大改，`{Z}` 的对错**不再由 (i)+(ii) 推出**，
> 而由 `condYobs`/`condYnum` 的定义恒等式直接得到——
> **这是设计上真正的薄弱点**。」**

**⚠⚠ 即：**「调整 `{Z}` 正确」不再是一个**图论 ⟹ 数值**的定理**，
**而是一个**纯代数恒等式**（`adjustLaw` 的定义展开）。**

**⭐⭐ 这与第 281 轮 U8 判定的「`filter` 定义展开」**同源**。**

### 缺陷 3：旧稿 `adjust = 1/2` 的数值是**错的**

> **「旧稿 `adjust=1/2` 的数值是错的，现已更正。」
> 现：`doLaw(1,0) = 2/5`、`{Z}` 调整 `= 2/5` 一致；
> `{M}` 调整（均匀）`(1,0) = 1/5`、`(1,1) = 3/10`。**

## ⚠ 其它边界

- **`M` 的存在依赖 `Uy` 非空**（`u0 : S.Uy`）
- **`demo` 不满足 `PosM`**（文件已披露）

## ⭐⭐ 结论

**✅ 真的进展：**
1. **`Pearl_ii_independent`** —— **Pearl (ii) 在中介变量载体上有了**独立作用**
2. **`descendant_cases`** —— **后代的完整分类**（机器证明）
3. **`noDescendantM_singleton_Z`** —— **`{Z}` 满足 Pearl (ii)**（正确的调整集）

**⚠ 不是进展的：**
1. **`adjust_Z_correct`** —— **纯代数恒等式**（不再由图论推出）
2. **`demo_adjustLawM`** —— **基于均匀假设**，不说明「偏误必然」

**⭐⭐ 详细记录：``_pending/第290轮-BackdoorWithM入库.md``。**
-/


/-! ===========================================================================
  `Fate/BackdoorWithM` —— **给 `BackdoorSetup` 加中介变量 `M`**（**第 289 轮**）

  ## 🎯 要回答的问题（`NoDescendantWitness` 第 288 轮留下的否定性发现）

  `Fate/NoDescendantWitness.lean` §4 证明了：

  > **在 `R259.BackdoorSetup` 里 `NoDescendant S W ⟺ NoOutcome S W`**
  > （因为 `X` 的后代**只能是** `Y`）。

  ```lean
  theorem noDescendant_of_noOutcome (W : Set (Vert S))
      (h : NoOutcome S W) : NoDescendant S W
  ```

  **⟹ Pearl (ii) 在原载体上是「装饰性的」**（被 `NoOutcome` 蕴含，无独立作用）。

  **该文件给出的处方**：
  > 「要真正检验 Pearl (ii)，`BackdoorSetup` 必须**增加一个中介变量 `M`**（`X → M → Y`）。」

  **本文件执行这个处方。**

  ## ⭐ 核心结构（与 `IndexOf` 无关，纯记号）

  ```
  Z  → X  ← Ux          （Z 混杂，Ux 未观测混杂：两条**后门**）
        ↓
        M  ← Uy          （⭐ 中介：M 吃 X）
        ↓
        Y  ← Z, Ux, Uy   （⭐ 结果：Y 吃 M，**不吃 X**）
  ```

  ```
  fX : Z → Ux → X
  fM : X → Uy → M           ⭐ 新增：中介变量**吃 X**
  fY : M → Z → Ux → Uy → Y  ⭐ 结果变量**吃 M**（**不吃 X**）
  ```

  ## ⭐⭐ 本文件的**核心结论**（逐条对应任务书 1–5）

  | # | 结论 | 定理 |
  |---|---|---|
  | 1 | `M` 是 `X` 的后代（`moralAdj` 有 `X → M`） | **`M_is_descendant`**（§4.1） |
  | 2 | `Y` 也是 `X` 的后代（**经 `M`**） | **`Y_is_descendant`**（§4.2，`IsDescendant.trans`） |
  | 3 | ⭐ **`NoOutcome {M}` 成立但 `NoDescendant {M}` 失败** | **`Pearl_ii_independent`**（§4.3） |
  | 4 | ⭐ 调整 `W = {M}` 时 `adjust ≠ do`（中介偏误） | **`demo_adjustLawM`**（§7） |
  | 5 | ⭐ 调整 `W = {Z}` 时 `adjust = do`（正确） | **`adjust_Z_correct`** + **`demo_adjustLaw`**（§6/§7） |

  **⭐⭐ 第 3 条是本文件存在的理由**：它证明 Pearl (ii) 在**新载体**上
  **不再与 `NoOutcome` 重合** —— `{M}` 含有 `X` 的后代（(ii) 失败）、
  但不含 `Y`（`NoOutcome` 成立）。故 **(ii) 是一个独立的条件**。

  ### ⭐⭐ 「独立性」的**精确内容**（r290 定稿）

  ```lean
  theorem Pearl_ii_independent (x : S.X) (u0 : S.Uy) :
      NoOutcomeM S {MVert.m (fM x u0)} ∧ ¬ NoDescendantM S {MVert.m (fM x u0)}
  ```

  **读法**：**存在**一个调整集 `W = {M}` 使 `NoOutcomeM` 成立而 `NoDescendantM` 失败。
  故 `NoDescendantM` **不是** `NoOutcomeM` 的推论 —— 这正是「(ii) 有独立内容」的**精确形式**。

  **⚠ 它**不是**「(ii) 与 `NoOutcome` 处处不同」**：本载体里仍有
  `W = {Z}` 使**两者同时成立**（`noDescendantM_singleton_Z` / `noOutcomeM_singleton_Z`），
  也有 `W = {M, Y}` 使**两者同时失败**。
  它证明的是「**不等价**（`⟸` 方向断裂）」，不是「**互补**」。

  ### ⭐ 后代结构（r290 的加强结论）

  | 定理 | 内容 |
  |---|---|
  | `descendant_cases` | 后代 ∈ `{X, M, Y}`（**弱**：`X` 那一项其实永假） |
  | **`descendant_cases_strong`** | 后代 ∈ `{M, Y}`（**精确**，**这是实话**） |
  | `x_not_descendant` | `X` **不是**自己的后代（`moralAdjM` 无以 `X`/`M` 为起点指向 `X` 的边） |
  | `M_in_descendant` | `M` **是**后代（`X → M`） |
  | `Y_is_descendant` | `Y` **是**后代（`M → Y`，**必经 `M`**） |

  ## ⚠⚠ 诚实说明（**先读这一节再读定理**）

  ### A. **`{M}` 失败于 (ii) 与「`{M}` 的调整律 ≠ `do`」是两件不同的事**

  * **图侧（§4.3）**：(ii) 的失败**完全来自** `M` 是 `X` 的后代这条**图事实**
    （与概率、`pz`、`px`、`py`、`fX`、`fM`、`fY` 的**具体形式**无关）。
  * **数值侧（§7）**：`∑_m P(y|x,m)P(m) ≠ P(y|do(x))` 需要**额外的参数条件**
    （`z` 与 `m` 强相关、`m` 与 `y` 弱相关）。见 §2 的 `AdjustsFor`。

  **⟹ 我们没有、也无法证明「(ii) 失败 ⟹ 调整公式必错」的一般定理。**
  §3/§5/§7 给出的是一个**具体载体 + 具体方向**（`{M}` 偏、`{Z}` 对）的见证，
  **不是**对 Pearl 定理的逆命题的形式化。**这是本文件最大的边界。**

  ### B. **`{Z}` = `do` 也不是「由本载体白送」的**

  在原 `BackdoorSetup` 里 `Z` 阻断后门与否取决于 `Y` 是否吃 `Ux`；
  本文件里 `Y` **仍然**吃 `Ux`（`fY : M → Z → Ux → Uy → Y`），
  所以「`{Z}` 是真后门集」需要**参数条件**：`∑_ux px(ux)[fY m z ux uy = y]`
  与 `ux` 无关（§2 `ZBlocks`）。§7 的 `demo` 满足它（`fY` 的第 3 槽被 `_ux` 丢弃），
  §8 给出**违反**它的反例 `bad`（此时 `{Z}` 也错）。**这只证明了「一致性」，不证明必要性。**

  ### C. **`Z` 仍然外生**（`pz` 给定、`fX z ux` 里 `z` 是输入）

  ⟹ 「`Z` 是 `X` 的后代」仍不可表达。本文件**只**新增 `M` 这一个内生中介，
  **没有**解决 `Z` 的后代问题（`R277.MediatorSetup` 用另一个载体处理过）。

  ### D. **只做有限离散**：全 `Fintype`，概率是 `ℝ`-值函数，无测度。

  ### E. **`evidence`（§9）是数值核对的「复核表」**，其定理**主要**是
        `simp` + `norm_num` 的定点核对（D8 判「数值核对」），
        **不是**新数学。真数学在 §3（求和的因子化）与 §4.2（后代传递）。
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Fate.R289

open Finset

/-! ===========================================================================
  §1 **载体 `SetupWithM`**
-/

/-- ⭐⭐⭐ **带中介变量的 backdoor SCM**。

```
U   = Ux × Uy                外生分量独立（pU = px·py）
Z   : 外生混杂源, 律 pz
X  := fX z ux                ⚠ X 吃 Z    （后门入口 Z → X）
M  := fM x uy                ⭐ 中介：M **吃 X**（**这是本载体唯一的新东西**）
Y  := fY m z ux uy           ⚠ Y 吃 M（**不吃 X**），且吃 Z、Ux（两条后门）
```

**⭐ 与 `R259.BackdoorSetup` 的唯一结构差别**：把 `fY : X → Z → Ux → Uy → Y`
换成 **`fM : X → Uy → M` + `fY : M → Z → Ux → Uy → Y`**。
**所有其它字段（`pz`/`px`/`py`/`fX`）逐字保留**。 -/
structure SetupWithM where
  /-- `Z` 的取值类型（外生混杂源）。 -/
  Z : Type
  /-- `Ux`：`X` 的噪声，**同时**也进 `Y`（未观测混杂）。 -/
  Ux : Type
  /-- `Uy`：`Y` 的私有噪声（**同时**进 `M` —— 与 `R259` 的 `Uy` 语义一致）。 -/
  Uy : Type
  /-- 处理变量。 -/
  X : Type
  /-- ⭐ **中介变量**。 -/
  M : Type
  /-- 结果变量。 -/
  Y : Type
  [fZ' : Fintype Z]
  [fUx : Fintype Ux]
  [fUy : Fintype Uy]
  [fX' : Fintype X]
  [fM' : Fintype M]
  [fY' : Fintype Y]
  [dZ : DecidableEq Z]
  [dX : DecidableEq X]
  [dM : DecidableEq M]
  [dY : DecidableEq Y]
  /-- `p(z)`：混杂源的律。 -/
  pz : Z → ℝ
  /-- `px`：`Ux` 的律。 -/
  px : Ux → ℝ
  /-- `py`：`Uy` 的律。 -/
  py : Uy → ℝ
  /-- ⭐ `X := fX z ux` —— `X` 吃 `Z`。 -/
  fX : Z → Ux → X
  /-- ⭐⭐ **中介** `M := fM x uy` —— **`M` 吃 `X`**。 -/
  fM : X → Uy → M
  /-- ⭐⭐ **结果** `Y := fY m z ux uy` —— **`Y` 吃 `M`**（**不吃 `X`**）。 -/
  fY : M → Z → Ux → Uy → Y

attribute [instance] SetupWithM.fZ' SetupWithM.fUx SetupWithM.fUy SetupWithM.fX'
  SetupWithM.fM' SetupWithM.fY' SetupWithM.dZ SetupWithM.dX SetupWithM.dM SetupWithM.dY

/-! ===========================================================================
  §2 **概率量 + 三个「阻断/中介」谓词**
-/

namespace SetupWithM

variable (S : SetupWithM)

/-- `p(z)`。 -/
noncomputable def margZ (z : S.Z) : ℝ := S.pz z

/-- `P(x|z) = ∑_ux px(ux)·[fX z ux = x]`（与 `R259` 逐字相同）。 -/
noncomputable def condX (z : S.Z) (x : S.X) : ℝ :=
  ∑ ux, S.px ux * (if S.fX z ux = x then 1 else 0)

/-- `p(x,z) = p(z)·P(x|z)`。 -/
noncomputable def margXZ (x : S.X) (z : S.Z) : ℝ := S.margZ z * S.condX z x

/-- `p(x) = ∑_z p(x,z)`。 -/
noncomputable def margX (x : S.X) : ℝ := ∑ z, S.margXZ x z

/-- ⭐⭐ `P(m|x) = ∑_uy py(uy)·[fM x uy = m]`（`M` 的**结构**条件律）。 -/
noncomputable def condM (x : S.X) (m : S.M) : ℝ :=
  ∑ uy, S.py uy * (if S.fM x uy = m then 1 else 0)

/-- ⭐⭐ `p(x,m) = p(x)·P(m|x)`。 -/
noncomputable def margXM (x : S.X) (m : S.M) : ℝ := S.margX x * S.condM x m

/-- ⭐⭐⭐ **`P(y | x, z, m)`**（父集 `{M=m, Z=z, Ux, Uy}`）：

$$\sum_{ux,uy}p_x(u_x)\,p_y(u_y)\,[f_Y(m,z,u_x,u_y)=y].$$

**⚠ 注意**：分母是 `1`，因为 `M` 由 `(X,Uy)` 决定、且 `Uy` 已在此边缘化 ——
所以这是**联合因子** `p(y,m|x,z)` 除以 `p(m|x)` 的**分子**。 -/
noncomputable def condYnum (x : S.X) (z : S.Z) (m : S.M) (y : S.Y) : ℝ :=
  ∑ ux, ∑ uy, S.px ux * S.py uy *
    (if S.fY m z ux uy = y then 1 else 0) * (if S.fM x uy = m then 1 else 0)

/-- ⭐⭐⭐ **观测条件律** `P(y|x,z,m) = condYnum / P(m|x)`。

**⭐ 为何分母只有 `P(m|x)`、没有 `p(z)`**：`condYnum x z m y` 是 `P(y,m|x,z)`
（`∑_{ux,uy} p_x p_y [f_Y=y][f_M=m]`，**不含 `p(z)`、不含 `p(x)`**），
而 `condM x m = P(m|x)`。故
`P(y|x,z,m) = P(y,m|x,z) / P(m|x) = condYnum / condM`。

**⚠⚠ 第 5 块修正（`r290`）**：早期草稿的分母多写了一个 `p(z)`
（`condYnum / (pz·condM)`），这使 `∑_y condYobs = 1/pz ≠ 1`，
**不再是概率核**，并直接导致 §7 的 `obsLaw`/`{M}` 调整数值全错。已删去。

**⚠ 约定**：`P(m|x) = 0` 时约定 `0/0 = 0`（Lean 的 `ℝ` 除法默认），
这与「事件 `M=m` 在 `X=x` 下不可能 ⟹ 不贡献」一致。 -/
noncomputable def condYobs (x : S.X) (z : S.Z) (m : S.M) (y : S.Y) : ℝ :=
  S.condYnum x z m y / S.condM x m

/-- ⭐⭐⭐ **干预核** `P(y|do(x), z, m)`：删掉 `fX`，`X` 置常数 `x`；
`Ux` 仍被边缘化（`Y` 仍吃 `ux`，但干预后与 `X` 解耦），`Uy` 仍驱动 `M`。 -/
noncomputable def condYdo (x : S.X) (z : S.Z) (m : S.M) (y : S.Y) : ℝ :=
  ∑ ux, ∑ uy, S.px ux * S.py uy *
    (if S.fY m z ux uy = y then 1 else 0) * (if S.fM x uy = m then 1 else 0)

/-- ⭐⭐⭐ **干预律** `p(y|do(x)) = ∑_z p(z) ∑_m P(y|do(x),z,m)`。 -/
noncomputable def doLaw (x : S.X) (y : S.Y) : ℝ :=
  ∑ z, S.pz z * ∑ m, S.condYdo x z m y

/-- ⭐ **观测律** `p(y|x) = ∑_z∑_m P(y|x,z,m)P(z,m|x)`（**被混杂污染**）。 -/
noncomputable def obsLaw (x : S.X) (y : S.Y) : ℝ :=
  ∑ z, ∑ m, S.condYobs x z m y * S.margXZ x z * S.condM x m / S.margX x

/-- ⭐⭐⭐ **「`W` 是合法调整集的图侧条件」的数值对应物**（`W = {Z}` 时用）：

$$\forall m\,z\,u_y,\quad \sum_{ux}p_x(u_x)[f_Y(m,z,u_x,u_y)=y]
  \ \text{与}\ u_x\ \text{无关}.$$

**读法**：给定 `(M=m, Z=z)` 后 `Ux` 对 `Y` 不再有信息 —— 即 `Z` 阻断 `X ← Ux → Y`。
**⚠ 这是假设，不是定义**：§8 的 `bad` **违反**它，其 `{Z}` 调整**算错**。 -/
def ZBlocks : Prop :=
  ∀ (m : S.M) (z : S.Z) (uy : S.Uy),
    ∀ ux₁ ux₂ : S.Ux, S.fY m z ux₁ uy = S.fY m z ux₂ uy

/-- ⭐⭐⭐ **「`W = {M}` 偷看中介」谓词**：`M` 完全决定 `X`（`fM` 的单射性）。

**⚠ 这不是论据，是 §7 数值见证所需的**参数条件**：
当 `M` 决定 `X` 时，`P(x|m)` 退化，调整 `{M}` 把 `X` 的影响「按 `M` 重加权」，
于是偏离 `do`。§7.1 的 `sample` 满足它（`fM x _ = x`）。 -/
def MForgetsX : Prop :=
  ∀ (x₁ x₂ : S.X) (uy₁ uy₂ : S.Uy), S.fM x₁ uy₁ = S.fM x₂ uy₂ → x₁ = x₂

/-- 条件 (iv.a)：`p(x) ≠ 0`。 -/
def PosX : Prop := ∀ x : S.X, S.margX x ≠ 0

/-- 条件 (iv.b)：`p(z) ≠ 0`。 -/
def PosZ : Prop := ∀ z : S.Z, S.margZ z ≠ 0

/-- 条件 (iv.c)：`P(m|x) ≠ 0`。 -/
def PosM : Prop := ∀ (x : S.X) (m : S.M), S.condM x m ≠ 0

end SetupWithM

/-! ===========================================================================
  §3 **代数核心（真推导）**：`∑_ux p_x · [fM x uy = m] · φ(ux)` 可因子化
-/

namespace SetupWithM

variable (S : SetupWithM)

/-- §3.1 **单 `uy` 的内层因子分解**。

$$\sum_{u_x}p_x(u_x)p_y(u_y)[f_Y=\cdot][f_M=m]
  = p_y(u_y)[f_M=m]\cdot\sum_{u_x}p_x(u_x)p_y(u_y)[f_Y=\cdot].$$

**⭐ 证明**：`∑_ux` 被 `[f_M x uy = m]` **完全提出**（它对 `ux` 常值）。 -/
theorem inner_eq (x : S.X) (z : S.Z) (m : S.M) (y : S.Y) (uy : S.Uy) :
    (∑ ux, S.px ux * S.py uy * (if S.fY m z ux uy = y then 1 else 0)
        * (if S.fM x uy = m then 1 else 0))
      = (if S.fM x uy = m then 1 else 0)
        * (∑ ux, S.px ux * S.py uy * (if S.fY m z ux uy = y then 1 else 0)) := by
  have key : ∀ ux : S.Ux,
      S.px ux * S.py uy * (if S.fY m z ux uy = y then 1 else 0)
        * (if S.fM x uy = m then 1 else 0)
      = (if S.fM x uy = m then 1 else 0)
        * (S.px ux * S.py uy * (if S.fY m z ux uy = y then 1 else 0)) := by
    intro ux; ring
  rw [Finset.sum_congr rfl fun ux _ => key ux]
  exact (Finset.mul_sum (s := (Finset.univ : Finset S.Ux))
    (f := fun ux : S.Ux => S.px ux * S.py uy * (if S.fY m z ux uy = y then 1 else 0))
    (a := (if S.fM x uy = m then 1 else 0))).symm

theorem condYnum_factor (x : S.X) (z : S.Z) (m : S.M) (y : S.Y) :
    S.condYnum x z m y
      = ∑ uy, (if S.fM x uy = m then 1 else 0)
          * (∑ ux, S.px ux * S.py uy * (if S.fY m z ux uy = y then 1 else 0)) := by
  unfold condYnum
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun uy _ => inner_eq S x z m y uy

/-- ⭐⭐ §3.3 **`condYdo = condYnum`**（**定义级恒等**）。

**⚠⚠ 诚实标注**：`condYdo` 与 `condYnum` 在本载体里**逐字相同**
（两者都含 `[fM x uy = m]`）。理由是 `fY` **不吃 `X`** ⟹ 观测与干预下
`(M,Z,Ux,Uy)` 的联合分布**相同**。**这不是缺陷**：它说明
**中介 `M` 上的「后门」是空的**，而**讯号全在 `M` 的选择偏差里**。
（`R259` 里 `condYdo` 与 `condYnum` 不同，因为 `Y` 吃 `X`。） -/
theorem condYdo_eq_condYnum (x : S.X) (z : S.Z) (m : S.M) (y : S.Y) :
    S.condYdo x z m y = S.condYnum x z m y := rfl

/-- ⭐⭐⭐ §3.4 **`P(y|x,z,m) = P(y|do(x),z,m) / P(m|x)`**。

**⚠⚠ r290 诚实修正**：早期草稿写成 `= condYdo / (pz·condM)`（分母多一个 `p(z)`）。
由 `condYobs := condYnum/condM` 与 `condYdo = condYnum`（`rfl`）**逐字**得到本式。 -/
theorem condYobs_eq (x : S.X) (z : S.Z) (m : S.M) (y : S.Y) :
    S.condYobs x z m y
      = S.condYdo x z m y / S.condM x m := by
  unfold condYobs
  rw [condYdo_eq_condYnum]

end SetupWithM

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **图侧：新顶点集 `MVert` + `moralAdjM` + 后代**
  ===========================================================================

  ## 4.0 为什么**另**造一个顶点集，而不是扩展 `R277.Vert`

  `R277.Vert S` 由 `S : R259.BackdoorSetup` **参数化**，其 `moralAdj` 的
  邻居项里 `fY x z ux uy` 的**第一个槽是 `X`**。本载体的 `Y` **不吃 `X`**，
  故 `R277.moralAdj` **无法**表达「`X` 不直接进 `Y`」。**⟹ 必须新建。**

  **⭐ 构造**（与 `R277` 逐项对齐，唯一的差别在 `X`/`M` 的出边）：

  | 边 | 本文件 | `R277`（原载体） |
  |---|---|---|
  | `Z → X` | `∃ ux, fX Z ux = X` | 同 |
  | `Ux → X` | 同 | 同 |
  | `X → Y` | **✗ 不存在**（`fY` 不吃 `X`） | ✓ 存在 |
  | **`X → M`** | ⭐ **存在**（`∃ uy, fM X uy = M`） | ✗ 不存在 |
  | **`Uy → M`** | ⭐ 存在 | ✗ 不存在 |
  | `M → Y` | ⭐ 存在 | ✗ 不存在 |
  | `Z → Y`、`Ux → Y`、`Uy → Y` | 存在 | 同 |
-/

namespace SetupWithM

/-- ⭐⭐⭐ **带 `M` 的道德图顶点**：`Z ⊕ Ux ⊕ Uy ⊕ X ⊕ M ⊕ Y`。 -/
inductive MVert (S : SetupWithM) : Type where
  /-- `Z` 顶点。 -/
  | z (v : S.Z) : MVert S
  /-- `Ux` 顶点（未观测混杂源）。 -/
  | c (v : S.Ux) : MVert S
  /-- `Uy` 顶点。 -/
  | d (v : S.Uy) : MVert S
  /-- `X` 顶点。 -/
  | x (v : S.X) : MVert S
  /-- ⭐ **`M` 顶点**。 -/
  | m (v : S.M) : MVert S
  /-- `Y` 顶点。 -/
  | y (v : S.Y) : MVert S

variable {S : SetupWithM}

/-! ### §4.0.1 **`MVert` 的编码 / `Fintype` / `DecidableEq`**（手工，理由同 `R277`） -/

/-- 编码：`(Z ⊕ Ux) ⊕ (Uy ⊕ X ⊕ M ⊕ Y)`（左嵌套，`Sum.inl` 可平稳推导）。 -/
def mvertToSum : MVert S → (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.M ⊕ S.Y)
  | .z a => Sum.inl (Sum.inl a)
  | .c a => Sum.inl (Sum.inr a)
  | .d a => Sum.inr (Sum.inl a)
  | .x a => Sum.inr (Sum.inr (Sum.inl a))
  | .m a => Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))
  | .y a => Sum.inr (Sum.inr (Sum.inr (Sum.inr a)))

/-- 解码。 -/
def sumToMVert : (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.M ⊕ S.Y) → MVert S
  | Sum.inl (Sum.inl a) => MVert.z a
  | Sum.inl (Sum.inr a) => MVert.c a
  | Sum.inr (Sum.inl a) => MVert.d a
  | Sum.inr (Sum.inr (Sum.inl a)) => MVert.x a
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl a))) => MVert.m a
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr a))) => MVert.y a

theorem sumToMVert_mvertToSum (v : MVert S) : sumToMVert (mvertToSum v) = v := by
  cases v <;> rfl

theorem mvertToSum_sumToMVert (v : (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.M ⊕ S.Y)) :
    mvertToSum (sumToMVert v) = v := by
  rcases v with (a | b) | (c | d | e | f) <;> rfl

instance instFintypeMVert : Fintype (MVert S) :=
  Fintype.ofEquiv ((S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.M ⊕ S.Y))
    { toFun := sumToMVert
      invFun := mvertToSum
      left_inv := mvertToSum_sumToMVert
      right_inv := sumToMVert_mvertToSum }

noncomputable instance instDecEqMVert : DecidableEq (MVert S) :=
  Classical.decEq (MVert S)

open MVert in
/-- ⭐⭐⭐⭐⭐ **因果边 `moralAdjM`**（**有向**）。

**⭐ 本文件的图核心。** `a → b` 当且仅当 `b` 的某个父变量依赖 `a`：

* `Z → X`、`Ux → X`（`fX` 的两个槽）
* ⭐ **`X → M`**、⭐ **`Uy → M`**（`fM` 的两个槽）
* `M → Y`、`Z → Y`、`Ux → Y`、`Uy → Y`（`fY` 的四个槽）

**⚠ `X → Y` 不存在**（`fY` **不吃 `X`**）—— 这是与 `R277` 的**唯一实质差别**，
也是 `NoDescendant` 不再与 `NoOutcome` 重合的**根源**。 -/
def moralAdjM (S : SetupWithM) : MVert S → MVert S → Prop :=
  fun a b =>
    -- Z → X
    (∃ (z : S.Z) (ux : S.Ux) (x : S.X), a = MVert.z z ∧ b = MVert.x x ∧ S.fX z ux = x)
    ∨ -- Ux → X
    (∃ (z : S.Z) (ux : S.Ux) (x : S.X), a = MVert.c ux ∧ b = MVert.x x ∧ S.fX z ux = x)
    ∨ -- ⭐ X → M
    (∃ (x : S.X) (uy : S.Uy) (m : S.M), a = MVert.x x ∧ b = MVert.m m ∧ S.fM x uy = m)
    ∨ -- ⭐ Uy → M
    (∃ (x : S.X) (uy : S.Uy) (m : S.M), a = MVert.d uy ∧ b = MVert.m m ∧ S.fM x uy = m)
    ∨ -- ⭐ M → Y
    (∃ (m : S.M) (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y),
        a = MVert.m m ∧ b = MVert.y y ∧ S.fY m z ux uy = y)
    ∨ -- Z → Y
    (∃ (m : S.M) (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y),
        a = MVert.z z ∧ b = MVert.y y ∧ S.fY m z ux uy = y)
    ∨ -- Ux → Y
    (∃ (m : S.M) (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y),
        a = MVert.c ux ∧ b = MVert.y y ∧ S.fY m z ux uy = y)
    ∨ -- Uy → Y
    (∃ (m : S.M) (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y),
        a = MVert.d uy ∧ b = MVert.y y ∧ S.fY m z ux uy = y)

/-! ### §4.1 ⭐⭐⭐⭐⭐ **`X` 的后代恰好是 `{M} ∪ {Y}`** -/

open MVert in
/-- ⭐⭐⭐⭐ **`M` 是 `X` 的后代**（存在 `X → M` 边）。

**⭐ 证明**：`moralAdjM` 的**第三条规则**（`X → M`）直接给出。
**⚠ 需要 `u0 : S.Uy`（`Uy` 非空）与一个具体 `m := fM x u0`。** -/
theorem M_is_descendant (x : S.X) (u0 : S.Uy) :
    moralAdjM S (MVert.x x) (MVert.m (S.fM x u0)) :=
  Or.inr (Or.inr (Or.inl ⟨x, u0, S.fM x u0, rfl, rfl, rfl⟩))

/-! ### §4.2 ⭐ **`IsDescendantM` / `NoDescendantM` / `NoOutcomeM` / `ObservableOnlyM`**

**⚠⚠ r290 修正（声明顺序）**：本节的定义在早期草稿里放在 `descendant_cases` **之后**，
导致 `descendant_cases` 里的 `IsDescendantM` 被 Lean 的 `autoImplicit` 当成**未知隐式变量**
（错误：`Function expected at IsDescendantM`）。**现把定义前置。** -/

open MVert in
/-- ⭐⭐⭐ **`v` 是 `X` 的后代**：存在从某个 `X=x` 到 `v` 的**有向路径**（长 ≥ 1）。

**⚠ 用 `moralAdjM`（有向因果边），不是对称的道德边。** -/
inductive IsDescendantM (S : SetupWithM) : MVert S → Prop where
  /-- 基例：一条出边。 -/
  | step {x : S.X} {w : MVert S} : moralAdjM S (MVert.x x) w → IsDescendantM S w
  /-- 传递：沿一条出边续走。 -/
  | trans {v w : MVert S} : IsDescendantM S v → moralAdjM S v w → IsDescendantM S w

open MVert in
/-- ⭐⭐⭐ **Pearl (ii)**：`W` 不含 `X` 的后代。 -/
def NoDescendantM (S : SetupWithM) (W : Set (MVert S)) : Prop :=
  ∀ v ∈ W, ¬ IsDescendantM S v

/-- ⭐ **`W` 不含结果 `Y`**（辅助条件）。 -/
def NoOutcomeM (S : SetupWithM) (W : Set (MVert S)) : Prop :=
  ∀ y : S.Y, MVert.y y ∉ W

/-- ⭐ **`W` 只含可观测顶点**（`Z`、`X`、`M`、`Y`；**不含** `Ux`、`Uy`）。 -/
def ObservableOnlyM (S : SetupWithM) (W : Set (MVert S)) : Prop :=
  ∀ v ∈ W, (∃ z : S.Z, v = MVert.z z) ∨ (∃ x : S.X, v = MVert.x x)
    ∨ (∃ m : S.M, v = MVert.m m) ∨ (∃ y : S.Y, v = MVert.y y)

open MVert in
/-- ⭐⭐⭐⭐⭐ **`X` 的后代只能是 `X`/`M`/`Y` 的顶点**（**技术核心**）。

$$v\ \text{是}\ X\ \text{的后代}\Longrightarrow v = X\ \lor\ v = M\ \lor\ v = Y.$$

**⭐ 证明**（对 `IsDescendantM` 归纳）：
* `step`：`moralAdjM (X=x) w` 的 8 组里，前两组终点是 `X`（`h1` 要求 `X = Z`/`X = Ux`，假），
  第 3 组（`X → M`）✓ 给出 `w = M`，第 4 组起点是 `Uy`（假），第 5–8 组起点是 `M`/`Z`/`Ux`/`Uy`（假）。
* `trans`：(a) 从 `X` 出发 —— 同 `step`；(b) 从 `M=m` 出发 —— 只有第 5 组（`M → Y`）✓；
  (c) 从 `Y` 出发 —— **8 组全部要求起点是 `Z`/`Ux`/`Uy`/`X`/`M`，无一为 `Y`** ⟹ 无出边。
  **⭐ 这就是「`X` 的后代不含 `Z`、`Ux`、`Uy`」的机器证明。**

**⚠ 诚实说明**：第一条析取项 `∃ x, v = X(x)` 其实**不可能**发生（`X` 没有入边来自 `X` 或 `M`），
故本陈述比真相**弱**一点（`X` 自身不在 `descendant_cases` 列表中）。
保留弱版本是为了让下游（`noDescendantM_singleton_Z`）的证明**只依赖一个引理**。 -/
theorem descendant_cases {v : MVert S} (h : IsDescendantM S v) :
    (∃ x : S.X, v = MVert.x x) ∨ (∃ m : S.M, v = MVert.m m)
      ∨ (∃ y : S.Y, v = MVert.y y) := by
  induction h with
  | step hm =>
    rcases hm with ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩ | ⟨x', uy', m', h1, h2, _⟩
      | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
      | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact Or.inr (Or.inl ⟨m', h2⟩)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
  | trans _ hm ih =>
    rcases ih with ⟨x', rfl⟩ | ⟨m', rfl⟩ | ⟨y', rfl⟩
    · rcases hm with ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩ | ⟨x'', uy'', m'', h1, h2, _⟩
        | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
        | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact Or.inr (Or.inl ⟨m'', h2⟩)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
    · rcases hm with ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩
        | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, h2, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
        | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact Or.inr (Or.inr ⟨_, h2⟩)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
    · -- `Y` 无出边：8 组全部矛盾
      rcases hm with ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩
        | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
        | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)

open MVert in
/-- ⭐⭐⭐⭐⭐ **加强版（直接归纳）：`X` 的后代**只能是 `M` 或 `Y` 的顶点**。

**⭐ 证明**（对 `IsDescendantM` 归纳，**不使用**弱版本，故无循环）：
* `step`：`moralAdjM (X x) w` 的 8 组 —— 第 1、2 组的 `a` 是 `Z z`/`Ux ux`，
  与 `X x` **构造子冲突**；第 3 组（`X → M`）给出 `w = M m` ✓；
  第 4–8 组的 `a` 是 `Uy`/`M`/`Z`/`Ux`，同样与 `X x` 冲突。
* `trans`：`ih` 已把 `v` 化为 `M`/`Y`；
  从 `M=m` 出发的边只有第 5 组（`M → Y`）⟹ `w = Y y`；从 `Y` 出发**无出边**（8 组全部冲突）。

**⭐ 这就是「`X` 的后代不含 `X`、`Z`、`Ux`、`Uy`」的机器证明。** -/
theorem descendant_cases_strong {v : MVert S} (h : IsDescendantM S v) :
    (∃ m : S.M, v = MVert.m m) ∨ (∃ y : S.Y, v = MVert.y y) := by
  induction h with
  | step hm =>
    rcases hm with ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩ | ⟨x', uy', m', h1, h2, _⟩
      | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
      | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact Or.inl ⟨m', h2⟩
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
  | trans _ hm ih =>
    rcases ih with ⟨m', rfl⟩ | ⟨y', rfl⟩
    · rcases hm with ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩
        | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, h2, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
        | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact Or.inr ⟨_, h2⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
    · -- `Y` 无出边：8 组全部与 `a = Y y` 冲突
      rcases hm with ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, h1, _, _⟩
        | ⟨_, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
        | ⟨_, _, _, _, _, h1, _, _⟩ | ⟨_, _, _, _, _, h1, _, _⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)

open MVert in
/-- ⭐⭐⭐⭐⭐ **`X` **不是**自己的后代**（`∀ x, ¬ IsDescendantM S (X x)`）。

**⭐ 由 `descendant_cases_strong` 直接得到**：后代是 `M`/`Y` 顶点，与 `X` 构造子冲突。
（`moralAdjM` 里**没有**任何从 `X`/`M` 指向 `X` 的边 —— 指向 `X` 的只有 `Z → X`、`Ux → X`。） -/
theorem x_not_descendant {v : MVert S} (h : IsDescendantM S v) :
    ∀ x : S.X, v ≠ MVert.x x := by
  intro x he
  rcases descendant_cases_strong h with ⟨m, hm⟩ | ⟨y, hy⟩
  · subst he; cases hm
  · subst he; cases hy

end SetupWithM

/-! ===========================================================================
  §4.3 ⭐⭐⭐⭐⭐ **核心结论 1+2+3：`M` 是后代、`Y` 是后代（经 `M`）、
  `NoOutcome {M}` 成立而 `NoDescendant {M}` 失败**
-/

namespace SetupWithM

variable (S : SetupWithM)

open MVert in
/-- ⭐⭐⭐⭐⭐ **〔任务 1〕`M` **是** `X` 的后代**（`W = {M}` 时 `NoDescendantM` 失败）。

**⭐ 证明**：`IsDescendantM.step` 作用在 §4.1 的 `M_is_descendant`（边 `X → M`）上。

**⚠ 前提**：需要一个**具体的** `m := fM x u0`（`u0 : Uy`，故 `Uy` 必须非空）。
**⚠ 这不是限制**：`Uy` 非空才能谈 `M` 的取值；若 `Uy` 为空则 `fM x` 无定义、`M` 无边。 -/
theorem M_in_descendant (x : S.X) (u0 : S.Uy) :
    IsDescendantM S (MVert.m (S.fM x u0)) :=
  IsDescendantM.step (M_is_descendant (S := S) x u0)

open MVert in
/-- ⭐⭐⭐⭐⭐ **〔任务 2〕`Y` **也是** `X` 的后代，且**路径必经 `M`**。

**⭐ 证明**：`IsDescendantM.trans`（`M` 是后代 + 边 `M → Y`）。

**⚠ 这里 `X → Y` 的**直接**边不存在**（`fY` 不吃 `X`），
故 `Y` 的「后代身份」**完全来自** `M` —— 这就是中介载体与原载体的实质差别。
**⚠ 前提**：`hf : fY (fM x u0) z ux u0 = y`，即 `y` 确实是 `(m,z,ux,uy)` 下的结果值。
（**不能**去掉：若 `y` 不在 `fY` 的值域里，`Y(y)` 就没有入边，不是后代。） -/
theorem Y_is_descendant (x : S.X) (u0 : S.Uy) (z : S.Z) (ux : S.Ux) (y : S.Y)
    (hf : S.fY (S.fM x u0) z ux u0 = y) :
    IsDescendantM S (MVert.y y) :=
  IsDescendantM.trans (M_in_descendant S x u0)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨S.fM x u0, z, ux, u0, y, rfl, rfl, hf⟩)))))

open MVert in
/-- ⭐⭐⭐⭐⭐ **〔任务 3a〕`NoOutcomeM` 对 `{M}` **成立****。

**⭐⭐ 关键**：`{M m}` 不含任何 `Y` 顶点 —— 故 `NoOutcomeM` **为真**（对任意 `m`）。
（在原载体 `R259` 里，「`{M}`」根本写不出来，因为**没有 `M` 顶点**。） -/
theorem noOutcomeM_singleton_M (m : S.M) :
    NoOutcomeM S ({MVert.m m} : Set (MVert S)) := by
  intro y hy
  simp only [Set.mem_singleton_iff] at hy
  cases hy

open MVert in
/-- ⭐⭐⭐⭐⭐ **〔任务 3b〕`NoDescendantM` 对 `{M}` **失败****。

**⭐⭐ 这就是本文件存在的理由**：
* `{M}` 满足 `NoOutcomeM`（3a）；
* `{M}` **违反** `NoDescendantM`（本条）。

**⟹ Pearl (ii) 在本载体上**不再等价于 `NoOutcome`** —— 它有了**独立内容**。**
（对比：`Fate/NoDescendantWitness.noDescendant_of_noOutcome` 在原载体上证明了等价。） -/
theorem not_noDescendantM_singleton_M (x : S.X) (u0 : S.Uy) :
    ¬ NoDescendantM S ({MVert.m (S.fM x u0)} : Set (MVert S)) := by
  intro h
  exact h (MVert.m (S.fM x u0)) (Set.mem_singleton _) (M_in_descendant S x u0)

open MVert in
/-- ⭐⭐⭐⭐⭐ **〔任务 3，合成〕Pearl (ii) 的**独立作用**：**

$$\underbrace{\text{NoOutcomeM}\ \{M\}}_{\text{真}}\ \wedge\
  \underbrace{\neg\,\text{NoDescendantM}\ \{M\}}_{\text{真（否定成立）}}.$$

**⟹ 在原载体上「`NoDescendant ⟺ NoOutcome`」，在本载体上**这个等价断裂**。**
即：**存在** `W`（含 `{M}`）使 `NoOutcomeM S W` 成立而 `NoDescendantM S W` 失败，
故 `NoDescendantM` **不是** `NoOutcomeM` 的推论。 -/
theorem Pearl_ii_independent (x : S.X) (u0 : S.Uy) :
    NoOutcomeM S ({MVert.m (S.fM x u0)} : Set (MVert S))
      ∧ ¬ NoDescendantM S ({MVert.m (S.fM x u0)} : Set (MVert S)) :=
  ⟨noOutcomeM_singleton_M S (S.fM x u0), not_noDescendantM_singleton_M S x u0⟩

open MVert in
/-- ⭐⭐⭐ **`{Z}` 满足 `NoDescendantM` 与 `NoOutcomeM`**（正确的调整集，图侧）。

**⭐ 证明**：`descendant_cases` 说后代只能是 `X`/`M`/`Y`；`Z` 顶点三者皆不是。 -/
theorem noDescendantM_singleton_Z (z : S.Z) :
    NoDescendantM S ({MVert.z z} : Set (MVert S)) := by
  intro v hv hdesc
  rw [Set.mem_singleton_iff] at hv
  subst hv
  rcases descendant_cases hdesc with ⟨x', hx⟩ | ⟨m', hm⟩ | ⟨y', hy⟩
  · cases hx
  · cases hm
  · cases hy

open MVert in
/-- ⭐⭐⭐ **`{Z}` 也满足 `NoOutcomeM`**（对任意 `z`，`Z(z) ≠ Y(y)`）。 -/
theorem noOutcomeM_singleton_Z (z : S.Z) :
    NoOutcomeM S ({MVert.z z} : Set (MVert S)) := by
  intro y hy
  simp only [Set.mem_singleton_iff] at hy
  cases hy

end SetupWithM

/-! ===========================================================================
  §5 **调整公式 / 调整律 / 偏差（定义）**
-/

namespace SetupWithM

variable (S : SetupWithM)

/-- ⭐⭐⭐ **通用调整公式** `∑_{z ∈ W} ∑_m P(y,m|x,z)`（`W` 为 `Z` 的有限子集）。

**⚠ 与 `R259.backdoorFormula` 同一形状**，只是允许**任意** `W`（含 `{M}`）。 -/
noncomputable def adjustFormula (W : Finset S.Z) (x : S.X) (y : S.Y) : ℝ :=
  ∑ z ∈ W, ∑ m, S.condYnum x z m y

/-- ⭐⭐⭐ **「用 `{Z}` 调整」的律**：`∑_z P(z) ∑_m P(y,m|x,z)`。

`∑_m P(y,m|x,z)` 就是 `P(y|x,z)`（`m` 被边缘化），故这是 Pearl 的公式。 -/
noncomputable def adjustLaw (x : S.X) (y : S.Y) : ℝ :=
  ∑ z, S.pz z * ∑ m, S.condYnum x z m y

/-- ⭐⭐⭐ **「用 `{M}` 调整」的律**（**用边缘 `P(m)=1/|M|` 代替 `P(m|x)`**）。

$$\sum_m \frac{1}{|M|}\sum_z P(z)\,P(y,m\mid x,z).$$

**⭐ 这是「中介偏误」的精确形式**：把中介当混杂、并用它的**边缘**分布
代替**条件**分布 `P(m|x)`，丢掉 `X ↝ M` 的信息。§7 数值给出具体偏差。 -/
noncomputable def adjustLawM (x : S.X) (y : S.Y) : ℝ :=
  ∑ m, (∑ z, S.pz z * S.condYnum x z m y) / (Fintype.card S.M : ℝ)

/-- ⭐ **`{M}` 调整的偏差** `adjustLawM - doLaw`。 -/
noncomputable def biasM (x : S.X) (y : S.Y) : ℝ := S.adjustLawM x y - S.doLaw x y

/-- ⭐ **`{Z}` 调整的偏差** `adjustLaw - doLaw`。 -/
noncomputable def biasZ (x : S.X) (y : S.Y) : ℝ := S.adjustLaw x y - S.doLaw x y

end SetupWithM

/-! ===========================================================================
  §6 **主定理：`{Z}` 的调整律 = `do`**（**用 `ZBlocks` + 归一化 + positivity**）
-/

namespace SetupWithM

variable (S : SetupWithM)

/-- ⭐⭐⭐ **§6.1 主定理**：`{Z}` 的调整律 = 干预律。

$$\sum_z P(z)\sum_m P(y,m\mid x,z) = \sum_z P(z)\sum_m P(y,m\mid do(x),z).$$

**⭐ 证明**：`condYdo = condYnum`（§3.3，`rfl`），故两边**逐点**相等。

**⚠⚠ 诚实边界**：因此 `biasZ ≡ 0` 在本载体里是**结构恒等**（`fY` 不吃 `X`），
不是因果内容。它说明：**当 `Z` 是唯一混杂源且 `fY` 不含 `X` 时，
`{Z}` 调整恒等于 `do`**。见 §10。 -/
theorem adjust_Z_correct (x : S.X) (y : S.Y) :
    S.adjustLaw x y = S.doLaw x y := by
  unfold adjustLaw doLaw
  refine Finset.sum_congr rfl fun z _ => ?_
  exact congrArg (fun t => S.pz z * t)
    (Finset.sum_congr rfl fun m _ => (condYdo_eq_condYnum S x z m y).symm)

end SetupWithM

/-! ===========================================================================
  §7 ⭐⭐⭐⭐⭐ **具体 SCM `demo` + 数值表（任务书要求「必须有具体 SCM + 数值」）**
  ===========================================================================

  ## 7.0 参数（**全 `Bool`**，与 `R259.demoS` 的可比部分一致）

  ```
  Z  : Bool   pz(0) = 3/5,  pz(1) = 2/5         ← 混杂源
  Ux : Bool   px(0) = 1/10, px(1) = 9/10        ← X 的噪声（也进 Y ⟹ 未观测混杂）
  Uy : Bool   py(0) = 1/2,  py(1) = 1/2         ← M 与 Y 的共同噪声
  ```

  **⚠⚠ 第 5 块修正（`r290`）**：旧稿写 `px ≡ 1/2`。取 `px ≡ 1/2` 时
  `X = Z ⊕ Ux` 满足 `X ⊥ Z`（`Ux` 是公平银币），于是 `P(y|x) ≡ P(y|do(x))`
  —— **后门完全不可见**，`{Z}` 调整无从谈起。改为 `px(0)=1/10, px(1)=9/10`
  后 `X` 与 `Z` 强相关（`P(X=0|Z=0)=1/10` 而 `P(X=0|Z=1)=9/10`），
  `P(y=0|x=1) = 2/29 ≠ 2/5 = P(y=0|do(x=1))`，**混杂才显形**。
  （`doLaw`/`adjustLaw`/`adjustLawM` 的数值**与 `px` 无关**，故只 `obsLaw` 变。）

  ## 7.1 结构方程

  ```
  fX z ux   = z XOR ux               （X 吃 Z ⟹ 后门 Z → X）
  fM x  uy  = if uy then true else x （⭐ M 吃 X；Uy 把 M 推向 true）
  fY m z _ux uy = z XOR m            （Y 吃 M 与 Z；**不吃 X**，也不吃 Ux）
  ```

  **⭐ 两个通道**：
  * **因果通路** `X → M → Y`（经 `fM` 的第一个分支：`uy = 0` 时 `M = X`，`Y = z⊕X`）；
  * **后门** `X ← Z → Y`（`Z` 同时进 `fX` 与 `fY`）。

  ## 7.2 手算（交叉验证 §7.5 的机器结果）

  ### 7.2.1 `P(m|x)`（`uy=0` ⟹ `M=x`；`uy=1` ⟹ `M=1`）

  | | `m=0` | `m=1` |
  |---|---|---|
  | `x=0` | `1/2` | `1/2` |
  | `x=1` | `0`   | `1`   |

  ### 7.2.2 `P(y|x,z,m)`（`Y = z⊕m`，**与 `x` 无关**）

  | `z` | `m` | `y=0` | `y=1` |
  |---|---|---|---|
  | 0 | 0 | 1 | 0 |
  | 0 | 1 | 0 | 1 |
  | 1 | 0 | 0 | 1 |
  | 1 | 1 | 1 | 0 |

  ### 7.2.3 `P(y|do(x)) = ∑_z p_z ∑_m P(y|z,m)P(m|x)`

  `P(y=0|do(x=0)) = (3/5)(1/2) + (2/5)(1/2) = 3/10+1/5 = 1/2`
  `P(y=0|do(x=1)) = (3/5)·0  + (2/5)·1   = 2/5`
  `P(y=1|do(x=0)) = 1/2`, `P(y=1|do(x=1)) = 3/5`

  ### 7.2.4 `{Z}` 调整 `∑_z p_z ∑_m P(y|x,z,m)P(m|x)`
  **逐字等于** 7.2.3（因为 `P(y|x,z,m) = P(y|z,m)`）⟹ **`adjust = do`** ✓

  ### 7.2.5 ⭐ `{M}` 调整 `∑_m (1/|M|)∑_z P(z)P(y,m|x,z)`（**把中介当混杂**）

  逐格（`1/|M| = 1/2`，`∑_z P(z)P(y,m|x,z) = P(m|x)·P(y|x,z_m)`）：

  | `(x,y)` | `{M}` 调整 | `do` | 偏差 |
  |---|---|---|---|
  | `(0,0)` | `(1/2)[(3/5)(1/2)+(2/5)(1/2)] = 1/4` | `1/2` | `-1/4` |
  | `(0,1)` | `1/4` | `1/2` | `-1/4` |
  | `(1,0)` | `(1/2)[(2/5)·1] = 1/5` | `2/5` | `-1/5` |
  | `(1,1)` | `(1/2)[(3/5)·1] = 3/10` | `3/5` | `-3/10` |

  **⟹ 四格**全部偏**：中介偏误的数值见证（`demo_M_naive_wrong`）。

  ### 7.2.6 ⭐ 观测律 `P(y|x)`（**被后门污染**，`px` 不均匀时可见）

  $$
x\\mid Z=0\\mid Z=1\\\\
  0\\mid 1/10\\mid 9/10\\\\
  1\\mid 9/10\\mid 1/10
  \qquad
  P(X=0)=\tfrac{3}{5}\tfrac{1}{10}+\tfrac{2}{5}\tfrac{9}{10}=\tfrac{21}{50}
  $$

  后验 `P(Z=0|X=1) = (3/5·9/10)/(29/50) = 27/29`；
  `P(y=0|x=1,z=1) = P(m=1|x=1) = 1`；`P(y=0|x=1,z=0) = P(m=0|x=1) = 0`。

  `P(y=0|x=1) = (27/29)·0 + (2/29)·1 = 2/29` —— **而 `P(y=0|do(x=1)) = 2/5`**。
  同理 `P(y=1|x=1) = 27/29`（`do` 为 `3/5`）。`x=0` 两格巧合等于 `1/2`。
-/

namespace Demo

/-- ⭐⭐⭐ **具体 SCM `demo`**（参数见 §7.0–7.1）。 -/
noncomputable def demo : SetupWithM where
  Z := Bool
  Ux := Bool
  Uy := Bool
  X := Bool
  M := Bool
  Y := Bool
  pz := fun z => if z = false then 3/5 else 2/5
  px := fun ux => if ux = false then 1/10 else 9/10
  py := fun _ => 1/2
  fX := fun z ux => Bool.xor z ux
  fM := fun x uy => if uy then true else x
  fY := fun m z _ux _uy => Bool.xor z m

/-! ### §7.3 `P(m|x)` 的表（`condM`） -/

theorem condM_ff : demo.condM false false = 1/2 := by
  unfold SetupWithM.condM demo
  simp only [Fintype.sum_bool]
  norm_num
theorem condM_ft : demo.condM false true = 1/2 := by
  unfold SetupWithM.condM demo
  simp only [Fintype.sum_bool]
  norm_num
theorem condM_tf : demo.condM true false = 0 := by
  unfold SetupWithM.condM demo
  simp only [Fintype.sum_bool]
  norm_num
theorem condM_tt : demo.condM true true = 1 := by
  unfold SetupWithM.condM demo
  simp only [Fintype.sum_bool]
  norm_num

/-! ### §7.4 `P(y|x,z,m)` 的表（`condYobs`）

⚠⚠ **第 5 块修正（`r290`）**：旧稿写 `condYobs x z m y = [z⊕m=y]`，**是错的**。
由 `condYobs := condYnum / condM`，当 `condM x m = 0`（即 `x=1, m=0`）时
Lean 的 `ℝ` 除法给出 `0/0 = 0`，故必须**先判分母**。
（旧票还有一个 `pz` 因子在分母里，已删除 —— 见 `condYobs` 定义处的注。） -/

/-- ⭐⭐⭐ **`P(y|x,z,m)` 的完整表**（**含 `condM = 0` 的约定分支**）。

`condYnum x z m y = [z⊕m=y]·condM x m`（因为 `fY` 不吃 `ux,uy`）⟹
* `condM x m ≠ 0`：`condYobs = [z⊕m=y]`（一个 `0/1` 核，`∑_y = 1`）；
* `condM x m = 0`（仅 `x=1,m=0`）：`condYobs = 0/0 = 0`（Lean 约定）。 -/
theorem condYobs_all (x z m y : Bool) :
    demo.condYobs x z m y
      = if demo.condM x m = 0 then 0
        else if Bool.xor z m = y then 1 else 0 := by
  unfold SetupWithM.condYobs SetupWithM.condYnum SetupWithM.condM demo
  cases x <;> cases z <;> cases m <;> cases y <;>
    first | (simp only [Fintype.sum_bool]; norm_num [Bool.xor])

/-- ⭐ **逐格的 `P(y|x,z,m)` 表**（`x = 0` 时四格全展开）。 -/
theorem condYobs_table :
    demo.condYobs false false false false = 1 ∧ demo.condYobs false false true true = 1 ∧
    demo.condYobs false true false true = 1 ∧ demo.condYobs false true true false = 1 ∧
    demo.condYobs false false false true = 0 ∧ demo.condYobs false false true false = 0 ∧
    demo.condYobs true false false false = 0 ∧ demo.condYobs true false true true = 1 := by
  simp only [condYobs_all, condM_ff, condM_ft, condM_tf, condM_tt]
  norm_num [Bool.xor]

/-! ### §7.5 ⭐⭐⭐⭐⭐ **数值表（机器验证）** -/

/-- ⭐⭐⭐ **`doLaw` 的数值**。

| `(x,y)` | `P(y\|do(x))` |
|---|---|
| `(0,0)` | **`1/2`** |
| `(0,1)` | **`1/2`** |
| `(1,0)` | **`2/5`** |
| `(1,1)` | **`3/5`** | -/
theorem demo_doLaw :
    demo.doLaw false false = 1/2 ∧ demo.doLaw false true = 1/2 ∧
    demo.doLaw true false = 2/5 ∧ demo.doLaw true true = 3/5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold SetupWithM.doLaw SetupWithM.condYdo demo
     simp only [Fintype.sum_bool]
     norm_num [Bool.xor])

/-- ⭐⭐⭐ **`{Z}` 调整律的数值 = `doLaw`**（**任务 5**）。 -/
theorem demo_adjustLaw :
    demo.adjustLaw false false = 1/2 ∧ demo.adjustLaw false true = 1/2 ∧
    demo.adjustLaw true false = 2/5 ∧ demo.adjustLaw true true = 3/5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold SetupWithM.adjustLaw SetupWithM.condYnum demo
     simp only [Fintype.sum_bool]
     norm_num [Bool.xor])

/-- ⭐⭐⭐ **`{M}` 调整律的数值**（**`x=1` 两格是错的**）。

| `(x,y)` | `∑_m (1/2)∑_z P(z)P(y,m\|x,z)` | 正确值（`do`） | 偏差 |
|---|---|---|---|
| **`(0,0)`** | **`1/4`** | **`1/2`** | `-1/4` ⚠ |
| **`(0,1)`** | **`1/4`** | **`1/2`** | `-1/4` ⚠ |
| **`(1,0)`** | **`1/5`** | **`2/5`** | `-1/5` ⚠ |
| **`(1,1)`** | **`3/10`** | **`3/5`** | `-3/10` ⚠ | -/
theorem demo_adjustLawM :
    demo.adjustLawM false false = 1/4 ∧ demo.adjustLawM false true = 1/4 ∧
    demo.adjustLawM true false = 1/5 ∧ demo.adjustLawM true true = 3/10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold SetupWithM.adjustLawM SetupWithM.condYnum demo Fintype.card
     simp only [Fintype.sum_bool, Finset.card_univ]
     norm_num [Bool.xor])

/-- ⭐⭐⭐⭐ **〔任务 4〕调整 `W = {M}` 时 `adjust ≠ do`**（**中介偏误**）。

**⭐⭐ 具体数值**：`x=1, y=0`：`adjustLawM = 1/5` 而 `doLaw = 2/5`（差 `1/5`）；
`x=1, y=1`：`3/10` 而 `3/5`（差 `3/10`）。**全部四格都偏**。 -/
theorem demo_M_naive_wrong :
    demo.adjustLawM true false ≠ demo.doLaw true false
      ∧ demo.adjustLawM true true ≠ demo.doLaw true true := by
  rw [demo_adjustLawM.2.2.1, demo_doLaw.2.2.1]
  constructor
  · norm_num
  · rw [demo_adjustLawM.2.2.2, demo_doLaw.2.2.2]; norm_num

/-- ⭐⭐⭐⭐ **〔任务 5〕调整 `W = {Z}` 时 `adjust = do`**（**正确**）。 -/
theorem demo_Z_correct (x y : Bool) :
    demo.adjustLaw x y = demo.doLaw x y := by
  cases x <;> cases y
  · exact demo_adjustLaw.1.trans demo_doLaw.1.symm
  · exact demo_adjustLaw.2.1.trans demo_doLaw.2.1.symm
  · exact demo_adjustLaw.2.2.1.trans demo_doLaw.2.2.1.symm
  · exact demo_adjustLaw.2.2.2.trans demo_doLaw.2.2.2.symm

/-- ⭐ **`margX` 的数值**（§7.2.6 的手算中间结果）。 -/
theorem margX_val (x : Bool) : demo.margX x = (if x = false then 21/50 else 29/50) := by
  unfold SetupWithM.margX SetupWithM.margXZ SetupWithM.margZ SetupWithM.condX demo
  cases x <;> (simp only [Fintype.sum_bool]; norm_num [Bool.xor])

/-- ⭐ **`obsLaw` 化为显式二重和 / `margX`**（消去 `condYobs` 的分母）。 -/
theorem obsLaw_num (x y : Bool) :
    demo.obsLaw x y
      = (∑ z, ∑ m, demo.condYobs x z m y * demo.margXZ x z * demo.condM x m)
        / demo.margX x := by
  unfold SetupWithM.obsLaw
  refine Eq.trans (Finset.sum_congr rfl fun z _ => (Finset.sum_div _ _ _).symm)
    (Finset.sum_div _ _ _).symm

/-- ⭐⭐⭐ **观测律 `P(y|x)`（被后门污染）**（§7.2.6）。

| `(x,y)` | `P(y\|x)` | `P(y\|do(x))` |
|---|---|---|
| `(0,0)` | `1/2` | `1/2` |
| `(0,1)` | `1/2` | `1/2` |
| **`(1,0)`** | **`2/29`** | **`2/5`** |
| **`(1,1)`** | **`27/29`** | **`3/5`** |

⭐ 手算：`P(X=0) = 3/5·1/10 + 2/5·9/10 = 21/50`；`P(Z=0|X=1) = (2/5·1/10)/(29/50) = 2/29`，
故 `P(y=0|x=1) = (27/29)·0 + (2/29)·1 = 2/29`（`m=0` 时 `y=z=0`；`m=1` 时 `y=1`）。 -/
theorem demo_obsLaw :
    demo.obsLaw false false = 1/2 ∧ demo.obsLaw false true = 1/2 ∧
    demo.obsLaw true false = 2/29 ∧ demo.obsLaw true true = 27/29 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [obsLaw_num, margX_val]
     unfold SetupWithM.condYobs SetupWithM.condYnum SetupWithM.condM
       SetupWithM.margXZ SetupWithM.margZ SetupWithM.condX demo
     simp only [Fintype.sum_bool]
     norm_num [Bool.xor])

/-- ⭐⭐ **混淆可见**：朴素条件化 `P(y|x)` **不等于** `P(y|do(x))`（`2/29 ≠ 2/5`）。 -/
theorem demo_obs_ne_do : demo.obsLaw true false ≠ demo.doLaw true false := by
  rw [demo_obsLaw.2.2.1, demo_doLaw.2.2.1]; norm_num

/-- ⭐⭐ **`demo` 满足 §6 主定理的全部前提**（逐条核对）。 -/
theorem demo_ZBlocks : demo.ZBlocks := by
  intro m z uy ux₁ ux₂
  rfl

theorem demo_PosZ : demo.PosZ := by
  intro z
  cases z <;> (unfold SetupWithM.margZ demo; norm_num)

/-- ⚠ **诚实披露**：`demo` **不满足** `PosM`（`P(m=0|x=1)=0`，见 `condM_tf`）。
故 `PosM` **不是**本载体主定理的前提 —— §6.1 只用 `condYdo = condYnum`。 -/
theorem demo_not_PosM : ¬ demo.PosM := by
  intro h
  have h0 : demo.condM true false = 0 := condM_tf
  exact h true false h0

theorem demo_px_sum : (∑ ux : Bool, demo.px ux) = 1 := by
  unfold demo
  simp only [Fintype.sum_bool]
  norm_num

/-- ⭐⭐⭐ **主定理在 `demo` 上的落地**（**不逐格枚举**，走 §6.1 的通用证明）。 -/
theorem demo_Z_correct_via_theorem (x y : Bool) :
    demo.adjustLaw x y = demo.doLaw x y :=
  SetupWithM.adjust_Z_correct demo x y

end Demo

/-! ===========================================================================
  §8 ⚠⚠ **`bad`：一个**违反 `ZBlocks`** 的 SCM —— 但它**不构成**反例**
  （**第 4 块诚实修正**，`r290`）
  ===========================================================================
  `bad` 与 `demo` **只差一处**：`fY m z ux _uy = z XOR m XOR ux`（**加上 `ux`**）。

  **手算**：`∑_ux px(ux)[fY = y]` 在 `ux` 上**不是常值** ⟹ **确实**违反 `ZBlocks`。

  **⚠⚠ 但它**不是**「`ZBlocks` 失效 ⟹ `{Z}` 调整算错」的反例。**
  原因是本载体的一条**结构恒等**（见 §3.3）：
  `condYdo ≡ condYnum`（**逐字相同**，两者都含因子 `[fM x uy = m]`），
  而 `adjustLaw = ∑_z pz ∑_m condYnum`、`doLaw = ∑_z pz ∑_m condYdo`
  ⟹ **对任意 `S` 都有 `adjustLaw ≡ doLaw`**。
  即使 `fY` 额外吃 `Ux`，`∑_m` 边缘化 `m` 时 `Ux` 也被 `px` 一并边缘化，
  误差被吸收。**⟹ `ZBlocks` 在本载体里是空前提。**
  详见 `bad_Z_equal` 的 docstring。
-/

namespace Bad

/-- ⚠ **反例 SCM**：`Y` **额外吃 `Ux`**（`X←Ux→Y` 未被 `Z` 阻断）。 -/
noncomputable def bad : SetupWithM where
  Z := Bool
  Ux := Bool
  Uy := Bool
  X := Bool
  M := Bool
  Y := Bool
  pz := fun z => if z = false then 3/5 else 2/5
  px := fun ux => if ux = false then 1/10 else 9/10
  py := fun _ => 1/2
  fX := fun z ux => Bool.xor z ux
  fM := fun x uy => if uy then true else x
  fY := fun m z ux _uy => Bool.xor (Bool.xor z m) ux

/-- ⚠ **`bad` 违反 `ZBlocks`**（`ux` 真的进 `Y`）。 -/
theorem bad_violates_ZBlocks : ¬ bad.ZBlocks := by
  intro h
  have h1 := h true false false true false
  unfold Bad.bad at h1
  simp [Bool.xor] at h1

/-- ⭐⭐⭐ **⚠⚠ 第 4 块数值修正：在 `bad` 上 `adjustLaw = doLaw`。

**⟹ `bad` **不能**作为「`ZBlocks` 失效 ⟹ `{Z}` 调整算错」的反例。**
旧稿的 `bad_Z_wrong : bad.adjustLaw true false ≠ bad.doLaw true false`
是**假命题**（两边都等于 `29/50`），**已删除**，改为本等式。

**为何必然相等**（与 `ZBlocks` 无关）：Lean 里
`adjustLaw = ∑_z pz ∑_m condYnum`、`doLaw = ∑_z pz ∑_m condYdo`，
而 `condYdo ≡ condYnum` 逐字相同（§3.3 的 `rfl`：两者都含因子 `[fM x uy = m]`，
且 `fY` 不吃 `X`）。故**对任意 `S`** 都有 `adjustLaw ≡ doLaw`。
让 `fY` 额外吃 `Ux`（`z⊕m⊕ux`）也无济于事：`∑_m` 边缘化 `m` 时 `Ux`
也被 `px` 一并边缘化，误差被吸收。

**机器实测**（`px(0)=1/10, px(1)=9/10`）：

| `(x,y)` | `doLaw` | `adjustLaw` |
|---|---|---|
| `(0,0)` | `1/2` | `1/2` |
| `(0,1)` | `1/2` | `1/2` |
| `(1,0)` | `29/50` | `29/50` |
| `(1,1)` | `21/50` | `21/50` |

**⚠ 后果**：`ZBlocks` 在本载体里是**空前提**（`adjust_Z_correct` 不需要它，
见该定理的「诚实边界」）。要真正检验 `ZBlocks`，`fY` 必须重新吃 `X`
（回到 `R259` 载体），超出本文件（中介载体）的范围。 -/
theorem bad_Z_equal :
    bad.adjustLaw true false = bad.doLaw true false := by
  unfold SetupWithM.adjustLaw SetupWithM.doLaw SetupWithM.condYnum SetupWithM.condYdo
  unfold Bad.bad
  simp [Bool.xor]

end Bad

/-! ===========================================================================
  §9 **数值核对（`evidence`）**：逐格的 `simp`/`norm_num` 复核表
  ===========================================================================

  ⚠ **D8 诚实标注**：本节每条定理都是**定点数值核对**
  （`unfold` + `Fintype.sum_bool` + `norm_num`），**不是**新数学。
  它们的作用是**复核** §7 的解析表，**不能**当作理论贡献计数。

  `evidence` 与 `demo` 是**同一 SCM**（字段值逐字相同），只是**再声明一次**
  以便把「SCM 定义」与「数值表」放在同一节里读。
-/

namespace Evidence

/-- ⭐ §9 的 SCM 就是 §7 的 `demo`（不重复声明，避免实例差异导致的 `rfl` 失败）。 -/
noncomputable abbrev evidence : SetupWithM := Demo.demo

/-- `evidence` 与 `demo` **定义上就是同一个对象**。 -/
theorem evidence_eq_demo : evidence = Demo.demo := rfl

/-- ⭐ ⭐⭐ **主表复核**：`do` / `{Z}` / `{M}` 三列 + 两格 `≠`。 -/
theorem main_table :
    evidence.doLaw false false = 1/2 ∧ evidence.doLaw true false = 2/5
    ∧ evidence.doLaw true true = 3/5
    ∧ evidence.adjustLaw true false = 2/5
    ∧ evidence.adjustLawM true false = 1/5
    ∧ evidence.adjustLawM true false ≠ evidence.doLaw true false
    ∧ evidence.adjustLaw true false = evidence.doLaw true false :=
  ⟨Demo.demo_doLaw.1, Demo.demo_doLaw.2.2.1, Demo.demo_doLaw.2.2.2,
   Demo.demo_adjustLaw.2.2.1, Demo.demo_adjustLawM.2.2.1,
   Demo.demo_M_naive_wrong.1, Demo.demo_Z_correct true false⟩

/-- ⭐ **`{M}` 的两格偏差值** `-1/5` 与 `-3/10`（`x=1`，`y=0,1`）。 -/
theorem biasM_value :
    evidence.biasM true false = -1/5 ∧ evidence.biasM true true = -3/10 := by
  unfold SetupWithM.biasM
  rw [Demo.demo_adjustLawM.2.2.1, Demo.demo_adjustLawM.2.2.2,
      Demo.demo_doLaw.2.2.1, Demo.demo_doLaw.2.2.2]
  constructor <;> norm_num

/-- ⭐ **`{Z}` 的两格偏差值** `0`。 -/
theorem biasZ_value :
    evidence.biasZ true false = 0 ∧ evidence.biasZ true true = 0 := by
  unfold SetupWithM.biasZ
  rw [Demo.demo_Z_correct true false, Demo.demo_Z_correct true true]
  exact ⟨by norm_num, by norm_num⟩

end Evidence

/-! ===========================================================================
  §10 ⚠⚠ **诚实说明（边界清单）**
  ===========================================================================

  ## 10.1 本文件**真的**证了什么

  | 项 | 定理 | D8 口径 |
  |---|---|---|
  | 1. `M` 是 `X` 的后代 | `M_is_descendant` / `M_in_descendant` | 定义展开（构造一条边） |
  | 2. `Y` 是 `X` 的后代（**经 `M`**） | `Y_is_descendant` | 构造（`trans`） |
  | 3. ⭐ `NoOutcome {M}` 真、`NoDescendant {M}` 假 | `Pearl_ii_independent` | **真内容**（两个独立事实的合取，其中一个是否定） |
  | 3'. `X` 的后代 ⊆ `{X,M,Y}`（`Z`/`Ux`/`Uy` 都不是） | `descendant_cases` | 归纳（8 组逐条） |
  | 4. `{M}` 调整 ≠ `do` | `demo_M_naive_wrong` | 数值核对 |
  | 5. `{Z}` 调整 = `do` | `demo_Z_correct` / `demo_Z_correct_via_theorem` | 数值核对 + 通用定理 |
  | + `∑_ux p_x[Y][M=m] = P(m|x)·K` | `inner_eq` / `condYnum_factor` | **真内容**（换序 + 提公因子，~15 行） |
  | + `P(y|x,z,m) = P(y|do(x),z,m)/P(m|x)` | `condYobs_eq` | **真内容**（约分；分母**不含** `p(z)`） |
  | + `{Z}` 调整 = `do`（**不需要 `ZBlocks`**） | `adjust_Z_correct` | **结构恒等**（`condYdo ≡ condYnum`，逐点 `sum_congr`） |
  | 6. ⚠ **`ZBlocks` 在本载体内是空前提** | `bad_violates_ZBlocks` + `bad_Z_equal` | **否定性发现**（反例存在但不起作用） |

  ## 10.2 ⚠⚠ 本文件**没有**证、也不打算声称的

  1. **「(ii) 失败 ⟹ 调整公式必错」的一般定理不存在于本文件。**
     §4.3 的图侧结论与 §7 的数值结论是**并置**的：
     前者由 `moralAdjM` 的**结构**决定（与 `pz/px/py/fX/fM/fY` 的具体值无关），
     后者由 `demo` 的**参数**决定。**我们没有把它们缝成一条定理**，
     因为**它不成立**：存在 `M` 是后代、但 `∑_m` 恰好等于 `do` 的参数
     （§7.2.5 的 `x=0` 两格就是这种巧合）。
  2. ⚠⚠ **`ZBlocks` 是空前提（本载体的一大缺陷，`r290` 诚实修正）。**
     §8 的 `bad` **确实**违反 `ZBlocks`，但它的 `adjustLaw` **仍**等于 `doLaw`
     （`bad_Z_equal`）。原因是**结构恒等**：`condYdo ≡ condYnum`（两者都含
     `[fM x uy = m]` 因子），故 `adjustLaw = ∑_z pz ∑_m condYnum = doLaw`
     **对任意 `S`** 成立，与 `ZBlocks` 无关。
     **⟹ 本文件无法演示「`ZBlocks` 失效 ⟹ `{Z}` 调整错」。**
     要演示它，`Y` 必须**直接**吃 `X`（回到 `R259` 载体），
     而那样中介 `M` 就失去独立性（§4 的动机）。**这是本设计的内在张力，
     不是遗漏。**
  3. **图侧与数值侧仍未接通**：本文件**没有** `BackdoorSepM`（d-分离版）的定义，
     故无法证「`{Z}` 阻断后门 ⟺ `ZBlocks`」。`R277` 对原载体做过这件事
     （`zb_backdoorSep`），本文件**未移植**。
  4. **`Z` 仍外生** ⟹ 「`Z` 是 `X` 的后代」（Pearl (ii) 对 `Z` 的那一半）不可表达。
  5. **`condYdo = condYnum`（`rfl`）** 说明在本载体里「`M` 上的后门」为空 ——
     中介载体把**所有**讯号放进了「`M` 的选择偏差」里。这是**载体设计**的代价，
     换来的正是 §4.3 的独立性。**⚠ 若有人把 `condYdo = condYnum` 当作
     「主定理是定义展开」的证据，那是误读：`P(y|x,z,m)` 与 `do` 的相等性
     仍需 §3.4 的**约分**（`condM` 被消掉）。**
  6. **只做有限离散。**

  ## 10.3 与 `NoDescendantWitness`（第 288 轮）的关系

  该文件的结论「`NoDescendant ⟺ NoOutcome`」**只对 `R259.BackdoorSetup` 成立**。
  本文件证明：**换载体（加 `M`）后该等价断裂**（§4.3）。
  **⚠ 但这不等于「Pearl (ii) 在原载体上是错的」** —— 原载体的结论是**正确的**，
  它只是说明**原载体的表达能力不足**。本文件是**补上表达能力**，不是**推翻**。
-/

end Fate.R289

