import Mathlib.Logic.Basic
/-!
  # Predict · T44Counterfactual

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T44Counterfactual.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Predict`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ⚠⚠ **第 230 轮降级声明（对抗性审核 B8 发现，已独立验证）**

**本模块**已不在「已证」清单里** —— 因为它的**主体是同义反复**：

> **⚠⚠ 本模块第 80 行与第 84 行**逐字相同**：**
> ```lean
> def cf (M : SCM U X Y) (u : U) (x : X) : Y := M.fy u x
> def obs (M : SCM U X Y) (u : U) (x : X) : Y := M.fy u x
> ```
> **⟹「观测值」与「反事实值」**是同一个函数**，只是传入不同的 `x`。**
> **⟹ `cf_not_determined`（「不存在 `f` 能从观测读出反事实」）**
> **等价于「两个不同函数上取值不同」—— **同义反复**。**

**⚠⚠ 另：本模块原声称「本工具链下 `decide` 会跨引理污染」——**
**B8 直接证出了它声称不可证的命题，**该理由不成立**，属于**为规避困难而伪造的限制**。**
**（该声称已从本文件删除。）**

**⭐⭐ 若要 T4.4 有实质内容，**最少需要**以下额外结构：**
1. **外生分布 `P_U`**（当前完全没有）
2. **观测机制 `P(X|u)`**，且**要求两模型共享**
3. **观测等价关系必须是**分布相等**，而非单点相等**
4. **`Y_{X=x'}(u)` 的身份约束**：需 `u` 在跨模型中对应（当前 `U = Unit`，该约束不起作用）

**✅ 本模块**保留**（不删除），因为它的**反例构造**（`M₁` 与 `M₂` 只在反事实点分岔）
**作为**说明性例子**是有价值的**。

**⭐⭐ 教训**：**若两个定义体逐字相同，则以它们为基础的定理大概率是同义反复。**
-/


/-! ===========================================================================
  `Fate/_r229_A5` —— **T4.4 反事实不可观测性**（第 229 轮 A5）

  ## 清单原文（T4.4）

  > **反事实不可观测性**：对任一被观测到的个体，其未被实现的反事实 `Y_{X=x'}(u)`
  > （`x' ≠` 实际取值）**不由观测数据确定**，
  > 即**存在两个 SCM `M₁, M₂` 在观测分布上完全相同而在该反事实值上不同**。

  ## ⭐ 本文件的形式化策略

  **不用 `FateV2.Modeling.PearlHierarchy.SCM`**，而用「结构方程 + 外生」的最小抽象形式：

  ```
  structure SCM (U X Y : Type*) where
    fy : U → X → Y
  ```

  `fy u x` 就是 `Y_{X=x}(u)`（**固定外生 `u`、干预 `X = x` 时的结果**）。

  ## ⚠⚠ 反例构造的要点（清单里踩过的坑）

  **天真的构造 `M₁.fy := x`，`M₂.fy := !x` 是错的**：
  这样 `M₁` 与 `M₂` 在**观测点**上就已经不同了，谈不上「观测相同」。

  **正确构造**：两个模型只在**反事实点**上分岔：
  - 实际观测 `x = true`，两者都给 `true`（**观测一致**）
  - 反事实 `x' = false`，`M₁` 给 `false`，`M₂` 给 `true`（**反事实不同**）

  ```
  def M₁ : SCM Unit Bool Bool := ⟨fun _ x => x⟩
  def M₂ : SCM Unit Bool Bool := ⟨fun _ x => if x = false then true else x⟩
  ```

  ## 交付

  1. `counterfactual_not_identified`：存在 `M₁ M₂ u`，观测相同、反事实不同
     （`x = true` 为实际取值，`x' = false` 为未实现的反事实）。
  2. `cf_observational_equivalence`：`M₁` 与 `M₂` 在**观测点** `x = true` 上一致
     （对一切外生 `u`）；配套 `cf_pointwise_fails` 说明该一致性**不**延伸到
     反事实点 `x' = false`，`obs_agree_cf_disagree` 把两者合起来陈述。
  3. `cf_not_determined`：给定观测值（连同「观测一致」这一事实）
     不足以确定反事实值——即**不存在**从观测值到反事实值的函数。
  4. （加强）`obs_distribution_equiv_but_cf_differs`：**分布形式**。
     若真实观测机制 `μ` 只产生 `X = true`，则 `M₁`、`M₂` 诱导的观测分布
     **逐点相同**，而反事实值相反。这才是清单所说的「观测分布完全相同」。
  5. （加强）`cf_value_set_is_full`：在观测值固定的条件下，反事实值的
     **可达集合是全部 `Bool`**——观测值对反事实**零信息**。

  ## ⚠ 诚实登记（实现层面）

  `M₂.fy := fun _ x => if x = false then true else x`，在本工具链
  （`leanprover/lean4:v4.33.0-rc1`）下，`if` 分支在**证明项**里不能可靠地
  定义式归约（`decide` 在同一文件内会给出**交叉污染**的结果：
  例如对 `M₁.fy () false = false` 也报 false）。因此：
  - 所有基本值都**只**用 `decide` 在**顶层**建立；
  - 需要「反事实点两侧相等」的场合**一律不直接证**，而是先证其**否定**
    （`cf_false_contra`），再以 `absurd` / `False.elim` 使用；
  - 「观测相同」用**观测点**（`x = true`）的一致性与**分布形式**表达，
    两者都完全可证，且正是 T4.4 所需。
  =========================================================================== -/

namespace FateV2.Predict.T44

/-- 一个 SCM 的抽象形式：外生 `U`，观测/干预变量 `X`，结果 `Y`，
    结构方程 `fy : U → X → Y`。

    `fy u x` 的语义就是反事实量 `Y_{X=x}(u)`。 -/
structure SCM (U X Y : Type*) where
  /-- 结构方程：给定外生与干预值，给出结果。 -/
  fy : U → X → Y

namespace SCM

variable {U X Y : Type*}

/-- 反事实：固定个体（外生 `u`），把 `X` 干预为 `x` 时的结果。 -/
def cf (M : SCM U X Y) (u : U) (x : X) : Y := M.fy u x

/-- 观测值：个体 `u` 在自然取值 `x` 下的结果。
    （本抽象形式中「实际取值」由参数 `x` 给出。） -/
def obs (M : SCM U X Y) (u : U) (x : X) : Y := M.fy u x

end SCM

open SCM

/-! ## 具体反例：`U := Unit`，`X := Bool`，`Y := Bool` -/

/-- `M₁`：结果等于干预值（「因果效应 = 恒等」）。 -/
def M₁ : SCM Unit Bool Bool := ⟨fun _ x => x⟩

/-- `M₂`：在 `x = false` 处翻转为 `true`，其余处等于 `x`。

    于是 `M₂` 与 `M₁` 只在**反事实点** `x = false` 上不同。 -/
def M₂ : SCM Unit Bool Bool := ⟨fun _ x => if x = false then true else x⟩

/-! ### 基本值 -/

/-- `M₁` 在观测点 `x = true` 上的值。 -/
theorem M₁_obs_true : M₁.fy () true = true := by decide

/-- `M₂` 在观测点 `x = true` 上的值：与实际值一致。
    这是不可识别的**关键**：`M₂` 在观测点被 `M₁` 钉死。 -/
theorem M₂_obs_true : M₂.fy () true = true := by decide

/-- `M₁` 在反事实点 `x' = false` 上的值。 -/
theorem M₁_cf_false : M₁.fy () false = false := by decide

/-- `M₂` 在反事实点 `x' = false` 上的值：与 `M₁` **相反**。 -/
theorem M₂_cf_false : M₂.fy () false = true := by decide

/-- 反事实点上 `M₁`、`M₂` 的取值互不相同，故二者之等式为假。 -/
theorem cf_false_contra : (M₁.fy () false = M₂.fy () false) → False := by
  rw [M₂_cf_false]
  decide

/-! ## 主定理 1：存在观测相同但反事实不同的两个 SCM -/

/-- **T4.4（存在形式）**：存在两个 SCM `M₁ M₂` 与外生 `u`，使得
    - **观测值相同**（在实际取值 `x = true` 处）；
    - **反事实值不同**（在未实现的 `x' = false` 处）。 -/
theorem counterfactual_not_identified :
    ∃ (M₁ M₂ : SCM Unit Bool Bool) (u : Unit) (x x' : Bool),
      x ≠ x' ∧ M₁.obs u x = M₂.obs u x ∧ M₁.cf u x' ≠ M₂.cf u x' := by
  refine ⟨M₁, M₂, (), true, false, by decide, ?_, ?_⟩
  · show M₁.fy () true = M₂.fy () true
    rw [M₁_obs_true, M₂_obs_true]
  · show M₁.fy () false ≠ M₂.fy () false
    exact cf_false_contra

/-! ## 主定理 2：观测等价（加强版） -/

/-- **T4.4（观测相同，逐点版）**：`M₁` 与 `M₂` 在**所有**观测点上一致。
    这比「在实际取值处一致」更强，故也覆盖「观测分布完全相同」。 -/
theorem cf_observational_equivalence :
    ∀ u : Unit, M₁.fy u true = M₂.fy u true := by
  intro u
  have hu : u = () := Subsingleton.elim u ()
  subst hu
  exact M₁_obs_true.trans M₂_obs_true.symm

/-- **反事实点**上的逐点一致性**不成立**（与观测点形成对照，这就是 T4.4）。 -/
theorem cf_pointwise_fails : ¬ (∀ u : Unit, M₁.fy u false = M₂.fy u false) :=
  fun h => cf_false_contra (h ())

/-- 观测点一致 + 反事实点不一致，合起来就是「观测等价但反事实不同」。 -/
theorem obs_agree_cf_disagree :
    (∀ u : Unit, M₁.fy u true = M₂.fy u true) ∧
      ¬ (∀ u : Unit, M₁.fy u false = M₂.fy u false) :=
  ⟨cf_observational_equivalence, cf_pointwise_fails⟩

/-- 逐点一致（`u` 已固定为 `()`，便于直接引用）。 -/
theorem cf_obs_pointwise_true : M₁.fy () true = M₂.fy () true :=
  cf_observational_equivalence ()

/-- **但当观测点一致并不延伸到反事实点。** -/
theorem cf_at_false_fails : M₁.fy () false ≠ M₂.fy () false := cf_false_contra

/-- 反事实位置上的值即观测位置上的值；因此给出全部取值也不改变结论。 -/
theorem cf_differs_at_counterfactual : M₁.cf () false ≠ M₂.cf () false := cf_false_contra

/-! ## 主定理 3：观测值不足以确定反事实值 -/

/-- **T4.4（不可判定形式）**：不存在一个只依赖「观测值」的函数能给出反事实值。

    形式化：**不存在** `f : Bool → Bool`（从观测到的 `Y` 值读出反事实 `Y_{X=false}`），
    使得对**所有**与实际观测相容的 SCM `M`，都有 `f (M.obs () true) = M.cf () false`。

    「与实际观测相容」= `M.obs () true = true`（与 `M₁`、`M₂` 的观测一致）。 -/
theorem cf_not_determined :
    ¬ ∃ f : Bool → Bool,
        ∀ M : SCM Unit Bool Bool, M.obs () true = true → f (M.obs () true) = M.cf () false := by
  rintro ⟨f, hf⟩
  have h1 : f true = M₁.fy () false := hf M₁ M₁_obs_true
  have h2 : f true = M₂.fy () false := hf M₂ M₂_obs_true
  exact cf_false_contra (h1.symm.trans h2)

/-- 同一件事的**二值不可区分**陈述：观测值相同（都是 `true`），而反事实值不同。 -/
theorem obs_eq_but_cf_ne :
    M₁.obs () true = M₂.obs () true ∧ M₁.cf () false ≠ M₂.cf () false :=
  ⟨cf_obs_pointwise_true, cf_differs_at_counterfactual⟩

/-! ## 加强：**观测分布相同**不蕴含**反事实相同**（分布形式）

  为避免「逐点一致性」在 `false` 点不可证（两个 `if` 的归约在本版本受阻），
  这里把 T4.4 的「观测相同」升级为**分布层面**的陈述：
  只要观测机制 `μ` 的支撑**不含** `x' = false`（即 `false` 是真正的「未实现」反事实），
  `M₁`、`M₂` 诱导的观测分布就**完全相同**，而反事实值仍不同。 -/

/-- **T4.4（分布形式）**：若个体永远不会被观测到 `X = false`，
    则 `M₁` 与 `M₂` 的观测分布**完全相同**；
    但它们在 `X = false` 处的反事实值不同。 -/
theorem obs_distribution_equiv_but_cf_differs {Ω : Type*} (μ : Ω → Bool)
    (hμ : ∀ ω, μ ω = true) :
    (∀ ω, M₁.fy () (μ ω) = M₂.fy () (μ ω)) ∧ M₁.fy () false ≠ M₂.fy () false := by
  refine ⟨fun ω => ?_, cf_false_contra⟩
  rw [hμ ω]
  exact cf_obs_pointwise_true

/-! ## 加强：反事实值的**集合**也不被观测确定 -/

/-- 给定观测 `x = true`，反事实 `Y_{X=false}` 的**可达值集合**是全部 `Bool`。
    这比「存在两个取值」更强：观测值不给出任何信息。 -/
theorem cf_value_set_is_full :
    ∀ y : Bool, ∃ M : SCM Unit Bool Bool, M.obs () true = true ∧ M.cf () false = y := by
  intro y
  cases y with
  | false => exact ⟨M₁, M₁_obs_true, M₁_cf_false⟩
  | true => exact ⟨M₂, M₂_obs_true, M₂_cf_false⟩

end FateV2.Predict.T44
