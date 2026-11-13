import FateWorld.FateV2.Modeling.Construct

/-!
  # Model · State —— 内生赋值作为系统状态

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F1-01（状态载体）、F1-13（数据载体）、F5-02（内生赋值）
  - 依赖裁决：**D-013**（模型是一体化完整系统，状态不按模态拆）、
              **D-014**（模型 = SCM）、**D-023 D1**（`Val : V → Type` 的依赖类型要求
              ——见尾项，本批先用单一 `Val`）
  - 改动：原文件空骨架。此处落 `WholeState = V → Val`（即 `SCM.Model.Endo`），
          并给出单点覆盖（闭环回写作用到状态上的基本动作）。
  - 状态：已验证

  ## 超出定义之处
  * `update_comm`：两处**不同**节点的更新**可交换**——定义只是逐点覆盖，
    完全没有说顺序无关；本定理把这条顺序无关性证出来（它是「当前点」可以
    按任意顺序装配的根据）。
  * `update_other`：覆盖是**局部**的（别的坐标不动）。
  * `update_eq_self`：覆盖成原值则状态不变。

  ## 尾项
  D-023 D1 要求 `Val : V → Type`（依赖类型）。本批的 `WholeState` 用单一 `Val`：
  依赖类型版会让 `update` 的类型变成 `(w : V) → Val w`，
  **与 `SCM.Model` 的 `Val : Type` 字段不兼容**（要同时改只读区的 `SCM.lean`）。
  ⟹ 已登记为尾项，不在本批突破。
-/

namespace FateV2.Model

universe u

/-! ===========================================================================
  §1  当前点：内生赋值
  =========================================================================== -/

/-- **当前点状态** = 内生赋值 `V → Val`（D-013 的 `WholeState`）。

  与 `Modeling.SCM.Model.Endo` 是**同一个类型**——此处另给名字，
  是为了在 `Model/` 层说「这是状态」而不必每次提到 SCM。 -/
abbrev WholeState (Val : Type u) (V : Type u) : Type u := V → Val

namespace WholeState

variable {Val V : Type u}

/-- 读出当前点。 -/
def get (s : WholeState Val V) (v : V) : Val := s v

/-- **单点覆盖**：把 `v` 的值改成 `x`，其余不动。

  这是闭环回写（`Loop/WriteBack`）作用到状态上的基本动作。
  `[DecidableEq V]` 是**实现层**的需要（要判「是否同一个节点」），
  不是理论前提——状态本体的定义不需要它。 -/
def update [DecidableEq V] (s : WholeState Val V) (v : V) (x : Val) : WholeState Val V :=
  fun w => if w = v then x else s w

/-- 覆盖后 `v` 处恰是新值。 -/
theorem update_eq [DecidableEq V] (s : WholeState Val V) (v : V) (x : Val) :
    update s v x v = x := by
  show (if v = v then x else s v) = x
  rw [if_pos rfl]

/-- 覆盖 `v` 不影响**别的**节点。

  **超出定义之处**：定义里覆盖是「按坐标的 if」，本定理说的是
  「`w ≠ v` 处保持原值」——即覆盖是**局部**的，
  这正是回写可以只改一个机制而不动其余状态的根据。 -/
theorem update_other [DecidableEq V] (s : WholeState Val V) (v : V) (x : Val)
    (w : V) (h : w ≠ v) : update s v x w = s w := by
  show (if w = v then x else s w) = s w
  rw [if_neg h]

/-- **两处不同节点的更新可交换**（顺序无关）。

  **超出定义之处**：`update` 的定义是逐点覆盖，**完全没有**声明
  两个覆盖的先后无关；本定理把它证出来。没有这条，
  「同时回写多个机制」就只能是某种**约定顺序**，而不是良定义的运算。

  证明按坐标三分：`u = v` / `u = w` / 其余；每支都只用
  `update_eq`（同坐标取新值）与 `update_other`（异坐标保持）。 -/
theorem update_comm [DecidableEq V] (s : WholeState Val V)
    (v w : V) (x y : Val) (h : v ≠ w) :
    update (update s v x) w y = update (update s w y) v x := by
  funext u
  unfold update
  by_cases hvw : u = v
  · rw [if_pos hvw, if_pos hvw]
    rw [if_neg (fun hc => h (hvw.symm.trans hc))]
  · by_cases hww : u = w
    · rw [if_pos hww, if_pos hww]
      rw [if_neg hvw]
    · rw [if_neg hww, if_neg hvw, if_neg hvw, if_neg hww]

/-- 覆盖成原值则状态不变。 -/
theorem update_eq_self [DecidableEq V] (s : WholeState Val V) (v : V) :
    update s v (s v) = s := by
  funext u
  by_cases hu : u = v
  · subst hu; rw [update_eq]
  · rw [update_other _ _ _ _ hu]

end WholeState

/-- 下游可写 `State.update`（同一对象的别名）。 -/
abbrev State := WholeState

end FateV2.Model
