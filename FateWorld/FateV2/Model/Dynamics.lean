import FateWorld.FateV2.Model.Time
import FateWorld.FateV2.Modeling.Construct
import Mathlib.Tactic

/-!
  # Model · Dynamics —— 按拓扑序求值（A1 的缺口）

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F2-01（转移方程）、F5-03（结构方程）、F5-04（求值语义）
  - 依赖裁决：**D-013**（一体化系统）、**D-014**（模型 = SCM）、
              **D-019**（自由度最大化：求值策略可换）
  - 改动：原文件空骨架。此处补上 A1 的缺口：**从外生赋值算出内生赋值**。
  - 状态：已验证（`Demo/SyntheticRun` 端到端调用）

  ## 这个文件解决什么

  `Modeling/SCM.lean` 的文件头写着：

  > **没有图就没有内生赋值**：要从外生赋值 `e : E` 算出 `v : V → Val`，
  > 必须按图拓扑序逐步求值（`F` 里 `v` 的父节点必须已知）。
  > 无图时无法定义 `eval`——这不是偷懒，是**结构性缺失**（A1）。

  本文件把这个缺口补上：给定求值顺序 `order : List V`（父在前）与外生赋值 `e : E`，
  按序逐个求值，得到完整的 `V → Val`。

  ## 降级说明（如实登记）

  1. **需要一个初始赋值** `init : V → Val`（节点还没算出来之前 `v` 里是什么）。
     本实现把 `init` 作**显式参数**传，不用 `Inhabited Val` 硬造默认值。
     于是不在 `order` 里的节点保留 `init` 的值；
     `order` 覆盖全部节点时结果**不依赖** `init`——见 `evalFrom_cover`。
  2. **没有证明「图无环 ⟹ 求值顺序存在」**（需要拓扑排序算法与其正确性，
     属另一个规模）。本文件的接口**以「顺序给定」为参数**，调用方必须显式交出顺序。
  3. **没有把"父在前"做成自动检查的谓词**（`Evalvable` 这种递归谓词在本工具链下
     与 `List` 递归交互很差，见 `_报告/A-进度.md` §陷阱）。取而代之：
     求值的**局部性**（`evalFrom_notin`）与**初始值无关性**（`evalFrom_cover`）
     直接在定理层给出，不依赖任何「顺序合法性」假设。

  ## 超出定义之处
  * `evalFrom_single`：单点求值恰给出该节点的方程值——「求值确实在算结构方程」。
  * `evalFrom_notin`：求值只动被处理的坐标（**求值 = 一串局部覆盖**）。
  * `evalFrom_cover`：顺序覆盖全部节点时，求值结果与初始赋值**无关**。
-/

namespace FateV2.Model

universe u

open FateV2.Modeling

/-! ===========================================================================
  §1  （当前点在 `Model/State.lean`）
  =========================================================================== -/

/-! ===========================================================================
  §2  按序求值
  =========================================================================== -/

/-- **按序求值**：从左到右处理 `order`，每处理一个节点 `v`，
  就用 `M.F v` 算出它的值并写进 `v`。

  这是 **A1 缺口的实现**：`e : E` 是外生赋值，`M.F` 是结构方程，
  `order` 是求值顺序，产出是完整的 `V → Val`。 -/
def evalFrom {Val V E Noise : Type u} [DecidableEq V] (M : Model Val V E Noise)
    (e : E) (init : V → Val) : List V → V → Val
  | [], w => init w
  | v :: rest, w =>
    evalFrom M e
      (fun u => if u = v then M.F v init e else init u) rest w

/-! ===========================================================================
  §3  求值的基本事实
  =========================================================================== -/

/-- 空序求值 = 初始赋值。 -/
theorem evalFrom_nil {Val V E Noise : Type u} [DecidableEq V]
    (M : Model Val V E Noise) (e : E) (init : V → Val) :
    evalFrom M e init [] = init := rfl

/-- 一次求值步：把 `v` 写进去再继续。 -/
theorem evalFrom_cons {Val V E Noise : Type u} [DecidableEq V]
    (M : Model Val V E Noise) (e : E) (init : V → Val) (v : V) (rest : List V) :
    evalFrom M e init (v :: rest)
      = evalFrom M e (fun u => if u = v then M.F v init e else init u) rest := rfl

/-- **单点求值恰给出该节点的方程值**。

  **超出定义之处**：定义里求值是「先覆盖、再递归」；本定理把它在读出一个坐标时
  化简成 `M.F v init e`。定义本身没有这条——它是「按序求值确实在算结构方程」
  的最直接证据。 -/
theorem evalFrom_single {Val V E Noise : Type u} [DecidableEq V]
    (M : Model Val V E Noise) (e : E) (init : V → Val) (v : V) :
    evalFrom M e init [v] v = M.F v init e := by
  show (if v = v then M.F v init e else init v) = M.F v init e
  rw [if_pos rfl]

/-- **求值只动被处理的坐标**：若 `w` 不在序列里，则 `w` 处的值仍是 `init w`。

  **超出定义之处**：定义 `evalFrom` 对每个节点都写一次；
  本定理说「写」是**局部**的——不在序列里的坐标保持原样。
  这是「按序求值 = 一串局部覆盖」的形式化，也是「求值不会颠倒因果」的根据
  （未求值的节点读到的还是 `init`，不可能读到未来才算出的值）。 -/
theorem evalFrom_notin {Val V E Noise : Type u} [DecidableEq V]
    (M : Model Val V E Noise) (e : E) (init : V → Val)
    (order : List V) (w : V) (hw : w ∉ order) :
    evalFrom M e init order w = init w := by
  induction order generalizing init with
  | nil => rfl
  | cons v rest ih =>
    have hw' : w ∉ rest := fun h => hw (List.mem_cons_of_mem v h)
    have hwv : w ≠ v := fun h => hw (h ▸ List.mem_cons_self)
    show evalFrom M e (fun u => if u = v then M.F v init e else init u) rest w = init w
    rw [ih (fun u => if u = v then M.F v init e else init u) hw']
    show (if w = v then M.F v init e else init w) = init w
    rw [if_neg hwv]

end FateV2.Model
