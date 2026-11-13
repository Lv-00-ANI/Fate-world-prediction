import FateWorld.FateV2.Classical.Assumptions
import Mathlib.MeasureTheory.Measure.Map

/-!
  # Modeling · 模型 = SCM

  ## 迁移登记
  - 来源：新写（参考 `命运-素材-原始文件-不可更改/Fate/SCMGraph.lean`、
          `SCMSemantics.lean`、`ParamSCM.lean`）
  - 动作：C 重写
  - 对应环节：F5-01（SCM 结构）、F5-03（结构方程）、F5-07（外生律）、
              F2-01（转移方程）、F2-12（随机转移核）
  - 依赖裁决：**D-013**（一体化完整系统）、**D-014**（模型 = SCM）、
              **D-016**（三条公理入账本）、**D-019**（自由度最大化）
  - 改动：旧代码把 SCM 与「图」「语义」「可辨识性」混在一个文件里，且写死 `V = Fin n`。
          此处只保留最小骨架：**结构方程族 + 外生律 + 可选图**。
  - 状态：已编译未验证

  ## 口径约定（重要）

  外生侧统一用**赋值类型 `E`**，不用「外生变量下标集 `U` + `U → Val`」：

  | 概念 | 类型 |
  |---|---|
  | 外生赋值 | `E`（一次噪声实现就是一个 `E` 的元素） |
  | 外生律 | `Noise`（默认实例 `Measure E`） |

  这样 `P_U : Measure E` 与 `F` 取的 `E` 是**同一个东西**，
  不会出现「测度在 `U` 上、函数吃 `U → Val`」的错位。

  ## 三件事被显式分开

  | 概念 | 类型 | 是否必需 |
  |---|---|---|
  | 结构方程族 | `F : V → (V → Val) → E → Val` | ✅ 必需 |
  | 外生律 | `P_U : Noise` | ✅ 必需（`Noise` 参数化） |
  | 图 | `Option (Graph V)` | ⬜ **可选** |

  **为什么图可选**：`D-014` 尾#3 与架构未定项 A1——「图从哪来」还没定。
  设成 `Option` 之后，不需要图的部分现在就能用；
  需要图的部分（求值、d-分离、可辨识性）显式依赖 `HasGraph`。

  ## 一个必须点破的依赖

  **没有图就没有内生赋值**：要从外生赋值 `e : E` 算出内生赋值 `v : V → Val`，
  必须按图拓扑序逐步求值（`F` 里 `v` 的父节点必须已知）。
  无图时无法定义 `eval`——这不是偷懒，是**结构性缺失**（A1）。

  因此 `Model.eval` **不在本文件**；`induce` 把 `eval` 作为参数收进来，
  于是「噪声尺度」的接口先立起来，等 A1 定了再填实现。
-/

namespace FateV2.Modeling

universe u

open MeasureTheory

/-! ## 图（可选） -/

/-- **图**：每个节点的父节点列表。

    无环性暂不作字段——它属于 A1 的另一半，且作为 `Prop` 字段会强迫
    所有构造都携带证明。先留接口。 -/
structure Graph (V : Type u) where
  /-- 父节点 -/
  pa : V → List V

/-! ## 模型 = SCM -/

/-- **结构因果模型（SCM）**，也就是 `D-014` 的 `Model`。

    四个参数全部开放（D-019）：

    * `Val`   —— 取值类型（`ℝ`、`Bool`、任意）
    * `V`     —— 内生变量集
    * `E`     —— 外生赋值类型（一次噪声实现）
    * `Noise` —— 外生律的载体（默认 `Measure E`，见 `ModelOnMeasure`）

    不写死 `V = Fin n`，不写死 `Val = ℝ`，不写死 `Noise = Measure E`。 -/
structure Model (Val : Type u) (V : Type u) (E : Type u) (Noise : Type u) where
  /-- 结构方程族：给定内生赋值与外生赋值，算出某个内生变量的值 -/
  F   : V → (V → Val) → E → Val
  /-- 外生律（= 噪声结构，D-014） -/
  P_U : Noise
  /-- 图（可选，A1 未定） -/
  graph : Option (Graph V)

namespace Model

variable {Val V E Noise : Type u}

/-- **内生赋值** = 系统状态（D-013 的 `WholeState`）。 -/
abbrev Endo (Val : Type u) (V : Type u) : Type u := V → Val

/-- 有图吗？需要图的功能必须显式检查这一条。 -/
def HasGraph (M : Model Val V E Noise) : Prop := M.graph.isSome

/-- 把模型推成某模态上的分布。

    * `eval`    —— 外生赋值 → 内生赋值（**需要图**，见文件头）
    * `project` —— 内生赋值 → 某模态的值（D-013 的投影）
    * `push`    —— 把外生律推前（`Noise` 是什么，就怎么推） -/
def induce {Z : Type u}
    (M : Model Val V E Noise)
    (eval : E → Endo Val V)
    (project : Endo Val V → Z)
    (push : Noise → (E → Z) → Noise) : Noise :=
  push M.P_U (fun e => project (eval e))

/-- **σ_model 的接口**：推前之后再取离散度（D-014 的 `induce` + `spread`）。

    `spread` 是参数（D-019）：方差 / 分位数 / Wasserstein 半径都可。
    具体选哪种属实现细节（D-015 策略③）。 -/
def sigmaModel {Z : Type u}
    (M : Model Val V E Noise)
    (eval : E → Endo Val V)
    (project : Endo Val V → Z)
    (push : Noise → (E → Z) → Noise)
    (spread : Noise → ℝ) : ℝ :=
  spread (M.induce eval project push)

end Model

/-! ## 默认实例：外生律 = 测度

  这是 `D-014` 原本写的 `P_U : Measure U`。作为**一个实例**放在这里，
  而不是 `Model` 的硬编码字段（D-019）。 -/

/-- 外生律取测度时的模型。 -/
abbrev ModelOnMeasure (Val : Type u) (V : Type u) (E : Type u) [MeasurableSpace E] : Type u :=
  Model Val V E (Measure E)

namespace ModelOnMeasure

variable {Val V E : Type u} [MeasurableSpace E]

/-- 测度版的推前：`Measure.map`（`noncomputable`：测度推前本身不可计算）。 -/
noncomputable def pushMap {Z : Type u} [MeasurableSpace Z]
    (M : ModelOnMeasure Val V E) (f : E → Z) : Measure Z :=
  Measure.map f M.P_U

/-- 推前恒等映射不变。 -/
theorem pushMap_id (M : ModelOnMeasure Val V E) : M.pushMap (Z := E) id = M.P_U := by
  unfold pushMap
  exact Measure.map_id

end ModelOnMeasure

end FateV2.Modeling
