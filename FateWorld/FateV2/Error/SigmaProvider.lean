import FateWorld.FateV2.Error.SigmaFromDomain
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/SigmaProvider.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 3 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Loop

/-
  σ 解析器的接口契约（对应论文 §10）

  给出 resolveSigma 的非负性：对任意来源、任意误差剖面、任意默认分辨率均成立。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  来源：该结论原与其它 σ 相关结果同置于一个聚合模块中，而那个模块又引入了世界模型
  一系（约百个模块），与本结论无关。故此处单列一条：陈述与证明体逐字相同，均直接调用
  SigmaFromDomain.resolveSigma_nonneg。

  注：本结论内容很薄（只是把接口契约在三个来源上逐点检查一遍），不构成新数学。
     本模块仅被「σ 的数值依赖」模块使用。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error

namespace SigmaDataDependence

/-- **`resolveSigma` 对任意来源、任意剖面、任意 `g0` 均非负。**

    provenance：与 `SigmaUnified.resolveSigma_provider_nonneg` 相同
    （同一陈述、同一证明体，均直接调用 `SigmaFromDomain.resolveSigma_nonneg`）。 -/
theorem resolveSigma_provider_nonneg
    (src : SigmaFromDomain.SigmaSource) (W : Core.ErrProfileWeak) (g0 : ℝ) :
    0 ≤ SigmaFromDomain.resolveSigma src W g0 :=
  SigmaFromDomain.resolveSigma_nonneg src W g0

end SigmaDataDependence

end FateV2.Error
