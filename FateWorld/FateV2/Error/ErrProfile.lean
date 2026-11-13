import FateWorld.FateV2.Modeling.SCM
import Mathlib.Tactic

/-!
  # Error · ErrProfile —— 指向 `ErrProfileN`

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F7-02（误差剖面）
  - 依赖裁决：**裁决 K**、**D-008**
  - 改动：本文件是**转发表**。实际内容在
          `Error/ErrProfileN.lean`（离散版）与 `Error/FitBoundary.lean`
          （B 类迁移的连续版，原样保留）。
  - 状态：已验证

  ## 为什么拆成转发

  `Error/FitBoundary.lean` 是 **B 类迁移**文件（来源 `Legacy/ProperFit-*/FitBoundary.lean`），
  它里面已经定义了 `FateV2.Error.Core.ErrProfileWeak` 与 `IsFitBoundary`。
  本批的 demo 用的是**离散**索引（`γ : Nat`），若把离散定义塞进同一个
  `namespace FateV2.Error`，会与 `open FateV2.Loop`（`OptimalFit.lean` 需要）
  产生命名冲突。

  ⟹ 离散版另立**独立命名空间** `FateV2.ErrorN`（`N` = Nat 索引），
  与 `FateV2.Error.Core` 平行，互不遮蔽。这不是"绕过"，而是把
  「连续版」与「离散版」显式分开——两者**并列**，不是一条链。

  ⚠ **降级**：没有证明「离散 → 连续」的嵌入，已登记进报告。
-/

namespace FateV2.Error

end FateV2.Error
