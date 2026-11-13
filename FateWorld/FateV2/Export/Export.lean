import FateWorld.FateV2.Export.Modality
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
  # Export · Export —— 默认全导出 + scope 限定

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F6-10（多模态导出）
  - 依赖裁决：**D-011**（模态 = 推导器）、**D-012**（默认导出全部；
              受限导出须标记）、**D-013**（模态是导出轴）
  - 改动：原文件空骨架。
  - 状态：已验证

  ## 名字

  导出函数取名 `exportModalities` 而不是 `export`：
  `export` 在 Lean 4 里是**关键字**（`export Foo (bar)`），不能当标识符。

  ## `exportModalities` 做什么

  ```
  exportModalities reg M scope = 逐条取注册表里 scope 允许的模态，算出它的值
  ```

  三条要点：

  1. **不设「有意义」判据**（D-012 §一.1）：只要注册了，就算、就导。
  2. **边界 = 注册表**（D-012 §一.3）：想多看一个模态就得**注册**它。
  3. **受限导出带标记**（D-012 代价 3）：结果里的 `scope` 就是标记。

  ## 超出定义之处
  * `filter_true_eq_self`：**恒真的过滤器不挡任何元素**。定义只是递归的 `if`；
    本定理把它在 `p ≡ true` 时化简掉，是 `export_all_count` 的支点。
  * `export_all_count`：默认范围下导出条数 = 注册表长度
    （「默认导出全部」（D-012 §一.1）的**计数形式**）。
  * `export_all_not_restricted`：默认导出不带「受限」标记
    （D-012 代价 3 的另一半）。
-/

namespace FateV2.Export

universe u

open FateV2.Modeling FateV2.Model

/-! ===========================================================================
  §1  导出
  =========================================================================== -/

/-- 取一个模态的值。 -/
def Modality.value {Val V E Noise : Type u} (m : Modality Val V E Noise)
    (M : Model Val V E Noise) : ModalityId × ExportVal := (m.id, m.project M)

/-- **导出**：默认导出注册表里**全部**模态；`scope` 可限定。 -/
def exportModalities {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (M : Model Val V E Noise) (sc : Scope) : ExportResult where
  items := (reg.filter (fun m => sc.admits m.id)).map (fun m => m.value M)
  scope := sc

/-- 导出到**默认范围**（全部）。 -/
def exportAll {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (M : Model Val V E Noise) : ExportResult :=
  exportModalities reg M Scope.all

/-! ===========================================================================
  §2  性质
  =========================================================================== -/

/-- **恒真的过滤器不挡任何元素**。

  **超出定义之处**：`List.filter` 的定义是逐元素的 `if`；本定理说明
  当谓词恒为 `true` 时它**是恒等**。这条不是定义展开——它需要归纳，
  且正是「默认导出全部」能从一句注释变成可检事实的支点。 -/
theorem filter_true_eq_self {α : Type u} (l : List α) (p : α → Bool)
    (h : ∀ x, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = true := h x
    show (x :: xs).filter p = x :: xs
    rw [List.filter_cons, hx, if_pos rfl, ih]

/-- **默认范围下，导出条数 = 注册表长度**。

  **超出定义之处**：这是「默认导出全部」（D-012 §一.1）的**计数形式**——
  `exportModalities` 的定义含一个 `filter`，本定理说明当范围是 `all` 时
  这个 `filter` **一条都不挡**，于是条数恰好等于注册了多少个模态。
  没有这条，「默认导出全部」就只是一句注释。 -/
theorem export_all_count {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (M : Model Val V E Noise) :
    (exportAll reg M).count = reg.length := by
  have h : reg.filter (fun m => Scope.all.admits m.id) = reg := by
    apply filter_true_eq_self
    intro m
    exact Scope.admits_all m.id
  show (List.map (fun m => m.value M)
      (reg.filter (fun m => Scope.all.admits m.id))).length = reg.length
  rw [h, List.length_map]

/-- **默认导出不带「受限」标记**。

  D-012 代价 3：只有用 `scope` 限定过，才能/才需要标记为受限；
  默认导出**可以**声称「这是完整模型」。 -/
theorem export_all_not_restricted {Val V E Noise : Type u}
    (reg : Registry Val V E Noise) (M : Model Val V E Noise) :
    (exportAll reg M).restricted = false := rfl

end FateV2.Export
