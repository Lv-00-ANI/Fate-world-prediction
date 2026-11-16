import FateWorld.FateV2.Error.ErrorBound

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ScoreBound.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 15 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Modeling
/-
# `ScoreBound.lean` — 把 `s` 绑定到打分器 `linScore w x`（如实登记）

## (a) `margin` 的定义

`FateV2.Error/ErrorBound.lean:170`（命名空间 `FateV2.Error.R250ErrorBound`）：

```
def margin {ι : Type*} [Fintype ι] (w x : ι → ℝ) : ℝ := |linScore w x|
```

`linScore` 的定义（`FateV2.Error/ErrorBound.lean:151`）：

```
def linScore {ι : Type*} [Fintype ι] (w x : ι → ℝ) : ℝ := ∑ i, w i * x i
```

⟹ **`margin w x` 就是 `|linScore w x|`**（定义相等，`rfl`）。

## (b) `:239` 的 `s` 是自由的（未绑定）

`FateV2.Error/ErrorBound.lean:239`：

```
theorem error_bound_gives_correct_classification_margin {s δ ε : ℝ}
    (hδ : |δ| ≤ ε) (h2 : 2 * ε < |s|) :
    ∃ σ : ℤ, σ ≠ 0 ∧ sgn (s + δ) = σ ∧ sgn s = σ
```

`s : ℝ` 是**自由参数**，`|s|` 是一个自由实数。`:236` 附近的文档只说
「$s = \langle w,x\rangle$ 时它就是分类器版」，但那**只是注释**，没有绑定。

## (c) 本定理做到了什么

本文件的唯一交付物把 `s` 实例化为 `linScore w x`，
从而前件中的 `|s|` 变成 `|linScore w x| = margin w x`（由 `w`、`x` 算出）。
即：`|s|` 从自由实数变成 `margin w x`。

## (d) 诚实：这【不算】前件减少

按裁决 2=(甲)：`s : ℝ` → `w x : ι → ℝ` 是 **1 换 2**（参数个数反而增加）。
所以**不声称前件减少**；价值仅在于 `|s|` 现在可由 `w`、`x` 算出。

## (e) 不声称「消除了所有自由参数」

`δ`、`ε` 仍是自由实数参数，`w`、`x` 本身也是自由输入。
本文件**不**声称「消除了所有自由参数」，只声称「`s` 已绑定到 `linScore w x`」。

## 内容

| # | 定理 | 说明 |
|---|------|------|
| 1 | `error_bound_gives_correct_classification_linScore` | `:239` 的直接实例化，`s := linScore w x`，`|s| = margin w x` |

本文件不含任何占位符（三个占位常量名均未出现）。
-/

namespace FateV2.Error
namespace ScoreBound

open FateV2.Error.R250ErrorBound

/-! ## 绑定定理 -/

/-- **【`s` 绑定到打分器：`|s|` 不再是自由参数】**

`ErrorBound.lean:239` 的 `error_bound_gives_correct_classification_margin`
以 `{s δ ε : ℝ}` 为参数，`s` 是自由的。本定理把 `s` 绑到 `linScore w x`，
从而 `|s| = margin w x`（由 `margin` 的定义 `|linScore w x|`）。

前件变化：
- 原：`s : ℝ`（自由）+ `h2 : 2 * ε < |s|`
- 新：`w x : ι → ℝ` + `h2 : 2 * ε < margin w x`

⚠ 按裁决 2=(甲)，这**不算**前件减少（`s` → `w`+`x` 是 1 换 2）；
它的价值是 `|s|` 变成 `margin w x`，可以从 `w`/`x` 算出。 -/
theorem error_bound_gives_correct_classification_linScore
    {ι : Type*} [Fintype ι] (w x : ι → ℝ) {δ ε : ℝ}
    (hδ : |δ| ≤ ε) (h2 : 2 * ε < FateV2.Error.R250ErrorBound.margin w x) :
    ∃ σ : ℤ, σ ≠ 0
      ∧ FateV2.Error.R250ErrorBound.sgn (FateV2.Error.R250ErrorBound.linScore w x + δ) = σ
      ∧ FateV2.Error.R250ErrorBound.sgn (FateV2.Error.R250ErrorBound.linScore w x) = σ := by
  -- `margin w x = |linScore w x|` 是定义相等，因此 `h2` 可直接喂给 `:239`。
  exact FateV2.Error.R250ErrorBound.error_bound_gives_correct_classification_margin
    (s := FateV2.Error.R250ErrorBound.linScore w x) hδ h2

end ScoreBound
end FateV2.Error
