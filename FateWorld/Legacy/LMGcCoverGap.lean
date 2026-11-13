import FateWorld.Legacy.CardBalanceLMGc
import FateWorld.Legacy.LMGcCondIndepEquiv

/-! ===========================================================================
  §0  ⚠ `LMGc` 直接计算路线的**第二个障碍**：`nd v` 的 cover 条件不满足

  ## 已有工具（均正确）

  | 工具 | 内容 | 模块 |
  |---|---|---|
  | `mass_eq_of_reads_cover` | 若**所有**因子只读 `S`，则 `mass S p x = |α|^(|V|-|S|)·p x` | `MassOfReadsCover` |
  | `card_balance_lmgc` | `|{v}∪pa v| + |nd v| = |pa v| + |{v}∪nd v|` | `CardBalanceLMGc` |
  | `lmgc_iff` | `LMGc ⟺ ∀ v, CondIndep {v} (nd v) (pa v)` | `LMGcCondIndepEquiv` |

  ## 障碍

  `LMGc` 的四个 `mass` 及其 `S`：

  | 项 | `S` | 所有因子都只读 `S` 吗？ |
  |---|---|---|
  | `mass (insert v (pa v))` | `{v} ∪ pa v` | **✅**（由 `LocalTo` + `pa v ⊆ {v}∪pa v`）|
  | `mass (insert v (nd v ∪ pa v))` | `{v} ∪ nd v` | **✅**（由 `LocalTo` + `pa v ⊆ nd v`）|
  | `mass (pa v)` | `pa v` | **❌**（`ψ v` 读 `v`，而 `v ∉ pa v`）|
  | `mass (nd v ∪ pa v)` | `nd v` | **❌**（`ψ v` 读 `v`，而 `v ∉ nd v`）|

  **⟹ `mass_eq_of_reads_cover` 只能处理前两项。**

  后两项中 `ψ v` 不读 `S`，故不能直接化为 `|α|^k · p x`。

  ## 可能的出路

  后两项的 `S` 都是 `nd v` 的子集。`ψ v` 读 `{v} ∪ pa v`，其读集**落在 `{v} ∪ nd v` 内**
  （因 `pa v ⊆ nd v`），但**不在 `nd v` 内**。

  ⟹ 可以用 `mass_mul` 的一个变体：把 `ψ v` 从 `mass (nd v)` 中提出来，
     但需要 `ψ v` 在 `nd v`-纤维上常值，即 `ψ v` 只读 `nd v`——不成立。

  **⟹ 或者：先对 `{v} ∪ nd v` 做 `mass_self_insert` 得到 `|α|^(|V|-|{v}∪nd v|)·p x`，
     再用「`mass (nd v)` 与 `mass ({v} ∪ nd v)` 的关系」转换。**
     后者正是 `Fate/MassSdiffConst.lean` 的 `mass_sdiff_of_reads`（需 `g` 只读 `T\{s}`）。

  ## 诚实边界

  本文件只做障碍分析。`LMGc` 仍未证。
  =========================================================================== -/
