import FateWorld.Legacy.BarSdiffEq
import FateWorld.Legacy.MassSdiffConst

/-! ===========================================================================
  §0  `sink_peel` 的**最终判决**：不是「补因子/加前提」能修的

  ## 六步诊断链（本会话完整）

  1. **机检反例**（`Fate/SinkPeelCounterexample.lean`）：
     `V = Fin 1`、`α = Bool`、`f ≡ 1`、`T = {0}`、`s = 0` ⟹ 左 1 ≠ 右 2
  2. **完整诊断**（`Fate/SinkPeelDiagnosis.lean`）：缺 `|α|` 因子
  3. **`mass (T\\{s}) = |α| · mass T`**（`Fate/MassSdiffConst.lean`，
     假设 `g` 只依赖 `T\\{s}`）
  4. **补集分解** `univ\\(T\\{s}) = {s} ∪ (univ\\T)`（`Fate/SdiffEraseEq.lean`）
  5. **被积函数分解** `∏_{v ∉ T\\{s}} f v = f_s · ∏_{v ∉ T} f v`（`Fate/BarSdiffEq.lean`）
  6. **最终判决**（本文件）

  ## 最终判决：方向相反，无法用现有工具修

  `mass T g x` 的两个极端行为：

  | `g` 的属性 | 结果 |
  |---|---|
  | **只依赖 `T` 内坐标** | **`g w = g x`，故 `mass T g x = \\|α\\|^(\\|V\\|-\\|T\\|) · g x`** |
  | **只依赖 `T` 的补集** | **`g w` 在纤维内自由变化，**不能**提出** |

  `sink_peel` 里的 `f_s · tail_f T`：
  * `tail f T = ∏_{v ∉ T} f v` ⟹ 依赖 `univ \\ T`
  * `f_s` 依赖 `s`
  * 合起来依赖 `{s} ∪ (univ \\ T) = univ \\ (T \\ {s})`，
    即 `T\\{s}` 的**补集**

  **⟹ 与 `mass_sdiff_of_reads` 的假设（只依赖 `T\\{s}`）方向相反，不能套用。**

  ## 结论

  `sink_peel` 的正确形式**不是**简单的「补 `|α|` 因子」或「加一个前提」，
  而是需要在「只依赖补集」这个区域重新设计引理体系。

  **本会话到此为止的所有工具都不适用。**

  ## 诚实边界

  本文件不含新定理。它是对 6 步诊断链的最终登记。
  =========================================================================== -/
