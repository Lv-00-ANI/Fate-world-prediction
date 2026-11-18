import FateWorld.FateV2.Predict.MassSdiffConst
import FateWorld.FateV2.Predict.SinkPeelCounterexample
import FateWorld.FateV2.Predict.FactorMarkov
/-!
  # Predict · SinkPeelDiagnosis

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SinkPeelDiagnosis.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MassSdiffConst, SinkPeelCounterexample, FactorMarkov
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `sink_peel` 的**完整诊断**（不是定理，是结构分析 + 一个机检反例的引用）

  ## 原定理（Fate/Strategy9SinkPeelNorm.lean）

  ```lean

namespace FateV2.Predict.SinkPeelDiagnosis

  theorem sink_peel (hloc : LocalTo G f) (hsT : s ∈ T) (hsink : ∀ w, ¬ G.edge s w) :
      bar T f x = bar (T \\ {s}) f (unpin s x a₀) * f s x
  ```

  ## 反例（`Fate/SinkPeelCounterexample.lean`，机检）

  `V = Fin 1`、`α = Bool`、`f ≡ 1`、`T = {0}`、`s = 0`：
  左 = 1，右 = 2。**故原陈述不成立。**

  ## 诊断：缺 `|α|` 因子

  `mass (T \\ {s})` 的纤维比 `mass T` 大 `|α|` 倍
  （少一个约束 `w_s = x_s`）。这是 `Fate/MassSdiffConst.lean` 的
  `mass_sdiff_of_reads` 证明的内容（在 `g` 只读 `T \\ {s}` 时）。

  ## 但 `mass_sdiff_of_reads` 不能直接用于 `sink_peel`

  `sink_peel` 里的被积函数是 `∏_{v ∉ T} f_v`，它读 `univ \\ T`，
  **不是** `T \\ {s}`。两个集合不同，故不能直接套用。

  ## 正确的修正方向

  `sink_peel` 需要额外前提「`f_s` 只读 `s`」（或「`f_s` 在 `T`-纤维上常值」），
  这样才能把 `f_s` 从 `mass` 内部提出来。`hloc : LocalTo G f` 只给
  「`f_v` 读 `{v} ∪ pa(v)`」，**不**蕴含 `f_s` 只读 `s`。

  ## 诚实边界

  本文件不含新定理，只登记诊断。反例见 `SinkPeelCounterexample.lean`。
  =========================================================================== -/

end FateV2.Predict.SinkPeelDiagnosis
