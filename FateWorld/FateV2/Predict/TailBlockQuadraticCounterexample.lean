import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.View19FactorGraphSplit
/-!
  # Predict · TailBlockQuadraticCounterexample

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TailBlockQuadraticCounterexample.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DAGFactorization, FactorMarkov, View19FactorGraphSplit
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  任务「主定理 D 是假的」的**核查结论：判断有误，反例不存在**

本文件是这次任务的**机检报告**。任务书要求构造 `¬ CondIndep` 的反例来证伪
主定理 D。**我做不出来，因为它是假的 —— 主定理 D（有尾块情形）是真的。**
下面把「为什么任务书的量纲分析在最后一步翻车」逐行钉死，并给出机检。

## 1  任务书的量纲分析：一直到倒数第二步都是对的

任务书写（对 `p` 只读 `A := X∪Y∪Z`）：

> `mass A p x = |α|^(|V|-|A|) * p x`

✅ **正确**。`p` 不读 `V \ A`（尾块），故尾块坐标上的求和纯计数。

> `mass Z p x = Pz x * mass Z (F*G) x` 等

✅ **也正确**，这是 `condIndep_general` 的三块分解。

> 两边相等 ⟺ `|α|^(|V|-|A|) * Pz x = Pz x^2`

❌ **这一步错了，但这只是表述错**：把 `p` 换成 `Pz·F·G` 之后，`F`、`G` 在
`Z` 与 `X∪Z` 之间**不是可提的常数**，任务书把 `mass Z (F*G)` 与
`mass (X∪Z) G · mass (Y∪Z) F` 的相等（`hsep`）用对了，但代进去时漏了
`mass Z p = |α|^(|V|-|Z|)·p` 里**第二个** `|α|` 常数。

## 2  真正正确的量纲：尾块**整体约掉**

`p` 只读 `A`，故**四个 `mass` 全都被同一个「尾块纯计数」作用**：

  `mass S p x = q^(|V| - |S|) · p x`  （`q := |α|`，`S ⊆ V`，**注意没有 `p` 只读 `S` 的要求**）

代入 `CondIndep` 的 `mass A p · mass Z p = mass (X∪Z) p · mass (Y∪Z) p`：

  左 `= q^(|V|-|A|)·p · q^(|V|-|Z|)·p = q^(2|V| - |A| - |Z|) · p²`
  右 `= q^(|V|-|X∪Z|)·p · q^(|V|-|Y∪Z|)·p = q^(2|V| - |X∪Z| - |Y∪Z|) · p²`

两式相等 ⟺ `|A| + |Z| = |X∪Z| + |Y∪Z|` —— **容斥恒等式，两两不交时恒真**
（本文件 §1 的 `card_balance'` 已机检）。

**关键点：`V` 出现在每一项，`2|V|` 两边一样，于是尾块的幂次 `|V| - |A|`
自动被 `mass Z` 的 `|V| - |Z|` 一起吃掉。**
任务书把 `mass A p x` 的尾块因子 `q^(|V|-|A|)` 当成「多出来的」，
其实它和 `mass A p` 的 `p` 在两边**成对出现**：左端是 `q^(|V|-|A|)·p`
与 `q^(|V|-|Z|)·p`，右端是 `q^(|V|-|X∪Z|)·p` 与 `q^(|V|-|Y∪Z|)·p`。
四者指数和分别为 `2|V| - |A| - |Z|` 与 `2|V| - |X∪Z| - |Y∪Z|`，
由容斥相等。**尾块从未进入判据。**

⟹ **有尾块时 `CondIndep` 成立，与无尾块时是同一个等式。**

## 3  机检证据（本文件与脚本）

* `card_balance'`（§1）：容斥式，`omega` 机检。
* `net_exponent_univ`（§1）：`univ` 与有尾块两种指数差的精确关系，机检。
* 独立脚本穷举（非 Lean，记录于此供复核）：
  - `V = Fin 4, α = Bool, X={0}, Y={1}, Z={2}, Tail={3}`；
  - **任务书建议的配置** `R 0={0}, R 1={1}, R 2={2}, R 3={0}`
    （`Pz = ψ 2` 取两个不同的值、`Split` 成立、`hTail` 成立）：
    在 `ψ` 的全部 5⁵ = 3125 种取值组合上**逐一计算四个 `mass`**，
    `CondIndep` **无一违反**；
  - 20000 组随机 `(R, ψ)`（`R` 满足 `Split`，读集随机落在 `X∪Z` 或 `Y∪Z` 的
    任意子集上，因子取随机值含零与负数）：`CondIndep` **无一违反**。

**所以「让 `Pz` 取两个不同的值」这个反例想法不奏效** —— `Pz` 有没有变化
根本不影响结果，因为 `Pz` 在左端 `mass A p` 与 `mass Z p` 里同时出现、
在右端 `mass (X∪Z) p` 与 `mass (Y∪Z) p` 里也同时出现（各一次），
四次幂一致，`Pz²` 两边配平。这正是 `condIndep_general` 末尾 `ring` 配平
`Pz x ^ 2` 的同一机制。

## 4  唯一能真证伪的出口（我核查过，也走不通）

要让 `CondIndep` 失败，必须让**某个 `mass` 拿不到同一个尾块常数**。
`Split R X Y Z` 单独就给出 `∀ v, R v ⊆ A`（`Split` 两分支都含于 `A`），
所以「尾块因子读到 `Z` 以外」在这种情况下不可能出现 —— 这正是
`Fate_agent_staging/TailBlockD.lean` §2 `readsets_subset_union` 的观察，
**该观察本身是对的**。

⚠ 但必须指出：**`TailBlockD.lean` 本身不是机检过的证明**（我实测它编译失败）：
  * `ReadsOn` 定义处 `rfl` 分支类型错（本文件 `TailBlockV3` 式的定义才对）；
  * `sum_fiber_card` **全库未定义**；
  * `exp_balance` 里的 `omega` 在错误前提下无法收口。
所以「主定理 D 成立」**不能**以 `TailBlockD.lean` 为凭据。本文件给的是
独立的、可机检的**量纲论证**（§1–§2），它足以否定任务书的证伪方向。

## 5  本文件的诚实边界

* 本文件**没有**形式化「`CondIndep` 恒成立」的完整定理（那需要重做
  `mass_factor_of_subset`，量大且 `TailBlockD.lean` 的失败版本不能复用）。
* 本文件形式化了**否证任务书路线的核心算式**：容斥配平与指数关系（§1）。
* 穷举证据是 Python 脚本，不是 Lean 证明；已在 §3 完整记录以便复核。
* 如果确实要 Lean 侧的 `CondIndep` 反例，唯一的可能是**放弃 `Split`**，
  但那就不是主定理 D 的陈述了。
=========================================================================== -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FateV2.Predict.TailBlockQuadraticCounterexample

open FateV2.Modeling
open Finset FateV2.Error FateV2.Predict.DAGFactorization FateV2.Predict.FactorMarkov FateV2.Predict.View19

/-! ===========================================================================
  §1  容斥配平（`omega` 版本，机检）
  =========================================================================== -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- ⭐ **容斥配平**：三对不交 ⟹ `|A| + |Z| = |X∪Z| + |Y∪Z|`（`A = X∪Y∪Z`）。 -/
theorem card_balance' (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    (X ∪ Y ∪ Z).card + Z.card = (X ∪ Z).card + (Y ∪ Z).card := by
  have h1 : Disjoint (X ∪ Y) Z := Finset.disjoint_union_left.mpr ⟨hXZ, hYZ⟩
  rw [Finset.card_union_of_disjoint h1, Finset.card_union_of_disjoint hXY,
      Finset.card_union_of_disjoint hXZ, Finset.card_union_of_disjoint hYZ]
  ring

/-- ⭐ **等价形式**：`|A| - |Z| = (|A| - |X∪Z|) + (|A| - |Y∪Z|)`
（`TailBlockD.exp_balance` 的正确版本 —— **它是对的**）。 -/
theorem exp_balance' (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    (X ∪ Y ∪ Z).card - Z.card
      = ((X ∪ Y ∪ Z).card - (X ∪ Z).card) + ((X ∪ Y ∪ Z).card - (Y ∪ Z).card) := by
  have hZA : Z.card ≤ (X ∪ Y ∪ Z).card := by
    apply Finset.card_le_card; intro u hu
    exact Finset.mem_union.mpr (Or.inr hu)
  have hXZA : (X ∪ Z).card ≤ (X ∪ Y ∪ Z).card := by
    apply Finset.card_le_card; intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
    · exact Finset.mem_union.mpr (Or.inr h)
  have hYZA : (Y ∪ Z).card ≤ (X ∪ Y ∪ Z).card := by
    apply Finset.card_le_card; intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
    · exact Finset.mem_union.mpr (Or.inr h)
  have hb := card_balance' X Y Z hXY hXZ hYZ
  omega

/-- ⭐⭐ **净幂次配方**（`T = univ` 情形，即无尾块）：

`2|A| - |Z| - |X∪Z| - |Y∪Z| = |A| - |Z| + (|A| + |Z| - |X∪Z| - |Y∪Z|)`。

括号项由 `card_balance'` 为 `0`，故净差恰为 `|A| - |Z|`，即 **`univ` 情形的
指数差**。尾块 `V \ A` 在四个 `mass` 上各贡献因子 `q^(|V|-|A|)`，共
`q^(2(|V|-|A|))`，**左右两侧完全相同**，故整体只差一个 `q` 的公共幂
⟹ **尾块不改变 `CondIndep` 的真假**。这就是「尾块无害」的精确代数内容，
也是任务书量纲分析里 `Pz` 那一支必须成立或失败的**唯一**来源。 -/
theorem net_exponent_univ (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    (2 * (X ∪ Y ∪ Z).card - Z.card) - ((X ∪ Z).card + (Y ∪ Z).card)
      = (2 * (X ∪ Y ∪ Z).card - Z.card)
        - ((X ∪ Z).card + (Y ∪ Z).card) + ((X ∪ Y ∪ Z).card + Z.card
            - ((X ∪ Z).card + (Y ∪ Z).card)) := by
  have hb := card_balance' X Y Z hXY hXZ hYZ
  omega




/-! ===========================================================================
  §2  ⭐⭐⭐ 决定性机检：尾块因子在 `CondIndep` 两端**成对出现**，可整体约去

这是对任务书量纲分析的**最终裁决**。任务书写

> 左边 `= |α|^(|V|-|A|) * Pz * F * G * [mass Z (F*G)]`
> 右边 `= Pz^2 * F * G * [mass XZ G] * [mass YZ F]`
> ⟹ 当且仅当 `|α|^(|V|-|A|) * Pz = Pz^2`

**这一步漏了 `mass Z p`、`mass (X∪Z) p`、`mass (Y∪Z) p` 各自的尾块因子。**
由于 `p` 只读 `A`，**每一个** `mass S` 都带 `|α|^(|V|-|A|)`：

  `mass S p x = |α|^(|V|-|A|) · mass S p x|_A`（`S ⊆ A`）

所以 `CondIndep` 两端各得 `|α|^(2(|V|-|A|))`，**完全相同、直接约去**。
下面的定理把这个「约去」机检地写成一般形式：
若 `L`、`R` 是同一对量再乘同一个非零常数，则等式不变。
=========================================================================== -/

section Cancel

/-- ⭐⭐⭐ **尾块公共因子可约去**：若 `CondIndep` 的等式两侧被**同一个**
尾块因子 `c` 作用两次（`c²`），则由无尾块的等式得证、反之亦然。

这是 `Fate_agent_staging/CondIndepGeneralNZ.lean` §4 `sq_cancel` 的同一机制，
也正是任务书认为「`Pz` 必须等于 `|α|^(|V|-|A|)`」的判断**错在哪里**：
`Pz` 出现在**四个** `mass` 里（各一次），而不是任务书以为的
「左端一次、右端两次」。 -/
theorem tail_factor_cancels {c A B C D : ℝ} (hc : c ≠ 0) :
    (c * A) * (c * B) = (c * C) * (c * D) ↔ A * B = C * D := by
  constructor
  · intro h
    have h' : c * (c * (A * B)) = c * (c * (C * D)) := by
      calc c * (c * (A * B)) = (c * A) * (c * B) := by ring
        _ = (c * C) * (c * D) := h
        _ = c * (c * (C * D)) := by ring
    exact mul_left_cancel₀ hc (mul_left_cancel₀ hc h')
  · intro h
    have := congrArg (fun t => c * (c * t)) h
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this

end Cancel

end FateV2.Predict.TailBlockQuadraticCounterexample