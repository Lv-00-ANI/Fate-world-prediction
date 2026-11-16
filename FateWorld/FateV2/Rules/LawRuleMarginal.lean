/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.LawRuleMarginal
阶段：**「边缘化」—— 规格开放问题 5.1 的候选语义 #2**

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
`Fate/LawRule.lean` 的头注释明写：`∘` 的语义「是两条规则前后相接、
是条件分布的**边缘化**、还是规则集的并？原文未给。」

本文件实现**第二个候选语义**：**边缘化（推前）**。

CHAIN-1 报告实测：三候选分处**三个互不相连的载体**上 ——

| 候选 | 载体 | 状态 |
|---|---|---|
| #1 前后相接 | `MeasurableRule`（`ComposeOperator` 的 `comp`） | 已实现，但不在 `LawRule` 上 |
| #2 边缘化 | 全库 0 命中 | **❌ 完全缺** |
| #3 并 | `Set K3.MFCA`（`WiringFourOperators` 的 `combClosure`） | 已实现，但在第三个载体上 |

本文件把候选 #2 补到 **`LawRule` 这个载体上**，从而使 5.1 的三个候选
中至少有一个能在**同一载体**上与 `compose`（取交）同台比较。

---------------------------------------------------------------------------
数学定义
---------------------------------------------------------------------------
规则 `R : LawRule C X Y` 在每个 `(c, x)` 处给出一族允许的测度。
边缘化把 `Y` 上的测度沿可测映射 `phi : Y.Carrier → Z.Carrier` 推到 `Z` 上：

    marginal R phi hphi c x  :=  Measure.map phi hphi '' (R c x)

即「把每一条允许的测度都推前，得到 `Z` 上的允许集」。

| 算子 | 语义 | 空间 |
|---|---|---|
| `compose` | 两条规律**同时**成立（取交） | **同一**空间上收窄 |
| `marginal` | 把允许的测度**搬到**另一个空间 | **跨**空间搬运 |

---------------------------------------------------------------------------
主要结果
---------------------------------------------------------------------------
1. `mem_marginal_iff`：**语义刻画** —— `mu ∈ marginal R phi hphi c x`
   ⟺ 存在 `nu ∈ R c x` 使 `mu = phi_* nu`；
2. `marginal_id`：**单位律** —— 恒等映射的边缘化是恒等；
3. `marginal_comp`：**结合律（函子性）** —— 两次边缘化 = 复合映射的边缘化；
4. `marginal_mono`：边缘化**保持包含**（单调性）；
5. `marginal_inter_subset`：⭐ **关键否定/限定结果** ——
   边缘化与 `compose`（取交）之间只有**包含**关系，**等号不成立**。
6. `marginal_eq_empty_iff` / `marginal_bot`：边缘化保持空（`bot` 是边缘化的零元）。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- ⚠ 本文件**不**证明「`marginal` 是 `∘` 的正确语义」，它只是把 5.1 的
  第二个候选**形式化**，使三选一成为可比较的问题。
- ⚠ **任务草案中的 `marginal_inter` 等式是假的**（作为等式）。

  草案写：

      marginal (compose R1 R2) phi hphi
        = compose (marginal R1 phi hphi) (marginal R2 phi hphi)

  这条**不能**由 `Set.image_inter` 得到 —— `Set.image_inter` 需要
  `Function.Injective phi`（本库实测签名：
  `Set.image_inter : Function.Injective f → f '' (s ∩ t) = f '' s ∩ f '' t`），
  而边缘化必须对**任意可测**（通常不单）`phi` 有意义。
  对非单射 `phi`，两个不同测度可以推前到同一个像，
  于是左边严格小于右边。本文件给出**成立的方向**：
  `marginal_inter_subset`（左边 ⊆ 右边），
  并在 `marginal_inter_of_injective` 中给出**单射下等号成立**的正确陈述。
- G54：本文件全部标识符使用 ASCII（`phi`/`psi`/`mu`/`nu`/`R1`/`R2`/`c`/`x`）。
- 无 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。
-/

import FateWorld.FateV2.Rules.LawRule
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace LawRule

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} {Z : OutSpace} {W : OutSpace}
  [MeasurableSpace Y.Carrier] [MeasurableSpace Z.Carrier] [MeasurableSpace W.Carrier]

/-!
  # Rules · LawRuleMarginal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LawRuleMarginal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  定义：边缘化（推前）
    =========================================================================== -/

/-- **边缘化（推前）**：把每条允许的测度通过 `phi` 推到 `Z` 上。

这是规格开放问题 5.1 的候选语义 #2：「条件分布的边缘化」。

**与 `compose`（取交）的对偶**：
- `compose`：在**同一空间**上收窄（取交）
- `marginal`：把测度**搬到另一个空间**（推前）

⚠ **本库实测签名**（见报告 §`#check` 输出）：

    Measure.map : (α → β) → Measure α → Measure β

`Measure.map` **不把可测性作为参数**（与部分旧版 Mathlib 不同）。
故 `hphi` 在本定义中**不被消费**，我保留它只是为了在类型层留下
「`phi` 可测」这一语义见证，供下游（如 `marginal_comp` 的 `Measure.map_map`）使用。
`marginal_inter_subset` / `marginal_bot` 等不依赖可测性的结论因此是**免费的**。 -/
def marginal (R : LawRule C X Y) (phi : Y.Carrier → Z.Carrier)
    (_hphi : Measurable phi) : LawRule C X Z :=
  fun c x => MeasureTheory.Measure.map phi '' (R c x)

/-! ===========================================================================
    §2  语义刻画
    =========================================================================== -/

/-- **边缘化的语义**：`mu ∈ marginal R phi hphi c x` 当且仅当
存在 `nu ∈ R c x` 使得 `mu = phi_* nu`。

这条把 `marginal` 的**读法**固化为定理：边缘化之后的允许集，
恰是「原本允许的测度」的推前像。 -/
theorem mem_marginal_iff (R : LawRule C X Y) (phi : Y.Carrier → Z.Carrier)
    (hphi : Measurable phi) (c : C.Carrier) (x : X.Carrier)
    (mu : MeasureTheory.Measure Z.Carrier) :
    mu ∈ marginal R phi hphi c x ↔
      ∃ nu ∈ R c x, MeasureTheory.Measure.map phi nu = mu :=
  Iff.rfl

/-! ===========================================================================
    §3  单位律与结合律（函子性）
    =========================================================================== -/

/-- **边缘化的幺元**：恒等映射不改变规则。

恒等映射的推前是恒等（`Measure.map_id`），故逐点的像集还原为原集合。 -/
theorem marginal_id (R : LawRule C X Y) :
    marginal R (fun y => y) measurable_id = R := by
  funext c x
  show (fun mu => MeasureTheory.Measure.map id mu) '' (R c x) = R c x
  have h : (fun mu : MeasureTheory.Measure Y.Carrier => MeasureTheory.Measure.map id mu) = id := by
    funext mu
    exact MeasureTheory.Measure.map_id
  rw [h]
  exact Set.image_id _

/-- **边缘化的复合**：两次边缘化 = 一次复合映射的边缘化。

这是 `marginal` 作为**函子**的相容性：`(psi ∘ phi)_* mu = psi_* (phi_* mu)`，
由 `Measure.map_map` 给出。 -/
theorem marginal_comp (R : LawRule C X Y) (phi : Y.Carrier → Z.Carrier)
    (hphi : Measurable phi) (psi : Z.Carrier → W.Carrier) (hpsi : Measurable psi) :
    marginal (marginal R phi hphi) psi hpsi =
      marginal R (fun y => psi (phi y)) (hpsi.comp hphi) := by
  funext c x
  show (fun mu => MeasureTheory.Measure.map psi mu) ''
      ((fun mu => MeasureTheory.Measure.map phi mu) '' (R c x)) =
    (fun mu => MeasureTheory.Measure.map (fun y => psi (phi y)) mu) '' (R c x)
  rw [Set.image_image]
  refine Set.image_congr' ?_
  intro mu
  exact MeasureTheory.Measure.map_map hpsi hphi

/-! ===========================================================================
    §4  单调性与零元
    =========================================================================== -/

/-- **边缘化保持包含**（单调性）：规则越宽，边缘化之后越宽。 -/
theorem marginal_mono {R1 R2 : LawRule C X Y} (h : ∀ c x, R1 c x ⊆ R2 c x)
    (phi : Y.Carrier → Z.Carrier) (hphi : Measurable phi) :
    ∀ c x, marginal R1 phi hphi c x ⊆ marginal R2 phi hphi c x := by
  intro c x mu hmu
  obtain ⟨nu, hnu, heq⟩ := (mem_marginal_iff R1 phi hphi c x mu).mp hmu
  exact (mem_marginal_iff R2 phi hphi c x mu).mpr ⟨nu, h c x hnu, heq⟩

/-- **边缘化保持空**：空规则的边缘化仍为空。 -/
theorem marginal_eq_empty_iff (R : LawRule C X Y) (phi : Y.Carrier → Z.Carrier)
    (hphi : Measurable phi) (c : C.Carrier) (x : X.Carrier) :
    marginal R phi hphi c x = ∅ ↔ R c x = ∅ :=
  Set.image_eq_empty

/-- **`bot` 在边缘化下仍是 `bot`**（与 `compose_bot` 的零元地位对偶）。 -/
theorem marginal_bot (phi : Y.Carrier → Z.Carrier) (hphi : Measurable phi) :
    marginal (bot C X Y) phi hphi = bot C X Z := by
  funext c x
  exact Set.image_empty _

/-! ===========================================================================
    §5  ⭐ 与 `compose`（取交）的关系 —— 只有包含，没有等式
    =========================================================================== -/

/-- ⭐ **边缘化与取交：包含方向成立**。

「先取交再边缘化」⊆「先边缘化再取交」。

证明：`mu` 来自某个 `nu ∈ R1 c x ∩ R2 c x`；同一个 `nu` 同时见证
`mu ∈ marginal R1 ...` 与 `mu ∈ marginal R2 ...`。

⚠ 反向**不成立**（见下条注释）：`R1` 与 `R2` 的允许测度可以**不同**，
经非单射 `phi` 推前后却相同，于是落在右边而不落在左边。 -/
theorem marginal_inter_subset (R1 R2 : LawRule C X Y) (phi : Y.Carrier → Z.Carrier)
    (hphi : Measurable phi) :
    ∀ c x, marginal (compose R1 R2) phi hphi c x ⊆
      compose (marginal R1 phi hphi) (marginal R2 phi hphi) c x := by
  intro c x mu hmu
  obtain ⟨nu, hnu, heq⟩ := (mem_marginal_iff (compose R1 R2) phi hphi c x mu).mp hmu
  refine ⟨?_, ?_⟩
  · exact (mem_marginal_iff R1 phi hphi c x mu).mpr ⟨nu, hnu.1, heq⟩
  · exact (mem_marginal_iff R2 phi hphi c x mu).mpr ⟨nu, hnu.2, heq⟩

/-- **边缘化与取交：`phi` 为可测嵌入时等号成立**。

`Set.image_inter`（本库实测签名：

    Set.image_inter : Function.Injective f → f '' (s ∩ t) = f '' s ∩ f '' t

）需要的是 **`Measure.map phi` 在测度上单射**，而**不是** `phi` 在点上单射 ——
这是任务草案里那条等式为假的**真正原因**（草案误以为点单射就够）。

本库实测的可用事实是

    Measure.map_injective (hf : MeasurableEmbedding f) : Function.Injective (Measure.map f)

（`Mathlib/MeasureTheory/Measure/Map.lean:285`，命名空间 `MeasurableEmbedding`）。
故正确前件是 **`MeasurableEmbedding phi`** —— 它既蕴含 `Measurable phi`
又蕴含测度推前单射。此即「先取交再边缘化 = 先边缘化再取交」的确切条件。 -/
theorem marginal_inter_of_embedding (R1 R2 : LawRule C X Y) (phi : Y.Carrier → Z.Carrier)
    (_hphi : Measurable phi) (hemb : MeasurableEmbedding phi) :
    marginal (compose R1 R2) phi _hphi =
      compose (marginal R1 phi _hphi) (marginal R2 phi _hphi) := by
  funext c x
  show (fun mu => MeasureTheory.Measure.map phi mu) '' (R1 c x ∩ R2 c x) =
    (fun mu => MeasureTheory.Measure.map phi mu) '' (R1 c x) ∩
      (fun mu => MeasureTheory.Measure.map phi mu) '' (R2 c x)
  exact Set.image_inter (hemb.map_injective)

end LawRule

end FateV2.Rules