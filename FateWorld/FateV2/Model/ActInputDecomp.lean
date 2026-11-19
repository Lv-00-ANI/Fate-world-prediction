/-
命运理论 · Lean 4 形式化实现
================================

模块：FateV2.Model
主题：**开放问题 2.2 —— `a_t` 与 `u_t` 的分解存在性**

---------------------------------------------------------------------------
(a) 净版 2.2 的原文（`10-命运理论-净版.md:589`）
---------------------------------------------------------------------------
> **[开放问题] 开放问题 2.2（`a_t` 与 `u_t` 的关系）**
> 约定 1.8 声明 `u_t = (a_t, ũ_t)`，即**干预是外生输入的一个可辨识分量**。
> 但**该分解是否总是存在**，以及 `a_t` 与 `ũ_t` 的取值空间是否独立，
> 原素材未给。
> 〔`[原文 turn-19]` 只给出该分解式，未给存在性条件。〕

---------------------------------------------------------------------------
(b) 事实：`Frame` 里 `U` 与 `Act` 是【并列的独立字段】，不是嵌入
---------------------------------------------------------------------------
`Fate/Frame.lean` 的 `Frame` 结构（`Frame.lean:73-83`）有

    U   : InputSpace    -- 外生输入空间 U（规格 §1.2）
    Act : ActionSpace   -- 动作空间 A（规格 §1.2）

二者是**并列的独立字段**，`U` **不是** `Act × ũ` 的写法，
`Frame` 中**没有**任何 `Act → U` 的字段。这是已入链的事实，本文件不修改它。

---------------------------------------------------------------------------
(c) 本文件的结论（三条，逐条对应下面三个具体的定理）
---------------------------------------------------------------------------
**读法 A（并列，Lean 现状）** —— 「分解」只可能读作配对 `(a, u) ∈ Act × U`。
  - 该配对**平凡存在**（`actInput_pair_bijective`、`actInput_pair_surjective`）。
  - **但**：这只说明 `Act × U` 这个类型非空／可换序，
    **完全不**说明「干预 `a_t` 是 `u_t ∈ U` 的一个分量」。
    净版所说的「可辨识分量」需要从 `u_t` 中**读出** `a_t`，
    而 `Act × U` 的配对**没有**提供任何 `U → Act` 的读出映射。
  - 故 **读法 A 不支撑净版的分解式**。

**读法 B（嵌入，净版原意）** —— 「`Act` 是 `U` 的一个可辨识分量」。
  这在 `Frame` 现状下**不成立**，证据有两层：
  1. **反例（否定性结论，本文件的主要价值）**：
     `noEmbed_counterFrame` 给出一个**具体的 `Frame`**，
     其 `Act = Unit`、`U = Empty`，并证明**不存在**单射 `Act → U`。
     故「分解总是存在」**不能**从 `Frame` 的定义推出。
  2. **正向（需加结构）**：给出结构 `FrameWithDecomp`，
     它显式携带嵌入 `embed : Act → U`（+ 单射性）**以及**收缩
     `retract : U → Act`（+ `retract ∘ embed = id`）。
     在此结构下分解式**成立且可构造**（`decomp_B_holds` 等）。

  **⚠ 为何要收缩而不止单射**：净版说的是「**可辨识**分量」。
  单射只保证 `a ↦ (a, ũ)` 不碰撞，**不保证**能从 `u_t` 反读出 `a_t`。
  「可辨识」在类型层的准确落点是存在**左逆**（`Function.LeftInverse`），
  即 `∀ a, retract (embed a) = a`。本文件把这一层如实区分：
  `FrameWithDecomp.embed_inj`（可分辨）与 `FrameWithDecomp.retract_embed`（可辨识）**分列**。

**两条最锋利的定理（对应上面正负两面）**：
  - `exists_decomp_iff`：`Frame` 可升级为 `FrameWithDecomp` **当且仅当**
    存在带左逆的单射 `Act → U`。这是开放问题 2.2 在 `Frame` 层上的**可操作等价形式**。
  - `counterFrame_no_decomp`：`noEmbedCounterFrame` **不可能**升级为
    `FrameWithDecomp`（经由上述 iff 与 `U = Empty` 闭合）。
    故否定性结论**不是「暂未找到」而是「结构上不可能」**。

---------------------------------------------------------------------------
(d) ⚠ 本文件【不】声称「开放问题 2.2 已解决」
---------------------------------------------------------------------------
本文件给出的是：
  - 读法 A 平凡成立（但不足以支撑净版分解式）；
  - 读法 B 在 `Frame` 现状下**不成立**（有具体反例），
    **加结构 `FrameWithDecomp` 后成立**。
  - **未**回答「该分解**是否总是**存在」这一问题的世界性内容——
    该问题的答案取决于**具体实例**的 `U`、`Act` 是否允许一个带左逆的嵌入；
    这是**经验/建模问题**，不是定义层能裁决的。
  - **未**讨论 `a_t` 与 `ũ_t` 取值空间是否独立（净版同时问的第二问）——
    本结构只给出「`Act` 经嵌入落在 `U` 内」，对 `ũ_t` 的取值空间**不作断言**。

---------------------------------------------------------------------------
依赖与纪律
---------------------------------------------------------------------------
- `import FateV2.Model.Frame`；**不修改** `Frame`；新结构 `FrameWithDecomp` 为新建。
- 零 `sorry` / `admit` / `axiom`。
- 文件头只列实际存在的定理。
-/

import FateWorld.FateV2.Model.Frame
namespace FateV2.Model
open Function

universe u

noncomputable section

/-!
  # Model · ActInputDecomp

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ActInputDecomp.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  读法 A（并列）：`Act × U` —— 配对平凡存在
    =========================================================================== -/

/-- **读法 A 的配对换序是双射**。

`Act × U` 与 `U × Act` 之间的换序 `(a, u) ↦ (u, a)` 是双射。

**这说明了什么**：`Frame` 中 `U` 与 `Act` 两个字段**都是可取值的类型**，
故配对 `Act × U` **非空地存在**（假设两者非空——见下条）。
「带分解的输入」在**类型层**不构成障碍。

**这不说明什么（关键）**：它**不**说明 `a_t` 是 `u_t` 的**分量**。
换序只是 `Act × U` 内部的重排，**没有**触及 `U` 本身。
「`Act` 是 `U` 的可辨识分量」需要 `U → Act` 的读出映射，
而 `Act × U` 的**第一**投影是 `Act × U → Act`，定义域是**积**，不是 `U`。
故本定理**不支撑**净版 `u_t = (a_t, ũ_t)` 的读法。 -/
theorem actInput_pair_bijective (F : Frame) :
    Function.Bijective (fun p : F.Act.Carrier × F.U.Carrier => (p.2, p.1)) := by
  constructor
  · rintro ⟨a₁, u₁⟩ ⟨a₂, u₂⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · rintro ⟨u, a⟩
    exact ⟨(a, u), rfl⟩

/-- **读法 A 的配对投影是满射**（`Act × U → Act × U` 的恒等配对）。

即：`(a, u) ↦ (a, u)` 命中 `Act × U` 中每一点。

**意义**：`Frame` 允许「同时指定一个干预 **和** 一个外生输入」，
这在类型层是平凡的（恒等映射）。**这与「`a` 从 `u` 中读出」是两件事**。 -/
theorem actInput_pair_surjective (F : Frame) :
    Function.Surjective (fun p : F.Act.Carrier × F.U.Carrier => (p.1, p.2)) :=
  fun q => ⟨q, rfl⟩

/-- **读法 A 的最强可证形式（如实标注其限度）**：

若 **`Act` 与 `U` 都非空**，则存在从 `U` 到 `Act` 的**某个**映射
（常函数）。但这**不是**「分量」——常映射没有任何辨识力，
它把 `U` 的全部信息压到单个 `a`。

**⚠ 本定理故意做得弱并保留于此**，是为了**明确划出读法 A 的天花板**：
从 `Frame` 现状（仅有非空性）出发，能得到的「`U → Act` 映射」
**至多是常映射**，它**不**区分 `U` 中任何两个不同的 `u`。
故「可辨识」在 `Frame` 现状下**无从谈起**。 -/
theorem actInput_const_map_of_nonempty (F : Frame)
    [Nonempty F.Act.Carrier] [Nonempty F.U.Carrier] :
    ∃ f : F.U.Carrier → F.Act.Carrier, ∀ u₁ u₂, f u₁ = f u₂ := by
  obtain ⟨a⟩ := ‹Nonempty F.Act.Carrier›
  exact ⟨fun _ => a, fun _ _ => rfl⟩

/-! ===========================================================================
    §2  读法 B 的否定性结论：`Frame` 现状下【不】保证嵌入存在
    =========================================================================== -/

/-- **反例框架**：`Act = Unit`（非空），`U = Empty`（空）。

其余空间取最小可行（`Unit`）。

**为何选它**：`Act` 非空而 `U` 为空，则**任何** `Act → U` 的映射
都必须把 `()` 送到 `Empty` 中某点——不可能。
故这是「分解**不**存在」的最小见证，**排除了「所有 Frame 都有分解」**。

**其余字段的取法说明**：`StateSpace` 带 `borel_le` 前件，
取 `MeasurableSpace := ⊤` 使 `borel Carrier ≤ ⊤` 恒真（`le_top`），
这是 `Fate/SCMWorldModel.lean:229` 等处的同一最小可行选择。 -/
def noEmbedCounterFrame : Frame where
  Θ := { Carrier := Unit }
  X := { Carrier := Unit, borel_le := le_top }
  U := { Carrier := Empty }
  Act := { Carrier := Unit }
  Ν := { Carrier := Unit }

/-- ⭐⭐ **否定性结论（本文件的主要价值）**：

在 `Frame` 现状下，**「嵌入 `Act ↪ U` 总是存在」为假**。

具体地，`noEmbedCounterFrame` 有 `Act = Unit`、`U = Empty`，故
**不存在**单射 `Act.Carrier → U.Carrier`：

    若 i : Act → U 存在，则 i () : Empty，矛盾。

**⟹ 推论**：净版 2.2 的分解式 `u_t = (a_t, ũ_t)`（作为 `Act ↪ U` 的读法）
**不能**由 `Frame` 的定义推出。这正是开放问题 2.2 的准确状态：
**需要额外结构**（见 §3 的 `FrameWithDecomp`）。 -/
theorem noEmbed_counterFrame :
    ¬ ∃ i : noEmbedCounterFrame.Act.Carrier → noEmbedCounterFrame.U.Carrier,
        Function.Injective i := by
  rintro ⟨i, _hi⟩
  exact (i ()).elim

/-- **否定性结论的「存在」版本（给下游更好用）**：

存在一个 `Frame`，其中**不存在**任何 `Act → U` 的映射（更谈不上单射）。

**为何单列**：下游若要对「所有 Frame」做量化否定，
用本定理的 `¬ ∀ ... 存在` 形式更直接（`noEmbed_counterFrame` 是它的见证形式）。 -/
theorem not_forall_embed :
    ¬ ∀ G : Frame, ∃ i : G.Act.Carrier → G.U.Carrier, Function.Injective i := by
  intro h
  obtain ⟨i, _⟩ := h noEmbedCounterFrame
  exact (i ()).elim

/-! ===========================================================================
    §3  读法 B 的正向：加结构 `FrameWithDecomp`（不修改 `Frame`）
    =========================================================================== -/

/-- **带分解的框架**：在 `Frame` 上**额外**携带 `Act` 作为 `U` 的可辨识分量。

**两个字段的层次必须分清**（净版「可辨识」一词的准确落点）：

| 字段 | 类型 | 满足净版的哪一层 |
|---|---|---|
| `embed` | `Act → U` | 分解式的**存在**（`a` 对应到某个 `u`） |
| `embed_inj` | 单射 | **可分辨**（不同 `a` 不碰撞） |
| `retract` | `U → Act` | **可辨识**：从 `u` **反读**出 `a` |
| `retract_embed` | `∀ a, retract (embed a) = a` | 反读正确（`retract ∘ embed = id`） |

**⚠ 为何需要 `retract` 而非仅 `embed_inj`**：
单射**不**给出左逆（一般存在单射而无左逆的映射，例如
`Bool → Bool × Bool` 的两种嵌入在某些纤维外无逆）。
净版要的是「**可辨识**分量」——即从 `u_t` 能取回 `a_t`——
这正是**左逆**（`Function.LeftInverse retract embed`）。
本结构把二者**并列保留**（`embed_inj` 与 `retract_embed` 分开），
使「可分辨」与「可辨识」的差别在类型层可见、不可混淆。

**⚠ 本结构不修改 `Frame`**（已入链），故用 `extends`。
`toFrame` 投影 `FrameWithDecomp → Frame` 由 `extends` 自动生成。 -/
structure FrameWithDecomp extends Frame where
  /-- 嵌入：把干预 `a` 送到外生输入 `u` 中的一个点。 -/
  embed : Act.Carrier → U.Carrier
  /-- 嵌入**不碰撞**：不同的干预对应不同的输入点（可分辨）。 -/
  embed_inj : Function.Injective embed
  /-- 收缩：从外生输入 `u` 中**反读**出干预分量 `a`（可辨识的落点）。 -/
  retract : U.Carrier → Act.Carrier
  /-- 反读正确：先嵌入再反读回到原干预。这是**可辨识性**的核心等式。 -/
  retract_embed : ∀ a, retract (embed a) = a

/-! ### §3.1 读法 B 的直接落点 -/

/-- ⭐ **读法 B 成立（在 `FrameWithDecomp` 下）**：

存在单射 `Act → U`。

**这是「嵌入」层面（可分辨）的分解式**，直接由结构字段给出。 -/
theorem decomp_B_holds (F : FrameWithDecomp) :
    ∃ i : F.Act.Carrier → F.U.Carrier, Function.Injective i :=
  ⟨F.embed, F.embed_inj⟩

/-- ⭐⭐ **读法 B 的完整形式（可辨识分解）**：

存在 `i : Act → U` 与 `r : U → Act` 使得
`i` 单射、`r` 是 `i` 的**左逆**（`∀ a, r (i a) = a`）。

**这是净版「干预是外生输入的**可辨识**分量」在类型层的准确形式**：
`i` 给出分解（`a` 落进 `U`），`r` 给出**辨识**（从 `U` 取回 `a`）。

**⚠ 与「读法 A」的对比**：读法 A 只有 `Act × U` 的投影，
**没有**任何 `U → Act`。本定理的 `r : U → Act` 正是读法 A 所缺的东西。 -/
theorem decomp_B_identifiable (F : FrameWithDecomp) :
    ∃ (i : F.Act.Carrier → F.U.Carrier) (r : F.U.Carrier → F.Act.Carrier),
      Function.Injective i ∧ Function.LeftInverse r i :=
  ⟨F.embed, F.retract, F.embed_inj, F.retract_embed⟩

/-- **分解读出映射的满射性**（可辨识 `⟹` 每个 `a` 都被某个 `u` 达到）。

由于 `retract ∘ embed = id`，`retract` 是满射：
每给定一个 `a`，取 `embed a` 即可。

**意义**：净版的 `a_t` 作为 `U` 的分量**总是被某个 `u` 取到**，
故「`U` 中出现干预 `a`」不是空洞的。 -/
theorem retract_surjective (F : FrameWithDecomp) :
    Function.Surjective F.retract :=
  fun a => ⟨F.embed a, F.retract_embed a⟩

/-! ### §3.2 从 `Frame` 到 `FrameWithDecomp`：何时可升级 -/

/-- **升级判据**：一个 `Frame` 可升级为 `FrameWithDecomp`，**当且仅当**
存在带左逆的单射 `Act → U`。

**两个方向都直接**：
- `→`：从 `FrameWithDecomp` 取出 `embed`、`retract`（并注意其 `toFrame`）；
- `←`：给定 `i`、`r` 与 `r ∘ i = id`，以 `F` 的各字段填 `FrameWithDecomp`。

**这是开放问题 2.2 的可操作答案**：
「分解是否总是存在」等价于「带左逆的单射 `Act → U` 是否总是存在」，
而 §2 已证明后者**不总成立**（`noEmbed_counterFrame`）。
**故原问题的答案是「否，不总是」**——须在实例层面另行论证。 -/
theorem exists_decomp_iff (F : Frame) :
    (∃ G : FrameWithDecomp, G.toFrame = F) ↔
      ∃ (i : F.Act.Carrier → F.U.Carrier) (r : F.U.Carrier → F.Act.Carrier),
        Function.Injective i ∧ Function.LeftInverse r i := by
  constructor
  · rintro ⟨G, rfl⟩
    exact ⟨G.embed, G.retract, G.embed_inj, G.retract_embed⟩
  · rintro ⟨i, r, hi, hr⟩
    refine ⟨{ toFrame := F, embed := i, embed_inj := hi,
              retract := r, retract_embed := hr }, rfl⟩

/-- **反例的强化版**：`noEmbedCounterFrame` **不能**升级为 `FrameWithDecomp`。

**证明**：若它可升级，由 `exists_decomp_iff` 得到带左逆的单射 `Act → U`，
但其 `U = Empty`，任何 `Act → U` 的映射都不存在——与 `noEmbed_counterFrame` 同源矛盾。

**意义**：这**闭合**了否定性论证——
不是「我们暂时没找到嵌入」，而是**该 Frame 结构上不可能有嵌入**。 -/
theorem counterFrame_no_decomp :
    ¬ ∃ G : FrameWithDecomp, G.toFrame = noEmbedCounterFrame := by
  rw [exists_decomp_iff]
  rintro ⟨i, _r, _hi, _hr⟩
  exact (i ()).elim

/-! ===========================================================================
    §4  小结（以定理形式登记状态；不含 `True := trivial` 之类空壳）
    =========================================================================== -/

/-- **状态登记（可证形式）**：把 §1–§3 的三条结论并合为一个合取。

三条内容**各自是非平凡的定理**（分别对应前文）：
1. 读法 A：配对换序双射（`actInput_pair_bijective`）；
2. 读法 B 否定：存在 `Frame` 无嵌入（`noEmbed_counterFrame`）；
3. 读法 B 正向：`FrameWithDecomp` 下可辨识分解成立（`decomp_B_identifiable`）。

**⚠ 本定理不是「开放问题已解决」的声明**：
它只是把三条已证事实打包，便于下游引用与审计。
原问题中「是否**总是**存在」的答案由第 2 条给出（**否**），
「加什么结构才成立」由第 3 条给出（**带左逆的单射**）。
「`a_t` 与 `ũ_t` 取值空间是否独立」**未被本文件回答**（见文件头 (d)）。 -/
theorem open22_status :
    (∀ F : Frame, Function.Bijective (fun p : F.Act.Carrier × F.U.Carrier => (p.2, p.1)))
    ∧ (¬ ∃ i : noEmbedCounterFrame.Act.Carrier → noEmbedCounterFrame.U.Carrier,
          Function.Injective i)
    ∧ (∀ F : FrameWithDecomp,
        ∃ (i : F.Act.Carrier → F.U.Carrier) (r : F.U.Carrier → F.Act.Carrier),
          Function.Injective i ∧ Function.LeftInverse r i) :=
  ⟨actInput_pair_bijective, noEmbed_counterFrame, decomp_B_identifiable⟩

end

end FateV2.Model