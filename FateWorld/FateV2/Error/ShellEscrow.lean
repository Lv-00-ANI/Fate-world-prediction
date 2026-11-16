/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.Stage2.ShellEscrow`
审计编号：R123（「合法空壳」豁免登记）
性质：**登记模块**，不含任何数学内定理。

---------------------------------------------------------------------------
本模块要解决的问题（一句话）
---------------------------------------------------------------------------
`Fate/Stage2/ErrorQuadruple.lean` 用 `def E1Statement … : Prop := <不等式>`
把 8 条未证断言**冻结成定义**。这**绕开了**「零 `sorry`」的字面约束：

- 它**不是**假交付（没有 `sorry`，编译器也没被骗）；
- 但若这个模式被推广成「所有未证断言都写成 `def … : Prop`」，
  则「零 `sorry`」将变成**空洞的**指标——库里满是 `def` 形式的未证断言，
  而 `sorry` 计数为零。

本模块因此把「这 8 条是**未证断言**」这一事实变成**可被编译器核对**的常量，
使「不得被下游当作已证前提使用」这条纪律**不依赖人的记忆**。

---------------------------------------------------------------------------
本模块**不**做什么（界限要先说清）
---------------------------------------------------------------------------
- **不**修改 `ErrorQuadruple.lean`（一字符都不改；本模块只 import 它）。
- **不**证明 E1–E8 中任何一个（那需要真正的数学工作，且 E8 依赖未定义的 A32）。
- **不**声明任何 `axiom` / `sorry` / `admit`。
- **不**把 `E1Statement …` 从库里删掉（它是形式冻结，有独立价值）。

本模块做的唯一一件事：**给「空壳」贴上机器可读的标签。**
-/

import FateWorld.FateV2.Error.ErrorQuadruple
namespace FateV2.Error.Stage2.Escrow

open FateV2.Error.Stage2

/-!
  # Error · ShellEscrow

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ShellEscrow.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Stage2.ErrorQuadruple
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1 空壳的分类

审计需要一个**精确**的分类，否则「空壳」会变成辱骂性词汇而不是技术术语。
本模块把 `ErrorQuadruple.lean` 中的 `def` 按**是否存在数学内容**分为三类：

| 类 | 定义 | 是否算「空壳」 |
|---|---|---|
| `A 型：未证断言` | 定义体是**不等式/断言**，与理论原文的 `[待证]` 条目一一对应 | ⭐ **是**。它写着「某事成立」，但没证 |
| `B 型：元登记` | 定义体是 `True`，文档承担内容，类型只是载体（`E8_A32_undefined`、`Stage2FormsFrozen`） | 否（但见 §3 的警告） |
| `C 型：真定义` | 定义体是**真定义**（如 `L_Pi_of` 的乘积、`E5_dimension` 的量纲标签、`allE` 的清单） | 否 |

⭐ **只有 A 型需要登记**。本模块的 `EscrowItem` 枚举**恰好**是这 8 条 A 型。
这一点本身是可核对的：见 `escrowItems_length` 与 `escrowItems_nodup`。
-/

/-- **A 型空壳：8 条未证断言**的枚举（与 `ErrorQuadruple.lean` 的 §2 一一对应）。

⚠ **`E1`–`E8` 的命名与 `ErrorQuadruple.EItem` 一致**，二者通过
`EscrowItem.toEItem` 显式关联——这不是装饰：它使「登记表」与
「`ErrorQuadruple` 的编号表」**不可能失同步**（缺一个就编译失败，
见 `escrowItems_covers_allE`）。 -/
inductive EscrowItem where
  /-- 未证断言：数学近似（Euler 全局误差的 `exp` 形界）。 -/
  | E1
  /-- 未证断言：统计估计（泛化界，点态形态）。 -/
  | E2
  /-- 未证断言：模型误差分解界。 -/
  | E3
  /-- 未证断言：结构误差界。 -/
  | E4
  /-- 未证断言：分布偏移风险差界。 -/
  | E5
  /-- 未证断言：浮点迭代收敛界。 -/
  | E6
  /-- 未证断言：反事实误差双部界。 -/
  | E7
  /-- 未证断言：FCA 编码纤维直径界（**另**依赖未定义的 A32）。 -/
  | E8
  deriving DecidableEq, Repr

/-- `EscrowItem → ErrorQuadruple.EItem`：把登记项映到编号表。

⭐ 这个映射存在的唯一理由是**防失同步**：
`ErrorQuadruple.lean` 若日后增删 `EItem` 的构造子，
本文件的 `escrowItems_covers_allE` 会**编译失败**，从而强迫维护者更新登记表。 -/
def EscrowItem.toEItem : EscrowItem → EItem
  | .E1 => .E1
  | .E2 => .E2
  | .E3 => .E3
  | .E4 => .E4
  | .E5 => .E5
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8

/-- 全部 8 条 A 型空壳的清单。 -/
def escrowItems : List EscrowItem :=
  [.E1, .E2, .E3, .E4, .E5, .E6, .E7, .E8]

/-- ⭐ **机械核对：登记表恰好 8 条**（不是「声称」，是编译器证明）。 -/
theorem escrowItems_length : escrowItems.length = 8 := rfl

/-- ⭐ **机械核对：8 条两两不同**（无重复登记、无重复豁免）。 -/
theorem escrowItems_nodup : escrowItems.Nodup := by decide

/-- ⭐⭐ **机械核对：登记表与 `ErrorQuadruple.EItem` **完全一致**。

左：登记表的 8 条，经 `toEItem` 映射后；
右：`ErrorQuadruple` 的 `allE` 清单（其长度由 `allE_length` 证明为 8）。

本引理使「本登记表覆盖了 `ErrorQuadruple` 的每一条 E」是**编译器证明的事实**，
而不是文档里的一句承诺。 -/
theorem escrowItems_covers_allE :
    escrowItems.map EscrowItem.toEItem = allE := rfl

/-- 推论：每一条 `EItem` 都被登记表覆盖（反面核验：不存在「漏登记」的空壳）。 -/
theorem escrow_covers_every_eitem :
    ∀ e : EItem, ∃ i : EscrowItem, EscrowItem.toEItem i = e := by
  intro e
  have hmem : e ∈ allE := allE_complete e
  rw [← escrowItems_covers_allE] at hmem
  obtain ⟨i, _, hi⟩ := List.mem_map.mp hmem
  exact ⟨i, hi⟩

/-! ## §2 「未证」的机器可读标签

上面的枚举只登记了**编号**。审计还需要能回答「这条**是不是**已证」。
本模块给出一个 `Proved : EscrowItem → Bool`，**全部取 `false`**，
并**以一条定理钉住**这个事实。

⚠ **为什么用 `Bool` 而不是 `Prop`**：`Prop` 版本的「未证」无法表达
（Lean 里没有「命题 P 未被证明」这种类型——那是元语言事实）。
`Bool` 版本是**登记**，不是数学事实；它的价值是让下游代码能**查询**
（`if Proved .E3 then … else …`），并在有人偷偷改成 `true` 时**留下 diff**。

⚠ **这是登记，不是保证**：一个恶意的 agent 可以把 `Proved` 改成全 `true`
而不改任何定理。本模块**不能**防止这个——防止它需要评审（git diff + 本模块头部）。
本模块能做的是：**让这个改动变成一行刺眼的 diff**，而不是无声的。
这一局限显式登记于此，不冒充「本机构已解决该问题」。 -/
def Proved : EscrowItem → Bool
  | .E1 => false
  | .E2 => false
  | .E3 => false
  | .E4 => false
  | .E5 => false
  | .E6 => false
  | .E7 => false
  | .E8 => false

/-- ⭐ **钉住：8 条全部未证**（一一列举，使任何一条被改成 `true` 都会使本定理失败）。 -/
theorem all_unproved :
    Proved .E1 = false ∧ Proved .E2 = false ∧ Proved .E3 = false ∧ Proved .E4 = false
    ∧ Proved .E5 = false ∧ Proved .E6 = false ∧ Proved .E7 = false ∧ Proved .E8 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 推论：登记表中**不存在**已证项。 -/
theorem no_proved_in_escrow : ∀ i ∈ escrowItems, Proved i = false := by
  intro i hi
  match i with
  | .E1 => rfl
  | .E2 => rfl
  | .E3 => rfl
  | .E4 => rfl
  | .E5 => rfl
  | .E6 => rfl
  | .E7 => rfl
  | .E8 => rfl

/-! ## §3 「不得当作已证前提使用」的登记

审计的核心纪律是：**这 8 条不得被下游当作已证前提使用**。
本模块把这个纪律变成**可检索的常量**（同 `E8_A32_undefined` 的手法）。

⚠ **诚实的界限**：Lean 的**类型系统不阻止**下游写
`(h : E1Statement X M L T h x_n x_T)` 然后从 `h` 推出结论——
那在逻辑上**完全合法**（假设-蕴含是合法的推理形式）。
本模块**不能**在类型层禁止这件事。它能做的是：

1. 让纪律**有名可查**（`EscrowNotice`）；
2. 在 `ESCROW-空壳登记.md` 里写明「若下游这样做，该下游定理的结论
   **不是**该空壳的证明，而是「假设它成立」的条件命题」——
   这在**语义**上把责任转移给下游的读者；
3. 提供 `escrowed_premise_is_conditional` 作为**样板**：
   它演示「用空壳做前提」时，定理的正确读法是**条件命题**，
   不是无条件结论。

这一点是本模块**最重要的诚实声明**：零 `sorry` **不等于**零未证断言。
-/

/-- **纪律常量**：空壳的前提使用规则（内容在文档，`True` 只是载体）。

检索方式：`grep -rn "EscrowNotice" Fate/`。 -/
def EscrowNotice : Prop := True

/-- `EscrowNotice` 的平凡证明（不引入任何新假设）。 -/
theorem EscrowNotice_true : EscrowNotice := trivial

/-- ⭐⭐ **样板：用空壳做前提时，定理的正确形态是「条件命题」**。

本引理**演示**（不是证明 E4）：
给定 `g 0 = 0` 且 `g` 在 `0` 处连续，对每个 `ε > 0`，存在 `δ > 0`，使**对任意** `dGG0`，
只要 `|dGG0| < δ`（图距足够小）且**假设** `E4Statement P_G P_G0 g dGG0` 成立，
就有 `|P_G - P_G0| < ε`。

⚠ **本引理不证明 E4**。它的前提里带有 `E4Statement …`——
**去掉这个前提，本引理不成立**（`|P_G - P_G0|` 与 `g` 之间无任何联系）。
这正是「空壳不得当作已证前提」的精确含义：
你**可以**用它做前提，但你得到的是**条件命题**，
其条件（E4 本身的成立）**没有被本库证明**。

⚠ **本引理不是同义反复**（不是自定义前件包住结论）：
- 前件 `hE4` 是 E4 的**点态界**（`|P_G-P_G0| ≤ g dGG0`，`dGG0` 是一个**自由变元**的实例值）；
- 结论是「对每个 `ε > 0`，存在 `δ`，使得**当 `dGG0` 趋近 0 时**误差 `|P_G-P_G0|` 被压到 `ε` 以下」——
  这是一个带 `ε`/`δ` 与全称量词的**收敛结构**，`hE4` 里没有任何量词出现。
- 二者的连接是**真正的推理**：连续性给出 `|g dGG0| < ε`（当 `|dGG0| < δ`），
  此时由 `hE4` 的 `|P_G-P_G0| ≤ g dGG0 ≤ |g dGG0| < ε` 传递而得。
  这一步传递不可省：若没有 `hE4`，无论 `dGG0` 多小，`|P_G-P_G0|` 都**与 `g` 无关**。
- 反向也不成立：由本引理的结论**推不出** `E4Statement` 本身
  （结论只说「误差最终小」，不说「被 `g dGG0` 这个特定函数控制」）。

⭐ 本引理的**真正价值**在于它是**可被审计的样板**：
任何想用空壳的下游，都必须写出**同等强度**的条件命题——
即必须**显式**把空壳放进假设栏，从而使「这一条是假设的，不是证的」
在**签名里**可见，而不是在正文里被忘记。 -/
theorem escrowed_premise_is_conditional
    (P_G P_G0 : ℝ) (g : ℝ → ℝ)
    (hg0 : g 0 = 0) (hg : ContinuousAt g 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ dGG0 : ℝ, |dGG0| < δ →
      E4Statement P_G P_G0 g dGG0 → |P_G - P_G0| < ε := by
  intro ε hε
  -- 连续性窗口：`|dGG0| < δ` ⇒ `|g dGG0| < ε`
  obtain ⟨δ, hδ0, hδ⟩ := bound_vanishes_at_zero g hg0 hg ε hε
  refine ⟨δ, hδ0, fun dGG0 hd hE4 => ?_⟩
  -- `hE4`：误差被 `g dGG0` 控制（点态，`dGG0` 已固定）
  have hle : |P_G - P_G0| ≤ g dGG0 := hE4
  have hgt : |g dGG0| < ε := hδ dGG0 hd
  linarith [le_abs_self (g dGG0)]

/-! ## §4 汇总登记 -/

/-- `[元登记]` **R123 的执行结果**：8 条 A 型空壳已登记为「未证断言」。

本常量使审计结论**可被检索**：`grep -rn "ShellEscrowRegistered" Fate/`。 -/
def ShellEscrowRegistered : Prop := True

/-- `ShellEscrowRegistered` 的平凡证明（不引入任何新假设）。 -/
theorem ShellEscrowRegistered_true : ShellEscrowRegistered := trivial

end FateV2.Error.Stage2.Escrow

/-! ## 接口自检 -/

#check @FateV2.Error.Stage2.Escrow.EscrowItem
#check @FateV2.Error.Stage2.Escrow.escrowItems
#check @FateV2.Error.Stage2.Escrow.escrowItems_length
#check @FateV2.Error.Stage2.Escrow.escrowItems_nodup
#check @FateV2.Error.Stage2.Escrow.escrowItems_covers_allE
#check @FateV2.Error.Stage2.Escrow.escrow_covers_every_eitem
#check @FateV2.Error.Stage2.Escrow.Proved
#check @FateV2.Error.Stage2.Escrow.all_unproved
#check @FateV2.Error.Stage2.Escrow.no_proved_in_escrow
#check @FateV2.Error.Stage2.Escrow.EscrowNotice
#check @FateV2.Error.Stage2.Escrow.escrowed_premise_is_conditional
#check @FateV2.Error.Stage2.Escrow.ShellEscrowRegistered

/-! ## 公理自检（预期：无 `sorryAx`） -/

#print axioms FateV2.Error.Stage2.Escrow.escrowItems_covers_allE
#print axioms FateV2.Error.Stage2.Escrow.escrow_covers_every_eitem
#print axioms FateV2.Error.Stage2.Escrow.all_unproved
#print axioms FateV2.Error.Stage2.Escrow.no_proved_in_escrow
#print axioms FateV2.Error.Stage2.Escrow.escrowed_premise_is_conditional
#print axioms FateV2.Error.Stage2.Escrow.ShellEscrowRegistered_true
#print axioms FateV2.Error.Stage2.Escrow.EscrowNotice_true
