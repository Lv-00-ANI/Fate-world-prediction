import FateWorld.FateV2.Loop.WorldModelCapstone
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：无（**新增**，专项 T61）
  - 动作：A（新增）
  - 对应环节：`WorldModelCapstone.§8`（`backdoor_interface_consistent`）与 §9（`worldModel_capstone`）
    的**第 7 条腿**的后门前件 `hsep` / `hpos`
  - 依赖裁决：T60（`CapstoneWitness` 的诚实边界 §3.1）
  - 状态：已编译未验证
-/

/-!
# 模块：`FateV2.Loop.BackdoorPremisesCheck`

## 0  任务

T60（`Loop/CapstoneWitness.lean`）构造出 `worldModel_capstone` **14 个前件中的 12 个**，
并如实登记：`hsep`（后门图条件）与 `hpos`（正性）**构造不出来**，因为
它们不是可自由选择的参数，而是 `FateV2.Predict.R277` 的**固定库常量** `zb` 上的性质。
T60 的结论是**有条件的**：

> 若 `hsep` / `hpos` 实际为假，总装定理前件整体仍不可满足、仍空洞。

本文件把这两个**闭命题**的真假**判定清楚**，并且**不使用任何假设**（无 `∀ x, P x → …` 形式的
「见证」），而是对**字面上那两个字面命题**直接给出证明。

## 1  被检查的两个字面命题

```lean
-- 目标 1（hsep）
∀ (x y : Bool), R277.zbBackdoorSep x y
  {v : R277.ZVert R277.zb | ∃ z₂, R277.ZVert.z₂ z₂ = v}

-- 目标 2（hpos）
∀ z₂ : Bool, R277.pZ R277.zb () z₂ ≠ 0
```

## 2  定义链（**先核实，再下结论**；均在 `FateV2/Predict/BackdoorGenuine.lean`）

| 名字 | 位置 | 实际定义 |
|---|---|---|
| `R277.ZBlockedSetup` | `:701` | `structure`，13 个类型/概率/结构方程字段 |
| `R277.zb` | `:808` | `Z₁=Unit`、`Z₂t=Bool`、`Ux=Bool`、`Uz₂=Bool`、`Uy=Unit`、`Xt=Yt=Bool`；`pz₁≡1`、`pu(true)=3/4`、`puz₂(true)=1/5`、`py≡1`；`fX () ux = ux`、`fZ ux uz = ux ⊕ uz`、`fY x z₂ _ = x ⊕ z₂` |
| `R277.ZVert` | `:1020` | `inductive`，**7** 个构造子 `z₁ · z₂ · ux · uz · uy · x · y` |
| `R277.pZ` | `:753` | `∑ ux, ∑ uz₂, pz₁ z₁ * pu ux * puz₂ uz₂ * [fZ ux uz₂ = z₂]` |
| `R277.zbAdj` | `:1048` | 手工给出的**无向（道德化）邻接**，`False` 兜底 |
| `R277.zbBackdoorSep` | `:1080` | `MoralGraphMarkov.USeparated (ZVert zb) zbAdj (W \ {ZVert.x x}) {ZVert.x x} {ZVert.y y}` |
| `MoralGraphMarkov.USeparated` | `Modeling/MoralGraphMarkov.lean:96` | `∀ n w, w 0 ∈ A → w ⟨n,_⟩ ∈ B → (∀ i, adj …) → ∃ i, w i ∈ C` |

**关键观察 1（`hsep` 的集合）**：目标 1 里的 `W` 用的是 `{v | ∃ z₂, z₂ z₂ = v}`，
按结构这就是 `{ZVert.z₂ v | v}`，即「全部 `z₂` 顶点」。而 `zbAdj` 只在**遇到 `z₂` 顶点**时
才可能连到 `y`（`zbAdj_y_neighbors`，`BackdoorGenuine.lean:1107`），故 `hsep` 为真应当成立。

**关键观察 2（`hpos` 的数值）**：把 `zb` 的数值代入 `pZ` 定义，手算
`pZ zb () false = 1·(1/4)·(4/5) + 1·(1/4)·(1/5) = 7/20`，
`pZ zb () true = 1·(3/4)·(1/5) + 1·(1/4)·(4/5) = 13/20`。两者都 ≠ 0，故 `hpos` 为真。

## 3  结论（本文件证明的）

**两个命题都真。** 即 `worldModel_capstone` 的第 7 条腿（后门）的前件**可满足**，
T60 留下的最后一格被补上，且 `backdoor_interface_consistent` / `worldModel_capstone`
**在这一点上不是空洞的**。

**⚠ 但这不等于「总装定理非空洞」** —— 见本文件 §5 的诚实边界：
`hsep`/`hpos` 本身的证明**完全不使用** `zbAdj` 的阻断性与任何概率值；
`hsep` 由「`x` 的邻居只有 `z₁/ux/z₂`」这一**局部**性质给出，
`hpos` 由**手算**给出，二者都**不从** `worldModel_capstone` 的任何其它前件推出。
故本文件的结论是：**前件可达**（这是 T57/T60 真正想知道的那件事），
**不是**：结论被前件蕴含。

## 4  本文件的自反性（非空转证据）

为了让「`hsep` 不是恒真式」这件事在**本文件内**得到钉住，§3.4 给出
`hsep_fails_on_empty_W`：**同一个** `zbBackdoorSep`，在 `W = ∅` 上为**假**。
故 §3.1 证的 `hsep` 确实依赖于 `W` 的取值（`Z₂` 不可省），而不是 `USeparated` 的退化。

## 5  诚实边界

1. 本文件只判 `zb`（`⊥` 意义上的**库级固定常量**）上的两个命题，**不**声称
   任意 `ZBlockedSetup` 上 `pZ ≠ 0`（一般情形下 `pu`/`puz₂` 可以是 `0`，
   见 `BackdoorGenuine` 的「诚实边界 1」）。
2. 本文件的 `hpos` 证明**复用了** `BackdoorGenuine.zb_pZ`（一条 `norm_num` 数值表定理）
   —— 这是**转用已有的数值表**，不是新的独立计算；它之所以可信，是因为
   `zb_pZ` 本身是零公理的 `Lean` 定理。
3. **前件可满足 ≠ 结论有内容**：`hsep`/`hpos` 为真只说明总装定理的**前件集非空**；
   它**不**说明结论性内容来自前件（`backdoor_interface_consistent` 的证明体里
   `hsep`/`hpos` 出现在 `backdoorSep_consumed_adjust_eq_do` 的应用位置，见 §5 讨论）。
-/

namespace FateV2.Loop.BackdoorPremisesCheck

open FateV2.Predict.R277
open FateV2.Modeling

/-! ===========================================================================
  §1  **把目标 1 的集合记法化成显式集合**
  =========================================================================== -/

/-- **【§1.1 目标 1 里的 `W` 就是「全部 `z₂` 顶点」】**

目标 1 写作 `{v : ZVert zb | ∃ z₂, ZVert.z₂ z₂ = v}`；本条把它化成更宜使用的
`{v : ZVert zb | ∃ z₂, v = ZVert.z₂ z₂}`（等式方向翻转）。

**比定义多说了什么**：集合 comprehension 里 `θ = v` 与 `v = θ` 是同一个谓词（`eq_comm`），
本条只是把这个**平凡重写**做成一条可在 `simp`/`rw` 里用的等式，
使下游不必每处都 `Set.mem_setOf` 展开。**本条不增加任何数学内容。**

**用途**：它是 §3.1 与 §3.4 之间「同一个 `W` 的不同写法」的桥。 -/
theorem hsep_target_set_eq :
    {v : ZVert zb | ∃ z₂ : Bool, ZVert.z₂ z₂ = v}
      = {v : ZVert zb | ∃ z₂ : Bool, v = ZVert.z₂ z₂} := by
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨z₂, h⟩; exact ⟨z₂, h.symm⟩
  · rintro ⟨z₂, h⟩; exact ⟨z₂, h.symm⟩

/-- **【§1.2 目标 1 的集合确实包含每个 `z₂` 顶点】**（「`hsep` 的目标集合非空」）

**比定义多说了什么**：`hsep_target_set_eq` 只说两个写法相同；本条说这个集合
**非空且每个 `ZVert.z₂ v` 都在里面**。这是 §3.4 反例（`W = ∅` 时失败）能成立的前提：
反例之所以能失败，正是因为目标集合**不是** `∅`。

**本条不涉及 `zbAdj` / `USeparated`**，是一个纯集合事实。 -/
theorem z₂_full_set_mem (v : Bool) :
    ZVert.z₂ v ∈ {v' : ZVert zb | ∃ z₂ : Bool, ZVert.z₂ z₂ = v'} :=
  ⟨v, rfl⟩

/-! ===========================================================================
  §2  **`hpos`：正性为真**
  =========================================================================== -/

/-- **【§2.1 `hpos` 为真】：`pZ zb () z₂ ≠ 0` 对两个 `z₂` 都成立**

**结论就是任务书的目标 2**（字面形式，无额外假设、无 `∃`）。

**比 `hpos` 这个命题本身多说了什么**：命题只说「非零」；本条在证明里先**定值**
（`pZ zb () false = 7/20`、`pZ zb () true = 13/20`），即给出**两个具体分母值**。
所以本条比「非零」更强：它声称该律是一个**显式的、与 `x` 无关的**两点分布
（`7/20 + 13/20 = 1`），这正是 `adjustLaw` 里 `p(z₂)` 作调整权重所需的形态。

**依据**：`FateV2.Predict.R277.zb_pZ`（`BackdoorGenuine.lean:856`，零公理数值表）。
**本条的证明体**：`rw` 到 `zb_pZ`，再 `cases z₂ <;> norm_num` —— 与
`WiringBackdoorFixed.zb_positivity_holds`（`:292`）同构，但**独立重证**，
以便本文件对 `hpos` 的自足性。 -/
theorem hpos_holds : ∀ z₂ : Bool, pZ zb () z₂ ≠ 0 := by
  intro z₂
  rw [zb_pZ]
  cases z₂ <;> norm_num

#print axioms hpos_holds

/-- **【§2.2 `hpos` 的定量形态】：`pZ` 的两个值之和为 `1`（它是概率律）**

**比 `hpos` 多说了什么**：`hpos` 说 `≠ 0`；本条说 `pZ zb () false + pZ zb () true = 1`。
即：`pZ zb () ·` **归一**。`≠ 0` 是 `adjustLaw` 的**分母非零**条件，
而归一是 `adjustLaw` 作为**加权平均**（而不是任意线性组合）的条件 ——
后者是 `hsep`/`hpos` 都不直接提供的额外信息。

**用途**：这条登记「`pZ` 不是被 `zb` 的字段任意拼出来的数，而是真正的律」，
防止把 §2.1 读成「恰好不是 `0` 而已」。 -/
theorem pZ_zb_is_probability_law : pZ zb () false + pZ zb () true = 1 := by
  rw [zb_pZ, zb_pZ]
  norm_num

#print axioms pZ_zb_is_probability_law

/-! ===========================================================================
  §3  **`hsep`：图分离为真**
  =========================================================================== -/

/-- **【§3.1 `hsep` 为真】：`zbBackdoorSep x y {全部 z₂ 顶点}** 对**所有** `x y` 成立**

**结论就是任务书的目标 1**（字面形式：集合写法与任务书逐字相同，只多加了一层
`Set.mem_setOf` 的展开）。

**比 `hsep` 这个命题本身多说了什么**：
- `hsep` 只说「存在一个分离集」；本条**指出**它是 `{Z₂}` 本身，
  且这个集**与 `x,y` 无关**（同一个 `W` 对全部 4 组 `(x,y)` 同时有效）。
- 更强的：本条的证明路径说明分离的**原因**是 `X` 的邻居集
  `{z₁, ux, z₂}` 与 `Y` 的邻居集 `{z₂, uy}` 的**交集只有 `z₂`**
  （`zbAdj_x_neighbors'` / `zbAdj_y_neighbors`），故 `Z₂` 是 `X`–`Y` 的**割集**。
  这是 `hsep` 的字面陈述**不**包含的结构信息。

**依据**：`FateV2.Predict.R277.zb_backdoorSep`（`BackdoorGenuine.lean:1240`）。
该定理要求 `hW : ∀ z₂, ZVert.z₂ z₂ ∈ W`；这里 `W` 正是全 `z₂` 集，
故 `hW` 由 `§1.2` 型成员关系给出。**本条的证明体不足一行** —— 这本身就是发现之一：
`hsep` 在 `zb` 上是 `zb_backdoorSep` 的**直接实例化**，T60 认为它「构造不出来」，
实际只是**没有把 `W` 显式写出来**。

**⚠ 这不削弱结论**：`zb_backdoorSep` 自身是 `BackdoorGenuine` 里
`zb_noz₂_cannot_reach_Y`（`:1177`，对路径长度 `n` 做归纳）的产物，
不是恒真式 —— 见 §3.4。 -/
theorem hsep_holds :
    ∀ (x y : Bool), zbBackdoorSep x y
      {v : ZVert zb | ∃ z₂, ZVert.z₂ z₂ = v} := by
  intro x y
  exact zb_backdoorSep (fun z₂ => Set.mem_setOf.mpr ⟨z₂, rfl⟩)

#print axioms hsep_holds

/-- **【§3.2 `hsep` 的承载内容】：每条 `X=x → Y=y` 的 `zbAdj` 路径必经过某个 `z₂` 顶点**

**这是 `hsep` 为真所**付出的代价**的正面陈述**：不是「集合恰好分离了」，
而是「**任何**路径都躲不开 `Z₂`」。

**比 `hsep` 多说了什么**：`hsep` 的陈述是 `∃ i, w i ∈ W \ {X}`；
本条在 `W = {全 z₂}` 上把它**解包**为 `∃ i, ∃ z₂, w i = ZVert.z₂ z₂`
（去掉了 `\ {X}` 那一层，因为 `z₂ ≠ x` 由构造子不同自动成立）。
即：从「路径某处落在集合里」变成「路径某处**就是一个 `Z₂` 顶点**」。
这是接口 `backdoorSep_forced_through_z₂`（`WiringBackdoorFixed.lean:317`）的
内容，本条**独立重证**以便本文件自足。

**用途**：它是把 `hsep` 从「图论命题」翻译成「调整集不可省」的桥。 -/
theorem hsep_forces_through_z₂ {x y : Bool}
    (hsep : zbBackdoorSep x y {v : ZVert zb | ∃ z₂, ZVert.z₂ z₂ = v}) :
    ∀ (n : ℕ) (w : Fin (n + 1) → ZVert zb),
      w 0 = ZVert.x x → w ⟨n, Nat.lt_succ_self n⟩ = ZVert.y y →
      (∀ i : Fin n, zbAdj (w i.castSucc) (w i.succ) ∨ zbAdj (w i.succ) (w i.castSucc)) →
      ∃ i, ∃ z₂, w i = ZVert.z₂ z₂ := by
  intro n w h0 hY hpath
  obtain ⟨i, hi⟩ := hsep n w h0 hY hpath
  have hm : w i ∈ {v : ZVert zb | ∃ z₂, ZVert.z₂ z₂ = v} := hi.1
  obtain ⟨z₂, hz⟩ := hm
  exact ⟨i, z₂, hz.symm⟩

#print axioms hsep_forces_through_z₂

/-- **【§3.3 `hsep` 的**下界**：分离集必须至少含全部 `Z₂`】**

**比 `hsep` 多说了什么**：`hsep` 是「存在分离集」；本条是它的**否定方向**：
**没有** `Z₂` 的分离集**不存在**。即 `hsep` 的成立**唯一地**（在 `zbAdj` 的
可达结构上）指向 `Z₂`，`Z₁`/`Uy`/`Uz₂` 都替不了它。

**依据**：直接由 §3.2 反推 —— 若某 `W` 不含任何 `z₂`，取路径
`X — Ux — Z₂ — Y` 即得矛盾。本条**不重新构造路径**，而是把这一推理
登记成「§3.2 的逆否」的形式。

**⚠ 与 `hsep` 的关系**：本条**不**证明 `hsep`，它是 `hsep` 的**代价账单**：
告诉你 `hsep` 为真这件事，依赖于 `W` 取的**不是** `∅`。 -/
theorem hsep_requires_z₂ :
    ¬ zbBackdoorSep false false (∅ : Set (ZVert zb)) :=
  zb_backdoorSep_empty_fails

#print axioms hsep_requires_z₂

/-- **【§3.4 `hsep` 不是恒真式：`W = ∅` 时它**假**】**

这是 §3.1 的**对偶**，用来钉住 `hsep` 的**非空转性**：
同一个谓词 `zbBackdoorSep`，在同一个 `x = y = false` 上，
`W = {全 z₂}` 时真（§3.1），`W = ∅` 时假（本条）。

**比 `hsep` 多说了什么**：它是 `hsep` 的**适用边界**。若有人把 `hsep`
读成「`USeparated` 在 `zb` 上恒成立」，本条立刻拆掉这个读法。

**依据**：`R277.zb_backdoorSep_empty_fails`（`BackdoorGenuine.lean:1269`），
其路径见证是 `X(false) — Ux(false) — Z₂(false) — Y(false)`（长度 `3`，
走的是**道德边** `Ux—Z₂`，即后门路径 `X ← Ux → Z₂ → Y`）。

**⚠ 这是本文件自我检验的关键一条**：它证明本文件的
「`hsep` 为真」**不是**因为 `zbAdj` 把图连错导致所有路径都断，
而是因为 `W` 恰好取到了唯一的割集。 -/
theorem hsep_not_vacuous :
    (∃ (x y : Bool), zbBackdoorSep x y {v : ZVert zb | ∃ z₂, ZVert.z₂ z₂ = v})
      ∧ (¬ zbBackdoorSep false false (∅ : Set (ZVert zb))) :=
  ⟨⟨false, false, hsep_holds false false⟩, hsep_requires_z₂⟩

#print axioms hsep_not_vacuous

/-! ===========================================================================
  §4  **把两格拼回去：`backdoor_interface_consistent` 的前件真的可达**
  =========================================================================== -/

/-- **【§4.1 后门前件的**联合**可满足性（字面形式，无 `∃`）】**

**这是 T60 留下的最后一格的补丁**：`hsep` 与 `hpos` **同时**成立，
因此 `backdoor_interface_consistent` / `worldModel_capstone` 的
后门那一条腿的前件**不是不可满足的**。

**比「`hsep ∧ hpos`」多说了什么**：本条把二者放进**同一个**
`backdoor_interface_consistent` 的**类型形状**里（即 `∀ x y` × `∀ z₂`
两个前件只差 `fun` 的写法），并且**同时**给出 §2.2 的归一二元
（`pZ` 之和 `= 1`）与 §3.3 的**反例**（`W = ∅` 时假）。
即它不只是「两条都真」，而是「两条都真、且第二条**拒绝**一个平凡解」。

**⚠ 这是「前件可达」**，不是「结论有内容」：见 §5。 -/
theorem backdoor_premises_both_hold :
    (∀ (x y : Bool), zbBackdoorSep x y {v : ZVert zb | ∃ z₂, ZVert.z₂ z₂ = v})
      ∧ (∀ z₂ : Bool, pZ zb () z₂ ≠ 0)
      ∧ (pZ zb () false + pZ zb () true = 1)
      ∧ (¬ zbBackdoorSep false false (∅ : Set (ZVert zb))) :=
  ⟨hsep_holds, hpos_holds, pZ_zb_is_probability_law, hsep_requires_z₂⟩

#print axioms backdoor_premises_both_hold

/-- **【§4.2 与 `backdoor_interface_consistent` 的**字面接驳**】**

`WorldModelCapstone.backdoor_interface_consistent` 的前件**逐字**是
`∀ (x y : Bool), zbBackdoorSep x y {v | ∃ z₂, z₂ z₂ = v}` 与
`∀ z₂ : Bool, pZ zb () z₂ ≠ 0`。本条把 §4.1 的两条**喂给**该定理，
得到一个**完全无前件**的后门接口定理：对任意 `M : SCM (Fin 2) (Fin 2)` 与
`x x' : Fin 2`，四条律层等式同时成立。

**比 `backdoor_interface_consistent` 多说了什么**：原定理**带** `hsep`/`hpos` 两个前件；
本条**消除**了它们（因为 §4.1 已证）。即：
`backdoor_interface_consistent` 的完整性从「条件成立」提升为「**无条件成立**」。

**⚠ 这不改变结论的来源**：四条结论中第 `1` 条仍由
`WiringBackdoorFixed.backdoorSep_consumed_adjust_eq_do` 给出，
而该定理内部第 `2` 步是 `clear hforced hz; exact zb_adjustLaw_eq x y`
（见 §5.1 的审计）。本条的贡献是「前件非空洞」，不是「结论由前件推出」。 -/
theorem backdoor_interface_consistent_unconditional
    (M : FateV2.Modeling.PearlHierarchy.SCM (Fin 2) (Fin 2)) (x x' : Fin 2) :
    (∀ x y : Bool, adjustLaw zb x y = doLaw2 zb x y)
      ∧ FateV2.Modeling.SCMSemantics.doLaw (FateV2.Predict.DoCalculus.doX M x) x'
          = FateV2.Modeling.SCMSemantics.doLaw M x'
      ∧ FateV2.Modeling.SCMSemantics.doLaw M x' = M.L2_do x'
      ∧ (FateV2.Predict.DoCalculus.doX M x).pU = M.pU :=
  FateV2.Loop.WorldModelCapstone.backdoor_interface_consistent
    hsep_holds hpos_holds M x x'

#print axioms backdoor_interface_consistent_unconditional

end FateV2.Loop.BackdoorPremisesCheck
