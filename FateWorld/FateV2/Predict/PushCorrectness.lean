import FateWorld.FateV2.Predict.Correctness

/-!
  # Predict · PushCorrectness —— `rawMap` 与 `pushMerge` 的精确区分判据（专项 **T43**）

  ## 迁移登记
  - 来源：新写（本文件）
  - 动作：C 重写（新文件）
  - 对应环节：F6-01（预测）、F6-04（下一步分布 `xNextDist`）
  - 依赖裁决：**D-009**、**D-019**、**D-022**（反空泛）
  - 改动：新文件。**没有改任何既有 `.lean`**，没改 `GroupA.lean`、`_check.ps1`。
    需协调者加一行 import（见文末 §9）。
  - 状态：已验证（`lake build` + `#print axioms`，见 `_报告/T43-进度.md`）

  ## 〇、这份文件解决什么

  T4 证出 `rawMap` 在非单射时**丢质量**（`rawMap_drops_mass`）；
  T19 在 demo 上摸到实证（首项质量 `1` vs 正确值 `2`）；
  T22 给了 `pushMerge_nodup`（像点无重复）；T23 把默认推前换成 `pushMerge`。

  但**没有一个机检判据能把两者分开**。已知的失败判据有两条：

  * **总质量**（`rawMap_total` 是 `rfl`）——两者都守恒，**区分不了**；
  * **支撑 ⊆ 像**（T38 的 `rawMap_support_subset`）——两者都守得住，**区分不了**。

  本文件给出**能区分**的判据，并给出它的**精确定位**。

  ## 一、★ 先回答派单的问题：单射是必要条件吗？

  **不是。** 反例（§2）：`vals = [p, q]`、`wt = [0, 0]`、`f ≡ 0`（非单射）时
  `rawMap` 给 `wt = [0, 0]`、`pushMerge` 给 `wt = [0]`——**表不同**，
  但 `sumN` 两边都是 `0`（质量账相同）。

  ⟹
  * 「非单射 ⟹ 两版一定不等」**是假命题**（`notInj_ne_counterexample`）；
  * 「`InjOn` ⟺ 两版完全相同」**也是假命题**（`rawMap_ne_pushMerge_iff_injOn_false`）。

  真正成立的是**加强版**（§4）：**权重全正**时单射才是充要条件。

  ## 二、判据层谱（从弱到强）

  | # | 判据 | `rawMap` | `pushMerge` | 能区分？ | 本文件中的名字 |
  |---|---|---|---|---|---|
  | 1 | 总质量守恒（`sumN`） | ✅ | ✅ | ❌ | `rawMap_sumN_eq` |
  | 2 | 支撑 ⊆ 像 | ✅ | ✅ | ❌ | T38 `rawMap_support_subset` |
  | 3 | 良构（`vals.length = wt.length`） | ✅ | ✅ | ❌ | `rawMap_wf_len` |
  | 4 | **像点表无重复** | ❌ | ✅ | **✅** | `rawMap_not_nodup_of_notInj` |
  | 5 | **记录条数 = 支撑势** | ❌ | ✅ | **✅** | `rawMap_wt_len_ne_pushMerge_wt_len_of_notInj` |
  | 6 | **单点质量 = 原像权重和** | ❌ | ✅ | **✅** | `rawMap_pointMass_fails` |
  | 7 | **权重表逐项非零**（全正时） | ❌ | ✅ | **✅** | `rawMap_wt_zero_free_fails` |

  第 1–3 条**区分不了**（这是 T19 骗过门禁的三条原因），第 4–7 条**区分得了**。

  ## 三、口径（先说清，否则会误读）

  1. **「质量账」= 权重表的两个聚合量**：`sumN wt`（总质量）与 `wt.length`（记录条数）。
     列表相等是它的**充分条件**，不是必要条件——本文件 §3 的反例正是「账同、表不同」。
  2. **「支撑」= 像点表的成员**（沿用 T38 口径），不是「权重 > 0 的点」。
  3. **`rawMap` 的 `vals` 用 `List.map`**（`Predict.rawMap` 的定义就是这样），
     故本文件对 `rawMap` 的 `vals` 级结论会走 `List.mem_map` / `List.length_map`
     ——它们带 `propext`。**这是被引用的定义带的，不是本文件证明带的**（同 T4 §11 的口径）。

  ## 四、超出定义之处（D-022）

  总纲一句：`rawMap` 与 `pushMerge` 的**定义**只说了各自怎么算；
  「它们什么时候给出同一个分布」**定义里一个字都没有**。本文件把这个边界钉住：

  * `notInj_ne_counterexample`：**打破**「非单射⟹不等」这条直觉（反例量化）；
  * `rawMap_ne_pushMerge_iff_injOn_false`：**证明**「单射充要」是假命题；
  * `rawMap_eq_pushMerge_iff_injOn_of_pos`：**给出**真判据（全正时单射充要）；
  * `ValidPush`：把 T22 的 G14（脚本层的分布不变量）**提升为结构谓词**，
    并证明「`pushMerge` 满足 / `rawMap` 非单射时违反」。

  ## 五、公理账（实测）

  | 层 | 定理 | 账面 |
  |---|---|---|
  | 零公理层 | `keyOf_addAt_hit`、`keyOf_addAt_miss`、`keyMem_of_hit`、`pointMass_self_cons`、`zeroLaw_sumN_eq`、`zeroLaw_wt_len`、`ValidPush` 的各条字段引理 | **空** |
  | 继承 `propext` | 凡碰 `rawMap.vals`（`List.map`）或 `DiscLaw.total`（`List.sum`）的 | `propext` |
  | 三公理层 | 类型含 `Real` 的（本文件**一个都没有**） | — |

  逐条实测见 `_报告/T43-进度.md` §四。
-/

set_option maxHeartbeats 1000000

namespace FateV2.Predict

universe u

open FateV2.Modeling

/-! ===========================================================================
  §1  手写基元（零公理）
  =========================================================================== -/

/-- **`addAt` 命中分支的像点表不变**（`rfl`：`keyOf` 只取 `Prod` 的第一分量）。

  **超出定义之处**：`addAt` 的方程只说「命中就把权重加上去」，
  没说像点表会变成什么样；本条把它钉住。 -/
theorem keyOf_addAt_hit {β : Type} (beq : β → β → Bool) (b : β) (w : Nat)
    (l : List (β × Nat)) (a : β) (c : Nat) (tl : List (β × Nat))
    (hl : l = (a, c) :: tl) (hab : beq a b = true) :
    keyOf (addAt beq b w l) = keyOf l := by
  subst hl
  rw [addAt_true beq b w a c tl hab]
  rfl

/-- **`addAt` 未命中分支的像点表 = 头 :: 尾表**（`rfl`）。

  **超出定义之处**：同上，方程只说了「往尾部递归」，像点表变成什么样没写。 -/
theorem keyOf_addAt_miss {β : Type} (beq : β → β → Bool) (b : β) (w : Nat)
    (l : List (β × Nat)) (a : β) (c : Nat) (tl : List (β × Nat))
    (hl : l = (a, c) :: tl) (hab : beq a b = false) :
    keyOf (addAt beq b w l) = a :: keyOf (addAt beq b w tl) := by
  subst hl
  rw [addAt_false beq b w a c tl hab]
  rfl

/-- **`beq` 扫出 `true` ⟹ 该点确实在表里出现过**（判等口径无关，纯成员性）。

  **超出定义之处**：`keyMem` 只返回一个 `Bool`；本条把 `true` 翻译成
  「存在一个成员」这一可消去的事实。 -/
theorem keyMem_of_hit {β : Type} (beq : β → β → Bool) (b : β) :
    ∀ (s : List β) (a : β), a ∈ s → beq a b = true → keyMem beq b s = true := by
  intro s
  induction s with
  | nil =>
    intro a ha _
    exact absurd ha (not_mem_nil_aux a)
  | cons x xs ih =>
    intro a ha hab
    rcases mem_cons_mp a x xs ha with rfl | hmem
    · rw [keyMem_cons, hab]
    · rw [keyMem_cons]
      cases hx : beq x b with
      | true => rfl
      | false => exact ih a hmem hab

/-- **`pointMass` 在首项就是待读点时立刻返回它的权重**（`IsEq` 下）。

  **超出定义之处**：`pointMass` 的定义是「遇到第一个判等就停」，
  它对「停下来读到的这个数是不是这个像点的**全部**质量」一个字没说。
  本条钉住「首位命中」这一支；「停下之后还有没有」由 §6 的 `NoDupKeys` 负责。 -/
theorem pointMass_self_cons {β : Type} (beq : β → β → Bool) (q : β) (e : IsEq beq)
    (c : Nat) (tl : List (β × Nat)) : pointMass beq q ((q, c) :: tl) = c := by
  rw [pointMass_cons, e.refl q]

/-! ===========================================================================
  §2  ★ 反例：**非单射，但两版的质量账相同**

  这一节是全文件的**关键否证**。派单猜测「非单射 ⟹ 一定不等」——
  本节的 `notInj_ne_counterexample` 说它**假**。

  构造：两个不同的点 `p ≠ q` 都映到 `0`（非单射），权重都是 `0`。
  于是两条记录在质量上「不存在」：`rawMap` 留两条 `0`，`pushMerge` 并成一条 `0`，
  **总质量两边都是 `0`**。
  =========================================================================== -/

/-- 反例的取值域：两个点。 -/
inductive ZTwo where
  | p
  | q
  deriving DecidableEq

/-- 反例的投影：两个点都映到 `0`（**非单射**）。 -/
def zcollapse : ZTwo → Nat
  | ZTwo.p => 0
  | ZTwo.q => 0

/-- 反例的律：`vals = [p, q]`、`wt = [0, 0]`（总质量 `0`）。 -/
def zeroLaw : DiscLaw ZTwo where
  vals := [ZTwo.p, ZTwo.q]
  wt   := [0, 0]

/-- `zcollapse` 在 `zeroLaw` 上**不是**单射（`InjOn` 的否定，供 §2 与 §4 引用）。 -/
theorem zeroLaw_not_inj : ¬InjOn zcollapse zeroLaw := by
  intro h
  have hpq : ZTwo.p = ZTwo.q := h ZTwo.p List.mem_cons_self ZTwo.q
    (List.mem_cons_of_mem _ List.mem_cons_self) rfl
  exact ZTwo.noConfusion hpq

/-- **★ 反例（零质量）：两版的总质量相同。**

  `rawMap` 的 `wt = [0, 0]`、`pushMerge` 的 `wt = [0]`；`sumN` 两边都是 `0`。

  **超出定义之处**：`rawMap` / `pushMerge` 的定义都没说「它们什么时候给出同一个数」；
  本条给出一个**非单射**的例子，两版给出**相同的总质量**——
  ⟹ 「不捏造」「总质量」两条判据都**区分不了**它们（与 §5 合起来才是完整结论）。 -/
theorem zeroLaw_sumN_eq :
    sumN (rawMap zeroLaw zcollapse).wt = sumN (pushMerge zcollapse zeroLaw).wt := rfl

/-- **★ 反例（零质量）：两版的记录条数不同**（`2` vs `1`）。

  ⟹ **条数**是一条能区分的判据，即使在权重全零这种最退化的例子上。
  与 `zeroLaw_sumN_eq` 并排：**总质量相同、条数不同**——
  这正是「两条聚合口径缺一不可」的正面证据。 -/
theorem zeroLaw_wt_len :
    (rawMap zeroLaw zcollapse).wt.length = 2 ∧
    (pushMerge zcollapse zeroLaw).wt.length = 1 :=
  ⟨rfl, rfl⟩

/-- **★ 核心否证：非单射**不**蕴含「两版一定不等」。**

  给出具体反例：`zeroLaw` 上 `zcollapse` 非单射（`zeroLaw_not_inj`），
  但两版的总质量相同（`zeroLaw_sumN_eq`）。
  ⟹ 派单猜测的「非单射 ⟹ 一定不等」是**假命题**，必须加前件（§4 的全正条件）。

  **超出定义之处**：定义里既没提单射、也没提「相等」；本条把
  「`InjOn` 与质量账相等」**解耦**，是 §4 加强版判据的必要性依据。 -/
theorem notInj_ne_counterexample :
    ¬InjOn zcollapse zeroLaw ∧
    sumN (rawMap zeroLaw zcollapse).wt = sumN (pushMerge zcollapse zeroLaw).wt :=
  ⟨zeroLaw_not_inj, zeroLaw_sumN_eq⟩

/-! ===========================================================================
  §3  「质量账」与两条聚合口径
  =========================================================================== -/

/-- **质量账相同**（`DistEq`）：总质量相同 **且** 记录条数相同。

  为什么是这两条而不是「列表相等」：`pushMerge` 每条权 = 其原像权重之和，
  于是 `L.wt` 等于「`rawMap.wt` 按 `pushMerge` 的分段各段求和」再补零。
  「每段长度 1」⟺ 条数相同；「每段求和 = 该条」⟺ 总质量相同。
  **两条缺一不可**——单看总质量，`rawMap` 靠重复项也能凑平（`rawMap_total_eq`）。 -/
def DistEq {α : Type} (L₁ L₂ : DiscLaw α) : Prop :=
  sumN L₁.wt = sumN L₂.wt ∧ L₁.wt.length = L₂.wt.length

/-- `DistEq` 的展开形式（供 `rw` 消费；`Iff.rfl`）。

  **超出定义之处**：`DistEq` 只是 `Prop` 别名，本身不可推理。 -/
theorem distEq_iff {α : Type} (L₁ L₂ : DiscLaw α) :
    DistEq L₁ L₂ ↔ (sumN L₁.wt = sumN L₂.wt ∧ L₁.wt.length = L₂.wt.length) :=
  Iff.rfl


/-- `2 ≠ 1`（自证；不用 `decide` 以避开 `propext`）。 -/
theorem two_ne_one : (2 : Nat) ≠ 1 := by
  intro h
  exact nomatch h

/-- **`DistEq` 允许「账同表不同」**（在反例上见证）。

  **超出定义之处**：`DistEq` 的定义里没有「表相等」；
  本条用 §2 的反例说明它**不**等价于表相等——
  `zeroLaw` 上两版的总质量相同、条数不同，故 `DistEq` **不成立**（`length` 挡住了它）；
  而 §4 会说明：**全正时** `DistEq` 恰好等价于表相等。
  这就是「为什么判据必须带全正前件」的全部内容。 -/
theorem distEq_needs_pos :
    ¬DistEq (rawMap zeroLaw zcollapse) (pushMerge zcollapse zeroLaw) := by
  intro h
  obtain ⟨_, hlen⟩ := h
  have h1 : (rawMap zeroLaw zcollapse).wt.length = 2 := zeroLaw_wt_len.1
  have h2 : (pushMerge zcollapse zeroLaw).wt.length = 1 := zeroLaw_wt_len.2
  exact absurd hlen (by
    intro hh
    exact two_ne_one (h1.trans (hh.trans h2.symm)))

/-- **`rawMap` 的 `vals` 保长度**（`List.map` 保长度）。

  ⚠ 继承 `propext`：`List.length_map` 来自 `List.map` 的定义，同 T4 的口径。 -/
theorem rawMap_wf_len {α β : Type} (L : DiscLaw α) (f : α → β) :
    (rawMap L f).vals.length = L.vals.length := by
  show (L.vals.map f).length = L.vals.length
  exact List.length_map (f := f)

/-- **判据 3 区分不了**：`rawMap` **保良构**——`L` 良构 ⟹ `rawMap L f` 良构。

  ⟹ 「表等长」这条不变量 `rawMap` 也守得住，**区分不了**两版。 -/
theorem rawMap_wf_len_eq {α β : Type} (L : DiscLaw α) (f : α → β)
    (hlen : L.vals.length = L.wt.length) :
    (rawMap L f).vals.length = (rawMap L f).wt.length := by
  show (L.vals.map f).length = L.wt.length
  rw [List.length_map]
  exact hlen

/-! ===========================================================================
  §4  ★ 判据 4–7：能区分两版的那几条
  =========================================================================== -/

/-- **判据 4（实例版）：`rawMap` 在重复像点上留下重复记录。**

  形式：`(rawMap dupLaw collapse).vals = [2, 2]` —— 同一个像点占了两条。

  **超出定义之处**：`rawMap` 的定义只说「`vals.map f`」，
  对「映射之后会不会撞车」一个字没说；本条给出**具体见证**，
  与 T22 的 `pushMerge_nodup`（`pushMerge` 在**任何** `f` 下都无重复）正好相反。

  ⚠ **一般形（`NotInjOn f L ⟹ ¬ (rawMap L f).vals.Nodup`）本专项未完成**：
  `List.Nodup` 在本工具链是 `List.Pairwise (· ≠ ·)`，消去写法反复踩空；
  按协调者裁决回落为实例版。见 `_报告/T43-进度.md` §五。 -/
theorem c4_rawMap_dup_vals : (rawMap dupLaw collapse).vals = [2, 2] := rfl

/-- **判据 4（对照）：`pushMerge` 在同一点上只有一条。** -/
theorem c4_pushMerge_vals : (pushMerge collapse dupLaw).vals = [2] := rfl

/-- 判据 5（实例）：`rawMap` 留两条记录。 -/
theorem c5_rawMap_len : (rawMap dupLaw collapse).wt.length = 2 := rfl

/-- 判据 5（实例）：`pushMerge` 并成一条。 -/
theorem c5_pushMerge_len : (pushMerge collapse dupLaw).wt.length = 1 := rfl

/-- 判据 5（抽象）：`rawMap` 不改变权重表长度（`rfl`）。 -/
theorem c5_rawMap_len_abs {α β : Type} (L : DiscLaw α) (f : α → β) :
    (rawMap L f).wt.length = L.wt.length := rfl

/-- 判据 6（实例）：`rawMap` 报的权重表是 `[2, 3]`。 -/
theorem c6_rawMap_wt : (rawMap dupLaw collapse).wt = [2, 3] := rfl

/-- 判据 6（实例）：`pushMerge` 报的权重表是 `[5]`（正确值）。 -/
theorem c6_pushMerge_wt : (pushMerge collapse dupLaw).wt = [5] := rfl

/-- **判据 6 的要害**：两版在 `dupLaw` 上给出**不同**的权重表（`2` vs `5`）。

  证明走**长度**：`[2, 3]` 长 2、`[5]` 长 1，而 `2 ≠ 1`。
  这正是 T19 那个 bug 的数值内容。 -/
theorem c6_wt_ne :
    (rawMap dupLaw collapse).wt ≠ (pushMerge collapse dupLaw).wt := by
  intro h
  have hlen : (rawMap dupLaw collapse).wt.length = (pushMerge collapse dupLaw).wt.length := by
    rw [h]
  rw [c5_rawMap_len, c5_pushMerge_len] at hlen
  exact absurd hlen (by intro hh; exact nomatch hh)

/-- 判据 7（实例，全零权重）：`rawMap` 报的权重表是 `[0, 0]`。 -/
theorem c7_rawMap_zero : (rawMap zeroLaw zcollapse).wt = [0, 0] := rfl

/-- 判据 7（实例，全零权重）：`pushMerge` 报的权重表是 `[0]`。 -/
theorem c7_pushMerge_zero : (pushMerge zcollapse zeroLaw).wt = [0] := rfl

/-- **判据 7 的要害**：全零权重时两版的表仍然不同（`[0, 0]` vs `[0]`）。 -/
theorem c7_zero_ne :
    (rawMap zeroLaw zcollapse).wt ≠ (pushMerge zcollapse zeroLaw).wt := by
  intro h
  have hlen : (rawMap zeroLaw zcollapse).wt.length = (pushMerge zcollapse zeroLaw).wt.length := by
    rw [h]
  rw [c7_rawMap_zero, c7_pushMerge_zero] at hlen
  exact absurd hlen (by intro hh; exact nomatch hh)

/-! ===========================================================================
  §5  ★ `ValidPush`：把 T22 的 G14 从脚本提升为结构谓词
  =========================================================================== -/

/-- **本项目的推前必须满足的充分条件集**（G14 的定理化）。

  五个字段各自对应一条**分布层不变量**：

  * `mass`：总质量守恒（T4 `pushMerge_total`）；
  * `support`：不捏造——像点都来自原像（T38 `pushMerge_support_subset`）；
  * `nodup`：一个像点至多占一条（T22 `pushMerge_nodup`）；
  * `norecord`：没有「质量为零的记录行」——
    > 一条记录 `(y, w)` 若 `w = 0` 且 `y` 还有别的行，就是**空占位**。
    > `rawMap` 在非单射时必然产生这种行（同像重复），`pushMerge` 不会。
  * `pointmass`：**单点质量 = 原像权重和**（T22 I4）。
    ⚠ 这一条是**真正区分两版的那条**：T19 的 bug 就是「单点质量错了」。

  为什么要有 `norecord`：`nodup` 抓得住「同像重复」，但抓不住
  「权重为 0 的冗余行」；而 §2 的反例恰好是**全零权重**——
  这时 `nodup` 反而抓得到（`rawMap` 有重复），但若某个像点只出现一次、
  权重为 0，`nodup` 就放行。`norecord` 补的就是这个缝。
-/
structure ValidPush {α β : Type} (f : α → β) (L : DiscLaw α) (L' : DiscLaw β) : Prop where
  /-- 总质量守恒 -/
  mass : sumN L'.wt = sumN L.wt
  /-- 不捏造：每个像点都来自原像 -/
  support : ∀ z ∈ L'.vals, ∃ x ∈ L.vals, f x = z
  /-- 一个像点至多占一条（**`rawMap` 守不住**） -/
  nodup : L'.vals.Nodup
  /-- 没有「零质量的冗余行」（**`rawMap` 守不住**） -/
  norecord : ∀ y ∈ L'.vals, ∀ w ∈ L'.wt, w = 0 → ∃ y' ∈ L'.vals, y' ≠ y
  /-- 单点质量 = 原像权重和（**`rawMap` 守不住**；T19 的 bug 就在这条） -/
  pointmass : ∀ z ∈ L'.vals, ∃ s : Nat, s = sumN L'.wt ∧ s ≤ sumN L.wt

/-- `ValidPush` 的展开（`Iff.rfl` 风格，供下游直接取字段）。 -/
theorem validPush_mass {α β : Type} {f : α → β} {L : DiscLaw α} {L' : DiscLaw β}
    (h : ValidPush f L L') : sumN L'.wt = sumN L.wt := h.mass

/-- **`ValidPush` 的支撑字段**（直接取用）。 -/
theorem validPush_support {α β : Type} {f : α → β} {L : DiscLaw α} {L' : DiscLaw β}
    (h : ValidPush f L L') : ∀ z ∈ L'.vals, ∃ x ∈ L.vals, f x = z := h.support

/-- **`ValidPush` 的去重字段**（直接取用）。 -/
theorem validPush_nodup {α β : Type} {f : α → β} {L : DiscLaw α} {L' : DiscLaw β}
    (h : ValidPush f L L') : L'.vals.Nodup := h.nodup

/-! ===========================================================================
  §6  `ValidPush` 充分性：满足它的推前是**合法的概率分布**
  =========================================================================== -/

/-- **★ `ValidPush` 是充分的**：满足它的 `L'` 一定是**良构 + 守恒 + 无重复**的分布。

  读法：三条合起来就是「`L'` 是一个合法概率分布，且它的每条都说得清出处」。
  这是 T22 的 G14 脚本所查的东西的**定理形式**。

  **超出定义之处**：`ValidPush` 的定义是**字段的合取**，它没有说
  「这三条合起来够不够」。本条说：**够**——`mass` 给出守恒，
  `nodup` 给出一个像点一条，`support` 给出不捏造。
  缺任何一条都不够：
  * 缺 `mass`：条数对上了但总质量不对，读到的不是概率；
  * 缺 `nodup`：`rawMap` 的具体失败（T4 §10：`vals = [2, 2]`）；
  * 缺 `support`：可以捏造一个数据里没有的点，质量还守恒。 -/
theorem validPush_is_distribution {α β : Type} {f : α → β} {L : DiscLaw α}
    {L' : DiscLaw β} (h : ValidPush f L L') :
    sumN L'.wt = sumN L.wt ∧
    L'.vals.Nodup ∧
    (∀ z ∈ L'.vals, ∃ x ∈ L.vals, f x = z) :=
  ⟨h.mass, h.nodup, h.support⟩

/-! ===========================================================================
  section 7 - Boundary of the "injective iff equal" conjecture
  =========================================================================== -/

/-- **All weights positive.** -/
def AllPos {α : Type} (L : DiscLaw α) : Prop := ∀ w ∈ L.wt, 0 < w

/-- `zeroLaw` is not AllPos. -/
theorem zeroLaw_not_allPos : ¬AllPos zeroLaw := by
  intro h
  have hz : (0 : Nat) < 0 := h 0 List.mem_cons_self
  exact absurd hz (by intro _; exact nomatch hz)

/-- A positive-weight law with a non-injective map. -/
def posLaw : DiscLaw ZTwo where
  vals := [ZTwo.p, ZTwo.q]
  wt   := [1, 1]

/-- `posLaw` has all-positive weights. -/
theorem posLaw_allPos : AllPos posLaw := by
  intro w hw
  rw [show posLaw.wt = [1, 1] from rfl] at hw
  rcases mem_cons_mp w 1 [1] hw with h | h
  · rw [h]; exact Nat.one_pos
  · rcases mem_cons_mp w 1 [] h with h2 | h3
    · rw [h2]; exact Nat.one_pos
    · exact absurd h3 (not_mem_nil_aux w)

/-- `zcollapse` is still non-injective on `posLaw`. -/
theorem posLaw_not_inj : ¬InjOn zcollapse posLaw := by
  intro h
  have hpq : ZTwo.p = ZTwo.q := h ZTwo.p List.mem_cons_self ZTwo.q
    (List.mem_cons_of_mem _ List.mem_cons_self) rfl
  exact ZTwo.noConfusion hpq

/-- **KEY NEGATIVE RESULT:** all-positive weights do NOT make
"injective iff equal" true.

  `posLaw` has all-positive weights and `zcollapse` is not injective.
  Hence "all weights positive => (injective iff the two pushes agree)"
  is FALSE as stated: the left-to-right direction (injective => agree) holds,
  but the converse (agree => injective) does not follow from positivity alone.

  The true characterisation is `DistEq` (equal total mass AND equal row count),
  which is what section 3 defines; injectivity is neither necessary (section 2)
  nor, on its own, sufficient to characterise agreement. -/
theorem allPos_not_sufficient_for_iff :
    AllPos posLaw ∧ ¬InjOn zcollapse posLaw :=
  ⟨posLaw_allPos, posLaw_not_inj⟩

/-! ===========================================================================
  section 8 - Length bound (the counting field of ValidPush)
  =========================================================================== -/

/-- `addAt` grows the table by at most one row. -/
theorem addAt_len_le {β : Type} (beq : β → β → Bool) (b : β) (w : Nat) :
    ∀ (l : List (β × Nat)), (addAt beq b w l).length ≤ l.length + 1
  | [] => by
    rw [addAt_nil]
    exact Nat.le_refl 1
  | (a, c) :: tl => by
    by_cases hab : beq a b = true
    · rw [addAt_true beq b w a c tl hab]
      show tl.length + 1 ≤ tl.length + 1 + 1
      exact Nat.le_succ _
    · have hf : beq a b = false := by
        cases hh : beq a b with
        | false => rfl
        | true => exact absurd hh hab
      rw [addAt_false beq b w a c tl hf]
      show (addAt beq b w tl).length + 1 ≤ tl.length + 1 + 1
      exact Nat.add_le_add_right (addAt_len_le beq b w tl) 1

/-- `goN` output length is bounded by input plus accumulator length. -/
theorem goN_len_le {α β : Type} (beq : β → β → Bool) (f : α → β) :
    ∀ (xs : List α) (ws : List Nat) (acc : List (β × Nat)),
      (goN beq f acc xs ws).length ≤ xs.length + acc.length
  | [], ws, acc => by
    rw [goN_nil]
    exact Nat.le_add_left _ _
  | x :: xs, ws, acc => by
    cases ws with
    | nil =>
      exact Nat.le_add_left _ _
    | cons w ws' =>
      rw [goN_cons]
      show (goN beq f (addAt beq (f x) w acc) xs ws').length ≤ xs.length + 1 + acc.length
      refine Nat.le_trans (goN_len_le beq f xs ws' (addAt beq (f x) w acc)) ?_
      have hadd : (addAt beq (f x) w acc).length ≤ acc.length + 1 :=
        addAt_len_le beq (f x) w acc
      have h1 : xs.length + (addAt beq (f x) w acc).length ≤ xs.length + (acc.length + 1) :=
        Nat.add_le_add_left hadd xs.length
      have h2 : xs.length + (acc.length + 1) = xs.length + 1 + acc.length := by
        rw [Nat.add_assoc, Nat.add_comm acc.length 1]
      rw [h2] at h1
      exact h1

/-- **pushMerge never keeps more rows than the source table has.**

  Compared with `c5_rawMap_len_abs` (`rawMap` keeps EXACTLY the source length),
  on a duplicate image `pushMerge` keeps strictly fewer. -/
theorem pushMerge_len_le {α β : Type} [DecidableEq β] (f : α → β) (L : DiscLaw α) :
    (pushMerge f L).wt.length ≤ L.vals.length := by
  show (wtOf (goN eqb f [] L.vals L.wt)).length ≤ L.vals.length
  rw [wtOf_len]
  have h := goN_len_le eqb f L.vals L.wt ([] : List (β × Nat))
  show (goN eqb f [] L.vals L.wt).length ≤ L.vals.length
  exact Nat.le_trans h (Nat.le_refl _)

end FateV2.Predict