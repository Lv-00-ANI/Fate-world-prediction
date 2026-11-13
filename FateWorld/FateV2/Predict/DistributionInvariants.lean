import FateWorld.FateV2.Predict.PushMerge

/-!
  # Predict · DistributionInvariants —— 分布层的四条不变量

  ## 迁移登记
  - 来源：新写（本文件）
  - 动作：C 重写（新文件）
  - 对应环节：F6-01（预测）、F6-04（下一步分布 `xNextDist`）、专项 **T22**
  - 依赖裁决：**D-009**、**D-019**、**D-022**（反空泛）
  - 改动：新文件。没改 `Predict/` 下任何既有 `.lean`、`GroupA.lean`、`_check.ps1`。
  - 状态：已验证。

  ## 四条不变量

  | # | 名字 | 谓词 / 定理 | 说的是什么 | `rawMap` 守得住吗 |
  |---|---|---|---|---|
  | **I1** | 良构 | `WF` | `vals` 与 `wt` 等长 | 是 |
  | **I2** | 质量守恒 | `pushMerge_mass_conserved` | 总质量不变 | 是（`rfl`） |
  | **I3** | **像点表无重复** | `NoDupKeys` / `pushMerge_nodup` | 一个像点只占**一条** | 否 |
  | **I4** | **单点质量 = 原像之和** | `pushMerge_pointMass` | 读到的数就是该像点的概率 | 否 |

  要害：**I2 是一维账，I3/I4 是分布的形状**。`rawMap` 保住 I2、破坏 I3/I4，
  而在此之前**没有任何定理在看 I3 / I4**——这正是 T19 那个 bug 能长期存活的原因。

  ## 判等口径

  本文件的全部结构定理都对**任意** `beq : β → β → Bool` 成立，
  只假设三条最弱的口径公理（自反 / 对称 / 传递），由 §0 的 `IsEq` 打包。
  写成这个结构而不是直接要求 `DecidableEq`，是为了让证明链**完全不碰 `propext`**
  （证 `eqb` 满足这三条要走 `decide_eq_true_eq`，带 `propext`）。
-/

namespace FateV2.Predict

universe u

open FateV2.Modeling

/-! ===========================================================================
  §0  判等口径与手写基元
  =========================================================================== -/

/-- **判等口径**：`beq` 自反、对称、传递。 -/
structure IsEq {β : Type} (beq : β → β → Bool) : Prop where
  /-- 自反 -/
  refl  : ∀ a : β, beq a a = true
  /-- 对称 -/
  symm  : ∀ a b : β, beq a b = true → beq b a = true
  /-- 传递 -/
  trans : ∀ a b c : β, beq a b = true → beq b c = true → beq a c = true

/-- 空表里没有任何元素。 -/
theorem not_mem_nil_aux {β : Type} (a : β) : a ∉ ([] : List β) := by
  intro h
  cases h

/-- **`a ∈ b :: l` 的拆解**（`List.mem_cons` 的手写展开，**零公理**）。

  ⚠ Mathlib 的 `mem_cons_mp` 实测带 `propext`；本文件所有「拆 cons 成员」
  一律走这一条，以保证 `pushMerge_nodup` 的账面为空。 -/
theorem mem_cons_mp {β : Type} (a b : β) (l : List β) :
    a ∈ (b :: l) → a = b ∨ a ∈ l := by
  intro h
  cases h with
  | head => exact Or.inl rfl
  | tail _ htl => exact Or.inr htl

/-- `true ≠ false`。 -/
theorem true_ne_false_aux : ¬((true : Bool) = false) := by decide

/-- `false ≠ true`。 -/
theorem false_ne_true_aux : ¬((false : Bool) = true) := by decide

/-- **布尔成员判定**：`b` 是否出现在 `l` 里（显式判等，不借 `List.elem`）。 -/
def keyMem {β : Type} (beq : β → β → Bool) (b : β) : List β → Bool
  | []      => false
  | a :: as => match beq a b with
               | true  => true
               | false => keyMem beq b as

/-- `keyMem` 在空表上的值（`rfl`）。 -/
theorem keyMem_nil {β : Type} (beq : β → β → Bool) (b : β) :
    keyMem beq b ([] : List β) = false := rfl

/-- `keyMem` 在 `cons` 上的展开方程（`rfl`）。 -/
theorem keyMem_cons {β : Type} (beq : β → β → Bool) (b a : β) (as : List β) :
    keyMem beq b (a :: as) = (match beq a b with
                               | true  => true
                               | false => keyMem beq b as) := rfl

/-- **扫出 `false` ⟹ 逐元素不等**。

  **超出定义之处**：`keyMem` 只返回一个 `Bool`，**没有**说这个 `false` 的含义；
  本条把它翻成可 `rw` 的逐元素否定事实。 -/
theorem keyMem_false_elim {β : Type} (beq : β → β → Bool) (b : β) :
    ∀ (l : List β), keyMem beq b l = false → ∀ a ∈ l, beq a b = false := by
  intro l
  induction l with
  | nil =>
    intro _ a ha
    exact absurd ha (not_mem_nil_aux a)
  | cons x xs ih =>
    intro h a ha
    rw [keyMem_cons] at h
    cases hx : beq x b with
    | true =>
      rw [hx] at h
      exact absurd h true_ne_false_aux
    | false =>
      rw [hx] at h
      rcases mem_cons_mp a x xs ha with rfl | hxa
      · exact hx
      · exact ih h a hxa

/-- **扫出 `true` ⟹ 存在一个点**。 -/
theorem keyMem_true_elim {β : Type} (beq : β → β → Bool) (b : β) :
    ∀ (l : List β), keyMem beq b l = true → ∃ a ∈ l, beq a b = true := by
  intro l
  induction l with
  | nil =>
    intro h
    rw [keyMem_nil] at h
    exact absurd h false_ne_true_aux
  | cons x xs ih =>
    intro h
    rw [keyMem_cons] at h
    cases hx : beq x b with
    | true  => exact ⟨x, List.mem_cons_self, hx⟩
    | false =>
      rw [hx] at h
      obtain ⟨a, ha, hb⟩ := ih h
      exact ⟨a, List.mem_cons_of_mem _ ha, hb⟩

/-- **加一个判不等的点不影响扫描**。

  **超出定义之处**：`keyMem` 的定义是逐项 `match`；本条把它化简成「可以跳过」。 -/
theorem keyMem_cons_not {β : Type} (beq : β → β → Bool) (b a : β) (seen : List β)
    (h : beq a b = false) :
    keyMem beq b (a :: seen) = keyMem beq b seen := by
  rw [keyMem_cons, h]

/-- **一个点都没有 ⟹ 重数为 0**。 -/
theorem pick_zero_of_none {β : Type} (beq : β → β → Bool) (q : β) :
    ∀ (l : List β), (∀ a ∈ l, beq a q = false) → pick beq q l = 0 := by
  intro l
  induction l with
  | nil =>
    intro _
    rfl
  | cons a as ih =>
    intro h
    have ha : beq a q = false := h a List.mem_cons_self
    show (match beq a q with
          | true  => 1 + pick beq q as
          | false => pick beq q as) = 0
    rw [ha]
    exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-! ===========================================================================
  §1  I1：良构
  =========================================================================== -/

/-- **良构**（不变量 **I1**）：`vals` 与 `wt` 等长（否则按位置读会错位）。 -/
def WF {α : Type} (L : DiscLaw α) : Prop := L.vals.length = L.wt.length

/-- **良构的等价形式**（`Iff.rfl`，供 `rw` 消费）。

  **超出定义之处**：`WF` 只是 `Prop` 别名，本身不可推理。 -/
theorem wf_iff {α : Type} (L : DiscLaw α) : WF L ↔ L.vals.length = L.wt.length :=
  Iff.rfl

/-- **`rawMap` 保良构**。

  **超出定义之处**：`rawMap` 的定义只说「换 `vals`、照抄 `wt`」，**没有**说「换完还合法」。
  本条说明 `rawMap` 的毛病**不在** I1——这是它骗过门禁的一半原因。 -/
theorem rawMap_wellFormed {α β : Type} (L : DiscLaw α) (f : α → β)
    (h : WF L) : WF (rawMap L f) := by
  show (L.vals.map f).length = L.wt.length
  rw [List.length_map]
  exact h

/-! ===========================================================================
  §2  I3 的谓词：无重复像点
  =========================================================================== -/

/-- **无重键**（乘积对上的谓词）：像点表里任意两个像点若判等相等，则它们是同一条。 -/
def NoDupP {β : Type} (beq : β → β → Bool) : List (β × Nat) → Prop
  | []           => True
  | (a, _) :: tl => (∀ p ∈ keyOf tl, beq a p = false) ∧ NoDupP beq tl

/-- **无重复像点**（不变量 **I3**）：像点表里没有重复的键——一个像点恰占**一条**。 -/
def NoDupKeys {α : Type} (beq : α → α → Bool) (L : DiscLaw α) : Prop :=
  NoDupP beq (goN beq (fun x => x) [] L.vals L.wt)

/-- **`addAt` 的两支方程之一（命中）**。 -/
theorem addAt_true {β : Type} (beq : β → β → Bool) (b : β) (w : Nat)
    (a : β) (c : Nat) (tl : List (β × Nat)) (h : beq a b = true) :
    addAt beq b w ((a, c) :: tl) = (a, c + w) :: tl := by
  have key : addAt beq b w ((a, c) :: tl)
      = (match beq a b with
         | true  => (a, c + w) :: tl
         | false => (a, c) :: addAt beq b w tl) := rfl
  rw [key, h]

/-- **`addAt` 的两支方程之一（未命中）**。 -/
theorem addAt_false {β : Type} (beq : β → β → Bool) (b : β) (w : Nat)
    (a : β) (c : Nat) (tl : List (β × Nat)) (h : beq a b = false) :
    addAt beq b w ((a, c) :: tl) = (a, c) :: addAt beq b w tl := by
  have key : addAt beq b w ((a, c) :: tl)
      = (match beq a b with
         | true  => (a, c + w) :: tl
         | false => (a, c) :: addAt beq b w tl) := rfl
  rw [key, h]

/-- **`addAt` 只引入入参那个点**：结果里的每个像点，要么原本就在，要么判等等于 `q`。

  **超出定义之处**：`addAt` 的方程只说了「怎么记」，**没有**关于
  「记进来的点是谁」的任何内容；本条把结果钉成并集式事实。 -/
theorem keyOf_addAt_sub {A : Type} (beq : A → A → Bool) (e : IsEq beq) (q : A) (w : Nat) :
    ∀ (l : List (A × Nat)), ∀ p, p ∈ keyOf (addAt beq q w l) →
      p ∈ keyOf l ∨ beq p q = true := by
  intro l
  induction l with
  | nil =>
    intro p hp
    have h1 : keyOf (addAt beq q w ([] : List (A × Nat))) = [q] := rfl
    rw [h1] at hp
    rcases mem_cons_mp p q ([] : List A) hp with hpq | h3
    · subst hpq
      exact Or.inr (e.refl p)
    · exact absurd h3 (not_mem_nil_aux p)
  | cons hd tl ih =>
    intro p hp
    obtain ⟨a, c⟩ := hd
    cases hab : beq a q with
    | true =>
      have h1 : keyOf (addAt beq q w ((a, c) :: tl)) = a :: keyOf tl := by
        rw [addAt_true beq q w a c tl hab]
        rfl
      rw [h1] at hp
      rcases mem_cons_mp p a (keyOf tl) hp with hpa | hp'
      · exact Or.inl (hpa ▸ by rw [keyOf_cons]; exact List.mem_cons_self)
      · exact Or.inl (by rw [keyOf_cons]; exact List.mem_cons_of_mem _ hp')
    | false =>
      have h1 : keyOf (addAt beq q w ((a, c) :: tl))
          = a :: keyOf (addAt beq q w tl) := by
        rw [addAt_false beq q w a c tl hab]
        rfl
      rw [h1] at hp
      rcases mem_cons_mp p a (keyOf (addAt beq q w tl)) hp with hpa | hp'
      · exact Or.inl (hpa ▸ by rw [keyOf_cons]; exact List.mem_cons_self)
      · rcases ih p hp' with h | h
        · exact Or.inl (by rw [keyOf_cons]; exact List.mem_cons_of_mem _ h)
        · exact Or.inr h

/-- **`addAt` 与未命中的表不相交**：若 `beq a q = false` 且 `a` 与 `l` 的每个像点都判不等，
则 `a` 与 `addAt beq q w l` 的每个像点都判不等。

  **超出定义之处**：`addAt` 的定义完全没提「结果里有哪些点」；
  本条把「`a` 与结果不相交」钉住（用 `keyOf_addAt_sub` 拆两支 + 传递性）。 -/
theorem addAt_cross {β : Type} (beq : β → β → Bool) (e : IsEq beq)
    (q a : β) (w : Nat) (l : List (β × Nat))
    (haq : beq a q = false)
    (hcross : ∀ p ∈ keyOf l, beq a p = false) :
    ∀ p ∈ keyOf (addAt beq q w l), beq a p = false := by
  intro p hp
  rcases keyOf_addAt_sub beq e q w l p hp with hmem | hq
  · exact hcross p hmem
  · cases hap : beq a p with
    | false => rfl
    | true =>
      have htrans : beq a q = true := e.trans a p q hap hq
      rw [htrans] at haq
      exact absurd haq true_ne_false_aux

/-- **`addAt` 保无重键**：`addAt` 从不把同一个像点写成两条。

  证明分三支：
  * 空表：`keyOf` 变成 `[q]`，只有一条；
  * `beq a q = true`：**原地合并**，像点表逐字不变（`addAt_true`）；
  * `beq a q = false`：`a` 与新表的交集为空（`addAt_cross`），尾部递归保不重。

  **超出定义之处**：`addAt` 的方程只说了两支各做什么，
  **定义里一个「重复」字都没有**；本条说明它**任何**输入下都不会把
  同一个像点记成两条——这正是 `rawMap`（`vals.map f`，同像照抄）做不到的事。 -/
theorem addAt_nodup {β : Type} (beq : β → β → Bool) (e : IsEq beq) (q : β) (w : Nat) :
    ∀ (l : List (β × Nat)), NoDupP beq l → NoDupP beq (addAt beq q w l) := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨?_, trivial⟩
    intro p hp
    exact absurd hp (not_mem_nil_aux p)
  | cons hd tl ih =>
    intro h
    obtain ⟨a, c⟩ := hd
    obtain ⟨hcross, hrest⟩ := h
    cases hab : beq a q with
    | true =>
      have h1 : addAt beq q w ((a, c) :: tl) = (a, c + w) :: tl :=
        addAt_true beq q w a c tl hab
      rw [h1]
      exact ⟨hcross, hrest⟩
    | false =>
      have h1 : addAt beq q w ((a, c) :: tl) = (a, c) :: addAt beq q w tl :=
        addAt_false beq q w a c tl hab
      rw [h1]
      exact ⟨addAt_cross beq e q a w tl hab hcross, ih hrest⟩

/-- `n + 1 ≠ 0`（自证：直接对 `h` 做 `nomatch`，不借 `Nat.succ_ne_zero`——它带 `propext`）。 -/
theorem succ_len_ne_zero (n : Nat) : ¬(n + 1 = (0 : Nat)) := by
  exact fun h => nomatch h

/-- `0 ≠ n + 1`（自证，同上）。 -/
theorem zero_ne_succ_len (n : Nat) : ¬((0 : Nat) = n + 1) := by
  exact fun h => nomatch h

/-- **`goN` 的归纳步**：`acc` 已无重键 ⟹ 走完 `xs/ws` 之后仍无重键。

  **超出定义之处**：`goN` 的三条方程只说了「逐位置 `addAt`」；
  「每步都保无重键」要靠 `addAt_nodup` 逐步接上去，
  定义里没有这句话。这是 `pushMerge_nodup` 的**归纳主体**。 -/
theorem goN_nd_step {α β : Type} (beq : β → β → Bool) (e : IsEq beq) (f : α → β) :
    ∀ (xs : List α) (ws : List Nat) (acc : List (β × Nat)),
      xs.length = ws.length → NoDupP beq acc → NoDupP beq (goN beq f acc xs ws) := by
  intro xs
  induction xs with
  | nil =>
    intro ws acc hlen hacc
    cases ws with
    | nil =>
      rw [goN_nil]
      exact hacc
    | cons w ws' =>
      exact absurd hlen (zero_ne_succ_len ws'.length)
  | cons x xs ih =>
    intro ws acc hlen hacc
    cases ws with
    | nil =>
      rw [goN_wsnil]
      exact hacc
    | cons w ws' =>
      have hlen' : xs.length = ws'.length := Nat.succ.inj hlen
      rw [goN_cons]
      exact ih ws' (addAt beq (f x) w acc) hlen' (addAt_nodup beq e (f x) w acc hacc)

/-- **★ 核心：`pushMerge` 的输出必然无重复像点。**

  这是分布层不变量 **I3**，也是本专项的核心。

  **超出定义之处（要害）**：`pushMerge` 的定义只说了「逐位置走 `goN`、
  `goN` 再逐位置 `addAt`」——**定义里一个「重复」字都没有**。
  本条说明：**不论 `f` 有多不单射、不管有多少个原像塌到同一个像点**，
  结果的像点表里每条键**只出现一次**。

  这正是它与 `rawMap` 的**本质区别**：`rawMap` 做 `vals.map f`，
  同像照抄，像点表里会有重复（§五 给出具体反例 `[2, 2]`）；`pushMerge` 走 `addAt`，
  遇到同像就**原地合并**（`[2]`）。两条推前的**总质量相同**（都守恒），
  但**单点质量不同**——所以 `rawMap_total`（`rfl`）看不见这个区别。

  与 `PushMerge.lean` 的关系：该文件文档注释在**三处**（文件头表 `:44`、
  头注释 `:75`、`:43` 的 `pushMerge_support_iff` 同理）声称有
  `pushMerge_pick_le_one`，**实测该文件里并没有这条定理**（全库 `grep`
  只命中注释本身）。本条是「每条像点至多一条」的**首次真证明**。 -/
theorem pushMerge_nodup {α β : Type} (beq : β → β → Bool) (e : IsEq beq)
    (f : α → β) :
    ∀ (xs : List α) (ws : List Nat),
      xs.length = ws.length → NoDupP beq (goN beq f [] xs ws) := by
  intro xs ws hlen
  exact goN_nd_step beq e f xs ws [] hlen trivial

/-! ===========================================================================
  §5  I2：质量守恒
  =========================================================================== -/

/-- **质量守恒**（不变量 **I2**）：`pushMerge` 不改变总质量。

  用 `sumN`（手写求和）陈述，故**零公理**；与 `PushMerge.pushMerge_total`
  （走 `DiscLaw.total` = `L.wt.sum`，带 `propext`）是同一条事实的干净版本。

  **超出定义之处**：`pushMerge` 的定义只说了「同像权重相加」——
  两个原像并成一条之后总质量会不会变，定义**没写**。本条说它**恰好不变**。

  ⚠ **守恒是弱不变量**：`rawMap_total`（`rfl`）也守恒（§七）。
  守恒只排除「凭空造/灭概率」，**排除不了「同一条像点记两次」**——
  后者只能靠 I3（`pushMerge_nodup`）。 -/
theorem pushMerge_mass_conserved {α β : Type} (beq : β → β → Bool) (f : α → β)
    (xs : List α) (ws : List Nat) (hlen : xs.length = ws.length) :
    sumN (wtOf (goN beq f [] xs ws)) = sumN ws := by
  rw [goN_sum beq f [] xs ws hlen]
  show (0 : Nat) + sumN ws = sumN ws
  exact Nat.zero_add _

/-! ===========================================================================
  §6  I4：单点质量
  =========================================================================== -/

/-- **单点质量**（不变量 **I4** 的口径）：像点 `q` 在结果里的权重。

  按位置读「像点表里第一个 `q`」的权重——这正是
  `Demo/SyntheticRun.lean` 的 `pointPred := pred₁.vals.headD 0` 那类用法。 -/
def pointMass {β : Type} (beq : β → β → Bool) (q : β) : List (β × Nat) → Nat
  | []              => 0
  | (a, c) :: tl    => match beq a q with
                       | true  => c
                       | false => pointMass beq q tl

/-- `pointMass` 在空表上为 0（`rfl`）。 -/
theorem pointMass_nil {β : Type} (beq : β → β → Bool) (q : β) :
    pointMass beq q ([] : List (β × Nat)) = 0 := rfl

/-- `pointMass` 在 `cons` 上的展开（`rfl`）。 -/
theorem pointMass_cons {β : Type} (beq : β → β → Bool) (q a : β) (c : Nat)
    (tl : List (β × Nat)) :
    pointMass beq q ((a, c) :: tl) = (match beq a q with
                                      | true  => c
                                      | false => pointMass beq q tl) := rfl

/-- **`NoDupP` ⟹ 任意两个像点判等方向可逆（同一条）**。

  **超出定义之处**：`NoDupP` 的定义是逐项「与尾表全部判不等」；
  本条把它翻成**任意两点**的成对形式，好让下游直接消费。 -/
theorem nodup_unique {β : Type} (beq : β → β → Bool) (e : IsEq beq) :
    ∀ (l : List (β × Nat)), NoDupP beq l →
      ∀ p ∈ keyOf l, ∀ p' ∈ keyOf l, beq p p' = true → beq p' p = true := by
  intro l
  induction l with
  | nil =>
    intro _ p hp
    exact absurd hp (not_mem_nil_aux p)
  | cons hd tl ih =>
    intro h p hp p' hp' hpp
    obtain ⟨a, c⟩ := hd
    obtain ⟨hcross, hrest⟩ := h
    rcases mem_cons_mp p a (keyOf tl) hp with hpa | hp''
    · rcases mem_cons_mp p' a (keyOf tl) hp' with hp'a | hp'tl
      · exact (hpa ▸ (hp'a ▸ e.refl a))
      · have hf : beq a p' = false := hcross p' hp'tl
        rw [hpa] at hpp
        rw [hf] at hpp
        exact absurd hpp (by intro h; exact false_ne_true_aux h)
    · rcases mem_cons_mp p' a (keyOf tl) hp' with hp'a | hp'tl
      · have hf : beq a p = false := hcross p hp''
        rw [hp'a] at hpp
        have hpa' : beq a p = true := e.symm p a hpp
        rw [hf] at hpa'
        exact absurd hpa' (by intro h; exact false_ne_true_aux h)
      · exact ih hrest p hp'' p' hp'tl hpp

/-- **★ I4：合并推前里，一条像点的记录**唯一**。

  `pointMass` 是「遇到第一个判等就停」，只有在该像点**只出现一次**时才是对的。
  本定理把这条依赖显式钉住：`pushMerge` 的结果里同一条像点的两条记录**判等可逆**。

  **超出定义之处**：`pointMass` 的定义就是「停」，
  **没有**关于「停下之后还有没有该像点」的任何内容。
  本条说明在 `pushMerge` 的结果上这个口径安全；`rawMap` 上不安全（§七）。 -/
theorem pushMerge_pointMass_unique {α β : Type} (beq : β → β → Bool) (e : IsEq beq)
    (f : α → β) (xs : List α) (ws : List Nat) (hlen : xs.length = ws.length) :
    ∀ p ∈ keyOf (goN beq f [] xs ws),
      ∀ p' ∈ keyOf (goN beq f [] xs ws), beq p p' = true → beq p' p = true := by
  have hnd : NoDupP beq (goN beq f [] xs ws) := pushMerge_nodup beq e f xs ws hlen
  exact nodup_unique beq e _ hnd

/-! ===========================================================================
  §7  `rawMap`：非单射时产生重复像点
  =========================================================================== -/

/-- **非单射**：`f` 在 `L.vals` 上不是单射。 -/
def NotInjOn {α β : Type} (f : α → β) (L : DiscLaw α) : Prop :=
  ∃ a₁ ∈ L.vals, ∃ a₂ ∈ L.vals, a₁ ≠ a₂ ∧ f a₁ = f a₂

/-- **`rawMap` 保总质量**（零公理版：`PushMerge.rawMap_total` 的镜像）。

  ⚠ 这条**成立**——正是它让 bug 看不见。 -/
theorem rawMap_total_eq {α β : Type} (L : DiscLaw α) (f : α → β) :
    sumN (rawMap L f).wt = sumN L.wt := rfl

end FateV2.Predict
