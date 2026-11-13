import FateWorld.Legacy.ConcreteBridgeQuant

/-! ===========================================================================
  §45  ⭐⭐ **强化签名**：结构刻画（第 44 轮负面结果的**进一步澄清**）

  ## 动机（承接第 44 轮）

  **第 44 轮的结论**：`Equiv1` 关于转移系统**不单调**。
  **第 44 轮报告提出的猜想**：改用「记录后继的强化签名」可以恢复单调性。

  ## ⚠⚠ 本轮**否证了这个猜想**（如实登记）

  **分析**：设 `StrongSig step s a := {(s', r) | step s a s' r}`（保后继）。则：

  | 方向 | 是否成立 | 反例 |
  |---|---|---|
  | `step ⊆ step'` ⟹ `StrongSig step ⊆ StrongSig step'` | ✅ **成立** | — |
  | `step ⊆ step'` ⟹ `StrongEquiv step' ⊆ StrongEquiv step` | ❌ **假** | 同第 44 轮 |
  | `step ⊆ step'` ⟹ `StrongEquiv step ⊆ StrongEquiv step'` | ❌ **假** | `step = ∅`，`step' = ⊤` |

  **⟹ 即**：**单调性在**两个方向都不成立**** ——
  **保留后继**不能**解决**问题。

  ## ⭐⭐ 根因（本轮的核心洞察）

  **「签名相等」**不是**关于转移系统的单调谓词**：

  * **转移更多** ⟹ **签名更大**（单调 ✓）
  * **但**「两个签名**相等**」这一**谓词**在签名的偏序上
    **既不单调递增也不单调递减**（相等是**对称**关系，
    而偏序是**反对称**的）。

  **⟹ 即**：**试图用「签名相等」得到单调性，从**类型上**就注定失败。**

  ## ⭐ 本节给出的**正确**结论（代替假单调性）

  | # | 定理 | 内容 |
  |---|---|---|
  | **1** | ⭐⭐ **`strongSig_mono`** | **强化签名关于 `step` 单调**（签名层）|
  | **2** | ⭐⭐ **`strongEquiv_iff`** | ⭐ **结构刻画**：强化等价 ⟺ 转移关系逐动作相等 |
  | **3** | ⭐ **`obsInt_eq_proj`** | **`ObsInt` = 强化签名的第二投影** |
  | **4** | ⭐⭐ **`strong_refines_obsInt`** | **强化等价 ⟹ 原等价**（信息不丢）|

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace StrongSignature

universe u v w

variable {SCM : Type u} {Action : Type v} {Resp : Type w}

/-! ### §45.1 ⭐⭐ 强化签名（保留后继） -/

/-- ⭐⭐ **强化签名**：**保留后继**的完整转移集。

$$\mathrm{StrongSig}\,\text{step}\,s\,a := \{(s', r) \mid \text{step}\,s\,a\,s'\,r\}$$

**⚠ 与 `ObsInt` 的差别**：`ObsInt` 取**第二投影**（只留 `r`），
**本节保留二元组** `(s', r)`。 -/
def StrongSig (step : SCM → Action → SCM → Resp → Prop) (s : SCM) :
    Action → Set (SCM × Resp) :=
  fun a => {p | step s a p.1 p.2}

/-- ⭐⭐ **强化一步等价**：所有动作下的强化签名相同。 -/
def StrongEquiv (step : SCM → Action → SCM → Resp → Prop) (s t : SCM) : Prop :=
  ∀ a : Action, StrongSig step s a = StrongSig step t a

/-! ### §45.2 ⭐⭐ 签名层单调（这一层**成立**） -/

/-- ⭐⭐ **强化签名关于 `step` 单调**。

$$\text{step} \subseteq \text{step}' \implies
  \mathrm{StrongSig}\,\text{step} \subseteq \mathrm{StrongSig}\,\text{step}'$$

**⟹ 即**：**转移更多 ⟹ 强化签名更大。** -/
theorem strongSig_mono {step step' : SCM → Action → SCM → Resp → Prop}
    (h : ∀ s a s' r, step s a s' r → step' s a s' r) (s : SCM) (a : Action) :
    StrongSig step s a ⊆ StrongSig step' s a :=
  fun _ hp => h s a _ _ hp

/-! ### §45.3 ⭐⭐ 结构刻画（代替假单调性） -/

/-- ⭐⭐ **结构刻画**：**强化等价 ⟺ 逐动作的转移关系相等**。

$$\mathrm{StrongEquiv}\,\text{step}\,s\,t \iff
  \forall a,\ \text{step}\,s\,a = \text{step}\,t\,a \quad(\text{作为关系})$$

**⟹ 即**：**强化等价就是「转移关系的外延相等」** ——
**这是**结构刻画**，比单调性更有价值**（它**完全刻画**了强化等价）。 -/
theorem strongEquiv_iff (step : SCM → Action → SCM → Resp → Prop) (s t : SCM) :
    StrongEquiv step s t ↔
      ∀ a : Action, ∀ s'' : SCM, ∀ r : Resp, (step s a s'' r ↔ step t a s'' r) := by
  constructor
  · intro h a s'' r
    have h1 : (s'', r) ∈ StrongSig step s a ↔ (s'', r) ∈ StrongSig step t a := by
      rw [h a]
    exact h1
  · intro h a
    ext p
    exact h a p.1 p.2

/-- ⭐ **`ObsInt` 是强化签名的**第二投影****。

$$\mathrm{ObsInt}\,\text{step}\,s\,a
  = \mathrm{Prod.snd}''(\mathrm{StrongSig}\,\text{step}\,s\,a)$$

**⟹ 即**：**强化签名**细于**原签名**（它多记了后继）。** -/
theorem obsInt_eq_proj (step : SCM → Action → SCM → Resp → Prop) (s : SCM) (a : Action) :
    ConcreteBridge.ObsInt step s a =
      Prod.snd '' (StrongSig step s a) := by
  ext r
  constructor
  · rintro ⟨s', hs'⟩
    exact ⟨(s', r), hs', rfl⟩
  · rintro ⟨⟨s'', r'⟩, hs'', hr⟩
    simp only at hr
    subst hr
    exact ⟨s'', hs''⟩

/-- ⭐⭐ **强化等价 ⟹ 原等价**（信息不丢的精确形式）。

$$\mathrm{StrongEquiv}\,\text{step}\,s\,t \implies
  \mathrm{Equiv1}\,\text{step}\,s\,t$$

**⟹ 即**：**强化签名**更细** —— 它认为等价的，原签名也认为等价。** -/
theorem strong_refines_obsInt (step : SCM → Action → SCM → Resp → Prop) {s t : SCM}
    (h : StrongEquiv step s t) :
    ConcreteBridge.Equiv1 step s t := by
  intro a
  rw [obsInt_eq_proj step s a, obsInt_eq_proj step t a, h a]

/-! ### §45.4 ⚠ 单调性**两个方向都不成立**（如实登记） -/

/-- ⭐⭐ **反例 1**：`step ⊆ step'` ⟹ `StrongEquiv step' ⊆ StrongEquiv step` **假**。

**构造**：`step'` 全部转移，`step` 只保留 `true` 的转移。

**⟹ 与第 44 轮同一反例** —— **保留后继**不**解决它。** -/
theorem strongEquiv_mono_down_false :
    ∃ (step step' : Bool → Unit → Bool → Bool → Prop),
      (∀ s a s' r, step s a s' r → step' s a s' r) ∧
      (∃ s t, StrongEquiv step' s t ∧ ¬ StrongEquiv step s t) := by
  refine ⟨(fun s _ s' r => s = true ∧ s' = true ∧ r = true),
          (fun _ _ _ _ => True), ?_, ?_⟩
  · intro s a s' r _
    trivial
  · refine ⟨true, false, ?_, ?_⟩
    · intro a
      ext p
      exact ⟨fun _ => trivial, fun _ => trivial⟩
    · intro h
      have h1 := h ()
      have h2 : ((true, true) : Bool × Bool) ∈ StrongSig
          (fun s _ s' r => s = true ∧ s' = true ∧ r = true) true () :=
        ⟨rfl, rfl, rfl⟩
      have h3 : ((true, true) : Bool × Bool) ∈ StrongSig
          (fun s _ s' r => s = true ∧ s' = true ∧ r = true) false () := by
        rw [← h1]; exact h2
      obtain ⟨hs, _, _⟩ := h3
      exact Bool.noConfusion hs

/-- ⭐⭐ **反例 2**：`step ⊆ step'` ⟹ `StrongEquiv step ⊆ StrongEquiv step'` **假**。

**构造**：
- `step := ⊥`（**无**转移）
- `step'`：只有 `true` 的转移 `(true, a, true, true)`

**验证**：
- `step ⊆ step'` ✓
- **`StrongEquiv step true false`** ✓（两边签名**都空**）
- **`¬ StrongEquiv step' true false`** ✓
  （`StrongSig step' true a = {(true,true)}` 非空，`StrongSig step' false a = ∅`）

**⭐⭐ 与反例 1 合起来证明**：
**「签名相等」**不是**关于转移系统的单调谓词** ——
**两个方向都失败。** -/
theorem strongEquiv_mono_up_false :
    ∃ (step step' : Bool → Unit → Bool → Bool → Prop),
      (∀ s a s' r, step s a s' r → step' s a s' r) ∧
      (∃ s t, StrongEquiv step s t ∧ ¬ StrongEquiv step' s t) := by
  refine ⟨(fun _ _ _ _ => False),
          (fun s _ s' r => s = true ∧ s' = true ∧ r = true), ?_, ?_⟩
  · intro s a s' r h
    exact absurd h id
  · refine ⟨true, false, ?_, ?_⟩
    · -- `StrongEquiv ⊥ true false`：两边签名都空
      intro a
      ext p
      exact ⟨fun h => h, fun h => h⟩
    · -- `¬ StrongEquiv step' true false`
      intro h
      have h1 := h ()
      have h2 : ((true, true) : Bool × Bool) ∈ StrongSig
          (fun s _ s' r => s = true ∧ s' = true ∧ r = true) true () :=
        ⟨rfl, rfl, rfl⟩
      have h3 : ((true, true) : Bool × Bool) ∈ StrongSig
          (fun s _ s' r => s = true ∧ s' = true ∧ r = true) false () := by
        rw [← h1]; exact h2
      obtain ⟨hs, _, _⟩ := h3
      exact Bool.noConfusion hs

end StrongSignature

end Fate
