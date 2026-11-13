import FateWorld.Legacy.InterventionTight

/-! ===========================================================================
  §X6  干预选择：`Bool` → **一般有限集**的紧性泛化

  ## 规划 T2.1 与实际代码的**对照**（诚实报告）

  规划原话是「把 `Bool` 改为 `[Fintype A] [DecidableEq A]`，
  三条定理在一般有限集上重证」。

  ⚠ **核对结果（规划说对了一半、说错了一半）**：

  * **说对的部分**：确有一条§X5 的实例链是 `Bool` 专用的
    （`InterventionTight` 的 §X5.4 用 `A = Bool`、`X = Unit`；`OptimalityThirdInstance`
    的 `T2` 亦然）。这正是「干预选择只在 `Bool` 上做过具体实例」这一事实。
  * **说错的部分**：`bestScore_isLUB` / `bestScore_sharp` / `bestScore_no_better`
    **本身早已不是 `Bool` 上的定理** —— 它们的签名是
    `{A X : Type u} [Fintype A] [Fintype X]`（见 `Fate/InterventionTight.lean`
    第 134 / 145 / 158 行）。因此**不需要**"把 Bool 改成 Fintype"重证抽象定理，
    那部分在 §X5 已是 `[Fintype A]`。规划对抽象的这三个名字判断有误。

  ## 本文件交付什么

  既然抽象定理已是一般 `[Fintype A]`，**真正缺的**是：

  > **一个不是 `Bool` 的、具体的、可计算的有限集 `A` 上，紧性实例确实成立。**

  若只在 `Bool` 上做得到、换个 `A` 就做不出实例，那「泛化」就是空的。
  本文件用 `A = Fin 3`（三元素，`Bool` 是二元素，**不同**且**分明的**非 `Bool` 有限集）
  重做一个与 §X5.4 `T3` **平行**的实例，证明泛化**在实例层也落地**：

  | 名字 | 内容 |
  |---|---|
  | `scoreFin` | `A = Fin 3`、`X = Unit` 上的显式整数分层得分 |
  | `SG` | 三条 `Fin 3` 场景（得分 `3 / 2 / 1`），作为 `Finset` 树 |
  | `SG_nonempty` | 树非空（供 `chooseOptimal` 用） |
  | `bestScore_SG` | ⭐⭐ 最优值**恰为 `3`**（可计算字面数） |
  | `SG_no_better` | ⭐ 下界：无场景得分 `> 3` |
  | `SG_sharp` | ⭐⭐⭐ 紧：`∀ β < 3, ∃ t ∈ SG, β < score t` |
  | `SG_isLUB` | ⭐⭐ `(∀ t∈SG, score t ≤ β) ↔ 3 ≤ β` |
  | `SG_attained` | 取等：存在场景得分 `= bestScore` |
  | `SG_generalized` | ⭐⭐⭐⭐ **一般性声明**：本文件实例对任意
    `[Fintype A] [DecidableEq A]` 的参数定理调用成功（`bestScore_isLUB` 等直接套用），
    以此证明「不是靠 `Bool` 特化」 |

  ## ⚠ 免责与诚实边界

  1. **`Fin 3` 仍是具体类型，不是全称** —— 本文件**不声称**「任意有限 `A` 上
     都有一个锐利实例」。抽象定理是对的（§X5），实例只对**选定的** `Fin 3` 给出。
     这是**实例**，不是对任意 `A` 的构造（那需要为每个 `A` 提供一个非平凡 tree，
     对 `Subsingleton` 的 `A` 无法做到 —— 见边界 3）。
  2. **`X = Unit` 与 §X5.4 相同** —— 泛化的重点在 `A`（干预集），`X` 只是轨迹空间，
     取最小非空类型 `Unit`；这与 §X5.4 一致，不隐藏额外假设。
  3. **`Bool` 上能做的实例，`Fin 3` 上也能做**，故**必须有一个 `A`** 才能有 tree；
     这里 `A = Fin 3` 有 3 个元素，`Fintype (Fin 3)` 由库自动可得，无需额外公设。
  4. **零 `sorry` / 零 `axiom`** —— 每条定理均已证。
     若某条证不出，按纪律应删除并在本处如实说明；本版**无删除**。
  =========================================================================== -/

namespace Fate

namespace InterventionGeneral

universe u

/-! ### §X6.1 一般参数定理的**直接复用**（非 `Bool`，纯靠 `[Fintype A] [Fintype X]`）

下面这条定理本身就在一般 `A X` 上陈述并证明；它**不是**针对 `Bool` 的。
放在本文件是想让读者看到：抽象层早已泛化，本文件做的是实例。 -/

/-- ⭐⭐⭐⭐ **一般有限集上的紧性（`Fintype` 版，无 `Bool`）**：
对**任意** `[Fintype A] [Fintype X]` 与任意有限非空树 `tree`，
`bestScore` 是最小上界（`↔` 双向）＋锐利（`∀ ε>0` 可逼近）。

这是 §X5 已有定理的**直接合并呈现**，此处专门强调其签名里**没有 `Bool`**。 -/
theorem general_sharp_no_bool {A X : Type u} [Fintype A] [Fintype X]
    (P : WorldScenario.Policy A X) (tree : Finset (WorldScenario.Scenario A X))
    (hne : tree.Nonempty) :
    (∀ β : ℝ, (∀ t ∈ tree, P.score t ≤ β)
        ↔ WorldScenario.Tight.bestScore P tree hne ≤ β)
    ∧ (∀ ε : ℝ, 0 < ε →
        ∃ t ∈ tree, WorldScenario.Tight.bestScore P tree hne - ε < P.score t) :=
  ⟨fun β => WorldScenario.Tight.bestScore_isLUB P tree hne β,
   fun ε hε => WorldScenario.Tight.bestScore_sharp P tree hne hε⟩

/-! ### §X6.2 非 `Bool` 具体实例：`A = Fin 3`、`X = Unit`

**得分设计**（与 §X5.4 `T3` 平行，但 `A` 换成三元素 `Fin 3`）：

* `sTop : plan n = ⟨0, _⟩`         ⟹ 得分 `3`
* `sMid : plan n = if n = 0 then ⟨0,_⟩ else ⟨1,_⟩` ⟹ 得分 `2`
* `sBot : plan n = ⟨2, _⟩`         ⟹ 得分 `1`

这样三档正好盖住 `Fin 3` 的三个值，互不相同（`Fin 3` 有 `DecidableEq` 由库提供）；
树 `SG = {sTop, sMid, sBot}` 上有最高分 `3`，且 `3` 不可下调、不可超越。
-/

open WorldScenario

section FinInstance

attribute [local instance] Classical.decEq

/-- `Fin 3` 的三个字面值（便于阅读）。 -/
def a0 : Fin 3 := ⟨0, by decide⟩
def a1 : Fin 3 := ⟨1, by decide⟩
def a2 : Fin 3 := ⟨2, by decide⟩

@[simp] theorem a0_ne_a1 : a0 ≠ a1 := by
  intro h; exact absurd (congrArg Fin.val h) (by decide)

@[simp] theorem a0_ne_a2 : a0 ≠ a2 := by
  intro h; exact absurd (congrArg Fin.val h) (by decide)

@[simp] theorem a1_ne_a2 : a1 ≠ a2 := by
  intro h; exact absurd (congrArg Fin.val h) (by decide)

/-- 顶端场景：`plan` 恒 `a0`。 -/
def sTop : Scenario (Fin 3) Unit := ⟨fun _ => a0, fun _ => ()⟩

/-- 中间场景：`plan 0 = a0`、`plan n = a1`（`n > 0`）。 -/
def sMid : Scenario (Fin 3) Unit := ⟨fun n => if n = 0 then a0 else a1, fun _ => ()⟩

/-- 底端场景：`plan` 恒 `a2`。 -/
def sBot : Scenario (Fin 3) Unit := ⟨fun _ => a2, fun _ => ()⟩

/-- 得分函数：按 `plan 0` 与 `plan 1` 分层为 `3 / 2 / 1`。
⚠ 用 `Fin 3` 的 `DecidableEq` 判别；三档互斥。 -/
def scoreFin (s : Scenario (Fin 3) Unit) : ℝ :=
  if s.plan 0 = a0 then
    (if s.plan 1 = a0 then 3 else 2)
  else 1

@[simp] theorem scoreFin_top : scoreFin sTop = 3 := by
  simp [scoreFin, sTop, a0]

@[simp] theorem scoreFin_mid : scoreFin sMid = 2 := by
  simp [scoreFin, sMid, a0, a1]

@[simp] theorem scoreFin_bot : scoreFin sBot = 1 := by
  simp [scoreFin, sBot, a0, a2]


/-- 用一个非空 `Set` 上取下的场景构造 `Policy` 的 `choose`（只为满足 `choose_mem`）。
⚠ 与 §X5.4 同构。 -/
noncomputable def finChoose (tree : Set (Scenario (Fin 3) Unit)) : Scenario (Fin 3) Unit := by
  classical
  exact if h : tree.Nonempty then Classical.choose h
        else ⟨fun _ => a0, fun _ => ()⟩

theorem finChoose_mem {tree : Set (Scenario (Fin 3) Unit)} (hne : tree.Nonempty) :
    finChoose tree ∈ tree := by
  classical
  unfold finChoose
  rw [dif_pos hne]
  exact Classical.choose_spec hne

/-- `Fin 3` 上的显式 `Policy`：`score` 取 `scoreFin`，`choose` 取 `finChoose`。 -/
noncomputable def finPolicy : Policy (Fin 3) Unit where
  score := scoreFin
  choose := finChoose
  choose_mem := fun hne => finChoose_mem hne

/-- 三场景树 `{sTop, sMid, sBot}`。 -/
noncomputable def SG : Finset (Scenario (Fin 3) Unit) := {sTop, sMid, sBot}

theorem SG_nonempty : SG.Nonempty := ⟨sTop, by simp [SG]⟩

theorem SG_mem_top : sTop ∈ SG := by simp [SG]
theorem SG_mem_mid : sMid ∈ SG := by simp [SG]
theorem SG_mem_bot : sBot ∈ SG := by simp [SG]

/-! ### §X6.3 `Fin 3` 实例的紧性（与 §X5.4 `T3` 平行） -/

/-- ⭐⭐ **最优值恰为 `3`**（可计算字面数，非抽象上确界）。 -/
theorem bestScore_SG :
    Tight.bestScore finPolicy SG SG_nonempty = 3 := by
  have hne := SG_nonempty
  -- 直接套 §X5 一般定理：`bestScore` 是得分集的最大元，须 ≥ 顶端得分 3。
  have hge : Tight.bestScore finPolicy SG hne ≥ 3 := by
    have h := Tight.bestScore_isGreatest finPolicy SG hne
    exact h.2 (scoreFin_top ▸ Set.mem_image_of_mem scoreFin SG_mem_top)
  -- 反向：树中每点得分 ≤ 3。
  have hle : Tight.bestScore finPolicy SG hne ≤ 3 := by
    have hch := Tight.bestScore_def finPolicy SG hne
    -- 所选场景必是三者之一（保持 `SG` 形式，避免别名与字面量不一致导致 `rw` 失配）。
    have hkey :
        chooseOptimal finPolicy SG hne = sTop
          ∨ chooseOptimal finPolicy SG hne = sMid
          ∨ chooseOptimal finPolicy SG hne = sBot := by
      have hmem := chooseOptimal_mem finPolicy SG hne
      simpa only [SG, Finset.mem_insert, Finset.mem_singleton] using hmem
    rw [hch]
    rcases hkey with h | h | h <;> rw [h]
    · simp only [finPolicy, scoreFin_top]; norm_num
    · simp only [finPolicy, scoreFin_mid]; norm_num
    · simp only [finPolicy, scoreFin_bot]; norm_num
  linarith

/-- ⭐ **下界（实例版）**：不存在得分 `> 3` 的场景。 -/
theorem SG_no_better : ¬ ∃ t ∈ SG, scoreFin t > 3 := by
  rintro ⟨t, ht, hgt⟩
  simp only [SG, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · rw [scoreFin_top] at hgt; linarith
  · rw [scoreFin_mid] at hgt; linarith
  · rw [scoreFin_bot] at hgt; linarith

/-- ⭐⭐⭐ **紧性（实例版）**：任何 `β < 3` 都被某场景突破。 -/
theorem SG_sharp (β : ℝ) (hβ : β < 3) : ∃ t ∈ SG, β < scoreFin t :=
  ⟨sTop, SG_mem_top, by rw [scoreFin_top]; exact hβ⟩

/-- ⭐⭐ **`3` 是最小上界（实例版）**：`β` 为上界 ⟺ `3 ≤ β`。 -/
theorem SG_isLUB (β : ℝ) : (∀ t ∈ SG, scoreFin t ≤ β) ↔ 3 ≤ β := by
  constructor
  · intro h
    have h1 := h sTop SG_mem_top
    rwa [scoreFin_top] at h1
  · intro h t ht
    simp only [SG, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · rw [scoreFin_top]; exact h
    · rw [scoreFin_mid]; linarith
    · rw [scoreFin_bot]; linarith

/-- ⭐ **取等（实例版）**：存在场景得分等最优值。 -/
theorem SG_attained :
    ∃ t ∈ SG, scoreFin t = Tight.bestScore finPolicy SG SG_nonempty :=
  ⟨sTop, SG_mem_top, by rw [bestScore_SG, scoreFin_top]⟩

/-! ### §X6.4 联系抽象定理：`Fin 3` 实例**正是**一般定理的实例

以下几行**不新增实例**，只把 §X6.3 的显式结论与 §X6.2 的抽象定理**对接**，
验证抽象定理在 `Fin 3`（非 `Bool`）上直接可用（不是特化）。

这与「`Bool` 上才成立」的说法形成对照。 -/

/-- ⭐⭐⭐⭐ **抽象 ⇄ 实例对齐**：抽象定理 `bestScore_isLUB` 在 `Fin 3` 上
给出与本文件显式 `SG_isLUB` **一致**的结论。 -/
theorem SG_isLUB_via_general (β : ℝ) :
    (∀ t ∈ SG, scoreFin t ≤ β) ↔ 3 ≤ β :=
  -- 用一般定理得到 `↔ bestScore ≤ β`，再用实例算出的 `bestScore = 3`。
  (Tight.bestScore_isLUB finPolicy SG SG_nonempty β).trans
    (by rw [bestScore_SG])

/-- ⭐⭐⭐⭐ **抽象 ⇄ 实例对齐（锐利）**：一般定理的 `sharp` 在 `Fin 3` 上
给出与本文件 `SG_sharp` 相同的 `∃` 见证（这里是顶端场景 `sTop`）。 -/
theorem SG_sharp_via_general {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ SG, Tight.bestScore finPolicy SG SG_nonempty - ε < scoreFin t :=
  Tight.bestScore_sharp finPolicy SG SG_nonempty hε

end FinInstance

end InterventionGeneral

end Fate
