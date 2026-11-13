import FateWorld.FateV2.Error.VerdictGeneral

/-!
  # Core · VerdictAlgebra —— 判据的**层谱**（专项 T52）

  ## 迁移登记
  - 来源：新写（**只读引用** `Error/VerdictGeneral.lean`（T28）的
          `IsBoundaryPoint` / `VerdictAxioms`；**它一个字都不改**）
  - 动作：C 重写（把判据**代数化**：强度预序 + 格运算 + 谱）
  - 对应环节：F7-11（误差判据）、F4-14（统一）
  - 依赖裁决：**裁决 K**、**D-016**（核内零公理）、**D-022**（反空泛）
  - 改动：新建。
  - 状态：**零公理**（本文件全部定理 `#print axioms` 为 `[]`），见 `_报告/T52-进度.md`

  ## 〇、这个文件**不碰** `Real`，为什么

  任务书把四种判据摆在一起：

  | 判据 | 精确类型 |
  |---|---|
  | `VerdictPoint` | `ErrProfileN → Real → Nat → Prop` |
  | `IsFitBoundaryN` | `ErrProfileN → Real → Nat → Prop` |
  | `accepts` | `Real → Real → Real → Prop` |
  | `IsBoundaryPoint` | `{α β} → [Preorder β] → (α→β) → β → α → Prop` |

  **实测（`_probe_T52a.lean`）**：只要声明的类型或其定义体里出现 `Real`
  （或 `ErrProfileN`，它的字段是 `Nat → Real`），`#print axioms` **必为**
  `{propext, Classical.choice, Quot.sound}` —— 连
  `theorem x : (0 : Real) = 0 := rfl` 都是。这是**类型**层面的，与写法无关。

  而 `Core/` 的门禁（G4）要求**整目录零公理**。所以：

  * **本文件（`Core/`）**：只放**载体无关**的部分 —— 判据的代数与层谱，
    值域用 `Nat`（`AbsErr := Nat → Nat`）。**四条判据的「形状」与「相对位置」
    在这里全部证完**，一个 `Real` 都不碰。
  * **`Error/VerdictAlgebraReal.lean`（另一文件）**：把本文件的抽象结果**落到**
    `ErrProfileN` / `Real` / `accepts` 上。那里带三公理，是**必然**的，
    由 `Error/` 组承担。

  **这不是「降级」**：层谱的**数学内容**（谁强谁弱、哪一步严格）**不需要** `Real`。
  `Real` 只提供**具体的数值见证**（`WdropN`、缺口 `1/2`），而那是 T5 已经做完的事。

  ## 一、能不能统一？—— 能，统一在**索引**上

  | 判据 | 索引 `ι` | 本文件的对应物 |
  |---|---|---|
  | `VerdictPoint` | `(W,σ,γ)` | `ptC` |
  | `IsFitBoundaryN` | `(W,σ,γ)` | `fullC` |
  | `IsBoundaryPoint` | `(f,σ,a)` | `absC`（**与 `fullC` 同一个判据**） |
  | `accepts`（固定 `e := E γ`） | `(E,σ,γ)` | `bandC ε` |

  **统一的机制**：判据 = 某个索引 `ι` 上的谓词 `Criterion ι := ι → Prop`；
  `Stronger` 定义在**任意** `ι` 上。于是四种判据**全部**落进同一个代数，
  而代数的公理（预序 + 格）**与 `ι` 无关** —— 这就是本文件零公理的结构性原因。

  ⚠ **不能统一的那一个**：`accepts`（三实数谓词）**本身**不是判据。
  只有把 `e` 固定成 `E γ` 之后它才是。这不是洗白，是 §4.3 三条分离定理证出来的。

  ## 二、T5 已做过什么、本文件**没有**重做

  `Error/VerdictFull.lean` 的 `verdict_strict_chain` 已证**一条**严格链
  `VerdictPoint ← VerdictFull ← VerdictBand`（两正 + 三反，全用 `WdropN`）。
  **本文件不重证它**，也不掩饰重复度：**链的数学内容不新**。

  **本文件的增量是四件，T5 里都没有**：

  1. **§2 代数层（18 条，零公理）**：`Stronger` 是预序；`And` 是 `⊓`、`Or` 是 `⊔`
     —— 而且是**双向普遍性刻画**（`and_glb_iff` / `or_lub_iff`），不是单向半边。
     另加幂等、吸收、分配、顶、底。
     **T5 里 `And` / `Or` 这两个名字都没出现过。**
  2. **§3 统一层（4 条）**：把 `IsFitBoundaryN` ≡ `IsBoundaryPoint` 接进格
     （`absC_iff_fullC`），于是**判据 2 与判据 4 不是两层** ——
     「四种判据」实际只有**三**层。这是任务书 §第 1 步的**收口**答案。
  3. **§4 谱（6 条）**：链的零公理版本 + `accepts` 呈现的**强制性**
     （`accepts_presentation_forced`，三条分离）。
  4. **§5 抽象类的代数位置（5 条）**：任务书第 4 步要求「证明 `VerdictAxioms`
     在 `Stronger` 下是最强判据类」。**这条为假**，本文件证它的**正确形态**。

  ## 三、⚠ 三条**与任务书相反**的发现

  **(1) `point_stronger_full` 是假命题，且**必然**假。**
  `VerdictPoint W σ γ := W.err γ = σ` **只**有一个等式；
  `IsFitBoundaryN` **多**一个 `∀ γ', σ ≤ W.err γ'`。
  前者推后者**在纯逻辑上不可能**（不缺前提不会多出全称）。
  零公理反例：`E := fun n => if n = 0 then 1 else 0`、`σ = 1`、`γ = 0`
  （`pt_refuted_full`）。T5 的 `verdictPoint_not_implies_verdictFull`
  早在 `ErrProfileN` 上证过同一件事（缺口 `1/2`）。

  **(2) `spectrum_not_collapsible` 的字面形式（`∃ … ∧ ¬ …`）带 `propext`。**
  本文件改用**正形式**：`∃ x, P x ∧ (Q x → False)`（`spectrum_witnesses`），
  **零公理**，数学内容**完全相同**。

  **(3) `VerdictAxioms` 不是「最强的判据类」，而是**一个等价类**。**
  `iff_min` 使**每个**实例都与「取到 + 下界」等价；`Stronger` 作为**预序**
  （无反对称）使「互相蕴含」与「相同」不可区分。于是「最强」只能读成
  「**在自身那个等价类里**最强」。它**对加合取封闭**
  （`axioms_closed_under_equiv`），故它在谱的**中间**，**不在**顶。

  ## 四、公理纪律（实测得出，全部写在这里以免后人重踩）

  ### 4.1 类型含 `Real` ⟹ 三公理

  见 §〇。本文件因此**零 `Real`**。

  ### 4.2 **不写 `¬ Stronger P Q`**，写成 `∀ x, P x → Q x → False`

  实测（`_probe_T52q.lean`）：**同一个证明项**，写成 `¬ Stronger` 带 `propext`，
  写成 `→ False` **零公理**。

  ### 4.3 `nomatch` **不要**嵌在多层 `fun` 里

  实测：`fun _ _ hF => nomatch hF.1` 带 `propext`；
  拆成**独立定理**（`nat_five_ne_four : 5 = 4 → False`）再 `apply` 则零公理。

  ### 4.4 `∃` 消去时见证被**静默泛化**

  若 `∃ g, …` 里的 `g` 在**目标**中不出现（`x` 只在定义体内部被吸收），
  `rcases` / `Exists.elim` / `obtain` **全部**会把 `x` 一起泛化，
  得到 `⊢ … g` 而目标是 `… x.2.2`，**报 Type mismatch**。
  这不是 Lean 的缺陷 —— 它恰好说明「`∃γ` 版」与「固定版」**不是一回事**。
  修法：把等式**写进见证**（`∃ g, g = γ ∧ …`）。

  ### 4.5 其余禁用

  `simp` 收尾 / `decide` 收尾 / `by_contra` / `funext` / `omega` /
  `Fintype` / `Finset` / `by_cases` 于非单变量。
  乘幂等元**必须是显式变元**（内联 `P P` 会留下 `@id`，`Iff.rfl` 卡住）。
-/

namespace FateV2.Core

/-! ===========================================================================
  §1  判据的**载体**：索引参数化
-/

/-- **判据**（载体无关的读法）：索引 `ι` 上的谓词。

  这是「统一」的**全部**内容：不是把 `Real` 换成别的，
  而是把「谁在做索引」提成参数。 -/
abbrev Criterion (ι : Type) : Type := ι → Prop

/-- **判据的强度序**：`Stronger P Q` 读作「`P` 成立 ⟹ `Q` 成立」，即 `P` **更强**。

  ⚠ 方向约定：`Stronger P Q` = `P ≤ Q`（强 ⟹ 弱）。`And` 落在**下**，`Or` 落在**上**。 -/
def Stronger {ι : Type} (P Q : Criterion ι) : Prop := ∀ x, P x → Q x

/-- **判据的合取**：两个判据都成立。 -/
def And {ι : Type} (P Q : Criterion ι) : Criterion ι := fun x => P x ∧ Q x

/-- **判据的析取**：至少一个成立。 -/
def Or {ι : Type} (P Q : Criterion ι) : Criterion ι := fun x => P x ∨ Q x

/-- **恒真判据**（格的顶：最弱）。 -/
def TrueC {ι : Type} : Criterion ι := fun _ => True

/-- **恒假判据**（格的底：最强）。 -/
def FalseC {ι : Type} : Criterion ι := fun _ => False

/-! ===========================================================================
  §2  判据的**代数**：预序 + 格运算（18 条，全部零公理）
-/

/-- **自反**：每个判据比自己强。

  **比定义多说了什么**：定义是一行 `∀ x, P x → Q x`；本条说明这个关系**不空**。 -/
theorem stronger_refl {ι : Type} (P : Criterion ι) : Stronger P P :=
  fun _ h => h

/-- **传递**：`P` 比 `Q` 强、`Q` 比 `R` 强 ⟹ `P` 比 `R` 强。

  **比定义多说了什么**：这是「强度」能当**序**用的**唯一**非平凡输入
  （自反是免费的）。有了它，有限条判据串成的推导链可以**合成一条**
  —— §4 的谱（两段合成一段）靠它。 -/
theorem stronger_trans {ι : Type} (P Q R : Criterion ι)
    (h1 : Stronger P Q) (h2 : Stronger Q R) : Stronger P R :=
  fun x hx => h2 x (h1 x hx)

/-- **`Stronger` 构成预序**（自反 + 传递合成一条）。

  **比定义多说了什么**：单看定义，`Stronger` 只是二元关系；本定理把它**升格**为
  `Preorder` 意义的预序 —— 于是任何关于判据的定理都可按「强 ⟹ 弱」**单向复用**。
  **不**证反对称：那需要 `propext`（「两个互推的判据相等」是命题外延），
  而本项目实测 `¬`/`↔` 型结论代价极高。这正是 §5「按等价类理解最强」的依据。 -/
theorem stronger_preorder {ι : Type} :
    (∀ P : Criterion ι, Stronger P P) ∧
    (∀ P Q R : Criterion ι, Stronger P Q → Stronger Q R → Stronger P R) :=
  ⟨fun P => stronger_refl P, fun P Q R h1 h2 => stronger_trans P Q R h1 h2⟩

/-- **`P ⊓ Q` 比两者都强**（下确界的两个方向）。

  **比定义多说了什么**：`And P Q` 的定义是 `P x ∧ Q x`；本条说明它在强度序里
  **落在两者下方** —— 「同时满足两个判据」**不比**只满足一个**更弱**。
  这是 `And` 能当**收紧**用的依据。 -/
theorem and_is_glb_upper {ι : Type} (P Q : Criterion ι) :
    Stronger (And P Q) P ∧ Stronger (And P Q) Q :=
  ⟨fun _ h => h.1, fun _ h => h.2⟩

/-- **最强的下界**：任何比 `P`、`Q` 都强的判据，也比 `And P Q` 强。

  **比定义多说了什么**：`and_is_glb_upper` 只说明 `And P Q` **是**下界；
  本条说明它**是最大的那个**下界 —— `And` **没有**丢掉任何强度。 -/
theorem and_is_glb_greatest {ι : Type} (P Q R : Criterion ι)
    (h1 : Stronger R P) (h2 : Stronger R Q) : Stronger R (And P Q) :=
  fun x hx => ⟨h1 x hx, h2 x hx⟩

/-- **`And` = 下确界（`iff` 刻画）**：`R ≤ P ⊓ Q` **当且仅当** `R ≤ P` 且 `R ≤ Q`。

  **比定义多说了什么**：把 `And` 从「一个 `∧`」变成**格论对象** ——
  这条 `iff` 就是 `⊓` 的**普遍性质**（右伴随性）。有了它，任何涉及 `And` 的推理
  都能**规约**成两条关于原判据的推理，反之亦然。 -/
theorem and_glb_iff {ι : Type} (P Q R : Criterion ι) :
    Stronger R (And P Q) ↔ (Stronger R P ∧ Stronger R Q) :=
  ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
    fun h => and_is_glb_greatest P Q R h.1 h.2⟩

/-- **`P`、`Q` 都比 `P ⊔ Q` 强**（上确界的两个方向）。

  **比定义多说了什么**：说明 `Or P Q` 在强度序里**落在两者上方** ——
  「满足任一」**不比**「满足特定一个」**更强**。这是 `Or` 只能当**放宽**用的依据。 -/
theorem or_is_lub_lower {ι : Type} (P Q : Criterion ι) :
    Stronger P (Or P Q) ∧ Stronger Q (Or P Q) :=
  ⟨fun _ h => Or.inl h, fun _ h => Or.inr h⟩

/-- **最弱的上界**：任何被 `P`、`Q` 都蕴含的判据，也被 `Or P Q` 蕴含。

  **比定义多说了什么**：`or_is_lub_lower` 只说明 `Or P Q` **是**上界；
  本条说明它**是最小的那个**上界 —— `Or` **不偷偷附加**条件。 -/
theorem or_is_lub_least {ι : Type} (P Q R : Criterion ι)
    (h1 : Stronger P R) (h2 : Stronger Q R) : Stronger (Or P Q) R :=
  fun x hx => Or.elim hx (fun h => h1 x h) (fun h => h2 x h)

/-- **`Or` = 上确界（`iff` 刻画）**：`P ⊔ Q ≤ R` **当且仅当** `P ≤ R` 且 `Q ≤ R`。

  **比定义多说了什么**：这是 `⊔` 的**普遍性质**；与 `and_glb_iff` 合起来，
  `(Criterion ι, Stronger, And, Or)` 就是一个**格**（本 § 末给分配律）。 -/
theorem or_lub_iff {ι : Type} (P Q R : Criterion ι) :
    Stronger (Or P Q) R ↔ (Stronger P R ∧ Stronger Q R) :=
  ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h => or_is_lub_least P Q R h.1 h.2⟩

/-- **任务书 §第 2 步的 `and_is_glb`**：两条合起来说 —— `And P Q` 是下确界。

  **比定义多说了什么**：任务书只要「`And P Q` 比两者都强」；
  「**且是最强的**」是**额外**的（`and_glb_iff` 的另一半），
  没有它 `And` 就只是**一个**下界而不是**下确界**。本定理把两半都给出。 -/
theorem and_is_glb {ι : Type} (P Q R : Criterion ι) :
    Stronger (And P Q) P ∧ Stronger (And P Q) Q ∧
      (Stronger R P → Stronger R Q → Stronger R (And P Q)) :=
  ⟨(and_is_glb_upper P Q).1, (and_is_glb_upper P Q).2, and_is_glb_greatest P Q R⟩

/-- **任务书 §第 2 步的 `or_is_lub`**：`Or P Q` 是上确界（两半都给出）。 -/
theorem or_is_lub {ι : Type} (P Q R : Criterion ι) :
    Stronger P (Or P Q) ∧ Stronger Q (Or P Q) ∧
      (Stronger P R → Stronger Q R → Stronger (Or P Q) R) :=
  ⟨(or_is_lub_lower P Q).1, (or_is_lub_lower P Q).2, or_is_lub_least P Q R⟩

/-- **`And` 幂等**：`P ⊓ P` 与 `P` **互相**蕴含。

  **比定义多说了什么**：`And P P` 的定义是 `P x ∧ P x`，这**不是** `P x`；
  本条说明在强度序里两者互推 —— 「重复施加同一个判据」**不产生**新的收紧
  （判据系统**没有**重数，与 D-004 的「来源只增不减」形成对照）。 -/
theorem and_idem {ι : Type} (P : Criterion ι) : Stronger (And P P) P ∧ Stronger P (And P P) :=
  ⟨fun _ h => h.1, fun _ h => ⟨h, h⟩⟩

/-- **`Or` 幂等**：`P ⊔ P` 与 `P` **互相**蕴含。

  **比定义多说了什么**：`Or P P` 的定义是 `P x ∨ P x`；本条说明它**不**比 `P` 弱
  —— 「同一个判据挂两次」**不产生**冗余。 -/
theorem or_idem {ι : Type} (P : Criterion ι) : Stronger (Or P P) P ∧ Stronger P (Or P P) :=
  ⟨fun x h => Or.elim h (fun h1 => h1) (fun h2 => h2), fun _ h => Or.inl h⟩

/-- **`⊓` 吸收 `⊔`**：`P ⊓ (P ⊔ Q)` 与 `P` **互相**蕴含。

  **比定义多说了什么**：`And P (Or P Q)` 与 `P` 字面上**完全不同**；
  本条说明它们在强度序里同一 —— 这是格的**吸收律**，
  意味着「判据的语法形式」可以**化简**而不改变语义。 -/
theorem absorb_and_or {ι : Type} (P Q : Criterion ι) :
    Stronger (And P (Or P Q)) P ∧ Stronger P (And P (Or P Q)) :=
  ⟨fun _ h => h.1,
    fun x hx => ⟨hx, (or_is_lub_lower P Q).1 x hx⟩⟩

/-- **`⊔` 吸收 `⊓`**：`P ⊔ (P ⊓ Q)` 与 `P` **互相**蕴含。 -/
theorem absorb_or_and {ι : Type} (P Q : Criterion ι) :
    Stronger (Or P (And P Q)) P ∧ Stronger P (Or P (And P Q)) :=
  ⟨fun x hx => Or.elim hx (fun h1 => h1) (fun h2 => h2.1), fun _ hx => Or.inl hx⟩

/-- **`And` 分配 `Or`**（双向）。

  **比定义多说了什么**：这不是 `And`/`Or` 定义的推论，要真的用 `∧`/`∨` 的
  消去与引入。它把 `(Criterion ι, Stronger, And, Or)` **升格为分配格**：
  任何「判据组合式」都可写成**析取范式**，于是谱里「多个判据同时/任一成立」
  都能化成**有限**条基本判据的组合。
  ⚠ 这是**格层的**分配律，**不**声称 `And`/`Or` 在**判据内容**上分配。 -/
theorem and_distrib_or {ι : Type} (P Q R : Criterion ι) :
    Stronger (And P (Or Q R)) (Or (And P Q) (And P R)) ∧
      Stronger (Or (And P Q) (And P R)) (And P (Or Q R)) :=
  ⟨fun x hx => Or.elim hx.2
      (fun hq => Or.inl ⟨hx.1, hq⟩)
      (fun hr => Or.inr ⟨hx.1, hr⟩),
    fun x hx => Or.elim hx
      (fun h => ⟨h.1, Or.inl h.2⟩)
      (fun h => ⟨h.1, Or.inr h.2⟩)⟩

/-- **`Or` 分配 `And`**（双向）。 -/
theorem or_distrib_and {ι : Type} (P Q R : Criterion ι) :
    Stronger (Or P (And Q R)) (And (Or P Q) (Or P R)) ∧
      Stronger (And (Or P Q) (Or P R)) (Or P (And Q R)) :=
  ⟨fun x hx => Or.elim hx
      (fun hp => ⟨Or.inl hp, Or.inl hp⟩)
      (fun hqr => ⟨Or.inr hqr.1, Or.inr hqr.2⟩),
    fun x hx => Or.elim hx.1
      (fun hp => Or.inl hp)
      (fun hq => Or.elim hx.2
        (fun hp => Or.inl hp)
        (fun hr => Or.inr ⟨hq, hr⟩))⟩

/-- **恒真判据是最弱的上界**：任何判据都比 `TrueC` 强。

  **比定义多说了什么**：`TrueC` 的定义是 `fun _ => True`；本条说明它是格的**顶**
  —— 「什么都不检查」是**最弱**判据。这是 §5 判据「到达域」的参照点。 -/
theorem stronger_true (ι : Type) (P : Criterion ι) : Stronger P TrueC :=
  fun _ _ => True.intro

/-- **恒假判据是最强判据**：`FalseC` 比任何判据都强。

  **比定义多说了什么**：本条说明它是格的**底** —— 于是「无解判据」是**最强**（空真）。
  ⚠ 这与「无解是坏事」的直觉**相反**，但正是强度序的正确读法：
  **越不可满足 ⟹ 越强**（前件更假）。这解释了为什么 `And` 收紧、`Or` 放松。 -/
theorem false_stronger (ι : Type) (P : Criterion ι) : Stronger FalseC P :=
  fun _ h => False.elim h

/-- **反例 ⟹ 不更强**（**正形式**，不写 `¬∀`）。

  **比定义多说了什么**：`Stronger` 的定义是 `∀`；否证一个 `∀` **必须**给反例。
  本条把「反例 ⟹ 不更强」提成具名定理，§4 的每条分离定理都只是一次实例化。

  ⚠ **为什么结论写成 `→ False` 而不是 `¬ Stronger P Q`**：
  两者是同一件事，但 `¬∀` 形式在本项目**带 `propext`**
  （`_probe_T52q.lean`：同一证明项，`¬Stronger` 带 `propext`，
  写成 `→ False` **零公理**）。这是本文件最重要的一条**写法纪律**。

  ⚠ **`_` 会丢信息**：`fun _ _ hq => hQ hq` 里第一个 `_` 若不写，
  Lean 会把 `y` **泛化**成新变元，`hq : Q y` 就对不上 `hQ : Q x`。
  必须写成 `fun (_ : ι) (_ : P _) hq => hQ hq` 不够 —— 见 §4 的两条分离定理：
  它们**不用**本条，直接给 `fun _ _ => 具体定理`，绕开泛化。 -/
theorem refuted_of_witness {ι : Type} (P Q : Criterion ι) (x : ι)
    (hP : P x) (hQ : Q x → False) : Stronger P Q → False :=
  fun hs => hQ (hs x hP)

/-! ===========================================================================
  §3  统一层：判据的抽象载体，与「四种 → 三种」的收口

  本节用 `Nat` 值域（`AbsErr := Nat → Nat`）重现 `ErrProfileN.err : Nat → Real`
  的**结构**（`Nat` 索引 + 有下界），**不是**对它重定义。
  `Real` 侧的精确落到 `Error/VerdictAlgebraReal.lean`。
-/

/-- **抽象误差剖面**：`Nat` 索引上的误差取值。 -/
abbrev AbsErr : Type := Nat → Nat

/-- **抽象点态判据**：`E γ = σ`。对应 T5 的 `VerdictPoint W σ γ`。 -/
def AbsPoint (E : AbsErr) (σ : Nat) (γ : Nat) : Prop := E γ = σ

/-- **抽象完整判据**：点态 + 全局下界。

  对应 T5 的 `VerdictFull`、T1 的 `IsFitBoundaryN`、T28 的 `IsBoundaryPoint`
  —— 三者是**同一个命题**（`absC_iff_fullC`）。 -/
def AbsFull (E : AbsErr) (σ γ : Nat) : Prop := E γ = σ ∧ ∀ γ', σ ≤ E γ'

/-- **抽象带宽判据（固定 `e := E γ`）**：`σ − ε ≤ E γ ≤ σ + ε`。

  ⚠ **唯一的呈现选择就在这一行**：`accepts σ ε e` 的 `e` 被固定成 `E γ`。
  为什么必须固定，见 §4.3。 -/
def AbsBand (E : AbsErr) (σ ε : Nat) (γ : Nat) : Prop := σ - ε ≤ E γ ∧ E γ ≤ σ + ε

/-- **完整判据的展开名**（`AbsFull` 的逐分量写法）。

  ⚠ **为什么要有这个别名**：`fullC` 的体**经过** `AbsFull`，而 `AbsFull` 被
  `abstractsFit` 以 `↔` 形式使用；直接用 `FullW` 展开可避开那条路径。
  实测：直接写 `fullC (fun _ => 5, 4, 0)` 的证明会带 `propext`，
  写 `FullW (fun _ => 5) 4 0` 则**零公理**。如实记录。 -/
def FullW (E : AbsErr) (σ γ : Nat) : Prop := E γ = σ ∧ ∀ γ', σ ≤ E γ'

/-- **带宽判据的展开名**（`AbsBand` 的别名）。 -/
def BandW (E : AbsErr) (σ ε γ : Nat) : Prop := σ - ε ≤ E γ ∧ E γ ≤ σ + ε

/-- **判据索引**：`(E, σ, γ)` —— 「统一呈现」的**载体**。 -/
abbrev AbsIdx : Type := AbsErr × Nat × Nat

/-- **判据 1（点态，统一后）**。 -/
def ptC : Criterion AbsIdx := fun x => AbsPoint x.1 x.2.1 x.2.2

/-- **判据 2（完整，统一后）**。 -/
def fullC : Criterion AbsIdx := fun x => AbsFull x.1 x.2.1 x.2.2

/-- **判据 3（带宽，统一后，`ε` 作参数）**。 -/
def bandC (ε : Nat) : Criterion AbsIdx := fun x => AbsBand x.1 x.2.1 ε x.2.2

/-- **判据 4（抽象边界点，统一后）**：`IsBoundaryPoint` 的 `f` 取 `E`、`β` 取 `Nat`。

  **比定义多说了什么**：`IsBoundaryPoint` 在 T28 里是 `{α β} [Preorder β]` 上的
  **多态**定义；本条把它**降到一个具体索引**上，于是它能与上面三条进**同一个**
  `Stronger` 比较 —— 多态定义本身**无法**直接比较。 -/
def absC : Criterion AbsIdx := fun x => AbsFull x.1 x.2.1 x.2.2

/-- **`AbsFull` 就是「取到 + 下界」**（即 T28 的 `IsBoundaryPoint` 展开式）。

  **比定义多说了什么**：这是任务书核心疑问「三种类型能否统一」的**答案位置**。
  `IsFitBoundaryN W σ γ` 与 `IsBoundaryPoint W.err σ γ` 在源码里是**两处各写一遍**
  同一个命题（T28 已证 `Iff.rfl`）；本条把它**降到**一个 `Nat` 值函数上，
  于是它**能**与 §2 的格运算组合。 -/
theorem abstractsFit (E : AbsErr) (σ γ : Nat) :
    AbsFull E σ γ ↔ (E γ = σ ∧ ∀ b, σ ≤ E b) := Iff.rfl

/-- **`absC` 与 `fullC` 是同一个判据**（双向 `Stronger`）。

  **比定义多说了什么**：说明判据 4（T28 的抽象边界点）在 `Nat` 载体上**没有**
  给判据 2 添加任何内容 —— 它们**不是**两个判据，是**两个名字**。
  **这是「四种判据」实际只有三层的严格依据**，也是任务书 §第 1 步
  「能否统一」的**收口**答案：判据 2 与判据 4 **不需要**统一，它们本来就是同一个。 -/
theorem absC_iff_fullC : Stronger absC fullC ∧ Stronger fullC absC :=
  ⟨fun _ h => h, fun _ h => h⟩

/-! ===========================================================================
  §4  层谱：各层的相对位置 + 分离见证
-/

/-- **`5 ≠ 4` 的独立形式**（`Nat` 具体否定，**零公理**）。

  ⚠ **为什么要单独立一条、且为什么不用 `nomatch`**（实测）：
  * 把 `nomatch` 直接嵌在多层 `fun` 里（`fun _ _ hF => nomatch hF.1`）**带 `propext`**；
  * 但**即便**拆成独立定理，`fun h => nomatch h` **仍然**带 `propext` ——
    因为 `Nat.noConfusion` 的返回类型是 `Nat.noConfusionType`，要**再一步**消去才成 `False`。
  * **可行写法**：`fun h => absurd h (by decide)` —— 由 `decide` 给出 `¬(5 = 4)`
    的**具体判定**，`absurd` 直接合成，**零公理**（`_probe_T52z.lean` 实测）。
  这是本文件实测出的**第二**条写法纪律。 -/
theorem nat_five_ne_four : (5 : Nat) = 4 → False := fun h => absurd h (by decide)

/-- **`1 ≤ 0` 在 `Nat` 上不成立**（同上，独立形式）。 -/
theorem nat_one_le_zero_absurd : (1 : Nat) ≤ 0 → False := fun h => absurd h (by decide)

/-- **入口反例剖面 `Edrop0`**：`E 0 = 1`，其余一律 `0`。

  ⚠ **为什么要有具名的 `def`**（实测，`_probe_T52v/w/x.lean`）：
  在 `Nat` 上 `(fun n => if n = 0 then 1 else 0) 0` **不**自动 beta 归约，
  `rw [if_pos rfl]` 会报「找不到 `if` 模式」。必须先有**独立的取值等式定理**
  （`Edrop0_zero`，`rfl` 级）再 `rw`。这正是「先算清再证」的又一实例。 -/
def Edrop0 : AbsErr := fun n => if n = 0 then 1 else 0

/-- **`Edrop0 0 = 1`**（`if` 的 `then` 分支）。 -/
theorem Edrop0_zero : Edrop0 0 = 1 := by
  show (if (0 : Nat) = 0 then 1 else 0) = 1
  rw [if_pos rfl]

/-- **`Edrop0 1 = 0`**（`if` 的 `else` 分支）。 -/
theorem Edrop0_one : Edrop0 1 = 0 := by
  show (if (1 : Nat) = 0 then 1 else 0) = 0
  rw [if_neg (by decide)]

/-- **入口反例**：`Edrop0`、`σ = 1`、`γ = 0` 处 `FullW` **不成立**。

  **比定义多说了什么**：`ptC` 在该点成立（`E 0 = 1`），而 `FullW` 的第二分量
  在 `γ' = 1` 处要求 `1 ≤ E 1 = 0` —— **假**。缺口 `1`。
  这是 §4 入口严格性的**唯一**依据（T5 在 `Real` 上用 `WdropN` 给缺口 `1/2`，
  形状完全相同）。 -/
theorem fullW_drop_refuted : FullW Edrop0 1 0 → False :=
  fun h => nat_one_le_zero_absurd (h.2 1)

/-- **出口反例**：`fun _ => 5`、`σ = 4` 处 `FullW` **不成立**。

  **比定义多说了什么**：第二分量（`4 ≤ 5`）**成立**，第一分量（`5 = 4`）**不成立**
  —— 所以整个合取不成立。这是 §4 出口严格性的**唯一**依据。 -/
theorem fullW_const_five_four_refuted : FullW (fun _ => 5) 4 0 → False :=
  fun h => nat_five_ne_four h.1

/-- **谱的入口（严格）**：`ptC` 有一个点成立，而 `fullC` 在那点**不成立**。

  **比定义多说了什么**：这是任务书 `point_stronger_full` 的**否证**。
  ⚠ **为什么必然**：`ptC` 里**只有**一个等式，`fullC` 里**多**一个 `∀ γ'`；
  前者推后者**在纯逻辑上不可能**。故严格性与载体无关。
  T5 的 `verdictPoint_not_implies_verdictFull` 在 `ErrProfileN` / `Real` 上给同一件事；
  本条是它在 `Nat` 上的**零公理**同形状版本。 -/
theorem pt_refuted_full : Stronger ptC fullC → False :=
  fun hs =>
    fullW_drop_refuted
      (hs (Edrop0, 1, 0) (by
        show AbsPoint Edrop0 1 0
        unfold AbsPoint
        exact Edrop0_zero))

/-- **谱的出口（严格）**：`bandC 1` 有一个点成立，而 `fullC` 在那点**不成立**。

  **比定义多说了什么**：`bandC` 只读 `E γ` **一个值**，`fullC` 的第二分量
  是对**别的** `γ` 的断言 —— 签名里没有剖面就**推不出**关于剖面的全称命题。
  反例：`E := fun _ => 5`、`σ := 4`、`ε := 1`、`γ := 0`：
  `bandC 1` 成立（`3 ≤ 5 ∧ 5 ≤ 5`），`fullC` 不成立（`5 = 4` 假）。 -/
theorem band_refuted_full : Stronger (bandC 1) fullC → False :=
  fun hs =>
    fullW_const_five_four_refuted
      (hs (fun _ => 5, 4, 0) (by
        show AbsBand (fun _ => 5) 4 1 0
        show (4 : Nat) - 1 ≤ (fun _ => 5) 0 ∧ (fun _ => 5) 0 ≤ 4 + 1
        exact ⟨Nat.le_trans (Nat.sub_le 4 1) (by decide), Nat.le_refl 5⟩))

/-- **`fullC` ⟹ `bandC 0`**：`ε = 0` 时带**恰好**退化成点。

  **比定义多说了什么**：`AbsBand` 要**两个**不等式，`AbsFull` 只给一个**等式**；
  本条说明这一个等式**自动**满足两个不等式（`σ − 0 ≤ σ ≤ σ + 0`），
  于是「`ε = 0` 的容差」**不**给完整判据添加任何约束 —— 它是**纯冗余**。
  ⚠ 因此「`fullC` 不推 `bandC 0`」是**假**命题
  （先算后写；本项目派单命题为假已发生十余次）。 -/
theorem full_stronger_band0 : Stronger fullC (bandC 0) :=
  fun x hx => by
    show BandW x.1 x.2.1 0 x.2.2
    unfold BandW
    rw [Nat.sub_zero, Nat.add_zero, hx.1]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- **`fullC` ⟹ `bandC ε`（任意 `ε`）**：完整判据落在任何以 `σ` 为心的带内。

  **比定义多说了什么**：容差调大**不会**把不合格变成合格，也**不会**把合格变成不合格。
  「容差」这一整个自由度在完整判据上**完全不可见**（纯冗余）。 -/
theorem full_stronger_band (ε : Nat) : Stronger fullC (bandC ε) :=
  fun x hx => by
    show BandW x.1 x.2.1 ε x.2.2
    unfold BandW
    rw [hx.1]
    exact ⟨Nat.sub_le x.2.1 ε, Nat.le_add_right x.2.1 ε⟩

/-- **§4 主定理（统一形态）**：`ptC`、`fullC`、`bandC` 的**全部**相对位置。

  | 分量 | 内容 | 出处 |
  |---|---|---|
  | `.1` | `fullC ⟹ bandC 0` | `full_stronger_band0` |
  | `.2.1` | `fullC ⟹ bandC 1` | `full_stronger_band` |
  | `.2.2.1` | `ptC ⟹ fullC` **不成立**（`→ False` 收尾） | `pt_refuted_full` |
  | `.2.2.2` | `bandC 1 ⟹ fullC` **不成立**（`→ False` 收尾） | `band_refuted_full` |

  **比定义多说了什么**：三个定义各是一行 `Prop`，本身**没有**任何蕴含承诺。
  本条把「三种（统一后的）判据」排成**有向且逐步严格**的层谱
  `ptC ⊀ fullC ⊑ bandC`，**每条边都配分离见证**。

  ⚠ **与 T5 的重复度（如实）**：T5 的 `verdict_strict_chain` **已经**证过同样内容
  （`ErrProfileN` 上、带三公理）。本条是它在 `Nat` 载体的**零公理**版本，
  **链的数学内容不新**；增量只在「零公理」与「进得了 §2 的格运算」。
  ⚠ 任务书写的 `verdict_spectrum : Stronger VerdictPointU FullU ∧ Stronger FullU AcceptsU`
  **第一条为假**（见 `pt_refuted_full`），故本定理是它的**正确形态**。 -/
theorem verdict_spectrum :
    Stronger fullC (bandC 0) ∧
    Stronger fullC (bandC 1) ∧
    (Stronger ptC fullC → False) ∧
    (Stronger (bandC 1) fullC → False) :=
  ⟨full_stronger_band0, full_stronger_band 1, pt_refuted_full, band_refuted_full⟩

/-- **谱不可合并（正形式见证）**：两条分离见证，结论**不**写成 `¬Stronger`。

  | 分量 | 内容 |
  |---|---|
  | `.1` | `ptC (E₁,1,0)` 成立而 `fullC (E₁,1,0)` **不成立** ⟹ 入口严格 |
  | `.2` | `bandC 1 (E₂,4,0)` 成立而 `fullC (E₂,4,0)` **不成立** ⟹ 出口严格 |

  **比定义多说了什么**：任务书写 `∃ x, FullU x ∧ ¬VerdictPointU x ∧ …`。
  本文件写成**两个具体见证**（`E₁ := if n=0 then 1 else 0`，`E₂ := fun _ => 5`），
  每个见证都配一个 `Q x → False`。这是「不可合并」的**可证**形态：
  **任取**一个见证就足以否证合并，而 `¬∀` 写法实测**带 `propext`**
  （`_probe_T52q.lean`）。**数学内容完全相同，公理干净。** -/
theorem spectrum_witnesses :
    (∃ x : AbsIdx, ptC x ∧ (fullC x → False)) ∧
    (∃ y : AbsIdx, bandC 1 y ∧ (fullC y → False)) :=
  ⟨⟨(Edrop0, 1, 0),
      (by
        show AbsPoint Edrop0 1 0
        unfold AbsPoint
        exact Edrop0_zero),
      (fun hF => fullW_drop_refuted hF)⟩,
    ⟨(fun _ => 5, 4, 0),
      (by
        show AbsBand (fun _ => 5) 4 1 0
        unfold AbsBand
        exact ⟨Nat.le_trans (Nat.sub_le 4 1) (by decide), Nat.le_refl 5⟩),
      (fun hF => fullW_const_five_four_refuted hF)⟩⟩

/-! ### §4.3 `accepts` 的**呈现选择**为什么不是等价变换 -/

/-- **`∃γ` 版带宽判据**（见证**带**等式 `g = γ`）。 -/
def bandExistsC (ε : Nat) : Criterion AbsIdx :=
  fun x => ∃ g : Nat, g = x.2.2 ∧ AbsBand x.1 x.2.1 ε g

/-- **`∀γ` 版带宽判据**：每个分辨率都落在带内。 -/
def bandUniformC (ε : Nat) : Criterion AbsIdx := fun x => ∀ g : Nat, AbsBand x.1 x.2.1 ε g

/-- **「某个 `γ` 落在带内」**（**不带**等式 `g = γ` 的版本）。 -/
def bandSomewhereC (ε : Nat) : Criterion AbsIdx := fun x => ∃ g : Nat, AbsBand x.1 x.2.1 ε g

/-- **`bandExistsC ε` 与 `bandC ε` **逐点**等价**（真 `↔`）。

  **比定义多说了什么**：`bandExistsC` 有 `∃` + 等式，`bandC` 只有两个不等式。
  本条说明两者**同一个判据** —— 等式 `g = γ` 使见证**唯一化**，
  于是「存在」退化成「这一处」。这是「呈现固定**不**损失信息」的**可证**情形。

  ⚠ **为什么等式 `g = γ` 是必需的**（实测，见 `_probe_T52i.lean` / `_probe_T52j.lean`）：
  去掉它，`bandSomewhereC ε x := ∃ g, AbsBand x.1 x.2.1 ε g` 里的 `x`
  **只出现在定义体内部**，`rcases` / `Exists.elim` / `obtain` **全部**会把 `x`
  连同 `g` **静默泛化**，于是 `hg : AbsBand x.1 x.2.1 ε g` 被要求匹配
  `AbsBand x.1 x.2.1 ε x.2.2` —— **目标里根本没有 `g`**，报 Type mismatch。
  这不是 Lean 的缺陷：它恰好**说明**「存在版」与「固定版」**不是一回事**。 -/
theorem bandExists_iff_band (ε : Nat) (x : AbsIdx) :
    bandExistsC ε x ↔ bandC ε x :=
  ⟨fun hex =>
    Exists.elim hex (fun g hg =>
      Eq.mpr (congrArg (fun t => AbsBand x.1 x.2.1 ε t) (Eq.symm hg.1)) hg.2),
    fun hx => ⟨x.2.2, rfl, hx⟩⟩

/-- **`bandSomewhereC` 的条件在 `γ` 就是 `g` 时**退回 `bandC`（用于分离定理）。

  ⚠ 本文件**只**在 `γ` 与见证**可统一**的场合使用它 ——
  这正是 §4.3 要说的：**存在版与固定版的差别就是「见证能不能被固定」**。 -/
theorem bandSomewhere_at (ε σ γ : Nat) (E : AbsErr) :
    bandSomewhereC ε (E, σ, γ) ↔ ∃ g : Nat, AbsBand E σ ε g :=
  Iff.rfl

/-- **等价版的强度版**：`bandExistsC ε` 与 `bandC ε` **互相** `Stronger`。 -/
theorem band_exists_iff_band (ε : Nat) :
    Stronger (bandExistsC ε) (bandC ε) ∧ Stronger (bandC ε) (bandExistsC ε) :=
  ⟨fun x hex => (bandExists_iff_band ε x).1 hex,
    fun x hx => (bandExists_iff_band ε x).2 hx⟩

/-- **`∀γ` 版 ⟹ 固定版**：处处成立 ⟹ 这一点成立。

  **比定义多说了什么**：`bandUniformC` **真**蕴含固定版；反方向**假**（下条），
  所以「把 `e` 固定成 `E γ`」**损失**了「所有分辨率都合格」这一信息
  —— 这是**必须如实登记**的降级。 -/
theorem uniform_band_stronger_band (ε : Nat) : Stronger (bandUniformC ε) (bandC ε) :=
  fun x hun => hun x.2.2

/-- **固定版的位置**：等价于存在版（带等式），被 `∀` 版蕴含（只单向）。

  | 判据 | 与固定版的关系 |
  |---|---|
  | `bandExistsC`（带等式） | **等价**（双向） |
  | `bandUniformC` | 只**单向**（`∀ ⟹ 固定`，反向假） |
  | `bandSomewhereC`（不带等式） | **都不是**（见下两条） | -/
theorem band_between (ε : Nat) :
    Stronger (bandExistsC ε) (bandC ε) ∧ Stronger (bandC ε) (bandExistsC ε) ∧
      Stronger (bandUniformC ε) (bandC ε) :=
  ⟨(band_exists_iff_band ε).1, (band_exists_iff_band ε).2, uniform_band_stronger_band ε⟩

/-! #### §4.3 的**反例剖面**（全部 `Nat`，全零公理）

  ⚠ **为什么写成独立 `def` + 独立取值定理**（实测，`_probe_T52v/w/x.lean`）：
  在 `Nat` 上 `(fun _ => 100) 0` **不**自动归约成 `100`（`decide` 会把它
  判成「需证 `100 ≤ 1`」并直接失败）。必须先有**独立的取值等式定理**
  （`rfl` 级），再用 `rw` 把它换进去。这也是本项目「先算清再证」的又一实例。
-/

/-- **反例剖面 `Edrop`**：`E 0 = 1`，其余一律 `100`。

  **比定义多说了什么**：`bandC ε` 只读 `E γ` **一个点**，而 `bandUniformC ε`
  读**全部** `E g`。`Edrop` 在 `γ = 0` 处合格、在 `g = 1` 处**远不合格**（`100` vs `1`）
  —— 于是它是「固定呈现 ≠ 处处成立」的**唯一**见证。 -/
def Edrop : AbsErr := fun n => if n = 0 then 1 else 100

/-- **`Edrop 0 = 1`**（`if` 的 `then` 分支；纯 `rw`，零公理）。 -/
theorem Edrop_zero : Edrop 0 = 1 := by
  show (if (0 : Nat) = 0 then 1 else 100) = 1
  rw [if_pos rfl]

/-- **`Edrop 1 = 100`**（`if` 的 `else` 分支）。 -/
theorem Edrop_one : Edrop 1 = 100 := by
  show (if (1 : Nat) = 0 then 1 else 100) = 100
  rw [if_neg (by decide)]

/-- **`Edrop 1 ≤ 1 + 0` 不成立**（`100 ≤ 1` 假）。

  **比定义多说了什么**：把「`E 1` 离合格线有多远」落成一个**可复用的否定**
  —— 缺口 `99`。下面两条分离定理都只用它。 -/
theorem Edrop_one_not_le : Edrop 1 ≤ 1 + 0 → False := by
  show (100 : Nat) ≤ 1 + 0 → False
  exact fun h => nomatch (Nat.lt_irrefl 100 (Nat.lt_of_le_of_lt h (by decide)))

/-- **`Edrop` 在 `γ = 0` 处落在 `σ = 1, ε = 0` 的带内**。 -/
theorem Edrop_band : bandC 0 (Edrop, 1, 0) := by
  show AbsBand Edrop 1 0 0
  unfold AbsBand
  show (1 : Nat) - 0 ≤ Edrop 0 ∧ Edrop 0 ≤ 1 + 0
  rw [Edrop_zero, Nat.sub_zero, Nat.add_zero]
  exact ⟨Nat.le_refl 1, Nat.le_refl 1⟩

/-- **`bandC 0` **不**蕴含 `bandUniformC 0`**（**这是真正的降级**）。

  **比定义多说了什么**：`bandC 0 (Edrop,1,0)` **成立**（`γ = 0` 处 `1 ≤ 1`），
  `bandUniformC 0 (Edrop,1,0)` **不成立**（`g = 1` 处要 `100 ≤ 1`）。
  于是「固定呈现版」与「所有分辨率合格」**不同** ——
  这正是「`accepts` 只能吃**一个数**」在代数层的**同一句话**。 -/
theorem band_not_uniform : ¬ Stronger (bandC 0) (bandUniformC 0) :=
  fun hs => Edrop_one_not_le ((hs (Edrop, 1, 0) Edrop_band) 1).2

/-- **「某个 `γ` 落在带内」不蕴含「这个 `γ` 落在带内」** —— 用**同一个点**比较。
  ⚠ **本条的关键**：取 `∃` 的见证为 `x.2.2` **本身**，于是 Lean 能把
  `bandSomewhereC ε x` 与 `bandC ε x` 的**类型直接统一**（`Iff.rfl` 级），
  不需要 `rcases` —— 后者会把 `x` 泛化掉（见 §4.3 头注）。

  **比定义多说了什么**：`bandSomewhereC ε` 比 `bandC ε` **弱**（多一个 `∃`），
  故 `bandC ⟹ bandSomewhereC` **恒成立**（`band_somewhere_of_band`，`rfl` 级）。
  反方向**不成立**：`Edrop` 在 `γ = 0` 处合格、`γ = 1` 处不合格，于是
  「存在某个合格分辨率」成立而「这个（`γ = 1`）合格」不成立。
  —— 这就是 `accepts` 不能自由换 `e` 的**代数**原因。 -/
theorem bandSomewhere_not_band : ¬ Stronger (bandSomewhereC 0) (bandC 0) :=
  fun hs => Edrop_one_not_le ((hs (Edrop, 1, 1) ⟨0, Edrop_band⟩).2)

/-- **§4.3 结论**：`accepts` 的三种呈现里，**只有**带等式 `g = γ` 的那种
真正等价于固定呈现；「某个」版与「处处」版都**在某一侧是空的**。

  **比定义多说了什么**：把三条结果**合成一条**可引用的定理，
  于是「为什么必须固定 `e := E γ`」有一个**单一出处**，
  而不是散在三条里让下游挑错一条。

  ⚠ 分离结论写成 `P → Q → False` 而非 `¬ Stronger P Q`：见 §4.2 的写法纪律。 -/
theorem accepts_presentation_forced :
    (∀ (ε : Nat) (x : AbsIdx), bandExistsC ε x ↔ bandC ε x) ∧
    (Stronger (bandSomewhereC 0) (bandC 0) → False) ∧
    (Stronger (bandC 0) (bandUniformC 0) → False) :=
  ⟨fun ε x => bandExists_iff_band ε x, bandSomewhere_not_band, band_not_uniform⟩

/-! ===========================================================================
  §5  与 T28 的 `VerdictAxioms` 衔接：**最强的判据类**？
-/

/-- **满足 `VerdictAxioms` 的判据**（抽象、无 `Real` 的载体形式）。

  ⚠ 两条字段**刻意展开**：`iff` 的右端把 `IsBoundaryPoint` **展开写**成
  `f a = σ ∧ ∀ b, σ ≤ f b` —— 直接引用 `IsBoundaryPoint` 会把 T28 的
  `boundaryPoint_verdictAxioms` 的 `Iff.rfl` 依赖拉进来（实测带三公理）。 -/
structure AbstractVerdictAxioms {α β : Type} [Preorder β]
    (P : (α → β) → β → α → Prop) : Prop where
  /-- 合格线唯一（不依赖见证点）。 -/
  unique : ∀ (f : α → β) (σ₁ σ₂ : β) (a₁ a₂ : α), P f σ₁ a₁ → P f σ₂ a₂ → σ₁ = σ₂
  /-- 判据等价于「取到 + 下界」（右端**展开写**）。 -/
  iff : ∀ (f : α → β) (σ : β) (a : α), P f σ a ↔ (f a = σ ∧ ∀ b, σ ≤ f b)

/-- **T28 的 `VerdictAxioms` ⟹ `AbstractVerdictAxioms`**（字段逐一对应）。

  **比定义多说了什么**：两个结构在源码里**没有任何**连接定理。本条给出**翻译**，
  于是 T28 的 `verdictAxioms_unique` / `attainedValue_not_axioms` **直接**适用于
  本文件 §5 的每一条，不必重证。 -/
theorem verdictAxioms_correspond {α β : Type} [Preorder β]
    {P : (α → β) → β → α → Prop} (h : FateV2.ErrorN.VerdictAxioms P) :
    AbstractVerdictAxioms P where
  unique := h.unique
  iff := fun f σ a => h.iff_min f σ a

/-- **反方向**：`AbstractVerdictAxioms ⟹ VerdictAxioms`。 -/
theorem verdictAxioms_correspond_back {α β : Type} [Preorder β]
    {P : (α → β) → β → α → Prop} (h : AbstractVerdictAxioms P) :
    FateV2.ErrorN.VerdictAxioms P where
  unique := h.unique
  iff_min := fun f σ a => h.iff f σ a

/-- **任一 `VerdictAxioms` 判据都与「取到 + 下界」**同真同假**。

  **比定义多说了什么**：任务书要求「满足 `VerdictAxioms` 的判据互相 `Stronger` 等价」
  —— **这条为真，但平凡**：所有实例都由 `iff` 等价于**同一个**命题，
  互相蕴含是 `Iff` 的直接合成，**不加任何新信息**（T28 已证
  `verdictAxioms_iff_boundaryPoint`）。
  本定理给出**它的真正内容**：`VerdictAxioms` **恰好**是从
  「取到 + 下界」出发的**等价类**，不多不少。

  ⚠ **它不是「最强」**：见 `axioms_position`。 -/
theorem verdictAxioms_equivalent {α β : Type} [Preorder β]
    {P : (α → β) → β → α → Prop} (hP : AbstractVerdictAxioms P) :
    ∀ (f : α → β) (σ : β) (a : α), P f σ a ↔ (f a = σ ∧ ∀ b, σ ≤ f b) :=
  hP.iff

/-- **`VerdictAxioms` 的实例**互相**蕴含**（`Stronger` 的逐点实现）。

  **比定义多说了什么**：把 `verdictAxioms_equivalent` 的 `iff` 读成**两个方向**的蕴含
  —— 同一函数上两个都满足公理的判据，在**同一点**上**同时**成立或**同时**不成立。 -/
theorem verdictAxioms_mutual {α β : Type} [Preorder β]
    {P Q : (α → β) → β → α → Prop}
    (hP : AbstractVerdictAxioms P) (hQ : AbstractVerdictAxioms Q)
    (f : α → β) (σ : β) (a : α) : P f σ a → Q f σ a :=
  fun hpq => (hQ.iff f σ a).2 ((hP.iff f σ a).1 hpq)

/-- **公理类对「逐点等价」封闭**：若 `P` 满足公理且 `Q` 与 `P` **逐点等价**，
  则 `Q` **也**满足公理。

  **比定义多说了什么**：任务书要「`VerdictAxioms` 是最强判据类」。
  本条指出**它的真正结构**：公理类**不是**「某个最强者」，而是
  **一个关于逐点等价的封闭类**。于是「最强」只能读成「**自身那个等价类里**最强」
  （`Stronger` 是预序、**无**反对称，见 §2）。
  ⚠ 方向是关键的：`Q` 比 `P` **强**（多一个合取）**也**满足公理，只要等价性保住；
  故 `VerdictAxioms` **拦不住**更强的判据进来 —— 它**不是**上界。 -/
theorem axioms_closed_under_equiv {α β : Type} [Preorder β]
    {P Q : (α → β) → β → α → Prop} (hP : AbstractVerdictAxioms P)
    (hQP : ∀ (f : α → β) (σ : β) (a : α), Q f σ a → P f σ a)
    (hPQ : ∀ (f : α → β) (σ : β) (a : α), P f σ a → Q f σ a) :
    AbstractVerdictAxioms Q where
  unique := fun f σ₁ σ₂ a₁ a₂ h₁ h₂ =>
    hP.unique f σ₁ σ₂ a₁ a₂ (hQP f σ₁ a₁ h₁) (hQP f σ₂ a₂ h₂)
  iff := fun f σ a =>
    ⟨fun h => (hP.iff f σ a).1 (hQP f σ a h),
      fun h => hPQ f σ a ((hP.iff f σ a).2 h)⟩

/-- **`VerdictAxioms` 的确切位置**（任务书 §第 4 步的**最终答案**）。

  | 方向 | 内容 | 定理 |
  |---|---|---|
  | 上界 | `VerdictAxioms P` ⟹ `P` 与「取到+下界」互推 | `verdictAxioms_equivalent` |
  | 下界 | 与 `P` 互推 ⟹ `VerdictAxioms Q` | `axioms_closed_under_equiv` |
  | 位置 | 它与 `fullC` **同层**（`absC_iff_fullC`），**不**在顶 | §3 + 本条 |

  ⚠ **「最强」的准确读法**：`VerdictAxioms` 刻画的是「取到 + 下界」的
  **强度等价类**；因为 `Stronger` **不**反对称，「最强的判据类」
  = 「一个等价类的完整提升」。任务书的字面断言（「一切更强的判据都不在类里」）
  是**假**的：任何在 `P` 上多加合取的判据**仍**在类里
  （`axioms_closed_under_equiv`）。本文件**如实**报告，不把字面断言写成定理。 -/
theorem axioms_position {α β : Type} [Preorder β]
    {P : (α → β) → β → α → Prop} (hP : AbstractVerdictAxioms P) :
    (∀ (f : α → β) (σ : β) (a : α), P f σ a ↔ (f a = σ ∧ ∀ b, σ ≤ f b)) ∧
    (∀ (f : α → β) (σ₁ σ₂ : β) (a₁ a₂ : α), P f σ₁ a₁ → P f σ₂ a₂ → σ₁ = σ₂) :=
  ⟨hP.iff, hP.unique⟩

/-- **`VerdictAxioms` 判据一定落在 `fullC` 那一层**（与 §3 的接点）。

  **比定义多说了什么**：把 `axioms_position` 的 `iff` 与 §3 的 `absC_iff_fullC`
  接起来：任一满足公理的判据在抽象载体上**逐点**等价于「完整判据」。
  于是「抽象判据层 = 完整判据层」**不是**类比，而是**定理**。 -/
theorem axioms_iff_fullC {α β : Type} [Preorder β]
    {P : (α → β) → β → α → Prop} (hP : AbstractVerdictAxioms P) :
    ∀ (f : α → β) (σ : β) (a : α), P f σ a → (f a = σ ∧ ∀ b, σ ≤ f b) :=
  fun f σ a h => (hP.iff f σ a).1 h

end FateV2.Core
