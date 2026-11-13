import FateWorld.Legacy.CondIndepSemigraphoid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! ===========================================================================
  §Semigraphoid 收缩律（非空洞版本）：`blockRel_contraction`

  ## 0  ⚠⚠⚠ 诚实声明（必读）：任务单要求的那条定理是**空洞的**

  任务单要求「在 `Fate/CondIndepSemigraphoid.lean` 证收缩律
  `A ⟂ B | C ∧ A ⟂ D | B ∪ C ⟹ A ⟂ (B ∪ D) | C`」。
  **在 `CondRel` 的现有定义下，那条定理是同义反复（前件已把结论包进去）。**

  `Fate.Semigraphoid.CondRel p A B C`（`CondIndepSemigraphoid.lean:401`）定义为

      CondRel p A B C  :=  Disjoint A B ∧ Disjoint A C ∧ Disjoint B C
                            ∧ CondIndepN (proj p (A ∪ B ∪ C))

  **`cond` 字段只依赖集合 `A ∪ B ∪ C`，完全忽略 `A` 与 `B` 的分工**：
  它声称「`A ∪ B ∪ C` 上的**所有**坐标**全体互相**条件独立」，
  **不是**教科书意义上的「`A` 这块 ⟂ `B` 这块，给定 `C`」。

  **⟹ 收缩律在这一定义下退化为集合恒等式。**
  前提 2 的 `cond` 是 `CondIndepN (proj p (A ∪ D ∪ (B ∪ C)))`，
  结论的 `cond` 是 `CondIndepN (proj p (A ∪ (B ∪ D) ∪ C))`，而作为 `Finset` 有

      A ∪ D ∪ (B ∪ C)  =  A ∪ (B ∪ D) ∪ C        (union 的交换 / 结合)

  **逐字相等**。于是结论的实质内容**就是**前提 2 的实质内容，
  **前提 1（`A ⟂ B | C`）一个字都没用到**。这正是任务纪律第 7 条点名的
  「前件把结论包进去」错误。
  第 1 节的 `condRel_contraction_is_vacuous` 把这一点形式化证明。

  **⟹ 本文件不交付那条定理**（按纪律：识别出同义反复必须如实报告，
  不得用「证出来了」冒充实质进展）。改为交付**第 3 节的非空洞收缩律**。

  ## 1  非空洞版本：`BlockRel`

  真正的「两块条件独立」必须携带**两块的分工**。本文件采用「块状因子分解」定义
  （与 `Fate.FactorMarkov.CondIndep`、`Fate.C5g.BlockCI_Gap` 同一形式）：

      BlockRel mass A B C  :=  ∀ z, mass (A ∪ B ∪ C) z * mass C z
                                  = mass (A ∪ C) z * mass (B ∪ C) z

  这里分工是**实质的**：把 `B` 换成别的集合，命题会变。

  ⚠ 若 `mass` 满足**归一化**（`mass ∅ = 1`），则 `mass (A∪B∪C) = mass (A∪C)`、
  `mass (B∪C) = mass C`，命题自动成立 —— 故本节**不假设归一化**，
  `mass : Finset ι → γ → ℝ` 任意。此时 `BlockRel` 是实质条件。

  ## 2  交付内容

  | 定理 | 内容 | 状态 |
  |---|---|---|
  | `contraction_proj_index_eq` | 收缩律两个 `proj` 集合逐字相等 | ✅ |
  | `condRel_contraction_is_vacuous` | 只依赖 `proj` 集合的谓词上，结论 ⟺ 前提 2 | ✅（以**警告**形式交付）|
  | `contraction_algebra` | 纯实数收缩代数核（需 `P ≠ 0`）| ✅ |
  | `contraction_algebra_needs_guard` | `P = 0` 时代数核为假（守卫不可去）| ✅ |
  | `blockRel_contraction` | **非空洞收缩律**（需 `∀ z, mass (B∪C) z ≠ 0`）| ✅ |
  | `BlockRel.comm` / `BlockRel.iff_def` | `A`/`B` 对称、定义展开 | ✅ |
  | `projMass` / `projMass_blockRel_iff` | `BlockRel` 在 `proj`/`NMass` 上的真实实例（非空类）| ✅ |

  ## 3  诚实边界

  * **收缩律唯一的额外假设是 `∀ z, mass (B ∪ C) z ≠ 0`**（除法守卫）。
    这**不是**全局正性 `Pos p`，只是「消去元非零」；
    `contraction_algebra_needs_guard` 证明它在纯代数层面**去不掉**。
  * **本文件不声称「半图样公理全部实现」。**
    `Fate/CondIndepSemigraphoid.lean` 的 §9 已给出「无正性时边缘化不保持
    条件独立」的严格反例（`pje`）；本文件只补上**收缩**一条，
    且是在**换了（正确的）定义之后**。分解 / 弱并 在 `BlockRel` 下**仍未做**。
  * 全部定理**无 `sorry` / `admit` / `axiom`**，**无 `→ True` 形式的占位**。

  ## 4  修复记录（第 627 轮主控漏查的 2 个 error，本文件当时 `lake env lean` = EXIT 1）

  本文件**不在** `Fate.lean` 的 import 链上
  （`grep -c "^import Fate.CondIndepContraction$" Fate.lean` = 0），
  所以 `lake build` 不编它；但 `lake env lean Fate/CondIndepContraction.lean` 曾报 2 个 error。
  本轮**只修这 2 个 error，未改任何定理陈述、未删除定理、未用 `sorry`/`trivial`/`→ True`**。

  ### (a) 两个 error 的根因（原文）

  **error 1（`:150`）`contraction_algebra_needs_guard`**
  ```
  Fate/CondIndepContraction.lean:150:73: error: Type mismatch
    h 0 0 1 0 0 1
  has type
    0 * 0 = 1 * 0 → 0 * 0 = 0 * 1 → 0 * 0 = 1 * 1
  but is expected to have type
    0 * 0 = 1 * 0 → 0 * 0 = 0 * 1 → 0 = 1
  ```
  根因：原代码把 `h 0 0 1 0 0 1`（一个**函数**，其结论段是 `0 * 0 = 1 * 1`）
  直接标注成结论段为 `0 = 1` 的类型，未先化简。`0 * 0 = 1 * 1` 与 `0 = 1`
  在定义上并不相同（需 `norm_num` 求值）。

  **error 2（`:189`）`BlockRel.comm`**
  ```
  Fate/CondIndepContraction.lean:189:7: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
    B ∪ A ∪ C
  in the target expression
    mass (A ∪ B ∪ C) z * mass C z = mass (A ∪ C) z * mass (B ∪ C) z
  ```
  根因：原代码用 `rwa [show (B ∪ A ∪ C) = A ∪ B ∪ C from ...] at hz`，
  但 `hz` 中的集合是 `A ∪ B ∪ C`，**根本没有** `B ∪ A ∪ C` 这个子项，
  重写找不到模式；本应重写的是**目标**（含 `B ∪ A ∪ C`），而非 `hz`。

  ### (b) 各怎么修的

  * **error 1**：改为先应用 `h` 并把两个前件用 `norm_num` 消掉，
    得到 `h33 : 0 * 0 = 1 * 1`，再 `norm_num at h33` 把它化为矛盾，
    从而关闭目标 `False`：
    ```lean
    have h33 := h 0 0 1 0 0 1 (by norm_num) (by norm_num)
    norm_num at h33
    ```
    （**未改**定理陈述，仍是 `¬ ∀ (Q P R S U V : ℝ), ...`。）
  * **error 2**：不用 `rwa ... at hz`，改为对 `hz` 做定向 `simpa`，
    显式把 `A∪B∪C` 重排为 `B∪A∪C`、把右侧两因子交换：
    ```lean
    have hz := h z
    simpa only [Finset.union_comm A B, Finset.union_left_comm A B C,
      Finset.union_assoc, mul_comm] using hz
    ```
    （**未改**定理陈述。）

  ### (c) 验证结果

  * `lake env lean Fate/CondIndepContraction.lean`：**EXIT 从 1 → 0**，
    仅余 1 条**非 error 的 linter warning**
    （`unusedSectionVars`，`projMass_blockRel_iff` 未用到 `[Nonempty ι']`/`[Fintype ζ]`，
    这是修复前就已存在的 warning，非本轮引入，不影响编译）。
  * `grep -c "declaration uses"` = 0（无 `sorry`）。

  ### (d) 不在链上的事实（如实声明）

  * **本文件仍不在 `Fate.lean` 的 import 链上**，本任务**未改 `Fate.lean`**。
    `lake build` 不编译本文件，故**不能**用 `lake build` 成功来冒充本文件通过；
    本文件通过的依据是上面 `lake env lean` 的 **EXIT=0**。

  =========================================================================== -/

namespace Fate

namespace Contraction

open Finset

/-! ---------------------------------------------------------------------------
  §1  ⚠ 空洞性诊断：现有 `CondRel` 下收缩律的结论 ≡ 前提 2
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐ **空洞性核心：收缩律的结论与前件 2 的 `proj` 集合逐字相等。**

$A\cup D\cup(B\cup C) = A\cup(B\cup D)\cup C$（`Finset.union` 的交换/结合）。 -/
theorem contraction_proj_index_eq {ι : Type*} [DecidableEq ι]
    (A B C D : Finset ι) :
    A ∪ D ∪ (B ∪ C) = A ∪ (B ∪ D) ∪ C := by
  ext i
  simp only [mem_union]
  tauto

/-- ⭐⭐⭐ **（警告）现有 `CondRel` 定义下，收缩律是空洞的。**

对**任意**谓词 `F : Finset ι → Prop`：

$$F\big(A\cup D\cup(B\cup C)\big) \;\Longleftrightarrow\; F\big(A\cup(B\cup D)\cup C\big).$$

取 `F = fun S => GenC3.CondIndepN (proj p S)`：左式是 `CondRel p A D (B∪C)`
的 `cond` 字段，右式是 `CondRel p A (B∪D) C` 的 `cond` 字段。
**⟹ 结论的实质内容 = 前提 2 的实质内容，与前提 1 无关。**

**这就是「前件把结论包进去」：本文件因此不把该定理当作收缩律交付。** -/
theorem condRel_contraction_is_vacuous {ι : Type*} [DecidableEq ι]
    (A B C D : Finset ι) (F : Finset ι → Prop) :
    F (A ∪ D ∪ (B ∪ C)) ↔ F (A ∪ (B ∪ D) ∪ C) := by
  rw [contraction_proj_index_eq]

/-! ---------------------------------------------------------------------------
  §2  ⭐⭐ 收缩代数核
  --------------------------------------------------------------------------- -/

/-- ⭐⭐⭐ **收缩律的代数核**（纯实数，无任何结构假设）。

$$\begin{cases}
  Q\cdot S = R\cdot P & (\text{前件 1})\\
  U\cdot P = Q\cdot V & (\text{前件 2})
\end{cases}
\quad\xRightarrow{\;P\ne 0\;}\quad
U\cdot S = R\cdot V .$$

**⟹ 推导**：由前件 2 得 `U = Q·V/P`，由前件 1 得 `R = Q·S/P`；
于是 `U·S = (Q·V/P)·S = (Q·S/P)·V = R·V`。
**唯一假设是 `P ≠ 0`** —— 这就是收缩律对正性的**全部**需求。 -/
theorem contraction_algebra {Q P R S U V : ℝ}
    (hP : P ≠ 0) (h1 : Q * S = R * P) (h2 : U * P = Q * V) :
    U * S = R * V := by
  have hU : U = Q * V / P := by
    rw [eq_div_iff hP]; exact h2
  have hR : R = Q * S / P := by
    rw [eq_div_iff hP]
    linarith [h1]
  rw [hU, hR]
  field_simp

/-- ⭐ **守卫不可去**：`P = 0` 时代数核的结论**假**。

取 `Q = 0, P = 0, R = 1, S = 0, U = 0, V = 1`：
前件 `Q·S = R·P` 即 `0 = 0` ✔，`U·P = Q·V` 即 `0 = 0` ✔，
结论 `U·S = R·V` 即 `0 = 1` ✘。

**⟹ 收缩律在纯代数层面就**必须**带「消去元非零」守卫。 -/
theorem contraction_algebra_needs_guard :
    ¬ ∀ (Q P R S U V : ℝ), Q * S = R * P → U * P = Q * V → U * S = R * V := by
  intro h
  have h33 := h 0 0 1 0 0 1 (by norm_num) (by norm_num)
  norm_num at h33

/-! ---------------------------------------------------------------------------
  §3  ⭐⭐⭐ 非空洞收缩律 `BlockRel`
  --------------------------------------------------------------------------- -/

variable {ι : Type*} [DecidableEq ι] {γ : Type*}

/-- ⭐⭐⭐ **块状条件独立**（真正的两块分裂）：$A \perp B \mid C$。

$$\mathrm{BlockRel}\,\mathrm{mass}\,A\,B\,C
  \;\Longleftrightarrow\;
  \forall z,\ \mathrm{mass}(A\cup B\cup C)\,z\cdot \mathrm{mass}\,C\,z
    = \mathrm{mass}(A\cup C)\,z\cdot \mathrm{mass}(B\cup C)\,z .$$

**与 `CondRel` 的差别**（本文件存在的理由）：这里 `A` 与 `B` 的分工是**实质**的
—— 交换 `A`、`B` 恒等（`BlockRel.comm`），但**换掉 `B` 会改变命题内容**；
`CondRel` 的 `cond` 只说「并集上全体互相独立」，**丢掉**了这块分工。

**⟹ 与既有定义的关系**：形式与 `Fate.FactorMarkov.CondIndep`
（`mass (A ∪ B ∪ Z) * mass Z = mass (A ∪ Z) * mass (B ∪ Z)`）一致，
也与 `Fate.C5g.BlockCI_Gap`（`p x * mass C = mass A * mass (B ∪ C)`）同族；
但那两者绑定在 `(V → α) → ℝ` 的 `mass` 上，本定义对 `mass` **完全抽象**。 -/
def BlockRel (mass : Finset ι → γ → ℝ) (A B C : Finset ι) : Prop :=
  ∀ z, mass (A ∪ B ∪ C) z * mass C z = mass (A ∪ C) z * mass (B ∪ C) z

/-- ⭐ **定义展开**（审计用：确认 `BlockRel` 无隐藏内容）。 -/
theorem BlockRel.iff_def {mass : Finset ι → γ → ℝ} (A B C : Finset ι) :
    BlockRel mass A B C ↔
      ∀ z, mass (A ∪ B ∪ C) z * mass C z = mass (A ∪ C) z * mass (B ∪ C) z :=
  Iff.rfl

/-- ⭐ **`BlockRel` 对 `A`、`B` 交换对称**（两块分工是对称的）。 -/
theorem BlockRel.comm {mass : Finset ι → γ → ℝ} {A B C : Finset ι}
    (h : BlockRel mass A B C) : BlockRel mass B A C := by
  rw [BlockRel.iff_def] at h ⊢
  intro z
  have hz := h z
  simpa only [Finset.union_comm A B, Finset.union_left_comm A B C,
    Finset.union_assoc, mul_comm] using hz

/-- ⭐⭐⭐ **非空洞收缩律**：

$$A\perp B\mid C \;\wedge\; A\perp D\mid B\cup C
  \;\Longrightarrow\; A\perp (B\cup D)\mid C
\qquad(\text{需 } \forall z,\ \mathrm{mass}(B\cup C)\,z\ne 0).$$

**⟹ 把 §2 的代数核套到 `BlockRel` 上**：令
`P := mass (B∪C) z`、`Q := mass (A∪B∪C) z`、`R := mass (A∪C) z`、
`S := mass C z`、`U := mass (A∪D∪(B∪C)) z`、`V := mass (D∪(B∪C)) z`。
两个前件正是 `Q·S = R·P` 与 `U·P = Q·V`，结论正是 `U·S = R·V`；
中间的集合等式（`A∪(B∪D)∪C = A∪D∪(B∪C)` 等）由 `union` 的 AC 提供。

**⚠ 唯一假设**：`hpos : ∀ z, mass (B ∪ C) z ≠ 0`（除法守卫）。
**⚠ 不做**全局正性假设 `Pos p`（见 `contraction_algebra_needs_guard`）。
**⚠ 不预设归一化**（若归一化，命题自动成立，就没有内容了）。 -/
theorem blockRel_contraction {mass : Finset ι → γ → ℝ} {A B C D : Finset ι}
    (hpos : ∀ z, mass (B ∪ C) z ≠ 0)
    (h1 : BlockRel mass A B C)
    (h2 : BlockRel mass A D (B ∪ C)) :
    BlockRel mass A (B ∪ D) C := by
  rw [BlockRel.iff_def] at h1 h2 ⊢
  intro z
  have h1z : mass (A ∪ B ∪ C) z * mass C z = mass (A ∪ C) z * mass (B ∪ C) z := h1 z
  have h2z : mass (A ∪ D ∪ (B ∪ C)) z * mass (B ∪ C) z
      = mass (A ∪ (B ∪ C)) z * mass (D ∪ (B ∪ C)) z := h2 z
  have e1 : (A ∪ (B ∪ D) ∪ C : Finset ι) = A ∪ D ∪ (B ∪ C) :=
    (contraction_proj_index_eq A B C D).symm
  have e2 : ((B ∪ D) ∪ C : Finset ι) = D ∪ (B ∪ C) := by
    ext i; simp only [mem_union]; tauto
  have e3 : (A ∪ (B ∪ C) : Finset ι) = A ∪ B ∪ C := by
    ext i; simp only [mem_union]; tauto
  rw [e3] at h2z
  rw [e1, e2]
  exact contraction_algebra (hpos z) h1z h2z

/-! ---------------------------------------------------------------------------
  §4  ⭐ `BlockRel` 非空类：接到本项目的 `proj` / `NMass` 上
  --------------------------------------------------------------------------- -/

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι'] [Nonempty ι']
variable {α : ι' → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
variable {ζ : Type*} [Fintype ζ]

/-- ⭐⭐ **集合质量**：`proj` 到 `S`、再对 `S` 上全取值求和。

$$\mathrm{projMass}\,p\,S\,z := \mathrm{NMass}\,(\mathrm{proj}\,p\,S)\,z .$$

**⟹ 这把 §3 的抽象 `BlockRel` 接到本项目的 `proj`/`NMass` 上**，
证明 `BlockRel` **不是空类**（`projMass_blockRel_iff` 给出逐字对应）。
特别地 `projMass p ∅ z = NMass p z`（`projMass_empty`）。 -/
noncomputable def projMass (p : GenC3.NJoint (ι := ι') α ζ) (S : Finset ι') (z : ζ) : ℝ :=
  GenC3.NMass (Fate.Semigraphoid.proj p S) z

/-- ⭐ **`projMass` 与 `NMass` 相容**：$S=\emptyset$ 时退化为总质量
（用 `proj_empty` / `nmass_proj_empty`：`proj p ∅` 是常数 `NMass p z`，
故其 `NMass` 仍是 `NMass p z`）。这里直接展开为等式的复合。 -/
theorem projMass_empty (p : GenC3.NJoint (ι := ι') α ζ) (z : ζ) :
    projMass (α := α) p ∅ z = GenC3.NMass p z :=
  Fate.Semigraphoid.nmass_proj_empty p z

/-- ⭐⭐ **`BlockRel` 在 `projMass` 上的展开**（逐字对应，说明实例化是平凡的、
但**不是空的**）：`BlockRel (projMass p) A B C` 就是
三条边缘质量的乘积等式。 -/
theorem projMass_blockRel_iff (p : GenC3.NJoint (ι := ι') α ζ) (A B C : Finset ι') :
    BlockRel (projMass (α := α) p) A B C ↔
      ∀ z, GenC3.NMass (Fate.Semigraphoid.proj p (A ∪ B ∪ C)) z
              * GenC3.NMass (Fate.Semigraphoid.proj p C) z
        = GenC3.NMass (Fate.Semigraphoid.proj p (A ∪ C)) z
              * GenC3.NMass (Fate.Semigraphoid.proj p (B ∪ C)) z :=
  Iff.rfl

end Contraction

end Fate
