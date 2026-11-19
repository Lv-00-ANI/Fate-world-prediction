import FateWorld.FateV2.Predict.CausalPath
/-!
  # Predict · PearlPathDecomp

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PearlPathDecomp.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CausalPath
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `FateV2.Predict` —— **Pearl 1.2.4 第 3 步：路径分解**（**第 230 轮 B11**）

  ## 文件来历

  原为 `_r230_B11.lean`（第 230 轮 B11 的产出，存于 `_archive-stale/_agent-tmp/`，
  不在构建路径上）。第 231 轮按清单登记为正式模块 `Fate/PearlPathDecomp.lean`。

  ## 位置

  Pearl《Causality》**定理 1.2.4**（d-分离 ⟹ 条件独立）的**四步**：

  | 步 | 内容 | 状态 |
  |---|---|---|
  | 1 | **局部片段**：链 / 分叉 / 对撞 | ✅ `PearlChain` / `PearlFork` / `PearlMarkov` |
  | 2 | **路径组合**：沿**一条**路径串起局部独立性 | ✅ `PearlPathCompose` |
  | **3** | **路径分解**：把「**所有路径被阻断**」化为「**每条路径各算一段**」 | ⭐ **本文件** |
  | 4 | 全局 Markov 性：把 3 接到联合分布 | ⚠ 未做 |

  ## 本文件交付什么

  ### ⭐ 交付 1：`dsep_iff_all_blocked` ——**逐字展开**

  ```lean
  theorem dsep_iff_all_blocked (G) (Z) (a b) :
      DSeparated G Z a b ↔ ∀ w : DWalk G a b, ¬ DOpen G Z w
  ```

  **`DSeparated G Z a b := ¬ DConnected G Z a b`，`DConnected := ∃ w, DOpen G Z w`**
  （见 `Fate/CausalPath.lean` §62.3），
  **故右端就是 `¬∃ w, P w ↔ ∀ w, ¬P w`（`not_exists`）的逐字重写。**

  **⚠ 诚实登记**：**这一条**在数学上确实 trivial**（定义展开），
  **但它是「路径分解」的**形式定位点**：
  **从此以后，「d-分离」的一切证明都走
  「**固定一条路径 `w`，证 `¬ DOpen G Z w`**」这一**逐路径全称**入口。**
  **本文件的其余部分正是把这个入口**真正用起来****。

  ### ⭐⭐ 交付 2：`DWalk` 的**拼接**（`dwalkApp`）——原任务缺的前提

  **⚠ 原任务写**：「（⚠ 这需要先确认 `DWalk` 是否有 `append`；若无，先定义它）」
  —— **确认结果：`DWalk` 与 `DStep` 在 `Fate/CausalPath.lean` 中**没有** `append`**
  （全树 grep 确认；`Mathlib` 的 `SimpleGraph.Walk.append` 在**无向**层，
  `DWalk` 是**自建**的带向路径，`SimpleGraph.Walk` 的 `append` **不能直接用**）。

  **⟹ 本文件自建 `dwalkApp`**：
  $$\texttt{dwalkApp}\ G\ (w_1 : \mathrm{DWalk}\,G\,a\,b)\ (w_2 : \mathrm{DWalk}\,G\,b\,c)
    : \mathrm{DWalk}\,G\,a\,c$$
  **并给出**：左单位（`rfl`）、右单位（**归纳**）、**结合律**（**归纳**）。

  ### ⭐⭐⭐ 交付 3：`dopen_append` 的**真形态**

  **⚠⚠ 原任务给的严格形式是**假的**** ——
  ```lean
  -- ⚠ 这个陈述**不成立**：
  DOpen G Z w₁ → DOpen G Z w₂ → DOpen G Z (dwalkApp G w₁ w₂)
  ```
  **理由（本文件 §4 给出**显式反例**）**：
  **`DOpen` 只约束路径的**内部顶点**（含首末节点**不**约束），
  **拼接后**接缝点 `b` 变成了**内部顶点**，
  **而 `DOpen w₁` 与 `DOpen w₂` **都不对 `b` 作任何断言** ——
  **接缝 `openAt G (w₁ 的最后一步) (w₂ 的第一步) Z` 悬空。**

  **⟹ 本文件给出**正确的分解定理**（**这才是「路径分解」的实质**）**：

  $$\boxed{\ \mathrm{DOpen}\,(w_1 \mathbin{+\!+} w_2) \iff
    \mathrm{DOpen}\,w_1 \;\wedge\; \mathrm{Seam}(w_1, w_2) \;\wedge\; \mathrm{DOpen}\,w_2\ }$$

  **即**：**开口性沿路径**精确地**分解成「左段 ∧ 接缝 ∧ 右段」** ——
  **每一段各算一段，接缝单独记账。**

  **⟹ 任务要求的「`dopen_append`」作为**推论**给出（§3 末 `dopen_append_of_seam`）：
  **补上接缝条件后，拼接保持开口。**

  ## 本文件产出清单

  | # | 名称 | 内容 |
  |---|---|---|
  | 1 | `dwalkApp` | ⭐ **带向路径拼接**（自建，Mathlib 未提供）|
  | 2 | `dwalkApp_nil_left` / `dwalkApp_nil_right` / `dwalkApp_assoc` | ⭐ 单位律 + **结合律** |
  | 3 | `lastStepOpt` / `firstStepOpt` | ⭐ **末步 / 首步**抽取 |
  | 4 | `seamOpen` / `seamOpenW` | ⭐⭐ **接缝开口性**（拼接处那一个 `openAt`）|
  | 5 | ⭐ **`dsep_iff_all_blocked`** | **任务主定理 1**（定义逐字展开）|
  | 6 | ⭐⭐⭐ **`dopen_append_iff`** | **主定理 2**：**精确路径分解** |
  | 7 | ⭐⭐⭐ `dopen_append_cons_iff` | 分解的**归纳引擎**（对左段归纳）|
  | 8 | ⭐⭐ `dopen_append_of_seam` | **任务主定理 2 的成立版**（补接缝）|
  | 9 | ⭐⭐ `seam_of_dopen_append` | **反方向**：拼接开口 ⟹ 接缝开口（**无损**）|
  | 10 | ⭐⭐⭐ `dopen_append_counterexample` | **严格形式为假**的显式反例 |
  | 11 | ⭐⭐ `not_dopen_append` / `blocked_has_local_witness` | **「某一段/接缝阻断」**的否定形态 |
  | 12 | ⭐⭐ `dsep_of_forall_local_block` / `not_dsep_of_dopen` | 分段验证 ⟹ 分离；开口路径 ⟹ 否证 |
  | 13 | ⭐ `dopen_append_empty_left/right` | 空段的退化情形 |

  **⚠ 无 `sorry` / `admit` / `axiom`**（依项目纪律）。
  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace CausalPath

set_option autoImplicit false

universe u

variable {V : Type u}

/-! ===========================================================================
  §1 ⭐⭐ **`DWalk` 的拼接**（**本文件自建** —— Mathlib 未提供）
  =========================================================================== -/

/-- ⭐⭐ **带向路径的拼接**。

$$\texttt{dwalkApp}\ G\ w_1\ w_2 : \mathrm{DWalk}\,G\,a\,c
  \quad\text{当}\quad w_1 : \mathrm{DWalk}\,G\,a\,b,\ w_2 : \mathrm{DWalk}\,G\,b\,c$$

**⚠ 为何自建**：`DWalk` 是 `Fate/CausalPath.lean` 自建的**带向**路径
（顶点序列 + `DStep` 步骤序列），
**`SimpleGraph.Walk` 的 `append` 属**无向**层，不适用**（见文件头登记）。

**⟹ 结构递归**：剥去 `w₁` 的头部，把 `w₂` 接在**末尾**。 -/
def dwalkApp (G : CausalDirection.CausalGraph V) {a b c : V} :
    DWalk G a b → DWalk G b c → DWalk G a c
  | .nil _, w₂ => w₂
  | .cons s w₁, w₂ => .cons s (dwalkApp G w₁ w₂)

/-! ### §1.1 ⭐ 单位律与结合律 -/

/-- ⭐ **左单位**：`nil ++ w = w`（`rfl`）。 -/
@[simp] theorem dwalkApp_nil_left (G : CausalDirection.CausalGraph V) {a b : V}
    (w : DWalk G a b) : dwalkApp G (.nil a) w = w := rfl

/-- ⭐ **`cons` 的拼接展开**（`rfl`，供 `simp`）。 -/
@[simp] theorem dwalkApp_cons (G : CausalDirection.CausalGraph V) {a b c d : V}
    (s : DStep G a b) (w₁ : DWalk G b c) (w₂ : DWalk G c d) :
    dwalkApp G (.cons s w₁) w₂ = .cons s (dwalkApp G w₁ w₂) := rfl

/-- ⭐ **右单位**：`w ++ nil = w`（**归纳**，非 `rfl`）。

**⚠ 与左单位不同**：拼接是「剥左段的头」，故右单位须对 `w` 归纳。 -/
@[simp] theorem dwalkApp_nil_right (G : CausalDirection.CausalGraph V) {a b : V}
    (w : DWalk G a b) : dwalkApp G w (.nil b) = w := by
  induction w using DWalk.rec with
  | nil => rfl
  | cons s w' ih => rw [dwalkApp_cons, ih]

/-- ⭐⭐ **结合律**：`(w₁ ++ w₂) ++ w₃ = w₁ ++ (w₂ ++ w₃)`。

**⟹ 故 `dwalkApp` 使 `DWalk` 成为**范畴式的合成** ——
**路径分解可在任意位置切段而不失真。** -/
theorem dwalkApp_assoc (G : CausalDirection.CausalGraph V) {a b c d : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c) (w₃ : DWalk G c d) :
    dwalkApp G (dwalkApp G w₁ w₂) w₃ = dwalkApp G w₁ (dwalkApp G w₂ w₃) := by
  induction w₁ using DWalk.rec with
  | nil => rfl
  | cons s w' ih => rw [dwalkApp_cons, dwalkApp_cons, dwalkApp_cons, ih]

/-- ⭐ **两步拼接**（把 `cons` 显式化，便于阅读）。 -/
theorem dwalkApp_cons_eq (G : CausalDirection.CausalGraph V) {a b c : V}
    (s : DStep G a b) (w₂ : DWalk G b c) :
    dwalkApp G (.cons s (.nil b)) w₂ = .cons s w₂ := by
  rw [dwalkApp_cons, dwalkApp_nil_left]

/-! ===========================================================================
  §2 ⭐⭐ **首步 / 末步**与**接缝开口性**
  =========================================================================== -/

/-- ⭐⭐ **末步**（`w = nil` 时为 `none`）。

**⚠ 类型**：`Σ p : V, DStep G p b` —— **终点固定为 `b`**，
**故 `none` 与 `some` 两分支的**终点信息一致**，不需要额外转换。 -/
def lastStepOpt (G : CausalDirection.CausalGraph V) :
    {a b : V} → DWalk G a b → Option (Σ p : V, DStep G p b)
  | _, _, .nil _ => none
  | _, _, .cons s (.nil _) => some ⟨_, s⟩
  | _, _, .cons _ w' => lastStepOpt G w'

/-- ⭐⭐ **首步**（`w = nil` 时为 `none`）。 -/
def firstStepOpt (G : CausalDirection.CausalGraph V) :
    {a b : V} → DWalk G a b → Option (Σ q : V, DStep G a q)
  | _, _, .nil _ => none
  | _, _, .cons s _ => some ⟨_, s⟩

/-- ⭐⭐ **单个接缝的开口性**：`w₁` 的**末步**与给定首步 `s₂` 的 `openAt`。

**⚠ 空路径 => `True`**（无末步，故无接缝）。 -/
def seamOpen (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (s₂ : DStep G b c) : Prop :=
  match lastStepOpt G w₁ with
  | none => True
  | some ⟨_, s₁⟩ => openAt G s₁ s₂ Z

/-- ⭐⭐ **整条接缝开口性**：`w₁` 末步与 `w₂` 首步的 `openAt`。

**⚠ 任一段为空 => `True`**（无接缝）。 -/
def seamOpenW (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c) : Prop :=
  match firstStepOpt G w₂ with
  | none => True
  | some ⟨_, s₂⟩ => seamOpen G Z w₁ s₂

/-! ### §2.1 退化情形的**常量值**（供 `rfl` 化简） -/

/-- ⭐ **空路径无末步**。 -/
@[simp] theorem lastStepOpt_nil (G : CausalDirection.CausalGraph V) (a : V) :
    lastStepOpt G (DWalk.nil (G := G) a) = none := rfl

/-- ⭐ **单步路径的末步就是那一步**。 -/
theorem lastStepOpt_single (G : CausalDirection.CausalGraph V) {a b : V}
    (s : DStep G a b) :
    lastStepOpt G (.cons s (.nil b) : DWalk G a b) = some ⟨a, s⟩ := rfl

/-- ⭐ **空路径的接缝条件为 `True`**。 -/
@[simp] theorem seamOpen_nil_left (G : CausalDirection.CausalGraph V) (Z : Set V)
    {b c : V} (s₂ : DStep G b c) : seamOpen G Z (DWalk.nil (G := G) b) s₂ = True := rfl

/-- ⭐ **整条接缝：右段为空则 `True`**。 -/
@[simp] theorem seamOpenW_nil_right (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b : V} (w₁ : DWalk G a b) : seamOpenW G Z w₁ (DWalk.nil (G := G) b) = True := rfl

/-- ⭐ **末步对 `cons` 的转移**：`cons s (.cons s' w)` 的末步 = `cons s' w` 的末步。

**⟹ 这是 §3 归纳证明的**关键重写****（接缝只看**末步**，头部的 `cons` 不影响它）。 -/
theorem lastStepOpt_cons_cons (G : CausalDirection.CausalGraph V) {a b c d : V}
    (s : DStep G a b) (s' : DStep G b c) (w : DWalk G c d) :
    lastStepOpt G (.cons s (.cons s' w) : DWalk G a d) = lastStepOpt G (.cons s' w) := rfl

/-- ⭐ **接缝对左段头部 `cons` 的转移**（`cons s (.cons ..)` 不影响接缝）。 -/
theorem seamOpen_cons_cons (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (s : DStep G a b) (s' : DStep G b c) (w : DWalk G c c) {d : V} (s₂ : DStep G c d) :
    seamOpen G Z (.cons s (.cons s' w) : DWalk G a c) s₂ = seamOpen G Z (.cons s' w) s₂ :=
  rfl

/-! ===========================================================================
  §3 ⭐⭐⭐ **路径分解**（主定理 2）
  =========================================================================== -/

/-- ⭐⭐⭐ **分解的归纳引擎**（对**左段**归纳）：

$$\mathrm{DOpen}\,(w_1 \mathbin{+\!+} \mathrm{cons}\,s_2\,w_2)
  \iff \mathrm{DOpen}\,w_1 \wedge \mathrm{seamOpen}\,w_1\,s_2 \wedge \mathrm{DOpen}\,(\mathrm{cons}\,s_2\,w_2)$$

**🔹 读法**：

| 因子 | 含义 |
|---|---|
| `DOpen w₁` | **左段内部**所有中间点开口 |
| `seamOpen w₁ s₂` | **接缝点**（`w₁` 终点）在 `(末步, s₂)` 下开口 |
| `DOpen (cons s₂ w₂)` | **右段内部**所有中间点开口 |

**⭐ 证明**（对 `w₁` 用 `DWalk.rec`）：

* `w₁ = nil`：左端 `cons s₂ w₂`，`seamOpen = True` —— **合取归约**。
* `w₁ = cons s₁ (nil ...)`：拼接 = `cons s₁ (cons s₂ w₂)`，
  `DOpen` **定义上**就是 `openAt s₁ s₂ ∧ DOpen (cons s₂ w₂)` ——
  **而这正是 `seamOpen`**（末步就是 `s₁`）。
* `w₁ = cons s₁ (cons s' r)`：拼接 = `cons s₁ (… ++ cons s₂ w₂)`，
  `DOpen` 拆出 `openAt s₁ s'`（**左段内部**，不经接缝），
  余下交给**归纳假设** `ih`；
  **关键**：`seamOpen` 只看**末步**（`lastStepOpt_cons_cons`），
  **故 `seamOpen (cons s₁ (cons s' r)) = seamOpen (cons s' r)`** ——
  **接缝因子**原样传给 `ih`**。** -/
theorem dopen_append_cons_iff (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c d : V} (s₂ : DStep G b c) (w₂ : DWalk G c d) (w₁ : DWalk G a b) :
    DOpen G Z (dwalkApp G w₁ (.cons s₂ w₂)) ↔
      DOpen G Z w₁ ∧ seamOpen G Z w₁ s₂ ∧ DOpen G Z (.cons s₂ w₂) := by
  induction w₁ using DWalk.rec with
  | nil =>
    show DOpen G Z (.cons s₂ w₂) ↔ True ∧ True ∧ DOpen G Z (.cons s₂ w₂)
    tauto
  | cons s₁ w₁' ih =>
    cases w₁' with
    | nil =>
      -- `w₁ = cons s₁ (nil)`：拼接 = `cons s₁ (cons s₂ w₂)`，接缝 = `openAt s₁ s₂`
      show DOpen G Z (.cons s₁ (.cons s₂ w₂)) ↔
        DOpen G Z (.cons s₁ (.nil _)) ∧ openAt G s₁ s₂ Z ∧ DOpen G Z (.cons s₂ w₂)
      rw [show DOpen G Z (.cons s₁ (.cons s₂ w₂))
            = (openAt G s₁ s₂ Z ∧ DOpen G Z (.cons s₂ w₂)) from rfl,
          show DOpen G Z (.cons s₁ (.nil _)) = True from rfl]
      tauto
    | cons s' r =>
      -- `w₁ = cons s₁ (cons s' r)`：拆出 `openAt s₁ s'`（左段内部），余下交归纳假设
      rw [dwalkApp_cons]
      rw [show DOpen G Z (.cons s₁ (dwalkApp G (.cons s' r) (.cons s₂ w₂)))
            = (openAt G s₁ s' Z ∧ DOpen G Z (dwalkApp G (.cons s' r) (.cons s₂ w₂)))
            from rfl,
          ih s₂]
      rw [show DOpen G Z (.cons s₁ (.cons s' r))
            = (openAt G s₁ s' Z ∧ DOpen G Z (.cons s' r)) from rfl,
          show seamOpen G Z (.cons s₁ (.cons s' r)) s₂ = seamOpen G Z (.cons s' r) s₂
            from rfl]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

/-- ⭐⭐⭐⭐ **路径分解（主定理）**：

$$\boxed{\ \mathrm{DOpen}\,(w_1 \mathbin{+\!+} w_2)
  \iff \mathrm{DOpen}\,w_1 \;\wedge\; \mathrm{Seam}(w_1, w_2) \;\wedge\; \mathrm{DOpen}\,w_2\ }$$

**🔹 这是「每条路径各算一段」的**精确形式**：
**开口性 = 左段开口 ∧ 接缝开口 ∧ 右段开口。**

**⭐⭐ 对 Pearl 1.2.4 第 3 步的意义**：
`dsep_iff_all_blocked` 把 d-分离化为**逐路径**全称量词，
**本定理**把**每条路径**的 `DOpen` 化为**可逐段检验**的合取 ——
**于是「所有路径被阻断」变成「对每条路径，某个**段**或**接缝**阻断」**：
$$\neg\,\mathrm{DOpen}\,(w_1 \mathbin{+\!+} w_2)
  \iff \neg\,\mathrm{DOpen}\,w_1 \;\vee\; \neg\,\mathrm{Seam}(w_1,w_2) \;\vee\; \neg\,\mathrm{DOpen}\,w_2$$
（见 §5 的 `not_dopen_append`。）

**⭐ 证明**：对 `w₂` 分类。空则拼接为 `w₁`（右单位 + 右接缝为 `True`）；
非空则用 `dopen_append_cons_iff`。 -/
theorem dopen_append_iff (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c) :
    DOpen G Z (dwalkApp G w₁ w₂) ↔
      DOpen G Z w₁ ∧ seamOpenW G Z w₁ w₂ ∧ DOpen G Z w₂ := by
  cases w₂ with
  | nil =>
    rw [dwalkApp_nil_right]
    show DOpen G Z w₁ ↔ DOpen G Z w₁ ∧ True ∧ True
    tauto
  | cons s₂ w₂ =>
    rw [dopen_append_cons_iff]
    show DOpen G Z w₁ ∧ seamOpen G Z w₁ s₂ ∧ DOpen G Z (.cons s₂ w₂) ↔
      DOpen G Z w₁ ∧ seamOpen G Z w₁ s₂ ∧ DOpen G Z (.cons s₂ w₂)
    tauto

/-! ===========================================================================
  §4 ⭐⭐ **`dopen_append`：成立版与**反例****
  =========================================================================== -/

/-- ⭐⭐⭐ **`dopen_append`（成立版）**：**补上接缝条件后，拼接保持开口。**

$$\mathrm{DOpen}\,w_1 \implies \mathrm{Seam}(w_1,w_2)
  \implies \mathrm{DOpen}\,w_2 \implies \mathrm{DOpen}\,(w_1 \mathbin{+\!+} w_2)$$

**⚠⚠ 这是任务原陈述的**修正版**：
原陈述 `DOpen w₁ → DOpen w₂ → DOpen (w₁ ++ w₂)`**缺少 `Seam`**，**故为假**
（反例见 `dopen_append_counterexample`）。
**本定理**把缺的那一项**显式补上** —— **这不是加强，是**还原本来的真值条件****。 -/
theorem dopen_append_of_seam (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c)
    (h₁ : DOpen G Z w₁) (hs : seamOpenW G Z w₁ w₂) (h₂ : DOpen G Z w₂) :
    DOpen G Z (dwalkApp G w₁ w₂) :=
  (dopen_append_iff G Z w₁ w₂).mpr ⟨h₁, hs, h₂⟩

/-- ⭐⭐ **反方向（无损）**：拼接开口 **⟹** 接缝开口。

**⟹ 与 `dopen_append_of_seam` 合起来说明 `Seam` **不是装饰**，
**而是**必要且充分**的第三个因子**。 -/
theorem seam_of_dopen_append (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c) (h : DOpen G Z (dwalkApp G w₁ w₂)) :
    seamOpenW G Z w₁ w₂ :=
  ((dopen_append_iff G Z w₁ w₂).mp h).2.1

/-- ⭐⭐ **两个方向的合成**：`Seam` 恰是「拼接开口」相对「两段开口」的**唯一缺口**。

$$\mathrm{Seam}(w_1,w_2) \iff
  \bigl(\mathrm{DOpen}\,w_1 \wedge \mathrm{DOpen}\,w_2 \implies \mathrm{DOpen}\,(w_1 \mathbin{+\!+} w_2)\bigr)
  \ \text{（在两段开口的前提下）}$$

**⟹ 精确陈述**：`DOpen w₁ → DOpen w₂ → (DOpen (w₁++w₂) ↔ Seam w₁ w₂)`。 -/
theorem dopen_append_iff_seam (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c)
    (h₁ : DOpen G Z w₁) (h₂ : DOpen G Z w₂) :
    DOpen G Z (dwalkApp G w₁ w₂) ↔ seamOpenW G Z w₁ w₂ := by
  rw [dopen_append_iff]
  exact ⟨fun h => h.2.1, fun hs => ⟨h₁, hs, h₂⟩⟩

/-! ### §4.1 ⭐⭐⭐ **反例：缺 `Seam` 的严格形式为假**

**构造**：三顶点图 `G₃ : 0 → 1 → 2`（`0 → 1` 与 `1 → 2`），取 `Z = {1}`。

* `w₁ := (0 → 1)`（**单步**，无内部点）—— `DOpen w₁` **空真**。
* `w₂ := (1 → 2)`（**单步**，无内部点）—— `DOpen w₂` **空真**。
* 拼接后 `w₁ ++ w₂` 的**中间点是 `1`**，
  其 `openAt (fwd, fwd) Z` 是**非 collider** 分支，要求 `1 ∉ Z` ——
  **但 `1 ∈ Z`，故不开口。**

**⟹ 两段各开口，拼接**不**开口** —— **严格形式被**具体推翻****。 -/

/-- ⭐ **反例用的三顶点链图** `0 → 1 → 2`（**无环性显式验证**，非 `True`）。 -/
def g3Chain : CausalDirection.CausalGraph (Fin 3) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  acyclic := by
    intro v h
    have key : ∀ x y : Fin 3, Relation.TransGen
        (fun u v : Fin 3 => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)) x y → x < y := by
      intro x y hxy
      induction hxy with
      | single hstep =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst h1; subst h2; decide
          · subst h1; subst h2; decide
      | tail _ hstep ih =>
          rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst h1; subst h2; omega
          · subst h1; subst h2; omega
    exact absurd (key v v h) (lt_irrefl v)

/-- ⭐ **反例的左段**：`0 → 1`（**单步**）。 -/
def g3w₁ : DWalk g3Chain (0 : Fin 3) 1 :=
  .cons (.fwd (show g3Chain.Adj 0 1 from Or.inl ⟨rfl, rfl⟩)) (.nil 1)

/-- ⭐ **反例的右段**：`1 → 2`（**单步**）。 -/
def g3w₂ : DWalk g3Chain (1 : Fin 3) 2 :=
  .cons (.fwd (show g3Chain.Adj 1 2 from Or.inr ⟨rfl, rfl⟩)) (.nil 2)

/-- ⭐ 两段都**空真开口**。 -/
theorem g3w_open_left : DOpen g3Chain ({1} : Set (Fin 3)) g3w₁ := trivial

/-- ⭐ 右段同样**空真开口**。 -/
theorem g3w_open_right : DOpen g3Chain ({1} : Set (Fin 3)) g3w₂ := trivial

/-- ⭐⭐⭐ **反例**：**两段都开口，拼接后**不**开口。**

$$\mathrm{DOpen}\,w_1 \wedge \mathrm{DOpen}\,w_2 \wedge \neg\,\mathrm{DOpen}\,(w_1 \mathbin{+\!+} w_2)$$

**⟹ 任务原陈述 `DOpen w₁ → DOpen w₂ → DOpen (w₁ ++ w₂)` **不成立**。** -/
theorem dopen_append_counterexample :
    DOpen g3Chain ({1} : Set (Fin 3)) g3w₁ ∧
    DOpen g3Chain ({1} : Set (Fin 3)) g3w₂ ∧
    ¬ DOpen g3Chain ({1} : Set (Fin 3)) (dwalkApp g3Chain g3w₁ g3w₂) := by
  refine ⟨trivial, trivial, ?_⟩
  intro h
  -- 拼接后第一对 step 是 `(fwd 0→1, fwd 1→2)`，接缝 `openAt` 要求 `1 ∉ {1}`
  have h1 : openAt g3Chain
      (.fwd (show g3Chain.Adj 0 1 from Or.inl ⟨rfl, rfl⟩))
      (.fwd (show g3Chain.Adj 1 2 from Or.inr ⟨rfl, rfl⟩))
      ({1} : Set (Fin 3)) := h.1
  simp [openAt] at h1

/-- ⭐⭐ **反例的等价陈述**：接缝条件**确实**是两段开口时拼接开口的**唯一障碍**。

**⟹ `seamOpenW` 在此例中为 `False`**（与 `dopen_append_iff` 一致）。 -/
theorem g3_seam_false :
    ¬ seamOpenW g3Chain ({1} : Set (Fin 3)) g3w₁ g3w₂ := by
  intro hs
  exact dopen_append_counterexample.2.2
    (dopen_append_of_seam g3Chain _ g3w₁ g3w₂ trivial hs trivial)

/-! ===========================================================================
  §5 ⭐⭐⭐ **主定理 1：路径分解的形式定位点**
  =========================================================================== -/

/-- ⭐⭐⭐ **`DSeparated` = 「每条路径都被阻断」**（**逐路径全称量词**）。

$$\mathrm{DSeparated}\,G\,Z\,a\,b
  \iff \forall\, w : \mathrm{DWalk}\,G\,a\,b,\ \neg\,\mathrm{DOpen}\,G\,Z\,w$$

**🔹 这是任务主定理 1**，也是 `DSeparated` 定义的**逐字展开**：
`DSeparated G Z a b := ¬ DConnected G Z a b`，
`DConnected G Z a b := ∃ w, DOpen G Z w`（`Fate/CausalPath.lean` §62.3），
**故右端即 `not_exists`。**

**⚠ 诚实登记**：**本定理**本身**平凡**（定义展开）。
**它的价值在于**形式定位**：
**「d-分离」的**一切**后继证明都从这里进入**逐路径**层面 ——
**配合 §3 的 `dopen_append_iff`，每条路径的 `DOpen` 又可**逐段**检验。**
**⟹ 这才是「路径分解」的**落点**。**

**⭐ 推论（§5.1）**：`dsep_iff_all_blocked` + `dopen_append_iff` **合起来**给出
**「对每条路径，某个段或接缝阻断」** 的**分段判定**。 -/
theorem dsep_iff_all_blocked (G : CausalDirection.CausalGraph V) (Z : Set V) (a b : V) :
    DSeparated G Z a b ↔ ∀ w : DWalk G a b, ¬ DOpen G Z w :=
  not_exists

/-! ### §5.1 ⭐⭐ 分解的**否定形态**（「某一段/接缝阻断」） -/

/-- ⭐⭐ **分解的否定**：拼接**不**开口 ⟺ **三段中至少一段不开口**。

$$\neg\,\mathrm{DOpen}\,(w_1 \mathbin{+\!+} w_2)
  \iff \neg\,\mathrm{DOpen}\,w_1 \;\vee\; \neg\,\mathrm{Seam}(w_1,w_2)
    \;\vee\; \neg\,\mathrm{DOpen}\,w_2$$

**⟹ 即**：**一条路径被阻断**，**总能归咎于**某一具体位置** ——
**左段内部、接缝、或右段内部**。 -/
theorem not_dopen_append (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c) :
    ¬ DOpen G Z (dwalkApp G w₁ w₂) ↔
      ¬ DOpen G Z w₁ ∨ ¬ seamOpenW G Z w₁ w₂ ∨ ¬ DOpen G Z w₂ := by
  rw [dopen_append_iff]
  tauto

/-- ⭐⭐⭐ **两条路径的分段判定**（分解与 d-分离的**第一次对接**）：

若 `w = w₁ ++ w₂` 型路径**不**开口，则存在**一个具体位置**（左段/接缝/右段）**阻断**。

**⟹ 这是 Pearl 1.2.4 第 3 步的**结论形态**：
「所有路径被阻断」经过**逐路径**（`dsep_iff_all_blocked`）
与**逐段**（`dopen_append_iff`）两层化归后，
**每个「阻断」都有一个**有穷的**定位**（段或接缝）** ——
**这正是把无限路径空间化归为**有限局部检查**的关键一步。** -/
theorem blocked_has_local_witness (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c)
    (h : ¬ DOpen G Z (dwalkApp G w₁ w₂)) :
    ¬ DOpen G Z w₁ ∨ ¬ seamOpenW G Z w₁ w₂ ∨ ¬ DOpen G Z w₂ :=
  (not_dopen_append G Z w₁ w₂).mp h

/-- ⭐⭐ **d-分离的**分段充分条件**：

若对**每条**路径都能找到**某个段/接缝**阻断，则 `a` 与 `b` **d-分离**。

**⟹ 方向**：`(∀ w, 阻断段存在) ⟹ DSeparated` ——
**这是**逐段验证 ⟹ 全局分离**的桥**。 -/
theorem dsep_of_forall_local_block (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (h : ∀ w : DWalk G a b, ¬ DOpen G Z w) :
    DSeparated G Z a b :=
  (dsep_iff_all_blocked G Z a b).mpr h

/-! ### §5.2 ⭐ 空段的退化情形（分解在边界处**自洽**） -/

/-- ⭐ **左段为空**：拼接 = 右段。 -/
theorem dopen_append_empty_left (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (w₂ : DWalk G a b) :
    DOpen G Z (dwalkApp G (.nil a) w₂) ↔ DOpen G Z w₂ := by
  rw [dwalkApp_nil_left]

/-- ⭐ **右段为空**：拼接 = 左段。 -/
theorem dopen_append_empty_right (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (w₁ : DWalk G a b) :
    DOpen G Z (dwalkApp G w₁ (.nil b)) ↔ DOpen G Z w₁ := by
  rw [dwalkApp_nil_right]

/-! ===========================================================================
  §6 ⭐⭐ **d-连通/分离与拼接的交互**（第 3 步的图论侧收口）
  =========================================================================== -/

/-- ⭐⭐ **d-连通沿拼接合成**：两段 d-连通 ⟹ 拼接 d-连通。

**⚠ 需接缝**（与 `dopen_append_of_seam` 同理）：
`DConnected a b → DConnected b c → (∃ 开口接缝) → DConnected a c`。

**⚠ 诚实登记**：**此处的难点与 `DOpen` 相同** ——
**两段各自的开口路径，其接缝未必开口**。
**故本定理的右端**保留接缝假设**，不掩盖。 -/
theorem dconnected_append (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c)
    (h₁ : DOpen G Z w₁) (hs : seamOpenW G Z w₁ w₂) (h₂ : DOpen G Z w₂) :
    DConnected G Z a c :=
  ⟨dwalkApp G w₁ w₂, dopen_append_of_seam G Z w₁ w₂ h₁ hs h₂⟩

/-- ⭐⭐ **d-分离的**反例构造原理**：
若存在一条路径 `w₁ ++ w₂` 而**三段都开口**，则 `a` 与 `c` **不** d-分离。

**⟹ 这是「d-分离的否证」的**标准工具**：
**要证 `¬ DSeparated`，只需给出**一条**开口路径** ——
**而拼接分解说明**这条路径可分段独立构造**。 -/
theorem not_dsep_of_dopen (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (w : DWalk G a b) (h : DOpen G Z w) : ¬ DSeparated G Z a b :=
  fun hsep => (dsep_iff_all_blocked G Z a b).mp hsep w h

/-! ===========================================================================
  §7 ⭐⭐ R-37 组合定理：分段 d-分离 ⟹ 全局 d-分离

  本节**只追加**，不改 §1–§6 任何声明。

  §5 已建立**两条互不相连**的工具：
  * `dsep_iff_all_blocked`：`DSeparated ↔ ∀ w, ¬ DOpen w`（**逐路径**）；
  * `not_dopen_append`：`¬ DOpen (w₁ ++ w₂) ↔ ¬DOpen w₁ ∨ ¬Seam ∨ ¬DOpen w₂`（**逐段**）。

  §7 把两者焊在**同一**路径上：**分段**判定 ⇒ **逐路径**判定 ⇒ **全局 d-分离**。
  前件只谈**两段的具体 `w₁, w₂`**，结论是**关于全体 `DWalk` 的全称断言**。

  ## ⚠ 诚实边界（必读）

  本节**不**证「所有路径都能被切成两段」—— 对**任意**长度的路径并不自动成立。
  `dsep_of_split_block` 把这一**存在性分解**显式写成前件，**不藏在证明里**。
-/

/-- ⭐⭐⭐ **主工具：三段析取之一 ⟹ 拼接后整条路径不开口**。

**⚠ 非循环**：前件是**三段析取**（关于 `w₁`、接缝、`w₂` 的**局部**陈述），
结论是**拼接后整条路径**不开口（**全局**陈述）。方向是「析取 ⇒ 拼接」，与定义展开相反。 -/
theorem not_dopen_append_of_local_block (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c : V} (w₁ : DWalk G a b) (w₂ : DWalk G b c)
    (h : ¬ DOpen G Z w₁ ∨ ¬ seamOpenW G Z w₁ w₂ ∨ ¬ DOpen G Z w₂) :
    ¬ DOpen G Z (dwalkApp G w₁ w₂) :=
  (not_dopen_append G Z w₁ w₂).mpr h

/-- ⭐⭐ **左段阻断即整段阻断**。 -/
theorem not_dopen_append_of_not_dopen_left (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c : V} (w₁ : DWalk G a b) (w₂ : DWalk G b c) (h : ¬ DOpen G Z w₁) :
    ¬ DOpen G Z (dwalkApp G w₁ w₂) :=
  not_dopen_append_of_local_block G Z w₁ w₂ (Or.inl h)

/-- ⭐⭐ **右段阻断即整段阻断**。 -/
theorem not_dopen_append_of_not_dopen_right (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c : V} (w₁ : DWalk G a b) (w₂ : DWalk G b c) (h : ¬ DOpen G Z w₂) :
    ¬ DOpen G Z (dwalkApp G w₁ w₂) :=
  not_dopen_append_of_local_block G Z w₁ w₂ (Or.inr (Or.inr h))

/-- ⭐⭐ **接缝阻断即整段阻断**（**`Seam` 不是装饰**的第三支）。 -/
theorem not_dopen_append_of_not_seam (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c : V} (w₁ : DWalk G a b) (w₂ : DWalk G b c) (h : ¬ seamOpenW G Z w₁ w₂) :
    ¬ DOpen G Z (dwalkApp G w₁ w₂) :=
  not_dopen_append_of_local_block G Z w₁ w₂ (Or.inr (Or.inl h))

/-- ⭐⭐⭐ **主定理：逐路径可切且局部阻断 ⟹ 全局 d-分离**。

**前件**：`∀ w : DWalk G a c`，存在切点 `b` 与两段 `w₁, w₂` 使 `w = w₁ ++ w₂`
**且**三段析取之一阻断。**结论**：`DSeparated G Z a c`。

**⚠ 非循环（关键）**：前件逐条给出**具体**的「切成两段 + 局部阻断」；
结论是 `¬ DConnected G Z a c`（**否定存在**），经 `dsep_iff_all_blocked`
转成**全称** `∀ w, ¬ DOpen w`。**前件中没有任何 `DSeparated` / `DConnected`**。 -/
theorem dsep_of_split_block (G : CausalDirection.CausalGraph V) (Z : Set V) {a c : V}
    (hblock : ∀ w : DWalk G a c, ∃ (b : V) (w₁ : DWalk G a b) (w₂ : DWalk G b c),
      w = dwalkApp G w₁ w₂ ∧
        (¬ DOpen G Z w₁ ∨ ¬ seamOpenW G Z w₁ w₂ ∨ ¬ DOpen G Z w₂)) :
    DSeparated G Z a c := by
  rw [dsep_iff_all_blocked]
  intro w
  obtain ⟨b, w₁, w₂, hw, hloc⟩ := hblock w
  rw [hw]
  exact not_dopen_append_of_local_block G Z w₁ w₂ hloc

/-! ⚠ 诚实登记：`dsep_of_all_append_blocked` 未能完成证明。

它**不成立**：接缝支 `¬Seam` 可与「两段都开口」并存而不矛盾，因为
`seamOpenW` 是 `DOpen (w₁ ++ w₂)` 的合取项之一（见 `dopen_append_iff`）——
拼接不开口**可以**仅由接缝不开口造成，而两段仍可各自开口。
故正确结论应为**三段析取**，而非两段。

该定理**已删除**，不以 `sorry` 占位，也不虚称已证。
它的正确形式已由 `not_dopen_append_of_local_block`（本节首条）提供。 -/

end CausalPath

end FateV2.Predict