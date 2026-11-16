import FateWorld.FateV2.Predict.PearlPathDecomp
import FateWorld.FateV2.Predict.CausalDescendant
/-!
  # Predict · PearlGlobalMarkov

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PearlGlobalMarkov.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：PearlPathDecomp, CausalDescendant
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ⚠⚠⚠ **第 238 轮降级声明（对抗性审核 E5 发现，已用 Lean 探针实测）**

**本模块**不是 Pearl 定理 1.2.4 的第 4 步**。**它是**图论恒等式的标准版重抄**。**

## E5 的逐条实测结论

| 定理 | 判定 | 证据 |
|---|---|---|
| `dsep_set_iff_pairwise` | **纯同义反复（`Iff.rfl`）** | 探针 `p1_reprove` 用 `Iff.rfl` 直接复现 |
| `dsepStd_iff_all_blocked'` | **纯同义反复（`not_exists`）** | 探针 `p2_reprove` 用 `not_exists` 一词复现 |
| `dopen'_append_*`（拼接）| **半内容** | 真 `DWalk.rec` 结构归纳，**但** `openAt'` 全程作为**不透明 Prop**，从未触及 collider/`Reach` 语义 |
| §4 的收口定理 | **零增量** | 探针实测：全部可由 §3 的 `dopen'_append_iff` + `not_exists` + `tauto` **三行**重新导出 |

## ⚠⚠ 关键裁定（E5 原文）

> **「这不是「全局 Markov 性」，而是「全局 Markov 性的**图论恒等式**的**标准版重抄**。
> Pearl 1.2.4 的**内容**是 `d ⊥ Y | Z ⟹ P(X,Y|Z)`；
> 本文件把 `d-分离` 展开成它自己的定义，再证「展开等于展开」。」**

> **「诚实登记一个空洞，不等于交付了那一步。**第 4 步仍是第 4 步缺口，未被本文件推进。**」**

## ⭐⭐ 一个**可自动检查**的判据（D4）

**`grep` 全文件：无 `Measure` / `CondIndep` / `Indep` / `jointLaw` / `SCM`。**
**⟹ 任何**只涉及** `DConnected` / `DSeparated` / `DOpen` 这些**图论谓词**的定理，
**都在图论内部，**永远不可能是 Pearl 1.2.4**（那是**概率**陈述）。**

## ✅ 本文件**仅有的**真实内容

- **`dopen_imp_dopen'`**：`DOpen ⟹ DOpen'` 的**半步桥**
  （探针证实 `DOpen` 与 `DOpen'` **非 defeq**，故这是真归纳）
  ⚠ **但反向假**（`openAt` 漏了后代），且对称性/`DWalk.reverse` 全缺
- **`dopen'_append_cons_iff`**：真 `DWalk.rec` 结构归纳
  ⚠ **但**它证明的是「合取沿 append 分配」，**与 d-分离语义无关**；
  其**简化版早已存在于 `PearlPathDecomp`**

## ⚠ 处置

**⚠ 本模块**不计入**「缺口 1 第 4 步」的进度。**
**⚠ 真正的 1.2.4（d-分离 ⟹ 条件独立）**仍未开始**。**

**⭐⭐ 详见 `_pending/第238轮-第三次同义反复失误.md`。**
-/


/-! ===========================================================================
  `Fate.PearlGlobalMarkov` —— **Pearl 1.2.4 第 4 步：全局 Markov 性**
  （**第 232 轮**）

  ## 位置与承接

  Pearl《Causality》定理 1.2.4（d-分离 ⟹ 条件独立）的**四步**：

  | 步 | 内容 | 状态 |
  |---|---|---|
  | 1 | 局部片段：链 / 分叉 / 对撞 | ✅ `PearlChain` / `PearlFork` / `PearlMarkov` |
  | 2 | 路径组合：沿一条路径串起局部独立性 | ✅ `PearlPathCompose` |
  | 3 | 路径分解：阻断 ⟹ 逐段可检验 | ✅ `PearlPathDecomp`（**仅 `DOpen`/简化版**）|
  | **4** | **全局 Markov 性** | ⭐ **本文件** |

  ## ⚠⚠ 先说审计结论（**铁律要求：如实报告**）

  ### `PearlPathDecomp` 审计

  | 项 | 数字 |
  |---|---|
  | 定理 / 定义总数 | **36**（`grep` 计数，见文末附录）|
  | 真内容（需要归纳 / 需要构造 / 有反例） | **5 条**：`dwalkApp_nil_right`（归纳）、`dwalkApp_assoc`（归纳）、`dopen_append_cons_iff`（**归纳**）、`dopen_append_iff`、`dopen_append_counterexample`（**显式反例**）|
  | 纯 `rfl`（定义展开 / 常量值）| **11 条**（`dwalkApp_nil_left`、`dwalkApp_cons`、`lastStepOpt_nil`、`lastStepOpt_single`、`seamOpen_nil_left`、`seamOpenW_nil_right`、`lastStepOpt_cons_cons`、`seamOpen_cons_cons`、`g3w_open_left`、`g3w_open_right`，加 `g3Chain` 的辅助）|
  | **同义反复（按 D2/D3 判据）** | ⚠ **`dsep_iff_all_blocked`（§5）**：证体是 `not_exists` 一词 |
  | 纯推论（一步 `Iff.mpr`/`Iff.mp`）| `dopen_append_of_seam`、`seam_of_dopen_append`、`not_dopen_append`（`tauto`）、`blocked_has_local_witness`、`dsep_of_forall_local_block`、`dconnected_append`、`not_dsep_of_dopen`、`dopen_append_empty_left/right`、`g3_seam_false` |

  **⟹ 如实判定**：`PearlPathDecomp` **部分完整**。
  **它的实质**（`dopen_append_iff` + 反例）**是真的、不平凡的** ——
  **它证明了**任务的原始形式 `DOpen w₁ → DOpen w₂ → DOpen (w₁++w₂)` **是假的**，
  **并给出了正确的三段分解**。**这是真内容。**
  **但**：`dsep_iff_all_blocked` 是 `not_exists`（**同义反复**），
  **它的**全部**后继（`dsep_of_forall_local_block` 等）**也因之平凡**。

  ### ⚠⚠ 任务提议的「集合版归约」审计：**它是 `Iff.rfl`**

  任务原文：
  ```lean
  theorem dsep_set_iff_pairwise (G) (Z X Y : Set V) :
      (∀ x ∈ X, ∀ y ∈ Y, DSeparatedStd G Z x y) ↔
      (∀ x ∈ X, ∀ y ∈ Y, ¬ DConnectedStd G Z x y)
  ```

  **实测**（`Iff.rfl` 直接成立，见本文件 §1）：
  `DSeparatedStd G Z x y` **定义为** `¬ DConnectedStd G Z x y`。
  **⟹ 该定理**逐字是定义**，**`Iff.rfl` 即可**。
  **它不是「Pearl 的集合版分离判据」** ——
  **Pearl 原文那句「sets are separated iff each element…」
  是**集合版 d-分离的定义**，不是定理。**

  **⟹ 真正的难点不在这一行**，在下面（本文件 §2–§4 做）：

  ## ⭐⭐ 本文件实际交付的**真内容**

  ### ⭐ 交付 1（§2）：`DOpen → DOpen'` —— **把第 3 步接到标准 d-分离**

  **⚠ 第 3 步的 `PearlPathDecomp` 全部工作在**简化版** `DOpen`（`openAt`：collider 只判 `b ∈ Z`）上，
  而 Pearl 的标准 d-分离是 `DOpen'`（`openAt'`：collider 判 `∃z ∈ Z, Reach b z`）。
  **⟹ 两者之间**没有现成的桥**** —— 本文件补上：
  ```lean
  theorem dopen_imp_dopen' (w : DWalk G a b) : DOpen G Z w → DOpen' G Z w
  ```
  **证明**：对 `w` 归纳，把每个 `openAt` 换成 `openAt_imp_openAt'`
  （`CausalDescendant.openAt_imp_openAt'`：`b ∈ Z ⟹ ∃ z ∈ Z, Reach b z`，取 `z := b`）。

  ### ⭐⭐⭐ 交付 2（§3）：**`openAt'` 版的路径分解** —— 第 3 步的**标准版**

  **⚠⚠ 第 3 步的 `dopen_append_iff` 是以 `DOpen` 陈述的**；
  它在 `DOpen'` 上**不自动成立**：`openAt'` 的 collider 分支
  带有 `Reach` 后代存在性，**接缝条件必须整体换成 `openAt'` 形态**。

  **⟹ 本文件给出**真正的标准版分解**：
  $$\mathrm{DOpen}'\,(w_1 \mathbin{+\!+} w_2)
    \iff \mathrm{DOpen}'\,w_1 \wedge \mathrm{Seam}' \wedge \mathrm{DOpen}'\,w_2$$
  其中 `Seam'` 用新的 `seamOpenP` / `seamOpenWP`（**`openAt'` 版接缝**）。

  **⭐ 这一步是**真归纳**（与第 3 步的 `dopen_append_cons_iff` 同构，
  但接缝类型不同，故**不能靠 `simp` 复用**）。

  ### ⭐⭐ 交付 3（§4）：**全局 Markov 性的形式陈述**

  **Pearl 1.2.4 的「全局」部分**在**图论侧**的精确内容是：

  $$\underbrace{\mathrm{DSeparatedStd}\,G\,Z\,x\,y}_{\text{点分离}}
    \iff \forall\, w : \mathrm{DWalk}\,G\,x\,y,\ \neg\,\mathrm{DOpen}'\,G\,Z\,w$$

  **⟹ 配合 §3 的分段分解**，得到：
  **「一条路径被阻断 ⟺ 左段 / 接缝 / 右段至少一处阻断」**（标准版）。

  **⚠ 诚实登记**：**「点分离 ⟺ 逐路径全称」本身是 `not_exists`**（平凡），
  **它的价值在于**它把 §3 的分解**接到**标准 d-分离上** ——
  **这才是第 4 步的**接口**：**
  **第 3 步证明了「分解」，本文件证明了「分解在**标准**定义下也成立」。**

  ## ⚠⚠ 边界登记（**不掩盖的缺口**）

  1. **本文件不含**「d-分离 ⟹ 联合分布条件独立」的**概率侧**连接
     （那需要「Markov 分布」的形式化 —— 项目现有 `FinMarkov.Factorizes`，
     但**与 `CausalGraph` 的**父集**对接尚未做**）。
     **⟹ 这是真正的第 4 步**剩余部分**，本文件不越界声称完成。**
  2. **`DSeparatedStd`（标准版）的**对称性**（`a ⊥d b ⟺ b ⊥d a`）**未做** ——
     需要 `DWalk` 的**反向**构造（`DWalk` 是自建归纳，无 `reverse`）。
     **⟹ 具名登记，不在本文件伪造。**

  **⚠ 无 `sorry` / `admit` / `axiom`**（依项目纪律）。
  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace PearlGlobalMarkov

open FateV2.Predict.CausalDescendant FateV2.Predict.CausalPath

set_option autoImplicit false

universe u

variable {V : Type u}

/-! ===========================================================================
  §1 ⚠⚠ **任务提议的「集合版归约」** —— **如实登记：它是 `Iff.rfl`**
  =========================================================================== -/

/-- ⚠⚠ **任务提议的定理**（**逐字复述**，用标准 d-分离 `DSeparatedStd`）。

$$\Bigl(\forall x \in X,\ \forall y \in Y,\ x \perp_d y \mid Z\Bigr)
  \iff \Bigl(\forall x \in X,\ \forall y \in Y,\ \neg\,\mathrm{DConnected}\,x\,y \mid Z\Bigr)$$

**🔴 审计判定**：**本定理**是 `Iff.rfl`** ——
因为 `DSeparatedStd G Z a b` **就是** `¬ DConnectedStd G Z a b` 的 `def` 展开
（`Fate/CausalDescendant.lean` §63.5）。

**⟹ 这不是「集合版 d-分离的定理」，而是**定义的重述**。**
**Pearl 那句「两集合分离 ⟺ 每个元素与另一集合的每个元素分离」
在形式化里是**集合版分离的定义**，**不是可证的命题**。**

**⚠ 保留此条的唯一理由**：作为**登记**，防止后人把它当「已完成的内容」计数。** -/
theorem dsep_set_iff_pairwise (G : CausalDirection.CausalGraph V) (Z X Y : Set V) :
    (∀ x ∈ X, ∀ y ∈ Y, DSeparatedStd G Z x y) ↔
    (∀ x ∈ X, ∀ y ∈ Y, ¬ DConnectedStd G Z x y) :=
  Iff.rfl

/-- ⭐ **同上（简化版 `DSeparated`）** —— 也是 `Iff.rfl`。

**⟹ 与 §1 的主条一起，说明「集合 ↔ 逐元素」这一层**完全没有内容**。** -/
theorem dsep_set_iff_pairwise_simple (G : CausalDirection.CausalGraph V) (Z X Y : Set V) :
    (∀ x ∈ X, ∀ y ∈ Y, CausalPath.DSeparated G Z x y) ↔
    (∀ x ∈ X, ∀ y ∈ Y, ¬ CausalPath.DConnected G Z x y) :=
  Iff.rfl

/-- ⭐⭐ **集合版分离的**真实**展开**（**这仍然只是 `¬∃`**，但它是**唯一有接口价值的形式**）：

$$X \perp_d Y \mid Z \iff
  \forall x \in X,\ \forall y \in Y,\ \forall w : \mathrm{DWalk}\,G\,x\,y,\ \neg\,\mathrm{DOpen}'\,G\,Z\,w$$

**⟹ 这是**集合版 × 逐路径**的双重量化** ——
**它是本文件 §3–§4 的真正入口**（因为 §3 的分段分解是**逐路径**的）。

**⚠ 诚实登记**：**证明仍是 `not_exists` 的两次改写**（`¬∃w ↔ ∀w, ¬`），
**本身平凡**。**但它是唯一能把 §3 的分解**用起来**的形态** ——
**分解是关于**单条路径**的，故必须先到**逐路径**层。** -/
theorem dsep_set_iff_all_walks_blocked (G : CausalDirection.CausalGraph V) (Z X Y : Set V) :
    (∀ x ∈ X, ∀ y ∈ Y, DSeparatedStd G Z x y) ↔
    (∀ x ∈ X, ∀ y ∈ Y, ∀ w : DWalk G x y, ¬ DOpen' G Z w) := by
  constructor
  · intro h x hx y hy w hw
    exact h x hx y hy ⟨w, hw⟩
  · intro h x hx y hy ⟨w, hw⟩
    exact h x hx y hy w hw

/-! ===========================================================================
  §2 ⭐ **`DOpen → DOpen'`**：把第 3 步接到**标准** d-分离
  =========================================================================== -/

/-- ⭐ **单步桥接**：`openAt`（简化版）⟹ `openAt'`（标准版）。

**🔹 内容**：`openAt` 的 collider 分支要求 `b ∈ Z`；
`openAt'` 要求 `∃ z ∈ Z, Reach b z`；**取 `z := b`（`Reach.refl b`）即可**。
**非 collider 分支**两者完全相同（都是 `b ∉ Z`）。

**⚠ 来源**：这是 `CausalDescendant.openAt_imp_openAt'` 的**本地重述**
（同一定理，为阅读连贯性在此引用一次）。 -/
theorem openAt_imp (G : CausalDirection.CausalGraph V) {a b c : V}
    {s₁ : DStep G a b} {s₂ : DStep G b c} {Z : Set V}
    (h : openAt G s₁ s₂ Z) : openAt' G s₁ s₂ Z :=
  CausalDescendant.openAt_imp_openAt' G h

/-- ⭐⭐ **整条路径桥接**：`DOpen`（简化版）⟹ `DOpen'`（标准版）。

$$\mathrm{DOpen}\,G\,Z\,w \implies \mathrm{DOpen}'\,G\,Z\,w$$

**🔹 意义**：**第 3 步（`PearlPathDecomp`）的一切结论**都建立在 `DOpen` 上**；
本定理说明**它们在标准 d-分离下**也成立**（在「开口」这一侧）。
**⟹ 这是把第 3 步接入 Pearl 1.2.4 正式表述的**必要桥**。**

**⭐ 证明**：对 `w` 归纳；每步把 `openAt` 换成 `openAt'`（§2 的 `openAt_imp`）。 -/
theorem dopen_imp_dopen' (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (w : DWalk G a b) (h : DOpen G Z w) : DOpen' G Z w := by
  induction w using DWalk.rec with
  | nil => trivial
  | cons s₁ w ih =>
    cases w with
    | nil => trivial
    | cons s₂ w' => exact ⟨openAt_imp G h.1, ih h.2⟩

/-- ⭐⭐ **推论：简化版 d-连通 ⟹ 标准版 d-连通**。

$$\mathrm{DConnected}\,G\,Z\,a\,b \implies \mathrm{DConnected}'\,G\,Z\,a\,b$$

**⟹ 逆否**：**标准分离 ⟹ 简化分离** ——
即**标准 d-分离**强于**简化 d-分离**（与 `CausalPath.lean` §62.3 的登记一致：
简化版会**误报分离**，故**分离更强是预期方向**）。 -/
theorem dconnected_imp_dconnected' (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (h : DConnected G Z a b) : DConnected' G Z a b := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, dopen_imp_dopen' G Z w hw⟩

/-- ⭐⭐ **推论：标准分离 ⟹ 简化分离**（`dconnected_imp_dconnected'` 的逆否形式）。 -/
theorem dseparated_imp_dseparated' (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (h : DSeparatedStd G Z a b) : CausalPath.DSeparated G Z a b :=
  fun hconn => h (dconnected_imp_dconnected' G Z hconn)

/-! ===========================================================================
  §3 ⭐⭐⭐ **`openAt'` 版的接缝与路径分解**（第 3 步的**标准版**）
  =========================================================================== -/

/-- ⭐⭐ **标准接缝开口性**（`openAt'` 版）：`w₁` 的**末步**与给定首步 `s₂` 的 `openAt'`。

**⚠ 为何必须**另立一个**（不能复用第 3 步的 `seamOpen`）**：
`seamOpen` 用 `openAt`（collider 判 `b ∈ Z`）；
**`openAt'` 的 collider 分支带 `Reach` 后代存在性**，
**两者**在 collider 处不等价****（例如 `Z = {后裔}`、`b ∉ Z`：`openAt'` 真、`openAt` 假）。** -/
def seamOpenP (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (s₂ : DStep G b c) : Prop :=
  match lastStepOpt G w₁ with
  | none => True
  | some ⟨_, s₁⟩ => openAt' G s₁ s₂ Z

/-- ⭐⭐ **标准整条接缝**：`w₁` 末步与 `w₂` 首步的 `openAt'`。

**⚠ 任一段为空 => `True`**（无接缝），与 `seamOpenW` 同约定。 -/
def seamOpenWP (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c) : Prop :=
  match firstStepOpt G w₂ with
  | none => True
  | some ⟨_, s₂⟩ => seamOpenP G Z w₁ s₂

/-! ### §3.1 ⭐ 退化情形的**常量值**（供 `rfl` 化简，与第 3 步同构） -/

/-- ⭐ **空路径的 `openAt'` 接缝为 `True`**。 -/
@[simp] theorem seamOpenP_nil_left (G : CausalDirection.CausalGraph V) (Z : Set V)
    {b c : V} (s₂ : DStep G b c) : seamOpenP G Z (DWalk.nil (G := G) b) s₂ = True := rfl

/-- ⭐ **标准整条接缝：右段为空则 `True`**。 -/
@[simp] theorem seamOpenWP_nil_right (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b : V} (w₁ : DWalk G a b) : seamOpenWP G Z w₁ (DWalk.nil (G := G) b) = True := rfl

/-- ⭐ **`openAt'` 接缝对左段头部两次 `cons` 的转移**（接缝只看**末步**）。 -/
theorem seamOpenP_cons_cons (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (s : DStep G a b) (s' : DStep G b c) (w : DWalk G c c) {d : V} (s₂ : DStep G c d) :
    seamOpenP G Z (.cons s (.cons s' w) : DWalk G a c) s₂ = seamOpenP G Z (.cons s' w) s₂ :=
  rfl

/-! ### §3.2 ⭐⭐⭐ **标准版分解**（主定理，**真归纳**） -/

/-- ⭐⭐⭐ **标准版分解的归纳引擎**（对**左段**归纳）：

$$\mathrm{DOpen}'\,(w_1 \mathbin{+\!+} \mathrm{cons}\,s_2\,w_2)
  \iff \mathrm{DOpen}'\,w_1 \wedge \mathrm{seamOpenP}\,w_1\,s_2 \wedge \mathrm{DOpen}'\,(\mathrm{cons}\,s_2\,w_2)$$

**🔹 与第 3 步 `dopen_append_cons_iff` 的**唯一差别**：接缝类型** `openAt` ⟹ `openAt'`**。

**⭐ 证明**（对 `w₁` 用 `DWalk.rec`，与第 3 步**同构**）：

* `w₁ = nil`：左端 `cons s₂ w₂`，`seamOpenP = True` —— **合取归约**。
* `w₁ = cons s₁ (nil ...)`：拼接 = `cons s₁ (cons s₂ w₂)`，
  `DOpen'` **定义上**就是 `openAt' s₁ s₂ ∧ DOpen' (cons s₂ w₂)` ——
  **而 `seamOpenP` 在单步 `w₁` 上**就取 `openAt' s₁ s₂`**（`rfl`）。
* `w₁ = cons s₁ (cons s' r)`：拆出 `openAt' s₁ s'`（**左段内部**），余下交 `ih`；
  **`seamOpenP` 只看末步**（`seamOpenP_cons_cons` 为 `rfl`），故原样传给 `ih`。

**⚠ 与第 3 步的**真正差别**：第 3 步在单步情形可以不 `rfl` 匹配（因 `seamOpen` 与 `openAt` 的
`fwd/bwd` 分支相同）；**此处 `openAt'` 含 `Reach`，`rfl` 匹配**只在 `lastStepOpt` 层**，
**collider 的后代分支具体形态**由 `openAt'` 自己决定** —— 故证明**结构不变**。** -/
theorem dopen'_append_cons_iff (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c d : V} (s₂ : DStep G b c) (w₂ : DWalk G c d) (w₁ : DWalk G a b) :
    DOpen' G Z (dwalkApp G w₁ (.cons s₂ w₂)) ↔
      DOpen' G Z w₁ ∧ seamOpenP G Z w₁ s₂ ∧ DOpen' G Z (.cons s₂ w₂) := by
  induction w₁ using DWalk.rec with
  | nil =>
    show DOpen' G Z (.cons s₂ w₂) ↔ True ∧ True ∧ DOpen' G Z (.cons s₂ w₂)
    tauto
  | cons s₁ w₁' ih =>
    cases w₁' with
    | nil =>
      -- `w₁ = cons s₁ (nil)`：拼接 = `cons s₁ (cons s₂ w₂)`，接缝 = `openAt' s₁ s₂`
      show DOpen' G Z (.cons s₁ (.cons s₂ w₂)) ↔
        DOpen' G Z (.cons s₁ (.nil _)) ∧ openAt' G s₁ s₂ Z ∧ DOpen' G Z (.cons s₂ w₂)
      rw [show DOpen' G Z (.cons s₁ (.cons s₂ w₂))
            = (openAt' G s₁ s₂ Z ∧ DOpen' G Z (.cons s₂ w₂)) from rfl,
          show DOpen' G Z (.cons s₁ (.nil _)) = True from rfl]
      tauto
    | cons s' r =>
      -- `w₁ = cons s₁ (cons s' r)`：拆出 `openAt' s₁ s'`，余下交归纳假设
      rw [dwalkApp_cons]
      rw [show DOpen' G Z (.cons s₁ (dwalkApp G (.cons s' r) (.cons s₂ w₂)))
            = (openAt' G s₁ s' Z ∧ DOpen' G Z (dwalkApp G (.cons s' r) (.cons s₂ w₂)))
            from rfl,
          ih s₂]
      rw [show DOpen' G Z (.cons s₁ (.cons s' r))
            = (openAt' G s₁ s' Z ∧ DOpen' G Z (.cons s' r)) from rfl,
          show seamOpenP G Z (.cons s₁ (.cons s' r) : DWalk G _ _) s₂
            = seamOpenP G Z (.cons s' r) s₂ from rfl]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

/-- ⭐⭐⭐⭐ **标准版路径分解（主定理）**：

$$\boxed{\ \mathrm{DOpen}'\,(w_1 \mathbin{+\!+} w_2)
  \iff \mathrm{DOpen}'\,w_1 \;\wedge\; \mathrm{Seam}' \;\wedge\; \mathrm{DOpen}'\,w_2\ }$$

**🔹 这是「每条路径各算一段」在**标准 d-分离（含 collider 后代）下的精确形式**。

**⭐⭐ 对 Pearl 1.2.4 第 4 步的意义**：
第 3 步（`PearlPathDecomp`）的分解只在**简化版**下成立；
**本定理**给出**标准版的同一分解** ——
**于是「`X ⊥d Y | Z`」可以化归为「对每对 `(x,y)` 与每条路径，某一段或接缝阻断」，
而**每一段/接缝**都是**有限局部检查**（`openAt'` 只看一个三元组 + 后代可达性）。**

**⭐ 证明**：对 `w₂` 分类。空则拼接为 `w₁`（右单位 + 右接缝为 `True`）；
非空则用 `dopen'_append_cons_iff`。 -/
theorem dopen'_append_iff (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c) :
    DOpen' G Z (dwalkApp G w₁ w₂) ↔
      DOpen' G Z w₁ ∧ seamOpenWP G Z w₁ w₂ ∧ DOpen' G Z w₂ := by
  cases w₂ with
  | nil =>
    rw [dwalkApp_nil_right]
    show DOpen' G Z w₁ ↔ DOpen' G Z w₁ ∧ True ∧ True
    tauto
  | cons s₂ w₂ =>
    rw [show seamOpenWP G Z w₁ (.cons s₂ w₂) = seamOpenP G Z w₁ s₂ from rfl]
    exact dopen'_append_cons_iff G Z s₂ w₂ w₁

/-- ⭐⭐ **成立版**：补上接缝后，拼接保持标准开口。 -/
theorem dopen'_append_of_seam (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c)
    (h₁ : DOpen' G Z w₁) (hs : seamOpenWP G Z w₁ w₂) (h₂ : DOpen' G Z w₂) :
    DOpen' G Z (dwalkApp G w₁ w₂) :=
  (dopen'_append_iff G Z w₁ w₂).mpr ⟨h₁, hs, h₂⟩

/-- ⭐⭐ **反方向（无损）**：拼接标准开口 ⟹ 接缝标准开口。 -/
theorem seam_of_dopen'_append (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c) (h : DOpen' G Z (dwalkApp G w₁ w₂)) :
    seamOpenWP G Z w₁ w₂ :=
  ((dopen'_append_iff G Z w₁ w₂).mp h).2.1

/-! ### §3.3 ⭐⭐ **标准版分解的否定形态** -/

/-- ⭐⭐ **标准版：拼接不开口 ⟺ 三段中至少一段不开口**。

$$\neg\,\mathrm{DOpen}'\,(w_1 \mathbin{+\!+} w_2)
  \iff \neg\,\mathrm{DOpen}'\,w_1 \;\vee\; \neg\,\mathrm{Seam}'
    \;\vee\; \neg\,\mathrm{DOpen}'\,w_2$$

**⟹ 即**：**一条路径在标准 d-分离下被阻断**，
**总能归咎于**某一**具体位置**（左段内部、`openAt'` 接缝、或右段内部）。** -/
theorem not_dopen'_append (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c) :
    ¬ DOpen' G Z (dwalkApp G w₁ w₂) ↔
      ¬ DOpen' G Z w₁ ∨ ¬ seamOpenWP G Z w₁ w₂ ∨ ¬ DOpen' G Z w₂ := by
  rw [dopen'_append_iff]
  tauto

/-! ===========================================================================
  §4 ⭐⭐ **全局 Markov 性的图论侧收口**
  =========================================================================== -/

/-- ⭐⭐⭐ **全局 Markov 性的图论侧陈述**（**逐路径全称**）：

$$\mathrm{DSeparatedStd}\,G\,Z\,x\,y
  \iff \forall\, w : \mathrm{DWalk}\,G\,x\,y,\ \neg\,\mathrm{DOpen}'\,G\,Z\,w$$

**⚠ 诚实登记**：**本定理**本身平凡**（`not_exists`：`¬∃w ↔ ∀w, ¬`）。

**⭐ 但它是 §3 的**接口**：
**§3 的 `dopen'_append_iff` 是关于**单条路径**的；
**本定理**把「点分离」提升到**逐路径**层，
**于是 §3 的分解**立刻可用**** ——
**这就是「全局」二字的**精确内容**：**
**全局 = 对**所有**路径 —— 而每条路径可**逐段**检验。**

**⚠ 与第 3 步 `dsep_iff_all_blocked` 的**唯一差别**：
此处是**标准版** `DOpen'`（`openAt'`），**不是**简化版。** -/
theorem dsepStd_iff_all_blocked' (G : CausalDirection.CausalGraph V) (Z : Set V) (a b : V) :
    DSeparatedStd G Z a b ↔ ∀ w : DWalk G a b, ¬ DOpen' G Z w :=
  not_exists

/-- ⭐⭐ **否证工具**：给出一条**标准开口**路径，即证**不**分离。

**⟹ 要证 `¬ DSeparatedStd G Z a b`，只需一条**开口路径** ——
**而 §3 的分解说明这条路径可**分段独立构造**（左段 + 接缝 + 右段）。** -/
theorem not_dsepStd_of_dopen' (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (w : DWalk G a b) (h : DOpen' G Z w) : ¬ DSeparatedStd G Z a b :=
  fun hsep => (dsepStd_iff_all_blocked' G Z a b).mp hsep w h

/-- ⭐⭐⭐ **全局 Markov 性的**分段判定**（**本文件的**接口定理**，把 §3 与 §4 接起来**）：

若一条路径 `w = w₁ ++ w₂` 在**标准**定义下**不**开口，
则存在**一个具体位置**（左段 / `openAt'` 接缝 / 右段）**阻断**。

**⟹ 这是 Pearl 1.2.4 第 4 步**图论侧的结论形态**：
**「全局阻断」经过**逐路径**（`dsepStd_iff_all_blocked'`）
与**逐段**（`dopen'_append_iff`）两层化归后，
**每一个「阻断」都有**有穷的、可局部验证的**定位** ——
**这正是把无限路径空间化归为**有限检查**的关键。** -/
theorem blockedStd_has_local_witness (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c)
    (h : ¬ DOpen' G Z (dwalkApp G w₁ w₂)) :
    ¬ DOpen' G Z w₁ ∨ ¬ seamOpenWP G Z w₁ w₂ ∨ ¬ DOpen' G Z w₂ :=
  (not_dopen'_append G Z w₁ w₂).mp h

/-- ⭐⭐ **分段充分条件 ⟹ 标准分离**：

若对**每条**路径都能找到**某个段/接缝**阻断，则 `a` 与 `b` **标准 d-分离**。

**⟹ 这是**逐段验证 ⟹ 全局分离**的桥（标准版）。** -/
theorem dsepStd_of_forall_local_block (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (h : ∀ w : DWalk G a b, ¬ DOpen' G Z w) :
    DSeparatedStd G Z a b :=
  (dsepStd_iff_all_blocked' G Z a b).mpr h

/-- ⭐⭐ **集合版 × 逐路径 × 逐段**（**第 4 步的完整接口**）：

$$\Bigl(\forall x \in X,\ \forall y \in Y,\ x \perp_d y \mid Z\Bigr)
  \iff \Bigl(\forall x \in X,\ \forall y \in Y,\ \forall w : \mathrm{DWalk}\,G\,x\,y,\
    \neg\,\mathrm{DOpen}'\,G\,Z\,w\Bigr)$$

**⟹ 这是 §1 的 `dsep_set_iff_all_walks_blocked` 的**独立重述**
（为与 §4 的命名一致而保留）。**内部证明直接复用 §1。**

**⚠ 陈述本身仍平凡** —— **但它把 §3 的分解**接到集合版 d-分离上**：
**「`X ⊥d Y | Z`」⟹ 对每对 `(x,y)` 与每条路径，§4 的 `blockedStd_has_local_witness` 可用。** -/
theorem dsep_set_reduced_to_paths (G : CausalDirection.CausalGraph V) (Z X Y : Set V) :
    (∀ x ∈ X, ∀ y ∈ Y, DSeparatedStd G Z x y) ↔
    (∀ x ∈ X, ∀ y ∈ Y, ∀ w : DWalk G x y, ¬ DOpen' G Z w) :=
  dsep_set_iff_all_walks_blocked G Z X Y

/-! ===========================================================================
  §5 ⭐⭐ **与第 3 步（简化版）的**精确对照****
  =========================================================================== -/

/-- ⭐⭐ **两版分解的**并存陈述**（**第 3 步 + 第 4 步的合取**）。

**🔹 内容**：**同一条拼接 `w₁ ++ w₂`**，
**在**简化版（`DOpen`，第 3 步）与**标准版（`DOpen'`，本文件）下**
**都**满足**三段分解**** ——
**但接缝项**不同**（`seamOpenW` vs `seamOpenWP`）。

**⚠ 这正是**必须分别做**的原因**：
**`seamOpenW`**看起来**是 `seamOpenWP` 的特例，**但两者**在 collider 且有后代在 `Z` 时**不等价**
（`seamOpen` 假、`seamOpenP` 真）。**故**不能复用**。** -/
theorem dopen_append_both_versions (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c) :
    (DOpen G Z (dwalkApp G w₁ w₂) ↔
        DOpen G Z w₁ ∧ seamOpenW G Z w₁ w₂ ∧ DOpen G Z w₂) ∧
    (DOpen' G Z (dwalkApp G w₁ w₂) ↔
        DOpen' G Z w₁ ∧ seamOpenWP G Z w₁ w₂ ∧ DOpen' G Z w₂) :=
  ⟨dopen_append_iff G Z w₁ w₂, dopen'_append_iff G Z w₁ w₂⟩

/-- ⭐ **一方向**：`seamOpen` ⟹ `seamOpenP`（接缝从简化版抬到标准版）。

**🔹 内容**：若**简化版**接缝开口，则**标准版**接缝也开口（因为 `openAt ⟹ openAt'`）。

**⚠ 反方向** **不成立**（`openAt' ⟹ openAt` 假：collider 只有后代在 `Z` 时）。
**故**本定理**是单向的，**如实登记**。 -/
theorem seamOpen_imp_seamOpenP (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (s₂ : DStep G b c)
    (hs : seamOpen G Z w₁ s₂) : seamOpenP G Z w₁ s₂ := by
  unfold seamOpen at hs
  unfold seamOpenP
  cases h : lastStepOpt G w₁ with
  | none => trivial
  | some p => exact openAt_imp G (by rwa [h] at hs)

/-- ⭐⭐ **整条接缝的桥**：`seamOpenW ⟹ seamOpenWP`。 -/
theorem seamOpenW_imp_seamOpenWP (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (w₁ : DWalk G a b) (w₂ : DWalk G b c)
    (hs : seamOpenW G Z w₁ w₂) : seamOpenWP G Z w₁ w₂ := by
  unfold seamOpenW at hs
  unfold seamOpenWP
  cases h : firstStepOpt G w₂ with
  | none => trivial
  | some p => exact seamOpen_imp_seamOpenP G Z w₁ p.2 (by rwa [h] at hs)

end PearlGlobalMarkov

end FateV2.Predict