import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorMarkov
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

/-!
  # Predict · BridgeView3AtomStratification

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeView3AtomStratification.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, DAGFactorization, FactorMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeView3AtomStratification`
  —— 「图 ⟹ 概率」桥的**第 3 条非塔策略：原子分层（atom stratification）**

  ⚠ **P-006 修复登记（必读，勿跳过）**

  本文件由 P-006 分诊判为 **FIX**，原始状态 **10 error / 15 定理**。修复中我逐条核验
  了每条陈述是否为真，**并非只把编译错误消掉**。核验结果导致三处**实质性让步**，
  全部如实登记如下：

  ### R1. 删除 `A_family_Yconst` / `B_family_Xconst`（原 §4 两条）
  原陈述是 `(∏ v ∈ A, f v (...)) = (∏ v ∈ A, f v (...))` —— **左右逐字相同**，
  证明就是 `rfl`，`linter` 已报 `hA`/`hB` 未被引用。**这是空壳恒等式，零内容**，
  留着会让「15 定理」的计数虚高。已删。

  ### R2. 删除 `FiberSplitAt.prod_form` —— **原陈述为假**
  原陈述：从 `FiberSplitAt X Y Z p w`（`∃ lam F, F 不依赖第一参数 ∧ F 不依赖第二参数 ∧
  p[w;·;·] = lam * F · ·`）推出 `∃ lam fA fB, p[...] = lam * fA ux * fB uy`。
  **反例**：取 `lam = 1`、`F ≡ 2`。则 `fA ux = F ux w = 2`、`fB uy = F w uy = 2`，
  右边 `= 1 * 2 * 2 = 4`，左边 `= 1 * 2 = 2`，`4 ≠ 2`。
  本质原因：`lam * fA * fB` 有三个乘子，而 `lam * F` 只有两个；多出的那个 `fB`
  无从消去。**该定理不可证，且陈述为假，已删除。**
  替代品是 `FiberSplitAt.const_form`（见 R3），它才是该定义的**真实内容**。

  ### R3. `FiberSplitAt` 定义本身是**退化的** —— 必须登记
  `FiberSplitAt` 的两条「不依赖」条件合起来意味 `F ux uy = F w w` 对**所有** `ux, uy`
  成立（`hY ux uy w` 去第二参数、`hX w ux w` 去第一参数）。
  ⟹ `FiberSplitAt X Y Z p w` 等价于「`p` 在 `Z` 钉死处**是常数**」。
  机器验证见 `FiberSplitAt.const_form`：`FiberSplitAt ⟹ ∃ lam, ∀ ux uy, p[...] = lam`。
  **故「纤维分裂」这个名字名不副实**：它没有分裂出任何东西，只是一个常数性判据。
  我保留该定义（不删，以免破坏可能的外部引用形状），但**不再声称它等价于乘积分裂**；
  主定理改用 `const_form` 陈述，这是能证的、同时也是诚实的（虽然弱）。

  ### R4. `fiber_split_of_reads` 的前件 `hXA` / `hYB` 是**冗余的**
  原证明里 `hXA`（`A` 族不读 `X`）与 `hYB`（`B` 族不读 `Y`）**从未被引用**
  （`linter` 已报警告）。该定理的真实内容是纯代数的：
  `hfac` 展开 + `hDZ`（`D` 族只读 `Z`，故冻结为 `∏_D f v w`）+ `Finset.prod_union` 拆 `D | A∪B`，
  再拆 `A | B`，`ring` 收尾。**结论仍是真的**（不是空壳：`∏_D` 确实被换成 `∏_D f v w`），
  但**「读集分族」对它是多余装饰**，文件头原先声称「这就是原子分层，A/B 两族各自只读一侧」
  是**夸大**。已把 `hXA`/`hYB` 改名为 `_hXA`/`_hYB` 并在定理文档里如实标注为「未使用」。

  ### R5. 补齐真正缺失的前件 `hA : Disjoint A B`
  `fiber_split_of_reads` 用了 `Finset.prod_union hA` 把 `∏_{A∪B}` 拆成 `∏_A * ∏_B`，
  但原签名里**没有** `Disjoint A B`。原代码在 `fiberSplitAt_of_reads` 里试图用不存在的
  `hD_AB hD` 从 `Disjoint D (A ∪ B)` 推出 `Disjoint A B` —— **推不出来**
  （反例：`D = ∅`、`A = B = univ` 满足 `D ∪ (A∪B) = univ` 且 `Disjoint D (A∪B)`，
  但 `A ∩ B = univ ≠ ∅`）。这是原 10 个 error 的主因之一。已作为**显式前件**补上。

  ### R6. 删除 `fiberSplitAt_of_reads`（原 §5 的 `FiberSplitAt` 装配定理）
  它要证 `FiberSplitAt` 的首条（`∏_A f` 不依赖 `ux`）与次条（`∏_B f` 不依赖 `uy`），
  但在 `mergeOn` 里 `ux` 落在 `X` 位、`uy` 落在 `Y` 位：
  * `∏_A f` 不依赖 `ux` 需要「`A` 族不读 `X`」，而 `A` 族的本意是「不读 `Y`」；
  * `∏_B f` 不依赖 `uy` 需要「`B` 族不读 `Y`」，而 `B` 族的本意是「不读 `X`」。
  原代码在 `B` 族分支里调 `hXA`（`hXA` 要求 `v ∈ A`，这是**用错前提**），
  这正是 error `hXAB_aux` / `hD_AB` 的来源。
  **若要修好，必须再补 `hXB`（`B` 族不读 `X`）与 `hYA`（`A` 族不读 `Y`）两条前件；
  但补完之后 `FiberSplitAt` 按 R3 退化为「常数」，装配定理就空了。**
  ⟹ 该装配定理**无实质内容可救**，已删。真内容在 `fiber_split_of_reads`（乘积形态），
  已单独保留。

  ### R7. 保留 `sum_comm_half`（诚实的退化登记，非假命题）
  `Xsum = Ysum` 由 `Finset.sum_comm` 给出，**无需任何图论假设**，前件为空、恒真。
  严格说它是「重言」，但它是**被明确标注为「退化那一半」的诊断定理**（文件头 §0/§1 与
  定理文档都逐字承认「不需要任何图论假设」「保留此定理是为把退化的那一半精确地定理化」）。
  它不是**假**陈述，也不是**把结论塞进前件**的同义反复；它诚实地记录了本策略的空洞之处。
  故**保留**，但读者不应把它当作桥的任何进展。

  ### 修复结果
  * 定理数：**15 → 12**（删 4 条：2 空壳 + 1 假陈述 + 1 不可救的装配；新增 1 条 `const_form`）。
  * error：**10 → 0**；**零 `sorry` / 零 `admit` / 零 `axiom`**。
  * **无下游**：经两种 grep 模式（`FateV2.Predict.BridgeView3` 前缀、`BridgeView3.` 限定）
    确认本模块**不在 `Fate.lean` 中、未被任何 `.lean` import**，改动零外部影响。

  ---

  ## 0 一句话（原文，保留并修正措辞）

  > **把桥的两半切开，两半都不碰 `mass` 的复合：**
  > **(α) 概率半边**：因子分解 ⟹ `D` 族被冻结、`A`/`B` 两族按读集拆开（`Finset.prod_union`）；
  > **(β) 图侧半边**：本文件**原本**设想的 `ReadBisect` 与 `bridge_of_bisect` **已不在本文件**
  > （它们随 R6 一并失效，见上）；实际交付的图侧内容为零。
  > **⟹ 故本文件现在只是「概率半边」的一个纯代数引理集，不构成桥。**

  ## 1 为什么这是「第 3 条」

  * **策略 1**（`BridgeStrategy1TopoPeel`）：拓扑序 sink 剥离 + 诱导子图归纳 ——
    卡在**库缺口 `DAG.induce`**。
  * **策略 2**（`BridgeView2Elimination`）：把 `mass (V∖{v})` 一次性算成「对 `v` 求和」
    （`peel`）—— 落点是 **sink 处的消元定律**，终点仍是集合口径 `mass`；
    而集合口径已被判定 **退化**（`Fate.View20.facstep_globalMarkov_anyGraph`）。
  * **策略 3（本文件）**：**不归纳、不用诱导子图、不复合 `mass`**。
    概率侧只保留「一个因子族如何被 `prod_union` 拆成两块」。

  ## 2 失败模式对照

  | 历史失败模式 | 机制 | 本文件对策 |
  |---|---|---|
  | `mass` 塔 | `mass S (mass T p)` 为假（`TowerAudit.mass_idempotent_fails`）| 全程**无 `mass`** |
  | 集合口径退化 | `CondMulLike` 四个 `mass` 取**同一** `x` | 终点是**乘积形态**（`fiber_split_of_reads`）|
  | 结论入前件 | `FactorizesOn` 定义即可分离 | 前件只有 `hfac`（因子分解）+ 分块不交，**结论是 `∏_D` 换成 `∏_D f v w`**，非前件子式 |
  | **前件冗余（本次实测）** | `hXA`/`hYB` 未被引用 | 已改名 `_hXA`/`_hYB` 并在文档标注（R4），不掩盖 |

  ## 3 交付清单（全部 `EXIT=0`，零 `sorry` / 零 `axiom`）

  | # | 名字 | 内容 | 状态 |
  |---|---|---|---|
  | V3-1 | `mergeOn` | 三点拼接 `[w on Z; ux on X; uy on Y; x elsewhere]` | ✅ |
  | V3-2 | `mergeOn_Z/X/Y/else` | 拼接的坐标律 | ✅ |
  | V3-3 | `mergeOn_congr_off` | 其余坐标无关性 | ✅ |
  | V3-4 | `Xsum` / `Ysum` | 两个**单层**算子（只差求和次序）| ✅ |
  | V3-5 | `Xsum_congr_off` / `Ysum_congr_off` | 算子只依赖 `Z ∪ X ∪ Y` 上的值 | ✅ |
  | V3-6 | `prod_congr_of_reads` | 只读 `Z` 的因子族在拼接点一致 | ✅ |
  | V3-7 | `sum_sum_const_of_Zlocal` | `Z`-局部函数在两层求和里是常数 | ✅ |
  | V3-8 | **`fiber_split_of_reads`** | **主定理**：`D` 冻结 + `A`/`B` 拆开（乘积形态）| ✅ |
  | V3-9 | `FiberSplitAt` / `FiberSplitAt.const_form` | 定义 + **其真实内容（退化：即常数性）** | ✅（R3 登记）|
  | V3-10 | `sum_comm_half` | 「求和次序」那一半的**退化登记**（无图论假设）| ✅（R7 登记）|
  | — | ~~`A_family_Yconst`~~ / ~~`B_family_Xconst`~~ | ~~`rfl` 空壳~~ | ❌ 删（R1）|
  | — | ~~`FiberSplitAt.prod_form`~~ | ~~**陈述为假**~~ | ❌ 删（R2）|
  | — | ~~`fiberSplitAt_of_reads`~~ | ~~装配定理，用错前提且修补后为空~~ | ❌ 删（R6）|

  ## 4 ⚠ 诚实边界

  1. **本文件不构成桥。** 原文件头的 `ReadBisect` / `bridge_of_bisect` / `chain_bisect` /
     `collider_not_bisect` / `ancestor_not_bisect` / `dSep_gives_bisect_inputs` 等图侧定理
     **在原文件中就从未编译通过**（正是那 10 个 error 的一部分），本次修复**未**重建它们。
     ⟹ 现在交付的是**纯代数半边**，且我明确标注它**不是桥**。
  2. `FiberSplitAt` **已退化**（R3），不要用它当「纤维分裂」的证据。
  3. `fiber_split_of_reads` 的 `hXA`/`hYB` **未被使用**（R4），「A/B 两族各自只读一侧」
     的说法对证明无贡献，仅是陈述上的装饰。
  4. **零 `mass`**（本文件不 `open` 也不使用 `mass`）。
  =========================================================================== -/

namespace FateV2.Predict.BridgeView3

open FateV2.Modeling

open Finset FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §1 三点拼接 `[w on Z; ux on X; uy on Y; x elsewhere]`
  =========================================================================== -/

/-- ⭐ **参数化三点拼接**：`Z` 上取 `w`、`X` 上取 `ux`、`Y` 上取 `uy`、其余取 `x`。 -/
def mergeOn (X Y Z : Finset V) (w ux uy x : V → α) : V → α :=
  fun j => if j ∈ Z then w j else if j ∈ X then ux j else if j ∈ Y then uy j else x j

variable {X Y Z : Finset V}

/-- ⭐⭐ **`mergeOn` 在 `Z` 位取 `w`**（**无需任何不交假设**：`Z` 优先）。 -/
theorem mergeOn_Z {w ux uy x : V → α} {j : V} (hj : j ∈ Z) :
    mergeOn X Y Z w ux uy x j = w j := by
  unfold mergeOn; rw [if_pos hj]

/-- ⭐⭐ **`mergeOn` 在 `X` 位取 `ux`**（需 `X`、`Z` 不交）。 -/
theorem mergeOn_X (hXZ : Disjoint X Z) {w ux uy x : V → α} {j : V} (hj : j ∈ X) :
    mergeOn X Y Z w ux uy x j = ux j := by
  unfold mergeOn
  rw [if_neg (fun h => (Finset.disjoint_left.mp hXZ) hj h), if_pos hj]

/-- ⭐⭐ **`mergeOn` 在 `Y` 位取 `uy`**（需 `Y` 与 `Z`、`X` 都不交）。 -/
theorem mergeOn_Y (hXY : Disjoint X Y) (hYZ : Disjoint Y Z)
    {w ux uy x : V → α} {j : V} (hj : j ∈ Y) :
    mergeOn X Y Z w ux uy x j = uy j := by
  unfold mergeOn
  rw [if_neg (fun h => (Finset.disjoint_left.mp hYZ) hj h),
      if_neg (fun h => (Finset.disjoint_left.mp hXY) h hj), if_pos hj]

/-- ⭐⭐ **`mergeOn` 在 `Z ∪ X ∪ Y` 之外取 `x`**。 -/
theorem mergeOn_else {w ux uy x : V → α} {j : V}
    (hZ : j ∉ Z) (hX : j ∉ X) (hY : j ∉ Y) :
    mergeOn X Y Z w ux uy x j = x j := by
  unfold mergeOn; rw [if_neg hZ, if_neg hX, if_neg hY]

/-- ⭐⭐⭐ **`mergeOn` 的其余坐标无关性**：`x`、`x'` 在 `Z ∪ X ∪ Y` 之外一致 ⟹ 结果相同。 -/
theorem mergeOn_congr_off {w ux uy : V → α} {x x' : V → α}
    (h : ∀ u, u ∉ Z → u ∉ X → u ∉ Y → x u = x' u) :
    mergeOn X Y Z w ux uy x = mergeOn X Y Z w ux uy x' := by
  funext j
  unfold mergeOn
  by_cases hZ : j ∈ Z
  · rw [if_pos hZ, if_pos hZ]
  · by_cases hX : j ∈ X
    · rw [if_neg hZ, if_pos hX, if_neg hZ, if_pos hX]
    · by_cases hY : j ∈ Y
      · rw [if_neg hZ, if_neg hX, if_pos hY, if_neg hZ, if_neg hX, if_pos hY]
      · rw [if_neg hZ, if_neg hX, if_neg hY, if_neg hZ, if_neg hX, if_neg hY,
          h j hZ hX hY]

/-! ===========================================================================
  §2 两个**单层**算子（`Z` 钉死为 `w`）
  =========================================================================== -/

/-- ⭐⭐⭐ **`X`-侧算子**：先对 `Y` 求和、再对 `X` 求和（`Z` 钉死 `w`，其余取 `x`）。 -/
noncomputable def Xsum (X Y Z : Finset V) (p : (V → α) → ℝ) (x w : V → α) : ℝ :=
  ∑ ux : V → α, ∑ uy : V → α, p (mergeOn X Y Z w ux uy x)

/-- ⭐⭐⭐ **`Y`-侧算子**：先对 `X` 求和、再对 `Y` 求和。**与 `Xsum` 只差求和次序。** -/
noncomputable def Ysum (X Y Z : Finset V) (p : (V → α) → ℝ) (x w : V → α) : ℝ :=
  ∑ uy : V → α, ∑ ux : V → α, p (mergeOn X Y Z w ux uy x)

/-- ⭐⭐ **`Xsum` 与"其余坐标"无关**。 -/
theorem Xsum_congr_off (p : (V → α) → ℝ) {x x' w : V → α}
    (h : ∀ u, u ∉ Z → u ∉ X → u ∉ Y → x u = x' u) :
    Xsum X Y Z p x w = Xsum X Y Z p x' w := by
  unfold Xsum
  refine Finset.sum_congr rfl fun ux _ => Finset.sum_congr rfl fun uy _ => ?_
  rw [mergeOn_congr_off h]

/-- ⭐⭐ **`Ysum` 与"其余坐标"无关**。 -/
theorem Ysum_congr_off (p : (V → α) → ℝ) {x x' w : V → α}
    (h : ∀ u, u ∉ Z → u ∉ X → u ∉ Y → x u = x' u) :
    Ysum X Y Z p x w = Ysum X Y Z p x' w := by
  unfold Ysum
  refine Finset.sum_congr rfl fun uy _ => Finset.sum_congr rfl fun ux _ => ?_
  rw [mergeOn_congr_off h]

/-! ===========================================================================
  §3 代数核心
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **只读 `Z` 的因子族在两个拼接点一致**（`Finset.prod_congr`）。 -/
theorem prod_congr_of_reads {A B : Finset V} {f : V → (V → α) → ℝ}
    (hA : ∀ v, v ∈ A → ∀ y y' : V → α, (∀ u ∈ Z, y u = y' u) → f v y = f v y')
    (hB : ∀ v, v ∈ B → ∀ y y' : V → α, (∀ u ∈ Z, y u = y' u) → f v y = f v y')
    {w ux uy x : V → α} :
    (∏ v ∈ A, f v (mergeOn X Y Z w ux uy x)) = (∏ v ∈ A, f v (mergeOn X Y Z w ux uy w))
    ∧ (∏ v ∈ B, f v (mergeOn X Y Z w ux uy x)) = (∏ v ∈ B, f v (mergeOn X Y Z w ux uy w)) := by
  have hkey : ∀ (D : Finset V) (g : V → (V → α) → ℝ),
      (∀ v, v ∈ D → ∀ y y' : V → α, (∀ u ∈ Z, y u = y' u) → g v y = g v y') →
      (∏ v ∈ D, g v (mergeOn X Y Z w ux uy x)) = (∏ v ∈ D, g v (mergeOn X Y Z w ux uy w)) :=
    fun D g hg => Finset.prod_congr rfl fun v hv => hg v hv _ _ fun u hu => by
      rw [mergeOn_Z (X := X) (Y := Y) (Z := Z) hu, mergeOn_Z (X := X) (Y := Y) (Z := Z) hu]
  exact ⟨hkey A f hA, hkey B f hB⟩

/-- ⭐⭐⭐ **求和层面的读集游离**：`f` 只读 `Z` ⟹ 在 `X`/`Y` 两层求和里是常数。 -/
theorem sum_sum_const_of_Zlocal {g : (V → α) → ℝ}
    (hg : ∀ y y' : V → α, (∀ u ∈ Z, y u = y' u) → g y = g y')
    {w ux uy x : V → α} :
    (∑ ux' : V → α, ∑ uy' : V → α, g (mergeOn X Y Z w ux' uy' x))
      = (Fintype.card (V → α) : ℝ) * (Fintype.card (V → α) : ℝ) * g (mergeOn X Y Z w ux uy w) := by
  classical
  set n : ℝ := (Fintype.card (V → α) : ℝ) with hn
  have h1 : ∀ ux' : V → α, (∑ uy' : V → α, g (mergeOn X Y Z w ux' uy' x))
      = n * g (mergeOn X Y Z w ux uy w) := by
    intro ux'
    rw [show (∑ uy' : V → α, g (mergeOn X Y Z w ux' uy' x))
        = ∑ _uy' : V → α, g (mergeOn X Y Z w ux uy w) from
      Finset.sum_congr rfl fun uy' _ =>
        hg _ _ fun u hu => by
          rw [mergeOn_Z (X := X) (Y := Y) (Z := Z) hu, mergeOn_Z (X := X) (Y := Y) (Z := Z) hu]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
  calc (∑ ux' : V → α, ∑ uy' : V → α, g (mergeOn X Y Z w ux' uy' x))
      = ∑ _ux' : V → α, n * g (mergeOn X Y Z w ux uy w) := Finset.sum_congr rfl fun i _ => h1 i
    _ = n * (n * g (mergeOn X Y Z w ux uy w)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
    _ = n * n * g (mergeOn X Y Z w ux uy w) := by ring
    _ = (Fintype.card (V → α) : ℝ) * (Fintype.card (V → α) : ℝ) *
          g (mergeOn X Y Z w ux uy w) := by rw [hn]

/-! ===========================================================================
  §4 主定理：`D` 族冻结 + `A`/`B` 两族拆开
  =========================================================================== -/

section MainProb

variable {p : (V → α) → ℝ} {f : V → (V → α) → ℝ} {c₀ : ℝ}
variable {D A B : Finset V}

/-- ⭐⭐⭐⭐⭐ **主定理（乘积形态）：`D` 族冻结为 `∏_D f v w`，`A`/`B` 两族分离。**

设 `D ∪ (A ∪ B) = univ`、`D` 与 `A ∪ B` 不交、`A` 与 `B` 不交，且
`v ∈ D ⟹ f v` 只读 `Z` 位。则对任意 `u_x, u_y`：

$$p[w;u_x;u_y]
 =\underbrace{\Bigl(\prod_{D}f_v(w)\Bigr)\cdot c}_{\text{层权}}\cdot
  \Bigl(\prod_{A}f_v[w;u_x;u_y]\Bigr)\cdot
  \Bigl(\prod_{B}f_v[w;u_x;u_y]\Bigr).$$

**⚠ 诚实标注（R4）**：`_hXA` / `_hYB` 两个读集前提**在证明中未被使用**
（原签名有此前提但证明不引用）。去掉它们定理仍成立。它们被保留以维持调用方形状，
但读者**不应**认为「A 族不读 X、B 族不读 Y」对本案有贡献。 -/
theorem fiber_split_of_reads
    (hfac : ∀ x, p x = (∏ v, f v x) * c₀)
    (_hpart : D ∪ (A ∪ B) = (univ : Finset V))
    (hD : Disjoint D (A ∪ B))
    (hA : Disjoint A B)
    (_hDZ : ∀ v, v ∈ D → ∀ y y' : V → α, (∀ u ∈ Z, y u = y' u) → f v y = f v y')
    (_hXA : ∀ v, v ∈ A → ∀ y y' : V → α, (∀ u ∈ X, y u = y' u) → f v y = f v y')
    (_hYB : ∀ v, v ∈ B → ∀ y y' : V → α, (∀ u ∈ Y, y u = y' u) → f v y = f v y')
    (w ux uy : V → α) :
    p (mergeOn X Y Z w ux uy w)
      = ((∏ v ∈ D, f v w) * c₀) *
        ((∏ v ∈ A, f v (mergeOn X Y Z w ux uy w)) *
         (∏ v ∈ B, f v (mergeOn X Y Z w ux uy w))) := by
  classical
  rw [hfac]
  have h1 : (∏ v, f v (mergeOn X Y Z w ux uy w))
      = (∏ v ∈ D, f v (mergeOn X Y Z w ux uy w)) *
        (∏ v ∈ (A ∪ B), f v (mergeOn X Y Z w ux uy w)) := by
    rw [← _hpart, Finset.prod_union hD, mul_comm]
  have h2 : (∏ v ∈ (A ∪ B), f v (mergeOn X Y Z w ux uy w))
      = (∏ v ∈ A, f v (mergeOn X Y Z w ux uy w)) *
        (∏ v ∈ B, f v (mergeOn X Y Z w ux uy w)) :=
    Finset.prod_union hA
  have hDconst : (∏ v ∈ D, f v (mergeOn X Y Z w ux uy w)) = (∏ v ∈ D, f v w) :=
    Finset.prod_congr rfl fun v hv => _hDZ v hv _ _ fun u hu => by
      rw [mergeOn_Z (X := X) (Y := Y) (Z := Z) hu]
  rw [h1, h2, hDconst]
  ring

/-! ===========================================================================
  §5 `FiberSplitAt`：定义 + **其真实内容（退化）**
  =========================================================================== -/

/-- ⭐⭐ **`FiberSplitAt`**（原始定义，保留形状）。

**⚠ R3：本定义已退化。** 两条「不依赖」条件合起来使 `F ux uy = F w w`
对**所有** `ux, uy` 成立，故 `FiberSplitAt X Y Z p w` 等价于
「`p` 在 `Z` 钉死处是常数」。见 `FiberSplitAt.const_form`。

**它不表达「纤维分裂」**：没有任何乘积结构被分裂出来。名字是历史遗留。 -/
def FiberSplitAt (X Y Z : Finset V) (p : (V → α) → ℝ) (w : V → α) : Prop :=
  ∃ (lam : ℝ) (F : (V → α) → (V → α) → ℝ),
    (∀ uy : V → α, ∀ ux ux' : V → α, F ux uy = F ux' uy) ∧
    (∀ ux : V → α, ∀ uy uy' : V → α, F ux uy = F ux uy') ∧
    ∀ ux uy : V → α, p (mergeOn X Y Z w ux uy w) = lam * F ux uy

/-- ⭐⭐⭐ **`FiberSplitAt` 的真实内容：`p` 在此纤维上是常数。**

这是 `FiberSplitAt` **能**推出的全部（`F` 的两个参数都不可用 ⟹ `F ≡ F w w`）。

**替代原来的 `FiberSplitAt.prod_form`**（R2：原陈述为假，已删）。 -/
theorem FiberSplitAt.const_form (h : FiberSplitAt X Y Z p w) :
    ∃ lam : ℝ, ∀ ux uy : V → α, p (mergeOn X Y Z w ux uy w) = lam := by
  obtain ⟨lam, F, hX, hY, hpt⟩ := h
  refine ⟨lam * F w w, fun ux uy => ?_⟩
  rw [hpt, hY ux uy w, hX w ux w]

end MainProb

/-! ===========================================================================
  §6 「求和次序」那一半的**退化登记**（R7）
  =========================================================================== -/

section CommHalf

variable {p : (V → α) → ℝ}

/-- ⭐⭐ **`Xsum = Ysum`：纯 `Finset.sum_comm`，无任何图论/因子分解假设。**

**⚠ R7：这是重言式的退化登记，不是桥的任何进展。**
`Xsum` 与 `Ysum` 的定义**只差求和次序**，故等式恒成立。
保留它只为把「策略 3 的求和次序那一半是空的」精确地定理化，防止再被当作桥。 -/
theorem sum_comm_half (p : (V → α) → ℝ) (w : V → α) :
    Xsum X Y Z p w w = Ysum X Y Z p w w :=
  Finset.sum_comm

end CommHalf

end FateV2.Predict.BridgeView3
