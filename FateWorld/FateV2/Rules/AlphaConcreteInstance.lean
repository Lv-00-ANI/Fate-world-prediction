/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.AlphaConcreteInstance
阶段：**阶段 1B —— α（取概念过程）的完整具体实例**

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
`Fate.Alpha` 里 α 是 `takeConcept B = closureOp B`——**一个具体函数**，
但该文件**没有给出任何一个具体的 (G, M, I)**。
本文件补上这个缺口：给出**一个完整实例**，其规模为

  * 对象：`G = Fin 3`（3 个对象）
  * 属性：`M = Fin 2`（2 个属性）

并把 α 在**全部 4 个属性子集**上的取值**逐条算出**，
再把 α 的 5 条结构性质在该实例上**落地**：

| 编号 | 内容 | 定理 |
|---|---|---|
| I1 | 实例本身（`K3`）与关系表（6 格全列） | `Irel_0_0` … `Irel_2_1` |
| I2 | α 在 4 个属性子集上的**取值** | `takeConcept_eq_empty` / `_a` / `_b` / `_ab` |
| I3 | α 的输出**确为闭集**（值域正确） | `alpha_*_closed` |
| I4 | α **幂等**（再取一次不变） | `alpha_idem_instance` |
| I5 | α **扩张**（且严格）+ **单调** | `subset_alpha_instance` / `alpha_strictly_expands` / `alpha_mono_instance` |
| I6 | 闭集恰 3 个；α **非单射**（纤维 = 压缩内容） | `closed_sets_are` / `alpha_not_injective` / `fiber_ab` |
| I7 | 编码算子 `enc` + **自洽性** `Coherent`（实例上为真） | `enc3` / `enc_coherent` |
| I8 | `α ∘ enc` **保持**抽象等价 `∼_E`，且**在商上良定义** | `alpha_respects_equiv_instance` / `alphaOnQuotient_instance` |
| I9 | E8（离散化误差）**诚实处置** | `e8_instance_satisfiable` |

---------------------------------------------------------------------------
实例设计（意在地给出**非平凡**的概念格）
---------------------------------------------------------------------------
关系表 `I ⊆ G × M`（行 = 对象，列 = 属性 `a = 0`, `b = 1`）：

|        | a (0) | b (1) |
|--------|-------|-------|
| g=0    | ✓     | ✓     |
| g=1    | ✓     | ✗     |
| g=2    | ✗     | ✗     |

即 `I(g, m) ⟺ g = 0 ∨ (g = 1 ∧ m = 0)`。

由此 α 的**全部作用**为：

```
α(∅)    = ∅
α({a})  = {a}         （已闭）
α({b})  = {a,b}       （唯一的非平凡扩张）
α({a,b})= {a,b}       （已闭）
```

———————————————————————————————————————————————————————————————
⚠ 本文件**不是**「又一套定义」：`K3` 是 `Fate.Alpha` 的 `FormalCtx` 的
一个**取值**，`takeConcept`/`isClosed`/`idem`/`mono`/`alpha_respects_equiv`
**全部直接调用** `Fate.Alpha` 的定理。本文件是它的**消费方**（consumer）。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
1. **不含** `sorry`、**不含** `axiom`；`#print axioms` 只出现 3 个标准公理
   （`propext`、`Classical.choice`、`Quot.sound`）。
2. E8（离散化误差界）在本实例中**仍然不填** $g$ 的具体表达式——
   依 `Fate.Alpha` §4 的登记，填数即为虚构。
   本文件只给出 `E8Holds` 在**空胞腔**上的可满足性（I9），并如实标注其弱。
3. `∼_E` 的判据是待裁决项 Q-3；本文件取**最粗**的等价关系（`⊤`），
   目的是让 `RespectsEquiv` 的前件**在本实例上为真**——
   这是**验证** α 保抽象的蕴含式，不是对 Q-3 的裁决。
-/

import FateWorld.FateV2.Rules.Alpha
namespace FateV2.Rules

open FateV2.Model
namespace AlphaInstance

open Set

/-!
  # Rules · AlphaConcreteInstance

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaConcreteInstance.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Alpha
  - 补充 open 域：FateV2.Model
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  实例：形式背景 𝕂 = (G, M, I)，3 个对象 × 2 个属性
    =========================================================================== -/

/-- **对象集** $G_{\mathrm{FCA}} = \{0, 1, 2\}$（3 个对象）。 -/
abbrev G3 : Type := Fin 3

/-- **属性集** $M_{\mathrm{FCA}} = \{a, b\} = \{0, 1\}$（2 个属性）。 -/
abbrev M2 : Type := Fin 2

/-- **对象–属性关系** $I$：

```
I(g, m)  ⟺  g = 0  ∨  (g = 1 ∧ m = 0)
```

即 `I 0 = 全真`、`I 1 = 仅 a`、`I 2 = 全假`。

**为什么不写成 `Fin` 上的模式匹配**：模式匹配要用依赖的 `⟨0, _⟩`，
它在 `simp`/`decide` 下的归约被 proof-irrelevance 卡住；
写成**等式析取**后每条都能由 `simp`/`fin_cases` 直接算出。 -/
def I3 (g : G3) (m : M2) : Prop := g = 0 ∨ (g = 1 ∧ m = 0)

/-- **唯一的形式背景**（本实例）。

⚠ 用 `abbrev` 而非 `def`：使其在**实例搜索**中可展开
（`K3.MFCA` 展开为 `Fin 2` 后，`Fintype`/`OfNat` 实例才自动可得，
下游 `fin_cases`、数字字面量才可用）。 -/
abbrev K3 : FormalCtx where
  GFCA := G3
  MFCA := M2
  Irel := I3

/-! ### §1.1 关系表登记（**逐格核实**，6 个格全列出）

这不是装饰：把 `I3` 的**每一格**都钉成一条定理，
下游任何「实例被静默改动」都会立刻让本文件变红。 -/

theorem Irel_0_0 : I3 (0 : G3) (0 : M2) := Or.inl rfl

theorem Irel_0_1 : I3 (0 : G3) (1 : M2) := Or.inl rfl

theorem Irel_1_0 : I3 (1 : G3) (0 : M2) := Or.inr ⟨rfl, rfl⟩

theorem Irel_1_1 : ¬ I3 (1 : G3) (1 : M2) := by
  intro h; rcases h with h | ⟨_, h⟩ <;> simp at h

theorem Irel_2_0 : ¬ I3 (2 : G3) (0 : M2) := by
  intro h; rcases h with h | ⟨h, _⟩ <;> simp at h

theorem Irel_2_1 : ¬ I3 (2 : G3) (1 : M2) := by
  intro h; rcases h with h | ⟨h, _⟩ <;> simp at h

/-! ===========================================================================
    §2  α 在**全部 4 个**属性子集上的取值（逐个算出）
    =========================================================================== -/

/-- 属性子集 `{a} = {0}`（用 `abbrev` 使其在 `rw` 中可展开）。 -/
abbrev BA : Set M2 := {0}

/-- 属性子集 `{a,b} = {0,1} = univ`（用 `abbrev` 同理）。 -/
abbrev BAB : Set M2 := {0, 1}

/-- **`α` 的定义在本实例上的展开形式**。

`takeConcept B = closureOp B = polarUp (polarDown B)`（`rfl`，非新定义）。 -/
theorem alpha_eq (B : Set M2) : K3.takeConcept B = K3.polarUp (K3.polarDown B) := rfl

/-! ### §2.1 四条导出算子等式（α 的**全部计算基础**）

`α` 的每次取值都经 `polarDown` 再 `polarUp`，故先把导出算子算清。
**它们的正确性是 α 取值正确性的充要条件**。 -/

/-- `∅' = G`（所有对象都满足空属性集，空洞真）。 -/
theorem pD_empty : K3.polarDown (∅ : Set M2) = univ := by
  ext g; rw [FormalCtx.mem_polarDown_iff]; simp

/-- `G' = ∅`（对象 `2` 不满足任何属性，故无属性被全部对象满足）。 -/
theorem pU_univ : K3.polarUp (univ : Set G3) = (∅ : Set M2) := by
  ext m; rw [FormalCtx.mem_polarUp_iff]
  constructor
  · intro h
    have h2 := h (g := (2 : G3)) (by simp)
    fin_cases m
    · simp [I3] at h2
    · exact absurd h2 (by simp [I3])
  · intro h; exact absurd h (by simp)

/-- `{a}' = {0,1}`（`a` 被对象 `0`、`1` 满足）。 -/
theorem pD_a : K3.polarDown ({0} : Set M2) = ({0,1} : Set G3) := by
  ext g; rw [FormalCtx.mem_polarDown_iff]; fin_cases g <;> simp [I3]

/-- `{0,1}' = {a}`（`b` 只被对象 `0` 满足，`1` 不满足它）。 -/
theorem pU_ab : K3.polarUp ({0,1} : Set G3) = ({0} : Set M2) := by
  ext m; rw [FormalCtx.mem_polarUp_iff]
  constructor
  · intro h
    have h1 := h (g := (1 : G3)) (by simp)
    fin_cases m
    · rfl
    · simp [I3] at h1
  · intro h g hg
    fin_cases g
    · simp [I3]
    · fin_cases m
      · simp [I3]
      · simp at h
    · simp at hg

/-- `{b}' = {0}`（只有对象 `0` 满足 `b`）。 -/
theorem pD_b : K3.polarDown ({1} : Set M2) = ({0} : Set G3) := by
  ext g; rw [FormalCtx.mem_polarDown_iff]; fin_cases g <;> simp [I3]

/-- `{0}' = {a,b}`（对象 `0` 满足全部两个属性）。 -/
theorem pU_a : K3.polarUp ({0} : Set G3) = ({0,1} : Set M2) := by
  ext m; rw [FormalCtx.mem_polarUp_iff]
  constructor
  · intro h; fin_cases m <;> simp
  · intro h g hg
    simp at hg; subst hg
    fin_cases m <;> simp [I3]

/-- `{a,b}' = {0}`（同时满足 `a` 与 `b` 的对象只有 `0`）。 -/
theorem pD_ab : K3.polarDown ({0,1} : Set M2) = ({0} : Set G3) := by
  ext g; rw [FormalCtx.mem_polarDown_iff]; fin_cases g <;> simp [I3]

/-! ### §2.2 α 的四个取值 -/

/-- **`α(∅) = ∅`**：`∅' = G`，`G' = ∅`。 -/
theorem takeConcept_eq_empty : K3.takeConcept (∅ : Set M2) = ∅ := by
  show K3.polarUp (K3.polarDown ∅) = ∅
  rw [pD_empty, pU_univ]

/-- **`α({a}) = {a}`**——`{a}` 已是闭集（不动点）。 -/
theorem takeConcept_eq_a : K3.takeConcept BA = BA := by
  show K3.polarUp (K3.polarDown {0}) = {0}
  rw [pD_a, pU_ab]

/-- **`α({b}) = {a,b}`**——`{b}` **不**闭，α 把它**扩张**成 `{a,b}`。
这是本实例上 α 唯一的非平凡作用。 -/
theorem takeConcept_eq_b : K3.takeConcept ({1} : Set M2) = BAB := by
  show K3.polarUp (K3.polarDown {1}) = {0,1}
  rw [pD_b, pU_a]

/-- **`α({a,b}) = {a,b}`**——`univ` 已闭。 -/
theorem takeConcept_eq_ab : K3.takeConcept BAB = BAB := by
  show K3.polarUp (K3.polarDown {0,1}) = {0,1}
  rw [pD_ab, pU_a]

/-! ### §2.3 「覆盖全部子集」的完备性

`Fin 2` 的属性子集**恰有 4 个**：`∅, {0}, {1}, {0,1}`。
上面 4 条已覆盖全部。下面这条定理把「覆盖完备」写成 Lean 命题——
防止「只算了自己感兴趣的 3 个」这类遗漏。 -/

/-- **4 个属性子集穷尽**：任一 `B ⊆ M2` 必等于上述四者之一。 -/
theorem all_attr_subsets (B : Set M2) :
    B = ∅ ∨ B = {0} ∨ B = {1} ∨ B = ({0, 1} : Set M2) := by
  by_cases h0 : (0 : M2) ∈ B <;> by_cases h1 : (1 : M2) ∈ B
  · right; right; right
    ext m; fin_cases m <;> simp_all
  · right; left
    ext m; fin_cases m <;> simp_all
  · right; right; left
    ext m; fin_cases m <;> simp_all
  · left
    ext m; fin_cases m <;> simp_all

/-! ===========================================================================
    §3  α 的 5 条结构性质，在本实例上落地
    =========================================================================== -/

/-- **I3：α 的输出全是闭集**（本实例 4 个属性子集）。

由 `FormalCtx.takeConcept_isClosed` 直接给出，此处**逐一代入**以表明
「值域落在概念侧」在本实例上**不是空话**。 -/
theorem alpha_empty_closed : K3.IsClosedAttr (K3.takeConcept ∅) :=
  K3.takeConcept_isClosed ∅

theorem alpha_a_closed : K3.IsClosedAttr (K3.takeConcept BA) :=
  K3.takeConcept_isClosed BA

theorem alpha_b_closed : K3.IsClosedAttr (K3.takeConcept {1}) :=
  K3.takeConcept_isClosed {1}

theorem alpha_ab_closed : K3.IsClosedAttr (K3.takeConcept BAB) :=
  K3.takeConcept_isClosed BAB

/-- **I4：α 幂等**（本实例，取**非闭**输入 `{b}` 这一非平凡情形）。

`α(α{b}) = α({a,b}) = {a,b} = α({b})`。 -/
theorem alpha_idem_instance :
    K3.takeConcept (K3.takeConcept {1}) = K3.takeConcept {1} :=
  K3.takeConcept_idem {1}

/-- **I5a：α 扩张**（本实例，`{b} ⊆ α({b})`）。 -/
theorem subset_alpha_instance : ({1} : Set M2) ⊆ K3.takeConcept {1} :=
  K3.subset_takeConcept {1}

/-- **I5a'：扩张在本实例上确实严格**：`α({b})` **新增了属性 a**。

这条定理把「α 不是恒等映射」写成可判定的陈述——
排除「α = id 则该实例无信息」的读法。 -/
theorem alpha_strictly_expands :
    (0 : M2) ∈ K3.takeConcept {1} ∧ (0 : M2) ∉ ({1} : Set M2) := by
  constructor
  · rw [takeConcept_eq_b]; simp [BAB]
  · simp

/-- **I5b：α 单调**（本实例：`{b} ⊆ {a,b} ⟹ α{b} ⊆ α{a,b}`）。 -/
theorem alpha_mono_instance :
    K3.takeConcept ({1} : Set M2) ⊆ K3.takeConcept BAB :=
  K3.takeConcept_mono (by
    intro m hm
    rw [show m = 1 from by simpa using hm]
    simp [BAB])

/-- **I6：闭集穷尽**——本实例的闭集恰为 `∅`、`{a}`、`{a,b}`（3 个）。

即 4 个属性子集中，除 `{b}` 外的**全部**都是闭集。 -/
theorem closed_sets_are (B : Set M2) (h : K3.IsClosedAttr B) :
    B = ∅ ∨ B = BA ∨ B = BAB := by
  rcases all_attr_subsets B with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · -- `{1}` 不闭：其闭包是 `{0,1} ≠ {1}`
    exfalso
    have hc : K3.takeConcept ({1} : Set M2) = ({1} : Set M2) := h
    rw [takeConcept_eq_b] at hc
    have h0 : (0 : M2) ∈ ({1} : Set M2) := by rw [← hc]; simp [BAB]
    simp at h0
  · exact Or.inr (Or.inr rfl)

/-- **α 在本实例上不是单射**——它把 `{b}` 与 `{a,b}` **合并**到同一闭集。

这正是「取概念」的**信息压缩**语义：α 的纤维非平凡。 -/
theorem alpha_not_injective : ¬ Function.Injective K3.takeConcept := by
  intro hinj
  have heq : K3.takeConcept ({1} : Set M2) = K3.takeConcept BAB := by
    rw [takeConcept_eq_b, takeConcept_eq_ab]
  have h1 : ({1} : Set M2) = BAB := hinj heq
  have h0 : (0 : M2) ∈ ({1} : Set M2) := by rw [h1]; simp [BAB]
  simp at h0

/-- **α 在 `{a,b}` 上的纤维恰为 `{{b}, {a,b}}`**（压缩内容的精确刻画）。 -/
theorem fiber_ab (B : Set M2) (h : K3.takeConcept B = BAB) :
    B = {1} ∨ B = BAB := by
  rcases all_attr_subsets B with rfl | rfl | rfl | rfl
  · -- `α(∅) = ∅ ≠ {a,b}`
    rw [takeConcept_eq_empty] at h
    have h0 : (0 : M2) ∈ BAB := by simp [BAB]
    rw [← h] at h0
    exact absurd h0 (by simp)
  · -- `α({a}) = {a} ≠ {a,b}`
    rw [takeConcept_eq_a] at h
    have h1 : (1 : M2) ∈ (BAB : Set M2) := by simp [BAB]
    rw [← h] at h1
    exact absurd h1 (by simp [BA])
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ===========================================================================
    §4  编码算子 enc 与自洽性 Coherent（A32 的「存在」一半，实例化）
    =========================================================================== -/

/-- **本实例用到的框架**：五个空间都取 `ℝ`（只为满足 `Frame` 的拓扑/可测要求）。

真正的信息全在 `enc3` 里，它读的是 `M2` 侧，**不读** `ℝ`。 -/
def frame3 : Frame where
  Θ := ⟨ℝ⟩
  X := ⟨ℝ, le_rfl⟩
  U := ⟨ℝ⟩
  Act := ⟨ℝ⟩
  Ν := ⟨ℝ⟩

/-- **离散化**：把实数状态 `x` 映到两个属性上的二值判定
（阈值 `0`：`a = [0 ≤ x]`，`b = [1 ≤ x]`）。 -/
def toAttrs3 (x : ℝ) : Set M2 :=
  {m | (m = 0 ∧ 0 ≤ x) ∨ (m = 1 ∧ 1 ≤ x)}

/-- **编码算子** $(\mathrm{enc})$：`toObjects` 取 `toAttrs` 的**下极**。

**这是刻意的选择**：它使 `Coherent` **按构造成立**（见 `enc_coherent`），
而不是靠碰运气。这也正是 `Fate.Alpha` 的 `Coherent` 定义所说的
「对象侧由属性侧的下极确定」的最自然实现。 -/
def enc3 : Encoder frame3 K3 where
  toObjects := fun x => K3.polarDown (toAttrs3 x)
  toAttrs := toAttrs3

/-- **I7：`enc3` 自洽**（`Coherent` 在本实例上**为真**，非假设）。 -/
theorem enc_coherent : enc3.Coherent := by
  intro x
  rfl

/-- **I7'：自洽性的逐元素判据在本实例上落地**
（`Encoder.coherent_iff_pointwise` 的实例）。

「对每个状态 `x` 与对象 `g`：`g` 属于 `x` 的对象集 ⟺ `g` 满足 `x` 读出的全部属性」。 -/
theorem enc_coherent_pointwise (x : ℝ) (g : G3) :
    g ∈ enc3.toObjects x ↔ ∀ m ∈ enc3.toAttrs x, K3.Irel g m :=
  (enc3.coherent_iff_pointwise).mp enc_coherent x g

/-- **状态 `1/2` 读出的属性集恰为 `{a}`**（`a = [0 ≤ 1/2]` 真，`b = [1 ≤ 1/2]` 假）。 -/
theorem toAttrs3_half : toAttrs3 ((1 : ℝ) / 2) = BA := by
  ext m
  fin_cases m <;>
    simp only [toAttrs3, BA, mem_setOf_eq, mem_singleton_iff, Fin.isValue,
      Fin.reduceFinMk, true_and, Fin.zero_eta] <;>
    norm_num

/-! ===========================================================================
    §5  抽象等价 ∼_E 与 α 在商上的良定义（T1B.2b 的实例）
    =========================================================================== -/

/-- **实例集**（2 个实例，对应「2–3 个实例」的要求）：`0` 与 `1`。 -/
def Inst2 : InstSpace := ⟨Fin 2⟩

/-- **抽象等价 ∼_E**：**全部**实例等价（最粗的商）。

这是 `Fate.Alpha` 明确**参数化**的那一项（判据是待裁决项 Q-3），
本实例取最粗者，理由是：它使 `RespectsEquiv` 的前件**在本实例上可真**。 -/
@[instance_reducible]
def eqv2 : AbstractEquiv Inst2 := ⊤

/-- **实例 ↦ 状态**：两个实例都映到同一状态 `1/2`。

⚠ 取**同一个**状态是为使 `RespectsEquiv` 成立——
本实例的任务是**验证 α 保抽象的蕴含式**，不是构造反例。 -/
noncomputable def embed2 (_e : Inst2.Carrier) : frame3.X.Carrier := (1 : ℝ) / 2

/-- `embed2` 与参数无关（两个实例落在同一状态）。 -/
theorem embed2_const (e₁ e₂ : Inst2.Carrier) : embed2 e₁ = embed2 e₂ := rfl

/-- **I8a：`enc3` 与 `∼_E` 相容**（前件在本实例上**可真**）。 -/
theorem enc3_respects : enc3.RespectsEquiv embed2 eqv2 := by
  intro e₁ e₂ _
  rw [embed2_const e₁ e₂]

/-- **I8b（T1B.2b 的实例）：α 保持抽象等价**。 -/
theorem alpha_respects_equiv_instance :
    ∀ e₁ e₂ : Inst2.Carrier, eqv2.r e₁ e₂ →
      K3.takeConcept (enc3.toAttrs (embed2 e₁)) =
        K3.takeConcept (enc3.toAttrs (embed2 e₂)) :=
  K3.alpha_respects_equiv enc3 embed2 eqv2 enc3_respects

/-- **I8c：α 在商上良定义，且可以算出值**。

把 `α ∘ enc` 下降到商 `Inst2/∼_E`。本实例取状态 `x = 1/2`，
`enc` 读出属性 `{a}`（因为 `1/2 < 1` 不满足 `b`），故其值恰是 `α({a}) = {a}`。 -/
theorem alphaOnQuotient_instance :
    ∀ q : Quotient eqv2,
      K3.alphaOnQuotient enc3 embed2 eqv2 enc3_respects q = BA := by
  intro q
  refine Quotient.inductionOn q ?_
  intro e
  show K3.takeConcept (enc3.toAttrs (embed2 e)) = BA
  rw [show enc3.toAttrs (embed2 e) = BA from toAttrs3_half]
  exact takeConcept_eq_a

/-! ===========================================================================
    §6  E8（离散化误差）在本实例上的**诚实处置**
    =========================================================================== -/

/-- **I9：`E8Holds` 在本实例的胞腔上可满足**（取空胞腔，`g ≡ 0`）。

⚠ **本定理很弱**：依 `Fate.Alpha` §4 的登记，`g` 的具体表达式**不填**
（填数即为虚构）。本定理只排除「谓词写空了」这一形式错误。 -/
theorem e8_instance_satisfiable :
    ∃ (form : E8BoundForm) (g : E8BoundForm → ℝ),
      E8Holds frame3 form g (fun _ _ => 0) (∅ : Set frame3.X.Carrier) :=
  e8_predicate_satisfiable frame3 (fun _ _ => 0)

/-! ===========================================================================
    §7  汇总：本实例上一眼能看清的 α 画像
    =========================================================================== -/

/-- **α 在本实例上的完整画像**（4 个输入全部列出）。

```
α(∅)    = ∅
α({a})  = {a}
α({b})  = {a,b}     ← 唯一的非平凡作用
α({a,b})= {a,b}
```

这是一条**可判定的等式链**，且每条都由上面的定理**独立证过**。
本定理只是把它们**并列**，便于读者一次看到实例的全貌。 -/
theorem alpha_full_picture :
    K3.takeConcept (∅ : Set M2) = ∅ ∧
    K3.takeConcept BA = BA ∧
    K3.takeConcept ({1} : Set M2) = BAB ∧
    K3.takeConcept BAB = BAB :=
  ⟨takeConcept_eq_empty, takeConcept_eq_a, takeConcept_eq_b, takeConcept_eq_ab⟩

end AlphaInstance
end FateV2.Rules