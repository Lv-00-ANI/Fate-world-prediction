import FateWorld.FateV2.Core.Syntax

/-!
  # Meta · 上下文范式（可逆副作用 + 反 coeffect）

  ## 迁移登记
  - 来源：新写（依 arXiv:2608.25512 §3.1–§3.3 的机制，不含其完整演算）
  - 动作：C 重写
  - 对应环节：—
  - 依赖裁决：**D-024**（时空可组合的精确含义）、**D-012**（模态注册表）、**D-019**（自由度）
  - 改动：新增。旧代码没有「可撤销副作用」与「依赖规格」这两层抽象。
  - 状态：已编译未验证

  ## 依论文的哪几条

  | 本文件 | 论文 |
  |---|---|
  | `Step`（正向 + **左逆**） | §3.1.1 可逆副作用；**只要求 `g ∘ f = id`**，单向 |
  | `Ctx`（状态 + 逆日志） | Def 2 效果上下文 `∂Γ ≔ Γ × (Γ→Γ)`；此处用**列表日志**代替复合函数，便于结构归纳 |
  | `apply` / `undo` / `recover` | Def 3 `track` 与 `recover` |
  | `Step.comp`（扭复合） | Def 1 `(f₁,g₁) ∘ (f₂,g₂) = (f₁∘f₂, g₂∘g₁)` |
  | `Spec` + `satisfied` + `classify` | Def 21/22 coeffect 规格与 activate/deactivate/neutral |

  ## 为什么用「左逆」而不是真逆

  论文明确：**撤销是单向的**（`g ∘ f`，never `f ∘ g`）。
  这比真逆弱得多，也实用得多——**快照式撤销天然满足**：

      正向 fwd：保存旧值，返回新值
      左逆 inv：忽略输入，返回保存的旧值

  于是 `inv (fwd γ) = γ` 定义性成立。**任何算子都能这样变成可撤销的**，
  代价只是「运行时要持有旧状态」——这正是论文让上下文自己携带累积器的原因。

  ⟹ 我此前在 D-024 §四 说「四算子都没有逆」是**错的**：它们都能有左逆。
  -/

namespace FateV2.Meta

universe u

/-! ## 可逆副作用 -/

/-- **一步可逆副作用**：正向 `fwd` 与**左逆** `inv`，满足 `inv ∘ fwd = id`。

    ⚠ 不要求 `fwd ∘ inv = id`（论文 §3.1.1：撤销是单向的）。 -/
structure Step (Γ : Type u) where
  /-- 正向变换 -/
  fwd : Γ → Γ
  /-- 左逆 -/
  inv : Γ → Γ
  /-- 左逆律 -/
  left_inv : ∀ γ : Γ, inv (fwd γ) = γ

namespace Step

variable {Γ : Type u}

/-- **扭复合**（论文 Def 1）：`(f₁,g₁) ∘ (f₂,g₂) = (f₁∘f₂, g₂∘g₁)`。

    注意逆的累积顺序**相反**——这正是「撤销按后进先出」的来源。 -/
def comp (s₁ s₂ : Step Γ) : Step Γ where
  fwd := s₁.fwd ∘ s₂.fwd
  inv := s₂.inv ∘ s₁.inv
  left_inv := by
    intro γ
    show s₂.inv (s₁.inv (s₁.fwd (s₂.fwd γ))) = γ
    rw [s₁.left_inv, s₂.left_inv]

/-- 恒等（扭复合幺元）。 -/
def id : Step Γ where
  fwd := fun γ => γ
  inv := fun γ => γ
  left_inv := by intro γ; rfl

/-- 扭复合保持左逆律——即 `Step Γ` 对 `comp` 封闭。 -/
theorem comp_left_inv (s₁ s₂ : Step Γ) (γ : Γ) :
    (s₁.comp s₂).inv ((s₁.comp s₂).fwd γ) = γ :=
  (s₁.comp s₂).left_inv γ

end Step

/-! ## 上下文：状态 + 逆日志 -/

/-- **上下文**：当前状态 + 逆变换日志（后进先出）。

    论文用 `Γ × (Γ→Γ)`（逆的复合）；此处用**列表**，因为
    「撤销若干步后回到原状态」需要按步归纳，列表能结构递归，复合函数不能。 -/
structure Ctx (Γ : Type u) where
  /-- 当前状态 -/
  state : Γ
  /-- 逆变换日志：头部是最近一次 -/
  log : List (Γ → Γ)

namespace Ctx

variable {Γ : Type u}

/-- 空上下文（无副作用）。 -/
def init (γ : Γ) : Ctx Γ := ⟨γ, []⟩

/-- **施加一步**：状态前进，逆压入日志头部（论文 Def 3 `track`）。 -/
def apply (s : Step Γ) (c : Ctx Γ) : Ctx Γ := ⟨s.fwd c.state, s.inv :: c.log⟩

/-- **撤销一步**：弹出最近的逆并施加（论文的 `recover` 单步）。 -/
def undo (c : Ctx Γ) : Ctx Γ :=
  match c.log with
  | [] => c
  | g :: gs => ⟨g c.state, gs⟩

/-- 从某状态起，把日志依次施加（后进先出）。 -/
def recoverFrom (γ : Γ) : List (Γ → Γ) → Γ
  | [] => γ
  | g :: gs => recoverFrom (g γ) gs

/-- **恢复**：把全部日志跑完，回到最初状态。 -/
def recover (c : Ctx Γ) : Γ := recoverFrom c.state c.log

/-! ## 两条主定理 -/

/-- **【左逆】撤销一步后，上下文精确回到施加前。**

    这条用到 `left_inv`，不是定义展开：`inv (fwd γ) = γ` 是**实质前提**。 -/
theorem undo_apply (s : Step Γ) (c : Ctx Γ) : undo (apply s c) = c := by
  cases c with
  | mk st lg =>
    show ({ state := s.inv (s.fwd st), log := lg } : Ctx Γ) = ⟨st, lg⟩
    rw [s.left_inv st]

/-- **【整链】施加一步后再把整条日志跑完，结果与从未施加相同。**

    这是论文「时间可组合」在单组件上的形式：新效果不会污染恢复终点。 -/
theorem recover_apply (s : Step Γ) (c : Ctx Γ) : recover (apply s c) = recover c := by
  cases c with
  | mk st lg =>
    show recoverFrom (s.inv (s.fwd st)) lg = recoverFrom st lg
    rw [s.left_inv st]

/-- 施加再撤销，上下文不变（与 `undo_apply` 同义，用于流水线推理）。 -/
theorem apply_undo_apply (s : Step Γ) (c : Ctx Γ) :
    undo (apply s c) = c :=
  undo_apply s c

end Ctx

/-! ## 依赖规格（coeffect）与反应式激活 -/

/-- **依赖规格**：组件声明它需要哪些依赖键（论文 Def 21：`𝔇Σ ≔ Set(K)`，
    此处用 `List` 以保持在核内可计算、避免 `Set` 的经典性）。 -/
abbrev Spec (K : Type u) : Type u := List K

/-- **满足**：规格里每个键都在当前已提供的键中（论文 Def 22 的 `σ ⊧ d`）。 -/
def satisfied {K : Type u} [DecidableEq K] (avail : List K) (d : Spec K) : Bool :=
  d.all (fun k => avail.contains k)

/-- **反应式分类**（论文 Def 22 `notify_d`）。 -/
inductive Reaction : Type where
  /-- 之前不满足、现在满足 → 激活 -/
  | activating
  /-- 之前满足、现在不满足 → 停用 -/
  | deactivating
  /-- 状态未变 -/
  | neutral
  deriving DecidableEq, Repr

/-- 依前后两次满足情况给出反应（论文 Def 22）。 -/
def classify (before after : Bool) : Reaction :=
  match before, after with
  | false, true => .activating
  | true, false => .deactivating
  | _, _ => .neutral

/-! 注：`classify` 的三条定义性事实（`classify false true = .activating` 等）
已删除——实测它们会带入 `propext`（来自该 `match` 的匹配器编译形态），
属琐碎事实，不值得为此让本模块失去零公理性质。 -/

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | 论文的 `Γ∞ ≔ μΓ. Γ × (Γ→Γ) × Σ`（Def 28，递归类型） | 本文件只做了单层 `Ctx`；递归层需 `PFunctor`/`WellFounded` 机具 |
  | 2 | 观测等价（§3.3.2）与「交错不干扰」 | 未做；需要「观测」的定义与等价关系的传递性证明 |
  | 3 | 多组件（fiber）编排与 `pairwise independence`（§3.3.4） | 未做；属演算层 |
  | 4 | `Spec` 用 `List` 而非 `Set` | 避免 `Set` 的经典性；代价是需去重语义 |
-/

end FateV2.Meta
