import FateWorld.FateV2.Core.Syntax
import FateWorld.FateV2.Core.Subst

/-!
  # Core · 绑定结构（λ / let）

  ## 迁移登记
  - 来源：新写（旧稿 §2.1 `λ (x : A), t` 与 `let x : A := t in u`，决策点 1）
  - 动作：C 重写
  - 对应环节：IR 表达力（函数抽象 / 局部定义）
  - 依赖裁决：**D-016**（纯 CIC）、**D-019**（不写死、不改既有 inductive）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## ⚠ 为什么不给 `Term` 加构造子

  `Term`/`Formula`/`Data` 是 **mutual** 归纳族，且 `Judgment`/`Ops`/`Modeling`/`Error`/`Loop`
  大量构造 `Term`——那是**冻结 API**（A 类依赖）。

  ⟹ 本模块另立 `TermExt`：**一个新的、非 mutual 的 inductive**。
  它不碰任何既有类型，且因为不是 mutual 族，可以**自由结构递归**：

  | 在 mutual 族（`Term`）上 | 在 `TermExt` 上 |
  |---|---|
  | `mutual` 归纳子带 `Quot.sound` | 普通 `induction` 干净 |
  | `funext` 带 `Quot.sound` | 同样（但本文件不用 `funext`） |
  | 列表遍历必须手写 | 同样（本文件用 `List.map` 但不依赖其引理） |

  与 `Term` 的连接由 `toTerm`（嵌入）与 `ofTerm`（提升既有项）给出。
-/

namespace FateV2.Core

universe u

/-! ## 三个绑定算子的注册名 -/

/-- `lam` —— 函数抽象（走 `Registry` 的 C2 通道）。 -/
def lamOp : OpId := "lam"

/-- `app` —— 应用。 -/
def appOp : OpId := "app"

/-- `let` —— 局部定义。 -/
def letOp : OpId := "let"

/-- 三个绑定算子的名字表。 -/
def bindOps : List OpId := [lamOp, appOp, letOp]

/-! ## 扩展项 -/

/-- **扩展项**：在既有 `Term L` 之上加绑定结构。

    * `lift`  —— 既有 `Term` 原样提升（既有代码零改动）
    * `lam`   —— `λ. body`，`body` 里的 `bvar 0` 被绑定
    * `app`   —— 应用
    * `let_`  —— `let x := v in body`，`body` 里的 `bvar 0` 是 `x`
    * `bvar`  —— 绑定变量（de Bruijn） -/
inductive TermExt (L : Type u) : Type u where
  | lift (t : Term L)
  | lam  (body : TermExt L)
  | app  (f a : TermExt L)
  | let_ (v body : TermExt L)
  | bvar (n : Nat)

/-! ## 嵌入与提升 -/

/-- 扩展项 → 项。`lam`/`let` 通过注册表里的算子名编码，**不新增 `Term` 构造子**。

    ⚠ 编码口径（写死一次）：`lam` 体是唯一的 `ext` 参数；`let` 的参数顺序固定为 `[v, body]`。 -/
def TermExt.toTerm {L : Type u} : TermExt L → Term L
  | .lift t   => t
  | .lam b    => .ext lamOp [b.toTerm]
  | .app f a  => .ext appOp [f.toTerm, a.toTerm]
  | .let_ v b => .ext letOp [v.toTerm, b.toTerm]
  | .bvar n   => .var n

/-- 既有项 → 扩展项。 -/
def TermExt.ofTerm {L : Type u} (t : Term L) : TermExt L := .lift t

/-- **提升再落回还是原项**（既有代码可无成本进出扩展层）。 -/
theorem toTerm_ofTerm {L : Type u} (t : Term L) : TermExt.toTerm (.ofTerm t) = t := rfl

/-! ## 类正确性 -/

/-- 扩展项的数值性。`lam` 的值是函数，**不是**数值（不该被 `add`/`mul` 吃进去）。 -/
def TermExt.Numeric {L : Type u} : TermExt L → Prop
  | .lift t   => t.Numeric
  | .lam _    => False
  | .app _ _  => True
  | .let_ v b => v.Numeric ∧ b.Numeric
  | .bvar _   => True

/-- 扩展项的类正确性。 -/
def TermExt.WellSorted {L : Type u} : TermExt L → Prop
  | .lift t   => t.WellSorted
  | .lam b    => b.WellSorted
  | .app f a  => f.WellSorted ∧ a.WellSorted
  | .let_ v b => v.WellSorted ∧ b.WellSorted
  | .bvar _   => True

/-- `bvar` 是数值项。 -/
theorem TermExt.numeric_bvar {L : Type u} (n : Nat) : TermExt.Numeric (.bvar (L := L) n) := trivial

/-- `lam` **不是**数值项——函数抽象不能被塞进 `add`。 -/
theorem TermExt.not_numeric_lam {L : Type u} (b : TermExt L) : ¬ TermExt.Numeric (.lam (L := L) b) :=
  fun h => h

/-- `let` 的两侧都数值 ⟹ `let` 数值。 -/
theorem TermExt.numeric_let {L : Type u} {v b : TermExt L}
    (hv : v.Numeric) (hb : b.Numeric) : TermExt.Numeric (.let_ v b) :=
  ⟨hv, hb⟩

/-- 既有项的数值性等价地传给它的提升。 -/
theorem TermExt.numeric_lift {L : Type u} {t : Term L}
    (h : Term.Numeric t) : TermExt.Numeric (.lift t) := h

/-! ## 变量重命名（完整递归，因为 `TermExt` 不是 mutual 族） -/

/-- **提升映射**：穿过一层绑定。`0 ↦ 0`，`m+1 ↦ Δ m + 1`。 -/
def liftRen (Δ : Nat → Nat) : Nat → Nat
  | 0     => 0
  | m + 1 => Δ m + 1

/-- 扩展项的重命名。 -/
def TermExt.rename {L : Type u} (Δ : Nat → Nat) : TermExt L → TermExt L
  | .lift t   => .lift t
  | .lam b    => .lam (TermExt.rename (liftRen Δ) b)
  | .app f a  => .app (TermExt.rename Δ f) (TermExt.rename Δ a)
  | .let_ v b => .let_ (TermExt.rename Δ v) (TermExt.rename (liftRen Δ) b)
  | .bvar n   => .bvar (Δ n)

/-! ## 主定理

  ⚠ `liftRen id` 与 `id` **不是同一个函数项**；`funext` 能拉平它们，
  但实测 `funext` 带 `Quot.sound`（违反 D-016）。

  ⟹ 本文件不用 `funext`，也不依赖 `rw` 的函数项匹配（后者对
  「`liftRen (liftRen id)` vs `liftRen id`」这类形态常常匹配不上）。
  做法：把**提升层数**显式参数化，每一层都是独立的结构归纳。 -/

/-- `liftRen` 的 `k` 次迭代（本工具链下没有 `Nat.iter`）。 -/
def iterRen : Nat → (Nat → Nat)
  | 0     => fun n => n
  | k + 1 => (fun n => match n with
      | 0     => 0
      | m + 1 => iterRen k m + 1)

/-- `iterRen k` 在每点上都是恒等（`Nat` 归纳，`liftRen` 的每分支直接算）。 -/
theorem iterRen_id_at : ∀ (k n : Nat), iterRen k n = n
  | 0, n => by cases n <;> rfl
  | k + 1, n => by
      show (match n with | 0 => 0 | m + 1 => iterRen k m + 1) = n
      cases n with
      | zero => rfl
      | succ m =>
          show iterRen k m + 1 = m + 1
          rw [iterRen_id_at k m]

/-- **【恒等律 · 任意迭代次数】**：`id` 经 `iterRen k` 后不动扩展项。

    比定义多说了什么：`lam`/`let_` 会**再加一层**，于是归纳假设必须对
    `k+1` 也成立——本定理把 `k` 当参数，因而对该分支直接可用。
    `bvar` 分支用 `iterRen_id_at`。 -/
theorem TermExt.rename_id_iter {L : Type u} : ∀ (k : Nat) (e : TermExt L),
    TermExt.rename (iterRen k) e = e
  | k, .lift t   => rfl
  | k, .lam b    => congrArg TermExt.lam (TermExt.rename_id_iter (k + 1) b)
  | k, .app f a  =>
      (congrArg (fun x => TermExt.app x (TermExt.rename (iterRen k) a))
        (TermExt.rename_id_iter k f)).trans
        (congrArg (TermExt.app f) (TermExt.rename_id_iter k a))
  | k, .let_ v b =>
      (congrArg (fun x => TermExt.let_ x (TermExt.rename (iterRen (k + 1)) b))
        (TermExt.rename_id_iter k v)).trans
        (congrArg (TermExt.let_ v) (TermExt.rename_id_iter (k + 1) b))
  | k, .bvar n   => congrArg TermExt.bvar (iterRen_id_at k n)

/-- **【恒等律：重命名 `id` 不动扩展项】**（主定理，`k = 0`）。 -/
theorem TermExt.rename_id {L : Type u} (e : TermExt L) :
    TermExt.rename (fun n => n) e = e :=
  TermExt.rename_id_iter 0 e

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | `TermExt` 上的**替换 / β 归约** | 未做。任意替换要把 `Nat → TermExt` 送进绑定子，与本文件的重命名同构 |
  | 2 | `toTerm` 的单射性 | `lam` 与 `ext "lam" [..]` 混叠，**不单射**；要单射得给 `Term` 加构造子（破坏冻结 API） |
  | 3 | 强归约 / Church–Rosser | `TermExt` 无类型，`β` 不终止（`Ω`）；加类型归 Lean |
  | 4 | α-等价 | 需取商（`Quot` 被 D-017 禁用），属未决 |
-/

end FateV2.Core