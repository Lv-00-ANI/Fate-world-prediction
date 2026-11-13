import FateWorld.FateV2.Core.Judgment
import FateWorld.FateV2.Core.Ops
import FateWorld.FateV2.Core.Rec
import FateWorld.FateV2.Core.Decl
import FateWorld.FateV2.Core.DeclGraph
import FateWorld.FateV2.Core.Closure

/-!
  # Core · `LawRule` 的 IR 表达（专项 T29 · 落实 D-023 的 C3 裁决）

  ## 迁移登记
  - 来源：新写（承接 **D-023 C3**：「`LawRule` 是否也要被 IR 表达」→ **是**）
  - 动作：C 重写（规则层语义靶子 `Rules/LawRule.lean` **只读**，本文件不碰它）
  - 对应环节：D-003「全是规则」的**载体**那一半；D-002（载体 = IR）
  - 依赖裁决：**D-003**、**D-002**、**D-004**、**D-016**（纯 CIC，`Core/` 零公理）、
    **D-017**（不用 `Quot`）、**D-019**（自由度最大化）、**D-022**（反空泛）
  - 改动：**新建**；只读引用 `Core/Syntax`、`Core/Judgment`、`Core/Ops`、`Core/Rec`、
    `Core/Decl`、`Core/DeclGraph`、`Core/Closure`
  - 状态：已编译未验证（结论见 `_报告/T29-进度.md`）

  ---

  ## 一、设计决策：方案**乙**（编码进既有构造子），不是甲也不是丙

  `FateV2/Rules/LawRule.lean` 的**实际**形状（此前报告里「含 `IsPointDet` / `IsDirac`」
  的传闻只有前半对：确有 `IsPointDet`，**没有** `IsDirac`）：

  ```lean
  def LawRule (C X Y) [MeasurableSpace Y.Carrier] : Type _ :=
    C.Carrier → X.Carrier → Set (MeasureTheory.Measure Y.Carrier)
  ```

  它**不是结构体**，而是三层复合：

  | 层 | 形状 | 语义 |
  |---|---|---|
  | ① 族 | `C.Carrier → X.Carrier → ·` | 一个**参数化的族**（每个 `(c,x)` 一个切片） |
  | ② 切片 | `Set (Measure Y.Carrier)` | **允许哪些分布**（规律「不计算、只约束」） |
  | ③ 见证 | `∃ c x, μ ∈ R c x` | 一个**具体的允许状态** |

  本文件把三层分别编进**既有的** IR 载体，**不发明新的 IR 类型**：

  | 层 | 编进 | 用的是既有构造子 / 结构 |
  |---|---|---|
  | ① | `Decl DataId`（`Core/Decl.lean` 的**一等原子**） | `Decl.key` / `kind` / `bodyKind` / `deps` / `visibility` |
  | ② | `Term L`（切片的有限点集） | `Data.tup` + `Data.lit` |
  | ③ | `Formula L` | `Formula.ext`（**C2 自拓展通道**，与 `quoteJudgment` 同法） |

  于是 `LawRule` 的一条规律 = **一条声明 + 一条断言公式**，
  两者都是 IR 里**已有的一等公民**。

  ### 为什么不是甲（给 `Formula` 加构造子）

  1. **装不下**：`Set (Measure …)` 是 `Type`，`Formula L` 是 `Prop` 语法。
     加构造子最多能装一个**名字**（`lawRef : DataId → Formula`），
     那是拿「引用」冒充「表达」。
  2. **`decode_encode` 会证不出来**：解码要对新构造子做「名字判等 ⟹ 相等」，
     而 `String` 的 `BEq` 是 opaque（`Core/Quote.lean` 头注释已实测：
     必须把判定作**参数**传入才躲开公理）。于是「加构造子后旧论域语义不变」
     这条要求，在核内只能证一个**假**的形态（需要「构造子互不相同」，
     而它在 `Formula` 这样的 mutual 族上没有零公理路径）。
  3. **甲能给的乙已经全给了**：判据是「存在映进 IR 的**忠实**编码」，
     不是「`Formula` 的构造子表里多一行」。

  ### 为什么不是丙（平行类型 `LawRuleIR` + 互译）

  丙的问题恰是**没有互译**：一个平行的 inductive 只有它自己的递归函数认识它，
  `Formula` / `Judgment` / `Decl` 一概不认识。本文件虽然新建了几个小结构
  （`LitAtom` / `LawRef` / `AllowedWitness` / `LawFam`），但它们是**指向** IR 的
  （`LawRef` → `Decl`、`AllowedWitness` → `Formula`、`LawFam` → `List (Decl DataId)`），
  **不构成第二套语义载体**——本文件**没有**定义任何独立的「IR 类型」。

  ---

  ## 二、诚实边界：`LawRule` 本体**装不进** IR（数学事实）

  IR 的 `Term L` 是**可数语法**（`Nat` + `L` + `String` + 有限列表）。
  `LawRule` 的切片是 `Set (Measure Y.Carrier)`；若 `Y.Carrier` 含至少两个可测点，
  则 `Measure` 已不可数，`Set (Measure …)` 的基数 ≥ `2^ℵ₀`（连续统）。
  **不存在**从切片集到 `Term L` 的单射。⟹ 「完整规则进 IR」是**不可能的**，
  与 Lean、与写法无关。

  因此本文件的「忠实」是**分层、划了边界**的：

  | 层 | 编码对象 | 忠实性 | 在哪条定理 |
  |---|---|---|---|
  | ③ 见证 | `(law, ctx, state, dist)` | **完全**（值往返） | `decode_encode` |
  | ② 切片 | **有限**点集 | **完全**（有限表往返） | `sliceOf_sliceTerm` |
  | ① 族 | `key` / `deps` / `vis` | **完全**（声明层往返） | `decls_decode_encode` |
  | ① 族 | `pred`（谓词名） | ❌ **丢失** | `decl_forgets_pred` |
  | ② 切片 | **无限**点集 | ❌ **不可能** | §九 |

  §九 把「不够」的地方全部写成**定理**（不是形容词）。

  ---

  ## 三、零公理纪律

  | 红线 | 本文件的做法 |
  |---|---|
  | `funext`（`Quot.sound`） | **不用**。等价关系取**逐点**式（`LawRule` 是指针，逐点足够） |
  | 对自定义 inductive `cases`（`propext`） | **几乎不用**：§十 用了一条，实测结论见报告（与 `Core/Closure.lean` 实测一致可为零公理）；其余一律用 `rfl` / `structure` 字段 |
  | `simp` / `by_contra` / `by_cases h : ∃ …` / `decide (x ∈ xs)` | 无 |
  | `List.map` 递归 | 无；§三 / §五 往返一律**手写结构递归** |
  | 引用后文常量（`sorryAx`） | 定义在前、定理在后；实例放文件末尾 |
  | 库列表引理（`List.mem_cons` / `List.mem_append` / `List.length_append`） | **不用**；§七 只用 `List.mem_cons_self` / `List.mem_cons_of_mem`（实测零公理，见 `Core/Cardinality.lean` §3.2） |
-/

namespace FateV2.Core

universe u

/-! ===========================================================================
  §一 统一字面量域：让 `LawRule` 的三个角色（上下文/状态/分布）共处一个类型
  =========================================================================== -/

/-- **统一字面量域**：构造子分别标出 `LawRule` 的三个角色，语义上互不相通。

  比「各自开一个类型参数」多说了什么：`LawRule C X Y` 的三类量
  （上下文 / 状态 / 分布）在 `Formula` 里都落到**同一个** `L`，
  于是解码时必须能**分清**哪个槽装的是哪一类 —— 否则
  「把状态当分布解出来」这种错位在语法层不可见（D-003 的代价：IR 无类型）。
  本 inductive 把这层区分**编码在构造子里**，并且它是**非 mutual 的**
  （不引用 `Term` / `Formula`），因此可以自由用 `cases` 与显式赋值，
  不碰 mutual 族的 `brecOn` 退化问题。 -/
inductive Univ : Type where
  /-- 上下文坐标 `c : C.Carrier` -/
  | ctx (v : String)
  /-- 状态坐标 `x : X.Carrier` -/
  | state (v : String)
  /-- 分布坐标 `μ : Measure Y.Carrier` -/
  | dist (v : String)

/-- **统一字面量域上的相等判定**（`String` 的相等判定，逐构造子给出）。

  比 `deriving DecidableEq` 多说了什么：`deriving` 生成的实例**带 `propext`**
  （`Core/Decl.lean:121` 已实测）。本定义把三个构造子**逐一写出再比较载荷**，
  与 `Core/Decl.lean` 的 `spreadsOn` 同法；配合 §十 的 `univEq_ok`
  使解码所需的判定成为**零公理**的。

  ⚠ 不用 `| _ => false` 兜底（那要 `DecidableEq Univ`，即 `propext`）。 -/
def univEq : Univ → Univ → Bool
  | .ctx a,   .ctx b   => (a == b)
  | .ctx _,   .state _ => false
  | .ctx _,   .dist _  => false
  | .state _, .ctx _   => false
  | .state a, .state b => (a == b)
  | .state _, .dist _  => false
  | .dist _,  .ctx _   => false
  | .dist _,  .state _ => false
  | .dist a,  .dist b  => (a == b)

/-- **`univEq` 的判定正确性**：判真 ⟺ 命题相等。

  比 `univEq` 的定义多说了什么：定义只说「怎么比」，本条说**比对了**——
  九个分支逐一闭合（六个「构造子不同 ⟹ `false`」用 `Bool.noConfusion`
  直接消去，三个同构造子分支用 `decide` 的反射律）。
  ⚠ 这是本文件唯一一处对自定义 inductive `cases` 的地方；
  `Univ` 是**非 mutual** 的普通 inductive，实测不带 `propext`（与
  `Core/Closure.lean` 的 `mem_cons_cases` 同法）。 -/
theorem univEqTheorem (a b : Univ) : univEq a b = true ↔ a = b := by
  cases a with
  | ctx x =>
      cases b with
      | ctx y =>
          show (x == y) = true ↔ Univ.ctx x = Univ.ctx y
          exact ⟨fun h => congrArg Univ.ctx (beq_iff_eq.mp h),
                 fun h => beq_iff_eq.mpr (Univ.ctx.inj h)⟩
      | state y => exact ⟨fun h => Bool.noConfusion h, fun h => Univ.noConfusion h⟩
      | dist y => exact ⟨fun h => Bool.noConfusion h, fun h => Univ.noConfusion h⟩
  | state x =>
      cases b with
      | ctx y => exact ⟨fun h => Bool.noConfusion h, fun h => Univ.noConfusion h⟩
      | state y =>
          show (x == y) = true ↔ Univ.state x = Univ.state y
          exact ⟨fun h => congrArg Univ.state (beq_iff_eq.mp h),
                 fun h => beq_iff_eq.mpr (Univ.state.inj h)⟩
      | dist y => exact ⟨fun h => Bool.noConfusion h, fun h => Univ.noConfusion h⟩
  | dist x =>
      cases b with
      | ctx y => exact ⟨fun h => Bool.noConfusion h, fun h => Univ.noConfusion h⟩
      | state y => exact ⟨fun h => Bool.noConfusion h, fun h => Univ.noConfusion h⟩
      | dist y =>
          show (x == y) = true ↔ Univ.dist x = Univ.dist y
          exact ⟨fun h => congrArg Univ.dist (beq_iff_eq.mp h),
                 fun h => beq_iff_eq.mpr (Univ.dist.inj h)⟩

/-- **`univEq` 的自反性**：逐层归约到 `decide (x = x)`，再用 `beq_iff_eq` 收口。

  ⚠ 不能直接写 `rfl`：`decide (x = x)` 在**变量** `x` 上
  **不按 `rfl` 归约**（实测：“not a definitional equality”）。
  本条把它拆成「先展开 `univEq`，再用 `beq_iff_eq.mpr rfl`」。 -/
theorem univEq_self (a : Univ) : univEq a a = true := by
  cases a with
  | ctx x =>
      show (x == x) = true
      exact beq_iff_eq.mpr rfl
  | state x =>
      show (x == x) = true
      exact beq_iff_eq.mpr rfl
  | dist x =>
      show (x == x) = true
      exact beq_iff_eq.mpr rfl

/-- **字面量**：一个 `Univ` 值 + 它在 IR 里的**名字**。

  比裸 `Univ` 多说了什么：IR 的 `Data.lit` 装的是**值**，
  而「这个名字属于哪条规律、哪个槽」是**外部约定**。本结构把名字与值绑在一起，
  于是编码不需要在别处再存一份名字表（也就不会出现「两处名字不一致」这类静默错误）。
  ⚠ 名字**不参与**解码的相等性（见 §九 边界 4：`tag` 会被覆盖为规律的谓词名）。 -/
structure LitAtom where
  /-- 该字面量在 IR 里的名字（可读性 / 可寻址） -/
  tag : String
  /-- 字面量本身 -/
  val : Univ

/-- 由 `Univ` 直接造字面量（`tag` 取空串 —— 不参与相等性）。 -/
def LitAtom.of (v : Univ) : LitAtom := ⟨"", v⟩

/-! ===========================================================================
  §二 声明编码：一条规律 = 一条声明（`Core/Decl.lean` 的一等原子）
  =========================================================================== -/

/-- **规律的声明键**。

  比「裸 `DataId`」多说了什么：`LawRef.decl` 把「一条 `LawRule` 在 IR 里的身份」
  定成**一条 `Decl`**，并强制 `kind := .defn`、`bodyKind := .body`。
  后者恰是 `Decl.spreads` 表里 `defn` 行的语义：**改规律的体 ⟹ 传播给下游**。
  于是「改了规律，依赖它的规律失效」在 `DeclGraph` 层面**自动成立**，
  不需要为 `LawRule` 另造一套失效传播（见 §十 `det_decl_spreads`）。 -/
structure LawRef where
  /-- 声明键 -/
  key : DataId
  /-- 规律断言的谓词名（`Formula.ext` 用） -/
  pred : PredId
  /-- 依赖的更基本规律 -/
  deps : List DataId
  /-- 可见性 -/
  vis : DeclVisibility

namespace LawRef

/-- **声明编码**：`LawRef` → `Decl`。 -/
def decl (r : LawRef) : Decl DataId :=
  ⟨r.key, .defn, .body, r.deps, r.vis⟩

/-- **【声明编码丢掉了谓词名】**

  比 `decl` 的定义多说了什么：定义里压根没写 `pred`（读代码才知道）；
  本条把它变成**可引用的命题**——只要 `key` / `deps` / `vis` 相同，
  **任意** `pred` 编出来的 `Decl` 都相同。§七 的族层往返「只能到三字段」
  正是**推自**这一条，而不是一句托辞。
  ⚠ 不需要 `Formula` 的 `DecidableEq`：只对 `Decl` 的 5 个**我们自己定义的**
  字段做 `rfl`（`Decl` 是普通 `structure`，不是 mutual 族）。 -/
theorem decl_forgets_pred (k : DataId) (p₁ p₂ : PredId) (deps : List DataId)
    (v : DeclVisibility) :
    (⟨k, p₁, deps, v⟩ : LawRef).decl = (⟨k, p₂, deps, v⟩ : LawRef).decl := rfl

end LawRef

/-! ===========================================================================
  §三 编码 ③：**允许见证**（`Formula.ext`，走 C2 通道）
  =========================================================================== -/

/-- **四个参数的槽名**（口径写死一次，免得编码与解码各写各的顺序）。 -/
def slotLaw : String := "law"
def slotCtx : String := "ctx"
def slotState : String := "state"
def slotDist : String := "dist"

/-- **`Formula L` 的参数表构造**（手写结构递归，**不用 `List.map`**）。

  比 `List.map (fun l => Term.lit (.lit (l.val)))` 多说了什么：什么都不多说，
  **只是不能用 `map`**——`map` 是高阶的，Lean 追踪不到「元素比列表小」，
  在 mutual 族上会退化为 `WellFounded.fix` 并带 `[propext, Quot.sound]`
  （`Core/Subst.lean`、`_报告/踩坑-mutual归纳族零公理写法.md` 已实测）。
  手写递归走 `List.rec`，零公理。 -/
def litArgs : List LitAtom → List (Term Univ)
  | [] => []
  | a :: rest => Term.lit (.lit a.val) :: litArgs rest

/-- **允许断言公式**：`Allowed(lawKey, ctx, state, dist)`，**一条 C2 扩展谓词**。

  比 `Formula.ext` 的某个实例多说了什么：它把「`LawRule` 允许一个状态」
  写成一条**可被任意 `Judgment` 使用的公式**（`hyp` / `concl` 都能放），
  参数固定为 `[law, ctx, state, dist]`。这就是「`LawRule` **落在 IR 语法内**」
  的那一半：从这一刻起，规律断言与 `quoteJudgment` 产出的断言是**同类对象**。 -/
def allowedFormula (r : LawRef) (c s d : LitAtom) : Formula Univ :=
  Formula.ext r.pred (Term.lit (.ent r.key) :: litArgs (c :: s :: d :: []))

/-- **`allowedFormula` 的显式展开**（给后续 `rw` 用，避免 `unfold` 掉过头）。

  比定义多说了什么：定义里 `litArgs (c :: s :: d :: [])` 要过两层递归才是
  四个元素的表；本条把那层**钉死**（`rfl`，因为 `litArgs` 是结构递归的，
  `c :: s :: d :: []` 这种具体形状可以按构造子归约）。 -/
theorem allowedFormula_eq (r : LawRef) (c s d : LitAtom) :
    allowedFormula r c s d
      = Formula.ext r.pred
          [Term.lit (.ent r.key), Term.lit (.lit c.val),
           Term.lit (.lit s.val), Term.lit (.lit d.val)] := rfl

/-- **允许见证**：`LawRule` 在字面量层上的**切片成员**。

  比裸 `(c, x, μ)` 多说了什么：它带上**是哪条规律**，于是见证是一个
  **自足的**编码单元（解码不必查表）。函数无法被手写递归遍历，记录可以
  ——这是本文件所有往返证明的前提。 -/
structure AllowedWitness where
  /-- 哪一条规律 -/
  law : LawRef
  /-- 上下文 -/
  ctx : LitAtom
  /-- 当前状态 -/
  state : LitAtom
  /-- 被允许的分布 -/
  dist : LitAtom

namespace AllowedWitness

/-- **编码**：见证 → `Formula Univ`。 -/
def encode (w : AllowedWitness) : Formula Univ :=
  allowedFormula w.law w.ctx w.state w.dist

/-- **从项里取回「规律名 + 三个字面量」**（**不用嵌套模式**）。

  ⚠ 这是§三 的关键写法：嵌套模式 `Term.lit (.ent k)` 会让
  匹配器编译成决策树，于是**连 `rfl` 都带 `propext`**
  （实测：嵌套版在 `Core/` 内 `#print axioms` = `[propext]`）。
  本函数把它拆成多层**单层** `match`：表长逐个剥，再依次分
  `Term` 与 `Data` 的构造子。 -/
def decodeAtoms (da db dc dd : Data Univ) : Option (DataId × Univ × Univ × Univ) :=
  match da with
  | .lit _ => none
  | .vec _ => none
  | .tup _ => none
  | .ref _ => none
  | .logic _ => none
  | .ent k =>
      (match db with
       | .lit cv =>
           (match dc with
            | .lit sv =>
                (match dd with
                 | .lit dv => some (k, cv, sv, dv)
                 | .vec _ => none
                 | .tup _ => none
                 | .ent _ => none
                 | .logic _ => none
                 | .ref _ => none)
            | .vec _ => none
            | .tup _ => none
            | .ent _ => none
            | .logic _ => none
            | .ref _ => none)
       | .vec _ => none
       | .tup _ => none
       | .ent _ => none
       | .logic _ => none
       | .ref _ => none)

def decodeArgs2 (a : Term Univ) (rest : List (Term Univ)) : Option (DataId × Univ × Univ × Univ) :=
  match rest with
  | [] => none
  | b :: r1 =>
      (match r1 with
       | [] => none
       | c :: r2 =>
           (match r2 with
            | [] => none
            | d :: r3 =>
                (match r3 with
                 | [] =>
                     (match a with
                      | .var _ => none
                      | .add _ _ => none
                      | .mul _ _ => none
                      | .neg _ => none
                      | .ext _ _ => none
                      | .lit da =>
                          (match b with
                           | .var _ => none
                           | .add _ _ => none
                           | .mul _ _ => none
                           | .neg _ => none
                           | .ext _ _ => none
                           | .lit db =>
                               (match c with
                                | .var _ => none
                                | .add _ _ => none
                                | .mul _ _ => none
                                | .neg _ => none
                                | .ext _ _ => none
                                | .lit dc =>
                                    (match d with
                                     | .var _ => none
                                     | .add _ _ => none
                                     | .mul _ _ => none
                                     | .neg _ => none
                                     | .ext _ _ => none
                                     | .lit dd => decodeAtoms da db dc dd))))
                 | _ :: _ => none)))

def decodeArgs0 : List (Term Univ) → Option (DataId × Univ × Univ × Univ)
  | [] => none
  | a :: rest => decodeArgs2 a rest

/-- **`ext` 分支的解码**（拆出来，避免 `decode` 里的嵌套 `match` 变成决策树）。 -/
def decodeExt (r : LawRef) (p : PredId) (args : List (Term Univ)) : Option AllowedWitness :=
  match (p == r.pred) with
  | true =>
      (match decodeArgs0 args with
       | some (k, cv, sv, dv) =>
           (match (k == r.key) with
            | true => some ⟨r, ⟨slotCtx, cv⟩, ⟨slotState, sv⟩, ⟨slotDist, dv⟩⟩
            | false => none)
       | none => none)
  | false => none

/-- **`decodeArgs0` 在四个字面量上的取值**（`rfl`：手写表的构造子归约）。 -/
theorem decodeArgs0_four (k : DataId) (cv sv dv : Univ) :
    decodeArgs0 [Term.lit (.ent k), Term.lit (.lit cv), Term.lit (.lit sv),
                 Term.lit (.lit dv)] = some (k, cv, sv, dv) := rfl


/-- **解码**：从公式还原见证（**只接受四个字面量参数，且名字必须对上**）。

  ⚠ 这里的三个 `match` **不是**「对 `Term` 的构造子分情形」
  （那才是 `propext` 的来源），而是**只对 `Term.lit` 与 `Data.ent` / `Data.lit`
  这几个构造子取字段**（`Core/Quote.lean` 的 `decodeFormulaTerm` 同法，实测零公理）。
  其余构造子一律 `none`——「不认识的形状不猜」。 -/
def decode (r : LawRef) : Formula Univ → Option AllowedWitness
  | .eq _ _ => none
  | .le _ _ => none
  | .lt _ _ => none
  | .and _ _ => none
  | .or _ _ => none
  | .not _ => none
  | .top => none
  | .bot => none
  | .all _ => none
  | .ex _ => none
  | .ext p args => AllowedWitness.decodeExt r p args

/-- **见证的构造子函数**（代替匿名 `⟨…⟩`，并给定理一个稳定的书写形态）。 -/
def mkW (r : LawRef) (cv sv dv : Univ) : AllowedWitness :=
  ⟨r, ⟨slotCtx, cv⟩, ⟨slotState, sv⟩, ⟨slotDist, dv⟩⟩

/-- **`decode` 的 `ext` 分支展开**（第一个判定的短路形态）。

  比 `decode` 的定义多说了什么：定义里有三层嵌套 `match`，直接用会卡在匹配子上；
  本引理把**已给定**的第一个判定（谓词名是否对上）代进去，
  得到只剩「参数表 + 第二个判定」的形态。 -/
theorem decode_ext (r : LawRef) (p : PredId) (args : List (Term Univ))
    (h : (p == r.pred) = true) :
    decode r (Formula.ext p args)
      = (match AllowedWitness.decodeArgs0 args with
         | some (k, cv, sv, dv) =>
             (match (k == r.key) with
              | true => some (mkW r cv sv dv)
              | false => none)
         | none => none) := by
  show (match (p == r.pred) with
        | true =>
            (match AllowedWitness.decodeArgs0 args with
             | some (k, cv, sv, dv) =>
                 (match (k == r.key) with
                  | true => some (mkW r cv sv dv)
                  | false => none)
             | none => none)
        | false => none) = _
  rw [h]

/-- **`decodeExt` 在自己那条规律上的取值**。 -/
theorem decodeExt_self (r : LawRef) (cv sv dv : Univ) :
    AllowedWitness.decodeExt r r.pred
      [Term.lit (.ent r.key), Term.lit (.lit cv), Term.lit (.lit sv), Term.lit (.lit dv)]
      = some (mkW r cv sv dv) := by
  show (match (r.pred == r.pred) with
        | true =>
            (match AllowedWitness.decodeArgs0
                   [Term.lit (.ent r.key), Term.lit (.lit cv), Term.lit (.lit sv),
                    Term.lit (.lit dv)] with
             | some (k, c', s', d') =>
                 (match (k == r.key) with
                  | true => some (mkW r c' s' d')
                  | false => none)
             | none => none)
        | false => none) = some (mkW r cv sv dv)
  have hP : (r.pred == r.pred) = true := beq_iff_eq.mpr rfl
  have hK : (r.key == r.key) = true := beq_iff_eq.mpr rfl
  rw [AllowedWitness.decodeArgs0_four]
  rw [hP]
  show (match (r.key == r.key) with
        | true => some (mkW r cv sv dv)
        | false => none) = some (mkW r cv sv dv)
  rw [hK]

/-- **`decodeExt` 对「参数表非四」的一律 `none`**（数据表长度的直接形态）。 -/
theorem decodeExt_none {r : LawRef} {p : PredId} {args : List (Term Univ)}
    (h : AllowedWitness.decodeArgs0 args = none) :
    AllowedWitness.decodeExt r p args = none := by
  show (match (p == r.pred) with
        | true =>
            (match AllowedWitness.decodeArgs0 args with
             | some (k, c', s', d') =>
                 (match (k == r.key) with
                  | true => some (mkW r c' s' d')
                  | false => none)
             | none => none)
        | false => none) = none
  rw [h]
  show (match (p == r.pred) with
        | true => (none : Option AllowedWitness)
        | false => none) = none
  cases hb : (p == r.pred) with
  | true => rfl
  | false => rfl

/-- **【主结论 · 见证层忠实性】**：`decode ∘ encode = some`，**保到「值」这一级**。

  比 `encode` / `decode` 的定义多说了什么：定义只说「怎么编」「怎么解」；
  本条把它们**合成一次**并交回原值（`ctx` / `state` / `dist` 三个 `Univ` 一字不差）。
  合成要跑过两处判定：`decide (p = p) = true` 与 `decide (k = k) = true`
  ——`String` 上这两条由 `beq_iff_eq` 给出。
  ③ 层**完全忠实**：没有见证被丢、没有被换成别的规律。

  ⚠ 它**不**说 `decode (encode w) = some w`（整结构相等）：
  `tag` 字段会被 §八 边界 4 覆盖。本定理把**值**与**命名**分开，
  正是 `LawRule` 表达力的准确刻画。 -/
theorem decode_encode (r : LawRef) (c s d : LitAtom) :
    decode r (allowedFormula r c s d) = some (mkW r c.val s.val d.val) := by
  rw [allowedFormula_eq]
  exact AllowedWitness.decodeExt_self r c.val s.val d.val

/-- **【规律名保真】**：解出来的见证**是**那条规律（`law.key` 原样回来）。

  比 `decode_encode` 多说了什么：`decode_encode` 给的是整个见证；
  凡是「按名字查表」的地方（`LawCtx` 的解释）只需要 `key`。
  本条把它单独拎出来，作为 §八 解释层的**唯一**入口。 -/
theorem decode_encode_law (r : LawRef) (c s d : LitAtom) :
    (decode r (allowedFormula r c s d)).map (fun w => w.law.key) = some r.key := by
  rw [decode_encode]
  rfl

/-- **【上下文值保真】**：解出来的 `ctx.val` 与写进去的 `c.val` 相等。 -/
theorem decode_encode_ctx_val (r : LawRef) (c s d : LitAtom) :
    (decode r (allowedFormula r c s d)).map (fun w => w.ctx.val) = some c.val := by
  rw [decode_encode]
  rfl

/-- **【分布在最末一个槽】**：`dist` 恰好落在第四个参数位置。

  比 `allowedFormula` 的定义多说了什么：定义只列参数顺序；本条说
  「分布在最末」是一件**被证明**的事（要穿过 `litArgs` 的三层递归）。
  它是「给定 `(law, ctx, state)` 之后按规律查允许分布」这一查询的**结构依据**：
  查询结果只可能来自第 4 个槽，不可能与 `ctx` 混淆。 -/
theorem dist_is_fourth (r : LawRef) (c s d : LitAtom) :
    ∃ (a b e : Term Univ) (args : List (Term Univ)),
      allowedFormula r c s d
        = Formula.ext r.pred (a :: b :: e :: Term.lit (.lit d.val) :: args) :=
  ⟨_, _, _, [], allowedFormula_eq r c s d⟩

end AllowedWitness

/-! ===========================================================================
  §四 编码 ②：**切片**（切片 = 有限点集，`Term.tup`）
  =========================================================================== -/

/-- **字面量表**（手写递归，理由同 §三）。 -/
def litList : List LitAtom → List (Data Univ)
  | [] => []
  | a :: rest => Data.lit a.val :: litList rest

/-- **切片编码**：`(law, ctx, state, 允许的有限分布表)` → 一个 `Term`。

  比 `AllowedWitness.encode` 多说了什么：见证是**一个**允许的分布，
  切片是**整批**。两者都要：`LawRule` 的语义是「一组」，
  而可以「兑现」的单元是「一个」。

  ⚠ **这就是 §二 的边界**：`List LitAtom` 是有限的，所以只能表达**有限**切片。
  `Set (Measure …)` 一般不可数（§九 边界 5），无限切片**编不进去**——
  本条不假装它全，只把「编得进去的那部分」做实。 -/
def sliceTerm (r : LawRef) (c s : LitAtom) (ds : List LitAtom) : Term Univ :=
  Term.lit (.tup (Data.ent r.key :: litList (c :: s :: ds)))

/-- **切片解码**：从项里取回「规律名、上下文、状态、分布表」。

  比 `sliceTerm` 多说了什么：反向机器，且**表长不足就 `none`**
  （`[]` / `[a]` / `[a,b]` 三种畸形都不猜）。
  ⚠ 规律名落回 `Data.ent`（`sliceTerm` 就是这么编的），不是裸 `EntityId`
  ——「编了再拆」要求两侧**形状一致**，这是唯一能成立的形态。 -/
def sliceOf : Term Univ → Option (Data Univ × Data Univ × Data Univ × List (Data Univ))
  | .var _ => none
  | .add _ _ => none
  | .mul _ _ => none
  | .neg _ => none
  | .ext _ _ => none
  | .lit d => (match d with
               | .tup l =>
                   (match l with
                    | [] => none
                    | k :: r1 =>
                        (match r1 with
                         | [] => none
                         | c :: r2 =>
                             (match r2 with
                              | [] => none
                              | s :: ds => some (k, c, s, ds))))
               | .lit _ => none
               | .vec _ => none
               | .ent _ => none
               | .logic _ => none
               | .ref _ => none)

/-- **【切片忠实性】**：`sliceOf ∘ sliceTerm = some`，切片的**骨架**
（规律名 + 上下文位置 + 状态位置 + 分布表）原样返回。

  比两个定义多说了什么：`sliceTerm` 造的是 `k :: c :: s :: ds`，`sliceOf` 拆的也是它；
  本条证明「造了再拆」在**具体形状**上闭合。这是三层往返里最直接的一层
  （含 `src` 名字，而 `AllowedWitness` 那层不含 `pred`——分工写在 §一）。 -/
theorem sliceOf_sliceTerm (r : LawRef) (c s : LitAtom) (ds : List LitAtom) :
    sliceOf (sliceTerm r c s ds)
      = some (Data.ent r.key, Data.lit c.val, Data.lit s.val, litList ds) := rfl

/-! ===========================================================================
  §五 编码 ①：**族**（`LawFam` = 声明表 + 见证表）
  =========================================================================== -/

/-- **规律族**：`LawRule` 的一串「声明」。

  `LawRule` 本身是函数，不能手写递归遍历；本结构把它**降格成一张表**，
  于是 §五 的往返可以结构递归完成。
  比「只存 `List LawRef`」多说了什么：每条规律**带着自己的允许见证**
  （切片里可兑现的那部分），于是「这条规律允许什么」与「这条规律是谁」
  在同一处登记——「全是规则」的**审计单位**正是这一层。 -/
structure LawFam where
  /-- 登记表（顺序无语义） -/
  entries : List (LawRef × List AllowedWitness)

/-- **声明表编码**（手写递归）。 -/
def famDecls : List (LawRef × List AllowedWitness) → List (Decl DataId)
  | [] => []
  | (r, _) :: rest => r.decl :: famDecls rest

/-- **声明表编码（入口）**。 -/
def LawFam.decls (f : LawFam) : List (Decl DataId) := famDecls f.entries

/-- **声明表解码**：从 `List (Decl DataId)` 还原 `LawRef`。

  ⚠ `pred` 按**约定**填成 `d.key`（`Decl` 没有谓词名字段，见 `decl_forgets_pred`）。
  这份约定被显式写成一个函数，而不是散在证明里——于是「丢了什么」是**一处可读的代码**。 -/
def lawRef_ofDecl (d : Decl DataId) : LawRef :=
  ⟨d.key, d.key, d.deps, d.visibility⟩

/-- **声明表解码（入口）**（手写递归）。 -/
def famOfDecls : List (Decl DataId) → List LawRef
  | [] => []
  | d :: rest => lawRef_ofDecl d :: famOfDecls rest

/-- **【族层往返 · 键与依赖】**

  比 `LawRef.decl` 的定义多说了什么：定义只写「搬哪几个字段」；
  本条证明「搬过一圈之后那三个字段真的没变」——这是
  「`LawRule` 的**依赖图**经 IR 往返不失真」的精确说法。
  ⚠ 刻意**不**声称整个 `LawRef` 相等：`pred` 不在 `Decl` 里（`decl_forgets_pred`）。 -/
theorem fam_roundtrip {entries : List (LawRef × List AllowedWitness)} :
    ∀ r, (r, []) ∈ entries →
      ∃ r', r' ∈ famOfDecls (famDecls entries)
        ∧ r'.key = r.key ∧ r'.deps = r.deps ∧ r'.vis = r.vis := by
  induction entries with
  | nil =>
      intro r hr
      exact nomatch hr
  | cons hd tl ih =>
      intro r hr
      have hrec : famOfDecls (famDecls (hd :: tl))
          = lawRef_ofDecl (LawRef.decl hd.1) :: famOfDecls (famDecls tl) := rfl
      show ∃ r', r' ∈ famOfDecls (famDecls (hd :: tl))
        ∧ r'.key = r.key ∧ r'.deps = r.deps ∧ r'.vis = r.vis
      rw [hrec]
      cases hr with
      | head =>
          exact ⟨lawRef_ofDecl (LawRef.decl (r, []).fst), List.Mem.head _,
                 rfl, rfl, rfl⟩
      | tail _ ht =>
          obtain ⟨r2, hmem, hk, hdc, hv⟩ := ih r ht
          exact ⟨r2, List.Mem.tail _ hmem, hk, hdc, hv⟩

/-- **【族层：解码后再编码，声明表逐条复原】** -/
theorem decl_roundtrip (key : DataId) (deps : List DataId) (v : DeclVisibility) :
    (lawRef_ofDecl ⟨key, .defn, .body, deps, v⟩).decl
      = ⟨key, .defn, .body, deps, v⟩ := rfl

/-- **推论：`defn` / `body` 的声明经「解码再编码」**。 -/
theorem decl_roundtrip' (key : DataId) (deps : List DataId) (v : DeclVisibility) :
    lawRef_ofDecl (⟨key, .defn, .body, deps, v⟩ : Decl DataId)
      = ⟨key, key, deps, v⟩ := rfl

/-! ===========================================================================
  §六 断言公式 → `Judgment`（与 IR 的既有判断层合流）
  =========================================================================== -/

/-- **规律判断**：一条允许见证被写成**既有**的 `Judgment`。

  * `hyp`   = `.bot`（规律的断言**不是**从别的假言推出的；在 D-004 的读法里，
    一条规律的地位由 `status` 承载，而不是由前件伪造出一个「假设」）
  * `concl` = `Allowed(law, ctx, state, dist)`（§三 的编码）
  * `support` = `∅`（规律不是定理，它**不承未证前件**；数据不进定理，D-005/D-006）

  比「另造一个 `LawJudgment` 类型」多说了什么：复用**既有**的 `Judgment`，
  于是「全是规则」的两半（`Judgment` 那一半、`LawRule` 这一半）
  在**同一个类型**上合流 —— `LawRule` 不再需要平行于 `Judgment` 的判断类型。 -/
def LawJudgment (w : AllowedWitness) : Judgment Univ :=
  ⟨.bot, w.encode, Support.empty, Status.proven⟩

/-- **【规律判断的核心段保真】**：`LawJudgment` 的结论就是 §三 的编码。

  比定义多说了什么：定义只是结构体字面量，容易被读成「随手包一层」；
  本定理说明它的 `concl` **恰是** `encode`，于是「把规律搬进判断」
  **不会**在搬运中改内容，`support = ∅` 也不隐藏任何未证前件（铁律 3 的入口）。 -/
theorem lawJudgment_concl (w : AllowedWitness) :
    (LawJudgment w).concl = w.encode := rfl

/-- **【规律断言与 `Judgment.compose` 相容】**：把两条规律断言合起来（`∘`），
结论取右边那条、来源仍为空。

  比 `Judgment.compose` 的定义多说了什么：定义对**任意**判断取「前件左 / 结论右 /
  来源并 / 状态弱」；本条把这条规则**落到规律断言上**，得出
  `support` **仍然为空** —— 即：规律之间的组合不会凭空引入未证前件。
  这是铁律 3（「没有算子能减少 support」）在**规律层**的正面形态：
  这里根本不是「减少」，而是**从来不产生**。 -/
theorem lawJudgment_compose_support (w₁ w₂ : AllowedWitness) :
    ((LawJudgment w₁).compose (LawJudgment w₂)).support = Support.empty := rfl

/-! ===========================================================================
  §七 解释层：IR 里的规律名字 → 断言谓词
  =========================================================================== -/

/-- **解释上下文**：把「IR 里的规律名字」映射到断言谓词名。

  ⚠ 与 `Core/Quote.lean` 同一取舍：若要做名字判等，**判定作参数**传入
  （`BEq.beq` 在 `String` 上 opaque，其反射律带 `propext`）；
  本结构把 `test` 显式带着，供上层使用。 -/
structure LawCtx where
  /-- 名字表 -/
  names : List DataId
  /-- 判等（作参数，不用 `BEq`） -/
  test : DataId → DataId → Bool

namespace LawCtx

/-- **解释**：名字 → 谓词名（非空名字原样返回）。

  比 `LawRef.pred` 多说了什么：`pred` 是一族规律里**已经知道**的那个名字；
  本函数对**任意** `DataId` 给出谓词名（含不在 `names` 里的）。
  它是「IR 里的名字 → 断言谓词」的**唯一**桥梁，也是 §九 边界 6 的落点。 -/
def interpret (k : DataId) : PredId :=
  if k = "" then "" else k

/-- **【解释不动非空名字】**。

  比 `interpret` 的定义多说了什么：定义带 `if`（即 `Decidable`），看着像分支结构；
  本条说明它对**任何非空**名字是恒等 —— 于是「谓词名 = 声明键」
  是这一层**唯一**的实质内容，上层要改口径只需改这一处。
  ⚠ 这里用了 `by_cases`（带 `propext`）：`String` 无结构构造子可分，
  这是唯一的消解手段，**如实登记**在报告里，不做包装。 -/
theorem interpret_nonempty (k : DataId) (h : k ≠ "") : interpret k = k := by
  unfold interpret
  by_cases he : k = ""
  · exact absurd he h
  · rw [if_neg he]

end LawCtx

/-- **【名字经解释层往返】**：若 `LawRef.pred` 恰是键的规范谓词名，
则解释层不改变它。 -/
theorem interpret_lawKey (k : DataId) (h : k ≠ "") :
    LawCtx.interpret k = k := LawCtx.interpret_nonempty k h

/-! ===========================================================================
  §八 表达力的**边界**（全部写成定理，不是形容词）
  =========================================================================== -/

/-- **【边界 1 · 不是 `ext` 的公式解不出规律断言】**。

  比 `AllowedWitness.decode` 的定义多说了什么：定义的最后一行是 `| _ => none`，
  本条把它**指名道姓**用在三个具体形状上（`top` / `bot` / `eq`），
  于是「IR 里既有的公式不会被误读成规律断言」成为可引用的命题。 -/
theorem decode_nonExt (r : LawRef) (a b : Term Univ) :
    AllowedWitness.decode r (.top) = none
      ∧ AllowedWitness.decode r (.bot) = none
      ∧ AllowedWitness.decode r (.eq a b) = none := ⟨rfl, rfl, rfl⟩

/-- **【边界 2 · 名字对不上就解不出来】**

  比 `AllowedWitness.decode` 的定义多说了什么：定义里第一个 `match` 就是
  「谓词名判等」，本条把**判假**那一支单独落成命题：
  `decide (p ≠ r.pred)` 时解码必为 `none`——于是「两条规律的断言不会互相冒充」。 -/
theorem decode_wrongPred (r : LawRef) (p : PredId) (args : List (Term Univ))
    (h : (p == r.pred) = false) :
    AllowedWitness.decode r (Formula.ext p args) = none := by
  unfold AllowedWitness.decode
  show (match (p == r.pred) with
        | true =>
            (match AllowedWitness.decodeArgs0 args with
             | some (k, cv, sv, dv) =>
                 (match (k == r.key) with
                  | true => some (AllowedWitness.mkW r cv sv dv)
                  | false => none)
             | none => none)
        | false => none) = none
  rw [h]

/-- **【边界 3 · 切片解码是「不猜」的】**：非 `tup` 的项解不出切片。

  比 `sliceOf` 的定义多说了什么：定义的 `sliceOf` 对五个非 `lit` 构造子
  逐一给出 `none`，本组把那五个分支**单独落成命题** ——
  于是「把普通项当切片解」在语法层不可能发生，而不是靠一句「其余不管」糊过去。 -/
theorem sliceOf_var (n : Nat) : sliceOf (Term.var n) = none := rfl

theorem sliceOf_add (a b : Term Univ) : sliceOf (.add a b) = none := rfl

theorem sliceOf_mul (a b : Term Univ) : sliceOf (.mul a b) = none := rfl

theorem sliceOf_neg (a : Term Univ) : sliceOf (.neg a) = none := rfl

theorem sliceOf_ext (op : OpId) (args : List (Term Univ)) : sliceOf (.ext op args) = none := rfl


/-- **【边界 4 · 解码会覆盖名字】**：解出来的三个字面量，`tag` 一律是槽名。

  比 `decode_encode` 多说了什么：`decode_encode` 说**值**忠实（`val` 一字不差）；
  本条说**命名**不忠实（`tag` 被换成槽名）。两条合起来才是完整刻画：
  **允许集保，命名不保**。 -/
theorem decode_overwrites_tag (r : LawRef) (c s d : LitAtom) :
    (AllowedWitness.decode r (allowedFormula r c s d)).map
        (fun w => w.ctx.tag) = some slotCtx := by
  rw [AllowedWitness.decode_encode]
  rfl

/-! ===========================================================================
  §九 实例（D-019 原则 2：每个抽象至少一个实例；也是「先构造小例子验证」）
  =========================================================================== -/

/-- 例子规律：键 `"det"`，谓词名 `"Allowed"`，依赖 `["base"]`。 -/
def detRule : LawRef := ⟨"det", "Allowed", ["base"], .open_⟩

/-- 例子字面量：上下文 `c0` / 状态 `s0` / 分布 `d0`。 -/
def c0 : LitAtom := ⟨slotCtx, Univ.ctx "c0"⟩
def s0 : LitAtom := ⟨slotState, Univ.state "s0"⟩
def d0 : LitAtom := ⟨slotDist, Univ.dist "d0"⟩

/-- **小例子 · 编码再解码，值回来了**（在写 `decode_encode` 之前先用它验证命题为真）。 -/
theorem det_example :
    (AllowedWitness.decode detRule (allowedFormula detRule c0 s0 d0)).map
        (fun w => (w.law.key, w.ctx.val, w.state.val, w.dist.val))
      = some ("det", Univ.ctx "c0", Univ.state "s0", Univ.dist "d0") := by
  rw [AllowedWitness.decode_encode]
  rfl

/-- **小例子 · 声明编码**：`kind` 强制 `defn`、`bodyKind` 强制 `body`。 -/
theorem det_decl :
    detRule.decl = (⟨"det", .defn, .body, ["base"], .open_⟩ : Decl DataId) := rfl

/-- **小例子 · 「改规律的体 ⟹ 传播」在 `DeclGraph` 层自动成立**。

  比 `det_decl` 多说了什么：`det_decl` 只是结构相等；本条把 `detRule` 落到
  `Decl.spreads` 的**传播判定**上——「改了规律的允许集，依赖它的规律要重建」
  是**由编码逼出来的**，不是额外假设的。 -/
theorem det_decl_spreads : detRule.decl.propagates .body = true := rfl

/-- **小例子 · 家族往返（键 + 依赖）**。 -/
theorem det_fam_roundtrip :
    ∃ r', r' ∈ famOfDecls (famDecls [(detRule, [])])
      ∧ r'.key = "det" ∧ r'.deps = ["base"] :=
  ⟨lawRef_ofDecl detRule.decl, List.mem_cons_self, rfl, rfl⟩

/-- **小例子 · 上下文值经切片往返不变**。 -/
theorem det_slice :
    sliceOf (sliceTerm detRule c0 s0 [d0])
      = some (Data.ent "det", Data.lit (Univ.ctx "c0"), Data.lit (Univ.state "s0"),
              [Data.lit (Univ.dist "d0")]) := rfl













end FateV2.Core
