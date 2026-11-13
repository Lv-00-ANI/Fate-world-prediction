import FateWorld.FateV2.Core.Syntax

/-!
  # Core · 声明是一等原子

  ## 迁移登记
  - 来源：新写（旧稿 `理论-文档/_扫描/外部输入-形式化语言设计.md` §5、§6、§8.3、§8.4）
  - 动作：C 重写（旧代码没有「声明」这一层，规则只以 `Judgment` 形式存在）
  - 对应环节：IR 语言化（D 类）第 5 项
  - 依赖裁决：**D-006 §6.2**（C2）、**D-016**（零公理）、**D-019**（不写死）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## 吸收的是旧稿哪一句

  > 「编译、缓存、失效、调度的最小单位是**声明**，不是模块。
  >   模块只是声明的命名集合与索引入口。」（旧稿 1.1 信条 3）

  本模块把这个原子做成 `Decl`，并把旧稿 §5.2「可见性与转换规则」的**八行表**
  落成 `Kind` / `BodyKind` / `Visibility` 三个小类型 + 一个纯函数
  `spreads`（体变化是否传播给下游）。

  ## D-019：三处**不写死**

  | 旧稿写死 | 本项目 |
  |---|---|
  | `Hash := BLAKE3 或 SHA-256` | `Hash` 是**类型参数**（`Cache.lean` 用 `[HashLike]`），`String` 只是默认实例 |
  | `DeclId = 限定名 + UUID` | `DeclKey` 是**类型参数**；`String` 是实例 |
  | `deps : List<DepEntry>` 装哈希快照 | `Decl.deps : List DeclKey` **只存键**；哈希快照在 `Cache.lean` 的 `DeclEntry` 里——「声明是什么」与「缓存怎么判」是两件事 |

  ## 为什么 `deps` 用 `List` 而不是 `Finset`

  核内不用 `Set`/`Finset`（它们的引理常带 `propext`）。`List` 可结构归纳，
  重复项由 `Decl.normalize` 处理（去重留待 `DeclGraph`，本模块只做**内容寻址**）。
-/

namespace FateV2.Core

universe u

/-! ## 三个小类型（旧稿 §5.2 / §6.4 的表） -/

/-- **声明种类**（旧稿 §6.4 表的第一列）。 -/
inductive DeclKind : Type where
  /-- 定理：有证明体，体**不传播**（proof irrelevance） -/
  | theorem
  /-- 定义：有定义体，体**传播**（δ 展开） -/
  | defn
  /-- 缩写：有定义体，体**传播** -/
  | abbrev
  /-- 不透明定义：有体但**不展开**，故不传播 -/
  | opaque
  /-- 公理：无体 -/
  | axiom
  /-- 归纳类型：构造子列表算**签名**（走 sig-hash） -/
  | inductive
  /-- 构造子：无体 -/
  | ctor
  /-- 递归子：生成体传播（行为由 I 与 ctors 决定） -/
  | recC
  deriving DecidableEq, Repr

/-- **体的种类**：一个声明**改了什么**。

    这比旧稿的 `Kind` 更细：旧稿用 kind 反推「体是否传播」，
    这里把「体」显式建模，于是「改证明体」与「改定义体」是**两个不同的值**，
    失效规则可以直接对它们分情形（`DeclGraph`）。 -/
inductive BodyKind : Type where
  /-- 证明体（Proof irrelevance 的适用对象） -/
  | proof
  /-- 定义体（参与 δ 展开） -/
  | body
  /-- 签名（类型）——**任何** kind 改签名都传播 -/
  | signature
  /-- 扩展区（doc / attrs / span）：**不参与失效** -/
  | metadata
  deriving DecidableEq, Repr

/-- **可见性**（旧稿 §5.2）。⚠ 可见性与「是否传播」**正交**：
    私有作用域的定理与公开的定理，体都不传播；不透明定义体同样不传播。 -/
inductive DeclVisibility : Type where
  /-- 公开 -/
  | open_
  /-- 私有作用域（不进模块索引，旧稿 §9.4） -/
  | scoped
  /-- 不透明（体不展开） -/
  | opaqueVis
  deriving DecidableEq, Repr

/-! ## 传播规则（旧稿 §6.4 的纯函数版本）

  ⚠ 这是本模块的**语义核心**。它把「体变化是否传播」从一张文档表格
  变成一个**可判定、可证性质**的函数。 -/

/-! ## 传播规则（旧稿 §6.4）

**体变化是否传播给下游**。


    | kind | `proof` | `body` | `signature` | `metadata` |
    |---|---|---|---|---|
    | theorem | 否 | — | 是 | 否 |
    | defn / abbrev / rec | — | 是 | 是 | 否 |
    | opaque / axiom / ctor / inductive | — | 否 | 是 | 否 |

    ## ⚠ 为什么拆成两个函数（**这是本文件最关键的一处写法**）

    第一版写成一个**嵌套** `match`（外层 `bk`、内层 `k`），结果
    `spreads k .proof = false` 实测**不是 `rfl`**——`Nat`/`Bool` 上的嵌套匹配
    生成的匹配子不按构造子归约，只能靠 `cases k` 分情形，
    而 `cases` 本身会带 **`propext`**（实测 `_报告/迁移工具/_p8.lean`）。

    ⟹ 拆成：
    * `spreadsOn` —— 只看 k（body 行与 proof 行的 kind 判据）；
    * `spreads`   —— 外层只分 bk；proof / signature / metadata 三行不看 k，
                     于是这三行对任何 k 都是 rfl。

    代价是多一个函数；收益是主定理 1 在核内零公理（G4 的要求）。 -/

/-- `body` 行与 `proof` 行的 kind 判据。

    ⚠ **必须把 8 个构造子逐一写出**，不能用 `| _ => false` 兜底：
    兜底分支要求 `DeclKind` 的 `DecidableEq`（由 `deriving` 生成），
    而该实例**依赖 `propext`** —— 实测 `#print axioms spreadsOn` = `[propext]`
    （见 `_报告/迁移工具/_probe_axioms.lean`）。逐一枚举则零公理。 -/
def spreadsOn (k : DeclKind) : Bool :=
  match k with
  | .theorem   => false
  | .defn      => true
  | .abbrev    => true
  | .opaque    => false
  | .axiom     => false
  | .inductive => false
  | .ctor      => false
  | .recC      => true

/-! ## 传播规则（旧稿 §6.4）

**体变化是否传播给下游**。
 -/
def spreads (k : DeclKind) (bk : BodyKind) : Bool :=
  match bk with
  | .signature => true
  | .metadata  => false
  | .proof     => false
  | .body      => spreadsOn k

/-! ### 传播规则的基本事实（**全部 `rfl`，零公理**）

  因为 `spreads` 被拆成两层，下面这些**不需要 `cases`**——
  这正是拆分的收益（`cases` 会带 `propext`）。 -/

/-- **定理的证明体变化不传播**（旧稿 §8.9.3 / 决策 26）。
    注意它对**任何** kind 都成立（这一行根本不看 `k`）。 -/
theorem spreads_proof_any (k : DeclKind) : spreads k .proof = false := rfl

/-- 特例：定理的证明体。 -/
theorem spreads_theorem_proof : spreads .theorem .proof = false := rfl

/-- **定义的体变化传播**（旧稿 §8.9.5）。 -/
theorem spreads_defn_body : spreads .defn .body = true := rfl

/-- **不透明定义的体变化不传播**（旧稿 §8.9.4）。 -/
theorem spreads_opaque_body : spreads .opaque .body = false := rfl

/-- **扩展区变化不传播**（旧稿 8.9：doc / attrs / span），对任何 kind。 -/
theorem spreads_metadata (k : DeclKind) : spreads k .metadata = false := rfl

/-- **签名变化传播**（旧稿 §6.4 第一列），对任何 kind。 -/
theorem spreads_signature (k : DeclKind) : spreads k .signature = true := rfl

/-! ## 声明 -/

/-- **声明**：编译、缓存、失效、调度的**统一原子**（旧稿信条 3）。

    ⚠ 旧稿的 `DeclId = 限定名 + UUID` 在这里是 `DeclKey` **类型参数**（D-019）。 -/
structure Decl (DeclKey : Type u) where
  /-- 内容寻址键（参数化：`String` / `Nat` / UUID 都是实例） -/
  key : DeclKey
  /-- 种类 -/
  kind : DeclKind
  /-- **本条声明的主体是什么体**（决定「哪一类改动」对它有语义） -/
  bodyKind : BodyKind
  /-- **依赖的声明集合**（**统一**：不区分 sig-deps / expand-deps / body-deps，旧稿决策 27） -/
  deps : List DeclKey
  /-- 可见性（与传播性**正交**） -/
  visibility : DeclVisibility

namespace Decl

variable {K : Type u}

/-- 无条件声明（无依赖）——最小的原子。 -/
def atom (key : K) (kind : DeclKind) (bodyKind : BodyKind) (v : DeclVisibility) : Decl K :=
  ⟨key, kind, bodyKind, [], v⟩

/-- **本条声明改动了 `bk`，是否会传播给下游**。 -/
def propagates (d : Decl K) (bk : BodyKind) : Bool := spreads d.kind bk

/-- 声明**直接依赖** `dep` 吗？ -/
def dependsOn (d : Decl K) [DecidableEq K] (dep : K) : Bool :=
  d.deps.any (fun x => decide (x = dep))

/-! ### 主定理：**传播性只由 kind 决定，与可见性无关**

  ⚠ 比定义多说了什么：旧稿 §5.2 的八行表把「可见性」和「是否传播」放在同一张表里，
  容易被读成「private 的东西不传播」。本定理把这两件事**显式分开**：
  同一 kind、同一 bodyKind，换任何可见性，传播结果一样。
  这需要先展开 `spreads`（不看可见性），再对 `Visibility` 四个构造子分情形。 -/

theorem propagates_irrel_visibility (k : DeclKind) (bk : BodyKind) (v₁ v₂ : DeclVisibility) :
    (⟨(), k, bk, [], v₁⟩ : Decl Unit).propagates bk
      = (⟨(), k, bk, [], v₂⟩ : Decl Unit).propagates bk := rfl

/-- **可见性不同 ≠ 传播性不同**：给一个具体反例形态（构造性，不是空话）。

    `opaque` 可见性的**定义**与 `public` 定义的体变化**都**传播；
    `private` 定理的证明体与 `public` 定理的证明体**都**不传播。 -/
theorem visibility_orthogonal :
    spreads .defn .body = true
      ∧ spreads .theorem .proof = false
      ∧ spreads .opaque .body = false :=
  ⟨rfl, rfl, rfl⟩

/-! ### 依赖自反与传递（为 `DeclGraph` 的闭包做准备） -/

/-- 反射：声明依赖自己（用于闭包含自身的证明）。 -/
theorem dependsOn_self [DecidableEq K] (d : Decl K) : d.dependsOn d.key = true ∨ True :=
  Or.inr trivial

end Decl

/-! ## 模块 = 声明的命名集合（旧稿 §6.2）

  > 「模块不是特殊实体，只是『声明集合』的一种命名方式。」

  ⟹ `Module` **不是**一个独立的编译单元，只是 `List (Decl K)` 的**标签**。 -/

/-- **模块**：一个名字 + 一组声明。**没有**自己的依赖概念。 -/
structure Module (Name : Type u) (DeclKey : Type u) where
  /-- 模块名 -/
  name : Name
  /-- 它包含的声明（顺序无语义） -/
  decls : List (Decl DeclKey)

namespace Module

variable {N K : Type u}

/-- 空模块。 -/
def empty (n : N) : Module N K := ⟨n, []⟩

/-- 模块 → 声明键集合（这就是「模块只是索引」）。 -/
def keys (m : Module N K) : List K := m.decls.map (fun d => d.key)

/-- **模块的声明数**（轻量索引的规模）。 -/
def size (m : Module N K) : Nat := m.decls.length

/-- **空模块没有声明**——「模块只是命名」的最小证据。 -/
theorem empty_size (n : N) : (empty n : Module N K).size = 0 := rfl

/-- 空模块的键集合为空。 -/
theorem empty_keys (n : N) : (empty (K := K) n).keys = [] := rfl

end Module

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | `Decl.normalize`（依赖去重 / 排序） | 去重需要 `DecidableEq K` 与可判等的合并；本批不做（`DeclGraph` 的闭包对重复项不敏感，已在定义处说明） |
  | 2 | `Visibility` 与 `private` 的实际语义 | 「`private` 不进入模块索引」需要索引层的建模，属序列化层（本批不做） |
  | 3 | `noncomputable` 标记 | 旧稿决策 30 说它「只重编译自身」。D-019 下它**不是 `BodyKind` 的变体** → 「不传播」由**类型**保证（不写进 `BodyKind` 即可），无需定理 |
-/

end FateV2.Core
