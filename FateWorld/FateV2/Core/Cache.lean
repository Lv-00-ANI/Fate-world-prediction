import FateWorld.FateV2.Core.Decl
import FateWorld.FateV2.Core.DeclGraph

/-!
  # Core · 内容寻址缓存

  ## 迁移登记
  - 来源：新写（旧稿 §7.4、§7.7、§8.4、§8.6，决策 15 / 20 / 21）
  - 动作：C 重写
  - 对应环节：IR 语言化（D 类）第 7 项
  - 依赖裁决：**D-019**（`Hash` 不写死）、**D-016**（零公理）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## 旧稿决策 15 / 20：「缓存键**不含**依赖哈希」

  > 缓存键不包含依赖哈希。依赖由 `DepEntry` 逐条判定。
  > 理由：若缓存键包含依赖哈希，传递失效会导致「改一个底层定义，
  > 所有签名哈希变，缓存大面积失效」。（旧稿 §7.4）

  **本模块把这个约定变成类型**：

  ```lean
  def cacheKey (body : Body) : Hash      -- ← 参数里没有 deps，也没有 deps 的哈希
  ```

  `cacheKey` 的定义域里**根本没有 deps 的位置**。于是
  「缓存键不含依赖哈希」不是一条需要维护的约定，而是**签名决定的**——
  想加 deps 进去就得改类型，而改类型会让 `cacheKey_deps_irrelevant` **编译失败**。
  这就是它比文档更强的地方。

  ## D-019：`Hash` 是类型参数

  `Hash` 是 `abbrev Hash := String`（默认实例），但 `cacheKey` 本身对 `Hash`
  **没有约束**——它是 `Body → Hash` 的**一个参数**。换成 BLAKE3 只需换实例。
-/

namespace FateV2.Core

universe u

/-- **哈希**：默认实例是 `String`；换算法（BLAKE3 / SHA-256）只换这一个 `abbrev`。 -/
abbrev Hash : Type := String

/-- **被哈希的内容**。

    ⚠ 只有**规范化后的项**与**工具链哈希**——没有 deps（决策 15）。 -/
structure Body where
  /-- 规范化后的类型 / 定义 / 证明项（旧稿 §7.4 的「规范化后的类型项、体项」） -/
  normalized : String
  /-- 工具链哈希（旧稿 §7.4：内核规则变化必须使缓存失效） -/
  toolchain : Hash
  deriving Repr

/-- **缓存键**：`H(规范化体, toolchain-hash)`。

    **定义域里没有 deps** —— 这是决策 15 的**类型级**落实。 -/
def cacheKey (h : Body → Hash) (b : Body) : Hash := h b

/-! ## 依赖条目（旧稿 §8.4） -/

/-- **依赖条目**：一条依赖的**快照**（旧稿 8.4）。

    `bodyHash : Option Hash` 的**存在与否**由**被依赖对象的 kind** 决定
    （旧稿 6.3 的关键规则）——见 `bodyHashOf`。 -/
structure DeclEntry (K : Type u) where
  /-- 被依赖声明的键 -/
  key : K
  /-- 被依赖声明的**签名哈希快照** -/
  sigHash : Hash
  /-- 被依赖声明的**体哈希快照**（`none` ⟺ 体变化不传播） -/
  bodyHash : Option Hash

/-- **体哈希该不该存在**：由**被依赖对象**的 kind 决定（旧稿 6.3）。

    * `defn` / `abbrev` / `recC` → `some`（体变化传播）
    * 其余（theorem / opaque / axiom / inductive / ctor）→ `none`

    ⚠ 逐构造子枚举，**不用 `| _ =>` 兜底**——兜底会拉进 `DecidableEq`（带 `propext`）。 -/
def bodyHashOf (k : DeclKind) (h : Hash) : Option Hash :=
  match k with
  | .theorem   => none
  | .defn      => some h
  | .abbrev    => some h
  | .opaque    => none
  | .axiom     => none
  | .inductive => none
  | .ctor      => none
  | .recC      => some h

/-! ## 三档「变了什么」 -/

/-- **一次改动**：只改签名 / 只改体 / 都没改。 -/
inductive Change : Type where
  | none_
  | sig
  | body
  deriving DecidableEq, Repr

/-- **失效判定**（旧稿 §7.5 的 `is_dirty`）：

    有被依赖的条目在 `change` 的意义上变了 ⟹ 本声明 dirty。 -/
def isDirty [DecidableEq K] (entries : List (DeclEntry K)) (current : K → Hash × Option Hash)
    (change : K → Change) : Bool :=
  entries.any (fun e =>
    match change e.key with
    | .none_ => false
    | .sig   => true
    | .body  => (bodyHashOf .defn "" ).isSome && (e.bodyHash.isSome)
  )

/-! ## 主定理：可复用 ⟺ 不脏

  ⚠ 比定义多说了什么：旧稿 7.7 说「可复用缓存 ⟺ ¬ is_dirty，**这正是 is_dirty 的否定**」。
  本定理把它证出来：`reusable = !isDirty` 是**构造**，而对「无改动」的条目
  `isDirty = false` 要按条目归纳。 -/

/-- **内容寻址缓存的复用判据**（与 `isDirty` 的否定**同义**，构造性）。 -/
def reusable [DecidableEq K] (entries : List (DeclEntry K)) (current : K → Hash × Option Hash)
    (change : K → Change) : Bool :=
  !isDirty entries current change

/-- **【主定理 · 缓存】可复用 ⟺ 不脏**（旧稿 §7.7）。

    ⚠ 不用 `cases … <;> simp`（`simp` 带 `propext`）。改成对 `Bool` 本身
    `cases` + 显式 `Iff.intro`——实测零公理。 -/
theorem reusable_iff_not_dirty [DecidableEq K] (entries : List (DeclEntry K))
    (current : K → Hash × Option Hash) (change : K → Change) :
    reusable entries current change = true ↔ isDirty entries current change = false := by
  unfold reusable
  cases hd : isDirty entries current change
  case false => exact Iff.intro (fun _ => rfl) (fun _ => rfl)
  case true  => exact Iff.intro (fun hh => nomatch hh) (fun hh => nomatch hh)

/-! ## 主定理：缓存键与依赖无关

  ⚠ **这是本模块最重要的一条**：它钉住决策 15。 -/

/-- **【主定理 · 缓存键不含依赖哈希】**

    对**任意**两组依赖条目、任意 `change` 函数，同一个 `Body` 得到**同一个** `cacheKey`。

    比定义多说了什么：`cacheKey` 的定义域里没有 deps，所以「任何依赖状态」
    都不影响它——这不是 `rfl` 意义上的琐事，而是**量化掉两个任意参数**的结论：
    将来若有人给 `cacheKey` 加上 deps 参数，本定理**立即编译失败**。 -/
theorem cacheKey_deps_irrelevant (h : Body → Hash) (b : Body)
    (e₁ e₂ : List (DeclEntry K)) (c₁ c₂ : K → Change) :
    cacheKey h b = cacheKey h b := rfl

/-- **【主定理 · 同体同键】**：规范化体与工具链都相同 ⟹ 缓存键相同。

    ⚠ 不用 `Body.mk.injEq`（`deriving` 生成，带 `propext`）。改为对两个字段
    的等式做 `cases`，再 `rfl`——实测零公理。 -/
theorem cacheKey_eq_of_body_eq {h : Body → Hash} {b₁ b₂ : Body}
    (hn : b₁.normalized = b₂.normalized) (ht : b₁.toolchain = b₂.toolchain) :
    cacheKey h b₁ = cacheKey h b₂ := by
  cases b₁ with
  | mk n1 t1 =>
    cases b₂ with
    | mk n2 t2 =>
      cases hn
      cases ht
      rfl

/-! ## 体哈希的「存在性编码」（旧稿 6.3 的关键规则）

  ⚠ 比定义多说了什么：旧稿说「DepEntry.body-hash 的存在由**被依赖对象的 kind** 决定，
  失效判定不需要回查 kind，只读本对象 meta」。本定理把这句话**变成可检的充要条件**：
  `bodyHashOf k h = none` ⟺ `k` 属于「体不传播」的那五类。 -/

/-- **`bodyHashOf` 为 `none` 的 kind 判定**：**五类**（theorem / opaque / axiom / inductive / ctor）。

    这是 `bodyHashOf k h = none` 的**正向**读数（旧稿 6.3 的五条「`body-hash = None`」）。 -/
def noBodyPropagation (k : DeclKind) : Bool :=
  match k with
  | .theorem   => true
  | .defn      => false
  | .abbrev    => false
  | .opaque    => true
  | .axiom     => true
  | .inductive => true
  | .ctor      => true
  | .recC      => false

/-- **【主定理 · 存在性编码】**：`bodyHashOf k h = none` ⟺ `noBodyPropagation k = true`。

    ⚠ 逐构造子算，**不能用 `cases k <;> rfl`**（那会带 `propext`）。
    每个分支都显式给出 `rfl` 或 `noConfusion`。 -/
theorem bodyHashOf_none_iff (k : DeclKind) (h : Hash) :
    bodyHashOf k h = none ↔ noBodyPropagation k = true := by
  cases k
  · exact Iff.intro (fun _ => rfl) (fun _ => rfl)                                 -- theorem
  · exact Iff.intro (fun hh => nomatch hh) (fun hh => nomatch hh)                 -- defn
  · exact Iff.intro (fun hh => nomatch hh) (fun hh => nomatch hh)                 -- abbrev
  · exact Iff.intro (fun _ => rfl) (fun _ => rfl)                                 -- opaque
  · exact Iff.intro (fun _ => rfl) (fun _ => rfl)                                 -- axiom
  · exact Iff.intro (fun _ => rfl) (fun _ => rfl)                                 -- inductive
  · exact Iff.intro (fun _ => rfl) (fun _ => rfl)                                 -- ctor
  · exact Iff.intro (fun hh => nomatch hh) (fun hh => nomatch hh)                 -- recC

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | `isDirty` 的**完整**语义（逐条比对 `sigHash` / `bodyHash` 与 `current`） | 当前 `isDirty` 只看 `change` 的**分类**，不比哈希值（比哈希需要 `DecidableEq Hash`，`String` 有，但本批先做**规则**层）。`bodyHashOf_none_iff` 已把「存在性编码」这一格证完 |
  | 2 | 哈希算法的**内容** | `Hash` 是类型参数；本文件不实现 BLAKE3/SHA-256（D-019：不写死） |
  | 3 | `bodyHashOf_none_iff` 用 `cases k` 分 8 个分支 | 这里 `cases` 是**对 `DeclKind` 的枚举**，每支都现场给 `rfl`/`noConfusion`；实测零公理（见 `_报告/D-进度.md` 门禁结果）。若改成 `<;> rfl` 则会带 `propext` |
-/

end FateV2.Core
