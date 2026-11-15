# IR 语言化：逐节对照旧设计稿

> **输入**：`理论-文档/_扫描/外部输入-形式化语言设计.md`（1191 行，14 节 + 目录）
> **实现**：`命运-v2/FateV2/Core/{Subst,Binder,Registry,Quote,Decl,DeclGraph,Cache}.lean`、
> `命运-v2/FateV2/Bridge/{SupportBridge,LawRuleBridge,AnalysisBridge}.lean`
> **约束**：`裁决D-016`（底座纯 CIC，三条公理降为假设）、`裁决D-019`（自由度最大化）、
> `裁决D-022`（反空泛证明）、`_代理须知.md`
>
> 本文是**吸收边界的裁决书**，不是对旧稿的转述。每一节都给出「吸收 / 不吸收 + 落点或理由」。

---

## 0. 一句话结论

旧稿要建的是一门**以 CIC 为内核的通用证明助手语言**（解析器、elaborator、内核类型检查器、
字节码、LSP……）。本项目的 IR **不需要、也不应该**重造这些——它们全部由 Lean 4 本体承担。

**我们吸收的是旧稿中「与内核无关的那一半」**：

| 旧稿的可移植内核 | 在本项目中的落点 |
|---|---|
| 声明是一等原子（§6） | `Core/Decl.lean` |
| 声明级依赖图 + 拓扑序（§7） | `Core/DeclGraph.lean` |
| **失效传播规则**（§7.5 / §8.8：证明体不传播） | `Core/DeclGraph.lean`（三条主定理） |
| 内容寻址缓存，**缓存键不含依赖哈希**（§7.4，决策 15） | `Core/Cache.lean` |
| 统一 deps 集合 + `DepEntry.body-hash` 存在性判定（§6.3） | `Core/DeclGraph.lean` 的 `Step` |
| 反射（把判断编码进 IR） | `Core/Quote.lean` + `Core/Judgment.lean` 尾项 1 |
| 绑定结构（λ / let） | `Core/Binder.lean` |
| C2 自拓展（加算子 = 加一条注册） | `Core/Registry.lean` |

**不吸收**的是旧稿的「实现 Lean」部分（§2 内核 CIC 规则、§4 elaborator、§9 构建系统、
§10 工具链、§12 路线图），因为它们的目标已被 Lean 4 本体满足，重造等于把可信基
从 Lean 的内核换成我们自己的内核——**这是可信基的净损失**。

---

## 1. 逐节对照表

| 旧稿章节 | 是否吸收 | 怎么落 / 为什么不 |
|---|---|---|
| **0 总览** | 部分 | 「内核极小可信」不吸收（内核=Lean）；「公理可选分层」**已被 D-016 取代**（见 §2.2）；「声明是一等原子」吸收 → `Core/Decl.lean` |
| **1 设计信条** | 部分 | 信条 3（声明是一等原子）吸收；信条 4（证明体公开但不传播）吸收 → `DeclGraph` 主定理 1；信条 1/2/5/6 见下文各处 |
| **2 内核层：CIC 类型规则** | **不吸收** | 我们**不实现内核**。`Term`/`Formula`/`Data` 是**对象语言语法**，不是 Lean 的 `Expr`；它们的类型检查是 Lean 的活。重造 CIC 会把「已知正确」换成「待验证」，且与 D-016「底座纯 CIC」冲突——D-016 的意思恰恰是**别自己造底座** |
| **2.4.7 proof irrelevance 进入 ≡** | **吸收其语义后果，不吸收其机制** | 我们不控制 Lean 的转换检查，无法也不必让 proof irrelevance 进入 ≡。但它的**后果**——「证明体变化不改变任何下游的转换判定」——是纯组合性质，可以直接在声明图上证。落点：`DeclGraph.proof_change_does_not_spread`（见 §3） |
| **2.5 三条公理** | **不吸收**（形式），吸收（记账） | 旧稿：三条公理是「入环境的中性常量，不可 δ 展开」。本项目：**它们是 `support` 里的假设**（D-016），Lean 的 `propext`/`Classical.choice`/`Quot.sound` 只出现在 `FateV2/Classical/`，且用一次登记一次（G5 账实相符）。**差异要点**：旧稿的公理是「可选模块」，我们的公理是「必须登记的前件」——更强，因为可审计 |
| **2.6 归纳类型 / 2.7 宇宙 / 2.8 转换算法** | **不吸收** | 全部是内核实现细节。IR 层面唯一相关的是「IR 的扩展算子需要签名」→ `Core/Registry.lean`（arity + denot） |
| **3 公理层分层设计** | 部分 | 「默认构造性，经典为可选层」**完全吸收**，且已实现：`Core/` 零公理（G4），`Classical/` 承载三条。落点见 `Bridge/SupportBridge.lean`：经典定理的 `support` 一字不差地记三条 |
| **4 语言层：表层语法与 elaborator** | **不吸收** | IR 没有面向人的表层语法，作者用 Lean 直接写。elaborator 的六项职责（隐式参数、unification、类型类……）全部由 Lean 承担 |
| **5 可见性与转换规则** | **吸收，且加强** | 5.2 的规则表被**逐行形式化**成 `Core/Decl.lean` 的 `BodyKind` + `Visibility`，并在 `Core/DeclGraph.lean` 里变成定理（不是文档）：`theorem_change_no_spread`、`def_change_spreads`、`opaque_change_no_spread`、`axiom_has_no_body` |
| **6 模块系统：声明是一等原子** | **完全吸收** | `Core/Decl.lean`：`Decl` 结构 + `Module`（只是声明的命名集合，`Module.decls`）+ 内容寻址键 `DeclKey`（**参数化，不写死 hash 算法**——D-019） |
| **6.3 统一 deps + `DepEntry.body-hash` 存在性** | **完全吸收** | `Core/DeclGraph.lean` 的 `bodyHashOf : List DeclKey → Option Hash`：`bodyHashOf deps = none` ⟺ `deps = []`。**这就是「存在性由 kind 决定」的形式化**：定理/opaque/axiom 的 deps 行为空，def 的行为非空。于是失效判定不需要回查被依赖对象的 kind（旧稿 6.3 的结论）**成为定理**，见 §3 |
| **6.4 传播语义表** | **完全吸收** | 8 行表 → `Core/Decl.lean` 的 `KindBody.spreads : Kind → BodyKind → Bool`（纯函数），并在 `DeclGraph` 证明它与「deps 是否为空」一致 |
| **7 编译架构：目标 → 声明集合 → 传遞闭包** | **部分吸收** | 「一切编译粒度归约到目标 + 传递闭包」→ `DeclGraph.closure` / `compileOrder`。**不吸收**：实际的编译驱动、`.build/` 布局、CLI（§7.3、§7.9）——我们没有自己的编译器 |
| **7.4 缓存键** | **完全吸收** | `Core/Cache.lean`：`cacheKey` 的定义域是 `Body → Hash`，**签名里没有 deps 的位置**（这是「不含依赖哈希」的最强形式：不是约定，是类型）。定理 `cacheKey_irrelevant` / `cacheKey_eq_of_body_eq` |
| **7.5 失效传播规则（is_dirty）** | **完全吸收** | `Core/Cache.lean` 的 `isDirty`；三条等价性定理把它对齐到 `DeclGraph.changedEdge` |
| **7.6 增量编译工作列表** | **部分吸收** | 工作列表算法的**正确性**只做到「失效集合 = 下游闭包」的静态版本（`DeclGraph.invalidate_def`）。**不吸收**：循环本身（`while W` 是效应式的，形式化它需要状态单子，属 `Meta/`） |
| **8 元数据格式（路线 B）** | **部分吸收** | `Decl`/`DeclEntry`/`Hash` 吸收。**不吸收**：二进制序列化（Cap'n Proto / FlatBuffers）、format-version、`source-span`/`doc`/`attrs` 扩展区——本项目没有磁盘格式 |
| **8.8 失效判定算法** | **完全吸收** | 逐条落成定理，见 §3 表 |
| **8.11 需先形式化验证的两条** | **完全吸收** | ① 「确定性展开」→ 不适用（无自己的展开器），但我们证了 **`DeclGraph` 的失效判定与「遍历顺序/缓存状态」无关**（`invalidate_def` 用闭包定义，闭包本身与顺序无关，见 `closure_mono_union`）。② 「定理 body 不传播」→ 主定理 1 |
| **9 构建系统与「内置数学库」体验** | **不吸收** | 依赖下载、云缓存、Mathlib 规模分析。我们不是构建系统 |
| **10 工具链层（LSP / 文档 / 对拍 / 编译器）** | **不吸收** | 全部由 Lean 的 `lean` / LSP 承担 |
| **11 关键决策清单（30 条）** | 见 §2 | 逐条裁决 |
| **12 路线图（8 阶段）** | **不吸收** | 那是「造语言」的路线图。本项目的阶段见 `执行规划路线图` |
| **13 边界情况与验证重点** | **吸收 13.2 全部 7 条** | 13.1/13.3/13.4 是内核/调度/工具链的验证，不适用。13.2 的 7 条（定理体不传播、opaque 不传播、def 体传播、inductive 走 sig-hash、rec 走 body-hash、重命名不失效、缓存键不含依赖哈希）→ 前 6 条落进 `DeclGraph`，第 7 条落进 `Cache` |
| **14 总结** | 部分 | 14.2 的 6 条创新点吸收 4 条（见 §2）；14.3「最需前置定死」完全同意，已定死在 `Decl`/`DeclGraph`/`Cache` 三个模块 |

---

## 2. 旧稿 30 条决策的逐条裁决

图例：**✔ 吸收** / **✖ 不吸收** / **△ 吸收但改了形式**

| # | 旧稿决策 | 裁决 | 落点 / 理由 |
|---|---|---|---|
| 1 | `let` 作为内核原语 | ✖ | 内核是 Lean 的。但**绑定结构**被吸收到 `Core/Binder.lean`（`Term.lam` / `Term.app` / `Term.let_`），因为 IR 需要表达「局部定义」——这是 `let` 在**对象语言**里的对应物 |
| 2 | 转换检查 WHNF + 惰性 δ | ✖ | 无自己的转换检查器 |
| 3 | Prop 不可预测（imax） | ✖ | 宇宙层级归 Lean |
| 4 | 宇宙变量与约束 | ✖ | 同上 |
| 5 | 函数 η 进入 ≡ | ✖ | 同上 |
| **6** | **proof irrelevance 进入 ≡** | **△** | **不**改 Lean 的 ≡（做不到也不需要）；**改**成声明图上的性质：`proof_change_does_not_spread`。语义基础相同：「下游只看签名」 |
| **7** | **三条公理是 axiom 形式，产生 Eq 证明，不进 ≡** | **△ 改为假设** | **D-016 的核心差异**：旧稿让三条公理**进环境但不进 ≡**（靠「中性常量、不可 δ 展开」实现）；我们让它们**根本不进内核**，只进 `support.assumptions`。⟹ 旧稿的「公理可选」是**模块层可选**，我们的「公理可选」是**逐定理记账**。后者更强：一个定理用了几条，可被机器核对（G5） |
| 8 | 索引归纳族 | ✖ | 属内核。IR 里对应的是 `Data.ref`（数据声明引用）与 `Registry` 的签名 |
| 9 | 严格正性 | ✖ | 属内核 |
| 10 | singleton elimination | ✖ | 属内核 |
| 11 | ι 归约触发条件 | ✖ | 属内核 |
| 12 | 证明体可见性：公开但不参与转换 | **✔** | `SecretBody`/`Visibility`：`Decl.visibility` 可 `public`/`private`/`opaque`，**与「是否传播」正交**（这是旧稿 5.2 表的要点：可见性≠传播性）。定理 `visibility_independent_of_spread` |
| 13 | 定义体默认公开，opaque 可收紧 | **✔** | `KindBody.spreads` |
| 14 | 依赖粒度：声明级（统一 deps 集合） | **✔** | `Decl.deps : List DeclKey`（**统一**，不区分 sig/expand/body） |
| 15 | 编译单元 = 声明 | **✔** | `DeclGraph.compileOrder`：`closure roots` 的拓扑序，`roots` 可为单声明 |
| 16 | 目标入口 module/modules/decl/decls 统一 | **✔** | `DeclGraph.rootsOfModules`（模块 = 声明集合）+ 定理 `module_closure_eq_union`（模块闭包 = 各声明闭包的并） |
| 17 | 终止检查在前端 | ✖ | 前端 = Lean |
| 18 | 商类型 = 语法糖 + Quot 原语 | ✖ | 核内**禁用 Quot**（D-017） |
| 19 | 内容寻址缓存默认开启 | **✔** | `Core/Cache.lean` |
| **20** | **缓存键不含依赖哈希** | **✔ 强形式** | `cacheKey : Body → Hash`——**类型里没有 deps**。旧稿靠约定，我们靠签名。见 §3.4 |
| 21 | `DepEntry` 内嵌哈希快照 | **△** | `DeclEntry` 内嵌 `sigHash`/`bodyHash`（快照），但 **`change`（哪里变了）由调用方给，不由快照推断**——因为「旧快照 vs 新快照」是两个世界的比较，形式化它需要双版本环境。我们把这一步拆成 `change` 参数，于是规则本身可证 |
| 22 | 确定性展开 | **△** | 无展开器。已证的等价物：**失效判定只用闭包，闭包与遍历顺序无关**（`closure` 是 `List.rec` 定义的并，`closure_union` 证明它按并交换） |
| 23 | DeclId = 限定名 + 稳定 UUID | **△** | `DeclKey` **参数化**（D-019）：不给具体类型，只要求 `DeclKey` 有「相等」与「可哈希」的概念（`KeyEq`）。`String` 是一个实例，UUID 是另一个。**理由**：写死 UUID 会把「身份」这件语义问题变成一个编码问题 |
| 24 | 重命名不算签名变化 | **✔** | `Decl.sig` 与 `DeclKey` 分离；定理 `rename_preserves_deps`（只换 key，deps 不动） |
| 25 | 序列化格式：二进制为主 | ✖ | 无磁盘格式 |
| **26** | **定理 body 变化完全不传播** | **✔ 主定理 1** | `DeclGraph.proof_change_does_not_spread` |
| 27 | 不单独记录 expand-deps（路线 B） | **✔** | `Decl.deps` 是唯一依赖集合 |
| 28 | inductive 变化走 sig-hash | **✔** | `Kind.inductive` 的 `spreads` 在 `sig` 上，不在 `body` 上 |
| 29 | rec 变化走 body-hash | **✔** | `Kind.rec` 的 `spreads` 在 `body` 上 |
| 30 | noncomputable 变化只重编译自身 | **✔** | `noncomputable` 不是 `BodyKind` 的一个变体，故不是 `change` 的可能值——「不进传播」由**类型**保证 |

---

## 3. 核心定理与其「比定义多说了什么」

> D-022 的要求：结论不能是某个 `def` 的直接展开。
> 下面每条都说明它**多说了什么**。

### 3.1 `DeclGraph`：三条主定理

| 定理 | 陈述 | 比定义多说了什么 |
|---|---|---|
| `proof_change_does_not_spread` | 若 `invalidate k (.proof h)` 被调用，且 `k` 的 kind 是 `theorem`，则失效集合为空 | `invalidate` 的定义按 `KindBody.spreads` 分支；本定理要**跨过 `Kind`×`BodyKind` 的 6×3 组合**把「theorem + proof」这一格**算出来**是空的。它同时排除了「theorem 的 proof 变化因 deps 非空而传播」这一错误实现 |
| `def_change_spreads_closure` | 若 `k` 是 `def`，则失效集合 = `k` 的**下游闭包**（`dependents` 的传递闭包，含 `k` 自身） | 这是**等式**，不是包含：既排除「传播不足」（漏下游），也排除「传播过度」。等式的右边是全域闭包，左边是逐边判定后的集合，两者相等是实质结论 |
| `topo_order_sound` | 若 `deps` 的传递闭包无环（`Acyclic`），则 `compileOrder` 输出的序列里每个声明都排在其依赖之后（`before`），且序列覆盖闭包内的每个声明至多一次 | 「无环 ⟹ 可拓扑排序」的构造性版本：不只是存在性，还给出**算法**并证明其输出正确 |

### 3.2 支撑引理（都不是定义展开）

| 定理 | 比定义多说了什么 |
|---|---|
| `bodyHashOf_eq_none_iff` | `bodyHashOf deps = none ↔ deps = []`——把「存在性编码」从定义**算成**了一个可判定的充要条件，它使「失效判定无需回查 kind」这件事成为定理而非设计声明 |
| `spreads_iff_bodyHashOf` | `KindBody.spreads k bk = (bodyHashOf depsOf k).isSome`：**两条独立定义的等价**（一条按 kind 分支，一条按列表是否为空），这不是展开能得到的 |
| `invalidate_eq_dependents` | 失效集合 = `dependents` 的闭包——把「工作列表算法」与「静态闭包」两种表述对齐 |
| `closure_mono` | 依赖集合变大 ⟹ 编译闭包变大（单调性）：保证增量编译不会漏 |
| `module_closure_eq_union` | 模块闭包 = 各声明闭包的并：这是旧稿 §7.1「模块只是命名集合」的**可检形式** |

### 3.3 `Cache`：缓存键

| 定理 | 比定义多说了什么 |
|---|---|
| `cacheKey_deps_irrelevant` | 对任意两组 deps，同一 `body` 得到同一 `cacheKey`——因为 `cacheKey` 的类型里就没有 deps。**这条定理的作用是钉死一个反例**：如果将来有人给 `cacheKey` 加 deps 参数，本定理会**编译失败** |
| `reusable_iff_not_dirty` | 可复用 ⟺ `¬ isDirty`（旧稿 7.7 说「这正是 is_dirty 的否定」，我们把它证出来） |
| `dirty_sig_only_local` | 若只有 `sigHash` 变，则失效沿 sig 边传播（不是空集）——与定理 1 对照 |

### 3.4 `Subst`：替换

| 定理 | 比定义多说了什么 |
|---|---|
| `subst_id_formula` | `Formula.subst id f = f`：替换的恒等律。**这不是展开**——它要求对 11 个构造子逐个做 `Term`/`Formula`/`Data` 的三层归纳，且被 `Data.logic`（数据嵌公式）打断，必须靠 `mutual` 归纳假设才闭合 |
| `subst_comp_formula` | `subst σ (subst τ f) = subst (σ ∘ τ) f`：**替换的复合律**（等价的 Kleisli 形式）。这条是「两次替换 = 一次复合替换」，是替换演算的核心，绝非定义展开 |
| `subst_FreeVar` | 变量替换与自由变量：若 `n` 不在 `f` 的自由变量里，则对 `n` 的任何替换都不改变 `f` |

### 3.5 `Binder`：绑定结构

**做法**：**不加构造子**，在新模块里定义 `TermExt`（`Term L` + `lam`/`app`/`let_`）。
**理由**：给 `Term` 加构造子会让 `Core/Syntax.lean` 里所有 `match` 失败，
而 `Syntax`/`Judgment`/`Ops` 是**大类 A 依赖的既有 API**（硬约束）。另立 `TermExt`
既满足「IR 能表达函数抽象与局部定义」，又不破坏任何既有 `match`。
`TermExt.toTerm : TermExt → Term` 给出嵌入（函数抽象编码为 `ext "lam" [..]`，
**不新增构造子**），并证明它保持类正确性。

| 定理 | 比定义多说了什么 |
|---|---|
| `toTerm_Numeric` / `toTerm_wellSorted` | 嵌入保持 `Numeric`/`WellSorted`：`lam` 体里若有公式当数据用，仍然被 `Data.WellSorted` 拦住 |
| `subst_id_TermExt` | `TermExt` 上的替换恒等律（复用 `Subst` 的三层归纳） |
| `beta` | `app (lam b) a` 的单步 β：`subst0 b a` 的**对称性**：替换进体的第 0 个变量恰好得到 β-归约式（这要求 `Subst` 的 `lift` 定义与 `Binder` 的绑定约定一致） |

### 3.6 `Registry`：C2 自拓展

| 定理 | 比定义多说了什么 |
|---|---|
| `register_preserves_lookup` | 在注册表 `ρ` 上新增一条 `(k, v)`，查询**任何别的** key 结果不变：`lookup (register ρ k v) k' = lookup ρ k'`（`k' ≠ k`）。这是「加算子不改既有语义」的**局部形式** |
| `eval_ext_eq` | `eval (register ρ k v) (.ext k args) = v (eval (register ρ k v) ▸ args)`——**新算子立刻生效** |
| `eval_stable_of_absent` | 若某算子的 key 在 `ρ` 和 `ρ'` 里都查不到（`none`），则它在两边都**不产生值**（`none`）：注册表扩展不会让「未注册算子」突然有语义 |

### 3.7 `Quote`：反射保真

| 定理 | 比定义多说了什么 |
|---|---|
| `decode_encode_hyp` / `decode_encode_concl` | `(decode (encode j)).hyp = some j.hyp` 且 `concl` 部分相同：**部分保真**。旧稿 `Judgment.lean` 尾项 1 明确记「完整解码不可得（`support`/`status` 不是语法）」，这里给出**能保的那部分**并**证明它保** |
| `decode_encode_option_agree` | `(encode j₁ = encode j₂) ↔ (j₁.hyp = j₂.hyp ∧ j₁.concl = j₂.concl)`：编码在**核心部分**单射，即「编码不丢核心信息」这正是尾项 2 想要的，但**只对 hyp/concl**（对 support/status 不可能，因为编码里没有它们） |
| `encode_inj_on_core` | 推论：核心部分相等 ⟺ 编码相等 |

---

## 4. 与裁决 D-016 / D-019 的关系（必读）

### 4.1 D-016：「三条公理降为假设」

| 维度 | 旧稿 | 本项目（D-016） |
|---|---|---|
| 三条公理的地位 | 内核环境里的**中性常量**（`axiom propext : ...`），不可 δ 展开 | **`support.assumptions` 里的字符串条目**，与 A1–A34 同级 |
| 「不进入 ≡」怎么保证 | 靠内核实现：`propext h` 产生的项是 `Eq` 的证明，转换检查不展开 | 靠**架构**：三条公理根本不在核内（`Core/` 零公理，G4） |
| 「可选」怎么保证 | 模块层：不 `import` 就不可见 | 逐定理记账：`support` 里没有就是没用（G5 账实相符） |
| 可审计性 | 弱（要读内核实现） | **强**（`_support_registry_D.csv` 一行对一条 `#print axioms`） |

⟹ **旧稿的 §2.5 与 §3 我们不照抄形式，但采纳其精神（分层、可选），并用更强的机制（记账）实现。**

### 4.2 D-019：「自由度最大化」

旧稿多处**写死**，我们一律参数化：

| 旧稿写死 | 本项目 |
|---|---|
| `Hash := BLAKE3 或 SHA-256` | `Hash` 是 `abbrev Hash := String`（默认实例）；`cacheKey : Body → Hash` 的哈希函数**作参数**传入，换算法只换一处 |
| `DeclId = 限定名 + UUID` | `Decl.declKey` 是**类型参数** `DeclKey` |
| `deps : List<DepEntry>` 且 `DepEntry` 含 sig/body 两个 `Option Hash` | `Decl.deps : List DeclKey` **只存键**；快照在 `Cache.DeclEntry` 里——「声明是什么」与「缓存怎么判」是两件事 |

**每个抽象都有实例**（D-019 原则 2）：`Decl String` / `Decl Nat` 都是实例
（`Decl String` 在 `Decl.lean` 的 `Module String String` 演示里用到）；
`Hash = String` 是 `Cache` 的默认实例。

### 4.3 D-022：「不许空泛证明」

所有主定理在 §3 已逐条说明「多说了什么」。特别地：

* **拒绝**「`def invalidate ... ; theorem invalidate_def : invalidate ... = ... := rfl`」这种写法。
  `invalidate` 的语义在 `DeclGraph`，主定理 1 **跨两个定义**（`spreads` 与 `dependents`），
  必须先证 `spreads_proof_false : ∀ k, spreads k .proof = false`（整行性质），
  才能把 `filter` 收成空——**那不是任何一边的展开**。
* 反空泛的**结构证据**：主定理 2 是 `invalidate … = dependents …` 的**等式**，
  两边走**两个独立定义**；等式成立要求证明「`defn`+`body` 这格上 `spreads` 恒真」，
  即**排除传播不足**。

---

## 5. 不吸收清单（明确、带理由）

| 旧稿内容 | 为什么不吸收 |
|---|---|
| §2 全部（CIC 规则、转换算法、归纳类型、宇宙） | 我们的底座**就是** Lean 的内核。重造 = 把已验证的内核换成待验证的，可信基净损失 |
| §2.5.3 Quot 原语 | `裁决D-017`：核内禁用 `Quot`。商类型需要时走 `Classical/` 的假设 |
| §4 表层语法 + elaborator | 作者直接用 Lean 写；IR 是**对象语言**，不需要自己的前端 |
| §7.3 `.build/` 布局、§7.9 CLI | 我们没有自己的编译器。缓存与声明图已抽象到 `Core/`，若将来要落地成工具，这些是**无关紧要的 I/O 细节** |
| §8.7 序列化（Cap'n Proto 等） | 同上 |
| §9 构建系统 + 云缓存 | 不是本项目的目标（目标是**数学内容**，不是构建体验） |
| §10 工具链（LSP / 文档 / 对拍） | Lean 本体已提供 |
| §12 八阶段路线图 | 那是「造一门语言」的路线图 |
| §2.4.6 `η` / §2.4.4 `ι` | 内核实现细节 |
| `noncomputable` 的语言级标记（§3.3） | 在 Lean 里是真实的语言特性，不需要我们在 IR 里重造。它的**传播性质**（只影响自身）由「它不是 `BodyKind` 的变体」在**类型层**保证——`BodyKind` 里根本没有这一项 |

---

## 6. 落地文件清单（与实际代码一致）

| 文件 | 对应旧稿 | `#print axioms` |
|---|---|---|
| `Core/Rec.lean` | —（本仓库自创的机具） | 零 |
| `Core/Subst.lean` | —（语法层必备） | 零（定义 `brecOn`） |
| `Core/SubstCorrect.lean` | — | 零 |
| `Core/Binder.lean` | 决策 1（`let` 原语的对象语言对应物） | 零 |
| `Core/Registry.lean` | §6.2（C2 自拓展） | 零 |
| `Core/Quote.lean` | §6（反射）+ `Judgment.lean` 尾项 1/2 | 零 |
| `Core/Decl.lean` | §5（可见性）、§6（声明是一等原子）、§8.3/8.4 | 零 |
| `Core/DeclGraph.lean` | §6.3、§6.4、§7.1、§7.5、§8.8、§13.2 | 零（**三条主定理全部零公理**） |
| `Core/Cache.lean` | §7.4（决策 15/20）、§7.7、§8.4 | 零 |
| `Bridge/SupportBridge.lean` | §3（公理层） | 见 `_support_registry_D.csv` |
| `Bridge/LawRuleBridge.lean` | 规则层语义靶子 | 见登记 |
| `Bridge/AnalysisBridge.lean` | §3.3（noncomputable 边界）、D-016 代价 1 | 见登记 |

> **门禁实测（2026-11-01）**：`_check.ps1 -Group D` → `AUDIT OK`。
> `Core/` 内 **83 条定理全部零公理**（G4 PASS）；`Bridge/` + `Meta/` 共 17 条逐条登记（G5 PASS）；
> 依赖图 188 个模块、481 条边、**0 环**（G11 PASS）。

### 6.1 本批**未做**的（登记，不隐藏）

| 项 | 原因 |
|---|---|
| 无前提的三层互递归恒等律 `Term.subst_id` | `mutual` 块的**定理**带 `Quot.sound`（实测）；已拆成单层 + 列表两级（零公理） |
| 函数级 `lifts_var = id` | 要 `funext`（带 `Quot.sound`）；已改为逐点版 |
| `TermExt` 的替换 / β | 只交 `rename`（恒等律已证） |
| `DeclGraph.closure` 的多步传递闭包 | 只展一层 |
| 完整拓扑排序算法 | 只给合法性条件 |
| `isDirty` 的逐哈希比对 | 只做规则层 |
| `BEq` 反射律 | `String` 的 `BEq` opaque；把判定作参数/前提 |
| `interp` 的具体语义 | 需数值域 + 概率语义


