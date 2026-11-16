import FateWorld.FateV2.Predict.CausalClassificationBridge
import FateWorld.FateV2.Predict.CausalFCAAdjacency
import Mathlib.Tactic

/-!
  # Predict · CausalCtxUnified

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CausalCtxUnified.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CausalClassificationBridge, CausalFCAAdjacency
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate.CausalCtxUnified` —— 合并两份重复的 `ctxOf`

## 背景

审计 R399 指出「因果方向已 5 模块做 1 件事」，其中一处**纯重复定义**是：

| 位置 | 定义 |
|---|---|
| `Fate/CausalClassificationBridge.lean:298` | `def ctxOf (G : DAG V) : FateV2.Rules.FormalCtx` |
| `Fate/CausalFCAAdjacency.lean:150` | `def ctxOf (G : DAG V) : FateV2.Rules.FormalCtx` |

**实测**：两者的签名**逐字相同**（同 `DAG V`、同 `Fate.FormalCtx`、同 `universe u`、
同 `[DecidableEq V] [Fintype V]`），**定义体也逐字相同**：

```lean
{ GFCA := V, MFCA := V, Irel := fun a b => G.edge a b ∨ G.edge b a }
```

## 本文件的交付（纪律：**不改**那两个已入链的文件）

既然不能删重复定义，本文件把「重复」**固化为可复用的等式引理**——
下游只要 import 本文件，就可以把两份 `ctxOf` **当成同一个函数**用：

| 定理 | 内容 |
|---|---|
| `ctxOf_agree` | `Bridge.ctxOf G = Adjacency.ctxOf G`（**函数相等**，`rfl`）|
| `ctxOf_GFCA_agree` | 两者作为函数相等（`funext` 形式，用于需要 `funext` 的场合）|
| `ctxOf_Irel_agree` | 逐点关系等价：`Bridge..Irel a b ↔ Adjacency..Irel a b` |
| `ctxOf_GFCA_fields` | 对象集字段一致：`(Bridge.ctxOf G).GFCA = (Adjacency.ctxOf G).GFCA` |
| `ctxOf_MFCA_fields` | 属性集字段一致 |

**⚠ 关键事实**：这两个 `ctxOf` 是**不同命名空间下的不同常量**，
但它们的定义体在 Lean 中是**定义上相等**（defeq），故 `ctxOf_agree` 的证明是 `rfl`：
不是「巧合相等」，而是「**本来就是同一份定义被抄了两遍**」。
这正面支持审计 R399 的「纯重复」判定。

另记：`Fate/CausalFCADSep.lean:156` 的 `ctxOfSep (G : DAG V) (Z : Finset V)`
是**带条件集的变体**，签名不同（多一个 `Z` 参数），**不在本合并范围内**，
仅在此记录以备下游区分。
-/

namespace FateV2.Predict

open FateV2.Modeling
namespace CausalCtxUnified

open FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ## §1 函数相等（`rfl`） -/

/-- ⭐⭐⭐ **两份 `ctxOf` 是同一个函数**（定义上相等，`rfl`）。

这条定理是「合并」的**形式化**：不删定义，但下游可据它**任选一份**调用，
不必关心用的是 `CausalClassificationBridge` 还是 `CausalFCAAdjacency` 的版本。 -/
theorem ctxOf_agree (G : DAG V) :
    Fate.CausalClassificationBridge.ctxOf G
      = Fate.CausalFCAAdjacency.ctxOf G := rfl

/-- 同一事实的 **`funext` 形式**：两个 `ctxOf` 作为 `DAG V → FateV2.Rules.FormalCtx` 函数相等。 -/
theorem ctxOf_GFCA_agree :
    (Fate.CausalClassificationBridge.ctxOf :
        DAG V → FateV2.Rules.FormalCtx)
      = (Fate.CausalFCAAdjacency.ctxOf : DAG V → FateV2.Rules.FormalCtx) :=
  funext ctxOf_agree

/-! ## §2 逐字段一致 -/

/-- ⭐ **对象集字段一致**。 -/
theorem ctxOf_GFCA_fields (G : DAG V) :
    (Fate.CausalClassificationBridge.ctxOf G).GFCA
      = (Fate.CausalFCAAdjacency.ctxOf G).GFCA := rfl

/-- ⭐ **属性集字段一致**。 -/
theorem ctxOf_MFCA_fields (G : DAG V) :
    (Fate.CausalClassificationBridge.ctxOf G).MFCA
      = (Fate.CausalFCAAdjacency.ctxOf G).MFCA := rfl

/-- ⭐ **关系字段逐点等价**：两份 `Irel` 在任意 `a b` 上等价。 -/
theorem ctxOf_Irel_agree (G : DAG V) (a b : V) :
    (Fate.CausalClassificationBridge.ctxOf G).Irel a b
      ↔ (Fate.CausalFCAAdjacency.ctxOf G).Irel a b :=
  Iff.rfl

/-! ## §3 合并后可用的统一接口 -/

/-- ⭐⭐ **统一接口**：给定 `G`，`unifiedCtxOf G` 就是那个唯一的 `FormalCtx`。
它**借用** `CausalFCAAdjacency.ctxOf`（避免再抄第三遍）。 -/
def unifiedCtxOf (G : DAG V) : FateV2.Rules.FormalCtx :=
  Fate.CausalFCAAdjacency.ctxOf G

/-- ⭐⭐ `unifiedCtxOf` 与 `CausalFCAAdjacency.ctxOf` 相同（`rfl`）。 -/
theorem unifiedCtxOf_eq_adjacency (G : DAG V) :
    unifiedCtxOf G = Fate.CausalFCAAdjacency.ctxOf G := rfl

/-- ⭐⭐⭐ `unifiedCtxOf` 与 `CausalClassificationBridge.ctxOf` 也相同——
**这就是「合并」的落点**：一份接口，两份来源都对得上。 -/
theorem unifiedCtxOf_eq_bridge (G : DAG V) :
    unifiedCtxOf G = Fate.CausalClassificationBridge.ctxOf G :=
  (ctxOf_agree G).symm

/-- ⭐ `unifiedCtxOf` 的对象集是 `V`。 -/
theorem unifiedCtxOf_GFCA (G : DAG V) : (unifiedCtxOf G).GFCA = V := rfl

/-- ⭐ `unifiedCtxOf` 的关系是对称化的有向边。 -/
theorem unifiedCtxOf_Irel (G : DAG V) (a b : V) :
    (unifiedCtxOf G).Irel a b ↔ G.edge a b ∨ G.edge b a := Iff.rfl

end CausalCtxUnified
end FateV2.Predict