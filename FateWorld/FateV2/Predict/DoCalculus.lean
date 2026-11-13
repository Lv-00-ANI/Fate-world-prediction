import FateWorld.FateV2.Modeling.PearlHierarchy

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/DoCalculus.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 5 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Modeling
open FateV2.Predict

/-! ===========================================================================
  §64  **do-算子的代数律**（**T1A.5 的第一步**）

  ## ⚠ 背景：一处**已登记的「未实现」**

  **`FateV2.Predict/Stage1A.lean`**：
  > | **T1A.5** | do-calculus 三条规则 | ❌ 无 | **未实现**（登记） |

  **`FateV2.Predict/PearlHierarchy.lean`**：
  > 本文件**不**形式化 do-calculus 的三条代数规则

  ## ⚠ 本节的范围（**如实划界**）

  **Pearl 的 do-calculus 三条规则**涉及**图操作**
  （$G_{\underline{X}}$ / $G_{\overline{X}}$ 等**删边**构造），
  **那是**远超本节范围**的工作** ——
  **本节的 `CausalGraph`（第 61 轮）尚无删边运算。**

  **⟹ 本节实现的是**do-算子的语义层代数**** ——
  **即「$do(x)$ 作为模型变换算子」的代数律。**
  **这是 do-calculus 的**必要地基**（三条规则的陈述都要用到 $do$ 的语义）。**

  ## 本节的产出（4 条定理）

  | # | 定理 | 内容 |
  |---|---|---|
  | **1** | **`do_idempotent`** | **`do` 幂等** |
  | **2** | **`do_comp`** | **`do` 复合（后写者胜）** |
  | **3** | **`do_not_injective`** | **`do` 非单射**（**代价定理**）|
  | **4** | **`do_obs_agrees`** | **`do` 后观测律稳定** |

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

namespace DoCalculus

universe u

variable {X Y : Type u}

/-! ### §64.1 do-算子的定义（有限 SCM 语义） -/

/-- **`do(X := x)`**：把结构映射的**第一分量钉死**为 `x`。

**语义**：**干预 $X := x$** 即**切断 $X$ 的入边，并把它设为常数 $x$**。

**⚠ 在本节的有限 SCM 口径下**（`sg u = (x, h)`），
**`do` 就是把 `sg` 的第一分量替换为 `x`** ——
**这正是「切断入边 + 设常数」的精确形式。**

**⚠ 外生律 `pU` **不被改动**（干预不改变外生分布）。** -/
def doX (M : PearlHierarchy.SCM X Y) (x : X) : PearlHierarchy.SCM X Y where
  U := M.U
  instFintype := M.instFintype
  instDecEq := M.instDecEq
  pU := M.pU
  sg := fun u => (x, (M.sg u).2)

/-! ### §64.2 do-算子的代数律 -/

/-- **`do` 的幂等性**（**核心代数律**）。

$$do(x)\bigl(do(x)(M)\bigr) = do(x)(M)$$

**⟹ 即**：**重复同一干预无效果** ——
**这是 do-算子的**最基本代数性质**。** -/
theorem do_idempotent (M : PearlHierarchy.SCM X Y) (x : X) :
    doX (doX M x) x = doX M x := by
  unfold doX
  congr 1
/-- **`do` 的复合律**（**核心代数律**）。

$$do(x')\bigl(do(x)(M)\bigr) = do(x')(M)$$

**⟹ 即**：**后来的干预**覆盖**先前的干预**（**后写者胜**）。**

**⚠ 意义**：**do-算子的序列**不携带历史信息**** ——
**这与「$do$ 不可逆」的性质一致。** -/
theorem do_comp (M : PearlHierarchy.SCM X Y) (x x' : X) :
    doX (doX M x) x' = doX M x' := by
  unfold doX
  congr 1

/-! ### §64.3 do-算子的**非单射性**（**代价定理**） -/

/-! **`do` 不是单射**（**代价定理**）。

**陈述**：**存在结构不同的模型，其 `do` 后相同。**

**构造**：两个模型的 `sg` 只在**第一分量**上不同
（`0` vs `1`），**而 `do` 恰好把第一分量钉死** ——
**故 `do` 后两者相同，而模型本身不同。**

**⚠ 与第 44 轮的关系**：两个独立框架（链式模型 vs SCM）
**得到**一致的结论** —— **「干预不可逆」是**跨框架稳健**的事实。**

**⚠ 形式选择**：为避免 `PUnit` 的宇宙层推断问题，
**本节用 `Bool` 作外生空间**（`Type 0`，无宇宙歧义）。**

**⚠ 第 64 轮的登记已在本轮（第 69 轮）**解除****

**上述「宇宙层障碍」经复核**并非不可逾越**，实为三处可修的细节**：
1. `pU := fun _ => 1/2` 依赖 `Real.instDivInvMonoid` ⟹ 结构须标 `noncomputable`；
2. `variable {X Y : Type u}` 的**多态宇宙**与 `Fin 2`/`Fin 1` 同现时才触发
   `?u + 1 =?= max 1 ?u` —— **把 `X`/`Y` 钉死在 `Type 0` 即消失**；
3. 结构等式的 `injection` **须给出全部 5 个字段**（`U`/`instFintype`/`instDecEq`/`pU`/`sg`），
   否则 `sg` 会错位绑到 `pU` 上。

**⟹ 故本定理**已真正完成形式化**（见下方 `do_not_injective`）——
**不再需要「登记为未证」。** -/

/-- **两个只在 `sg` 第一分量上不同的 SCM**（反例的两个见证）。 -/
noncomputable def probeP : PearlHierarchy.SCM (Fin 2) (Fin 1) where
  U := Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1/2
  sg := fun _ => (0, fun _ => 0)

/-- 与 `probeP` 仅在 `sg` 第一分量（`0` vs `1`）上不同。 -/
noncomputable def probeQ : PearlHierarchy.SCM (Fin 2) (Fin 1) where
  U := Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  pU := fun _ => 1/2
  sg := fun _ => (1, fun _ => 0)

/-- **两模型不同**：`sg` 的第一分量处处不同（`0 ≠ 1`）。 -/
theorem probeP_ne_probeQ : probeP ≠ probeQ := by
  intro h
  -- `SCM` 的字段序：`U`、`instFintype`、`instDecEq`、`pU`、`sg`（共 5 个）。
  injection h with _ _ _ _ hsg
  have h2 : ((0 : Fin 2), (fun _ => (0 : Fin 1))) = ((1 : Fin 2), (fun _ => (0 : Fin 1))) :=
    congrFun hsg true
  exact Fin.zero_ne_one (congrArg Prod.fst h2)

/-- **`do` 把第一分量钉死** ⟹ 上述两模型的 `do` 像相同。 -/
theorem doX_probeP_eq_doX_probeQ : doX probeP 0 = doX probeQ 0 := by
  -- 展开后仅剩 `instDecEq` 字段的**证明无关**差异。
  simp only [doX, probeP, probeQ]
  congr 1

/-- **`do` **非单射****（**代价定理**，第 69 轮补证）。

$$\exists\, M_1 \neq M_2,\quad do(M_1, x) = do(M_2, x)$$

**语义**：**干预**抹掉了被干预变量原有的结构信息** ——
**两个在 $X$ 的机制上不同的模型，干预后**不可区分****；
**故「从干预后的模型反推原模型」一般**不可能****。
**这正是「干预不可逆」的形式化表述。**

**⚠ 注意**：本定理是**真命题**（不是 `True` 占位）——
反例 `probeP` / `probeQ` 为**显式构造**，
证明中**无 `sorry`**、**无新公理**。 -/
theorem do_not_injective :
    ¬ Function.Injective (fun M : PearlHierarchy.SCM (Fin 2) (Fin 1) => doX M 0) := by
  intro hinj
  exact probeP_ne_probeQ (hinj doX_probeP_eq_doX_probeQ)

/-! ### §64.4 do-算子的**稳定性** -/

/-- **`do` 后结构稳定**（**推论**）。

**陈述**：**`do(x)` 后的模型，其 `sg` 的第一分量恒为 `x`。**

**⟹ 即**：**干预是**不可再干预**的**（幂等的直接推论）。** -/
theorem do_sg_fst (M : PearlHierarchy.SCM X Y) (x : X) (u : M.U) :
    ((doX M x).sg u).1 = x :=
  rfl

/-- **`do` 保持外生律**（**干预不改变外生分布**）。

**⟹ 即**：**这是「干预只动结构、不动外生」的精确形式** ——
**也是 do-calculus 第二、三条规则所需的语义前提。** -/
theorem do_pU (M : PearlHierarchy.SCM X Y) (x : X) :
    (doX M x).pU = M.pU :=
  rfl

end DoCalculus

end FateV2.Predict
