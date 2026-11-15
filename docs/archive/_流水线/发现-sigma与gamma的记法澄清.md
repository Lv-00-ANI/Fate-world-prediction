# 澄清：多模态的 σ 与 γ（T28 与 T31 的"冲突"是记法造成的）

> **日期**：2026-11-03
> **起因**：T28 与 T31 对「多模态 σ 是否联合」给出看似相反的结论
> **结论**：两者**不矛盾**，是我（协调者）读错了 T28 的命题

---

## 一、实际定义

### T28（`VerdictGeneral.lean:265`）

```lean
def IsJointBoundary {ι : Type} [Fintype ι] (W : ι → ErrProfileN) (σ : ι → Real) : Prop :=
  ∃ γ : Nat, ∀ i : ι, IsFitBoundaryN (W i) (σ i) γ
```

**注意**：`σ : ι → Real` 是**函数**（逐分量），`γ : Nat` 是**单一标量**（联合）。

### T28 的 `multiGamma_conflict`

```lean
theorem multiGamma_conflict :
    IsComponentwiseBoundary conflictFamily (fun i => ...) ∧
    ¬ IsJointBoundary conflictFamily (fun i => ...)
```

**它证的是**：存在一个 `σ`（逐分量的函数），使得
- **逐分量**边界存在（每个 `i` 有自己的 `γ`）
- **联合**边界不存在（无法用单一 `γ` 覆盖全部）

**⟹ 它证的是「`γ` 不能联合」，不是「`σ` 不能逐分量」。**

### T31（`Coupling.lean`）

```lean
def ErrEnv.jointSigma (E) (σ : Nat) : Prop := ∀ (i : M) (γ : Nat), E.env i γ ≤ σ
def ErrEnv.pointwiseSigma (E) (σ : M → Nat) : Prop := ∀ (i : M) (γ : Nat), E.env i γ ≤ σ i
theorem joint_to_pointwise : jointSigma σ → pointwiseSigma (fun _ => σ)
theorem sigma_pointwise_iff_joint : 逐分量 → 联合 需公共上界
```

**它说的是 σ 的两种取法之间的关系。**

---

## 二、正确的统一陈述

> **σ 是联合的**（单一标量，由最坏模态决定，T31 已证）
> **γ 是逐分量的**（每个模态有自己的最优分辨率，T28 已证）

**两者不矛盾，因为说的是不同变量。**

| 变量 | 结论 | 依据 |
|---|---|---|
| **`σ`** | 联合（单一标量，需公共上界才能从逐分量推出） | T31 `sigma_pointwise_iff_joint` + `joint_sigma_tight` |
| **`γ`** | 逐分量（不能用单一分辨率覆盖所有模态） | T28 `multiGamma_conflict` |

---

## 三、仍然缺的定理

T39 指出两个**未形式化**的关键点：

1. **「`γ` 必须逐分量」需要加条件**——
   在二值/单调场景里，「`γ` 逐分量」与「`γ` 联合」**可能等价**。

2. **`UnifiedVerdict` 的 `consistent` 推不出 `JointSigma`**——
   `consistent : ∀ i, env i (gamma i) ≤ sigma` 只约束了 `gamma i` 这一个点，
   **未覆盖的分辨率没约束**。所以「σ 联合」会退化成「σ 是个标量」这个空条件。

   **需要补一条「σ 是上确界」的桥接定理**，否则统一陈述是空的。

---

## 四、教训（给我的）

**我读错了 T28 的命题陈述。** 我看到 `IsJointBoundary` 里有 `σ : ι → Real`，
就以为它在讨论「σ 逐分量」，实际上它在讨论「γ 联合」。

**这是第三次因为「凭印象转述别的专项的结论」而误判。**

改进：**引用其他专项的结论时，必须先读一遍实际的定义和命题陈述**，不能凭报告里的摘要。
