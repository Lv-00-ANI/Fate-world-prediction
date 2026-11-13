/-
  ===========================================================================
  `Fate/T35Rule1NoConfounding` —— **反例登记：草稿的第 242 轮 G3 命题为假**
  ===========================================================================

  ## 0. 本文件是什么

  第 242 轮 G3 代理产出了一份 218 行的草稿，标题为
  「**do-calculus 规则 1 的语义版本**（T3.5 的逆命题：
  **无混杂 ⟹ 观测律 = 干预律**）」。

  **⚠ 本文件是那份草稿的「反例登记」，不是它的修复版。**

  ## 1. 草稿的命题

  草稿定义了（原样抄录，见 §2 的 `NoConfoundingDraft`）：

  ```lean
  def NoConfounding (M : SCM X Y) (e : M.U ≃ Ux × Uy) : Prop :=
    (∀ (u : Ux) (v v' : Uy), (M.sg (e.symm (u, v))).1 = (M.sg (e.symm (u, v'))).1) ∧
    (∀ (u : Ux) (v : Uy),    (M.sg (e.symm (u, v))).2 = (M.sg (e.symm (u, v))).2)
  ```

  然后打算证明 `rule1_no_confounding`：

  ```lean
  theorem rule1_no_confounding ... :
      ∀ x, SCMSemantics.doLaw M x = SCMSemantics.condY M x
  ```

  ## 2. ⭐⭐⭐ 为什么这个命题为假（本文件的核心）

  **草稿的 `NoConfounding` 是一个恒真的退化谓词**，理由精确到一行：

  > **第二个合取项的左右两边是同一个项** `(M.sg (e.symm (u, v))).2`，
  > 于是它是 `fun _ _ => rfl`。**（`draft_second_conjunct_tautology`）**

  因此（`draft_NoConfounding_iff`）：

  ```lean
  NoConfounding M e  ↔  (∀ u v v', (M.sg (e.symm (u, v))).1 = (M.sg (e.symm (u, v'))).1)
  ```

  **⟹ 「无混杂」只约束 `X` 的方程不读 `Uy` 分量；
  它对 `Y` 的方程 `(M.sg ·).2` 施加零约束。**

  而「`condY = doLaw`」要成立，恰恰需要 `Y` 的方程**不读 `X` 所用的那个外生分量 `Ux`**
  —— 这条约束在草稿的定义里**根本不存在**。

  §3 的 `MBad` 就是这个缺口的数值见证：
  `X` 不读 `Uy`（故满足草稿的 `NoConfounding`），
  但 `Y` 读 `Uy`（与 `x` 无关，是纯 `Uy` 的函数），
  于是 `condY = P(X=x)·P(Y=y) = 1/4` 而 `doLaw = P(Y=y) = 1/2`。

  ## 3. ⭐ 草稿自称的 5 个定理与 §4.2/§5/§6 全部不存在

  **⚠ 这是必须如实登记的事实**：归档的 218 行文件在
  `MNC_marginalX` 的证明中途**被截断**（末行 `simp [MNC, eNC)` 括号不配对）。
  草稿模块文档承诺的以下**全部不存在**：

  | 承诺 | 实际 |
  |---|---|
  | §4.1 `MNC`（无混杂实例，`rule1` 成立）| 只有 `MNC`/`eNC`/`MNC_noConfounding`/`MNC_pU_sum`，`MNC_marginalX` **残缺** |
  | §4.2 `MCNC`（有混杂实例，`MCNC_rule1_fails`）| ❌ 不存在 |
  | §5 主定理 `rule1_no_confounding` | ❌ 不存在 |
  | §6 `rule1_naive_false` / `rule1_doLaw_mass` / `MBad`（反例！）| ❌ 全部不存在 |
  | 模块文档声称的「5 定理」| 只有 4 条 `def`/`theorem` 完整 |

  **⭐⭐ 反讽**：草稿的模块文档 §1 与 §4 表格**已经自己写对了答案**
  （「`T35.M` 与 `MBad` 都满足 `noConfounding`，却让 `condY = doLaw` 失败」），
  但它**从未把这些写下来**，反而在 §3 把主定理写成「无混杂 ⟹ 归一化相等」，
  而它的 `NoConfounding` 定义**推不出**这个结论。

  ## 4. 正确的替代（已在本仓库中）

  **`Fate/Rule1Semantic.lean`（在构建图中）** 给出了正确的精确化，
  且**不是**自欺式循环：

  ```lean
  def SCM.NoConfounding (M) : Prop :=
    ∀ x y, condY M x y = marginalX M x * doLaw M x y
  ```

  它以 `marginalX` 因子吸收「`condY` 是联合质量」这个归一化差异，
  并且：
  - `T35_not_noConfounding`：T3.5 的 `M` **不满足**它（真算 `0 ≠ 1/4`）；
  - `noConfounding_M1` / `noConfounding_M2`：两个具体 SCM **满足**它；
  - `noConfounding_iff_condProb_eq_doLaw_guarded`：**双向**证明它
    ⟺ `P(Y|X=x) = P(Y|do(X=x))`（在 `marginalX ≠ 0` 的守卫下）。

  **⟹ 本文件不重复那条路线**；它只登记──**草稿的版本为什么不行**。

  ## 5. 无 `sorry` / `axiom` / `native_decide` / 硬编码。

  **⚠ 一处刻意的技术选择**：`M.U` 由 `def` 包装时，`∑ u : M.U` 携带
  `M.instFintype`，与 `Fin 4` 的标准实例 **defeq 但不是同一个项**，
  导致 `Fintype.sum_prod_type` / `Finset.univ_product_univ` 的 `rw` 全部失败
  （这就是原草稿 7 个错误里 4 个的根因，见 §6）。**故本文件把反例的
  外生载体取 `Fin 4`**（原子类型，`rfl` 可直接贯通），
  两个外生坐标用 `u.val % 2`（`Ux`）与 `u.val / 2`（`Uy`）编码。

  ## 6. 原草稿的 7 个错误（逐条）

  | # | 位置 | 错误 | 原因 |
  |---|---|---|---|
  | 1 | `condY_unfold` | `rw [← e.sum_comp]` 失败 | `Equiv.sum_comp` 是 `∑ i, (f ∘ e) i = ∑ j, f j`；它**不**直接产生二重和，缺 `Fintype.sum_prod_type` 一步；且方向应为 `e.symm` |
  | 2 | `doLaw_unfold` | 同上 | 同上 |
  | 3 | `MNC_noConfounding` 第二项 | `simp [MNC, eNC]` 未解决 | 目标其实是 `x = x`（`rfl` 即可）；`simp` 在 `Equiv.refl` 的 `toFun` 上打转 |
  | 4 | `MNC_pU_sum` | `rw [Fintype.sum_prod_type]` 失败 | `MNC.instFintype` 与 `Prod.fintype` 不同项（见 §5 的技术说明） |
  | 5 | `MNC_marginalX` | 同上 + 截断 | 同上；且文件在此处**物理截断**（`eNC)` 括号错配） |
  | 6 | `MNC_marginalX` | `simp [MNC, eNC]` 未解决 | `Equiv.refl` 未归约 |
  | 7 | 文件末尾 | `unexpected token ')'` | **文件被截断**，非战术错误 |

  **⚠ 错误 #7 不是可以「修好」的错误**：文件在证明中途就结束了。
  即使把 1–6 全修好，草稿承诺的 §4.2/§5/§6 与主定理**仍然缺失**，
  而它们才是这份文件的全部数学内容。

  **⟹ 结论**：修好 6 个战术错误只会得到一个 4 定理的残缺文件，
  而**它要证的命题（按草稿的定义）是假的**。
  故本文件改为**反例登记**。
  ===========================================================================
-/

import FateWorld.Legacy.T35Confounding

namespace Fate.T35Rule1NoConfounding

open PearlHierarchy

/-! ## §1 草稿的 `NoConfounding` 定义（原样抄录） -/

/-- ⭐ **草稿（第 242 轮 G3）的「无混杂」定义，原样抄录**。

- 第 1 个合取项：`X` 的方程不读 `Uy` 分量；
- 第 2 个合取项：`(M.sg (e.symm (u, v))).2 = (M.sg (e.symm (u, v))).2`
  —— **左右是同一个项**。 -/
def NoConfoundingDraft {X Y : Type*} {Ux Uy : Type*}
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) : Prop :=
  (∀ (u : Ux) (v v' : Uy), (M.sg (e.symm (u, v))).1 = (M.sg (e.symm (u, v'))).1) ∧
  (∀ (u : Ux) (v : Uy), (M.sg (e.symm (u, v))).2 = (M.sg (e.symm (u, v))).2)

/-! ## §2 ⭐⭐⭐ 草稿的谓词是恒真的退化谓词

**这是整个反例的支点**：第 2 个合取项是 `rfl`。 -/

/-- ⭐⭐⭐ **草稿 `NoConfounding` 的第 2 个合取项恒真**：`fun _ _ => rfl`。

**⟹ 它对 `Y` 的方程施加零约束。** -/
theorem draft_second_conjunct_tautology {X Y Ux Uy : Type*}
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) :
    (∀ (u : Ux) (v : Uy), (M.sg (e.symm (u, v))).2 = (M.sg (e.symm (u, v))).2) :=
  fun _ _ => rfl

/-- ⭐⭐⭐ **故草稿的 `NoConfounding` 等价于「`X` 不读 `Uy`」**。

**⟹ 它对 `Y` 的方程零约束 ⟹ 推不出 `condY = doLaw`。** -/
theorem draft_NoConfounding_iff {X Y Ux Uy : Type*}
    (M : SCM X Y) (e : M.U ≃ Ux × Uy) :
    NoConfoundingDraft M e ↔
      (∀ (u : Ux) (v v' : Uy), (M.sg (e.symm (u, v))).1 = (M.sg (e.symm (u, v'))).1) :=
  ⟨fun h => h.1, fun h => ⟨h, draft_second_conjunct_tautology M e⟩⟩

/-! ## §3 ⭐⭐⭐⭐⭐ 反例 `MBad`

```
    ux ──→ X        uy ──→ Y
```

`U = Fin 4`，`u.val % 2` 编码 `Ux`、`u.val / 2` 编码 `Uy`，
`pU ≡ 1/4`。

- **`X = Ux`**（`u.val % 2`）：**不读 `Uy`** ⟹ 满足草稿的 `NoConfounding`；
- **`Y ≡ Uy`**（`u.val / 2`，**与 `x` 无关**）：**读 `Uy`**。

**⭐ 直觉**：`X` 与 `Y` 由**独立**的硬币驱动，故
`P(X=x, Y=y) = P(X=x)·P(Y=y)` ⟹ `condY = 1/4`；
而 `do(X:=x)` 不动 `Y` 的外生 ⟹ `doLaw = P(Y=y) = 1/2`。

**⚠ 注意这与 `T35.M`（完全混杂 `X = Y = U`）性质相反**：
`T35.M` 有混杂（`T35_not_noConfounding`），本 `MBad` **无混杂**，
但**两者都让 `condY ≠ doLaw`** —— 这正是「草稿谓词与结论无关」的证据。 -/

/-- ⭐⭐⭐ **反例 SCM**：`U = Fin 4`，`X = u.val % 2`，`Y ≡ u.val / 2`，`pU ≡ 1/4`。 -/
noncomputable def MBad : SCM (Fin 2) (Fin 2) where
  U := Fin 4
  pU := fun _ => (1 : ℝ) / 4
  sg := fun u => (if u.val % 2 = 0 then (0 : Fin 2) else 1,
                  fun _ => if u.val / 2 = 0 then (0 : Fin 2) else 1)

/-- 草稿所要求的外生坐标分解 `M.U ≃ Ux × Uy`（此处 `Ux = Uy = Fin 2`）。 -/
def eBad : MBad.U ≃ Fin 2 × Fin 2 where
  toFun u := (if u.val % 2 = 0 then 0 else 1, if u.val / 2 = 0 then 0 else 1)
  invFun p := ⟨p.2.val * 2 + p.1.val, by
    have h1 : p.2.val < 2 := p.2.isLt
    have h2 : p.1.val < 2 := p.1.isLt
    omega⟩
  left_inv u := by
    simp only
    have h : u.val < 4 := u.isLt
    apply Fin.ext
    simp only
    split <;> split <;> omega
  right_inv p := by
    simp only
    have h1 : p.2.val < 2 := p.2.isLt
    have h2 : p.1.val < 2 := p.1.isLt
    have key1 : (p.2.val * 2 + p.1.val) % 2 = p.1.val := by omega
    have key2 : (p.2.val * 2 + p.1.val) / 2 = p.2.val := by omega
    ext
    · simp only [key1]; split <;> omega
    · simp only [key2]; split <;> omega

/-- `eBad.symm (ux, uy)` 的 `val` 是 `uy.val * 2 + ux.val`。 -/
theorem eBad_symm_val (ux uy : Fin 2) :
    ((eBad.symm (ux, uy)) : Fin 4).val = uy.val * 2 + ux.val := by
  show (⟨uy.val * 2 + ux.val, _⟩ : Fin 4).val = uy.val * 2 + ux.val
  rfl

/-- ⭐⭐⭐⭐⭐ **`MBad` 满足草稿的 `NoConfounding`**。

**⭐ 证明的实质**：`X` 的分量是 `u.val % 2`，而
`eBad.symm (ux, uy)` 的 `val` 是 `uy.val * 2 + ux.val`，
故 `(uy.val * 2 + ux.val) % 2 = ux.val % 2` —— **与 `uy` 无关**。 -/
theorem MBad_noConfounding : NoConfoundingDraft MBad eBad := by
  rw [draft_NoConfounding_iff]
  intro ux uy uy'
  have h1 : ((eBad.symm (ux, uy)) : Fin 4).val % 2 = ux.val % 2 := by
    rw [eBad_symm_val]; omega
  have h2 : ((eBad.symm (ux, uy')) : Fin 4).val % 2 = ux.val % 2 := by
    rw [eBad_symm_val]; omega
  simp only [MBad]
  change (if ((eBad.symm (ux, uy)) : Fin 4).val % 2 = 0 then (0 : Fin 2) else 1)
    = (if ((eBad.symm (ux, uy')) : Fin 4).val % 2 = 0 then (0 : Fin 2) else 1)
  rw [h1, h2]

/-! ## §4 ⭐⭐⭐⭐⭐ 数值：两律不等

**⭐ 计算**（`x = y = 0`）：

$$\mathrm{condY}\,M_{\mathrm{Bad}}\,0\,0 = \sum_{u : \mathrm{Fin}\,4} \tfrac14
  \cdot [u\%2 = 0]\cdot[u/2 = 0] = \tfrac14,$$
$$\mathrm{doLaw}\,M_{\mathrm{Bad}}\,0\,0 = \sum_{u : \mathrm{Fin}\,4} \tfrac14
  \cdot [u/2 = 0] = \tfrac12.$$ -/

/-- ⭐⭐⭐ **观测律**：`condY MBad 0 0 = 1/4`（`X`、`Y` 独立，各 `1/2`）。 -/
theorem condY_MBad : SCMSemantics.condY MBad 0 0 = (1 : ℝ) / 4 := by
  have h1 : SCMSemantics.condY MBad (0 : Fin 2) (0 : Fin 2)
      = ∑ u : Fin 4,
          (1 / 4 : ℝ) * (if (if u.val % 2 = 0 then (0 : Fin 2) else 1) = 0 then 1 else 0)
            * (if (if u.val / 2 = 0 then (0 : Fin 2) else 1) = 0 then 1 else 0) := rfl
  rw [h1]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, if_true, zero_add]
  norm_num

/-- ⭐⭐⭐ **干预律**：`doLaw MBad 0 0 = 1/2`（`Y` 按 `Uy` 均匀）。 -/
theorem doLaw_MBad : SCMSemantics.doLaw MBad 0 0 = (1 : ℝ) / 2 := by
  have h1 : SCMSemantics.doLaw MBad (0 : Fin 2) (0 : Fin 2)
      = ∑ u : Fin 4,
          (1 / 4 : ℝ) * (if (if u.val / 2 = 0 then (0 : Fin 2) else 1) = 0 then 1 else 0) := rfl
  rw [h1]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Nat.reduceAdd, Nat.reduceDiv, if_true, zero_add]
  norm_num

/-- ⭐⭐⭐⭐⭐ **反例**：草稿的 `NoConfounding` 成立，**但**两律不等。

$$\textbf{NoConfounding}_{\text{draft}}(M_{\mathrm{Bad}}, e_{\mathrm{Bad}})
  \ \wedge\ \mathrm{condY}\,M_{\mathrm{Bad}}\,0\,0 \ne \mathrm{doLaw}\,M_{\mathrm{Bad}}\,0\,0.$$

**⟹ 草稿要证的 `rule1_no_confounding`（按草稿的定义）为假。** -/
theorem draft_rule1_false :
    NoConfoundingDraft MBad eBad ∧
      SCMSemantics.condY MBad 0 0 ≠ SCMSemantics.doLaw MBad 0 0 :=
  ⟨MBad_noConfounding, by rw [condY_MBad, doLaw_MBad]; norm_num⟩

/-- ⭐⭐⭐⭐⭐ **否定形式的登记**：不存在「草稿无混杂 ⟹ 两律处处相等」这一定理。

**⚠ 诚实说明**：这条定理的否定见证就是 `draft_rule1_false`。
它不是「命题在某个空洞前提下平凡成立」，而是
**反例的 `condY`/`doLaw` 是具体实数 `1/4` 与 `1/2`**。 -/
theorem draft_conclusion_not_derivable :
    ¬ ∀ x y : Fin 2,
        NoConfoundingDraft MBad eBad →
          SCMSemantics.condY MBad x y = SCMSemantics.doLaw MBad x y := by
  intro h
  exact draft_rule1_false.2 (h 0 0 draft_rule1_false.1)

/-! ## §5 ⭐ 反例不依赖 `T35.M`：两个方向都失败

**`MBad`**（`X = Ux`、`Y = Uy` 完全独立）满足草稿的谓词（已证），
**却仍让 `condY ≠ doLaw`**。
而 **`T35.M`**（完全混杂 `X = Y = U`）让两律不等（`Fate/T35Confounding.lean`
的 `t35_observational_ne_interventional`）。

**⚠ 精确说明**：`T35.M` 的 `U = Fin 2`，**不能**代入草稿的谓词
（`Fin 2 ≃ Ux × Uy` 需 `Ux × Uy` 恰有 2 元素；`T35.M` 的「混杂」是
`X` 与 `Y` 共用**同一个**外生坐标，草稿的分解形式无法表达它）。
**⟹ 下面只把 `T35.M` 用作「另一端的」对照，
不断言它满足草稿谓词。**

**⟹ 草稿的谓词与结论之间没有任何联系**：
它在 `MBad` 上成立而结论失败；
在 `T35.M` 上无法陈述，但结论同样失败。 -/

/-- ⭐ **`MBad` 与 `T35.M` 的对照**：前者 `X ⊥ Y`（外生独立），后者 `X = Y`。
**前者被草稿的谓词接受、却违反结论；后者无法代入该谓词、结论同样失败。** -/
theorem two_opposite_witnesses :
    -- 反例 1：完全独立
    (NoConfoundingDraft MBad eBad ∧
      SCMSemantics.condY MBad 0 0 ≠ SCMSemantics.doLaw MBad 0 0) ∧
    -- 反例 2：T35 的完全混杂（数值见 `Fate/T35Confounding.lean`）
    (SCMSemantics.condY Fate.T35.M 0 1 ≠ SCMSemantics.doLaw Fate.T35.M 0 1) :=
  ⟨draft_rule1_false, by
    rw [Fate.T35.condY_M, Fate.T35.doLaw_M]; norm_num⟩

end Fate.T35Rule1NoConfounding
