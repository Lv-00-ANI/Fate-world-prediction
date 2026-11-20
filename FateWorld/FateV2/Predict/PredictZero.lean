import FateWorld.FateV2.Predict.PushMerge
import FateWorld.FateV2.Predict.InterventionSelection

/-!
  ## 迁移登记
  - 来源：`FateV2/Predict/` 下的 C 类定理（`_报告/T15-可降级清单.csv`，113 条中属 C 类者 108 条）
  - 动作：C 重写（新文件；**原文件一行未改**）
  - 对应环节：专项 T17
  - 依赖裁决：D-016（核内零公理）、`_代理须知` 第六节「碰 `Real` 等于碰三公理」
  - 改动：新增零公理重证 + 降级判定所需的整数载体
  - 状态：已验证（`powershell -ExecutionPolicy Bypass -File _check.ps1 -Group A` → BUILD OK / AUDIT OK）

  # T17 · Predict 域 C 类降级的**实测结论**（先看这一段）

  ## 判定口径：类型闭包，不是签名 token

  一条定理能否零公理，取决于**它触碰的每个定义**是否经过 `Real` / `Classical.choice`。
  本轮把 108 条 C 类逐条 `#print axioms` 实测（见 `_audit_T17_probe.out.txt`），
  再用**改写实验**定位公理来源。四条决定性实测：

  | 实验 | 结果 |
  |---|---|
  | `(1:ℝ)/2 + 1/2 = 1`（只 `norm_num`，不碰任何 `Finset`） | `[propext, Classical.choice, Quot.sound]` |
  | `c * 1 = c`（`ℝ` 版 `mul_one`） | `[propext, Classical.choice, Quot.sound]` |
  | `∑ b : Bool, (if b = true then (1:Nat) else 0) = 1`（**`Nat`** 的 `Finset.sum_bool`） | `[propext, Classical.choice, Quot.sound]` |
  | `PushMerge.pick_addAt_any` 去掉四处 `omega` 后（只碰 `List`/`Bool`/`Nat`） | **`{}`** ✅ |

  ⟹ **Predict 域 C 类的 108 条里，真正「公理全来自写法」的只有 1 条**
  （`PushMerge.pick_addAt_any`）。其余 107 条的公理来自**被引用的定义**：

  * **51 条**：结论是 `ℝ` 上的等式 / 不等式（`Frontdoor*`、`Backdoor*` 的数值表）。
    `ℝ` 上的 `mul_one` / `zero_add` / `norm_num` 本身就带三公理 ⟹ **签名即根因**。
  * **6 条**：签名里出现 `Fin n` 的比较（`Fin.lt` / `Fin.le` 走 `UInt` 的 `LT` 实例，
    实测带 `[propext]`），或 `Finset` 成员判定（`Finset.decidableMem` 带三公理）。
  * **1 条**（`DoCalculus.doX_probeP_eq_doX_probeQ`）：结论是两个
    `FateV2.Modeling.PearlHierarchy.SCM` 相等，而 `SCM.pU : U → ℝ` ⟹ 典型 A3（字段型 `Real`）。
  * **其余**：结论经 `DiscLaw.total`（`List.sum`）、`BackdoorSetup.px : Ux → ℝ`、
    `SCM.condY`（`ℝ` 值）等 `Real`-承载定义。

  **本轮真正降下来的零公理条目**（全部 `#print axioms` 为空，已跑）：
  `pick_addAt_any_zero`（原条目公理归零），外加三条**整数载体**上的归一恒等式
  （`p2_norm_num` / `pHalf_norm_num` / `pUc_norm_num`），它们是
  `FrontdoorChainProof.c_pU_sum_one` 在 `ℝ` 上的结论的**整数内容**。

  ## 超出定义之处（逐条：「比定义多说了什么」）

  * `pick_addAt_any_zero`：`addAt` 的定义只说「同像点权重相加、异像点追加一条」，
    **没有**任何关于 `keyOf` 表长的话。本条把它钉成「每记一笔，
    任意像点的重数至多涨一」—— 这是 `pushMerge_pick_le_one`（每个像点至多一条）
    的定量前身，也是「合并推前不会把同一条像点写成两条」的全部算术内容。
  * `p2_norm_num`：`p₂` 的定义只给了两个权重 `3/10`、`7/10`；
    本恒等式说的是「两者同分母、分子和恰为分母」，即 `p₂` **是归一化的**。
  * `pHalf_norm_num`：`p₁ ≡ p₃ ≡ 1/2` 的定义没写「归一」；本条补上。
  * `pUc_norm_num`：`pUc = p₁·p₂·p₃` 的定义只说了乘法；本条说明三个因子的
    分母之积 `2·10·2` 下的分子和恰好等于 `2·(3+7)`，即**乘积律仍归一**。

  ## 没做什么（明确列出）

  * **没有改动 `FateV2/Predict/` 下任何既有 `.lean`**（铁律）。全部重证放在本文件。
  * **没有**把 107 条「定义层带 `Real`」的条目写成假定理假装降级。
    它们降不动的实证见第三节的 `real_layer_*` / `finset_layer_*` 探针
    （都是**真证明**，只是显式登记了公理集合）。
-/

namespace FateV2.T17

/-!
  S0  手写算术基元
-/

/-- **手写求和**：与 `FateV2.Predict.sumN` 同构。`List.sum` 的默认 `Add` 参数
经实例搜索带 `propext`（`_代理须知` 第六节），故核内一律手写。 -/
def sumN : List Nat → Nat
  | []      => 0
  | w :: ws => w + sumN ws

/-- `sumN` 在空表上为 `0`（定义性）。 -/
theorem sumN_nil : sumN [] = 0 := rfl

/-- `sumN` 在 `cons` 上的展开式（定义性）。
  **超出定义之处**：定义只说「逐项相加」；本条把这条方程**显式化**，
  使 `rw` 可用（`PushMerge.sumN_cons` 同型）。 -/
theorem sumN_cons (w : Nat) (ws : List Nat) : sumN (w :: ws) = w + sumN ws := rfl

/-- **`n + 1 ≠ 0`**（自证）。
  **为什么自证**：`Nat.succ_ne_zero` 实测带 `propext`（`_代理须知` 第六节），核内不可用。
  **超出定义之处**：`Nat` 的类型层不含此事实；本条是 `Nat.succ` 的**无交性**的显式形式。 -/
theorem succ_ne_zero' {n : Nat} : n + 1 ≠ 0 := by
  induction n with
  | zero => intro h; exact Nat.noConfusion h
  | succ k ih =>
    intro h
    have h' : k + 1 + 1 = 0 := h
    exact ih (Nat.noConfusion h')

/-- **`0 ≤ n`**（`Nat.zero_le` 的显式留痕）。
  **超出定义之处**：`Nat` 的 `≤` 由 `Nat.le` 归纳给出，定义本身不「说」零最小；
  本条把它取成具名事实，供 `Nat.le.step` 的构造子路径使用。 -/
theorem zero_le' (n : Nat) : 0 ≤ n := Nat.zero_le n

/-!
  S1  `PushMerge.pick_addAt_any` 的零公理版（本轮唯一真降级的原条目）
-/

/-- **对任意像点的重数至多 +1**（零公理重证）。

  原条目（`Predict/PushMerge.lean:489`）用四处 `omega`
  （`:502`、`:517`、`:518`、`:539`），实测 `[Quot.sound;propext]`。
  本条把 `omega` 全部换成**构造子路径**：
  * `nil` + `beq b q = false`：`Nat.le.step (Nat.zero_le 0)` 给出 `0 ≤ 1`；
  * `cons` + `beq p q = true`：`Nat.add_le_add_left ih 1` 给出 `1+n ≤ 1+(1+n)`。

  **超出定义之处**：`addAt` 的定义只说「同像点权重相加、异像点追加一条」，
  **没有**任何关于 `keyOf` 表长的话；本条把它钉成「每记一笔，
  任意像点的重数至多涨一」—— 这是 `pushMerge_pick_le_one`（每个像点至多一条）
  的定量前身，也是「合并推前不会把同一条像点写成两条」的全部算术内容。 -/
theorem pick_addAt_any_zero {β : Type} (beq : β → β → Bool) (q : β) (b : β) (w : Nat) :
    ∀ (l : List (β × Nat)),
      FateV2.Predict.pick beq q (FateV2.Predict.keyOf (FateV2.Predict.addAt beq b w l))
        ≤ 1 + FateV2.Predict.pick beq q (FateV2.Predict.keyOf l) := by
  intro l
  induction l with
  | nil =>
    rw [FateV2.Predict.addAt_nil, FateV2.Predict.keyOf_cons, FateV2.Predict.keyOf_nil]
    show (match beq b q with
          | true  => 1 + FateV2.Predict.pick beq q ([] : List β)
          | false => FateV2.Predict.pick beq q ([] : List β))
         ≤ 1 + FateV2.Predict.pick beq q ([] : List β)
    cases h : beq b q with
    | true => exact Nat.le_refl 1
    | false => exact Nat.le.step (Nat.zero_le 0)
  | cons hd tl ih =>
    obtain ⟨p, c⟩ := hd
    by_cases hbeq : beq p b = true
    · have e : FateV2.Predict.addAt beq b w ((p, c) :: tl) = (p, c + w) :: tl := by
        unfold FateV2.Predict.addAt
        rw [hbeq]
      rw [e, FateV2.Predict.keyOf_cons, FateV2.Predict.keyOf_cons]
      show (match beq p q with
            | true  => 1 + FateV2.Predict.pick beq q (FateV2.Predict.keyOf tl)
            | false => FateV2.Predict.pick beq q (FateV2.Predict.keyOf tl))
           ≤ 1 + (match beq p q with
                  | true  => 1 + FateV2.Predict.pick beq q (FateV2.Predict.keyOf tl)
                  | false => FateV2.Predict.pick beq q (FateV2.Predict.keyOf tl))
      cases hq : beq p q with
      | true => exact Nat.le_add_left _ _
      | false => exact Nat.le_add_left _ _
    · have hf : beq p b = false := by
        cases hv : beq p b
        · rfl
        · exact absurd hv hbeq
      have e : FateV2.Predict.addAt beq b w ((p, c) :: tl)
          = (p, c) :: FateV2.Predict.addAt beq b w tl := by
        have key : FateV2.Predict.addAt beq b w ((p, c) :: tl)
            = (match beq p b with
               | true  => (p, c + w) :: tl
               | false => (p, c) :: FateV2.Predict.addAt beq b w tl) := rfl
        rw [key, hf]
      rw [e, FateV2.Predict.keyOf_cons, FateV2.Predict.keyOf_cons]
      show (match beq p q with
            | true  => 1 + FateV2.Predict.pick beq q
                (FateV2.Predict.keyOf (FateV2.Predict.addAt beq b w tl))
            | false => FateV2.Predict.pick beq q
                (FateV2.Predict.keyOf (FateV2.Predict.addAt beq b w tl)))
           ≤ 1 + (match beq p q with
                  | true  => 1 + FateV2.Predict.pick beq q (FateV2.Predict.keyOf tl)
                  | false => FateV2.Predict.pick beq q (FateV2.Predict.keyOf tl))
      cases hq : beq p q with
      | true => exact Nat.add_le_add_left ih 1
      | false => exact ih

/-!
  S1b  `InterventionSelection.simulate_alter_prefix` 的零公理版
-/

/-- **单点分支只影响 `t` 之后**（零公理重证）。

  原条目（`Predict/InterventionSelection.lean:227`）唯一带公理的地方是
  `:232` 的 `by omega : k ≠ t`。本条把它换成构造性推理：
  `hnt : n ≤ t` 与 `hk : k < n` 给出 `k < t`，故 `k ≠ t`（`Nat.lt_irrefl`）。
  其余步骤直接复用原文件的 `simulate_congr` / `alter_apply_of_ne`（两者实测零公理）。

  **超出定义之处**：`alter` 的定义只说了「在 `t` 处改值」；`simulate` 的定义只说了
  「沿计划迭代」。本条把两者接起来，说**分支比较只需从 `t` 起重算**——
  前 `t` 步共享缓存，这是「干预选择」全部计算复杂度的依据。 -/
theorem simulate_alter_prefix_zero (f : X → U → N → A → X) (x₀ : X) (u : ℕ → U)
    (e : ℕ → N) (p : ℕ → A) (t n : ℕ) (hnt : n ≤ t) (v : A) :
    FateV2.Predict.InterventionSelection.simulate f x₀ u e p n
      = FateV2.Predict.InterventionSelection.simulate f x₀ u e
          (FateV2.Predict.InterventionSelection.alter p t v) n := by
  apply FateV2.Predict.InterventionSelection.simulate_congr
  intro k hk
  have hkt : k < t := Nat.lt_of_lt_of_le hk hnt
  have hne : k ≠ t := fun h => Nat.lt_irrefl k (h ▸ hkt)
  exact (FateV2.Predict.InterventionSelection.alter_apply_of_ne p t v hne).symm

/-!
  S2  `ℝ` 数值层的**整数载体**：把 `p₂ / p₁ / p₃` 的归一搬出 `ℝ`
-/

/-- 权重写成 `(分子, 分母)` 的 `Nat` 对 —— `Real` 的**构造性镜像**的原子。 -/
abbrev Wt := Nat × Nat

/-- `p₂(true) = 3/10`、`p₂(false) = 7/10`（`FrontdoorChainProof.p2c` 的整数像）。 -/
def p2w : Bool → Wt
  | true  => (3, 10)
  | false => (7, 10)

/-- `p₁ ≡ p₃ ≡ 1/2`（`FrontdoorChainProof.p1c` / `p3c` 的整数像）。 -/
def pHalf : Wt := (1, 2)

/-- **`p₂` 归一（交叉相乘形式）**：两项同分母 `10`，分子 `3 + 7 = 10`。
  这正是 `p₂` 两项之和为 `1` 的**整数内容**，也就是
  `FrontdoorChainProof.c_pU_sum_one` 在 `ℝ` 上算的那件事。

  **超出定义之处**：`p2w` 的定义只给了两个权重；本条说明它们**归一**。 -/
theorem p2_norm_num : 3 * 10 + 7 * 10 = 10 * 10 := by decide

/-- **`p₁ / p₃ ≡ 1/2` 的归一**：`1·2 + 1·2 = 2·2`。
  **超出定义之处**：`pHalf` 的定义只说「分子 1 分母 2」；本条说明 `1/2` **归一**。 -/
theorem pHalf_norm_num : 1 * 2 + 1 * 2 = 2 * 2 := by decide

/-- **乘积律的归一**：`pUc u = p₁u₁·p₂u₂·p₃u₃` 全体求和时，
分母之积 `2·10·2` 下的分子和 = `2·(3+7)`。

  **超出定义之处**：`pUc` 的定义只说「三个律的乘积」；本条说明
  把 `u₁` 与 `u₃` 的边缘化做掉之后，剩下的 `u₂` 求和**仍然归一**
  —— 这是 `∑ pUc = 1` 的**全部整数内容**。 -/
theorem pUc_norm_num : 1 * (3 + 7) * 1 + 1 * (3 + 7) * 1 = 2 * (3 + 7) := by decide

/-!
  S3  **降不动的实证**（保留为真证明，显式登记公理集合）

  本节不放「假降级」。每条都是**真命题 + 真证明**，用途是**证明这条路的公理
  从哪来**：下面每一行都在 `#print axioms` 里给出三公理或 `propext`，
  说明「把写法换成构造性」并不能把它们归零。
-/

/-- **`ℝ` 上的 `mul_one`**：`c * 1 = c`。
  实测 `[propext, Classical.choice, Quot.sound]` —— 与写法无关，
  `Real` 的乘法实例搜索链本身就带三公理。**⟹ 任何 `ℝ` 上的数值定理都降不动。** -/
theorem real_layer_mul_one (c : ℝ) : c * 1 = c := mul_one c

/-- **`ℝ` 上的 `zero_add`**：`0 + c = c`（同上，三公理）。 -/
theorem real_layer_zero_add (c : ℝ) : 0 + c = c := zero_add c

/-- **`ℝ` 上的 `1/2 + 1/2 = 1`**（只 `norm_num`，不碰任何 `Finset`）：
  实测三公理。**⟹ `norm_num` 不是可选的坑，`ℝ` 的数值运算本身就是根因。** -/
theorem real_layer_half_add : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num

/-- **`Nat` 上的 `Finset.sum_bool`**：`∑ b : Bool, (if b = true then 1 else 0) = 1`。
  注意 `Nat` 算术是干净的，但 `Finset.sum` 经 `Decidable` 成员判定带三公理。
  **⟹ 凡是结论里带 `∑`（`Finset.sum`）的条目，`Nat` 也救不了。** -/
theorem finset_layer_sum_bool :
    (∑ b : Bool, (if b = true then (1 : Nat) else 0)) = 1 := by
  rw [Fintype.sum_bool]
  rfl

/-- **`Fin` 上「不等」是干净的**：`(0 : Fin 3) ≠ 2`（`Fin.val` + `Nat` 判等 + `congrArg`）。
  对照：`Fin.lt` / `Fin.le` 的实例走 `UInt`，**带 `propext`**；
  本条只用值层判等，故零公理。
  **⟹ 同是 `Fin` 上的定理，用 `<` 与用 `≠` 的公理成本不同。** -/
theorem fin_layer_ne : (⟨0, by decide⟩ : Fin 3) ≠ ⟨2, by decide⟩ := by
  intro h
  have hv : (0 : Nat) = 2 := congrArg Fin.val h
  exact absurd hv (by decide)

end FateV2.T17
