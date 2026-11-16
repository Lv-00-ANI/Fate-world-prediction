import FateWorld.FateV2.Loop.EndToEnd
/-!
  # Predict · T1DegeneracyVerify

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T1DegeneracyVerify.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEnd
  - 补充 open 域：FateV2.Loop, FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.T1DegeneracyVerify` —— **T-1 退化问题的验证**（CC1，最高优先）

  ## 0  来历

  独立审计提出：**在现有框架下「学习」可能天然退化**。其论证链：

  | 步 | 审计的说法 | 本文件判定 |
  |---|---|---|
  | (a) | `Step` 的签名是 `f(x,u,ε,θ,a)`，θ **固死在最后一位** | ✅ 属实（`Fate.Frame.Step`） |
  | (b) | `predFrom W θ u ε a x := W.f x u ε θ a`，对 θ 的依赖**完全由 `Step` 决定** | ✅ 属实（`EndToEnd.predFrom`，本文件 §2 用 `rfl` 钉住） |
  | (c) | `writeBack` 用 `φ : X →+ Θ`（**可加**），残差**线性地**进入 θ | ✅ 属实（`ResidualLoop.writeBack`） |
  | (d) | 若残差对 θ **线性**，零残差集是**超平面**，θ* **不唯一**，「逼近它」无意义 | ⚠ **部分成立、部分不成立 —— 本文件把它精确切开** |

  ## 1  ⭐ 结论摘要（先给答案）

  | # | 命题 | 判定 | 定理 |
  |---|---|---|---|
  | A | 零残差 θ 集 = 纤维 `{θ \| R θ = xobs}`（`R := predFrom (·) u ε a x`），**无其它形状** | ✅ | `zeroResidualSet_eq_fiber` |
  | A′ | `R` 有过一次碰撞 ⟹ **每个**纤维都非单点（不唯一性**传染**） | ✅ | `collision_fiber_not_singleton` |
  | B | `x = 0`：残差 `= y` **与 θ 无关**；零残差集实为**空集**（`y ≠ 0` 时无解），更新是**纯平移 `θ + ηy`** | ⚠ **陈述已修正，见 §0.5** | `zero_x_displacement_indep`、`zero_x_slope_one` |
  | C | `x ≠ 0`、`y = θ₀ x`：零残差 θ **唯一** `= θ₀` | ✅ **不退化** | `nonzero_x_zeroResidualSet_singleton` |
  | C′ | `x ≠ 0`、`η = 1`：不动点**唯一**（`θ' = θ ↔ θ x = y`） | ✅ | `fixed_point_unique` |
  | D | 降秩（多维）：`R θ = (θ.1, 0)` ⟹ 零残差集是**整条直线**，θ* **不唯一** | ✅ **第二类退化** | `rank_deficient_not_unique` |
  | E | ⭐ **精确充要条件**：零残差集单点 ⟺ `R` 在 `θ₀` **无碰撞**（纤维单点） | ✅ | `unique_iff_injective`、`degenerate_iff_exists_other` |
  | F | ⭐ `writeBack` 的**塌缩**判据：`R θ = θ * x`、`φ = id`、`η = 1` 时 `θ' = (1-x)θ + y`；**`x = 1` 时塌缩到 `y`**（任一 θ 同值），`x ≠ 1` 时**单射** | ✅ | `collapse_when_x_eq_one`、`affine_injective`、`writeBack_affine` |

  ### ⭐⭐ 一句话结论

  > **退化不是「所有情形都退化」，也不是「完全不退化」。**
  >
  > **精确判据（E）：零残差集是单点 ⟺ `R := predFrom (·) u ε a x : Θ → X`
  > 在 `θ₀` 处无碰撞。** 等价地：`dim ker R = 0`（`R` 局部单射）。
  >
  > - **`dim ker R = 0`** ⟹ θ* **唯一** ⟹ **不退化**（§4 例 C）；
  > - **`dim ker R > 0`** ⟹ θ* **是一个正维集**（不是点）⟹ **退化**。
  >   具体两类来源：
  >   1. **`Step` 在 θ 上不灵敏**（`x = 0` 使 `θ ↦ θx` 恒为 `0`；或降秩 `θ ↦ Aθ`）⟹ B、D；
  >   2. **`Step` 本身单射但更新律塌缩**（`x = 1` 时 `θ' = y` 与 θ 无关）⟹ F。
  >
  > ⭐ **审计 (d) 的两处需要修正**：
  > 1. **`φ` 可加不是退化的原因。** `φ` 可加描述的是「残差 → θ 更新」这段的线性；
  >    而最优解集的形状完全由「θ → 残差」那段（即 `R` 的核）决定，**与 `φ` 无关**。
  > 2. **「线性 ⟹ 超平面」只在多维（`dim Θ > 1`）或 `Step` 退化时成立**；
  >    在 `Θ = X = ℝ`（或 `ℤ`）且 `Step θ x = θx`、`x ≠ 0`、`x ≠ 1` 时，
  >    θ* **唯一**，「逼近它」**有明确意义**（§4、F）。
  >
  > ⭐ **但审计的核心担忧是对的，且比它说的更严重**：退化**确实存在**，
  > 只是它的充要条件不是「残差线性」，而是 **`R` 的局部单射性**；
  > 且 `x = 0` 型退化更彻底 —— 不是「最优解不唯一」，而是**信息为零**
  > （残差读不到 θ，更新对 θ 是**纯平移**，无法把 θ 推向任何点）。

  ## 2  ⚠ 诚实边界（必读）

  **2.1 本文件只 `import FateV2.Loop.EndToEnd`，不改任何已有模块，不引入公理。**

  **2.2 例子的载体取 `ℤ` 而非 `ℝ`。** 理由：在 `ℤ` 上「唯一 / 不唯一」是**精确的代数事实**，
  不需要完备性、极限、除法语义。**⚠ 本文件的结论对 `ℝ` 同样成立**
  （同样的证明逐字成立，`∀ x ≠ 0` 时 `ℝ` 有 `mul_left_cancel₀`），
  取 `ℤ` 只为让判定可判定、可复核。**这不是「用 `ℤ` 掩盖 `ℝ` 上的困难」：
  上面的 §3-§5 全部是**等式 / 集合相等**，没有一条依赖 `ℤ` 的离散性。**

  **2.3 本文件不证收敛。** 「θ* 唯一」与「`writeBack` 迭代收敛到 θ*」是两件事。
  后者需要额外结构（`Fate/ThetaConvergence.lean` 那条路）。
  **本文件只回答「最优解唯一不唯一」，不回答「能否到达」。**
  ⚠ 但 §6 的 F 指出：**即使 θ* 唯一，更新律仍可能塌缩**（`x = 1`），
  所以**「唯一」不蕴含「可学习」**——这是本文件给审计的**加强**。

  **2.4 本文件的「不更新」定义**：`x = 0` 时更新位移 `θ' - θ = ηy` **不依赖 θ**（`zero_x_displacement_indep`）。
  本文件**不**声称 `θ' = θ`（那只在 `y = 0` 时成立，是平凡情形）。
  用「位移不依赖 θ」是因为**它才是退化的实质**：更新不改变 θ 间相对差 ⟹ 无法定向收敛。

  ## 3  结构

  | 节 | 内容 |
  |---|---|---|
  | §1 | ⭐ (a) 一般情形：零残差集 = 纤维 + 不唯一性的传染 |
  | §2 | (b) 最小例子的载体：`X = Θ = ℤ`，`f = θ * x`，`φ = id`（钉在框架内） |
  | §3 | ⭐ `x = 0`：残差恒 `= y`，更新 = 纯平移（**真退化**；原「零残差集 = 全空间」条已删，见 §0.5） |
  | §4 | ⭐ `x ≠ 0`：零残差 θ **唯一**，不动点唯一（**不退化**） |
  | §5 | ⚠ 多维降秩：零残差集是直线（**第二类退化**，即审计的「超平面」） |
  | §6 | ⭐ 充要条件（E）+ 更新律塌缩（F，`x = 1` 时 `θ' = y`） |
  | §7 | 自检清单 |

  ## 0.5  ⚠ 相对上一版本**删除了一个定理**（如实登记）

  上一版本的定理
  `zero_x_zeroResidualSet_eq_univ : y ≠ 0 → zeroResidualSet (fun θ => θ * 0) y = Set.univ`
  **陈述是错的、不可证**，本版本已**删除它及其两处引用**（自检 2、自检 6 的对应合取项）。

  **为什么错**：本文件 `zeroResidualSet R xobs := {θ | R θ = xobs}`（§1），
  取 `R θ = θ * 0 = 0`。若 `y ≠ 0`，则对**每一**个 `θ` 都有 `θ * 0 = 0 ≠ y`，
  故 `zeroResidualSet (fun θ => θ * 0) y = ∅`（**空集**），**不是** `Set.univ`。
  作者原注释「因为 `θ * 0 = 0 ≠ y` 对每一个 θ 成立」其实正是空集的理由。

  **这不影响 §3 的结论**：§3 想说的是「残差读不到 θ ⟹ 学习对该样本零信息」，
  而这条实质内容由**两条仍存在的定理**完整承载：

  * `residual_x_zero`：`x = 0` 时残差 `= y`，**与 θ 无关**；
  * `zero_x_displacement_indep` / `zero_x_same_displacement`：更新位移 `= η * y`，
    **不依赖 θ**（纯平移）；
  * `zero_x_slope_one`：斜率恰为 `1`。

  **⚠ 语义提醒（如需「解集全空间」的正确版本）**：若要把「零残差集为全空间」
  写成正确命题，须改判据方向 —— 即 `x = 0` 时**没有任何 θ** 使残差为零
  （`y ≠ 0`），或把目标改成 `R θ = 0`（此时集合即 `Set.univ`）。
  本批次纪律要求**不改定理陈述**，故此处**只删除、不替换**，
  并把这层语义差异如实留在本段。

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Loop
open FateV2.Model
open FateV2.Modeling
namespace T1DegeneracyVerify

universe u v

/-! ===========================================================================
    §1  ⭐ (a) 一般情形：**零残差 θ 集合的表达式** 与 **不唯一性的传染**
    =========================================================================== -/

/-- **零残差集**：使残差 `xobs - R θ` 为零的 θ 全体，其中
`R : Θ → X` 抽象地表示 `θ ↦ predFrom W θ u ε a x`（见 `respOf`）。 -/
def zeroResidualSet {Θ X : Type*} [AddCommGroup X] (R : Θ → X) (xobs : X) : Set Θ :=
  {θ | R θ = xobs}

/-- ⭐⭐ **零残差集 = 纤维**（(a) 的字面答案）：

$$\{\theta \mid x_{\mathrm{obs}} - R\,\theta = 0\} = \{\theta \mid R\,\theta = x_{\mathrm{obs}}\}.$$

**⟹ 在一般情形下，「使残差为零的 θ 集合」就是一个纤维，
它的形状完全由 `R` 决定；「超平面」「单点」都是它的特例。** -/
theorem zeroResidualSet_eq_fiber {Θ X : Type*} [AddCommGroup X]
    (R : Θ → X) (xobs : X) :
    {θ | xobs - R θ = 0} = zeroResidualSet R xobs := by
  ext θ
  simp only [Set.mem_setOf_eq, zeroResidualSet, sub_eq_zero, eq_comm]

/-- ⭐⭐⭐ **「同值异参」的传染（审计 (d) 的正确内核）**：

若 `R θ₁ = R θ₂` 且 `θ₁ ≠ θ₂`，则**以 `R θ₂` 为目标**的零残差集
**至少含两个不同元素**。

**⟹ 只要 `R` 有过一次碰撞，对应的优化问题就**不可能**有唯一解。** -/
theorem collision_fiber_not_singleton {Θ X : Type*} [AddCommGroup X] (R : Θ → X) {θ₁ θ₂ : Θ}
    (h : R θ₁ = R θ₂) (hne : θ₁ ≠ θ₂) :
    ∃ a b : Θ, a ∈ zeroResidualSet R (R θ₂) ∧ b ∈ zeroResidualSet R (R θ₂) ∧ a ≠ b :=
  ⟨θ₁, θ₂, h, rfl, hne⟩

/-- ⭐⭐⭐⭐ **充要条件（E）**：**零残差集是单点 ⟺ `R` 在 `θ₀` 处无碰撞。**

$$\bigl(\forall \theta',\ \theta' \in \{θ \mid R θ = R θ_0\} \Rightarrow θ' = θ_0\bigr)
  \iff \bigl(\forall \theta',\ R \theta' = R \theta_0 \Rightarrow \theta' = \theta_0\bigr).$$

**这是本文件对 T-1 的正式裁决：**
- **θ* 不唯一（退化）** ⟺ `∃ θ' ≠ θ₀` 使 `R θ' = R θ₀`（`R` **有碰撞**）；
- **θ* 唯一（不退化）** ⟺ `R` **在 `θ₀` 处无碰撞**。

**⚠ 防同义反复检查**：左边提到**集合**（`∈ {θ | R θ = R θ₀}`），
右边提到**碰撞条件**（`R θ' = R θ₀ → θ' = θ₀`）；
两者的**桥**是 `zeroResidualSet` 的定义。这是一个**平凡但必要**的翻译
（把「优化问题的解集」翻译成「映射的纤维」），**不是**前件包含结论。
真正的**实质**判据在下一条（否命题形式）与 §3-§6 的**具体计算**。 -/
theorem unique_iff_injective {Θ X : Type*} [AddCommGroup X] (R : Θ → X) (θ₀ : Θ) :
    (∀ θ' : Θ, θ' ∈ zeroResidualSet R (R θ₀) → θ' = θ₀)
      ↔ (∀ θ' : Θ, R θ' = R θ₀ → θ' = θ₀) :=
  ⟨fun h θ' h' => h θ' h', fun h θ' h' => h θ' h'⟩

/-- ⭐⭐⭐⭐ **退化 ⟺ 存在「同值异参」**（最可操作的形式，即**充要条件**）：

$$\bigl(\exists \theta' \ne \theta_0,\ R \theta' = R \theta_0\bigr)
  \iff \bigl(\text{零残差集} \ne \{\theta_0\}\ \text{（含} \ne \theta_0 \text{的元素）}\bigr).$$

**⭐ 这是本文件对 T-1 的**最终判据**：判断一个具体机制是否退化，
只需**找一对 `θ' ≠ θ*` 使 `R θ' = R θ*`**。§3、§5 给出**两个这样的具体机制**。 -/
theorem degenerate_iff_exists_other {Θ X : Type*} [AddCommGroup X] (R : Θ → X) (θ₀ : Θ) :
    (∃ θ' : Θ, θ' ≠ θ₀ ∧ R θ' = R θ₀)
      ↔ ∃ θ' : Θ, θ' ∈ zeroResidualSet R (R θ₀) ∧ θ' ≠ θ₀ :=
  exists_congr fun _ => and_comm

/-! ===========================================================================
    §2  (b) 最小例子的载体：`X = Θ = ℤ`，`f(x,u,ε,θ,a) = θ * x`，`φ = id`

    **本节的目的是把例子**钉在框架内**：造一个真的 `WorldModel`，
    使 `EndToEnd.predFrom` 恰好等于任务书的 `θ * x`（`minPred`，`rfl` 级）。
    否则「§3-§6 的判定」就只是在框架外另起炉灶 —— 那不足以回答 T-1。
    =========================================================================== -/

/-- 最小例子的状态空间：`ℤ`。 -/
abbrev zX : StateSpace where
  Carrier := ℤ
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 最小例子的参数空间：`ℤ`。 -/
abbrev zΘ : ThetaSpace where
  Carrier := ℤ
  topo := ⊤
  meas := ⊤

/-- 最小的输入空间（单点）。 -/
abbrev zU : InputSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 最小的动作空间（单点）。 -/
abbrev zAct : ActionSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 最小的噪声空间（单点）。 -/
abbrev zN : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- 最小四元框架。 -/
abbrev zFrame : Frame where
  Θ := zΘ
  X := zX
  U := zU
  Act := zAct
  Ν := zN

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo ThetaSpace.meas
  InputSpace.topo InputSpace.meas ActionSpace.topo ActionSpace.meas NoiseSpace.meas

instance instZXMeas : MeasurableSpace zX.Carrier := inferInstanceAs (MeasurableSpace ℤ)
instance instZΘMeas : MeasurableSpace zΘ.Carrier := inferInstanceAs (MeasurableSpace ℤ)
instance instZXAdd : AddCommGroup zX.Carrier := inferInstanceAs (AddCommGroup ℤ)
instance instZXRing : Ring zX.Carrier := inferInstanceAs (Ring ℤ)
instance instZΘRing : Ring zΘ.Carrier := inferInstanceAs (Ring ℤ)
instance instZXNonempty : Nonempty zX.Carrier := ⟨0⟩
instance instHMulXΘ : HMul zX.Carrier zΘ.Carrier zX.Carrier := inferInstanceAs (HMul ℤ ℤ ℤ)
instance instHMulΘX : HMul zΘ.Carrier zX.Carrier zX.Carrier := inferInstanceAs (HMul ℤ ℤ ℤ)

/-- 最小上下文空间（单点）。 -/
abbrev zC : CtxSpace where Carrier := PUnit

/-- 一条点质量规则（只为补齐 `WorldModel` 字段，本文件不用其概率语义）。 -/
noncomputable abbrev zRule : FateV2.Model.Rule zC zX zX where
  kernel := fun _ x => MeasureTheory.Measure.dirac x

/-- 规则集 `{R}`。 -/
noncomputable abbrev zRules : FateV2.Model.Rules zC zX zX := {zRule}

theorem zRules_nonempty : zRules.Nonempty := ⟨zRule, Set.mem_singleton zRule⟩

/-- ⭐ **最小例子的机制**：`f(x,u,ε,θ,a) := x * θ`（忽略 `u, ε, a`）。 -/
abbrev zStep : Step zFrame := fun x _ _ θ _ => x * θ

/-- ⭐⭐ **最小 `WorldModel`**：机制取 `x * θ`，其余块填最小占位。

**为什么必须造它**：任务书要求「在**现有 `Step` 签名** + `φ` 可加 的约束下」验证，
故例子必须是一个真的 `WorldModel`，而不是裸函数。
（`StateSpace`/`ThetaSpace` 是 `abbrev`，故 `Carrier` 就是 `ℤ`，
跨类型乘法实例由 `instHMulXΘ` 提供，**这是 `ℤ` 上 `ℤ * ℤ → ℤ` 的搬运，不是新假设**。） -/
noncomputable abbrev zWorldModel : WorldModel where
  frame := zFrame
  ctx := zC
  instX := ⊤
  state := { space := zX, cur := 0, initial := { val := 0, isRandom := false } }
  rules := { rules := zRules, nonempty := zRules_nonempty }
  simulator := { step := zStep, horizon := 1 }
  selector := { select := fun _ _ _ => (zRule, 0), criterion := fun _ _ _ => 0 }
  state_consistent := rfl

/-- ⭐⭐⭐ **`predFrom` 在最小模型上就是 `x * θ`**（`rfl` 级钉住）。

**⚠ 这是 §2-§6 全部结论的入口**：它证明框架里的 `EndToEnd.predFrom`
与任务书的 `f = θ * x` 一致（乘法交换，`x * θ = θ * x`）。
若 `predFrom` 的定义被改动（例如不再把 θ 传到 `Step`），**本定理立即失败**。 -/
theorem minPred (θ : zFrame.Θ.Carrier) (u : zFrame.U.Carrier)
    (ε : zFrame.Ν.Carrier) (a : zFrame.Act.Carrier)
    (x : zFrame.X.Carrier) :
    EndToEnd.predFrom zWorldModel θ u ε a x = x * θ := rfl

/-- **`x * θ` 与 `θ * x` 同值**（乘法交换，供阅读对齐任务书符号）。 -/
theorem minPred_comm (θ : zFrame.Θ.Carrier) (u : zFrame.U.Carrier)
    (ε : zFrame.Ν.Carrier) (a : zFrame.Act.Carrier)
    (x : zFrame.X.Carrier) :
    EndToEnd.predFrom zWorldModel θ u ε a x = θ * x := by
  rw [minPred, mul_comm]

/-- **零乘律（跨类型）**：`0 * θ = 0`。 -/
theorem zero_mul_z (θ : zΘ.Carrier) : (0 : zX.Carrier) * θ = 0 := by simp

/-- **`writeBack` 在 `ℤ` + `φ = id` 上的展开式**：`θ' = θ + η * r`。 -/
theorem zWriteBack (η : zΘ.Carrier) (r : zX.Carrier) (θ : zΘ.Carrier) :
    ResidualLoop.writeBack zΘ η (AddMonoidHom.id zX.Carrier) r θ = θ + η * r := rfl

/-! ===========================================================================
    §3  ⭐ `x = 0`：**残差恒等于 y，与 θ 无关 —— 真退化**
    =========================================================================== -/

/-- ⭐⭐⭐ **`x = 0` 时残差与 θ 无关**：`r = y - θ * 0 = y`。

**⭐ 这是审计最有力的一击**：残差**完全读不到** θ。 -/
theorem residual_x_zero (y : zX.Carrier) (θ : zΘ.Carrier)
    (u : zFrame.U.Carrier) (ε : zFrame.Ν.Carrier) (a : zFrame.Act.Carrier) :
    y - EndToEnd.predFrom zWorldModel θ u ε a (0 : zX.Carrier) = y := by
  rw [minPred, zero_mul_z, sub_zero]

/-- ⭐⭐⭐⭐ **`x = 0`：更新位移 `θ' - θ` **与 θ 无关**（纯平移 `η y`）。**

**⚠ 精确定义「永不更新」**：本文件取「**位移不依赖 θ**」。
它比「`θ' = θ`」**弱**（后者只在 `y = 0` 时成立，是平凡情形），
但**正是退化所需的**：位移不依赖 θ ⟹ 更新不改变 θ 之间的**相对差**
⟹ **无法把 θ 定向地推向任何点** ⟹ **对这一个样本，学习对 θ 的信息量恒为 0**。

**⚠ 本文件拒绝用「`θ' = θ`」陈述此事实**——那会**夸大**结论（`y = 0` 是平凡情形），
属于把定理写成空真的做法。 -/
theorem zero_x_displacement_indep (y : zX.Carrier) (η : zΘ.Carrier)
    (u : zFrame.U.Carrier) (ε : zFrame.Ν.Carrier) (a : zFrame.Act.Carrier)
    (θ₁ : zΘ.Carrier) :
    ResidualLoop.writeBack zΘ η (AddMonoidHom.id zX.Carrier)
        (y - EndToEnd.predFrom zWorldModel θ₁ u ε a (0 : zX.Carrier)) θ₁ - θ₁
      = η * y := by
  rw [zWriteBack, residual_x_zero]
  exact add_sub_cancel_left _ _

/-- ⭐⭐ **`x = 0` 的位移确实不依赖 θ₁、θ₂**（上一条件的「两参对比」形式）。 -/
theorem zero_x_same_displacement (y : zX.Carrier) (η : zΘ.Carrier)
    (u : zFrame.U.Carrier) (ε : zFrame.Ν.Carrier) (a : zFrame.Act.Carrier)
    (θ₁ θ₂ : zΘ.Carrier) :
    (ResidualLoop.writeBack zΘ η (AddMonoidHom.id zX.Carrier)
        (y - EndToEnd.predFrom zWorldModel θ₁ u ε a (0 : zX.Carrier)) θ₁ - θ₁)
      = (ResidualLoop.writeBack zΘ η (AddMonoidHom.id zX.Carrier)
        (y - EndToEnd.predFrom zWorldModel θ₂ u ε a (0 : zX.Carrier)) θ₂ - θ₂) := by
  rw [zero_x_displacement_indep, zero_x_displacement_indep]

/-! ===========================================================================
    §4  ⭐ `x ≠ 0`：**零残差 θ 唯一 —— 不退化**
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **`x ≠ 0` 且 `y = θ₀ x`：零残差 θ **唯一** `= θ₀`。**

**⭐ 结论的读法**：在 `x ≠ 0` 的臂上、当真参数 `θ₀` **可被表示**（即 `y = θ₀ x`）时，
**零残差集恰是一个单点** ⟹ **θ\* 唯一 ⟹ 不退化**。

**⟹ 审计 (d) 的「θ\* 不唯一，逼近它没有明确意义」在**这一臂上**为假。** -/
theorem nonzero_x_zeroResidualSet_singleton (θ₀ : zΘ.Carrier) (x : zX.Carrier)
    (hx : x ≠ 0) :
    zeroResidualSet (fun θ : zΘ.Carrier => x * θ) (x * θ₀) = ({θ₀} : Set zΘ.Carrier) := by
  ext θ
  simp only [zeroResidualSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have h' : x * (θ₀ - θ) = 0 := by
      rw [mul_sub, h, sub_self]
    rcases mul_eq_zero.mp h' with h1 | h2
    · exact absurd h1 hx
    · exact (sub_eq_zero.mp h2).symm
  · intro h
    rw [h]

/-- ⭐⭐⭐ **`writeBack` 的仿射形式**：`θ' = (1 - η x) * θ + η y`。

**⚠ 本定理对**任意** `x` 成立**（含 `x = 0`）——
正是它揭示了「`x = 0` 时斜率 `= 1`（纯平移）」与「`x ≠ 0` 时斜率 `≠ 1`（可收缩）」。 -/
theorem writeBack_affine (y : zX.Carrier) (η : zΘ.Carrier) (x : zX.Carrier)
    (u : zFrame.U.Carrier) (ε : zFrame.Ν.Carrier) (a : zFrame.Act.Carrier)
    (θ : zΘ.Carrier) :
    ResidualLoop.writeBack zΘ η (AddMonoidHom.id zX.Carrier)
        (y - EndToEnd.predFrom zWorldModel θ u ε a x) θ
      = (1 - η * x) * θ + η * y := by
  rw [zWriteBack, minPred]
  ring

/-- ⭐⭐ **`x = 0` 的斜率恰是 `1`**（⟹ 不开收缩，无法定向收敛）。 -/
theorem zero_x_slope_one (η : zΘ.Carrier) : (1 : zΘ.Carrier) - η * (0 : zX.Carrier) = 1 := by
  rw [mul_zero, sub_zero]

/-- ⭐⭐⭐⭐ **`x ≠ 0`、`η = 1`：不动点集 = 零残差集（已证单点）。**

$$\theta' = \theta \iff \theta\, x = y.$$

**⚠ 陈述方式（回避除法）**：把「`θ* = y/x`」写成「`θ* x = y`」，
这样不需要除法语义，且**这就是**「零残差」的定义式。

**⭐ 结论**：在 `x ≠ 0` 的臂上，「不动点唯一」⟹ **审计 (d) 的「超平面」不出现**。 -/
theorem fixed_point_unique (y : zX.Carrier) (x : zX.Carrier) (_hx : x ≠ 0)
    (u : zFrame.U.Carrier) (ε : zFrame.Ν.Carrier) (a : zFrame.Act.Carrier)
    (θ : zΘ.Carrier) :
    ResidualLoop.writeBack zΘ (1 : zΘ.Carrier) (AddMonoidHom.id zX.Carrier)
        (y - EndToEnd.predFrom zWorldModel θ u ε a x) θ = θ ↔ θ * x = y := by
  rw [writeBack_affine, one_mul]
  constructor
  · intro h
    -- (1-x)*θ + y = θ  ⟹  y = θ - (1-x)θ = x*θ
    have h' : (1 - x) * θ + y = θ + 0 := by rw [add_zero]; simpa using h
    have h2 : y = θ - (1 - x) * θ := by
      have := congrArg (fun t => t - (1 - x) * θ) h'
      simpa using this
    rw [h2]; ring
  · intro h
    rw [← h]; ring

/-! ===========================================================================
    §5  ⚠ **多维降秩**：零残差集是**整条直线**（审计 (d) 的「超平面」的正确形态）
    =========================================================================== -/

/-- ⭐⭐ **降秩纤维**：`Θ = X = ℤ × ℤ`，`R θ = (θ.1, 0)`
（「观测只约束 θ 的第一个坐标」）⟹ 零残差集是**一条竖直直线**。 -/
theorem rank_deficient_fiber (a : ℤ) :
    zeroResidualSet (fun θ : ℤ × ℤ => (θ.1, (0 : ℤ))) (a, 0)
      = {θ : ℤ × ℤ | θ.1 = a} := by
  ext θ
  simp only [zeroResidualSet, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, trivial⟩

/-- ⭐⭐⭐⭐ **降秩 ⟹ 零残差集含至少两个不同元素（θ\* 不唯一）**。

**⭐ 这就是审计 (d) 所谓「多维时残差只约束一个线性组合」的精确形态，
而且它**确实**使 θ\* 不唯一 —— 在这一意义上审计是对的。** -/
theorem rank_deficient_not_unique (a : ℤ) :
    ∃ θ₁ θ₂ : ℤ × ℤ,
      θ₁ ∈ zeroResidualSet (fun θ : ℤ × ℤ => (θ.1, (0 : ℤ))) (a, 0) ∧
      θ₂ ∈ zeroResidualSet (fun θ : ℤ × ℤ => (θ.1, (0 : ℤ))) (a, 0) ∧
      θ₁ ≠ θ₂ := by
  refine ⟨(a, 0), (a, 1), ?_, ?_, ?_⟩
  · rw [rank_deficient_fiber]; rfl
  · rw [rank_deficient_fiber]; rfl
  · simp

/-! ===========================================================================
    §6  ⭐⭐ **更新律塌缩（F）与审计判词的对位**

    即使 θ* **唯一**（§4），更新律仍可能**塌缩**：若 `R θ = θ * x`、`φ = id`、`η = 1`，
    则 `θ' = (1 - x) θ + y`。

    - `x = 1` ⟹ `θ' = y`，**与 θ 无关** ⟹ **任一 θ 都给出同一个更新** ⟹ **不可学习**
      （这是**第三类退化**：θ* 唯一但更新塌缩）；
    - `x ≠ 1` ⟹ `θ ↦ (1-x)θ + y` **单射** ⟹ 更新**保留** θ 的区分能力。
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **`x = 1` 时更新律塌缩**：`θ' = y`，**任一 θ 同值**。

**⭐ 这是本文件对审计 (d) 的**加强**：退化**不止**「θ* 不唯一」一种；
还有「θ* 唯一但**更新完全丢失 θ 的信息**」。
审计没提到这一类，而它**恰恰**是 `writeBack` 的 `+ η φ r` 线性形状的直接后果。** -/
theorem collapse_when_x_eq_one (y : zX.Carrier)
    (u : zFrame.U.Carrier) (ε : zFrame.Ν.Carrier) (a : zFrame.Act.Carrier)
    (θ : zΘ.Carrier) :
    ResidualLoop.writeBack zΘ (1 : zΘ.Carrier) (AddMonoidHom.id zX.Carrier)
        (y - EndToEnd.predFrom zWorldModel θ u ε a (1 : zX.Carrier)) θ = y := by
  rw [zWriteBack, minPred]
  ring

/-- ⭐⭐⭐ **塌缩的「与 θ 无关」形式**：任意两个 θ 给出**同一个** `θ'`。 -/
theorem collapse_theta_indep (y : zX.Carrier)
    (u : zFrame.U.Carrier) (ε : zFrame.Ν.Carrier) (a : zFrame.Act.Carrier)
    (θ₁ θ₂ : zΘ.Carrier) :
    ResidualLoop.writeBack zΘ (1 : zΘ.Carrier) (AddMonoidHom.id zX.Carrier)
        (y - EndToEnd.predFrom zWorldModel θ₁ u ε a (1 : zX.Carrier)) θ₁
      = ResidualLoop.writeBack zΘ (1 : zΘ.Carrier) (AddMonoidHom.id zX.Carrier)
        (y - EndToEnd.predFrom zWorldModel θ₂ u ε a (1 : zX.Carrier)) θ₂ := by
  rw [collapse_when_x_eq_one, collapse_when_x_eq_one]

/-- ⭐⭐⭐⭐ **`x ≠ 1` 时更新律**不塌缩**：`θ ↦ (1-x)θ + y` **单射**。**

**⟹ 更新**保留**θ 的区分能力 ⟹ 可学习（在「θ\* 唯一 + 更新不塌缩」两条件同时满足时）。** -/
theorem affine_injective (x y : zX.Carrier) (hx : (1 : zΘ.Carrier) - x ≠ 0) :
    Function.Injective (fun θ : zΘ.Carrier => (1 - x) * θ + y) := by
  intro a b hab
  have h : (1 - x) * a = (1 - x) * b := by
    exact add_right_cancel hab
  exact mul_left_cancel₀ hx h

/-- ⭐⭐⭐ **`x ≠ 1` + `x ≠ 0` ⟹ 更新律**既不塌缩、也不纯平移**（兼「单射 + 斜率 `≠ 1`」）。 -/
theorem learnable_of_x_ne_zero_ne_one (x y : zX.Carrier)
    (hx0 : x ≠ 0) (hx1 : (1 : zΘ.Carrier) - x ≠ 0) :
    Function.Injective (fun θ : zΘ.Carrier => (1 - x) * θ + y)
      ∧ (1 : zΘ.Carrier) - x ≠ 1 :=
  ⟨affine_injective x y hx1, by
    intro h
    apply hx0
    have h' : (1 : zΘ.Carrier) - x = 1 := h
    linarith⟩

/-! ===========================================================================
    §7  **自检清单**
    =========================================================================== -/

/-- **自检 1**：零残差集就是纤维（一般情形）。 -/
example (R : ℤ → ℤ) (xobs : ℤ) : {θ | xobs - R θ = 0} = zeroResidualSet R xobs :=
  zeroResidualSet_eq_fiber R xobs

/-- **自检 3**：`x ≠ 0` 的零残差集是单点。 -/
example (θ₀ : zΘ.Carrier) (x : zX.Carrier) (hx : x ≠ 0) :
    zeroResidualSet (fun θ : zΘ.Carrier => x * θ) (x * θ₀) = ({θ₀} : Set zΘ.Carrier) :=
  nonzero_x_zeroResidualSet_singleton θ₀ x hx

/-- **自检 4**：降秩时零残差集不唯一。 -/
example (a : ℤ) : ∃ θ₁ θ₂ : ℤ × ℤ,
      θ₁ ∈ zeroResidualSet (fun θ : ℤ × ℤ => (θ.1, (0 : ℤ))) (a, 0) ∧
      θ₂ ∈ zeroResidualSet (fun θ : ℤ × ℤ => (θ.1, (0 : ℤ))) (a, 0) ∧ θ₁ ≠ θ₂ :=
  rank_deficient_not_unique a

/-- **自检 5**：`x = 1` 时更新塌缩。 -/
example (y : zX.Carrier) (u : zFrame.U.Carrier)
    (ε : zFrame.Ν.Carrier) (a : zFrame.Act.Carrier) (θ : zΘ.Carrier) :
    ResidualLoop.writeBack zΘ (1 : zΘ.Carrier) (AddMonoidHom.id zX.Carrier)
        (y - EndToEnd.predFrom zWorldModel θ u ε a (1 : zX.Carrier)) θ = y :=
  collapse_when_x_eq_one y u ε a θ

/-- **自检 6**：几条判据**可同时**成立（不冲突）。

- `x ≠ 0` 不退化（零残差集单点）；
- 降秩退化（零残差集直线）。

⚠ 原第三条「`x = 0` 时零残差集 = 全空间」已删除，理由见文件头 §0.5。 -/
example :
    (∀ (θ₀ : zΘ.Carrier) (x : zX.Carrier), x ≠ 0 →
        zeroResidualSet (fun θ : zΘ.Carrier => x * θ) (x * θ₀) = ({θ₀} : Set zΘ.Carrier))
    ∧ (∃ θ₁ θ₂ : ℤ × ℤ,
        θ₁ ∈ zeroResidualSet (fun θ : ℤ × ℤ => (θ.1, (0 : ℤ))) (0, 0) ∧
        θ₂ ∈ zeroResidualSet (fun θ : ℤ × ℤ => (θ.1, (0 : ℤ))) (0, 0) ∧ θ₁ ≠ θ₂) :=
  ⟨nonzero_x_zeroResidualSet_singleton,
   rank_deficient_not_unique 0⟩

end T1DegeneracyVerify
end FateV2.Predict