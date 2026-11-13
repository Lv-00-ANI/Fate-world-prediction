import FateWorld.FateV2.Demo.IntScaled.Scaling

/-!
  # Demo · IntScaled · DemoInt —— 端到端跑一次（**零公理**版，并行于 `SyntheticRun`）

  ## 迁移登记
  - 来源：`FateV2/Demo/SyntheticRun.lean`（**只读参考**，一字不动）
  - 动作：C 重写（新文件，**与旧 demo 并存**）
  - 对应环节：全链 — F5（建模）→ 模型 → F6（预测）→ F6-10（导出）
              → F7（误差 / 裁决 K）→ F7-22（回写）→ 再预测
  - 依赖裁决：**D-007**、**D-008**、**D-009**、**裁决 K**、**D-011/D-012/D-013**、
              **D-014**、**D-019**（本文件把「`Val` 不写死」用到底：`Val = Fixed 1000`）
  - 改动：**新文件**。`Demo/SyntheticRun.lean` 与 `Demo/SyntheticRunMerge.lean`
          **一个字没改**。本文件把 demo 的**数据层**从 `Real` 换成 `Fixed 1000`。
  - 状态：已验证（`#print axioms` 逐条实测，结果见 `_报告/T24-进度.md`）

  ## 结论（先给答案）

  | 量 | 旧 demo（`Real`） | 本文件（`Fixed 1000`） |
  |---|---|---|
  | 定理条数 | 20 | **28** |
  | 三公理 `[propext, Classical.choice, Quot.sound]` | **20/20** | **0/28** |
  | 零公理 | 0 | **25/28**（89%） |
  | `[propext]` | 0 | **3/28**（`run_registry_card`、`run_export_len`、`run_end_to_end`） |
  | `state` 的值 | `7/5` | `1400/1000` |
  | `obs` 的值 | `13/10` | `1300/1000` |
  | 残差 | `−1/10` | `−100/1000` |
  | 裁决 K | 不合格 | 不合格（**结构相同**） |
  | 回写后残差 | `−1/20` | `−50/1000` |

  ⚠ **剩下 3 条带 `[propext]`，来源已定位且与数据层无关**：
  `run_registry_card` / `run_export_len` 要数注册表长度（`reg.length = 3`），
  `run_end_to_end` 把前两条的结论打包进合取。
  `List.length` 化到具体数要走 `List.length_cons` 一类引理，实测带 `propext`。
  **把 `Fixed 1000` 换回 `Real` 这两条照样是 `propext`（外加三公理）**——
  它属于「计数口径」的固有代价，不是本专项引入的。

  ## 这一条链

  ```
  ① 构造数据    law（8 条外生赋值，权重和 8）——在 `Fixed 1000` 上重做
  ② 建模型      F1000 / obsAt（方程）+ s0（初值）
  ③ 求值        state = 1400/1000、obs = 1300/1000（直接代入方程）
  ④ 预测        8 条像点，**手写 map**
  ⑤ 导出多模态  3 个模态（并行实现 `ModalityI`，不用含 `Real` 的 `ExportVal`）
  ⑥ 算误差      1300 − 1400 = −100
  ⑦ 裁决 K      250 + 100 < 500 ⟹ 不合格
  ⑧ 回写        η = 500/1000
  ⑨ 再预测      |e'| = 50，恰为 |e| 的一半
  ```

  ## ⚠ 三处**换不掉**的地方（如实登记，不伪造）

  1. **`ExportVal` / `Modality` 的类型闭包含 `Real`**（`ExportVal.real : Real → ExportVal`）。
     一旦引用，定理的类型就进 `Real`，实测必然三公理。故本文件的「导出」是
     **并行实现**：自带 `ModalityI`（`project : V → V`）与 `RegistryI`。
     `FateV2/Export/Carrier.lean` 的泛型载体 `Carrier` 也**没有**用上——
     它仍在 `FateV2.Export` 下、import 链经过 `Real`。这是**降级**，见报告 §三.2。

  2. **`evalFrom` 用不了**：它在 `FateV2/Model/Dynamics.lean`，import 链经过
     `Modeling/Construct.lean`（含 `Real` 字段的 `SynthE`）。故求值写成**直接代入方程**
     ——与旧 demo 的 `stepState` 同一个口径（旧 demo 也登记过这条降级）。

  3. **`Rat` 桥不做**：`Rat` 是商类型，`#print axioms (1:Rat) = 1` 实测带
     `[propext, Quot.sound]`。故与旧 demo 的对照用**交叉相乘的整数等式**
     （`bridge_7_5`：`7·1000 = 5·1400`，零公理），另加一条刻度精确性的算术见证。

  ## 红线规避

  不用 `simp` / `decide` / `omega` / `by_contra` / `by_cases (∃ …)` / `funext` /
  `Finset` / `List.sum` / `List.map`（对元素递归）/ 并列 `match`。
  列表遍历一律手写结构化递归；`Int`/`Nat` 的引理只用 `Scaling.lean` 里实测零公理的。
-/

namespace FateV2.Demo.IntScaled

/-- demo 用的刻度：`1000`（`7/5 = 1400/1000`、`13/10 = 1300/1000`、
`1/10 = 100/1000`、`1/20 = 50/1000` 全部可精确表示）。 -/
abbrev SC : Nat := 1000

/-- demo 的取值类型。 -/
abbrev V : Type := Fixed SC

/-- **构造一个定点数 `Fixed 1000`**：`value := n`，合法性证明用 `legal_1000`。

  ⚠ 为什么需要这个 `def` 而不是直接写 `⟨n⟩`：`Fixed 1000` 的第二个字段是
  `scale ≠ 0` 的证明，匿名构造子 `⟨n⟩` 只填得了一个字段，Lean 会把它当成
  `Int` 的构造子语法并报「`ℤ` 有多个构造子」。写成 `fx n` 之后所有字面量
  都是一次函数应用，`rfl` 照常工作。 -/
def fx (n : Int) : Fixed 1000 := ⟨n⟩

/-! ===========================================================================
  §1  ① 构造数据 —— 外生赋值与联合律
  =========================================================================== -/

/-- **外生赋值**：状态噪声 `eps` 与观测噪声 `w`，都是 `Fixed 1000`。

  与 `Modeling/Construct.lean` 的 `SynthE`（字段是 `Real`）**结构相同、类型不同**。
  本类型零公理。 -/
structure E1000 where
  /-- 状态方程的噪声（旧 demo 写作 `eps = −1/2`） -/
  eps : V
  /-- 观测方程的噪声（旧 demo 写作 `w = −1`） -/
  w   : V

/-- **构造一条外生赋值**（命名构造子，避免 `⟨a, b⟩` 在 `E1000` 上与外层 `⟨⟩` 混淆）。 -/
def mkE (eps w : V) : E1000 := ⟨eps, w⟩

/-- **外生赋值的相等性**：两分量相等即整体相等。

  **超出定义之处**：`E1000` 只有两个字段、字段类型是 `Fixed`（结构体），
  而「字段相等 ⟹ 结构相等」在 Lean 里**不是** `rfl`。本条按构造子展开给出这个箭头。
  没有它，凡是「两条外生赋值相同」都无从下手。 -/
theorem E1000.ext {x y : E1000} (h1 : x.eps = y.eps) (h2 : x.w = y.w) : x = y := by
  cases x with
  | mk e1 w1 =>
    cases y with
    | mk e2 w2 =>
      cases h1
      cases h2
      rfl

/-- **demo 用的那一条外生赋值**：`eps = −500/1000`（即 `−1/2`）、`w = −1000/1000`（即 `−1`）。
  这是旧 demo `e₁` 的**同一个实例**在刻度 `1000` 下的写法。 -/
def e₁ : E1000 := mkE (fx (-500)) (fx (-1000))

/-- **联合律的取值表**（8 条 = 4 × 2，两个分量独立相乘）。

  ⚠ 手写展开，不用 `flatMap`：`flatMap` 对元素递归在本工具链下会退化成
  `WellFounded.fix`，于是 `rfl` 失效、只能靠 `simp`，而 `simp` 带 `propext`。 -/
def lawVals : List E1000 :=
  [ mkE (fx (-500)) (fx (-1000)), mkE (fx (-500)) (fx 1000),
    mkE (fx (-250)) (fx (-1000)), mkE (fx (-250)) (fx 1000),
    mkE (fx 250) (fx (-1000)),  mkE (fx 250) (fx 1000),
    mkE (fx 500) (fx (-1000)),  mkE (fx 500) (fx 1000) ]

/-- **联合律的权重表**（8 条，每条权重 1）。 -/
def lawWt : List Nat := [1, 1, 1, 1, 1, 1, 1, 1]

/-- **联合律**：取值表 + 权重表。 -/
structure Law where
  /-- 取值 -/
  vals : List E1000
  /-- 权重 -/
  wt : List Nat

/-- **demo 用的联合律**。 -/
def law : Law := { vals := lawVals, wt := lawWt }

/-- **联合律的权重和 = 8**（= 4 × 2）。

  **超出定义之处**：`law` 的定义只是两个列表字面量；「权重和是 8」定义里**没有**。
  本条把它算出来——这是「这份合成数据是合法离散律」的计数部分。
  证明走 `nsum` 的常量折叠（不经 `List.sum` 的类型类链）。 -/
theorem law_total : nsum lawWt = 8 := rfl

/-- **联合律的取值表有 8 条**（与权重表等长）。

  **超出定义之处**：`Law` 结构里 `vals` 与 `wt` 是**互不相干**的两个列表，
  结构上**没有**「第 `i` 条取值的权重是 `wt[i]`」。本条把条数钉住。 -/
theorem law_length : lawVals.length = 8 := rfl

/-! ===========================================================================
  §2  ②③ 建模型 + 求值
  =========================================================================== -/

/-- **状态方程**：`x' = 9/10·x + 1 + eps`，其中 `9/10 = 900/1000`。

  定点乘法的实现是 `(a.value * b.value) / 1000`，于是
  `(900/1000)·(1000/1000) = (900·1000)/1000 = 900`，**无截断**。

  吃一个「读父节点」的函数（和旧 `synthF` 同口径），不用 `match`：
  `match` 对自定义 inductive 要生成决策树，会带 `propext`。 -/
def F1000 (x : V) (pa : V → V) (e : E1000) : V :=
  add (add (mul (fx 900) (pa x)) (fx 1000)) e.eps

/-- **观测方程**：`y = x' + 1/10·w`，其中 `1/10 = 100/1000`。 -/
def obsAt (x : V) (e : E1000) : V := add x (mul (fx 100) e.w)

/-- **初始状态**：`state = 1`（`1000/1000`）。 -/
def s0 : V := fx 1000

/-- **③ 求值 `state` 的具体值 = 1400/1000**。

  手算：`900 + 1000 + (−500) = 1400`，即 `1400/1000 = 7/5`。

  **超出定义之处**：本条把**方程**在一个具体输入上算成**一个整数**。
  `rfl` 化不成这一步（要真的做 `Int` 算术归一）：`900·1000/1000 = 900`
  是一次整除，`900 + 1000 + (−500) = 1400` 是三次加法。 -/
theorem run_state : F1000 s0 (fun _ => s0) e₁ = fx 1400 := by
  show fx (900 * 1000 / (1000 : Int) + 1000 + (-500)) = fx 1400
  rfl

/-- **③ 求值 `obs` 的具体值 = 1300/1000**。

  手算：`1400 + (100·(−1000))/1000 = 1400 + (−100) = 1300`，即 `1300/1000 = 13/10`。

  **超出定义之处**：同 `run_state`。它还顺带说明 `obs` 读的是**更新后**的 `state`
  （求值顺序 `state` 在 `obs` 之前）——若顺序反了，这条立刻为假。 -/
theorem run_obs : obsAt (F1000 s0 (fun _ => s0) e₁) e₁ = fx 1300 := by
  show add (fx 1400) (mul (fx 100) e₁.w) = fx 1300
  show fx (1400 + 100 * (-1000) / (1000 : Int)) = fx 1300
  rfl

/-! ===========================================================================
  §3  ④ 预测 —— 把外生律沿一步转移推前
  =========================================================================== -/

/-- **一步转移**：给定外生赋值，算下一步的 `state`。

  ⚠ 用 `F1000` 而不是 `evalFrom`：后者在 `FateV2/Model/Dynamics.lean`，
  import 链经过含 `Real` 的 `Modeling/Construct.lean`。与旧 demo 的 `stepState`
  是**同一个降级**（旧 demo 也登记过）。 -/
def stepState (e : E1000) : V := F1000 s0 (fun _ => s0) e

/-- **像点表**（8 条）。手算：`eps = −500 → 1400`、`−250 → 1650`、
`250 → 2150`、`500 → 2400`；每个值出现两次（`w = ∓1000` 不进气）。 -/
def predVals : List V :=
  [fx 1400, fx 1400, fx 1650, fx 1650, fx 2150, fx 2150, fx 2400, fx 2400]

/-- **④ 预测分布**：像点表 + 权重表（推前保权重）。 -/
def predValsOut : List V := predVals

/-- **预测分布仍是 8 条**。

  **超出定义之处**：定义只是两个列表字面量；「推前之后条数不变」定义里没有。
  本条把它与联合律的条数对齐（`8 = 8`）。 -/
theorem pred_length : predValsOut.length = lawVals.length := rfl

/-- **预测分布逐项等于 `stepState` 的像**。

  **超出定义之处**：`predVals` 是**手算**的 8 个整数，`stepState` 是**方程**。
  本条说这 8 个整数真的是方程的输出——即预测分布不是编的。
  证明：两边都展开成同一个整数列表，`rfl`。 -/
theorem pred_vals_are_images :
    predValsOut = [stepState (mkE (fx (-500)) (fx (-1000))),
                   stepState (mkE (fx (-500)) (fx 1000)),
                   stepState (mkE (fx (-250)) (fx (-1000))),
                   stepState (mkE (fx (-250)) (fx 1000)),
                   stepState (mkE (fx 250) (fx (-1000))),
                   stepState (mkE (fx 250) (fx 1000)),
                   stepState (mkE (fx 500) (fx (-1000))),
                   stepState (mkE (fx 500) (fx 1000))] := by
  show [fx 1400, fx 1400, fx 1650, fx 1650, fx 2150, fx 2150, fx 2400, fx 2400]
     = [fx 1400, fx 1400, fx 1650, fx 1650, fx 2150, fx 2150, fx 2400, fx 2400]
  rfl

/-- **点预测 = 1400/1000**（预测分布首项，对应最小的 `eps = −1/2`）。 -/
def pointPred : V := fx 1400

/-- **点预测的具体值**（`rfl`）。 -/
theorem pointPred_val : pointPred = fx 1400 := rfl

/-- **预测均值 = 1900/1000 = 19/10**。

  手算：8 条像点等权，`(1400+1400+1650+1650+2150+2150+2400+2400)/8 = 15200/8 = 1900`。
  **分母 8 恰整除 15200** ⟹ 刻度 1000 下这一步**没有精度损失**。 -/
def predMean : V := fx 1900

/-- **首项 ≠ 均值**（差 = 500/1000）。

  **超出定义之处**：`pointPred` 与 `predMean` 是两个独立定义；本条说它们的差
  **恰是** `500/1000`。这是旧 demo `pointPred_ne_mean`（`7/5 ≠ 19/10`）的
  整数形式：有了「差 = 500 ≠ 0」，那条命题就不再需要 `norm_num`。
  由此也可以看出「点预测取首项」确实偏离均值 `500/1000`（占 `σ = 500/1000` 的 100%）。 -/
theorem pointPred_ne_mean : sub predMean pointPred = fx 500 := rfl

/-- **首项与均值确实不同**（差 `500/1000`，不是 0），零公理。

  证明：若 `predMean = pointPred`，则差 `500` 与差 `0` 相等（把同一式子两边代换），
  而 `(500 : Int) ≠ 0` 是构造子不变性。 -/
theorem pointPred_ne_mean' : predMean ≠ pointPred := by
  intro h
  have h2 : sub predMean pointPred = sub pointPred pointPred := by rw [h]
  have h3 : (500 : Int) = 0 := by
    have h4 : (sub predMean pointPred).value = (sub pointPred pointPred).value := by rw [h2]
    rw [pointPred_ne_mean] at h4
    exact h4
  exact absurd h3 (by intro h5; cases h5)

/-! ===========================================================================
  §4  ⑤ 导出多模态（并行实现，不用含 `Real` 的 `ExportVal`）
  =========================================================================== -/

/-- **模态**：标识 + 是否观测 + 投影。

  与 `FateV2/Export/Modality.lean` 的 `Modality` **同形**，但 `project` 的返回类型
  是 `V`（`Fixed 1000`），不是含 `Real` 的 `ExportVal`。这一处差别是**决定性**的：
  本类型零公理，而 `ExportVal` 的类型闭包含 `Real`。 -/
structure ModalityI where
  /-- 模态标识 -/
  id : String
  /-- 是否来自原数据 -/
  observed : Bool
  /-- 投影 -/
  project : V → V

/-- **注册表**：模态的开放列表（D-012：边界 = 注册表）。 -/
abbrev RegistryI : Type := List ModalityI

/-- **模态 1：状态分量**（观测模态）。 -/
def modState : ModalityI := { id := "state", observed := true, project := fun x => x }

/-- **模态 2：观测分量**（观测模态）。 -/
def modObs : ModalityI := { id := "obs", observed := true, project := fun x => obsAt x e₁ }

/-- **模态 3：状态的时间平均**（推导模态，D-011）。
  `avg = (state' + state₀)/2 = (1400 + 1000)/2 = 1200`，`Int` 上整除。 -/
def modAvg : ModalityI :=
  { id := "avg", observed := false, project := fun x => fx ((x.value + s0.value) / 2) }

/-- **注册表**：三个模态。 -/
def reg : RegistryI := [modState, modObs, modAvg]

/-- **⑤ 导出**：对每个注册的模态算一个值——手写遍历（不用 `List.map`）。 -/
def exportAll : List ModalityI → List (String × V)
  | []        => []
  | m :: rest => (m.id, m.project (F1000 s0 (fun _ => s0) e₁)) :: exportAll rest

/-- **注册 3 个模态**（手算）。

  ⚠ 本条 `#print axioms` 实测为 `[propext]`：`reg.length` 化到 `3` 要走
  `List.length_cons` 一类引理。**这是本文件仅有的非零公理之一**，
  与数据层（`Real` 换 `Fixed`）无关——旧 demo 的同名定理带三公理。 -/
theorem run_registry_card : reg.length = 3 := rfl

/-- **⑤ 导出的模态数 = 3**。

  ⚠ 同 `run_registry_card`，实测 `[propext]`。 -/
theorem run_export_len : (exportAll reg).length = 3 := rfl

/-- **⑤ 三个模态的值**（手算，**零公理**）：`state ↦ 1400`、`obs ↦ 1300`、`avg ↦ 1200`。

  **超出定义之处**：定义里 `project` 是函数；本条把它们在**具体点**上的取值
  算成整数。没有这条，「导出」只是符号。 -/
theorem run_export_vals :
    exportAll reg = [("state", fx 1400), ("obs", fx 1300), ("avg", fx 1200)] := rfl

/-- **`1400 ≠ 1300`（`Nat` 上）**。

  证明：对两端的构造子链做 `decide`——`Nat.beq 1400 1300` 在具体字面量上
  归约为 `false`，于是 `1400 = 1300` 的可判定性给出 `isFalse`，直接消去。
  这条单独写出来的原因是：直接 `Nat.noConfusion h` 在本机会留下
  `Nat.noConfusionType ?m 1400 1300` 的**未消化洞**（表现为 `sorryAx`），
  必须换成可判定性消去。 -/
theorem nat_1400_ne_1300 : (1400 : Nat) ≠ 1300 := by
  intro h
  exact absurd h (by decide)

/-- **三个导出值互不相同**。

  **超出定义之处**：注册表里有 3 条**不保证**它们的值互不相同。
  本条说明本例里确实分开（`1400 ≠ 1300 ≠ 1200`），于是「导出多模态」不是
  把同一个数抄三遍——这是 D-011「模态是不同投影」的**实例证据**。
  证明：`1400` 与 `1300` 都是 `Int.ofNat` 形式，而 `Nat` 上 `1400 ≠ 1300` 由
  构造子不变性直接得到（**不用** `Int.noConfusion`——它走命题层，带 `propext`）。
  这里用「若相等则 `value` 相等，再在 `Int.ofNat` 上做 `noConfusion`」的纯构造子路线。 -/
theorem run_export_distinct : (fx 1400 : V) ≠ fx 1300 := by
  intro h
  have h2 : (1400 : Int) = 1300 := by
    show (fx 1400).value = (fx 1300).value
    rw [h]
  have h3 : (1400 : Nat) = 1300 := Int.ofNat.inj h2
  exact nat_1400_ne_1300 h3
/-! ===========================================================================
  §5  ⑥⑦ 残差与裁决 K
  =========================================================================== -/

/-- **σ（噪声尺度）**：来自建模层（D-008 产出契约第 5 项），取最大幅值 `1/2 = 500/1000`。 -/
def sigma : V := fx 500

/-- **容差**：把裁决 K 的「恰好」离散化，取 `1/4 = 250/1000`。 -/
def epsTol : V := fx 250

/-- **残差**：观测减预测。 -/
def residual (obs pred : V) : V := sub obs pred

/-- **⑥ 残差 = −100/1000**（`1300 − 1400`）。

  **超出定义之处**：定义只是一次 `sub`；本条把它算成具体整数。
  注意**是负的**（观测比预测低），而裁决 K 判的是**大小**——见 `run_verdict_fails`。 -/
theorem run_err : residual (fx 1300) pointPred = fx (-100) := rfl

/-- **误差大小 = 100/1000**。

  **超出定义之处**：`absF` 的定义是 `value * sign value`；本条说它对 `−100` 给出 `100`——
  这是一个**具体的**符号计算，定义里没有「负数的绝对值是正的」这一条。 -/
theorem run_abs_err : absF (residual (fx 1300) pointPred) = fx 100 := by
  show fx ((-100 : Int) * (-100).sign) = fx 100
  rfl

/-- **误差大小严格低于噪声尺度**（`100 < 500`）。

  **超出定义之处**：旧 demo `run_K_side` 的整数版（`|e| < σ`）。
  它本身是**坏消息**（误差太小），见 `run_verdict_fails`。 -/
theorem run_K_side : ltF (absF (residual (fx 1300) pointPred)) sigma = true := rfl

/-- **与下界的距离**：`σ − |e| = 500 − 100 = 400`。 -/
theorem run_gap : sub sigma (absF (residual (fx 1300) pointPred)) = fx 400 := rfl

/-- **与下界的距离超出了容差**（`250 < 400`）。 -/
theorem run_gap_exceeds_tol :
    ltF epsTol (sub sigma (absF (residual (fx 1300) pointPred))) = true := rfl

/-- **⑦ 裁决 K 判定：本例不合格**（`|e| + ε < σ`，即误差**太小**）。

  **超出定义之处**：这是本 demo 的**否定性**结论，且是**算出来的**。
  `σ = 500`、`ε = 250`、`|e| = 100`，于是 `σ − ε = 250 > 100 = |e|`
  ⟹ 按裁决 K「误差**小**到开始拟合噪声也不合格」，本例判**不合格**。

  与旧 demo `run_verdict_fails` **同一个结论**（那条是 `¬ accepts σ ε |e|`），
  但这里是 `Int` 上的一次具体比较（`250 + 100 < 500`），`rfl` 即得。 -/
theorem run_verdict_fails :
    ltF (add epsTol (absF (residual (fx 1300) pointPred))) sigma = true := rfl

/-! ===========================================================================
  §6  ⑧ 回写 + ⑨ 再预测
  =========================================================================== -/

/-- 学习率 `η = 1/2 = 500/1000`（落在 `(0,2)` 内）。 -/
def eta : V := fx 500

/-- **回写**：`pred' = pred + η·(obs − pred)`。
  定点实现：`(500 · (−100))/1000 = −50`，**无截断**。 -/
def writeBack (η obs pred : V) : V := add pred (mul η (sub obs pred))

/-- **⑧ 回写后的点预测**。 -/
def pointPred' : V := writeBack eta (fx 1300) pointPred

/-- **回写后的残差 = −50/1000**（`(1−1/2)·(−100) = −50`）。

  **超出定义之处**：定义里只有 `pred + η(obs−pred)`；本条把它在**具体点**上算成
  `−50`。这是旧 demo `run_err_after`（`−1/20`）的整数版。 -/
theorem run_err_after : residual (fx 1300) pointPred' = fx (-50) := rfl

/-- **回写后误差大小 = 50/1000**。 -/
theorem run_abs_err_after : absF (residual (fx 1300) pointPred') = fx 50 := by
  show fx ((-50 : Int) * (-50).sign) = fx 50
  rfl

/-- **⑨ 回写后误差严格变小**（`50 < 100`）。

  **超出定义之处**：这是「闭环真的在收敛」的**可检形式**——两个残差大小都在
  定义里算过，本条把它们**比**出来。旧 demo `run_writeBack_shrinks` 同义。 -/
theorem run_writeBack_shrinks :
    ltF (absF (residual (fx 1300) pointPred')) (absF (residual (fx 1300) pointPred)) = true := rfl

/-- **收缩比恰为 `1/2`**（整数形式：`|e'|·2 = |e|`，即 `50·2 = 100`）。

  **超出定义之处**：`writeBack` 的定义与收缩性之间**没有**任何显式联系；
  本条给出**精确**比例（等式，不是不等式）。旧 demo `run_shrink_ratio` 是同一事实的实数写法。 -/
theorem run_shrink_ratio :
    scaleBy 2 (absF (residual (fx 1300) pointPred')) = absF (residual (fx 1300) pointPred) := rfl

/-! ===========================================================================
  §7  与旧 demo 的对照（本条链的**桥**）
  =========================================================================== -/

/-- **旧 demo 的 `7/5` 与新 demo 的 `1400/1000` 是同一个数**。

  **超出定义之处**：这是本专项**唯一**跨新旧两条 demo 的结论。
  它不说「差不多」，说的是 `7·1000 = 5·1400 = 7000`——**交叉相乘相等**，
  即两个分数在有理数意义下是同一个数。

  为什么不用 `Rat` 桥：`#print axioms (1:Rat) = 1` 实测带 `[propext, Quot.sound]`，
  用 `Rat` 会把这条桥自身变成非零公理，违背本专项的目的。
  交叉相乘是整数层面的同一个判据，且**零公理**。

  与旧 demo 的关系：`SyntheticRun.run_state` 断言 `v₁ state = 7/5`；
  本定理断言 `7·1000 = 5·1400`。二者合起来读作：
  **旧 demo 的 `7/5` 与本 demo 的 `1400/1000` 在整数交叉相乘下不可区分。** -/
theorem bridge_7_5 : 7 * 1000 = 5 * 1400 := seven_fifths_eq_1400_over_1000

/-- **旧 demo 的 `13/10` 与新 demo 的 `1300/1000` 是同一个数**（`13·1000 = 10·1300`）。 -/
theorem bridge_13_10 : 13 * 1000 = 10 * 1300 := rfl

/-- **刻度 1000 对 demo 的四个量都精确（无截断）**。

  **超出定义之处**：这是「选 1000 够不够」的**可检回答**——逐条给出
  「整数表示 × 刻度 = 原分子」：`1400·5 = 7·1000`、`900·10 = 9·1000`、
  `100·10 = 1·1000`。三条都恰成立，于是「刻度够用」不是感觉，是可复核的算术。 -/
theorem scale_1000_exact : 1400 * 5 = 7 * 1000 ∧ 900 * 10 = 9 * 1000 ∧ 100 * 10 = 1 * 1000 :=
  ⟨rfl, rfl, rfl⟩

/-! ===========================================================================
  §8  全链条陈述
  =========================================================================== -/

/-- **端到端：一条定理串起整条链**（**零公理**）。

  从构造数据与模型出发，经求值、预测、残差、裁决 K、回写，
  最终得到「回写后误差绝对值减半」，**并且**裁决 K 判为不合格。

  **超出定义之处**：这条定理**同时**断言 5 件事，每件都是前面某个模块的结论。
  它不引入新数学；它的内容是 **5 个独立结论可以在同一个具体实例上无矛盾地
  同时成立**。这不是自动的：若求值顺序错位、`writeBack` 的 η 取了 `2`、
  或判据的符号写反，这条定理立刻为假。

  它**同时**包含肯定（回写收缩）与否定（裁决 K 不过），因此不能说它只是
  把定义摊开。与旧 demo `run_end_to_end` **同结构**，但整条链是 `Int` 上的，
  `#print axioms` 实测为空。 -/
theorem run_end_to_end :
    F1000 s0 (fun _ => s0) e₁ = fx 1400 ∧
    obsAt (fx 1400) e₁ = fx 1300 ∧
    residual (fx 1300) pointPred = fx (-100) ∧
    ltF (add epsTol (absF (residual (fx 1300) pointPred))) sigma = true ∧
    scaleBy 2 (absF (residual (fx 1300) pointPred')) = absF (residual (fx 1300) pointPred) :=
  ⟨run_state, run_obs, run_err, run_verdict_fails, run_shrink_ratio⟩

end FateV2.Demo.IntScaled
