import FateWorld.FateV2.Predict.PushMerge
import FateWorld.FateV2.Predict.DistributionInvariants
import FateWorld.FateV2.Predict.PushCorrectness
import FateWorld.FateV2.Model.Dynamics
import FateWorld.FateV2.Modeling.Construction

/-!
  # Data · Ingest —— 从「外部数据」到 `Model` 的可执行路径（专项 **T54**）

  ## 迁移登记
  - 来源：新写（本文件）
  - 动作：C 重写（新目录 + 新文件）
  - 对应环节：F1-13（数据载体并入建模层）、F5-01（SCM 结构）、F6-01（预测）、
              专项 **T54**（补 `D-023` A2「暂时无数据」的工程缺口）
  - 依赖裁决：**D-007**、**D-008**、**D-014**、**D-019**、**D-023 A2**、**D-022**
  - 改动：**只新建**。既有文件一个字没改。需协调者加一行 import（见文末 §9）。
  - 状态：已验证（`lake build` + `#print axioms` + `#eval`，见 `_报告/T54-进度.md`）

  ## 〇、这份文件解决什么（先给结论）

  | # | 派单交付 | 交割 | 命题真假核实 |
  |---|---|---|---|
  | 1 | `DataSpec` + 良构判据 + 解析器全性 | §1 / §2 | ✅ 真（须显式写 `WF` 前件） |
  | 2 | `discLawFromColumn` + `valid` | §3 / §4 | ⚠ 原式在**空列**上为假，须加 `col ≠ []` |
  | 3 | `modelFromData` + 两条定理 | §5 | ✅ 真（失败情形改成 `isSome` 的**充要**刻画） |
  | 4 | `dataToPrediction` + 两条定理 | §6 | ✅ 真（「走 `predict`」证成**等式**） |
  | 5 | `#eval` 演示 | §7 | ✅ 真跑出数 |

  ## 一、★ 派单第 2 条：命题真假核实（先算真假再动手）

  派单写的是：

  ```lean
  theorem discLawFromColumn_valid (col : List Int) :
      (discLawFromColumn col).vals.Nodup ∧ (discLawFromColumn col).total = col.length
  ```

  **核实过程**：取 `col = [2, 2]`。

  * 若不合并（取值表 = 原列、权重全 1）：`vals = [2, 2]`，`Nodup` 为 **假**；
  * 若合并（按派单 ⚠ 提示，像 `pushMerge` 那样把同值权重相加）：
    `vals = [2]`（`Nodup` **真**），`wt = [2]`，`total = 2 = col.length`（**真**）。

  ⟹ 在**非空列**上两个合取项都成立；派单担心的「`Nodup` 不成立」被
  「合并」消掉，而 `total = col.length` 那一半**与合并无关**——
  它成立的理由是**每个样本权重都是 `1`**（经验测度），
  合并只把若干 `1` 加成一个更大的数，总量不变。证明因此落在
  **`pushMerge` 保权重和**（§4 的 `discLawFromColumn_total`，走 T4 的 `goN_sum`，
  **不是** `rfl`）。

  ⚠ **派单原式没有前件，而它在空列上是假命题**：
  `[].length = 0`，但空列必须给一个**合法**分布（否则下游 `predict`
  拿 `total` 当分母会除零），本文件选 Dirac `0 ↦ 1`，于是 `total = 1 ≠ 0`。
  故定理加了前件 `col ≠ []`，并把空列这一例外单独证成 `nolaw_empty_ne` ——
  「命题在哪为真、在哪为假」两边都有据可查。

  ⚠ **派单原式里的 `(discLawFromColumn col).total` 不能直接用**：
  `DiscLaw.total` 是 `L.wt.sum`（`List.sum`，默认 `Add` 实例搜索带 `propext`）。
  本文件用**零公理**的 `sumN` 陈述同一条事实（`lawTotal := sumN L.wt`），
  再用 `lawTotal_eq_total`（§3）把它与 `DiscLaw.total` **接上**。

  ## 二、`DataSpec` 长什么样

  派单给的三个字段**原样保留**（`vars` / `rows` / `colTypes`）。三处补充：

  1. **判等只用 `DecidableEq` 的 `decide`**，不用 `BEq` 的 `==`：
     `String` 的 `BEq` 反射律在本项目已实测要打开内部表示（T37）。
  2. **全文件的 `Int` 判等只走 `eqI`**（§0），于是「A 处用 `==`、B 处用 `decide`」
     这类分叉在类型层就不可能发生。
  3. **`rows` 是 `List (List Int)`**：`[]`（零行）与 `[[]]`（一行零列）
     是两个**不同**的数据。

  ## 三、为什么取 `Int` 而不是 `Real`

  * `Int` 上 `decide (· = ·)` **可计算**（实测零公理），`pushMerge` 能 `#eval` 跑；
  * `Real` 的 `DecidableEq` 是 `noncomputable` 实例（T13 实测），取 `Real`
    会让整条链变成 `noncomputable`，`#eval` 一个数都跑不出来 ——
    **那就不是「数据能进来」的证据了**。

  于是「真实数据」在这里的落地形态是：**数值型数据集先锚定到整数格点**
  （计数、分位数、或按最小单位放大后的整数）。这是表示选择，不是分布假设。

  ## 四、建模选择最小化（派单的硬要求）

  **不**假设正态、线性、独立。本文件只做一件事：

  > 把一列数据变成它的**经验分布**（每个样本权重 `1`，同值合并），
  > 再把经验分布装进 `Model.P_U`。

  `Model.F` 也**不**做回归拟合 —— 它是「读外生赋值本身」（理由写在 §5）。

  ## 五、公理账（逐条实测见 `_报告/T54-进度.md` §四）

  | 层 | 说明 |
  |---|---|
  | **零公理** | 全部算术/列表基元、经验分布的总质量、`modelFromData` 的边界 |
  | `propext` | 凡引用 `decide_eq_true_eq`（`eqI` 的反射律）/ T22 `pushMerge_nodup` |
  | `Quot.sound` / `Classical.choice` | 仅 `column_length_le` / `parse_full` |

  ⚠ **`Quot.sound` 的来源必须说清**：`parse_full` 用到了
  `List.getElem?_eq_getElem`，它经 `List.getElem?` 的 `decide` 分支带进了
  `Quot.sound`。这是**被引用的列表引理**带的，不是本文件的推理带。
-/

set_option maxHeartbeats 1000000

namespace FateV2.DataIngest

open FateV2.Modeling FateV2.Predict

/-! ===========================================================================
  §0  `Int` 上的判等（**先定口径**）
  =========================================================================== -/

/-- **`Int` 的判等**：`decide (a = b)`。

  为什么不直接写 `a == b`：`String` 的 `BEq` 反射律在本项目已实测要打开
  内部表示（T37）；本定义让全文件的判等**只有一个来源**。 -/
def eqI (a b : Int) : Bool := decide (a = b)

/-- **`eqI` 自反**（⚠ 带 `propext`）。

  **超出定义之处**：`eqI` 的定义只说「包装 `decide`」，
  没说它对任何数自己返回 `true`。 -/
theorem eqI_refl (a : Int) : eqI a a = true := by
  show decide (a = a) = true
  rw [decide_eq_true_eq]

/-- **`eqI` 对称**（⚠ 带 `propext`）。

  **超出定义之处**：`decide` 的定义对参数顺序毫无要求；
  本条说明两个方向是同一件事。 -/
theorem eqI_symm (a b : Int) (h : eqI a b = true) : eqI b a = true := by
  show decide (b = a) = true
  rw [decide_eq_true_eq]
  have h' : decide (a = b) = true := h
  rw [decide_eq_true_eq] at h'
  exact h'.symm

/-- **`eqI` 传递**（⚠ 带 `propext`）。

  **超出定义之处**：定义里没有任何关于「链式判等」的内容；
  本条说明 `eqI` 满足传递性，于是它才能当 `pushMerge` 的合并键。 -/
theorem eqI_trans (a b c : Int) (h1 : eqI a b = true) (h2 : eqI b c = true) :
    eqI a c = true := by
  show decide (a = c) = true
  rw [decide_eq_true_eq]
  have h1' : decide (a = b) = true := h1
  have h2' : decide (b = c) = true := h2
  rw [decide_eq_true_eq] at h1' h2'
  rw [h1', h2']

/-- **`eqI` 是一个判等口径**（打包成 T22 的 `IsEq`）。

  **超出定义之处**：`eqI` 的定义**没有**声明自己满足那三条；
  本条是「本文件的判等能被 T22 全部定理消费」的唯一入口 ——
  没有它，`pushMerge_nodup` 在本文件里用不上。 -/
theorem eqI_isEq : IsEq eqI where
  refl := eqI_refl
  symm := eqI_symm
  trans := eqI_trans

/-- **非空表不是空表**（构造子级，零公理）。 -/
theorem cons_ne_nil2 (v : String) (vs : List String) : (v :: vs : List String) ≠ [] :=
  fun h => nomatch h

/-- **空表不是非空表**（构造子级，零公理）。 -/
theorem nil_ne_cons2 (v : String) (vs : List String) : ([] : List String) ≠ v :: vs :=
  fun h => nomatch h

/-- **`false` 不是 `true`**（零公理）。 -/
theorem false_ne_true2 : (false : Bool) ≠ true :=
  fun h => nomatch h

/-- **`none` 不是 `some`**（零公理）。 -/
theorem none_ne_some2 {α : Type} (a : α) : (none : Option α) ≠ some a :=
  fun h => nomatch h

/-! ===========================================================================
  §1  `DataSpec`：外部数据的 Lean 表示
  =========================================================================== -/

/-- **列类型**。

  * `bool`  —— 只允许 `0` / `1`（编码成 `Int`，于是整张表仍是 `List (List Int)`）；
  * `cat`   —— 类别码（任意 `Int`，**只有相等有意义**）；
  * `num`   —— 数值。

  ⚠ **`num` 与 `cat` 的构造行为完全一致，这是有意的**（「建模选择最小化」）：
  对 `num` 做回归/平滑/标准化都属于分布假设，派单明令不要。
  `num` 的唯一可检验后果是 `ColTypesOk` 对数值列不施加 `0/1` 限制
  （`numCol_any_value_ok` 把这条证明出来）。 -/
inductive ColType where
  /-- 数值列 -/
  | num
  /-- 类别码列 -/
  | cat
  /-- 布尔列（`0` / `1`） -/
  | bool
  deriving DecidableEq, Repr

/-- **数据规范**：外部数据以 Lean 能表达的形式住在这里。

  三字段与派单**逐字一致**。语义约定：

  * `rows[i][j]` = 第 `i` 个样本在第 `j` 个变量上的取值；
  * `vars[j]` 与该列的列类型 `colTypes[j]` 一一对应；
  * 判 `bool` 列时只看 `0`/`1`。

  **超出定义之处**：结构体本身**没有任何约束**——`vars` 可以 3 条而
  `rows` 的行宽是 5，`colTypes` 可以更短。这些约束全部在 `WF` 里，
  于是「良构」是一个**可检验命题**而不是一句口头约定（D-022）。 -/
structure DataSpec where
  /-- 变量名 -/
  vars : List String
  /-- 观测表：每行是一个样本 -/
  rows : List (List Int)
  /-- 每列的类型 -/
  colTypes : List ColType
  deriving Repr

/-- **列类型匹配**：`bool` 列只许放 `0` / `1`。

  `num` / `cat` 两列**不做数值检查**——这是「不做分布假设」的直接后果：
  **不检查取值范围，只检查编码约定**。

  **超出定义之处**：定义对数值列**恒真**（`numCol_any_value_ok`）。 -/
def ColTypesOk (spec : DataSpec) : Prop :=
  ∀ r ∈ spec.rows, ∀ t ∈ spec.colTypes.zip r,
    t.1 = ColType.bool → t.2 = 0 ∨ t.2 = 1

/-- **良构（`WF`）**：三个条件同时成立。

  1. **变量表与列类型表等长**；
  2. **每行与变量表等宽**；
  3. **列类型匹配**（`ColTypesOk`）。

  **超出定义之处**：`DataSpec` 的三个字段彼此**没有约束**；
  本条把它们之间**必须成立**的关系写出来，于是 `parse_full` 才有前件可写。 -/
def WF (spec : DataSpec) : Prop :=
  spec.vars.length = spec.colTypes.length ∧
  (∀ r ∈ spec.rows, r.length = spec.vars.length) ∧
  ColTypesOk spec

/-! ===========================================================================
  §1.5  演示数据集（端到端 `#eval` 用）
  =========================================================================== -/

/-- **演示数据集**：4 个样本、3 个变量。

  | # | `x` | `flag` | `z` |
  |---|---|---|---|
  | 1 | 1 | 0 | 0 |
  | 2 | 2 | 1 | 1 |
  | 3 | 3 | 1 | 0 |
  | 4 | 1 | 0 | 0 |

  这份数据是**手写的、公开的**（不是「假装是真实数据」）：
  用途是证明**通路存在**，不是证明「某个真实世界结论」。
  `x` 列有重复值（`1` 出现两次），于是 §3 的合并逻辑在这份数据上
  **真的会触发** —— 这是有意选的。 -/
def demoData : DataSpec :=
  { vars := ["x", "flag", "z"]
  , rows := [[1, 0, 0], [2, 1, 1], [3, 1, 0], [1, 0, 0]]
  , colTypes := [ColType.num, ColType.bool, ColType.cat] }

/-! ===========================================================================
  §2  可执行解析：不丢行、不丢列
  =========================================================================== -/

/-- **样本数**：`rows` 的行数。

  单独做成一个 `def`，于是「解析器全性」的陈述是
  `(columnOf spec j).length = numRows spec`，读过去就是「**行一行不少**」。 -/
def numRows (spec : DataSpec) : Nat := spec.rows.length

/-- **`numRows` 的定义式**（`rfl`）。 -/
theorem numRows_eq (spec : DataSpec) : numRows spec = spec.rows.length := rfl

/-- **取一列**：第 `j` 列的全部取值，**顺序与 `rows` 一致**。

  ⚠ 手写递归而**不用** `List.map (·.get? j)`：后者在本工具链上会退化成
  well-founded，而 `parse_full` 要的正是「列长 = 行数」这条**结构**事实。

  **超出定义之处（跳过）**：行比 `j` 短时该行**不进入这一列**。
  这是定义**留出的唯一漏洞**——`shortRow_loses_row`（§2.2）给出具体数值。 -/
def column (rows : List (List Int)) (j : Nat) : List Int :=
  match rows with
  | [] => []
  | r :: rs =>
    match r[j]? with
    | none => column rs j
    | some x => x :: column rs j

/-- **在 `DataSpec` 上取一列**（派单口径的接口）。

  **超出定义之处**：`column` 的签名里没有 `DataSpec`（它只在 `rows` 上递归）；
  本条把它装回 `DataSpec`，于是「取列**不看** `vars` / `colTypes`」
  成为**类型层**的事实。 -/
def columnOf (spec : DataSpec) (j : Nat) : List Int := column spec.rows j

/-- **列长 ≤ 行数**（无前件版）：短行只让列**变短**，绝不让它**变长**。

  **超出定义之处**：`column` 在短行上「跳过」，定义里没有一句关于
  「跳过之后还剩多少」的话；本条给出**无条件**上界。 -/
theorem column_length_le : ∀ (spec : DataSpec) (j : Nat), (columnOf spec j).length ≤ numRows spec
  | ⟨_, [], _⟩, _ => by
    rw [numRows_eq]
    exact Nat.zero_le 0
  | ⟨vars, r :: rs, cols⟩, j => by
    rw [numRows_eq]
    show (match r[j]? with
          | none => column rs j
          | some x => x :: column rs j).length ≤ rs.length + 1
    cases hq : r[j]? with
    | none =>
      show (column rs j).length ≤ rs.length + 1
      exact Nat.le_trans (column_length_le ⟨vars, rs, cols⟩ j) (Nat.le_succ rs.length)
    | some x =>
      show (column rs j).length + 1 ≤ rs.length + 1
      exact Nat.succ_le_succ (column_length_le ⟨vars, rs, cols⟩ j)

/-- **★ 解析器对良构数据是全的**（派单第 1 条的后半）：第 `j` 列**一行不少**。

  **超出定义之处（要害）**：`column` 在 `r[j]? = none` 时会**跳过**该行，
  于是定义本身**允许**丢行。本条说明：只要数据良构（每行都比 `j` 宽），
  `get?` 永远命中，**一行都不会被跳过**。去掉 `h : WF spec` 时命题**是假的**
  （`shortRow_loses_row`，§2.2）。 -/
theorem parse_full (spec : DataSpec) (h : WF spec) (j : Nat) (hj : j < spec.vars.length) :
    (columnOf spec j).length = numRows spec := by
  match spec with
  | ⟨vars, [], cols⟩ =>
    show ([] : List Int).length = ([] : List (List Int)).length
    rfl
  | ⟨vars, r :: rs, cols⟩ =>
    obtain ⟨hvc, hwidth, hcol⟩ := h
    have hjv : j < vars.length := hj
    have hr : j < r.length := by
      rw [hwidth r List.mem_cons_self]
      exact hjv
    have hg : r[j]? = some (r.get ⟨j, hr⟩) := List.getElem?_eq_getElem hr
    show (match r[j]? with
          | none => column rs j
          | some x => x :: column rs j).length = rs.length + 1
    rw [hg]
    show (column rs j).length + 1 = rs.length + 1
    have htail : (columnOf ⟨vars, rs, cols⟩ j).length = rs.length :=
      parse_full ⟨vars, rs, cols⟩
        ⟨hvc, (fun r2 hr2 => hwidth r2 (List.mem_cons_of_mem r hr2)),
         (fun r2 hr2 => hcol r2 (List.mem_cons_of_mem r hr2))⟩ j hjv
    show (columnOf ⟨vars, rs, cols⟩ j).length + 1 = rs.length + 1
    rw [htail]

/-! ## §2.1 良构的三个分量各有反例（判据不是空话） -/

/-- 反例数据：两行，宽度不一（第 2 行只有 1 列）。-/
def raggedData : DataSpec :=
  { vars := ["a", "b"], rows := [[1, 2], [3]], colTypes := [ColType.num, ColType.num] }

/-- 反例数据：`colTypes` 比 `vars` 短（3 个变量只登记了 2 个类型）。-/
def shortTypesData : DataSpec :=
  { vars := ["a", "b", "c"], rows := [[1, 2, 3]], colTypes := [ColType.num, ColType.num] }

/-- 反例数据：`bool` 列里放了 `2`。-/
def badBoolData : DataSpec :=
  { vars := ["flag"], rows := [[2], [0]], colTypes := [ColType.bool] }

/-- **宽度反例不满足 `WF`**。

  **超出定义之处**：`raggedData` 只是字面量，定义里没有「它坏」这句话；
  本条说明 `WF` 的第二分量在它上**恰好失败**。 -/
theorem raggedData_not_wf : ¬ WF raggedData := by
  intro h
  have hw : ∀ r ∈ raggedData.rows, r.length = raggedData.vars.length := h.2.1
  have h1 : ([1, 2] : List Int).length = ([3] : List Int).length :=
    hw [1, 2] List.mem_cons_self ▸
      (hw [3] (List.mem_cons_of_mem [1, 2] List.mem_cons_self)).symm
  exact absurd h1 (by decide)

/-- **类型表长度反例不满足 `WF`**。 -/
theorem shortTypesData_not_wf : ¬ WF shortTypesData := by
  intro h
  exact absurd h.1 (by decide)

/-- **`bool` 编码反例不满足 `WF`**。

  **超出定义之处**：`badBoolData` 在语法上完全「合法」（全是 `Int`）；
  本条说明 `WF` 的第三分量**真的在把关**。 -/
theorem badBoolData_not_wf : ¬ WF badBoolData := by
  intro h
  obtain ⟨_, _, hok⟩ := h
  have hmem : (ColType.bool, (2 : Int)) ∈ (([] : List ColType) ++ [ColType.bool]).zip [2] :=
    List.mem_cons_self
  have hb := hok [2] List.mem_cons_self (ColType.bool, (2 : Int)) hmem rfl
  rcases hb with h1 | h1
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

/-- **`demoData` 的列类型表**（`rfl`）。 -/
theorem demoData_colTypes :
    demoData.colTypes = ([ColType.num, ColType.bool, ColType.cat] : List ColType) := rfl

/-- **★ `WF` 不是空谓词**：良构数据确实存在（`demoData` 就是一个）。

  **超出定义之处**：上面三条只说「可以失败」（D-022 的一半要求）；
  本条补上「也可以成立」——于是 `WF` 是**两边都非空**的判据，
  `parse_full` 的前件**不是空的**。 -/
theorem wf_witness : WF demoData := by
  refine ⟨rfl, ?_, ?_⟩
  · intro r hr
    rcases mem_cons_mp r [1, 0, 0] [[2, 1, 1], [3, 1, 0], [1, 0, 0]] hr with rfl | hr1
    · rfl
    · rcases mem_cons_mp r [2, 1, 1] [[3, 1, 0], [1, 0, 0]] hr1 with rfl | hr2
      · rfl
      · rcases mem_cons_mp r [3, 1, 0] [[1, 0, 0]] hr2 with rfl | hr3
        · rfl
        · rcases mem_cons_mp r [1, 0, 0] [] hr3 with rfl | hnil
          · rfl
          · exact absurd hnil (not_mem_nil_aux r)
  · intro r hr t ht hb
    have hr3 : r = [r[0]?.getD 0, r[1]?.getD 0, r[2]?.getD 0] := by
      rcases mem_cons_mp r [1, 0, 0] [[2, 1, 1], [3, 1, 0], [1, 0, 0]] hr with rfl | hr1
      · rfl
      · rcases mem_cons_mp r [2, 1, 1] [[3, 1, 0], [1, 0, 0]] hr1 with rfl | hr2
        · rfl
        · rcases mem_cons_mp r [3, 1, 0] [[1, 0, 0]] hr2 with rfl | hr3'
          · rfl
          · rcases mem_cons_mp r [1, 0, 0] [] hr3' with rfl | hnil
            · rfl
            · exact absurd hnil (not_mem_nil_aux r)
    rw [demoData_colTypes, hr3] at ht
    rcases mem_cons_mp t (ColType.num, r[0]?.getD 0)
        ([(ColType.bool, r[1]?.getD 0), (ColType.cat, r[2]?.getD 0)] :
          List (ColType × Int)) ht with h1 | h1
    · rw [h1] at hb; exact absurd hb (by intro hh; exact ColType.noConfusion hh)
    · rcases mem_cons_mp t (ColType.bool, r[1]?.getD 0)
          ([(ColType.cat, r[2]?.getD 0)] : List (ColType × Int)) h1 with h2 | h2
      · rw [h2] at hb ⊢
        rcases mem_cons_mp r [1, 0, 0] [[2, 1, 1], [3, 1, 0], [1, 0, 0]] hr with rfl | hr1
        · exact Or.inl rfl
        · rcases mem_cons_mp r [2, 1, 1] [[3, 1, 0], [1, 0, 0]] hr1 with rfl | hr2
          · exact Or.inr rfl
          · rcases mem_cons_mp r [3, 1, 0] [[1, 0, 0]] hr2 with rfl | hr3'
            · exact Or.inr rfl
            · rcases mem_cons_mp r [1, 0, 0] [] hr3' with rfl | hnil
              · exact Or.inl rfl
              · exact absurd hnil (not_mem_nil_aux r)
      · rcases mem_cons_mp t (ColType.cat, r[2]?.getD 0) [] h2 with h3 | h3
        · rw [h3] at hb; exact absurd hb (by intro hh; exact ColType.noConfusion hh)
        · exact absurd h3 (not_mem_nil_aux t)

/-- **`ColTypesOk` 对数值列恒真**：`num` / `cat` 列放什么数都不违反它。

  **超出定义之处**：`ColTypesOk` 里有一个 `t.1 = bool →` 的前件，
  它**看起来**像在检查每一列；本条说明对数值列这个蕴含的前提是假的，
  于是谓词**恒真** ——「不检查取值范围」由此成为一个**可证**的性质。 -/
theorem numCol_any_value_ok (spec : DataSpec)
    (h : ∀ r ∈ spec.rows, ∀ t ∈ spec.colTypes.zip r, t.1 = ColType.num) :
    ColTypesOk spec := by
  intro r hr t ht hb
  have hn := h r hr t ht
  rw [hn] at hb
  exact absurd hb (by intro hh; exact ColType.noConfusion hh)

/-! ## §2.2 前件不可去掉：短行真的会丢行 -/

/-- **短行会让解析器丢行**（`parse_full` 的前件不可去掉）。

  在 `raggedData` 上取第 2 列（`j = 1`）：第 1 行 `[1, 2]` 命中，
  第 2 行只有 `[3]`，`[3][1]? = none`，于是这一行被**跳过**：
  列长 `1` ≠ 行数 `2`。

  **超出定义之处**：`column` 的「跳过」分支在定义里只是一行 `| none =>`；
  本条给出它**真的会少一行**的具体数值见证。 -/
theorem shortRow_loses_row : (columnOf raggedData 1).length = 1 ∧ numRows raggedData = 2 := by
  constructor
  · rfl
  · rfl

/-! ===========================================================================
  §3  从一列数据构造经验分布（`DiscLaw`）—— 派单第 2 条
  =========================================================================== -/

/-- **全 1 权重表**：每个样本权重 `1`（经验测度，**非参数**）。

  ⚠ 手写递归而不用 `List.map (fun _ => 1)`：后者会退化成 well-founded。
  定义的内容在 `onesWt_length` 与 `sumN_onesWt` 两条定理里。 -/
def onesWt : List Int → List Nat
  | [] => []
  | _ :: t => 1 :: onesWt t

/-- **`onesWt` 保长度**（结构递归，零公理）。

  **超出定义之处**：定义没有说「等长」；本条把它钉住 ——
  于是 `discLawFromColumn` 的 `vals`/`wt` 按位置对齐有保证。 -/
theorem onesWt_length (l : List Int) : (onesWt l).length = l.length := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    show (onesWt t).length + 1 = t.length + 1
    rw [ih]

/-- **`sumN` 在 `onesWt` 上等于列表长度**（结构递归，零公理）。

  **超出定义之处**：定义没有说「权重和是多少」；本条给出它的**闭式** ——
  `n` 个样本的权重和恰是 `n`。这是「合并保总质量」那一步的前件。 -/
theorem sumN_onesWt (l : List Int) : FateV2.Predict.sumN (onesWt l) = l.length := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    show 1 + FateV2.Predict.sumN (onesWt t) = t.length + 1
    rw [ih, Nat.add_comm]

/-- **`DiscLaw` 上的权重和**（零公理口径）：`sumN L.wt`。

  为什么不用 `DiscLaw.total`：后者是 `L.wt.sum`，而 `List.sum` 的默认
  `Add` 实例搜索带 `propext`（T4 §11 / T22 §5 已实测）。
  与 `DiscLaw.total` 的接口见 `lawTotal_eq_total`。 -/
def lawTotal (L : DiscLaw Int) : Nat := FateV2.Predict.sumN L.wt

/-- **`lawTotal` 与 `DiscLaw.total` 是同一条事实的两种写法**（走 T4 的 `sumN_sum`）。

  **超出定义之处**：两个定义**分别**写的（一个手写递归、一个 `List.sum`）；
  本条说明它们给出同一个数 —— 于是 §4 的定理可以换写成派单原式的
  `DiscLaw.total` 形态而不损失内容。 -/
theorem lawTotal_eq_total (L : DiscLaw Int) : lawTotal L = L.wt.sum :=
  FateV2.Predict.sumN_sum L.wt

/-- **★ 从一列整数构造经验分布**（派单第 2 条的正体，**可执行**）。

  * **空列**：给出 Dirac 律 `0 ↦ 1`
  * **非空列**：每个样本权重 `1`，**同值合并**（走 T4 的 `pushMerge`）

  ⚠ **空列为什么取 `0 ↦ 1` 而不是空律**：空律的总质量是 `0`，
  它**不是**概率分布，下游 `predict` 拿 `total` 当分母会除零。
  取 Dirac 之后空列是一个**合法**的概率分布，代价是空列的
  `total = 1 ≠ 0 = [].length`（`discLawFromColumn_empty_total` 与
  `nolaw_empty_ne` 把这条差别单独写出来）。
  这是「全函数」与「经验测度」必须二选一的地方，本文件选全函数。 -/
def discLawFromColumn (col : List Int) : DiscLaw Int :=
  match col with
  | [] => { vals := [0], wt := [1] }
  | c :: t => FateV2.Predict.pushMerge (fun x : Int => x) { vals := c :: t, wt := onesWt (c :: t) }

/-- **非空列的 `discLawFromColumn` 就是 `pushMerge` 恒等推前**（`rfl`）。

  **超出定义之处**：定义里的 `match` 有两支；本条把**非空那一支**
  摊成可直接 `rw` 的等式，于是 §4 的定理全部能引 T4/T22 的
  `pushMerge` 系列结论，而不必重新证一遍合并逻辑。 -/
theorem discLawFromColumn_cons (col : List Int) (h : col ≠ []) :
    discLawFromColumn col =
      FateV2.Predict.pushMerge (fun x : Int => x) { vals := col, wt := onesWt col } := by
  match col with
  | [] => exact absurd rfl h
  | x :: t => rfl

/-- **空列给出 Dirac 律**（`rfl`）。 -/
theorem discLawFromColumn_nil :
    (discLawFromColumn []).vals = [0] ∧ (discLawFromColumn []).wt = [1] :=
  ⟨rfl, rfl⟩

/-! ===========================================================================
  §4  ★ 派单第 2 条的定理：`discLawFromColumn` 给出**合法**分布
  =========================================================================== -/

/-- **门槛：`NoDupP` ⟹ `List.Nodup`**（对 `keyOf` 出的表）。

  T22 的 `pushMerge_nodup` 的结论是 `NoDupP eqb (goN …)`（乘积对的谓词），
  而派单要的是 `vals.Nodup`（`List.Nodup`）。本条就是两者之间的**唯一**桥梁，
  且**只**依赖 `eqI` 的自反性（不需要对称/传递）——
  比 T22 的 `IsEq` 要求**弱**。

  **超出定义之处**：`NoDupP` 是「每项与尾巴判不等」，`List.Nodup` 是
  `Pairwise (· ≠ ·)`；本条把它们接上。 -/
theorem nodup_of_noDupP_keyOf :
    ∀ (l : List (Int × Nat)), FateV2.Predict.NoDupP eqI l → (FateV2.Predict.keyOf l).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons hd tl ih =>
    intro h
    obtain ⟨a, c⟩ := hd
    obtain ⟨hcross, hrest⟩ := h
    show (a :: FateV2.Predict.keyOf tl).Nodup
    rw [List.nodup_cons]
    refine ⟨?_, ih hrest⟩
    intro hmem
    have hf : eqI a a = false := hcross a hmem
    rw [eqI_refl a] at hf
    exact absurd hf (by decide)

/-- **★ `discLawFromColumn` 的取值表无重复**（派单第 2 条的第一半）。

  **超出定义之处（要害）**：这是**派单点名要核实**的那一条。
  「合并」真的在起作用：不合并的写法（`vals := col`）在 `col = [2, 2]`
  上给出 `vals = [2, 2]`（`Nodup` **假**）；本定义走 `pushMerge`，
  同值合并成一条。具体数值见 `twoTwos`（§4.1）。 -/
theorem discLawFromColumn_nodup (col : List Int) (hne : col ≠ []) :
    (discLawFromColumn col).vals.Nodup := by
  rw [discLawFromColumn_cons col hne]
  show (FateV2.Predict.keyOf (FateV2.Predict.goN eqI (fun x : Int => x) []
    col (onesWt col))).Nodup
  exact nodup_of_noDupP_keyOf _
    (FateV2.Predict.pushMerge_nodup eqI eqI_isEq (fun x : Int => x) col (onesWt col)
      (onesWt_length col).symm)

/-- **★ `discLawFromColumn` 保总质量**（派单第 2 条的第二半）。

  `lawTotal (discLawFromColumn col) = col.length`（`col` 非空时）。

  **超出定义之处**：定义只说「合并 + 全 1 权重」，
  **没有**任何关于总质量的话。本条说合并**不丢**权重：
  每个样本贡献的 `1` 都被记进某个像点（同值就加到同一条上），
  故总质量恰是样本数。走的是 T4 的 `goN_sum`（**不是** `rfl`）。 -/
theorem discLawFromColumn_total (col : List Int) (hne : col ≠ []) :
    lawTotal (discLawFromColumn col) = col.length := by
  rw [discLawFromColumn_cons col hne]
  show FateV2.Predict.sumN (FateV2.Predict.wtOf (FateV2.Predict.goN eqI (fun x : Int => x) []
    col (onesWt col))) = col.length
  have h1 := FateV2.Predict.goN_sum eqI (fun x : Int => x) ([] : List (Int × Nat))
    col (onesWt col) (onesWt_length col).symm
  show FateV2.Predict.sumN (FateV2.Predict.wtOf (FateV2.Predict.goN eqI (fun x : Int => x) []
    col (onesWt col))) = col.length
  rw [h1, sumN_onesWt]
  show (0 : Nat) + col.length = col.length
  exact Nat.zero_add _

/-- **空列的总质量是 `1`**（`rfl`）：空列给 Dirac 律。

  **超出定义之处**：这是 `discLawFromColumn_total` 的**例外**，
  必须单独写出来 —— 否则会有人以为「总质量 = 样本数」对**所有**列成立。 -/
theorem discLawFromColumn_empty_total : lawTotal (discLawFromColumn []) = 1 := rfl

/-- **★ 派单第 2 条（主定理）：`discLawFromColumn` 给出合法分布。**

  `(discLawFromColumn col).vals.Nodup ∧ lawTotal (discLawFromColumn col) = col.length`

  ⚠ **与派单原式的三点差别，逐条交代**：

  1. **派单原式没有 `hne : col ≠ []`**。本定理**加了**这个前件，
     因为空列上总质量是 `1`（Dirac）而 `[].length = 0`，两者不等
     （`discLawFromColumn_empty_total` + `nolaw_empty_ne`）。
     **派单原式在空列上是假命题**；本定理给出它**为真的那个范围**。
  2. **派单原式写 `(discLawFromColumn col).total`**，本定理写 `lawTotal`。
     两者是同一事实（`lawTotal_eq_total`），换成 `sumN` 是为了零公理。
  3. **派单原式说「`Nodup` 在有重复的列上可能不成立」**：核实结论是
     「合并之后它成立」，且这里**真的用了合并**（证明走 `pushMerge_nodup`）。

  **超出定义之处**：这是两条独立结论的**合取**：
  `Nodup` 来自合并逻辑（T22），`total` 来自保质量（T4）。
  定义本身对两者**都没有承诺**。 -/
theorem discLawFromColumn_valid (col : List Int) (hne : col ≠ []) :
    (discLawFromColumn col).vals.Nodup ∧ lawTotal (discLawFromColumn col) = col.length :=
  ⟨discLawFromColumn_nodup col hne, discLawFromColumn_total col hne⟩

/-- **派单原式在空列上不成立**：`1 ≠ 0`。

  **超出定义之处**：这是**负结果**，价值在于它把
  `discLawFromColumn_valid` 的前件 `col ≠ []` 钉成**必要**的。 -/
theorem nolaw_empty_ne : ¬(lawTotal (discLawFromColumn []) = ([] : List Int).length) := by
  rw [discLawFromColumn_empty_total]
  intro h
  exact absurd h.symm (by decide)

/-! ## §4.1 合并在具体数据上真的生效（数值见证） -/

/-- **带重复的列**：`[2, 2, 3]`。-/
def dupCol : List Int := [2, 2, 3]

/-- **★ 合并把两个 `2` 并成一条**：`vals = [2, 3]`、`wt = [2, 1]`。

  **超出定义之处**：定义只说「走 `pushMerge`」；本条给出**具体数值**，
  于是「合并真的发生了」是一个 `rfl` 可验的事实 ——
  **不合并**的写法会给出 `vals = [2, 2, 3]`、`wt = [1, 1, 1]`。 -/
theorem dupCol_shape :
    (discLawFromColumn dupCol).vals = [2, 3] ∧ (discLawFromColumn dupCol).wt = [2, 1] :=
  ⟨rfl, rfl⟩

/-- **带重复的列也有 `Nodup`**（具体见证）。 -/
theorem dupCol_nodup : (discLawFromColumn dupCol).vals.Nodup := by
  rw [dupCol_shape.1]
  exact List.nodup_cons.mpr ⟨(by decide), List.nodup_singleton 3⟩

/-- **带重复的列总质量仍是样本数**：`2 + 1 = 3 = dupCol.length`。 -/
theorem dupCol_total : lawTotal (discLawFromColumn dupCol) = 3 := rfl

/-- **★ 派单原式的两个合取项在 `[2, 2]` 上都成立**（最小的重复例子）。

  `vals = [2]`（两条并成一条）、`wt = [2]`、`total = 2 = [2,2].length`。

  **超出定义之处**：派单用 `[2, 2]` 做**担心**的例子（怕 `Nodup` 不成立）；
  本条把它变成**正面**的例子 —— 合并之后它成立，且总质量没丢。 -/
theorem twoTwos :
    (discLawFromColumn [2, 2]).vals = [2] ∧ lawTotal (discLawFromColumn [2, 2]) = 2 :=
  ⟨rfl, rfl⟩


/-! ===========================================================================
  §5  从数据构造 SCM —— 派单第 3 条
  =========================================================================== -/

/-- **数据造出的模型的变量**：只有一个内生节点 `x`（对应第 0 列）。 -/
inductive DataV where
  /-- 唯一的内生节点 -/
  | x
  deriving DecidableEq, Repr

/-- **数据造出的外生赋值**：噪声就是这一列上的一个整数。

  于是 `P_U : DiscLaw Int` 直接就是**这一列的经验分布** ——
  这是「数据能进来」的核心：**外生律不再是手写的，而是从数据数出来的**。 -/
abbrev DataE := Int

/-- **结构方程：读外生赋值本身**（`x := e`）。

  ⚠ **为什么不做回归拟合**：派单的「建模选择最小化」明令
  「不要假设数据的分布形态（正态、线性等）」。回归拟合（哪怕是线性）
  都在假设「`y` 是 `x` 的线性函数 + 噪声」—— 那是一个**分布假设**，
  不是表示选择。取 `F x _ e := e` 之后，`x` 就是「这一行数据的外生输入」，
  模型是**非参数**的：它把数据原样当作经验分布，不做任何形状假设。

  代价如实登记：这样的 `F` **没有学到任何条件关系**。
  「数据 → 有结构的 SCM」需要图 + 拟合，属 A1 与后续专项；
  本专项只交付**通路**。

  **超出定义之处**：定义本身只是一个投影函数；它满足「与父赋值无关」
  （`dataF_ignores_pa`）—— 于是图可以是空父集，不需要额外假设任何边。 -/
def dataF : DataV → (DataV → Int) → DataE → Int
  | DataV.x, _, e => e

/-- **结构方程不看父赋值**（`rfl`）。

  **超出定义之处**：`dataF` 的定义是一个 `match`；本条说明它在 `pa` 上
  **恒定**，于是「`x` 没有父节点」是一条可证的事实。 -/
theorem dataF_ignores_pa (pa pa' : DataV → Int) (e : DataE) :
    dataF DataV.x pa e = dataF DataV.x pa' e := rfl

/-- **图**：`x` 没有父节点。 -/
def dataGraph : Graph DataV where
  pa := fun _ => []

/-- **★ 从数据构造 SCM**（派单第 3 条的正体，**可执行**）。

  * **成功条件**：`vars` 非空（至少一列）。这时取第 0 列的经验分布当 `P_U`；
  * **失败条件**：`vars = []`（没有变量）。这时返回 `none`。

  ⚠ **为什么失败条件是「`vars` 空」而不是「`rows` 空」**：
  `rows = []`（零样本）时，第 0 列是空列，`discLawFromColumn []` 给出
  Dirac 律 `0 ↦ 1` —— 那是一个**合法**的（退化的）外生律，
  于是模型仍然造得出来。而 `vars = []` 时连「第 0 列」都不存在，
  模型没有可命名的内生节点，**只能**失败。
  这条边界的**充要性**见 `modelFromData_isSome_iff`（§5.1）。 -/
def modelFromData (spec : DataSpec) : Option (Model Int DataV DataE (DiscLaw Int)) :=
  match spec.vars with
  | [] => none
  | _ :: _ =>
    some
      { F := dataF
      , P_U := discLawFromColumn (columnOf spec 0)
      , graph := some dataGraph }

/-- **★ 构造成功时，`P_U` 就是数据的经验分布**（派单第 3 条的第一半）。

  **超出定义之处**：`modelFromData` 的定义里 `P_U` 是**内联**写在结构体
  字面量里的；本条把它摊成等式，于是「模型的噪声律来自数据」不是
  「看定义能看出来」，而是一条**可引用**的定理 ——
  §6 的 `dataToPrediction` 正是靠它把预测接回数据。 -/
theorem modelFromData_PU (spec : DataSpec) (M : Model Int DataV DataE (DiscLaw Int))
    (h : modelFromData spec = some M) :
    M.P_U = discLawFromColumn (columnOf spec 0) ∧ M.F = dataF ∧
      M.graph = some dataGraph := by
  match hv : spec.vars with
  | [] =>
    have hnone : modelFromData spec = none := by rw [modelFromData, hv]
    rw [hnone] at h
    exact absurd h (none_ne_some2 M)
  | v :: vs =>
    rw [modelFromData, hv] at h
    cases h
    exact ⟨rfl, rfl, rfl⟩

/-! ## §5.1 构造的确切边界：`isSome` 的**充要**刻画 -/

/-- **★ 构造失败的**充要**条件：`vars = []`**（派单第 3 条的第二半）。

  `(modelFromData spec).isSome ↔ spec.vars ≠ []`

  **超出定义之处（要害）**：派单要「构造失败的情形**有据可查**」。
  `modelFromData` 的定义里只有一行 `| [] => none` —— 它**没有**说
  「除了这一支，别的情形全都成功」。本定理把这条边界**两边都钉住**：

  * ⟸（`vars ≠ []` ⟹ 成功）：非空变量表一定走 `some` 那一支；
  * ⟹（成功 ⟹ `vars ≠ []`）：`vars = []` 时定义**只能**给 `none`。

  于是「什么时候没有模型」**完全可以由数据本身判定**。 -/
theorem modelFromData_isSome_iff (spec : DataSpec) :
    (modelFromData spec).isSome ↔ spec.vars ≠ [] := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · intro hc
    match hv : spec.vars with
    | [] =>
      have hz : (modelFromData spec).isSome = false := by rw [modelFromData, hv]; rfl
      rw [hz] at h
      exact false_ne_true2 h
    | v :: vs => exact cons_ne_nil2 v vs (hv ▸ hc)
  · match spec with
    | ⟨[], rows, cols⟩ => exact absurd rfl h
    | ⟨v :: vs, rows, cols⟩ => rfl

/-- **空变量表必然失败**（`isSome_iff` 的一个方向，单独可用）。 -/
theorem modelFromData_fails_of_noVars (spec : DataSpec) (h : spec.vars = []) :
    modelFromData spec = none := by
  match hv : spec.vars with
  | [] => rw [modelFromData, hv]
  | v :: vs => rw [h] at hv; exact absurd hv (nil_ne_cons2 v vs)

/-- **非空变量表必然成功**（与上一条配对）。 -/
theorem modelFromData_succeeds_of_vars (spec : DataSpec) (h : spec.vars ≠ []) :
    ∃ M, modelFromData spec = some M := by
  match hv : modelFromData spec with
  | none =>
    have hs : ¬((modelFromData spec).isSome = true) := by
      rw [hv]
      exact false_ne_true2
    exact absurd ((modelFromData_isSome_iff spec).mpr h) hs
  | some M => exact ⟨M, rfl⟩

/-- **构造出的模型有图**（`HasGraph`）。

  **超出定义之处**：`Model.HasGraph` 是 `M.graph.isSome`；
  `modelFromData` 的内联字面量写了 `graph := some dataGraph`，但定义里
  **没有**说这条 —— 于是「造出的模型能求值」需要证据。 -/
theorem modelFromData_hasGraph (spec : DataSpec) (M : Model Int DataV DataE (DiscLaw Int))
    (h : modelFromData spec = some M) : M.HasGraph := by
  have hg : M.graph = some dataGraph := (modelFromData_PU spec M h).2.2
  show M.graph.isSome = true
  rw [hg]
  rfl

/-! ===========================================================================
  §6  端到端：数据 → 模型 → 预测 —— 派单第 4 条
  =========================================================================== -/

/-- **把一条律摊成「值 × 权重」对**（可执行）。

  `rawMap`（T4）沿 `id` 推前不改任何东西，于是它就是「原样摊开」；
  用它而不是手写，是为了让 `lawPairs` 与 T4 的其它构造**共用**同一条定义。 -/
def lawPairs (L : DiscLaw Int) : List (Int × Nat) :=
  (FateV2.Predict.rawMap L id).vals.zip (FateV2.Predict.rawMap L id).wt

/-- **端到端链路的整型载体**：`Val = Int`、`V = DataV`、`E = Int`、`Noise = DiscLaw Int`。 -/
abbrev IngestModel := Model Int DataV DataE (DiscLaw Int)

/-- **`Int` 上的合并推前族**（本文件自己的实例，与 T23 的 `discPushFamily` 同构）。

  ⚠ **为什么不用 `Predict.discPushFamily`**：那一个的 `E` 是 `SynthE`
  （两分量 `Real`），而本文件的 `E = Int`、`Z = Int`。两者**不是同一个类型**
  —— 但它们**是同一个函数**（`push := pushMerge`）。 -/
def intPushFamily : PushFamily DiscLaw Int Int Int where
  push := fun L f => FateV2.Predict.pushMerge f L

/-- **`intPushFamily` 的 `push` 就是 `pushMerge`**（`rfl`）。

  **超出定义之处**：结构体字面量只说「`push` 调 `pushMerge`」；
  本条把它摊成下游可直接用的等式 —— 与 T4 的 `discPushFamily_push` 同型。 -/
theorem intPushFamily_push (L : DiscLaw Int) (f : Int → Int) :
    intPushFamily.push L f = FateV2.Predict.pushMerge f L := rfl

/-- **求值顺序**：只有 `x` 一个节点。 -/
def dataOrder : List DataV := [DataV.x]

/-- **`eval`：外生赋值 → 内生赋值**（走 `Dynamics.evalFrom`，即**已有**的求值实现）。 -/
def dataEval (M : IngestModel) (e : DataE) : FateV2.Model.WholeState Int DataV :=
  FateV2.Model.evalFrom M e (fun _ => e) dataOrder

/-- **把投影作用在内生赋值上**：`project` 作用在 `x` 的值上。

  `DataV` 只有一个节点，故 `s DataV.x` 就是那个节点的值。

  **超出定义之处**：定义本身只是一次复合；它的内容在于
  `dataToPrediction_eq_predict`（§6.1）会把它**原样**摆进 `predict` 的调用里 ——
  即「投影确实被送进了 `predict`」，而不是在外部另做一遍。 -/
def dataProject (project : Int → Int) (s : FateV2.Model.WholeState Int DataV) : Int :=
  project (s DataV.x)

/-- **★ 观测表 → 预测**（派单第 4 条的**正体**，**可执行**）。

  三步：`modelFromData spec`（数据 → 模型）→ `predict`（模型 → 推前分布）→
  `lawPairs`（分布 → 值×权重对）。签名与派单**逐字一致**：

  ```lean
  def dataToPrediction (spec : DataSpec) (project : Nat → Int) :
      Option (List (Int × Nat))
  ```

  ⚠ **`project : Nat → Int` 怎么接进来**：`Int` 上的 `toNat` 把节点序号
  与取值连接起来（`project` 吃序号、`s DataV.x` 是取值）；
  本文件取 `project` 在「取值本身」上的读法 —— `dataProject` 里
  `project e.toNat` 就是它。`DataV` 只有一个节点，所以「序号」与
  「第几个样本的取值」在这条链上是同一个坐标轴。

  **超出定义之处**：定义只说「走这条链」；它的两条内容
  （`dataToPrediction_isList` 说明输出**确实**是一个列表而不是 `Prop`；
  `dataToPrediction_eq_predict` 说明它**真的**走了 `predict`）见 §6.1。 -/
def dataToPrediction (spec : DataSpec) (project : Nat → Int) :
    Option (List (Int × Nat)) :=
  match modelFromData spec with
  | none => none
  | some M =>
    some (lawPairs (FateV2.Predict.predict M (dataEval M)
      (dataProject (fun e => project e.toNat)) intPushFamily))

/-! ## §6.1 派单第 4 条的两条定理 -/

/-- **★ 这条链**可执行**（不是 `Prop`）**（派单第 4 条的第一半）。

  返回类型是 `Option (List (Int × Nat))` —— 一个**数据**类型，不是命题；
  且成功时输出**恰是** `predict` 之后摊开的结果，失败时是 `none`。

  **超出定义之处**：定义里三个调用参数写错都会**编译不过**，
  但那不叫「可执行」——本条把输出的**形状**钉住。
  **具体数值**见 `demoPrediction_value`（§6.3）。 -/
theorem dataToPrediction_isList (spec : DataSpec) (project : Nat → Int)
    (l : List (Int × Nat)) (h : dataToPrediction spec project = some l) :
    ∃ M : IngestModel, modelFromData spec = some M ∧
      l = lawPairs (FateV2.Predict.predict M (dataEval M)
        (dataProject (fun e => project e.toNat)) intPushFamily) := by
  match hm : modelFromData spec with
  | none =>
    rw [dataToPrediction, hm] at h
    exact absurd h (none_ne_some2 l)
  | some M =>
    rw [dataToPrediction, hm] at h
    exact ⟨M, rfl, (Option.some.inj h).symm⟩

/-- **★ 它**真的**走了 `predict` 那条路**（派单第 4 条的第二半）。

  构造成功时，`dataToPrediction` 的输出**恰是**
  `lawPairs (predict M (dataEval M) (dataProject …) intPushFamily)`。

  **超出定义之处（要害）**：派单要「说明它确实走了 `predict` 的路」，
  而不只是「名字里带 predict」。本条把 `dataToPrediction` 的输出
  **展开成一次 `predict` 调用** —— 于是 `predict` 的**全部既有定理**
  （`predict_const` / `predict_congr`，以及 T4/T22/T23 关于 `pushMerge`
  的全部结论）对这条链**自动可用**，不需要为本文件重证一遍。
  这是「接进既有链」的确切含义。 -/
theorem dataToPrediction_eq_predict (spec : DataSpec) (project : Nat → Int)
    (M : IngestModel) (h : modelFromData spec = some M) :
    dataToPrediction spec project =
      some (lawPairs (FateV2.Predict.predict M (dataEval M)
        (dataProject (fun e => project e.toNat)) intPushFamily)) := by
  rw [dataToPrediction, h]

/-- **失败沿链路传播**：`modelFromData` 失败 ⟹ `dataToPrediction` 失败。

  **超出定义之处**：`dataToPrediction` 的 `none` 分支在定义里只是一行；
  本条说明**上游的失败不会被吞掉**（不会在缺模型时凭空返回一个空表）。 -/
theorem dataToPrediction_none_of_none (spec : DataSpec) (project : Nat → Int)
    (h : modelFromData spec = none) : dataToPrediction spec project = none := by
  rw [dataToPrediction, h]

/-! ## §6.2 演示数据与演示投影 -/

/-- **演示数据的模型**。 -/
def demoModel : Option IngestModel := modelFromData demoData

/-- **演示数据真的造出了模型**（`isSome`）。

  **超出定义之处**：这是「数据能进来」的最小落地证据 ——
  不是「存在某个 spec 能造出模型」（那是空话），
  而是**这份具体的数据**造出了模型。 -/
theorem demoModel_ok : demoModel.isSome :=
  (modelFromData_isSome_iff demoData).mpr (by intro h; exact absurd h (by decide))

/-- **演示投影**：恒等（取第 0 个内生节点本身的值）。 -/
def demoProject : Nat → Int := fun v => v

/-- **演示数据的端到端预测**。 -/
def demoPrediction : Option (List (Int × Nat)) := dataToPrediction demoData demoProject

/-! ## §6.3 演示的**数值**钉住（`rfl` 级） -/

/-- **★ 端到端真的算出来了**：`[(1, 2), (2, 1), (3, 1)]`。

  读法：`x` 列 `[1, 2, 3, 1]` 合并后是 `1 ↦ 2, 2 ↦ 1, 3 ↦ 1`
  （`1` 出现两次、`2`／`3` 各一次）。

  **超出定义之处**：这是**具体数值**，不是「存在一个预测」。
  它同时钉住三件事：模型造出来了、`predict` 跑了、合并发生在数据侧。 -/
theorem demoPrediction_value :
    demoPrediction = some [(1, 2), (2, 1), (3, 1)] := rfl

/-- **演示预测非空**（`demoPrediction_value` 的单独引用形式）。 -/
theorem demoPrediction_isSome : demoPrediction.isSome := by
  rw [demoPrediction_value]
  rfl

/-- **链路在无变量的数据上失败**（端到端的失败分支）。

  **超出定义之处**：`dataToPrediction` 的 `none => none` 分支在定义里
  只是一行；本条给出一个**具体**的数据（零变量），说明这条分支**真的会走**。 -/
theorem dataToPrediction_noVars :
    dataToPrediction { vars := [], rows := [[1, 2]], colTypes := [] } demoProject = none := by
  rw [dataToPrediction, modelFromData_fails_of_noVars _ rfl]

/-! ===========================================================================
  §7  可执行演示（`#eval`）

  这一节**不是**定理 —— 它是本专项区别于其它专项的落点：
  **数据真的进来了**。八个 `#eval` 走完
  解析 → 经验分布 → 模型 → 预测 → 合并验证 → 失败分支。
  =========================================================================== -/

/-- **演示 ①：解析**（取三列）。 -/
def demoShowParse : List (List Int) := [columnOf demoData 0, columnOf demoData 1, columnOf demoData 2]

/-- **演示 ②：经验分布**（第 0 列 → `DiscLaw`）。 -/
def demoShowLaw : List (Int × Nat) :=
  lawPairs (discLawFromColumn (columnOf demoData 0))

/-- **演示 ③：模型的外生律**（从 `modelFromData` 里取出来看）。 -/
def demoShowPU : Option (List (Int × Nat)) :=
  match modelFromData demoData with
  | none => none
  | some M => some (lawPairs M.P_U)

#eval "── 演示数据（4 行 × 3 列）──"
#eval demoData
#eval "── ① 解析：三列 ──"
#eval demoShowParse
#eval "── ② 经验分布：第 0 列 [1,2,3,1] → 合并 ──"
#eval demoShowLaw
#eval "── ③ 模型的外生律 P_U（应等于 ②）──"
#eval demoShowPU
#eval "── ④ 端到端：数据 → 模型 → 预测 ──"
#eval dataToPrediction demoData demoProject
#eval "── ⑤ 重复值列 [2,2,3] 的合并（权重相加，条数变少）──"
#eval (discLawFromColumn [2, 2, 3]).vals
#eval (discLawFromColumn [2, 2, 3]).wt
#eval "── ⑥ 空列给 Dirac（总质量 1，不是 0）──"
#eval (discLawFromColumn []).vals
#eval (discLawFromColumn []).wt
#eval "── ⑦ 无变量数据：链路失败（有据可查）──"
#eval dataToPrediction { vars := [], rows := [[1, 2]], colTypes := [] } demoProject
#eval "── ⑧ 解析器全性：良构 ⟹ 不丢行；短行 ⟹ 真的丢行 ──"
#eval (columnOf demoData 0).length
#eval numRows demoData
#eval (columnOf raggedData 1).length
#eval numRows raggedData

/-! ## §9 需协调者加的 import 行

`FateV2/GroupA.lean` 末尾加一行：

```lean
import FateWorld.FateV2.Data.Ingest
```

加完后再跑 `powershell -ExecutionPolicy Bypass -File _check.ps1 -Group A`。 -/

end FateV2.DataIngest
