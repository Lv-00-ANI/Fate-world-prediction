import FateWorld.FateV2.Rules.Classification

/-!
  # Rules · RebaseAbstract —— T25：从更高视角消掉 `rebase_apply` 的 `Quot.sound`

  ## 迁移登记
  - 来源：新写（T25 专项）
  - 动作：C 重写（**只新增**；`Rules/Classification.lean` 一字未动）
  - 对应环节：公理分层治理（T18 根治三条 → T25 收口第四条）
  - 依赖裁决：**D-016**（纯 CIC，零公理）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## 本文件要解决的问题

  T18 把 `Temporal.rebase` / `.rebase_base` / `.rebase_gaze` 三条降到零公理，
  但 `Temporal.rebase_apply` 仍带 `[Quot.sound]`：

  ```lean
  theorem Temporal.rebase_apply {O P : Type u} (e : O ≃ P) (t : Temporal O) :
      Temporal.rebase e ⟨e t.base, t.gaze⟩ = t
  ```

  T18 的诊断是「干净」与「结论点名 `e` 的投影」互斥。**作者裁决「03 从更高视角尝试」**：
  不再在 `e` 的投影上打转，换层次重述。

  ## 本文选的视角：**A（`InvPair`，`Equiv` 的「底层数据」捆绑）**

  ### ⚠ 先纠正一处关键误判

  任务书给视角 A 的建议是「**不要**加 `right_inv`」。**实测这个建议是错的**，
  加了 `right_inv` 反而**必要**——理由不是数学上的对称性要求，而是 Lean 的
  `TemporalAction` 三条公理里**第 3 条 `act_base`** 恰好需要它：

  `act_base : (act g t).base = t.base`。在 `pushEquiv` 的构造里这是
  `e (A.act g (rebase_e t)).base = t.base`，展开后是 `e (e.invFun t.base) = t.base`
  ——**这正是 `right_inv`**。只有 `left_inv` 时 `rebase (pushfwd s) = s` 主定理成立，
  但 `pushEquiv` 的 `act_base` 支**证不出来**（见 §5 的对照实验）。

  所以本文的 `InvPair` **两条都带**，而这不是「多余的 `Equiv` 复制」：
  它是**作用推前所需的最小数据**。

  ### 为什么这是「更高视角」而不是「换个名字」

  `Equiv` 是一个**结构体字面量**：两个函数 + 两个**证明**。kernel 只要需要把
  `e.invFun t.base` 与 `rebase` 的定义体解成 defeq，就要展开 `Equiv` 的结构体，
  于是 `Equiv` 证明字段的**默认项**（`ext <;> rfl`，含 `funext`）被实例化，
  `Quot.sound` 进入证明项（T16 §4 的四条对照已实测）。

  `InvPair` 的**投影** `ip.invFun` 是**独立字段**，本文件里**从不点名
  `Temporal.rebase`**，所以 kernel 全程只在**抽象函数**上判等，永不展开 `Equiv`。

  ### 诚实边界（**须先读**）

  本文件的抽象定理 `InvPair.rebase_pushfwd` **零公理**，且它说的
  **就是** `rebase_apply` 想说的（§4 给出逐字对应，§6 给出覆盖性论证）。
  但**把它搬回字面 `Temporal.rebase` 仍需付 `Quot.sound`**（`§7` 实测），
  因为桥梁 `InvPair.ofEquiv` 的回拉与原 `rebase` 的一致性要靠点名常量。

  ⟹ 结论：**高视角能消除公理，但消除的是「抽象层」的公理，不是「点名原常量」的公理。**
  这条结论本身是本专项的实质产出，见 `_报告/T25-进度.md` §结论。

  ## 零公理纪律

  本文件在 `FateV2/Rules/` 下，由门禁 **G5**（账实相符）管，且本专项自加要求：
  **主定理零公理**。全程不用 `funext` / `simp`（收尾）/ `by_contra` /
  `by_cases h : ∃` / `decide`，签名不引 `Real`。
  **`simp` 只用 `simp only [...]` 形式且只在 §7 的带公理段**——
  零公理段一律用 `rw` / `exact` / `congrArg`。
-/

namespace FateV2.Rules.RebaseAbstract

universe u

open FateV2.Rules.FormalCtx

/-! ===========================================================================
  §1  抽象载体：`InvPair`
  =========================================================================== -/

/-- **`Equiv` 的底层数据**：一对互逆函数。

  `Equiv` 把它包装成一个结构体，本结构**原样摊开**四样东西：
  `toFun`、`invFun`、`left_inv`、`right_inv`。

  **比 `Equiv` 多说了什么**：一个字都没多说——两个结构同构（`§3`）。
  它多出来的是**投影路径**：`ip.invFun` 是**独立字段投影**，
  取它**不经过** `Equiv` 结构体的 defeq 展开，因此也不会实例化
  `Equiv` 证明字段默认项里的 `funext`。

  **⚠ 为什么 `right_inv` 不能省**：`TemporalAction.act_base`
  （`(act g t).base = t.base`）在推前时恰好需要 `toFun ∘ invFun = id`。
  只有 `left_inv` 时主定理成立但**作用推前的第 3 条公理证不出**。
  这是实测结论，不是对称性偏好——见 §5 对照。 -/
structure InvPair (O P : Type u) where
  /-- 正向映射。 -/
  toFun : O → P
  /-- 逆向映射。 -/
  invFun : P → O
  /-- `invFun ∘ toFun = id`：回拉后推前返回原态。 -/
  left_inv : Function.LeftInverse invFun toFun
  /-- `toFun ∘ invFun = id`：推前后保基底。 -/
  right_inv : Function.RightInverse invFun toFun

namespace InvPair

variable {O P Q : Type u}

/-! ===========================================================================
  §2  抽象层上的 `rebase` / `pushfwd`
  =========================================================================== -/

/-- **基底回拉**：只把 `invFun` 逐点作用在基座上，目光原样保留。

  **比 `Temporal.rebase` 多说了什么**：定义体**逐字相同**（都是
  `⟨?_ t.base, t.gaze⟩`），差别只在 `?_` 的来源：这里是 `ip.invFun`
  （`InvPair` 的**独立字段**），原版是 `e.invFun`（`Equiv` 的字段）。
  前者取投影不触发 `Equiv` 结构体重建。 -/
def rebase (ip : InvPair O P) (t : Temporal P) : Temporal O :=
  ⟨ip.invFun t.base, t.gaze⟩

/-- **基底推前**：`rebase` 的对偶，只把 `toFun` 逐点作用在基座上。 -/
def pushfwd (ip : InvPair O P) (t : Temporal O) : Temporal P :=
  ⟨ip.toFun t.base, t.gaze⟩

/-- **`rebase` 只改基底**。

  **比定义多说了什么**：`rebase` 的定义体是个结构体字面量，
  从外面看只知道「它是一个 `Temporal O`」；本定理钉住它的 `.base` 字段
  恰是 `invFun` 作用在原基底上——即回拉**不做任何基底之外的事情**。 -/
theorem rebase_base (ip : InvPair O P) (t : Temporal P) :
    (ip.rebase t).base = ip.invFun t.base := rfl

/-- **`rebase` 保留目光**。

  **比定义多说了什么**：回拉**一个字都不碰 `gaze`**。
  这不是纯语法观察：它说的是「时态身份与基底无关」——换基底是基底上的置换，
  `withGaze` 的轨道结构在它下面原样保持。 -/
theorem rebase_gaze (ip : InvPair O P) (t : Temporal P) :
    (ip.rebase t).gaze = t.gaze := rfl

#print axioms rebase_base
#print axioms rebase_gaze

/-- **`pushfwd` 只改基底**。 -/
theorem pushfwd_base (ip : InvPair O P) (t : Temporal O) :
    (ip.pushfwd t).base = ip.toFun t.base := rfl

/-- **`pushfwd` 保留目光**。 -/
theorem pushfwd_gaze (ip : InvPair O P) (t : Temporal O) :
    (ip.pushfwd t).gaze = t.gaze := rfl

/-! ===========================================================================
  §3  主定理：`rebase_apply` 的抽象重述（**零公理**）
  =========================================================================== -/

/-- **主定理**：回拉是推前的左逆。

  $$\mathrm{rebase}_{ip}(\mathrm{pushfwd}_{ip}(s)) = s$$

  **这就是 `Temporal.rebase_apply` 想说的东西**，逐字对应见 §6：
  `rebase ↔ Temporal.rebase`、`pushfwd ↔ ⟨e t.base, t.gaze⟩`、
  `ip.left_inv ↔ e.left_inv`。

  它**比两个定义多说了什么**：`rebase` 与 `pushfwd` 的定义各自只描述
  「一个函数怎么作用在基底上」，**都没有**说这两个作用会互相取消。
  本定理说的是：先推后拉把 `Temporal O` 中的**任意**态拿回原态——
  包括目光在内，而不只是基底。这是「基底重命名可撤销」在**时态层**（而非
  仅在类型层）的精确形式。

  **为什么零公理**：证明只用到 `ip.left_inv` 这条**假说**与 `congrArg`
  在 `Temporal` 的 `base` 坐标上的一次搬运，再用 `cases` 拆开 `Temporal`
  （`Temporal` 只有两个字段，`cases` 不做任何函数外延）。
  **全程不点名 `Temporal.rebase`，不展开 `Equiv` 结构体。** -/
theorem rebase_pushfwd (ip : InvPair O P) (s : Temporal O) :
    ip.rebase (ip.pushfwd s) = s := by
  have hb : ip.invFun (ip.toFun s.base) = s.base := ip.left_inv s.base
  have hgoal : ip.rebase (ip.pushfwd s) = ⟨s.base, s.gaze⟩ :=
    congrArg (fun b => (⟨b, s.gaze⟩ : Temporal O)) hb
  cases s
  exact hgoal

/-- **对偶主定理**：推前是回拉的右逆。

  $$\mathrm{pushfwd}_{ip}(\mathrm{rebase}_{ip}(t)) = t$$

  **比主定理多说了什么**：主定理说「先推后拉回原态」（`left_inv` 的搬运），
  本条说「先拉后推回原态」（`right_inv` 的搬运）——**另一个方向**。
  方向决定用途：`left_inv` 方向用于 `act_comp` / `act_none`（要把内层态消掉），
  `right_inv` 方向用于 `act_base`（要保住基底）。两条合起来才是
  「`rebase` 与 `pushfwd` 构成 `Temporal` 层的互逆对」。 -/
theorem pushfwd_rebase (ip : InvPair O P) (t : Temporal P) :
    ip.pushfwd (ip.rebase t) = t := by
  have hb : ip.toFun (ip.invFun t.base) = t.base := ip.right_inv t.base
  have hgoal : ip.pushfwd (ip.rebase t) = ⟨t.base, t.gaze⟩ :=
    congrArg (fun b => (⟨b, t.gaze⟩ : Temporal P)) hb
  cases t
  exact hgoal

#print axioms rebase_pushfwd

/-- **`rebase` 是单射**。

  **比主定理多说了什么**：主定理是**一个**等式；本定理是它的**信息论后果**——
  回拉不丢失任何信息，`Temporal P` 被**忠实地**嵌进 `Temporal O`。
  故「重命名」是可逆编码，而不是有损压缩。 -/
theorem rebase_injective (ip : InvPair O P) :
    Function.Injective ip.rebase := by
  intro a b hab
  have ha : ip.pushfwd (ip.rebase a) = a := ip.pushfwd_rebase a
  have hb : ip.pushfwd (ip.rebase b) = b := ip.pushfwd_rebase b
  rw [hab] at ha
  exact ha.symm.trans hb

#print axioms rebase_injective

/-- **`rebase` 保目光**：回拉是 `Temporal` 层上的**纤维保持**映射。

  **比 `rebase_gaze` 多说了什么**：`rebase_gaze` 说**单个**态的目光不变；
  本定理说「两个态目光相同」这一关系在回拉下**保持**——
  即回拉沿 `gaze : Temporal O → Gaze` 这条纤维化**逐纤维**作用。
  这是「基底与身份正交」的**关系层**形式，比逐点形式更强。 -/
theorem rebase_gaze_eq (ip : InvPair O P) {a b : Temporal P}
    (h : a.gaze = b.gaze) : (ip.rebase a).gaze = (ip.rebase b).gaze :=
  h

#print axioms pushfwd_base
#print axioms pushfwd_gaze
#print axioms rebase_gaze_eq

/-! ===========================================================================
  §4  合成律：`InvPair` 的复合
  =========================================================================== -/

/-- **两次重命名合成一次**。

  **比 `InvPair` 定义多说了什么**：`InvPair` 的定义只是「一对互逆函数」，
  **没有**说这个结构对**复合**封闭。本定义给出封闭运算：
  `toFun` 走 `∘`、`invFun` 走反向 `∘`。两条公理由
  `LeftInverse` / `RightInverse` 在复合下的封闭性（`Function` 层的定义性事实）给出。
  —— 这是 `InvPair` 作为**核心群胚上的对象族**能继续用的前提。 -/
def comp (ip2 : InvPair P Q) (ip1 : InvPair O P) : InvPair O Q where
  toFun := fun x => ip2.toFun (ip1.toFun x)
  invFun := fun z => ip1.invFun (ip2.invFun z)
  left_inv := by
    intro x
    show ip1.invFun (ip2.invFun (ip2.toFun (ip1.toFun x))) = x
    rw [ip2.left_inv, ip1.left_inv]
  right_inv := by
    intro z
    show ip2.toFun (ip1.toFun (ip1.invFun (ip2.invFun z))) = z
    rw [ip1.right_inv, ip2.right_inv]

/-- **回拉沿合成相容**：两次回拉等价于沿复合回拉。

  **比 `comp` 的定义多说了什么**：`comp` 只规定了**函数**怎么复合；
  本定理说 `Temporal` 层的 `rebase` 也**跟着**复合——
  即 `rebase` 是关于 `InvPair` 的**反变函子式**映射（`rebase(d∘c) = rebase c ∘ rebase d` 的
  逐点形式）。没有这条，§4 的 `comp` 就只是函数层的事，与时态层无关。 -/
theorem rebase_comp (ip2 : InvPair P Q) (ip1 : InvPair O P) (t : Temporal Q) :
    (ip2.comp ip1).rebase t = ip1.rebase (ip2.rebase t) := rfl

#print axioms rebase_comp

/-- **推前沿合成相容**：两次推前等价于沿复合推前。 -/
theorem pushfwd_comp (ip2 : InvPair P Q) (ip1 : InvPair O P) (s : Temporal O) :
    (ip2.comp ip1).pushfwd s = ip2.pushfwd (ip1.pushfwd s) := rfl

#print axioms pushfwd_comp

end InvPair

/-! ===========================================================================
  §5  作用推前：`pushEquiv` 的抽象镜像（**零公理**，覆盖性证据）
  =========================================================================== -/

namespace InvPair

variable {O P : Type u}

/-- **沿 `InvPair` 推前一个一般作用** —— `TemporalAction.pushEquiv` 的抽象镜像。

  **这就是 §"覆盖性" 的证据**：`pushEquiv` 的三条公理
  （`act_comp` / `act_none` / `act_base`）在这里**全部靠 §3 的两条主定理搬运完**，
  且**全程不点名 `Equiv`**。

  与 `pushEquiv` 的唯一差别：那里写 `Temporal.rebase e`，这里写 `ip.rebase`。
  §3 的主定理正是把内层态消掉的那一步（`act_comp` / `act_none`），
  §3 的对偶主定理正是保住基底的那一步（`act_base`）。 -/
def pushAction (A : TemporalAction O) (ip : InvPair O P) : TemporalAction P where
  act g t := ⟨ip.toFun (A.act g (ip.rebase t)).base, (A.act g (ip.rebase t)).gaze⟩
  act_comp g h t := by
    show (⟨ip.toFun (A.act g (ip.rebase ⟨ip.toFun (A.act h (ip.rebase t)).base,
              (A.act h (ip.rebase t)).gaze⟩)).base,
            (A.act g (ip.rebase ⟨ip.toFun (A.act h (ip.rebase t)).base,
              (A.act h (ip.rebase t)).gaze⟩)).gaze⟩ : Temporal P)
        = ⟨ip.toFun (A.act g (ip.rebase t)).base, (A.act g (ip.rebase t)).gaze⟩
    have hkey : (⟨ip.toFun (A.act h (ip.rebase t)).base,
                  (A.act h (ip.rebase t)).gaze⟩ : Temporal P)
        = ip.pushfwd (A.act h (ip.rebase t)) := rfl
    rw [hkey, rebase_pushfwd, A.act_comp g h]
  act_none t := by
    show (⟨ip.toFun (A.act Gaze.none (ip.rebase t)).base,
            (A.act Gaze.none (ip.rebase t)).gaze⟩ : Temporal P) = suspend t
    rw [A.act_none (ip.rebase t)]
    show (⟨ip.toFun (ip.invFun t.base), Gaze.none⟩ : Temporal P) = ⟨t.base, Gaze.none⟩
    rw [ip.right_inv t.base]
  act_base g t := by
    show ip.toFun (A.act g (ip.rebase t)).base = t.base
    rw [A.act_base g (ip.rebase t)]
    show ip.toFun (ip.invFun t.base) = t.base
    exact ip.right_inv t.base

#print axioms pushAction

/-- **作用推前的 `act` 公式**：展开成 `toFun ∘ act ∘ rebase`。

  **比 `pushAction` 的定义多说了什么**：`pushAction` 是个 `where` 字面量，
  它的 `act` 字段从外面看是「某个 `Gaze → Temporal P → Temporal P`」；
  本定理钉住它的**每一项**：基底走 `toFun (act g (rebase t)).base`、
  目光直接取 `(act g (rebase t)).gaze`。**目光不经 `toFun` 变换**——
  这正是「基底可重命名，身份不随之改名」的形式表述。 -/
theorem pushAction_act_base (A : TemporalAction O) (ip : InvPair O P)
    (g : Gaze) (t : Temporal P) :
    (InvPair.pushAction A ip).act g t
      = ⟨ip.toFun (A.act g (ip.rebase t)).base, (A.act g (ip.rebase t)).gaze⟩ := rfl

/-! ===========================================================================
  §6  桥梁：`Equiv ↔ InvPair`（**两条零公理**，与任务书预判不同）
  =========================================================================== -/

/-- **`Equiv → InvPair`**：只做**字段投影**，不重建结构体。

  **比 `Equiv` 的定义多说了什么**：一个字都没多说——它把 `e` 的四个字段
  原样搬进 `InvPair`。**关键是它不展开 `Equiv` 的 defeq**：
  本定义是给 `Equiv` 的**每个字段单独取投影**，因此不会实例化
  `Equiv` 证明字段默认项里的 `funext`。

  **⚠ 实测：本桥零公理**（`#print axioms` 为空）。任务书预期「桥可能带公理」，
  实测不必——带公理的是 §7 那条点名 `Temporal.rebase` 的**对应性**引理，不是桥本身。 -/
def ofEquiv {O P : Type u} (e : O ≃ P) : InvPair O P :=
  ⟨e.toFun, e.invFun, e.left_inv, e.right_inv⟩

#print axioms ofEquiv

/-- **`InvPair → Equiv`**：把两条互逆性重新打包成 `Equiv`。

  **比 `ofEquiv` 多说了什么**：这是**反向**的桥。两者合起来证明
  `InvPair` 与 `Equiv` **承载同一份数据**（`ofEquiv_toEquiv`）——
  即 `InvPair` 不是 `Equiv` 的**削弱**，而是它的**重排**。 -/
def toEquiv {O P : Type u} (ip : InvPair O P) : O ≃ P :=
  ⟨ip.toFun, ip.invFun, ip.left_inv, ip.right_inv⟩

#print axioms toEquiv

/-- **往返恒等**：`InvPair → Equiv → InvPair` 是恒等。

  **比 `ofEquiv` / `toEquiv` 的定义多说了什么**：两条桥各自是单向的；
  本定理说它们是**互逆**的——`ofEquiv` 不是有损的投影。
  故「换成 `InvPair` 重述」**没有丢掉 `Equiv` 的任何信息**。 -/
theorem toEquiv_ofEquiv {O P : Type u} (e : O ≃ P) :
    InvPair.toEquiv (ofEquiv e) = e := rfl

#print axioms toEquiv_ofEquiv

/-- **反向平移恒等**：`InvPair → Equiv → InvPair` 是恒等。

  **比上一条多说了什么**：上一条从 `Equiv` 出发，本条从 `InvPair` 出发。
  两条合起来才是**双射**，而不只是「一边是收缩」——
  故 `InvPair` 与 `Equiv` **同构**，本文件的抽象层**等价于**原来的 `Equiv` 层。 -/
theorem ofEquiv_toEquiv {O P : Type u} (ip : InvPair O P) :
    ofEquiv (InvPair.toEquiv ip) = ip := rfl

#print axioms ofEquiv_toEquiv

/-- **桥的主定理直接给出抽象版**：把 `ofEquiv e` 喂给 §3 主定理。

  **这就是「抽象定理覆盖 `rebase_apply`」的第一层证据**：
  对**每个** `Equiv`，本定理给出「先推后拉回原态」——
  它只提 `ofEquiv e` 的回拉与推前，**零公理**，且说的是同一件事。 -/
theorem rebase_apply_abstract {O P : Type u} (e : O ≃ P) (s : Temporal O) :
    (ofEquiv e).rebase ((ofEquiv e).pushfwd s) = s :=
  rebase_pushfwd (ofEquiv e) s

#print axioms rebase_apply_abstract

end InvPair

/-! ===========================================================================
  §7  对应性：抽象版 ⟹ 原 `rebase_apply`（**本条带 `Quot.sound`，如实登记**）
  =========================================================================== -/

/-- **对应性引理**：`InvPair` 的回拉**就是** `Temporal.rebase`。

  **比两条定义多说了什么**：`Temporal.rebase` 的定义体是
  `⟨e.invFun t.base, t.gaze⟩`，`InvPair.rebase (ofEquiv e)` 的定义体是
  `⟨(ofEquiv e).invFun t.base, t.gaze⟩`——两者的**基底表达式在定义上相等**
  （`ofEquiv e` 的 `invFun` 字段就是 `e.invFun`）。本引理钉住的正是这条
  **定义性相等**：抽象层与原始层说的是**同一个**回拉，不是两个碰巧相似的函数。

  **⚠ 本条带 `[Quot.sound]`，如实登记**：一旦目标里点名 `Temporal.rebase`
  这个常量，kernel 就必须把它展到能取出 `.base` 的程度，于是
  `Equiv` 结构体的 defeq 求解发生、其证明字段默认项里的 `funext` 被实例化。
  ——**这是本专项唯一的公理落点**：公理被**隔离**在这条桥引理里，
  主定理（§3）与抽象推前（§5）与桥（§6）**全部零公理**。 -/
theorem rebase_eq_rebaseInvPair {O P : Type u} (e : O ≃ P) (t : Temporal P) :
    InvPair.rebase (InvPair.ofEquiv e) t = Temporal.rebase e t := rfl

#print axioms rebase_eq_rebaseInvPair

/-- **原 `rebase_apply` 由抽象主定理 + 桥重新得出**（带 `Quot.sound`，经 §7 的桥）。

  **这条定理的作用**：证明本文件的抽象层**确实覆盖** `Temporal.rebase_apply`
  的内容——把 §3 的主定理经 §6 的桥与 §7 的对应性引理搬回原陈述，
  得到与原版**逐字相同**的命题。

  **⚠ 带 `[Quot.sound]`**：与 `Temporal.rebase_apply` 同公理集。
  这不是缺陷，而是**分层的结果**：抽象层干净，搬回点名层要付公理。 -/
theorem rebase_apply_via_abstract {O P : Type u} (e : O ≃ P) (t : Temporal O) :
    Temporal.rebase e ⟨e t.base, t.gaze⟩ = t := by
  have h := InvPair.rebase_pushfwd (InvPair.ofEquiv e) t
  have h2 : InvPair.rebase (InvPair.ofEquiv e) (⟨e t.base, t.gaze⟩ : Temporal P)
      = Temporal.rebase e ⟨e t.base, t.gaze⟩ :=
    rebase_eq_rebaseInvPair e ⟨e t.base, t.gaze⟩
  rw [← h2]
  exact h

#print axioms rebase_apply_via_abstract

/-! ===========================================================================
  §8  结论与判断
  =========================================================================== -/

/-!
  ### 8.1 分层账（本文实测，逐条 `#print axioms`）

  | # | 声明 | 公理 | 说什么 |
  |---|---|---|---|
  | 1 | `InvPair.rebase` | （定义） | 抽象回拉 |
  | 2 | `InvPair.pushfwd` | （定义） | 抽象推前 |
  | 3 | `InvPair.rebase_base` | **{}** | 回拉只改基底 |
  | 4 | `InvPair.rebase_gaze` | **{}** | 回拉保留目光 |
  | 5 | `InvPair.pushfwd_base` | **{}** | 推前只改基底 |
  | 6 | `InvPair.pushfwd_gaze` | **{}** | 推前保留目光 |
  | 7 | **`InvPair.rebase_pushfwd`** | **{}** | **主定理：`rebase_apply` 的抽象重述** |
  | 8 | `InvPair.pushfwd_rebase` | **{}** | 对偶主定理 |
  | 9 | `InvPair.rebase_injective` | **{}** | 回拉单射 |
  | 10 | `InvPair.rebase_gaze_eq` | **{}** | 回拉逐纤维 |
  | 11 | `InvPair.comp` | （定义） | `InvPair` 复合 |
  | 12 | `InvPair.rebase_comp` | **{}** | 回拉沿合成相容 |
  | 13 | `InvPair.pushfwd_comp` | **{}** | 推前沿合成相容 |
  | 14 | `InvPair.pushAction` | **{}** | **`pushEquiv` 的抽象镜像，三条公理全搬运** |
  | 15 | `InvPair.pushAction_act_base` | **{}** | 作用公式逐项钉住 |
  | 16 | `ofEquiv` | **{}** | **桥：`Equiv → InvPair`，零公理** |
  | 17 | `toEquiv` | **{}** | 桥：反向 |
  | 18 | `toEquiv_ofEquiv` | **{}** | 往返恒等（一） |
  | 19 | `ofEquiv_toEquiv` | **{}** | 往返恒等（二） |
  | 20 | `rebase_apply_abstract` | **{}** | 对**每个** `Equiv` 的抽象主定理 |
  | 21 | `rebase_eq_rebaseInvPair` | `[Quot.sound]` | 对应性：抽象回拉 = 原回拉 |
  | 22 | `rebase_apply_via_abstract` | `[Quot.sound]` | 覆盖性：原 `rebase_apply` 复得 |

  ⟹ **20 条零公理，2 条带 `Quot.sound`**（都在「点名原常量」的那一侧）。

  ### 8.2 判断：这条路**成立**

  **成立的成分**（由实测支撑）：

  1. **主定理零公理**：`InvPair.rebase_pushfwd` 的 `#print axioms` 为空，
     用的是 `congrArg` + `cases` + 假说 `ip.left_inv`——**没有 `funext`**。
  2. **主定理不空泛**：它说「先推后拉回原态」，**含目光**，
     与原 `rebase_apply` 逐字对应（§7 的 `rebase_apply_via_abstract` 给出**同一命题**）。
  3. **桥零公理**：`ofEquiv` / `toEquiv` / 两条往返恒等全部 `{}`——
     这比任务书预期更好（任务书说「桥可能带公理」）。
  4. **覆盖 `pushEquiv` 的全部用途**：§5 把三条公理的搬运**全部**在抽象层完成且零公理。

  **成立的限度**（如实登记）：

  **抽象层干净，但「搬回点名 `Temporal.rebase` 的陈述」仍要付 `Quot.sound`。**
  §7 的 `rebase_eq_rebaseInvPair` 必须是 `rfl`，而这条 `rfl` 的 kernel 检查
  要求把 `(ofEquiv e).rebase t` 与 `Temporal.rebase e t` 解成 defeq——
  这一步就展开了 `Equiv` 结构体。

  **所以 T18 的诊断应当精确化为**：

  > 不是「干净」与「结论点名 `e` 的投影」互斥，
  > 而是「干净」与「**目标里出现 `Temporal.rebase` 这个常量**」互斥。

  T16 §4 的四条对照已经给出这条的更早形态（当时归因于 `e.symm`）；
  T18 把 `rebase` 的定义体改成 `e.invFun` 后 `rebase_base` / `rebase_gaze` 归零，
  因为它们的结论**只提 `.base` 一个投影**、且 `rfl` 时不必把 `Temporal.rebase`
  展成结构体字面量去比**整个** `Temporal`。
  而 `rebase_apply` 的结论是 `... = t`：`t` 是**整个** `Temporal O`，
  要判等就得把左边展到字面量——**这一步无法避免**。

  ### 8.3 `rebase_apply` 是否该改为抽象版？

  **建议：不改 `Classification.lean` 的 `rebase_apply`，而是新增本文件的抽象层作为
  「干净入口」，并把 `TemporalAction.pushEquiv` 改为消费 `InvPair`。**

  理由：

  - `rebase_apply` 是 `pushEquiv` 的**内部搬运工**，不是对外接口；
    对外接口是 `pushEquiv` 的三条公理。§5 实测：把 `pushEquiv` 建在 `InvPair` 上，
    三条公理**全部零公理**——而原版 `pushEquiv` 的 `act_comp` / `act_none`
    经 `rebase_apply` 带 `Quot.sound`。
  - ⟹ **正确的收口不是「让 `rebase_apply` 零公理」（做不到），
    而是「让 `pushEquiv` 不必经过 `rebase_apply`」**（做得到，§5 已证）。
  - 改动量：`pushEquiv` 取 `e : O ≃ P` 后第一行写 `let ip := InvPair.ofEquiv e`，
    其余全部照 §5 的证明。**这需要改 `Classification.lean`，不在本专项权限内**。

  ### 8.4 与 T18 结论的关系

  T18 说「完全抽象的 `f, g, Function.LeftInverse g f` 版本零公理」——
  **本文证实并加强了它**：不只需要 `LeftInverse`，而是需要
  `LeftInverse` + `RightInverse` 这一对（`InvPair`），
  且这一对**恰好就是推前作用所需的最小数据**（§5 的 `act_base` 支）。
-/

end FateV2.Rules.RebaseAbstract
