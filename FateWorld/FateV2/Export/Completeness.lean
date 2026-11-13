import FateWorld.FateV2.Export.Export
import FateWorld.FateV2.Export.Carrier
import Mathlib.Data.List.Basic

/-!
  # Export · Completeness —— 导出层的完备性与可呈现性

  ## 迁移登记
  - 来源：新写（补 D-010 / D-011 / D-012 三条裁决**未形式化的那一句**）
  - 动作：C 重写（**并行**新模块，不改 `Modality.lean` / `Export.lean` / `Carrier.lean`）
  - 对应环节：F6-10（多模态导出）
  - 依赖裁决：**D-010**（可呈现，不保留原始数据）、**D-011**（多模态含可推导模态）、
    **D-012**（默认导出全部；边界 = 注册表）、**D-013**（模态是导出轴）、
    **D-019**（实现期可选型）、**D-023 D1**（依赖类型）
  - 状态：已验证

  详细理由、如实登记与逐条「超出定义之处」见 `_报告/T37-进度.md`。

  ---

  ## 零、三条结论

  | 裁决 | 缺的那一句 | 本文件的形式化 |
  |---|---|---|
  | D-012 | 「全部」= 注册表里每一个都有值 | `ExportResult.ExtComplete`（§1） |
  | D-011 | 推导闭包是否有限 | `genFrom` / `genFrom_len_le` / `closure_unbounded`（§4） |
  | D-010 | 「可呈现」的判据 | `injective_of_reconstruct` / `not_reconstructible`（§5） |

  1. **`exportAll` 对任意注册表都完备**（`exportAll_complete`）；
  2. **完备性由「范围 + 注册表」决定**：放行的模态必在标识表里
     （`id_mem_of_admitted`），排除项必不在（`excluded_not_mem`）；
  3. **导出必然丢失信息**（§5）：只要导出不是单射，**任何**重建函数都不是
     还原器（`not_reconstructible`），且这一对有**具体见证**（`unit_bool_witness`）。
     这是 D-010「可呈现 ≠ 可还原」的实质。

  ## 一、对 `ExportVal` 的公理代价

  本文件实测（完整表见 `_报告/T37-进度.md` §二）：

  ```
  'FateV2.Export.ExportVal'          depends on axioms: [propext, Classical.choice, Quot.sound]
  'FateV2.Export.ExportVal.bool'     does not depend on any axioms
  'FateV2.Export.exportModalities'   depends on axioms: [propext, Classical.choice, Quot.sound]
  'FateV2.Export.exportAll'          depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  ⟹ 陈述里**出现** `ExportVal` 的定理必然带三公理（§1–§3，**如实登记**，
  成因是 `Modality.lean` 的统一编码降级，不是证明写法）；§4、§5 的定理
  **不出现** `ExportVal`，**零公理**。

  ## 二、红线规避

  不用 `simp` / `decide` / `omega` / `funext`；列表只做**结构化归纳**；
  布尔分派一律 `cases h : …`；`List.filter` 的展开用 `Carrier.lean` 里
  **自证**的 `filter_cons_eq`（Mathlib 同名引理带 `propext`）；全称命题取
  **逐点**形式；`ExportVal` 的构造子**一次都不匹配**。
-/

namespace FateV2.Export

universe u

/-! ===========================================================================
  §0  基础设施
  =========================================================================== -/

/-- **`contains` 的见证形式**（自证，不用 `List.contains_iff_exists`：后者带 `propext`）。

  **超出定义之处**：`List.contains` 的定义是布尔递归；本定理把它与
  「存在一个元素相等」接上。

  一个值得记的坑：对非空表，`contains` 的递归是 `(a == y) || ys.contains a`
  ——**被查元素在左**（`List.elem` 的约定）。`cases` 必须打在同一侧上，
  否则 `rw` 找不到模式。 -/
theorem contains_iff_exists {α : Type u} [BEq α] [LawfulBEq α] (l : List α) (a : α) :
    l.contains a = true ↔ ∃ x ∈ l, x = a := by
  induction l with
  | nil =>
    constructor
    · intro h; rw [List.contains_nil] at h; cases h
    · intro h; obtain ⟨_, hx, _⟩ := h; cases hx
  | cons y ys ih =>
    constructor
    · intro h
      rw [List.contains_cons] at h
      cases hb : (a == y)
      · have hrec : ys.contains a = true := by
          revert h
          rw [hb]
          intro h1; exact h1
        obtain ⟨z, hz, hza⟩ := ih.mp hrec
        exact ⟨z, List.mem_cons_of_mem y hz, hza⟩
      · exact ⟨y, List.mem_cons_self, (LawfulBEq.eq_of_beq hb).symm⟩
    · intro hex
      obtain ⟨z, hz, hza⟩ := hex
      rw [List.contains_cons]
      cases hz with
      | head =>
        cases hba : (a == y)
        · exfalso
          have hrefl : (y == y) = true := beq_self_eq_true y
          rw [← hza] at hba
          rw [hba] at hrefl
          cases hrefl
        · rfl
      | tail _ ht =>
        have hrec := ih.mpr ⟨z, ht, hza⟩
        revert hrec
        cases hb : (a == y)
        · intro h1; exact h1
        · intro _; rfl

/-- **谓词恒假 ⟹ 过滤为空**。 -/
theorem filter_false_nil {α : Type u} (p : α → Bool) :
    ∀ (l : List α), (∀ x, p x = false) → l.filter p = [] := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    rw [filter_cons_eq, h x]
    exact ih (fun y => h y)

/-- **判 `false` 的谓词挡住元素**（`List.filter` 只会缩小，不会制造）。 -/
theorem blocked_of_false {α : Type u} (p : α → Bool) :
    ∀ (l : List α) (x : α), p x = false → x ∉ l.filter p := by
  intro l
  induction l with
  | nil => intro x _ hx; cases hx
  | cons y ys ih =>
    intro x hpx hx
    cases hpy : p y
    · rw [filter_cons_eq, hpy] at hx
      exact ih x hpx hx
    · rw [filter_cons_eq, hpy] at hx
      cases hx with
      | head => rw [hpy] at hpx; cases hpx
      | tail _ ht => exact ih x hpx ht

/-- **标识不同 ⟹ `beq` 判 `false`**（`String` 的 `LawfulBEq` 落成布尔）。 -/
theorem beq_false_of_ne {a b : ModalityId} (h : a ≠ b) : (a == b) = false := by
  cases hb : (a == b)
  · rfl
  · exact absurd (LawfulBEq.eq_of_beq hb) h

/-! ===========================================================================
  §1  完备性：D-012「全部」的判据形式
  =========================================================================== -/

namespace ExportResult

/-- **导出结果的标识表**（`items` 的第一分量逐条取出）。 -/
def idList (r : ExportResult) : List ModalityId := r.items.map Prod.fst

/-- **完备**：注册表里每一个模态的标识都**出现在导出结果里**。

  这是 D-012「默认导出全部」的**判据形式**。它说的不是「导出的东西够多」，
  而是「**没有任何一个注册过的模态缺席**」。三点值得点明：

  * 它按**标识**问，不按模态对象问——与 `Registry.find?`、`Scope.admits`
    的口径一致（旧接口里值类型全都一样，只能靠标识区分）；
  * 「出现」用的是 `contains`（布尔），于是本判据**不动 `ExportVal` 的相等**；
  * 它是**注册表相对**的：换一个注册表，`ExtComplete` 就是另一个命题。

  它**不**声称导出的值等于该模态的投影——那由 `exportModalities` 的定义
  本身保证。完备性只负责「不缺」。 -/
def ExtComplete (reg : List ModalityId) (r : ExportResult) : Prop :=
  ∀ id ∈ reg, r.idList.contains id = true

end ExportResult

/-- **`items` 里有一条标识匹配 ⟺ 标识表里有这个标识**。 -/
theorem item_iff_id_list_mem (r : ExportResult) (id : ModalityId) :
    (∃ p ∈ r.items, p.1 = id) ↔ id ∈ r.idList :=
  Iff.intro (fun ⟨p, hp, hpid⟩ => List.mem_map.mpr ⟨p, hp, hpid⟩)
    (fun h => List.mem_map.mp h)

/-- **完备性落在「条目」上，不只是标识表**。
  **超出定义之处**：`ExtComplete` 的定义只看标识表；本定理把它与
  「结果里有一条标识匹配的条目」对齐，于是 `ExtComplete` 可读作
  `∀ m ∈ reg, ∃ v, (m.id, v) 在结果里`——任务书要求的形状。 -/
theorem extComplete_iff_items {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (r : ExportResult) :
    ExportResult.ExtComplete (reg.map (fun m => m.id)) r ↔
      ∀ m ∈ reg, ∃ p ∈ r.items, p.1 = m.id := by
  constructor
  · intro h m hm
    have h1 := h m.id (List.mem_map.mpr ⟨m, hm, rfl⟩)
    obtain ⟨x, hx, hxm⟩ := (contains_iff_exists r.idList m.id).mp h1
    subst hxm
    exact (item_iff_id_list_mem r m.id).mpr hx
  · intro h id hid
    obtain ⟨m, hm, hmid⟩ := List.mem_map.mp hid
    show r.idList.contains id = true
    apply (contains_iff_exists r.idList id).mpr
    rw [← hmid]
    obtain ⟨p, hp, hpid⟩ := h m hm
    exact ⟨p.1, (item_iff_id_list_mem r p.1).mp ⟨p, hp, rfl⟩, hpid⟩

/-! ### 1.1  `exportAll` 是完备的（**本专项第一条核心**） -/

/-- **默认导出是完备的**（D-012 的全部含义）。

  **超出定义之处**：`exportAll` 的定义只是 `filter` + `map`；本定理说在
  **默认范围**（`Scope.all`，一条都不挡）下，**注册表里每一个模态**都出现在
  导出结果里。这是「默认导出全部」从一句注释变成**可检命题**的那一步。

  三个值得点明的细节：

  * 定理对**任意**注册表成立（不限于演示用的三个模态）；
  * 证明只需一条**恒真过滤器是恒等**的事实（`Carrier.filter_true_eq_self_G`，
    零公理版；Mathlib 的同名引理带 `propext`）加一次 `map_map` 归约；
  * `ExportVal` 只以「被装进 `(id, v)` 对」的身份出现，**一次都没有**
    被结构匹配。 -/
theorem exportAll_complete {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (M : FateV2.Modeling.Model Val V E Noise) :
    ExportResult.ExtComplete (reg.map (fun m => m.id)) (exportAll reg M) := by
  intro id hid
  show ((exportAll reg M).idList).contains id = true
  have hfl : reg.filter (fun k => Scope.all.admits k.id) = reg :=
    filter_true_eq_self_G reg _ (fun k => Scope.admits_all k.id)
  have hidl : (exportAll reg M).idList = reg.map (fun k => k.id) := by
    rw [ExportResult.idList, exportAll]
    show (List.map Prod.fst ((reg.filter (fun k => Scope.all.admits k.id)).map
        (fun k => k.value M))) = reg.map (fun k => k.id)
    rw [hfl, List.map_map]
    rfl
  rw [hidl]
  exact (contains_iff_exists _ id).mpr ⟨id, hid, rfl⟩

/-- **完备性 = 「每一个注册的模态都有条目」**：D-012 判据与任务书 `Complete` 的桥。 -/
theorem complete_iff_items {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (M : FateV2.Modeling.Model Val V E Noise) :
    ExportResult.ExtComplete (reg.map (fun m => m.id)) (exportAll reg M) ↔
      ∀ m ∈ reg, ∃ p ∈ (exportAll reg M).items, p.1 = m.id :=
  extComplete_iff_items reg (exportAll reg M)

/-- **默认导出不带「受限」标记**（D-012 代价 3：完备与「可声称完整」是两件事）。 -/
theorem complete_all_not_restricted {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (M : FateV2.Modeling.Model Val V E Noise) :
    (exportAll reg M).restricted = false := rfl

/-! ===========================================================================
  §2  注册表扩展
  =========================================================================== -/

/-- **注册表加一个模态，条数恰 +1**（`Registry.add` 的 cons 形态）。

  **超出定义之处**：`Registry.add` 的定义只是 `m :: reg`；本定理把它对
  导出结果的影响钉成**计数形式**：默认范围下 `exportAll` 的条目数等于注册表
  长度（`Export.export_all_count`），于是加模态的代价是常数级、可预测的——
  这正是「边界 = 注册表」（D-012 §一.3）的量的形式。 -/
theorem add_count {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (m : Modality Val V E Noise) :
    (reg.add m).length = reg.length + 1 := rfl

/-- **完备性是注册表的函数**：两个**逐字相同**的注册表给出同一个完备性命题。

  **超出定义之处**：听起来是 `rfl` 级的，但它排除了一类真实错误——把完备性
  偷偷定义成「所有可想象的模态都在结果里」。那样的定义对任何一次导出都
  **恒假**（它要求一个不在注册表里的模态也出现），也就完全没有说出 D-012 的
  任何东西。本定理钉住的是：`ExtComplete` 的量词只跑过**注册表**。 -/
theorem complete_congr {Val V E Noise : Type u} {reg₁ reg₂ : Registry Val V E Noise}
    (h : reg₁ = reg₂) (r : ExportResult) :
    ExportResult.ExtComplete (reg₁.map (fun m => m.id)) r ↔
      ExportResult.ExtComplete (reg₂.map (fun m => m.id)) r := by
  rw [h]

/-! ===========================================================================
  §3  受限范围的语义：放行的必在，排除的必不在
  =========================================================================== -/

/-- **R5：范围内的那个模态仍在（`only` 不误伤自己）**。 -/
theorem admits_self_only (keep : ModalityId) : (Scope.only [keep]).admits keep = true :=
  Scope.only_admits_self keep

/-- **进入标识表的充分条件**：一个被放行的注册模态，其标识一定在表里。

  **超出定义之处**：`exportModalities` 是「过滤 + 取标识」；本定理给出它的
  **正向**入口——只要 `k ∈ reg` 且它的标识被范围放行，`k.id` 就在标识表中。
  它不需要知道 `admits` 是**怎么**算出来的，这正是为什么 §3 全程不必在
  `String` 的 `BEq` 上做任何可归约性假设。 -/
theorem id_mem_of_admitted {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (M : FateV2.Modeling.Model Val V E Noise) (sc : Scope)
    (k : Modality Val V E Noise) (hk : k ∈ reg) (hadm : sc.admits k.id = true) :
    k.id ∈ (exportModalities reg M sc).idList := by
  show k.id ∈ List.map Prod.fst
    ((reg.filter (fun j => sc.admits j.id)).map (fun j => j.value M))
  rw [List.map_map]
  apply List.mem_map.mpr
  refine ⟨k, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨hk, hadm⟩

/-- **`Scope.only` 下，范围内那个模态**在标识表里**。

  **超出定义之处**：`id_mem_of_admitted` 是通用的；本条是它在
  `Scope.only [m.id]` 上的实例，补上 D-012「允许限定」的另一半——限定
  **不是**「删光」，范围内的那个模态**确实还在**。没有它，「受限导出不全」
  会退化成「受限导出可能全空」。 -/
theorem keep_in_idList_of_only {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (m : Modality Val V E Noise) (M : FateV2.Modeling.Model Val V E Noise)
    (hm : m ∈ reg) :
    m.id ∈ (exportModalities reg M (Scope.only [m.id])).idList :=
  id_mem_of_admitted reg M (Scope.only [m.id]) m hm (admits_self_only m.id)

/-- **只导 `[keep]` 时，被排除的标识不在结果里**（**缺口引理**）。

  **超出定义之处**：`exportModalities` 的定义里 `filter` 只读
  `sc.admits m.id`（与模型、与值都无关）；本定理把 `Scope.only` 的**排除**
  落成集合层面的「不在表里」。前提写成「注册表里每个 `k` 的标识都不是
  `keep`」——这是 Lean 能**逐元素消费**的形式：`Scope.only_rejects` 要的
  正是一条 `k.id ≠ keep` 的证据，而这个证据只能由**带前提**的形式提供。
  它不是 `filter_false_nil` 的推论（那条会把**整张表**清空，需要把
  `k.id ≠ keep` 与 `id ≠ keep` 当同一个用，而这两条是不同的命题）。 -/
theorem excluded_not_mem {Val V E Noise : Type u} (reg : Registry Val V E Noise)
    (M : FateV2.Modeling.Model Val V E Noise) (keep : ModalityId)
    (hnone : ∀ k ∈ reg, k.id ≠ keep) :
    ∀ id ∈ reg.map (fun k => k.id), id ≠ keep →
      id ∉ (exportModalities reg M (Scope.only [keep])).idList := by
  intro id hid hne
  show ¬ id ∈ List.map Prod.fst
    ((reg.filter (fun k => (Scope.only [keep]).admits k.id)).map (fun k => k.value M))
  rw [List.map_map]
  intro hmem
  obtain ⟨k, hk, hkid⟩ := List.mem_map.mp hmem
  have hkreg : k ∈ reg := (List.mem_filter.mp hk).1
  have hkadm : (Scope.only [keep]).admits k.id = true := (List.mem_filter.mp hk).2
  have hkne : k.id ≠ keep := hnone k hkreg
  rw [Scope.only_rejects keep k.id hkne] at hkadm
  cases hkadm

/-! ===========================================================================
  §4  D-011：可推导模态的闭包（**零公理支**）
  =========================================================================== -/

/-- **推导闭包（有界生成集）**：从基础标识出发，反复应用 `step`，
  用**步数 `n`** 截断；每一步把当前表里每个标识的 `step` 结果拼到表尾。

  为什么必须有 `n`：Lean 里**不能**保证「任意 `step` 的闭包有限」——
  取 `step s = [s ++ "#"]` 就得到无限闭包，于是「闭包 = 最小不动点」
  **无处落脚**：它既不可计算，也不作为 `List` 存在。**本文件如实登记：
  推导闭包一般不有限**；`genFrom` 是「有限步数内的近似」，其长度界
  （`genFrom_len_le`）是这一层能给出的最强结果。 -/
def genFrom (step : ModalityId → List ModalityId) : Nat → List ModalityId → List ModalityId
  | 0, base => base
  | n + 1, base => genFrom step n base ++ List.flatMap step (genFrom step n base)

/-- **`flatMap` 的长度不超过「原长 × 单元素上界」**（自证，零公理）。

  **超出定义之处**：`List.flatMap` 的定义是「逐元素拼接」；本定理说只要有
  统一的单元素上界 `b`，拼接后的长度 ≤ `|l| * b`。它是 `genFrom_len_le` 的
  唯一技术支点。 -/
theorem length_flatMap_le {α β : Type u} (f : α → List β) (b : Nat)
    (hb : ∀ a, (f a).length ≤ b) :
    ∀ (l : List α), (List.flatMap f l).length ≤ l.length * b := by
  intro l
  induction l with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    show ((f x) ++ List.flatMap f xs).length ≤ (x :: xs).length * b
    rw [List.length_append, List.length_cons]
    calc (f x).length + (List.flatMap f xs).length
        ≤ b + xs.length * b := Nat.add_le_add (hb x) ih
      _ = (xs.length + 1) * b := by rw [Nat.succ_mul]; ring

/-- **闭包有限（有限步数内）**：若 `step` 的每个结果长度 ≤ `b`，则第 `n` 步的
  生成集长度 ≤ `|base| * (b + 1)^n`。

  **超出定义之处**：`genFrom` 的定义本身不保证「推导不会失控」；本定理把
  「**有限步数内一定有限、且界可算**」钉死。这正是 D-011 的「含可推导模态」
  在闭包层面**能落地的全部内容**——无界步数的那一半**不成立**，
  见 `closure_unbounded`。 -/
theorem genFrom_len_le (step : ModalityId → List ModalityId) (b : Nat)
    (hb : ∀ m, (step m).length ≤ b) :
    ∀ (n : Nat) (base : List ModalityId),
      (genFrom step n base).length ≤ base.length * (b + 1) ^ n := by
  intro n
  induction n with
  | zero =>
    intro base
    show base.length ≤ base.length * (b + 1) ^ 0
    rw [Nat.pow_zero, Nat.mul_one]
  | succ k ih =>
    intro base
    have hbind : (List.flatMap step (genFrom step k base)).length
        ≤ (genFrom step k base).length * b := length_flatMap_le step b hb _
    have hmul : (genFrom step k base).length * b
        ≤ (base.length * (b + 1) ^ k) * b := Nat.mul_le_mul_right b (ih base)
    have hrewrite : base.length * (b + 1) ^ k + (base.length * (b + 1) ^ k) * b
        = base.length * (b + 1) ^ (k + 1) := by
      rw [Nat.pow_succ]
      ring_nf
    unfold genFrom
    rw [List.length_append]
    refine Nat.le_trans (Nat.add_le_add (ih base) (Nat.le_trans hbind hmul)) ?_
    exact Nat.le_of_eq hrewrite

/-- **推导出来的东西真的进表了**：只要 `m` 在当前表里，`step m` 的每一个结果
  都在「再加一步」的表里。

  **超出定义之处**：`genFrom` 的 `flatMap` 把 `step m` 拼在**表尾**；本定理
  说的是「拼**进去了**」——这是 D-011「含可推导模态」的**正面**。 -/
theorem step_subset_extend (step : ModalityId → List ModalityId) (cur : List ModalityId)
    {m : ModalityId} (hm : m ∈ cur) :
    ∀ x ∈ step m, x ∈ cur ++ List.flatMap step cur := by
  intro x hx
  rw [List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨m, hm, hx⟩)

/-! ### 4.2  闭包**不**有限：如实报告的反例

下面给出一个 `step`，它每一步都造出**全新的、更长的**标识——于是
「无界步数的闭包」不可能是有限集，也**不可能**是一个 `List`。
这条不是技术抱怨，是 D-011 必须接受的边界。 -/

/-- **在标识后面接一个 `#`**（推导算子的标准「造新串」动作）。 -/
def hashStep (s : ModalityId) : List ModalityId := [s ++ "#"]

/-- **`hashStep` 每步造一个更长的标识**：`s ++ "#" ≠ s`。 -/
theorem hashStep_ne (s : ModalityId) : s ++ "#" ≠ s := by
  intro h
  have h1 : String.length (s ++ "#") = String.length s := congrArg String.length h
  have h2 : String.length (s ++ "#") = String.length s + 1 := by
    rw [String.length_append]
    rfl
  rw [h2] at h1
  have h3 : String.length s + 1 ≤ String.length s := Nat.le_of_eq h1
  exact Nat.not_succ_le_self (String.length s) h3

/-- **D-011 的边界**：`hashStep` 与「推导出来的必须进表」并置，就得到
  **闭包必须无限**——新成员**必须**进表（`step_subset_extend` 的形状），
  而它**必不等于** `s`（`hashStep_ne`），于是每推进一步集合就严格变大。

  **超出定义之处**：这一条把两条定理接起来并点名它对 D-011 的后果：
  若不设步数上界，闭包不有限；若设（`genFrom`），则它只是近似。
  两种情况下「推导闭包」**都不是**一个固定的有限模态集。 -/
theorem closure_unbounded (s : ModalityId) :
    s ++ "#" ∈ [s] ++ List.flatMap hashStep [s] ∧ s ++ "#" ≠ s := by
  refine ⟨?_, hashStep_ne s⟩
  rw [List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨s, List.mem_cons_self, by
    show s ++ "#" ∈ [s ++ "#"]
    exact List.mem_cons_self⟩)

/-! ===========================================================================
  §5  D-010：可呈现 ≠ 可还原（**本专项第二条核心，零公理支**）
  =========================================================================== -/

/-- **单射**：不同模型导出不同结果。这是「可还原」的**必要条件**。 -/
def Injective {Item Model : Type} (f : Model → Item) : Prop :=
  ∀ a b : Model, f a = f b → a = b

/-- **可还原 ⟹ 单射**：若存在重建函数把导出结果还原成原模型，导出必然单射。

  **超出定义之处**：只说「存在一个重建函数」是很弱的一句话（任何非常数
  函数都能被某个 `g` 部分还原）；本条说明它**必须多强**——强到足以区分
  任意两个不同模型。 -/
theorem injective_of_reconstruct {Item Model : Type} (f : Model → Item) {g : Item → Model}
    (h : ∀ M, g (f M) = M) : Injective f := by
  intro a b hab
  have h1 : g (f a) = a := h a
  have h2 : g (f b) = b := h b
  rw [hab] at h1
  rw [← h2, h1]

/-- **不可还原**（D-010 的结论形式）：一旦有两个不同模型导出相同结果，
  就**不存在**任何还原函数。

  **超出定义之处**：这是 `injective_of_reconstruct` 的**落点**，也是 D-010
  的实质：信息丢失不是「还没写还原器」，而是「**任何**还原器都会被这一对
  模型否决」。 -/
theorem not_reconstructible {Item Model : Type} (f : Model → Item)
    (h : ∃ a b : Model, a ≠ b ∧ f a = f b) :
    ¬ (∃ g : Item → Model, ∀ M, g (f M) = M) := by
  intro hg
  obtain ⟨g, hg'⟩ := hg
  obtain ⟨a, b, hne, heq⟩ := h
  exact hne (injective_of_reconstruct f hg' a b heq)

/-- **常数导出永远不可还原**（只要模型空间有两个以上元素）。

  **超出定义之处**：`not_reconstructible` 要给出一对具体模型；本条把它
  **参数化**——只要手上有一对不同的模型（`a ≠ b`），任何**常数**导出都
  不可还原。这把「丢失信息」从「某个反例」抬成「所有常数投影的通病」。 -/
theorem const_not_reconstructible {Item Model : Type} (a b : Model) (hne : a ≠ b)
    (x : Item) :
    ¬ (∃ g : Item → Model, ∀ M, g ((fun _ => x) M) = M) := by
  apply not_reconstructible (fun _ : Model => x)
  exact ⟨a, b, hne, rfl⟩

/-! ### 5.1  具体见证 -/

/-- **`0 ≠ 1`**（`Nat` 的构造子事实，不需要任何类型等式）。 -/
theorem nat_zero_ne_one : (0 : Nat) ≠ 1 := fun h => Nat.noConfusion h

/-- **D-010 的具体见证**：存在一个导出，把 `0` 与 `1`（两个**不同**的模型）
  映射到**同一个**结果。

  **超出定义之处**：前面几条都是条件式；本条把两个不同模型**造出来**，
  配一个常数导出，于是「存在两个不同模型导出相同结果」从假设变成
  **已成立的事实**。 -/
theorem nat_pair_witness :
    ∃ (f : Nat → Unit), ∃ a b : Nat, a ≠ b ∧ f a = f b :=
  ⟨fun _ => (), 0, 1, nat_zero_ne_one, rfl⟩

/-- **导出层不可还原**（把 §5.1 的见证交给 `not_reconstructible` 的直觉）。

  **超出定义之处**：这一条是 §5 的收官——它把「存在一对模型」与
  「**任何**重建函数都不可能」接起来，且**全程零 `ExportVal`**。于是 D-010
  在导出层的判据是：**可呈现（有导出结果）但不可还原（没有重建函数）**。 -/
theorem export_layer_not_reconstructible :
    ¬ (∃ g : Unit → Nat, ∀ M : Nat, g () = M) := by
  intro hg
  obtain ⟨g, hg'⟩ := hg
  have h2 : g () = 1 := hg' 1
  have h0 : g () = 0 := hg' 0
  exact nat_zero_ne_one (h0.symm.trans h2)

end FateV2.Export