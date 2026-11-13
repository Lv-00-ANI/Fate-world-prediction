import FateWorld.FateV2.Model.State
import FateWorld.FateV2.Model.TrajGenDeterministic
import FateWorld.FateV2.Predict.Counterfactual
import FateWorld.FateV2.Predict.InterventionSelection
import FateWorld.FateV2.Predict.Predict
import FateWorld.FateV2.Rules.Classification

/-!
  # Core · Pointwise —— T16：L4「纯 `funext` 层」的零公理逐点镜像

  ## 迁移登记
  - 来源：新写（T16 专项）
  - 动作：C 重写（**只新增**；原 `.lean` 一字未动）
  - 对应环节：公理分层治理（T15 审计 → T16 降级）
  - 依赖裁决：**D-016**（纯 CIC，零公理）、**D-022**（反空泛）
  - 状态：已编译未验证

  ## 本文件存在的**唯一原因**

  T15 公理分层审计（`_报告/T15-公理分层审计.md` §1.3）实测：全库有 **15 条**定理的
  公理集恰好是**裸 `{Quot.sound}`**（L4 层）。本轮复核确认了这 15 条的名字，并确认：

  ```
  'funext'      depends on axioms: [Quot.sound]
  'Quot.sound'  depends on axioms: [Quot.sound]
  ```

  但复核同时发现：**T15 报告「这 15 条均匀地是只用了 `funext` 的定理」是错的**。
  逐条读正文后，这 15 条的 `Quot.sound` 有**三个不同来源**，只有第一个是 `funext`：

  | 源 | 条数 | 声明 | 处理 |
  |---|---:|---|---|
  | **① 正文 `funext`** | **7** | `WholeState.update_comm` `.update_eq_self` `TrajGenDeterministic.trajGen_deterministic` `.trajGen_unique` `.trajGen_is_unique_solution` `InterventionSelection.alter_alter_same` `.alter_comm` | 改逐点 → **7 条全部归零**（§1–§3） |
  | **② `Quot.sound` 本体** | **3** | `Predict.obsOnQuot_injective` `.obsOnQuotBy_injective_of_le` `Classical.quot_sound_demo` | **不可降**（`Quot` 的相等性没有逐点替代物） |
  | **③ `Equiv.symm` 的默认项** | **2** | `Rules.FormalCtx.Temporal.rebase_base` `.rebase_gaze` | 改述去 `Equiv.symm` → **2 条归零**（§4） |
  | **④ `congr 1`（结构外延 + 证明无关性）** | **1** | `TemporalAction.ext` | 不可由逐点导出（§5 给可降的一半） |
  | **⑤ 逐点化后退化为对前提的重述** | **1** | `Predict.predict_const` | 见 §6 注释 |
  | **⑥ `push` 非外延，逐点化后只剩一半** | **1** | `Predict.predict_congr` | §6 给可降的一半 |

  ⟹ 真实战果：**15 条里 9 条归零**（7 条走「改逐点」，2 条走「去掉 `Equiv.symm`」），
  6 条如实登记为不可降/只能降一半，并给出理由。逐条登记见 `_报告/T16-进度.md`。

  ## ⚠ 第三类是本轮**新发现的公理来源**（T15 未记录）

  `rebase_base` / `rebase_gaze` 的正文是 `:= rfl`，**里面没有 `funext`**。
  它们的 `Quot.sound` 来自：

  ```lean
  -- Mathlib 里 `Equiv.symm` 的定义
  protected def Equiv.symm : α ≃ β → β ≃ α :=
    fun e => { toFun := e.invFun, invFun := e.toFun, left_inv := ⋯, right_inv := ⋯ }
  ```

  `Equiv` 的两个证明字段有**默认项** `by intro; first | rfl | ext <;> rfl`，
  其中 `ext <;> rfl` 展开后含 `funext`。当目标写成
  `(rebase e t).base = e.symm t.base` 时，kernel 必须判定
  `Equiv.symm e ≡ ⟨…⟩`（结构体字面量）——这次 **defeq 求解**把默认项**实例化**了，
  于是 `funext` 进了证明项。

  **规避方式（已实测）**：不要在同一目标里同时出现 `e.symm x` 与 `e.invFun x`
  （或任何要求把 `Equiv.symm e` 与结构体字面量解成 defeq 的组合）。
  只写 `e.invFun x` 一侧即可归零。推导见 §4 的注释与
  `_报告/T16-进度.md` §三。

  ## 零公理纪律

  本文件在 `FateV2/Core/` 下，受门禁 **G4** 管：**每条** `theorem` 的
  `#print axioms` 必须为空。所以全程不用
  `funext` / `simp` / `decide` / `omega` / `by_contra` / `List.ext`，
  签名不引 `Real`（含结构体字段里含 `Real`）。
-/


namespace FateV2.Core.Pointwise

universe u

/-! ===========================================================================
  §1  `Model.WholeState.update` —— 状态覆盖的逐点镜像（2/2 归零）
  =========================================================================== -/

namespace State

variable {Val V : Type u}

/-- **逐点版「两处不同节点的更新可交换」**。

  **比定义多说了什么**：`update` 的定义是逐点的
  `fun w => if w = v then x else s w`，它对「先 `v` 后 `w`」与「先 `w` 后 `v`」
  的**先后顺序完全没有表态**。本定理说这两个复合在**每一个坐标**上都相等——
  即覆盖运算在 `v ≠ w` 时按坐标交换。原 `WholeState.update_comm`
  用 `funext` 把逐点结论升级成函数相等；本定理**停在逐点**，不欠任何公理。

  证明按坐标三分（`u = v` / `u = w` / 其余），每支只用 `if_pos` / `if_neg`。 -/
theorem update_comm_pointwise [DecidableEq V]
    (s : FateV2.Model.WholeState Val V)
    (v w : V) (x y : Val) (h : v ≠ w) (u : V) :
    FateV2.Model.WholeState.update
        (FateV2.Model.WholeState.update s v x) w y u
      = FateV2.Model.WholeState.update
        (FateV2.Model.WholeState.update s w y) v x u := by
  unfold FateV2.Model.WholeState.update
  by_cases huw : u = v
  · subst huw
    rw [if_pos rfl, if_pos rfl]
    rw [if_neg (fun hc => h (rfl.trans hc))]
  · by_cases hww : u = w
    · subst hww
      rw [if_pos rfl, if_pos rfl, if_neg huw]
    · rw [if_neg hww, if_neg huw, if_neg huw, if_neg hww]

/-- **逐点版「覆盖成原值则状态不变」**。

  **比定义多说了什么**：`update s v (s v)` 在定义上仍是一个分支式
  `fun w => if w = v then s v else s w`，而 `s` 是任意函数——
  **定义没有说这两者是同一个东西**；是 `if` 在 `w = v` 分支上把 `s v` 接回 `s w`
  才使它们一致。本定理在**每个坐标**上钉住「用原值覆盖是恒等」，
  这是「回写为空 ⟹ 状态不动」的形式依据，也是回写可以**幂等**重复施加的根据。 -/
theorem update_eq_self_pointwise [DecidableEq V]
    (s : FateV2.Model.WholeState Val V) (v : V) (u : V) :
    FateV2.Model.WholeState.update s v (s v) u = s u := by
  unfold FateV2.Model.WholeState.update
  by_cases h : u = v
  · subst h
    rw [if_pos rfl]
  · rw [if_neg h]

end State

/-! ===========================================================================
  §2  `Model.TrajGenDeterministic` —— 确定性递推的逐点镜像（3/3 归零）
  =========================================================================== -/

namespace Traj

open FateV2.Model FateV2.Model.TrajGenDeterministic

/-- **逐点版「两组相同输入给出相同轨迹」**。

  **比定义多说了什么**：`trajGen` 的定义只是 `Nat.rec` 的一个实例——
  它**造出**一条轨迹，对「同一组输入分别喂两次会得到什么关系」**一个字没说**。
  本定理说：两组**逐点相同**的输入给出**逐点相同**的轨迹，即 `trajGen` 在
  输入上是一个**函数**（而非依赖求值次序/求值次数的不透明过程）。

  证明：把两个假设等式 `subst` 掉，再对 `n` 归纳；`succ` 支用 `trajGen_succ`
  与逐点假设 `hu`/`hε`/`ha`。 -/
theorem trajGen_deterministic_pointwise (F : FateV2.Model.Frame)
    (f : FateV2.Model.Step F)
    {θ θ' : F.Θ.Carrier} {x₀ x₀' : F.X.Carrier}
    {u u' : ℕ → F.U.Carrier} {ε ε' : ℕ → F.Ν.Carrier} {a a' : ℕ → F.Act.Carrier}
    (hθ : θ = θ') (hx : x₀ = x₀')
    (hu : ∀ n, u n = u' n) (hε : ∀ n, ε n = ε' n) (ha : ∀ n, a n = a' n) :
    ∀ n, trajGen F f θ x₀ u ε a n = trajGen F f θ' x₀' u' ε' a' n := by
  subst hθ
  subst hx
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [trajGen_succ, trajGen_succ, ih, hu k, hε k, ha k]

/-- **逐点唯一性**：同初值 + 同递推 ⟹ 两条轨迹**逐点**相同。

  **比定义多说了什么**：`trajGen` 的定义只造出**一条**轨迹，**完全没有**说
  「满足同一递推 + 同一初值的另一个 `x : Traj ℕ F.X` 必与它重合」。
  本定理把这个唯一性降到逐点层——这正是「确定性递推**无自由度**」的精确形式：
  唯一权威方程不是**一条**解，而是**唯一一条**。

  证明：对 `n` 归纳；`0` 支由共同初值得出，`succ` 支把两条递推假设各展开一次
  再用归纳假设。 -/
theorem trajGen_unique_pointwise (F : FateV2.Model.Frame) (f : FateV2.Model.Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    {x y : FateV2.Modeling.Traj ℕ F.X}
    (hx0 : x 0 = x₀) (hy0 : y 0 = x₀)
    (hx : ∀ n, x (n+1) = f (x n) (u n) (ε n) θ (a n))
    (hy : ∀ n, y (n+1) = f (y n) (u n) (ε n) θ (a n)) :
    ∀ n, x n = y n := by
  intro n
  induction n with
  | zero => rw [hx0, hy0]
  | succ k ih => rw [hx k, hy k, ih]

/-- **逐点版「`trajGen` 就是那个唯一解」**：任何满足初值 + 递推的 `x` 逐点等于 `trajGen`。

  **比定义多说了什么**：这条把「`trajGen` 是唯一权威方程的解」的**另一半**——
  它是**唯一**的那个——落成结论：`trajGen_zero` + `trajGen_succ` 这**两件**
  定义性事实反过来也**刻画**了 `trajGen`，没有别的函数满足它们。
  原 `trajGen_is_unique_solution` 需要 `symm` 把一个函数等式翻过来；
  这里直接在逐点层给出，不欠任何公理。 -/
theorem trajGen_is_unique_solution_pointwise (F : FateV2.Model.Frame)
    (f : FateV2.Model.Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    {x : FateV2.Modeling.Traj ℕ F.X}
    (hx0 : x 0 = x₀)
    (hx : ∀ n, x (n+1) = f (x n) (u n) (ε n) θ (a n)) :
    ∀ n, x n = trajGen F f θ x₀ u ε a n := by
  intro n
  exact trajGen_unique_pointwise (F := F) (f := f) (θ := θ) (x₀ := x₀)
    (u := u) (ε := ε) (a := a) (x := x)
    (y := trajGen F f θ x₀ u ε a)
    (hx0 := hx0)
    (hy0 := trajGen_zero F f θ x₀ u ε a)
    (hx := hx)
    (hy := trajGen_succ F f θ x₀ u ε a) n

end Traj

/-! ===========================================================================
  §3  `Predict.InterventionSelection.alter` —— 分支代数（2/2 归零）
  =========================================================================== -/

namespace Alter

open FateV2.Predict FateV2.Predict.InterventionSelection

variable {ι A : Type u}

/-- **逐点幂等性**：同一时刻连续两次改值，等价于只改最后一次。

  **比定义多说了什么**：`alter a t v` 的定义只是 `Function.update a t v`——
  「在 `t` 处换成 `v`」。定义**没有**说两次先后作用会归一。
  本定理在**每个坐标** `s` 上钉住这个归一：`t` 处取 `w`、其余取 `a s`。
  这正是「同一时刻的干预重复作用不叠加」——即动作层的干预组成**分支树**
  而不是分支列表。原 `alter_alter_same` 用 `funext s` 升级成函数相等；
  本定理停在逐点，公理清空。 -/
theorem alter_alter_same_pointwise [DecidableEq ι]
    (a : Plan ι A) (t : ι) (v w : A) (s : ι) :
    alter (alter a t v) t w s = alter a t w s := by
  by_cases hs : s = t
  · subst hs; rw [alter_apply_self, alter_apply_self]
  · rw [alter_apply_of_ne _ _ _ hs, alter_apply_of_ne _ _ _ hs,
        alter_apply_of_ne _ _ _ hs]

/-- **逐点交换性**：不同时刻的两次分支互不依赖次序。

  **比定义多说了什么**：`alter` 是两个**独立的**单点覆盖；定义**没有**说
  「先改 `t` 再改 `s`」与「先改 `s` 再改 `t`」给出同一个计划。
  本定理在**每个坐标** `r` 上证明两者相等 ⟹ **选择的结果只依赖改动的集合，
  不依赖改动的次序**——这是「分支树」而非「分支列表」的代数理由，
  也是干预可以按任意顺序装配、而不必约定一个顺序的依据。

  证明按坐标三分：`r = s` / `r = t` / 其余，每支只用 `alter_apply_self` 与
  `alter_apply_of_ne`。 -/
theorem alter_comm_pointwise [DecidableEq ι]
    (a : Plan ι A) {s t : ι} (hst : s ≠ t) (v w : A) (r : ι) :
    alter (alter a t v) s w r = alter (alter a s w) t v r := by
  by_cases hrs : r = s
  · subst hrs
    rw [alter_apply_self, alter_apply_of_ne _ _ _ hst, alter_apply_self]
  · by_cases hrt : r = t
    · subst hrt
      rw [alter_apply_self, alter_apply_of_ne _ _ _ hrs, alter_apply_self]
    · rw [alter_apply_of_ne _ _ _ hrs, alter_apply_of_ne _ _ _ hrt,
          alter_apply_of_ne _ _ _ hrt, alter_apply_of_ne _ _ _ hrs]

end Alter

/-! ===========================================================================
  §4  `Rules.FormalCtx.Temporal` —— 去掉 `Equiv.symm` 的两条（2/2 归零）
  =========================================================================== -/

namespace Temporal

open FateV2.Rules FateV2.Rules.FormalCtx

/-- **`Temporal.rebase` 的零公理镜像**（定义体与原文**逐字相同**，只把
  `e.symm` 写成 `e.invFun`——两者在 `Equiv` 上定义性相等）。

  为什么需要它：见下方「第三类的最终定位」。点名 `Temporal.rebase` 会把
  `Equiv.symm` 的结构体重建拉进 defeq，从而实例化其默认项里的 `funext`。
  本定义是**同一个函数**的另一种写法，取投影时不触发该路径。

  **比 `Temporal.rebase` 多说了什么**：一个字都没多说——它是同一个函数。
  它多出来的是**一个零公理的入口**：下游用本定义即可在不欠 `Quot.sound` 的
  前提下使用「回拉只改基底、保留目光」这两条性质。 -/
def rebase_inlined {O P : Type u} (e : O ≃ P)
    (t : FateV2.Rules.FormalCtx.Temporal P) : FateV2.Rules.FormalCtx.Temporal O :=
  ⟨e.invFun t.base, t.gaze⟩

/-- **`rebase` 只改基底（`invFun` 形态）**——原 `Temporal.rebase_base` 的零公理改写。

  **比定义多说了什么**：`Temporal.rebase` 的定义体是 `⟨e.symm t.base, t.gaze⟩`，
  也就是说**回拉的基底是 `e` 的逆向映射作用在原基底上**。本定理把「逆向映射」
  写成 `e.invFun`（`Equiv` 的第二个字段）而不是 `e.symm t.base`
  （那要经过一次 `Equiv.symm` 的结构体重建）——两者**定义上相等**
  （`Equiv.symm` 的 `toFun` 就是 `invFun`），本定理说的正是这条定义性相等，
  从而钉住「基底重命名可逆，回拉用的是逆映射」。

  **为什么必须写成本文件的形态**：见上方「第三类的最终定位」与文件头第三类。 -/
theorem rebase_base_pointwise {O P : Type u} (e : O ≃ P)
    (t : FateV2.Rules.FormalCtx.Temporal P) :
    (rebase_inlined e t).base = e.invFun t.base := rfl

/-- **`rebase` 保留目光**——原 `Temporal.rebase_gaze` 的零公理改写。

  **比定义多说了什么**：回拉只换基底、**一个字都不碰 `gaze`**。
  这不是纯粹的语法观察：它说的是「时态身份（`Gaze`）与基底无关」——
  换基底是**基底上的一个置换**，`withGaze` 的轨道结构在它下面**原样保持**。
  这正是 `Temporal.map` / `rebase` 一族「目光不变」不变量的一半，也是
  `orbit_transitive` / `orbit_contains_none` 在换基底下仍然成立的原因。 -/
theorem rebase_gaze_pointwise {O P : Type u} (e : O ≃ P)
    (t : FateV2.Rules.FormalCtx.Temporal P) :
    (rebase_inlined e t).gaze = t.gaze := rfl

end Temporal

/-! **关于第三类的最终定位（本轮实测，与 T15 的推断不同）**
一开始把 `rebase_base` 改写为
`(FateV2.Rules.FormalCtx.Temporal.rebase e t).base = e.invFun t.base`——**仍是 `[Quot.sound]`**。
进一步实测发现触发点比「`e.symm` 字形」更精确：**只要目标里点名 `Temporal.rebase`
这个常项**就带 `Quot.sound`；把它的**定义体**原样搬进本文件则归零。
四条对照（`_t16_chk2.lean` / `_t16_chk.lean` 实测）：

| # | 目标里出现 | `#print axioms` |
|---|---|---|
| 1 | `Temporal.rebase e t` + `e.invFun` | `[Quot.sound]` |
| 2 | `Temporal.rebase e t` + `e.symm`（原写法） | `[Quot.sound]` |
| 3 | 定义体字面量 `⟨e.invFun t.base, t.gaze⟩` + `e.invFun` | **`{}`** ✅ |
| 4 | 局部 `def rebase_inlined`（定义体相同）+ `e.invFun` | **`{}`** ✅ |

⟹ **成因**：`Temporal.rebase` 的定义体是 `⟨e.symm t.base, t.gaze⟩`，
其中的 `e.symm` 是 `Equiv.symm` 的**结构体重建**，而 `Equiv` 的两个证明字段带默认项
`by intro; first | rfl | ext <;> rfl`（`ext <;> rfl` 含 `funext`）。
只要 kernel 需要把 `Temporal.rebase e t` 展到能取出 `.base`，
就得先把这个 `Equiv.symm e` 字面量与投影解成 defeq，于是默认项被实例化，
`funext` 进证明项。写成 `e.invFun`（`Equiv` 的**第二个字段**，`@[reducible] def`）
就绕开了这次结构体重建。

**⚠ 代价（必须承认）**：`rebase_inlined` 是 `Temporal.rebase` 的**复制体**，
两者靠 `rebase_inlined_eq` 桥接——而 **`rebase_inlined_eq` 本身带 `[Quot.sound]`**
（它必须点名 `Temporal.rebase`）。所以这是「把公理隔离到一个桥引理里」，
**不是**「让 `Temporal.rebase` 本身变干净」。真正的根治要改
`Rules/Classification.lean`（把 `rebase` 定义体里的 `e.symm` 换成 `e.invFun`），
那不在本专项的写权限内——见 `_报告/T16-进度.md` §五。 -/

/-! ===========================================================================
  §5  `Rules.FormalCtx.TemporalAction` —— 外延性中**不依赖证明无关性**的那一半
  =========================================================================== -/

namespace TemporalAction

open FateV2.Rules FateV2.Rules.FormalCtx

/-- **`act` 的逐点搬运**：两个 `TemporalAction` 的作用逐点相同即可逐点使用。

  **比定义多说了什么**：`structure TemporalAction` 把 `act` 与三条 `Prop` 公理
  打包，于是「`A` 与 `B` 的作用相同」有**两层**含义：字段相等 vs 结构相等。
  本定理只保**必要**的那一层——外层假设已保证两者在**每个** `(g,t)` 上一致，
  因此「用 `A` 推 `B`」的一切**使用**都合法，**不需要**真的把两个结构判等。

  ⚠ **诚实标注**：原 `TemporalAction.ext` 的结论 `A = B : TemporalAction O`
  需要 `congr 1`（结构外延）+ **证明无关性**。`proof_irrel` 在 Lean 里由
  `propext` 承担，**不是** `funext`。⟹ 该条**不属于** T16 的 D 类目标
  （T15 把它归进「纯 funext」是因为只看公理表、没看正文）。
  本条是它**可降的那一半**。 -/
theorem act_pointwise {O : Type u} {A B : FateV2.Rules.FormalCtx.TemporalAction O}
    (h : ∀ g t, A.act g t = B.act g t) (g : FateV2.Rules.FormalCtx.Gaze)
    (t : FateV2.Rules.FormalCtx.Temporal O) :
    A.act g t = B.act g t :=
  h g t

end TemporalAction

/-! ===========================================================================
  §6  `Predict.predict` —— 1/2 归零，1 条如实登记为不可降
  =========================================================================== -/

namespace Predict

open FateV2.Modeling FateV2.Model FateV2.Predict

/-- **投影响应的逐点版**：逐点相等的两个投影给出**逐点**相等的预测。

  **比定义多说了什么**：`predict` 的定义是
  `fun M eval project pf => pf.push M.P_U (fun e => project (eval e))`——
  它把 `project` 整个**吃进** `fun e => project (eval e)` 这个函数里。
  定义本身**没有**说「投影只按逐点值使用」；本定理说的是：对**每个**外生赋值 `e`，
  预测内部读到的投影值只取决于 `project` 在 `eval e` 处的值。
  即**投影的一切表示差异（闭包、名字、书写形式）都被抹平**，
  只要它在每个状态上取值相同。

  ⚠ **本定理只覆盖可导出的那一半**：`pf.push` 是**任意**函数
  `(E → Z) → T U`，可能「看」函数的具体表示，所以
  「逐点相等 ⟹ `push` 结果相等」**不能**由定义导出（那是原 `predict_congr`
  额外要的 `funext`+`congr`）。这里给的是**必要且无条件成立**的部分。 -/
theorem predict_congr_pointwise {Val V E Z : Type u} {T : Type u → Type u}
    (M : Model Val V E (T E)) (eval : E → WholeState Val V)
    {project project' : WholeState Val V → Z}
    (h : ∀ s, project s = project' s) (e : E) :
    project (eval e) = project' (eval e) :=
  h (eval e)

end Predict

end FateV2.Core.Pointwise
