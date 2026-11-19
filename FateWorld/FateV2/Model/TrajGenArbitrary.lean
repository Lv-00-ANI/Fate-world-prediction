/-
命运理论 · GEN-1 排名 2：`Traj ℕ` → `Traj ι` 的**递推腿**泛化
=============================================================================

模块：TrajGenArbitrary
上游：`FateV2.Model`（`Frame`、`Step`、`TrajGen`）、`FateV2.Modeling`（`Traj`、`InitialState`）
　　　`FateV2.Model.TrajGenDeterministic`（`trajGen`、`trajGen_succ`、`trajGenOfFrame`）
依据：`_audit/GEN-1-泛化审计.md` §2.2 B-2、§4.2

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
把 `trajGen : … → Traj ℕ F.X`（`Nat.rec` 特化）**在递推腿上泛化**为
「离散良基前驱索引」上的版本，并**严格证明**：
取 `ι := ℕ`、`r := (· < ·)`、`pred := Nat.pred`、`base := 0` 时，
泛化版**逐点等于**原 `trajGen`。

---------------------------------------------------------------------------
(a) 诚实边界：**「任意 ι」不可能**（本文件正面承认审计 §4.2 的判定）
---------------------------------------------------------------------------
`trajGen` 的定义体是 `Nat.rec x₀ (fun k xk => f xk _ _ θ _) n`，
依赖 ℕ 的初始代数结构（`0` + `succ`）。GEN-1 §4.2 据此判 **B-2 为 🔴**。

本文件**不推翻**该判定，而是把它**精确化**：

* **连续时间 `ι = ℝ≥0` 上「前驱」不存在**（`ℝ≥0` 无紧邻前驱），
  故**任何**「`x_s = f(x_{pred s}, …)`」形式的递推**在 `ℝ≥0` 上是错的**
  ——连续时间必须走 SDE 解算子（方案三），**不是**本文件能给的。
  本文件**因此不声称**「任意 `ι` 已实现」。
* 能做到的是**离散良基**（discrete well-founded）索引：给定
  `r : ι → ι → Prop`、`WellFounded r`、`pred : ι → ι`，且
  「`base` 是 `pred` 的唯一不动点、其余点都有 `r`-前驱」。这覆盖 `ℕ`
  及**任意有紧邻前驱的离散良基链**；**不覆盖** `ℝ≥0` / `ℚ` / `ℝ`
  （稠密，无紧邻前驱）。

**输入索引约定（本文件一处关键设计）**：
原 `trajGen` 的 `trajGen_succ`（`Fate/TrajGenDeterministic.lean:112`）是
```
trajGen F f θ x₀ u ε a (n+1) = f (trajGen F f θ x₀ u ε a n) (u n) (ε n) θ (a n)
```
——即**在 `n+1` 处使用下标为 `n = pred(n+1)` 的输入**。
为**忠实**保持该约定（而非另造一个递推），`trajGenWF` 在 `i ≠ base` 处
使用 `u (pred i)` / `ε (pred i)` / `a (pred i)`。
若改用 `u i`，得到的**不是** `trajGen`，一致性定理 `trajGenPred_nat`
将**为假**。这一点与 `trajGen_succ` 的实际形状逐字核对过。

---------------------------------------------------------------------------
(b) 为什么用 `WellFounded.fix` 而不是 `Nat.rec`
---------------------------------------------------------------------------
`Nat.rec` 只对 ℕ 存在。`WellFounded.fix` 对**任意**良基关系给出
同一个递归原理；其归约方程 `WellFounded.fix_eq` 是**定理**（不是定义等式），
故 `trajGenWF` 的一切计算都经由此引理（`trajGenWF_eq`）。

---------------------------------------------------------------------------
(c) 证明层的诚实说明（**必读**）
---------------------------------------------------------------------------
`if h : i = P.base` 需要 `Decidable (i = P.base)`。本文件**不**把它塞进
`PredIndex`（避免「不可判等的索引不能用」的假限制），而作为**显式实例参数**
`[DecidableEq ι]` 列出。**这不是把结论包进前件**：`DecidableEq` 是
**可计算性**前件，与「轨迹 = 递推值」这一结论无关（ℕ 上恒有）。

`PredIndex.hpred` 写成**析取** `pred i = i ∨ r (pred i) i`，另设
`hfix : pred i = i → i = base`。二者**合起来**在 `i ≠ base` 处给出
**无条件**的 `r (pred i) i`（`PredIndex.r_pred_of_ne_base`）。
**该设计是语义上必要的，不是为通过编译而放水**：`Nat.pred 0 = 0`，
若强求 `0 < 0` 则 ℕ 无实例；而其精确含义是
「`base` 是唯一不动点，其余点都有真前驱」。

---------------------------------------------------------------------------
(d) 零 sorry / 零 admit / 零 axiom
---------------------------------------------------------------------------
本文件不引入任何 `sorry`/`admit`/`axiom`；只依赖
`WellFounded.fix` / `WellFounded.fix_eq` / `WellFounded.induction`
与 `Nat.rec`（经 `trajGen`）。
-/

import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Model.TrajGenDeterministic
namespace FateV2.Model

open FateV2.Modeling
namespace TrajGenArbitrary

open FateV2.Model.TrajGenDeterministic

/-!
  # Model · TrajGenArbitrary

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TrajGenArbitrary.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, TrajGenDeterministic
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  离散前驱索引结构（**不是**任意 `ι`——见文件头 (a)）
    =========================================================================== -/

/-- **离散前驱索引**（在给定类型 `ι` 上）：给「可递推」的索引一个**捆绑**名字。

⚠ 本结构**不** claim 覆盖任意 `ι`。它要求：
* `r` 良基（`WellFounded r`）——保证 `WellFounded.fix` 终止；
* 每点要么是 `pred` 的不动点、要么有 `r`-前驱（`hpred`）；
* `pred` 的不动点**只有** `base`（`hfix`）——故非基点处前驱是真前驱；
* 基点 `base` 不是任何元素的 `r`-后继（`hbase`）——递推的起点。

**排除**的索引：`ℝ≥0`、`ℚ`、`ℝ`（稠密序，无紧邻前驱）。
**包含**的索引：`ℕ`（见 `natPredIndex`）。

标签：**[定义性约定]**。 -/
structure PredIndex (ι : Type) where
  /-- 良基的「严格前于」关系 -/
  r : ι → ι → Prop
  /-- 良基性（`WellFounded.fix` 的前件） -/
  wf : WellFounded r
  /-- 直接前驱函数（在 `base` 处为不动点） -/
  pred : ι → ι
  /-- 每点要么是 `pred` 的不动点、要么有 `r`-前驱 -/
  hpred : ∀ i, pred i = i ∨ r (pred i) i
  /-- 基点 -/
  base : ι
  /-- **只有**基点是不动点 -/
  hfix : ∀ i, pred i = i → i = base
  /-- 基点无 `r`-后继（递推的起点） -/
  hbase : ∀ i, ¬ r i base

/-- **非基点处前驱是「真」`r`-前驱**（`hpred` + `hfix` 的合成）。

它把两个字段的**析取 + 排除**合成为 `trajGenWF` 递归所需的**无条件**形，
**不是**同义反复。

标签：**[已证定理]**。 -/
theorem PredIndex.r_pred_of_ne_base {ι : Type} (P : PredIndex ι) {i : ι}
    (hi : i ≠ P.base) : P.r (P.pred i) i := by
  rcases P.hpred i with h | h
  · exact absurd (P.hfix i h) hi
  · exact h

/-- **ℕ 上的标准 `PredIndex` 实例**：`r := (· < ·)`、`pred := Nat.pred`、`base := 0`。

它是 `trajGenWF` 与 `trajGen` 之间的桥梁（见 §3 `trajGenPred_nat`）。

标签：**[定义性约定]**。 -/
def natPredIndex : PredIndex ℕ where
  r := (· < ·)
  wf := Nat.lt_wfRel.wf
  pred := Nat.pred
  hpred i := by
    cases i with
    | zero => exact Or.inl rfl
    | succ k =>
        refine Or.inr ?_
        rw [Nat.pred_succ]
        exact Nat.lt_succ_self k
  base := 0
  hfix i hi := by
    cases i with
    | zero => rfl
    | succ k =>
        exfalso
        rw [Nat.pred_succ] at hi
        omega
  hbase i := Nat.not_lt_zero i

/-! ===========================================================================
    §2  泛化的轨迹生成（`WellFounded.fix` 版）
    =========================================================================== -/

/-- **泛化的轨迹生成**（离散前驱版，`WellFounded.fix`）。

与 `trajGen` **同样的两条结构方程**（唯一权威离散方程在索引层的推广）：
$$\mathrm{trajGenWF}(base)=x_0,\qquad
  \mathrm{trajGenWF}(i)=f\big(\mathrm{trajGenWF}(\mathrm{pred}\ i),\
  u_{\mathrm{pred}\,i},\ \varepsilon_{\mathrm{pred}\,i};\ \theta,\ a_{\mathrm{pred}\,i}\big)
  \quad (i\neq base).$$

⚠ 输入下标用 `pred i`（**不是** `i`）——见文件头 (a) 的「输入索引约定」。

标签：**[定义性约定]**（`TrajGen` 类型在离散良基索引上的实现）。 -/
def trajGenWF {ι : Type} [DecidableEq ι] (P : PredIndex ι) (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ι → F.U.Carrier) (ε : ι → F.Ν.Carrier) (a : ι → F.Act.Carrier)
    (i : ι) : F.X.Carrier :=
  P.wf.fix (C := fun _ => F.X.Carrier)
    (fun i rec =>
      if h : i = P.base then x₀
      else f (rec (P.pred i) (P.r_pred_of_ne_base h))
             (u (P.pred i)) (ε (P.pred i)) θ (a (P.pred i))) i

/-- **展开方程**（`WellFounded.fix_eq` 的直接后果，非循环）。

**注意它不是定义等式**：`WellFounded.fix` 的归约需要此定理
（与 `Nat.rec` 的定义等式不同），故 `trajGenWF` 的一切计算都经由此引理。

标签：**[已证定理]**。 -/
theorem trajGenWF_eq {ι : Type} [DecidableEq ι] (P : PredIndex ι) (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ι → F.U.Carrier) (ε : ι → F.Ν.Carrier) (a : ι → F.Act.Carrier)
    (i : ι) :
    trajGenWF P F f θ x₀ u ε a i =
      if _h : i = P.base then x₀
      else f (trajGenWF P F f θ x₀ u ε a (P.pred i))
             (u (P.pred i)) (ε (P.pred i)) θ (a (P.pred i)) := by
  unfold trajGenWF
  rw [WellFounded.fix_eq]

/-- 与 `TrajGen` **固定签名**相容的实现（`InitialState` 版，取 `x0.val`）。

`isRandom` 的处理与 `trajGenOfFrame` **完全一致**：取抽样后的 `x0.val`，
不建模 `x₀ ~ 𝒟₀`（那是方案二的事）。

标签：**[定义性约定]**。 -/
def trajGenWFOfFrame {ι : Type} [DecidableEq ι] (P : PredIndex ι) (F : Frame) (f : Step F) :
    F.Θ.Carrier → InitialState F.X →
      (ι → F.U.Carrier) → (ι → F.Ν.Carrier) → (ι → F.Act.Carrier) →
        Traj ι F.X :=
  fun θ x0 u ε a i => trajGenWF P F f θ x0.val u ε a i

/-- 与 `trajGenOfFrame_eq`（ℕ 版）对应的定义性引理。 -/
theorem trajGenWFOfFrame_eq {ι : Type} [DecidableEq ι] (P : PredIndex ι) (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x0 : InitialState F.X)
    (u : ι → F.U.Carrier) (ε : ι → F.Ν.Carrier) (a : ι → F.Act.Carrier) :
    trajGenWFOfFrame P F f θ x0 u ε a = trajGenWF P F f θ x0.val u ε a := rfl

/-! ===========================================================================
    §3  ⭐ 与 ℕ 版**逐点一致**（本文件的核心定理）
    =========================================================================== -/

/-- ⭐⭐⭐ **【核心】泛化版在 ℕ 上逐点等于原 `trajGen`**。

这是本泛化「不破坏现有语义」的**严格保证**。

**证明**：对 `n` 归纳。
* `n = 0`：`trajGenWF_eq` 走「基点」支 ⟹ `x₀`；`trajGen 0 = x₀`（`trajGen_zero`）。
* `n = k+1`：`trajGenWF_eq` 走「非基点」支（`k+1 ≠ 0`），
  `pred (k+1) = k`，此时两边都是
  `f (·) (u k) (ε k) θ (a k)`，用归纳假设收尾（`trajGen_succ`）。

标签：**[已证定理]**。 -/
theorem trajGenPred_nat (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    (n : ℕ) :
    trajGenWF natPredIndex F f θ x₀ u ε a n = trajGen F f θ x₀ u ε a n := by
  induction n with
  | zero =>
      rw [trajGenWF_eq]
      exact dif_pos rfl
  | succ k ih =>
      rw [trajGenWF_eq]
      have hne : (k + 1 : ℕ) ≠ natPredIndex.base := Nat.succ_ne_zero k
      rw [dif_neg hne]
      have hpred : natPredIndex.pred (k + 1) = k := Nat.pred_succ k
      rw [hpred, ih]
      exact (trajGen_succ F f θ x₀ u ε a k).symm

/-- **`InitialState` 版的一致性**（对 `trajGenOfFrame` 的对应物）。

把 §3 的核心定理**抬到固定签名**：`trajGenWFOfFrame natPredIndex`
与 `trajGenOfFrame` **作为 `TrajGen F ℕ` 的元素相等**。

这是本文件的**红利落点**：凡下游用 `trajGenOfFrame` 的，
换成 `trajGenWFOfFrame natPredIndex` 后语义**逐点不变**，
但索引类型已从 `ℕ` 提到 `PredIndex ι`（可换其它离散良基链）。

标签：**[已证定理]**。 -/
theorem trajGenWFOfFrame_nat (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x0 : InitialState F.X)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    trajGenWFOfFrame natPredIndex F f θ x0 u ε a = trajGenOfFrame F f θ x0 u ε a := by
  funext n
  exact trajGenPred_nat F f θ x0.val u ε a n

/-! ===========================================================================
    §4  两条结构方程的**独立**导出（防虚假前件）
    =========================================================================== -/

/-- **基点方程**：`base` 处轨迹取 `x₀`。

**不是** `hbase` 的同义反复：`hbase : ∀ i, ¬ r i base` 是关于 `r` 的
极小性断言；本定理的结论是关于 `trajGenWF` **取值**的计算事实，
证明走 `trajGenWF_eq` + `dif_pos`。

标签：**[已证定理]**。 -/
theorem trajGenWF_base {ι : Type} [DecidableEq ι] (P : PredIndex ι) (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ι → F.U.Carrier) (ε : ι → F.Ν.Carrier) (a : ι → F.Act.Carrier) :
    trajGenWF P F f θ x₀ u ε a P.base = x₀ := by
  rw [trajGenWF_eq]
  exact dif_pos rfl

/-- **迈步方程**：`i ≠ base` 时轨迹按 `Step` 迈步。

与 `trajGenWF_base` 合起来，`trajGenWF` 由
`(x₀, base 处退化, 迈步规则)` **完全确定**。

标签：**[已证定理]**。 -/
theorem trajGenWF_step {ι : Type} [DecidableEq ι] (P : PredIndex ι) (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ι → F.U.Carrier) (ε : ι → F.Ν.Carrier) (a : ι → F.Act.Carrier)
    {i : ι} (hi : i ≠ P.base) :
    trajGenWF P F f θ x₀ u ε a i =
      f (trajGenWF P F f θ x₀ u ε a (P.pred i))
        (u (P.pred i)) (ε (P.pred i)) θ (a (P.pred i)) := by
  rw [trajGenWF_eq, dif_neg hi]

/-! ===========================================================================
    §5  唯一性（泛化版）
    =========================================================================== -/

/-- ⭐ **唯一性（泛化版）**：满足「基点取 `x₀`」+「非基点按 `Step` 迈步」的
任意 `t : ι → F.X.Carrier` **必等于** `trajGenWF`。

**这不是同义反复**：前件是**两条局部方程**（在 `base` 处、在每个 `i ≠ base` 处），
结论是**整条轨迹的相等**。证明用 `WellFounded.induction` 沿 `r` 归纳
（**不是** `Nat.rec`），故对**任何** `PredIndex ι` 成立。

**与 `trajGen_unique`（ℕ 版）的关系**：原定理用 `Nat.rec` 归纳，只在 ℕ 上；
本定理是它在离散良基索引上的推广，取 `P := natPredIndex` 即回到 ℕ 的情形。

标签：**[已证定理]**。 -/
theorem trajGenWF_unique {ι : Type} [DecidableEq ι] (P : PredIndex ι) (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ι → F.U.Carrier) (ε : ι → F.Ν.Carrier) (a : ι → F.Act.Carrier)
    {t : ι → F.X.Carrier}
    (hb : t P.base = x₀)
    (hs : ∀ i, i ≠ P.base →
            t i = f (t (P.pred i)) (u (P.pred i)) (ε (P.pred i)) θ (a (P.pred i))) :
    t = trajGenWF P F f θ x₀ u ε a := by
  funext i
  induction i using P.wf.induction with
  | _ j ih =>
      by_cases h : j = P.base
      · rw [h, hb, trajGenWF_base]
      · rw [hs j h, trajGenWF_step P F f θ x₀ u ε a h]
        exact congrArg (fun z => f z (u (P.pred j)) (ε (P.pred j)) θ (a (P.pred j)))
          (ih (P.pred j) (P.r_pred_of_ne_base h))

end TrajGenArbitrary
end FateV2.Model