/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.WorldModelNoPredict
性质：**审计「显式拒绝」文档 + 结构性定理**
上游：`Fate.WorldModel`（`WorldModel`、`WorldModel.sim`）、`Fate.Basic`（`Traj`）

---------------------------------------------------------------------------
# 世界模型无法预测分布 —— 显式拒绝（P0-G3）
---------------------------------------------------------------------------

## CHAIN-2 审计的发现

`WorldModel.sim` 的签名（`#check` 实测，见 `_audit/G3-无predict.md`）是

    WorldModel.sim : (W : WorldModel) → W.frame.Θ.Carrier →
      (ℕ → W.frame.U.Carrier) → (ℕ → W.frame.Ν.Carrier) →
      (ℕ → W.frame.Act.Carrier) → Traj ℕ W.frame.X

返回**单条轨迹** `Traj ℕ W.frame.X`，而（`Fate/Basic.lean:227`）

    Traj (ι : Type u) (X : StateSpace) := ι → X.Carrier

即 `Traj` 是**普通函数类型** `ℕ → X.Carrier`，**类型里没有 `Measure`**。
`Fate/WorldModel.lean:161` 自承「**代价：丢弃分布**」。

## 这意味着什么

「通用预测系统」的核心能力是**给出未来状态的概率分布**
（例如「60% 概率到 A，40% 到 B」）。而当前 `WorldModel`：

1. `sim` 是**函数**——对同一输入必然返回同一输出，**没有随机性来源**
   （定理 `sim_deterministic`）；
2. `sim` 的输出类型 `ℕ → X.Carrier` 是**取值层**的对象，
   **不是** `Measure (Traj ℕ X)`（定理 `sim_output_not_measure_arrow`）；
3. `sim` **完全忽略** `W.rules` 与 `W.selector`——它不是「由规则推出预测」，
   只是「用 `Step` 迭代」（定理 `sim_ignores_rules`、`sim_ignores_selector`）；
4. `sim` **忽略** `horizon`（观测窗口）——预测不求积分
   （定理 `sim_ignores_horizon`）；
5. `sim` 在时刻 `n` 的取值只依赖**输入序列的前缀** `[0, n)`
   （定理 `sim_depends_only_on_input_prefix`）。

⟹ 结论：`sim` 是**点预测**（point prediction），**不是**分布预测。
把 `sim` 当作「预测」会**系统性误读**其表达力上限。

## 本文件的处置（为什么是「显式拒绝」而非「加 predict」）

**不做**「给 `WorldModel` 加 `predict` 字段」：
`WorldModel` 是 `structure`，加字段会改变其构造签名，
进而**破坏所有已构造 `WorldModel` 值的文件**（大范围破坏性改动）。

**而做**「显式记录这个限制」：把「`sim` 不是分布预测」拆成
**若干条可编译的结构性定理**，使该限制成为**类型检查器强制的事实**，
以免后续误以为 `sim` 是分布预测。

## 定理清单（7 条，全部 `#check` 核过；见 `_audit/G3-无predict.md`）

| # | 定理 | 签名要点 | 证明强度 |
|---|---|---|---|
| 1 | `sim_eq_trajGen` | `W.sim θ u ε a = trajGen W.frame W.f θ W.x u ε a` | `rfl`（定义性桥） |
| 2 | `sim_deterministic` | `W.sim θ u ε a = W.sim θ u ε a` | `rfl`（浅，见该定理注） |
| 3 | `sim_ignores_rules` | 换 `rules` ⟹ `sim` 不变 | `rfl`（结构性） |
| 4 | `sim_ignores_selector` | 换 `selector` ⟹ `sim` 不变 | `rfl`（结构性） |
| 5 | `sim_ignores_horizon` | 换 `horizon` ⟹ `sim` 不变 | `rfl`（结构性） |
| 6 | `sim_depends_only_on_input_prefix` | 前缀相等 ⟹ 时刻 `n` 相等 | **归纳**（真证明） |
| 7 | `sim_blind_to_future_noise` | 未来噪声可变 ⟹ 时刻 `n` 不变 | 由 6 实例化 |

**定理 2 的诚实说明**：它字面上是自反性（`rfl`），**本身并不深刻**。
保留它的唯一理由是：把它作为「`sim` 是函数 ⟹ 无内部随机源」的**具名锚点**，
供文档与后续 agent 引用；**不应**把它当作实质结论。实质结论在 3–7。

## ⚠ 诚实标注：本文件**没有**证明「不存在 `predict` 函数」

**「证 `¬ ∃ predict`」在类型层不可如此陈述**，原因有二：

1. 对**任意**类型 `α` 都可写出 `fun _ => (0 : Measure α)`，即
   「存在一个 `Θ → Measure α` 的函数」在集合论意义下**恒真**。
   故「`¬ ∃ predict`」若照字面写出来，**是假的**（只要 `Measure α` 非空）。
2. 真正的限制不是「不存在这样的函数」，而是
   「**`WorldModel` 的现有数据不足以确定**这样的函数」，且
   「**`sim` 的类型里根本没有 `Measure`**」——
   前者是**元层**论断（模型是否欠定），后者是**类型层**事实。

故本文件**不声称**证明了「不存在 `predict`」。
交付的是**可证的那部分**：`sim` 的确定性、`sim` 的值域是**取值层**、
`sim` **丢弃了哪些信息**（规则集／选择器／窗口／未来噪声）。
这些定理**合起来**刻画「无法表达分布」的**类型层成因**（没有分支可承载概率质量）。
**未证明**的部分在此**如实声明**，不用 `sorry` 占位，不虚假声称。

## 定理 7 为什么是「无法表达分布」的核心

概率分布要求**同一时刻多个可能取值并存**。而定理 7 说：
时刻 `n` 的 `sim` 值**只有一个**，把任何未来噪声换成别的序列，
时刻 `n` 的值**逐字不变**。⟹ **`sim` 里没有可以承载概率质量的「分支」**。
这是类型层的根因，不是措辞问题。

## 出路（供后续参考）

1. 让 `sim` 返回 `Measure (Traj ℕ X)`（破坏性改动，
   `Fate.TrajGenStochastic` 已备「方案二」）；
2. 或加一个新字段 `predictDist : Θ → Measure (Traj ℕ X)`（向后兼容）；
3. 或证明 `sim` 在「仅需点预测」的场合**足够**（如 `sim_succ` 的递推已封闭）。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 零 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。
- **不修改**任何已有模块（本文件只 `import`）。
- 全部标识符 ASCII（不用希腊字母作绑定名）。
- 每条定理都用 `#check` 核过签名（见 `_audit/G3-无predict.md`）。
-/

import FateWorld.Legacy.WorldModel

namespace Fate

universe u

noncomputable section

open Fate.TrajGenDeterministic

/-! ===========================================================================
    §1  `sim` 是**确定性的**：无随机性来源
    =========================================================================== -/

/-- ⭐⭐⭐ **【`sim` 不是别的东西：它就是 `trajGen` 的确定性迭代】**

`W.sim θ u ε a` **定义性等于** `trajGen W.frame W.f θ W.x u ε a`。
这条桥引理把「`sim` 的全部内容」钉成一处：**单步机制 + 初值 + 输入序**，
除此之外 `sim` 里**没有**任何别的成分（没有随机源、没有内部状态）。

**为什么必须显式写出**：`sim` 的文档与签名分散在 `WorldModel.lean` 的两处
（L161 的自承「丢弃分布」与 §5.2 的接线），若下游直接引用 `W.sim`
而不看这条桥，就会误以为 `sim` 可能还藏着分布语义。 -/
theorem sim_eq_trajGen (W : WorldModel)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    W.sim theta u eps a
      = TrajGenDeterministic.trajGen W.frame W.f theta W.x u eps a := rfl

/-- ⭐⭐ **【`sim` 是函数 ⟹ 同一输入只有一条轨迹（无随机性来源）】**

`sim` 的确定性：给定 `W` 与全部输入，输出**唯一**。
成立的**唯一**原因就是 `sim` 是函数——即 **`sim` 内部没有随机源**，
随机性必须以 `eps : ℕ → Ν` 的形式**显式喂入**。

**诚实标注**：本定理的证明是 `rfl`（自反性），**不深刻**；
但其**内容**恰是「无法表达分布」的第一层成因：
一个函数在给定输入后**没有第二个可能取值**，故「概率分布」无处附着。 -/
theorem sim_deterministic (W : WorldModel)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    W.sim theta u eps a = W.sim theta u eps a := rfl

/-! ===========================================================================
    §2  `sim` **丢弃了什么**：规则集／选择器／窗口

    这一节是「显式拒绝」的**实质内容**：`sim` 不是「由世界模型的规则推出预测」，
    它只是一次 `Step` 迭代。故称它为「预测」会**高估**它与 `rules` 的联系。
    =========================================================================== -/

/-- ⭐⭐⭐ **【`sim` 完全忽略规则集】**

把 `W` 的规则集换成**任意** `R'`，`sim` 的输出**逐字不变**。
故 `sim` 的预测**不经由** `rules` —— 「规则决定未来」在此实现中**不成立**，
`sim` 只用 `W.f`（单步机制）与 `W.x`（初值）迭代。

**这是「无法表达分布」的第二层成因**：分布本应由规则集的随机核给出，
而 `sim` 根本不看规则集。 -/
theorem sim_ignores_rules (W : WorldModel)
    (R' : WorldRules W.ctx W.frame.X W.frame.X)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    ({ W with rules := R' } : WorldModel).sim theta u eps a
      = W.sim theta u eps a := rfl

/-- ⭐⭐⭐ **【`sim` 完全忽略选择器】**

同理：换掉选择器，`sim` 输出不变。
故 `sim` 与「以观测为条件选规则」的预测路径（裁决 J 的 $R$ 路径）**不相交**。 -/
theorem sim_ignores_selector (W : WorldModel)
    (S' : Selector W.ctx W.frame.X W.frame.X)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    ({ W with selector := S' } : WorldModel).sim theta u eps a
      = W.sim theta u eps a := rfl

/-- ⭐⭐ **【`sim` 忽略观测窗口 `horizon`】**

`WorldSimulator` 的 `horizon`（$T_{\max}$）不参与 `sim`：
`sim` 定义在整个 `ℕ` 上。故 `sim` **不是**「在 $T_{\max}$ 内对分布求积分」，
它就是把递推一路展开——**没有求期望的步骤**。 -/
theorem sim_ignores_horizon (W : WorldModel) (T : ℕ)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    ({ W with simulator := { W.simulator with horizon := T } } : WorldModel).sim
        theta u eps a
      = W.sim theta u eps a := rfl

/-! ===========================================================================
    §3  `sim` 在时刻 `n` 只依赖**输入前缀**

    这是 `sim` 的「**因果性**」（非预期性）：未来的噪声输入**不影响**过去的状态。
    同时它是**真正的定理**（不是 `rfl`），需要沿 `Nat.rec` 做归纳。
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【`sim` 在时刻 `n` 只依赖输入序列的前缀 `[0, n)`】**

若两条输入序在 `[0, n)` 上逐点相等，则 `sim` 在时刻 `n` 的取值相等。
（**因果性／非预期性**：未来的噪声不影响过去。）

**这是 `sim` 的又一条表达力边界**：`sim` 的每个时刻 `n` 只有一个**确定值**，
该值由有限前缀唯一决定——**没有任何「多个可能取值同时并存」的位置**，
故不存在可以承载概率质量的「分支」。

证明：对 `n` 归纳，`n = 0` 时两侧皆为 `W.x`；`n + 1` 时
`sim (n+1) = f (sim n) (u n) (eps n) theta (a n)`（`WorldModel.sim_succ`），
由归纳假设与三项前缀相等即得。 -/
theorem sim_depends_only_on_input_prefix (W : WorldModel)
    (theta : W.frame.Θ.Carrier)
    (u u' : ℕ → W.frame.U.Carrier) (eps eps' : ℕ → W.frame.Ν.Carrier)
    (a a' : ℕ → W.frame.Act.Carrier) :
    ∀ n, (∀ k, k < n → u k = u' k) → (∀ k, k < n → eps k = eps' k) →
      (∀ k, k < n → a k = a' k) →
      W.sim theta u eps a n = W.sim theta u' eps' a' n := by
  intro n
  induction n with
  | zero =>
      intro _ _ _
      exact (WorldModel.sim_zero W theta u eps a).trans
        (WorldModel.sim_zero W theta u' eps' a').symm
  | succ n ih =>
      intro hu heps ha
      rw [WorldModel.sim_succ W theta u eps a n,
          WorldModel.sim_succ W theta u' eps' a' n,
          ih (fun k hk => hu k (Nat.lt_trans hk (Nat.lt_succ_self n)))
             (fun k hk => heps k (Nat.lt_trans hk (Nat.lt_succ_self n)))
             (fun k hk => ha k (Nat.lt_trans hk (Nat.lt_succ_self n))),
          hu n (Nat.lt_succ_self n), heps n (Nat.lt_succ_self n),
          ha n (Nat.lt_succ_self n)]

/-- ⭐⭐⭐ **【「改变未来噪声」不影响当前时刻：`sim` 没有分支】**

若 `eps` 与 `eps'` **只在索引 `j ≥ n` 处可以不同**，则 `sim` 在时刻 `n` 的
取值**相同**。即：时刻 `n` 的预测值**看不到**第 `n` 步及以后的噪声。

**这是「无法表达分布」的第三层成因（最关键的一层）**：
一个概率分布需要**同一时刻多个可能取值并存**（如「60% 到 A、40% 到 B」）。
而本定理表明：时刻 `n` 的值**只有一个**，改动任何未来噪声都不产生第二个值——
**没有分支可承载概率质量**。（本定理由 `sim_depends_only_on_input_prefix`
直接实例化，不是 `rfl`。） -/
theorem sim_blind_to_future_noise (W : WorldModel)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps eps' : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier)
    (n : ℕ) (h : ∀ k, k < n → eps k = eps' k) :
    W.sim theta u eps a n = W.sim theta u eps' a n :=
  sim_depends_only_on_input_prefix W theta u u eps eps' a a n
    (fun _ _ => rfl) h (fun _ _ => rfl)

end

end Fate

/-! ===========================================================================
   §4  R-22 追加：`sim` 语义与本模块 §1–§3 之间的**组合定理**

   §1–§3 给出 `sim` 的逐条边界（忽略规则集／忽略选择器／忽略窗口／只看前缀）。
   本节把这些**逐条**结论组合成**联合**结论，并接上 `TrajGenDeterministic`
   的 restart（`trajGen_split`）与确定性（`trajGen_deterministic`）两条跨模块结果。

   诚实标注：本节定理**不加深** §1–§3 的结论强度——它们的价值在于
   *把分散的边界合并为一次可引用的联合断言*，并把 `sim` 与生成器
   `trajGen` 的结构定理（restart / 确定性）**真正接上**（此前无模块引用
   `sim_eq_trajGen` 去推 restart）。
   =========================================================================== -/

namespace Fate

noncomputable section

open Fate.TrajGenDeterministic

/-- ⭐⭐⭐ **【三段同时替换：规则集 + 选择器 + 观测窗口，`sim` 轨迹逐字不变】**

把 §2 的三条「忽略」合并成**一次**联合断言：同时替换
`rules`、`selector`、`simulator.horizon` 三者，`sim` 的输出**完全不变**。

**意义**：这是「裁决 J 的 R 路径」（以观测条件选规则）与本实现 `sim`
**整体不相交**的联合表达——不是三次分别更换，而是三者**同时**更换后依然相等，
故不存在「三者协同才能产生影响」的漏洞。
（证明只用到 `sim_ignores_rules`：`sim` 的定义根本不读取另外两段。） -/
theorem sim_ignores_rules_selector_horizon (W : WorldModel)
    (R' : WorldRules W.ctx W.frame.X W.frame.X)
    (S' : Selector W.ctx W.frame.X W.frame.X) (T : ℕ)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    ({ { { W with rules := R' } with selector := S' } with
        simulator := { W.simulator with horizon := T } } : WorldModel).sim theta u eps a
      = W.sim theta u eps a :=
  sim_ignores_rules W R' theta u eps a

/-- ⭐⭐⭐⭐ **【`sim` 的 restart 性质：从时刻 `m` 重新起跑等价于原轨迹】**

`sim` 在时刻 `m` 之后的部分，等于**以 `sim m` 为初值、以 `m` 之后的输入序重新起跑**
所得到的轨迹（`theta` 保持不变）。

**这是跨模块接线**：由 `sim_eq_trajGen` 把 `sim` 换成 `trajGen`，
再套 `TrajGenDeterministic.trajGen_split`，最后用桥引理把 `trajGen` 换回 `sim`。
故本定理**必须**同时使用两个模块的结果，不是 `rfl`。

**意义**：`sim` 与 `trajGen` 共享**同一套马尔可夫结构**——
时刻 `m` 之前的历史被完全压缩进单点 `sim m`。这同时说明
`sim` **没有**「需要携带的隐藏状态」（如规则选择历史、分布残留）。 -/
theorem sim_split (W : WorldModel)
    (m : ℕ) (theta : W.frame.Θ.Carrier)
    (u : ℕ → W.frame.U.Carrier) (eps : ℕ → W.frame.Ν.Carrier)
    (a : ℕ → W.frame.Act.Carrier) :
    W.sim theta u eps a = fun k =>
      if _h : k < m then W.sim theta u eps a k
      else TrajGenDeterministic.trajGen W.frame W.f theta
             (W.sim theta u eps a m) (fun j => u (m + j))
             (fun j => eps (m + j)) (fun j => a (m + j)) (k - m) := by
  conv_lhs => rw [sim_eq_trajGen W theta u eps a]
  rw [TrajGenDeterministic.trajGen_split W.frame W.f m theta W.x u eps a]
  funext k
  by_cases hk : k < m
  · rw [dif_pos hk, dif_pos hk]
    exact (sim_eq_trajGen W theta u eps a).symm ▸ rfl
  · rw [dif_neg hk, dif_neg hk]
    rw [show TrajGenDeterministic.trajGen W.frame W.f theta W.x u eps a m
          = W.sim theta u eps a m from (sim_eq_trajGen W theta u eps a).symm ▸ rfl]

/-- ⭐⭐⭐⭐ **【前缀相同 ⟹ 从 `0` 到 `n` 的**整段**轨迹相同】**

§3 的 `sim_depends_only_on_input_prefix` 只断言**单点** `n` 的相等。
本条把它升级为**整段**：`[0, n]` 上**每个**时刻都相等。

**意义**：这是「`sim` 的观测窗口内容完全由前缀决定」的**联合**形式——
一次得到 `n + 1` 个点的相等，而不是逐点重复调用。 -/
theorem sim_prefix_eq_on_range (W : WorldModel)
    (theta : W.frame.Θ.Carrier)
    (u u' : ℕ → W.frame.U.Carrier) (eps eps' : ℕ → W.frame.Ν.Carrier)
    (a a' : ℕ → W.frame.Act.Carrier) (n : ℕ) :
    (∀ k, k < n → u k = u' k) → (∀ k, k < n → eps k = eps' k) →
      (∀ k, k < n → a k = a' k) →
      ∀ j, j ≤ n → W.sim theta u eps a j = W.sim theta u' eps' a' j := by
  intro hu heps ha j hj
  exact sim_depends_only_on_input_prefix W theta u u' eps eps' a a' j
    (fun k hk => hu k (Nat.lt_of_lt_of_le hk hj))
    (fun k hk => heps k (Nat.lt_of_lt_of_le hk hj))
    (fun k hk => ha k (Nat.lt_of_lt_of_le hk hj))

/-- ⭐⭐⭐⭐ **【改动未来噪声不改变**整段**已发生轨迹】**

§3 的 `sim_blind_to_future_noise` 只断言**单点** `n` 不受未来噪声影响。
本条把它升级为**整段**：改动索引 `≥ n` 的噪声，`[0, n]` 上**每个**时刻都不变。

**意义**：这是「`sim` 没有分支可承载概率质量」的**最强联合形式**——
整个已发生窗口内**没有任何一个时刻**存在第二个可能取值。 -/
theorem sim_future_noise_free_on_range (W : WorldModel)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps eps' : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier)
    (n : ℕ) (h : ∀ k, k < n → eps k = eps' k) :
    ∀ j, j ≤ n → W.sim theta u eps a j = W.sim theta u eps' a j := by
  intro j hj
  exact sim_depends_only_on_input_prefix W theta u u eps eps' a a j
    (fun _ _ => rfl)
    (fun k hk => h k (Nat.lt_of_lt_of_le hk hj))
    (fun _ _ => rfl)

/-- ⭐⭐⭐⭐ **【`sim` 的整条轨迹由输入唯一决定（跨模块：`trajGen_deterministic`）】**

若 `theta` 相等且三条输入序**逐点**相等，则 `sim` 的**整条轨迹**
（作为 `ℕ → X` 的函数）相等。

**这是跨模块接线**：由 `sim_eq_trajGen` 换成 `trajGen`，套
`TrajGenDeterministic.trajGen_deterministic`，再用桥引理换回。
与 §1 的 `sim_deterministic`（`rfl`，只断言 `a = a`）不同，本条是
**两条不同输入序之间**的比较，且用到了 `trajGen` 模块的定理。 -/
theorem sim_traj_deterministic (W : WorldModel) {th th' : W.frame.Θ.Carrier}
    {u u' : ℕ → W.frame.U.Carrier} {eps eps' : ℕ → W.frame.Ν.Carrier}
    {a a' : ℕ → W.frame.Act.Carrier}
    (hth : th = th') (hu : ∀ k, u k = u' k) (he : ∀ k, eps k = eps' k)
    (ha : ∀ k, a k = a' k) :
    W.sim th u eps a = W.sim th' u' eps' a' := by
  rw [sim_eq_trajGen W th u eps a, sim_eq_trajGen W th' u' eps' a']
  exact TrajGenDeterministic.trajGen_deterministic W.frame W.f hth rfl hu he ha

/-- ⭐⭐⭐ **【规则集只影响「换哪一个」，不影响轨迹：任意两个规则集给出同一条 `sim`】**

把规则集换成 `R1` 或换成 `R2`，两次得到的 `sim` 轨迹**相同**。
故规则集对 `sim` 的影响**恒为零**（不只是「单个替换不影响」，
而是「任意两个替换之间也没有差别」）。 -/
theorem sim_rule_swap_any_two (W : WorldModel)
    (R1 R2 : WorldRules W.ctx W.frame.X W.frame.X)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    ({ W with rules := R1 } : WorldModel).sim theta u eps a
      = ({ W with rules := R2 } : WorldModel).sim theta u eps a :=
  (sim_ignores_rules W R1 theta u eps a).trans
    (sim_ignores_rules W R2 theta u eps a).symm

/-- ⭐⭐⭐ **【选择器对 `sim` 的影响恒为零：任意两个选择器给出同一条轨迹】**

与 `sim_rule_swap_any_two` 对偶：任意两个选择器 `S1`、`S2` 给出的 `sim` 轨迹相同。
故「以观测为条件选规则」这一整条路径对 `sim` 的贡献**恒为零**。 -/
theorem sim_selector_swap_any_two (W : WorldModel)
    (S1 S2 : Selector W.ctx W.frame.X W.frame.X)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    ({ W with selector := S1 } : WorldModel).sim theta u eps a
      = ({ W with selector := S2 } : WorldModel).sim theta u eps a :=
  (sim_ignores_selector W S1 theta u eps a).trans
    (sim_ignores_selector W S2 theta u eps a).symm

end

end Fate
