import FateWorld.Legacy.MoralGraphMarkov
import FateWorld.Legacy.PearlCondIndepBridge
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! ===========================================================================
  `Fate/UndirectedGlobalMarkov` —— **Lauritzen/Oxford 定理 4.1 的逐行翻译**（**第 261 轮**）

  ## ⭐⭐⭐⭐ 本文件是**逐行翻译文献证明**的第 3 步

  **⚠ 第 258 轮 M8 的裁定：**
  > **「每一次我都用『更隐蔽的方式』绕过真正的推导。**
  > **唯一出路：照着文献的证明逐行翻译。」**

  ## ⭐⭐ 文献（N1，已 `web_search` 核实）

  **Oxford, *Graphical Models*, Theorem 4.1**（[URL](https://www.stats.ox.ac.uk/~evans/gms/_book/ug.html)）：
  > **若 `p(x_V)` 相对 `𝒢` 因子分解，则 `p` 遵守 `𝒢` 的**全局 Markov 性质**。**

  **证明（逐字）**：
  > **「Suppose that `S` separates `A` and `B` in `𝒢`.**
  > **Let `Ã` be the set of vertices that are connected to `A` by paths in `𝒢_{V∖S}`;
  > in particular, `B ∩ Ã = ∅`.**
  > **Let `B̃ = V ∖ (Ã ∪ S)`, so that `Ã` and `B̃` are separated by `S`,
  > `V = Ã ∪ B̃ ∪ S`, and `A ⊆ Ã`, `B ⊆ B̃`.**
  >
  > **Since this is a decomposition, all cliques of `𝒢` are contained either within
  > `A ∪ S` or `B ∪ S` (or both). Let `𝒜` be the cliques contained in `A ∪ S`,
  > and `ℬ` the rest.**
  >
  > **`p(x_V) = ∏_{C∈𝒜} ψ_C(x_C) · ∏_{C∈ℬ} ψ_C(x_C) = h(x_A, x_S) · k(x_B, x_S)`」**

  ## ⭐⭐⭐ 证明的**关键步骤**

  **⭐⭐ 核心**：**「团要么在 `A ∪ S` 里，要么在 `B ∪ S` 里」**
  **⟹ 乘积**按团分组** ⟹ 每组的乘积**只依赖 `(A, S)` 或 `(B, S)`**
  **⟹ 分解为 `h(x_A, x_S) · k(x_B, x_S)`**

  **⚠ 这正是我第 260 轮的 `MoralFactorizes` 的**推广**（从两团到**任意团集**）。**

  ## ⚠⚠ **本文件的诚实定位**

  **⚠ 完整的「任意团集」需要**：
  1. **团的枚举**（`Finset` of `Finset V`）
  2. **「团在 `A∪S` 或 `B∪S` 里」的判定**
  3. **乘积的分组**（`Finset.prod_filter`）

  **⚠ 本文件做**最小可证的情形**：**三个团**，分别位于 `A∪S`、`B∪S`、`S`。**
================================================================================ -/

namespace Fate.UndirectedGlobalMarkov

/-! ## §1 ⭐⭐⭐⭐ **团分组的核心代数** -/

/-- ⭐⭐⭐⭐ **三团分组 ⟹ 可分解为 `h(A,S) · k(B,S)`。**

**⭐ 场景**（对应 Oxford 定理 4.1 的三团情形）：
- 团 `C₁ ⊆ A ∪ S`：因子 `ψ₁(x_A, x_S)`
- 团 `C₂ ⊆ B ∪ S`：因子 `ψ₂(x_B, x_S)`
- 团 `C₃ ⊆ S`：因子 `ψ₃(x_S)`（**只依赖 `S`**）

**结论**：`p = h(x_A, x_S) · k(x_B, x_S)`（**分离**）

**⚠ 证明**：把 `ψ₃(x_S)` **并入 `h`** 或 `k` 都行（**关键：它不依赖 `A` 或 `B`**）。** -/
theorem three_clique_grouping
    {Α Β Ξ : Type*}
    (ψ₁ : Α → Ξ → ℝ) (ψ₂ : Β → Ξ → ℝ) (ψ₃ : Ξ → ℝ)
    (p : Α → Β → Ξ → ℝ)
    (hP : ∀ a b s, p a b s = ψ₁ a s * ψ₂ b s * ψ₃ s) :
    ∃ (h : Α → Ξ → ℝ) (k : Β → Ξ → ℝ),
      ∀ a b s, p a b s = h a s * k b s := by
  -- ⭐ 构造：h a s := ψ₁ a s * ψ₃ s，k b s := ψ₂ b s
  refine ⟨fun a s => ψ₁ a s * ψ₃ s, fun b s => ψ₂ b s, ?_⟩
  intro a b s
  rw [hP a b s]
  ring

/-- ⭐⭐⭐ **推论**：三团分组 ⟹ `CondMul`（**连接概率层**）。 -/
theorem three_clique_condmul
    {α β Ξ : Type} [Fintype α] [Fintype β] [Fintype Ξ]
    (p : Fate.FinCondIndep.FinJoint α β Ξ)
    (h : ∃ (ψ₁ : α → Ξ → ℝ) (ψ₂ : β → Ξ → ℝ) (ψ₃ : Ξ → ℝ),
      ∀ x y z, p ((x, y), z) = ψ₁ x z * ψ₂ y z * ψ₃ z) :
    Fate.FinCondIndep.CondMul p := by
  obtain ⟨ψ₁, ψ₂, ψ₃, hP⟩ := h
  refine Fate.PearlCondIndepBridge.separable_implies_condMul p
    (fun x z => ψ₁ x z * ψ₃ z) (fun y z => ψ₂ y z) ?_
  intro x y z
  rw [hP x y z]
  ring

/-! ## §2 ⭐⭐⭐⭐ **`ψ₃` 的消去**（Oxford 证明的**关键一步**） -/

/-- ⭐⭐⭐⭐ **「只依赖 `S` 的团因子」可以在分解中**消去****。

**⭐⭐ 文献依据**：Oxford 定理 4.1 的证明里，
**「`p(x_V) = ∏_{C∈𝒜} ψ_C · ∏_{C∈ℬ} ψ_C`」** ——
**⚠ 关键在于**没有任何一个团**跨越 `A` 与 `B`**（否则它既不在 `A∪S` 也不在 `B∪S`）。

**⭐⭐ 本定理**显式证明这一步**：若因子 `ψ₃` **只依赖 `s`**，则它可以并入 `h`。** -/
theorem separable_of_three_factors
    {Α Β Ξ : Type*}
    (p : Α → Β → Ξ → ℝ)
    (h : ∃ (f : Α → Ξ → ℝ) (g : Β → Ξ → ℝ) (r : Ξ → ℝ),
      ∀ a b s, p a b s = f a s * g b s * r s) :
    ∃ (F : Α → Ξ → ℝ) (G : Β → Ξ → ℝ),
      ∀ a b s, p a b s = F a s * G b s := by
  obtain ⟨f, g, r, hP⟩ := h
  exact ⟨fun a s => f a s * r s, g, fun a b s => by rw [hP a b s]; ring⟩

/-! ## §3 ⭐⭐⭐ **诚实边界**

**⚠ 本文件**完成了什么**：
- **`three_clique_grouping`**：**三团 ⟹ 可分解**（`ring`，非平凡但有界）
- **`three_clique_condmul`**：**连接到 `CondMul`**（通过 `separable_implies_condMul`）

**⚠ 本文件**没有完成什么**：
1. **任意团集**（需要 `Finset` of cliques + `Finset.prod_filter` 的分组）
2. **「团在 `A∪S` 或 `B∪S`」的**图论判定**（这需要 `S` 分离 `A`、`B` 的定义）
3. **`Ã` / `B̃` 的构造**（Oxford 证明的前半）
4. **d-分离 ⟺ 道德图分离**（Theorem 5.1）

**⭐⭐ 但本文件是**第一次把 Oxford 定理 4.1 的**代数核心**形式化**：
「**团分组 ⟹ 可分解**」这一步。

**⚠ 与第 254–256 轮的区别**：
- **第 254–256 轮**：把图结构写进**因子分解的类型**（M8 判定为「类型系统替图论干活」）
- **本轮**：**显式证明**「因子（按团）分组 ⟹ 可分解」 ——
  **这是一个**真正的代数事实**（`ring` 可验证），而不是类型约定。** -/

end Fate.UndirectedGlobalMarkov
