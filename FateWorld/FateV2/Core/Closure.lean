import FateWorld.FateV2.Core.DeclGraph

/-!
  # Core · 依赖闭包（传递版）

  补 `Core/DeclGraph.lean` 尾项第 1 项：「多步闭包当前只展一层」。
-/

namespace FateV2.Core

universe u

/-- **`a ∈ y :: ys` 的分情形**（`List.mem_cons` 带 `propext`）。 -/
theorem mem_cons_cases {α : Type u} {a y : α} {ys : List α} (h : a ∈ y :: ys) :
    a = y ∨ a ∈ ys :=
  match h with
  | List.Mem.head _ => Or.inl rfl
  | List.Mem.tail _ ht => Or.inr ht

/-- **`a ∈ l₁ ++ l₂` 落在某一侧**（`List.mem_append` 带 `propext`）。 -/
theorem mem_append_cases {α : Type u} {a : α} : ∀ (l₁ l₂ : List α),
    a ∈ l₁ ++ l₂ → a ∈ l₁ ∨ a ∈ l₂
  | [], l₂, h => Or.inr h
  | b :: bs, l₂, h => by
      have ht : a ∈ b :: (bs ++ l₂) := h
      cases ht with
      | head => exact Or.inl List.mem_cons_self
      | tail _ htl =>
          cases mem_append_cases bs l₂ htl with
          | inl hl => exact Or.inl (List.mem_cons_of_mem b hl)
          | inr hr => exact Or.inr hr

/-- **`¬¬P → P`（可判定时构造性成立）**。 -/
theorem of_not_not_of_decidable {P : Prop} (d : Decidable P) : ¬ ¬ P → P :=
  match d with
  | isTrue h => fun _ => h
  | isFalse h => fun hnn => absurd h hnn

/-- **列表成员的可判定版**（手写 `Bool`）。 -/
def memBool {α : Type u} (eq : α → α → Bool) : α → List α → Bool
  | _, [] => false
  | a, b :: bs => match eq a b with
    | true => true
    | false => memBool eq a bs

/-- `memBool` 判真 ⟹ 真的在。 -/
theorem mem_of_memBool {α : Type u} (eq : α → α → Bool)
    (heq : ∀ a b : α, eq a b = true → a = b) :
    ∀ (a : α) (l : List α), memBool eq a l = true → a ∈ l
  | _, [], h => absurd h (fun e => Bool.noConfusion e)
  | a, b :: bs, h => by
      cases hb : eq a b with
      | true => exact heq a b hb ▸ List.mem_cons_self
      | false =>
          have h' : memBool eq a bs = true := by
            have ht : (match eq a b with
                       | true => true
                       | false => memBool eq a bs) = true := h
            rw [hb] at ht
            exact ht
          exact List.Mem.tail _ (mem_of_memBool eq heq a bs h')

/-- **真的在 ⟹ `memBool` 判真**（另一方向）。 -/
theorem memBool_of_mem {α : Type u} (eq : α → α → Bool)
    (heq : ∀ a b : α, a = b → eq a b = true) :
    ∀ (a : α) (l : List α), a ∈ l → memBool eq a l = true
  | _, [], h => absurd h (List.not_mem_nil)
  | a, b :: bs, h => by
      cases hb : eq a b with
      | true =>
          have ht : (match eq a b with
                     | true => true
                     | false => memBool eq a bs) = true := by rw [hb]
          exact ht
      | false =>
          have htl : a ∈ bs := by
            cases h with
            | head =>
                have hbad : eq a a = true := heq a a rfl
                have hnot : eq a a = false := hb
                exact absurd (hnot.symm.trans hbad) (by intro e; cases e)
            | tail _ htl' => exact htl'
          have ht : (match eq a b with
                     | true => true
                     | false => memBool eq a bs) = true := by
            rw [hb]
            exact memBool_of_mem eq heq a bs htl
          exact ht

end FateV2.Core

namespace FateV2.Core.DeclGraph

variable {K : Type u}

/-- **一声明的直接依赖**：在 `g` 里找键为 `r` 的那条声明，取其 `deps`。 -/
def depsOf [DecidableEq K] (g : DeclGraph K) (r : K) : List K :=
  match g.find? (fun (d : Decl K) => decide (d.key = r)) with
  | some d => d.deps
  | none => []

/-- `find?` 命中的元素确实在列表里。 -/
theorem find?_mem {α : Type u} (p : α → Bool) :
    ∀ {l : List α} {a : α}, l.find? p = some a → a ∈ l
  | b :: bs, a, h => by
      have hc : (match p b with
                 | true => some b
                 | false => bs.find? p) = some a := h
      cases hp : p b with
      | true =>
          have ha : b = a := Option.some.inj (by rw [hp] at hc; exact hc)
          exact ha ▸ List.mem_cons_self
      | false =>
          have h' : bs.find? p = some a := by rw [hp] at hc; exact hc
          exact List.Mem.tail _ (find?_mem p h')

/-- `find?` 命中的元素满足谓词。 -/
theorem find?_val {α : Type u} (p : α → Bool) :
    ∀ {l : List α} {a : α}, l.find? p = some a → p a = true
  | b :: bs, a, h => by
      have hc : (match p b with
                 | true => some b
                 | false => bs.find? p) = some a := h
      cases hp : p b with
      | true =>
          have hba : b = a := Option.some.inj (by rw [hp] at hc; exact hc)
          exact hba ▸ hp
      | false =>
          have h' : bs.find? p = some a := by rw [hp] at hc; exact hc
          exact find?_val p h'

/-- **`depsOf` 命中时的取值**。 -/
theorem depsOf_some [DecidableEq K] (g : DeclGraph K) (r : K) (d : Decl K)
    (hd : g.find? (fun (e : Decl K) => decide (e.key = r)) = some d) :
    depsOf g r = d.deps := by
  have hc : (match g.find? (fun (e : Decl K) => decide (e.key = r)) with
             | some e => e.deps
             | none => []) = d.deps := by
    rw [hd]
  exact hc

/-- **`depsOf` 吐出的是图里某条声明的 `deps`**（「新东西仍是图里的东西」）。 -/
theorem mem_depsOf_origin [DecidableEq K] (g : DeclGraph K) (r : K) :
    ∀ x ∈ depsOf g r, ∃ d, d ∈ g ∧ d.key = r ∧ x ∈ d.deps := by
  cases hf : g.find? (fun (e : Decl K) => decide (e.key = r)) with
  | none =>
      have hnil : depsOf g r = [] := by
        show (match g.find? (fun (e : Decl K) => decide (e.key = r)) with
              | some e => e.deps
              | none => []) = ([] : List K)
        rw [hf]
      intro x hx
      exact absurd (hnil ▸ hx) (List.not_mem_nil)
  | some d =>
      have hdeps : depsOf g r = d.deps := depsOf_some g r d hf
      have hmem : d ∈ g := find?_mem _ hf
      have hval : decide (d.key = r) = true :=
        find?_val (fun (e : Decl K) => decide (e.key = r)) hf
      intro x hx
      exact ⟨d, hmem, of_decide_eq_true hval, hdeps ▸ hx⟩

/-- **一步展开**：从 `frontier` 出发，把它们的直接依赖加进来。

    ⚠ **手写遍历**，不用 `List.map` / `flatMap`：后者对元素递归会退化成
    well-founded 递归而带 `propext` / `Quot.sound`。 -/
def step [DecidableEq K] (g : DeclGraph K) : List K → List K
  | [] => []
  | r :: rs => depsOf g r ++ step g rs

/-- `step` 在空表上（`rfl`）。 -/
theorem step_nil [DecidableEq K] (g : DeclGraph K) : step g [] = [] := rfl

/-- `step` 的展开律（`rfl`）。 -/
theorem step_cons [DecidableEq K] (g : DeclGraph K) (r : K) (rs : List K) :
    step g (r :: rs) = depsOf g r ++ step g rs := rfl

/-- **`step` 吐出的每一项都在 `g` 的某条声明的 `deps` 里**。 -/
theorem mem_step_origin [DecidableEq K] (g : DeclGraph K) :
    ∀ (roots : List K) (x : K), x ∈ step g roots → ∃ d, d ∈ g ∧ x ∈ d.deps := by
  intro roots
  induction roots with
  | nil => intro x hx; exact absurd hx (List.not_mem_nil)
  | cons r rs ih =>
      intro x hx
      have hstep : x ∈ depsOf g r ++ step g rs := hx
      cases mem_append_cases (depsOf g r) (step g rs) hstep with
      | inl ha =>
          obtain ⟨d, hd, _, hxd⟩ := mem_depsOf_origin g r x ha
          exact ⟨d, hd, hxd⟩
      | inr hb =>
          obtain ⟨d, hd, hxd⟩ := ih x hb
          exact ⟨d, hd, hxd⟩

end FateV2.Core.DeclGraph

namespace FateV2.Core.DeclGraph

variable {K : Type u}

/-- **累积闭包**：`acc` 是已累积的声明，`frontier` 是本轮要展开的一层。

    每一步把 `step g frontier` 追加到 `acc`，并把**刚追加的那一段**当作下一轮的
    `frontier`。`Nat` 参数保证终止。 -/
def closureNAux [DecidableEq K] (g : DeclGraph K) : Nat → List K → List K → List K
  | 0, acc, _ => acc
  | k + 1, acc, frontier => closureNAux g k (acc ++ step g frontier) (step g frontier)

/-- **`n` 步传递闭包**：从 `roots` 出发累积展开 `n` 层。 -/
def closureN [DecidableEq K] (g : DeclGraph K) (n : Nat) (roots : List K) : List K :=
  roots ++ closureNAux g n roots roots

/-- **累积量只长不缩**：`acc ⊆ closureNAux g n acc frontier`。

    比 `closureNAux` 的定义多说了：不论走多少层、每层展开出什么，
    已累积的东西都不会丢 —— 推进式是 `acc ++ …`。 -/
theorem subset_closureNAux [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    ∀ (acc frontier : List K) (x : K), x ∈ acc → x ∈ closureNAux g n acc frontier := by
  induction n with
  | zero => intro acc frontier x hx; exact hx
  | succ k ih =>
      intro acc frontier x hx
      exact ih (acc ++ step g frontier) (step g frontier) x (List.mem_append_left _ hx)

/-- **根永远留在闭包里**：`roots ⊆ closureN g n roots`。 -/
theorem mem_closureN_roots [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    ∀ (roots : List K) (x : K), x ∈ roots → x ∈ closureN g n roots :=
  fun roots x hx => List.mem_append_left _ hx

/-- **累积部分的内容也在闭包里**。 -/
theorem mem_closureN_of_aux [DecidableEq K] (g : DeclGraph K) (n : Nat) :
    ∀ (roots : List K) (x : K), x ∈ closureNAux g n roots roots → x ∈ closureN g n roots :=
  fun roots x hx => List.mem_append_right _ hx

/-- **`closureN` 的定义展开**（`rfl`）。 -/
theorem closureN_def [DecidableEq K] (g : DeclGraph K) (n : Nat) (roots : List K) :
    closureN g n roots = roots ++ closureNAux g n roots roots := rfl



/-- **递推式**（`rfl`）。 -/
theorem closureNAux_succ [DecidableEq K] (g : DeclGraph K) (k : Nat) (acc frontier : List K) :
    closureNAux g (k + 1) acc frontier
      = closureNAux g k (acc ++ step g frontier) (step g frontier) := rfl

/-- **`n+1` 步闭包的累积起点**（`rfl`）。 -/
theorem closureN_succ_eq [DecidableEq K] (g : DeclGraph K) (k : Nat) (roots : List K) :
    closureN g (k + 1) roots
      = roots ++ closureNAux g k (roots ++ step g roots) (step g roots) := rfl

end FateV2.Core.DeclGraph
