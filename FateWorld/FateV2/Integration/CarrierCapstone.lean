import FateWorld.FateV2.Export.Carrier

/-!
# Integration · Export · 异质条目的忠实性

## 本文件做什么

`Export/Carrier.lean` 里关于 `Entry`（依赖对 `Sigma (fun m => C.fiber m)`）
的结果各自独立：

- `entry_mk_fst`：`⟨e.fst, e.snd⟩ = e`
- `entry_roundtrip`：投影与配对在 `Entry` 上互逆
- `entry_eq_iff`：同索引下 `⟨m,x⟩ = ⟨m,y⟩ ↔ x = y`

这些**没有被任何下游调用**。本文件把它们组合成三条关于
「异质条目是忠实的依赖对」的定理，供导出层一次性取用。

## 与迁移的关系

第三例整合：把假接线转为真消费。

## 不引入新数学

全部为既有定理的组合。
-/

namespace FateV2.Integration

namespace CarrierCapstone

open FateV2.Export

universe u v

variable {M : Type u} {C : Carrier M}

/-- ⭐ **投影-配对在整个 `Entry` 上互逆**。

对任意条目 `e`，先取 `fst`/`snd` 再重新配对回到 `e`。
本体即 `entry_mk_fst`；单列是因为下游常用「条目可还原」这一形式，
而不想每次都展开 `Sigma.eta`。 -/
theorem entry_reconstruct (e : Entry C) : Sigma.mk e.fst e.snd = e :=
  entry_mk_fst e

/-- ⭐⭐ **同索引下编码的单射性 + 投影可还原**。

固定模态索引 `m` 时：
1. 投影回到 `m` 与 `x`（`entry_roundtrip` 的前两支）；
2. `⟨m,x⟩ = ⟨m,y⟩ ↔ x = y`（`entry_eq_iff`）。

**为什么值得一条定理**：导出层需要「同一模态的条目由载荷唯一决定」
这一事实。它由 `entry_roundtrip` 与 `entry_eq_iff` **协同**得到 ——
前者保证投影不丢索引，后者保证载荷可分辨。任意一条单独都不够。 -/
theorem entry_at_index_faithful (m : M) (x y : C.fiber m) :
    ((Sigma.mk m x).fst = m ∧ (Sigma.mk m x).snd = x)
      ∧ (Sigma.mk m x = Sigma.mk m y ↔ x = y) := by
  refine ⟨?_, entry_eq_iff m x y⟩
  obtain ⟨h1, h2, _⟩ := entry_roundtrip (C := C) m x
  exact ⟨h1, h2⟩

/-- ⭐ **条目外延性**。

`e = e'` 等价于「两者重新配对后相等」。

正向由 `entry_mk_fst` 重写两端得到；反向把两条 `entry_mk_fst`
代回。**这条把等式的判定从「依赖对」降到「配对后的形态」**，
下游可以直接在 `Sigma.mk` 上做 `cases`/`rw` 而不必处理 `Sigma.eta`。 -/
theorem entry_ext_iff (e e' : Entry C) :
    e = e' ↔ Sigma.mk e.fst e.snd = Sigma.mk e'.fst e'.snd := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← entry_mk_fst e, ← entry_mk_fst e']
    exact h

end CarrierCapstone

end FateV2.Integration