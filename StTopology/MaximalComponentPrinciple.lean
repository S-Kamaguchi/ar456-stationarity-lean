import Mathlib

set_option linter.style.header false

/-!
# 最大連結成分の原理 (`9_maximal_component_principle.tex`, Section 3.8)

論文の Proposition (maximal component principle) の形式化。

論文の `C(x_0,\Omega)` (Ω 内で x_0 を含む連結集合すべての和集合) は、Mathlib の
`connectedComponentIn Ω x_0` にそのまま対応する。論文の `Lemma component-maximal` の
内容 (i)(ii) は Mathlib にすでに存在する:
* (i) 連結・`x_0` を含む・(局所連結空間なら)開: `isPreconnected_connectedComponentIn`,
  `mem_connectedComponentIn`, `IsOpen.connectedComponentIn`
* (ii) 最大性 (定義から自明): `IsPreconnected.subset_connectedComponentIn`

したがって、ここでは論文の Proposition 本体 (`prop:mcp`) のみを証明すればよい。
`X` を一般の位相空間としておく (`AR(4)/(5)/(6)` への適用では `X = Fin p → ℝ`)。
-/

open Set

namespace StTopology

/-- **最大連結成分の原理** (`9_maximal_component_principle.tex`, Proposition `prop:mcp`).

`Ω` を `O` を含む集合、`St` を `O` を含む開かつ preconnected な集合とする。もし
(a) `St ⊆ Ω` (論文の hypothesis (a))、かつ
(b) `L := connectedComponentIn Ω O` が `St` の境界 `frontier St` と交わらない
    (論文の hypothesis (b))
ならば、`L = St`。

証明は論文の2段の包含関係の議論をそのままなぞる:
* `St ⊆ L`: `St` は `O` を含む `Ω` 内の連結集合なので、`connectedComponentIn` の
  最大性 (`IsPreconnected.subset_connectedComponentIn`) から従う。
* `L ⊆ St`: `St` が開なので `frontier St = closure St \ St`。仮定(b)より `L` は
  `St` と `(closure St)ᶜ` という互いに素な2つの開集合の和集合に含まれ、かつ
  `O` を通じて `St` 側と交わる。`L` は連結なので、`(closure St)ᶜ` 側には
  はみ出せない (`IsPreconnected.subset_left_of_subset_union`)。 -/
theorem maximal_component_principle {X : Type*} [TopologicalSpace X]
    (Ω St : Set X) (O : X)
    (hO_Ω : O ∈ Ω)
    (hSt_open : IsOpen St) (hSt_preconn : IsPreconnected St) (hO_St : O ∈ St)
    (ha : St ⊆ Ω)
    (hb : connectedComponentIn Ω O ∩ frontier St = ∅) :
    connectedComponentIn Ω O = St := by
  set L := connectedComponentIn Ω O with hL_def
  have hL_sub_St : St ⊆ L := hSt_preconn.subset_connectedComponentIn hO_St ha
  have hL_preconn : IsPreconnected L := isPreconnected_connectedComponentIn
  have hu : IsOpen St := hSt_open
  have hv : IsOpen (closure St)ᶜ := isClosed_closure.isOpen_compl
  have huv : Disjoint St (closure St)ᶜ := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx' (subset_closure hx)
  have hsuv : L ⊆ St ∪ (closure St)ᶜ := by
    intro x hxL
    by_cases hxSt : x ∈ St
    · exact Or.inl hxSt
    · refine Or.inr ?_
      intro hxclosure
      have hx_frontier : x ∈ frontier St := by
        rw [hSt_open.frontier_eq]
        exact ⟨hxclosure, hxSt⟩
      have hcontra : x ∈ L ∩ frontier St := ⟨hxL, hx_frontier⟩
      rw [hb] at hcontra
      exact hcontra
  have hsu : (L ∩ St).Nonempty := ⟨O, mem_connectedComponentIn hO_Ω, hO_St⟩
  have hL_sub_St' : L ⊆ St :=
    hL_preconn.subset_left_of_subset_union hu hv huv hsuv hsu
  exact hL_sub_St'.antisymm hL_sub_St

end StTopology
