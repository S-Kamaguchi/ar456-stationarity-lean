import Mathlib
import StTopology.StationarityRegions
import StTopology.VietaBound
import StTopology.StOpen

set_option linter.style.header false

/-!
# 根の摂動: Rouché を使わない初等的な議論

`∂St(p) ⊆ {単位円上に根を持つ}` を示すために必要な、根の連続性にあたる部分。

## 鍵になる不等式

`Q := charPoly ψ` は monic で ℂ 上分解するので、任意の `α` に対して

  `‖Q.eval α‖ = ∏_{β ∈ Q.roots} ‖α - β‖`

が成り立つ (`Splits.eval_eq_prod_roots_of_monic`)。よって **`ψ` の根がすべて `α` から
`δ` 以上離れていれば `‖Q.eval α‖ ≥ δ^p`** となる (`norm_eval_ge_of_roots_far`)。

対偶を取ると「`‖Q.eval α‖` が小さければ `ψ` は `α` の近くに根を持つ」となり、
これが Rouché の定理を経由しない根の摂動である。`StOpen.lean` の摂動評価
`normF_sub_le` と組み合わせると:

  `φ` が根 `α` を持つ ⟹ `φ` に十分近い `ψ` も `α` の近くに根を持つ

が従い、`{φ | 単位円の外に根を持つ}` が開集合であることが分かる
(`isOpen_hasOuterRoot`)。したがって `∂St(p)` の点は単位円の外に根を持てず、
一方 `St(p)` に属さないので、ちょうど単位円上に根を持つ
(`exists_unit_root_of_mem_frontier`)。
-/

open Finset Polynomial

namespace StTopology

/-- `Q := charPoly ψ` の `α` での値のノルムは、根までの距離の積に等しい。 -/
theorem norm_eval_charPoly {p : ℕ} (hp : 0 < p) (ψ : Fin p → ℝ) (α : ℂ) :
    ‖(charPoly ψ).eval α‖ = (((charPoly ψ).roots.map (fun β => ‖α - β‖)).prod) := by
  have hmonic : (charPoly ψ).Monic := charPoly_monic hp ψ
  have hsplits : (charPoly ψ).Splits := IsAlgClosed.splits _
  rw [hsplits.eval_eq_prod_roots_of_monic hmonic]
  induction (charPoly ψ).roots using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [Multiset.prod_cons, ih]

/-- **根が遠ければ多項式の値は大きい**: `ψ` の根がすべて `α` から `δ` 以上離れていれば
`‖Q.eval α‖ ≥ δ^p`。 -/
theorem norm_eval_ge_of_roots_far {p : ℕ} (hp : 0 < p) (ψ : Fin p → ℝ) (α : ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hfar : ∀ β ∈ (charPoly ψ).roots, δ ≤ ‖α - β‖) :
    δ ^ p ≤ ‖(charPoly ψ).eval α‖ := by
  have hmonic : (charPoly ψ).Monic := charPoly_monic hp ψ
  have hsplits : (charPoly ψ).Splits := IsAlgClosed.splits _
  have hcard : (charPoly ψ).roots.card = p := by
    rw [hsplits.natDegree_eq_card_roots.symm, charPoly_natDegree hp ψ]
  rw [norm_eval_charPoly hp ψ α]
  -- 各因子が δ 以上、因子の個数は p 個
  have key : ∀ s : Multiset ℂ, (∀ β ∈ s, δ ≤ ‖α - β‖) →
      δ ^ s.card ≤ (s.map (fun β => ‖α - β‖)).prod := by
    intro s
    induction s using Multiset.induction with
    | empty => intro _; simp
    | cons a t ih =>
      intro hmem
      have ha : δ ≤ ‖α - a‖ := hmem a (Multiset.mem_cons_self a t)
      have ht : ∀ β ∈ t, δ ≤ ‖α - β‖ := fun β hβ => hmem β (Multiset.mem_cons_of_mem hβ)
      have htprod := ih ht
      have htpos : 0 < δ ^ t.card := pow_pos hδ _
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
      calc δ ^ t.card * δ ≤ δ ^ t.card * ‖α - a‖ :=
            mul_le_mul_of_nonneg_left ha htpos.le
        _ ≤ (t.map (fun β => ‖α - β‖)).prod * ‖α - a‖ :=
            mul_le_mul_of_nonneg_right htprod (norm_nonneg _)
        _ = ‖α - a‖ * (t.map (fun β => ‖α - β‖)).prod := by ring
  have := key (charPoly ψ).roots hfar
  rwa [hcard] at this

/-- `charPoly` の根であることと、逆特性方程式の根であることは同値。 -/
theorem mem_roots_charPoly_iff {p : ℕ} (hp : 0 < p) (ψ : Fin p → ℝ) (β : ℂ) :
    β ∈ (charPoly ψ).roots ↔ β ^ p = ∑ i : Fin p, (ψ i : ℂ) * β ^ (p - 1 - (i : ℕ)) := by
  have hmonic : (charPoly ψ).Monic := charPoly_monic hp ψ
  have hne : charPoly ψ ≠ 0 := hmonic.ne_zero
  rw [Polynomial.mem_roots hne]
  constructor
  · intro h
    have heval : (charPoly ψ).eval β = 0 := h
    rw [charPoly_eval] at heval
    linear_combination heval
  · intro h
    change (charPoly ψ).eval β = 0
    rw [charPoly_eval]
    linear_combination h

/-- `charPoly` の値は `StOpen.F` と一致する。 -/
theorem charPoly_eval_eq_F {p : ℕ} (ψ : Fin p → ℝ) (z : ℂ) :
    (charPoly ψ).eval z = F ψ z := by
  rw [charPoly_eval]
  rfl

/-- **根の摂動 (Rouché 不要)**: `φ` が根 `α` を持つとき、`φ` に十分近い `ψ` は
`α` から `δ` 未満のところに根を持つ。 -/
theorem exists_root_near {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) (α : ℂ)
    (hα : α ^ p = ∑ i : Fin p, (φ i : ℂ) * α ^ (p - 1 - (i : ℕ)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ ψ : Fin p → ℝ, dist ψ φ < ε →
      ∃ β : ℂ, β ^ p = ∑ i : Fin p, (ψ i : ℂ) * β ^ (p - 1 - (i : ℕ)) ∧ ‖α - β‖ < δ := by
  set R : ℝ := max 1 ‖α‖ with hR
  have hR1 : (1 : ℝ) ≤ R := le_max_left _ _
  have hαR : ‖α‖ ≤ R := le_max_right _ _
  have hRpow : (0 : ℝ) < R ^ (p - 1) := pow_pos (by linarith) _
  refine ⟨δ ^ p / ((p + 1) * R ^ (p - 1)), by positivity, ?_⟩
  intro ψ hdist
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  -- ψ の根はすべて α から δ 以上離れている
  have hfar : ∀ β ∈ (charPoly ψ).roots, δ ≤ ‖α - β‖ := fun β hβ =>
    hcon β ((mem_roots_charPoly_iff hp ψ β).mp hβ)
  have hlow : δ ^ p ≤ ‖(charPoly ψ).eval α‖ := norm_eval_ge_of_roots_far hp ψ α hδ hfar
  -- 一方、φ の根 α では F φ α = 0 なので摂動評価から小さいはず
  have hFφ : F φ α = 0 := (F_eq_zero_iff φ α).mpr hα
  have hpert : ‖F ψ α‖ ≤ (∑ i, |ψ i - φ i|) * R ^ (p - 1) := by
    have := normF_sub_le ψ φ α R hR1 hαR
    rwa [hFφ, sub_zero] at this
  have hsum : ∑ i, |ψ i - φ i| ≤ (p : ℝ) * dist ψ φ := by
    calc ∑ i, |ψ i - φ i| ≤ ∑ _i : Fin p, dist ψ φ := by
          apply Finset.sum_le_sum
          intro i _
          have := dist_le_pi_dist ψ φ i
          rwa [Real.dist_eq] at this
      _ = (p : ℝ) * dist ψ φ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [charPoly_eval_eq_F] at hlow
  have hppos : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hfinal : (∑ i, |ψ i - φ i|) * R ^ (p - 1) < δ ^ p := by
    have h1 : (∑ i, |ψ i - φ i|) * R ^ (p - 1) ≤ ((p : ℝ) * dist ψ φ) * R ^ (p - 1) :=
      mul_le_mul_of_nonneg_right hsum hRpow.le
    have h2 : ((p : ℝ) * dist ψ φ) * R ^ (p - 1)
        < ((p : ℝ) * (δ ^ p / ((p + 1) * R ^ (p - 1)))) * R ^ (p - 1) := by
      apply mul_lt_mul_of_pos_right _ hRpow
      rcases eq_or_lt_of_le hppos with hp0 | hp0
      · exfalso
        have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
        exact this hp0.symm
      · exact mul_lt_mul_of_pos_left hdist hp0
    have h3 : ((p : ℝ) * (δ ^ p / ((p + 1) * R ^ (p - 1)))) * R ^ (p - 1) < δ ^ p := by
      have hδp : (0 : ℝ) < δ ^ p := pow_pos hδ p
      have hkey : ((p : ℝ) * (δ ^ p / ((p + 1) * R ^ (p - 1)))) * R ^ (p - 1)
          = ((p : ℝ) * δ ^ p) / ((p : ℝ) + 1) := by
        field_simp
      rw [hkey, div_lt_iff₀ (by positivity)]
      nlinarith [hδp, hppos]
    linarith
  linarith

/-! ### `∂St(p) ⊆ {単位円上に根を持つ}`

`exists_root_near` から直接従う。`φ ∈ ∂St(p)` なら `φ ∈ closure St(p)` かつ `φ ∉ St(p)`。
`φ ∉ St(p)` から、単位円上ではない (仮定により) ノルム `>1` の根 `α₀` が取れる。
`exists_root_near` より、`φ` に十分近い `ψ` は `α₀` の近くに根を持ち、その根も
ノルム `>1` になる。したがって `φ` のある近傍が `St(p)` と交わらず、
`φ ∉ closure St(p)` となって矛盾する。 -/
theorem frontier_isStationary_subset_hasUnitRoot {p : ℕ} (hp : 0 < p) :
    frontier {φ : Fin p → ℝ | IsStationary φ}
      ⊆ {φ : Fin p → ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧
          z ^ p = ∑ i : Fin p, (φ i : ℂ) * z ^ (p - 1 - (i : ℕ))} := by
  intro φ hφ
  by_contra hnu
  simp only [Set.mem_setOf_eq, not_exists] at hnu
  push Not at hnu
  by_cases hmem : IsStationary φ
  · have hint : φ ∈ interior {ψ : Fin p → ℝ | IsStationary ψ} := by
      rwa [(isOpen_isStationary hp).interior_eq]
    exact hφ.2 hint
  · unfold IsStationary at hmem
    push Not at hmem
    obtain ⟨α₀, hα₀eq, hα₀ge⟩ := hmem
    have hne1 : ‖α₀‖ ≠ 1 := fun h => hnu α₀ h hα₀eq
    have hα₀gt : 1 < ‖α₀‖ := lt_of_le_of_ne hα₀ge (Ne.symm hne1)
    set δ : ℝ := (‖α₀‖ - 1) / 2 with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; linarith
    obtain ⟨ε, hεpos, hε⟩ := exists_root_near hp φ α₀ hα₀eq hδpos
    have hsub : Metric.ball φ ε ⊆ {ψ : Fin p → ℝ | IsStationary ψ}ᶜ := by
      intro ψ hψball hψSt
      rw [Metric.mem_ball] at hψball
      obtain ⟨β, hβeq, hβclose⟩ := hε ψ hψball
      have h1 : ‖α₀‖ - ‖β‖ ≤ ‖α₀ - β‖ := norm_sub_norm_le α₀ β
      have hβge1 : (1 : ℝ) ≤ ‖β‖ := by
        rw [hδdef] at hβclose
        linarith
      exact absurd (hψSt β hβeq) (not_lt.mpr hβge1)
    have hmemint : φ ∈ interior ({ψ : Fin p → ℝ | IsStationary ψ}ᶜ) :=
      interior_maximal hsub Metric.isOpen_ball (Metric.mem_ball_self hεpos)
    rw [interior_compl] at hmemint
    exact hmemint hφ.1

/-! ### `{単位円の外に根を持つ}` は開集合

`exists_root_near` から `frontier_isStationary_subset_hasUnitRoot` と全く同じ要領で従う:
`φ₀` がノルム `>1` の根 `z₀` を持てば、`φ₀` に十分近い `ψ` も `z₀` の近くに
(したがってやはりノルム `>1` の) 根を持つ。 -/
theorem isOpen_hasOuterRoot {p : ℕ} (hp : 0 < p) :
    IsOpen {φ : Fin p → ℝ | ∃ z : ℂ, 1 < ‖z‖ ∧
        z ^ p = ∑ i : Fin p, (φ i : ℂ) * z ^ (p - 1 - (i : ℕ))} := by
  rw [Metric.isOpen_iff]
  intro φ₀ hφ₀
  obtain ⟨z₀, hz₀gt, hz₀eq⟩ := hφ₀
  set δ : ℝ := (‖z₀‖ - 1) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨ε, hεpos, hε⟩ := exists_root_near hp φ₀ z₀ hz₀eq hδpos
  refine ⟨ε, hεpos, ?_⟩
  intro ψ hψball
  rw [Metric.mem_ball] at hψball
  obtain ⟨β, hβeq, hβclose⟩ := hε ψ hψball
  refine ⟨β, ?_, hβeq⟩
  have h1 : ‖z₀‖ - ‖β‖ ≤ ‖z₀ - β‖ := norm_sub_norm_le z₀ β
  rw [hδdef] at hβclose
  linarith

/-! ### 単位円上に根を持たない経路は定常性を保つ

一般化された `L41_eq_isStationary` の路版: `γ:ℝ→(Fin p → ℝ)` が連続で `γ 0` が定常、
かつ `t∈[0,1]` の間ずっと `γ t` が単位円上に根を持たないならば、`γ 1` も定常。

証明は `MaximalComponentPrinciple.lean` の 2 分割の議論とまったく同じ形:
`U:=γ⁻¹(IsStationary)` と `V:=γ⁻¹(外側に根を持つ)` はどちらも開 (`isOpen_isStationary`,
`isOpen_hasOuterRoot` の引き戻し) で互いに素、`Icc 0 1 ⊆ U∪V` (仮定 `hno` により
「単位円上」の第三の可能性が排除されるので、定常 (根がすべて内側) か外側に根を持つかの
二択になる)。`Icc 0 1` は preconnected で `0∈U` だから `Icc 0 1 ⊆ U`、特に `1∈U`。 -/
theorem isStationary_of_path_no_unit_root {p : ℕ} (hp : 0 < p) {γ : ℝ → Fin p → ℝ}
    (hγ : Continuous γ) (h0 : IsStationary (γ 0))
    (hno : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 →
        z ^ p ≠ ∑ i : Fin p, (γ t i : ℂ) * z ^ (p - 1 - (i : ℕ))) :
    IsStationary (γ 1) := by
  set U : Set ℝ := γ ⁻¹' {φ : Fin p → ℝ | IsStationary φ} with hU
  set V : Set ℝ := γ ⁻¹' {φ : Fin p → ℝ | ∃ z : ℂ, 1 < ‖z‖ ∧
      z ^ p = ∑ i : Fin p, (φ i : ℂ) * z ^ (p - 1 - (i : ℕ))} with hV
  have hUopen : IsOpen U := (isOpen_isStationary hp).preimage hγ
  have hVopen : IsOpen V := (isOpen_hasOuterRoot hp).preimage hγ
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro t htU htV
    obtain ⟨z, hzgt, hzeq⟩ := htV
    exact absurd (htU z hzeq) (not_lt.mpr hzgt.le)
  have hsubset : Set.Icc (0 : ℝ) 1 ⊆ U ∪ V := by
    intro t ht
    by_cases h : IsStationary (γ t)
    · exact Or.inl h
    · refine Or.inr ?_
      unfold IsStationary at h
      push Not at h
      obtain ⟨z, hzeq, hzge⟩ := h
      have hzne1 : ‖z‖ ≠ 1 := fun heq => hno t ht z heq hzeq
      exact ⟨z, lt_of_le_of_ne hzge (Ne.symm hzne1), hzeq⟩
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∩ U := ⟨⟨le_refl 0, zero_le_one⟩, h0⟩
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ U :=
    isPreconnected_Icc.subset_left_of_subset_union hUopen hVopen hdisj hsubset ⟨0, hmem0⟩
  exact hsub ⟨zero_le_one, le_refl 1⟩

end StTopology
