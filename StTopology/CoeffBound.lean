import Mathlib
import StTopology.Mu

set_option linter.style.header false

/-!
# 一般化された Vieta による係数の評価、および `closure St(p)` のコンパクト性

論文 `5_kanren.tex`, Section 2.3 の一般的な主張(`abs_last_coeff_lt_one` の一般化):
「逆特性方程式の根と係数の関係(Vieta の公式)と、根がすべて単位円内にあることから
`|φ_m| < C(p,m)` (`1≤m≤p`) が従う」。ここでは根が(開でなく)閉単位円内、
すなわち `μ(φ)≤1` の場合の非狭義版 `|φ_i| ≤ C(p,i+1)` を示し(Lean は `φ` を
`0`-始まり添字にしているので、論文の `m` は `i+1` に対応)、これを使って
`closure St(p) = {μ≤1}` のコンパクト性を示す(`prop:xi-homeo` の `O_p` での
連続性に必要、`OpenBall_formalization_plan.md` 6節)。

`Multiset.esymm`(基本対称式)を経由した一般化 Vieta
(`Polynomial.coeff_eq_esymm_roots_of_splits`)が核心: `charPoly φ` は monic で
分解するので、係数は根の基本対称式(符号付き)に一致する。根のノルムがすべて
`R` 以下なら、`k` 次基本対称式は「`k` 個の根の積」の(`C(s.card,k)` 個の)和なので、
そのノルムは `C(s.card,k)·R^k` で抑えられる。
-/

open Finset Polynomial

namespace StTopology

/-- 根のノルムがすべて `R` 以下の `k` 個の積のノルムは `R^k` 以下。 -/
theorem norm_prod_le_of_forall_norm_le {t : Multiset ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hmem : ∀ x ∈ t, ‖x‖ ≤ R) : ‖t.prod‖ ≤ R ^ t.card := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha : ‖a‖ ≤ R := hmem a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, ‖x‖ ≤ R := fun x hx => hmem x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.prod_cons, Multiset.card_cons]
    calc ‖a * s.prod‖ = ‖a‖ * ‖s.prod‖ := norm_mul a s.prod
      _ ≤ R * R ^ s.card := mul_le_mul ha (ih hs) (norm_nonneg _) hR
      _ = R ^ (s.card + 1) := by rw [← pow_succ']

/-- `f`, `g : α → ℝ` が `u` 上で `f ≤ g` なら、`map`した和も `≤`。 -/
theorem multiset_sum_map_le_sum_map {α : Type*} {u : Multiset α} {f g : α → ℝ}
    (h : ∀ x ∈ u, f x ≤ g x) : (u.map f).sum ≤ (u.map g).sum := by
  induction u using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha : f a ≤ g a := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, f x ≤ g x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    linarith [ih hs]

/-- **`k` 次基本対称式のノルム評価**: 根のノルムがすべて `R` 以下なら、
`k` 次基本対称式 `esymm s k` のノルムは `C(s.card,k)·R^k` 以下。 -/
theorem norm_esymm_le {s : Multiset ℂ} {R : ℝ} (hR : 0 ≤ R) (hmem : ∀ x ∈ s, ‖x‖ ≤ R)
    (n : ℕ) : ‖s.esymm n‖ ≤ (s.card.choose n : ℝ) * R ^ n := by
  unfold Multiset.esymm
  calc ‖((s.powersetCard n).map Multiset.prod).sum‖
      ≤ (((s.powersetCard n).map Multiset.prod).map (‖·‖)).sum := norm_multiset_sum_le _
    _ = ((s.powersetCard n).map (fun t => ‖t.prod‖)).sum := by rw [Multiset.map_map]; rfl
    _ ≤ ((s.powersetCard n).map (fun _ => R ^ n)).sum := by
        apply multiset_sum_map_le_sum_map
        intro t ht
        have ht' := Multiset.mem_powersetCard.mp ht
        have htmem : ∀ x ∈ t, ‖x‖ ≤ R := fun x hx => hmem x (Multiset.mem_of_le ht'.1 hx)
        calc ‖t.prod‖ ≤ R ^ t.card := norm_prod_le_of_forall_norm_le hR htmem
          _ = R ^ n := by rw [ht'.2]
    _ = (s.card.choose n : ℝ) * R ^ n := by
        rw [Multiset.map_const', Multiset.sum_replicate, Multiset.card_powersetCard, nsmul_eq_mul]

/-- `(charPoly φ).coeff (p-1-i) = -(φ i : ℂ)`(`charPoly = X^p - ∑...` と
`charPoly_sub_coeff` から)。 -/
theorem charPoly_coeff_eq {p : ℕ} (φ : Fin p → ℝ) (i : Fin p) :
    (charPoly φ).coeff (p - 1 - (i : ℕ)) = -(φ i : ℂ) := by
  have hcoeff := charPoly_sub_coeff φ i
  have hi : (i : ℕ) < p := i.2
  unfold charPoly
  rw [Polynomial.coeff_sub]
  have hXpow : (Polynomial.X ^ p : Polynomial ℂ).coeff (p - 1 - (i : ℕ)) = 0 := by
    rw [Polynomial.coeff_X_pow, if_neg (by omega)]
  rw [hXpow, hcoeff]
  ring

/-- **係数の一般評価**(論文 Section 2.3): 逆特性方程式の根がすべてノルム `R`
以下なら、`|φ_i| ≤ C(p,i+1)·R^{i+1}`(論文の添字 `m=i+1`、`1≤m≤p`)。 -/
theorem abs_coeff_le_of_roots_norm_le {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hbound : ∀ z ∈ (charPoly φ).roots, ‖z‖ ≤ R) (i : Fin p) :
    |φ i| ≤ (p.choose ((i : ℕ) + 1) : ℝ) * R ^ ((i : ℕ) + 1) := by
  have hmonic := charPoly_monic hp φ
  have hsplits : (charPoly φ).Splits := IsAlgClosed.splits _
  have hdeg := charPoly_natDegree hp φ
  have hi : (i : ℕ) < p := i.2
  have hk : p - 1 - (i : ℕ) ≤ (charPoly φ).natDegree := by rw [hdeg]; omega
  have hvieta := Polynomial.coeff_eq_esymm_roots_of_splits hsplits hk
  rw [hdeg, hmonic, charPoly_coeff_eq φ i, one_mul] at hvieta
  have hexp : p - (p - 1 - (i : ℕ)) = (i : ℕ) + 1 := by omega
  rw [hexp] at hvieta
  have hnegone : ‖(-1 : ℂ) ^ ((i : ℕ) + 1)‖ = 1 := by
    rw [norm_pow]; norm_num
  have hcongr := congrArg (‖·‖) hvieta
  rw [norm_neg, norm_mul, hnegone, one_mul, Complex.norm_real, Real.norm_eq_abs] at hcongr
  rw [hcongr]
  have hcard : (charPoly φ).roots.card = p := charPoly_roots_card hp φ
  have hesymm := norm_esymm_le hR hbound ((i : ℕ) + 1)
  rwa [hcard] at hesymm

/-- **`μ(φ)≤1` のときの係数評価**: `|φ_i| ≤ C(p,i+1)`(`R=1` の特殊ケース)。 -/
theorem abs_coeff_le_choose {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : mu hp φ ≤ 1)
    (i : Fin p) : |φ i| ≤ (p.choose ((i : ℕ) + 1) : ℝ) := by
  have hbound : ∀ z ∈ (charPoly φ).roots, ‖z‖ ≤ 1 := by
    intro z hz
    have hzmem : z ∈ (charPoly φ).roots.toFinset := Multiset.mem_toFinset.mpr hz
    calc ‖z‖ ≤ mu hp φ := by unfold mu; exact Finset.le_sup' (‖·‖) hzmem
      _ ≤ 1 := hφ
  have := abs_coeff_le_of_roots_norm_le hp φ (by norm_num : (0 : ℝ) ≤ 1) hbound i
  simpa using this

/-- **`closure St(p)` のコンパクト性**(`prop:xi-homeo` の `O_p` での連続性に必要)。
`closure St(p) = {μ≤1}` は閉(`closure_isStationary` + `continuous_mu`)かつ
`abs_coeff_le_choose` による明示的な箱 `∏ᵢ[-C(p,i+1),C(p,i+1)]`(コンパクト、
`isCompact_univ_pi`)の閉部分集合。 -/
theorem isCompact_closure_isStationary {p : ℕ} (hp : 0 < p) :
    IsCompact (closure {φ : Fin p → ℝ | IsStationary φ}) := by
  rw [closure_isStationary hp]
  have hbox : IsCompact (Set.univ.pi
      (fun i : Fin p => Set.Icc (-(p.choose ((i : ℕ) + 1) : ℝ)) (p.choose ((i : ℕ) + 1) : ℝ))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  refine hbox.of_isClosed_subset (isClosed_le (continuous_mu hp) continuous_const) ?_
  intro φ hφ i _
  rw [Set.mem_Icc]
  exact abs_le.mp (abs_coeff_le_choose hp hφ i)

end StTopology
