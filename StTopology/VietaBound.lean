import Mathlib
import StTopology.StationarityRegions

set_option linter.style.header false

/-!
# Vieta の公式による「最後の係数の絶対値 < 1」の一般証明

AR(p) の逆特性方程式 `z^p - (φ_1 z^{p-1}+⋯+φ_p) = 0` に対応する ℂ 係数多項式を
`charPoly φ` とする。これは monic な p 次多項式であり、ℂ が代数的閉体であることから
分解 (`Splits`) する。Vieta の公式 (`Polynomial.Splits.coeff_zero_eq_prod_roots_of_monic`)
により、定数項は (符号を除いて) 全根の積に等しい。

`IsStationary φ` ならば全ての根のノルムが1未満なので、定数項の絶対値
(= `|φ_p|`, Lean の 0-始まり添字では `φ (最後の添字)`) は
「1未満の数を p 個掛けた積」として、やはり 1 未満になる。

これは AR(3) の `1>|φ_3|` や、AR(4) の Remark 1 (`|φ_4|<1` が自動的に従う) に
対応する一般的 (p に依存しない) な事実であり、判別式や `St(p)` の開集合性・
連結性の議論に一切依存せずに、`IsStationary` の定義から直接証明できる。
-/

open Finset Polynomial

namespace StTopology

/-- AR(p) の逆特性方程式に対応する ℂ 係数多項式:
`Q(z) = z^p - (φ_1 z^{p-1} + ⋯ + φ_p)`. -/
noncomputable def charPoly {p : ℕ} (φ : Fin p → ℝ) : Polynomial ℂ :=
  Polynomial.X ^ p - ∑ i : Fin p, Polynomial.C (φ i : ℂ) * Polynomial.X ^ (p - 1 - (i : ℕ))

theorem charPoly_eval {p : ℕ} (φ : Fin p → ℝ) (z : ℂ) :
    (charPoly φ).eval z = z ^ p - ∑ i : Fin p, (φ i : ℂ) * z ^ (p - 1 - (i : ℕ)) := by
  simp [charPoly, Polynomial.eval_finsetSum]

theorem charPoly_sub_natDegree_lt {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    (∑ i : Fin p, Polynomial.C (φ i : ℂ) * Polynomial.X ^ (p - 1 - (i : ℕ))).natDegree < p := by
  have hle : (∑ i : Fin p, Polynomial.C (φ i : ℂ) * Polynomial.X ^ (p - 1 - (i : ℕ))).natDegree
      ≤ p - 1 :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have hip : (i : ℕ) < p := i.2; omega))
  omega

theorem charPoly_sub_degree_lt {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    (∑ i : Fin p, Polynomial.C (φ i : ℂ) * Polynomial.X ^ (p - 1 - (i : ℕ))).degree
      < (p : WithBot ℕ) := by
  set R := ∑ i : Fin p, Polynomial.C (φ i : ℂ) * Polynomial.X ^ (p - 1 - (i : ℕ)) with hR
  rcases eq_or_ne R 0 with hR0 | hR0
  · rw [hR0, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe p
  · rw [Polynomial.degree_eq_natDegree hR0]
    exact_mod_cast charPoly_sub_natDegree_lt hp φ

theorem charPoly_degree {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    (charPoly φ).degree = (p : ℕ) := by
  unfold charPoly
  rw [Polynomial.degree_sub_eq_left_of_degree_lt (by
    rw [Polynomial.degree_X_pow]; exact charPoly_sub_degree_lt hp φ)]
  exact Polynomial.degree_X_pow p

theorem charPoly_natDegree {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    (charPoly φ).natDegree = p :=
  Polynomial.natDegree_eq_of_degree_eq_some (charPoly_degree hp φ)

theorem charPoly_monic {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) : (charPoly φ).Monic := by
  unfold charPoly
  exact Polynomial.monic_X_pow_sub (charPoly_sub_degree_lt hp φ)

/-- **一般化された Remark**: `IsStationary φ` ならば、最後の係数 `φ_p`
(Lean の 0-始まり添字では `φ ⟨p-1,_⟩`) は絶対値1未満である。
AR(3) では `p=2` を指定すれば `|φ_3|<1`、AR(4) では `p=3` を指定すれば
`|φ_4|<1` が直ちに得られる (判別式や開集合性の議論は一切不要)。 -/
theorem abs_last_coeff_lt_one {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : IsStationary φ) :
    |φ ⟨p - 1, by omega⟩| < 1 := by
  set lastIdx : Fin p := ⟨p - 1, by omega⟩ with hlastIdx
  set Q := charPoly φ with hQ
  have hQmonic : Q.Monic := charPoly_monic hp φ
  have hQsplits : Q.Splits := IsAlgClosed.splits Q
  have hQdeg : Q.natDegree = p := charPoly_natDegree hp φ
  have hroots_lt : ∀ r ∈ Q.roots, ‖r‖ < 1 := by
    intro r hr
    have hIsRoot : Q.IsRoot r := (Polynomial.mem_roots'.mp hr).2
    have heval : Q.eval r = 0 := hIsRoot
    rw [charPoly_eval] at heval
    have heq : r ^ p = ∑ i : Fin p, (φ i : ℂ) * r ^ (p - 1 - (i : ℕ)) := by
      linear_combination heval
    exact hφ r heq
  have hvieta := hQsplits.coeff_zero_eq_prod_roots_of_monic hQmonic
  rw [hQdeg] at hvieta
  have hcoeff0 : Q.coeff 0 = -(φ lastIdx : ℂ) := by
    have hX : (Polynomial.X ^ p : Polynomial ℂ).coeff 0 = 0 := by
      rw [Polynomial.coeff_X_pow, if_neg (by omega)]
    have hRcoeff : (∑ i : Fin p, Polynomial.C (φ i : ℂ) * Polynomial.X ^ (p - 1 - (i : ℕ))).coeff 0
        = (φ lastIdx : ℂ) := by
      rw [Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single lastIdx]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        have hz : p - 1 - (lastIdx : ℕ) = 0 := by simp [hlastIdx]
        simp [hz]
      · intro i _ hne
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        have hne0 : ¬ (0 = p - 1 - (i : ℕ)) := by
          intro heqc
          apply hne
          apply Fin.ext
          change (i : ℕ) = p - 1
          have hip : (i : ℕ) < p := i.2
          omega
        simp [hne0]
      · intro h
        exact absurd (Finset.mem_univ lastIdx) h
    change (Polynomial.X ^ p
        - ∑ i : Fin p, Polynomial.C (φ i : ℂ) * Polynomial.X ^ (p - 1 - (i : ℕ))).coeff 0
        = -(φ lastIdx : ℂ)
    rw [Polynomial.coeff_sub, hX, hRcoeff]
    ring
  rw [hcoeff0] at hvieta
  have hnorm : ‖(φ lastIdx : ℂ)‖ = ‖Q.roots.prod‖ := by
    have hcongr := congrArg (‖·‖) hvieta
    simpa [norm_mul, norm_neg, norm_pow] using hcongr
  have hnorm_prod : ‖Q.roots.prod‖ = (Q.roots.map (‖·‖)).prod := by
    induction Q.roots using Multiset.induction with
    | empty => simp
    | cons a s ih => simp [Multiset.prod_cons, ih]
  rw [hnorm_prod] at hnorm
  have hcard : (Q.roots.map (‖·‖)).card = p := by
    rw [Multiset.card_map, ← hQdeg, hQsplits.natDegree_eq_card_roots]
  have hmem : ∀ x ∈ Q.roots.map (‖·‖), 0 ≤ x ∧ x < 1 := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨r, hr, hrx⟩ := hx
    subst hrx
    exact ⟨norm_nonneg r, hroots_lt r hr⟩
  have hprod_le_one : ∀ s : Multiset ℝ, (∀ x ∈ s, 0 ≤ x ∧ x < 1) → 0 ≤ s.prod ∧ s.prod ≤ 1 := by
    intro s hs
    induction s using Multiset.induction with
    | empty => simp
    | cons a t ih =>
      have ha : 0 ≤ a ∧ a < 1 := hs a (Multiset.mem_cons_self a t)
      have ht : ∀ x ∈ t, 0 ≤ x ∧ x < 1 := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
      obtain ⟨ht0, ht1⟩ := ih ht
      rw [Multiset.prod_cons]
      exact ⟨mul_nonneg ha.1 ht0,
        le_trans (mul_le_mul_of_nonneg_left ht1 ha.1) (by linarith [ha.2])⟩
  have hs_ne : Q.roots.map (‖·‖) ≠ 0 := by
    intro hcontra
    rw [hcontra] at hcard
    simp at hcard
    omega
  obtain ⟨a, hmemA⟩ := Multiset.exists_mem_of_ne_zero hs_ne
  obtain ⟨t, hst⟩ := Multiset.exists_cons_of_mem hmemA
  have ha : 0 ≤ a ∧ a < 1 := hmem a hmemA
  have ht_mem : ∀ x ∈ t, 0 ≤ x ∧ x < 1 := fun x hx => hmem x (hst ▸ Multiset.mem_cons_of_mem hx)
  obtain ⟨ht0, ht1⟩ := hprod_le_one t ht_mem
  have hprod_eq : (Q.roots.map (‖·‖)).prod = a * t.prod := by rw [hst, Multiset.prod_cons]
  rw [hprod_eq] at hnorm
  have hfinal : a * t.prod < 1 := by
    calc a * t.prod ≤ a * 1 := mul_le_mul_of_nonneg_left ht1 ha.1
      _ = a := mul_one a
      _ < 1 := ha.2
  rw [← hnorm] at hfinal
  simpa using hfinal

end StTopology
