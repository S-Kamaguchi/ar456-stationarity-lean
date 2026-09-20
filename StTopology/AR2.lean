import Mathlib
import StTopology.StationarityRegions

set_option linter.style.header false

/-!
# AR(2) の定常性: 古典的なJury三角形条件

`St4`/`St5`/`St6` の同値性証明に向けた、最小の完全なテストケースとして、
AR(2) について `St2 φ → IsStationary φ` (十分性) を示す。
必要性 (`IsStationary φ → St2 φ`) は今後の課題(実根の場合はコメントの通り
既に十分性側で使った恒等式の逆方向で示せるはずだが、非実根の場合の共役根
の議論を含め、別途取り組む)。
-/

open Finset StTopology

namespace StTopology

/-- St(2): 古典的なAR(2)定常性三角形 (6_kanren.tex 図1のキャプション参照)。
`φ 0 = φ_1, φ 1 = φ_2` の対応。 -/
def St2 (φ : Fin 2 → ℝ) : Prop :=
  φ 1 > -1 ∧ φ 0 + φ 1 < 1 ∧ φ 1 - φ 0 < 1

/-- 十分性: 三角形の内部なら定常 (根はすべて単位円の内側)。 -/
theorem St2.isStationary {φ : Fin 2 → ℝ} (h : St2 φ) : IsStationary φ := by
  obtain ⟨hp1, hg1, hgm1⟩ := h
  intro α hα
  have ha_eq : α ^ 2 = (φ 0 : ℂ) * α + (φ 1 : ℂ) := by
    simpa [Fin.sum_univ_two] using hα
  by_cases him : α.im = 0
  · -- 実根の場合
    have hre : α = ((α.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [him]
    set a := α.re with ha_def
    have ha_eq' : a ^ 2 = φ 0 * a + φ 1 := by
      have h2 := ha_eq
      rw [hre] at h2
      exact_mod_cast h2
    have hb : (1 - a) * (1 + a - φ 0) = 1 - φ 0 - φ 1 := by
      linear_combination -ha_eq'
    have hc : (1 + a) * (1 - a + φ 0) = 1 + φ 0 - φ 1 := by
      linear_combination -ha_eq'
    have hb_pos : (1 - a) * (1 + a - φ 0) > 0 := by linarith [hb]
    have hc_pos : (1 + a) * (1 - a + φ 0) > 0 := by linarith [hc]
    have ha1 : a < 1 := by nlinarith [hb_pos, hc_pos, ha_eq', hp1]
    have ha2 : a > -1 := by nlinarith [hb_pos, hc_pos, ha_eq', hp1]
    rw [hre]
    have hnorm : ‖((a : ℝ) : ℂ)‖ = |a| := by simp
    rw [hnorm, abs_lt]
    exact ⟨ha2, ha1⟩
  · -- 非実根の場合: 共役根も根であることを使い、Vieta の関係式から直接評価する
    have hconjeq : (starRingEnd ℂ) α ^ 2 = (φ 0 : ℂ) * (starRingEnd ℂ) α + (φ 1 : ℂ) := by
      have h := congrArg (starRingEnd ℂ) ha_eq
      simp only [map_add, map_mul, map_pow, Complex.conj_ofReal] at h
      exact h
    have hne : (starRingEnd ℂ) α ≠ α := by
      intro heq
      have hh := congrArg Complex.im heq
      rw [Complex.conj_im] at hh
      exact him (by linarith)
    have hne' : α - (starRingEnd ℂ) α ≠ 0 := sub_ne_zero.mpr hne.symm
    have hfactor : (α - (starRingEnd ℂ) α) * (α + (starRingEnd ℂ) α)
        = (α - (starRingEnd ℂ) α) * (φ 0 : ℂ) := by
      linear_combination ha_eq - hconjeq
    have hsum : α + (starRingEnd ℂ) α = (φ 0 : ℂ) :=
      mul_left_cancel₀ hne' hfactor
    have hprod : α * (starRingEnd ℂ) α = -(φ 1 : ℂ) := by
      linear_combination -ha_eq + α * hsum
    have hnormsq : (Complex.normSq α : ℂ) = -(φ 1 : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      linear_combination hprod
    have hnormsq_real : Complex.normSq α = -(φ 1) := by exact_mod_cast hnormsq
    have hlt : Complex.normSq α < 1 := by rw [hnormsq_real]; linarith [hp1]
    have hsq : ‖α‖ ^ 2 < 1 := by rw [Complex.sq_norm]; exact hlt
    nlinarith [norm_nonneg α, hsq]

/-- 必要性: 定常なら三角形の内部。判別式 `D = φ_1^2+4φ_2` の符号で
実根・複素共役根の2つの場合に分けて、根を具体的に構成し評価する。 -/
theorem St2.of_isStationary {φ : Fin 2 → ℝ} (h : IsStationary φ) : St2 φ := by
  set p0 := φ 0
  set p1 := φ 1
  set D := p0 ^ 2 + 4 * p1 with hD_def
  by_cases hDpos : 0 ≤ D
  · -- 実根の場合
    set d := Real.sqrt D with hd_def
    have hd2 : d ^ 2 = D := Real.sq_sqrt hDpos
    set r1 := (p0 + d) / 2 with hr1_def
    set r2 := (p0 - d) / 2 with hr2_def
    have heq1 : r1 ^ 2 = p0 * r1 + p1 := by
      have hexp : r1 ^ 2 - p0 * r1 - p1 = (d ^ 2 - D) / 4 := by
        rw [hr1_def]; ring
      rw [hd2] at hexp; linarith [hexp]
    have heq2 : r2 ^ 2 = p0 * r2 + p1 := by
      have hexp : r2 ^ 2 - p0 * r2 - p1 = (d ^ 2 - D) / 4 := by
        rw [hr2_def]; ring
      rw [hd2] at hexp; linarith [hexp]
    have hcα1 : (r1 : ℂ) ^ 2 = ∑ i : Fin 2, (φ i : ℂ) * (r1 : ℂ) ^ (2 - 1 - (i : ℕ)) := by
      simpa [Fin.sum_univ_two] using (by exact_mod_cast heq1 : (r1:ℂ) ^ 2 = (p0:ℂ) * r1 + (p1:ℂ))
    have hcα2 : (r2 : ℂ) ^ 2 = ∑ i : Fin 2, (φ i : ℂ) * (r2 : ℂ) ^ (2 - 1 - (i : ℕ)) := by
      simpa [Fin.sum_univ_two] using (by exact_mod_cast heq2 : (r2:ℂ) ^ 2 = (p0:ℂ) * r2 + (p1:ℂ))
    have hn1 : ‖(r1 : ℂ)‖ < 1 := h (r1 : ℂ) hcα1
    have hn2 : ‖(r2 : ℂ)‖ < 1 := h (r2 : ℂ) hcα2
    have habs1 : |r1| < 1 := by simpa using hn1
    have habs2 : |r2| < 1 := by simpa using hn2
    rw [abs_lt] at habs1 habs2
    obtain ⟨ha1, ha2⟩ := habs1
    obtain ⟨hb1, hb2⟩ := habs2
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [ha1, ha2, hb1, hb2, heq1, heq2, hr1_def, hr2_def]
    · nlinarith [ha1, ha2, hb1, hb2, heq1, heq2, hr1_def, hr2_def]
    · nlinarith [ha1, ha2, hb1, hb2, heq1, heq2, hr1_def, hr2_def]
  · -- 複素共役根の場合
    replace hDpos : D < 0 := not_le.mp hDpos
    set d := Real.sqrt (-D) with hd_def
    have hd2 : d ^ 2 = -D := Real.sq_sqrt (by linarith)
    have hdpos : 0 < d := Real.sqrt_pos.mpr (by linarith)
    set δ : ℂ := (d : ℂ) * Complex.I with hδ_def
    have hδ2 : δ ^ 2 = (D : ℂ) := by
      have h1 : δ ^ 2 = -((d : ℂ) ^ 2) := by
        rw [hδ_def]
        have h1a : ((d:ℂ) * Complex.I) ^ 2 = (d:ℂ) ^ 2 * Complex.I ^ 2 := by ring
        rw [h1a, Complex.I_sq]; ring
      rw [h1]
      have h2 : (d : ℂ) ^ 2 = ((d ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [h2, hd2]
      push_cast
      ring
    set r1 : ℂ := ((p0 : ℂ) + δ) / 2 with hr1_def
    have heq1 : r1 ^ 2 = (p0 : ℂ) * r1 + (p1 : ℂ) := by
      have hexp : r1 ^ 2 - (p0 : ℂ) * r1 - (p1 : ℂ) = (δ ^ 2 - (D : ℂ)) / 4 := by
        rw [hr1_def, hD_def]; push_cast; ring
      rw [hδ2] at hexp
      linear_combination hexp
    have hconj_r1 : (starRingEnd ℂ) r1 = ((p0 : ℂ) - δ) / 2 := by
      rw [hr1_def, hδ_def]
      simp only [map_div₀, map_add, map_mul, map_ofNat,
        Complex.conj_ofReal, Complex.conj_I]
      ring
    have hr1_ne_conj : (starRingEnd ℂ) r1 ≠ r1 := by
      rw [hconj_r1, hr1_def]
      intro hcontra
      have hδ0 : δ = 0 := by linear_combination -hcontra
      rw [hδ_def] at hδ0
      have hd0 : (d : ℂ) = 0 := by
        rcases mul_eq_zero.mp hδ0 with hh | hh
        · exact hh
        · exact absurd hh Complex.I_ne_zero
      have : d = 0 := by exact_mod_cast hd0
      linarith [hdpos]
    have hconjeq : (starRingEnd ℂ) r1 ^ 2
        = (p0 : ℂ) * (starRingEnd ℂ) r1 + (p1 : ℂ) := by
      have hc := congrArg (starRingEnd ℂ) heq1
      simp only [map_add, map_mul, map_pow, Complex.conj_ofReal] at hc
      exact hc
    set r2 : ℂ := (starRingEnd ℂ) r1 with hr2_def
    have hne' : r1 - r2 ≠ 0 := sub_ne_zero.mpr hr1_ne_conj.symm
    have hfactor : (r1 - r2) * (r1 + r2) = (r1 - r2) * (p0 : ℂ) := by
      linear_combination heq1 - hconjeq
    have hsum : r1 + r2 = (p0 : ℂ) := mul_left_cancel₀ hne' hfactor
    have hprod : r1 * r2 = -(p1 : ℂ) := by
      linear_combination -heq1 + r1 * hsum
    have hcα1 : r1 ^ 2 = ∑ i : Fin 2, (φ i : ℂ) * r1 ^ (2 - 1 - (i : ℕ)) := by
      simpa [Fin.sum_univ_two] using heq1
    have hn1 : ‖r1‖ < 1 := h r1 hcα1
    have hone_ne : (1 : ℂ) - r1 ≠ 0 := by
      intro hh
      apply hr1_ne_conj
      have hr1_eq_one : r1 = 1 := by linear_combination -hh
      rw [hr1_eq_one, hr2_def, hr1_eq_one]
      simp
    have hnegone_ne : (1 : ℂ) + r1 ≠ 0 := by
      intro hh
      apply hr1_ne_conj
      have hr1_eq_negone : r1 = -1 := by linear_combination hh
      rw [hr1_eq_negone, hr2_def, hr1_eq_negone]
      simp
    have hg1_eq : (1 - r1) * (1 - r2) = (1 : ℂ) - p0 - p1 := by
      linear_combination -hsum + hprod
    have hgm1_eq : (1 + r1) * (1 + r2) = (1 : ℂ) + p0 - p1 := by
      linear_combination hsum + hprod
    have hg1_normsq : ((Complex.normSq (1 - r1) : ℝ) : ℂ) = (1 : ℂ) - p0 - p1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      rw [show (starRingEnd ℂ) (1 - r1) = 1 - r2 by rw [hr2_def]; simp]
      linear_combination hg1_eq
    have hgm1_normsq : ((Complex.normSq (1 + r1) : ℝ) : ℂ) = (1 : ℂ) + p0 - p1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      rw [show (starRingEnd ℂ) (1 + r1) = 1 + r2 by rw [hr2_def]; simp]
      linear_combination hgm1_eq
    have hg1_real : Complex.normSq (1 - r1) = 1 - p0 - p1 := by exact_mod_cast hg1_normsq
    have hgm1_real : Complex.normSq (1 + r1) = 1 + p0 - p1 := by exact_mod_cast hgm1_normsq
    have hg1_pos : 0 < Complex.normSq (1 - r1) := (Complex.normSq_pos).mpr hone_ne
    have hgm1_pos : 0 < Complex.normSq (1 + r1) := (Complex.normSq_pos).mpr hnegone_ne
    have hprod_real : Complex.normSq r1 = -p1 := by
      have h1 : ((Complex.normSq r1 : ℝ) : ℂ) = -(p1 : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self, hr2_def] at *
        linear_combination hprod
      exact_mod_cast h1
    have hn1sq : ‖r1‖ ^ 2 < 1 := by
      have := norm_nonneg r1
      nlinarith [hn1, this]
    have hp1_bound : Complex.normSq r1 < 1 := by rw [Complex.sq_norm] at hn1sq; exact hn1sq
    refine ⟨?_, ?_, ?_⟩
    · rw [hprod_real] at hp1_bound; linarith
    · rw [hg1_real] at hg1_pos; linarith
    · rw [hgm1_real] at hgm1_pos; linarith

end StTopology
