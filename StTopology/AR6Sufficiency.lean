import Mathlib
import StTopology.StationarityRegions
import StTopology.AR3
import StTopology.AR4
import StTopology.AR4Sufficiency
import StTopology.AR5
import StTopology.AR5Sufficiency
import StTopology.AR6
import StTopology.RootPerturbation
import StTopology.StOpen

set_option linter.style.header false

/-!
# AR(6) の定常性の十分性: `St6 φ → IsStationary φ`

`AR5Sufficiency.lean` と同型の方針。`ψ := phiDown5 φ` (`AR6.lean` で定義済み) が `St5` を
満たすことを、`AR6.lean` の hypothesis (a)/(b) で確立済みの恒等式 (`cplxCond5(ψ)·(1-φ_6)²
(1+φ_6)^5=cplxCond6(φ)` および `(2A5(ψ)∓B5(ψ))(1-φ_6)(1+φ_6)²=∓(2A6±B6)`) を逆向きに使って
示し、`AR5.St5_imp_isStationary` で `ψ` の定常性を得たあと、`phiUpPath5`
(`AR6.lean` で定義済み、Step-down 補題のために作った経路をそのまま流用) で
`φ` の定常性を復元する。
-/

open Finset StTopology

namespace StTopology

/-! ### `ψ := phiDown5 φ` は `St5` を満たす -/

theorem St5_phiDown5_of_St6 {φ : Fin 6 → ℝ} (hSt6 : St6 φ) : St5 (phiDown5 φ) := by
  obtain ⟨h1, h2, hunit, h4, h5⟩ := hSt6
  have hsqpos : (0 : ℝ) < 1 - φ 5 ^ 2 := by
    have := abs_nonneg (φ 4 + φ 0 * φ 5); linarith [hunit]
  have hpos : (0 : ℝ) < 1 - φ 5 := by nlinarith [hsqpos, sq_nonneg (φ 5 - 1)]
  have hpos' : (0 : ℝ) < 1 + φ 5 := by nlinarith [hsqpos, sq_nonneg (φ 5 + 1)]
  have hne : (1 : ℝ) - φ 5 ≠ 0 := hpos.ne'
  have hne' : (1 : ℝ) + φ 5 ≠ 0 := hpos'.ne'
  have hsqne : (1 : ℝ) - φ 5 ^ 2 ≠ 0 := hsqpos.ne'
  have hψ0 : phiDown5 φ 0 = (φ 0 + φ 5 * φ 4) / (1 - φ 5 ^ 2) := rfl
  have hψ1 : phiDown5 φ 1 = (φ 1 + φ 5 * φ 3) / (1 - φ 5 ^ 2) := rfl
  have hψ2 : phiDown5 φ 2 = (φ 2 + φ 5 * φ 2) / (1 - φ 5 ^ 2) := rfl
  have hψ3 : phiDown5 φ 3 = (φ 3 + φ 5 * φ 1) / (1 - φ 5 ^ 2) := rfl
  have hψ4 : phiDown5 φ 4 = (φ 4 + φ 5 * φ 0) / (1 - φ 5 ^ 2) := rfl
  -- 条件1・2: `φ(±1)`。奇数個 (`Fin 5`) の和は `φ(1)`・`φ(-1)` いずれも `(1-φ_6)` 倍で一致する
  -- (偶数個の `AR5Sufficiency.lean` の場合と異なり `φ(-1)` 側も符号が反転しない、数値検証済み)。
  -- `field_simp` が `ψ_3=φ_3(1+φ_6)/(1-φ_6²)=φ_3/(1-φ_6)` を自動簡約してしまい分母のスケールが
  -- 不整合になるのを避けるため、まず `(1-φ_6²)` 倍の対称な形を経由する。
  have hidPhi1' : phiAt1 (phiDown5 φ) * (1 - φ 5 ^ 2) = phiAt1 φ * (1 + φ 5) := by
    simp only [phiAt1, Fin.sum_univ_five, Fin.sum_univ_six, hψ0, hψ1, hψ2, hψ3, hψ4]
    field_simp
    ring
  have hidPhi1 : phiAt1 (phiDown5 φ) * (1 - φ 5) = phiAt1 φ := by
    have h' : phiAt1 (phiDown5 φ) * (1 - φ 5) * (1 + φ 5) = phiAt1 φ * (1 + φ 5) := by
      rw [← hidPhi1']; ring
    exact mul_right_cancel₀ hne' h'
  have hidPhiNeg1' : phiAtNeg1 (phiDown5 φ) * (1 - φ 5 ^ 2) = phiAtNeg1 φ * (1 + φ 5) := by
    simp only [phiAtNeg1, Fin.sum_univ_five, Fin.sum_univ_six, hψ0, hψ1, hψ2, hψ3, hψ4]
    norm_num
    field_simp
    ring
  have hidPhiNeg1 : phiAtNeg1 (phiDown5 φ) * (1 - φ 5) = phiAtNeg1 φ := by
    have h' : phiAtNeg1 (phiDown5 φ) * (1 - φ 5) * (1 + φ 5) = phiAtNeg1 φ * (1 + φ 5) := by
      rw [← hidPhiNeg1']; ring
    exact mul_right_cancel₀ hne' h'
  -- 条件3: `|ψ_5|<1`
  have hψ4lt1 : |phiDown5 φ 4| < 1 := by
    rw [hψ4, abs_div, abs_of_pos hsqpos, div_lt_one hsqpos]
    have heq : φ 4 + φ 0 * φ 5 = φ 4 + φ 5 * φ 0 := by ring
    rw [← heq]; exact hunit
  -- 条件4: `cplxCond5(ψ)<0`
  have hidCplx : cplxCond5 (phiDown5 φ) * ((1 - φ 5) ^ 2 * (1 + φ 5) ^ 5) = cplxCond6 φ := by
    simp only [cplxCond5, cplxCond6, A5, B5, A6, B6, hψ0, hψ1, hψ2, hψ3, hψ4]
    field_simp
    ring
  have h4' : cplxCond6 φ < 0 := h4
  have hcplx5neg : cplxCond5 (phiDown5 φ) < 0 := by
    have hscale_pos : (0 : ℝ) < (1 - φ 5) ^ 2 * (1 + φ 5) ^ 5 :=
      mul_pos (pow_pos hpos 2) (pow_pos hpos' 5)
    nlinarith [hidCplx, h4', hscale_pos]
  -- 条件5: `2A5(ψ)>|B5(ψ)|`
  have hcube_pos : (0 : ℝ) < (1 - φ 5) * (1 + φ 5) ^ 2 := mul_pos hpos (pow_pos hpos' 2)
  have hident1 : (2 * A5 (phiDown5 φ) - B5 (phiDown5 φ)) * ((1 - φ 5) * (1 + φ 5) ^ 2)
      = B6 φ - 2 * A6 φ := by
    simp only [A5, B5, A6, B6, hψ0, hψ1, hψ2, hψ3, hψ4]
    field_simp
    ring
  have hident2 : (2 * A5 (phiDown5 φ) + B5 (phiDown5 φ)) * ((1 - φ 5) * (1 + φ 5) ^ 2)
      = -(2 * A6 φ + B6 φ) := by
    simp only [A5, B5, A6, B6, hψ0, hψ1, hψ2, hψ3, hψ4]
    field_simp
    ring
  have hB6gt : B6 φ > 2 * A6 φ := by linarith [(abs_lt.mp h5).1]
  have hB6lt : B6 φ < -(2 * A6 φ) := by linarith [(abs_lt.mp h5).2]
  have hc1 : 0 < (2 * A5 (phiDown5 φ) - B5 (phiDown5 φ)) * ((1 - φ 5) * (1 + φ 5) ^ 2) := by
    rw [hident1]; linarith [hB6gt]
  have hc2 : 0 < (2 * A5 (phiDown5 φ) + B5 (phiDown5 φ)) * ((1 - φ 5) * (1 + φ 5) ^ 2) := by
    rw [hident2]; linarith [hB6lt]
  have h1' : 0 < 2 * A5 (phiDown5 φ) - B5 (phiDown5 φ) := by
    by_contra hcon
    push Not at hcon
    exact absurd hc1 (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hcon hcube_pos.le))
  have h2' : 0 < 2 * A5 (phiDown5 φ) + B5 (phiDown5 φ) := by
    by_contra hcon
    push Not at hcon
    exact absurd hc2 (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hcon hcube_pos.le))
  have hcond5 : 2 * A5 (phiDown5 φ) > |B5 (phiDown5 φ)| := by
    rw [gt_iff_lt, abs_lt]; constructor <;> linarith [h1', h2']
  have hφAt1pos : 0 < phiAt1 (phiDown5 φ) := by
    by_contra hcon
    push Not at hcon
    have hle : phiAt1 (phiDown5 φ) * (1 - φ 5) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hpos.le
    rw [hidPhi1] at hle
    linarith [h1]
  have hφAtNeg1pos : 0 < phiAtNeg1 (phiDown5 φ) := by
    by_contra hcon
    push Not at hcon
    have hle : phiAtNeg1 (phiDown5 φ) * (1 - φ 5) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcon hpos.le
    rw [hidPhiNeg1] at hle
    linarith [h2]
  exact ⟨hφAt1pos, hφAtNeg1pos, hψ4lt1, hcplx5neg, hcond5⟩

/-! ### `(ψ,0)` は定常 -/

theorem isStationary_pad0_of_isStationary5 {ψ0 ψ1 ψ2 ψ3 ψ4 : ℝ}
    (hψ : IsStationary (![ψ0, ψ1, ψ2, ψ3, ψ4] : Fin 5 → ℝ)) :
    IsStationary (![ψ0, ψ1, ψ2, ψ3, ψ4, 0] : Fin 6 → ℝ) := by
  intro α hα
  simp [Fin.sum_univ_six] at hα
  have hfact : α * (α ^ 5 - (ψ0 : ℂ) * α ^ 4 - (ψ1 : ℂ) * α ^ 3 - (ψ2 : ℂ) * α ^ 2
      - (ψ3 : ℂ) * α - (ψ4 : ℂ)) = 0 := by linear_combination hα
  rcases mul_eq_zero.mp hfact with h0 | hquintic
  · rw [h0]; simp
  · have hroot : α ^ 5 = ∑ i : Fin 5, (![ψ0, ψ1, ψ2, ψ3, ψ4] i : ℂ) * α ^ (5 - 1 - (i : ℕ)) := by
      simp [Fin.sum_univ_five]
      linear_combination hquintic
    exact hψ α hroot

/-! ### 反射係数のスケーリング経路 (`phiUpPath5`, `AR6.lean` で定義済み) -/

theorem phiUpPath5_zero (φ : Fin 6 → ℝ) :
    phiUpPath5 φ 0
      = ![phiDown5 φ 0, phiDown5 φ 1, phiDown5 φ 2, phiDown5 φ 3, phiDown5 φ 4, 0] := by
  funext i
  fin_cases i <;> simp [phiUpPath5]

theorem phiUpPath5_one_of_St6 {φ : Fin 6 → ℝ} (hSt6 : St6 φ) : phiUpPath5 φ 1 = φ := by
  obtain ⟨h1, h2, hunit, h4, h5⟩ := hSt6
  have hsqpos : (0 : ℝ) < 1 - φ 5 ^ 2 := by
    have := abs_nonneg (φ 4 + φ 0 * φ 5); linarith [hunit]
  have hψ0 : phiDown5 φ 0 = (φ 0 + φ 5 * φ 4) / (1 - φ 5 ^ 2) := rfl
  have hψ1 : phiDown5 φ 1 = (φ 1 + φ 5 * φ 3) / (1 - φ 5 ^ 2) := rfl
  have hψ2 : phiDown5 φ 2 = (φ 2 + φ 5 * φ 2) / (1 - φ 5 ^ 2) := rfl
  have hψ3 : phiDown5 φ 3 = (φ 3 + φ 5 * φ 1) / (1 - φ 5 ^ 2) := rfl
  have hψ4 : phiDown5 φ 4 = (φ 4 + φ 5 * φ 0) / (1 - φ 5 ^ 2) := rfl
  funext i
  fin_cases i <;> simp [phiUpPath5, hψ0, hψ1, hψ2, hψ3, hψ4] <;> field_simp <;> ring

/-- **`phiUpPath5 φ t` は単位円上に根を持たない** (`t∈[0,1]`)。`ψ:=phiDown5 φ` は
`St5` を満たす (`St5_phiDown5_of_St6`) ので `AR5.St5_imp_isStationary` から定常。 -/
theorem phiUpPath5_no_unit_root {φ : Fin 6 → ℝ} (hSt6 : St6 φ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 →
      z ^ 6 ≠ ∑ i : Fin 6, (phiUpPath5 φ t i : ℂ) * z ^ (6 - 1 - (i : ℕ)) := by
  have hψSt5 : St5 (phiDown5 φ) := St5_phiDown5_of_St6 hSt6
  have hψStat : IsStationary (phiDown5 φ) := St5_imp_isStationary hψSt5
  have hunit := hSt6.2.2.1
  have hsqpos : (0 : ℝ) < 1 - φ 5 ^ 2 := by
    have := abs_nonneg (φ 4 + φ 0 * φ 5); linarith [hunit]
  have h5lt1 : |φ 5| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hsqpos, sq_nonneg (φ 5 - 1), sq_nonneg (φ 5 + 1)]
  set ψ0 := phiDown5 φ 0
  set ψ1 := phiDown5 φ 1
  set ψ2 := phiDown5 φ 2
  set ψ3 := phiDown5 φ 3
  set ψ4 := phiDown5 φ 4
  intro t ht z hz hcontra
  set Qψ : ℂ := z ^ 5 - (ψ0 : ℂ) * z ^ 4 - (ψ1 : ℂ) * z ^ 3 - (ψ2 : ℂ) * z ^ 2 - (ψ3 : ℂ) * z
    - (ψ4 : ℂ) with hQψdef
  set Qrev : ℂ := 1 - (ψ0 : ℂ) * z - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z ^ 3 - (ψ3 : ℂ) * z ^ 4
    - (ψ4 : ℂ) * z ^ 5 with hQrevdef
  have hQψne : Qψ ≠ 0 := by
    intro hQ0
    have hroot : z ^ 5 = ∑ i : Fin 5, (phiDown5 φ i : ℂ) * z ^ (5 - 1 - (i : ℕ)) := by
      simp [Fin.sum_univ_five]
      linear_combination hQ0
    have := hψStat z hroot
    rw [hz] at this
    exact absurd this (lt_irrefl 1)
  have hrev_eq : Qrev = z ^ 5 * (starRingEnd ℂ) Qψ :=
    reversal_eq_on_unit_circle5 ψ0 ψ1 ψ2 ψ3 ψ4 z hz
  have heq : z * Qψ = (t * φ 5 : ℝ) * Qrev := by
    simp [phiUpPath5, Fin.sum_univ_six] at hcontra
    push_cast at hcontra ⊢
    rw [hQψdef, hQrevdef]
    linear_combination hcontra
  have hnormeq : ‖z * Qψ‖ = ‖((t * φ 5 : ℝ) : ℂ) * Qrev‖ := by rw [heq]
  rw [norm_mul, norm_mul, hz, one_mul] at hnormeq
  rw [hrev_eq, norm_mul, norm_pow, hz, one_pow, one_mul, Complex.norm_conj] at hnormeq
  have hQψnormpos : 0 < ‖Qψ‖ := norm_pos_iff.mpr hQψne
  have hk'norm : ‖((t * φ 5 : ℝ) : ℂ)‖ = |t * φ 5| := Complex.norm_real _
  rw [hk'norm] at hnormeq
  have htabs : |t * φ 5| < 1 := by
    rw [abs_mul]
    rcases ht with ⟨ht0, ht1⟩
    have habst : |t| = t := abs_of_nonneg ht0
    rw [habst]
    calc t * |φ 5| ≤ 1 * |φ 5| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ = |φ 5| := by ring
      _ < 1 := h5lt1
  nlinarith [hnormeq, hQψnormpos, htabs]

/-! ### 仕上げ -/

theorem St6_imp_isStationary {φ : Fin 6 → ℝ} (hSt6 : St6 φ) : IsStationary φ := by
  have hψSt5 : St5 (phiDown5 φ) := St5_phiDown5_of_St6 hSt6
  have hψStat' : IsStationary
      (![phiDown5 φ 0, phiDown5 φ 1, phiDown5 φ 2, phiDown5 φ 3, phiDown5 φ 4] : Fin 5 → ℝ) := by
    have heq : (![phiDown5 φ 0, phiDown5 φ 1, phiDown5 φ 2, phiDown5 φ 3, phiDown5 φ 4]
        : Fin 5 → ℝ) = phiDown5 φ := by
      funext i; fin_cases i <;> simp
    rw [heq]; exact St5_imp_isStationary hψSt5
  have hγ0 : IsStationary (phiUpPath5 φ 0) := by
    rw [phiUpPath5_zero]
    exact isStationary_pad0_of_isStationary5 hψStat'
  have hresult : IsStationary (phiUpPath5 φ 1) :=
    isStationary_of_path_no_unit_root (by norm_num) (continuous_phiUpPath5 φ) hγ0
      (phiUpPath5_no_unit_root hSt6)
  rwa [phiUpPath5_one_of_St6 hSt6] at hresult

/-- **AR(6) の定常性の必要十分条件**: `St6 φ ↔ IsStationary φ`。 -/
theorem St6_iff_isStationary {φ : Fin 6 → ℝ} : St6 φ ↔ IsStationary φ :=
  ⟨St6_imp_isStationary, isStationary_imp_St6⟩

end StTopology
