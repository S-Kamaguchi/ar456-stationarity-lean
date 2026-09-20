import Mathlib
import StTopology.StationarityRegions
import StTopology.AR3
import StTopology.AR4
import StTopology.AR4Sufficiency
import StTopology.AR5
import StTopology.RootPerturbation
import StTopology.StOpen

set_option linter.style.header false

/-!
# AR(5) の定常性の十分性: `St5 φ → IsStationary φ`

`AR4Sufficiency.lean` と同型の方針。`St5` には既に `|φ_5|<1` が明示的に含まれているので
(`AR4` の `St4` と異なり、`|φ_4|<1` を別途導出する必要がない)、直接
`ψ := phiDown4 φ` (`AR5.lean` で定義済み) が `St4` を満たすことを4つの恒等式で示し、
`AR4.St4_imp_isStationary` で `ψ` の定常性を得たあと、`phiUpPath4`
(`AR5.lean` で定義済み、Step-down 補題のために作った経路をそのまま流用) で
`φ` の定常性を復元する。
-/

open Finset StTopology

namespace StTopology

/-! ### `ψ := phiDown4 φ` は `St4` を満たす -/

theorem St4_phiDown4_of_St5 {φ : Fin 5 → ℝ} (hSt5 : St5 φ) : St4 (phiDown4 φ) := by
  obtain ⟨h1, h2, h4lt1, h5, h6⟩ := hSt5
  have hpos : (0 : ℝ) < 1 - φ 4 := by linarith [(abs_lt.mp h4lt1).2]
  have hpos' : (0 : ℝ) < 1 + φ 4 := by linarith [(abs_lt.mp h4lt1).1]
  have hne : (1 : ℝ) - φ 4 ≠ 0 := hpos.ne'
  have hne' : (1 : ℝ) + φ 4 ≠ 0 := hpos'.ne'
  have hsqpos : (0 : ℝ) < 1 - φ 4 ^ 2 := by nlinarith [hpos, hpos']
  have hsqne : (1 : ℝ) - φ 4 ^ 2 ≠ 0 := hsqpos.ne'
  have hψ0 : phiDown4 φ 0 = (φ 0 + φ 4 * φ 3) / (1 - φ 4 ^ 2) := rfl
  have hψ1 : phiDown4 φ 1 = (φ 1 + φ 4 * φ 2) / (1 - φ 4 ^ 2) := rfl
  have hψ2 : phiDown4 φ 2 = (φ 2 + φ 4 * φ 1) / (1 - φ 4 ^ 2) := rfl
  have hψ3 : phiDown4 φ 3 = (φ 3 + φ 4 * φ 0) / (1 - φ 4 ^ 2) := rfl
  have hidPhi1 : phiAt1 (phiDown4 φ) * (1 - φ 4) = phiAt1 φ := by
    simp only [phiAt1, Fin.sum_univ_four, Fin.sum_univ_five, hψ0, hψ1, hψ2, hψ3]
    field_simp
    ring
  have hidPhiNeg1 : phiAtNeg1 (phiDown4 φ) * (1 + φ 4) = phiAtNeg1 φ := by
    simp only [phiAtNeg1, Fin.sum_univ_four, Fin.sum_univ_five, hψ0, hψ1, hψ2, hψ3]
    norm_num
    field_simp
    ring
  have hidCplx : (phiDown4 φ 2 + phiDown4 φ 0 * phiDown4 φ 3) * (phiDown4 φ 0 - phiDown4 φ 2)
        + (1 + phiDown4 φ 3) ^ 2 * (1 + phiDown4 φ 1 - phiDown4 φ 3)
      = -cplxCond5 φ / ((1 - φ 4) ^ 2 * (1 + φ 4) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    simp only [cplxCond5, A5, B5, hψ0, hψ1, hψ2, hψ3]
    field_simp
    ring
  have hidDiff : (phiDown4 φ 0 - phiDown4 φ 2) = B5 φ / (1 - φ 4 ^ 2) := by
    rw [hψ0, hψ2]; simp only [B5]; ring
  have hid1plus3 : (1 + phiDown4 φ 3) = A5 φ / (1 - φ 4 ^ 2) := by
    rw [hψ3, eq_div_iff hsqne]
    field_simp
    simp only [A5]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [hidPhi1, h1, hpos]
  · nlinarith [hidPhiNeg1, h2, hpos']
  · have hcube : (0 : ℝ) < (1 - φ 4) ^ 2 * (1 + φ 4) ^ 2 := by positivity
    have hnum : (0 : ℝ) < -cplxCond5 φ := neg_pos.mpr h5
    rw [hidCplx]
    exact div_pos hnum hcube
  · rw [hidDiff, hid1plus3, gt_iff_lt, abs_div, abs_of_pos hsqpos, div_lt_iff₀ hsqpos]
    have heq3 : 2 * (A5 φ / (1 - φ 4 ^ 2)) * (1 - φ 4 ^ 2) = 2 * A5 φ := by field_simp
    rw [heq3]
    exact h6

/-! ### `(ψ,0)` は定常 -/

theorem isStationary_pad0_of_isStationary4 {ψ0 ψ1 ψ2 ψ3 : ℝ}
    (hψ : IsStationary (![ψ0, ψ1, ψ2, ψ3] : Fin 4 → ℝ)) :
    IsStationary (![ψ0, ψ1, ψ2, ψ3, 0] : Fin 5 → ℝ) := by
  intro α hα
  simp [Fin.sum_univ_five] at hα
  have hfact : α * (α ^ 4 - (ψ0 : ℂ) * α ^ 3 - (ψ1 : ℂ) * α ^ 2 - (ψ2 : ℂ) * α - (ψ3 : ℂ))
      = 0 := by linear_combination hα
  rcases mul_eq_zero.mp hfact with h0 | hquartic
  · rw [h0]; simp
  · have hroot : α ^ 4 = ∑ i : Fin 4, (![ψ0, ψ1, ψ2, ψ3] i : ℂ) * α ^ (4 - 1 - (i : ℕ)) := by
      simp [Fin.sum_univ_four]
      linear_combination hquartic
    exact hψ α hroot

/-! ### 反射係数のスケーリング経路 (`phiUpPath4`, `AR5.lean` で定義済み) -/

theorem phiUpPath4_zero (φ : Fin 5 → ℝ) :
    phiUpPath4 φ 0 = ![phiDown4 φ 0, phiDown4 φ 1, phiDown4 φ 2, phiDown4 φ 3, 0] := by
  funext i
  fin_cases i <;> simp [phiUpPath4]

theorem phiUpPath4_one_of_St5 {φ : Fin 5 → ℝ} (hSt5 : St5 φ) : phiUpPath4 φ 1 = φ := by
  obtain ⟨h1, h2, h4lt1, h5, h6⟩ := hSt5
  have hpos : (0 : ℝ) < 1 - φ 4 := by linarith [(abs_lt.mp h4lt1).2]
  have hpos' : (0 : ℝ) < 1 + φ 4 := by linarith [(abs_lt.mp h4lt1).1]
  have hsqpos : (0 : ℝ) < 1 - φ 4 ^ 2 := by nlinarith [hpos, hpos']
  have hsqne : (1 : ℝ) - φ 4 ^ 2 ≠ 0 := hsqpos.ne'
  have hψ0 : phiDown4 φ 0 = (φ 0 + φ 4 * φ 3) / (1 - φ 4 ^ 2) := rfl
  have hψ1 : phiDown4 φ 1 = (φ 1 + φ 4 * φ 2) / (1 - φ 4 ^ 2) := rfl
  have hψ2 : phiDown4 φ 2 = (φ 2 + φ 4 * φ 1) / (1 - φ 4 ^ 2) := rfl
  have hψ3 : phiDown4 φ 3 = (φ 3 + φ 4 * φ 0) / (1 - φ 4 ^ 2) := rfl
  funext i
  fin_cases i <;> simp [phiUpPath4, hψ0, hψ1, hψ2, hψ3] <;> field_simp <;> ring

/-- **`phiUpPath4 φ t` は単位円上に根を持たない** (`t∈[0,1]`)。`ψ:=phiDown4 φ` は
`St4` を満たす (`St4_phiDown4_of_St5`) ので `AR4.St4_imp_isStationary` から定常。 -/
theorem phiUpPath4_no_unit_root {φ : Fin 5 → ℝ} (hSt5 : St5 φ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 →
      z ^ 5 ≠ ∑ i : Fin 5, (phiUpPath4 φ t i : ℂ) * z ^ (5 - 1 - (i : ℕ)) := by
  have hψSt4 : St4 (phiDown4 φ) := St4_phiDown4_of_St5 hSt5
  have hψStat : IsStationary (phiDown4 φ) := St4_imp_isStationary hψSt4
  have h4lt1 : |φ 4| < 1 := hSt5.2.2.1
  set ψ0 := phiDown4 φ 0
  set ψ1 := phiDown4 φ 1
  set ψ2 := phiDown4 φ 2
  set ψ3 := phiDown4 φ 3
  intro t ht z hz hcontra
  set Qψ : ℂ := z ^ 4 - (ψ0 : ℂ) * z ^ 3 - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z - (ψ3 : ℂ) with hQψdef
  set Qrev : ℂ := 1 - (ψ0 : ℂ) * z - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z ^ 3 - (ψ3 : ℂ) * z ^ 4
    with hQrevdef
  have hQψne : Qψ ≠ 0 := by
    intro hQ0
    have hroot : z ^ 4 = ∑ i : Fin 4, (phiDown4 φ i : ℂ) * z ^ (4 - 1 - (i : ℕ)) := by
      simp [Fin.sum_univ_four]
      linear_combination hQ0
    have := hψStat z hroot
    rw [hz] at this
    exact absurd this (lt_irrefl 1)
  have hrev_eq : Qrev = z ^ 4 * (starRingEnd ℂ) Qψ :=
    reversal_eq_on_unit_circle4 ψ0 ψ1 ψ2 ψ3 z hz
  have heq : z * Qψ = (t * φ 4 : ℝ) * Qrev := by
    simp [phiUpPath4, Fin.sum_univ_five] at hcontra
    push_cast at hcontra ⊢
    rw [hQψdef, hQrevdef]
    linear_combination hcontra
  have hnormeq : ‖z * Qψ‖ = ‖((t * φ 4 : ℝ) : ℂ) * Qrev‖ := by rw [heq]
  rw [norm_mul, norm_mul, hz, one_mul] at hnormeq
  rw [hrev_eq, norm_mul, norm_pow, hz, one_pow, one_mul, Complex.norm_conj] at hnormeq
  have hQψnormpos : 0 < ‖Qψ‖ := norm_pos_iff.mpr hQψne
  have hk'norm : ‖((t * φ 4 : ℝ) : ℂ)‖ = |t * φ 4| := Complex.norm_real _
  rw [hk'norm] at hnormeq
  have htabs : |t * φ 4| < 1 := by
    rw [abs_mul]
    rcases ht with ⟨ht0, ht1⟩
    have habst : |t| = t := abs_of_nonneg ht0
    rw [habst]
    calc t * |φ 4| ≤ 1 * |φ 4| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ = |φ 4| := by ring
      _ < 1 := h4lt1
  nlinarith [hnormeq, hQψnormpos, htabs]

/-! ### 仕上げ -/

theorem St5_imp_isStationary {φ : Fin 5 → ℝ} (hSt5 : St5 φ) : IsStationary φ := by
  have hψSt4 : St4 (phiDown4 φ) := St4_phiDown4_of_St5 hSt5
  have hψStat' : IsStationary
      (![phiDown4 φ 0, phiDown4 φ 1, phiDown4 φ 2, phiDown4 φ 3] : Fin 4 → ℝ) := by
    have heq : (![phiDown4 φ 0, phiDown4 φ 1, phiDown4 φ 2, phiDown4 φ 3] : Fin 4 → ℝ)
        = phiDown4 φ := by
      funext i; fin_cases i <;> simp
    rw [heq]; exact St4_imp_isStationary hψSt4
  have hγ0 : IsStationary (phiUpPath4 φ 0) := by
    rw [phiUpPath4_zero]
    exact isStationary_pad0_of_isStationary4 hψStat'
  have hresult : IsStationary (phiUpPath4 φ 1) :=
    isStationary_of_path_no_unit_root (by norm_num) (continuous_phiUpPath4 φ) hγ0
      (phiUpPath4_no_unit_root hSt5)
  rwa [phiUpPath4_one_of_St5 hSt5] at hresult

/-- **AR(5) の定常性の必要十分条件**: `St5 φ ↔ IsStationary φ`。 -/
theorem St5_iff_isStationary {φ : Fin 5 → ℝ} : St5 φ ↔ IsStationary φ :=
  ⟨St5_imp_isStationary, isStationary_imp_St5⟩

end StTopology
