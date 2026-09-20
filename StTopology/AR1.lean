import Mathlib
import StTopology.StationarityRegions

set_option linter.style.header false

/-!
# AR(1) の定常性: 古典的な |φ_1|<1 条件

一番小さいケース。`St4`/`St5`/`St6` の同値性証明に向けた足慣らし。
-/

open Finset StTopology

namespace StTopology

/-- St(1): 古典的なAR(1)定常性条件 -/
def St1 (φ : Fin 1 → ℝ) : Prop := |φ 0| < 1

theorem isStationary_iff_St1 (φ : Fin 1 → ℝ) : IsStationary φ ↔ St1 φ := by
  unfold IsStationary St1
  constructor
  · intro h
    have hα : (φ 0 : ℂ) ^ 1 = ∑ i : Fin 1, (φ i : ℂ) * (φ 0 : ℂ) ^ (1 - 1 - (i : ℕ)) := by
      simp
    have hres := h (φ 0 : ℂ) hα
    simpa using hres
  · intro h α hα
    have heq : α = (φ 0 : ℂ) := by simpa [Fin.sum_univ_one] using hα
    rw [heq]
    simpa using h

end StTopology
