import Mathlib
import StTopology.StationarityRegions

set_option linter.style.header false

/-!
# Cauchy 型の根の評価: 根は有界領域に閉じ込められる

AR(p) の逆特性方程式 `α^p = φ_1 α^{p-1} + ⋯ + φ_p` の任意の根 `α` について、
係数だけで決まる明示的な上界

  `‖α‖ ≤ 1 + ∑ᵢ |φ_i|`

が成り立つことを示す。これは St(p) の開集合性を示す議論の第一段階
(「根はコンパクト集合の中にしか存在しえない」) にあたる。

古典的な Cauchy の評価は `1 + max_i |φ_i|` という、より鋭い上界を与えるが、
その証明には等比級数の総和と `p-1-i` の添字の付け替えが必要になる。
ここでの目的 (根が有界領域に入ること) には和による評価で十分であり、
証明は `AbsSum.lean` の三角不等式の議論をそのまま再利用できる。

証明の構造は `abs_sum_stationary` と同一:
`‖α‖ > 1` の場合に `‖α‖^{p-1-i} ≤ ‖α‖^{p-1}` で各項を上から押さえ、
`‖α‖^p = ‖α‖^{p-1}·‖α‖` と `‖α‖^{p-1} > 0` で割る。
`‖α‖ ≤ 1` の場合は `∑|φ_i| ≥ 0` から直ちに従う。
-/

open Finset

namespace StTopology

/-- **Cauchy 型の根の評価**: 逆特性方程式の任意の根は
`1 + ∑|φ_i|` 以下のノルムを持つ。 -/
theorem root_norm_le {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) (α : ℂ)
    (hα : α ^ p = ∑ i : Fin p, (φ i : ℂ) * α ^ (p - 1 - (i : ℕ))) :
    ‖α‖ ≤ 1 + ∑ i, |φ i| := by
  have hSnonneg : 0 ≤ ∑ i, |φ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  by_cases hle : ‖α‖ ≤ 1
  · linarith
  · -- ‖α‖ > 1 の場合: AbsSum.lean と同じ三角不等式の議論
    replace hle : (1 : ℝ) < ‖α‖ := not_le.mp hle
    have h : (1 : ℝ) ≤ ‖α‖ := hle.le
    have hpos : 0 < ‖α‖ := lt_of_lt_of_le one_pos h
    have step1 : ‖α‖ ^ p ≤ ∑ i : Fin p, |φ i| * ‖α‖ ^ (p - 1 - (i : ℕ)) := by
      calc ‖α‖ ^ p = ‖α ^ p‖ := (norm_pow α p).symm
        _ = ‖∑ i : Fin p, (φ i : ℂ) * α ^ (p - 1 - (i : ℕ))‖ := by rw [hα]
        _ ≤ ∑ i : Fin p, ‖(φ i : ℂ) * α ^ (p - 1 - (i : ℕ))‖ := norm_sum_le _ _
        _ = ∑ i : Fin p, |φ i| * ‖α‖ ^ (p - 1 - (i : ℕ)) := by
            apply Finset.sum_congr rfl
            intro i _
            simp [norm_pow]
    have step2 : ∑ i : Fin p, |φ i| * ‖α‖ ^ (p - 1 - (i : ℕ))
        ≤ ∑ i : Fin p, |φ i| * ‖α‖ ^ (p - 1) := by
      apply Finset.sum_le_sum
      intro i _
      have : ‖α‖ ^ (p - 1 - (i : ℕ)) ≤ ‖α‖ ^ (p - 1) :=
        pow_le_pow_right₀ h (by omega)
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
    rw [← Finset.sum_mul] at step2
    have hchain : ‖α‖ ^ p ≤ (∑ i, |φ i|) * ‖α‖ ^ (p - 1) := step1.trans step2
    have hp1 : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos hp).symm
    have hpow : ‖α‖ ^ p = ‖α‖ ^ (p - 1) * ‖α‖ := by
      conv_lhs => rw [hp1]
      rw [pow_succ]
    rw [hpow] at hchain
    have hposp : 0 < ‖α‖ ^ (p - 1) := pow_pos hpos (p - 1)
    nlinarith [hchain, hposp]

end StTopology
