import Mathlib

set_option linter.style.header false

/-!
# 絶対値和性 (Absolute value sum property)

論文 `10_section3_propositions.tex` (prop:abs-sum) / `5_kanren.tex` の命題。

AR(p) の係数 φ_1,…,φ_p が `∑|φ_i| < 1` を満たすなら、特性方程式
`α^p = φ_1 α^{p-1} + ⋯ + φ_p` の根 α はすべて `|α| < 1` を満たす
(= その AR(p) 過程は定常)。

証明はRouchéの定理を使わず、三角不等式のみで完結する初等的な議論:
`|α| ≥ 1` と仮定すると
`|α|^p ≤ (∑|φ_i|) |α|^{p-1} < |α|^{p-1}`
となり、`|α| < 1` が従って矛盾。
-/

open Finset

/-- 絶対値和性: `∑ |φ i| < 1` ならば、特性方程式の根はすべて単位円の内側にある。 -/
theorem abs_sum_stationary {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ)
    (hsum : ∑ i, |φ i| < 1) (α : ℂ)
    (hα : α ^ p = ∑ i : Fin p, (φ i : ℂ) * α ^ (p - 1 - (i : ℕ))) :
    ‖α‖ < 1 := by
  by_contra h
  rw [not_lt] at h
  have hpos : 0 < ‖α‖ := lt_of_lt_of_le one_pos h
  -- Step 1: |α|^p = |∑ φ_i α^{p-1-i}| ≤ ∑ |φ_i| |α|^{p-1-i}
  have step1 : ‖α‖ ^ p ≤ ∑ i : Fin p, |φ i| * ‖α‖ ^ (p - 1 - (i : ℕ)) := by
    calc ‖α‖ ^ p = ‖α ^ p‖ := (norm_pow α p).symm
      _ = ‖∑ i : Fin p, (φ i : ℂ) * α ^ (p - 1 - (i : ℕ))‖ := by rw [hα]
      _ ≤ ∑ i : Fin p, ‖(φ i : ℂ) * α ^ (p - 1 - (i : ℕ))‖ := norm_sum_le _ _
      _ = ∑ i : Fin p, |φ i| * ‖α‖ ^ (p - 1 - (i : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [norm_pow]
  -- Step 2: 各項は |α| ≥ 1 なので |α|^{p-1-i} ≤ |α|^{p-1} で置き換えられる
  have step2 : ∑ i : Fin p, |φ i| * ‖α‖ ^ (p - 1 - (i : ℕ))
      ≤ ∑ i : Fin p, |φ i| * ‖α‖ ^ (p - 1) := by
    apply Finset.sum_le_sum
    intro i _
    have : ‖α‖ ^ (p - 1 - (i : ℕ)) ≤ ‖α‖ ^ (p - 1) :=
      pow_le_pow_right₀ h (by omega)
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  -- Step 3: 仮定 ∑|φ_i| < 1 を使う
  have step3 : (∑ i : Fin p, |φ i|) * ‖α‖ ^ (p - 1) < 1 * ‖α‖ ^ (p - 1) :=
    mul_lt_mul_of_pos_right hsum (pow_pos hpos (p - 1))
  rw [Finset.sum_mul, one_mul] at step3
  have chain : ‖α‖ ^ p < ‖α‖ ^ (p - 1) := lt_of_le_of_lt (step1.trans step2) step3
  -- p = (p-1)+1 として α^p = α^{p-1} * α に書き換え、矛盾を導く
  have hp1 : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos hp).symm
  have hpow : ‖α‖ ^ p = ‖α‖ ^ (p - 1) * ‖α‖ := by
    conv_lhs => rw [hp1]
    rw [pow_succ]
  rw [hpow] at chain
  have hmul : ‖α‖ ^ (p - 1) ≤ ‖α‖ ^ (p - 1) * ‖α‖ :=
    le_mul_of_one_le_right (pow_pos hpos (p - 1)).le h
  linarith
