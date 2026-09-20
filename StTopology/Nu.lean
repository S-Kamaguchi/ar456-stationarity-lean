import Mathlib
import StTopology.StConnected

set_option linter.style.header false

/-!
# `ν`(絶対値和ゲージ)の定義と基本性質

論文 `5_kanren.tex`, Section 3.9 の `ν(φ) := ∑|φ_i|`。`AbsSum.lean` の
`abs_sum_stationary`(`∑|φ_i|<1 ⟹ IsStationary φ`)の左辺そのもので、
`C_p := {φ | ν(φ) < 1}` のゲージ。`μ` との比較を経由して共有動径座標 `r(φ)`
(`lem:r-welldef`)を構成する土台になる(`OpenBall_formalization_plan.md` 3節)。
-/

open Finset

namespace StTopology

/-- `ν(φ) := ∑ᵢ|φᵢ|`。`AbsSum.lean` の `abs_sum_stationary` の仮定 `∑|φ_i|<1` の
左辺、`StOpen.lean` の `S₀` と同じ式。 -/
def nu {p : ℕ} (φ : Fin p → ℝ) : ℝ := ∑ i, |φ i|

theorem nu_nonneg {p : ℕ} (φ : Fin p → ℝ) : 0 ≤ nu φ :=
  Finset.sum_nonneg fun i _ => abs_nonneg (φ i)

/-- `ν` は各座標を(絶対値で)上から抑える: `|φᵢ| ≤ ν(φ)`(`Ξ`の`O_p`での連続性で使う)。 -/
theorem abs_le_nu {p : ℕ} (φ : Fin p → ℝ) (i : Fin p) : |φ i| ≤ nu φ :=
  Finset.single_le_sum (fun j _ => abs_nonneg (φ j)) (Finset.mem_univ i)

/-- **`ν` の `0`-点特徴づけ**: `ν(φ) = 0 ↔ φ = O_p`。 -/
theorem nu_eq_zero_iff {p : ℕ} (φ : Fin p → ℝ) : nu φ = 0 ↔ φ = fun _ => 0 := by
  unfold nu
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (φ i)]
  constructor
  · intro h
    funext i
    exact abs_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h i _
    rw [h]
    simp

/-- `ν(γ_t φ) = ∑ᵢ t^{i+1}|φᵢ|` (`t ≥ 0`)。`gammaT` の定義 `t^{i+1}φᵢ` から
`|t^{i+1}φᵢ| = t^{i+1}|φᵢ|` (`t≥0` なので `|t|=t`)。 -/
theorem nu_gammaT {p : ℕ} (φ : Fin p → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    nu (gammaT t φ) = ∑ i : Fin p, t ^ ((i : ℕ) + 1) * |φ i| := by
  unfold nu gammaT
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_mul, abs_pow, abs_of_nonneg ht]

/-- **`lem:nu-mono`(弱)**: `t ↦ ν(γ_t φ)` は `[0,∞)` 上単調非減少。各単項式
`t^{i+1}|φᵢ|` が(係数 `|φᵢ|≥0` ゆえ)`t` について単調非減少であることの
`Finset.sum` としての合成。 -/
theorem nu_gammaT_monotoneOn {p : ℕ} (φ : Fin p → ℝ) :
    MonotoneOn (fun t : ℝ => nu (gammaT t φ)) (Set.Ici 0) := by
  intro t₁ ht₁ t₂ ht₂ hle
  simp only [Set.mem_Ici] at ht₁ ht₂
  change nu (gammaT t₁ φ) ≤ nu (gammaT t₂ φ)
  rw [nu_gammaT φ ht₁, nu_gammaT φ ht₂]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht₁ hle _) (abs_nonneg _)

/-- **`lem:nu-mono`(狭義)**: `φ≠O_p`(`ν(φ)≠0`)ならば `t ↦ ν(γ_t φ)` は `[0,∞)`
上狭義単調増加。`φᵢ≠0` となる添字 `i₀` での単項式が狭義に増加することと、
残りの項の単調性(弱)を `Finset.sum_lt_sum` で合成する。`lem:r-welldef`
(共有動径座標 `r(φ)` の一意性)で使う。 -/
theorem nu_gammaT_strictMonoOn {p : ℕ} {φ : Fin p → ℝ} (hφ : nu φ ≠ 0) :
    StrictMonoOn (fun t : ℝ => nu (gammaT t φ)) (Set.Ici 0) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  simp only [Set.mem_Ici] at ht₁ ht₂
  change nu (gammaT t₁ φ) < nu (gammaT t₂ φ)
  rw [nu_gammaT φ ht₁, nu_gammaT φ ht₂]
  have hex : ∃ i : Fin p, φ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ ((nu_eq_zero_iff φ).mpr (funext hcon))
  obtain ⟨i₀, hi₀⟩ := hex
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht₁ hlt.le _) (abs_nonneg _)
  · exact ⟨i₀, Finset.mem_univ i₀,
      mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hlt ht₁ (by omega)) (abs_pos.mpr hi₀)⟩

/-- `t ↦ ν(γ_t φ)` の連続性(`lem:r-welldef` の `ε`-`δ` 論法で使う)。各単項式
`t^{i+1}|φᵢ|` の連続性の有限和。 -/
theorem continuous_nu_gammaT {p : ℕ} (φ : Fin p → ℝ) :
    Continuous (fun t : ℝ => nu (gammaT t φ)) := by
  unfold nu gammaT
  fun_prop

/-- `ν(s • φ) = s · ν(φ)` (`s ≥ 0`)。`ν` の斉次性(単純なスカラー倍版、
`lem:crystal-closure` の `s → 1⁻` スケーリングで使う)。 -/
theorem nu_smul {p : ℕ} (φ : Fin p → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    nu (s • φ) = s * nu φ := by
  unfold nu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hs]

/-- `ν : (Fin p → ℝ) → ℝ` は連続(有限和 `∑ᵢ|φᵢ|` の各項が連続)。 -/
theorem continuous_nu {p : ℕ} : Continuous (nu : (Fin p → ℝ) → ℝ) := by
  unfold nu
  fun_prop

/-! ### `lem:crystal-closure`: `closure C_p = {ν≤1}`

`lem:closure`(`closure_isStationary`)と全く同型の証明パターン。`gammaT`を
単純なスカラー倍`s • φ`に、`isStationary_iff_mu_lt_one`/`isOpen_isStationary`を
`ν`の定義そのもの/`continuous_nu`に置き換えるだけで踏襲できる
(`OpenBall_formalization_plan.md` 4節)。 -/

/-- **クロスポリトープ`C_p`の閉包**: `closure {φ | ν(φ)<1} = {φ | ν(φ)≤1}`。 -/
theorem closure_crystal {p : ℕ} :
    closure {φ : Fin p → ℝ | nu φ < 1} = {φ : Fin p → ℝ | nu φ ≤ 1} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro φ hφ
      simp only [Set.mem_setOf_eq] at hφ
      exact hφ.le
    · exact isClosed_le continuous_nu continuous_const
  · intro φ hφ
    simp only [Set.mem_setOf_eq] at hφ
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hcont : Continuous (fun s : ℝ => s • φ) := by fun_prop
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuous_iff.mp hcont 1 ε hε
    set s : ℝ := 1 - min δ 1 / 2 with hsdef
    have hδ'pos : 0 < min δ 1 / 2 := by
      have : 0 < min δ 1 := lt_min hδpos one_pos
      linarith
    have hmin_le1 : min δ 1 ≤ 1 := min_le_right δ 1
    have hmin_leδ : min δ 1 ≤ δ := min_le_left δ 1
    have hs0 : 0 ≤ s := by rw [hsdef]; linarith
    have hslt1 : s < 1 := by rw [hsdef]; linarith
    have hs1 : dist s 1 < δ := by
      rw [Real.dist_eq, hsdef]
      have habs : |1 - min δ 1 / 2 - 1| = min δ 1 / 2 := by
        rw [show (1 : ℝ) - min δ 1 / 2 - 1 = -(min δ 1 / 2) by ring, abs_neg,
          abs_of_pos hδ'pos]
      rw [habs]
      linarith
    have hcrystal : nu (s • φ) < 1 := by
      rw [nu_smul φ hs0]
      have hle : s * nu φ ≤ s * 1 := mul_le_mul_of_nonneg_left hφ hs0
      rw [mul_one] at hle
      linarith
    refine ⟨s • φ, hcrystal, ?_⟩
    have hd := hδ s hs1
    rw [one_smul, dist_comm] at hd
    exact hd

end StTopology
