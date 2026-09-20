import Mathlib
import StTopology.Xi

set_option linter.style.header false

/-!
# `lem:crystal-ball`: クロスポリトープは球である

論文 `5_kanren.tex`, Section 3.9 の `lem:crystal-ball`。`σ(x) := (‖x‖/ν(x))·x`
(`x≠0`、`σ(0):=O_p`)は `closed_B^p := {x | ‖x‖≤1}`(通常の Euclid 閉球)から
`closure C_p := {ψ | ν(ψ)≤1}` への同相写像であり、単位球面 `S^{p-1}` を `∂C_p`
の上に制限する。

`Fin p → ℝ` の既定の(`dist`/`Metric.continuous_iff` 等がこれまで使ってきた)ノルムは
座標ごとの `sup` ノルムであり、論文の通常の Euclid ノルムとは異なるので、`‖·‖`
記法とは衝突しない独立関数 `euclideanNorm` として定義する(有限次元空間では
どのノルムも位相は同じなので、`Fin p → ℝ` 上の(`sup`ノルム由来の)位相をそのまま
使ってよい)。
-/

open Finset

namespace StTopology

/-- ℝᵖ の通常の Euclid ノルム `‖x‖₂ = √(∑ᵢxᵢ²)`。 -/
noncomputable def euclideanNorm {p : ℕ} (x : Fin p → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

theorem euclideanNorm_nonneg {p : ℕ} (x : Fin p → ℝ) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

theorem euclideanNorm_eq_zero_iff {p : ℕ} (x : Fin p → ℝ) :
    euclideanNorm x = 0 ↔ x = fun _ => 0 := by
  unfold euclideanNorm
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _]
  constructor
  · intro h
    funext i
    exact pow_eq_zero_iff two_ne_zero |>.mp (h i (Finset.mem_univ i))
  · intro h i _
    rw [h]; ring

theorem euclideanNorm_smul {p : ℕ} {s : ℝ} (hs : 0 ≤ s) (x : Fin p → ℝ) :
    euclideanNorm (s • x) = s * euclideanNorm x := by
  unfold euclideanNorm
  have hsum : ∑ i, (s • x) i ^ 2 = s ^ 2 * ∑ i, (x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [hsum, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

theorem continuous_euclideanNorm {p : ℕ} : Continuous (euclideanNorm : (Fin p → ℝ) → ℝ) := by
  unfold euclideanNorm
  fun_prop

/-- **`ν` と Euclid ノルムの同値性**: `ν(x) ≥ c·‖x‖₂` となる `c>0` が存在する。
`{x|‖x‖₂=1}` がコンパクト(有界閉)であることと、`ν`がそこで連続かつ`0`にならない
ことから最小値を取り(`IsCompact.exists_isMinOn`)、斉次性(`nu_smul`・
`euclideanNorm_smul`)でスケーリングして任意の `x` に拡張する。 -/
theorem exists_nu_ge_euclideanNorm {p : ℕ} (hp : 0 < p) :
    ∃ c > 0, ∀ x : Fin p → ℝ, c * euclideanNorm x ≤ nu x := by
  set S : Set (Fin p → ℝ) := {x | euclideanNorm x = 1} with hSdef
  have hbox : IsCompact (Set.univ.pi (fun _ : Fin p => Set.Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hSclosed : IsClosed S := isClosed_eq continuous_euclideanNorm continuous_const
  have hSsub : S ⊆ Set.univ.pi (fun _ : Fin p => Set.Icc (-1 : ℝ) 1) := by
    intro x hx
    simp only [hSdef, Set.mem_setOf_eq, euclideanNorm] at hx
    have hxsq : ∀ i : Fin p, (x i) ^ 2 ≤ 1 := by
      intro i
      have := Real.sqrt_eq_one.mp hx
      calc (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        _ = 1 := this
    intro i _
    rw [Set.mem_Icc, ← abs_le, ← sq_le_one_iff_abs_le_one]
    exact hxsq i
  have hScompact : IsCompact S := hbox.of_isClosed_subset hSclosed hSsub
  have hSne : S.Nonempty := by
    refine ⟨Pi.single ⟨0, hp⟩ 1, ?_⟩
    simp only [hSdef, Set.mem_setOf_eq, euclideanNorm]
    rw [Finset.sum_eq_single ⟨0, hp⟩]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcont : ContinuousOn nu S := continuous_nu.continuousOn
  obtain ⟨x₀, hx₀mem, hx₀min⟩ := hScompact.exists_isMinOn hSne hcont
  have hx₀pos : 0 < nu x₀ := by
    have hx₀ne : x₀ ≠ fun _ => 0 := by
      intro h
      rw [h] at hx₀mem
      simp only [hSdef, Set.mem_setOf_eq, (euclideanNorm_eq_zero_iff _).mpr rfl] at hx₀mem
      norm_num at hx₀mem
    exact (nu_nonneg x₀).lt_of_ne (fun h => hx₀ne ((nu_eq_zero_iff x₀).mp h.symm))
  refine ⟨nu x₀, hx₀pos, ?_⟩
  intro x
  by_cases hx0 : x = fun _ => 0
  · simp [hx0, euclideanNorm, (nu_eq_zero_iff _).mpr rfl]
  · have hxnorm0 : euclideanNorm x ≠ 0 := fun h => hx0 ((euclideanNorm_eq_zero_iff x).mp h)
    have hxnormpos : 0 < euclideanNorm x := (euclideanNorm_nonneg x).lt_of_ne (Ne.symm hxnorm0)
    have hmem : (euclideanNorm x)⁻¹ • x ∈ S := by
      simp only [hSdef, Set.mem_setOf_eq]
      rw [euclideanNorm_smul (by positivity), mul_comm, mul_inv_cancel₀ hxnorm0]
    have hle : nu x₀ ≤ (euclideanNorm x)⁻¹ * nu x := by
      have hmin := hx₀min hmem
      simp only [Set.mem_setOf_eq] at hmin
      rwa [nu_smul x (inv_nonneg.mpr (euclideanNorm_nonneg x))] at hmin
    calc nu x₀ * euclideanNorm x ≤ (euclideanNorm x)⁻¹ * nu x * euclideanNorm x :=
          mul_le_mul_of_nonneg_right hle (euclideanNorm_nonneg x)
      _ = nu x := by field_simp

/-- 各座標は Euclid ノルムで抑えられる: `|xᵢ| ≤ ‖x‖₂`。 -/
theorem abs_le_euclideanNorm {p : ℕ} (x : Fin p → ℝ) (i : Fin p) : |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- 通常の(座標ごとの `sup`)距離は Euclid ノルムで抑えられる。 -/
theorem dist_le_euclideanNorm {p : ℕ} (x : Fin p → ℝ) :
    dist x (fun _ => (0 : ℝ)) ≤ euclideanNorm x := by
  rw [dist_pi_le_iff (euclideanNorm_nonneg x)]
  intro i
  rw [Real.dist_eq, sub_zero]
  exact abs_le_euclideanNorm x i

/-- 逆に、Euclid ノルムは `sup` 距離を(次元の平方根倍で)抑える。 -/
theorem euclideanNorm_le_sqrt_mul_dist {p : ℕ} (x : Fin p → ℝ) :
    euclideanNorm x ≤ Real.sqrt p * dist x (fun _ => 0) := by
  unfold euclideanNorm
  have hsum : ∑ i, (x i) ^ 2 ≤ (p : ℝ) * (dist x (fun _ => (0 : ℝ))) ^ 2 := by
    calc ∑ i, (x i) ^ 2 ≤ ∑ _i : Fin p, (dist x (fun _ => (0 : ℝ))) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have h1 : |x i| ≤ dist x (fun _ => (0 : ℝ)) := by
            have := dist_le_pi_dist x (fun _ => (0 : ℝ)) i
            rwa [Real.dist_eq, sub_zero] at this
          calc (x i) ^ 2 = |x i| ^ 2 := (sq_abs _).symm
            _ ≤ (dist x (fun _ => (0 : ℝ))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (p : ℝ) * (dist x (fun _ => (0 : ℝ))) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i, (x i) ^ 2)
      ≤ Real.sqrt ((p : ℝ) * (dist x (fun _ => (0 : ℝ))) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt p * Real.sqrt ((dist x (fun _ => (0 : ℝ))) ^ 2) :=
        Real.sqrt_mul (Nat.cast_nonneg p) _
    _ = Real.sqrt p * dist x (fun _ => (0 : ℝ)) := by rw [Real.sqrt_sq dist_nonneg]

/-! ### `σ`, `τ`: `closed_B^p` と `closure C_p` の同相 -/

/-- `σ(x) := (‖x‖₂/ν(x))·x`(`x≠0`)、`σ(O_p):=O_p`。`closed_B^p → closure C_p`。 -/
noncomputable def sigmaMap {p : ℕ} (x : Fin p → ℝ) : Fin p → ℝ :=
  if x = fun _ => 0 then x else (euclideanNorm x / nu x) • x

/-- `τ(ψ) := (ν(ψ)/‖ψ‖₂)·ψ`(`ψ≠O_p`)、`τ(O_p):=O_p`。`closure C_p → closed_B^p`
(`σ` の逆写像)。 -/
noncomputable def tauMap {p : ℕ} (ψ : Fin p → ℝ) : Fin p → ℝ :=
  if ψ = fun _ => 0 then ψ else (nu ψ / euclideanNorm ψ) • ψ

theorem sigmaMap_zero {p : ℕ} : sigmaMap (fun _ : Fin p => (0 : ℝ)) = fun _ => 0 := by
  unfold sigmaMap; rw [if_pos rfl]

theorem tauMap_zero {p : ℕ} : tauMap (fun _ : Fin p => (0 : ℝ)) = fun _ => 0 := by
  unfold tauMap; rw [if_pos rfl]

theorem sigmaMap_of_ne_zero {p : ℕ} {x : Fin p → ℝ} (hx : x ≠ fun _ => 0) :
    sigmaMap x = (euclideanNorm x / nu x) • x := by
  unfold sigmaMap; rw [if_neg hx]

theorem tauMap_of_ne_zero {p : ℕ} {ψ : Fin p → ℝ} (hψ : ψ ≠ fun _ => 0) :
    tauMap ψ = (nu ψ / euclideanNorm ψ) • ψ := by
  unfold tauMap; rw [if_neg hψ]

/-- **`ν∘σ=‖·‖₂`**: 論文の `ν(σ(x))=‖x‖ν(x)/ν(x)=‖x‖`。 -/
theorem nu_sigmaMap {p : ℕ} {x : Fin p → ℝ} (hx : x ≠ fun _ => 0) :
    nu (sigmaMap x) = euclideanNorm x := by
  have hnuxpos : 0 < nu x := (nu_nonneg x).lt_of_ne (fun h => hx ((nu_eq_zero_iff x).mp h.symm))
  rw [sigmaMap_of_ne_zero hx, nu_smul x (div_nonneg (euclideanNorm_nonneg x) hnuxpos.le)]
  field_simp

/-- **`‖τ(ψ)‖₂=ν`**: 論文の `‖τ(ψ)‖=ν(ψ)`。 -/
theorem euclideanNorm_tauMap {p : ℕ} {ψ : Fin p → ℝ} (hψ : ψ ≠ fun _ => 0) :
    euclideanNorm (tauMap ψ) = nu ψ := by
  have hψnormpos : 0 < euclideanNorm ψ :=
    (euclideanNorm_nonneg ψ).lt_of_ne (fun h => hψ ((euclideanNorm_eq_zero_iff ψ).mp h.symm))
  rw [tauMap_of_ne_zero hψ, euclideanNorm_smul (div_nonneg (nu_nonneg ψ) hψnormpos.le) ψ]
  field_simp

/-- **`σ,τ` は互いに逆写像**(`σ`側)。 -/
theorem sigmaMap_tauMap {p : ℕ} (ψ : Fin p → ℝ) : sigmaMap (tauMap ψ) = ψ := by
  by_cases hψ : ψ = fun _ => 0
  · rw [hψ, tauMap_zero, sigmaMap_zero]
  · have hψnupos : 0 < nu ψ := (nu_nonneg ψ).lt_of_ne (fun h => hψ ((nu_eq_zero_iff ψ).mp h.symm))
    have hψnormpos : 0 < euclideanNorm ψ :=
      (euclideanNorm_nonneg ψ).lt_of_ne (fun h => hψ ((euclideanNorm_eq_zero_iff ψ).mp h.symm))
    rw [tauMap_of_ne_zero hψ]
    set c : ℝ := nu ψ / euclideanNorm ψ with hcdef
    have hcpos : 0 < c := by rw [hcdef]; positivity
    set ψ' : Fin p → ℝ := c • ψ with hψ'def
    have hψ'0 : ψ' ≠ fun _ => 0 := by
      rw [hψ'def]
      intro h
      rcases smul_eq_zero.mp h with h1 | h2
      · exact hcpos.ne' h1
      · exact hψ h2
    have hnuψ' : nu ψ' = c * nu ψ := by rw [hψ'def]; exact nu_smul ψ hcpos.le
    have hnormψ' : euclideanNorm ψ' = nu ψ := by
      rw [hψ'def, euclideanNorm_smul hcpos.le, hcdef]
      field_simp
    rw [sigmaMap_of_ne_zero hψ'0, hnuψ', hnormψ']
    have hscalar : nu ψ / (c * nu ψ) * c = 1 := by rw [hcdef]; field_simp
    rw [hψ'def, smul_smul, hscalar, one_smul]

/-- **`σ,τ` は互いに逆写像**(`τ`側)。 -/
theorem tauMap_sigmaMap {p : ℕ} (x : Fin p → ℝ) : tauMap (sigmaMap x) = x := by
  by_cases hx : x = fun _ => 0
  · rw [hx, sigmaMap_zero, tauMap_zero]
  · have hxnupos : 0 < nu x := (nu_nonneg x).lt_of_ne (fun h => hx ((nu_eq_zero_iff x).mp h.symm))
    have hxnormpos : 0 < euclideanNorm x :=
      (euclideanNorm_nonneg x).lt_of_ne (fun h => hx ((euclideanNorm_eq_zero_iff x).mp h.symm))
    rw [sigmaMap_of_ne_zero hx]
    set c : ℝ := euclideanNorm x / nu x with hcdef
    have hcpos : 0 < c := by rw [hcdef]; positivity
    set x' : Fin p → ℝ := c • x with hx'def
    have hx'0 : x' ≠ fun _ => 0 := by
      rw [hx'def]
      intro h
      rcases smul_eq_zero.mp h with h1 | h2
      · exact hcpos.ne' h1
      · exact hx h2
    have hnormx' : euclideanNorm x' = c * euclideanNorm x := by
      rw [hx'def]; exact euclideanNorm_smul hcpos.le x
    have hnux' : nu x' = euclideanNorm x := by
      rw [hx'def, nu_smul x hcpos.le, hcdef]
      field_simp
    rw [tauMap_of_ne_zero hx'0, hnux', hnormx']
    have hscalar : euclideanNorm x / (c * euclideanNorm x) * c = 1 := by
      rw [hcdef]; field_simp
    rw [hx'def, smul_smul, hscalar, one_smul]

theorem continuous_euclideanNorm_div_nu_smul_of_ne_zero {p : ℕ} {x₀ : Fin p → ℝ}
    (hx₀ : x₀ ≠ fun _ => 0) :
    ContinuousAt (fun x : Fin p → ℝ => (euclideanNorm x / nu x) • x) x₀ := by
  have hnux₀ne : nu x₀ ≠ 0 := fun h => hx₀ ((nu_eq_zero_iff x₀).mp h)
  have hdiv : ContinuousAt (fun x : Fin p → ℝ => euclideanNorm x / nu x) x₀ :=
    continuous_euclideanNorm.continuousAt.div continuous_nu.continuousAt hnux₀ne
  exact ContinuousAt.comp₂ continuous_smul.continuousAt hdiv continuousAt_id

theorem continuous_nu_div_euclideanNorm_smul_of_ne_zero {p : ℕ} {ψ₀ : Fin p → ℝ}
    (hψ₀ : ψ₀ ≠ fun _ => 0) :
    ContinuousAt (fun ψ : Fin p → ℝ => (nu ψ / euclideanNorm ψ) • ψ) ψ₀ := by
  have hnormψ₀ne : euclideanNorm ψ₀ ≠ 0 := fun h => hψ₀ ((euclideanNorm_eq_zero_iff ψ₀).mp h)
  have hdiv : ContinuousAt (fun ψ : Fin p → ℝ => nu ψ / euclideanNorm ψ) ψ₀ :=
    continuous_nu.continuousAt.div continuous_euclideanNorm.continuousAt hnormψ₀ne
  exact ContinuousAt.comp₂ continuous_smul.continuousAt hdiv continuousAt_id

/-- **`σ` の `O_p` を除いた連続性**。 -/
theorem continuousAt_sigmaMap_of_ne_zero {p : ℕ} {x₀ : Fin p → ℝ} (hx₀ : x₀ ≠ fun _ => 0) :
    ContinuousAt sigmaMap x₀ := by
  refine (continuous_euclideanNorm_div_nu_smul_of_ne_zero hx₀).congr ?_
  filter_upwards [isOpen_ne.mem_nhds hx₀] with x hx
  rw [sigmaMap_of_ne_zero hx]

/-- **`τ` の `O_p` を除いた連続性**。 -/
theorem continuousAt_tauMap_of_ne_zero {p : ℕ} {ψ₀ : Fin p → ℝ} (hψ₀ : ψ₀ ≠ fun _ => 0) :
    ContinuousAt tauMap ψ₀ := by
  refine (continuous_nu_div_euclideanNorm_smul_of_ne_zero hψ₀).congr ?_
  filter_upwards [isOpen_ne.mem_nhds hψ₀] with ψ hψ
  rw [tauMap_of_ne_zero hψ]

/-- `closed_B^p := {x | ‖x‖₂≤1}`(通常の Euclid 閉球)。`Fin p → ℝ` 自体の位相
(既定の `sup` 距離由来、有限次元なのでどのノルムでも同じ位相になる)を保ったまま、
この`euclideanNorm`による**集合**として定義する。 -/
def closedBallEuclid (p : ℕ) : Set (Fin p → ℝ) := {x | euclideanNorm x ≤ 1}

/-- **`σ` の `O_p` での連続性**: `‖σ(x)‖₂ ≤ ‖x‖₂/c ≤ (√p/c)·dist(x,O_p) → 0`
(`exists_nu_ge_euclideanNorm` の同値定数 `c` と `euclideanNorm_le_sqrt_mul_dist`)。 -/
theorem continuousAt_sigmaMap_zero {p : ℕ} (hp : 0 < p) :
    ContinuousAt sigmaMap (fun _ : Fin p => (0 : ℝ)) := by
  obtain ⟨c, hcpos, hc⟩ := exists_nu_ge_euclideanNorm hp
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨c * ε / Real.sqrt p, by positivity, fun x hxdist => ?_⟩
  rw [sigmaMap_zero]
  have hbound : euclideanNorm (sigmaMap x) ≤ euclideanNorm x / c := by
    by_cases hx : x = fun _ => 0
    · rw [hx, sigmaMap_zero, (euclideanNorm_eq_zero_iff _).mpr rfl]; norm_num
    · have hxnormpos : 0 < euclideanNorm x :=
        (euclideanNorm_nonneg x).lt_of_ne (fun h => hx ((euclideanNorm_eq_zero_iff x).mp h.symm))
      have hxnupos : 0 < nu x := (nu_nonneg x).lt_of_ne (fun h => hx ((nu_eq_zero_iff x).mp h.symm))
      rw [sigmaMap_of_ne_zero hx,
        euclideanNorm_smul (div_nonneg (euclideanNorm_nonneg x) (nu_nonneg x)) x]
      rw [div_mul_eq_mul_div]
      rw [div_le_div_iff₀ hxnupos hcpos]
      nlinarith [hc x, hxnormpos]
  have hxsmall : euclideanNorm x < c * ε := by
    calc euclideanNorm x ≤ Real.sqrt p * dist x (fun _ => 0) := euclideanNorm_le_sqrt_mul_dist x
      _ < Real.sqrt p * (c * ε / Real.sqrt p) := by
          apply mul_lt_mul_of_pos_left hxdist (Real.sqrt_pos.mpr (by exact_mod_cast hp))
      _ = c * ε := by field_simp
  calc dist (sigmaMap x) (fun _ => (0 : ℝ)) ≤ euclideanNorm (sigmaMap x) :=
        dist_le_euclideanNorm _
    _ ≤ euclideanNorm x / c := hbound
    _ < ε := by rw [div_lt_iff₀ hcpos]; linarith [hxsmall]

/-- **`τ` の `O_p` での連続性**: `‖τ(ψ)‖₂=ν(ψ)`(`euclideanNorm_tauMap`)から
`ν`の連続性(`continuous_nu`)に直接帰着する(`σ`側と違って係数評価は不要)。 -/
theorem continuousAt_tauMap_zero {p : ℕ} :
    ContinuousAt tauMap (fun _ : Fin p => (0 : ℝ)) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hcontnu : ContinuousAt (nu : (Fin p → ℝ) → ℝ) (fun _ => (0 : ℝ)) :=
    continuous_nu.continuousAt
  rw [Metric.continuousAt_iff] at hcontnu
  obtain ⟨δ, hδpos, hδ⟩ := hcontnu ε hε
  refine ⟨δ, hδpos, fun ψ hψdist => ?_⟩
  have hnuψ : dist (nu ψ) (nu (fun _ => (0 : ℝ))) < ε := hδ hψdist
  rw [(nu_eq_zero_iff _).mpr rfl, Real.dist_eq, sub_zero, abs_of_nonneg (nu_nonneg ψ)] at hnuψ
  rw [tauMap_zero]
  by_cases hψ : ψ = fun _ => 0
  · rw [hψ, tauMap_zero]
    simpa using hε
  · calc dist (tauMap ψ) (fun _ => (0 : ℝ)) ≤ euclideanNorm (tauMap ψ) := dist_le_euclideanNorm _
      _ = nu ψ := euclideanNorm_tauMap hψ
      _ < ε := hnuψ

theorem continuousOn_sigmaMap {p : ℕ} (hp : 0 < p) :
    ContinuousOn sigmaMap (closedBallEuclid p) := by
  intro x _
  by_cases hx : x = fun _ => 0
  · subst hx; exact (continuousAt_sigmaMap_zero hp).continuousWithinAt
  · exact (continuousAt_sigmaMap_of_ne_zero hx).continuousWithinAt

theorem continuousOn_tauMap {p : ℕ} :
    ContinuousOn tauMap (closure {ψ : Fin p → ℝ | nu ψ < 1}) := by
  intro ψ _
  by_cases hψ : ψ = fun _ => 0
  · subst hψ; exact continuousAt_tauMap_zero.continuousWithinAt
  · exact (continuousAt_tauMap_of_ne_zero hψ).continuousWithinAt

theorem sigmaMap_mapsTo {p : ℕ} :
    Set.MapsTo sigmaMap (closedBallEuclid p) (closure {ψ : Fin p → ℝ | nu ψ < 1}) := by
  intro x hx
  rw [closure_crystal]
  simp only [Set.mem_setOf_eq]
  unfold closedBallEuclid at hx
  simp only [Set.mem_setOf_eq] at hx
  by_cases hx0 : x = fun _ => 0
  · rw [hx0, sigmaMap_zero, (nu_eq_zero_iff _).mpr rfl]; norm_num
  · rw [nu_sigmaMap hx0]; exact hx

theorem tauMap_mapsTo {p : ℕ} :
    Set.MapsTo tauMap (closure {ψ : Fin p → ℝ | nu ψ < 1}) (closedBallEuclid p) := by
  intro ψ hψ
  rw [closure_crystal] at hψ
  simp only [Set.mem_setOf_eq] at hψ
  unfold closedBallEuclid
  simp only [Set.mem_setOf_eq]
  by_cases hψ0 : ψ = fun _ => 0
  · rw [hψ0, tauMap_zero, (euclideanNorm_eq_zero_iff _).mpr rfl]; norm_num
  · rw [euclideanNorm_tauMap hψ0]; exact hψ

/-- **`σ` は`Fin p → ℝ`全体で連続**(`O_p`を除いた連続性と`O_p`での連続性から)。 -/
theorem continuous_sigmaMap {p : ℕ} (hp : 0 < p) : Continuous (sigmaMap : (Fin p → ℝ) → _) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = fun _ => 0
  · subst hx; exact continuousAt_sigmaMap_zero hp
  · exact continuousAt_sigmaMap_of_ne_zero hx

/-- **`τ` は`Fin p → ℝ`全体で連続**。 -/
theorem continuous_tauMap {p : ℕ} : Continuous (tauMap : (Fin p → ℝ) → _) := by
  rw [continuous_iff_continuousAt]
  intro ψ
  by_cases hψ : ψ = fun _ => 0
  · subst hψ; exact continuousAt_tauMap_zero
  · exact continuousAt_tauMap_of_ne_zero hψ

/-- **`lem:crystal-ball`**: `σ : closed_B^p ≃ₜ closure C_p`(閉 Euclid 球とクロス
ポリトープの閉包の明示的な同相)。 -/
noncomputable def SigmaHomeo {p : ℕ} (hp : 0 < p) :
    closedBallEuclid p ≃ₜ closure {ψ : Fin p → ℝ | nu ψ < 1} where
  toFun x := ⟨sigmaMap x.1, sigmaMap_mapsTo x.2⟩
  invFun y := ⟨tauMap y.1, tauMap_mapsTo y.2⟩
  left_inv x := Subtype.ext (tauMap_sigmaMap x.1)
  right_inv y := Subtype.ext (sigmaMap_tauMap y.1)
  continuous_toFun := Continuous.subtype_mk ((continuous_sigmaMap hp).comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (continuous_tauMap.comp continuous_subtype_val) _

/-- **Proposition (`closure St(p)` is a closed ball)**: `closure St(p) ≃ₜ closed_B^p`。
`Ξ`(`prop:xi-homeo`)と`σ⁻¹`(`lem:crystal-ball`)の合成。 -/
noncomputable def closureStHomeoClosedBall {p : ℕ} (hp : 0 < p) :
    closure {φ : Fin p → ℝ | IsStationary φ} ≃ₜ closedBallEuclid p :=
  (XiHomeo hp).trans (SigmaHomeo hp).symm

/-- **`prop:open-ball`(本命)**: `St(p) ≃ₜ B^p`(定常領域は開 Euclid 球に同相)。
`τ∘Ξ`(`Ξ`は`prop:xi-homeo`、`τ=σ⁻¹`は`lem:crystal-ball`)を`{μ<1}`↔`{‖·‖₂<1}`
に直接制限する。`Ξ`・`τ`がともに`Fin p → ℝ`全体で連続(`continuous_Xi`・
`continuous_tauMap`)なので、`closure`上の`ContinuousOn`を経由するより単純。 -/
noncomputable def stHomeoOpenBall {p : ℕ} (hp : 0 < p) :
    {φ : Fin p → ℝ | IsStationary φ} ≃ₜ {x : Fin p → ℝ | euclideanNorm x < 1} where
  toFun x := ⟨tauMap (Xi hp x.1), by
    have hx2 : mu hp x.1 < 1 := (isStationary_iff_mu_lt_one hp x.1).mp x.2
    simp only [Set.mem_setOf_eq]
    by_cases hzero : Xi hp x.1 = fun _ => 0
    · rw [hzero, tauMap_zero, (euclideanNorm_eq_zero_iff _).mpr rfl]; norm_num
    · rw [euclideanNorm_tauMap hzero, nu_Xi_eq_mu]; exact hx2⟩
  invFun y := ⟨XiInv hp (sigmaMap y.1), by
    have hy2 : euclideanNorm y.1 < 1 := y.2
    simp only [Set.mem_setOf_eq]
    rw [isStationary_iff_mu_lt_one hp]
    by_cases hzero : y.1 = fun _ => 0
    · rw [hzero, sigmaMap_zero, XiInv_zero, (mu_eq_zero_iff hp _).mpr rfl]
      norm_num
    · rw [mu_XiInv_eq_nu, nu_sigmaMap hzero]
      exact hy2⟩
  left_inv x := by
    apply Subtype.ext
    change XiInv hp (sigmaMap (tauMap (Xi hp x.1))) = x.1
    rw [sigmaMap_tauMap]
    exact XiInv_Xi hp x.1
  right_inv y := by
    apply Subtype.ext
    change tauMap (Xi hp (XiInv hp (sigmaMap y.1))) = y.1
    rw [Xi_XiInv]
    exact tauMap_sigmaMap y.1
  continuous_toFun :=
    Continuous.subtype_mk
      ((continuous_tauMap.comp (continuous_Xi hp)).comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk
      (((continuous_XiInv hp).comp (continuous_sigmaMap hp)).comp continuous_subtype_val) _

/-- `σ(x)=O_p ↔ x=O_p`(`tauMap_sigmaMap`と`tauMap_zero`から、`σ`が大域的単射
なので)。 -/
theorem sigmaMap_eq_zero_iff {p : ℕ} (x : Fin p → ℝ) :
    sigmaMap x = (fun _ => 0) ↔ x = fun _ => 0 := by
  constructor
  · intro h
    have := tauMap_sigmaMap x
    rw [h, tauMap_zero] at this
    exact this.symm
  · intro h
    rw [h, sigmaMap_zero]

/-- **`∂St(p) = {μ=1}` の境界(`prop:ball`の球面部分)**: `Ξ`(`prop:xi-homeo`)と
`τ`(`lem:crystal-ball`)を`μ=1`↔`‖·‖₂=1`の断面に制限した同相写像。`stHomeoOpenBall`
と全く同じ式(`τ∘Ξ`とその逆`Ξ⁻¹∘σ`)を使い、値がちょうど`1`になる場合として構成する。 -/
noncomputable def frontierStMuEqOneHomeoSphere {p : ℕ} (hp : 0 < p) :
    {φ : Fin p → ℝ | mu hp φ = 1} ≃ₜ {x : Fin p → ℝ | euclideanNorm x = 1} where
  toFun x := ⟨tauMap (Xi hp x.1), by
    have hx2 : mu hp x.1 = 1 := x.2
    have hx1 : x.1 ≠ fun _ => 0 := by
      intro h
      rw [h, (mu_eq_zero_iff hp _).mpr rfl] at hx2
      norm_num at hx2
    have hXine : Xi hp x.1 ≠ fun _ => 0 := fun h => hx1 ((Xi_eq_zero_iff hp x.1).mp h)
    simp only [Set.mem_setOf_eq]
    rw [euclideanNorm_tauMap hXine, nu_Xi_eq_mu]
    exact hx2⟩
  invFun y := ⟨XiInv hp (sigmaMap y.1), by
    have hy2 : euclideanNorm y.1 = 1 := y.2
    have hy1 : y.1 ≠ fun _ => 0 := by
      intro h
      rw [h, (euclideanNorm_eq_zero_iff _).mpr rfl] at hy2
      norm_num at hy2
    simp only [Set.mem_setOf_eq]
    rw [mu_XiInv_eq_nu, nu_sigmaMap hy1]
    exact hy2⟩
  left_inv x := by
    apply Subtype.ext
    change XiInv hp (sigmaMap (tauMap (Xi hp x.1))) = x.1
    rw [sigmaMap_tauMap]
    exact XiInv_Xi hp x.1
  right_inv y := by
    apply Subtype.ext
    change tauMap (Xi hp (XiInv hp (sigmaMap y.1))) = y.1
    rw [Xi_XiInv]
    exact tauMap_sigmaMap y.1
  continuous_toFun :=
    Continuous.subtype_mk
      ((continuous_tauMap.comp (continuous_Xi hp)).comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk
      (((continuous_XiInv hp).comp (continuous_sigmaMap hp)).comp continuous_subtype_val) _

/-- **`prop:ball`の球面部分**: `∂St(p) ≅ S^{p-1}`(定常領域の境界は単位球面に同相)。
`frontier_isStationary_eq`(`Mu.lean`)で`∂St(p)={μ=1}`に言い換え、
`frontierStMuEqOneHomeoSphere`と合成する。 -/
noncomputable def frontierStHomeoSphere {p : ℕ} (hp : 0 < p) :
    frontier {φ : Fin p → ℝ | IsStationary φ} ≃ₜ {x : Fin p → ℝ | euclideanNorm x = 1} :=
  (Homeomorph.setCongr (frontier_isStationary_eq hp)).trans (frontierStMuEqOneHomeoSphere hp)

end StTopology
