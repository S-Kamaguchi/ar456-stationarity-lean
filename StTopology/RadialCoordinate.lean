import Mathlib
import StTopology.Mu
import StTopology.Nu

set_option linter.style.header false

/-!
# 共有動径座標 `r(φ)` (`lem:r-welldef`)

論文 `5_kanren.tex`, Section 3.9 の `lem:r-welldef`。`φ ≠ O_p` のとき、
`ν(γ_t φ) = μ(φ)` を満たす `t > 0` がただ一つ存在する。これが `Ξ` の定義
(`prop:xi-homeo`)の核になる共有動径座標 `r(φ)`。

存在は `t ↦ ν(γ_t φ)` が `[0,∞)` 上連続(`continuous_nu_gammaT`)・`0` から出発
(`ν(γ_0φ)=0`)・大きい `t` でいくらでも大きくなることから IVT(`intermediate_value_Icc`)
で、一意性は狭義単調性(`nu_gammaT_strictMonoOn`)から従う
(`OpenBall_formalization_plan.md` 5節)。連続性は追って別途扱う。
-/

open Finset

namespace StTopology

/-- **`lem:r-welldef`(存在・一意性)**: `φ≠O_p` のとき、`ν(γ_t φ)=μ(φ)` を満たす
`t>0` がただ一つ存在する。 -/
theorem exists_unique_r {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : φ ≠ fun _ => 0) :
    ∃! t : ℝ, 0 < t ∧ nu (gammaT t φ) = mu hp φ := by
  have hmupos : 0 < mu hp φ := by
    rcases (mu_nonneg hp φ).eq_or_lt with h | h
    · exact absurd ((mu_eq_zero_iff hp φ).mp h.symm) hφ
    · exact h
  have hnupos : nu φ ≠ 0 := fun h => hφ ((nu_eq_zero_iff φ).mp h)
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin p, φ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ (funext hcon)
  -- 十分大きい T を明示的に取り、[0,T] 上で IVT を使う
  set T : ℝ := max 1 (mu hp φ / |φ i₀|) with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_left _ _
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hTbig : mu hp φ / |φ i₀| ≤ T := le_max_right _ _
  have hcont : ContinuousOn (fun t : ℝ => nu (gammaT t φ)) (Set.Icc 0 T) :=
    (continuous_nu_gammaT φ).continuousOn
  have hf0 : nu (gammaT (0 : ℝ) φ) = 0 := by
    rw [gammaT_zero]
    exact (nu_eq_zero_iff _).mpr rfl
  have hfT : mu hp φ ≤ nu (gammaT T φ) := by
    rw [nu_gammaT φ hT0]
    have hterm : T ^ ((i₀ : ℕ) + 1) * |φ i₀| ≤ ∑ i : Fin p, T ^ ((i : ℕ) + 1) * |φ i| :=
      Finset.single_le_sum (f := fun i : Fin p => T ^ ((i : ℕ) + 1) * |φ i|)
        (fun i _ => mul_nonneg (pow_nonneg hT0 _) (abs_nonneg _)) (Finset.mem_univ i₀)
    have hTge : T ≤ T ^ ((i₀ : ℕ) + 1) := by
      calc T = T ^ 1 := (pow_one T).symm
        _ ≤ T ^ ((i₀ : ℕ) + 1) := pow_le_pow_right₀ hT1 (by omega)
    have habspos : 0 < |φ i₀| := abs_pos.mpr hi₀
    have h1 : mu hp φ / |φ i₀| ≤ T ^ ((i₀ : ℕ) + 1) := hTbig.trans hTge
    rw [div_le_iff₀ habspos] at h1
    linarith [hterm]
  have hmem : mu hp φ ∈ Set.Icc (nu (gammaT (0 : ℝ) φ)) (nu (gammaT T φ)) := by
    rw [hf0]
    exact ⟨hmupos.le, hfT⟩
  obtain ⟨r₀, hr₀mem, hr₀eq⟩ := intermediate_value_Icc hT0 hcont hmem
  dsimp only at hr₀eq
  have hr₀pos : 0 < r₀ := by
    rcases hr₀mem.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hf0] at hr₀eq
      linarith
    · exact h
  refine ⟨r₀, ⟨hr₀pos, hr₀eq⟩, ?_⟩
  rintro t₁ ⟨ht₁pos, ht₁eq⟩
  exact (nu_gammaT_strictMonoOn hnupos).injOn (Set.mem_Ici.mpr ht₁pos.le)
    (Set.mem_Ici.mpr hr₀pos.le) (ht₁eq.trans hr₀eq.symm)

/-- **共有動径座標 `r(φ)`**: `φ≠O_p` のとき `ν(γ_{r(φ)}φ) = μ(φ)` を満たす一意な
`r(φ) > 0`(`exists_unique_r` からの `Classical.choose`)。 -/
noncomputable def r {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : φ ≠ fun _ => 0) : ℝ :=
  (exists_unique_r hp hφ).choose

theorem r_pos {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : φ ≠ fun _ => 0) : 0 < r hp hφ :=
  (exists_unique_r hp hφ).choose_spec.1.1

theorem r_eq {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : φ ≠ fun _ => 0) :
    nu (gammaT (r hp hφ) φ) = mu hp φ :=
  (exists_unique_r hp hφ).choose_spec.1.2

theorem r_unique {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : φ ≠ fun _ => 0)
    {t : ℝ} (ht0 : 0 < t) (ht : nu (gammaT t φ) = mu hp φ) : t = r hp hφ :=
  (exists_unique_r hp hφ).choose_spec.2 t ⟨ht0, ht⟩

/-- **`lem:r-welldef`(連続性)**: `φ₀≠O_p` を固定すると、`r` は `φ₀` で連続
(定義域 `{φ | φ≠O_p}` 上、`ε`-`δ`の形で)。論文の `H(t,φ):=ν(γ_tφ)-μ(φ)` を使う
近傍論法をそのまま移植する: `a:=r(φ₀)-ε'`, `b:=r(φ₀)+ε'`(`ε'`は`ε`と`r(φ₀)/2`の
小さい方)を固定すると狭義単調性から`ν(γ_aφ₀)<μ(φ₀)<ν(γ_bφ₀)`。この2つの不等式は
`φ↦ν(γ_aφ)`・`φ↦ν(γ_bφ)`・`μ`の連続性により`φ₀`のある近傍で保たれ、その近傍では
(弱)単調性の対偶から`a<r(φ)<b`が従う。 -/
theorem r_continuousAt {p : ℕ} (hp : 0 < p) {φ₀ : Fin p → ℝ} (hφ₀ : φ₀ ≠ fun _ => 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ φ, ∀ hφ : φ ≠ fun _ => 0, dist φ φ₀ < δ →
      dist (r hp hφ) (r hp hφ₀) < ε := by
  intro ε hε
  have hr₀pos : 0 < r hp hφ₀ := r_pos hp hφ₀
  set ε' : ℝ := min ε (r hp hφ₀ / 2) with hε'def
  have hε'pos : 0 < ε' := lt_min hε (by linarith)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'ler0 : ε' ≤ r hp hφ₀ / 2 := min_le_right _ _
  set a : ℝ := r hp hφ₀ - ε' with hadef
  set b : ℝ := r hp hφ₀ + ε' with hbdef
  have ha0 : 0 ≤ a := by rw [hadef]; linarith
  have hb0 : 0 ≤ b := by rw [hbdef]; linarith
  have hab : a < r hp hφ₀ := by rw [hadef]; linarith
  have hbr₀ : r hp hφ₀ < b := by rw [hbdef]; linarith
  have hnu₀ : nu φ₀ ≠ 0 := fun h => hφ₀ ((nu_eq_zero_iff φ₀).mp h)
  have hcont_a : Continuous (fun φ : Fin p → ℝ => nu (gammaT a φ)) :=
    continuous_nu.comp (continuous_gammaT_apply a)
  have hcont_b : Continuous (fun φ : Fin p → ℝ => nu (gammaT b φ)) :=
    continuous_nu.comp (continuous_gammaT_apply b)
  -- `φ₀` における符号: `ν(γ_aφ₀) < μ(φ₀) < ν(γ_bφ₀)`
  have hSa0 : nu (gammaT a φ₀) < mu hp φ₀ := by
    have h := (nu_gammaT_strictMonoOn hnu₀) (Set.mem_Ici.mpr ha0)
      (Set.mem_Ici.mpr hr₀pos.le) hab
    dsimp only at h
    rwa [r_eq hp hφ₀] at h
  have hSb0 : mu hp φ₀ < nu (gammaT b φ₀) := by
    have h := (nu_gammaT_strictMonoOn hnu₀) (Set.mem_Ici.mpr hr₀pos.le)
      (Set.mem_Ici.mpr hb0) hbr₀
    dsimp only at h
    rwa [r_eq hp hφ₀] at h
  -- 上の2つの不等式は`φ₀`の近傍で保たれる
  obtain ⟨δa, hδapos, hδa⟩ := Metric.isOpen_iff.mp
    (isOpen_lt hcont_a (continuous_mu hp)) φ₀ hSa0
  obtain ⟨δb, hδbpos, hδb⟩ := Metric.isOpen_iff.mp
    (isOpen_lt (continuous_mu hp) hcont_b) φ₀ hSb0
  refine ⟨min δa δb, lt_min hδapos hδbpos, ?_⟩
  intro φ hφ hφdist
  have hφa : φ ∈ Metric.ball φ₀ δa := Metric.mem_ball.mpr (hφdist.trans_le (min_le_left _ _))
  have hφb : φ ∈ Metric.ball φ₀ δb := Metric.mem_ball.mpr (hφdist.trans_le (min_le_right _ _))
  have hSaφ : nu (gammaT a φ) < mu hp φ := hδa hφa
  have hSbφ : mu hp φ < nu (gammaT b φ) := hδb hφb
  have hrφpos : 0 < r hp hφ := r_pos hp hφ
  -- (弱)単調性の対偶から `a < r(φ) < b`
  have hlt_a : a < r hp hφ := by
    by_contra hcon
    push Not at hcon
    have hmono := (nu_gammaT_monotoneOn φ) (Set.mem_Ici.mpr hrφpos.le)
      (Set.mem_Ici.mpr ha0) hcon
    dsimp only at hmono
    rw [r_eq hp hφ] at hmono
    linarith
  have hlt_b : r hp hφ < b := by
    by_contra hcon
    push Not at hcon
    have hmono := (nu_gammaT_monotoneOn φ) (Set.mem_Ici.mpr hb0)
      (Set.mem_Ici.mpr hrφpos.le) hcon
    dsimp only at hmono
    rw [r_eq hp hφ] at hmono
    linarith
  rw [Real.dist_eq, abs_lt]
  refine ⟨by linarith, by linarith⟩

end StTopology
