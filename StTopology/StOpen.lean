import Mathlib
import StTopology.StationarityRegions
import StTopology.CauchyBound

set_option linter.style.header false

/-!
# St(p) は開集合である

`MaximalComponentPrinciple.lean` の Proposition を実際に適用するために必要な
仮定 `hSt_open : IsOpen St` を、一般の `p` について証明する。

## 証明の方針 (根の連続性を避ける)

「根が係数に連続的に依存する」という抽象論を経由せず、コンパクト性と
明示的な摂動評価だけで示す。`φ₀` を定常な係数とし、

* `S₀ := ∑|φ₀ᵢ|`, `R := 2 + S₀` (したがって `R ≥ 2 > 1`)
* `K := {z | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ R}` (コンパクトな閉環状領域)

とおく。`φ₀` は定常なので、`K` 上に `F φ₀` の零点は存在しない。`K` はコンパクトで
`z ↦ ‖F φ₀ z‖` は連続だから、最大値・最小値の定理 (`IsCompact.exists_isMinOn`) より
`K` 上の最小値 `m > 0` が存在する。

一方、係数の摂動に対しては明示的な評価

  `‖F φ z - F ψ z‖ ≤ (∑|φᵢ-ψᵢ|) · R^(p-1)`   (`‖z‖ ≤ R`, `R ≥ 1`)

が成り立つ (`normF_sub_le`)。よって `∑|φᵢ-φ₀ᵢ|` が `m/(2R^(p-1))` 未満かつ `1` 未満なら:

* `CauchyBound.root_norm_le` より `φ` の任意の根は `‖α‖ ≤ 1+∑|φᵢ| ≤ R`;
* もし `1 ≤ ‖α‖` なら `α ∈ K` なので `‖F φ₀ α‖ ≥ m`。しかし `F φ α = 0` と
  上の摂動評価から `‖F φ₀ α‖ < m/2`、矛盾。

したがってすべての根が `‖α‖ < 1` を満たし、`φ` も定常である。
一様連続性の抽象論は使わず、評価はすべて具体的な三角不等式で済む。
-/

open Finset Metric

namespace StTopology

/-- 逆特性方程式の左辺 `F φ z = z^p - (φ₁z^{p-1} + ⋯ + φ_p)`。
`IsStationary φ` は「`F φ z = 0` なるすべての `z` が `‖z‖<1`」と言い換えられる。 -/
noncomputable def F {p : ℕ} (φ : Fin p → ℝ) (z : ℂ) : ℂ :=
  z ^ p - ∑ i : Fin p, (φ i : ℂ) * z ^ (p - 1 - (i : ℕ))

theorem F_eq_zero_iff {p : ℕ} (φ : Fin p → ℝ) (z : ℂ) :
    F φ z = 0 ↔ z ^ p = ∑ i : Fin p, (φ i : ℂ) * z ^ (p - 1 - (i : ℕ)) := by
  unfold F
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

theorem continuous_F {p : ℕ} (φ : Fin p → ℝ) : Continuous (F φ) := by
  unfold F
  fun_prop

/-- 係数の摂動に対する明示的な評価。`‖z‖ ≤ R` かつ `1 ≤ R` のとき、
`F φ z` と `F ψ z` の差は係数の差の総和と `R^(p-1)` で押さえられる。 -/
theorem normF_sub_le {p : ℕ} (φ ψ : Fin p → ℝ) (z : ℂ) (R : ℝ)
    (hR1 : 1 ≤ R) (hzR : ‖z‖ ≤ R) :
    ‖F φ z - F ψ z‖ ≤ (∑ i, |φ i - ψ i|) * R ^ (p - 1) := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hdiff : F φ z - F ψ z
      = ∑ i : Fin p, ((ψ i : ℂ) - (φ i : ℂ)) * z ^ (p - 1 - (i : ℕ)) := by
    unfold F
    have hsplit : ∑ i : Fin p, ((ψ i : ℂ) - (φ i : ℂ)) * z ^ (p - 1 - (i : ℕ))
        = (∑ i : Fin p, (ψ i : ℂ) * z ^ (p - 1 - (i : ℕ)))
          - ∑ i : Fin p, (φ i : ℂ) * z ^ (p - 1 - (i : ℕ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsplit]
    ring
  rw [hdiff]
  calc ‖∑ i : Fin p, ((ψ i : ℂ) - (φ i : ℂ)) * z ^ (p - 1 - (i : ℕ))‖
      ≤ ∑ i : Fin p, ‖((ψ i : ℂ) - (φ i : ℂ)) * z ^ (p - 1 - (i : ℕ))‖ := norm_sum_le _ _
    _ = ∑ i : Fin p, |φ i - ψ i| * ‖z‖ ^ (p - 1 - (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, norm_pow]
        congr 1
        rw [show ((ψ i : ℂ) - (φ i : ℂ)) = ((ψ i - φ i : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ ∑ i : Fin p, |φ i - ψ i| * R ^ (p - 1) := by
        apply Finset.sum_le_sum
        intro i _
        have h1 : ‖z‖ ^ (p - 1 - (i : ℕ)) ≤ R ^ (p - 1) := by
          calc ‖z‖ ^ (p - 1 - (i : ℕ)) ≤ R ^ (p - 1 - (i : ℕ)) :=
                pow_le_pow_left₀ hz0 hzR _
            _ ≤ R ^ (p - 1) := pow_le_pow_right₀ hR1 (by omega)
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (∑ i, |φ i - ψ i|) * R ^ (p - 1) := by rw [Finset.sum_mul]

/-- 閉環状領域 `{z | 1 ≤ ‖z‖ ≤ R}` はコンパクト。 -/
theorem isCompact_annulus (R : ℝ) :
    IsCompact {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  have hset : {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ R}
      = Metric.closedBall (0 : ℂ) R ∩ {z : ℂ | 1 ≤ ‖z‖} := by
    ext z
    simp [Metric.mem_closedBall, and_comm]
  rw [hset]
  exact (isCompact_closedBall (0 : ℂ) R).inter_right
    (isClosed_le continuous_const continuous_norm)

/-- **St(p) は開集合**。`MaximalComponentPrinciple` の仮定 `hSt_open` にあたる。 -/
theorem isOpen_isStationary {p : ℕ} (hp : 0 < p) :
    IsOpen {φ : Fin p → ℝ | IsStationary φ} := by
  rw [Metric.isOpen_iff]
  intro φ₀ hφ₀
  simp only [Set.mem_setOf_eq] at hφ₀
  set S₀ : ℝ := ∑ i, |φ₀ i| with hS₀
  have hS₀nonneg : 0 ≤ S₀ := Finset.sum_nonneg fun i _ => abs_nonneg _
  set R : ℝ := 2 + S₀ with hRdef
  have hR1 : (1 : ℝ) ≤ R := by simp only [hRdef]; linarith
  have hRpos : (0 : ℝ) < R := by linarith
  have hRpow : (0 : ℝ) < R ^ (p - 1) := pow_pos hRpos _
  -- K 上に F φ₀ の零点はない
  set K : Set ℂ := {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ R} with hK
  have hKcompact : IsCompact K := isCompact_annulus R
  have hKne : K.Nonempty := ⟨1, by simp [hK]; linarith⟩
  have hcont : ContinuousOn (fun z => ‖F φ₀ z‖) K :=
    (continuous_norm.comp (continuous_F φ₀)).continuousOn
  obtain ⟨z₀, hz₀K, hz₀min⟩ := hKcompact.exists_isMinOn hKne hcont
  set m : ℝ := ‖F φ₀ z₀‖ with hm
  have hmpos : 0 < m := by
    rw [hm, norm_pos_iff]
    intro hcontra
    have hroot := (F_eq_zero_iff φ₀ z₀).mp hcontra
    have := hφ₀ z₀ hroot
    exact absurd hz₀K.1 (not_le.mpr this)
  -- 近さの閾値
  set δ : ℝ := min 1 (m / (2 * R ^ (p - 1))) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min one_pos (div_pos hmpos (by linarith))
  refine ⟨δ / (p + 1), div_pos hδpos (by positivity), ?_⟩
  intro φ hφdist
  simp only [Set.mem_setOf_eq]
  -- 係数の差の総和を押さえる
  have hsum_lt : ∑ i, |φ i - φ₀ i| < δ := by
    have hbound : ∀ i : Fin p, |φ i - φ₀ i| ≤ dist φ φ₀ := by
      intro i
      have := dist_le_pi_dist φ φ₀ i
      rwa [Real.dist_eq] at this
    have hcard : ∑ i, |φ i - φ₀ i| ≤ (p : ℝ) * dist φ φ₀ := by
      calc ∑ i, |φ i - φ₀ i| ≤ ∑ _i : Fin p, dist φ φ₀ :=
            Finset.sum_le_sum fun i _ => hbound i
        _ = (p : ℝ) * dist φ φ₀ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hd : dist φ φ₀ < δ / (p + 1) := by
      rw [Metric.mem_ball] at hφdist
      exact hφdist
    have hppos : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    calc ∑ i, |φ i - φ₀ i| ≤ (p : ℝ) * dist φ φ₀ := hcard
      _ ≤ (p : ℝ) * (δ / (p + 1)) := by
          apply mul_le_mul_of_nonneg_left hd.le hppos
      _ < δ := by
          rw [mul_div_assoc'] at *
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [hδpos, hppos]
  have hsum_le_one : ∑ i, |φ i - φ₀ i| ≤ 1 := by
    have : δ ≤ 1 := min_le_left _ _
    linarith
  have hsum_lt_half : (∑ i, |φ i - φ₀ i|) * R ^ (p - 1) < m / 2 := by
    have hδ2 : δ ≤ m / (2 * R ^ (p - 1)) := min_le_right _ _
    have h1 : (∑ i, |φ i - φ₀ i|) * R ^ (p - 1) < δ * R ^ (p - 1) :=
      mul_lt_mul_of_pos_right hsum_lt hRpow
    have h2 : δ * R ^ (p - 1) ≤ (m / (2 * R ^ (p - 1))) * R ^ (p - 1) :=
      mul_le_mul_of_nonneg_right hδ2 hRpow.le
    have h3 : (m / (2 * R ^ (p - 1))) * R ^ (p - 1) = m / 2 := by
      field_simp
    linarith
  -- 以上より φ の根はすべて単位円の内側
  intro α hα
  have hFα : F φ α = 0 := (F_eq_zero_iff φ α).mpr hα
  by_contra hcontra
  rw [not_lt] at hcontra
  -- α ∈ K を示す
  have hαR : ‖α‖ ≤ R := by
    have hcauchy := root_norm_le hp φ α hα
    have hsplit : ∑ i, |φ i| ≤ S₀ + ∑ i, |φ i - φ₀ i| := by
      rw [hS₀, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      have := abs_sub_abs_le_abs_sub (φ i) (φ₀ i)
      linarith
    rw [hRdef]
    linarith
  have hαK : α ∈ K := ⟨hcontra, hαR⟩
  have hmin : m ≤ ‖F φ₀ α‖ := hz₀min hαK
  have hpert : ‖F φ₀ α‖ ≤ (∑ i, |φ₀ i - φ i|) * R ^ (p - 1) := by
    have := normF_sub_le φ₀ φ α R hR1 hαR
    rwa [hFα, sub_zero] at this
  have hsymm : ∑ i, |φ₀ i - φ i| = ∑ i, |φ i - φ₀ i| := by
    apply Finset.sum_congr rfl
    intro i _
    exact abs_sub_comm _ _
  rw [hsymm] at hpert
  linarith

end StTopology
