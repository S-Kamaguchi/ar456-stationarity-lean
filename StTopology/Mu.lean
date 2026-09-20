import Mathlib
import StTopology.StationarityRegions
import StTopology.VietaBound
import StTopology.RootPerturbation
import StTopology.StConnected

set_option linter.style.header false

/-!
# `μ`(最大根ノルム)の定義と基本性質

論文 `5_kanren.tex`, Section 3.9 の `μ(φ) := max{‖z‖ : \tilde φ(z) = 0}`。
`St(p) = {φ | μ(φ) < 1}` という言い換えが、`prop:open-ball` に向けた
動径座標構成全体の出発点になる。
-/

open Finset Polynomial

namespace StTopology

theorem charPoly_roots_card {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    (charPoly φ).roots.card = p := by
  have hsplits : (charPoly φ).Splits := IsAlgClosed.splits _
  rw [hsplits.natDegree_eq_card_roots.symm, charPoly_natDegree hp φ]

theorem charPoly_roots_toFinset_nonempty {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    ((charPoly φ).roots.toFinset).Nonempty := by
  rw [Multiset.toFinset_nonempty]
  intro hcontra
  have hcard := charPoly_roots_card hp φ
  rw [hcontra] at hcard
  simp only [Multiset.card_zero] at hcard
  omega

/-- `μ(φ) := max{‖z‖ : z は逆特性方程式の根}`。`(charPoly φ).roots` の重複を
`toFinset` で潰した上で `sup'` を取る。 -/
noncomputable def mu {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) : ℝ :=
  ((charPoly φ).roots.toFinset).sup' (charPoly_roots_toFinset_nonempty hp φ) (‖·‖)

theorem mu_nonneg {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) : 0 ≤ mu hp φ := by
  unfold mu
  obtain ⟨x, hx⟩ := charPoly_roots_toFinset_nonempty hp φ
  exact (norm_nonneg x).trans (Finset.le_sup' (‖·‖) hx)

/-- **`μ` と `IsStationary` の橋渡し**: `IsStationary φ ↔ μ(φ) < 1`。 -/
theorem isStationary_iff_mu_lt_one {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    IsStationary φ ↔ mu hp φ < 1 := by
  unfold mu IsStationary
  rw [Finset.sup'_lt_iff]
  constructor
  · intro hφ z hz
    rw [Multiset.mem_toFinset] at hz
    exact hφ z ((mem_roots_charPoly_iff hp φ z).mp hz)
  · intro hφ z hz
    exact hφ z (Multiset.mem_toFinset.mpr ((mem_roots_charPoly_iff hp φ z).mpr hz))

/-- `∑ᵢ C(φᵢ) X^{p-1-i}` の `X^{p-1-j}` 係数は `φ j` (Vieta と同じ計算、
`VietaBound.lean` の `abs_last_coeff_lt_one` の `hRcoeff` を一般の添字 `j` に
拡張したもの)。 -/
theorem charPoly_sub_coeff {p : ℕ} (φ : Fin p → ℝ) (j : Fin p) :
    (∑ i : Fin p, Polynomial.C (φ i : ℂ) * Polynomial.X ^ (p - 1 - (i : ℕ))).coeff
        (p - 1 - (j : ℕ)) = (φ j : ℂ) := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl]
    simp
  · intro i _ hne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have hne0 : ¬ (p - 1 - (j : ℕ) = p - 1 - (i : ℕ)) := by
      intro heqc
      apply hne
      apply Fin.ext
      have hip : (i : ℕ) < p := i.2
      have hjp : (j : ℕ) < p := j.2
      omega
    simp [hne0]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `charPoly φ = X^p` ならば `φ` はすべての係数が `0`。 -/
theorem eq_zero_of_charPoly_eq_X_pow {p : ℕ} (φ : Fin p → ℝ)
    (h : charPoly φ = Polynomial.X ^ p) : φ = fun _ => 0 := by
  unfold charPoly at h
  have hsub : (∑ i : Fin p, Polynomial.C (φ i : ℂ) * Polynomial.X ^ (p - 1 - (i : ℕ))) = 0 :=
    sub_eq_self.mp h
  funext j
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff (p - 1 - (j : ℕ))) hsub
  simp only [Polynomial.coeff_zero] at hcoeff
  rw [charPoly_sub_coeff φ j] at hcoeff
  exact_mod_cast hcoeff

/-- `μ(φ) = 0` ならば `charPoly φ` のすべての根 (重複度込み) は `0`。 -/
theorem roots_eq_replicate_zero_of_mu_eq_zero {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ)
    (hmu : mu hp φ = 0) : (charPoly φ).roots = Multiset.replicate p 0 := by
  rw [Multiset.eq_replicate]
  refine ⟨charPoly_roots_card hp φ, ?_⟩
  intro b hb
  have hbmem : b ∈ (charPoly φ).roots.toFinset := Multiset.mem_toFinset.mpr hb
  have hle : ‖b‖ ≤ mu hp φ := by
    unfold mu
    exact Finset.le_sup' (‖·‖) hbmem
  rw [hmu] at hle
  exact norm_le_zero_iff.mp hle

theorem charPoly_eq_X_pow_of_mu_eq_zero {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ)
    (hmu : mu hp φ = 0) : charPoly φ = Polynomial.X ^ p := by
  have hfactored : ((charPoly φ).roots.map (fun a => Polynomial.X - Polynomial.C a)).prod
      = charPoly φ :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charPoly_monic hp φ)
      (by rw [charPoly_roots_card hp φ, charPoly_natDegree hp φ])
  rw [roots_eq_replicate_zero_of_mu_eq_zero hp φ hmu, Multiset.map_replicate,
    Multiset.prod_replicate, Polynomial.C_0, sub_zero] at hfactored
  exact hfactored.symm

/-- **`μ` の `0`-点特徴づけ**: `μ(φ) = 0 ↔ φ = O_p`。 -/
theorem mu_eq_zero_iff {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    mu hp φ = 0 ↔ φ = fun _ => 0 := by
  constructor
  · intro hmu
    exact eq_zero_of_charPoly_eq_X_pow φ (charPoly_eq_X_pow_of_mu_eq_zero hp φ hmu)
  · intro hφ
    subst hφ
    apply le_antisymm _ (mu_nonneg hp _)
    unfold mu
    rw [Finset.sup'_le_iff]
    intro z hz
    rw [Multiset.mem_toFinset] at hz
    have heq := (mem_roots_charPoly_iff hp (fun _ => (0 : ℝ)) z).mp hz
    simp only [Complex.ofReal_zero, zero_mul, Finset.sum_const_zero] at heq
    have hz0 : z = 0 := by
      have hpne : p ≠ 0 := hp.ne'
      exact (pow_eq_zero_iff hpne).mp heq
    simp [hz0]

/-! ### 斉次性: `μ(γ_t φ) = t · μ(φ)` (`t ≥ 0`)

`isStationary_scale` (`StConnected.lean`) の `key` 計算と同じ変数変換 `β ↦ β/t` を
経由する。`Multiset` レベルの根の対応を経由せず、`t≠0` のときの往復2方向を個別に
`root_div_of_root_gammaT` / `root_gammaT_mul_of_root` として取り出し、`Finset.sup'`
の単調性で挟み撃ちにする(`OpenBall_formalization_plan.md` 1.2節の「軽いルート」)。 -/

/-- `t > 0` のとき、`gammaT t φ` の根 `β` に対して `β/t` は `φ` の根
(`isStationary_scale` の `key`/`hα_eq` 計算をそのまま流用)。 -/
theorem root_div_of_root_gammaT {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) {t : ℝ} (ht : 0 < t)
    {β : ℂ} (hβ : β ∈ (charPoly (gammaT t φ)).roots) :
    (β / (t : ℂ)) ∈ (charPoly φ).roots := by
  rw [mem_roots_charPoly_iff hp (gammaT t φ)] at hβ
  rw [mem_roots_charPoly_iff hp φ]
  unfold gammaT at hβ
  push_cast at hβ
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have key : ∀ i : Fin p, (φ i : ℂ) * (β / (t : ℂ)) ^ (p - 1 - (i : ℕ))
      = ((t : ℂ) ^ ((i : ℕ) + 1) * (φ i : ℂ) * β ^ (p - 1 - (i : ℕ))) / (t : ℂ) ^ p := by
    intro i
    have hi : (i : ℕ) < p := i.2
    have hts : (t : ℂ) ^ (p - 1 - (i : ℕ)) * (t : ℂ) ^ ((i : ℕ) + 1) = (t : ℂ) ^ p := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_pow, ← hts]
    field_simp
  rw [div_pow]
  simp_rw [key]
  rw [← Finset.sum_div, ← hβ]

/-- 任意の `t` (符号不問) について、`φ` の根 `α` から `t·α` は `gammaT t φ` の根
(除算を経由しない純代数的な向き、`t=0` でも成り立つ)。 -/
theorem root_gammaT_mul_of_root {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) (t : ℝ)
    {α : ℂ} (hα : α ∈ (charPoly φ).roots) :
    (t : ℂ) * α ∈ (charPoly (gammaT t φ)).roots := by
  rw [mem_roots_charPoly_iff hp φ] at hα
  rw [mem_roots_charPoly_iff hp (gammaT t φ)]
  have key : ∀ i : Fin p, (t : ℂ) ^ p * ((φ i : ℂ) * α ^ (p - 1 - (i : ℕ)))
      = (gammaT t φ i : ℂ) * ((t : ℂ) * α) ^ (p - 1 - (i : ℕ)) := by
    intro i
    have hi : (i : ℕ) < p := i.2
    have hts : (t : ℂ) ^ ((i : ℕ) + 1) * (t : ℂ) ^ (p - 1 - (i : ℕ)) = (t : ℂ) ^ p := by
      rw [← pow_add]
      congr 1
      omega
    unfold gammaT
    push_cast
    rw [mul_pow, ← hts]
    ring
  calc ((t : ℂ) * α) ^ p = (t : ℂ) ^ p * α ^ p := mul_pow (t : ℂ) α p
    _ = (t : ℂ) ^ p * ∑ i : Fin p, (φ i : ℂ) * α ^ (p - 1 - (i : ℕ)) := by rw [hα]
    _ = ∑ i : Fin p, (t : ℂ) ^ p * ((φ i : ℂ) * α ^ (p - 1 - (i : ℕ))) := by
        rw [Finset.mul_sum]
    _ = ∑ i : Fin p, (gammaT t φ i : ℂ) * ((t : ℂ) * α) ^ (p - 1 - (i : ℕ)) :=
        Finset.sum_congr rfl fun i _ => key i

/-- **`μ` の斉次性**: `μ(γ_t φ) = t · μ(φ)` (`t ≥ 0`)。`t=0` は `gammaT_zero` と
`mu_eq_zero_iff` から即座に、`t>0` は `root_div_of_root_gammaT` /
`root_gammaT_mul_of_root` による根の対応を `Finset.sup'` の単調性で挟み撃ちにして示す。 -/
theorem mu_gammaT {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    mu hp (gammaT t φ) = t * mu hp φ := by
  rcases ht.eq_or_lt with ht0 | ht0
  · rw [← ht0, gammaT_zero, (mu_eq_zero_iff hp _).mpr rfl, zero_mul]
  · have htnorm : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht0]
    have ht0' : t ≠ 0 := ht0.ne'
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0'
    apply le_antisymm
    · unfold mu
      rw [Finset.sup'_le_iff]
      intro β hβmem
      rw [Multiset.mem_toFinset] at hβmem
      have hβroot := root_div_of_root_gammaT hp φ ht0 hβmem
      have hβmem' : (β / (t : ℂ)) ∈ (charPoly φ).roots.toFinset :=
        Multiset.mem_toFinset.mpr hβroot
      have hle : ‖β / (t : ℂ)‖ ≤ mu hp φ := by
        unfold mu
        exact Finset.le_sup' (‖·‖) hβmem'
      have heq : β = (t : ℂ) * (β / (t : ℂ)) := by field_simp [htC]
      rw [heq, norm_mul, htnorm]
      exact mul_le_mul_of_nonneg_left hle ht0.le
    · have hstep : mu hp φ ≤ mu hp (gammaT t φ) / t := by
        unfold mu
        rw [Finset.sup'_le_iff]
        intro α hαmem
        rw [Multiset.mem_toFinset] at hαmem
        have hβroot := root_gammaT_mul_of_root hp φ t hαmem
        have hβmem' : (t : ℂ) * α ∈ (charPoly (gammaT t φ)).roots.toFinset :=
          Multiset.mem_toFinset.mpr hβroot
        have hle : ‖(t : ℂ) * α‖ ≤ mu hp (gammaT t φ) := by
          unfold mu
          exact Finset.le_sup' (‖·‖) hβmem'
        rw [norm_mul, htnorm] at hle
        rw [le_div_iff₀ ht0, mul_comm]
        exact hle
      calc t * mu hp φ ≤ t * (mu hp (gammaT t φ) / t) :=
            mul_le_mul_of_nonneg_left hstep ht0.le
        _ = mu hp (gammaT t φ) := by field_simp [ht0']

/-! ### 連続性: `Continuous (mu hp)`

上半連続性(`{μ<c}`が開)は斉次性(`mu_gammaT`)を経由して`isOpen_isStationary`の
引き戻しとして無料で得られ、下半連続性(`{μ>c}`が開)は`exists_root_near`
(`RootPerturbation.lean`)を根の存在に直接適用するだけで得られる
(`OpenBall_formalization_plan.md` 1.3節、「根の連続性を一から作らない」という
発見の核心部分)。最後に`Metric.continuous_iff`の`ε`-`δ`論法で貼り合わせる。 -/

/-- **`μ`の上半連続性**: `{φ | μ(φ) < c}`は開。`c≤0`なら空集合。`c>0`なら
`μ(φ)<c ↔ IsStationary (γ_{1/c} φ)`(斉次性`mu_gammaT`と`isStationary_iff_mu_lt_one`)
という言い換えにより、`isOpen_isStationary`を`γ_{1/c}·`で引き戻すだけで開性が従う。 -/
theorem isOpen_mu_lt {p : ℕ} (hp : 0 < p) (c : ℝ) :
    IsOpen {φ : Fin p → ℝ | mu hp φ < c} := by
  rcases le_or_gt c 0 with hc | hc
  · have hempty : {φ : Fin p → ℝ | mu hp φ < c} = ∅ := by
      ext φ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hc.trans (mu_nonneg hp φ)
    rw [hempty]
    exact isOpen_empty
  · have hset : {φ : Fin p → ℝ | mu hp φ < c}
        = (fun φ : Fin p → ℝ => gammaT (1 / c) φ) ⁻¹' {ψ : Fin p → ℝ | IsStationary ψ} := by
      ext φ
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [isStationary_iff_mu_lt_one hp, mu_gammaT hp φ (by positivity), one_div,
        inv_mul_eq_div, div_lt_one hc]
    rw [hset]
    exact IsOpen.preimage (continuous_gammaT_apply (1 / c)) (isOpen_isStationary hp)

/-- **`μ`の下半連続性**: `{φ | c < μ(φ)}`は開。`c<μ(φ)`なら`φ`にはノルム`μ(φ)`の
根`α₀`が存在し(`Finset.exists_mem_eq_sup'`)、`exists_root_near`を`δ:=μ(φ)-c`で
適用すれば`φ`に近い`ψ`も`α₀`の近くにノルム`>c`の根を持つ。 -/
theorem isOpen_mu_gt {p : ℕ} (hp : 0 < p) (c : ℝ) :
    IsOpen {φ : Fin p → ℝ | c < mu hp φ} := by
  rw [Metric.isOpen_iff]
  intro φ hφ
  simp only [Set.mem_setOf_eq] at hφ
  obtain ⟨α₀, hα₀mem, hα₀eq⟩ :
      ∃ α₀ ∈ (charPoly φ).roots.toFinset, mu hp φ = ‖α₀‖ := by
    unfold mu
    exact Finset.exists_mem_eq_sup' (charPoly_roots_toFinset_nonempty hp φ) (‖·‖)
  rw [Multiset.mem_toFinset] at hα₀mem
  have hα₀root := (mem_roots_charPoly_iff hp φ α₀).mp hα₀mem
  have hδpos : 0 < mu hp φ - c := by linarith
  obtain ⟨ε, hεpos, hε⟩ := exists_root_near hp φ α₀ hα₀root hδpos
  refine ⟨ε, hεpos, ?_⟩
  intro ψ hψball
  rw [Metric.mem_ball] at hψball
  obtain ⟨β, hβeq, hβclose⟩ := hε ψ hψball
  have hβroot : β ∈ (charPoly ψ).roots := (mem_roots_charPoly_iff hp ψ β).mpr hβeq
  have hβmem : β ∈ (charPoly ψ).roots.toFinset := Multiset.mem_toFinset.mpr hβroot
  have hβle : ‖β‖ ≤ mu hp ψ := by
    unfold mu
    exact Finset.le_sup' (‖·‖) hβmem
  have htri : ‖α₀‖ - ‖β‖ ≤ ‖α₀ - β‖ := norm_sub_norm_le α₀ β
  simp only [Set.mem_setOf_eq]
  linarith

/-- **`μ`の連続性**。上半連続性(`isOpen_mu_lt`)・下半連続性(`isOpen_mu_gt`)を
`Metric.continuous_iff`の`ε`-`δ`論法で貼り合わせる。`lem:closure`(`St(p)`の閉包が
`{μ≤1}`になること)の土台。 -/
theorem continuous_mu {p : ℕ} (hp : 0 < p) : Continuous (mu hp) := by
  rw [Metric.continuous_iff]
  intro φ₀ ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.isOpen_iff.mp (isOpen_mu_lt hp (mu hp φ₀ + ε)) φ₀
    (by simp only [Set.mem_setOf_eq]; linarith)
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ := Metric.isOpen_iff.mp (isOpen_mu_gt hp (mu hp φ₀ - ε)) φ₀
    (by simp only [Set.mem_setOf_eq]; linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro a ha
  have ha1 : a ∈ Metric.ball φ₀ δ₁ := Metric.mem_ball.mpr (ha.trans_le (min_le_left _ _))
  have ha2 : a ∈ Metric.ball φ₀ δ₂ := Metric.mem_ball.mpr (ha.trans_le (min_le_right _ _))
  have hlt : mu hp a < mu hp φ₀ + ε := hδ₁sub ha1
  have hgt : mu hp φ₀ - ε < mu hp a := hδ₂sub ha2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### `lem:closure`: `closure St(p) = {μ≤1}`

`μ`の連続性(`continuous_mu`)があれば機械的。`⊆`は`{μ≤1}`が閉かつ`St(p)`を含むことから
`closure_minimal`で即座に。`⊇`は`μ(φ)≤1`のとき`γ_t φ`(`0≤t<1`)がすべて`St(p)`に
入り(斉次性より`μ(γ_t φ)=t·μ(φ)≤t<1`)、`t→1⁻`で`φ`に収束する
(`continuous_radialPath`)ことから`φ∈closure St(p)`
(`OpenBall_formalization_plan.md` 2節)。 -/

/-- **`St(p)`の閉包**: `closure St(p) = {φ | μ(φ) ≤ 1}`。 -/
theorem closure_isStationary {p : ℕ} (hp : 0 < p) :
    closure {φ : Fin p → ℝ | IsStationary φ} = {φ : Fin p → ℝ | mu hp φ ≤ 1} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro φ hφ
      exact ((isStationary_iff_mu_lt_one hp φ).mp hφ).le
    · exact isClosed_le (continuous_mu hp) continuous_const
  · intro φ hφ
    simp only [Set.mem_setOf_eq] at hφ
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuous_iff.mp (continuous_radialPath φ) 1 ε hε
    set t : ℝ := 1 - min δ 1 / 2 with htdef
    have hδ'pos : 0 < min δ 1 / 2 := by
      have : 0 < min δ 1 := lt_min hδpos one_pos
      linarith
    have hmin_le1 : min δ 1 ≤ 1 := min_le_right δ 1
    have hmin_leδ : min δ 1 ≤ δ := min_le_left δ 1
    have ht0 : 0 ≤ t := by rw [htdef]; linarith
    have htlt1 : t < 1 := by rw [htdef]; linarith
    have ht1 : dist t 1 < δ := by
      rw [Real.dist_eq, htdef]
      have habs : |1 - min δ 1 / 2 - 1| = min δ 1 / 2 := by
        rw [show (1 : ℝ) - min δ 1 / 2 - 1 = -(min δ 1 / 2) by ring, abs_neg,
          abs_of_pos hδ'pos]
      rw [habs]
      linarith
    have hstat : IsStationary (gammaT t φ) := by
      rw [isStationary_iff_mu_lt_one hp, mu_gammaT hp φ ht0]
      have hle : t * mu hp φ ≤ t * 1 := mul_le_mul_of_nonneg_left hφ ht0
      rw [mul_one] at hle
      linarith
    refine ⟨gammaT t φ, hstat, ?_⟩
    have hd := hδ t ht1
    rw [gammaT_one, dist_comm] at hd
    exact hd

/-- **`∂St(p) = {μ=1}`**: 定常領域の境界は`μ=1`という「超曲面」
(`IsOpen St(p)`(`isOpen_isStationary`)と`closure_isStationary`の特徴づけから従う)。 -/
theorem frontier_isStationary_eq {p : ℕ} (hp : 0 < p) :
    frontier {φ : Fin p → ℝ | IsStationary φ} = {φ : Fin p → ℝ | mu hp φ = 1} := by
  unfold frontier
  rw [(isOpen_isStationary hp).interior_eq, closure_isStationary hp]
  ext φ
  simp only [Set.mem_sdiff, Set.mem_setOf_eq, isStationary_iff_mu_lt_one hp, not_lt]
  constructor
  · intro h
    exact le_antisymm h.1 h.2
  · intro h
    exact ⟨h.le, h.ge⟩

end StTopology
