import Mathlib
import StTopology.RadialCoordinate
import StTopology.CoeffBound

set_option linter.style.header false

/-!
# `Ξ : closure St(p) → closure C_p` (`prop:xi-homeo`)

論文 `5_kanren.tex`, Section 3.9 の `prop:xi-homeo`。`Ξ φ := if φ=O_p then O_p
else γ_{r(φ)}(φ)`。このファイルでは値域(`ν∘Ξ=μ`)・単射性・全射性(逆写像の公式)
を扱う(論文の証明をそのまま逐語訳)。連続性は追って別途扱う。

## 単射性・全射性の証明の骨子(論文どおり)

**単射性**: `Ξφ_1=Ξφ_2=ψ`(`φ_1,φ_2≠O_p`)のとき、`r_i:=r(φ_i)`とおくと
`ν(ψ)=ν(γ_{r_i}φ_i)=μ(φ_i)`(`r_eq`)なので`μ(φ_1)=μ(φ_2)=:ρ>0`。斉次性`mu_gammaT`
より`μ(ψ)=r_i·ρ`なので`r_1=r_2=:r`。`γ_r φ_1=ψ=γ_r φ_2`に`γ_{1/r}`を当て、半群律
`gammaT_gammaT`と`γ_1=id`(`gammaT_one`)で`φ_1=φ_2`。

**全射性・逆写像公式**: `ψ≠O_p`、`ν(ψ)≤1`のとき`φ:=γ_{ν(ψ)/μ(ψ)}(ψ)`とおくと
斉次性より`μ(φ)=ν(ψ)≤1`。半群律より`γ_{μ(ψ)/ν(ψ)}(φ)=ψ`であり、これと`r`の一意性
(`r_unique`)から`r(φ)=μ(ψ)/ν(ψ)`、よって`Ξφ=γ_{r(φ)}φ=ψ`。
-/

namespace StTopology

/-- **`Ξ`の定義**: `φ=O_p`なら`O_p`自身、そうでなければ共有動径座標`r(φ)`による
`γ`スケーリング。 -/
noncomputable def Xi {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) : Fin p → ℝ :=
  if h : φ = fun _ => 0 then φ else gammaT (r hp h) φ

theorem Xi_zero {p : ℕ} (hp : 0 < p) : Xi hp (fun _ => (0 : ℝ)) = fun _ => 0 := by
  unfold Xi
  rw [dif_pos rfl]

theorem Xi_apply_of_ne_zero {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : φ ≠ fun _ => 0) :
    Xi hp φ = gammaT (r hp hφ) φ := by
  unfold Xi
  rw [dif_neg hφ]

/-- **`ν∘Ξ=μ`**: `Ξ`の値域が`closure C_p`に入ることの核心的な等式(`O_p`でも
`r_eq`による非零の場合でも成り立つ)。 -/
theorem nu_Xi_eq_mu {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    nu (Xi hp φ) = mu hp φ := by
  by_cases hφ : φ = fun _ => 0
  · subst hφ
    rw [Xi_zero, (nu_eq_zero_iff _).mpr rfl, (mu_eq_zero_iff hp _).mpr rfl]
  · rw [Xi_apply_of_ne_zero hp hφ, r_eq hp hφ]

theorem Xi_eq_zero_iff {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    Xi hp φ = (fun _ => 0) ↔ φ = fun _ => 0 := by
  constructor
  · intro h
    by_contra hφ
    rw [Xi_apply_of_ne_zero hp hφ] at h
    exact hφ ((gammaT_eq_zero_iff (r_pos hp hφ).ne' φ).mp h)
  · intro h
    rw [h, Xi_zero]

/-- **`Ξ`の単射性**(論文どおり、`closure St(p)`への制限すら不要な大域的な事実)。 -/
theorem Xi_injective {p : ℕ} (hp : 0 < p) : Function.Injective (Xi hp) := by
  intro φ1 φ2 heq
  by_cases h1 : φ1 = fun _ => 0
  · by_cases h2 : φ2 = fun _ => 0
    · rw [h1, h2]
    · exfalso
      rw [h1, Xi_zero] at heq
      exact h2 ((Xi_eq_zero_iff hp φ2).mp heq.symm)
  · by_cases h2 : φ2 = fun _ => 0
    · exfalso
      rw [h2, Xi_zero] at heq
      exact h1 ((Xi_eq_zero_iff hp φ1).mp heq)
    · rw [Xi_apply_of_ne_zero hp h1, Xi_apply_of_ne_zero hp h2] at heq
      have e1 := r_eq hp h1
      have e2 := r_eq hp h2
      rw [heq] at e1
      have hρeq : mu hp φ1 = mu hp φ2 := e1.symm.trans e2
      have hρne : mu hp φ1 ≠ 0 := fun h => h1 ((mu_eq_zero_iff hp φ1).mp h)
      have hmu1 : mu hp (gammaT (r hp h1) φ1) = r hp h1 * mu hp φ1 :=
        mu_gammaT hp φ1 (r_pos hp h1).le
      have hmu2 : mu hp (gammaT (r hp h2) φ2) = r hp h2 * mu hp φ2 :=
        mu_gammaT hp φ2 (r_pos hp h2).le
      rw [heq] at hmu1
      have hkey : r hp h1 * mu hp φ1 = r hp h2 * mu hp φ2 := hmu1.symm.trans hmu2
      rw [← hρeq] at hkey
      have hreq : r hp h1 = r hp h2 := mul_right_cancel₀ hρne hkey
      rw [hreq] at heq
      have hrne : r hp h2 ≠ 0 := (r_pos hp h2).ne'
      have hcong := congrArg (gammaT (1 / r hp h2)) heq
      simp only [gammaT_gammaT] at hcong
      have h1r : (1 : ℝ) / r hp h2 * r hp h2 = 1 := by field_simp
      rwa [h1r, gammaT_one, gammaT_one] at hcong

/-- **`Ξ`の逆写像**: 論文の逆写像公式 `ψ ↦ γ_{ν(ψ)/μ(ψ)}(ψ)` を(`O_p`は`O_p`に、
という junk value で)totalize した関数。 -/
noncomputable def XiInv {p : ℕ} (hp : 0 < p) (ψ : Fin p → ℝ) : Fin p → ℝ :=
  if ψ = fun _ => 0 then ψ else gammaT (nu ψ / mu hp ψ) ψ

theorem XiInv_of_ne_zero {p : ℕ} (hp : 0 < p) {ψ : Fin p → ℝ} (hψ : ψ ≠ fun _ => 0) :
    XiInv hp ψ = gammaT (nu ψ / mu hp ψ) ψ := by
  unfold XiInv; rw [if_neg hψ]

theorem XiInv_zero {p : ℕ} (hp : 0 < p) : XiInv hp (fun _ => (0 : ℝ)) = fun _ => 0 := by
  unfold XiInv; rw [if_pos rfl]

/-- **`μ∘Ξ⁻¹=ν`**(`ν∘Ξ=μ`の対の等式)。 -/
theorem mu_XiInv_eq_nu {p : ℕ} (hp : 0 < p) (ψ : Fin p → ℝ) :
    mu hp (XiInv hp ψ) = nu ψ := by
  by_cases hψ : ψ = fun _ => 0
  · subst hψ
    rw [XiInv_zero, (mu_eq_zero_iff hp _).mpr rfl, (nu_eq_zero_iff _).mpr rfl]
  · have hnuψpos : 0 < nu ψ :=
      (nu_nonneg ψ).lt_of_ne (fun h => hψ ((nu_eq_zero_iff ψ).mp h.symm))
    have hmuψpos : 0 < mu hp ψ :=
      (mu_nonneg hp ψ).lt_of_ne (fun h => hψ ((mu_eq_zero_iff hp ψ).mp h.symm))
    rw [XiInv_of_ne_zero hp hψ, mu_gammaT hp ψ (by positivity)]
    field_simp

/-- **`Ξ`は`Ξ⁻¹`の右逆写像**: `Ξ(Ξ⁻¹ψ)=ψ`(すべての`ψ`で、`ν(ψ)≤1`という制約は
不要)。論文の全射性・逆写像公式の議論そのもの。 -/
theorem Xi_XiInv {p : ℕ} (hp : 0 < p) (ψ : Fin p → ℝ) : Xi hp (XiInv hp ψ) = ψ := by
  by_cases hψ0 : ψ = fun _ => 0
  · rw [hψ0, XiInv_zero]; exact Xi_zero hp
  · have hnuψpos : 0 < nu ψ :=
      (nu_nonneg ψ).lt_of_ne (fun h => hψ0 ((nu_eq_zero_iff ψ).mp h.symm))
    have hmuψpos : 0 < mu hp ψ :=
      (mu_nonneg hp ψ).lt_of_ne (fun h => hψ0 ((mu_eq_zero_iff hp ψ).mp h.symm))
    rw [XiInv_of_ne_zero hp hψ0]
    set c : ℝ := nu ψ / mu hp ψ with hcdef
    have hc0 : 0 ≤ c := by rw [hcdef]; positivity
    set φ : Fin p → ℝ := gammaT c ψ with hφdef
    have hmuφ : mu hp φ = nu ψ := by
      rw [hφdef, mu_gammaT hp ψ hc0, hcdef]
      field_simp
    have hφ0 : φ ≠ fun _ => 0 := by
      intro h
      rw [h, (mu_eq_zero_iff hp _).mpr rfl] at hmuφ
      linarith
    have hmul1 : mu hp ψ / nu ψ * (nu ψ / mu hp ψ) = 1 := by field_simp
    have hinvcomp : gammaT (mu hp ψ / nu ψ) φ = ψ := by
      rw [hφdef, gammaT_gammaT, hcdef, hmul1, gammaT_one]
    have hνeq : nu (gammaT (mu hp ψ / nu ψ) φ) = mu hp φ := by
      rw [hinvcomp, hmuφ]
    have hrpos : 0 < mu hp ψ / nu ψ := div_pos hmuψpos hnuψpos
    have hreq : mu hp ψ / nu ψ = r hp hφ0 := r_unique hp hφ0 hrpos hνeq
    rw [Xi_apply_of_ne_zero hp hφ0, ← hreq]
    exact hinvcomp

/-- **`Ξ⁻¹`は`Ξ`の左逆写像**: `Ξ⁻¹(Ξφ)=φ`。`Xi_XiInv`(右逆)と`Xi_injective`から
直ちに従う(単射 + どこでも右逆写像を持つ ⟹ そこでも左逆写像)。 -/
theorem XiInv_Xi {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) : XiInv hp (Xi hp φ) = φ :=
  Xi_injective hp (Xi_XiInv hp (Xi hp φ))

/-- **`Ξ`の全射性・逆写像公式**: `ν(ψ)≤1`ならば`ψ`は`Ξ`の(`closure St(p)`内の)
像に入る。`Xi_XiInv`・`mu_XiInv_eq_nu`から即座。 -/
theorem exists_preimage_Xi {p : ℕ} (hp : 0 < p) {ψ : Fin p → ℝ} (hψ : nu ψ ≤ 1) :
    ∃ φ, mu hp φ ≤ 1 ∧ Xi hp φ = ψ :=
  ⟨XiInv hp ψ, by rw [mu_XiInv_eq_nu]; exact hψ, Xi_XiInv hp ψ⟩

/-- **`Ξ`は`Fin p → ℝ`全体の(`closure St(p)`への制限なしの)大域的な全単射**。 -/
noncomputable def XiEquiv {p : ℕ} (hp : 0 < p) : (Fin p → ℝ) ≃ (Fin p → ℝ) where
  toFun := Xi hp
  invFun := XiInv hp
  left_inv := XiInv_Xi hp
  right_inv := Xi_XiInv hp

/-! ### 連続性

`O_p` を除いた連続性は `r` の連続性(`r_continuousAt`)と `gammaT` の(組)連続性の
合成として機械的。`O_p` での連続性は、`ν∘Ξ=μ`(`nu_Xi_eq_mu`)と「`ν` は各座標を
上から抑える」(`abs_le_nu`)を組み合わせると `μ` の `O_p` での連続性
(`continuous_mu`)に直接帰着し、コンパクト性を経由しない(`OpenBall_formalization_plan.md`
は`closure St(p)`のコンパクト性を要求していたが、`ν∘Ξ=μ`という強い等式のおかげで
不要だった)。 -/

/-- `r` の定義域外(`φ=O_p`)でも使える、`0` を junk value とする totalize 版。 -/
noncomputable def rExt {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) : ℝ :=
  if h : φ = fun _ => 0 then 0 else r hp h

theorem rExt_of_ne {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : φ ≠ fun _ => 0) :
    rExt hp φ = r hp hφ := by
  unfold rExt
  rw [dif_neg hφ]

/-- **`Ξ = γ_{rExt(·)}(·)`**(大域的な等式、`O_p`でも成り立つ: 両辺とも`O_p`)。 -/
theorem Xi_eq_gammaT_rExt {p : ℕ} (hp : 0 < p) (φ : Fin p → ℝ) :
    Xi hp φ = gammaT (rExt hp φ) φ := by
  by_cases hφ : φ = fun _ => 0
  · subst hφ
    rw [Xi_zero]
    funext i
    unfold gammaT
    simp
  · rw [Xi_apply_of_ne_zero hp hφ, rExt_of_ne hp hφ]

/-- `γ` の `(t,φ)` に関する同時連続性。 -/
theorem continuous_gammaT_uncurry {p : ℕ} :
    Continuous (fun x : ℝ × (Fin p → ℝ) => gammaT x.1 x.2) := by
  apply continuous_pi
  intro i
  unfold gammaT
  fun_prop

/-- `rExt` は `φ₀≠O_p` で連続(`r_continuousAt` を `{φ≠O_p}` が開であることと
組み合わせて `ContinuousAt` の形に翻訳するだけ)。 -/
theorem continuousAt_rExt {p : ℕ} (hp : 0 < p) {φ₀ : Fin p → ℝ} (hφ₀ : φ₀ ≠ fun _ => 0) :
    ContinuousAt (rExt hp) φ₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := r_continuousAt hp hφ₀ ε hε
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.isOpen_iff.mp isOpen_ne φ₀ hφ₀
  refine ⟨min δ₀ δ₁, lt_min hδ₀pos hδ₁pos, fun φ hφdist => ?_⟩
  have hφne : φ ≠ fun _ => 0 :=
    hδ₀sub (Metric.mem_ball.mpr (hφdist.trans_le (min_le_left _ _)))
  have hφdist1 : dist φ φ₀ < δ₁ := hφdist.trans_le (min_le_right _ _)
  rw [rExt_of_ne hp hφne, rExt_of_ne hp hφ₀]
  exact hδ₁ φ hφne hφdist1

/-- **`Ξ` の `O_p` を除いた連続性**。 -/
theorem continuousAt_Xi_of_ne_zero {p : ℕ} (hp : 0 < p) {φ₀ : Fin p → ℝ}
    (hφ₀ : φ₀ ≠ fun _ => 0) : ContinuousAt (Xi hp) φ₀ := by
  have heq : Xi hp = fun φ => gammaT (rExt hp φ) φ := funext (Xi_eq_gammaT_rExt hp)
  rw [heq]
  exact ContinuousAt.comp₂ continuous_gammaT_uncurry.continuousAt (continuousAt_rExt hp hφ₀)
    continuousAt_id

/-- **`Ξ` の `O_p` での連続性**: `ν(Ξφ)=μ(φ)` と「`ν` は各座標を抑える」ことから、
`Ξφ`の各座標は`μ(φ)`で抑えられる。`μ`の`O_p`での連続性(`continuous_mu`)に直接帰着し、
コンパクト性は不要。 -/
theorem continuousAt_Xi_zero {p : ℕ} (hp : 0 < p) :
    ContinuousAt (Xi hp) (fun _ => (0 : ℝ)) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hcontmu : ContinuousAt (mu hp) (fun _ => (0 : ℝ)) := (continuous_mu hp).continuousAt
  rw [Metric.continuousAt_iff] at hcontmu
  obtain ⟨δ, hδpos, hδ⟩ := hcontmu ε hε
  refine ⟨δ, hδpos, fun φ hφdist => ?_⟩
  have hmuφ : dist (mu hp φ) (mu hp (fun _ => (0 : ℝ))) < ε := hδ hφdist
  rw [(mu_eq_zero_iff hp _).mpr rfl, Real.dist_eq, sub_zero,
    abs_of_nonneg (mu_nonneg hp φ)] at hmuφ
  rw [Xi_zero]
  have hbound : dist (Xi hp φ) (fun _ : Fin p => (0 : ℝ)) ≤ mu hp φ := by
    rw [dist_pi_le_iff (mu_nonneg hp φ)]
    intro i
    rw [Real.dist_eq, sub_zero]
    calc |Xi hp φ i| ≤ nu (Xi hp φ) := abs_le_nu (Xi hp φ) i
      _ = mu hp φ := nu_Xi_eq_mu hp φ
  exact lt_of_le_of_lt hbound hmuφ

/-- **`Ξ` の連続性**(`ContinuousOn`版、まとめ)。 -/
theorem continuousOn_Xi {p : ℕ} (hp : 0 < p) :
    ContinuousOn (Xi hp) (closure {φ : Fin p → ℝ | IsStationary φ}) := by
  intro φ hφmem
  by_cases hφ : φ = fun _ => 0
  · subst hφ
    exact (continuousAt_Xi_zero hp).continuousWithinAt
  · exact (continuousAt_Xi_of_ne_zero hp hφ).continuousWithinAt

/-- **`Ξ` は`Fin p → ℝ`全体で連続**(`O_p`を除いた連続性と`O_p`での連続性を
あわせると、実は定義域全体で連続になる)。 -/
theorem continuous_Xi {p : ℕ} (hp : 0 < p) : Continuous (Xi hp) := by
  rw [continuous_iff_continuousAt]
  intro φ
  by_cases hφ : φ = fun _ => 0
  · subst hφ; exact continuousAt_Xi_zero hp
  · exact continuousAt_Xi_of_ne_zero hp hφ

/-- **`Ξ⁻¹` の `O_p` を除いた連続性**: `φ ↦ γ_{ν(φ)/μ(φ)}(φ)` という明示式そのもの
(`r` を経由しないぶん `Ξ` 自身の連続性より単純)。 -/
theorem continuousAt_XiInv_of_ne_zero {p : ℕ} (hp : 0 < p) {ψ₀ : Fin p → ℝ}
    (hψ₀ : ψ₀ ≠ fun _ => 0) : ContinuousAt (XiInv hp) ψ₀ := by
  have hmuψ₀ne : mu hp ψ₀ ≠ 0 := fun h => hψ₀ ((mu_eq_zero_iff hp ψ₀).mp h)
  have hdiv : ContinuousAt (fun ψ : Fin p → ℝ => nu ψ / mu hp ψ) ψ₀ :=
    continuous_nu.continuousAt.div (continuous_mu hp).continuousAt hmuψ₀ne
  have hcont : ContinuousAt (fun ψ : Fin p → ℝ => gammaT (nu ψ / mu hp ψ) ψ) ψ₀ :=
    ContinuousAt.comp₂ continuous_gammaT_uncurry.continuousAt hdiv continuousAt_id
  refine hcont.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hψ₀] with ψ hψ
  rw [XiInv_of_ne_zero hp hψ]

/-- **`Ξ⁻¹` の `O_p` での連続性**: `μ(Ξ⁻¹ψ)=ν(ψ)`(`mu_XiInv_eq_nu`)と一般化 Vieta
による係数評価(`abs_coeff_le_of_roots_norm_le`、`CoeffBound.lean`)を組み合わせて
`|Ξ⁻¹(ψ)ᵢ| ≤ C(p,i+1)·ν(ψ)^{i+1}` を得て、`ν`の`O_p`での連続性(`continuous_nu`)に
帰着する。ここが`Ξ`自身の`O_p`での連続性と違って係数評価を要する箇所
(`μ`は根のノルムしか直接抑えないので、`ν`のように座標を直接抑えられない)。 -/
theorem continuousAt_XiInv_zero {p : ℕ} (hp : 0 < p) :
    ContinuousAt (XiInv hp) (fun _ => (0 : ℝ)) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set M : ℝ := ∑ i : Fin p, (p.choose ((i : ℕ) + 1) : ℝ) with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hMbound : ∀ i : Fin p, (p.choose ((i : ℕ) + 1) : ℝ) ≤ M := fun i => by
    rw [hMdef]
    exact Finset.single_le_sum (f := fun j : Fin p => (p.choose ((j : ℕ) + 1) : ℝ))
      (fun j _ => Nat.cast_nonneg _) (Finset.mem_univ i)
  have hcontnu : ContinuousAt (nu : (Fin p → ℝ) → ℝ) (fun _ => (0 : ℝ)) :=
    continuous_nu.continuousAt
  rw [Metric.continuousAt_iff] at hcontnu
  obtain ⟨δ, hδpos, hδ⟩ := hcontnu (min 1 (ε / (M + 1))) (by positivity)
  refine ⟨δ, hδpos, fun ψ hψdist => ?_⟩
  have hnuψ : dist (nu ψ) (nu (fun _ => (0 : ℝ))) < min 1 (ε / (M + 1)) := hδ hψdist
  rw [(nu_eq_zero_iff _).mpr rfl, Real.dist_eq, sub_zero, abs_of_nonneg (nu_nonneg ψ)] at hnuψ
  have hnuψle1 : nu ψ ≤ 1 := (hnuψ.trans_le (min_le_left _ _)).le
  have hnuψsmall : nu ψ < ε / (M + 1) := hnuψ.trans_le (min_le_right _ _)
  rw [XiInv_zero]
  have hbound : dist (XiInv hp ψ) (fun _ : Fin p => (0 : ℝ)) ≤ M * nu ψ := by
    rw [dist_pi_le_iff (mul_nonneg hM0 (nu_nonneg ψ))]
    intro i
    rw [Real.dist_eq, sub_zero]
    have hzbound : ∀ z ∈ (charPoly (XiInv hp ψ)).roots, ‖z‖ ≤ mu hp (XiInv hp ψ) := by
      intro z hz
      have hzmem : z ∈ (charPoly (XiInv hp ψ)).roots.toFinset := Multiset.mem_toFinset.mpr hz
      unfold mu
      exact Finset.le_sup' (‖·‖) hzmem
    have hcoeffbound := abs_coeff_le_of_roots_norm_le hp (XiInv hp ψ) (mu_nonneg hp _) hzbound i
    rw [mu_XiInv_eq_nu] at hcoeffbound
    have hpow : (nu ψ) ^ ((i : ℕ) + 1) ≤ nu ψ := by
      calc (nu ψ) ^ ((i : ℕ) + 1) ≤ (nu ψ) ^ 1 :=
            pow_le_pow_of_le_one (nu_nonneg ψ) hnuψle1 (by omega)
        _ = nu ψ := pow_one _
    calc |XiInv hp ψ i| ≤ (p.choose ((i : ℕ) + 1) : ℝ) * (nu ψ) ^ ((i : ℕ) + 1) := hcoeffbound
      _ ≤ (p.choose ((i : ℕ) + 1) : ℝ) * nu ψ :=
          mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
      _ ≤ M * nu ψ := mul_le_mul_of_nonneg_right (hMbound i) (nu_nonneg ψ)
  have hMεbound : M * nu ψ < ε := by
    have h1 : nu ψ * (M + 1) < ε := (lt_div_iff₀ (by linarith)).mp hnuψsmall
    nlinarith [nu_nonneg ψ]
  exact lt_of_le_of_lt hbound hMεbound

/-- **`Ξ⁻¹` の連続性**(`ContinuousOn`版、まとめ)。 -/
theorem continuousOn_XiInv {p : ℕ} (hp : 0 < p) :
    ContinuousOn (XiInv hp) (closure {ψ : Fin p → ℝ | nu ψ < 1}) := by
  intro ψ hψmem
  by_cases hψ : ψ = fun _ => 0
  · subst hψ
    exact (continuousAt_XiInv_zero hp).continuousWithinAt
  · exact (continuousAt_XiInv_of_ne_zero hp hψ).continuousWithinAt

/-- **`Ξ⁻¹` は`Fin p → ℝ`全体で連続**(`Ξ`と同様、`O_p`を除いた連続性と`O_p`での
連続性をあわせると定義域全体で連続になる)。 -/
theorem continuous_XiInv {p : ℕ} (hp : 0 < p) : Continuous (XiInv hp) := by
  rw [continuous_iff_continuousAt]
  intro ψ
  by_cases hψ : ψ = fun _ => 0
  · subst hψ; exact continuousAt_XiInv_zero hp
  · exact continuousAt_XiInv_of_ne_zero hp hψ

/-! ### `Homeomorph` としてのパッケージング -/

theorem nu_Xi_le_one_of_mu_le_one {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : mu hp φ ≤ 1) :
    nu (Xi hp φ) ≤ 1 := by rw [nu_Xi_eq_mu]; exact hφ

theorem mu_XiInv_le_one_of_nu_le_one {p : ℕ} (hp : 0 < p) {ψ : Fin p → ℝ} (hψ : nu ψ ≤ 1) :
    mu hp (XiInv hp ψ) ≤ 1 := by rw [mu_XiInv_eq_nu]; exact hψ

theorem Xi_mapsTo {p : ℕ} (hp : 0 < p) :
    Set.MapsTo (Xi hp) (closure {φ : Fin p → ℝ | IsStationary φ})
      (closure {ψ : Fin p → ℝ | nu ψ < 1}) := by
  intro φ hφ
  rw [closure_isStationary hp] at hφ
  rw [closure_crystal]
  exact nu_Xi_le_one_of_mu_le_one hp hφ

theorem XiInv_mapsTo {p : ℕ} (hp : 0 < p) :
    Set.MapsTo (XiInv hp) (closure {ψ : Fin p → ℝ | nu ψ < 1})
      (closure {φ : Fin p → ℝ | IsStationary φ}) := by
  intro ψ hψ
  rw [closure_crystal] at hψ
  rw [closure_isStationary hp]
  exact mu_XiInv_le_one_of_nu_le_one hp hψ

/-- **`prop:xi-homeo`**: `Ξ : closure St(p) ≃ₜ closure C_p`(明示的な同相写像)。 -/
noncomputable def XiHomeo {p : ℕ} (hp : 0 < p) :
    closure {φ : Fin p → ℝ | IsStationary φ} ≃ₜ closure {ψ : Fin p → ℝ | nu ψ < 1} where
  toFun x := ⟨Xi hp x.1, Xi_mapsTo hp x.2⟩
  invFun y := ⟨XiInv hp y.1, XiInv_mapsTo hp y.2⟩
  left_inv x := Subtype.ext (XiInv_Xi hp x.1)
  right_inv y := Subtype.ext (Xi_XiInv hp y.1)
  continuous_toFun := Continuous.subtype_mk (continuousOn_Xi hp).restrict _
  continuous_invFun := Continuous.subtype_mk (continuousOn_XiInv hp).restrict _

end StTopology
