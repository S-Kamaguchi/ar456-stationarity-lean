import Mathlib
import StTopology.StationarityRegions
import StTopology.MaximalComponentPrinciple
import StTopology.StOpen
import StTopology.StConnected
import StTopology.RootPerturbation
import StTopology.VietaBound
import StTopology.AR3
import StTopology.AR4
import StTopology.AR4Sufficiency
import StTopology.AR5
import StTopology.AR5Sufficiency

set_option linter.style.header false

/-!
# AR(6) の定常性: 明示的閉形式条件との同値性

`6_kanren.tex`, Section 4.6 の議論を、`AR5.lean`/`AR5Sufficiency.lean` と同型の方針で
形式化する。`AR5.lean` の Step-down 補題 (次数5→4) をそのまま次数6→5に一般化する。
-/

open Finset StTopology

namespace StTopology

/-! ### Schur–Cohn 変換 (down-step) `ψ = φ^{(5)}`, 次数6→5 -/

/-- `ψ_i = (φ_i + φ_6 φ_{6-i}) / (1-φ_6^2)`, `i=1,…,5`。`6_kanren.tex` Section 4.6,
hypothesis (a) の検証部分で使われている式。 -/
noncomputable def phiDown5 (φ : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![(φ 0 + φ 5 * φ 4) / (1 - φ 5 ^ 2), (φ 1 + φ 5 * φ 3) / (1 - φ 5 ^ 2),
    (φ 2 + φ 5 * φ 2) / (1 - φ 5 ^ 2), (φ 3 + φ 5 * φ 1) / (1 - φ 5 ^ 2),
    (φ 4 + φ 5 * φ 0) / (1 - φ 5 ^ 2)]

/-- 反射係数を `0` から `φ_6` にスケーリングする経路 (Levinson–Durbin の step-up 公式)。
`γ(t)_i = ψ_i - t k ψ_{4-i}` (`i=0,…,4`), `γ(t)_5 = tk`, ただし `ψ=phiDown5 φ`, `k=φ_6`。
`γ(0)=(ψ,0)` は自明に定常、`γ(1)=φ`。 -/
noncomputable def phiUpPath5 (φ : Fin 6 → ℝ) (t : ℝ) : Fin 6 → ℝ :=
  ![phiDown5 φ 0 - t * φ 5 * phiDown5 φ 4, phiDown5 φ 1 - t * φ 5 * phiDown5 φ 3,
    phiDown5 φ 2 - t * φ 5 * phiDown5 φ 2, phiDown5 φ 3 - t * φ 5 * phiDown5 φ 1,
    phiDown5 φ 4 - t * φ 5 * phiDown5 φ 0, t * φ 5]

theorem continuous_phiUpPath5 (φ : Fin 6 → ℝ) : Continuous (phiUpPath5 φ) := by
  unfold phiUpPath5
  fun_prop

/-- `Q_ψ(z) := z^5-ψ_0z^4-ψ_1z^3-ψ_2z^2-ψ_3z-ψ_4` の反転が、`‖z‖=1` 上で
`Q_ψ^{rev}(z) = z^5 \overline{Q_ψ(z)}` を満たす (実係数・`z\bar z=1` のみ使う純代数)。 -/
theorem reversal_eq_on_unit_circle5 (ψ0 ψ1 ψ2 ψ3 ψ4 : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    (1 - (ψ0 : ℂ) * z - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z ^ 3 - (ψ3 : ℂ) * z ^ 4
        - (ψ4 : ℂ) * z ^ 5)
      = z ^ 5 * (starRingEnd ℂ)
          (z ^ 5 - (ψ0 : ℂ) * z ^ 4 - (ψ1 : ℂ) * z ^ 3 - (ψ2 : ℂ) * z ^ 2 - (ψ3 : ℂ) * z
            - (ψ4 : ℂ)) := by
  set w : ℂ := (starRingEnd ℂ) z with hw_def
  have hzw : z * w = 1 := by
    rw [hw_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hw5 : z ^ 5 * w ^ 5 = 1 := by
    rw [show z ^ 5 * w ^ 5 = (z * w) ^ 5 from by ring, hzw]; ring
  have hw4 : z ^ 5 * w ^ 4 = z := by
    rw [show z ^ 5 * w ^ 4 = z * (z * w) ^ 4 from by ring, hzw]; ring
  have hw3 : z ^ 5 * w ^ 3 = z ^ 2 := by
    rw [show z ^ 5 * w ^ 3 = z ^ 2 * (z * w) ^ 3 from by ring, hzw]; ring
  have hw2 : z ^ 5 * w ^ 2 = z ^ 3 := by
    rw [show z ^ 5 * w ^ 2 = z ^ 3 * (z * w) ^ 2 from by ring, hzw]; ring
  have hw1 : z ^ 5 * w = z ^ 4 := by
    rw [show z ^ 5 * w = z ^ 4 * (z * w) from by ring, hzw]; ring
  have hexpand : (starRingEnd ℂ) (z ^ 5 - (ψ0 : ℂ) * z ^ 4 - (ψ1 : ℂ) * z ^ 3
        - (ψ2 : ℂ) * z ^ 2 - (ψ3 : ℂ) * z - (ψ4 : ℂ))
      = w ^ 5 - (ψ0 : ℂ) * w ^ 4 - (ψ1 : ℂ) * w ^ 3 - (ψ2 : ℂ) * w ^ 2 - (ψ3 : ℂ) * w
        - (ψ4 : ℂ) := by
    simp only [map_sub, map_mul, map_pow, Complex.conj_ofReal, ← hw_def]
  rw [hexpand]
  have hexpand2 : z ^ 5 * (w ^ 5 - (ψ0 : ℂ) * w ^ 4 - (ψ1 : ℂ) * w ^ 3 - (ψ2 : ℂ) * w ^ 2
        - (ψ3 : ℂ) * w - (ψ4 : ℂ))
      = (z ^ 5 * w ^ 5) - (ψ0 : ℂ) * (z ^ 5 * w ^ 4) - (ψ1 : ℂ) * (z ^ 5 * w ^ 3)
        - (ψ2 : ℂ) * (z ^ 5 * w ^ 2) - (ψ3 : ℂ) * (z ^ 5 * w) - (ψ4 : ℂ) * z ^ 5 := by ring
  rw [hexpand2, hw5, hw4, hw3, hw2, hw1]

/-! ### Step-down 補題: 次数下げ変換は定常性を保つ (次数6→5、`AR5.lean` と同型) -/

/-- `gammaT (clampUnit t) φ` の `φ_6`-座標 `k(t) := (clampUnit t)^6・φ_5` は
`|φ_5|<1` のとき常に `|k(t)|<1`。 -/
theorem clampUnit_pow_mul_lt_one6 {φ5 : ℝ} (h5 : |φ5| < 1) (t : ℝ) :
    |(clampUnit t) ^ 6 * φ5| < 1 := by
  have hmem := clampUnit_mem t
  have h1 : |clampUnit t| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hmem.1], hmem.2⟩
  rw [abs_mul, abs_pow]
  calc |clampUnit t| ^ 6 * |φ5| ≤ 1 ^ 6 * |φ5| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact pow_le_pow_left₀ (abs_nonneg _) h1 6
    _ = |φ5| := by ring
    _ < 1 := h5

/-- **Step-down 補題**: `IsStationary φ` (次数6) ならば `IsStationary (phiDown5 φ)` (次数5)。
`AR5.lean` の `stepDown_isStationary` (次数5→4) と同型。 -/
theorem stepDown_isStationary6 {φ : Fin 6 → ℝ} (hφ : IsStationary φ) :
    IsStationary (phiDown5 φ) := by
  have h5lt1 : |φ 5| < 1 := abs_last_coeff_lt_one (p := 6) (by norm_num) hφ
  set ψAux : ℝ → Fin 5 → ℝ := fun t => phiDown5 (gammaT (clampUnit t) φ) with hψAux_def
  -- 分母が常に非零であること
  have hdenom_pos : ∀ t : ℝ, (0 : ℝ) < 1 - (gammaT (clampUnit t) φ 5) ^ 2 := by
    intro t
    have hgt5 : gammaT (clampUnit t) φ 5 = (clampUnit t) ^ 6 * φ 5 := by
      unfold gammaT; norm_num
    rw [hgt5]
    have := clampUnit_pow_mul_lt_one6 h5lt1 t
    nlinarith [(abs_lt.mp this).1, (abs_lt.mp this).2]
  -- 連続性
  have hψAux_cont : Continuous ψAux := by
    have hgcont : Continuous (fun t : ℝ => gammaT (clampUnit t) φ) :=
      (continuous_radialPath φ).comp clampUnit_continuous
    rw [hψAux_def]
    unfold phiDown5
    apply continuous_pi
    intro i
    fin_cases i <;>
      (apply Continuous.div (by fun_prop) (by fun_prop)
       intro t
       exact (hdenom_pos t).ne')
  -- t=0 での値と定常性
  have hψAux_zero : ψAux 0 = fun _ => (0 : ℝ) := by
    have hc0 : clampUnit 0 = 0 := by unfold clampUnit; norm_num
    simp only [hψAux_def, hc0, gammaT_zero]
    unfold phiDown5
    funext i; fin_cases i <;> norm_num
  have hstat0 : IsStationary (ψAux 0) := by rw [hψAux_zero]; exact isStationary_zero
  -- 開集合性から、小さい t₀>0 で ψAux t₀ も定常
  have hopen : IsOpen (ψAux ⁻¹' {ψ : Fin 5 → ℝ | IsStationary ψ}) :=
    (isOpen_isStationary (by norm_num : (0:ℕ) < 5)).preimage hψAux_cont
  have hmem0 : (0 : ℝ) ∈ ψAux ⁻¹' {ψ : Fin 5 → ℝ | IsStationary ψ} := hstat0
  obtain ⟨δ, hδpos, hδball⟩ := Metric.isOpen_iff.mp hopen 0 hmem0
  set t₀ : ℝ := min (δ / 2) (1 / 2) with ht₀_def
  have ht₀pos : 0 < t₀ := lt_min (by linarith) (by norm_num)
  have ht₀le1 : t₀ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have ht₀ball : t₀ ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht₀pos]
    calc t₀ ≤ δ / 2 := by rw [ht₀_def]; exact min_le_left _ _
      _ < δ := by linarith
  have hstat_t₀ : IsStationary (ψAux t₀) := hδball ht₀ball
  -- 単位円上に根を持たないこと (t∈[0,1] 全域)
  have hno : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 →
      z ^ 5 ≠ ∑ i : Fin 5, (ψAux t i : ℂ) * z ^ (5 - 1 - (i : ℕ)) := by
    intro t ht z hz hcontra
    have hrt : clampUnit t = t := clampUnit_eq_of_mem ht
    have hγstat : IsStationary (gammaT t φ) := isStationary_scale (by norm_num) hφ ht.1 ht.2
    set k : ℝ := (gammaT t φ) 5 with hk_def
    set ψ0 := phiDown5 (gammaT t φ) 0 with hψ0_def
    set ψ1 := phiDown5 (gammaT t φ) 1 with hψ1_def
    set ψ2 := phiDown5 (gammaT t φ) 2 with hψ2_def
    set ψ3 := phiDown5 (gammaT t φ) 3 with hψ3_def
    set ψ4 := phiDown5 (gammaT t φ) 4 with hψ4_def
    have hψAux_t : ψAux t = phiDown5 (gammaT t φ) := by rw [hψAux_def]; dsimp only; rw [hrt]
    rw [hψAux_t] at hcontra
    have hkne : (1 : ℝ) - k ^ 2 ≠ 0 := by
      have := hdenom_pos t
      rw [hrt] at this
      rw [hk_def]; linarith [this]
    have hkC : (k : ℂ) = (gammaT t φ 5 : ℝ) := by rw [hk_def]
    have hdne : (1 : ℝ) - gammaT t φ 5 ^ 2 ≠ 0 := by
      have := hdenom_pos t; rw [hrt] at this; linarith [this]
    have hpd0 : phiDown5 (gammaT t φ) 0
        = (gammaT t φ 0 + gammaT t φ 5 * gammaT t φ 4) / (1 - gammaT t φ 5 ^ 2) := rfl
    have hpd1 : phiDown5 (gammaT t φ) 1
        = (gammaT t φ 1 + gammaT t φ 5 * gammaT t φ 3) / (1 - gammaT t φ 5 ^ 2) := rfl
    have hpd2 : phiDown5 (gammaT t φ) 2
        = (gammaT t φ 2 + gammaT t φ 5 * gammaT t φ 2) / (1 - gammaT t φ 5 ^ 2) := rfl
    have hpd3 : phiDown5 (gammaT t φ) 3
        = (gammaT t φ 3 + gammaT t φ 5 * gammaT t φ 1) / (1 - gammaT t φ 5 ^ 2) := rfl
    have hpd4 : phiDown5 (gammaT t φ) 4
        = (gammaT t φ 4 + gammaT t φ 5 * gammaT t φ 0) / (1 - gammaT t φ 5 ^ 2) := rfl
    have hQψ0 : z ^ 5 - (ψ0 : ℂ) * z ^ 4 - (ψ1 : ℂ) * z ^ 3 - (ψ2 : ℂ) * z ^ 2 - (ψ3 : ℂ) * z
        - (ψ4 : ℂ) = 0 := by
      simp only [Fin.sum_univ_five] at hcontra
      norm_num at hcontra
      linear_combination hcontra
    have hQrev0 : (1 - (ψ0 : ℂ) * z - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z ^ 3 - (ψ3 : ℂ) * z ^ 4
        - (ψ4 : ℂ) * z ^ 5) = 0 := by
      rw [reversal_eq_on_unit_circle5 ψ0 ψ1 ψ2 ψ3 ψ4 z hz, hQψ0]
      simp
    have hUP0 : ψ0 - k * ψ4 = gammaT t φ 0 := by
      rw [hψ0_def, hψ4_def, hk_def, hpd0, hpd4]
      field_simp
      ring
    have hUP1 : ψ1 - k * ψ3 = gammaT t φ 1 := by
      rw [hψ1_def, hψ3_def, hk_def, hpd1, hpd3]
      field_simp
      ring
    have hUP2 : ψ2 - k * ψ2 = gammaT t φ 2 := by
      rw [hψ2_def, hk_def, hpd2]
      field_simp
      ring
    have hUP3 : ψ3 - k * ψ1 = gammaT t φ 3 := by
      rw [hψ3_def, hψ1_def, hk_def, hpd3, hpd1]
      field_simp
      ring
    have hUP4 : ψ4 - k * ψ0 = gammaT t φ 4 := by
      rw [hψ4_def, hψ0_def, hk_def, hpd4, hpd0]
      field_simp
      ring
    have hUP0C : (ψ0 : ℂ) - (k : ℂ) * (ψ4 : ℂ) = (gammaT t φ 0 : ℂ) := by exact_mod_cast hUP0
    have hUP1C : (ψ1 : ℂ) - (k : ℂ) * (ψ3 : ℂ) = (gammaT t φ 1 : ℂ) := by exact_mod_cast hUP1
    have hUP2C : (ψ2 : ℂ) - (k : ℂ) * (ψ2 : ℂ) = (gammaT t φ 2 : ℂ) := by exact_mod_cast hUP2
    have hUP3C : (ψ3 : ℂ) - (k : ℂ) * (ψ1 : ℂ) = (gammaT t φ 3 : ℂ) := by exact_mod_cast hUP3
    have hUP4C : (ψ4 : ℂ) - (k : ℂ) * (ψ0 : ℂ) = (gammaT t φ 4 : ℂ) := by exact_mod_cast hUP4
    have htarget : z ^ 6 - (gammaT t φ 0 : ℂ) * z ^ 5 - (gammaT t φ 1 : ℂ) * z ^ 4
        - (gammaT t φ 2 : ℂ) * z ^ 3 - (gammaT t φ 3 : ℂ) * z ^ 2 - (gammaT t φ 4 : ℂ) * z
        - (gammaT t φ 5 : ℂ)
        = z * (z ^ 5 - (ψ0 : ℂ) * z ^ 4 - (ψ1 : ℂ) * z ^ 3 - (ψ2 : ℂ) * z ^ 2 - (ψ3 : ℂ) * z
            - (ψ4 : ℂ))
          - (k : ℂ) * (1 - (ψ0 : ℂ) * z - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z ^ 3
            - (ψ3 : ℂ) * z ^ 4 - (ψ4 : ℂ) * z ^ 5) := by
      rw [← hkC]
      linear_combination z ^ 5 * hUP0C + z ^ 4 * hUP1C + z ^ 3 * hUP2C + z ^ 2 * hUP3C + z * hUP4C
    rw [hQψ0, hQrev0] at htarget
    simp only [mul_zero, sub_zero] at htarget
    have hzroot : z ^ 6 = (gammaT t φ 0 : ℂ) * z ^ 5 + (gammaT t φ 1 : ℂ) * z ^ 4
        + (gammaT t φ 2 : ℂ) * z ^ 3 + (gammaT t φ 3 : ℂ) * z ^ 2 + (gammaT t φ 4 : ℂ) * z
        + (gammaT t φ 5 : ℂ) := by
      linear_combination htarget
    have hzroot' : z ^ 6 = ∑ i : Fin 6, (gammaT t φ i : ℂ) * z ^ (6 - 1 - (i : ℕ)) := by
      simp only [Fin.sum_univ_six]
      norm_num
      linear_combination hzroot
    have := hγstat z hzroot'
    rw [hz] at this
    exact absurd this (lt_irrefl 1)
  -- 種と単位円回避を合わせて `isStationary_of_path_no_unit_root` を適用 (経路を `[t₀,1]` にずらす)
  set γ' : ℝ → Fin 5 → ℝ := fun s => ψAux (t₀ + s * (1 - t₀)) with hγ'_def
  have hγ'cont : Continuous γ' := by
    rw [hγ'_def]
    exact hψAux_cont.comp (by fun_prop)
  have hγ'0 : γ' 0 = ψAux t₀ := by rw [hγ'_def]; norm_num
  have hγ'1 : γ' 1 = ψAux 1 := by rw [hγ'_def]; norm_num
  have hγ'no : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 →
      z ^ 5 ≠ ∑ i : Fin 5, (γ' s i : ℂ) * z ^ (5 - 1 - (i : ℕ)) := by
    intro s hs z hz
    have hmem : t₀ + s * (1 - t₀) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · nlinarith [hs.1, hs.2, ht₀pos.le, ht₀le1]
      · nlinarith [hs.1, hs.2, ht₀pos.le, ht₀le1]
    exact hno (t₀ + s * (1 - t₀)) hmem z hz
  have hresult : IsStationary (γ' 1) := by
    apply isStationary_of_path_no_unit_root (by norm_num) hγ'cont
    · rw [hγ'0]; exact hstat_t₀
    · exact hγ'no
  rw [hγ'1] at hresult
  have h1eq : clampUnit 1 = 1 := clampUnit_eq_of_mem ⟨zero_le_one, le_refl 1⟩
  have hfin : ψAux 1 = phiDown5 φ := by rw [hψAux_def]; dsimp only; rw [h1eq, gammaT_one]
  rwa [hfin] at hresult

/-! ## 必要性: `IsStationary φ → St6 φ`

`AR5.lean` と同型の方針 (`Ω6` の定義 → `L61 := connectedComponentIn Ω6 O6` →
最大連結成分の原理 → `L61 = IsStationary` → connectedness による符号復元)。
`A6`, `B6` は `StationarityRegions.lean` で既に定義済み。 -/

/-- `E := (1+φ_6)B6² + A6·B6·(φ_5-φ_1) + A6²·(-1-φ_2+φ_4-φ_6)`。`St6` の4番目の条件の
左辺そのもの。 -/
def cplxCond6 (φ : Fin 6 → ℝ) : ℝ :=
  (1 + φ 5) * (B6 φ) ^ 2 + (A6 φ) * (B6 φ) * (φ 4 - φ 0) + (A6 φ) ^ 2 * (-1 - φ 1 + φ 3 - φ 5)

/-- `Ω6`: 論文の `Ω = {φ(1)≠0, φ(-1)≠0, 1-φ_6²>|φ_5+φ_1φ_6|, E≠0}` にあたる開集合。 -/
def Ω6 : Set (Fin 6 → ℝ) :=
  {φ : Fin 6 → ℝ | phiAt1 φ ≠ 0 ∧ phiAtNeg1 φ ≠ 0 ∧ 1 - φ 5 ^ 2 > |φ 4 + φ 0 * φ 5| ∧
    cplxCond6 φ ≠ 0}

/-- 原点 `O_6` は `Ω6` に属する: `φ(1)=1≠0`, `φ(-1)=1≠0`, `1-0=1>0=|0|`,
`cplxCond6=1·0+0-1·(-1)=1≠0`。 -/
theorem zero_mem_Ω6 : (fun _ : Fin 6 => (0 : ℝ)) ∈ Ω6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [phiAt1, phiAtNeg1, cplxCond6, A6, B6]

/-- `L_{6,1}`: `Ω6` 内で原点 `O_6` を含む最大の連結成分。 -/
def L61 : Set (Fin 6 → ℝ) :=
  connectedComponentIn Ω6 (fun _ : Fin 6 => (0 : ℝ))

/-- AR(6) の逆特性方程式を、`Fin 6` の総和を展開した具体形に書き換える。 -/
theorem root_six_iff {φ : Fin 6 → ℝ} (α : ℂ) :
    (α ^ 6 = ∑ i : Fin 6, (φ i : ℂ) * α ^ (6 - 1 - (i : ℕ)))
      ↔ α ^ 6 = (φ 0 : ℂ) * α ^ 5 + (φ 1 : ℂ) * α ^ 4 + (φ 2 : ℂ) * α ^ 3 + (φ 3 : ℂ) * α ^ 2
        + (φ 4 : ℂ) * α + (φ 5 : ℂ) := by
  simp only [Fin.sum_univ_six]
  norm_num

/-! ### hypothesis (a) の4つの部品 -/

theorem phiAt1_ne_zero_of_isStationary6 {φ : Fin 6 → ℝ} (hφ : IsStationary φ) :
    phiAt1 φ ≠ 0 := by
  intro h
  simp only [phiAt1, Fin.sum_univ_six] at h
  have hsum : φ 0 + φ 1 + φ 2 + φ 3 + φ 4 + φ 5 = 1 := by linarith
  have hsumC : (φ 0 : ℂ) + (φ 1 : ℂ) + (φ 2 : ℂ) + (φ 3 : ℂ) + (φ 4 : ℂ) + (φ 5 : ℂ) = 1 := by
    exact_mod_cast hsum
  have hroot : (1 : ℂ) ^ 6 = ∑ i : Fin 6, (φ i : ℂ) * (1 : ℂ) ^ (6 - 1 - (i : ℕ)) := by
    rw [root_six_iff]
    linear_combination -hsumC
  have hlt := hφ 1 hroot
  simp at hlt

theorem phiAtNeg1_ne_zero_of_isStationary6 {φ : Fin 6 → ℝ} (hφ : IsStationary φ) :
    phiAtNeg1 φ ≠ 0 := by
  intro h
  simp only [phiAtNeg1, Fin.sum_univ_six] at h
  norm_num at h
  have hsum : φ 0 - φ 1 + φ 2 - φ 3 + φ 4 - φ 5 = -1 := by linarith
  have hsumC : (φ 0 : ℂ) - (φ 1 : ℂ) + (φ 2 : ℂ) - (φ 3 : ℂ) + (φ 4 : ℂ) - (φ 5 : ℂ) = -1 := by
    exact_mod_cast hsum
  have hroot : (-1 : ℂ) ^ 6 = ∑ i : Fin 6, (φ i : ℂ) * (-1 : ℂ) ^ (6 - 1 - (i : ℕ)) := by
    rw [root_six_iff]
    norm_num
    linear_combination hsumC
  have hlt := hφ (-1) hroot
  simp at hlt

/-- `Ω6` の3番目の条件 (Schur–Cohn 2ステップ分の反射係数の有界性をまとめたもの) は、
`ψ:=phiDown5 φ` に Step-down 補題を適用して得られる `St5 ψ` の3番目の条件 `|ψ_5|<1`
そのもの (`ψ_5 = (φ_5+φ_1φ_6)/(1-φ_6²)` の代数的書き換え)。 -/
theorem unit_cond6_of_isStationary {φ : Fin 6 → ℝ} (hφ : IsStationary φ) :
    1 - φ 5 ^ 2 > |φ 4 + φ 0 * φ 5| := by
  have hψstat : IsStationary (phiDown5 φ) := stepDown_isStationary6 hφ
  have hψSt5 : St5 (phiDown5 φ) := isStationary_imp_St5 hψstat
  have hψ4lt1 : |phiDown5 φ 4| < 1 := hψSt5.2.2.1
  have h5lt1 : |φ 5| < 1 := abs_last_coeff_lt_one (p := 6) (by norm_num) hφ
  have hpos : (0 : ℝ) < 1 - φ 5 := by linarith [(abs_lt.mp h5lt1).2]
  have hpos' : (0 : ℝ) < 1 + φ 5 := by linarith [(abs_lt.mp h5lt1).1]
  have hsqpos : (0 : ℝ) < 1 - φ 5 ^ 2 := by nlinarith [hpos, hpos']
  have hψ4 : phiDown5 φ 4 = (φ 4 + φ 5 * φ 0) / (1 - φ 5 ^ 2) := rfl
  rw [hψ4, abs_div, abs_of_pos hsqpos, div_lt_one hsqpos] at hψ4lt1
  have heq : φ 4 + φ 0 * φ 5 = φ 4 + φ 5 * φ 0 := by ring
  rw [heq]
  linarith [hψ4lt1]

/-- **hypothesis (a) の核**: `cplxCond6 φ ≠ 0`。Step-down 補題 (`stepDown_isStationary6`) で
`ψ:=phiDown5 φ` の定常性を得て、`AR5.isStationary_imp_St5` から `cplxCond5 ψ < 0`
(特に `≠0`) を得る。恒等式 `cplxCond5(ψ)·(1-φ_6)²(1+φ_6)^5 = cplxCond6(φ)` (`field_simp`+
`ring` で検証) と組み合わせ、`cplxCond6 φ ≠ 0` を結論する。 -/
theorem cplxCond6_ne_zero_of_isStationary {φ : Fin 6 → ℝ} (hφ : IsStationary φ) :
    cplxCond6 φ ≠ 0 := by
  have hψstat : IsStationary (phiDown5 φ) := stepDown_isStationary6 hφ
  have hψSt5 : St5 (phiDown5 φ) := isStationary_imp_St5 hψstat
  have hcplx5neg : cplxCond5 (phiDown5 φ) < 0 := hψSt5.2.2.2.1
  have h5lt1 : |φ 5| < 1 := abs_last_coeff_lt_one (p := 6) (by norm_num) hφ
  have hpos : (0 : ℝ) < 1 - φ 5 := by linarith [(abs_lt.mp h5lt1).2]
  have hpos' : (0 : ℝ) < 1 + φ 5 := by linarith [(abs_lt.mp h5lt1).1]
  have hne : (1 : ℝ) - φ 5 ≠ 0 := hpos.ne'
  have hne' : (1 : ℝ) + φ 5 ≠ 0 := hpos'.ne'
  have hsqne : (1 : ℝ) - φ 5 ^ 2 ≠ 0 := by
    intro hc
    apply hne
    have : (1 - φ 5) * (1 + φ 5) = 0 := by nlinarith [hc]
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hne'
  have hψ0 : phiDown5 φ 0 = (φ 0 + φ 5 * φ 4) / (1 - φ 5 ^ 2) := rfl
  have hψ1 : phiDown5 φ 1 = (φ 1 + φ 5 * φ 3) / (1 - φ 5 ^ 2) := rfl
  have hψ2 : phiDown5 φ 2 = (φ 2 + φ 5 * φ 2) / (1 - φ 5 ^ 2) := rfl
  have hψ3 : phiDown5 φ 3 = (φ 3 + φ 5 * φ 1) / (1 - φ 5 ^ 2) := rfl
  have hψ4 : phiDown5 φ 4 = (φ 4 + φ 5 * φ 0) / (1 - φ 5 ^ 2) := rfl
  have hident : cplxCond5 (phiDown5 φ) * ((1 - φ 5) ^ 2 * (1 + φ 5) ^ 5) = cplxCond6 φ := by
    simp only [cplxCond5, cplxCond6, A5, B5, A6, B6, hψ0, hψ1, hψ2, hψ3, hψ4]
    field_simp
    ring
  intro hzero
  rw [hzero] at hident
  have hpossq : (0 : ℝ) < (1 - φ 5) ^ 2 * (1 + φ 5) ^ 5 :=
    mul_pos (pow_pos hpos 2) (pow_pos hpos' 5)
  nlinarith [hcplx5neg, hident, hpossq]

theorem isStationary_mem_Ω6 {φ : Fin 6 → ℝ} (hφ : IsStationary φ) : φ ∈ Ω6 :=
  ⟨phiAt1_ne_zero_of_isStationary6 hφ, phiAtNeg1_ne_zero_of_isStationary6 hφ,
    unit_cond6_of_isStationary hφ, cplxCond6_ne_zero_of_isStationary hφ⟩

/-! ### hypothesis (b) の代数的核: 単位円上の非実根 ⟹ `cplxCond6=0`

`z` を単位円上の非実根、`w:=z̄` (`zw=1`) とする。`AR5.lean` の手法 (`w²`倍) を
6次式に適用すると `w³·sextic(z) = z³-φ0z²-φ1z-φ2-φ3w-φ4w²-φ5w³ =: ⋆` (3次)。`⋆` とその
`z↔w` 版 `⋆'` の差から2次式 (I6), 和から3次式 (R6) が出て、(I6) を使って (R6) の
3次の項を消去すると1次式 (L): `A6·u=B6` (`u=z+w`) が出る。(I6) と (L) から `u` を
消去すると `cplxCond6=0` が得られる (`6_kanren.tex` Section 4.6 の議論)。 -/
theorem cplxCond6_eq_zero_of_unit_root_of_ne {φ : Fin 6 → ℝ} (z : ℂ)
    (hroot : z ^ 6 = (φ 0 : ℂ) * z ^ 5 + (φ 1 : ℂ) * z ^ 4 + (φ 2 : ℂ) * z ^ 3 + (φ 3 : ℂ) * z ^ 2
      + (φ 4 : ℂ) * z + (φ 5 : ℂ))
    (hnorm : ‖z‖ = 1) (hne : z ≠ (starRingEnd ℂ) z) :
    cplxCond6 φ = 0 := by
  set w : ℂ := (starRingEnd ℂ) z with hw
  have hzw : z * w = 1 := by
    rw [hw, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
  have hwz : w * z = 1 := by rw [mul_comm]; exact hzw
  have hroot0 : z ^ 6 - (φ 0 : ℂ) * z ^ 5 - (φ 1 : ℂ) * z ^ 4 - (φ 2 : ℂ) * z ^ 3
      - (φ 3 : ℂ) * z ^ 2 - (φ 4 : ℂ) * z - (φ 5 : ℂ) = 0 := by linear_combination hroot
  have hrootw : w ^ 6 = (φ 0 : ℂ) * w ^ 5 + (φ 1 : ℂ) * w ^ 4 + (φ 2 : ℂ) * w ^ 3
      + (φ 3 : ℂ) * w ^ 2 + (φ 4 : ℂ) * w + (φ 5 : ℂ) := by
    have := congrArg (starRingEnd ℂ) hroot
    simpa [hw, map_add, map_mul, map_pow, Complex.conj_ofReal] using this
  have hrootw0 : w ^ 6 - (φ 0 : ℂ) * w ^ 5 - (φ 1 : ℂ) * w ^ 4 - (φ 2 : ℂ) * w ^ 3
      - (φ 3 : ℂ) * w ^ 2 - (φ 4 : ℂ) * w - (φ 5 : ℂ) = 0 := by linear_combination hrootw
  -- ⋆ : w³·sextic(z) の還元
  have hstar : z ^ 3 - (φ 0 : ℂ) * z ^ 2 - (φ 1 : ℂ) * z - (φ 2 : ℂ) - (φ 3 : ℂ) * w
      - (φ 4 : ℂ) * w ^ 2 - (φ 5 : ℂ) * w ^ 3 = 0 := by
    have h6 : w ^ 3 * z ^ 6 = z ^ 3 := by
      rw [show w ^ 3 * z ^ 6 = z ^ 3 * (z * w) ^ 3 from by ring, hzw]; ring
    have h5 : w ^ 3 * z ^ 5 = z ^ 2 := by
      rw [show w ^ 3 * z ^ 5 = z ^ 2 * (z * w) ^ 3 from by ring, hzw]; ring
    have h4 : w ^ 3 * z ^ 4 = z := by
      rw [show w ^ 3 * z ^ 4 = z * (z * w) ^ 3 from by ring, hzw]; ring
    have h3 : w ^ 3 * z ^ 3 = 1 := by
      rw [show w ^ 3 * z ^ 3 = (z * w) ^ 3 from by ring, hzw]; ring
    have h2 : w ^ 3 * z ^ 2 = w := by
      rw [show w ^ 3 * z ^ 2 = w * (z * w) ^ 2 from by ring, hzw]; ring
    have h1 : w ^ 3 * z = w ^ 2 := by
      rw [show w ^ 3 * z = w ^ 2 * (z * w) from by ring, hzw]; ring
    have hexpand : w ^ 3 * (z ^ 6 - (φ 0 : ℂ) * z ^ 5 - (φ 1 : ℂ) * z ^ 4 - (φ 2 : ℂ) * z ^ 3
          - (φ 3 : ℂ) * z ^ 2 - (φ 4 : ℂ) * z - (φ 5 : ℂ))
        = (w ^ 3 * z ^ 6) - (φ 0 : ℂ) * (w ^ 3 * z ^ 5) - (φ 1 : ℂ) * (w ^ 3 * z ^ 4)
          - (φ 2 : ℂ) * (w ^ 3 * z ^ 3) - (φ 3 : ℂ) * (w ^ 3 * z ^ 2) - (φ 4 : ℂ) * (w ^ 3 * z)
          - (φ 5 : ℂ) * w ^ 3 := by ring
    rw [h6, h5, h4, h3, h2, h1] at hexpand
    rw [hroot0, mul_zero] at hexpand
    linear_combination -hexpand
  -- ⋆' : z³·sextic(w) の還元 (z↔w を入れ替えただけ)
  have hstar' : w ^ 3 - (φ 0 : ℂ) * w ^ 2 - (φ 1 : ℂ) * w - (φ 2 : ℂ) - (φ 3 : ℂ) * z
      - (φ 4 : ℂ) * z ^ 2 - (φ 5 : ℂ) * z ^ 3 = 0 := by
    have h6 : z ^ 3 * w ^ 6 = w ^ 3 := by
      rw [show z ^ 3 * w ^ 6 = w ^ 3 * (w * z) ^ 3 from by ring, hwz]; ring
    have h5 : z ^ 3 * w ^ 5 = w ^ 2 := by
      rw [show z ^ 3 * w ^ 5 = w ^ 2 * (w * z) ^ 3 from by ring, hwz]; ring
    have h4 : z ^ 3 * w ^ 4 = w := by
      rw [show z ^ 3 * w ^ 4 = w * (w * z) ^ 3 from by ring, hwz]; ring
    have h3 : z ^ 3 * w ^ 3 = 1 := by
      rw [show z ^ 3 * w ^ 3 = (w * z) ^ 3 from by ring, hwz]; ring
    have h2 : z ^ 3 * w ^ 2 = z := by
      rw [show z ^ 3 * w ^ 2 = z * (w * z) ^ 2 from by ring, hwz]; ring
    have h1 : z ^ 3 * w = z ^ 2 := by
      rw [show z ^ 3 * w = z ^ 2 * (w * z) from by ring, hwz]; ring
    have hexpand : z ^ 3 * (w ^ 6 - (φ 0 : ℂ) * w ^ 5 - (φ 1 : ℂ) * w ^ 4 - (φ 2 : ℂ) * w ^ 3
          - (φ 3 : ℂ) * w ^ 2 - (φ 4 : ℂ) * w - (φ 5 : ℂ))
        = (z ^ 3 * w ^ 6) - (φ 0 : ℂ) * (z ^ 3 * w ^ 5) - (φ 1 : ℂ) * (z ^ 3 * w ^ 4)
          - (φ 2 : ℂ) * (z ^ 3 * w ^ 3) - (φ 3 : ℂ) * (z ^ 3 * w ^ 2) - (φ 4 : ℂ) * (z ^ 3 * w)
          - (φ 5 : ℂ) * z ^ 3 := by ring
    rw [h6, h5, h4, h3, h2, h1] at hexpand
    rw [hrootw0, mul_zero] at hexpand
    linear_combination -hexpand
  have hne' : z - w ≠ 0 := sub_ne_zero.mpr hne
  -- (I6): ⋆-⋆' を (z-w) で割る
  have hII : (1 + (φ 5 : ℂ)) * ((z + w) ^ 2 - 1) + ((φ 4 : ℂ) - (φ 0 : ℂ)) * (z + w)
      + ((φ 3 : ℂ) - (φ 1 : ℂ)) = 0 := by
    have hsub : (z - w) * ((1 + (φ 5 : ℂ)) * ((z + w) ^ 2 - 1) + ((φ 4 : ℂ) - (φ 0 : ℂ)) * (z + w)
        + ((φ 3 : ℂ) - (φ 1 : ℂ))) = 0 := by
      linear_combination hstar - hstar' + (1 + (φ 5 : ℂ)) * (z - w) * hzw
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd h hne'
    · exact h
  -- (R6): ⋆+⋆'
  have hRR : (1 - (φ 5 : ℂ)) * ((z + w) ^ 3 - 3 * (z + w))
      - ((φ 0 : ℂ) + (φ 4 : ℂ)) * ((z + w) ^ 2 - 2) - ((φ 1 : ℂ) + (φ 3 : ℂ)) * (z + w)
      - 2 * (φ 2 : ℂ) = 0 := by
    linear_combination hstar + hstar'
      + (3 * (1 - (φ 5 : ℂ)) * (z + w) - 2 * ((φ 0 : ℂ) + (φ 4 : ℂ))) * hzw
  -- u := z+w (実数)
  set u : ℝ := 2 * z.re with hu_def
  have huC : (u : ℂ) = z + w := by
    rw [hu_def, hw]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.conj_re, Complex.add_im, Complex.conj_im] <;> ring
  have hIIu : (1 + φ 5) * u ^ 2 + (φ 4 - φ 0) * u + (-1 - φ 1 + φ 3 - φ 5) = 0 := by
    have hIIC : (1 + (φ 5 : ℂ)) * (u : ℂ) ^ 2 + ((φ 4 : ℂ) - (φ 0 : ℂ)) * (u : ℂ)
        + (-1 - (φ 1 : ℂ) + (φ 3 : ℂ) - (φ 5 : ℂ)) = 0 := by
      rw [huC]; linear_combination hII
    exact_mod_cast hIIC
  have hRRu : (1 - φ 5) * u ^ 3 - (φ 0 + φ 4) * u ^ 2 + (-3 + 3 * φ 5 - φ 1 - φ 3) * u
      + 2 * (φ 0 + φ 4 - φ 2) = 0 := by
    have hRRC : (1 - (φ 5 : ℂ)) * (u : ℂ) ^ 3 - ((φ 0 : ℂ) + (φ 4 : ℂ)) * (u : ℂ) ^ 2
        + (-3 + 3 * (φ 5 : ℂ) - (φ 1 : ℂ) - (φ 3 : ℂ)) * (u : ℂ)
        + 2 * ((φ 0 : ℂ) + (φ 4 : ℂ) - (φ 2 : ℂ)) = 0 := by
      rw [huC]; linear_combination hRR
    exact_mod_cast hRRC
  -- (L): A6·u = B6 (`(1+φ_6)^2·(R6) - ((1-φ_6²)u - 2(φ_5+φ_1φ_6))·(I6) = 2(A6·u-B6)` を使う)
  have hL : (A6 φ) * u = B6 φ := by
    unfold A6 B6
    linear_combination ((1 : ℝ) / 2) * (1 + φ 5) ^ 2 * hRRu
      - ((1 : ℝ) / 2) * ((1 - φ 5 ^ 2) * u - 2 * (φ 4 + φ 0 * φ 5)) * hIIu
  -- u を消去して cplxCond6 = 0
  unfold cplxCond6
  linear_combination (A6 φ) ^ 2 * hIIu
    + (-(1 + φ 5) * ((B6 φ) + (A6 φ) * u) - (φ 4 - φ 0) * (A6 φ)) * hL

/-- 単位円上の根を持つ `φ` は `Ω6` に属さない (hypothesis (b) の代数部分)。 -/
theorem not_mem_Ω6_of_unit_root {φ : Fin 6 → ℝ} (z : ℂ)
    (hroot : z ^ 6 = (φ 0 : ℂ) * z ^ 5 + (φ 1 : ℂ) * z ^ 4 + (φ 2 : ℂ) * z ^ 3 + (φ 3 : ℂ) * z ^ 2
      + (φ 4 : ℂ) * z + (φ 5 : ℂ))
    (hnorm : ‖z‖ = 1) :
    φ ∉ Ω6 := by
  rintro ⟨h1, hm1, _, hc⟩
  by_cases hreal : z = (starRingEnd ℂ) z
  · have him : z.im = 0 := Complex.conj_eq_iff_im.mp hreal.symm
    have hre : |z.re| = 1 := by
      have : ‖z‖ = |z.re| := by
        rw [Complex.norm_def, Complex.normSq_apply, him]
        simp [Real.sqrt_mul_self_eq_abs]
      rwa [this] at hnorm
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hre with hp | hn
    · have hz1 : z = 1 := by apply Complex.ext <;> simp [hp, him]
      rw [hz1] at hroot
      apply h1
      simp only [phiAt1, Fin.sum_univ_six]
      have : (1 : ℂ) = (φ 0 : ℂ) + (φ 1 : ℂ) + (φ 2 : ℂ) + (φ 3 : ℂ) + (φ 4 : ℂ) + (φ 5 : ℂ) := by
        linear_combination hroot
      have hr : (1 : ℝ) = φ 0 + φ 1 + φ 2 + φ 3 + φ 4 + φ 5 := by exact_mod_cast this
      linarith
    · have hz1 : z = -1 := by apply Complex.ext <;> simp [hn, him]
      rw [hz1] at hroot
      apply hm1
      simp only [phiAtNeg1, Fin.sum_univ_six]
      norm_num
      have : (-1 : ℂ) = (φ 0 : ℂ) - (φ 1 : ℂ) + (φ 2 : ℂ) - (φ 3 : ℂ) + (φ 4 : ℂ) - (φ 5 : ℂ) := by
        linear_combination -hroot
      have hr : (-1 : ℝ) = φ 0 - φ 1 + φ 2 - φ 3 + φ 4 - φ 5 := by exact_mod_cast this
      linarith
  · exact hc (cplxCond6_eq_zero_of_unit_root_of_ne z hroot hnorm hreal)

/-- `Ω6` は開集合。 -/
theorem isOpen_Ω6 : IsOpen Ω6 := by
  have h1 : Continuous (fun φ : Fin 6 → ℝ => phiAt1 φ) := by unfold phiAt1; fun_prop
  have h2 : Continuous (fun φ : Fin 6 → ℝ => phiAtNeg1 φ) := by unfold phiAtNeg1; fun_prop
  have h3 : Continuous (fun φ : Fin 6 → ℝ => φ 4 + φ 0 * φ 5) := by fun_prop
  have h4 : Continuous (fun φ : Fin 6 → ℝ => cplxCond6 φ) := by
    unfold cplxCond6 A6 B6; fun_prop
  exact (isOpen_ne_fun h1 continuous_const).inter
    ((isOpen_ne_fun h2 continuous_const).inter
      ((isOpen_lt (continuous_abs.comp h3) (by fun_prop)).inter
        (isOpen_ne_fun h4 continuous_const)))

/-- hypothesis (b): `L61` は `St(6)` の境界と交わらない。 -/
theorem L61_disjoint_frontier :
    L61 ∩ frontier {φ : Fin 6 → ℝ | IsStationary φ} = ∅ := by
  ext φ
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hφL61, hφfrontier⟩
  obtain ⟨z, hznorm, hzeq⟩ :=
    frontier_isStationary_subset_hasUnitRoot (p := 6) (by norm_num) hφfrontier
  rw [root_six_iff] at hzeq
  exact not_mem_Ω6_of_unit_root z hzeq hznorm (connectedComponentIn_subset Ω6 _ hφL61)

/-- **`L61 = St(6)`**: 最大連結成分の原理を AR(6) に適用した結果。 -/
theorem L61_eq_isStationary : L61 = {φ : Fin 6 → ℝ | IsStationary φ} :=
  maximal_component_principle Ω6 {φ : Fin 6 → ℝ | IsStationary φ}
    (fun _ : Fin 6 => (0 : ℝ))
    zero_mem_Ω6
    (isOpen_isStationary (by norm_num))
    (isPreconnected_isStationary (by norm_num))
    (isStationary_zero (p := 6))
    (fun _ hφ => isStationary_mem_Ω6 hφ)
    L61_disjoint_frontier

/-! ### 符号の復元 -/

theorem phiAt1_pos_on_L61 : ∀ φ ∈ L61, 0 < phiAt1 φ := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold phiAt1; fun_prop)
    (fun φ hφ => (connectedComponentIn_subset Ω6 _ hφ).1)
    (mem_connectedComponentIn zero_mem_Ω6)
  simp [phiAt1]

theorem phiAtNeg1_pos_on_L61 : ∀ φ ∈ L61, 0 < phiAtNeg1 φ := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold phiAtNeg1; fun_prop)
    (fun φ hφ => (connectedComponentIn_subset Ω6 _ hφ).2.1)
    (mem_connectedComponentIn zero_mem_Ω6)
  simp [phiAtNeg1]

theorem unit_cond6_on_L61 : ∀ φ ∈ L61, 1 - φ 5 ^ 2 > |φ 4 + φ 0 * φ 5| :=
  fun _ hφ => (connectedComponentIn_subset Ω6 _ hφ).2.2.1

theorem cplxCond6_neg_on_L61 : ∀ φ ∈ L61, cplxCond6 φ < 0 := by
  have := sign_fixed_pos_on_preconnected (f := fun φ => -cplxCond6 φ)
    isPreconnected_connectedComponentIn
    (by unfold cplxCond6 A6 B6; fun_prop)
    (fun φ hφ => neg_ne_zero.mpr (connectedComponentIn_subset Ω6 _ hφ).2.2.2)
    (mem_connectedComponentIn zero_mem_Ω6)
    (by simp [cplxCond6, A6, B6])
  intro φ hφ
  have := this φ hφ
  linarith

/-- **`-2A6>|B6|` の直接証明**: `ψ:=phiDown5 φ` に Step-down 補題を適用して `St5 ψ` を得ると
`2A5(ψ)>|B5(ψ)|` が成り立つ。恒等式 `(2A5(ψ)∓B5(ψ))(1-φ_6)(1+φ_6)²=-2A6±B6` (`field_simp`+
`ring` で検証) と `(1-φ_6)(1+φ_6)²>0` (`|φ_6|<1` より) を組み合わせると、符号がそのまま
`-2A6>|B6|` に転写される (`AR5.lean` の必要性の再利用、`L61` の連結性は不要な独立な議論)。 -/
theorem abs_B6_lt_negTwoA6_of_isStationary {φ : Fin 6 → ℝ} (hφ : IsStationary φ) :
    -2 * A6 φ > |B6 φ| := by
  have hψstat : IsStationary (phiDown5 φ) := stepDown_isStationary6 hφ
  have hψSt5 : St5 (phiDown5 φ) := isStationary_imp_St5 hψstat
  have hψabs : 2 * A5 (phiDown5 φ) > |B5 (phiDown5 φ)| := hψSt5.2.2.2.2
  have h5lt1 : |φ 5| < 1 := abs_last_coeff_lt_one (p := 6) (by norm_num) hφ
  have hpos : (0 : ℝ) < 1 - φ 5 := by linarith [(abs_lt.mp h5lt1).2]
  have hpos' : (0 : ℝ) < 1 + φ 5 := by linarith [(abs_lt.mp h5lt1).1]
  have hsqne : (1 : ℝ) - φ 5 ^ 2 ≠ 0 := by nlinarith [hpos, hpos']
  have hψ0 : phiDown5 φ 0 = (φ 0 + φ 5 * φ 4) / (1 - φ 5 ^ 2) := rfl
  have hψ1 : phiDown5 φ 1 = (φ 1 + φ 5 * φ 3) / (1 - φ 5 ^ 2) := rfl
  have hψ2 : phiDown5 φ 2 = (φ 2 + φ 5 * φ 2) / (1 - φ 5 ^ 2) := rfl
  have hψ3 : phiDown5 φ 3 = (φ 3 + φ 5 * φ 1) / (1 - φ 5 ^ 2) := rfl
  have hψ4 : phiDown5 φ 4 = (φ 4 + φ 5 * φ 0) / (1 - φ 5 ^ 2) := rfl
  have hcube_pos : (0 : ℝ) < (1 - φ 5) * (1 + φ 5) ^ 2 := mul_pos hpos (pow_pos hpos' 2)
  have hident1 : (2 * A5 (phiDown5 φ) - B5 (phiDown5 φ)) * ((1 - φ 5) * (1 + φ 5) ^ 2)
      = B6 φ - 2 * A6 φ := by
    simp only [A5, B5, A6, B6, hψ0, hψ1, hψ2, hψ3, hψ4]
    field_simp
    ring
  have hident2 : (2 * A5 (phiDown5 φ) + B5 (phiDown5 φ)) * ((1 - φ 5) * (1 + φ 5) ^ 2)
      = -(2 * A6 φ + B6 φ) := by
    simp only [A5, B5, A6, B6, hψ0, hψ1, hψ2, hψ3, hψ4]
    field_simp
    ring
  have h1 : 0 < 2 * A5 (phiDown5 φ) - B5 (phiDown5 φ) := by linarith [(abs_lt.mp hψabs).2]
  have h2 : 0 < 2 * A5 (phiDown5 φ) + B5 (phiDown5 φ) := by linarith [(abs_lt.mp hψabs).1]
  have hc1 : 0 < B6 φ - 2 * A6 φ := by rw [← hident1]; exact mul_pos h1 hcube_pos
  have hc2 : 0 < -(2 * A6 φ + B6 φ) := by rw [← hident2]; exact mul_pos h2 hcube_pos
  rw [gt_iff_lt, abs_lt]
  constructor <;> linarith [hc1, hc2]

/-- **AR(6) の定常性の必要性**: `IsStationary φ` ならば `St6 φ`。 -/
theorem isStationary_imp_St6 {φ : Fin 6 → ℝ} (hφ : IsStationary φ) : St6 φ := by
  have hφ' : φ ∈ {φ : Fin 6 → ℝ | IsStationary φ} := hφ
  rw [← L61_eq_isStationary] at hφ'
  exact ⟨phiAt1_pos_on_L61 φ hφ', phiAtNeg1_pos_on_L61 φ hφ', unit_cond6_on_L61 φ hφ',
    cplxCond6_neg_on_L61 φ hφ', abs_B6_lt_negTwoA6_of_isStationary hφ⟩

end StTopology
