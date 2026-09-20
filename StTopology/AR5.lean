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

set_option linter.style.header false

/-!
# AR(5) の定常性: 明示的閉形式条件との同値性

`6_kanren.tex`, Section 4.5 の議論を、`AR4.lean`/`AR4Sufficiency.lean` と同型の方針で
形式化する。

## AR(4) との違い: 一般 Step-down 補題

AR(5) の hypothesis (a) (`St(5)⊆Ω5`) では、`cplxCond5 φ ≠ 0` を示す必要があるが、
AR(4) で使った「直接分解」方式 (5次式を`(z²-Xz+1)×(3次式)`に分解する) は、消去後の
多項式が数千項規模に爆発し手作業では不可能なことが判明した (ユーザーとの相談の上、
方針転換)。代わりに、論文本来の Schur–Cohn 再帰 (`φ^{(4)}` への変換) を使うが、
その正しさの核心である「次数下げ変換は定常性を保つ」という事実 (`step-down補題`)
がまだ形式化されていなかったので、ここで一般的な形で証明する。

**証明の方針 (Rouché の定理は使わない)**:
1. `γ_t := gammaT t φ` (`isStationary_scale`, 既存・一般の`p`) は `t∈[0,1]` で常に定常。
2. `ψ(t) := phiDown4 (γ_t)` は連続。`ψ(0) = O_4` は自明に定常なので、
   `isOpen_isStationary` (既存, `p=4`) より、十分小さい `t₀>0` で `ψ(t₀)` は定常 (種)。
3. `ψ(t)` が単位円上に根 `β` を持てば、Schur–Cohn の恒等式 `Q_{γt}(z)=z·Q_{ψ(t)}(z)
   -k·Q_{ψ(t)}^{rev}(z)` (`k=(γt)_4`) と反転恒等式 (単位円上で `Q^{rev}(β)=β^4\overline{Q(β)}`)
   から、`β` は `γ_t(φ)` の根にもなってしまい、`γ_t(φ)` の定常性 (1.) と矛盾する。
   よって `ψ(t)` は `t∈[0,1]` の間ずっと単位円上に根を持たない。
4. 種 (2.) と単位円回避 (3.) を `isStationary_of_path_no_unit_root`
   (`RootPerturbation.lean`, 既存・一般の`p`, 経路を`[t₀,1]`にずらして適用) に渡し、
   `ψ(1) = phiDown4 φ` の定常性を得る。
-/

open Finset StTopology

namespace StTopology

/-! ### Schur–Cohn 変換 (down-step) `ψ = φ^{(4)}`, 次数5→4 -/

/-- `ψ_i = (φ_i + φ_5 φ_{4-i}) / (1-φ_5^2)`, `i=0,1,2,3`。`6_kanren.tex` Section 4.5,
hypothesis (a) の検証部分で使われている式。 -/
noncomputable def phiDown4 (φ : Fin 5 → ℝ) : Fin 4 → ℝ :=
  ![(φ 0 + φ 4 * φ 3) / (1 - φ 4 ^ 2), (φ 1 + φ 4 * φ 2) / (1 - φ 4 ^ 2),
    (φ 2 + φ 4 * φ 1) / (1 - φ 4 ^ 2), (φ 3 + φ 4 * φ 0) / (1 - φ 4 ^ 2)]

/-- 反射係数を `0` から `φ_5` にスケーリングする経路 (Levinson–Durbin の step-up 公式)。
`γ(t)_i = ψ_i - t k ψ_{3-i}` (`i=0,1,2,3`), `γ(t)_4 = tk`, ただし `ψ=phiDown4 φ`, `k=φ_5`。
`γ(0)=(ψ,0)` は自明に定常、`γ(1)=φ`。 -/
noncomputable def phiUpPath4 (φ : Fin 5 → ℝ) (t : ℝ) : Fin 5 → ℝ :=
  ![phiDown4 φ 0 - t * φ 4 * phiDown4 φ 3, phiDown4 φ 1 - t * φ 4 * phiDown4 φ 2,
    phiDown4 φ 2 - t * φ 4 * phiDown4 φ 1, phiDown4 φ 3 - t * φ 4 * phiDown4 φ 0, t * φ 4]

theorem continuous_phiUpPath4 (φ : Fin 5 → ℝ) : Continuous (phiUpPath4 φ) := by
  unfold phiUpPath4
  fun_prop

/-- `Q_ψ(z) := z^4-ψ_0z^3-ψ_1z^2-ψ_2z-ψ_3` の反転が、`‖z‖=1` 上で
`Q_ψ^{rev}(z) = z^4 \overline{Q_ψ(z)}` を満たす (実係数・`z\bar z=1` のみ使う純代数)。 -/
theorem reversal_eq_on_unit_circle4 (ψ0 ψ1 ψ2 ψ3 : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    (1 - (ψ0 : ℂ) * z - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z ^ 3 - (ψ3 : ℂ) * z ^ 4)
      = z ^ 4 * (starRingEnd ℂ)
          (z ^ 4 - (ψ0 : ℂ) * z ^ 3 - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z - (ψ3 : ℂ)) := by
  set w : ℂ := (starRingEnd ℂ) z with hw_def
  have hzw : z * w = 1 := by
    rw [hw_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hw4 : z ^ 4 * w ^ 4 = 1 := by
    rw [show z ^ 4 * w ^ 4 = (z * w) ^ 4 from by ring, hzw]; ring
  have hw3 : z ^ 4 * w ^ 3 = z := by
    rw [show z ^ 4 * w ^ 3 = z * (z * w) ^ 3 from by ring, hzw]; ring
  have hw2 : z ^ 4 * w ^ 2 = z ^ 2 := by
    rw [show z ^ 4 * w ^ 2 = z ^ 2 * (z * w) ^ 2 from by ring, hzw]; ring
  have hw1 : z ^ 4 * w = z ^ 3 := by
    rw [show z ^ 4 * w = z ^ 3 * (z * w) from by ring, hzw]; ring
  have hexpand : (starRingEnd ℂ) (z ^ 4 - (ψ0 : ℂ) * z ^ 3 - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z
        - (ψ3 : ℂ))
      = w ^ 4 - (ψ0 : ℂ) * w ^ 3 - (ψ1 : ℂ) * w ^ 2 - (ψ2 : ℂ) * w - (ψ3 : ℂ) := by
    simp only [map_sub, map_mul, map_pow, Complex.conj_ofReal, ← hw_def]
  rw [hexpand]
  have hexpand2 : z ^ 4 * (w ^ 4 - (ψ0 : ℂ) * w ^ 3 - (ψ1 : ℂ) * w ^ 2 - (ψ2 : ℂ) * w - (ψ3 : ℂ))
      = (z ^ 4 * w ^ 4) - (ψ0 : ℂ) * (z ^ 4 * w ^ 3) - (ψ1 : ℂ) * (z ^ 4 * w ^ 2)
        - (ψ2 : ℂ) * (z ^ 4 * w) - (ψ3 : ℂ) * z ^ 4 := by ring
  rw [hexpand2, hw4, hw3, hw2, hw1]

/-! ### Step-down 補題: 次数下げ変換は定常性を保つ -/

/-- `t` の連続なリトラクション `[0,1]` への値。`ψ` の経路をℝ全域で連続にするために使う
(`isStationary_of_path_no_unit_root` は `Continuous γ` を ℝ 全域で要求するため)。 -/
noncomputable def clampUnit (t : ℝ) : ℝ := min (max t 0) 1

theorem clampUnit_continuous : Continuous clampUnit := by unfold clampUnit; fun_prop

theorem clampUnit_mem (t : ℝ) : clampUnit t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min (le_max_right t 0) zero_le_one, min_le_right _ _⟩

theorem clampUnit_eq_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clampUnit t = t := by
  unfold clampUnit
  rw [max_eq_left ht.1, min_eq_left ht.2]

/-- `gammaT (clampUnit t) φ` の `φ_5`-座標 `k(t) := (clampUnit t)^5・φ_4` は
`|φ_4|<1` のとき常に `|k(t)|<1`。 -/
theorem clampUnit_pow_mul_lt_one {φ4 : ℝ} (h4 : |φ4| < 1) (t : ℝ) :
    |(clampUnit t) ^ 5 * φ4| < 1 := by
  have hmem := clampUnit_mem t
  have h1 : |clampUnit t| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hmem.1], hmem.2⟩
  rw [abs_mul, abs_pow]
  calc |clampUnit t| ^ 5 * |φ4| ≤ 1 ^ 5 * |φ4| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact pow_le_pow_left₀ (abs_nonneg _) h1 5
    _ = |φ4| := by ring
    _ < 1 := h4

/-- **Step-down 補題**: `IsStationary φ` (次数5) ならば `IsStationary (phiDown4 φ)` (次数4)。
Rouché の定理は使わず、`gammaT` スケーリング経路と反転恒等式だけで示す。 -/
theorem stepDown_isStationary {φ : Fin 5 → ℝ} (hφ : IsStationary φ) :
    IsStationary (phiDown4 φ) := by
  have h4lt1 : |φ 4| < 1 := abs_last_coeff_lt_one (p := 5) (by norm_num) hφ
  set ψAux : ℝ → Fin 4 → ℝ := fun t => phiDown4 (gammaT (clampUnit t) φ) with hψAux_def
  -- 分母が常に非零であること
  have hdenom_pos : ∀ t : ℝ, (0 : ℝ) < 1 - (gammaT (clampUnit t) φ 4) ^ 2 := by
    intro t
    have hgt4 : gammaT (clampUnit t) φ 4 = (clampUnit t) ^ 5 * φ 4 := by
      unfold gammaT; norm_num
    rw [hgt4]
    have := clampUnit_pow_mul_lt_one h4lt1 t
    nlinarith [(abs_lt.mp this).1, (abs_lt.mp this).2]
  -- 連続性
  have hψAux_cont : Continuous ψAux := by
    have hgcont : Continuous (fun t : ℝ => gammaT (clampUnit t) φ) :=
      (continuous_radialPath φ).comp clampUnit_continuous
    rw [hψAux_def]
    unfold phiDown4
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
    unfold phiDown4
    funext i; fin_cases i <;> norm_num
  have hstat0 : IsStationary (ψAux 0) := by rw [hψAux_zero]; exact isStationary_zero
  -- 開集合性から、小さい t₀>0 で ψAux t₀ も定常
  have hopen : IsOpen (ψAux ⁻¹' {ψ : Fin 4 → ℝ | IsStationary ψ}) :=
    (isOpen_isStationary (by norm_num : (0:ℕ) < 4)).preimage hψAux_cont
  have hmem0 : (0 : ℝ) ∈ ψAux ⁻¹' {ψ : Fin 4 → ℝ | IsStationary ψ} := hstat0
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
      z ^ 4 ≠ ∑ i : Fin 4, (ψAux t i : ℂ) * z ^ (4 - 1 - (i : ℕ)) := by
    intro t ht z hz hcontra
    have hrt : clampUnit t = t := clampUnit_eq_of_mem ht
    have hγstat : IsStationary (gammaT t φ) := isStationary_scale (by norm_num) hφ ht.1 ht.2
    set k : ℝ := (gammaT t φ) 4 with hk_def
    set ψ0 := phiDown4 (gammaT t φ) 0 with hψ0_def
    set ψ1 := phiDown4 (gammaT t φ) 1 with hψ1_def
    set ψ2 := phiDown4 (gammaT t φ) 2 with hψ2_def
    set ψ3 := phiDown4 (gammaT t φ) 3 with hψ3_def
    have hψAux_t : ψAux t = phiDown4 (gammaT t φ) := by rw [hψAux_def]; dsimp only; rw [hrt]
    rw [hψAux_t] at hcontra
    have hkne : (1 : ℝ) - k ^ 2 ≠ 0 := by
      have := hdenom_pos t
      rw [hrt] at this
      rw [hk_def]; linarith [this]
    have hkC : (k : ℂ) = (gammaT t φ 4 : ℝ) := by rw [hk_def]
    have hdne : (1 : ℝ) - gammaT t φ 4 ^ 2 ≠ 0 := by
      have := hdenom_pos t; rw [hrt] at this; linarith [this]
    have hpd0 : phiDown4 (gammaT t φ) 0
        = (gammaT t φ 0 + gammaT t φ 4 * gammaT t φ 3) / (1 - gammaT t φ 4 ^ 2) := rfl
    have hpd1 : phiDown4 (gammaT t φ) 1
        = (gammaT t φ 1 + gammaT t φ 4 * gammaT t φ 2) / (1 - gammaT t φ 4 ^ 2) := rfl
    have hpd2 : phiDown4 (gammaT t φ) 2
        = (gammaT t φ 2 + gammaT t φ 4 * gammaT t φ 1) / (1 - gammaT t φ 4 ^ 2) := rfl
    have hpd3 : phiDown4 (gammaT t φ) 3
        = (gammaT t φ 3 + gammaT t φ 4 * gammaT t φ 0) / (1 - gammaT t φ 4 ^ 2) := rfl
    have hQψ0 : z ^ 4 - (ψ0 : ℂ) * z ^ 3 - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z - (ψ3 : ℂ) = 0 := by
      simp only [Fin.sum_univ_four] at hcontra
      norm_num at hcontra
      linear_combination hcontra
    have hQrev0 : (1 - (ψ0 : ℂ) * z - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z ^ 3 - (ψ3 : ℂ) * z ^ 4)
        = 0 := by
      rw [reversal_eq_on_unit_circle4 ψ0 ψ1 ψ2 ψ3 z hz, hQψ0]
      simp
    have hUP0 : ψ0 - k * ψ3 = gammaT t φ 0 := by
      rw [hψ0_def, hψ3_def, hk_def, hpd0, hpd3]
      field_simp
      ring
    have hUP1 : ψ1 - k * ψ2 = gammaT t φ 1 := by
      rw [hψ1_def, hψ2_def, hk_def, hpd1, hpd2]
      field_simp
      ring
    have hUP2 : ψ2 - k * ψ1 = gammaT t φ 2 := by
      rw [hψ2_def, hψ1_def, hk_def, hpd2, hpd1]
      field_simp
      ring
    have hUP3 : ψ3 - k * ψ0 = gammaT t φ 3 := by
      rw [hψ3_def, hψ0_def, hk_def, hpd3, hpd0]
      field_simp
      ring
    have hUP0C : (ψ0 : ℂ) - (k : ℂ) * (ψ3 : ℂ) = (gammaT t φ 0 : ℂ) := by exact_mod_cast hUP0
    have hUP1C : (ψ1 : ℂ) - (k : ℂ) * (ψ2 : ℂ) = (gammaT t φ 1 : ℂ) := by exact_mod_cast hUP1
    have hUP2C : (ψ2 : ℂ) - (k : ℂ) * (ψ1 : ℂ) = (gammaT t φ 2 : ℂ) := by exact_mod_cast hUP2
    have hUP3C : (ψ3 : ℂ) - (k : ℂ) * (ψ0 : ℂ) = (gammaT t φ 3 : ℂ) := by exact_mod_cast hUP3
    have htarget : z ^ 5 - (gammaT t φ 0 : ℂ) * z ^ 4 - (gammaT t φ 1 : ℂ) * z ^ 3
        - (gammaT t φ 2 : ℂ) * z ^ 2 - (gammaT t φ 3 : ℂ) * z - (gammaT t φ 4 : ℂ)
        = z * (z ^ 4 - (ψ0 : ℂ) * z ^ 3 - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z - (ψ3 : ℂ))
          - (k : ℂ) * (1 - (ψ0 : ℂ) * z - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z ^ 3
            - (ψ3 : ℂ) * z ^ 4) := by
      rw [← hkC]
      linear_combination z ^ 4 * hUP0C + z ^ 3 * hUP1C + z ^ 2 * hUP2C + z * hUP3C
    rw [hQψ0, hQrev0] at htarget
    simp only [mul_zero, sub_zero] at htarget
    have hzroot : z ^ 5 = (gammaT t φ 0 : ℂ) * z ^ 4 + (gammaT t φ 1 : ℂ) * z ^ 3
        + (gammaT t φ 2 : ℂ) * z ^ 2 + (gammaT t φ 3 : ℂ) * z + (gammaT t φ 4 : ℂ) := by
      linear_combination htarget
    have hzroot' : z ^ 5 = ∑ i : Fin 5, (gammaT t φ i : ℂ) * z ^ (5 - 1 - (i : ℕ)) := by
      simp only [Fin.sum_univ_five]
      norm_num
      linear_combination hzroot
    have := hγstat z hzroot'
    rw [hz] at this
    exact absurd this (lt_irrefl 1)
  -- 種と単位円回避を合わせて `isStationary_of_path_no_unit_root` を適用 (経路を `[t₀,1]` にずらす)
  set γ' : ℝ → Fin 4 → ℝ := fun s => ψAux (t₀ + s * (1 - t₀)) with hγ'_def
  have hγ'cont : Continuous γ' := by
    rw [hγ'_def]
    exact hψAux_cont.comp (by fun_prop)
  have hγ'0 : γ' 0 = ψAux t₀ := by rw [hγ'_def]; norm_num
  have hγ'1 : γ' 1 = ψAux 1 := by rw [hγ'_def]; norm_num
  have hγ'no : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 →
      z ^ 4 ≠ ∑ i : Fin 4, (γ' s i : ℂ) * z ^ (4 - 1 - (i : ℕ)) := by
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
  have hfin : ψAux 1 = phiDown4 φ := by rw [hψAux_def]; dsimp only; rw [h1eq, gammaT_one]
  rwa [hfin] at hresult

/-! ## 必要性: `IsStationary φ → St5 φ`

`AR4.lean` と同型の方針 (`Ω5` の定義 → `L51 := connectedComponentIn Ω5 O5` →
最大連結成分の原理 → `L51 = IsStationary` → connectedness による符号復元)。
`A5`, `B5` は `StationarityRegions.lean` で既に定義済み。 -/

/-- `E := B5² + A5·B5·(φ_5-φ_1) + A5²·(-1-φ_2+φ_4)`。`St5` の4番目の条件の左辺そのもの。 -/
def cplxCond5 (φ : Fin 5 → ℝ) : ℝ :=
  (B5 φ) ^ 2 + (A5 φ) * (B5 φ) * (φ 4 - φ 0) + (A5 φ) ^ 2 * (-1 - φ 1 + φ 3)

/-- `Ω5`: 論文の `Ω = {φ(1)≠0, φ(-1)≠0, |φ_5|<1, E≠0}` にあたる開集合。 -/
def Ω5 : Set (Fin 5 → ℝ) :=
  {φ : Fin 5 → ℝ | phiAt1 φ ≠ 0 ∧ phiAtNeg1 φ ≠ 0 ∧ |φ 4| < 1 ∧ cplxCond5 φ ≠ 0}

/-- 原点 `O_5` は `Ω5` に属する: `φ(1)=1≠0`, `φ(-1)=1≠0`, `|φ_5|=0<1`,
`cplxCond5=(-1)²·(-1)=-1≠0`。 -/
theorem zero_mem_Ω5 : (fun _ : Fin 5 => (0 : ℝ)) ∈ Ω5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [phiAt1, phiAtNeg1, cplxCond5, A5, B5]

/-- `L_{5,1}`: `Ω5` 内で原点 `O_5` を含む最大の連結成分。 -/
def L51 : Set (Fin 5 → ℝ) :=
  connectedComponentIn Ω5 (fun _ : Fin 5 => (0 : ℝ))

/-- AR(5) の逆特性方程式を、`Fin 5` の総和を展開した具体形に書き換える。 -/
theorem root_five_iff {φ : Fin 5 → ℝ} (α : ℂ) :
    (α ^ 5 = ∑ i : Fin 5, (φ i : ℂ) * α ^ (5 - 1 - (i : ℕ)))
      ↔ α ^ 5 = (φ 0 : ℂ) * α ^ 4 + (φ 1 : ℂ) * α ^ 3 + (φ 2 : ℂ) * α ^ 2 + (φ 3 : ℂ) * α
        + (φ 4 : ℂ) := by
  simp only [Fin.sum_univ_five]
  norm_num

/-! ### hypothesis (a) の4つの部品 -/

theorem phiAt1_ne_zero_of_isStationary5 {φ : Fin 5 → ℝ} (hφ : IsStationary φ) :
    phiAt1 φ ≠ 0 := by
  intro h
  simp only [phiAt1, Fin.sum_univ_five] at h
  have hsum : φ 0 + φ 1 + φ 2 + φ 3 + φ 4 = 1 := by linarith
  have hsumC : (φ 0 : ℂ) + (φ 1 : ℂ) + (φ 2 : ℂ) + (φ 3 : ℂ) + (φ 4 : ℂ) = 1 := by
    exact_mod_cast hsum
  have hroot : (1 : ℂ) ^ 5 = ∑ i : Fin 5, (φ i : ℂ) * (1 : ℂ) ^ (5 - 1 - (i : ℕ)) := by
    rw [root_five_iff]
    linear_combination -hsumC
  have hlt := hφ 1 hroot
  simp at hlt

theorem phiAtNeg1_ne_zero_of_isStationary5 {φ : Fin 5 → ℝ} (hφ : IsStationary φ) :
    phiAtNeg1 φ ≠ 0 := by
  intro h
  simp only [phiAtNeg1, Fin.sum_univ_five] at h
  norm_num at h
  have hsum : φ 0 - φ 1 + φ 2 - φ 3 + φ 4 = -1 := by linarith
  have hsumC : (φ 0 : ℂ) - (φ 1 : ℂ) + (φ 2 : ℂ) - (φ 3 : ℂ) + (φ 4 : ℂ) = -1 := by
    exact_mod_cast hsum
  have hroot : (-1 : ℂ) ^ 5 = ∑ i : Fin 5, (φ i : ℂ) * (-1 : ℂ) ^ (5 - 1 - (i : ℕ)) := by
    rw [root_five_iff]
    norm_num
    linear_combination -hsumC
  have hlt := hφ (-1) hroot
  simp at hlt

/-- **hypothesis (a) の核**: `cplxCond5 φ ≠ 0`。Step-down 補題 (`stepDown_isStationary`) で
`ψ:=phiDown4 φ` の定常性を得て、`AR4.isStationary_imp_St4` から `cplxCond4 ψ > 0`
(特に `≠0`) を得る。恒等式 `cplxCond4(ψ)·(1-φ_5)²(1+φ_5)² = -cplxCond5(φ)` (Step 2 の
恒等式の類似, `field_simp`+`ring` で検証) と組み合わせ、`cplxCond5 φ ≠ 0` を結論する。 -/
theorem cplxCond5_ne_zero_of_isStationary {φ : Fin 5 → ℝ} (hφ : IsStationary φ) :
    cplxCond5 φ ≠ 0 := by
  have hψstat : IsStationary (phiDown4 φ) := stepDown_isStationary hφ
  have hψSt4 : St4 (phiDown4 φ) := isStationary_imp_St4 hψstat
  have hcplx4pos : cplxCond4 (phiDown4 φ) > 0 := hψSt4.2.2.1
  have h4lt1 : |φ 4| < 1 := abs_last_coeff_lt_one (p := 5) (by norm_num) hφ
  have hpos : (0 : ℝ) < 1 - φ 4 := by linarith [(abs_lt.mp h4lt1).2]
  have hpos' : (0 : ℝ) < 1 + φ 4 := by linarith [(abs_lt.mp h4lt1).1]
  have hne : (1 : ℝ) - φ 4 ≠ 0 := hpos.ne'
  have hne' : (1 : ℝ) + φ 4 ≠ 0 := hpos'.ne'
  have hsqne : (1 : ℝ) - φ 4 ^ 2 ≠ 0 := by
    intro hc
    apply hne
    have : (1 - φ 4) * (1 + φ 4) = 0 := by nlinarith [hc]
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hne'
  have hψ0 : phiDown4 φ 0 = (φ 0 + φ 4 * φ 3) / (1 - φ 4 ^ 2) := rfl
  have hψ1 : phiDown4 φ 1 = (φ 1 + φ 4 * φ 2) / (1 - φ 4 ^ 2) := rfl
  have hψ2 : phiDown4 φ 2 = (φ 2 + φ 4 * φ 1) / (1 - φ 4 ^ 2) := rfl
  have hψ3 : phiDown4 φ 3 = (φ 3 + φ 4 * φ 0) / (1 - φ 4 ^ 2) := rfl
  have hident : cplxCond4 (phiDown4 φ) * ((1 - φ 4) ^ 2 * (1 + φ 4) ^ 2) = -cplxCond5 φ := by
    simp only [cplxCond4, cplxCond5, A5, B5, hψ0, hψ1, hψ2, hψ3]
    field_simp
    ring
  intro hzero
  rw [hzero, neg_zero] at hident
  have hpossq : (0 : ℝ) < (1 - φ 4) ^ 2 * (1 + φ 4) ^ 2 := by positivity
  nlinarith [hcplx4pos, hident, hpossq]

theorem isStationary_mem_Ω5 {φ : Fin 5 → ℝ} (hφ : IsStationary φ) : φ ∈ Ω5 :=
  ⟨phiAt1_ne_zero_of_isStationary5 hφ, phiAtNeg1_ne_zero_of_isStationary5 hφ,
    abs_last_coeff_lt_one (p := 5) (by norm_num) hφ, cplxCond5_ne_zero_of_isStationary hφ⟩

/-! ### hypothesis (b) の代数的核: 単位円上の非実根 ⟹ `cplxCond5=0`

`z` を単位円上の非実根、`w:=z̄` (`zw=1`) とする。`AR4.lean` の手法 (`w²`倍) を
5次式に適用すると `w²·quintic(z) = z³-φ0z²-φ1z-φ2-φ3w-φ4w² =: ⋆` (3次)。`⋆` とその
`z↔w` 版 `⋆'` の差から2次式 (I''), 和から3次式 (R'') が出て、(I'') を使って (R'') の
3次の項を消去すると1次式 (L): `A5·u=B5` (`u=z+w`) が出る。(I'') と (L) から `u` を
消去すると `cplxCond5=0` が得られる。 -/
theorem cplxCond5_eq_zero_of_unit_root_of_ne {φ : Fin 5 → ℝ} (z : ℂ)
    (hroot : z ^ 5 = (φ 0 : ℂ) * z ^ 4 + (φ 1 : ℂ) * z ^ 3 + (φ 2 : ℂ) * z ^ 2 + (φ 3 : ℂ) * z
      + (φ 4 : ℂ))
    (hnorm : ‖z‖ = 1) (hne : z ≠ (starRingEnd ℂ) z) :
    cplxCond5 φ = 0 := by
  set w : ℂ := (starRingEnd ℂ) z with hw
  have hzw : z * w = 1 := by
    rw [hw, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
  have hwz : w * z = 1 := by rw [mul_comm]; exact hzw
  have hroot0 : z ^ 5 - (φ 0 : ℂ) * z ^ 4 - (φ 1 : ℂ) * z ^ 3 - (φ 2 : ℂ) * z ^ 2 - (φ 3 : ℂ) * z
      - (φ 4 : ℂ) = 0 := by linear_combination hroot
  have hrootw : w ^ 5 = (φ 0 : ℂ) * w ^ 4 + (φ 1 : ℂ) * w ^ 3 + (φ 2 : ℂ) * w ^ 2 + (φ 3 : ℂ) * w
      + (φ 4 : ℂ) := by
    have := congrArg (starRingEnd ℂ) hroot
    simpa [hw, map_add, map_mul, map_pow, Complex.conj_ofReal] using this
  have hrootw0 : w ^ 5 - (φ 0 : ℂ) * w ^ 4 - (φ 1 : ℂ) * w ^ 3 - (φ 2 : ℂ) * w ^ 2 - (φ 3 : ℂ) * w
      - (φ 4 : ℂ) = 0 := by linear_combination hrootw
  -- ⋆ : w²·quintic(z) の還元
  have hstar : z ^ 3 - (φ 0 : ℂ) * z ^ 2 - (φ 1 : ℂ) * z - (φ 2 : ℂ) - (φ 3 : ℂ) * w
      - (φ 4 : ℂ) * w ^ 2 = 0 := by
    have h5 : w ^ 2 * z ^ 5 = z ^ 3 := by
      rw [show w ^ 2 * z ^ 5 = z ^ 3 * (z * w) ^ 2 from by ring, hzw]; ring
    have h4 : w ^ 2 * z ^ 4 = z ^ 2 := by
      rw [show w ^ 2 * z ^ 4 = z ^ 2 * (z * w) ^ 2 from by ring, hzw]; ring
    have h3 : w ^ 2 * z ^ 3 = z := by
      rw [show w ^ 2 * z ^ 3 = z * (z * w) ^ 2 from by ring, hzw]; ring
    have h2 : w ^ 2 * z ^ 2 = 1 := by
      rw [show w ^ 2 * z ^ 2 = (z * w) ^ 2 from by ring, hzw]; ring
    have h1 : w ^ 2 * z = w := by
      rw [show w ^ 2 * z = w * (z * w) from by ring, hzw]; ring
    have hexpand : w ^ 2 * (z ^ 5 - (φ 0 : ℂ) * z ^ 4 - (φ 1 : ℂ) * z ^ 3 - (φ 2 : ℂ) * z ^ 2
          - (φ 3 : ℂ) * z - (φ 4 : ℂ))
        = (w ^ 2 * z ^ 5) - (φ 0 : ℂ) * (w ^ 2 * z ^ 4) - (φ 1 : ℂ) * (w ^ 2 * z ^ 3)
          - (φ 2 : ℂ) * (w ^ 2 * z ^ 2) - (φ 3 : ℂ) * (w ^ 2 * z) - (φ 4 : ℂ) * w ^ 2 := by ring
    rw [h5, h4, h3, h2, h1] at hexpand
    rw [hroot0, mul_zero] at hexpand
    linear_combination -hexpand
  -- ⋆' : z²·quintic(w) の還元 (z↔w を入れ替えただけ)
  have hstar' : w ^ 3 - (φ 0 : ℂ) * w ^ 2 - (φ 1 : ℂ) * w - (φ 2 : ℂ) - (φ 3 : ℂ) * z
      - (φ 4 : ℂ) * z ^ 2 = 0 := by
    have h5 : z ^ 2 * w ^ 5 = w ^ 3 := by
      rw [show z ^ 2 * w ^ 5 = w ^ 3 * (w * z) ^ 2 from by ring, hwz]; ring
    have h4 : z ^ 2 * w ^ 4 = w ^ 2 := by
      rw [show z ^ 2 * w ^ 4 = w ^ 2 * (w * z) ^ 2 from by ring, hwz]; ring
    have h3 : z ^ 2 * w ^ 3 = w := by
      rw [show z ^ 2 * w ^ 3 = w * (w * z) ^ 2 from by ring, hwz]; ring
    have h2 : z ^ 2 * w ^ 2 = 1 := by
      rw [show z ^ 2 * w ^ 2 = (w * z) ^ 2 from by ring, hwz]; ring
    have h1 : z ^ 2 * w = z := by
      rw [show z ^ 2 * w = z * (w * z) from by ring, hwz]; ring
    have hexpand : z ^ 2 * (w ^ 5 - (φ 0 : ℂ) * w ^ 4 - (φ 1 : ℂ) * w ^ 3 - (φ 2 : ℂ) * w ^ 2
          - (φ 3 : ℂ) * w - (φ 4 : ℂ))
        = (z ^ 2 * w ^ 5) - (φ 0 : ℂ) * (z ^ 2 * w ^ 4) - (φ 1 : ℂ) * (z ^ 2 * w ^ 3)
          - (φ 2 : ℂ) * (z ^ 2 * w ^ 2) - (φ 3 : ℂ) * (z ^ 2 * w) - (φ 4 : ℂ) * z ^ 2 := by ring
    rw [h5, h4, h3, h2, h1] at hexpand
    rw [hrootw0, mul_zero] at hexpand
    linear_combination -hexpand
  have hne' : z - w ≠ 0 := sub_ne_zero.mpr hne
  -- (I'')
  have hII : (z + w) ^ 2 - 1 - (φ 0 : ℂ) * (z + w) - (φ 1 : ℂ) + (φ 3 : ℂ) + (φ 4 : ℂ) * (z + w)
      = 0 := by
    have hsub : (z - w) * ((z + w) ^ 2 - 1 - (φ 0 : ℂ) * (z + w) - (φ 1 : ℂ) + (φ 3 : ℂ)
        + (φ 4 : ℂ) * (z + w)) = 0 := by
      linear_combination hstar - hstar' + (z - w) * hzw
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd h hne'
    · exact h
  -- (R'')
  have hRR : (z + w) ^ 3 - 3 * (z + w) - (φ 0 : ℂ) * ((z + w) ^ 2 - 2) - (φ 1 : ℂ) * (z + w)
      - 2 * (φ 2 : ℂ) - (φ 3 : ℂ) * (z + w) - (φ 4 : ℂ) * ((z + w) ^ 2 - 2) = 0 := by
    linear_combination hstar + hstar' + (3 * z + 3 * w - 2 * (φ 0 : ℂ) - 2 * (φ 4 : ℂ)) * hzw
  -- u := z+w (実数)
  set u : ℝ := 2 * z.re with hu_def
  have huC : (u : ℂ) = z + w := by
    rw [hu_def, hw]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.conj_re, Complex.add_im, Complex.conj_im] <;> ring
  have hIIu : u ^ 2 - (φ 0 - φ 4) * u + (φ 3 - φ 1 - 1) = 0 := by
    have hIIC : (u : ℂ) ^ 2 - ((φ 0 : ℂ) - (φ 4 : ℂ)) * (u : ℂ) + ((φ 3 : ℂ) - (φ 1 : ℂ) - 1)
        = 0 := by rw [huC]; linear_combination hII
    exact_mod_cast hIIC
  have hRRu : u ^ 3 - (φ 0 + φ 4) * u ^ 2 - (3 + φ 1 + φ 3) * u + 2 * (φ 0 + φ 4 - φ 2) = 0 := by
    have hRRC : (u : ℂ) ^ 3 - ((φ 0 : ℂ) + (φ 4 : ℂ)) * (u : ℂ) ^ 2
        - (3 + (φ 1 : ℂ) + (φ 3 : ℂ)) * (u : ℂ) + 2 * ((φ 0 : ℂ) + (φ 4 : ℂ) - (φ 2 : ℂ))
        = 0 := by rw [huC]; linear_combination hRR
    exact_mod_cast hRRC
  -- (L): A5·u = B5
  have hL : (A5 φ) * u = B5 φ := by
    unfold A5 B5
    linear_combination (-1 / 2 : ℝ) * hRRu + ((u - 2 * φ 4) / 2) * hIIu
  -- u を消去して cplxCond5 = 0
  change (B5 φ) ^ 2 + (A5 φ) * (B5 φ) * (φ 4 - φ 0) + (A5 φ) ^ 2 * (-1 - φ 1 + φ 3) = 0
  linear_combination (A5 φ) ^ 2 * hIIu + ((φ 0 - φ 4) * (A5 φ) - (A5 φ) * u - B5 φ) * hL

/-- 単位円上の根を持つ `φ` は `Ω5` に属さない (hypothesis (b) の代数部分)。 -/
theorem not_mem_Ω5_of_unit_root {φ : Fin 5 → ℝ} (z : ℂ)
    (hroot : z ^ 5 = (φ 0 : ℂ) * z ^ 4 + (φ 1 : ℂ) * z ^ 3 + (φ 2 : ℂ) * z ^ 2 + (φ 3 : ℂ) * z
      + (φ 4 : ℂ))
    (hnorm : ‖z‖ = 1) :
    φ ∉ Ω5 := by
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
      simp only [phiAt1, Fin.sum_univ_five]
      have : (1 : ℂ) = (φ 0 : ℂ) + (φ 1 : ℂ) + (φ 2 : ℂ) + (φ 3 : ℂ) + (φ 4 : ℂ) := by
        linear_combination hroot
      have hr : (1 : ℝ) = φ 0 + φ 1 + φ 2 + φ 3 + φ 4 := by exact_mod_cast this
      linarith
    · have hz1 : z = -1 := by apply Complex.ext <;> simp [hn, him]
      rw [hz1] at hroot
      apply hm1
      simp only [phiAtNeg1, Fin.sum_univ_five]
      norm_num
      have : (-1 : ℂ) = (φ 0 : ℂ) - (φ 1 : ℂ) + (φ 2 : ℂ) - (φ 3 : ℂ) + (φ 4 : ℂ) := by
        linear_combination hroot
      have hr : (-1 : ℝ) = φ 0 - φ 1 + φ 2 - φ 3 + φ 4 := by exact_mod_cast this
      linarith
  · exact hc (cplxCond5_eq_zero_of_unit_root_of_ne z hroot hnorm hreal)

/-- `Ω5` は開集合。 -/
theorem isOpen_Ω5 : IsOpen Ω5 := by
  have h1 : Continuous (fun φ : Fin 5 → ℝ => phiAt1 φ) := by unfold phiAt1; fun_prop
  have h2 : Continuous (fun φ : Fin 5 → ℝ => phiAtNeg1 φ) := by unfold phiAtNeg1; fun_prop
  have h3 : Continuous (fun φ : Fin 5 → ℝ => φ 4) := by fun_prop
  have h4 : Continuous (fun φ : Fin 5 → ℝ => cplxCond5 φ) := by
    unfold cplxCond5 A5 B5; fun_prop
  exact (isOpen_ne_fun h1 continuous_const).inter
    ((isOpen_ne_fun h2 continuous_const).inter
      ((isOpen_lt (continuous_abs.comp h3) continuous_const).inter
        (isOpen_ne_fun h4 continuous_const)))

/-- hypothesis (b): `L51` は `St(5)` の境界と交わらない。 -/
theorem L51_disjoint_frontier :
    L51 ∩ frontier {φ : Fin 5 → ℝ | IsStationary φ} = ∅ := by
  ext φ
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hφL51, hφfrontier⟩
  obtain ⟨z, hznorm, hzeq⟩ :=
    frontier_isStationary_subset_hasUnitRoot (p := 5) (by norm_num) hφfrontier
  rw [root_five_iff] at hzeq
  exact not_mem_Ω5_of_unit_root z hzeq hznorm (connectedComponentIn_subset Ω5 _ hφL51)

/-- **`L51 = St(5)`**: 最大連結成分の原理を AR(5) に適用した結果。 -/
theorem L51_eq_isStationary : L51 = {φ : Fin 5 → ℝ | IsStationary φ} :=
  maximal_component_principle Ω5 {φ : Fin 5 → ℝ | IsStationary φ}
    (fun _ : Fin 5 => (0 : ℝ))
    zero_mem_Ω5
    (isOpen_isStationary (by norm_num))
    (isPreconnected_isStationary (by norm_num))
    (isStationary_zero (p := 5))
    (fun _ hφ => isStationary_mem_Ω5 hφ)
    L51_disjoint_frontier

/-! ### 符号の復元 -/

theorem phiAt1_pos_on_L51 : ∀ φ ∈ L51, 0 < phiAt1 φ := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold phiAt1; fun_prop)
    (fun φ hφ => (connectedComponentIn_subset Ω5 _ hφ).1)
    (mem_connectedComponentIn zero_mem_Ω5)
  simp [phiAt1]

theorem phiAtNeg1_pos_on_L51 : ∀ φ ∈ L51, 0 < phiAtNeg1 φ := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold phiAtNeg1; fun_prop)
    (fun φ hφ => (connectedComponentIn_subset Ω5 _ hφ).2.1)
    (mem_connectedComponentIn zero_mem_Ω5)
  simp [phiAtNeg1]

theorem abs_phi4_lt_one_on_L51 : ∀ φ ∈ L51, |φ 4| < 1 :=
  fun _ hφ => (connectedComponentIn_subset Ω5 _ hφ).2.2.1

theorem cplxCond5_neg_on_L51 : ∀ φ ∈ L51, cplxCond5 φ < 0 := by
  have := sign_fixed_pos_on_preconnected (f := fun φ => -cplxCond5 φ)
    isPreconnected_connectedComponentIn
    (by unfold cplxCond5 A5 B5; fun_prop)
    (fun φ hφ => neg_ne_zero.mpr (connectedComponentIn_subset Ω5 _ hφ).2.2.2)
    (mem_connectedComponentIn zero_mem_Ω5)
    (by simp [cplxCond5, A5, B5])
  intro φ hφ
  have := this φ hφ
  linarith

theorem A5_ne_zero_on_L51 : ∀ φ ∈ L51, A5 φ ≠ 0 := by
  intro φ hφ hzero
  have hEeq : cplxCond5 φ = (B5 φ) ^ 2 := by
    simp only [cplxCond5, hzero]; ring
  have hEneg := cplxCond5_neg_on_L51 φ hφ
  nlinarith [sq_nonneg (B5 φ), hEeq, hEneg]

theorem A5_pos_on_L51 : ∀ φ ∈ L51, 0 < A5 φ := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold A5; fun_prop) A5_ne_zero_on_L51
    (mem_connectedComponentIn zero_mem_Ω5)
  simp [A5]

/-- `B5=2A5` なら `cplxCond5·(1-φ_5) = A5²·φ(1)`。`6_kanren.tex` line 271-273 の恒等式
(`field_simp`/`ring` 直前に `φ_2` を消去する代数、`nlinarith`+代入で検証)。 -/
theorem B5_ne_twoA5_on_L51 : ∀ φ ∈ L51, B5 φ ≠ 2 * A5 φ := by
  intro φ hφ heq
  have hident : cplxCond5 φ * (1 - φ 4) = (A5 φ) ^ 2 * phiAt1 φ := by
    have h2 : φ 2 = φ 0 - φ 1 * φ 4 + φ 3 * φ 4 - 2 * A5 φ := by
      simp only [B5] at heq; linarith [heq]
    simp only [cplxCond5, A5, B5, phiAt1, Fin.sum_univ_five, h2]
    ring
  have hApos := A5_pos_on_L51 φ hφ
  have h1pos := phiAt1_pos_on_L51 φ hφ
  have hEneg := cplxCond5_neg_on_L51 φ hφ
  have h4lt1 := abs_phi4_lt_one_on_L51 φ hφ
  have h4pos : (0:ℝ) < 1 - φ 4 := by linarith [(abs_lt.mp h4lt1).2]
  nlinarith [hident, mul_pos (mul_pos hApos hApos) h1pos, mul_neg_of_neg_of_pos hEneg h4pos]

/-- `B5=-2A5` なら `cplxCond5·(1+φ_5) = A5²·φ(-1)`。同上の `φ(-1)` 版。 -/
theorem B5_ne_negTwoA5_on_L51 : ∀ φ ∈ L51, B5 φ ≠ -(2 * A5 φ) := by
  intro φ hφ heq
  have hident : cplxCond5 φ * (1 + φ 4) = (A5 φ) ^ 2 * phiAtNeg1 φ := by
    have h2 : φ 2 = φ 0 - φ 1 * φ 4 + φ 3 * φ 4 + 2 * A5 φ := by
      simp only [B5] at heq; linarith [heq]
    simp only [cplxCond5, A5, B5, phiAtNeg1, Fin.sum_univ_five, h2]
    norm_num
    ring
  have hApos := A5_pos_on_L51 φ hφ
  have hm1pos := phiAtNeg1_pos_on_L51 φ hφ
  have hEneg := cplxCond5_neg_on_L51 φ hφ
  have h4lt1 := abs_phi4_lt_one_on_L51 φ hφ
  have h4pos : (0:ℝ) < 1 + φ 4 := by linarith [(abs_lt.mp h4lt1).1]
  nlinarith [hident, mul_pos (mul_pos hApos hApos) hm1pos, mul_neg_of_neg_of_pos hEneg h4pos]

theorem B5sq_ne_four_A5sq_on_L51 : ∀ φ ∈ L51, (2 * A5 φ) ^ 2 - (B5 φ) ^ 2 ≠ 0 := by
  intro φ hφ heq
  have hfact : (2 * A5 φ - B5 φ) * (2 * A5 φ + B5 φ) = 0 := by linear_combination heq
  rcases mul_eq_zero.mp hfact with h | h
  · exact B5_ne_twoA5_on_L51 φ hφ (by linarith)
  · exact B5_ne_negTwoA5_on_L51 φ hφ (by linarith)

theorem B5sq_lt_four_A5sq_on_L51 : ∀ φ ∈ L51, 0 < (2 * A5 φ) ^ 2 - (B5 φ) ^ 2 := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold A5 B5; fun_prop) B5sq_ne_four_A5sq_on_L51
    (mem_connectedComponentIn zero_mem_Ω5)
  simp [A5, B5]

theorem abs_B5_lt_two_A5_on_L51 : ∀ φ ∈ L51, 2 * A5 φ > |B5 φ| := by
  intro φ hφ
  have hApos := A5_pos_on_L51 φ hφ
  have h := B5sq_lt_four_A5sq_on_L51 φ hφ
  have hsq : (B5 φ) ^ 2 < (2 * A5 φ) ^ 2 := by linarith
  exact abs_lt_of_sq_lt_sq hsq (by linarith)

/-- **AR(5) の定常性の必要性**: `IsStationary φ` ならば `St5 φ`。 -/
theorem isStationary_imp_St5 {φ : Fin 5 → ℝ} (hφ : IsStationary φ) : St5 φ := by
  have hφ' : φ ∈ {φ : Fin 5 → ℝ | IsStationary φ} := hφ
  rw [← L51_eq_isStationary] at hφ'
  exact ⟨phiAt1_pos_on_L51 φ hφ', phiAtNeg1_pos_on_L51 φ hφ', abs_phi4_lt_one_on_L51 φ hφ',
    cplxCond5_neg_on_L51 φ hφ', abs_B5_lt_two_A5_on_L51 φ hφ'⟩

end StTopology
