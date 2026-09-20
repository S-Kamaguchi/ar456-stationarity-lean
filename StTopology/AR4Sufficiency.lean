import Mathlib
import StTopology.StationarityRegions
import StTopology.AR3
import StTopology.AR4
import StTopology.RootPerturbation
import StTopology.StOpen

set_option linter.style.header false

/-!
# AR(4) の定常性の十分性: `St4 φ → IsStationary φ`

`AR4.lean` の必要性 (`IsStationary φ → St4 φ`) とは異なる方針で証明する
(`AR3.lean` と同型の重み付きスケーリング `γ4(φ,t)=(tφ_1,…,t⁴φ_4)` は、境界の
極値点 `(4,-6,4,-1)` で `St4` の4条件すべてが同時にタイトになるため、
Bernstein 係数の非負性を直接 `nlinarith` で示すのが極めて難しいことが判明した)。

## 方針 (Schur–Cohn 再帰 + 「単位円上に根を持たない経路」)

論文 Remark (`rem:phi4-automatic`) の議論を「逆方向」に使う:

1. **Step 3 の議論**を使い、`St4` の4条件だけ (定常性を仮定せずに) から `|φ_4|<1` を導く
   (`abs_phi3_lt_one_of_St4`)。
2. **Step 2 の恒等式**を使い、Schur–Cohn 変換 `ψ := φ^{(3)}` が `St3` を満たすことを示す
   (`field_simp`+`ring` による純代数)。
3. 既に証明済みの `AR3.St3_imp_isStationary` で `ψ` の定常性を得る。
4. 反射係数を `0→φ_4` にスケーリングする経路 `γ(t)` (Levinson–Durbin の
   step-up 公式、`γ(0)=(ψ,0)` は自明に定常、`γ(1)=φ`) を構成する。
5. この経路が `t∈[0,1]` の間ずっと単位円上に根を持たないことを、
   「反転多項式は単位円上でノルムを保つ」という初等的な等式と `|tφ_4|<1` だけで示す
   (`RootPerturbation.lean` の `isStationary_of_path_no_unit_root` を適用)。

Rouché の定理そのものは使わない: 使うのは (i) 反転多項式の単位円上でのノルム保存
(純代数)、(ii) `RootPerturbation.lean` に既にある `exists_root_near` から作った
「単位円上に根を持たない経路は定常性を保つ」という一般補題のみ。
-/

open Finset StTopology

namespace StTopology

/-! ### Step 3: `St4` の4条件だけから `|φ_4|<1` を導く -/

/-- 論文 Remark `rem:phi4-automatic` の Step 3 の議論そのもの。
`St4` の (a) `φ(1)>0∧φ(-1)>0` (まとめると `1-φ_2-φ_4>|φ_1+φ_3|`)、(c) `cplxCond4>0`、
(d) `2(1+φ_4)>|φ_1-φ_3|` の3条件だけから (定常性は一切仮定せずに) `|φ_4|<1` が従う。 -/
theorem abs_phi3_lt_one_of_ineqs {φ0 φ1 φ2 φ3 : ℝ}
    (ha : 1 - φ1 - φ3 > |φ0 + φ2|)
    (hc : (φ2 + φ0 * φ3) * (φ0 - φ2) + (1 + φ3) ^ 2 * (1 + φ1 - φ3) > 0)
    (hd : 2 * (1 + φ3) > |φ0 - φ2|) :
    |φ3| < 1 := by
  rw [abs_lt]
  constructor
  · by_contra h
    push Not at h
    have habs : (0 : ℝ) ≤ |φ0 - φ2| := abs_nonneg _
    nlinarith [hd, habs]
  · by_contra h
    push Not at h
    set s : ℝ := φ0 + φ2 with hs_def
    set d : ℝ := φ2 - φ0 with hd_def
    have hdeq : φ0 - φ2 = -d := by rw [hd_def]; ring
    have hrhopos : (0 : ℝ) < 1 + φ3 := by linarith
    have hkappa : (0 : ℝ) ≤ φ3 - 1 := by linarith
    have hsabs : (0 : ℝ) ≤ abs s := abs_nonneg _
    have hdabs : (0 : ℝ) ≤ abs d := abs_nonneg _
    have hsle : s ≤ abs s := le_abs_self s
    have hsge : -abs s ≤ s := neg_abs_le s
    have hdle : d ≤ abs d := le_abs_self d
    have hdge : -abs d ≤ d := neg_abs_le d
    have haa : φ3 - 1 - φ1 > 2 * (φ3 - 1) + abs s := by linarith [ha]
    have hprodpos : (φ2 + φ0 * φ3) * (-d) > 0 := by
      rw [← hdeq]
      nlinarith [hc, sq_nonneg (1 + φ3), haa, hsabs, h]
    have hprodneg : (φ2 + φ0 * φ3) * d < 0 := by linarith [hprodpos]
    have habsmul : abs ((φ2 + φ0 * φ3) * d) = abs (φ2 + φ0 * φ3) * abs d := abs_mul _ _
    have habsval : abs ((φ2 + φ0 * φ3) * d) = -((φ2 + φ0 * φ3) * d) := abs_of_neg hprodneg
    have hprodeq : (φ2 + φ0 * φ3) * d = -(abs (φ2 + φ0 * φ3) * abs d) := by
      linarith [habsmul, habsval]
    have hckey : abs (φ2 + φ0 * φ3) * abs d > (1 + φ3) ^ 2 * (φ3 - 1 - φ1) := by
      nlinarith [hc, hprodeq, hdeq]
    have hident : φ2 + φ0 * φ3 = (s * (1 + φ3) - d * (φ3 - 1)) / 2 := by
      rw [hs_def, hd_def]; ring
    have hbound : abs (φ2 + φ0 * φ3) ≤ (abs s * (1 + φ3) + abs d * (φ3 - 1)) / 2 := by
      rw [hident, abs_le]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_right hsge hrhopos.le,
          mul_le_mul_of_nonneg_right hdle hkappa]
      · nlinarith [mul_le_mul_of_nonneg_right hsle hrhopos.le,
          mul_le_mul_of_nonneg_right hdge hkappa]
    have hd2 : abs d < 2 * (1 + φ3) := by
      rw [hd_def, show φ2 - φ0 = -(φ0 - φ2) from by ring, abs_neg]; exact hd
    have hrhosqpos : (0 : ℝ) < (1 + φ3) ^ 2 := by positivity
    have hstep3 : (1 + φ3) ^ 2 * (2 * (φ3 - 1) + abs s) < (1 + φ3) ^ 2 * (φ3 - 1 - φ1) :=
      mul_lt_mul_of_pos_left haa hrhosqpos
    have hstep1 : abs (φ2 + φ0 * φ3) * abs d ≤ (abs s * (1 + φ3) + abs d * (φ3 - 1)) / 2 * abs d :=
      mul_le_mul_of_nonneg_right hbound hdabs
    have hchain : (1 + φ3) ^ 2 * (2 * (φ3 - 1) + abs s)
        < (abs s * (1 + φ3) + abs d * (φ3 - 1)) / 2 * abs d := by
      linarith [hstep3, hckey, hstep1]
    have hfactor_nonneg : (0 : ℝ) ≤
        (2 * (1 + φ3) - abs d) * (abs s * (1 + φ3) + (φ3 - 1) * (abs d + 2 * (1 + φ3))) :=
      mul_nonneg (by linarith [hd2]) (by nlinarith [hsabs, hrhopos, hkappa, hdabs])
    nlinarith [hchain, hfactor_nonneg]

/-- `St4 φ` から (定常性を仮定せずに) `|φ_4|<1` が従う。 -/
theorem abs_phi3_lt_one_of_St4 {φ : Fin 4 → ℝ} (hSt4 : St4 φ) : |φ 3| < 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hSt4
  have ha : 1 - φ 1 - φ 3 > |φ 0 + φ 2| := by
    have h1' : phiAt1 φ > 0 := h1
    have h2' : phiAtNeg1 φ > 0 := h2
    simp only [phiAt1, phiAtNeg1, Fin.sum_univ_four] at h1' h2'
    norm_num at h2'
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  exact abs_phi3_lt_one_of_ineqs ha h3 h4

/-! ### Step 2: Schur–Cohn 変換 `ψ = φ^{(3)}` が `St3` を満たすこと -/

/-- Schur–Cohn 変換 (down-step) `ψ = φ^{(3)}`。`6_kanren.tex` Remark, Step 2 の式。 -/
noncomputable def phiDown3 (φ : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![(φ 0 + φ 3 * φ 2) / (1 - φ 3 ^ 2), φ 1 / (1 - φ 3),
    (φ 2 + φ 3 * φ 0) / (1 - φ 3 ^ 2)]

theorem St3_phiDown3_of_St4 {φ : Fin 4 → ℝ} (hSt4 : St4 φ) : St3 (phiDown3 φ) := by
  have h3lt1 : |φ 3| < 1 := abs_phi3_lt_one_of_St4 hSt4
  obtain ⟨h1, h2, h3, h4⟩ := hSt4
  have hpos : (0 : ℝ) < 1 - φ 3 := by linarith [(abs_lt.mp h3lt1).2]
  have hpos' : (0 : ℝ) < 1 + φ 3 := by linarith [(abs_lt.mp h3lt1).1]
  have hne : (1 : ℝ) - φ 3 ≠ 0 := hpos.ne'
  have hne' : (1 : ℝ) + φ 3 ≠ 0 := hpos'.ne'
  have hsqne : (1 : ℝ) - φ 3 ^ 2 ≠ 0 := by
    intro hc
    apply hne
    have : (1 - φ 3) * (1 + φ 3) = 0 := by nlinarith [hc]
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hne'
  -- 座標を具体形に展開しておく
  have hψ0 : phiDown3 φ 0 = (φ 0 + φ 3 * φ 2) / (1 - φ 3 ^ 2) := rfl
  have hψ1 : phiDown3 φ 1 = φ 1 / (1 - φ 3) := rfl
  have hψ2 : phiDown3 φ 2 = (φ 2 + φ 3 * φ 0) / (1 - φ 3 ^ 2) := rfl
  -- Step 2 の4つの恒等式
  have hidPhi1 : phiAt1 (phiDown3 φ) * (1 - φ 3) = phiAt1 φ := by
    simp only [phiAt1, Fin.sum_univ_three, Fin.sum_univ_four, hψ0, hψ1, hψ2]
    field_simp
    ring
  have hidPhiNeg1 : phiAtNeg1 (phiDown3 φ) * (1 - φ 3) = phiAtNeg1 φ := by
    simp only [phiAtNeg1, Fin.sum_univ_three, Fin.sum_univ_four, hψ0, hψ1, hψ2]
    norm_num
    field_simp
    ring
  have hidCplx : (phiDown3 φ 2 ^ 2 - phiDown3 φ 0 * phiDown3 φ 2 - phiDown3 φ 1 - 1)
      * ((1 - φ 3) * (1 + φ 3) ^ 2)
      = -((φ 2 + φ 0 * φ 3) * (φ 0 - φ 2) + (1 + φ 3) ^ 2 * (1 + φ 1 - φ 3)) := by
    simp only [hψ0, hψ1, hψ2]
    field_simp
    ring
  have hidDiff : (phiDown3 φ 0 - phiDown3 φ 2) * (1 + φ 3) = φ 0 - φ 2 := by
    simp only [hψ0, hψ2]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hidPhi1
    nlinarith [h1, hpos, this]
  · have := hidPhiNeg1
    nlinarith [h2, hpos, this]
  · have hcube : (0:ℝ) < (1 - φ 3) * (1 + φ 3) ^ 2 := by positivity
    nlinarith [hidCplx, h3, hcube]
  · have h4' : |φ 0 - φ 2| < 2 * (1 + φ 3) := h4
    have hval : |phiDown3 φ 0 - phiDown3 φ 2| * (1 + φ 3) = |φ 0 - φ 2| := by
      rw [← hidDiff, abs_mul, abs_of_pos hpos']
    have hlt : |phiDown3 φ 0 - phiDown3 φ 2| * (1 + φ 3) < 2 * (1 + φ 3) := by
      rw [hval]; exact h4'
    by_contra hge
    push Not at hge
    nlinarith [mul_le_mul_of_nonneg_right hge hpos'.le, hlt]

/-! ### `(ψ,0)` は定常 (次数を1つ上げて0を追加しても定常性は保たれる) -/

theorem isStationary_pad0_of_isStationary3 {ψ0 ψ1 ψ2 : ℝ}
    (hψ : IsStationary (![ψ0, ψ1, ψ2] : Fin 3 → ℝ)) :
    IsStationary (![ψ0, ψ1, ψ2, 0] : Fin 4 → ℝ) := by
  intro α hα
  simp [Fin.sum_univ_four] at hα
  have hfact : α * (α ^ 3 - (ψ0 : ℂ) * α ^ 2 - (ψ1 : ℂ) * α - (ψ2 : ℂ)) = 0 := by
    linear_combination hα
  rcases mul_eq_zero.mp hfact with h0 | hcubic
  · rw [h0]; simp
  · have hroot : α ^ 3 = ∑ i : Fin 3, (![ψ0, ψ1, ψ2] i : ℂ) * α ^ (3 - 1 - (i : ℕ)) := by
      simp [Fin.sum_univ_three]
      linear_combination hcubic
    exact hψ α hroot

/-! ### Levinson–Durbin の step-up 経路 -/

/-- 反射係数を `0` から `φ_4` にスケーリングする経路 (Levinson–Durbin の step-up 公式)。
`γ(0)=(ψ,0)`, `γ(1)=φ` となる (`phiUpPath_zero`, `phiUpPath_one_of_St4`)。 -/
noncomputable def phiUpPath (φ : Fin 4 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![phiDown3 φ 0 - t * φ 3 * phiDown3 φ 2, phiDown3 φ 1 * (1 - t * φ 3),
    phiDown3 φ 2 - t * φ 3 * phiDown3 φ 0, t * φ 3]

theorem continuous_phiUpPath (φ : Fin 4 → ℝ) : Continuous (phiUpPath φ) := by
  unfold phiUpPath
  fun_prop

theorem phiUpPath_zero (φ : Fin 4 → ℝ) :
    phiUpPath φ 0 = ![phiDown3 φ 0, phiDown3 φ 1, phiDown3 φ 2, 0] := by
  funext i
  fin_cases i <;> simp [phiUpPath]

theorem phiUpPath_one_of_St4 {φ : Fin 4 → ℝ} (hSt4 : St4 φ) : phiUpPath φ 1 = φ := by
  have h3lt1 : |φ 3| < 1 := abs_phi3_lt_one_of_St4 hSt4
  have hpos : (0 : ℝ) < 1 - φ 3 := by linarith [(abs_lt.mp h3lt1).2]
  have hpos' : (0 : ℝ) < 1 + φ 3 := by linarith [(abs_lt.mp h3lt1).1]
  have hsqpos : (0 : ℝ) < 1 - φ 3 ^ 2 := by nlinarith [hpos, hpos']
  have hsqne : (1 : ℝ) - φ 3 ^ 2 ≠ 0 := hsqpos.ne'
  have hψ0 : phiDown3 φ 0 = (φ 0 + φ 3 * φ 2) / (1 - φ 3 ^ 2) := rfl
  have hψ1 : phiDown3 φ 1 = φ 1 / (1 - φ 3) := rfl
  have hψ2 : phiDown3 φ 2 = (φ 2 + φ 3 * φ 0) / (1 - φ 3 ^ 2) := rfl
  funext i
  fin_cases i <;> simp [phiUpPath, hψ0, hψ1, hψ2] <;> field_simp <;> ring

/-! ### 経路は単位円上に根を持たない -/

/-- `Q_ψ(z) := z^3-ψ_0z^2-ψ_1z-ψ_2` の反転 `Q_ψ^{rev}(z) := 1-ψ_0z-ψ_1z^2-ψ_2z^3` は、
`‖z‖=1` 上で `Q_ψ^{rev}(z) = z^3 \overline{Q_ψ(z)}` を満たす (実係数・`z\bar z=1` のみ使う純代数)。 -/
theorem reversal_eq_on_unit_circle (ψ0 ψ1 ψ2 : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    (1 - (ψ0 : ℂ) * z - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z ^ 3)
      = z ^ 3 * (starRingEnd ℂ) (z ^ 3 - (ψ0 : ℂ) * z ^ 2 - (ψ1 : ℂ) * z - (ψ2 : ℂ)) := by
  set w : ℂ := (starRingEnd ℂ) z with hw_def
  have hzw : z * w = 1 := by
    rw [hw_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hw3 : z ^ 3 * w ^ 3 = 1 := by rw [show z ^ 3 * w ^ 3 = (z * w) ^ 3 from by ring, hzw]; ring
  have hw2 : z ^ 3 * w ^ 2 = z := by
    rw [show z ^ 3 * w ^ 2 = z * (z * w) ^ 2 from by ring, hzw]; ring
  have hw1 : z ^ 3 * w = z ^ 2 := by
    rw [show z ^ 3 * w = z ^ 2 * (z * w) from by ring, hzw]; ring
  have hexpand : (starRingEnd ℂ) (z ^ 3 - (ψ0 : ℂ) * z ^ 2 - (ψ1 : ℂ) * z - (ψ2 : ℂ))
      = w ^ 3 - (ψ0 : ℂ) * w ^ 2 - (ψ1 : ℂ) * w - (ψ2 : ℂ) := by
    simp only [map_sub, map_mul, map_pow, Complex.conj_ofReal, ← hw_def]
  rw [hexpand]
  have hexpand2 : z ^ 3 * (w ^ 3 - (ψ0 : ℂ) * w ^ 2 - (ψ1 : ℂ) * w - (ψ2 : ℂ))
      = (z ^ 3 * w ^ 3) - (ψ0 : ℂ) * (z ^ 3 * w ^ 2) - (ψ1 : ℂ) * (z ^ 3 * w)
        - (ψ2 : ℂ) * z ^ 3 := by
    ring
  rw [hexpand2, hw3, hw2, hw1]

/-- **`phiUpPath φ t` は単位円上に根を持たない** (`t∈[0,1]`)。`ψ:=phiDown3 φ` は定常
(`AR3.St3_imp_isStationary`) なので `Qψ(z)≠0` (`‖z‖=1` 上)。`|tφ_4|≤|φ_4|<1` と
`reversal_eq_on_unit_circle` (単位円上でのノルム保存) を組み合わせると、
`z・Qψ(z) = tφ_4・Qψ^{rev}(z)` は両辺のノルムを比べる (`1=|tφ_4|<1`) と矛盾する。 -/
theorem phiUpPath_no_unit_root {φ : Fin 4 → ℝ} (hSt4 : St4 φ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 →
      z ^ 4 ≠ ∑ i : Fin 4, (phiUpPath φ t i : ℂ) * z ^ (4 - 1 - (i : ℕ)) := by
  have h3lt1 : |φ 3| < 1 := abs_phi3_lt_one_of_St4 hSt4
  have hψSt3 : St3 (phiDown3 φ) := St3_phiDown3_of_St4 hSt4
  have hψStat : IsStationary (phiDown3 φ) := St3_imp_isStationary hψSt3
  set ψ0 := phiDown3 φ 0
  set ψ1 := phiDown3 φ 1
  set ψ2 := phiDown3 φ 2
  intro t ht z hz hcontra
  set Qψ : ℂ := z ^ 3 - (ψ0 : ℂ) * z ^ 2 - (ψ1 : ℂ) * z - (ψ2 : ℂ) with hQψdef
  set Qrev : ℂ := 1 - (ψ0 : ℂ) * z - (ψ1 : ℂ) * z ^ 2 - (ψ2 : ℂ) * z ^ 3 with hQrevdef
  have hQψne : Qψ ≠ 0 := by
    intro hQ0
    have hroot : z ^ 3 = ∑ i : Fin 3, (phiDown3 φ i : ℂ) * z ^ (3 - 1 - (i : ℕ)) := by
      simp only [Fin.sum_univ_three]
      norm_num
      linear_combination hQ0
    have := hψStat z hroot
    rw [hz] at this
    exact absurd this (lt_irrefl 1)
  have hrev_eq : Qrev = z ^ 3 * (starRingEnd ℂ) Qψ := reversal_eq_on_unit_circle ψ0 ψ1 ψ2 z hz
  have heq : z * Qψ = (t * φ 3 : ℝ) * Qrev := by
    simp [phiUpPath, Fin.sum_univ_four] at hcontra
    push_cast at hcontra ⊢
    rw [hQψdef, hQrevdef]
    linear_combination hcontra
  have hnormeq : ‖z * Qψ‖ = ‖((t * φ 3 : ℝ) : ℂ) * Qrev‖ := by rw [heq]
  rw [norm_mul, norm_mul, hz, one_mul] at hnormeq
  rw [hrev_eq, norm_mul, norm_pow, hz, one_pow, one_mul, Complex.norm_conj] at hnormeq
  have hQψnormpos : 0 < ‖Qψ‖ := norm_pos_iff.mpr hQψne
  have hk'norm : ‖((t * φ 3 : ℝ) : ℂ)‖ = |t * φ 3| := Complex.norm_real _
  rw [hk'norm] at hnormeq
  have htabs : |t * φ 3| < 1 := by
    rw [abs_mul]
    rcases ht with ⟨ht0, ht1⟩
    have habst : |t| = t := abs_of_nonneg ht0
    rw [habst]
    calc t * |φ 3| ≤ 1 * |φ 3| := by
          apply mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ = |φ 3| := by ring
      _ < 1 := h3lt1
  nlinarith [hnormeq, hQψnormpos, htabs]

/-! ### 仕上げ -/

theorem St4_imp_isStationary {φ : Fin 4 → ℝ} (hSt4 : St4 φ) : IsStationary φ := by
  have hψSt3 : St3 (phiDown3 φ) := St3_phiDown3_of_St4 hSt4
  have hψStat : IsStationary (phiDown3 φ) := St3_imp_isStationary hψSt3
  have hψStat' : IsStationary
      (![phiDown3 φ 0, phiDown3 φ 1, phiDown3 φ 2] : Fin 3 → ℝ) := by
    have heq : (![phiDown3 φ 0, phiDown3 φ 1, phiDown3 φ 2] : Fin 3 → ℝ) = phiDown3 φ := by
      funext i; fin_cases i <;> simp
    rwa [heq]
  have hγ0 : IsStationary (phiUpPath φ 0) := by
    rw [phiUpPath_zero]
    exact isStationary_pad0_of_isStationary3 hψStat'
  have hresult : IsStationary (phiUpPath φ 1) :=
    isStationary_of_path_no_unit_root (by norm_num) (continuous_phiUpPath φ) hγ0
      (phiUpPath_no_unit_root hSt4)
  rwa [phiUpPath_one_of_St4 hSt4] at hresult

/-- **AR(4) の定常性の必要十分条件**: `St4 φ ↔ IsStationary φ`。 -/
theorem St4_iff_isStationary {φ : Fin 4 → ℝ} : St4 φ ↔ IsStationary φ :=
  ⟨St4_imp_isStationary, isStationary_imp_St4⟩

end StTopology
