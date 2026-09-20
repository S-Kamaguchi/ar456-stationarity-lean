import Mathlib
import StTopology.StationarityRegions
import StTopology.VietaBound
import StTopology.AR5
import StTopology.AR6
import StTopology.TwoStepMerge

set_option linter.style.header false

/-!
# 一般次数向け Schur–Cohn Step-down (`6_kanren.tex` Section 4.7, `prop:count-bound` の道具立て)

`AR5.lean` の `phiDown4`/`reversal_eq_on_unit_circle4`/`stepDown_isStationary`(次数5→4)と
`AR6.lean` の `phiDown5`/`reversal_eq_on_unit_circle5`/`stepDown_isStationary6`(次数6→5)を、
任意の次数 `n+1 → n` に一般化する。`Fin.rev`・`Fin.castSucc` で添字の反転・埋め込みを表す。
-/

open Finset StTopology

namespace StTopology

/-! ### 一般反転恒等式 -/

/-- `Q_ψ(z) := z^n-∑ᵢψᵢz^{n-1-i}` の反転が、`‖z‖=1` 上で `Q_ψ^{rev}(z) = z^n \overline{Q_ψ(z)}`
を満たす (実係数・`z\bar z=1` のみ使う純代数)。`reversal_eq_on_unit_circle4`(`AR5.lean`)・
`reversal_eq_on_unit_circle5`(`AR6.lean`) の一般 `n` 版。 -/
theorem reversal_eq_on_unit_circle_gen {n : ℕ} (ψ : Fin n → ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    (1 - ∑ i : Fin n, (ψ i : ℂ) * z ^ ((i : ℕ) + 1))
      = z ^ n * (starRingEnd ℂ) (z ^ n - ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - 1 - (i : ℕ))) := by
  set w : ℂ := (starRingEnd ℂ) z with hw_def
  have hzw : z * w = 1 := by
    rw [hw_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hconj : (starRingEnd ℂ) (z ^ n - ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - 1 - (i : ℕ)))
      = w ^ n - ∑ i : Fin n, (ψ i : ℂ) * w ^ (n - 1 - (i : ℕ)) := by
    simp only [map_sub, map_sum, map_mul, map_pow, Complex.conj_ofReal, ← hw_def]
  rw [hconj, mul_sub, Finset.mul_sum]
  have hzwn : z ^ n * w ^ n = 1 := by
    rw [show z ^ n * w ^ n = (z * w) ^ n from by ring, hzw, one_pow]
  rw [hzwn]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hsplit : n = ((i : ℕ) + 1) + (n - 1 - (i : ℕ)) := by omega
  have hzn : z ^ n = z ^ ((i : ℕ) + 1) * z ^ (n - 1 - (i : ℕ)) := by
    rw [← pow_add, ← hsplit]
  have hzwi : z ^ (n - 1 - (i : ℕ)) * w ^ (n - 1 - (i : ℕ)) = 1 := by
    rw [show z ^ (n - 1 - (i : ℕ)) * w ^ (n - 1 - (i : ℕ)) = (z * w) ^ (n - 1 - (i : ℕ))
      from by ring, hzw, one_pow]
  have hexp : z ^ n * ((ψ i : ℂ) * w ^ (n - 1 - (i : ℕ))) = (ψ i : ℂ) * z ^ ((i : ℕ) + 1) :=
    calc z ^ n * ((ψ i : ℂ) * w ^ (n - 1 - (i : ℕ)))
        = (z ^ ((i : ℕ) + 1) * z ^ (n - 1 - (i : ℕ))) * ((ψ i : ℂ) * w ^ (n - 1 - (i : ℕ))) := by
          rw [hzn]
      _ = (ψ i : ℂ) * z ^ ((i : ℕ) + 1)
          * (z ^ (n - 1 - (i : ℕ)) * w ^ (n - 1 - (i : ℕ))) := by ring
      _ = (ψ i : ℂ) * z ^ ((i : ℕ) + 1) * 1 := by rw [hzwi]
      _ = (ψ i : ℂ) * z ^ ((i : ℕ) + 1) := by ring
  linear_combination -hexp

/-! ### 一般 Schur–Cohn 変換 (down-step) `ψ = φ^{(n)}`, 次数`(n+1)→n` -/

/-- `ψ_i = (φ_i + k φ_{n-1-i}) / (1-k²)` (`k := φ_n`、`Fin (n+1)` の最後の添字)。`phiDown4`
(`AR5.lean`、`n=4`)・`phiDown5`(`AR6.lean`、`n=5`)の一般 `n` 版。`Fin.castSucc` で
`Fin n → Fin (n+1)` の自然な埋め込みを、`Fin.rev` で `Fin n` 内の添字反転を表す。 -/
noncomputable def phiDownGen {n : ℕ} (φ : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => (φ i.castSucc + φ (Fin.last n) * φ (Fin.rev i).castSucc) / (1 - φ (Fin.last n) ^ 2)

/-- `phiDownGen` は `n=4` (次数5→4) のとき `AR5.lean` の `phiDown4` と一致する (添字のズレが
ないことのサニティチェック)。 -/
theorem phiDownGen_eq_phiDown4 (φ : Fin 5 → ℝ) :
    phiDownGen (n := 4) φ = phiDown4 φ := by
  funext i
  fin_cases i <;> simp [phiDownGen, phiDown4]

/-- `phiDownGen` は `n=5` (次数6→5) のとき `AR6.lean` の `phiDown5` と一致する (添字のズレが
ないことのサニティチェック)。 -/
theorem phiDownGen_eq_phiDown5 (φ : Fin 6 → ℝ) :
    phiDownGen (n := 5) φ = phiDown5 φ := by
  funext i
  fin_cases i <;> simp [phiDownGen, phiDown5]

/-! ### 一般 Step-down 補題: 次数下げ変換は定常性を保つ -/

/-- `gammaT (clampUnit t) φ` の最後の座標 `k(t) := (clampUnit t)^p・φ_last` は `|φ_last|<1`
のとき常に `|k(t)|<1`。`clampUnit_pow_mul_lt_one`(`AR5.lean`)・`clampUnit_pow_mul_lt_one6`
(`AR6.lean`) の一般 `p` 版。 -/
theorem clampUnit_pow_mul_lt_one_gen {p : ℕ} {c : ℝ} (h : |c| < 1) (t : ℝ) :
    |(clampUnit t) ^ p * c| < 1 := by
  have hmem := clampUnit_mem t
  have h1 : |clampUnit t| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hmem.1], hmem.2⟩
  rw [abs_mul, abs_pow]
  calc |clampUnit t| ^ p * |c| ≤ 1 ^ p * |c| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact pow_le_pow_left₀ (abs_nonneg _) h1 p
    _ = |c| := by ring
    _ < 1 := h

/-- **一般 Step-down 補題**: `IsStationary φ` (次数`n+1`) ならば `IsStationary (phiDownGen φ)`
(次数`n`)。`stepDown_isStationary`(`AR5.lean`)・`stepDown_isStationary6`(`AR6.lean`) の一般
`n` 版 (`n>0` を仮定、`isOpen_isStationary` 等が `0<p` を要求するため)。 -/
theorem stepDown_isStationary_gen {n : ℕ} (hn : 0 < n) {φ : Fin (n + 1) → ℝ}
    (hφ : IsStationary φ) : IsStationary (phiDownGen φ) := by
  have hnlt1 : |φ (Fin.last n)| < 1 := by
    have h := abs_last_coeff_lt_one (p := n + 1) (Nat.succ_pos n) hφ
    have heq : (⟨(n + 1) - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext; simp
    rwa [heq] at h
  set ψAux : ℝ → Fin n → ℝ := fun t => phiDownGen (gammaT (clampUnit t) φ) with hψAux_def
  -- 分母が常に非零であること
  have hdenom_pos : ∀ t : ℝ, (0 : ℝ) < 1 - (gammaT (clampUnit t) φ (Fin.last n)) ^ 2 := by
    intro t
    have hgt : gammaT (clampUnit t) φ (Fin.last n)
        = (clampUnit t) ^ (n + 1) * φ (Fin.last n) := by
      unfold gammaT; congr 1
    rw [hgt]
    have := clampUnit_pow_mul_lt_one_gen (p := n + 1) hnlt1 t
    nlinarith [(abs_lt.mp this).1, (abs_lt.mp this).2]
  -- 連続性 (`fin_cases` なし、`phiDownGen` が `fun i => …` で定義されているため一様に扱える)
  have hψAux_cont : Continuous ψAux := by
    have hgcont : Continuous (fun t : ℝ => gammaT (clampUnit t) φ) :=
      (continuous_radialPath φ).comp clampUnit_continuous
    rw [hψAux_def]
    unfold phiDownGen
    apply continuous_pi
    intro i
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    exact (hdenom_pos t).ne'
  -- t=0 での値と定常性
  have hψAux_zero : ψAux 0 = fun _ => (0 : ℝ) := by
    have hc0 : clampUnit 0 = 0 := by unfold clampUnit; norm_num
    simp only [hψAux_def, hc0, gammaT_zero]
    unfold phiDownGen
    funext i; norm_num
  have hstat0 : IsStationary (ψAux 0) := by rw [hψAux_zero]; exact isStationary_zero
  -- 開集合性から、小さい t₀>0 で ψAux t₀ も定常
  have hopen : IsOpen (ψAux ⁻¹' {ψ : Fin n → ℝ | IsStationary ψ}) :=
    (isOpen_isStationary hn).preimage hψAux_cont
  have hmem0 : (0 : ℝ) ∈ ψAux ⁻¹' {ψ : Fin n → ℝ | IsStationary ψ} := hstat0
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
      z ^ n ≠ ∑ i : Fin n, (ψAux t i : ℂ) * z ^ (n - 1 - (i : ℕ)) := by
    intro t ht z hz hcontra
    have hrt : clampUnit t = t := clampUnit_eq_of_mem ht
    have hγstat : IsStationary (gammaT t φ) :=
      isStationary_scale (Nat.succ_pos n) hφ ht.1 ht.2
    set φt : Fin (n + 1) → ℝ := gammaT t φ with hφt_def
    set k : ℝ := φt (Fin.last n) with hk_def
    set ψ : Fin n → ℝ := phiDownGen φt with hψ_def
    have hψAux_t : ψAux t = ψ := by rw [hψAux_def]; dsimp only; rw [hrt]
    rw [hψAux_t] at hcontra
    have hkne : (1 : ℝ) - k ^ 2 ≠ 0 := by
      have := hdenom_pos t; rw [hrt] at this; rw [hk_def]; linarith [this]
    have hQψ0 : z ^ n - ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - 1 - (i : ℕ)) = 0 := by
      linear_combination hcontra
    have hQrev0 : (1 - ∑ i : Fin n, (ψ i : ℂ) * z ^ ((i : ℕ) + 1)) = 0 := by
      rw [reversal_eq_on_unit_circle_gen ψ z hz, hQψ0]; simp
    -- `ψ_i - k ψ_{rev i} = φt_i` (一般添字)
    have hUP : ∀ i : Fin n, ψ i - k * ψ (Fin.rev i) = φt i.castSucc := by
      intro i
      have hψi : ψ i = (φt i.castSucc + k * φt (Fin.rev i).castSucc) / (1 - k ^ 2) := by
        rw [hψ_def, hk_def]; rfl
      have hψri : ψ (Fin.rev i)
          = (φt (Fin.rev i).castSucc + k * φt (Fin.rev (Fin.rev i)).castSucc) / (1 - k ^ 2) := by
        rw [hψ_def, hk_def]; rfl
      rw [hψi, hψri, Fin.rev_rev]
      field_simp
      ring
    have hUPC : ∀ i : Fin n,
        (ψ i : ℂ) - (k : ℂ) * (ψ (Fin.rev i) : ℂ) = (φt i.castSucc : ℂ) := fun i => by
      exact_mod_cast hUP i
    -- 添字反転の和の並べ替え: `∑ᵢψᵢz^{i+1} = ∑ᵢψ_{rev i}z^{n-i}`
    have hreindex : ∑ i : Fin n, (ψ i : ℂ) * z ^ ((i : ℕ) + 1)
        = ∑ i : Fin n, (ψ (Fin.rev i) : ℂ) * z ^ (n - (i : ℕ)) := by
      apply Fintype.sum_equiv Fin.revPerm (fun i => (ψ i : ℂ) * z ^ ((i : ℕ) + 1))
        (fun j => (ψ (Fin.rev j) : ℂ) * z ^ (n - (j : ℕ)))
      intro i
      have hrp : (Fin.revPerm i : Fin n) = Fin.rev i := rfl
      have hval : n - ((Fin.rev i : Fin n) : ℕ) = (i : ℕ) + 1 := by
        have hi := i.isLt; simp only [Fin.rev]; omega
      rw [hrp, Fin.rev_rev, hval]
    -- `∑ⱼ:Fin(n+1) φtⱼz^{n-j}` を `∑ᵢ:Fin n φt(i.castSucc)z^{n-i} + k` に分解
    have hsplitsum : ∑ j : Fin (n + 1), (φt j : ℂ) * z ^ (n - (j : ℕ))
        = (∑ i : Fin n, (φt i.castSucc : ℂ) * z ^ (n - (i : ℕ))) + (k : ℂ) := by
      rw [Fin.sum_univ_castSucc]
      simp [hk_def]
    have hsubst : ∑ i : Fin n, (φt i.castSucc : ℂ) * z ^ (n - (i : ℕ))
        = ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - (i : ℕ))
          - (k : ℂ) * ∑ i : Fin n, (ψ (Fin.rev i) : ℂ) * z ^ (n - (i : ℕ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      linear_combination -z ^ (n - (i : ℕ)) * hUPC i
    have htarget : z ^ (n + 1) - ∑ j : Fin (n + 1), (φt j : ℂ) * z ^ (n - (j : ℕ))
        = z * (z ^ n - ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - 1 - (i : ℕ)))
          - (k : ℂ) * (1 - ∑ i : Fin n, (ψ i : ℂ) * z ^ ((i : ℕ) + 1)) := by
      rw [hsplitsum, hsubst, ← hreindex]
      have hzn1 : z ^ (n + 1) = z * z ^ n := by ring
      have hzQ : z * ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - 1 - (i : ℕ))
          = ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - (i : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have : n - (i : ℕ) = 1 + (n - 1 - (i : ℕ)) := by
          have := i.isLt; omega
        rw [this, pow_add]
        ring
      linear_combination hzn1 + hzQ
    rw [hQψ0, hQrev0] at htarget
    simp only [mul_zero, sub_zero] at htarget
    have hzroot : z ^ (n + 1) = ∑ j : Fin (n + 1), (φt j : ℂ) * z ^ (n - (j : ℕ)) := by
      linear_combination htarget
    have hzroot' : z ^ (n + 1) = ∑ j : Fin (n + 1), (φt j : ℂ) * z ^ (n + 1 - 1 - (j : ℕ)) := by
      simpa using hzroot
    have := hγstat z hzroot'
    rw [hz] at this
    exact absurd this (lt_irrefl 1)
  -- 種と単位円回避を合わせて `isStationary_of_path_no_unit_root` を適用 (経路を `[t₀,1]` にずらす)
  set γ' : ℝ → Fin n → ℝ := fun s => ψAux (t₀ + s * (1 - t₀)) with hγ'_def
  have hγ'cont : Continuous γ' := by
    rw [hγ'_def]; exact hψAux_cont.comp (by fun_prop)
  have hγ'0 : γ' 0 = ψAux t₀ := by rw [hγ'_def]; norm_num
  have hγ'1 : γ' 1 = ψAux 1 := by rw [hγ'_def]; norm_num
  have hγ'no : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 →
      z ^ n ≠ ∑ i : Fin n, (γ' s i : ℂ) * z ^ (n - 1 - (i : ℕ)) := by
    intro s hs z hz
    have hmem : t₀ + s * (1 - t₀) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · nlinarith [hs.1, hs.2, ht₀pos.le, ht₀le1]
      · nlinarith [hs.1, hs.2, ht₀pos.le, ht₀le1]
    exact hno (t₀ + s * (1 - t₀)) hmem z hz
  have hresult : IsStationary (γ' 1) := by
    apply isStationary_of_path_no_unit_root hn hγ'cont
    · rw [hγ'0]; exact hstat_t₀
    · exact hγ'no
  rw [hγ'1] at hresult
  have h1eq : clampUnit 1 = 1 := clampUnit_eq_of_mem ⟨zero_le_one, le_refl 1⟩
  have hfin : ψAux 1 = phiDownGen φ := by rw [hψAux_def]; dsimp only; rw [h1eq, gammaT_one]
  rwa [hfin] at hresult

/-! ### 一般 Step-up 補題: `phiDownGen` の逆方向 (十分性) -/

/-- `ψ_i - k ψ_{rev i} = φ_i` (`k:=φ_last`)。`stepDown_isStationary_gen` 内で `hUP` として
局所的に示していたのと同じ恒等式を、`phiDownGen` 自体の性質として独立に取り出したもの。 -/
theorem phiDownGen_rev_ident {n : ℕ} (φ : Fin (n + 1) → ℝ)
    (hk : (1 : ℝ) - φ (Fin.last n) ^ 2 ≠ 0) (i : Fin n) :
    phiDownGen φ i - φ (Fin.last n) * phiDownGen φ (Fin.rev i) = φ i.castSucc := by
  change (φ i.castSucc + φ (Fin.last n) * φ (Fin.rev i).castSucc) / (1 - φ (Fin.last n) ^ 2)
      - φ (Fin.last n) * ((φ (Fin.rev i).castSucc
        + φ (Fin.last n) * φ (Fin.rev (Fin.rev i)).castSucc) / (1 - φ (Fin.last n) ^ 2))
      = φ i.castSucc
  rw [Fin.rev_rev]
  field_simp
  ring

/-- 添字反転の和の並べ替え: `∑ᵢψᵢz^{i+1} = ∑ᵢψ_{rev i}z^{n-i}`。`stepDown_isStationary_gen`
内の `hreindex` と同じ議論を、`ψ`・`z` について独立な補題として取り出したもの。 -/
theorem sum_rev_reindex_gen {n : ℕ} (ψ : Fin n → ℝ) (z : ℂ) :
    ∑ i : Fin n, (ψ i : ℂ) * z ^ ((i : ℕ) + 1)
      = ∑ i : Fin n, (ψ (Fin.rev i) : ℂ) * z ^ (n - (i : ℕ)) := by
  apply Fintype.sum_equiv Fin.revPerm (fun i => (ψ i : ℂ) * z ^ ((i : ℕ) + 1))
    (fun j => (ψ (Fin.rev j) : ℂ) * z ^ (n - (j : ℕ)))
  intro i
  have hrp : (Fin.revPerm i : Fin n) = Fin.rev i := rfl
  have hval : n - ((Fin.rev i : Fin n) : ℕ) = (i : ℕ) + 1 := by
    have hi := i.isLt; simp only [Fin.rev]; omega
  rw [hrp, Fin.rev_rev, hval]

/-- `γ(t)_i := ψ_i - tk ψ_{n-1-i}` (`i:Fin n`, `Fin.castSucc` で埋め込み), `γ(t)_{last} := tk`
(`ψ:=phiDownGen φ`, `k:=φ_last`)。`phiUpPath4`(`AR5.lean`)・`phiUpPath5`(`AR6.lean`) の一般
`n` 版。`Fin.snoc` で `Fin n → ℝ` と最後の値から `Fin (n+1) → ℝ` を組み立てる。 -/
noncomputable def phiUpPathGen {n : ℕ} (φ : Fin (n + 1) → ℝ) (t : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (fun i : Fin n => phiDownGen φ i - t * φ (Fin.last n) * phiDownGen φ (Fin.rev i))
    (t * φ (Fin.last n))

theorem continuous_phiUpPathGen {n : ℕ} (φ : Fin (n + 1) → ℝ) :
    Continuous (phiUpPathGen φ) := by
  unfold phiUpPathGen
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ ?_ j
  · simp only [Fin.snoc_last]; fun_prop
  · intro i; simp only [Fin.snoc_castSucc]; fun_prop

theorem phiUpPathGen_zero {n : ℕ} (φ : Fin (n + 1) → ℝ) :
    phiUpPathGen φ 0 = Fin.snoc (phiDownGen φ) (0 : ℝ) := by
  unfold phiUpPathGen
  simp

theorem phiUpPathGen_one {n : ℕ} {φ : Fin (n + 1) → ℝ}
    (hk : (1 : ℝ) - φ (Fin.last n) ^ 2 ≠ 0) : phiUpPathGen φ 1 = φ := by
  unfold phiUpPathGen
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp
  · intro i
    simp only [Fin.snoc_castSucc, one_mul]
    exact phiDownGen_rev_ident φ hk i

/-- `(ψ,0)` は定常 (`ψ` が定常なら)。`isStationary_pad0_of_isStationary4`(`AR5Sufficiency.lean`)・
`isStationary_pad0_of_isStationary5`(`AR6Sufficiency.lean`) の一般 `n` 版、`Fin.snoc` 版。 -/
theorem isStationary_snoc_zero_gen {n : ℕ} {ψ : Fin n → ℝ} (hψ : IsStationary ψ) :
    IsStationary (Fin.snoc ψ (0 : ℝ) : Fin (n + 1) → ℝ) := by
  intro α hα
  have hα' : α ^ (n + 1) = ∑ i : Fin n, (ψ i : ℂ) * α ^ (n - (i : ℕ)) := by
    rw [Fin.sum_univ_castSucc] at hα
    simpa using hα
  have hstep : α * ∑ i : Fin n, (ψ i : ℂ) * α ^ (n - 1 - (i : ℕ))
      = ∑ i : Fin n, (ψ i : ℂ) * α ^ (n - (i : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hexp : n - (i : ℕ) = 1 + (n - 1 - (i : ℕ)) := by have := i.isLt; omega
    rw [hexp, pow_add]; ring
  have hfact : α * (α ^ n - ∑ i : Fin n, (ψ i : ℂ) * α ^ (n - 1 - (i : ℕ))) = 0 := by
    have hcomb : α * α ^ n = α * ∑ i : Fin n, (ψ i : ℂ) * α ^ (n - 1 - (i : ℕ)) := by
      rw [hstep, ← hα']; ring
    linear_combination hcomb
  rcases mul_eq_zero.mp hfact with h0 | hn
  · rw [h0]; simp
  · have hroot : α ^ n = ∑ i : Fin n, (ψ i : ℂ) * α ^ (n - 1 - (i : ℕ)) := by
      linear_combination hn
    exact hψ α hroot

/-- **`phiUpPathGen φ t` は単位円上に根を持たない** (`t∈[0,1]`)。`phiDownGen φ` が定常であれば
(Step-up 側の仮定)、`AR5Sufficiency.lean`・`AR6Sufficiency.lean` の `phiUpPath4_no_unit_root`・
`phiUpPath5_no_unit_root` と同じ議論の一般 `n` 版。 -/
theorem phiUpPathGen_no_unit_root {n : ℕ} {φ : Fin (n + 1) → ℝ}
    (hstat : IsStationary (phiDownGen φ)) (hklt1 : |φ (Fin.last n)| < 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 →
      z ^ (n + 1) ≠ ∑ j : Fin (n + 1), (phiUpPathGen φ t j : ℂ) * z ^ (n + 1 - 1 - (j : ℕ)) := by
  set ψ : Fin n → ℝ := phiDownGen φ with hψ_def
  set k : ℝ := φ (Fin.last n) with hk_def
  intro t ht z hz hcontra
  set Qψ : ℂ := z ^ n - ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - 1 - (i : ℕ)) with hQψdef
  set Qrev : ℂ := 1 - ∑ i : Fin n, (ψ i : ℂ) * z ^ ((i : ℕ) + 1) with hQrevdef
  have hQψne : Qψ ≠ 0 := by
    intro hQ0
    have hroot : z ^ n = ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - 1 - (i : ℕ)) := by
      rw [hQψdef] at hQ0; linear_combination hQ0
    have := hstat z hroot
    rw [hz] at this
    exact absurd this (lt_irrefl 1)
  have hrev_eq : Qrev = z ^ n * (starRingEnd ℂ) Qψ :=
    reversal_eq_on_unit_circle_gen ψ z hz
  have hcontra' : z ^ (n + 1)
      = ∑ j : Fin (n + 1), (phiUpPathGen φ t j : ℂ) * z ^ (n - (j : ℕ)) := by
    simpa using hcontra
  have hsplitsum : ∑ j : Fin (n + 1), (phiUpPathGen φ t j : ℂ) * z ^ (n - (j : ℕ))
      = (∑ i : Fin n, (phiUpPathGen φ t i.castSucc : ℂ) * z ^ (n - (i : ℕ)))
        + (t : ℝ) * (k : ℝ) := by
    rw [Fin.sum_univ_castSucc]
    unfold phiUpPathGen
    simp [hk_def]
  have hexpand : ∑ i : Fin n, (phiUpPathGen φ t i.castSucc : ℂ) * z ^ (n - (i : ℕ))
      = ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - (i : ℕ))
        - (t : ℝ) * (k : ℝ) * ∑ i : Fin n, (ψ (Fin.rev i) : ℂ) * z ^ (n - (i : ℕ)) := by
    unfold phiUpPathGen
    simp only [Fin.snoc_castSucc]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hψ_def, hk_def]
    ring
  have hzQ : z * Qψ = z ^ (n + 1) - ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - (i : ℕ)) := by
    rw [hQψdef, mul_sub]
    have hzn1 : z * z ^ n = z ^ (n + 1) := by ring
    have hzsum : z * ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - 1 - (i : ℕ))
        = ∑ i : Fin n, (ψ i : ℂ) * z ^ (n - (i : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hexp : n - (i : ℕ) = 1 + (n - 1 - (i : ℕ)) := by have := i.isLt; omega
      rw [hexp, pow_add]; ring
    rw [hzn1, hzsum]
  have htkQrev : (t : ℝ) * (k : ℝ) * Qrev = (t : ℝ) * (k : ℝ)
      - (t : ℝ) * (k : ℝ) * ∑ i : Fin n, (ψ i : ℂ) * z ^ ((i : ℕ) + 1) := by
    rw [hQrevdef]; ring
  have htarget : z * Qψ - (t : ℝ) * (k : ℝ) * Qrev
      = z ^ (n + 1) - ∑ j : Fin (n + 1), (phiUpPathGen φ t j : ℂ) * z ^ (n - (j : ℕ)) := by
    rw [hzQ, htkQrev, hsplitsum, hexpand, sum_rev_reindex_gen ψ z]
    ring
  rw [hcontra'] at htarget
  simp only [sub_self] at htarget
  have heq0 : z * Qψ = ((t * k : ℝ) : ℂ) * Qrev := by
    push_cast at htarget ⊢; linear_combination htarget
  have hnormeq : ‖z * Qψ‖ = ‖((t * k : ℝ) : ℂ) * Qrev‖ := by rw [heq0]
  rw [norm_mul, norm_mul, hz, one_mul] at hnormeq
  rw [hrev_eq, norm_mul, norm_pow, hz, one_pow, one_mul, Complex.norm_conj] at hnormeq
  have hQψnormpos : 0 < ‖Qψ‖ := norm_pos_iff.mpr hQψne
  have hk'norm : ‖((t * k : ℝ) : ℂ)‖ = |t * k| := Complex.norm_real _
  rw [hk'norm] at hnormeq
  have htabs : |t * k| < 1 := by
    rw [abs_mul]
    rcases ht with ⟨ht0, ht1⟩
    have habst : |t| = t := abs_of_nonneg ht0
    rw [habst]
    calc t * |k| ≤ 1 * |k| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ = |k| := by ring
      _ < 1 := hklt1
  nlinarith [hnormeq, hQψnormpos, htabs]

/-- **一般 Step-up 補題**: `|φ_last|<1 ∧ IsStationary (phiDownGen φ)` ならば `IsStationary φ`。
`St5_imp_isStationary`(`AR5Sufficiency.lean`)・`St6_imp_isStationary`(`AR6Sufficiency.lean`)
の一般 `n` 版。 -/
theorem stepUp_isStationary_gen {n : ℕ} {φ : Fin (n + 1) → ℝ}
    (hklt1 : |φ (Fin.last n)| < 1) (hstat : IsStationary (phiDownGen φ)) : IsStationary φ := by
  have hkne : (1 : ℝ) - φ (Fin.last n) ^ 2 ≠ 0 := by
    have hpos : (0 : ℝ) < 1 - φ (Fin.last n) := by linarith [(abs_lt.mp hklt1).2]
    have hpos' : (0 : ℝ) < 1 + φ (Fin.last n) := by linarith [(abs_lt.mp hklt1).1]
    nlinarith [hpos, hpos']
  have hγ0 : IsStationary (phiUpPathGen φ 0) := by
    rw [phiUpPathGen_zero]
    exact isStationary_snoc_zero_gen hstat
  have hresult : IsStationary (phiUpPathGen φ 1) :=
    isStationary_of_path_no_unit_root (Nat.succ_pos n) (continuous_phiUpPathGen φ) hγ0
      (phiUpPathGen_no_unit_root hstat hklt1)
  rwa [phiUpPathGen_one hkne] at hresult

/-- **一般 Step-down/Step-up 同値**: `IsStationary φ ↔ |φ_last|<1 ∧ IsStationary (phiDownGen φ)`
(`n>0`)。`prop:count-bound` の帰納法の核となる、次数 `n+1` の定常性を次数 `n` の定常性
+1条件に帰着する一般命題。 -/
theorem isStationary_iff_stepDown_gen {n : ℕ} (hn : 0 < n) {φ : Fin (n + 1) → ℝ} :
    IsStationary φ ↔ |φ (Fin.last n)| < 1 ∧ IsStationary (phiDownGen φ) := by
  constructor
  · intro hφ
    have heq : (⟨(n + 1) - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext; simp
    have hlt1 : |φ (Fin.last n)| < 1 := by
      have h := abs_last_coeff_lt_one (p := n + 1) (Nat.succ_pos n) hφ
      rwa [heq] at h
    exact ⟨hlt1, stepDown_isStationary_gen hn hφ⟩
  · rintro ⟨hlt1, hstat⟩
    exact stepUp_isStationary_gen hlt1 hstat

/-! ### 偶数次数向け: 2段 Step-down のマージ (`prop:count-bound` 偶数ケースの道具) -/

/-- 次数 `n+2` のとき、`phiDownGen` を1回適用した末端の反射係数
`phiDownGen φ (Fin.last n)` は、`lem:twostep` の `k_{m-1}` の形
`(φ_{p-1}+φ_1φ_p)/(1-φ_p²)` と一致する (`φ_p=φ(Fin.last(n+1))`, `φ_1=φ 0`,
`φ_{p-1}=φ(Fin.last n).castSucc`)。 -/
theorem phiDownGen_last_eq {n : ℕ} (φ : Fin (n + 2) → ℝ) :
    phiDownGen φ (Fin.last n)
      = (φ (Fin.last n).castSucc + φ 0 * φ (Fin.last (n + 1)))
        / (1 - φ (Fin.last (n + 1)) ^ 2) := by
  change (φ (Fin.last n).castSucc
      + φ (Fin.last (n + 1)) * φ (Fin.rev (Fin.last n)).castSucc)
      / (1 - φ (Fin.last (n + 1)) ^ 2)
    = (φ (Fin.last n).castSucc + φ 0 * φ (Fin.last (n + 1)))
        / (1 - φ (Fin.last (n + 1)) ^ 2)
  simp only [Fin.rev_last, Fin.castSucc_zero]
  ring

/-- **一般2段 Step-down 同値**(次数 `n+2`, `n>0`): `IsStationary φ` は、単一のマージ済み条件
`1-φ_p²>|φ_{p-1}+φ_1φ_p|` と `IsStationary (phiDownGen (phiDownGen φ))`(次数 `n`)の積に
同値。`stepDown_isStationary_gen`/`isStationary_iff_stepDown_gen` を2回合成し `twostep_merge`
で2つの反射係数条件を1本化する。`prop:count-bound` の偶数 `p` ケースで使う。 -/
theorem isStationary_iff_twostepDown_gen {n : ℕ} (hn : 0 < n) {φ : Fin (n + 2) → ℝ} :
    IsStationary φ ↔
      (1 - φ (Fin.last (n + 1)) ^ 2
          > |φ (Fin.last n).castSucc + φ 0 * φ (Fin.last (n + 1))|)
        ∧ IsStationary (phiDownGen (phiDownGen φ)) := by
  rw [isStationary_iff_stepDown_gen (Nat.succ_pos n) (φ := φ),
      isStationary_iff_stepDown_gen hn (φ := phiDownGen φ), ← and_assoc, phiDownGen_last_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨(twostep_merge _ _ _).mpr ⟨h1, h2⟩, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(twostep_merge _ _ _).mp h1, h2⟩

end StTopology
