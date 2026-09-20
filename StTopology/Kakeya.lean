import Mathlib
import StTopology.StationarityRegions

set_option linter.style.header false

/-!
# Eneström–Kakeya型条件 (`prop:kakeya`, `5_kanren.tex` Section 3.5)

`-1 < φ_1 < φ_2 < ⋯ < φ_p < 0` ならば `p φ` は定常。

論文の議論: 特性多項式 `φ(x) = 1 - (φ_1x+⋯+φ_px^p)` に対し `a_0:=1, a_k:=-φ_k`
(`k=1,…,p`) とおくと `a_0>a_1>⋯>a_p>0` (狭義単調減少・正)。Eneström–Kakeya定理
(係数が正で狭義単調減少な多項式の根はすべて `|x|>1` を満たす)より `φ(x)` の根は
すべて `|x|>1`。`AR(p)` の定常性は `φ(x)` の逆特性多項式(`IsStationary`)の根が
すべて `|x|<1` であることと同値(reversal: `α` が `IsStationary` の方程式の根 ⟺
`z=1/α` が `φ(x)=0` の根)なので、主張が従う。

Mathlibに Eneström–Kakeya定理が存在しないため、テレスコーピング和と三角不等式による
自前証明を行う。標準的な証明(`(1-z)f(z) = a_0 - ∑_{k=1}^{p+1} d_k z^k`,
`d_k>0`, `∑d_k=a_0`)を、`|z|≤1` の場合に**実部**の議論で強化し(`|z|=1` の境界も
含めて根を排除する狭義版)、`z=1` に強制されることを示してから `z=1` では
方程式が成立しないことと矛盾させる、という一直線の議論にまとめている
(`AbsSum.lean`/`CauchyBound.lean` と同系統の「三角不等式による根の評価」)。
-/

open Finset StTopology

namespace StTopology

/-! ### 一般補題1: 差分の和はテレスコープする -/

theorem sum_succ_sub_castSucc_eq {p : ℕ} (g : Fin (p + 1) → ℝ) :
    ∑ i : Fin p, (g i.succ - g i.castSucc) = g (Fin.last p) - g 0 := by
  set g2 : ℕ → ℝ := fun k => if h : k < p + 1 then g ⟨k, h⟩ else g (Fin.last p) with hg2
  have hstep : ∀ i : Fin p, g i.succ - g i.castSucc = g2 ((i : ℕ) + 1) - g2 (i : ℕ) := by
    intro i
    have hi := i.isLt
    have h1 : g2 ((i : ℕ) + 1) = g ⟨(i : ℕ) + 1, by omega⟩ := by simp [hg2]
    have h2 : g2 (i : ℕ) = g ⟨(i : ℕ), by omega⟩ := by simp [hg2]
    rw [h1, h2]
    congr 2
  have key : ∑ i : Fin p, (g i.succ - g i.castSucc)
      = ∑ k ∈ Finset.range p, (g2 (k + 1) - g2 k) := by
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    exact Fin.sum_univ_eq_sum_range (fun k => g2 (k + 1) - g2 k) p
  rw [key, Finset.sum_range_sub g2 p]
  have e1 : g2 p = g (Fin.last p) := by
    simp only [hg2]; rw [dif_pos (Nat.lt_succ_self p)]; congr 1
  have e2 : g2 0 = g 0 := by simp [hg2]
  rw [e1, e2]

/-! ### 一般補題2: `|z|≤1` かつ正の重みつき凸結合が `1` に等しければ `z=1` -/

theorem eq_one_of_norm_le_one_of_sum_eq_one {n : ℕ} (d : Fin (n + 1) → ℝ) (hd : ∀ i, 0 < d i)
    (hsum : ∑ i, d i = 1) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (heq : (1 : ℂ) = ∑ i : Fin (n + 1), (d i : ℂ) * z ^ ((i : ℕ) + 1)) : z = 1 := by
  set i0 : Fin (n + 1) := 0 with hi0_def
  have hre : (1 : ℝ) = ∑ i : Fin (n + 1), d i * (z ^ ((i : ℕ) + 1)).re := by
    have hc := congrArg Complex.re heq
    simpa [Complex.re_sum] using hc
  have hbound : ∀ i : Fin (n + 1), (z ^ ((i : ℕ) + 1)).re ≤ 1 := by
    intro i
    calc (z ^ ((i : ℕ) + 1)).re ≤ ‖z ^ ((i : ℕ) + 1)‖ := Complex.re_le_norm _
      _ = ‖z‖ ^ ((i : ℕ) + 1) := norm_pow z _
      _ ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
  have hnonneg : ∀ i : Fin (n + 1), 0 ≤ d i * (1 - (z ^ ((i : ℕ) + 1)).re) :=
    fun i => mul_nonneg (hd i).le (by linarith [hbound i])
  have hsum0 : ∑ i : Fin (n + 1), d i * (1 - (z ^ ((i : ℕ) + 1)).re) = 0 := by
    have hexpand : ∀ i : Fin (n + 1), d i * (1 - (z ^ ((i : ℕ) + 1)).re)
        = d i - d i * (z ^ ((i : ℕ) + 1)).re := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hexpand i), Finset.sum_sub_distrib, hsum, ← hre]
    ring
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), d i * (1 - (z ^ ((i : ℕ) + 1)).re) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hsum0
  have hterm := hzero i0 (Finset.mem_univ i0)
  have hd0 : d i0 ≠ 0 := (hd i0).ne'
  have hre1 : (z ^ ((i0 : ℕ) + 1)).re = 1 := by
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h hd0
    · linarith
  have hre : z.re = 1 := by
    have hi0val : (i0 : ℕ) = 0 := by simp [hi0_def]
    rw [hi0val, zero_add, pow_one] at hre1
    exact hre1
  have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have h2 : ‖z‖ = 1 := le_antisymm hz (hre ▸ h1)
  have h3 : ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2 := Complex.sq_norm_sub_sq_re z
  rw [h2, hre] at h3
  norm_num at h3
  have h4 : z.im = 0 := by
    have h3' : z.im ^ 2 = 0 := h3.symm
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3'
  apply Complex.ext
  · exact hre
  · simp [h4]

/-! ### Eneström–Kakeya係数列 -/

/-- `φ` を `0` で1つ延長した係数列 (`φ'_m := 0`)。 -/
noncomputable def kakeyaExt {m : ℕ} (φ : Fin (m + 1) → ℝ) : Fin (m + 2) → ℝ := Fin.snoc φ 0

/-- Eneström–Kakeyaの差分係数列: `d_0 = 1+φ_0`, `d_{i+1} = φ'_{i+1}-φ'_i`
(`a_0=1, a_k=-φ_k` の連続差分)。 -/
noncomputable def kakeyaDiff {m : ℕ} (φ : Fin (m + 1) → ℝ) : Fin (m + 2) → ℝ :=
  Fin.cons (1 + φ 0) (fun i : Fin (m + 1) => kakeyaExt φ i.succ - kakeyaExt φ i.castSucc)

theorem kakeyaDiff_pos {m : ℕ} {φ : Fin (m + 1) → ℝ} (hmono : StrictMono φ) (h0 : -1 < φ 0)
    (hlast : φ (Fin.last m) < 0) : ∀ I : Fin (m + 2), 0 < kakeyaDiff φ I := by
  intro I
  refine Fin.cases ?_ ?_ I
  · change 0 < 1 + φ 0
    linarith
  · intro i
    change 0 < kakeyaExt φ i.succ - kakeyaExt φ i.castSucc
    rcases eq_or_ne i (Fin.last m) with hi | hi
    · subst hi
      have h1 : kakeyaExt φ (Fin.last m).succ = 0 := by
        unfold kakeyaExt
        have heq : (Fin.last m).succ = Fin.last (m + 1) := by apply Fin.ext; simp
        rw [heq, Fin.snoc_last]
      have h2 : kakeyaExt φ (Fin.last m).castSucc = φ (Fin.last m) := by
        unfold kakeyaExt; rw [Fin.snoc_castSucc]
      rw [h1, h2]; linarith
    · have hilt : (i : ℕ) < m := by
        have hine : (i : ℕ) ≠ m := by
          intro he; apply hi; apply Fin.ext; simpa using he
        have := i.isLt
        omega
      have h1 : kakeyaExt φ i.succ = φ ⟨(i : ℕ) + 1, by omega⟩ := by
        unfold kakeyaExt
        have heq : i.succ = (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)).castSucc := by
          apply Fin.ext; simp
        rw [heq, Fin.snoc_castSucc]
      have h2 : kakeyaExt φ i.castSucc = φ i := by unfold kakeyaExt; rw [Fin.snoc_castSucc]
      rw [h1, h2]
      have hlt : i < (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)) := by simp [Fin.lt_def]
      linarith [hmono hlt]

theorem sum_kakeyaDiff_eq_one {m : ℕ} (φ : Fin (m + 1) → ℝ) :
    ∑ I : Fin (m + 2), kakeyaDiff φ I = 1 := by
  unfold kakeyaDiff
  rw [Fin.sum_cons, sum_succ_sub_castSucc_eq]
  unfold kakeyaExt
  rw [Fin.snoc_last]
  have h0eq : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := by apply Fin.ext; simp
  rw [h0eq, Fin.snoc_castSucc]
  ring

theorem kakeya_reversal {m : ℕ} (φ : Fin (m + 1) → ℝ) {α : ℂ} (hα0 : α ≠ 0)
    (hα : α ^ (m + 1) = ∑ i : Fin (m + 1), (φ i : ℂ) * α ^ (m - (i : ℕ))) :
    (1 : ℂ) = ∑ i : Fin (m + 1), (φ i : ℂ) * (α⁻¹) ^ ((i : ℕ) + 1) := by
  have hne : (α ^ (m + 1) : ℂ) ≠ 0 := pow_ne_zero _ hα0
  have hmul : α ^ (m + 1) * (1 - ∑ i : Fin (m + 1), (φ i : ℂ) * (α⁻¹) ^ ((i : ℕ) + 1))
      = α ^ (m + 1) - ∑ i : Fin (m + 1), (φ i : ℂ) * α ^ (m - (i : ℕ)) := by
    rw [mul_sub, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i : ℕ) < m + 1 := i.isLt
    have hexp : α ^ (m + 1) * (α⁻¹) ^ ((i : ℕ) + 1) = α ^ (m - (i : ℕ)) := by
      rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hα0), ← pow_add]
      congr 1
      omega
    calc α ^ (m + 1) * ((φ i : ℂ) * (α⁻¹) ^ ((i : ℕ) + 1))
        = (φ i : ℂ) * (α ^ (m + 1) * (α⁻¹) ^ ((i : ℕ) + 1)) := by ring
      _ = (φ i : ℂ) * α ^ (m - (i : ℕ)) := by rw [hexp]
  have hzero : α ^ (m + 1) - ∑ i : Fin (m + 1), (φ i : ℂ) * α ^ (m - (i : ℕ)) = 0 := by
    rw [hα]; ring
  rw [hzero] at hmul
  have hfact := mul_eq_zero.mp hmul
  rcases hfact with h | h
  · exact absurd h hne
  · exact sub_eq_zero.mp h

theorem sum_kakeyaDiff_mul_pow {m : ℕ} (φ : Fin (m + 1) → ℝ) (z : ℂ) :
    ∑ I : Fin (m + 2), (kakeyaDiff φ I : ℂ) * z ^ ((I : ℕ) + 1)
      = z + (∑ i : Fin (m + 1), (φ i : ℂ) * z ^ ((i : ℕ) + 1))
          - z * (∑ i : Fin (m + 1), (φ i : ℂ) * z ^ ((i : ℕ) + 1)) := by
  set T : ℂ := ∑ i : Fin (m + 1), (φ i : ℂ) * z ^ (i : ℕ) with hT_def
  set S : ℂ := ∑ i : Fin (m + 1), (φ i : ℂ) * z ^ ((i : ℕ) + 1) with hS_def
  have hST : S = z * T := by
    rw [hS_def, hT_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsplit : ∑ I : Fin (m + 2), (kakeyaDiff φ I : ℂ) * z ^ ((I : ℕ) + 1)
      = (kakeyaDiff φ 0 : ℂ) * z
        + ∑ i : Fin (m + 1), (kakeyaDiff φ i.succ : ℂ) * z ^ ((i : ℕ) + 2) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, zero_add, pow_one, Fin.val_succ]
  rw [hsplit]
  have hd0 : kakeyaDiff φ 0 = 1 + φ 0 := by unfold kakeyaDiff; simp
  have hdsucc : ∀ i : Fin (m + 1),
      kakeyaDiff φ i.succ = kakeyaExt φ i.succ - kakeyaExt φ i.castSucc := by
    intro i; unfold kakeyaDiff; simp
  rw [hd0]
  simp_rw [hdsucc]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hA : ∑ i : Fin (m + 1), (kakeyaExt φ i.castSucc : ℂ) * z ^ ((i : ℕ) + 2) = z ^ 2 * T := by
    rw [hT_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have heq : kakeyaExt φ i.castSucc = φ i := by unfold kakeyaExt; rw [Fin.snoc_castSucc]
    rw [heq]; ring
  have hTfull : ∑ J : Fin (m + 2), (kakeyaExt φ J : ℂ) * z ^ (J : ℕ) = T := by
    rw [hT_def, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hlast : (kakeyaExt φ (Fin.last (m + 1)) : ℂ) * z ^ (m + 1 : ℕ) = 0 := by
      have heq : kakeyaExt φ (Fin.last (m + 1)) = 0 := by unfold kakeyaExt; rw [Fin.snoc_last]
      rw [heq]; simp
    rw [hlast, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    have heq : kakeyaExt φ i.castSucc = φ i := by unfold kakeyaExt; rw [Fin.snoc_castSucc]
    rw [heq]
  have hreindex : ∑ i : Fin (m + 1), (kakeyaExt φ i.succ : ℂ) * z ^ ((i : ℕ) + 1)
      = T - (φ 0 : ℂ) := by
    have hexpand : ∑ J : Fin (m + 2), (kakeyaExt φ J : ℂ) * z ^ (J : ℕ)
        = (kakeyaExt φ 0 : ℂ) * z ^ (0 : ℕ)
          + ∑ i : Fin (m + 1), (kakeyaExt φ i.succ : ℂ) * z ^ ((i : ℕ) + 1) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
    rw [hTfull] at hexpand
    have hphi0 : kakeyaExt φ (0 : Fin (m + 2)) = φ 0 := by
      unfold kakeyaExt
      have h0eq : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := by apply Fin.ext; simp
      rw [h0eq, Fin.snoc_castSucc]
    rw [hphi0] at hexpand
    simp only [pow_zero, mul_one] at hexpand
    linear_combination -hexpand
  have hB : ∑ i : Fin (m + 1), (kakeyaExt φ i.succ : ℂ) * z ^ ((i : ℕ) + 2) = z * (T - φ 0) := by
    rw [← hreindex, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hA, hB, hST]
  ring

/-- **`prop:kakeya`**: `-1<φ_1<⋯<φ_p<0` ならば `φ` は定常。 -/
theorem isStationary_of_kakeya {m : ℕ} {φ : Fin (m + 1) → ℝ} (hmono : StrictMono φ)
    (h0 : -1 < φ 0) (hlast : φ (Fin.last m) < 0) : IsStationary φ := by
  intro α hα
  by_contra hcon
  rw [not_lt] at hcon
  have hα0 : α ≠ 0 := by
    intro h; rw [h] at hcon; simp at hcon; linarith
  set z : ℂ := α⁻¹ with hz_def
  have hαpos : 0 < ‖α‖ := lt_of_lt_of_le one_pos hcon
  have hzle : ‖z‖ ≤ 1 := by
    rw [hz_def, norm_inv, inv_le_one₀ hαpos]
    exact hcon
  have hS1 : (1 : ℂ) = ∑ i : Fin (m + 1), (φ i : ℂ) * z ^ ((i : ℕ) + 1) :=
    kakeya_reversal φ hα0 hα
  have heq1 : (1 : ℂ) = ∑ I : Fin (m + 2), (kakeyaDiff φ I : ℂ) * z ^ ((I : ℕ) + 1) := by
    rw [sum_kakeyaDiff_mul_pow φ z, ← hS1]; ring
  have hz1 : z = 1 :=
    eq_one_of_norm_le_one_of_sum_eq_one (kakeyaDiff φ) (kakeyaDiff_pos hmono h0 hlast)
      (sum_kakeyaDiff_eq_one φ) z hzle heq1
  rw [hz1] at hS1
  simp only [one_pow, mul_one] at hS1
  have hS1' : (1 : ℝ) = ∑ i : Fin (m + 1), φ i := by exact_mod_cast hS1
  have hall_neg : ∀ i : Fin (m + 1), φ i < 0 := by
    intro i
    have hle : φ i ≤ φ (Fin.last m) := hmono.monotone (Fin.le_last i)
    linarith
  have hne : (Finset.univ : Finset (Fin (m + 1))).Nonempty := Finset.univ_nonempty
  have hsumneg : ∑ i : Fin (m + 1), φ i < 0 := Finset.sum_neg (fun i _ => hall_neg i) hne
  linarith

end StTopology
