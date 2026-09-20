import Mathlib
import StTopology.StationarityRegions

set_option linter.style.header false

/-!
# 次元倍加性 (`prop:dim-mult`, `5_kanren.tex` Section 3.3)

`m ≥ 1` に対し、`φ = (φ_1,…,φ_p)` が `AR(p)` で定常であることと、`Fin (p*m) → ℝ` の
係数列であって位置 `k*m` (1-indexed, `k=1,…,p`) に `φ_k`、それ以外に `0` を置いたもの
(`pm φ`) が `AR(pm)` で定常であることは同値。

論文の議論: `pm φ` の逆特性多項式は
`x^{pm} - ∑_k φ_k x^{pm-km} = (x^m)^p - ∑_k φ_k (x^m)^{p-k} = φ̃(x^m)`
と分解される。`x` が `AR(pm)` の根であることと `w:=x^m` が `φ̃` の根であることは
同値で(複素数体は代数閉体なので `w` の `m` 乗根 `x` は必ず存在する)、
`|x|<1 ⟺ |x|^m<1 ⟺ |w|<1` (`t↦t^m` が `t≥0` で狭義単調増加、`m≥1`) なので、
「全ての根が単位円内」は両辺で同値になる。
-/

open Finset StTopology

namespace StTopology

/-- `dimMult φ m` : 位置 `(i+1)*m-1` (0-indexed, `i:Fin p`) に `φ i` を置き、それ以外を `0`
とした `Fin (p*m) → ℝ` の係数列 (`prop:dim-mult` の `pm φ`)。 -/
def dimMult {p : ℕ} (φ : Fin p → ℝ) (m : ℕ) : Fin (p * m) → ℝ :=
  fun j => if _h : m ∣ ((j : ℕ) + 1) then
      (if hk : ((j : ℕ) + 1) / m - 1 < p then φ ⟨((j : ℕ) + 1) / m - 1, hk⟩ else 0)
    else 0

/-- `dimMult` の値を持つ位置への埋め込み `Fin p → Fin (p*m)`, `i ↦ i*m + (m-1)`
(0-indexed。1-indexed では `(i+1)*m`)。 -/
def dimMultIdx {p : ℕ} (m : ℕ) (hm : 0 < m) (i : Fin p) : Fin (p * m) :=
  ⟨(i : ℕ) * m + (m - 1), by
    have h1 : (i : ℕ) + 1 ≤ p := i.isLt
    have h2 : (i : ℕ) * m + (m - 1) < (i : ℕ) * m + m := by omega
    have h3 : (i : ℕ) * m + m = ((i : ℕ) + 1) * m := by ring
    have h4 : ((i : ℕ) + 1) * m ≤ p * m := by gcongr
    omega⟩

theorem dimMultIdx_val {p : ℕ} (m : ℕ) (hm : 0 < m) (i : Fin p) :
    ((dimMultIdx m hm i : Fin (p * m)) : ℕ) = (i : ℕ) * m + (m - 1) := rfl

/-- `dimMult φ m` は埋め込んだ位置ではもとの `φ` の値をとる。 -/
theorem dimMult_dimMultIdx {p : ℕ} (φ : Fin p → ℝ) (m : ℕ) (hm : 0 < m) (i : Fin p) :
    dimMult φ m (dimMultIdx m hm i) = φ i := by
  have hi := i.isLt
  have hval : ((dimMultIdx m hm i : Fin (p * m)) : ℕ) + 1 = ((i : ℕ) + 1) * m := by
    rw [dimMultIdx_val]
    have h4 : (i : ℕ) * m + (m - 1) + 1 = (i : ℕ) * m + m := by omega
    rw [h4]; ring
  unfold dimMult
  rw [hval]
  have hdvd : m ∣ ((i : ℕ) + 1) * m := ⟨(i : ℕ) + 1, by ring⟩
  rw [dif_pos hdvd]
  have hquot : ((i : ℕ) + 1) * m / m = (i : ℕ) + 1 := Nat.mul_div_cancel _ hm
  rw [hquot]
  have hk : (i : ℕ) + 1 - 1 < p := by omega
  rw [dif_pos hk]
  congr 1

/-- 埋め込んだ位置以外では `dimMult φ m` は `0`。 -/
theorem dimMult_eq_zero_of_not_mem {p : ℕ} (φ : Fin p → ℝ) (m : ℕ) (hm : 0 < m)
    (j : Fin (p * m)) (hj : j ∉ Finset.univ.image (dimMultIdx m hm)) :
    dimMult φ m j = 0 := by
  unfold dimMult
  split_ifs with h hk
  · exfalso
    apply hj
    rw [Finset.mem_image]
    refine ⟨⟨((j : ℕ) + 1) / m - 1, hk⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change (((j : ℕ) + 1) / m - 1) * m + (m - 1) = (j : ℕ)
    have hdm : ((j : ℕ) + 1) / m * m = (j : ℕ) + 1 := Nat.div_mul_cancel h
    have hge1 : 1 ≤ ((j : ℕ) + 1) / m := by
      rcases Nat.eq_zero_or_pos (((j : ℕ) + 1) / m) with h0 | h0
      · rw [h0] at hdm; omega
      · exact h0
    have hQm : m ≤ ((j : ℕ) + 1) / m * m := by
      calc m = 1 * m := (one_mul m).symm
        _ ≤ ((j : ℕ) + 1) / m * m := Nat.mul_le_mul_right m hge1
    rw [Nat.sub_mul, one_mul]
    omega
  · rfl
  · rfl

/-- `dimMult φ m` の逆特性多項式は `x^m` を代入した `φ` の逆特性多項式に一致する:
`∑_{j:Fin(pm)} (dimMult φ m)_j x^{pm-1-j} = ∑_{i:Fin p} φ_i (x^m)^{p-1-i}`。 -/
theorem sum_dimMult_eq {p : ℕ} (φ : Fin p → ℝ) (m : ℕ) (hm : 0 < m) (x : ℂ) :
    ∑ j : Fin (p * m), (dimMult φ m j : ℂ) * x ^ (p * m - 1 - (j : ℕ))
      = ∑ i : Fin p, (φ i : ℂ) * (x ^ m) ^ (p - 1 - (i : ℕ)) := by
  have hsubset : Finset.univ.image (dimMultIdx m hm) ⊆ (Finset.univ : Finset (Fin (p * m))) :=
    Finset.subset_univ _
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin (p * m))),
      j ∉ Finset.univ.image (dimMultIdx m hm) →
      (dimMult φ m j : ℂ) * x ^ (p * m - 1 - (j : ℕ)) = 0 := by
    intro j _ hj
    rw [dimMult_eq_zero_of_not_mem φ m hm j hj]
    simp
  rw [← Finset.sum_subset hsubset hzero]
  have hinj : Function.Injective (dimMultIdx (p := p) m hm) := by
    intro a b hab
    apply Fin.ext
    have hcoe := congrArg (fun x : Fin (p * m) => (x : ℕ)) hab
    simp only [dimMultIdx_val] at hcoe
    have heq : (a : ℕ) * m = (b : ℕ) * m := by omega
    exact Nat.eq_of_mul_eq_mul_right hm heq
  rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
  apply Finset.sum_congr rfl
  intro i _
  rw [dimMult_dimMultIdx φ m hm i]
  congr 1
  rw [dimMultIdx_val]
  have hi := i.isLt
  have hexp : p * m - 1 - ((i : ℕ) * m + (m - 1)) = (p - 1 - (i : ℕ)) * m := by
    have h2 : ((i : ℕ) + 1) * m ≤ p * m := by gcongr; omega
    have h3 : (p - 1 - (i : ℕ)) * m = p * m - (i : ℕ) * m - m := by
      rw [Nat.sub_mul, Nat.sub_mul, one_mul]
      omega
    have h5 : ((i : ℕ) + 1) * m = (i : ℕ) * m + m := by ring
    omega
  rw [hexp, mul_comm (p - 1 - (i : ℕ)) m, pow_mul]

/-- **`prop:dim-mult`**: `φ` が `AR(p)` で定常であることと、`dimMult φ m` が `AR(pm)` で
定常であることは同値 (`m ≥ 1`)。 -/
theorem isStationary_dimMult_iff {p : ℕ} (φ : Fin p → ℝ) (m : ℕ) (hm : 0 < m) :
    IsStationary φ ↔ IsStationary (dimMult φ m) := by
  constructor
  · intro hφ α hα
    have hβ : (α ^ m) ^ p = ∑ i : Fin p, (φ i : ℂ) * (α ^ m) ^ (p - 1 - (i : ℕ)) := by
      rw [← sum_dimMult_eq φ m hm α, ← hα]
      ring
    have hnorm := hφ (α ^ m) hβ
    rw [norm_pow] at hnorm
    by_contra hcon
    rw [not_lt] at hcon
    have : (1 : ℝ) ≤ ‖α‖ ^ m := one_le_pow₀ hcon
    linarith
  · intro hψ β hβ
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq β hm
    have hcontra : α ^ (p * m)
        = ∑ j : Fin (p * m), (dimMult φ m j : ℂ) * α ^ (p * m - 1 - (j : ℕ)) := by
      rw [sum_dimMult_eq φ m hm α, hα, ← hβ, ← hα, ← pow_mul, Nat.mul_comm m p]
    have hres := hψ α hcontra
    have hβnorm : ‖β‖ = ‖α‖ ^ m := by rw [← hα, norm_pow]
    rw [hβnorm]
    exact pow_lt_one₀ (norm_nonneg α) hres (by omega)

end StTopology
