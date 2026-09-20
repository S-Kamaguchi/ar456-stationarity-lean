import Mathlib
import StTopology.StationarityRegions

set_option linter.style.header false

/-!
# 符号交代対称性 (`prop:sign-sym`, `5_kanren.tex` Section 3.2)

任意の `p ≥ 0` (論文では `p ≥ 1` だが証明はこの仮定を使わない) に対し、
`φ = (φ_1,…,φ_p)` が定常であることと、`ψ = (-φ_1, φ_2, -φ_3, …, (-1)^p φ_p)`
(`ψ_m = (-1)^m φ_m`) が定常であることは同値。

論文の議論: 逆特性多項式について `φ̃(-x) = (-1)^p ψ̃(x)` が成り立つので、
`ψ̃` の根はちょうど `{-z : φ̃(z)=0}` であり、`|-z|=|z|` なので
「全ての根が単位円内」は両辺で同値になる。

Lean での定式化: `signFlip φ i := (-1)^{i+1} φ_i` (0-indexed `i`, 論文の1始まり添字
`m=i+1` に対応)。`signFlip` は対合 (`signFlip (signFlip φ) = φ`) なので、片方向
(`isStationary_signFlip`: `φ` 定常 ⟹ `signFlip φ` 定常) だけ直接示せば、対合性から
`iff` が従う。
-/

open Finset StTopology

namespace StTopology

/-- 符号反転変換: `ψ_i = (-1)^{i+1} φ_i` (0-indexed `i`; 論文の1始まり添字 `m=i+1` に対応)。 -/
def signFlip {p : ℕ} (φ : Fin p → ℝ) : Fin p → ℝ :=
  fun i => (-1 : ℝ) ^ ((i : ℕ) + 1) * φ i

/-- `signFlip` は対合: 2回適用すると元に戻る (`(-1)^{2(i+1)}=1` より)。 -/
theorem signFlip_signFlip {p : ℕ} (φ : Fin p → ℝ) : signFlip (signFlip φ) = φ := by
  funext i
  unfold signFlip
  rw [← mul_assoc, ← pow_add]
  have h2 : (-1 : ℝ) ^ (((i : ℕ) + 1) + ((i : ℕ) + 1)) = 1 := by
    rw [← two_mul, pow_mul]; norm_num
  rw [h2, one_mul]

/-- `⇒` 方向: `φ` が定常ならば `signFlip φ` も定常。`β` が `signFlip φ` の逆特性方程式の根
なら、`-β` が `φ` の逆特性方程式の根になる (`(-1)^{p-1-i}·(-1)^{i+1}=(-1)^p` を使う純代数)、
という計算で示す。 -/
theorem isStationary_signFlip {p : ℕ} {φ : Fin p → ℝ} (hφ : IsStationary φ) :
    IsStationary (signFlip φ) := by
  intro β hβ
  have hα : (-β) ^ p = ∑ i : Fin p, (φ i : ℂ) * (-β) ^ (p - 1 - (i : ℕ)) := by
    have key : ∀ i : Fin p, (φ i : ℂ) * (-β) ^ (p - 1 - (i : ℕ))
        = (-1 : ℂ) ^ p * ((signFlip φ i : ℂ) * β ^ (p - 1 - (i : ℕ))) := by
      intro i
      have hi := i.isLt
      have hsplit : (-1 : ℂ) ^ (p - 1 - (i : ℕ)) * (-1 : ℂ) ^ ((i : ℕ) + 1) = (-1 : ℂ) ^ p := by
        rw [← pow_add]; congr 1; omega
      have hself : (-1 : ℂ) ^ ((i : ℕ) + 1) * (-1 : ℂ) ^ ((i : ℕ) + 1) = 1 := by
        rw [← pow_add]
        have heq : (i : ℕ) + 1 + ((i : ℕ) + 1) = 2 * ((i : ℕ) + 1) := by ring
        rw [heq, pow_mul]; norm_num
      -- `(-1)^(p-1-i)` を `(-1)^p * (-1)^(i+1)` の形に書き換える (`hsplit` を `(-1)^(i+1)` 倍し、
      -- `hself` で自乗を消す)
      have hsplit2 : (-1 : ℂ) ^ (p - 1 - (i : ℕ)) = (-1 : ℂ) ^ p * (-1 : ℂ) ^ ((i : ℕ) + 1) := by
        linear_combination (-1 : ℂ) ^ ((i : ℕ) + 1) * hsplit
          - (-1 : ℂ) ^ (p - 1 - (i : ℕ)) * hself
      have hφi : (signFlip φ i : ℝ) = (-1 : ℝ) ^ ((i : ℕ) + 1) * φ i := rfl
      calc (φ i : ℂ) * (-β) ^ (p - 1 - (i : ℕ))
          = (φ i : ℂ) * ((-1 : ℂ) ^ (p - 1 - (i : ℕ)) * β ^ (p - 1 - (i : ℕ))) := by
            rw [neg_pow]
        _ = (-1 : ℂ) ^ p
            * (((-1 : ℝ) ^ ((i : ℕ) + 1) * φ i : ℝ) * β ^ (p - 1 - (i : ℕ))) := by
            push_cast
            rw [hsplit2]; ring
        _ = (-1 : ℂ) ^ p * ((signFlip φ i : ℂ) * β ^ (p - 1 - (i : ℕ))) := by rw [hφi]
    calc (-β) ^ p = (-1 : ℂ) ^ p * β ^ p := by rw [neg_pow]
      _ = (-1 : ℂ) ^ p * ∑ i : Fin p, (signFlip φ i : ℂ) * β ^ (p - 1 - (i : ℕ)) := by rw [hβ]
      _ = ∑ i : Fin p, (-1 : ℂ) ^ p * ((signFlip φ i : ℂ) * β ^ (p - 1 - (i : ℕ))) := by
          rw [Finset.mul_sum]
      _ = ∑ i : Fin p, (φ i : ℂ) * (-β) ^ (p - 1 - (i : ℕ)) := by
          apply Finset.sum_congr rfl; intro i _; rw [key i]
  have hres := hφ (-β) hα
  simpa using hres

/-- **`prop:sign-sym`**: `φ` が定常であることと `signFlip φ` が定常であることは同値。 -/
theorem isStationary_signFlip_iff {p : ℕ} {φ : Fin p → ℝ} :
    IsStationary φ ↔ IsStationary (signFlip φ) := by
  constructor
  · exact isStationary_signFlip
  · intro h
    have := isStationary_signFlip h
    rwa [signFlip_signFlip] at this

end StTopology
