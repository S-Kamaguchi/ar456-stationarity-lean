import Mathlib
import StTopology.StationarityRegions
import StTopology.StepDown

set_option linter.style.header false

/-!
# 次数拡張性 (`prop:zero-ext`, `5_kanren.tex` Section 3.1)

`p φ = (φ_1,…,φ_p)` が `AR(p)` で定常 ⟺ `p+1 φ = (φ_1,…,φ_p,0)` が `AR(p+1)` で定常。

論文の議論: `p+1 φ` の逆特性多項式は
`x^{p+1} - (φ_1 x^p + ⋯ + φ_p x + 0) = x·[x^p - (φ_1 x^{p-1} + ⋯ + φ_p)] = x·φ̃(x)`
と分解される。根の集合は `{0} ∪ {φ̃ の根}` であり `|0| < 1` は常に成り立つので、
「全ての根が単位円内」は両辺で同値になる。

Lean では `p+1 φ = Fin.snoc φ 0 : Fin (p+1) → ℝ` として定式化する。`⇒` 方向
(`ψ` が定常なら `(ψ,0)` も定常) は既に `StepDown.lean` の `isStationary_snoc_zero_gen`
として一般 `n` について示されている。ここでは `⇐` 方向 (`isStationary_of_snoc_zero`)
を新たに示し、両方向を `isStationary_snoc_zero_iff` としてまとめる。
-/

open Finset StTopology

namespace StTopology

/-- `⇐` 方向: `(ψ,0)` が定常ならば `ψ` も定常 (`isStationary_snoc_zero_gen` の逆)。
根の対応で言えば、`x·φ̃(x)` の根から `0` を除いたものが `φ̃` の根そのものである、
という議論に対応する代数計算 (`α` が `ψ` の根なら、両辺に `α` を掛けて
`snoc ψ 0` の根の等式が得られる)。 -/
theorem isStationary_of_snoc_zero {p : ℕ} {ψ : Fin p → ℝ}
    (hψ : IsStationary (Fin.snoc ψ (0 : ℝ) : Fin (p + 1) → ℝ)) : IsStationary ψ := by
  intro α hα
  apply hψ
  -- α^{p+1} = ∑_{i:Fin p} ψ_i α^{p-i} (両辺に α を掛けて指数を1つ上げる)
  have hα' : α ^ (p + 1) = ∑ i : Fin p, (ψ i : ℂ) * α ^ (p - (i : ℕ)) := by
    have hstep : α * α ^ p = α * ∑ i : Fin p, (ψ i : ℂ) * α ^ (p - 1 - (i : ℕ)) := by
      rw [hα]
    have hsum : α * ∑ i : Fin p, (ψ i : ℂ) * α ^ (p - 1 - (i : ℕ))
        = ∑ i : Fin p, (ψ i : ℂ) * α ^ (p - (i : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hexp : p - (i : ℕ) = 1 + (p - 1 - (i : ℕ)) := by have := i.isLt; omega
      rw [hexp, pow_add]; ring
    calc α ^ (p + 1) = α * α ^ p := by ring
      _ = α * ∑ i : Fin p, (ψ i : ℂ) * α ^ (p - 1 - (i : ℕ)) := hstep
      _ = ∑ i : Fin p, (ψ i : ℂ) * α ^ (p - (i : ℕ)) := hsum
  -- `Fin.snoc ψ 0` の逆特性方程式に書き換える
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Complex.ofReal_zero, zero_mul, add_zero]
  rw [hα']
  apply Finset.sum_congr rfl
  intro i _
  have hidx : p + 1 - 1 - ((i.castSucc : Fin (p + 1)) : ℕ) = p - (i : ℕ) := by
    simp
  rw [hidx]

/-- **`prop:zero-ext`**: `φ` が `AR(p)` で定常であることと `(φ,0)` が `AR(p+1)` で定常
であることは同値。 -/
theorem isStationary_snoc_zero_iff {p : ℕ} {φ : Fin p → ℝ} :
    IsStationary φ ↔ IsStationary (Fin.snoc φ (0 : ℝ) : Fin (p + 1) → ℝ) :=
  ⟨isStationary_snoc_zero_gen, isStationary_of_snoc_zero⟩

/-! ## `l` 個のゼロ拡張への一般化 (`2_kanren.tex` Section 2.3 の地の文)

`φ_p = ⋯ = φ_{p-l+1} = 0` (`1≤l≤p-1`) のとき、`(φ_1,…,φ_p)` の定常性は
`AR(p-l)` の `(φ_1,…,φ_{p-l})` の定常性に帰着する、という `prop:zero-ext`
(`l=1` の場合)の一般化。論文の議論: 逆特性多項式は
`φ̃(x) = x^p - (φ_1x^{p-1}+⋯+φ_{p-l}x^l) = x^l·{x^{p-l}-(φ_1x^{p-l-1}+⋯+φ_{p-l})}`
と分解されるので、`l` は根 `x=0` の重複度に対応し、残りの根が `AR(p-l)` の
逆特性方程式の根に対応する。

Lean では `padZeros l φ : Fin (n+l) → ℝ` (`φ:Fin n→ℝ` の末尾に `l` 個の `0` を
追加したもの、`Fin.snoc` を `l` 回ネストして構成) を定義し、`isStationary_snoc_zero_iff`
を `l` に関する帰納法で `l` 回合成するだけで示せる (`l=1` の場合が `prop:zero-ext`
そのものに一致することは `padZeros 1 φ = Fin.snoc φ 0` から直ちに従う)。 -/

/-- `φ : Fin n → ℝ` の末尾に `l` 個の `0` を追加した `Fin (n+l) → ℝ`
(`Fin.snoc` を `l` 回ネスト)。`padZeros 0 φ = φ`、
`padZeros (l+1) φ = Fin.snoc (padZeros l φ) 0`。 -/
noncomputable def padZeros {n : ℕ} : (l : ℕ) → (Fin n → ℝ) → (Fin (n + l) → ℝ)
  | 0, φ => φ
  | l + 1, φ => Fin.snoc (padZeros l φ) 0

/-- `padZeros 1 φ` は `prop:zero-ext` の `Fin.snoc φ 0` そのもの。 -/
theorem padZeros_one {n : ℕ} (φ : Fin n → ℝ) :
    padZeros 1 φ = Fin.snoc φ (0 : ℝ) := rfl

/-- **`prop:zero-ext` の一般化**(`2_kanren.tex` Section 2.3 の地の文): `φ` が定常である
ことと、末尾に `l` 個 `0` を追加した `padZeros l φ` が定常であることは同値。`l=1` の
場合が `isStationary_snoc_zero_iff`(`prop:zero-ext`)そのもの。 -/
theorem isStationary_padZeros_iff {n : ℕ} (l : ℕ) (φ : Fin n → ℝ) :
    IsStationary φ ↔ IsStationary (padZeros l φ) := by
  induction l with
  | zero => exact Iff.rfl
  | succ l ih => exact ih.trans isStationary_snoc_zero_iff

end StTopology
