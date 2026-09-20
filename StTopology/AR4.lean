import Mathlib
import StTopology.StationarityRegions
import StTopology.MaximalComponentPrinciple
import StTopology.StOpen
import StTopology.StConnected
import StTopology.RootPerturbation
import StTopology.VietaBound
import StTopology.AR3

set_option linter.style.header false

/-!
# AR(4) の定常性: 明示的閉形式条件との同値性

`6_kanren.tex`, Section 4.4 の議論を、`AR3.lean` と同型の方針
(Ω4 の定義 → `L41 := connectedComponentIn Ω4 O4` → 最大連結成分の原理 →
`L41 = IsStationary` → connectedness による符号復元) で形式化する。

論文との相違点 (ユーザーとの確認済み):
* hypothesis (a) (`St(4)⊆Ω4`) は、論文の Schur–Cohn 再帰 + `St(3)` 経由の議論ではなく、
  `AR3.lean` の `cplxCond_ne_zero_of_isStationary` と同型の「直接分解」方式で示す:
  `cplxCond4 φ = 0` かつ `1+φ_4≠0` (`abs_last_coeff_lt_one` から) を仮定すると、
  4次式が `(z²-Xz+1)(z²-az-φ_4)` に分解でき、`z²-Xz+1` の2根の積が1になるので
  両方 `‖z‖<1` はあり得ない。
* 4番目の条件 `2(1+φ_4)>|φ_1-φ_3|` の必要性は、論文の圧縮された記述
  (`2(1+φ_4)=φ_1-φ_3` "would force" `φ(1)=0`) を、次の恒等式として厳密化する:
  `2(1+φ_4)=φ_1-φ_3` ⟹ `cplxCond4 φ = -(1+φ_4)²・φ(1)`。
  `L41` 上では既に `cplxCond4>0` と `φ(1)>0` が確立しているので、この恒等式から
  直接矛盾が出る (`-2(1+φ_4)=φ_1-φ_3` の場合は `φ(-1)` 版)。
* hypothesis (b) (単位円上の非実根 ⟹ `cplxCond4=0`) も、論文の
  `θ`/Chebyshev 経由ではなく、`z,w=z̄` を直接使う複素代数
  (`z²=uz-1` (`u=z+w`, `zw=1`), これを繰り返し使って `z³,z⁴` を `u` の1次式に還元し、
  `hroot` に代入して `A・z+B=0` (`A,B` は `u,φ` の実多項式) の形にし、
  `z` が非実なので `A=0∧B=0` を得る) で行う。

添字対応は `StationarityRegions.lean` と同じ: `φ 0 = φ_1, φ 1 = φ_2, φ 2 = φ_3, φ 3 = φ_4`。
-/

open Finset StTopology

namespace StTopology

/-- `Q := (φ_3+φ_1φ_4)(φ_1-φ_3)+(1+φ_4)²(1+φ_2-φ_4)`。`St4` の3番目の条件の左辺そのもの。
論文の `P` の符号反転版 (`P+Q=0` が恒等式として成り立つ, 後述)。 -/
def cplxCond4 (φ : Fin 4 → ℝ) : ℝ :=
  (φ 2 + φ 0 * φ 3) * (φ 0 - φ 2) + (1 + φ 3) ^ 2 * (1 + φ 1 - φ 3)

/-- Ω4: 論文の `Ω = {φ(1)≠0, φ(-1)≠0, (複素根条件)≠0}` にあたる開集合。 -/
def Ω4 : Set (Fin 4 → ℝ) :=
  {φ : Fin 4 → ℝ | phiAt1 φ ≠ 0 ∧ phiAtNeg1 φ ≠ 0 ∧ cplxCond4 φ ≠ 0}

/-- 原点 `O_4` は `Ω4` に属する: `φ(1)=1≠0`, `φ(-1)=1≠0`, `cplxCond4=1≠0`。 -/
theorem zero_mem_Ω4 : (fun _ : Fin 4 => (0 : ℝ)) ∈ Ω4 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [phiAt1, phiAtNeg1, cplxCond4]

/-- `L_{4,1}`: `Ω4` 内で原点 `O_4` を含む最大の連結成分。 -/
def L41 : Set (Fin 4 → ℝ) :=
  connectedComponentIn Ω4 (fun _ : Fin 4 => (0 : ℝ))

/-- AR(4) の逆特性方程式を、`Fin 4` の総和を展開した具体形に書き換える。 -/
theorem root_four_iff {φ : Fin 4 → ℝ} (α : ℂ) :
    (α ^ 4 = ∑ i : Fin 4, (φ i : ℂ) * α ^ (4 - 1 - (i : ℕ)))
      ↔ α ^ 4 = (φ 0 : ℂ) * α ^ 3 + (φ 1 : ℂ) * α ^ 2 + (φ 2 : ℂ) * α + (φ 3 : ℂ) := by
  simp only [Fin.sum_univ_four]
  norm_num

/-! ### hypothesis (a) の3つの部品 -/

theorem phiAt1_ne_zero_of_isStationary4 {φ : Fin 4 → ℝ} (hφ : IsStationary φ) :
    phiAt1 φ ≠ 0 := by
  intro h
  simp only [phiAt1, Fin.sum_univ_four] at h
  have hsum : φ 0 + φ 1 + φ 2 + φ 3 = 1 := by linarith
  have hsumC : (φ 0 : ℂ) + (φ 1 : ℂ) + (φ 2 : ℂ) + (φ 3 : ℂ) = 1 := by exact_mod_cast hsum
  have hroot : (1 : ℂ) ^ 4 = ∑ i : Fin 4, (φ i : ℂ) * (1 : ℂ) ^ (4 - 1 - (i : ℕ)) := by
    rw [root_four_iff]
    linear_combination -hsumC
  have hlt := hφ 1 hroot
  simp at hlt

theorem phiAtNeg1_ne_zero_of_isStationary4 {φ : Fin 4 → ℝ} (hφ : IsStationary φ) :
    phiAtNeg1 φ ≠ 0 := by
  intro h
  simp only [phiAtNeg1, Fin.sum_univ_four] at h
  norm_num at h
  have hsum : φ 0 - φ 1 + φ 2 - φ 3 = -1 := by linarith
  have hsumC : (φ 0 : ℂ) - (φ 1 : ℂ) + (φ 2 : ℂ) - (φ 3 : ℂ) = -1 := by exact_mod_cast hsum
  have hroot : (-1 : ℂ) ^ 4 = ∑ i : Fin 4, (φ i : ℂ) * (-1 : ℂ) ^ (4 - 1 - (i : ℕ)) := by
    rw [root_four_iff]
    norm_num
    linear_combination hsumC
  have hlt := hφ (-1) hroot
  simp at hlt

/-- **hypothesis (a) の核**: `cplxCond4 φ = 0` と `1+φ_4≠0` を仮定すると、4次式が
`(z²-Xz+1)(z²-(φ_1-X)z-φ_4)` (`X=(φ_1-φ_3)/(1+φ_4)`) に分解できる。`z²-Xz+1` の
2根の積は1なので、両方 `‖z‖<1` ということはあり得ず、定常性と矛盾する。
Schur–Cohn 再帰は一切使わない (`AR3.lean` の `cplxCond_ne_zero_of_isStationary` と同型)。 -/
theorem cplxCond4_ne_zero_of_isStationary {φ : Fin 4 → ℝ} (hφ : IsStationary φ) :
    cplxCond4 φ ≠ 0 := by
  intro hQ
  have h4lt1 : |φ 3| < 1 := by
    have h := abs_last_coeff_lt_one (p := 4) (by norm_num) hφ
    exact h
  have h4pos : (0 : ℝ) < 1 + φ 3 := by
    have := (abs_lt.mp h4lt1).1
    linarith
  have h4ne : (1 : ℝ) + φ 3 ≠ 0 := h4pos.ne'
  set X : ℝ := (φ 0 - φ 2) / (1 + φ 3) with hXdef
  have hX : (1 + φ 3) * X = φ 0 - φ 2 := by
    rw [hXdef]; field_simp
  have hQ' : (φ 2 + φ 0 * φ 3) * (φ 0 - φ 2) + (1 + φ 3) ^ 2 * (1 + φ 1 - φ 3) = 0 := hQ
  have hne2 : (1 + φ 3) ^ 2 ≠ 0 := pow_ne_zero 2 h4ne
  have haX : (φ 0 - X) * X = φ 3 - φ 1 - 1 := by
    apply mul_left_cancel₀ hne2
    have expand : (1 + φ 3) ^ 2 * ((φ 0 - X) * X)
        = φ 0 * ((1 + φ 3) * X) * (1 + φ 3) - ((1 + φ 3) * X) ^ 2 := by ring
    rw [expand, hX]
    nlinarith [hQ']
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq ((X : ℂ) ^ 2 - 4) (by norm_num : 0 < 2)
  set α : ℂ := ((X : ℂ) + d) / 2 with hαdef
  set β : ℂ := (X : ℂ) - α with hβdef
  have hα2 : α ^ 2 - (X : ℂ) * α + 1 = 0 := by
    rw [hαdef]; field_simp; linear_combination hd
  have hβ2 : β ^ 2 - (X : ℂ) * β + 1 = 0 := by
    rw [hβdef]; linear_combination hα2
  have hαβ : α * β = 1 := by
    rw [hβdef]; linear_combination -hα2
  have hXC : (1 + (φ 3 : ℂ)) * (X : ℂ) = (φ 0 : ℂ) - (φ 2 : ℂ) := by exact_mod_cast hX
  have haXC : ((φ 0 : ℂ) - (X : ℂ)) * (X : ℂ) = (φ 3 : ℂ) - (φ 1 : ℂ) - 1 := by exact_mod_cast haX
  have hfact : ∀ z : ℂ, z ^ 4 - (φ 0 : ℂ) * z ^ 3 - (φ 1 : ℂ) * z ^ 2 - (φ 2 : ℂ) * z - (φ 3 : ℂ)
      = (z ^ 2 - (X : ℂ) * z + 1) * (z ^ 2 - ((φ 0 : ℂ) - (X : ℂ)) * z - (φ 3 : ℂ)) := by
    intro z
    linear_combination (-z ^ 2) * haXC + (-z) * hXC
  have hrootα : α ^ 4 = ∑ i : Fin 4, (φ i : ℂ) * α ^ (4 - 1 - (i : ℕ)) := by
    rw [root_four_iff]
    linear_combination hfact α + (α ^ 2 - ((φ 0 : ℂ) - (X : ℂ)) * α - (φ 3 : ℂ)) * hα2
  have hrootβ : β ^ 4 = ∑ i : Fin 4, (φ i : ℂ) * β ^ (4 - 1 - (i : ℕ)) := by
    rw [root_four_iff]
    linear_combination hfact β + (β ^ 2 - ((φ 0 : ℂ) - (X : ℂ)) * β - (φ 3 : ℂ)) * hβ2
  have hαlt := hφ α hrootα
  have hβlt := hφ β hrootβ
  have hprod : ‖α‖ * ‖β‖ = 1 := by rw [← norm_mul, hαβ, norm_one]
  nlinarith [norm_nonneg α, norm_nonneg β, hαlt, hβlt, hprod]

theorem isStationary_mem_Ω4 {φ : Fin 4 → ℝ} (hφ : IsStationary φ) : φ ∈ Ω4 :=
  ⟨phiAt1_ne_zero_of_isStationary4 hφ, phiAtNeg1_ne_zero_of_isStationary4 hφ,
    cplxCond4_ne_zero_of_isStationary hφ⟩

/-! ### hypothesis (b) の代数的核 -/

/-- `z` が単位円上の非実根なら `cplxCond4 φ = 0`。`w=z̄` とおき、`u:=z+w` (実数) を使うと
`z²=uz-1` (`zw=1` から) が成り立つので、これを繰り返し使って `z³,z⁴` を `u` の1次式に
還元でき、`hroot` に代入すると `A・z+B=0` (`A,B` は `u,φ` の実多項式) の形になる。
`z` が非実なので `A=0∧B=0`。これが論文の実部/虚部の2条件 (二次式(I)・一次式(B)) に
あたり、あとは `u` を消去すれば `cplxCond4 φ = 0` が出る。 -/
theorem cplxCond4_eq_zero_of_unit_root_of_ne {φ : Fin 4 → ℝ} (z : ℂ)
    (hroot : z ^ 4 = (φ 0 : ℂ) * z ^ 3 + (φ 1 : ℂ) * z ^ 2 + (φ 2 : ℂ) * z + (φ 3 : ℂ))
    (hnorm : ‖z‖ = 1) (hne : z ≠ (starRingEnd ℂ) z) :
    cplxCond4 φ = 0 := by
  set w : ℂ := (starRingEnd ℂ) z with hw
  have hzw : z * w = 1 := by
    rw [hw, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
  have hzim : z.im ≠ 0 := by
    intro h0
    apply hne
    rw [hw]
    apply Complex.ext
    · simp
    · simp [h0]
  set u : ℝ := 2 * z.re with hu_def
  have hu : (u : ℂ) = z + w := by
    rw [hu_def, hw]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.conj_re, Complex.add_im, Complex.conj_im] <;> ring
  have hz2 : z ^ 2 = (u : ℂ) * z - 1 := by
    rw [hu]; linear_combination -hzw
  have hz3 : z ^ 3 = ((u : ℂ) ^ 2 - 1) * z - (u : ℂ) := by
    have e : z ^ 3 = z * z ^ 2 := by ring
    rw [e, hz2, show z * ((u : ℂ) * z - 1) = (u : ℂ) * z ^ 2 - z from by ring, hz2]
    ring
  have hz4 : z ^ 4 = ((u : ℂ) ^ 3 - 2 * (u : ℂ)) * z - ((u : ℂ) ^ 2 - 1) := by
    have e : z ^ 4 = z * z ^ 3 := by ring
    rw [e, hz3,
      show z * (((u : ℂ) ^ 2 - 1) * z - (u : ℂ)) = ((u : ℂ) ^ 2 - 1) * z ^ 2 - (u : ℂ) * z
        from by ring, hz2]
    ring
  have hcomb : ((u : ℂ) ^ 3 - 2 * (u : ℂ)) * z - ((u : ℂ) ^ 2 - 1)
      = (φ 0 : ℂ) * (((u : ℂ) ^ 2 - 1) * z - (u : ℂ)) + (φ 1 : ℂ) * ((u : ℂ) * z - 1)
        + (φ 2 : ℂ) * z + (φ 3 : ℂ) := by
    rw [← hz4, ← hz3, ← hz2]; exact hroot
  have hAB : (((u : ℂ) ^ 3 - 2 * (u : ℂ)) - (φ 0 : ℂ) * ((u : ℂ) ^ 2 - 1) - (φ 1 : ℂ) * (u : ℂ)
        - (φ 2 : ℂ)) * z
      = ((u : ℂ) ^ 2 - 1) - (φ 0 : ℂ) * (u : ℂ) - (φ 1 : ℂ) + (φ 3 : ℂ) := by
    linear_combination hcomb
  set A_real : ℝ := u ^ 3 - 2 * u - φ 0 * (u ^ 2 - 1) - φ 1 * u - φ 2 with hA_def
  set B_real : ℝ := u ^ 2 - 1 - φ 0 * u - φ 1 + φ 3 with hB_def
  have hABcast : (A_real : ℂ) * z = (B_real : ℂ) := by
    have hAcc : (A_real : ℂ)
        = ((u : ℂ) ^ 3 - 2 * (u : ℂ)) - (φ 0 : ℂ) * ((u : ℂ) ^ 2 - 1) - (φ 1 : ℂ) * (u : ℂ)
          - (φ 2 : ℂ) := by rw [hA_def]; push_cast; ring
    rw [hAcc]
    have hBcc : (B_real : ℂ)
        = ((u : ℂ) ^ 2 - 1) - (φ 0 : ℂ) * (u : ℂ) - (φ 1 : ℂ) + (φ 3 : ℂ) := by
      rw [hB_def]; push_cast; ring
    rw [hBcc]
    exact hAB
  have him : A_real * z.im = 0 := by
    have hcong := congrArg Complex.im hABcast
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hcong
    simpa using hcong
  have hA0 : A_real = 0 := (mul_eq_zero.mp him).resolve_right hzim
  have hB0 : B_real = 0 := by
    rw [hA0, Complex.ofReal_zero, zero_mul] at hABcast
    exact_mod_cast hABcast.symm
  have hlin : (1 + φ 3) * u = φ 0 - φ 2 := by
    have hidentity : A_real - u * B_real + (1 + φ 3) * u - (φ 0 - φ 2) = 0 := by
      rw [hA_def, hB_def]; ring
    rw [hA0, hB0] at hidentity
    linarith [hidentity]
  have hquad : u ^ 2 - φ 0 * u + (φ 3 - φ 1 - 1) = 0 := by
    rw [hB_def] at hB0; linarith [hB0]
  have hP : (φ 0 - φ 2) ^ 2 - φ 0 * (1 + φ 3) * (φ 0 - φ 2) + (1 + φ 3) ^ 2 * (φ 3 - φ 1 - 1)
      = 0 := by
    linear_combination (1 + φ 3) ^ 2 * hquad + (φ 0 * (1 + φ 3) - (φ 0 - φ 2) - (1 + φ 3) * u)
      * hlin
  unfold cplxCond4
  linear_combination -hP

/-- 単位円上の根を持つ `φ` は `Ω4` に属さない (hypothesis (b) の代数部分)。 -/
theorem not_mem_Ω4_of_unit_root {φ : Fin 4 → ℝ} (z : ℂ)
    (hroot : z ^ 4 = (φ 0 : ℂ) * z ^ 3 + (φ 1 : ℂ) * z ^ 2 + (φ 2 : ℂ) * z + (φ 3 : ℂ))
    (hnorm : ‖z‖ = 1) :
    φ ∉ Ω4 := by
  rintro ⟨h1, hm1, hc⟩
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
      simp only [phiAt1, Fin.sum_univ_four]
      have : (1 : ℂ) = (φ 0 : ℂ) + (φ 1 : ℂ) + (φ 2 : ℂ) + (φ 3 : ℂ) := by
        linear_combination hroot
      have hr : (1 : ℝ) = φ 0 + φ 1 + φ 2 + φ 3 := by exact_mod_cast this
      linarith
    · have hz1 : z = -1 := by apply Complex.ext <;> simp [hn, him]
      rw [hz1] at hroot
      apply hm1
      simp only [phiAtNeg1, Fin.sum_univ_four]
      norm_num
      have : (-1 : ℂ) = (φ 0 : ℂ) - (φ 1 : ℂ) + (φ 2 : ℂ) - (φ 3 : ℂ) := by
        linear_combination -hroot
      have hr : (-1 : ℝ) = φ 0 - φ 1 + φ 2 - φ 3 := by exact_mod_cast this
      linarith
  · exact hc (cplxCond4_eq_zero_of_unit_root_of_ne z hroot hnorm hreal)

/-- `Ω4` は開集合。 -/
theorem isOpen_Ω4 : IsOpen Ω4 := by
  have h1 : Continuous (fun φ : Fin 4 → ℝ => phiAt1 φ) := by unfold phiAt1; fun_prop
  have h2 : Continuous (fun φ : Fin 4 → ℝ => phiAtNeg1 φ) := by unfold phiAtNeg1; fun_prop
  have h3 : Continuous (fun φ : Fin 4 → ℝ => cplxCond4 φ) := by unfold cplxCond4; fun_prop
  exact ((isOpen_ne_fun h1 continuous_const).inter
    ((isOpen_ne_fun h2 continuous_const).inter (isOpen_ne_fun h3 continuous_const)))

/-- hypothesis (b): `L41` は `St(4)` の境界と交わらない。 -/
theorem L41_disjoint_frontier :
    L41 ∩ frontier {φ : Fin 4 → ℝ | IsStationary φ} = ∅ := by
  ext φ
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hφL41, hφfrontier⟩
  obtain ⟨z, hznorm, hzeq⟩ :=
    frontier_isStationary_subset_hasUnitRoot (p := 4) (by norm_num) hφfrontier
  rw [root_four_iff] at hzeq
  exact not_mem_Ω4_of_unit_root z hzeq hznorm (connectedComponentIn_subset Ω4 _ hφL41)

/-- **`L41 = St(4)`**: 最大連結成分の原理を AR(4) に適用した結果。 -/
theorem L41_eq_isStationary : L41 = {φ : Fin 4 → ℝ | IsStationary φ} :=
  maximal_component_principle Ω4 {φ : Fin 4 → ℝ | IsStationary φ}
    (fun _ : Fin 4 => (0 : ℝ))
    zero_mem_Ω4
    (isOpen_isStationary (by norm_num))
    (isPreconnected_isStationary (by norm_num))
    (isStationary_zero (p := 4))
    (fun _ hφ => isStationary_mem_Ω4 hφ)
    L41_disjoint_frontier

/-! ### 符号の復元 -/

theorem phiAt1_pos_on_L41 : ∀ φ ∈ L41, 0 < phiAt1 φ := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold phiAt1; fun_prop)
    (fun φ hφ => (connectedComponentIn_subset Ω4 _ hφ).1)
    (mem_connectedComponentIn zero_mem_Ω4)
  simp [phiAt1]

theorem phiAtNeg1_pos_on_L41 : ∀ φ ∈ L41, 0 < phiAtNeg1 φ := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold phiAtNeg1; fun_prop)
    (fun φ hφ => (connectedComponentIn_subset Ω4 _ hφ).2.1)
    (mem_connectedComponentIn zero_mem_Ω4)
  simp [phiAtNeg1]

theorem cplxCond4_pos_on_L41 : ∀ φ ∈ L41, 0 < cplxCond4 φ := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold cplxCond4; fun_prop)
    (fun φ hφ => (connectedComponentIn_subset Ω4 _ hφ).2.2)
    (mem_connectedComponentIn zero_mem_Ω4)
  simp [cplxCond4]

/-! ### `1+φ_4 ≠ 0` の復元と符号

`cplxCond4 φ = -(φ_1-φ_3)²` となるのは `1+φ_4=0` のとき (`Q=-P`, `1+φ_4=0` で `P=(φ_1-φ_3)²`)。
`L41` 上では既に `cplxCond4>0` なので、これは `L41` 上で `1+φ_4≠0` を強制する。
`O_4` での値 `1+φ_4=1>0` から、connectedness で `L41` 全体での符号が決まる。 -/

theorem onePlusPhi3_ne_zero_on_L41 : ∀ φ ∈ L41, (1 : ℝ) + φ 3 ≠ 0 := by
  intro φ hφ heq
  have hident : cplxCond4 φ = -(φ 0 - φ 2) ^ 2 := by
    have h3 : φ 3 = -1 := by linarith
    unfold cplxCond4; rw [h3]; ring
  have hpos := cplxCond4_pos_on_L41 φ hφ
  nlinarith [hident, sq_nonneg (φ 0 - φ 2)]

theorem onePlusPhi3_pos_on_L41 : ∀ φ ∈ L41, (0 : ℝ) < 1 + φ 3 := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by fun_prop) onePlusPhi3_ne_zero_on_L41
    (mem_connectedComponentIn zero_mem_Ω4)
  simp

/-! ### 4番目の条件 `2(1+φ_4)>|φ_1-φ_3|` の復元

`2(1+φ_4)=φ_1-φ_3` なら `cplxCond4 φ = -(1+φ_4)²・φ(1)`。`L41` 上では既に
`cplxCond4>0` と `φ(1)>0` と `1+φ_4>0` が確立しているので、これは
`-(1+φ_4)²・φ(1) > 0` かつ `φ(1)>0` かつ `(1+φ_4)^2>0` を意味し矛盾する。
`-2(1+φ_4)=φ_1-φ_3` の場合は `φ(-1)` 版で同様。 -/

theorem s_ne_twoOnePlusPhi3_on_L41 : ∀ φ ∈ L41, 2 * (1 + φ 3) ≠ φ 0 - φ 2 := by
  intro φ hφ heq
  have hident : cplxCond4 φ = -(1 + φ 3) ^ 2 * phiAt1 φ := by
    have h2 : φ 2 = φ 0 - 2 * (1 + φ 3) := by linarith
    simp only [cplxCond4, phiAt1, Fin.sum_univ_four]
    rw [h2]; ring
  have hQpos := cplxCond4_pos_on_L41 φ hφ
  have h1pos := phiAt1_pos_on_L41 φ hφ
  have h4pos := onePlusPhi3_pos_on_L41 φ hφ
  nlinarith [hident, sq_nonneg (1 + φ 3), mul_pos (mul_pos h4pos h4pos) h1pos]

theorem s_ne_negTwoOnePlusPhi3_on_L41 : ∀ φ ∈ L41, -(2 * (1 + φ 3)) ≠ φ 0 - φ 2 := by
  intro φ hφ heq
  have hident : cplxCond4 φ = -(1 + φ 3) ^ 2 * phiAtNeg1 φ := by
    have h2 : φ 2 = φ 0 + 2 * (1 + φ 3) := by linarith
    simp only [cplxCond4, phiAtNeg1, Fin.sum_univ_four]
    norm_num
    rw [h2]; ring
  have hQpos := cplxCond4_pos_on_L41 φ hφ
  have h1pos := phiAtNeg1_pos_on_L41 φ hφ
  have h4pos := onePlusPhi3_pos_on_L41 φ hφ
  nlinarith [hident, sq_nonneg (1 + φ 3), mul_pos (mul_pos h4pos h4pos) h1pos]

theorem sSq_ne_zero_on_L41 :
    ∀ φ ∈ L41, 4 * (1 + φ 3) ^ 2 - (φ 0 - φ 2) ^ 2 ≠ 0 := by
  intro φ hφ heq
  have hfact : (2 * (1 + φ 3) - (φ 0 - φ 2)) * (2 * (1 + φ 3) + (φ 0 - φ 2)) = 0 := by
    linear_combination heq
  rcases mul_eq_zero.mp hfact with h | h
  · exact s_ne_twoOnePlusPhi3_on_L41 φ hφ (by linarith)
  · exact s_ne_negTwoOnePlusPhi3_on_L41 φ hφ (by linarith)

theorem sSq_pos_on_L41 : ∀ φ ∈ L41, 0 < 4 * (1 + φ 3) ^ 2 - (φ 0 - φ 2) ^ 2 := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by fun_prop) sSq_ne_zero_on_L41
    (mem_connectedComponentIn zero_mem_Ω4)
  simp

theorem abs_diff_lt_two_onePlusPhi3_on_L41 :
    ∀ φ ∈ L41, |φ 0 - φ 2| < 2 * (1 + φ 3) := by
  intro φ hφ
  have h := sSq_pos_on_L41 φ hφ
  have h4pos := onePlusPhi3_pos_on_L41 φ hφ
  rw [abs_lt]
  constructor <;>
    nlinarith [sq_nonneg (φ 0 - φ 2 - 2 * (1 + φ 3)), sq_nonneg (φ 0 - φ 2 + 2 * (1 + φ 3))]

/-- **AR(4) の定常性の必要性**: `IsStationary φ` ならば `St4 φ`。 -/
theorem isStationary_imp_St4 {φ : Fin 4 → ℝ} (hφ : IsStationary φ) : St4 φ := by
  have hφ' : φ ∈ {φ : Fin 4 → ℝ | IsStationary φ} := hφ
  rw [← L41_eq_isStationary] at hφ'
  refine ⟨phiAt1_pos_on_L41 φ hφ', phiAtNeg1_pos_on_L41 φ hφ', cplxCond4_pos_on_L41 φ hφ', ?_⟩
  have := abs_diff_lt_two_onePlusPhi3_on_L41 φ hφ'
  linarith

end StTopology
