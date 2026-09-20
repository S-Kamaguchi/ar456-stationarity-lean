import Mathlib
import StTopology.StationarityRegions
import StTopology.MaximalComponentPrinciple
import StTopology.StOpen
import StTopology.StConnected
import StTopology.RootPerturbation

set_option linter.style.header false

/-!
# AR(3) の定常性: 古典的な閉形式条件

`6_kanren.tex` (Section 4.4 内, St(3) の記述) より:
`St(3) = {φ(1)>0, φ(-1)>0, φ_3^2-φ_1φ_3-φ_2-1<0, 2>|φ_1-φ_3|}`
-/

open Finset StTopology

namespace StTopology

/-- St(3) の明示的閉形式。`φ 0 = φ_1, φ 1 = φ_2, φ 2 = φ_3` の対応。 -/
def St3 (φ : Fin 3 → ℝ) : Prop :=
  phiAt1 φ > 0 ∧ phiAtNeg1 φ > 0 ∧
  φ 2 ^ 2 - φ 0 * φ 2 - φ 1 - 1 < 0 ∧
  2 > |φ 0 - φ 2|

/-
十分性の実根ケースを nlinarith への当てずっぽうな丸投げ (`q_one_pos`, 判別式によらない
根の直接構成) で通す試みは、ヒント項を増減させても heartbeat タイムアウトに阻まれ続けた
ため、この方針は放棄した。今後は `MaximalComponentPrinciple.lean` で形式化した
「最大連結成分の原理」(論文 Section 3.8) を使い、判別式による場合分けなしに
`St3 = IsStationary` を示す方針に切り替える。
-/

/-! ## 最大連結成分の原理を適用するための準備

論文 Section 4.4 の AR(4) の議論を AR(3) に対して行う。AR(3) では、Chebyshev 置換
`x = cos θ` のもとで単位円上の複素根の存在条件が

* `4x² - 1 - 2φ_1 x - φ_2 = 0`   …(II)
* `4x³ - 3x - φ_1(2x² - 1) - φ_2 x - φ_3 = 0`   …(I)

と書ける。(II) の `4x²` を (I) に代入すると `x²` の項が完全に消えて、`2x = φ_1 - φ_3`
という一次関係だけが残る。AR(4) の `(1+φ_4)` のような符号不明の係数が AR(3) には
現れないため、`-1 < x < 1` から直ちに `|φ_1 - φ_3| < 2` が従う (符号確定の補題すら不要)。
これを (II) に戻すと `φ_3² - φ_1φ_3 - φ_2 - 1 = 0` になり、`St3` の定義の4条件と
ちょうど一致する。
-/

/-- `q(φ) = φ_3² - φ_1φ_3 - φ_2 - 1`。`St3` の第3条件の左辺であり、
単位円上に複素根が存在するための (Chebyshev 置換後の) 条件そのもの。 -/
def cplxCond (φ : Fin 3 → ℝ) : ℝ := φ 2 ^ 2 - φ 0 * φ 2 - φ 1 - 1

/-- Ω_3: 論文の `Ω = {φ(1)≠0, φ(-1)≠0, (複素根条件)≠0}` にあたる開集合。
`L_{3,1} := connectedComponentIn Ω3 O_3` が、最大連結成分の原理を適用する対象。

3つの条件はいずれも「単位円上に根が存在する」ことと同値な等式の否定であり、
それぞれ `φ(1)=0` (根 `z=1`)、`φ(-1)=0` (根 `z=-1`)、`cplxCond=0` (非実の
単位円上の根) に対応する。 -/
def Ω3 : Set (Fin 3 → ℝ) :=
  {φ : Fin 3 → ℝ | phiAt1 φ ≠ 0 ∧ phiAtNeg1 φ ≠ 0 ∧ cplxCond φ ≠ 0}

/-- 原点 `O_3` (すべての係数が 0) は `Ω3` に属する。
実際、`φ(1)=1≠0`, `φ(-1)=1≠0`, `cplxCond=-1≠0`。 -/
theorem zero_mem_Ω3 : (fun _ : Fin 3 => (0 : ℝ)) ∈ Ω3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [phiAt1, phiAtNeg1, cplxCond]

/-- `L_{3,1}`: `Ω3` 内で原点 `O_3` を含む最大の連結成分。
論文の「上記の条件を満たす `O_3` を含む最大の path-connected 集合」に対応する。 -/
def L31 : Set (Fin 3 → ℝ) :=
  connectedComponentIn Ω3 (fun _ : Fin 3 => (0 : ℝ))

/-- AR(3) の逆特性方程式を、`Fin 3` の総和を展開した具体形に書き換える。 -/
theorem root_three_iff {φ : Fin 3 → ℝ} (α : ℂ) :
    (α ^ 3 = ∑ i : Fin 3, (φ i : ℂ) * α ^ (3 - 1 - (i : ℕ)))
      ↔ α ^ 3 = (φ 0 : ℂ) * α ^ 2 + (φ 1 : ℂ) * α + (φ 2 : ℂ) := by
  simp only [Fin.sum_univ_three]
  norm_num

/-! ### hypothesis (a): `St(3) ⊆ Ω3`

`φ` が定常なら単位円上に根は存在しない。`Ω3` の3条件はいずれも
「単位円上に根が存在する」ことと同値な等式なので、どれも成り立ちえない。

3つ目 (`cplxCond φ ≠ 0`) が要点であり、鍵になるのは次の因数分解である:
`cplxCond φ = 0` のとき、`s := φ_1 - φ_3` とおくと逆特性多項式が

  `z³ - φ_1z² - φ_2z - φ_3 = (z - φ_3)(z² - sz + 1)`

と分解する (係数比較で `s + φ_3 = φ_1` と `cplxCond φ = 0` がちょうど対応する)。
`z² - sz + 1` の2根は積が 1 なので、両方のノルムが 1 未満ということはありえない。
判別式の符号で場合分けする必要はまったくない。 -/

theorem phiAt1_ne_zero_of_isStationary {φ : Fin 3 → ℝ} (hφ : IsStationary φ) :
    phiAt1 φ ≠ 0 := by
  intro h
  simp only [phiAt1, Fin.sum_univ_three] at h
  have hsum : φ 0 + φ 1 + φ 2 = 1 := by linarith
  have hsumC : (φ 0 : ℂ) + (φ 1 : ℂ) + (φ 2 : ℂ) = 1 := by exact_mod_cast hsum
  have hroot : (1 : ℂ) ^ 3 = ∑ i : Fin 3, (φ i : ℂ) * (1 : ℂ) ^ (3 - 1 - (i : ℕ)) := by
    rw [root_three_iff]
    linear_combination -hsumC
  have hlt := hφ 1 hroot
  simp at hlt

theorem phiAtNeg1_ne_zero_of_isStationary {φ : Fin 3 → ℝ} (hφ : IsStationary φ) :
    phiAtNeg1 φ ≠ 0 := by
  intro h
  simp only [phiAtNeg1, Fin.sum_univ_three] at h
  norm_num at h
  have hsum : φ 0 - φ 1 + φ 2 = -1 := by linarith
  have hsumC : (φ 0 : ℂ) - (φ 1 : ℂ) + (φ 2 : ℂ) = -1 := by exact_mod_cast hsum
  have hroot : (-1 : ℂ) ^ 3 = ∑ i : Fin 3, (φ i : ℂ) * (-1 : ℂ) ^ (3 - 1 - (i : ℕ)) := by
    rw [root_three_iff]
    norm_num
    linear_combination -hsumC
  have hlt := hφ (-1) hroot
  simp at hlt

theorem cplxCond_ne_zero_of_isStationary {φ : Fin 3 → ℝ} (hφ : IsStationary φ) :
    cplxCond φ ≠ 0 := by
  intro h
  simp only [cplxCond] at h
  have hcC : (φ 2 : ℂ) ^ 2 - (φ 0 : ℂ) * (φ 2 : ℂ) - (φ 1 : ℂ) - 1 = 0 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  set s : ℂ := (φ 0 : ℂ) - (φ 2 : ℂ) with hs
  -- z² - sz + 1 の2根 α, β を作る (積は 1)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (s ^ 2 - 4) (by norm_num : 0 < 2)
  set α : ℂ := (s + d) / 2 with hαdef
  set β : ℂ := s - α with hβdef
  have hα2 : α ^ 2 - s * α + 1 = 0 := by
    rw [hαdef]
    field_simp
    linear_combination hd
  have hβ2 : β ^ 2 - s * β + 1 = 0 := by
    rw [hβdef]
    linear_combination hα2
  have hαβ : α * β = 1 := by
    rw [hβdef]
    linear_combination -hα2
  -- 因数分解 `z³-φ₁z²-φ₂z-φ₃ = (z-φ₃)(z²-sz+1) + z·cplxCond` により α, β は逆特性方程式の根
  have hrootα : α ^ 3 = ∑ i : Fin 3, (φ i : ℂ) * α ^ (3 - 1 - (i : ℕ)) := by
    rw [root_three_iff]
    linear_combination (α - (φ 2 : ℂ)) * hα2 + α * hcC
  have hrootβ : β ^ 3 = ∑ i : Fin 3, (φ i : ℂ) * β ^ (3 - 1 - (i : ℕ)) := by
    rw [root_three_iff]
    linear_combination (β - (φ 2 : ℂ)) * hβ2 + β * hcC
  have hαlt := hφ α hrootα
  have hβlt := hφ β hrootβ
  -- しかし ‖α‖·‖β‖ = ‖αβ‖ = 1 なので矛盾
  have hprod : ‖α‖ * ‖β‖ = 1 := by
    rw [← norm_mul, hαβ, norm_one]
  nlinarith [norm_nonneg α, norm_nonneg β, hαlt, hβlt, hprod]

/-! ### hypothesis (b) の代数的核: 単位円上に根があれば `Ω3` から外れる

`(a)` の逆向き。`‖z‖ = 1` なる根 `z` が存在すれば、`Ω3` の3条件のいずれかが
破れる (等号が成立する) ことを示す。

* `z = 1` なら `φ(1) = 0`、`z = -1` なら `φ(-1) = 0` (代入するだけ)。
* それ以外なら `z` は非実で、共役 `z̄` も根であり `z·z̄ = ‖z‖² = 1`。
  2式の差を `z - z̄ (≠0)` で割って `u := z + z̄` の関係式を作り、
  2式の和と組み合わせると `u = φ_1 - φ_3` が出る。これを戻すと
  `cplxCond φ = 0` がちょうど得られる。

この向きも判別式は一切使わない。 -/
theorem cplxCond_eq_zero_of_unit_root_of_ne {φ : Fin 3 → ℝ} (z : ℂ)
    (hroot : z ^ 3 = (φ 0 : ℂ) * z ^ 2 + (φ 1 : ℂ) * z + (φ 2 : ℂ))
    (hnorm : ‖z‖ = 1) (hne : z ≠ (starRingEnd ℂ) z) :
    cplxCond φ = 0 := by
  set w : ℂ := (starRingEnd ℂ) z with hw
  -- 共役も根
  have hrootw : w ^ 3 = (φ 0 : ℂ) * w ^ 2 + (φ 1 : ℂ) * w + (φ 2 : ℂ) := by
    have := congrArg (starRingEnd ℂ) hroot
    simpa [hw, map_add, map_mul, map_pow, Complex.conj_ofReal] using this
  -- z·w = ‖z‖² = 1
  have hzw : z * w = 1 := by
    rw [hw, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hsub : z - w ≠ 0 := sub_ne_zero.mpr hne
  -- 差を z-w で割った式
  have hA : z ^ 2 + z * w + w ^ 2 - (φ 0 : ℂ) * (z + w) - (φ 1 : ℂ) = 0 := by
    have hdiff : (z - w) * (z ^ 2 + z * w + w ^ 2 - (φ 0 : ℂ) * (z + w) - (φ 1 : ℂ)) = 0 := by
      linear_combination hroot - hrootw
    rcases mul_eq_zero.mp hdiff with hc | hc
    · exact absurd hc hsub
    · exact hc
  -- 和と組み合わせて u = φ_1 - φ_3
  have hu : z + w = (φ 0 : ℂ) - (φ 2 : ℂ) := by
    linear_combination (-1 / 2 : ℂ) * hroot + (-1 / 2 : ℂ) * hrootw
      + ((z + w) / 2) * hA + ((φ 0 : ℂ) - (z + w)) * hzw
  -- 戻すと cplxCond = 0
  have hgoal : (φ 2 : ℂ) ^ 2 - (φ 0 : ℂ) * (φ 2 : ℂ) - (φ 1 : ℂ) - 1 = 0 := by
    linear_combination hA + ((φ 2 : ℂ) - (z + w)) * hu + hzw
  have : ((φ 2 ^ 2 - φ 0 * φ 2 - φ 1 - 1 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
    push_cast
    linear_combination hgoal
  simp only [cplxCond]
  exact_mod_cast this

/-- 単位円上の根を持つ `φ` は `Ω3` に属さない (hypothesis (b) の代数部分)。 -/
theorem not_mem_Ω3_of_unit_root {φ : Fin 3 → ℝ} (z : ℂ)
    (hroot : z ^ 3 = (φ 0 : ℂ) * z ^ 2 + (φ 1 : ℂ) * z + (φ 2 : ℂ))
    (hnorm : ‖z‖ = 1) :
    φ ∉ Ω3 := by
  rintro ⟨h1, hm1, hc⟩
  by_cases hreal : z = (starRingEnd ℂ) z
  · -- z が実数なら ‖z‖=1 より z = ±1
    have him : z.im = 0 := Complex.conj_eq_iff_im.mp hreal.symm
    have hre : |z.re| = 1 := by
      have : ‖z‖ = |z.re| := by
        rw [Complex.norm_def, Complex.normSq_apply, him]
        simp [Real.sqrt_mul_self_eq_abs]
      rwa [this] at hnorm
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hre with hp | hn
    · -- z = 1 なら φ(1) = 0
      have hz1 : z = 1 := by
        apply Complex.ext <;> simp [hp, him]
      rw [hz1] at hroot
      apply h1
      simp only [phiAt1, Fin.sum_univ_three]
      have : (1 : ℂ) = (φ 0 : ℂ) + (φ 1 : ℂ) + (φ 2 : ℂ) := by linear_combination hroot
      have hr : (1 : ℝ) = φ 0 + φ 1 + φ 2 := by exact_mod_cast this
      linarith
    · -- z = -1 なら φ(-1) = 0
      have hz1 : z = -1 := by
        apply Complex.ext <;> simp [hn, him]
      rw [hz1] at hroot
      apply hm1
      simp only [phiAtNeg1, Fin.sum_univ_three]
      norm_num
      have : (-1 : ℂ) = (φ 0 : ℂ) - (φ 1 : ℂ) + (φ 2 : ℂ) := by linear_combination hroot
      have hr : (-1 : ℝ) = φ 0 - φ 1 + φ 2 := by exact_mod_cast this
      linarith
  · exact hc (cplxCond_eq_zero_of_unit_root_of_ne z hroot hnorm hreal)

/-- **hypothesis (a)**: 定常な `φ` は `Ω3` に属する。 -/
theorem isStationary_mem_Ω3 {φ : Fin 3 → ℝ} (hφ : IsStationary φ) : φ ∈ Ω3 :=
  ⟨phiAt1_ne_zero_of_isStationary hφ,
    phiAtNeg1_ne_zero_of_isStationary hφ,
    cplxCond_ne_zero_of_isStationary hφ⟩

/-- `Ω3` は開集合 (3つの連続関数の零点集合の補集合の共通部分)。 -/
theorem isOpen_Ω3 : IsOpen Ω3 := by
  have h1 : Continuous (fun φ : Fin 3 → ℝ => phiAt1 φ) := by
    unfold phiAt1
    fun_prop
  have h2 : Continuous (fun φ : Fin 3 → ℝ => phiAtNeg1 φ) := by
    unfold phiAtNeg1
    fun_prop
  have h3 : Continuous (fun φ : Fin 3 → ℝ => cplxCond φ) := by
    unfold cplxCond
    fun_prop
  exact ((isOpen_ne_fun h1 continuous_const).inter
    ((isOpen_ne_fun h2 continuous_const).inter (isOpen_ne_fun h3 continuous_const)))

/-! ### hypothesis (b) の仕上げと最大連結成分の原理の適用 -/

/-- hypothesis (b): `L31` は `St(3)` の境界と交わらない。
`frontier_isStationary_subset_hasUnitRoot` (一般の p) と `not_mem_Ω3_of_unit_root`
(AR(3) 固有) を合わせるだけで従う。 -/
theorem L31_disjoint_frontier :
    L31 ∩ frontier {φ : Fin 3 → ℝ | IsStationary φ} = ∅ := by
  ext φ
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hφL31, hφfrontier⟩
  obtain ⟨z, hznorm, hzeq⟩ :=
    frontier_isStationary_subset_hasUnitRoot (p := 3) (by norm_num) hφfrontier
  rw [root_three_iff] at hzeq
  exact not_mem_Ω3_of_unit_root z hzeq hznorm (connectedComponentIn_subset Ω3 _ hφL31)

/-- **`L31 = St(3)`**: 最大連結成分の原理 (`MaximalComponentPrinciple.lean`) を
AR(3) に適用した結果。 -/
theorem L31_eq_isStationary : L31 = {φ : Fin 3 → ℝ | IsStationary φ} :=
  maximal_component_principle Ω3 {φ : Fin 3 → ℝ | IsStationary φ}
    (fun _ : Fin 3 => (0 : ℝ))
    zero_mem_Ω3
    (isOpen_isStationary (by norm_num))
    (isPreconnected_isStationary (by norm_num))
    (isStationary_zero (p := 3))
    (fun _ hφ => isStationary_mem_Ω3 hφ)
    L31_disjoint_frontier

/-! ### 符号の復元 (Lemma sign)

`L31` は `Ω3` (等号を除いた条件) の連結成分として定義されているので、そのままでは
`phiAt1 ≠ 0` などの「≠0」の情報しか持たない。`L31` が連結で、原点でこれらの符号が
確定していることから、連結性だけで `L31` 全体での符号が決まる
(論文の Lemma sign, IVT の唯一の使用箇所)。 -/

/-- 連結集合上で連続かつ非零な関数は、1点での符号がそのまま全体に伝播する。 -/
theorem sign_fixed_pos_on_preconnected {X : Type*} [TopologicalSpace X] {C : Set X}
    (hC : IsPreconnected C) {f : X → ℝ} (hf : Continuous f) (hne : ∀ φ ∈ C, f φ ≠ 0)
    {φ0 : X} (hφ0 : φ0 ∈ C) (hpos : 0 < f φ0) :
    ∀ φ ∈ C, 0 < f φ := by
  have hu : IsOpen {φ : X | 0 < f φ} := isOpen_lt continuous_const hf
  have hv : IsOpen {φ : X | f φ < 0} := isOpen_lt hf continuous_const
  have hdisj : Disjoint {φ : X | 0 < f φ} {φ : X | f φ < 0} := by
    rw [Set.disjoint_left]
    intro φ h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    linarith
  have hsub : C ⊆ {φ : X | 0 < f φ} ∪ {φ : X | f φ < 0} := by
    intro φ hφ
    rcases lt_or_gt_of_ne (hne φ hφ) with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases hC.subset_or_subset hu hv hdisj hsub with h | h
  · exact h
  · exact absurd hpos (not_lt.mpr (h hφ0).le)

theorem phiAt1_pos_on_L31 : ∀ φ ∈ L31, 0 < phiAt1 φ := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold phiAt1; fun_prop)
    (fun φ hφ => (connectedComponentIn_subset Ω3 _ hφ).1)
    (mem_connectedComponentIn zero_mem_Ω3)
  simp [phiAt1]

theorem phiAtNeg1_pos_on_L31 : ∀ φ ∈ L31, 0 < phiAtNeg1 φ := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by unfold phiAtNeg1; fun_prop)
    (fun φ hφ => (connectedComponentIn_subset Ω3 _ hφ).2.1)
    (mem_connectedComponentIn zero_mem_Ω3)
  simp [phiAtNeg1]

theorem cplxCond_neg_on_L31 : ∀ φ ∈ L31, cplxCond φ < 0 := by
  have := sign_fixed_pos_on_preconnected (f := fun φ => -cplxCond φ)
    isPreconnected_connectedComponentIn
    (by unfold cplxCond; fun_prop)
    (fun φ hφ => neg_ne_zero.mpr (connectedComponentIn_subset Ω3 _ hφ).2.2)
    (mem_connectedComponentIn zero_mem_Ω3)
    (by simp [cplxCond])
  intro φ hφ
  have := this φ hφ
  linarith

/-- **AR(3) の定常性からの3条件の導出 (必要性)**: `IsStationary φ` ならば、
古典的 Schur–Cohn の4条件のうち `2>|φ_1-φ_3|` を除いた3条件が成り立つ。

逆向き (3条件から `IsStationary` を導く、すなわちこの3条件だけで十分であること) は、
`{phiAt1>0 ∧ phiAtNeg1>0 ∧ cplxCond<0}` という領域自体が (`Ω3` の中で) 連結で
あることを別途示す必要があり、現時点では証明できていない。それが言えれば
AR(4) の Remark 1 と同種の「3条件で十分」という簡約になるが、今のところ
確立できているのは必要性のみである。 -/
theorem isStationary_imp_three_conditions {φ : Fin 3 → ℝ} (hφ : IsStationary φ) :
    phiAt1 φ > 0 ∧ phiAtNeg1 φ > 0 ∧ cplxCond φ < 0 := by
  have hφ' : φ ∈ {φ : Fin 3 → ℝ | IsStationary φ} := hφ
  rw [← L31_eq_isStationary] at hφ'
  exact ⟨phiAt1_pos_on_L31 φ hφ', phiAtNeg1_pos_on_L31 φ hφ', cplxCond_neg_on_L31 φ hφ'⟩

/-! ### 4つ目の条件 `2>|φ_1-φ_3|` の復元

`3条件だけでは St(3) にならない` ことが数値実験で確認された
(範囲を広げると3条件を満たすが非定常な点が大量に存在する)。したがって
`2>|φ_1-φ_3|` は本質的な条件であり、これも `L31` 上で成り立つことを示す必要がある。

鍵になるのは次の2つの恒等式 (`s := φ_1-φ_3` とおく):

* `cplxCond φ - phiAt1 φ = (1-φ_3)(s-2)`
* `cplxCond φ - phiAtNeg1 φ = -(φ_3+1)(s+2)`

もし `L31` 上のある点で `s=2` になったとすると、1つ目の恒等式から
`cplxCond φ = phiAt1 φ` になるが、`L31` 上では既に `phiAt1>0` かつ `cplxCond<0`
なので矛盾する。`s=-2` も同様に2つ目の恒等式と矛盾する。したがって `L31` 上では
常に `s≠±2`。原点で `s=0` (`|s|<2`) なので、連結性による符号の復元 (`Lemma sign`)
から `L31` 全体で `|s|<2` が従う。 -/

theorem s_ne_two_on_L31 : ∀ φ ∈ L31, φ 0 - φ 2 ≠ 2 := by
  intro φ hφ heq
  have hident : cplxCond φ - phiAt1 φ = (1 - φ 2) * (φ 0 - φ 2 - 2) := by
    simp only [cplxCond, phiAt1, Fin.sum_univ_three]
    ring
  rw [heq] at hident
  simp only [sub_self, mul_zero] at hident
  have h1 := phiAt1_pos_on_L31 φ hφ
  have h2 := cplxCond_neg_on_L31 φ hφ
  linarith

theorem s_ne_neg_two_on_L31 : ∀ φ ∈ L31, φ 0 - φ 2 ≠ -2 := by
  intro φ hφ heq
  have hident : cplxCond φ - phiAtNeg1 φ = -(φ 2 + 1) * (φ 0 - φ 2 + 2) := by
    simp only [cplxCond, phiAtNeg1, Fin.sum_univ_three]
    norm_num
    ring
  rw [heq] at hident
  simp only [neg_add_cancel, mul_zero] at hident
  have h1 := phiAtNeg1_pos_on_L31 φ hφ
  have h2 := cplxCond_neg_on_L31 φ hφ
  linarith

theorem sSq_ne_four_on_L31 : ∀ φ ∈ L31, (4 : ℝ) - (φ 0 - φ 2) ^ 2 ≠ 0 := by
  intro φ hφ heq
  have h2 : (φ 0 - φ 2) ^ 2 = 4 := by linarith
  have hfact : (φ 0 - φ 2 - 2) * (φ 0 - φ 2 + 2) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp hfact with h | h
  · exact s_ne_two_on_L31 φ hφ (by linarith)
  · exact s_ne_neg_two_on_L31 φ hφ (by linarith)

theorem sSq_lt_four_on_L31 : ∀ φ ∈ L31, (4 : ℝ) - (φ 0 - φ 2) ^ 2 > 0 := by
  apply sign_fixed_pos_on_preconnected isPreconnected_connectedComponentIn
    (by fun_prop)
    sSq_ne_four_on_L31
    (mem_connectedComponentIn zero_mem_Ω3)
  simp

theorem abs_diff_lt_two_on_L31 : ∀ φ ∈ L31, |φ 0 - φ 2| < 2 := by
  intro φ hφ
  have h := sSq_lt_four_on_L31 φ hφ
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (φ 0 - φ 2 - 2), sq_nonneg (φ 0 - φ 2 + 2)]

/-- **AR(3) の定常性の必要性**: `IsStationary φ` ならば `St3 φ` (論文の4条件すべて)。
数値実験で確認した通り3条件では不十分だったため、4つ目の条件もここで復元している。 -/
theorem isStationary_imp_St3 {φ : Fin 3 → ℝ} (hφ : IsStationary φ) : St3 φ := by
  have hφ' : φ ∈ {φ : Fin 3 → ℝ | IsStationary φ} := hφ
  rw [← L31_eq_isStationary] at hφ'
  refine ⟨phiAt1_pos_on_L31 φ hφ', phiAtNeg1_pos_on_L31 φ hφ', cplxCond_neg_on_L31 φ hφ', ?_⟩
  have := abs_diff_lt_two_on_L31 φ hφ'
  linarith

/-! ### 十分性への挑戦: 重み付き星型性

数値実験で「一様スケーリング `t·φ` は境界近くで失敗するが、根の縮小に対応する
重み付きスケーリング `(tφ_1,t²φ_2,t³φ_3)` は St(3) の4条件を保つ」ことを確認した。
まず `phiAt1` (最も単純な条件) について、この事実の証明を試みる。

鍵になるのは次の恒等式:
`1-tφ_1-t²φ_2-t³φ_3 = (1-t) + t·phiAt1(φ) + t(1-t)(φ_2+φ_3+tφ_3)`
(`t=0,1` でそれぞれ自明に一致することを利用して導出できる)。
最初の2項は非負だが、最後の項の符号は自明ではなく、`phiAtNeg1>0` と
`cplxCond<0` による `φ_2` の上下からの評価が必要になる。 -/

theorem phiAt1_scale_pos {φ : Fin 3 → ℝ} (hSt3 : St3 φ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < 1 - t * φ 0 - t ^ 2 * φ 1 - t ^ 3 * φ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hSt3
  have h4' : |φ 0 - φ 2| < 2 := h4
  rw [abs_lt] at h4'
  have ha : 0 < 1 - φ 0 - φ 1 - φ 2 := by
    have h1' := h1; simp only [phiAt1, Fin.sum_univ_three] at h1'; linarith
  have hR : 0 < φ 1 - φ 2 ^ 2 + φ 0 * φ 2 + 1 := by linarith
  have hS : 0 < 2 - (φ 0 - φ 2) := by linarith [h4'.2]
  -- from `ha + hR = (1 - φ 2) * hS` (a ring identity), together with `hS > 0`, we get `φ 2 < 1`.
  have hphi2lt1 : φ 2 < 1 := by nlinarith [ha, hR, hS]
  -- `φ 0 - φ 2 < 2` and `φ 2 < 1` give `φ 0 < 3`.
  have hphi0lt3 : φ 0 < 3 := by linarith [h4'.2]
  -- Bernstein coefficients (on `[0,1]`) of the cubic `1 - tφ0 - t²φ1 - t³φ2` in `t`.
  have hp1 : 0 ≤ 1 - φ 0 / 3 := by linarith
  have hp2 : 0 ≤ 1 - (2 * φ 0 + φ 1) / 3 := by linarith [ha, h4'.2]
  have hbernstein : 1 - t * φ 0 - t ^ 2 * φ 1 - t ^ 3 * φ 2
      = 1 * (1 - t) ^ 3 + 3 * (1 - φ 0 / 3) * (t * (1 - t) ^ 2)
        + 3 * (1 - (2 * φ 0 + φ 1) / 3) * (t ^ 2 * (1 - t)) + (1 - φ 0 - φ 1 - φ 2) * t ^ 3 := by
    ring
  rcases eq_or_ne t 0 with ht0eq | ht0ne
  · subst ht0eq; norm_num
  · have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0ne)
    have h1t : 0 ≤ 1 - t := by linarith
    rw [hbernstein]
    have e1 : 0 ≤ (1 - t) ^ 3 := pow_nonneg h1t 3
    have e2 : 0 ≤ t * (1 - t) ^ 2 := mul_nonneg ht0 (pow_nonneg h1t 2)
    have e3 : 0 ≤ t ^ 2 * (1 - t) := mul_nonneg (pow_nonneg ht0 2) h1t
    have e4 : 0 < t ^ 3 := pow_pos ht0' 3
    nlinarith [mul_nonneg hp1 e2, mul_nonneg hp2 e3, mul_pos ha e4, e1]

/-- `phiAtNeg1` 版。`phiAt1_scale_pos` と対称な議論(`Q+R=(1+φ_3)T` という
恒等式を使って `φ_3>-1` を出し、そこから Bernstein 係数の非負性を示す)。 -/
theorem phiAtNeg1_scale_pos {φ : Fin 3 → ℝ} (hSt3 : St3 φ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < 1 + t * φ 0 - t ^ 2 * φ 1 + t ^ 3 * φ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hSt3
  have h4' : |φ 0 - φ 2| < 2 := h4
  rw [abs_lt] at h4'
  have hQ : 0 < 1 + φ 0 + φ 2 - φ 1 := by
    have h2' := h2
    simp only [phiAtNeg1, Fin.sum_univ_three] at h2'
    norm_num at h2'
    linarith
  have hR : 0 < φ 1 - φ 2 ^ 2 + φ 0 * φ 2 + 1 := by linarith
  have hT : 0 < 2 + (φ 0 - φ 2) := by linarith [h4'.1]
  -- from `hQ + hR = (1 + φ 2) * hT` (a ring identity), together with `hT > 0`, we get `φ 2 > -1`.
  have hphi2gtm1 : -1 < φ 2 := by nlinarith [hQ, hR, hT]
  -- `φ 0 - φ 2 > -2` and `φ 2 > -1` give `φ 0 > -3`.
  have hphi0gtm3 : -3 < φ 0 := by linarith [h4'.1]
  -- Bernstein coefficients (on `[0,1]`) of the cubic `1 + tφ0 - t²φ1 + t³φ2` in `t`.
  have hp1 : 0 ≤ 1 + φ 0 / 3 := by linarith
  have hp2 : 0 ≤ 1 + 2 * φ 0 / 3 - φ 1 / 3 := by linarith [hQ, h4'.1]
  have hbernstein : 1 + t * φ 0 - t ^ 2 * φ 1 + t ^ 3 * φ 2
      = 1 * (1 - t) ^ 3 + 3 * (1 + φ 0 / 3) * (t * (1 - t) ^ 2)
        + 3 * (1 + 2 * φ 0 / 3 - φ 1 / 3) * (t ^ 2 * (1 - t)) + (1 + φ 0 + φ 2 - φ 1) * t ^ 3 := by
    ring
  rcases eq_or_ne t 0 with ht0eq | ht0ne
  · subst ht0eq; norm_num
  · have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0ne)
    have h1t : 0 ≤ 1 - t := by linarith
    rw [hbernstein]
    have e1 : 0 ≤ (1 - t) ^ 3 := pow_nonneg h1t 3
    have e2 : 0 ≤ t * (1 - t) ^ 2 := mul_nonneg ht0 (pow_nonneg h1t 2)
    have e3 : 0 ≤ t ^ 2 * (1 - t) := mul_nonneg (pow_nonneg ht0 2) h1t
    have e4 : 0 < t ^ 3 := pow_pos ht0' 3
    nlinarith [mul_nonneg hp1 e2, mul_nonneg hp2 e3, mul_pos hQ e4, e1]

/-- `cplxCond` 版。`s := t²∈[0,1]` の置換のもとで再び3次(`s` について)の
Bernstein 分解に帰着する。`p1,p2` の非負性は、`h3`(`cplxCond<0`)と
`|φ_1-φ_3|<2`・`|φ_3|<1` から出る2次形式の評価(`(x-2y)²≥0` 型の補題)で示す。 -/
theorem cplxCond_scale_neg {φ : Fin 3 → ℝ} (hSt3 : St3 φ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ^ 6 * φ 2 ^ 2 - t ^ 4 * φ 0 * φ 2 - t ^ 2 * φ 1 - 1 < 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hSt3
  have h4' : |φ 0 - φ 2| < 2 := h4
  rw [abs_lt] at h4'
  have ha : 0 < 1 - φ 0 - φ 1 - φ 2 := by
    have h1' := h1; simp only [phiAt1, Fin.sum_univ_three] at h1'; linarith
  have hQ : 0 < 1 + φ 0 + φ 2 - φ 1 := by
    have h2' := h2
    simp only [phiAtNeg1, Fin.sum_univ_three] at h2'
    norm_num at h2'
    linarith
  have hR : 0 < φ 1 - φ 2 ^ 2 + φ 0 * φ 2 + 1 := by linarith
  have hS : 0 < 2 - (φ 0 - φ 2) := by linarith [h4'.2]
  have hT : 0 < 2 + (φ 0 - φ 2) := by linarith [h4'.1]
  have hphi2lt1 : φ 2 < 1 := by nlinarith [ha, hR, hS]
  have hphi2gtm1 : -1 < φ 2 := by nlinarith [hQ, hR, hT]
  -- `p1 ≥ 0`: `φ1 > φ2²-φ0φ2-1 = -(φ0-φ2)φ2-1 > -3` via
  -- `4(φ0-φ2)φ2 ≤ (φ0-φ2)²+4φ2² < 4+4 = 8`.
  have hp1 : 0 ≤ 1 + φ 1 / 3 := by
    nlinarith [hR, sq_nonneg (φ 0 - 3 * φ 2), mul_pos hS hT,
      mul_pos (sub_pos.mpr hphi2lt1 : (0:ℝ) < 1 - φ 2) (by linarith : (0:ℝ) < 1 + φ 2)]
  -- `p2 ≥ 0`: `3+2φ1+φ0φ2 > 1+2φ2²-φ0φ2 = (φ2-(φ0-φ2)/2)²+1-(φ0-φ2)²/4 > 0`.
  have hp2 : 0 ≤ 1 + 2 * φ 1 / 3 + φ 0 * φ 2 / 3 := by
    nlinarith [hR, sq_nonneg (3 * φ 2 - φ 0), mul_pos hS hT]
  have hp3 : 0 < 1 + φ 1 + φ 0 * φ 2 - φ 2 ^ 2 := by linarith [h3]
  have hbernstein : 1 + t ^ 2 * φ 1 + t ^ 4 * φ 0 * φ 2 - t ^ 6 * φ 2 ^ 2
      = 1 * (1 - t ^ 2) ^ 3 + 3 * (1 + φ 1 / 3) * (t ^ 2 * (1 - t ^ 2) ^ 2)
        + 3 * (1 + 2 * φ 1 / 3 + φ 0 * φ 2 / 3) * ((t ^ 2) ^ 2 * (1 - t ^ 2))
        + (1 + φ 1 + φ 0 * φ 2 - φ 2 ^ 2) * (t ^ 2) ^ 3 := by
    ring
  rcases eq_or_ne t 0 with ht0eq | ht0ne
  · subst ht0eq; norm_num
  · have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0ne)
    have hsle : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
    have hsge : (0:ℝ) ≤ t ^ 2 := sq_nonneg t
    have h1s : 0 ≤ 1 - t ^ 2 := by linarith
    have hpos : 0 < 1 + t ^ 2 * φ 1 + t ^ 4 * φ 0 * φ 2 - t ^ 6 * φ 2 ^ 2 := by
      rw [hbernstein]
      have e1 : 0 ≤ (1 - t ^ 2) ^ 3 := pow_nonneg h1s 3
      have e2 : 0 ≤ t ^ 2 * (1 - t ^ 2) ^ 2 := mul_nonneg hsge (pow_nonneg h1s 2)
      have e3 : 0 ≤ (t ^ 2) ^ 2 * (1 - t ^ 2) := mul_nonneg (pow_nonneg hsge 2) h1s
      have e4 : 0 < (t ^ 2) ^ 3 := pow_pos (pow_pos ht0' 2) 3
      nlinarith [mul_nonneg hp1 e2, mul_nonneg hp2 e3, mul_pos hp3 e4, e1]
    linarith

/-- 重み付きスケーリング `γ_t(φ) = (tφ_1,t²φ_2,t³φ_3)`。 -/
def γ3 (φ : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ := ![t * φ 0, t ^ 2 * φ 1, t ^ 3 * φ 2]

/-! ### 十分性の仕上げ: `St3 → IsStationary`

`4つ目の条件(`2>|φ_1-φ_3|`)のスケーリング保存は不要`。道 `t↦γ_t(φ)` が `t∈[0,1]`
の全域で `Ω3` に収まることを、既に証明した3つの強いスケーリング補題(いずれも
`≠0` を含意する)から直接示し、`t=1` の `φ` と `t=0` の `O_3` が `Ω3` の同じ
連結成分にいることから `φ∈L31=IsStationary` を結論する。 -/
theorem St3_imp_isStationary {φ : Fin 3 → ℝ} (hSt3 : St3 φ) : IsStationary φ := by
  have hcont : Continuous (γ3 φ) := by unfold γ3; fun_prop
  have hsub : γ3 φ '' Set.Icc (0:ℝ) 1 ⊆ Ω3 := by
    rintro ψ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hzero
      have h := phiAt1_scale_pos hSt3 ht0 ht1
      simp [γ3, phiAt1, Fin.sum_univ_three] at hzero
      linarith
    · intro hzero
      have h := phiAtNeg1_scale_pos hSt3 ht0 ht1
      simp [γ3, phiAtNeg1, Fin.sum_univ_three] at hzero
      norm_num at hzero
      linarith
    · intro hzero
      have h := cplxCond_scale_neg hSt3 ht0 ht1
      simp [γ3, cplxCond] at hzero
      linarith
  have hpre : IsPreconnected (γ3 φ '' Set.Icc (0:ℝ) 1) :=
    isPreconnected_Icc.image (γ3 φ) hcont.continuousOn
  have hmemO : (fun _ : Fin 3 => (0:ℝ)) ∈ γ3 φ '' Set.Icc (0:ℝ) 1 := by
    refine ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩
    funext i
    fin_cases i <;> simp [γ3]
  have hmemφ : φ ∈ γ3 φ '' Set.Icc (0:ℝ) 1 := by
    refine ⟨1, ⟨zero_le_one, le_refl 1⟩, ?_⟩
    funext i
    fin_cases i <;> simp [γ3]
  have hkey := hpre.subset_connectedComponentIn hmemO hsub
  have hmem : φ ∈ L31 := hkey hmemφ
  rw [L31_eq_isStationary] at hmem
  exact hmem

/-- **AR(3) の定常性の必要十分条件**: `St3 φ ↔ IsStationary φ`。 -/
theorem St3_iff_isStationary {φ : Fin 3 → ℝ} : St3 φ ↔ IsStationary φ :=
  ⟨St3_imp_isStationary, isStationary_imp_St3⟩

end StTopology
