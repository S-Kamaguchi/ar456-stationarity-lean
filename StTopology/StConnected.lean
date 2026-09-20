import Mathlib
import StTopology.StationarityRegions

set_option linter.style.header false

/-!
# St(p) の原点に関する星型性 (radial scaling)

`9_maximal_component_principle.tex` の Proposition の証明冒頭 (Section 3.7 参照,
"St(p) is open and path-connected (via the radial scaling map
`t↦(t φ_1,…,t^p φ_p)`, `0≤t≤1`), and contains `O_p`") にあたる事実を、
一般の `p` について形式化する。

具体的には: `φ` が定常 (`IsStationary φ`) ならば、`0≤t≤1` に対して係数を
`t^i` 倍してスケーリングした `(t φ_1, t^2 φ_2, …, t^p φ_p)` も定常である
(`isStationary_scale`)。また原点 `O_p` (すべての係数が0の点) 自身も定常である
(`isStationary_zero`)。この2つから、`t ↦ (fun i => t^(i+1) * φ i)` が
`O_p` (t=0) と `φ` (t=1) を St(p) 内で結ぶ経路を与えることになる
(St(p) の path-connectedness の核心部分。経路の連続性からの
`IsPreconnected` の組み立ては別途行う)。

証明の核心 (`t>0` の場合): `α := β/t` が元の逆特性方程式を満たすことを、
`p - (p-1-i) = i+1` という指数の関係だけを使って直接確認する。
判別式などによる場合分けは一切不要。
-/

open Finset

namespace StTopology

/-- 論文の重み付きスケーリング `γ_t(φ) := (t φ_1, t² φ_2, …, t^p φ_p)`
(`5_kanren.tex`, Section 3.9)。`Ξ`, `σ`, `μ`, `ν`, `r` の土台となる。 -/
def gammaT {p : ℕ} (t : ℝ) (φ : Fin p → ℝ) : Fin p → ℝ :=
  fun i : Fin p => t ^ ((i : ℕ) + 1) * φ i

theorem gammaT_zero {p : ℕ} (φ : Fin p → ℝ) :
    gammaT (0 : ℝ) φ = fun _ : Fin p => (0 : ℝ) := by
  funext i
  simp [gammaT, pow_succ]

theorem gammaT_one {p : ℕ} (φ : Fin p → ℝ) : gammaT (1 : ℝ) φ = φ := by
  funext i
  simp [gammaT]

/-- **半群律**: `γ_s ∘ γ_t = γ_{st}`(座標ごとに `(st)^{i+1} = s^{i+1} t^{i+1}` を
使うだけの純代数的な事実)。`prop:xi-homeo` の単射性・逆写像公式で使う。 -/
theorem gammaT_gammaT {p : ℕ} (s t : ℝ) (φ : Fin p → ℝ) :
    gammaT s (gammaT t φ) = gammaT (s * t) φ := by
  funext i
  unfold gammaT
  rw [mul_pow]
  ring

/-- `t≠0` のとき、`γ_t φ = O_p ↔ φ = O_p`(各座標の係数 `t^{i+1}` が非零なので)。 -/
theorem gammaT_eq_zero_iff {p : ℕ} {t : ℝ} (ht : t ≠ 0) (φ : Fin p → ℝ) :
    gammaT t φ = (fun _ => 0) ↔ φ = fun _ => 0 := by
  unfold gammaT
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    have ht' : t ^ ((i : ℕ) + 1) ≠ 0 := pow_ne_zero _ ht
    exact (mul_eq_zero.mp hi).resolve_left ht'
  · intro h
    funext i
    rw [h]
    ring

/-- St(p) の原点に関する星型性: 定常な `φ` を `0≤t≤1` でスケーリングしても
定常性は保たれる。 -/
theorem isStationary_scale {p : ℕ} (hp : 0 < p) {φ : Fin p → ℝ} (hφ : IsStationary φ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsStationary (gammaT t φ) := by
  intro β hβ
  unfold gammaT at hβ
  push_cast at hβ
  rcases ht0.eq_or_lt with ht0' | ht0'
  · -- t = 0 の場合: 右辺の各項が 0 になるので β^p = 0, したがって β = 0
    have hβ0 : β ^ p = 0 := by
      rw [hβ]
      apply Finset.sum_eq_zero
      intro i _
      have ht0eq : (t : ℂ) ^ ((i : ℕ) + 1) = 0 := by
        have ht0eq' : (t : ℝ) = 0 := ht0'.symm
        simp [ht0eq']
      simp [ht0eq]
    have hβeq : β = 0 := by
      have hpne : p ≠ 0 := hp.ne'
      exact (pow_eq_zero_iff hpne).mp hβ0
    simp [hβeq]
  · -- t > 0 の場合: α := β/t が元の方程式を満たすことを直接確認する
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0'.ne'
    have key : ∀ i : Fin p, (φ i : ℂ) * (β / (t : ℂ)) ^ (p - 1 - (i : ℕ))
        = ((t : ℂ) ^ ((i : ℕ) + 1) * (φ i : ℂ) * β ^ (p - 1 - (i : ℕ))) / (t : ℂ) ^ p := by
      intro i
      have hi : (i : ℕ) < p := i.2
      have ht1' : (t : ℂ) ^ (p - 1 - (i : ℕ)) ≠ 0 := pow_ne_zero _ htC
      have ht2' : (t : ℂ) ^ ((i : ℕ) + 1) ≠ 0 := pow_ne_zero _ htC
      have hts : (t : ℂ) ^ (p - 1 - (i : ℕ)) * (t : ℂ) ^ ((i : ℕ) + 1) = (t : ℂ) ^ p := by
        rw [← pow_add]
        congr 1
        omega
      rw [div_pow, ← hts]
      field_simp
    have hα_eq : (β / (t : ℂ)) ^ p
        = ∑ i : Fin p, (φ i : ℂ) * (β / (t : ℂ)) ^ (p - 1 - (i : ℕ)) := by
      rw [div_pow]
      simp_rw [key]
      rw [← Finset.sum_div, ← hβ]
    have hres := hφ (β / (t : ℂ)) hα_eq
    have htnorm : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht0']
    rw [norm_div, htnorm] at hres
    rw [div_lt_one ht0'] at hres
    linarith

/-- 原点 `O_p` (すべての係数が0の点) は定常である。 -/
theorem isStationary_zero {p : ℕ} : IsStationary (fun _ : Fin p => (0 : ℝ)) := by
  intro α hα
  simp only [Complex.ofReal_zero, zero_mul, Finset.sum_const_zero] at hα
  rcases eq_or_ne p 0 with hp0 | hp0
  · subst hp0
    simp only [pow_zero] at hα
    exact absurd hα one_ne_zero
  · have hαeq : α = 0 := (pow_eq_zero_iff hp0).mp hα
    simp [hαeq]

/-- 径路 `t ↦ (t φ_1, t² φ_2, …, t^p φ_p)` は連続。 -/
theorem continuous_radialPath {p : ℕ} (φ : Fin p → ℝ) :
    Continuous (fun t : ℝ => gammaT t φ) := by
  apply continuous_pi
  intro i
  unfold gammaT
  fun_prop

/-- `t` を固定したとき、`φ ↦ γ_t(φ)` も連続 (`Mu.lean` の `μ` の上半連続性で使う)。 -/
theorem continuous_gammaT_apply {p : ℕ} (t : ℝ) :
    Continuous (fun φ : Fin p → ℝ => gammaT t φ) := by
  apply continuous_pi
  intro i
  unfold gammaT
  fun_prop

/-- **St(p) は `O_p` を含む path-connected 集合**。
`isStationary_scale` の与えるスケーリング径路が、任意の定常な `φ` を原点 `O_p` に
`St(p)` の内部だけを通って結ぶことによる。 -/
theorem isPathConnected_isStationary {p : ℕ} (hp : 0 < p) :
    IsPathConnected {φ : Fin p → ℝ | IsStationary φ} := by
  refine ⟨(fun _ : Fin p => (0 : ℝ)), isStationary_zero, ?_⟩
  intro ψ hψ
  simp only [Set.mem_setOf_eq] at hψ
  -- `t ↦ γ_t(ψ)` を `t : [0,1]` で走らせた径路。t=0 で原点、t=1 で ψ。
  refine JoinedIn.ofLine (f := fun t : ℝ => gammaT t ψ)
    (continuous_radialPath ψ).continuousOn (gammaT_zero ψ) (gammaT_one ψ) ?_
  rintro φ ⟨t, ht, rfl⟩
  simp only [Set.mem_Icc] at ht
  exact isStationary_scale hp hψ ht.1 ht.2

/-- St(p) は preconnected (`maximal_component_principle` の仮定 `hSt_preconn`)。 -/
theorem isPreconnected_isStationary {p : ℕ} (hp : 0 < p) :
    IsPreconnected {φ : Fin p → ℝ | IsStationary φ} :=
  (isPathConnected_isStationary hp).isConnected.isPreconnected

end StTopology
