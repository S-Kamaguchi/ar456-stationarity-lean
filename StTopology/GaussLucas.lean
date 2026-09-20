import Mathlib
import StTopology.VietaBound
import StTopology.RootPerturbation

set_option linter.style.header false

/-!
# Gauss–Lucas縮約 (`prop:gauss-lucas`, `5_kanren.tex` Section 3.6)

`p ≥ 2` かつ `p φ = (φ_1,…,φ_p)` が `AR(p)` で定常であるとき、
`p-1 φ' = ((p-1)/p·φ_1, (p-2)/p·φ_2, …, (p-m)/p·φ_m, …, 1/p·φ_{p-1})`
は `AR(p-1)` で定常である(逆は一般には成り立たない)。

論文の議論: `φ̃(x) = x^p - ∑_{m=1}^p φ_m x^{p-m}` を項別に微分して `p` で割ると、
`φ̃'(x)/p = x^{p-1} - ∑_{m=1}^{p-1} ((p-m)/p) φ_m x^{p-1-m}` となり、これは
`p-1 φ'` の逆特性多項式そのものである。`φ̃` の根はすべて凸集合 `D = {|z|<1}` に
入るので、Gauss–Lucas定理より `φ̃'` の根は `φ̃` の根の凸包(⊆D)に入り、
`φ̃'/p` すなわち `p-1 φ'` の逆特性多項式の根もすべて `D` に入る。

Lean での定式化: `p = n+1` (`n ≥ 1`、すなわち `p ≥ 2`) とし、`φ : Fin (n+1) → ℝ`、
`gaussLucasDeriv φ : Fin n → ℝ` を `p-1 φ'` の0-indexed版とする。命題の主張(`⇒`方向)
のみを形式化する(逆が成り立たないことは反例の存在を述べているだけで、形式化必須の
主張ではないため)。

核心は`charPoly`(`VietaBound.lean`、`φ̃(x)`に対応する`ℂ`係数多項式)の微分が
`(n+1)·charPoly (gaussLucasDeriv φ)` に一致するという恒等式(`derivative_charPoly`、
項別微分の計算)。ここから Mathlib の
`Polynomial.rootSet_derivative_subset_convexHull_rootSet`(Gauss–Lucas定理)と
単位開球の凸性(`convex_ball`)を組み合わせて主定理を得る。`IsStationary`の定義
(根を直接扱う`∀α,…`形式)と`Polynomial.rootSet`(`Polynomial.roots`ベース)の橋渡しには
`RootPerturbation.lean`の`mem_roots_charPoly_iff`を使う。
-/

open Finset Polynomial StTopology

namespace StTopology

/-- `gaussLucasDeriv φ` : `p-1 φ' = ((p-m)/p)φ_m`(`p=n+1`)の0-indexed版。
`i : Fin n` に対し `gaussLucasDeriv φ i = ((n-i)/(n+1)) * φ (i.castSucc)`。 -/
noncomputable def gaussLucasDeriv {n : ℕ} (φ : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => (((n : ℝ) - (i : ℕ)) / (n + 1)) * φ i.castSucc

/-- **核心の恒等式**: `charPoly φ` の微分は `(n+1) * charPoly (gaussLucasDeriv φ)` に一致する
(`φ̃'(x) = (n+1)·(p-1 φ' の逆特性多項式)`、項別微分の計算)。 -/
theorem derivative_charPoly {n : ℕ} (φ : Fin (n + 1) → ℝ) :
    Polynomial.derivative (charPoly φ)
      = Polynomial.C ((n : ℂ) + 1) * charPoly (gaussLucasDeriv φ) := by
  unfold charPoly
  rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_sum]
  have hn1 : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · rw [hn1]; congr 1
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last]
    -- 最後の項 (定数項 φ_p) は微分すると消える
    have hlast : Polynomial.derivative
        (Polynomial.C (φ (Fin.last n) : ℂ) * Polynomial.X ^ (n + 1 - 1 - n)) = 0 := by
      have hz : n + 1 - 1 - n = 0 := by omega
      rw [hz]; simp
    rw [hlast, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
    have hi : (i : ℕ) < n := i.isLt
    have hile : (i : ℕ) ≤ n := le_of_lt hi
    have hexp1 : n + 1 - 1 - ((i.castSucc : Fin (n + 1)) : ℕ) = n - (i : ℕ) := by simp
    have hexp2 : n - (i : ℕ) - 1 = n - 1 - (i : ℕ) := by omega
    rw [hexp1, hexp2]
    -- 係数の等式: φ_{i+1} * (n-i) = (n+1) * gaussLucasDeriv φ i
    have hcoefR : φ i.castSucc * ((n - (i : ℕ) : ℕ) : ℝ) = ((n : ℝ) + 1) * gaussLucasDeriv φ i := by
      unfold gaussLucasDeriv
      rw [Nat.cast_sub hile]
      have hn1ne : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    have hcoefC : (φ i.castSucc : ℂ) * ((n - (i : ℕ) : ℕ) : ℂ)
        = ((n : ℂ) + 1) * (gaussLucasDeriv φ i : ℂ) := by exact_mod_cast hcoefR
    calc Polynomial.C (φ i.castSucc : ℂ)
          * (Polynomial.C ((n - (i : ℕ) : ℕ) : ℂ) * Polynomial.X ^ (n - 1 - (i : ℕ)))
        = Polynomial.C ((φ i.castSucc : ℂ) * ((n - (i : ℕ) : ℕ) : ℂ))
            * Polynomial.X ^ (n - 1 - (i : ℕ)) := by rw [Polynomial.C_mul]; ring
      _ = Polynomial.C (((n : ℂ) + 1) * (gaussLucasDeriv φ i : ℂ))
            * Polynomial.X ^ (n - 1 - (i : ℕ)) := by rw [hcoefC]
      _ = Polynomial.C ((n : ℂ) + 1)
            * (Polynomial.C (gaussLucasDeriv φ i : ℂ) * Polynomial.X ^ (n - 1 - (i : ℕ))) := by
          rw [Polynomial.C_mul]; ring

/-- **`prop:gauss-lucas`**(`⇒`方向): `p φ` が定常(`p=n+1≥2`、`hn:0<n`)ならば、
`p-1 φ'`(`gaussLucasDeriv φ`)も定常。Gauss–Lucas定理
(`Polynomial.rootSet_derivative_subset_convexHull_rootSet`)を、`φ̃` の根が単位開球
(凸)に入ることと組み合わせて示す。 -/
theorem isStationary_gaussLucasDeriv {n : ℕ} (hn : 0 < n) {φ : Fin (n + 1) → ℝ}
    (hφ : IsStationary φ) : IsStationary (gaussLucasDeriv φ) := by
  intro α hα
  have hne : charPoly (gaussLucasDeriv φ) ≠ 0 := (charPoly_monic hn (gaussLucasDeriv φ)).ne_zero
  have hroot : α ∈ (charPoly (gaussLucasDeriv φ)).roots :=
    (mem_roots_charPoly_iff hn (gaussLucasDeriv φ) α).mpr hα
  have hIsRoot : (charPoly (gaussLucasDeriv φ)).IsRoot α := (Polynomial.mem_roots hne).mp hroot
  have hpne : charPoly φ ≠ 0 := (charPoly_monic (Nat.succ_pos n) φ).ne_zero
  have hcne : (Polynomial.C ((n : ℂ) + 1) : Polynomial ℂ) ≠ 0 := by
    simp only [ne_eq, Polynomial.C_eq_zero]
    intro h
    have hne1 : (n : ℝ) + 1 ≠ 0 := by positivity
    exact hne1 (by exact_mod_cast h)
  -- `derivative (charPoly φ)` の根であることに翻訳
  have hdne : Polynomial.derivative (charPoly φ) ≠ 0 := by
    rw [derivative_charPoly]; exact mul_ne_zero hcne hne
  have hdroot : (Polynomial.derivative (charPoly φ)).IsRoot α := by
    rw [derivative_charPoly, Polynomial.IsRoot, Polynomial.eval_mul]
    simp [Polynomial.IsRoot] at hIsRoot
    simp [hIsRoot]
  have hmemDrv : α ∈ (Polynomial.derivative (charPoly φ)).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hdne, by simpa using hdroot⟩
  -- Gauss–Lucas定理を適用
  have hdeg : 0 < (charPoly φ).degree := by
    rw [charPoly_degree (Nat.succ_pos n) φ]; exact_mod_cast Nat.succ_pos n
  have hsubset := Polynomial.rootSet_derivative_subset_convexHull_rootSet (P := charPoly φ) hdeg
  have hmemConv : α ∈ convexHull ℝ ((charPoly φ).rootSet ℂ) := hsubset hmemDrv
  -- `charPoly φ` の根はすべて単位開球(凸)に入る
  have hballsub : (charPoly φ).rootSet ℂ ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    rw [Polynomial.mem_rootSet] at hz
    have hzroot : z ∈ (charPoly φ).roots := (Polynomial.mem_roots hpne).mpr (by simpa using hz.2)
    have heq := (mem_roots_charPoly_iff (Nat.succ_pos n) φ z).mp hzroot
    have hlt := hφ z heq
    rw [Metric.mem_ball, dist_zero_right]
    exact hlt
  have hconvsub : convexHull ℝ ((charPoly φ).rootSet ℂ) ⊆ Metric.ball (0 : ℂ) 1 :=
    convexHull_min hballsub (convex_ball 0 1)
  have hfin : α ∈ Metric.ball (0 : ℂ) 1 := hconvsub hmemConv
  rwa [Metric.mem_ball, dist_zero_right] at hfin

end StTopology
