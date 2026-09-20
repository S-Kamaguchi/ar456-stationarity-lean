import Mathlib

set_option linter.style.header false

/-!
# 一般2ステップマージ (`lem:twostep`, `6_kanren.tex` Section 4.7)

Schur–Cohn の反射係数 `k_m := ψ_m`、`k_{m-1} := (ψ_{m-1}+ψ_1ψ_m)/(1-ψ_m²)` (`ψ_m²≠1` のとき)
に対し、単一の不等式 `1-ψ_m² > |ψ_{m-1}+ψ_1ψ_m|` が `|k_m|<1 ∧ |k_{m-1}|<1` と同値であることを
示す一般的な補題。

AR(6) の形式化 (`AR6.lean` の `unit_cond6_of_isStationary`・`AR6Sufficiency.lean` の
`hψ4lt1`) で `p=6` の場合に個別に行った議論 (`|ψ_5|<1 ↔ 1-φ_6²>|φ_5+φ_1φ_6|`、Schur–Cohn の
2ステップ分の反射係数の有界性をまとめたもの) を、一般の `m` について述べたもの。命題の内容
自体は `m` と `ψ_1,…,ψ_{m-2}` の値には依存しないので、`ψ_1 =: a`, `ψ_{m-1} =: b`, `ψ_m =: c`
の3変数のみで述べる (`a,b,c` への対応は論文の添字通り)。
-/

namespace StTopology

/-- **`lem:twostep`(一般2ステップマージ)**: `k_m := c`, `k_{m-1} := (b+ac)/(1-c²)`
(実数の除算、`1-c²=0` のときは Lean の junk value `0` を返すが、その場合は左右いずれの
条件も成り立たないので問題にならない) に対し、
`1-c² > |b+ac|  ↔  |c|<1 ∧ |k_{m-1}|<1`。 -/
theorem twostep_merge (a b c : ℝ) :
    (1 - c ^ 2 > |b + a * c|) ↔ (|c| < 1 ∧ |(b + a * c) / (1 - c ^ 2)| < 1) := by
  constructor
  · intro h
    have hc2pos : (0 : ℝ) < 1 - c ^ 2 := lt_of_le_of_lt (abs_nonneg _) h
    have hclt1 : |c| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith [hc2pos, sq_nonneg (c - 1), sq_nonneg (c + 1)]
    refine ⟨hclt1, ?_⟩
    rw [abs_div, abs_of_pos hc2pos, div_lt_one hc2pos]
    exact h
  · rintro ⟨hclt1, hklt1⟩
    have hc2pos : (0 : ℝ) < 1 - c ^ 2 := by
      have h1 := (abs_lt.mp hclt1).1
      have h2 := (abs_lt.mp hclt1).2
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - c) (by linarith : (0 : ℝ) < 1 + c)]
    rw [abs_div, abs_of_pos hc2pos, div_lt_one hc2pos] at hklt1
    exact hklt1

end StTopology
