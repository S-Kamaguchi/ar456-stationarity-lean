import Mathlib
import StTopology.StepDown
import StTopology.AR1
import StTopology.AR6
import StTopology.AR6Sufficiency

set_option linter.style.header false

/-!
# 明示的記述の個数の上限 (`prop:count-bound`, `6_kanren.tex` Section 4.7)

`St(p)` が `⌈p/2⌉` 個以下の不等式で明示的に記述できる、という上限命題を形式化する。

**【2026-08-26修正】** 当初(2026-08-13)は基底ケースを`p=6`(`AR6.lean`/`AR6Sufficiency.lean`の
具体的4不等式記述、`hasExplicitDescription_six`)に取り、そこから帰納していたため、実際に
証明できていたのは`∀p≥6, HasExplicitDescription p (⌈p/2⌉+1)`であり、論文Proposition~12
(`⌈p/2⌉`、`+1`なし、全`p≥1`)より1個多い・範囲も狭い別の(弱い)命題になっていた。原因は
AR(6)のSection 4の具体的記述が`⌈6/2⌉=3`より1個多い4不等式である点(論文519行目でも
明記されている通り)が、そのまま`p≥6`の帰納全体に伝播していたため。論文の証明が実際に
基底ケースとする`p=1,2`(`hasExplicitDescription_one`・`hasExplicitDescription_two`)から
汎用の`isStationary_iff_stepDown_gen`/`isStationary_iff_twostepDown_gen`(AR(4)/(5)/(6)の
個別結果には非依存)で組み立て直し、`hasExplicitDescription_of_ge_one`として修正した。
`hasExplicitDescription_six`自体は`p=6`個別ケースの事実(Table 1の「Derived」列相当)として
引き続き真であり、削除せず残している(現在の一般帰納では参照されない)。

**【重要・注意】`HasExplicitDescription` は正則性を課しておらず、命題単体としては自明化する**:
下記の定義には `f i` の連続性・多項式性など一切の正則性条件を課していない。この結果、
`f 0 φ := if IsStationary φ then 1 else -1` という(実数値関数としては合法な)`f` を
とれば `HasExplicitDescription p 1` は**任意の `p` について定義から直ちに成り立ってしまい**、
`hasExplicitDescription_of_ge_one`(`1 ≤ ⌈p/2⌉` なので同じ `f` が使える)も、
以下で実際に構築した `phiDownGen` による帰納的構成を一切使わずに証明できてしまう
(2026-08-13、ユーザーからの指摘で判明)。

この問題を解消するには `Continuous (f i)` を課すことが自然な対応だが、検討の結果これは
見た目より難しいことが分かった:
1. **大域 `Continuous` は端的に偽**: `phiDownGen` は分母 `1-φ_last²` を含む有理関数であり、
   Lean の除算の junk value 規約(分母0なら値0)により `φ_last=±1` で実際に不連続になる
   (分子が非零な一般の点では `φ_last→1⁻` で発散し、`φ_last=1` ちょうどでの junk value に
   収束しない)。したがって `f' i ∘ phiDownGen` の大域連続性はそもそも証明不可能な命題。
2. **`ContinuousOn`(領域を制限した連続性)に緩めても、再帰構成のせいで見た目より重い**:
   例えば `{|φ_last|<1}` のような固定領域上の `ContinuousOn` を課そうとしても、
   `phiDownGen` がその領域から「次数を1つ落とした後の対応する領域(`|ψ_last|<1`)」へ
   写ることを一般には保証できない(定常性に近い構造を持たない、単に `|φ_last|<1` なだけの
   点では、`phiDownGen φ` 自身の最後の座標が `(-1,1)` に収まる保証がない)。合成を通じて
   連続性が保たれる「正しい定義域」を再帰的に(各段でそれ以前の段の値に依存する形で)
   追跡する必要があり、`AR6.lean` の `A6`・`B6` のように各段で分母を払って多項式化する
   のと同程度かそれ以上の作業量になる見込み(ユーザーとの相談の結果、この作業は見送り、
   現在の(正則性なしの)定式化のまま進める判断とした)。

**結論**: `prop:count-bound` の本当の数学的内容は `HasExplicitDescription` という
**命題(Prop)自体には宿っていない**(正則性がない以上、命題としては自明化しうる)。
実質的な内容は `hasExplicitDescription_of_ge_one` の**証明項**——`p` に関する強い帰納法の
中で実際に構築される、`f' i ∘ phiDownGen`(奇数段)・`f' i ∘ (phiDownGen∘phiDownGen)`
(偶数段、`lem:twostep` でマージ済み)という**具体的な有理式の連鎖**——の方にある。この
ファイルを読む際は、`HasExplicitDescription` という Prop の主張内容だけでなく、実際に
何が構築されているか(証明項の中身)を見る必要がある。
-/

open Finset StTopology

namespace StTopology

/-- `C-|D|>0 ↔ C-D>0 ∧ C+D>0`。`phiAt1>0 ∧ phiAtNeg1>0` を単一の不等式にまとめる際に使う
純代数的な一般補題。 -/
theorem sub_abs_pos_iff {C D : ℝ} : C - |D| > 0 ↔ (C - D > 0 ∧ C + D > 0) := by
  rw [gt_iff_lt, sub_pos, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- `St(p)` が `N` 個の不等式による明示的記述を持つ、という主張の定式化。
**正則性を課していないため命題単体としては自明化しうる。上のモジュールdocstring参照。** -/
def HasExplicitDescription (p N : ℕ) : Prop :=
  ∃ f : Fin N → (Fin p → ℝ) → ℝ, {φ : Fin p → ℝ | IsStationary φ} = {φ | ∀ i, 0 < f i φ}

/-- `phiAt1>0 ∧ phiAtNeg1>0` は単一の不等式 `(1-φ_2-φ_4-φ_6)-|φ_1+φ_3+φ_5|>0` と同値。 -/
theorem phiAt1_phiAtNeg1_iff {φ : Fin 6 → ℝ} :
    (phiAt1 φ > 0 ∧ phiAtNeg1 φ > 0)
      ↔ ((1 - φ 1 - φ 3 - φ 5) - |φ 0 + φ 2 + φ 4| > 0) := by
  simp only [phiAt1, phiAtNeg1, Fin.sum_univ_six]
  norm_num
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- `St6` を、`phiAt1>0 ∧ phiAtNeg1>0` を単一の不等式にまとめた4条件の形に書き換える。 -/
theorem St6_iff_four_ineq {φ : Fin 6 → ℝ} :
    St6 φ ↔ ((1 - φ 1 - φ 3 - φ 5) - |φ 0 + φ 2 + φ 4| > 0)
      ∧ ((1 - φ 5 ^ 2) - |φ 4 + φ 0 * φ 5| > 0)
      ∧ (-((1 + φ 5) * (B6 φ) ^ 2 + (A6 φ) * (B6 φ) * (φ 4 - φ 0)
          + (A6 φ) ^ 2 * (-1 - φ 1 + φ 3 - φ 5)) > 0)
      ∧ ((-2 * A6 φ) - |B6 φ| > 0) := by
  unfold St6
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨phiAt1_phiAtNeg1_iff.mp ⟨h1, h2⟩, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨ha, hb⟩ := phiAt1_phiAtNeg1_iff.mpr h1
    exact ⟨ha, hb, by linarith, by linarith, by linarith⟩

/-- **基底ケース `p=1`**(論文の証明が実際に使う基底ケース): `St(1)` は `⌈1/2⌉=1` 個の
不等式で明示的に記述できる。`isStationary_iff_St1`(`AR1.lean`)そのもの。 -/
theorem hasExplicitDescription_one : HasExplicitDescription 1 1 := by
  refine ⟨![fun φ => 1 - |φ 0|], ?_⟩
  ext φ
  simp only [Set.mem_setOf_eq]
  rw [isStationary_iff_St1]
  unfold St1
  constructor
  · intro h i
    fin_cases i
    change 0 < 1 - |φ 0|
    linarith
  · intro h
    have h0 : 0 < 1 - |φ 0| := h 0
    linarith

/-- **基底ケース `p=2`**(論文の証明が実際に使う基底ケース): `St(2)` は `⌈2/2⌉=1` 個の
不等式で明示的に記述できる(`lem:twostep`による`k_1,k_2`のマージ済み1条件)。 -/
theorem hasExplicitDescription_two : HasExplicitDescription 2 1 := by
  refine ⟨![fun φ => (1 - φ 1 ^ 2) - |φ 0 * (1 + φ 1)|], ?_⟩
  ext φ
  simp only [Set.mem_setOf_eq]
  rw [isStationary_iff_stepDown_gen (n := 1) (by norm_num)]
  have hlastIdx : (Fin.last 1 : Fin 2) = 1 := by decide
  have hlast : φ (Fin.last 1) = φ 1 := by rw [hlastIdx]
  have hrev : (Fin.rev (0 : Fin 1)) = (0 : Fin 1) := by decide
  have hpd : phiDownGen φ 0 = (φ 0 * (1 + φ 1)) / (1 - φ 1 ^ 2) := by
    change (φ (0 : Fin 1).castSucc + φ (Fin.last 1) * φ (Fin.rev (0 : Fin 1)).castSucc)
        / (1 - φ (Fin.last 1) ^ 2) = (φ 0 * (1 + φ 1)) / (1 - φ 1 ^ 2)
    simp only [hrev, hlast, Fin.castSucc_zero]
    ring
  rw [isStationary_iff_St1]
  unfold St1
  rw [hpd, hlast]
  have hmerge := twostep_merge (φ 0) (φ 0) (φ 1)
  rw [show φ 0 + φ 0 * φ 1 = φ 0 * (1 + φ 1) from by ring] at hmerge
  rw [← hmerge]
  constructor
  · intro h i
    fin_cases i
    change 0 < (1 - φ 1 ^ 2) - |φ 0 * (1 + φ 1)|
    linarith
  · intro h
    have h0 : 0 < (1 - φ 1 ^ 2) - |φ 0 * (1 + φ 1)| := h 0
    linarith

/-- **基底ケース `p=6`**(2026-08-13、現在の一般帰納(`hasExplicitDescription_of_ge_one`)
では参照されないが、Table 1の「Derived」列(4不等式)に対応する個別事実として残す):
`St(6)` は `4`(`=⌈6/2⌉+1`、`lem:twostep`を使わずAR(6)本体の生の記述の個数)個の不等式で
明示的に記述できる。 -/
theorem hasExplicitDescription_six : HasExplicitDescription 6 4 := by
  refine ⟨![fun φ => (1 - φ 1 - φ 3 - φ 5) - |φ 0 + φ 2 + φ 4|,
      fun φ => (1 - φ 5 ^ 2) - |φ 4 + φ 0 * φ 5|,
      fun φ => -((1 + φ 5) * (B6 φ) ^ 2 + (A6 φ) * (B6 φ) * (φ 4 - φ 0)
        + (A6 φ) ^ 2 * (-1 - φ 1 + φ 3 - φ 5)),
      fun φ => (-2 * A6 φ) - |B6 φ|], ?_⟩
  ext φ
  simp only [Set.mem_setOf_eq, ← St6_iff_isStationary, St6_iff_four_ineq]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i
    · change 0 < (1 - φ 1 - φ 3 - φ 5) - |φ 0 + φ 2 + φ 4|; linarith
    · change 0 < (1 - φ 5 ^ 2) - |φ 4 + φ 0 * φ 5|; linarith
    · change 0 < -((1 + φ 5) * (B6 φ) ^ 2 + (A6 φ) * (B6 φ) * (φ 4 - φ 0)
        + (A6 φ) ^ 2 * (-1 - φ 1 + φ 3 - φ 5)); linarith
    · change 0 < (-2 * A6 φ) - |B6 φ|; linarith
  · intro hf
    have h0 : 0 < (1 - φ 1 - φ 3 - φ 5) - |φ 0 + φ 2 + φ 4| := hf 0
    have h1 : 0 < (1 - φ 5 ^ 2) - |φ 4 + φ 0 * φ 5| := hf 1
    have h2 : 0 < -((1 + φ 5) * (B6 φ) ^ 2 + (A6 φ) * (B6 φ) * (φ 4 - φ 0)
        + (A6 φ) ^ 2 * (-1 - φ 1 + φ 3 - φ 5)) := hf 2
    have h3 : 0 < (-2 * A6 φ) - |B6 φ| := hf 3
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **`prop:count-bound`(上限 `⌈p/2⌉`、論文Proposition~12)**: `p≥1` ならば `St(p)` は
`⌈p/2⌉`(`=(p+1)/2`、自然数除算)個以下の不等式で明示的に記述できる。`p` に関する強い
帰納法。基底ケース `p=1,2` は `hasExplicitDescription_one`・`hasExplicitDescription_two`
(論文の証明が実際に使う基底ケース、AR(4)/(5)/(6)の個別結果には非依存)。奇数 `p` は1段の
Step-down(`isStationary_iff_stepDown_gen`)、偶数 `p` は `lem:twostep` でマージした2段の
Step-down(`isStationary_iff_twostepDown_gen`)を使い、それぞれ帰納法の仮定
(次数 `p-1` あるいは `p-2`) の記述に1個の不等式を追加する。 -/
theorem hasExplicitDescription_of_ge_one :
    ∀ p, 1 ≤ p → HasExplicitDescription p ((p + 1) / 2) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro hp
  rcases Nat.lt_or_ge p 3 with hp3 | hp3
  · interval_cases p
    · exact hasExplicitDescription_one
    · exact hasExplicitDescription_two
  · rcases Nat.even_or_odd p with hev | hodd
    · -- 偶数の場合: p = n+2, n = p-2 ≥ 2。`lem:twostep` によるマージ済み1段
      obtain ⟨k, hk⟩ := hev
      obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by omega⟩
      have hn1 : 1 ≤ n := by omega
      have hnpos : 0 < n := by omega
      obtain ⟨f', hfeq⟩ := ih n (by omega) hn1
      have hf'_iff : ∀ ψ : Fin n → ℝ, IsStationary ψ ↔ ∀ i, 0 < f' i ψ := fun ψ =>
        Set.ext_iff.mp hfeq ψ
      have hNeq : (n + 2 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      rw [hNeq]
      refine ⟨Fin.cons
        (fun φ : Fin (n + 2) → ℝ => 1 - φ (Fin.last (n + 1)) ^ 2
          - |φ (Fin.last n).castSucc + φ 0 * φ (Fin.last (n + 1))|)
        (fun i => f' i ∘ (phiDownGen ∘ phiDownGen)), ?_⟩
      ext φ
      simp only [Set.mem_setOf_eq]
      rw [isStationary_iff_twostepDown_gen hnpos, hf'_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine Fin.cases ?_ ?_
        · change 0 < 1 - φ (Fin.last (n + 1)) ^ 2
              - |φ (Fin.last n).castSucc + φ 0 * φ (Fin.last (n + 1))|
          linarith
        · intro j
          change 0 < f' j ((phiDownGen ∘ phiDownGen) φ)
          exact h2 j
      · intro h
        refine ⟨?_, fun j => by have := h j.succ; simpa using this⟩
        have h0 := h 0
        simp only [Fin.cons_zero] at h0
        linarith
    · -- 奇数の場合: p = n+1, n = p-1 ≥ 2。1段の Step-down
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
      have hn1 : 1 ≤ n := by omega
      have hnpos : 0 < n := by omega
      obtain ⟨f', hfeq⟩ := ih n (by omega) hn1
      have hf'_iff : ∀ ψ : Fin n → ℝ, IsStationary ψ ↔ ∀ i, 0 < f' i ψ := fun ψ =>
        Set.ext_iff.mp hfeq ψ
      have hNeq : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      rw [hNeq]
      refine ⟨Fin.cons
        (fun φ : Fin (n + 1) → ℝ => 1 - φ (Fin.last n) ^ 2)
        (fun i => f' i ∘ phiDownGen), ?_⟩
      ext φ
      simp only [Set.mem_setOf_eq]
      rw [isStationary_iff_stepDown_gen hnpos, hf'_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine Fin.cases ?_ ?_
        · change 0 < 1 - φ (Fin.last n) ^ 2
          rw [abs_lt] at h1; nlinarith [h1.1, h1.2]
        · intro j
          change 0 < f' j (phiDownGen φ)
          exact h2 j
      · intro h
        refine ⟨?_, fun j => by have := h j.succ; simpa using this⟩
        have h0 := h 0
        simp only [Fin.cons_zero] at h0
        rw [abs_lt]
        constructor <;> nlinarith [h0]

end StTopology
