/-
In 1963, Ronald Graham proved that every integer $n ≥ 78$ can be written as a sum of distinct positive integers $n = a_1 + ⋯ + a_r$ such that $1/a_1 + ⋯ + 1/a_r = 1$.

More generally, he (non-constructively) showed that for all rationals $α > 0$ and all positive integers $m$ there exists an $n_{α, m}$ such that for all positive integers $n ≥ n_{α, m}$ there exist distinct integers $a_1, …, a_r$, all larger than or equal to $m$, with $n = a_1 + ⋯ + a_r$ and $α = 1/a_1 + ⋯ + 1/a_r$.

Combining his ideas with results from Ernie Croot, I managed to show that for fixed $α$ we have the asymptotic

$$n_{α, m} = (1/2 - o_{α}(1))(e^{2α} - 1)m^2.$$

Conditional on Proposition 1 and 2 from Croot's paper, and conditional on the fact that smooth integers have positive density in every residue class, Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) managed to formalize the proof of the aforementioned $n_{α, m}$ asymptotic. This formalization can be found below.

References:
Graham, R. L., A theorem on partitions. J. Austral. Math. Soc. (1963), 435-441.
Croot, III, Ernest S., On unit fractions with denominators in short intervals. Acta Arith. (2001), 99-114.
W. van Doorn, Partitions with prescribed sum of rationals: asymptotic bounds. arXiv:2502.02200 (2025).

Lean version: leanprover/lean4:v4.28.0
Mathlib version: 8f9d9cff6bd728b17a24e163c9402775d9e6a365
-/

import Mathlib

open Finset Filter Topology Real

set_option maxHeartbeats 1600000

/-
----------------------------------
PART 1: Basic definitions and two axioms.
----------------------------------
-/

/-- We say that a triple (α m n) is Admissible, if a representation of `n` as a sum of distinct integers `≥ m` exists, whose reciprocals sum to `α`. -/
def Admissible (α : ℚ) (m : ℕ) (n : ℕ) : Prop :=
  ∃ S : Finset ℕ,
    (∀ a ∈ S, m ≤ a) ∧
    S.sum id = n ∧
    S.sum (fun a => (1 : ℚ) / a) = α

/-- `n_{α,m}` is the smallest positive integer `N` such that every `n ≥ N` admits a
representation as a sum of distinct integers `≥ m` whose reciprocals sum to `α`. -/
noncomputable def nAlphaM (α : ℚ) (m : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ ∀ n, N ≤ n → Admissible α m n}

/-- A natural number `n` is x-smooth if every prime factor of `n` is at most `x`. -/
def IsSmooth (x : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ x

/-- A natural number `n` is x-powersmooth if every prime power dividing `n` is at most `x`. -/
def IsPowersmooth (x : ℝ) (n : ℕ) : Prop :=
  ∀ (p k : ℕ), p.Prime → 1 ≤ k → p ^ k ∣ n → (p ^ k : ℝ) ≤ x

/-- AXIOM: Proposition 1 and 2 from Croot's paper. -/
axiom Croot_lemma :
    ∀ (α : ℚ), 0 < α → ∀ (ε : ℝ), 0 < ε →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ C₁ : Finset ℕ,
        (∀ a ∈ C₁, (m : ℝ) < (a : ℝ) ∧ (a : ℝ) < (m : ℝ) * Real.exp (α : ℝ)) ∧
        let β : ℚ := α - C₁.sum (fun a => (1 : ℚ) / (a : ℚ))
        -- (1) β ≈ 3α · (log log m / log m)
        (|(β : ℝ) - 3 * (α : ℝ) * (Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ))| ≤
          ε * |Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)|) ∧
        -- (2) denominator of β is m^{1/5}-powersmooth
        IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β.den ∧
        -- (3) Egyptian fraction decomposition in (m·eᵅ, (1+ε)·m·eᵅ)
        (∀ (s t : ℕ), Nat.Coprime s t → 0 < t →
          (β : ℝ) / 2 < (s : ℝ) / (t : ℝ) →
          (s : ℝ) / (t : ℝ) ≤ (β : ℝ) →
          IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) t →
          ∃ C₂ : Finset ℕ,
            (∀ a ∈ C₂, (m : ℝ) * Real.exp (α : ℝ) < (a : ℝ) ∧
              (a : ℝ) < (1 + ε) * (m : ℝ) * Real.exp (α : ℝ)) ∧
            C₂.sum (fun a => (1 : ℚ) / (a : ℚ)) = (s : ℚ) / (t : ℚ))

/-- AXIOM: Smooth integers have positive density in every residue class. -/
axiom smoothinarithgeneral :
    ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
    ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
      δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
        (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N})

/-
----------------------------------
PART 2: Proving Graham's original result that 78 ≤ n → Admissible 1 1 n.
----------------------------------
-/

/-- Stronger version of admissibility -/
def StrongAdmissible (n : ℕ) : Prop :=
  ∃ S : Finset ℕ,
    (∀ a ∈ S, 2 ≤ a ∧ a ≠ 39) ∧
    S.sum id = n ∧
    S.sum (fun a => (1 : ℚ) / a) = 1

lemma StrongAdmissible.toAdmissible {n : ℕ} (h : StrongAdmissible n) :
    Admissible 1 1 n := by
  obtain ⟨S, hS, hsum, hrecip⟩ := h
  exact ⟨S, fun a ha => by have := (hS a ha).1; omega, hsum, hrecip⟩

/-- Witness checker -/
def checkWitnessNat (n : ℕ) (S : List ℕ) : Bool :=
  S.Nodup &&
  S.all (fun a => decide (2 ≤ a) && decide (a ≠ 39)) &&
  decide (S.sum = n) &&
  (let l := S.foldl Nat.lcm 1; decide ((S.map (fun a => l / a)).sum = l))

/-
Every element of a list divides the foldl lcm.
-/
lemma dvd_foldl_lcm {a : ℕ} {S : List ℕ} (ha : a ∈ S) :
    a ∣ S.foldl Nat.lcm 1 := by
  induction S using List.reverseRecOn ; aesop;
  by_cases ha : a ∈ ‹List ℕ› <;> simp_all +decide [ List.foldl_append ];
  · exact Nat.dvd_trans ‹_› ( Nat.dvd_lcm_left _ _ );
  · exact Nat.dvd_lcm_right _ _

/-
Foldl lcm of positive elements is positive.
-/
lemma foldl_lcm_pos {S : List ℕ} (hpos : ∀ a ∈ S, 0 < a) :
    0 < S.foldl Nat.lcm 1 := by
  induction S using List.reverseRecOn <;> aesop

/-
If the LCM-based check passes and all elements are positive, the ℚ reciprocal sum is 1
-/
lemma lcm_check_implies_recip_sum {S : List ℕ} (hpos : ∀ a ∈ S, 0 < a)
    (hnodup : S.Nodup)
    (hlcm : (S.map (fun a => S.foldl Nat.lcm 1 / a)).sum = S.foldl Nat.lcm 1) :
    S.toFinset.sum (fun a => (1 : ℚ) / a) = 1 := by
  -- Let $l = \text{foldl lcm}_S 1$.
  set l := S.foldl Nat.lcm 1 with hldec
  have hldec_pos : 0 < l := by
    exact foldl_lcm_pos hpos;
  -- For each $a_i$ in $S$, we have $(1 / a_i : ℚ) = (l / a_i) / l$.
  have h_recip : ∀ a ∈ S.toFinset, (1 / (a : ℚ)) = ((l / a) : ℕ) / l := by
    intro a ha
    have h_div : a ∣ l := by
      apply dvd_foldl_lcm; aesop;
    field_simp [h_div];
    rw [ Nat.cast_div h_div ( Nat.cast_ne_zero.mpr <| ne_of_gt <| hpos a <| List.mem_toFinset.mp ha ) ];
  convert congr_arg ( fun x : ℕ => ( x : ℚ ) / l ) hlcm using 1;
  · convert Finset.sum_congr rfl h_recip using 1 ; norm_num [ Finset.sum_div _ _ _ ] ; ring_nf!;
    rw [ ← Finset.mul_sum _ _ _, List.sum_toFinset ] ; ring_nf;
    · ac_rfl;
    · assumption;
  · rw [ div_self ( by positivity ) ]

lemma checkWitnessNat_sound {n : ℕ} {S : List ℕ} (h : checkWitnessNat n S = true) :
    StrongAdmissible n := by
  simp only [checkWitnessNat, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hnodup, hge⟩, hsum⟩, hlcm⟩ := h
  have hpos : ∀ a ∈ S, 0 < a := by
    intro a ha
    have := hge a ha
    simp only at this
    omega
  have hconds : ∀ a ∈ S, 2 ≤ a ∧ a ≠ 39 := by
    intro a ha
    have := hge a ha
    simp only at this
    exact this
  refine ⟨S.toFinset, fun a ha => ?_, ?_, ?_⟩
  · exact hconds a (List.mem_toFinset.mp ha)
  · rw [List.sum_toFinset id hnodup]; simp [hsum]
  · exact lcm_check_implies_recip_sum hpos hnodup hlcm

def checkBaseCasesAuxNat : List (List ℕ) → ℕ → Bool
  | [], _ => true
  | S :: rest, n => checkWitnessNat n S && checkBaseCasesAuxNat rest (n + 1)

lemma checkBaseCasesAuxNat_sound (ws : List (List ℕ)) (start : ℕ) (m : ℕ)
    (hcheck : checkBaseCasesAuxNat ws start = true)
    (hge : start ≤ m) (hlt : m < start + ws.length) :
    StrongAdmissible m := by
  induction ws generalizing start m with
  | nil => simp [List.length] at hlt; omega
  | cons S rest ih =>
    simp only [checkBaseCasesAuxNat, Bool.and_eq_true] at hcheck
    obtain ⟨hS, hrest⟩ := hcheck
    by_cases h : m = start
    · subst h; exact checkWitnessNat_sound hS
    · exact ih (start + 1) m hrest (by omega) (by simp [List.length] at hlt ⊢; omega)

/-- Base case witnesses (78 ≤ n ≤ 333) -/
def baseCaseWitnesses : List (List ℕ) := [
  [3, 4, 8, 9, 12, 18, 24],  -- 78
  [2, 3, 10, 24, 40],  -- 79
  [2, 4, 10, 15, 21, 28],  -- 80
  [2, 3, 12, 16, 48],  -- 81
  [2, 4, 9, 18, 21, 28],  -- 82
  [3, 4, 7, 9, 14, 18, 28],  -- 83
  [2, 4, 11, 12, 22, 33],  -- 84
  [2, 4, 10, 15, 18, 36],  -- 85
  [2, 5, 9, 10, 15, 45],  -- 86
  [2, 4, 8, 21, 24, 28],  -- 87
  [3, 4, 7, 8, 14, 24, 28],  -- 88
  [2, 6, 7, 8, 24, 42],  -- 89
  [2, 7, 9, 12, 14, 18, 28],  -- 90
  [3, 4, 6, 11, 12, 22, 33],  -- 91
  [2, 4, 8, 18, 24, 36],  -- 92
  [2, 5, 8, 9, 24, 45],  -- 93
  [3, 4, 6, 8, 21, 24, 28],  -- 94
  [2, 3, 9, 27, 54],  -- 95
  [2, 6, 9, 12, 18, 21, 28],  -- 96
  [2, 4, 9, 16, 18, 48],  -- 97
  [3, 4, 5, 12, 18, 20, 36],  -- 98
  [3, 4, 6, 8, 18, 24, 36],  -- 99
  [2, 6, 7, 8, 21, 56],  -- 100
  [2, 6, 8, 12, 21, 24, 28],  -- 101
  [2, 4, 8, 16, 24, 48],  -- 102
  [2, 4, 8, 14, 35, 40],  -- 103
  [2, 4, 7, 21, 28, 42],  -- 104
  [2, 4, 7, 20, 30, 42],  -- 105
  [2, 6, 8, 11, 22, 24, 33],  -- 106
  [2, 6, 7, 14, 20, 28, 30],  -- 107
  [2, 3, 18, 21, 28, 36],  -- 108
  [2, 4, 7, 18, 36, 42],  -- 109
  [2, 3, 9, 24, 72],  -- 110
  [2, 3, 8, 42, 56],  -- 111
  [2, 4, 8, 14, 28, 56],  -- 112
  [2, 3, 8, 40, 60],  -- 113
  [2, 4, 7, 21, 24, 56],  -- 114
  [2, 3, 12, 14, 84],  -- 115
  [2, 6, 8, 12, 16, 24, 48],  -- 116
  [3, 4, 8, 11, 12, 22, 24, 33],  -- 117
  [2, 3, 16, 21, 28, 48],  -- 118
  [2, 4, 7, 16, 42, 48],  -- 119
  [2, 4, 14, 15, 20, 30, 35],  -- 120
  [2, 3, 8, 36, 72],  -- 121
  [2, 4, 7, 18, 28, 63],  -- 122
  [2, 3, 16, 18, 36, 48],  -- 123
  [2, 4, 8, 12, 42, 56],  -- 124
  [2, 5, 7, 20, 21, 28, 42],  -- 125
  [2, 4, 11, 18, 22, 33, 36],  -- 126
  [2, 3, 14, 24, 28, 56],  -- 127
  [2, 6, 7, 12, 21, 24, 56],  -- 128
  [2, 3, 15, 21, 28, 60],  -- 129
  [2, 6, 8, 9, 24, 27, 54],  -- 130
  [2, 4, 9, 14, 18, 84],  -- 131
  [3, 4, 7, 9, 18, 21, 28, 42],  -- 132
  [2, 6, 7, 12, 16, 42, 48],  -- 133
  [2, 3, 8, 33, 88],  -- 134
  [2, 3, 9, 22, 99],  -- 135
  [2, 4, 8, 14, 24, 84],  -- 136
  [2, 7, 8, 14, 18, 24, 28, 36],  -- 137
  [3, 4, 6, 9, 14, 18, 84],  -- 138
  [2, 3, 12, 24, 42, 56],  -- 139
  [2, 4, 12, 14, 24, 28, 56],  -- 140
  [2, 3, 8, 32, 96],  -- 141
  [2, 3, 14, 18, 42, 63],  -- 142
  [3, 4, 6, 8, 14, 24, 84],  -- 143
  [2, 4, 6, 22, 44, 66],  -- 144
  [2, 4, 9, 21, 27, 28, 54],  -- 145
  [2, 6, 8, 9, 21, 28, 72],  -- 146
  [2, 4, 8, 12, 33, 88],  -- 147
  [2, 4, 7, 14, 44, 77],  -- 148
  [2, 3, 12, 22, 44, 66],  -- 149
  [2, 5, 6, 12, 25, 100],  -- 150
  [2, 6, 7, 9, 28, 36, 63],  -- 151
  [2, 3, 14, 21, 28, 84],  -- 152
  [2, 4, 7, 14, 42, 84],  -- 153
  [2, 4, 6, 21, 44, 77],  -- 154
  [2, 4, 5, 24, 120],  -- 155
  [2, 9, 11, 12, 18, 21, 22, 28, 33],  -- 156
  [2, 3, 14, 18, 36, 84],  -- 157
  [2, 6, 8, 16, 18, 24, 36, 48],  -- 158
  [2, 3, 12, 21, 44, 77],  -- 159
  [2, 4, 9, 16, 27, 48, 54],  -- 160
  [2, 3, 9, 21, 126],  -- 161
  [2, 3, 12, 24, 33, 88],  -- 162
  [3, 4, 7, 8, 16, 21, 48, 56],  -- 163
  [2, 3, 12, 21, 42, 84],  -- 164
  [2, 4, 9, 18, 22, 44, 66],  -- 165
  [2, 4, 8, 18, 36, 42, 56],  -- 166
  [2, 3, 14, 16, 48, 84],  -- 167
  [2, 6, 8, 14, 18, 28, 36, 56],  -- 168
  [2, 3, 12, 19, 57, 76],  -- 169
  [2, 4, 8, 22, 24, 44, 66],  -- 170
  [2, 3, 21, 27, 28, 36, 54],  -- 171
  [2, 3, 11, 24, 44, 88],  -- 172
  [2, 6, 7, 8, 36, 42, 72],  -- 173
  [2, 3, 12, 22, 36, 99],  -- 174
  [2, 4, 9, 16, 24, 48, 72],  -- 175
  [2, 3, 10, 33, 40, 88],  -- 176
  [2, 4, 6, 18, 63, 84],  -- 177
  [2, 4, 9, 18, 24, 33, 88],  -- 178
  [2, 4, 8, 18, 28, 56, 63],  -- 179
  [2, 3, 11, 21, 66, 77],  -- 180
  [2, 3, 7, 78, 91],  -- 181
  [2, 3, 12, 18, 63, 84],  -- 182
  [2, 6, 7, 11, 14, 66, 77],  -- 183
  [2, 3, 9, 42, 56, 72],  -- 184
  [2, 4, 7, 27, 28, 54, 63],  -- 185
  [2, 3, 12, 13, 156],  -- 186
  [2, 4, 7, 22, 42, 44, 66],  -- 187
  [2, 6, 7, 16, 18, 28, 48, 63],  -- 188
  [2, 3, 14, 16, 42, 112],  -- 189
  [2, 4, 8, 19, 24, 57, 76],  -- 190
  [2, 3, 16, 24, 42, 48, 56],  -- 191
  [2, 3, 10, 30, 42, 105],  -- 192
  [2, 4, 11, 12, 21, 66, 77],  -- 193
  [2, 4, 7, 12, 78, 91],  -- 194
  [2, 4, 6, 21, 36, 126],  -- 195
  [2, 4, 8, 18, 32, 36, 96],  -- 196
  [2, 3, 9, 36, 63, 84],  -- 197
  [2, 4, 7, 21, 36, 56, 72],  -- 198
  [2, 4, 6, 17, 68, 102],  -- 199
  [2, 3, 12, 21, 36, 126],  -- 200
  [2, 3, 7, 63, 126],  -- 201
  [2, 4, 9, 13, 18, 156],  -- 202
  [2, 4, 8, 18, 24, 63, 84],  -- 203
  [2, 3, 12, 17, 68, 102],  -- 204
  [2, 3, 14, 27, 42, 54, 63],  -- 205
  [2, 3, 18, 21, 36, 42, 84],  -- 206
  [2, 3, 9, 33, 72, 88],  -- 207
  [2, 6, 8, 9, 28, 36, 56, 63],  -- 208
  [2, 3, 8, 28, 168],  -- 209
  [2, 3, 14, 28, 42, 44, 77],  -- 210
  [2, 3, 14, 28, 36, 56, 72],  -- 211
  [2, 3, 9, 33, 66, 99],  -- 212
  [2, 6, 7, 9, 21, 42, 126],  -- 213
  [2, 3, 9, 32, 72, 96],  -- 214
  [2, 4, 7, 18, 44, 63, 77],  -- 215
  [2, 3, 16, 21, 42, 48, 84],  -- 216
  [2, 4, 8, 14, 21, 168],  -- 217
  [2, 3, 11, 26, 33, 143],  -- 218
  [2, 3, 9, 36, 52, 117],  -- 219
  [2, 3, 14, 24, 42, 63, 72],  -- 220
  [2, 3, 16, 19, 48, 57, 76],  -- 221
  [2, 4, 6, 18, 48, 144],  -- 222
  [2, 3, 13, 21, 28, 156],  -- 223
  [2, 4, 6, 16, 84, 112],  -- 224
  [2, 3, 14, 24, 42, 56, 84],  -- 225
  [2, 3, 16, 22, 36, 48, 99],  -- 226
  [2, 3, 12, 18, 48, 144],  -- 227
  [2, 3, 13, 18, 36, 156],  -- 228
  [2, 3, 12, 16, 84, 112],  -- 229
  [2, 4, 8, 14, 42, 48, 112],  -- 230
  [2, 3, 13, 28, 42, 52, 91],  -- 231
  [2, 3, 8, 63, 72, 84],  -- 232
  [2, 4, 8, 14, 33, 84, 88],  -- 233
  [2, 3, 11, 22, 42, 154],  -- 234
  [2, 3, 14, 22, 44, 66, 84],  -- 235
  [2, 3, 7, 56, 168],  -- 236
  [2, 3, 12, 24, 28, 168],  -- 237
  [2, 3, 8, 56, 78, 91],  -- 238
  [2, 6, 8, 9, 18, 28, 168],  -- 239
  [2, 3, 18, 22, 24, 72, 99],  -- 240
  [2, 3, 13, 24, 52, 56, 91],  -- 241
  [2, 3, 9, 36, 48, 144],  -- 242
  [2, 3, 12, 32, 42, 56, 96],  -- 243
  [2, 4, 6, 16, 72, 144],  -- 244
  [2, 3, 12, 27, 54, 63, 84],  -- 245
  [2, 3, 11, 42, 44, 56, 88],  -- 246
  [2, 3, 8, 52, 78, 104],  -- 247
  [2, 3, 14, 24, 33, 84, 88],  -- 248
  [2, 3, 12, 16, 72, 144],  -- 249
  [2, 3, 12, 28, 44, 77, 84],  -- 250
  [2, 3, 12, 33, 36, 66, 99],  -- 251
  [2, 3, 9, 28, 84, 126],  -- 252
  [2, 3, 12, 32, 36, 72, 96],  -- 253
  [2, 3, 8, 52, 72, 117],  -- 254
  [2, 3, 7, 54, 189],  -- 255
  [2, 3, 8, 27, 216],  -- 256
  [2, 3, 8, 48, 84, 112],  -- 257
  [2, 3, 8, 56, 63, 126],  -- 258
  [2, 3, 22, 24, 42, 44, 56, 66],  -- 259
  [2, 3, 12, 24, 63, 72, 84],  -- 260
  [2, 3, 11, 14, 231],  -- 261
  [2, 4, 6, 27, 52, 54, 117],  -- 262
  [2, 5, 9, 15, 27, 30, 54, 55, 66],  -- 263
  [2, 3, 18, 21, 28, 48, 144],  -- 264
  [2, 4, 7, 18, 42, 48, 144],  -- 265
  [2, 3, 12, 24, 56, 78, 91],  -- 266
  [2, 3, 12, 27, 52, 54, 117],  -- 267
  [2, 3, 8, 51, 68, 136],  -- 268
  [2, 4, 8, 12, 27, 216],  -- 269
  [2, 4, 6, 16, 66, 176],  -- 270
  [2, 3, 11, 28, 66, 77, 84],  -- 271
  [2, 3, 13, 14, 84, 156],  -- 272
  [2, 3, 21, 28, 33, 42, 56, 88],  -- 273
  [2, 4, 11, 12, 14, 231],  -- 274
  [2, 3, 12, 16, 66, 176],  -- 275
  [2, 3, 11, 32, 44, 88, 96],  -- 276
  [2, 3, 8, 44, 88, 132],  -- 277
  [2, 3, 14, 28, 33, 44, 154],  -- 278
  [2, 4, 6, 24, 27, 216],  -- 279
  [2, 4, 6, 22, 63, 84, 99],  -- 280
  [2, 3, 16, 18, 42, 56, 144],  -- 281
  [2, 3, 9, 26, 99, 143],  -- 282
  [2, 4, 7, 14, 32, 224],  -- 283
  [2, 3, 9, 27, 81, 162],  -- 284
  [2, 3, 12, 22, 63, 84, 99],  -- 285
  [2, 3, 12, 24, 56, 63, 126],  -- 286
  [2, 4, 7, 16, 42, 72, 144],  -- 287
  [2, 3, 16, 28, 48, 56, 63, 72],  -- 288
  [2, 3, 12, 16, 64, 192],  -- 289
  [2, 3, 12, 27, 48, 54, 144],  -- 290
  [2, 3, 11, 33, 44, 66, 132],  -- 291
  [2, 3, 9, 36, 44, 198],  -- 292
  [2, 4, 7, 24, 44, 63, 72, 77],  -- 293
  [2, 3, 12, 21, 32, 224],  -- 294
  [2, 3, 11, 26, 65, 78, 110],  -- 295
  [2, 3, 12, 24, 51, 68, 136],  -- 296
  [2, 3, 8, 42, 88, 154],  -- 297
  [2, 3, 11, 18, 66, 198],  -- 298
  [2, 3, 18, 21, 24, 63, 168],  -- 299
  [2, 3, 12, 22, 54, 99, 108],  -- 300
  [2, 3, 7, 51, 238],  -- 301
  [2, 3, 8, 44, 77, 168],  -- 302
  [2, 3, 8, 48, 66, 176],  -- 303
  [2, 4, 7, 18, 21, 252],  -- 304
  [2, 3, 12, 24, 44, 88, 132],  -- 305
  [2, 3, 13, 22, 44, 66, 156],  -- 306
  [2, 3, 8, 42, 84, 168],  -- 307
  [2, 4, 6, 21, 66, 77, 132],  -- 308
  [2, 3, 10, 35, 63, 70, 126],  -- 309
  [2, 3, 11, 21, 42, 231],  -- 310
  [2, 3, 9, 56, 72, 78, 91],  -- 311
  [2, 5, 6, 10, 34, 255],  -- 312
  [2, 3, 12, 21, 66, 77, 132],  -- 313
  [2, 4, 7, 12, 51, 238],  -- 314
  [2, 4, 7, 14, 54, 108, 126],  -- 315
  [2, 3, 11, 33, 36, 99, 132],  -- 316
  [2, 3, 8, 38, 114, 152],  -- 317
  [2, 4, 6, 27, 36, 81, 162],  -- 318
  [2, 4, 8, 16, 17, 272],  -- 319
  [2, 3, 9, 52, 72, 78, 104],  -- 320
  [2, 3, 12, 26, 36, 99, 143],  -- 321
  [2, 4, 8, 11, 33, 264],  -- 322
  [2, 3, 9, 54, 63, 84, 108],  -- 323
  [2, 4, 6, 18, 42, 252],  -- 324
  [2, 3, 12, 24, 42, 88, 154],  -- 325
  [2, 3, 11, 24, 66, 88, 132],  -- 326
  [2, 3, 8, 44, 72, 198],  -- 327
  [2, 3, 11, 18, 63, 231],  -- 328
  [2, 3, 9, 27, 72, 216],  -- 329
  [2, 3, 9, 48, 72, 84, 112],  -- 330
  [2, 3, 9, 56, 63, 72, 126],  -- 331
  [2, 3, 9, 24, 126, 168],  -- 332
  [2, 3, 12, 21, 52, 117, 126]  -- 333
]

set_option maxRecDepth 4096 in
lemma baseCases_verified :
    checkBaseCasesAuxNat baseCaseWitnesses 78 = true := by decide

set_option maxRecDepth 4096 in
lemma strongAdmissible_base {n : ℕ} (h1 : 78 ≤ n) (h2 : n ≤ 333) :
    StrongAdmissible n := by
  have hlen : baseCaseWitnesses.length = 256 := by decide
  exact checkBaseCasesAuxNat_sound baseCaseWitnesses 78 n baseCases_verified h1 (by omega)

/-- Inductive step: even case -/
lemma strongAdmissible_even_step {m : ℕ} (hm : StrongAdmissible m) :
    StrongAdmissible (2 * m + 2) := by
  obtain ⟨S, hS, hsum, hrecip⟩ := hm
  set f : ℕ → ℕ := fun x => x * 2 with hf_def
  have hinj : Set.InjOn f (↑S : Set ℕ) :=
    fun a _ b _ h => by simp [f] at h; omega
  have hdisj : Disjoint ({2} : Finset ℕ) (S.image f) := by
    rw [Finset.disjoint_left]
    intro a ha
    simp only [Finset.mem_singleton] at ha; subst ha
    rw [Finset.mem_image]
    rintro ⟨b, hb, hb2⟩
    simp [f] at hb2
    have := (hS b hb).1; omega
  refine ⟨{2} ∪ S.image f, ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at ha
    rcases ha with rfl | ⟨b, hb, rfl⟩
    · exact ⟨le_refl _, by omega⟩
    · constructor
      · have := (hS b hb).1; simp [f]; omega
      · have := (hS b hb).1; simp [f]; omega
  · rw [Finset.sum_union hdisj, Finset.sum_singleton, Finset.sum_image hinj]
    simp only [id, f]
    have h1 : ∑ x ∈ S, (x * 2) = 2 * ∑ x ∈ S, x := by
      rw [Finset.mul_sum]; congr 1; ext; ring
    have h2 : S.sum id = m := hsum
    simp only [id] at h2
    rw [h1]; omega
  · rw [Finset.sum_union hdisj, Finset.sum_singleton, Finset.sum_image hinj]
    simp only [f]
    have key : ∑ x ∈ S, ((1 : ℚ) / ↑(x * 2)) = (1 / 2) * ∑ x ∈ S, ((1 : ℚ) / ↑x) := by
      rw [Finset.mul_sum]
      congr 1; ext x; push_cast; ring
    rw [key, hrecip]; ring

/-- Inductive step: odd case -/
lemma strongAdmissible_odd_step {m : ℕ} (hm : StrongAdmissible m) :
    StrongAdmissible (2 * m + 179) := by
  obtain ⟨S, hS, hsum, hrecip⟩ := hm
  set f : ℕ → ℕ := fun x => x * 2 with hf_def
  set T : Finset ℕ := {3, 7, 78, 91} with hT_def
  have hinj : Set.InjOn f (↑S : Set ℕ) :=
    fun a _ b _ h => by simp [f] at h; omega
  have hdisj : Disjoint T (S.image f) := by
    rw [Finset.disjoint_left]
    intro a ha
    simp only [hT_def, Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_image]
    rintro ⟨b, hb, hb2⟩
    simp [f] at hb2
    rcases ha with rfl | rfl | rfl | rfl
    · omega
    · omega
    · have := (hS b hb).2; omega
    · omega
  refine ⟨T ∪ S.image f, ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_union, hT_def, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image] at ha
    rcases ha with (rfl | rfl | rfl | rfl) | ⟨b, hb, rfl⟩
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · constructor
      · have := (hS b hb).1; simp [f]; omega
      · have := (hS b hb).1; simp [f]; omega
  · rw [Finset.sum_union hdisj, Finset.sum_image hinj]
    have hT_sum : T.sum id = 179 := by decide
    simp only [id, f]
    have h1 : ∑ x ∈ S, (x * 2) = 2 * ∑ x ∈ S, x := by
      rw [Finset.mul_sum]; congr 1; ext; ring
    have h2 : S.sum id = m := hsum
    simp only [id] at h2 hT_sum
    rw [h1, hT_sum]; omega
  · rw [Finset.sum_union hdisj, Finset.sum_image hinj]
    have hT_recip : T.sum (fun a => (1 : ℚ) / ↑a) = 1 / 2 := by
      simp only [hT_def]
      norm_num [Finset.sum_cons, Finset.sum_singleton, Finset.sum_empty, Finset.sum_insert,
        Finset.mem_insert, Finset.mem_singleton]
    simp only [f]
    have key : ∑ x ∈ S, ((1 : ℚ) / ↑(x * 2)) = (1 / 2) * ∑ x ∈ S, ((1 : ℚ) / ↑x) := by
      rw [Finset.mul_sum]
      congr 1; ext x; push_cast; ring
    rw [hT_recip, key, hrecip]; ring

/-- Main induction for ogGraham -/
lemma strongAdmissible_main (n : ℕ) (h : 78 ≤ n) : StrongAdmissible n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h333 : n ≤ 333
    · exact strongAdmissible_base h h333
    · push_neg at h333
      by_cases heven : n % 2 = 0
      · -- n is even, write n = 2 * (n/2 - 1) + 2
        have hm_lt : n / 2 - 1 < n := by omega
        have hm_ge : 78 ≤ n / 2 - 1 := by omega
        have hstep := strongAdmissible_even_step (ih _ hm_lt hm_ge)
        convert hstep using 1; omega
      · -- n is odd, write n = 2 * ((n - 179) / 2) + 179
        have hm_lt : (n - 179) / 2 < n := by omega
        have hm_ge : 78 ≤ (n - 179) / 2 := by omega
        have hstep := strongAdmissible_odd_step (ih _ hm_lt hm_ge)
        convert hstep using 1; omega

/-- Every integer larger than or equal to $78$ can be written as a sum of distinct integers whose reciprocal sum is equal to $1$ -/
lemma ogGraham :
    ∀ n : ℕ, 78 ≤ n → Admissible 1 1 n := by
  intro n hn
  exact (strongAdmissible_main n hn).toAdmissible

/-
----------------------------------
PART 3: Auxiliary (power)smooth results.
----------------------------------
-/

lemma IsPowersmooth_of_dvd {x : ℝ} {a n : ℕ} (hn : IsPowersmooth x n) (ha : a ∣ n) :
    IsPowersmooth x a := fun p k hp hk hpk => hn p k hp hk (dvd_trans hpk ha)

/-- Monotonicity of IsPowersmooth -/
lemma IsPowersmooth_mono {y z : ℝ} (hyz : y ≤ z) {n : ℕ} (h : IsPowersmooth y n) :
    IsPowersmooth z n :=
  fun p k hp hk hpk => le_trans (h p k hp hk hpk) hyz

/-- 1 is x-powersmooth for any x ≥ 1. -/
lemma IsPowersmooth_one {x : ℝ} (hx : 1 ≤ x) : IsPowersmooth x 1 := by
  intro p k hp hk hpk
  have h3 : p ^ k = 1 := le_antisymm (Nat.le_of_dvd (by positivity) hpk) (Nat.one_le_pow k p hp.one_le)
  calc (p : ℝ) ^ k = (↑(p ^ k) : ℝ) := by push_cast; ring
    _ = 1 := by exact_mod_cast h3
    _ ≤ x := hx

-- Any positive natural ≤ x is x-powersmooth
lemma nat_le_is_powersmooth (x : ℝ) (n : ℕ) (hn : 0 < n) (hle : (n : ℝ) ≤ x) :
    IsPowersmooth x n := by
  intro p k hp hk hpk
  exact le_trans (by exact_mod_cast Nat.le_of_dvd hn hpk) hle

/-
Product of two ps-numbers: if a is y-ps and b is x-ps, then ab is (yx)-ps.
-/
lemma isPowersmooth_mul_two {y x z : ℝ} {a b : ℕ}
    (ha : IsPowersmooth y a) (hb : IsPowersmooth x b)
    (hbound : y * x ≤ z)
    (hy : 1 ≤ y) (hx : 1 ≤ x)
    (ha_pos : 0 < a) (hb_pos : 0 < b) :
    IsPowersmooth z (a * b) := by
  intro p k hp hk hdiv
  have href : p ^ (Nat.factorization a p + Nat.factorization b p) ∣ a * b := by
    rw [ pow_add ] ; exact mul_dvd_mul ( Nat.ordProj_dvd _ _ ) ( Nat.ordProj_dvd _ _ ) ;
  -- Consider two cases: $p^{Nat.factorization a p} \leq y$ and $p^{Nat.factorization b p} \leq x$.
  by_cases hpa : p ^ (Nat.factorization a p) ≤ y
  by_cases hpb : p ^ (Nat.factorization b p) ≤ x;
  · refine' le_trans _ hbound
    generalize_proofs at *; (
    refine' le_trans _ ( mul_le_mul hpa hpb ( by positivity ) ( by positivity ) ) ; norm_cast ; simp_all +decide [ Nat.pow_add ] ; (
    rw [ ← pow_add ] ; exact pow_le_pow_right₀ hp.one_lt.le ( by simpa [ Nat.factorization_mul ha_pos.ne' hb_pos.ne' ] using Nat.le_of_not_lt fun h => absurd ( Nat.dvd_trans ( pow_dvd_pow _ h ) hdiv ) ( Nat.pow_succ_factorization_not_dvd ( by positivity ) hp ) ) ;)) -- This line is just to handle the generalization proof孤儿. In a real proof, replace this with the actual proof steps.;
  · contrapose! hpb;
    by_cases hpb : Nat.factorization b p ≥ 1;
    · exact hb p ( Nat.factorization b p ) hp hpb ( Nat.ordProj_dvd _ _ );
    · aesop;
  · exact False.elim <| hpa <| ha p ( Nat.factorization a p ) hp ( Nat.pos_of_ne_zero <| fun h => by aesop ) <| Nat.ordProj_dvd _ _

/-
Product of three ps-numbers is ps with combined bound.
-/
lemma IsPowersmooth_mul_three {y x z : ℝ} {a b c : ℕ}
    (ha : IsPowersmooth y a) (hb : IsPowersmooth x b) (hc : IsPowersmooth x c)
    (hbound : y * x * x ≤ z)
    (hy : 1 ≤ y) (hx : 1 ≤ x)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c) :
    IsPowersmooth z (a * b * c) := by
  intro p k hp hk hdiv
  have href : (p ^ k : ℝ) ≤ y * x * x := by
    -- By definition of $IsPowersmooth$, we know that if $p^k$ divides $a * b * c$, then $p^k \leq y * x * x$.
    have hdiv_le_yx : (p ^ (Nat.factorization (a * b * c) p) : ℝ) ≤ y * x * x := by
      -- By definition of $IsPowersmooth$, we know that if $p^k$ divides $a * b * c$, then $p^k \leq y * x * x$. Use this fact.
      have hdiv_le_yx : (p ^ (Nat.factorization a p) : ℝ) ≤ y ∧ (p ^ (Nat.factorization b p) : ℝ) ≤ x ∧ (p ^ (Nat.factorization c p) : ℝ) ≤ x := by
        exact ⟨ if h : 1 ≤ Nat.factorization a p then ha p ( Nat.factorization a p ) hp h ( Nat.ordProj_dvd _ _ ) else by aesop, if h : 1 ≤ Nat.factorization b p then hb p ( Nat.factorization b p ) hp h ( Nat.ordProj_dvd _ _ ) else by aesop, if h : 1 ≤ Nat.factorization c p then hc p ( Nat.factorization c p ) hp h ( Nat.ordProj_dvd _ _ ) else by aesop ⟩;
      convert mul_le_mul ( mul_le_mul hdiv_le_yx.1 hdiv_le_yx.2.1 ( by positivity ) ( by positivity ) ) hdiv_le_yx.2.2 ( by positivity ) ( by positivity ) using 1 ; ring_nf;
      rw [ ← pow_add, ← pow_add, Nat.factorization_mul, Nat.factorization_mul ] <;> aesop;
    exact le_trans ( pow_le_pow_right₀ ( mod_cast hp.one_lt.le ) ( Nat.le_of_not_lt fun h => absurd ( Nat.dvd_trans ( pow_dvd_pow _ h ) hdiv ) ( Nat.pow_succ_factorization_not_dvd ( by positivity ) hp ) ) ) hdiv_le_yx;
  linarith

/-
12 is 4-powersmooth: the prime powers dividing 12 are 3 and 4, both ≤ 4.
-/
lemma isPowersmooth_4_12 : IsPowersmooth 4 12 := by
  intro p k hp hk hk';
  have : p ^ k ≤ 12 := Nat.le_of_dvd ( by decide ) hk'; interval_cases _ : p ^ k <;> norm_num at *;
  all_goals norm_cast at *;
  all_goals rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.Prime.pow_eq_iff ] ;
  · have := Nat.le_of_dvd ( by norm_num ) ( ‹p ^ ( k + 1 + 1 ) = 6› ▸ dvd_pow_self _ ( by norm_num ) ) ; interval_cases p <;> norm_num at *;
    · linarith [ Nat.pow_le_pow_right ( show 1 ≤ 2 by norm_num ) ( show k + 1 + 1 ≥ 3 by linarith [ show k ≥ 1 by contrapose! this; interval_cases k ; trivial ] ) ];
    · grind;
    · linarith [ Nat.pow_le_pow_right ( show 1 ≤ 5 by norm_num ) ( show k + 1 + 1 ≥ 2 by linarith ) ];
  · have := Nat.le_of_dvd ( by norm_num ) ( ‹p ^ ( k + 1 + 1 ) = 12› ▸ dvd_pow_self _ ( by norm_num ) ) ; interval_cases p <;> norm_num at *;
    · linarith [ Nat.pow_le_pow_right ( show 1 ≤ 2 by norm_num ) ( show k + 1 + 1 ≥ 4 by contrapose! this; interval_cases k + 1 + 1 <;> trivial ) ];
    · linarith [ Nat.pow_le_pow_right ( show 1 ≤ 3 by norm_num ) ( show k + 1 + 1 ≥ 3 by linarith [ show k ≥ 1 by contrapose! this; interval_cases k ; trivial ] ) ];
    · grind;
    · grind +splitImp;
    · linarith [ Nat.pow_le_pow_right ( show 1 ≤ 11 by norm_num ) ( show k + 1 + 1 ≥ 2 by linarith ) ]

/-
For m ≥ 4^30, 4 * m^(1/12) * m^(1/12) ≤ m^(1/5).
-/
lemma ps_bound_12_two_twelfths (m : ℕ) (hm : ⌈(4 : ℝ) ^ 30⌉₊ ≤ m) :
    4 * (m : ℝ) ^ ((1 : ℝ) / 12) * (m : ℝ) ^ ((1 : ℝ) / 12) ≤ (m : ℝ) ^ ((1 : ℝ) / 5) := by
  -- We can divide both sides by $m^{1/6}$ to get $4 \leq m^{1/30}$.
  suffices h_div : (4 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 30) by
    convert mul_le_mul_of_nonneg_right h_div ( show ( 0 : ℝ ) ≤ m ^ ( 1 / 6 : ℝ ) by positivity ) using 1 ; ring_nf;
    · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
    · rw [ ← Real.rpow_add' ] <;> norm_num;
  exact le_trans ( by norm_num ) ( Real.rpow_le_rpow ( by positivity ) ( Nat.cast_le.2 hm ) ( by norm_num ) )

/-
For m ≥ 4^30, 4 * m^(1/6) ≤ m^(1/5) (i.e. 4 ≤ m^(1/30)).
-/
lemma ps_bound_12_sixth (m : ℕ) (hm : ⌈(4 : ℝ) ^ 30⌉₊ ≤ m) :
    4 * (m : ℝ) ^ ((1 : ℝ) / 6) ≤ (m : ℝ) ^ ((1 : ℝ) / 5) := by
  -- We can divide both sides by $m^{1/6}$ to get $4 \leq m^{1/30}$.
  suffices h_div : (4 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 30) by
    exact le_trans ( mul_le_mul_of_nonneg_right h_div <| by positivity ) ( by rw [ ← Real.rpow_add ( by norm_cast; contrapose! hm; aesop ) ] ; ring_nf; norm_num );
  exact le_trans ( by norm_num ) ( Real.rpow_le_rpow ( by positivity ) ( Nat.cast_le.2 hm ) ( by norm_num ) )

/-
12 * n is m^(1/5)-ps when n is m^(1/6)-ps, for m ≥ 4^30.
-/
lemma ps_12_times_sixth {m : ℕ} {n : ℕ} (hn_pos : 0 < n)
    (hm : ⌈(4 : ℝ) ^ 30⌉₊ ≤ m)
    (hn_ps : IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 6)) n) :
    IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) (12 * n) := by
  convert isPowersmooth_mul_two _ _ _ _ _ _ _ using 1 <;> norm_num [ * ];
  exact 4;
  exact ( m : ℝ ) ^ ( 1 / 6 : ℝ );
  · exact isPowersmooth_4_12;
  · exact ((fun a => hn_ps) ∘ fun a => m) m;
  · exact ps_bound_12_sixth m hm;
  · norm_num;
  · exact Real.one_le_rpow ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by rintro rfl; norm_num at hm ) ( by norm_num )

/-- If M ≡ 2 (mod 210) and M ≥ 2, then M - 1 is coprime to 210. -/
lemma coprime_210_of_mod_eq_2 (M : ℕ) (hmod : (M : ℤ) ≡ 2 [ZMOD 210]) :
    Nat.Coprime (M - 1) 210 := by
  rw [ Int.ModEq ] at *; norm_cast at *; rw [ ← Nat.mod_add_div M 210 ] at *; simp_all +arith +decide;

lemma smooth_not_ps_witness {y : ℝ} {N : ℕ}
    (hs : IsSmooth y N) (hps : ¬IsPowersmooth y N) :
    ∃ (p k : ℕ), p.Prime ∧ 2 ≤ k ∧ (p : ℝ) ≤ y ∧ y < (p ^ k : ℝ) ∧ p ^ k ∣ N := by
      by_contra h;
      refine' hps fun p k hp hk hpk => _;
      by_cases hk2 : 2 ≤ k;
      · exact le_of_not_gt fun hy => h ⟨ p, k, hp, hk2, hs p hp ( dvd_trans ( dvd_pow_self _ ( by linarith ) ) hpk ), hy, hpk ⟩;
      · interval_cases k ; aesop

lemma ncard_multiples_le' (B : ℝ) (d : ℕ) (hd : 0 < d) :
    Set.ncard {n : ℕ | (n : ℝ) ≤ B ∧ d ∣ n} ≤ ⌊B / d⌋₊ + 1 := by
      -- Let $S = {n : ℕ | (n : ℝ) ≤ B ∧ d ∣ n}$.
      set S := {n : ℕ | (n : ℝ) ≤ B ∧ d ∣ n} with hS_def
      -- By definition of $S$, we know that every element $n$ in $S$ satisfies $n \leq \lfloor B \rfloor$.
      have h_bound : ∀ n ∈ S, n ≤ Nat.floor B := by
        exact fun n hn => Nat.le_floor hn.1;
      -- Since $S$ is a subset of $\{0, d, 2d, \ldots, \lfloor B \rfloor\}$, we can estimate its cardinality by counting the number of multiples of $d$ in this range.
      have h_subset : S ⊆ Finset.image (fun k => k * d) (Finset.range (Nat.floor (B / d) + 1)) := by
        intros n hn
        obtain ⟨hn_le, hn_div⟩ := hn
        obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * d := by
          exact exists_eq_mul_left_of_dvd hn_div
        have hk_le : k ≤ Nat.floor (B / d) := by
          exact Nat.le_floor <| by rw [ le_div_iff₀ <| by positivity ] ; push_cast [ hk ] at *; linarith;
        exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le), hk.symm⟩;
      exact le_trans ( Set.ncard_le_ncard h_subset ) ( by rw [ Set.ncard_coe_finset ] ; exact Finset.card_image_le.trans ( by norm_num ) )

lemma sum_inv_sq_telescoping (M : ℕ) (hM : 0 < M) (K : ℕ) :
    ∑ i ∈ Finset.range K, (1 : ℝ) / ((↑(M + 1 + i)) ^ 2) ≤ 1 / (M : ℝ) := by
      -- By comparison, we can use the fact that $\frac{1}{(M + 1 + i)^2} \leq \frac{1}{(M + i)(M + 1 + i)}$.
      have h_le : ∑ i ∈ Finset.range K, (1 / (M + 1 + i : ℝ) ^ 2) ≤ ∑ i ∈ Finset.range K, (1 / (M + i : ℝ) - 1 / (M + 1 + i : ℝ)) := by
        exact Finset.sum_le_sum fun i _ => by rw [ div_sub_div, div_le_div_iff₀ ] <;> ring_nf <;> nlinarith [ show ( M : ℝ ) ≥ 1 by norm_cast ] ;
      -- The series $\sum_{i=0}^{K-1} \left(\frac{1}{M+i} - \frac{1}{M+1+i}\right)$ is a telescoping series.
      have h_telescope : ∑ i ∈ Finset.range K, (1 / (M + i : ℝ) - 1 / (M + 1 + i : ℝ)) = 1 / (M : ℝ) - 1 / (M + K : ℝ) := by
        convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
      exact_mod_cast h_le.trans ( h_telescope.le.trans ( sub_le_self _ <| by positivity ) )

lemma ncard_exists_large_sq_dvd_le (B : ℝ) (hB : 0 ≤ B) (M : ℕ) (hM : 0 < M) :
    (Set.ncard {n : ℕ | (n : ℝ) ≤ B ∧ ∃ d : ℕ, M < d ∧ d ^ 2 ∣ n} : ℝ) ≤
      B / (M : ℝ) + Real.sqrt B + 1 := by
        -- We need to show that the cardinality of the set is bounded by the given expression.
        have h_card : Set.ncard {n : ℕ | (n : ℝ) ≤ B ∧ ∃ d, M < d ∧ d ^ 2 ∣ n} ≤ (∑ d ∈ Finset.Icc (M + 1) (Nat.floor (Real.sqrt B)), (Nat.floor (B / (d : ℝ) ^ 2) + 1)) + 1 := by
          have h_card : {n : ℕ | (n : ℝ) ≤ B ∧ ∃ d, M < d ∧ d ^ 2 ∣ n} ⊆ Finset.biUnion (Finset.Icc (M + 1) (Nat.floor (Real.sqrt B))) (fun d => Finset.image (fun m => d ^ 2 * m) (Finset.range (Nat.floor (B / d ^ 2) + 1))) ∪ {0} := by
            intro n hn
            obtain ⟨hn_le, d, hd_gt, hd_div⟩ := hn
            by_cases hn_zero : n = 0
            · simp [hn_zero]
            ·
              obtain ⟨ k, hk ⟩ := hd_div; simp_all +decide ;
              refine' ⟨ d, ⟨ hd_gt, Nat.le_floor <| Real.le_sqrt_of_sq_le <| by nlinarith [ show ( k : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr <| Nat.pos_of_ne_zero hn_zero.2 ] ⟩, k, Nat.le_floor <| by rw [ le_div_iff₀ <| by norm_cast; nlinarith ] ; linarith, rfl ⟩;
          refine le_trans ( Set.ncard_le_ncard h_card ) ?_;
          rw [ Set.ncard_eq_toFinset_card' ];
          simp +zetaDelta at *;
          refine' le_trans ( Finset.card_insert_le _ _ ) _;
          exact Nat.succ_le_succ ( le_trans ( Finset.card_biUnion_le ) <| Finset.sum_le_sum fun x hx => Finset.card_image_le.trans <| by simp );
        -- We need to show that the sum $\sum_{d=M+1}^{\lfloor \sqrt{B} \rfloor} \frac{B}{d^2}$ is bounded by $\frac{B}{M}$.
        have h_sum : ∑ d ∈ Finset.Icc (M + 1) (Nat.floor (Real.sqrt B)), (B / (d : ℝ) ^ 2) ≤ B / (M : ℝ) := by
          -- We'll use the fact that $\sum_{d=M+1}^{\infty} \frac{1}{d^2} \leq \frac{1}{M}$.
          have h_sum_le : ∑ d ∈ Finset.Icc (M + 1) (Nat.floor (Real.sqrt B)), (1 / (d : ℝ) ^ 2) ≤ 1 / (M : ℝ) := by
            convert sum_inv_sq_telescoping M hM ( ⌊Real.sqrt B⌋₊ - M ) using 1 ; norm_num [ add_comm, add_left_comm, Finset.sum_Ico_eq_sum_range ];
            erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
            rw [ Nat.add_comm, Nat.add_sub_add_right ];
          simpa [ div_eq_mul_inv, Finset.mul_sum _ _ _, mul_comm ] using mul_le_mul_of_nonneg_left h_sum_le hB;
        refine le_trans ( Nat.cast_le.mpr h_card ) ?_;
        simp +decide [ Finset.sum_add_distrib ];
        refine' add_le_add ( le_trans ( Finset.sum_le_sum fun _ _ => Nat.floor_le <| by positivity ) h_sum ) _;
        exact le_trans ( Nat.cast_le.mpr ( Nat.sub_le _ _ ) ) ( Nat.floor_le ( Real.sqrt_nonneg _ ) )

lemma ncard_exists_small_prime_large_power_le (B : ℝ) (hB : 0 ≤ B) (M L : ℕ) (hL : 0 < L) :
    (Set.ncard {n : ℕ | (n : ℝ) ≤ B ∧
      ∃ p : ℕ, p.Prime ∧ p ≤ M ∧ ∃ k : ℕ, 2 ≤ k ∧ L < p ^ k ∧ p ^ k ∣ n} : ℝ) ≤
      (M : ℝ) * (B / (L : ℝ) + 1) := by
        -- By the union bound, we have:
        have h_union_bound : (Set.ncard {n : ℕ | (n : ℝ) ≤ B ∧ ∃ p : ℕ, p.Prime ∧ p ≤ M ∧ ∃ k : ℕ, 2 ≤ k ∧ L < p ^ k ∧ p ^ k ∣ n} : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 M), (Set.ncard {n : ℕ | (n : ℝ) ≤ B ∧ ∃ k : ℕ, 2 ≤ k ∧ L < p ^ k ∧ p ^ k ∣ n} : ℝ) := by
          norm_cast;
          have h_union_bound : {n : ℕ | (n : ℝ) ≤ B ∧ ∃ p : ℕ, p.Prime ∧ p ≤ M ∧ ∃ k : ℕ, 2 ≤ k ∧ L < p ^ k ∧ p ^ k ∣ n} ⊆ ⋃ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 M), {n : ℕ | (n : ℝ) ≤ B ∧ ∃ k : ℕ, 2 ≤ k ∧ L < p ^ k ∧ p ^ k ∣ n} := by
            simp +zetaDelta at *;
            exact fun n hn => by rcases hn with ⟨ hn₁, p, hp₁, hp₂, k, hk₁, hk₂, hk₃ ⟩ ; exact Set.mem_iUnion₂.mpr ⟨ p, ⟨ ⟨ Nat.Prime.pos hp₁, hp₂ ⟩, hp₁ ⟩, hn₁, k, hk₁, hk₂, hk₃ ⟩ ;
          have h_card_union : ∀ {S : Finset ℕ} {f : ℕ → Set ℕ}, (Set.ncard (⋃ p ∈ S, f p)) ≤ ∑ p ∈ S, (Set.ncard (f p)) := by
            exact fun {S} {f} => set_ncard_biUnion_le S f;
          refine le_trans ?_ ( h_card_union );
          apply_rules [ Set.ncard_le_ncard ];
          exact Set.Finite.subset ( Set.finite_Iic ⌊B⌋₊ ) fun x hx => Nat.le_floor <| by aesop;
        -- For each prime $p$ in the range $1$ to $M$, we need to bound the number of $n \leq B$ such that there exists $k \geq 2$ with $p^k > L$ and $p^k \mid n$.
        have h_bound : ∀ p : ℕ, Nat.Prime p → p ≤ M → (Set.ncard {n : ℕ | (n : ℝ) ≤ B ∧ ∃ k : ℕ, 2 ≤ k ∧ L < p ^ k ∧ p ^ k ∣ n} : ℝ) ≤ B / L + 1 := by
          intro p hp hpM
          have h_bound : (Set.ncard {n : ℕ | (n : ℝ) ≤ B ∧ ∃ k : ℕ, 2 ≤ k ∧ L < p ^ k ∧ p ^ k ∣ n} : ℝ) ≤ (Set.ncard {n : ℕ | (n : ℝ) ≤ B ∧ p ^ (Nat.log p L + 1) ∣ n} : ℝ) := by
            gcongr;
            · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊B⌋₊, fun n hn => Nat.le_floor <| hn.1 ⟩;
            · rintro ⟨ k, hk₁, hk₂, hk₃ ⟩ ; exact dvd_trans ( pow_dvd_pow _ ( Nat.succ_le_of_lt ( Nat.log_lt_of_lt_pow ( by linarith ) ( by linarith ) ) ) ) hk₃;
          refine le_trans h_bound ?_;
          refine' le_trans ( Nat.cast_le.mpr <| ncard_multiples_le' _ _ _ ) _;
          · exact pow_pos hp.pos _;
          · norm_num [ Nat.floor_le, Nat.lt_floor_add_one ];
            refine' le_trans ( Nat.floor_le <| by positivity ) _;
            gcongr ; norm_cast ; exact Nat.lt_pow_succ_log_self hp.one_lt _ |> Nat.le_of_lt;
        refine le_trans h_union_bound ?_;
        refine' le_trans ( Finset.sum_le_sum fun p hp => h_bound p ( Finset.mem_filter.mp hp |>.2 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) ) _;
        norm_num [ mul_add ];
        exact add_le_add ( mul_le_mul_of_nonneg_right ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by simp ) ) ( by positivity ) ) ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by simp ) )

lemma smooth_not_ps_subset_union (ε x : ℝ) (hx : 0 < x) :
    {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧ IsSmooth (x ^ ε) N ∧ ¬IsPowersmooth (x ^ ε) N} ⊆
    {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧ ∃ d : ℕ, ⌊x ^ (ε / 2)⌋₊ < d ∧ d ^ 2 ∣ N} ∪
    {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧
      ∃ p : ℕ, p.Prime ∧ p ≤ ⌊x ^ (ε / 2)⌋₊ ∧
      ∃ k : ℕ, 2 ≤ k ∧ ⌊x ^ ε⌋₊ < p ^ k ∧ p ^ k ∣ N} := by
        intro N hN;
        obtain ⟨ p, k, hp, hk, hpk, hk', hk'' ⟩ := smooth_not_ps_witness hN.2.1 hN.2.2;
        by_cases h : p > ⌊x ^ ( ε / 2 ) ⌋₊;
        · exact Or.inl ⟨ hN.1, p, h, dvd_trans ( pow_dvd_pow _ hk ) hk'' ⟩;
        · refine Or.inr ⟨ hN.1, p, hp, le_of_not_gt h, k, hk, ?_, hk'' ⟩;
          rw [ Nat.floor_lt ] <;> first | positivity | aesop;

lemma ncard_smooth_not_ps_le (ε x : ℝ) (hε : 0 < ε) (hx : 0 < x)
    (hM : 0 < ⌊x ^ (ε / 2)⌋₊) (hL : 0 < ⌊x ^ ε⌋₊) :
    (Set.ncard {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧
      IsSmooth (x ^ ε) N ∧ ¬IsPowersmooth (x ^ ε) N} : ℝ) ≤
    (1 + ε) * x / ⌊x ^ (ε / 2)⌋₊ + Real.sqrt ((1 + ε) * x) + 1 +
    ⌊x ^ (ε / 2)⌋₊ * ((1 + ε) * x / ⌊x ^ ε⌋₊ + 1) := by
      -- Apply the bounds from the lemmas to each part of the union.
      have h_union_bound : Set.ncard {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧ IsSmooth (x ^ ε) N ∧ ¬IsPowersmooth (x ^ ε) N} ≤ Set.ncard {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧ ∃ d : ℕ, ⌊x ^ (ε / 2)⌋₊ < d ∧ d ^ 2 ∣ N} + Set.ncard {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧ ∃ p : ℕ, p.Prime ∧ p ≤ ⌊x ^ (ε / 2)⌋₊ ∧ ∃ k : ℕ, 2 ≤ k ∧ ⌊x ^ ε⌋₊ < p ^ k ∧ p ^ k ∣ N} := by
        refine' le_trans _ ( Set.ncard_union_le _ _ );
        fapply Set.ncard_le_ncard;
        · exact smooth_not_ps_subset_union ε x hx;
        · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊ ( 1 + ε ) * x⌋₊, fun n hn => Nat.le_floor <| hn.elim ( fun hn => hn.1 ) fun hn => hn.1 ⟩;
      refine le_trans ( Nat.cast_le.mpr h_union_bound ) ?_;
      convert add_le_add ( ncard_exists_large_sq_dvd_le ( ( 1 + ε ) * x ) ( by positivity ) ⌊x ^ ( ε / 2 ) ⌋₊ hM ) ( ncard_exists_small_prime_large_power_le ( ( 1 + ε ) * x ) ( by positivity ) ⌊x ^ ( ε / 2 ) ⌋₊ ⌊x ^ ε⌋₊ hL ) using 1 ; norm_num

lemma smooth_not_ps_sparse_large_eps (ε : ℝ) (hε' : 1 < ε)
    (η : ℝ) (hη : 0 < η) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 0 < x →
      (Set.ncard {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧
        IsSmooth (x ^ ε) N ∧ ¬IsPowersmooth (x ^ ε) N} : ℝ) < η * x := by
          -- Let's choose $x₀$ such that for $x \geq x₀$, $x^\epsilon > (1+\epsilon)x$.
          obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, 0 < x → x ^ ε > (1 + ε) * x := by
            -- We can choose $x₀$ such that for all $x \geq x₀$, $x^{\epsilon - 1} > 1 + \epsilon$.
            obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, 0 < x → x ^ (ε - 1) > 1 + ε := by
              have h_exp : Filter.Tendsto (fun x : ℝ => x ^ (ε - 1)) Filter.atTop Filter.atTop := by
                exact tendsto_rpow_atTop ( by linarith );
              exact Filter.eventually_atTop.mp ( h_exp.eventually_gt_atTop ( 1 + ε ) ) |> fun ⟨ x₀, hx₀ ⟩ => ⟨ x₀, fun x hx₁ hx₂ => hx₀ x hx₁ ⟩;
            exact ⟨ Max.max x₀ 1, fun x hx₁ hx₂ => by have := hx₀ x ( le_trans ( le_max_left _ _ ) hx₁ ) hx₂; rw [ show x ^ ε = x ^ ( ε - 1 ) * x by rw [ ← Real.rpow_add_one hx₂.ne', sub_add_cancel ] ] ; nlinarith ⟩;
          use Max.max x₀ 1;
          -- Since $x \geq x₀$ and $x > 0$, we have $x^\epsilon > (1+\epsilon)x$.
          intro x hx hx_pos
          have h_empty : {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧ IsSmooth (x ^ ε) N ∧ ¬IsPowersmooth (x ^ ε) N} = ∅ := by
            ext N
            simp;
            intro hN hs
            by_contra h_not_powersmooth
            obtain ⟨p, k, hp_prime, hk_ge2, hp_le_xε, hp_k_gt_xε, hp_k_div_N⟩ : ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ (p : ℝ) ≤ x ^ ε ∧ x ^ ε < (p ^ k : ℝ) ∧ p ^ k ∣ N := by
              exact smooth_not_ps_witness hs h_not_powersmooth;
            -- Since $p^k \mid N$, we have $p^k \leq N$.
            have hp_k_le_N : (p ^ k : ℝ) ≤ N := by
              norm_cast;
              apply Nat.le_of_dvd (Nat.pos_of_ne_zero (by
              rintro rfl; simp_all +decide [ IsSmooth, IsPowersmooth ] ;
              exact absurd ( hs ( Nat.find ( Nat.exists_infinite_primes ( ⌊x ^ ε⌋₊ + 1 ) ) ) ( Nat.find_spec ( Nat.exists_infinite_primes ( ⌊x ^ ε⌋₊ + 1 ) ) |>.2 ) ) ( by exact not_le_of_gt ( Nat.lt_of_floor_lt ( Nat.find_spec ( Nat.exists_infinite_primes ( ⌊x ^ ε⌋₊ + 1 ) ) |>.1 ) ) ))) hp_k_div_N;
            linarith [ hx₀ x ( le_trans ( le_max_left _ _ ) hx ) hx_pos ];
          aesop

lemma bound_tendsto_zero (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1) :
    Filter.Tendsto (fun x : ℝ =>
      ((1 + ε) * x / ⌊x ^ (ε / 2)⌋₊ + Real.sqrt ((1 + ε) * x) + 1 +
      ⌊x ^ (ε / 2)⌋₊ * ((1 + ε) * x / ⌊x ^ ε⌋₊ + 1)) / x)
      Filter.atTop (nhds 0) := by
        -- We'll use the fact that if the denominator grows much faster than the numerator, the limit will be zero.
        have h_lim : Filter.Tendsto (fun x : ℝ => (1 + ε) / ⌊x ^ (ε / 2)⌋₊) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => Real.sqrt ((1 + ε) * x) / x) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => ⌊x ^ (ε / 2)⌋₊ * ((1 + ε) * x / ⌊x ^ ε⌋₊ + 1) / x) Filter.atTop (nhds 0) := by
          refine' ⟨ _, _, _, _ ⟩;
          · exact tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop.comp <| tendsto_rpow_atTop <| by positivity;
          · -- We can simplify the expression inside the limit.
            suffices h_simp : Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + ε) / Real.sqrt x) Filter.atTop (nhds 0) by
              refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.sqrt_mul ( by positivity ), div_eq_div_iff ] <;> ring_nf <;> norm_num [ hx.le, hx.ne' ] );
            exact tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
          · exact tendsto_const_nhds.div_atTop Filter.tendsto_id;
          · -- We can split the term into two parts: $(1 + ε) * x / ⌊x^ε⌋₊$ and $1$.
            have h_split : Filter.Tendsto (fun x : ℝ => (⌊x ^ (ε / 2)⌋₊ : ℝ) * ((1 + ε) * x / ⌊x ^ ε⌋₊) / x) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => (⌊x ^ (ε / 2)⌋₊ : ℝ) / x) Filter.atTop (nhds 0) := by
              constructor;
              · -- We can simplify the expression inside the limit.
                suffices h_simp : Filter.Tendsto (fun x : ℝ => (⌊x ^ (ε / 2)⌋₊ : ℝ) * (1 + ε) / ⌊x ^ ε⌋₊) Filter.atTop (nhds 0) by
                  refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ eq_div_iff hx.ne' ] ; ring );
                -- We can bound the expression by noting that $\frac{\lfloor x^{\epsilon/2} \rfloor}{\lfloor x^{\epsilon} \rfloor} \leq \frac{x^{\epsilon/2}}{x^{\epsilon} - 1}$.
                have h_bound : ∀ x : ℝ, 1 < x → (⌊x ^ (ε / 2)⌋₊ : ℝ) * (1 + ε) / ⌊x ^ ε⌋₊ ≤ (x ^ (ε / 2) : ℝ) * (1 + ε) / (x ^ ε - 1) := by
                  intro x hx; gcongr <;> norm_num;
                  · exact Real.one_lt_rpow hx hε;
                  · exact Nat.floor_le ( by positivity );
                  · exact le_of_lt <| Nat.lt_floor_add_one _;
                -- We can simplify the expression $x^{ε/2} * (1 + ε) / (x^ε - 1)$ to $(1 + ε) / (x^{ε/2} - x^{-ε/2})$.
                suffices h_simp : Filter.Tendsto (fun x : ℝ => (1 + ε) / (x ^ (ε / 2) - x ^ (-ε / 2))) Filter.atTop (nhds 0) by
                  refine' squeeze_zero_norm' _ h_simp;
                  filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx ; rw [ Real.norm_of_nonneg ( by positivity ) ] ; convert h_bound x hx |> le_trans <| ?_ using 1 ; ring_nf;
                  rw [ show ε * ( -1 / 2 ) = ε * ( 1 / 2 ) - ε by ring, Real.rpow_sub ] <;> norm_num <;> ring_nf <;> try positivity;
                  field_simp;
                  rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf ; norm_num;
                norm_num [ neg_div ];
                exact tendsto_const_nhds.div_atTop ( Filter.Tendsto.atTop_add ( tendsto_rpow_atTop ( by positivity ) ) ( Filter.Tendsto.neg ( tendsto_rpow_neg_atTop ( by positivity ) ) ) );
              · -- We'll use the fact that $\frac{\lfloor x^{\epsilon/2} \rfloor}{x}$ is bounded above by $\frac{x^{\epsilon/2}}{x} = x^{\epsilon/2 - 1}$.
                have h_bound : ∀ x : ℝ, 0 < x → (⌊x ^ (ε / 2)⌋₊ : ℝ) / x ≤ x ^ (ε / 2 - 1) := by
                  intro x hx; rw [ Real.rpow_sub hx, Real.rpow_one ] ; rw [ div_le_div_iff₀ ] <;> first | positivity | nlinarith [ Nat.floor_le ( Real.rpow_nonneg hx.le ( ε / 2 ) ) ] ;
                refine' squeeze_zero_norm' _ _;
                exacts [ fun x => x ^ ( ε / 2 - 1 ), Filter.eventually_atTop.mpr ⟨ 1, fun x hx => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_bound x ( by positivity ) ⟩, by simpa using tendsto_rpow_neg_atTop ( show 0 < - ( ε / 2 - 1 ) by linarith ) ];
            convert h_split.1.add h_split.2 using 2 <;> ring;
        convert h_lim.1.add ( h_lim.2.1.add ( h_lim.2.2.1.add h_lim.2.2.2 ) ) using 2 <;> ring_nf;
        by_cases h : ‹ℝ› = 0 <;> simp +decide [ h, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
        · norm_num [ hε.ne' ];
        · ring

lemma smooth_not_ps_sparse_small_eps (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 0 < x →
      (Set.ncard {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧
        IsSmooth (x ^ ε) N ∧ ¬IsPowersmooth (x ^ ε) N} : ℝ) < η * x := by
          -- By bound_tendsto_zero, there exists x₁ such that for x ≥ x₁, f(x)/x < η.
          obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → 0 < x →
            ((1 + ε) * x / ⌊x ^ (ε / 2)⌋₊ + Real.sqrt ((1 + ε) * x) + 1 +
            ⌊x ^ (ε / 2)⌋₊ * ((1 + ε) * x / ⌊x ^ ε⌋₊ + 1)) / x < η := by
              have := bound_tendsto_zero ε hε hε';
              exact Filter.eventually_atTop.mp ( this.eventually ( gt_mem_nhds hη ) ) |> fun ⟨ x₁, hx₁ ⟩ => ⟨ x₁, fun x hx₁' hx₁'' => hx₁ x hx₁' ⟩;
          use Max.max x₁ 2;
          intro x hx hx'; specialize hx₁ x ( le_trans ( le_max_left _ _ ) hx ) hx'; rw [ div_lt_iff₀ hx' ] at hx₁;
          refine' lt_of_le_of_lt _ hx₁;
          convert ncard_smooth_not_ps_le ε x hε hx' _ _ using 1;
          · exact Nat.floor_pos.mpr ( Real.one_le_rpow ( by linarith [ le_max_right x₁ 2 ] ) ( by positivity ) );
          · exact Nat.floor_pos.mpr ( Real.one_le_rpow ( by linarith [ le_max_right x₁ 2 ] ) ( by linarith ) )

/-
Almost all smooth integers are powersmooth.
-/
lemma smooth_not_powersmooth_sparse (ε : ℝ) (hε : 0 < ε) :
    ∀ η : ℝ, 0 < η →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 0 < x →
      (Set.ncard {N : ℕ | (N : ℝ) ≤ (1 + ε) * x ∧
        IsSmooth (x ^ ε) N ∧ ¬IsPowersmooth (x ^ ε) N} : ℝ) < η * x := by
  intro η hη
  by_cases h : ε ≤ 1
  · exact smooth_not_ps_sparse_small_eps ε hε h η hη
  · exact smooth_not_ps_sparse_large_eps ε (not_le.mp h) η hη

/-
Powersmooth integers have positive density in every residue class.
-/
lemma smoothinarith
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N}))
    (a : ℤ) (b : ℕ) (hb : 0 < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
      δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
        (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsPowersmooth (x ^ ε) N}) := by
  obtain ⟨x₀, δ, hδ_pos, hδ⟩ := smooth_arith a b hb ε hε
  obtain ⟨x₁, hx₁⟩ := smooth_not_powersmooth_sparse ε hε (δ / 2) (half_pos hδ_pos)
  refine' ⟨Max.max x₀ (Max.max x₁ 1), δ / 2, half_pos hδ_pos, fun x hx => _⟩
  set S := {N : ℕ | x < N ∧ N < (1 + ε) * x ∧ (N : ℤ) ≡ a [ZMOD b] ∧ IsSmooth (x ^ ε) N}
  set P := {N : ℕ | x < N ∧ N < (1 + ε) * x ∧ (N : ℤ) ≡ a [ZMOD b] ∧ IsPowersmooth (x ^ ε) N}
  set B := {N : ℕ | N ≤ (1 + ε) * x ∧ IsSmooth (x ^ ε) N ∧ ¬IsPowersmooth (x ^ ε) N}
  have h_card : Set.ncard S ≤ Set.ncard P + Set.ncard B := by
    have h_sub : S ⊆ P ∪ B := by
      intro n hn
      simp only [Set.mem_setOf_eq, S] at hn
      by_cases hps : IsPowersmooth (x ^ ε) n
      · exact Or.inl ⟨hn.1, hn.2.1, hn.2.2.1, hps⟩
      · exact Or.inr ⟨le_of_lt hn.2.1, hn.2.2.2, hps⟩
    have h_ncard : Set.ncard S ≤ Set.ncard (P ∪ B) := by
      apply_rules [Set.ncard_le_ncard]
      refine Set.Finite.union ?_ ?_
      · exact Set.finite_iff_bddAbove.mpr ⟨⌊(1 + ε) * x⌋₊, fun n hn => Nat.le_floor <| hn.2.1.le⟩
      · exact Set.finite_iff_bddAbove.mpr ⟨⌊(1 + ε) * x⌋₊, fun n hn => Nat.le_floor <| hn.1⟩
    exact h_ncard.trans (Set.ncard_union_le _ _)
  -- By contradiction: if (δ/2)x > ncard P, then ncard S ≤ ncard P + ncard B < (δ/2)x + (δ/2)x = δx
  -- But δ*x ≤ ncard S, contradiction.
  by_contra h_neg
  push_neg at h_neg
  have hx_pos : 0 < x := by linarith [le_max_right x₀ (Max.max x₁ 1), le_max_right x₁ 1]
  have h_B_bound := hx₁ x (le_trans (le_max_of_le_right (le_max_left _ _)) hx) hx_pos
  have h_S_bound := hδ x (le_trans (le_max_left _ _) hx)
  have h_P_cast : (Set.ncard P : ℝ) < δ / 2 * x := h_neg
  have h_card_cast : (Set.ncard S : ℝ) ≤ (Set.ncard P : ℝ) + (Set.ncard B : ℝ) := by
    exact_mod_cast h_card
  linarith

/-
----------------------------------
PART 4: Definition and properties of β.
----------------------------------
-/

/-- For large m, β ≈ 3α·(log log m / log m) > 0 when ε < 3α. -/
lemma β_pos_for_large_m (α : ℚ) (_hα : 0 < α) (ε : ℝ) (_hε : 0 < ε)
    (hε_small : ε < 3 * (α : ℝ)) :
    ∀ᶠ (m : ℕ) in atTop,
    ∀ (β : ℚ),
    (|(β : ℝ) - 3 * (α : ℝ) * (Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ))| ≤
      ε * |Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)|) →
    0 < β := by
  have h_loglog_pos : ∀ᶠ (m : ℕ) in Filter.atTop,
      (0 : ℝ) < Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop (⌈Real.exp (Real.exp 1)⌉₊)] with m hm
    have hm_large : (m : ℝ) > Real.exp (Real.exp 1) := by
      calc (m : ℝ) > (⌈Real.exp (Real.exp 1)⌉₊ : ℝ) := by exact_mod_cast hm
        _ ≥ Real.exp (Real.exp 1) := Nat.le_ceil _
    have hm_gt_e : (m : ℝ) > Real.exp 1 :=
      lt_trans (lt_of_lt_of_le (by linarith [Real.add_one_le_exp 1]) (Real.add_one_le_exp (Real.exp 1))) hm_large
    have h1 : Real.log (m : ℝ) > 1 := by
      have := Real.log_lt_log (Real.exp_pos 1) hm_gt_e
      rwa [Real.log_exp] at this
    have h2 : Real.log (Real.log (m : ℝ)) > 0 := Real.log_pos h1
    exact div_pos h2 (lt_trans zero_lt_one h1)
  filter_upwards [h_loglog_pos] with m hm
  intro β hβ; rw [abs_le] at hβ; rw [abs_of_pos hm] at hβ
  exact_mod_cast (by nlinarith : (0 : ℝ) < β)

/-- For any fixed δ > 0, the Croot β is eventually < δ. -/
lemma beta_lt_any_pos (α : ℚ) (_hα : 0 < α) (ε : ℝ) (_hε : 0 < ε)
    (hε_small : ε < 3 * (α : ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (m : ℕ) in atTop,
    ∀ (β : ℚ),
    (|(β : ℝ) - 3 * (α : ℝ) * (Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ))| ≤
      ε * |Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)|) →
    0 < β → (β : ℝ) < δ := by
  have h_log_log_div_log : Filter.Tendsto (fun m : ℕ => |Real.log (Real.log m) / Real.log m|) Filter.atTop (nhds 0) := by
    suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) by
      simpa using Filter.Tendsto.abs ( h_log_y.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) )
    suffices h_log_recip : Filter.Tendsto (fun z : ℝ => z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
      exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] )
    norm_num +zetaDelta at *
    exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 )
  have h_beta_bound : ∀ᶠ m : ℕ in Filter.atTop, ∀ β : ℚ, |(β : ℝ) - 3 * α * (Real.log (Real.log m) / Real.log m)| ≤ ε * |Real.log (Real.log m) / Real.log m| → (β : ℝ) ≤ 3 * α * |Real.log (Real.log m) / Real.log m| + ε * |Real.log (Real.log m) / Real.log m| := by
    filter_upwards [ Filter.eventually_gt_atTop 1 ] with m hm β hβ using by cases abs_cases ( Real.log ( Real.log m ) / Real.log m ) <;> nlinarith [ abs_le.mp hβ, ( by norm_cast : ( 0 :ℝ ) < α ) ]
  have h_beta_lt : ∀ᶠ m : ℕ in Filter.atTop, ∀ β : ℚ, |(β : ℝ) - 3 * α * (Real.log (Real.log m) / Real.log m)| ≤ ε * |Real.log (Real.log m) / Real.log m| → (β : ℝ) < δ := by
    filter_upwards [ h_beta_bound, h_log_log_div_log.eventually ( gt_mem_nhds <| show 0 < δ / ( 3 * α + ε + 1 ) by positivity ) ] with m hm₁ hm₂ using fun β hβ => lt_of_le_of_lt ( hm₁ β hβ ) <| by
      have hf := abs_nonneg (Real.log (Real.log m) / Real.log m)
      have h3ae : (0 : ℝ) < 3 * (↑α : ℝ) + ε := by positivity
      have h3ae1 : (0 : ℝ) < 3 * (↑α : ℝ) + ε + 1 := by positivity
      have hmul := mul_lt_mul_of_pos_left hm₂ h3ae
      have hdiv : (3 * (↑α : ℝ) + ε) * (δ / (3 * (↑α : ℝ) + ε + 1)) < δ := by
        have : (3 * (↑α : ℝ) + ε) * (δ / (3 * (↑α : ℝ) + ε + 1)) =
          δ * ((3 * (↑α : ℝ) + ε) / (3 * (↑α : ℝ) + ε + 1)) := by ring
        rw [this]; exact mul_lt_of_lt_one_right hδ (div_lt_one h3ae1 |>.mpr (by linarith))
      nlinarith
  filter_upwards [ h_beta_lt ] with m hm using fun β hβ hβ' => hm β hβ

/-- For a positive rational β, β.num.toNat and β.den satisfy Croot's input conditions. -/
lemma rat_pos_Croot_input (β : ℚ) (hβ : 0 < β) :
    Nat.Coprime β.num.toNat β.den ∧
    0 < β.den ∧
    (β : ℝ) / 2 < (β.num.toNat : ℝ) / (β.den : ℝ) ∧
    (β.num.toNat : ℝ) / (β.den : ℝ) ≤ (β : ℝ) := by
  refine' ⟨ _, β.pos, _, _ ⟩
  · rw [ ← Int.natAbs_of_nonneg ( Rat.num_nonneg.mpr hβ.le ) ] ; exact β.reduced
  · rw [ div_lt_div_iff₀ ] <;> norm_cast <;> try linarith [ β.pos ]
    rw [ ← @Rat.num_div_den β ]
    rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> norm_cast <;> norm_num [ Rat.num_div_den ]
    · rw [ max_eq_left ( Rat.num_nonneg.mpr hβ.le ) ] ; nlinarith [ β.pos, Rat.num_pos.mpr hβ ]
    · exact β.pos
  · rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num [ Rat.cast_def ]
    · exact_mod_cast Int.toNat_of_nonneg ( Rat.num_nonneg.mpr hβ.le ) |> le_of_eq
    · exact β.pos

-- β·m eventually exceeds any fixed constant, from the Croot approximation β ≈ 3α·loglog m/log m
lemma beta_times_m_eventually_large (α : ℚ) (ε : ℝ) (hε : 0 < ε)
    (hε_3α : ε < 3 * (α : ℝ)) (C : ℝ) :
    ∀ᶠ (m : ℕ) in atTop,
    ∀ (β : ℚ),
    (|(β : ℝ) - 3 * (α : ℝ) * (Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ))| ≤
      ε * |Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)|) →
    0 < β → C ≤ (β : ℝ) * (↑m : ℝ) := by
  -- Since $3\alpha - \epsilon > 0$, we have $\beta \geq (3\alpha - \epsilon) \log \log m / \log m$.
  have h_beta_lower_bound : ∀ᶠ m : ℕ in Filter.atTop, ∀ β : ℚ, abs ((β : ℝ) - 3 * α * (Real.log (Real.log m) / Real.log m)) ≤ ε * abs (Real.log (Real.log m) / Real.log m) → 0 < β → (β : ℝ) ≥ (3 * α - ε) * (Real.log (Real.log m) / Real.log m) := by
    filter_upwards [ Filter.eventually_gt_atTop 2 ] with m hm β hβ hβ' using by cases abs_cases ( ( β : ℝ ) - 3 * α * ( Real.log ( Real.log m ) / Real.log m ) ) <;> cases abs_cases ( Real.log ( Real.log m ) / Real.log m ) <;> nlinarith [ show ( 0 : ℝ ) ≤ Real.log ( Real.log m ) / Real.log m from div_nonneg ( Real.log_nonneg <| show 1 ≤ Real.log m from by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( m :ℝ ) ≥ 3 by exact_mod_cast hm ] ) <| Real.log_nonneg <| show 1 ≤ ( m :ℝ ) from by norm_cast; linarith ] ;
  -- Since $\frac{\log \log m}{\log m} \to 0$ as $m \to \infty$, we have $(3\alpha - \epsilon) \frac{\log \log m}{\log m} \cdot m \to \infty$.
  have h_lim_inf : Filter.Tendsto (fun m : ℕ => (3 * α - ε) * (Real.log (Real.log m) / Real.log m) * (m : ℝ)) Filter.atTop Filter.atTop := by
    -- We'll use the fact that $\frac{\log \log m}{\log m} \cdot m = \frac{m}{\log m} \cdot \log \log m$.
    suffices h_lim_inf' : Filter.Tendsto (fun m : ℕ => (m : ℝ) / Real.log m * Real.log (Real.log m)) Filter.atTop Filter.atTop by
      convert h_lim_inf'.const_mul_atTop ( show 0 < ( 3 * α - ε : ℝ ) by linarith ) using 2 ; ring;
    -- We'll use the fact that $\frac{m}{\log m}$ grows faster than $\log \log m$.
    have h_lim_inf' : Filter.Tendsto (fun m : ℕ => (m : ℝ) / Real.log m) Filter.atTop Filter.atTop := by
      -- We can use the change of variables $u = \log m$ to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
        have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm using by rw [ Function.comp_apply, Function.comp_apply, Real.exp_log ( Nat.cast_pos.mpr hm ) ] );
      simpa using Real.tendsto_exp_div_pow_atTop 1;
    exact Filter.Tendsto.atTop_mul_atTop₀ h_lim_inf' ( Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop );
  filter_upwards [ h_beta_lower_bound, h_lim_inf.eventually_gt_atTop C ] with m hm₁ hm₂ using fun β hβ₁ hβ₂ => by nlinarith [ hm₁ β hβ₁ hβ₂, show ( 0 :ℝ ) ≤ m by positivity ] ;

/-
Reciprocal sum of 1/(12d) where each d > k is small relative to β.
-/
lemma recip_12d_sum_lt_half_beta
    (k : ℕ) (hk : 0 < k)
    (l₁ : ℕ) (e : ℕ → ℕ)
    (he_pos : ∀ i, i ≤ l₁ → 0 < e i)
    (he_growth : ∀ i, i ≤ l₁ → 3 * e i < 2 * e (i + 1))
    (l₂ : ℕ) (f : Fin l₂ → ℕ)
    (hf_gt_k : ∀ i, k < f i)
    (L_bound : ℕ) (hl₂ : l₂ ≤ L_bound)
    (β : ℚ) (hβ_pos : 0 < β)
    (hβ_recip : (↑L_bound + 4 : ℝ) ≤ (β : ℝ) * (↑k : ℝ))
    (D₁ : Finset ℕ) (D₂ : Finset ℕ)
    (hD₁_eq : D₁ = (Finset.range (l₁ + 1)).image (fun i => e i * (k + 1)))
    (hD₂_eq : D₂ = Finset.univ.image f) :
    (((D₁ ∪ D₂).sum (fun d => (1 : ℚ) / (12 * d)) : ℚ) : ℝ) < (β : ℝ) / 2 := by
  -- First, note that each term in the sum over $D₁$ is bounded by $\frac{1}{12(k+1)}$.
  have h_bound_D1 : (∑ d ∈ D₁, (1 / (12 * d) : ℚ)) ≤ (1 / 4 * (1 / (k + 1))) := by
    -- Since the sequence $e_i$ grows exponentially, the sum $\sum_{i=0}^{l₁} \frac{1}{12 e_i (k+1)}$ is bounded above by $\frac{1}{4(k+1)}$.
    have h_sum_bound : (∑ i ∈ Finset.range (l₁ + 1), (1 / (12 * (e i) * (k + 1) : ℚ))) ≤ (1 / 4 * (1 / (k + 1))) := by
      -- Since $e$ is strictly increasing, we have $e i ≥ (3/2)^i$.
      have h_exp_growth : ∀ i ≤ l₁, (e i : ℚ) ≥ (3 / 2 : ℚ) ^ i := by
        intro i hi; induction' i with i ih <;> norm_num [ pow_succ' ] at *;
        · linarith [ he_pos 0 bot_le ];
        · linarith [ ih ( Nat.le_of_lt hi ), show ( e ( i + 1 ) : ℚ ) ≥ ( 3 * e i + 1 ) / 2 by rw [ ge_iff_le ] ; rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ he_growth i hi.le ] ];
      -- Using the exponential growth bound, we can sum the series.
      have h_sum_bound : (∑ i ∈ Finset.range (l₁ + 1), (1 / (12 * (3 / 2 : ℚ) ^ i * (k + 1) : ℚ))) ≤ (1 / 4 * (1 / (k + 1))) := by
        -- The sum of the geometric series $\sum_{i=0}^{l₁} \frac{1}{(3/2)^i}$ is $\frac{1 - (2/3)^{l₁+1}}{1 - 2/3} = 3(1 - (2/3)^{l₁+1})$.
        have h_geo_sum : (∑ i ∈ Finset.range (l₁ + 1), (1 / (3 / 2 : ℚ) ^ i)) = 3 * (1 - (2 / 3 : ℚ) ^ (l₁ + 1)) := by
          ring_nf; norm_num [ geom_sum_eq ] ; ring;
        norm_num [ ← div_div, ← Finset.sum_div _ _ _ ] at *;
        norm_num [ div_eq_mul_inv, ← mul_assoc, ← Finset.mul_sum _ _ _, h_geo_sum ];
        exact mul_le_mul_of_nonneg_right ( mul_le_of_le_one_right ( by norm_num ) ( sub_le_self _ ( by positivity ) ) ) ( by positivity );
      exact le_trans ( Finset.sum_le_sum fun i hi => one_div_le_one_div_of_le ( by positivity ) <| mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( h_exp_growth i <| Finset.mem_range_succ_iff.mp hi ) <| by positivity ) <| by positivity ) h_sum_bound;
    simp_all +decide [mul_assoc];
    rw [ Finset.sum_image ] <;> norm_num [ mul_assoc, mul_comm, mul_left_comm ] at * ; aesop;
    -- Since $e$ is strictly increasing, if $e i * (k + 1) = e j * (k + 1)$, then $e i = e j$.
    have h_inj : StrictMonoOn e (Set.Iio (l₁ + 1)) := by
      intros i hi j hj hij
      generalize_proofs at *; (
      -- By induction on $j - i$, we can show that $e_i < e_j$ for any $i < j$.
      induction' hij with j hj ih
      generalize_proofs at *; (
      linarith [ he_growth i ( Nat.le_of_lt_succ hi ), he_pos i ( Nat.le_of_lt_succ hi ) ]);
      grind)
    generalize_proofs at *; (
    exact fun i hi j hj hij => h_inj.eq_iff_eq hi hj |>.1 <| by nlinarith;);
  -- Next, note that each term in the sum over $D₂$ is bounded by $\frac{1}{12(k+1)}$.
  have h_bound_D2 : (∑ d ∈ D₂, (1 / (12 * d) : ℚ)) ≤ (1 / 12 * (1 / (k + 1)) * L_bound) := by
    have h_bound_D2 : (∑ d ∈ D₂, (1 / (12 * d) : ℚ)) ≤ (1 / 12 * (1 / (k + 1)) * l₂) := by
      have h_bound_D2 : (∑ d ∈ D₂, (1 / (12 * d) : ℚ)) ≤ (∑ d ∈ D₂, (1 / (12 * (k + 1)) : ℚ)) := by
        gcongr ; norm_cast ; aesop;
      simp_all +decide [ mul_comm ];
      exact h_bound_D2.trans ( mul_le_mul_of_nonneg_right ( mod_cast le_trans ( Finset.card_image_le ) ( by norm_num ) ) ( by positivity ) );
    exact h_bound_D2.trans ( mul_le_mul_of_nonneg_left ( mod_cast hl₂ ) ( by positivity ) );
  -- Combine the bounds for $D₁$ and $D₂$.
  have h_combined : (∑ d ∈ D₁ ∪ D₂, (1 / (12 * d) : ℚ)) ≤ (1 / 4 * (1 / (k + 1))) + (1 / 12 * (1 / (k + 1)) * L_bound) := by
    refine le_trans ?_ ( add_le_add h_bound_D1 h_bound_D2 );
    rw [ ← Finset.sum_union_inter ] ; norm_num [ Finset.sum_nonneg ] ;
  -- Combine the bounds for $D₁$ and $D₂$ and simplify.
  have h_simplified : (1 / 4 * (1 / (k + 1)) : ℚ) + (1 / 12 * (1 / (k + 1)) * L_bound) < β / 2 := by
    field_simp;
    norm_cast at *;
    norm_num at * ; nlinarith [ ( by norm_cast : ( 1 : ℚ ) ≤ k ) ];
  rw [ lt_div_iff₀ ] at * <;> norm_cast at * ; linarith [ show 0 ≤ ∑ d ∈ D₁ ∪ D₂, 1 / ( 12 * d : ℕ ) from Finset.sum_nonneg fun _ _ => Nat.zero_le _ ] ;

/-
Denominator of β - Σ 1/(12d) is powersmooth.
-/
lemma beta_sub_recip_den_ps
    (m : ℕ)
    (D : Finset ℕ)
    (hD_ps : ∀ d ∈ D, IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) (12 * d))
    (β : ℚ)
    (hβ_ps : IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β.den)
    (β' : ℚ) (hβ'_def : β' = β - D.sum (fun d => (1 : ℚ) / (12 * d)))
    (hβ'_pos : 0 < β') :
    IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β'.den := by
  -- By induction on the number of terms in the sum, we can show that the denominator of β' is x-ps.
  have h_ind : ∀ S : Finset ℕ, (∀ d ∈ S, IsPowersmooth ((m : ℝ) ^ (1 / 5 : ℝ)) (12 * d)) → IsPowersmooth ((m : ℝ) ^ (1 / 5 : ℝ)) (β - ∑ d ∈ S, (1 / (12 * d) : ℚ)).den := by
    -- By induction on the number of terms in the sum, we can show that the denominator of β' is x-ps. We'll use the fact that the denominator of a difference of two rationals divides the lcm of their denominators.
    have h_ind_step : ∀ q r : ℚ, IsPowersmooth ((m : ℝ) ^ (1 / 5 : ℝ)) q.den → IsPowersmooth ((m : ℝ) ^ (1 / 5 : ℝ)) r.den → IsPowersmooth ((m : ℝ) ^ (1 / 5 : ℝ)) (q - r).den := by
      intros q r hq hr
      have h_denom : (q - r).den ∣ Nat.lcm q.den r.den := by
        -- The denominator of the difference of two rational numbers divides the least common multiple of their denominators.
        have h_denom_div_lcm : ∀ (a b : ℚ), (a - b).den ∣ Nat.lcm a.den b.den := by
          intros a b
          have h_denom_div_lcm : (a - b).den ∣ Nat.lcm a.den b.den := by
            have h_denom_div_lcm : (a - b).den ∣ Nat.lcm a.den b.den := by
              have h_denom_div_lcm : (a - b).den ∣ Nat.lcm a.den b.den := by
                have h_denom_div_lcm : (a - b).den ∣ Nat.lcm a.den b.den := by
                  exact Rat.sub_den_dvd_lcm a b
                exact h_denom_div_lcm
              exact h_denom_div_lcm
            exact h_denom_div_lcm
          exact h_denom_div_lcm;
        exact h_denom_div_lcm q r;
      have h_lcm_ps : IsPowersmooth ((m : ℝ) ^ (1 / 5 : ℝ)) (Nat.lcm q.den r.den) := by
        intro p k hp hk hdiv
        have hdiv_q : p ^ k ∣ q.den ∨ p ^ k ∣ r.den := by
          contrapose! hdiv; simp_all +decide [ Nat.Prime.pow_dvd_iff_le_factorization ] ;
          rw [ Nat.factorization_lcm ] <;> aesop;
        cases' hdiv_q with hq_div hr_div
        · exact hq p k hp hk hq_div
        · exact hr p k hp hk hr_div;
      exact IsPowersmooth_of_dvd h_lcm_ps h_denom;
    intro S hS; induction' S using Finset.induction with d S hd ih; aesop;
    rw [ Finset.sum_insert hd ];
    convert h_ind_step _ _ ( ih fun x hx => hS x ( Finset.mem_insert_of_mem hx ) ) ( show IsPowersmooth ( m ^ ( 1 / 5 : ℝ ) ) ( 1 / ( 12 * d ) |> Rat.den ) from ?_ ) using 1 ; ring_nf;
    norm_num [ Rat.mul_den ];
    split_ifs <;> simp_all +decide;
    · exact fun p k hp hk h => by have := Nat.le_of_dvd ( by positivity ) h; linarith [ Nat.Prime.one_lt hp, Nat.pow_le_pow_right hp.one_lt.le hk ] ;
    · simp_all +decide [ mul_comm, Int.sign_eq_one_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ‹_› ) ) ];
  aesop

/-
----------------------------------
PART 5: Existence of k ∈ C₁ with the required properties.
----------------------------------
-/

/-- For ε₁ < 1/12 and α > 0, eventually ((1-ε₁)me^α)^ε₁ ≤ m^(1/12). -/
lemma x_eps_le_m_12_main (α : ℚ) (ε₁ : ℝ) (hε₁_pos : 0 < ε₁)
    (hε₁_lt : ε₁ < 1/12) (hε₁_lt1 : ε₁ < 1) :
    ∀ᶠ (m : ℕ) in atTop,
      ((1 - ε₁) * (m : ℝ) * rexp (α : ℝ)) ^ ε₁ ≤ (m : ℝ) ^ ((1:ℝ)/12) := by
  suffices h_le : ∀ᶠ m : ℕ in Filter.atTop, (Real.exp (α : ℝ)) ^ ε₁ ≤ (m : ℝ) ^ (1 / 12 - ε₁) by
    filter_upwards [ h_le, Filter.eventually_gt_atTop 0 ] with m hm₁ hm₂
    refine le_trans ( Real.rpow_le_rpow ( by exact mul_nonneg ( mul_nonneg ( sub_nonneg.2 hε₁_lt1.le ) ( Nat.cast_nonneg _ ) ) ( Real.exp_nonneg _ ) ) ( show ( 1 - ε₁ ) * m * Real.exp α ≤ m * Real.exp α by exact mul_le_mul_of_nonneg_right ( mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( sub_le_self _ hε₁_pos.le ) ) ( Real.exp_nonneg _ ) ) ( by positivity ) ) ?_
    rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ]
    exact le_trans ( mul_le_mul_of_nonneg_left hm₁ <| by positivity ) ( by rw [ ← Real.rpow_add ( by positivity ) ] ; ring_nf; norm_num )
  exact (tendsto_rpow_atTop ( by linarith ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop).eventually_ge_atTop _

/-- Pigeonhole: if there are enough smooth integers in (x, (1+ε₁)x) and the
complement of C₁ in (x-1, me^α) is small, some smooth integer - 1 is in C₁. -/
lemma smooth_minus_one_in_C1_main
    (C₁ : Finset ℕ)
    (x meα : ℝ) (ε₁ : ℝ)
    (hx_hi : (1 + ε₁) * x ≤ meα)
    (S_count : ℕ)
    (hS_count : (S_count : ℝ) ≤ Set.ncard {N : ℕ | x < (N : ℝ) ∧ (N : ℝ) < (1 + ε₁) * x ∧
        (N : ℤ) ≡ 2 [ZMOD 210] ∧ IsPowersmooth (x ^ ε₁) N})
    (compl_bound : ℕ)
    (hCompl : Set.ncard {n : ℕ | x - 1 < (n : ℝ) ∧ (n : ℝ) < meα ∧ n ∉ C₁} ≤ compl_bound)
    (hPigeon : compl_bound < S_count) :
    ∃ M : ℕ, x < (M : ℝ) ∧ (M : ℝ) < (1 + ε₁) * x ∧
      (M : ℤ) ≡ 2 [ZMOD 210] ∧ IsPowersmooth (x ^ ε₁) M ∧ (M - 1) ∈ C₁ := by
  by_contra h_contra
  push_neg at h_contra
  have h_inj : (Set.image (fun M : ℕ => M - 1) {N : ℕ | x < N ∧ N < (1 + ε₁) * x ∧ (N : ℤ) ≡ 2 [ZMOD 210] ∧ IsPowersmooth (x ^ ε₁) N}).ncard ≤ compl_bound := by
    refine le_trans ?_ hCompl
    apply Set.ncard_le_ncard_of_injOn
    case f => exact fun n => n
    · rintro _ ⟨ M, ⟨ hM₁, hM₂, hM₃, hM₄ ⟩, rfl ⟩ ; exact ⟨ by cases M <;> norm_num at * ; linarith, by cases M <;> norm_num at * ; linarith, h_contra M hM₁ hM₂ hM₃ hM₄ ⟩
    · exact Set.injOn_id _
    · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊meα⌋₊, fun n hn => Nat.le_floor <| le_of_lt hn.2.1 ⟩
  rw [ Set.InjOn.ncard_image ] at h_inj
  · norm_cast at *; linarith
  · exact fun a ha b hb hab => by linarith [ Nat.sub_add_cancel ( show 1 ≤ a from Nat.pos_of_ne_zero fun ha' => by norm_num [ ha' ] at ha ), Nat.sub_add_cancel ( show 1 ≤ b from Nat.pos_of_ne_zero fun hb' => by norm_num [ hb' ] at hb ) ]

/-- For C₁ ⊂ (m, me^α) with β = α - Σ C₁⁻¹, the number of integers
in any sub-interval of (m, me^α) that are NOT in C₁ is bounded by
O(β · me^α + 1). -/
lemma C1_complement_sparse (m : ℕ) (hm : 2 ≤ m) (α : ℚ)
    (C₁ : Finset ℕ)
    (hC₁_range : ∀ a ∈ C₁, (m : ℝ) < (a : ℝ) ∧ (a : ℝ) < (m : ℝ) * Real.exp (α : ℝ))
    (β : ℚ) (hβ_def : β = α - C₁.sum (fun a => (1 : ℚ) / (a : ℚ)))
    (hβ_pos : 0 < β) (x : ℝ) (hx_lo : (m : ℝ) ≤ x)
    (hx_hi : x < (m : ℝ) * Real.exp (α : ℝ)) :
    (Set.ncard {n : ℕ | x < (n : ℝ) ∧ (n : ℝ) < (m : ℝ) * Real.exp (α : ℝ) ∧ n ∉ C₁} : ℝ)
      ≤ (β : ℝ) * ((m : ℝ) * Real.exp (α : ℝ)) + 1 := by
  have h_sum_complement : (∑ n ∈ Finset.filter (fun n : ℕ => x < n ∧ (n : ℝ) < m * Real.exp α ∧ n∉ C₁) (Finset.Ico m (Nat.floor (m * Real.exp α) + 1)), (1 / (n : ℝ))) ≤ β := by
    have h_sum_complement_le : (∑ n ∈ Finset.filter (fun n : ℕ => x < n ∧ (n : ℝ) < m * Real.exp α ∧ n∉ C₁) (Finset.Ico m (Nat.floor (m * Real.exp α) + 1)), (1 / (n : ℝ))) ≤ (∑ n ∈ Finset.Ico (m + 1) (Nat.floor (m * Real.exp α) + 1), (1 / (n : ℝ))) - (∑ a ∈ C₁, (1 / (a : ℝ))) := by
      have h_sum_complement_le : (∑ n ∈ Finset.filter (fun n : ℕ => x < n ∧ (n : ℝ) < m * Real.exp α ∧ n∉ C₁) (Finset.Ico m (Nat.floor (m * Real.exp α) + 1)), (1 / (n : ℝ))) ≤ (∑ n ∈ (Finset.Ico (m + 1) (Nat.floor (m * Real.exp α) + 1)) \ C₁, (1 / (n : ℝ))) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        grind
      convert h_sum_complement_le using 1 ; rw [ ← Finset.sum_sdiff <| show C₁ ⊆ Finset.Ico ( m + 1 ) ( ⌊ ( m : ℝ ) * Real.exp α⌋₊ + 1 ) from fun a ha => Finset.mem_Ico.mpr ⟨ Nat.succ_le_of_lt <| mod_cast hC₁_range a ha |>.1, Nat.lt_succ_of_le <| Nat.le_floor <| mod_cast hC₁_range a ha |>.2.le ⟩ ] ; aesop
    have h_sum_I₁_le_alpha : (∑ n ∈ Finset.Ico (m + 1) (Nat.floor (m * Real.exp α) + 1), (1 / (n : ℝ))) ≤ α := by
      have h_integral_bound : (∑ n ∈ Finset.Ico (m + 1) (Nat.floor (m * Real.exp α) + 1), (1 / (n : ℝ))) ≤ Real.log (Nat.floor (m * Real.exp α)) - Real.log m := by
        have h_integral_bound : ∀ N : ℕ, m < N → (∑ n ∈ Finset.Ico (m + 1) (N + 1), (1 / (n : ℝ))) ≤ Real.log (N : ℝ) - Real.log (m : ℝ) := by
          intros N hN
          have h_integral_bound : ∀ n ∈ Finset.Ico (m + 1) (N + 1), (1 / (n : ℝ)) ≤ Real.log n - Real.log (n - 1) := by
            intros n hn
            have h_integral_bound : ∫ x in (n - 1 : ℝ)..n, (1 / x) ≥ (1 / (n : ℝ)) := by
              refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ fun x hx => one_div_le_one_div_of_le _ <| hx.2 ) <;> norm_num
              · apply_rules [ ContinuousOn.intervalIntegrable ]
                exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const continuousAt_id <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Ico.mp hn ] ]
              · linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Ico.mp hn ] ]
            rcases n with ( _ | _ | n ) <;> norm_num at *
            · linarith
            · rw [ integral_inv_of_pos, Real.log_div ] at h_integral_bound <;> norm_num at * <;> linarith
          convert Finset.sum_le_sum h_integral_bound using 1 ; erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm ] ; ring_nf; (
          rw [ show ( 1 + N - ( 1 + m ) ) = N - m by rw [ Nat.add_sub_add_left ] ] ; have := Finset.sum_range_sub ( fun x => Real.log ( m + x ) ) ( N - m ) ; simp_all +decide [add_comm,
            add_left_comm]
          rw [ Nat.cast_sub hN.le, add_sub_cancel ])
        by_cases hN : m < Nat.floor (m * Real.exp α)
        · exact h_integral_bound _ hN
        · norm_num [ show ⌊ ( m : ℝ ) * Real.exp α⌋₊ = m by exact le_antisymm ( Nat.le_of_not_lt hN ) ( Nat.le_floor <| by nlinarith [ Real.add_one_le_exp α, ( by norm_cast : ( 2 :ℝ ) ≤ m ) ] ) ] at *
      refine le_trans h_integral_bound ?_
      rw [ ← Real.log_div ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.floor_pos.mpr <| by nlinarith [ Real.add_one_le_exp α, show ( m : ℝ ) ≥ 2 by norm_cast ] ) ( Nat.cast_ne_zero.mpr <| by positivity ) ] ; exact Real.log_le_iff_le_exp ( div_pos ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by nlinarith [ Real.add_one_le_exp α, show ( m : ℝ ) ≥ 2 by norm_cast ] ) <| Nat.cast_pos.mpr <| by positivity ) |>.2 <| by rw [ div_le_iff₀ <| Nat.cast_pos.mpr <| by positivity ] ; nlinarith [ Nat.floor_le <| show 0 ≤ ( m : ℝ ) * Real.exp α by positivity, Real.add_one_le_exp α ]
    exact h_sum_complement_le.trans ( by push_cast [ hβ_def ] ; linarith )
  have h_card_le_beta : (∑ n ∈ Finset.filter (fun n : ℕ => x < n ∧ (n : ℝ) < m * Real.exp α ∧ n∉ C₁) (Finset.Ico m (Nat.floor (m * Real.exp α) + 1)), (1 / (n : ℝ))) ≥ (∑ n ∈ Finset.filter (fun n : ℕ => x < n ∧ (n : ℝ) < m * Real.exp α ∧ n∉ C₁) (Finset.Ico m (Nat.floor (m * Real.exp α) + 1)), (1 / (m * Real.exp α : ℝ))) := by
    gcongr
    · exact Nat.cast_pos.mpr ( by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp ‹_› |>.1 ) ] )
    · exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ico.mp ( Finset.mem_filter.mp ‹_› |>.1 ) |>.2 |> Nat.lt_succ_iff.mp ) <| Nat.floor_le <| by positivity
  have h_eq_sets : {n : ℕ | x < n ∧ (n : ℝ) < m * Real.exp α ∧ n∉ C₁} = Finset.filter (fun n : ℕ => x < n ∧ (n : ℝ) < m * Real.exp α ∧ n∉ C₁) (Finset.Ico m (Nat.floor (m * Real.exp α) + 1)) := by
    ext; simp [Finset.mem_Ico]
    exact fun h₁ h₂ h₃ => ⟨ Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith }, Nat.le_floor <| by linarith ⟩
  simp_all +decide
  rw [ ← Set.ncard_coe_finset ] at * ; norm_num at *
  rw [ ← div_eq_inv_mul ] at *
  rw [ mul_div, div_le_iff₀ ] at h_card_le_beta <;> nlinarith [ show ( m : ℝ ) ≥ 2 by norm_cast, Real.exp_pos α, mul_inv_cancel₀ ( by positivity : ( m : ℝ ) ≠ 0 ), mul_pos ( by positivity : 0 < ( m : ℝ ) ) ( Real.exp_pos α ) ]

/-
For large m, there exists k ∈ C₁ with k > (1-ε₀)me^α, k coprime to 210, and k+1 is m^(1/12)-powersmooth.
-/
lemma k_exists_in_C1
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N}))
    (α : ℚ) (hα : 0 < α) (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀_lt : ε₀ < 1/3) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ᶠ (m : ℕ) in atTop,
    ∀ (C₁ : Finset ℕ) (β : ℚ),
    (∀ a ∈ C₁, (m : ℝ) < (a : ℝ) ∧ (a : ℝ) < (m : ℝ) * Real.exp (α : ℝ)) →
    β = α - C₁.sum (fun a => (1 : ℚ) / (a : ℚ)) →
    0 < β →
    (β : ℝ) < δ →
    ∃ k : ℕ, k ∈ C₁ ∧
      0 < k ∧
      Nat.Coprime k 210 ∧
      IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 12)) (k + 1) ∧
      (1 - ε₀) * (m : ℝ) * Real.exp (α : ℝ) < (k : ℝ) := by
  set eα := rexp (↑α : ℝ) with heα_def
  have heα_pos : 0 < eα := exp_pos _
  have heα_gt1 : 1 < eα := Real.one_lt_exp_iff.mpr (by exact_mod_cast hα)
  set ε₁ := min (ε₀ / 4) ((eα - 1) / (2 * eα)) with hε₁_def
  have hε₁_pos : 0 < ε₁ := by
    apply lt_min <;> [positivity; exact div_pos (by linarith) (by positivity)]
  have hε₁_le_ε₀_4 : ε₁ ≤ ε₀ / 4 := min_le_left _ _
  have hε₁_lt_12 : ε₁ < 1 / 12 := lt_of_le_of_lt hε₁_le_ε₀_4 (by linarith)
  have hε₁_lt1 : ε₁ < 1 := by linarith
  have h1_sub_ε₁_pos : 0 < 1 - ε₁ := by linarith
  have h_interval_ok : 1 < (1 - ε₁) * eα := by
    have h1 : ε₁ ≤ (eα - 1) / (2 * eα) := min_le_right _ _
    have h2 : (1 - ε₁) * eα ≥ (1 - (eα - 1) / (2 * eα)) * eα := by nlinarith
    have h3 : (1 - (eα - 1) / (2 * eα)) * eα = (eα + 1) / 2 := by field_simp; ring
    linarith
  obtain ⟨x₀, δ_sm, hδ_sm_pos, hδ_sm⟩ :=
    smoothinarith smooth_arith 2 210 (by norm_num) ε₁ hε₁_pos
  refine ⟨δ_sm * (1 - ε₁) / 2, by positivity, ?_⟩
  have ev1 : ∀ᶠ (m : ℕ) in atTop, x₀ ≤ (1 - ε₁) * (m : ℝ) * eα := by
    filter_upwards [Filter.eventually_ge_atTop ⌈x₀ / ((1 - ε₁) * eα) + 1⌉₊] with m hm
    have h_prod_pos : 0 < (1 - ε₁) * eα := by positivity
    have hceil : x₀ / ((1 - ε₁) * eα) + 1 ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
    have hq : x₀ / ((1 - ε₁) * eα) ≤ (m : ℝ) := by linarith
    rw [div_le_iff₀ h_prod_pos] at hq
    linarith [mul_comm (↑m : ℝ) ((1 - ε₁) * eα)]
  have ev2 := x_eps_le_m_12_main α ε₁ hε₁_pos hε₁_lt_12 hε₁_lt1
  have ev3 : ∀ᶠ (m : ℕ) in atTop,
      (1 - ε₀) * (m : ℝ) * eα + 1 < (1 - ε₁) * (m : ℝ) * eα := by
    have h_diff : 0 < ε₀ - ε₁ := by linarith [hε₁_le_ε₀_4]
    filter_upwards [Filter.eventually_ge_atTop ⌈ 2 / ((ε₀ - ε₁) * eα) + 1⌉₊] with m hm
    have : 2 / ((ε₀ - ε₁) * eα) + 1 ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
    have : 2 / ((ε₀ - ε₁) * eα) < (m : ℝ) := by linarith
    rw [div_lt_iff₀ (by positivity : 0 < (ε₀ - ε₁) * eα)] at this
    nlinarith
  have ev4 : ∀ᶠ (m : ℕ) in atTop,
      (m : ℝ) + 1 < (1 - ε₁) * (m : ℝ) * eα := by
    filter_upwards [Filter.eventually_ge_atTop ⌈ 2 / ((1 - ε₁) * eα - 1) + 1⌉₊] with m hm
    have h_pos : 0 < (1 - ε₁) * eα - 1 := by linarith [h_interval_ok]
    have : 2 / ((1 - ε₁) * eα - 1) + 1 ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
    have : 2 / ((1 - ε₁) * eα - 1) < (m : ℝ) := by linarith
    rw [div_lt_iff₀ h_pos] at this
    nlinarith
  have ev5 : ∀ᶠ (m : ℕ) in atTop,
      1 < δ_sm * (1 - ε₁) / 2 * ((m : ℝ) * eα) := by
    filter_upwards [Filter.eventually_ge_atTop ⌈ 4 / (δ_sm * (1 - ε₁) * eα) + 1⌉₊] with m hm
    have : 4 / (δ_sm * (1 - ε₁) * eα) + 1 ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
    have : 4 / (δ_sm * (1 - ε₁) * eα) < (m : ℝ) := by linarith
    rw [div_lt_iff₀ (by positivity : 0 < δ_sm * (1 - ε₁) * eα)] at this
    nlinarith
  filter_upwards [ev1, ev2, ev3, ev4, ev5, Filter.eventually_ge_atTop 2] with m hx_ge hps_mono hgap hx_m_gap h_meα_large hm2
  intro C₁ β hC₁_range hβ_def hβ_pos hβ_lt
  set x := (1 - ε₁) * (m : ℝ) * eα with hx_def
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast show 0 < m by omega
  have hx_pos : 0 < x := by rw [hx_def]; positivity
  have hx_lo : (m : ℝ) ≤ x := by
    rw [hx_def]; have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg' m; nlinarith
  have hx_hi : (1 + ε₁) * x ≤ (m : ℝ) * eα := by
    rw [hx_def]; nlinarith [sq_nonneg ε₁]
  have hx_strict : x < (m : ℝ) * eα := by nlinarith
  have hδ_applied := hδ_sm x hx_ge
  have hx_m1_lo : (m : ℝ) ≤ x - 1 := by linarith [hx_m_gap]
  have hx_m1_hi : x - 1 < (m : ℝ) * eα := by linarith
  have hCompl := C1_complement_sparse m hm2 α C₁ hC₁_range β hβ_def hβ_pos (x - 1) hx_m1_lo hx_m1_hi
  have hβδ_ineq : (β : ℝ) * ((m : ℝ) * eα) + 1 < δ_sm * x := by
    rw [hx_def]; nlinarith
  have hCompl_nat : Set.ncard {n : ℕ | x - 1 < (n : ℝ) ∧ (n : ℝ) < (m : ℝ) * eα ∧ n ∉ C₁}
      < Set.ncard {N : ℕ | x < (N : ℝ) ∧ (N : ℝ) < (1 + ε₁) * x ∧
        (N : ℤ) ≡ 2 [ZMOD 210] ∧ IsPowersmooth (x ^ ε₁) N} := by
    have hc1 : (Set.ncard {n : ℕ | x - 1 < (n : ℝ) ∧ (n : ℝ) < ↑m * eα ∧ n ∉ C₁} : ℝ) < δ_sm * x := by
      calc (Set.ncard {n : ℕ | x - 1 < (n : ℝ) ∧ (n : ℝ) < ↑m * eα ∧ n ∉ C₁} : ℝ)
          ≤ (β : ℝ) * ((m : ℝ) * rexp (α : ℝ)) + 1 := hCompl
        _ = (β : ℝ) * ((m : ℝ) * eα) + 1 := by rfl
        _ < δ_sm * x := hβδ_ineq
    have hc2 : δ_sm * x ≤ (Set.ncard {N : ℕ | x < (N : ℝ) ∧ (N : ℝ) < (1 + ε₁) * x ∧
        (N : ℤ) ≡ 2 [ZMOD 210] ∧ IsPowersmooth (x ^ ε₁) N} : ℝ) := hδ_applied
    exact_mod_cast show (Set.ncard {n : ℕ | x - 1 < (n : ℝ) ∧ (n : ℝ) < ↑m * eα ∧ n ∉ C₁} : ℝ) <
      (Set.ncard {N : ℕ | x < (N : ℝ) ∧ (N : ℝ) < (1 + ε₁) * x ∧
        (N : ℤ) ≡ 2 [ZMOD 210] ∧ IsPowersmooth (x ^ ε₁) N} : ℝ) by linarith
  obtain ⟨M, hM_lo, hM_hi, hM_mod, hM_ps, hM_in_C1⟩ :=
    smooth_minus_one_in_C1_main C₁ x ((m : ℝ) * eα) ε₁ hx_hi
      (Set.ncard {N : ℕ | x < (N : ℝ) ∧ (N : ℝ) < (1 + ε₁) * x ∧
        (N : ℤ) ≡ 2 [ZMOD 210] ∧ IsPowersmooth (x ^ ε₁) N})
      (by linarith)
      (Set.ncard {n : ℕ | x - 1 < (n : ℝ) ∧ (n : ℝ) < (m : ℝ) * eα ∧ n ∉ C₁})
      le_rfl
      hCompl_nat
  have hM_ge2 : 2 ≤ M := by
    have : 1 < (M : ℝ) := by linarith [hx_lo, show (2 : ℝ) ≤ (m : ℝ) by exact_mod_cast hm2]
    exact_mod_cast this
  refine ⟨M - 1, hM_in_C1, by omega, coprime_210_of_mod_eq_2 M hM_mod, ?_, ?_⟩
  · rw [show M - 1 + 1 = M from by omega]
    exact IsPowersmooth_mono hps_mono hM_ps
  · have : (↑(M - 1) : ℝ) = (↑M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ M)]; norm_num
    rw [this]; linarith

/-
----------------------------------
PART 6: Definition and properties of the e_i sequence.
----------------------------------
-/

open Classical in
/-- The set of IsPowersmooth x integers ≤ n is nonempty (contains 1) when x ≥ 1. -/
lemma ps_le_nonempty {x : ℝ} (hx : 1 ≤ x) (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.Icc 1 n).filter (IsPowersmooth x)).Nonempty :=
  ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl _, hn⟩, IsPowersmooth_one hx⟩⟩

open Classical in
/-- The largest IsPowersmooth x integer in [1, n]. -/
noncomputable def largest_ps_le (x : ℝ) (n : ℕ) : ℕ :=
  if h : 1 ≤ n ∧ 1 ≤ x then
    ((Finset.Icc 1 n).filter (IsPowersmooth x)).max' (ps_le_nonempty h.2 n h.1)
  else 1

open Classical in
lemma largest_ps_le_mem {x : ℝ} {n : ℕ} (hx : 1 ≤ x) (hn : 1 ≤ n) :
    largest_ps_le x n ∈ (Finset.Icc 1 n).filter (IsPowersmooth x) := by
  show (if h : 1 ≤ n ∧ 1 ≤ x then _ else 1) ∈ _
  rw [dif_pos ⟨hn, hx⟩]; exact Finset.max'_mem _ _

open Classical in
lemma largest_ps_le_le {x : ℝ} {n : ℕ} (hx : 1 ≤ x) (hn : 1 ≤ n) :
    largest_ps_le x n ≤ n :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp (largest_ps_le_mem hx hn)).1).2

open Classical in
lemma largest_ps_le_is_ps {x : ℝ} {n : ℕ} (hx : 1 ≤ x) (hn : 1 ≤ n) :
    IsPowersmooth x (largest_ps_le x n) :=
  (Finset.mem_filter.mp (largest_ps_le_mem hx hn)).2

open Classical in
lemma largest_ps_le_is_max {x : ℝ} {n : ℕ} (hx : 1 ≤ x) (hn : 1 ≤ n)
    (a : ℕ) (ha : 1 ≤ a) (ha_le : a ≤ n) (ha_ps : IsPowersmooth x a) :
    a ≤ largest_ps_le x n := by
  show a ≤ (if h : 1 ≤ n ∧ 1 ≤ x then _ else 1)
  rw [dif_pos ⟨hn, hx⟩]
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha, ha_le⟩, ha_ps⟩)

/-- The e_i sequence: e_0 = 1, e_{i+1} = largest m^{1/12}-powersmooth integer ≤ 2·e_i. -/
noncomputable def e_seq (x : ℝ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => largest_ps_le x (2 * e_seq x i)

lemma e_seq_zero (x : ℝ) : e_seq x 0 = 1 := rfl

lemma e_seq_succ (x : ℝ) (i : ℕ) : e_seq x (i + 1) = largest_ps_le x (2 * e_seq x i) := rfl

open Classical in
lemma e_seq_pos (x : ℝ) (hx : 1 ≤ x) (i : ℕ) : 0 < e_seq x i := by
  induction i with
  | zero => simp [e_seq]
  | succ i ih =>
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp (largest_ps_le_mem hx (by linarith))).1).1

lemma e_seq_le_double (x : ℝ) (hx : 1 ≤ x) (i : ℕ) :
    e_seq x (i + 1) ≤ 2 * e_seq x i :=
  largest_ps_le_le hx (by linarith [e_seq_pos x hx i])

lemma e_seq_ps (x : ℝ) (hx : 1 ≤ x) (i : ℕ) : IsPowersmooth x (e_seq x i) := by
  induction i with
  | zero => exact IsPowersmooth_one hx
  | succ i _ => exact largest_ps_le_is_ps hx (by linarith [e_seq_pos x hx i])

lemma e_seq_mono (x : ℝ) (hx : 1 ≤ x) : Monotone (e_seq x) := by
  apply monotone_nat_of_le_succ; intro i
  show e_seq x i ≤ largest_ps_le x (2 * e_seq x i)
  exact largest_ps_le_is_max hx (by linarith [e_seq_pos x hx i])
    (e_seq x i) (by linarith [e_seq_pos x hx i]) (by omega) (e_seq_ps x hx i)

/-- If there exists an IsPowersmooth x integer in (3/2 · n, 2n],
    then largest_ps_le x (2n) > 3/2 · n. -/
lemma largest_ps_le_growth {x : ℝ} {n : ℕ} (hx : 1 ≤ x) (hn : 1 ≤ n)
    (N : ℕ) (hN_lo : 3 * n < 2 * N) (hN_hi : N ≤ 2 * n)
    (hN_ps : IsPowersmooth x N) :
    3 * n < 2 * largest_ps_le x (2 * n) := by
  have hN_pos : 1 ≤ N := by omega
  have h2n_pos : 1 ≤ 2 * n := by omega
  have hN_le := largest_ps_le_is_max hx h2n_pos N hN_pos hN_hi hN_ps
  omega

/-- For sufficiently large e_i we get e_{i+1} > 3/2 · e_i. -/
lemma e_seq_growth_from_witness (x : ℝ) (hx : 1 ≤ x) (i : ℕ)
    (N : ℕ) (hN_lo : 3 * e_seq x i < 2 * N) (hN_hi : N ≤ 2 * e_seq x i)
    (hN_ps : IsPowersmooth x N) :
    3 * e_seq x i < 2 * e_seq x (i + 1) := by
  rw [e_seq_succ]
  exact largest_ps_le_growth hx (e_seq_pos x hx i) N hN_lo hN_hi hN_ps

/-- For any target value T with T ≥ 2, the e_seq eventually reaches
    the interval [T/2, T). This gives us l₁. -/
lemma e_seq_reaches_interval (x : ℝ) (hx : 1 ≤ x) (T : ℕ) (hT : 2 ≤ T)
    (h_unbounded : ∃ j, T ≤ e_seq x j) :
    ∃ l₁ : ℕ, T / 2 ≤ e_seq x l₁ ∧ e_seq x l₁ < T := by
  have h_pos : ∀ i, 1 ≤ e_seq x i := fun i => e_seq_pos x hx i
  obtain ⟨j₀, hj₀_ge, hj₀_min⟩ : ∃ j₀, T / 2 ≤ e_seq x j₀ ∧ ∀ i < j₀, e_seq x i < T / 2 := by
    have : ∃ j₀, T / 2 ≤ e_seq x j₀ := ⟨_, le_trans (Nat.div_le_self T 2) (h_unbounded.choose_spec)⟩
    exact ⟨Nat.find this, Nat.find_spec this, fun i hi => not_le.mp (Nat.find_min this hi)⟩
  refine ⟨j₀, hj₀_ge, ?_⟩
  by_cases hj₀_zero : j₀ = 0
  · subst hj₀_zero; simp [e_seq] at hj₀_ge ⊢; omega
  · obtain ⟨j₀', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj₀_zero
    have h_prev : e_seq x j₀' < T / 2 := hj₀_min j₀' (by omega)
    have h_step : e_seq x (j₀' + 1) ≤ 2 * e_seq x j₀' := e_seq_le_double x hx j₀'
    linarith [Nat.mul_div_le T 2]

lemma rpow_eps_le_rpow_twelfth (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀_lt : ε₀ < 1/3) :
    ∀ᶠ (m : ℕ) in atTop,
    ∀ (a : ℝ), 0 < a → a ≤ 2 * (m : ℝ) ^ 2 →
    a ^ (ε₀ / 12) ≤ (m : ℝ) ^ ((1 : ℝ) / 12) := by
  rw [Filter.eventually_atTop]
  refine ⟨2, fun m hm => ?_⟩
  intro a ha ha_le
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm_ge_2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2m2_ge_1 : (1 : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by nlinarith
  have hε_le : ε₀ / 12 ≤ 1 / 36 := by linarith
  have h1 : a ^ (ε₀ / 12) ≤ (2 * (m : ℝ) ^ 2) ^ (ε₀ / 12) :=
    Real.rpow_le_rpow (le_of_lt ha) ha_le (by positivity)
  have h2 : (2 * (m : ℝ) ^ 2) ^ (ε₀ / 12) ≤ (2 * (m : ℝ) ^ 2) ^ ((1 : ℝ) / 36) :=
    Real.rpow_le_rpow_of_exponent_le h2m2_ge_1 hε_le
  have h3 : (2 * (m : ℝ) ^ 2) ^ ((1 : ℝ) / 36) = 2 ^ ((1 : ℝ) / 36) * ((m : ℝ) ^ 2) ^ ((1 : ℝ) / 36) :=
    Real.mul_rpow (by positivity) (by positivity)
  have h4 : ((m : ℝ) ^ 2) ^ ((1 : ℝ) / 36) = (m : ℝ) ^ ((1 : ℝ) / 18) := by
    rw [← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ m)]
    norm_num
  have h5 : (2 : ℝ) ^ ((1 : ℝ) / 36) ≤ (m : ℝ) ^ ((1 : ℝ) / 36) :=
    Real.rpow_le_rpow (by positivity) hm_ge_2 (by norm_num)
  have h6 : (m : ℝ) ^ ((1 : ℝ) / 36) * (m : ℝ) ^ ((1 : ℝ) / 18) = (m : ℝ) ^ ((1 : ℝ) / 12) := by
    rw [← Real.rpow_add hm_pos]
    norm_num
  have hm18_pos : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 18) := Real.rpow_nonneg (by positivity) _
  calc a ^ (ε₀ / 12) ≤ (2 * (m : ℝ) ^ 2) ^ ((1 : ℝ) / 36) := le_trans h1 h2
    _ = 2 ^ ((1 : ℝ) / 36) * (m : ℝ) ^ ((1 : ℝ) / 18) := by rw [h3, h4]
    _ ≤ (m : ℝ) ^ ((1 : ℝ) / 36) * (m : ℝ) ^ ((1 : ℝ) / 18) :=
        mul_le_mul_of_nonneg_right h5 hm18_pos
    _ = (m : ℝ) ^ ((1 : ℝ) / 12) := h6

lemma e_seq_growth_eventually
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N})) :
    ∀ᶠ (m : ℕ) in atTop, ∀ i : ℕ,
      (m : ℝ) ^ ((1 : ℝ) / 12) ≤ (e_seq ((m : ℝ) ^ ((1 : ℝ) / 12)) i : ℝ) →
      (e_seq ((m : ℝ) ^ ((1 : ℝ) / 12)) i : ℝ) ≤ (m : ℝ) ^ 2 →
      3 * e_seq ((m : ℝ) ^ ((1 : ℝ) / 12)) i < 2 * e_seq ((m : ℝ) ^ ((1 : ℝ) / 12)) (i + 1) := by
  set ε := (1 : ℝ) / 48 with hε_def
  have hε_pos : (0 : ℝ) < ε := by norm_num
  obtain ⟨x₀, δ, hδ_pos, hδ⟩ := smoothinarith smooth_arith 1 210 (by norm_num) ε hε_pos
  have h_rpow := rpow_eps_le_rpow_twelfth (1/4) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / 4 / 12 = ε from by rw [hε_def]; ring] at h_rpow
  rw [Filter.eventually_atTop] at h_rpow ⊢
  obtain ⟨m₀_rpow, hm_rpow⟩ := h_rpow
  refine ⟨max (max (⌈x₀⌉₊ ^ 12) 2) m₀_rpow, fun m hm => ?_⟩
  have hm_ge_2 : 2 ≤ m := by omega
  have hm_ge_ceil12 : ⌈x₀⌉₊ ^ 12 ≤ m := by omega
  have hm_ge_rpow : m₀_rpow ≤ m := by omega
  have h_rpow_m := hm_rpow m hm_ge_rpow
  set x := (m : ℝ) ^ ((1 : ℝ) / 12) with hx_def
  have hx_ge_1 : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  have hx_ge_ceil : (⌈x₀⌉₊ : ℝ) ≤ x := by
    rw [hx_def]
    have h12 : (⌈x₀⌉₊ : ℝ) ^ 12 ≤ (m : ℝ) := by exact_mod_cast hm_ge_ceil12
    have h_rpow12 : ((⌈x₀⌉₊ : ℝ) ^ 12) ^ ((1 : ℝ) / 12) ≤ (m : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.rpow_le_rpow (by positivity) h12 (by norm_num)
    have : (⌈x₀⌉₊ : ℝ) ^ ((12 : ℕ) : ℝ) = (⌈x₀⌉₊ : ℝ) ^ 12 := Real.rpow_natCast _ _
    rw [← this, ← Real.rpow_mul (Nat.cast_nonneg _)] at h_rpow12
    have : ((12 : ℕ) : ℝ) * ((1 : ℝ) / 12) = 1 := by push_cast; ring
    rw [this, Real.rpow_one] at h_rpow12
    exact h_rpow12
  intro i hei_ge hei_le
  have hei_pos : 0 < e_seq x i := e_seq_pos x hx_ge_1 i
  have hx_arg_pos : (0 : ℝ) < (3 : ℝ) / 2 * (e_seq x i : ℝ) := by positivity
  have hx_arg_ge_x0 : x₀ ≤ (3 : ℝ) / 2 * (e_seq x i : ℝ) := by
    calc x₀ ≤ (⌈x₀⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ x := hx_ge_ceil
      _ ≤ (e_seq x i : ℝ) := hei_ge
      _ ≤ (3 : ℝ) / 2 * (e_seq x i : ℝ) := by linarith [show (0 : ℝ) < e_seq x i from by exact_mod_cast hei_pos]
  have h_density := hδ ((3 : ℝ) / 2 * (e_seq x i : ℝ)) hx_arg_ge_x0
  have hS_nonempty : {N : ℕ | (3 : ℝ) / 2 * (e_seq x i : ℝ) < (N : ℝ) ∧
    (N : ℝ) < (1 + ε) * ((3 : ℝ) / 2 * (e_seq x i : ℝ)) ∧
    (N : ℤ) ≡ 1 [ZMOD (210 : ℤ)] ∧ IsPowersmooth (((3 : ℝ) / 2 * (e_seq x i : ℝ)) ^ ε) N}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero; intro h0
    have : (Set.ncard {N : ℕ | (3 : ℝ) / 2 * (e_seq x i : ℝ) < (N : ℝ) ∧
      (N : ℝ) < (1 + ε) * ((3 : ℝ) / 2 * (e_seq x i : ℝ)) ∧
      (N : ℤ) ≡ 1 [ZMOD (210 : ℤ)] ∧ IsPowersmooth (((3 : ℝ) / 2 * (e_seq x i : ℝ)) ^ ε) N} : ℝ) = 0 := by
      convert Nat.cast_zero
    linarith [mul_pos hδ_pos hx_arg_pos]
  obtain ⟨N, hN_lo, hN_hi, _, hN_ps⟩ := hS_nonempty
  apply e_seq_growth_from_witness x hx_ge_1 i N
  · exact_mod_cast show (3 : ℝ) * (e_seq x i : ℝ) < 2 * (N : ℝ) by linarith
  · have : (N : ℝ) < (1 + ε) * (3 / 2 * (e_seq x i : ℝ)) := hN_hi
    have : (1 + ε) * (3 / 2) < 2 := by rw [hε_def]; norm_num
    have : (N : ℝ) < 2 * (e_seq x i : ℝ) := by nlinarith
    exact_mod_cast show (N : ℝ) ≤ 2 * (e_seq x i : ℝ) by linarith
  · apply IsPowersmooth_mono _ hN_ps
    rw [hx_def]
    apply h_rpow_m
    · exact hx_arg_pos
    · calc (3 : ℝ) / 2 * (e_seq x i : ℝ) ≤ 2 * (e_seq x i : ℝ) := by linarith [show (0 : ℝ) < e_seq x i from by exact_mod_cast hei_pos]
        _ ≤ 2 * (m : ℝ) ^ 2 := by nlinarith

lemma e_seq_reaches_nat (x : ℝ) (hx : 1 ≤ x) (n : ℕ) (hn : 1 ≤ n) (hn_le : (n : ℝ) ≤ x) :
    ∃ j, n ≤ e_seq x j := by
  induction n with
  | zero => exact ⟨0, by omega⟩
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0; exact ⟨0, by simp [e_seq]⟩
    · have hn_pos : 1 ≤ n := by omega
      have hn_le_x : (n : ℝ) ≤ x := by
        exact le_trans (by exact_mod_cast (show (n : ℝ) ≤ n + 1 by linarith)) hn_le
      obtain ⟨j, hj⟩ := ih hn_pos hn_le_x
      refine ⟨j + 1, ?_⟩
      show n + 1 ≤ largest_ps_le x (2 * e_seq x j)
      have h2ej_pos : 1 ≤ 2 * e_seq x j := by
        have := e_seq_pos x hx j; omega
      have h_n1_le : n + 1 ≤ 2 * e_seq x j := by omega
      have h_n1_ps : IsPowersmooth x (n + 1) := by
        intro p k hp hk hpk
        have : p ^ k ≤ n + 1 := Nat.le_of_dvd (by omega) hpk
        exact le_trans (by exact_mod_cast this) hn_le
      exact largest_ps_le_is_max hx h2ej_pos (n + 1) (by omega) h_n1_le h_n1_ps

lemma e_seq_exceeds_x
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N})) :
    ∀ᶠ (m : ℕ) in atTop,
      ∃ j₀, (m : ℝ) ^ ((1 : ℝ) / 12) ≤ (e_seq ((m : ℝ) ^ ((1 : ℝ) / 12)) j₀ : ℝ) := by
  obtain ⟨x₀_boot, δ_boot, hδ_boot_pos, hsmooth_boot⟩ :=
    smoothinarith smooth_arith 1 1 one_pos 1 one_pos
  rw [Filter.eventually_atTop]
  refine ⟨(⌈x₀_boot⌉₊ + 1) ^ 12, fun m hm => ?_⟩
  set x := (m : ℝ) ^ ((1 : ℝ) / 12) with hx_def
  have hm_ge : (⌈x₀_boot⌉₊ + 1) ^ 12 ≤ m := hm
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (by intro h; subst h; simp at hm_ge)
  have hx_ge_1 : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  have hx_nonneg : (0 : ℝ) ≤ x := by linarith
  have h_ceil_le_x : ((⌈x₀_boot⌉₊ + 1 : ℕ) : ℝ) ≤ x := by
    rw [hx_def]
    have h12 : ((⌈x₀_boot⌉₊ + 1 : ℕ) : ℝ) ^ 12 ≤ (m : ℝ) := by exact_mod_cast hm_ge
    have h_rpow12 : (((⌈x₀_boot⌉₊ + 1 : ℕ) : ℝ) ^ 12) ^ ((1 : ℝ) / 12) ≤ (m : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.rpow_le_rpow (by positivity) h12 (by norm_num)
    rw [← Real.rpow_natCast ((⌈x₀_boot⌉₊ + 1 : ℕ) : ℝ) 12,
        ← Real.rpow_mul (Nat.cast_nonneg _)] at h_rpow12
    simp only [show ((12 : ℕ) : ℝ) * ((1 : ℝ) / 12) = 1 from by push_cast; ring] at h_rpow12
    rwa [Real.rpow_one] at h_rpow12
  have hfloor_pos : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx_ge_1
  have hfloor_ge_ceil_boot : ⌈x₀_boot⌉₊ + 1 ≤ ⌊x⌋₊ := by
    exact Nat.le_floor h_ceil_le_x
  have hfloor_ge_boot : x₀_boot ≤ (⌊x⌋₊ : ℝ) := by
    calc x₀_boot ≤ (⌈x₀_boot⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ ((⌈x₀_boot⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
      _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hfloor_ge_ceil_boot
  obtain ⟨j_floor, hj_floor⟩ := e_seq_reaches_nat x hx_ge_1 ⌊x⌋₊ hfloor_pos (Nat.floor_le hx_nonneg)
  have hfloor_pos_real : (0 : ℝ) < (⌊x⌋₊ : ℝ) := Nat.cast_pos.mpr hfloor_pos
  have h_density := hsmooth_boot (⌊x⌋₊ : ℝ) hfloor_ge_boot
  have hS_nonempty : {N : ℕ | (⌊x⌋₊ : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + 1) * (⌊x⌋₊ : ℝ) ∧
      (N : ℤ) ≡ 1 [ZMOD (1 : ℤ)] ∧ IsPowersmooth ((⌊x⌋₊ : ℝ) ^ (1 : ℝ)) N}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero; intro h0
    have h_le_zero : δ_boot * (⌊x⌋₊ : ℝ) ≤ 0 := h_density.trans (by exact_mod_cast h0.le)
    linarith [mul_pos hδ_boot_pos hfloor_pos_real]
  obtain ⟨N, hN_lo, hN_hi, _, hN_ps⟩ := hS_nonempty
  refine ⟨j_floor + 1, ?_⟩
  show x ≤ (e_seq x (j_floor + 1) : ℝ)
  have hN_gt_floor : ⌊x⌋₊ < N := by exact_mod_cast hN_lo
  have hN_ge_x : x ≤ (N : ℝ) := by
    have h1 : ⌊x⌋₊ + 1 ≤ N := hN_gt_floor
    calc x ≤ ↑⌊x⌋₊ + 1 := Nat.lt_floor_add_one x |>.le
      _ ≤ (N : ℝ) := by exact_mod_cast h1
  have hN_lt_2floor : (N : ℝ) < 2 * (⌊x⌋₊ : ℝ) := by linarith [hN_hi]
  have hN_le_2ej : N ≤ 2 * e_seq x j_floor := by
    have : N < 2 * ⌊x⌋₊ := by exact_mod_cast hN_lt_2floor
    omega
  have hN_ps_x : IsPowersmooth x N := by
    apply IsPowersmooth_mono _ hN_ps
    rw [Real.rpow_one]
    exact Nat.floor_le hx_nonneg
  have hN_pos : 1 ≤ N := by omega
  have h2ej_pos : 1 ≤ 2 * e_seq x j_floor := by
    have := e_seq_pos x hx_ge_1 j_floor; omega
  have hN_le_eseq : N ≤ e_seq x (j_floor + 1) :=
    largest_ps_le_is_max hx_ge_1 h2ej_pos N hN_pos hN_le_2ej hN_ps_x
  calc x ≤ (N : ℝ) := hN_ge_x
    _ ≤ (e_seq x (j_floor + 1) : ℝ) := by exact_mod_cast hN_le_eseq

lemma e_seq_bounded_unbounded
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N})) :
    ∀ᶠ (m : ℕ) in atTop, ∀ T : ℕ, 2 ≤ T → (T : ℝ) ≤ (m : ℝ) ^ 2 →
      ∃ j, T ≤ e_seq ((m : ℝ) ^ ((1 : ℝ) / 12)) j := by
  have h_growth := e_seq_growth_eventually smooth_arith
  have h_boot := e_seq_exceeds_x smooth_arith
  filter_upwards [h_growth, h_boot, Filter.eventually_ge_atTop 2] with m hgrowth hboot hm_ge_2
  set x := (m : ℝ) ^ ((1 : ℝ) / 12) with hx_def
  have hx_ge_1 : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  obtain ⟨j₀, hj₀⟩ := hboot
  intro T hT hT_le
  by_contra h_not
  push_neg at h_not
  have h_all_lt : ∀ j, e_seq x j < T := fun j => h_not j
  have h_all_le_m2 : ∀ j, (e_seq x j : ℝ) ≤ (m : ℝ) ^ 2 := fun j => by
    have hlt := h_all_lt j
    have : (e_seq x j : ℝ) < (T : ℝ) := by exact_mod_cast hlt
    linarith
  have h_strictly_inc : ∀ j, j₀ ≤ j → e_seq x j < e_seq x (j + 1) := by
    intro j hj
    have hge : x ≤ (e_seq x j : ℝ) :=
      le_trans hj₀ (by exact_mod_cast (e_seq_mono x hx_ge_1 hj))
    have := hgrowth j hge (h_all_le_m2 j)
    omega
  have h_lower : ∀ n, e_seq x j₀ + n ≤ e_seq x (j₀ + n) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      have h_inc := h_strictly_inc (j₀ + n) (by omega)
      have : j₀ + (n + 1) = j₀ + n + 1 := by omega
      rw [this]
      omega
  have := h_lower T
  have := h_all_lt (j₀ + T)
  omega

-- e_seq growth for early values: when 2*e_seq ≤ x, doubling gives 3/2 growth
lemma e_seq_growth_early (x : ℝ) (hx : 1 ≤ x) (i : ℕ)
    (hi : 2 * (e_seq x i : ℝ) ≤ x) :
    3 * e_seq x i < 2 * e_seq x (i + 1) := by
  have hei_pos := e_seq_pos x hx i
  apply e_seq_growth_from_witness x hx i (2 * e_seq x i)
  · linarith
  · exact le_refl _
  · apply nat_le_is_powersmooth x (2 * e_seq x i) (by omega)
    exact_mod_cast hi

-- Full growth: for all e_seq values below m², 3/2 growth holds
lemma e_seq_growth_all
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N})) :
    ∀ᶠ (m : ℕ) in atTop, ∀ i : ℕ,
      (e_seq ((m : ℝ) ^ ((1 : ℝ) / 12)) i : ℝ) ≤ (m : ℝ) ^ 2 →
      3 * e_seq ((m : ℝ) ^ ((1 : ℝ) / 12)) i < 2 * e_seq ((m : ℝ) ^ ((1 : ℝ) / 12)) (i + 1) := by
  have h_large := e_seq_growth_eventually smooth_arith
  set ε := (1 : ℝ) / 48 with hε_def
  have hε_pos : (0 : ℝ) < ε := by norm_num
  obtain ⟨x₀, δ, hδ_pos, hδ⟩ := smoothinarith smooth_arith 1 210 (by norm_num) ε hε_pos
  have h_rpow := rpow_eps_le_rpow_twelfth (1/4) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / 4 / 12 = ε from by rw [hε_def]; ring] at h_rpow
  filter_upwards [h_large, h_rpow,
    Filter.eventually_ge_atTop (max (max (⌈x₀⌉₊ ^ 12) 2) ⌈(2 * x₀ + 2) ^ 12⌉₊)] with m hgrowth_large h_rpow_m hm_ge
  set x := (m : ℝ) ^ ((1 : ℝ) / 12) with hx_def
  have hm_ge_2 : 2 ≤ m := by omega
  have hx_ge_1 : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  intro i hi
  by_cases h_early : 2 * (e_seq x i : ℝ) ≤ x
  · exact e_seq_growth_early x hx_ge_1 i h_early
  · push_neg at h_early
    by_cases h_mid : x ≤ (e_seq x i : ℝ)
    · exact hgrowth_large i h_mid hi
    · push_neg at h_mid
      -- Transition case: x/2 < e_seq < x
      have hei_pos : 0 < e_seq x i := e_seq_pos x hx_ge_1 i
      have hx_arg_pos : (0 : ℝ) < (3 : ℝ) / 2 * (e_seq x i : ℝ) := by positivity
      have hx_ge_x0 : x₀ ≤ (3 : ℝ) / 2 * (e_seq x i : ℝ) := by
        have : x₀ ≤ x / 2 := by
          have h12 : (2 * x₀ + 2) ^ 12 ≤ (m : ℝ) := by
            calc (2 * x₀ + 2) ^ 12 ≤ (⌈(2 * x₀ + 2) ^ 12⌉₊ : ℝ) := Nat.le_ceil _
              _ ≤ (m : ℝ) := by exact_mod_cast (show ⌈(2 * x₀ + 2) ^ 12⌉₊ ≤ m by omega)
          have hx12 : x ^ 12 = (m : ℝ) := by
            rw [hx_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
          have : (2 * x₀ + 2) ^ 12 ≤ x ^ 12 := by linarith
          have hx_pos : 0 < x := by linarith
          have : 2 * x₀ + 2 ≤ x := by
            by_contra h; push_neg at h
            have : x ^ 12 < (2 * x₀ + 2) ^ 12 := by
              exact pow_lt_pow_left₀ h (by linarith) (by omega)
            linarith
          linarith
        linarith [show (0 : ℝ) < e_seq x i from by exact_mod_cast hei_pos]
      have h_density := hδ ((3 : ℝ) / 2 * (e_seq x i : ℝ)) hx_ge_x0
      have hS_nonempty : {N : ℕ | (3 : ℝ) / 2 * (e_seq x i : ℝ) < (N : ℝ) ∧
        (N : ℝ) < (1 + ε) * ((3 : ℝ) / 2 * (e_seq x i : ℝ)) ∧
        (N : ℤ) ≡ 1 [ZMOD (210 : ℤ)] ∧ IsPowersmooth (((3 : ℝ) / 2 * (e_seq x i : ℝ)) ^ ε) N}.Nonempty := by
        apply Set.nonempty_of_ncard_ne_zero; intro h0
        have : (Set.ncard {N : ℕ | (3 : ℝ) / 2 * (e_seq x i : ℝ) < (N : ℝ) ∧
          (N : ℝ) < (1 + ε) * ((3 : ℝ) / 2 * (e_seq x i : ℝ)) ∧
          (N : ℤ) ≡ 1 [ZMOD (210 : ℤ)] ∧ IsPowersmooth (((3 : ℝ) / 2 * (e_seq x i : ℝ)) ^ ε) N} : ℝ) = 0 := by
          convert Nat.cast_zero
        linarith [mul_pos hδ_pos hx_arg_pos]
      obtain ⟨N, hN_lo, hN_hi, _, hN_ps⟩ := hS_nonempty
      apply e_seq_growth_from_witness x hx_ge_1 i N
      · exact_mod_cast show (3 : ℝ) * (e_seq x i : ℝ) < 2 * (N : ℝ) by linarith
      · have : (N : ℝ) < (1 + ε) * (3 / 2 * (e_seq x i : ℝ)) := hN_hi
        have : (1 + ε) * (3 / 2) < 2 := by rw [hε_def]; norm_num
        have : (N : ℝ) < 2 * (e_seq x i : ℝ) := by nlinarith
        exact_mod_cast show (N : ℝ) ≤ 2 * (e_seq x i : ℝ) by linarith
      · apply IsPowersmooth_mono _ hN_ps
        rw [hx_def]
        apply h_rpow_m
        · exact hx_arg_pos
        · calc (3 : ℝ) / 2 * (e_seq x i : ℝ) ≤ 2 * (e_seq x i : ℝ) := by linarith [show (0 : ℝ) < e_seq x i from by exact_mod_cast hei_pos]
            _ ≤ 2 * (m : ℝ) ^ 2 := by nlinarith

lemma rpow_eps_le_rpow_sixth (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀_lt : ε₀ < 1/3) :
    ∀ᶠ (m : ℕ) in atTop,
    ∀ (a : ℝ), 0 < a → a ≤ 2 * (m : ℝ) ^ 2 →
    a ^ (ε₀ / 12) ≤ (m : ℝ) ^ ((1 : ℝ) / 6) := by
  rw [Filter.eventually_atTop]
  refine ⟨2, fun m hm => ?_⟩
  intro a ha ha_le
  have hm_pos : (0 : ℝ) < m := by positivity
  have hm_ge_1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have h2m2_ge_1 : (1 : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by nlinarith
  have hε_12_le : ε₀ / 12 ≤ 1 / 36 := by linarith
  have hε_12_pos : 0 < ε₀ / 12 := by positivity
  have h1 : a ^ (ε₀ / 12) ≤ (2 * (m : ℝ) ^ 2) ^ (ε₀ / 12) :=
    Real.rpow_le_rpow (le_of_lt ha) ha_le (le_of_lt hε_12_pos)
  have h2 : (2 * (m : ℝ) ^ 2) ^ (ε₀ / 12) ≤ (2 * (m : ℝ) ^ 2) ^ ((1 : ℝ) / 36) :=
    Real.rpow_le_rpow_of_exponent_le h2m2_ge_1 hε_12_le
  have h3 : (2 * (m : ℝ) ^ 2) ^ ((1 : ℝ) / 36) = 2 ^ ((1 : ℝ) / 36) * ((m : ℝ) ^ 2) ^ ((1 : ℝ) / 36) :=
    Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)
  have h4 : ((m : ℝ) ^ 2) ^ ((1 : ℝ) / 36) = (m : ℝ) ^ ((1 : ℝ) / 18) := by
    rw [← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ m)]
    norm_num
  have h5 : (2 : ℝ) ^ ((1 : ℝ) / 36) ≤ (m : ℝ) ^ ((1 : ℝ) / 9) := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 36) ≤ (2 : ℝ) ^ ((1 : ℝ) / 9) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ (m : ℝ) ^ ((1 : ℝ) / 9) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hm) (by norm_num)
  have h6 : (m : ℝ) ^ ((1 : ℝ) / 9) * (m : ℝ) ^ ((1 : ℝ) / 18) = (m : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < m)]
    norm_num
  have hm18_pos : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 18) := Real.rpow_nonneg (by positivity) _
  calc a ^ (ε₀ / 12) ≤ (2 * (m : ℝ) ^ 2) ^ ((1 : ℝ) / 36) := le_trans h1 h2
    _ = 2 ^ ((1 : ℝ) / 36) * (m : ℝ) ^ ((1 : ℝ) / 18) := by rw [h3, h4]
    _ ≤ (m : ℝ) ^ ((1 : ℝ) / 9) * (m : ℝ) ^ ((1 : ℝ) / 18) :=
        mul_le_mul_of_nonneg_right h5 hm18_pos
    _ = (m : ℝ) ^ ((1 : ℝ) / 6) := h6

lemma J_interval_elements
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N}))
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀_lt : ε₀ < 1/3) :
    ∀ᶠ (m : ℕ) in atTop,
      ∀ (k : ℕ), 0 < k → Nat.Coprime k 210 → (m : ℝ) < (k : ℝ) → (k : ℝ) ≤ (m : ℝ) ^ 2 →
      ∀ (a b : ℝ), (k : ℝ) < a → b < 2 * (k : ℝ) → a < b →
      b / a ≥ 1 + ε₀ / 12 →
      ∃ N : ℕ, a < (N : ℝ) ∧ (N : ℝ) < b ∧
        Nat.Coprime N 210 ∧ IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 6)) N := by
  have hε_pos : (0 : ℝ) < ε₀ / 12 := by positivity
  obtain ⟨x₀_sm, δ_sm, hδ_pos, hδ_sm⟩ := smoothinarith smooth_arith 1 210 (by norm_num) (ε₀ / 12) hε_pos
  have h_rpow := rpow_eps_le_rpow_sixth ε₀ hε₀ hε₀_lt
  rw [Filter.eventually_atTop]
  obtain ⟨m₀_rpow, hm_rpow⟩ := Filter.eventually_atTop.mp h_rpow
  refine ⟨max ⌈x₀_sm⌉₊ m₀_rpow, fun m hm => ?_⟩
  have hm_ge_rpow : m₀_rpow ≤ m := by omega
  have h_rpow_m := hm_rpow m hm_ge_rpow
  intro k hk_pos hk_cop hm_lt_k hk_le_m2 a b ha_lo hb_hi hab hba
  have ha_pos : 0 < a := lt_trans (Nat.cast_pos.mpr hk_pos) ha_lo
  have ha_ge_x0 : x₀_sm ≤ a := le_of_lt (by
    calc x₀_sm ≤ (⌈x₀_sm⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (m : ℝ) := by exact_mod_cast (show ⌈x₀_sm⌉₊ ≤ m by omega)
      _ < (k : ℝ) := hm_lt_k
      _ < a := ha_lo)
  have h_density := hδ_sm a ha_ge_x0
  have hS_nonempty : {N : ℕ | (a : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε₀ / 12) * a ∧
    (N : ℤ) ≡ 1 [ZMOD (210 : ℤ)] ∧ IsPowersmooth (a ^ (ε₀ / 12)) N}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero; intro h0
    have : (Set.ncard {N : ℕ | (a : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε₀ / 12) * a ∧
      (N : ℤ) ≡ 1 [ZMOD (210 : ℤ)] ∧ IsPowersmooth (a ^ (ε₀ / 12)) N} : ℝ) = 0 := by
      convert Nat.cast_zero
    linarith [mul_pos hδ_pos ha_pos]
  obtain ⟨N, hN_lo, hN_hi, hN_mod, hN_ps⟩ := hS_nonempty
  have hb_ge : (1 + ε₀ / 12) * a ≤ b := by
    rwa [ge_iff_le, le_div_iff₀ ha_pos] at hba
  refine ⟨N, hN_lo, lt_of_lt_of_le hN_hi hb_ge, ?_, ?_⟩
  · exact Nat.coprime_of_mul_modEq_one 1 (by rw [mul_one]; exact_mod_cast hN_mod)
  · apply IsPowersmooth_mono _ hN_ps
    exact h_rpow_m a ha_pos (by linarith)

-- ε₀/2 * k ≤ el₁ implies ε₀/2 ≤ el₁/k
lemma eps1_lower_bound (el₁ : ℕ) (k : ℕ) (hk : 0 < k)
    (ε₀ : ℝ) (_hε₀ : 0 < ε₀) (h : ⌈ε₀ / 2 * (k : ℝ)⌉₊ ≤ el₁) :
    ε₀ / 2 ≤ (el₁ : ℝ) / (k : ℝ) := by
  rw [le_div_iff₀ (Nat.cast_pos.mpr hk)]
  calc ε₀ / 2 * (k : ℝ) ≤ (⌈ε₀ / 2 * (k : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (el₁ : ℝ) := by exact_mod_cast h

-- (4/3)^(i+1) * ε₁ < 1 when i+1 < ⌊-log(ε₁)/log(4/3)⌋
lemma pow_43_eps_lt_one (ε₁ : ℝ) (hε₁ : 0 < ε₁) (hε₁_lt : ε₁ < 1) (i : ℕ)
    (hi : i + 1 < ⌊-Real.log ε₁ / Real.log (4/3 : ℝ)⌋₊) :
    ((4:ℝ)/3) ^ (i + 1) * ε₁ < 1 := by
  have hlog43 : (0 : ℝ) < Real.log (4/3) := Real.log_pos (by norm_num)
  have hlog_neg : 0 < -Real.log ε₁ := by rw [neg_pos]; exact Real.log_neg hε₁ hε₁_lt
  have hL_pos : (0 : ℝ) < -Real.log ε₁ / Real.log (4/3) := div_pos hlog_neg hlog43
  have hi_lt_L : (↑(i + 1) : ℝ) < -Real.log ε₁ / Real.log (4/3) :=
    lt_of_lt_of_le (by exact_mod_cast hi) (Nat.floor_le hL_pos.le)
  have h_mul : (↑(i + 1) : ℝ) * Real.log (4/3) < -Real.log ε₁ := by
    rwa [lt_div_iff₀ hlog43] at hi_lt_L
  have h_log_prod : Real.log ((4/3 : ℝ) ^ (i + 1) * ε₁) < 0 := by
    rw [Real.log_mul (by positivity) (ne_of_gt hε₁), Real.log_pow]
    linarith
  exact (Real.log_neg_iff (by positivity)).mp h_log_prod

lemma J_ratio_ge (ε₀ ε₁ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁)
    (hε₁_ge : ε₀ / 2 ≤ ε₁) (hε₁_lt : ε₁ < 1) (k : ℕ) (hk : 0 < k) (i : ℕ)
    (h_pow_lt : ((4:ℝ)/3) ^ (i + 1) * ε₁ < 1) :
    ((k : ℝ) + ((4:ℝ)/3) ^ (i + 1) * ε₁ * (k : ℝ)) /
    ((k : ℝ) + ((4:ℝ)/3) ^ i * ε₁ * (k : ℝ)) ≥ 1 + ε₀ / 12 := by
  field_simp at *
  ring_nf at *
  nlinarith [pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 4 / 3) (show i ≥ 0 by norm_num)]

/-
----------------------------------
PART 7: Construction and properties of D.
----------------------------------
-/

def D_multiplier_injective (D : Finset ℕ) : Prop :=
  ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ c₁ ∈ ({20, 21, 28, 30} : Finset ℕ),
    ∀ c₂ ∈ ({20, 21, 28, 30} : Finset ℕ), c₁ * d₁ = c₂ * d₂ → c₁ = c₂ ∧ d₁ = d₂

lemma coprime_210_to_c (d : ℕ) (h : Nat.Coprime d 210) (c : ℕ) (hc : c ∈ ({20, 21, 28, 30} : Finset ℕ)) :
    Nat.Coprime d c := by
  have h2 : Nat.Coprime d 2 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  have h3 : Nat.Coprime d 3 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  have h5 : Nat.Coprime d 5 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  have h7 : Nat.Coprime d 7 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  fin_cases hc
  · exact (h2.pow_right 2).mul_right h5
  · exact h3.mul_right h7
  · exact (h2.pow_right 2).mul_right h7
  · exact (h2.mul_right h3).mul_right h5

-- D₂ elements coprime to 210 satisfy multiplier injectivity
lemma mult_inj_coprime_210 (D : Finset ℕ)
    (hcop : ∀ d ∈ D, Nat.Coprime d 210)
    (hpos : ∀ d ∈ D, 0 < d) :
    D_multiplier_injective D := by
  intro d₁ hd₁ d₂ hd₂ c₁ hc₁ c₂ hc₂ heq
  have hcop_d₁_c₂ : Nat.Coprime d₁ c₂ := coprime_210_to_c d₁ (hcop d₁ hd₁) c₂ hc₂
  have hcop_d₂_c₁ : Nat.Coprime d₂ c₁ := coprime_210_to_c d₂ (hcop d₂ hd₂) c₁ hc₁
  have h₁ : d₁ ∣ d₂ := by
    apply hcop_d₁_c₂.dvd_of_dvd_mul_left
    exact Dvd.intro_left c₁ (by linarith)
  have h₂ : d₂ ∣ d₁ := by
    apply hcop_d₂_c₁.dvd_of_dvd_mul_left
    exact Dvd.intro_left c₂ (by linarith)
  have hd_eq : d₁ = d₂ := Nat.dvd_antisymm h₁ h₂
  exact ⟨by nlinarith [hpos d₁ hd₁], hd_eq⟩

-- Mixed D₁/D₂ case: if c₁d₁ = c₂d₂ where d₁ = e*(k+1) with e < k, d₂ coprime to 210 in (k,2k), then d₁=d₂ and c₁=c₂
lemma mult_inj_mixed (k : ℕ) (_hk : 0 < k) (_hk2 : 1 < k)
    (d₁ d₂ c₁ c₂ : ℕ)
    (hc₁ : c₁ ∈ ({20, 21, 28, 30} : Finset ℕ))
    (hc₂ : c₂ ∈ ({20, 21, 28, 30} : Finset ℕ))
    (hd₁_form : ∃ e : ℕ, 0 < e ∧ e < k ∧ d₁ = e * (k + 1))
    (hd₂_cop : Nat.Coprime d₂ 210)
    (hd₂_gt : k < d₂) (hd₂_lt : d₂ < 2 * k)
    (heq : c₁ * d₁ = c₂ * d₂) :
    c₁ = c₂ ∧ d₁ = d₂ := by
  obtain ⟨e, he_pos, he_lt, rfl⟩ := hd₁_form
  have hcop_d₂_c₁ : Nat.Coprime d₂ c₁ := coprime_210_to_c d₂ hd₂_cop c₁ hc₁
  have hdvd : d₂ ∣ e * (k + 1) :=
    hcop_d₂_c₁.dvd_of_dvd_mul_left (Dvd.intro_left c₂ (by linarith))
  obtain ⟨q, hq⟩ := hdvd
  have hq_pos : 0 < q := by
    by_contra h; push_neg at h; interval_cases q; simp at hq; omega
  have hcq : c₁ * q = c₂ :=
    mul_right_cancel₀ (show (d₂ : ℕ) ≠ 0 by omega) (show c₁ * q * d₂ = c₂ * d₂ by nlinarith)
  have hq1 : q = 1 := by
    have hc₁_ge : 20 ≤ c₁ := by fin_cases hc₁ <;> omega
    have hc₂_le : c₂ ≤ 30 := by fin_cases hc₂ <;> omega
    nlinarith
  subst hq1; simp at hq hcq; exact ⟨hcq, hq⟩

-- D₁ multiplier injectivity: 3/2 growth implies no c₁d_i = c₂d_j collision for distinct elements
lemma mult_inj_32_growth {d₁ d₂ c₁ c₂ : ℕ}
    (hc₁ : c₁ ∈ ({20, 21, 28, 30} : Finset ℕ))
    (hc₂ : c₂ ∈ ({20, 21, 28, 30} : Finset ℕ))
    (hd_lt : d₁ < d₂)
    (h32 : 3 * d₁ < 2 * d₂)
    (heq : c₁ * d₁ = c₂ * d₂) : False := by
  have hc₁_pos : 0 < c₁ := by fin_cases hc₁ <;> omega
  have hc₂_pos : 0 < c₂ := by fin_cases hc₂ <;> omega
  have hd₂_pos : 0 < d₂ := by
    by_contra h; push_neg at h; interval_cases d₂; omega
  have hd₁_pos : 0 < d₁ := by
    by_contra h; push_neg at h; interval_cases d₁
    simp at heq; rcases heq with h | h <;> omega
  have heq' : (c₁ : ℤ) * d₁ = c₂ * d₂ := by exact_mod_cast heq
  have h32' : 3 * (d₁ : ℤ) < 2 * d₂ := by exact_mod_cast h32
  have hd_lt' : (d₁ : ℤ) < d₂ := by exact_mod_cast hd_lt
  have hd₁_pos' : (0 : ℤ) < d₁ := by exact_mod_cast hd₁_pos
  have : (c₂ : ℤ) < c₁ := by nlinarith
  have : (3 : ℤ) * c₂ < 2 * c₁ := by nlinarith
  fin_cases hc₁ <;> fin_cases hc₂ <;> omega

/-
StrictMono e on {0,...,l₁} given e(j) < e(j+1) for j < l₁.
-/
lemma strict_mono_e (l₁ : ℕ) (e : ℕ → ℕ)
    (he_step : ∀ j, j < l₁ → e j < e (j + 1)) :
    ∀ a b, a ≤ l₁ → b ≤ l₁ → a < b → e a < e b := by
  intro a b ha hb hab;
  induction' hab with k hk;
  · exact he_step a ( Nat.lt_of_succ_le hb );
  · exact lt_trans ( by solve_by_elim [ Nat.le_of_succ_le ] ) ( he_step _ ( Nat.lt_of_succ_le hb ) )

/-
Monotone e on {0,...,l₁}.
-/
lemma mono_e (l₁ : ℕ) (e : ℕ → ℕ)
    (he_step : ∀ j, j < l₁ → e j < e (j + 1)) :
    ∀ a b, a ≤ l₁ → b ≤ l₁ → a ≤ b → e a ≤ e b := by
  intros a b ha hb hab; induction' b with b ih generalizing a; induction' a with a ih' ; aesop;
  · contradiction;
  · grind

/-
Combined vals is strictly monotone.
-/
lemma combined_vals_strict_mono
    (k l₁ : ℕ) (e : ℕ → ℕ)
    (he_mono : ∀ j, j < l₁ → e j < e (j + 1))
    (l₂ : ℕ) (f : Fin l₂ → ℕ)
    (hf_gt_k : ∀ i, k < f i)
    (hf_res_mono : StrictMono (fun i : Fin l₂ => f i - k))
    (he_lt_f_res : ∀ (h : 0 < l₂), e l₁ < f ⟨0, h⟩ - k) :
    StrictMono (fun i : Fin (l₁ + 1 + l₂) =>
      if h : i.val < l₁ + 1 then e i.val
      else f ⟨i.val - (l₁ + 1), by omega⟩ - k) := by
  intro i j hij;
  by_cases hi : i.val < l₁ + 1 <;> by_cases hj : j.val < l₁ + 1 <;> simp +decide [ * ]
  all_goals generalize_proofs at *;
  · convert strict_mono_e l₁ e he_mono _ _ _ _ _ using 1 <;> linarith [ show ( i : ℕ ) < j from hij ];
  · -- Since $i < j$ and $j \geq l₁ + 1$, we have $e i \leq e l₁$ by the monotonicity of $e$.
    have h_e_i_le_e_l₁ : e i ≤ e l₁ := by
      apply_rules [ mono_e ];
      · linarith;
      · linarith;
      · linarith;
    refine lt_of_le_of_lt h_e_i_le_e_l₁ <| lt_of_lt_of_le ( he_lt_f_res <| Nat.pos_of_ne_zero <| by aesop ) <| hf_res_mono.monotone <| Nat.zero_le _;
  · exact False.elim <| hi <| lt_of_lt_of_le hij hj.le;
  · exact hf_res_mono ( Nat.sub_lt_sub_right ( by linarith [ show ( i : ℕ ) < j from hij ] ) ( by linarith [ show ( i : ℕ ) < j from hij ] ) )

/-
Combined vals gap property.
-/
lemma combined_vals_gap
    (k l₁ : ℕ) (e : ℕ → ℕ)
    (he_le_double : ∀ j, j ≤ l₁ → e (j + 1) ≤ 2 * e j)
    (l₂ : ℕ) (f : Fin l₂ → ℕ)
    (hf_gt_k : ∀ i, k < f i)
    (hf_first_le : ∀ (h : 0 < l₂), f ⟨0, h⟩ - k ≤ 2 * e l₁)
    (hf_res_gap : ∀ (i : Fin l₂), (i : ℕ) ≥ 1 →
      f i - k ≤ 2 * (f ⟨(i : ℕ) - 1, by omega⟩ - k)) :
    let vals : Fin (l₁ + 1 + l₂) → ℕ := fun i =>
      if h : i.val < l₁ + 1 then e i.val
      else f ⟨i.val - (l₁ + 1), by omega⟩ - k
    ∀ i : Fin (l₁ + 1 + l₂), (i : ℕ) ≥ 1 →
      vals i ≤ 2 * vals ⟨i - 1, by omega⟩ := by
  grind +splitIndPred

/-
Combined sum equals e sum + f residue sum.
-/
lemma combined_vals_sum
    (k l₁ : ℕ) (e : ℕ → ℕ) (l₂ : ℕ) (f : Fin l₂ → ℕ)
    (hf_gt_k : ∀ i, k < f i) :
    let vals : Fin (l₁ + 1 + l₂) → ℕ := fun i =>
      if h : i.val < l₁ + 1 then e i.val
      else f ⟨i.val - (l₁ + 1), by omega⟩ - k
    Finset.univ.sum vals =
      (Finset.range (l₁ + 1)).sum e +
      (Finset.univ : Finset (Fin l₂)).sum (fun i => f i - k) := by
  simp +zetaDelta at *;
  rw [ Finset.sum_fin_eq_sum_range ];
  rw [ Finset.sum_range_add _ _ ];
  norm_num [ add_assoc, Finset.sum_range ];
  grind

/-
g is injective.
-/
lemma combined_g_injective
    (k l₁ : ℕ) (hk2 : 1 < k)
    (e : ℕ → ℕ)
    (he_lt_k : ∀ j, j ≤ l₁ → e j < k)
    (he_inj : ∀ a b, a ≤ l₁ → b ≤ l₁ → e a = e b → a = b)
    (he_mono : ∀ j, j < l₁ → e j < e (j + 1))
    (l₂ : ℕ) (f : Fin l₂ → ℕ)
    (hf_gt_k : ∀ i, k < f i)
    (hf_lt_2k : ∀ i, f i < 2 * k)
    (hf_inj : Function.Injective f)
    (he_lt_f_res : ∀ (h : 0 < l₂), e l₁ < f ⟨0, h⟩ - k)
    (hf_res_mono : StrictMono (fun i : Fin l₂ => f i - k)) :
    let g : Fin (l₁ + 1 + l₂) → ℕ := fun i =>
      if h : i.val < l₁ + 1 then e i.val * (k + 1)
      else f ⟨i.val - (l₁ + 1), by omega⟩
    Function.Injective g := by
  simp +zetaDelta at *;
  intro i j; rcases i with ⟨ i, hi ⟩ ; rcases j with ⟨ j, hj ⟩ ; simp +decide [ * ] ;
  split_ifs;
  · exact fun h => he_inj i j ‹_› ‹_› ( by nlinarith );
  · intro h_eq
    have h_mod : e i = f ⟨j - (l₁ + 1), by omega⟩ - k := by
      have h_mod : e i * (k + 1) % k = (f ⟨j - (l₁ + 1), by omega⟩ - k) % k := by
        simp +decide [ ← h_eq ];
        rw [ Nat.modEq_of_dvd ];
        rw [ Nat.cast_sub ] <;> push_cast <;> ring_nf <;> norm_num ;
        grind +splitImp;
      norm_num [ Nat.add_mod, Nat.mul_mod ] at h_mod;
      simp +zetaDelta at *;
      rw [ Nat.mod_eq_of_lt ( he_lt_k i ‹_› ), Nat.mod_eq_of_lt ( show f ⟨ j - ( l₁ + 1 ), by omega ⟩ - k < k from by rw [ tsub_lt_iff_left ] <;> linarith [ hf_gt_k ⟨ j - ( l₁ + 1 ), by omega ⟩, hf_lt_2k ⟨ j - ( l₁ + 1 ), by omega ⟩ ] ) ] at h_mod ; linarith;
    have h_contra : e i ≤ e l₁ := by
      apply_rules [ mono_e ];
      grobner;
    have h_contra : e l₁ < f ⟨j - (l₁ + 1), by omega⟩ - k := by
      exact lt_of_lt_of_le ( he_lt_f_res ( by linarith ) ) ( hf_res_mono.monotone ( Nat.zero_le _ ) );
    grind;
  · intro h_eq
    have h_mod : f ⟨i - (l₁ + 1), by omega⟩ % k = e j := by
      norm_num [ h_eq, Nat.add_mod, Nat.mul_mod ];
      norm_num [ Nat.mod_eq_of_lt ( he_lt_k j ‹_› ) ];
    have h_mod : f ⟨i - (l₁ + 1), by omega⟩ % k = f ⟨i - (l₁ + 1), by omega⟩ - k := by
      rw [ Nat.mod_eq_sub_mod ( by linarith [ hf_gt_k ⟨ i - ( l₁ + 1 ), by omega ⟩ ] ) ]
      rw [ Nat.mod_eq_of_lt ( by
        have := hf_gt_k ⟨ i - ( l₁ + 1 ), by omega ⟩
        have := hf_lt_2k ⟨ i - ( l₁ + 1 ), by omega ⟩
        omega ) ]
    generalize_proofs at *; (
    have h_contra : e j ≥ f ⟨0, Nat.pos_of_ne_zero (by
    grind +extAll)⟩ - k := by
      exact Nat.le_of_not_lt fun h => by have := hf_res_mono.monotone ( show ⟨ 0, by linarith ⟩ ≤ ⟨ i - ( l₁ + 1 ), by linarith ⟩ from Nat.zero_le _ ) ; norm_num at * ; omega;
    generalize_proofs at *; (
    exact absurd h_contra ( not_le_of_gt ( lt_of_le_of_lt ( show e j ≤ e l₁ from by exact mono_e l₁ e he_mono _ _ ( by linarith ) ( by linarith ) ( by linarith ) ) ( he_lt_f_res ‹_› ) ) )));
  · exact fun h => by have := hf_inj h; simp_all +decide [ Fin.ext_iff ] ; omega;

/-
g(i) % k = vals(i).
-/
lemma combined_g_mod
    (k l₁ : ℕ)
    (e : ℕ → ℕ)
    (he_lt_k : ∀ j, j ≤ l₁ → e j < k)
    (l₂ : ℕ) (f : Fin l₂ → ℕ)
    (hf_gt_k : ∀ i, k < f i)
    (hf_lt_2k : ∀ i, f i < 2 * k) :
    let vals : Fin (l₁ + 1 + l₂) → ℕ := fun i =>
      if h : i.val < l₁ + 1 then e i.val
      else f ⟨i.val - (l₁ + 1), by omega⟩ - k
    let g : Fin (l₁ + 1 + l₂) → ℕ := fun i =>
      if h : i.val < l₁ + 1 then e i.val * (k + 1)
      else f ⟨i.val - (l₁ + 1), by omega⟩
    ∀ i, g i % k = vals i := by
  simp +zetaDelta at *;
  intro i;
  split_ifs <;> norm_num [ Nat.add_mod, Nat.mul_mod ];
  · norm_num [ Nat.mod_eq_of_lt ( he_lt_k _ ‹_› ) ];
  · rw [ Nat.mod_eq_sub_mod ( by linarith [ hf_gt_k ⟨ i - ( l₁ + 1 ), by omega ⟩ ] ),
         Nat.mod_eq_of_lt ( by
           have := hf_gt_k ⟨ i - ( l₁ + 1 ), by omega ⟩
           have := hf_lt_2k ⟨ i - ( l₁ + 1 ), by omega ⟩
           omega ) ]

/-
g(i) ∈ D₁ ∪ D₂.
-/
lemma combined_g_mem
    (k l₁ : ℕ) (e : ℕ → ℕ)
    (l₂ : ℕ) (f : Fin l₂ → ℕ)
    (D₁ : Finset ℕ) (hD₁ : D₁ = (Finset.range (l₁ + 1)).image (fun j => e j * (k + 1)))
    (D₂ : Finset ℕ) (hD₂ : D₂ = Finset.univ.image f) :
    let g : Fin (l₁ + 1 + l₂) → ℕ := fun i =>
      if h : i.val < l₁ + 1 then e i.val * (k + 1)
      else f ⟨i.val - (l₁ + 1), by omega⟩
    ∀ i, g i ∈ D₁ ∪ D₂ := by
  grind

/-- Complete sequences: if x is a strictly monotone sequence with x(0)=1 and
    x(i) ≤ 2·x(i-1), then every integer in {1,...,∑x} is a subset sum. -/
lemma complete_sequence (l : ℕ) (hl : l ≥ 1) (x : Fin l → ℕ)
    (hpos : ∀ i, 0 < x i)
    (hmono : StrictMono x)
    (hx1 : x ⟨0, by omega⟩ = 1)
    (hgap : ∀ i : Fin l, (i : ℕ) ≥ 1 → x i ≤ 2 * x ⟨i - 1, by omega⟩) :
    ∀ n : ℕ, 1 ≤ n → n ≤ Finset.univ.sum x →
      ∃ S : Finset (Fin l), S.sum x = n := by
  induction' l with l ih;
  · contradiction;
  · by_cases hl : l ≥ 1;
    · -- Let $y = \sum_{i=0}^{l-1} x_i$.
      set y := Finset.sum (Finset.univ : Finset (Fin l)) (fun i => x (Fin.castSucc i)) with hy;
      -- Since $x$ is strictly increasing, we have $x_l \leq y + 1$.
      have hx_l_le_y_plus_1 : x (Fin.last l) ≤ y + 1 := by
        -- By induction on $i$, we can show that $x_i \leq \sum_{j=0}^{i-1} x_j + 1$ for all $i$.
        have h_ind : ∀ i : Fin (l + 1), x i ≤ ∑ j ∈ Finset.univ.filter (fun j => j.val < i.val), x j + 1 := by
          intro i
          induction' i using Fin.induction with i ih;
          · grind;
          · specialize hgap ( Fin.succ i ) ; simp_all +decide [Finset.sum_filter];
            simp_all +decide [Finset.sum_ite];
            rw [ show ( Finset.filter ( fun j : Fin ( l + 1 ) => ( j : ℕ ) ≤ i ) Finset.univ : Finset ( Fin ( l + 1 ) ) ) = Finset.filter ( fun j : Fin ( l + 1 ) => ( j : ℕ ) < i ) Finset.univ ∪ { ⟨ i, by linarith [ Fin.is_lt i ] ⟩ } from ?_, Finset.sum_union ] <;> norm_num;
            · linarith!;
            · grind +ring;
        convert h_ind ( Fin.last l ) using 1;
        simp +zetaDelta at *;
        refine' Finset.sum_bij ( fun i hi => Fin.castSucc i ) _ _ _ _ <;> simp +decide [ Fin.ext_iff ];
        exact fun i hi => ⟨ ⟨ i, hi ⟩, rfl ⟩;
      intro n hn1 hn2; by_cases hn3 : n ≤ y;
      · specialize ih hl ( fun i => x ( Fin.castSucc i ) ) ( fun i => hpos _ ) ( fun i j hij => hmono ( by simpa using hij ) ) ( by simpa using hx1 ) ( fun i hi => hgap _ <| by simpa using hi ) n hn1 hn3;
        obtain ⟨ S, hS ⟩ := ih; use Finset.image ( Fin.castSucc ) S; aesop;
      · -- Since $n > y$, we have $n = x_l + m$ for some $m$ such that $0 \leq m \leq y$.
        obtain ⟨m, hm⟩ : ∃ m, n = x (Fin.last l) + m ∧ m ≤ y := by
          use n - x (Fin.last l);
          rw [ Fin.sum_univ_castSucc ] at hn2 ; omega;
        by_cases hm1 : 1 ≤ m;
        · obtain ⟨ S, hS ⟩ := ih hl ( fun i => x ( Fin.castSucc i ) ) ( fun i => hpos _ ) ( fun i j hij => hmono ( by simpa using hij ) ) ( by simpa using hx1 ) ( fun i hi => hgap _ <| by simpa using hi ) m hm1 hm.2;
          use Finset.image ( Fin.castSucc ) S ∪ { Fin.last l } ; aesop;
        · exact ⟨ { Fin.last l }, by aesop ⟩;
    · interval_cases l ; simp_all +decide;
      intro n hn hn'; interval_cases n; exact ⟨ { 0 }, by norm_num [ hx1 ] ⟩ ;

/-
Subset sums of D cover all residues mod k, given a complete sequence of residues.
-/
lemma D_cover_from_complete_seq
    (k : ℕ)
    (l : ℕ) (hl : 1 ≤ l)
    (vals : Fin l → ℕ)
    (hvals_pos : ∀ i, 0 < vals i)
    (hvals_mono : StrictMono vals)
    (hvals_1 : vals ⟨0, by omega⟩ = 1)
    (hvals_gap : ∀ i : Fin l, (i : ℕ) ≥ 1 → vals i ≤ 2 * vals ⟨i - 1, by omega⟩)
    (hsum_ge : Finset.univ.sum vals ≥ k)
    (D : Finset ℕ)
    (hD_vals : ∃ g : Fin l → ℕ, (∀ i, g i ∈ D) ∧ Function.Injective g ∧
      ∀ i, g i % k = vals i) :
    ∀ r : ℕ, r < k → ∃ D' : Finset ℕ, D' ⊆ D ∧ D'.sum id % k = r := by
  intro r hr;
  obtain ⟨g, hg_mem, hg_inj, hg_mod⟩ := hD_vals
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin l), S.sum vals = r := by
    by_cases hr1 : 1 ≤ r;
    · have := complete_sequence l hl vals hvals_pos hvals_mono hvals_1 hvals_gap r hr1 ( by linarith ) ; aesop;
    · exact ⟨ ∅, by aesop ⟩
  use S.image g;
  simp_all +decide [ Finset.sum_nat_mod, Finset.sum_image, hg_inj.eq_iff ];
  exact ⟨ Finset.image_subset_iff.mpr fun i hi => hg_mem i, Nat.mod_eq_of_lt hr ⟩

-- The main cover lemma
lemma D_cover_combined
    (k : ℕ) (hk2 : 1 < k)
    (l₁ : ℕ)
    (e : ℕ → ℕ)
    (he_pos : ∀ j, j ≤ l₁ → 0 < e j)
    (he_1 : e 0 = 1)
    (he_le_double : ∀ j, j ≤ l₁ → e (j + 1) ≤ 2 * e j)
    (he_mono : ∀ j, j < l₁ → e j < e (j + 1))
    (he_lt_k : ∀ j, j ≤ l₁ → e j < k)
    (l₂ : ℕ)
    (f : Fin l₂ → ℕ)
    (hf_gt_k : ∀ i, k < f i)
    (hf_lt_2k : ∀ i, f i < 2 * k)
    (hf_first_le : ∀ (h : 0 < l₂), f ⟨0, h⟩ - k ≤ 2 * e l₁)
    (hf_res_mono : StrictMono (fun i : Fin l₂ => f i - k))
    (hf_res_gap : ∀ (i : Fin l₂), (i : ℕ) ≥ 1 →
      f i - k ≤ 2 * (f ⟨(i : ℕ) - 1, by omega⟩ - k))
    (he_lt_f_res : ∀ (h : 0 < l₂), e l₁ < f ⟨0, h⟩ - k)
    (hsum_ge : (Finset.range (l₁ + 1)).sum e +
      (Finset.univ : Finset (Fin l₂)).sum (fun i => f i - k) ≥ k)
    (D₁ : Finset ℕ) (hD₁ : D₁ = (Finset.range (l₁ + 1)).image (fun j => e j * (k + 1)))
    (D₂ : Finset ℕ) (hD₂ : D₂ = Finset.univ.image f)
    (he_inj : ∀ a b, a ≤ l₁ → b ≤ l₁ → e a = e b → a = b)
    (hf_inj : Function.Injective f) :
    ∀ r : ℕ, r < k → ∃ D' : Finset ℕ, D' ⊆ D₁ ∪ D₂ ∧ D'.sum id % k = r := by
  set l := l₁ + 1 + l₂
  set vals : Fin l → ℕ := fun i =>
    if h : i.val < l₁ + 1 then e i.val
    else f ⟨i.val - (l₁ + 1), by omega⟩ - k
  set g_fn : Fin l → ℕ := fun i =>
    if h : i.val < l₁ + 1 then e i.val * (k + 1)
    else f ⟨i.val - (l₁ + 1), by omega⟩
  -- vals positive
  have hvals_pos : ∀ i, 0 < vals i := by
    intro i; simp only [vals]; split_ifs with h
    · exact he_pos i.val (by omega)
    · have := hf_gt_k ⟨i.val - (l₁ + 1), by omega⟩; omega
  -- vals strictly monotone
  have hvals_mono := combined_vals_strict_mono k l₁ e he_mono l₂ f hf_gt_k hf_res_mono he_lt_f_res
  -- vals(0) = 1
  have hl_pos : 0 < l := by omega
  have hvals_1 : vals ⟨0, hl_pos⟩ = 1 := by
    simp only [vals]; split_ifs with h
    · exact he_1
    · exfalso; omega
  -- gap
  have hvals_gap := combined_vals_gap k l₁ e he_le_double l₂ f hf_gt_k hf_first_le hf_res_gap
  -- vals < k
  have hvals_lt : ∀ i, vals i < k := by
    intro i; simp only [vals]; split_ifs with h
    · exact he_lt_k i.val (by omega)
    · have := hf_lt_2k ⟨i.val - (l₁ + 1), by omega⟩
      have := hf_gt_k ⟨i.val - (l₁ + 1), by omega⟩; omega
  -- sum ≥ k
  have hvals_sum : Finset.univ.sum vals ≥ k := by
    have hsv := combined_vals_sum k l₁ e l₂ f hf_gt_k
    simp only at hsv; rw [hsv]; exact hsum_ge
  exact D_cover_from_complete_seq k l (by omega) vals hvals_pos hvals_mono hvals_1
    hvals_gap hvals_sum (D₁ ∪ D₂) ⟨g_fn,
      combined_g_mem k l₁ e l₂ f D₁ hD₁ D₂ hD₂,
      combined_g_injective k l₁ hk2 e he_lt_k he_inj he_mono l₂ f hf_gt_k hf_lt_2k hf_inj
        he_lt_f_res hf_res_mono,
      combined_g_mod k l₁ e he_lt_k l₂ f hf_gt_k hf_lt_2k⟩

/-
Geometric sum of f₂ residues plus e_seq sum exceeds k.
-/
lemma geom_residue_sum_ge_k
    (k : ℕ) (hk_pos : 0 < k) (el₁ : ℕ)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀_lt : ε₀ < 1 / 3)
    (ε₁ : ℝ) (hε₁_pos : 0 < ε₁) (hε₁_lt : ε₁ < 1)
    (hε₁_def : ε₁ = (el₁ : ℝ) / (k : ℝ))
    (l₂ : ℕ) (hl₂_def : l₂ = ⌊-Real.log ε₁ / Real.log (4 / 3 : ℝ)⌋₊ - 1)
    (f₂ : Fin l₂ → ℕ)
    (hf₂_gt : ∀ i : Fin l₂, k < f₂ i)
    (hf₂_spec : ∀ i : Fin l₂,
      (k : ℝ) + ((4 : ℝ) / 3) ^ (i : ℕ) * ε₁ * (k : ℝ) < (f₂ i : ℝ))
    (S_eseq : ℕ) (hS_ge : el₁ ≤ S_eseq)
    (hk_large : (192 : ℕ) ≤ k)
    (hel₁_upper : (el₁ : ℝ) ≤ ε₀ * (k : ℝ) + 2) :
    S_eseq + (Finset.univ : Finset (Fin l₂)).sum (fun i => f₂ i - k) ≥ k := by
  -- From Lemma 2, we have $\sum_{i=0}^{l₂-1} (f₂ i - k : ℝ) > 3ε₁k((4/3)^l₂ - 1)$.
  have h_geom_sum : ∑ i, ((f₂ i : ℝ) - k) > 3 * ε₁ * k * ((4 / 3 : ℝ) ^ l₂ - 1) := by
    -- Applying the hypothesis `hf₂_spec` to each term in the sum:
    have h_term_spec : ∀ i : Fin l₂, ((f₂ i : ℝ) - k) > ((4 / 3 : ℝ) ^ (i.val)) * ε₁ * k := by
      exact fun i => lt_tsub_iff_left.mpr ( hf₂_spec i )
    have h_geom_sum_rhs : ∑ i : Fin l₂, ((4 / 3 : ℝ) ^ (i.val)) * ε₁ * k = (3 * ε₁ * k) * ((4 / 3 : ℝ) ^ l₂ - 1) := by
      erw [ ← Finset.sum_mul _ _ _ ] ; rw [ ← Finset.sum_mul ] ; erw [ ← Finset.sum_range ] ; norm_num [ geom_sum_eq ] ; ring;
    have h_geom_sum_gt_rhs : ∑ i : Fin l₂, ((f₂ i : ℝ) - k) > ∑ i : Fin l₂, ((4 / 3 : ℝ) ^ (i.val)) * ε₁ * k := by
      apply Finset.sum_lt_sum;
      · exact fun i _ => le_of_lt ( h_term_spec i );
      · rcases l₂ <;> norm_num at *;
        · rw [ eq_comm, Nat.sub_eq_zero_iff_le ] at hl₂_def ;
          contrapose! hl₂_def;
          refine Nat.le_floor ?_;
          rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ) ] ; norm_num [ ← Real.log_inv, ← Real.log_rpow, Real.log_le_log ];
          exact Real.log_le_log ( by positivity ) ( by rw [ inv_eq_one_div, le_div_iff₀ ( by positivity ) ] ; nlinarith [ show ( k : ℝ ) ≥ 192 by norm_cast, mul_div_cancel₀ ( el₁ : ℝ ) ( by positivity : ( k : ℝ ) ≠ 0 ) ] );
        · exact ⟨ 0, h_term_spec 0 ⟩
    rw [h_geom_sum_rhs] at h_geom_sum_gt_rhs; exact_mod_cast h_geom_sum_gt_rhs;
  -- Also from Lemma 2, we have $(4/3)^l₂ \geq 9/(16ε₁)$.
  have h_exp_bound : (4 / 3 : ℝ) ^ l₂ ≥ 9 / (16 * ε₁) := by
    -- By definition of $l₂$, we know that $l₂ \geq -\frac{\log \varepsilon₁}{\log (4/3)} - 2$.
    have h_l2_ge : (l₂ : ℝ) ≥ -Real.log ε₁ / Real.log (4 / 3) - 2 := by
      rw [ hl₂_def, Nat.cast_sub ] <;> norm_num;
      · linarith [ Nat.lt_floor_add_one ( -Real.log ε₁ / Real.log ( 4 / 3 ) ) ];
      · rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ) ] ; norm_num [ ← Real.log_inv, Real.log_le_log, hε₁_pos, hε₁_lt ];
        exact Real.log_le_log ( by norm_num ) ( by rw [ inv_eq_one_div, le_div_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 192 by norm_cast, mul_div_cancel₀ ( el₁ : ℝ ) ( by positivity : ( k : ℝ ) ≠ 0 ) ] );
    -- Exponentiating both sides of $l₂ \geq -\frac{\log \varepsilon₁}{\log (4/3)} - 2$, we get $(4/3)^{l₂} \geq (4/3)^{-\frac{\log \varepsilon₁}{\log (4/3)} - 2}$.
    have h_exp_ge : (4 / 3 : ℝ) ^ l₂ ≥ (4 / 3 : ℝ) ^ (-Real.log ε₁ / Real.log (4 / 3) - 2) := by
      exact_mod_cast Real.rpow_le_rpow_of_exponent_le ( by norm_num ) h_l2_ge;
    convert h_exp_ge using 1 ; norm_num [ Real.rpow_sub, Real.rpow_natCast, Real.rpow_neg, Real.exp_neg, Real.exp_log, hε₁_pos ] ; ring_nf ; norm_num [ hε₁_pos.ne', hε₁_lt.ne' ] ;
    rw [ Real.rpow_def_of_pos ] <;> norm_num ; ring_nf ; norm_num [ hε₁_pos.ne', hε₁_lt.ne' ];
    norm_num [ mul_comm, Real.exp_neg, Real.exp_log hε₁_pos ];
  -- Substitute the exponential bound into the geometric sum inequality.
  have h_subst : ∑ i, ((f₂ i : ℝ) - k) > 3 * ε₁ * k * (9 / (16 * ε₁) - 1) := by
    exact h_geom_sum.trans_le' ( mul_le_mul_of_nonneg_left ( sub_le_sub_right h_exp_bound _ ) ( by positivity ) );
  -- Simplify the expression $3 * ε₁ * k * (9 / (16 * ε₁) - 1)$ to get $27k/16 - 3ε₁k$.
  have h_simplify : 3 * ε₁ * k * (9 / (16 * ε₁) - 1) = 27 * k / 16 - 3 * ε₁ * k := by
    grind;
  -- Since $el₁ \leq S_eseq$, we have $el₁ + \sum_{i=0}^{l₂-1} (f₂ i - k) \geq k$.
  have h_final : (el₁ : ℝ) + ∑ i, ((f₂ i : ℝ) - k) ≥ k := by
    nlinarith [ ( by norm_cast : ( 192 : ℝ ) ≤ k ), mul_div_cancel₀ ( el₁ : ℝ ) ( by positivity : ( k : ℝ ) ≠ 0 ) ];
  norm_cast at *;
  norm_num [ Int.subNatNat_of_le ( le_of_lt ( hf₂_gt _ ) ) ] at * ; linarith

-- D₁ ∪ D₂ sum bound helper
lemma D_union_sum_le
    (k : ℕ) (hk : 0 < k)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (l₁ : ℕ) (e : ℕ → ℕ)
    (he_pos : ∀ i, i ≤ l₁ → 0 < e i)
    (he_growth : ∀ i, i ≤ l₁ → 3 * e i < 2 * e (i + 1))
    (el₁_bound : (e l₁ : ℝ) ≤ ε₀ * k + 2)
    (l₂ : ℕ) (f : Fin l₂ → ℕ)
    (hf_lt : ∀ i, f i < 2 * k)
    (L_bound : ℕ) (hl₂ : l₂ ≤ L_bound)
    (hk_large : (3 * ε₀ + 9 + 2 * ↑L_bound) / ε₀ + 1 ≤ (k : ℝ))
    (D₁ : Finset ℕ) (D₂ : Finset ℕ)
    (hD₁_eq : D₁ = (Finset.range (l₁ + 1)).image (fun i => e i * (k + 1)))
    (hD₂_eq : D₂ = Finset.univ.image f)
    (hD_disj : Disjoint D₁ D₂) :
    (((D₁ ∪ D₂).sum id : ℕ) : ℝ) ≤ 4 * ε₀ * (k : ℝ) ^ 2 := by
      -- From the growth condition 3*e(i) < 2*e(i+1), by induction on l₁, Σ_{i=0}^{l₁} e(i) ≤ 3 * e(l₁).
      have h_sum_e : ∑ i ∈ Finset.range (l₁ + 1), e i ≤ 3 * e l₁ := by
        clear hD_disj hD₁_eq hD₂_eq hl₂ hk_large hf_lt el₁_bound;
        induction' l₁ with l₁ ih;
        · norm_num; linarith [ he_pos 0 bot_le ];
        · rw [ Finset.sum_range_succ ] ; linarith [ ih ( fun i hi => he_pos i ( by linarith ) ) ( fun i hi => he_growth i ( by linarith ) ), he_growth l₁ ( by linarith ) ] ;
      -- Therefore, the sum over D₁ is bounded by 3 * e(l₁) * (k + 1).
      have h_sum_D₁ : (D₁.sum id) ≤ 3 * e l₁ * (k + 1) := by
        rw [ hD₁_eq, Finset.sum_image ] <;> norm_num [ mul_comm ];
        · rw [ ← Finset.sum_mul _ _ _ ] ; nlinarith [ hk ] ;
        · -- Since $e$ is strictly increasing, if $e i = e j$, then $i = j$.
          have h_inj : StrictMonoOn e (Set.Ico 0 (l₁ + 1)) := by
            intros i hi j hj hij;
            -- By induction on $j - i$, we can show that $e i < e j$ for any $i < j$.
            induction' hij with j hj ih;
            · linarith [ he_growth i ( Nat.le_of_lt_succ hi.2 ) ];
            · linarith [ ih ⟨ Nat.zero_le _, by linarith [ Set.mem_Ico.mp hj ] ⟩, he_growth j ( by linarith [ Set.mem_Ico.mp hj ] ) ];
          exact fun i hi j hj hij => h_inj.eq_iff_eq ( by aesop ) ( by aesop ) |>.1 <| by nlinarith;
      -- Therefore, the sum over D₂ is bounded by L_bound * (2k - 1).
      have h_sum_D₂ : (D₂.sum id) ≤ L_bound * (2 * k - 1) := by
        -- Each element in D₂ is some f(i) < 2k, and D₂ has at most l₂ elements.
        have h_card_D₂ : D₂.card ≤ l₂ := by
          exact hD₂_eq ▸ Finset.card_image_le.trans ( by simp );
        exact le_trans ( Finset.sum_le_sum fun x hx => show x ≤ 2 * k - 1 from Nat.le_sub_one_of_lt <| by obtain ⟨ i, _, rfl ⟩ := Finset.mem_image.mp ( hD₂_eq ▸ hx ) ; exact hf_lt i ) ( by norm_num; nlinarith [ Nat.sub_add_cancel ( show 1 ≤ 2 * k from by linarith ) ] );
      -- Combine the bounds for D₁ and D₂.
      have h_combined : (D₁ ∪ D₂).sum id ≤ (3 * e l₁ * (k + 1)) + (L_bound * (2 * k - 1)) := by
        exact le_trans ( Finset.sum_union hD_disj |> le_of_eq ) ( add_le_add h_sum_D₁ h_sum_D₂ );
      -- Substitute the bounds for $e(l₁)$ and $L_bound$ into the combined sum.
      have h_substituted : (D₁ ∪ D₂).sum id ≤ 3 * (ε₀ * k + 2) * (k + 1) + L_bound * (2 * k - 1) := by
        refine le_trans ( Nat.cast_le.mpr h_combined ) ?_;
        norm_num [ Nat.cast_sub ( show 1 ≤ 2 * k from by linarith ) ] ; nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ k ) ] ;
      rw [ div_add_one, div_le_iff₀ ] at hk_large <;> nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ k ) ]

/-- Given k ∈ C₁ with the right properties, construct the set D
with all required properties. -/
lemma D_set_construction
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N}))
    (α : ℚ) (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀_lt : ε₀ < 1/3) :
    ∀ᶠ (m : ℕ) in atTop,
    ∀ (k : ℕ),
    0 < k →
    (m : ℝ) < (k : ℝ) →
    (k : ℝ) < (m : ℝ) * Real.exp (α : ℝ) →
    Nat.Coprime k 210 →
    IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 12)) (k + 1) →
    (1 - ε₀) * (m : ℝ) * Real.exp (α : ℝ) < (k : ℝ) →
    ∀ (β : ℚ), 0 < β → (β : ℝ) ≤ 1 →
    ((↑(⌊-Real.log (ε₀ / 2) / Real.log (4/3 : ℝ)⌋₊) + 4 : ℝ) ≤ (β : ℝ) * (↑k : ℝ)) →
    IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β.den →
    ∃ D : Finset ℕ,
      (∀ d ∈ D, k < d ∧ ¬(k ∣ d)) ∧
      D_multiplier_injective D ∧
      (∀ r : ℕ, r < k → ∃ D₂ : Finset ℕ, D₂ ⊆ D ∧ D₂.sum id % k = r) ∧
      (let β' := β - D.sum (fun d => (1 : ℚ) / (12 * d))
       0 < β' ∧
       (β : ℝ) / 2 < (β'.num.toNat : ℝ) / (β'.den : ℝ) ∧
       IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β'.den) ∧
      ((D.sum id : ℕ) : ℝ) ≤ 4 * ε₀ * (↑k) ^ 2 := by
  have h_e_growth := e_seq_growth_eventually smooth_arith
  have h_e_unbounded := e_seq_bounded_unbounded smooth_arith
  have h_J_elements := J_interval_elements smooth_arith ε₀ hε₀ hε₀_lt
  have h_e_growth_all := e_seq_growth_all smooth_arith
  set L_bound := ⌊-Real.log (ε₀ / 2) / Real.log (4/3 : ℝ)⌋₊ with hL_bound_def
  filter_upwards [Filter.eventually_ge_atTop (max 2 (max ⌈Real.exp (α : ℝ)⌉₊ (max ⌈2 / ε₀⌉₊ (max ⌈ε₀ * Real.exp (α : ℝ) + 2⌉₊ (max ⌈(3 * ε₀ + 9 + 2 * L_bound) / ε₀ + 1⌉₊ ⌈(4 : ℝ) ^ 30⌉₊))))),
                  h_e_growth, h_e_unbounded, h_J_elements, h_e_growth_all] with m hm_ge hgrowth hunbound hJ hgrowth_all
  have hm_ge_2 : 2 ≤ m := by omega
  have hm_ge_ceil_exp : ⌈Real.exp (α : ℝ)⌉₊ ≤ m := by omega
  have hm_ge_ceil_eps : ⌈2 / ε₀⌉₊ ≤ m := by omega
  have hm_ge_ceil_eα : ⌈ε₀ * Real.exp (α : ℝ) + 2⌉₊ ≤ m := by omega
  have hm_ge_sum_bound : ⌈(3 * ε₀ + 9 + 2 * ↑L_bound) / ε₀ + 1⌉₊ ≤ m := by omega
  have hm_ge_ps_bound : ⌈(4 : ℝ) ^ 30⌉₊ ≤ m := by omega
  have hm_ge_exp : Real.exp (α : ℝ) ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hm_ge_ceil_exp)
  have hm_ge_eps : (2 / ε₀ : ℝ) ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm_ge_ceil_eps)
  have hm_ge_eα : ε₀ * Real.exp (α : ℝ) + 2 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm_ge_ceil_eα)
  intro k hk_pos hm_lt_k hk_lt_meα hk_cop hk_ps hk_large β hβ_pos hβ_le_1 hβ_recip hβ_ps
  set x := (m : ℝ) ^ ((1 : ℝ) / 12) with hx_def
  have hx_ge_1 : 1 ≤ x := by
    rw [hx_def]; exact Real.one_le_rpow
      (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  set T_val : ℕ := 2 * ⌈ε₀ / 2 * (k : ℝ)⌉₊ with hT_val_def
  have hk_pos_real : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  have heps_k_pos : (0 : ℝ) < ε₀ / 2 * (k : ℝ) := by positivity
  have hT : 2 ≤ T_val := by
    rw [hT_val_def]
    have : 1 ≤ ⌈ε₀ / 2 * (k : ℝ)⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      intro h0; simp at h0; linarith)
    omega
  have hT_le_m2 : (T_val : ℝ) ≤ (m : ℝ) ^ 2 := by
    rw [hT_val_def]; push_cast
    have hceil_le : (⌈ε₀ / 2 * (k : ℝ)⌉₊ : ℝ) ≤ ε₀ / 2 * (k : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity) |>.le
    have hk_lt : (k : ℝ) < (m : ℝ) * Real.exp (α : ℝ) := hk_lt_meα
    have h_eα_le_m : ε₀ * Real.exp (α : ℝ) ≤ (m : ℝ) - 2 := by linarith [hm_ge_eα]
    have h_m_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have : ε₀ * (k : ℝ) < ε₀ * ((m : ℝ) * Real.exp (α : ℝ)) := by nlinarith
    have : ε₀ * ((m : ℝ) * Real.exp (α : ℝ)) ≤ (m : ℝ) * ((m : ℝ) - 2) := by nlinarith
    have : (m : ℝ) * ((m : ℝ) - 2) ≤ (m : ℝ) ^ 2 - 2 := by nlinarith
    nlinarith
  obtain ⟨l₁, hl₁_ge, hl₁_lt⟩ := e_seq_reaches_interval x hx_ge_1
    T_val hT (hunbound T_val hT hT_le_m2)
  have hl₁_ge' : ⌈ε₀ / 2 * (k : ℝ)⌉₊ ≤ e_seq x l₁ := by
    have : T_val / 2 = ⌈ε₀ / 2 * (k : ℝ)⌉₊ := by
      rw [hT_val_def]; exact Nat.mul_div_cancel_left _ (by norm_num)
    omega
  have hk_le_m2 : (k : ℝ) ≤ (m : ℝ) ^ 2 := le_of_lt (calc
    (k : ℝ) < (m : ℝ) * Real.exp (α : ℝ) := hk_lt_meα
    _ ≤ (m : ℝ) * (m : ℝ) := by nlinarith [hm_ge_exp]
    _ = (m : ℝ) ^ 2 := by ring)
  set el₁ := e_seq x l₁ with hel₁_def
  have hel₁_pos : 0 < el₁ := e_seq_pos x hx_ge_1 l₁
  set ε₁ : ℝ := (el₁ : ℝ) / (k : ℝ) with hε₁_def
  have hε₁_pos : 0 < ε₁ := div_pos (Nat.cast_pos.mpr hel₁_pos) hk_pos_real
  have hε₁_lt_one : ε₁ < 1 := by
    rw [hε₁_def, div_lt_one hk_pos_real]
    have hT_le_k : T_val ≤ k := by
      rw [hT_val_def]
      have : (⌈ε₀ / 2 * (k : ℝ)⌉₊ : ℝ) ≤ ε₀ / 2 * (k : ℝ) + 1 :=
        Nat.ceil_lt_add_one (by positivity) |>.le
      have : (2 * ⌈ε₀ / 2 * (k : ℝ)⌉₊ : ℝ) ≤ ε₀ * (k : ℝ) + 2 := by nlinarith
      have hk_ge_3 : (3 : ℝ) ≤ (k : ℝ) := by
        have : m < k := by exact_mod_cast hm_lt_k
        exact_mod_cast (show 3 ≤ k by omega)
      have : ε₀ * (k : ℝ) + 2 ≤ (k : ℝ) := by nlinarith [hε₀_lt]
      exact_mod_cast show (2 * ⌈ε₀ / 2 * (k : ℝ)⌉₊ : ℝ) ≤ (k : ℝ) by linarith
    exact_mod_cast lt_of_lt_of_le hl₁_lt (by exact_mod_cast hT_le_k)
  have hε₁_ge : ε₀ / 2 ≤ ε₁ := eps1_lower_bound el₁ k hk_pos ε₀ hε₀ hl₁_ge'
  set l₂ : ℕ := ⌊-Real.log ε₁ / Real.log (4/3 : ℝ)⌋₊ - 1 with hl₂_def
  let D₁ : Finset ℕ := (Finset.range (l₁ + 1)).image (fun i => e_seq x i * (k + 1))
  have hJ_each : ∀ i : ℕ, i < l₂ →
      ∃ N : ℕ, (k : ℝ) + ((4:ℝ)/3)^i * ε₁ * (k : ℝ) < (N : ℝ) ∧
        (N : ℝ) < (k : ℝ) + ((4:ℝ)/3)^(i+1) * ε₁ * (k : ℝ) ∧
        Nat.Coprime N 210 ∧ IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 6)) N := by
    intro i hi
    have hi' : i + 1 < ⌊-Real.log ε₁ / Real.log (4/3 : ℝ)⌋₊ := by omega
    apply hJ k hk_pos hk_cop (by linarith [hm_lt_k]) hk_le_m2
    · linarith [mul_pos (pow_pos (by norm_num : (0:ℝ) < 4/3) i) (mul_pos hε₁_pos hk_pos_real)]
    · have h_pow := pow_43_eps_lt_one ε₁ hε₁_pos hε₁_lt_one i hi'
      nlinarith
    · have h43_pos : (0:ℝ) < (4:ℝ)/3 := by norm_num
      have h_diff : 0 < ((4:ℝ)/3)^(i+1) * ε₁ * (k:ℝ) - ((4:ℝ)/3)^i * ε₁ * (k:ℝ) := by
        have : ((4:ℝ)/3)^(i+1) = ((4:ℝ)/3)^i * (4/3) := pow_succ _ _
        rw [this]
        nlinarith [pow_pos h43_pos i, mul_pos hε₁_pos hk_pos_real]
      linarith
    · exact J_ratio_ge ε₀ ε₁ hε₀ hε₁_pos hε₁_ge hε₁_lt_one k hk_pos i
        (pow_43_eps_lt_one ε₁ hε₁_pos hε₁_lt_one i hi')
  have hf₂ : ∀ i : Fin l₂, ∃ N : ℕ,
      (k : ℝ) + ((4:ℝ)/3)^(i : ℕ) * ε₁ * (k : ℝ) < (N : ℝ) ∧
      (N : ℝ) < (k : ℝ) + ((4:ℝ)/3)^((i : ℕ)+1) * ε₁ * (k : ℝ) ∧
      Nat.Coprime N 210 ∧ IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 6)) N :=
    fun ⟨i, hi⟩ => hJ_each i hi
  let f₂ : Fin l₂ → ℕ := fun i => (hf₂ i).choose
  let D₂ : Finset ℕ := Finset.univ.image f₂
  have hf₂_spec : ∀ i : Fin l₂,
      (k : ℝ) + ((4:ℝ)/3)^(i : ℕ) * ε₁ * (k : ℝ) < (f₂ i : ℝ) ∧
      (f₂ i : ℝ) < (k : ℝ) + ((4:ℝ)/3)^((i : ℕ)+1) * ε₁ * (k : ℝ) ∧
      Nat.Coprime (f₂ i) 210 ∧ IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 6)) (f₂ i) :=
    fun i => (hf₂ i).choose_spec
  have hel₁_lt_k : el₁ < k := by
    have : ε₁ < 1 := hε₁_lt_one
    rw [hε₁_def, div_lt_one hk_pos_real] at this
    exact_mod_cast this
  have hel_lt_k : ∀ j, j ≤ l₁ → e_seq x j < k := by
    intro j hj
    exact lt_of_le_of_lt (e_seq_mono x hx_ge_1 hj) (by rw [← hel₁_def]; exact hel₁_lt_k)
  have hf₂_gt_k : ∀ i : Fin l₂, k < f₂ i := by
    intro i
    have h := (hf₂_spec i).1
    have : (k : ℝ) < (f₂ i : ℝ) := by linarith [mul_pos (pow_pos (by norm_num : (0:ℝ) < 4/3) (i : ℕ)) (mul_pos hε₁_pos hk_pos_real)]
    exact_mod_cast this
  have hf₂_lt_2k : ∀ i : Fin l₂, f₂ i < 2 * k := by
    intro i
    have hi' : (i : ℕ) + 1 < ⌊-Real.log ε₁ / Real.log (4/3 : ℝ)⌋₊ := by omega
    have h_pow := pow_43_eps_lt_one ε₁ hε₁_pos hε₁_lt_one (i : ℕ) hi'
    have := (hf₂_spec i).2.1
    have : (f₂ i : ℝ) < (k : ℝ) + 1 * (k : ℝ) := by nlinarith
    exact_mod_cast show (f₂ i : ℝ) < 2 * (k : ℝ) by linarith
  -- Property 1: elements > k and not divisible by k
  have hD_range : ∀ d ∈ D₁ ∪ D₂, k < d ∧ ¬(k ∣ d) := by
    intro d hd
    rcases Finset.mem_union.mp hd with hd₁ | hd₂
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd₁
      have hj' := Finset.mem_range.mp hj
      have he_pos := e_seq_pos x hx_ge_1 j
      constructor
      · calc k < k + 1 := by omega
          _ ≤ e_seq x j * (k + 1) := Nat.le_mul_of_pos_left _ he_pos
      · intro hdvd
        have he_lt_k := hel_lt_k j (by omega)
        have he_pos' := he_pos
        have : k ∣ e_seq x j := by
          rwa [show e_seq x j * (k + 1) = e_seq x j * k + e_seq x j by ring,
            Nat.dvd_add_right (dvd_mul_left k _)] at hdvd
        exact absurd (Nat.le_of_dvd he_pos this) (not_le.mpr he_lt_k)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd₂
      constructor
      · exact hf₂_gt_k i
      · intro hdvd
        have hgt := hf₂_gt_k i
        have hlt := hf₂_lt_2k i
        have h1 : f₂ i / k = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        have h2 : f₂ i = k * (f₂ i / k) := by rw [Nat.mul_div_cancel' hdvd]
        rw [h1] at h2; omega
  -- D₁ elements have 3/2 growth (needed for multiplier injectivity)
  have hD1_growth : ∀ j, j ≤ l₁ → 3 * e_seq x j < 2 * e_seq x (j + 1) := by
    intro j hj
    apply hgrowth_all j
    have := hel_lt_k j hj
    exact_mod_cast show (e_seq x j : ℝ) ≤ (m : ℝ) ^ 2 by
      exact le_trans (by exact_mod_cast le_of_lt this) hk_le_m2
  -- For distinct D₁ elements, 3*d₁ < 2*d₂ (from growth and monotonicity)
  have hD1_32 : ∀ a b, a ≤ l₁ → b ≤ l₁ → e_seq x a < e_seq x b →
      3 * (e_seq x a * (k + 1)) < 2 * (e_seq x b * (k + 1)) := by
    intro a b ha hb hab
    have hab_idx : a < b := by
      by_contra h; push_neg at h
      exact absurd (e_seq_mono x hx_ge_1 h) (not_le.mpr hab)
    have : 3 * e_seq x a < 2 * e_seq x b := by
      calc 3 * e_seq x a < 2 * e_seq x (a + 1) := hD1_growth a ha
        _ ≤ 2 * e_seq x b := Nat.mul_le_mul_left 2 (e_seq_mono x hx_ge_1 (by omega))
    nlinarith
  -- Property 2: multiplier injectivity
  have hD_inj : D_multiplier_injective (D₁ ∪ D₂) := by
    intro d₁ hd₁ d₂ hd₂ c₁ hc₁ c₂ hc₂ heq
    rcases Finset.mem_union.mp hd₁ with hd₁_in | hd₁_in <;>
    rcases Finset.mem_union.mp hd₂ with hd₂_in | hd₂_in
    · -- Both in D₁
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd₁_in
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd₂_in
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      by_cases hab : e_seq x a = e_seq x b
      · constructor
        · have hd_eq : e_seq x a * (k + 1) = e_seq x b * (k + 1) := by rw [hab]
          rw [hd_eq] at heq
          exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (e_seq_pos x hx_ge_1 b) (by omega)) heq
        · exact congr_arg (· * (k + 1)) hab
      · exfalso
        rcases lt_or_gt_of_ne hab with h | h
        · exact mult_inj_32_growth hc₁ hc₂
            (by nlinarith [e_seq_pos x hx_ge_1 a]) (hD1_32 a b (by omega) (by omega) h) heq
        · exact mult_inj_32_growth hc₂ hc₁
            (by nlinarith [e_seq_pos x hx_ge_1 b]) (hD1_32 b a (by omega) (by omega) h) heq.symm
    · -- d₁ in D₁, d₂ in D₂
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd₁_in
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd₂_in
      have ha' := Finset.mem_range.mp ha
      exact mult_inj_mixed k hk_pos (by omega) _ _ c₁ c₂ hc₁ hc₂
        ⟨e_seq x a, e_seq_pos x hx_ge_1 a, hel_lt_k a (by omega), rfl⟩
        (hf₂_spec i).2.2.1 (hf₂_gt_k i) (hf₂_lt_2k i) heq
    · -- d₁ in D₂, d₂ in D₁
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd₁_in
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd₂_in
      have hb' := Finset.mem_range.mp hb
      have h := mult_inj_mixed k hk_pos (by omega) _ _ c₂ c₁ hc₂ hc₁
        ⟨e_seq x b, e_seq_pos x hx_ge_1 b, hel_lt_k b (by omega), rfl⟩
        (hf₂_spec i).2.2.1 (hf₂_gt_k i) (hf₂_lt_2k i) heq.symm
      exact ⟨h.1.symm, h.2.symm⟩
    · -- Both in D₂: coprime to 210
      have hD2_cop : ∀ d ∈ D₂, Nat.Coprime d 210 := by
        intro d hd
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
        exact (hf₂_spec i).2.2.1
      have hD2_pos : ∀ d ∈ D₂, 0 < d := by
        intro d hd
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
        exact lt_trans hk_pos (hf₂_gt_k i)
      exact mult_inj_coprime_210 D₂ hD2_cop hD2_pos _ hd₁_in _ hd₂_in c₁ hc₁ c₂ hc₂ heq
  have hD_cover : ∀ r : ℕ, r < k → ∃ D₂' : Finset ℕ, D₂' ⊆ D₁ ∪ D₂ ∧ D₂'.sum id % k = r := by
    have hk2 : 1 < k := by
      have : m < k := by exact_mod_cast hm_lt_k
      omega
    -- e_seq strict mono on [0, l₁]
    have he_smono : ∀ j, j < l₁ → e_seq x j < e_seq x (j + 1) := by
      intro j hj
      have := hD1_growth j (by omega)
      have := e_seq_pos x hx_ge_1 j
      omega
    -- e_seq doubling property
    have he_le_d : ∀ j, j ≤ l₁ → e_seq x (j + 1) ≤ 2 * e_seq x j :=
      fun j hj => e_seq_le_double x hx_ge_1 j
    -- e_seq injectivity from strict mono
    have he_smono' : StrictMonoOn (e_seq x) (Set.Iic l₁) := by
      intro a (ha : a ≤ l₁) b (hb : b ≤ l₁) hab
      suffices h : ∀ n, n ≤ l₁ → a < n → e_seq x a < e_seq x n by exact h b hb hab
      intro n hn han
      induction n with
      | zero => omega
      | succ n ih =>
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp han) with rfl | hlt
        · exact he_smono a (by omega)
        · exact lt_trans (ih (by omega) hlt) (he_smono n (by omega))
    have he_inj : ∀ a b, a ≤ l₁ → b ≤ l₁ → e_seq x a = e_seq x b → a = b := by
      intro a b ha hb hab
      by_contra h
      rcases lt_or_gt_of_ne h with h | h
      · exact absurd hab (ne_of_lt (he_smono' ha hb h))
      · exact absurd hab.symm (ne_of_lt (he_smono' hb ha h))
    -- f₂ residue strict mono
    have hf_res_mono : StrictMono (fun i : Fin l₂ => f₂ i - k) := by
      intro i j hij
      have hi_spec := hf₂_spec i
      have hj_spec := hf₂_spec j
      have hi_val : (i : ℕ) < (j : ℕ) := hij
      have : ((4:ℝ)/3)^((i : ℕ)+1) ≤ ((4:ℝ)/3)^(j : ℕ) :=
        pow_le_pow_right₀ (by norm_num : 1 ≤ (4:ℝ)/3) (by omega)
      have hfi_lt : (f₂ i : ℝ) < (k : ℝ) + ((4:ℝ)/3)^((i : ℕ)+1) * ε₁ * (k : ℝ) := hi_spec.2.1
      have hfj_gt : (k : ℝ) + ((4:ℝ)/3)^(j : ℕ) * ε₁ * (k : ℝ) < (f₂ j : ℝ) := hj_spec.1
      have hfij : (f₂ i : ℝ) < (f₂ j : ℝ) := by nlinarith [mul_pos hε₁_pos hk_pos_real]
      show (fun i : Fin l₂ => f₂ i - k) i < (fun i : Fin l₂ => f₂ i - k) j
      simp only
      have h1 : f₂ i < f₂ j := by exact_mod_cast hfij
      have h2 : k < f₂ i := hf₂_gt_k i
      omega
    -- f₂ residue gap
    have hf_res_gap : ∀ (i : Fin l₂), (i : ℕ) ≥ 1 →
        f₂ i - k ≤ 2 * (f₂ ⟨(i : ℕ) - 1, by omega⟩ - k) := by
      intro i hi
      have hi_spec := hf₂_spec i
      have him1_spec := hf₂_spec ⟨(i : ℕ) - 1, by omega⟩
      have hfi_lt : (f₂ i : ℝ) < (k : ℝ) + ((4:ℝ)/3)^((i : ℕ)+1) * ε₁ * (k : ℝ) := hi_spec.2.1
      have hfm_gt : (k : ℝ) + ((4:ℝ)/3)^((i : ℕ) - 1) * ε₁ * (k : ℝ) < (f₂ ⟨(i : ℕ) - 1, by omega⟩ : ℝ) :=
        him1_spec.1
      have h43 : ((4:ℝ)/3)^((i : ℕ)+1) ≤ 2 * ((4:ℝ)/3)^((i : ℕ) - 1) := by
        rw [show (i : ℕ) + 1 = ((i : ℕ) - 1) + 2 from by omega]
        rw [pow_add]
        have : ((4:ℝ)/3)^2 = 16/9 := by norm_num
        rw [this]
        nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 4/3) ((i : ℕ) - 1)]
      have hfi_sub : (f₂ i : ℝ) - (k : ℝ) ≤ 2 * ((f₂ ⟨(i : ℕ) - 1, by omega⟩ : ℝ) - (k : ℝ)) := by
        nlinarith [mul_pos hε₁_pos hk_pos_real]
      have hfi_k : k ≤ f₂ i := le_of_lt (hf₂_gt_k i)
      have hfm_k : k ≤ f₂ ⟨(i : ℕ) - 1, by omega⟩ := le_of_lt (hf₂_gt_k _)
      have h1 : (f₂ i - k : ℝ) = ((f₂ i - k : ℕ) : ℝ) := by
        rw [Nat.cast_sub hfi_k]
      have h2 : (f₂ ⟨(i : ℕ) - 1, by omega⟩ - k : ℝ) = ((f₂ ⟨(i : ℕ) - 1, by omega⟩ - k : ℕ) : ℝ) := by
        rw [Nat.cast_sub hfm_k]
      rw [h1, h2] at hfi_sub; exact_mod_cast hfi_sub
    -- first f₂ residue ≤ 2 * el₁
    have hf_first_le : ∀ (h : 0 < l₂), f₂ ⟨0, h⟩ - k ≤ 2 * e_seq x l₁ := by
      intro hl₂_pos
      have h0_spec := hf₂_spec ⟨0, hl₂_pos⟩
      have hf0_lt : (f₂ ⟨0, hl₂_pos⟩ : ℝ) < (k : ℝ) + ((4:ℝ)/3) * ε₁ * (k : ℝ) := by
        have := h0_spec.2.1; simp only at this; linarith [pow_succ ((4:ℝ)/3) 0]
      have hεk : ε₁ * (k : ℝ) ≤ (el₁ : ℝ) := by
        rw [hε₁_def, div_mul_cancel₀ (el₁ : ℝ) (ne_of_gt hk_pos_real)]
      have hf0_bound : (f₂ ⟨0, hl₂_pos⟩ : ℝ) < (k : ℝ) + 2 * (el₁ : ℝ) := by nlinarith
      have hf0_nat : f₂ ⟨0, hl₂_pos⟩ < k + 2 * el₁ := by exact_mod_cast hf0_bound
      have hf0_k_nat : k ≤ f₂ ⟨0, hl₂_pos⟩ := le_of_lt (hf₂_gt_k _)
      rw [← hel₁_def]; omega
    -- el₁ < f₂(0) - k
    have he_lt_f : ∀ (h : 0 < l₂), e_seq x l₁ < f₂ ⟨0, h⟩ - k := by
      intro hl₂_pos
      have h0_spec := hf₂_spec ⟨0, hl₂_pos⟩
      have hf0_gt : (k : ℝ) + 1 * ε₁ * (k : ℝ) < (f₂ ⟨0, hl₂_pos⟩ : ℝ) := by simpa using h0_spec.1
      have hel_eq : (el₁ : ℝ) = ε₁ * (k : ℝ) := by rw [hε₁_def]; field_simp
      have hel_lt : (el₁ : ℝ) + (k : ℝ) < (f₂ ⟨0, hl₂_pos⟩ : ℝ) := by nlinarith
      have hel_nat : el₁ + k < f₂ ⟨0, hl₂_pos⟩ := by exact_mod_cast hel_lt
      rw [← hel₁_def]; omega
    -- sum ≥ k (follows from β * k ≥ L_bound + 4 ≥ l₁ + l₂ + 4, and complete sum dominance)
    have hsum_ge : (Finset.range (l₁ + 1)).sum (e_seq x) +
        (Finset.univ : Finset (Fin l₂)).sum (fun i => f₂ i - k) ≥ k := by
      -- e_seq sum ≥ el₁ (last term is at least el₁)
      have he_sum_ge : el₁ ≤ (Finset.range (l₁ + 1)).sum (e_seq x) :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      have hf_res_lower : ∀ (i : Fin l₂),
          (f₂ i - k : ℕ) ≥ 1 := by
        intro i; have := hf₂_gt_k i; omega
      have hf_sum_ge : l₂ ≤ (Finset.univ : Finset (Fin l₂)).sum (fun i => f₂ i - k) :=
        le_trans (by simp) (Finset.sum_le_sum (fun i _ => hf_res_lower i))
      have hk_192 : (192 : ℕ) ≤ k := by
        have : m < k := by exact_mod_cast hm_lt_k
        have : (192 : ℕ) ≤ m := le_trans (by exact_mod_cast le_trans (by norm_num : (192 : ℝ) ≤ (4 : ℝ) ^ 30) (Nat.le_ceil _)) hm_ge_ps_bound
        omega
      have hel_upper : (el₁ : ℝ) ≤ ε₀ * (k : ℝ) + 2 := by
        have hlt : el₁ < T_val := hl₁_lt
        have hceil : (⌈ε₀ / 2 * (↑k : ℝ)⌉₊ : ℝ) ≤ ε₀ / 2 * ↑k + 1 :=
          Nat.ceil_lt_add_one (by positivity) |>.le
        have hT_real : (T_val : ℝ) ≤ ε₀ * ↑k + 2 := by rw [hT_val_def]; push_cast; nlinarith
        linarith [show (↑el₁ : ℝ) < ↑T_val from by exact_mod_cast hlt]
      exact geom_residue_sum_ge_k k hk_pos el₁ ε₀ hε₀ hε₀_lt ε₁ hε₁_pos hε₁_lt_one
        hε₁_def l₂ hl₂_def f₂ hf₂_gt_k
        (fun i => (hf₂_spec i).1)
        ((Finset.range (l₁ + 1)).sum (e_seq x)) he_sum_ge hk_192 hel_upper
    -- f₂ injectivity from strict mono on residues
    have hf₂_inj : Function.Injective f₂ := by
      intro i j hij
      have := hf_res_mono.injective (show f₂ i - k = f₂ j - k by omega)
      exact this
    exact D_cover_combined k hk2 l₁ (e_seq x)
      (fun j hj => e_seq_pos x hx_ge_1 j)
      (e_seq_zero x)
      he_le_d he_smono hel_lt_k l₂ f₂
      hf₂_gt_k hf₂_lt_2k hf_first_le hf_res_mono hf_res_gap he_lt_f
      hsum_ge D₁ rfl D₂ rfl he_inj hf₂_inj
  have hD_beta : (let β' := β - (D₁ ∪ D₂).sum (fun d => (1 : ℚ) / (12 * d))
       0 < β' ∧
       (β : ℝ) / 2 < (β'.num.toNat : ℝ) / (β'.den : ℝ) ∧
       IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β'.den) := by
    set S := (D₁ ∪ D₂).sum (fun d => (1 : ℚ) / (12 * d)) with hS_def
    set β' := β - S
    -- S is nonneg
    have hS_nn : (0 : ℚ) ≤ S :=
      Finset.sum_nonneg (fun d _ => by positivity)
    -- Bound S < β/2 using hβ_recip
    have hl₂_le' : l₂ ≤ L_bound := by
      rw [hl₂_def, hL_bound_def]
      have : ⌊-Real.log ε₁ / Real.log (4/3 : ℝ)⌋₊ ≤ ⌊-Real.log (ε₀ / 2) / Real.log (4/3 : ℝ)⌋₊ :=
        Nat.floor_mono (div_le_div_of_nonneg_right
          (neg_le_neg (Real.log_le_log (by linarith) hε₁_ge))
          (Real.log_nonneg (by norm_num)))
      omega
    have hS_lt : (S : ℝ) < (β : ℝ) / 2 :=
      recip_12d_sum_lt_half_beta k hk_pos l₁ (e_seq x)
        (fun i _ => e_seq_pos x hx_ge_1 i) hD1_growth l₂ f₂
        (fun i => hf₂_gt_k i)
        L_bound hl₂_le' β hβ_pos hβ_recip D₁ D₂ rfl rfl
    -- β' > 0
    have hβ'_pos : 0 < β' := by
      have h1 : (S : ℝ) < (β : ℝ) := lt_of_lt_of_le hS_lt (half_le_self (le_of_lt (Rat.cast_pos.mpr hβ_pos)))
      exact sub_pos.mpr (by exact_mod_cast h1)
    -- β/2 < β'.num.toNat/β'.den from rat_pos_Croot_input
    have h_rat := rat_pos_Croot_input β' hβ'_pos
    have hβ'_half : (β : ℝ) / 2 < (β'.num.toNat : ℝ) / (β'.den : ℝ) := by
      have h1 : (β' : ℝ) / 2 < (β'.num.toNat : ℝ) / (β'.den : ℝ) := h_rat.2.2.1
      have h2 : (β'.num.toNat : ℝ) / (β'.den : ℝ) ≤ (β' : ℝ) := h_rat.2.2.2
      have h3 : (β : ℝ) / 2 < (β' : ℝ) := by
        have : (β' : ℝ) = (β : ℝ) - (S : ℝ) := by simp only [β']; push_cast; ring
        linarith
      -- β'.num.toNat / β'.den = β' for positive rationals
      have h4 : (β'.num.toNat : ℝ) / (β'.den : ℝ) = (β' : ℝ) := by
        rw [Rat.cast_def]
        congr 1
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (le_of_lt hβ'_pos))
      linarith
    -- Powersmoothness of β'.den
    have hβ'_ps : IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β'.den := by
      have hD_pos : ∀ d ∈ D₁ ∪ D₂, 0 < d := by
        intro d hd
        rcases Finset.mem_union.mp hd with h | h
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
          exact Nat.mul_pos (e_seq_pos x hx_ge_1 j) (by omega)
        · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
          exact lt_trans hk_pos (hf₂_gt_k i)
      -- Each 12d is m^(1/5)-ps: for D₁ elements e_seq(j)*(k+1), both factors are m^(1/12)-ps;
      -- for D₂ elements f₂(i), they are m^(1/6)-ps. Factor 12 = 2²*3 adds prime powers 4,3.
      -- For large m, p^{v_p(12*d)} = p^{v_p(12)} * p^{v_p(d)} ≤ 4 * m^(1/6) ≤ m^(1/5).
      have hD_ps : ∀ d ∈ D₁ ∪ D₂, IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) (12 * d) := by
        intro d hd
        rcases Finset.mem_union.mp hd with hmem | hmem
        · -- D₁: 12*(e_seq(j)*(k+1)) is m^(1/5)-ps
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hmem
          have hj' := Finset.mem_range.mp hj
          show IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) (12 * (e_seq x j * (k + 1)))
          rw [show 12 * (e_seq x j * (k + 1)) = 12 * e_seq x j * (k + 1) from by ring]
          exact IsPowersmooth_mul_three
              isPowersmooth_4_12
              (e_seq_ps x hx_ge_1 j)
              hk_ps
              (ps_bound_12_two_twelfths m hm_ge_ps_bound)
              (by norm_num)
              (Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num))
              (by norm_num)
              (e_seq_pos x hx_ge_1 j)
              (by omega)
        · -- D₂: 12*f₂(i) is m^(1/5)-ps
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
          exact ps_12_times_sixth
            (lt_trans hk_pos (hf₂_gt_k i))
            hm_ge_ps_bound
            ((hf₂_spec i).2.2.2)
      exact beta_sub_recip_den_ps m (D₁ ∪ D₂) hD_ps β
        hβ_ps β' rfl hβ'_pos
    exact ⟨hβ'_pos, hβ'_half, hβ'_ps⟩
  have hD_sum : (((D₁ ∪ D₂).sum id : ℕ) : ℝ) ≤ 4 * ε₀ * (↑k) ^ 2 := by
    have hD_disj : Disjoint D₁ D₂ := by
      rw [Finset.disjoint_left]
      intro d hd₁ hd₂
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd₁
      obtain ⟨i, _, heq_fi⟩ := Finset.mem_image.mp hd₂
      have hj' := Finset.mem_range.mp hj
      have he_pos_j := e_seq_pos x hx_ge_1 j
      by_cases hj1 : e_seq x j ≥ 2
      · have h1 : e_seq x j * (k + 1) ≥ 2 * (k + 1) := Nat.mul_le_mul_right _ hj1
        have h2 : f₂ i < 2 * k := hf₂_lt_2k i
        omega
      · push_neg at hj1
        have hej1 : e_seq x j = 1 := by omega
        have hel₁_ge_1 : 1 ≤ el₁ := by
          exact le_trans (Nat.one_le_iff_ne_zero.mpr (by intro h; simp at h; linarith)) hl₁_ge'
        have hfi_gt : f₂ i > k + 1 := by
          have h1 := (hf₂_spec i).1
          have h2 : ((4:ℝ)/3)^(i : ℕ) ≥ 1 := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4/3)
          have h3 : ε₁ * ↑k = ↑el₁ := by rw [hε₁_def]; field_simp
          have h4 : (f₂ i : ℝ) > ↑k + ↑el₁ := by nlinarith
          have h5 : (↑k : ℝ) + ↑el₁ ≥ ↑k + 1 := by exact_mod_cast (show k + el₁ ≥ k + 1 by omega)
          have : (f₂ i : ℝ) > ↑k + 1 := by linarith
          exact_mod_cast (show f₂ i > k + 1 by exact_mod_cast show (↑(f₂ i) : ℝ) > ↑(k + 1) by push_cast; linarith)
        rw [hej1, one_mul] at heq_fi
        omega
    have hel₁_le : (↑el₁ : ℝ) ≤ ε₀ * ↑k + 2 := by
      have hlt : el₁ < T_val := hl₁_lt
      have hceil : (⌈ε₀ / 2 * (↑k : ℝ)⌉₊ : ℝ) ≤ ε₀ / 2 * ↑k + 1 :=
        Nat.ceil_lt_add_one (by positivity) |>.le
      have hT_real : (T_val : ℝ) ≤ ε₀ * ↑k + 2 := by rw [hT_val_def]; push_cast; nlinarith
      linarith [show (↑el₁ : ℝ) < ↑T_val from by exact_mod_cast hlt]
    have hl₂_le : l₂ ≤ L_bound := by
      rw [hl₂_def, hL_bound_def]
      have : ⌊-Real.log ε₁ / Real.log (4/3 : ℝ)⌋₊ ≤ ⌊-Real.log (ε₀ / 2) / Real.log (4/3 : ℝ)⌋₊ :=
        Nat.floor_mono (div_le_div_of_nonneg_right
          (neg_le_neg (Real.log_le_log (by linarith) hε₁_ge))
          (Real.log_nonneg (by norm_num)))
      omega
    have hk_large_enough : (3 * ε₀ + 9 + 2 * ↑L_bound) / ε₀ + 1 ≤ (↑k : ℝ) := by
      have h1 : (3 * ε₀ + 9 + 2 * ↑L_bound) / ε₀ + 1 ≤ (↑m : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hm_ge_sum_bound)
      have h2 : (↑m : ℝ) < (↑k : ℝ) := by exact_mod_cast hm_lt_k
      linarith
    exact D_union_sum_le k hk_pos ε₀ hε₀ l₁ (e_seq x)
      (fun i _ => e_seq_pos x hx_ge_1 i)
      (fun i hi => hD1_growth i hi)
      hel₁_le l₂ f₂ (fun i => hf₂_lt_2k i) L_bound hl₂_le hk_large_enough
      D₁ D₂ rfl rfl hD_disj
  exact ⟨D₁ ∪ D₂, hD_range, hD_inj, hD_cover, hD_beta, hD_sum⟩

/-- Combining the D and k construction. -/
lemma D_and_k_construction
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N}))
    (α : ℚ) (hα : 0 < α) (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀_lt : ε₀ < 1/3) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ᶠ (m : ℕ) in atTop,
    ∀ (C₁ : Finset ℕ) (β : ℚ),
    (∀ a ∈ C₁, (m : ℝ) < (a : ℝ) ∧ (a : ℝ) < (m : ℝ) * Real.exp (α : ℝ)) →
    β = α - C₁.sum (fun a => (1 : ℚ) / (a : ℚ)) →
    0 < β →
    (β : ℝ) < δ →
    ((↑(⌊-Real.log (ε₀ / 2) / Real.log (4/3 : ℝ)⌋₊) + 4 : ℝ) ≤ (β : ℝ) * (↑m : ℝ)) →
    IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β.den →
    ∃ (k : ℕ) (D : Finset ℕ),
      k ∈ C₁ ∧
      0 < k ∧
      Nat.Coprime k 210 ∧
      (∀ d ∈ D, k < d ∧ ¬(k ∣ d)) ∧
      D_multiplier_injective D ∧
      (∀ r : ℕ, r < k → ∃ D₂ : Finset ℕ, D₂ ⊆ D ∧ D₂.sum id % k = r) ∧
      (let β' := β - D.sum (fun d => (1 : ℚ) / (12 * d))
       0 < β' ∧
       (β : ℝ) / 2 < (β'.num.toNat : ℝ) / (β'.den : ℝ) ∧
       IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β'.den) ∧
      ((D.sum id : ℕ) : ℝ) ≤ 4 * ε₀ * (↑k) ^ 2 ∧
      (1 + ε₀) * (↑m : ℝ) * Real.exp (↑α : ℝ) < 2 * (↑k : ℝ) := by
  obtain ⟨δ₁, hδ₁_pos, hk_ev⟩ := k_exists_in_C1 smooth_arith α hα ε₀ hε₀ hε₀_lt
  have hD_ev := D_set_construction smooth_arith α ε₀ hε₀ hε₀_lt
  refine ⟨min δ₁ 1, lt_min hδ₁_pos one_pos, ?_⟩
  filter_upwards [hk_ev, hD_ev] with m hk_m hD_m
  intro C₁ β hC₁_range hβ_def hβ_pos hβ_lt hβ_recip hβ_ps
  have hβ_lt_δ₁ : (β : ℝ) < δ₁ := lt_of_lt_of_le hβ_lt (min_le_left _ _)
  obtain ⟨k, hk_mem, hk_pos, hk_cop, hk_ps, hk_large⟩ :=
    hk_m C₁ β hC₁_range hβ_def hβ_pos hβ_lt_δ₁
  have hk_in_range := hC₁_range k hk_mem
  have hβ_le_1 : (β : ℝ) ≤ 1 := le_of_lt (lt_of_lt_of_le hβ_lt (min_le_right _ _))
  have hβ_recip_k : (↑(⌊-Real.log (ε₀ / 2) / Real.log (4/3 : ℝ)⌋₊) + 4 : ℝ) ≤ (β : ℝ) * (↑k : ℝ) := by
    have hk_ge_m : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_of_lt (by exact_mod_cast hk_in_range.1 : m < k)
    calc (↑(⌊-Real.log (ε₀ / 2) / Real.log (4/3 : ℝ)⌋₊) + 4 : ℝ)
        ≤ (β : ℝ) * (↑m : ℝ) := hβ_recip
      _ ≤ (β : ℝ) * (↑k : ℝ) := by
          apply mul_le_mul_of_nonneg_left hk_ge_m (le_of_lt (Rat.cast_pos.mpr hβ_pos))
  obtain ⟨D, hD_range, hD_inj, hD_cover, hD_beta, hD_sum⟩ :=
    hD_m k hk_pos (by exact_mod_cast hk_in_range.1) hk_in_range.2 hk_cop hk_ps hk_large
      β hβ_pos hβ_le_1 hβ_recip_k hβ_ps
  refine ⟨k, D, hk_mem, hk_pos, hk_cop, hD_range, hD_inj, hD_cover, hD_beta, hD_sum, ?_⟩
  -- Prove (1 + ε₀) * m * e^α < 2 * k
  have hk_cast : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  have hexp : (0 : ℝ) < Real.exp (α : ℝ) := Real.exp_pos _
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg' m
  nlinarith [mul_nonneg hm_nn hexp.le]

/-
----------------------------------
PART 8: Definition of A and proof that it works.
----------------------------------
-/

/-
Build a finset from 7 pairwise disjoint finsets
-/
lemma seven_union_props
    (S₁ S₂ S₃ S₄ S₅ S₆ S₇ : Finset ℕ) (m : ℕ)
    (hm₁ : ∀ a ∈ S₁, m ≤ a) (hm₂ : ∀ a ∈ S₂, m ≤ a) (hm₃ : ∀ a ∈ S₃, m ≤ a)
    (hm₄ : ∀ a ∈ S₄, m ≤ a) (hm₅ : ∀ a ∈ S₅, m ≤ a) (hm₆ : ∀ a ∈ S₆, m ≤ a)
    (hm₇ : ∀ a ∈ S₇, m ≤ a)
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃) (h14 : Disjoint S₁ S₄)
    (h15 : Disjoint S₁ S₅) (h16 : Disjoint S₁ S₆) (h17 : Disjoint S₁ S₇)
    (h23 : Disjoint S₂ S₃) (h24 : Disjoint S₂ S₄)
    (h25 : Disjoint S₂ S₅) (h26 : Disjoint S₂ S₆) (h27 : Disjoint S₂ S₇)
    (h34 : Disjoint S₃ S₄) (h35 : Disjoint S₃ S₅)
    (h36 : Disjoint S₃ S₆) (h37 : Disjoint S₃ S₇)
    (h45 : Disjoint S₄ S₅) (h46 : Disjoint S₄ S₆) (h47 : Disjoint S₄ S₇)
    (h56 : Disjoint S₅ S₆) (h57 : Disjoint S₅ S₇)
    (h67 : Disjoint S₆ S₇)
    (n : ℕ) (α : ℚ)
    (hsum : S₁.sum id + S₂.sum id + S₃.sum id + S₄.sum id + S₅.sum id + S₆.sum id + S₇.sum id = n)
    (hrecip : S₁.sum (fun a => (1:ℚ)/a) + S₂.sum (fun a => (1:ℚ)/a) + S₃.sum (fun a => (1:ℚ)/a) +
              S₄.sum (fun a => (1:ℚ)/a) + S₅.sum (fun a => (1:ℚ)/a) + S₆.sum (fun a => (1:ℚ)/a) +
              S₇.sum (fun a => (1:ℚ)/a) = α) :
    Admissible α m n := by
  use S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅ ∪ S₆ ∪ S₇; simp_all +decide [ Finset.sum_union ] ; ring_nf; aesop;

/-
Disjointness: k-multiples vs elements < 2k (not equal to k)
-/
lemma disj_kmult_lt2k (B S : Finset ℕ) (k : ℕ) (hk : 0 < k)
    (hB_ge : ∀ b ∈ B, k ≤ b) (hB_dvd : ∀ b ∈ B, k ∣ b)
    (hS_lt : ∀ a ∈ S, a < 2 * k) (hS_ne : ∀ a ∈ S, a ≠ k) :
    Disjoint B S := by
  -- Suppose for contradiction that there exists an element $a$ in both $B$ and $S$.
  by_contra h_inter_ne_empty
  obtain ⟨a, haB, haS⟩ : ∃ a, a ∈ B ∧ a ∈ S := by
    exact Finset.not_disjoint_iff.mp h_inter_ne_empty
  have ha_k_le : k ≤ a := hB_ge a haB
  have ha_k_div : k ∣ a := hB_dvd a haB
  have ha_lt_2k : a < 2 * k := hS_lt a haS
  have ha_ne_k : a ≠ k := hS_ne a haS
  have ha_eq_k : a = k := by
    obtain ⟨ m, rfl ⟩ := ha_k_div ; nlinarith [ show m = 1 by nlinarith ] ;
  contradiction

/-
Disjointness: k-multiples vs c*D where k coprime to 210, D not k-divisible
-/
lemma disj_kmult_cD (B D : Finset ℕ) (k c : ℕ) (hk_cop : Nat.Coprime k 210)
    (hB_dvd : ∀ b ∈ B, k ∣ b) (hD_ndvd : ∀ d ∈ D, ¬(k ∣ d))
    (hc : c ∈ ({20,21,28,30} : Finset ℕ)) :
    Disjoint B (D.image (c * ·)) := by
  refine' Finset.disjoint_left.mpr fun x hx_B hx_cD => _;
  norm_num +zetaDelta at *;
  obtain ⟨ a, ha_D, rfl ⟩ := hx_cD; specialize hB_dvd _ hx_B; rcases Nat.dvd_mul.mp hB_dvd with ( h | h ) <;> simp_all +decide [ Nat.Coprime ] ;
  · grind;
  · rcases ‹_› with ⟨ h₁, x, hx₁, rfl ⟩ ; simp_all +decide ;
    rcases hc with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ Nat.coprime_mul_iff_left ] ;
    · have := Nat.le_of_dvd ( by decide ) ‹h + 1 ∣ 20›; interval_cases _ : h + 1 <;> simp_all +decide ;
    · have := Nat.le_of_dvd ( by decide ) ‹h + 1 ∣ 21›; interval_cases _ : h + 1 <;> simp_all +decide ;
    · have := Nat.le_of_dvd ( by decide ) ‹h + 1 ∣ 28›; interval_cases _ : h + 1 <;> simp_all +decide ;
    · have := Nat.le_of_dvd ( by decide ) ‹h + 1 ∣ 30›; interval_cases _ : h + 1 <;> simp_all +decide ;

/-
Disjointness: elements < 2k vs c*D where D elements > k, c ≥ 20
-/
lemma disj_lt2k_cD (S D : Finset ℕ) (k c : ℕ)
    (hS_lt : ∀ a ∈ S, a < 2 * k) (hD_gt : ∀ d ∈ D, k < d) (hc : 20 ≤ c) :
    Disjoint S (D.image (c * ·)) := by
  by_contra h;
  obtain ⟨a, haS, haD⟩ : ∃ a ∈ S, ∃ d ∈ D, a = c * d := by
    rw [ Finset.not_disjoint_iff ] at h; aesop;
  obtain ⟨ d, hdD, rfl ⟩ := haD; nlinarith [ hS_lt _ haS, hD_gt _ hdD ] ;

lemma disj_from_mult_inj (D₁ D₂ D : Finset ℕ) (c₁ c₂ : ℕ) (hne : c₁ ≠ c₂)
    (hD₁ : D₁ ⊆ D) (hD₂ : D₂ ⊆ D)
    (hc₁ : c₁ ∈ ({20, 21, 28, 30} : Finset ℕ))
    (hc₂ : c₂ ∈ ({20, 21, 28, 30} : Finset ℕ))
    (hinj : D_multiplier_injective D) :
    Disjoint (D₁.image (c₁ * ·)) (D₂.image (c₂ * ·)) := by
  rw [Finset.disjoint_left]
  intro a ha₁ ha₂
  obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.mp ha₁
  obtain ⟨d₂, hd₂, h_eq⟩ := Finset.mem_image.mp ha₂
  exact absurd (hinj d₂ (hD₂ hd₂) d₁ (hD₁ hd₁) c₂ hc₂ c₁ hc₁ h_eq).1 (Ne.symm hne)

/-
Sum of c*D image = c * sum D
-/
lemma sum_image_mul (D : Finset ℕ) (c : ℕ) (hc : 0 < c) :
    (D.image (c * ·)).sum id = c * D.sum id := by
  rw [ Finset.mul_sum, Finset.sum_image ] ; aesop;
  exact fun x hx y hy hxy => mul_left_cancel₀ hc.ne' hxy

-- Reciprocal sum of c*D image
lemma recip_image_mul (D : Finset ℕ) (c : ℕ) (hc : 0 < c)
    (_hpos : ∀ d ∈ D, 0 < d) :
    (D.image (c * ·)).sum (fun a => (1:ℚ)/a) = D.sum (fun d => (1:ℚ)/(c * d)) := by
  rw [Finset.sum_image]
  · congr 1; ext d; simp [Nat.cast_mul]
  · intro x _ y _ h; exact mul_left_cancel₀ (Nat.pos_iff_ne_zero.mp hc) h

lemma helpers_og_graham_scaled (k n' : ℕ) (hk : 0 < k) (hn' : 78 ≤ n') :
    ∃ B : Finset ℕ,
      (∀ b ∈ B, k ≤ b) ∧
      (∀ b ∈ B, k ∣ b) ∧
      B.sum id = k * n' ∧
      B.sum (fun a => (1 : ℚ) / a) = (1 : ℚ) / k := by
  obtain ⟨S, hS_ge, hS_sum, hS_recip⟩ := ogGraham n' hn'
  have hinj : ∀ x ∈ S, ∀ y ∈ S, x * k = y * k → x = y :=
    fun x _ y _ h => mul_right_cancel₀ (Nat.pos_iff_ne_zero.mp hk) h
  refine ⟨S.image (· * k), ?_, ?_, ?_, ?_⟩
  · intro b hb; simp only [Finset.mem_image] at hb; obtain ⟨a, ha, rfl⟩ := hb
    exact Nat.le_mul_of_pos_left k (hS_ge a ha)
  · intro b hb; simp only [Finset.mem_image] at hb; obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a, mul_comm a k⟩
  · rw [Finset.sum_image hinj]; change (∑ x ∈ S, x * k) = k * n'
    rw [← Finset.sum_mul]; change S.sum id * k = k * n'; rw [hS_sum, mul_comm]
  · rw [Finset.sum_image hinj]
    have : (∑ a ∈ S, (1 : ℚ) / (↑(a * k) : ℚ)) =
        (∑ a ∈ S, ((1 : ℚ) / (↑a : ℚ))) * ((1 : ℚ) / (↑k : ℚ)) := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _
      rw [Nat.cast_mul, div_mul_div_comm, one_mul]
    rw [this, hS_recip, one_mul]

theorem helpers_admissible_assembly
    (α : ℚ) (m : ℕ) (k : ℕ) (hk : 0 < k) (hk_gt_m : m < k)
    (hk_cop : Nat.Coprime k 210)
    (C₁ : Finset ℕ) (C₂ : Finset ℕ) (D : Finset ℕ)
    (hC₁_range : ∀ a ∈ C₁, m < a ∧ a < 2 * k)
    (hk_mem : k ∈ C₁)
    (hC₂_range : ∀ a ∈ C₂, k < a ∧ a < 2 * k)
    (hD_range : ∀ d ∈ D, k < d ∧ ¬(k ∣ d))
    (hD_inj : D_multiplier_injective D)
    (hD_cover : ∀ r : ℕ, r < k → ∃ D₂ : Finset ℕ, D₂ ⊆ D ∧ D₂.sum id % k = r)
    (hrecip : C₁.sum (fun a => (1 : ℚ) / a) +
              C₂.sum (fun a => (1 : ℚ) / a) +
              D.sum (fun d => (1 : ℚ) / (12 * d)) = α)
    (hC₁C₂_disj : Disjoint C₁ C₂)
    :
    ∀ n : ℕ, n ≥ C₁.sum id + C₂.sum id + 50 * D.sum id + 78 * k →
    Admissible α m n := by
  intro n hn
  have hk_le_sum : k ≤ C₁.sum id := Finset.single_le_sum (fun x _ => Nat.zero_le x) hk_mem
  set Y := C₁.sum id - k + C₂.sum id + 49 * D.sum id with hY_def
  obtain ⟨D₂, hD₂_sub, hD₂_mod⟩ := hD_cover ((n - Y) % k) (Nat.mod_lt _ hk)
  have hD₂_le : D₂.sum id ≤ D.sum id := Finset.sum_le_sum_of_subset hD₂_sub
  have hY_le_n : Y ≤ n := by omega
  have hYD₂_le_n : Y + D₂.sum id ≤ n := by omega
  have hmod_eq : (n - Y - D₂.sum id) % k = 0 := by
    rw [Nat.sub_sub]
    exact Nat.sub_mod_eq_zero_of_mod_eq
      (by rw [Nat.add_mod, hD₂_mod, ← Nat.add_mod, Nat.add_sub_cancel' hY_le_n])
  set n' := (n - Y - D₂.sum id) / k with hn'_def
  have hn'_eq : n = Y + D₂.sum id + k * n' := by
    have := Nat.div_add_mod (n - Y - D₂.sum id) k
    rw [hmod_eq, add_zero] at this
    simp only [hn'_def] at this ⊢; omega
  have hn'_ge : 78 ≤ n' := by rw [Nat.le_div_iff_mul_le hk]; omega
  obtain ⟨B, hB_ge, hB_dvd, hB_sum, hB_recip⟩ := helpers_og_graham_scaled k n' hk hn'_ge
  set D₁ := D \ D₂
  have hD₁_gt : ∀ d ∈ D₁, k < d := fun d hd => (hD_range d (Finset.mem_sdiff.mp hd).1).1
  have hD₂_gt : ∀ d ∈ D₂, k < d := fun d hd => (hD_range d (hD₂_sub hd)).1
  have hD₁_ndvd : ∀ d ∈ D₁, ¬(k ∣ d) := fun d hd => (hD_range d (Finset.mem_sdiff.mp hd).1).2
  have hD₂_ndvd : ∀ d ∈ D₂, ¬(k ∣ d) := fun d hd => (hD_range d (hD₂_sub hd)).2
  have hD₁_pos : ∀ d ∈ D₁, 0 < d := fun d hd => by linarith [hD₁_gt d hd]
  have hD₂_pos : ∀ d ∈ D₂, 0 < d := fun d hd => by linarith [hD₂_gt d hd]
  have hC₁ek_lt : ∀ a ∈ C₁.erase k, a < 2 * k := fun a ha => (hC₁_range a (Finset.mem_of_mem_erase ha)).2
  have hC₁ek_ne : ∀ a ∈ C₁.erase k, a ≠ k := fun a ha => Finset.ne_of_mem_erase ha
  have hC₂_lt : ∀ a ∈ C₂, a < 2 * k := fun a ha => (hC₂_range a ha).2
  have hC₂_ne : ∀ a ∈ C₂, a ≠ k := fun a ha => Nat.ne_of_gt (hC₂_range a ha).1
  -- Apply seven_union_props
  apply seven_union_props B (C₁.erase k) C₂
    (D₁.image (21 * ·)) (D₁.image (28 * ·))
    (D₂.image (20 * ·)) (D₂.image (30 * ·)) m
  -- ≥ m goals
  · exact fun a ha => le_of_lt (lt_of_lt_of_le hk_gt_m (hB_ge a ha))
  · exact fun a ha => le_of_lt (hC₁_range a (Finset.mem_of_mem_erase ha)).1
  · exact fun a ha => le_of_lt (lt_of_lt_of_le hk_gt_m (le_of_lt (hC₂_range a ha).1))
  · intro a ha; simp at ha; obtain ⟨d, hd, rfl⟩ := ha; nlinarith [hD₁_gt d hd]
  · intro a ha; simp at ha; obtain ⟨d, hd, rfl⟩ := ha; nlinarith [hD₁_gt d hd]
  · intro a ha; simp at ha; obtain ⟨d, hd, rfl⟩ := ha; nlinarith [hD₂_gt d hd]
  · intro a ha; simp at ha; obtain ⟨d, hd, rfl⟩ := ha; nlinarith [hD₂_gt d hd]
  -- Disjointness: B vs others
  · exact disj_kmult_lt2k B (C₁.erase k) k hk hB_ge hB_dvd hC₁ek_lt hC₁ek_ne
  · exact disj_kmult_lt2k B C₂ k hk hB_ge hB_dvd hC₂_lt hC₂_ne
  · exact disj_kmult_cD B D₁ k 21 hk_cop hB_dvd hD₁_ndvd (by simp)
  · exact disj_kmult_cD B D₁ k 28 hk_cop hB_dvd hD₁_ndvd (by simp)
  · exact disj_kmult_cD B D₂ k 20 hk_cop hB_dvd hD₂_ndvd (by simp)
  · exact disj_kmult_cD B D₂ k 30 hk_cop hB_dvd hD₂_ndvd (by simp)
  -- C₁\{k} vs others
  · exact Finset.disjoint_of_subset_left (Finset.erase_subset k C₁) hC₁C₂_disj
  · exact disj_lt2k_cD (C₁.erase k) D₁ k 21 hC₁ek_lt hD₁_gt (by omega)
  · exact disj_lt2k_cD (C₁.erase k) D₁ k 28 hC₁ek_lt hD₁_gt (by omega)
  · exact disj_lt2k_cD (C₁.erase k) D₂ k 20 hC₁ek_lt hD₂_gt (by omega)
  · exact disj_lt2k_cD (C₁.erase k) D₂ k 30 hC₁ek_lt hD₂_gt (by omega)
  -- C₂ vs D images
  · exact disj_lt2k_cD C₂ D₁ k 21 hC₂_lt hD₁_gt (by omega)
  · exact disj_lt2k_cD C₂ D₁ k 28 hC₂_lt hD₁_gt (by omega)
  · exact disj_lt2k_cD C₂ D₂ k 20 hC₂_lt hD₂_gt (by omega)
  · exact disj_lt2k_cD C₂ D₂ k 30 hC₂_lt hD₂_gt (by omega)
  -- D image pairs
  · exact disj_from_mult_inj D₁ D₁ D 21 28 (by omega) Finset.sdiff_subset Finset.sdiff_subset (by simp) (by simp) hD_inj
  · exact disj_from_mult_inj D₁ D₂ D 21 20 (by omega) Finset.sdiff_subset hD₂_sub (by simp) (by simp) hD_inj
  · exact disj_from_mult_inj D₁ D₂ D 21 30 (by omega) Finset.sdiff_subset hD₂_sub (by simp) (by simp) hD_inj
  · exact disj_from_mult_inj D₁ D₂ D 28 20 (by omega) Finset.sdiff_subset hD₂_sub (by simp) (by simp) hD_inj
  · exact disj_from_mult_inj D₁ D₂ D 28 30 (by omega) Finset.sdiff_subset hD₂_sub (by simp) (by simp) hD_inj
  · exact disj_from_mult_inj D₂ D₂ D 20 30 (by omega) hD₂_sub hD₂_sub (by simp) (by simp) hD_inj
  -- Sum = n
  · rw [hB_sum, sum_image_mul D₁ 21 (by omega), sum_image_mul D₁ 28 (by omega),
        sum_image_mul D₂ 20 (by omega), sum_image_mul D₂ 30 (by omega)]
    have h_erase : (C₁.erase k).sum id + k = C₁.sum id := Finset.sum_erase_add C₁ id hk_mem
    have h_sdiff : D₁.sum id + D₂.sum id = D.sum id := by
      change (D \ D₂).sum id + D₂.sum id = D.sum id
      rw [← Finset.sum_sdiff hD₂_sub]
    omega
  -- Reciprocal sum = α
  · rw [hB_recip,
        recip_image_mul D₁ 21 (by omega) hD₁_pos,
        recip_image_mul D₁ 28 (by omega) hD₁_pos,
        recip_image_mul D₂ 20 (by omega) hD₂_pos,
        recip_image_mul D₂ 30 (by omega) hD₂_pos]
    have h_erase_recip : (C₁.erase k).sum (fun a => (1:ℚ)/a) + (1:ℚ)/k = C₁.sum (fun a => (1:ℚ)/a) :=
      Finset.sum_erase_add C₁ _ hk_mem
    have h_sdiff_recip : D₁.sum (fun d => (1:ℚ)/(21*d) + (1:ℚ)/(28*d)) +
        D₂.sum (fun d => (1:ℚ)/(20*d) + (1:ℚ)/(30*d)) = D.sum (fun d => (1:ℚ)/(12*d)) := by
      change (D \ D₂).sum _ + D₂.sum _ = D.sum _
      rw [← Finset.sum_sdiff hD₂_sub]; ring_nf
    have h1 : D₁.sum (fun d => (1:ℚ)/(21*d)) + D₁.sum (fun d => (1:ℚ)/(28*d)) =
        D₁.sum (fun d => (1:ℚ)/(21*d) + (1:ℚ)/(28*d)) := (Finset.sum_add_distrib).symm
    have h2 : D₂.sum (fun d => (1:ℚ)/(20*d)) + D₂.sum (fun d => (1:ℚ)/(30*d)) =
        D₂.sum (fun d => (1:ℚ)/(20*d) + (1:ℚ)/(30*d)) := (Finset.sum_add_distrib).symm
    linarith [h_erase_recip, h_sdiff_recip, h1, h2]

/-- Assembly lemma. -/
lemma admissible_assembly
    (α : ℚ) (m : ℕ) (k : ℕ) (hk : 0 < k) (hk_gt_m : m < k)
    (hk_cop : Nat.Coprime k 210)
    (C₁ : Finset ℕ) (C₂ : Finset ℕ) (D : Finset ℕ)
    (hC₁_range : ∀ a ∈ C₁, m < a ∧ a < 2 * k)
    (hk_mem : k ∈ C₁)
    (hC₂_range : ∀ a ∈ C₂, k < a ∧ a < 2 * k)
    (hD_range : ∀ d ∈ D, k < d ∧ ¬(k ∣ d))
    (hD_inj : D_multiplier_injective D)
    (hD_cover : ∀ r : ℕ, r < k → ∃ D₂ : Finset ℕ, D₂ ⊆ D ∧ D₂.sum id % k = r)
    (hrecip : C₁.sum (fun a => (1 : ℚ) / a) +
              C₂.sum (fun a => (1 : ℚ) / a) +
              D.sum (fun d => (1 : ℚ) / (12 * d)) = α)
    (hC₁C₂_disj : Disjoint C₁ C₂) :
    ∀ n : ℕ, n ≥ C₁.sum id + C₂.sum id + 50 * D.sum id + 78 * k →
    Admissible α m n :=
  helpers_admissible_assembly α m k hk hk_gt_m hk_cop C₁ C₂ D hC₁_range hk_mem
    hC₂_range hD_range hD_inj hD_cover hrecip hC₁C₂_disj

/-
----------------------------------
PART 9: Bound analysis, asymptotics, and main theorem.
----------------------------------
-/

/-
If S is a finset of naturals all in the open interval (a, b) with 0 ≤ a,
then S.sum id ≤ (Ioc ⌊a⌋₊ ⌊b⌋₊).sum id.
-/
lemma finset_sum_in_interval_le (S : Finset ℕ) (a b : ℝ) (ha : 0 ≤ a)
    (hS : ∀ x ∈ S, a < (x : ℝ) ∧ (x : ℝ) < b) :
    S.sum id ≤ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).sum id := by
  exact Finset.sum_le_sum_of_subset ( fun x hx => Finset.mem_Ioc.mpr ⟨ Nat.lt_of_not_ge fun hx' : x ≤ ⌊a⌋₊ => by have := hS x hx; linarith [ Nat.floor_le ha, ( by norm_cast : ( x:ℝ ) ≤ ⌊a⌋₊ ) ], Nat.le_floor <| by linarith [ hS x hx ] ⟩ )

-- Algebraic core for construction_bound_part2
lemma bound_core (m k : ℕ) (α : ℚ) (ε ε₀ : ℝ)
    (hε_pos : 0 < ε) (hεq : ε ≤ 1 / 4)
    (hε_le : ε ≤ ε₀ / (500 * (Real.exp (2 * ↑α) + 1)))
    (hm_large : 8 * (1 + ε) * Real.exp (↑α : ℝ) ≤ ε₀ * (↑m : ℝ))
    (hm_ge2 : 2 ≤ m)
    (hk_lt : (↑k : ℝ) < ↑m * Real.exp (↑α : ℝ))
    (v50D vC2 : ℝ)
    (h50D : v50D ≤ 200 * ε * (↑k) ^ 2)
    (hC2 : vC2 ≤ (ε * ↑m * Real.exp (↑α : ℝ) + 1) * ((1 + ε) * ↑m * Real.exp (↑α : ℝ))) :
    v50D + vC2 ≤ ε₀ * (↑m) ^ 2 := by
  have hea := Real.exp_pos (↑α : ℝ)
  have he2a := Real.exp_pos (2 * (↑α : ℝ))
  have hm_pos : (0 : ℝ) < ↑m := by exact_mod_cast show 0 < m by omega
  have hexp_sq : rexp (↑α : ℝ) * rexp (↑α : ℝ) = rexp (2 * (↑α : ℝ)) := by
    rw [← Real.exp_add]; ring_nf
  have hk_sq : (↑k : ℝ) ^ 2 ≤ (↑m) ^ 2 * rexp (2 * ↑α) := by
    have := sq_le_sq' (by nlinarith : -(↑m * rexp ↑α) ≤ (↑k : ℝ)) (le_of_lt hk_lt)
    nlinarith [sq_nonneg (↑m : ℝ)]
  have h1 : v50D ≤ 200 * ε * (↑m) ^ 2 * rexp (2 * ↑α) := by nlinarith
  have h2 : vC2 ≤ ε * (1 + ε) * (↑m) ^ 2 * rexp (2 * ↑α) + (1 + ε) * ↑m * rexp ↑α := by
    have key : (ε * ↑m * rexp ↑α + 1) * ((1 + ε) * ↑m * rexp ↑α) =
        ε * (1 + ε) * ↑m ^ 2 * (rexp ↑α * rexp ↑α) + (1 + ε) * ↑m * rexp ↑α := by ring
    rw [hexp_sq] at key; linarith
  have h3 : (1 + ε) * ↑m * rexp ↑α ≤ ε₀ * (↑m) ^ 2 / 8 := by nlinarith [sq_nonneg (↑m : ℝ)]
  have hεb : ε * (500 * (rexp (2 * ↑α) + 1)) ≤ ε₀ := by
    rw [le_div_iff₀ (by positivity)] at hε_le; linarith
  have h4 : (201 + ε) * ε * rexp (2 * ↑α) ≤ ε₀ * 7 / 8 := by
    have h4a : (201 + ε) * ε ≤ 201.25 * ε := by nlinarith
    have h4c := mul_le_mul_of_nonneg_right h4a (le_of_lt he2a)
    calc (201 + ε) * ε * rexp (2 * ↑α) ≤ 201.25 * ε * rexp (2 * ↑α) := h4c
      _ ≤ 201.25 * ε * (rexp (2 * ↑α) + 1) := by nlinarith
      _ = (201.25 / 500) * (ε * (500 * (rexp (2 * ↑α) + 1))) := by ring
      _ ≤ (201.25 / 500) * ε₀ := by nlinarith
      _ ≤ ε₀ * 7 / 8 := by nlinarith
  nlinarith [sq_nonneg (↑m : ℝ)]

lemma construction_bound_part2
    (m k : ℕ) (α : ℚ) (ε ε₀ : ℝ)
    (hε_pos : 0 < ε)
    (hε_le_quarter : ε ≤ 1 / 4)
    (hε_le : ε ≤ ε₀ / (500 * (rexp (2 * ↑α) + 1)))
    (hm_large : 8 * (1 + ε) * rexp (↑α : ℝ) ≤ ε₀ * (m : ℝ))
    (hm_ge2 : 2 ≤ m)
    (C₁ C₂ D : Finset ℕ)
    (hC₁_range : ∀ a ∈ C₁, (m : ℝ) < ↑a ∧ ↑a < ↑m * rexp ↑α)
    (hC₂_range : ∀ a ∈ C₂, ↑m * rexp ↑α < ↑a ∧ ↑a < (1 + ε) * ↑m * rexp ↑α)
    (hk_lt : (k : ℝ) < ↑m * rexp ↑α)
    (hD_bound : ((D.sum id : ℕ) : ℝ) ≤ 4 * ε * (↑k) ^ 2) :
    ((C₁.sum id + C₂.sum id + 50 * D.sum id + 78 * k : ℕ) : ℝ) ≤
    ((Finset.Ioc m (⌊↑m * rexp ↑α⌋₊)).sum id : ℕ) + ε₀ * ↑m ^ 2 + 78 * ↑m * rexp ↑α := by
  norm_num +zetaDelta at *;
  have h_bound_core : (∑ x ∈ C₁, x : ℝ) + (∑ x ∈ C₂, x : ℝ) ≤ (∑ x ∈ Ioc m ⌊ ( m : ℝ ) * Real.exp α⌋₊, x : ℝ) + (ε * m * Real.exp α + 1) * ((1 + ε) * m * Real.exp α) := by
    refine' add_le_add _ _;
    · exact Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => Finset.mem_Ioc.mpr ⟨ hC₁_range x hx |>.1, Nat.le_floor <| le_of_lt <| hC₁_range x hx |>.2 ⟩ ) fun _ _ _ => Nat.cast_nonneg _;
    · have hC₂_bound : (∑ x ∈ C₂, x : ℝ) ≤ (Finset.Ioc ⌊(m : ℝ) * Real.exp α⌋₊ ⌊(1 + ε) * m * Real.exp α⌋₊).sum id := by
        have hC₂_le : C₂.sum id ≤ Finset.sum (Finset.Ioc (Nat.floor (m * Real.exp α)) (Nat.floor ((1 + ε) * m * Real.exp α))) id := by
          apply finset_sum_in_interval_le C₂ (m * Real.exp α) ((1 + ε) * m * Real.exp α) (by positivity) (by
          assumption)
        generalize_proofs at *; (
        rw [ ← Nat.cast_sum ] ; exact_mod_cast hC₂_le;);
      refine' le_trans hC₂_bound _;
      norm_num [ Finset.sum_Ioc_succ_top ];
      refine' le_trans ( Finset.sum_le_sum fun x hx => show ( x : ℝ ) ≤ ( 1 + ε ) * m * Real.exp α from _ ) _ <;> norm_num at *;
      · exact le_trans ( Nat.cast_le.mpr hx.2 ) ( Nat.floor_le ( by positivity ) );
      · rw [ Nat.cast_sub ( Nat.floor_mono <| by nlinarith [ show ( 0 :ℝ ) ≤ m * Real.exp α by positivity ] ) ] ; nlinarith [ Nat.floor_le ( show ( 0 :ℝ ) ≤ ( 1 + ε ) * m * Real.exp α by positivity ), Nat.lt_floor_add_one ( ( 1 + ε ) * m * Real.exp α ), Nat.floor_le ( show ( 0 :ℝ ) ≤ m * Real.exp α by positivity ), Nat.lt_floor_add_one ( m * Real.exp α ) ] ;
  have h_bound_core2 : (ε * m * Real.exp α + 1) * ((1 + ε) * m * Real.exp α) + 50 * (4 * ε * k ^ 2) ≤ ε₀ * m ^ 2 := by
    convert bound_core m k α ε ε₀ hε_pos hε_le_quarter ?_ ?_ ?_ ?_ ?_ using 1 <;> try nlinarith [ Real.exp_pos α ] ;
    swap;
    exact 50 * ( 4 * ε * k ^ 2 );
    exact ⟨ fun h vC2 hvC2 hvC2' => by linarith, fun h => by linarith [ h ( ( ε * m * Real.exp α + 1 ) * ( ( 1 + ε ) * m * Real.exp α ) ) ( by linarith ) ( by linarith ) ] ⟩;
  linarith

/-- Main construction theorem. -/
theorem admissible_above_threshold
    (Croot :
      ∀ (α : ℚ), 0 < α → ∀ (ε : ℝ), 0 < ε →
      ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
        ∃ C₁ : Finset ℕ,
          (∀ a ∈ C₁, (m : ℝ) < (a : ℝ) ∧ (a : ℝ) < (m : ℝ) * Real.exp (α : ℝ)) ∧
          let β : ℚ := α - C₁.sum (fun a => (1 : ℚ) / (a : ℚ))
          (|(β : ℝ) - 3 * (α : ℝ) * (Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ))| ≤
            ε * |Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)|) ∧
          IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β.den ∧
          (∀ (s t : ℕ), Nat.Coprime s t → 0 < t →
            (β : ℝ) / 2 < (s : ℝ) / (t : ℝ) →
            (s : ℝ) / (t : ℝ) ≤ (β : ℝ) →
            IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) t →
            ∃ C₂ : Finset ℕ,
              (∀ a ∈ C₂, (m : ℝ) * Real.exp (α : ℝ) < (a : ℝ) ∧
                (a : ℝ) < (1 + ε) * (m : ℝ) * Real.exp (α : ℝ)) ∧
              C₂.sum (fun a => (1 : ℚ) / (a : ℚ)) = (s : ℚ) / (t : ℚ)))
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N}))
    (α : ℚ) (hα : 0 < α) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∀ᶠ m in atTop, ∃ X : ℕ, 0 < X ∧
      (∀ n, X ≤ n → Admissible α m n) ∧
      (X : ℝ) ≤ ((Finset.Ioc m (⌊(m : ℝ) * Real.exp (α : ℝ)⌋₊)).sum id : ℕ) +
        ε₀ * (↑m) ^ 2 + 78 * (↑m) * Real.exp (↑α : ℝ) := by
  -- Choose ε for Croot
  have hα_pos : (0 : ℝ) < (α : ℝ) := Rat.cast_pos.mpr hα
  set ε := min (ε₀ / (500 * (Real.exp (2 * (α : ℝ)) + 1))) (min ((α : ℝ) / 2) (1/4)) with hε_def
  have hε_pos : 0 < ε := by positivity
  have hε_lt_3α : ε < 3 * (α : ℝ) := by
    calc ε ≤ (α : ℝ) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      _ < 3 * (α : ℝ) := by linarith
  -- Get Croot output
  obtain ⟨m₀, hm₀⟩ := Croot α hα ε hε_pos
  -- Get D&k construction
  have hε_lt_third : ε < 1/3 := calc ε ≤ 1/4 := le_trans (min_le_right _ _) (min_le_right _ _)
    _ < 1/3 := by norm_num
  obtain ⟨δ_Dk, hδ_Dk_pos, h_Dk⟩ := D_and_k_construction smooth_arith α hα ε hε_pos hε_lt_third
  -- Get β positivity
  have h_β_pos := β_pos_for_large_m α hα ε hε_pos hε_lt_3α
  -- For Part 2: need m large enough that (1+ε)me^α ≤ (ε₀/8)m²
  have h_m_large_c2 : ∀ᶠ (m : ℕ) in atTop,
      8 * (1 + ε) * rexp (↑α : ℝ) ≤ ε₀ * (m : ℝ) := by
    rw [Filter.eventually_atTop]
    exact ⟨⌈8 * (1 + ε) * rexp (↑α : ℝ) / ε₀⌉₊, fun m hm => by
      have h1 : 8 * (1 + ε) * rexp (↑α : ℝ) / ε₀ ≤ (m : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
      rw [div_le_iff₀ hε₀] at h1; linarith⟩
  -- β < δ_Dk eventually (from β → 0)
  have h_β_lt_δ : ∀ᶠ (m : ℕ) in atTop,
      ∀ (β : ℚ),
      (|(β : ℝ) - 3 * (α : ℝ) * (Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ))| ≤
        ε * |Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)|) →
      0 < β → (β : ℝ) < δ_Dk := by
    exact beta_lt_any_pos α hα ε hε_pos hε_lt_3α δ_Dk hδ_Dk_pos
  -- β * m ≥ L_bound + 4 eventually (from β ≈ 3α·loglog m/log m, so β·m → ∞)
  set L_adm := (↑(⌊-Real.log (ε / 2) / Real.log (4/3 : ℝ)⌋₊) + 4 : ℝ) with hL_adm_def
  -- β * m ≥ L_adm eventually: β ≥ (3α - ε) · loglog m / log m, so β·m ≥ (3α - ε) · m · loglog m / log m → ∞
  have h_β_recip : ∀ᶠ (m : ℕ) in atTop,
      ∀ (β : ℚ),
      (|(β : ℝ) - 3 * (α : ℝ) * (Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ))| ≤
        ε * |Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)|) →
      0 < β → L_adm ≤ (β : ℝ) * (↑m : ℝ) :=
    beta_times_m_eventually_large α ε hε_pos hε_lt_3α L_adm
  -- Combine all filter conditions
  filter_upwards [h_Dk, h_β_pos,
                  Filter.eventually_ge_atTop m₀,
                  Filter.eventually_ge_atTop 2,
                  h_m_large_c2, h_β_lt_δ, h_β_recip] with m hDk hβ_ev hm_Croot hm_ge2 hm_large hβ_lt hβ_recip_m
  -- Get C₁ from Croot
  obtain ⟨C₁, hC₁_range, hβ_approx, hβ_ps, hCroot3⟩ := hm₀ m hm_Croot
  -- β > 0
  set β := α - C₁.sum (fun a => (1 : ℚ) / (a : ℚ))
  have hβ_pos : 0 < β := hβ_ev β hβ_approx
  -- Get k, D from D_and_k_construction
  obtain ⟨k, D, hk_mem, hk_pos, hk_cop, hD_range, hD_inj, hD_cover,
          ⟨hβ'_pos, hβ'_half, hβ'_ps⟩, hD_sum_bound, h2k⟩ :=
    hDk C₁ β hC₁_range rfl hβ_pos (hβ_lt β hβ_approx hβ_pos) (hβ_recip_m β hβ_approx hβ_pos) hβ_ps
  -- Key properties of k
  have hk_in_C1 := hC₁_range k hk_mem
  have hk_gt_m : m < k := by exact_mod_cast hk_in_C1.1
  have hk_lt_meA : (k : ℝ) < (m : ℝ) * rexp (↑α) := hk_in_C1.2
  have hmeA_lt_2k : (↑m : ℝ) * rexp (↑α) < 2 * (↑k : ℝ) := by
    have hε_le : 0 ≤ ε := le_of_lt hε_pos
    linarith [mul_nonneg hε_le (mul_nonneg (Nat.cast_nonneg' m) (Real.exp_pos (↑α)).le)]
  -- β' properties
  set β' := β - D.sum (fun d => (1 : ℚ) / (12 * d))
  have h_rat := rat_pos_Croot_input β' hβ'_pos
  -- β' ≤ β (we subtracted nonneg terms)
  have hβ'_le_β : (β' : ℝ) ≤ (β : ℝ) := by
    have hsub : β' = β - D.sum (fun d => (1 : ℚ) / (12 * d)) := rfl
    rw [hsub]
    have : (0 : ℚ) ≤ D.sum (fun d => (1 : ℚ) / (12 * d)) :=
      Finset.sum_nonneg (fun d hd => by positivity)
    exact_mod_cast sub_le_self β this
  -- Apply Croot's part 3 to get C₂
  have h_st_le_β : (β'.num.toNat : ℝ) / (β'.den : ℝ) ≤ (β : ℝ) :=
    le_trans h_rat.2.2.2 hβ'_le_β
  obtain ⟨C₂, hC₂_range_raw, hC₂_recip⟩ := hCroot3 β'.num.toNat β'.den
    h_rat.1 h_rat.2.1 hβ'_half h_st_le_β hβ'_ps
  -- Set X
  set X := C₁.sum id + C₂.sum id + 50 * D.sum id + 78 * k
  have hX_pos : 0 < X := by
    have : k ≤ C₁.sum id := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hk_mem
    omega
  refine ⟨X, hX_pos, ?_, ?_⟩
  -- Part 1: All n ≥ X are admissible
  · intro n hn
    apply admissible_assembly α m k hk_pos hk_gt_m hk_cop C₁ C₂ D
    -- C₁ range: m < a ∧ a < 2k
    · intro a ha
      refine ⟨by exact_mod_cast (hC₁_range a ha).1, ?_⟩
      have : (a : ℝ) < 2 * (k : ℝ) := lt_trans (hC₁_range a ha).2 hmeA_lt_2k |>.trans_le le_rfl |>.trans_le le_rfl
      exact_mod_cast this
    · exact hk_mem
    -- C₂ range: k < a ∧ a < 2k
    · intro a ha
      obtain ⟨hmeA_lt_a, ha_lt⟩ := hC₂_range_raw a ha
      refine ⟨?_, ?_⟩
      · exact_mod_cast (show (k : ℝ) < (a : ℝ) by linarith)
      · have : (a : ℝ) < 2 * (↑k : ℝ) := lt_of_lt_of_le ha_lt (le_of_lt h2k)
        exact_mod_cast this
    · exact hD_range
    · exact hD_inj
    · exact hD_cover
    -- Reciprocal sum = α
    · have hC2_eq : C₂.sum (fun a => (1 : ℚ) / a) = β' := by
        rw [hC₂_recip]
        have h_num : (β'.num.toNat : ℚ) = (β'.num : ℚ) := by
          exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (le_of_lt hβ'_pos))
        rw [h_num]
        exact Rat.num_div_den β'
      rw [hC2_eq]; ring
    -- Disjoint C₁ C₂
    · rw [Finset.disjoint_left]
      intro a ha1 ha2
      have h1 : (a : ℝ) < (m : ℝ) * rexp (↑α) := (hC₁_range a ha1).2
      have h2 : (m : ℝ) * rexp (↑α) < (a : ℝ) := (hC₂_range_raw a ha2).1
      linarith
    · exact hn
  -- Part 2: X ≤ ΣI₁ + ε₀m² + 78me^α
  · exact construction_bound_part2 m k α ε ε₀ hε_pos
      (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _)
      hm_large hm_ge2 C₁ C₂ D hC₁_range hC₂_range_raw hk_lt_meA hD_sum_bound

/-
For large m, the sum of integers in (m, ⌊me^α⌋) is approximately (1/2)(e^{2α}-1)m².
-/
lemma interval_sum_asymp (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun m : ℕ =>
      (((Finset.Ioc m (⌊(m : ℝ) * Real.exp α⌋₊)).sum id : ℕ) : ℝ) /
        ((Real.exp (2 * α) - 1) * (↑m) ^ 2))
      Filter.atTop (nhds (1 / 2)) := by
  -- Set $r = N/m$, then $N = rm + O(1)$, and the sum = $(r²m² + rm)/2 - (m² + m)/2 = (r²-1)m²/2 + (r-1)m/2$.
  suffices h_suff : Filter.Tendsto (fun m : ℕ => (((Nat.floor (m * (Real.exp α))) * ((Nat.floor (m * (Real.exp α))) + 1)) / 2 - m * (m + 1) / 2 : ℝ) / (((Real.exp (2 * α)) - 1) * m ^ 2)) Filter.atTop (nhds ((1 : ℝ) / 2)) by
    refine' h_suff.congr' _;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm ; norm_num [ mul_comm, Finset.sum_Ioc_succ_top, add_assoc ] ; ring_nf;
    -- By definition of sum, we can rewrite the right-hand side as the sum of integers from $m+1$ to $\lfloor m e^\alpha \rfloor$.
    have h_sum : ∑ x ∈ Finset.Ioc m (Nat.floor (m * Real.exp α)), (x : ℝ) = ((Nat.floor (m * Real.exp α)) * ((Nat.floor (m * Real.exp α)) + 1) / 2 : ℝ) - (m * (m + 1) / 2 : ℝ) := by
      have h_sum : ∀ n : ℕ, ∑ x ∈ Finset.Icc 1 n, (x : ℝ) = (n * (n + 1)) / 2 := by
        exact fun n => by induction n <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at * ; linarith;
      rw [ ← h_sum, ← h_sum ] ; erw [ eq_sub_iff_add_eq' ] ; erw [ Finset.sum_Ioc_consecutive ] <;> norm_num;
      · rfl;
      · exact Nat.le_floor <| le_mul_of_one_le_right ( Nat.cast_nonneg _ ) <| Real.one_le_exp hα.le;
    rw [ h_sum ] ; ring;
  -- We'll use the fact that $\frac{\lfloor e^\alpha m \rfloor}{m}$ converges to $e^\alpha$ as $m \to \infty$.
  have h_floor : Filter.Tendsto (fun m : ℕ => (Nat.floor (m * (Real.exp α))) / (m : ℝ)) Filter.atTop (nhds (Real.exp α)) := by
    refine' Metric.tendsto_nhds.2 fun ε εpos => _;
    refine' Filter.eventually_atTop.mpr ⟨ ⌈ε⁻¹⌉₊ + 1, fun n hn => abs_lt.mpr ⟨ _, _ ⟩ ⟩ <;> nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ( ne_of_gt εpos ), Nat.lt_of_ceil_lt hn, Nat.floor_le ( show 0 ≤ ( n : ℝ ) * Real.exp α by positivity ), Nat.lt_floor_add_one ( ( n : ℝ ) * Real.exp α ), div_mul_cancel₀ ( ⌊ ( n : ℝ ) * Real.exp α⌋₊ : ℝ ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ];
  -- Let's simplify the expression inside the limit.
  suffices h_simp' : Filter.Tendsto (fun m : ℕ => (((Nat.floor (m * (Real.exp α))) / (m : ℝ)) ^ 2 - 1) / (2 * ((Real.exp (2 * α)) - 1)) + (((Nat.floor (m * (Real.exp α))) / (m : ℝ)) - 1) / (2 * ((Real.exp (2 * α)) - 1) * m)) Filter.atTop (nhds (1 / 2)) by
    refine Filter.Tendsto.congr' ?_ h_simp';
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm;
    field_simp [hm]
    ring;
  convert Filter.Tendsto.add ( Filter.Tendsto.div_const ( Filter.Tendsto.sub ( h_floor.pow 2 ) tendsto_const_nhds ) _ ) ( Filter.Tendsto.div_atTop ( h_floor.sub tendsto_const_nhds ) _ ) using 2 <;> norm_num [ Real.exp_add, two_mul, Real.exp_add ] ; ring_nf;
  · nlinarith [ Real.add_one_le_exp α, mul_inv_cancel₀ ( show -2 + Real.exp α ^ 2 * 2 ≠ 0 by nlinarith [ Real.add_one_le_exp α, Real.exp_pos α ] ) ];
  · exact Filter.Tendsto.const_mul_atTop ( by nlinarith [ Real.add_one_le_exp α ] ) tendsto_natCast_atTop_atTop

/-- Combining the existence of threshold with interval sum asymptotics. -/
theorem upper_bound_construction_hyp
    (Croot :
      ∀ (α : ℚ), 0 < α → ∀ (ε : ℝ), 0 < ε →
      ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
        ∃ C₁ : Finset ℕ,
          (∀ a ∈ C₁, (m : ℝ) < (a : ℝ) ∧ (a : ℝ) < (m : ℝ) * Real.exp (α : ℝ)) ∧
          let β : ℚ := α - C₁.sum (fun a => (1 : ℚ) / (a : ℚ))
          (|(β : ℝ) - 3 * (α : ℝ) * (Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ))| ≤
            ε * |Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ)|) ∧
          IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) β.den ∧
          (∀ (s t : ℕ), Nat.Coprime s t → 0 < t →
            (β : ℝ) / 2 < (s : ℝ) / (t : ℝ) →
            (s : ℝ) / (t : ℝ) ≤ (β : ℝ) →
            IsPowersmooth ((m : ℝ) ^ ((1 : ℝ) / 5)) t →
            ∃ C₂ : Finset ℕ,
              (∀ a ∈ C₂, (m : ℝ) * Real.exp (α : ℝ) < (a : ℝ) ∧
                (a : ℝ) < (1 + ε) * (m : ℝ) * Real.exp (α : ℝ)) ∧
              C₂.sum (fun a => (1 : ℚ) / (a : ℚ)) = (s : ℚ) / (t : ℚ)))
    (smooth_arith :
      ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ (ε : ℝ), 0 < ε →
      ∃ (x₀ : ℝ) (δ : ℝ), 0 < δ ∧ ∀ x : ℝ, x₀ ≤ x →
        δ * x ≤ ↑(Set.ncard {N : ℕ | (x : ℝ) < (N : ℝ) ∧ (N : ℝ) < (1 + ε) * x ∧
          (N : ℤ) ≡ a [ZMOD (b : ℤ)] ∧ IsSmooth (x ^ ε) N}))
    (α : ℚ) (hα : 0 < α) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∃ N : ℕ, 0 < N ∧
      (∀ n, N ≤ n → Admissible α m n) ∧
      (N : ℝ) ≤ (1 / 2 + ε) * (Real.exp (2 * (α : ℝ)) - 1) * (↑m) ^ 2 := by
  -- Choose ε₀ so that ε₀·m² is a small fraction of (e^{2α}-1)·m²
  set E := Real.exp (2 * (α : ℝ)) - 1 with hE_def
  have hE_pos : 0 < E := by
    simp only [hE_def]; linarith [Real.one_lt_exp_iff.mpr (by positivity : (0 : ℝ) < 2 * ↑α)]
  set ε₀ := ε * E / 8 with hε₀_def
  have hε₀_pos : 0 < ε₀ := by positivity
  -- Step 1: Apply admissible_above_threshold
  have h1 := admissible_above_threshold Croot smooth_arith α hα ε₀ hε₀_pos
  -- Step 2: interval sum asymptotics gives ΣI₁ ≤ (1/2 + ε/4)·E·m² eventually
  have h_asymp := interval_sum_asymp (α : ℝ) (by exact_mod_cast hα : (0 : ℝ) < ↑α)
  have h2 : ∀ᶠ m in atTop,
      (((Finset.Ioc m (⌊(m : ℝ) * Real.exp (α : ℝ)⌋₊)).sum id : ℕ) : ℝ) ≤
        (1/2 + ε/4) * E * (↑m) ^ 2 := by
    have := h_asymp.eventually (gt_mem_nhds (show (1 : ℝ)/2 < 1/2 + ε/4 by linarith))
    filter_upwards [this, Filter.eventually_gt_atTop 0] with m hm hm_pos
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < E * ↑m ^ 2)] at hm
    linarith
  -- Step 3: 78·m·e^α ≤ (ε/4)·E·m² eventually (since 78me^α = o(m²))
  have h3 : ∀ᶠ (m : ℕ) in atTop,
      78 * (↑m : ℝ) * Real.exp (↑α : ℝ) ≤ (ε/4) * E * (↑m) ^ 2 := by
    rw [Filter.eventually_atTop]
    refine ⟨⌈78 * Real.exp (↑α : ℝ) / (ε/4 * E)⌉₊ + 1, fun m hm => ?_⟩
    have hm_pos : (0 : ℝ) < ↑m := by
      have : (⌈78 * Real.exp (↑α : ℝ) / (ε/4 * E)⌉₊ + 1 : ℕ) ≥ 1 := by omega
      exact_mod_cast lt_of_lt_of_le (by omega : 0 < ⌈78 * Real.exp (↑α : ℝ) / (ε/4 * E)⌉₊ + 1) hm
    have h_ceil := Nat.le_ceil (78 * Real.exp (↑α : ℝ) / (ε/4 * E))
    have h_m_ge : (78 * Real.exp (↑α : ℝ) / (ε/4 * E)) ≤ (m : ℝ) := by
      have : ⌈78 * Real.exp (↑α : ℝ) / (ε/4 * E)⌉₊ ≤ m := by omega
      exact le_trans h_ceil (by exact_mod_cast this)
    have hεE_pos : (0 : ℝ) < ε/4 * E := by positivity
    have h1 : 78 * Real.exp (↑α : ℝ) ≤ ε/4 * E * (m : ℝ) := by
      rw [div_le_iff₀ hεE_pos] at h_m_ge; linarith
    nlinarith [sq_nonneg (↑m : ℝ)]
  filter_upwards [h1, h2, h3] with m ⟨X, hX_pos, hX_adm, hX_bound⟩ hI1_bound h78_bound
  refine ⟨X, hX_pos, hX_adm, ?_⟩
  calc (X : ℝ) ≤ ↑(((Finset.Ioc m (⌊↑m * rexp ↑α⌋₊)).sum id : ℕ)) +
      ε₀ * ↑m ^ 2 + 78 * ↑m * rexp ↑α := hX_bound
    _ ≤ (1/2 + ε/4) * E * ↑m ^ 2 + ε₀ * ↑m ^ 2 + (ε/4) * E * ↑m ^ 2 := by linarith
    _ = (1/2 + ε/4) * E * ↑m ^ 2 + (ε * E / 8) * ↑m ^ 2 + (ε/4) * E * ↑m ^ 2 := by rw [hε₀_def]
    _ = (1/2 + 5*ε/8) * E * ↑m ^ 2 := by ring
    _ ≤ (1/2 + ε) * E * ↑m ^ 2 := by nlinarith [sq_nonneg (↑m : ℝ)]

/-- Main Theorem: upper bound direction. -/
theorem upper_bound_construction (α : ℚ) (hα : 0 < α) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∃ N : ℕ, 0 < N ∧
      (∀ n, N ≤ n → Admissible α m n) ∧
      (N : ℝ) ≤ (1 / 2 + ε) * (Real.exp (2 * (α : ℝ)) - 1) * (↑m) ^ 2 := by
  have h := upper_bound_construction_hyp
    (fun α' hα' ε' hε' => by
      obtain ⟨m₀, hm₀⟩ := Croot_lemma α' hα' ε' hε'
      exact ⟨m₀, fun m hm => by
        obtain ⟨C₁, h⟩ := hm₀ m hm
        exact ⟨C₁, h.1, h.2.1, fun p k hp hk hpk => h.2.2.1 p k hp hk hpk,
          fun s t hst ht hβ1 hβ2 hps => by
            exact h.2.2.2 s t hst ht hβ1 hβ2 (fun p k hp hk hpk => hps p k hp hk hpk)⟩⟩)
    (fun a b hb ε' hε' => by
      obtain ⟨x₀, δ, hδ, hx⟩ := smoothinarithgeneral a b hb ε' hε'
      exact ⟨x₀, δ, hδ, fun x hx₀ => by exact_mod_cast hx x hx₀⟩)
    α hα ε hε
  exact h

/-
For a finset of distinct naturals all ≥ m, the sum is at least the sum of
the first |S| consecutive integers starting from m.
-/
lemma sum_ge_consecutive (S : Finset ℕ) (m : ℕ) (hm : ∀ a ∈ S, m ≤ a) :
    (S.card : ℝ) * m + (S.card : ℝ) * ((S.card : ℝ) - 1) / 2 ≤ ((S.sum id : ℕ) : ℝ) := by
  -- By induction on $|S|$, we can show that the sum of elements in $S$ is at least the sum of the first $|S|$ natural numbers starting from $m$.
  have h_ind : ∀ S : Finset ℕ, (∀ a ∈ S, m ≤ a) → S.sum id ≥ (Finset.range S.card).sum (fun i => m + i) := by
    -- By ordering the elements of $S$ as $a_1 < a_2 < \cdots < a_k$, we have $a_i \geq m + i - 1$ for all $i$.
    have h_order : ∀ S : Finset ℕ, (∀ a ∈ S, m ≤ a) → ∃ f : Fin S.card → ℕ, StrictMono f ∧ ∀ i, f i ∈ S ∧ m ≤ f i ∧ f i ≥ m + i := by
      intros S hm
      obtain ⟨f, hf⟩ : ∃ f : Fin S.card → ℕ, StrictMono f ∧ ∀ i, f i ∈ S := by
        exact ⟨ fun i => S.orderEmbOfFin rfl i, by simp +decide [ StrictMono ], fun i => S.orderEmbOfFin_mem rfl _ ⟩;
      refine' ⟨ f, hf.1, fun i => ⟨ hf.2 i, hm _ ( hf.2 i ), _ ⟩ ⟩;
      induction' i with i ih;
      induction' i with i ih;
      · exact hm _ ( hf.2 _ );
      · exact lt_of_le_of_lt ( ‹∀ ( ih : i < #S ), f ⟨ i, ih ⟩ ≥ m + i› ( Nat.lt_of_succ_lt ih ) ) ( hf.1 ( Nat.lt_succ_self _ ) );
    -- By ordering the elements of $S$ as $a_1 < a_2 < \cdots < a_k$, we have $a_i \geq m + i - 1$ for all $i$. Therefore, the sum of the elements in $S$ is at least the sum of the first $k$ natural numbers starting from $m$.
    intros S hS
    obtain ⟨f, hf_mono, hf⟩ := h_order S hS
    have h_sum : S.sum id ≥ Finset.sum (Finset.image f Finset.univ) id := by
      exact Finset.sum_le_sum_of_subset ( Finset.image_subset_iff.mpr fun i _ => hf i |>.1 );
    rw [ Finset.sum_image <| by intros i hi j hj hij; exact hf_mono.injective hij ] at h_sum;
    simpa only [ Finset.sum_range ] using h_sum.trans' ( Finset.sum_le_sum fun i _ => hf i |>.2.2 );
  convert Nat.cast_le.mpr ( h_ind S hm ) using 1 ; norm_num [ Finset.sum_add_distrib ] ; ring_nf;
  · exact Nat.recOn ( Finset.card S ) ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] ; linarith;
  · infer_instance;
  · infer_instance;
  · infer_instance

/-
For a finset of distinct naturals all ≥ m (with m ≥ 1), the reciprocal sum
is at most the reciprocal sum of the first |S| consecutive integers from m.
-/
lemma recip_sum_le_consecutive (S : Finset ℕ) (m : ℕ) (hm : ∀ a ∈ S, m ≤ a)
    (hm0 : 0 < m) :
    (S.sum (fun a => (1 : ℝ) / a) : ℝ) ≤
    (Finset.range S.card).sum (fun j => (1 : ℝ) / (↑m + ↑j)) := by
  -- Let's denote the elements of $S$ as $a_1, a_2, \ldots, a_k$ where $a_1 < a_2 < \cdots < a_k$.
  obtain ⟨a, ha⟩ : ∃ a : Fin (Finset.card S) → ℕ, StrictMono a ∧ ∀ i, a i ∈ S := by
    exact ⟨ fun i => S.orderEmbOfFin rfl i, by simp +decide [ StrictMono ], fun i => S.orderEmbOfFin_mem rfl _ ⟩;
  -- Since $a$ is strictly monotone, we have $a i ≥ m + i$ for all $i$.
  have h_ai_ge : ∀ i, a i ≥ m + i := by
    -- We proceed by induction on $i$.
    intro i
    induction' i with i ih;
    induction' i with i ih;
    · exact hm _ ( ha.2 _ );
    · exact lt_of_le_of_lt ( ‹∀ ( ih : i < Finset.card S ), a ⟨ i, ih ⟩ ≥ m + i› ( Nat.lt_of_succ_lt ih ) ) ( ha.1 ( Nat.lt_succ_self _ ) );
  -- Applying the inequality $a i ≥ m + i$ to each term in the sum, we get $\sum_{a \in S} \frac{1}{a} ≤ \sum_{i : Fin #S} \frac{1}{m + i}$.
  have h_sum_le : (∑ a ∈ S, (1 / (a : ℝ))) ≤ (∑ i : Fin #S, (1 / (a i : ℝ))) := by
    have h_sum_le : (∑ a ∈ Finset.image a Finset.univ, (1 / (a : ℝ))) ≤ (∑ i : Fin #S, (1 / (a i : ℝ))) := by
      rw [ Finset.sum_image <| by intros i hi j hj hij; exact ha.1.injective hij ];
    rwa [ Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => ha.2 i ) ( by rw [ Finset.card_image_of_injective _ ha.1.injective, Finset.card_fin ] ) ] at h_sum_le;
  exact h_sum_le.trans ( by rw [ Finset.sum_range ] ; exact Finset.sum_le_sum fun i _ => by gcongr ; exact_mod_cast h_ai_ge i )

/-
For n ≥ 2, we have 1/n ≤ log(n) - log(n-1).
-/
lemma inv_le_log_sub (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / n ≤ Real.log n - Real.log (n - 1) := by
  rw [ ← Real.log_div ( by positivity ) ( by exact ne_of_gt ( by norm_num; linarith ) ) ];
  convert Real.one_sub_inv_le_log_of_pos _ using 1 <;> ring_nf;
  · norm_num [ show n ≠ 0 by linarith ];
    linarith [ inv_mul_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ) ];
  · exact mul_pos ( by positivity ) ( inv_pos.mpr ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast ] ) )

/-
The partial harmonic sum ∑_{j=0}^{k-1} 1/(m+j) is bounded above by
log((m+k-1)/(m-1)) for m ≥ 2 and k ≥ 1.
-/
lemma partial_harmonic_le_log (m k : ℕ) (hm : 2 ≤ m) (_hk : 1 ≤ k) :
    (Finset.range k).sum (fun j => (1 : ℝ) / (↑m + ↑j)) ≤
    Real.log (↑(m + k) - 1) - Real.log (↑m - 1) := by
  -- By the properties of logarithms and the inequality for each term in the sum, we can bound the sum from above.
  have h_telescope : ∑ x ∈ Finset.range k, (Real.log (m + x) - Real.log (m + x - 1)) = Real.log (m + k - 1) - Real.log (m - 1) := by
    convert Finset.sum_range_sub _ _ using 3 <;> push_cast <;> ring_nf;
  convert Finset.sum_le_sum fun i hi => inv_le_log_sub ( m + i ) ?_ using 2 <;> norm_num at * ; ring_nf at * ; aesop;
  linarith

/-
If S is a finset of distinct naturals all ≥ m (m ≥ 2) whose reciprocal sum
(in ℝ) is at least α > 0, then |S| ≥ (m-1)(e^α - 1).
-/
lemma card_ge_of_recip_sum_ge (S : Finset ℕ) (α : ℝ) (m : ℕ)
    (hα : 0 < α) (hm : 2 ≤ m)
    (hge : ∀ a ∈ S, m ≤ a)
    (hrecip : α ≤ S.sum (fun a => (1 : ℝ) / a)) :
    (↑m - 1) * (Real.exp α - 1) ≤ (S.card : ℝ) := by
  have := partial_harmonic_le_log m S.card hm ( Nat.pos_of_ne_zero ?_ );
  · -- From the inequality α ≤ log((m + k - 1) / (m - 1)), we can exponentiate both sides to get exp(α) ≤ (m + k - 1) / (m - 1).
    have h_exp : Real.exp α ≤ (m + S.card - 1) / (m - 1) := by
      convert Real.exp_le_exp.mpr ( hrecip.trans <| recip_sum_le_consecutive S m hge ( by linarith ) |> le_trans <| this ) using 1;
      rw [ Real.exp_sub, Real.exp_log, Real.exp_log ] <;> push_cast <;> ring_nf <;> nlinarith [ show ( m : ℝ ) ≥ 2 by norm_cast ];
    rw [ le_div_iff₀ ] at h_exp <;> nlinarith [ show ( m : ℝ ) ≥ 2 by norm_cast ];
  · -- If S were empty, then the sum of reciprocals would be zero, contradicting α being positive. Therefore, S must have at least one element, so its cardinality is positive.
    by_contra h_empty
    have h_sum_zero : ∑ a ∈ S, (1 : ℝ) / a = 0 := by
      aesop;
    linarith

/-
Any admissible representation has sum at least Cm + C(C-1)/2
where C = (m-1)*(exp(α) - 1).
-/
lemma admissible_sum_ge (α : ℚ) (m n : ℕ) (hα : 0 < α) (hm : 2 ≤ m)
    (hadm : Admissible α m n) :
    let C := (↑m - 1 : ℝ) * (Real.exp (↑α : ℝ) - 1)
    C * ↑m + C * (C - 1) / 2 ≤ (n : ℝ) := by
  -- By definition of admissibility, there exists a finite set of distinct positive integers all at least m whose sum is n and whose reciprocals sum to α.
  obtain ⟨S, hS⟩ := hadm;
  -- By `card_ge_of_recip_sum_ge`, we have that `S.card ≥ (m - 1) * (Real.exp α - 1)`.
  have h_card : (S.card : ℝ) ≥ (m - 1) * (Real.exp α - 1) := by
    apply_rules [ card_ge_of_recip_sum_ge ];
    · positivity;
    · exact hS.1;
    · aesop;
  -- By `sum_ge_consecutive`, we have that `n ≥ S.card * m + S.card * (S.card - 1) / 2`.
  have h_sum : (n : ℝ) ≥ (S.card : ℝ) * m + (S.card : ℝ) * ((S.card : ℝ) - 1) / 2 := by
    have := sum_ge_consecutive S m hS.1; aesop;
  nlinarith [ show ( m : ℝ ) ≥ 2 by norm_cast, show ( Real.exp α - 1 : ℝ ) ≥ 0 by exact sub_nonneg_of_le <| Real.one_le_exp <| by positivity, mul_le_mul_of_nonneg_left h_card <| show ( 0 : ℝ ) ≤ m by positivity, mul_le_mul_of_nonneg_left h_card <| show ( 0 : ℝ ) ≤ Real.exp α - 1 by exact sub_nonneg_of_le <| Real.one_le_exp <| by positivity ]

/-
If the threshold nAlphaM exists (is positive), then it is admissible,
hence satisfies the admissible sum lower bound.
-/
lemma nAlphaM_ge_lower_bound (α : ℚ) (m : ℕ) (hα : 0 < α) (hm : 2 ≤ m)
    (hpos : 0 < nAlphaM α m) :
    let C := (↑m - 1 : ℝ) * (Real.exp (↑α : ℝ) - 1)
    C * ↑m + C * (C - 1) / 2 ≤ (nAlphaM α m : ℝ) := by
  -- Apply the admissible sum lower bound to nAlphaM.
  apply admissible_sum_ge α m (nAlphaM α m) hα hm;
  obtain ⟨ N, hN ⟩ := Nat.sInf_mem ( show { N : ℕ | 0 < N ∧ ∀ n, N ≤ n → Admissible α m n }.Nonempty from Nat.nonempty_of_pos_sInf <| by assumption ) ; aesop;

/-
The lower bound Cm + C(C-1)/2 with C = (m-1)*(e^α - 1) is
asymptotically (1/2)(e^{2α} - 1)m².
-/
lemma lower_bound_ratio_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun m : ℕ =>
        let C := (↑m - 1) * (Real.exp α - 1)
        (C * ↑m + C * (C - 1) / 2) /
          ((Real.exp (2 * α) - 1) * (↑m) ^ 2))
      atTop (nhds (1 / 2)) := by
  -- After expanding and simplifying, the expression becomes $\frac{1}{2} - \frac{2e + 1}{2(e + 1)} \cdot \frac{1}{m} + \frac{e}{2(e + 1)} \cdot \frac{1}{m^2}$.
  have h_simplified : ∀ m : ℕ, m ≥ 2 → (let C := ((m - 1) * (Real.exp α - 1));
    (C * m + C * (C - 1) / 2) / ((Real.exp (2 * α) - 1) * m^2)) = 1 / 2 - (2 * Real.exp α + 1) / (2 * (Real.exp α + 1)) * (1 / (m : ℝ)) + (Real.exp α) / (2 * (Real.exp α + 1)) * (1 / (m : ℝ)^2) := by
      field_simp;
      intro m hm; rw [ div_eq_iff ] <;> rw [ two_mul, Real.exp_add ] <;> ring_nf ; nlinarith [ Real.add_one_le_exp α, Real.exp_pos α ] ;
  -- As $m$ tends to infinity, the terms $\frac{1}{m}$ and $\frac{1}{m^2}$ tend to $0$.
  have h_zero_terms : Filter.Tendsto (fun m : ℕ => (1 / (m : ℝ))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun m : ℕ => (1 / (m : ℝ)^2)) Filter.atTop (nhds 0) := by
    exact ⟨ tendsto_one_div_atTop_nhds_zero_nat, tendsto_const_nhds.div_atTop <| Filter.tendsto_pow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ⟩;
  rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_ge_atTop 2 ] with m hm; rw [ h_simplified m hm ] ) ] ; simpa using Filter.Tendsto.add ( tendsto_const_nhds.sub ( h_zero_terms.1.const_mul _ ) ) ( h_zero_terms.2.const_mul _ ) ;

/-- The threshold nAlphaM exists for large m, derived from the upper bound construction. -/
lemma nAlphaM_eventually_pos (α : ℚ) (hα : 0 < α) :
    ∀ᶠ m in atTop, 0 < nAlphaM α m := by
  have h := upper_bound_construction α hα 1 one_pos
  filter_upwards [h] with m ⟨N, hN_pos, hN_adm, _⟩
  have hne : {N : ℕ | 0 < N ∧ ∀ n, N ≤ n → Admissible α m n}.Nonempty :=
    ⟨N, hN_pos, hN_adm⟩
  exact (Nat.sInf_mem hne).1

/-
Lower bound: for all ε > 0, eventually
n_{α,m} / ((e^{2α} - 1) * m²) ≥ 1/2 - ε.
-/
theorem explicit_graham_lb (α : ℚ) (hα : 0 < α) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
      1 / 2 - ε < (nAlphaM α m : ℝ) /
        ((Real.exp (2 * (α : ℝ)) - 1) * (↑m) ^ 2) := by
  intro ε hε_pos
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℕ, ∀ m ≥ M₁, (let C := ((m - 1 : ℝ) * (Real.exp (α : ℝ) - 1))
    (C * (m : ℝ) + C * (C - 1) / 2) / ((Real.exp (2 * α) - 1) * (m : ℝ) ^ 2)) > 1 / 2 - ε := by
      have := lower_bound_ratio_tendsto α ( mod_cast hα ) |> fun h => h.eventually ( lt_mem_nhds <| show 1 / 2 - ε < 1 / 2 by linarith ) ; aesop;
  -- By nAlphaM_eventually_pos, there exists M₂ such that for m ≥ M₂, nAlphaM > 0.
  obtain ⟨M₂, hM₂⟩ : ∃ M₂ : ℕ, ∀ m ≥ M₂, 0 < nAlphaM α m := by
    exact Filter.eventually_atTop.mp ( nAlphaM_eventually_pos α hα );
  -- By nAlphaM_ge_lower_bound, for m ≥ max(M₁, max(M₂, 2)), we have nAlphaM ≥ B(m).
  have h_ge_lower_bound : ∀ m ≥ max M₁ (max M₂ 2), (let C := ((m - 1 : ℝ) * (Real.exp (α : ℝ) - 1))
    (C * (m : ℝ) + C * (C - 1) / 2)) ≤ (nAlphaM α m : ℝ) := by
      intros m hm
      apply nAlphaM_ge_lower_bound α m hα (by
      linarith [ le_max_right M₁ ( max M₂ 2 ), le_max_right M₂ 2 ]) (by
      exact hM₂ m ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hm ));
  filter_upwards [ Filter.eventually_ge_atTop ( max M₁ ( max M₂ 2 ) ), Filter.eventually_gt_atTop 0 ] with m hm₁ hm₂ using lt_of_lt_of_le ( hM₁ m ( le_trans ( le_max_left _ _ ) hm₁ ) ) ( div_le_div_of_nonneg_right ( h_ge_lower_bound m hm₁ ) ( mul_nonneg ( sub_nonneg.mpr <| Real.one_le_exp <| by positivity ) <| sq_nonneg _ ) )

/-
Upper bound: for all ε > 0, eventually
n_{α,m} / ((e^{2α} - 1) * m²) < 1/2 + ε.
-/
theorem explicit_graham_ub (α : ℚ) (hα : 0 < α) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
      (nAlphaM α m : ℝ) /
        ((Real.exp (2 * (α : ℝ)) - 1) * (↑m) ^ 2) < 1 / 2 + ε := by
  intro ε hε
  have h := upper_bound_construction α hα (ε / 2) (by linarith)
  filter_upwards [h, Filter.eventually_gt_atTop 0] with m ⟨N, hN_pos, hN_adm, hN_bound⟩ hm_pos
  have hle : nAlphaM α m ≤ N := Nat.sInf_le ⟨hN_pos, hN_adm⟩
  have hexp_pos : (0 : ℝ) < Real.exp (2 * (α : ℝ)) - 1 := by
    linarith [Real.one_lt_exp_iff.mpr (by positivity : (0 : ℝ) < 2 * (α : ℝ))]
  have hm2_pos : (0 : ℝ) < (↑m) ^ 2 := by positivity
  have hdenom_pos : (0 : ℝ) < (Real.exp (2 * (α : ℝ)) - 1) * (↑m) ^ 2 := by positivity
  calc (nAlphaM α m : ℝ) / ((Real.exp (2 * ↑α) - 1) * ↑m ^ 2)
      ≤ (N : ℝ) / ((Real.exp (2 * ↑α) - 1) * ↑m ^ 2) := by
        apply div_le_div_of_nonneg_right (by exact_mod_cast hle) (le_of_lt hdenom_pos)
    _ ≤ ((1 / 2 + ε / 2) * (Real.exp (2 * ↑α) - 1) * ↑m ^ 2) /
          ((Real.exp (2 * ↑α) - 1) * ↑m ^ 2) := by
        apply div_le_div_of_nonneg_right hN_bound (le_of_lt hdenom_pos)
    _ = 1 / 2 + ε / 2 := by
        field_simp
    _ < 1 / 2 + ε := by linarith

/-- For every fixed positive rational `α`, we have
`n_{α,m} ∼ (1/2)(e^{2α} - 1) m²` as `m → ∞`. -/
theorem explicit_graham (α : ℚ) (hα : 0 < α) :
    Tendsto
      (fun m : ℕ => (nAlphaM α m : ℝ) /
        ((Real.exp (2 * (α : ℝ)) - 1) * (m : ℝ) ^ 2))
      atTop (nhds (1 / 2)) := by
  rw [tendsto_order]
  constructor
  · -- Lower bound direction: for a < 1/2, eventually a < ratio
    intro a ha
    have hε : (0 : ℝ) < 1 / 2 - a := by linarith
    have := explicit_graham_lb α hα (1 / 2 - a) hε
    filter_upwards [this] with m hm
    linarith
  · -- Upper bound direction: for b > 1/2, eventually ratio < b
    intro b hb
    have hε : (0 : ℝ) < b - 1 / 2 := by linarith
    have := explicit_graham_ub α hα (b - 1 / 2) hε
    filter_upwards [this] with m hm
    linarith

#print axioms explicit_graham
