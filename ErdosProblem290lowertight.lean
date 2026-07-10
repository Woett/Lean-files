import Mathlib

/-!
Let `r : ℕ → ℤ` be periodic with period `t` and not identically zero.  Writing
the partial sum `∑_{i=a}^{b} r_i / i` as a reduced fraction `u_{a,b} / v_{a,b}`
with `v_{a,b} > 0`, the main theorem below states that for every `ε > 0` there
are infinitely many `a` admitting some `b` with
`a < b < a + (1+ε)·t(t+1)·φ(t)·log a` and `v_{a,b} < v_{a,b-1}`.

This result is proven in

W. van Doorn, On the non-monotonicity of the denominator of generalized harmonic
sums. arXiv:2411.03073 (2024).

The file is self-contained except for a single black box,
`ap_prime_product_lower_bound` (a lower bound, coming from the prime number
theorem for arithmetic progressions, on products of primes in a residue class).

Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) deserves the credit
for obtaining this formalization.

Lean version: leanprover/lean4:v4.28.0
-/

open scoped BigOperators
open Filter

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- The partial sum `S_{a,b} = ∑_{i=a}^{b} r_i / i ∈ ℚ`. -/
noncomputable def Ssum (r : ℕ → ℤ) (a b : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc a b, (r i : ℚ) / (i : ℚ)

/-- The reduced positive denominator `v_{a,b}` of `S_{a,b}`. -/
noncomputable def vden (r : ℕ → ℤ) (a b : ℕ) : ℕ := (Ssum r a b).den

/-- `L_{a,b} = lcm { i : a ≤ i ≤ b and r_i ≠ 0 }` (empty lcm `= 1`). -/
noncomputable def Lden (r : ℕ → ℤ) (a b : ℕ) : ℕ :=
  ((Finset.Icc a b).filter (fun i => r i ≠ 0)).lcm id

/-- The integer `X_{a,b} = L_{a,b} · S_{a,b} = ∑_{i} (L_{a,b}/i) r_i`. -/
noncomputable def Xnum (r : ℕ → ℤ) (a b : ℕ) : ℤ :=
  ∑ i ∈ (Finset.Icc a b).filter (fun i => r i ≠ 0),
    ((Lden r a b : ℤ) / (i : ℤ)) * r i

/-- `g_{a,b} = gcd(L_{a,b}, X_{a,b})`. -/
noncomputable def gfun (r : ℕ → ℤ) (a b : ℕ) : ℕ :=
  Nat.gcd (Lden r a b) (Xnum r a b).natAbs

/-- `𝓑(a) = { b > a : v_{a,b} < v_{a,b-1} }`. -/
def Bset (r : ℕ → ℤ) (a : ℕ) : Set ℕ := {b | a < b ∧ vden r a b < vden r a (b - 1)}

/-- `R = max_{1 ≤ i ≤ t} |r i|`. -/
def Rmax (r : ℕ → ℤ) (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).sup (fun i => (r i).natAbs)

/-
Let `M ∈ ℕ` with `gcd(A, M) = 1`, `0 < α < β`, and `ε > 0`.  Then for all
sufficiently large real `X`, the product of the primes `q` in `(αX, βX)` with
`q ≡ A (mod M)` is at least `exp(((β-α)/φ(M) - ε) X)`.

This is the only statement in the development that is left unproved.  It follows
from the prime number theorem for arithmetic progressions.
-/
axiom ap_prime_product_lower_bound
    (M : ℕ) (A : ℤ) (hM : 0 < M) (hA : Int.gcd A M = 1)
    (α β : ℝ) (hα : 0 < α) (hab : α < β) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      Real.exp (((β - α) / (Nat.totient M) - ε) * X) ≤
        ∏ q ∈ (Finset.range (⌊β * X⌋₊ + 1)).filter
          (fun q => Nat.Prime q ∧ (α * X < (q : ℝ)) ∧ ((q : ℝ) < β * X) ∧
            (q : ℤ) ≡ A [ZMOD (M : ℤ)]),
          (q : ℝ)

/-- Every nonzero index `i ∈ [a,b]` divides `L_{a,b}`. -/
lemma dvd_Lden (r : ℕ → ℤ) (a b i : ℕ) (hi : i ∈ Finset.Icc a b) (hr : r i ≠ 0) :
    i ∣ Lden r a b := by
  have : i ∈ ((Finset.Icc a b).filter (fun i => r i ≠ 0)) := by simp [hi, hr]
  have := Finset.dvd_lcm (f := id) this
  simpa using this

/-
If all indices in `[a,b]` are positive then `L_{a,b} ≠ 0`.
-/
lemma Lden_ne_zero (r : ℕ → ℤ) (a b : ℕ) (hpos : ∀ i ∈ Finset.Icc a b, 0 < i) :
    Lden r a b ≠ 0 := by
  have h_pos : ∀ s : Finset ℕ, (∀ i ∈ s, 0 < i) → s.lcm id ≠ 0 := by
    simp +contextual [ Finset.lcm_eq_zero_iff ];
    exact fun s hs => fun h => by simpa using hs 0 h;
  exact h_pos _ fun i hi => hpos i <| Finset.mem_filter.mp hi |>.1

/-- Summation form of `X_{a,b}` over the whole interval `[a,b]`, using natural-number
division (equal because every nonzero index divides `L_{a,b}`). -/
lemma Xnum_sum (r : ℕ → ℤ) (a b : ℕ) :
    Xnum r a b = ∑ i ∈ Finset.Icc a b, r i * ((Lden r a b / i : ℕ) : ℤ) := by
  unfold Xnum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hr : r i = 0
  · simp [hr]
  · rw [if_pos hr, mul_comm, Int.natCast_div]

/-- Summation form of `X_{a,b}` over `[a,b]` using integer division. -/
lemma Xnum_sum_int (r : ℕ → ℤ) (a b : ℕ) :
    Xnum r a b = ∑ i ∈ Finset.Icc a b, r i * ((Lden r a b : ℤ) / (i : ℤ)) := by
  unfold Xnum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hr : r i = 0 <;> simp [hr, mul_comm]

/-- `g_{a,b}` equals the integer gcd of `X_{a,b}` and `L_{a,b}`. -/
lemma gfun_eq (r : ℕ → ℤ) (a b : ℕ) :
    gfun r a b = Int.gcd (Xnum r a b) (Lden r a b) := by
  unfold gfun Int.gcd
  rw [Int.natAbs_natCast, Nat.gcd_comm]

/-
`X_{a,b} = L_{a,b} · S_{a,b}` as rationals (needs all indices positive).
-/
lemma Xnum_eq (r : ℕ → ℤ) (a b : ℕ) (hpos : ∀ i ∈ Finset.Icc a b, 0 < i) :
    (Xnum r a b : ℚ) = (Lden r a b : ℚ) * Ssum r a b := by
  rw [Xnum_sum]; unfold Ssum;
  push_cast [ Finset.mul_sum _ _ _ ];
  refine Finset.sum_congr rfl fun i hi => ?_;
  by_cases hi' : r i = 0 <;> simp_all +decide [ mul_comm ];
  rw [ Int.cast_div ( mod_cast dvd_Lden r a b i ( Finset.mem_Icc.mpr hi ) hi' ) ( by norm_cast; linarith [ hpos i hi.1 hi.2 ] ) ] ; push_cast ; ring

/-
`S_{a,b} = X_{a,b} / L_{a,b}`.
-/
lemma Ssum_eq_div (r : ℕ → ℤ) (a b : ℕ) (hpos : ∀ i ∈ Finset.Icc a b, 0 < i) :
    Ssum r a b = (Xnum r a b : ℚ) / (Lden r a b : ℚ) := by
  rw [ eq_div_iff ];
  · rw [ mul_comm, Xnum_eq r a b hpos ];
  · exact_mod_cast Lden_ne_zero r a b hpos

/-
`g_{a,b} ∣ L_{a,b}`.
-/
lemma gfun_dvd_Lden (r : ℕ → ℤ) (a b : ℕ) : gfun r a b ∣ Lden r a b := by
  exact Nat.gcd_dvd_left _ _

/-
The reduced denominator formula `v_{a,b} = L_{a,b} / g_{a,b}`.
-/
lemma vden_eq (r : ℕ → ℤ) (a b : ℕ) (hpos : ∀ i ∈ Finset.Icc a b, 0 < i) :
    vden r a b = Lden r a b / gfun r a b := by
  rw [ @vden, gfun_eq ];
  rw [ Ssum_eq_div r a b hpos, div_eq_mul_inv ];
  erw [ Rat.mul_den ] ; norm_num;
  split_ifs <;> simp_all +decide [ Lden_ne_zero ];
  rw [ Int.sign_eq_one_of_pos ( Int.natCast_pos.mpr ( Nat.pos_of_ne_zero ( Lden_ne_zero r a b fun i hi => hpos i ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2 ) ) ) ) ] ; norm_num [ Int.gcd, Int.natAbs_mul ]

/-
Equal residues give equal values.
-/
lemma rper_congr (r : ℕ → ℤ) (t : ℕ) (hper : ∀ i, r (i + t) = r i) {i j : ℕ}
    (h : i ≡ j [MOD t]) : r i = r j := by
  rw [ ← Nat.mod_add_div i t, ← Nat.mod_add_div j t, h ];
  induction i / t <;> induction j / t <;> simp_all +decide [ Nat.mul_succ, ← add_assoc ];
  exact Nat.recOn ( j / t ) rfl fun n hn => by rw [ Nat.mul_succ, ← add_assoc, hper, hn ] ;

/-- If some index in `[a,b]` is a nonzero multiple of `d`, then `d ∣ L_{a,b}`. -/
lemma dvd_Lden_of_exists (r : ℕ → ℤ) (a b d : ℕ)
    (h : ∃ i ∈ Finset.Icc a b, d ∣ i ∧ r i ≠ 0) : d ∣ Lden r a b := by
  obtain ⟨i, hi, hd, hr⟩ := h
  exact hd.trans (dvd_Lden r a b i hi hr)

/-
`Rmax` bounds each `|r i|` for `i` a positive residue.
-/
lemma abs_r_le_Rmax (r : ℕ → ℤ) (t : ℕ) (hper : ∀ i, r (i + t) = r i) (ht : 1 ≤ t) (i : ℕ) :
    (r i).natAbs ≤ Rmax r t := by
  -- Let's denote `j` as `i % t` if `i % t ≠ 0`, otherwise `j = t`.
  set j := if i % t = 0 then t else i % t;
  -- By definition of $j$, we know that $r i = r j$ and $j \in [1, t]$.
  have h_rj : r i = r j := by
    have h_r_eq : r i = r (i % t) := by
      rw [ ← Nat.mod_add_div i t, Function.Periodic.map_mod_nat hper ];
    grind +locals
  have h_j_range : 1 ≤ j ∧ j ≤ t := by
    simp +zetaDelta at *;
    split_ifs <;> [ exact ⟨ ht, le_rfl ⟩ ; exact ⟨ Nat.pos_of_ne_zero ‹_›, Nat.le_of_lt <| Nat.mod_lt _ ht ⟩ ];
  exact h_rj.symm ▸ Finset.le_sup ( f := fun i => Int.natAbs ( r i ) ) ( Finset.mem_Icc.mpr h_j_range )

/-
A squarefree number all of whose prime factors are `≡ 1 (mod t)` is itself `≡ 1 (mod t)`.
-/
lemma sqfree_prod_congr_one (Q t : ℕ) (hsf : Squarefree Q)
    (h : ∀ q, Nat.Prime q → q ∣ Q → q ≡ 1 [MOD t]) : Q ≡ 1 [MOD t] := by
  -- By definition of squarefree, Q can be written as a product of distinct primes.
  have h_factor : Q = Finset.prod (Q.primeFactors) (fun p => p) := by
    rw [ Nat.prod_primeFactors_of_squarefree hsf ];
  convert Nat.ModEq.prod fun p hp => h p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) using 1;
  norm_num

/-
Characterisation of the multiples of `q` inside `[M - h·N, M - 1]`: they are exactly the
`M - i·q` for `1 ≤ i ≤ h`.
-/
lemma mult_char (M q N h : ℕ) (hh : 1 ≤ h) (hq0 : 0 < q) (hq : q < N)
    (hqbig : h * N < (h + 1) * q) (hqM : q ∣ M) (hMN : h * N ≤ M) (n : ℕ)
    (hn1 : M - h * N ≤ n) (hn2 : n ≤ M - 1) (hqn : q ∣ n) :
    ∃ i, 1 ≤ i ∧ i ≤ h ∧ n = M - i * q := by
  obtain ⟨ k, hk ⟩ := hqn;
  obtain ⟨ m, hm ⟩ := hqM;
  refine' ⟨ m - k, _, _, _ ⟩ <;> subst_vars;
  · exact Nat.sub_pos_of_lt ( by nlinarith [ Nat.sub_add_cancel ( show 1 ≤ q * m from by nlinarith ) ] );
  · rw [ tsub_le_iff_left ];
    rw [ tsub_le_iff_right ] at hn1 ; nlinarith;
  · exact eq_tsub_of_add_eq ( by nlinarith only [ Nat.sub_add_cancel ( show k ≤ m from by nlinarith [ Nat.sub_add_cancel ( show 1 ≤ q * m from by nlinarith ) ] ) ] )

/-
Characterisation of the multiples of `q` inside `[M - h·N, M - 1]` in the regime `N < q`:
they are exactly the `M - i·q` for `1 ≤ i < h`.
-/
lemma mult_char_gt (M q N h : ℕ) (hh : 1 ≤ h) (hN0 : 0 < N) (hqN : N < q)
    (hqM : q ∣ M) (hMN : h * N ≤ M) (n : ℕ)
    (hn1 : M - h * N ≤ n) (hn2 : n ≤ M - 1) (hqn : q ∣ n) :
    ∃ i, 1 ≤ i ∧ i < h ∧ n = M - i * q := by
  have hMpos : 0 < M := lt_of_lt_of_le (Nat.mul_pos hh hN0) hMN
  have hnM : n < M := lt_of_le_of_lt hn2 (Nat.sub_lt hMpos one_pos)
  have hdvd : q ∣ (M - n) := (Nat.dvd_sub hqM hqn)
  obtain ⟨i, hi⟩ := hdvd
  refine ⟨i, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; simp at hi; omega
    · exact h0
  · have h1 : i * q = M - n := by rw [mul_comm]; omega
    have h2 : M - n ≤ h * N := by omega
    have h3 : h * N < h * q := (Nat.mul_lt_mul_left hh).2 hqN
    nlinarith [h1, h2, h3]
  · have h1 : i * q = M - n := by rw [mul_comm]; omega
    omega

/-
Periodic shift: `r (M - i·q) = r (e - i)` when `M ≡ e` and `q ≡ 1 (mod t)`.
-/
lemma r_shift (r : ℕ → ℤ) (t : ℕ) (hper : ∀ i, r (i + t) = r i) (M i q e : ℕ)
    (hMe : M ≡ e [MOD t]) (hq1 : q ≡ 1 [MOD t]) (hle : i ≤ e) (hiqM : i * q ≤ M) :
    r (M - i * q) = r (e - i) := by
  convert rper_congr r t hper _;
  simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]

/-
A squarefree `Q` divides `L` as soon as each of its prime factors does.
-/
lemma sqfree_dvd_of_forall_prime_dvd (Q L : ℕ) (hsf : Squarefree Q)
    (h : ∀ p, Nat.Prime p → p ∣ Q → p ∣ L) : Q ∣ L := by
  have h_prod_ne_zero : ∏ p ∈ Nat.primeFactors Q, p = Q := by
    exact Nat.prod_primeFactors_of_squarefree hsf;
  rw [ ← h_prod_ne_zero ];
  convert Finset.lcm_dvd fun p hp => h p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) using 1;
  have h_lcm_eq_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Finset.lcm S (fun p => p) = ∏ p ∈ S, p := by
    intros S hS; induction S using Finset.induction <;> simp_all +decide ;
    exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop;
  rw [ h_lcm_eq_prod fun p hp => Nat.prime_of_mem_primeFactors hp ]

/-
The `q`-adic valuation of a finset lcm is the sup of the valuations.
-/
lemma factorization_lcm_sup (q : ℕ) (s : Finset ℕ) (hs : ∀ i ∈ s, 0 < i) :
    (s.lcm id).factorization q = s.sup (fun i => i.factorization q) := by
  induction' s using Finset.induction with a s has ih;
  · simp +decide [ Finset.lcm ];
  · rw [ Finset.lcm_insert ];
    erw [ Nat.factorization_lcm ] <;> simp_all +decide [ ne_of_gt ];
    exact fun h => by simpa using hs.2 0 h;

/-
Adding a top index `b` that is either zero-valued or already divides the lcm does not
change `L`.
-/
lemma Lden_top_eq (r : ℕ → ℤ) (a b : ℕ) (hab : a < b)
    (h : r b = 0 ∨ b ∣ Lden r a (b - 1)) :
    Lden r a b = Lden r a (b - 1) := by
  rcases h with ( h | h ) <;> simp_all +decide [ Lden ];
  · congr 1 with i ; rcases b with ( _ | _ | b ) <;> simp_all +decide [ Finset.mem_Icc ]; all_goals grind;
  · rw [ show Finset.Icc a b = Finset.Icc a ( b - 1 ) ∪ { b } from ?_, Finset.filter_union ];
    · by_cases hb : r b = 0 <;> simp_all +decide [ Finset.filter_singleton ];
      exact Nat.dvd_antisymm ( Nat.lcm_dvd h ( dvd_refl _ ) ) ( Nat.dvd_lcm_right _ _ );
    · grind

/-
If `q ∣ lcm s` but `q ∤ i` for `i ∈ s`, then `q ∣ (lcm s)/i`.
-/
lemma prime_dvd_lcm_div_of_not_dvd (q i : ℕ) (s : Finset ℕ) (hq : q.Prime)
    (hi : i ∈ s) (hqi : ¬ q ∣ i) (hqL : q ∣ s.lcm id) :
    q ∣ (s.lcm id / i) := by
  -- Since $q \mid s.lcm id$ and $i \mid s.lcm id$, it follows that $q \mid (s.lcm id) / i$.
  have h_div : q ∣ s.lcm id ∧ i ∣ s.lcm id := by
    exact ⟨ hqL, Finset.dvd_lcm hi ⟩;
  refine' Nat.Coprime.dvd_of_dvd_mul_left _ _;
  exacts [ i, hq.coprime_iff_not_dvd.mpr hqi, by convert h_div.1 using 1; rw [ Nat.mul_div_cancel' h_div.2 ] ]

/-
If `i0` is the unique element of `s` divisible by `q`, then `q ∤ (lcm s)/i0`.
-/
lemma not_dvd_lcm_div_of_unique (q i0 : ℕ) (s : Finset ℕ) (hq : q.Prime)
    (hs : ∀ x ∈ s, 0 < x) (hi0 : i0 ∈ s) (huniq : ∀ x ∈ s, q ∣ x → x = i0) :
    ¬ q ∣ (s.lcm id / i0) := by
  -- By factorization_lcm_sup q hq s hs, L.factorization q = s.sup (fun x => x.factorization q). Show this sup equals i0.factorization q:
  have hsup : (s.lcm id).factorization q = (i0.factorization q) := by
    rw [ factorization_lcm_sup ];
    · refine' le_antisymm ( Finset.sup_le fun x hx => _ ) ( Finset.le_sup ( f := fun i => i.factorization q ) hi0 );
      by_cases hqdiv : q ∣ x;
      · rw [ huniq x hx hqdiv ];
      · rw [ Nat.factorization_eq_zero_of_not_dvd hqdiv ] ; norm_num;
    · assumption;
  rw [ ← Nat.factorization_le_iff_dvd ];
  · rw [ Nat.factorization_div ] <;> norm_num [ hq, hsup ];
    exact Finset.dvd_lcm hi0;
  · exact hq.ne_zero;
  · exact Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by intros h; obtain ⟨ x, hx ⟩ := h; specialize hs x hx.1; aesop ) ) ) ( Finset.dvd_lcm hi0 ) ) ( hs i0 hi0 ) )

/-
Characterisation of the multiples of `N` inside `[M - h·N, M - 1]` (divisor equal to the
step): they are exactly the `M - i·N` for `1 ≤ i ≤ h`.
-/
lemma mult_char_self (M N h : ℕ) (hh : 1 ≤ h) (hN0 : 0 < N) (hNM : N ∣ M) (hMN : h * N ≤ M)
    (n : ℕ) (hn1 : M - h * N ≤ n) (hn2 : n ≤ M - 1) (hNn : N ∣ n) :
    ∃ i, 1 ≤ i ∧ i ≤ h ∧ n = M - i * N := by
  refine' ⟨ ( M - n ) / N, _, _, _ ⟩;
  · exact Nat.div_pos ( Nat.le_of_dvd ( Nat.sub_pos_of_lt ( lt_of_le_of_lt hn2 ( Nat.pred_lt ( ne_bot_of_gt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ) ) ) ( Nat.dvd_sub hNM hNn ) ) hN0;
  · exact Nat.div_le_of_le_mul <| by rw [ tsub_le_iff_left ] at *; linarith;
  · rw [ Nat.div_mul_cancel, Nat.sub_sub_self ];
    · exact hn2.trans ( Nat.pred_le _ );
    · exact Nat.dvd_sub hNM hNn

/-
If no prime factor of `Q` divides `m`, then `gcd (e*Q) m ∣ e`.
-/
lemma gcd_left_dvd_of_no_common (e Q m : ℕ)
    (h : ∀ q, Nat.Prime q → q ∣ Q → ¬ q ∣ m) : Nat.gcd (e * Q) m ∣ e := by
  convert Nat.dvd_of_mod_eq_zero _ using 1;
  exact Nat.mod_eq_zero_of_dvd <| Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( Nat.gcd ( e * Q ) m ) Q from Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_right _ _ ) <| Nat.Coprime.symm <| Nat.coprime_of_dvd <| by aesop ) <| Nat.gcd_dvd_left _ _

/-
Solvability of `A * ρ ≡ B (mod p)` with `ρ` a unit, when `A, B` are units mod `p`.
-/
lemma zmod_solve (p : ℕ) (hp : p.Prime) (A B : ℤ) (hA : ¬ (p : ℤ) ∣ A) (hB : ¬ (p : ℤ) ∣ B) :
    ∃ ρ : ℤ, ¬ (p : ℤ) ∣ ρ ∧ A * ρ ≡ B [ZMOD (p : ℤ)] := by
  obtain ⟨ ρ, hρ ⟩ := IsUnit.exists_left_inv ( show IsUnit ( A : ZMod p ) from by haveI := Fact.mk hp; exact IsUnit.mk0 _ <| by rw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] at *; aesop );
  use ρ.val * B;
  haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
  haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, mul_comm ] ;
  grind

/-- Adding the last term `b` to the sum, when the lcm does not change:
`X_{a,b} = X_{a,b-1} + r_b · (L_{a,b} / b)`. -/
lemma Xnum_succ (r : ℕ → ℤ) (a b : ℕ) (hab : a < b)
    (hL : Lden r a b = Lden r a (b - 1)) :
    Xnum r a b = Xnum r a (b - 1) + r b * ((Lden r a b / b : ℕ) : ℤ) := by
  simp only [Xnum_sum]; rcases b with ( _ | _ | b ) <;> simp_all +decide ; ring_nf;
  · erw [ Finset.sum_Ico_succ_top ] <;> norm_num [ Finset.sum_range_succ ];
  · erw [ Finset.sum_Ico_succ_top, Nat.cast_succ ] ; aesop;
    linarith

/-
Denominators are decreasing exactly when gcds are increasing (same lcm).
-/
lemma vden_lt_of_gfun_lt (r : ℕ → ℤ) (a b : ℕ)
    (hpos : ∀ i ∈ Finset.Icc a b, 0 < i)
    (hpos' : ∀ i ∈ Finset.Icc a (b - 1), 0 < i)
    (hL : Lden r a b = Lden r a (b - 1))
    (h : gfun r a (b - 1) < gfun r a b) :
    vden r a b < vden r a (b - 1) := by
  rw [ vden_eq r a b hpos, vden_eq r a ( b - 1 ) hpos' ];
  rw [ hL, Nat.div_lt_iff_lt_mul ];
  · nlinarith [ Nat.div_mul_cancel ( show gfun r a ( b - 1 ) ∣ Lden r a ( b - 1 ) from gfun_dvd_Lden _ _ _ ), show Lden r a ( b - 1 ) > 0 from Nat.pos_of_ne_zero ( Lden_ne_zero _ _ _ hpos' ) ];
  · exact lt_of_le_of_lt ( Nat.zero_le _ ) h

/-
Valuation comparison: If `L_{a,b} = L_{a,b-1}` and both `X`'s are nonzero,
then for every prime `ℓ`,
`ν_ℓ(g_{a,b-1}) ≤ ν_ℓ(g_{a,b}) + min(ν_ℓ(X_{a,b-1}), ν_ℓ(b))`.
-/
lemma valuation_comparison (r : ℕ → ℤ) (a b : ℕ) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hab : a < b) (hpos : ∀ i ∈ Finset.Icc a b, 0 < i)
    (hL : Lden r a b = Lden r a (b - 1))
    (hX : Xnum r a b ≠ 0) (hX' : Xnum r a (b - 1) ≠ 0) :
    (gfun r a (b - 1)).factorization ℓ ≤
      (gfun r a b).factorization ℓ
        + min ((Xnum r a (b - 1)).natAbs.factorization ℓ) (b.factorization ℓ) := by
  by_cases hr : r b = 0 <;> simp_all +decide [ Xnum_succ ];
  · -- Since $r b = 0$, we have $Xnum r a b = Xnum r a (b - 1)$.
    have hX_eq : Xnum r a b = Xnum r a (b - 1) := by
      convert Xnum_succ r a b hab hL using 1 ; aesop;
    simp_all +decide [ gfun_eq ];
  · -- By definition of `gfun`, we know that `(gfun r a b).factorization ℓ = min ((Xnum r a b).natAbs.factorization ℓ) ((Lden r a b).factorization ℓ)`.
    have h_gfun_def : (gfun r a b).factorization ℓ = min ((Xnum r a b).natAbs.factorization ℓ) ((Lden r a b).factorization ℓ) ∧ (gfun r a (b - 1)).factorization ℓ = min ((Xnum r a (b - 1)).natAbs.factorization ℓ) ((Lden r a (b - 1)).factorization ℓ) := by
      unfold gfun;
      rw [ Nat.gcd_comm, Nat.factorization_gcd, Nat.gcd_comm, Nat.factorization_gcd ] <;> simp_all +decide [ ne_of_gt ];
      · exact Lden_ne_zero r a ( b - 1 ) fun i hi => hpos i ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2.trans ( Nat.pred_le _ ) );
      · rw [ Xnum_succ ] <;> aesop;
      · exact Lden_ne_zero r a ( b - 1 ) fun i hi => hpos i ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2.trans ( Nat.pred_le _ ) );
    have h_ultrametric : (Xnum r a (b - 1) + r b * (Lden r a (b - 1) / b : ℤ)).natAbs.factorization ℓ ≥ min ((Xnum r a (b - 1)).natAbs.factorization ℓ) ((Lden r a (b - 1) / b : ℕ).factorization ℓ) := by
      have h_ultrametric : (Xnum r a (b - 1) + r b * (Lden r a (b - 1) / b : ℤ)) % ℓ ^ min ((Xnum r a (b - 1)).natAbs.factorization ℓ) ((Lden r a (b - 1) / b : ℕ).factorization ℓ) = 0 := by
        refine Int.emod_eq_zero_of_dvd ?_;
        refine' dvd_add _ _;
        · exact dvd_trans ( pow_dvd_pow _ ( min_le_left _ _ ) ) ( by simpa using Int.natCast_dvd.mpr ( Nat.ordProj_dvd _ _ ) );
        · refine' dvd_mul_of_dvd_right _ _;
          refine' mod_cast Nat.dvd_trans ( pow_dvd_pow _ ( min_le_right _ _ ) ) ( Nat.ordProj_dvd _ _ );
      have h_ultrametric : ℓ ^ min ((Xnum r a (b - 1)).natAbs.factorization ℓ) ((Lden r a (b - 1) / b : ℕ).factorization ℓ) ∣ (Xnum r a (b - 1) + r b * (Lden r a (b - 1) / b : ℤ)).natAbs := by
        simpa [ ← Int.natCast_dvd_natCast ] using Int.dvd_of_emod_eq_zero h_ultrametric;
      rw [ ← Nat.factorization_le_iff_dvd ] at h_ultrametric <;> aesop;
    have h_factorization_div : (Lden r a (b - 1) / b : ℕ).factorization ℓ ≥ (Lden r a (b - 1)).factorization ℓ - b.factorization ℓ := by
      rw [ Nat.factorization_div ] <;> norm_num;
      exact hL ▸ dvd_Lden r a b b ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) hr;
    cases min_cases ( ( Xnum r a ( b - 1 ) ).natAbs.factorization ℓ ) ( ( Lden r a ( b - 1 ) ).factorization ℓ ) <;> cases min_cases ( ( Xnum r a ( b - 1 ) ).natAbs.factorization ℓ ) ( b.factorization ℓ ) <;> simp_all +decide [ Xnum_succ ];
    · grind +qlia;
    · grind;
    · omega

/-
Drop criterion: With `b = E · p^m`, `m ≥ 1`, `p` prime, `p ∤ E`,
assuming `L_{a,b} = L_{a,b-1}`, `p ∣ X_{a,b}`, `p ∤ X_{a,b-1}`, and
`gcd(E, X_{a,b-1}) < p`, we get a denominator drop `v_{a,b} < v_{a,b-1}`.
-/
lemma drop_criterion (r : ℕ → ℤ) (a b E p m : ℕ)
    (hab : a < b) (hp : p.Prime) (hm : 1 ≤ m) (hb : b = E * p ^ m) (hpE : ¬ p ∣ E)
    (hpos : ∀ i ∈ Finset.Icc a b, 0 < i)
    (hL : Lden r a b = Lden r a (b - 1))
    (hpX : (p : ℤ) ∣ Xnum r a b) (hpX' : ¬ (p : ℤ) ∣ Xnum r a (b - 1))
    (hgcd : Nat.gcd E (Xnum r a (b - 1)).natAbs < p) :
    vden r a b < vden r a (b - 1) := by
  apply vden_lt_of_gfun_lt r a b hpos ( fun i hi => hpos i ( Finset.Icc_subset_Icc_right ( Nat.pred_le _ ) hi ) ) hL;
  by_cases hX : Xnum r a b = 0;
  · have h_ne : gfun r a (b - 1) ≠ Lden r a b := by
      intro h_eq
      have h_div : p ∣ gfun r a (b - 1) := by
        have h_div : b ∈ ((Finset.Icc a b).filter (fun i => r i ≠ 0)) := by
          grind +suggestions;
        exact h_eq.symm ▸ dvd_trans ( hb.symm ▸ dvd_mul_of_dvd_right ( dvd_pow_self _ ( by linarith ) ) _ ) ( dvd_Lden r a b b ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ( by aesop ) );
      exact hpX' ( Int.natCast_dvd.mpr ( Nat.dvd_trans h_div ( by rw [gfun_eq]; exact Int.natCast_dvd.mp ( Int.gcd_dvd_left _ _ ) ) ) );
    unfold gfun at *; simp_all +decide ;
    exact lt_of_le_of_ne ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( Lden_ne_zero r a ( E * p ^ m - 1 ) fun i hi => hpos i ( Finset.mem_Icc.mp hi |>.1 ) ( Nat.le_trans ( Finset.mem_Icc.mp hi |>.2 ) ( Nat.sub_le _ _ ) ) ) ) ( Nat.gcd_dvd_left _ _ ) ) h_ne;
  · have h_div : gfun r a (b - 1) * p ∣ gfun r a b * Nat.gcd E (Xnum r a (b - 1)).natAbs := by
      rw [ ← Nat.factorization_le_iff_dvd ] <;> simp_all +decide;
      · rw [ Nat.factorization_mul, Nat.factorization_mul ];
        · intro q; by_cases hq : Nat.Prime q <;> by_cases hq' : q = p <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
          · rw [ Nat.factorization_eq_zero_of_not_dvd ] <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ];
            · refine' Or.inl ( Nat.pos_of_ne_zero _ );
              simp_all +decide [ Nat.factorization_eq_zero_iff, gfun_eq, Int.gcd_eq_zero_iff ];
              refine' Nat.dvd_gcd ( Int.natCast_dvd.mp hpX ) _;
              refine' dvd_trans _ ( hL ▸ dvd_Lden r a ( E * p ^ m ) ( E * p ^ m ) ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) _ );
              · exact dvd_mul_of_dvd_right ( dvd_pow_self _ ( by linarith ) ) _;
              · intro H; simp_all +decide [ Xnum_succ ] ;
            · refine' hp.coprime_iff_not_dvd.mpr _;
              exact fun h => hpX' <| Int.natCast_dvd.mpr <| Nat.dvd_trans h <| Nat.gcd_dvd_right _ _;
          · have := valuation_comparison r a ( E * p ^ m ) q hq ( by linarith ) ( fun i hi => hpos i ( by linarith [ Finset.mem_Icc.mp hi ] ) ( by linarith [ Finset.mem_Icc.mp hi ] ) ) hL hX ( by aesop ) ; simp_all +decide ;
            refine le_trans this ?_;
            rw [ Nat.factorization_gcd ] <;> simp_all +decide;
            · rw [ Nat.factorization_mul ] <;> simp_all +decide [ Nat.Prime.ne_zero ];
              aesop_cat;
            · aesop_cat;
            · aesop;
        · grind +locals;
        · exact Nat.ne_of_gt ( Nat.gcd_pos_of_pos_left _ ( Nat.pos_of_ne_zero ( by aesop_cat ) ) );
        · grind +suggestions;
        · exact hp.ne_zero;
      · exact ⟨ Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( gfun_dvd_Lden _ _ _ ) ( Nat.pos_of_ne_zero ( Lden_ne_zero _ _ _ fun i hi => hpos i ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2.trans ( Nat.sub_le _ _ ) ) ) ) ), hp.ne_zero ⟩;
      · simp_all +decide [ gfun ];
        aesop;
    contrapose! h_div;
    exact Nat.not_dvd_of_pos_of_lt ( Nat.mul_pos ( Nat.pos_of_ne_zero ( by rw [gfun_eq]; exact mt Int.gcd_eq_zero_iff.mp ( by aesop ) ) ) ( Nat.gcd_pos_of_pos_right _ ( Int.natAbs_pos.mpr ( show Xnum r a ( b - 1 ) ≠ 0 from by aesop ) ) ) ) ( by nlinarith [ Nat.pos_of_ne_zero ( show gfun r a b ≠ 0 from by rw [gfun_eq]; exact mt Int.gcd_eq_zero_iff.mp ( by aesop ) ) ] )

/-- Case I: there is an adjacent pair `c < e` of nonzero indices, with nothing nonzero
strictly between, whose values do not cancel (`r c ≠ -r e`), within the first two periods. -/
def CaseI (r : ℕ → ℤ) (t : ℕ) : Prop :=
  ∃ c e : ℕ, 1 ≤ c ∧ r c ≠ 0 ∧ r e ≠ 0 ∧ c < e ∧ e - c ≤ t ∧ e ≤ 2 * t ∧
    r c ≠ - r e ∧ (∀ i, c < i → i < e → r i = 0)

/-- Case II: every adjacent nonzero pair cancels; then there are three consecutive
nonzero indices `c < d < e` spanning one period with `r c = r e = -r d`, the gap ratio
`h/(e-d) ≥ t/(t-1)` (written multiplicatively), and nothing else nonzero in between. -/
def CaseII (r : ℕ → ℤ) (t : ℕ) : Prop :=
  ∃ c d e : ℕ, 1 ≤ c ∧ r c ≠ 0 ∧ r d ≠ 0 ∧ r e ≠ 0 ∧ c < d ∧ d < e ∧ e - c ≤ t ∧
    e ≤ 2 * t ∧ (e - c) * (t - 1) ≥ t * (e - d) ∧ r c = r e ∧ r c = - r d ∧
    (∀ i, c < i → i < e → i ≠ d → r i = 0)

/-
Case split: Under periodicity with a nonzero term and `t ≥ 2`, either
Case I or Case II holds.
-/
lemma case_split (r : ℕ → ℤ) (t : ℕ) (ht : 2 ≤ t)
    (hper : ∀ i, r (i + t) = r i) (hne : ∃ i, 1 ≤ i ∧ r i ≠ 0) :
    CaseI r t ∨ CaseII r t := by
  -- By periodicity, there exist indices $c$ and $e$ within the first two periods such that $r_c \neq 0$, $r_e \neq 0$, and $c < e \leq 2t$.
  obtain ⟨c, hc⟩ : ∃ c, 1 ≤ c ∧ c ≤ t ∧ r c ≠ 0 := by
    obtain ⟨ i, hi, hi' ⟩ := hne;
    induction' i using Nat.strong_induction_on with i ih;
    by_cases hi'' : i ≤ t;
    · exact ⟨ i, hi, hi'', hi' ⟩;
    · exact ih ( i - t ) ( Nat.sub_lt hi ( by linarith ) ) ( Nat.sub_pos_of_lt ( lt_of_not_ge hi'' ) ) ( by rw [ show r i = r ( i - t ) by rw [ ← hper ( i - t ), Nat.sub_add_cancel ( by linarith ) ] ] at hi'; exact hi' );
  by_cases h_case : ∃ c e : ℕ, 1 ≤ c ∧ c < e ∧ e ≤ 2 * t ∧ r c ≠ 0 ∧ r e ≠ 0 ∧ (∀ i, c < i → i < e → r i = 0) ∧ r c ≠ -r e;
  · obtain ⟨ c, e, hc, he, he', hc', he'', h, h' ⟩ := h_case;
    refine Or.inl ⟨ c, e, hc, hc', he'', he, ?_, he', h', h ⟩;
    grind +splitImp;
  · -- Let $c$ be the smallest index such that $1 \leq c \leq t$ and $r c \neq 0$.
    obtain ⟨c, hc⟩ : ∃ c, 1 ≤ c ∧ c ≤ t ∧ r c ≠ 0 ∧ ∀ i, 1 ≤ i → i < c → r i = 0 := by
      exact ⟨ Nat.find ( ⟨ c, hc.1, hc.2.1, hc.2.2 ⟩ : ∃ c, 1 ≤ c ∧ c ≤ t ∧ r c ≠ 0 ), Nat.find_spec ( ⟨ c, hc.1, hc.2.1, hc.2.2 ⟩ : ∃ c, 1 ≤ c ∧ c ≤ t ∧ r c ≠ 0 ) |>.1, Nat.find_spec ( ⟨ c, hc.1, hc.2.1, hc.2.2 ⟩ : ∃ c, 1 ≤ c ∧ c ≤ t ∧ r c ≠ 0 ) |>.2.1, Nat.find_spec ( ⟨ c, hc.1, hc.2.1, hc.2.2 ⟩ : ∃ c, 1 ≤ c ∧ c ≤ t ∧ r c ≠ 0 ) |>.2.2, fun i hi₁ hi₂ => Classical.not_not.1 fun hi₃ => Nat.find_min ( ⟨ c, hc.1, hc.2.1, hc.2.2 ⟩ : ∃ c, 1 ≤ c ∧ c ≤ t ∧ r c ≠ 0 ) hi₂ ⟨ hi₁, by linarith [ Nat.find_spec ( ⟨ c, hc.1, hc.2.1, hc.2.2 ⟩ : ∃ c, 1 ≤ c ∧ c ≤ t ∧ r c ≠ 0 ) |>.2.1 ], hi₃ ⟩ ⟩;
    -- Let $d$ be the smallest index such that $c < d \leq 2t$ and $r d \neq 0$.
    obtain ⟨d, hd⟩ : ∃ d, c < d ∧ d ≤ 2 * t ∧ r d ≠ 0 ∧ ∀ i, c < i → i < d → r i = 0 := by
      have hd_exists : ∃ d, c < d ∧ d ≤ 2 * t ∧ r d ≠ 0 := by
        grind;
      exact ⟨ Nat.find hd_exists, Nat.find_spec hd_exists |>.1, Nat.find_spec hd_exists |>.2.1, Nat.find_spec hd_exists |>.2.2, fun i hi₁ hi₂ => Classical.not_not.1 fun hi₃ => Nat.find_min hd_exists hi₂ ⟨ hi₁, by linarith [ Nat.find_spec hd_exists |>.2.1 ], hi₃ ⟩ ⟩;
    -- Let $e$ be the smallest index such that $d < e \leq c + t$ and $r e \neq 0$.
    obtain ⟨e, he⟩ : ∃ e, d < e ∧ e ≤ c + t ∧ r e ≠ 0 ∧ ∀ i, d < i → i < e → r i = 0 := by
      have h_exists_e : ∃ e, d < e ∧ e ≤ c + t ∧ r e ≠ 0 := by
        grind +revert;
      exact ⟨ Nat.find h_exists_e, Nat.find_spec h_exists_e |>.1, Nat.find_spec h_exists_e |>.2.1, Nat.find_spec h_exists_e |>.2.2, fun i hi₁ hi₂ => Classical.not_not.1 fun hi₃ => Nat.find_min h_exists_e hi₂ ⟨ hi₁, by linarith [ Nat.find_spec h_exists_e |>.2.1 ], hi₃ ⟩ ⟩;
    -- By definition of $c$, $d$, and $e$, we have $r c = -r d$ and $r d = -r e$.
    have h_cd : r c = -r d := by
      grind
    have h_de : r d = -r e := by
      contrapose! h_case;
      use d, e;
      lia;
    refine Or.inr ⟨ c, d, e, hc.1, hc.2.2.1, hd.2.2.1, he.2.2.1, hd.1, he.1, ?_, ?_, ?_, ?_, ?_, ?_ ⟩ <;> try linarith;
    · omega;
    · rcases t with ( _ | _ | t ) <;> simp_all +decide [ Nat.mul_succ ];
      nlinarith only [ Nat.sub_add_cancel ( by linarith : c ≤ e ), Nat.sub_add_cancel ( by linarith : d ≤ e ), he.2.1, hd.1 ];
    · grind

/-- From the AP prime-product bound: for all sufficiently large `X`, every coprime residue
class mod `M` contains a prime in `(αX, βX)`. -/
lemma exists_prime_in_ap (M : ℕ) (hM : 0 < M) (α β : ℝ) (hα : 0 < α) (hab : α < β) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ A : ℤ, Int.gcd A M = 1 →
      ∃ q, Nat.Prime q ∧ α * X < (q : ℝ) ∧ (q : ℝ) < β * X ∧ (q : ℤ) ≡ A [ZMOD (M : ℤ)] := by
  have hφ : (0:ℝ) < Nat.totient M := by exact_mod_cast Nat.totient_pos.mpr hM
  set res := (Finset.range M).filter (fun a => Nat.Coprime a M) with hres
  have key : ∀ a ∈ res, ∀ᶠ X in Filter.atTop,
      ∃ q, Nat.Prime q ∧ α * X < (q:ℝ) ∧ (q:ℝ) < β * X ∧ (q:ℤ) ≡ (a:ℤ) [ZMOD (M:ℤ)] := by
    intro a ha
    have hcop : Int.gcd (a:ℤ) M = 1 := by
      rw [Int.gcd_natCast_natCast]; exact (Finset.mem_filter.mp ha).2
    have hεpos : (0:ℝ) < (β-α)/(2*Nat.totient M) := div_pos (sub_pos.mpr hab) (by positivity)
    have hax := ap_prime_product_lower_bound M (a:ℤ) hM hcop α β hα hab ((β-α)/(2*Nat.totient M)) hεpos
    filter_upwards [hax, Filter.eventually_gt_atTop 0] with X hXprod hXpos
    set F := (Finset.range (⌊β * X⌋₊ + 1)).filter
          (fun q => Nat.Prime q ∧ (α * X < (q : ℝ)) ∧ ((q : ℝ) < β * X) ∧
            (q : ℤ) ≡ (a:ℤ) [ZMOD (M : ℤ)]) with hF
    have hcoef : (β - α) / (Nat.totient M) - (β-α)/(2*Nat.totient M) = (β-α)/(2*Nat.totient M) := by
      field_simp; ring
    have hexp : (1:ℝ) < Real.exp (((β - α) / (Nat.totient M) - (β-α)/(2*Nat.totient M)) * X) := by
      rw [hcoef]
      have := Real.add_one_le_exp (((β-α)/(2*Nat.totient M)) * X)
      nlinarith [mul_pos hεpos hXpos]
    have hprodgt : (1:ℝ) < ∏ q ∈ F, (q : ℝ) := lt_of_lt_of_le hexp hXprod
    have hne : F.Nonempty := by
      rcases Finset.eq_empty_or_nonempty F with h | h
      · rw [h] at hprodgt; simp at hprodgt
      · exact h
    obtain ⟨q, hq⟩ := hne
    rw [hF, Finset.mem_filter] at hq
    exact ⟨q, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2⟩
  rw [← Finset.eventually_all] at key
  filter_upwards [key] with X hX A hA
  set a := (A % M).toNat with hadef
  have haZ : (a:ℤ) = A % M := Int.toNat_of_nonneg (Int.emod_nonneg A (by exact_mod_cast hM.ne'))
  have ha_mem : a ∈ res := by
    rw [hres, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have : (a:ℤ) < M := by rw [haZ]; exact Int.emod_lt_of_pos A (by exact_mod_cast hM)
      exact_mod_cast this
    · have : Int.gcd (a:ℤ) (M:ℤ) = 1 := by rw [haZ, Int.gcd_emod]; exact hA
      rw [Int.gcd_natCast_natCast] at this; exact this
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := hX a ha_mem
  refine ⟨q, hq1, hq2, hq3, ?_⟩
  have haA : (a:ℤ) ≡ A [ZMOD (M:ℤ)] := by
    show (a:ℤ) % M = A % M
    rw [haZ]; exact Int.emod_emod_of_dvd A dvd_rfl
  exact hq4.trans haA

/-- A product of distinct primes is squarefree. -/
lemma prod_primes_squarefree (S : Finset ℕ) (h : ∀ q ∈ S, Nat.Prime q) :
    Squarefree (∏ q ∈ S, q) := by
  induction S using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hprime : Nat.Prime a := h a (Finset.mem_insert_self a s)
    have hs : ∀ q ∈ s, Nat.Prime q := fun q hq => h q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime a (∏ q ∈ s, q) := by
      rw [Nat.Prime.coprime_iff_not_dvd hprime]
      rw [Prime.dvd_finset_prod_iff hprime.prime]
      rintro ⟨x, hx, hax⟩
      have : a = x := ((Nat.prime_dvd_prime_iff_eq hprime (hs x hx)).mp hax)
      exact ha (this ▸ hx)
    rw [Nat.squarefree_mul hcop]
    exact ⟨hprime.squarefree, ih hs⟩

/-- Large product with prescribed residue: From the AP prime-product lower
bound one extracts a squarefree `Q` whose prime factors all lie in `(αX, βX)` and are
`≡ 1 (mod t)`, with `Q ≡ ρ (mod p)` and `log Q` large. -/
lemma selection_lemma (t : ℕ) (ht : 1 ≤ t) (p : ℕ) (hp : p.Prime) (hpt : Nat.Coprime p t)
    (ρ : ℤ) (hρ : ¬ (p : ℤ) ∣ ρ) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop, ∃ Q : ℕ, 0 < Q ∧ Squarefree Q ∧
      (∀ q, Nat.Prime q → q ∣ Q → (α * X < (q : ℝ) ∧ (q : ℝ) < β * X ∧ q ≡ 1 [MOD t])) ∧
      (Q : ℤ) ≡ ρ [ZMOD (p : ℤ)] ∧
      ((β - α) / (Nat.totient t) - ε) * X ≤ Real.log Q := by
  classical
  haveI := Fact.mk hp
  have hβ : 0 < β := lt_trans hα hαβ
  have hinv : ∃ ρ' : ℤ, ρ * ρ' ≡ 1 [ZMOD (p:ℤ)] := by
    have hu : IsUnit (ρ : ZMod p) := by
      rw [isUnit_iff_ne_zero, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hρ
    obtain ⟨u, hu2⟩ := hu.exists_right_inv
    refine ⟨(u.val:ℤ), ?_⟩
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id]; exact hu2
  obtain ⟨ρ', hρ'⟩ := hinv
  have hρ'z : (ρ : ZMod p) * (ρ' : ZMod p) = 1 := by
    have := hρ'; rw [← ZMod.intCast_eq_intCast_iff] at this; push_cast at this; exact this
  have hρ'z0 : (ρ' : ZMod p) ≠ 0 := by
    intro h; rw [h, mul_zero] at hρ'z; exact one_ne_zero hρ'z.symm
  have hpρ' : ¬ (p:ℤ) ∣ ρ' := by rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hρ'z0
  have hlog : ∀ᶠ X : ℝ in atTop, Real.log (β*X) ≤ (ε/2)*X := by
    have h0 : Filter.Tendsto (fun X:ℝ => Real.log (β*X)/X) atTop (nhds 0) := by
      have hstep : Filter.Tendsto (fun X:ℝ => (Real.log β + Real.log X)/X) atTop (nhds 0) := by
        have hlogX : Tendsto (fun X:ℝ => Real.log X/X) atTop (nhds 0) := by
          simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
        have hc : Tendsto (fun X:ℝ => Real.log β/X) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
        simpa [add_div] using hc.add hlogX
      refine hstep.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with X hX
      rw [Real.log_mul (ne_of_gt hβ) (ne_of_gt hX)]
    filter_upwards [h0.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity)), eventually_gt_atTop 0] with X hX1 hX2
    rw [div_lt_iff₀ hX2] at hX1; linarith
  have hbig : ∀ᶠ X : ℝ in atTop, (p:ℝ) < α * X :=
    (Tendsto.const_mul_atTop hα tendsto_id).eventually_gt_atTop _
  have hax := ap_prime_product_lower_bound t 1 (by omega) (by simp [Int.gcd]) α β hα hαβ (ε/2) (by positivity)
  have hex := exists_prime_in_ap (p*t) (Nat.mul_pos hp.pos (by omega)) α β hα hαβ
  filter_upwards [hax, hex, hlog, hbig, eventually_gt_atTop (0:ℝ)] with X hax hex hlog hbig hXpos
  set G := (Finset.range (⌊β * X⌋₊ + 1)).filter
      (fun q => Nat.Prime q ∧ (α * X < (q : ℝ)) ∧ ((q : ℝ) < β * X) ∧ (q : ℤ) ≡ 1 [ZMOD (t : ℤ)]) with hG
  set P := ∏ q ∈ G, q with hPdef
  have hGprime : ∀ q ∈ G, Nat.Prime q := fun q hq => (Finset.mem_filter.mp hq).2.1
  have hPpos : 0 < P := Finset.prod_pos (fun q hq => (hGprime q hq).pos)
  have hcastP : ((P:ℕ):ℝ) = ∏ q ∈ G, (q:ℝ) := by rw [hPdef]; push_cast; rfl
  have hlogP : ((β - α) / (Nat.totient t) - ε/2) * X ≤ Real.log P := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast hPpos), hcastP]; exact hax
  have hpP : ¬ p ∣ P := by
    rw [hPdef, Prime.dvd_finset_prod_iff hp.prime]
    rintro ⟨q, hqG, hpq⟩
    have hm := Finset.mem_filter.mp hqG
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hm.2.1).mp hpq
    have : (p:ℝ) < (q:ℝ) := lt_trans hbig hm.2.2.1
    rw [heq] at this; exact lt_irrefl _ this
  set vp := ((P:ℤ)*ρ' % p).toNat with hvpdef
  have hvpZ : (vp:ℤ) = (P:ℤ)*ρ' % p := Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.pos.ne'))
  have hpvp : ¬ p ∣ vp := by
    intro h
    have h2 : (p:ℤ) ∣ ((P:ℤ)*ρ' % p) := by rw [← hvpZ]; exact_mod_cast h
    have hx : (P:ℤ)*ρ' = (P:ℤ)*ρ' % p + p * ((P:ℤ)*ρ' / p) := (Int.emod_add_mul_ediv _ _).symm
    have hpx : (p:ℤ) ∣ (P:ℤ)*ρ' := by rw [hx]; exact dvd_add h2 (Dvd.dvd.mul_right (dvd_refl _) _)
    rcases Int.Prime.dvd_mul' hp hpx with h3 | h3
    · exact hpP (by exact_mod_cast h3)
    · exact hpρ' h3
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hpt vp 1
  have hcopk : Nat.Coprime k (p*t) := by
    rw [Nat.coprime_mul_iff_right]
    refine ⟨?_, ?_⟩
    · have gk : Nat.gcd k p = Nat.gcd vp p := Nat.ModEq.gcd_eq hk1
      have hcvp : Nat.Coprime vp p := (hp.coprime_iff_not_dvd.mpr hpvp).symm
      simpa [Nat.Coprime, gk] using hcvp
    · have : Nat.gcd k t = Nat.gcd 1 t := Nat.ModEq.gcd_eq hk2
      simpa [Nat.Coprime] using this
  have hgcdInt : Int.gcd (k:ℤ) ((p*t : ℕ):ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact hcopk
  obtain ⟨q0, hq0p, hq0lo, hq0hi, hq0mod⟩ := hex (k:ℤ) hgcdInt
  have hq0k_p : (q0:ℤ) ≡ (k:ℤ) [ZMOD (p:ℤ)] :=
    Int.ModEq.of_dvd (by push_cast; exact Dvd.dvd.mul_right (dvd_refl _) _) hq0mod
  have hq0k_t : (q0:ℤ) ≡ (k:ℤ) [ZMOD (t:ℤ)] :=
    Int.ModEq.of_dvd (by push_cast; exact Dvd.dvd.mul_left (dvd_refl _) _) hq0mod
  have hq0t1Z : (q0:ℤ) ≡ 1 [ZMOD (t:ℤ)] := hq0k_t.trans (by exact_mod_cast hk2)
  have hq0t1 : q0 ≡ 1 [MOD t] := by exact_mod_cast hq0t1Z
  have hq0mem : q0 ∈ G := by
    rw [hG, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hq0p, hq0lo, hq0hi, hq0t1Z⟩
    have hle : (q0:ℝ) ≤ β * X := le_of_lt hq0hi
    have := Nat.le_floor hle
    omega
  have hq0dvd : q0 ∣ P := hPdef ▸ Finset.dvd_prod_of_mem _ hq0mem
  set Q := P / q0 with hQdef
  have hQq0 : Q * q0 = P := Nat.div_mul_cancel hq0dvd
  have hQdvdP : Q ∣ P := ⟨q0, hQq0.symm⟩
  have hQpos : 0 < Q := Nat.div_pos (Nat.le_of_dvd hPpos hq0dvd) hq0p.pos
  refine ⟨Q, hQpos, ?_, ?_, ?_, ?_⟩
  · exact (prod_primes_squarefree G hGprime).squarefree_of_dvd (hPdef ▸ hQdvdP)
  · intro q hqp hqQ
    have hqP : q ∣ P := hqQ.trans hQdvdP
    have hdd : q ∣ ∏ g ∈ G, g := hPdef ▸ hqP
    rw [Prime.dvd_finset_prod_iff hqp.prime] at hdd
    obtain ⟨g, hgG, hqg⟩ := hdd
    have hgeq : q = g := (Nat.prime_dvd_prime_iff_eq hqp (hGprime g hgG)).mp hqg
    subst hgeq
    have hm := Finset.mem_filter.mp hgG
    exact ⟨hm.2.2.1, hm.2.2.2.1, by exact_mod_cast hm.2.2.2.2⟩
  · have hPz0 : (P : ZMod p) ≠ 0 := by
      have h : ¬ (p:ℤ) ∣ (P:ℤ) := by exact_mod_cast hpP
      rw [Ne, show ((P:ℕ):ZMod p) = ((P:ℤ):ZMod p) by push_cast; ring,
        ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h
    have hzP : (Q : ZMod p) * (q0 : ZMod p) = (P : ZMod p) := by
      exact_mod_cast (congrArg (Nat.cast : ℕ → ZMod p) hQq0)
    have hzq0 : (q0 : ZMod p) = (P : ZMod p) * (ρ' : ZMod p) := by
      have h1 : (q0:ℤ) ≡ (P:ℤ)*ρ' [ZMOD (p:ℤ)] := by
        refine hq0k_p.trans ?_
        have h2 : (k:ℤ) ≡ (vp:ℤ) [ZMOD (p:ℤ)] := by exact_mod_cast hk1
        refine h2.trans ?_
        rw [hvpZ]; exact Int.emod_emod_of_dvd _ dvd_rfl
      have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr h1
      push_cast at this; exact this
    have hcancel : (Q : ZMod p) * (ρ' : ZMod p) = 1 := by
      have hh : (Q : ZMod p) * ((P : ZMod p) * (ρ' : ZMod p)) = (P : ZMod p) := by rw [← hzq0]; exact hzP
      have h3 : (P : ZMod p) * ((Q : ZMod p) * (ρ' : ZMod p)) = (P : ZMod p) * 1 := by
        rw [mul_one]; linear_combination hh
      exact mul_left_cancel₀ hPz0 h3
    have hQeqρ : (Q : ZMod p) = (ρ : ZMod p) := by
      have : (Q : ZMod p) * (ρ' : ZMod p) = (ρ : ZMod p) * (ρ' : ZMod p) := by rw [hcancel, hρ'z]
      exact mul_right_cancel₀ hρ'z0 this
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast; exact hQeqρ
  · have hcast : ((Q:ℕ):ℝ) = (P:ℝ) / (q0:ℝ) := by
      rw [hQdef, Nat.cast_div hq0dvd (by exact_mod_cast hq0p.pos.ne')]
    rw [hcast, Real.log_div (by exact_mod_cast hPpos.ne') (by exact_mod_cast hq0p.pos.ne')]
    have hlogq0 : Real.log q0 ≤ (ε/2)*X :=
      le_trans (Real.log_le_log (by exact_mod_cast hq0p.pos) (le_of_lt hq0hi)) hlog
    have hrw : ((β - α) / (Nat.totient t) - ε) * X
        = ((β - α) / (Nat.totient t) - ε/2) * X - (ε/2)*X := by ring
    rw [hrw]; linarith [hlogP, hlogq0]

/-
Large primes making a fixed integer a square: For `D ≠ 0` there are
arbitrarily large primes `p` for which `D` is a quadratic residue mod `p`.
-/
lemma qr_prime (D : ℤ) (hD : D ≠ 0) :
    ∀ B : ℕ, ∃ p, Nat.Prime p ∧ B < p ∧ IsSquare (D : ZMod p) := by
  intro B;
  obtain ⟨p, hp_prime, hp_gt, hp_mod⟩ : ∃ p : ℕ, Nat.Prime p ∧ B < p ∧ p ≡ 1 [MOD 8 * D.natAbs] := by
    exact Exists.imp ( by tauto ) ( Nat.exists_prime_gt_modEq_one B ( by positivity ) );
  -- Since $p \equiv 1 \pmod{8|D|}$, we have that $D$ is a quadratic residue modulo $p$.
  have h_quad_res : IsSquare (D : ZMod p) := by
    have h_jacobi : jacobiSym D p = 1 := by
      rw [ jacobiSym.mod_right ];
      · rw [ show p % ( 4 * D.natAbs ) = 1 % ( 4 * D.natAbs ) from Nat.ModEq.of_dvd ( by exact ⟨ 2, by ring ⟩ ) hp_mod ];
        rw [ Nat.mod_eq_of_lt ] <;> norm_num ; linarith [ abs_pos.mpr hD ];
      · exact hp_prime.odd_of_ne_two <| by rintro rfl; exact absurd ( hp_mod.of_dvd <| dvd_mul_of_dvd_left ( by decide : 2 ∣ 8 ) _ ) ( by norm_num ) ;
    haveI := Fact.mk hp_prime; simp_all +decide [ jacobiSym ] ;
    haveI := Fact.mk hp_prime; simp_all +decide [ Nat.primeFactorsList_prime hp_prime, legendreSym ] ;
    rw [ quadraticCharFun ] at h_jacobi ; aesop;
  use p

/-!  Case I construction.  Throughout, `b = e·Q·N` and `a = b - (e-c)·N`. -/

section CaseIConstr

variable (r : ℕ → ℤ) (t c e : ℕ) (ht : 1 ≤ t)
    (hper : ∀ i, r (i + t) = r i)
    (hc : 1 ≤ c) (hrc : r c ≠ 0) (hre : r e ≠ 0) (hce : c < e) (hcet : e - c ≤ t)
    (he2t : e ≤ 2 * t)
    (hne : r c ≠ - r e) (hzero : ∀ i, c < i → i < e → r i = 0)
    (p : ℕ) (hp : p.Prime) (hpbig : 2 * max (Rmax r t) t < p) (hcop : ¬ p ∣ t)
    (N Q : ℕ) (hNpow : ∃ j, 1 ≤ j ∧ N = p ^ j) (hNmod : N ≡ 1 [MOD t])
    (hQpos : 0 < Q) (hQsf : Squarefree Q)
    (hQprime : ∀ q, Nat.Prime q → q ∣ Q →
      ((e - c) * N < (e - c + 1) * q ∧ q < N ∧ q ≡ 1 [MOD t]))
    (hQmod : ((e : ℤ) * (r e + r c)) * (Q : ℤ) ≡ (r e) * (e - c) [ZMOD (p : ℤ)])
    (hpQ : ¬ (p : ℤ) ∣ (Q : ℤ))
    (hNlarge : e * (2 * t) < N)

include ht hper hc hrc hre hce hcet he2t hzero hp hpbig hcop hNpow hNmod hQpos hQsf hQprime hpQ hNlarge

/-
`b = e·Q·N` divides `L_{a,b-1}`.
-/
lemma case1_bdvd :
    (e * Q * N) ∣ Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
  -- By definition of $Lden$, we know that $N$, $e$, and $Q$ divide $Lden$.
  have hN_div : N ∣ Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
    obtain ⟨ j, hj, rfl ⟩ := hNpow;
    -- Since $a \equiv c \pmod{t}$ and $r$ is periodic, we have $r(a) = r(c)$.
    have ha_mod : (e * Q * p ^ j - (e - c) * p ^ j) % t = c % t := by
      have hQ_mod : Q ≡ 1 [MOD t] := by
        convert sqfree_prod_congr_one Q t hQsf _ using 1;
        exact fun q hq hq' => hQprime q hq hq' |>.2.2;
      zify;
      rw [ Nat.cast_sub ];
      · simp_all +decide [ ← ZMod.intCast_eq_intCast_iff', Nat.cast_sub hce.le ];
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c ] )
    have ha_r : r (e * Q * p ^ j - (e - c) * p ^ j) = r c := by
      convert rper_congr r t hper _;
      exact ha_mod;
    refine' dvd_Lden_of_exists _ _ _ _ _;
    refine' ⟨ e * Q * p ^ j - ( e - c ) * p ^ j, _, _, _ ⟩ <;> norm_num [ ha_r, hrc ];
    · nlinarith [ Nat.sub_add_cancel ( show 1 ≤ e * Q * p ^ j from Nat.mul_pos ( Nat.mul_pos ( by linarith ) hQpos ) ( pow_pos hp.pos _ ) ), Nat.sub_pos_of_lt hce, pow_pos hp.pos j ];
    · exact Nat.dvd_sub ( dvd_mul_left _ _ ) ( dvd_mul_left _ _ )
  have he_div : e ∣ Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
    apply dvd_Lden_of_exists;
    refine' ⟨ e * Q * N - e * t, _, _, _ ⟩ <;> norm_num;
    · constructor <;> nlinarith [ Nat.sub_add_cancel ( show e * t ≤ e * Q * N from by nlinarith [ mul_pos ( by linarith : 0 < e ) hQpos ] ), Nat.sub_add_cancel ( show c ≤ e from by linarith ), Nat.sub_add_cancel ( show 1 ≤ e * Q * N from by nlinarith [ mul_pos ( by linarith : 0 < e ) hQpos ] ) ];
    · exact Nat.dvd_sub ( dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _ ) ( dvd_mul_right _ _ );
    · -- Since $e * Q * N - e * t \equiv e \pmod{t}$, we have $r (e * Q * N - e * t) = r e$.
      have h_cong : e * Q * N - e * t ≡ e [MOD t] := by
        have h_periodic : e * Q * N ≡ e [MOD t] := by
          have h_mod : Q ≡ 1 [MOD t] := by
            exact sqfree_prod_congr_one Q t hQsf fun q hq hq' => hQprime q hq hq' |>.2.2;
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        cases le_total ( e * Q * N ) ( e * t ) <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        nlinarith [ mul_pos ( by linarith : 0 < e ) hQpos ];
      exact rper_congr r t hper h_cong ▸ hre
  have hQ_div : Q ∣ Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
    apply sqfree_dvd_of_forall_prime_dvd Q (Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1)) hQsf;
    intro q hq hqQ
    have hq_mem : ∃ i ∈ Finset.Icc (e * Q * N - (e - c) * N) (e * Q * N - 1), q ∣ i ∧ r i ≠ 0 := by
      refine' ⟨ e * Q * N - ( e - c ) * q, _, _, _ ⟩;
      · simp +zetaDelta at *;
        constructor <;> nlinarith [ Nat.sub_add_cancel ( show ( e - c ) * q ≤ e * Q * N from by nlinarith [ hQprime q hq hqQ, Nat.sub_add_cancel hce.le, Nat.mul_le_mul_left e hQpos ] ), Nat.sub_add_cancel ( show 1 ≤ e * Q * N from by nlinarith [ Nat.mul_le_mul_left e hQpos ] ), hQprime q hq hqQ, Nat.sub_add_cancel hce.le, Nat.mul_le_mul_left e hQpos ];
      · exact Nat.dvd_sub ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right hqQ _ ) _ ) ( dvd_mul_left _ _ );
      · -- By periodicity, we have $r (e * Q * N - (e - c) * q) = r (e - (e - c)) = r c$.
        have h_periodic : r (e * Q * N - (e - c) * q) = r (e - (e - c)) := by
          apply r_shift r t hper;
          · have hQ_mod : Q ≡ 1 [MOD t] := by
              apply sqfree_prod_congr_one Q t hQsf;
              exact fun q hq hqQ => by simpa [ ← ZMod.natCast_eq_natCast_iff ] using hQprime q hq hqQ |>.2.2;
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          · exact hQprime q hq hqQ |>.2.2;
          · exact Nat.sub_le _ _;
          · refine' le_trans _ ( Nat.mul_le_mul_left _ ( show N ≥ q from _ ) );
            · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c, Nat.le_of_dvd hQpos hqQ ] );
            · grind +splitImp;
        grind +splitIndPred;
    exact dvd_Lden_of_exists _ _ _ _ hq_mem;
  have h_coprime_eN : Nat.Coprime e N := by
    rcases hNpow with ⟨ j, hj₁, rfl ⟩ ; simp_all +decide ;
    exact Nat.Coprime.pow_right _ <| Nat.Coprime.symm <| hp.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt ( by linarith ) <| by nlinarith [ Nat.le_max_right ( Rmax r t ) t ] ;
  have h_coprime_NQ : Nat.Coprime N Q := by
    rcases hNpow with ⟨ j, hj, rfl ⟩ ; exact Nat.Coprime.pow_left _ <| hp.coprime_iff_not_dvd.mpr fun h => hpQ <| Int.natCast_dvd_natCast.mpr h;
  have h_coprime_eQ : Nat.Coprime e Q := by
    refine' Nat.coprime_of_dvd' _;
    intro k hk hk₁ hk₂; have := hQprime k hk hk₂; nlinarith [ Nat.sub_add_cancel hce.le, Nat.le_of_dvd ( by linarith ) hk₁ ] ;
  convert Nat.lcm_dvd ( Nat.lcm_dvd he_div hQ_div ) hN_div using 1;
  simp_all +decide [ Nat.lcm, Nat.Coprime, Nat.Coprime.symm, Nat.Coprime.gcd_mul ]

/-
The lcm is unchanged.
-/
lemma case1_L :
    Lden r (e * Q * N - (e - c) * N) (e * Q * N)
      = Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
  apply Lden_top_eq;
  · exact Nat.sub_lt ( by nlinarith [ mul_pos ( by linarith : 0 < e ) ( by linarith : 0 < Q ) ] ) ( by nlinarith [ Nat.sub_pos_of_lt hce ] );
  · exact Or.inr ( case1_bdvd r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hpQ hNlarge )

/-
Each prime factor of `Q` does not divide `X_{a,b-1}`.
-/
lemma case1_q :
    ∀ q, Nat.Prime q → q ∣ Q →
      ¬ (q : ℤ) ∣ Xnum r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
  intro q hq hqdivQ hqdivX
  have hq_gt_Rmax : (q : ℤ) > Rmax r t := by
    have := hQprime q hq hqdivQ;
    obtain ⟨ j, hj, rfl ⟩ := hNpow;
    nlinarith [ Nat.sub_add_cancel hce.le, Nat.pow_le_pow_right hp.one_lt.le hj, Nat.le_max_left ( Rmax r t ) t, Nat.le_max_right ( Rmax r t ) t ];
  obtain ⟨i0, hi0_mem, hi0_dvd⟩ : ∃ i0 ∈ Finset.Icc (e * Q * N - (e - c) * N) (e * Q * N - 1), q ∣ i0 ∧ r i0 ≠ 0 ∧ ∀ x ∈ Finset.Icc (e * Q * N - (e - c) * N) (e * Q * N - 1), q ∣ x → r x ≠ 0 → x = i0 := by
    refine' ⟨ e * Q * N - ( e - c ) * q, _, _, _, _ ⟩ <;> norm_num at *;
    · zify;
      rw [ Nat.cast_sub, Nat.cast_sub ] <;> push_cast <;> repeat nlinarith only [ hq_gt_Rmax, hNlarge, hQprime q hq hqdivQ, hce, Nat.sub_add_cancel hce.le ] ;
      · constructor <;> rw [ Nat.cast_sub ] <;> push_cast <;> try nlinarith only [ hNlarge, hce, hcet, hq_gt_Rmax, hQpos, hQsf, hQprime q hq hqdivQ ] ;
        exact Nat.mul_pos ( Nat.mul_pos ( by linarith ) hQpos ) ( by nlinarith );
      · nlinarith [ Nat.sub_add_cancel hce.le, Nat.mul_le_mul_left e hQpos, hQprime q hq hqdivQ ];
    · exact Nat.dvd_sub ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right hqdivQ _ ) _ ) ( dvd_mul_left _ _ );
    · rw [ show e * Q * N - ( e - c ) * q = e * Q * N - ( e - c ) * q from rfl, show r ( e * Q * N - ( e - c ) * q ) = r ( e - ( e - c ) ) from ?_ ];
      · rwa [ Nat.sub_sub_self hce.le ];
      · apply r_shift r t hper (e * Q * N) (e - c) q e;
        · simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          have hQ_mod : ∀ q, Nat.Prime q → q ∣ Q → (q : ZMod t) = 1 := by
            exact fun q hq hqdivQ => hQprime q hq hqdivQ |>.2.2;
          rw [ ← Nat.factorization_prod_pow_eq_self hQpos.ne' ] ; simp_all +decide [ Finsupp.prod ] ;
          rw [ Finset.prod_congr rfl fun x hx => by rw [ hQ_mod x ( Nat.prime_of_mem_primeFactors hx ) ( Nat.dvd_of_mem_primeFactors hx ) ] ] ; aesop;
        · exact hQprime q hq hqdivQ |>.2.2;
        · exact Nat.sub_le _ _;
        · nlinarith [ Nat.sub_add_cancel hce.le, Nat.mul_le_mul_left e hQpos, Nat.mul_le_mul_left e ( Nat.one_le_iff_ne_zero.mpr hQpos.ne' ), Nat.mul_le_mul_left e ( Nat.one_le_iff_ne_zero.mpr hp.ne_zero ), hQprime q hq hqdivQ ];
    · intros x hx₁ hx₂ hx₃ hx₄
      have hx₅ : ∃ i, 1 ≤ i ∧ i ≤ e - c ∧ x = e * Q * N - i * q := by
        have := mult_char ( e * Q * N ) q N ( e - c ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num at *;
        any_goals omega;
        · exact this hx₁ hx₂ hx₃;
        · exact hQprime q hq hqdivQ |>.2.1;
        · exact hQprime q hq hqdivQ |>.1;
        · exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right hqdivQ _ ) _;
        · exact Nat.mul_le_mul_right _ ( Nat.sub_le_of_le_add <| by nlinarith ) |> le_trans <| Nat.mul_le_mul_right _ <| Nat.le_mul_of_pos_right _ hQpos;
      obtain ⟨i, hi₁, hi₂, hi₃⟩ := hx₅
      have hi₄ : i = e - c := by
        contrapose! hx₄; simp_all +decide ;
        convert hzero ( e - i ) _ _ using 1 <;> try omega;
        convert r_shift r t hper ( e * Q * N ) i q e _ _ _ _ using 1;
        · have hQ_mod_t : Q ≡ 1 [MOD t] := by
            apply sqfree_prod_congr_one Q t hQsf;
            exact fun q hq hqdivQ => by simpa [ ← ZMod.natCast_eq_natCast_iff ] using hQprime q hq hqdivQ |>.2.2;
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        · exact hQprime q hq hqdivQ |>.2.2;
        · exact le_trans hi₂ ( Nat.sub_le _ _ );
        · gcongr;
          · exact le_trans hi₂ ( Nat.sub_le_of_le_add <| by nlinarith only [ hce, hQpos ] );
          · linarith [ hQprime q hq hqdivQ ]
      rw [hi₃, hi₄];
  -- The term for $i0$ is not divisible by $q$.
  have h_term_i0 : ¬((q : ℤ) ∣ r i0 * ((Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) / i0 : ℕ) : ℤ)) := by
    have h_term_i0 : ¬((q : ℤ) ∣ r i0) := by
      exact fun h => by have := Int.le_of_dvd ( abs_pos.mpr hi0_dvd.2.1 ) ( by simpa using h ) ; linarith [ abs_r_le_Rmax r t hper ( by linarith ) i0 ] ;
    have h_term_i0 : ¬((q : ℤ) ∣ (Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) / i0 : ℕ)) := by
      have h_term_i0 : ¬(q ∣ (Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) / i0 : ℕ)) := by
        have h_unique : ∀ x ∈ ((Finset.Icc (e * Q * N - (e - c) * N) (e * Q * N - 1)).filter (fun i => r i ≠ 0)), q ∣ x → x = i0 := by
          exact fun x hx hx' => hi0_dvd.2.2 x ( Finset.mem_filter.mp hx |>.1 ) hx' ( Finset.mem_filter.mp hx |>.2 )
        apply not_dvd_lcm_div_of_unique q i0 (((Finset.Icc (e * Q * N - (e - c) * N) (e * Q * N - 1)).filter (fun i => r i ≠ 0))) hq (by
        simp +decide [ Finset.mem_filter ];
        exact fun x hx₁ hx₂ hx₃ => Nat.pos_of_ne_zero fun hx₄ => by subst hx₄; exact absurd hx₁ ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : c ≤ e ), Nat.mul_le_mul_left e hQpos ] ) ;) (by
        exact Finset.mem_filter.mpr ⟨ hi0_mem, hi0_dvd.2.1 ⟩) (by
        exact h_unique);
      exact_mod_cast h_term_i0;
    exact mt ( Int.Prime.dvd_mul' hq ) ( by tauto );
  -- The sum of the other terms is divisible by $q$.
  have h_sum_other : ∀ x ∈ Finset.erase (Finset.Icc (e * Q * N - (e - c) * N) (e * Q * N - 1)) i0, (q : ℤ) ∣ r x * ((Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) / x : ℕ) : ℤ) := by
    intros x hx
    by_cases hx_zero : r x = 0;
    · simp [hx_zero];
    · have hq_div_L : q ∣ Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
        exact dvd_Lden r ( e * Q * N - ( e - c ) * N ) ( e * Q * N - 1 ) i0 ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi0_mem ], by linarith [ Finset.mem_Icc.mp hi0_mem ] ⟩ ) hi0_dvd.2.1 |> dvd_trans hi0_dvd.1;
      have hq_not_div_x : ¬(q ∣ x) := by
        grind;
      have hq_div_L_div_x : q ∣ (Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) / x) := by
        refine' Nat.dvd_div_of_mul_dvd _;
        refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ hq_div_L;
        · exact Nat.Coprime.symm ( hq.coprime_iff_not_dvd.mpr hq_not_div_x );
        · exact dvd_Lden r _ _ _ ( Finset.mem_Icc.mpr <| Finset.mem_Icc.mp <| Finset.mem_of_mem_erase hx ) hx_zero;
      exact dvd_mul_of_dvd_right ( mod_cast hq_div_L_div_x ) _;
  contrapose! hqdivX;
  rw [ show Xnum r ( e * Q * N - ( e - c ) * N ) ( e * Q * N - 1 ) = ∑ i ∈ Finset.Icc ( e * Q * N - ( e - c ) * N ) ( e * Q * N - 1 ), r i * ( Lden r ( e * Q * N - ( e - c ) * N ) ( e * Q * N - 1 ) / i : ℕ ) from Xnum_sum r _ _ ];
  rw [ ← Finset.sum_erase_add _ _ hi0_mem ];
  rw [ Int.dvd_add_right ( Finset.dvd_sum h_sum_other ) ] ; exact h_term_i0

/-
`p ∤ e·Q`.
-/
lemma case1_pndvd_eQ : ¬ p ∣ (e * Q) := by
  rw [ Nat.Prime.dvd_mul ] <;> norm_cast at *;
  exact not_or.mpr ⟨ Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith [ Nat.le_max_right ( Rmax r t ) t ] ), hpQ ⟩

include hQmod in
/-- `p ∤ e·Q - (e-c)`. -/
lemma case1_pndvd_eQh : ¬ p ∣ (e * Q - (e - c)) := by
  intro hdiv
  have hdiv_int : (p : ℤ) ∣ (e - c) * (r c) := by
    convert hQmod.symm.dvd.sub ( Int.natCast_dvd_natCast.mpr hdiv |> fun x => x.mul_right ( r e + r c ) ) using 1 ; ring_nf;
    rw [ Nat.cast_sub ] <;> push_cast ;
    · rw [ Nat.cast_sub hce.le ] ; ring;
    · nlinarith [ Nat.sub_le e c ];
  have hdiv_rc : ¬ (p : ℤ) ∣ r c := by
    have h_abs_r_le_Rmax : Int.natAbs (r c) ≤ Rmax r t := by
      apply abs_r_le_Rmax r t hper (by linarith) c;
    exact fun h => by have := Int.natAbs_dvd_natAbs.mpr h; exact absurd ( Nat.le_of_dvd ( Int.natAbs_pos.mpr hrc ) this ) ( by omega ) ;
  have hdiv_ec : (p : ℤ) ∣ (e - c) := by
    exact Or.resolve_right ( Int.Prime.dvd_mul' hp hdiv_int ) hdiv_rc;
  exact absurd ( Int.le_of_dvd ( by linarith [ Nat.sub_add_cancel hce.le ] ) hdiv_ec ) ( by omega )

include hQmod in
/-- The `p`-adic valuation of `L` equals that of `N` (i.e. `= j`). -/
lemma case1_pval :
    (Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1)).factorization p
      = N.factorization p := by
  apply le_antisymm; (
  have h_sup_le : ∀ x ∈ ((Finset.Icc (e * Q * N - (e - c) * N) (e * Q * N - 1)).filter (fun i => r i ≠ 0)), x.factorization p ≤ N.factorization p := by
    intro x hx
    by_contra h_contra
    obtain ⟨i, hi⟩ : ∃ i, 1 ≤ i ∧ i ≤ e - c ∧ x = e * Q * N - i * N := by
      apply mult_char_self (e * Q * N) N (e - c) (by
      exact Nat.sub_pos_of_lt hce) (by
      grind) (by
      exact dvd_mul_left _ _) (by
      exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c ] )) x (by
      exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1) (by
      exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2) (by
      have h_div : p ^ (N.factorization p + 1) ∣ x := by
        exact Nat.dvd_trans ( pow_dvd_pow _ ( Nat.succ_le_of_lt ( lt_of_not_ge h_contra ) ) ) ( Nat.ordProj_dvd _ _ )
      generalize_proofs at *; (
      obtain ⟨ j, hj₁, rfl ⟩ := hNpow; simp_all +decide [ Nat.factorization_pow ] ;
      exact dvd_of_mul_right_dvd h_div))
    generalize_proofs at *; (
    -- Then $r x = r (e - i)$ by $r_shift$.
    have h_rx : r x = r (e - i) := by
      convert r_shift r t hper ( e * Q * N ) i N e _ _ _ _ using 1 <;> norm_num [ hi ];
      · simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        have hQmod : ∀ q, Nat.Prime q → q ∣ Q → (q : ZMod t) = 1 := by
          exact fun q hq hq' => hQprime q hq hq' |>.2.2
        generalize_proofs at *; (
        rw [ ← Nat.prod_primeFactors_of_squarefree hQsf ] ; simp_all +decide ;
        rw [ Finset.prod_congr rfl fun x hx => hQmod x ( Nat.prime_of_mem_primeFactors hx ) ( Nat.dvd_of_mem_primeFactors hx ) ] ; norm_num);
      · exact hNmod;
      · exact le_trans hi.2.1 ( Nat.sub_le _ _ );
      · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c ] )
    generalize_proofs at *; (
    -- Since $r x \neq 0$, we have $r (e - i) \neq 0$, which implies $e - i = c$.
    have h_ei_eq_c : e - i = c := by
      by_cases h_cases : c < e - i ∧ e - i < e <;> simp_all +decide [ Finset.mem_filter ];
      grind
    generalize_proofs at *; (
    -- Since $e - i = c$, we have $x = e * Q * N - (e - c) * N = N * (e * Q - (e - c))$.
    have hx_eq : x = N * (e * Q - (e - c)) := by
      rw [ hi.2.2, mul_tsub, mul_comm ] ; ring_nf;
      rw [ ← h_ei_eq_c, Nat.sub_sub_self ( by omega ) ]
    generalize_proofs at *; (
    have h_factorization : (N * (e * Q - (e - c))).factorization p = N.factorization p + (e * Q - (e - c)).factorization p := by
      rw [ Nat.factorization_mul ] <;> norm_num [ hp.ne_zero ] ; aesop;
      exact Nat.sub_ne_zero_of_lt ( by nlinarith only [ hce, hc, hQpos, Nat.sub_add_cancel hce.le ] )
    generalize_proofs at *; (
    have h_factorization_zero : (e * Q - (e - c)).factorization p = 0 := by
      exact Nat.factorization_eq_zero_of_not_dvd ( case1_pndvd_eQh r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hQmod hpQ hNlarge ) |> fun h => h.symm ▸ by norm_num;
    generalize_proofs at *; (
    grind +ring))))))
  generalize_proofs at *; (
  convert factorization_lcm_sup p ( ((Finset.Icc ( e * Q * N - ( e - c ) * N ) ( e * Q * N - 1 )).filter (fun i => r i ≠ 0)) ) _ |> le_of_eq |> le_trans <| Finset.sup_le h_sup_le using 1
  generalize_proofs at *; (
  simp +decide [ Finset.mem_filter ];
  intro i hi₁ hi₂ hi₃; contrapose! hi₃; simp_all +decide ;
  exact absurd hi₁ ( by nlinarith [ Nat.sub_add_cancel hce.le, show e * Q > e - c from by nlinarith [ Nat.sub_add_cancel hce.le, show Q > 0 from hQpos ] ] )))); (
  refine' Nat.factorization_le_iff_dvd _ _ |>.2 _ p;
  · grind;
  · refine' Lden_ne_zero _ _ _ _;
    simp +zetaDelta at *;
    intro i hi₁ hi₂; contrapose! hi₁; simp_all +decide ;
    exact mul_lt_mul_of_pos_right ( by nlinarith [ Nat.sub_add_cancel hce.le ] ) ( Nat.pos_of_ne_zero ( by aesop_cat ) );
  · convert case1_bdvd r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hpQ hNlarge |> fun h => dvd_trans _ h using 1;
    exact dvd_mul_left _ _)

include hQmod in
/-- `p ∣ X_{a,b}`. -/
lemma case1_p1 :
    (p : ℤ) ∣ Xnum r (e * Q * N - (e - c) * N) (e * Q * N) := by
  -- Let $L' = Lden r a (M-1)$, where $M = e * Q * N$ and $a = M - (e - c) * N$.
  set M := e * Q * N
  set a := M - (e - c) * N
  set L' := Lden r a (M - 1);
  -- Step 1: Xnum r a M = r a*(L'/a) + r M*(L'/M) + ∑ i ∈ (Finset.Icc a M) \ {a, M}, r i*(L'/i).
  have hXnum : Xnum r a M = r a * (L' / a : ℕ) + r M * (L' / M : ℕ) + ∑ i ∈ Finset.Icc a M \ {a, M}, r i * (L' / i : ℕ) := by
    have hXnum : Xnum r a M = ∑ i ∈ Finset.Icc a M, r i * (L' / i : ℕ) := by
      have hL : Lden r a M = L' := by
        convert case1_L r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hpQ hNlarge using 1;
      exact hL ▸ Xnum_sum r a M;
    rw [ hXnum, ← Finset.sum_sdiff ( show { a, M } ⊆ Finset.Icc a M from ?_ ) ];
    · rw [ Finset.sum_pair ];
      · ring;
      · exact ne_of_lt ( Nat.sub_lt ( Nat.mul_pos ( Nat.mul_pos ( by linarith ) hQpos ) ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ( Nat.mul_pos ( Nat.sub_pos_of_lt hce ) ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) );
    · simp +decide [ Finset.insert_subset_iff ];
      exact Nat.sub_le _ _;
  -- Step 2: Rewrite r a = r c and r M = r e via periodicity.
  have hRa : r a = r c := by
    convert r_shift r t hper ( M - ( e - c ) * N ) 0 N c _ _ _ _ using 1 <;> norm_num [ hNmod ];
    · rfl;
    · simp +zetaDelta at *;
      rw [ Nat.modEq_iff_dvd ] at *;
      rw [ Nat.cast_sub ] <;> push_cast;
      · rw [ Nat.cast_sub hce.le ] ; ring_nf at * ; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
        rw [ show ( N : ZMod t ) = 1 by linear_combination' -hNmod ] ; ring_nf;
        have hQmod : ∀ q, Nat.Prime q → q ∣ Q → (q : ZMod t) = 1 := by
          exact fun q hq hq' => by simpa [ ← ZMod.natCast_eq_natCast_iff ] using hQprime q hq hq' |>.2.2;
        rw [ ← Nat.prod_primeFactors_of_squarefree hQsf ] ; rw [ Nat.cast_prod ] ; rw [ Finset.prod_eq_one ] <;> aesop;
      · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c ] )
  have hRm : r M = r e := by
    -- Since $N \equiv 1 \pmod{t}$, we have $M \equiv e \pmod{t}$.
    have hM_mod : M ≡ e [MOD t] := by
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      simp +zetaDelta at *;
      rw [ ← Nat.prod_primeFactors_of_squarefree hQsf ] ; simp_all +decide [ Finset.prod_eq_one ] ;
    rw [ ← Nat.mod_add_div M t, ← Nat.mod_add_div e t, hM_mod ];
    induction M / t <;> simp_all +decide [ Nat.mul_succ, ← add_assoc ];
    exact Nat.recOn ( e / t ) rfl fun n hn => by rw [ Nat.mul_succ, ← add_assoc, hper, hn ] ;
  -- Step 3: The rest-sum is (p:ℤ)-divisible.
  have hrest : (p : ℤ) ∣ ∑ i ∈ Finset.Icc a M \ {a, M}, r i * (L' / i : ℕ) := by
    -- For each $i \in (Finset.Icc a M) \ {a, M}$ with $r i \neq 0$, we have $N \nmid i$.
    have hNnmid : ∀ i ∈ Finset.Icc a M \ {a, M}, r i ≠ 0 → ¬(N ∣ i) := by
      intros i hi hri hNi
      have h_eq : ∃ i', 1 ≤ i' ∧ i' ≤ e - c ∧ i = M - i' * N := by
        apply mult_char_self;
        any_goals omega;
        · exact dvd_mul_left _ _;
        · exact Nat.mul_le_mul_right _ ( Nat.sub_le _ _ ) |> le_trans <| Nat.mul_le_mul_right _ <| Nat.le_mul_of_pos_right _ hQpos;
        · exact Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hi |>.1 ) |>.1;
        · grind +splitIndPred;
      obtain ⟨ i', hi₁, hi₂, rfl ⟩ := h_eq;
      -- By periodicity, $r (M - i' * N) = r (e - i')$.
      have h_periodic : r (M - i' * N) = r (e - i') := by
        apply r_shift;
        exact hper;
        · simp +zetaDelta at *;
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          rw [ ← Nat.prod_primeFactors_of_squarefree hQsf ] ; simp_all +decide [ Finset.prod_eq_one ] ;
        · exact hNmod;
        · exact le_trans hi₂ ( Nat.sub_le _ _ );
        · exact le_of_lt ( Nat.lt_of_sub_ne_zero ( by aesop_cat ) );
      grind;
    -- Since $N \nmid i$, we have $i.factorization p < N.factorization p = L'.factorization p$.
    have hfactorization : ∀ i ∈ Finset.Icc a M \ {a, M}, r i ≠ 0 → i.factorization p < L'.factorization p := by
      intros i hi hri
      have hfactorization_i : i.factorization p < N.factorization p := by
        contrapose! hNnmid;
        refine' ⟨ i, hi, hri, _ ⟩;
        rw [ ← Nat.factorization_le_iff_dvd ];
        · intro q; by_cases hq : Nat.Prime q <;> by_cases hq' : q = p <;> simp_all +decide ;
          rw [ Nat.factorization_eq_zero_of_not_dvd ] <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ];
          rcases hNpow with ⟨ j, hj₁, rfl ⟩ ; exact Nat.Coprime.pow_right _ <| hq.coprime_iff_not_dvd.mpr fun h => hq' <| by have := Nat.prime_dvd_prime_iff_eq hq hp; tauto;
        · grind;
        · grind;
      convert hfactorization_i using 1;
      apply case1_pval (t := t);
      all_goals assumption;
    -- Since $i.factorization p < L'.factorization p$, we have $p \mid (L' / i)$.
    have hdiv : ∀ i ∈ Finset.Icc a M \ {a, M}, r i ≠ 0 → (p : ℤ) ∣ (L' / i : ℕ) := by
      intros i hi hri
      have hdiv : p ∣ (L' / i : ℕ) := by
        rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
        · rw [ Nat.factorization_div ] <;> norm_num [ hp ];
          · exact Nat.sub_pos_of_lt ( hfactorization i hi hri );
          · apply dvd_Lden;
            · grind +qlia;
            · assumption;
        · exact hp.ne_zero;
        · refine' ⟨ _, _ ⟩;
          · grind;
          · refine' Nat.le_of_dvd ( Nat.pos_of_ne_zero _ ) ( dvd_Lden _ _ _ _ _ _ );
            · intro H; simp_all +decide ;
            · grind;
            · assumption
      exact_mod_cast hdiv;
    exact Finset.dvd_sum fun i hi => if hi0 : r i = 0 then by simp +decide [ hi0 ] else dvd_mul_of_dvd_right ( hdiv i hi hi0 ) _;
  -- Step 4: Show (p:ℤ) ∣ r c*(L'/a) + r e*(L'/M).
  have hsum : (p : ℤ) ∣ r c * (L' / a : ℕ) + r e * (L' / M : ℕ) := by
    have hA : (e * Q - (e - c) : ℤ) * (L' / a : ℕ) = (L' / N : ℕ) := by
      have hA : a = (e * Q - (e - c)) * N := by
        rw [ tsub_mul ];
      have hA : a ∣ L' := by
        apply dvd_Lden;
        · simp +zetaDelta at *;
          nlinarith [ Nat.sub_add_cancel ( show 1 ≤ e * Q * N from Nat.mul_pos ( Nat.mul_pos ( by linarith ) hQpos ) ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ), Nat.sub_pos_of_lt hce ];
        · grind;
      norm_cast;
      rw [ Int.subNatNat_of_le hce.le ] ; norm_cast;
      rw [ Int.subNatNat_of_le ] <;> norm_cast;
      · rw [ ← Nat.mul_div_assoc ];
        · rw [ ‹a = ( e * Q - ( e - c ) ) * N›, Nat.mul_div_mul_left _ _ ( Nat.sub_pos_of_lt ( by nlinarith [ Nat.sub_add_cancel hce.le ] ) ) ];
        · assumption;
      · nlinarith only [ hce, hQpos, Nat.sub_le e c ]
    have hB : (e * Q : ℤ) * (L' / M : ℕ) = (L' / N : ℕ) := by
      norm_cast;
      rw [ ← Nat.mul_div_assoc ];
      · rw [ Nat.mul_div_mul_left _ _ ( Nat.mul_pos ( by linarith ) hQpos ) ];
      · convert case1_bdvd r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hpQ hNlarge using 1;
    have hdiv : (p : ℤ) ∣ (e * Q * (r e + r c) - r e * (e - c)) * (L' / N : ℕ) := by
      exact dvd_mul_of_dvd_left ( by convert hQmod.symm.dvd using 1; ring ) _;
    have hdiv : (p : ℤ) ∣ (e * Q * (e * Q - (e - c))) * (r c * (L' / a : ℕ) + r e * (L' / M : ℕ)) := by
      grind +qlia;
    have hdiv : ¬(p : ℤ) ∣ (e * Q * (e * Q - (e - c))) := by
      have hdiv : ¬(p : ℤ) ∣ (e * Q) := by
        exact_mod_cast case1_pndvd_eQ r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hpQ hNlarge
      have hdiv' : ¬(p : ℤ) ∣ (e * Q - (e - c)) := by
        convert case1_pndvd_eQh r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hQmod hpQ hNlarge using 1;
        rw [ ← Int.natCast_dvd_natCast ] ; norm_num [ Nat.cast_sub ( show e * Q ≥ e - c from Nat.sub_le_of_le_add <| by nlinarith ) ] ;
        rw [ Nat.cast_sub hce.le ]
      exact fun h => hdiv <| Int.Prime.dvd_mul' hp h |> fun h => h.resolve_right hdiv';
    exact Or.resolve_left ( Int.Prime.dvd_mul' hp ‹_› ) hdiv;
  convert dvd_add hsum hrest using 1 ; rw [ hXnum, hRa, hRm ]

include hQmod in
/-- `p ∤ X_{a,b-1}`. -/
lemma case1_p2 :
    ¬ (p : ℤ) ∣ Xnum r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
  -- Combine: Xnum = r a*(L/a) + ∑_{erase a} (...); if p ∣ Xnum then p ∣ a-term (Int.dvd_add_right with the sum divisible), contradiction. So ¬ p ∣ Xnum.
  apply Classical.byContradiction
  intro h_contra;
  obtain ⟨j, hj1, rfl⟩ := hNpow;
  obtain ⟨a, ha⟩ : ∃ a, a = e * Q * p ^ j - (e - c) * p ^ j ∧ a ∈ Finset.Icc (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1) ∧ r a ≠ 0 ∧ ¬(p : ℤ) ∣ r a ∧ ¬(p : ℤ) ∣ (Lden r (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1) / a) := by
    refine' ⟨ _, rfl, _, _, _, _ ⟩;
    · simp +zetaDelta at *;
      nlinarith [ Nat.sub_add_cancel ( show c ≤ e from hce.le ), Nat.sub_add_cancel ( show 1 ≤ e * Q * p ^ j from Nat.mul_pos ( Nat.mul_pos ( by linarith ) hQpos ) ( pow_pos hp.pos _ ) ), pow_pos hp.pos j ];
    · -- By periodicity, we have $r (e * Q * p ^ j - (e - c) * p ^ j) = r (e - (e - c)) = r c$.
      have h_periodic : r (e * Q * p ^ j - (e - c) * p ^ j) = r c := by
        have h_periodic : r (e * Q * p ^ j - (e - c) * p ^ j) = r ((e - (e - c)) * p ^ j) := by
          convert rper_congr r t hper _ using 1;
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_sub ( show ( e - c ) * p ^ j ≤ e * Q * p ^ j from Nat.mul_le_mul_right _ <| by nlinarith [ Nat.sub_le e c ] ) ];
          rw [ ← Nat.prod_primeFactors_of_squarefree hQsf ] ; simp_all +decide [ Finset.prod_eq_one ] ;
        rw [ h_periodic, Nat.sub_sub_self hce.le ];
        convert rper_congr r t hper _ using 1;
        simpa using hNmod.mul_left c;
      aesop;
    · -- By periodicity, $r (e * Q * p ^ j - (e - c) * p ^ j) = r (e - (e - c)) = r c$.
      have h_periodic : r (e * Q * p ^ j - (e - c) * p ^ j) = r c := by
        have h_periodic : r (e * Q * p ^ j - (e - c) * p ^ j) = r ((e - (e - c)) * p ^ j) := by
          convert rper_congr r t hper _ using 1;
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_sub ( show ( e - c ) * p ^ j ≤ e * Q * p ^ j from Nat.mul_le_mul_right _ <| by nlinarith [ Nat.sub_le e c ] ) ];
          rw [ ← Nat.prod_primeFactors_of_squarefree hQsf ] ; simp_all +decide [ Finset.prod_eq_one ] ;
        rw [ h_periodic, Nat.sub_sub_self hce.le ];
        convert rper_congr r t hper _ using 1;
        simpa using hNmod.mul_left c;
      rw [ h_periodic ];
      exact fun h => by have := Int.le_of_dvd ( abs_pos.mpr hrc ) ( by simpa using h ) ; linarith [ abs_r_le_Rmax r t hper ( by linarith ) c, le_max_left ( Rmax r t ) t, le_max_right ( Rmax r t ) t ] ;
    · have h_factorization : (Lden r (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1)).factorization p = j := by
        convert case1_pval r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop _ _ _ _ _ _ _ _ _ _ using 1;
        all_goals norm_cast at *;
        · norm_num [ hp ];
        · use j;
      have h_factorization_a : (Lden r (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1) / (e * Q * p ^ j - (e - c) * p ^ j)).factorization p = 0 := by
        rw [ Nat.factorization_div ] <;> norm_num [ h_factorization ];
        · rw [ show e * Q * p ^ j - ( e - c ) * p ^ j = p ^ j * ( e * Q - ( e - c ) ) by rw [ Nat.mul_sub_left_distrib ] ; ring_nf, Nat.factorization_mul ] <;> norm_num [ hp.ne_zero, hp.ne_one ];
          · simp +decide [ hp.factorization ];
          · exact Nat.sub_ne_zero_of_lt ( by nlinarith [ Nat.sub_add_cancel hce.le ] );
        · convert dvd_Lden r ( e * Q * p ^ j - ( e - c ) * p ^ j ) ( e * Q * p ^ j - 1 ) ( e * Q * p ^ j - ( e - c ) * p ^ j ) _ _ using 1;
          · simp +zetaDelta at *;
            nlinarith [ Nat.sub_add_cancel ( show 1 ≤ e * Q * p ^ j from Nat.mul_pos ( Nat.mul_pos ( by linarith ) hQpos ) ( pow_pos hp.pos _ ) ), Nat.sub_pos_of_lt hce, pow_pos hp.pos j ];
          · rw [ show e * Q * p ^ j - ( e - c ) * p ^ j = p ^ j * ( e * Q - ( e - c ) ) by rw [ Nat.mul_sub_left_distrib ] ; ring_nf ];
            convert hrc using 1;
            convert rper_congr r t hper _ using 1;
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
            rw [ Nat.cast_sub ] <;> norm_num [ hNmod ];
            · rw [ Nat.cast_sub hce.le ] ; ring_nf;
              have hQmod : ∀ q, Nat.Prime q → q ∣ Q → (q : ZMod t) = 1 := by
                exact fun q hq hq' => hQprime q hq hq' |>.2.2;
              rw [ ← Nat.prod_primeFactors_of_squarefree hQsf ] ; simp +decide ;
              rw [ Finset.prod_congr rfl fun x hx => hQmod x ( Nat.prime_of_mem_primeFactors hx ) ( Nat.dvd_of_mem_primeFactors hx ) ] ; norm_num;
            · nlinarith;
      norm_cast;
      rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num [ h_factorization_a ];
      · simp_all +decide [ Nat.Prime.factorization ];
      · exact hp.ne_zero;
      · refine' ⟨ Nat.sub_ne_zero_of_lt _, _ ⟩;
        · exact mul_lt_mul_of_pos_right ( by nlinarith [ Nat.sub_add_cancel hce.le ] ) ( pow_pos hp.pos _ );
        · have := case1_bdvd r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop ( p ^ j ) Q ⟨ j, hj1, rfl ⟩ hNmod hQpos hQsf hQprime hpQ hNlarge;
          exact le_add_of_le_of_nonneg ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop_cat ) ) this ) ( Nat.zero_le _ );
  have h_sum_div : ∀ i ∈ Finset.Icc (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1), i ≠ a → (p : ℤ) ∣ r i * ((Lden r (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1) / i : ℕ) : ℤ) := by
    intros i hi hia
    by_cases hri : r i = 0;
    · simp [hri];
    · have h_not_div_i : ¬(p ^ j ∣ i) := by
        intro hpi
        have h_eq : ∃ i', 1 ≤ i' ∧ i' ≤ e - c ∧ i = e * Q * p ^ j - i' * p ^ j := by
          apply mult_char_self;
          any_goals linarith [ Finset.mem_Icc.mp hi ];
          · exact Nat.sub_pos_of_lt hce;
          · exact pow_pos hp.pos _;
          · exact dvd_mul_left _ _;
          · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c ] );
          · assumption;
        obtain ⟨ i', hi'₁, hi'₂, rfl ⟩ := h_eq;
        have h_eq : r (e * Q * p ^ j - i' * p ^ j) = r (e - i') := by
          apply r_shift;
          exact hper;
          · have h_cong : Q ≡ 1 [MOD t] := by
              apply sqfree_prod_congr_one Q t hQsf;
              exact fun q hq hq' => hQprime q hq hq' |>.2.2;
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          · exact hNmod;
          · exact le_trans hi'₂ ( Nat.sub_le _ _ );
          · exact le_of_lt ( Nat.lt_of_sub_ne_zero ( by aesop_cat ) );
        grind;
      have h_factorization_i : (Lden r (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1)).factorization p > i.factorization p := by
        have h_factorization_i : (Lden r (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1)).factorization p = j := by
          convert case1_pval r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop _ _ _ _ _ _ _ _ _ _ using 1;
          all_goals norm_cast;
          · norm_num [ hp ];
          · use j;
          · grind +locals;
          · exact_mod_cast hpQ;
        exact h_factorization_i.symm ▸ Nat.lt_of_not_ge fun h => h_not_div_i <| Nat.dvd_trans ( pow_dvd_pow _ h ) <| Nat.ordProj_dvd _ _;
      have h_factorization_i : p ∣ (Lden r (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1) / i) := by
        rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
        · rw [ Nat.factorization_div ];
          · intro q; by_cases hq : p = q <;> simp_all +decide ;
            exact Nat.sub_pos_of_lt h_factorization_i;
          · apply dvd_Lden;
            · exact hi;
            · assumption;
        · exact hp.ne_zero;
        · exact ⟨ by aesop_cat, Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( dvd_Lden _ _ _ _ ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hi ] ⟩ ) hri ) ⟩;
      exact dvd_mul_of_dvd_right ( mod_cast h_factorization_i ) _;
  simp_all +decide [ Xnum_sum ];
  rw [ Finset.sum_eq_add_sum_diff_singleton ( show a ∈ Finset.Icc ( e * Q * p ^ j - ( e - c ) * p ^ j ) ( e * Q * p ^ j - 1 ) from Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩ ) ] at h_contra;
  rw [ Int.dvd_add_left ( Finset.dvd_sum fun x hx => h_sum_div x ( by aesop ) ( by aesop ) ( by aesop ) ) ] at h_contra;
  exact ha.2.2.2.2 ( by exact Or.resolve_left ( Int.Prime.dvd_mul' hp h_contra ) ha.2.2.2.1 )

include hQmod in
/-- `p ∣ X_{a,b}` and `p ∤ X_{a,b-1}`. -/
lemma case1_p :
    (p : ℤ) ∣ Xnum r (e * Q * N - (e - c) * N) (e * Q * N) ∧
      ¬ (p : ℤ) ∣ Xnum r (e * Q * N - (e - c) * N) (e * Q * N - 1) :=
  ⟨case1_p1 r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod
      hQpos hQsf hQprime hQmod hpQ hNlarge,
   case1_p2 r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod
      hQpos hQsf hQprime hQmod hpQ hNlarge⟩

include hQmod in
/-- The endpoint `b = e·Q·N` is a denominator-drop point for `a = b - (e-c)·N`. -/
lemma caseI_isDrop :
    (e * Q * N) ∈ Bset r (e * Q * N - (e - c) * N) := by
  refine' ⟨ _, _ ⟩;
  · exact Nat.sub_lt ( by nlinarith [ mul_pos ( by linarith : 0 < e ) hQpos ] ) ( by nlinarith [ Nat.sub_pos_of_lt hce ] );
  · apply drop_criterion;
    any_goals exact hp;
    any_goals exact hNpow.choose_spec.1;
    any_goals rw [ ← hNpow.choose_spec.2 ];
    any_goals exact case1_p r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hQmod hpQ hNlarge |>.1;
    any_goals exact case1_p r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hQmod hpQ hNlarge |>.2;
    · exact Nat.sub_lt ( by nlinarith [ mul_pos ( by linarith : 0 < e ) hQpos ] ) ( by nlinarith [ Nat.sub_pos_of_lt hce ] );
    · rw [ Nat.Prime.dvd_mul ] <;> norm_cast at *;
      exact not_or.mpr ⟨ Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by nlinarith [ Nat.le_max_right ( Rmax r t ) t ] ), hpQ ⟩;
    · simp +zetaDelta at *;
      intro i hi₁ hi₂; contrapose! hi₁; simp_all +decide ;
      exact mul_lt_mul_of_pos_right ( by nlinarith [ Nat.sub_add_cancel hce.le ] ) ( Nat.pos_of_ne_zero ( by aesop_cat ) );
    · apply case1_L (t := t);
      all_goals tauto;
    · refine' lt_of_le_of_lt ( Nat.le_of_dvd _ _ ) _;
      exact e;
      · linarith;
      · apply gcd_left_dvd_of_no_common;
        exact fun q hq hq' => by simpa [ ← Int.natCast_dvd_natCast ] using case1_q r t c e ht hper hc hrc hre hce hcet he2t hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hpQ hNlarge q hq hq';
      · grind +splitIndPred

end CaseIConstr

/-
Case I construction: Given `CaseI` and a target constant `D` strictly above
`t(t+1)φ(t)`, we build denominator-drop pairs `a k < b k` with ratio eventually `< D`.
-/
lemma caseI_construction (r : ℕ → ℤ) (t : ℕ) (ht : 1 ≤ t)
    (hper : ∀ i, r (i + t) = r i) (hCI : CaseI r t)
    (D : ℝ) (hD : (t : ℝ) * (t + 1) * (Nat.totient t) < D) :
    ∃ a b : ℕ → ℕ,
      Filter.Tendsto a Filter.atTop Filter.atTop ∧
      (∀ᶠ k in Filter.atTop, b k ∈ Bset r (a k)) ∧
      (∀ᶠ k in Filter.atTop, ((b k : ℝ) - (a k : ℝ)) / Real.log (a k) < D) := by
  obtain ⟨c, e, hc, hrc, hre, hce, hcet, he2t, hne, hzero⟩ := hCI
  set h := e - c
  set R := Rmax r t
  obtain ⟨p, hp, hpbig, hcop⟩ : ∃ p : ℕ, p.Prime ∧ 2 * max R t < p ∧ ¬(p : ℤ) ∣ t := by
    have := Nat.exists_infinite_primes ( 2 * max R t + t + 1 );
    exact ⟨ this.choose, this.choose_spec.2, by linarith [ this.choose_spec.1, Nat.zero_le ( max R t ) ], by exact_mod_cast Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith [ this.choose_spec.1, Nat.zero_le ( max R t ) ] ) ⟩
  set A := (e : ℤ) * (r e + r c)
  set B := (r e : ℤ) * (e - c)
  obtain ⟨ρ, hρ, hρmod⟩ : ∃ ρ : ℤ, ¬ (p : ℤ) ∣ ρ ∧ A * ρ ≡ B [ZMOD p] := by
    apply zmod_solve p hp A B;
    · have hA_not_div : ¬(p : ℤ) ∣ (r e + r c) := by
        intro hdiv
        have h_abs : |r e + r c| ≤ 2 * R := by
          have h_abs : |r e| ≤ R ∧ |r c| ≤ R := by
            exact ⟨ by simpa [ ← Int.ofNat_le ] using abs_r_le_Rmax r t hper ( by linarith ) e, by simpa [ ← Int.ofNat_le ] using abs_r_le_Rmax r t hper ( by linarith ) c ⟩;
          exact abs_le.mpr ⟨ by linarith [ abs_le.mp h_abs.1, abs_le.mp h_abs.2 ], by linarith [ abs_le.mp h_abs.1, abs_le.mp h_abs.2 ] ⟩;
        exact absurd ( Int.le_of_dvd ( abs_pos.mpr ( show r e + r c ≠ 0 from fun h => hne <| by linarith ) ) <| by simpa using hdiv ) ( by cases abs_cases ( r e + r c ) <;> linarith [ Nat.le_max_left R t, Nat.le_max_right R t ] );
      exact mt ( Int.Prime.dvd_mul' hp ) ( by exact not_or.mpr ⟨ by exact_mod_cast Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith [ Nat.le_max_right R t ] ), hA_not_div ⟩ );
    · have hB_not_div : ¬(p : ℤ) ∣ r e ∧ ¬(p : ℤ) ∣ (e - c) := by
        constructor;
        · contrapose! hpbig;
          have := abs_r_le_Rmax r t hper ( by linarith ) e;
          exact le_trans ( Nat.le_of_dvd ( Int.natAbs_pos.mpr hre ) ( Int.natCast_dvd.mp hpbig ) ) ( by linarith [ Nat.le_max_left R t, Nat.le_max_right R t ] );
        · exact fun h => by have := Int.le_of_dvd ( by linarith ) h; linarith [ Nat.sub_add_cancel hce.le, Nat.le_max_right R t ] ;
      exact mt ( Int.Prime.dvd_mul' hp ) ( by aesop );
  set L := (Nat.totient t : ℝ)
  set α := (h : ℝ) / (h + 1)
  set β := (1 : ℝ)
  set X0 := 1 / ((h + 1) * L) with hX0d
  have hL_pos : 0 < L := by
    exact Nat.cast_pos.mpr (Nat.totient_pos.mpr (by linarith))
  have hh_pos : (0:ℝ) < (h : ℝ) := by
    have : 0 < h := Nat.sub_pos_of_lt hce
    exact_mod_cast this
  have hposHL : (0:ℝ) < ((h:ℝ) + 1) * L := by positivity
  have hX0pos : 0 < X0 := by positivity
  have hht : (h : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcet
  have hbound' : (h:ℝ) * ((h:ℝ) + 1) ≤ (t:ℝ) * ((t:ℝ) + 1) := by nlinarith [hht, hh_pos]
  have hDbig : (h:ℝ) * ((h:ℝ) + 1) * L < D :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbound' hL_pos.le) hD
  have hDpos : 0 < D := lt_of_le_of_lt (by positivity) hDbig
  have hkey : (h:ℝ) < D * X0 := by
    rw [hX0d, mul_one_div, lt_div_iff₀ hposHL]
    nlinarith [hDbig]
  set ε := (X0 - (h:ℝ) / D) / 2 with hε_def
  have hhD : (h:ℝ) / D < X0 := by
    rw [div_lt_iff₀ hDpos]; nlinarith [hkey]
  have hεpos : 0 < ε := by rw [hε_def]; linarith [hhD]
  have hεltX0 : ε < X0 := by
    rw [hε_def]
    have : (0:ℝ) < (h:ℝ) / D := by positivity
    linarith
  have hXε : (0:ℝ) < X0 - ε := by rw [hε_def]; linarith [hhD]
  have hDne : D ≠ 0 := hDpos.ne'
  have hCltD : (h:ℝ) / (X0 - ε) < D := by
    rw [div_lt_iff₀ hXε]
    have hDe : D * (X0 - ε) = (D * X0 + (h:ℝ)) / 2 := by
      rw [hε_def]; field_simp; ring
    rw [hDe]; linarith [hkey]
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℕ, ∀ᶠ k in atTop, 0 < Q k ∧ Squarefree (Q k) ∧ (∀ q, Nat.Prime q → q ∣ Q k → α * (p ^ (Nat.totient t * k) : ℝ) < q ∧ q < β * (p ^ (Nat.totient t * k) : ℝ) ∧ q ≡ 1 [MOD t]) ∧ (Q k : ℤ) ≡ ρ [ZMOD p] ∧ ((β - α) / L - ε) * (p ^ (Nat.totient t * k) : ℝ) ≤ Real.log (Q k) := by
    have := @selection_lemma t (by linarith) p hp (Nat.Coprime.gcd_eq_one (by
    exact hp.coprime_iff_not_dvd.mpr fun h => hcop <| Int.natCast_dvd_natCast.mpr h)) ρ hρ α β (by
    exact div_pos ( Nat.cast_pos.mpr ( Nat.sub_pos_of_lt hce ) ) ( Nat.cast_add_one_pos _ )) (by
    exact div_lt_one ( by positivity ) |>.2 ( by linarith )) ε hεpos
    generalize_proofs at *;
    obtain ⟨ Q, hQ ⟩ := Filter.eventually_atTop.mp this;
    choose! Q hQ using hQ;
    use fun k => Q (p ^ (Nat.totient t * k));
    have h_exp_growth : Filter.Tendsto (fun k : ℕ => (p : ℝ) ^ (Nat.totient t * k)) Filter.atTop Filter.atTop := by
      exact tendsto_pow_atTop_atTop_of_one_lt ( mod_cast hp.one_lt ) |> Filter.Tendsto.comp <| Filter.tendsto_id.nsmul_atTop <| Nat.pos_of_ne_zero <| by aesop;
    exact h_exp_growth.eventually_ge_atTop _ |> fun h => h.mono fun k hk => hQ _ hk;
  refine' ⟨ fun k => e * Q k * p ^ ( Nat.totient t * k ) - h * p ^ ( Nat.totient t * k ), fun k => e * Q k * p ^ ( Nat.totient t * k ), _, _, _ ⟩;
  · refine' Filter.tendsto_atTop_mono' _ _ _;
    use fun k => p ^ ( Nat.totient t * k );
    · filter_upwards [ hQ, Filter.eventually_gt_atTop 0 ] with k hk hk';
      refine' Nat.le_sub_of_add_le _;
      nlinarith [ Nat.sub_add_cancel hce.le, pow_pos hp.pos ( Nat.totient t * k ), mul_le_mul_right ( show e ≥ 2 by linarith ) ( p ^ ( Nat.totient t * k ) ) ];
    · exact tendsto_pow_atTop_atTop_of_one_lt hp.one_lt |> Filter.Tendsto.comp <| Filter.tendsto_id.nsmul_atTop <| Nat.pos_of_ne_zero <| by aesop;
  · filter_upwards [ hQ, Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( Nat.log p ( e * ( 2 * t ) ) ) ] with k hk hk' hk'';
    apply caseI_isDrop (t := t);
    any_goals tauto;
    exact_mod_cast hcop;
    exact ⟨ t.totient * k, Nat.mul_pos ( Nat.pos_of_ne_zero ( by aesop_cat ) ) hk', rfl ⟩;
    · have h_euler : p ^ Nat.totient t ≡ 1 [MOD t] := by
        exact Nat.ModEq.pow_totient <| Nat.coprime_iff_gcd_eq_one.mpr <| hp.coprime_iff_not_dvd.mpr fun h => hcop <| mod_cast h;
      simpa [ pow_mul ] using h_euler.pow k;
    · simp +zetaDelta at *;
      intro q hq hq'; specialize hk; have := hk.2.2.1 q hq hq'; rw [ div_mul_eq_mul_div, div_lt_iff₀ ] at this <;> norm_cast at * <;> simp_all +decide [ Nat.succ_mul ] ;
      grind;
    · exact Int.ModEq.trans ( Int.ModEq.mul_left _ hk.2.2.2.1 ) hρmod;
    · exact fun h => hρ <| Int.dvd_of_emod_eq_zero <| hk.2.2.2.1.symm.trans <| Int.modEq_zero_iff_dvd.mpr h;
    · refine' lt_of_lt_of_le ( Nat.lt_pow_of_log_lt hp.one_lt hk'' ) _;
      exact pow_le_pow_right₀ hp.one_lt.le ( by nlinarith [ Nat.totient_pos.mpr ( by linarith : 0 < t ) ] );
  · filter_upwards [ hQ, Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( Nat.log p ( e * ( 2 * t ) ) ) ] with k hk hk' hk'';
    refine lt_of_le_of_lt ?_ hCltD;
    rw [ Nat.cast_sub ] <;> norm_num;
    · -- Simplify the logarithmic term in the denominator.
      have h_log_simplified : Real.log (e * Q k * p ^ (Nat.totient t * k) - h * p ^ (Nat.totient t * k)) ≥ Real.log (Q k) := by
        refine' Real.log_le_log ( Nat.cast_pos.mpr hk.1 ) _;
        rw [ le_sub_iff_add_le ];
        norm_cast;
        nlinarith [ Nat.sub_add_cancel hce.le, show p ^ ( Nat.totient t * k ) > 0 by exact pow_pos hp.pos _, show Q k > 0 by linarith, show e * p ^ ( Nat.totient t * k ) > 0 by exact mul_pos ( by linarith ) ( pow_pos hp.pos _ ), show h * p ^ ( Nat.totient t * k ) > 0 by exact mul_pos ( Nat.sub_pos_of_lt hce ) ( pow_pos hp.pos _ ) ];
      rw [ div_le_div_iff₀ ] <;> try linarith;
      · refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_log_simplified <| Nat.cast_nonneg _ );
        convert mul_le_mul_of_nonneg_left hk.2.2.2.2 ( Nat.cast_nonneg h ) using 1 ; ring_nf;
        grind;
      · refine' lt_of_lt_of_le _ h_log_simplified;
        refine' Real.log_pos _;
        norm_cast;
        contrapose! hk; interval_cases Q k ; simp_all +decide ;
        simp +zetaDelta at *;
        intro h₁ h₂; refine' mul_pos _ _ <;> norm_num at *;
        · refine' lt_of_lt_of_le hεltX0 _;
          field_simp;
          norm_num;
        · exact_mod_cast pow_pos hp.pos _;
    · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_add_cancel hce.le, show Q k ≥ 1 from hk.1 ] )

/-!  Case II construction.  Throughout, `b = e·Q·N` and `a = b - (e-c)·N`, with three
nonzero residue classes `c < d < e` satisfying `r c = r e = -r d`.  Compared to Case I,
each prime `q ∣ Q` now divides exactly one nonzero index `b - (e-d)·q`, and the
`p`-adic computation is governed by the quadratic
`f(x) = x² + 2(d-e)x + (e-c)(e-d)`. -/

section CaseIIConstr

variable (r : ℕ → ℤ) (t c d e : ℕ) (ht : 2 ≤ t)
    (hper : ∀ i, r (i + t) = r i)
    (hc : 1 ≤ c) (hrc : r c ≠ 0) (hrd : r d ≠ 0) (hre : r e ≠ 0)
    (hcd : c < d) (hde : d < e) (hcet : e - c ≤ t) (he2t : e ≤ 2 * t)
    (hval1 : r c = r e) (hval2 : r c = - r d)
    (hzero : ∀ i, c < i → i < e → i ≠ d → r i = 0)
    (p : ℕ) (hp : p.Prime) (hpbig : 2 * max (Rmax r t) t < p) (hcop : ¬ p ∣ t)
    (N Q : ℕ) (hNpow : ∃ j, 1 ≤ j ∧ N = p ^ j) (hNmod : N ≡ 1 [MOD t])
    (hQpos : 0 < Q) (hQsf : Squarefree Q)
    (hQprime : ∀ q, Nat.Prime q → q ∣ Q →
      (N < q ∧ (e - d) * q < (e - c) * N ∧ q ≡ 1 [MOD t]))
    (hroot : (p : ℤ) ∣ ((e : ℤ) * Q) ^ 2 + 2 * ((d : ℤ) - e) * ((e : ℤ) * Q)
        + ((e : ℤ) - c) * ((e : ℤ) - d))
    (hne0 : ¬ (p : ℤ) ∣ (e : ℤ) * Q)
    (hne1 : ¬ (p : ℤ) ∣ ((e : ℤ) * Q - ((e : ℤ) - d)))
    (hne2 : ¬ (p : ℤ) ∣ ((e : ℤ) * Q - ((e : ℤ) - c)))
    (hNlarge : e * (2 * t) < N)

include ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero hp hpbig hcop hNpow hNmod
    hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge

/-
`b = e·Q·N` divides `L_{a,b-1}`.
-/
lemma case2_bdvd :
    (e * Q * N) ∣ Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd;
  · obtain ⟨ j, hj₁, rfl ⟩ := hNpow;
    refine' Nat.Coprime.pow_right _ _;
    exact Nat.Coprime.symm ( hp.coprime_iff_not_dvd.mpr fun h => hne0 <| mod_cast h );
  · have hQ_div : ∀ q, Nat.Prime q → q ∣ Q → (q : ℕ) ∣ Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
      intro q hq hqQ
      have hq_div_L : ∃ i ∈ Finset.Icc (e * Q * N - (e - c) * N) (e * Q * N - 1), q ∣ i ∧ r i ≠ 0 := by
        refine' ⟨ e * Q * N - ( e - d ) * q, _, _, _ ⟩;
        · simp;
          constructor;
          · grind +qlia;
          · linarith [ Nat.sub_add_cancel ( show 1 ≤ e * Q * N from Nat.mul_pos ( Nat.mul_pos ( by linarith ) hQpos ) ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ), show ( e - d ) * q ≥ 1 from Nat.mul_pos ( Nat.sub_pos_of_lt hde ) hq.pos ];
        · exact Nat.dvd_sub ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right hqQ _ ) _ ) ( dvd_mul_left _ _ );
        · have h_mod : (e * Q * N - (e - d) * q) ≡ d [MOD t] := by
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
            rw [ Nat.cast_sub ];
            · simp_all +decide [ Nat.cast_sub ( show d ≤ e from by linarith ) ];
              have hQ_mod : Q ≡ 1 [MOD t] := by
                rw [ ← Nat.factorization_prod_pow_eq_self hQpos.ne' ];
                simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, Finsupp.prod ];
                exact Finset.prod_eq_one fun x hx => by rw [ hQprime x ( Nat.prime_of_mem_primeFactors hx ) ( Nat.dvd_of_mem_primeFactors hx ) |>.2.2 ] ; simp +decide ;
              simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
            · nlinarith [ Nat.sub_le e d, Nat.sub_le e c, hQprime q hq hqQ, Nat.mul_le_mul_left e ( show Q ≥ 1 from hQpos ) ];
          convert hrd using 1;
          convert rper_congr r t hper _;
          exact h_mod;
      obtain ⟨ i, hi₁, hi₂, hi₃ ⟩ := hq_div_L; exact dvd_trans hi₂ ( dvd_Lden r _ _ _ hi₁ hi₃ ) ;
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd;
    · refine' Nat.coprime_of_dvd' _;
      intro k hk hk₁ hk₂; have := hQprime k hk hk₂; nlinarith [ Nat.le_of_dvd ( by linarith ) hk₁ ] ;
    · apply dvd_Lden_of_exists;
      refine' ⟨ e * Q * N - e * t, _, _, _ ⟩ <;> norm_num;
      · constructor;
        · rw [ tsub_add_eq_add_tsub ];
          · exact le_tsub_of_add_le_left ( by nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ) ] );
          · nlinarith [ Nat.mul_le_mul_left e hQpos ];
        · nlinarith [ Nat.sub_add_cancel ( show 1 ≤ e * Q * N from Nat.mul_pos ( Nat.mul_pos ( by linarith ) ( by linarith ) ) ( by nlinarith ) ) ];
      · exact Nat.dvd_sub ( dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _ ) ( dvd_mul_right _ _ );
      · -- Since $e * Q * N - e * t \equiv e \pmod{t}$, we have $r (e * Q * N - e * t) = r e$.
        have h_cong : e * Q * N - e * t ≡ e [MOD t] := by
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          rw [ Nat.cast_sub ] <;> norm_num [ hNmod ];
          · rw [ ← Nat.prod_primeFactors_of_squarefree hQsf ] ; simp_all +decide [ Finset.prod_eq_one ] ;
          · nlinarith [ Nat.mul_le_mul_left e hQpos ];
        rw [ ← Nat.mod_add_div ( e * Q * N - e * t ) t, h_cong ];
        induction ( e * Q * N - e * t ) / t <;> simp_all +decide [ Nat.mul_succ, ← add_assoc ];
        convert hre using 1;
        rw [ ← Nat.mod_add_div e t, Function.Periodic.map_mod_nat hper ];
    · convert sqfree_dvd_of_forall_prime_dvd Q ( Lden r ( e * Q * N - ( e - c ) * N ) ( e * Q * N - 1 ) ) hQsf _;
      assumption;
  · apply dvd_Lden_of_exists;
    refine' ⟨ N * ( e * Q - ( e - c ) ), _, _, _ ⟩ <;> norm_num;
    · constructor;
      · nlinarith [ Nat.sub_add_cancel ( show e * Q ≥ e - c from le_trans ( Nat.sub_le _ _ ) ( by nlinarith ) ) ];
      · rw [ mul_comm ];
        exact Nat.le_sub_one_of_lt ( mul_lt_mul_of_pos_right ( Nat.sub_lt ( by nlinarith ) ( Nat.sub_pos_of_lt ( by linarith ) ) ) ( Nat.pos_of_ne_zero ( by aesop_cat ) ) );
    · -- Since $N \equiv 1 \pmod{t}$, we have $N * (e * Q - (e - c)) \equiv e * Q - (e - c) \equiv c \pmod{t}$.
      have h_cong : N * (e * Q - (e - c)) ≡ c [MOD t] := by
        have h_cong : Q ≡ 1 [MOD t] := by
          apply sqfree_prod_congr_one Q t hQsf;
          exact fun q hq hq' => hQprime q hq hq' |>.2.2;
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        rw [ Nat.cast_sub ] <;> norm_num [ h_cong ];
        · rw [ Nat.cast_sub ] <;> norm_num ; linarith;
        · nlinarith only [ hc, hQpos ];
      convert hrc using 1;
      rw [ ← rper_congr r t hper h_cong ]

/-
The lcm is unchanged.
-/
lemma case2_L :
    Lden r (e * Q * N - (e - c) * N) (e * Q * N)
      = Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
  apply Lden_top_eq;
  · exact Nat.sub_lt ( Nat.mul_pos ( Nat.mul_pos ( by linarith ) hQpos ) ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ( Nat.mul_pos ( Nat.sub_pos_of_lt ( by linarith ) ) ( Nat.pos_of_ne_zero ( by aesop_cat ) ) );
  · exact Or.inr <| case2_bdvd r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge

/-
Each prime factor of `Q` does not divide `X_{a,b-1}`.
-/
lemma case2_q :
    ∀ q, Nat.Prime q → q ∣ Q →
      ¬ (q : ℤ) ∣ Xnum r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
  intros q hq hqQ hqX
  set a := e * Q * N - (e - c) * N
  set b := e * Q * N - 1
  set L := Lden r a b
  set i0 := e * Q * N - (e - d) * q
  have ha_b : a ≤ i0 ∧ i0 ≤ b := by
    constructor;
    · grind +splitImp;
    · exact Nat.sub_le_sub_left ( Nat.one_le_iff_ne_zero.mpr <| mul_ne_zero ( Nat.sub_ne_zero_of_lt hde ) hq.ne_zero ) _
  have hi0_q : q ∣ i0 := by
    exact Nat.dvd_sub ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right hqQ _ ) _ ) ( dvd_mul_left _ _ )
  have hi0_r : r i0 = r d := by
    convert r_shift r t hper ( e * Q * N ) ( e - d ) q e _ _ _ _ using 1 <;> norm_num [ Nat.ModEq ] at *;
    · rw [ Nat.sub_sub_self ( by linarith ) ];
    · have hQ_mod : Q ≡ 1 [MOD t] := by
        exact sqfree_prod_congr_one Q t hQsf fun q hq hqQ => hQprime q hq hqQ |>.2.2;
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
    · exact hQprime q hq hqQ |>.2.2;
    · exact le_trans ( hQprime q hq hqQ |>.2.1.le ) ( by nlinarith [ Nat.sub_le e c, Nat.sub_le e d, Nat.mul_le_mul_left e hQpos ] )
  have hi0_L : ¬ (q : ℤ) ∣ (L / i0 : ℕ) := by
    have hi0_L : ¬ (q : ℤ) ∣ (L / i0 : ℕ) := by
      have h_unique : ∀ x ∈ Finset.Icc a b, q ∣ x → r x ≠ 0 → x = i0 := by
        intros x hx hxq hxr
        obtain ⟨i, hi1, hi2, rfl⟩ : ∃ i, 1 ≤ i ∧ i < e - c ∧ x = e * Q * N - i * q := by
          apply mult_char_gt (e * Q * N) q N (e - c) (by
          exact Nat.sub_pos_of_lt ( by linarith )) (by
          grind) (by
          exact hQprime q hq hqQ |>.1) (by
          exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right hqQ _ ) _) (by
          exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c, show Q > 0 from hQpos ] )) x (by
          exact Finset.mem_Icc.mp hx |>.1) (by
          exact Finset.mem_Icc.mp hx |>.2) hxq;
        have hi_r : r (e * Q * N - i * q) = r (e - i) := by
          apply r_shift r t hper (e * Q * N) i q e;
          · have hQ_mod : Q ≡ 1 [MOD t] := by
              apply sqfree_prod_congr_one Q t hQsf (fun q hq hqQ => (hQprime q hq hqQ).2.2);
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          · exact hQprime q hq hqQ |>.2.2;
          · grind;
          · contrapose! hx;
            rw [ Nat.sub_eq_zero_of_le hx.le ] ; norm_num;
            exact Nat.sub_ne_zero_of_lt ( by nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ), Nat.mul_le_mul_left e hQpos ] );
        grind
      convert not_dvd_lcm_div_of_unique q i0 ( ((Finset.Icc a b).filter (fun i => r i ≠ 0)) ) hq _ _ _ using 1;
      · norm_cast;
      · intro x hx; exact Nat.pos_of_ne_zero (by
        exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1.trans_lt' ( Nat.sub_pos_of_lt ( by nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ), Nat.mul_le_mul_left e hQpos ] ) ) ));
      · simp only [Finset.mem_filter]; simp +decide [ hi0_r, hrd ] ;
        exact ha_b;
      · exact fun x hx hx' => h_unique x ( Finset.mem_filter.mp hx |>.1 ) hx' ( Finset.mem_filter.mp hx |>.2 );
    exact hi0_L
  have hi0_X : ¬(q : ℤ) ∣ (r i0 * ((L / i0 : ℕ) : ℤ)) := by
    have hi0_r_ne_zero : ¬ (q : ℤ) ∣ r i0 := by
      have hi0_r_ne_zero : (r i0).natAbs ≤ Rmax r t := by
        apply abs_r_le_Rmax r t hper (by linarith) i0;
      contrapose! hi0_r_ne_zero;
      have hq_gt_Rmax : q > 2 * max (Rmax r t) t := by
        have := hQprime q hq hqQ;
        obtain ⟨ j, hj₁, rfl ⟩ := hNpow; nlinarith [ Nat.pow_le_pow_right hp.one_lt.le hj₁ ] ;
      exact lt_of_lt_of_le ( by linarith [ Nat.le_max_left ( Rmax r t ) t, Nat.le_max_right ( Rmax r t ) t ] ) ( Nat.le_of_dvd ( Int.natAbs_pos.mpr ( show r i0 ≠ 0 from by aesop ) ) ( Int.natCast_dvd.mp hi0_r_ne_zero ) );
    exact mt ( Int.Prime.dvd_mul' hq ) ( by tauto );
  -- Every other index x with r x ≠ 0 has q ∤ x (uniqueness) but q ∣ L, so q ∣ (L/x) via `prime_dvd_lcm_div_of_not_dvd`.
  have h_other_X : ∀ x ∈ Finset.Icc a b, x ≠ i0 → (r x ≠ 0 → (q : ℤ) ∣ (L / x : ℕ)) := by
    intros x hx hx_ne_i0 hx_r_ne_zero
    have hx_q : ¬(q : ℕ) ∣ x := by
      intro hx_q_div_x
      have hx_q_div_i0 : x ∈ Finset.image (fun i => e * Q * N - i * q) (Finset.Ico 1 (e - c)) := by
        have := mult_char_gt ( e * Q * N ) q N ( e - c ) ?_ ?_ ?_ ?_ ?_ x ?_ ?_ hx_q_div_x <;> norm_num at *;
        any_goals omega;
        · exact ⟨ this.choose, ⟨ this.choose_spec.1, this.choose_spec.2.1 ⟩, this.choose_spec.2.2.symm ⟩;
        · exact hQprime q hq hqQ |>.1;
        · exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right hqQ _ ) _;
        · exact le_trans ( Nat.mul_le_mul_right _ ( Nat.sub_le _ _ ) ) ( Nat.mul_le_mul_right _ ( by nlinarith ) );
      obtain ⟨ i, hi, rfl ⟩ := Finset.mem_image.mp hx_q_div_i0;
      have hx_r_zero : r (e * Q * N - i * q) = r (e - i) := by
        apply r_shift r t hper (e * Q * N) i q e (by
        have hM_mod : Q ≡ 1 [MOD t] := by
          exact sqfree_prod_congr_one Q t hQsf fun q hq hqQ => hQprime q hq hqQ |>.2.2;
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]) (by
        exact hQprime q hq hqQ |>.2.2) (by
        exact le_trans ( Finset.mem_Ico.mp hi |>.2.le ) ( Nat.sub_le _ _ )) (by
        contrapose! hx;
        rw [ Nat.sub_eq_zero_of_le hx.le ] ; norm_num;
        exact Nat.sub_ne_zero_of_lt ( by nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ), Nat.mul_le_mul_left e hQpos ] ));
      grind +qlia
    have hx_L : q ∣ L := by
      exact dvd_Lden_of_exists r a b q ⟨ i0, by
        exact Finset.mem_Icc.mpr ⟨ ha_b.1, ha_b.2 ⟩, hi0_q, by
        grind ⟩
    exact (by
    convert Int.natCast_dvd_natCast.mpr ( prime_dvd_lcm_div_of_not_dvd q x ( Finset.filter ( fun i => r i ≠ 0 ) ( Finset.Icc a b ) ) hq ?_ ?_ hx_L ) using 1;
    · aesop;
    · assumption);
  -- Split the sum at i0 with `Finset.sum_eq_add_sum_diff_singleton` to derive the contradiction.
  have h_split_sum : Xnum r a b = r i0 * ((L / i0 : ℕ) : ℤ) + ∑ x ∈ Finset.Icc a b \ {i0}, r x * ((L / x : ℕ) : ℤ) := by
    rw [Xnum_sum]; simp +decide [ Finset.sum_eq_add_sum_diff_singleton ( show i0 ∈ Finset.Icc a b from Finset.mem_Icc.mpr ⟨ ha_b.1, ha_b.2 ⟩ ) ] ;
    rfl;
  -- Since $q \mid Xnum r a b$, we have $q \mid \sum_{x \in \text{Finset.Icc } a b \setminus \{i0\}} r x * (L / x)$.
  have h_sum_div : (q : ℤ) ∣ ∑ x ∈ Finset.Icc a b \ {i0}, r x * ((L / x : ℕ) : ℤ) := by
    exact Finset.dvd_sum fun x hx => if hx' : r x = 0 then by simp +decide [ hx' ] else dvd_mul_of_dvd_right ( h_other_X x ( Finset.mem_sdiff.mp hx |>.1 ) ( by aesop ) hx' ) _;
  exact hi0_X ( by simpa using dvd_sub hqX h_sum_div |> fun x => by simpa [ h_split_sum ] using x )

/-
The `p`-adic valuation of `L` equals that of `N` (i.e. `= j`).
-/
lemma case2_pval :
    (Lden r (e * Q * N - (e - c) * N) (e * Q * N - 1)).factorization p
      = N.factorization p := by
  obtain ⟨ j, hj, rfl ⟩ := hNpow;
  -- Show that every x ∈ ((Finset.Icc a (b-1)).filter (fun i => r i ≠ 0)) has x.factorization p ≤ j.
  have h_factorization_le_j : ∀ x ∈ ((Finset.Icc (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1)).filter (fun i => r i ≠ 0)), x.factorization p ≤ j := by
    intro x hx
    by_contra h_contra;
    -- Since $p^{j+1} \mid x$, we have $p^j \mid x$, and thus $x = M - i \cdot p^j$ for some $1 \leq i \leq e - c$.
    obtain ⟨i, hi1, hi2⟩ : ∃ i, 1 ≤ i ∧ i ≤ e - c ∧ x = e * Q * p ^ j - i * p ^ j := by
      apply mult_char_self;
      any_goals omega;
      · exact dvd_mul_left _ _;
      · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c, show Q ≥ 1 from hQpos ] );
      · exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1;
      · exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2;
      · exact Nat.dvd_trans ( pow_dvd_pow _ ( le_of_not_ge h_contra ) ) ( Nat.ordProj_dvd _ _ );
    -- Since $r x \neq 0$, we have $r (e - i) \neq 0$.
    have h_r_e_i_ne_zero : r (e - i) ≠ 0 := by
      have h_r_e_i_ne_zero : r (e * Q * p ^ j - i * p ^ j) = r (e - i) := by
        apply r_shift;
        exact hper;
        · have hQmod : Q ≡ 1 [MOD t] := by
            exact sqfree_prod_congr_one Q t hQsf fun q hq hq' => hQprime q hq hq' |>.2.2;
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        · exact hNmod;
        · exact le_trans hi2.1 ( Nat.sub_le _ _ );
        · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c ] );
      simp only [Finset.mem_filter] at hx; aesop;
    -- Since $r (e - i) \neq 0$, we have $e - i \in \{c, d\}$.
    have h_e_i_in_cd : e - i = c ∨ e - i = d := by
      grind;
    cases h_e_i_in_cd <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ];
    · rw [ show e * Q * p ^ j - i * p ^ j = p ^ j * ( e * Q - i ) by rw [ Nat.mul_sub_left_distrib ] ; ring_nf ] at h_contra ; rw [ Nat.factorization_mul ] at h_contra <;> simp_all +decide;
      · rw [ Nat.factorization_eq_zero_of_not_dvd ] at h_contra <;> norm_num at *;
        rw [ ← Int.natCast_dvd_natCast ] ; simp_all +decide [ Nat.cast_sub ( show i ≤ e * Q from by nlinarith [ Nat.sub_le e c ] ) ] ;
        grind;
      · grind;
      · exact Nat.sub_ne_zero_of_lt ( by nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ) ] );
    · rw [ show e * Q * p ^ j - i * p ^ j = p ^ j * ( e * Q - i ) by rw [ Nat.mul_sub_left_distrib ] ; ring_nf ] at h_contra ; rw [ Nat.factorization_mul ] at h_contra <;> simp_all +decide;
      · rw [ Nat.factorization_eq_zero_of_not_dvd ] at h_contra <;> norm_num at *;
        rw [ ← Int.natCast_dvd_natCast ] ; simp_all +decide [ Nat.cast_sub ( show i ≤ e * Q from by nlinarith [ Nat.sub_le e c ] ) ] ;
        grind;
      · grind;
      · exact Nat.sub_ne_zero_of_lt ( by nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ) ] );
  refine' le_antisymm _ _;
  · convert factorization_lcm_sup p _ _ |> le_of_eq |> le_trans <| Finset.sup_le _;
    · simp only [Finset.mem_filter]; norm_num;
      intro i hi₁ hi₂ hi₃; contrapose! hi₃; simp_all +decide ;
      exact absurd hi₁ ( by nlinarith [ Nat.sub_lt ( by linarith : 0 < e ) ( by linarith : 0 < c ), pow_pos hp.pos j, mul_pos ( by linarith : 0 < e ) ( pow_pos hp.pos j ), mul_pos ( by linarith : 0 < Q ) ( pow_pos hp.pos j ) ] );
    · simp_all +decide;
  · refine' Nat.factorization_le_iff_dvd ( by aesop ) ( _ ) |>.2 _ p;
    · refine' Lden_ne_zero _ _ _ _;
      simp +zetaDelta at *;
      intro i hi₁ hi₂; contrapose! hi₁; simp_all +decide ;
      gcongr;
      · exact pow_pos hp.pos _;
      · nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ) ];
    · refine' dvd_trans _ ( case2_bdvd r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop ( p ^ j ) Q ⟨ j, hj, rfl ⟩ hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge );
      exact dvd_mul_left _ _

/-
`p ∣ X_{a,b}`.
-/
lemma case2_p1 :
    (p : ℤ) ∣ Xnum r (e * Q * N - (e - c) * N) (e * Q * N) := by
  -- By the definition of $Xnum$, we can write it as a sum of terms involving $r_i$ and $Lden$.
  set a := e * Q * N - (e - c) * N
  set b := e * Q * N
  set mid := e * Q * N - (e - d) * N
  set s := r e;
  -- By the definition of $Xnum$, we can write it as a sum of terms involving $r_i$ and $Lden$. We split the sum into three parts: the terms involving $a$, $mid$, and $b$.
  have hXnum_split : Xnum r a b = r a * (Lden r a b / a : ℤ) + r mid * (Lden r a b / mid : ℤ) + r b * (Lden r a b / b : ℤ) + ∑ i ∈ Finset.Icc a b \ {a, mid, b}, r i * (Lden r a b / i : ℤ) := by
    have hXnum_split : Xnum r a b = ∑ i ∈ Finset.Icc a b, r i * (Lden r a b / i : ℤ) := by
      exact Xnum_sum_int r a b;
    rw [ hXnum_split, ← Finset.sum_sdiff <| show { a, mid, b } ⊆ Finset.Icc a b from ?_ ];
    · rw [ Finset.sum_insert, Finset.sum_insert ] <;> norm_num;
      · ring;
      · exact ne_of_lt ( Nat.sub_lt ( Nat.mul_pos ( Nat.mul_pos ( by linarith ) ( by linarith ) ) ( by linarith [ show N > 0 from Nat.pos_of_ne_zero ( by aesop_cat ) ] ) ) ( Nat.mul_pos ( Nat.sub_pos_of_lt ( by linarith ) ) ( by linarith [ show N > 0 from Nat.pos_of_ne_zero ( by aesop_cat ) ] ) ) );
      · constructor;
        · rw [ tsub_right_inj ];
          · exact ne_of_gt ( mul_lt_mul_of_pos_right ( by omega ) ( by nlinarith ) );
          · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c ] );
          · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e d, Nat.sub_le e c, mul_pos hQpos ( Nat.pos_of_ne_zero ( by aesop_cat : N ≠ 0 ) ) ] );
        · exact ne_of_lt ( Nat.sub_lt ( by nlinarith [ mul_pos hQpos ( show 0 < N by nlinarith ) ] ) ( by nlinarith [ Nat.sub_pos_of_lt ( by linarith : c < e ) ] ) );
    · simp +decide [ Finset.insert_subset_iff ];
      exact ⟨ Nat.sub_le _ _, ⟨ Nat.sub_le_sub_left ( Nat.mul_le_mul_right _ ( Nat.sub_le_sub_left hcd.le _ ) ) _, Nat.sub_le _ _ ⟩, Nat.sub_le _ _ ⟩;
  -- By the properties of the gcd and the definition of $Lden$, we know that $p \mid Lden r a b / i$ for all $i \in \text{Finset.Icc } a b \setminus \{a, mid, b\}$.
  have h_div : ∀ i ∈ Finset.Icc a b \ {a, mid, b}, r i ≠ 0 → (p : ℤ) ∣ (Lden r a b / i : ℤ) := by
    intros i hi hri
    have h_div_i : ¬(N ∣ i) := by
      intro hdiv
      have h_eq : ∃ k, i = e * Q * N - k * N ∧ 0 ≤ k ∧ k ≤ e - c := by
        obtain ⟨ k, hk ⟩ := hdiv;
        simp +zetaDelta at *;
        exact ⟨ e * Q - k, by rw [ hk, tsub_mul, mul_comm ] ; rw [ Nat.sub_sub_self ( by nlinarith ) ], Nat.sub_le_of_le_add <| by nlinarith ⟩;
      obtain ⟨ k, rfl, hk₀, hk₁ ⟩ := h_eq;
      have h_eq : r (e * Q * N - k * N) = r (e - k) := by
        apply r_shift;
        exact hper;
        · simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          rw [ ← Nat.prod_primeFactors_of_squarefree hQsf ] ; simp_all +decide [ Finset.prod_eq_one ] ;
        · exact hNmod;
        · exact le_trans hk₁ ( Nat.sub_le _ _ );
        · exact le_trans ( Nat.mul_le_mul_right _ ( show k ≤ e by omega ) ) ( by nlinarith [ Nat.mul_le_mul_left e hQpos ] );
      by_cases hk : e - k = c ∨ e - k = d ∨ e - k = e; all_goals grind;
    have h_div_i : (Nat.factorization i p) < (Nat.factorization (Lden r a b) p) := by
      have h_div_i : (Nat.factorization i p) < (Nat.factorization N p) := by
        contrapose! h_div_i;
        rw [ ← Nat.factorization_le_iff_dvd ];
        · obtain ⟨ j, hj₁, rfl ⟩ := hNpow; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
        · grind;
        · grind +qlia;
      have h_div_i : (Nat.factorization (Lden r a b) p) = (Nat.factorization N p) := by
        convert case2_pval r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge using 1;
        convert congr_arg ( fun x => Nat.factorization x p ) ( case2_L r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge ) using 1;
      grind;
    norm_cast;
    rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
    · rw [ Nat.factorization_div ];
      · intro q; by_cases hq : p = q <;> simp_all +decide ;
        exact Nat.sub_pos_of_lt h_div_i;
      · apply dvd_Lden;
        · exact Finset.mem_sdiff.mp hi |>.1;
        · assumption;
    · exact hp.ne_zero;
    · refine' ⟨ _, _ ⟩;
      · grind;
      · refine' Nat.le_of_dvd ( Nat.pos_of_ne_zero _ ) ( dvd_Lden r a b i _ _ );
        · intro H; simp_all +decide [ Lden, Finset.mem_filter ] ;
          rw [ Nat.sub_eq_zero_iff_le ] at H ; nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ), Nat.mul_le_mul_left e hQpos ];
        · exact Finset.mem_sdiff.mp hi |>.1;
        · grind +qlia;
  -- By the properties of the gcd and the definition of $Lden$, we know that $p \mid r a * (Lden r a b / a : ℤ) + r mid * (Lden r a b / mid : ℤ) + r b * (Lden r a b / b : ℤ)$.
  have h_div_sum : (p : ℤ) ∣ r a * (Lden r a b / a : ℤ) + r mid * (Lden r a b / mid : ℤ) + r b * (Lden r a b / b : ℤ) := by
    -- By the properties of the gcd and the definition of $Lden$, we know that $r a = r c$, $r mid = r d$, and $r b = r e$.
    have h_r_eq : r a = r c ∧ r mid = r d ∧ r b = r e := by
      have h_r_eq : ∀ i, r i = r (i % t) := by
        exact fun i => by rw [ ← Nat.mod_add_div i t, Function.Periodic.map_mod_nat hper ] ;
      have h_mod : a % t = c % t ∧ mid % t = d % t ∧ b % t = e % t := by
        have h_mod : Q ≡ 1 [MOD t] := by
          exact sqfree_prod_congr_one Q t hQsf fun q hq hq' => hQprime q hq hq' |>.2.2;
        zify;
        rw [ Nat.cast_sub, Nat.cast_sub ] <;> push_cast;
        · simp +decide [ ← ZMod.intCast_eq_intCast_iff', Nat.cast_sub ( show c ≤ e from by linarith ), Nat.cast_sub ( show d ≤ e from by linarith ) ];
          simp +zetaDelta at *;
          simp +decide [ ← ZMod.natCast_eq_natCast_iff ] at *;
          simp +decide [ hNmod, h_mod ];
        · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e d, Nat.mul_le_mul_left e hQpos ] );
        · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e c, Nat.mul_le_mul_left e hQpos ] );
      simp +decide [ h_r_eq, h_mod ];
    -- By the properties of the gcd and the definition of $Lden$, we know that $Lden r a b / a = Lden r a b / (N * (e * Q - (e - c)))$, $Lden r a b / mid = Lden r a b / (N * (e * Q - (e - d)))$, and $Lden r a b / b = Lden r a b / (N * e * Q)$.
    have h_div_eq : (Lden r a b / a : ℤ) * (e * Q - (e - c)) = (Lden r a b / N : ℤ) ∧ (Lden r a b / mid : ℤ) * (e * Q - (e - d)) = (Lden r a b / N : ℤ) ∧ (Lden r a b / b : ℤ) * (e * Q) = (Lden r a b / N : ℤ) := by
      have h_div_eq : a ∣ Lden r a b ∧ mid ∣ Lden r a b ∧ b ∣ Lden r a b := by
        refine' ⟨ _, _, _ ⟩;
        · convert dvd_Lden r a b a _ _ using 1;
          · exact Finset.mem_Icc.mpr ⟨ le_rfl, Nat.sub_le _ _ ⟩;
          · grind;
        · apply dvd_Lden;
          · simp +zetaDelta at *;
            rw [ tsub_add_eq_add_tsub ];
            · exact le_tsub_of_add_le_left ( by nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ), Nat.sub_add_cancel ( by linarith : d ≤ e ) ] );
            · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_le e d, Nat.mul_le_mul_left e hQpos ] );
          · grind +qlia;
        · apply dvd_Lden;
          · exact Finset.mem_Icc.mpr ⟨ Nat.sub_le _ _, le_rfl ⟩;
          · grind;
      have h_div_eq : (Lden r a b / a : ℤ) * a = Lden r a b ∧ (Lden r a b / mid : ℤ) * mid = Lden r a b ∧ (Lden r a b / b : ℤ) * b = Lden r a b := by
        exact ⟨ mod_cast Nat.div_mul_cancel h_div_eq.1, mod_cast Nat.div_mul_cancel h_div_eq.2.1, mod_cast Nat.div_mul_cancel h_div_eq.2.2 ⟩;
      have h_div_eq : (Lden r a b / a : ℤ) * (e * Q - (e - c)) * N = Lden r a b ∧ (Lden r a b / mid : ℤ) * (e * Q - (e - d)) * N = Lden r a b ∧ (Lden r a b / b : ℤ) * (e * Q) * N = Lden r a b := by
        grind;
      exact ⟨ Eq.symm ( Int.ediv_eq_of_eq_mul_left ( Nat.cast_ne_zero.mpr <| by aesop_cat ) <| by linarith ), Eq.symm ( Int.ediv_eq_of_eq_mul_left ( Nat.cast_ne_zero.mpr <| by aesop_cat ) <| by linarith ), Eq.symm ( Int.ediv_eq_of_eq_mul_left ( Nat.cast_ne_zero.mpr <| by aesop_cat ) <| by linarith ) ⟩;
    have h_div_sum : (p : ℤ) ∣ (Lden r a b / N : ℤ) * (s * ((e * Q) ^ 2 + 2 * (d - e) * (e * Q) + (e - c) * (e - d))) := by
      exact dvd_mul_of_dvd_right ( dvd_mul_of_dvd_right hroot _ ) _;
    have h_div_sum : (p : ℤ) ∣ (r a * (Lden r a b / a : ℤ) + r mid * (Lden r a b / mid : ℤ) + r b * (Lden r a b / b : ℤ)) * (e * Q * (e * Q - (e - d)) * (e * Q - (e - c))) := by
      grind;
    haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
  convert dvd_add h_div_sum ( show ( p : ℤ ) ∣ ∑ i ∈ Finset.Icc a b \ { a, mid, b }, r i * ( Lden r a b / i : ℤ ) from Finset.dvd_sum fun i hi => ?_ ) using 1;
  by_cases hi' : r i = 0 <;> simp_all +decide [ dvd_mul_of_dvd_right ]

/-
`p ∤ X_{a,b-1}`.
-/
lemma case2_p2 :
    ¬ (p : ℤ) ∣ Xnum r (e * Q * N - (e - c) * N) (e * Q * N - 1) := by
  intro h;
  -- By `case2_p1`, (p:ℤ) ∣ Xnum r a b. Subtracting, (p:ℤ) ∣ r b * (Lden r a b / b).
  have h_div : (p : ℤ) ∣ r (e * Q * N) * ((Lden r (e * Q * N - (e - c) * N) (e * Q * N) / (e * Q * N) : ℕ) : ℤ) := by
    convert dvd_sub ( case2_p1 r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge ) ( h ) using 1;
    rw [ Xnum_succ ];
    · ring;
    · exact Nat.sub_lt ( by nlinarith [ mul_pos hQpos ( show 0 < N by obtain ⟨ j, hj, rfl ⟩ := hNpow; exact pow_pos hp.pos _ ) ] ) ( by nlinarith [ Nat.sub_pos_of_lt ( by linarith : c < e ), show 0 < N by obtain ⟨ j, hj, rfl ⟩ := hNpow; exact pow_pos hp.pos _ ] );
    · convert case2_L r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge using 1;
  -- But $p \nmid r_b$ and $p \nmid (Lden r a b / b)$.
  have h_not_div_rb : ¬(p : ℤ) ∣ r (e * Q * N) := by
    have h_not_div_r : |r (e * Q * N)| ≤ Rmax r t := by
      convert abs_r_le_Rmax r t hper ( by linarith ) ( e * Q * N ) using 1;
      norm_num [ ← Int.ofNat_le ];
    exact fun h => by have := Int.le_of_dvd ( abs_pos.mpr ( show r ( e * Q * N ) ≠ 0 from by
                                                              rw [ show r ( e * Q * N ) = r e from ?_ ] ; aesop;
                                                              rw [ ← Nat.mod_add_div ( e * Q * N ) t, show e * Q * N % t = e % t from ?_ ];
                                                              · rw [ show r ( e % t + t * ( e * Q * N / t ) ) = r ( e % t ) from Nat.recOn ( e * Q * N / t ) rfl fun n hn => by rw [ Nat.mul_succ, ← add_assoc, hper, hn ] ] ; rw [ ← Nat.mod_add_div e t ] ; simp +decide ;
                                                                exact Nat.recOn ( e / t ) rfl fun n hn => by rw [ Nat.mul_succ, ← add_assoc, hper, hn ] ;
                                                              · have hQmod : Q ≡ 1 [MOD t] := by
                                                                  apply sqfree_prod_congr_one Q t hQsf;
                                                                  exact fun q hq hq' => hQprime q hq hq' |>.2.2;
                                                                simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
                                                                simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ) ) ( by simpa using h ) ; linarith [ abs_le.mp h_not_div_r, Nat.le_max_left ( Rmax r t ) t, Nat.le_max_right ( Rmax r t ) t ] ;
  have h_not_div_Lb : ¬(p : ℕ) ∣ (Lden r (e * Q * N - (e - c) * N) (e * Q * N) / (e * Q * N)) := by
    rw [ Nat.Prime.dvd_iff_one_le_factorization ] <;> norm_num [ hp ];
    · have h_not_div_Lb : (Lden r (e * Q * N - (e - c) * N) (e * Q * N)).factorization p = N.factorization p := by
        convert case2_pval r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge using 1;
        rw [ case2_L r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge ];
      rw [ Nat.factorization_div ] <;> norm_num [ h_not_div_Lb ];
      · rw [ Nat.factorization_mul ] <;> norm_num [ hp.ne_zero, hQpos.ne' ];
        · linarith;
        · grind;
      · convert case2_bdvd r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge using 1;
        exact case2_L r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge;
    · refine' ⟨ ⟨ ⟨ by linarith, by linarith ⟩, by aesop_cat ⟩, _ ⟩;
      refine' Nat.le_of_dvd ( Nat.pos_of_ne_zero _ ) _;
      · refine' Lden_ne_zero _ _ _ _;
        simp +zetaDelta at *;
        intro i hi₁ hi₂; contrapose! hi₁; nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ), mul_pos hQpos ( show 0 < N by obtain ⟨ j, hj₁, rfl ⟩ := hNpow; exact pow_pos hp.pos _ ) ] ;
      · convert case2_bdvd r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge using 1;
        convert case2_L r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop N Q hNpow hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge using 1;
  exact absurd ( Int.Prime.dvd_mul' hp h_div ) ( by norm_cast; aesop )

include he2t in
/-- The endpoint `b = e·Q·N` is a denominator-drop point for `a = b - (e-c)·N`. -/
lemma caseII_isDrop :
    (e * Q * N) ∈ Bset r (e * Q * N - (e - c) * N) := by
  obtain ⟨ j, hj, rfl ⟩ := hNpow;
  apply Set.mem_setOf_eq.mpr;
  refine' ⟨ Nat.sub_lt _ _, _ ⟩;
  · exact mul_pos ( mul_pos ( by linarith ) hQpos ) ( pow_pos hp.pos _ );
  · exact Nat.mul_pos ( Nat.sub_pos_of_lt ( by linarith ) ) ( pow_pos hp.pos _ );
  · convert drop_criterion r ( e * Q * p ^ j - ( e - c ) * p ^ j ) ( e * Q * p ^ j ) ( e * Q ) p j _ _ _ _ _ _ _ _ _;
    any_goals assumption;
    any_goals exact case2_p1 r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop ( p ^ j ) Q ⟨ j, hj, rfl ⟩ hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge;
    any_goals exact case2_L r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop ( p ^ j ) Q ⟨ j, hj, rfl ⟩ hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge;
    any_goals exact case2_p2 r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop ( p ^ j ) Q ⟨ j, hj, rfl ⟩ hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge;
    · have h_gcd : Nat.gcd (e * Q) (Xnum r (e * Q * p ^ j - (e - c) * p ^ j) (e * Q * p ^ j - 1)).natAbs ∣ e := by
        apply gcd_left_dvd_of_no_common;
        intro q hq hqQ;
        convert case2_q r t c d e ht hper hc hrc hrd hre hcd hde hcet hval1 hval2 hzero p hp hpbig hcop _ _ ⟨ j, hj, rfl ⟩ hNmod hQpos hQsf hQprime hroot hne0 hne1 hne2 hNlarge q hq hqQ using 1;
        norm_num [ ← Int.natCast_dvd_natCast ];
      refine' ⟨ fun h => _, fun h => _ ⟩;
      · exact fun _ => h;
      · refine' h ( lt_of_le_of_lt ( Nat.le_of_dvd ( by linarith ) h_gcd ) _ );
        exact lt_of_le_of_lt he2t (by nlinarith [Nat.le_max_right (Rmax r t) t]);
    · exact Nat.sub_lt ( by nlinarith [ mul_pos hQpos ( pow_pos hp.pos j ) ] ) ( Nat.mul_pos ( Nat.sub_pos_of_lt ( by linarith ) ) ( pow_pos hp.pos j ) );
    · rfl;
    · exact_mod_cast hne0;
    · intro i hi;
      contrapose! hNlarge; simp_all +decide ;
      exact absurd hi ( not_le_of_gt ( mul_lt_mul_of_pos_right ( by nlinarith [ Nat.sub_add_cancel ( by linarith : c ≤ e ) ] ) ( pow_pos hp.pos _ ) ) )

end CaseIIConstr

/-
From `(e-d)(c-d)` being a square mod `p`, the quadratic `f(x) = x²+2(d-e)x+(e-c)(e-d)`
has a root `x₀` mod `p` avoiding `0, e-d, e-c`.
-/
lemma caseII_root_exists (c d e p : ℕ) (hp : p.Prime)
    (hpec : ¬ (p:ℤ) ∣ ((e:ℤ) - c)) (hped : ¬ (p:ℤ) ∣ ((e:ℤ) - d))
    (hpdc : ¬ (p:ℤ) ∣ ((d:ℤ) - c))
    (hsq : IsSquare ((((e:ℤ) - d) * ((c:ℤ) - d)) : ZMod p)) :
    ∃ x0 : ℤ, (p:ℤ) ∣ (x0 ^ 2 + 2 * ((d:ℤ) - e) * x0 + ((e:ℤ) - c) * ((e:ℤ) - d)) ∧
      ¬ (p:ℤ) ∣ x0 ∧ ¬ (p:ℤ) ∣ (x0 - ((e:ℤ) - d)) ∧ ¬ (p:ℤ) ∣ (x0 - ((e:ℤ) - c)) := by
  obtain ⟨ s, hs ⟩ := hsq;
  haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
  refine' ⟨ ( e - d + s ).val, _, _, _, _ ⟩ <;> simp_all +decide;
  · grind;
  · grind;
  · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
  · grind

/-
Case II construction: Given `CaseII` and a target constant `D` strictly above
`t(t+1)φ(t)`, we build denominator-drop pairs `a k < b k` with ratio eventually `< D`.
-/
lemma caseII_construction (r : ℕ → ℤ) (t : ℕ) (ht : 2 ≤ t)
    (hper : ∀ i, r (i + t) = r i) (hCII : CaseII r t)
    (D : ℝ) (hD : (t : ℝ) * (t + 1) * (Nat.totient t) < D) :
    ∃ a b : ℕ → ℕ,
      Filter.Tendsto a Filter.atTop Filter.atTop ∧
      (∀ᶠ k in Filter.atTop, b k ∈ Bset r (a k)) ∧
      (∀ᶠ k in Filter.atTop, ((b k : ℝ) - (a k : ℝ)) / Real.log (a k) < D) := by
  obtain ⟨c, d, e, hc, hrc, hrd, hre, hcd, hde, hcet, he2t, hgap, hval1, hval2, hzero⟩ := hCII
  have hce : c < e := lt_trans hcd hde
  set h := e - c with hh_def
  set R := Rmax r t
  -- Choose a prime `p` above `2·max R t` making `(e-d)(c-d)` a square mod `p`.
  have hDint_ne : ((e:ℤ) - d) * ((c:ℤ) - d) ≠ 0 := by
    have h1 : (e:ℤ) - d ≠ 0 := by
      have : (d:ℤ) < e := by exact_mod_cast hde
      linarith
    have h2 : (c:ℤ) - d ≠ 0 := by
      have : (c:ℤ) < d := by exact_mod_cast hcd
      linarith
    exact mul_ne_zero h1 h2
  obtain ⟨p, hp, hpbig, hsq⟩ :
      ∃ p : ℕ, p.Prime ∧ 2 * max R t < p ∧ IsSquare (((((e:ℤ) - d) * ((c:ℤ) - d)) : ZMod p)) := by
    obtain ⟨p, hp, hpB, hsq⟩ := qr_prime (((e:ℤ) - d) * ((c:ℤ) - d)) hDint_ne (2 * max R t)
    refine ⟨p, hp, hpB, ?_⟩
    convert hsq using 2
    push_cast; ring
  have hcop : ¬ (p : ℤ) ∣ t := by
    intro hdvd
    have : (p : ℤ) ≤ t := Int.le_of_dvd (by exact_mod_cast (by linarith : 0 < t)) hdvd
    have : p ≤ t := by exact_mod_cast this
    have := Nat.le_max_right R t
    omega
  -- basic non-divisibilities: p ∤ e, e-c, e-d, d-c (all in (0,p))
  have hpe : ¬ (p : ℤ) ∣ (e : ℤ) := by
    intro hdvd
    have h1 : (p : ℤ) ≤ e := Int.le_of_dvd (by exact_mod_cast (by linarith : 0 < e)) hdvd
    have : p ≤ e := by exact_mod_cast h1
    have := Nat.le_max_right R t
    omega
  have hpec : ¬ (p : ℤ) ∣ ((e:ℤ) - c) := by
    intro hdvd
    have hpos : (0:ℤ) < (e:ℤ) - c := by
      have hlt' : (c:ℤ) < e := by exact_mod_cast hce
      linarith
    have h1 : (p : ℤ) ≤ (e:ℤ) - c := Int.le_of_dvd hpos hdvd
    have hlt : (e:ℤ) - c ≤ t := by
      have : ((e - c : ℕ) : ℤ) ≤ t := by exact_mod_cast hcet
      rwa [Nat.cast_sub hce.le] at this
    have := Nat.le_max_right R t
    have : (p:ℤ) ≤ t := le_trans h1 hlt
    have : p ≤ t := by exact_mod_cast this
    omega
  have hped : ¬ (p : ℤ) ∣ ((e:ℤ) - d) := by
    intro hdvd
    have hpos : (0:ℤ) < (e:ℤ) - d := by
      have hlt' : (d:ℤ) < e := by exact_mod_cast hde
      linarith
    have h1 : (p : ℤ) ≤ (e:ℤ) - d := Int.le_of_dvd hpos hdvd
    have hlt : (e:ℤ) - d ≤ t := by
      have : (e:ℤ) - c ≤ t := by
        have : ((e - c : ℕ) : ℤ) ≤ t := by exact_mod_cast hcet
        rwa [Nat.cast_sub hce.le] at this
      have : (d:ℤ) > c := by exact_mod_cast hcd
      linarith
    have := Nat.le_max_right R t
    have : (p:ℤ) ≤ t := le_trans h1 hlt
    have : p ≤ t := by exact_mod_cast this
    omega
  have hpdc : ¬ (p : ℤ) ∣ ((d:ℤ) - c) := by
    intro hdvd
    have hpos : (0:ℤ) < (d:ℤ) - c := by
      have hlt' : (c:ℤ) < d := by exact_mod_cast hcd
      linarith
    have h1 : (p : ℤ) ≤ (d:ℤ) - c := Int.le_of_dvd hpos hdvd
    have hlt : (d:ℤ) - c ≤ t := by
      have : (e:ℤ) - c ≤ t := by
        have : ((e - c : ℕ) : ℤ) ≤ t := by exact_mod_cast hcet
        rwa [Nat.cast_sub hce.le] at this
      have : (d:ℤ) < e := by exact_mod_cast hde
      linarith
    have := Nat.le_max_right R t
    have : (p:ℤ) ≤ t := le_trans h1 hlt
    have : p ≤ t := by exact_mod_cast this
    omega
  -- Get a root `x₀` of `f` mod `p` avoiding `0, e-d, e-c`.
  obtain ⟨x0, hf0, hx0_0, hx0_d, hx0_c⟩ := caseII_root_exists c d e p hp hpec hped hpdc hsq
  -- Choose `ρ` with `e·ρ ≡ x₀ (mod p)` and `p ∤ ρ`.
  obtain ⟨ρ, hρ, hρmod⟩ : ∃ ρ : ℤ, ¬ (p : ℤ) ∣ ρ ∧ (e : ℤ) * ρ ≡ x0 [ZMOD p] :=
    zmod_solve p hp (e : ℤ) x0 hpe hx0_0
  -- Real constants.
  set L := (Nat.totient t : ℝ) with hL_def
  set α := (1 : ℝ) with hα_def
  set β := (h : ℝ) / ((e : ℝ) - d) with hβ_def
  have hL_pos : 0 < L := by
    exact Nat.cast_pos.mpr (Nat.totient_pos.mpr (by linarith))
  have hh_pos : (0:ℝ) < (h : ℝ) := by
    have : 0 < h := Nat.sub_pos_of_lt hce
    exact_mod_cast this
  have hed_pos : (0:ℝ) < (e : ℝ) - d := by
    have : (d:ℤ) < e := by exact_mod_cast hde
    have : (d:ℝ) < e := by exact_mod_cast hde
    linarith
  have hdc_pos : (0:ℝ) < (d : ℝ) - c := by
    have : (c:ℝ) < d := by exact_mod_cast hcd
    linarith
  have hhR : (h : ℝ) = (e : ℝ) - (c : ℝ) := by
    rw [hh_def]; rw [Nat.cast_sub hce.le]
  have hbma : β - α = ((d:ℝ) - c) / ((e:ℝ) - d) := by
    rw [hβ_def, hα_def, hhR]
    field_simp
    ring
  set X0 := (β - α) / L with hX0d
  have hβgt : (1:ℝ) < β := by
    rw [hβ_def, lt_div_iff₀ hed_pos, hhR]
    have : (c:ℝ) < d := by exact_mod_cast hcd
    linarith
  have hX0pos : 0 < X0 := by
    rw [hX0d]; apply div_pos _ hL_pos; rw [hα_def]; linarith
  -- `h / X0 = h(e-d)L/(d-c) ≤ t(t+1)L < D`.
  have hkey : (h:ℝ) < D * X0 := by
    rw [hX0d, hbma, div_div, ← mul_div_assoc, lt_div_iff₀ (by positivity)]
    -- goal: h * ((e-d) * L) < D * (d - c)
    have hnat : (h:ℝ) * ((e:ℝ) - d) ≤ (t:ℝ) * ((t:ℝ) + 1) := by
      have h1 : (h:ℝ) ≤ (t:ℝ) := by exact_mod_cast hcet
      have h2 : (e:ℝ) - d ≤ (t:ℝ) := by
        have hcd' : (c:ℝ) ≤ d := by exact_mod_cast hcd.le
        have hstep : (e:ℝ) - d ≤ (e:ℝ) - c := by linarith
        rw [← hhR] at hstep; linarith [h1]
      nlinarith [hh_pos, hed_pos, h1, h2]
    have hdcge : (1:ℝ) ≤ (d:ℝ) - c := by
      have : (c:ℤ) + 1 ≤ d := by exact_mod_cast hcd
      have : (c:ℝ) + 1 ≤ d := by exact_mod_cast this
      linarith
    have hDpos : 0 < D := lt_trans (by positivity) hD
    nlinarith [hnat, hdcge, hD, hDpos, hL_pos, mul_pos hh_pos hed_pos]
  set ε := (X0 - (h:ℝ) / D) / 2 with hε_def
  have hDpos : 0 < D := lt_trans (by positivity) hD
  have hhD : (h:ℝ) / D < X0 := by
    rw [div_lt_iff₀ hDpos]; nlinarith [hkey]
  have hεpos : 0 < ε := by rw [hε_def]; linarith [hhD]
  have hεltX0 : ε < X0 := by
    rw [hε_def]
    have : (0:ℝ) < (h:ℝ) / D := by positivity
    linarith
  have hXε : (0:ℝ) < X0 - ε := by rw [hε_def]; linarith [hhD]
  have hDne : D ≠ 0 := hDpos.ne'
  have hCltD : (h:ℝ) / (X0 - ε) < D := by
    rw [div_lt_iff₀ hXε]
    have hDe : D * (X0 - ε) = (D * X0 + (h:ℝ)) / 2 := by
      rw [hε_def]; field_simp; ring
    rw [hDe]; linarith [hkey]
  -- Selection lemma.
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℕ, ∀ᶠ k in atTop, 0 < Q k ∧ Squarefree (Q k) ∧ (∀ q, Nat.Prime q → q ∣ Q k → α * (p ^ (Nat.totient t * k) : ℝ) < q ∧ q < β * (p ^ (Nat.totient t * k) : ℝ) ∧ q ≡ 1 [MOD t]) ∧ (Q k : ℤ) ≡ ρ [ZMOD p] ∧ (X0 - ε) * (p ^ (Nat.totient t * k) : ℝ) ≤ Real.log (Q k) := by
    have := @selection_lemma t (by linarith) p hp (Nat.Coprime.gcd_eq_one (by
      exact hp.coprime_iff_not_dvd.mpr fun hh => hcop <| Int.natCast_dvd_natCast.mpr hh)) ρ hρ α β (by rw [hα_def]; exact zero_lt_one) (by rw [hα_def]; exact hβgt) ε hεpos
    generalize_proofs at *
    obtain ⟨ Q, hQ ⟩ := Filter.eventually_atTop.mp this
    choose! Q hQ using hQ
    use fun k => Q (p ^ (Nat.totient t * k))
    have h_exp_growth : Filter.Tendsto (fun k : ℕ => (p : ℝ) ^ (Nat.totient t * k)) Filter.atTop Filter.atTop := by
      exact tendsto_pow_atTop_atTop_of_one_lt ( mod_cast hp.one_lt ) |> Filter.Tendsto.comp <| Filter.tendsto_id.nsmul_atTop <| Nat.pos_of_ne_zero <| by aesop
    exact h_exp_growth.eventually_ge_atTop _ |> fun hh => hh.mono fun k hk => hQ _ hk
  refine' ⟨ fun k => e * Q k * p ^ ( Nat.totient t * k ) - h * p ^ ( Nat.totient t * k ), fun k => e * Q k * p ^ ( Nat.totient t * k ), _, _, _ ⟩
  · -- tendsto a → ∞
    refine' Filter.tendsto_atTop_mono' _ _ _
    use fun k => p ^ ( Nat.totient t * k )
    · filter_upwards [ hQ, Filter.eventually_gt_atTop 0 ] with k hk hk'
      refine' Nat.le_sub_of_add_le _
      nlinarith [ Nat.sub_add_cancel hce.le, pow_pos hp.pos ( Nat.totient t * k ), mul_le_mul_right ( show e ≥ 2 by linarith ) ( p ^ ( Nat.totient t * k ) ) ]
    · exact tendsto_pow_atTop_atTop_of_one_lt hp.one_lt |> Filter.Tendsto.comp <| Filter.tendsto_id.nsmul_atTop <| Nat.pos_of_ne_zero <| by aesop
  · -- membership in Bset (denominator drop)
    filter_upwards [ hQ, Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( Nat.log p ( e * ( 2 * t ) ) ) ] with k hk hk' hk''
    have heqx0 : (e : ℤ) * (Q k) ≡ x0 [ZMOD p] :=
      (Int.ModEq.mul_left _ hk.2.2.2.1).trans hρmod
    refine caseII_isDrop r t c d e ht hper hc hrc hrd hre hcd hde hcet he2t hval1 hval2 hzero
      p hp hpbig (by exact_mod_cast hcop) (p ^ (Nat.totient t * k)) (Q k)
      ⟨Nat.totient t * k, Nat.mul_pos (Nat.totient_pos.mpr (by linarith)) hk', rfl⟩ ?_
      hk.1 hk.2.1 ?_ ?_ ?_ ?_ ?_ ?_
    · -- N ≡ 1 mod t
      have h_euler : p ^ Nat.totient t ≡ 1 [MOD t] :=
        Nat.ModEq.pow_totient <| Nat.coprime_iff_gcd_eq_one.mpr <| hp.coprime_iff_not_dvd.mpr fun hh => hcop <| mod_cast hh
      simpa [ pow_mul ] using h_euler.pow k
    · -- hQprime interval
      intro q hq hq'
      obtain ⟨hlo, hhi, hmod⟩ := hk.2.2.1 q hq hq'
      refine ⟨?_, ?_, hmod⟩
      · have : ((p ^ (Nat.totient t * k) : ℕ) : ℝ) < (q : ℝ) := by
          have := hlo; rw [hα_def] at this; simpa using this
        exact_mod_cast this
      · have hhi' : (q : ℝ) < ((h:ℝ) / ((e:ℝ) - d)) * (p ^ (Nat.totient t * k) : ℝ) := by
          rw [hβ_def] at hhi; exact hhi
        rw [div_mul_eq_mul_div, lt_div_iff₀ hed_pos] at hhi'
        have : ((e - d : ℕ) * q : ℝ) < ((e - c : ℕ) * (p ^ (Nat.totient t * k)) : ℝ) := by
          push_cast [Nat.cast_sub hde.le, Nat.cast_sub hce.le]
          rw [hhR] at *
          nlinarith [hhi']
        exact_mod_cast this
    · -- hroot
      have hcong : ((e:ℤ) * (Q k))^2 + 2 * ((d:ℤ) - e) * ((e:ℤ) * (Q k)) + ((e:ℤ) - c) * ((e:ℤ) - d)
          ≡ x0 ^ 2 + 2 * ((d:ℤ) - e) * x0 + ((e:ℤ) - c) * ((e:ℤ) - d) [ZMOD p] :=
        ((heqx0.pow 2).add (heqx0.mul_left (2 * ((d:ℤ) - e)))).add (Int.ModEq.refl _)
      exact Int.modEq_zero_iff_dvd.mp (hcong.trans (Int.modEq_zero_iff_dvd.mpr hf0))
    · -- hne0
      intro hdvd
      exact hx0_0 (Int.modEq_zero_iff_dvd.mp (heqx0.symm.trans (Int.modEq_zero_iff_dvd.mpr hdvd)))
    · -- hne1
      intro hdvd
      apply hx0_d
      have : x0 - ((e:ℤ) - d) ≡ 0 [ZMOD p] :=
        ((heqx0.sub_right ((e:ℤ) - d)).symm).trans (Int.modEq_zero_iff_dvd.mpr hdvd)
      exact Int.modEq_zero_iff_dvd.mp this
    · -- hne2
      intro hdvd
      apply hx0_c
      have : x0 - ((e:ℤ) - c) ≡ 0 [ZMOD p] :=
        ((heqx0.sub_right ((e:ℤ) - c)).symm).trans (Int.modEq_zero_iff_dvd.mpr hdvd)
      exact Int.modEq_zero_iff_dvd.mp this
    · -- hNlarge
      refine' lt_of_lt_of_le ( Nat.lt_pow_of_log_lt hp.one_lt hk'' ) _
      exact pow_le_pow_right₀ hp.one_lt.le ( by nlinarith [ Nat.totient_pos.mpr ( by linarith : 0 < t ) ] )
  · -- ratio bound
    filter_upwards [ hQ, Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( Nat.log p ( e * ( 2 * t ) ) ) ] with k hk hk' hk''
    refine lt_of_le_of_lt ?_ hCltD
    rw [ Nat.cast_sub ] <;> norm_num
    · have h_log_simplified : Real.log (e * Q k * p ^ (Nat.totient t * k) - h * p ^ (Nat.totient t * k)) ≥ Real.log (Q k) := by
        refine' Real.log_le_log ( Nat.cast_pos.mpr hk.1 ) _
        rw [ le_sub_iff_add_le ]
        norm_cast
        nlinarith [ Nat.sub_add_cancel hce.le, show p ^ ( Nat.totient t * k ) > 0 by exact pow_pos hp.pos _, show Q k > 0 by linarith, show e * p ^ ( Nat.totient t * k ) > 0 by exact mul_pos ( by linarith ) ( pow_pos hp.pos _ ), show h * p ^ ( Nat.totient t * k ) > 0 by exact mul_pos ( Nat.sub_pos_of_lt hce ) ( pow_pos hp.pos _ ) ]
      rw [ div_le_div_iff₀ ] <;> try linarith
      · refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_log_simplified <| Nat.cast_nonneg _ )
        convert mul_le_mul_of_nonneg_left hk.2.2.2.2 ( Nat.cast_nonneg h ) using 1 ; ring
      · refine' lt_of_lt_of_le _ h_log_simplified
        refine' Real.log_pos _
        norm_cast
        contrapose! hk; interval_cases Q k ; simp_all +decide
        simp +zetaDelta at *
        intro h₁ h₂; refine' mul_pos _ _ <;> norm_num at *
        · refine' lt_of_lt_of_le hεltX0 _
          field_simp
          norm_num
        · exact_mod_cast pow_pos hp.pos _
    · exact Nat.mul_le_mul_right _ ( by nlinarith [ Nat.sub_add_cancel hce.le, show Q k ≥ 1 from hk.1 ] )

/-
If `a → ∞` and `P (a k)` holds eventually, then `P` holds frequently.
-/
lemma frequently_of_tendsto_atTop (a : ℕ → ℕ) (P : ℕ → Prop)
    (ha : Tendsto a atTop atTop) (h : ∀ᶠ k in atTop, P (a k)) :
    ∃ᶠ n in atTop, P n := by
  simp_all +contextual [ Filter.frequently_atTop, Filter.eventually_atTop ];
  exact fun n => by rcases h with ⟨ m, hm ⟩ ; rcases Filter.eventually_atTop.mp ( ha.eventually_ge_atTop n ) with ⟨ k, hk ⟩ ; exact ⟨ a ( Max.max m k ), hk _ ( le_max_right _ _ ), hm _ ( le_max_left _ _ ) ⟩ ;

/-- From a construction subsequence `a k < b k` with denominator drops and ratio `< D`,
extract that infinitely many `a` admit a nearby drop `b` with `b < a + D·log a`. -/
lemma frequently_drop_of_construction (r : ℕ → ℤ) (D : ℝ)
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hmem : ∀ᶠ k in atTop, b k ∈ Bset r (a k))
    (hbound : ∀ᶠ k in atTop, ((b k : ℝ) - (a k : ℝ)) / Real.log (a k) < D) :
    ∃ᶠ (n : ℕ) in atTop, ∃ m, n < m ∧ (m : ℝ) < (n : ℝ) + D * Real.log n ∧
      vden r n m < vden r n (m - 1) := by
  apply frequently_of_tendsto_atTop a _ ha
  filter_upwards [hmem, hbound, ha.eventually_ge_atTop 2] with k hmemk hbk hagek
  refine ⟨b k, hmemk.1, ?_, hmemk.2⟩
  have hlog : 0 < Real.log (a k) := Real.log_pos (by exact_mod_cast hagek)
  rw [div_lt_iff₀ hlog] at hbk
  linarith [hbk]

/-- Let `r` be a period-`t` integer sequence, not all equal to `0`.  Then for
      every `ε > 0` there are infinitely many `a` such that there eaxists  `b`
      with `a < b < a + (1+ε)·t(t+1)·φ(t)·log a` and `v_{a,b} < v_{a,b-1}`. -/
theorem exists_nearby_drop (r : ℕ → ℤ) (t : ℕ) (ht : 1 ≤ t)
    (hper : ∀ i, r (i + t) = r i) (hne : ∃ i, r i ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ (a : ℕ) in atTop, ∃ b, a < b ∧
      (b : ℝ) < (a : ℝ) + (1 + ε) * ((t : ℝ) * (t + 1) * (Nat.totient t)) * Real.log a ∧
      vden r a b < vden r a (b - 1) := by
  set D := (1 + ε) * ((t : ℝ) * (t + 1) * (Nat.totient t)) with hD_def
  -- `D` is strictly above `t(t+1)φ(t)`.
  have htotpos : 0 < Nat.totient t := Nat.totient_pos.mpr (by linarith)
  have hpos0 : (0:ℝ) < (t : ℝ) * (t + 1) * (Nat.totient t) := by
    have h1 : (0:ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by linarith)
    have h2 : (0:ℝ) < (Nat.totient t : ℝ) := by exact_mod_cast htotpos
    have : (0:ℝ) < (t : ℝ) + 1 := by linarith
    positivity
  have hDgt : (t : ℝ) * (t + 1) * (Nat.totient t) < D := by
    rw [hD_def]; nlinarith [mul_pos hε hpos0]
  -- Upgrade the nonzero term to a positive index using periodicity.
  have hposIdx : ∃ i, 1 ≤ i ∧ r i ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i + t, by omega, by rw [hper]; exact hi⟩
  -- Obtain the construction sequence.
  obtain ⟨a, b, ha, hmem, hbound⟩ :
      ∃ a b : ℕ → ℕ, Tendsto a atTop atTop ∧
        (∀ᶠ k in atTop, b k ∈ Bset r (a k)) ∧
        (∀ᶠ k in atTop, ((b k : ℝ) - (a k : ℝ)) / Real.log (a k) < D) := by
    rcases Nat.lt_or_ge t 2 with h1 | h2
    · -- `t = 1`
      have ht1 : t = 1 := by omega
      subst ht1
      have hCI : CaseI r 1 := by
        obtain ⟨i, hi1, hine⟩ := hposIdx
        have hr1 : r 1 ≠ 0 := by
          have : r i = r 1 := rper_congr r 1 hper (Nat.modEq_one)
          rw [this] at hine; exact hine
        have hr2 : r 2 = r 1 := rper_congr r 1 hper (Nat.modEq_one)
        refine ⟨1, 2, le_refl 1, hr1, by rw [hr2]; exact hr1, by norm_num, by norm_num,
          by norm_num, ?_, ?_⟩
        · rw [hr2]; intro hcon
          apply hr1; linarith [hcon]
        · intro i hi hi'; omega
      exact caseI_construction r 1 (by norm_num) hper hCI D hDgt
    · -- `t ≥ 2`
      rcases case_split r t h2 hper hposIdx with hCI | hCII
      · exact caseI_construction r t ht hper hCI D hDgt
      · exact caseII_construction r t h2 hper hCII D hDgt
  exact frequently_drop_of_construction r D a b ha hmem hbound

#print axioms exists_nearby_drop
