import Mathlib

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Finset Nat Real Set

/-!
Following Erdős and Hall we say that positive integers interlock if between any
two divisors of one there is a divisor of the other, and vice versa. A positive
integer is said to be separable if there exists a positive integer with which it
interlocks.

P. Erdős and R. R. Hall. On some unconventional problems on the divisors of
integers. J. Aust. Math. Soc., Ser. A, 25:479–485, 1978.

Stijn Cambie and I showed that the density of k such that 2^k is separable, is
positive and strictly less than 1.

S. Cambie and W. van Doorn, Resolution of two conjectures by Erdős and Hall
concerning separable numbers, arXiv:2510.19727.

Below you can find a formalization of our results, which was obtained by
Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

To prove the positive density result, we require three results from the
literature. These can be found as axioms near the start of the file.

Finally, we show that there are only finitely many interlocking pairs m, n for
which mn is equal to a primorial.

Lean version: leanprover/lean4:v4.28.0
-/

/-- Two positive integers `m` and `n` **interlock** if between every two
divisors (both > 1) of `n` there is a divisor of `m`, and vice-versa. -/
def Interlock (m n : ℕ) : Prop :=
  (∀ a b, 1 < a → 1 < b → a ∣ n → b ∣ n → a < b →
    ∃ d, d ∣ m ∧ a < d ∧ d < b) ∧
  (∀ a b, 1 < a → 1 < b → a ∣ m → b ∣ m → a < b →
    ∃ d, d ∣ n ∧ a < d ∧ d < b)

/-- A positive integer `n` is **separable** if there exists a positive integer `m`
such that `m` and `n` interlock. -/
def Separable (n : ℕ) : Prop := ∃ m : ℕ, 0 < m ∧ Interlock m n

/-- For all x ≥ 396738 there exists a prime p such that x < p ≤ x(1 + 1/(25(log x)²)).

  P. Dusart. Estimates of Some Functions Over Primes without R.H. arXiv:1002.0442 -/
axiom prime_gap_dusart : ∀ x : ℕ, 396738 ≤ x →
  ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x) ^ 2))

/-- For all x ≥ exp(exp(33.217)) there is a prime p such that x < p < x + 3x^{2/3}.

  A. Dudek. An explicit result for primes between cubes. Funct. Approx. Comment. Math.,
  55(2):177–197, 2014. -/
axiom prime_gap_dudek : ∀ x : ℕ, (Real.exp (Real.exp 33.217) : ℝ) ≤ x →
  ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) < x + 3 * (x : ℝ) ^ (2/3 : ℝ)

/-- There exists an absolute constant c such that for all x, y, z with 2 ≤ y ≤ z
≤ x, there are at most cx·log(y)/log(z) positive integers n ≤ x which do not
have a divisor in [y, z].

  G. Tenenbaum. On the probability that an integer has a divisor in a given interval. Compos.
  Math., 51:243–263, 1984 -/
axiom tenenbaum_divisor_interval : ∃ c : ℝ, 0 < c ∧
  ∀ x y z : ℝ, 2 ≤ y → y ≤ z → z ≤ x →
  (Set.ncard {n : ℕ | (n : ℝ) ≤ x ∧ 0 < n ∧
    ∀ d : ℕ, d ∣ n → (d : ℝ) < y ∨ z < d} : ℝ) ≤ c * x * Real.log y / Real.log z

/-- The product of the first `k` primes (primorial). -/
noncomputable def Primorial : ℕ → ℕ
  | 0 => 1
  | k + 1 => (Nat.nth Nat.Prime k) * Primorial k

/-- A positive integer n has C-well-spread divisors if for every pair of
consecutive divisors d_{j-1} < d_j (with d_j > 1), we have
d_j ≤ exp(max(C, d_{j-1})). -/
def WellSpreadDivisors (C : ℝ) (n : ℕ) : Prop :=
  ∀ a b : ℕ, 1 ≤ a → a ∣ n → b ∣ n → a < b →
    (∀ c : ℕ, c ∣ n → a < c → c < b → False) →
    (b : ℝ) ≤ Real.exp (max C (a : ℝ))

/-- For n ≤ exp(C), n has C-well-spread divisors. -/
lemma wellSpreadDivisors_of_le_exp (C : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hle : (n : ℝ) ≤ Real.exp C) :
    WellSpreadDivisors C n := by
  intro a b ha hb hbn' hab h
  exact le_trans (Nat.cast_le.mpr (Nat.le_of_dvd hn hbn'))
    (le_trans hle (Real.exp_le_exp.mpr (le_max_left _ _)))

/-- The sequence √C, C, C², C⁴, C⁸, ... defined by iterated squaring.
  `expTower C 0 = √C` and `expTower C (n+1) = (expTower C n)²`. -/
noncomputable def expTower (C : ℝ) : ℕ → ℝ
  | 0 => Real.sqrt C
  | n + 1 => (expTower C n) ^ 2

@[simp] lemma expTower_zero (C : ℝ) : expTower C 0 = Real.sqrt C := rfl
@[simp] lemma expTower_succ (C : ℝ) (n : ℕ) : expTower C (n + 1) = (expTower C n) ^ 2 := rfl

/-
For C ≥ 0, expTower C n ≥ 0.
-/
lemma expTower_nonneg (C : ℝ) (n : ℕ) : 0 ≤ expTower C n := by
  exact Nat.recOn n ( Real.sqrt_nonneg _ ) fun n ih => sq_nonneg _

/-
For C > 0, expTower C n > 0.
-/
lemma expTower_pos (C : ℝ) (hC : 0 < C) (n : ℕ) : 0 < expTower C n := by
  induction n <;> [ exact Real.sqrt_pos.mpr hC; exact pow_pos ( by solve_by_elim ) 2 ]

/-
For C ≥ 100, expTower C n ≥ 10 for all n.
-/
lemma expTower_ge_ten (C : ℝ) (hC : C ≥ 100) (n : ℕ) : expTower C n ≥ 10 := by
  induction' n with n ih;
  · exact Real.le_sqrt_of_sq_le ( by linarith );
  · rw [ show expTower C ( n + 1 ) = ( expTower C n ) ^ 2 by rfl ] ; nlinarith

/-
Monotonicity: expTower C (n+1) ≥ expTower C n for C ≥ 100.
-/
lemma expTower_mono (C : ℝ) (hC : C ≥ 100) (n : ℕ) :
    expTower C n ≤ expTower C (n + 1) := by
  -- Expand the definition of `expTower` and substitute the base case for the inductive step.
  rw [expTower_succ];
  nlinarith [ show 1 ≤ expTower C n from Nat.recOn n ( Real.le_sqrt_of_sq_le <| by linarith ) fun n ihn => by rw [ expTower_succ ] ; nlinarith ]

/-
expTower C 1 = C for C ≥ 0
-/
lemma expTower_one (C : ℝ) (hC : 0 ≤ C) : expTower C 1 = C :=
  Real.sq_sqrt hC

/-
For x ≥ 10, we have 4·ln(x) ≤ x, equivalently x⁴ ≤ eˣ.
-/
lemma four_mul_log_le (x : ℝ) (hx : 10 ≤ x) : 4 * Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos ( by positivity : 0 < x / 10 );
  rw [ Real.log_div ] at this <;> try linarith;
  have := Real.log_two_lt_d9 ; norm_num1 at * ; rw [ show ( 10 : ℝ ) = ( 2:ℝ ) * ( 5:ℝ ) by norm_num, Real.log_mul ] at * <;> norm_num at *;
  rw [ show ( 5 : ℝ ) = ( 2 ^ 2 ) * ( 1.25 ) by norm_num, Real.log_mul, Real.log_pow ] at * <;> norm_num at *;
  linarith [ Real.log_le_sub_one_of_pos ( show 0 < 5 / 4 by norm_num ) ]

/-
If C ≥ 100, then (expTower C i)⁴ ≤ exp(expTower C i).
-/
lemma expTower_fourth_le_exp (C : ℝ) (hC : C ≥ 100) (i : ℕ) :
    (expTower C i) ^ 4 ≤ Real.exp (expTower C i) := by
  convert Real.exp_le_exp.mpr ( four_mul_log_le ( expTower C i ) ( expTower_ge_ten C hC i ) ) using 1 ; rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by linarith [ expTower_pos C ( by linarith ) i ] ) ] ; ring_nf

/-
If C ≥ 100, then Σ_{i=0}^{l} 1/expTower(C,i) < 10/(9√C).
-/
lemma sum_inv_expTower_bound (C : ℝ) (hC : C ≥ 100) (l : ℕ) :
    ∑ i ∈ Finset.range (l + 1), 1 / expTower C i ≤ 10 / (9 * Real.sqrt C) := by
  -- We bound the sum by a geometric series with first term $1/C$ and ratio $1/C$.
  have h_geo_series : (∑ i ∈ Finset.range l, (1 / (expTower C (i + 1) : ℝ))) ≤ (1 / C) / (1 - 1 / C) := by
    -- Each term in the sum from i=1 to l is less than or equal to (1/C) * (1/C)^i.
    have h_term_bound : ∀ i ∈ Finset.range l, (1 / (expTower C (i + 1) : ℝ)) ≤ (1 / C) * (1 / C) ^ i := by
      intro i hi;
      induction i <;> simp_all +decide [ pow_succ ];
      · rw [ ← mul_inv, Real.mul_self_sqrt ( by positivity ) ];
      · rename_i k hk;
        refine le_trans ( mul_le_mul_of_nonneg_right ( hk ( Nat.lt_of_succ_lt hi ) ) ( by exact mul_self_nonneg _ ) ) ?_;
        rw [ mul_assoc ];
        gcongr;
        refine' le_trans ( hk ( Nat.lt_of_succ_lt hi ) ) _;
        exact mul_le_of_le_one_right ( by positivity ) ( inv_le_one_of_one_le₀ ( one_le_pow₀ ( by linarith ) ) );
    refine' le_trans ( Finset.sum_le_sum h_term_bound ) _;
    rw [ ← Finset.mul_sum _ _ _, geom_sum_eq ] <;> ring_nf <;> norm_num [ show C ≠ 0 by linarith ];
    · rw [ show ( -1 + C⁻¹ ) = - ( 1 - C⁻¹ ) by ring, inv_neg ] ; ring_nf ; norm_num;
      exact mul_nonneg ( mul_nonneg ( inv_nonneg.2 ( by positivity ) ) ( inv_nonneg.2 ( by positivity ) ) ) ( inv_nonneg.2 ( sub_nonneg.2 ( inv_le_one_of_one_le₀ ( by linarith ) ) ) );
    · linarith;
  -- We bound the first term $1/√C$ by $10/(9√C)$.
  have h_first_term : (1 / Real.sqrt C) + (1 / C) / (1 - 1 / C) ≤ 10 / (9 * Real.sqrt C) := by
    field_simp;
    rw [ add_div', div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg C, Real.sq_sqrt ( show 0 ≤ C by linarith ) ];
  rw [ Finset.sum_range_succ' ];
  rw [ show expTower C 0 = Real.sqrt C from rfl ] ; linarith

/-
If C ≥ 5c² and c > 0, then 10c/(9√C) < 1/2.
-/
lemma density_bound (c : ℝ) (hc : 0 < c) (C : ℝ)
    (hC1 : C ≥ 100) (hC2 : C ≥ 5 * c ^ 2) :
    10 * c / (9 * Real.sqrt C) < 1 / 2 := by
  rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg C, Real.sq_sqrt ( show 0 ≤ C by linarith ) ]

/-
expTower C (i+2) = (expTower C i)^4.
-/
lemma expTower_succ_succ (C : ℝ) (i : ℕ) :
    expTower C (i + 2) = (expTower C i) ^ 4 := by
  rw [ show expTower C ( i + 2 ) = ( expTower C ( i + 1 ) ) ^ 2 by rfl, show expTower C ( i + 1 ) = ( expTower C i ) ^ 2 by rfl ] ; ring

/-
If C ≥ 100, then expTower C (i+2) ≤ exp(expTower C i).
-/
lemma expTower_succ_succ_le_exp (C : ℝ) (hC : C ≥ 100) (i : ℕ) :
    expTower C (i + 2) ≤ Real.exp (expTower C i) := by
  -- By expTower_succ_succ, expTower C (i+2) = (expTower C i)^4.
  have h_expTower_succ_succ : expTower C (i + 2) = (expTower C i) ^ 4 := by
    exact expTower_succ_succ C i;
  exact h_expTower_succ_succ ▸ expTower_fourth_le_exp C hC i

/-
The expTower sequence is unbounded.
-/
lemma expTower_tendsto_atTop (C : ℝ) (hC : C ≥ 100) :
    Filter.Tendsto (expTower C) Filter.atTop Filter.atTop := by
  -- By induction, we can show that expTower C n ≥ 10^(2^n) for all n.
  have h_inductive_bound : ∀ n : ℕ, expTower C n ≥ 10 ^ (2 ^ n) := by
    intro n;
    induction' n with n ih;
    · exact Real.le_sqrt_of_sq_le ( by norm_num; linarith );
    · rw [ pow_succ, pow_mul ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) ih 2 ) ( by rw [ expTower_succ ] ) ;
  exact Filter.tendsto_atTop_mono h_inductive_bound ( tendsto_pow_atTop_atTop_of_one_lt ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_pow_atTop_atTop_of_one_lt one_lt_two )

/-
For any M, there exists i such that exp(expTower C i) > M.
-/
lemma exists_expTower_exp_gt (C : ℝ) (hC : C ≥ 100) (M : ℝ) :
    ∃ i : ℕ, M < Real.exp (expTower C i) := by
  have := Real.tendsto_exp_atTop.comp ( expTower_tendsto_atTop C hC ) ; exact ( this.eventually_gt_atTop M ) |> fun h => h.exists;

/-
For any a ≥ 1, there exists i such that
  exp(expTower C i) ≤ a < exp(expTower C (i+1)).
-/
lemma exists_expTower_interval (C : ℝ) (hC : C ≥ 100) (a : ℝ) (ha : Real.exp (expTower C 0) ≤ a) :
    ∃ i : ℕ, Real.exp (expTower C i) ≤ a ∧ a < Real.exp (expTower C (i + 1)) := by
  -- By the properties of the exponential function and the unboundedness of the sequence expTower C i, there exists some j such that a < exp(expTower C j).
  obtain ⟨j, hj⟩ : ∃ j : ℕ, a < Real.exp (expTower C j) := by
    exact exists_expTower_exp_gt C hC a;
  contrapose! hj;
  exact Nat.recOn j ( by simpa using ha ) hj

/-
If n > 0, C ≥ 100, and n has a divisor in [exp(expTower C i), exp(expTower C (i+1))]
for every i such that exp(expTower C i) ≤ n, then n has C-well-spread divisors.
-/
lemma well_spread_of_divisors_in_intervals (C : ℝ) (hC : C ≥ 100) (n : ℕ) (hn : 0 < n) :
    (∀ i : ℕ, Real.exp (expTower C i) ≤ ↑n →
      ∃ d : ℕ, d ∣ n ∧ Real.exp (expTower C i) ≤ (d : ℝ) ∧
        (d : ℝ) ≤ Real.exp (expTower C (i + 1))) →
    WellSpreadDivisors C n := by
  -- First consider the case where $b \leq e^C$, which directly implies $b \leq e^{\max(C, a)}$.
  intro h_divisors a b ha hb hb_pos hab hconsecutive
  by_cases h_case1 : (b : ℝ) ≤ Real.exp C;
  · exact le_trans h_case1 ( Real.exp_le_exp.mpr ( le_max_left _ _ ) );
  · -- Since $b > \exp(C)$, there exists $i₀$ such that $\exp(\expTower C i₀) \leq a < \exp(\expTower C (i₀+1))$.
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ℕ, Real.exp (expTower C i₀) ≤ a ∧ a < Real.exp (expTower C (i₀ + 1)) := by
      apply exists_expTower_interval;
      · linarith;
      · -- Since $a$ is a divisor of $n$ and $n$ has a divisor in $[e^{\sqrt{C}}, e^C]$, we have $a \geq e^{\sqrt{C}}$.
        have h_a_ge_exp_sqrt_C : ∃ d : ℕ, d ∣ n ∧ Real.exp (Real.sqrt C) ≤ d ∧ d ≤ Real.exp C := by
          convert h_divisors 0 _;
          · exact Eq.symm ( expTower_one C ( by positivity ) );
          · exact le_trans ( Real.exp_le_exp.mpr ( show Real.sqrt C ≤ C by exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩ ) ) ( le_trans ( le_of_not_ge h_case1 ) ( Nat.cast_le.mpr ( Nat.le_of_dvd hn hb_pos ) ) );
        obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := h_a_ge_exp_sqrt_C;
        contrapose! hconsecutive;
        exact ⟨ d, hd₁, by exact_mod_cast hconsecutive.trans_le hd₂, by exact_mod_cast hd₃.trans_lt ( lt_of_not_ge h_case1 ), trivial ⟩;
    by_cases h_case2 : Real.exp (expTower C (i₀ + 1)) > n;
    · -- Since $b \leq n$ and $n < \exp(\expTower C (i₀ + 1))$, we have $b < \exp(\expTower C (i₀ + 1))$.
      have h_b_lt_exp : (b : ℝ) < Real.exp (expTower C (i₀ + 1)) := by
        exact lt_of_le_of_lt ( Nat.cast_le.mpr ( Nat.le_of_dvd hn hb_pos ) ) h_case2;
      -- Since $b < \exp(\expTower C (i₀ + 1))$ and $\expTower C (i₀ + 1) = (\expTower C i₀)^2$, we have $b < \exp((\expTower C i₀)^2)$.
      have h_b_lt_exp_sq : (b : ℝ) < Real.exp ((expTower C i₀) ^ 2) := by
        convert h_b_lt_exp using 1;
      -- Since $a \geq \exp(\expTower C i₀)$ and $\expTower C i₀ \geq 10$, we have $(\expTower C i₀)^2 \leq \exp(\expTower C i₀)$.
      have h_exp_sq_le_exp : (expTower C i₀) ^ 2 ≤ Real.exp (expTower C i₀) := by
        have h_exp_sq_le_exp : ∀ x : ℝ, 10 ≤ x → x ^ 2 ≤ Real.exp x := by
          intro x hx; rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ] ; norm_num;
          have := Real.log_le_sub_one_of_pos ( by positivity : 0 < x / 2 );
          rw [ Real.log_div ] at this <;> linarith [ Real.log_le_sub_one_of_pos zero_lt_two ];
        exact h_exp_sq_le_exp _ ( expTower_ge_ten _ hC _ );
      exact h_b_lt_exp_sq.le.trans ( Real.exp_le_exp.mpr <| h_exp_sq_le_exp.trans <| hi₀.1.trans <| le_max_right _ _ );
    · -- Since $exp(expTower C (i₀+1)) \leq n$, by the hypothesis $h_divisors$, there exists a divisor $d$ of $n$ in the interval $[exp(expTower C (i₀+1)), exp(expTower C (i₀+2))]$.
      obtain ⟨d, hd_div, hd_interval⟩ : ∃ d : ℕ, d ∣ n ∧ Real.exp (expTower C (i₀ + 1)) ≤ d ∧ d ≤ Real.exp (expTower C (i₀ + 2)) := by
        exact h_divisors _ ( le_of_not_gt h_case2 );
      -- Since $d \geq b$ and $d \leq \exp(\expTower C (i₀+2))$, we have $b \leq \exp(\expTower C (i₀+2))$.
      have hb_le_exp : (b : ℝ) ≤ Real.exp (expTower C (i₀ + 2)) := by
        exact le_trans ( mod_cast le_of_not_gt fun h => hconsecutive d hd_div ( by exact_mod_cast hi₀.2.trans_le hd_interval.1 ) h ) hd_interval.2;
      refine le_trans hb_le_exp <| Real.exp_le_exp.mpr ?_;
      refine' le_trans ( expTower_succ_succ_le_exp C hC i₀ ) _;
      exact le_trans hi₀.1 ( le_max_right _ _ )

/-- ncard of biUnion over a Finset is at most the sum of ncards. -/
lemma ncard_biUnion_le_sum {α : Type*} (s : Finset ℕ)
    (f : ℕ → Set α) (hf : ∀ i ∈ s, (f i).Finite) :
    (⋃ i ∈ s, f i).ncard ≤ ∑ i ∈ s, (f i).ncard := by
  induction' s using Finset.induction with i s hi ihide;
  · simp +decide;
  · have h_union : (f i ∪ ⋃ j ∈ s, f j).ncard ≤ (f i).ncard + (⋃ j ∈ s, f j).ncard := by
      exact Set.ncard_union_le _ _;
    simp_all +decide [ Finset.sum_insert hi ];
    lia

/-
If exp(expTower C i) ≤ n and n ≤ N < exp(expTower C (i+1)),
then n has a divisor (namely itself) in the interval [exp(expTower C i), exp(expTower C (i+1))].
-/
lemma gap_forces_upper_bound (C : ℝ) (n : ℕ) (i : ℕ)
    (hi_lower : Real.exp (expTower C i) ≤ (n : ℝ))
    (h_no_div : ∀ d : ℕ, d ∣ n → (d : ℝ) < Real.exp (expTower C i) ∨
        Real.exp (expTower C (i + 1)) < (d : ℝ)) :
    Real.exp (expTower C (i + 1)) < (n : ℝ) := by
  cases h_no_div n dvd_rfl <;> linarith

/-
For non-well-spread n ≤ N, there exists i with exp(expTower C (i+1)) ≤ N
such that n has no divisor in the i-th interval.
-/
lemma non_ws_subset_tenenbaum_range (C : ℝ) (hC : C ≥ 100) (N : ℕ) :
    {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ ¬WellSpreadDivisors C n} ⊆
    ⋃ (i : ℕ) (_ : Real.exp (expTower C (i + 1)) ≤ (N : ℝ)),
      {n : ℕ | (n : ℝ) ≤ N ∧ 0 < n ∧
        ∀ d : ℕ, d ∣ n → (d : ℝ) < Real.exp (expTower C i) ∨
          Real.exp (expTower C (i + 1)) < d} := by
  intro n hn
  obtain ⟨hn1, hn2, hn3⟩ := hn
  have h_exists_i : ∃ i : ℕ, Real.exp (expTower C i) ≤ (n : ℝ) ∧ ∀ d : ℕ, d ∣ n → (d : ℝ) < Real.exp (expTower C i) ∨ Real.exp (expTower C (i + 1)) < (d : ℝ) := by
    contrapose! hn3;
    apply well_spread_of_divisors_in_intervals C hC n hn1;
    assumption;
  -- By Let's choose such an $i$.
  obtain ⟨i, hi1, hi2⟩ := h_exists_i;
  have hi3 : Real.exp (expTower C (i + 1)) ≤ (n : ℝ) := by
    exact le_of_lt ( gap_forces_upper_bound C n i hi1 hi2 );
  exact Set.mem_iUnion₂.mpr ⟨ i, by exact_mod_cast hi3.trans ( Nat.cast_le.mpr hn2 ), by exact_mod_cast hn2, hn1, hi2 ⟩;

/-
If N > 0, then 2 * #{non-ws n ≤ N} < N.
-/
lemma non_well_spread_count_lt (c : ℝ) (hc : 0 < c) (C : ℝ)
    (hC1 : C ≥ 100) (hC2 : C ≥ 5 * c ^ 2)
    (h_ten : ∀ x y z : ℝ, 2 ≤ y → y ≤ z → z ≤ x →
      (Set.ncard {n : ℕ | (n : ℝ) ≤ x ∧ 0 < n ∧
        ∀ d : ℕ, d ∣ n → (d : ℝ) < y ∨ z < d} : ℝ) ≤ c * x * Real.log y / Real.log z)
    (N : ℕ) (hN : 0 < N) :
    2 * Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ ¬WellSpreadDivisors C n} < N := by
  by_cases hN_le_expC : (N : ℝ) ≤ Real.exp C;
  · rw [ show { n : ℕ | 1 ≤ n ∧ n ≤ N ∧ ¬WellSpreadDivisors C n } = ∅ from _ ] <;> norm_num;
    · grind;
    · exact Set.eq_empty_of_forall_notMem fun n hn => hn.2.2 <| wellSpreadDivisors_of_le_exp C n hn.1 <| le_trans ( Nat.cast_le.mpr hn.2.1 ) hN_le_expC;
  · -- Find l with exists_expTower_interval
    obtain ⟨l, hl⟩ : ∃ l : ℕ, Real.exp (expTower C l) ≤ (N : ℝ) ∧ (N : ℝ) < Real.exp (expTower C (l + 1)) := by
      apply exists_expTower_interval C hC1 ( N : ℝ ) ?_;
      exact le_trans ( Real.exp_le_exp.mpr ( show Real.sqrt C ≤ C by rw [ Real.sqrt_le_left ] <;> nlinarith ) ) ( le_of_not_ge hN_le_expC );
    -- By ncard_biUnion_le_sum: ncard ≤ Σ_{i < l} ncard(B_i).
    have h_ncard_le_sum : (Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ ¬WellSpreadDivisors C n}) ≤ ∑ i ∈ Finset.range l, (Set.ncard {n : ℕ | (n : ℝ) ≤ N ∧ 0 < n ∧ ∀ d : ℕ, d ∣ n → (d : ℝ) < Real.exp (expTower C i) ∨ Real.exp (expTower C (i + 1)) < d}) := by
      have h_subset : {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ ¬WellSpreadDivisors C n} ⊆ ⋃ i ∈ Finset.range l, {n : ℕ | (n : ℝ) ≤ N ∧ 0 < n ∧ ∀ d : ℕ, d ∣ n → (d : ℝ) < Real.exp (expTower C i) ∨ Real.exp (expTower C (i + 1)) < d} := by
        intro n hn;
        have := non_ws_subset_tenenbaum_range C hC1 N hn;
        simp +zetaDelta at *;
        obtain ⟨ x, hx₁, hx₂ ⟩ := this.2.2;
        refine' ⟨ this.1, this.2.1, x, _, hx₂ ⟩;
        contrapose! hx₁;
        refine' lt_of_lt_of_le hl.2 _;
        gcongr;
        · exact expTower_nonneg C _;
        · exact monotone_nat_of_le_succ ( fun n => expTower_mono C hC1 n ) hx₁;
      have h_ncard_le_sum : (Set.ncard (⋃ i ∈ Finset.range l, {n : ℕ | (n : ℝ) ≤ N ∧ 0 < n ∧ ∀ d : ℕ, d ∣ n → (d : ℝ) < Real.exp (expTower C i) ∨ Real.exp (expTower C (i + 1)) < d})) ≤ ∑ i ∈ Finset.range l, (Set.ncard {n : ℕ | (n : ℝ) ≤ N ∧ 0 < n ∧ ∀ d : ℕ, d ∣ n → (d : ℝ) < Real.exp (expTower C i) ∨ Real.exp (expTower C (i + 1)) < d}) := by
        convert ncard_biUnion_le_sum ( Finset.range l ) _ _ using 1;
        exact fun i hi => Set.finite_iff_bddAbove.mpr ⟨ N, fun n hn => mod_cast hn.1 ⟩;
      refine le_trans ?_ h_ncard_le_sum;
      apply_rules [ Set.ncard_le_ncard ];
      exact Set.finite_iff_bddAbove.mpr ⟨ N, fun n hn => by rcases Set.mem_iUnion₂.mp hn with ⟨ i, hi, hn ⟩ ; exact_mod_cast hn.1 ⟩;
    -- By tenenbaum_interval_bound (each B_i has exp(expTower C (i+1)) ≤ N): (ncard(B_i) : ℝ) ≤ c * N / expTower C i.
    have h_ncard_bound : ∀ i ∈ Finset.range l, (Set.ncard {n : ℕ | (n : ℝ) ≤ N ∧ 0 < n ∧ ∀ d : ℕ, d ∣ n → (d : ℝ) < Real.exp (expTower C i) ∨ Real.exp (expTower C (i + 1)) < d}) ≤ c * N / expTower C i := by
      intros i hi
      specialize h_ten (N : ℝ) (Real.exp (expTower C i)) (Real.exp (expTower C (i + 1))) (by
      exact le_trans ( by norm_num ) ( Real.add_one_le_exp _ ) |> le_trans <| Real.exp_le_exp.mpr <| show expTower C i ≥ 1 from Nat.recOn i ( Real.le_sqrt_of_sq_le <| by linarith ) fun n ihn => by rw [ expTower_succ ] ; nlinarith;) (by
      exact Real.exp_le_exp.mpr ( expTower_mono C hC1 i )) (by
      refine' le_trans _ hl.1;
      gcongr;
      exact monotone_nat_of_le_succ ( fun n => expTower_mono C hC1 n ) ( by linarith [ Finset.mem_range.mp hi ] ));
      simp_all +decide [ expTower_succ ];
      exact h_ten.trans_eq ( by rw [ div_eq_div_iff ] <;> nlinarith [ show 0 < expTower C i from expTower_pos C ( by positivity ) i ] );
    -- By sum_inv_expTower_bound: Σ_{i < l} (1/expTower C i) ≤ 10/(9√C).
    have h_sum_bound : ∑ i ∈ Finset.range l, (1 / expTower C i : ℝ) ≤ 10 / (9 * Real.sqrt C) := by
      exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.le_succ _ ) ) fun _ _ _ => one_div_nonneg.mpr ( expTower_nonneg _ _ ) ) ( sum_inv_expTower_bound _ hC1 _ );
    -- By combining the results from h_ncard_le_sum, h_ncard_bound, and h_sum_bound, we get the desired inequality.
    have h_final_bound : (Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ ¬WellSpreadDivisors C n}) ≤ c * N * (10 / (9 * Real.sqrt C)) := by
      refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_sum_bound <| by positivity );
      convert le_trans ( Nat.cast_le.mpr h_ncard_le_sum ) _ using 1;
      · infer_instance;
      · infer_instance;
      · infer_instance;
      · simpa [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum h_ncard_bound;
    -- By density_bound: c * N * (10 / (9 * Real.sqrt C)) < N / 2.
    have h_density_bound : c * N * (10 / (9 * Real.sqrt C)) < N / 2 := by
      have := density_bound c hc C hC1 hC2;
      convert mul_lt_mul_of_pos_left this ( Nat.cast_pos.mpr hN ) using 1 <;> ring;
    exact_mod_cast ( by linarith : ( 2 : ℝ ) * Set.ncard { n : ℕ | 1 ≤ n ∧ n ≤ N ∧ ¬WellSpreadDivisors C n } < N )

lemma Interlock.mk' {m n : ℕ}
    (h1 : ∀ a b, 1 < a → 1 < b → a ∣ n → b ∣ n → a < b →
      ∃ d, d ∣ m ∧ a < d ∧ d < b)
    (h2 : ∀ a b, 1 < a → 1 < b → a ∣ m → b ∣ m → a < b →
      ∃ d, d ∣ n ∧ a < d ∧ d < b) :
    Interlock m n := ⟨h1, h2⟩

lemma Interlock.fst {m n : ℕ} (h : Interlock m n) :
    ∀ a b, 1 < a → 1 < b → a ∣ n → b ∣ n → a < b →
      ∃ d, d ∣ m ∧ a < d ∧ d < b := h.1

lemma Interlock.snd {m n : ℕ} (h : Interlock m n) :
    ∀ a b, 1 < a → 1 < b → a ∣ m → b ∣ m → a < b →
      ∃ d, d ∣ n ∧ a < d ∧ d < b := h.2

/-- If m is odd with k divisors, m < 2^k, and Nat.log 2 is injective
on divisors > 1 of m, then m interlocks with 2^k. -/
lemma interlock_of_odd_inj_log (k : ℕ) (hk : 2 ≤ k)
    (m : ℕ) (hm : 0 < m) (h_odd : ¬ 2 ∣ m)
    (h_tau : (Nat.divisors m).card = k)
    (h_lt : m < 2 ^ k)
    (h_inj : ∀ d₁ d₂ : ℕ, d₁ ∣ m → d₂ ∣ m → 1 < d₁ → 1 < d₂ →
      Nat.log 2 d₁ = Nat.log 2 d₂ → d₁ = d₂) :
    Interlock m (2 ^ k) := by
  have h_divisors : ∀ i : ℕ, 1 ≤ i → i < k → ∃ d, d ∣ m ∧ 2 ^ i < d ∧ d < 2 ^ (i + 1) := by
    have h_divisors_gt1 : (Finset.filter (fun d => 1 < d) m.divisors).card = k - 1 := by
      rw [ ← h_tau, show { d ∈ m.divisors | 1 < d } = m.divisors \ { 1 } from ?_, Finset.card_sdiff ] <;> norm_num [ hm.ne' ];
      ext ( _ | _ | d ) <;> simp +arith +decide;
    have h_divisors_gt1_log : Finset.image (fun d => Nat.log 2 d) (Finset.filter (fun d => 1 < d) m.divisors) = Finset.Ico 1 k := by
      refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _
      · simp +zetaDelta at *
        exact fun x hx₁ hx₂ hx₃ => ⟨ Nat.le_log_of_pow_le ( by decide ) ( by linarith ), Nat.log_lt_of_lt_pow ( by linarith ) ( by linarith [ Nat.le_of_dvd hm hx₁ ] ) ⟩
      · rw [ Finset.card_image_of_injOn fun x hx y hy hxy => h_inj x y ( Nat.dvd_of_mem_divisors ( Finset.filter_subset _ _ hx ) ) ( Nat.dvd_of_mem_divisors ( Finset.filter_subset _ _ hy ) ) ( Finset.mem_filter.mp hx |>.2 ) ( Finset.mem_filter.mp hy |>.2 ) hxy ] ; aesop
    intro i hi₁ hi₂; replace h_divisors_gt1_log := Finset.ext_iff.mp h_divisors_gt1_log i; simp_all +decide ;
    obtain ⟨ d, hd₁, hd₂ ⟩ := h_divisors_gt1_log; use d; simp_all +decide ;
    exact ⟨ lt_of_le_of_ne ( Nat.pow_le_of_le_log ( by linarith ) ( by linarith ) ) fun h => by have := Nat.dvd_trans ( h.symm ▸ dvd_pow_self _ ( by linarith ) ) hd₁.1.1; rw [ Nat.dvd_iff_mod_eq_zero ] at this; simp_all +decide, Nat.lt_pow_of_log_lt ( by linarith ) ( by linarith ) ⟩
  apply Interlock.mk'
  · intro a b ha hb ha' hb' hab
    rw [ Nat.dvd_prime_pow ( by decide ) ] at ha' hb'
    rcases ha' with ⟨ i, hi, rfl ⟩ ; rcases hb' with ⟨ j, hj, rfl ⟩
    have hij : i < j := by
      rwa [ pow_lt_pow_iff_right₀ ( by decide : 1 < 2 ) ] at hab
    have hi1 : 1 ≤ i := by
      rcases i with ( _ | i ) <;> simp_all +decide
    obtain ⟨d, hd₁, hd₂, hd₃⟩ := h_divisors i hi1 (by omega)
    exact ⟨d, hd₁, hd₂, lt_of_lt_of_le hd₃ (pow_le_pow_right₀ (show 1 ≤ (2:ℕ) by decide) (by omega : i + 1 ≤ j))⟩
  · intro a b ha hb ha_div hb_div hab
    have h_log : Nat.log 2 a < Nat.log 2 b := by
      rcases eq_or_lt_of_le ( Nat.log_mono_right hab.le ) with h | h
      · exact absurd ( h_inj a b ha_div hb_div ha hb h ) ( by linarith )
      · exact h
    have h_exp : 2 ^ (Nat.log 2 a + 1) ≤ b :=
      Nat.pow_le_of_le_log ( by linarith ) ( by linarith )
    refine' ⟨ 2 ^ ( Nat.log 2 a + 1 ), pow_dvd_pow _ ( show Nat.log 2 a + 1 ≤ k from _ ), _, _ ⟩
    · contrapose! h_lt
      exact le_trans ( pow_le_pow_right₀ ( by decide ) ( by linarith ) ) ( Nat.pow_log_le_self 2 ( by linarith ) |> le_trans <| Nat.le_of_dvd hm ha_div )
    · exact Nat.lt_pow_succ_log_self ( by decide ) _
    · refine' lt_of_le_of_ne h_exp _
      intro H
      exact h_odd ( dvd_trans ( H.symm ▸ dvd_pow_self _ ( Nat.succ_ne_zero _ ) ) hb_div )

/-
(257/256)^1 < exp(1/4^4) = exp(1/256).
-/
lemma ratio_bound_257 : (257 : ℝ) / 256 < Real.exp (1 / 256) := by
  linarith [ Real.add_one_lt_exp ( by norm_num : ( 1 : ℝ ) / 256 ≠ 0 ) ]

/-
(65537/65536)^1 < exp(1/4^5) = exp(1/1024).
-/
lemma ratio_bound_65537 : (65537 : ℝ) / 65536 < Real.exp (1 / 1024) := by
  exact lt_of_le_of_lt ( by norm_num ) ( Real.add_one_lt_exp ( by norm_num ) )

/-
For x ≥ 2^32 (so x ≥ 396738), using Dusart's bound,
if p is the smallest prime > x, then p/x < 1 + 1/4^i
when x = 2^{2^{i-1}} and i ≥ 6. More precisely, for b ≥ 32,
1/(25·(b·ln 2)²) ≤ 1/4^i when 2^i ≤ 2b (i.e., i ≤ log₂(2b)).
-/
lemma dusart_ratio_bound (x : ℕ) (hx : 396738 ≤ x) (i : ℕ) (hi : 6 ≤ i)
    (hx_bound : (x : ℝ) ≥ 2 ^ (2 ^ (i - 1) : ℕ))
    (_h_dusart : ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x) ^ 2)))
    (p : ℕ) (_hp : p.Prime) (_hpx : x < p) (hpu : (p : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x) ^ 2))) :
    ((p : ℝ) / x) < Real.exp ((1 : ℝ) / 4 ^ i) := by
  -- Since $x \geq 2^{2^{i-1}}$, we have $\log x \geq 2^{i-1} \log 2$.
  have h_log_bound : Real.log x ≥ 2 ^ (i - 1) * Real.log 2 := by
    simpa using Real.log_le_log ( by positivity ) hx_bound;
  -- Therefore, $1 / (25 * (log x)^2) \leq 1 / (25 * (2^{i-1} * log 2)^2) = 1 / (25 * 4^{i-1} * (log 2)^2) = 1 / (100 * 4^{i-2} * (log 2)^2)$.
  have h_inv_log_bound : 1 / (25 * (Real.log x)^2) ≤ 1 / (100 * 4^(i-2) * (Real.log 2)^2) := by
    nontriviality;
    refine' one_div_le_one_div_of_le _ _;
    · positivity;
    · rcases i with ( _ | _ | i ) <;> simp_all +decide [ pow_succ' ];
      convert mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) h_log_bound 2 ) ( show ( 0 : ℝ ) ≤ 25 by positivity ) using 1 ; ring_nf;
      norm_num [ pow_mul' ];
  -- Since $1 / (100 * 4^{i-2} * (log 2)^2) \leq 1 / 4^i$, we have $1 / (25 * (log x)^2) \leq 1 / 4^i$.
  have h_inv_log_bound_final : 1 / (25 * (Real.log x)^2) ≤ 1 / 4^i := by
    refine le_trans h_inv_log_bound ?_;
    rcases i with ( _ | _ | i ) <;> norm_num [ pow_succ' ] at *;
    field_simp;
    exact le_trans ( by ring_nf; norm_num ) ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( show Real.log 2 ≥ 1 / 2 by exact Real.log_two_gt_d9.le.trans' <| by norm_num ) 2 ) <| by positivity ) <| by positivity );
  rw [ div_lt_iff₀ ( by positivity ) ];
  nlinarith [ show ( x : ℝ ) ≥ 396738 by exact_mod_cast hx, Real.add_one_lt_exp ( show ( 1 : ℝ ) / 4 ^ i ≠ 0 by positivity ), show ( 1 : ℝ ) / 4 ^ i > 0 by positivity, mul_div_cancel₀ ( 1 : ℝ ) ( show ( 4 ^ i : ℝ ) ≠ 0 by positivity ) ]

/-
For the Dudek case: if n ≥ exp(exp(33.217)), p is prime with
n < p < n + 3n^{2/3}, and e ≤ n^{1/4}, then (p/n)^e < exp(3·n^{-1/12}).
-/
lemma dudek_ratio_bound (n : ℕ) (p : ℕ) (e : ℕ)
    (hn : (n : ℝ) ≥ 2)
    (hp_upper : (p : ℝ) < n + 3 * (n : ℝ) ^ (2/3 : ℝ))
    (hpn : (n : ℕ) < p)
    (he : (e : ℝ) ≤ (n : ℝ) ^ (1/4 : ℝ)) :
    ((p : ℝ) / n) ^ e < Real.exp (3 * (n : ℝ) ^ (-(1:ℝ)/12)) := by
  -- Applying the inequality $(1 + x)^e \leq \exp(ex)$ to $(p/n)^e$.
  have h_exp : ((p : ℝ) / n) ^ e ≤ Real.exp (e * ((p : ℝ) / n - 1)) := by
    rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by exact div_pos ( Nat.cast_pos.mpr ( pos_of_gt hpn ) ) ( Nat.cast_pos.mpr ( pos_of_gt ( show 0 < n from Nat.cast_pos.mp ( lt_of_lt_of_le ( by norm_num ) hn ) ) ) ) ) ] ; norm_num;
    rw [ mul_comm ] ; gcongr;
    exact Real.log_le_sub_one_of_pos ( div_pos ( Nat.cast_pos.mpr ( pos_of_gt hpn ) ) ( Nat.cast_pos.mpr ( pos_of_gt ( show 0 < n from Nat.cast_pos.mp ( lt_of_lt_of_le ( by norm_num ) hn ) ) ) ) );
  -- Since $e \leq n^{1/4}$, we have $e * (p / n - 1) \leq n^{1/4} * (p / n - 1)$.
  have h_mul : (e : ℝ) * ((p : ℝ) / n - 1) ≤ (n : ℝ) ^ (1 / 4 : ℝ) * ((p : ℝ) / n - 1) := by
    exact mul_le_mul_of_nonneg_right he ( sub_nonneg_of_le <| by rw [ le_div_iff₀ <| by positivity ] ; norm_cast ; linarith );
  -- Since $p < n + 3n^{2/3}$, we have $p/n - 1 < 3n^{-1/3}$.
  have h_diff : (p : ℝ) / n - 1 < 3 * (n : ℝ) ^ (-1 / 3 : ℝ) := by
    rw [ sub_lt_iff_lt_add', div_lt_iff₀ ] <;> try linarith;
    convert hp_upper using 1 ; ring_nf;
    rw [ ← Real.rpow_add_one ] <;> ring_nf ; linarith;
  refine lt_of_le_of_lt h_exp <| Real.exp_lt_exp.mpr <| lt_of_le_of_lt h_mul ?_;
  convert mul_lt_mul_of_pos_left h_diff ( Real.rpow_pos_of_pos ( by positivity : 0 < ( n : ℝ ) ) ( 1 / 4 : ℝ ) ) using 1 ; ring_nf;
  rw [ ← Real.rpow_add ( by positivity ) ] ; norm_num

structure GoodInterlocker (m c : ℕ) (R : ℝ) : Prop where
  m_pos : 0 < m
  m_odd : ¬ 2 ∣ m
  tau_eq : m.divisors.card = c
  c_ge : c ≥ 2
  log_inj : ∀ d₁ d₂ : ℕ, d₁ ∣ m → d₂ ∣ m → 1 < d₁ → 1 < d₂ →
    Nat.log 2 d₁ = Nat.log 2 d₂ → d₁ = d₂
  log_lt : ∀ d : ℕ, d ∣ m → 1 < d → Nat.log 2 d < c
  div_upper : ∀ d : ℕ, d ∣ m → 0 < d →
    (d : ℝ) < (10 / 11 : ℝ) * R * (2 : ℝ) ^ (Nat.log 2 d + 1)
  R_pos : (0 : ℝ) < R

lemma good_m_lt_pow (m c : ℕ) (R : ℝ) (hg : GoodInterlocker m c R) : m < 2 ^ c := by
  cases' hg with m_pos m_odd tau_eq c_ge log_inj log_lt div_upper R_pos;
  by_cases hm : 1 < m;
  · exact Nat.lt_pow_of_log_lt ( by linarith ) ( by linarith [ log_lt m ( dvd_refl m ) hm ] );
  · interval_cases m ; norm_num at * ; linarith [ Nat.pow_le_pow_right two_pos c_ge ]

lemma good_to_separable (m k : ℕ) (R : ℝ) (hg : GoodInterlocker m k R) : Separable (2 ^ k) := by
  refine ⟨m, hg.m_pos, ?_⟩
  exact interlock_of_odd_inj_log k hg.c_ge m hg.m_pos hg.m_odd hg.tau_eq
    (good_m_lt_pow m k R hg) hg.log_inj

lemma base_good_231 : GoodInterlocker 231 8 1 := by
  constructor <;> norm_num;
  · decide;
  · intro d₁ d₂ h₁ h₂ h₃ h₄ h₅; have := Nat.le_of_dvd ( by decide ) h₁; have := Nat.le_of_dvd ( by decide ) h₂; interval_cases d₁ <;> norm_num at h₁ <;> interval_cases d₂ <;> simp_all +decide;
  · exact fun d h1 h2 => Nat.log_lt_of_lt_pow ( by linarith ) ( by linarith [ Nat.le_of_dvd ( by linarith ) h1 ] );
  · intro d hd hd'; have := Nat.le_of_dvd ( by decide ) hd; interval_cases d <;> norm_num at *;

lemma prime_gt_not_dvd (m c : ℕ) (p : ℕ) (hm : 0 < m) (hm_lt : m < 2 ^ c)
    (hp : 2 ^ c < p) (_hp_prime : Nat.Prime p) : ¬ p ∣ m := by
  exact Nat.not_dvd_of_pos_of_lt hm ( lt_trans hm_lt hp )

lemma log_mul_prime_pow (d p a c : ℕ) (R : ℝ)
    (hd_pos : 0 < d) (hp_gt : 2 ^ c < p) (hd_log_lt : Nat.log 2 d < c)
    (hd_upper : (d : ℝ) < (10 / 11 : ℝ) * R * (2 : ℝ) ^ (Nat.log 2 d + 1))
    (hR_bound : (10 / 11 : ℝ) * R * ((p : ℝ) / (2 : ℝ) ^ c) ^ a < 1)
    (_hc_pos : 0 < c) :
    Nat.log 2 (d * p ^ a) = Nat.log 2 d + a * c := by
  have h_bounds : 2 ^ (Nat.log 2 d + a * c) ≤ d * p ^ a ∧ d * p ^ a < 2 ^ (Nat.log 2 d + a * c + 1) := by
    constructor;
    · rw [ pow_add, pow_mul' ];
      exact Nat.mul_le_mul ( Nat.pow_log_le_self 2 hd_pos.ne' ) ( Nat.pow_le_pow_left hp_gt.le _ );
    · have h_upper_bound : (d : ℝ) * p ^ a < (10 / 11 : ℝ) * R * (p / 2 ^ c) ^ a * 2 ^ (Nat.log 2 d + a * c + 1) := by
        convert mul_lt_mul_of_pos_right hd_upper ( show ( 0 :ℝ ) < p ^ a by exact pow_pos ( Nat.cast_pos.mpr <| pos_of_gt hp_gt ) _ ) using 1 ; ring_nf;
        simp +zetaDelta at *;
      exact_mod_cast h_upper_bound.trans_le ( mul_le_of_le_one_left ( by positivity ) hR_bound.le );
  rw [ Nat.log_eq_iff ] <;> aesop

lemma dvd_coprime_decomp (m p e : ℕ) (hp_prime : Nat.Prime p)
    (d : ℕ) (hd : d ∣ m * p ^ e) :
    ∃ d₁ a, d₁ ∣ m ∧ a ≤ e ∧ d = d₁ * p ^ a := by
  rw [ Nat.dvd_mul ] at hd;
  rcases hd with ⟨ k₁, k₂, hk₁, hk₂, rfl ⟩ ; rw [ Nat.dvd_prime_pow hp_prime ] at hk₂; aesop;

lemma R'_bound_for_extend (R : ℝ) (p c : ℕ) (e a : ℕ) (ha : a ≤ e)
    (hR_pos : 0 < R) (hp_gt : 2 ^ c < p)
    (hR' : R * ((p : ℝ) / (2 : ℝ) ^ c) ^ e < 11 / 10) :
    (10 / 11 : ℝ) * R * ((p : ℝ) / (2 : ℝ) ^ c) ^ a < 1 := by
  nlinarith [ show ( p / 2 ^ c : ℝ ) ^ a ≤ ( p / 2 ^ c : ℝ ) ^ e by exact pow_le_pow_right₀ ( by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast; linarith ) ha ]

lemma tau_coprime_mul (m p e c : ℕ) (hp_prime : Nat.Prime p)
    (h_not_dvd : ¬ p ∣ m) (h_tau : m.divisors.card = c)
    (_he_pos : 0 < e) :
    (m * p ^ e).divisors.card = c * (e + 1) := by
  have h_coprime : Nat.Coprime m (p ^ e) := by
    exact Nat.Coprime.pow_right _ ( Nat.Coprime.symm <| hp_prime.coprime_iff_not_dvd.mpr h_not_dvd );
  have h_tau_mul := Nat.Coprime.card_divisors_mul h_coprime
  rw [ h_tau_mul, h_tau, Nat.divisors_prime_pow hp_prime, Finset.card_map, Finset.card_range ]

/-
Oddness of m * p^e when m is odd and p is an odd prime
-/
lemma odd_mul_prime_pow (m p e : ℕ) (hm_odd : ¬ 2 ∣ m) (hp_prime : Nat.Prime p)
    (hp_odd : p ≠ 2) : ¬ 2 ∣ m * p ^ e := by
  simp_all +decide [ ← even_iff_two_dvd, parity_simps ];
  exact fun h => absurd ( hp_prime.even_iff.mp h ) hp_odd

/-
Log injectivity for extend
-/
lemma log_inj_extend (m c : ℕ) (R : ℝ) (e p : ℕ)
    (hg : GoodInterlocker m c R) (hp_gt : 2 ^ c < p)
    (hR' : R * ((p : ℝ) / (2 : ℝ) ^ c) ^ e < 11 / 10)
    (h_not_dvd : ¬ p ∣ m)
    (d₁' d₂' a₁ a₂ : ℕ) (hd₁' : d₁' ∣ m) (hd₂' : d₂' ∣ m)
    (ha₁ : a₁ ≤ e) (ha₂ : a₂ ≤ e)
    (hgt₁ : 1 < d₁' * p ^ a₁) (hgt₂ : 1 < d₂' * p ^ a₂)
    (hlog : Nat.log 2 (d₁' * p ^ a₁) = Nat.log 2 (d₂' * p ^ a₂)) :
    d₁' * p ^ a₁ = d₂' * p ^ a₂ := by
  -- Since $m$ is odd, we have $d₁' > 1$ and $d₂' > 1$, and thus $Nat.log 2 d₁' < c$ and $Nat.log 2 d₂' < c$.
  have hlog_lt_c : Nat.log 2 d₁' < c ∧ Nat.log 2 d₂' < c := by
    have hlog_lt_c : ∀ d : ℕ, d ∣ m → 1 < d → Nat.log 2 d < c := by
      exact fun d hd hd' => hg.log_lt d hd hd';
    refine ⟨ if h : 1 < d₁' then hlog_lt_c d₁' hd₁' h else ?_, if h : 1 < d₂' then hlog_lt_c d₂' hd₂' h else ?_ ⟩ <;> simp_all +decide ;
    · interval_cases d₁' <;> norm_num at *;
      exact Nat.pos_of_ne_zero ( by rintro rfl; linarith [ hg.c_ge ] );
    · interval_cases d₂' <;> norm_num at *;
      exact Nat.pos_of_ne_zero ( by rintro rfl; exact absurd ( hg.c_ge ) ( by norm_num ) );
  have hlog_eq : Nat.log 2 d₁' + a₁ * c = Nat.log 2 d₂' + a₂ * c := by
    have hlog_eq : Nat.log 2 (d₁' * p ^ a₁) = Nat.log 2 d₁' + a₁ * c ∧ Nat.log 2 (d₂' * p ^ a₂) = Nat.log 2 d₂' + a₂ * c := by
      apply And.intro;
      · apply log_mul_prime_pow;
        grind +qlia;
        exact hp_gt;
        exact hlog_lt_c.1;
        exact hg.div_upper d₁' hd₁' ( Nat.pos_of_dvd_of_pos hd₁' ( Nat.pos_of_ne_zero ( by rintro rfl; simp_all +decide ) ) );
        · have := R'_bound_for_extend R p c e a₁ ha₁ ( by linarith [ hg.m_pos, show 0 < R from by linarith [ hg.R_pos ] ] ) ( by linarith ) hR';
          exact this;
        · linarith;
      · apply log_mul_prime_pow;
        grind +qlia;
        exact hp_gt;
        exact hlog_lt_c.2;
        exact hg.div_upper _ hd₂' ( Nat.pos_of_dvd_of_pos hd₂' ( Nat.pos_of_ne_zero ( by rintro rfl; simp_all +decide ) ) );
        · have hR_bound : (10 / 11 : ℝ) * R * ((p : ℝ) / (2 : ℝ) ^ c) ^ a₂ < 1 := by
            have := R'_bound_for_extend R p c e a₂ ha₂ (by
            exact hg.R_pos) hp_gt hR'
            exact this;
          exact hR_bound;
        · linarith;
    linarith;
  -- Since $a₁ = a₂$, we have $Nat.log 2 d₁' = Nat.log 2 d₂'$.
  have hlog_eq' : Nat.log 2 d₁' = Nat.log 2 d₂' := by
    nlinarith [ show a₁ = a₂ by nlinarith ];
  have := hg.log_inj d₁' d₂' hd₁' hd₂';
  rcases d₁' with ( _ | _ | d₁' ) <;> rcases d₂' with ( _ | _ | d₂' ) <;> simp_all +decide;
  · grind;
  · grind +suggestions;
  · linarith;
  · cases hlog_eq <;> simp_all +decide

/-
Log bound for extend
-/
lemma log_lt_extend (m c : ℕ) (R : ℝ) (e p : ℕ)
    (hg : GoodInterlocker m c R) (hp_gt : 2 ^ c < p)
    (hR' : R * ((p : ℝ) / (2 : ℝ) ^ c) ^ e < 11 / 10)
    (h_not_dvd : ¬ p ∣ m)
    (d₁ a : ℕ) (hd₁ : d₁ ∣ m) (ha : a ≤ e) :
    Nat.log 2 (d₁ * p ^ a) < c * (e + 1) := by
  -- Use log_mul_prime_pow: Nat.log 2 (d₁ * p^a) = Nat.log 2 d₁ + a * c.
  have h_log_mul : Nat.log 2 (d₁ * p ^ a) = Nat.log 2 d₁ + a * c := by
    apply log_mul_prime_pow;
    any_goals assumption;
    · exact Nat.pos_of_dvd_of_pos hd₁ ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd ( hg.m_pos ) ( by norm_num ) ) );
    · by_cases hd₁_one : d₁ = 1;
      · rcases c with ( _ | _ | c ) <;> simp_all +decide;
        exact absurd hg.c_ge ( by norm_num );
      · exact hg.log_lt d₁ hd₁ ( lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos hd₁ ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ( Ne.symm hd₁_one ) );
    · convert hg.div_upper d₁ hd₁ ( Nat.pos_of_dvd_of_pos hd₁ hg.m_pos ) using 1;
    · have hR_bound : (10 / 11 : ℝ) * R * ((p : ℝ) / (2 : ℝ) ^ c) ^ a < 1 := by
        have := hg.R_pos
        exact R'_bound_for_extend R p c e a ha this ( mod_cast hp_gt ) hR';
      exact hR_bound;
    · exact Nat.pos_of_ne_zero ( by rintro rfl; exact absurd ( hg.c_ge ) ( by norm_num ) );
  by_cases hd₁_one : d₁ = 1 <;> simp_all +decide [ mul_add ];
  · nlinarith [ hg.c_ge ];
  · nlinarith [ hg.log_lt d₁ hd₁ ( lt_of_le_of_ne ( Nat.succ_le_of_lt ( Nat.pos_of_dvd_of_pos hd₁ ( hg.m_pos ) ) ) ( Ne.symm hd₁_one ) ) ]

/-
Upper bound for extend
-/
lemma div_upper_extend (m c : ℕ) (R : ℝ) (e p : ℕ)
    (hg : GoodInterlocker m c R)
    (hp_prime : Nat.Prime p) (hp_gt : 2 ^ c < p)
    (hR' : R * ((p : ℝ) / (2 : ℝ) ^ c) ^ e < 11 / 10)
    (d₁ a : ℕ) (hd₁ : d₁ ∣ m) (ha : a ≤ e)
    (hpos : 0 < d₁ * p ^ a) :
    (d₁ * p ^ a : ℝ) < (10 / 11 : ℝ) * (R * ((p : ℝ) / (2 : ℝ) ^ c) ^ e) *
      (2 : ℝ) ^ (Nat.log 2 (d₁ * p ^ a) + 1) := by
  have h_log : (d₁ : ℝ) < (10 / 11) * R * 2 ^ (Nat.log 2 d₁ + 1) := by
    convert hg.div_upper d₁ hd₁ ( Nat.pos_of_dvd_of_pos hd₁ hg.m_pos ) using 1;
  have h_log_mul : (d₁ * p ^ a : ℝ) < (10 / 11) * R * (p / 2 ^ c) ^ a * 2 ^ (Nat.log 2 d₁ + a * c + 1) := by
    convert mul_lt_mul_of_pos_right h_log ( pow_pos ( show ( 0 : ℝ ) < p by norm_cast; linarith [ Nat.Prime.pos hp_prime ] ) a ) using 1 ; ring_nf;
    norm_num [ mul_assoc ];
    norm_num [ ← mul_assoc, ← mul_pow ];
  have h_log_mul : (Nat.log 2 (d₁ * p ^ a) : ℝ) = Nat.log 2 d₁ + a * c := by
    have h_log_mul : Nat.log 2 (d₁ * p ^ a) = Nat.log 2 d₁ + a * c := by
      have h_log_mul : Nat.log 2 d₁ < c := by
        by_cases hd₁_one : d₁ = 1;
        · rcases c with ( _ | _ | c ) <;> simp_all +decide;
          exact absurd hg.c_ge ( by norm_num );
        · exact hg.log_lt d₁ hd₁ ( lt_of_le_of_ne ( Nat.succ_le_of_lt ( Nat.pos_of_dvd_of_pos hd₁ hg.m_pos ) ) ( Ne.symm hd₁_one ) )
      grind +suggestions;
    exact_mod_cast h_log_mul;
  norm_cast at *;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  refine lt_of_lt_of_le ‹_› ?_;
  gcongr;
  · exact le_of_lt ( hg.R_pos );
  · rw [ one_le_div ( by positivity ) ] ; exact_mod_cast hp_gt.le

/-- Extension step -/
lemma extend_good (m c : ℕ) (R : ℝ) (e : ℕ) (p : ℕ)
    (hg : GoodInterlocker m c R) (_hR : R < 11 / 10)
    (hp_prime : Nat.Prime p) (hp_odd : p ≠ 2) (hp_gt : 2 ^ c < p)
    (he_pos : 0 < e)
    (hR' : R * ((p : ℝ) / (2 : ℝ) ^ c) ^ e < 11 / 10) :
    GoodInterlocker (m * p ^ e) (c * (e + 1)) (R * ((p : ℝ) / (2 : ℝ) ^ c) ^ e) := by
  have h_not_dvd : ¬ p ∣ m := prime_gt_not_dvd m c p hg.m_pos (good_m_lt_pow m c R hg) hp_gt hp_prime
  exact {
    m_pos := mul_pos hg.m_pos (pow_pos hp_prime.pos e)
    m_odd := odd_mul_prime_pow m p e hg.m_odd hp_prime hp_odd
    tau_eq := tau_coprime_mul m p e c hp_prime h_not_dvd hg.tau_eq he_pos
    c_ge := by nlinarith [hg.c_ge]
    log_inj := fun d₁ d₂ hd₁ hd₂ hd₁_gt hd₂_gt hlog => by
      obtain ⟨d₁', a₁, hd₁', ha₁, rfl⟩ := dvd_coprime_decomp m p e hp_prime d₁ hd₁
      obtain ⟨d₂', a₂, hd₂', ha₂, rfl⟩ := dvd_coprime_decomp m p e hp_prime d₂ hd₂
      exact log_inj_extend m c R e p hg hp_gt hR' h_not_dvd d₁' d₂' a₁ a₂ hd₁' hd₂' ha₁ ha₂ hd₁_gt hd₂_gt hlog
    log_lt := fun d hd hd_gt => by
      obtain ⟨d₁, a, hd₁, ha, rfl⟩ := dvd_coprime_decomp m p e hp_prime d hd
      exact log_lt_extend m c R e p hg hp_gt hR' h_not_dvd d₁ a hd₁ ha
    div_upper := fun d hd hd_pos => by
      obtain ⟨d₁, a, hd₁, ha, rfl⟩ := dvd_coprime_decomp m p e hp_prime d hd
      exact_mod_cast div_upper_extend m c R e p hg hp_prime hp_gt hR' d₁ a hd₁ ha hd_pos
    R_pos := mul_pos hg.R_pos (pow_pos (_root_.div_pos (Nat.cast_pos.mpr hp_prime.pos) (by positivity)) e)
  }

/-!
# Iterative construction of interlocking partners

We prove `separable_of_well_spread_aux` by iterating `extend_good`:
1. **Doubling phase**: extend `base_good_231` (c=8) by factor 2, (t-3) times, reaching c=2^t.
2. **j-phase**: extend from c=2^t to c=2^t*j using prime factors of j.

The R-ratio is tracked via partial sums of 1/4^{i+4}, bounded by exp(1/192) < 11/10.
-/

/-- exp(1/96) < 11/10. Used for the combined doubling + j-phase bound. -/
lemma exp_one_96_lt : Real.exp ((1 : ℝ) / 96) < 11 / 10 := by
  rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ] ; norm_num;
  rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
  exact Real.exp_one_lt_d9.trans_le <| by norm_num;

/-- Partial sum of the geometric series 1/4^{i+4} is strictly less than 1/192. -/
lemma partial_sum_lt_inv192 (a : ℕ) :
    ∑ i ∈ Finset.range a, ((1 : ℝ) / 4) ^ (i + 4) < 1 / 192 := by
  ring_nf;
  rw [ ← Finset.sum_mul _ _ _, geom_sum_eq ] <;> ring_nf <;> norm_num

/-- Find a prime for doubling step a with the right ratio bound. -/
lemma find_doubling_prime (a : ℕ)
    (h_dusart : ∀ x : ℕ, 396738 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x) ^ 2))) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 2 ^ (8 * 2 ^ a) < p ∧
    ((p : ℝ) / 2 ^ (8 * 2 ^ a)) < Real.exp ((1 : ℝ) / 4 ^ (a + 4)) := by
  by_cases ha : a = 0 ∨ a = 1;
  · rcases ha with ( rfl | rfl ) <;> norm_num at *;
    · use 257
      norm_num [ratio_bound_257];
    · exact ⟨ 65537, by norm_num, by norm_num, by norm_num, by rw [ div_lt_iff₀ ] <;> norm_num ; linarith [ ratio_bound_65537 ] ⟩;
  · obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := h_dusart ( 2 ^ ( 8 * 2 ^ a ) ) ( by
      exact le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) ( Nat.mul_le_mul_left _ ( Nat.pow_le_pow_right ( by decide ) ( Nat.lt_of_le_of_ne ( Nat.pos_of_ne_zero ( by tauto ) ) ( Ne.symm ( by tauto ) ) ) ) ) ) );
    refine' ⟨ p, hp₁, _, hp₂, _ ⟩;
    · linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( show 8 * 2 ^ a ≥ 8 by linarith [ Nat.one_le_pow a 2 ( by decide ) ] ) ];
    · convert dusart_ratio_bound ( 2 ^ ( 8 * 2 ^ a ) ) _ ( a + 4 ) _ _ _ p hp₁ hp₂ hp₃ using 1 <;> norm_num;
      · exact le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) ( Nat.mul_le_mul_left _ ( Nat.pow_le_pow_right ( by decide ) ( Nat.lt_of_le_of_ne ( Nat.pos_of_ne_zero ( by tauto ) ) ( Ne.symm ( by tauto ) ) ) ) ) );
      · omega;
      · exact pow_le_pow_right₀ ( by norm_num ) ( by ring_nf; norm_num );
      · exact ⟨ p, hp₁, hp₂, by simpa [ mul_pow, mul_assoc, mul_comm, mul_left_comm ] using hp₃ ⟩

lemma doubling_chain_tight (a : ℕ)
    (h_dusart : ∀ x : ℕ, 396738 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x) ^ 2))) :
    ∃ m R, GoodInterlocker m (8 * 2 ^ a) R ∧ R ≤ Real.exp (1 / 192) := by
  have := @partial_sum_lt_inv192;
  obtain ⟨m, R, hmR⟩ : ∃ m R, GoodInterlocker m (8 * 2 ^ a) R ∧ R ≤ Real.exp (∑ i ∈ Finset.range a, ((1 : ℝ) / 4) ^ (i + 4)) := by
    induction' a with a ih;
    · exact ⟨ 231, 1, base_good_231, by norm_num ⟩;
    · obtain ⟨ m, R, hm, hR ⟩ := ih
      obtain ⟨ p, hp_prime, hp_odd, hp_gt, hp_bound ⟩ := find_doubling_prime a h_dusart
      use m * p^1, R * ((p : ℝ) / 2 ^ (8 * 2 ^ a)) ^ 1
      constructor
      ·
        convert extend_good m (8 * 2 ^ a) R 1 p hm _ hp_prime hp_odd hp_gt _ _ using 1 <;> norm_num [ pow_succ' ] at *;
        · ring;
        · exact hR.trans_lt ( lt_of_lt_of_le ( Real.exp_lt_exp.mpr ( this a ) ) ( by exact le_trans ( Real.exp_le_exp.mpr ( show ( 1 : ℝ ) / 192 ≤ 1 / 96 by norm_num ) ) ( by exact le_of_lt ( exp_one_96_lt ) ) ) );
        · refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_right hR ( by positivity ) ) _;
          refine' lt_of_lt_of_le ( mul_lt_mul_of_pos_left hp_bound ( Real.exp_pos _ ) ) _;
          rw [ ← Real.exp_add ];
          refine' le_trans ( Real.exp_le_exp.mpr ( add_le_add ( le_of_lt ( this a ) ) ( show ( 4 ^ ( a + 4 ) : ℝ ) ⁻¹ ≤ 1 / 192 by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 4 ) ( show a + 4 ≥ 4 by linarith ) ] ) ) ) _ ; norm_num ;
          exact le_of_lt ( exp_one_96_lt )
      ·
        norm_num [ Finset.sum_range_succ ] at *;
        convert mul_le_mul hR hp_bound.le ( by positivity ) ( by positivity ) using 1 ; rw [ Real.exp_add ] ; ring_nf;
        norm_num;
  exact ⟨ m, R, hmR.1, hmR.2.trans ( Real.exp_le_exp.mpr ( le_of_lt ( this a ) ) ) ⟩

lemma eight_mul_pow2_eq (t : ℕ) (ht : t ≥ 3) : 8 * 2 ^ (t - 3) = 2 ^ t := by
  have h3 : t = (t - 3) + 3 := by omega
  calc 8 * 2 ^ (t - 3) = 2 ^ 3 * 2 ^ (t - 3) := by norm_num
    _ = 2 ^ (3 + (t - 3)) := (pow_add 2 3 (t - 3)).symm
    _ = 2 ^ t := by congr 1; omega

/-- For c ≥ 2^50, the Dudek threshold is met. -/
lemma dudek_threshold_met (c : ℕ) (hc : c ≥ 2 ^ 50) :
    (Real.exp (Real.exp 33.217) : ℝ) ≤ (2 : ℝ) ^ (c : ℕ) := by
  refine' le_trans _ ( pow_le_pow_right₀ ( by norm_num ) hc );
  have h_exp_exp : Real.exp (Real.exp 33.217) < 2 ^ (2 ^ 50) := by
    have : Real.exp 33.217 < 2 ^ 50 * Real.log 2 := by
      have := Real.exp_one_lt_d9.le;
      rw [ show Real.exp 33.217 = ( Real.exp 1 ) ^ 33 * Real.exp 0.217 by rw [ ← Real.exp_nat_mul, ← Real.exp_add ] ; norm_num ];
      exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by positivity ) ) ( by have := Real.log_two_gt_d9; norm_num1 at *; nlinarith [ Real.exp_pos 0.217, Real.exp_le_exp.2 ( show ( 0.217 : ℝ ) ≤ 1 by norm_num ), pow_le_pow_left₀ ( by positivity ) this.le 33 ] )
    rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
    exact this.trans_le ( by rw [ Real.log_pow ] ; norm_num );
  exact_mod_cast h_exp_exp.le

/-
Helper lemmas for j-phase bound
-/
lemma coprime_of_lt_minFac (d j : ℕ)
    (h : ∀ p : ℕ, Nat.Prime p → p ∣ d → p < j.minFac) :
    Nat.Coprime d j := by
  -- Assume that there's a common divisor p of d and j. Then p must be a prime divisor of d. By the hypothesis h, p must be less than the minimal prime factor of j. But since p divides j, it can't be less than the minimal prime factor of j. Therefore, p must be 1. Hence, d and j are coprime.
  by_contra h_not_coprime
  obtain ⟨p, hp_prime, hp_div_d, hp_div_j⟩ : ∃ p, Nat.Prime p ∧ p ∣ d ∧ p ∣ j := by
    exact Nat.Prime.not_coprime_iff_dvd.mp h_not_coprime;
  exact not_le_of_gt ( h p hp_prime hp_div_d ) ( Nat.minFac_le_of_dvd hp_prime.two_le hp_div_j )

lemma ws_prev_divisor_bound (j₀ : ℕ) (hj₀ : 1 ≤ j₀) (C : ℝ)
    (hws : WellSpreadDivisors C j₀) (q : ℕ) (hq_prime : Nat.Prime q) (hq_dvd : q ∣ j₀) :
    ∃ d : ℕ, d ∣ j₀ ∧ d < q ∧ 1 ≤ d ∧ (q : ℝ) ≤ Real.exp (max C (d : ℝ)) := by
  -- Let d be the largest divisor of j₀ that is less than q.
  obtain ⟨d, hd_dvd, hd_lt⟩ : ∃ d : ℕ, d ∣ j₀ ∧ d < q ∧ ∀ d' : ℕ, d' ∣ j₀ → d' < q → d' ≤ d := by
    have h_divisors_finite : Set.Finite {d : ℕ | d ∣ j₀ ∧ d < q} := by
      exact Set.finite_iff_bddAbove.mpr ⟨ q, fun x hx => le_of_lt hx.2 ⟩;
    obtain ⟨d, hd⟩ : ∃ d ∈ {d : ℕ | d ∣ j₀ ∧ d < q}, ∀ d' ∈ {d : ℕ | d ∣ j₀ ∧ d < q}, d' ≤ d := by
      apply_rules [ Set.exists_max_image ];
      exact ⟨ 1, one_dvd _, hq_prime.one_lt ⟩;
    exact ⟨ d, hd.1.1, hd.1.2, fun d' hd' hd'' => hd.2 d' ⟨ hd', hd'' ⟩ ⟩;
  refine' ⟨ d, hd_dvd, hd_lt.1, _, _ ⟩;
  · exact Nat.pos_of_dvd_of_pos hd_dvd hj₀;
  · convert hws d q ?_ hd_dvd hq_dvd ?_ ?_ using 1;
    · exact Nat.pos_of_dvd_of_pos hd_dvd hj₀;
    · linarith;
    · exact fun c hc₁ hc₂ hc₃ => not_lt_of_ge ( hd_lt.2 c hc₁ hc₃ ) hc₂

/-
We have minFac(j) ≤ 2^(c/4) from well-spread + invariant.
-/
lemma minFac_bound_from_ws (t : ℕ) (ht : t ≥ 50) (c : ℕ) (hc : c ≥ 2 ^ t)
    (j₀ j : ℕ) (hj₀ : 1 ≤ j₀) (hj : 2 ≤ j) (hjdvd : j ∣ j₀)
    (C : ℝ) (hC : C = Real.log 2 * 2 ^ (t - 2))
    (hws : WellSpreadDivisors C j₀) (hcj : 2 ^ t * j₀ ≤ c * j) :
    (j.minFac : ℝ) ≤ (2 : ℝ) ^ ((c : ℝ) / 4) := by
  -- By the well-spread hypothesis, there exists a divisor d of j₀ such that d < q (where q is the minimum prime factor of j) and q ≤ exp(max(C, d)).
  obtain ⟨d, hd_div, hd_lt_q, hd_ge_1, hq_le_exp⟩ : ∃ d : ℕ, d ∣ j₀ ∧ d < j.minFac ∧ 1 ≤ d ∧ (j.minFac : ℝ) ≤ Real.exp (max C (d : ℝ)) := by
    apply ws_prev_divisor_bound j₀ hj₀ C hws j.minFac (Nat.minFac_prime (by linarith)) (Nat.minFac_dvd j |> dvd_trans <| hjdvd);
  nontriviality;
  refine le_trans hq_le_exp ?_;
  -- Since $d \leq j₀/j$ and $j₀/j \leq c/2^t$, we have $d \leq c/2^t$.
  have hd_le_ct : (d : ℝ) ≤ c / 2 ^ t := by
    have hd_le_ct : (d : ℝ) ≤ j₀ / j := by
      rw [ le_div_iff₀ ] <;> norm_cast;
      · have h_coprime : Nat.Coprime d j := by
          apply coprime_of_lt_minFac d j;
          exact fun p pp dp => lt_of_le_of_lt ( Nat.le_of_dvd ( by linarith ) dp ) hd_lt_q;
        exact Nat.le_of_dvd hj₀ ( Nat.Coprime.mul_dvd_of_dvd_of_dvd h_coprime hd_div hjdvd );
      · linarith;
    exact hd_le_ct.trans ( by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith [ pow_pos ( zero_lt_two' ℕ ) t ] );
  -- Since $C = \log 2 \cdot 2^{t-2}$ and $d \leq c/2^t$, we have $\max(C, d) \leq \max(\log 2 \cdot 2^{t-2}, c/2^t)$.
  have h_max_le : max C (d : ℝ) ≤ max (Real.log 2 * 2 ^ (t - 2)) (c / 2 ^ t) := by
    exact max_le_max ( hC.le ) hd_le_ct;
  refine' le_trans ( Real.exp_le_exp.mpr h_max_le ) _;
  rw [ max_def ] ; split_ifs <;> norm_num [ Real.rpow_def_of_pos ];
  · rw [ div_le_iff₀ ] <;> ring_nf <;> norm_num;
    nlinarith only [ show ( c : ℝ ) ≥ 2 ^ t by exact_mod_cast hc, show ( 2 : ℝ ) ^ t ≥ 2 ^ 50 by exact pow_le_pow_right₀ ( by norm_num ) ht, Real.log_two_gt_d9, mul_le_mul_of_nonneg_left ( show ( 2 : ℝ ) ^ t ≥ 2 ^ 50 by exact pow_le_pow_right₀ ( by norm_num ) ht ) ( show ( 0 : ℝ ) ≤ c by positivity ) ];
  · gcongr;
    rw [ le_div_iff₀ ] <;> norm_cast;
    rcases t with ( _ | _ | t ) <;> simp_all +decide [ pow_succ' ];
    grind

/-
After consuming 3*2^(-c/12) from budget ≥ 6*2^(-c/12),
    the remainder ≥ 6*2^(-c*q/12) for q ≥ 2 with c*(q-1) ≥ 12.
-/
lemma budget_remainder (c q : ℕ) (budget : ℝ)
    (hq : 2 ≤ q) (hc : c ≥ 2 ^ 50)
    (hbudget_ge : budget ≥ 6 * (2 : ℝ) ^ (-(c : ℝ) / 12)) :
    budget - 3 * (2 : ℝ) ^ (-(c : ℝ) / 12) ≥
      6 * (2 : ℝ) ^ (-((c : ℝ) * (q : ℝ)) / 12) := by
  refine' le_trans _ ( sub_le_sub_right hbudget_ge _ );
  rw [ show ( - ( c * q : ℝ ) / 12 ) = - ( c : ℝ ) / 12 + ( - ( c * ( q - 1 ) : ℝ ) / 12 ) by ring, Real.rpow_add ] <;> ring_nf <;> norm_num;
  rw [ mul_assoc ] ; gcongr;
  refine' le_trans ( mul_le_mul_of_nonneg_right ( Real.rpow_le_rpow_of_exponent_le ( by norm_num ) <| show ( c : ℝ ) * ( 1 / 12 ) + - ( c * q * ( 1 / 12 ) ) ≤ -1 by nlinarith [ show ( c : ℝ ) ≥ 2 ^ 50 by exact_mod_cast hc, show ( q : ℝ ) ≥ 2 by exact_mod_cast hq ] ) <| by norm_num ) _ ; norm_num

/-
The Dudek ratio fits within the budget.
-/
lemma dudek_ratio_le_budget (c : ℕ) (q : ℕ) (p : ℕ)
    (hc : c ≥ 2 ^ 50) (hq_bound : (q : ℝ) ≤ (2 : ℝ) ^ ((c : ℝ) / 4))
    (hp_upper : (p : ℝ) < (2 : ℝ) ^ c + 3 * ((2 : ℝ) ^ c) ^ ((2 : ℝ) / 3))
    (hpn : 2 ^ c < p)
    (budget : ℝ)
    (hbudget_ge : budget ≥ 6 * (2 : ℝ) ^ (-(c : ℝ) / 12)) :
    ((p : ℝ) / (2 : ℝ) ^ c) ^ (q - 1) < Real.exp budget := by
  -- Apply the lemma dudek_ratio_bound with n = 2^c and e = q-1.
  have h_dudek : ((p : ℝ) / (2 : ℝ) ^ c) ^ (q - 1) < Real.exp (3 * (2 : ℝ) ^ (-(c : ℝ) / 12)) := by
    convert dudek_ratio_bound ( 2 ^ c ) p ( q - 1 ) _ _ _ _ using 1 <;> norm_num;
    · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> ring_nf ; norm_num;
    · exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) ( show c ≥ 1 by linarith ) );
    · convert hp_upper using 1;
    · exact_mod_cast hpn;
    · refine' le_trans _ ( Real.rpow_le_rpow ( by positivity ) ( show ( 2 : ℝ ) ^ c ≥ 2 ^ ( c : ℝ ) from le_of_eq ( by norm_num [ Real.rpow_natCast ] ) ) ( by positivity ) );
      rw [ ← Real.rpow_mul ] <;> norm_num;
      exact le_trans ( Nat.cast_le.mpr ( Nat.pred_le _ ) ) ( by simpa [ mul_one_div ] using hq_bound );
  exact h_dudek.trans_le ( Real.exp_le_exp.mpr <| by linarith [ Real.rpow_pos_of_pos zero_lt_two ( - ( c : ℝ ) / 12 ) ] )

/-
The j-phase of the construction. Given GoodInterlocker m c R,
well-spread divisors for j₀, j | j₀, and the invariant 2^t * j₀ ≤ c * j,
we can extend to GoodInterlocker m' (c*j) R' with R' < 11/10.
-/
lemma j_phase (t : ℕ) (ht : t ≥ 50) (c : ℕ) (hc : c ≥ 2 ^ t)
    (j₀ : ℕ) (hj₀ : 1 ≤ j₀)
    (C : ℝ) (hC : C = Real.log 2 * 2 ^ (t - 2))
    (hws : WellSpreadDivisors C j₀)
    (j : ℕ) (hj : 1 ≤ j)
    (hjdvd : j ∣ j₀)
    (hcj : 2 ^ t * j₀ ≤ c * j)
    (m : ℕ) (R : ℝ) (hg : GoodInterlocker m c R)
    (budget : ℝ) (hbudget_pos : 0 < budget)
    (hRbudget : R * Real.exp budget < 11 / 10)
    (hbudget_ge : budget ≥ 6 * (2 : ℝ) ^ (-(c : ℝ) / 12))
    (h_dudek : ∀ x : ℕ, (Real.exp (Real.exp 33.217) : ℝ) ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) < x + 3 * (x : ℝ) ^ (2/3 : ℝ)) :
    ∃ m' R', GoodInterlocker m' (c * j) R' ∧ R' < 11 / 10 := by
  -- By strong induction on j using Nat.strong_rec_on.
  induction' j using Nat.strong_induction_on with j ih generalizing m R c budget;
  by_cases hj1 : j = 1;
  · exact ⟨ m, R, by simpa [ hj1 ] using hg, by nlinarith [ Real.add_one_le_exp budget ] ⟩;
  · -- Let q = minFac(j), q ≤ 2^(c/4) from the invariant + well-spread
    obtain ⟨q, hq_prime, hq_gt_one, hq_dvd_j, hq_bound⟩ : ∃ q : ℕ, Nat.Prime q ∧ 2 ≤ q ∧ q ∣ j ∧ (q : ℝ) ≤ (2 : ℝ) ^ ((c : ℝ) / 4) := by
      have := minFac_bound_from_ws t ht c hc j₀ j hj₀ ( Nat.lt_of_le_of_ne hj ( Ne.symm hj1 ) ) hjdvd C hC hws hcj;
      exact ⟨ j.minFac, Nat.minFac_prime hj1, Nat.Prime.two_le ( Nat.minFac_prime hj1 ), Nat.minFac_dvd j, this ⟩;
    -- Find prime p via Dudek.
    obtain ⟨p, hp_prime, hp_gt, hp_upper⟩ : ∃ p : ℕ, Nat.Prime p ∧ 2 ^ c < p ∧ (p : ℝ) < 2 ^ c + 3 * ((2 : ℝ) ^ c) ^ ((2 : ℝ) / 3) := by
      convert h_dudek ( 2 ^ c ) _ using 1;
      · norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ];
      · have := dudek_threshold_met c ( by linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ht ] ) ; aesop;
    -- Apply extend_good to get GoodInterlocker (m*p^(q-1)) (c*q) R'
    obtain ⟨m', R', hm', hR'⟩ : ∃ m' R', GoodInterlocker m' (c * q) R' ∧ R' < 11 / 10 ∧ R' = R * ((p : ℝ) / 2 ^ c) ^ (q - 1) := by
      have h_ratio : R * ((p : ℝ) / 2 ^ c) ^ (q - 1) < 11 / 10 := by
        have h_ratio : ((p : ℝ) / 2 ^ c) ^ (q - 1) < Real.exp budget := by
          apply dudek_ratio_le_budget c q p (by
          exact le_trans ( pow_le_pow_right₀ ( by decide ) ht ) hc) hq_bound hp_upper (by
          exact_mod_cast hp_gt) budget hbudget_ge;
        exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_left h_ratio.le hg.R_pos.le ) hRbudget;
      have := @extend_good m c R (q - 1) p hg (by
      exact lt_of_le_of_lt ( le_mul_of_one_le_right ( show 0 ≤ R by exact hg.R_pos.le ) ( Real.one_le_exp hbudget_pos.le ) ) hRbudget) hp_prime (by
      grind) hp_gt (by
      exact Nat.sub_pos_of_lt hq_gt_one) h_ratio;
      exact ⟨ _, _, by rwa [ Nat.sub_add_cancel hq_prime.pos ] at this, h_ratio, rfl ⟩;
    -- Recurse on j' = j / minFac(j)
    obtain ⟨m'', R'', hm'', hR''⟩ : ∃ m'' R'', GoodInterlocker m'' (c * q * (j / q)) R'' ∧ R'' < 11 / 10 := by
      apply ih (j / q) (Nat.div_lt_self hj (by linarith)) (c * q) (by
      nlinarith [ Nat.Prime.two_le hq_prime ]) (by
      exact Nat.div_pos ( Nat.le_of_dvd hj hq_dvd_j ) hq_prime.pos) (by
      exact Nat.dvd_trans ( Nat.div_dvd_of_dvd hq_dvd_j ) hjdvd) (by
      rw [ Nat.mul_assoc, Nat.mul_div_cancel' hq_dvd_j ] ; linarith) m' R' hm' (budget - 3 * (2 : ℝ) ^ (-(c : ℝ) / 12)) (by
      grind) (by
      have h_ratio : ((p : ℝ) / 2 ^ c) ^ (q - 1) < Real.exp (3 * (2 : ℝ) ^ (-(c : ℝ) / 12)) := by
        convert dudek_ratio_bound ( 2 ^ c ) p ( q - 1 ) _ _ _ _ using 1 <;> norm_num;
        · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> ring_nf ; norm_num;
        · exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) ( show c ≥ 1 by linarith [ Nat.pow_le_pow_right ( by norm_num : 1 ≤ 2 ) ht ] ) );
        · convert hp_upper using 1;
        · exact_mod_cast hp_gt;
        · rw [ Nat.cast_pred hq_prime.pos ] ; exact le_trans ( sub_le_self _ zero_le_one ) hq_bound |> le_trans <| by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> ring_nf <;> norm_num;
      rw [ hR'.2, mul_assoc ];
      refine' lt_of_le_of_lt _ hRbudget;
      gcongr;
      · exact le_of_lt ( hg.R_pos );
      · exact le_trans ( mul_le_mul_of_nonneg_right h_ratio.le ( Real.exp_nonneg _ ) ) ( by rw [ ← Real.exp_add ] ; ring_nf; norm_num )) (by
      convert budget_remainder c q budget hq_gt_one ( show c ≥ 2 ^ 50 by exact le_trans ( by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) ht ) ) hc ) hbudget_ge using 1;
      norm_num);
    exact ⟨ m'', R'', by simpa only [ Nat.mul_assoc, Nat.mul_div_cancel' hq_dvd_j ] using hm'', hR'' ⟩

/-
Initial budget bound: 1/192 ≥ 6·2^{-c/12} for c ≥ 2^50.
-/
lemma budget_init_bound (c : ℕ) (hc : c ≥ 2 ^ 50) :
    (6 : ℝ) * (2 : ℝ) ^ (-(c : ℝ) / 12) ≤ 1 / 192 := by
  -- We'll use that $2^{-c/12} \leq 2^{-11}$ since $c \geq 2^{50}$.
  have h_exp : (2 : ℝ) ^ (-(c : ℝ) / 12) ≤ (2 : ℝ) ^ (-11 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le ( by norm_num ) ( by linarith [ ( by norm_cast : ( 2 ^ 50 : ℝ ) ≤ c ) ] );
  exact le_trans ( mul_le_mul_of_nonneg_left h_exp <| by norm_num ) <| by norm_num;

theorem separable_of_well_spread_aux_proof (t : ℕ) (ht : t ≥ 50)
    (C : ℝ) (hC : C = Real.log 2 * 2 ^ (t - 2))
    (j : ℕ) (hj : 0 < j)
    (hws : WellSpreadDivisors C j)
    (h_dusart : ∀ x : ℕ, 396738 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x) ^ 2)))
    (h_dudek : ∀ x : ℕ, (Real.exp (Real.exp 33.217) : ℝ) ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) < x + 3 * (x : ℝ) ^ (2/3 : ℝ)) :
    Separable (2 ^ (2 ^ t * j)) := by
  -- Step 1: Doubling chain gives GoodInterlocker m (2^t) R with R ≤ exp(1/192)
  obtain ⟨m, R, hg, hR⟩ := doubling_chain_tight (t - 3) h_dusart
  rw [eight_mul_pow2_eq t (by omega)] at hg
  -- Step 2: j-phase with budget = 1/192
  have hR_budget : R * Real.exp (1 / 192) < 11 / 10 := by
    calc R * Real.exp (1/192) ≤ Real.exp (1/192) * Real.exp (1/192) := by gcongr
      _ = Real.exp (1/192 + 1/192) := (Real.exp_add _ _).symm
      _ = Real.exp (1/96) := by ring_nf
      _ < 11/10 := exp_one_96_lt
  have hbudget_ge : (6 : ℝ) * (2 : ℝ) ^ (-((2 ^ t : ℕ) : ℝ) / 12) ≤ 1 / 192 :=
    budget_init_bound (2 ^ t) (by exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) ht)
  obtain ⟨m', R', hg', hR'⟩ := j_phase t ht (2 ^ t) le_rfl j (by omega) C hC hws
    j (by omega) (dvd_refl j) (le_refl _) m R hg (1/192) (by positivity) hR_budget
    (by linarith) h_dudek
  -- Step 3: Convert to Separable
  exact good_to_separable m' (2 ^ t * j) R' hg'

/-
For C ≥ max(100, 5c²) where c is from Tenenbaum, at least half of
integers up to x have C-well-spread divisors.
-/
lemma well_spread_density (c : ℝ) (hc : 0 < c) (C : ℝ)
    (hC1 : C ≥ 100) (hC2 : C ≥ 5 * c ^ 2)
    (h_tenenbaum : ∀ x y z : ℝ, 2 ≤ y → y ≤ z → z ≤ x →
      (Set.ncard {n : ℕ | (n : ℝ) ≤ x ∧ 0 < n ∧
        ∀ d : ℕ, d ∣ n → (d : ℝ) < y ∨ z < d} : ℝ) ≤ c * x * Real.log y / Real.log z) :
    ∀ N : ℕ, N ≤ 2 * Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ WellSpreadDivisors C n} := by
  have h_bound : ∀ N : ℕ, 0 < N → 2 * Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ ¬WellSpreadDivisors C n} < N := by
    exact fun N a => non_well_spread_count_lt c hc C hC1 hC2 h_tenenbaum N a;
  intro N
  by_cases hN : N = 0;
  · simp [hN];
  · have h_card : Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ WellSpreadDivisors C n} + Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ ¬WellSpreadDivisors C n} = N := by
      rw [ ← @Set.ncard_union_eq ];
      · rw [ show { n | 1 ≤ n ∧ n ≤ N ∧ WellSpreadDivisors C n } ∪ { n | 1 ≤ n ∧ n ≤ N ∧ ¬WellSpreadDivisors C n } = Set.Icc 1 N by ext; by_cases h : WellSpreadDivisors C ‹_› <;> aesop ] ; norm_num [ Set.ncard_eq_toFinset_card' ];
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₂.2.2 hx₁.2.2;
      · exact Set.finite_iff_bddAbove.mpr ⟨ N, fun n hn => hn.2.1 ⟩;
      · exact Set.finite_iff_bddAbove.mpr ⟨ N, fun n hn => hn.2.1 ⟩;
    linarith [ h_bound N ( Nat.pos_of_ne_zero hN ) ]

/-! ## Construction of interlocking partner -/

/-- For t ≥ 50, C = ln(2)·2^{t-2}, and j with C-well-spread divisors,
the integer 2^{2^t · j} is separable.

The construction builds m = 231 · ∏_{i=4}^r p_i^{e_i} where:
- k = 2^t · j = ∏_{i=1}^r (e_i + 1) is the prime factorization of k
- n_i = 2^{(e_1+1)···(e_{i-1}+1)} for i ≥ 4
- p_i = smallest prime > n_i
Then (m, 2^k) interlocks. -/
lemma separable_of_well_spread (t : ℕ) (ht : t ≥ 50)
    (C : ℝ) (hC : C = Real.log 2 * 2 ^ (t - 2))
    (j : ℕ) (hj : 0 < j)
    (hws : WellSpreadDivisors C j)
    (h_dusart : ∀ x : ℕ, 396738 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x) ^ 2)))
    (h_dudek : ∀ x : ℕ, (Real.exp (Real.exp 33.217) : ℝ) ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) < x + 3 * (x : ℝ) ^ (2/3 : ℝ)) :
    Separable (2 ^ (2 ^ t * j)) :=
  separable_of_well_spread_aux_proof t ht C hC j hj hws h_dusart h_dudek

/-
Combining density and construction
-/
lemma dense_multiples_separable' :
    (∀ x : ℕ, 396738 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x) ^ 2))) →
    (∀ x : ℕ, (Real.exp (Real.exp 33.217) : ℝ) ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) < x + 3 * (x : ℝ) ^ (2/3 : ℝ)) →
    (∃ c : ℝ, 0 < c ∧
      ∀ x y z : ℝ, 2 ≤ y → y ≤ z → z ≤ x →
      (Set.ncard {n : ℕ | (n : ℝ) ≤ x ∧ 0 < n ∧
        ∀ d : ℕ, d ∣ n → (d : ℝ) < y ∨ z < d} : ℝ) ≤ c * x * Real.log y / Real.log z) →
    ∃ T : ℕ, 0 < T ∧
    ∀ N : ℕ, N ≤ 2 * Set.ncard {j : ℕ | 1 ≤ j ∧ j ≤ N ∧ Separable (2 ^ (T * j))} := by
  intro h₀ h₁ h₂;
  obtain ⟨ c, hc₀, hc ⟩ := h₂;
  obtain ⟨ t, ht₁, ht₂ ⟩ : ∃ t : ℕ, 50 ≤ t ∧ Real.log 2 * 2 ^ (t - 2) ≥ max 100 (5 * c ^ 2) := by
    have ht₁ : Filter.Tendsto (fun t : ℕ => Real.log 2 * 2 ^ (t - 2)) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| Filter.tendsto_sub_atTop_nat 2 );
    exact Filter.eventually_atTop.mp ( ht₁.eventually_ge_atTop ( Max.max 100 ( 5 * c ^ 2 ) ) ) |> fun ⟨ t, ht ⟩ => ⟨ t + 50, by linarith, ht _ <| by linarith ⟩;
  have h_density : ∀ N : ℕ, N ≤ 2 * Set.ncard {j : ℕ | 1 ≤ j ∧ j ≤ N ∧ WellSpreadDivisors (Real.log 2 * 2 ^ (t - 2)) j} := by
    apply well_spread_density;
    exacts [ hc₀, le_trans ( le_max_left _ _ ) ht₂, le_trans ( le_max_right _ _ ) ht₂, hc ];
  refine' ⟨ 2 ^ t, by positivity, fun N => le_trans ( h_density N ) _ ⟩;
  gcongr;
  · exact Set.finite_iff_bddAbove.mpr ⟨ N, fun x hx => hx.2.1 ⟩;
  · exact fun h => separable_of_well_spread t ht₁ _ rfl _ ( by linarith ) h h₀ h₁

lemma dense_multiples_separable :
    ∃ T : ℕ, 0 < T ∧
    ∀ N : ℕ, N ≤ 2 * Set.ncard {j : ℕ | 1 ≤ j ∧ j ≤ N ∧ Separable (2 ^ (T * j))} :=
  dense_multiples_separable' prime_gap_dusart prime_gap_dudek tenenbaum_divisor_interval

/-
The integer 2 = 2^1 is separable, witnessed by m = 3.
-/
lemma separable_two : Separable (2 ^ 1) := by
  refine ⟨3, by norm_num, Interlock.mk' ?_ ?_⟩
  · intro a b ha hb hdva hdvb hab
    exfalso
    have : a ≤ 2 := Nat.le_of_dvd (by norm_num) hdva
    have : b ≤ 2 := Nat.le_of_dvd (by norm_num) hdvb
    omega
  · intro a b ha hb hdva hdvb hab
    exfalso
    have : a ≤ 3 := Nat.le_of_dvd (by norm_num) hdva
    have : b ≤ 3 := Nat.le_of_dvd (by norm_num) hdvb
    interval_cases a; all_goals (interval_cases b; all_goals simp_all)

/-
The injection j ↦ T·j maps {j : 1 ≤ j ≤ N/T, Sep(2^{T·j})} into
  {k : 1 ≤ k ≤ N, Sep(2^k)}, giving ncard of the latter ≥ ncard of the former.
-/
lemma ncard_separable_ge_multiples (T : ℕ) (hT : 0 < T) (N : ℕ) :
    Set.ncard {j : ℕ | 1 ≤ j ∧ j ≤ N / T ∧ Separable (2 ^ (T * j))} ≤
    Set.ncard {k : ℕ | 1 ≤ k ∧ k ≤ N ∧ Separable (2 ^ k)} := by
  fapply Set.ncard_le_ncard_of_injOn;
  use fun j => T * j;
  · exact fun a ha => ⟨ by nlinarith [ ha.1 ], by nlinarith [ ha.2.1, Nat.div_mul_le_self N T ], by simpa only [ mul_comm ] using ha.2.2 ⟩;
  · aesop_cat;
  · exact Set.finite_iff_bddAbove.2 ⟨ N, fun k hk => hk.2.1 ⟩

/-
The above lemmas are sufficient to prove that the set of k such that 2^k is
separable, is positive. This result will be shown at the end of the file. The
next section contais intermediate results towards the fact that if m and n
interlock and mn = primorial k, then k ≤ 8.
-/

/-- Interlock is symmetric. -/
lemma interlock_symm {m n : ℕ} : Interlock m n ↔ Interlock n m := by
  constructor <;> intro h <;> exact Interlock.mk' h.snd h.fst

/-- If a,b > 1 divide m with nothing between them dividing n,
then m and n don't interlock (using the m-side of the interlock condition). -/
lemma interlock_false_consec_m {m n a b : ℕ}
    (hlock : Interlock m n) (ha1 : 1 < a) (hb1 : 1 < b) (hab : a < b)
    (ham : a ∣ m) (hbm : b ∣ m)
    (hno : ∀ d, a < d → d < b → d ∣ n → False) : False := by
  obtain ⟨d, hdn, hda, hdb⟩ := hlock.snd a b ha1 hb1 ham hbm hab
  exact hno d hda hdb hdn

lemma not_interlock_of_nine_primes_aux (m n : ℕ)
    (hsf : Squarefree (m * n))
    (h2 : 2 ∣ m) (h3 : 3 ∣ m * n) (h5 : 5 ∣ m * n)
    (h7 : 7 ∣ m * n) (h11 : 11 ∣ m * n) (h13 : 13 ∣ m * n)
    (h17 : 17 ∣ m * n) (h19 : 19 ∣ m * n) (h23 : 23 ∣ m * n)
    (h_interlock : Interlock m n) : False := by
  have h2n : ¬(2 ∣ n) := by
    exact fun h => absurd ( hsf.squarefree_of_dvd <| Nat.mul_dvd_mul h2 h ) ( by decide )
  have h3m : ¬(3 ∣ m) := by
    intro h3m;
    have := h_interlock.snd 2 3 ( by decide ) ( by decide ) h2 h3m ( by decide );
    grind +locals
  have h5n : ¬(5 ∣ n) := by
    intro h5n
    have h5m : 5 ∣ m := by
      have := h_interlock.snd 2 5; simp_all +decide [ Nat.Prime.dvd_mul ] ;
      have := h_interlock.fst 3 5; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
      obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := this; interval_cases d ; simp_all +decide ;
      exact absurd ( hsf.squarefree_of_dvd <| show 4 ∣ m * n from dvd_mul_of_dvd_left ( Nat.dvd_of_mod_eq_zero hd₁ ) _ ) ( by decide )
    have h5_squarefree : ¬ Squarefree (m * n) := by
      exact fun h => absurd ( h 5 <| by exact ⟨ m * n / 25, by linarith [ Nat.div_mul_cancel ( show 25 ∣ m * n from dvd_trans ( by decide ) ( mul_dvd_mul h5m h5n ) ) ] ⟩ ) ( by norm_num )
    contradiction
  have h7m : ¬(7 ∣ m) := by
    intro h7m_interlock;
    have := interlock_false_consec_m h_interlock (by norm_num : 1 < 5) (by norm_num : 1 < 7) (by norm_num : 5 < 7) (by
    exact Or.resolve_right ( Nat.prime_iff.mp ( by norm_num ) |> fun p => p.dvd_mul.mp h5 ) h5n) (by
    assumption) (by
    intro d hd₁ hd₂ hd₃; interval_cases d ; simp_all +decide ;
    grind);
    contradiction
  have h11m : ¬(11 ∣ m) := by
    intro h11mlock;
    have := h_interlock.fst 10 11; simp_all +decide;
    have := h_interlock.snd 10 11; simp_all +decide [ Nat.Prime.dvd_mul ] ;
    exact absurd ( this ( Nat.lcm_dvd h2 h5 ) ) ( by rintro ⟨ d, hd1, hd2, hd3 ⟩ ; interval_cases d )
  have h13n : ¬(13 ∣ n) := by
    intro h13nlock;
    have := h_interlock.snd 11 13 ( by decide ) ( by decide ) ; simp_all +decide [ Nat.Prime.dvd_mul ] ;
    have := h_interlock.fst 11 13 ( by norm_num ) ( by norm_num ) h11 h13nlock ( by norm_num ) ; obtain ⟨ d, hd1, hd2, hd3 ⟩ := this; interval_cases d ; norm_num at hd1 hd2 hd3;
    exact absurd ( Nat.dvd_trans ( by decide : 3 ∣ 12 ) hd1 ) h3m
  have h17m : ¬(17 ∣ m) := by
    intro h17mlock;
    obtain ⟨d, hd⟩ : ∃ d, d ∣ n ∧ 13 < d ∧ d < 17 := by
      have h17nlock : ∃ d, d ∣ n ∧ 13 < d ∧ d < 17 := by
        have := h_interlock.left
        apply h_interlock.right;
        · bv_decide;
        · norm_num;
        · simp_all +decide [ Nat.Prime.dvd_mul ];
        · assumption;
        · norm_num;
      exact h17nlock;
    rcases hd with ⟨ hd₁, hd₂, hd₃ ⟩ ; interval_cases d <;> simp_all +decide;
    · grind +qlia;
    · exact h5n ( dvd_trans ( by decide ) hd₁ );
    · lia
  have h19n : ¬(19 ∣ n) := by
    intro h19nlock;
    have h18m : ¬(18 ∣ m) := by
      exact fun h => h3m ( dvd_trans ( by decide ) h )
    obtain ⟨d, hd⟩ : ∃ d, d ∣ m ∧ 17 < d ∧ d < 19 := by
      apply h_interlock.left 17 19 (by norm_num) (by norm_num) (by
      exact Or.resolve_left ( Nat.prime_iff.mp ( by norm_num ) |> fun p => p.dvd_mul.mp h17 ) h17m) (by
      assumption) (by norm_num);
    rcases hd with ⟨ hd₁, hd₂, hd₃ ⟩ ; interval_cases d ; simp_all +decide ;
  have h23m : ¬(23 ∣ m) := by
    intro h23mlock;
    obtain ⟨d, hd⟩ : ∃ d, d ∣ n ∧ 23 < d ∧ d < 26 := by
      have := h_interlock.snd 23 26 ( by decide ) ( by decide ) h23mlock ( show 26 ∣ m from ?_ ) ( by decide ) ; aesop;
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by decide ) h2 ( show 13 ∣ m from by exact Or.resolve_right ( Nat.prime_iff.mp ( by decide ) |> fun p => p.dvd_mul.mp h13 ) h13n );
    rcases hd with ⟨ hd₁, hd₂, hd₃ ⟩ ; interval_cases d <;> simp_all +decide ;
    · lia;
    · exact h5n ( dvd_trans ( by decide ) hd₁ );
  have h3n : 3 ∣ n := by
    exact Or.resolve_left ( Nat.prime_three.dvd_mul.mp h3 ) h3m
  have h5m : 5 ∣ m := by
    exact Or.resolve_right ( Nat.prime_iff.mp ( by norm_num ) |> fun p => p.dvd_mul.mp h5 ) h5n
  have h7n : 7 ∣ n := by
    exact Or.resolve_left ( Nat.prime_iff.mp ( by norm_num ) |> fun p => p.dvd_mul.mp h7 ) h7m
  have h11n : 11 ∣ n := by
    exact Or.resolve_left ( Nat.prime_iff.mp ( by norm_num ) |> fun p => p.dvd_mul.mp h11 ) h11m
  have h13m : 13 ∣ m := by
    exact Or.resolve_right ( Nat.prime_iff.mp ( by norm_num ) |> fun p => p.dvd_mul.mp h13 ) h13n
  have h17n : 17 ∣ n := by
    exact Or.resolve_left ( Nat.prime_iff.mp ( by norm_num ) |> fun p => p.dvd_mul.mp h17 ) h17m
  have h19m : 19 ∣ m := by
    exact Or.resolve_right ( Nat.prime_iff.mp ( by norm_num ) |> fun p => p.dvd_mul.mp h19 ) h19n;
  have h23n : 23 ∣ n := by
    exact Or.resolve_left ( Nat.prime_iff.mp ( by norm_num ) |> fun p => p.dvd_mul.mp h23 ) h23m;
  have h21n : 21 ∣ n := by
    exact Nat.lcm_dvd h3n h7n;
  have := h_interlock.fst 21 23; simp_all +decide ;
  obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := this; interval_cases d ; simp_all +decide ;
  exact absurd ( Nat.dvd_trans ( by decide : 11 ∣ 22 ) hd₁ ) h11m

/-
If the first 9 primes all divide mn and mn is squarefree,
then m and n don't interlock.
-/
theorem not_interlock_of_nine_primes (m n : ℕ)
    (hsf : Squarefree (m * n))
    (h2 : 2 ∣ m * n) (h3 : 3 ∣ m * n) (h5 : 5 ∣ m * n)
    (h7 : 7 ∣ m * n) (h11 : 11 ∣ m * n) (h13 : 13 ∣ m * n)
    (h17 : 17 ∣ m * n) (h19 : 19 ∣ m * n) (h23 : 23 ∣ m * n) :
    ¬ Interlock m n := by
  intro h_interlock
  by_cases h2m : 2 ∣ m
  · exact not_interlock_of_nine_primes_aux m n hsf h2m h3 h5 h7 h11 h13 h17 h19 h23 h_interlock
  · exact not_interlock_of_nine_primes_aux n m ( by rwa [ mul_comm ] ) ( Or.resolve_left ( Nat.prime_two.dvd_mul.mp h2 ) h2m ) ( by rwa [ mul_comm ] ) ( by rwa [ mul_comm ] ) ( by rwa [ mul_comm ] ) ( by rwa [ mul_comm ] ) ( by rwa [ mul_comm ] ) ( by rwa [ mul_comm ] ) ( by rwa [ mul_comm ] ) ( by rwa [ mul_comm ] ) ( interlock_symm.mp h_interlock )

/-- No prime `Nat.nth Nat.Prime j` with `j ≥ k` divides `Primorial k`. -/
lemma nth_prime_not_dvd_primorial (j k : ℕ) (hjk : k ≤ j) :
    ¬ (Nat.nth Nat.Prime j ∣ Primorial k) := by
  induction k with
  | zero =>
    simp [Primorial]
    exact (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j).one_lt.ne'
  | succ k ih =>
    simp only [Primorial]
    intro h
    have hpk : Nat.Prime (Nat.nth Nat.Prime k) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
    have hpj : Nat.Prime (Nat.nth Nat.Prime j) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j
    rw [hpj.dvd_mul] at h
    rcases h with h1 | h2
    · rcases hpk.eq_one_or_self_of_dvd _ h1 with h | h
      · exact hpj.one_lt.ne' h
      · exact absurd (Nat.nth_injective Nat.infinite_setOf_prime h) (by omega)
    · exact ih (by omega) h2

/-- `Primorial k` is squarefree. -/
lemma primorial_squarefree (k : ℕ) : Squarefree (Primorial k) := by
  induction k with
  | zero => simp [Primorial]
  | succ k ih =>
    simp only [Primorial]
    rw [squarefree_mul_iff]
    refine ⟨?_, ?_, ih⟩
    · exact (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k).coprime_iff_not_dvd.mpr
        (nth_prime_not_dvd_primorial k k le_rfl)
    · exact (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k).squarefree

/-- The i-th prime divides `Primorial k` for `i < k`. -/
lemma nth_prime_dvd_primorial (i k : ℕ) (h : i < k) :
    Nat.nth Nat.Prime i ∣ Primorial k := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [Primorial]
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with rfl | h'
    · exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (ih h') _

/-- Every prime p ≤ 23 satisfies p ∣ Primorial 9. -/
lemma small_prime_dvd_primorial_nine (p : ℕ) (hp : Nat.Prime p) (hle : p ≤ 23) :
    p ∣ Primorial 9 := by
  -- p is one of the first 9 primes
  have hlt : Nat.count Nat.Prime p < 9 := by
    calc Nat.count Nat.Prime p ≤ Nat.count Nat.Prime 23 := by
            exact Nat.count_monotone Nat.Prime (by omega)
         _ = 8 := by decide
         _ < 9 := by omega
  have hlt24 : p < 24 := by omega
  have h_count_lt : Nat.count Nat.Prime p < 9 := hlt
  -- nth (count p) = p
  have h_nth : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  rw [← h_nth]
  exact nth_prime_dvd_primorial _ 9 (by omega)

/-- Primorial k for k ≥ 9 is divisible by all primes ≤ 23. -/
lemma small_prime_dvd_primorial (p k : ℕ) (hp : Nat.Prime p) (hle : p ≤ 23) (hk : 9 ≤ k) :
    p ∣ Primorial k := by
  have h9 : p ∣ Primorial 9 := small_prime_dvd_primorial_nine p hp hle
  suffices hsub : Primorial 9 ∣ Primorial k from dvd_trans h9 hsub
  -- Primorial 9 divides Primorial k for k ≥ 9 by induction
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with rfl | h'
    · exact dvd_refl _
    · simp only [Primorial]
      exact dvd_mul_of_dvd_right (ih (by omega)) _

/-!
# Result 1: For k > 2 with k ≡ 1,2,9,10 (mod 12), 2^k is not separable.
-/

/-- If τ(m) is odd and p is prime with p | m, then p² | m. -/
lemma sq_dvd_of_odd_card_divisors {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hpm : p ∣ m)
    (hodd : ¬ 2 ∣ m.divisors.card) : p ^ 2 ∣ m := by
  have h_card_divisors : m.divisors.card = ∏ q ∈ m.primeFactors, (m.factorization q + 1) := by
    exact card_divisors hm
  have h_factor_even : ∀ q ∈ m.primeFactors, Even (m.factorization q) := by
    simp_all +decide [ Finset.prod_nat_mod, Nat.even_iff ]
    intro q hq hqm; contrapose! hodd; simp_all +decide [ Finset.prod_eq_mul_prod_diff_singleton <| Nat.mem_primeFactors.mpr ⟨ hq, hqm, hm ⟩ ]
    norm_num [ Nat.add_mod, Nat.mul_mod, hodd ]
  exact dvd_trans ( pow_dvd_pow _ ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ) ) ( even_iff_two_dvd.mp ( h_factor_even p ( by aesop ) ) ) ) ) ( Nat.ordProj_dvd _ _ )

/-- If m and 2^k interlock, then m is odd, assuming k > 2. -/
lemma interlock_pow_two_odd {m k : ℕ} (_hm : 0 < m) (hk : 2 < k)
    (hlock : Interlock m (2^k)) : ¬ (2 ∣ m) := by
  by_contra h_two_divides_m
  have h_three_divides_m : 3 ∣ m := by
    obtain ⟨d, hd₁, hd₂, hd₃⟩ : ∃ d, d ∣ m ∧ 2 < d ∧ d < 4 :=
      hlock.fst 2 4 (by norm_num) (by norm_num) (by
      exact dvd_pow_self _ ( by linarith )) (by
      exact dvd_trans ( by decide ) ( pow_dvd_pow _ hk )) (by norm_num)
    generalize_proofs at *
    grind +splitIndPred
  generalize_proofs at *
  exact interlock_false_consec_m hlock (by norm_num) (by norm_num) (by norm_num) h_two_divides_m h_three_divides_m (by
  grind)

/-- No power of 2 lies strictly between a and b when 2^i < a and b < 2^(i+1). -/
lemma no_pow_two_between {k i a b : ℕ} (ha : 2^i < a) (hb : b < 2^(i+1))
    (d : ℕ) (hd : d ∣ 2^k) (hda : a < d) (hdb : d < b) : False := by
  obtain ⟨j, hj⟩ : ∃ j, d = 2^j := by
    rw [ Nat.dvd_prime_pow ] at hd <;> norm_num at * ; tauto
  linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( show j ≥ i + 1 by exact Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => by linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) h ] ) ), pow_succ' 2 i ]

/-
If m has two divisors a < b in (2^i, 2^{i+1}) and interlocks with 2^k, contradiction.
-/
lemma two_divs_in_interval_false {m k i : ℕ} {a b : ℕ}
    (ha_m : a ∣ m) (hb_m : b ∣ m) (ha1 : 1 < a) (hab : a < b)
    (hai : 2^i < a) (hbi : b < 2^(i+1))
    (hlock : Interlock m (2^k)) : False := by
  -- By the interlock condition, there must be a divisor $d$ of $2^k$ such that $a < d < b$.
  obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := hlock.snd a b ha1 ( by linarith ) ha_m hb_m hab;
  exact no_pow_two_between hai hbi d hd₁ hd₂ hd₃

/-
3 | m when m and 2^k interlock and m is odd, k > 2.
-/
lemma three_dvd_of_interlock {m k : ℕ} (_hm : 0 < m) (hk : 2 < k)
    (hlock : Interlock m (2^k)) (_hodd_m : ¬ 2 ∣ m) : 3 ∣ m := by
  -- From the interlock condition, between 2 and 4 (consecutive divisors > 1 of 2^k), there must be a divisor of m.
  obtain ⟨d, hd⟩ : ∃ d, d ∣ m ∧ 2 < d ∧ d < 4 :=
    hlock.fst 2 4 ( by decide ) ( by decide ) ( dvd_pow_self _ ( by linarith ) ) ( dvd_trans ( by decide ) ( pow_dvd_pow _ hk ) ) ( by norm_num );
  rcases hd with ⟨ hd₁, hd₂, hd₃ ⟩ ; interval_cases d ; simp_all +decide ;

/-
5 | m or 7 | m when m and 2^k interlock and m is odd, k > 2.
-/
lemma five_or_seven_dvd_of_interlock {m k : ℕ} (_hm : 0 < m) (hk : 2 < k)
    (hlock : Interlock m (2^k)) (_hodd_m : ¬ 2 ∣ m) : 5 ∣ m ∨ 7 ∣ m := by
  -- From the interlock, between 4 and 8 (consecutive divisors > 1 of 2^k), there must be a divisor d of m with 4 < d < 8.
  obtain ⟨d, hd⟩ : ∃ d, d ∣ m ∧ 4 < d ∧ d < 8 :=
    hlock.fst 4 8 (by norm_num) (by norm_num) ( dvd_trans ( by decide ) ( pow_dvd_pow _ hk ) )
      ( dvd_trans ( by decide ) ( pow_dvd_pow _ hk ) ) (by norm_num);
  rcases hd with ⟨ hd₁, hd₂, hd₃ ⟩ ; interval_cases d <;> simp_all +decide;
  omega

/-
If m and 2^k interlock, m is odd, and τ(m) is odd, contradiction.
-/
lemma not_interlock_odd_tau {m k : ℕ} (hm : 0 < m) (hk : 2 < k)
    (hlock : Interlock m (2^k)) (hodd_m : ¬ 2 ∣ m)
    (hodd_tau : ¬ 2 ∣ m.divisors.card) : False := by
  -- Use three_dvd_of_interlock to get 3 | m. Then sq_dvd_of_odd_card_divisors to get 9 | m.
  have three_dvd : 3 ∣ m := by
    exact three_dvd_of_interlock hm hk hlock hodd_m
  have nine_dvd : 9 ∣ m := by
    exact sq_dvd_of_odd_card_divisors hm.ne' ( by norm_num ) three_dvd hodd_tau;
  -- Use five_or_seven_dvd_of_interlock to get 5 | m or 7 | m.
  obtain five_dvd | seven_dvd : 5 ∣ m ∨ 7 ∣ m := by
    apply five_or_seven_dvd_of_interlock hm hk hlock hodd_m;
  · -- Then 9 | m and 15 = 3*5 | m.
    have fifteen_dvd : 15 ∣ m := by
      exact Nat.lcm_dvd three_dvd five_dvd;
    -- Apply two_divs_in_interval_false with a = 9, b = 15, i = 3 (since 2^3 = 8 < 9 < 15 < 16 = 2^4).
    have := two_divs_in_interval_false (by
    assumption : 9 ∣ m) (by
    assumption : 15 ∣ m) (by
    decide +revert : 1 < 9) (by
    decide +revert : 9 < 15) (by
    decide +revert : 2^3 < 9) (by
    decide +revert : 15 < 2^(3+1)) hlock;
    aesop;
  · -- Then 49 | m and 63 = 9*7 | m.
    have forty_nine_dvd : 49 ∣ m := by
      exact sq_dvd_of_odd_card_divisors hm.ne' ( by norm_num ) seven_dvd hodd_tau
    have sixty_three_dvd : 63 ∣ m := by
      exact Nat.lcm_dvd nine_dvd seven_dvd;
    -- Apply two_divs_in_interval_false with a = 49, b = 63, i = 5 (since 2^5 = 32 < 49 < 63 < 64 = 2^6).
    apply two_divs_in_interval_false;
    exact forty_nine_dvd;
    exact sixty_three_dvd;
    all_goals norm_num;
    rotate_left;
    rotate_left;
    exact hlock;
    exacts [ 5, by decide, by decide ]

/-
Lower bound: m.divisors.card ≥ k when m interlocks with 2^k and m is odd.
-/
lemma tau_lower_bound {m k : ℕ} (hm : 0 < m) (hk : 2 < k)
    (hlock : Interlock m (2^k)) (hodd_m : ¬ 2 ∣ m) :
    k ≤ m.divisors.card := by
  -- For each i ∈ {1, ..., k-1}, obtain d_i ∣ m with 2^i < d_i < 2^{i+1}
  have h_divisors : ∀ i ∈ Finset.Ico 1 k, ∃ d ∈ m.divisors, 2^i < d ∧ d < 2^(i+1) := by
    intro i hi
    obtain ⟨d, hd_div_m, hd_bounds⟩ : ∃ d, d ∣ m ∧ 2^i < d ∧ d < 2^(i+1) := by
      exact hlock.fst (2^i) (2^(i+1)) (by grind +revert) (by grind)
        ( pow_dvd_pow _ ( Finset.mem_Ico.mp hi |>.2.le ) )
        ( pow_dvd_pow _ ( by linarith [ Finset.mem_Ico.mp hi ] ) )
        ( pow_lt_pow_right₀ ( by decide ) ( Nat.lt_succ_self _ ) );
    use d
    aesop;
  choose! f hf₁ hf₂ hf₃ using h_divisors;
  -- Show that these $f(i)$ are pairwise distinct.
  have h_distinct : ∀ i j, i ∈ Finset.Ico 1 k → j ∈ Finset.Ico 1 k → i ≠ j → f i ≠ f j := by
    intros i j hi hj hij h_eq
    have h_interval : i < j → f i < 2^j := by
      exact fun hij => lt_of_lt_of_le ( hf₃ i hi ) ( pow_le_pow_right₀ ( by decide ) ( Nat.succ_le_of_lt hij ) )
    have h_interval' : j < i → f j < 2^i := by
      exact fun h => lt_of_lt_of_le ( hf₃ j hj ) ( Nat.pow_le_pow_right ( by decide ) ( by linarith ) )
    by_cases h_cases : i < j;
    · linarith [ hf₂ j hj, h_interval h_cases ];
    · exact absurd ( h_interval' ( lt_of_le_of_ne ( le_of_not_gt h_cases ) hij.symm ) ) ( by linarith [ hf₂ i hi, hf₃ j hj ] );
  -- Since these $f(i)$ are pairwise distinct and lie in $m.divisors$, we have at least $k-1$ distinct elements in $m.divisors$.
  have h_card_ge_k_minus_1 : (Finset.image f (Finset.Ico 1 k)).card ≥ k - 1 := by
    rw [ Finset.card_image_of_injOn fun i hi j hj hij => by contrapose hij; exact h_distinct i j hi hj hij ] ; simp +arith +decide;
  have h_card_ge_k : (Finset.image f (Finset.Ico 1 k) ∪ {1}).card ≥ k := by
    grind;
  exact h_card_ge_k.trans ( Finset.card_mono <| Finset.union_subset ( Finset.image_subset_iff.mpr hf₁ ) <| Finset.singleton_subset_iff.mpr <| Nat.one_mem_divisors.mpr hm.ne' )

/-
Upper bound: m.divisors.card ≤ k + 1 when m interlocks with 2^k and m is odd.
-/
lemma tau_upper_bound {m k : ℕ} (hm : 0 < m) (hk : 2 < k)
    (hlock : Interlock m (2^k)) (_hodd_m : ¬ 2 ∣ m) :
    m.divisors.card ≤ k + 1 := by
  -- Let $a_1 < a_2 < \cdots < a_r$ be the divisors of $m$ greater than 1.
  set a := m.divisors.filter (1 < ·) with ha_def
  have ha_card : a.card = m.divisors.card - 1 := by
    rw [ show a = m.divisors \ { 1 } from ?_, Finset.card_sdiff ] <;> norm_num [ hm.ne' ];
    ext ( _ | _ | x ) <;> aesop;
  -- By definition of $a$, we know that every element in $a$ is a divisor of $m$ greater than 1.
  obtain ⟨f, hf⟩ : ∃ f : Fin a.card → ℕ, StrictMono f ∧ ∀ i, f i ∈ a := by
    exact ⟨ fun i => a.orderEmbOfFin rfl i, by simp +decide [ StrictMono ], fun i => a.orderEmbOfFin_mem rfl _ ⟩;
  -- By the interlock condition, between every two consecutive divisors of $m$, there is a power of 2 dividing $2^k$.
  have h_interlock : ∀ i : Fin (a.card - 1), ∃ j : ℕ, 2 ≤ j ∧ j ≤ k ∧ f ⟨i.val, by
    exact lt_of_lt_of_le i.2 ( Nat.pred_le _ )⟩ < 2^j ∧ 2^j < f ⟨i.val + 1, by
    exact Nat.lt_pred_iff.mp i.2⟩ := by
    all_goals generalize_proofs at *;
    intro i
    obtain ⟨d, hd⟩ : ∃ d, d ∣ 2^k ∧ f ⟨i.val, by
      exact lt_of_lt_of_le i.2 ( Nat.pred_le _ )⟩ < d ∧ d < f ⟨i.val + 1, by
      grind +qlia⟩ := by
      all_goals generalize_proofs at *;
      have hfi := hf.2 ⟨ i, by solve_by_elim ⟩
      have hfi1 := hf.2 ⟨ i + 1, by solve_by_elim ⟩
      simp +decide [ha_def] at hfi hfi1
      exact hlock.snd _ _ hfi.2 hfi1.2 hfi.1.1 hfi1.1.1 (hf.1.lt_iff_lt.mpr (by simp +decide));
    generalize_proofs at *;
    -- Since $d$ divides $2^k$, we have $d = 2^j$ for some $j$.
    obtain ⟨j, hj⟩ : ∃ j, d = 2^j := by
      rw [ Nat.dvd_prime_pow ] at hd <;> norm_num at * ; tauto
    generalize_proofs at *;
    refine' ⟨ j, _, _, _, _ ⟩ <;> simp_all +decide [ Nat.dvd_prime_pow ];
    contrapose! hd; interval_cases j <;> simp_all +decide ;
    · exact fun h => absurd h ( by linarith [ hf.2 ⟨ i, by linarith ⟩ ] );
    · exact fun _ _ => by linarith [ hf.2 ⟨ i, by linarith ⟩ ] ;
  generalize_proofs at *;
  choose! j hj using h_interlock;
  -- Since $j$ is strictly increasing, the values $j i$ are distinct.
  have h_distinct : Function.Injective j := by
    intros i j hij;
    have h_distinct : ∀ i j : Fin (a.card - 1), i < j → 2 ^ (‹Fin (a.card - 1) → ℕ› i) < 2 ^ (‹Fin (a.card - 1) → ℕ› j) := by
      intros i j hij;
      exact lt_of_lt_of_le ( hj i |>.2.2.2 ) ( le_of_lt ( hj j |>.2.2.1 ) |> le_trans ( hf.1.monotone ( Nat.succ_le_of_lt hij ) ) );
    exact le_antisymm ( le_of_not_gt fun hi => by have := h_distinct _ _ hi; aesop ) ( le_of_not_gt fun hj => by have := h_distinct _ _ hj; aesop );
  have := Finset.card_le_card ( show Finset.image j Finset.univ ⊆ Finset.Icc 2 k from Finset.image_subset_iff.mpr fun i _ => Finset.mem_Icc.mpr ⟨ hj i |>.1, hj i |>.2.1 ⟩ ) ; simp_all +decide [ Finset.card_image_of_injective _ h_distinct ] ;
  omega

/-- The τ-lemma specialized to n = 2^k: τ(m) ∈ {k, k+1}. -/
lemma tau_interlock_pow_two {m k : ℕ} (hm : 0 < m) (hk : 2 < k)
    (hlock : Interlock m (2^k)) (hodd_m : ¬ 2 ∣ m) :
    m.divisors.card = k ∨ m.divisors.card = k + 1 := by
  have hlb := tau_lower_bound hm hk hlock hodd_m
  have hub := tau_upper_bound hm hk hlock hodd_m
  omega

/-
If p prime, p | m, exp(p) ≥ 4, then p^4 | m.
-/
lemma pow_four_dvd_of_factorization_ge {m p : ℕ} (_hm : m ≠ 0) (_hp : p.Prime)
    (_hpm : p ∣ m) (hge : m.factorization p ≥ 4) : p ^ 4 ∣ m := by
  exact dvd_trans ( pow_dvd_pow _ hge ) ( Nat.ordProj_dvd _ _ )

/-
Given constraints on τ(m) mod 12, extract that for each prime factor,
  the exponent is ≥ 4 with at most one exception.
-/
lemma exp_ge_four_all_but_one {m : ℕ} (hm : m ≠ 0)
    (heven_tau : 2 ∣ m.divisors.card)
    (hnot4 : ¬ 4 ∣ m.divisors.card)
    (hnot3 : ¬ 3 ∣ m.divisors.card)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpm : p ∣ m) (hqm : q ∣ m) :
    m.factorization p ≥ 4 ∨ m.factorization q ≥ 4 := by
  by_cases h1 : m.factorization p ≥ 4 <;> by_cases h2 : m.factorization q ≥ 4 <;> simp_all +decide;
  -- If both $p$ and $q$ have exponents less than 4 in the factorization of $m$, then $(p+1)(q+1)$ divides $\tau(m)$.
  have h_div : (m.factorization p + 1) * (m.factorization q + 1) ∣ m.divisors.card := by
    have h_div : m.divisors.card = ∏ r ∈ m.primeFactors, (m.factorization r + 1) := by
      exact card_divisors hm;
    rw [ h_div, ← Finset.prod_sdiff ( Finset.insert_subset_iff.mpr ⟨ Nat.mem_primeFactors.mpr ⟨ hp, hpm, hm ⟩, Finset.singleton_subset_iff.mpr ( Nat.mem_primeFactors.mpr ⟨ hq, hqm, hm ⟩ ) ⟩ ) ];
    rw [ Finset.prod_pair hpq ] ; exact dvd_mul_left _ _;
  interval_cases _ : m.factorization p <;> interval_cases _ : m.factorization q <;> simp_all +decide only;
  all_goals simp_all +decide [ Nat.factorization_eq_zero_iff ];
  all_goals omega;

/-- Case a₁: if 3⁴·5 | m, contradiction via 9 and 15 in (8, 16). -/
lemma case_a1 {m k : ℕ} (hlock : Interlock m (2^k))
    (h : 3^4 * 5 ∣ m) : False := by
  exact two_divs_in_interval_false (show 9 ∣ m from dvd_trans (by norm_num) h)
    (show 15 ∣ m from dvd_trans (by norm_num) h) (by norm_num) (by norm_num)
    (show 2^3 < 9 from by norm_num) (show 15 < 2^(3+1) from by norm_num) hlock

/-- Case a₂: if 3⁴·7 | m, contradiction via 21 and 27 in (16, 32). -/
lemma case_a2 {m k : ℕ} (hlock : Interlock m (2^k))
    (h : 3^4 * 7 ∣ m) : False := by
  exact two_divs_in_interval_false (show 21 ∣ m from dvd_trans (by norm_num) h)
    (show 27 ∣ m from dvd_trans (by norm_num) h) (by norm_num) (by norm_num)
    (show 2^4 < 21 from by norm_num) (show 27 < 2^(4+1) from by norm_num) hlock

/-- Case a₃: if 3·5⁴ | m, contradiction via 75 and 125 in (64, 128). -/
lemma case_a3 {m k : ℕ} (hlock : Interlock m (2^k))
    (h : 3 * 5^4 ∣ m) : False := by
  exact two_divs_in_interval_false (show 75 ∣ m from dvd_trans (by norm_num) h)
    (show 125 ∣ m from dvd_trans (by norm_num) h) (by norm_num) (by norm_num)
    (show 2^6 < 75 from by norm_num) (show 125 < 2^(6+1) from by norm_num) hlock

/-- Case a₄: if 3·7⁴ | m and m interlocks with 2^k, contradiction. -/
lemma case_a4 {m k : ℕ} (hm : 0 < m) (hk : 2 < k)
    (hlock : Interlock m (2^k)) (hodd_m : ¬ 2 ∣ m)
    (h3 : 3 ∣ m) (h74 : 7^4 ∣ m) : False := by
  -- First establish k ≥ 9 using the τ upper bound
  have h3_74 : 3 * 7 ^ 4 ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h74
  have h_div_sub : (3 * 7 ^ 4).divisors ⊆ m.divisors :=
    Nat.divisors_subset_of_dvd hm.ne' h3_74
  have h_card_ge : (3 * 7 ^ 4).divisors.card ≤ m.divisors.card :=
    Finset.card_le_card h_div_sub
  have h_card_7203 : (3 * 7 ^ 4).divisors.card = 10 := by
      rw [(show Nat.Coprime 3 (7^4) from by norm_num).card_divisors_mul,
        show (3:ℕ) = 3^1 from by norm_num, Nat.divisors_prime_pow (by norm_num : Nat.Prime 3),
        Nat.divisors_prime_pow (by norm_num : Nat.Prime 7)]; simp
  have hub := tau_upper_bound hm hk hlock hodd_m
  have hk9 : k ≥ 9 := by omega
  -- Get a divisor of m in (8, 16)
  have h49 : 49 ∣ m := dvd_trans (by norm_num : 49 ∣ 7 ^ 4) h74
  have h7 : 7 ∣ m := dvd_trans (by norm_num : 7 ∣ 7 ^ 4) h74
  obtain ⟨d, hd_m, hd_lb, hd_ub⟩ : ∃ d, d ∣ m ∧ 8 < d ∧ d < 16 :=
    hlock.fst 8 16 ( by decide ) ( by decide ) ( dvd_trans ( by decide ) ( pow_dvd_pow _ hk9 ) )
      ( dvd_trans ( by decide ) ( pow_dvd_pow _ hk9 ) ) ( by decide );
  -- d is odd and in {9, 11, 13, 15}
  have hd_odd : ¬ 2 ∣ d := fun h => hodd_m (dvd_trans h hd_m)
  interval_cases d <;> simp_all <;> (
    first
    | (-- d = 9: 49 and 63 = 9*7 in (32, 64)
       exact @two_divs_in_interval_false m k 5 49 63 h49
         (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd_m h7)
         (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlock)
    | (-- d = 11: 33 = 3*11 and 49 in (32, 64)
       exact @two_divs_in_interval_false m k 5 33 49
         (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 hd_m)
         h49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlock)
    | (-- d = 13: 39 = 3*13 and 49 in (32, 64)
       exact @two_divs_in_interval_false m k 5 39 49
         (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 hd_m)
         h49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlock)
    | (-- d = 15: 5 | m and 7 | m, both in (4, 8)
       have h5 : 5 ∣ m := dvd_trans (by norm_num : 5 ∣ 15) hd_m
       exact @two_divs_in_interval_false m k 2 5 7 h5 h7
         (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlock))

/-
If m and 2^k interlock, m is odd, τ(m) even, k ≡ 1,2,9,10 mod 12, contradiction.
-/
lemma not_interlock_even_tau {m k : ℕ} (hm : 0 < m) (hk : 2 < k)
    (hlock : Interlock m (2^k)) (hodd_m : ¬ 2 ∣ m)
    (heven_tau : 2 ∣ m.divisors.card)
    (hmod : k % 12 = 1 ∨ k % 12 = 2 ∨ k % 12 = 9 ∨ k % 12 = 10) : False := by
  -- By tau_interlock_pow_two: m.divisors.card = k or k+1.
  have hcard : m.divisors.card = k ∨ m.divisors.card = k + 1 := by
    exact tau_interlock_pow_two hm hk hlock hodd_m;
  -- Get 3 ∣ m and (5 ∣ m ∨ 7 ∣ m).
  have h3 : 3 ∣ m := by
    exact three_dvd_of_interlock hm hk hlock hodd_m
  have h5_or_7 : 5 ∣ m ∨ 7 ∣ m := by
    exact five_or_seven_dvd_of_interlock hm hk hlock hodd_m;
  -- By exp_ge_four_all_but_one with p=3, q=5 or p=3, q=7: factorization 3 ≥ 4 or factorization 5 ≥ 4 or factorization 7 ≥ 4.
  have h_exp_ge_four : m.factorization 3 ≥ 4 ∨ m.factorization 5 ≥ 4 ∨ m.factorization 7 ≥ 4 := by
    have hnot4 : ¬(4 ∣ m.divisors.card) := by
      omega
    have hnot3 : ¬(3 ∣ m.divisors.card) := by
      omega;
    rcases h5_or_7 with ( h5 | h7 );
    · have := exp_ge_four_all_but_one ( show m ≠ 0 by linarith ) heven_tau hnot4 hnot3 3 5 ( by decide ) ( by decide ) ( by decide ) h3 h5; aesop;
    · have := exp_ge_four_all_but_one hm.ne' heven_tau hnot4 hnot3 3 7 ( by norm_num ) ( by norm_num ) ( by norm_num ) h3 h7; aesop;
  rcases h_exp_ge_four with ( h | h | h );
  · -- If fact(3) ≥ 4: by pow_four_dvd_of_factorization_ge, 3^4 ∣ m. Then 3^4 * 5 ∣ m (coprime). Apply case_a1.
    have h34 : 3^4 ∣ m := by
      exact dvd_trans ( pow_dvd_pow _ h ) ( Nat.ordProj_dvd _ _ );
    rcases h5_or_7 with ( h5 | h7 );
    · exact case_a1 hlock ( Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by decide ) h34 h5 );
    · exact case_a2 hlock ( Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by decide ) h34 h7 );
  · -- If fact(5) ≥ 4: 5^4 ∣ m. Then 3 * 5^4 ∣ m (coprime). Apply case_a3.
    have h54 : 5^4 ∣ m := by
      exact dvd_trans ( pow_dvd_pow _ h ) ( Nat.ordProj_dvd _ _ )
    have h354 : 3 * 5^4 ∣ m := by
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by decide ) h3 h54
    exact case_a3 hlock h354;
  · exact case_a4 hm hk hlock hodd_m h3 ( pow_four_dvd_of_factorization_ge hm.ne' ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( Nat.mod_eq_zero_of_dvd ( by contrapose! h; simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ) ) ) h )

/-- Result 1: For k > 2 with k ≡ 1,2,9,10 (mod 12), 2^k is not separable. -/
theorem positive_density_not_separable {k : ℕ} (hk : 2 < k)
    (hmod : k % 12 = 1 ∨ k % 12 = 2 ∨ k % 12 = 9 ∨ k % 12 = 10) :
    ¬ Separable (2 ^ k) := by
  intro ⟨m, hm_pos, hlock⟩
  have hodd_m := interlock_pow_two_odd hm_pos hk hlock
  by_cases hτ : 2 ∣ m.divisors.card
  · exact not_interlock_even_tau hm_pos hk hlock hodd_m hτ hmod
  · exact not_interlock_odd_tau hm_pos hk hlock hodd_m hτ

/-- Result 2: There exists a δ > 0 such that for all N,
  the number of k ∈ {1,...,N} with 2^k separable is at least δN. -/
theorem positive_density_separable :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ,
      δ * N ≤ Set.ncard {k : ℕ | 1 ≤ k ∧ k ≤ N ∧ Separable (2 ^ k)} := by
  obtain ⟨T, hT, hdens⟩ := dense_multiples_separable
  refine ⟨(3 * T : ℝ)⁻¹, by positivity, fun N => ?_⟩
  have hNat :
      N ≤ (3 * T) *
        Set.ncard {k : ℕ | 1 ≤ k ∧ k ≤ N ∧ Separable (2 ^ k)} := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    -- ncard of separable set ≥ 1 (since 2^1 is separable)
    have hS_fin : Set.Finite {k : ℕ | 1 ≤ k ∧ k ≤ N ∧ Separable (2 ^ k)} :=
      Set.Finite.subset (Set.finite_Icc 1 N)
        (fun k ⟨h1, h2, _⟩ => Set.mem_Icc.mpr ⟨h1, h2⟩)
    have hcard1 : 1 ≤ Set.ncard {k : ℕ | 1 ≤ k ∧ k ≤ N ∧ Separable (2 ^ k)} :=
      (Set.ncard_pos hS_fin).mpr ⟨1, le_refl 1, hN, separable_two⟩
    -- ncard of separable set ≥ ncard of multiples set (via injection)
    have hcard_ge := ncard_separable_ge_multiples T hT N
    -- From the density lemma
    have hdens_M := hdens (N / T)
    -- Combine using nlinarith
    nlinarith [Nat.div_mul_le_self N T, Nat.mod_lt N hT, Nat.div_add_mod N T]
  have hReal :
      (N : ℝ) ≤ (3 * T : ℝ) *
        (Set.ncard {k : ℕ | 1 ≤ k ∧ k ≤ N ∧ Separable (2 ^ k)} : ℝ) := by
    exact_mod_cast hNat
  simpa [div_eq_inv_mul] using
    (div_le_iff₀' (show (0 : ℝ) < (3 * T : ℝ) by positivity)).2 hReal

/-- Result 3: If m and n interlock and m*n = primorial k, then k ≤ 8. -/
theorem interlock_primorial_le_eight (m n k : ℕ)
    (hprod : m * n = Primorial k)
    (hlock : Interlock m n) : k ≤ 8 := by
  by_contra hk
  push_neg at hk
  apply not_interlock_of_nine_primes m n
  · rw [hprod]; exact primorial_squarefree k
  all_goals (
    try (rw [hprod]; exact small_prime_dvd_primorial _ k (by norm_num) (by norm_num) (by omega)))
  exact hlock

#print axioms positive_density_not_separable
#print axioms positive_density_separable
#print axioms interlock_primorial_le_eight
