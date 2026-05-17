import Mathlib

/-!
Below you can find a conditional formalization of an approximation to the
Buchstab function, which is used in an upper bound on Erdős Problem #425
(https://www.erdosproblems.com/425). For the formalization of this upper bound,
see my GitHub

https://github.com/Woett/Lean-files/blob/main/ErdosProblem425Upper.lean

Both the linked formalization as well as this one make use of two estimates on
the distribution of prime numbers by Dusart that can be found at the start of
the file.

Dusart, P. Explicit estimates of some functions over primes. Ramanujan J. 45,
227–251 (2018).

Lean version: leanprover/lean4:v4.28.0
-/

open scoped BigOperators Real Nat Classical Pointwise
open Real Finset

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

/-! ## Definitions -/

/-- The set of natural number primes ≤ x. -/
def primesUpTo (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime

/-- Φ(x, y) = #{m ∈ ℕ : 1 ≤ m ≤ x, P⁻(m) ≥ y}, i.e. the count of integers up to x
    whose smallest prime factor is ≥ y. -/
def sievePhi (x : ℕ) (y : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun m => ∀ p ∈ m.primeFactors, y ≤ p)).card

/-- For x ≥ 88789, π(x) ≥ x/log x + x/log²x + 2x/log³x. -/
axiom dusart_pi_lower (x : ℝ) (hx : x ≥ 88789) :
    x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 ≤
      ((primesUpTo x).card : ℝ)

/-- For x > 1, π(x) ≤ x/log x + x/log²x + 2.53816·x/log³x. -/
axiom dusart_pi_upper (x : ℝ) (hx : x > 1) :
    ((primesUpTo x).card : ℝ) ≤
      x / Real.log x + x / Real.log x ^ 2 + 2.53816 * x / Real.log x ^ 3

/-! ## Prime counting bounds -/

/-
log(88789) > 11.39, so for t ≥ 88789 we have log t ≥ 3.
-/
lemma log_ge_three_of_ge (t : ℝ) (ht : t ≥ 88789) : Real.log t ≥ 3 := by
  rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ];
  exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 3:ℝ ) = 1+1+1 by norm_num, Real.exp_add, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ] ) ht

/-
For t ≥ 88789, |π(t) - t/log t| ≤ 2 * t / (log t)².
-/
lemma pi_error_simple (t : ℝ) (ht : t ≥ 88789) :
    |((primesUpTo t).card : ℝ) - t / Real.log t| ≤ 2 * t / (Real.log t) ^ 2 := by
  refine' abs_sub_le_iff.mpr _;
  constructor;
  · -- Applying the upper bound from Dusart's theorem.
    have h_upper : ((primesUpTo t).card : ℝ) ≤ t / Real.log t + t / Real.log t ^ 2 + 2.53816 * t / Real.log t ^ 3 := by
      exact dusart_pi_upper t ( by linarith );
    refine le_trans ( sub_le_sub_right h_upper _ ) ?_;
    ring_nf;
    nlinarith [ show 0 < t * ( Real.log t ) ⁻¹ ^ 2 by exact mul_pos ( by positivity ) ( sq_pos_of_pos ( inv_pos.mpr ( Real.log_pos ( by linarith ) ) ) ), show ( Real.log t ) ⁻¹ ≤ 1 / 3 by rw [ inv_le_comm₀ ] <;> norm_num <;> linarith [ log_ge_three_of_ge t ht ] ];
  · have := dusart_pi_lower t ( by linarith );
    ring_nf at *;
    nlinarith [ show 0 < t * ( Real.log t ) ⁻¹ ^ 3 by exact mul_pos ( by positivity ) ( pow_pos ( inv_pos.mpr ( Real.log_pos ( by linarith ) ) ) _ ) ]

/-
For t ≥ 88789, π(t) ≤ 2 * t / log t.
-/
lemma pi_upper_simple (t : ℝ) (ht : t ≥ 88789) :
    ((primesUpTo t).card : ℝ) ≤ 2 * t / Real.log t := by
  -- By dusart_pi_upper, π(t) ≤ t/L + t/L² + 2.53816*t/L³ where L = log t ≥ 3.
  have h_upper : (primesUpTo t).card ≤ t / Real.log t + t / (Real.log t) ^ 2 + 2.53816 * t / (Real.log t) ^ 3 := by
    convert dusart_pi_upper t ( by linarith ) using 1;
  refine le_trans h_upper ?_;
  -- We'll use that $L \geq 3$ to simplify the expression.
  have h_log_ge_three : Real.log t ≥ 3 := by
    exact log_ge_three_of_ge t ht;
  field_simp;
  norm_num; nlinarith
lemma abel_summation (f g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, f k * g k =
      (∑ k ∈ Finset.Icc a b, f k) * g b -
      ∑ k ∈ Finset.Ico a b, (∑ j ∈ Finset.Icc a k, f j) * (g (k + 1) - g k) := by
  induction' b with b ih;
  · aesop;
  · cases hab.eq_or_lt <;> simp_all +decide [ (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc), (Nat.succ_eq_succ ▸ Finset.Ico_succ_right_eq_Icc) ] ; ring_nf;
    erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] at * <;> norm_num at *;
    · erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] at *;
      · simp_all +decide [ add_comm 1, Finset.sum_range_succ ];
        erw [ Finset.sum_Ico_eq_sub _ _ ] at *;
        · simp_all +decide [ Finset.sum_range_succ, mul_sub ] ; linarith;
        · linarith;
      · linarith;
      · linarith;
      · linarith;
    · linarith;
    · linarith;
    · linarith;
    · grind

/-! ## Helper lemmas -/

/-! ### Primes in range equals difference of primesUpTo -/

/-
The count of primes in [Z, N] for naturals Z, N equals π(N) - π(Z-1) when Z ≥ 2.
-/
lemma primes_Icc_eq_diff (Z N : ℕ) (hZ : Z ≥ 2) (hZN : Z ≤ N) :
    ((Finset.Icc Z N).filter Nat.Prime).card =
      (primesUpTo (N : ℝ)).card - (primesUpTo ((Z : ℝ) - 1)).card := by
  rw [ tsub_eq_of_eq_add ];
  rw [ ← Finset.card_union_of_disjoint ];
  · congr with x ; norm_num [ primesUpTo ];
    grind;
  · norm_num [ Finset.disjoint_left, primesUpTo ];
    intros; omega;

lemma primesUpTo_diff_le_one (Z : ℕ) (hZ : Z ≥ 1) :
    (primesUpTo (Z : ℝ)).card ≤ (primesUpTo ((Z : ℝ) - 1)).card + 1 := by
  simp only [primesUpTo]
  rw [show ⌊(Z : ℝ) - 1⌋₊ = Z - 1 from by
    rw [show (Z : ℝ) - 1 = ((Z - 1 : ℕ) : ℝ) from by rw [Nat.cast_sub hZ]; push_cast; ring]
    exact Nat.floor_natCast _]
  rw [show ⌊(Z : ℝ)⌋₊ = Z from Nat.floor_natCast _]
  have hZeq : Z + 1 = (Z - 1 + 1) + 1 := by omega
  rw [hZeq, Finset.range_add_one, Finset.filter_insert]
  split
  · exact Finset.card_insert_le _ _
  · omega

lemma pi_Zm1_error (Z : ℕ) (hZ : Z ≥ 88789) :
    |((primesUpTo ((Z : ℝ) - 1)).card : ℝ) - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1)| ≤
      3 * ((Z : ℝ) - 1) / (Real.log ((Z : ℝ) - 1)) ^ 2 := by
  by_cases hZ88789 : Z = 88789
  · subst hZ88789
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
    · have := dusart_pi_upper 88788 (by norm_num)
      have h_log_bound : Real.log 88788 > 11 := by
        norm_num [Real.lt_log_iff_exp_lt]
        have := Real.exp_one_lt_d9.le; norm_num1 at *
        rw [show Real.exp 11 = (Real.exp 1) ^ 11 by rw [← Real.exp_nat_mul]; norm_num]
        exact lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) this _) (by norm_num)
      ring_nf at *
      nlinarith [inv_pos.mpr (Real.log_pos (show 88788 > 1 by norm_num)),
                 mul_inv_cancel₀ (ne_of_gt (Real.log_pos (show 88788 > 1 by norm_num))),
                 pow_pos (inv_pos.mpr (Real.log_pos (show 88788 > 1 by norm_num))) 3]
    · have h_diff := primesUpTo_diff_le_one 88789 (by norm_num)
      have h_dusart := dusart_pi_lower 88789 (by norm_num)
      have h_pi_lower : 88789 / Real.log 88789 + 88789 / (Real.log 88789) ^ 2 +
          2 * 88789 / (Real.log 88789) ^ 3 - 1 ≤ ((primesUpTo (88788 : ℝ)).card : ℝ) := by
        have : ((primesUpTo (88789 : ℝ)).card : ℝ) ≤ ((primesUpTo (88788 : ℝ)).card : ℝ) + 1 := by
          have := h_diff; norm_num at this; exact_mod_cast this
        linarith
      have h_log_88789_hi : Real.log (88789 : ℝ) < 12 := by
        rw [show (12 : ℝ) = Real.log (Real.exp 12) from by rw [Real.log_exp]]
        exact Real.log_lt_log (by positivity) (by
          rw [show Real.exp 12 = (Real.exp 1) ^ 12 by rw [← Real.exp_nat_mul]; norm_num]
          have h3 : Real.exp 1 > 2.7 := Real.exp_one_gt_d9.trans' (by norm_num)
          have h4 : (Real.exp 1) ^ 2 > 7.29 := by nlinarith [sq_nonneg (Real.exp 1 - 2.7)]
          have h6 : (Real.exp 1) ^ 4 > 53.14 := by nlinarith [sq_nonneg ((Real.exp 1) ^ 2 - 7.29)]
          have h8 : (Real.exp 1) ^ 8 > 2823 := by nlinarith [sq_nonneg ((Real.exp 1) ^ 4 - 53.14)]
          nlinarith [sq_nonneg ((Real.exp 1) ^ 6 - 387)])
      have h_log_88789_lo : Real.log (88789 : ℝ) > 11 := by
        norm_num [Real.lt_log_iff_exp_lt]
        have := Real.exp_one_lt_d9.le; norm_num1 at *
        rw [show Real.exp 11 = (Real.exp 1) ^ 11 by rw [← Real.exp_nat_mul]; norm_num]
        exact lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) this _) (by norm_num)
      have h_log_88788 : Real.log (88788 : ℝ) > 11 := by
        norm_num [Real.lt_log_iff_exp_lt]
        have := Real.exp_one_lt_d9.le; norm_num1 at *
        rw [show Real.exp 11 = (Real.exp 1) ^ 11 by rw [← Real.exp_nat_mul]; norm_num]
        exact lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) this _) (by norm_num)
      norm_num
      have hL1_inv_lo : (Real.log (88789 : ℝ))⁻¹ > 1/12 := by
        rw [one_div]; exact (inv_lt_inv₀ (by positivity) (by linarith)).mpr h_log_88789_hi
      have hL2_inv_hi : (Real.log (88788 : ℝ))⁻¹ < 1/11 := by
        rw [one_div]; exact (inv_lt_inv₀ (by positivity) (by linarith)).mpr h_log_88788
      ring_nf at *
      nlinarith [sq_nonneg ((Real.log (88789 : ℝ))⁻¹ - 1/12),
                 sq_nonneg ((Real.log (88788 : ℝ))⁻¹ - 1/12),
                 sq_nonneg (Real.log (88789 : ℝ))⁻¹,
                 sq_nonneg (Real.log (88788 : ℝ))⁻¹,
                 inv_pos.mpr (Real.log_pos (show (88789 : ℝ) > 1 by norm_num)),
                 inv_pos.mpr (Real.log_pos (show (88788 : ℝ) > 1 by norm_num))]
  · have := pi_error_simple (Z - 1 : ℝ) ?_
    · grind
    · exact le_tsub_of_add_le_left (mod_cast lt_of_le_of_ne hZ (Ne.symm hZ88789))

/-
The error bound 3(Z-1)/(log(Z-1))² ≤ 18N/(log N)² when Z² ≤ N and Z ≥ 88789.
-/
lemma pi_Zm1_error_transfer (N Z : ℕ) (hZ : Z ≥ 88789) (hNZ : Z ^ 2 ≤ N) :
    3 * ((Z : ℝ) - 1) / (Real.log ((Z : ℝ) - 1)) ^ 2 ≤ 18 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
  -- Using the fact that the function $f(x) = \frac{x}{(\log x)^2}$ is increasing for $x \geq 88788$, we can conclude that $\frac{Z-1}{(\log(Z-1))^2} \leq \frac{N}{(\log N)^2}$.
  have h_inc : (Z - 1 : ℝ) / (Real.log (Z - 1))^2 ≤ (N : ℝ) / (Real.log N)^2 := by
    -- Since $f(x) = \frac{x}{(\log x)^2}$ is increasing for $x \geq e^2$, and $Z-1 \geq 88788 > e^2$, we have $f(Z-1) \leq f(N)$.
    have h_inc : ∀ x y : ℝ, Real.exp 2 ≤ x → x ≤ y → x / (Real.log x)^2 ≤ y / (Real.log y)^2 := by
      -- Let's calculate the derivative of $f(x) = \frac{x}{(\log x)^2}$ and show it is positive for $x \geq e^2$.
      have h_deriv_pos : ∀ x : ℝ, Real.exp 2 < x → 0 < deriv (fun x => x / (Real.log x)^2) x := by
        intro x hx;
        norm_num [ show x ≠ 0 by linarith [ Real.exp_pos 2 ], show Real.log x ≠ 0 by exact ne_of_gt <| Real.log_pos <| lt_trans ( by norm_num ) hx ];
        exact div_pos ( by nlinarith [ Real.add_one_le_exp 2, mul_inv_cancel₀ ( by linarith [ Real.exp_pos 2 ] : x ≠ 0 ), Real.log_exp 2, Real.log_lt_log ( by positivity ) hx ] ) ( sq_pos_of_pos ( sq_pos_of_pos ( Real.log_pos ( by linarith [ Real.add_one_le_exp 2 ] ) ) ) );
      intro x y hx hy; cases eq_or_lt_of_le hy <;> cases eq_or_lt_of_le hx <;> ( ( contrapose! h_deriv_pos ) );
      · aesop;
      · aesop;
      · have := exists_deriv_eq_slope ( f := fun x => x / Real.log x ^ 2 ) ‹x < y›;
        exact this ( continuousOn_of_forall_continuousAt fun z hz => DifferentiableAt.continuousAt <| by exact DifferentiableAt.div ( differentiableAt_id ) ( DifferentiableAt.pow ( Real.differentiableAt_log <| by linarith [ hz.1, Real.exp_pos 2 ] ) _ ) <| ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by linarith [ hz.1, Real.add_one_le_exp 2 ] ) ( fun z hz => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.div ( differentiableAt_id ) ( DifferentiableAt.pow ( Real.differentiableAt_log <| by linarith [ hz.1, Real.exp_pos 2 ] ) _ ) <| ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by linarith [ hz.1, Real.add_one_le_exp 2 ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, by linarith [ hc₁.1, Real.add_one_le_exp 2 ], by rw [ hc₂ ] ; exact div_nonpos_of_nonpos_of_nonneg ( sub_nonpos_of_le <| le_of_lt h_deriv_pos ) <| by linarith ⟩;
      · have := exists_deriv_eq_slope ( f := fun x => x / Real.log x ^ 2 ) ‹x < y›;
        exact this ( continuousOn_of_forall_continuousAt fun z hz => DifferentiableAt.continuousAt <| by exact DifferentiableAt.div ( differentiableAt_id ) ( DifferentiableAt.pow ( Real.differentiableAt_log <| by linarith [ hz.1, Real.exp_pos 2 ] ) _ ) <| ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by linarith [ hz.1, Real.add_one_le_exp 2 ] ) ( fun z hz => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.div ( differentiableAt_id ) ( DifferentiableAt.pow ( Real.differentiableAt_log <| by linarith [ hz.1, Real.exp_pos 2 ] ) _ ) <| ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by linarith [ hz.1, Real.add_one_le_exp 2 ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, by linarith [ hc₁.1 ], by rw [ hc₂ ] ; exact div_nonpos_of_nonpos_of_nonneg ( sub_nonpos_of_le <| le_of_lt h_deriv_pos ) <| sub_nonneg_of_le <| by linarith ⟩;
    exact h_inc _ _ ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 2:ℝ ) = 1+1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1, ( by norm_cast : ( 88789:ℝ ) ≤ Z ) ] ) ( by nlinarith [ ( by norm_cast : ( Z:ℝ ) ^ 2 ≤ N ), ( by norm_cast : ( 88789:ℝ ) ≤ Z ) ] );
  ring_nf at *; nlinarith;

/-
Antiderivative identity for the weighted sum
-/
lemma antiderivative_eval (N Z : ℕ) (hZ : Z ≥ 3) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3) :
    let T := Real.log (N : ℝ)
    (1 / T) * (Real.log (T / 2) - Real.log (T - Real.log (N : ℝ) / 2)
      - Real.log (Real.log (Z : ℝ)) + Real.log (T - Real.log (Z : ℝ))) =
    Real.log (T / Real.log (Z : ℝ) - 1) / T := by
  by_cases h : Real.log Z = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_comm ];
  · rcases h with ( rfl | rfl | h ) <;> norm_cast at *;
  · rw [ ← Real.log_div, ← Real.log_div ] <;> ring_nf <;> norm_num;
    · rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; nlinarith ) ) ), one_mul ];
      rw [ ← Real.log_mul ] <;> ring_nf <;> norm_num;
      · exact Or.inl ( by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith ) ) ) ] );
      · tauto;
      · exact sub_ne_zero_of_ne ( ne_of_gt ( Real.log_lt_log ( by norm_cast; linarith ) ( by norm_cast; nlinarith ) ) );
    · exact ⟨ by nlinarith, by nlinarith, by linarith ⟩;
    · tauto;
    · exact ⟨ by nlinarith, by nlinarith, by linarith ⟩;
    · exact ⟨ by nlinarith, by nlinarith, by linarith ⟩

/-
When Z > √N and N ≥ 1, sievePhi(N, Z) = 1 + #{primes in [Z, N]}.
-/
lemma sievePhi_no_semiprimes (N Z : ℕ) (_hZ : Z ≥ 2) (hN : N ≥ 1) (hZsq : N < Z ^ 2) :
    sievePhi N Z = 1 + ((Finset.Icc Z N).filter Nat.Prime).card := by
  -- We start by showing that the set {m ∈ [1,N] : ∀ p ∈ primeFactors(m), Z ≤ p} is equal to {1} ∪ {primes in [Z,N]}.
  have h_set_eq : ((Finset.Icc 1 N).filter (fun m => ∀ p ∈ m.primeFactors, Z ≤ p)) = {1} ∪ ((Finset.Icc Z N).filter Nat.Prime) := by
    ext m;
    constructor <;> intro hm <;> simp_all +decide ;
    · by_cases hm_prime : Nat.Prime m;
      · exact Or.inr ⟨ hm.2 m hm_prime ( dvd_refl m ) ( by linarith ), hm_prime ⟩;
      · by_cases hm_one : m = 1;
        · exact Or.inl hm_one;
        · -- Since $m$ is not prime and not equal to 1, it must have at least two prime factors.
          obtain ⟨p, hp_prime, hp_div⟩ : ∃ p, Nat.Prime p ∧ p ∣ m := by
            exact Nat.exists_prime_and_dvd hm_one;
          obtain ⟨ q, hq ⟩ := hp_div;
          rcases p with ( _ | _ | p ) <;> rcases q with ( _ | _ | q ) <;> simp_all +decide;
          nlinarith only [ hm.1.2, hZsq, hm.2 _ hp_prime ( dvd_mul_right _ _ ), hm.2 _ ( Nat.minFac_prime ( by aesop ) ) ( Nat.minFac_dvd _ ), Nat.minFac_le_of_dvd ( by linarith ) ( dvd_mul_right ( p + 1 + 1 ) ( q + 1 + 1 ) ), Nat.minFac_le_of_dvd ( by linarith ) ( dvd_mul_left ( q + 1 + 1 ) ( p + 1 + 1 ) ) ];
    · rcases hm with ( rfl | ⟨ ⟨ hm₁, hm₂ ⟩, hm₃ ⟩ ) <;> simp_all +decide [ Nat.dvd_prime ];
      · aesop;
      · exact ⟨ hm₃.pos, by rintro p pp ( rfl | rfl ) <;> aesop ⟩;
  convert congr_arg Finset.card h_set_eq using 1;
  rw [ Finset.card_union_of_disjoint ] <;> norm_num

/-
Integral evaluation via FTC
-/
lemma integral_weighted_reciprocal (N Z : ℕ)
    (hZ : Z ≥ 3) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3) :
    ∫ t in (Z : ℝ)..(Real.sqrt N), 1 / (t * Real.log t * (Real.log N - Real.log t)) =
      Real.log (Real.log N / Real.log Z - 1) / Real.log N := by
  have h_integral_eval : ∀ a b : ℝ, 3 ≤ a → a ≤ b → b ≤ Real.sqrt N → ∫ t in a..b, 1 / (t * Real.log t * (Real.log N - Real.log t)) = (1 / Real.log N) * (Real.log (Real.log b) - Real.log (Real.log N - Real.log b)) - (1 / Real.log N) * (Real.log (Real.log a) - Real.log (Real.log N - Real.log a)) := by
    intros a b _ _ _; rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    · intro x hx; convert HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.sub ( HasDerivAt.log ( Real.hasDerivAt_log ( show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith ) ) ( ne_of_gt ( Real.log_pos ( show x > 1 by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) ) ( HasDerivAt.log ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_log ( show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) ( ne_of_gt ( sub_pos.mpr ( show Real.log x < Real.log N from Real.log_lt_log ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.mul_self_sqrt ( Nat.cast_nonneg N ), ( by norm_cast : ( 3 :ℝ ) ≤ Z ), ( by norm_cast : ( Z :ℝ ) ^ 2 ≤ N ), ( by norm_cast : ( N :ℝ ) ≤ Z ^ 3 ) ] ) ) ) ) ) ) using 1 ; ring_nf;
      field_simp;
      rw [ div_add_div ] <;> ring_nf <;> norm_num;
      · by_cases h : Real.log x = 0 <;> by_cases h' : Real.log N - Real.log x = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ];
        · rcases h with ( rfl | rfl | rfl ) <;> norm_num at *;
        · rcases h with ( rfl | rfl | rfl ) <;> norm_num at *;
        · grind;
        · field_simp;
          rw [ one_add_div ( ne_of_gt ( Real.log_pos ( by linarith ) ) ), div_div, mul_comm ] ; ring_nf;
          rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; nlinarith ) ) ), mul_one ];
      · exact ⟨ by cases Set.mem_uIcc.mp hx <;> linarith, by cases Set.mem_uIcc.mp hx <;> linarith, by cases Set.mem_uIcc.mp hx <;> linarith ⟩;
      · rw [ sub_eq_zero, eq_comm ];
        exact ne_of_lt ( Real.log_lt_log ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.mul_self_sqrt ( Nat.cast_nonneg N ), ( by norm_cast : ( 3 :ℝ ) ≤ Z ), ( by norm_cast : ( Z :ℝ ) ^ 2 ≤ N ), ( by norm_cast : ( N :ℝ ) ≤ Z ^ 3 ) ] ) );
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      refine' continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const _ _;
      · exact ContinuousAt.mul ( ContinuousAt.mul continuousAt_id ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) ) ( ContinuousAt.sub continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) );
      · simp +zetaDelta at *;
        exact ⟨ ⟨ by cases Set.mem_uIcc.mp ht <;> linarith, by cases Set.mem_uIcc.mp ht <;> linarith, by cases Set.mem_uIcc.mp ht <;> linarith ⟩, sub_ne_zero_of_ne <| ne_of_gt <| Real.log_lt_log ( by cases Set.mem_uIcc.mp ht <;> linarith ) <| by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.mul_self_sqrt <| Nat.cast_nonneg N, show ( N :ℝ ) ≥ 9 by norm_cast; nlinarith ] ⟩;
  rw [ h_integral_eval ] <;> norm_num;
  · convert antiderivative_eval N Z hZ hN_lo hN_hi using 1 ; ring_nf;
    rw [ Real.log_sqrt ( Nat.cast_nonneg _ ) ] ; ring_nf;
  · linarith;
  · exact Real.le_sqrt_of_sq_le ( mod_cast hN_lo )

/-! ### Abel summation for prime sum -/

/-
The Abel summation formula specialised to the prime sum:
    Σ_{Z≤p≤M, prime} G(p) = π_range(M)·G(M) - Σ_{k=Z}^{M-1} π_range(k)·(G(k+1)-G(k))
    where π_range(k) = #{primes in [Z,k]} and G(k) = 1/(k·log(N/k)).
-/
lemma prime_sum_abel_form (N Z : ℕ) (G : ℕ → ℝ) (hZ : Z ≤ Nat.sqrt N) :
    ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime, G p =
      ((Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime).card • G (Nat.sqrt N) -
      ∑ k ∈ Finset.Ico Z (Nat.sqrt N),
        ((Finset.Icc Z k).filter Nat.Prime).card • (G (k + 1) - G k) := by
  convert abel_summation ( fun k => if Nat.Prime k then 1 else 0 ) G Z N.sqrt hZ using 1;
  · simp +decide [ Finset.sum_ite ];
  · simp +decide

lemma sievePhi_decomp_bound (N Z : ℕ) (hZ : Z ≥ 2) (hNZ : N ≤ Z ^ 3) :
    |(sievePhi N Z : ℤ) -
      (1 + ((Finset.Icc Z N).filter Nat.Prime).card
       + ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
           ((Finset.Icc p (N / p)).filter Nat.Prime).card)| ≤ 1 := by
  refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
  · refine' le_trans ( sub_le_sub_right ( Nat.cast_le.mpr <| Finset.card_le_card _ ) _ ) _;
    exact { 1 } ∪ Finset.filter Nat.Prime ( Finset.Icc Z N ) ∪ Finset.biUnion ( Finset.filter Nat.Prime ( Finset.Icc Z ( Nat.sqrt N ) ) ) ( fun p => Finset.image ( fun q => p * q ) ( Finset.filter Nat.Prime ( Finset.Icc p ( N / p ) ) ) ) ∪ if Z.Prime ∧ N = Z ^ 3 then { N } else ∅;
    · intro m hm; by_cases hm1 : m = 1 <;> by_cases hm2 : Nat.Prime m <;> simp_all +decide ;
      · exact Or.inl ( hm.2 m hm2 ( dvd_refl m ) ( by linarith ) );
      · -- Since $m$ is not prime and not equal to 1, it must have at least two prime factors.
        obtain ⟨p, hp₁, hp₂⟩ : ∃ p, Nat.Prime p ∧ p ∣ m ∧ ∀ q, Nat.Prime q → q ∣ m → p ≤ q := by
          exact ⟨ Nat.minFac m, Nat.minFac_prime hm1, Nat.minFac_dvd m, fun q hq hqm => Nat.minFac_le_of_dvd hq.two_le hqm ⟩;
        -- Since $p$ is the smallest prime factor of $m$, we have $m = p * q$ for some integer $q$.
        obtain ⟨q, hq⟩ : ∃ q, m = p * q := hp₂.left
        have hq_ge_p : p ≤ q := by
          exact hp₂.2 _ ( Nat.minFac_prime ( by aesop ) ) ( Nat.minFac_dvd _ ) |> le_trans <| Nat.minFac_le_of_dvd ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop, by aesop ⟩ ) <| hq.symm ▸ dvd_mul_left _ _;
        have hq_le_N_div_p : q ≤ N / p := by
          rw [ Nat.le_div_iff_mul_le hp₁.pos ] ; nlinarith [ hm.1.2 ] ;
        have hq_prime : Nat.Prime q ∨ q = 1 ∨ q = p ^ 2 ∧ p = Z ∧ N = Z ^ 3 := by
          by_cases hq_prime : Nat.Prime q <;> simp_all +decide [ Nat.prime_mul_iff ];
          -- Since $q$ is not prime and $q \neq 1$, it must have a prime factor $r$ such that $r \leq \sqrt{q}$.
          obtain ⟨r, hr₁, hr₂⟩ : ∃ r, Nat.Prime r ∧ r ∣ q ∧ r ≤ Nat.sqrt q := by
            obtain ⟨ r, hr₁, hr₂ ⟩ := Nat.exists_prime_and_dvd hm2
            generalize_proofs at *; (
            obtain ⟨ s, rfl ⟩ := hr₂; simp_all +decide [ Nat.prime_mul_iff ] ;
            exact ⟨ Nat.minFac ( r * s ), Nat.minFac_prime ( by aesop ), Nat.minFac_dvd _, by rw [ Nat.le_sqrt ] ; nlinarith only [ Nat.minFac_le_of_dvd ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop, by aesop ⟩ ) ( dvd_mul_right r s ), Nat.minFac_le_of_dvd ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop, by aesop ⟩ ) ( dvd_mul_left s r ) ] ⟩)
          generalize_proofs at *; (
          -- Since $r$ is a prime factor of $q$ and $r \leq \sqrt{q}$, we have $r \leq \sqrt{N/p}$.
          have hr_le_sqrt_N_div_p : r ≤ Nat.sqrt (N / p) := by
            exact le_trans hr₂.2 ( Nat.sqrt_le_sqrt hq_le_N_div_p )
          generalize_proofs at *; (
          -- Since $r$ is a prime factor of $q$ and $r \leq \sqrt{N/p}$, we have $r \leq Z$.
          have hr_le_Z : r ≤ Z := by
            refine le_trans hr_le_sqrt_N_div_p <| Nat.le_of_lt_succ <| Nat.sqrt_lt.mpr ?_;
            rw [ Nat.div_lt_iff_lt_mul <| Nat.Prime.pos hp₁ ] ; nlinarith [ Nat.pow_le_pow_left hZ 2, hm.2 p hp₁ ( dvd_mul_right _ _ ) hp₁.ne_zero ( by aesop_cat ) ] ;
          generalize_proofs at *; (
          have := hm.2 r hr₁ ( dvd_mul_of_dvd_right hr₂.1 _ ) hp₁.ne_zero ( by aesop_cat ) ; cases this.eq_or_lt <;> first | linarith | simp_all +decide ;
          have hp_eq_r : p = r := by
            exact le_antisymm ( hp₂ r hr₁ ( dvd_mul_of_dvd_right hr₂.1 _ ) ) ( hm.2 p hp₁ ( dvd_mul_right _ _ ) hp₁.ne_zero ( by aesop_cat ) ) ▸ rfl
          generalize_proofs at *; (
          have hq_eq_p_sq : q = p ^ 2 := by
            have hq_eq_p_sq : q ≤ p ^ 2 := by
              exact hq_le_N_div_p.trans ( Nat.div_le_of_le_mul <| by subst hp_eq_r; nlinarith )
            generalize_proofs at *; (
            exact le_antisymm hq_eq_p_sq ( by nlinarith only [ hq_ge_p, hp₁.two_le, hr₂.2, Nat.sqrt_le q, hp_eq_r ] )) ;
          generalize_proofs at *; (
          simp_all +decide [ pow_succ' ];
          nlinarith [ Nat.div_mul_le_self N r ])))))
        generalize_proofs at *; (
        rcases hq_prime with ( hq_prime | rfl | ⟨ rfl, rfl, rfl ⟩ ) <;> simp_all +decide [ Nat.pow_succ' ];
        refine Or.inl ⟨ p, ⟨ ⟨ hm.2 p hp₁ ( dvd_mul_right _ _ ) hp₁.ne_zero hq_prime.ne_zero, ?_ ⟩, hp₁ ⟩, q, ⟨ ⟨ hp₂ q hq_prime ( dvd_mul_left _ _ ), hq_le_N_div_p ⟩, hq_prime ⟩, rfl ⟩;
        rw [ Nat.le_sqrt ] ; nlinarith [ hp₂ q hq_prime ( dvd_mul_left _ _ ) ]);
    · refine' le_trans ( sub_le_sub_right ( Nat.cast_le.mpr <| Finset.card_union_le _ _ ) _ ) _;
      refine' le_trans ( sub_le_sub_right ( Nat.cast_le.mpr <| add_le_add ( Finset.card_union_le _ _ ) le_rfl ) _ ) _;
      refine' le_trans ( sub_le_sub_right ( Nat.cast_le.mpr <| add_le_add_three ( Finset.card_union_le _ _ ) ( Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun p hp => Finset.card_image_le ) le_rfl ) _ ) _ ; norm_num;
      split_ifs <;> norm_num;
  · -- Let's simplify the right-hand side of the inequality.
    simp [sievePhi];
    -- Let's simplify the right-hand side of the inequality further.
    have h_simplify_rhs : ∑ x ∈ Finset.filter Nat.Prime (Finset.Icc Z (Nat.sqrt N)), (Finset.filter Nat.Prime (Finset.Icc x (N / x))).card ≤ (Finset.filter (fun m => ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ m = p * q ∧ p ≥ Z ∧ q ≥ p ∧ m ≤ N) (Finset.Icc 1 N)).card := by
      have h_simplify_rhs : Finset.filter (fun m => ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ m = p * q ∧ p ≥ Z ∧ q ≥ p ∧ m ≤ N) (Finset.Icc 1 N) ⊇ Finset.biUnion (Finset.filter Nat.Prime (Finset.Icc Z (Nat.sqrt N))) (fun p => Finset.image (fun q => p * q) (Finset.filter Nat.Prime (Finset.Icc p (N / p)))) := by
        simp +decide [ Finset.subset_iff ];
        rintro _ p hp₁ hp₂ hp₃ q hq₁ hq₂ hq₃ rfl; exact ⟨ ⟨ by nlinarith [ Nat.Prime.two_le hp₃, Nat.Prime.two_le hq₃ ], by nlinarith [ Nat.div_mul_le_self N p ] ⟩, p, hp₃, q, hq₃, hq₁, rfl, hp₁, hq₁, by nlinarith [ Nat.div_mul_le_self N p ] ⟩ ;
      refine' le_trans _ ( Finset.card_mono h_simplify_rhs );
      rw [ Finset.card_biUnion ];
      · exact Finset.sum_le_sum fun x hx => by rw [ Finset.card_image_of_injective _ fun a b h => mul_left_cancel₀ ( Nat.ne_of_gt ( Nat.Prime.pos ( by aesop ) ) ) h ] ;
      · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ] ;
        intro a x hx₁ hx₂ hx₃ hx₄ y hy₁ hy₂ hy₃ hy₄; subst_vars;
        -- Since $p$ and $q$ are distinct primes and $p \mid q * y$, it must be that $p \mid y$.
        have hp_div_y : p ∣ y := by
          exact Or.resolve_left ( hp.2.dvd_mul.mp ( hy₄.symm ▸ dvd_mul_right _ _ ) ) ( by rintro H; have := Nat.prime_dvd_prime_iff_eq hp.2 hq.2; tauto );
        rw [ Nat.prime_dvd_prime_iff_eq ] at hp_div_y <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
        exact hpq ( by nlinarith only [ hy₄, hx₁, hx₂, hy₁, hy₂, hx₃.two_le, hy₃.two_le ] );
    -- Let's simplify the right-hand side of the inequality further by considering the set of primes and semiprimes.
    have h_simplify_rhs' : (Finset.filter (fun m => ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ m = p * q ∧ p ≥ Z ∧ q ≥ p ∧ m ≤ N) (Finset.Icc 1 N)).card + (Finset.filter Nat.Prime (Finset.Icc Z N)).card ≤ (Finset.filter (fun m => ∀ p : ℕ, Nat.Prime p → p ∣ m → ¬m = 0 → Z ≤ p) (Finset.Icc 1 N)).card := by
      rw [ ← Finset.card_union_of_disjoint ];
      · refine Finset.card_mono ?_;
        intro m hm; simp_all +decide ;
        rcases hm with ( ⟨ ⟨ hm₁, hm₂ ⟩, p, hp, q, hq, hpq, rfl, hZp, hpq', hm₃ ⟩ | ⟨ ⟨ hZm, hm₂ ⟩, hm₃ ⟩ ) <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
        · intro r hr hr' hpq hrq; rw [ Nat.Prime.dvd_mul hr ] at hr'; rcases hr' with ( hr' | hr' ) <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
          grind +splitIndPred;
        · grind +revert;
      · rw [ Finset.disjoint_left ] ; simp +contextual [ Nat.prime_mul_iff ];
        exact fun a ha₁ ha₂ x hx y hy hxy ha₃ ha₄ ha₅ => ⟨ hy.ne_one, hx.ne_one ⟩;
    norm_cast ; linarith

/-! ## Ceiling/floor transfer -/
lemma primes_in_range_approx (N Z : ℕ) (hZ : Z ≥ 88789) (hNZ : Z ^ 2 ≤ N) :
    |(((Finset.Icc Z N).filter Nat.Prime).card : ℝ) -
      ((N : ℝ) / Real.log N - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))| ≤
      20 * (N : ℝ) / (Real.log N) ^ 2 := by
  have h_card_diff : |((Finset.Icc Z N).filter Nat.Prime).card - ((primesUpTo (N : ℝ)).card - (primesUpTo ((Z : ℝ) - 1)).card : ℝ)| ≤ 0 := by
    rw [ primes_Icc_eq_diff ] <;> norm_num;
    · rw [ Nat.cast_sub ];
      · ring;
      · refine' Finset.card_mono _;
        exact Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ <| Nat.floor_mono <| by nlinarith [ show ( Z : ℝ ) ≥ 88789 by norm_cast, show ( N : ℝ ) ≥ Z ^ 2 by norm_cast ] ;
    · linarith;
    · nlinarith;
  -- Apply the error bounds to the prime counts.
  have h_pi_bounds : |((primesUpTo (N : ℝ)).card : ℝ) - N / Real.log N| ≤ 2 * N / (Real.log N) ^ 2 ∧ |((primesUpTo ((Z : ℝ) - 1)).card : ℝ) - (Z - 1) / Real.log (Z - 1)| ≤ 3 * (Z - 1) / (Real.log (Z - 1)) ^ 2 := by
    apply And.intro;
    · convert pi_error_simple N _;
      exact_mod_cast by nlinarith;
    · convert pi_Zm1_error Z hZ using 1;
  -- Apply the error transfer bound to the second term.
  have h_pi_Zm1_bound : 3 * (Z - 1) / (Real.log (Z - 1)) ^ 2 ≤ 18 * N / (Real.log N) ^ 2 := by
    convert pi_Zm1_error_transfer N Z hZ hNZ using 1;
  exact abs_le.mpr ⟨ by ring_nf at *; linarith [ abs_le.mp h_card_diff, abs_le.mp h_pi_bounds.1, abs_le.mp h_pi_bounds.2 ], by ring_nf at *; linarith [ abs_le.mp h_card_diff, abs_le.mp h_pi_bounds.1, abs_le.mp h_pi_bounds.2 ] ⟩

/-
For primes p with Z ≤ p ≤ √N, the count π(N/p) is approximately
    (N/p)/log(N/p) with error at most 2(N/p)/(log(N/p))² ≤ 8(N/p)/(log N)².
-/
lemma pi_quot_approx (N p : ℕ) (hp : Nat.Prime p) (hp_le : p ≤ Nat.sqrt N)
    (hN : N ≥ 88789 ^ 2) :
    |((Finset.Icc 1 (N / p)).filter Nat.Prime).card -
      ((N : ℝ) / p) / Real.log ((N : ℝ) / p)| ≤
      8 * ((N : ℝ) / p) / (Real.log (N : ℝ)) ^ 2 := by
  -- Apply the lemma pi_error_simple to t = (N : ℝ) / p.
  have h_pi_error : |((primesUpTo ((N : ℝ) / p)).card : ℝ) - ((N : ℝ) / p) / Real.log ((N : ℝ) / p)| ≤ 2 * ((N : ℝ) / p) / (Real.log ((N : ℝ) / p)) ^ 2 := by
    convert pi_error_simple ( N / p ) _ using 1;
    rw [ ge_iff_le, le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.sqrt_le N, hp.two_le ];
  -- Since $p \leq \sqrt{N}$, we have $\log((N : ℝ) / p) \geq \log(\sqrt{N}) = \frac{\log N}{2}$.
  have h_log_bound : Real.log ((N : ℝ) / p) ≥ Real.log N / 2 := by
    rw [ ge_iff_le, div_le_iff₀' ] <;> norm_num;
    erw [ ← Real.log_pow, Real.log_le_log_iff ] <;> norm_num <;> try positivity [ Nat.sqrt_le N, hp.two_le, Nat.div_mul_le_self N p, Nat.div_add_mod N p, Nat.mod_lt N hp.pos ];
    rw [ div_pow, le_div_iff₀ ] <;> norm_cast;
    · nlinarith [ Nat.sqrt_le N, pow_le_pow_left' hp_le 2 ];
    · exact pow_pos hp.pos _;
  -- Therefore, $2 * ((N : ℝ) / p) / (Real.log ((N : ℝ) / p)) ^ 2 \leq 8 * ((N : ℝ) / p) / (Real.log N) ^ 2$.
  have h_final_bound : 2 * ((N : ℝ) / p) / (Real.log ((N : ℝ) / p)) ^ 2 ≤ 8 * ((N : ℝ) / p) / (Real.log N) ^ 2 := by
    rw [ div_le_div_iff₀ ];
    · nlinarith only [ show 0 ≤ ( N : ℝ ) / p by positivity, show 0 ≤ Real.log N ^ 2 by positivity, show 0 ≤ Real.log ( N / p ) ^ 2 by positivity, h_log_bound, show Real.log N ^ 2 ≤ 4 * Real.log ( N / p ) ^ 2 by nlinarith only [ show 0 ≤ Real.log N by positivity, show 0 ≤ Real.log ( N / p ) by exact Real.log_nonneg <| by rw [ le_div_iff₀ <| Nat.cast_pos.mpr hp.pos ] ; norm_cast ; nlinarith [ Nat.sqrt_le N ], h_log_bound ] ];
    · exact sq_pos_of_pos ( lt_of_lt_of_le ( by exact div_pos ( Real.log_pos ( by norm_cast; linarith ) ) zero_lt_two ) h_log_bound );
    · exact sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith;
  convert h_pi_error.trans h_final_bound using 2;
  unfold primesUpTo; norm_num [ Nat.floor_div_natCast ] ;
  congr 1 with ( _ | i ) <;> simp +arith +decide

/-
Reciprocal prime sum bound: Σ_{Z≤p≤√N} 1/p ≤ 2.
-/
lemma reciprocal_prime_sum_bound (N Z : ℕ)
    (hZ : Z ≥ 88789) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3) :
    ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime, (1 / (p : ℝ)) ≤ 2 := by
  -- Apply the Abel summation formula to the sum.
  have h_abel : (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc Z (Nat.sqrt N)), (1 / (p : ℝ))) ≤
    (2 * Nat.sqrt N / Real.log (Nat.sqrt N)) / (Nat.sqrt N : ℝ) +
    (∑ k ∈ Finset.Icc Z (Nat.sqrt N - 1), (2 * k / Real.log k) * (1 / (k : ℝ) - 1 / (k + 1 : ℝ))) := by
      have h_abel : (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc Z (Nat.sqrt N)), (1 / (p : ℝ))) ≤
        (∑ p ∈ Finset.Icc Z (Nat.sqrt N), (if Nat.Prime p then 1 else 0) : ℝ) / (Nat.sqrt N : ℝ) +
        (∑ k ∈ Finset.Icc Z (Nat.sqrt N - 1), (∑ p ∈ Finset.Icc Z k, (if Nat.Prime p then 1 else 0) : ℝ) * (1 / (k : ℝ) - 1 / (k + 1 : ℝ))) := by
          have h_abel : ∀ {a b : ℕ} (hab : a ≤ b), (∑ p ∈ Finset.Icc a b, (if Nat.Prime p then 1 else 0) * (1 / (p : ℝ))) =
            (∑ p ∈ Finset.Icc a b, (if Nat.Prime p then 1 else 0) : ℝ) * (1 / (b : ℝ)) +
            (∑ k ∈ Finset.Ico a b, (∑ p ∈ Finset.Icc a k, (if Nat.Prime p then 1 else 0) : ℝ) * (1 / (k : ℝ) - 1 / (k + 1 : ℝ))) := by
              intros a b hab
              have h_abel : ∀ {a b : ℕ} (hab : a ≤ b), (∑ p ∈ Finset.Icc a b, (if Nat.Prime p then 1 else 0) * (1 / (p : ℝ))) =
                (∑ p ∈ Finset.Icc a b, (if Nat.Prime p then 1 else 0) : ℝ) * (1 / (b : ℝ)) +
                (∑ k ∈ Finset.Ico a b, (∑ p ∈ Finset.Icc a k, (if Nat.Prime p then 1 else 0) : ℝ) * (1 / (k : ℝ) - 1 / (k + 1 : ℝ))) := by
                intros a b hab
                exact (by
                convert abel_summation ( fun p => if Nat.Prime p then 1 else 0 ) ( fun p => ( p : ℝ ) ⁻¹ ) a b hab using 1 ; norm_num [ Finset.sum_Ico_eq_sum_range ] ; ring_nf!;
                norm_num [ sub_eq_add_neg, add_comm, add_left_comm, add_assoc ];
                rw [ ← Finset.sum_neg_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by ring;);
              exact h_abel hab;
          nontriviality;
          convert h_abel ( show Z ≤ Nat.sqrt N from _ ) |> le_of_eq using 1;
          · rw [ Finset.sum_filter ] ; congr ; ext ; aesop;
          · cases h : Nat.sqrt N <;> simp_all +decide [ Finset.sum_Ico_eq_sum_range ];
            · rw [ Nat.sqrt_eq_zero ] at h ; nlinarith;
            · erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
              ring;
          · rw [ Nat.le_sqrt ] ; linarith;
      refine le_trans h_abel <| add_le_add ?_ <| Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_right ?_ <| sub_nonneg_of_le <| one_div_le_one_div_of_le ( Nat.cast_pos.mpr <| by linarith [ Finset.mem_Icc.mp hx ] ) <| by linarith [ Finset.mem_Icc.mp hx ] ;
      · gcongr;
        have := pi_upper_simple ( Nat.sqrt N ) ( show ( Nat.sqrt N : ℝ ) ≥ 88789 by exact_mod_cast le_trans hZ <| Nat.le_sqrt.mpr <| by nlinarith ) ; simp_all +decide ;
        refine le_trans ?_ this;
        refine' mod_cast Finset.card_mono _;
        simp +decide [ Finset.subset_iff, primesUpTo ];
        exact fun x hx₁ hx₂ hx₃ => ⟨ hx₂, hx₃ ⟩;
      · have := pi_upper_simple x ( show ( x : ℝ ) ≥ 88789 by exact_mod_cast le_trans hZ <| Finset.mem_Icc.mp hx |>.1 ) ; simp_all +decide ;
        refine le_trans ?_ this;
        refine' mod_cast Finset.card_mono _;
        simp +decide [ Finset.subset_iff, primesUpTo ];
        exact fun p hp₁ hp₂ hp₃ => ⟨ hp₂, hp₃ ⟩;
  -- Simplify the sum $\sum_{k=Z}^{\sqrt{N}-1} \frac{2k}{\log k} \left(\frac{1}{k} - \frac{1}{k+1}\right)$.
  have h_sum_simplified : (∑ k ∈ Finset.Icc Z (Nat.sqrt N - 1), (2 * k / Real.log k) * (1 / (k : ℝ) - 1 / (k + 1 : ℝ))) ≤
    (∑ k ∈ Finset.Icc Z (Nat.sqrt N - 1), (2 / (k : ℝ) * (1 / Real.log Z))) := by
      refine Finset.sum_le_sum fun x hx => ?_;
      field_simp;
      rw [ div_le_div_iff₀ ] <;> ring_nf;
      · norm_num [ sq, pow_three, mul_assoc, ne_of_gt ( show 0 < x from by linarith [ Finset.mem_Icc.mp hx ] ) ];
        exact le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by norm_cast; linarith [ Finset.mem_Icc.mp hx ] ) ) ( by positivity ) ) ( Real.log_nonneg ( by norm_cast; linarith [ Finset.mem_Icc.mp hx ] ) );
      · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Finset.mem_Icc.mp hx ];
      · exact mul_pos ( Nat.cast_pos.mpr ( by linarith [ Finset.mem_Icc.mp hx ] ) ) ( Real.log_pos ( by norm_cast; linarith ) );
  -- Simplify the sum $\sum_{k=Z}^{\sqrt{N}-1} \frac{2}{k \log Z}$.
  have h_sum_final : (∑ k ∈ Finset.Icc Z (Nat.sqrt N - 1), (2 / (k : ℝ) * (1 / Real.log Z))) ≤ (2 / Real.log Z) * (Real.log (Nat.sqrt N) - Real.log Z + 1 / Z) := by
    -- Apply the inequality $\sum_{k=Z}^{M-1} \frac{1}{k} \leq \log M - \log Z + \frac{1}{Z}$.
    have h_sum_ineq : ∀ {M : ℕ}, Z ≤ M → (∑ k ∈ Finset.Icc Z (M - 1), (1 / (k : ℝ))) ≤ Real.log M - Real.log Z + 1 / Z := by
      intros M hM
      have h_sum_ineq : ∀ k ∈ Finset.Icc Z (M - 1), (1 / (k : ℝ)) ≤ Real.log (k + 1) - Real.log k + (1 / (k : ℝ) - 1 / (k + 1 : ℝ)) := by
        intros k hk
        have h_log_ineq : Real.log (k + 1) - Real.log k ≥ 1 / (k + 1 : ℝ) := by
          have := exists_deriv_eq_slope Real.log ( show ( k : ℝ ) < k + 1 by norm_num ) ; norm_num at *;
          exact this ( continuousOn_of_forall_continuousAt fun x hx => Real.continuousAt_log <| ne_of_gt <| lt_of_lt_of_le ( by norm_cast; linarith ) hx.1 ) ( fun x hx => DifferentiableAt.differentiableWithinAt <| Real.differentiableAt_log <| ne_of_gt <| lt_of_lt_of_le ( by norm_cast; linarith ) hx.1.le ) |> fun ⟨ c, hc₁, hc₂ ⟩ => hc₂ ▸ inv_anti₀ ( by linarith ) ( by linarith );
        linarith;
      have h_sum_telescope : ∑ k ∈ Finset.Icc Z (M - 1), (Real.log (k + 1) - Real.log k) = Real.log M - Real.log Z := by
        erw [ Finset.sum_Ico_eq_sum_range ];
        convert Finset.sum_range_sub _ _ using 3 <;> push_cast <;> ring_nf;
        rw [ Nat.cast_sub <| by omega, Nat.cast_add, Nat.cast_sub <| by omega ] ; push_cast ; ring;
      have h_sum_telescope : ∑ k ∈ Finset.Icc Z (M - 1), (1 / (k : ℝ) - 1 / (k + 1 : ℝ)) = 1 / Z - 1 / (M : ℝ) := by
        erw [ Finset.sum_Ico_eq_sum_range ];
        convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring_nf;
        rw [ Nat.cast_sub <| by omega, Nat.cast_add, Nat.cast_one, Nat.cast_sub <| by omega ] ; ring;
      exact le_trans ( Finset.sum_le_sum h_sum_ineq ) ( by rw [ Finset.sum_add_distrib, ‹∑ k ∈ Finset.Icc Z ( M - 1 ), ( Real.log ( k + 1 ) - Real.log k ) = Real.log M - Real.log Z›, h_sum_telescope ] ; linarith [ show ( 0 : ℝ ) ≤ 1 / M by positivity ] );
    convert mul_le_mul_of_nonneg_left ( h_sum_ineq <| show Z ≤ Nat.sqrt N from _ ) ( show ( 0 : ℝ ) ≤ 2 / Real.log Z by positivity ) using 1 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    exact Nat.le_sqrt.mpr ( by linarith );
  -- Combine the inequalities to conclude the proof.
  have h_final : (2 * Nat.sqrt N / Real.log (Nat.sqrt N)) / (Nat.sqrt N : ℝ) + (2 / Real.log Z) * (Real.log (Nat.sqrt N) - Real.log Z + 1 / Z) ≤ 2 := by
    -- Simplify the expression by combining like terms.
    suffices h_simplified : (2 / Real.log (Nat.sqrt N)) + (2 / Real.log Z) * (Real.log (Nat.sqrt N) - Real.log Z + 1 / Z) ≤ 2 by
      convert h_simplified using 1;
      rw [ div_right_comm, mul_div_cancel_right₀ _ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.sqrt_pos.mpr <| by nlinarith ) ];
    -- Use the fact that $\log(\sqrt{N}) \leq \frac{3}{2} \log(Z)$ and $\log(Z) \geq 11$.
    have h_log_bounds : Real.log (Nat.sqrt N) ≤ (3 / 2) * Real.log Z ∧ Real.log Z ≥ 11 := by
      constructor;
      · rw [ div_mul_eq_mul_div, le_div_iff₀' ] <;> norm_num;
        erw [ ← Real.log_pow, ← Real.log_pow ] ; gcongr ; norm_cast;
        · exact pow_pos ( Nat.sqrt_pos.mpr ( by nlinarith ) ) _;
        · exact_mod_cast le_trans ( Nat.sqrt_le' _ ) hN_hi;
      · rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ];
        exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 11 = ( Real.exp 1 ) ^ 11 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) ( Nat.cast_le.mpr hZ );
    rw [ div_mul_eq_mul_div, div_add_div, div_le_iff₀ ] <;> try nlinarith [ Real.log_pos ( show ( N.sqrt :ℝ ) > 1 by exact Nat.one_lt_cast.mpr <| Nat.le_sqrt.mpr <| by nlinarith ) ];
    field_simp;
    nlinarith [ show ( Z : ℝ ) ≥ 88789 by norm_cast, mul_le_mul_of_nonneg_left h_log_bounds.2 <| Nat.cast_nonneg Z, mul_le_mul_of_nonneg_left h_log_bounds.1 <| Nat.cast_nonneg Z, Real.log_nonneg <| show ( N.sqrt :ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr <| Nat.sqrt_pos.mpr <| by nlinarith, Real.log_le_log ( by positivity ) <| show ( N.sqrt :ℝ ) ≥ Z by exact_mod_cast Nat.le_sqrt.mpr <| by nlinarith ];
  linarith

/-
π(√N)² ≤ 16N/(log N)² for N ≥ 88789².
-/
lemma pi_sqrt_sq_bound (N : ℕ) (hN : N ≥ 88789 ^ 2) :
    ((primesUpTo (Real.sqrt N)).card : ℝ) ^ 2 ≤ 16 * N / (Real.log N) ^ 2 := by
  -- By definition of π, we have π(√N) = #((primesUpTo (Real.sqrt N)).filter Nat.Prime).
  set A := (primesUpTo (Real.sqrt N)).card
  have hA : A ≤ 4 * Real.sqrt N / Real.log N := by
    -- Since $N \geq 88789^2$, we have $\sqrt{N} \geq 88789$. Therefore, we can apply the bound $\pi(x) \leq 2x/\log x$ with $x = \sqrt{N}$.
    have h_sqrt_bound : (primesUpTo (Real.sqrt N)).card ≤ 2 * Real.sqrt N / Real.log (Real.sqrt N) := by
      have := pi_upper_simple ( Real.sqrt N ) ?_ <;> norm_num at *;
      · convert this using 1;
      · exact Real.le_sqrt_of_sq_le ( mod_cast by linarith );
    convert h_sqrt_bound using 1 ; rw [ Real.log_sqrt ( Nat.cast_nonneg _ ) ] ; ring
  have hA_sq : A^2 ≤ (4 * Real.sqrt N / Real.log N)^2 := by
    gcongr;
  convert hA_sq using 1 ; ring_nf ; norm_num [ Real.sq_sqrt <| Nat.cast_nonneg N ] ;
  ring

lemma denom_monotone (N Z : ℕ) (hZ : Z ≥ 3) (hN_lo : Z ^ 2 ≤ N) (_hN_hi : N ≤ Z ^ 3) :
    MonotoneOn (fun t : ℝ => t * Real.log t * (Real.log N - Real.log t))
      (Set.Icc (Z : ℝ) (Nat.sqrt N + 1 : ℝ)) := by
  -- We'll use the fact that if the derivative of a function is non-negative on an interval, then the function is monotone increasing on that interval.
  have h_deriv_nonneg : ∀ t ∈ Set.Ioo (Z : ℝ) (Real.sqrt N + 1), deriv (fun t => t * Real.log t * (Real.log N - Real.log t)) t ≥ 0 := by
    intro t ht; norm_num [ show t ≠ 0 from by linarith [ ht.1, show ( Z :ℝ ) ≥ 3 by norm_cast ] ] ; ring_nf;
    -- Since $t \in [Z, \sqrt{N} + 1]$, we have $\log t \leq \log (\sqrt{N} + 1) \leq \log (\sqrt{N}) + \log (1 + 1/\sqrt{N}) \leq \frac{1}{2} \log N + \frac{1}{\sqrt{N}}$.
    have h_log_bound : Real.log t ≤ (1 / 2) * Real.log N + 1 / Real.sqrt N := by
      have h_log_bound : Real.log t ≤ Real.log (Real.sqrt N + 1) := by
        exact Real.log_le_log ( by linarith [ ht.1, show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ht.2.le;
      have h_log_bound : Real.log (Real.sqrt N + 1) ≤ Real.log (Real.sqrt N) + Real.log (1 + 1 / Real.sqrt N) := by
        rw [ ← Real.log_mul ( by exact ne_of_gt <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| by nlinarith ) ( by exact ne_of_gt <| add_pos zero_lt_one <| one_div_pos.mpr <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| by nlinarith ), mul_add, mul_div_cancel₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| by nlinarith ] ; norm_num;
      rw [ Real.log_sqrt ( Nat.cast_nonneg _ ) ] at h_log_bound;
      exact le_trans ‹_› ( h_log_bound.trans ( by linarith [ Real.log_le_sub_one_of_pos ( show 0 < 1 + 1 / Real.sqrt N by positivity ), show ( 1 : ℝ ) / Real.sqrt N ≥ 0 by positivity ] ) );
    -- Since $t \in [Z, \sqrt{N} + 1]$, we have $\log t \geq \log Z \geq \log 3 > 1$.
    have h_log_pos : 1 ≤ Real.log t := by
      rw [ Real.le_log_iff_exp_le ( by linarith [ ht.1, show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ];
      exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num; linarith [ ht.1, show ( Z : ℝ ) ≥ 3 by norm_cast ] );
    -- Since $t \in [Z, \sqrt{N} + 1]$, we have $\log N \geq 2 \log Z \geq 2 \log 3 > 2$.
    have h_log_N_pos : 2 ≤ Real.log N := by
      rw [ Real.le_log_iff_exp_le ( by norm_cast; nlinarith ) ];
      exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 2:ℝ ) = 1+1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ] ) ( Nat.cast_le.mpr ( show N ≥ 9 by nlinarith ) );
    -- Since $t \in [Z, \sqrt{N} + 1]$, we have $\frac{1}{\sqrt{N}} \leq \frac{1}{Z}$.
    have h_inv_sqrt_N_le_inv_Z : 1 / Real.sqrt N ≤ 1 / Z := by
      exact one_div_le_one_div_of_le ( by positivity ) ( Real.le_sqrt_of_sq_le ( mod_cast hN_lo ) );
    nlinarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, one_div_le_one_div_of_le ( by positivity ) ( show ( Z : ℝ ) ≥ 3 by norm_cast ), mul_inv_cancel₀ ( show t ≠ 0 by linarith [ ht.1, show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ];
  apply_rules [ monotoneOn_of_deriv_nonneg ];
  · exact convex_Icc _ _;
  · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.mul ( ContinuousAt.mul continuousAt_id ( Real.continuousAt_log ( by linarith [ ht.1, show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) ) ( ContinuousAt.sub continuousAt_const ( Real.continuousAt_log ( by linarith [ ht.1, show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) );
  · exact DifferentiableOn.mul ( DifferentiableOn.mul ( differentiableOn_id ) ( DifferentiableOn.log ( differentiableOn_id ) ( by intro t ht; linarith [ Set.mem_Icc.mp ( interior_subset ht ), show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) ) ( DifferentiableOn.sub ( differentiableOn_const _ ) ( DifferentiableOn.log ( differentiableOn_id ) ( by intro t ht; linarith [ Set.mem_Icc.mp ( interior_subset ht ), show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) );
  · simp +zetaDelta at *;
    exact fun x hx₁ hx₂ => h_deriv_nonneg x hx₁ <| hx₂.trans_le <| by nlinarith [ Real.sqrt_nonneg N, Real.sq_sqrt <| Nat.cast_nonneg N, show ( N : ℝ ) ≤ Z ^ 3 by norm_cast, show ( Z : ℝ ) ≥ 3 by norm_cast, show ( Nat.sqrt N : ℝ ) ≤ Real.sqrt N by exact Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' N ] ;

/-
f(t) = 1/(t·log t·(T-log t)) is AntitoneOn [Z, √N+1].
-/
lemma f_antitone_on (N Z : ℕ) (hZ : Z ≥ 3) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3) :
    AntitoneOn (fun t : ℝ => 1 / (t * Real.log t * (Real.log N - Real.log t)))
      (Set.Icc (Z : ℝ) (Nat.sqrt N + 1 : ℝ)) := by
  have h_denom_pos : ∀ t ∈ Set.Icc (Z : ℝ) (Nat.sqrt N + 1), t * Real.log t * (Real.log N - Real.log t) > 0 := by
    refine fun t ht => mul_pos ( mul_pos ( lt_of_lt_of_le ( by positivity ) ht.1 ) ( Real.log_pos <| lt_of_lt_of_le ( by norm_cast; linarith ) ht.1 ) ) ( sub_pos_of_lt <| Real.log_lt_log ( by linarith [ ht.1, show ( Z :ℝ ) ≥ 3 by norm_cast ] ) <| lt_of_le_of_lt ht.2 <| ?_ );
    norm_cast;
    nlinarith [ Nat.sqrt_le N, show N > 3 by nlinarith ];
  exact fun x hx y hy hxy => one_div_le_one_div_of_le ( h_denom_pos x hx ) ( denom_monotone N Z hZ hN_lo hN_hi hx hy hxy )

/-
The Riemann sum of f over [Z, M] bounds the integral from above.
-/
lemma riemann_sum_upper (N Z : ℕ) (hZ : Z ≥ 3) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3) :
    ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
        (1 / ((k : ℝ) * Real.log k * (Real.log N - Real.log k))) -
      ∫ t in (Z : ℝ)..(Real.sqrt N), 1 / (t * Real.log t * (Real.log N - Real.log t)) ≤
    1 / ((Z : ℝ) * Real.log Z * (Real.log N - Real.log Z)) := by
  have h_riemann : 0 ≤ ∑ k ∈ Finset.Icc Z (Nat.sqrt N), 1 / (k * Real.log k * (Real.log N - Real.log k)) - ∫ t in (Z : ℝ)..(Nat.sqrt N : ℝ), 1 / (t * Real.log t * (Real.log N - Real.log t)) := by
    have h_riemann_sum : ∫ t in (Z : ℝ)..(Nat.sqrt N : ℝ), 1 / (t * Real.log t * (Real.log N - Real.log t)) ≤ ∑ k ∈ Finset.Icc Z (Nat.sqrt N - 1), 1 / (k * Real.log k * (Real.log N - Real.log k)) := by
      convert AntitoneOn.integral_le_sum _ using 1;
      rotate_left;
      rotate_left;
      exact ↑Z;
      exact Nat.sqrt N - Z;
      use fun t => 1 / ( t * Real.log t * ( Real.log N - Real.log t ) );
      · convert f_antitone_on N Z hZ hN_lo hN_hi |> fun h => h.mono _ using 1;
        exact Set.Icc_subset_Icc_right ( by rw [ Nat.cast_sub ( show Z ≤ N.sqrt from by nlinarith [ Nat.lt_succ_sqrt N ] ) ] ; linarith );
      · rw [ Nat.cast_sub ( show Z ≤ N.sqrt from by nlinarith [ Nat.lt_succ_sqrt N ] ) ] ; ring_nf;
      · erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm ];
        rw [ show 1 + ( N.sqrt - 1 ) - Z = N.sqrt - Z from by omega ];
    refine' sub_nonneg_of_le ( h_riemann_sum.trans _ );
    exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc_right ( Nat.pred_le _ ) ) fun _ _ _ => one_div_nonneg.2 <| mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) <| Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith [ Finset.mem_Icc.1 ‹_› ] ) <| sub_nonneg.2 <| Real.log_le_log ( Nat.cast_pos.2 <| by linarith [ Finset.mem_Icc.1 ‹_› ] ) <| Nat.cast_le.2 <| by nlinarith [ Finset.mem_Icc.1 ‹_›, Nat.sqrt_le N ] ;
  have h_riemann_upper : ∑ k ∈ Finset.Icc Z (Nat.sqrt N), (1 / (k * Real.log k * (Real.log N - Real.log k))) ≤ 1 / (Z * Real.log Z * (Real.log N - Real.log Z)) + ∫ t in (Z : ℝ)..(Nat.sqrt N : ℝ), 1 / (t * Real.log t * (Real.log N - Real.log t)) := by
    have h_riemann_upper : ∑ k ∈ Finset.Icc (Z + 1) (Nat.sqrt N), (1 / (k * Real.log k * (Real.log N - Real.log k))) ≤ ∫ t in (Z : ℝ)..(Nat.sqrt N : ℝ), 1 / (t * Real.log t * (Real.log N - Real.log t)) := by
      have h_riemann_upper : ∀ k ∈ Finset.Icc (Z + 1) (Nat.sqrt N), ∫ t in (k - 1 : ℝ)..k, 1 / (t * Real.log t * (Real.log N - Real.log t)) ≥ 1 / (k * Real.log k * (Real.log N - Real.log k)) := by
        intros k hk
        have h_integral_bound : ∀ t ∈ Set.Icc (k - 1 : ℝ) k, 1 / (t * Real.log t * (Real.log N - Real.log t)) ≥ 1 / (k * Real.log k * (Real.log N - Real.log k)) := by
          intros t ht
          have h_monotone : t * Real.log t * (Real.log N - Real.log t) ≤ k * Real.log k * (Real.log N - Real.log k) := by
            have h_monotone : MonotoneOn (fun t : ℝ => t * Real.log t * (Real.log N - Real.log t)) (Set.Icc (Z : ℝ) (Nat.sqrt N + 1 : ℝ)) := by
              apply denom_monotone N Z hZ hN_lo hN_hi;
            apply h_monotone;
            · constructor <;> linarith [ ht.1, ht.2, show ( k : ℝ ) ≥ Z + 1 by exact_mod_cast Finset.mem_Icc.mp hk |>.1, show ( k : ℝ ) ≤ N.sqrt by exact_mod_cast Finset.mem_Icc.mp hk |>.2 ];
            · exact ⟨ by norm_cast; linarith [ Finset.mem_Icc.mp hk ], by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ⟩;
            · linarith [ ht.2 ];
          refine' one_div_le_one_div_of_le _ h_monotone;
          refine' mul_pos ( mul_pos _ ( Real.log_pos _ ) ) ( sub_pos.mpr ( Real.log_lt_log _ _ ) ) <;> norm_num at *;
          · linarith [ show ( k : ℝ ) ≥ 4 by norm_cast; linarith ];
          · linarith [ show ( k : ℝ ) ≥ 4 by norm_cast; linarith ];
          · linarith [ show ( k : ℝ ) ≥ 4 by norm_cast; linarith ];
          · nlinarith [ show ( k : ℝ ) ≤ N.sqrt by norm_cast; linarith, show ( N.sqrt : ℝ ) ^ 2 ≤ N by norm_cast; linarith [ Nat.sqrt_le N ], show ( Z : ℝ ) ≥ 3 by norm_cast, show ( k : ℝ ) ≥ Z + 1 by norm_cast; linarith ];
        refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ h_integral_bound ) <;> norm_num;
        apply_rules [ ContinuousOn.intervalIntegrable ];
        refine' ContinuousOn.mul _ _;
        · refine' ContinuousOn.inv₀ _ _;
          · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.sub continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ] ) );
          · intro x hx; rw [ Ne.eq_def, sub_eq_zero ] ; intro H; have := congr_arg Real.exp H; norm_num [ Real.exp_log ( show 0 < ( N : ℝ ) by norm_cast; nlinarith ), Real.exp_log ( show 0 < x by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 4 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ] ) ] at this;
            cases Set.mem_uIcc.mp hx <;> nlinarith [ show ( k : ℝ ) ≥ 4 by norm_cast; linarith [ Finset.mem_Icc.mp hk ], show ( k : ℝ ) ≤ Nat.sqrt N by norm_cast; linarith [ Finset.mem_Icc.mp hk ], Real.sqrt_nonneg N, Real.sq_sqrt <| Nat.cast_nonneg N, show ( N : ℝ ) ≥ k ^ 2 by norm_cast; nlinarith [ Finset.mem_Icc.mp hk, Nat.sqrt_le N ] ];
        · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( ContinuousAt.inv₀ ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 4 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 4 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ] ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 4 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ] ) ) );
      have h_riemann_upper : ∑ k ∈ Finset.Icc (Z + 1) (Nat.sqrt N), ∫ t in (k - 1 : ℝ)..k, 1 / (t * Real.log t * (Real.log N - Real.log t)) = ∫ t in (Z : ℝ)..(Nat.sqrt N : ℝ), 1 / (t * Real.log t * (Real.log N - Real.log t)) := by
        erw [ Finset.sum_Ico_eq_sum_range ];
        convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
        · ring;
        · rw [ Nat.cast_sub ] <;> push_cast <;> linarith [ Nat.lt_succ_sqrt N, show Z ≤ Nat.sqrt N from by nlinarith [ Nat.lt_succ_sqrt N ] ];
        · intro k hk; apply_rules [ ContinuousOn.intervalIntegrable ] ; ring_nf ;
          refine' continuousOn_of_forall_continuousAt fun t ht => _;
          refine' ContinuousAt.mul ( ContinuousAt.mul ( ContinuousAt.inv₀ ( continuousAt_const.sub ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) ) _ ) ( ContinuousAt.inv₀ ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) _ ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) _ ) <;> norm_num at *;
          · rw [ sub_eq_zero, eq_comm ];
            refine' ne_of_lt ( Real.log_lt_log _ _ );
            · linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ];
            · refine' lt_of_le_of_lt ht.2 _;
              norm_cast;
              nlinarith only [ hN_lo, hN_hi, hZ, Nat.sqrt_le N, hk, Nat.sub_add_cancel ( show Z + 1 ≤ N.sqrt + 1 from by nlinarith only [ hN_lo, hZ, Nat.lt_succ_sqrt N ] ) ];
          · exact ⟨ by linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ], by linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ], by linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ] ⟩;
          · linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ];
      exact h_riemann_upper ▸ Finset.sum_le_sum ‹_›;
    erw [ Finset.sum_Ico_eq_sub _ ] at * <;> norm_num at *;
    · norm_num [ Finset.sum_range_succ ] at * ; linarith;
    · nlinarith [ Nat.lt_succ_sqrt N ];
    · exact Nat.le_sqrt.mpr ( by linarith );
    · nlinarith [ Nat.lt_succ_sqrt N ];
  refine le_trans ( sub_le_sub_right ( h_riemann_upper ) _ ) ?_;
  rw [ show ( ∫ t in ( Z : ℝ )..Real.sqrt N, 1 / ( t * Real.log t * ( Real.log N - Real.log t ) ) ) = ( ∫ t in ( Z : ℝ ).. ( Nat.sqrt N : ℝ ), 1 / ( t * Real.log t * ( Real.log N - Real.log t ) ) ) + ( ∫ t in ( Nat.sqrt N : ℝ )..Real.sqrt N, 1 / ( t * Real.log t * ( Real.log N - Real.log t ) ) ) from ?_ ];
  · norm_num [ add_comm ];
    refine' intervalIntegral.integral_nonneg _ _ <;> norm_num;
    · exact Real.le_sqrt_of_sq_le ( mod_cast Nat.sqrt_le' _ );
    · intro u hu₁ hu₂; refine' mul_nonneg _ _ <;> norm_num;
      · exact Real.log_le_log ( by linarith [ show ( N.sqrt : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.sqrt_pos.mpr ( by nlinarith ) ) ] ) ( by nlinarith [ Real.mul_self_sqrt ( Nat.cast_nonneg N ), show ( N : ℝ ) ≥ 1 by norm_cast; nlinarith ] );
      · exact mul_nonneg ( inv_nonneg.2 ( Real.log_nonneg ( by nlinarith [ show ( N.sqrt : ℝ ) ≥ 1 by exact Nat.one_le_cast.2 ( Nat.sqrt_pos.2 ( by nlinarith ) ) ] ) ) ) ( inv_nonneg.2 ( by nlinarith [ show ( N.sqrt : ℝ ) ≥ 1 by exact Nat.one_le_cast.2 ( Nat.sqrt_pos.2 ( by nlinarith ) ) ] ) );
  · rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ];
    · refine' continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const _ _;
      · exact ContinuousAt.mul ( ContinuousAt.mul continuousAt_id ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N.sqrt : ℝ ) ≥ Z by exact_mod_cast Nat.le_sqrt.mpr ( by linarith ) ] ) ) ) ( ContinuousAt.sub continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N.sqrt : ℝ ) ≥ Z by exact_mod_cast Nat.le_sqrt.mpr ( by linarith ) ] ) ) );
      · simp +zetaDelta at *;
        refine' ⟨ ⟨ _, _, _ ⟩, _ ⟩;
        · cases Set.mem_uIcc.mp ht <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( Nat.sqrt N : ℝ ) ≥ Z by exact_mod_cast Nat.le_sqrt.mpr ( by nlinarith ) ];
        · cases Set.mem_uIcc.mp ht <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( Nat.sqrt N : ℝ ) ≥ Z by exact_mod_cast Nat.le_sqrt.mpr ( by linarith ) ];
        · cases Set.mem_uIcc.mp ht <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N.sqrt : ℝ ) ≥ Z by exact_mod_cast Nat.le_sqrt.mpr ( by linarith ) ];
        · rw [ sub_eq_zero, eq_comm ];
          refine' ne_of_lt ( Real.log_lt_log _ _ );
          · cases Set.mem_uIcc.mp ht <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N.sqrt : ℝ ) ≥ Z by exact_mod_cast Nat.le_sqrt.mpr ( by linarith ) ];
          · cases Set.mem_uIcc.mp ht <;> nlinarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N : ℝ ) ≥ Z ^ 2 by norm_cast, show ( Nat.sqrt N : ℝ ) ^ 2 ≤ N by norm_cast; exact Nat.sqrt_le' N, show ( Nat.sqrt N : ℝ ) < N by norm_cast; nlinarith [ Nat.sqrt_le N ] ];
    · refine' continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const _ _;
      · exact ContinuousAt.mul ( ContinuousAt.mul continuousAt_id ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.sqrt_nonneg N, Real.sq_sqrt ( Nat.cast_nonneg N ), show ( N : ℝ ) ≥ 1 by norm_cast; nlinarith, show ( Nat.sqrt N : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.sqrt_pos.mpr ( by nlinarith ) ) ] ) ) ) ( ContinuousAt.sub continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.sqrt_nonneg N, Real.sq_sqrt ( Nat.cast_nonneg N ), show ( N : ℝ ) ≥ 1 by norm_cast; nlinarith, show ( Nat.sqrt N : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.sqrt_pos.mpr ( by nlinarith ) ) ] ) ) );
      · refine' mul_ne_zero ( mul_ne_zero _ _ ) _ <;> norm_num at *;
        · cases Set.mem_uIcc.mp ht <;> nlinarith [ show ( N.sqrt : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.sqrt_pos.mpr ( by nlinarith ) ), Real.sqrt_nonneg N, Real.sq_sqrt ( Nat.cast_nonneg N ), show ( N : ℝ ) ≥ 1 by norm_cast; nlinarith ];
        · rcases Set.mem_uIcc.mp ht with ⟨ ht₁, ht₂ ⟩ <;> refine' ⟨ _, _, _ ⟩ <;> nlinarith [ show ( N : ℝ ) ≥ 9 by norm_cast; nlinarith, Real.sqrt_nonneg N, Real.sq_sqrt <| Nat.cast_nonneg N, show ( Nat.sqrt N : ℝ ) ≥ 3 by exact_mod_cast Nat.le_sqrt.mpr <| by nlinarith ];
        · rw [ sub_eq_zero, eq_comm ];
          refine' ne_of_lt ( Real.log_lt_log _ _ );
          · cases Set.mem_uIcc.mp ht <;> nlinarith [ show ( N.sqrt : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.sqrt_pos.mpr ( by nlinarith ) ), Real.sqrt_nonneg N, Real.sq_sqrt ( Nat.cast_nonneg N ), show ( N : ℝ ) ≥ 1 by norm_cast; nlinarith ];
          · cases Set.mem_uIcc.mp ht <;> nlinarith [ Real.mul_self_sqrt ( Nat.cast_nonneg N ), show ( N : ℝ ) ≥ Z ^ 2 by norm_cast, show ( Z : ℝ ) ≥ 3 by norm_cast, show ( Nat.sqrt N : ℝ ) ≤ Real.sqrt N by exact Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' N, Real.sqrt_nonneg N, Real.sq_sqrt <| Nat.cast_nonneg N, show ( N : ℝ ) ≥ 1 by norm_cast; nlinarith ]

/-
The Riemann sum of f over [Z, M] bounds the integral from below.
-/
lemma riemann_sum_lower (N Z : ℕ) (hZ : Z ≥ 3) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3) :
    0 ≤ ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
        (1 / ((k : ℝ) * Real.log k * (Real.log N - Real.log k))) -
      ∫ t in (Z : ℝ)..(Real.sqrt N), 1 / (t * Real.log t * (Real.log N - Real.log t)) := by
  refine' sub_nonneg.mpr _;
  -- Since $f(t)$ is decreasing on $[Z, \sqrt{N}]$, we have $\int_{Z}^{\sqrt{N}} f(t) \, dt \leq \sum_{k=Z}^{\sqrt{N}} f(k)$.
  have h_integral_le_sum : ∫ t in (Z : ℝ)..Real.sqrt N, (1 / (t * Real.log t * (Real.log N - Real.log t))) ≤ ∑ k ∈ Finset.Icc Z (Nat.sqrt N), ∫ t in (k : ℝ)..(k + 1 : ℝ), (1 / (t * Real.log t * (Real.log N - Real.log t))) := by
    have h_integral_le_sum : ∫ t in (Z : ℝ)..Real.sqrt N, (1 / (t * Real.log t * (Real.log N - Real.log t))) ≤ ∫ t in (Z : ℝ)..(Nat.sqrt N + 1 : ℝ), (1 / (t * Real.log t * (Real.log N - Real.log t))) := by
      apply_rules [ intervalIntegral.integral_mono_interval ];
      · norm_num;
      · exact Real.le_sqrt_of_sq_le ( mod_cast hN_lo );
      · exact real_sqrt_le_nat_sqrt_succ;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx;
        refine' one_div_nonneg.mpr _;
        refine' mul_nonneg ( mul_nonneg ( by linarith [ hx.1, show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ( Real.log_nonneg ( by linarith [ hx.1, show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) ) ( sub_nonneg.mpr ( Real.log_le_log ( by linarith [ hx.1, show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ( by nlinarith [ hx.1, hx.2, show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N : ℝ ) ≥ Z ^ 2 by norm_cast, Real.mul_self_sqrt ( Nat.cast_nonneg N ), show ( Nat.sqrt N : ℝ ) ^ 2 ≤ N by norm_cast; linarith [ Nat.sqrt_le N ] ] ) ) );
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        refine' continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const _ _;
        · exact ContinuousAt.mul ( ContinuousAt.mul continuousAt_id ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N.sqrt : ℝ ) + 1 ≥ 1 by linarith ] ) ) ) ( ContinuousAt.sub continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N.sqrt : ℝ ) + 1 ≥ 1 by linarith ] ) ) );
        · simp +zetaDelta at *;
          refine' ⟨ ⟨ _, _, _ ⟩, _ ⟩ <;> try cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ];
          · cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N.sqrt : ℝ ) ≥ Z by exact_mod_cast Nat.le_sqrt.mpr ( by nlinarith ) ];
          · rw [ sub_eq_zero, eq_comm ];
            refine' ne_of_lt ( Real.log_lt_log _ _ );
            · cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N.sqrt : ℝ ) ≥ 0 by positivity ];
            · cases Set.mem_uIcc.mp hx <;> nlinarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( N : ℝ ) ≥ Z ^ 2 by norm_cast, show ( Nat.sqrt N : ℝ ) ^ 2 ≤ N by norm_cast; exact Nat.sqrt_le' N, show ( Nat.sqrt N : ℝ ) + 1 ≤ N by norm_cast; nlinarith [ Nat.sqrt_le N ] ];
    convert h_integral_le_sum using 1;
    erw [ Finset.sum_Ico_eq_sum_range ];
    convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
    · ring;
    · rw [ Nat.cast_sub ] <;> norm_num ; nlinarith [ Nat.lt_succ_sqrt N ];
    · intro k hk; apply_rules [ ContinuousOn.intervalIntegrable ] ; norm_num [ ContinuousOn ];
      intro x hx₁ hx₂; refine' ContinuousAt.continuousWithinAt _; refine' ContinuousAt.mul _ _;
      · refine' ContinuousAt.inv₀ _ _;
        · exact ContinuousAt.sub continuousAt_const ( Real.continuousAt_log ( by linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ] ) );
        · refine' ne_of_gt ( sub_pos_of_lt ( Real.log_lt_log _ _ ) );
          · linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ];
          · refine' lt_of_le_of_lt hx₂ _;
            norm_cast;
            rw [ lt_tsub_iff_left ] at hk ; nlinarith [ Nat.sqrt_le N ];
      · exact ContinuousAt.mul ( ContinuousAt.inv₀ ( Real.continuousAt_log ( by linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) );
  nontriviality;
  refine le_trans h_integral_le_sum <| Finset.sum_le_sum fun x hx => ?_;
  refine' le_trans ( intervalIntegral.integral_mono_on _ _ _ _ ) _;
  refine' fun t => 1 / ( x * Real.log x * ( Real.log N - Real.log x ) );
  · norm_num;
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    refine' continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const _ _;
    · exact ContinuousAt.mul ( ContinuousAt.mul continuousAt_id ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ show ( x : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hx ] ] ) ) ) ( ContinuousAt.sub continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ show ( x : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hx ] ] ) ) );
    · simp +zetaDelta at *;
      refine' ⟨ ⟨ by linarith [ show ( x : ℝ ) ≥ 3 by norm_cast; linarith ], by linarith [ show ( x : ℝ ) ≥ 3 by norm_cast; linarith ], by linarith [ show ( x : ℝ ) ≥ 3 by norm_cast; linarith ] ⟩, _ ⟩;
      rw [ sub_eq_zero, eq_comm ];
      refine' ne_of_lt ( Real.log_lt_log _ _ );
      · linarith [ show ( x : ℝ ) ≥ 3 by norm_cast; linarith ];
      · nlinarith [ show ( x : ℝ ) ≤ N.sqrt by exact_mod_cast hx.2, Real.mul_self_sqrt ( Nat.cast_nonneg N ), show ( N.sqrt : ℝ ) ^ 2 ≤ N by exact_mod_cast Nat.sqrt_le' N, show ( Z : ℝ ) ≥ 3 by norm_cast, show ( x : ℝ ) ≥ Z by exact_mod_cast hx.1 ];
  · norm_num;
  · intro t ht;
    refine' one_div_le_one_div_of_le _ _;
    · refine' mul_pos ( mul_pos ( Nat.cast_pos.mpr <| by linarith [ Finset.mem_Icc.mp hx ] ) <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Finset.mem_Icc.mp hx ] ) <| sub_pos.mpr <| Real.log_lt_log ( Nat.cast_pos.mpr <| by linarith [ Finset.mem_Icc.mp hx ] ) <| Nat.cast_lt.mpr <| by nlinarith [ Finset.mem_Icc.mp hx, Nat.sqrt_le N ] ;
    · refine' denom_monotone N Z hZ hN_lo hN_hi _ _ _;
      · exact ⟨ mod_cast Finset.mem_Icc.mp hx |>.1, mod_cast Nat.le_succ_of_le ( Finset.mem_Icc.mp hx |>.2 ) ⟩;
      · exact ⟨ ht.1.trans' ( mod_cast Finset.mem_Icc.mp hx |>.1 ), ht.2.trans ( mod_cast Nat.succ_le_succ ( Finset.mem_Icc.mp hx |>.2 ) ) ⟩;
      · linarith [ ht.1 ];
  · norm_num

/-
f(Z) ≤ 1/(Z·(log Z)²) since log N - log Z ≥ log Z.
-/
lemma fZ_bound (N Z : ℕ) (hZ : Z ≥ 3) (hN_lo : Z ^ 2 ≤ N) :
    1 / ((Z : ℝ) * Real.log Z * (Real.log N - Real.log Z)) ≤
    1 / ((Z : ℝ) * (Real.log Z) ^ 2) := by
  convert one_div_le_one_div_of_le _ _ using 2;
  · infer_instance;
  · exact mul_pos ( by positivity ) ( sq_pos_of_pos ( Real.log_pos ( by norm_cast; linarith ) ) );
  · rw [ sq, mul_assoc ];
    gcongr;
    rw [ le_sub_iff_add_le, ← Real.log_mul ( by positivity ) ( by positivity ) ] ; exact Real.log_le_log ( by positivity ) ( by norm_cast; linarith )

/-! ## Weighted prime sum helpers

The strategy is to prove |Σ_p 1/(p·(T-log p)) - log(u-1)/T| ≤ 100/T²
using Abel summation + PNT error bounds.

Key decomposition:
  S = Σ_p G(p) = Main + Error
where
  Main = Σ_{k=Z}^{√N} [k/log k - (k-1)/log(k-1)] · G(k)
  Error = Σ_{k=Z}^{√N} [π_range(k) - (k/log k - (Z-1)/log(Z-1))] · ΔG(k) + boundary

We show |Main - I| ≤ 38/T² and |Error| ≤ 62/T².
-/

/-! ### Derivative bound for G(k) = 1/(k(T-log k)) -/

/-
G is decreasing: G(k) ≥ G(k+1) when T ≥ 6 and T/3 ≤ log k ≤ T/2, k ≥ 3.
    The product k(T-log k) is increasing because
    (k+1)(T-log(k+1)) - k(T-log k) = T - k·log(1+1/k) - log(k+1) ≥ T/2 - 1 - 1/k > 0.
-/
lemma G_decreasing (k : ℕ) (T : ℝ) (hk : k ≥ 3) (hT : T ≥ 6)
    (_hlog_lo : T / 3 ≤ Real.log k) (hlog_hi : Real.log k ≤ T / 2) :
    1 / ((k + 1 : ℝ) * (T - Real.log (k + 1))) ≤
    1 / ((k : ℝ) * (T - Real.log k)) := by
  refine' one_div_le_one_div_of_le _ _;
  · exact mul_pos ( by positivity ) ( by linarith );
  · have h_log_bound : Real.log (1 + 1 / (k : ℝ)) ≤ 1 / (k : ℝ) := by
      exact le_trans ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by norm_num );
    rw [ one_add_div ( by positivity ), Real.log_div ] at h_log_bound <;> norm_num at * <;> try linarith;
    nlinarith [ ( by norm_cast : ( 3 : ℝ ) ≤ k ), inv_mul_cancel₀ ( by positivity : ( k : ℝ ) ≠ 0 ), Real.log_le_sub_one_of_pos ( by positivity : 0 < ( k : ℝ ) ), Real.log_le_log ( by positivity ) ( by linarith : ( k : ℝ ) + 1 ≥ k ) ]

/-
Bound on t/log t derivative: |k/log k - (k-1)/log(k-1) - 1/log k| ≤ 2/(log k)² for k ≥ 88789.
-/
lemma pi_approx_diff_error (k : ℕ) (hk : k ≥ 88789) :
    |(k : ℝ) / Real.log k - ((k : ℝ) - 1) / Real.log ((k : ℝ) - 1) - 1 / Real.log k| ≤
    2 / (Real.log (k : ℝ)) ^ 2 := by
  have h_log_bound : Real.log k > 11 := by
    rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ( by positivity ) ];
    exact lt_of_lt_of_le ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 11 = ( Real.exp 1 ) ^ 11 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) ( Nat.cast_le.mpr hk );
  rw [ abs_le ];
  constructor;
  · rw [ div_sub_div, div_sub_div, le_div_iff₀ ] <;> try positivity;
    · ring_nf;
      norm_num [ show Real.log k ≠ 0 by positivity ];
      have h_log_bound : Real.log (-1 + (k : ℝ)) ≥ Real.log k - 1 / (k - 1) := by
        rw [ ge_iff_le, sub_le_iff_le_add ];
        rw [ Real.log_le_iff_le_exp, Real.exp_add, Real.exp_log ] <;> try linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast ];
        nlinarith [ Real.add_one_le_exp ( 1 / ( k - 1 ) ), show ( k : ℝ ) ≥ 88789 by norm_cast, one_div_mul_cancel ( show ( k : ℝ ) - 1 ≠ 0 by linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast ] ) ];
      rw [ ge_iff_le, sub_div', div_le_iff₀ ] at h_log_bound <;> nlinarith [ show ( k : ℝ ) ≥ 88789 by norm_cast, Real.log_le_sub_one_of_pos ( show 0 < ( k : ℝ ) by positivity ), Real.log_le_log ( by linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast ] ) ( show ( -1 + ( k : ℝ ) ) ≤ k by linarith ) ];
    · exact mul_pos ( mul_pos ( by positivity ) ( Real.log_pos ( by linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast ] ) ) ) ( by positivity );
    · exact ne_of_gt ( mul_pos ( lt_trans ( by norm_num ) h_log_bound ) ( Real.log_pos ( by linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast ] ) ) );
    · exact ne_of_gt <| Real.log_pos <| by linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast ];
  · rw [ div_sub_div, div_sub_div, div_le_div_iff₀ ] <;> try positivity;
    · have h_log_bound : Real.log (k - 1) ≤ Real.log k := by
        exact Real.log_le_log ( by linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast ] ) ( by linarith );
      nlinarith [ show ( k : ℝ ) ≥ 88789 by norm_cast, mul_le_mul_of_nonneg_left h_log_bound <| show 0 ≤ Real.log k by positivity, mul_le_mul_of_nonneg_left h_log_bound <| show 0 ≤ Real.log k ^ 2 by positivity, mul_le_mul_of_nonneg_left h_log_bound <| show 0 ≤ Real.log k ^ 3 by positivity, Real.log_nonneg <| show ( k : ℝ ) ≥ 1 by norm_cast; linarith ];
    · exact mul_pos ( mul_pos ( by positivity ) ( Real.log_pos ( by linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast ] ) ) ) ( by positivity );
    · exact ne_of_gt ( mul_pos ( lt_trans ( by norm_num ) h_log_bound ) ( Real.log_pos ( by linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast ] ) ) );
    · exact ne_of_gt <| Real.log_pos <| by linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast ]

/-
Sum of 1/(k(log k)²) from Z to M is ≤ 1/log(Z-1).
-/
lemma sum_reciprocal_k_log_sq_bound (Z M : ℕ) (hZ : Z ≥ 3) (hM : Z ≤ M) :
    ∑ k ∈ Finset.Icc Z M, (1 / ((k : ℝ) * (Real.log k) ^ 2)) ≤
    1 / Real.log ((Z : ℝ) - 1) := by
  nontriviality;
  -- By integral comparison, we have $\sum_{k=Z}^M \frac{1}{k(\log k)^2} \leq \int_{Z-1}^M \frac{1}{t(\log t)^2} dt$.
  have h_integral_comparison : (∑ k ∈ Finset.Icc Z M, (1 / ((k : ℝ) * (Real.log k) ^ 2))) ≤ ∫ t in (Z - 1 : ℝ)..M, (1 / (t * (Real.log t) ^ 2)) := by
    have h_integral_comparison : ∀ k ∈ Finset.Icc Z M, (1 / ((k : ℝ) * (Real.log k) ^ 2)) ≤ ∫ t in (k - 1 : ℝ)..k, (1 / (t * (Real.log t) ^ 2)) := by
      intros k hk
      have h_integral_bound : ∫ t in (k - 1 : ℝ)..k, (1 / (t * (Real.log t) ^ 2)) ≥ ∫ t in (k - 1 : ℝ)..k, (1 / ((k : ℝ) * (Real.log k) ^ 2)) := by
        refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ] ) ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ] ) ) );
        · intro x hx₁ hx₂; gcongr;
          · exact sq_pos_of_pos <| Real.log_pos <| by linarith [ show ( k : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ];
          · exact Real.log_nonneg ( by linarith [ show ( k : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ] );
          · linarith [ show ( k : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ];
          · linarith [ show ( k : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ];
      aesop;
    convert Finset.sum_le_sum h_integral_comparison using 1;
    erw [ Finset.sum_Ico_eq_sum_range ];
    symm;
    convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
    · ring;
    · rw [ Nat.cast_sub ] <;> push_cast <;> linarith;
    · intro k hk; apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast ] ) ) );
  -- Evaluate the integral $\int_{Z-1}^M \frac{1}{t(\log t)^2} dt$.
  have h_integral_eval : ∫ t in (Z - 1 : ℝ)..M, (1 / (t * (Real.log t) ^ 2)) = (1 / Real.log (Z - 1)) - (1 / Real.log M) := by
    rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    rotate_right;
    use fun x => -1 / Real.log x;
    · ring;
    · intro x hx; convert HasDerivAt.div ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_log ( show x ≠ 0 from by cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( M : ℝ ) ≥ Z by norm_cast ] ) ) ( show Real.log x ≠ 0 from ne_of_gt <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( M : ℝ ) ≥ Z by norm_cast ] ) using 1 ; ring;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( M : ℝ ) ≥ Z by norm_cast ] ) _ ) <| ne_of_gt <| mul_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( M : ℝ ) ≥ Z by norm_cast ] ) <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, show ( M : ℝ ) ≥ Z by norm_cast ] ;
  exact h_integral_comparison.trans ( h_integral_eval ▸ sub_le_self _ ( one_div_nonneg.mpr ( Real.log_nonneg ( by norm_cast; linarith ) ) ) )
lemma riemann_sum_vs_integral (N Z : ℕ)
    (hZ : Z ≥ 3) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3) :
    |∑ k ∈ Finset.Icc Z (Nat.sqrt N),
        (1 / ((k : ℝ) * Real.log k * (Real.log N - Real.log k))) -
      ∫ t in (Z : ℝ)..(Real.sqrt N), 1 / (t * Real.log t * (Real.log N - Real.log t))| ≤
    1 / ((Z : ℝ) * (Real.log Z) ^ 2) := by
  -- By combining the results from `riemann_sum_upper` and `fZ_bound`, we conclude the proof.
  have h_combined : (∑ k ∈ Finset.Icc Z (Nat.sqrt N), (1 / ((k : ℝ) * Real.log k * ((Real.log N) - Real.log k)))) - ∫ t in (Z : ℝ)..(Real.sqrt N), 1 / (t * Real.log t * ((Real.log N) - Real.log t)) ≤ 1 / ((Z : ℝ) * (Real.log Z) ^ 2) := by
    convert riemann_sum_upper N Z hZ hN_lo hN_hi |> le_trans <| fZ_bound N Z hZ hN_lo using 1;
  rw [ abs_of_nonneg ] <;> linarith [ riemann_sum_lower N Z hZ hN_lo hN_hi ]

/-
PNT error bound: |π_range(k) - (k/log k - (Z-1)/log(Z-1))| ≤ 5k/(log k)².
-/
lemma pi_range_pnt_error (k Z : ℕ) (hZ : Z ≥ 88789) (hk : k ≥ Z) :
    |((Finset.Icc Z k).filter Nat.Prime).card -
      ((k : ℝ) / Real.log k - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))| ≤
    5 * (k : ℝ) / (Real.log k) ^ 2 := by
  -- Use the triangle inequality:
  have h_triangle : |((Finset.Icc Z k).filter Nat.Prime).card - (k / Real.log k - (Z - 1) / Real.log (Z - 1))| ≤
    |(primesUpTo (k : ℝ)).card - k / Real.log k| + |(primesUpTo ((Z : ℝ) - 1)).card - (Z - 1) / Real.log (Z - 1)| := by
      have := primes_Icc_eq_diff Z k (by linarith) (by linarith);
      rw [ this, Nat.cast_sub ];
      · cases abs_cases ( ( primesUpTo k |> Finset.card : ℝ ) - k / Real.log k ) <;> cases abs_cases ( ( primesUpTo ( Z - 1 ) |> Finset.card : ℝ ) - ( Z - 1 ) / Real.log ( Z - 1 ) ) <;> cases abs_cases ( ( primesUpTo k |> Finset.card : ℝ ) - ( primesUpTo ( Z - 1 ) |> Finset.card : ℝ ) - ( k / Real.log k - ( Z - 1 ) / Real.log ( Z - 1 ) ) ) <;> linarith;
      · unfold primesUpTo; gcongr ; norm_num;
        exact_mod_cast Nat.le_succ_of_le hk;
  refine le_trans h_triangle ?_;
  refine' le_trans ( add_le_add ( pi_error_simple k ( by linarith [ show ( k : ℝ ) ≥ 88789 by norm_cast; linarith ] ) ) ( pi_Zm1_error Z ( by linarith ) ) ) _;
  -- Since $Z \geq 88789$, we have $\frac{Z-1}{(\log(Z-1))^2} \leq \frac{k}{(\log k)^2}$.
  have h_bound : (Z - 1 : ℝ) / (Real.log (Z - 1)) ^ 2 ≤ k / (Real.log k) ^ 2 := by
    -- Since $x / (\log x)^2$ is increasing for $x \geq e^2$, we have $(Z - 1) / (\log (Z - 1))^2 \leq k / (\log k)^2$.
    have h_inc : ∀ x y : ℝ, Real.exp 2 ≤ x → x ≤ y → x / (Real.log x) ^ 2 ≤ y / (Real.log y) ^ 2 := by
      -- Let's calculate the derivative of $f(x) = \frac{x}{(\log x)^2}$ and show it is positive for $x \geq e^2$.
      have h_deriv_pos : ∀ x : ℝ, Real.exp 2 < x → 0 < deriv (fun x => x / (Real.log x) ^ 2) x := by
        intro x hx; norm_num [ show x ≠ 0 by linarith [ Real.exp_pos 2 ], show Real.log x ≠ 0 by exact ne_of_gt <| Real.log_pos <| lt_trans ( by norm_num ) hx ] ;
        exact div_pos ( by nlinarith [ Real.add_one_le_exp 2, Real.log_exp 2, Real.log_lt_log ( by positivity ) hx, mul_inv_cancel₀ ( by linarith [ Real.add_one_le_exp 2, Real.log_exp 2, Real.log_lt_log ( by positivity ) hx ] : x ≠ 0 ), Real.log_pos ( show 1 < x by linarith [ Real.add_one_le_exp 2, Real.log_exp 2, Real.log_lt_log ( by positivity ) hx ] ) ] ) ( sq_pos_of_pos ( sq_pos_of_pos ( Real.log_pos ( show 1 < x by linarith [ Real.add_one_le_exp 2, Real.log_exp 2, Real.log_lt_log ( by positivity ) hx ] ) ) ) );
      intro x y hx hy; cases eq_or_lt_of_le hy <;> [ aesop; have := exists_deriv_eq_slope ( fun x => x / Real.log x ^ 2 ) ‹_› ] ;
      contrapose! this;
      exact ⟨ continuousOn_of_forall_continuousAt fun z hz => ContinuousAt.div continuousAt_id ( ContinuousAt.pow ( Real.continuousAt_log ( by linarith [ hz.1, Real.exp_pos 2 ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by linarith [ hz.1, Real.add_one_le_exp 2 ] ) ) ) ), fun z hz => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.div ( differentiableAt_id ) ( DifferentiableAt.pow ( Real.differentiableAt_log ( by linarith [ hz.1, Real.exp_pos 2 ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by linarith [ hz.1, Real.add_one_le_exp 2 ] ) ) ) ) ), fun c hc => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_deriv_pos c ( by linarith [ hc.1, Real.add_one_le_exp 2 ] ) ] ⟩;
    convert h_inc ( Z - 1 ) k _ _ using 1 <;> norm_num;
    · exact le_tsub_of_add_le_right ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 2:ℝ ) = 1+1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1, ( by norm_cast : ( 88789:ℝ ) ≤ Z ) ] );
    · exact_mod_cast Nat.le_succ_of_le hk;
  grind

lemma delta_pnt_telescoping (Z k : ℕ) (hZk : Z ≤ k) :
    ∑ j ∈ Finset.Icc Z k,
      ((j : ℝ) / Real.log j - ((j : ℝ) - 1) / Real.log ((j : ℝ) - 1)) =
    (k : ℝ) / Real.log k - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1) := by
  induction hZk <;> simp_all +decide ;
  erw [ Finset.sum_Ico_succ_top ( by linarith ), Finset.sum_Ico_succ_top ( by linarith ) ];
  erw [ Finset.sum_Ico_succ_top ( by linarith ), Finset.sum_Ico_succ_top ( by linarith ) ] at * ; norm_num at * ; linarith!

/-- Riemann sum = Σ ΔPNT·G - Σ d·G (algebraic identity). -/
lemma riemann_as_delta_pnt_minus_d (N Z : ℕ) :
    ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
      (1 / ((k : ℝ) * Real.log k * (Real.log N - Real.log k))) =
    ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
      (((k : ℝ) / Real.log k - ((k : ℝ) - 1) / Real.log ((k : ℝ) - 1)) *
       (1 / ((k : ℝ) * (Real.log N - Real.log k)))) -
    ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
      (((k : ℝ) / Real.log k - ((k : ℝ) - 1) / Real.log ((k : ℝ) - 1) -
        1 / Real.log k) *
       (1 / ((k : ℝ) * (Real.log N - Real.log k)))) := by
  rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; ring_nf;
  rw [ ← mul_inv ] ; ring;

/-- Abel summation for ΔPNT·G, using telescoping. -/
lemma delta_pnt_abel_identity (N Z : ℕ) (hN_lo : Z ^ 2 ≤ N) :
    ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
      (((k : ℝ) / Real.log k - ((k : ℝ) - 1) / Real.log ((k : ℝ) - 1)) *
       (1 / ((k : ℝ) * (Real.log N - Real.log k)))) =
    ((Nat.sqrt N : ℝ) / Real.log (Nat.sqrt N : ℝ) -
      ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1)) *
    (1 / ((Nat.sqrt N : ℝ) * (Real.log N - Real.log (Nat.sqrt N : ℝ)))) -
    ∑ k ∈ Finset.Ico Z (Nat.sqrt N),
      (((k : ℝ) / Real.log k - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1)) *
       (1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))) -
        1 / ((k : ℝ) * (Real.log N - Real.log k)))) := by
  convert abel_summation _ _ _ _ _ using 3;
  · convert delta_pnt_telescoping Z ( Nat.sqrt N ) ( Nat.le_sqrt.mpr ( by nlinarith ) ) |> Eq.symm using 1;
  · rw [ delta_pnt_telescoping ] <;> aesop;
  · rw [ Nat.le_sqrt ] ; nlinarith

/-
The "middle term" PNT(M)·G(M) + Σ PNT(k)·(G(k)-G(k+1)) equals Σ ΔPNT·G,
    and hence equals riemann_sum + Σ d·G. So |middle - riemann_sum| = |Σ d·G|.
-/
lemma middle_minus_riemann (N Z : ℕ) (hN_lo : Z ^ 2 ≤ N) :
    ((Nat.sqrt N : ℝ) / Real.log (Nat.sqrt N : ℝ) -
        ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1)) *
      (1 / ((Nat.sqrt N : ℝ) * (Real.log N - Real.log (Nat.sqrt N : ℝ)))) -
    ∑ k ∈ Finset.Ico Z (Nat.sqrt N),
      (((k : ℝ) / Real.log k - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1)) *
       (1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))) -
        1 / ((k : ℝ) * (Real.log N - Real.log k)))) -
    ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
      (1 / ((k : ℝ) * Real.log k * (Real.log N - Real.log k))) =
    ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
      (((k : ℝ) / Real.log k - ((k : ℝ) - 1) / Real.log ((k : ℝ) - 1) -
        1 / Real.log k) *
       (1 / ((k : ℝ) * (Real.log N - Real.log k)))) := by
  have := delta_pnt_abel_identity N Z hN_lo; have := riemann_as_delta_pnt_minus_d N Z; linarith;

/-
Convert prime_sum_abel_form from nsmul to mul.
-/
lemma prime_sum_as_mul (N Z : ℕ) (hZ : Z ≤ Nat.sqrt N) :
    ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
        (1 / ((p : ℝ) * (Real.log N - Real.log p))) =
    ↑((Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime).card *
      (1 / ((Nat.sqrt N : ℝ) * (Real.log N - Real.log (Nat.sqrt N : ℝ)))) -
    ∑ k ∈ Finset.Ico Z (Nat.sqrt N),
      (↑((Finset.Icc Z k).filter Nat.Prime).card *
       (1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))) -
        1 / ((k : ℝ) * (Real.log N - Real.log k)))) := by
  convert prime_sum_abel_form N Z ( fun k => 1 / ( k * ( Real.log N - Real.log k ) ) ) hZ using 1;
  norm_num [ nsmul_eq_mul ]

/-
The difference A*x - Σ A_k*y_k - (B*x - Σ B_k*y_k) = (A-B)*x - Σ (A_k-B_k)*y_k.
-/
lemma abel_diff_eq (N Z : ℕ)
    (A B : ℝ) (Ak Bk : ℕ → ℝ) (x : ℝ) (y : ℕ → ℝ) :
    (A * x - ∑ k ∈ Finset.Ico Z (Nat.sqrt N), Ak k * y k) -
    (B * x - ∑ k ∈ Finset.Ico Z (Nat.sqrt N), Bk k * y k) =
    (A - B) * x - ∑ k ∈ Finset.Ico Z (Nat.sqrt N), (Ak k - Bk k) * y k := by
  simpa only [ sub_mul, Finset.sum_sub_distrib, Finset.sum_mul _ _ _ ] using by ring;

/-
Algebraic identity: prime - middle = (card-PNT)*G(M) - Σ(card_k-PNT_k)*(G'-G).
-/
lemma prime_minus_middle_eq (N Z : ℕ) (hN_lo : Z ^ 2 ≤ N) :
    ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
        (1 / ((p : ℝ) * (Real.log N - Real.log p))) -
      (((Nat.sqrt N : ℝ) / Real.log (Nat.sqrt N : ℝ) -
        ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1)) *
       (1 / ((Nat.sqrt N : ℝ) * (Real.log N - Real.log (Nat.sqrt N : ℝ)))) -
      ∑ k ∈ Finset.Ico Z (Nat.sqrt N),
        (((k : ℝ) / Real.log k - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1)) *
         (1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))) -
          1 / ((k : ℝ) * (Real.log N - Real.log k))))) =
    (↑((Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime).card -
      ((Nat.sqrt N : ℝ) / Real.log (Nat.sqrt N : ℝ) -
       ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))) *
    (1 / ((Nat.sqrt N : ℝ) * (Real.log N - Real.log (Nat.sqrt N : ℝ)))) -
    ∑ k ∈ Finset.Ico Z (Nat.sqrt N),
      ((↑((Finset.Icc Z k).filter Nat.Prime).card -
        ((k : ℝ) / Real.log k - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))) *
       (1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))) -
        1 / ((k : ℝ) * (Real.log N - Real.log k)))) := by
  convert abel_diff_eq N Z _ _ _ _ _ _ using 1;
  · rw [ prime_sum_as_mul ];
    rw [ Nat.le_sqrt ] ; linarith

/-
Σ |d(k)| / (k·(T-log k)) ≤ 16/(log N)².
-/
lemma deriv_approx_error_sum_bound (N Z : ℕ)
    (hZ : Z ≥ 88789) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3)
    (hlogN : Real.log (N : ℝ) ≥ 24) :
    ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
      (|(k : ℝ) / Real.log k - ((k : ℝ) - 1) / Real.log ((k : ℝ) - 1) -
        1 / Real.log k| /
      ((k : ℝ) * (Real.log N - Real.log k))) ≤
    16 / (Real.log (N : ℝ)) ^ 2 := by
  -- By pi_approx_diff_error, |d(k)| ≤ 2/(log k)^2. And T - log k ≥ T/2. So each term ≤ 4/(k*T*(log k)^2).
  have h_term_bound : ∀ k ∈ Finset.Icc Z (Nat.sqrt N), |((k : ℝ) / Real.log k - ((k : ℝ) - 1) / Real.log ((k : ℝ) - 1) - 1 / Real.log k)| / ((k : ℝ) * (Real.log N - Real.log k)) ≤ 4 / ((k : ℝ) * (Real.log N) * (Real.log k) ^ 2) := by
    intros k hk
    have h_abs_d : |(k : ℝ) / Real.log k - ((k : ℝ) - 1) / Real.log ((k : ℝ) - 1) - 1 / Real.log k| ≤ 2 / (Real.log k) ^ 2 := by
      convert pi_approx_diff_error k ( by linarith [ Finset.mem_Icc.mp hk ] ) using 1;
    have h_log_bound : Real.log N - Real.log k ≥ Real.log N / 2 := by
      have h_log_bound : Real.log k ≤ Real.log N / 2 := by
        rw [ le_div_iff₀' ] <;> norm_num;
        rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ Finset.mem_Icc.mp hk, Nat.sqrt_le N ];
      linarith;
    convert mul_le_mul_of_nonneg_right h_abs_d ( inv_nonneg.mpr ( show 0 ≤ ( k : ℝ ) * ( Real.log N - Real.log k ) by exact mul_nonneg ( Nat.cast_nonneg _ ) ( by linarith ) ) ) |> le_trans <| ?_ using 1 ; ring_nf;
    field_simp;
    rw [ div_le_div_iff₀ ] <;> nlinarith [ show 0 < Real.log k ^ 2 * k by exact mul_pos ( sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Finset.mem_Icc.mp hk ] ) <| Nat.cast_pos.mpr <| by linarith [ Finset.mem_Icc.mp hk ] ];
  refine le_trans ( Finset.sum_le_sum h_term_bound ) ?_;
  -- Sum ≤ (4/T) * Σ 1/(k*(log k)^2) ≤ (4/T) * 1/log(Z-1) ≤ (4/T) * 4/T = 16/T².
  have h_sum_bound : ∑ k ∈ Finset.Icc Z (Nat.sqrt N), (1 / ((k : ℝ) * (Real.log k) ^ 2)) ≤ 4 / (Real.log N) := by
    refine le_trans ( sum_reciprocal_k_log_sq_bound Z ( Nat.sqrt N ) ( by linarith ) ( by nlinarith [ Nat.lt_succ_sqrt N ] ) ) ?_;
    rw [ div_le_div_iff₀ ] <;> try linarith [ Real.log_pos <| show ( N :ℝ ) > 1 by norm_cast; nlinarith ];
    · rw [ one_mul, ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_num <;> try nlinarith [ ( by norm_cast : ( Z :ℝ ) ≥ 88789 ) ];
      · nlinarith only [ show ( Z : ℝ ) ≥ 88789 by norm_cast, show ( N : ℝ ) ≤ Z ^ 3 by norm_cast, pow_two ( Z - 1 : ℝ ) ];
      · exact pow_pos ( by linarith [ show ( Z : ℝ ) ≥ 88789 by norm_cast ] ) _;
    · exact Real.log_pos <| by linarith [ show ( Z : ℝ ) ≥ 88789 by norm_cast ] ;
  convert mul_le_mul_of_nonneg_left h_sum_bound ( show ( 0 : ℝ ) ≤ 4 / Real.log N by positivity ) using 1 <;> ring_nf;
  simp +decide only [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _]

/-
Boundary PNT error: |e(M)|/|G(M)⁻¹| ≤ 4/(log N)².
-/
lemma boundary_pnt_error_bound (N Z : ℕ)
    (hZ : Z ≥ 88789) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3)
    (hlogN : Real.log (N : ℝ) ≥ 24) :
    abs (((Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime).card -
      ((Nat.sqrt N : ℝ) / Real.log (Nat.sqrt N : ℝ) -
       ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))) /
    ((Nat.sqrt N : ℝ) * (Real.log N - Real.log (Nat.sqrt N : ℝ))) ≤
    4 / (Real.log (N : ℝ)) ^ 2 := by
  -- Apply the lemma pi_range_pnt_error to bound |e(M)|.
  have h_error_bound : |((Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime).card - ((Nat.sqrt N : ℝ) / Real.log (Nat.sqrt N : ℝ) - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))| ≤ 5 * (Nat.sqrt N : ℝ) / (Real.log (Nat.sqrt N : ℝ)) ^ 2 := by
    apply pi_range_pnt_error;
    · bv_omega;
    · exact Nat.le_sqrt.2 ( by linarith );
  -- Since $T - \log M \geq T/2$, we have $M(T - \log M) \geq M \cdot T/2$.
  have h_denom_bound : (Nat.sqrt N : ℝ) * (Real.log N - Real.log (Nat.sqrt N : ℝ)) ≥ (Nat.sqrt N : ℝ) * (Real.log N / 2) := by
    have h_denom_bound : Real.log (Nat.sqrt N : ℝ) ≤ Real.log N / 2 := by
      rw [ le_div_iff₀' ] <;> norm_num;
      rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ Nat.sqrt_le N, Nat.lt_succ_sqrt N ];
    exact mul_le_mul_of_nonneg_left ( by linarith ) ( Nat.cast_nonneg _ );
  have h_log_bound : Real.log (Nat.sqrt N : ℝ) ≥ Real.log N / 3 := by
    rw [ ge_iff_le, div_le_iff₀' ] <;> norm_num;
    rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast;
    · nlinarith only [ Nat.lt_succ_sqrt N, hN_lo, hN_hi, pow_two ( Nat.sqrt N - Z : ℤ ), pow_two ( Nat.sqrt N + Z : ℤ ), hZ ];
    · nlinarith;
    · exact pow_pos ( Nat.sqrt_pos.mpr ( by nlinarith ) ) _;
    · exact Nat.sqrt_pos.mpr ( by nlinarith );
  refine' le_trans ( div_le_div_of_nonneg_left _ _ h_denom_bound ) _;
  · positivity;
  · exact mul_pos ( Nat.cast_pos.mpr ( Nat.sqrt_pos.mpr ( by nlinarith ) ) ) ( div_pos ( lt_of_lt_of_le ( by norm_num ) hlogN ) zero_lt_two );
  · refine' le_trans ( mul_le_mul_of_nonneg_right h_error_bound <| by positivity ) _;
    field_simp;
    rw [ div_le_iff₀ ] <;> nlinarith [ show ( N.sqrt : ℝ ) > 0 by exact Nat.cast_pos.mpr <| Nat.sqrt_pos.mpr <| by nlinarith, show ( Real.log N : ℝ ) > 0 by exact lt_of_lt_of_le ( by norm_num ) hlogN, show ( Real.log N.sqrt : ℝ ) ^ 2 > 0 by exact sq_pos_of_pos <| lt_of_lt_of_le ( by positivity ) h_log_bound, mul_le_mul_of_nonneg_left h_log_bound <| show ( 0 : ℝ ) ≤ N.sqrt by positivity ]

/-! ## Weighted prime sum estimate -/

/-
The g-function difference bound:
    g(k) - g(k+1) ≤ (log N) / (k² · (log N - log k)²)
    where g(k) = 1/(k·(log N - log k)).
-/
lemma g_diff_upper_bound (k N : ℕ) (hk : k ≥ 3) (hN : N ≥ k ^ 2)
    (hlog : Real.log k ≤ Real.log N / 2) :
    1 / ((k : ℝ) * (Real.log N - Real.log k)) -
    1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))) ≤
    Real.log N / ((k : ℝ) ^ 2 * (Real.log N - Real.log k) ^ 2) := by
  by_cases h : Real.log N - Real.log k = 0 <;> by_cases h' : Real.log N - Real.log ( k + 1 ) = 0 <;> simp_all +decide [ division_def ];
  · exact absurd h ( sub_ne_zero_of_ne ( ne_of_gt ( Real.log_lt_log ( by positivity ) ( by norm_cast; nlinarith ) ) ) );
  · exact absurd h' ( sub_ne_zero_of_ne ( ne_of_gt ( Real.log_lt_log ( by positivity ) ( by norm_cast; nlinarith ) ) ) );
  · field_simp;
    rw [ div_le_div_iff₀ ];
    · have h_log_bound : Real.log (k + 1) ≤ Real.log k + 1 / k := by
        rw [ Real.log_le_iff_le_exp, Real.exp_add, Real.exp_log ] <;> try norm_num ; linarith;
        nlinarith [ Real.add_one_le_exp ( 1 / ( k : ℝ ) ), one_div_mul_cancel ( by positivity : ( k : ℝ ) ≠ 0 ) ];
      have h_log_bound : Real.log N - Real.log (k + 1) ≥ Real.log N - Real.log k - 1 / k := by
        grobner;
      have h_log_bound : Real.log N - Real.log k ≥ Real.log k := by
        grind;
      have h_log_bound : Real.log k ≥ 1 := by
        exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( k : ℝ ) ≥ 3 by norm_cast ] ) );
      have h_log_bound : Real.log N - Real.log k ≤ Real.log N := by
        grind;
      have h_log_bound : Real.log N - Real.log k ≥ 1 := by
        linarith;
      have h_log_bound : Real.log N - Real.log (k + 1) ≤ Real.log N - Real.log k := by
        exact sub_le_sub_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) _;
      have h_log_bound : (k : ℝ) ≥ 3 := by
        norm_cast;
      field_simp at *;
      nlinarith [ mul_le_mul_of_nonneg_left ‹3 ≤ ( k : ℝ ) › ( sub_nonneg_of_le ‹1 ≤ Real.log N - Real.log k› ), mul_le_mul_of_nonneg_left ‹3 ≤ ( k : ℝ ) › ( sub_nonneg_of_le ‹1 ≤ Real.log k› ), mul_le_mul_of_nonneg_left ‹3 ≤ ( k : ℝ ) › ( sub_nonneg_of_le ‹Real.log N - Real.log ( k + 1 ) ≤ Real.log N - Real.log k› ) ];
    · exact lt_of_le_of_ne ( sub_nonneg_of_le <| Real.log_le_log ( by positivity ) <| by norm_cast; nlinarith ) ( Ne.symm h );
    · exact mul_pos ( sq_pos_of_pos ( lt_of_le_of_ne ( sub_nonneg.mpr ( Real.log_le_log ( by positivity ) ( by norm_cast; nlinarith ) ) ) ( Ne.symm h ) ) ) ( lt_of_le_of_ne ( sub_nonneg.mpr ( Real.log_le_log ( by positivity ) ( by norm_cast; nlinarith ) ) ) ( Ne.symm h' ) )

/-
Bound on Σ 1/(k·(log k)²·(log N - log k)²): since log k ≥ T/3 and
    log N - log k ≥ T/2, we get ≤ 36/T⁴ · Σ 1/k ≤ 12/T³.
-/
lemma sum_inv_k_log_sq_T_sq_bound (N Z : ℕ) (hZ : Z ≥ 3) (hN_lo : Z ^ 2 ≤ N)
    (hN_hi : N ≤ Z ^ 3) :
    ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
      (1 / ((k : ℝ) * (Real.log k) ^ 2 * (Real.log N - Real.log k) ^ 2)) ≤
    12 / (Real.log N) ^ 3 := by
  -- Since $k \in [Z, \sqrt{N}]$, we have $\log k \geq \log Z \geq \frac{\log N}{3}$ and $\log N - \log k \geq \log N - \log \sqrt{N} = \frac{\log N}{2}$.
  have h_log_bounds : ∀ k ∈ Finset.Icc Z (Nat.sqrt N), Real.log k ≥ Real.log N / 3 ∧ Real.log N - Real.log k ≥ Real.log N / 2 := by
    intro k hk
    have h_log_k : Real.log k ≥ Real.log Z := by
      exact Real.log_le_log ( by positivity ) ( mod_cast Finset.mem_Icc.mp hk |>.1 )
    have h_log_N_k : Real.log N - Real.log k ≥ Real.log N / 2 := by
      linarith [ show Real.log k ≤ Real.log N / 2 by rw [ le_div_iff₀' ] <;> norm_num ; rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ Finset.mem_Icc.mp hk, Nat.sqrt_le N ] ];
    exact ⟨ by linarith [ show ( Real.log N : ℝ ) ≤ Real.log Z * 3 by rw [ mul_comm, ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ pow_succ Z 2 ] ], h_log_N_k ⟩;
  -- Therefore, $1/(k·(\log k)^2·(\log N - \log k)^2) \leq 36/(k·(\log N)^4)$.
  have h_reciprocal_bound : ∀ k ∈ Finset.Icc Z (Nat.sqrt N), 1 / ((k : ℝ) * (Real.log k) ^ 2 * (Real.log N - Real.log k) ^ 2) ≤ 36 / ((k : ℝ) * (Real.log N) ^ 4) := by
    intro k hk; rw [ div_le_div_iff₀ ];
    · have := h_log_bounds k hk;
      nlinarith [ show 0 ≤ ( k : ℝ ) * Real.log N ^ 2 by positivity, show 0 ≤ ( k : ℝ ) * Real.log N ^ 3 by positivity, show 0 ≤ ( k : ℝ ) * Real.log N ^ 4 by positivity, show 0 ≤ ( k : ℝ ) * Real.log k ^ 2 by positivity, show 0 ≤ ( k : ℝ ) * ( Real.log N - Real.log k ) ^ 2 by positivity, pow_le_pow_left₀ ( by positivity ) this.1 2, pow_le_pow_left₀ ( by linarith [ Real.log_nonneg ( show ( N :ℝ ) ≥ 1 by norm_cast; nlinarith ) ] ) this.2 2 ];
    · exact mul_pos ( mul_pos ( Nat.cast_pos.mpr ( by linarith [ Finset.mem_Icc.mp hk ] ) ) ( sq_pos_of_pos ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Icc.mp hk ] ) ) ) ) ( sq_pos_of_pos ( by linarith [ h_log_bounds k hk, Real.log_pos ( show ( N : ℝ ) > 1 by norm_cast; nlinarith ) ] ) );
    · exact mul_pos ( Nat.cast_pos.mpr ( by linarith [ Finset.mem_Icc.mp hk ] ) ) ( pow_pos ( Real.log_pos ( by norm_cast; nlinarith ) ) _ );
  -- Since $\sum_{k=Z}^{\sqrt{N}} \frac{1}{k} \leq \log(\sqrt{N}/Z) + 1/Z \leq \frac{\log N}{4} + \frac{1}{Z} \leq \frac{\log N}{3}$,
  have h_harmonic_sum : ∑ k ∈ Finset.Icc Z (Nat.sqrt N), (1 / (k : ℝ)) ≤ (Real.log N) / 3 := by
    -- Since $\sqrt{N} \leq Z^{3/2}$, we have $\sum_{k=Z}^{\sqrt{N}} \frac{1}{k} \leq \log(\sqrt{N}/Z) + 1/Z$.
    have h_harmonic_sum_bound : ∑ k ∈ Finset.Icc Z (Nat.sqrt N), (1 / (k : ℝ)) ≤ Real.log (Nat.sqrt N / Z) + 1 / Z := by
      -- We'll use the fact that $\sum_{k=Z}^{M} \frac{1}{k}$ is bounded above by $\log(M/Z) + 1/Z$.
      have h_harmonic_bound : ∀ {M : ℕ}, Z ≤ M → (∑ k ∈ Finset.Icc Z M, (1 / (k : ℝ))) ≤ Real.log (M / Z) + 1 / Z := by
        intros M hM
        induction' M, hM using Nat.le_induction with M ih;
        · norm_num [ show Z ≠ 0 by linarith ];
        · erw [ Finset.sum_Ico_succ_top ( by linarith ), add_comm ];
          -- We'll use the fact that $\frac{1}{M+1} \leq \int_{M}^{M+1} \frac{1}{x} \, dx$.
          have h_integral_bound : (1 / (M + 1 : ℝ)) ≤ Real.log (M + 1) - Real.log M := by
            have := exists_deriv_eq_slope Real.log ( show ( M : ℝ ) < M + 1 by norm_num ) ; norm_num at *;
            exact this ( continuousOn_of_forall_continuousAt fun x hx => Real.continuousAt_log <| ne_of_gt <| lt_of_lt_of_le ( by norm_cast; linarith ) hx.1 ) ( fun x hx => DifferentiableAt.differentiableWithinAt <| Real.differentiableAt_log <| ne_of_gt <| lt_of_lt_of_le ( by norm_cast; linarith ) hx.1.le ) |> fun ⟨ c, hc₁, hc₂ ⟩ => hc₂ ▸ inv_anti₀ ( by linarith ) ( by linarith );
          rw [ Real.log_div ] at * <;> norm_num at * <;> linarith!;
      exact h_harmonic_bound <| Nat.le_sqrt.mpr <| by nlinarith;
    refine le_trans h_harmonic_sum_bound ?_;
    refine' le_trans ( add_le_add ( Real.log_le_log ( by exact div_pos ( Nat.cast_pos.mpr <| Nat.sqrt_pos.mpr <| by nlinarith ) <| Nat.cast_pos.mpr <| by linarith ) <| show ( N.sqrt : ℝ ) / Z ≤ Real.sqrt N / Z from div_le_div_of_nonneg_right ( Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' _ ) <| Nat.cast_nonneg _ ) le_rfl ) _;
    rw [ Real.log_div ( by exact ne_of_gt <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| by nlinarith ) <| by positivity, Real.log_sqrt <| by positivity ];
    have h_log_bound : Real.log N ≤ 3 * Real.log Z := by
      rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ pow_succ' Z 2 ];
    nlinarith [ show ( Z : ℝ ) ≥ 3 by norm_cast, Real.log_inv ( Z : ℝ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( Z : ℝ ) ) ), mul_inv_cancel₀ ( by positivity : ( Z : ℝ ) ≠ 0 ), one_div_mul_cancel ( by positivity : ( Z : ℝ ) ≠ 0 ) ];
  refine le_trans ( Finset.sum_le_sum h_reciprocal_bound ) ?_;
  convert mul_le_mul_of_nonneg_left h_harmonic_sum ( show ( 0 : ℝ ) ≤ 36 / ( Real.log N ^ 4 ) by positivity ) using 1 <;> ring_nf;
  · simp +decide only [mul_comm, Finset.mul_sum _ _ _];
  · grind +splitImp

/-
The step that converts the sum Σ_k 1/(k·log k·(T-log k)) to the integral
    log(u-1)/T, combining riemann_sum_vs_integral with integral_weighted_reciprocal.
-/
lemma riemann_to_integral_bound (N Z : ℕ) (hZ : Z ≥ 88789)
    (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3) :
    |∑ k ∈ Finset.Icc Z (Nat.sqrt N),
        (1 / ((k : ℝ) * Real.log k * (Real.log N - Real.log k))) -
      Real.log (Real.log N / Real.log Z - 1) / Real.log N| ≤
    1 / (Real.log (N : ℝ)) ^ 2 := by
  have := @riemann_sum_vs_integral N Z ( by linarith ) ( by linarith ) ( by linarith );
  rw [ integral_weighted_reciprocal ] at this;
  · refine le_trans this ?_;
    gcongr;
    · exact sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr <| by nlinarith;
    · -- Since $N \leq Z^3$, we have $\log N \leq 3 \log Z$.
      have h_log_N_le_3_log_Z : Real.log N ≤ 3 * Real.log Z := by
        rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ pow_succ' Z 2 ];
      exact le_trans ( pow_le_pow_left₀ ( Real.log_nonneg <| Nat.one_le_cast.mpr <| by nlinarith ) h_log_N_le_3_log_Z 2 ) <| by nlinarith [ show ( Z : ℝ ) ≥ 88789 by norm_cast, Real.log_nonneg <| show ( Z : ℝ ) ≥ 1 by norm_cast; linarith ] ;
  · linarith;
  · linarith;
  · linarith

/-
Bound on the weighted PNT error sum:
    Σ 5k/(log k)² · (g(k)-g(k+1)) ≤ 60/T²
-/
lemma weighted_pnt_error_sum (N Z : ℕ) (hZ : Z ≥ 3)
    (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3)
    (hlogN : Real.log (N : ℝ) ≥ 6) :
    ∑ k ∈ Finset.Ico Z (Nat.sqrt N),
      (5 * (k : ℝ) / (Real.log k) ^ 2 *
       (1 / ((k : ℝ) * (Real.log N - Real.log k)) -
        1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))))) ≤
    60 / (Real.log (N : ℝ)) ^ 2 := by
  have h_sum_bound : ∑ k ∈ Finset.Ico Z (Nat.sqrt N),
      (5 * k / (Real.log k) ^ 2 : ℝ) * (1 / ((k : ℝ) * (Real.log N - Real.log k)) -
        1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ)))) ≤
      5 * Real.log N * ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
      (1 / ((k : ℝ) * (Real.log k) ^ 2 * (Real.log N - Real.log k) ^ 2 : ℝ)) := by
        have h_sum_bound : ∀ k ∈ Finset.Ico Z (Nat.sqrt N), 5 * (k : ℝ) / (Real.log k) ^ 2 * (1 / ((k : ℝ) * (Real.log N - Real.log k)) - 1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ)))) ≤ 5 * Real.log N * (1 / ((k : ℝ) * (Real.log k) ^ 2 * (Real.log N - Real.log k) ^ 2 : ℝ)) := by
          intro k hk
          have h_g_diff : 1 / ((k : ℝ) * (Real.log N - Real.log k)) - 1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))) ≤ Real.log N / ((k : ℝ) ^ 2 * (Real.log N - Real.log k) ^ 2) := by
            convert g_diff_upper_bound k N ( by linarith [ Finset.mem_Ico.mp hk ] ) ( by nlinarith [ Finset.mem_Ico.mp hk, Nat.sqrt_le N ] ) _ using 1;
            rw [ le_div_iff₀' ] <;> norm_num;
            rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ Finset.mem_Ico.mp hk, Nat.sqrt_le N ];
          convert mul_le_mul_of_nonneg_left h_g_diff ( show ( 0 :ℝ ) ≤ 5 * k / Real.log k ^ 2 by positivity ) using 1 ; ring_nf;
          grind +splitImp;
        refine' le_trans ( Finset.sum_le_sum h_sum_bound ) _;
        rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ Finset.mem_Ico.mp hx |>.1, Finset.mem_Ico.mp hx |>.2.le ⟩ ) fun _ _ _ => mul_nonneg ( by positivity ) ( one_div_nonneg.mpr <| mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) <| sq_nonneg _ ) <| sq_nonneg _ ) ;
  exact h_sum_bound.trans ( by have := sum_inv_k_log_sq_T_sq_bound N Z hZ hN_lo hN_hi; ring_nf at *; nlinarith [ inv_pos.mpr ( show 0 < Real.log N by positivity ), mul_inv_cancel₀ ( ne_of_gt ( show 0 < Real.log N by positivity ) ) ] )

/-
Abel summation error: the difference between the prime sum and
    the Riemann sum is bounded by 99/(log N)².
-/
lemma abel_summation_error (N Z : ℕ)
    (hZ : Z ≥ 88789) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3)
    (hlogN : Real.log (N : ℝ) ≥ 24) :
    |∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
        (1 / ((p : ℝ) * (Real.log N - Real.log p))) -
      ∑ k ∈ Finset.Icc Z (Nat.sqrt N),
        (1 / ((k : ℝ) * Real.log k * (Real.log N - Real.log k)))| ≤
      99 / (Real.log (N : ℝ)) ^ 2 := by
  have := @weighted_pnt_error_sum N Z;
  have := @prime_minus_middle_eq N Z ( by linarith );
  have := @middle_minus_riemann N Z ( by linarith );
  have := @boundary_pnt_error_bound N Z ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith );
  have := @deriv_approx_error_sum_bound N Z ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith );
  rename_i h₁ h₂ h₃ h₄₅;
  -- Apply the triangle inequality to the absolute value.
  have h_triangle : |∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime, (1 / ((p : ℝ) * (Real.log N - Real.log p))) - ∑ k ∈ Finset.Icc Z (Nat.sqrt N), (1 / ((k : ℝ) * Real.log k * (Real.log N - Real.log k)))| ≤
    |((Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime).card - ((Nat.sqrt N : ℝ) / Real.log (Nat.sqrt N : ℝ) - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))| / ((Nat.sqrt N : ℝ) * (Real.log N - Real.log (Nat.sqrt N : ℝ))) +
    ∑ k ∈ Finset.Ico Z (Nat.sqrt N), |((Finset.Icc Z k).filter Nat.Prime).card - ((k : ℝ) / Real.log k - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))| * |1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))) - 1 / ((k : ℝ) * (Real.log N - Real.log k))| +
    ∑ k ∈ Finset.Icc Z (Nat.sqrt N), |(k : ℝ) / Real.log k - ((k : ℝ) - 1) / Real.log ((k : ℝ) - 1) - 1 / Real.log k| / ((k : ℝ) * (Real.log N - Real.log k)) := by
      have h_triangle : |∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime, (1 / ((p : ℝ) * (Real.log N - Real.log p))) - ∑ k ∈ Finset.Icc Z (Nat.sqrt N), (1 / ((k : ℝ) * Real.log k * (Real.log N - Real.log k)))| ≤
        |((Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime).card - ((Nat.sqrt N : ℝ) / Real.log (Nat.sqrt N : ℝ) - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))| * |1 / ((Nat.sqrt N : ℝ) * (Real.log N - Real.log (Nat.sqrt N : ℝ)))| +
        ∑ k ∈ Finset.Ico Z (Nat.sqrt N), |((Finset.Icc Z k).filter Nat.Prime).card - ((k : ℝ) / Real.log k - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))| * |1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))) - 1 / ((k : ℝ) * (Real.log N - Real.log k))| +
        ∑ k ∈ Finset.Icc Z (Nat.sqrt N), |(k : ℝ) / Real.log k - ((k : ℝ) - 1) / Real.log ((k : ℝ) - 1) - 1 / Real.log k| * |1 / ((k : ℝ) * (Real.log N - Real.log k))| := by
          rw [ ← abs_mul ];
          rw [ show ( ∑ p ∈ Icc Z N.sqrt with Nat.Prime p, 1 / ( p * ( Real.log N - Real.log p ) ) ) - ∑ k ∈ Icc Z N.sqrt, 1 / ( k * Real.log k * ( Real.log N - Real.log k ) ) = ( ( # ( filter Nat.Prime ( Icc Z N.sqrt ) ) - ( N.sqrt / Real.log N.sqrt - ( Z - 1 ) / Real.log ( Z - 1 ) ) ) * ( 1 / ( N.sqrt * ( Real.log N - Real.log N.sqrt ) ) ) ) - ∑ k ∈ Ico Z N.sqrt, ( # ( filter Nat.Prime ( Icc Z k ) ) - ( k / Real.log k - ( Z - 1 ) / Real.log ( Z - 1 ) ) ) * ( 1 / ( ( k + 1 ) * ( Real.log N - Real.log ( k + 1 ) ) ) - 1 / ( k * ( Real.log N - Real.log k ) ) ) + ∑ k ∈ Icc Z N.sqrt, ( k / Real.log k - ( k - 1 ) / Real.log ( k - 1 ) - 1 / Real.log k ) * ( 1 / ( k * ( Real.log N - Real.log k ) ) ) by linarith ];
          refine' le_trans ( abs_add_three _ _ _ ) _;
          gcongr;
          · rw [ abs_neg ];
            simpa only [ ← abs_mul ] using Finset.abs_sum_le_sum_abs _ _;
          · simpa only [ ← abs_mul ] using Finset.abs_sum_le_sum_abs _ _;
      convert h_triangle using 2;
      · rw [ abs_of_nonneg ( one_div_nonneg.mpr <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Real.log_le_log ( Nat.cast_pos.mpr <| Nat.sqrt_pos.mpr <| by nlinarith ) <| Nat.cast_le.mpr <| Nat.sqrt_le_self _ ) ] ; ring;
      · refine' Finset.sum_congr rfl fun x hx => _;
        rw [ abs_of_nonneg ( one_div_nonneg.mpr ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Real.log_le_log ( Nat.cast_pos.mpr ( by linarith [ Finset.mem_Icc.mp hx ] ) ) ( Nat.cast_le.mpr ( by nlinarith [ Finset.mem_Icc.mp hx, Nat.sqrt_le N ] ) ) ) ) ) ) ] ; ring;
  have h_sum_bound : ∑ k ∈ Finset.Ico Z (Nat.sqrt N), |((Finset.Icc Z k).filter Nat.Prime).card - ((k : ℝ) / Real.log k - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))| * |1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ))) - 1 / ((k : ℝ) * (Real.log N - Real.log k))| ≤ ∑ k ∈ Finset.Ico Z (Nat.sqrt N), (5 * (k : ℝ) / (Real.log k) ^ 2) * (1 / ((k : ℝ) * (Real.log N - Real.log k)) - 1 / ((k + 1 : ℝ) * (Real.log N - Real.log (k + 1 : ℝ)))) := by
    apply Finset.sum_le_sum fun x hx => ?_;
    gcongr;
    · convert pi_range_pnt_error x Z ( by linarith ) ( by linarith [ Finset.mem_Ico.mp hx ] ) using 1;
    · rw [ abs_sub_comm, abs_of_nonneg ];
      refine' sub_nonneg_of_le _;
      apply_rules [ G_decreasing ];
      · grind +qlia;
      · grind;
      · rw [ div_le_iff₀' ] <;> norm_num;
        rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> try nlinarith [ Finset.mem_Ico.mp hx ];
        · exact le_trans hN_hi ( Nat.pow_le_pow_left ( by nlinarith [ Finset.mem_Ico.mp hx, Nat.sqrt_le N ] ) 3 );
        · exact pow_pos ( by linarith [ Finset.mem_Ico.mp hx ] ) _;
      · rw [ le_div_iff₀' ] <;> norm_num;
        rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ Finset.mem_Ico.mp hx, Nat.sqrt_le N ];
  grind

/-
The weighted prime sum Σ_{Z≤p≤√N} 1/(p·log(N/p)) is approximately
    log(log N/log Z - 1)/log N with error ≤ 100/(log N)².
-/
lemma weighted_prime_sum_estimate (N Z : ℕ)
    (hZ : Z ≥ 88789) (hN_lo : Z ^ 2 ≤ N) (hN_hi : N ≤ Z ^ 3)
    (hlogN : Real.log (N : ℝ) ≥ 24) :
    |∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
        (1 / ((p : ℝ) * Real.log ((N : ℝ) / p))) -
      Real.log (Real.log N / Real.log Z - 1) / Real.log N| ≤
      100 / (Real.log (N : ℝ)) ^ 2 := by
  have := @abel_summation_error;
  specialize this N Z hZ hN_lo hN_hi hlogN;
  convert le_trans ( abs_sub_le _ _ _ ) ( add_le_add this ( riemann_to_integral_bound N Z hZ hN_lo hN_hi ) ) using 1;
  · exact congr_arg _ ( by rw [ Finset.sum_congr rfl ] ; intros; rw [ Real.log_div ( by norm_cast; nlinarith ) ( by norm_cast; nlinarith [ Finset.mem_Icc.mp ( by aesop : ‹ℕ› ∈ Finset.Icc Z N.sqrt ) ] ) ] );
  · ring


/-! ## Main theorem -/

/-! ### Step 0: Hypothesis transfer -/

/-
From the hypotheses of buchstab_core, Z = ⌈y⌉₊ ≥ 88789.
-/
lemma buchstab_Z_ge (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_hi : Real.log x / Real.log y ≤ 3) :
    (⌈y⌉₊ : ℕ) ≥ 88789 := by
  -- From x ≥ 88789³ and log x/log y ≤ 3: we get log x ≤ 3·log y, so x ≤ y³ (since exp is monotone). Thus y³ ≥ x ≥ 88789³, so y ≥ 88789.
  have hy_ge : y ^ 3 ≥ 88789 ^ 3 := by
    -- From the hypothesis hu_hi, we have log x ≤ 3 * log y. Exponentiating both sides gives x ≤ y^3.
    have h_exp : x ≤ y^3 := by
      rw [ div_le_iff₀ ( Real.log_pos ( by linarith ) ) ] at hu_hi;
      rw [ ← Real.log_le_log_iff ( by linarith [ le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ) ] ) ( by positivity ), Real.log_pow ] ; norm_num ; linarith;
    exact le_trans ( le_max_right _ _ ) hx |> le_trans <| h_exp;
  exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ sq_nonneg <| y^2 - 88789^2, Nat.le_ceil y ] ;

/-
From the hypotheses of buchstab_core, N = ⌊x⌋₊ ≤ Z³ = ⌈y⌉₊³.
-/
lemma buchstab_N_le_Z3 (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_hi : Real.log x / Real.log y ≤ 3) :
    ⌊x⌋₊ ≤ ⌈y⌉₊ ^ 3 := by
  have h_floor_le : x ≤ y^3 := by
    rw [ div_le_iff₀ ( Real.log_pos ( by linarith ) ) ] at hu_hi;
    rw [ ← Real.log_le_log_iff ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.exp_pos 48 ] ) ( by positivity ), Real.log_pow ] ; norm_num ; linarith;
  exact Nat.floor_le_of_le ( by exact le_trans h_floor_le ( by exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( Nat.le_ceil _ ) _ ) ( by norm_cast ) ) )

/-
From the hypotheses of buchstab_core, log N ≥ 24.
-/
lemma buchstab_logN_ge (x : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ)) :
    Real.log (⌊x⌋₊ : ℝ) ≥ 24 := by
  refine' le_trans _ ( Real.log_le_log _ <| Nat.cast_le.mpr <| Nat.floor_mono hx );
  · rw [ Real.le_log_iff_exp_le ] <;> norm_num;
    · refine' le_trans _ ( Nat.cast_le.mpr <| Nat.floor_mono <| le_max_left _ _ );
      rw [ show Real.exp 48 = ( Real.exp 24 ) ^ 2 by rw [ ← Real.exp_nat_mul ] ; norm_num ];
      nlinarith [ Nat.lt_floor_add_one ( Real.exp 24 ^ 2 ), Real.add_one_le_exp 24 ];
    · exact Nat.floor_pos.mpr ( le_trans ( by norm_num ) ( le_max_right _ _ ) );
  · exact Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| le_trans ( by norm_num ) <| le_max_left _ _

/-
From the hypotheses, N/(log N)² ≤ 2x/(log x)².
-/
lemma buchstab_NlogN_bound (x : ℝ)
    (hx : x ≥ Real.exp 48) :
    (⌊x⌋₊ : ℝ) / (Real.log (⌊x⌋₊ : ℝ)) ^ 2 ≤
      2 * x / (Real.log x) ^ 2 := by
  have h_log_N_ge : Real.log (⌊x⌋₊ : ℝ) ≥ Real.log x - 1 := by
    rw [ ge_iff_le, sub_le_iff_le_add, Real.log_le_iff_le_exp ];
    · rw [ Real.exp_add, Real.exp_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith [ Real.add_one_le_exp 48 ] ) ];
      nlinarith [ Nat.lt_floor_add_one x, Real.add_one_le_exp 1, Real.add_one_le_exp 48 ];
    · linarith [ Real.exp_pos 48 ];
  have h_log_x_ge : Real.log x ≥ 48 := by
    exact Real.log_exp 48 ▸ Real.log_le_log ( by positivity ) hx;
  have h_log_N_sq_ge : (Real.log (⌊x⌋₊ : ℝ)) ^ 2 ≥ (Real.log x) ^ 2 / 2 := by
    nlinarith [ Real.log_nonneg ( show ( ⌊x⌋₊ : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.floor_pos.mpr ( by linarith [ Real.add_one_le_exp 48 ] ) ) ) ];
  rw [ div_le_div_iff₀ ] <;> nlinarith [ Nat.floor_le ( show 0 ≤ x by linarith [ Real.exp_pos 48 ] ), Real.log_pos ( show 1 < x by linarith [ Real.add_one_le_exp 48 ] ) ]

/-! ### Step 1: Semiprime sum approximation -/

/-
The sum of π(p-1) over primes p in [Z, √N] is bounded by 16N/(log N)².
-/
lemma sum_pi_prev_bound (N Z : ℕ) (hZ : Z ≥ 88789) (hN : N ≥ 88789 ^ 2) :
    (∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
      ((Finset.Icc 1 (p - 1)).filter Nat.Prime).card : ℝ) ≤
    16 * N / (Real.log N) ^ 2 := by
  -- Each term in the sum is less than or equal to the number of primes less than or equal to $\sqrt{N}$.
  have h_term_le_pi_sqrt : ∀ p ∈ ((Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime), ((Finset.Icc 1 (p - 1)).filter Nat.Prime).card ≤ (Finset.card (primesUpTo (Real.sqrt N))) := by
    intros p hp
    have h_p_le_sqrt : p - 1 ≤ Nat.sqrt N := by
      grind;
    refine' Finset.card_mono _;
    intro x hx; simp_all +decide [ primesUpTo ];
    omega;
  -- The number of summands is at most $\pi(\sqrt{N})$.
  have h_card_le_pi_sqrt : (Finset.card ((Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime)) ≤ (Finset.card (primesUpTo (Real.sqrt N))) := by
    refine Finset.card_mono ?_;
    intro p hp; simp_all +decide [ primesUpTo ] ;
  refine le_trans ( Finset.sum_le_sum fun p hp => Nat.cast_le.mpr ( h_term_le_pi_sqrt p hp ) ) ?_;
  have := pi_sqrt_sq_bound N hN;
  norm_num at *;
  exact le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr h_card_le_pi_sqrt ) ( Nat.cast_nonneg _ ) ) ( by nlinarith )

/-
The pi_quot_approx error summed over primes is bounded by 16N/(log N)².
-/
lemma pi_quot_sum_error (N Z : ℕ) (hZ : Z ≥ 88789) (hN : N ≥ 88789 ^ 2)
    (hZ2 : Z ^ 2 ≤ N) (hNZ3 : N ≤ Z ^ 3) :
    |∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
        ((Finset.Icc 1 (N / p)).filter Nat.Prime).card -
      ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
        ((N : ℝ) / p / Real.log ((N : ℝ) / p))| ≤
    16 * N / (Real.log N) ^ 2 := by
  nontriviality;
  refine' le_trans ( _ : _ ≤ _ ) ( _ : _ ≤ _ );
  exact 8 * ( N : ℝ ) / ( Real.log N ) ^ 2 * ∑ p ∈ Finset.filter ( fun p => Nat.Prime p ) ( Finset.Icc Z ( Nat.sqrt N ) ), ( 1 / ( p : ℝ ) );
  · have h_sum_approx : ∀ p ∈ Finset.filter (fun p => Nat.Prime p) (Finset.Icc Z (Nat.sqrt N)), |((Finset.Icc 1 (N / p)).filter Nat.Prime).card - ((N : ℝ) / p) / Real.log ((N : ℝ) / p)| ≤ 8 * ((N : ℝ) / p) / (Real.log N) ^ 2 := by
      simp +zetaDelta at *;
      intro p hp₁ hp₂ hp₃; convert pi_quot_approx N p hp₃ ( by nlinarith [ Nat.sqrt_le N ] ) ( by linarith ) using 1;
    convert Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum h_sum_approx using 1 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring;
  · refine' le_trans ( mul_le_mul_of_nonneg_left ( reciprocal_prime_sum_bound N Z hZ hZ2 hNZ3 ) ( by positivity ) ) _;
    lia

lemma semiprime_approx (N Z : ℕ) (hZ : Z ≥ 88789) (hN : N ≥ 88789 ^ 2)
    (hZ2 : Z ^ 2 ≤ N) (hNZ3 : N ≤ Z ^ 3) (hlogN : Real.log (N : ℝ) ≥ 24) :
    |∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
        (((Finset.Icc p (N / p)).filter Nat.Prime).card : ℝ) -
      Real.log (Real.log N / Real.log Z - 1) * N / Real.log N| ≤
    150 * N / (Real.log N) ^ 2 := by
  revert hN hZ2 hNZ3 hlogN;
  intro hN hZ2 hNZ3 hlogN
  have h_sum : ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
       ((Finset.Icc p (N / p)).filter Nat.Prime).card =
      ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
      ((Finset.Icc 1 (N / p)).filter Nat.Prime).card -
      ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
      ((Finset.Icc 1 (p - 1)).filter Nat.Prime).card := by
        refine' eq_tsub_of_add_eq _;
        rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ];
        intro p hp; rw [ ← Finset.card_union_of_disjoint ] ; congr; ext; simp +decide ;
        · constructor <;> intro h <;> rcases h with ⟨ ⟨ h₁, h₂ ⟩, h₃ ⟩ <;> simp_all +decide [ Nat.le_sqrt ];
          · exact h₃.pos;
          · rw [ Nat.le_div_iff_mul_le hp.2.pos ] ; nlinarith [ Nat.sub_add_cancel hp.2.pos ];
          · exact Classical.or_iff_not_imp_left.2 fun h => Nat.le_sub_one_of_lt <| lt_of_not_ge h;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ), Nat.sub_add_cancel ( show 1 ≤ p from Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) ] ;
  have h_sum_bound : |∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
      ((Finset.Icc 1 (N / p)).filter Nat.Prime).card -
      N * (Real.log (Real.log N / Real.log Z - 1)) / Real.log N| ≤
      116 * N / (Real.log N) ^ 2 := by
        have h_sum_bound : |∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
              ((Finset.Icc 1 (N / p)).filter Nat.Prime).card -
              ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
              ((N : ℝ) / p / Real.log ((N : ℝ) / p))| ≤
              16 * N / (Real.log N) ^ 2 := by
                convert pi_quot_sum_error N Z hZ hN hZ2 hNZ3 using 1;
        have h_sum_bound : |∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
                      ((N : ℝ) / p / Real.log ((N : ℝ) / p)) -
                      N * (Real.log (Real.log N / Real.log Z - 1)) / Real.log N| ≤
                      100 * N / (Real.log N) ^ 2 := by
                        have := @weighted_prime_sum_estimate N Z hZ hZ2 hNZ3 hlogN;
                        convert mul_le_mul_of_nonneg_left this ( Nat.cast_nonneg N ) using 1 <;> ring_nf;
                        rw [ show ( - ( N * log ( -1 + log N * ( log Z ) ⁻¹ ) * ( log N ) ⁻¹ ) + ∑ x ∈ Icc Z N.sqrt with Nat.Prime x, N * ( x : ℝ ) ⁻¹ * ( log ( N * ( x : ℝ ) ⁻¹ ) ) ⁻¹ ) = N * ( - ( log ( -1 + log N * ( log Z ) ⁻¹ ) * ( log N ) ⁻¹ ) + ∑ x ∈ Icc Z N.sqrt with Nat.Prime x, ( x : ℝ ) ⁻¹ * ( log ( N * ( x : ℝ ) ⁻¹ ) ) ⁻¹ ) by simp +decide [ mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ] ; rw [ abs_mul, abs_of_nonneg ( by positivity ) ];
        grind;
  have h_sum_bound : ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime,
        ((Finset.Icc 1 (p - 1)).filter Nat.Prime).card ≤
        16 * N / (Real.log N) ^ 2 := by
          convert sum_pi_prev_bound N Z hZ hN using 1;
          norm_cast;
  rw [ abs_le ] at *;
  rw [ ← @Nat.cast_inj ℝ ] at * ; norm_num at *;
  rw [ Nat.cast_sub ] at * <;> norm_num at *;
  · constructor <;> ring_nf at * <;> linarith [ show ( 0 : ℝ ) ≤ ∑ x ∈ Icc Z N.sqrt with Nat.Prime x, ( # ( filter Nat.Prime ( Icc 1 ( x - 1 ) ) ) : ℝ ) from Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ] ;
  · refine' Finset.sum_le_sum fun p hp => _;
    refine' Finset.card_mono _;
    simp_all +decide [ Finset.subset_iff ];
    exact fun x hx₁ hx₂ hx₃ => by rw [ Nat.le_div_iff_mul_le hp.2.pos ] ; nlinarith only [ hx₁, hx₂, hp.1.2, Nat.sub_add_cancel hp.2.pos, Nat.sqrt_le N ] ;

/-! ### Step 2: Full NZ approximation -/

/-
Sieve approximation in terms of N, Z: combines decomp, primes, semiprimes.
-/
lemma sieve_NZ_approx (N Z : ℕ) (hZ : Z ≥ 88789) (hN : N ≥ 88789 ^ 2)
    (hZ2 : Z ^ 2 ≤ N) (hNZ3 : N ≤ Z ^ 3) (hlogN : Real.log (N : ℝ) ≥ 24) :
    |((sievePhi N Z : ℕ) : ℝ) -
      ((1 + Real.log (Real.log N / Real.log Z - 1)) * N / Real.log N -
       ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))| ≤
    175 * N / (Real.log N) ^ 2 := by
  -- By sievePhi_decomp_bound: |sievePhi(N,Z) - (1 + P + S)| ≤ 1, where P = #{primes in [Z,N]} and S = Σ_p #{primes in [p, N/p]}.
  have h_decomp : |(sievePhi N Z : ℝ) - (1 + ((Finset.Icc Z N).filter Nat.Prime).card + ∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime, ((Finset.Icc p (N / p)).filter Nat.Prime).card)| ≤ 1 := by
    convert sievePhi_decomp_bound N Z ( by linarith ) ( by linarith ) using 1 ; norm_cast;
  -- By primes_in_range_approx: |P - (N/logN - (Z-1)/log(Z-1))| ≤ 20N/(logN)².
  have h_primes : |((Finset.Icc Z N).filter Nat.Prime).card - ((N : ℝ) / Real.log N - ((Z : ℝ) - 1) / Real.log ((Z : ℝ) - 1))| ≤ 20 * (N : ℝ) / (Real.log N) ^ 2 := by
    convert primes_in_range_approx N Z hZ hZ2 using 1;
  -- By semiprime_approx: |S - log(logN/logZ - 1)·N/logN| ≤ 150N/(logN)².
  have h_semiprimes : |∑ p ∈ (Finset.Icc Z (Nat.sqrt N)).filter Nat.Prime, ((Finset.Icc p (N / p)).filter Nat.Prime).card - Real.log (Real.log N / Real.log Z - 1) * N / Real.log N| ≤ 150 * N / (Real.log N) ^ 2 := by
    convert semiprime_approx N Z hZ hN hZ2 hNZ3 hlogN using 1;
    norm_num;
  -- Since $N \geq 88789^2$, we have $N / (\log N)^2 \geq 1$.
  have h_N_logN_sq_ge_1 : (N : ℝ) / (Real.log N) ^ 2 ≥ 1 := by
    rw [ ge_iff_le, le_div_iff₀ ] <;> try positivity;
    have := Real.log_le_sub_one_of_pos ( show 0 < Real.sqrt N / 2 by exact div_pos ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) ) ) zero_lt_two );
    rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] at this;
    nlinarith only [ this, Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two, Real.sqrt_nonneg N, Real.sq_sqrt <| Nat.cast_nonneg N, show ( N :ℝ ) ≥ 88789 ^ 2 by exact_mod_cast hN, hlogN ];
  grind

/-! ### Step 3: Transfer bound on t/log t -/

/-
|t/log t - s/log s| ≤ |t - s| / log(min t s) for t, s > 1.
-/
lemma t_div_logt_diff_bound (t s : ℝ) (ht : t ≥ 3) (hs : s ≥ 3) (hts : |t - s| ≤ 1) :
    |t / Real.log t - s / Real.log s| ≤ 2 / Real.log (min t s) := by
  -- By the Mean Value Theorem, there exists some $c$ between $t$ and $s$ such that $t/\log t - s/\log s = (t-s) \cdot f'(c)$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Icc (min t s) (max t s), t / Real.log t - s / Real.log s = (t - s) * (Real.log c - 1) / (Real.log c)^2 := by
    cases eq_or_ne t s <;> simp_all +decide [ div_eq_mul_inv ];
    cases' lt_or_gt_of_ne ‹_› with h h;
    · have := exists_deriv_eq_slope ( f := fun x => x * ( Real.log x ) ⁻¹ ) h;
      obtain ⟨ c, hc₁, hc₂ ⟩ := this ( by exact ContinuousOn.mul continuousOn_id <| ContinuousOn.inv₀ ( Real.continuousOn_log.mono <| by intro x hx; exact ne_of_gt <| by linarith [ hx.1 ] ) fun x hx => ne_of_gt <| Real.log_pos <| by linarith [ hx.1 ] ) ( by exact fun x hx => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.mul differentiableAt_id <| DifferentiableAt.inv ( Real.differentiableAt_log <| by linarith [ hx.1 ] ) <| ne_of_gt <| Real.log_pos <| by linarith [ hx.1 ] ) ; use c; simp_all +decide [ sub_eq_iff_eq_add ];
      norm_num [ show c ≠ 0 by linarith, show Real.log c ≠ 0 by exact ne_of_gt <| Real.log_pos <| by linarith, show s ≠ 0 by linarith, show t ≠ 0 by linarith, Real.differentiableAt_log, differentiableAt_inv ] at *;
      grind;
    · have := exists_deriv_eq_slope ( f := fun x => x / Real.log x ) h;
      obtain ⟨ c, hc₁, hc₂ ⟩ := this ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_id ( Real.continuousAt_log ( by linarith [ hx.1 ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ hx.1 ] ) ) ) ) ( by exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.div ( differentiableAt_id ) ( Real.differentiableAt_log ( by linarith [ hx.1 ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ hx.1 ] ) ) ) ) ) ; use c; norm_num [ Real.differentiableAt_log, show c ≠ 0 by linarith [ hc₁.1 ], show Real.log c ≠ 0 by exact ne_of_gt ( Real.log_pos ( by linarith [ hc₁.1 ] ) ) ] at *;
      norm_num [ show c ≠ 0 by linarith, show Real.log c ≠ 0 by exact ne_of_gt ( Real.log_pos ( by linarith ) ), Real.differentiableAt_log, mul_comm, div_eq_mul_inv ] at *;
      grind;
  -- Since $c \geq \min(t, s)$, we have $\log c \geq \log(\min(t, s))$.
  have h_log_c_ge_log_min : Real.log c ≥ Real.log (min t s) := by
    exact Real.log_le_log ( by positivity ) hc.1.1;
  -- Since $c \geq \min(t, s)$, we have $|\log c - 1| \leq \log c$.
  have h_log_c_minus_one_le_log_c : |Real.log c - 1| ≤ Real.log c := by
    exact abs_le.mpr ⟨ by linarith [ show 1 ≤ Real.log c from by rw [ Real.le_log_iff_exp_le ( by cases min_cases t s <;> linarith [ hc.1.1 ] ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num ; cases min_cases t s <;> linarith [ hc.1.1 ] ) ], by linarith [ show 1 ≤ Real.log c from by rw [ Real.le_log_iff_exp_le ( by cases min_cases t s <;> linarith [ hc.1.1 ] ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num ; cases min_cases t s <;> linarith [ hc.1.1 ] ) ] ⟩;
  rw [ hc.2, abs_div, abs_mul ];
  nontriviality;
  rw [ div_le_div_iff₀ ] <;> norm_num at *;
  · exact le_trans ( mul_le_mul_of_nonneg_right ( mul_le_of_le_one_left ( abs_nonneg _ ) hts ) ( Real.log_nonneg ( by cases min_cases t s <;> linarith ) ) ) ( by nlinarith [ abs_le.mp h_log_c_minus_one_le_log_c, Real.log_nonneg ( show 1 ≤ min t s by cases min_cases t s <;> linarith ) ] );
  · exact sq_pos_of_pos ( lt_of_lt_of_le ( Real.log_pos ( by cases min_cases t s <;> linarith ) ) h_log_c_ge_log_min );
  · exact Real.log_pos ( by cases min_cases t s <;> linarith )

/-
N≥ 88789² under the hypotheses.
-/
lemma buchstab_N_ge_sq (x : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ)) :
    ⌊x⌋₊ ≥ 88789 ^ 2 := by
  exact Nat.le_floor <| le_trans ( by norm_num ) <| le_trans ( le_max_right _ _ ) hx

/-
Transfer: |(N:ℝ)/log N - x/log x| ≤ x/(log x)² for N = ⌊x⌋₊.
-/
lemma floor_div_log_transfer (x : ℝ) (hx : x ≥ Real.exp 48) :
    |(⌊x⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ) - x / Real.log x| ≤
    x / (Real.log x) ^ 2 := by
  have h_diff_bound : |(⌊x⌋₊ : ℝ) / Real.log ⌊x⌋₊ - x / Real.log x| ≤ 2 / Real.log (⌊x⌋₊) := by
    convert t_div_logt_diff_bound ( ⌊x⌋₊ : ℝ ) x _ _ _ using 1 <;> norm_num;
    · rw [ min_eq_left ( Nat.floor_le ( by linarith [ Real.exp_pos 48 ] ) ) ];
    · exact Nat.le_floor <| le_trans ( by exact le_of_lt <| by have := Real.exp_one_gt_d9.le; norm_num1 at *; rw [ show Real.exp 48 = ( Real.exp 1 ) ^ 48 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_lt_of_le ( by norm_num ) <| pow_le_pow_left₀ ( by positivity ) this _ ) hx;
    · exact le_trans ( by linarith [ Real.add_one_le_exp 48 ] ) hx;
    · exact abs_sub_le_iff.mpr ⟨ by linarith [ Nat.floor_le ( show 0 ≤ x by linarith [ Real.exp_pos 48 ] ) ], by linarith [ Nat.lt_floor_add_one x ] ⟩;
  -- Since $x \geq e^{48}$, we have $\log \lfloor x \rfloor \geq \log (e^{48} - 1) \geq 47$.
  have h_log_floor : Real.log ⌊x⌋₊ ≥ 47 := by
    have h_log_floor : Real.log ⌊x⌋₊ ≥ Real.log (Real.exp 48 - 1) := by
      exact Real.log_le_log ( by linarith [ Real.add_one_le_exp 48 ] ) ( by linarith [ Nat.lt_floor_add_one x ] );
    refine le_trans ?_ h_log_floor;
    rw [ Real.le_log_iff_exp_le ] <;> norm_num;
    rw [ show ( 48 : ℝ ) = 47 + 1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1, Real.add_one_le_exp 47 ];
  refine le_trans h_diff_bound ?_;
  rw [ div_le_div_iff₀ ] <;> try positivity;
  · have h_log_x : Real.log x ≤ Real.sqrt x := by
      have := Real.log_le_sub_one_of_pos ( show 0 < Real.sqrt x / Real.exp 1 by exact div_pos ( Real.sqrt_pos.mpr ( by linarith [ Real.exp_pos 48 ] ) ) ( Real.exp_pos 1 ) );
      rw [ Real.log_div ( by exact ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ Real.exp_pos 48 ] ) ( by positivity ), Real.log_sqrt <| by linarith [ Real.exp_pos 48 ], Real.log_exp ] at this ; nlinarith [ Real.add_one_le_exp 1, Real.sqrt_nonneg x, Real.sq_sqrt <| show 0 ≤ x by linarith [ Real.exp_pos 48 ], mul_div_cancel₀ ( Real.sqrt x ) <| ne_of_gt <| Real.exp_pos 1 ];
    nlinarith [ Real.log_nonneg ( show x ≥ 1 by linarith [ Real.add_one_le_exp 48 ] ), Real.mul_self_sqrt ( show 0 ≤ x by linarith [ Real.add_one_le_exp 48 ] ), Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith [ Real.add_one_le_exp 48 ] ) <| Nat.floor_le <| show 0 ≤ x by linarith [ Real.add_one_le_exp 48 ] ];
  · exact sq_pos_of_pos <| Real.log_pos <| lt_of_lt_of_le ( by norm_num ) hx

/-
Transfer: |(⌈y⌉₊-1)/log(⌈y⌉₊-1) - y/log y| ≤ y/(log y)².
-/
lemma ceil_div_log_transfer (y : ℝ) (hy : y ≥ 88789) :
    |((⌈y⌉₊ : ℝ) - 1) / Real.log ((⌈y⌉₊ : ℝ) - 1) - y / Real.log y| ≤
    y / (Real.log y) ^ 2 := by
  -- By t_div_logt_diff_bound: |(⌈y⌉₊-1)/log(⌈y⌉₊-1) - y/logy| ≤ 2/log(min(⌈y⌉₊-1, y)).
  have h_t_diff : |(↑⌈y⌉₊ - 1 : ℝ) / Real.log (↑⌈y⌉₊ - 1) - y / Real.log y| ≤ 2 / Real.log (min (↑⌈y⌉₊ - 1 : ℝ) y) := by
    apply t_div_logt_diff_bound;
    · linarith [ Nat.le_ceil y, show ( ⌈y⌉₊ : ℝ ) ≥ 88789 by exact_mod_cast Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil y ] ];
    · linarith;
    · exact abs_le.mpr ⟨ by linarith [ Nat.le_ceil y ], by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ y by linarith ) ] ⟩;
  refine le_trans h_t_diff ?_;
  rw [ div_le_div_iff₀ ];
  · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by linarith ) ( show ( min ( ⌈y⌉₊ - 1 : ℝ ) y ) ≥ y - 1 by cases min_cases ( ⌈y⌉₊ - 1 : ℝ ) y <;> linarith [ Nat.le_ceil y ] ) ) <| by positivity );
    have h_log_bound : Real.log y ≤ Real.sqrt y := by
      have := Real.log_le_sub_one_of_pos ( by positivity : 0 < Real.sqrt y / 2 );
      rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] at this;
      have := Real.log_two_lt_d9 ; norm_num at * ; linarith;
    have h_log_bound : Real.log (y - 1) ≥ 11 := by
      rw [ ge_iff_le, Real.le_log_iff_exp_le ( by linarith ) ];
      exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 11 = ( Real.exp 1 ) ^ 11 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) ( sub_le_sub_right hy _ );
    nlinarith [ Real.mul_self_sqrt ( show 0 ≤ y by linarith ), Real.log_nonneg ( show 1 ≤ y by linarith ) ];
  · exact Real.log_pos <| by cases min_cases ( ⌈y⌉₊ - 1 : ℝ ) y <;> linarith [ Nat.le_ceil y ] ;
  · exact sq_pos_of_pos <| Real.log_pos <| by linarith

/-
In the edge case, u = log x/log y is close to 2:
    log(u-1) ≤ 3/(y·log y).
-/
lemma edge_case_log_u_bound (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_lo : 2 ≤ Real.log x / Real.log y)
    (hZ2N : ⌊x⌋₊ < ⌈y⌉₊ ^ 2) :
    Real.log (Real.log x / Real.log y - 1) ≤
    3 / (y * Real.log y) := by
  -- Since $x < (y + 1)^2$, we have $\log x \leq \log((y + 1)^2) = 2 \log(y + 1)$.
  have h_log_x_le : Real.log x ≤ 2 * Real.log (y + 1) := by
    rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_num <;> try positivity;
    · contrapose! hZ2N;
      exact Nat.le_floor <| by push_cast; nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ y by positivity ), Nat.ceil_le.mp <| Nat.le_refl <| ⌈y⌉₊ ] ;
    · exact lt_of_lt_of_le ( by positivity ) hx;
  -- Using the inequality $\log(y + 1) \leq \log y + \frac{1}{y}$, we get $2 \log(y + 1) \leq 2 \log y + \frac{2}{y}$.
  have h_log_y_plus_1_le : 2 * Real.log (y + 1) ≤ 2 * Real.log y + 2 / y := by
    have h_log_y_plus_1_le : Real.log (y + 1) ≤ Real.log y + 1 / y := by
      rw [ Real.log_le_iff_le_exp, Real.exp_add, Real.exp_log ] <;> try linarith;
      nlinarith [ Real.add_one_le_exp ( 1 / y ), one_div_mul_cancel ( by linarith : y ≠ 0 ) ];
    convert mul_le_mul_of_nonneg_left h_log_y_plus_1_le zero_le_two using 1 ; ring;
  refine' le_trans ( Real.log_le_sub_one_of_pos _ ) _;
  · linarith;
  · ring_nf at *;
    nlinarith [ inv_pos.mpr ( Real.log_pos ( show y > 1 by linarith ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show y > 1 by linarith ) ) ), inv_pos.mpr ( show 0 < y by linarith ), mul_inv_cancel₀ ( ne_of_gt ( show 0 < y by linarith ) ), Real.log_pos ( show y > 1 by linarith ) ]

/-
The log ratios logN/logZ and logx/logy are close.
    |logN/logZ - logx/logy| ≤ 1/logx.
-/
lemma log_ratio_close (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_hi : Real.log x / Real.log y ≤ 3) :
    |Real.log (⌊x⌋₊ : ℝ) / Real.log (⌈y⌉₊ : ℝ) -
     Real.log x / Real.log y| ≤ 1 / Real.log x := by
  -- By the properties of logarithms and the definitions of floor and ceiling, we can bound the differences.
  have h_floor : |Real.log ⌊x⌋₊ - Real.log x| ≤ 1 / (x - 1) := by
    have h_logN_logx : Real.log x - Real.log ⌊x⌋₊ ≤ 1 / (x - 1) := by
      rw [ ← Real.log_div ( by linarith [ Real.exp_pos 48, le_max_left ( Real.exp 48 ) ( 88789 ^ 3 : ℝ ) ] ) ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.floor_pos.mpr <| by linarith [ Real.add_one_le_exp 48, le_max_left ( Real.exp 48 ) ( 88789 ^ 3 : ℝ ) ] ) ];
      refine' le_trans ( Real.log_le_sub_one_of_pos ( div_pos ( by linarith [ Real.add_one_le_exp 48, le_max_left ( Real.exp 48 ) ( 88789 ^ 3 : ℝ ) ] ) ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith [ Real.add_one_le_exp 48, le_max_left ( Real.exp 48 ) ( 88789 ^ 3 : ℝ ) ] ) ) ) _;
      rw [ div_sub_one, div_le_div_iff₀ ] <;> nlinarith [ Nat.lt_floor_add_one x, show ( ⌊x⌋₊ : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.floor_pos.mpr <| by linarith [ Real.add_one_le_exp 48, le_max_left ( Real.exp 48 ) ( 88789 ^ 3 : ℝ ) ] ), Real.add_one_le_exp 48, le_max_right ( Real.exp 48 ) ( 88789 ^ 3 : ℝ ) ];
    rw [ abs_sub_comm, abs_of_nonneg ] <;> linarith [ Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) <| Nat.floor_le <| show 0 ≤ x by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ]
  have h_ceil : |Real.log ⌈y⌉₊ - Real.log y| ≤ 1 / y := by
    rw [ abs_of_nonneg ];
    · rw [ ← Real.log_div ( by positivity ) ( by positivity ) ];
      exact le_trans ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by ring_nf; nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ y by positivity ), mul_inv_cancel₀ ( show y ≠ 0 by positivity ) ] );
    · exact sub_nonneg_of_le <| Real.log_le_log ( by positivity ) <| Nat.le_ceil _;
  -- Using the bounds on the differences of logarithms, we can bound the difference of the ratios.
  have h_ratio_bound : |Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ - Real.log x / Real.log y| ≤ |Real.log ⌊x⌋₊ - Real.log x| / Real.log ⌈y⌉₊ + |Real.log ⌈y⌉₊ - Real.log y| * Real.log x / (Real.log ⌈y⌉₊ * Real.log y) := by
    rw [ div_sub_div, abs_div ];
    · rw [ div_add_div, div_le_div_iff₀ ];
      · rw [ abs_of_nonneg ( mul_nonneg ( Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.ceil_pos.mpr <| by positivity ) <| Real.log_nonneg <| by linarith ) ];
        rw [ show log ⌊x⌋₊ * log y - log ⌈y⌉₊ * log x = ( log ⌊x⌋₊ - log x ) * log y - ( log ⌈y⌉₊ - log y ) * log x by ring ];
        refine' le_trans ( mul_le_mul_of_nonneg_right ( abs_sub _ _ ) ( mul_nonneg ( Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.ceil_pos.mpr <| by positivity ) <| mul_nonneg ( Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.ceil_pos.mpr <| by positivity ) <| Real.log_nonneg <| by linarith ) ) _;
        rw [ abs_mul, abs_mul, abs_of_nonneg ( Real.log_nonneg <| show ( y : ℝ ) ≥ 1 by linarith ), abs_of_nonneg ( Real.log_nonneg <| show ( x : ℝ ) ≥ 1 by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) ] ; ring_nf ; norm_num;
      · exact abs_pos.mpr ( mul_ne_zero ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.lt_ceil.mpr ( by norm_num; linarith ) ) ) ) ) ( ne_of_gt ( Real.log_pos ( by linarith ) ) ) );
      · exact mul_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.lt_ceil.mpr <| by norm_num; linarith ) ( mul_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.lt_ceil.mpr <| by norm_num; linarith ) ( Real.log_pos <| by linarith ) );
      · exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.lt_ceil.mpr <| by norm_num; linarith;
      · exact ne_of_gt ( mul_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.lt_ceil.mpr ( by norm_num; linarith ) ) ) ) ( Real.log_pos ( by linarith ) ) );
    · exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.lt_ceil.mpr <| by norm_num; linarith;
    · exact ne_of_gt <| Real.log_pos <| by linarith;
  -- Using the bounds on the differences of logarithms, we can further simplify the expression.
  have h_simplify : |Real.log ⌊x⌋₊ - Real.log x| / Real.log ⌈y⌉₊ + |Real.log ⌈y⌉₊ - Real.log y| * Real.log x / (Real.log ⌈y⌉₊ * Real.log y) ≤ 3 / ((x - 1) * Real.log x) + 9 / (y * Real.log x) := by
    refine' add_le_add _ _;
    · refine' le_trans ( div_le_div_of_nonneg_right h_floor <| Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.ceil_pos.mpr <| by positivity ) _;
      rw [ div_div, div_le_div_iff₀ ];
      · rw [ div_le_iff₀ ( Real.log_pos <| by linarith ) ] at hu_hi;
        nlinarith [ show ( ⌈y⌉₊ : ℝ ) ≥ y by exact Nat.le_ceil _, Real.log_le_log ( by positivity ) ( show ( ⌈y⌉₊ : ℝ ) ≥ y by exact Nat.le_ceil _ ), Real.log_pos ( show ( y : ℝ ) > 1 by linarith ), show ( x : ℝ ) ≥ 1 by exact le_trans ( by norm_num ) hx ];
      · exact mul_pos ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.lt_ceil.mpr <| by norm_num; linarith );
      · exact mul_pos ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) ( Real.log_pos ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) );
    · refine' le_trans ( div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_right h_ceil <| Real.log_nonneg <| by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) <| mul_nonneg ( Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.ceil_pos.mpr <| by linarith ) <| Real.log_nonneg <| by linarith ) _;
      rw [ div_mul_eq_mul_div, div_div, div_le_div_iff₀ ];
      · -- Using the bounds on the logarithms, we can simplify the inequality.
        have h_log_bounds : Real.log x ≤ 3 * Real.log y ∧ Real.log ⌈y⌉₊ ≥ Real.log y := by
          exact ⟨ by rw [ div_le_iff₀ ( Real.log_pos <| by linarith ) ] at hu_hi; linarith, Real.log_le_log ( by linarith ) <| Nat.le_ceil _ ⟩;
        nlinarith [ show 0 ≤ y * Real.log x by exact mul_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) ), show 0 ≤ y * Real.log y by exact mul_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ), Real.log_nonneg ( show 1 ≤ y by linarith ) ];
      · exact mul_pos ( by positivity ) ( mul_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.lt_ceil.mpr ( by norm_num; linarith ) ) ) ) ( Real.log_pos ( by linarith ) ) );
      · exact mul_pos ( by positivity ) ( Real.log_pos ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) );
  -- Since $x \geq \exp 48$, we have $x - 1 \geq \exp 48 - 1 \geq 24$.
  have h_x_minus_one : x - 1 ≥ 24 := by
    linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ];
  refine le_trans h_ratio_bound <| h_simplify.trans ?_;
  rw [ div_add_div, div_le_div_iff₀ ] <;> try nlinarith [ Real.log_pos <| show 1 < x by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ], Real.log_pos <| show 1 < y by linarith ];
  · rw [ div_le_iff₀ ( Real.log_pos <| by linarith ) ] at hu_hi;
    have h_log_x_ge_48 : Real.log x ≥ 48 := by
      exact Real.log_exp 48 ▸ Real.log_le_log ( by positivity ) ( le_trans ( le_max_left _ _ ) hx );
    nlinarith [ mul_le_mul_of_nonneg_left h_log_x_ge_48 <| show 0 ≤ y by linarith, mul_le_mul_of_nonneg_left h_log_x_ge_48 <| show 0 ≤ x - 1 by linarith, Real.log_le_sub_one_of_pos <| show 0 < y by linarith, Real.log_le_sub_one_of_pos <| show 0 < x by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ];
  · exact mul_pos ( mul_pos ( by linarith ) ( Real.log_pos ( by linarith ) ) ) ( mul_pos ( by linarith ) ( Real.log_pos ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) ) )

/-
y/(logy)² ≤ 9x/(logx)² when 2 ≤ logx/logy ≤ 3 and y ≤ √x.
-/
lemma y_log_transfer (x y : ℝ)
    (hx : x ≥ Real.exp 48)
    (hy : y ≥ 88789)
    (hu_lo : 2 ≤ Real.log x / Real.log y) :
    y / (Real.log y) ^ 2 ≤ 12 * x / (Real.log x) ^ 2 := by
  have h_log_y_le_log_x_div_2 : Real.log y ≤ Real.log x / 2 := by
    rw [ le_div_iff₀ ] at hu_lo <;> linarith [ Real.log_pos ( show y > 1 by linarith ) ];
  have h_log_x_ge_48 : Real.log x ≥ 48 := by
    exact Real.log_exp 48 ▸ Real.log_le_log ( by positivity ) hx;
  have h_sqrt_x_le_x_div_log_x_sq : Real.sqrt x / 121 ≤ 12 * x / (Real.log x)^2 := by
    have h_sqrt_x_le_x_div_log_x_sq : Real.log x ≤ 38.1 * x^(1/4 : ℝ) := by
      have := Real.log_le_sub_one_of_pos ( show 0 < x ^ ( 1 / 4 : ℝ ) / ( Real.exp 12 ) by exact div_pos ( Real.rpow_pos_of_pos ( by linarith [ Real.exp_pos 48 ] ) _ ) ( Real.exp_pos _ ) );
      rw [ Real.log_div ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( by linarith [ Real.exp_pos 48 ] ) _ ) ) ( by positivity ), Real.log_rpow ( by linarith [ Real.exp_pos 48 ] ), Real.log_exp ] at this ; norm_num at * ; nlinarith [ Real.add_one_le_exp 12, Real.rpow_pos_of_pos ( by linarith [ Real.exp_pos 48 ] : 0 < x ) ( 1 / 4 : ℝ ), mul_div_cancel₀ ( x ^ ( 1 / 4 : ℝ ) ) ( ne_of_gt ( Real.exp_pos 12 ) ) ];
    rw [ div_le_div_iff₀ ] <;> try positivity;
    refine le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) h_sqrt_x_le_x_div_log_x_sq 2 ) ( Real.sqrt_nonneg _ ) ) ?_ ; ring_nf ; norm_num;
    rw [ Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith [ Real.exp_pos 48 ] ) ] ; norm_num ; ring_nf ; norm_num [ ← Real.rpow_add ( by linarith [ Real.exp_pos 48 ] : 0 < x ) ];
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith [ Real.exp_pos 48 ] ) ] ; norm_num ; linarith [ Real.exp_pos 48 ];
  refine le_trans ?_ h_sqrt_x_le_x_div_log_x_sq;
  gcongr;
  · rw [ Real.le_sqrt ] <;> try linarith [ Real.exp_pos 48 ];
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by linarith [ Real.exp_pos 48 ] ), Real.log_pow ] ; norm_num ; linarith;
  · have h_log_y_ge_11 : Real.log y ≥ 11 := by
      rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ];
      exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 11 = ( Real.exp 1 ) ^ 11 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) hy;
    nlinarith only [ h_log_y_ge_11 ]

/-
Both cases: combine sieve_NZ_approx (or edge case) with transfer.
-/
lemma buchstab_core_main_case (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_lo : 2 ≤ Real.log x / Real.log y)
    (hu_hi : Real.log x / Real.log y ≤ 3)
    (hZ2N : ⌈y⌉₊ ^ 2 ≤ ⌊x⌋₊) :
    |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) -
      ((1 + Real.log (Real.log x / Real.log y - 1)) * x / Real.log x -
       y / Real.log y)| ≤
      500 * x / (Real.log x) ^ 2 := by
  have h1 := buchstab_N_ge_sq x hx
  have h2 := buchstab_NlogN_bound x (by
  exact le_trans ( le_max_left _ _ ) hx)
  have h3 := floor_div_log_transfer x (by
  exact le_trans ( le_max_left _ _ ) hx)
  have h4 := ceil_div_log_transfer y (by
  contrapose! hu_hi;
  rw [ lt_div_iff₀ ( Real.log_pos <| by linarith ) ];
  rw [ ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_num at * <;> try linarith;
  · exact lt_of_lt_of_le ( pow_lt_pow_left₀ hu_hi ( by linarith ) ( by norm_num ) ) ( by linarith );
  · positivity)
  have h5 := log_ratio_close x y hx hy hu_hi
  have h6 := y_log_transfer x y (by
  exact le_trans ( le_max_left _ _ ) hx) (by
  contrapose! hu_lo;
  rw [ div_le_iff₀ ( Real.log_pos <| by linarith ) ] at hu_hi;
  rw [ div_lt_iff₀ ( Real.log_pos <| by linarith ) ];
  rw [ ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_num at * <;> try linarith;
  · rw [ Real.log_le_iff_le_exp ( by linarith ) ] at hu_hi;
    rw [ show 3 * Real.log y = Real.log ( y ^ 3 ) by rw [ Real.log_pow ] ; norm_num, Real.exp_log ( by positivity ) ] at hu_hi ; nlinarith [ Nat.le_ceil y, pow_two ( ⌈y⌉₊ - y : ℝ ) ];
  · positivity) hu_lo;
  have h7 := sieve_NZ_approx ⌊x⌋₊ ⌈y⌉₊ (buchstab_Z_ge x y hx hy hu_hi) h1 hZ2N (buchstab_N_le_Z3 x y hx hy hu_hi) (buchstab_logN_ge x hx);
  -- Apply the triangle inequality to combine the bounds.
  have h8 : abs ((1 + Real.log (Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ - 1)) * ⌊x⌋₊ / Real.log ⌊x⌋₊ - (1 + Real.log (Real.log x / Real.log y - 1)) * x / Real.log x) ≤ 2 * x / Real.log x ^ 2 + x / Real.log x ^ 2 := by
    have h8 : abs ((1 + Real.log (Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ - 1)) * ⌊x⌋₊ / Real.log ⌊x⌋₊ - (1 + Real.log (Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ - 1)) * x / Real.log x) ≤ 2 * x / Real.log x ^ 2 := by
      have h8 : abs (1 + Real.log (Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ - 1)) ≤ 2 := by
        have h8 : 1 ≤ Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ - 1 ∧ Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ - 1 ≤ 2 := by
          have h8 : Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ ≥ 2 := by
            have h8 : Real.log ⌊x⌋₊ ≥ 2 * Real.log ⌈y⌉₊ := by
              rw [ ← Real.log_rpow, ge_iff_le, Real.log_le_log_iff ] <;> norm_cast <;> positivity;
            exact le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.lt_ceil.mpr <| by norm_num; linarith ) |>.2 h8
          have h9 : Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ ≤ 3 := by
            have h9 : Real.log ⌊x⌋₊ ≤ Real.log x := by
              exact Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) <| Nat.floor_le <| by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ;
            have h10 : Real.log ⌈y⌉₊ ≥ Real.log y := by
              exact Real.log_le_log ( by positivity ) ( Nat.le_ceil _ );
            exact le_trans ( div_le_div_of_nonneg_left ( Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.floor_pos.mpr <| by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) ( Real.log_pos <| by linarith ) h10 ) ( by simpa using hu_hi.trans' <| div_le_div_of_nonneg_right h9 <| Real.log_nonneg <| by linarith )
          exact ⟨by linarith, by linarith⟩;
        rw [ abs_le ];
        constructor <;> linarith [ Real.log_nonneg h8.1, Real.log_le_sub_one_of_pos ( by linarith : 0 < Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ - 1 ) ];
      convert mul_le_mul h8 h3 ( by positivity ) ( by positivity ) using 1 <;> ring_nf;
      rw [ ← abs_mul ] ; ring_nf;
    have h9 : abs ((1 + Real.log (Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ - 1)) * x / Real.log x - (1 + Real.log (Real.log x / Real.log y - 1)) * x / Real.log x) ≤ x / Real.log x ^ 2 := by
      have h9 : abs (Real.log (Real.log ⌊x⌋₊ / Real.log ⌈y⌉₊ - 1) - Real.log (Real.log x / Real.log y - 1)) ≤ 1 / Real.log x := by
        have h9 : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → abs (a - b) ≤ 1 / Real.log x → abs (Real.log a - Real.log b) ≤ 1 / Real.log x := by
          intros a b ha hb hab
          have h_log_diff : abs (Real.log a - Real.log b) ≤ abs (a - b) / min a b := by
            cases le_total a b <;> simp_all +decide [ abs_of_nonneg];
            · rw [ abs_of_nonpos ( sub_nonpos_of_le <| Real.log_le_log ( by linarith ) <| by linarith ), abs_of_nonpos ( sub_nonpos_of_le <| by linarith ) ];
              rw [ le_div_iff₀ ( by linarith ) ];
              have := Real.log_le_sub_one_of_pos ( show 0 < b / a by positivity );
              rw [ Real.log_div ] at this <;> nlinarith [ mul_div_cancel₀ b ( by linarith : a ≠ 0 ) ];
            · rw [ abs_of_nonneg ( sub_nonneg_of_le <| Real.log_le_log ( by linarith ) <| by linarith ) ];
              rw [ ← Real.log_div ( by linarith ) ( by linarith ) ];
              exact le_trans ( Real.log_le_sub_one_of_pos ( div_pos ( by linarith ) ( by linarith ) ) ) ( by ring_nf; norm_num [ show b ≠ 0 by linarith ] );
          exact h_log_diff.trans ( div_le_self ( abs_nonneg _ ) ( by cases min_cases a b <;> linarith ) |> le_trans <| by simpa using hab );
        apply h9;
        · rw [ le_sub_iff_add_le, le_div_iff₀ ] <;> norm_num;
          · rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> positivity;
          · exact Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.lt_ceil.mpr <| by norm_num; linarith;
        · grind;
        · simpa using h5;
      rw [ abs_le ] at *;
      ring_nf at *;
      constructor <;> nlinarith [ show 0 < x * ( Real.log x ) ⁻¹ from mul_pos ( by linarith [ Real.exp_pos 48, le_max_left ( Real.exp 48 ) 699966884713069 ] ) ( inv_pos.mpr ( Real.log_pos ( by linarith [ Real.add_one_le_exp 48, le_max_left ( Real.exp 48 ) 699966884713069 ] ) ) ) ];
    exact abs_le.mpr ⟨ by linarith [ abs_le.mp h8, abs_le.mp h9 ], by linarith [ abs_le.mp h8, abs_le.mp h9 ] ⟩;
  rw [ abs_le ] at *;
  grind +splitIndPred

/-! ### Edge case: Z² > N -/

/-
In the edge case, y ≥ 88789 (same as buchstab_Z_ge but for y directly).
-/
lemma edge_case_y_ge (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_hi : Real.log x / Real.log y ≤ 3) :
    y ≥ 88789 := by
      contrapose! hu_hi;
      rw [ lt_div_iff₀ ( Real.log_pos <| by linarith ) ];
      rw [ ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_num at * <;> try linarith;
      · exact lt_of_lt_of_le ( pow_lt_pow_left₀ hu_hi ( by linarith ) ( by norm_num ) ) ( by linarith );
      · positivity

/-- x ≥ e^48 extracted from hx. -/
lemma edge_case_x_ge_exp (x : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ)) :
    x ≥ Real.exp 48 := le_trans (le_max_left _ _) hx

/-
N ≥ Z in the edge case (since x ≥ y² and y ≥ 88789).
-/
lemma edge_case_Z_le_N (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_lo : 2 ≤ Real.log x / Real.log y)
    (hu_hi : Real.log x / Real.log y ≤ 3) :
    ⌈y⌉₊ ≤ ⌊x⌋₊ := by
      refine Nat.ceil_le.mpr ?__;
      refine' le_trans _ ( Nat.sub_one_lt_floor _ |> le_of_lt );
      -- From hu_lo: 2 ≤ log x / log y, so log x ≥ 2 log y = log(y²), so x ≥ y².
      have hxy_sq : x ≥ y^2 := by
        rw [ le_div_iff₀ ( Real.log_pos <| by linarith ) ] at hu_lo;
        rw [ ge_iff_le, ← Real.log_le_log_iff ( by positivity ) ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.exp_pos 48 ] ) ] ; simpa using hu_lo;
      nlinarith [ show ( 88789 : ℝ ) ≤ y by exact le_of_not_gt fun h => by have := edge_case_y_ge x y hx hy hu_hi; linarith ]

/-
(Z-1)/(log(Z-1))² ≤ y/(log y)² since Z-1 ≤ y.
-/
set_option linter.unnecessarySeqFocus false in
lemma Zm1_div_log_sq_le_y (y : ℝ) (hy : y ≥ 88789) :
    ((⌈y⌉₊ : ℝ) - 1) / (Real.log ((⌈y⌉₊ : ℝ) - 1)) ^ 2 ≤
    y / (Real.log y) ^ 2 := by
      -- Since $\frac{t}{\log^2 t}$ is increasing for $t \geq e^2$, we have $\frac{\lceil y \rceil - 1}{\log^2 (\lceil y \rceil - 1)} \leq \frac{y}{\log^2 y}$.
      have h_inc : ∀ t1 t2 : ℝ, Real.exp 2 ≤ t1 → t1 ≤ t2 → t1 / (Real.log t1)^2 ≤ t2 / (Real.log t2)^2 := by
        -- The derivative of $f(t) = \frac{t}{\log^2 t}$ is $f'(t) = \frac{\log t - 2}{\log^3 t}$, which is positive for $t > e^2$.
        have h_deriv_pos : ∀ t : ℝ, Real.exp 2 < t → deriv (fun t => t / (Real.log t)^2) t > 0 := by
          intro t ht; norm_num [ show t ≠ 0 by linarith [ Real.exp_pos 2 ], show Real.log t ≠ 0 by exact ne_of_gt <| Real.log_pos <| lt_trans ( by norm_num ) ht ];
          exact div_pos ( by nlinarith [ Real.log_exp 2 ▸ Real.log_lt_log ( by positivity ) ht, mul_inv_cancel_left₀ ( by linarith [ Real.exp_pos 2 ] : t ≠ 0 ) ( Real.log t ), Real.add_one_le_exp 2 ] ) ( sq_pos_of_pos ( sq_pos_of_pos ( Real.log_pos ( lt_trans ( by norm_num ) ht ) ) ) );
        -- Apply the mean value theorem to the interval $[t1, t2]$.
        have h_mvt : ∀ t1 t2 : ℝ, Real.exp 2 ≤ t1 → t1 < t2 → ∃ c ∈ Set.Ioo t1 t2, deriv (fun t => t / (Real.log t)^2) c = (t2 / (Real.log t2)^2 - t1 / (Real.log t1)^2) / (t2 - t1) := by
          intros t1 t2 ht1 ht2;
          apply_rules [ exists_deriv_eq_slope ];
          · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_id ( ContinuousAt.pow ( Real.continuousAt_log ( by linarith [ hx.1, Real.exp_pos 2 ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by linarith [ hx.1, Real.add_one_le_exp 2 ] ) ) ) );
          · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_gt ( h_deriv_pos x ( by linarith [ hx.1, Real.add_one_le_exp 2 ] ) ) ) );
        intro t1 t2 ht1 ht2; cases eq_or_lt_of_le ht2 <;> [ aesop; obtain ⟨ c, ⟨ hc1, hc2 ⟩, hc ⟩ := h_mvt t1 t2 ht1 ‹_› <;> have := h_deriv_pos c ( by linarith ) <;> rw [ hc, gt_iff_lt ] at this <;> rw [ lt_div_iff₀ ] at this <;> linarith ] ;
      apply h_inc;
      · exact le_tsub_of_add_le_right <| by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 2:ℝ ) = 1+1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1, Nat.le_ceil y ] ;
      · linarith [ Nat.ceil_lt_add_one ( by positivity : 0 ≤ y ) ]

/-
The prime count as a difference of primesUpTo.
-/
lemma edge_case_prime_card_eq (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_lo : 2 ≤ Real.log x / Real.log y)
    (hu_hi : Real.log x / Real.log y ≤ 3) :
    (((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) =
    ((primesUpTo ⌊x⌋₊).card : ℝ) - ((primesUpTo ((⌈y⌉₊ : ℝ) - 1)).card : ℝ) := by
      convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( primes_Icc_eq_diff ⌈y⌉₊ ⌊x⌋₊ ?_ ?_ ) using 1;
      · rw [ Nat.cast_sub ( Finset.card_le_card _ ) ];
        refine' Finset.filter_subset_filter _ _;
        norm_num +zetaDelta at *;
        exact le_trans ( show y ≤ x from le_of_not_gt fun h => by rw [ div_eq_mul_inv ] at hu_lo; nlinarith [ Real.log_pos <| show 1 < y by linarith, Real.log_lt_log ( by linarith ) h, inv_mul_cancel₀ <| ne_of_gt <| Real.log_pos <| show 1 < y by linarith ] ) <| by linarith [ Nat.lt_floor_add_one x ] ;
      · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; linarith ) );
      · apply edge_case_Z_le_N x y hx hy hu_lo hu_hi

/-
The prime count error in the edge case:
  |#{primes in [Z,N]} - (N/log N - (Z-1)/log(Z-1))| ≤ 40x/(log x)².
-/
lemma edge_case_prime_count_error (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_lo : 2 ≤ Real.log x / Real.log y)
    (hu_hi : Real.log x / Real.log y ≤ 3) :
    |(((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card -
      ((⌊x⌋₊ : ℝ) / Real.log ⌊x⌋₊ - ((⌈y⌉₊ : ℝ) - 1) / Real.log ((⌈y⌉₊ : ℝ) - 1)) : ℝ)| ≤
      40 * x / (Real.log x) ^ 2 := by
        -- Apply the triangle inequality to split the problem into two parts.
        have h_triangle : abs (((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card - (⌊x⌋₊ / Real.log ⌊x⌋₊ - (⌈y⌉₊ - 1) / Real.log (⌈y⌉₊ - 1))) ≤
          abs (((primesUpTo ⌊x⌋₊).card : ℝ) - ⌊x⌋₊ / Real.log ⌊x⌋₊) +
          abs (((primesUpTo (⌈y⌉₊ - 1)).card : ℝ) - (⌈y⌉₊ - 1) / Real.log (⌈y⌉₊ - 1)) := by
            have h_triangle : (((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) =
              ((primesUpTo ⌊x⌋₊).card : ℝ) - ((primesUpTo (⌈y⌉₊ - 1)).card : ℝ) := by
                convert edge_case_prime_card_eq x y hx hy hu_lo hu_hi using 1;
            grind;
        -- Apply the bounds from `pi_error_simple` and `pi_Zm1_error`.
        have h_bounds : abs (((primesUpTo ⌊x⌋₊).card : ℝ) - ⌊x⌋₊ / Real.log ⌊x⌋₊) ≤ 2 * ⌊x⌋₊ / (Real.log ⌊x⌋₊) ^ 2 ∧
            abs (((primesUpTo (⌈y⌉₊ - 1)).card : ℝ) - (⌈y⌉₊ - 1) / Real.log (⌈y⌉₊ - 1)) ≤ 3 * (⌈y⌉₊ - 1) / (Real.log (⌈y⌉₊ - 1)) ^ 2 := by
              apply And.intro;
              · convert pi_error_simple ⌊x⌋₊ _ using 1;
                exact_mod_cast Nat.le_floor ( by norm_num; linarith [ le_max_right ( Real.exp 48 ) ( 88789 ^ 3 : ℝ ) ] );
              · convert pi_Zm1_error ⌈y⌉₊ (buchstab_Z_ge x y hx hy hu_hi) using 1;
        -- Apply the bounds from `buchstab_NlogN_bound` and `y_log_transfer`.
        have h_transfer : 2 * ⌊x⌋₊ / (Real.log ⌊x⌋₊) ^ 2 ≤ 4 * x / (Real.log x) ^ 2 ∧
            3 * (⌈y⌉₊ - 1) / (Real.log (⌈y⌉₊ - 1)) ^ 2 ≤ 36 * x / (Real.log x) ^ 2 := by
              apply And.intro;
              · have := buchstab_NlogN_bound x ( le_trans ( le_max_left _ _ ) hx ) ; ring_nf at *; linarith;
              · have h_transfer : 3 * (⌈y⌉₊ - 1) / (Real.log (⌈y⌉₊ - 1)) ^ 2 ≤ 3 * y / (Real.log y) ^ 2 := by
                  have h_transfer : (⌈y⌉₊ - 1) / (Real.log (⌈y⌉₊ - 1)) ^ 2 ≤ y / (Real.log y) ^ 2 := by
                    apply Zm1_div_log_sq_le_y; exact edge_case_y_ge x y hx hy hu_hi;
                  grind;
                have := y_log_transfer x y ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ) ] ) ( by linarith [ edge_case_y_ge x y hx hy hu_hi ] ) hu_lo; ring_nf at *; linarith;
        exact h_triangle.trans ( by convert add_le_add ( h_bounds.1.trans h_transfer.1 ) ( h_bounds.2.trans h_transfer.2 ) using 1 ; ring )

/-
The transfer bound from N/log N - (Z-1)/log(Z-1) to x/log x - y/log y.
-/
lemma edge_case_transfer (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_lo : 2 ≤ Real.log x / Real.log y)
    (hu_hi : Real.log x / Real.log y ≤ 3) :
    |((⌊x⌋₊ : ℝ) / Real.log ⌊x⌋₊ - ((⌈y⌉₊ : ℝ) - 1) / Real.log ((⌈y⌉₊ : ℝ) - 1)) -
     (x / Real.log x - y / Real.log y)| ≤
      13 * x / (Real.log x) ^ 2 := by
        -- Apply the transfer bounds to each term individually.
        have h1 : abs ((⌊x⌋₊ : ℝ) / Real.log ⌊x⌋₊ - x / Real.log x) ≤ x / (Real.log x) ^ 2 := by
          exact floor_div_log_transfer x ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ) ] )
        have h2 : abs (((⌈y⌉₊ : ℝ) - 1) / Real.log ((⌈y⌉₊ : ℝ) - 1) - y / Real.log y) ≤ y / (Real.log y) ^ 2 := by
          convert ceil_div_log_transfer y ( edge_case_y_ge x y hx hy hu_hi ) using 1
        have h3 : y / (Real.log y) ^ 2 ≤ 12 * x / (Real.log x) ^ 2 := by
          apply y_log_transfer x y (edge_case_x_ge_exp x hx) (edge_case_y_ge x y hx hy hu_hi) hu_lo;
        exact abs_le.mpr ⟨ by ring_nf at *; linarith [ abs_le.mp h1, abs_le.mp h2 ], by ring_nf at *; linarith [ abs_le.mp h1, abs_le.mp h2 ] ⟩

/-
The log(u-1) term bound in the edge case.
-/
lemma edge_case_log_term (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_lo : 2 ≤ Real.log x / Real.log y)
    (hu_hi : Real.log x / Real.log y ≤ 3)
    (hZ2N : ⌊x⌋₊ < ⌈y⌉₊ ^ 2) :
    Real.log (Real.log x / Real.log y - 1) * x / Real.log x ≤
      6 * x / (Real.log x) ^ 2 := by
        -- By `edge_case_log_u_bound`: log(u-1) ≤ 3/(y·log y).
        have h_log_u_bound : Real.log (Real.log x / Real.log y - 1) ≤ 3 / (y * Real.log y) := by
          apply edge_case_log_u_bound x y hx hy hu_lo hZ2N;
        -- We need to show 3x/(y·log y·log x) ≤ 6x/(log x)².
        -- Equivalently: 3/(y·log y) ≤ 6/log x, i.e., log x ≤ 2·y·log y.
        have h_log_x_bound : Real.log x ≤ 2 * y * Real.log y := by
          rw [ div_le_iff₀ ( Real.log_pos <| by linarith ) ] at hu_hi;
          nlinarith [ Real.log_pos ( by linarith : 1 < y ) ];
        -- By combining the bounds, we get the desired inequality.
        have h_combined : Real.log (Real.log x / Real.log y - 1) * x / Real.log x ≤ 3 * x / (y * Real.log y * Real.log x) := by
          convert mul_le_mul_of_nonneg_right h_log_u_bound ( show 0 ≤ x / Real.log x from div_nonneg ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 : ℝ ), Real.exp_pos 48 ] ) ( Real.log_nonneg ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 : ℝ ), Real.add_one_le_exp 48 ] ) ) ) using 1 <;> ring;
        refine le_trans h_combined ?_;
        rw [ div_le_div_iff₀ ];
        · nlinarith [ show 0 ≤ x * Real.log x by exact mul_nonneg ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.exp_pos 48 ] ) ( Real.log_nonneg ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) ) ];
        · exact mul_pos ( mul_pos ( by positivity ) ( Real.log_pos ( by linarith ) ) ) ( Real.log_pos ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) );
        · exact sq_pos_of_pos ( Real.log_pos ( lt_of_lt_of_le ( by norm_num ) hx ) )

/-
1 ≤ x/(log x)² for x ≥ e^48.
-/
lemma one_le_x_div_log_sq (x : ℝ) (hx : x ≥ Real.exp 48) :
    1 ≤ x / (Real.log x) ^ 2 := by
      rw [ one_le_div ];
      · -- We'll use that $Real.log x \leq Real.sqrt x$ for $x \geq e^4$.
        have h_log_sqrt : Real.log x ≤ Real.sqrt x := by
          have := Real.log_le_sub_one_of_pos ( show 0 < Real.sqrt x / 2 by exact div_pos ( Real.sqrt_pos.mpr <| lt_of_lt_of_le ( by positivity ) hx ) zero_lt_two );
          rw [ Real.log_div ( by exact ne_of_gt <| Real.sqrt_pos.mpr <| lt_of_lt_of_le ( by positivity ) hx ) ( by positivity ), Real.log_sqrt <| by linarith [ Real.exp_pos 48 ] ] at this;
          have := Real.log_two_lt_d9 ; norm_num at * ; linarith;
        exact le_trans ( pow_le_pow_left₀ ( Real.log_nonneg ( by linarith [ Real.add_one_le_exp 48 ] ) ) h_log_sqrt 2 ) ( by rw [ Real.sq_sqrt ( by linarith [ Real.add_one_le_exp 48 ] ) ] );
      · exact sq_pos_of_pos <| Real.log_pos <| lt_of_lt_of_le ( by norm_num ) hx

lemma buchstab_core_edge_case (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_lo : 2 ≤ Real.log x / Real.log y)
    (hu_hi : Real.log x / Real.log y ≤ 3)
    (hZ2N : ⌊x⌋₊ < ⌈y⌉₊ ^ 2) :
    |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) -
      ((1 + Real.log (Real.log x / Real.log y - 1)) * x / Real.log x -
       y / Real.log y)| ≤
      500 * x / (Real.log x) ^ 2 := by
  have h_error_bound : |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) - (1 + ((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ)| ≤ 1 := by
    -- Apply the lemma `sievePhi_no_semiprimes` with $N = \lfloor x \rfloor$ and $Z = \lceil y \rceil$.
    have h_sievePhi_no_semiprimes : sievePhi ⌊x⌋₊ ⌈y⌉₊ = 1 + ((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card := by
      apply sievePhi_no_semiprimes;
      · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; linarith ) );
      · exact Nat.floor_pos.mpr ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] );
      · exact hZ2N;
    aesop;
  -- Apply the triangle inequality to combine the error bounds.
  have h_triangle : |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) - ((1 + Real.log (Real.log x / Real.log y - 1)) * x / Real.log x - y / Real.log y)| ≤
    |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) - (1 + ((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ)| +
    |((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card - ((⌊x⌋₊ : ℝ) / Real.log ⌊x⌋₊ - ((⌈y⌉₊ : ℝ) - 1) / Real.log ((⌈y⌉₊ : ℝ) - 1))| +
    |((⌊x⌋₊ : ℝ) / Real.log ⌊x⌋₊ - ((⌈y⌉₊ : ℝ) - 1) / Real.log ((⌈y⌉₊ : ℝ) - 1)) - (x / Real.log x - y / Real.log y)| +
    |Real.log (Real.log x / Real.log y - 1) * x / Real.log x| + 1 := by
      grind;
  refine le_trans h_triangle ?_;
  refine le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add h_error_bound ( edge_case_prime_count_error x y hx hy hu_lo hu_hi ) ) ( edge_case_transfer x y hx hy hu_lo hu_hi ) ) ( show |Real.log ( Real.log x / Real.log y - 1 ) * x / Real.log x| ≤ 6 * x / Real.log x ^ 2 from ?_ ) ) le_rfl ) ?_;
  · rw [ abs_of_nonneg ( div_nonneg ( mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.exp_pos 48 ] ) ) ( Real.log_nonneg ( by linarith [ le_max_left ( Real.exp 48 ) ( 88789 ^ 3 ), le_max_right ( Real.exp 48 ) ( 88789 ^ 3 ), Real.add_one_le_exp 48 ] ) ) ) ];
    convert edge_case_log_term x y hx hy hu_lo hu_hi hZ2N using 1;
  · ring_nf;
    have := one_le_x_div_log_sq x ( le_trans ( by norm_num ) hx );
    grind

/-- The core Buchstab estimate for sievePhi with natural number arguments. -/
lemma buchstab_core (x y : ℝ)
    (hx : x ≥ max (Real.exp 48) (88789 ^ 3 : ℝ))
    (hy : y ≥ 2)
    (hu_lo : 2 ≤ Real.log x / Real.log y)
    (hu_hi : Real.log x / Real.log y ≤ 3) :
    |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) -
      ((1 + Real.log (Real.log x / Real.log y - 1)) * x / Real.log x -
       y / Real.log y)| ≤
      500 * x / (Real.log x) ^ 2 := by
  by_cases h : ⌈y⌉₊ ^ 2 ≤ ⌊x⌋₊
  · exact buchstab_core_main_case x y hx hy hu_lo hu_hi h
  · exact buchstab_core_edge_case x y hx hy hu_lo hu_hi (not_le.mp h)

/-- The final Buchstab estimate in existential form. -/
lemma buchstab_estimate_23:
    ∃ K > 0, ∃ X₀ : ℝ, ∀ x y : ℝ, x ≥ X₀ → y ≥ 2 →
      2 ≤ Real.log x / Real.log y → Real.log x / Real.log y ≤ 3 →
        |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) -
          ((1 + Real.log (Real.log x / Real.log y - 1)) * x / Real.log x -
           y / Real.log y)| ≤
          K * x / (Real.log x) ^ 2 := by
  refine' ⟨ 500, by norm_num, _, _ ⟩
  exact Max.max ( Real.exp 48 ) ( 88789 ^ 3 )
  exact fun x y hx hy h₁ h₂ => buchstab_core x y hx hy h₁ h₂

end

#print axioms buchstab_estimate_23
