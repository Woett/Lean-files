/-
Solving Erdős Problem #314 (https://www.erdosproblems.com/314), Lim and Steinerberger proved that for every $\epsilon > 0$ there are infinitely many pairs $(n, m)$ such that $n^2 (1/n + 1/(n+1) + \ldots + 1/m - 1)$ is smaller than $\epsilon$.

J. Lim  and S. Steinerberger, On differences of two harmonic numbers. Mathematika 71 (2025).

Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) tried to formalize their proof, but it unfortunately came up short. For what it's worth, below you can find what it did end up getting before I decided to throw in the towel.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definition of H_n and f(n) as in the paper.
-/
noncomputable def H (n : ℕ) : ℝ := harmonic n

noncomputable def f (n : ℕ) : ℝ := Real.log n + Real.eulerMascheroniConstant + 1 / (2 * n) - 1 / (12 * n ^ 2)

/-
Extension of f to real numbers.
-/
noncomputable def f_real (x : ℝ) : ℝ := Real.log x + Real.eulerMascheroniConstant + 1 / (2 * x) - 1 / (12 * x ^ 2)

/-
Lemma 3.1: If $| \alpha - p/q | < 1 / (2 q^2)$, then $p/q$ is a convergent of $\alpha$.
-/
theorem lem_legendre (α : ℝ) (p q : ℕ) (hq : q > 0) :
  |α - (p : ℚ) / q| < 1 / (2 * q ^ 2) →
  ∃ (n : ℕ), (p : ℚ) / q = Real.convergent α n := by
    intro h;
    -- We use the Mathlib theorem `Real.exists_rat_eq_convergent` which states that if $| \alpha - r | < 1 / (2 r.den^2)$, then $r$ is a convergent.
    have h_convergent : ∀ r : ℚ, |α - r| < 1 / (2 * r.den ^ 2) → ∃ n : ℕ, (r : ℚ) = Real.convergent α n := by
      exact fun r a => Real.exists_rat_eq_convergent a;
    convert h_convergent ( p / q ) _;
    convert h.trans_le _ using 1 ; norm_num [ Rat.div_def' ];
    · norm_num [ Rat.mkRat_eq_div ];
    · gcongr;
      rw [ div_eq_mul_inv ] ; norm_num [ Rat.mul_den ];
      exact Nat.div_le_self _ _ |> le_trans <| by aesop;

/-
Lemma 3.2 (Corrected): If m = e^x n - 1/2 - e^x/2 + y/n, then either |y| >= 1/8 or (2m+1)/(2n-1) is a convergent of e^x.
-/
theorem lem_y_or_convergent_corrected (x : ℝ) (m n : ℕ) (hn : n ≥ 1) (y : ℝ) :
  (m : ℝ) = Real.exp x * n - 1 / 2 - Real.exp x / 2 + y / n →
  |y| ≥ 1 / 8 ∨ ∃ (k : ℕ), (2 * m + 1 : ℚ) / (2 * n - 1) = Real.convergent (Real.exp x) k := by
    intro h_eq
    by_cases hy : |y| < 1 / 8;
    · -- If $|y| < 1/8$, then $|(2m+1)/(2n-1) - e^x| < 1/(2(2n-1)^2)$.
      have h_ineq : |(2 * m + 1 : ℝ) / (2 * n - 1) - Real.exp x| < 1 / (2 * (2 * n - 1) ^ 2) := by
        rcases n with ( _ | _ | n ) <;> norm_num at *;
        · exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp hy ], by linarith [ abs_lt.mp hy ] ⟩;
        · rw [ abs_lt ] at *;
          constructor <;> norm_num [ h_eq ] <;> ring_nf at *;
          · field_simp at *;
            nlinarith [ Real.add_one_le_exp x, pow_nonneg ( Nat.cast_nonneg n : ( 0 : ℝ ) ≤ n ) 3 ];
          · field_simp at *;
            nlinarith [ Real.add_one_le_exp x, pow_nonneg ( Nat.cast_nonneg n : ( 0 : ℝ ) ≤ n ) 2, pow_nonneg ( Nat.cast_nonneg n : ( 0 : ℝ ) ≤ n ) 3 ];
      have := @lem_legendre ( Real.exp x ) ( 2 * m + 1 ) ( 2 * n - 1 ) ?_ ?_ <;> norm_num at *;
      · exact Or.inr <| by rcases this with ⟨ k, hk ⟩ ; exact ⟨ k, by rw [ Nat.cast_sub <| by linarith ] at hk; push_cast at *; linarith ⟩ ;
      · linarith;
      · rw [ Nat.cast_sub ( by linarith ) ] ; push_cast ; rw [ abs_sub_comm ] ; aesop;
    · exact Or.inl <| le_of_not_gt hy

/-
Definitions of p_n, q_n as the numerator and denominator of the n-th convergent of e, and r_k as the normalized error term for the subsequence.
-/
noncomputable def p_seq (n : ℕ) : ℤ := (Real.convergent (Real.exp 1) n).num
noncomputable def q_seq (n : ℕ) : ℕ := (Real.convergent (Real.exp 1) n).den

noncomputable def r_seq (k : ℕ) : ℝ := |Real.exp 1 - (p_seq (3 * k + 1) : ℝ) / (q_seq (3 * k + 1) : ℝ)| * (q_seq (3 * k + 1) : ℝ) ^ 2

/-
Definition of the continued fraction coefficients of e.
-/
def e_coeff (n : ℕ) : ℕ :=
  if n = 0 then 2
  else if n % 3 = 2 then 2 * (n / 3 + 1)
  else 1

/-
Initial values for the convergents of e.
-/
theorem e_cf_init :
  p_seq 0 = 2 ∧ q_seq 0 = 1 ∧ p_seq 1 = 3 ∧ q_seq 1 = 1 := by
    convert And.intro _ ( And.intro _ ( And.intro _ _ ) );
    · unfold p_seq;
      -- The zeroth convergent of $e$ is $2$, so its numerator is $2$.
      have h_zeroth_convergent : (Real.exp 1).convergent 0 = 2 := by
        convert Int.floor_eq_iff.mpr ?_;
        any_goals exact ( 2 : ℝ );
        all_goals first | infer_instance | norm_num;
        exact iff_of_true ( mod_cast Int.floor_eq_iff.mpr ⟨ by norm_num; exact Real.exp_one_gt_d9.le.trans' <| by norm_num, by norm_num; exact Real.exp_one_lt_d9.trans_le <| by norm_num ⟩ ) rfl;
        norm_num;
      exact h_zeroth_convergent.symm ▸ rfl;
    · unfold q_seq; norm_num;
    · unfold p_seq; norm_num;
      -- Since $\exp  ( 1 ) \approx 2.718$, we have $\lfloor \exp(1) \rfloor = 2$ and $\lfloor (\exp(1) - 2)^{-1} \rfloor = 1  $ .
      have h_floor : ⌊Real.exp 1⌋ = 2 ∧ ⌊(Int.fract (Real.exp 1))⁻¹⌋ = 1 := by
        have h_exp : 2.718 < Real.exp 1 ∧ Real.exp 1 < 2.719 := by
          -- We'll use the fact that $e \approx 2.718$ to estimate the bounds.
          exact ⟨Real.exp_one_gt_d9.trans_le' (by norm_num), Real.exp_one_lt_d9.trans_le (by norm_num)⟩;
        field_simp;
        exact ⟨ Int.floor_eq_iff.mpr ⟨ by norm_num1 at *; linarith, by norm_num1 at *; linarith ⟩, Int.floor_eq_iff.mpr ⟨ by norm_num1 at *; rw [ le_div_iff₀ ] <;> linarith [ Int.fract_add_floor ( Real.exp 1 ), show ( Int.floor ( Real.exp 1 ) : ℝ ) = 2 by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by norm_num1 at *; linarith, by norm_num1 at *; linarith ⟩ ], by norm_num1 at *; rw [ div_lt_iff₀ ] <;> linarith [ Int.fract_add_floor ( Real.exp 1 ), show ( Int.floor ( Real.exp 1 ) : ℝ ) = 2 by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by norm_num1 at *; linarith, by norm_num1 at *; linarith ⟩ ] ⟩ ⟩;
      norm_num [ h_floor ];
    · unfold q_seq; norm_num [ Real.convergent ] ; ring_nf;
      -- We'll use that $e \approx 2.718$ to show that $1 \leq \frac{1}{e - 2} < 2$.
      have h_bounds : 1 ≤ (Real.exp 1 - 2)⁻¹ ∧ (Real.exp 1 - 2)⁻¹ < 2 := by
        constructor;
        · field_simp;
          rw [ le_div_iff₀ ] <;> have := Real.exp_one_gt_d9.le <;> norm_num at * <;> linarith [ Real.exp_one_lt_d9.le ];
        · rw [ inv_eq_one_div, div_lt_iff₀ ] <;> have := Real.exp_one_gt_d9.le <;> norm_num at * <;> linarith;
      rw [ show Int.fract ( Real.exp 1 ) = Real.exp 1 - 2 by rw [ Int.fract ] ; norm_num [ show ⌊Real.exp 1⌋ = 2 by rw [ Int.floor_eq_iff ] ; norm_num ; exact ⟨ Real.exp_one_gt_d9.le.trans' <| by norm_num, Real.exp_one_lt_d9.trans_le <| by norm_num ⟩ ] ] ; norm_num [ show ⌊ ( Real.exp 1 - 2 ) ⁻¹⌋ = 1 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ]

/-
Recursive definitions of p_n and q_n.
-/
def p_rec : ℕ → ℤ
| 0 => 2
| 1 => 3
| n + 2 => (e_coeff (n + 2) : ℤ) * p_rec (n + 1) + p_rec n

def q_rec : ℕ → ℤ
| 0 => 1
| 1 => 1
| n + 2 => (e_coeff (n + 2) : ℤ) * q_rec (n + 1) + q_rec n

/-
The numerators p_{3k+1} are always odd.
-/
theorem p_rec_odd (k : ℕ) : Odd (p_rec (3 * k + 1)) := by
  induction' k with k ih;
  · decide +revert;
  · -- By definition of $p_rec$, we have $p_{3(k+1)+1} = e_{3(k+1)+1} p_{3(k+1)} + p_{3(k+1)-1}$.
    have h_recurrence : p_rec (3 * (k + 1) + 1) = (e_coeff (3 * (k + 1) + 1) : ℤ) * p_rec (3 * (k + 1)) + p_rec (3 * (k + 1) - 1) := by
      exact Eq.symm ((fun {a b} => Int.neg_inj.mp) rfl);
    -- By definition of $p_rec$, we have $p_{3k+3} = e_{3k+3} p_{3k  + 2} + p_{3k+1}$.
    have h_recurrence2 : p_rec (3 * k + 3) = (e_coeff (3 * k + 3) : ℤ) * p_rec (3 * k + 2) + p_rec (3 * k + 1) := by
      exact Eq.symm ((fun {a b} => Int.neg_inj.mp) rfl)
    simp_all +decide [ Nat.mul_succ, parity_simps ];
    unfold e_coeff; simp +decide [ parity_simps ] ;
    grind

/-
The denominators q_{3k+1} are always odd.
-/
theorem q_rec_odd (k : ℕ) : Odd (q_rec (3 * k + 1)) := by
  induction' k with k ih <;> simp_all +arith +decide [ Nat.mul_succ, parity_simps ];
  -- By definition of $q_rec$, we have $q_rec (3 * k + 4) = e_coeff (3 * k + 4) * q_rec (3 * k + 3) + q_rec (3 * k + 2)$.
  have h_q_rec_succ : q_rec (3 * k + 4) = e_coeff (3 * k + 4) * q_rec (3 * k + 3) + q_rec (3 * k + 2) := by
    rfl;
  -- By definition of $q_rec$, we have $q_rec (3 * k + 3) = e_coeff (3 * k + 3) * q_rec (3 * k + 2) + q_rec (3 * k + 1)$.
  have h_q_rec_succ2 : q_rec (3 * k + 3) = e_coeff (3 * k + 3) * q_rec (3 * k + 2) + q_rec (3 * k + 1) := by
    rfl;
  simp_all +decide [ e_coeff, parity_simps ];
  grind

/-
Hypothesis: The convergents of e match the recursive definitions p_rec and q_rec.
-/
def Hypothesis_CF_e : Prop :=
  ∀ n, (Real.convergent (Real.exp 1) n).num = p_rec n ∧ (Real.convergent (Real.exp 1) n).den = q_rec n

/-
With the notation of Lemma \ref{lem:secondorder}, if |f(m)-f(n-1) - x| \le \varepsilon/n^2 for arbitrarily small \varepsilon>0 (for infinitely many n), then y must satisfy y = y^* + o(1) as n\to\infty, where y^* := (e^{x}-e^{-x})/24 = \sinh x / 12.
-/
theorem cor_necessity (x : ℝ) (hx : x > 0) (R : ℝ) :
  ∃ C > 0, ∀ n : ℕ, n ≥ 2 → ∀ y : ℝ, |y| ≤ R →
  let m := Real.exp x * n - 1 + Real.exp x / 2 + y / n
  let y_star := Real.sinh x / 12
  (∀ ε > 0, ∃ N, ∀ n ≥ N, |f_real m - f_real (n - 1) - x| ≤ ε / n ^ 2) →
  abs (y - y_star) = 0 := by
    contrapose! hx;
    unfold f_real at *;
    simp +zetaDelta at *;
    have := hx 1 Nat.one_pos; obtain ⟨ n, hn₁, y, hy₁, hy₂, hy₃ ⟩ := this; have := hy₂ 1 zero_lt_one; obtain ⟨ N, hN ⟩ := this; have := hN ( Max.max N 2 ) ( le_max_left _ _ ) ; norm_num at this;
    have h_lim : Filter.Tendsto (fun n_1 : ℝ => Real.log (n_1 - 1) + Real.eulerMascheroniConstant + (n_1 - 1)⁻¹ * (1 / 2) - ((n_1 - 1) ^ 2)⁻¹ * (1 / 12)) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_add ( Filter.Tendsto.atTop_add ( Filter.Tendsto.atTop_add ( Real.tendsto_log_atTop.comp <| Filter.tendsto_id.atTop_add tendsto_const_nhds ) tendsto_const_nhds ) <| Filter.Tendsto.mul ( tendsto_inv_atTop_zero.comp <| Filter.tendsto_id.atTop_add tendsto_const_nhds ) tendsto_const_nhds ) <| Filter.Tendsto.neg <| Filter.Tendsto.mul ( tendsto_inv_atTop_zero.comp <| Filter.tendsto_pow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| Filter.tendsto_id.atTop_add tendsto_const_nhds ) tendsto_const_nhds;
    have h_lim : Filter.Tendsto (fun n_1 : ℝ => Real.log (Real.exp x * n - 1 + Real.exp x / 2 + y / n) + Real.eulerMascheroniConstant + (Real.exp x * n - 1 + Real.exp x / 2 + y / n)⁻¹ * (1 / 2) - ((Real.exp x * n - 1 + Real.exp x / 2 + y / n) ^ 2)⁻¹ * (1 / 12) - (Real.log (n_1 - 1) + Real.eulerMascheroniConstant + (n_1 - 1)⁻¹ * (1 / 2) - ((n_1 - 1) ^ 2)⁻¹ * (1 / 12)) - x) Filter.atTop Filter.atBot := by
      exact Filter.Tendsto.atBot_add ( Filter.Tendsto.add_atBot tendsto_const_nhds ( Filter.tendsto_neg_atTop_atBot.comp h_lim ) ) tendsto_const_nhds;
    have := h_lim.eventually ( Filter.eventually_lt_atBot ( -2 ) ) ; have := this.and ( Filter.eventually_ge_atTop ( Max.max N 2 ) ) ; obtain ⟨ n_1, hn_1₁, hn_1₂ ⟩ := this.exists; norm_num at *;
    have := hN n_1 hn_1₂.1; norm_num at this; linarith [ abs_le.mp this, inv_le_one_of_one_le₀ ( show 1 ≤ n_1 ^ 2 by nlinarith ) ] ;

/-
The coefficients of the continued fraction of e satisfy: e_coeff(3k+2) = 2(k+1), e_coeff(3k) = 1 for k>0, and e_coeff(3k+1) = 1.
-/
theorem e_coeff_values (k : ℕ) :
  e_coeff (3 * k + 2) = 2 * (k + 1) ∧
  (k > 0 → e_coeff (3 * k) = 1) ∧
  e_coeff (3 * k + 1) = 1 := by
    -- By definition of e_coeff, we can split into cases based on the modulo operation.
    simp [e_coeff];
    exact ⟨ by omega, fun hk => by linarith ⟩

/-
For all k, p_{3k+4} is congruent to p_{3k+1} modulo 2.
-/
theorem lem_p_mod_two (k : ℕ) : p_rec (3 * k + 4) % 2 = p_rec (3 * k + 1) % 2 := by
  rw [ show p_rec ( 3 * k + 4 ) = ( e_coeff ( 3 * k + 4 ) : ) * p_rec ( 3 * k + 3 ) + p_rec ( 3 * k + 2 ) from rfl, show p_rec ( 3 * k + 3 ) = ( e_coeff ( 3 * k + 3 ) : ℤ ) * p_rec ( 3 * k + 2 ) + p_rec ( 3 * k + 1 ) from rfl, show p_rec ( 3 * k + 2 ) = ( e_coeff ( 3 * k + 2 ) : ℤ ) * p_rec ( 3 * k + 1 ) + p_rec ( 3 * k ) from rfl ] ; norm_num [ Int.add_emod, Int.mul_emod, e_coeff ];
  cases Int.emod_two_eq_zero_or_one ( p_rec ( 3 * k ) ) <;> cases Int.emod_two_eq_zero_or_one ( p_rec ( 3 * k + 1 ) ) <;> simp +decide only [*]

/-
For all k, q_{3k+4} is congruent to q_{3k+1} modulo 2.
-/
theorem lem_q_mod_two (k : ℕ) : q_rec (3 * k + 4) % 2 = q_rec (3 * k + 1) % 2 := by
  -- By definition of $q_rec$, we have $q_rec (3 * k + 4) = e_coeff (3 * k + 4) * q_rec (3 * k + 3) + q_rec (3 * k + 2)$.
  have h_q_rec_def : q_rec (3 * k + 4) = e_coeff (3 * k + 4) * q_rec (3 * k + 3) + q_rec (3 * k + 2) := by
    rfl;
  -- By definition of $q_rec$, we have $q_rec (3 * k + 3) = e_coeff (3 * k + 3) * q_rec (3 * k + 2) + q_rec (3 * k + 1)$.
  have h_q_rec_def2 : q_rec (3 * k + 3) = e_coeff (3 * k + 3) * q_rec (3 * k + 2) + q_rec (3 * k + 1) := by
    rfl;
  -- By definition of $q_rec$, we have $q_rec (3 * k + 2) = e_coeff (3 * k + 2) * q_rec (3 * k + 1) + q_rec (3 * k)$.
  have h_q_rec_def3 : q_rec (3 * k + 2) = e_coeff (3 * k + 2) * q_rec (3 * k + 1) + q_rec (3 * k) := by
    rfl;
  unfold e_coeff at *; simp +decide [ *, Int.add_emod, Int.mul_emod ] ;
  cases Int.emod_two_eq_zero_or_one ( q_rec ( 3 * k ) ) <;> cases Int.emod_two_eq_zero_or_one ( q_rec ( 3 * k + 1 ) ) <;> simp +decide only [*]

/-
For all k, p_rec(3k+1) is odd.
-/
theorem lem_p_rec_odd (k : ℕ) : Odd (p_rec (3 * k + 1)) := by
  exact p_rec_odd k

/-
For all k, q_rec(3k+1) is odd.
-/
theorem lem_q_rec_odd (k : ℕ) : Odd (q_rec (3 * k + 1)) := by
  exact q_rec_odd k

/-
The denominator of the (n+1)-th auxiliary convergent is positive if the continued fraction is not terminated at n.
-/
theorem lem_contsAux_b_pos_of_not_terminated (v : ℝ) (n : ℕ) (h : ¬ (GenContFract.of v).TerminatedAt n) :
  0 < ((GenContFract.of v).contsAux (n + 1)).b := by
    -- By definition of `GenContFract.of`, if `¬TerminatedAt n`, then `¬TerminatedAt (n - 1)`.
    have h_not_terminated : ¬(GenContFract.of v).TerminatedAt (n - 1) := by
      cases n <;> simp_all +decide [ GenContFract.terminatedAt_iff_s_none ];
      -- By definition of `GenContFract.of`, if the (n+1)th partial quotient is not none, then the nth partial quotient must also be non-none.
      have h_partial_quotient : ∀ n, (GenContFract.of v).s.get? n = none → (GenContFract.of v).s.get? (n + 1) = none := by
        intros n hn_none
        have h_partial_quotient : ∀ m ≥ n, (GenContFract.of v).s.get? m = none := by
          exact fun m a => Stream'.Seq.le_stable (GenContFract.of v).s a hn_none;
        grind;
      exact fun h' => h <| h_partial_quotient _ h';
    have h_pos : ∀ n, ¬(GenContFract.of v).TerminatedAt n → 0 < ((GenContFract.of v).contsAux (n + 2)).b := by
      intro n hn_not_terminated
      have h_pos : 0 < ((GenContFract.of v).contsAux (n + 2)).b := by
        have h_fib_le : Nat.fib (n + 2) ≤ ((GenContFract.of v).contsAux (n + 2)).b := by
          apply_rules [ GenContFract.fib_le_of_contsAux_b ];
          tauto
        exact lt_of_lt_of_le ( by norm_num ) h_fib_le;
      exact h_pos;
    cases n <;> aesop

/-
The fractional part at step n is positive if the continued fraction is not terminated at n.
-/
theorem lem_ifp_fr_pos (v : ℝ) (n : ℕ) (ifp : GenContFract.IntFractPair ℝ)
  (stream_nth_eq : GenContFract.IntFractPair.stream v n = some ifp)
  (h_not_terminated : ¬ (GenContFract.of v).TerminatedAt n) :
  0 < ifp.fr := by
    contrapose! h_not_terminated; simp_all +decide [ GenContFract.TerminatedAt ] ;
    simp_all +decide [ GenContFract.of ];
    simp_all +decide [ GenContFract.IntFractPair.seq1 ];
    simp_all +decide [ Stream'.Seq.TerminatedAt, Stream'.Seq.map ];
    -- Since the fractional part is non-positive, the stream at n+1 is none by definition.
    have h_stream_none : ∀ n, GenContFract.IntFractPair.stream v n = some ifp → ifp.fr ≤ 0 → GenContFract.IntFractPair.stream v (n + 1) = none := by
      intros n stream_nth_eq h_not_terminated
      simp [GenContFract.IntFractPair.stream] at *;
      intros a stream_nth_eq; have := stream_nth_eq; simp_all +decide
      have h_pos : ∀ n, (GenContFract.IntFractPair.stream v n).isSome → (GenContFract.IntFractPair.stream v n).get!.fr ≥ 0 := by
        intro n hn; induction' n with n ih <;> simp_all +decide [ GenContFract.IntFractPair.stream ] ;
        · exact Int.fract_nonneg _;
        · cases h : GenContFract.IntFractPair.stream v n <;> simp_all +decide [ GenContFract.IntFractPair.of ];
      exact le_antisymm h_not_terminated ( by simpa [ this ] using h_pos n ( by simp +decide [ this ] ) );
    rw [ Stream'.map ] ; aesop

/-
Integer relations for m and n derived from parity.
-/
theorem prop_scaling_integers (d : ℕ) (p q : ℤ) (hd : Odd d) (hp : Odd p) (hq : Odd q) :
  let m := (d * p - 1) / 2
  let n := (d * q + 1) / 2
  (2 * m + 1 : ℤ) = d * p ∧ (2 * n - 1 : ℤ) = d * q := by
    constructor <;> linarith [ Int.ediv_mul_cancel ( show 2 ∣ ( d : ℤ ) * p - 1 from even_iff_two_dvd.mp <| by simp_all +decide [ parity_simps ] ), Int.ediv_mul_cancel ( show 2 ∣ ( d : ℤ ) * q + 1 from even_iff_two_dvd.mp <| by simp_all +decide [ parity_simps ] ) ]

/-
Algebraic identity for e in terms of m and n.
-/
theorem prop_scaling_algebra_e (k : ℕ) (d : ℕ) (p q : ℤ) (r : ℝ) (m n : ℤ)
  (h_m : 2 * m + 1 = d * p)
  (h_n : 2 * n - 1 = d * q)
  (hd_pos : (d : ℝ) ≠ 0)
  (h_err : Real.exp 1 - (p : ℝ) / q = (-1 : ℝ)^(k + 1) * r / q^2) :
  Real.exp 1 = (2 * m + 1 : ℝ) / (2 * n - 1 : ℝ) + (-1 : ℝ)^(k + 1) * r * (d : ℝ)^2 / (2 * n - 1 : ℝ)^2 := by
    convert eq_add_of_sub_eq' h_err using 1;
    rw [ show ( 2 * m + 1 : ℝ ) = d * p by exact mod_cast h_m, show ( 2 * n - 1 : ℝ ) = d * q by exact mod_cast h_n ] ; ring_nf;
    simp +decide [mul_assoc, mul_comm, sq, hd_pos]

/-
The coefficient $a_{3k+2}$ in the continued fraction of $e$ is $2(k+1)$.
-/
theorem e_coeff_val (k : ℕ) : e_coeff (3 * k + 2) = 2 * (k + 1) := by
  unfold e_coeff; norm_num [ Nat.add_mod, Nat.mul_mod ] ;
  grind

/-
Values of `e_coeff` at indices $3k$ and $3k+1$.
-/
theorem e_coeff_values_aux (k : ℕ) :
  (k > 0 → e_coeff (3 * k) = 1) ∧
  e_coeff (3 * k + 1) = 1 := by
    unfold e_coeff; aesop;

/-
For $|x| \le 1/2$, $|\log(1+x) - (x - x^2/2)| \le |x|^3$.
-/
theorem taylor_log_bound (x : ℝ) (hx : |x| ≤ 1/2) :
  |Real.log (1 + x) - (x - x^2/2)| ≤ |x|^3 := by
    -- Let's consider the expression $|\log(1+x) - (x - x^2/2)|$ for $|x| \le 1/2$.
    -- We can use the Taylor series expansion of $\log(1+x)$ around $x=0$.
    have h_taylor : ∀ x : ℝ, |x| ≤ 1 / 2 → |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ |x| ^ 3 := by
      intro x hx
      have h_taylor_series : ∀ x : ℝ, |x| ≤ 1 / 2 → |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ |x| ^ 3 := by
        intro x hx
        have h_integral : ∫ t in (0 : ℝ)..x, (t ^ 2 / (1 + t)) = Real.log (1 + x) - (x - x ^ 2 / 2) := by
          -- We'll use the fact that $\frac{t^2}{1+t} = t - 1 + \frac{1}{1+t}$ to simplify the integral.
          have h_integral_simplified : ∫ t in (0 : ℝ)..x, t ^ 2 / (1 + t) = ∫ t in (0 : ℝ)..x, (t - 1 + 1 / (1 + t)) := by
            refine' intervalIntegral.integral_congr fun t ht => _;
            rw [ add_div' ] <;> ring_nf ; cases Set.mem_uIcc.mp ht <;> linarith [ abs_le.mp hx ];
          rw [ h_integral_simplified, intervalIntegral.integral_add, intervalIntegral.integral_sub ] <;> norm_num;
          · rw [ integral_inv_of_pos ] <;> norm_num <;> linarith [ abs_le.mp hx ];
          · apply_rules [ ContinuousOn.intervalIntegrable ];
            exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( continuousAt_const.add continuousAt_id ) ( by cases Set.mem_uIcc.mp ht <;> linarith [ abs_le.mp hx ] )
        -- We'll use the fact that $|\int_0^x \frac{t^2}{1+t} dt| \leq |x|^3$ for $|x| \leq 1/2$.
        have h_integral_bound : ∀ x : ℝ, |x| ≤ 1 / 2 → |∫ t in (0 : ℝ)..x, t ^ 2 / (1 + t)| ≤ |x| ^ 3 := by
          intros x hx
          have h_integral_bound : ∀ t ∈ Set.Icc (0 : ℝ) (|x|), |t ^ 2 / (1 + t)| ≤ t ^ 2 := by
            exact fun t ht => by rw [ abs_of_nonneg ( div_nonneg ( sq_nonneg _ ) ( by linarith [ ht.1 ] ) ) ] ; exact div_le_self ( sq_nonneg _ ) ( by linarith [ ht.1 ] ) ;
          cases abs_cases x <;> simp_all +decide [ intervalIntegral ];
          · rw [ abs_of_nonneg ( MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun t ht => div_nonneg ( sq_nonneg _ ) ( by linarith [ ht.1 ] ) ) ];
            exact le_trans ( MeasureTheory.setIntegral_mono_on ( by exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun t ht => by exact ContinuousAt.div ( continuousAt_id.pow 2 ) ( continuousAt_const.add continuousAt_id ) ( by linarith [ ht.1 ] ) ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self ) ( by exact Continuous.integrableOn_Ioc <| by continuity ) measurableSet_Ioc fun t ht => le_of_abs_le <| h_integral_bound t ht.1.le ht.2 ) <| by rw [ ← intervalIntegral.integral_of_le ( by linarith ) ] ; norm_num [ abs_of_nonneg, * ] ; nlinarith [ sq_nonneg x ] ;
          · -- Since $x \leq 0$, we can rewrite the integral as $\int_{0}^{-x} \frac{t^2}{1-t} dt$.
            have h_integral_neg : ∫ t in Set.Ioc x 0, t ^ 2 / (1 + t) = ∫ t in Set.Ioc 0 (-x), t ^ 2 / (1 - t) := by
              rw [ ← intervalIntegral.integral_of_le ( by linarith ), ← intervalIntegral.integral_of_le ( by linarith ) ] ; convert intervalIntegral.integral_comp_neg _ using 3 <;> ring;
            -- Since $x \leq 0$, we can rewrite the integral as $\int_{0}^{-x} \frac{t^2}{1-t} dt$ and bound it.
            have h_integral_bound_neg : ∫ t in Set.Ioc 0 (-x), t ^ 2 / (1 - t) ≤ ∫ t in Set.Ioc 0 (-x), t ^ 2 / (1 - (-x)) := by
              refine' MeasureTheory.setIntegral_mono_on _ _ _ _ <;> norm_num at *;
              · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div ( continuousAt_id.pow 2 ) ( continuousAt_const.sub continuousAt_id ) ( by linarith [ ht.1, ht.2 ] ) ) |> fun h => h.mono_set ( Set.Ioc_subset_Icc_self );
              · exact Continuous.integrableOn_Ioc ( by continuity );
              · exact fun t ht₁ ht₂ => by rw [ div_le_div_iff₀ ] <;> nlinarith [ sq_pos_of_pos ht₁ ] ;
            simp_all +decide [ ← intervalIntegral.integral_of_le, abs_of_nonpos ];
            rw [ abs_of_nonneg ( intervalIntegral.integral_nonneg ( by linarith ) fun t ht => div_nonneg ( sq_nonneg _ ) ( by linarith [ ht.1, ht.2 ] ) ) ] ; exact h_integral_bound_neg.trans ( by rw [ div_div, div_le_iff₀ ] <;> nlinarith [ pow_pos ( neg_pos.mpr ( by linarith : x < 0 ) ) 3 ] ) ;
        exact h_integral ▸ h_integral_bound x hx
      exact h_taylor_series x hx;
    exact h_taylor x hx

/-
For $|x| \le 1/2$, $|(1+x)^{-1} - (1-x)| \le 2|x|^2$.
-/
theorem taylor_inv_bound (x : ℝ) (hx : |x| ≤ 1/2) :
  |1 / (1 + x) - (1 - x)| ≤ 2 * |x|^2 := by
    rw [ abs_le ] at *;
    constructor <;> cases abs_cases x <;> nlinarith [ mul_div_cancel₀ 1 ( by linarith : ( 1 + x ) ≠ 0 ), sq_nonneg ( x - 1 / 2 ), sq_nonneg ( x + 1 / 2 ) ]

/-
For $|x| \le 1/2$, $|(1+x)^{-2} - (1-2x)| \le 20|x|^2$.
-/
theorem taylor_inv_sq_bound (x : ℝ) (hx : |x| ≤ 1/2) :
  |1 / (1 + x)^2 - (1 - 2 * x)| ≤ 20 * |x|^2 := by
    by_cases hx' : x = 0 <;> norm_num [ hx', abs_le ] at hx ⊢;
    constructor <;> nlinarith [ mul_le_mul_of_nonneg_left hx.2 ( sq_nonneg ( x + 1 / 2 ) ), mul_le_mul_of_nonneg_left hx.1 ( sq_nonneg ( x - 1 / 2 ) ), mul_inv_cancel₀ ( show ( 1 + x ) ^ 2 ≠ 0 by nlinarith [ mul_self_pos.2 hx' ] ) ]

/-
Definition of the normalized error term r_n for the n-th convergent.
-/
noncomputable def r_val (n : ℕ) : ℝ := |Real.exp 1 - (p_seq n : ℝ) / (q_seq n : ℝ)| * (q_seq n : ℝ) ^ 2

/-
For any real number x, there exists an odd integer d within distance 1 of x.
-/
theorem exists_odd_near (x : ℝ) : ∃ d : ℤ, Odd d ∧ |d - x| ≤ 1 := by
  cases' em ( ⌊x⌋ % 2 = 0 ) with h h;
  · refine' ⟨ ⌊x⌋ + 1, _, _ ⟩;
    · exact Int.odd_iff.mpr ( by norm_num [ Int.add_emod, h ] );
    · exact abs_le.mpr ⟨ by push_cast; linarith [ Int.floor_le x, Int.lt_floor_add_one x ], by push_cast; linarith [ Int.floor_le x, Int.lt_floor_add_one x ] ⟩;
  · exact ⟨ ⌊x⌋, by simpa [ ← Int.odd_iff ] using h, abs_sub_le_iff.mpr ⟨ by linarith [ Int.floor_le x ], by linarith [ Int.lt_floor_add_one x ] ⟩ ⟩

/-
Definitions for the corrected m and s_0.
-/
noncomputable def s_0 (x : ℝ) : ℝ := -(Real.exp x + 1) / 2

noncomputable def m_def (x y : ℝ) (n : ℕ) : ℝ := Real.exp x * n + s_0 x + y / n

/-
Definitions of the three parts of the difference f(m) - f(n-1) - x.
-/
noncomputable def log_term (x y : ℝ) (n : ℕ) : ℝ := Real.log (m_def x y n / (n - 1)) - x
noncomputable def inv_term (x y : ℝ) (n : ℕ) : ℝ := 1 / (2 * m_def x y n) - 1 / (2 * ((n : ℝ) - 1))
noncomputable def quad_term (x y : ℝ) (n : ℕ) : ℝ := -1 / (12 * (m_def x y n)^2) + 1 / (12 * ((n : ℝ) - 1)^2)

/-
Definitions for the coefficients and the auxiliary term h.
-/
noncomputable def c1_log (x : ℝ) : ℝ := (1 - Real.exp (-x)) / 2
noncomputable def c2_log (x y : ℝ) : ℝ := Real.exp (-x) * y + (1 - Real.exp (-x)) / 2 - (1 - Real.exp (-x))^2 / 8
noncomputable def h_def (x y : ℝ) (n : ℕ) : ℝ := ((1 - Real.exp (-x)) / 2 + Real.exp (-x) * y / n) / (n - 1)

/-
Coefficient for the 1/n^2 term in the expansion of h.
-/
noncomputable def c2_h (x y : ℝ) : ℝ := (1 - Real.exp (-x)) / 2 + Real.exp (-x) * y

/-
Coefficient for the 1/n term in the expansion of h.
-/
noncomputable def c1_h (x : ℝ) : ℝ := (1 - Real.exp (-x)) / 2

/-
Approximation lemma for h.
-/
theorem h_bound_approx (x : ℝ) (hx : x > 0) (R : ℝ) :
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
  |h_def x y n - (c1_h x / n + c2_h x y / n^2)| ≤ C / n^3 := by
    -- Set $A$ and $B$ as given in the problem statement.
    set A := (1 - Real.exp (-x)) / 2
    set B := Real.exp (-x) * R;
    -- Then we have $|h - (A/n + (A+B)/n^2)| \leq (|A| + |B|) / (n^2(n-1))$.
    have h_bound : ∀ n : ℕ, n ≥ 2 → ∀ y : ℝ, |y| ≤ R → |h_def x y n - (A / (n : ℝ) + (A + Real.exp (-x) * y) / (n : ℝ)^2)| ≤ (|A| + |Real.exp (-x) * y|) / ((n : ℝ)^2 * (n - 1)) := by
      field_simp;
      intros n hn y hy; rw [ show h_def x y n = ( A + Real.exp ( -x ) * y / n ) / ( n - 1 ) by rfl ] ; rw [ div_sub_div, abs_le ];
      · rw [ mul_comm, div_le_div_iff₀, neg_le ];
        · rw [ neg_div', div_le_div_iff₀ ];
          · constructor <;> cases abs_cases A <;> cases abs_cases ( y * Real.exp ( -x ) ) <;> nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, show ( n ^ 2 : ℝ ) * ( n - 1 ) ≥ 0 by exact mul_nonneg ( sq_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ), show ( n ^ 3 : ℝ ) * ( n - 1 ) ≥ 0 by exact mul_nonneg ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ), mul_div_cancel₀ ( y * Real.exp ( -x ) ) ( by positivity : ( n : ℝ ) ≠ 0 ) ];
          · exact mul_pos ( by norm_num; linarith ) ( by positivity );
          · exact mul_pos ( sq_pos_of_pos ( by positivity ) ) ( by norm_num; linarith );
        · exact mul_pos ( by norm_num; linarith ) ( by positivity );
        · exact mul_pos ( sq_pos_of_pos ( by positivity ) ) ( by norm_num; linarith );
      · exact sub_ne_zero_of_ne ( by norm_cast; linarith );
      · positivity;
    -- We can simplify the expression on the right-hand side.
    have h_simplified : ∀ n : ℕ, n ≥ 2 → ∀ y : ℝ, |y| ≤ R → |h_def x y n - (A / (n : ℝ) + (A + Real.exp (-x) * y) / (n : ℝ)^2)| ≤ (|A| + |Real.exp (-x) * y|) / ((n : ℝ)^3 / 2) := by
      intro n hn y hy; refine le_trans ( h_bound n hn y hy ) ?_; gcongr ; nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast ] ;
    refine' ⟨ 2 * ( |A| + |Real.exp ( -x ) * R| ) + 1, _, 2, _ ⟩ <;> norm_num;
    · positivity;
    · intro n hn y hy; specialize h_simplified n hn y hy; refine' le_trans h_simplified _;
      field_simp;
      cases abs_cases y <;> cases abs_cases R <;> cases abs_cases ( Real.exp ( -x ) * y ) <;> nlinarith [ Real.exp_pos ( -x ), Real.exp_le_one_iff.mpr ( show -x ≤ 0 by linarith ) ]

/-
Approximation lemma for h^2.
-/
theorem h_sq_bound_approx (x : ℝ) (hx : x > 0) (R : ℝ) :
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
  |h_def x y n ^ 2 / 2 - c1_h x ^ 2 / (2 * (n : ℝ)^2)| ≤ C / (n : ℝ)^3 := by
    -- We'll use the fact that $h$ is approximately $c1_h x / n$ for large $n$.
    obtain ⟨C, hC_pos, N, hN⟩ : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R → |h_def x y n - c1_h x / n| ≤ C / n^2 := by
      -- Apply the approximation lemma for h.
      obtain ⟨C, hC_pos, N, hN⟩ : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R → |h_def x y n - (c1_h x / n + c2_h x y / n^2)| ≤ C / n^3 := by
        exact h_bound_approx x hx R;
      -- We'll use the fact that $|c2_h x y / n^2| \leq C' / n^2$ for some $C' > 0$.
      obtain ⟨C', hC'_pos, hC'⟩ : ∃ C' > 0, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R → |c2_h x y / (n : ℝ)^2| ≤ C' / (n : ℝ)^2 := by
        -- We'll use the fact that $|c2_h x y| \leq C'$ for some $C' > 0$.
        obtain ⟨C', hC'_pos, hC'⟩ : ∃ C' > 0, ∀ y : ℝ, |y| ≤ R → |c2_h x y| ≤ C' := by
          unfold c2_h;
          exact ⟨ |( 1 - Real.exp ( -x ) ) / 2| + Real.exp ( -x ) * ( |R| + 1 ), by positivity, fun y hy => abs_le.mpr ⟨ by cases abs_cases ( ( 1 - Real.exp ( -x ) ) / 2 ) <;> cases abs_cases R <;> nlinarith [ Real.exp_pos ( -x ), abs_le.mp hy ], by cases abs_cases ( ( 1 - Real.exp ( -x ) ) / 2 ) <;> cases abs_cases R <;> nlinarith [ Real.exp_pos ( -x ), abs_le.mp hy ] ⟩ ⟩;
        exact ⟨ C', hC'_pos, fun n hn y hy => by rw [ abs_div, abs_sq ] ; gcongr ; aesop ⟩;
      refine' ⟨ C + C', by positivity, N + 1, fun n hn y hy => _ ⟩ ; specialize hN n ( by linarith ) y hy ; specialize hC' n ( by linarith ) y hy ; simp_all +decide [ abs_le ];
      ring_nf at *;
      constructor <;> nlinarith [ show ( n : ℝ ) ⁻¹ ^ 3 ≤ ( n : ℝ ) ⁻¹ ^ 2 by exact pow_le_pow_of_le_one ( by positivity ) ( inv_le_one_of_one_le₀ ( by norm_cast; linarith ) ) ( by norm_num ) ];
    -- Using the bound on $|h_def x y n - c1_h x / n|$, we can bound $|h_def x y n^2 - c1_h x^2 / n^2|$.
    have h_bound_sq : ∃ C' > 0, ∃ N' : ℕ, ∀ n ≥ N', ∀ y : ℝ, |y| ≤ R → |h_def x y n^2 - c1_h x^2 / n^2| ≤ C' / n^3 := by
      -- Using the bound on $|h_def x y n - c1_h x / n|$, we can bound $|h_def x y n + c1_h x / n|$.
      have h_bound_sum : ∃ C'' > 0, ∃ N'' : ℕ, ∀ n ≥ N'', ∀ y : ℝ, |y| ≤ R → |h_def x y n + c1_h x / n| ≤ C'' / n := by
        -- Using the bound on $|h_def x y n - c1_h x / n|$, we can bound $|h_def x y n + c1_h x / n|$ by $|h_def x y n - c1_h x / n| + 2|c1_h x / n|$.
        have h_bound_sum : ∃ C'' > 0, ∃ N'' : ℕ, ∀ n ≥ N'', ∀ y : ℝ, |y| ≤ R → |h_def x y n + c1_h x / n| ≤ |h_def x y n - c1_h x / n| + 2 * |c1_h x / n| := by
          exact ⟨ 1, by norm_num, 0, fun n hn y hy => by cases abs_cases ( h_def x y n + c1_h x / n ) <;> cases abs_cases ( h_def x y n - c1_h x / n ) <;> cases abs_cases ( c1_h x / n ) <;> linarith ⟩;
        obtain ⟨ C'', hC''_pos, N'', hN'' ⟩ := h_bound_sum;
        refine' ⟨ C + 2 * |c1_h x| + 1, by positivity, Max.max N N'' + 1, fun n hn y hy => le_trans ( hN'' n ( by linarith [ le_max_left N N'', le_max_right N N'' ] ) y hy ) _ ⟩;
        refine le_trans ( add_le_add ( hN n ( by linarith [ le_max_left N N'' ] ) y hy ) ( mul_le_mul_of_nonneg_left ( show |c1_h x / n| ≤ |c1_h x| / n from by rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ n ) ] ) zero_le_two ) ) ?_;
        rw [ div_add', div_le_div_iff₀ ] <;> nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast; linarith [ le_max_left N N'', le_max_right N N'' ], abs_nonneg ( c1_h x ), mul_div_cancel₀ ( |c1_h x| : ℝ ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith [ le_max_left N N'', le_max_right N N'' ] ), pow_two ( n - 1 : ℝ ) ];
      -- Using the bounds on $|h_def x y n - c1_h x / n|$ and $|h_def x y n + c1_h x / n|$, we can bound $|h_def x y n^2 - c1_h x^2 / n^2|$.
      obtain ⟨C'', hC''_pos, N'', hN''⟩ := h_bound_sum;
      use C * C'', by
        positivity, max N N''; intros n hn y hy; (
      convert mul_le_mul ( hN n ( le_trans ( le_max_left _ _ ) hn ) y hy ) ( hN'' n ( le_trans ( le_max_right _ _ ) hn ) y hy ) ( by positivity ) ( by positivity ) using 1 <;> ring_nf;
      rw [ ← abs_mul ] ; ring_nf;);
    obtain ⟨ C', hC'_pos, N', hN' ⟩ := h_bound_sq; exact ⟨ C' / 2, half_pos hC'_pos, N', fun n hn y hy => abs_le.mpr ⟨ by have := abs_le.mp ( hN' n hn y hy ) ; ring_nf at *; linarith, by have := abs_le.mp ( hN' n hn y hy ) ; ring_nf at *; linarith ⟩ ⟩ ;

/-
Coefficients for the inverse term expansion.
-/
noncomputable def c1_inv (x : ℝ) : ℝ := (Real.exp (-x) - 1) / 2
noncomputable def c2_inv (x : ℝ) : ℝ := (Real.exp (-x) + Real.exp (-2 * x) - 2) / 4

/-
Helper lemma: The difference f(n) - f(n-1) approximates 1/n with an error of order 1/n^5.
-/
theorem lem_f_diff_bound : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → |f n - f (n - 1) - 1 / n| ≤ C / (n : ℝ) ^ 5 := by
  -- We compute the difference f(n) - f(n-1) using Taylor expansions in powers of 1/n.
  -- f(n) - f(n-1) = log(n) - log(n-1) + 1/(2n) - 1/(2(n-1)) - 1/(12n^2) + 1/(12(n-1)^2).
  -- Using log(n) - log(n-1) = -log(1 - 1/n) = 1/n + 1/(2n^2) + 1/(3n^3) + 1/(4n^4) + O(1/n^5),
  -- and expanding the rational terms, we find that the terms of order 1/n, 1/n^2, 1/n^3, 1/n^4 all cancel out.
  -- Thus the difference is O(1/n^5).
  have h_diff : ∀ n : ℕ, n ≥ 2 → |f n - f (n - 1) - 1 / (n : ℝ)| ≤ 10 / (n : ℝ) ^ 5 := by
    intros n hn_ge_2
    have h_log : |Real.log (n : ℝ) - Real.log ((n - 1) : ℝ) - (1 / (n : ℝ) + 1 / (2 * (n : ℝ)^2) + 1 / (3 * (n : ℝ)^3) + 1 / (4 * (n : ℝ)^4))| ≤ 1 / (n : ℝ)^5 := by
      -- Using the integral representation of the logarithm, we can bound the difference.
      have h_log_integral : Real.log n - Real.log (n - 1) = ∑ k ∈ Finset.range 4, (1 / (n : ℝ) ^ (k + 1)) / (k + 1) + ∫ x in (0 : ℝ)..1 / n, (x ^ 4) / (1 - x) := by
        have h_log_integral : ∀ x : ℝ, 0 < x ∧ x < 1 → Real.log (1 / (1 - x)) = ∑ k ∈ Finset.range 4, x ^ (k + 1) / (k + 1) + ∫ t in (0 : ℝ)..x, t ^ 4 / (1 - t) := by
          intros x hx
          have h_log_integral : ∫ t in (0 : ℝ)..x, t ^ 4 / (1 - t) = ∫ t in (0 : ℝ)..x, (1 / (1 - t) - ∑ k ∈ Finset.range 4, t ^ k) := by
            refine' intervalIntegral.integral_congr fun t ht => _;
            rw [ div_sub' ] <;> norm_num [ Finset.sum_range_succ ] ; ring ; cases Set.mem_uIcc.mp ht <;> linarith;
          rw [ h_log_integral, intervalIntegral.integral_sub ] <;> norm_num;
          · rw [ integral_inv_of_pos, intervalIntegral.integral_finset_sum ] <;> norm_num [ Finset.sum_range_succ ] ; linarith;
          · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( continuousAt_const.sub continuousAt_id ) ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx.1.le ] using ht ) ] ) );
          · exact Continuous.intervalIntegrable ( by continuity ) _ _;
        convert h_log_integral ( 1 / n ) ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ⟩ using 1 <;> norm_num;
        rw [ ← Real.log_div ( by positivity ) ( by exact ne_of_gt ( by norm_num; linarith ) ), inv_eq_one_div, one_sub_div ( by positivity ) ];
        rw [ ← Real.log_inv, inv_div ];
      -- We'll use the fact that $\int_0^{1/n} \frac{x^4}{1-x} \, dx$ is bounded.
      have h_integral_bound : |∫ x in (0 : ℝ)..1 / n, x^4 / (1 - x)| ≤ ∫ x in (0 : ℝ)..1 / n, x^4 / (1 - 1 / n) := by
        rw [ abs_of_nonneg ( intervalIntegral.integral_nonneg ( by positivity ) fun x hx => div_nonneg ( pow_nonneg hx.1 _ ) ( sub_nonneg.2 <| by exact hx.2.trans <| div_le_one_of_le₀ ( by norm_cast; linarith ) <| by positivity ) ) ];
        refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
        · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( continuousAt_id.pow 4 ) ( continuousAt_const.sub continuousAt_id ) ( by linarith [ show ( x : ℝ ) ≤ 1 / n by exact ( Set.mem_Icc.mp <| by simpa [ show ( 0 : ℝ ) ≤ 1 / n by positivity ] using hx ) |>.2, show ( 1 : ℝ ) / n < 1 by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ] ) );
        · field_simp;
          intro x hx₁ hx₂; rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, pow_nonneg hx₁ 2, pow_nonneg hx₁ 3, pow_nonneg hx₁ 4, mul_le_mul_of_nonneg_left ( show ( n : ℝ ) ≥ 2 by norm_cast ) ( pow_nonneg hx₁ 4 ) ] ;
      norm_num [ Finset.sum_range_succ ] at *;
      rw [ abs_le ];
      constructor <;> nlinarith [ abs_le.mp h_integral_bound, show ( n : ℝ ) ≥ 2 by norm_cast, inv_pos.mpr ( by positivity : 0 < ( n : ℝ ) ), inv_pos.mpr ( by positivity : 0 < ( n ^ 2 : ℝ ) ), inv_pos.mpr ( by positivity : 0 < ( n ^ 3 : ℝ ) ), inv_pos.mpr ( by positivity : 0 < ( n ^ 4 : ℝ ) ), inv_pos.mpr ( by positivity : 0 < ( n ^ 5 : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( n ^ 2 : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( n ^ 3 : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( n ^ 4 : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( n ^ 5 : ℝ ) ≠ 0 ), div_mul_cancel₀ ( ( n ^ 5 : ℝ ) ⁻¹ / 5 ) ( by nlinarith [ inv_mul_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ), ( by norm_cast : ( 2 :ℝ ) ≤ n ) ] : ( 1 - ( n :ℝ ) ⁻¹ ) ≠ 0 ) ];
    -- Using the bounds from Lemma 25, we can simplify the expression.
    have h_simplify : |(1 / (2 * (n : ℝ)) - 1 / (2 * ((n - 1) : ℝ))) - (-1 / (2 * (n : ℝ)^2) - 1 / (2 * (n : ℝ)^3) - 1 / (2 * (n : ℝ)^4))| ≤ 1 / (n : ℝ)^5 ∧ |(-1 / (12 * (n : ℝ)^2) + 1 / (12 * ((n - 1) : ℝ)^2)) - (1 / (6 * (n : ℝ)^3) + 1 / (4 * (n : ℝ)^4))| ≤ 1 / (n : ℝ)^5 := by
      constructor <;> rw [ abs_le ] <;> constructor <;> ring_nf;
      · field_simp;
        nlinarith only [ show ( n : ℝ ) ≥ 2 by norm_cast, pow_pos ( show ( n : ℝ ) > 0 by positivity ) 2, pow_pos ( show ( n : ℝ ) > 0 by positivity ) 3, pow_pos ( show ( n : ℝ ) > 0 by positivity ) 4, mul_div_cancel₀ ( ( n : ℝ ) ^ 4 ) ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast ] : ( -1 + n : ℝ ) ≠ 0 ) ];
      · field_simp;
        nlinarith only [ show ( n : ℝ ) ≥ 2 by norm_cast, pow_pos ( by positivity : 0 < ( n : ℝ ) ) 2, pow_pos ( by positivity : 0 < ( n : ℝ ) ) 3, pow_pos ( by positivity : 0 < ( n : ℝ ) ) 4, mul_div_cancel₀ ( ( n : ℝ ) ^ 4 ) ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast ] : ( -1 + n : ℝ ) ≠ 0 ) ];
      · field_simp;
        rw [ add_div', mul_div_assoc' ] <;> try nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast ];
        rw [ le_div_iff₀ ] <;> nlinarith only [ show ( n : ℝ ) ≥ 2 by norm_cast, pow_pos ( show ( n : ℝ ) > 0 by positivity ) 3, pow_pos ( show ( n : ℝ ) > 0 by positivity ) 4 ];
      · field_simp;
        rw [ add_div', mul_div_assoc' ] <;> try nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ n ) ];
        rw [ div_le_iff₀ ] <;> nlinarith only [ show ( n : ℝ ) ≥ 2 by norm_cast, pow_pos ( show ( n : ℝ ) > 0 by positivity ) 3, pow_pos ( show ( n : ℝ ) > 0 by positivity ) 4 ];
    unfold f;
    rw [ Nat.cast_pred ( by linarith ) ] ; ring_nf at *; exact abs_le.mpr ⟨ by linarith [ abs_le.mp h_log, abs_le.mp h_simplify.1, abs_le.mp h_simplify.2 ], by linarith [ abs_le.mp h_log, abs_le.mp h_simplify.1, abs_le.mp h_simplify.2 ] ⟩ ;
  exact ⟨ 10, by norm_num, h_diff ⟩

/-
Lemma: The quantity delta = (m/(n-1) - e^x)/e^x has the expansion c1_delta/n + c2_delta/n^2 + O(1/n^3).
-/
noncomputable def delta_val (x y : ℝ) (n : ℕ) : ℝ := (m_def x y n / (n - 1) - Real.exp x) / Real.exp x

noncomputable def c1_delta (x : ℝ) : ℝ := (1 - Real.exp (-x)) / 2
noncomputable def c2_delta (x y : ℝ) : ℝ := (1 - Real.exp (-x)) / 2 + Real.exp (-x) * y

theorem lem_delta_expansion (x : ℝ) (hx : x > 0) (R : ℝ) :
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
  |delta_val x y n - (c1_delta x / n + c2_delta x y / n^2)| ≤ C / n^3 := by
    obtain ⟨ C, hC₀, N, hN ⟩ := h_bound_approx x hx ( R + 1 );
    refine' ⟨ C, hC₀, N + 2, fun n hn y hy => _ ⟩ ; simp_all +decide [ abs_le ];
    convert hN n ( by linarith ) y ( by linarith ) ( by linarith ) using 1 <;> unfold c1_delta c2_delta c1_h c2_h delta_val h_def <;> ring_nf;
    · rw [ show m_def x y n = Real.exp x * n + s_0 x + y / n by rfl ] ; norm_num [ Real.exp_neg ] ; ring_nf;
      field_simp;
      rw [ show s_0 x = - ( Real.exp x + 1 ) / 2 by rfl ] ; ring_nf;
      rw [ show ( -n + n ^ 2 : ℝ ) = n * ( -1 + n ) by ring ] ; norm_num ; ring_nf;
      constructor <;> intro <;> nlinarith [ inv_mul_cancel_left₀ ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ( Real.exp x ), inv_mul_cancel_left₀ ( show ( -1 + n : ℝ ) ≠ 0 by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] ) ( Real.exp x ), inv_mul_cancel_left₀ ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ( ( n : ℝ ) ⁻¹ ), inv_mul_cancel_left₀ ( show ( -1 + n : ℝ ) ≠ 0 by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] ) ( ( n : ℝ ) ⁻¹ ), Real.exp_pos x ];
    · unfold m_def; ring_nf;
      norm_num [ Real.exp_neg, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Real.exp_pos x ) ] ; ring_nf;
      rw [ show ( -1 + n : ℝ ) ⁻¹ = ( n : ℝ ) ⁻¹ * ( 1 - ( n : ℝ ) ⁻¹ ) ⁻¹ by rw [ ← mul_inv, mul_sub, mul_one, mul_inv_cancel₀ ( by norm_cast; linarith ) ] ; ring ] ; norm_num ; ring_nf;
      rw [ show s_0 x = - ( Real.exp x + 1 ) / 2 by rfl ] ; ring_nf;
      norm_num [ ne_of_gt ( Real.exp_pos x ), ne_of_gt ( show 0 < ( n : ℝ ) by norm_cast; linarith ) ] ; ring_nf;
      constructor <;> intro <;> nlinarith [ inv_pos.mpr ( show 0 < ( n : ℝ ) by norm_cast; linarith ), inv_pos.mpr ( show 0 < ( 1 - ( n : ℝ ) ⁻¹ ) by exact sub_pos.mpr ( inv_lt_one_of_one_lt₀ ( by norm_cast; linarith ) ) ), mul_inv_cancel₀ ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ), mul_inv_cancel₀ ( show ( 1 - ( n : ℝ ) ⁻¹ ) ≠ 0 by exact sub_ne_zero.mpr ( ne_of_gt ( inv_lt_one_of_one_lt₀ ( by norm_cast; linarith ) ) ) ) ]

/-
Lemma: The expansion of log(m/(n-1)) - x is c1/n + c2/n^2 + O(1/n^3).
-/
theorem lem_log_expansion (x : ℝ) (hx : x > 0) (R : ℝ) :
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
  |Real.log (m_def x y n / (n - 1)) - x - (c1_log x / n + c2_log x y / n^2)| ≤ C / n^3 := by
    obtain ⟨ C₁, hC₁, N₁, hN₁ ⟩ := @lem_delta_expansion x hx R;
    -- For large n, |delta| <= 1/2, so |log(1+delta) - (delta - delta^2/2)| <= |delta|^3.
    obtain ⟨ N₂, hN₂ ⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, ∀ y : ℝ, |y| ≤ R → |delta_val x y n| ≤ 1 / 2 := by
      -- By definition of $delta_val$, we know that $|delta_val x y n|$ is bounded for large $n$.
      have h_delta_bound : ∃ N₂ : ℕ, ∀ n ≥ N₂, ∀ y : ℝ, |y| ≤ R → |c1_delta x / n + c2_delta x y / n^2| ≤ 1 / 4 := by
        -- We'll use that $c1_delta x$ and $c2_delta x y$ are bounded.
        have h_bounded : ∃ M : ℝ, ∀ y : ℝ, |y| ≤ R → |c1_delta x| ≤ M ∧ |c2_delta x y| ≤ M := by
          unfold c1_delta c2_delta;
          norm_num [ abs_le ];
          exact ⟨ |(1 - Real.exp ( -x )) / 2| + |Real.exp ( -x )| * R, fun y hy₁ hy₂ => ⟨ ⟨ by cases abs_cases ( ( 1 - Real.exp ( -x ) ) / 2 ) <;> cases abs_cases ( Real.exp ( -x ) ) <;> nlinarith [ Real.exp_pos ( -x ) ], by cases abs_cases ( ( 1 - Real.exp ( -x ) ) / 2 ) <;> cases abs_cases ( Real.exp ( -x ) ) <;> nlinarith [ Real.exp_pos ( -x ) ] ⟩, by cases abs_cases ( ( 1 - Real.exp ( -x ) ) / 2 ) <;> cases abs_cases ( Real.exp ( -x ) ) <;> nlinarith [ Real.exp_pos ( -x ) ], by cases abs_cases ( ( 1 - Real.exp ( -x ) ) / 2 ) <;> cases abs_cases ( Real.exp ( -x ) ) <;> nlinarith [ Real.exp_pos ( -x ) ] ⟩ ⟩;
        obtain ⟨ M, hM ⟩ := h_bounded;
        refine' ⟨ ⌈4 * M * 4⌉₊ + 1, fun n hn y hy => _ ⟩ ; rw [ abs_le ] ; constructor <;> nlinarith [ Nat.le_ceil ( 4 * M * 4 ), show ( n : ℝ ) ≥ ⌈4 * M * 4⌉₊ + 1 by exact_mod_cast hn, abs_le.mp ( hM y hy |>.1 ), abs_le.mp ( hM y hy |>.2 ), div_mul_cancel₀ ( c1_delta x ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ), div_mul_cancel₀ ( c2_delta x y ) ( show ( n ^ 2 : ℝ ) ≠ 0 by norm_cast; nlinarith ) ];
      -- Choose N₂ such that for all n ≥ N₂, C₁ / n^3 ≤ 1/4.
      obtain ⟨ N₂, hN₂ ⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, C₁ / (n : ℝ) ^ 3 ≤ 1 / 4 := by
        exact ⟨ ⌈C₁ * 4⌉₊ + 1, fun n hn => by rw [ div_le_iff₀ ] <;> nlinarith [ Nat.le_ceil ( C₁ * 4 ), show ( n : ℝ ) ≥ ⌈C₁ * 4⌉₊ + 1 by exact_mod_cast hn, pow_two ( n : ℝ ) ] ⟩;
      exact ⟨ Max.max N₁ N₂ + h_delta_bound.choose, fun n hn y hy => abs_le.mpr ⟨ by linarith [ abs_le.mp ( hN₁ n ( by linarith [ le_max_left N₁ N₂, h_delta_bound.choose_spec n ( by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) y hy ] ) y hy ), abs_le.mp ( h_delta_bound.choose_spec n ( by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) y hy ), hN₂ n ( by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) ], by linarith [ abs_le.mp ( hN₁ n ( by linarith [ le_max_left N₁ N₂, h_delta_bound.choose_spec n ( by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) y hy ] ) y hy ), abs_le.mp ( h_delta_bound.choose_spec n ( by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) y hy ), hN₂ n ( by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) ] ⟩ ⟩;
    -- For large n, |delta|^3 is O(1/n^3), so we can bound the error term by a constant times 1/n^3.
    obtain ⟨ C₂, hC₂, N₃, hN₃ ⟩ : ∃ C₂ > 0, ∃ N₃ : ℕ, ∀ n ≥ N₃, ∀ y : ℝ, |y| ≤ R → |Real.log (1 + delta_val x y n) - (delta_val x y n - delta_val x y n ^ 2 / 2)| ≤ C₂ / (n : ℝ) ^ 3 := by
      obtain ⟨ C₂, hC₂, N₃, hN₃ ⟩ : ∃ C₂ > 0, ∃ N₃ : ℕ, ∀ n ≥ N₃, ∀ y : ℝ, |y| ≤ R → |delta_val x y n|^3 ≤ C₂ / (n : ℝ) ^ 3 := by
        -- Using the expansion from lem_delta_expansion, we can bound |delta_val x y n| by a constant times 1/n.
        obtain ⟨ C₃, hC₃, N₃, hN₃ ⟩ : ∃ C₃ > 0, ∃ N₃ : ℕ, ∀ n ≥ N₃, ∀ y : ℝ, |y| ≤ R → |delta_val x y n| ≤ C₃ / (n : ℝ) := by
          have h_bound : ∃ C₃ > 0, ∃ N₃ : ℕ, ∀ n ≥ N₃, ∀ y : ℝ, |y| ≤ R → |c1_delta x / (n : ℝ) + c2_delta x y / (n : ℝ)^2| ≤ C₃ / (n : ℝ) := by
            -- Since $|c2_delta x y|$ is bounded for $|y| \leq R$, we can find a constant $M$ such that $|c2_delta x y| \leq M$ for all $y$ with $|y| \leq R$.
            obtain ⟨ M, hM ⟩ : ∃ M > 0, ∀ y : ℝ, |y| ≤ R → |c2_delta x y| ≤ M := by
              exact ⟨ |( 1 - Real.exp ( -x ) ) / 2| + |Real.exp ( -x ) * R| + 1, by positivity, fun y hy => by rw [ show c2_delta x y = ( 1 - Real.exp ( -x ) ) / 2 + Real.exp ( -x ) * y by rfl ] ; exact abs_le.mpr ⟨ by cases abs_cases ( ( 1 - Real.exp ( -x ) ) / 2 ) <;> cases abs_cases ( Real.exp ( -x ) * R ) <;> nlinarith [ abs_le.mp hy, Real.exp_pos ( -x ) ], by cases abs_cases ( ( 1 - Real.exp ( -x ) ) / 2 ) <;> cases abs_cases ( Real.exp ( -x ) * R ) <;> nlinarith [ abs_le.mp hy, Real.exp_pos ( -x ) ] ⟩ ⟩;
            refine' ⟨ |c1_delta x| + M + 1, by linarith [ abs_nonneg ( c1_delta x ) ], 1, fun n hn y hy => _ ⟩;
            rw [ abs_le ];
            constructor <;> cases abs_cases ( c1_delta x ) <;> nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ ( |c1_delta x| + M + 1 ) ( by positivity : ( n : ℝ ) ≠ 0 ), div_mul_cancel₀ ( c1_delta x ) ( by positivity : ( n : ℝ ) ≠ 0 ), div_mul_cancel₀ ( c2_delta x y ) ( by positivity : ( n ^ 2 : ℝ ) ≠ 0 ), abs_le.mp ( hM.2 y hy ), show ( n : ℝ ) ^ 2 ≥ n by norm_cast; nlinarith ];
          obtain ⟨ C₃, hC₃, N₃, hN₃ ⟩ := h_bound;
          use C₃ + C₁ + 1, by positivity, max N₁ (max N₂ N₃) + 1; intros n hn y hy; specialize hN₁ n (by
          linarith [ Nat.le_max_left N₁ ( max N₂ N₃ ) ]) y hy; specialize hN₃ n (by
          linarith [ Nat.le_max_left N₁ ( max N₂ N₃ ), Nat.le_max_right N₁ ( max N₂ N₃ ), Nat.le_max_left N₂ N₃, Nat.le_max_right N₂ N₃ ]) y hy; specialize hN₂ n (by
          linarith [ Nat.le_max_left N₁ ( max N₂ N₃ ), Nat.le_max_right N₁ ( max N₂ N₃ ), Nat.le_max_left N₂ N₃, Nat.le_max_right N₂ N₃ ]) y hy; (
          rw [ abs_le ] at *;
          constructor <;> ring_nf at * <;> nlinarith [ inv_pos.mpr ( show 0 < ( n : ℝ ) by norm_cast; linarith [ Nat.le_max_left N₁ ( Max.max N₂ N₃ ), Nat.le_max_right N₁ ( Max.max N₂ N₃ ), Nat.le_max_left N₂ N₃, Nat.le_max_right N₂ N₃ ] ), mul_inv_cancel₀ ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith [ Nat.le_max_left N₁ ( Max.max N₂ N₃ ), Nat.le_max_right N₁ ( Max.max N₂ N₃ ), Nat.le_max_left N₂ N₃, Nat.le_max_right N₂ N₃ ] ) ]);
        exact ⟨ C₃ ^ 3, pow_pos hC₃ 3, N₃, fun n hn y hy => le_trans ( pow_le_pow_left₀ ( abs_nonneg _ ) ( hN₃ n hn y hy ) 3 ) ( by ring_nf; norm_num ) ⟩;
      -- Using the Taylor series expansion of log(1 + delta), we have |log(1 + delta) - (delta - delta^2/2)| ≤ |delta|^3.
      have h_log_taylor : ∀ delta : ℝ, |delta| ≤ 1 / 2 → |Real.log (1 + delta) - (delta - delta^2 / 2)| ≤ |delta|^3 := by
        exact fun delta a => taylor_log_bound delta a;
      exact ⟨ C₂, hC₂, Max.max N₂ N₃, fun n hn y hy => le_trans ( h_log_taylor _ ( hN₂ n ( le_trans ( le_max_left _ _ ) hn ) y hy ) ) ( hN₃ n ( le_trans ( le_max_right _ _ ) hn ) y hy ) ⟩;
    -- For large n, delta^2 is (c1_delta/n)^2 + O(1/n^3) = c1_delta^2/n^2 + O(1/n^3).
    obtain ⟨ C₃, hC₃, N₄, hN₄ ⟩ : ∃ C₃ > 0, ∃ N₄ : ℕ, ∀ n ≥ N₄, ∀ y : ℝ, |y| ≤ R → |delta_val x y n ^ 2 / 2 - (c1_delta x ^ 2 / (2 * (n : ℝ)^2))| ≤ C₃ / (n : ℝ) ^ 3 := by
      obtain ⟨ C₃, hC₃, N₄, hN₄ ⟩ := h_sq_bound_approx x hx R;
      use C₃, hC₃, N₄ + 2;
      intro n hn y hy; convert hN₄ n ( by linarith ) y hy using 1; unfold delta_val h_def c1_h c1_delta; ring_nf;
      unfold m_def; norm_num [ Real.exp_neg, Real.exp_ne_zero ] ; ring_nf;
      unfold s_0; ring_nf;
      norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, Real.exp_ne_zero ] ; ring_nf;
      rw [ show ( -1 + n : ℝ ) = ( 1 - n * 2 + n ^ 2 ) / ( n - 1 ) by rw [ eq_div_iff ] <;> nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] ] ; norm_num ; ring_nf;
      exact congr_arg _ ( by nlinarith [ inv_mul_cancel₀ ( by nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] : ( 1 - n * 2 + n ^ 2 : ℝ ) ≠ 0 ) ] );
    -- Substitute the expansion of delta into the goal.
    have h_subst : ∀ n ≥ max N₂ (max N₁ (max N₃ N₄)), ∀ y : ℝ, |y| ≤ R → Real.log (m_def x y n / (n - 1)) - x = Real.log (1 + delta_val x y n) := by
      intros n hn y hy
      have h_delta : m_def x y n / (n - 1) = Real.exp x * (1 + delta_val x y n) := by
        unfold delta_val m_def; ring_nf;
        norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, Real.exp_ne_zero ] ; ring;
      rw [ h_delta, Real.log_mul ( by positivity ) ( by linarith [ abs_le.mp ( hN₂ n ( by linarith [ le_max_left N₂ ( max N₁ ( max N₃ N₄ ) ) ] ) y hy ) ] ), Real.log_exp ] ; ring;
    refine' ⟨ C₁ + C₂ + C₃, by positivity, max N₂ ( max N₁ ( max N₃ N₄ ) ), fun n hn y hy => _ ⟩ ; simp_all +decide [ abs_le ];
    unfold c1_log c2_log c1_delta c2_delta at *;
    constructor <;> ring_nf at * <;> linarith [ hN₁ n hn.2.1 y hy.1 hy.2, hN₃ n hn.2.2.1 y hy.1 hy.2, hN₄ n hn.2.2.2 y hy.1 hy.2 ]

/-
Lemma: The expansion of 1/(2m) is c1_inv_m/n + c2_inv_m/n^2 + O(1/n^3).
-/
noncomputable def c1_inv_m (x : ℝ) : ℝ := Real.exp (-x) / 2
noncomputable def c2_inv_m (x : ℝ) : ℝ := (Real.exp (-2 * x) + Real.exp (-x)) / 4

theorem lem_inv_m_expansion (x : ℝ) (R : ℝ) :
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
  |1 / (2 * m_def x y n) - (c1_inv_m x / (n : ℝ) + c2_inv_m x / (n : ℝ)^2)| ≤ C / (n : ℝ)^3 := by
    -- We have $1/(2m) = 1/(2(e^x n + s)) = e^{-x}/(2n) * (1 + s e^{-x}/n)^{-1}$.
    -- $s e^{-x} = -(e^{-x}+1)/2 + y e^{-x}/n$.
    -- $(1 + s e^{-x}/n)^{-1} = 1 - s e^{-x}/n + O(1/n^2)$.
    -- $1/(2m) = e^{-x}/(2n) (1 - (-(e^{-x}+1)/2)/n) + O(1/n^3)$
    -- $= e^{-x}/(2n) + e^{-x}(e^{-x}+1)/(4n^2) + O(1/n^3)$
    -- $= e^{-x}/(2n) + (e^{-2x}+e^{-x})/(4n^2) + O(1/n^3)$.
    have h_inv_m_expansion : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
      |1 / (2 * (Real.exp x * n + s_0 x + y / n)) - (Real.exp (-x) / (2 * n) + (Real.exp (-2 * x) + Real.exp (-x)) / (4 * n^2))| ≤ C / (n : ℝ)^3 := by
        -- Let's simplify the expression inside the absolute value.
        suffices h_simplify : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
          |(1 / (1 + ((s_0 x + y / n) * Real.exp (-x)) / n) - (1 - (-(Real.exp (-x) + 1) / 2) / n)) / (2 * n * Real.exp x)| ≤ C / (n : ℝ)^3 by
            obtain ⟨ C, hC₀, N, hN ⟩ := h_simplify; use C, hC₀, N+2; intros n hn y hy; convert hN n ( by linarith ) y hy using 1 ; ring_nf;
            norm_num [ Real.exp_neg, Real.exp_mul ] ; ring_nf;
            field_simp;
            field_simp;
            rw [ show ( Real.exp x * ( - ( n * 4 ) + -2 ) + -2 ) / n ^ 2 + Real.exp x ^ 2 * 4 / ( ( Real.exp x * n ^ 2 + y ) / n + s_0 x ) = ( Real.exp x * ( n * 4 * ( -1 + Real.exp x / ( Real.exp x + s_0 x / n + y / n ^ 2 ) ) + -2 ) + -2 ) / ( n ^ 2 ) by
                  by_cases hn : n = 0 <;> simp_all +decide [s_0, div_eq_mul_inv, mul_assoc,
                    mul_comm, sq] ; ring_nf;
                  field_simp [hn]
                  ring ] ; ring_nf;
        -- We'll use the fact that $1 / (1 + z) = 1 - z + O(z^2)$ for $z$ close to $0$.
        have h_inv_approx : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
          |1 / (1 + ((s_0 x + y / n) * Real.exp (-x)) / n) - (1 - ((s_0 x + y / n) * Real.exp (-x)) / n)| ≤ C / (n : ℝ)^2 := by
            -- We'll use the fact that $|(1 + z)^{-1} - (1 - z)| \leq 2z^2$ for $|z| \leq 1/2$.
            have h_inv_approx : ∀ z : ℝ, |z| ≤ 1 / 2 → |1 / (1 + z) - (1 - z)| ≤ 2 * z^2 := by
              intro z hz; rw [ abs_le ] ; constructor <;> nlinarith [ abs_le.mp hz, mul_div_cancel₀ 1 ( show ( 1 + z ) ≠ 0 by linarith [ abs_le.mp hz ] ), sq_nonneg ( z ) ] ;
            -- Let's choose $C = 2 * (|s_0 x| + R + 1)^2 * \exp(-2x)$.
            use 2 * (|s_0 x| + R + 1)^2 * Real.exp (-2 * x) + 1, by
              positivity;
            refine' ⟨ ⌈2 * ( |s_0 x| + R + 1 ) * Real.exp ( -x ) ⌉₊ + 1, fun n hn y hy => le_trans ( h_inv_approx _ _ ) _ ⟩ <;> norm_num [ abs_div, abs_mul, abs_of_nonneg, Real.exp_nonneg ] at *;
            · rw [ div_le_iff₀ ( by norm_cast; linarith ) ];
              rw [ abs_le ] at *;
              cases abs_cases ( s_0 x + y / n ) <;> cases abs_cases ( s_0 x ) <;> nlinarith [ Nat.le_ceil ( 2 * ( |s_0 x| + R + 1 ) * Real.exp ( -x ) ), show ( n : ℝ ) ≥ ⌈2 * ( |s_0 x| + R + 1 ) * Real.exp ( -x ) ⌉₊ + 1 by exact_mod_cast hn, Real.exp_pos ( -x ), mul_div_cancel₀ y ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ];
            · -- Let's simplify the expression inside the absolute value further.
              have h_simplify : |(s_0 x + y / n) * Real.exp (-x)| ≤ (|s_0 x| + R + 1) * Real.exp (-x) := by
                rw [ abs_mul, abs_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ];
                gcongr;
                exact abs_le.mpr ⟨ by cases abs_cases ( s_0 x ) <;> nlinarith [ abs_le.mp hy, show ( n : ℝ ) ≥ ⌈2 * ( |s_0 x| + R + 1 ) * Real.exp ( -x ) ⌉₊ + 1 by exact_mod_cast hn, Real.exp_pos ( -x ), mul_div_cancel₀ y ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ], by cases abs_cases ( s_0 x ) <;> nlinarith [ abs_le.mp hy, show ( n : ℝ ) ≥ ⌈2 * ( |s_0 x| + R + 1 ) * Real.exp ( -x ) ⌉₊ + 1 by exact_mod_cast hn, Real.exp_pos ( -x ), mul_div_cancel₀ y ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ] ⟩;
              rw [ div_pow, mul_div_assoc' ];
              gcongr;
              rw [ show ( - ( 2 * x ) ) = -x + -x by ring, Real.exp_add ] ; nlinarith [ abs_le.mp h_simplify, Real.exp_pos ( -x ), Real.exp_pos ( -x + -x ) ] ;
        -- We'll use the fact that $|(s_0 x + y / n) * Real.exp (-x) / n - (-(Real.exp (-x) + 1) / 2) / n| \leq C / n^2$ for some constant $C$.
        have h_diff_approx : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
          |((s_0 x + y / n) * Real.exp (-x) / n) - (-(Real.exp (-x) + 1) / 2) / n| ≤ C / (n : ℝ)^2 := by
            unfold s_0; ring_nf; norm_num;
            field_simp;
            refine' ⟨ 2 * ( |Real.exp ( -x ) * Real.exp x| + |Real.exp ( -x ) * 2 * R| + 1 ), by positivity, 1, fun n hn y hy => _ ⟩ ; rw [ abs_div ] ; norm_num [ abs_mul, abs_of_nonneg, hn ];
            field_simp;
            rw [ abs_le ] ; constructor <;> cases abs_cases R <;> nlinarith [ abs_le.mp hy, Real.exp_pos x, Real.exp_pos ( -x ), Real.exp_neg x, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos x ) ), mul_le_mul_of_nonneg_left ( show ( n : ℝ ) ≥ 1 by norm_cast ) ( Real.exp_nonneg x ), mul_le_mul_of_nonneg_left ( show ( n : ℝ ) ≥ 1 by norm_cast ) ( Real.exp_nonneg ( -x ) ) ];
        -- By combining the results from h_inv_approx and h_diff_approx, we can bound the expression.
        obtain ⟨C1, hC1_pos, N1, hC1⟩ := h_inv_approx
        obtain ⟨C2, hC2_pos, N2, hC2⟩ := h_diff_approx
        use (C1 + C2) / (2 * Real.exp x), by
          positivity, max N1 N2 + 1;
        intros n hn y hy
        have h_combined : |(1 / (1 + ((s_0 x + y / n) * Real.exp (-x)) / n) - (1 - (-(Real.exp (-x) + 1) / 2) / n))| ≤ (C1 + C2) / (n : ℝ)^2 := by
          have := hC1 n ( by linarith [ le_max_left N1 N2 ] ) y hy; have := hC2 n ( by linarith [ le_max_right N1 N2 ] ) y hy; rw [ abs_le ] at *; constructor <;> ring_nf at * <;> linarith;
        rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 * n * Real.exp x ) ];
        convert mul_le_mul_of_nonneg_right h_combined ( inv_nonneg.mpr ( show ( 0 : ℝ ) ≤ 2 * n * Real.exp x by positivity ) ) using 1 ; ring;
    convert h_inv_m_expansion using 8 ;unfold m_def c1_inv_m c2_inv_m ; ring_nf!

/-
Lemma: The expansion of 1/(2(n-1)) is 1/(2n) + 1/(2n^2) + O(1/n^3).
-/
theorem lem_inv_n_expansion :
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
  |1 / (2 * ((n : ℝ) - 1)) - (1 / (2 * (n : ℝ)) + 1 / (2 * (n : ℝ)^2))| ≤ C / (n : ℝ)^3 := by
    use 6; norm_num; use 2; intros n hn; rw [ abs_le ] ; constructor <;> ring_nf <;> norm_num at *;
    · field_simp;
      nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( ( n : ℝ ) ^ 2 ) ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast ] : ( -1 + n : ℝ ) ≠ 0 ) ];
    · field_simp;
      rw [ div_le_iff₀ ] <;> nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast ]

/-
Lemma: The expansion of 1/(2m) - 1/(2(n-1)) is c1_inv/n + c2_inv/n^2 + O(1/n^3).
-/
theorem lem_inv_expansion (x : ℝ) (R : ℝ) :
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
  |inv_term x y n - (c1_inv x / n + c2_inv x / n^2)| ≤ C / n^3 := by
    obtain ⟨ C₁, hC₁, N₁, hC₁N₁ ⟩ := lem_inv_m_expansion x R
    obtain ⟨ C₂, hC₂, N₂, hC₂N₂ ⟩ := lem_inv_n_expansion;
    use C₁ + C₂;
    refine' ⟨ add_pos hC₁ hC₂, Max.max N₁ N₂, fun n hn y hy => _ ⟩ ; simp_all +decide [ add_div ];
    convert le_trans ( abs_sub _ _ ) ( add_le_add ( hC₁N₁ n hn.1 y hy ) ( hC₂N₂ n hn.2 ) ) using 1 ; unfold inv_term ; ring_nf;
    unfold c1_inv c2_inv c1_inv_m c2_inv_m; ring_nf;
    rw [ show ( -2 + n * 2 : ℝ ) = 2 * ( -1 + n ) by ring, mul_inv ] ; ring_nf

/-
Lemma: The expansion of the quadratic term is c2_quad/n^2 + O(1/n^3).
-/
noncomputable def c2_quad (x : ℝ) : ℝ := (1 - Real.exp (-2 * x)) / 12

theorem lem_quad_expansion (x : ℝ) (R : ℝ) :
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
  |quad_term x y n - c2_quad x / n^2| ≤ C / n^3 := by
    by_contra! h_contra;
    -- By definition of $quad_term$, we have:
    have h_quad_def : ∀ n ≥ 2, ∀ y : ℝ, |y| ≤ R → quad_term x y n = -1 / (12 * (m_def x y n)^2) + 1 / (12 * ((n : ℝ) - 1)^2) := by
      exact fun n a y a => rfl;
    -- We have $1/m^2 = 1/(e^x n + s)^2 = e^{-2x}/n^2 * (1 + s e^{-x}/n)^{-2} = e^{-2x}/n^2 * (1 + O(1/n)) = e^{-2x}/n^2 + O(1/n^3)$.
    have h_inv_m_sq : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R → |1 / (m_def x y n)^2 - Real.exp (-2 * x) / ((n : ℝ)^2)| ≤ C / ((n : ℝ)^3) := by
      -- We have $1/m^2 = 1/(e^x n + s)^2 = e^{-2x}/n^2 * (1 + s e^{-x}/n)^{-2}$.
      have h_inv_m_sq : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R → |1 / (m_def x y n)^2 - Real.exp (-2 * x) / ((n : ℝ)^2) * (1 + (s_0 x + y / n) * Real.exp (-x) / n)^(-2 : ℝ)| ≤ C / ((n : ℝ)^3) := by
        -- We can factor out $e^{-2x}/n^2$ from the expression.
        have h_factor : ∀ n ≥ 2, ∀ y : ℝ, |y| ≤ R → 1 / (m_def x y n)^2 = Real.exp (-2 * x) / ((n : ℝ)^2) * (1 + (s_0 x + y / n) * Real.exp (-x) / n)^(-2 : ℝ) := by
          intros n hn y hy
          have h_m_def : m_def x y n = Real.exp x * n + s_0 x + y / n := by
            exact rfl
          have h_inv_m_sq : 1 / (m_def x y n)^2 = 1 / (Real.exp x * n * (1 + (s_0 x + y / n) * Real.exp (-x) / n))^2 := by
            rw [ h_m_def ] ; ring_nf; norm_num [ Real.exp_neg, Real.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, ne_of_gt ( zero_lt_two.trans_le hn ) ] ; ring_nf;
            -- Combine like terms and simplify the expression.
            field_simp
            ring
          have h_inv_m_sq_simplified : 1 / (m_def x y n)^2 = Real.exp (-2 * x) / ((n : ℝ)^2) * (1 + (s_0 x + y / n) * Real.exp (-x) / n)^(-2 : ℝ) := by
            rw [ h_inv_m_sq ] ; norm_cast ; norm_num ; ring_nf;
            rw [ inv_eq_iff_eq_inv ] ; norm_num ; ring_nf;
            norm_num [ ← Real.exp_nat_mul, ← Real.exp_neg ] ; ring_nf
          exact h_inv_m_sq_simplified ▸ rfl;
        exact ⟨ 1, by norm_num, 2, fun n hn y hy => by rw [ h_factor n hn y hy ] ; norm_num ⟩;
      -- We have $(1 + (s_0 x + y / n) * Real.exp (-x) / n)^{-2} = 1 + O(1/n)$.
      have h_inv_sq_approx : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R → |(1 + (s_0 x + y / n) * Real.exp (-x) / n)^(-2 : ℝ) - 1| ≤ C / ((n : ℝ)) := by
        -- We have $(1 + (s_0 x + y / n) * Real.exp (-x) / n)^{-2} = 1 + O(1/n)$ by the binomial approximation.
        have h_inv_sq_approx : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R → |(1 + (s_0 x + y / n) * Real.exp (-x) / n)^(-2 : ℝ) - 1| ≤ C * |(s_0 x + y / n) * Real.exp (-x) / n| := by
          -- We have $(1 + z)^{-2} = 1 - 2z + O(z^2)$ for $z$ close to $0$.
          have h_inv_sq_approx : ∃ C > 0, ∀ z : ℝ, |z| ≤ 1 / 2 → |(1 + z)^(-2 : ℝ) - 1| ≤ C * |z| := by
            use 8, by norm_num, fun z hz => ?_;
            norm_cast ; norm_num;
            rw [ abs_le ] at *;
            constructor <;> cases abs_cases z <;> nlinarith [ inv_mul_cancel₀ ( by nlinarith : ( 1 + z ) ^ 2 ≠ 0 ), pow_two_nonneg ( z + 1 / 2 ), pow_two_nonneg ( z - 1 / 2 ) ];
          -- Choose $N$ such that for all $n \geq N$, $|(s_0 x + y / n) * Real.exp (-x) / n| \leq 1 / 2$.
          obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R → |(s_0 x + y / n) * Real.exp (-x) / n| ≤ 1 / 2 := by
            -- We'll use the fact that |s_0 x + y / n| is bounded for large n.
            have h_bound : ∃ C > 0, ∀ n : ℕ, n ≥ 1 → ∀ y : ℝ, |y| ≤ R → |s_0 x + y / n| ≤ C := by
              use |s_0 x| + R + 1;
              exact ⟨ by linarith [ abs_nonneg ( s_0 x ), show 0 ≤ R by exact le_trans ( abs_nonneg _ ) ( h_contra 1 zero_lt_one 0 |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.left ) ], fun n hn y hy => abs_le.mpr ⟨ by cases abs_cases ( s_0 x ) <;> nlinarith [ abs_le.mp hy, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ y ( by positivity : ( n : ℝ ) ≠ 0 ) ], by cases abs_cases ( s_0 x ) <;> nlinarith [ abs_le.mp hy, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ y ( by positivity : ( n : ℝ ) ≠ 0 ) ] ⟩ ⟩;
            obtain ⟨ C, hC₀, hC ⟩ := h_bound;
            norm_num [ abs_div, abs_mul ];
            exact ⟨ ⌈2 * C * Real.exp ( -x ) ⌉₊ + 1, fun n hn y hy => by rw [ div_le_iff₀ ( by norm_cast; linarith ) ] ; nlinarith [ Nat.le_ceil ( 2 * C * Real.exp ( -x ) ), show ( n : ℝ ) ≥ ⌈2 * C * Real.exp ( -x ) ⌉₊ + 1 by exact_mod_cast hn, abs_nonneg ( s_0 x + y / n ), hC n ( by linarith ) y hy, Real.exp_pos ( -x ), mul_le_mul_of_nonneg_right ( hC n ( by linarith ) y hy ) ( Real.exp_nonneg ( -x ) ) ] ⟩;
          exact ⟨ h_inv_sq_approx.choose, h_inv_sq_approx.choose_spec.1, N, fun n hn y hy => h_inv_sq_approx.choose_spec.2 _ ( hN n hn y hy ) ⟩;
        -- We have $|(s_0 x + y / n) * Real.exp (-x) / n| \leq C / n$ for some constant $C$.
        have h_bound : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R → |(s_0 x + y / n) * Real.exp (-x) / n| ≤ C / ((n : ℝ)) := by
          use |s_0 x * Real.exp (-x)| + R * |Real.exp (-x)| + 1, by
            exact add_pos_of_nonneg_of_pos ( add_nonneg ( abs_nonneg _ ) ( mul_nonneg ( show 0 ≤ R by obtain ⟨ n, hn, y, hy, h ⟩ := h_contra 1 zero_lt_one 0; linarith [ abs_le.mp hy ] ) ( abs_nonneg _ ) ) ) zero_lt_one, 1, by
            intros n hn y hy
            have h_bound : |(s_0 x + y / n) * Real.exp (-x)| ≤ |s_0 x * Real.exp (-x)| + R * |Real.exp (-x)| := by
              rw [ abs_mul, abs_mul ];
              rw [ ← add_mul ];
              exact mul_le_mul_of_nonneg_right ( abs_le.mpr ⟨ by cases abs_cases ( s_0 x ) <;> cases abs_cases y <;> nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ y ( by positivity : ( n : ℝ ) ≠ 0 ) ], by cases abs_cases ( s_0 x ) <;> cases abs_cases y <;> nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ y ( by positivity : ( n : ℝ ) ≠ 0 ) ] ⟩ ) ( abs_nonneg _ );
            rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ n ) ] ; gcongr ; linarith [ abs_nonneg ( ( s_0 x + y / n ) * Real.exp ( -x ) ) ] ;
        obtain ⟨ C₁, hC₁, N₁, hN₁ ⟩ := h_inv_sq_approx; obtain ⟨ C₂, hC₂, N₂, hN₂ ⟩ := h_bound; exact ⟨ C₁ * C₂, mul_pos hC₁ hC₂, Max.max N₁ N₂, fun n hn y hy => le_trans ( hN₁ n ( le_trans ( le_max_left _ _ ) hn ) y hy ) ( by simpa only [ mul_div_assoc ] using mul_le_mul_of_nonneg_left ( hN₂ n ( le_trans ( le_max_right _ _ ) hn ) y hy ) hC₁.le ) ⟩ ;
      obtain ⟨ C₁, hC₁_pos, N₁, hN₁ ⟩ := h_inv_m_sq
      obtain ⟨ C₂, hC₂_pos, N₂, hN₂ ⟩ := h_inv_sq_approx
      use C₁ + C₂ * Real.exp (-2 * x), by
        positivity, max N₁ N₂ + 1
      intro n hn y hy
      have h_diff : |Real.exp (-2 * x) / ((n : ℝ)^2) * ((1 + (s_0 x + y / n) * Real.exp (-x) / n)^(-2 : ℝ) - 1)| ≤ C₂ * Real.exp (-2 * x) / ((n : ℝ)^3) := by
        rw [ abs_mul, abs_of_nonneg ( by positivity ) ];
        convert mul_le_mul_of_nonneg_left ( hN₂ n ( by linarith [ Nat.le_max_right N₁ N₂ ] ) y hy ) ( by positivity : 0 ≤ Real.exp ( -2 * x ) / ( n : ℝ ) ^ 2 ) using 1 ; ring
      generalize_proofs at *;
      exact abs_le.mpr ⟨ by have := abs_le.mp ( hN₁ n ( by linarith [ le_max_left N₁ N₂ ] ) y hy ) ; have := abs_le.mp h_diff; ring_nf at *; linarith, by have := abs_le.mp ( hN₁ n ( by linarith [ le_max_left N₁ N₂ ] ) y hy ) ; have := abs_le.mp h_diff; ring_nf at *; linarith ⟩;
    -- We have $1/(n-1)^2 = 1/n^2 * (1 - 1/n)^{-2} = 1/n^2 * (1 + O(1/n)) = 1/n^2 + O(1/n^3)$.
    have h_inv_n_sq : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, |1 / ((n : ℝ) - 1)^2 - 1 / ((n : ℝ)^2)| ≤ C / ((n : ℝ)^3) := by
      refine' ⟨ 8, by norm_num, 2, fun n hn => _ ⟩ ; rw [ div_sub_div, abs_div ] <;> try ring_nf ; nlinarith [ show ( n : ℝ ) ≥ 2 by exact_mod_cast hn ];
      rw [ div_le_div_iff₀ ] <;> norm_num <;> cases abs_cases ( ( n : ℝ ) ^ 2 - ( n - 1 ) ^ 2 ) <;> cases abs_cases ( ( n - 1 : ℝ ) ^ 2 * n ^ 2 ) <;> nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, pow_pos ( show ( n : ℝ ) > 0 by positivity ) 3 ];
    -- Combining the above results, we get:
    obtain ⟨C1, hC1_pos, N1, hC1⟩ := h_inv_m_sq
    obtain ⟨C2, hC2_pos, N2, hC2⟩ := h_inv_n_sq;
    obtain ⟨ n, hn1, y, hy1, hy2 ⟩ := h_contra ( C1 / 12 + C2 / 12 + 1 ) ( by positivity ) ( N1 + N2 + 2 ) ; specialize hC1 n ( by linarith ) y hy1 ; specialize hC2 n ( by linarith ) ; specialize h_quad_def n ( by linarith ) y hy1 ; norm_num [ div_eq_mul_inv ] at *;
    unfold c2_quad at * ; norm_num at *;
    cases abs_cases ( quad_term x y n - ( 1 - Real.exp ( - ( 2 * x ) ) ) / 12 * ( n ^ 2 : ℝ ) ⁻¹ ) <;> cases abs_cases ( ( m_def x y n ^ 2 ) ⁻¹ - Real.exp ( - ( 2 * x ) ) * ( n ^ 2 : ℝ ) ⁻¹ ) <;> cases abs_cases ( ( ( n - 1 ) ^ 2 : ℝ ) ⁻¹ - ( n ^ 2 : ℝ ) ⁻¹ ) <;> linarith [ inv_pos.mpr ( show 0 < ( n : ℝ ) ^ 3 by norm_cast; exact pow_pos ( by linarith ) 3 ) ]

/-
Lemma: The sum of the first order coefficients is 0, and the sum of the second order coefficients matches the target term.
-/
theorem lem_coeff_sum (x : ℝ) (y : ℝ) :
  c1_log x + c1_inv x = 0 ∧
  c2_log x y + c2_inv x + c2_quad x = (24 * Real.exp (-x) * y + Real.exp (-2 * x) - 1) / 24 := by
    unfold c1_log c1_inv c2_log c2_inv c2_quad; ring_nf;
    rw [ ← Real.exp_nat_mul ] ; ring_nf;
    norm_num

/-
Lemma 2.2 (Corrected): With m = e^x n - 1/2 - e^x/2 + y/n, f(m) - f(n-1) - x = (24 e^{-x} y + e^{-2x} - 1)/24 * 1/n^2 + O(1/n^3).
-/
theorem lem_secondorder (x : ℝ) (hx : x > 0) (R : ℝ) :
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R →
  let m := Real.exp x * n - 1 / 2 - Real.exp x / 2 + y / n
  let term := (24 * Real.exp (-x) * y + Real.exp (-2 * x) - 1) / 24
  |f_real m - f_real (n - 1) - x - term / n ^ 2| ≤ C / n ^ 3 := by
    by_contra! h_contra;
    -- Apply the expansion bounds from the provided solution.
    obtain ⟨C₁, hC₁_pos, N₁, hC₁⟩ := lem_log_expansion x hx R
    obtain ⟨C₂, hC₂_pos, N₂, hC₂⟩ := lem_inv_expansion x R
    obtain ⟨C₃, hC₃_pos, N₃, hC₃⟩ := lem_quad_expansion x R;
    obtain ⟨N₄, hN₄⟩ : ∃ N₄ : ℕ, ∀ n ≥ N₄, ∀ y : ℝ, |y| ≤ R → m_def x y n > 0 ∧ (n - 1 : ℝ) > 0 := by
      use Nat.ceil ((|s_0 x| + R + 1) / Real.exp x) + 2;
      intro n hn y hy; constructor <;> norm_num [ m_def ] at *;
      · have : Real.exp x * n > |s_0 x| + R := by
          nlinarith [ Nat.le_ceil ( ( |s_0 x| + R + 1 ) / Real.exp x ), Real.exp_pos x, mul_div_cancel₀ ( |s_0 x| + R + 1 ) ( ne_of_gt ( Real.exp_pos x ) ), show ( n : ℝ ) ≥ ⌈ ( |s_0 x| + R + 1 ) / Real.exp x⌉₊ + 2 by exact_mod_cast hn ];
        cases abs_cases ( s_0 x ) <;> nlinarith [ abs_le.mp hy, show ( n : ℝ ) ≥ ⌈ ( |s_0 x| + R + 1 ) / Real.exp x⌉₊ + 2 by exact_mod_cast hn, mul_div_cancel₀ y ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ];
      · linarith;
    obtain ⟨N₅, hN₅⟩ : ∃ N₅ : ℕ, ∀ n ≥ N₅, ∀ y : ℝ, |y| ≤ R → f_real (m_def x y n) - f_real ((n : ℝ) - 1) - x = (Real.log (m_def x y n / (n - 1)) - x) + (inv_term x y n) + (quad_term x y n) := by
      use N₄ + 2; intros n hn y hy; rw [ Real.log_div ] <;> norm_num [ f_real, inv_term, quad_term ] ; ring ; linarith [ hN₄ n ( by linarith ) y hy ] ;
      linarith [ hN₄ n ( by linarith ) y hy ];
    -- Combine the expansion bounds from the provided solution.
    obtain ⟨C, hC_pos, N, hC⟩ : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y : ℝ, |y| ≤ R → |(Real.log (m_def x y n / (n - 1)) - x) + (inv_term x y n) + (quad_term x y n) - ((c1_log x + c1_inv x) / n + (c2_log x y + c2_inv x + c2_quad x) / n^2)| ≤ C / n^3 := by
      use C₁ + C₂ + C₃, by positivity, max N₁ (max N₂ (max N₃ N₄)) + N₅ + 1; intros n hn y hy; specialize hC₁ n ( by linarith [ Nat.le_max_left N₁ ( max N₂ ( max N₃ N₄ ) ), Nat.le_max_right N₁ ( max N₂ ( max N₃ N₄ ) ), Nat.le_max_left N₂ ( max N₃ N₄ ), Nat.le_max_right N₂ ( max N₃ N₄ ), Nat.le_max_left N₃ N₄, Nat.le_max_right N₃ N₄ ] ) y hy; specialize hC₂ n ( by linarith [ Nat.le_max_left N₁ ( max N₂ ( max N₃ N₄ ) ), Nat.le_max_right N₁ ( max N₂ ( max N₃ N₄ ) ), Nat.le_max_left N₂ ( max N₃ N₄ ), Nat.le_max_right N₂ ( max N₃ N₄ ), Nat.le_max_left N₃ N₄, Nat.le_max_right N₃ N₄ ] ) y hy; specialize hC₃ n ( by linarith [ Nat.le_max_left N₁ ( max N₂ ( max N₃ N₄ ) ), Nat.le_max_right N₁ ( max N₂ ( max N₃ N₄ ) ), Nat.le_max_left N₂ ( max N₃ N₄ ), Nat.le_max_right N₂ ( max N₃ N₄ ), Nat.le_max_left N₃ N₄, Nat.le_max_right N₃ N₄ ] ) y hy; ring_nf at *;
      exact abs_le.mpr ⟨ by linarith [ abs_le.mp hC₁, abs_le.mp hC₂, abs_le.mp hC₃ ], by linarith [ abs_le.mp hC₁, abs_le.mp hC₂, abs_le.mp hC₃ ] ⟩;
    obtain ⟨ n, hn₁, y, hy₁, hy₂ ⟩ := h_contra C hC_pos ( Max.max N N₅ ) ; specialize hC n ( le_trans ( le_max_left _ _ ) hn₁ ) y hy₁ ; specialize hN₅ n ( le_trans ( le_max_right _ _ ) hn₁ ) y hy₁ ; simp_all +decide [ add_assoc ] ;
    convert hy₂.not_ge _;
    convert hC using 1;
    rw [ ← hN₅ ] ; unfold m_def ; ring_nf;
    unfold c1_log c1_inv c2_log c2_inv c2_quad s_0 ; ring_nf;
    rw [ ← Real.exp_nat_mul ] ; ring_nf

/-
Corollary 2.3: If |f(m)-f(n-1) - x| <= epsilon/n^2 for arbitrarily small epsilon, then y must satisfy y = y^*.
-/
theorem cor_necessity_final (x : ℝ) (hx : x > 0) (R : ℝ) :
  ∃ C > 0, ∀ n : ℕ, n ≥ 2 → ∀ y : ℝ, |y| ≤ R →
  let m := Real.exp x * n - 1 + Real.exp x / 2 + y / n
  let y_star := Real.sinh x / 12
  (∀ ε > 0, ∃ N, ∀ n ≥ N, |f_real m - f_real (n - 1) - x| ≤ ε / n ^ 2) →
  abs (y - y_star) = 0 := by
    exact cor_necessity x hx R

/-
Lemma: m is positive for sufficiently large n.
-/
theorem m_def_pos (x : ℝ) (hx : x > 0) (R : ℝ) : ∃ N, ∀ n ≥ N, ∀ y, |y| ≤ R → m_def x y n > 0 := by
  -- Choose N such that for all n ≥ N, e^x * n - 1 - e^x/2 > (1 + e^x)/2 + R/n.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, Real.exp x * n - 1 - Real.exp x / 2 > (1 + Real.exp x) / 2 + R / 2 := by
    exact ⟨ ⌊ ( 1 + Real.exp x ) / 2 + R / 2 + 1 + Real.exp x / 2⌋₊ + 1, fun n hn => by nlinarith [ Nat.lt_of_floor_lt hn, Real.add_one_le_exp x ] ⟩;
  use N + 2;
  intros n hn y hy
  have h_pos : Real.exp x * n - 1 - Real.exp x / 2 > (1 + Real.exp x) / 2 + R / 2 := hN n (by linarith)
  have h_m_pos : m_def x y n > 0 := by
    unfold m_def;
    unfold s_0; rw [ add_div', gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ abs_le.mp hy, Real.exp_pos x, show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] ;
  exact h_m_pos

/-
The denominator $q_{3k+1}$ defined by the recurrence is always odd.
-/
theorem lem_q_rec_odd_proven (k : ℕ) : Odd (q_rec (3 * k + 1)) := by
  -- By definition of $q_rec$, we know that $q_rec (3 * k + 1)$ is odd.
  apply lem_q_rec_odd

/-
The numerator $p_{3k+1}$ defined by the recurrence is always odd.
-/
theorem lem_p_rec_odd_proven (k : ℕ) : Odd (p_rec (3 * k + 1)) := by
  -- By definition of $p_rec$, we know that $p_rec (3 * k + 1)$ is odd.
  apply lem_p_rec_odd

/-
The values of the continued fraction coefficients of e at indices 3k, 3k+1, 3k+2.
-/
theorem e_coeff_values_proven (k : ℕ) :
  e_coeff (3 * k + 2) = 2 * (k + 1) ∧
  (k > 0 → e_coeff (3 * k) = 1) ∧
  e_coeff (3 * k + 1) = 1 := by
    exact e_coeff_values k

/-
Real.convergent is equivalent to GenContFract.convs for real numbers.
-/
theorem real_convergent_eq_gen_cont_fract_convs (x : ℝ) (n : ℕ) :
  Real.convergent x n = (GenContFract.of x).convs n := by
    -- By definition of `Real.convergent`, we know that it is equal to the convergent of the continued fraction `GenContFract.of x`.
    have h_convergent_eq : ∀ n, Real.convergent x n = (GenContFract.of x).convs n := by
      intro n;
      convert congr_arg _ ( Rat.num_div_den _ ) using 1;
      convert Rat.cast_inj.mpr rfl;
      rw [ Rat.num_div_den ];
      · infer_instance;
      · exact Real.convs_eq_convergent x n;
    exact h_convergent_eq n

/-
The 'a' coefficients in the generalized continued fraction of a real number are always 1.
-/
theorem gen_cont_fract_of_a_eq_one (x : ℝ) (n : ℕ) :
  let g := GenContFract.of x
  match g.s.get? n with
  | some gp => gp.a = 1
  | none => True := by
    unfold GenContFract.of;
    induction n <;> aesop

/-
The determinant formula for the generalized continued fraction of e: nums(n+1)*dens(n) - nums(n)*dens(n+1) = (-1)^n.
-/
theorem gen_cont_fract_determinant_exp (n : ℕ) :
  let g := GenContFract.of (Real.exp 1)
  g.nums (n + 1) * g.dens n - g.nums n * g.dens (n + 1) = (-1 : ℝ) ^ n := by
    induction' n with n ih <;> norm_num [ pow_succ, GenContFract.nums, GenContFract.dens ] at *;
    · unfold GenContFract.of; norm_num [ Stream'.map, Stream'.get ] ;
      unfold GenContFract.IntFractPair.seq1; norm_num [ Real.exp_pos ] ;
      unfold GenContFract.conts ;
      unfold Stream'.tail; norm_num [ GenContFract.IntFractPair.stream ] ;
      unfold Stream'.get; norm_num [ GenContFract.IntFractPair.stream ] ;
      unfold GenContFract.contsAux; norm_num [ GenContFract.IntFractPair.stream ] ;
      unfold GenContFract.IntFractPair.of; norm_num [ Real.exp_pos ] ;
      unfold GenContFract.nextConts; norm_num [ Int.fract_eq_iff ] ;
      split_ifs <;> norm_num [ GenContFract.nextNum, GenContFract.nextDen ];
      · obtain ⟨ z, hz ⟩ := ‹_›; have := Real.exp_one_gt_d9.le; norm_num at this; rcases z with ⟨ _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | z ⟩ <;> norm_num at * <;> linarith [ Real.exp_one_lt_d9.le ] ;
      · ring;
    · rw [ ← ih ];
      simp +decide [ Stream'.map, GenContFract.of ];
      simp +decide [ GenContFract.conts ];
      erw [ Stream'.get ] ; norm_num [ GenContFract.IntFractPair.seq1 ] ; ring_nf;
      rw [ show 3 + n = 2 + n + 1 by ring, show 2 + n = 1 + n + 1 by ring ] ; simp +decide [ GenContFract.contsAux ] ; ring_nf;
      cases h : GenContFract.IntFractPair.stream ( Real.exp 1 ) ( 2 + n ) <;> simp +decide;
      · have h_contra : ∀ n, GenContFract.IntFractPair.stream (Real.exp 1) n ≠ none := by
          have h_irrational : Irrational (Real.exp 1) := by
            by_contra h_contra
            obtain ⟨p, q, hq_pos, hpq_eq⟩ : ∃ p q : ℕ, q > 0 ∧ Real.exp 1 = p / q := by
              obtain ⟨ q, hq ⟩ := Classical.not_not.mp h_contra; exact ⟨ q.num.natAbs, q.den, Nat.cast_pos.mpr q.pos, by simpa [ abs_of_nonneg ( Rat.num_nonneg.mpr ( show 0 ≤ q by exact_mod_cast hq.symm ▸ Real.exp_nonneg _ ) ), Rat.cast_def ] using hq.symm ⟩ ;
            -- Multiply both sides of the equation by $q!$ to obtain a contradiction.
            have h_factorial : ∑ k ∈ Finset.range (q + 1), (q ! / k ! : ℝ) + ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) = p * q ! / q := by
              have h_factorial : ∑' k : ℕ, (q ! / k ! : ℝ) = p * q ! / q := by
                have h_factorial : ∑' k : ℕ, (q ! / k ! : ℝ) = Real.exp 1 * q ! := by
                  norm_num [ div_eq_mul_inv, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ];
                  rw [ mul_comm, tsum_mul_left ];
                rw [ h_factorial, hpq_eq, div_mul_eq_mul_div ];
              rw [ ← h_factorial, ← Summable.sum_add_tsum_nat_add ];
              rotate_left;
              use 0;
              · exact Summable.mul_left _ <| by simpa using summable_nat_add_iff ( q + 1 ) |>.2 <| Real.summable_pow_div_factorial 1;
              · rw [ eq_comm, ← Summable.sum_add_tsum_nat_add ];
                rotate_left;
                exact q + 1;
                · exact Summable.mul_left _ <| by simpa using Real.summable_pow_div_factorial 1;
                · norm_num [ add_assoc ];
            -- The second sum is strictly between 0 and 1, hence it cannot be an integer.
            have h_second_sum : 0 < ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) ∧ ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) < 1 := by
              refine' ⟨ _, _ ⟩;
              · refine' Summable.tsum_pos ..;
                exacts [ Summable.mul_left _ <| by simpa using summable_nat_add_iff ( q + 1 ) |>.2 <| Real.summable_pow_div_factorial 1, fun _ => by positivity, 0, by positivity ];
              · -- We'll use that the series $\sum_{k=q+1}^{\infty} \frac{q!}{k!}$ is a geometric series with the first term $\frac{q!}{(q+1)!} = \frac{1}{q+1}$ and common ratio $\frac{1}{q+2}$.
                have h_geo_series : ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) ≤ ∑' k : ℕ, (1 / (q + 1) : ℝ) * (1 / (q + 2)) ^ k := by
                  refine' Summable.tsum_le_tsum _ _ _;
                  · field_simp;
                    intro i; rw [ one_div_pow ] ; rw [ mul_comm ] ; rw [ ← div_eq_mul_one_div ] ; rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast ; induction' i with i ih <;> norm_num [ Nat.factorial_succ, pow_succ' ] at *;
                    rw [ show i + 1 + q = i + q + 1 by ring, Nat.factorial_succ ];
                    nlinarith [ Nat.factorial_succ ( i + q ), pow_pos ( by linarith : 0 < q + 2 ) i ];
                  · exact Summable.mul_left _ <| by simpa using summable_nat_add_iff ( q + 1 ) |>.2 <| Real.summable_pow_div_factorial 1;
                  · exact Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by rw [ div_lt_iff₀ ] <;> linarith;
                refine' lt_of_le_of_lt h_geo_series _;
                rw [ tsum_mul_left, tsum_geometric_of_lt_one ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> linarith ) ];
                field_simp;
                rw [ div_lt_iff₀ ] <;> nlinarith only [ show ( q : ℝ ) ≥ 1 by norm_cast ];
            -- The first sum is an integer, hence the second sum must also be an integer.
            have h_first_sum_int : ∃ m : ℤ, ∑ k ∈ Finset.range (q + 1), (q ! / k ! : ℝ) = m := by
              use ∑ k ∈ Finset.range (q + 1), (q ! / k ! : ℤ);
              norm_num [ Finset.sum_div _ _ _ ];
              exact Finset.sum_congr rfl fun x hx => by rw [ Int.cast_div ( mod_cast Nat.factorial_dvd_factorial ( Finset.mem_range_succ_iff.mp hx ) ) ( by positivity ) ] ; push_cast; ring;
            obtain ⟨ m, hm ⟩ := h_first_sum_int;
            have h_second_sum_int : ∃ n : ℤ, ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) = n := by
              use p * q ! / q - m;
              rw [ Int.cast_sub, Int.cast_div ] <;> norm_num;
              · grind;
              · exact dvd_mul_of_dvd_right ( mod_cast Nat.dvd_factorial ( by positivity ) ( by linarith ) ) _;
              · linarith;
            obtain ⟨ n, hn ⟩ := h_second_sum_int; exact h_second_sum.2.not_ge ( hn.symm ▸ mod_cast Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ show ( n : ℝ ) ≥ 1 by exact_mod_cast hn ▸ h_second_sum.1 ] ) ) ;
          intro n; exact (by
          induction' n with n ih <;> simp +decide [ GenContFract.IntFractPair.stream ];
          cases h : GenContFract.IntFractPair.stream ( Real.exp 1 ) n <;> simp_all +decide;
          have h_irrational : ∀ n, GenContFract.IntFractPair.stream (Real.exp 1) n ≠ none → Irrational (GenContFract.IntFractPair.stream (Real.exp 1) n).get!.fr := by
            intro n hn; induction' n with n ih <;> simp +decide [ GenContFract.IntFractPair.stream ] at hn ⊢;
            · exact h_irrational.sub_ratCast _;
            · obtain ⟨ x, hx₁, hx₂ ⟩ := hn; simp_all +decide ;
              exact_mod_cast ih.inv.sub_ratCast ⌊x.fr⁻¹⌋;
          specialize h_irrational n ; aesop);
        exact False.elim (h_contra (2 + n) h);
      · unfold GenContFract.nextConts; ring_nf;
        unfold GenContFract.nextNum GenContFract.nextDen; ring_nf;
        ring!

/-
For any C > 0, and for large k, there exists an odd integer d such that d^2/k is close to C with error O(1/sqrt(k)).
-/
theorem lem_square_approx (C : ℝ) (hC : C > 0) :
  ∃ K : ℕ, ∀ k ≥ K,
  ∃ d : ℤ, Odd d ∧ |(d : ℝ)^2 / k - C| ≤ (2 * Real.sqrt C + 1) / Real.sqrt k := by
    -- Let's choose any $k$ such that $k > \frac{4C}{1} = 4C$.
    use Nat.ceil (4 * C) + 1;
    -- Let's choose any $k$ such that $k \geq \lceil 4C \rceil + 1$.
    intro k hk
    obtain ⟨d, hd_odd, hd_bound⟩ : ∃ d : ℤ, Odd d ∧ |d - Real.sqrt (k * C)| ≤ 1 := by
      have := exists_odd_near ( Real.sqrt ( k * C ) );
      exact this;
    -- Using the bound on |d - sqrt(kC)|, we can derive the bound on |d^2/k - C|.
    have h_bound : |(d : ℝ)^2 / k - C| ≤ (2 * Real.sqrt (k * C) + 1) / k := by
      rw [ abs_le ] at *;
      constructor <;> nlinarith [ show ( k : ℝ ) ≥ ⌈4 * C⌉₊ + 1 by exact_mod_cast hk, Real.sqrt_nonneg ( k * C ), Real.mul_self_sqrt ( show 0 ≤ ( k : ℝ ) * C by positivity ), mul_div_cancel₀ ( ( 2 * Real.sqrt ( k * C ) + 1 ) : ℝ ) ( show ( k : ℝ ) ≠ 0 by norm_cast; linarith ), mul_div_cancel₀ ( ( d : ℝ ) ^ 2 ) ( show ( k : ℝ ) ≠ 0 by norm_cast; linarith ) ];
    refine' ⟨ d, hd_odd, h_bound.trans _ ⟩ ; rw [ div_le_div_iff₀ ] <;> norm_num;
    · nlinarith only [ show ( k : ℝ ) ≥ ⌈4 * C⌉₊ + 1 by norm_cast, Nat.le_ceil ( 4 * C ), show ( 0 : ℝ ) < Real.sqrt C by positivity, show ( 0 : ℝ ) < Real.sqrt k by exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) ), Real.mul_self_sqrt ( show ( k : ℝ ) ≥ 0 by positivity ), Real.mul_self_sqrt ( show ( C : ℝ ) ≥ 0 by positivity ), sq_nonneg ( Real.sqrt k - 2 * Real.sqrt C ) ];
    · linarith;
    · linarith

/-
The ratio of consecutive denominators $q_{n+1}/q_n$ is bounded by $a_{n+1}$ and $a_{n+1} + 1$.
-/
theorem lem_q_ratio_bounds (n : ℕ) (h : n ≥ 1) :
  (e_coeff (n + 1) : ℝ) < (q_rec (n + 1) : ℝ) / q_rec n ∧
  (q_rec (n + 1) : ℝ) / q_rec n ≤ (e_coeff (n + 1) : ℝ) + 1 := by
    -- By definition of $q_rec$, we know that $q_rec (n + 1) = (e_coeff (n + 1)) * q_rec n + q_rec (n - 1)$.
    have h_q_rec_def : ∀ n ≥ 1, q_rec (n + 1) = (e_coeff (n + 1) : ℤ) * q_rec n + q_rec (n - 1) := by
      rintro ( _ | n ) <;> tauto
    generalize_proofs at *; (
    -- By definition of $q_rec$, we know that $q_rec n > 0$ for all $n \geq 0$.
    have h_q_rec_pos : ∀ n ≥ 0, 0 < q_rec n := by
      intro n hn; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide ;
      exact add_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by unfold e_coeff; aesop ) ) ) ( ih _ ( by linarith ) ) ) ( ih _ ( by linarith ) )
    generalize_proofs at *; (
    rw [ h_q_rec_def n h, lt_div_iff₀, div_le_iff₀ ] <;> norm_cast;
    · simp_all +decide [ add_mul ];
      rcases n with ( _ | _ | n ) <;> simp_all +decide;
      exact le_add_of_le_of_nonneg ( le_mul_of_one_le_left ( le_of_lt ( h_q_rec_pos _ ) ) ( mod_cast Nat.one_le_iff_ne_zero.mpr ( by unfold e_coeff; aesop ) ) ) ( le_of_lt ( h_q_rec_pos _ ) );
    · exact h_q_rec_pos n ( Nat.zero_le n );
    · exact h_q_rec_pos n ( Nat.zero_le n )))

/-
The determinant of the recurrence matrices satisfies $p_{n+1} q_n - p_n q_{n+1} = (-1)^n$.
-/
theorem lem_det_rec (n : ℕ) : p_rec (n + 1) * q_rec n - p_rec n * q_rec (n + 1) = (-1) ^ n := by
  induction' n with n ih <;> norm_num [ pow_succ', e_coeff_values ] at *;
  · native_decide +revert;
  · rw [ ← ih ];
    rw [ show p_rec ( n + 2 ) = e_coeff ( n + 2 ) * p_rec ( n + 1 ) + p_rec n from rfl, show q_rec ( n + 2 ) = e_coeff ( n + 2 ) * q_rec ( n + 1 ) + q_rec n from rfl ] ; ring

/-
The difference between consecutive convergents is $1/(q_n q_{n+1})$.
-/
theorem lem_convergent_diff (n : ℕ) :
  |(p_rec n : ℝ) / q_rec n - (p_rec (n + 1) : ℝ) / q_rec (n + 1)| = 1 / ((q_rec n : ℝ) * (q_rec (n + 1) : ℝ)) := by
    have h_det : (p_rec (n + 1) * q_rec n - p_rec n * q_rec (n + 1) : ℝ) = (-1 : ℝ) ^ n := by
      exact_mod_cast lem_det_rec n;
    rw [ div_sub_div, abs_div ];
    · rw [ show ( p_rec n : ℝ ) * q_rec ( n + 1 ) - q_rec n * p_rec ( n + 1 ) = ( -1 ) ^ n * -1 by linarith, abs_mul, abs_neg, abs_one, abs_pow ] ; norm_num;
      rw [ abs_of_nonneg, abs_of_nonneg ];
      · -- By definition of $q_rec$, we know that $q_rec n$ is positive for all $n$.
        have h_q_pos : ∀ n, 0 < q_rec n := by
          intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ q_rec ] ;
          exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( ih _ ( by linarith ) ) ) ) ( ih _ ( by linarith ) );
        exact_mod_cast le_of_lt ( h_q_pos n );
      · -- By definition of $q_rec$, we know that $q_rec (n + 1)$ is positive.
        have h_q_pos : ∀ n, 0 < q_rec n := by
          intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ q_rec ] ;
          exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( ih _ ( by linarith ) ) ) ) ( ih _ ( by linarith ) );
        exact_mod_cast le_of_lt ( h_q_pos _ );
    · -- By definition of $q_rec$, we know that $q_rec n$ is positive for all $n$.
      have h_q_pos : ∀ n, 0 < q_rec n := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ q_rec ] ;
        exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( ih _ ( by linarith ) ) ) ) ( ih _ ( by linarith ) );
      exact_mod_cast ne_of_gt ( h_q_pos n );
    · -- By definition of $q_rec$, we know that $q_rec (n + 1) > 0$ for all $n$.
      have h_q_pos : ∀ n, 0 < q_rec n := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ q_rec ] ;
        exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( ih _ ( by linarith ) ) ) ) ( ih _ ( by linarith ) );
      exact_mod_cast ne_of_gt ( h_q_pos _ )

/-
The sequence of even convergents $p_{2n}/q_{2n}$ is strictly increasing.
-/
theorem lem_even_convergents_increasing (n : ℕ) :
  (p_rec (2 * n) : ℝ) / q_rec (2 * n) < (p_rec (2 * n + 2) : ℝ) / q_rec (2 * n + 2) := by
    rw [ div_lt_div_iff₀ ];
    · -- By the determinant formula, we have $p_{n+2} q_n - p_n q_{n+2} = a_{n+2} (-1)^n$.
      have h_det : p_rec (2 * n + 2) * q_rec (2 * n) - p_rec (2 * n) * q_rec (2 * n + 2) = (e_coeff (2 * n + 2) : ℝ) * (-1) ^ (2 * n) := by
        convert lem_det_rec ( 2 * n ) using 1 ; ring_nf;
        norm_num [ add_comm 1, add_comm 2, p_rec, q_rec ];
        norm_cast ; ring_nf;
        constructor <;> intro h <;> nlinarith [ show 0 < e_coeff ( 2 + n * 2 ) from Nat.pos_of_ne_zero ( by unfold e_coeff; aesop ) ];
      norm_num [ e_coeff ] at *;
      split_ifs at h_det <;> linarith;
    · -- By definition of $q_rec$, we know that $q_rec (2 * n)$ is positive for all $n$.
      have h_q_pos : ∀ n, 0 < (q_rec n : ℝ) := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ q_rec ] ;
        exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( ih _ ( by linarith ) ) ) ) ( ih _ ( by linarith ) );
      exact h_q_pos _;
    · -- By definition of $q_rec$, we know that $q_rec (2 * n + 2)$ is positive.
      have hq_pos : ∀ n, 0 < q_rec n := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ *, Nat.add_mod, Nat.mul_mod ] ;
        · exact zero_lt_one;
        · exact Int.sign_eq_one_iff_pos.mp rfl;
        · exact add_pos ( mul_pos ( Nat.cast_pos.mpr ( show 0 < e_coeff ( n + 2 ) from by { unfold e_coeff; split_ifs <;> omega } ) ) ( ih _ <| Nat.lt_succ_self _ ) ) ( ih _ <| Nat.lt_succ_of_lt <| Nat.lt_succ_self _ )
      exact_mod_cast hq_pos (2 * n + 2)

/-
The sequence of odd convergents $p_{2n+1}/q_{2n+1}$ is strictly decreasing.
-/
theorem lem_odd_convergents_decreasing (n : ℕ) :
  (p_rec (2 * n + 3) : ℝ) / q_rec (2 * n + 3) < (p_rec (2 * n + 1) : ℝ) / q_rec (2 * n + 1) := by
    -- Using the determinant formula, we can express the difference between consecutive convergents.
    have h_diff : p_rec (2 * n + 3) * q_rec (2 * n + 1) - p_rec (2 * n + 1) * q_rec (2 * n + 3) = - (e_coeff (2 * n + 3) : ℝ) := by
      convert lem_det_rec ( 2 * n + 1 ) using 1 ; ring_nf;
      rw [ show 3 + n * 2 = 2 + n * 2 + 1 by ring, show 2 + n * 2 = 1 + n * 2 + 1 by ring ] ; norm_cast ; ring_nf;
      rw [ show 3 + n * 2 = 2 + n * 2 + 1 by ring, show 2 + n * 2 = 1 + n * 2 + 1 by ring ] ; norm_num [ pow_succ, Int.negSucc_eq, p_rec, q_rec ] ; ring_nf;
      constructor <;> intro h <;> nlinarith [ show ( e_coeff ( 3 + n * 2 ) : ℤ ) > 0 from mod_cast Nat.pos_of_ne_zero ( by unfold e_coeff; aesop ) ];
    rw [ div_lt_div_iff₀ ] <;> norm_cast at *;
    · linarith [ show ( e_coeff ( 2 * n + 3 ) : ℤ ) > 0 by exact_mod_cast Nat.pos_of_ne_zero ( by unfold e_coeff; aesop ) ];
    · -- By definition of $q_rec$, we know that $q_rec (2 * n + 3)$ is positive.
      have h_q_pos : ∀ n, 0 < q_rec n := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ q_rec ] ;
        exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( ih _ ( by linarith ) ) ) ) ( ih _ ( by linarith ) )
      exact h_q_pos (2 * n + 3);
    · -- By definition of $q_rec$, we know that $q_rec (2 * n + 1)$ is positive.
      have h_q_pos : ∀ n, 0 < q_rec n := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ q_rec ] ;
        exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( ih _ ( by linarith ) ) ) ) ( ih _ ( by linarith ) )
      exact h_q_pos (2 * n + 1)

/-
The even convergents are strictly less than the odd convergents.
-/
theorem lem_even_lt_odd (n : ℕ) :
  (p_rec (2 * n) : ℝ) / q_rec (2 * n) < (p_rec (2 * n + 1) : ℝ) / q_rec (2 * n + 1) := by
    -- By the properties of the convergents, we know that $p_{2n+1} q_{2n} - p_{2n} q_{2n+1} = 1$.
    have h_det : (p_rec (2 * n + 1) : ℝ) * (q_rec (2 * n) : ℝ) - (p_rec (2 * n) : ℝ) * (q_rec (2 * n + 1) : ℝ) = 1 := by
      convert lem_det_rec ( 2 * n ) using 1 ; ring_nf;
      norm_num [ pow_mul' ] ; norm_cast;
    rw [ div_lt_div_iff₀ ];
    · linarith;
    · -- By definition of $q_rec$, we know that $q_rec (2 * n)$ is positive for all $n$.
      have h_q_pos : ∀ n, 0 < q_rec n := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ q_rec ] ;
        exact add_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by unfold e_coeff; aesop ) ) ) ( ih _ ( by linarith ) ) ) ( ih _ ( by linarith ) );
      exact_mod_cast h_q_pos _;
    · norm_cast;
      -- By definition of $q_rec$, we know that $q_rec (2 * n + 1)$ is positive.
      have h_q_pos : ∀ n, 0 < q_rec n := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ q_rec ] ;
        exact add_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by unfold e_coeff; aesop ) ) ) ( ih _ ( by linarith ) ) ) ( ih _ ( by linarith ) )
      exact h_q_pos (2 * n + 1)

/-
The recurrence relation for q_n holds.
-/
theorem lem_q_recurrence (n : ℕ) :
  (q_rec (n + 2) : ℝ) = (e_coeff (n + 2) : ℝ) * (q_rec (n + 1) : ℝ) + (q_rec n : ℝ) := by
    norm_cast

/-
The sequence of denominators q_n is non-decreasing.
-/
theorem lem_q_growth (n : ℕ) : q_rec n ≤ q_rec (n + 1) := by
  -- We proceed by induction on $n$.
  induction' n with n ih;
  · exact Int.le_refl (q_rec 0);
  · -- By definition of $q_rec$, we have $q_rec (n + 2) = e_coeff (n + 2) * q_rec (n + 1) + q_rec n$.
    have h_q_rec_succ : q_rec (n + 2) = (e_coeff (n + 2) : ℤ) * q_rec (n + 1) + q_rec n := by
      rfl;
    -- Since $q_rec n$ is non-negative, we have $q_rec (n + 1) \leq q_rec (n + 1) + q_rec n$.
    have h_nonneg : 0 ≤ q_rec n := by
      -- By definition of $q_rec$, we know that $q_rec n$ is non-negative for all $n$.
      have h_q_rec_nonneg : ∀ n, 0 ≤ q_rec n := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> norm_num [ q_rec ] ;
        exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( ih _ ( Nat.lt_succ_self _ ) ) ) ( ih _ ( Nat.lt_succ_of_lt ( Nat.lt_succ_self _ ) ) );
      exact h_q_rec_nonneg n;
    exact h_q_rec_succ.symm ▸ le_add_of_le_of_nonneg ( le_mul_of_one_le_left ( by linarith ) ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by unfold e_coeff; aesop ) ) h_nonneg

/-
The ratio q_{n+1}/q_n is between a_{n+1} and a_{n+1}+1.
-/
theorem lem_q_ratio (n : ℕ) (h : n ≥ 1) :
  (e_coeff (n + 1) : ℝ) ≤ (q_rec (n + 1) : ℝ) / q_rec n ∧
  (q_rec (n + 1) : ℝ) / q_rec n ≤ (e_coeff (n + 1) : ℝ) + 1 := by
    have := @lem_q_ratio_bounds;
    exact ⟨ le_of_lt ( this n h |>.1 ), this n h |>.2 ⟩

/-
For $k \ge 1$, $2k+2 < q_{3k+2}/q_{3k+1} < 2k+3$.
-/
theorem lem_q_ratio_bounds_explicit (k : ℕ) (hk : k ≥ 1) :
  2 * (k : ℝ) + 2 < (q_rec (3 * k + 2) : ℝ) / q_rec (3 * k + 1) ∧
  (q_rec (3 * k + 2) : ℝ) / q_rec (3 * k + 1) < 2 * (k : ℝ) + 3 := by
    -- Substitute the recurrence relation into the ratio.
    have h_sub : (q_rec (3 * k + 2) : ℝ) = 2 * (k + 1) * (q_rec (3 * k + 1) : ℝ) + (q_rec (3 * k) : ℝ) := by
      convert lem_q_recurrence ( 3 * k ) using 1 ; ring_nf;
      unfold e_coeff; norm_num; ring_nf;
      norm_num [ Nat.add_div ] ; ring;
    -- Since $k \ge 1$, we have $q_{3k} > 0$ and $q_{3k} < q_{3k+1}$ (strictly increasing denominators).
    have h_pos : (q_rec (3 * k) : ℝ) > 0 ∧ (q_rec (3 * k) : ℝ) < (q_rec (3 * k + 1) : ℝ) := by
      induction hk <;> simp_all +decide [ Nat.mul_succ, q_rec ];
      · norm_cast;
      · rename_i k hk ih; specialize ih; unfold e_coeff at *; simp_all +decide [Nat.add_mod] ;
        norm_cast at * ; simp_all +decide [ Nat.add_div ];
        exact ⟨ by norm_cast; nlinarith, by norm_cast; nlinarith ⟩;
    exact ⟨ by rw [ lt_div_iff₀ ] <;> nlinarith, by rw [ div_lt_iff₀ ] <;> nlinarith ⟩

/-
tail 0 is e.
-/
noncomputable def tail (n : ℕ) : ℝ :=
  if n = 0 then Real.exp 1
  else
    let pn := p_rec (n - 1)
    let qn := q_rec (n - 1)
    let qn_prev := if n = 1 then 0 else q_rec (n - 2)
    (1 : ℝ) / (qn ^ 2 * |Real.exp 1 - pn / qn|) - qn_prev / qn

theorem tail_zero : tail 0 = Real.exp 1 := by
  unfold tail; norm_num [ Real.exp_ne_zero ] ;

/-
Definition of r_rec using the recursive definitions of p and q.
-/
noncomputable def r_rec (k : ℕ) : ℝ :=
  (q_rec (3 * k + 1) : ℝ) ^ 2 * |Real.exp 1 - (p_rec (3 * k + 1) : ℝ) / q_rec (3 * k + 1)|

/-
The coefficient $a_n$ in the continued fraction of $e$ is always at least 1.
-/
noncomputable def tail_val (n : ℕ) : ℝ :=
  if n = 0 then Real.exp 1
  else 1 / (tail_val (n - 1) - (e_coeff (n - 1) : ℝ))

theorem lem_e_coeff_ge_one (n : ℕ) : e_coeff n ≥ 1 := by
  unfold e_coeff; split_ifs <;> norm_num;
  linarith [ Nat.zero_le ( n / 3 ) ]

/-
Definition of y* = sinh(1)/12.
-/
noncomputable def y_star : ℝ := Real.sinh 1 / 12

/-
Definition of m depending on k and d.
-/
noncomputable def m_sc (k d : ℕ) : ℤ := (d * p_seq (3 * k + 1) - 1) / 2

/-
Definition of n depending on k and d.
-/
noncomputable def n_sc (k d : ℕ) : ℤ := (d * q_seq (3 * k + 1) + 1) / 2

/-
Definition of y depending on k and d (inlined to avoid syntax errors).
-/
noncomputable def y_sc (k d : ℕ) : ℝ :=
  -1/2 * ((-1 : ℝ)^(k + 1)) * r_seq k * (d : ℝ)^2 * ((n_sc k d : ℝ) / (2 * (n_sc k d : ℝ) - 1))

/-
The continued fraction of e is not terminated at any n.
-/
theorem lem_exp_not_terminated (n : ℕ) : ¬ (GenContFract.of (Real.exp 1)).TerminatedAt n := by
  by_contra h_terminated;
  -- If the continued fraction of e were terminated at n, then e would be rational.
  have h_rational : ∃ q : ℚ, Real.exp 1 = q := by
    have h_rational : ∃ q : ℚ, (GenContFract.of (Real.exp 1)).convs n = q := by
      exact GenContFract.exists_rat_eq_nth_conv (rexp 1) n;
    have h_rational : (GenContFract.of (Real.exp 1)).convs n = Real.exp 1 := by
      exact Eq.symm (GenContFract.of_correctness_of_terminatedAt h_terminated);
    aesop;
  have h_exp_not_rational : ¬ ∃ q : ℚ, Real.exp 1 = q := by
    intro h
    obtain ⟨ q, hq ⟩ := h
    have h_contra : ∃ p k : ℕ, p > 0 ∧ k > 0 ∧ q = p / k := by
      exact ⟨ q.num.natAbs, q.den, by simpa using ne_of_gt ( Rat.num_pos.mpr ( show 0 < q from by exact_mod_cast hq ▸ Real.exp_pos _ ) ), Nat.cast_pos.mpr q.pos, by simpa [ abs_of_nonneg ( Rat.num_nonneg.mpr ( show 0 ≤ q from by exact_mod_cast hq ▸ Real.exp_nonneg _ ) ) ] using q.num_div_den.symm ⟩
    -- If $e$ were rational, then $e = \frac{p}{k}$ for some positive integers $p$ and $k$.
    obtain ⟨ p, k, hp_pos, hk_pos, hpk ⟩ := h_contra
    have h_expansion : Real.exp 1 * k ! = ∑ i ∈ Finset.range (k + 1), (k ! : ℝ) / (i ! : ℝ) + ∑' i : ℕ, (k ! : ℝ) / ((k + 1 + i)! : ℝ) := by
      have h_expansion : Real.exp 1 * k ! = ∑' i : ℕ, (k ! : ℝ) / (i ! : ℝ) := by
        norm_num [ div_eq_mul_inv, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ];
        rw [ ← tsum_mul_right ] ; exact tsum_congr fun _ => by ring;
      rw [ h_expansion, ← Summable.sum_add_tsum_nat_add ];
      congr! 2;
      · ac_rfl;
      · exact Summable.mul_left _ <| by simpa using Real.summable_pow_div_factorial 1;
    -- The second sum is strictly between 0 and 1, hence it cannot be an integer.
    have h_second_sum_bounds : 0 < ∑' i : ℕ, (k ! : ℝ) / ((k + 1 + i)! : ℝ) ∧ ∑' i : ℕ, (k ! : ℝ) / ((k + 1 + i)! : ℝ) < 1 := by
      constructor;
      · refine' Summable.tsum_pos ..;
        exacts [ Summable.mul_left _ <| by simpa [ add_comm, add_left_comm, add_assoc ] using summable_nat_add_iff ( k + 1 ) |>.2 <| Real.summable_pow_div_factorial 1, fun _ => by positivity, 0, by positivity ];
      · -- We'll use that the series $\sum_{i=0}^{\infty} \frac{k!}{(k+1+i)!}$ is a geometric series with the first term $\frac{k!}{(k+1)!} = \frac{1}{k+1}$ and common ratio $\frac{1}{k+2}$.
        have h_geo_series : ∑' i : ℕ, (k ! : ℝ) / ((k + 1 + i)! : ℝ) ≤ ∑' i : ℕ, (1 / (k + 1) : ℝ) * (1 / (k + 2)) ^ i := by
          refine' Summable.tsum_le_tsum _ _ _;
          · field_simp;
            intro i; rw [ mul_comm ] ; induction i <;> simp_all +decide [ Nat.factorial, pow_succ' ];
            field_simp at *;
            nlinarith [ ( by positivity : 0 < ( k + 1 : ℝ ) * k ! * ( k + 2 ) ^ ‹_› ) ];
          · exact Summable.mul_left _ <| by simpa using Summable.comp_injective ( Real.summable_pow_div_factorial 1 ) <| by intros a b; aesop;
          · exact Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by rw [ div_lt_iff₀ ] <;> linarith;
        refine lt_of_le_of_lt h_geo_series ?_;
        rw [ tsum_mul_left, tsum_geometric_of_lt_one ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> linarith ) ];
        field_simp;
        rw [ div_lt_iff₀ ] <;> nlinarith only [ show ( k : ℝ ) ≥ 1 by norm_cast ];
    -- Since $e * k!$ is an integer, the second sum must also be an integer.
    have h_second_sum_integer : ∃ m : ℤ, ∑' i : ℕ, (k ! : ℝ) / ((k + 1 + i)! : ℝ) = m := by
      have h_second_sum_integer : ∃ m : ℤ, Real.exp 1 * k ! = m := by
        use p * (k - 1)!;
        cases k <;> simp_all +decide [ Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
        rw [ ← h_expansion ] ; simp +decide [Nat.cast_add_one_ne_zero];
      obtain ⟨ m, hm ⟩ := h_second_sum_integer;
      use m - ∑ i ∈ Finset.range (k + 1), (k ! : ℤ) / (i ! : ℤ);
      simp +decide [ ← hm, h_expansion ];
      rw [ Finset.sum_congr rfl fun i hi => Int.cast_div ( by exact_mod_cast Nat.factorial_dvd_factorial <| by linarith [ Finset.mem_range.mp hi ] ) ( by positivity ) ] ; norm_num;
    obtain ⟨ m, hm ⟩ := h_second_sum_integer; rcases m with ⟨ _ | _ | m ⟩ <;> norm_num at hm <;> linarith;
  exact h_exp_not_rational h_rational

/-
p_seq n and q_seq n are coprime.
-/
theorem lem_coprime_pq (n : ℕ) : Nat.Coprime (Int.natAbs (p_seq n)) (q_seq n) := by
  have hpq : ∀ n, Int.gcd (p_seq n) (q_seq n) = 1 := by
    intro n
    unfold p_seq q_seq
    exact Rat.reduced _;
  exact hpq n

/-
p_rec n and q_rec n are coprime.
-/
theorem lem_coprime_rec (n : ℕ) : Nat.Coprime (Int.natAbs (p_rec n)) (Int.natAbs (q_rec n)) := by
  -- By definition of $p_rec$ and $q_rec$, we know that $p_{n+1} q_n - p_n q_{n+1} = (-1)^n$.
  have h_det : p_rec (n + 1) * q_rec n - p_rec n * q_rec (n + 1) = (-1 : ℤ) ^ n := by
    exact lem_det_rec n;
  refine' Nat.coprime_of_dvd' _;
  intro k hk hk₁ hk₂; replace h_det := congr_arg ( ( ↑ ) : ℤ → ZMod k ) h_det; simp_all +decide [ ← ZMod.natCast_eq_zero_iff ] ;
  cases' Nat.even_or_odd n with h h <;> simp_all +decide [ZMod.intCast_zmod_eq_zero_iff_dvd];
  · haveI := Fact.mk hk; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
  · simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ]

/-
q_rec n is positive for all n.
-/
theorem lem_q_rec_pos (n : ℕ) : q_rec n > 0 := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | n ) <;> norm_num [ * ];
  · exact zero_lt_one;
  · exact Int.sign_eq_one_iff_pos.mp rfl;
  · exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( ih _ ( Nat.lt_succ_self _ ) ) ) ) ( ih _ ( Nat.lt_succ_of_lt ( Nat.lt_succ_self _ ) ) )

/-
For any positive A and T, there exists an odd integer d such that A*d^2 is close to T.
-/
theorem lem_quadratic_approx (A T : ℝ) (hA : A > 0) (hT : T > 0) :
  ∃ d : ℤ, Odd d ∧ |A * d^2 - T| ≤ 3 * Real.sqrt (A * T) + 3 * A := by
    -- Let $x = \sqrt{T/A}$. Let $d$ be the odd integer closest to $x$. Then $|d-x| \le 1$.
    set x := Real.sqrt (T / A)
    obtain ⟨d, hd⟩ : ∃ d : ℤ, Odd d ∧ |(d : ℝ) - x| ≤ 1 := by
      exact exists_odd_near x;
    -- We have $|A d^2 - T| = A |d^2 - x^2| = A |d-x|(d+x) \le A(1)(2x+1) = 2\sqrt{AT} + A$.
    have h_bound : |A * (d : ℝ) ^ 2 - T| ≤ A * (1) * (2 * x + 1) := by
      have h_bound : |A * (d : ℝ) ^ 2 - T| = A * |(d : ℝ) - x| * |(d : ℝ) + x| := by
        rw [ show A * ( d : ℝ ) ^ 2 - T = A * ( ( d : ℝ ) - x ) * ( ( d : ℝ ) + x ) by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ T / A by positivity ), mul_div_cancel₀ T hA.ne' ] ] ; rw [ abs_mul, abs_mul, abs_of_pos hA ];
      exact h_bound.symm ▸ mul_le_mul ( mul_le_mul_of_nonneg_left hd.2 hA.le ) ( by cases abs_cases ( ( d : ℝ ) + x ) <;> cases abs_cases ( ( d : ℝ ) - x ) <;> linarith [ Real.sqrt_nonneg ( T / A ) ] ) ( by positivity ) ( by positivity );
    refine' ⟨ d, hd.1, h_bound.trans _ ⟩;
    rw [ show A * T = A ^ 2 * ( T / A ) by nlinarith [ mul_div_cancel₀ T hA.ne' ], Real.sqrt_mul ( by positivity ), Real.sqrt_sq hA.le ] ; nlinarith [ Real.sqrt_nonneg ( T / A ), Real.mul_self_sqrt ( show 0 ≤ T / A by positivity ), mul_div_cancel₀ T hA.ne' ]

/-
If d is odd, the ratio n/(2n-1) is very close to 1/2, with error at most 1/(2d).
-/
theorem lem_n_ratio_approx_odd (k d : ℕ) (hk : k ≥ 1) (hd : Odd d) :
  let n := n_sc k d
  |(n : ℝ) / (2 * n - 1) - 1 / 2| ≤ 1 / (2 * (d : ℝ)) := by
    obtain ⟨ m, rfl ⟩ := hd;
    rw [ abs_le ] ; constructor <;> norm_num [ n_sc ];
    · field_simp;
      rw [ div_add_one, le_div_iff₀ ] <;> norm_cast <;> norm_num [ Nat.add_mod, Nat.mul_mod, Nat.add_div ];
      · rcases Nat.even_or_odd' ( q_seq ( 3 * k + 1 ) ) with ⟨ c, d | d ⟩ <;> push_cast [ d ] <;> ring_nf <;> norm_num [ Int.subNatNat_eq_coe ] at *;
        · grind;
        · grind;
      · rw [ Int.subNatNat_eq_coe ] ; norm_num ; ring_nf;
        -- Since $q_{3k+1}$ is always positive and odd, we have $q_{3k+1} \geq 1$.
        have h_q_pos : 1 ≤ q_seq (1 + k * 3) := by
          exact Nat.pos_of_ne_zero ( by erw [ show q_seq ( 1 + k * 3 ) = ( Real.convergent ( Real.exp 1 ) ( 1 + k * 3 ) |> Rat.den ) from rfl ] ; exact Nat.ne_of_gt ( Rat.pos _ ) );
        grind;
    · rw [ inv_mul_eq_div, div_add_div, div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod, Nat.add_mod ];
      · rcases Nat.even_or_odd' ( q_seq ( 3 * k + 1 ) ) with ⟨ c, d | d ⟩ <;> push_cast [ * ] <;> ring_nf <;> norm_num;
        · unfold q_seq at d; simp_all +decide [ parity_simps ] ;
          split_ifs at d <;> norm_cast at * ; simp_all +decide [ parity_simps ];
          · cases c <;> cases d;
          · norm_num [ show m * c * 4 + c * 2 = 2 * ( m * c * 2 + c ) by ring, Nat.add_div ] ; ring_nf;
            rcases c with ( _ | _ | c ) <;> norm_num at *;
            · (expose_names; exact False.elim (h d));
            · nlinarith;
            · nlinarith;
        · norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod, Nat.add_mod ] ; nlinarith;
      · rw [ Int.subNatNat_eq_coe ] ; norm_num ; ring_nf;
        -- Since $q_{3k+1}$ is always positive and odd, we have $q_{3k+1} \geq 1$.
        have h_q_pos : 1 ≤ q_seq (1 + k * 3) := by
          exact Nat.pos_of_ne_zero ( by erw [ show q_seq ( 1 + k * 3 ) = ( Real.convergent ( Real.exp 1 ) ( 1 + k * 3 ) |> Rat.den ) from rfl ] ; exact Nat.ne_of_gt ( Rat.pos _ ) );
        grind

/-
The ratio $q_{3k+2}/q_{3k+1}$ is strictly between $2k+2$ and $2k+3$.
-/
theorem lem_q_ratio_bounds_explicit_proven (k : ℕ) (hk : k ≥ 1) :
  2 * (k : ℝ) + 2 < (q_rec (3 * k + 2) : ℝ) / q_rec (3 * k + 1) ∧
  (q_rec (3 * k + 2) : ℝ) / q_rec (3 * k + 1) < 2 * (k : ℝ) + 3 := by
    convert lem_q_ratio_bounds_explicit k hk using 1

/-
There exists a constant C>0 such that for every integer n>=1, |f(n) - f(n+1) + 1/(n+1)| <= C/n^5.
-/
theorem lem_f_diff_bound_aux : ∃ C > 0, ∀ n : ℕ, n ≥ 1 → |f n - f (n + 1) + 1 / (n + 1)| ≤ C / n ^ 5 := by
  by_contra! h_contra;
  obtain ⟨ C, hC_pos, hC ⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → |f n - f (n - 1) - 1 / n| ≤ C / n ^ 5 := by
    exact lem_f_diff_bound;
  -- By substituting $n+1$ for $n$ in the hypothesis $hC$, we can derive the required inequality for $n \geq 1$.
  have h_subst : ∀ n : ℕ, n ≥ 1 → |f (n + 1) - f n - 1 / (n + 1)| ≤ C / (n + 1) ^ 5 := by
    exact fun n hn => mod_cast hC _ ( Nat.succ_le_succ hn );
  obtain ⟨ n, hn₁, hn₂ ⟩ := h_contra C hC_pos;
  exact hn₂.not_ge ( le_trans ( by rw [ abs_sub_comm ] ; ring_nf at *; linarith ) ( h_subst n hn₁ ) |> le_trans <| by gcongr ; norm_num )

/-
The sequence H_n - f(n) tends to 0 as n goes to infinity.
-/
theorem lem_diff_tendsto_zero : Filter.Tendsto (fun n => H n - f n) Filter.atTop (nhds 0) := by
  -- We'll use the fact that the difference between the harmonic series and the natural logarithm converges to the Euler-Mascheroni constant.
  have h_harmonic_log : Filter.Tendsto (fun n => H n - Real.log n) Filter.atTop (nhds (Real.eulerMascheroniConstant)) := by
    convert Real.tendsto_harmonic_sub_log using 1;
  convert h_harmonic_log.sub ( show Filter.Tendsto ( fun n : ℕ => f n - Real.log n ) Filter.atTop ( nhds ( Real.eulerMascheroniConstant ) ) from ?_ ) using 2 <;> norm_num [ f ] ; ring_nf!;
  simpa using Filter.Tendsto.add ( tendsto_const_nhds.add ( tendsto_inverse_atTop_nhds_zero_nat.mul tendsto_const_nhds ) ) ( tendsto_inverse_atTop_nhds_zero_nat.pow 2 |> Filter.Tendsto.mul_const _ )

/-
There exists a constant C>0 such that for every integer n>=1, |H_n - f(n)| <= C/n^4.
-/
theorem lem_EM : ∃ C > 0, ∀ n : ℕ, n ≥ 1 → |H n - f n| ≤ C / n ^ 4 := by
  -- By combining the results from `lem_f_diff_bound_aux` and `lem_diff_tendsto_zero`, we can show that $|H_n - f(n)| \leq C/n^4$ for some constant $C$.
  obtain ⟨C, hC_pos, hC_bound⟩ : ∃ C > 0, ∀ n ≥ 1, |(H n - f n) - (H (n + 1) - f (n + 1))| ≤ C / n ^ 5 := by
    obtain ⟨ C, hC_pos, hC_bound ⟩ := lem_f_diff_bound_aux;
    use C, hC_pos;
    intro n hn; specialize hC_bound n hn; simp_all +decide [ abs_le, H ] ;
    constructor <;> linarith [ show ( harmonic n : ℝ ) = ∑ k ∈ Finset.range n, ( 1 / ( k + 1 : ℝ ) ) by exact mod_cast by simp +decide [ harmonic ] ] ;
  -- By induction, we can show that $|H_n - f(n)| \leq \sum_{k=n}^\infty |(H_k - f(k)) - (H_{k+1} - f(k+1))|$.
  have h_induction : ∀ n ≥ 1, |H n - f n| ≤ ∑' k : ℕ, C / (n + k) ^ 5 := by
    intro n hn
    have h_sum : |H n - f n| ≤ ∑' k : ℕ, |(H (n + k) - f (n + k)) - (H (n + k + 1) - f (n + k + 1))| := by
      have h_sum : Filter.Tendsto (fun m => ∑ k ∈ Finset.range m, (H (n + k) - f (n + k) - (H (n + k + 1) - f (n + k + 1)))) Filter.atTop (nhds (H n - f n)) := by
        have h_telescope : ∀ m : ℕ, ∑ k ∈ Finset.range m, ((H (n + k) - f (n + k)) - (H (n + k + 1) - f (n + k + 1))) = (H n - f n) - (H (n + m) - f (n + m)) := by
          exact fun m => by induction m <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
        rw [ Filter.tendsto_congr h_telescope ] ; simpa using tendsto_const_nhds.sub ( lem_diff_tendsto_zero.comp ( Filter.tendsto_atTop_mono ( fun m => by simp +arith +decide ) tendsto_natCast_atTop_atTop ) ) ;
      have h_sum_abs : Summable (fun k : ℕ => |(H (n + k) - f (n + k)) - (H (n + k + 1) - f (n + k + 1))|) := by
        have h_sum_abs : Summable (fun k : ℕ => C / (n + k : ℝ) ^ 5) := by
          exact Summable.mul_left _ <| by exact_mod_cast Summable.comp_injective ( Real.summable_nat_pow_inv.2 <| by norm_num ) <| by intros a b; aesop;
        exact Summable.of_nonneg_of_le ( fun k => abs_nonneg _ ) ( fun k => by simpa using hC_bound ( n + k ) ( by linarith ) ) h_sum_abs;
      exact le_of_tendsto' ( Filter.Tendsto.abs h_sum ) fun m => by simpa using Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Summable.sum_le_tsum ( Finset.range m ) ( fun _ _ => abs_nonneg _ ) h_sum_abs;
    refine' le_trans h_sum ( Summable.tsum_le_tsum _ _ _ );
    · exact fun k => mod_cast hC_bound _ ( by linarith );
    · refine' Summable.of_nonneg_of_le ( fun k => abs_nonneg _ ) ( fun k => hC_bound ( n + k ) ( by linarith ) ) _;
      exact Summable.mul_left _ <| by exact_mod_cast Summable.comp_injective ( Real.summable_nat_pow_inv.2 <| by norm_num ) <| by intros a b; aesop;
    · exact Summable.mul_left _ <| by exact_mod_cast Summable.comp_injective ( Real.summable_nat_pow_inv.2 <| by norm_num ) <| by intros a b; aesop;
  -- We can bound the sum $\sum_{k=n}^\infty \frac{C}{(n+k)^5}$ by comparing it to an integral.
  have h_integral_bound : ∀ n ≥ 1, ∑' k : ℕ, C / (n + k : ℝ) ^ 5 ≤ C / (n : ℝ) ^ 5 + C / 4 * (1 / (n : ℝ) ^ 4) := by
    intros n hn
    have h_integral_bound_step : ∀ k ≥ 1, C / (n + k : ℝ) ^ 5 ≤ C / 4 * (1 / (n + k - 1 : ℝ) ^ 4 - 1 / (n + k : ℝ) ^ 4) := by
      intro k hk; rw [ div_sub_div, div_mul_div_comm, div_le_div_iff₀ ] <;> try positivity;
      · nlinarith [ show 0 < C * ( n + k ) ^ 4 by positivity, show 0 < C * ( n + k ) ^ 5 by positivity, show 0 < C * ( n + k - 1 ) ^ 4 by exact mul_pos hC_pos ( pow_pos ( by linarith ) _ ), show 0 < C * ( n + k - 1 ) ^ 5 by exact mul_pos hC_pos ( pow_pos ( by linarith ) _ ), pow_two_nonneg ( ( n + k ) ^ 2 - ( n + k - 1 ) ^ 2 ) ];
      · exact mul_pos zero_lt_four ( mul_pos ( pow_pos ( by linarith ) 4 ) ( pow_pos ( by linarith ) 4 ) );
      · exact pow_ne_zero _ ( by linarith );
    -- Applying the integral bound step to each term in the sum, we get:
    have h_sum_integral_bound : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), C / (n + k : ℝ) ^ 5 ≤ C / n ^ 5 + C / 4 * (1 / n ^ 4 - 1 / (n + N : ℝ) ^ 4) := by
      intro N; induction' N with N ih <;> norm_num [ Finset.sum_range_succ ] at *;
      convert add_le_add ih ( h_integral_bound_step ( N + 1 ) ( by linarith ) ) using 1 ; ring;
    -- Taking the limit of the sum as $N$ approaches infinity, we get:
    have h_limit : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), C / (n + k : ℝ) ^ 5) Filter.atTop (nhds (∑' k : ℕ, C / (n + k : ℝ) ^ 5)) := by
      refine' ( Summable.hasSum _ ) |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1;
      have h_summable : Summable (fun k : ℕ => C / (k : ℝ) ^ 5) := by
        exact Summable.mul_left _ <| Real.summable_nat_pow_inv.2 <| by norm_num;
      rw [ ← summable_nat_add_iff 1 ] at *;
      exact Summable.of_nonneg_of_le ( fun _ => div_nonneg hC_pos.le <| pow_nonneg ( by positivity ) _ ) ( fun _ => div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) <| pow_le_pow_left₀ ( by positivity ) ( by linarith ) _ ) h_summable;
    exact le_of_tendsto_of_tendsto' h_limit tendsto_const_nhds fun N => le_trans ( h_sum_integral_bound N ) ( add_le_add_left ( mul_le_mul_of_nonneg_left ( sub_le_self _ <| by positivity ) <| by positivity ) _ );
  refine' ⟨ C + C / 4, by positivity, fun n hn => le_trans ( h_induction n <| mod_cast hn ) <| le_trans ( h_integral_bound n <| mod_cast hn ) _ ⟩ ; ring_nf ; norm_num [ hn ];
  nlinarith [ show 0 < C * ( n ^ 4 : ℝ ) ⁻¹ by positivity, show 0 < C * ( n ^ 5 : ℝ ) ⁻¹ by positivity, show ( n ^ 4 : ℝ ) ⁻¹ ≥ ( n ^ 5 : ℝ ) ⁻¹ by gcongr <;> norm_cast ]

/-
The number $e$ can be expressed in terms of the $(n+1)$-th tail of its continued fraction and the $n$-th and $(n-1)$-th convergents.
-/
theorem lem_exp_eq_tail_formula (n : ℕ) (h : n ≥ 1) :
  Real.exp 1 = ((tail_val (n + 1) : ℝ) * (p_rec n : ℝ) + (p_rec (n - 1) : ℝ)) /
               ((tail_val (n + 1) : ℝ) * (q_rec n : ℝ) + (q_rec (n - 1) : ℝ)) := by
                 -- By definition of `tail_val`, we know that `tail_val (n + 1)` is the tail of the continued fraction expansion of `e` starting from the `(n + 1)`-th term.
                 have h_tail : ∀ n, tail_val (n + 1) = 1 / (tail_val n - (e_coeff n : ℝ)) := by
                   intro n
                   rw [tail_val];
                   rfl;
                 -- By definition of `tail_val`, we know that `tail_val 0 = e`.
                 have h_tail_zero : tail_val 0 = Real.exp 1 := by
                   unfold tail_val; norm_num;
                 induction h <;> simp_all +decide ; ring_nf;
                 · unfold e_coeff p_rec q_rec; norm_num [ h_tail_zero ] ; ring_nf;
                   -- Substitute A = (-2 + Real.exp 1)⁻¹ and simplify the expression.
                   set A : ℝ := (-2 + Real.exp 1)⁻¹
                   have hA : 1 + A > 0 := by
                     exact add_pos_of_pos_of_nonneg zero_lt_one ( inv_nonneg.mpr ( by have := Real.exp_one_gt_d9.le; norm_num1 at *; linarith ) )
                   field_simp [hA]
                   ring_nf;
                   by_cases h : -1 + A = 0 <;> simp_all +decide [ mul_comm];
                   · -- If $-1 + A = 0$, then $A = 1$, which implies $(-2 + \exp 1)^{-1} = 1$, leading to $\exp 1 = 3$, contradicting the known value of $\exp 1$.
                     have h_contra : Real.exp 1 = 3 := by
                       grind;
                     exact absurd h_contra <| by exact ne_of_lt <| Real.exp_one_lt_d9.trans_le <| by norm_num;
                   · field_simp [h];
                     rw [ eq_div_iff ] <;> cases lt_or_gt_of_ne h <;> nlinarith [ Real.add_one_le_exp 1, mul_inv_cancel₀ ( show -2 + Real.exp 1 ≠ 0 from by have := Real.exp_one_gt_d9.le; norm_num1 at *; linarith ) ];
                 · rename_i k hk₁ hk₂;
                   rw [ show p_rec ( k + 1 ) = ( e_coeff ( k + 1 ) : ℤ ) * p_rec k + p_rec ( k - 1 ) from ?_, show q_rec ( k + 1 ) = ( e_coeff ( k + 1 ) : ℤ ) * q_rec k + q_rec ( k - 1 ) from ?_ ];
                   · by_cases h : ( tail_val k - e_coeff k : ℝ ) ⁻¹ - e_coeff ( k + 1 ) = 0 <;> simp +decide [h] ; ring_nf;
                     · simp_all +decide [ sub_eq_iff_eq_add ];
                       -- Since $e$ is irrational, the equation $e = \frac{a}{b}$ cannot hold for any integers $a$ and $b$.
                       have h_irrational : Irrational (Real.exp 1) := by
                         by_contra h_contra;
                         -- If $e$ were rational, then $e = \frac{p}{q}$ for some coprime positive integers $p$ and $q$.
                         obtain ⟨p, q, h_coprime, h_eq⟩ : ∃ p q : ℕ, Nat.gcd p q = 1 ∧ Real.exp 1 = p / q := by
                           have := Classical.not_not.1 h_contra; rcases this with ⟨ q, hq ⟩ ; exact ⟨ q.num.natAbs, q.den, q.reduced, by simpa [ abs_of_nonneg ( Rat.num_nonneg.mpr ( show 0 ≤ q by exact_mod_cast hq.symm ▸ Real.exp_nonneg _ ) ), Rat.cast_def ] using hq.symm ⟩ ;
                         -- Multiply both sides of the equation by $q!$ to obtain a contradiction.
                         have h_factorial : ∑ k ∈ Finset.range (q + 1), (q ! / k ! : ℝ) + ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) = p * (q - 1)! := by
                           have h_factorial : ∑' k : ℕ, (q ! / k ! : ℝ) = p * (q - 1)! := by
                             have h_factorial : ∑' k : ℕ, (q ! / k ! : ℝ) = Real.exp 1 * q ! := by
                               norm_num [ div_eq_mul_inv, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ];
                               rw [ mul_comm, tsum_mul_left ];
                             rcases q <;> simp_all +decide [ Nat.factorial_succ, mul_comm, div_eq_mul_inv ];
                             rw [ ← hk₂ ] ; ring_nf;
                             -- Combine like terms and simplify the expression.
                             field_simp
                             ring;
                           rw [ ← h_factorial, ← Summable.sum_add_tsum_nat_add ];
                           rotate_left;
                           use 0;
                           · exact Summable.mul_left _ <| by simpa using summable_nat_add_iff ( q + 1 ) |>.2 <| Real.summable_pow_div_factorial 1;
                           · rw [ eq_comm, ← Summable.sum_add_tsum_nat_add ];
                             congr! 1;
                             · norm_num [ add_assoc ];
                             · exact Summable.mul_left _ <| by simpa using Real.summable_pow_div_factorial 1;
                         -- The first sum is an integer, and the second sum is a positive number less than 1.
                         have h_sum_bounds : ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) < 1 := by
                           -- We'll use that the series $\sum_{k=q+1}^{\infty} \frac{q!}{k!}$ is a geometric series with the first term $\frac{q!}{(q+1)!} = \frac{1}{q+1}$ and common ratio $\frac{1}{q+2}$.
                           have h_geo_series : ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) ≤ ∑' k : ℕ, (1 / (q + 1) : ℝ) * (1 / (q + 2)) ^ k := by
                             refine' Summable.tsum_le_tsum _ _ _;
                             · field_simp;
                               intro i; rw [ mul_comm ] ; induction i <;> simp_all +decide [ Nat.factorial, pow_succ' ];
                               norm_num [ Nat.succ_add, Nat.factorial_succ ] at *;
                               field_simp at *;
                               nlinarith [ sq ( q : ℝ ), show ( 0 : ℝ ) ≤ ( q + 1 ) * q ! * ( q + 2 ) ^ ‹_› by positivity ];
                             · exact Summable.mul_left _ <| by simpa using summable_nat_add_iff ( q + 1 ) |>.2 <| Real.summable_pow_div_factorial 1;
                             · exact Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by rw [ div_lt_iff₀ ] <;> linarith;
                           refine lt_of_le_of_lt h_geo_series ?_;
                           rw [ tsum_mul_left, tsum_geometric_of_lt_one ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> linarith ) ];
                           field_simp;
                           rw [ div_lt_iff₀ ] <;> nlinarith only [ show ( q : ℝ ) ≥ 1 by norm_cast; exact Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ];
                         -- The first sum is an integer, and the second sum is a positive number less than 1, leading to a contradiction.
                         have h_contradiction : ∃ m : ℤ, ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) = m := by
                           use p * (q - 1)! - ∑ k ∈ Finset.range (q + 1), (q ! / k ! : ℤ);
                           simp +decide [ ← h_factorial ];
                           rw [ Finset.sum_congr rfl fun i hi => Int.cast_div ( by exact_mod_cast Nat.factorial_dvd_factorial ( by linarith [ Finset.mem_range.mp hi ] ) ) ( by positivity ) ] ; norm_num;
                         obtain ⟨ m, hm ⟩ := h_contradiction; rcases m with ⟨ _ | _ | m ⟩ <;> norm_num at hm <;> try linarith;
                         · rw [ Summable.tsum_eq_zero_add ] at hm;
                           · exact ne_of_gt ( add_pos_of_pos_of_nonneg ( by positivity ) ( tsum_nonneg fun _ => by positivity ) ) hm;
                           · exact Summable.mul_left _ <| by simpa using summable_nat_add_iff ( q + 1 ) |>.2 <| Real.summable_pow_div_factorial 1;
                         · linarith [ show ( 0 : ℝ ) ≤ ∑' k : ℕ, ( q ! : ℝ ) / ( k + q + 1 ) ! from tsum_nonneg fun _ => by positivity ];
                       exact False.elim <| h_irrational ⟨ ( e_coeff ( k + 1 ) * p_rec k + p_rec ( k - 1 ) ) / ( e_coeff ( k + 1 ) * q_rec k + q_rec ( k - 1 ) ), by push_cast; linarith ⟩;
                     · field_simp [h];
                       ring;
                   · rcases k with ( _ | k ) <;> tauto;
                   · rcases k with ( _ | _ | k ) <;> tauto

/-
The difference $e - p_n/q_n$ is given by $(-1)^n / (q_n (\alpha_{n+1} q_n + q_{n-1}))$.
-/
theorem lem_exp_diff_formula (n : ℕ) (h : n ≥ 1) :
  Real.exp 1 - (p_rec n : ℝ) / q_rec n = (-1 : ℝ)^n / ((q_rec n : ℝ) * ((tail_val (n + 1) : ℝ) * q_rec n + q_rec (n - 1))) := by
    have := @lem_exp_eq_tail_formula n h;
    have h_det : p_rec n * q_rec (n - 1) - p_rec (n - 1) * q_rec n = (-1 : ℝ) ^ (n - 1) := by
      convert lem_det_rec ( n - 1 ) using 1 ; cases n <;> norm_num [ pow_succ' ] at *;
      norm_cast;
    rw [ this, div_sub_div ];
    · cases n <;> simp_all +decide [ pow_succ' ] ; ring_nf;
      rw [ ← h_det ] ; ring_nf;
    · intro h_zero
      have := this.symm
      field_simp [h_zero] at this;
      norm_num [ h_zero ] at this ; linarith [ Real.exp_pos 1 ];
    · exact_mod_cast ne_of_gt ( lem_q_rec_pos n )

/-
The value of the n-th tail of the continued fraction of e is irrational for all n.
-/
theorem lem_tail_irrational (n : ℕ) : Irrational (tail_val n) := by
  induction' n with n ih <;> unfold tail_val <;> norm_num at *;
  · by_contra h_contra
    obtain ⟨p, q, hq_pos, hpq_eq⟩ : ∃ p q : ℕ, q > 0 ∧ Real.exp 1 = p / q := by
      unfold Irrational at h_contra;
      -- Obtain such a q from h_contra.
      obtain ⟨q, hq⟩ : ∃ q : ℚ, Real.exp 1 = q := by
        grind;
      exact ⟨ q.num.natAbs, q.den, Nat.cast_pos.mpr q.pos, by simpa [ abs_of_nonneg ( Rat.num_nonneg.mpr ( show 0 ≤ q by exact_mod_cast hq ▸ Real.exp_nonneg _ ) ), Rat.cast_def ] using hq ⟩
    have h_factorial : ∑ k ∈ Finset.range (q + 1), (q ! / k ! : ℝ) + ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) = q ! * (p / q) := by
      have h_factorial : ∑' k : ℕ, (q ! / k ! : ℝ) = q ! * (p / q) := by
        rw [ ← hpq_eq, Real.exp_eq_exp_ℝ ];
        norm_num [ div_eq_mul_inv, tsum_mul_left, NormedSpace.exp_eq_tsum ];
      rw [ ← h_factorial, ← Summable.sum_add_tsum_nat_add ];
      case k => exact 0;
      · rw [ eq_comm, ← Summable.sum_add_tsum_nat_add ];
        congr! 1;
        · norm_num [ add_assoc ];
        · exact Summable.mul_left _ <| by simpa using Real.summable_pow_div_factorial 1;
      · exact Summable.mul_left _ <| by simpa using summable_nat_add_iff ( q + 1 ) |>.2 <| Real.summable_pow_div_factorial 1;
    have h_int : ∃ m : ℤ, ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) = m := by
      use q ! * p / q - ∑ k ∈ Finset.range (q + 1), (q ! / k ! : ℤ);
      rw [ Int.cast_sub, Int.cast_div ] <;> norm_num [ h_factorial ];
      · convert eq_sub_of_add_eq' h_factorial using 1 ; ring_nf;
        exact congrArg _ ( Finset.sum_congr rfl fun x hx => by rw [ Int.cast_div ( mod_cast Nat.factorial_dvd_factorial ( by linarith [ Finset.mem_range.mp hx ] ) ) ( by positivity ) ] ; push_cast; ring );
      · exact dvd_mul_of_dvd_left ( mod_cast Nat.dvd_factorial ( by positivity ) ( by linarith ) ) _;
      · linarith
    have h_sum_lt_one : ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) < 1 := by
      -- We'll use that the series $\sum_{k=q+1}^{\infty} \frac{q!}{k!}$ is a geometric series with the first term $\frac{q!}{(q+1)!} = \frac{1}{q+1}$ and common ratio $\frac{1}{q+2}$.
      have h_geo_series : ∑' k : ℕ, (q ! / (k + q + 1)! : ℝ) ≤ ∑' k : ℕ, (1 / (q + 1) : ℝ) * (1 / (q + 2)) ^ k := by
        refine' Summable.tsum_le_tsum _ _ _ <;> norm_num +zetaDelta at *;
        · intro i; rw [ ← mul_inv ] ; rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> first | positivity | induction' i with i ih <;> norm_num [ Nat.factorial, pow_succ' ] at * ; ring_nf at * ; nlinarith;
          rw [ Nat.succ_add ] ; nlinarith [ Nat.factorial_succ ( i + q ), pow_pos ( by linarith : 0 < q + 2 ) i ] ;
        · exact Summable.mul_left _ <| by simpa using summable_nat_add_iff ( q + 1 ) |>.2 <| Real.summable_pow_div_factorial 1;
        · exact Summable.mul_left _ <| by simpa using summable_geometric_of_lt_one ( by positivity ) <| inv_lt_one_of_one_lt₀ <| by linarith;
      refine lt_of_le_of_lt h_geo_series ?_ ; rw [ tsum_mul_left, tsum_geometric_of_lt_one ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) ] ; norm_num ; ring_nf ; (
      rw [ ← mul_inv, inv_lt_one₀ ] <;> nlinarith only [ show ( q : ℝ ) ≥ 1 by norm_cast, inv_mul_cancel₀ ( by positivity : ( 2 + q : ℝ ) ≠ 0 ) ] ;);
    have h_contra : ∃ m : ℤ, 0 < m ∧ m < 1 := by
      obtain ⟨m, hm⟩ := h_int
      have hm_pos : 0 < m := by
        exact_mod_cast hm ▸ show 0 < ∑' k : ℕ, ( q ! : ℝ ) / ( k + q + 1 ) ! from lt_of_lt_of_le ( by positivity ) ( Summable.le_tsum ( show Summable _ from by exact Summable.mul_left _ <| by simpa using summable_nat_add_iff ( q + 1 ) |>.2 <| Real.summable_pow_div_factorial 1 ) 0 <| fun _ _ => by positivity ) ;
      have hm_lt_one : m < 1 := by
        exact_mod_cast hm ▸ h_sum_lt_one
      exact ⟨m, hm_pos, hm_lt_one⟩
    exact h_contra.elim fun m hm => by linarith [hm.1, hm.2] ;
  · assumption

/-
Formula for tail_val (n+1) in terms of e and convergents.
-/
theorem lem_tail_val_formula (n : ℕ) (h : n ≥ 1) :
  tail_val (n + 1) = - (p_rec (n - 1) - Real.exp 1 * q_rec (n - 1)) / (p_rec n - Real.exp 1 * q_rec n) := by
    rw [ eq_div_iff ];
    · have := @lem_exp_eq_tail_formula n h;
      rw [ eq_div_iff ] at this <;> first | linarith | intro H ; norm_num [ H ] at this;
    · -- By definition of $p_rec$ and $q_rec$, we know that $p_rec n$ and $q_rec n$ are coprime integers.
      have h_coprime : Nat.Coprime (Int.natAbs (p_rec n)) (Int.natAbs (q_rec n)) := by
        exact lem_coprime_rec n;
      rw [ sub_ne_zero ];
      by_contra h_contra;
      -- Since $e$ is irrational, $p_n / q_n$ cannot equal $e$, leading to a contradiction.
      have h_irrational : Irrational (Real.exp 1) := by
        have := @lem_tail_irrational 0;
        unfold tail_val at this; aesop;
      exact h_irrational ⟨ p_rec n / q_rec n, by push_cast [ h_contra ] ; rw [ mul_div_cancel_right₀ _ ( by aesop ) ] ⟩

/-
For all $n$, `tail_val n = e_coeff n + 1 / tail_val (n+1)`.
-/
theorem lem_tail_val_recurrence (n : ℕ) :
  tail_val n = (e_coeff n : ℝ) + 1 / tail_val (n + 1) := by
    -- By definition of `tail_val`, we have `tail_val (n + 1) = 1 / (tail_val n - e_coeff n)`.
    have h_tail_def : tail_val (n + 1) = 1 / (tail_val n - e_coeff n) := by
      have h_tail_def : ∀ n, tail_val (n + 1) = 1 / (tail_val n - e_coeff n) := by
        intro n
        rw [tail_val];
        rfl;
      exact h_tail_def n;
    grind

/-
r_seq k is strictly positive for all k.
-/
theorem r_seq_pos (k : ℕ) : r_seq k > 0 := by
  refine' mul_pos _ ( sq_pos_of_pos _ );
  · -- Since $e$ is irrational, $e - p/q$ is never zero for any rational $p/q$.
    have h_irr : Irrational (Real.exp 1) := by
      have := @lem_tail_irrational 0;
      unfold tail_val at this; aesop;
    exact abs_pos.mpr ( sub_ne_zero.mpr <| by exact fun h => h_irr <| by use ( p_seq ( 3 * k + 1 ) : ℚ ) / q_seq ( 3 * k + 1 ) ; aesop );
  · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( Rat.den_nz _ ) )

/-
y_star is strictly positive.
-/
theorem y_star_pos : y_star > 0 := by
  exact div_pos ( Real.sinh_pos_iff.mpr zero_lt_one ) ( by norm_num )

/-
The ratio of denominators satisfies
\[ 0 < \frac{q_{3k}}{q_{3k+1}} < 1. \]
-/
theorem lem_q_ratio_bound_tight (k : ℕ) (hk : k ≥ 1) :
  0 < (q_rec (3 * k) : ℝ) / q_rec (3 * k + 1) ∧ (q_rec (3 * k) : ℝ) / q_rec (3 * k + 1) < 1 := by
    refine' ⟨ div_pos ( mod_cast _ ) ( mod_cast _ ), div_lt_one _ |>.2 _ ⟩ <;> norm_cast;
    · exact lem_q_rec_pos (3 * k);
    · exact lem_q_rec_pos (3 * k + 1);
    · exact lem_q_rec_pos (3 * k + 1);
    · induction k <;> simp_all +decide [ Nat.mul_succ, le_add_iff_nonneg_left ];
      rename_i k ih; rw [ show q_rec ( 3 * k + 4 ) = e_coeff ( 3 * k + 4 ) * q_rec ( 3 * k + 3 ) + q_rec ( 3 * k + 2 ) from rfl ] ; rw [ show q_rec ( 3 * k + 3 ) = e_coeff ( 3 * k + 3 ) * q_rec ( 3 * k + 2 ) + q_rec ( 3 * k + 1 ) from rfl ] ; simp +decide [ e_coeff ] ; ring_nf;
      exact lem_q_rec_pos _

/-
The difference between consecutive convergents is $(-1)^n / (q_n q_{n+1})$.
-/
theorem lem_signed_convergent_diff (n : ℕ) :
  (p_rec (n + 1) : ℝ) / q_rec (n + 1) - (p_rec n : ℝ) / q_rec n = (-1 : ℝ)^n / ((q_rec n : ℝ) * (q_rec (n + 1) : ℝ)) := by
    field_simp;
    rw [ div_sub_div, mul_comm ];
    · congr 1 ; norm_cast ; ring_nf;
      convert lem_det_rec n using 1 ; ring_nf;
    · exact_mod_cast ne_of_gt ( lem_q_rec_pos _ );
    · exact_mod_cast ne_of_gt ( lem_q_rec_pos n )

/-
If a sequence is strictly increasing and converges to L, then every element is strictly less than L.
-/
theorem lem_strict_mono_limit_lt {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  {f : ℕ → α} {L : α} (h_mono : StrictMono f) (h_lim : Filter.Tendsto f Filter.atTop (nhds L)) :
  ∀ n, f n < L := by
    intro m
    by_cases h_ge : ∃ n, f n ≥ L;
    · obtain ⟨ n, hn ⟩ := h_ge;
      have h_ge : ∀ m ≥ n + 1, f m ≥ f (n + 1) := by
        exact fun m hm => h_mono.monotone hm;
      have h_ge : L ≥ f (n + 1) := by
        exact le_of_tendsto_of_tendsto tendsto_const_nhds h_lim ( Filter.eventually_atTop.mpr ⟨ n + 1, h_ge ⟩ );
      exact absurd h_ge ( not_le_of_gt ( lt_of_le_of_lt hn ( h_mono ( Nat.lt_succ_self _ ) ) ) );
    · exact lt_of_not_ge fun h => h_ge ⟨ m, h ⟩

/-
The sequence of denominators q_n tends to infinity.
-/
theorem lem_q_tendsto_atTop : Filter.Tendsto (fun n => (q_rec n : ℝ)) Filter.atTop Filter.atTop := by
  have h_q_recurrence : ∀ n, q_rec (n + 2) ≥ q_rec (n + 1) + q_rec n := by
    -- By definition of $q_rec$, we have $q_rec (n + 2) = e_coeff (n + 2) * q_rec (n + 1) + q_rec n$.
    have h_q_recurrence : ∀ n, q_rec (n + 2) = e_coeff (n + 2) * q_rec (n + 1) + q_rec n := by
      exact fun n => rfl;
    intro n; rw [ h_q_recurrence ] ; nlinarith [ show ( e_coeff ( n + 2 ) : ℤ ) ≥ 1 from mod_cast lem_e_coeff_ge_one _, show ( q_rec ( n + 1 ) : ℤ ) ≥ 0 from mod_cast lem_q_rec_pos _ |> le_of_lt ] ;
  -- By induction, we can show that $q_n \geq F_n$ for all $n$, where $F_n$ is the $n$-th Fibonacci number.
  have h_fib_lower_bound : ∀ n, q_rec n ≥ Nat.fib n := by
    intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.fib_add_two ] ;
    linarith [ ih n ( by linarith ), ih ( n + 1 ) ( by linarith ), h_q_recurrence n ];
  refine' Filter.tendsto_atTop_mono ( fun n => Int.cast_le.mpr ( h_fib_lower_bound n ) ) _;
  exact tendsto_natCast_atTop_atTop.comp ( Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x + 2, fun n hn => by linarith [ Nat.le_fib_add_one n ] ⟩ )
