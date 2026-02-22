/-
Note that this project is not quite finished yet. It will soon!

We say that a sequence of positive integers $A$ has:

- property $P$ if, for all positive integers $n$, there are only finitely many $a \in A$ such that $n+a$ is squarefree.
- property $Q$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$ with $a < n$.
- property $\overline{P}$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$.
- property $\overline{P}_\infty$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all but finitely many $a \in A$.

Solving Erdős Problem #1102 (https://www.erdosproblems.com/1102), Terence Tao and I managed to prove tight bounds on the possible densities of sequences with one of the above properties.

W. van Doorn and T. Tao, Growth rates of sequences governed by the squarefree properties of their translates. arXiv:2512.01087 (2025).

Define a sequence to be admissible if if avoids at least one residue class modulo $p^2$ for every prime $p$. Thanks to Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), the proof of the following theorem is formalized in the Lean file below:

There exists an absolute constant $C$ such that any admissible sequence $A = \{a_1 < a_2 < \cdots \}$ for which $a_j \ge \exp(C j/\log j)$ holds for infinitely many $j$, has property $Q$. In particular, the specific sequences $2^n \pm 1$ and $n! \pm 1$ all have property $Q$. 

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
The statement of the asymptotic bound for the product of p^2 for p <= x.
-/
def Bound_prod_primes_le_x_sq : Prop :=
  (fun (x : ℝ) => Real.log (∏ p ∈ Finset.filter (fun (p : ℕ) => (p : ℝ) ≤ x ∧ Nat.Prime p) (Finset.range (Nat.floor x + 1)), ((p : ℝ)^2)) - 2 * x) =o[Filter.atTop] (fun (x : ℝ) => x)

/-
The statement of the asymptotic bound for the sum of 1/p^2 for p >= x.
-/
def Bound_sum_primes_ge_x_inv_sq : Prop :=
  (fun (x : ℝ) => ∑' (p : ℕ), if (p : ℝ) ≥ x ∧ Nat.Prime p then 1 / (p : ℝ)^2 else 0) =Θ[Filter.atTop] (fun (x : ℝ) => 1 / (x * Real.log x))

/-
Structure bundling the asymptotic bounds that are assumed without proof.
-/
structure SieveAssumptions where
  bound_prod_primes_le_x_sq : Bound_prod_primes_le_x_sq
  bound_sum_primes_ge_x_inv_sq : Bound_sum_primes_ge_x_inv_sq

/-
SF is the set of squarefree numbers.
-/
def SF : Set ℕ := {n | Squarefree n}

/-
A set A has natural density d if the proportion of elements in A up to n tends to d as n goes to infinity.
-/
def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun n => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop (nhds d)

/-
The sum of mu(d) for d such that d^2 divides n is 1 if n is squarefree and 0 otherwise.
-/
lemma sum_moebius_sq_dvd_eq_indicator (n : ℕ) (hn : n > 0) :
    ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d^2 ∣ n), ArithmeticFunction.moebius d = if Squarefree n then 1 else 0 := by
      -- Let $k$ be the product of the primes dividing $n$.
      set k := ∏ p ∈ Nat.primeFactors n, p ^ (Nat.factorization n p / 2) with hk_def;
      -- If $n$ is not squarefree, then $k > 1$.
      by_cases h_squarefree : Squarefree n;
      · -- If $n$ is squarefree, then the only divisor $d$ such that $d^2 \mid n$ is $d = 1$.
        have h_divisors : ∀ d ∈ Finset.Icc 1 n, d^2 ∣ n → d = 1 := by
          exact fun d hd hdn => by have := h_squarefree.squarefree_of_dvd hdn; rw [ sq, Nat.squarefree_mul_iff ] at this; aesop;
        rw [ Finset.sum_eq_single 1 ] <;> norm_num [ h_squarefree ];
        · exact fun b hb₁ hb₂ hb₃ hb₄ => False.elim <| hb₄ <| h_divisors b ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ ) hb₃;
        · linarith;
      · -- If $n$ is not squarefree, then $k > 1$ and the sum becomes $\sum_{d \mid k} \mu(d)$.
        have h_sum_divisors : (∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (ArithmeticFunction.moebius d)) = (∑ d ∈ Nat.divisors k, (ArithmeticFunction.moebius d)) := by
          have h_sum_divisors : Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n) = Nat.divisors k := by
            ext d;
            constructor <;> intro hd <;> simp_all +decide;
            · -- Since $d^2 \mid n$, for each prime $p$ dividing $d$, we have $2 \cdot \text{exponent}(p \text  {  in } d) \leq \text{exponent}(p \text{ in } n)$.
              have h_exp : ∀ p ∈ Nat.primeFactors d, 2 * (Nat.factorization d p) ≤ Nat.factorization n p := by
                intro p hp; have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 hd.2; aesop;
              -- Since $d^2 \mid n$, for each prime $p$ dividing $d$, we have $d.factorization p \leq (Nat.factorization n p) / 2$.
              have h_exp_le : ∀ p ∈ Nat.primeFactors d, d.factorization p ≤ (Nat.factorization n p) / 2 := by
                exact fun p hp => by rw [ Nat.le_div_iff_mul_le zero_lt_two ] ; linarith [ h_exp p hp ] ;
              refine' ⟨ _, Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ <| Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp ⟩;
              conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith : d ≠ 0 ) ];
              rw [ ← Finset.prod_sdiff <| show d.primeFactors ⊆ n.primeFactors from Nat.primeFactors_mono ( dvd_of_mul_left_dvd hd.2 ) <| by aesop ];
              exact dvd_mul_of_dvd_right ( Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p ( h_exp_le p hp ) ) _;
            · refine' ⟨ ⟨ Nat.pos_of_dvd_of_pos hd.1 ( Finset.prod_pos fun p hp => pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ ), Nat.le_trans ( Nat.le_of_dvd ( Finset.prod_pos fun p hp => pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ ) hd.1 ) _ ⟩, _ ⟩;
              · conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self hn.ne' ];
                exact Finset.prod_le_prod' fun p hp => pow_le_pow_right₀ ( Nat.pos_of_mem_primeFactors hp ) ( Nat.div_le_self _ _ );
              · refine' dvd_trans ( pow_dvd_pow_of_dvd hd.1 2 ) _;
                conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self hn.ne' ];
                rw [ ← Finset.prod_pow ];
                exact Finset.prod_dvd_prod_of_dvd _ _ fun p hp => by rw [ ← pow_mul ] ; exact pow_dvd_pow _ ( Nat.div_mul_le_self _ _ ) ;
          congr;
        -- Since $k > 1$, we can apply the property of the Möbius function that $\sum_{d \mid k} \mu(d ( )  = 0$.
        have h_moebius_sum : ∀ {m : ℕ}, 1 < m → (∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d)) = 0 := by
          intros m hm_gt_one
          have h_moebius_sum : (∑ d ∈ Nat.divisors m, (ArithmeticFunction.moebius d)) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) m := by
            exact Eq.symm ArithmeticFunction.coe_mul_zeta_apply;
          simp_all +decide [ ArithmeticFunction.moebius_mul_coe_zeta ];
          exact if_neg hm_gt_one.ne';
        rw [ if_neg h_squarefree, h_sum_divisors, h_moebius_sum ];
        contrapose! h_squarefree;
        -- If $k \leq 1$, then for all primes $p$ dividing $n$, we have $p^{Nat.factorization n p / 2} \leq 1$, which implies $Nat.factorization n p / 2 = 0$, hence $Nat.factorization n p < 2$.
        have h_factorization : ∀ p ∈ Nat.primeFactors n, Nat.factorization n p < 2 := by
          exact fun p hp => Nat.lt_succ_of_le ( Nat.le_of_not_lt fun h => h_squarefree.not_gt <| lt_of_lt_of_le ( by exact one_lt_pow₀ ( Nat.Prime.one_lt <| Nat.prime_of_mem_primeFactors hp ) <| Nat.ne_of_gt <| Nat.div_pos ( by linarith ) zero_lt_two ) <| Nat.le_of_dvd ( Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos <| Nat.prime_of_mem_primeFactors hq ) _ ) <| Finset.dvd_prod_of_mem _ hp );
        rw [ Nat.squarefree_iff_prime_squarefree ];
        intro p pp dp; specialize h_factorization p; simp_all +decide [← sq] ;
        exact absurd ( h_factorization ( dvd_of_mul_left_dvd dp ) hn.ne' ) ( by have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 dp; aesop )

/-
For n in [1, N], the set of d in [1, N] such that d^2 divides n is the same as the set of d in [1, sqrt(N)] such that d^2 divides n.
-/
lemma filter_sq_dvd_eq_filter_sq_dvd_sqrt (N : ℕ) (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 N) = Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 (Nat.sqrt N)) := by
      ext d
      simp [Finset.mem_Icc];
      exact fun h1 h2 => ⟨ fun h3 => Nat.le_sqrt.2 <| by nlinarith [ Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hn ] ) h1, Finset.mem_Icc.mp hn ], fun h3 => by nlinarith [ Nat.sqrt_le N, Finset.mem_Icc.mp hn ] ⟩

/-
The number of squarefree integers up to N is equal to the sum of mu(d) * floor(N/d^2) for d up to sqrt(N).
-/
lemma sum_squarefree_indicator_eq_sum_moebius_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℤ) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (N / d ^ 2 : ℤ) := by
      -- We'll use the fact that if the condition holds for all $n \leq N$, then the sums are equal.
      have h_sum_eq : ∀ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (if d^2 ∣ n then 1 else 0) := by
        intro n hn
        have h_sum : ∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 (Nat.sqrt N)), (ArithmeticFunction.moebius d) = (if Squarefree n then 1 else 0) := by
          have h_sum : ∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (ArithmeticFunction.moebius d) = (if Squarefree n then 1 else 0) := by
            convert sum_moebius_sq_dvd_eq_indicator n ( Finset.mem_Icc.mp hn |>.1 ) using 1;
          rw [ ← h_sum, Finset.sum_subset ];
          · simp +contextual [ Finset.subset_iff ];
            exact fun x hx₁ hx₂ hx₃ => Nat.le_of_dvd ( Finset.mem_Icc.mp hn |>.1 ) ( dvd_of_mul_left_dvd hx₃ );
          · simp +zetaDelta at *;
            exact fun x hx₁ hx₂ hx₃ hx₄ => False.elim <| hx₄ hx₁ ( Nat.le_sqrt.mpr <| by nlinarith [ Nat.le_of_dvd ( by linarith ) hx₃ ] ) hx₃;
        simp_all +decide [ Finset.sum_ite ];
      -- By interchanging the order of summation, we can rewrite the right-hand side of the equation.
      have h_interchange : (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (if d^2 ∣ n then 1 else 0))) = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (∑ n ∈ Finset.Icc 1 N, (if d^2 ∣ n then 1 else 0))) := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _ ];
      convert h_interchange using 1;
      · exact Finset.sum_congr rfl h_sum_eq;
      · refine' Finset.sum_congr rfl fun x hx => _;
        simp +zetaDelta at *;
        rw [ show Finset.filter ( fun y => x ^ 2 ∣ y ) ( Finset.Icc 1 N ) = Finset.image ( fun y => x ^ 2 * y ) ( Finset.Icc 1 ( N / x ^ 2 ) ) from ?_, Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( pow_ne_zero 2 ( by linarith : x ≠ 0 ) ) h ] ; norm_num;
        -- To prove equality of finite sets, we show each set is a subset of the other.
        apply Finset.ext
        intro y
        simp;
        exact ⟨ fun h => ⟨ y / x ^ 2, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( pow_pos ( by linarith ) 2 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ pow_pos ( by linarith : 0 < x ) 2 ], by nlinarith [ Nat.div_mul_le_self N ( x ^ 2 ) ] ⟩, by norm_num ⟩ ⟩

/-
The number of squarefree integers up to N is equal to the sum of mu(d) * floor(N/d^2) for d up to sqrt(N).
-/
lemma sum_squarefree_indicator_eq_sum_moebius_floor_v2 (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℤ) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d) * (N / d ^ 2 : ℤ) := by
      convert sum_squarefree_indicator_eq_sum_moebius_floor N using 1

/-
The partial sums of mu(d)/d^2 converge to 6/pi^2.
-/
lemma sum_moebius_div_sq_tendsto : Filter.Tendsto (fun k => ∑ d ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius d : ℝ) / d ^ 2) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  -- We know that $\sum_{d=1}^{\infty} \frac{\mu(d)}{d^2} = \frac{1}{\zeta(2)}$.
  have h_sum : ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ) = 1 / (Real.pi ^ 2 / 6) := by
    -- By definition of $L(2, \mu)$, we know that $L(2, \mu) = \sum_{d=1}^{\infty} \frac{\mu(d)}{d^2}$.
    have h_L2_mu : (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) = (riemannZeta 2)⁻¹ := by
      have h_L2_mu : (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) = (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) := by
        norm_num [ LSeries ];
        convert Complex.ofReal_tsum _;
        norm_num [ LSeries.term ];
        aesop;
      have h_L2_mu : (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) * (riemannZeta 2) = 1 := by
        convert ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius _ using 1;
        rw [ mul_comm ];
        rw [ ArithmeticFunction.LSeries_zeta_eq_riemannZeta ];
        · norm_num;
        · norm_num;
      exact eq_inv_of_mul_eq_one_left <| by aesop;
    -- We know that $\zeta(2) = \frac{\pi^2}{6}$.
    have h_zeta2 : riemannZeta 2 = Real.pi ^ 2 / 6 := by
      exact riemannZeta_two;
    simp_all +decide [ Complex.ext_iff, sq ];
    norm_cast;
  convert h_sum ▸ Summable.hasSum _ |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 using 2 <;> norm_num [ Finset.sum_Ico_eq_sub ];
  · erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num;
  · exact ( by contrapose! h_sum; erw [ tsum_eq_zero_of_not_summable h_sum ] ; positivity )

/-
The set of squarefree numbers has natural density 6/pi^2.
-/
theorem SF_density : HasNaturalDensity SF (6 / Real.pi ^ 2) := by
  -- We need to show that $\frac{1}{N} |SF \cap [1, N]| \to \frac{6}{\pi^2}$.
  suffices h_limit : Filter.Tendsto (fun N => (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℝ)) / N) Filter.atTop (nhds (6 / Real.pi ^ 2)) by
    -- By definition of `SF`, we know that `|SF ∩ [1, N]|` is equal to the sum of mu(d) * floor(N/d^2) for d up to sqrt(N).
    have h_card : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℝ)) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℝ) - ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (Int.fract (N / d ^ 2 : ℝ)) := by
      intro N
      have h_card_eq : (∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℝ)) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℝ) - ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (Int.fract (N / d ^ 2 : ℝ)) := by
        have h_sum_eq : ∑ n ∈ Finset.Icc 1 N, (if Squarefree n then 1 else 0 : ℤ) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℤ) * (N / d ^ 2 : ℤ) := by
          convert sum_squarefree_indicator_eq_sum_moebius_floor_v2 N using 1
        -- Apply the equality of the integer and real sums to rewrite the left-hand side.
        have h_rewrite : (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℤ)) = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℝ)) - (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * (Int.fract (N / d ^ 2 : ℝ))) := by
          rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Int.fract ] ; ring_nf;
          field_simp;
          rw [ show ⌊ ( N : ℝ ) / x ^ 2⌋ = N / x ^ 2 from Int.floor_eq_iff.mpr ⟨ by rw [ le_div_iff₀ ( by norm_cast; nlinarith [ Finset.mem_Icc.mp hx ] ) ] ; norm_cast; linarith [ Nat.div_mul_le_self N ( x ^ 2 ) ], by rw [ div_lt_iff₀ ( by norm_cast; nlinarith [ Finset.mem_Icc.mp hx ] ) ] ; norm_cast; linarith [ Nat.div_add_mod N ( x ^ 2 ), Nat.mod_lt N ( by nlinarith [ Finset.mem_Icc.mp hx ] : 0 < x ^ 2 ) ] ⟩ ];
        convert h_rewrite using 1;
        exact_mod_cast h_sum_eq;
      convert h_card_eq using 1;
    -- The second term is bounded by $\frac{1}{N} \sum_{d=1}^{\sqrt{N}} 1 = \frac{\lfloor \sqrt{N} \rfloor}{N} \le \frac{1}{\sqrt{N}}$, which tends to 0.
    have h_second_term : Filter.Tendsto (fun N => (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * Int.fract (N / d ^ 2 : ℝ)) / N) Filter.atTop (nhds 0) := by
      -- The absolute value of the second term is bounded by $\frac{1}{N} \sum_{d=1}^{\sqrt{N}} 1 = \frac{\lfloor \sqrt{N} \rfloor}{N} \le \frac{1}{\sqrt{N}}$, which tends to 0.
      have h_second_term_abs : ∀ N : ℕ, |(∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * Int.fract (N / d ^ 2 : ℝ)) / N| ≤ (Nat.sqrt N : ℝ) / N := by
        intros N
        have h_abs : |∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * Int.fract (N / d ^ 2 : ℝ)| ≤ Nat.sqrt N := by
          refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
          refine' le_trans ( Finset.sum_le_sum fun i hi => _ ) _;
          use fun i => 1;
          · norm_num [ abs_mul, ArithmeticFunction.moebius ];
            split_ifs <;> norm_num [ abs_mul, abs_of_nonneg, Int.fract_nonneg, Int.fract_lt_one ];
            exact Int.fract_lt_one _ |> le_of_lt;
          · norm_num;
        rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ N ) ] ; gcongr;
      refine' squeeze_zero_norm h_second_term_abs _;
      refine' squeeze_zero_norm' _ _;
      use fun n => 1 / Real.sqrt n;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_le_div_iff₀ ] <;> first | positivity | nlinarith [ Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, show ( n :ℝ ) ≥ 1 by exact_mod_cast hn, show ( Nat.sqrt n :ℝ ) ^ 2 ≤ n by exact_mod_cast Nat.sqrt_le' n ] ;
      · simpa using tendsto_inverse_atTop_nhds_zero_nat.sqrt;
    refine' Filter.Tendsto.congr' _ ( by simpa using h_limit.sub h_second_term );
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN ; simp_all +decide [div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Set.ncard_eq_toFinset_card'] ;
    simp_all +decide [← Finset.mul_sum _ _ _, hN.ne'];
    rw [ show ( Finset.filter ( fun a => a ∈ SF ) ( Finset.Icc 1 N ) ) = Finset.filter ( fun x => Squarefree x ) ( Finset.Icc 1 N ) by ext; aesop ] ; rw [ h_card ] ; ring_nf;
    norm_num [ hN.ne' ];
  -- We'll use the fact that $\sum_{d=1}^{\sqrt{N}} \frac{\mu(d)}{d^2} \left\lfloor \frac{N}{d^2} \right\rfloor$ is approximately $\frac{6}{\pi^2} N$.
  have h_sum_approx : Filter.Tendsto (fun N : ℕ => (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) / d ^ 2)) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
    convert sum_moebius_div_sq_tendsto.comp ( Filter.tendsto_atTop_atTop.mpr _ ) using 1;
    · exact ⟨ 0 ⟩;
    · infer_instance;
    · exact fun b => ⟨ b ^ 2, fun a ha => by nlinarith [ Nat.lt_succ_sqrt a ] ⟩;
  refine h_sum_approx.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using by simp +decide [div_eq_mul_inv,
    mul_assoc, mul_comm, Finset.mul_sum _ _ _, hN.ne'] )

/-
A set A has property Q if for infinitely many n, n+a is squarefree for all a in A with a < n.
-/
def PropertyQ (A : Set ℕ) : Prop := ({n | ∀ a ∈ A, a < n → Squarefree (n + a)}).Infinite

/-
A set A is admissible if for every prime p, there is a residue class mod p^2 that A avoids.
-/
def Admissible (A : Set ℕ) : Prop :=
  ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ A, a % p^2 ≠ b

/-
Definitions of the sequences A1, A2, A3, A4 as sets of natural numbers.
-/
def A1 : Set ℕ := {n | ∃ j : ℕ, j ≥ 1 ∧ n = 2^j + 1}
def A2 : Set ℕ := {n | ∃ j : ℕ, j ≥ 1 ∧ n = 2^j - 1}
def A3 : Set ℕ := {n | ∃ j : ℕ, j ≥ 1 ∧ n = Nat.factorial j + 1}
def A4 : Set ℕ := {n | ∃ j : ℕ, j > 1 ∧ n = Nat.factorial j - 1}

/-
Every set with property Q is admissible.
-/
theorem PropertyQ_implies_Admissible (A : Set ℕ) (h : PropertyQ A) : Admissible A := by
  intro p hp
  obtain ⟨S, hS_inf, hS⟩ : ∃ S : Set ℕ, S.Infinite ∧ ∀ n ∈ S, ∀ a ∈ A, a < n → ¬(n + a) % p^2 = 0 := by
    refine' ⟨ _, h, fun n hn a ha ha' => _ ⟩;
    intro H; have := hn a ha ha'; rw [ ← Nat.dvd_iff_mod_eq_zero ] at H; have := this.squarefree_of_dvd H; simp_all +decide [ sq, Nat.squarefree_mul_iff ] ;
  -- By the pigeonhole principle, since there are infinitely many $n$ in $S$ and only finitely many residue classes mod $p^2$, there must be a residue class $b$ such that $b_n = b$ for infinitely many $n$.
  obtain ⟨b, hb⟩ : ∃ b < p^2, Set.Infinite {n ∈ S | n % p^2 = b} := by
    by_contra h_contra;
    exact hS_inf <| Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_lt_nat <| p ^ 2 ) fun i hi => Set.not_infinite.mp fun hi' => h_contra ⟨ i, hi, hi' ⟩ ) fun x hx => by have := Nat.mod_lt x ( pow_pos hp.pos 2 ) ; aesop;
  use ( p^2 - b % p^2 ) % p^2;
  refine' ⟨ Nat.mod_lt _ ( pow_pos hp.pos _ ), fun a ha ha' => _ ⟩;
  -- Since there are infinitely many $n \in S$ such that $n \equiv b \pmod{p^2}$, we can choose $n$ large enough so that $n > a$.
  obtain ⟨n, hnS, hn_gt⟩ : ∃ n ∈ S, n > a ∧ n % p^2 = b := by
    exact Exists.elim ( hb.2.exists_gt a ) fun n hn => ⟨ n, hn.1.1, hn.2, hn.1.2 ⟩;
  specialize hS n hnS a ha hn_gt.1 ; simp_all +decide [ Nat.add_mod ];
  simp_all +decide [ Nat.add_sub_of_le ( Nat.mod_lt _ ( pow_pos hp.pos 2 ) |> Nat.le_of_lt ) ]

/-
Property Q is downwardly monotone.
-/
lemma PropertyQ_monotone (A B : Set ℕ) (h : A ⊆ B) (hB : PropertyQ B) : PropertyQ A := by
  contrapose! hB;
  unfold PropertyQ at *;
  simp +zetaDelta at *;
  refine Set.Finite.subset ( hB.union ( Set.finite_singleton 0 ) ) ?_ ; intro n ; aesop

/-
The upper density of a set A of natural numbers.
-/
def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

/-
Weak asymptotic bound for the sum of 1/p^2 for p >= x.
-/
lemma sum_primes_ge_x_inv_sq_bound_weak :
    (fun (x : ℝ) => ∑' (p : ℕ), if (p : ℝ) ≥ x ∧ Nat.Prime p then 1 / (p : ℝ)^2 else 0) =O[Filter.atTop] (fun (x : ℝ) => 1 / x) := by
      refine' Asymptotics.isBigO_iff.mpr _;
      use 4;
      -- We'll use the fact that $\sum_{p \geq x} \frac{1}{p^2}$ is bounded above by $\frac{4}{x}$ for $x \geq 2$.
      have h_bound : ∀ x : ℝ, 2 ≤ x → ∑' p : ℕ, (if (p : ℝ) ≥ x ∧ Nat.Prime p then (1 / (p : ℝ) ^ 2) else 0) ≤ 4 / x := by
        -- We'll use the fact that $\sum_{p \geq x} \frac{1}{p^2}$ is bounded above by $\frac{4}{x}$ for $x \geq 2$. This follows from the integral test.
        have h_integral_bound : ∀ x : ℝ, 2 ≤ x → (∑' p : ℕ, (if (p : ℝ) ≥ x ∧ Nat.Prime p then (1 / (p : ℝ) ^ 2) else 0)) ≤ ∑' p : ℕ, (if (p : ℝ) ≥ x then (1 / (p : ℝ) ^ 2) else 0) := by
          intro x hx; refine' Summable.tsum_le_tsum _ _ _; aesop;
          · exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
          · exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
        -- We'll use the fact that $\sum_{p \geq x} \frac{1}{p^2}$ is bounded above by $\frac{4}{x}$ for $x \geq 2$. This follows from the integral test and the fact that $\sum_{p \geq x} \frac{1}{p^2}$ is a p-series with $p=2$.
        have h_pseries_bound : ∀ x : ℝ, 2 ≤ x → (∑' p : ℕ, (if (p : ℝ) ≥ x then (1 / (p : ℝ) ^ 2) else 0)) ≤ ∑' p : ℕ, (if (p : ℝ) ≥ x then (1 / ((p - 1) * p : ℝ)) else 0) := by
          intro x hx; refine' Summable.tsum_le_tsum _ _ _;
          · intro i; split_ifs <;> norm_num;
            rw [ ← mul_inv, inv_le_inv₀ ] <;> nlinarith [ show ( i : ℝ ) ≥ 2 by exact_mod_cast le_trans ( by norm_num ) ( Nat.cast_le.mpr ( show i ≥ 2 by exact_mod_cast le_trans ( by norm_num ) ( Nat.cast_le.mpr ( show i ≥ 2 by exact_mod_cast le_trans hx ‹x ≤ ( i : ℝ ) › ) ) ) ) ];
          · exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by split_ifs <;> first | positivity | simp ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
          · rw [ ← summable_nat_add_iff ⌈x⌉₊ ];
            refine' Summable.of_nonneg_of_le ( fun n => _ ) ( fun n => _ ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
            · split_ifs <;> first | positivity | exact one_div_nonneg.2 <| mul_nonneg ( sub_nonneg.2 <| Nat.one_le_cast.2 <| by linarith [ Nat.ceil_pos.2 <| show 0 < x by positivity ] ) <| Nat.cast_nonneg _;
            · split_ifs <;> norm_num;
              · rw [ ← mul_inv ] ; gcongr ; nlinarith [ Nat.le_ceil x, show ( n : ℝ ) ≥ 0 by positivity ];
              · positivity;
        -- We'll use the fact that $\sum_{p \geq x} \frac{1}{(p-1)p}$ is a telescoping series.
        have h_telescoping : ∀ x : ℝ, 2 ≤ x → (∑' p : ℕ, (if (p : ℝ) ≥ x then (1 / ((p - 1) * p : ℝ)) else 0)) ≤ 1 / (⌈x⌉₊ - 1) := by
          intros x hx
          have h_telescoping_series : ∀ N : ℕ, N ≥ ⌈x⌉₊ → (∑ p ∈ Finset.Icc ⌈x⌉₊ N, (1 / ((p - 1) * p : ℝ))) = 1 / (⌈x⌉₊ - 1) - 1 / (N : ℝ) := by
            intro N hN
            induction' N, hN using Nat.le_induction with N hN ih;
            · norm_num +zetaDelta at *;
              rw [ ← mul_inv, inv_sub_inv ] <;> ring_nf <;> nlinarith [ Nat.le_ceil x, show ( ⌈x⌉₊ : ℝ ) ≥ 2 by exact_mod_cast Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; linarith ) ) ];
            · erw [ Finset.sum_Ico_succ_top ( by linarith ), ih ] ; push_cast ; ring_nf;
              rw [ show ( N : ℝ ) + N ^ 2 = N * ( 1 + N ) by ring, mul_inv ] ; ring_nf;
              nlinarith only [ inv_pos.mpr ( show 0 < ( N : ℝ ) by norm_cast; linarith [ Nat.ceil_pos.mpr ( show 0 < x by linarith ) ] ), inv_pos.mpr ( show 0 < ( 1 + N : ℝ ) by positivity ), mul_inv_cancel₀ ( show ( N : ℝ ) ≠ 0 by norm_cast; linarith [ Nat.ceil_pos.mpr ( show 0 < x by linarith ) ] ), mul_inv_cancel₀ ( show ( 1 + N : ℝ ) ≠ 0 by positivity ) ];
          -- By the properties of the telescoping series, we can bound the sum.
          have h_telescoping_bound : ∀ N : ℕ, N ≥ ⌈x⌉₊ → (∑ p ∈ Finset.Icc 1 N, (if (p : ℝ) ≥ x then (1 / ((p - 1) * p : ℝ)) else 0)) ≤ 1 / (⌈x⌉₊ - 1) := by
            intro N hN; rw [ ← Finset.sum_filter ] ; rw [ show ( Finset.filter ( fun p : ℕ => x ≤ ( p : ℝ ) ) ( Finset.Icc 1 N ) ) = Finset.Icc ⌈x⌉₊ N from ?_ ] ; simp_all +decide [ mul_comm ] ;
            ext; simp [Finset.mem_Icc];
            exact ⟨ fun h => ⟨ h.2, h.1.2 ⟩, fun h => ⟨ ⟨ Nat.pos_of_ne_zero fun h' => by norm_num [ h' ] at h; linarith, h.2 ⟩, h.1 ⟩ ⟩;
          contrapose! h_telescoping_bound;
          have h_telescoping_bound : Filter.Tendsto (fun N : ℕ => ∑ p ∈ Finset.Icc 1 N, (if (p : ℝ) ≥ x then (1 / ((p - 1) * p : ℝ)) else 0)) Filter.atTop (nhds (∑' p : ℕ, (if (p : ℝ) ≥ x then (1 / ((p - 1) * p : ℝ)) else 0))) := by
            have h_telescoping_bound : Summable (fun p : ℕ => if (p : ℝ) ≥ x then (1 / ((p - 1) * p : ℝ)) else 0) := by
              exact ( by by_contra h; rw [ tsum_eq_zero_of_not_summable h ] at h_telescoping_bound; exact h_telescoping_bound.not_ge <| by exact div_nonneg zero_le_one <| sub_nonneg_of_le <| Nat.one_le_cast.mpr <| Nat.ceil_pos.mpr <| by positivity );
            convert h_telescoping_bound.hasSum.tendsto_sum_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) using 1;
            exact funext fun n => by erw [ Function.comp_apply, Finset.sum_Ico_eq_sub _ ] <;> norm_num;
          exact Filter.eventually_atTop.mp ( h_telescoping_bound.eventually ( lt_mem_nhds ‹_› ) ) |> fun ⟨ N, hN ⟩ => ⟨ N + ⌈x⌉₊, by linarith, hN _ <| by linarith ⟩;
        intro x hx; refine le_trans ( h_integral_bound x hx ) ( le_trans ( h_pseries_bound x hx ) ( le_trans ( h_telescoping x hx ) ?_ ) ) ; rw [ div_le_div_iff₀ ] <;> nlinarith [ Nat.le_ceil x, show ( x : ℝ ) ≥ 2 by exact_mod_cast hx ] ;
      filter_upwards [ Filter.eventually_ge_atTop 2 ] with x hx using by rw [ Real.norm_of_nonneg ( tsum_nonneg fun _ => by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; simpa using h_bound x hx;

/-
The number of integers in an interval of length L that are congruent to a modulo m is L/m + O(1).
-/
lemma card_filter_modEq_Icc (u L a m : ℕ) (hm : m > 0) :
  let I := Finset.Icc u (u + L - 1)
  let S := I.filter (fun x => x ≡ a [MOD m])
  abs ((S.card : ℝ) - (L : ℝ) / m) ≤ 2 := by
    refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
    · refine' le_trans ( sub_le_sub_right ( Nat.cast_le.mpr <| Finset.card_le_card <| show Finset.filter ( fun x => x ≡ a [MOD m] ) ( Finset.Icc u ( u + L - 1 ) ) ⊆ Finset.image ( fun k => m * k + a % m ) ( Finset.Icc ( u / m ) ( ( u + L - 1 ) / m ) ) from _ ) _ ) _;
      · intro x hx; simp_all +decide [ Nat.ModEq ];
        exact ⟨ x / m, ⟨ Nat.div_le_div_right hx.1.1, Nat.div_le_div_right hx.1.2 ⟩, by linarith [ Nat.mod_add_div x m ] ⟩;
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by nlinarith [ Nat.mod_lt a hm ] ] ; norm_num;
        rcases L with ( _ | L ) <;> norm_num [ Nat.succ_div ];
        · exact le_trans ( add_le_add_right ( Nat.div_le_div_right ( Nat.sub_le _ _ ) ) _ ) ( by omega );
        · field_simp;
          exact mod_cast by nlinarith [ Nat.div_mul_le_self ( u + L ) m, Nat.div_add_mod ( u + L ) m, Nat.mod_lt ( u + L ) hm, Nat.div_mul_le_self u m, Nat.div_add_mod u m, Nat.mod_lt u hm, Nat.sub_add_cancel ( show u / m ≤ ( u + L ) / m + 1 from Nat.le_succ_of_le ( Nat.div_le_div_right ( by linarith ) ) ) ] ;
    · -- The set of integers in [u, u+L-1] that are congruent to a modulo m forms an arithmetic progression with common difference m.
      have h_arith_prog : Finset.filter (fun x => x ≡ a [MOD m]) (Finset.Icc u (u + L - 1)) ⊇ Finset.image (fun k => u + ((a + m - u % m) % m) + k * m) (Finset.range (L / m)) := by
        intro x hxaesop;
        norm_num +zetaDelta at *;
        rcases hxaesop with ⟨ k, hk₁, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Nat.zero_le ( ( a + m - u % m ) % m ) ], Nat.le_sub_one_of_lt ( by nlinarith [ Nat.div_mul_le_self L m, Nat.zero_le ( ( a + m - u % m ) % m ), Nat.mod_lt ( a + m - u % m ) hm ] ) ⟩, by simp +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_sub ( show u % m ≤ a + m from by linarith [ Nat.mod_lt u hm ] ) ] ⟩ ;
      have := Finset.card_mono h_arith_prog; simp_all +decide [ Finset.card_image_of_injective, Function.Injective, hm.ne' ] ;
      rw [ div_le_iff₀ ] <;> norm_cast ; nlinarith [ Nat.div_add_mod L m, Nat.mod_lt L hm ]

/-
The number of integers in an interval of length L satisfying two coprime modular constraints is L/(Wq) + O(1).
-/
lemma card_intersect_bound (u L W q b c : ℕ) (hWq : Nat.Coprime W q) (hW : W > 0) (hq : q > 0) :
  let I := Finset.Icc u (u + L - 1)
  let S_intersect := I.filter (fun n => n ≡ b [MOD W] ∧ n ≡ c [MOD q])
  abs ((S_intersect.card : ℝ) - (L : ℝ) / (W * q)) ≤ 2 := by
    -- By the Chinese Remainder Theorem, there exists a unique solution modulo $Wq$ to the system of congruences $n \equiv b \pmod{W}$ and $n \equiv c \pmod{q}$.
    obtain ⟨a, ha⟩ : ∃ a, a ≡ b [MOD W] ∧ a ≡ c [MOD q] ∧ a < W * q := by
      have := Nat.chineseRemainder hWq b c;
      exact ⟨ this.val % ( W * q ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.property.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.property.2, Nat.mod_lt _ ( Nat.mul_pos hW hq ) ⟩;
    -- The set of integers in $I$ that are congruent to $a$ modulo $Wq$ is exactly the set of integers in $I$ that satisfy both congruences.
    have h_set_eq : {n ∈ Finset.Icc u (u + L - 1) | n ≡ b [MOD W] ∧ n ≡ c [MOD q]} = {n ∈ Finset.Icc u (u + L - 1) | n ≡ a [MOD (W * q)]} := by
      ext n; simp_all +decide ;
      intro _ _; rw [ ← Nat.modEq_and_modEq_iff_modEq_mul ] ; simp_all +decide [ Nat.ModEq ] ;
      assumption;
    convert card_filter_modEq_Icc u L a ( W * q ) ( mul_pos hW hq ) using 1 ; aesop

/-
Lemma freq: Let b mod W, c mod q be congruence classes with W coprime to q, and let I be an interval of length L >= W. Then, if n is drawn uniformly at random from those elements of b mod W that lie in I, the probability that n lies in c mod q is O(1/q + W/L).
-/
lemma lemma_freq :
  ∃ C : ℝ, C > 0 ∧ ∀ (W q : ℕ) (b c : ℕ) (u L : ℕ),
    Nat.Coprime W q → L ≥ W →
    let I := Finset.Icc u (u + L - 1)
    let S := I.filter (fun n => n ≡ b [MOD W])
    let N_S := S.card
    let N_intersect := (S.filter (fun n => n ≡ c [MOD q])).card
    N_S > 0 →
    (N_intersect : ℝ) / N_S ≤ C * (1 / (q : ℝ) + (W : ℝ) / L) := by
      refine' ⟨ 4, by norm_num, fun W q b c u L hWq hL hS => _ ⟩;
      -- Let's consider the two cases: $L \geq 4W$ and $W \leq L < 4W$.
      by_cases h_case : L ≥ 4 * W;
      · -- Using the bounds from card_filter_modEq_Icc and card_intersect_bound, we have:
        have h_bound : (Finset.filter (fun n => n ≡ c [MOD q]) (Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1)))).card ≤ (L : ℝ) / (W * q) + 2 ∧ (Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1))).card ≥ (L : ℝ) / W - 2 := by
          have h_bounds : abs ((Finset.filter (fun n => n ≡ c [MOD q]) (Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1)))).card - (L : ℝ) / (W * q)) ≤ 2 ∧ abs ((Finset.filter (fun n => n ≡ b [MOD W]) (Finset.Icc u (u + L - 1))).card - (L : ℝ) / W) ≤ 2 := by
            apply And.intro;
            · by_cases hW : W = 0 <;> by_cases hq : q = 0 <;> simp_all +decide [ Nat.Coprime ];
              · exact le_trans ( Finset.card_le_one.mpr ( by aesop ) ) ( by norm_num );
              · exact le_trans ( Finset.card_le_one.mpr ( by aesop ) ) ( by norm_num );
              · convert card_intersect_bound u L W q b c hWq ( Nat.pos_of_ne_zero hW ) ( Nat.pos_of_ne_zero hq ) using 1;
                simp +decide only [Finset.filter_filter];
            · by_cases hW : W = 0 <;> simp_all +decide [ Nat.ModEq ];
              · exact le_trans ( Finset.card_le_one.mpr ( by aesop ) ) ( by norm_num );
              · convert card_filter_modEq_Icc u L b W ( Nat.pos_of_ne_zero hW ) using 1;
          exact ⟨ by linarith [ abs_le.mp h_bounds.1 ], by linarith [ abs_le.mp h_bounds.2 ] ⟩;
        by_cases hW : W = 0 <;> by_cases hq : q = 0 <;> simp_all +decide [ division_def ];
        · exact le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr h_bound.1 ) ( by positivity ) ) ( by rw [ ← div_eq_mul_inv ] ; rw [ div_le_iff₀ ] <;> norm_cast <;> linarith [ Finset.card_pos.mpr hS ] );
        · norm_num [ Nat.modEq_iff_dvd ] at *;
          field_simp;
          rw [ div_le_iff₀ ] <;> norm_cast at * <;> cases L <;> norm_num at * ; nlinarith;
          linarith;
        · rw [ ← div_eq_mul_inv, div_le_iff₀ ];
          · field_simp at *;
            rw [ add_div', mul_div_assoc' ] <;> try norm_cast ; linarith [ Nat.pos_of_ne_zero hW, Nat.pos_of_ne_zero hq ];
            rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast at * <;> try linarith [ Nat.pos_of_ne_zero hW, Nat.pos_of_ne_zero hq ] ;
            nlinarith [ Nat.pos_of_ne_zero hW, Nat.pos_of_ne_zero hq, mul_pos ( Nat.pos_of_ne_zero hW ) ( Nat.pos_of_ne_zero hq ) ];
          · exact Nat.cast_pos.mpr ( Finset.card_pos.mpr hS );
      · refine' le_trans ( div_le_one_of_le₀ _ _ ) _;
        · exact_mod_cast Finset.card_mono <| Finset.filter_subset _ _;
        · positivity;
        · rcases q with ( _ | _ | q ) <;> norm_num at *;
          · rw [ mul_div, le_div_iff₀ ] <;> norm_cast <;> linarith [ show L > 0 from Nat.pos_of_ne_zero ( by aesop_cat ) ];
          · exact le_trans ( by norm_num ) ( mul_le_mul_of_nonneg_left ( le_add_of_nonneg_right <| by positivity ) zero_le_four );
          · field_simp;
            rw [ add_div', mul_div_assoc', le_div_iff₀ ] <;> norm_cast <;> nlinarith

/-
A set has upper density 0 if and only if it has natural density 0.
-/
lemma upperDensity_eq_zero_iff_HasNaturalDensity_zero (A : Set ℕ) :
  upperDensity A = 0 ↔ HasNaturalDensity A 0 := by
    constructor <;> intro h;
    · refine' tendsto_order.2 ⟨ _, _ ⟩;
      · exact fun x hx => Filter.Eventually.of_forall fun n => hx.trans_le <| by positivity;
      · intro a ha; rw [ upperDensity ] at h; simp_all +decide [ Filter.limsup_eq ] ;
        contrapose! h;
        refine' ne_of_gt ( lt_of_lt_of_le ha ( le_csInf _ _ ) ) <;> norm_num;
        · exact ⟨ 1, ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| show A ∩ Set.Icc 1 n ⊆ Set.Icc 1 n from fun x hx => hx.2 ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ) <| by positivity ⟩ ⟩;
        · exact fun b x hx => by obtain ⟨ y, hy₁, hy₂ ⟩ := h x; exact le_trans hy₂ ( hx y hy₁ ) ;
    · exact h.limsup_eq.symm ▸ rfl

/-
Every admissible set has upper density at most 6/pi^2.
-/
theorem Admissible_implies_upperDensity_le_6_div_pi_sq (A : Set ℕ) (h : Admissible A) :
  upperDensity A ≤ 6 / Real.pi^2 := by
    convert le_of_tendsto_of_tendsto' tendsto_const_nhds ( prod_primes_inv_sq_tendsto ) ( fun k => ?_ ) using 1;
    have := admissible_upper_bound_C A h ( k - 1 ) ; rcases k with ( _ | k ) <;> aesop;

/-
Theorem 2: Every sequence with property Q has upper density at most 6/pi^2.
-/
theorem TheoremQ1_upper (A : Set ℕ) (h : PropertyQ A) : upperDensity A ≤ 6 / Real.pi^2 := by
  -- Apply the lemma that states if A is admissible, then its upper density is at most 6/π².
  apply Admissible_implies_upperDensity_le_6_div_pi_sq A (PropertyQ_implies_Admissible A h)

/-
The product of $p^2$ for all primes $p \le n^2$.
-/
def W_sq (n : ℕ) : ℕ := ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n^2 + 1)), p^2

/-
W_val(x) is the product of p^2 for all primes p <= 0.1 log x.
-/
def W_val (x : ℝ) : ℕ := ∏ p ∈ (Finset.range (Nat.floor (0.1 * Real.log x) + 1)).filter Nat.Prime, p^2

/-
For sufficiently large x, W_val(x) <= x^0.25.
-/
lemma W_bound (h : SieveAssumptions) :
  ∀ᶠ x in Filter.atTop,
    (W_val x : ℝ) ≤ Real.exp (0.25 * Real.log x) := by
      -- From the assumption `bound_prod_primes_le_x_sq`, we know that $\log(\prod_{p \le y} p^2) = 2y + o(y)$.
      have h_log_prod : Filter.Tendsto (fun x => Real.log (W_val x) / (0.1 * Real.log x)) Filter.atTop (nhds 2) := by
        have h_log_prod : Filter.Tendsto (fun y => Real.log (∏ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.floor y + 1)), p^2) / y) Filter.atTop (nhds 2) := by
          have := h.bound_prod_primes_le_x_sq;
          have := this.tendsto_div_nhds_zero;
          have := this.const_add 2;
          simp_all +decide [ add_div ];
          refine' this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ show ( Finset.filter ( fun p : ℕ => ( p : ℝ ) ≤ x ∧ Nat.Prime p ) ( Finset.range ( ⌊x⌋₊ + 1 ) ) ) = Finset.filter Nat.Prime ( Finset.range ( ⌊x⌋₊ + 1 ) ) from Finset.filter_congr fun p hp => by exact ⟨ fun h => h.2, fun h => ⟨ Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp hp ), h ⟩ ⟩ ] ; rw [ add_div' ] ; ring ; positivity );
        convert h_log_prod.comp ( show Filter.Tendsto ( fun x : ℝ => 0.1 * Real.log x ) Filter.atTop Filter.atTop from Filter.Tendsto.const_mul_atTop ( by norm_num ) ( Real.tendsto_log_atTop ) ) using 2 ; norm_num [ W_val ];
      -- For large enough $x$, $0.2 \log x + o(\log x) \le 0.25 \log x$.
      have h_log_prod_le : ∀ᶠ x in Filter.atTop, Real.log (W_val x) ≤ 0.25 * Real.log x := by
        have := h_log_prod.eventually ( gt_mem_nhds <| show 2 < 0.25 / 0.1 by norm_num );
        filter_upwards [ this, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using by rw [ div_lt_iff₀ ( mul_pos ( by norm_num ) ( Real.log_pos hx₂ ) ) ] at hx₁; norm_num at *; linarith;
      filter_upwards [ h_log_prod_le, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using by rw [ ← Real.log_le_iff_le_exp ( by exact Nat.cast_pos.mpr <| Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) 2 ) ] ; exact hx₁;

/-
The sum of 1/p^2 for primes p in (0.1 log x, sqrt(2x)] is O(1/(log x log log x)).
-/
lemma sum_inv_sq_part_O (h : SieveAssumptions) :
  (fun x => ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), 1 / (p : ℝ)^2)
  =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
    have := h.2;
    -- The sum is bounded by the infinite sum $\sum_{p > 0.1 \log x} 1/p^2$.
    have h_sum_bound : ∀ x : ℝ, x ≥ 2 → (∑ p ∈ Finset.filter (fun p : ℕ => 0.1 * Real.log x < p ∧ p ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (1 / (p ^ 2 : ℝ))) ≤ (∑' p : ℕ, if (p : ℝ) ≥ 0.1 * Real.log x ∧ Nat.Prime p then 1 / (p ^ 2 : ℝ) else 0) := by
      intro x hx
      have h_subset : Finset.filter (fun p : ℕ => 0.1 * Real.log x < p ∧ p ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)) ⊆ Finset.filter (fun p : ℕ => Nat.Prime p ∧ 0.1 * Real.log x ≤ p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)) := by
        exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hp |>.1, Finset.mem_filter.mp hp |>.2.2.2, le_of_lt ( Finset.mem_filter.mp hp |>.2.1 ) ⟩;
      refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_subset fun _ _ _ => by positivity ) _;
      refine' le_trans _ ( Summable.sum_le_tsum _ _ _ );
      any_goals exact Finset.range ( ⌊Real.sqrt ( 2 * x ) ⌋₊ + 1 );
      · rw [ Finset.sum_filter ] ; exact Finset.sum_le_sum fun _ _ => by aesop;
      · exact fun _ _ => by positivity;
      · exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
    -- By assumption `bound_sum_primes_ge_x_inv_sq`, the tail sum starting at $y$ is $\Theta(1/(y \log y))$.
    have h_tail_sum : (fun x : ℝ => ∑' p : ℕ, if (p : ℝ) ≥ 0.1 * Real.log x ∧ Nat.Prime p then 1 / (p ^ 2 : ℝ) else 0) =O[Filter.atTop] (fun x : ℝ => 1 / ((0.1 * Real.log x) * Real.log (0.1 * Real.log x))) := by
      obtain ⟨ C, hC ⟩ := this;
      convert C.comp_tendsto ( show Filter.Tendsto ( fun x : ℝ => 0.1 * Real.log x ) Filter.atTop Filter.atTop from Filter.Tendsto.const_mul_atTop ( by norm_num ) ( Real.tendsto_log_atTop ) ) using 1;
    -- Since $0.1 \log x$ is a constant multiple of $\log x$, we can simplify the expression.
    have h_simplify : (fun x : ℝ => 1 / ((0.1 * Real.log x) * Real.log (0.1 * Real.log x))) =O[Filter.atTop] (fun x : ℝ => 1 / ((Real.log x) * Real.log (Real.log x))) := by
      rw [ Asymptotics.isBigO_iff ];
      -- Since $\log(0.1 \log x) = \log \log x + \log 0.1$, we can simplify the expression.
      have h_log_simplify : ∀ᶠ x in Filter.atTop, Real.log (0.1 * Real.log x) ≥ (1 / 2) * Real.log (Real.log x) := by
        have h_log_simplify : ∀ᶠ x in Filter.atTop, Real.log (0.1 * Real.log x) ≥ Real.log (Real.log x) - Real.log 10 := by
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ ← Real.log_div ( ne_of_gt <| Real.log_pos hx ) ( ne_of_gt <| by norm_num ) ] ; ring_nf; norm_num;
        have h_log_simplify : ∀ᶠ x in Filter.atTop, Real.log (Real.log x) ≥ 2 * Real.log 10 := by
          have h_log_simplify : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop := by
            exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop;
          exact h_log_simplify.eventually_ge_atTop _;
        filter_upwards [ ‹∀ᶠ x in Filter.atTop, Real.log ( 0.1 * Real.log x ) ≥ Real.log ( Real.log x ) - Real.log 10›, h_log_simplify ] with x hx₁ hx₂ using by linarith;
      refine' ⟨ 20, _ ⟩ ; filter_upwards [ h_log_simplify, Filter.eventually_gt_atTop 2, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃ ; rw [ Real.norm_of_nonneg, Real.norm_of_nonneg ] <;> norm_num at *;
      · rw [ inv_mul_eq_div, div_le_iff₀ ];
        · field_simp;
          rw [ div_le_div_iff₀ ] <;> ring_nf at * <;> norm_num at *;
          · nlinarith [ Real.log_pos ( show 1 < x by linarith ), Real.log_pos ( show 1 < Real.log x by rw [ Real.lt_log_iff_exp_lt ( by linarith ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ];
          · exact Real.log_pos <| by linarith [ Real.add_one_le_exp 1 ];
          · exact mul_pos ( Real.log_pos ( by linarith [ Real.add_one_le_exp 1 ] ) ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) );
        · exact lt_of_lt_of_le ( mul_pos ( by norm_num ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) hx₁;
      · exact mul_nonneg ( inv_nonneg.2 ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) ) ( inv_nonneg.2 ( Real.log_nonneg ( show 1 ≤ x from by linarith [ Real.add_one_le_exp 1 ] ) ) );
      · exact mul_nonneg ( inv_nonneg.mpr ( le_trans ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by linarith ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) ) hx₁ ) ) ( mul_nonneg ( inv_nonneg.mpr ( Real.log_nonneg ( by linarith ) ) ) ( by norm_num ) );
    refine' Asymptotics.IsBigO.trans _ ( h_tail_sum.trans h_simplify );
    rw [ Asymptotics.isBigO_iff ];
    exact ⟨ 1, Filter.eventually_atTop.mpr ⟨ 2, fun x hx => by rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ), Real.norm_of_nonneg ( tsum_nonneg fun _ => by positivity ) ] ; simpa using h_sum_bound x hx ⟩ ⟩

/-
For sufficiently large x, the sum of W/x for primes p in (0.1 log x, sqrt(2x)] is at most 1 / (log x log log x).
-/
lemma sum_W_div_x_bound (h : SieveAssumptions) :
  ∀ᶠ x in Filter.atTop,
    (∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (W_val x : ℝ) / x)
    ≤ 1 / (Real.log x * Real.log (Real.log x)) := by
      -- By `W_bound`, $W \le x^{0.25}$.
      have hW_le_x_0_25 : ∀ᶠ x in Filter.atTop, (W_val x : ℝ) ≤ Real.exp (0.25 * Real.log x) := by
        exact?;
      -- So sum $\le \sqrt{2} x^{0.5} x^{0.25} x^{-1} = \sqrt{2} x^{-0.25}$.
      have hsum_le_sqrt2_x_inv_0_25 : ∀ᶠ x in Filter.atTop,
        (∑ p ∈ Finset.filter (fun p : ℕ => 0.1 * Real.log x < p ∧ p ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (Real.exp (0.25 * Real.log x) : ℝ) / x) ≤ Real.sqrt 2 * x ^ (-0.25 : ℝ) := by
          have hsum_le_sqrt2_x_inv_0_25 : ∀ᶠ x in Filter.atTop, (∑ p ∈ Finset.filter (fun p : ℕ => 0.1 * Real.log x < p ∧ p ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (1 : ℝ)) ≤ Real.sqrt (2 * x) := by
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using le_trans ( le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( show Finset.filter ( fun p : ℕ => 0.1 * Real.log x < ( p : ℝ ) ∧ ( p : ℝ ) ≤ Real.sqrt ( 2 * x ) ∧ Nat.Prime p ) ( Finset.range ( ⌊Real.sqrt ( 2 * x ) ⌋₊ + 1 ) ) ⊆ Finset.Icc 1 ( ⌊Real.sqrt ( 2 * x ) ⌋₊ ) from fun p hp => Finset.mem_Icc.mpr ⟨ Nat.pos_of_ne_zero fun h => by norm_num [ h ] at hp, Nat.le_of_lt_succ <| Finset.mem_range.mp <| Finset.mem_filter.mp hp |>.1 ⟩ ) fun _ _ _ => by positivity ) <| by norm_num ) <| Nat.floor_le <| Real.sqrt_nonneg _;
          filter_upwards [ hsum_le_sqrt2_x_inv_0_25, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ ; norm_num [ Real.exp_mul, Real.exp_log hx₂ ] at *;
          convert mul_le_mul_of_nonneg_right hx₁ ( show 0 ≤ Real.exp ( 1 / 4 ) ^ Real.log x / x by positivity ) using 1 ; norm_num [ Real.rpow_def_of_pos, hx₂ ] ; ring;
          norm_num [ Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_neg, mul_assoc, mul_comm, mul_left_comm, hx₂.ne' ];
          rw [ Real.rpow_def_of_pos hx₂ ] ; ring;
          norm_num [ mul_assoc, ← Real.exp_add, ← Real.exp_neg ] ; ring;
          rw [ show Real.log x * ( -1 / 4 ) = Real.log x * ( 3 / 4 ) - Real.log x by ring, Real.exp_sub, Real.exp_log hx₂ ] ; ring;
      -- We want to show $\sqrt{2} x^{-0.25} \le 1 / (\log x \log \log x)$.
      -- This is equivalent to $\sqrt{2} \log x \log \log x \le x^{0.25}$.
      have h_sqrt2_log_log_le_x_0_25 : ∀ᶠ x in Filter.atTop,
        Real.sqrt 2 * Real.log x * Real.log (Real.log x) ≤ x ^ (0.25 : ℝ) := by
          -- We'll use that $\log x \log \log x$ grows much slower than $x^{0.25}$.
          have h_log_log_growth : Filter.Tendsto (fun x : ℝ => Real.log x * Real.log (Real.log x) / x ^ (0.25 : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $y = \log x$, therefore the expression becomes $\frac{y \log y}{e^{0.25 y}}$.
            suffices h_log : Filter.Tendsto (fun y : ℝ => y * Real.log y / Real.exp (0.25 * y)) Filter.atTop (nhds 0) by
              have := h_log.comp Real.tendsto_log_atTop;
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.rpow_def_of_pos hx ] ; ring );
            -- We can use the fact that $y \log y$ grows much slower than $e^{0.25 y}$.
            have h_log_growth : Filter.Tendsto (fun y : ℝ => y ^ 2 / Real.exp (0.25 * y)) Filter.atTop (nhds 0) := by
              -- Let $z = 0.25y$, therefore the expression becomes $\frac{(4z)^2}{e^z} = \frac{16z^2}{e^z}$.
              suffices h_z : Filter.Tendsto (fun z : ℝ => 16 * z^2 / Real.exp z) Filter.atTop (nhds 0) by
                convert h_z.comp ( Filter.tendsto_id.const_mul_atTop ( show ( 0 : ℝ ) < 0.25 by norm_num ) ) using 2 ; norm_num ; ring;
              simpa [ Real.exp_neg, mul_div_assoc ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2 |> Filter.Tendsto.const_mul 16;
            refine' squeeze_zero_norm' _ h_log_growth;
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( mul_nonneg ( by positivity ) ( Real.log_nonneg hx.le ) ) ( Real.exp_nonneg _ ) ) ] ; exact div_le_div_of_nonneg_right ( by nlinarith [ Real.log_le_sub_one_of_pos ( by positivity : 0 < x ) ] ) ( Real.exp_nonneg _ ) ;
          filter_upwards [ h_log_log_growth.eventually ( gt_mem_nhds <| show 0 < 1 / Real.sqrt 2 by positivity ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ using by rw [ div_lt_iff₀ ( by positivity ) ] at hx₁; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_div_cancel₀ ( 1 : ℝ ) ( ne_of_gt <| Real.sqrt_pos.mpr zero_lt_two ), Real.one_le_rpow hx₂.le ( show ( 0.25 : ℝ ) ≥ 0 by norm_num ) ] ;
      filter_upwards [ hW_le_x_0_25, hsum_le_sqrt2_x_inv_0_25, h_sqrt2_log_log_le_x_0_25, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃ hx₄ hx₅ ; refine le_trans ?_ ( hx₂.trans ?_ );
      · gcongr;
      · rw [ le_div_iff₀ ] <;> norm_num [ Real.rpow_neg ( by linarith : 0 ≤ x ) ] at *;
        · rw [ ← div_eq_mul_inv, div_mul_eq_mul_div, div_le_one ( by positivity ) ] ; linarith;
        · exact mul_pos ( Real.log_pos hx₄ ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) )

/-
failure_prob_sum(x) is the sum of (1/p^2 + W/x) for primes p in (0.1 log x, sqrt(2x)].
-/
def failure_prob_sum (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (1 / (p : ℝ)^2 + (W_val x : ℝ) / x)

/-
failure_prob_sum(x) is O(1/(log x log log x)).
-/
lemma failure_prob_sum_bound_O (h : SieveAssumptions) :
  failure_prob_sum =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
    -- Apply the sum_inv_sq_part_O lemma to conclude the proof.
    have h_sum_inv_sq_part_O : (fun x => ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), 1 / (p : ℝ)^2) =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
      exact?;
    have h_sum_W_div_x_bound : (fun x => ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (W_val x : ℝ) / x) =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
      refine' Asymptotics.IsBigO.of_bound 1 _;
      filter_upwards [ sum_W_div_x_bound h, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃;
      rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ), Real.norm_of_nonneg ( by exact one_div_nonneg.mpr ( mul_nonneg ( Real.log_nonneg hx₂.le ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) ) ) ] ; aesop;
    convert h_sum_inv_sq_part_O.add h_sum_W_div_x_bound using 2 ; norm_num [ failure_prob_sum ];
    norm_num [ Finset.sum_add_distrib ]

/-
If x = exp(C j / log j), then j <= (2/C) log x log log x for large j.
-/
lemma j_bound (C : ℝ) (hC : C > 0) :
  ∀ᶠ j in Filter.atTop,
    let x := Real.exp (C * j / Real.log j)
    j ≤ (2 / C) * Real.log x * Real.log (Real.log x) := by
      -- We'll use that $j \leq 2 * (\log x) * (\log (\log x)) / C$ simplifies to $j \leq 2 * j * (\log (\log x)) / (\log j)$.
      suffices h_simplified : ∀ᶠ (j : ℝ) in Filter.atTop,
          j ≤ 2 * j * (Real.log (Real.log (Real.exp (C * j / Real.log j)))) / Real.log j by
            filter_upwards [ h_simplified, Filter.eventually_gt_atTop 1 ] with j hj₁ hj₂ ; convert hj₁ using 1 ; ring_nf ; norm_num [ hC.ne', ne_of_gt, Real.log_pos hj₂ ] ;
            exact Or.inl ( by rw [ inv_mul_eq_div, div_eq_iff hC.ne' ] ; ring );
      -- Simplify the inequality to $1 \leq 2 * \log (C * j / \log j) / \log j$.
      suffices h_simplified : ∀ᶠ (j : ℝ) in Filter.atTop, 1 ≤ 2 * Real.log (C * j / Real.log j) / Real.log j by
        filter_upwards [ h_simplified, Filter.eventually_gt_atTop 1 ] with j hj₁ hj₂ using by rw [ Real.log_exp ] ; ring_nf at *; nlinarith;
      -- We'll use that $\log(Cj / \log j) \sim \log j$ as $j \to \infty$.
      have h_log : Filter.Tendsto (fun j => Real.log (C * j / Real.log j) / Real.log j) Filter.atTop (nhds 1) := by
        -- We can use the fact that $\log(Cj / \log j) = \log C + \log j - \log \log j$.
        suffices h_log : Filter.Tendsto (fun j => (Real.log C + Real.log j - Real.log (Real.log j)) / Real.log j) Filter.atTop (nhds 1) by
          refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with j hj using by rw [ Real.log_div ( by positivity ) ( by exact ne_of_gt ( Real.log_pos hj ) ), Real.log_mul ( by positivity ) ( by positivity ) ] );
        -- We can use the fact that $\frac{\log(\log j)}{\log j}$ tends to $0$ as $j$ tends to infinity.
        have h_log_log : Filter.Tendsto (fun j => Real.log (Real.log j) / Real.log j) Filter.atTop (nhds 0) := by
          -- Let $y = \log j$, therefore the expression becomes $\frac{\log y}{y}$.
          suffices h_log_y : Filter.Tendsto (fun y => Real.log y / y) Filter.atTop (nhds 0) by
            exact h_log_y.comp ( Real.tendsto_log_atTop );
          -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log(1/z)}{1/z} = -z \log z$.
          suffices h_log_z : Filter.Tendsto (fun z => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
            exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
        ring_nf;
        exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) ) ) ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) h_log_log ) ) ( by norm_num );
      filter_upwards [ h_log.eventually ( lt_mem_nhds <| show 1 > 1 / 2 by norm_num ) ] with j hj using by ring_nf at *; linarith;

/-
Define C_freq as the constant from lemma_freq.
-/
noncomputable def C_freq : ℝ := Classical.choose lemma_freq

lemma C_freq_pos : C_freq > 0 := (Classical.choose_spec lemma_freq).1

lemma C_freq_spec : ∀ (W q : ℕ) (b c : ℕ) (u L : ℕ),
    Nat.Coprime W q → L ≥ W →
    let I := Finset.Icc u (u + L - 1)
    let S := I.filter (fun n => n ≡ b [MOD W])
    let N_S := S.card
    let N_intersect := (S.filter (fun n => n ≡ c [MOD q])).card
    N_S > 0 →
    (N_intersect : ℝ) / N_S ≤ C_freq * (1 / (q : ℝ) + (W : ℝ) / L) := (Classical.choose_spec lemma_freq).2

/-
There exists a constant C such that for sufficiently large j, j * C_freq * failure_prob_sum(x) < 1, where x = exp(C j / log j).
-/
lemma exists_C_large_enough (h : SieveAssumptions) :
  ∃ C > 0, ∀ᶠ j in Filter.atTop,
    let x := Real.exp (C * j / Real.log j)
    (j : ℝ) * C_freq * failure_prob_sum x < 1 := by
      obtain ⟨K, hK_pos, hK_bound⟩ : ∃ K > 0, ∀ᶠ x in Filter.atTop, failure_prob_sum x ≤ K / (Real.log x * Real.log (Real.log x)) := by
        have := failure_prob_sum_bound_O h;
        rw [ Asymptotics.isBigO_iff' ] at this;
        simp +zetaDelta at *;
        obtain ⟨ c, hc₀, a, ha ⟩ := this; use c; exact ⟨ hc₀, Max.max a 3, fun x hx => le_of_abs_le <| by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, abs_mul, abs_inv, abs_of_nonneg ( Real.log_nonneg <| show 1 ≤ x by linarith [ le_max_left a 3, le_max_right a 3 ] ), abs_of_nonneg ( Real.log_nonneg <| show 1 ≤ Real.log x by rw [ Real.le_log_iff_exp_le <| by linarith [ le_max_left a 3, le_max_right a 3 ] ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ le_max_left a 3, le_max_right a 3 ] ) ] using ha x <| le_trans ( le_max_left a 3 ) hx ⟩ ;
      -- Choose $C$ such that $C > 2 K C_{freq}$.
      obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, C > 2 * K * C_freq := by
        exact ⟨ 2 * K * C_freq + 1, by nlinarith [ show 0 ≤ C_freq by exact le_of_lt ( C_freq_pos ) ], by linarith ⟩;
      -- By combining the results from hK_bound and j_bound, we can conclude that for sufficiently large j, the product is less than 1.
      use C, hC_pos
      have h_eventually : ∀ᶠ j in Filter.atTop, let x := Real.exp (C * j / Real.log j); j * C_freq * failure_prob_sum x ≤ 2 * K * C_freq / C := by
        have h_eventually : ∀ᶠ j in Filter.atTop, let x := Real.exp (C * j / Real.log j); j * C_freq * failure_prob_sum x ≤ j * C_freq * (K / (Real.log x * Real.log (Real.log x))) := by
          have h_eventually : ∀ᶠ j in Filter.atTop, let x := Real.exp (C * j / Real.log j); failure_prob_sum x ≤ K / (Real.log x * Real.log (Real.log x)) := by
            have h_eventually : Filter.Tendsto (fun j => Real.exp (C * j / Real.log j)) Filter.atTop Filter.atTop := by
              refine' Real.tendsto_exp_atTop.comp _;
              -- We can use the change of variables $u = \log j$ to transform the limit expression.
              suffices h_log : Filter.Tendsto (fun u => C * Real.exp u / u) Filter.atTop Filter.atTop by
                have := h_log.comp Real.tendsto_log_atTop;
                exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
              simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop hC_pos ( Real.tendsto_exp_div_pow_atTop 1 );
            exact hK_bound.filter_mono h_eventually;
          filter_upwards [ h_eventually, Filter.eventually_gt_atTop 0 ] with j hj₁ hj₂ using mul_le_mul_of_nonneg_left hj₁ <| mul_nonneg hj₂.le <| le_of_lt <| C_freq_pos;
        have h_eventually : ∀ᶠ j in Filter.atTop, let x := Real.exp (C * j / Real.log j); j * C_freq * (K / (Real.log x * Real.log (Real.log x))) ≤ 2 * K * C_freq / C := by
          have h_eventually : ∀ᶠ j in Filter.atTop, let x := Real.exp (C * j / Real.log j); j ≤ (2 / C) * Real.log x * Real.log (Real.log x) := by
            convert j_bound C hC_pos using 1;
          filter_upwards [ h_eventually, Filter.eventually_gt_atTop 1 ] with j hj₁ hj₂;
          field_simp at *;
          rw [ div_le_iff₀ ] <;> nlinarith [ show 0 < C_freq * K by exact mul_pos ( C_freq_pos ) hK_pos ];
        filter_upwards [ ‹∀ᶠ j in Filter.atTop, let x := Real.exp ( C * j / Real.log j ) ; j * C_freq * failure_prob_sum x ≤ j * C_freq * ( K / ( Real.log x * Real.log ( Real.log x ) ) ) ›, h_eventually ] with j hj₁ hj₂ using le_trans hj₁ hj₂;
      filter_upwards [ h_eventually ] with j hj using lt_of_le_of_lt hj ( by rw [ div_lt_iff₀ ] <;> linarith )

/-
failure_prob_sum_2(x) is the sum of (1/p^2 + 2W/x) for primes p in (0.1 log x, sqrt(2x)].
-/
def failure_prob_sum_2 (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (1 / (p : ℝ)^2 + 2 * (W_val x : ℝ) / x)

/-
failure_prob_sum_general(x, K) is the sum of (1/p^2 + K*W/x) for primes p in (0.1 log x, sqrt(2x)].
-/
def failure_prob_sum_general (x : ℝ) (K : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (1 / (p : ℝ)^2 + K * (W_val x : ℝ) / x)

/-
failure_prob_sum_2(x) is O(1/(log x log log x)).
-/
lemma failure_prob_sum_2_bound_O (h : SieveAssumptions) :
  failure_prob_sum_2 =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
    have h_failure_prob_sum_2 : failure_prob_sum_2 =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
      have h_sum_inv_sq : (fun x => ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (1 / (p : ℝ)^2)) =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
        convert sum_inv_sq_part_O h using 1
      have h_sum_W_div_x : (fun x => ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (W_val x : ℝ) / x) =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
        have := sum_W_div_x_bound h;
        rw [ Asymptotics.isBigO_iff ];
        exact ⟨ 1, by filter_upwards [ this, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃ using by rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ), Real.norm_of_nonneg ( one_div_nonneg.mpr <| mul_nonneg ( Real.log_nonneg <| by linarith ) <| Real.log_nonneg <| by exact Real.le_log_iff_exp_le ( by linarith ) |>.2 <| by linarith ) ] ; simpa using hx₁ ⟩
      have h_sum_W_div_x : (fun x => ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (2 * (W_val x : ℝ) / x)) =O[Filter.atTop] (fun x => 1 / (Real.log x * Real.log (Real.log x))) := by
        convert h_sum_W_div_x.const_mul_left 2 using 2 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      convert h_sum_inv_sq.add h_sum_W_div_x using 1;
      exact funext fun x => by rw [ ← Finset.sum_add_distrib ] ; rfl;
    exact h_failure_prob_sum_2

/-
There exists a constant C such that for sufficiently large j, j * C_freq * failure_prob_sum_2(x) < 1, where x = exp(C j / log j).
-/
lemma exists_C_large_enough_2 (h : SieveAssumptions) :
  ∃ C > 0, ∀ᶠ j in Filter.atTop,
    let x := Real.exp (C * j / Real.log j)
    (j : ℝ) * C_freq * failure_prob_sum_2 x < 1 := by
      -- We want $j \cdot C_{freq} \cdot \text{failure\_prob\_sum\_2}(x) < 1$.
      -- $j \le (2/C) \log x \log \log x$.
      -- $\text{failure\_prob\_sum\_2}(x) \le K / (\log x \log \log x)$.
      -- Product $\le (2/C) C_{freq} K$.
      -- Choose $C > 2 C_{freq} K$.
      obtain ⟨K, hK⟩ : ∃ K > 0, ∀ᶠ x in Filter.atTop, failure_prob_sum_2 x ≤ K / (Real.log x * Real.log (Real.log x)) := by
        have := failure_prob_sum_2_bound_O h;
        rw [ Asymptotics.isBigO_iff' ] at this;
        obtain ⟨ K, hK₀, hK ⟩ := this; refine' ⟨ K, hK₀, _ ⟩ ; filter_upwards [ hK, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃ ; rw [ Real.norm_of_nonneg ( show 0 ≤ failure_prob_sum_2 x from Finset.sum_nonneg fun _ _ => by positivity ), Real.norm_of_nonneg ( show 0 ≤ 1 / ( Real.log x * Real.log ( Real.log x ) ) from one_div_nonneg.mpr <| mul_nonneg ( Real.log_nonneg <| by linarith ) <| Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le ] <;> linarith ) ] at hx₁ ; ring_nf at * ; aesop;
      -- Choose $C > 2 C_{freq} K$.
      obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, 2 * C_freq * K / C < 1 := by
        exact ⟨ 2 * C_freq * K + 1, by nlinarith [ show 0 < C_freq by exact C_freq_pos ], by rw [ div_lt_iff₀ ] <;> nlinarith [ show 0 < C_freq by exact C_freq_pos ] ⟩;
      use C;
      -- For sufficiently large j, we have j * C_freq * failure_prob_sum_2(x) ≤ j * C_freq * (K / (log x * log log x)).
      have h_bound : ∀ᶠ j in Filter.atTop, let x := Real.exp (C * j / Real.log j);
        j * C_freq * failure_prob_sum_2 x ≤ j * C_freq * (K / (Real.log x * Real.log (Real.log x))) := by
          have h_bound : ∀ᶠ j in Filter.atTop, let x := Real.exp (C * j / Real.log j); failure_prob_sum_2 x ≤ K / (Real.log x * Real.log (Real.log x)) := by
            have h_bound : Filter.Tendsto (fun j => Real.exp (C * j / Real.log j)) Filter.atTop Filter.atTop := by
              refine' Real.tendsto_exp_atTop.comp _;
              -- We can use the change of variables $u = \log j$ to transform the limit expression.
              suffices h_log : Filter.Tendsto (fun u => C * Real.exp u / u) Filter.atTop Filter.atTop by
                have := h_log.comp Real.tendsto_log_atTop;
                exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
              simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop hC_pos ( Real.tendsto_exp_div_pow_atTop 1 );
            exact hK.2.filter_mono h_bound;
          filter_upwards [ h_bound, Filter.eventually_gt_atTop 0 ] with j hj₁ hj₂ using mul_le_mul_of_nonneg_left hj₁ <| mul_nonneg hj₂.le <| le_of_lt <| C_freq_pos;
      -- For sufficiently large j, we have j * C_freq * (K / (log x * log log x)) ≤ (2/C) * C_freq * K.
      have h_final_bound : ∀ᶠ j in Filter.atTop, let x := Real.exp (C * j / Real.log j);
        j * C_freq * (K / (Real.log x * Real.log (Real.log x))) ≤ (2 / C) * C_freq * K := by
          have h_final_bound : ∀ᶠ j in Filter.atTop, let x := Real.exp (C * j / Real.log j);
            j ≤ (2 / C) * Real.log x * Real.log (Real.log x) := by
              exact?;
          filter_upwards [ h_final_bound, Filter.eventually_gt_atTop 1 ] with j hj₁ hj₂;
          field_simp;
          rw [ div_le_iff₀ ] <;> norm_num at *;
          · convert mul_le_mul_of_nonneg_left hj₁ ( show 0 ≤ C_freq * K * C by exact mul_nonneg ( mul_nonneg ( le_of_lt ( C_freq_pos ) ) hK.1.le ) hC_pos.le ) using 1 <;> ring;
            norm_num [ sq, mul_assoc, mul_comm C, hC_pos.ne' ];
          · ring_nf at *;
            nlinarith [ inv_pos.mpr hC_pos, inv_pos.mpr ( Real.log_pos hj₂ ), mul_inv_cancel₀ hC_pos.ne', mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hj₂ ) ) ];
      exact ⟨ hC_pos, by filter_upwards [ h_bound, h_final_bound ] with j hj₁ hj₂ using lt_of_le_of_lt hj₁ ( lt_of_le_of_lt hj₂ ( by ring_nf at *; linarith ) ) ⟩

/-
If the probabilistic condition holds, there exists a valid n in the interval [x/2, x] such that n+a is squarefree for all a in A.
-/
lemma exists_good_n_of_bound (x : ℝ) (hx : x ≥ 100) (W : ℕ) (hW : W = W_val x) (b : ℕ) (A : Finset ℕ)
    (hA_subset : ∀ a ∈ A, a ≤ x)
    (hA_admissible : ∀ p, p ∣ W → ∀ a ∈ A, a % p^2 ≠ b % p^2)
    (hL : Nat.floor x - Nat.ceil (x / 2) + 1 ≥ W)
    (h_prob : (A.card : ℝ) * C_freq * failure_prob_sum_2 x < 1) :
    ∃ n ∈ Finset.Icc (Nat.ceil (x / 2)) (Nat.floor x), (n + b) % W = 0 ∧ ∀ a ∈ A, Squarefree (n + a) := by
      contrapose! hA_admissible;
      refine' ⟨ 1, _, _ ⟩ <;> norm_num;
      rcases A.eq_empty_or_nonempty with ( rfl | ⟨ a, ha ⟩ ) <;> simp_all +decide [ Nat.mod_one ];
      · -- Let's choose any $n$ in the interval $[x/2, x]$ such that $n + b$ is divisible by $W_val x$.
        obtain ⟨n, hn⟩ : ∃ n ∈ Finset.Icc (Nat.ceil (x / 2)) (Nat.floor x), (n + b) % W_val x = 0 := by
          -- By the pigeonhole principle, since the length of the interval is at least W_val x - 1, there must be at least one multiple of W_val x in this interval.
          have h_pigeonhole : ∃ k : ℕ, ⌈x / 2⌉₊ ≤ k * W_val x - b ∧ k * W_val x - b ≤ ⌊x⌋₊ := by
            use (⌈x / 2⌉₊ + b + W_val x - 1) / W_val x;
            constructor;
            · exact le_tsub_of_add_le_left ( by linarith [ Nat.div_add_mod ( ⌈x / 2⌉₊ + b + W_val x - 1 ) ( W_val x ), Nat.mod_lt ( ⌈x / 2⌉₊ + b + W_val x - 1 ) ( show W_val x > 0 from Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2 ), Nat.sub_add_cancel ( show 1 ≤ ⌈x / 2⌉₊ + b + W_val x from by linarith [ Nat.ceil_pos.mpr ( show 0 < x / 2 by positivity ), show 0 < W_val x from Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2 ] ) ] );
            · rw [ tsub_le_iff_left ];
              exact le_trans ( Nat.div_mul_le_self _ _ ) ( by rw [ tsub_le_iff_right ] ; linarith [ Nat.sub_add_cancel ( show ⌈x / 2⌉₊ ≤ ⌊x⌋₊ from Nat.ceil_le.mpr <| by linarith [ Nat.lt_floor_add_one x ] ) ] );
          cases' h_pigeonhole with k hk;
          use k * W_val x - b;
          rw [ Nat.sub_add_cancel ];
          · aesop;
          · exact le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith [ Nat.ceil_pos.mpr ( show 0 < x / 2 by positivity ) ] ) );
        exact hA_admissible n ( Nat.le_of_ceil_le ( Finset.mem_Icc.mp hn.1 |>.1 ) ) ( Finset.mem_Icc.mp hn.1 |>.2 ) hn.2;
      · use a

/-
For any admissible set A and real x, there exists an integer b such that for all prime factors p of W_val(x), A avoids the residue class b mod p^2.
-/
lemma admissible_to_b (A : Set ℕ) (hA : Admissible A) (W : ℕ) (hW : Squarefree W) :
    ∃ b, ∀ p, p ∣ W → Nat.Prime p → ∀ a ∈ A, a % p^2 ≠ b % p^2 := by
      choose! b hb using hA;
      -- By the Chinese Remainder Theorem, there exists a unique $b$ modulo $W$ such that $b \equiv b_p \pmod{p^2}$ for each prime $p$ dividing $W$.
      have h_crt : ∃ b₀ : ℕ, ∀ p : ℕ, p ∣ W → Nat.Prime p → b₀ ≡ b p [MOD p^2] := by
        have h_crt : ∀ p ∈ Nat.primeFactors W, ∃ x, x ≡ b p [MOD p^2] ∧ ∀ q ∈ Nat.primeFactors W, q ≠ p → x ≡ 0 [MOD q^2] := by
          -- For each prime $p$ dividing $W$, let $y_p$ be the multiplicative inverse of $\prod_{q \neq p} q^2$ modulo $p^2$.
          intros p hp
          obtain ⟨y_p, hy_p⟩ : ∃ y_p, y_p * (∏ q ∈ Nat.primeFactors W \ {p}, q^2) ≡ 1 [MOD p^2] := by
            have h_coprime : Nat.gcd (∏ q ∈ Nat.primeFactors W \ {p}, q^2) (p^2) = 1 := by
              simp_all +decide [ Nat.coprime_prod_left_iff, Nat.coprime_prod_right_iff ];
              exact fun q hq hq' hq'' => hq.coprime_iff_not_dvd.mpr fun h => hq'' <| Nat.prime_dvd_prime_iff_eq hq hp.1 |>.1 h;
            have := Nat.exists_mul_emod_eq_one_of_coprime h_coprime;
            simpa only [ mul_comm, Nat.ModEq, Nat.mod_eq_of_lt ( show 1 < p ^ 2 from one_lt_pow₀ ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) two_ne_zero ) ] using this ( one_lt_pow₀ ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) two_ne_zero );
          use y_p * (∏ q ∈ Nat.primeFactors W \ {p}, q^2) * b p;
          exact ⟨ by simpa using hy_p.mul_right _, fun q hq hqp => Nat.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩;
        choose! x hx₁ hx₂ using h_crt;
        use ∑ p ∈ Nat.primeFactors W, x p; intro p hp hp'; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
        rw [ Finset.sum_eq_single p ] <;> aesop;
      exact ⟨ h_crt.choose, fun p hp hp' a ha => by have := hb p hp'; have := h_crt.choose_spec p hp hp'; simp_all +decide [ Nat.ModEq, Nat.mod_eq_of_lt ] ⟩

/-
For any admissible set A and real x, there exists an integer b such that for all prime factors p of W_val(x), A avoids the residue class b mod p^2.
-/
lemma admissible_to_b_W_val (A : Set ℕ) (hA : Admissible A) (x : ℝ) :
    ∃ b, ∀ p, p ∣ W_val x → Nat.Prime p → ∀ a ∈ A, a % p^2 ≠ b % p^2 := by
      obtain ⟨W, hW⟩ : ∃ W : ℕ, Squarefree W ∧ ∀ p, p ∣ W_val x → Nat.Prime p → p ∣ W := by
        use ∏ p ∈ Nat.primeFactors ( W_val x ), p;
        rw [ Nat.squarefree_iff_prime_squarefree ];
        constructor;
        · intro p pp dp; rw [ Finset.prod_eq_prod_diff_singleton_mul <| Nat.mem_primeFactors.mpr ⟨ pp, ?_, ?_ ⟩ ] at dp <;> norm_num at *;
          · rw [ Nat.mul_dvd_mul_iff_right pp.pos ] at dp;
            simp_all +decide [ Nat.Prime.dvd_iff_not_coprime pp, Nat.coprime_prod_right_iff ];
            obtain ⟨ q, hq₁, hq₂, hq₃, hq₄, hq₅ ⟩ := dp; have := Nat.coprime_primes pp hq₁; aesop;
          · exact dvd_trans ( dvd_of_mul_left_dvd dp ) ( Nat.prod_primeFactors_dvd _ );
          · exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop;
        · exact fun p hp hp' => Finset.dvd_prod_of_mem _ <| Nat.mem_primeFactors.mpr ⟨ hp', hp, by unfold W_val; exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero 2 <| Nat.Prime.ne_zero <| by aesop ⟩;
      obtain ⟨ b, hb ⟩ := admissible_to_b A hA W hW.1;
      exact ⟨ b, fun p hp hp' a ha => hb p ( hW.2 p hp hp' ) hp' a ha ⟩

/-
The function 1 / (log x log log x) is decreasing for sufficiently large x.
-/
def bound_func (x : ℝ) : ℝ := 1 / (Real.log x * Real.log (Real.log x))

lemma bound_func_decreasing : ∀ᶠ x in Filter.atTop, ∀ y, x ≤ y → bound_func y ≤ bound_func x := by
  unfold bound_func;
  filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx;
  intro y hy; gcongr;
  any_goals nlinarith [ Real.add_one_le_exp 1, Real.log_exp 1, Real.log_lt_log ( by positivity ) hx ];
  · exact mul_pos ( Real.log_pos ( lt_trans ( by norm_num ) hx ) ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) );
  · exact Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by linarith [ Real.exp_pos 1 ] ) ] ; linarith [ Real.add_one_le_exp 1 ] );
  · exact Real.log_nonneg ( by linarith [ Real.add_one_le_exp 1 ] )

/-
There exists a constant C such that for sufficiently large j, if x >= exp(C j / log j), then j * C_freq * failure_prob_sum_2(x) < 1.
-/
lemma prob_condition_of_growth (h : SieveAssumptions) :
  ∃ C > 0, ∀ᶠ j in Filter.atTop,
    ∀ x, x ≥ Real.exp (C * j / Real.log j) →
    (j : ℝ) * C_freq * failure_prob_sum_2 x < 1 := by
      -- We know `failure_prob_sum_2` is $O(\text{bound\_func})$.
      have h_bound : ∃ K > 0, ∀ᶠ x in Filter.atTop, failure_prob_sum_2 x ≤ K * bound_func x := by
        obtain ⟨ K, hK ⟩ := Asymptotics.isBigO_iff.mp ( failure_prob_sum_2_bound_O h );
        refine' ⟨ Max.max K 1, by positivity, _ ⟩;
        filter_upwards [ hK, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃;
        refine' le_trans ( le_abs_self _ ) ( le_trans hx₁ _ );
        rw [ Real.norm_of_nonneg ( one_div_nonneg.mpr ( mul_nonneg ( Real.log_nonneg hx₂.le ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) ) ) ] ; exact mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( one_div_nonneg.mpr ( mul_nonneg ( Real.log_nonneg hx₂.le ) ( Real.log_nonneg ( show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) ) );
      -- Let $x_{min}(j) = \exp(C j / \log j)$.
      obtain ⟨K, hK_pos, hK_bound⟩ := h_bound
      obtain ⟨C, hC_pos, hC_bound⟩ : ∃ C > 0, ∀ᶠ j in Filter.atTop, j * C_freq * (K * bound_func (Real.exp (C * j / Real.log j))) < 1 := by
        -- Choose $C$ such that $C > C_{freq} \cdot K$.
        obtain ⟨C, hC_pos, hC_bound⟩ : ∃ C > 0, C > C_freq * K := by
          exact ⟨ Max.max ( C_freq * K + 1 ) 1, by positivity, by linarith [ le_max_left ( C_freq * K + 1 ) 1, le_max_right ( C_freq * K + 1 ) 1 ] ⟩;
        -- For large $j$, $\log(C j / \log j) \approx \log j$.
        have h_log_approx : Filter.Tendsto (fun j => Real.log (C * j / Real.log j) / Real.log j) Filter.atTop (nhds 1) := by
          -- We can use the fact that $\log(Cj / \log j) = \log C + \log j - \log \log j$.
          suffices h_log_simplified : Filter.Tendsto (fun j => (Real.log C + Real.log j - Real.log (Real.log j)) / Real.log j) Filter.atTop (nhds 1) by
            refine h_log_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with j hj using by rw [ Real.log_div ( by positivity ) ( by exact ne_of_gt ( Real.log_pos hj ) ), Real.log_mul ( by positivity ) ( by positivity ) ] );
          -- We can use the fact that $\frac{\log \log j}{\log j} \to 0$ as $j \to \infty$.
          have h_log_log : Filter.Tendsto (fun j => Real.log (Real.log j) / Real.log j) Filter.atTop (nhds 0) := by
            -- Let $y = \log j$, therefore the expression becomes $\frac{\log y}{y}$.
            suffices h_log_y : Filter.Tendsto (fun y => Real.log y / y) Filter.atTop (nhds 0) by
              exact h_log_y.comp ( Real.tendsto_log_atTop );
            -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
            suffices h_log_z : Filter.Tendsto (fun z => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
              exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
          ring_nf;
          exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) ) ) ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) h_log_log ) ) ( by norm_num );
        -- Using the approximation, we get $\text{bound\_func}(x_{min}(j)) \approx 1 / (C j)$.
        have h_bound_func_approx : Filter.Tendsto (fun j => j * bound_func (Real.exp (C * j / Real.log j))) Filter.atTop (nhds (1 / C)) := by
          have h_bound_func_approx : Filter.Tendsto (fun j => j / ((C * j / Real.log j) * Real.log (C * j / Real.log j))) Filter.atTop (nhds (1 / C)) := by
            convert h_log_approx.inv₀ ( by positivity ) |> Filter.Tendsto.const_mul ( 1 / C ) using 2 <;> ring;
            by_cases h : ‹ℝ› = 0 <;> aesop;
          convert h_bound_func_approx using 2 ; unfold bound_func ; norm_num ; ring;
          norm_num ; ring;
        have := h_bound_func_approx.const_mul ( C_freq * K );
        exact ⟨ C, hC_pos, by filter_upwards [ this.eventually ( gt_mem_nhds <| show C_freq * K * ( 1 / C ) < 1 by rw [ mul_one_div, div_lt_iff₀ ] <;> linarith ) ] with j hj using by linarith ⟩;
      -- By combining the results from hK_bound and hC_bound, we can conclude the proof.
      have h_final : ∀ᶠ j in Filter.atTop, ∀ x ≥ Real.exp (C * j / Real.log j), failure_prob_sum_2 x ≤ K * bound_func (Real.exp (C * j / Real.log j)) := by
        have h_final : ∀ᶠ j in Filter.atTop, ∀ x ≥ Real.exp (C * j / Real.log j), failure_prob_sum_2 x ≤ K * bound_func x := by
          have h_final : ∀ᶠ j in Filter.atTop, Real.exp (C * j / Real.log j) ≥ Classical.choose (Filter.eventually_atTop.mp hK_bound) := by
            have h_final : Filter.Tendsto (fun j => Real.exp (C * j / Real.log j)) Filter.atTop Filter.atTop := by
              refine' Real.tendsto_exp_atTop.comp _;
              -- We can use the change of variables $u = \log j$ to transform the limit expression.
              suffices h_log : Filter.Tendsto (fun u => C * Real.exp u / u) Filter.atTop Filter.atTop by
                have := h_log.comp Real.tendsto_log_atTop;
                exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
              simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop hC_pos ( Real.tendsto_exp_div_pow_atTop 1 );
            exact h_final.eventually_ge_atTop _;
          filter_upwards [ h_final ] with j hj using fun x hx => Classical.choose_spec ( Filter.eventually_atTop.mp hK_bound ) x ( le_trans hj hx );
        have h_final : ∀ᶠ x in Filter.atTop, ∀ y, x ≤ y → bound_func y ≤ bound_func x := by
          apply bound_func_decreasing;
        obtain ⟨x₀, hx₀⟩ : ∃ x₀, ∀ x ≥ x₀, ∀ y, x ≤ y → bound_func y ≤ bound_func x := by
          exact Filter.eventually_atTop.mp h_final;
        have h_final : ∀ᶠ j in Filter.atTop, Real.exp (C * j / Real.log j) ≥ x₀ := by
          have h_final : Filter.Tendsto (fun j => Real.exp (C * j / Real.log j)) Filter.atTop Filter.atTop := by
            have h_exp_growth : Filter.Tendsto (fun j => C * j / Real.log j) Filter.atTop Filter.atTop := by
              have h_exp_growth : Filter.Tendsto (fun j => j / Real.log j) Filter.atTop Filter.atTop := by
                -- We can use the change of variables $u = \log j$ to transform the limit expression.
                suffices h_log : Filter.Tendsto (fun u => Real.exp u / u) Filter.atTop Filter.atTop by
                  have := h_log.comp Real.tendsto_log_atTop;
                  exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
                simpa using Real.tendsto_exp_div_pow_atTop 1;
              simpa only [ mul_div_assoc ] using h_exp_growth.const_mul_atTop hC_pos;
            exact Real.tendsto_exp_atTop.comp h_exp_growth;
          exact h_final.eventually_ge_atTop x₀;
        filter_upwards [ h_final, ‹∀ᶠ j in Filter.atTop, ∀ x ≥ Real.exp ( C * j / Real.log j ), failure_prob_sum_2 x ≤ K * bound_func x› ] with j hj₁ hj₂ using fun x hx => le_trans ( hj₂ x hx ) ( mul_le_mul_of_nonneg_left ( hx₀ _ hj₁ _ hx ) hK_pos.le );
      use C, hC_pos;
      filter_upwards [ hC_bound, h_final, Filter.eventually_gt_atTop 0 ] with j hj₁ hj₂ hj₃ using fun x hx => lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( hj₂ x hx ) ( by exact mul_nonneg ( by positivity ) ( by exact le_of_lt ( show 0 < C_freq from C_freq_pos ) ) ) ) hj₁

/-
The function j * bound_func(exp(C j / log j)) tends to 1/C as j goes to infinity.
-/
lemma bound_func_growth_asymptotics (C : ℝ) (hC : C > 0) :
  Filter.Tendsto (fun j => j * bound_func (Real.exp (C * j / Real.log j))) Filter.atTop (nhds (1 / C)) := by
    unfold bound_func;
    -- Simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun j => 1 / (C * (1 + (Real.log C - Real.log (Real.log j)) / Real.log j))) Filter.atTop (nhds (1 / C)) by
      refine h_simplify.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with j hj₁ hj₂;
      field_simp;
      rw [ one_add_div, div_div_eq_mul_div ] <;> norm_num [ ne_of_gt, Real.log_pos, hj₁, hj₂ ];
      rw [ Real.log_div ( by positivity ) ( by linarith [ Real.log_pos hj₁ ] ), Real.log_mul ( by positivity ) ( by linarith [ Real.log_pos hj₁ ] ) ] ; ring;
      grind;
    -- We'll use the fact that $\frac{\log \log j}{\log j}$ tends to $0$ as $j$ tends to infinity.
    have h_log_log : Filter.Tendsto (fun j => Real.log (Real.log j) / Real.log j) Filter.atTop (nhds 0) := by
      -- Let $y = \log j$, therefore the expression becomes $\frac{\log y}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y => Real.log y / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop );
      -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
      suffices h_log_z : Filter.Tendsto (fun z => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
      norm_num +zetaDelta at *;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    norm_num [ sub_div ];
    exact le_trans ( Filter.Tendsto.mul ( Filter.Tendsto.inv₀ ( tendsto_const_nhds.add ( Filter.Tendsto.sub ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) h_log_log ) ) ( by norm_num ) ) tendsto_const_nhds ) ( by norm_num )

/-
Eventually, j * A * bound_func(x_min(j)) < target, provided A/C < target.
-/
lemma bound_func_xmin_bound (C : ℝ) (hC : C > 0) (A : ℝ) (hA : A > 0) (target : ℝ) (htarget : A / C < target) :
  ∀ᶠ j in Filter.atTop, j * A * bound_func (Real.exp (C * j / Real.log j)) < target := by
    -- By the properties of limits, if $A/C < target$, then there exists a $j_0$ such that for all $j \geq j_0$, $j * A * bound_func(exp(C*j/log j)) < target$.
    have h_limit : Filter.Tendsto (fun j => j * A * bound_func (Real.exp (C * j / Real.log j))) Filter.atTop (nhds (A / C)) := by
      convert Filter.Tendsto.const_mul A ( bound_func_growth_asymptotics C hC ) using 2 ; ring;
      ring;
    exact h_limit.eventually ( gt_mem_nhds htarget )

/-
There exists a constant C such that for sufficiently large j, if x >= exp(C j / log j), then j * C_freq * failure_prob_sum_2(x) < 1.
-/
lemma prob_condition_of_growth_v2 (h : SieveAssumptions) :
  ∃ C > 0, ∀ᶠ j in Filter.atTop,
    ∀ x, x ≥ Real.exp (C * j / Real.log j) →
    (j : ℝ) * C_freq * failure_prob_sum_2 x < 1 := by

      apply_mod_cast prob_condition_of_growth h
