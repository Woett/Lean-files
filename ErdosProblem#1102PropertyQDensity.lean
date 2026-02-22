/-
We say that a sequence of positive integers $A$ has:

- property $P$ if, for all positive integers $n$, there are only finitely many $a \in A$ such that $n+a$ is squarefree.
- property $Q$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$ with $a < n$.
- property $\overline{P}$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$.
- property $\overline{P}_\infty$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all but finitely many $a \in A$.

Solving Erdős Problem #1102 (https://www.erdosproblems.com/1102), Terence Tao and I managed to prove tight bounds on the possible densities of sequences with one of the above properties.

W. van Doorn and T. Tao, Growth rates of sequences governed by the squarefree properties of their translates. arXiv:2512.01087 (2025).

Thanks to Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), the proof of the following theorem is formalized in the Lean file below:

Any sequence with property $Q$ has upper density at most $6/\pi^2$. On the other hand, sequences with property $Q$ exist which have natural density equal to $6/\pi^2$.

At the very end you can find the (relevant parts of the) statement of Erdős Problem #1102 taken from the Formal Conjectures project by Google DeepMind, which we also prove. 

https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1102.lean

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

open Squarefree Set Order Filter Topology

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
SF is the set of squarefree numbers.
-/
def SF : Set ℕ := {n | Squarefree n}

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
The upper density of a set A of natural numbers.
-/
def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

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
If A is a subset of a periodic set B with period M, then the upper density of A is at most the density of B in one period.
-/
lemma density_of_subset_periodic (A B : Set ℕ) (M : ℕ) (hM : M > 0) (hB_per : ∀ n, n ∈ B ↔ n + M ∈ B) (hsub : A ⊆ B) :
  upperDensity A ≤ ((B ∩ Set.Icc 1 M).ncard : ℝ) / M := by
    field_simp;
    refine' le_trans ( mul_le_mul_of_nonneg_right ( show upperDensity A ≤ upperDensity ( B ) from _ ) ( Nat.cast_nonneg _ ) ) _;
    · apply_rules [ Filter.limsup_le_limsup ];
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using div_le_div_of_nonneg_right ( mod_cast Set.ncard_le_ncard <| Set.inter_subset_inter_left _ hsub ) <| Nat.cast_nonneg _;
      · refine' ⟨ 0, fun x hx => _ ⟩ ; norm_num at *;
        exact le_trans ( by positivity ) ( hx.choose_spec _ le_rfl ) |> le_trans <| by norm_num;
      · use 1; norm_num [ Filter.IsBoundedUnder ];
        exact ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ) <| by positivity ⟩;
    · -- Since B is periodic with period M, its natural density exists and is equal to the density in one period, which is |B ∩ [1, M]| / M.
      have hB_nat_density : HasNaturalDensity B ((B ∩ Set.Icc 1 M).ncard / M : ℝ) := by
        -- Since B is periodic with period M, the number of elements of B in [1, N] is approximately (N/M) times the number of elements of B in [1, M].
        have hB_card : ∀ N : ℕ, ((B ∩ Set.Icc 1 N).ncard : ℝ) ≤ (N / M) * ((B ∩ Set.Icc 1 M).ncard : ℝ) + M := by
          intro N
          have hB_card : ((B ∩ Set.Icc 1 N).ncard : ℝ) ≤ ((N / M) * ((B ∩ Set.Icc 1 M).ncard : ℝ)) + M := by
            have hB_card_period : ∀ k : ℕ, ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) ≤ k * ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
              intro k
              have hB_card_period : ∀ k : ℕ, ((B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
                intro k
                have hB_card_period : ∀ k : ℕ, ((B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
                  intro k
                  have hB_card_period : (B ∩ Set.Icc (k * M + 1) ((k + 1) * M)) ⊆ (fun n => n + k * M) '' (B ∩ Set.Icc 1 M) := by
                    intro n hn; use n - k * M; norm_num at *; constructor;
                    · have hB_card_period : ∀ k : ℕ, ∀ n ∈ B, n ≥ k * M + 1 → n - k * M ∈ B := by
                        intro k n hn hn'; induction' k with k ih generalizing n <;> norm_num at *;
                        · assumption;
                        · convert ih ( n - M ) ( by rw [ hB_per ] ; exact by rw [ Nat.sub_add_cancel ( by nlinarith ) ] ; exact hn ) ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : M ≤ n ) ] ) using 1 ; rw [ Nat.sub_sub ] ; ring_nf;
                      exact ⟨ hB_card_period k n hn.1 hn.2.1, Nat.sub_pos_of_lt hn.2.1, by linarith ⟩;
                    · rw [ Nat.sub_add_cancel ( by linarith ) ]
                  have hB_card_period : (B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard ≤ ((fun n => n + k * M) '' (B ∩ Set.Icc 1 M)).ncard := by
                    apply_rules [ Set.ncard_le_ncard ];
                    exact Set.Finite.image _ ( Set.finite_iff_bddAbove.mpr ⟨ M, fun x hx => hx.2.2 ⟩ );
                  rw [ Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy ] at hB_card_period ; exact_mod_cast hB_card_period;
                exact hB_card_period k;
              induction' k with k ih;
              · norm_num [ Set.ncard_eq_toFinset_card' ];
              · have hB_card_period : ((B ∩ Set.Icc 1 ((k + 1) * M)).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) + ((B ∩ Set.Icc (k * M + 1) ((k + 1) * M)).ncard : ℝ) := by
                  norm_cast;
                  convert Set.ncard_union_le _ _ using 2 ; ext ; norm_num ; ring_nf;
                  grind;
                grind
            have hB_card_bound : ((B ∩ Set.Icc 1 N).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 ((N / M + 1) * M)).ncard : ℝ) := by
              fapply Nat.cast_le.mpr;
              apply Set.ncard_le_ncard;
              · exact Set.inter_subset_inter_right _ ( Set.Icc_subset_Icc_right ( by nlinarith [ Nat.div_add_mod N M, Nat.mod_lt N hM ] ) );
              · exact Set.finite_iff_bddAbove.mpr ⟨ _, fun x hx => hx.2.2 ⟩;
            refine le_trans hB_card_bound <| le_trans ( hB_card_period _ ) ?_;
            field_simp;
            norm_cast; nlinarith [ Nat.div_mul_le_self N M, show ( B ∩ Set.Icc 1 M ).ncard ≤ M from le_trans ( Set.ncard_le_ncard ( show B ∩ Set.Icc 1 M ⊆ Set.Icc 1 M from fun x hx => hx.2 ) ) ( by simp +decide [ Set.ncard_eq_toFinset_card' ] ) ] ;
          convert hB_card using 1;
        have hB_card_lower : ∀ N : ℕ, ((B ∩ Set.Icc 1 N).ncard : ℝ) ≥ (N / M) * ((B ∩ Set.Icc 1 M).ncard : ℝ) - M := by
          intro N
          have hB_card_lower_step : ∀ k : ℕ, ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) ≥ k * ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
            intro k
            have hB_card_lower_step : ((B ∩ Set.Icc 1 (k * M)).ncard : ℝ) = ∑ i ∈ Finset.range k, ((B ∩ Set.Icc (i * M + 1) ((i + 1) * M)).ncard : ℝ) := by
              induction' k with k ih;
              · norm_num [ Set.ncard_eq_toFinset_card' ];
              · rw [ Finset.sum_range_succ, ← ih ];
                rw_mod_cast [ ← Set.ncard_union_eq ];
                · congr with x ; norm_num ; ring_nf ;
                  grind;
                · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Set.mem_Icc.mp hx₁.2, Set.mem_Icc.mp hx₂.2 ] ;
            -- Since B is periodic with period M, the number of elements of B in [i*M+1, (i+1)*M] is the same as the number of elements of B in [1, M].
            have hB_card_lower_step_periodic : ∀ i : ℕ, ((B ∩ Set.Icc (i * M + 1) ((i + 1) * M)).ncard : ℝ) = ((B ∩ Set.Icc 1 M).ncard : ℝ) := by
              intro i
              have hB_card_lower_step_periodic : (B ∩ Set.Icc (i * M + 1) ((i + 1) * M)) = (fun x => x + i * M) '' (B ∩ Set.Icc 1 M) := by
                ext x; simp [Set.mem_image];
                constructor;
                · intro hx
                  use x - i * M
                  simp;
                  refine' ⟨ ⟨ _, _, _ ⟩, Nat.sub_add_cancel ( by linarith ) ⟩;
                  · induction' i with i ih generalizing x <;> norm_num at *;
                    · tauto;
                    · convert ih ( x - M ) ( by rw [ hB_per ] ; exact by convert hx.1 using 1; rw [ Nat.sub_add_cancel ( by nlinarith ) ] ) ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : M ≤ x ) ] ) ( by nlinarith [ Nat.sub_add_cancel ( by nlinarith : M ≤ x ) ] ) using 1 ; rw [ Nat.sub_sub ] ; ring_nf;
                  · exact Nat.sub_pos_of_lt hx.2.1;
                  · linarith;
                · rintro ⟨ y, ⟨ hy₁, hy₂, hy₃ ⟩, rfl ⟩ ; exact ⟨ by exact Nat.recOn i ( by simpa using hy₁ ) fun n ihn => by simpa [ Nat.succ_mul, ← add_assoc ] using hB_per _ |>.1 ihn, by nlinarith, by nlinarith ⟩ ;
              rw [ hB_card_lower_step_periodic, Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy ];
            simp_all +singlePass [ mul_comm ];
          have hB_card_lower_step : ((B ∩ Set.Icc 1 N).ncard : ℝ) ≥ ((B ∩ Set.Icc 1 ((N / M) * M)).ncard : ℝ) := by
            gcongr;
            · exact Set.finite_iff_bddAbove.mpr ⟨ N, fun x hx => hx.2.2 ⟩;
            · exact Nat.div_mul_le_self _ _;
          refine le_trans ?_ hB_card_lower_step;
          refine le_trans ?_ ( ‹∀ k : ℕ, ( B ∩ Set.Icc 1 ( k * M ) |> Set.ncard : ℝ ) ≥ k * ( B ∩ Set.Icc 1 M |> Set.ncard : ℝ ) › ( N / M ) );
          field_simp;
          rw [ sub_le_iff_le_add ] ; norm_cast ; nlinarith [ Nat.div_add_mod N M, Nat.mod_lt N hM, show ( B ∩ Set.Icc 1 M |> Set.ncard ) ≤ M from le_trans ( Set.ncard_le_ncard <| show B ∩ Set.Icc 1 M ⊆ Set.Icc 1 M from Set.inter_subset_right ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ] ;
        refine' tendsto_iff_norm_sub_tendsto_zero.mpr _;
        refine' squeeze_zero_norm' _ _;
        use fun n => ( M : ℝ ) / n + ( M : ℝ ) / n;
        · norm_num +zetaDelta at *;
          refine' ⟨ M + 1, fun n hn => abs_sub_le_iff.mpr ⟨ _, _ ⟩ ⟩ <;> ring_nf at * <;> norm_num at *;
          · field_simp;
            rw [ div_add', div_le_div_iff_of_pos_right ] <;> try norm_num ; linarith;
            have := hB_card n; rw [ ← @Nat.cast_le ℝ ] at *; push_cast at *; nlinarith [ inv_mul_cancel_left₀ ( by positivity : ( M : ℝ ) ≠ 0 ) ( ( B ∩ Set.Icc 1 n ).ncard : ℝ ), inv_mul_cancel_left₀ ( by positivity : ( M : ℝ ) ≠ 0 ) ( ( B ∩ Set.Icc 1 M ).ncard : ℝ ) ] ;
          · have := hB_card_lower n; have := hB_card n; nlinarith [ inv_pos.mpr ( by norm_cast; linarith : 0 < ( n : ℝ ) ), mul_inv_cancel₀ ( by norm_cast; linarith : ( n : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( M : ℝ ) ≠ 0 ), ( by norm_cast : ( 1 : ℝ ) + M ≤ n ) ] ;
        · simpa using Filter.Tendsto.add ( tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat ) ( tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat );
      unfold upperDensity HasNaturalDensity at *;
      rw [ hB_nat_density.limsup_eq ] ; norm_num [ hM.ne' ]

/-
The product of (1 - 1/p^2) over primes p < k tends to 6/pi^2 as k goes to infinity.
-/
lemma prod_primes_inv_sq_tendsto : Filter.Tendsto (fun k => ∏ p ∈ Finset.filter Nat.Prime (Finset.range k), (1 - 1/(p:ℝ)^2)) Filter.atTop (nhds (6 / Real.pi^2)) := by
  -- The product over primes of (1 - 1/p^2) is the inverse of the sum over integers of 1/n^2 (Euler product). Since sum 1/n^2 = pi^2/6, the product is 6/pi^2.
  have h_euler_product : ∏' p : ℕ, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) = 6 / Real.pi^2 := by
    have h_euler_product : (∏' p : ℕ, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)) = (∑' n : ℕ, 1 / (n^2 : ℝ))⁻¹ := by
      -- Apply the Euler product formula to the Riemann zeta function.
      have h_euler_product : ∀ s : ℝ, 1 < s → (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^s)⁻¹ else 1) = (∑' n : ℕ, (1 / (n : ℝ)^s)) := by
        intro s hs;
        have := @EulerProduct.eulerProduct_hasProd;
        specialize @this ℝ _ ( fun n => ( n : ℝ ) ⁻¹ ^ s ) _ _ _ _ <;> norm_num at *;
        · intro m n hmn; rw [ Real.mul_rpow ( by positivity ) ( by positivity ), mul_comm ] ;
        · exact Summable.abs <| by simpa [ Real.inv_rpow ] using Real.summable_nat_rpow_inv.2 hs;
        · convert HasProd.tprod_eq ( this ( by rw [ Real.zero_rpow ( by positivity ) ] ) ) using 1;
          · convert ( tprod_subtype _ _ ) |> Eq.symm using 1;
            any_goals exact { p : ℕ | Nat.Prime p };
            any_goals try infer_instance;
            rotate_right;
            use fun p => 1 / ( 1 - 1 / ( p : ℝ ) ^ s );
            · simp +decide [ Set.mulIndicator ];
            · refine' tprod_congr fun p => _;
              rw [ one_div, ← tsum_geometric_of_lt_one ( by positivity ) ];
              · norm_num [ Real.inv_rpow ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ];
                norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), mul_comm ];
              · exact div_lt_self zero_lt_one ( Real.one_lt_rpow ( mod_cast p.2.one_lt ) ( by positivity ) );
          · norm_num [ Real.inv_rpow ];
      convert congr_arg ( fun x : ℝ => x⁻¹ ) ( h_euler_product 2 ( by norm_num ) ) using 1;
      · have h_prod_inv : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → (∏' p, f p)⁻¹ = ∏' p, (f p)⁻¹ := by
          intros f hf_pos hf_summable
          have h_prod_inv : (∏' p, f p) = Real.exp (∑' p, Real.log (f p)) := by
            exact Eq.symm (Real.rexp_tsum_eq_tprod hf_pos hf_summable)
          have h_prod_inv' : (∏' p, (f p)⁻¹) = Real.exp (∑' p, Real.log ((f p)⁻¹)) := by
            have h_prod_inv' : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → (∏' p, f p) = Real.exp (∑' p, Real.log (f p)) := by
              exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1);
            exact h_prod_inv' ( fun p => inv_pos.mpr ( hf_pos p ) ) ( by simpa [ Real.log_inv ] using hf_summable.neg ) ▸ by simp +decide ;
          simp_all +decide [Real.log_inv];
          rw [ ← Real.exp_neg, tsum_neg ];
        rw [ h_prod_inv ];
        · exact tprod_congr fun p => by split_ifs <;> norm_num;
        · intro p; split_ifs <;> norm_num;
          exact inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( mod_cast Nat.Prime.one_lt ‹_› ) two_ne_zero;
        · have h_sum_log : Summable (fun p : ℕ => if Nat.Prime p then Real.log (1 - 1 / (p : ℝ)^2)⁻¹ else 0) := by
            have h_log_bound : ∀ p : ℕ, Nat.Prime p → Real.log (1 - 1 / (p : ℝ)^2)⁻¹ ≤ 2 / (p : ℝ)^2 := by
              intro p hp; rw [ Real.log_inv ] ; ring_nf;
              nlinarith only [ Real.log_inv ( 1 - ( p : ℝ ) ⁻¹ ^ 2 ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( show 0 < 1 - ( p : ℝ ) ⁻¹ ^ 2 by exact sub_pos.mpr ( by simpa using inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( Nat.one_lt_cast.mpr hp.one_lt ) two_ne_zero ) ) ) ), inv_mul_cancel₀ ( show ( 1 - ( p : ℝ ) ⁻¹ ^ 2 ) ≠ 0 by exact ne_of_gt ( sub_pos.mpr ( by simpa using inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( Nat.one_lt_cast.mpr hp.one_lt ) two_ne_zero ) ) ) ), show ( p : ℝ ) ⁻¹ ^ 2 ≤ 1 / 4 by exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( inv_anti₀ ( by norm_num ) ( Nat.cast_le.mpr hp.two_le ) ) 2 ) ( by norm_num ) ]
            refine' Summable.of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ( Real.summable_nat_pow_inv.2 one_lt_two |> Summable.mul_left 2 );
            · split_ifs <;> first | positivity | exact Real.log_nonneg <| by rw [ inv_eq_one_div, le_div_iff₀ ] <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le ‹_›, one_div_mul_cancel <| show ( p : ℝ ) ^ 2 ≠ 0 by exact pow_ne_zero 2 <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero ‹_› ] ;
            · aesop;
          exact h_sum_log.congr fun p => by split_ifs <;> simp +decide [ * ] ;
      · norm_cast;
    field_simp;
    rw [ h_euler_product, inv_mul_eq_div, div_eq_iff ] <;> first | positivity | have := hasSum_zeta_two; have := this.tsum_eq; norm_num at * ; nlinarith [ Real.pi_gt_three ] ;
  generalize_proofs at *; (
  rw [ ← h_euler_product ];
  have h_euler_product : Filter.Tendsto (fun k => ∏ p ∈ Finset.range k, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)) Filter.atTop (nhds (∏' p : ℕ, (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1))) := by
    have h_abs_conv : Summable (fun p : ℕ => |Real.log (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)|) := by
      have h_log_conv : Summable (fun p : ℕ => |Real.log (1 - 1 / (p : ℝ)^2)|) := by
        -- We'll use the fact that |log(1 - x)| ≤ 2x for x in [0, 1/2].
        have h_log_bound : ∀ p : ℕ, p ≥ 2 → |Real.log (1 - 1 / (p : ℝ)^2)| ≤ 2 * (1 / (p : ℝ)^2) := by
          intros p hp
          have h_log_bound : |Real.log (1 - 1 / (p : ℝ)^2)| ≤ 2 * (1 / (p : ℝ)^2) := by
            have h_log_bound_aux : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → |Real.log (1 - x)| ≤ 2 * x := by
              intros x hx; rw [ abs_of_nonpos ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ] ; nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
            exact h_log_bound_aux _ ⟨ by positivity, by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith ⟩
          generalize_proofs at *; (
          exact h_log_bound)
        generalize_proofs at *; (
        rw [ ← summable_nat_add_iff 2 ];
        exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => h_log_bound _ ( by linarith ) ) ( Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two ))
      generalize_proofs at *; (
      exact Summable.of_nonneg_of_le ( fun p => abs_nonneg _ ) ( fun p => by split_ifs <;> norm_num ) h_log_conv)
    have h_exp_conv : Filter.Tendsto (fun k => Real.exp (∑ p ∈ Finset.range k, Real.log (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1))) Filter.atTop (nhds (Real.exp (∑' p : ℕ, Real.log (if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1)))) := by
      exact Real.continuous_exp.continuousAt.tendsto.comp <| h_abs_conv.of_abs.hasSum.tendsto_sum_nat
    generalize_proofs at *; (
    convert h_exp_conv using 2;
    · rw [ Real.exp_sum, Finset.prod_congr rfl fun _ _ => Real.exp_log ( by split_ifs <;> first | positivity | exact sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by assumption ) two_ne_zero ) ];
    · have h_exp_conv : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → ∏' p, f p = Real.exp (∑' p, Real.log (f p)) := by
        exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1)
      generalize_proofs at *; (
      exact h_exp_conv ( fun p => by split_ifs <;> first | positivity | exact sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( Nat.one_lt_cast.mpr <| Nat.Prime.one_lt ‹_› ) two_ne_zero ) <| h_abs_conv.of_abs;))
  generalize_proofs at *; (
  convert h_euler_product using 2 ; simp +decide [ Finset.prod_ite ]))

/-
If A is admissible, then for any C, A is contained in a periodic set B whose density is the product of (1 - 1/p^2) for primes p <= C.
-/
lemma admissible_subset_periodic (A : Set ℕ) (h : Admissible A) (C : ℕ) :
  ∃ B : Set ℕ, A ⊆ B ∧
  (∃ M > 0, (∀ n, n ∈ B ↔ n + M ∈ B) ∧
   ((B ∩ Set.Icc 1 M).ncard : ℝ) / M = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), (1 - 1/(p:ℝ)^2)) := by
     -- For each prime p, let b_p be a residue class mod p^2 that A avoids.
     obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ, ∀ p, Nat.Prime p → ∀ a ∈ A, ¬(a ≡ b p [MOD p^2]) := by
       have h_choose_residues : ∀ p, Nat.Prime p → ∃ b_p, ∀ a ∈ A, ¬(a ≡ b_p [MOD p^2]) := by
         intro p hp
         have h_residue : ∃ b_p ∈ Finset.range (p^2), ∀ a ∈ A, ¬(a ≡ b_p [MOD p^2]) := by
           have := h p hp;
           exact ⟨ this.choose, Finset.mem_range.mpr this.choose_spec.1, fun a ha => fun h => this.choose_spec.2 a ha <| h.symm ▸ Nat.mod_eq_of_lt this.choose_spec.1 ⟩;
         aesop;
       choose! b hb using h_choose_residues ; tauto;
     refine' ⟨ { n | ∀ p ∈ Finset.filter Nat.Prime ( Finset.range ( C + 1 ) ), ¬n ≡ b p [MOD p ^ 2] }, _, _ ⟩;
     · aesop_cat;
     · refine' ⟨ ∏ p ∈ Finset.filter Nat.Prime ( Finset.range ( C + 1 ) ), p ^ 2, Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _, _, _ ⟩;
       · simp +decide [Nat.ModEq, Nat.add_mod];
         intro n; refine' forall_congr' fun p => forall_congr' fun hp => forall_congr' fun hp' => _; simp +decide [ Nat.mod_eq_zero_of_dvd ( Finset.dvd_prod_of_mem _ <| Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hp, hp' ⟩ ) ] ;
       · -- The number of integers in [1, M] that are not congruent to b_p modulo p^2 for any prime p <= C is given by the Euler's totient function of M.
         have h_card : (Finset.filter (fun n => ∀ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), ¬n ≡ b p [MOD p^2]) (Finset.Icc 1 (∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), p^2))).card = (∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), (p^2 - 1)) := by
           have h_card : Finset.card (Finset.filter (fun n => ∀ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), ¬(n ≡ b p [MOD p^2])) (Finset.range (∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), p^2))) = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), (p^2 - 1) := by
             have h_card : ∀ (ps : Finset ℕ), (∀ p ∈ ps, Nat.Prime p) → Finset.card (Finset.filter (fun n => ∀ p ∈ ps, ¬(n ≡ b p [MOD p^2])) (Finset.range (∏ p ∈ ps, p^2))) = ∏ p ∈ ps, (p^2 - 1) := by
               intro ps hps;
               induction' ps using Finset.induction with p ps hps ih;
               · norm_num +zetaDelta at *;
               · have h_card_insert : Finset.card (Finset.filter (fun n => ¬(n ≡ b p [MOD p^2]) ∧ ∀ q ∈ ps, ¬(n ≡ b q [MOD q^2])) (Finset.range (p^2 * ∏ q ∈ ps, q^2))) = (p^2 - 1) * Finset.card (Finset.filter (fun n => ∀ q ∈ ps, ¬(n ≡ b q [MOD q^2])) (Finset.range (∏ q ∈ ps, q^2))) := by
                   have h_card_insert : Finset.card (Finset.filter (fun n => ¬(n ≡ b p [MOD p^2]) ∧ ∀ q ∈ ps, ¬(n ≡ b q [MOD q^2])) (Finset.range (p^2 * ∏ q ∈ ps, q^2))) = Finset.card (Finset.filter (fun n => ¬(n ≡ b p [MOD p^2])) (Finset.range (p^2))) * Finset.card (Finset.filter (fun n => ∀ q ∈ ps, ¬(n ≡ b q [MOD q^2])) (Finset.range (∏ q ∈ ps, q^2))) := by
                     rw [ ← Finset.card_product ];
                     refine' Finset.card_bij ( fun n hn => ( n % p ^ 2, n % ∏ q ∈ ps, q ^ 2 ) ) _ _ _;
                     · simp +contextual;
                       exact fun a ha₁ ha₂ ha₃ => ⟨ ⟨ Nat.mod_lt _ ( pow_pos ( Nat.Prime.pos ( hps p ( Finset.mem_insert_self _ _ ) ) ) 2 ), by simpa [ Nat.ModEq, Nat.mod_mod ] using ha₂ ⟩, Nat.mod_lt _ ( Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos ( hps q ( Finset.mem_insert_of_mem hq ) ) ) 2 ), fun q hq => by simpa [ Nat.ModEq, Nat.mod_mod, Finset.prod_eq_prod_diff_singleton_mul hq ] using ha₃ q hq ⟩;
                     · simp +zetaDelta at *;
                       intro a₁ ha₁ ha₂ ha₃ a₂ ha₄ ha₅ ha₆ ha₇ ha₈;
                       -- Since $a₁ \equiv a₂ \pmod{p^2}$ and $a₁ \equiv a₂ \pmod{\prod_{q \in ps} q^2}$, and $p^2$ and $\prod_{q \in ps} q^2$ are coprime, we have $a₁ \equiv a₂ \pmod{p^2 \prod_{q \in ps} q^2}$.
                       have h_cong : a₁ ≡ a₂ [MOD p^2 * ∏ q ∈ ps, q^2] := by
                         rw [ Nat.modEq_iff_dvd ] at *;
                         convert Int.coe_lcm_dvd ( Nat.modEq_iff_dvd.mp ha₇ ) ( Nat.modEq_iff_dvd.mp ha₈ ) using 1;
                         norm_cast;
                         rw [ Nat.Coprime.lcm_eq_mul ];
                         exact Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow _ _ <| hps.1.coprime_iff_not_dvd.mpr fun h => ‹p ∉ ps› <| by have := Nat.prime_dvd_prime_iff_eq hps.1 ( hps.2 q hq ) ; aesop;
                       exact Nat.mod_eq_of_lt ha₁ ▸ Nat.mod_eq_of_lt ha₄ ▸ h_cong;
                     · simp +zetaDelta at *;
                       intro a b_1 ha hb_1 hb_2 hb_3
                       obtain ⟨a_5, ha_5⟩ : ∃ a_5, a_5 ≡ a [MOD p^2] ∧ a_5 ≡ b_1 [MOD ∏ q ∈ ps, q^2] ∧ a_5 < p^2 * ∏ q ∈ ps, q^2 := by
                         have h_crt : Nat.gcd (p^2) (∏ q ∈ ps, q^2) = 1 := by
                           exact Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow _ _ <| hps.1.coprime_iff_not_dvd.mpr fun h => ‹p ∉ ps› <| by have := Nat.prime_dvd_prime_iff_eq hps.1 ( hps.2 q hq ) ; aesop;
                         have := Nat.chineseRemainder h_crt a b_1;
                         exact ⟨ this.val % ( p ^ 2 * ∏ q ∈ ps, q ^ 2 ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.2, Nat.mod_lt _ ( Nat.mul_pos ( pow_pos hps.1.pos 2 ) ( Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos ( hps.2 q hq ) ) 2 ) ) ⟩;
                       use a_5;
                       simp_all +decide [ Nat.ModEq, Nat.mod_eq_of_lt ];
                       intro q hq; specialize hb_3 q hq; rw [ ← Nat.mod_mod_of_dvd a_5 ( show q ^ 2 ∣ ∏ q ∈ ps, q ^ 2 from Finset.dvd_prod_of_mem _ hq ) ] ; aesop;
                   rw [ h_card_insert, show Finset.filter ( fun n => ¬n ≡ b p [MOD p ^ 2] ) ( Finset.range ( p ^ 2 ) ) = Finset.range ( p ^ 2 ) \ Finset.image ( fun n => n ) ( Finset.filter ( fun n => n ≡ b p [MOD p ^ 2] ) ( Finset.range ( p ^ 2 ) ) ) from ?_, Finset.card_sdiff ] <;> norm_num;
                   · rw [ show Finset.filter ( fun n => n ≡ b p [MOD p ^ 2] ) ( Finset.range ( p ^ 2 ) ) ∩ Finset.range ( p ^ 2 ) = { b p % ( p ^ 2 ) } from ?_ ] ; norm_num;
                     ext; simp [Nat.ModEq];
                     exact ⟨ fun h => by linarith [ Nat.mod_eq_of_lt h.1.1 ], fun h => ⟨ ⟨ by linarith [ Nat.mod_lt ( b p ) ( pow_pos ( Nat.Prime.pos ( hps p ( Finset.mem_insert_self p ps ) ) ) 2 ) ], by simp +decide [ h ] ⟩, by linarith [ Nat.mod_lt ( b p ) ( pow_pos ( Nat.Prime.pos ( hps p ( Finset.mem_insert_self p ps ) ) ) 2 ) ] ⟩ ⟩;
                   · grind;
                 simp_all +decide [Finset.prod_insert];
             exact h_card _ fun p hp => Finset.mem_filter.mp hp |>.2;
           rw [ ← h_card, Finset.range_eq_Ico, Finset.Ico_eq_cons_Ioo, Finset.filter_cons ] <;> norm_num;
           rw [ Finset.range_eq_Ico, Finset.Ico_eq_cons_Ioo, Finset.filter_cons ] <;> norm_num;
           · split_ifs <;> simp_all +decide;
             · rw [ Finset.Icc_eq_cons_Ico, Finset.filter_cons ] <;> norm_num;
               · split_ifs <;> simp_all +decide;
                 · rfl;
                 · obtain ⟨ p, hp₁, hp₂, hp₃, hp₄ ⟩ := ‹_›; specialize ‹∀ p : ℕ, 0 < p → p < C + 1 → Nat.Prime p → ¬0 ≡ b p [MOD p ^ 2]› p hp₁ hp₂ hp₃; simp_all +decide [ Nat.ModEq, Nat.mod_eq_zero_of_dvd ( Finset.dvd_prod_of_mem _ <| Finset.mem_filter.mpr ⟨ Finset.mem_Ioo.mpr ⟨ hp₁, hp₂ ⟩, hp₃ ⟩ ) ] ;
               · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( by aesop ) ) _;
             · rw [ Finset.Icc_eq_cons_Ico, Finset.filter_cons ] <;> norm_num;
               · split_ifs <;> simp_all +decide;
                 · rename_i h₁ h₂; obtain ⟨ p, hp₁, hp₂, hp₃, hp₄ ⟩ := h₁; specialize h₂ p hp₁ hp₂ hp₃; simp_all +decide [ Nat.ModEq ] ;
                   norm_num [ ← hp₄ ] at *;
                   exact False.elim <| h₂ <| Nat.mod_eq_zero_of_dvd <| Finset.dvd_prod_of_mem _ <| Finset.mem_filter.mpr ⟨ Finset.mem_Ioo.mpr ⟨ hp₁, hp₂ ⟩, hp₃ ⟩;
                 · rfl;
               · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2;
           · exact fun _ _ _ _ => pow_pos ‹_› 2;
         rw [ show ( { n | ∀ p ∈ Finset.filter Nat.Prime ( Finset.range ( C + 1 ) ), ¬n ≡ b p [MOD p ^ 2] } ∩ Set.Icc 1 ( ∏ p ∈ Finset.range ( C + 1 ) with Nat.Prime p, p ^ 2 ) ).ncard = ( Finset.filter ( fun n => ∀ p ∈ Finset.filter Nat.Prime ( Finset.range ( C + 1 ) ), ¬n ≡ b p [MOD p ^ 2] ) ( Finset.Icc 1 ( ∏ p ∈ Finset.range ( C + 1 ) with Nat.Prime p, p ^ 2 ) ) ).card from ?_ ];
         · rw [ h_card, Nat.cast_prod ];
           rw [ Nat.cast_prod, Finset.prod_congr rfl fun x hx => Nat.cast_sub <| Nat.one_le_pow _ _ <| Nat.Prime.pos <| Finset.mem_filter.mp hx |>.2 ] ; norm_num;
           rw [ ← Finset.prod_div_distrib, Finset.prod_congr rfl ] ; intros ; rw [ sub_div, inv_eq_one_div, div_self ] ; aesop;
         · rw [ ← Set.ncard_coe_finset ] ; congr ; ext ; aesop

/-
If A is admissible, its upper density is at most the product of (1 - 1/p^2) for primes p <= C.
-/
lemma admissible_upper_bound_C (A : Set ℕ) (h : Admissible A) (C : ℕ) :
  upperDensity A ≤ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (C + 1)), (1 - 1/(p:ℝ)^2) := by
    obtain ⟨ B, hB₁, hB₂ ⟩ := admissible_subset_periodic A h C;
    obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := hB₂; exact hM₃ ▸ density_of_subset_periodic A B M hM₁ hM₂ hB₁;

/-
Every admissible set has upper density at most 6/pi^2.
-/
theorem Admissible_implies_upperDensity_le_6_div_pi_sq (A : Set ℕ) (h : Admissible A) :
  upperDensity A ≤ 6 / Real.pi^2 := by
    convert le_of_tendsto_of_tendsto' tendsto_const_nhds ( prod_primes_inv_sq_tendsto ) ( fun k => ?_ ) using 1;
    have := admissible_upper_bound_C A h ( k - 1 ) ; rcases k with ( _ | k ) <;> aesop;

/-
The product of $p^2$ for all primes $p \le n^2$.
-/
def W_sq (n : ℕ) : ℕ := ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n^2 + 1)), p^2

/-
If $n'$ is a multiple of $W = \prod_{p \le n^2} p^2$ and $a \le n$ is squarefree, then if $n'+a$ is not squarefree, it must be divisible by the square of a prime $p > n^2$.
-/
lemma key_construction_i_deterministic (n : ℕ) (n' : ℕ) (a : ℕ)
    (hW : W_sq n ∣ n')
    (ha : a ∈ Finset.Icc 1 n)
    (ha_sf : a ∈ SF)
    (h_not_sf : n' + a ∉ SF) :
    ∃ p, Nat.Prime p ∧ p > n^2 ∧ p^2 ∣ (n' + a) := by
      -- Let $p$ be a prime such that $p^2 \mid n' + a$.
      obtain ⟨p, hp_prime, hp_sq⟩ : ∃ p : ℕ, Nat.Prime p ∧ p^2 ∣ n' + a := by
        contrapose! h_not_sf;
        exact Nat.squarefree_iff_prime_squarefree.mpr fun p hp => by simpa [ sq ] using h_not_sf p hp;
      by_cases hp_le : p ≤ n^2;
      · -- Since $p \leq n^2$, we have $p^2 \mid W_sq n$.
        have hp_sq_div_W_sq : p^2 ∣ W_sq n := by
          exact Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by nlinarith ), hp_prime ⟩ );
        simp_all +decide [ Nat.dvd_add_right, dvd_trans hp_sq_div_W_sq hW ];
        exact absurd ( ha_sf.squarefree_of_dvd hp_sq ) ( by rw [ sq, Nat.squarefree_mul_iff ] ; aesop );
      · exact ⟨ p, hp_prime, not_le.mp hp_le, hp_sq ⟩

/-
The set of multiples of W in [x/2, x].
-/
def candidates (x W : ℕ) : Finset ℕ := (Finset.Icc (x / 2) x).filter (fun n => W ∣ n)

/-
$W$ is positive.
-/
lemma W_sq_pos (n : ℕ) : W_sq n > 0 := by
  exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2

/-
If $x/2 \ge W$, then there is a multiple of $W$ in $[x/2, x]$.
-/
lemma candidates_card_pos (x W : ℕ) (hW : W > 0) (hx : x / 2 ≥ W) : (candidates x W).card > 0 := by
  -- Since $W \leq x/2$, there exists some multiple of $W$ in the interval $[x/2, x]$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, W * k ∈ Finset.Icc (x / 2) x := by
    exact ⟨ x / 2 / W + 1, Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod ( x / 2 ) W, Nat.mod_lt ( x / 2 ) hW ], by linarith [ Nat.div_mul_le_self ( x / 2 ) W, Nat.div_mul_le_self x 2 ] ⟩ ⟩;
  exact Finset.card_pos.mpr ⟨ W * k, Finset.mem_filter.mpr ⟨ hk, dvd_mul_right _ _ ⟩ ⟩

/-
The set of candidates $n'$ such that $n' + a$ is divisible by $p^2$.
-/
def bad_candidates (x W a p : ℕ) : Finset ℕ :=
  (candidates x W).filter (fun n' => p^2 ∣ (n' + a))

/-
The fraction of candidates $n'$ such that $p^2 \mid n' + a$ is bounded by $O(1/p^2 + W/x)$.
-/
lemma bad_candidates_prob_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (a : ℕ) (p : ℕ),
    n > 0 → p > n^2 → Nat.Prime p → x / 2 ≥ W_sq n →
    ((bad_candidates x (W_sq n) a p).card : ℝ) / (candidates x (W_sq n)).card ≤ C * (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) := by
      obtain ⟨ C, hC_pos, hC ⟩ := lemma_freq
      use C, hC_pos
      intro n x a p hn hp hp_prime hx
      have h_filter_bounds : (bad_candidates x (W_sq n) a p).card ≤ C * ((candidates x (W_sq n)).card : ℝ) * ((1 / (p : ℝ)^2) + ((W_sq n : ℝ) / (x / 2))) := by
        by_cases h : ( candidates x ( W_sq n ) |> Finset.card ) = 0 <;> simp_all +decide [ mul_assoc ];
        · unfold bad_candidates; aesop;
        · have := hC ( W_sq n ) ( p ^ 2 ) 0 ( -a % ( p ^ 2 ) |> Int.toNat ) ( x / 2 ) ( x - x / 2 + 1 ) ?_ ?_ ?_ <;> norm_num at *;
          · rw [ div_le_iff₀ ] at this;
            · refine le_trans ?_ ( this.trans ?_ );
              · refine' mod_cast Finset.card_le_card _;
                simp +decide [ Finset.subset_iff ];
                simp +contextual [Nat.ModEq];
                simp +contextual [ bad_candidates, candidates ];
                intro k hk₁ hk₂ hk₃ hk₄; rw [ Nat.mod_eq_zero_of_dvd hk₃ ] ; norm_num [ ← Int.natCast_inj, Int.toNat_of_nonneg ( Int.emod_nonneg _ ( pow_ne_zero 2 ( Nat.cast_ne_zero.mpr hp_prime.ne_zero ) ) ) ] ;
                exact ⟨ by omega, Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using hk₄ ⟩;
              · rw [ mul_right_comm ];
                rw [ mul_assoc ] ; gcongr;
                · simp +contextual [ Finset.subset_iff, candidates ];
                  exact fun n hn₁ hn₂ hn₃ => ⟨ by omega, Nat.dvd_of_mod_eq_zero hn₃ ⟩;
                · exact div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd hx ( by exact not_le_of_gt ( Nat.pos_of_ne_zero ( by exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero 2 ( Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ) ) ) ) zero_lt_two;
                · rw [ div_le_iff₀ ] <;> norm_cast ; omega;
            · simp_all +decide [ Finset.ext_iff, candidates ];
              exact ⟨ h.choose, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ h.choose_spec ], by linarith [ h.choose_spec, Nat.sub_add_cancel ( show x / 2 ≤ x from Nat.div_le_self _ _ ) ] ⟩, Nat.modEq_zero_iff_dvd.mpr h.choose_spec.2.2 ⟩ ⟩;
          · refine' Nat.Coprime.prod_left fun q hq => _;
            exact Nat.Coprime.pow_left 2 ( Nat.Coprime.symm <| hp_prime.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos <| Finset.mem_filter.mp hq |>.2 ) <| by nlinarith [ Finset.mem_range.mp <| Finset.mem_filter.mp hq |>.1 ] );
          · omega;
          · contrapose! h; simp_all +decide [ candidates ] ;
            exact fun y hy₁ hy₂ => fun hy₃ => h hy₁ ( by omega ) <| Nat.modEq_zero_iff_dvd.mpr hy₃
      norm_num at *; (
      exact div_le_of_le_mul₀ ( Nat.cast_nonneg _ ) ( by positivity ) ( by linarith ));

-- This is the end of the provided solution.

/-
The set of candidates $n'$ that fail condition (i), i.e., there exists $a \le n$ and $p > n^2$ such that $p^2 \mid n' + a$.
-/
def bad_candidates_i (n x : ℕ) : Finset ℕ :=
  Finset.biUnion (Finset.Icc 1 n) (fun a =>
    Finset.biUnion ((Finset.Ioc (n^2) (Nat.sqrt (2 * x))).filter Nat.Prime) (fun p =>
      bad_candidates x (W_sq n) a p))

/-
The fraction of candidates failing condition (i) is $O(1/n + n W/\sqrt{x})$.
-/
lemma bad_candidates_i_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ),
    n > 0 → x / 2 ≥ W_sq n →
    ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card ≤ C * (1 / (n : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      obtain ⟨ C, hC₀, hC ⟩ := bad_candidates_prob_bound;
      refine' ⟨ C * 4, by positivity, fun n x hn hx => _ ⟩;
      -- Apply the bound from `hC` to each term in the sum.
      have h_sum_bound : ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card ≤ C * (∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc (n^2) (Nat.sqrt (2 * x))), (1 / (p : ℝ)^2)) * n + C * (W_sq n : ℝ) / (x / 2) * n * (Nat.sqrt (2 * x)) := by
        have h_sum_bound : ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card ≤ ∑ a ∈ Finset.Icc 1 n, ∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc (n^2) (Nat.sqrt (2 * x))), (C * (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2))) := by
          have h_sum_bound : ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card ≤ ∑ a ∈ Finset.Icc 1 n, ∑ p ∈ ((Finset.Ioc (n^2) (Nat.sqrt (2 * x))).filter Nat.Prime), ((bad_candidates x (W_sq n) a p).card : ℝ) / (candidates x (W_sq n)).card := by
            have h_sum : ((bad_candidates_i n x).card : ℝ) ≤ ∑ a ∈ Finset.Icc 1 n, ∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc (n ^ 2) (Nat.sqrt (2 * x))), ((bad_candidates x (W_sq n) a p).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le.trans ( Finset.sum_le_sum fun a ha => Finset.card_biUnion_le );
            simpa only [ ← Finset.sum_div _ _ _ ] using div_le_div_of_nonneg_right h_sum <| Nat.cast_nonneg _;
          exact h_sum_bound.trans ( Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun p hp => hC n x a p hn ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) ( Finset.mem_filter.mp hp |>.2 ) hx );
        simp_all +decide [Finset.sum_add_distrib, mul_add, mul_comm, mul_left_comm,
          Finset.mul_sum _ _ _];
        refine le_trans h_sum_bound ?_;
        norm_num [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
        gcongr;
        exact le_trans ( Finset.card_filter_le _ _ ) ( by simp );
      -- The sum over $p$ of $1/p^2$ is $O(1/n^2)$.
      have h_sum_p_inv_sq : ∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc (n^2) (Nat.sqrt (2 * x))), (1 / (p : ℝ)^2) ≤ 2 / (n : ℝ)^2 := by
        -- The sum over $p$ of $1/p^2$ is $O(1/n^2)$ because there are at most $\sqrt{2x}$ terms and each term is at most $1/(n^2)^2$.
        have h_sum_p_inv_sq : ∑ p ∈ Finset.filter Nat.Prime (Finset.Ioc (n^2) (Nat.sqrt (2 * x))), (1 / (p : ℝ)^2) ≤ ∑ p ∈ Finset.Icc (n^2 + 1) (Nat.sqrt (2 * x)), (1 / (p : ℝ)^2) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg ( fun p hp => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) ], by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ⟩ ) fun _ _ _ => by positivity;
        -- The sum over $p$ of $1/p^2$ is $O(1/n^2)$ because there are at most $\sqrt{2x}$ terms and each term is at most $1/(n^2)^2$. We can bound the sum by comparing it to a telescoping series.
        have h_telescope : ∑ p ∈ Finset.Icc (n^2 + 1) (Nat.sqrt (2 * x)), (1 / (p : ℝ)^2) ≤ ∑ p ∈ Finset.Icc (n^2 + 1) (Nat.sqrt (2 * x)), (1 / (p - 1 : ℝ) - 1 / (p : ℝ)) := by
          gcongr;
          rw [ div_sub_div, div_le_div_iff₀ ] <;> nlinarith only [ show ( ↑‹ℕ› : ℝ ) ≥ 2 by norm_cast; nlinarith [ Finset.mem_Icc.mp ‹_› ], sq ( ( ↑‹ℕ› : ℝ ) - 1 ) ];
        -- The sum of a telescoping series is bounded by the difference of the first and last terms.
        have h_telescope_sum : ∑ p ∈ Finset.Icc (n^2 + 1) (Nat.sqrt (2 * x)), (1 / (p - 1 : ℝ) - 1 / (p : ℝ)) ≤ 1 / (n^2 : ℝ) := by
          erw [ Finset.sum_Ico_eq_sum_range ];
          -- The sum of a telescoping series is bounded by the difference of the first and last terms, which is $1/n^2$.
          have h_telescope_sum : ∀ m : ℕ, ∑ k ∈ Finset.range m, (1 / (n^2 + k : ℝ) - 1 / (n^2 + k + 1 : ℝ)) = 1 / (n^2 : ℝ) - 1 / (n^2 + m : ℝ) := by
            exact fun m => by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
          convert h_telescope_sum ( Nat.sqrt ( 2 * x ) + 1 - ( n ^ 2 + 1 ) ) |> le_of_eq |> le_trans <| sub_le_self _ <| by positivity using 1 ; norm_num [ add_assoc, add_tsub_assoc_of_le ];
          ac_rfl;
        exact h_sum_p_inv_sq.trans <| h_telescope.trans <| h_telescope_sum.trans <| by rw [ div_le_div_iff_of_pos_right ] <;> norm_cast ; nlinarith;
      -- The sum over $p$ of $W/x$ is at most $\sqrt{2x} \cdot W/x = O(W/\sqrt{x})$.
      have h_sum_p_W_div_x : (W_sq n : ℝ) / (x / 2) * n * (Nat.sqrt (2 * x)) ≤ 4 * (W_sq n : ℝ) * n / (Nat.sqrt x) := by
        rcases x with ( _ | _ | x ) <;> norm_num at *;
        · exact absurd hx <| ne_of_gt <| W_sq_pos n;
        · field_simp;
          norm_cast;
          nlinarith only [ show 0 ≤ W_sq n * ( x + 1 + 1 ) by positivity, show ( 2 * ( x + 1 + 1 ) ).sqrt * ( x + 1 + 1 ).sqrt ≤ ( x + 1 + 1 ) * 2 by nlinarith only [ Nat.sqrt_le ( 2 * ( x + 1 + 1 ) ), Nat.sqrt_le ( x + 1 + 1 ) ] ];
      refine le_trans h_sum_bound ?_;
      field_simp;
      refine le_trans ( mul_le_mul_of_nonneg_left ( add_le_add h_sum_p_inv_sq ( show ( W_sq n : ℝ ) * 2 * Nat.sqrt ( 2 * x ) / x ≤ ( W_sq n : ℝ ) * 2 * Nat.sqrt ( 2 * x ) / x from le_rfl ) ) ( sq_nonneg _ ) ) ?_;
      rw [ mul_add, mul_div_cancel₀ ] <;> norm_num [ hn.ne' ];
      ring_nf at *;
      nlinarith [ show ( n : ℝ ) ^ 2 ≥ 1 by exact_mod_cast Nat.one_le_pow _ _ hn ]

/-
Definitions for part (ii):
`I_R_eps` is the interval $(R, (1+\epsilon)R]$.
`relevant_primes` are primes $p$ with $\max(n^2, \sqrt{R}) < p \le \sqrt{2x}$.
`bad_a_ii` are $a \in \SF \cap I_R$ such that $n'+a$ is divisible by $p^2$ for some relevant prime.
`bad_candidates_ii_R` are candidates $n'$ where the number of bad $a$ is large ($> \epsilon^2 R$).
-/
def I_R_eps (R : ℕ) (ε : ℝ) : Finset ℕ := Finset.Ioc R (Nat.floor ((1 + ε) * R))

def relevant_primes (n R x : ℕ) : Finset ℕ :=
  (Finset.Ioc (max (n^2) (Nat.sqrt R)) (Nat.sqrt (2 * x))).filter Nat.Prime

def bad_a_ii (n' R x n : ℕ) (ε : ℝ) : Finset ℕ :=
  (I_R_eps R ε).filter (fun a => a ∈ SF ∧ ∃ p ∈ relevant_primes n R x, p^2 ∣ n' + a)

def bad_candidates_ii_R (R x n : ℕ) (ε : ℝ) (W : ℕ) : Finset ℕ :=
  (candidates x W).filter (fun n' => (bad_a_ii n' R x n ε).card > ε^2 * R)

/-
The sum of `bad_a_ii` sizes is bounded by the sum of `bad_candidates` sizes.
-/
lemma sum_bad_a_ii_le_sum_bad_candidates (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ) :
  ∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ) ≤
  ∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0 := by
    rw [ Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun p hp => ?_ ];
    rotate_left;
    use fun a p => if a ∈ SF then ∑ n' ∈ candidates x ( W_sq n ), if p ^ 2 ∣ n' + a then 1 else 0 else 0;
    · unfold bad_candidates; aesop;
    · rw [ Finset.sum_comm ];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      rotate_right;
      use fun n' => ∑ a ∈ I_R_eps R ε, if a ∈ SF ∧ ∃ p ∈ relevant_primes n R x, p ^ 2 ∣ n' + a then 1 else 0;
      · rw [ Finset.sum_comm ];
        gcongr;
        split_ifs <;> simp_all +decide;
        norm_cast;
        exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( Finset.card_biUnion_le );
      · unfold bad_a_ii; aesop;

/-
The expected number of bad $a$'s is bounded by the sum over relevant primes.
-/
lemma sum_bad_a_ii_bound_explicit :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ),
    n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ε > 0 →
    (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card ≤
    C * ((I_R_eps R ε).card : ℝ) * (∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2))) := by
      by_contra h;
      obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ (n : ℕ) (x : ℕ) (a : ℕ) (p : ℕ),
        n > 0 → p > n^2 → Nat.Prime p → x / 2 ≥ W_sq n →
        ((bad_candidates x (W_sq n) a p).card : ℝ) / (candidates x (W_sq n)).card ≤ C * (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) := by
          -- Apply the lemma bad_candidates_prob_bound to obtain the constant C.
          apply bad_candidates_prob_bound;
      refine' h ⟨ C, hC_pos, _ ⟩;
      intros n x R ε hn hx hR hx' hε_pos
      have h_sum : (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) ≤ ∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, if a ∈ SF then C * (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) * (candidates x (W_sq n)).card else 0 := by
        refine' le_trans _ ( Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun p hp => _ );
        convert sum_bad_a_ii_le_sum_bad_candidates n x R ε using 1;
        split_ifs <;> norm_num;
        have := hC n x a p hn ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1.trans_le' <| le_max_left _ _ ) ( Finset.mem_filter.mp hp |>.2 ) hx; rw [ div_le_iff₀ ] at this <;> norm_num at * ; linarith;
        exact Finset.card_pos.mp ( candidates_card_pos x ( W_sq n ) ( W_sq_pos n ) ( by linarith [ Nat.div_mul_le_self x 2 ] ) );
      refine' div_le_of_le_mul₀ _ _ _;
      · positivity;
      · exact mul_nonneg ( mul_nonneg hC_pos.le ( Nat.cast_nonneg _ ) ) ( Finset.sum_nonneg fun _ _ => by positivity );
      · refine' le_trans h_sum _;
        norm_num [ Finset.sum_ite, Finset.mul_sum _ _ _, Finset.sum_mul ];
        refine' Finset.sum_le_sum fun p hp => _;
        refine' le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| by positivity ) _ ; ring_nf ; norm_num

/-
The sum of $1/p^2$ for relevant primes is $O(1/\sqrt{R})$.
-/
lemma sum_inv_sq_relevant_primes_bound_R :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ),
    n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x →
    ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2) ≤ C / (Nat.sqrt R : ℝ) := by
      use 2;
      norm_num +zetaDelta at *;
      intros n x R hn hx hR hxR
      have h_sum_bound : ∑ p ∈ Finset.Icc (Nat.sqrt R + 1) (Nat.sqrt (2 * x)), (1 / (p : ℝ)^2) ≤ 2 / (Nat.sqrt R : ℝ) := by
        have h_sum_bound : ∑ p ∈ Finset.Icc (Nat.sqrt R + 1) (Nat.sqrt (2 * x)), (1 / (p : ℝ)^2) ≤ ∑ p ∈ Finset.Icc (Nat.sqrt R + 1) (Nat.sqrt (2 * x)), (1 / (p - 1 : ℝ) - 1 / (p : ℝ)) := by
          gcongr;
          rw [ div_sub_div, div_le_div_iff₀ ] <;> nlinarith only [ show ( ↑‹ℕ› : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Icc.mp ‹_›, Nat.sqrt_pos.mpr ( show 0 < R by linarith ) ] ];
        -- The series $\sum_{p=\sqrt{R}+1}^{\sqrt{2x}} \left(\frac{1}{p-1} - \frac{1}{p}\right)$ is a telescoping series.
        have h_telescoping : ∑ p ∈ Finset.Icc (Nat.sqrt R + 1) (Nat.sqrt (2 * x)), (1 / (p - 1 : ℝ) - 1 / (p : ℝ)) = 1 / (Nat.sqrt R : ℝ) - 1 / (Nat.sqrt (2 * x) : ℝ) := by
          erw [ Finset.sum_Ico_eq_sum_range ];
          convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring_nf;
          rw [ Nat.cast_sub ( Nat.sqrt_le_sqrt ( by linarith ) ) ] ; ring;
        exact h_sum_bound.trans <| h_telescoping.symm ▸ by exact le_trans ( sub_le_self _ <| by positivity ) <| by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.sqrt_pos.mpr <| show 0 < R by linarith ] ;
      refine le_trans ?_ h_sum_bound;
      norm_num [ relevant_primes ];
      exact Finset.sum_le_sum_of_subset_of_nonneg ( fun p hp => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ), Nat.le_max_right ( n ^ 2 ) ( Nat.sqrt R ) ], by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ), Nat.le_max_right ( n ^ 2 ) ( Nat.sqrt R ) ] ⟩ ) fun _ _ _ => by positivity;

/-
The conclusion of Proposition Key: n' satisfies properties (i) and (ii).
-/
def PropositionKey_conclusion (n n' : ℕ) (ε C : ℝ) : Prop :=
  (∀ a ∈ Finset.Icc 1 n, a ∈ SF → n' + a ∈ SF) ∧
  (∀ R : ℕ, n ≤ R → R ≤ n' →
    let numerator := ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n' + a ∈ SF)).card
    (numerator : ℝ) / R ≥ 6 / Real.pi^2 - C * ε)

/-
The set of bad a in the interval is contained in the union of bad a due to small primes, large primes, and very large primes.
-/
def bad_in_interval (n' : ℕ) (R : ℕ) (ε : ℝ) : Finset ℕ :=
  (I_R_eps R ε).filter (fun a => a ∈ SF ∧ n' + a ∉ SF)

def small_primes (n R : ℕ) : Finset ℕ :=
  (Finset.Ioc (n^2) (Nat.sqrt R)).filter Nat.Prime

def bad_small (n' R : ℕ) (ε : ℝ) (n : ℕ) : Finset ℕ :=
  (I_R_eps R ε).filter (fun a => ∃ p ∈ small_primes n R, p^2 ∣ n' + a)

def bad_large (n' R x : ℕ) (ε : ℝ) (n : ℕ) : Finset ℕ :=
  (I_R_eps R ε).filter (fun a => a ∈ SF ∧ ∃ p ∈ relevant_primes n R x, p^2 ∣ n' + a)

def bad_very_large (n' R x : ℕ) (ε : ℝ) : Finset ℕ :=
  (I_R_eps R ε).filter (fun a => ∃ p, Nat.Prime p ∧ p > Nat.sqrt (2 * x) ∧ p^2 ∣ n' + a)

lemma bad_in_interval_subset (n' R x n : ℕ) (ε : ℝ) (hW : W_sq n ∣ n') :
  bad_in_interval n' R ε ⊆ bad_small n' R ε n ∪ bad_large n' R x ε n ∪ bad_very_large n' R x ε := by
    intro a ha
    obtain ⟨ha_sqf, p, hp_prime, hp_sq_div⟩ : a ∈ SF ∧ ∃ p, Nat.Prime p ∧ p^2 ∣ n' + a ∧ p > n^2 := by
      obtain ⟨ha_sqf, ha_not_sqf⟩ : a ∈ SF ∧ n' + a ∉ SF := by
        unfold bad_in_interval at ha; aesop;
      obtain ⟨p, hp_prime, hp_sq_div⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ n' + a := by
        contrapose! ha_not_sqf
        generalize_proofs at *; (
        exact Nat.squarefree_iff_prime_squarefree.mpr fun p hp => by simpa [ sq ] using ha_not_sqf p hp;)
      generalize_proofs at *; (
      refine ⟨ ha_sqf, p, hp_prime, hp_sq_div, ?_ ⟩
      generalize_proofs at *; (
      by_contra h_contra
      generalize_proofs at *; (
      have h_div_a : p^2 ∣ a := by
        have h_div_a : p^2 ∣ n' := by
          exact dvd_trans ( by exact Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by nlinarith [ hp_prime.two_le ] ), hp_prime ⟩ ) ) hW
        generalize_proofs at *; (
        simpa using Nat.dvd_sub hp_sq_div h_div_a)
      generalize_proofs at *; (
      exact absurd ( ha_sqf.squarefree_of_dvd h_div_a ) ( by rw [ sq, Nat.squarefree_mul_iff ] ; aesop )))))
    generalize_proofs at *; (
    by_cases hp_le_sqrt_R : p ≤ Nat.sqrt R <;> by_cases hp_le_sqrt_2x : p ≤ Nat.sqrt (2 * x) <;> simp_all +decide [ bad_small, bad_large, bad_very_large ];
    · exact Or.inl ⟨ by unfold bad_in_interval at ha; aesop, p, by unfold small_primes; aesop ⟩;
    · exact Or.inr <| Or.inr <| ⟨ by unfold bad_in_interval at ha; aesop, p, hp_prime, hp_le_sqrt_2x, hp_sq_div.1 ⟩;
    · right; left; exact ⟨ by
        exact Finset.mem_Ioc.mpr ⟨ Finset.mem_Ioc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.1, Finset.mem_Ioc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.2 ⟩, p, by
        unfold relevant_primes; aesop;, hp_sq_div.1 ⟩ ;
    · exact Or.inr <| Or.inr <| ⟨ by unfold bad_in_interval at ha; aesop, p, hp_prime, hp_le_sqrt_2x, hp_sq_div.1 ⟩)

/-
The sum of 1/k^2 for k > n is at most 1/n.
-/
lemma sum_inv_sq_tail_bound (n : ℕ) (hn : n > 0) :
  ∑' k : ℕ, (if k > n then 1 / (k : ℝ)^2 else 0) ≤ 1 / (n : ℝ) := by
    -- We compare the sum to an integral and use the fact that the integral of $1/x^2$ is $1/x$.
    have h_integral_comparison : ∀ n : ℕ, (n > 0) → (∑' k : ℕ, if k > n then (1 : ℝ) / k^2 else 0) ≤ ∑' k : ℕ, (1 : ℝ) / ((k + n) * (k + n + 1)) := by
      -- By shifting the index of summation, we can rewrite the sum as starting from $k = 1$ to infinity.
      have h_shift : ∀ (n : ℕ) (hn : n > 0), (∑' k : ℕ, if k > n then (1 : ℝ) / k^2 else 0) = (∑' k : ℕ, (1 : ℝ) / (k + n + 1)^2) := by
        intro n hn; rw [ ← Summable.sum_add_tsum_nat_add n.succ ] ; norm_num [ add_assoc, add_left_comm, add_comm ] ;
        · exact Finset.sum_eq_zero fun x hx => if_neg <| by linarith [ Finset.mem_range.mp hx ] ;
        · exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
      intro n hn; rw [ h_shift n hn ] ; refine' Summable.tsum_le_tsum _ _ _;
      · exact fun k => by gcongr ; nlinarith;
      · exact_mod_cast summable_nat_add_iff ( n + 1 ) |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
      · exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> nlinarith ) ( summable_nat_add_iff n |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
    -- The series $\sum_{k=n+1}^\infty \frac{1}{k(k-1)}$ is a telescoping series.
    have h_telescoping : ∀ (N : ℕ), (∑ k ∈ Finset.range N, (1 : ℝ) / ((k + n) * (k + n + 1))) = (1 : ℝ) / n - (1 : ℝ) / (N + n) := by
      intro N; induction N <;> simp_all +decide [ Finset.sum_range_succ ];
      -- Combine and simplify the terms on the left-hand side.
      field_simp
      ring;
    -- By the properties of the telescoping series, we can conclude that the sum of the series is bounded above by $1/n$.
    have h_sum_bound : Filter.Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (1 : ℝ) / ((k + n) * (k + n + 1)))) Filter.atTop (nhds ((1 : ℝ) / n)) := by
      simpa only [ h_telescoping ] using by simpa using tendsto_const_nhds.sub ( tendsto_inverse_atTop_nhds_zero_nat.comp ( Filter.tendsto_add_atTop_nat n ) ) ;
    exact le_trans ( h_integral_comparison n hn ) ( le_of_tendsto_of_tendsto' ( by exact ( Summable.hasSum ( by exact by { by_contra h; exact not_tendsto_atTop_of_tendsto_nhds ( h_sum_bound ) <| by exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 h } ) |> HasSum.tendsto_sum_nat ) ) h_sum_bound fun N => by aesop )

/-
The number of multiples of k in the interval (a, b] is at most (b-a)/k + 1.
-/
lemma count_multiples_in_interval (a b k : ℕ) (hk : k > 0) :
  ((Finset.Ioc a b).filter (fun x => k ∣ x)).card ≤ (b - a) / k + 1 := by
    -- The multiples of $k$ in the interval $(a, b]$ are given by $k * (a / k + 1), k * (a / k + 2), \ldots, k * (b / k)$.
    have h_multiples : Finset.filter (fun x => k ∣ x) (Finset.Ioc a b) ⊆ Finset.image (fun m => k * m) (Finset.Icc (a / k + 1) (b / k)) := by
      intro x hx;
      simp +zetaDelta at *;
      exact ⟨ x / k, ⟨ Nat.succ_le_of_lt ( Nat.div_lt_of_lt_mul <| by linarith [ Nat.div_mul_cancel hx.2 ] ), Nat.div_le_div_right hx.1.2 ⟩, by rw [ mul_comm, Nat.div_mul_cancel hx.2 ] ⟩;
    refine' le_trans ( Finset.card_le_card h_multiples ) _ |> le_trans <| _;
    exact ( b / k ) - ( a / k );
    · exact Finset.card_image_le.trans ( by simp +arith +decide );
    · rw [ Nat.sub_le_iff_le_add ];
      rw [ Nat.div_le_iff_le_mul_add_pred hk ];
      cases le_total b a <;> simp_all +decide [ Nat.div_eq_of_lt ];
      · nlinarith [ Nat.div_add_mod a k, Nat.mod_lt a hk, Nat.sub_add_cancel hk ];
      · linarith [ Nat.div_add_mod ( b - a ) k, Nat.mod_lt ( b - a ) hk, Nat.sub_add_cancel ‹_›, Nat.div_add_mod a k, Nat.mod_lt a hk, Nat.sub_add_cancel hk ]

/-
The cardinality of bad_small is bounded by the sum over small primes p of (|I|/p^2 + 1).
-/
lemma bad_small_card_bound_sum (n' R : ℕ) (ε : ℝ) (n : ℕ) :
  ((bad_small n' R ε n).card : ℝ) ≤
  ∑ p ∈ small_primes n R, (((I_R_eps R ε).card : ℝ) / p^2 + 1) := by
    -- For each small prime $p$, the set $S_p = \{a \in I_{R,\epsilon} : p^2 \mid n' + a\}$ is in one-to-one correspondence with the set of multiples of $p^2$ in the interval $n' + I_{R,\epsilon}$.
    have h_card_S_p (p : ℕ) (hp : p ∈ small_primes n R) : ((I_R_eps R ε).filter (fun a => p^2 ∣ n' + a)).card ≤ ((I_R_eps R ε).card : ℝ) / (p : ℝ)^2 + 1 := by
      have h_multiples : ((Finset.Ioc (n' + R) (n' + Nat.floor ((1 + ε) * R))).filter (fun x => p^2 ∣ x)).card ≤ (Nat.floor ((1 + ε) * R) - R) / p^2 + 1 := by
        convert count_multiples_in_interval ( n' + R ) ( n' + ⌊ ( 1 + ε ) * R⌋₊ ) ( p ^ 2 ) _ using 1;
        · rw [ Nat.add_sub_add_left ];
        · exact pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2;
      have h_multiples : ((Finset.Ioc R (Nat.floor ((1 + ε) * R))).filter (fun a => p^2 ∣ n' + a)).card ≤ ((Finset.Ioc (n' + R) (n' + Nat.floor ((1 + ε) * R))).filter (fun x => p^2 ∣ x)).card := by
        rw [ ← Finset.card_image_of_injective _ ( add_right_injective n' ) ] ; exact Finset.card_le_card fun x hx => by aesop;
      refine le_trans ( Nat.cast_le.mpr <| h_multiples.trans ‹_› ) ?_;
      norm_num [ I_R_eps ];
      exact Nat.cast_div_le .. |> le_trans <| by norm_num;
    refine' le_trans _ ( Finset.sum_le_sum h_card_S_p );
    norm_cast;
    convert Finset.card_biUnion_le;
    all_goals try infer_instance;
    unfold bad_small; ext; aesop;

/-
The sum of 1/p^2 over small primes is at most 1/n^2.
-/
lemma sum_inv_sq_small_primes_bound (n R : ℕ) (hn : n > 0) :
  ∑ p ∈ small_primes n R, (1 / (p : ℝ)^2) ≤ 1 / (n^2 : ℝ) := by
    -- The sum is over primes $p \in (n^2, \sqrt{R}]$.
    -- This is bounded by the sum over all integers $k \in (n^2, \sqrt{R}]$.
    have h_sum_bound : ∑ p ∈ small_primes n R, (1 / (p : ℝ)^2) ≤ ∑' k : ℕ, (if k > n^2 then 1 / (k : ℝ)^2 else 0) := by
      refine' le_trans _ ( Summable.sum_le_tsum _ _ _ );
      any_goals exact Finset.filter ( fun p => Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ Nat.sqrt R ) ( Finset.Ioc ( n ^ 2 ) ( Nat.sqrt R ) );
      · simp +decide [ Finset.sum_ite ];
        refine' Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => by positivity;
        simp +decide [ Finset.subset_iff ];
        unfold small_primes; aesop;
      · exact fun _ _ => by positivity;
      · exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )
    generalize_proofs at *; (
    exact h_sum_bound.trans ( sum_inv_sq_tail_bound _ ( by positivity ) ) |> le_trans <| by norm_num;)

/-
The number of bad a due to small primes is bounded by 2 * epsilon^2 * R.
-/
lemma bad_small_bound :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∀ R : ℕ, R ≥ n →
  ∀ n' : ℕ,
  ((bad_small n' R ε n).card : ℝ) ≤ C * ε^2 * R := by
    use 2;
    refine' ⟨ by norm_num, fun ε hε_pos hε_lt_one => ⟨ ⌈ε⁻¹ ^ 4⌉₊ + 1, fun n hn R hR n' => _ ⟩ ⟩;
    -- By `bad_small_card_bound_sum`, the cardinality is bounded by $|I_{R,\epsilon}| \sum_{p \in small} \frac{1}{p^2} + |small|$.
    have h_card_bound : ((bad_small n' R ε n).card : ℝ) ≤ (I_R_eps R ε).card * (∑ p ∈ small_primes n R, (1 / (p : ℝ)^2)) + (small_primes n R).card := by
      refine le_trans ( bad_small_card_bound_sum n' R ε n ) ?_;
      norm_num [ div_eq_mul_inv, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
    -- Use the bounds on the sum of 1/p^2 and the cardinality of small_primes.
    have h_sum_bound : (∑ p ∈ small_primes n R, (1 / (p : ℝ)^2)) ≤ ε := by
      have h_sum_bound : (∑ p ∈ small_primes n R, (1 / (p : ℝ)^2)) ≤ 1 / (n^2 : ℝ) := by
        convert sum_inv_sq_small_primes_bound n R ( by linarith ) using 1;
      refine le_trans h_sum_bound ?_;
      rw [ div_le_iff₀ ] <;> nlinarith [ show ( n : ℝ ) ≥ ⌈ε⁻¹ ^ 4⌉₊ + 1 by exact_mod_cast hn, Nat.le_ceil ( ε⁻¹ ^ 4 ), inv_pos.2 hε_pos, mul_inv_cancel₀ ( ne_of_gt hε_pos ), pow_pos ( inv_pos.2 hε_pos ) 2, pow_pos ( inv_pos.2 hε_pos ) 3, pow_pos ( inv_pos.2 hε_pos ) 4 ]
    have h_card_small_bound : (small_primes n R).card ≤ Real.sqrt R := by
      have h_card_small_bound : (small_primes n R).card ≤ Nat.sqrt R := by
        exact le_trans ( Finset.card_le_card ( show small_primes n R ⊆ Finset.Icc 1 ( Nat.sqrt R ) from fun x hx => Finset.mem_Icc.mpr ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hx |>.2 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ⟩ ) ) ( by simp );
      exact le_trans ( Nat.cast_le.mpr h_card_small_bound ) ( Real.le_sqrt_of_sq_le ( mod_cast Nat.sqrt_le' _ ) );
    -- Use the bound on the cardinality of I_R_eps.
    have h_card_I_R_eps_bound : ((I_R_eps R ε).card : ℝ) ≤ ε * R := by
      unfold I_R_eps;
      norm_num [ Nat.floor_le ];
      rw [ Nat.cast_sub ] <;> norm_num;
      · exact le_trans ( Nat.floor_le ( by positivity ) ) ( by linarith );
      · exact Nat.le_floor <| by nlinarith;
    -- Use the bound on the square root of R.
    have h_sqrt_R_bound : Real.sqrt R ≤ ε^2 * R := by
      rw [ Real.sqrt_le_left ] <;> ring_nf;
      · have h_sqrt_R_bound : (ε⁻¹ ^ 4 : ℝ) ≤ R := by
          exact le_trans ( Nat.le_ceil _ ) ( mod_cast by linarith );
        rw [ inv_pow, inv_eq_one_div, div_le_iff₀ ] at h_sqrt_R_bound <;> nlinarith [ pow_pos hε_pos 4 ];
      · positivity;
    nlinarith [ show 0 ≤ ε * R by positivity ]

/-
If n' + max(a) <= 2x, then bad_very_large is empty.
-/
lemma bad_very_large_empty (n' R x : ℕ) (ε : ℝ) (h : n' + Nat.floor ((1 + ε) * R) ≤ 2 * x) :
  bad_very_large n' R x ε = ∅ := by
    -- Assume there exists $a \in \text{bad\_very\_large}$.
    by_contra h_nonempty;
    obtain ⟨a, ha⟩ : ∃ a ∈ I_R_eps R ε, ∃ p, Nat.Prime p ∧ p > Nat.sqrt (2 * x) ∧ p^2 ∣ n' + a := by
      unfold bad_very_large at h_nonempty; aesop;
    -- Since $a \in I_R_eps$, we have $a \leq \lfloor (1+\epsilon)R \rfloor$.
    have ha_le : a ≤ Nat.floor ((1 + ε) * R) := by
      exact Finset.mem_Ioc.mp ha.1 |>.2;
    obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := ha.2;
    nlinarith [ Nat.sqrt_lt.mp hp₂, Nat.le_of_dvd ( by linarith [ Finset.mem_Ioc.mp ha.1 ] ) hp₃ ]

/-
The tail sum of mu(d)/d^2 for d > k is bounded by 1/k.
-/
lemma sum_moebius_div_sq_tail_bound (k : ℕ) (hk : k > 0) :
  abs (∑' d : ℕ, (if d > k then (ArithmeticFunction.moebius d : ℝ) / d ^ 2 else 0)) ≤ 1 / (k : ℝ) := by
    -- By Lemma `sum_inv_sq_tail_bound`, we know that $\sum_{d > k} \frac{1}{d^2} \le \frac{1}{k}$.
    have h_sum_inv_sq_tail_bound : (∑' (d : ℕ), if k < d then (1 : ℝ) / d ^ 2 else 0) ≤ 1 / (k : ℝ) := by
      exact sum_inv_sq_tail_bound k hk;
    refine' le_trans ( le_of_eq <| _ ) ( h_sum_inv_sq_tail_bound.trans' _ );
    rw [ ← Real.norm_eq_abs ];
    refine' le_trans ( norm_tsum_le_tsum_norm _ ) _;
    · refine' Summable.of_nonneg_of_le ( fun i => norm_nonneg _ ) ( fun i => _ ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
      split_ifs <;> norm_num [ ArithmeticFunction.moebius ];
      split_ifs <;> norm_num;
    · refine' Summable.tsum_le_tsum _ _ _;
      · intro i; split_ifs <;> norm_num [ ArithmeticFunction.moebius ] ;
        split_ifs <;> norm_num;
      · refine' Summable.of_nonneg_of_le ( fun i => _ ) ( fun i => _ ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
        · positivity;
        · split_ifs <;> norm_num [ ArithmeticFunction.moebius ];
          split_ifs <;> norm_num;
      · exact Summable.of_nonneg_of_le ( fun d => by positivity ) ( fun d => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )

/-
The difference between the sum of mu(d) * floor(n/d^2) and n * sum(mu(d)/d^2) is at most sqrt(n).
-/
lemma sum_moebius_floor_approx (n : ℕ) :
  abs ((∑ d ∈ Finset.Icc 1 (Nat.sqrt n), (ArithmeticFunction.moebius d : ℝ) * (n / d^2 : ℕ)) -
       n * ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), (ArithmeticFunction.moebius d : ℝ) / d^2) ≤ Nat.sqrt n := by
         -- The absolute value of each term in the sum is bounded by 1.
         have h_abs_term : ∀ d ∈ Finset.Icc 1 (Nat.sqrt n), |(ArithmeticFunction.moebius d : ℝ) * (n / d^2 : ℕ) - n * (ArithmeticFunction.moebius d : ℝ) / d^2| ≤ 1 := by
           intro d hd; rw [ mul_div_right_comm ] ; simp +decide [ abs_le ] ;
           norm_num [ ArithmeticFunction.moebius ];
           split_ifs <;> norm_num;
           constructor <;> by_cases h : Even ( ArithmeticFunction.cardFactors d ) <;> simp_all +decide;
           · rw [ div_le_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod n ( d ^ 2 ), Nat.mod_lt n ( pow_pos ( by linarith : 0 < d ) 2 ) ];
           · exact le_add_of_nonneg_of_le zero_le_one ( by rw [ le_div_iff₀ ( by norm_cast; nlinarith ) ] ; norm_cast; nlinarith [ Nat.div_mul_le_self n ( d ^ 2 ) ] );
           · rw [ add_div', le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_mul_le_self n ( d ^ 2 ), Nat.pos_of_ne_zero ( show d ^ 2 ≠ 0 by nlinarith ) ];
           · rw [ div_le_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod n ( d ^ 2 ), Nat.mod_lt n ( pow_pos ( by linarith : 0 < d ) 2 ) ];
         simpa [ Finset.mul_sum _ _ _, mul_div_assoc ] using le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum h_abs_term ) |> le_trans <| by norm_num;

/-
The infinite sum of mu(d)/d^2 is equal to 6/pi^2.
-/
lemma sum_moebius_div_sq_tsum_eq :
  ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / d^2 = 6 / Real.pi^2 := by
    -- The series is absolutely convergent, so the infinite sum is the same as the limit of the partial sums.
    have h_abs_conv : Summable (fun d : ℕ => |(ArithmeticFunction.moebius d : ℝ) / d^2|) := by
      norm_num [ abs_div, ArithmeticFunction.moebius ];
      exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun n => by split_ifs <;> norm_num ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
    refine' tendsto_nhds_unique _ ( sum_moebius_div_sq_tendsto );
    convert h_abs_conv.of_abs.hasSum.tendsto_sum_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) using 1;
    exact funext fun n => by erw [ Function.comp_apply, Finset.sum_Ico_eq_sub _ ] <;> norm_num;

/-
The difference between the partial sum of mu(d)/d^2 and 6/pi^2 is at most 1/k.
-/
lemma partial_sum_diff_bound (k : ℕ) (hk : k > 0) :
  abs ((∑ d ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius d : ℝ) / d^2) - 6 / Real.pi^2) ≤ 1 / (k : ℝ) := by
    convert sum_moebius_div_sq_tail_bound k hk using 1;
    have h_tsum_eq : ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / d^2 = 6 / Real.pi^2 := by
      exact sum_moebius_div_sq_tsum_eq;
    have h_sum_split : ∑' d : ℕ, (if d > k then (ArithmeticFunction.moebius d : ℝ) / d^2 else 0) = ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / d^2 - ∑' d : ℕ, (if d ≤ k then (ArithmeticFunction.moebius d : ℝ) / d^2 else 0) := by
      rw [ ← Summable.tsum_sub ] ; congr ; ext d ; split_ifs <;> linarith;
      · exact ( by contrapose! h_tsum_eq; erw [ tsum_eq_zero_of_not_summable h_tsum_eq ] ; positivity );
      · rw [ ← summable_nat_add_iff ( k + 1 ) ];
        exact ⟨ _, hasSum_single 0 fun n hn => if_neg <| by linarith ⟩;
    rw [ h_sum_split, h_tsum_eq, ← Summable.sum_add_tsum_nat_add k.succ ];
    · rw [ ← abs_neg ] ; rw [ ← h_tsum_eq ] ; erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ] ;
      rw [ Finset.sum_congr rfl fun i hi => if_pos <| by linarith [ Finset.mem_range.mp hi ] ];
      rw [ tsum_congr fun i => if_neg ( by linarith ) ] ; norm_num;
    · refine' summable_of_ne_finset_zero _;
      exacts [ Finset.range ( k + 1 ), fun b hb => if_neg fun h => hb <| Finset.mem_range_succ_iff.mpr h ]

/-
The difference between n times the partial sum of mu(d)/d^2 and n times 6/pi^2 is at most 3 * sqrt(n).
-/
lemma bound_diff_partial_sum_limit (n : ℕ) (hn : n > 0) :
  abs ((n : ℝ) * (∑ d ∈ Finset.Icc 1 (Nat.sqrt n), (ArithmeticFunction.moebius d : ℝ) / d^2) - (n : ℝ) * (6 / Real.pi^2)) ≤ 3 * (Nat.sqrt n : ℝ) := by
    have := partial_sum_diff_bound ( Nat.sqrt n ) ?_ <;> norm_num at *;
    · rw [ ← mul_sub, abs_mul, abs_of_nonneg ( by positivity ) ];
      refine le_trans ( mul_le_mul_of_nonneg_left this <| Nat.cast_nonneg _ ) ?_;
      rw [ ← div_eq_mul_inv, div_le_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.lt_succ_sqrt n ];
    · positivity

/-
The number of squarefree integers up to n is 6/pi^2 * n + O(sqrt(n)).
-/
lemma SF_count_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 0 →
  abs (((Finset.Icc 1 n).filter (fun x => x ∈ SF)).card - (6 / Real.pi^2) * n) ≤ C * Nat.sqrt n := by
    use 4;
    use by norm_num;
    -- Apply the bounds from the previous lemmas to conclude the proof.
    intros n hn
    have h_sum_floor : abs ((∑ d ∈ Finset.Icc 1 (Nat.sqrt n), (ArithmeticFunction.moebius d : ℝ) * (n / d^2 : ℕ)) - (n : ℝ) * (6 / Real.pi^2)) ≤ 4 * (Nat.sqrt n : ℝ) := by
      convert le_trans ( abs_sub_le _ _ _ ) _ using 1;
      exact Real.instIsOrderedAddMonoid;
      exact ( n : ℝ ) * ∑ d ∈ Finset.Icc 1 ( Nat.sqrt n ), ( ArithmeticFunction.moebius d : ℝ ) / d ^ 2;
      refine' le_trans ( add_le_add ( sum_moebius_floor_approx n |> le_trans <| _ ) ( bound_diff_partial_sum_limit n hn |> le_trans <| _ ) ) _;
      exacts [ ↑n.sqrt, le_rfl, 3 * ↑n.sqrt, le_rfl, by linarith ];
    convert h_sum_floor using 2;
    convert congr_arg ( fun x : ℤ => ( x : ℝ ) - 6 / Real.pi ^ 2 * n ) ( sum_squarefree_indicator_eq_sum_moebius_floor n ) using 1;
    · norm_num [ SF ];
      convert rfl;
    · norm_num [ mul_comm ];
      exact rfl

/-
Definitions for the corrected geometric progression and the good candidate property.
-/
noncomputable def max_k (n x : ℕ) (ε : ℝ) : ℕ :=
  Nat.floor (Real.log ((x : ℝ) / n) / Real.log (1 + ε))

/-
Recursive definition of geometric progression to avoid gaps.
-/
noncomputable def geometric_R_rec (n : ℕ) (ε : ℝ) : ℕ → ℕ
| 0 => n
| k + 1 => Nat.floor ((1 + ε) * (geometric_R_rec n ε k : ℝ))

def geometric_points (n x : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.range (max_k n x ε + 5)).image (geometric_R_rec n ε)

/-
Definition of GeometricGood using the recursive geometric progression.
-/
def GeometricGood_rec (n n' : ℕ) (x : ℕ) (ε : ℝ) : Prop :=
  n' ∈ candidates x (W_sq n) ∧
  n' ∉ bad_candidates_i n x ∧
  ∀ k ∈ Finset.range (max_k n x ε + 5), n' ∉ bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)

/-
The set of bad elements up to R.
-/
def bad_upto (n' R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n' + a ∉ SF)

/-
The sum of the terms in the recursive geometric progression up to $m$ is bounded by $O(1/\epsilon)$ times the $m$-th term.
-/
lemma geometric_sum_bound :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∀ m : ℕ,
  ∑ k ∈ Finset.range m, (geometric_R_rec n ε k : ℝ) ≤ C * (1/ε) * (geometric_R_rec n ε m : ℝ) := by
    use 2;
    norm_num +zetaDelta at *;
    intro ε hε₁ hε₂;
    -- For sufficiently large $n$, the floor function does not affect the growth rate of the sequence.
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ k, geometric_R_rec n ε (k + 1) ≥ (1 + ε / 2) * geometric_R_rec n ε k := by
      use Nat.ceil (2 / ε) + 1;
      intro n hn k;
      have h_floor : ∀ x : ℕ, x ≥ Nat.ceil (2 / ε) + 1 → Nat.floor ((1 + ε) * x) ≥ (1 + ε / 2) * x := by
        intro x hx; nlinarith [ Nat.le_ceil ( 2 / ε ), Nat.lt_floor_add_one ( ( 1 + ε ) * x ), mul_div_cancel₀ 2 hε₁.ne', show ( x : ℝ ) ≥ ⌈2 / ε⌉₊ + 1 by exact_mod_cast hx ] ;
      convert h_floor ( geometric_R_rec n ε k ) _ using 1;
      exact Nat.recOn k ( by simpa using hn ) fun k ih => by exact Nat.le_floor <| by push_cast; nlinarith [ show ( geometric_R_rec n ε k : ℝ ) ≥ ⌈2 / ε⌉₊ + 1 by exact_mod_cast ih ] ;
    use N₀ + 1;
    intro n hn m; induction' m with m ih <;> norm_num [ Finset.sum_range_succ ] at *;
    · positivity;
    · nlinarith [ inv_pos.2 hε₁, mul_inv_cancel₀ hε₁.ne', hN₀ n ( by linarith ) m ]

/-
The set of bad elements up to $R$ is contained in the union of bad elements in the intervals of the geometric progression, provided the progression covers $R$ and the initial segment is good.
-/
lemma bad_upto_subset (n : ℕ) (n' : ℕ) (R : ℕ) (ε : ℝ) (m : ℕ)
  (h_cover : R ≤ geometric_R_rec n ε m)
  (h_good_i : ∀ a ∈ Finset.Icc 1 n, a ∈ SF → n' + a ∈ SF) :
  bad_upto n' R ⊆ Finset.biUnion (Finset.range m) (fun k => bad_in_interval n' (geometric_R_rec n ε k) ε) := by
    intros a ha;
    obtain ⟨k, hk⟩ : ∃ k < m, a ∈ Finset.Ioc (geometric_R_rec n ε k) (geometric_R_rec n ε (k + 1)) := by
      have h_seq : a ≤ geometric_R_rec n ε m := by
        exact le_trans ( Finset.mem_Icc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.2 ) h_cover
      generalize_proofs at *;
      by_cases h_cases : a ≤ geometric_R_rec n ε 0;
      · contrapose! h_good_i;
        unfold bad_upto at ha; aesop;
      · have h_seq : ∃ k ≤ m, a ≤ geometric_R_rec n ε k ∧ ∀ j < k, a > geometric_R_rec n ε j := by
          have h_seq : ∃ k ≤ m, a ≤ geometric_R_rec n ε k := by
            exact ⟨ m, le_rfl, h_seq ⟩
          generalize_proofs at *;
          exact ⟨ Nat.find h_seq, Nat.find_spec h_seq |>.1, Nat.find_spec h_seq |>.2, fun j hj => not_le.mp fun h => Nat.find_min h_seq hj ⟨ Nat.le_trans ( Nat.le_of_lt hj ) ( Nat.find_spec h_seq |>.1 ), h ⟩ ⟩
        generalize_proofs at *;
        obtain ⟨ k, hk₁, hk₂, hk₃ ⟩ := h_seq; use k - 1; rcases k <;> aesop;
    simp_all +decide [ bad_upto, bad_in_interval ];
    refine' ⟨ k, hk.1, _ ⟩ ; unfold I_R_eps ; aesop

/-
For a good candidate, the number of bad elements in the $k$-th interval is bounded by $C \epsilon^2 R_k$.
-/
lemma bad_in_interval_bound_rec :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ∈ Finset.range (max_k n x ε + 5),
  n' + Nat.floor ((1 + ε) * (geometric_R_rec n ε k)) ≤ 2 * x →
  ((bad_in_interval n' (geometric_R_rec n ε k) ε).card : ℝ) ≤ C * ε^2 * (geometric_R_rec n ε k) := by
    have h_good_candidates : ∃ C : ℝ, C > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ n' : ℕ, GeometricGood_rec n n' x ε → ∀ R ∈ geometric_points n x ε, n' + Nat.floor ((1 + ε) * R) ≤ 2 * x → ((bad_in_interval n' R ε).card : ℝ) ≤ C * ε^2 * R := by
      obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ n' : ℕ, GeometricGood_rec n n' x ε → ∀ R ∈ geometric_points n x ε, n' + Nat.floor ((1 + ε) * R) ≤ 2 * x → ((bad_small n' R ε n).card : ℝ) ≤ C₁ * ε^2 * R := by
        obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ R : ℕ, R ≥ n → ∀ n' : ℕ, ((bad_small n' R ε n).card : ℝ) ≤ C₁ * ε^2 * R := by
          exact bad_small_bound;
        exact ⟨ C₁, hC₁.1, fun ε hε₁ hε₂ => by obtain ⟨ N₀, hN₀ ⟩ := hC₁.2 ε hε₁ hε₂; exact ⟨ N₀, fun n hn => ⟨ n, fun x hx => fun n' hn' R hR hR' => hN₀ n hn R ( by
          obtain ⟨ k, hk ⟩ := Finset.mem_image.mp hR;
          -- By definition of `geometric_R_rec`, we know that `geometric_R_rec n ε k ≥ n` for all `k`.
          have h_geometric_R_rec_ge_n : ∀ k, geometric_R_rec n ε k ≥ n := by
            intro k; induction' k with k ih <;> norm_num [ geometric_R_rec ] ;
            exact Nat.le_floor <| by nlinarith [ show ( geometric_R_rec n ε k : ℝ ) ≥ n by exact_mod_cast ih ] ;
          linarith [ h_geometric_R_rec_ge_n k ] ) n' ⟩ ⟩ ⟩;
      obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ n' : ℕ, GeometricGood_rec n n' x ε → ∀ R ∈ geometric_points n x ε, n' + Nat.floor ((1 + ε) * R) ≤ 2 * x → ((bad_large n' R x ε n).card : ℝ) ≤ ε^2 * R := by
        use 1; norm_num;
        intros ε hε₁ hε₂
        use 1
        intro n hn
        use 1
        intro x hx n' hn' R hR hR';
        have := hn'.2.2 ( Finset.mem_image.mp hR |> Classical.choose ) ?_ <;> simp_all +decide [ GeometricGood_rec ];
        · contrapose! this;
          refine' Finset.mem_filter.mpr ⟨ _, _ ⟩ <;> norm_num [ bad_candidates_ii_R ];
          · exact hn'.1;
          · have := Classical.choose_spec ( Finset.mem_image.mp hR ) ; aesop;
        · have := Classical.choose_spec ( Finset.mem_image.mp hR ) ; aesop;
      have h_bad_very_large : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ n' : ℕ, GeometricGood_rec n n' x ε → ∀ R ∈ geometric_points n x ε, n' + Nat.floor ((1 + ε) * R) ≤ 2 * x → bad_very_large n' R x ε = ∅ := by
        intros ε hε_pos hε_lt_1
        use 1
        intro n hn
        use 1
        intro x hx
        intro n' hn'
        intro R hR
        intro hR_le
        apply bad_very_large_empty
        exact hR_le;
      refine' ⟨ C₁ + 1, by linarith, fun ε hε₁ hε₂ => _ ⟩;
      obtain ⟨ N₀₁, hN₀₁ ⟩ := hC₁.2 ε hε₁ hε₂
      obtain ⟨ N₀₂, hN₀₂ ⟩ := hC₂.2 ε hε₁ hε₂
      obtain ⟨ N₀₃, hN₀₃ ⟩ := h_bad_very_large ε hε₁ hε₂
      use max N₀₁ (max N₀₂ N₀₃);
      intros n hn
      obtain ⟨ x₀₁, hx₀₁ ⟩ := hN₀₁ n (by linarith [Nat.le_max_left N₀₁ (max N₀₂ N₀₃)])
      obtain ⟨ x₀₂, hx₀₂ ⟩ := hN₀₂ n (by linarith [Nat.le_max_right N₀₁ (max N₀₂ N₀₃), Nat.le_max_left N₀₂ N₀₃])
      obtain ⟨ x₀₃, hx₀₃ ⟩ := hN₀₃ n (by linarith [Nat.le_max_right N₀₁ (max N₀₂ N₀₃), Nat.le_max_right N₀₂ N₀₃]);
      use max x₀₁ (max x₀₂ x₀₃);
      intros x hx n' hn' R hR hR';
      have h_bad_in_interval_subset : bad_in_interval n' R ε ⊆ bad_small n' R ε n ∪ bad_large n' R x ε n ∪ bad_very_large n' R x ε := by
        apply bad_in_interval_subset;
        exact hn'.1 |> fun h => Finset.mem_filter.mp h |>.2;
      have h_bad_in_interval_card : ((bad_in_interval n' R ε).card : ℝ) ≤ ((bad_small n' R ε n).card : ℝ) + ((bad_large n' R x ε n).card : ℝ) + ((bad_very_large n' R x ε).card : ℝ) := by
        exact_mod_cast le_trans ( Finset.card_le_card h_bad_in_interval_subset ) ( Finset.card_union_le _ _ |> le_trans <| add_le_add_right ( Finset.card_union_le _ _ ) _ );
      rw [ hx₀₃ x ( by linarith [ Nat.le_max_right x₀₁ ( max x₀₂ x₀₃ ), Nat.le_max_right x₀₂ x₀₃ ] ) n' hn' R hR hR' ] at h_bad_in_interval_card ; norm_num at * ; nlinarith [ hx₀₁ x ( by linarith [ Nat.le_max_left x₀₁ ( max x₀₂ x₀₃ ), Nat.le_max_right x₀₁ ( max x₀₂ x₀₃ ) ] ) n' hn' R hR hR', hx₀₂ x ( by linarith [ Nat.le_max_left x₀₁ ( max x₀₂ x₀₃ ), Nat.le_max_right x₀₁ ( max x₀₂ x₀₃ ), Nat.le_max_left x₀₂ x₀₃, Nat.le_max_right x₀₂ x₀₃ ] ) n' hn' R hR hR' ] ;
    obtain ⟨ C, hC₀, hC ⟩ := h_good_candidates; use C, hC₀; intros ε hε₁ hε₂; obtain ⟨ N₀, hN₀ ⟩ := hC ε hε₁ hε₂; use N₀; intros n hn; obtain ⟨ x₀, hx₀ ⟩ := hN₀ n hn; use x₀; intros x hx; intros n' hn'; intros k hk; specialize hx₀ x hx n' hn'; simp_all +decide [ geometric_points ] ;

/-
For a good candidate, the number of bad elements in the $k$-th interval is bounded by $C \epsilon^2 R_k$.
-/
lemma bad_in_interval_bound_rec_v2 :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ∈ Finset.range (max_k n x ε + 5),
  n' + Nat.floor ((1 + ε) * (geometric_R_rec n ε k)) ≤ 2 * x →
  ((bad_in_interval n' (geometric_R_rec n ε k) ε).card : ℝ) ≤ C * ε^2 * (geometric_R_rec n ε k) := by
    -- Apply the bound from `bad_in_interval_bound_rec`.
    apply bad_in_interval_bound_rec

/-
Lower bound for the recursive geometric progression: $R_k \ge (1+\epsilon)^k (n - 1/\epsilon)$.
-/
lemma geometric_R_rec_lower_bound_explicit (n : ℕ) (ε : ℝ) (k : ℕ) (hε : 0 < ε) :
  (geometric_R_rec n ε k : ℝ) ≥ (1 + ε)^k * (n - 1/ε) := by
    -- Define the auxiliary sequence $a_k = R_k (1+\epsilon)^{-k}$.
    set a : ℕ → ℝ := fun k => (geometric_R_rec n ε k : ℝ) / (1 + ε)^k;
    -- Then $a_{k+1} (1+\epsilon)^{k+1} > (1+\epsilon) a_k (1+\epsilon)^k - 1$.
    have ha_recurrence : ∀ k, a (k + 1) > a k - (1 + ε)⁻¹ ^ (k + 1) := by
      intro k
      simp [a];
      rw [ show geometric_R_rec n ε ( k + 1 ) = Nat.floor ( ( 1 + ε ) * ( geometric_R_rec n ε k : ℝ ) ) by rfl ] ; rw [ div_sub', div_lt_div_iff₀ ] <;> try positivity;
      nlinarith [ Nat.lt_floor_add_one ( ( 1 + ε ) * ( geometric_R_rec n ε k : ℝ ) ), pow_pos ( by linarith : 0 < 1 + ε ) k, pow_succ' ( 1 + ε ) k, mul_inv_cancel_left₀ ( by positivity : ( 1 + ε ) ^ ( k + 1 ) ≠ 0 ) ( ( 1 + ε ) ^ k ) ];
    -- Summing this inequality:
    have ha_sum : ∀ k, a k ≥ n - ∑ j ∈ Finset.range k, (1 + ε)⁻¹ ^ (j + 1) := by
      intro k; induction' k with k ih <;> norm_num [ Finset.sum_range_succ ] at *;
      · aesop;
      · linarith [ ha_recurrence k ];
    -- The sum is bounded by $\sum_{j=1}^\infty (1+\epsilon)^{-j} = 1/\epsilon$.
    have ha_sum_bound : ∀ k, ∑ j ∈ Finset.range k, (1 + ε)⁻¹ ^ (j + 1) ≤ 1 / ε := by
      intro k; have := geom_sum_mul ( ( 1 + ε ) ⁻¹ ) k; simp_all +decide [pow_succ', mul_comm] ;
      rw [ ← Finset.mul_sum _ _ _ ] ; nlinarith [ inv_pos.mpr hε, inv_pos.mpr ( show 0 < 1 + ε by linarith ), mul_inv_cancel₀ ( show ( 1 + ε ) ≠ 0 by linarith ), mul_inv_cancel₀ ( show ( ε : ℝ ) ≠ 0 by linarith ), pow_pos ( show 0 < 1 + ε by linarith ) k, inv_pos.mpr ( show 0 < ( 1 + ε ) ^ k by positivity ), mul_inv_cancel₀ ( show ( ( 1 + ε ) ^ k : ℝ ) ≠ 0 by positivity ) ] ;
    have := ha_sum k; rw [ ge_iff_le ] at this; rw [ le_div_iff₀ ( by positivity ) ] at this; nlinarith [ ha_sum_bound k, pow_pos ( by positivity : 0 < ( 1 + ε ) ) k ] ;

/-
For a good candidate, the number of bad elements in the $k$-th interval is bounded by $C \epsilon^2 R_k$.
-/
lemma bad_in_interval_bound_rec_v3 :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ∈ Finset.range (max_k n x ε + 5),
  n' + Nat.floor ((1 + ε) * (geometric_R_rec n ε k)) ≤ 2 * x →
  ((bad_in_interval n' (geometric_R_rec n ε k) ε).card : ℝ) ≤ C * ε^2 * (geometric_R_rec n ε k) := by
    convert bad_in_interval_bound_rec_v2 using 1

/-
The recursive geometric progression eventually exceeds $x$.
-/
lemma geometric_covers_x :
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∀ x : ℕ, x ≥ n →
  geometric_R_rec n ε (max_k n x ε + 4) ≥ x := by
    intros ε hε_pos hε_lt_one
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x ≥ n, (1 + ε)^(max_k n x ε + 3) * (n - 1/ε) ≥ x := by
      -- By definition of $max_k$, we know that $(1 + ε)^{max_k n x ε} \geq (x / n) / (1 + ε)$.
      have h_max_k : ∀ n x : ℕ, n ≥ 1 → x ≥ n → (1 + ε)^(max_k n x ε) ≥ (x / n) / (1 + ε) := by
        intros n x hn hx
        have h_max_k : max_k n x ε ≥ Real.log ((x : ℝ) / n) / Real.log (1 + ε) - 1 := by
          exact le_of_lt ( Nat.sub_one_lt_floor _ );
        have h_exp : (1 + ε)^(max_k n x ε) ≥ Real.exp (Real.log ((x : ℝ) / n) - Real.log (1 + ε)) := by
          rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ];
          exact Real.exp_le_exp.mpr ( by nlinarith [ Real.log_pos ( show 1 + ε > 1 by linarith ), mul_div_cancel₀ ( Real.log ( x / n ) ) ( ne_of_gt ( Real.log_pos ( show 1 + ε > 1 by linarith ) ) ) ] );
        rw [ Real.exp_sub, Real.exp_log ( by exact div_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Nat.cast_pos.mpr ( by linarith ) ) ), Real.exp_log ( by linarith ) ] at h_exp ; aesop;
      -- Choose $N₀$ such that for all $n \geq N₀$, we have $(n - 1/ε) \geq n / (1 + ε)$.
      obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, (n - 1/ε : ℝ) ≥ n / (1 + ε) := by
        simp +zetaDelta at *;
        exact ⟨ ⌈ε⁻¹ * ( 1 + ε ) / ε⌉₊ + 1, fun n hn => by rw [ div_le_iff₀ ] <;> nlinarith [ Nat.le_ceil ( ε⁻¹ * ( 1 + ε ) / ε ), show ( n : ℝ ) ≥ ⌈ε⁻¹ * ( 1 + ε ) / ε⌉₊ + 1 by exact_mod_cast hn, mul_div_cancel₀ ( ε⁻¹ * ( 1 + ε ) ) hε_pos.ne', mul_inv_cancel₀ hε_pos.ne' ] ⟩;
      refine' ⟨ N₀ + 1, fun n hn x hx => _ ⟩ ; specialize hN₀ n ( by linarith ) ; specialize h_max_k n x ( by linarith ) ( by linarith ) ; simp_all +decide [ pow_add ];
      rw [ div_div, div_le_iff₀ ] at * <;> try positivity;
      · nlinarith [ pow_pos ( by linarith : 0 < 1 + ε ) 2, pow_pos ( by linarith : 0 < 1 + ε ) 3, mul_le_mul_of_nonneg_left hN₀ ( show 0 ≤ ( 1 + ε ) ^ max_k n x ε by positivity ) ];
      · exact mul_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( by linarith );
    use N₀; intros n hn x hx; specialize hN₀ n hn x hx; simp_all +decide [ pow_succ, mul_assoc ] ;
    have h_geometric_R_rec_lower_bound : (geometric_R_rec n ε (max_k n x ε + 4) : ℝ) ≥ (1 + ε)^(max_k n x ε + 4) * (n - 1/ε) := by
      exact geometric_R_rec_lower_bound_explicit n ε ( max_k n x ε + 4 ) hε_pos |> le_trans ( by norm_num );
    exact_mod_cast hN₀.trans ( h_geometric_R_rec_lower_bound.trans' ( by ring_nf; nlinarith ) )

/-
For a good candidate, the number of bad elements in the $k$-th interval is bounded by $C \epsilon^2 R_k$.
-/
lemma bad_in_interval_bound_rec_v4 :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ∈ Finset.range (max_k n x ε + 5),
  n' + Nat.floor ((1 + ε) * (geometric_R_rec n ε k)) ≤ 2 * x →
  ((bad_in_interval n' (geometric_R_rec n ε k) ε).card : ℝ) ≤ C * ε^2 * (geometric_R_rec n ε k) := by
    convert bad_in_interval_bound_rec_v3 using 1

/-
The expected number of bad $a$'s is bounded by a function involving $1/\sqrt{R}$.
-/
lemma expected_bad_a_bound_R :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ),
    n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ε > 0 →
    (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card ≤
    C * ((I_R_eps R ε).card : ℝ) * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      have := sum_bad_a_ii_bound_explicit;
      obtain ⟨ C, hC₀, hC ⟩ := this;
      -- Use the bound on the sum of 1/p^2 for relevant primes.
      have h_sum_bound : ∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x →
        ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) ≤ C * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x : ℝ)) := by
          have h_sum_bound : ∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x →
            ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2) ≤ C / (Nat.sqrt R : ℝ) := by
              obtain ⟨ C, hC₀, hC ⟩ := sum_inv_sq_relevant_primes_bound_R;
              exact ⟨ C, hC₀, hC ⟩;
          have h_sum_bound : ∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x →
            ∑ p ∈ relevant_primes n R x, (W_sq n : ℝ) / (x / 2) ≤ C * (W_sq n : ℝ) * n / (Nat.sqrt x : ℝ) := by
              use 2 * Real.sqrt 2 + 1;
              refine' ⟨ by positivity, fun n x R hn hx hR hx' => _ ⟩;
              -- The number of relevant primes is at most $\sqrt{2x}$.
              have h_num_primes : (relevant_primes n R x).card ≤ Nat.sqrt (2 * x) := by
                refine' le_trans ( Finset.card_le_card _ ) _;
                exact Finset.Icc 1 ( Nat.sqrt ( 2 * x ) );
                · exact fun p hp => Finset.mem_Icc.mpr ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ⟩;
                · norm_num;
              by_cases hx : x = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
              field_simp;
              refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr h_num_primes ) <| Nat.cast_nonneg _ ) zero_le_two ) <| Nat.cast_nonneg _ ) _;
              -- By simplifying, we can see that the inequality holds.
              have h_simplify : 2 * Nat.sqrt (x * 2) * Nat.sqrt x ≤ x * n * (2 * Real.sqrt 2 + 1) := by
                have h_simplify : 2 * Nat.sqrt (x * 2) * Nat.sqrt x ≤ x * (2 * Real.sqrt 2 + 1) := by
                  have h_sqrt : Nat.sqrt (x * 2) ≤ Real.sqrt (x * 2) ∧ Nat.sqrt x ≤ Real.sqrt x := by
                    exact ⟨ Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' _, Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' _ ⟩
                  norm_num at *;
                  nlinarith [ Real.sqrt_nonneg x, Real.sqrt_nonneg 2, Real.sq_sqrt ( Nat.cast_nonneg x ), Real.sq_sqrt zero_le_two, show ( x : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hx ), show ( Nat.sqrt x : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.sqrt_pos.mpr ( Nat.pos_of_ne_zero hx ) ) ];
                exact h_simplify.trans ( mul_le_mul_of_nonneg_right ( le_mul_of_one_le_right ( Nat.cast_nonneg _ ) ( mod_cast hn ) ) ( by positivity ) );
              nlinarith [ show 0 ≤ ( W_sq n : ℝ ) by positivity ];
          obtain ⟨ C₁, hC₁₀, hC₁ ⟩ := ‹∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ∑ p ∈ relevant_primes n R x, 1 / ( p : ℝ ) ^ 2 ≤ C / ( R.sqrt : ℝ ) ›
          obtain ⟨ C₂, hC₂₀, hC₂ ⟩ := h_sum_bound
          use max C₁ C₂ + 1
          simp;
          refine' ⟨ by positivity, fun n x R hn hx₁ hx₂ hx₃ => _ ⟩ ; simp_all +decide [ Finset.sum_add_distrib ];
          refine le_trans ( add_le_add ( hC₁ n x R hn hx₁ hx₂ hx₃ ) ( hC₂ n x R hn hx₁ hx₂ hx₃ ) ) ?_ ; ring_nf;
          nlinarith [ show 0 ≤ ( R.sqrt : ℝ ) ⁻¹ by positivity, show 0 ≤ ( x.sqrt : ℝ ) ⁻¹ by positivity, show 0 ≤ ( W_sq n : ℝ ) * n * ( x.sqrt : ℝ ) ⁻¹ by positivity, le_max_left C₁ C₂, le_max_right C₁ C₂ ];
      obtain ⟨ C', hC'₀, hC' ⟩ := h_sum_bound;
      exact ⟨ C * C', mul_pos hC₀ hC'₀, fun n x R ε hn hx hR hx' hε => le_trans ( hC n x R ε hn hx hR hx' hε ) ( by convert mul_le_mul_of_nonneg_left ( hC' n x R hn hx hR hx' ) ( mul_nonneg hC₀.le ( Nat.cast_nonneg ( I_R_eps R ε |> Finset.card ) ) ) using 1 ; ring ) ⟩

/-
The probability that a candidate is bad for a given R is bounded by a function of R, n, x, and epsilon.
-/
lemma prob_bad_candidates_ii_R_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ),
    n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ε > 0 →
    ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤
    C / ε^2 * ((I_R_eps R ε).card : ℝ) / R * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      -- By Lemma `expected_bad_a_bound_R`, we have that the expected number of bad $a$'s is bounded by a function involving $1/\sqrt{R}$.
      obtain ⟨C, hC_pos, hC⟩ : ∃ C : ℝ, C > 0 ∧ ∀ (n x R : ℕ) (ε : ℝ), n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ε > 0 → ((∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card) ≤ C * ((I_R_eps R ε).card : ℝ) * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
        exact expected_bad_a_bound_R;
      -- By Markov's inequality, the fraction of bad candidates is at most the expected number of bad $a$'s divided by $\epsilon^2 R$.
      have h_markov : ∀ (n x R : ℕ) (ε : ℝ), n > 0 → x / 2 ≥ W_sq n → R ≥ n → R ≤ x → ε > 0 → ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤ ((∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card) / (ε^2 * R) := by
        intros n x R ε hn hx hR hx' hε_pos
        have h_markov : ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) * (ε^2 * R) ≤ (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) := by
          have h_markov : ∀ n' ∈ bad_candidates_ii_R R x n ε (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ) ≥ ε^2 * R := by
            intros n' hn'_bad
            have h_card : (bad_a_ii n' R x n ε).card > ε^2 * R := by
              exact_mod_cast Finset.mem_filter.mp hn'_bad |>.2;
            exact le_of_lt h_card;
          have h_markov : ∑ n' ∈ bad_candidates_ii_R R x n ε (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ) ≥ (bad_candidates_ii_R R x n ε (W_sq n)).card * (ε^2 * R) := by
            simpa using Finset.sum_le_sum h_markov;
          exact h_markov.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Nat.cast_nonneg _ );
        rw [ div_right_comm ];
        gcongr;
        rwa [ le_div_iff₀ ( mul_pos ( sq_pos_of_pos hε_pos ) ( Nat.cast_pos.mpr ( by linarith ) ) ) ];
      refine' ⟨ C, hC_pos, fun n x R ε hn hx hR hx' hε => le_trans ( h_markov n x R ε hn hx hR hx' hε ) _ ⟩;
      convert div_le_div_of_nonneg_right ( hC n x R ε hn hx hR hx' hε ) ( by positivity : 0 ≤ ε ^ 2 * R ) using 1 ; ring

/-
The number of integers in $(R, (1+\epsilon)R]$ is at most $\epsilon R + 1$.
-/
lemma card_I_R_eps_le (R : ℕ) (ε : ℝ) (hR : R > 0) (hε : ε > 0) :
  ((I_R_eps R ε).card : ℝ) ≤ ε * R + 1 := by
    unfold I_R_eps;
    norm_num [ Finset.card_map, Finset.card_range ];
    rw [ Nat.cast_sub ] <;> norm_num;
    · exact le_trans ( Nat.floor_le ( by positivity ) ) ( by linarith );
    · exact Nat.le_floor <| by nlinarith;

/-
If R is very large, there are no bad candidates of type ii.
-/
lemma bad_candidates_ii_R_empty_of_large_R (n x R : ℕ) (ε : ℝ) (W : ℕ)
    (hR : R > 2 * x) (hε : ε > 0) :
    bad_candidates_ii_R R x n ε W = ∅ := by
      ext n';
      simp [bad_candidates_ii_R];
      intro hn'
      have h_empty : bad_a_ii n' R x n ε = ∅ := by
        ext a
        simp [bad_a_ii, relevant_primes];
        exact fun ha₁ ha₂ p hp₁ hp₂ hp₃ hp₄ => by nlinarith [ Nat.sqrt_lt.mp hp₂, Nat.sqrt_le ( 2 * x ) ] ;
      aesop

/-
The recursive geometric progression grows at least exponentially with rate 1 + epsilon/2.
-/
lemma geometric_R_rec_lower_bound (n k : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hn : n > 2 / ε) :
    (geometric_R_rec n ε k : ℝ) ≥ (1 + ε / 2) ^ k * n := by
      induction' k with k ih <;> norm_num [ *, pow_succ', mul_assoc ] at *;
      · exact Nat.le_refl n;
      · -- By definition of geometric_R_rec, we have geometric_R_rec n ε (k + 1) = floor((1 + ε) * geometric_R_rec n ε k).
        have h_geometric_R_rec_succ : geometric_R_rec n ε (k + 1) = Nat.floor ((1 + ε) * (geometric_R_rec n ε k : ℝ)) := by
          exact rfl;
        rw [ h_geometric_R_rec_succ ];
        refine' le_trans _ ( Nat.sub_one_lt_floor _ |> le_of_lt );
        rw [ div_lt_iff₀ ] at hn <;> nlinarith [ pow_le_pow_right₀ ( by linarith : ( 1 + ε / 2 ) ≥ 1 ) ( show k ≥ 0 by linarith ) ]

/-
The sum of the inverse square roots of the geometric progression is bounded by $O(1/(\epsilon \sqrt{n}))$.
-/
lemma sum_inv_sqrt_R_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 →
  ∀ n : ℕ, n > 2 / ε →
  ∀ m : ℕ,
  ∑ k ∈ Finset.range m, 1 / Real.sqrt (geometric_R_rec n ε k) ≤ C / (ε * Real.sqrt n) := by
    -- We use the lower bound on $R_k$ to bound the sum.
    have h_sum_bound : ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ n : ℕ, (n : ℝ) > 2 / ε → ∀ m : ℕ, ∑ k ∈ Finset.range m, (1 / Real.sqrt ((1 + ε / 2) ^ k * n : ℝ)) ≤ C / (ε * Real.sqrt n) := by
      -- We can sum the geometric series $\sum_{k=0}^{m-1} (1 + \epsilon / 2)^{-k/2}$ and show it is bounded by $C / \epsilon$.
      have h_geo_series_bound : ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ m : ℕ, ∑ k ∈ Finset.range m, (1 + ε / 2 : ℝ) ^ (-k / 2 : ℝ) ≤ C / ε := by
        -- The sum of a geometric series with ratio $r < 1$ is $\frac{1}{1-r}$. Here, $r = \frac{1}{\sqrt{1+\epsilon/2}}$.
        have h_geo_series_sum : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ m : ℕ, ∑ k ∈ Finset.range m, (1 + ε / 2 : ℝ) ^ (-k / 2 : ℝ) ≤ 1 / (1 - 1 / Real.sqrt (1 + ε / 2)) := by
          intros ε hε₁ hε₂ m
          have h_geo_series_sum : ∑ k ∈ Finset.range m, (1 / Real.sqrt (1 + ε / 2)) ^ k ≤ 1 / (1 - 1 / Real.sqrt (1 + ε / 2)) := by
            rw [ le_div_iff₀ ] <;> nlinarith [ show 0 < 1 / Real.sqrt ( 1 + ε / 2 ) by positivity, show 1 / Real.sqrt ( 1 + ε / 2 ) < 1 by rw [ div_lt_one ( by positivity ) ] ; exact Real.lt_sqrt_of_sq_lt ( by linarith ), pow_pos ( show 0 < 1 / Real.sqrt ( 1 + ε / 2 ) by positivity ) m, geom_sum_mul ( 1 / Real.sqrt ( 1 + ε / 2 ) ) m ];
          convert h_geo_series_sum using 2 ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg ( by positivity : 0 ≤ 1 + ε / 2 ) ] ; ring_nf;
          rw [ ← Real.rpow_natCast, ← Real.rpow_neg ( by positivity ), ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
        -- We need to show that $1 / (1 - 1 / \sqrt{1 + \epsilon / 2}) \leq C / \epsilon$ for some $C > 0$.
        have h_bound : ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → 1 / (1 - 1 / Real.sqrt (1 + ε / 2)) ≤ C / ε := by
          use 8, by norm_num, fun ε hε₁ hε₂ => ?_;
          field_simp;
          rw [ div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( Real.sqrt ( ( 2 + ε ) / 2 ) - 1 ), Real.sqrt_nonneg ( ( 2 + ε ) / 2 ), Real.mul_self_sqrt ( show 0 ≤ ( 2 + ε ) / 2 by positivity ) ];
        exact ⟨ h_bound.choose, h_bound.choose_spec.1, fun ε hε₁ hε₂ m => le_trans ( h_geo_series_sum ε hε₁ hε₂ m ) ( h_bound.choose_spec.2 ε hε₁ hε₂ ) ⟩;
      obtain ⟨ C, hC₀, hC ⟩ := h_geo_series_bound; use C, hC₀; intros ε hε₀ hε₁ n hn m; convert mul_le_mul_of_nonneg_right ( hC ε hε₀ hε₁ m ) ( inv_nonneg.mpr ( Real.sqrt_nonneg n ) ) using 1 ; ring_nf; norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( by positivity : ( 0 :ℝ ) ≤ 1 + ε / 2 ) ] ; ring_nf;
      · rw [ Finset.sum_mul _ _ _ ] ; refine' Finset.sum_congr rfl fun _ _ => _ ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf; norm_num [ ← Real.sqrt_eq_rpow ] ; ring_nf;
        exact Or.inl ( by rw [ ← Real.rpow_neg ( by positivity ) ] ; ring_nf );
      · ring;
    obtain ⟨ C, hC₀, hC ⟩ := h_sum_bound;
    refine' ⟨ C, hC₀, fun ε hε₁ hε₂ n hn m => le_trans _ ( hC ε hε₁ hε₂ n hn m ) ⟩;
    gcongr;
    · exact Real.sqrt_pos.mpr ( mul_pos ( pow_pos ( by positivity ) _ ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hn; linarith [ div_pos zero_lt_two hε₁ ] ) ) ) );
    · (expose_names; exact geometric_R_rec_lower_bound n i ε hε₁ hε₂ hn)

/-
The fraction of candidates failing condition (i) is less than 1/3 for sufficiently large n and x.
-/
lemma bad_candidates_i_fraction_bound :
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card < 1/3 := by
    obtain ⟨ C, hC₀, hC ⟩ := bad_candidates_i_bound;
    use ⌈C * 6⌉₊ + 1;
    intro n hn;
    -- Choose $x₀$ such that $C W n / \sqrt{x₀} < 1/6$ and $x₀/2 \ge W$.
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℕ, ∀ x ≥ x₀, C * (W_sq n * n / (Nat.sqrt x : ℝ)) < 1 / 6 ∧ x / 2 ≥ W_sq n := by
      have hx₀ : Filter.Tendsto (fun x : ℕ => C * (W_sq n * n / (Nat.sqrt x : ℝ))) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul ( tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat |> Filter.Tendsto.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => by nlinarith [ Nat.lt_succ_sqrt y ] ⟩ );
      exact Filter.eventually_atTop.mp ( hx₀.eventually ( gt_mem_nhds <| by norm_num ) ) |> fun ⟨ x₀, hx₀ ⟩ ↦ ⟨ x₀ + 2 * W_sq n, fun x hx ↦ ⟨ hx₀ x <| by linarith, by omega ⟩ ⟩;
    use x₀; intros x hx; specialize hC n x ( by linarith ) ( hx₀ x hx |>.2 ) ; specialize hx₀ x hx; norm_num at *;
    nlinarith [ Nat.le_ceil ( C * 6 ), show ( n : ℝ ) ≥ ⌈C * 6⌉₊ + 1 by exact_mod_cast hn, inv_mul_cancel₀ ( by norm_cast; linarith : ( n : ℝ ) ≠ 0 ) ]

/-
The term involving the number of steps and the bound for large primes tends to 0 as x goes to infinity.
-/
lemma term_2_tendsto_zero (n : ℕ) (ε : ℝ) (hε : ε > 0) :
  Filter.Tendsto (fun x => ((max_k n x ε + 5 : ℝ) * ((W_sq n : ℝ) * n / Real.sqrt x))) Filter.atTop (nhds 0) := by
    by_cases hn : n = 0;
    · aesop;
    · -- We'll use the fact that `max_k` grows logarithmically with `x`.
      have h_max_k_log : Filter.Tendsto (fun x => (max_k n x ε : ℝ) / Real.sqrt x) Filter.atTop (nhds 0) := by
        have h_max_k_log : Filter.Tendsto (fun x => (Real.log ((x : ℝ) / n) / Real.log (1 + ε)) / Real.sqrt x) Filter.atTop (nhds 0) := by
          -- We can factor out the constant $1 / \log(1 + \epsilon)$ and use the fact that $\frac{\log x}{\sqrt{x}}$ tends to $0$ as $x$ tends to infinity.
          have h_log_sqrt : Filter.Tendsto (fun x => Real.log x / Real.sqrt x) Filter.atTop (nhds 0) := by
            -- Let $y = \sqrt{x}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{2 \log y}{y}$.
            suffices h_log_y : Filter.Tendsto (fun y => 2 * Real.log y / y) Filter.atTop (nhds 0) by
              have := h_log_y.comp ( show Filter.Tendsto ( fun x : ℝ => Real.sqrt x ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
            -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
            suffices h_log_z : Filter.Tendsto (fun z : ℝ => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
              exact h_log_z.congr ( by simp +contextual [div_eq_mul_inv, mul_assoc, mul_comm] );
            norm_num +zetaDelta at *;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [ mul_assoc ] using Filter.Tendsto.neg ( tendsto_const_nhds.mul ( Real.continuous_mul_log.tendsto 0 ) ) );
          have h_log_sqrt : Filter.Tendsto (fun x => (Real.log x - Real.log n) / Real.sqrt x) Filter.atTop (nhds 0) := by
            simpa [ sub_div ] using h_log_sqrt.sub ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.sqrt ) );
          convert h_log_sqrt.div_const ( Real.log ( 1 + ε ) ) |> Filter.Tendsto.congr' _ using 2;
          · ring;
          · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.log_div ( by positivity ) ( by positivity ) ] ; ring;
        refine' squeeze_zero_norm' _ ( h_max_k_log.comp tendsto_natCast_atTop_atTop );
        simp +zetaDelta at *;
        refine' ⟨ n + 1, fun x hx => _ ⟩ ; rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; gcongr;
        exact Nat.floor_le ( div_nonneg ( Real.log_nonneg <| by rw [ le_div_iff₀ <| by positivity ] ; norm_cast ; linarith ) <| Real.log_nonneg <| by linarith );
      -- We can factor out the constant term $(W_sq n * n)$ and use the fact that $(max_k n x ε : ℝ) / \sqrt{x}$ tends to $0$.
      have h_factor : Filter.Tendsto (fun x => ((max_k n x ε : ℝ) + 5) / Real.sqrt x) Filter.atTop (nhds 0) := by
        simpa [ add_div ] using h_max_k_log.add ( tendsto_const_nhds.mul ( tendsto_inverse_atTop_nhds_zero_nat.sqrt ) );
      convert h_factor.const_mul ( W_sq n * n : ℝ ) using 2 <;> ring

/-
The probability of a bad candidate for a given R is bounded by a simplified expression involving 1/sqrt(R) and W*n/sqrt(x).
-/
lemma prob_bad_candidates_ii_R_bound_simplified :
  ∃ C : ℝ, C > 0 ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x : ℕ, x / 2 ≥ W_sq n →
  ∀ R : ℕ, n ≤ R → R ≤ x →
  ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤
  C / ε * (1 / Real.sqrt R + (W_sq n : ℝ) * n / Real.sqrt x) := by
    obtain ⟨ C, hC₀, hC ⟩ := prob_bad_candidates_ii_R_bound;
    refine' ⟨ 6 * C, by positivity, fun ε hε₁ hε₂ => ⟨ ⌈2 / ε⌉₊ + 1, fun n hn x hx R hR₁ hR₂ => le_trans ( hC n x R ε ( by linarith [ Nat.le_ceil ( 2 / ε ), div_pos zero_lt_two hε₁ ] ) hx hR₁ hR₂ hε₁ ) _ ⟩ ⟩;
    -- Using the bound $|I_R|/R \le \epsilon + 1/R$ and the fact that $R \ge n \ge 1$, we get $|I_R|/R \le 1.5 \epsilon$.
    have h_I_R_bound : ((I_R_eps R ε).card : ℝ) / R ≤ 1.5 * ε := by
      have h_I_R_bound : ((I_R_eps R ε).card : ℝ) ≤ ε * R + 1 := by
        convert card_I_R_eps_le R ε ( by linarith [ show n > 0 from by linarith ] ) hε₁ using 1;
      rw [ div_le_iff₀ ] <;> norm_num <;> nlinarith [ show ( R : ℝ ) ≥ ⌈2 / ε⌉₊ + 1 by exact_mod_cast by linarith, Nat.le_ceil ( 2 / ε ), mul_div_cancel₀ 2 hε₁.ne' ];
    -- Using the bound $1/\sqrt{R}_{nat} \le 2/\sqrt{R}_{real}$ and similarly for $x$, we get the desired inequality.
    have h_sqrt_bound : (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x : ℝ)) ≤ 2 * (1 / Real.sqrt R + (W_sq n : ℝ) * n / Real.sqrt x) := by
      have h_sqrt_bound : (1 / (Nat.sqrt R : ℝ)) ≤ 2 / Real.sqrt R ∧ (1 / (Nat.sqrt x : ℝ)) ≤ 2 / Real.sqrt x := by
        constructor <;> rw [ div_le_div_iff₀ ] <;> norm_num;
        any_goals nlinarith [ Nat.lt_succ_sqrt x, Nat.lt_succ_sqrt R ];
        · rw [ Real.sqrt_le_left ] <;> norm_cast <;> nlinarith only [ Nat.lt_succ_sqrt R ];
        · rw [ Real.sqrt_le_left ] <;> norm_cast <;> nlinarith only [ Nat.lt_succ_sqrt x ];
      ring_nf at *; nlinarith [ show 0 ≤ ( W_sq n : ℝ ) * n by positivity ] ;
    refine le_trans ( mul_le_mul ( by simpa only [ mul_div_assoc ] using mul_le_mul_of_nonneg_left h_I_R_bound <| by positivity ) h_sqrt_bound ( by positivity ) <| by positivity ) ?_ ; ring_nf ; norm_num [ hε₁.ne', hε₂.ne' ];
    norm_num [ sq, mul_assoc, hε₁.ne' ] ; ring_nf;
    gcongr <;> norm_num

/-
The set of relevant primes for R is a subset of the set of relevant primes for x if R >= x.
-/
lemma relevant_primes_subset (n R x : ℕ) (h : R ≥ x) :
  relevant_primes n R x ⊆ relevant_primes n x x := by
    -- Since $R \geq x$, we have $\sqrt{R} \geq \sqrt{x}$. Therefore, $\max(n^2, \sqrt{R}) \geq \max(n^2, \sqrt{x})$.
    have h_max : max (n^2) (Nat.sqrt R) ≥ max (n^2) (Nat.sqrt x) := by
      exact max_le_max le_rfl ( Nat.sqrt_le_sqrt h );
    exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_Ioc.mpr ⟨ by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) ], by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ⟩, Finset.mem_filter.mp hp |>.2 ⟩

/-
The bound on the sum of relevant primes holds for the case x < R <= 2x.
-/
lemma sum_relevant_primes_bound_case_mid :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ),
    n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x →
    ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) ≤
    C * (1 / Real.sqrt R + (W_sq n : ℝ) * n / Real.sqrt x) := by
      -- By Lemma `sum_inv_sq_relevant_primes_bound_R`, we have that the sum of `1/p^2` over relevant primes is bounded by `C / sqrt(x)`.
      have sum_relevant_primes_bound_R : ∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2) ≤ C / Real.sqrt x := by
        -- Since $x < R$, `relevant_primes n R x` is a subset of `relevant_primes n x x` (by `relevant_primes_subset`).
        have h_subset : ∀ n x R : ℕ, x < R → relevant_primes n R x ⊆ relevant_primes n x x := by
          intros n x R hR; exact relevant_primes_subset n R x hR.le;
        have h_sum_bound : ∃ C : ℝ, C > 0 ∧ ∀ n x : ℕ, n > 0 → x / 2 ≥ W_sq n → ∑ p ∈ relevant_primes n x x, (1 / (p : ℝ)^2) ≤ C / Real.sqrt x := by
          obtain ⟨ C, hC₀, hC ⟩ := sum_inv_sq_relevant_primes_bound_R;
          refine' ⟨ C * 2, mul_pos hC₀ zero_lt_two, fun n x hn hx => _ ⟩;
          by_cases hx_ge_n : x ≥ n;
          · refine le_trans ( hC n x x hn hx hx_ge_n le_rfl ) ?_;
            rw [ div_le_div_iff₀ ];
            · rw [ mul_assoc ] ; gcongr ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; nlinarith [ Nat.lt_succ_sqrt x ] ⟩ ;
            · exact Nat.cast_pos.mpr ( Nat.sqrt_pos.mpr ( by linarith ) );
            · exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) );
          · rw [ show relevant_primes n x x = ∅ from _ ] ; norm_num ; positivity
            generalize_proofs at *; (
            ext p; simp [relevant_primes];
            exact fun h₁ h₂ h₃ => absurd h₃ ( by rw [ Nat.le_sqrt ] ; nlinarith [ Nat.sqrt_le x ] ));
        exact ⟨ h_sum_bound.choose, h_sum_bound.choose_spec.1, fun n x R hn hx hR hR' => le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( h_subset n x R hR ) fun _ _ _ => by positivity ) ( h_sum_bound.choose_spec.2 n x hn hx ) ⟩;
      -- By Lemma `count_multiples_in_interval`, we have that the number of relevant primes is at most `sqrt(2x)`.
      have relevant_primes_card_bound_R : ∃ C > 0, ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → (relevant_primes n R x).card ≤ C / 2 * (n : ℝ) * Real.sqrt x := by
        -- Since the number of relevant primes is at most sqrt(2x), we can bound it by 2*sqrt(x).
        have relevant_primes_card_bound_R : ∀ n x R : ℕ, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → (relevant_primes n R x).card ≤ 2 * Real.sqrt x := by
          intros n x R hn hx hx' hx''; refine' le_trans ( Nat.cast_le.mpr <| Finset.card_le_card <| show relevant_primes n R x ⊆ Finset.Icc 1 ( Nat.sqrt ( 2 * x ) ) from _ ) _;
          · exact fun p hp => Finset.mem_Icc.mpr ⟨ Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2, Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ⟩;
          · norm_num +zetaDelta at *;
            nlinarith only [ Real.sqrt_nonneg x, Real.sq_sqrt ( Nat.cast_nonneg x ), show ( Nat.sqrt ( 2 * x ) : ℝ ) ^ 2 ≤ 2 * x by norm_cast; linarith [ Nat.sqrt_le ( 2 * x ) ] ];
        exact ⟨ 4, by norm_num, fun n x R hn hx hx' hx'' => le_trans ( relevant_primes_card_bound_R n x R hn hx hx' hx'' ) ( by nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast, Real.sqrt_nonneg x ] ) ⟩;
      obtain ⟨ C₁, hC₁_pos, hC₁ ⟩ := sum_relevant_primes_bound_R;
      obtain ⟨ C₂, hC₂_pos, hC₂ ⟩ := relevant_primes_card_bound_R;
      refine' ⟨ 8 * ( C₁ + C₂ + 1 ), by positivity, fun n x R hn hx hx' hx'' => _ ⟩ ; specialize hC₁ n x R hn hx hx' hx'' ; specialize hC₂ n x R hn hx hx' hx'' ; simp_all +decide [ Finset.sum_add_distrib ];
      refine le_trans ( add_le_add hC₁ ( mul_le_mul_of_nonneg_right hC₂ <| by positivity ) ) ?_;
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( le_add_of_nonneg_left <| by positivity ) <| by positivity );
      field_simp;
      rw [ Real.sq_sqrt ( Nat.cast_nonneg _ ) ] ; rw [ div_le_div_iff_of_pos_right ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop_cat ) ] ; ring_nf;
      by_cases hx : x = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      nlinarith [ show ( n : ℝ ) * W_sq n ≥ 1 by exact one_le_mul_of_one_le_of_one_le ( mod_cast hn ) ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero 2 <| Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ), show ( n : ℝ ) * W_sq n ≥ 0 by positivity ]

/-
The expected number of bad a's for R in (x, 2x] is bounded.
-/
lemma expected_bad_a_bound_mid :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ),
    n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ε > 0 →
    (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card ≤
    C * ((I_R_eps R ε).card : ℝ) * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      obtain ⟨ C, hC ⟩ := sum_relevant_primes_bound_case_mid;
      -- Apply the bound from `sum_bad_a_ii_le_sum_bad_candidates` and `bad_candidates_prob_bound`.
      have h_bound : ∀ n x R ε, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ε > 0 →
          (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card ≤
          (∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0) / (candidates x (W_sq n)).card := by
            intros n x R ε hn hx hxR hR ε_pos
            have h_sum_bound : (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) ≤ (∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0) := by
              convert sum_bad_a_ii_le_sum_bad_candidates _ _ _ _ using 1;
            gcongr;
      obtain ⟨ C', hC' ⟩ := bad_candidates_prob_bound;
      refine' ⟨ C' * C, mul_pos hC'.1 hC.1, fun n x R ε hn hx hR hR' hε => le_trans ( h_bound n x R ε hn hx hR hR' hε ) _ ⟩;
      -- Apply the bound from `bad_candidates_prob_bound` to each term in the sum.
      have h_term_bound : ∀ a ∈ I_R_eps R ε, ∀ p ∈ relevant_primes n R x, (if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0) / (candidates x (W_sq n)).card ≤ C' * (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2)) := by
        intros a ha p hp
        by_cases haSF : a ∈ SF;
        · rw [ if_pos haSF ];
          apply hC'.right n x a p hn (by
          exact Finset.mem_filter.mp hp |>.2 |> fun h => by exact lt_of_le_of_lt ( Nat.le_max_left _ _ ) ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) ;) (by
          exact Finset.mem_filter.mp hp |>.2) hx;
        · simp [haSF];
          exact mul_nonneg hC'.1.le ( add_nonneg ( inv_nonneg.2 ( sq_nonneg _ ) ) ( div_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ) );
      have h_sum_bound : (∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, if a ∈ SF then ((bad_candidates x (W_sq n) a p).card : ℝ) else 0) / (candidates x (W_sq n)).card ≤ C' * (∑ a ∈ I_R_eps R ε, ∑ p ∈ relevant_primes n R x, (1 / (p : ℝ)^2 + (W_sq n : ℝ) / (x / 2))) := by
        simp +decide only [Finset.mul_sum _ _ _];
        simpa only [ Finset.sum_div _ _ _ ] using Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun p hp => h_term_bound a ha p hp;
      refine le_trans h_sum_bound ?_;
      simp_all +decide [mul_assoc];
      rw [ mul_left_comm ];
      gcongr;
      refine le_trans ( hC.2 n x R hn hx hR hR' ) ?_;
      gcongr;
      · linarith;
      · exact Nat.cast_pos.mpr ( Nat.sqrt_pos.mpr ( by linarith ) );
      · exact Real.le_sqrt_of_sq_le ( mod_cast Nat.sqrt_le' _ );
      · exact Nat.cast_pos.mpr ( Nat.sqrt_pos.mpr ( by linarith ) );
      · exact Real.le_sqrt_of_sq_le ( mod_cast Nat.sqrt_le' _ )

/-
Markov's inequality for finite sets with integer-valued functions.
-/
lemma markov_bound {α : Type*} (S : Finset α) (f : α → ℕ) (C : ℝ) (hC : C > 0) :
  ((S.filter (fun x => (f x : ℝ) > C)).card : ℝ) ≤ (∑ x ∈ S, (f x : ℝ)) / C := by
    rw [ le_div_iff₀' hC ];
    rw [ Finset.card_filter ];
    push_cast [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun x _ => by split_ifs <;> linarith;

/-
The probability of a bad candidate for R in (x, 2x] is bounded.
-/
lemma prob_bad_candidates_ii_R_bound_mid :
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (x : ℕ) (R : ℕ) (ε : ℝ),
    n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ε > 0 →
    ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤
    C / ε^2 * ((I_R_eps R ε).card : ℝ) / R * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      obtain ⟨C₁, hC₁⟩ : ∃ C₁ > 0, ∀ n x R ε, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ε > 0 → ((∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (candidates x (W_sq n)).card ≤ C₁ * ((I_R_eps R ε).card : ℝ) * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x))) := by
        exact expected_bad_a_bound_mid;
      refine' ⟨ C₁, hC₁.1, fun n x R ε hn hx hx' hx'' hε => _ ⟩;
      have h_markov : ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) ≤ (∑ n' ∈ candidates x (W_sq n), ((bad_a_ii n' R x n ε).card : ℝ)) / (ε^2 * R) := by
        apply markov_bound;
        exact mul_pos ( sq_pos_of_pos hε ) ( Nat.cast_pos.mpr ( by linarith ) );
      refine le_trans ( div_le_div_of_nonneg_right h_markov <| Nat.cast_nonneg _ ) ?_;
      convert mul_le_mul_of_nonneg_right ( hC₁.2 n x R ε hn hx hx' hx'' hε ) ( by positivity : 0 ≤ ( ε ^ 2 * R : ℝ ) ⁻¹ ) using 1 ; ring;
      ring

/-
For large enough n, the ratio |I_R|/R is bounded by 2*epsilon.
-/
lemma card_I_R_eps_ratio_bound :
  ∀ ε : ℝ, 0 < ε →
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ R : ℕ, R ≥ n →
  ((I_R_eps R ε).card : ℝ) / R ≤ 2 * ε := by
    intro ε hε_pos
    use Nat.ceil (1 / ε) + 1
    intro n hn R hR
    have h_card_I_R_eps : ((I_R_eps R ε).card : ℝ) ≤ ε * R + 1 := by
      have := card_I_R_eps_le R ε ( by linarith ) hε_pos; aesop;
    rw [ div_le_iff₀ ] <;> nlinarith [ show ( R : ℝ ) ≥ ⌈1 / ε⌉₊ + 1 by exact_mod_cast hn.trans hR, Nat.le_ceil ( 1 / ε ), one_div_mul_cancel hε_pos.ne' ]

/-
Simplified bound for the probability of a bad candidate for x < R <= 2x.
-/
lemma prob_bad_candidates_ii_R_bound_mid_simplified :
  ∃ C : ℝ, C > 0 ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x : ℕ, x / 2 ≥ W_sq n →
  ∀ R : ℕ, n ≤ R → x < R → R ≤ 2 * x →
  ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤
  C / ε * (1 / Real.sqrt R + (W_sq n : ℝ) * n / Real.sqrt x) := by
    obtain ⟨C₁, hC₁⟩ : ∃ C₁ > 0, ∀ n x R ε, n > 0 → x / 2 ≥ W_sq n → x < R → R ≤ 2 * x → ε > 0 → ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤ C₁ / ε^2 * ((I_R_eps R ε).card : ℝ) / R * (1 / (Nat.sqrt R : ℝ) + (W_sq n : ℝ) * n / (Nat.sqrt x)) := by
      exact prob_bad_candidates_ii_R_bound_mid
    generalize_proofs at *; (
    obtain ⟨C₂, hC₂⟩ : ∃ C₂ > 0, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ R : ℕ, R ≥ n → ((I_R_eps R ε).card : ℝ) / R ≤ C₂ * ε := by
      exact ⟨ 2, by norm_num, fun ε hε => by obtain ⟨ N₀, hN₀ ⟩ := card_I_R_eps_ratio_bound ε hε; exact ⟨ N₀, fun n hn R hR => by linarith [ hN₀ n hn R hR ] ⟩ ⟩
    generalize_proofs at *; (
    refine' ⟨ 2 * C₁ * C₂, mul_pos ( mul_pos two_pos hC₁.1 ) hC₂.1, fun ε hε₁ hε₂ => _ ⟩ ; obtain ⟨ N₀, hN₀ ⟩ := hC₂.2 ε hε₁ ; use Max.max N₀ 1 ; intros n hn x hx R hn' hx' hx'' ; by_cases hn'' : n = 0 <;> simp_all +decide [ division_def ] ;
    refine le_trans ( hC₁.2 n x R ε ( Nat.pos_of_ne_zero hn'' ) hx hx' hx'' hε₁ ) ?_;
    -- Apply the bounds from hC₁ and hC₂ to simplify the expression.
    have h_simp : C₁ * (ε^2)⁻¹ * (C₂ * ε) * ((R.sqrt : ℝ)⁻¹ + (W_sq n : ℝ) * n * (x.sqrt : ℝ)⁻¹) ≤ 2 * C₁ * C₂ * ε⁻¹ * ((Real.sqrt R)⁻¹ + (W_sq n : ℝ) * n * (Real.sqrt x)⁻¹) := by
      field_simp;
      rw [ mul_assoc ];
      rw [ mul_assoc, mul_assoc ] ; gcongr ;
      · linarith [ hC₁.1 ];
      · linarith [ hC₂.1 ];
      · rw [ mul_add ] ; gcongr <;> norm_num [ Nat.sqrt_le ] ; ring_nf ;
        · rw [ inv_le_comm₀ ] <;> norm_num;
          · nlinarith only [ show ( R : ℝ ) ≥ 1 by norm_cast; linarith, Real.mul_self_sqrt ( Nat.cast_nonneg R ), show ( R.sqrt : ℝ ) ≥ 1 by exact_mod_cast Nat.sqrt_pos.mpr ( by linarith ), show ( R : ℝ ) ≤ ( R.sqrt + 1 ) ^ 2 by norm_cast; linarith [ Nat.lt_succ_sqrt R ] ];
          · exact Nat.sqrt_pos.mpr ( by linarith );
          · linarith [ Nat.pos_of_ne_zero hn'' ];
        · rw [ mul_div, div_le_div_iff₀ ] <;> norm_num;
          · nlinarith only [ show ( W_sq n : ℝ ) * n ≥ 0 by positivity, show ( Real.sqrt x : ℝ ) ≤ x.sqrt + 1 by rw [ Real.sqrt_le_left ] <;> norm_cast <;> linarith [ Nat.lt_succ_sqrt x ], show ( x.sqrt : ℝ ) ≥ 1 by exact_mod_cast Nat.sqrt_pos.mpr ( by linarith ) ];
          · exact Nat.sqrt_pos.mpr ( by linarith );
          · linarith [ Nat.pos_of_ne_zero hn'' ]
    generalize_proofs at *; (
    refine le_trans ?_ h_simp
    generalize_proofs at *; (
    convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( hN₀ n hn.1 R hn' ) ( show 0 ≤ C₁ * ( ε ^ 2 ) ⁻¹ by exact mul_nonneg hC₁.1.le ( inv_nonneg.2 ( sq_nonneg ε ) ) ) ) ( show 0 ≤ ( R.sqrt : ℝ ) ⁻¹ + W_sq n * n * ( x.sqrt : ℝ ) ⁻¹ by positivity ) using 1 ; ring!;))))

/-
There exists a constant C such that the probability of a bad candidate is bounded by $C/\epsilon * (1/\sqrt{R} + W n / \sqrt{x})$ for all $R \ge n$.
-/
lemma prob_bad_candidates_ii_R_bound_combined :
  ∃ C : ℝ, C > 0 ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x : ℕ, x / 2 ≥ W_sq n →
  ∀ R : ℕ, n ≤ R →
  ((bad_candidates_ii_R R x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤
  C / ε * (1 / Real.sqrt R + (W_sq n : ℝ) * n / Real.sqrt x) := by
    -- By combining the results from lemmas `prob_bad_candidates_ii_R_bound_simplified` and `prob_bad_candidates_ii_R_bound_mid_simplified`, we can construct the desired constant `C`.
    obtain ⟨C1, hC1⟩ := prob_bad_candidates_ii_R_bound_simplified
    obtain ⟨C2, hC2⟩ := prob_bad_candidates_ii_R_bound_mid_simplified;
    use Max.max C1 C2 + 1;
    refine' ⟨ by linarith [ le_max_left C1 C2, le_max_right C1 C2 ], fun ε hε₁ hε₂ => _ ⟩;
    obtain ⟨ N₀₁, hN₀₁ ⟩ := hC1.2 ε hε₁ hε₂
    obtain ⟨ N₀₂, hN₀₂ ⟩ := hC2.2 ε hε₁ hε₂
    use Max.max N₀₁ N₀₂ + 1;
    intro n hn x hx R hR;
    by_cases hR' : R ≤ 2 * x;
    · by_cases hR'' : R ≤ x;
      · exact le_trans ( hN₀₁ n ( by linarith [ Nat.le_max_left N₀₁ N₀₂ ] ) x hx R hR hR'' ) ( mul_le_mul_of_nonneg_right ( by rw [ div_le_div_iff_of_pos_right hε₁ ] ; linarith [ le_max_left C1 C2, le_max_right C1 C2 ] ) ( by positivity ) );
      · refine le_trans ( hN₀₂ n ( by linarith [ le_max_left N₀₁ N₀₂, le_max_right N₀₁ N₀₂ ] ) x hx R hR ( by linarith ) hR' ) ?_;
        gcongr ; linarith [ le_max_right C1 C2 ];
    · rw [ bad_candidates_ii_R_empty_of_large_R ] <;> norm_num;
      · exact mul_nonneg ( div_nonneg ( add_nonneg ( le_max_of_le_left hC1.1.le ) zero_le_one ) hε₁.le ) ( add_nonneg ( inv_nonneg.2 ( Real.sqrt_nonneg _ ) ) ( div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( Real.sqrt_nonneg _ ) ) );
      · linarith;
      · exact hε₁

/-
The total failure probability is the sum of the failure probabilities for each R in the geometric progression.
-/
def total_failure_prob (n x : ℕ) (ε : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (max_k n x ε + 5),
    ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card

/-
The total failure probability is less than 1/6 for sufficiently large n and x.
-/
lemma total_failure_prob_bound :
  ∀ (ε : ℝ), 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  total_failure_prob n x ε < 1/6 := by
    intro ε hε_pos hε_lt_1
    obtain ⟨C₁, hC₁_pos, hC₁_bound⟩ := prob_bad_candidates_ii_R_bound_combined
    obtain ⟨C₂, hC₂_pos, hC₂_sum⟩ := sum_inv_sqrt_R_bound
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ x₀ : ℕ, ∀ x ≥ x₀, (C₁ / ε * ((max_k n x ε + 5 : ℝ) * ((W_sq n : ℝ) * n / Real.sqrt x))) < 1 / 12 := by
      -- By Lemma term_2_tendsto_zero, the term tends to zero as x goes to infinity. So, for any fixed n, we can choose x₀ large enough so that the term is less than 1/12.
      have h_term_zero : ∀ n : ℕ, Filter.Tendsto (fun x : ℕ => (C₁ / ε) * ((max_k n x ε + 5 : ℝ) * ((W_sq n : ℝ) * n / Real.sqrt x))) Filter.atTop (nhds 0) := by
        intro n;
        have := term_2_tendsto_zero n ε hε_pos;
        simpa using this.const_mul _;
      exact ⟨ 0, fun n hn => by rcases Metric.tendsto_atTop.mp ( h_term_zero n ) ( 1 / 12 ) ( by norm_num ) with ⟨ x₀, hx₀ ⟩ ; exact ⟨ x₀, fun x hx => by linarith [ abs_lt.mp ( hx₀ x hx ) ] ⟩ ⟩;
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, ∀ x : ℕ, x / 2 ≥ W_sq n → (∑ k ∈ Finset.range (max_k n x ε + 5), (C₁ / ε * (1 / Real.sqrt (geometric_R_rec n ε k)))) ≤ (C₁ / ε^2 * C₂ / Real.sqrt n) := by
      use Nat.ceil (2 / ε) + 1;
      intro n hn x hx; specialize hC₂_sum ε hε_pos hε_lt_1 n ( Nat.lt_of_ceil_lt hn ) ( max_k n x ε + 5 ) ; simp_all +decide [mul_assoc,
        mul_comm, mul_left_comm, div_eq_mul_inv] ;
      convert mul_le_mul_of_nonneg_left hC₂_sum ( show 0 ≤ C₁ * ε⁻¹ by positivity ) using 1 <;> ring_nf;
      rw [ Finset.mul_sum _ _ _ ];
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, (C₁ / ε^2 * C₂ / Real.sqrt n) < 1 / 12 := by
      have h_lim : Filter.Tendsto (fun n : ℕ => C₁ / ε^2 * C₂ / Real.sqrt n) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      simpa using h_lim.eventually ( gt_mem_nhds <| by norm_num );
    obtain ⟨N₃, hN₃⟩ : ∃ N₃ : ℕ, ∀ n ≥ N₃, ∀ x : ℕ, x / 2 ≥ W_sq n → ∀ k ∈ Finset.range (max_k n x ε + 5), ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤ C₁ / ε * (1 / Real.sqrt (geometric_R_rec n ε k) + (W_sq n : ℝ) * n / Real.sqrt x) := by
      obtain ⟨ N₃, hN₃ ⟩ := hC₁_bound ε hε_pos hε_lt_1;
      use N₃ + 1;
      intros n hn x hx k hk;
      apply hN₃ n (by linarith) x hx (geometric_R_rec n ε k) (by
      induction' k with k ih;
      · exact Nat.le_refl n;
      · exact Nat.le_floor <| by nlinarith [ ih <| Finset.mem_range.mpr <| Nat.lt_of_succ_lt <| Finset.mem_range.mp hk, show ( geometric_R_rec n ε k : ℝ ) ≥ n from mod_cast ih <| Finset.mem_range.mpr <| Nat.lt_of_succ_lt <| Finset.mem_range.mp hk ] ;);
    use Max.max N₀ ( Max.max N₁ ( Max.max N₂ N₃ ) );
    intro n hn
    obtain ⟨x₀, hx₀⟩ := hN₀ n (le_trans (le_max_left _ _) hn);
    use Max.max x₀ (W_sq n * 2);
    intros x hx
    have h_sum_bound : ∑ k ∈ Finset.range (max_k n x ε + 5), ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card ≤ ∑ k ∈ Finset.range (max_k n x ε + 5), C₁ / ε * (1 / Real.sqrt (geometric_R_rec n ε k) + (W_sq n : ℝ) * n / Real.sqrt x) := by
      exact Finset.sum_le_sum fun k hk => hN₃ n ( le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_right _ _ ) ) ) hn ) x ( by linarith [ Nat.div_add_mod x 2, Nat.mod_lt x two_pos, le_max_right x₀ ( W_sq n * 2 ) ] ) k hk;
    simp_all +decide [ Finset.sum_add_distrib, mul_add ];
    exact lt_of_le_of_lt h_sum_bound ( by have := hN₁ n hn.2.1 x ( by omega ) ; have := hN₂ n hn.2.2.1; have := hx₀ x hx.1; norm_num at *; linarith )

/-
For sufficiently large n and x, there exists a candidate n' that satisfies the GeometricGood_rec property.
-/
lemma exists_GeometricGood_rec :
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∃ n', GeometricGood_rec n n' x ε := by
    intro ε hε_pos hε_lt_1
    obtain ⟨N₀₁, hN₀₁⟩ : ∃ N₀₁ : ℕ, ∀ n ≥ N₀₁, ∃ x₀₁ : ℕ, ∀ x ≥ x₀₁, ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card < 1/3 := by
      exact bad_candidates_i_fraction_bound

    obtain ⟨N₀₂, hN₀₂⟩ : ∃ N₀₂ : ℕ, ∀ n ≥ N₀₂, ∃ x₀₂ : ℕ, ∀ x ≥ x₀₂, total_failure_prob n x ε < 1/6 := by
      exact total_failure_prob_bound ε hε_pos hε_lt_1;
    obtain ⟨N₀₃, hN₀₃⟩ : ∃ N₀₃ : ℕ, ∀ n ≥ N₀₃, ∃ x₀₃ : ℕ, ∀ x ≥ x₀₃, (candidates x (W_sq n)).card > 0 := by
      use 1;
      intro n hn
      use 2 * W_sq n + 1;
      intro x hx
      have h_candidates_nonempty : ∃ n' ∈ Finset.Icc (x / 2 + 1) x, W_sq n ∣ n' := by
        use W_sq n * ((x / 2) / W_sq n + 1);
        norm_num +zetaDelta at *;
        exact ⟨ by linarith [ Nat.div_add_mod ( x / 2 ) ( W_sq n ), Nat.mod_lt ( x / 2 ) ( show W_sq n > 0 from Nat.pos_of_ne_zero ( by exact mt Finset.prod_eq_zero_iff.mp ( by intros h; cases h; aesop ) ) ) ], by linarith [ Nat.div_mul_le_self ( x / 2 ) ( W_sq n ), Nat.div_mul_le_self x 2, Nat.div_add_mod x 2, Nat.mod_lt x two_pos ] ⟩;
      exact Finset.card_pos.mpr ⟨ h_candidates_nonempty.choose, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp h_candidates_nonempty.choose_spec.1 ], by linarith [ Finset.mem_Icc.mp h_candidates_nonempty.choose_spec.1 ] ⟩, h_candidates_nonempty.choose_spec.2 ⟩ ⟩;
    use Max.max N₀₁ ( Max.max N₀₂ N₀₃ ) + 1;
    intros n hn; obtain ⟨ x₀₁, hx₀₁ ⟩ := hN₀₁ n ( by linarith [ le_max_left N₀₁ ( max N₀₂ N₀₃ ) ] ) ; obtain ⟨ x₀₂, hx₀₂ ⟩ := hN₀₂ n ( by linarith [ le_max_right N₀₁ ( max N₀₂ N₀₃ ), le_max_left N₀₂ N₀₃ ] ) ; obtain ⟨ x₀₃, hx₀₃ ⟩ := hN₀₃ n ( by linarith [ le_max_right N₀₁ ( max N₀₂ N₀₃ ), le_max_right N₀₂ N₀₃ ] ) ; use Max.max x₀₁ ( Max.max x₀₂ x₀₃ ) + 1; intros x hx; specialize hx₀₁ x ( by linarith [ le_max_left x₀₁ ( Max.max x₀₂ x₀₃ ) ] ) ; specialize hx₀₂ x ( by linarith [ le_max_right x₀₁ ( Max.max x₀₂ x₀₃ ), le_max_left x₀₂ x₀₃ ] ) ; specialize hx₀₃ x ( by linarith [ le_max_right x₀₁ ( Max.max x₀₂ x₀₃ ), le_max_right x₀₂ x₀₃ ] ) ; norm_num at *;
    have h_exists_good : ((bad_candidates_i n x).card : ℝ) / (candidates x (W_sq n)).card + ∑ k ∈ Finset.range (max_k n x ε + 5), ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℝ) / (candidates x (W_sq n)).card < 1 := by
      linarith!;
    have h_exists_good : ∃ n' ∈ candidates x (W_sq n), n' ∉ bad_candidates_i n x ∧ ∀ k ∈ Finset.range (max_k n x ε + 5), n' ∉ bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n) := by
      have h_sum : ((bad_candidates_i n x).card : ℝ) + ∑ k ∈ Finset.range (max_k n x ε + 5), ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℝ) < (candidates x (W_sq n)).card := by
        rw [ ← Finset.sum_div _ _ _ ] at *;
        rwa [ ← add_div, div_lt_one ( Nat.cast_pos.mpr <| Finset.card_pos.mpr hx₀₃ ) ] at h_exists_good
      contrapose! h_sum;
      have h_sum : (candidates x (W_sq n)).card ≤ (bad_candidates_i n x).card + ∑ k ∈ Finset.range (max_k n x ε + 5), ((bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)).card : ℕ) := by
        have h_union : candidates x (W_sq n) ⊆ bad_candidates_i n x ∪ Finset.biUnion (Finset.range (max_k n x ε + 5)) (fun k => bad_candidates_ii_R (geometric_R_rec n ε k) x n ε (W_sq n)) := by
          intro n' hn'; specialize h_sum n' hn'; by_cases h : n' ∈ bad_candidates_i n x <;> aesop;
        exact le_trans ( Finset.card_le_card h_union ) ( Finset.card_union_le _ _ ) |> le_trans <| add_le_add_left ( Finset.card_biUnion_le ) _;
      exact_mod_cast h_sum;
    exact h_exists_good

/-
For sufficiently large n and x, there exists a candidate n' that satisfies the GeometricGood_rec property.
-/
lemma exists_GeometricGood_rec_v2 :
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∃ n', GeometricGood_rec n n' x ε := by
    -- Apply the lemma `exists_GeometricGood_rec` to conclude the proof.
    apply exists_GeometricGood_rec

/-
If a set has good density at R1, and R is close to R1 (within factor 1+epsilon), then it has good density at R.
-/
lemma density_interpolation_lemma (S : Set ℕ) (R1 R2 R : ℕ) (ε C : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hR1 : R1 > 0)
    (hR2 : R2 ≤ (1 + ε) * R1)
    (hR : R1 ≤ R ∧ R ≤ R2)
    (h_dens : ((S ∩ Finset.Icc 1 R1).ncard : ℝ) / R1 ≥ 6 / Real.pi^2 - C * ε) :
    ((S ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥ 6 / Real.pi^2 - (C + 1) * ε := by
      -- Using the density bound for $R_1$, this is $\ge (6/\pi^2 - C\epsilon) \frac{R_1}{R}$.
      have h_dens_R : (S ∩ (Finset.Icc 1 R)).ncard / (R : ℝ) ≥ (6 / Real.pi ^ 2 - C * ε) * (R1 / R : ℝ) := by
        refine le_trans ( mul_le_mul_of_nonneg_right h_dens <| by positivity ) ?_;
        rw [ div_mul_div_cancel₀ ( by positivity ) ];
        gcongr;
        · exact Set.Finite.subset ( Finset.finite_toSet ( Finset.Icc 1 R ) ) fun x hx => hx.2;
        · linarith;
      -- Since $R \le R_2 \le (1+\epsilon)R_1$, we have $\frac{R_1}{R} \ge \frac{1}{1+\epsilon} \ge 1 - \epsilon$.
      have h_frac_R1_R : (R1 : ℝ) / R ≥ 1 - ε := by
        rw [ ge_iff_le, le_div_iff₀ ] <;> nlinarith [ show ( R1 : ℝ ) ≥ 1 by norm_cast, show ( R : ℝ ) ≥ R1 by norm_cast; linarith, show ( R2 : ℝ ) ≥ R by norm_cast; linarith ];
      contrapose! h_dens;
      refine' lt_of_le_of_lt _ ( lt_sub_iff_add_lt'.mpr _ );
      rotate_left;
      exact 1;
      · nlinarith [ show ( R1 : ℝ ) / R ≤ 1 by rw [ div_le_iff₀ ] <;> norm_cast <;> linarith ];
      · exact div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by simp [ Set.ncard_eq_toFinset_card' ] ) <| by positivity;

/-
If n' is a good candidate, then n' + a is squarefree for all squarefree a <= n.
-/
lemma GeometricGood_rec_implies_condition_i (n n' x : ℕ) (ε : ℝ)
  (hgood : GeometricGood_rec n n' x ε) :
  ∀ a ∈ Finset.Icc 1 n, a ∈ SF → n' + a ∈ SF := by
    -- Since $n'$ is not in bad_candidates_i, for all $a \in [1, n]$, if $a$ is squarefree, then $n' + a$ must be squarefree.
    have h_not_bad_i : n' ∉ bad_candidates_i n x := by
      exact hgood.2.1;
    contrapose! h_not_bad_i;
    obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := h_not_bad_i;
    have := hgood.1;
    obtain ⟨ p, hp₁, hp₂, hp₃, hp₄ ⟩ : ∃ p, Nat.Prime p ∧ p > n^2 ∧ p^2 ∣ n' + a := by
      apply key_construction_i_deterministic;
      · unfold candidates at this; aesop;
      · assumption;
      · assumption;
      · exact ha₃;
    simp_all +decide [ candidates, bad_candidates_i ];
    refine' ⟨ a, ha₁, p, ⟨ ⟨ hp₂, _ ⟩, hp₁ ⟩, _ ⟩;
    · rw [ Nat.le_sqrt ] ; nlinarith [ show hp₃ > 0 from Nat.pos_of_ne_zero ( by aesop_cat ) ];
    · exact Finset.mem_filter.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, this.2 ⟩, by aesop ⟩

/-
The terms of the recursive geometric progression are always positive if n > 0 and epsilon > 0.
-/
lemma geometric_R_rec_pos (n : ℕ) (ε : ℝ) (k : ℕ) (hn : n > 0) (hε : 0 < ε) :
  geometric_R_rec n ε k > 0 := by
    induction' k with k ih <;> [ exact hn; exact Nat.floor_pos.mpr ( by nlinarith [ ( by norm_cast : ( 0 :ℝ ) < n ), show ( geometric_R_rec n ε k : ℝ ) ≥ 1 from Nat.one_le_cast.mpr ih ] ) ] ;

/-
The recursive geometric progression grows at most by a factor of (1 + epsilon) at each step.
-/
lemma geometric_R_rec_growth (n : ℕ) (ε : ℝ) (k : ℕ) (hε : 0 < ε) :
  (geometric_R_rec n ε (k + 1) : ℝ) ≤ (1 + ε) * geometric_R_rec n ε k := by
    exact Nat.floor_le ( by positivity )

/-
Helper lemma: If the density is good at R_k, it is good at any R in [R_k, R_{k+1}] (with a slightly worse constant).
-/
lemma density_interpolation_geometric (n : ℕ) (ε : ℝ) (k : ℕ) (R : ℕ) (C : ℝ) (S : Set ℕ)
  (hε : 0 < ε) (hε1 : ε < 1)
  (hn : n > 0)
  (h_range : geometric_R_rec n ε k ≤ R ∧ R ≤ geometric_R_rec n ε (k + 1))
  (h_dens : ((S ∩ Finset.Icc 1 (geometric_R_rec n ε k)).ncard : ℝ) / (geometric_R_rec n ε k) ≥ 6 / Real.pi^2 - C * ε) :
  ((S ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥ 6 / Real.pi^2 - (C + 1) * ε := by
    apply density_interpolation_lemma S (geometric_R_rec n ε k) (geometric_R_rec n ε (k + 1)) R ε C hε hε1 (geometric_R_rec_pos n ε k hn hε) (geometric_R_rec_growth n ε k hε) h_range h_dens

/-
The recursive geometric progression is non-decreasing.
-/
lemma geometric_R_rec_monotone
  (n : ℕ) (ε : ℝ) (k : ℕ) (hε : 0 < ε) :
  geometric_R_rec n ε k ≤ geometric_R_rec n ε (k + 1) := by
  -- unfold the recursive definition at k+1
  change geometric_R_rec n ε k
      ≤ Nat.floor ((1 + ε) * (geometric_R_rec n ε k : ℝ))

  -- it suffices to prove the real inequality before applying floor
  apply Nat.le_floor

  have h_mul :
      (geometric_R_rec n ε k : ℝ)
        ≤ (1 + ε) * (geometric_R_rec n ε k : ℝ) := by
    have h₁ : (1 : ℝ) ≤ 1 + ε := by
      have : (0 : ℝ) ≤ ε := le_of_lt hε
      linarith
    have h₂ : (0 : ℝ) ≤ (geometric_R_rec n ε k : ℝ) := by
      exact_mod_cast Nat.zero_le _
    -- multiply inequality 1 ≤ 1+ε by a nonnegative number
    simpa [one_mul] using mul_le_mul_of_nonneg_right h₁ h₂

  simpa using h_mul

/-
If n' is a GeometricGood candidate, then the number of bad elements up to R_k is bounded by C * epsilon * R_k, provided R_k <= n'.
-/
lemma bad_upto_bound_rec :
  ∃ C : ℝ, C > 0 ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ≤ max_k n x ε + 5,
  geometric_R_rec n ε k ≤ n' →
  ((bad_upto n' (geometric_R_rec n ε k)).card : ℝ) ≤ C * ε * (geometric_R_rec n ε k) := by
    -- Let $C_{interval}$ be the constant from `bad_in_interval_bound_rec`.
    obtain ⟨C_interval, hC_interval_pos, hC_interval⟩ := bad_in_interval_bound_rec_v4;
    -- Let $C_{sum}$ be the constant from `geometric_sum_bound`.
    obtain ⟨C_sum, hC_sum_pos, hC_sum⟩ := geometric_sum_bound;
    use C_interval * C_sum;
    refine' ⟨ mul_pos hC_interval_pos hC_sum_pos, _ ⟩;
    intro ε hε hε1
    obtain ⟨N₀, hN₀⟩ := hC_interval ε hε hε1
    obtain ⟨N₀', hN₀'⟩ := hC_sum ε hε hε1
    use max N₀ N₀' + 1;
    intro n hn
    obtain ⟨x₀, hx₀⟩ := hN₀ n (by linarith [Nat.le_max_left N₀ N₀'])
    use max x₀ (2 * n) + 1
    intro x hx n' hn' k hk hk_le_n'
    have h_sum : ((bad_upto n' (geometric_R_rec n ε k)).card : ℝ) ≤ ∑ j ∈ Finset.range k, ((bad_in_interval n' (geometric_R_rec n ε j) ε).card : ℝ) := by
      have h_sum : bad_upto n' (geometric_R_rec n ε k) ⊆ Finset.biUnion (Finset.range k) (fun j => bad_in_interval n' (geometric_R_rec n ε j) ε) := by
        apply bad_upto_subset;
        · grind;
        · exact GeometricGood_rec_implies_condition_i n n' x ε hn' |> fun h => by simpa using h;
      exact_mod_cast le_trans ( Finset.card_le_card h_sum ) ( Finset.card_biUnion_le );
    refine le_trans h_sum ?_;
    refine' le_trans ( Finset.sum_le_sum fun i hi => hx₀ x ( by linarith [ Nat.le_max_left x₀ ( 2 * n ) ] ) n' hn' i ( Finset.mem_range.mpr ( by linarith [ Finset.mem_range.mp hi ] ) ) _ ) _;
    · have h_bound : n' ≤ x := by
        exact hn'.1 |> fun h => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp h |>.1 ) ] ;
      have h_bound : ⌊(1 + ε) * (geometric_R_rec n ε i : ℝ)⌋₊ ≤ x := by
        have h_bound : geometric_R_rec n ε (i + 1) ≤ x := by
          have h_bound : geometric_R_rec n ε (i + 1) ≤ geometric_R_rec n ε k := by
            have h_bound : ∀ j, i + 1 ≤ j → j ≤ k → geometric_R_rec n ε (i + 1) ≤ geometric_R_rec n ε j := by
              intros j hj₁ hj₂
              induction' hj₁ with j hj ih;
              · grind;
              · exact le_trans ( ih ( Nat.le_of_succ_le hj₂ ) ) ( geometric_R_rec_monotone n ε j hε );
            exact h_bound k ( by linarith [ Finset.mem_range.mp hi ] ) ( by linarith [ Finset.mem_range.mp hi ] );
          linarith;
        convert h_bound using 1;
      linarith;
    · convert mul_le_mul_of_nonneg_left ( hN₀' n ( by linarith [ Nat.le_max_right N₀ N₀' ] ) k ) ( show 0 ≤ C_interval * ε ^ 2 by positivity ) using 1 ; ring_nf;
      · rw [ Finset.mul_sum _ _ _ ];
      · grind

/-
For any epsilon, for sufficiently large R, the density of squarefree numbers up to R is at least 6/pi^2 - epsilon.
-/
lemma SF_density_lower_bound :
  ∀ ε : ℝ, 0 < ε →
  ∃ N₀ : ℕ, ∀ R ≥ N₀,
  ((Finset.Icc 1 R).filter (fun x => x ∈ SF)).card / (R : ℝ) ≥ 6 / Real.pi^2 - ε := by
    intro ε hε_pos
    have h_density : ∃ C : ℝ, C > 0 ∧ ∀ R : ℕ, R > 0 → abs (((Finset.Icc 1 R).filter (fun x => x ∈ SF)).card - (6 / Real.pi^2) * R) ≤ C * Real.sqrt R := by
      have := SF_count_bound;
      exact ⟨ this.choose, this.choose_spec.1, fun R hR => le_trans ( this.choose_spec.2 R hR ) ( mul_le_mul_of_nonneg_left ( Real.le_sqrt_of_sq_le ( mod_cast Nat.sqrt_le' _ ) ) this.choose_spec.1.le ) ⟩;
    obtain ⟨ C, hC₀, hC ⟩ := h_density; use ⌈ ( C / ε ) ^ 2⌉₊ + 1; intro R hR; rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;> norm_num at * <;> try nlinarith;
    have := hC R ( by linarith ) ; rw [ abs_le ] at this ; nlinarith [ show ( R : ℝ ) ≥ ⌈ ( C / ε ) ^ 2⌉₊ + 1 by exact_mod_cast hR, Nat.le_ceil ( ( C / ε ) ^ 2 ), Real.sqrt_nonneg R, Real.sq_sqrt <| Nat.cast_nonneg R, mul_div_cancel₀ C hε_pos.ne.symm, pow_two_nonneg ( Real.sqrt R - C / ε ), Real.mul_self_sqrt <| Nat.cast_nonneg R ] ;

/-
If n' is a GeometricGood candidate, then the density of good elements at each point in the geometric progression is close to 6/pi^2.
-/
lemma GeometricGood_rec_implies_density_at_points_strong :
  ∃ C : ℝ, C > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ k ≤ max_k n x ε + 5,
  let R := geometric_R_rec n ε k
  R ≤ n' →
  let S := {a | a ∈ SF ∧ n' + a ∈ SF}
  ((S ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥ 6 / Real.pi^2 - C * ε := by
    obtain ⟨C₁, hC₁⟩ := bad_upto_bound_rec;
    field_simp;
    refine' ⟨ 6 + C₁, by linarith, fun ε hε₁ hε₂ => _ ⟩;
    obtain ⟨ N₀, hN₀ ⟩ := SF_density_lower_bound ( ε / 2 ) ( half_pos hε₁ );
    obtain ⟨ N₁, hN₁ ⟩ := hC₁.2 ε hε₁ hε₂;
    use Max.max N₀ N₁ + 1;
    intro n hn; obtain ⟨ x₀, hx₀ ⟩ := hN₁ n ( by linarith [ le_max_right N₀ N₁ ] ) ; use x₀; intros x hx n' hn' k hk hk'; specialize hx₀ x hx n' hn' k hk hk'; specialize hN₀ ( geometric_R_rec n ε k ) ( by
      -- By definition of $geometric_R_rec$, we know that $geometric_R_rec n ε k \geq n$ for all $k$.
      have h_geometric_R_rec_ge_n : ∀ k, geometric_R_rec n ε k ≥ n := by
        intro k; induction' k with k ih <;> norm_num [ *, geometric_R_rec ] ;
        exact Nat.le_floor <| by nlinarith [ show ( geometric_R_rec n ε k : ℝ ) ≥ n by exact_mod_cast ih ] ;
      linarith [ h_geometric_R_rec_ge_n k, le_max_left N₀ N₁, le_max_right N₀ N₁ ] ) ; norm_num at *;
    -- The number of good elements is at least the number of squarefree elements minus the number of bad elements.
    have h_good_elements : (({a | a ∈ SF ∧ n' + a ∈ SF} ∩ Set.Icc 1 (geometric_R_rec n ε k)).ncard : ℝ) ≥ ((Finset.Icc 1 (geometric_R_rec n ε k)).filter (fun x => x ∈ SF)).card - ((bad_upto n' (geometric_R_rec n ε k)).card : ℝ) := by
      rw [ ← Set.ncard_coe_finset ];
      rw [ show { a | a ∈ SF ∧ n' + a ∈ SF } ∩ Set.Icc 1 ( geometric_R_rec n ε k ) = ( Finset.filter ( fun x => x ∈ SF ) ( Finset.Icc 1 ( geometric_R_rec n ε k ) ) ) \ ( bad_upto n' ( geometric_R_rec n ε k ) ) from ?_ ];
      · rw [ Set.ncard_coe_finset, Set.ncard_coe_finset ];
        rw [ Finset.card_sdiff ] ; norm_num;
        rw [ Nat.cast_sub ];
        · linarith [ show ( Finset.card ( bad_upto n' ( geometric_R_rec n ε k ) ∩ Finset.filter ( fun x => x ∈ SF ) ( Finset.Icc 1 ( geometric_R_rec n ε k ) ) ) : ℝ ) ≤ Finset.card ( bad_upto n' ( geometric_R_rec n ε k ) ) from mod_cast Finset.card_mono <| Finset.inter_subset_left ];
        · exact Finset.card_le_card fun x hx => by aesop;
      · ext; simp [bad_upto];
        grind;
    -- Substitute the lower bound for the number of good elements into the inequality.
    have h_subst : 6 / Real.pi^2 ≤ (({a | a ∈ SF ∧ n' + a ∈ SF} ∩ Set.Icc 1 (geometric_R_rec n ε k)).ncard : ℝ) / (geometric_R_rec n ε k) + C₁ * ε + ε / 2 := by
      refine le_trans hN₀ ?_;
      norm_num +zetaDelta at *;
      rw [ div_add', div_le_div_iff_of_pos_right ] <;> nlinarith [ show ( geometric_R_rec n ε k : ℝ ) > 0 from Nat.cast_pos.mpr ( geometric_R_rec_pos n ε k ( by linarith [ le_max_left N₀ N₁, le_max_right N₀ N₁ ] ) ( by linarith [ le_max_left N₀ N₁, le_max_right N₀ N₁ ] ) ) ];
    field_simp;
    rw [ div_le_iff₀ ] at h_subst <;> nlinarith [ Real.pi_gt_three, pow_pos Real.pi_pos 2 ]

/-
If n' is a GeometricGood candidate, then condition (ii) of the Key Proposition holds.
-/
lemma GeometricGood_rec_implies_condition_ii :
  ∃ C_ii : ℝ, C_ii > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  ∀ R : ℕ, n ≤ R → R ≤ n' →
  let numerator := ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n' + a ∈ SF)).card
  (numerator : ℝ) / R ≥ 6 / Real.pi^2 - C_ii * ε := by
    -- Set C_ii = C + 1.
    obtain ⟨C, hC_pos, hC⟩ := GeometricGood_rec_implies_density_at_points_strong;
    refine' ⟨ C + 1, _, _ ⟩ <;> try linarith;
    intro ε hε₁ hε₂
    obtain ⟨N₀, hN₀⟩ := hC ε hε₁ hε₂
    obtain ⟨N₀', hN₀'⟩ := geometric_covers_x ε hε₁ hε₂
    use max N₀ N₀' + 1;
    intro n hn
    obtain ⟨ x₀, hx₀ ⟩ := hN₀ n ( by linarith [ le_max_left N₀ N₀' ] );
    use x₀ + n + 1;
    intro x hx n' hn' R hR₁ hR₂
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k ≤ max_k n x ε + 5, geometric_R_rec n ε k ≤ R ∧ R ≤ geometric_R_rec n ε (k + 1) := by
      have h_exists_k : ∃ k ≤ max_k n x ε + 4, geometric_R_rec n ε k ≤ R ∧ R ≤ geometric_R_rec n ε (k + 1) := by
        have h_exists_k : ∃ k ≤ max_k n x ε + 4, geometric_R_rec n ε k ≤ R ∧ R ≤ geometric_R_rec n ε (k + 1) := by
          have h_exists_k : ∃ k ≤ max_k n x ε + 4, R ≤ geometric_R_rec n ε (k + 1) := by
            have h_exists_k : R ≤ geometric_R_rec n ε (max_k n x ε + 4) := by
              have hR_le_x : R ≤ x := by
                exact le_trans hR₂ ( hn'.1 |> fun h => Finset.mem_Icc.mp ( Finset.mem_filter.mp h |>.1 ) |> fun h => h.2 );
              exact le_trans hR_le_x ( hN₀' n ( by linarith [ Nat.le_max_right N₀ N₀' ] ) x ( by linarith ) );
            exact ⟨ max_k n x ε + 3, by linarith, h_exists_k ⟩
          contrapose! h_exists_k;
          intro k hk; induction' k with k ih <;> norm_num at *;
          · exact h_exists_k 0 bot_le ( by exact Nat.le_trans ( by exact Nat.le_refl _ ) hR₁ );
          · exact h_exists_k _ ( by linarith ) ( by linarith [ ih ( by linarith ) ] )
        exact h_exists_k;
      exact ⟨ h_exists_k.choose, Nat.le_succ_of_le h_exists_k.choose_spec.1, h_exists_k.choose_spec.2.1, h_exists_k.choose_spec.2.2 ⟩;
    have := hx₀ x ( by linarith ) n' hn' k hk₁ ( by linarith );
    convert density_interpolation_geometric n ε k R C { a | a ∈ SF ∧ n' + a ∈ SF } hε₁ hε₂ ( by linarith [ Nat.le_max_left N₀ N₀', Nat.le_max_right N₀ N₀' ] ) ⟨ hk₂.1, hk₂.2 ⟩ this using 1;
    rw [ ← Set.ncard_coe_finset ] ; congr ; ext ; aesop

/-
If n' is a GeometricGood candidate, then it satisfies the conclusion of the Key Proposition.
-/
lemma GeometricGood_implies_PropositionKey :
  ∃ C_key : ℝ, C_key > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∃ x₀ : ℕ, ∀ x ≥ x₀,
  ∀ n' : ℕ, GeometricGood_rec n n' x ε →
  PropositionKey_conclusion n n' ε C_key := by
    -- Let's choose C_key from GeometricGood_rec_implies_condition_ii.
    obtain ⟨C_ii, hC_ii_pos, hC_ii⟩ := GeometricGood_rec_implies_condition_ii
    use C_ii;
    exact ⟨ hC_ii_pos, fun ε hε₁ hε₂ => by obtain ⟨ N₀, hN₀ ⟩ := hC_ii ε hε₁ hε₂; exact ⟨ N₀, fun n hn => by obtain ⟨ x₀, hx₀ ⟩ := hN₀ n hn; exact ⟨ x₀, fun x hx n' hn' => ⟨ by simpa using GeometricGood_rec_implies_condition_i n n' x ε hn', hx₀ x hx n' hn' ⟩ ⟩ ⟩ ⟩

/-
Key Proposition: For any epsilon and sufficiently large n, there exist arbitrarily large n' satisfying properties (i) and (ii).
-/
theorem PropositionKey :
  ∃ C : ℝ, C > 0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
  ∀ M : ℕ, ∃ n' ≥ M, PropositionKey_conclusion n n' ε C := by
    obtain ⟨C_key, hC_key_pos, hC_key⟩ := GeometricGood_implies_PropositionKey;
    use C_key;
    -- By combining the results from hC_key and exists_GeometricGood_rec_v2, we can conclude the proof.
    have h_combined : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀, ∀ n ≥ N₀, ∃ x₀, ∀ x ≥ x₀, ∃ n', GeometricGood_rec n n' x ε ∧ n' ≥ x / 2 := by
      intro ε hε_pos hε_lt_1
      obtain ⟨N₀, hN₀⟩ := exists_GeometricGood_rec_v2 ε hε_pos hε_lt_1
      use N₀ + 1
      intro n hn
      obtain ⟨x₀, hx₀⟩ := hN₀ n (by linarith);
      use x₀ + 2 * W_sq n + 1;
      intro x hx
      obtain ⟨n', hn'⟩ := hx₀ x (by linarith);
      exact ⟨ n', hn', Nat.le_of_not_lt fun h => by have := hn'.1; unfold candidates at this; norm_num at this; omega ⟩;
    refine' ⟨ hC_key_pos, fun ε hε₁ hε₂ => _ ⟩;
    obtain ⟨ N₀, hN₀ ⟩ := h_combined ε hε₁ hε₂;
    obtain ⟨ N₁, hN₁ ⟩ := hC_key ε hε₁ hε₂;
    use Max.max N₀ N₁;
    intros n hn M
    obtain ⟨ x₀, hx₀ ⟩ := hN₀ n (le_trans (le_max_left _ _) hn)
    obtain ⟨ x₁, hx₁ ⟩ := hN₁ n (le_trans (le_max_right _ _) hn);
    obtain ⟨ n', hn'₁, hn'₂ ⟩ := hx₀ ( 2 * M + x₁ + x₀ + 1 ) ( by linarith ) ; exact ⟨ n', by omega, hx₁ _ ( by omega ) _ hn'₁ ⟩ ;

/-
The set A is the union of sets of squarefree numbers a in (n_k, n_{k+1}] such that n_{k+1} + a is squarefree.
-/
def constructed_A (n : ℕ → ℕ) : Set ℕ :=
  ⋃ k, { a | a ∈ Set.Ioc (n k) (n (k+1)) ∧ a ∈ SF ∧ n (k+1) + a ∈ SF }

/-
The sequence n_k satisfies the properties required for the construction of A.
-/
def SequenceProperties (n : ℕ → ℕ) (C : ℝ) : Prop :=
  (∀ k ≥ 1, n k < n (k+1)) ∧
  (∀ k ≥ 1, ∀ a ∈ Finset.Icc 1 (n k), a ∈ SF → n (k+1) + a ∈ SF) ∧
  (∀ k ≥ 1, ∀ R, n k ≤ R → R ≤ n (k+1) →
    ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n (k+1) + a ∈ SF)).card / (R : ℝ) ≥ 6 / Real.pi^2 - C / k) ∧
  (∀ k ≥ 1, n (k+1) ≥ (k+1) * n k)

/-
C_seq is the constant from PropositionKey. N_seq is the threshold function from PropositionKey.
-/
noncomputable def C_seq : ℝ := Classical.choose PropositionKey

lemma C_seq_pos : C_seq > 0 := (Classical.choose_spec PropositionKey).1

noncomputable def N_seq (ε : ℝ) : ℕ :=
  if h : 0 < ε ∧ ε < 1 then
    Classical.choose ((Classical.choose_spec PropositionKey).2 ε h.1 h.2)
  else 0

/-
epsilon_seq k is 1/(k+1). It is between 0 and 1 for k >= 1.
-/
noncomputable def epsilon_seq (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

lemma epsilon_seq_valid (k : ℕ) (hk : k ≥ 1) : 0 < epsilon_seq k ∧ epsilon_seq k < 1 := by
  exact ⟨ by rw [ epsilon_seq ] ; exact one_div_pos.mpr ( by positivity ), by rw [ epsilon_seq ] ; exact div_lt_self zero_lt_one ( by norm_cast; linarith ) ⟩

/-
N_seq satisfies the property that for any n >= N_seq(epsilon), and any M, there exists n' >= M satisfying the Key Proposition conclusion.
-/
lemma N_seq_spec (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
  ∀ n ≥ N_seq ε, ∀ M : ℕ, ∃ n' ≥ M, PropositionKey_conclusion n n' ε C_seq :=
  by
    simp [N_seq, hε, hε1]
    exact Classical.choose_spec ((Classical.choose_spec PropositionKey).2 ε hε hε1)

/-
n_seq is the sequence of natural numbers constructed to satisfy the properties.
-/
noncomputable def next_val (n : ℕ) (k : ℕ) : ℕ :=
  let ε := epsilon_seq k
  let M := max ((k + 1) * n) (N_seq (epsilon_seq (k + 1)))
  if h : n ≥ N_seq ε ∧ 0 < ε ∧ ε < 1 then
    Classical.choose (N_seq_spec ε h.2.1 h.2.2 n h.1 M)
  else
    M + 1

noncomputable def n_seq : ℕ → ℕ
| 0 => 1
| 1 => N_seq (epsilon_seq 1) + 1
| (k + 2) => next_val (n_seq (k + 1)) (k + 1)

/-
The terms of n_seq are positive.
-/
lemma n_seq_pos (k : ℕ) : n_seq k > 0 := by
  induction' k using Nat.strong_induction_on with k ih;
  rcases k with ( _ | _ | k ) <;> norm_num [ n_seq ];
  unfold next_val;
  simp +zetaDelta at *;
  split_ifs <;> norm_num [ ih ];
  have := Classical.choose_spec ( N_seq_spec ( epsilon_seq ( k + 1 ) ) ( by linarith ) ( by linarith ) ( n_seq ( k + 1 ) ) ( by linarith ) ( max ( ( k + 1 + 1 ) * n_seq ( k + 1 ) ) ( N_seq ( epsilon_seq ( k + 1 + 1 ) ) ) ) );
  grind

/-
n_seq grows at least factorially (or rather, n_{k+1} >= (k+1) n_k).
-/
lemma n_seq_growth (k : ℕ) : n_seq (k + 1) ≥ (k + 1) * n_seq k := by
  -- By definition of $next\_val$, we know that $n\_seq (k + 1) \geq (k + 1) * n\_seq k$.
  have h_next : ∀ n k, n > 0 → next_val n k ≥ (k + 1) * n := by
    unfold next_val;
    norm_num +zetaDelta at *;
    intro n k hn; split_ifs ;
    · have := Classical.choose_spec ( N_seq_spec ( epsilon_seq k ) ( by tauto ) ( by tauto ) n ( by tauto ) ( max ( ( k + 1 ) * n ) ( N_seq ( epsilon_seq ( k + 1 ) ) ) ) ) ; aesop;
    · exact Nat.le_succ_of_le ( Nat.le_max_left _ _ );
  induction' k with k ih;
  · exact Nat.le_add_left _ _;
  · exact h_next _ _ ( n_seq_pos _ )

/-
n_seq k is large enough to satisfy the threshold for epsilon_seq k.
-/
lemma n_seq_large (k : ℕ) (hk : k ≥ 1) : n_seq k ≥ N_seq (epsilon_seq k) := by
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ epsilon_seq ];
  · unfold n_seq; norm_num;
    unfold epsilon_seq; norm_num;
  · rw [ show n_seq ( k + 2 ) = next_val ( n_seq ( k + 1 ) ) ( k + 1 ) from rfl ];
    unfold next_val;
    unfold epsilon_seq; norm_num; split_ifs <;> norm_num at * ;
    · have := Classical.choose_spec ( N_seq_spec ( ( k + 1 + 1 : ℝ ) ⁻¹ ) ( by positivity ) ( by rw [ inv_eq_one_div, div_lt_iff₀ ] <;> linarith ) ( n_seq ( k + 1 ) ) ( by linarith ) ( Max.max ( ( k + 1 + 1 ) * n_seq ( k + 1 ) ) ( N_seq ( ( k + 1 + 1 + 1 : ℝ ) ⁻¹ ) ) ) ) ; aesop;
    · exact Nat.le_succ_of_le ( Nat.le_max_right _ _ )

/-
n_seq (k+1) satisfies the Key Proposition conclusion with respect to n_seq k and epsilon_seq k.
-/
lemma n_seq_prop_key (k : ℕ) (hk : k ≥ 1) :
  PropositionKey_conclusion (n_seq k) (n_seq (k + 1)) (epsilon_seq k) C_seq := by
    by_cases h : n_seq (k + 1) = next_val (n_seq k) k;
    · rw [h];
      unfold next_val;
      simp +zetaDelta at *;
      split_ifs;
      · exact Classical.choose_spec ( N_seq_spec ( epsilon_seq k ) ( by linarith ) ( by linarith ) ( n_seq k ) ( by linarith ) ( max ( ( k + 1 ) * n_seq k ) ( N_seq ( epsilon_seq ( k + 1 ) ) ) ) ) |> fun h => by aesop;
      · exact False.elim <| ‹¬ ( N_seq ( epsilon_seq k ) ≤ n_seq k ∧ 0 < epsilon_seq k ∧ epsilon_seq k < 1 ) › ⟨ n_seq_large k hk, epsilon_seq_valid k hk |>.1, epsilon_seq_valid k hk |>.2 ⟩;
    · rcases k with ( _ | _ | k ) <;> tauto

/-
n_seq (k+1) satisfies the Key Proposition conclusion with respect to n_seq k and epsilon_seq k.
-/
lemma n_seq_prop_key_v2 (k : ℕ) (hk : k ≥ 1) :
  PropositionKey_conclusion (n_seq k) (n_seq (k + 1)) (epsilon_seq k) C_seq := by
    convert n_seq_prop_key k hk using 1

/-
n_seq (k+1) satisfies the Key Proposition conclusion with respect to n_seq k and epsilon_seq k.
-/
lemma n_seq_prop_key_final (k : ℕ) (hk : k ≥ 1) :
  PropositionKey_conclusion (n_seq k) (n_seq (k + 1)) (epsilon_seq k) C_seq := by
    -- Apply the lemma n_seq_prop_key_v2 with the given k and hk.
    apply n_seq_prop_key_v2 k hk

/-
There exists a sequence n_k and a constant C satisfying the SequenceProperties.
-/
lemma exists_sequence :
  ∃ n : ℕ → ℕ, ∃ C : ℝ, SequenceProperties n C := by
    use n_seq, C_seq;
    constructor;
    · intro k hk; have := n_seq_growth k; have := n_seq_growth ( k + 1 ) ; norm_num at * ; nlinarith [ n_seq_pos k, n_seq_pos ( k + 1 ) ] ;
    · refine' ⟨ _, _, _ ⟩;
      · intro k hk a ha ha'; have := n_seq_prop_key k hk; unfold PropositionKey_conclusion at this; aesop;
      · intro k hk R hR₁ hR₂;
        have := n_seq_prop_key_final k hk;
        refine' le_trans _ ( this.2 R hR₁ hR₂ );
        unfold epsilon_seq;
        gcongr ; norm_num;
        exact mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( by linarith ) ) ( by exact le_of_lt ( C_seq_pos ) );
      · exact fun k a => n_seq_growth k

/-
The constructed set A is a subset of the squarefree numbers.
-/
lemma constructed_A_subset_SF (n : ℕ → ℕ) : constructed_A n ⊆ SF := by
  intro x hx
  rw [constructed_A] at hx
  simp at hx
  obtain ⟨k, hk⟩ := hx
  exact hk.2.1

/-
n_lower is the sequence, C_lower is the constant, and A_lower is the set constructed from them.
-/
noncomputable def n_lower : ℕ → ℕ := Classical.choose exists_sequence

noncomputable def C_lower : ℝ := Classical.choose (Classical.choose_spec exists_sequence)

lemma n_lower_properties : SequenceProperties n_lower C_lower :=
  Classical.choose_spec (Classical.choose_spec exists_sequence)

noncomputable def A_lower : Set ℕ := constructed_A n_lower

/-
The set A_lower has property Q.
-/
lemma A_lower_property_Q : PropertyQ A_lower := by
  -- By definition of $A_lower$, we know that for any $a \in A_lower$ with $a < n$ (where $n = n_lower (k+1)$), $n + a$ is squarefree.
  have h_A_lower_Q : ∀ k ≥ 1, ∀ a ∈ A_lower, a < n_lower (k + 1) → n_lower (k + 1) + a ∈ SF := by
    intro k hk a ha hlt
    obtain ⟨j, hj⟩ : ∃ j < k + 1, a ∈ Set.Ioc (n_lower j) (n_lower (j + 1)) ∧ a ∈ SF ∧ n_lower (j + 1) + a ∈ SF := by
      obtain ⟨ j, hj ⟩ := Set.mem_iUnion.mp ha;
      refine' ⟨ j, _, hj ⟩;
      contrapose! hlt;
      -- Since $n_lower$ is strictly increasing, we have $n_lower (k + 1) \leq n_lower j$ for $j \geq k + 1$.
      have h_inc : ∀ j k, j ≥ k + 1 → n_lower (k + 1) ≤ n_lower j := by
        intros j k hjk
        induction' hjk with j hj ih;
        · norm_num +zetaDelta at *;
        · have := n_lower_properties.1 j ( by linarith [ Nat.succ_le_iff.mp hj ] ) ; linarith!;
      exact le_trans ( h_inc _ _ hlt ) hj.1.1.le;
    by_cases hjk : j = k;
    · aesop;
    · -- Since $j < k$, we have $a \leq n_lower (j + 1) \leq n_lower k$.
      have h_le : a ≤ n_lower k := by
        have h_le : ∀ m ≥ j + 1, n_lower m ≥ n_lower (j + 1) := by
          intro m hm
          induction' hm with m ih;
          · norm_num +zetaDelta at *;
          · exact le_trans ‹_› ( n_lower_properties.1 _ ( by linarith [ Nat.succ_le_iff.mp ih ] ) |> le_of_lt );
        exact le_trans hj.2.1.2 ( h_le k ( Nat.succ_le_of_lt ( lt_of_le_of_ne ( Nat.le_of_lt_succ hj.1 ) hjk ) ) );
      have := n_lower_properties.2.1 k hk;
      exact this a ( Finset.mem_Icc.mpr ⟨ Nat.pos_of_ne_zero ( by aesop ), h_le ⟩ ) hj.2.2.1;
  -- Since $n_lower$ is strictly increasing, there are infinitely many $n_lower (k + 1)$.
  have h_inf : Set.Infinite {n | ∃ k ≥ 1, n = n_lower (k + 1)} := by
    refine Set.infinite_of_forall_exists_gt ?_;
    intro a
    use n_lower (a + 2);
    refine' ⟨ ⟨ a + 1, by linarith, rfl ⟩, _ ⟩;
    have h_seq_growth : ∀ k ≥ 1, n_lower (k + 1) ≥ (k + 1) * n_lower k := by
      exact fun k hk => n_lower_properties.2.2.2 k hk;
    induction' a with a ih;
    · nlinarith! [ h_seq_growth 1 le_rfl, n_lower_properties.1 1 le_rfl ];
    · nlinarith [ h_seq_growth ( a + 2 ) ( by linarith ), n_seq_pos ( a + 2 ) ];
  refine' h_inf.mono _ ; aesop;

/-
Inequality for the cardinality of A_lower intersection [1, R].
-/
lemma A_lower_card_ineq (k : ℕ) (hk : k ≥ 2) (R : ℕ) (hR1 : n_lower k ≤ R) (hR2 : R ≤ n_lower (k + 1)) :
  ((A_lower ∩ Finset.Icc 1 R).ncard : ℝ) ≥
  ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n_lower (k + 1) + a ∈ SF)).card -
  ((Finset.Icc 1 (n_lower k)).filter (fun a => a ∈ SF ∧ n_lower k + a ∉ SF)).card -
  n_lower (k - 1) := by
    rw [ Set.ncard_eq_toFinset_card _ ] ; norm_num [ Set.setOf_and ] ; ring_nf;
    -- Let's simplify the goal using the definitions of $A_lower$ and $SF$.
    have h_simp : Finset.filter (fun a => a ∈ SF ∧ n_lower (1 + k) + a ∈ SF) (Finset.Icc 1 R) ⊆ Finset.filter (fun a => a ∈ A_lower) (Finset.Icc 1 R) ∪ Finset.filter (fun a => a ∈ SF ∧ n_lower k + a ∉ SF) (Finset.Icc 1 (n_lower k)) ∪ Finset.Icc 1 (n_lower (k - 1)) := by
      intro a ha;
      by_cases ha1 : a ≤ n_lower k <;> by_cases ha2 : a ≤ n_lower (k - 1) <;> simp_all +decide [ add_comm 1 k ];
      · by_contra h_contra;
        rcases k with ( _ | _ | k ) <;> simp_all +decide;
        exact h_contra.1 <| Set.mem_iUnion.2 ⟨ k + 1, by aesop ⟩;
      · left;
        exact Set.mem_iUnion.mpr ⟨ k, ⟨ ⟨ by linarith, by linarith ⟩, ha.2.1, ha.2.2 ⟩ ⟩;
    exact_mod_cast le_trans ( Finset.card_le_card h_simp ) ( by exact le_trans ( Finset.card_union_le _ _ ) ( by exact le_trans ( add_le_add_right ( Finset.card_union_le _ _ ) _ ) ( by norm_num; linarith ) ) )

/-
Bound on the number of squarefree integers a <= n_k such that n_k + a is not squarefree.
-/
lemma bad_set_bound (k : ℕ) (hk : k ≥ 2) :
  ((Finset.Icc 1 (n_lower k)).filter (fun a => a ∈ SF ∧ n_lower k + a ∉ SF)).card ≤
  C_lower / (k - 1) * n_lower k + (Classical.choose SF_count_bound) * Real.sqrt (n_lower k) := by
    have := Classical.choose_spec SF_count_bound;
    have := n_lower_properties.2.2.1 ( k - 1 ) ( Nat.le_sub_one_of_lt hk ) ; rcases k with ( _ | _ | k ) <;> norm_num at *;
    have := this ( n_lower ( k + 1 + 1 ) ) ( by linarith [ n_lower_properties.1 ( k + 1 ) ( by linarith ) ] ) ( by linarith [ n_lower_properties.1 ( k + 1 ) ( by linarith ) ] ) ; rw [ div_add', le_div_iff₀ ] at this <;> norm_num at *;
    · have := ‹0 < Classical.choose SF_count_bound ∧ ∀ n : ℕ, 0 < n → |↑{x ∈ Finset.Icc 1 n | x ∈ SF}.card - 6 / Real.pi ^ 2 * ↑n| ≤ Classical.choose SF_count_bound * ↑n.sqrt›.2 ( n_lower ( k + 1 + 1 ) ) ( by linarith [ n_lower_properties.1 ( k + 1 ) ( by linarith ) ] ) ; rw [ abs_le ] at this ; norm_num at *;
      rw [ show ( Finset.filter ( fun a => a ∈ SF ∧ n_lower ( k + 1 + 1 ) + a ∉ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) ) = Finset.filter ( fun a => a ∈ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) \ Finset.filter ( fun a => a ∈ SF ∧ n_lower ( k + 1 + 1 ) + a ∈ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) by ext; aesop ] ; rw [ Finset.card_sdiff ];
      rw [ Nat.cast_sub ];
      · rw [ show ( Finset.filter ( fun a => a ∈ SF ∧ n_lower ( k + 1 + 1 ) + a ∈ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) ∩ Finset.filter ( fun a => a ∈ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) ) = Finset.filter ( fun a => a ∈ SF ∧ n_lower ( k + 1 + 1 ) + a ∈ SF ) ( Finset.Icc 1 ( n_lower ( k + 1 + 1 ) ) ) by ext; aesop ] ; norm_num;
        nlinarith [ Real.sqrt_nonneg ( n_lower ( k + 1 + 1 ) : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg ( n_lower ( k + 1 + 1 ) ) ), show ( Nat.sqrt ( n_lower ( k + 1 + 1 ) ) : ℝ ) ≤ Real.sqrt ( n_lower ( k + 1 + 1 ) ) from Real.le_sqrt_of_sq_le ( mod_cast Nat.sqrt_le' _ ) ];
      · exact Finset.card_mono <| Finset.inter_subset_right;
    · exact Nat.pos_of_ne_zero ( by linarith [ n_lower_properties.1 ( k + 1 ) ( by linarith ) ] );
    · exact ne_of_gt ( Nat.pos_of_ne_zero ( by linarith [ n_lower_properties.1 ( k + 1 ) ( by linarith ), n_lower_properties.2.2.2 ( k + 1 ) ( by linarith ) ] ) )

/-
Explicit lower bound for the density of A_lower in the interval [1, R].
-/
lemma A_lower_density_lower_bound_explicit (k : ℕ) (hk : k ≥ 2) (R : ℕ) (hR1 : n_lower k ≤ R) (hR2 : R ≤ n_lower (k + 1)) :
  ((A_lower ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥
  6 / Real.pi^2 - C_lower / k -
  (C_lower / (k - 1) * n_lower k + (Classical.choose SF_count_bound) * Real.sqrt (n_lower k) + n_lower (k - 1)) / R := by
    have := n_lower_properties.2.2.1 k ( by linarith ) R hR1 hR2;
    refine' le_trans ( sub_le_sub_right this _ ) _;
    have h_card_ineq : ((A_lower ∩ Finset.Icc 1 R).ncard : ℝ) ≥
      ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n_lower (k + 1) + a ∈ SF)).card -
      ((Finset.Icc 1 (n_lower k)).filter (fun a => a ∈ SF ∧ n_lower k + a ∉ SF)).card -
      n_lower (k - 1) := by
        convert A_lower_card_ineq k hk R hR1 hR2 using 1;
    have h_card_bound : ((Finset.Icc 1 (n_lower k)).filter (fun a => a ∈ SF ∧ n_lower k + a ∉ SF)).card ≤
      C_lower / (k - 1) * n_lower k + (Classical.choose SF_count_bound) * Real.sqrt (n_lower k) := by
        convert bad_set_bound k hk using 1;
    rw [ ← sub_div ];
    gcongr;
    linarith

/-
The sequence n_lower tends to infinity.
-/
lemma n_lower_tendsto_atTop : Filter.Tendsto n_lower Filter.atTop Filter.atTop := by
  -- By definition of $n_lower$, we know that it satisfies the properties of $SequenceProperties$.
  obtain ⟨C, hC⟩ := n_lower_properties;
  refine' Filter.tendsto_atTop_atTop.mpr _;
  intro b;
  use b + 1;
  intro a ha;
  induction' ha with k hk ih <;> norm_num at *;
  · exact Nat.recOn b ( by linarith! [ C 1 le_rfl, hC.2.2 1 le_rfl ] ) fun k ih => by linarith! [ C ( k + 1 ) ( by linarith ), hC.2.2 ( k + 1 ) ( by linarith ) ] ;
  · linarith [ C k ( by linarith ), hC.2.2 k ( by linarith ) ]

/-
The ratio n_{k-1}/n_k tends to 0.
-/
lemma term4_tendsto_zero :
  Filter.Tendsto (fun k => (n_lower (k - 1) : ℝ) / n_lower k) Filter.atTop (nhds 0) := by
    -- By definition of $n_lower$, we know that $n_lower (k - 1) / n_lower k \leq 1 / k$ for all $k \geq 2$.
    have h_bound : ∀ k ≥ 2, (n_lower (k - 1) : ℝ) / n_lower k ≤ 1 / k := by
      intro k hk
      have h_bound : n_lower k ≥ k * n_lower (k - 1) := by
        rcases k with ( _ | _ | k ) <;> simp_all +decide;
        exact n_lower_properties.2.2.2 _ ( by linarith ) |> le_trans ( by nlinarith )
      have h_ratio : (n_lower (k - 1) : ℝ) / n_lower k ≤ 1 / k := by
        field_simp;
        exact div_le_one_of_le₀ ( mod_cast by linarith ) ( Nat.cast_nonneg _ )
      exact h_ratio;
    exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 2, fun k hk => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_bound k hk ⟩ ) ( tendsto_one_div_atTop_nhds_zero_nat )

/-
The error terms in the density lower bound tend to 0 as k goes to infinity.
-/
lemma error_terms_tendsto_zero :
  Filter.Tendsto (fun (k : ℕ) => C_lower / (k : ℝ) + C_lower / ((k : ℝ) - 1) + (Classical.choose SF_count_bound) / Real.sqrt (n_lower k) + (n_lower (k - 1) : ℝ) / n_lower k) Filter.atTop (nhds 0) := by
    -- We'll use the fact that if the denominator grows faster than the numerator, the limit will tend to 0.
    have h_sqrt : Filter.Tendsto (fun k => Real.sqrt (n_lower k)) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop_atTop.mpr fun x => by rcases Filter.eventually_atTop.mp ( n_lower_tendsto_atTop.eventually_ge_atTop ( Nat.ceil ( x ^ 2 ) ) ) with ⟨ k, hk ⟩ ; exact ⟨ k, fun n hn => Real.le_sqrt_of_sq_le <| by simpa using Nat.le_of_ceil_le <| hk n hn ⟩ ;
    simpa using Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) ( tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ) ( tendsto_const_nhds.div_atTop h_sqrt ) ) term4_tendsto_zero

/-
The error term tends to 0.
-/
noncomputable def error_term (k : ℕ) : ℝ :=
  C_lower / (k : ℝ) + C_lower / ((k : ℝ) - 1) + (Classical.choose SF_count_bound) / Real.sqrt (n_lower k) + (n_lower (k - 1) : ℝ) / n_lower k

lemma error_term_tendsto_zero : Filter.Tendsto error_term Filter.atTop (nhds 0) := by
  convert error_terms_tendsto_zero using 1

/-
The lower density of a set A of natural numbers.
-/
def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

/-
If the upper density is at most d and the lower density is at least d, then the set has natural density d.
-/
lemma natural_density_of_densities (A : Set ℕ) (d : ℝ)
    (h_upper : upperDensity A ≤ d)
    (h_lower : lowerDensity A ≥ d) :
    HasNaturalDensity A d := by
      refine' tendsto_order.2 ⟨ _, _ ⟩;
      · intro a' ha'; contrapose! ha'; simp_all +decide [ upperDensity, lowerDensity ] ;
        refine' le_trans h_lower _;
        refine' csSup_le _ _ <;> norm_num;
        · exact ⟨ 0, ⟨ 1, fun n hn => by positivity ⟩ ⟩;
        · exact fun b x hx => by obtain ⟨ y, hy₁, hy₂ ⟩ := ha' x; linarith [ hx y hy₁ ] ;
      · unfold upperDensity lowerDensity at *;
        rw [ Filter.limsup_eq ] at h_upper;
        contrapose! h_upper;
        refine' lt_of_lt_of_le h_upper.choose_spec.1 ( le_csInf _ _ );
        · refine' ⟨ 1, _ ⟩;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ) <| by positivity;
        · intro b hb;
          exact le_of_not_gt fun h => h_upper.choose_spec.2 <| hb.mono fun n hn => by linarith [ h_upper.choose_spec.1 ] ;

/-
If the density in intervals [n_k, n_{k+1}] is bounded below by C - epsilon_k, and epsilon_k tends to 0, then the lower density is at least C.
-/
lemma lower_density_of_interval_bound (A : Set ℕ) (n : ℕ → ℕ) (C : ℝ) (ε : ℕ → ℝ)
    (hn : Filter.Tendsto n Filter.atTop Filter.atTop)
    (h_bound : ∀ k, ∀ R, n k ≤ R → R ≤ n (k + 1) →
      ((A ∩ Set.Icc 1 R).ncard : ℝ) / R ≥ C - ε k)
    (h_lim : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    lowerDensity A ≥ C := by
      -- By definition of lower density, we need to show that for any $d < C$, there exists an $N$ such that for all $n \geq N$, the density of $A$ up to $n$ is at least $d$.
      apply le_of_forall_lt_imp_le_of_dense
      intro d hd
      obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, ε k < C - d := by
        simpa using h_lim.eventually ( gt_mem_nhds <| by linarith );
      refine' le_csSup _ _ <;> norm_num [ lowerDensity ];
      · exact ⟨ 1, by rintro x ⟨ k, hk ⟩ ; exact le_trans ( hk ( k + 1 ) ( by linarith ) ) ( div_le_one_of_le₀ ( mod_cast Nat.le_trans ( Set.ncard_le_ncard ( Set.inter_subset_right ) ) ( by simp +decide [ Set.ncard_eq_toFinset_card' ] ) ) ( by positivity ) ) ⟩;
      · -- Choose $a = n_N$.
        use n N + 1;
        intro b hb
        obtain ⟨k, hk⟩ : ∃ k ≥ N, n k ≤ b ∧ b ≤ n (k + 1) := by
          have h_exists_k : ∃ k ≥ N, n k ≤ b ∧ b < n (k + 1) := by
            have h_unbounded : ∀ M, ∃ k ≥ N, n k > M := by
              exact fun M => by rcases Filter.eventually_atTop.mp ( hn.eventually_gt_atTop M ) with ⟨ k, hk ⟩ ; exact ⟨ _, le_max_left _ _, hk _ ( le_max_right _ _ ) ⟩ ;
            contrapose! h_unbounded;
            exact ⟨ b, fun x hx => Nat.le_induction ( by linarith ) h_unbounded x hx ⟩;
          exact ⟨ h_exists_k.choose, h_exists_k.choose_spec.1, h_exists_k.choose_spec.2.1, h_exists_k.choose_spec.2.2.le ⟩;
        linarith [ h_bound k b hk.2.1 hk.2.2, hN k hk.1 ]

/-
n_lower k is positive for k >= 2.
-/
lemma n_lower_pos_ge_2 (k : ℕ) (hk : k ≥ 2) : n_lower k > 0 := by
  induction' k with k ih;
  · contradiction;
  · have := n_lower_properties.2.2.2 k; rcases k with ( _ | _ | k ) <;> simp_all +decide ;
    · have := n_lower_properties.1 1; norm_num at this; linarith;
    · grind

/-
If a sequence n_k grows fast enough and the density of SF in [1, R] is lower bounded by 6/pi^2 - C/k, then C >= 0.
-/
lemma density_contradiction_abstract (n : ℕ → ℕ) (C : ℝ)
  (h_growth : ∀ k ≥ 1, n (k+1) ≥ (k+1) * n k)
  (h_pos : ∀ k ≥ 1, n k > 0)
  (h_dens : ∀ k ≥ 1, ∀ R, n k ≤ R → R ≤ n (k+1) →
    ((Finset.Icc 1 R).filter (fun a => a ∈ SF)).card / (R : ℝ) ≥ 6 / Real.pi^2 - C / k) :
  C ≥ 0 := by
    by_contra h_neg;
    -- From `SF_count_bound`, we have $|\SF \cap [1, R]|/R \le 6/\pi^2 + C_{SF}/\sqrt{R}$.
    have h_bound : ∀ R : ℕ, R > 0 → ((Finset.Icc 1 R).filter (fun a => a ∈ SF)).card / (R : ℝ) ≤ 6 / Real.pi^2 + (Classical.choose SF_count_bound) / Real.sqrt R := by
      intro R hR_pos
      have h_bound : ((Finset.Icc 1 R).filter (fun a => a ∈ SF)).card ≤ 6 / Real.pi^2 * R + (Classical.choose SF_count_bound) * Real.sqrt R := by
        have := Classical.choose_spec SF_count_bound;
        exact le_trans ( show ( Finset.card ( Finset.filter ( fun a => a ∈ SF ) ( Finset.Icc 1 R ) ) : ℝ ) ≤ 6 / Real.pi ^ 2 * R + Classical.choose SF_count_bound * Nat.sqrt R by linarith [ abs_le.mp ( this.2 R ( Nat.cast_pos.mpr hR_pos ) ) ] ) ( add_le_add_left ( mul_le_mul_of_nonneg_left ( Real.le_sqrt_of_sq_le ( mod_cast Nat.sqrt_le' _ ) ) ( by linarith ) ) _ );
      rw [ div_le_iff₀ ] <;> first | positivity | convert h_bound using 1 ; ring_nf ; norm_num [ hR_pos.ne', Real.sqrt_div_self ] ;
      rw [ mul_assoc, ← Real.sqrt_div_self, div_mul_cancel₀ _ ( by positivity ) ];
    -- From `h_growth`, $n_{k+1}$ grows super-polynomially.
    have h_super_poly : Filter.Tendsto (fun k : ℕ => (k : ℝ) / Real.sqrt (n (k + 1))) Filter.atTop (nhds 0) := by
      -- Since $n_{k+1} \geq (k+1)!$, we have $\sqrt{n_{k+1}} \geq \sqrt{(k+1)!}$.
      have h_sqrt_bound : ∀ k ≥ 1, Real.sqrt (n (k + 1)) ≥ Real.sqrt ((k + 1)!) := by
        intros k hk
        have h_factorial : n (k + 1) ≥ (k + 1)! := by
          induction hk <;> simp_all +decide [ Nat.factorial_succ ];
          · nlinarith [ h_growth 1 le_rfl, h_pos 1 le_rfl ];
          · nlinarith [ h_growth ( ‹_› + 1 ) ( by linarith ) ]
        exact Real.sqrt_le_sqrt (Nat.cast_le.mpr h_factorial);
      -- Since $\sqrt{(k+1)!}$ grows faster than $k$, we have $\frac{k}{\sqrt{(k+1)!}} \to 0$ as $k \to \infty$.
      have h_sqrt_factorial : Filter.Tendsto (fun k : ℕ => (k : ℝ) / Real.sqrt ((k + 1)!)) Filter.atTop (nhds 0) := by
        -- We can use the fact that $\sqrt{(k+1)!}$ grows faster than $k$.
        have h_sqrt_factorial : Filter.Tendsto (fun k : ℕ => (k : ℝ) / Real.sqrt (k !)) Filter.atTop (nhds 0) := by
          -- We can use the fact that $\sqrt{k!}$ grows faster than $k$.
          have h_sqrt_factorial : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ 2 / (k !)) Filter.atTop (nhds 0) := by
            refine' squeeze_zero_norm' _ tendsto_inverse_atTop_nhds_zero_nat;
            norm_num +zetaDelta at *;
            exact ⟨ 8, fun k hk => by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> first | positivity | induction hk <;> norm_num [ Nat.factorial_succ ] at * ; nlinarith ⟩;
          have := h_sqrt_factorial.sqrt;
          simpa [ Real.sqrt_div ( sq_nonneg _ ), Real.sqrt_sq ( Nat.cast_nonneg _ ) ] using this;
        exact squeeze_zero ( fun k => by positivity ) ( fun k => by gcongr ; linarith ) h_sqrt_factorial;
      refine' squeeze_zero_norm' _ h_sqrt_factorial;
      filter_upwards [ Filter.eventually_ge_atTop 1 ] with k hk using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( h_sqrt_bound k hk ) ;
    -- From `h_dens`, we have $6/\pi^2 + D/k \le 6/\pi^2 + C_{SF}/\sqrt{n_{k+1}}$.
    have h_ineq : ∀ k : ℕ, k ≥ 1 → 6 / Real.pi^2 + (-C) / (k : ℝ) ≤ 6 / Real.pi^2 + (Classical.choose SF_count_bound) / Real.sqrt (n (k + 1)) := by
      intro k hk; specialize h_dens k hk ( n ( k + 1 ) ) ( by nlinarith [ h_growth k hk, h_pos k hk ] ) le_rfl; specialize h_bound ( n ( k + 1 ) ) ( by nlinarith [ h_growth k hk, h_pos k hk ] ) ; ring_nf at *; linarith;
    -- From `h_ineq`, we have $-C/k \le C_{SF}/\sqrt{n_{k+1}}$.
    have h_ineq_simplified : ∀ k : ℕ, k ≥ 1 → -C ≤ (Classical.choose SF_count_bound) * (k : ℝ) / Real.sqrt (n (k + 1)) := by
      intro k hk; specialize h_ineq k hk; ring_nf at h_ineq ⊢; nlinarith [ inv_pos.mpr ( by positivity : 0 < ( k : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( k : ℝ ) ≠ 0 ) ] ;
    exact absurd ( le_of_tendsto_of_tendsto tendsto_const_nhds ( by simpa [ mul_div_assoc ] using h_super_poly.const_mul ( Classical.choose SF_count_bound ) ) ( Filter.eventually_atTop.mpr ⟨ 1, fun k hk => h_ineq_simplified k hk ⟩ ) ) ( by norm_num; linarith )

/-
C_lower is non-negative.
-/
lemma C_lower_nonneg : C_lower ≥ 0 := by
  by_contra h_neg_C_lower;
  obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ, ∃ C : ℝ, SequenceProperties n C ∧ C < 0 := by
    exact ⟨ n_lower, C_lower, n_lower_properties, lt_of_not_ge h_neg_C_lower ⟩;
  obtain ⟨ C, hC₁, hC₂ ⟩ := hn;
  have h_density : ∀ k ≥ 1, ∀ R, n k ≤ R → R ≤ n (k + 1) → ((Finset.Icc 1 R).filter (fun a => a ∈ SF)).card / (R : ℝ) ≥ 6 / Real.pi^2 - C / k := by
    intros k hk R hR1 hR2
    have h_density : ((Finset.Icc 1 R).filter (fun a => a ∈ SF ∧ n (k + 1) + a ∈ SF)).card / (R : ℝ) ≥ 6 / Real.pi^2 - C / k := by
      exact hC₁.2.2.1 k hk R hR1 hR2;
    refine le_trans h_density ?_;
    gcongr;
    exact fun x hx => hx.1;
  have := density_contradiction_abstract n C ( fun k hk => hC₁.2.2.2 k hk ) ( fun k hk => ?_ ) h_density;
  · linarith;
  · rcases k with ( _ | _ | k ) <;> simp_all +decide [ SequenceProperties ];
    · have := h_density 1 le_rfl ( n 1 ) le_rfl ( by linarith [ hC₁.1 1 le_rfl ] ) ; norm_num at this;
      exact Nat.pos_of_ne_zero fun h => by norm_num [ h ] at this; nlinarith [ Real.pi_gt_three, mul_div_cancel₀ ( 6 : ℝ ) ( pow_ne_zero 2 Real.pi_ne_zero ) ] ;
    · linarith [ hC₁.1 ( k + 1 ) ( by linarith ), hC₁.1 ( k + 2 ) ( by linarith ) ]

/-
For R in [n_k, n_{k+1}], the density of A_lower in [1, R] is at least 6/pi^2 - error_term k.
-/
lemma A_lower_density_bound_k (k : ℕ) (hk : k ≥ 2) (R : ℕ) (hR1 : n_lower k ≤ R) (hR2 : R ≤ n_lower (k + 1)) :
  ((A_lower ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥ 6 / Real.pi^2 - error_term k := by
    -- By Lemma `A_lower_density_lower_bound_explicit`, we have the inequality:
    have h_density : ((A_lower ∩ Finset.Icc 1 R).ncard : ℝ) / R ≥ 6 / Real.pi^2 - C_lower / (k : ℝ) - (C_lower / ((k : ℝ) - 1) * n_lower k + (Classical.choose SF_count_bound) * Real.sqrt (n_lower k) + n_lower (k - 1)) / (n_lower k : ℝ) := by
      have := A_lower_density_lower_bound_explicit k hk R hR1 hR2;
      refine le_trans ?_ this;
      gcongr;
      · exact add_nonneg ( add_nonneg ( mul_nonneg ( div_nonneg ( by linarith [ show 0 ≤ C_lower by exact le_of_not_gt fun h => by have := C_lower_nonneg; linarith ] ) ( by linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( Classical.choose_spec SF_count_bound |>.1.le ) ( Real.sqrt_nonneg _ ) ) ) ( Nat.cast_nonneg _ );
      · exact Nat.cast_pos.mpr ( n_lower_pos_ge_2 k hk );
    convert h_density using 1;
    unfold error_term; ring_nf; norm_num [ ne_of_gt ( show 0 < n_lower k from n_lower_pos_ge_2 k hk ) ] ;
    rw [ mul_assoc, ← Real.sqrt_div_self ] ; ring

/-
The lower density of A_lower is at least 6/pi^2.
-/
lemma A_lower_lowerDensity : lowerDensity A_lower ≥ 6 / Real.pi^2 := by
  -- Apply the lower_density_of_interval_bound lemma with the sequence n'_k = n_{k+2} and error term ε'_k = error_term (k+2).
  apply lower_density_of_interval_bound A_lower (fun k => n_lower (k + 2)) (6 / Real.pi^2) (fun k => error_term (k + 2)) (by
  exact n_lower_tendsto_atTop.comp ( Filter.tendsto_add_atTop_nat 2 )) (by
  intros k R hk₁ hk₂;
  convert A_lower_density_bound_k ( k + 2 ) ( by linarith ) R hk₁ hk₂ using 1;
  norm_num [ Set.ncard_eq_toFinset_card' ]) (by
  exact error_term_tendsto_zero.comp ( Filter.tendsto_add_atTop_nat 2 ))

/-
Every sequence with property Q has upper density at most 6/pi^2.
-/
theorem TheoremQ_upper (A : Set ℕ) (h : PropertyQ A) : upperDensity A ≤ 6 / Real.pi^2 := by
  -- Apply the lemma that states if A is admissible, then its upper density is at most 6/π².
  apply Admissible_implies_upperDensity_le_6_div_pi_sq A (PropertyQ_implies_Admissible A h)

/-
There exists a subset of SF with property Q and natural density 6/pi^2.
-/
theorem TheoremQ_lower : ∃ A : Set ℕ, A ⊆ SF ∧ PropertyQ A ∧ HasNaturalDensity A (6 / Real.pi^2) := by
  use A_lower
  refine ⟨constructed_A_subset_SF n_lower, A_lower_property_Q, ?_⟩
  apply natural_density_of_densities
  · exact TheoremQ_upper A_lower A_lower_property_Q
  · exact A_lower_lowerDensity

#print axioms TheoremQ_upper
#print axioms TheoremQ_lower

/-
Definition of HasPropertyQ as written down by the Formal Conjectures project of Google DeepMind.
-/
def HasPropertyQ (A : Set ℕ) : Prop :=
  {n : ℕ | ∀ a ∈ A, a < n → Squarefree (n + a)}.Infinite

/-
Statements from the Formal Conjectures project of Google DeepMind concerning Property Q.
-/
theorem erdos_1102.upper_density_Q
    (A : ℕ → ℕ) (h_inc : StrictMono A)
    (hQ : HasPropertyQ (range A)) :
    limsup (fun j : ℕ  ↦ (j / A j : ℝ)) atTop ≤ 6 / Real.pi^2 := by
  have h_upper_density : Filter.limsup (fun j => ((Set.range A ∩ Set.Icc 1 j).ncard : ℝ) / j) Filter.atTop ≤ 6 / Real.pi^2 := by
    convert TheoremQ_upper ( Set.range A ) hQ using 1;
  -- Since $A$ is strictly monotone, the number of elements in $\text{range}(A)$ up to $j$ is at most $j$.
  have h_card_le_j : ∀ j, ((Set.range A ∩ Set.Icc 1 j).ncard : ℝ) ≤ j := by
    intro j; exact_mod_cast le_trans ( Set.ncard_le_ncard ( show Set.range A ∩ Set.Icc 1 j ⊆ Set.Icc 1 j from fun x hx => hx.2 ) ) ( by simp [ Set.ncard_eq_toFinset_card' ] ) ;
  -- Since $A$ is strictly monotone, the number of elements in $\text{range}(A)$ up to $j$ is at least $j / A_j$.
  have h_card_ge_j_div_Aj : ∀ j, ((Set.range A ∩ Set.Icc 1 (A j)).ncard : ℝ) ≥ j := by
    intros j
    have h_card_ge_j_div_Aj : ((Set.range A ∩ Set.Icc 1 (A j)).ncard : ℝ) ≥ Finset.card (Finset.image A (Finset.Icc 1 j)) := by
      rw [ ← Set.ncard_coe_finset ];
      gcongr;
      · exact Set.finite_iff_bddAbove.mpr ⟨ A j, fun x hx => hx.2.2 ⟩;
      · exact fun x hx => by obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; exact ⟨ Set.mem_range_self _, ⟨ Nat.one_le_iff_ne_zero.mpr <| by linarith [ h_inc <| show 0 < y from Finset.mem_Icc.mp hy |>.1 ], h_inc.monotone <| Finset.mem_Icc.mp hy |>.2 ⟩ ⟩ ;
    rw [ Finset.card_image_of_injective _ h_inc.injective ] at h_card_ge_j_div_Aj ; aesop;
  refine' le_trans _ h_upper_density;
  refine' le_csInf _ _ <;> norm_num +zetaDelta at *;
  · exact ⟨ 1, ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast h_card_le_j n ) ( Nat.cast_nonneg _ ) ⟩ ⟩;
  · intro b x hx; refine' csInf_le _ _ <;> norm_num +zetaDelta at *;
    · exact ⟨ 0, by rintro a ⟨ k, hk ⟩ ; exact le_trans ( by positivity ) ( hk _ le_rfl ) ⟩;
    · use x + 1;
      -- By combining the results from hx and h_card_ge_j_div_Aj, we can conclude the proof.
      intros b_1 hb_1
      have h_ratio : (b_1 : ℝ) / (A b_1 : ℝ) ≤ (Set.range A ∩ Set.Icc 1 (A b_1)).ncard / (A b_1 : ℝ) := by
        gcongr ; aesop;
      grind

theorem erdos_1102.lower_density_Q_exists :
    ∃ A : ℕ → ℕ, StrictMono A ∧
    (∀ j, Squarefree (A j)) ∧
    HasPropertyQ (range A) ∧
    Tendsto (fun j : ℕ  ↦ (j / A j : ℝ)) atTop (𝓝 (6 / Real.pi^2)) := by
  obtain ⟨A, hA⟩ : ∃ A : Set ℕ, A ⊆ SF ∧ PropertyQ A ∧ HasNaturalDensity A (6 / Real.pi^2) := by
    -- Apply the theorem that states there exists a subset of SF with property Q and natural density 6/pi^2.
    apply TheoremQ_lower;
  -- Let's choose any enumeration of the set A.
  obtain ⟨A_enum, hA_enum⟩ : ∃ A_enum : ℕ → ℕ, StrictMono A_enum ∧ Set.range A_enum = A := by
    have h_enum : A.Infinite := by
      -- Since $A$ has property $Q$, it must be infinite. Otherwise, the set $\{n \mid \forall a \in A, a < n \rightarrow \text{Squarefree}(n + a)\}$ would be finite, contradicting property $Q$.
      by_contra h_finite;
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, n ∉ A := by
        exact Set.finite_iff_bddAbove.mp ( Classical.not_not.mp h_finite ) |> fun ⟨ N, hN ⟩ => ⟨ N + 1, fun n hn h => not_lt_of_ge ( hN h ) hn ⟩;
      have h_contra : Filter.Tendsto (fun n => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop (nhds 0) := by
        have h_contra : ∀ n ≥ N, ((A ∩ Set.Icc 1 n).ncard : ℝ) ≤ (A ∩ Set.Icc 1 N).ncard := by
          intros n hn; exact_mod_cast Set.ncard_le_ncard ( show A ∩ Set.Icc 1 n ⊆ A ∩ Set.Icc 1 N from fun x hx => ⟨ hx.1, ⟨ hx.2.1, by linarith [ hx.2.2, show x ≤ N from le_of_not_gt fun hx' => hN x ( by linarith [ hx.2.1, hx.2.2 ] ) hx.1 ] ⟩ ⟩ ) ;
        exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ N, fun n hn => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( h_contra n hn ) ( Nat.cast_nonneg _ ) ⟩ ) ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop );
      exact absurd ( tendsto_nhds_unique h_contra hA.2.2 ) ( by positivity );
    use fun n => Nat.nth A n;
    exact ⟨ Nat.nth_strictMono h_enum, Set.ext fun x => ⟨ fun hx => by obtain ⟨ n, rfl ⟩ := hx; exact Nat.nth_mem_of_infinite h_enum _, fun hx => ⟨ Nat.count A x, Nat.nth_count hx ⟩ ⟩ ⟩;
  have h_density : Filter.Tendsto (fun j : ℕ => ((Set.range A_enum ∩ Set.Icc 1 (A_enum j)).ncard : ℝ) / (A_enum j : ℝ)) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
    have h_density : Filter.Tendsto (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
      exact hA.2.2;
    convert h_density.comp ( show Filter.Tendsto ( fun j => A_enum j ) Filter.atTop Filter.atTop from ?_ ) using 2 ; aesop;
    exact hA_enum.1.tendsto_atTop;
  have h_card : ∀ j, ((Set.range A_enum ∩ Set.Icc 1 (A_enum j)).ncard : ℝ) = j + 1 := by
    intro j; rw [ show ( Set.range A_enum ∩ Set.Icc 1 ( A_enum j ) ) = Set.image A_enum ( Finset.Icc 0 j ) from ?_ ] ; rw [ Set.ncard_image_of_injective _ hA_enum.1.injective ] ; simp +decide [ Set.ncard_eq_toFinset_card' ] ;
    -- To prove equality of sets, we show each set is a subset of the other.
    apply Set.ext
    intro x
    simp [Set.mem_inter_iff, Set.mem_image];
    constructor;
    · rintro ⟨ ⟨ y, rfl ⟩, hy₁, hy₂ ⟩ ; exact ⟨ y, hA_enum.1.le_iff_le.mp hy₂, rfl ⟩ ;
    · rintro ⟨ k, hk₁, rfl ⟩ ; exact ⟨ ⟨ k, rfl ⟩, Nat.pos_of_ne_zero fun h => by have := hA.1 ( hA_enum.2.subset <| Set.mem_range_self k ) ; simp_all +decide [ SF ], hA_enum.1.monotone hk₁ ⟩ ;
  have h_card : Filter.Tendsto (fun j : ℕ => ((j + 1 : ℝ) / (A_enum j : ℝ))) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
    simpa only [ h_card ] using h_density;
  have h_card : Filter.Tendsto (fun j : ℕ => ((j : ℝ) / (A_enum j : ℝ))) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
    convert h_card.sub ( show Filter.Tendsto ( fun j : ℕ => ( 1 : ℝ ) / ( A_enum j : ℝ ) ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.comp hA_enum.1.tendsto_atTop ) using 2 <;> ring;
  use A_enum; aesop;

#print axioms erdos_1102.upper_density_Q
#print axioms erdos_1102.lower_density_Q_exists