/-
Note that this project is not quite finished yet. It will soon!

We say that a sequence of positive integers $A$ has:

- property $P$ if, for all positive integers $n$, there are only finitely many $a \in A$ such that $n+a$ is squarefree.
- property $Q$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$ with $a < n$.
- property $\overline{P}$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$.
- property $\overline{P}_infty$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all but finitely many $a \in A$.

Solving Erdős Problem #1102 (https://www.erdosproblems.com/1102), Terence Tao and I managed to prove tight bounds on the possible densities of sequences with one of the above properties.

W. van Doorn and T. Tao, Growth rates of sequences governed by the squarefree properties of their translates. arXiv:2512.01087 (2025).

Thanks to Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), the proof of the following theorem is formalized in the Lean file below:

Any sequence with property $\overline{P}$ or $\overline{P}_infty$ has density strictly smaller than $6/\pi^2$. On the other hand, for every $\epsilon > 0$ there exist a sequence with property $\overline{P}$ (which therefore has property $\overline{P}_infty$ as well) with lower density larger than $6/\pi^2 - \epsilon$.

The proof of the second part is conditional on various asymptotics on sums and products on primes, which all readily follow from the prime number theorem. These asymptotics are bundled as the structure SieveAssumptions that you can find at the start of the formalization below.

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
The statement of the asymptotic bound for the sum of 1/(p (log log p)^2) for p >= x.
-/
def Bound_sum_primes_ge_x_inv_p_loglog_sq : Prop :=
  (fun (x : ℝ) => ∑' (p : ℕ), if (p : ℝ) ≥ x ∧ Nat.Prime p then 1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0) =Θ[Filter.atTop] (fun (x : ℝ) => 1 / Real.log (Real.log x))

/-
The statement of the asymptotic bound for the sum of log log p / p^2 for p >= x.
-/
def Bound_sum_primes_ge_x_loglog_div_sq : Prop :=
  (fun (x : ℝ) => ∑' (p : ℕ), if (p : ℝ) ≥ x ∧ Nat.Prime p then Real.log (Real.log p) / (p : ℝ)^2 else 0) =Θ[Filter.atTop] (fun (x : ℝ) => Real.log (Real.log x) / (x * Real.log x))

/-
The statement of the asymptotic bound for the sum of p / (log log p)^2 for 2 < p <= x.
-/
def Bound_sum_primes_le_x_p_div_loglog_sq : Prop :=
  (fun (x : ℝ) => ∑ p ∈ Finset.filter (fun (p : ℕ) => 2 < p ∧ (p : ℝ) ≤ x ∧ Nat.Prime p) (Finset.range (Nat.floor x + 1)), (p : ℝ) / (Real.log (Real.log p))^2) =Θ[Filter.atTop] (fun (x : ℝ) => x^2 / (Real.log x * (Real.log (Real.log x))^2))

/-
The statement of the asymptotic bound for the sum of log log p for 2 < p <= x.
-/
def Bound_sum_primes_le_x_loglog : Prop :=
  (fun (x : ℝ) => ∑ p ∈ Finset.filter (fun (p : ℕ) => 2 < p ∧ (p : ℝ) ≤ x ∧ Nat.Prime p) (Finset.range (Nat.floor x + 1)), Real.log (Real.log p)) =Θ[Filter.atTop] (fun (x : ℝ) => x * Real.log (Real.log x) / Real.log x)

/-
Structure bundling the asymptotic bounds that are assumed without proof.
-/
structure SieveAssumptions where
  bound_prod_primes_le_x_sq : Bound_prod_primes_le_x_sq
  bound_sum_primes_ge_x_inv_sq : Bound_sum_primes_ge_x_inv_sq
  bound_sum_primes_ge_x_inv_p_loglog_sq : Bound_sum_primes_ge_x_inv_p_loglog_sq
  bound_sum_primes_ge_x_loglog_div_sq : Bound_sum_primes_ge_x_loglog_div_sq
  bound_sum_primes_le_x_p_div_loglog_sq : Bound_sum_primes_le_x_p_div_loglog_sq
  bound_sum_primes_le_x_loglog : Bound_sum_primes_le_x_loglog

/-
SF is the set of squarefree numbers.
-/
def SF : Set ℕ := {n | Squarefree n}

/-
A set A has property P_bar if for infinitely many n, n+a is squarefree for all a in A.
-/
def PropertyP_bar (A : Set ℕ) : Prop := ({n | ∀ a ∈ A, Squarefree (n + a)}).Infinite

/-
A set A has property P_bar_infty if for infinitely many n, n+a is squarefree for all but finitely many a in A.
-/
def PropertyP_bar_infty (A : Set ℕ) : Prop := ({n | ({a ∈ A | ¬Squarefree (n + a)}).Finite}).Infinite

/-
A set A is admissible if for every prime p, there is a residue class mod p^2 that A avoids.
-/
def Admissible (A : Set ℕ) : Prop :=
  ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ A, a % p^2 ≠ b

/-
A set A is almost admissible if for every prime p, there is a residue class mod p^2 that contains only finitely many elements of A.
-/
def AlmostAdmissible (A : Set ℕ) : Prop :=
  ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ({a ∈ A | a % p^2 = b}).Finite

/-
Every set with property P_bar has property P_bar_infty.
-/
theorem P_bar_implies_P_bar_infty (A : Set ℕ) (h : PropertyP_bar A) : PropertyP_bar_infty A := by
  -- By definition of PropertyP_bar, there are infinitely many n such that for all a in A, n+a is squarefree.
  have h_inf : {n | ∀ a ∈ A, Squarefree (n + a)}.Infinite := by
    exact h ;
  exact h_inf.mono fun n hn => Set.Finite.subset ( Set.finite_singleton 0 ) fun x hx => by aesop;

/-
Every admissible set is almost admissible.
-/
theorem Admissible_implies_AlmostAdmissible (A : Set ℕ) (h : Admissible A) : AlmostAdmissible A := by
  -- By definition of admissible, for every prime $p$, there exists a residue class $b \pmod{p^2}$ such that no element of $A$ is congruent to $b \pmod{p^2}$.
  intro p hp
  obtain ⟨b, hb₁, hb₂⟩ := h p hp
  use b
  simp [hb₁];
  exact Set.finite_empty.subset fun x hx => hb₂ x hx.1 hx.2

/-
Every set with property P_bar_infty is almost admissible.
-/
theorem PropertyP_bar_infty_implies_AlmostAdmissible (A : Set ℕ) (h : PropertyP_bar_infty A) : AlmostAdmissible A := by
  intro p hp;
  -- Fix a prime $p$.
  by_cases h_finite : ∀ b < p ^ 2, Set.Infinite {a ∈ A | a % p ^ 2 = b};
  · -- If for every $b < p^2$, the set $\{a \in A \mid a \equiv b \pmod{p^2}\}$ is infinite, then for any $n$, the set $\{a \in A \mid n + a \text{ is not squarefree}\}$ is infinite.
    have h_inf_not_squarefree : ∀ n, Set.Infinite {a ∈ A | ¬Squarefree (n + a)} := by
      intro n
      have h_inf_not_squarefree : Set.Infinite {a ∈ A | (n + a) % p ^ 2 = 0} := by
        have h_inf_not_squarefree : Set.Infinite {a ∈ A | a % p ^ 2 = (p ^ 2 - n % p ^ 2) % p ^ 2} := by
          exact h_finite _ ( Nat.mod_lt _ ( pow_pos hp.pos 2 ) );
        refine h_inf_not_squarefree.mono ?_;
        simp +contextual [ Nat.add_mod ];
        exact fun a ha ha' => by simp +decide [ Nat.add_sub_of_le ( Nat.mod_lt n ( pow_pos hp.pos 2 ) |> Nat.le_of_lt ) ] ;
      refine h_inf_not_squarefree.mono ?_;
      intro a ha; obtain ⟨ ha₁, ha₂ ⟩ := ha; rw [ ← Nat.dvd_iff_mod_eq_zero ] at ha₂; obtain ⟨ k, hk ⟩ := ha₂; simp_all +decide [ Nat.squarefree_mul_iff ] ;
      simp_all +decide [ sq, Nat.squarefree_mul_iff ];
      aesop;
    contrapose! h_inf_not_squarefree;
    exact Exists.elim ( h.nonempty ) fun n hn => ⟨ n, Set.not_infinite.mpr <| by simpa using hn ⟩;
  · aesop

/-
Property P_bar_infty is unaffected by finite modifications of the set.
-/
theorem PropertyP_bar_infty_finite_diff (A B : Set ℕ) (h : (A \ B).Finite ∧ (B \ A).Finite) : PropertyP_bar_infty A ↔ PropertyP_bar_infty B := by
  constructor <;> intro h' <;> unfold PropertyP_bar_infty at *;
  · refine Set.Infinite.mono ?_ h';
    intro n hn
    have h_finite : {a ∈ B | ¬Squarefree (n + a)} ⊆ ({a ∈ A | ¬Squarefree (n + a)} ∪ (B \ A)) := by
      exact fun x hx => if hx' : x ∈ A then Or.inl ⟨ hx', hx.2 ⟩ else Or.inr ⟨ hx.1, hx' ⟩;
    exact Set.Finite.subset ( hn.union h.2 ) h_finite;
  · refine' h'.diff ( h.1.union h.2 |> Set.Finite.image fun x => x ) |> fun h'' => h''.mono _;
    intro n hn; simp_all +decide ;
    refine' Set.Finite.subset ( hn.1.union ( h.1.union h.2 ) ) _;
    intro a ha; by_cases ha' : a ∈ B <;> aesop;

/-
AlmostAdmissible is unaffected by finite modifications of the set.
-/
theorem AlmostAdmissible_finite_diff (A B : Set ℕ) (h : (A \ B).Finite ∧ (B \ A).Finite) : AlmostAdmissible A ↔ AlmostAdmissible B := by
  constructor;
  · intro hA p hp
    obtain ⟨b, hb₁, hb₂⟩ := hA p hp
    use b;
    exact ⟨ hb₁, Set.Finite.subset ( hb₂.union ( h.1.union h.2 ) ) fun x hx => by by_cases hx' : x ∈ A <;> aesop ⟩;
  · -- For any prime $p$, choose $b$ such that $B \mod p^2 \neq b$. Since $A \mod p^2$ can differ from $B \mod p^2$ by at most a finite number of elements, we can adjust $b$ to avoid elements of $A$ that are congruent to $b$ modulo $p^2$.
    intros hB
    intro p hp
    obtain ⟨b, hb⟩ := hB p hp
    have h_finite_diff : ({a ∈ A | a % p^2 = b}).Finite := by
      exact Set.Finite.subset ( h.1.union hb.2 |> Set.Finite.union <| h.2 ) fun x hx => by by_cases hx' : x ∈ B <;> aesop;
    exact ⟨ b, hb.1, h_finite_diff ⟩
  
/-
Property P_bar is downwardly monotone.
-/
lemma PropertyP_bar_monotone (A B : Set ℕ) (h : A ⊆ B) (hB : PropertyP_bar B) : PropertyP_bar A := by
  exact Set.Infinite.mono ( fun n hn => by rintro a ha; exact hn a ( h ha ) ) hB

/-
Property P_bar_infty is downwardly monotone.
-/
lemma PropertyP_bar_infty_monotone (A B : Set ℕ) (h : A ⊆ B) (hB : PropertyP_bar_infty B) : PropertyP_bar_infty A := by
  refine Set.Infinite.mono ?_ ( hB );
  exact fun n hn => Set.Finite.subset ( hn ) fun x hx => ⟨ h hx.1, hx.2 ⟩
  
/-
The upper density of a set A of natural numbers.
-/
def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

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
If A has property P_bar_infty, there exist n1 < n2 such that n1+a and n2+a are squarefree for all but finitely many a in A.
-/
lemma P_bar_infty_implies_pair (A : Set ℕ) (h : PropertyP_bar_infty A) :
    ∃ n₁ n₂, n₁ < n₂ ∧ ({a ∈ A | ¬(Squarefree (n₁ + a) ∧ Squarefree (n₂ + a))}).Finite := by
      rcases h.exists_gt 0 with ⟨ n₁, hn₁ ⟩;
      obtain ⟨ n₂, hn₂ ⟩ := h.exists_gt n₁;
      exact ⟨ n₁, n₂, hn₂.2, Set.Finite.subset ( hn₁.1.union hn₂.1 ) fun x hx => by by_cases h : Squarefree ( n₁ + x ) <;> aesop ⟩

/-
The upper density of a set is invariant under finite modifications.
-/
lemma upperDensity_finite_diff (A B : Set ℕ) (h : (A \ B).Finite ∧ (B \ A).Finite) : upperDensity A = upperDensity B := by
  -- Since the difference between the two sets is finite, the proportion of elements in A and B up to n is the same for large n.
  have h_prop : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (((A ∩ Set.Icc 1 n).ncard : ℝ) / n - ((B ∩ Set.Icc 1 n).ncard : ℝ) / n) < ε := by
    -- Since the difference between the two sets is finite, the number of elements in A and B up to n is the same for large n.
    have h_card_diff : ∃ C : ℕ, ∀ n : ℕ, ((A ∩ Set.Icc 1 n).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 n).ncard : ℝ) + C ∧ ((B ∩ Set.Icc 1 n).ncard : ℝ) ≤ ((A ∩ Set.Icc 1 n).ncard : ℝ) + C := by
      obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℕ, ∀ n : ℕ, ((A ∩ Set.Icc 1 n).ncard : ℝ) ≤ ((B ∩ Set.Icc 1 n).ncard : ℝ) + C₁ := by
        use h.1.toFinset.card;
        intro n
        have h_card_diff : (A ∩ Set.Icc 1 n).ncard ≤ (B ∩ Set.Icc 1 n).ncard + ((A \ B) ∩ Set.Icc 1 n).ncard := by
          have h_card_diff : (A ∩ Set.Icc 1 n) ⊆ (B ∩ Set.Icc 1 n) ∪ ((A \ B) ∩ Set.Icc 1 n) := by
            intro x hx; by_cases hxB : x ∈ B <;> aesop;
          exact le_trans ( Set.ncard_le_ncard h_card_diff ) ( Set.ncard_union_le _ _ );
        refine' mod_cast h_card_diff.trans ( add_le_add_left _ _ );
        rw [ ← Set.ncard_coe_finset ] ; exact Set.ncard_le_ncard fun x hx => by aesop;
      obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℕ, ∀ n : ℕ, ((B ∩ Set.Icc 1 n).ncard : ℝ) ≤ ((A ∩ Set.Icc 1 n).ncard : ℝ) + C₂ := by
        use h.2.toFinset.card + 1;
        intro n; norm_cast; simp +decide [ Set.ncard_eq_toFinset_card' ] ;
        have h_diff_card : Finset.filter (fun a => a ∈ B) (Finset.Icc 1 n) ⊆ Finset.filter (fun a => a ∈ A) (Finset.Icc 1 n) ∪ h.2.toFinset := by
          intro x hx; by_cases hx' : x ∈ A <;> aesop;
        exact le_trans ( Finset.card_le_card h_diff_card ) ( Finset.card_union_le _ _ ) |> le_trans <| by linarith;
      use max C₁ C₂
      intro n
      exact ⟨by
      exact le_trans ( hC₁ n ) ( add_le_add_left ( mod_cast le_max_left _ _ ) _ ), by
        exact le_trans ( hC₂ n ) ( add_le_add_left ( mod_cast le_max_right _ _ ) _ )⟩;
    intro ε hε; obtain ⟨ C, hC ⟩ := h_card_diff; use ⌈ε⁻¹ * ( C + 1 ) ⌉₊ + 1; intro n hn; rw [ abs_lt ] ; constructor <;> nlinarith [ Nat.le_ceil ( ε⁻¹ * ( C + 1 ) ), mul_inv_cancel₀ hε.ne', show ( n : ℝ ) ≥ ⌈ε⁻¹ * ( C + 1 ) ⌉₊ + 1 by exact_mod_cast hn, hC n, div_mul_cancel₀ ( ( A ∩ Set.Icc 1 n |> Set.ncard : ℝ ) : ℝ ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ), div_mul_cancel₀ ( ( B ∩ Set.Icc 1 n |> Set.ncard : ℝ ) : ℝ ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ] ;
  refine' le_antisymm _ _ <;> rw [ upperDensity ];
  · refine' le_csInf _ _;
    · refine' ⟨ 1, _ ⟩ ; norm_num;
      exact ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard ( show B ∩ Set.Icc 1 n ⊆ Set.Icc 1 n from Set.inter_subset_right ) ) ( by simp +decide [ Set.ncard_eq_toFinset_card' ] ) ) ( by positivity ) ⟩;
    · intro b hb;
      refine' le_of_forall_pos_le_add fun ε ε_pos => _;
      refine' csInf_le _ _;
      · exact ⟨ 0, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ N, hN ⟩ ; exact le_trans ( by positivity ) ( hN _ le_rfl ) ⟩;
      · norm_num +zetaDelta at *;
        obtain ⟨ N, hN ⟩ := h_prop ε ε_pos; obtain ⟨ M, hM ⟩ := hb; exact ⟨ Max.max N M, fun n hn => by linarith [ abs_lt.mp ( hN n ( le_trans ( le_max_left _ _ ) hn ) ), hM n ( le_trans ( le_max_right _ _ ) hn ) ] ⟩ ;
  · refine' le_csInf _ _ <;> norm_num;
    · exact ⟨ 1, ⟨ 1, fun n hn => by rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ show Set.ncard ( A ∩ Set.Icc 1 n ) ≤ n by exact le_trans ( Set.ncard_le_ncard <| Set.inter_subset_right ) <| by norm_num [ Set.ncard_eq_toFinset_card' ] ] ⟩ ⟩;
    · intro b x hx;
      refine' le_of_forall_pos_le_add fun ε ε_pos => _;
      refine' csInf_le _ _ <;> norm_num;
      · exact ⟨ 0, by rintro _ ⟨ N, hN ⟩ ; exact le_trans ( by positivity ) ( hN _ le_rfl ) ⟩;
      · obtain ⟨ N, hN ⟩ := h_prop ε ε_pos ; exact ⟨ Max.max x N, fun n hn => by linarith [ abs_lt.mp ( hN n ( le_trans ( le_max_right _ _ ) hn ) ), hx n ( le_trans ( le_max_left _ _ ) hn ) ] ⟩

/-
The density of a set defined by modular constraints modulo squares of distinct primes is the product of the local densities.
-/
lemma density_of_coprime_mod_sieve (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (R : ℕ → Finset ℕ)
    (hR : ∀ p ∈ S, R p ⊆ Finset.range (p^2)) :
    let M := ∏ p ∈ S, p^2
    let B := {n : ℕ | ∀ p ∈ S, n % p^2 ∈ R p}
    M > 0 ∧
    (∀ n, n ∈ B ↔ n + M ∈ B) ∧
    ((B ∩ Set.Icc 1 M).ncard : ℝ) / M = ∏ p ∈ S, ((R p).card : ℝ) / p^2 := by
      refine' ⟨ Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( hS p hp ) ) _, _, _ ⟩;
      · simp +zetaDelta at *;
        intro n; congr! 2; simp +decide [ Nat.add_mod, Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_coe.mpr ‹_› ] ;
      · -- By the Chinese Remainder Theorem, the number of solutions modulo M is the product of the number of choices for each p.
        have h_crt : Finset.card (Finset.filter (fun n => ∀ p ∈ S, (n % p^2) ∈ R p) (Finset.range (∏ p ∈ S, p^2))) = ∏ p ∈ S, (Finset.card (R p)) := by
          induction' S using Finset.induction with p S hS ih;
          · norm_num;
          · have h_crt : ∀ (a b : ℕ), Nat.Coprime a b → ∀ (A : Finset ℕ), A ⊆ Finset.range a → ∀ (B : Finset ℕ), B ⊆ Finset.range b → Finset.card (Finset.filter (fun n => n % a ∈ A ∧ n % b ∈ B) (Finset.range (a * b))) = Finset.card A * Finset.card B := by
              intros a b hab A hA B hB;
              have h_crt : Finset.card (Finset.filter (fun n => n % a ∈ A ∧ n % b ∈ B) (Finset.range (a * b))) = Finset.card (Finset.product A B) := by
                refine' Finset.card_bij ( fun n hn => ( n % a, n % b ) ) _ _ _;
                · aesop;
                · simp +zetaDelta at *;
                  intro a₁ ha₁ ha₂ ha₃ a₂ ha₄ ha₅ ha₆ ha₇ ha₈;
                  -- Since $a$ and $b$ are coprime, by the Chinese Remainder Theorem, $a₁ \equiv a₂ \pmod{ab}$.
                  have h_crt : a₁ ≡ a₂ [MOD a] ∧ a₁ ≡ a₂ [MOD b] → a₁ ≡ a₂ [MOD (a * b)] := by
                    rw [ Nat.modEq_and_modEq_iff_modEq_mul ] ; aesop;
                    assumption;
                  exact Nat.mod_eq_of_lt ha₁ ▸ Nat.mod_eq_of_lt ha₄ ▸ h_crt ⟨ ha₇, ha₈ ⟩;
                · simp +zetaDelta at *;
                  intro x y hx hy;
                  -- By the Chinese Remainder Theorem, there exists a unique $z$ modulo $ab$ such that $z \equiv x \pmod{a}$ and $z \equiv y \pmod{b}$.
                  obtain ⟨z, hz⟩ : ∃ z, z < a * b ∧ z ≡ x [MOD a] ∧ z ≡ y [MOD b] := by
                    have := Nat.chineseRemainder hab x y;
                    exact ⟨ this.val % ( a * b ), Nat.mod_lt _ ( Nat.mul_pos ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.2 ⟩;
                  use z;
                  have := hA hx; have := hB hy; simp_all +decide [ Nat.ModEq, Nat.mod_eq_of_lt ] ;
              exact h_crt.trans ( Finset.card_product _ _ );
            simp_all +decide [Finset.prod_insert];
            convert h_crt ( p ^ 2 ) ( ∏ p ∈ S, p ^ 2 ) _ ( R p ) hR.1 ( Finset.filter ( fun n => ∀ p ∈ S, n % p ^ 2 ∈ R p ) ( Finset.range ( ∏ p ∈ S, p ^ 2 ) ) ) _ using 1;
            · congr! 2;
              ext; simp +decide ;
              intro hx; refine' ⟨ fun h => ⟨ Nat.mod_lt _ ( Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos ( hS.2 q hq ) ) 2 ), fun q hq => _ ⟩, fun h => _ ⟩ <;> simp_all +decide [ Nat.mod_mod_of_dvd _ ( Finset.dvd_prod_of_mem _ _ ) ] ;
            · rw [ ih ];
            · exact Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹p ∉ S› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 q hq ) ; aesop;
            · exact Finset.filter_subset _ _;
        -- The set of integers in [1, M] satisfying the modular constraints is exactly the set of solutions modulo M.
        have h_eq : {n | ∀ p ∈ S, (n % p^2) ∈ R p} ∩ (Set.Icc 1 (∏ p ∈ S, p^2)) = Finset.image (fun n => if n = 0 then ∏ p ∈ S, p^2 else n) (Finset.filter (fun n => ∀ p ∈ S, (n % p^2) ∈ R p) (Finset.range (∏ p ∈ S, p^2))) := by
          ext;
          simp +zetaDelta at *;
          constructor <;> intro h;
          · use if ‹_› = ∏ p ∈ S, p ^ 2 then 0 else ‹_›;
            split_ifs <;> simp_all +decide;
            · exact ⟨ fun p hp => pow_pos ( Nat.Prime.pos ( hS p hp ) ) 2, fun p hp => by simpa [ Nat.mod_eq_zero_of_dvd ( Finset.dvd_prod_of_mem _ hp ) ] using h.1 p hp ⟩;
            · exact lt_of_le_of_ne h.2.2 ‹_›;
          · rcases h with ⟨ x, hx, rfl ⟩ ; split_ifs <;> simp_all +decide ;
            · exact ⟨ fun p hp => by rw [ Nat.mod_eq_zero_of_dvd ( Finset.dvd_prod_of_mem _ hp ) ] ; exact hx.2 p hp, Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( hS p hp ) ) 2 ⟩;
            · exact ⟨ Nat.pos_of_ne_zero ‹_›, hx.1.le ⟩;
        rw [ h_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn ];
        · aesop;
        · intro x hx y hy; aesop

/-
For any K > C, the upper density of A is bounded by the product of (1 - 1/p^2) for p <= C and (1 - 2/p^2) for C < p <= K.
-/
lemma sieve_finite_bound (A : Set ℕ) (C K : ℕ) (hK : K > C)
    (h1 : ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ A, a % p^2 ≠ b)
    (h2 : ∀ p, Nat.Prime p → p > C → ∃ b1 b2, b1 < p^2 ∧ b2 < p^2 ∧ b1 ≠ b2 ∧ (∀ a ∈ A, a % p^2 ≠ b1) ∧ (∀ a ∈ A, a % p^2 ≠ b2)) :
    upperDensity A ≤ (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (C + 1) K), (1 - 2 / (p : ℝ)^2)) := by
      obtain ⟨B, hB⟩ : ∃ B : Set ℕ, A ⊆ B ∧ (∃ M > 0, (∀ n, n ∈ B ↔ n + M ∈ B) ∧ ((B ∩ Set.Icc 1 M).ncard : ℝ) / M = (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 K), if p ≤ C then (1 - 1/(p:ℝ)^2) else (1 - 2/(p:ℝ)^2))) := by
        -- Let $S$ be the set of primes in $[1, K]$.
        set S := Finset.filter Nat.Prime (Finset.Icc 1 K) with hS_def;
        -- For each $p \in S$, let $R(p) = \{x \in [0, p^2-1] \mid \exists a \in A, a \equiv x \pmod{p^2}\}$.
        obtain ⟨R, hR⟩ : ∃ R : ℕ → Finset ℕ, (∀ p ∈ S, R p ⊆ Finset.range (p^2)) ∧ (∀ p ∈ S, (R p).card = if p ≤ C then p^2 - 1 else p^2 - 2) ∧ A ⊆ {n : ℕ | ∀ p ∈ S, n % p^2 ∈ R p} := by
          choose! b hb₁ hb₂ using h1;
          choose! b1 b2 hb3 hb4 hb5 hb6 hb7 using h2;
          refine' ⟨ fun p => if p ≤ C then Finset.range ( p ^ 2 ) \ { b p } else Finset.range ( p ^ 2 ) \ { b1 p, b2 p }, _, _, _ ⟩ <;> simp_all +decide;
          · intro p hp₁ hp₂ hp₃; split_ifs <;> simp +decide [ Finset.sdiff_subset ] ;
          · intro p hp₁ hp₂ hp₃; split_ifs <;> simp_all +decide [ Finset.card_sdiff, Finset.card_singleton ] ;
          · intro a ha p hp₁ hp₂ hp₃; split_ifs <;> simp_all +decide [ Finset.mem_sdiff, Finset.mem_singleton ] ;
            · exact Nat.mod_lt _ ( by positivity );
            · exact Nat.mod_lt _ ( by positivity );
        refine' ⟨ { n | ∀ p ∈ S, n % p ^ 2 ∈ R p }, hR.2.2, ∏ p ∈ S, p ^ 2, _, _, _ ⟩;
        · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2;
        · simp +decide [ Nat.add_mod ];
          intro n; refine' forall₂_congr fun p hp => _; simp +decide [ Nat.mod_eq_zero_of_dvd ( Finset.dvd_prod_of_mem _ hp ) ] ;
        · convert density_of_coprime_mod_sieve S ( fun p hp => Finset.mem_filter.mp hp |>.2 ) R ( fun p hp => hR.1 p hp ) |> And.right |> And.right using 1;
          refine' Finset.prod_congr rfl fun p hp => _;
          rw [ hR.2.1 p hp ] ; split_ifs <;> norm_num [ Nat.cast_sub ( show 1 ≤ p ^ 2 from pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2 ), Nat.cast_sub ( show 2 ≤ p ^ 2 from by nlinarith only [ Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ) ] ; ring_nf;
          · norm_num [ Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ];
          · rw [ sub_div, div_self ( by norm_cast; nlinarith only [ Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ) ];
      obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := hB.2;
      refine' le_trans ( density_of_subset_periodic A B M hM₁ hM₂ hB.1 ) _;
      convert hM₃.le using 1;
      rw [ show ( Finset.filter Nat.Prime ( Finset.Icc 1 K ) ) = Finset.filter Nat.Prime ( Finset.Icc 1 C ) ∪ Finset.filter Nat.Prime ( Finset.Icc ( C + 1 ) K ) from ?_, Finset.prod_union ];
      · exact congrArg₂ _ ( Finset.prod_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ] ) ( Finset.prod_congr rfl fun x hx => by rw [ if_neg ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ] ) ] );
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
      · ext; simp [Finset.mem_union, Finset.mem_filter];
        grind

/-
The infinite product of (1 - 2/p^2) for p > C is strictly less than the infinite product of (1 - 1/p^2) for p > C.
-/
lemma prod_inequality (C : ℕ) :
  (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1) <
  (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 1 / (p : ℝ)^2) else 1) := by
    have h_log_lt : Summable (fun p : ℕ => if Nat.Prime p ∧ C < p then Real.log (1 - 1 / (p : ℝ)^2) else 0) ∧ Summable (fun p : ℕ => if Nat.Prime p ∧ C < p then Real.log (1 - 2 / (p : ℝ)^2) else 0) := by
      constructor;
      · -- We can bound the absolute value of the logarithm by the absolute value of the argument.
        have h_log_bound : ∀ p : ℕ, Nat.Prime p ∧ C < p → |Real.log (1 - 1 / (p : ℝ) ^ 2)| ≤ 2 / (p : ℝ) ^ 2 := by
          intro p hp
          have h_log_bound : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 4 → |Real.log (1 - x)| ≤ 2 * x := by
            intro x hx; rw [ abs_of_nonpos ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ] ; nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
          convert h_log_bound ( 1 / ( p : ℝ ) ^ 2 ) ⟨ by exact one_div_pos.mpr ( sq_pos_of_pos ( Nat.cast_pos.mpr hp.1.pos ) ), by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith [ hp.1.two_le ] ⟩ using 1 ; ring;
        have h_summable : Summable (fun p : ℕ => 2 / (p : ℝ) ^ 2) := by
          exact Summable.mul_left _ <| Real.summable_nat_pow_inv.2 one_lt_two;
        -- Apply the comparison test with the summable series ∑' p : ℕ, 2 / (p : ℝ) ^ 2.
        have h_comparison : Summable (fun p : ℕ => |if Nat.Prime p ∧ C < p then Real.log (1 - 1 / (p : ℝ) ^ 2) else 0|) := by
          exact Summable.of_nonneg_of_le ( fun p => abs_nonneg _ ) ( fun p => by split_ifs <;> [ exact h_log_bound p ‹_›; exact by norm_num; positivity ] ) h_summable;
        exact h_comparison.of_abs;
      · -- The series $\sum_{p > C} \log(1 - 2/p^2)$ converges absolutely because $\log(1 - 2/p^2) \leq -2/p^2$ and $\sum_{p > C} 2/p^2$ converges.
        have h_abs_conv : Summable (fun p : ℕ => if Nat.Prime p ∧ C < p then |Real.log (1 - 2 / (p : ℝ)^2)| else 0) := by
          -- We'll use the fact that |Real.log (1 - x)| ≤ 2x for x in [0, 1/2].
          have h_log_bound : ∀ p : ℕ, Nat.Prime p → C < p → |Real.log (1 - 2 / (p : ℝ)^2)| ≤ 4 / (p : ℝ)^2 := by
            intros p hp hC
            have h_log_bound : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → abs (Real.log (1 - x)) ≤ 2 * x := by
              intros x hx; rw [ abs_of_nonpos ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ] ; nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
            convert h_log_bound ( 2 / ( p : ℝ ) ^ 2 ) ⟨ by exact div_pos zero_lt_two ( sq_pos_of_pos ( Nat.cast_pos.mpr hp.pos ) ), by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith [ hp.two_le ] ⟩ using 1 ; ring;
          refine' Summable.of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ( Summable.mul_left 4 <| Real.summable_nat_pow_inv.2 one_lt_two );
          · positivity;
          · split_ifs <;> [ exact h_log_bound p ( by tauto ) ( by tauto ) ; exact by positivity ];
        exact Summable.of_norm <| h_abs_conv.congr fun p => by split_ifs <;> norm_num;
    have h_exp_log_lt : (∏' p : ℕ, if Nat.Prime p ∧ C < p then (1 - 2 / (p : ℝ)^2) else 1) = Real.exp (∑' p : ℕ, if Nat.Prime p ∧ C < p then Real.log (1 - 2 / (p : ℝ)^2) else 0) ∧ (∏' p : ℕ, if Nat.Prime p ∧ C < p then (1 - 1 / (p : ℝ)^2) else 1) = Real.exp (∑' p : ℕ, if Nat.Prime p ∧ C < p then Real.log (1 - 1 / (p : ℝ)^2) else 0) := by
      constructor <;> rw [ Real.exp_eq_exp_ℝ ];
      · have h_exp_log_lt : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → (∏' p, f p) = Real.exp (∑' p, Real.log (f p)) := by
          exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1);
        convert h_exp_log_lt _ _ using 1;
        · rw [ Real.exp_eq_exp_ℝ ] ; congr ; ext p ; aesop;
        · intro p; split_ifs <;> norm_num;
          rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.Prime.two_le ( by tauto : Nat.Prime p ) ];
        · exact h_log_lt.2.congr fun p => by aesop;
      · have h_exp_log_lt : ∀ {f : ℕ → ℝ}, (∀ p, 0 < f p) → Summable (fun p => Real.log (f p)) → (∏' p, f p) = Real.exp (∑' p, Real.log (f p)) := by
          exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1);
        rw [ ← Real.exp_eq_exp_ℝ, h_exp_log_lt ];
        · exact congr_arg Real.exp ( tsum_congr fun p => by split_ifs <;> norm_num );
        · intro p; split_ifs <;> norm_num;
          exact inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( mod_cast Nat.Prime.one_lt ( by tauto ) ) two_ne_zero;
        · exact h_log_lt.1.congr fun p => by split_ifs <;> norm_num;
    -- Since there exists at least one prime $p > C$, we can find such a prime $p$.
    obtain ⟨p, hp_prime, hp_gt⟩ : ∃ p : ℕ, Nat.Prime p ∧ C < p := by
      exact Exists.imp ( by tauto ) ( Nat.exists_infinite_primes ( C + 1 ) );
    have h_log_lt : ∑' p : ℕ, (if Nat.Prime p ∧ C < p then Real.log (1 - 2 / (p : ℝ)^2) else 0) < ∑' p : ℕ, (if Nat.Prime p ∧ C < p then Real.log (1 - 1 / (p : ℝ)^2) else 0) := by
      fapply Summable.tsum_lt_tsum;
      use p;
      · intro n; by_cases hn : Nat.Prime n ∧ C < n <;> simp +decide [ hn ];
        exact Real.log_le_log ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith only [ hn.1.two_le ] ) <| sub_le_sub_left ( by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith only [ hn.1.two_le ] ) _;
      · rw [ if_pos ⟨ hp_prime, hp_gt ⟩, if_pos ⟨ hp_prime, hp_gt ⟩ ];
        exact Real.log_lt_log ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith only [ hp_prime.two_le ] ) <| sub_lt_sub_left ( by rw [ div_lt_div_iff_of_pos_right ] <;> norm_cast ; nlinarith only [ hp_prime.two_le ] ) _;
      · exact h_log_lt.2;
      · exact h_log_lt.1;
    aesop

/-
If a set A avoids at least 1 residue class mod p^2 for all p, and at least 2 residue classes mod p^2 for all p > C, then its upper density is strictly less than 6/pi^2.
-/
lemma sieve_strict_bound (A : Set ℕ) (C : ℕ)
    (h1 : ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ A, a % p^2 ≠ b)
    (h2 : ∀ p, Nat.Prime p → p > C → ∃ b1 b2, b1 < p^2 ∧ b2 < p^2 ∧ b1 ≠ b2 ∧ (∀ a ∈ A, a % p^2 ≠ b1) ∧ (∀ a ∈ A, a % p^2 ≠ b2)) :
    upperDensity A < 6 / Real.pi^2 := by
      have h_limit : Filter.Tendsto (fun K => (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (C + 1) K), (1 - 2 / (p : ℝ)^2))) Filter.atTop (nhds ((∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1))) := by
        refine' Filter.Tendsto.mul tendsto_const_nhds _;
        have h_partial_prod : Filter.Tendsto (fun K => ∏ p ∈ Finset.filter (fun p => Nat.Prime p ∧ p > C) (Finset.range (K + 1)), (1 - 2 / (p : ℝ)^2)) Filter.atTop (nhds (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1)) := by
          have h_partial_prod : Filter.Tendsto (fun K => ∏ p ∈ Finset.range (K + 1), (if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1)) Filter.atTop (nhds (∏' p : ℕ, (if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1))) := by
            have h_limit : Multipliable (fun p : ℕ => if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1) := by
              have h_abs_conv : Summable (fun p : ℕ => |Real.log (if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1)|) := by
                have h_prod_conv : Summable (fun p : ℕ => |Real.log (1 - 2 / (p : ℝ)^2)| * (if Nat.Prime p ∧ p > C then 1 else 0)) := by
                  have h_prod_conv : Summable (fun p : ℕ => |Real.log (1 - 2 / (p : ℝ)^2)|) := by
                    -- We'll use the fact that |log(1 - x)| ≤ 2x for x in [0, 1/2].
                    have h_log_bound : ∀ p : ℕ, p ≥ 2 → |Real.log (1 - 2 / (p : ℝ)^2)| ≤ 4 / (p : ℝ)^2 := by
                      intros p hp
                      have h_log_bound : |Real.log (1 - 2 / (p : ℝ)^2)| ≤ 2 / (p : ℝ)^2 / (1 - 2 / (p : ℝ)^2) := by
                        have h_log_bound : ∀ x : ℝ, 0 < x ∧ x < 1 → |Real.log (1 - x)| ≤ x / (1 - x) := by
                          intros x hx; rw [ abs_of_nonpos ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ] ; rw [ div_eq_mul_inv ] ; nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
                        exact h_log_bound _ ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith ⟩;
                      refine le_trans h_log_bound ?_;
                      rw [ div_div, div_le_div_iff₀ ] <;> nlinarith only [ show ( p : ℝ ) ≥ 2 by norm_cast, show ( p : ℝ ) ^ 2 ≥ 4 by norm_cast; nlinarith, div_mul_cancel₀ ( 2 : ℝ ) ( show ( p : ℝ ) ^ 2 ≠ 0 by positivity ) ];
                    exact Summable.of_nonneg_of_le ( fun p => abs_nonneg _ ) ( fun p => if hp : p ≥ 2 then h_log_bound p hp else by interval_cases p <;> norm_num ) ( Summable.mul_left _ <| Real.summable_nat_pow_inv.2 one_lt_two );
                  exact Summable.of_nonneg_of_le ( fun p => mul_nonneg ( abs_nonneg _ ) ( by positivity ) ) ( fun p => mul_le_of_le_one_right ( abs_nonneg _ ) ( by aesop ) ) h_prod_conv;
                convert h_prod_conv using 2 ; aesop;
              have h_abs_conv : Multipliable (fun p : ℕ => Real.exp (Real.log (if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1))) := by
                refine' ⟨ _, _ ⟩;
                exact Real.exp ( ∑' p : ℕ, Real.log ( if Nat.Prime p ∧ p > C then 1 - 2 / ( p : ℝ ) ^ 2 else 1 ) );
                convert h_abs_conv.of_abs.hasSum.exp using 1;
                any_goals exact ℝ;
                all_goals first | infer_instance | simp +decide [ Real.exp_eq_exp_ℝ ];
                rfl;
              convert h_abs_conv using 1;
              ext p; split_ifs <;> norm_num;
              rw [ Real.exp_log ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.Prime.two_le ( by tauto : Nat.Prime p ) ] ) ];
            convert h_limit.hasProd.tendsto_prod_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) using 1;
          convert h_partial_prod using 2 ; simp +decide [ Finset.prod_ite ];
        convert h_partial_prod using 2;
        congr! 1;
        ext; simp [Finset.mem_Icc];
        exact ⟨ fun h => ⟨ by linarith, h.2, by linarith ⟩, fun h => ⟨ ⟨ by linarith, by linarith ⟩, h.2.1 ⟩ ⟩;
      have h_limit : (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1) < 6 / Real.pi ^ 2 := by
        have h_limit : (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 2 / (p : ℝ)^2) else 1) < (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 1 / (p : ℝ)^2) else 1) := by
          apply_rules [ mul_lt_mul_of_pos_left, prod_inequality ];
          exact Finset.prod_pos fun p hp => sub_pos_of_lt <| by simpa using inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( mod_cast Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) two_ne_zero;
        have h_limit : (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 1 / (p : ℝ)^2) else 1) = (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) := by
          have h_limit : (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) = (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 C), (1 - 1 / (p : ℝ)^2)) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 1 / (p : ℝ)^2) else 1) := by
            have h_split : (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) = (∏' p : ℕ, if Nat.Prime p ∧ p ≤ C then (1 - 1 / (p : ℝ)^2) else 1) * (∏' p : ℕ, if Nat.Prime p ∧ p > C then (1 - 1 / (p : ℝ)^2) else 1) := by
              rw [ ← Multipliable.tprod_mul ];
              · congr with p ; by_cases hp : Nat.Prime p <;> by_cases hp' : p ≤ C <;> simp +decide [ hp, hp' ];
              · refine' multipliable_of_ne_finset_one _;
                exacts [ Finset.range ( C + 1 ), fun p hp => if_neg fun h => hp <| Finset.mem_range.mpr <| by linarith ];
              · have h_prod_conv : Summable (fun p : ℕ => if Nat.Prime p ∧ p > C then (1 / (p : ℝ)^2) else 0) := by
                  exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
                have h_prod_conv : Multipliable (fun p : ℕ => 1 - (if Nat.Prime p ∧ p > C then (1 / (p : ℝ)^2) else 0)) := by
                  refine' multipliable_one_add_of_summable _;
                  exact h_prod_conv.norm.congr fun n => by split_ifs <;> norm_num;
                convert h_prod_conv using 2 ; aesop
            convert h_split using 2;
            rw [ tprod_eq_prod ];
            any_goals exact Finset.filter Nat.Prime ( Finset.Icc 1 C );
            · exact Finset.prod_congr rfl fun x hx => by aesop;
            · aesop;
          rw [h_limit];
        have h_limit : (∏' p : ℕ, if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) = 6 / Real.pi ^ 2 := by
          convert tendsto_nhds_unique ( show Filter.Tendsto ( fun k => ∏ p ∈ Finset.filter Nat.Prime ( Finset.range k ), ( 1 - 1 / ( p : ℝ ) ^ 2 ) ) Filter.atTop ( nhds ( ∏' p : ℕ, if Nat.Prime p then ( 1 - 1 / ( p : ℝ ) ^ 2 ) else 1 ) ) from ?_ ) ( prod_primes_inv_sq_tendsto ) using 1;
          have h_prod : Multipliable (fun p : ℕ => if Nat.Prime p then (1 - 1 / (p : ℝ)^2) else 1) := by
            have h_prod : Summable (fun p : ℕ => if Nat.Prime p then (1 / (p : ℝ)^2) else 0) := by
              exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
            have h_prod : Multipliable (fun p : ℕ => 1 - (if Nat.Prime p then (1 / (p : ℝ)^2) else 0)) := by
              refine' multipliable_one_add_of_summable _;
              exact h_prod.norm.congr fun _ => by split_ifs <;> norm_num;
            convert h_prod using 2 ; aesop;
          convert h_prod.hasProd.tendsto_prod_nat using 1;
          exact funext fun n => by rw [ Finset.prod_filter ] ;
        linarith;
      refine' lt_of_le_of_lt _ h_limit;
      exact le_of_tendsto_of_tendsto tendsto_const_nhds ‹_› ( Filter.eventually_atTop.mpr ⟨ C + 1, fun K hK => sieve_finite_bound A C K ( by linarith ) h1 h2 ⟩ )

/-
The tail sum of 1/(p (log log p)^2) tends to 0 as P goes to infinity.
-/
lemma tail_sum_bound (assumps : SieveAssumptions) :
    Filter.Tendsto (fun P => ∑' p, if p > P ∧ Nat.Prime p then 1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0) Filter.atTop (nhds 0) := by
      have := assumps.bound_sum_primes_ge_x_inv_p_loglog_sq;
      convert this.isBigO.trans_isLittleO _;
      any_goals exact Real;
      any_goals exact fun x => 1;
      any_goals exact Real.norm;
      · constructor <;> intro h;
        · convert this.isBigO.trans_isLittleO _;
          rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
          exact tendsto_inv_atTop_zero.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop;
        · rw [ Asymptotics.isLittleO_iff_tendsto' ] at h <;> norm_num at *;
          convert h.comp ( show Filter.Tendsto ( fun P : ℕ => ↑P + 1 ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) using 2 ; norm_num;
          norm_cast;
      · rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
        exact tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) )

/-
The sum of p/(log log p)^2 for p <= sqrt(2x) is o(x).
-/
lemma error_term_small (assumps : SieveAssumptions) :
  (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x)) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (p : ℝ) / (Real.log (Real.log p))^2) =o[Filter.atTop] (fun x => x) := by
    rw [ Asymptotics.isLittleO_iff_tendsto' ];
    · -- Applying the hypothesis `assumps.bound_sum_primes_le_x_p_div_loglog_sq` with $y = \sqrt{2x}$.
      have h_apply_bound : Filter.Tendsto (fun x => (∑ p ∈ Finset.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (p : ℝ) / (Real.log (Real.log p))^2) / x) Filter.atTop (nhds 0) := by
        have h_apply_bound : Filter.Tendsto (fun y => (∑ p ∈ Finset.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) ≤ y ∧ Nat.Prime p) (Finset.range (Nat.floor y + 1)), (p : ℝ) / (Real.log (Real.log p))^2) / y^2) Filter.atTop (nhds 0) := by
          have := assumps.bound_sum_primes_le_x_p_div_loglog_sq;
          have := this.isBigO;
          rw [ Asymptotics.isBigO_iff' ] at this;
          obtain ⟨ c, hc₀, hc ⟩ := this;
          -- We'll use the fact that if the denominator grows faster than the numerator, the limit will tend to 0.
          have h_lim : Filter.Tendsto (fun y => c * (1 / (Real.log y * (Real.log (Real.log y))^2))) Filter.atTop (nhds 0) := by
            norm_num;
            exact le_trans ( Filter.Tendsto.mul tendsto_const_nhds <| Filter.Tendsto.mul ( Filter.Tendsto.inv_tendsto_atTop <| Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop ) <| Filter.Tendsto.inv_tendsto_atTop <| Real.tendsto_log_atTop ) <| by norm_num;
          refine' squeeze_zero_norm' _ h_lim;
          filter_upwards [ hc, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ ; simp_all +decide [div_eq_mul_inv,
            mul_comm];
          rw [ inv_mul_le_iff₀ ( by positivity ) ] ; convert hx₁ using 1 ; rw [ abs_of_nonneg ( Real.log_nonneg hx₂.le ) ] ; ring;
        have h_apply_bound : Filter.Tendsto (fun x => (∑ p ∈ Finset.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (p : ℝ) / (Real.log (Real.log p))^2) / (Real.sqrt (2 * x))^2) Filter.atTop (nhds 0) := by
          exact h_apply_bound.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2 / 2, fun y hy => Real.le_sqrt_of_sq_le <| by linarith ⟩;
        convert h_apply_bound.const_mul 2 |> Filter.Tendsto.congr' _ using 2;
        · norm_num;
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.sq_sqrt ( by positivity ) ] ; ring;
      -- Since the primes less than or equal to 2 are finite, their contribution to the sum is bounded.
      have h_finite_primes : ∃ C : ℝ, ∀ x : ℝ, x ≥ 2 → (∑ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x)) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (p : ℝ) / (Real.log (Real.log p))^2) ≤ (∑ p ∈ Finset.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (p : ℝ) / (Real.log (Real.log p))^2) + C := by
        use ∑ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p ∧ p ≤ 2) (Finset.range 3), (p : ℝ) / (Real.log (Real.log p))^2;
        intro x hx; rw [ ← Finset.sum_union ];
        · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ );
          grind;
        · exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => by linarith [ Finset.mem_filter.mp hp₁, Finset.mem_filter.mp hp₂ ] ;
      obtain ⟨ C, hC ⟩ := h_finite_primes;
      refine' squeeze_zero_norm' _ ( by simpa using h_apply_bound.add ( tendsto_inv_atTop_zero.const_mul ( C : ℝ ) ) );
      filter_upwards [ Filter.eventually_ge_atTop 2 ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ ) ) ( by positivity ) ) ] ; simpa [ div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm ] using div_le_div_of_nonneg_right ( hC x hx ) ( by positivity ) ;
    · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne'

/-
Definitions for relevant primes, bound for a, relevant pairs, and the set S_x of multiples of W in the interval. Corrected type of relevant_pairs.
-/
def relevant_primes (P : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)).filter (fun p => Nat.Prime p ∧ p > P)

def a_bound (p : ℕ) : ℕ := Nat.floor ((p : ℝ) / (Real.log (Real.log p))^2)

def relevant_pairs (P : ℕ) (x : ℝ) : Finset (ℕ × ℕ) :=
  (relevant_primes P x).biUnion (fun p => (Finset.Icc 1 (a_bound p)).image (fun a => (p, a)))

def S_x (x : ℝ) (W : ℕ) : Finset ℕ :=
  (Finset.Icc (Nat.ceil (x/2)) (Nat.floor x)).filter (fun n => n % W = 0)

/-
Definitions for W_P (product of p^2 for p <= P) and the set of bad n for a specific pair (p, a).
-/
def W_P (P : ℕ) : ℕ := ∏ p ∈ Finset.filter Nat.Prime (Finset.range (P + 1)), p^2

def bad_n_for_pair (x : ℝ) (W : ℕ) (p a : ℕ) : Finset ℕ :=
  (S_x x W).filter (fun n => (n + a) % p^2 = 0)

/-
Length of the interval [ceil(x/2), floor(x)].
-/
def L_x (x : ℝ) : ℕ := Nat.floor x - Nat.ceil (x/2) + 1

/-
The number of bad n for a given pair (p, a) is at most L_x / (W p^2) + 2.
-/
lemma bad_n_for_pair_bound (x : ℝ) (W : ℕ) (p a : ℕ) (hW : W > 0) (hp : p > 0) (hWp : Nat.Coprime W (p^2)) :
  ((bad_n_for_pair x W p a).card : ℝ) ≤ (L_x x : ℝ) / (W * p^2) + 2 := by
    unfold bad_n_for_pair S_x L_x;
    by_cases h : ⌊x⌋₊ ≥ ⌈x / 2⌉₊ <;> simp_all +decide;
    · -- Apply the lemma about the number of solutions to the congruence $n \equiv 0 \pmod{W}$ and $n \equiv -a \pmod{p^2}$.
      have h_card : ((Finset.Icc ⌈x / 2⌉₊ ⌊x⌋₊).filter (fun n => n % W = 0 ∧ (n + a) % p ^ 2 = 0)).card ≤ (⌊x⌋₊ - ⌈x / 2⌉₊ + 1 : ℝ) / (W * p ^ 2) + 2 := by
        have h_card : ∀ (u L : ℕ) (W q : ℕ) (b c : ℕ), Nat.Coprime W q → W > 0 → q > 0 → let I := Finset.Icc u (u + L - 1); let S_intersect := I.filter (fun n => n ≡ b [MOD W] ∧ n ≡ c [MOD q]); (S_intersect.card : ℝ) ≤ (L : ℝ) / (W * q) + 2 := by
          intros u L W q b c hWq hW hq
          have h_card : abs ((Finset.card (Finset.filter (fun n => n ≡ b [MOD W] ∧ n ≡ c [MOD q]) (Finset.Icc u (u + L - 1))) : ℝ) - (L : ℝ) / (W * q)) ≤ 2 := by
            convert card_intersect_bound u L W q b c hWq hW hq using 1;
          linarith [ abs_le.mp h_card ];
        convert h_card ⌈x / 2⌉₊ (⌊x⌋₊ - ⌈x / 2⌉₊ + 1) W (p ^ 2) 0 (p ^ 2 - a % (p ^ 2)) _ _ _ using 1 <;> norm_num [ Nat.Coprime, Nat.gcd_comm ];
        · rw [ show ⌈x / 2⌉₊ + ( ⌊x⌋₊ - ⌈x / 2⌉₊ ) = ⌊x⌋₊ from add_tsub_cancel_of_le <| Nat.ceil_le.mpr <| by linarith ] ; congr! 2 ; simp +decide [Nat.ModEq] ;
          ext; simp +decide ;
          intro h; rw [ ← Nat.dvd_iff_mod_eq_zero ] at *; simp_all +decide [←
              ZMod.natCast_eq_zero_iff] ;
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
          rw [ Nat.cast_sub ( Nat.le_of_lt <| Nat.mod_lt _ <| by positivity ) ] ; simp +decide;
          rw [ eq_neg_iff_add_eq_zero ];
        · rw [ Nat.cast_sub ( Nat.ceil_le.mpr ( by linarith ) ) ];
        · exact hWp;
        · positivity;
        · positivity;
      simpa only [ Finset.filter_filter ] using h_card;
    · rw [ Finset.Icc_eq_empty ] <;> norm_num;
      · positivity;
      · linarith

/-
Definitions of sums S1 and S2, and a bound on the cardinality of S_x.
-/
def sum_S1 (P : ℕ) (x : ℝ) : ℝ := ∑ p ∈ relevant_primes P x, (a_bound p : ℝ) / p^2
def sum_S2 (P : ℕ) (x : ℝ) : ℝ := ∑ p ∈ relevant_primes P x, (a_bound p : ℝ)

lemma card_S_x_bound (x : ℝ) (W : ℕ) (hW : W > 0) :
  abs ((S_x x W).card - (L_x x : ℝ) / W) ≤ 2 := by
    -- Apply the lemma `card_filter_modEq_Icc` to the interval [ceil(x/2), floor(x)].
    have h_apply_lemma : let I := Finset.Icc (Nat.ceil (x / 2)) (Nat.floor x);
      let S := I.filter (fun n => n % W = 0);
      abs ((S.card : ℝ) - (L_x x : ℝ) / W) ≤ 2 := by
        by_cases hx : ⌈x / 2⌉₊ ≤ ⌊x⌋₊ <;> simp_all +decide [ L_x ];
        · convert card_filter_modEq_Icc ⌈x / 2⌉₊ (⌊x⌋₊ - ⌈x / 2⌉₊ + 1) 0 W hW using 1;
          simp +decide [ Nat.ModEq, Nat.mod_eq_of_lt hW ];
          rw [ Nat.add_sub_of_le ( Nat.ceil_le.mpr ( by linarith ) ) ] ; rw [ Nat.cast_sub ( Nat.ceil_le.mpr ( by linarith ) ) ] ;
        · rw [ Nat.sub_eq_zero_of_le ] <;> norm_num;
          · rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
            · exact le_trans ( inv_le_one_of_one_le₀ <| mod_cast hW ) <| by norm_num;
            · intros; linarith [ Nat.floor_le ( show 0 ≤ x by linarith [ Nat.lt_floor_add_one x ] ), show ( ↑‹ℕ› : ℝ ) ≤ ⌊x⌋₊ by norm_cast ] ;
          · exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( x / 2 ) ] ;
    convert h_apply_lemma using 1

/-
Bound for the term a_bound p / p^2.
-/
lemma a_bound_term_le (p : ℕ) (hp : p ≥ 3) :
  (a_bound p : ℝ) / p^2 ≤ 1 / ((p : ℝ) * (Real.log (Real.log p))^2) := by
    field_simp;
    exact Nat.floor_le ( div_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ ) )

/-
Definition of tail_val as the infinite sum of 1/(p (log log p)^2) for primes p > P.
-/
def tail_val (P : ℕ) : ℝ := ∑' p, if p > P ∧ Nat.Prime p then 1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0

/-
sum_S1 is bounded by the sum of the upper bounds of its terms.
-/
lemma sum_S1_le_sum_bound (P : ℕ) (x : ℝ) :
  sum_S1 P x ≤ ∑ p ∈ relevant_primes P x, 1 / ((p : ℝ) * (Real.log (Real.log p))^2) := by
    apply Finset.sum_le_sum;
    intro p hp; by_cases hp3 : p ≥ 3;
    · convert a_bound_term_le p hp3 using 1;
    · interval_cases p <;> norm_num [ a_bound ] at hp ⊢;
      rw [ div_le_iff₀ ] <;> norm_num;
      exact Nat.floor_le ( by positivity ) |> le_trans <| by ring_nf; norm_num;

/-
The tail series of 1/(p (log log p)^2) is summable.
-/
lemma tail_summable (assumps : SieveAssumptions) (P : ℕ) :
  Summable (fun p : ℕ => if p > P ∧ Nat.Prime p then 1 / ((p : ℝ) * (Real.log (Real.log p))^2) else 0) := by
    contrapose! assumps;
    rintro ⟨ h1, h2, h3, h4, h5, h6 ⟩;
    have := h3;
    obtain ⟨ C, hC ⟩ := this;
    rw [ Asymptotics.isBigO_iff ] at hC;
    obtain ⟨ c, hc ⟩ := hC; obtain ⟨ x, hx ⟩ := Filter.eventually_atTop.mp hc; specialize hx ( Max.max x 3 ) ; norm_num at hx;
    rw [ tsum_eq_zero_of_not_summable ] at hx <;> norm_num at hx;
    · rcases hx with ( ( hx | hx | hx ) | hx | hx ) <;> linarith [ le_max_right x 3, Real.lt_log_iff_exp_lt ( show 0 < max x 3 by positivity ) |>.2 <| show Real.exp 1 < max x 3 by exact lt_of_lt_of_le ( Real.exp_one_lt_d9.trans_le <| by norm_num ) <| le_max_right x 3 ];
    · intro H;
      refine' assumps _;
      rw [ ← summable_nat_add_iff ( ⌈x⌉₊ + P + 3 ) ] at *;
      convert H using 2 ; norm_num ; ring_nf;
      exact if_congr ⟨ fun h => ⟨ ⟨ by linarith [ Nat.le_ceil x ], by linarith ⟩, h.2 ⟩, fun h => ⟨ by linarith, h.2 ⟩ ⟩ rfl rfl

/-
The sum over relevant primes is bounded by the tail value.
-/
lemma sum_subset_le_tail (P : ℕ) (x : ℝ) (assumps : SieveAssumptions) :
  ∑ p ∈ relevant_primes P x, 1 / ((p : ℝ) * (Real.log (Real.log p))^2) ≤ tail_val P := by
    refine' le_trans _ ( Summable.sum_le_tsum _ _ _ );
    refine' Finset.sum_le_sum fun p hp => _;
    · unfold relevant_primes at hp; aesop;
    · intro i hi; split_ifs <;> positivity;
    · exact tail_summable assumps P

/-
Sum S1 is bounded by the tail value.
-/
lemma sum_S1_le_tail (P : ℕ) (x : ℝ) (assumps : SieveAssumptions) : sum_S1 P x ≤ tail_val P := by
  refine le_trans ( sum_S1_le_sum_bound P x ) ( sum_subset_le_tail P x assumps )

/-
sum_S2 is o(x).
-/
lemma sum_S2_is_littleO (P : ℕ) (assumps : SieveAssumptions) :
  (fun x => sum_S2 P x) =o[Filter.atTop] (fun x => x) := by
    -- By definition of `sum_S2`, we have `sum_S2 P x ≤ ∑ p ∈ relevant_primes P x, p / (Real.log (Real.log p))^2`.
    have h_sum_S2_le : ∀ x : ℝ, sum_S2 P x ≤ ∑ p ∈ relevant_primes P x, (p : ℝ) / (Real.log (Real.log p))^2 := by
      intro x;
      refine' Finset.sum_le_sum fun p hp => _;
      exact Nat.floor_le ( div_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ ) );
    -- The sum over relevant primes is bounded by the sum over all primes $p \le \sqrt{2x}$ by definition of `relevant_primes`.
    have h_relevant_primes_le_all_primes : ∀ x : ℝ, ∑ p ∈ relevant_primes P x, (p : ℝ) / (Real.log (Real.log p))^2 ≤ ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x)) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (p : ℝ) / (Real.log (Real.log p))^2 := by
      intros x
      simp [relevant_primes];
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ );
      simp +contextual [ Finset.subset_iff ];
      exact fun p hp₁ hp₂ hp₃ => Nat.floor_le ( by positivity ) |> le_trans ( mod_cast Nat.le_of_lt_succ hp₁ );
    -- By `error_term_small`, this larger sum is $o(x)$.
    have h_error_term_small : (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ Real.sqrt (2 * x)) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (p : ℝ) / (Real.log (Real.log p))^2) =o[Filter.atTop] (fun x => x) := by
      convert error_term_small assumps using 1;
    rw [ Asymptotics.isLittleO_iff ] at *;
    intro c hc; filter_upwards [ h_error_term_small hc, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂; rw [ Real.norm_of_nonneg ( show 0 ≤ sum_S2 P x from Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ] ; exact le_trans ( h_sum_S2_le x |> le_trans <| h_relevant_primes_le_all_primes x ) ( le_trans ( le_abs_self _ ) hx₁ ) ;

/-
Bound on the total number of bad n.
-/
def bad_n_total (P : ℕ) (x : ℝ) (W : ℕ) : Finset ℕ :=
  (relevant_pairs P x).biUnion (fun ⟨p, a⟩ => bad_n_for_pair x W p a)

lemma bad_n_card_bound (P : ℕ) (x : ℝ) (W : ℕ) (hW : W > 0)
    (h_coprime : ∀ p ∈ relevant_primes P x, Nat.Coprime W (p^2)) :
  (bad_n_total P x W).card ≤ (L_x x : ℝ) / W * (sum_S1 P x) + 2 * (sum_S2 P x) := by
    -- The cardinality of the union is at most the sum of cardinalities.
    have h_union_card : ((bad_n_total P x W).card : ℝ) ≤ ∑ p ∈ (relevant_primes P x), ∑ a ∈ (Finset.Icc 1 (a_bound p)), ((bad_n_for_pair x W p a).card : ℝ) := by
      refine' mod_cast le_trans ( Finset.card_biUnion_le ) _;
      erw [ Finset.sum_biUnion ];
      · exact Finset.sum_le_sum fun p hp => by rw [ Finset.sum_image ] ; aesop;
      · exact fun p hp q hq hpq => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hpq <| by aesop;
    -- Using `bad_n_for_pair_bound`, each term is $\le L_x / (W p^2) + 2$.
    have h_term_bound : ∀ p ∈ relevant_primes P x, ∀ a ∈ Finset.Icc 1 (a_bound p), ((bad_n_for_pair x W p a).card : ℝ) ≤ (L_x x : ℝ) / (W * p^2) + 2 := by
      intros p hp a ha
      apply bad_n_for_pair_bound x W p a hW (by
      exact Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2.1 )) (by
      exact h_coprime p hp);
    convert h_union_card.trans ( Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun a ha => h_term_bound p hp a ha ) using 1 ; norm_num [ div_eq_mul_inv, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ] ; ring_nf!;
    unfold sum_S1 sum_S2; simp +decide [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      Finset.mul_sum _ _ _] ;

/-
The lower density of a set A of natural numbers.
-/
def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

/-
For sufficiently large P, and sufficiently large x (depending on P), the number of bad n is strictly less than the number of multiples of W_P in the interval.
-/
lemma large_P_bound_satisfied (assumps : SieveAssumptions) :
    ∃ P₀, ∀ P ≥ P₀, ∃ x₀, ∀ x ≥ x₀, (bad_n_total P x (W_P P)).card < (S_x x (W_P P)).card := by
      -- By Lemma~\ref{lem:tail_sum_bound}, we can find $P$ large enough such that the tail value (and thus sum_S1) is less than 0.5.
      obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ, ∀ P ≥ P₀, tail_val P < 0.5 := by
        have h_tail_zero : Filter.Tendsto tail_val Filter.atTop (nhds 0) := by
          convert tail_sum_bound assumps;
        simpa using h_tail_zero.eventually ( gt_mem_nhds <| by norm_num );
      -- By Lemma~\ref{lem:sum_S2_is_littleO}, the term $2 * sum_S2$ is $o(x)$, while $L_x x / W$ is proportional to $x$. So $2 * sum_S2 / (L_x x / W)$ tends to 0.
      have h_term_zero : ∀ P ≥ P₀, Filter.Tendsto (fun x => 2 * sum_S2 P x / ((L_x x : ℝ) / W_P P)) Filter.atTop (nhds 0) := by
        intro P hP
        have h_term_zero : Filter.Tendsto (fun x => sum_S2 P x / x) Filter.atTop (nhds 0) := by
          have := sum_S2_is_littleO P assumps; exact this.tendsto_div_nhds_zero;
        have h_term_zero : Filter.Tendsto (fun x => (L_x x : ℝ) / x) Filter.atTop (nhds 0.5) := by
          have h_floor_ceil : ∀ x : ℝ, x ≥ 2 → (Nat.floor x : ℝ) - Nat.ceil (x / 2) + 1 ≥ x / 2 - 2 ∧ (Nat.floor x : ℝ) - Nat.ceil (x / 2) + 1 ≤ x / 2 + 2 := by
            intro x hx; constructor <;> linarith [ Nat.floor_le ( show 0 ≤ x by linarith ), Nat.lt_floor_add_one x, Nat.le_ceil ( x / 2 ), Nat.ceil_lt_add_one ( show 0 ≤ x / 2 by linarith ) ] ;
          rw [ Metric.tendsto_nhds ];
          intro ε hε; filter_upwards [ Filter.eventually_ge_atTop 2, Filter.eventually_gt_atTop ( 4 / ε ) ] with x hx₁ hx₂; rw [ dist_eq_norm ] ; norm_num [ L_x ];
          rw [ Nat.cast_sub ( show ⌈x / 2⌉₊ ≤ ⌊x⌋₊ from Nat.ceil_le.mpr <| by linarith [ Nat.lt_floor_add_one x ] ) ] ; rw [ abs_lt ] ; constructor <;> nlinarith [ h_floor_ceil x hx₁, mul_div_cancel₀ ( ( ⌊x⌋₊ - ⌈x / 2⌉₊ : ℝ ) + 1 ) ( by linarith : x ≠ 0 ), mul_div_cancel₀ ( 4 : ℝ ) hε.ne' ];
        have h_term_zero : Filter.Tendsto (fun x => 2 * sum_S2 P x / x * (x / (L_x x : ℝ)) * (W_P P : ℝ)) Filter.atTop (nhds 0) := by
          have h_term_zero : Filter.Tendsto (fun x => 2 * sum_S2 P x / x * (x / (L_x x : ℝ))) Filter.atTop (nhds 0) := by
            convert Filter.Tendsto.mul ( ‹Filter.Tendsto ( fun x : ℝ => sum_S2 P x / x ) Filter.atTop ( nhds 0 ) ›.const_mul 2 ) ( h_term_zero.inv₀ <| by norm_num ) using 2 <;> ring_nf ; norm_num;
            ring;
          simpa using h_term_zero.mul_const _;
        refine h_term_zero.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hx.ne' ] );
      -- By combining the results from h_term_zero and h_bad_n_card_bound, we can find such an x₀.
      have h_combined : ∀ P ≥ P₀, ∃ x₀ : ℝ, ∀ x ≥ x₀, (L_x x : ℝ) / W_P P * (tail_val P) + 2 * sum_S2 P x < (L_x x : ℝ) / W_P P - 2 := by
        intro P hP
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, 2 * sum_S2 P x / ((L_x x : ℝ) / W_P P) < 1 / 4 := by
          exact Filter.eventually_atTop.mp ( h_term_zero P hP |> fun h => h.eventually ( gt_mem_nhds <| by norm_num ) );
        -- Choose x₀ such that for all x ≥ x₀, (L_x x : ℝ) / W_P P > 8.
        obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, ∀ x ≥ x₁, (L_x x : ℝ) / W_P P > 8 := by
          have hL_x_growth : Filter.Tendsto (fun x => (L_x x : ℝ)) Filter.atTop Filter.atTop := by
            refine' tendsto_natCast_atTop_atTop.comp _;
            refine' Filter.tendsto_atTop_atTop.mpr _;
            intro b; use 2 * b + 2; intro a ha; unfold L_x;
            exact Nat.le_succ_of_le ( Nat.le_sub_of_add_le <| Nat.le_floor <| by norm_num; linarith [ Nat.ceil_lt_add_one <| show 0 ≤ a / 2 by linarith ] );
          exact Filter.eventually_atTop.mp ( hL_x_growth.eventually_gt_atTop ( 8 * W_P P ) ) |> fun ⟨ x₁, hx₁ ⟩ ↦ ⟨ x₁, fun x hx ↦ by rw [ gt_iff_lt ] ; rw [ lt_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| Finset.prod_ne_zero_iff.mpr fun p hp ↦ pow_ne_zero 2 <| Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ) ] ; linarith [ hx₁ x hx ] ⟩;
        exact ⟨ Max.max x₀ x₁, fun x hx => by have := hx₀ x ( le_trans ( le_max_left _ _ ) hx ) ; have := hx₁ x ( le_trans ( le_max_right _ _ ) hx ) ; rw [ div_lt_iff₀ ] at * <;> nlinarith [ hP₀ P hP ] ⟩;
      use P₀;
      intros P hP
      obtain ⟨x₀, hx₀⟩ := h_combined P hP
      use x₀ + 2;
      intro x hx
      have h_card_bound : (bad_n_total P x (W_P P)).card ≤ (L_x x : ℝ) / W_P P * sum_S1 P x + 2 * sum_S2 P x := by
        apply_rules [ bad_n_card_bound ];
        · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2;
        · intros p hp
          have h_coprime : Nat.Coprime (∏ p ∈ Finset.filter Nat.Prime (Finset.range (P + 1)), p^2) (p^2) := by
            simp +zetaDelta at *;
            exact Nat.Coprime.prod_left fun q hq => Nat.Coprime.pow_left 2 <| Nat.coprime_comm.mp <| Nat.Prime.coprime_iff_not_dvd ( Finset.mem_filter.mp hp |>.2.1 ) |>.2 fun h => by have := Nat.le_of_dvd ( Nat.pos_of_ne_zero <| by aesop ) h; linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hq |>.1 ), Finset.mem_filter.mp hp |>.2.2 ] ;
          exact h_coprime
      have h_card_S_x : (S_x x (W_P P)).card ≥ (L_x x : ℝ) / W_P P - 2 := by
        have := card_S_x_bound x ( W_P P ) ?_ <;> norm_num at *;
        · linarith [ abs_le.mp this ];
        · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2
      have h_final : (bad_n_total P x (W_P P)).card < (S_x x (W_P P)).card := by
        have h_final : (L_x x : ℝ) / W_P P * sum_S1 P x + 2 * sum_S2 P x < (L_x x : ℝ) / W_P P - 2 := by
          exact lt_of_le_of_lt ( add_le_add ( mul_le_mul_of_nonneg_left ( sum_S1_le_tail P x assumps ) ( by positivity ) ) le_rfl ) ( hx₀ x ( by linarith ) );
        exact_mod_cast h_card_bound.trans_lt ( h_final.trans_le h_card_S_x )
      exact h_final

/-
For $p \ge 20$, if $a \le p / (\log \log p)^2$, then $a < p$.
-/
lemma a_lt_p (p : ℕ) (a : ℕ) (hp : p ≥ 20) (ha_bound : (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2) : a < p := by
  -- Since $p \geq 20$, we have $\log \log p > 1$, thus $(\log \log p)^2 > 1$.
  have h_log_log_p_gt_1 : 1 < (Real.log (Real.log p)) := by
    rw [ Real.lt_log_iff_exp_lt ( Real.log_pos <| by norm_cast; linarith ) ];
    rw [ Real.lt_log_iff_exp_lt ] <;> norm_num <;> try linarith;
    have := Real.exp_one_lt_d9.le;
    -- We'll use that $e^e < 16$ to conclude the proof.
    have h_exp_exp_lt_16 : Real.exp (Real.exp 1) < 16 := by
      rw [ ← Real.log_lt_log_iff ( by positivity ) ] <;> norm_num;
      rw [ show ( 16 : ℝ ) = ( 2 ^ 4 ) by norm_num, Real.log_pow ] ; norm_num;
      exact lt_of_le_of_lt this ( by have := Real.log_two_gt_d9; norm_num1 at *; linarith );
    exact h_exp_exp_lt_16.trans_le ( mod_cast by linarith );
  exact_mod_cast ( by rw [ le_div_iff₀ ( by positivity ) ] at ha_bound; nlinarith [ show ( p :ℝ ) ≥ 20 by norm_cast, show ( Real.log ( Real.log p ) ^ 2 :ℝ ) > 1 by exact one_lt_pow₀ h_log_log_p_gt_1 ( by norm_num ) ] : ( a :ℝ ) < p )

/-
If $p \le \sqrt{2x}$ and the bad condition holds, then $n$ is in `bad_n_total`.
-/
lemma bad_implies_mem_bad_n_total_of_le_sqrt
  (n : ℕ) (x : ℝ) (P : ℕ) (hn : n ∈ S_x x (W_P P)) (p : ℕ) (hp_prime : Nat.Prime p) (hp_gt : p > P) (hp_le : (p : ℝ) ≤ Real.sqrt (2 * x))
  (a : ℕ) (ha_pos : 1 ≤ a) (ha_bound : (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2) (h_div : (n + a) % p^2 = 0) :
  n ∈ bad_n_total P x (W_P P) := by

  -- Extract 0 ≤ 2 * x from hp_le
  have hx2 : 0 ≤ 2 * x := by
    by_contra hneg
    have hneg' : 2 * x ≤ 0 := le_of_lt (lt_of_not_ge hneg)
    have hsqrt : Real.sqrt (2 * x) = 0 :=
      Real.sqrt_eq_zero_of_nonpos hneg'
    have hp_pos : (0 : ℝ) < p := by
      exact_mod_cast hp_prime.pos
    have : (p : ℝ) ≤ 0 := by
      simpa [hsqrt] using hp_le
    exact (not_le_of_gt hp_pos) this

  exact Finset.mem_biUnion.mpr
    ⟨ (p, a),
      Finset.mem_biUnion.mpr
        ⟨ p,
          Finset.mem_filter.mpr
            ⟨ Finset.mem_range.mpr
                (Nat.lt_succ_of_le
                  (Nat.le_floor <|
                    by
                      nlinarith [Real.mul_self_sqrt hx2])),
              hp_prime,
              hp_gt ⟩,
          Finset.mem_image.mpr
            ⟨ a,
              Finset.mem_Icc.mpr ⟨ ha_pos, Nat.le_floor ha_bound ⟩,
              rfl ⟩ ⟩,
      by
        unfold bad_n_for_pair
        aesop ⟩

/-
If n is in S_x, it satisfies condition (a).
-/
lemma lemma_condition_a_of_mem_Sx (P : ℕ) (x : ℝ) (n : ℕ)
    (hn_mem : n ∈ S_x x (W_P P)) :
    (∀ p, Nat.Prime p → p ≤ P → n % p^2 = 0) := by
      intro p pp pP; exact Nat.mod_eq_zero_of_dvd ( dvd_trans ( by exact Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), pp ⟩ ) |> fun h => dvd_trans ( by norm_num ) h ) ( Nat.dvd_of_mod_eq_zero <| Finset.mem_filter.mp hn_mem |>.2 ) ) ;

/-
If n is not in bad_n_total, then for small p, condition (b) holds.
-/
lemma lemma_condition_b_small_p (P : ℕ) (x : ℝ) (n : ℕ)
    (hn_mem : n ∈ S_x x (W_P P))
    (hn_not_bad : n ∉ bad_n_total P x (W_P P)) :
    (∀ p, Nat.Prime p → p > P → (p : ℝ) ≤ Real.sqrt (2 * x) →
     ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0) := by
  intros p hp_prime hp_gt hp_le a ha_pos ha_bound h_div
  apply hn_not_bad
  apply bad_implies_mem_bad_n_total_of_le_sqrt n x P hn_mem p hp_prime hp_gt hp_le a ha_pos ha_bound h_div

/-
If n is in S_x and x is large enough, then for large p, condition (b) holds.
-/
lemma lemma_condition_b_large_p (P : ℕ) (x : ℝ) (n : ℕ)
    (hx : x ≥ 200)
    (hn_mem : n ∈ S_x x (W_P P)) :
    (∀ p, Nat.Prime p → p > P → (p : ℝ) > Real.sqrt (2 * x) →
     ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0) := by
       intros p hp_prime hp_gt hp_gt_sqrt a ha_pos ha_bound
       have h_n_lt_x : n < p^2 := by
         have h_n_lt_x : n ≤ x := by
           exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn_mem |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
         exact_mod_cast ( by nlinarith [ Real.sqrt_nonneg ( 2 * x ), Real.mul_self_sqrt ( show 0 ≤ 2 * x by positivity ) ] : ( n : ℝ ) < p ^ 2 )
       have h_a_lt_p : a < p := by
         by_cases hp : p ≥ 20;
         · exact a_lt_p p a hp ha_bound;
         · interval_cases p <;> norm_num at *;
           all_goals rw [ ← Real.sqrt_mul <| by positivity ] at hp_gt_sqrt; rw [ Real.sqrt_lt' <| by positivity ] at hp_gt_sqrt; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
       have h_n_a_lt_p_sq : n + a < p^2 := by
         have h_n_a_lt_p_sq : n ≤ x := by
           exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn_mem |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
         exact_mod_cast ( by nlinarith [ Real.sqrt_nonneg ( 2 * x ), Real.mul_self_sqrt ( show 0 ≤ 2 * x by positivity ), show ( p : ℝ ) ≥ a + 1 by norm_cast ] : ( n : ℝ ) + a < p ^ 2 )
       exact (by
       rw [ Nat.mod_eq_of_lt ] <;> linarith [ show n + a > 0 from by linarith ])

/-
If the number of bad n is less than the size of S_x, then there exists a good n satisfying conditions (a) and (b).
-/
lemma lemma_exists_good_n_if_card_lt (P : ℕ) (x : ℝ) (hx : x ≥ 200)
    (h_card : (bad_n_total P x (W_P P)).card < (S_x x (W_P P)).card) :
    ∃ n ∈ S_x x (W_P P),
    (∀ p, Nat.Prime p → p ≤ P → n % p^2 = 0) ∧
    (∀ p, Nat.Prime p → p > P → ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0) := by
  have h_exists : ∃ n, n ∈ S_x x (W_P P) ∧ n ∉ bad_n_total P x (W_P P) := by
    by_contra h
    push_neg at h
    have h_subset : S_x x (W_P P) ⊆ bad_n_total P x (W_P P) := fun n hn => h n hn
    have h_le : (S_x x (W_P P)).card ≤ (bad_n_total P x (W_P P)).card := Finset.card_le_card h_subset
    linarith
  obtain ⟨n, hn_mem, hn_not_bad⟩ := h_exists
  use n
  constructor
  · exact hn_mem
  · constructor
    · apply lemma_condition_a_of_mem_Sx; assumption
    · intros p hp hp_gt a ha_pos ha_bound
      by_cases hp_le : (p : ℝ) ≤ Real.sqrt (2 * x)
      · apply lemma_condition_b_small_p P x n hn_mem hn_not_bad p hp hp_gt hp_le a ha_pos ha_bound
      · apply lemma_condition_b_large_p P x n hx hn_mem p hp hp_gt (lt_of_not_ge hp_le) a ha_pos ha_bound

/-
For any sufficiently large $P \ge 3$, there exist arbitrarily large natural numbers $n$ such that
(a) $n \equiv 0 \pmod{p^2}$ whenever $p \leq P$; and
(b) $n + a \not \equiv 0 \pmod{p^2}$ whenever $p>P$ and $1 \leq a \leq \frac{p}{(\log\log p)^2}$.
-/
lemma lemma_largeP (assumps : SieveAssumptions) :
    ∃ P₀ ≥ 3, ∀ P ≥ P₀, ∀ M : ℕ, ∃ n ≥ M,
    (∀ p, Nat.Prime p → p ≤ P → n % p^2 = 0) ∧
    (∀ p, Nat.Prime p → p > P → ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0) := by
      obtain ⟨ P₀, hP₀ ⟩ := large_P_bound_satisfied assumps;
      refine' ⟨ P₀ + 3, by linarith, fun P hP M => _ ⟩;
      obtain ⟨ x₀, hx₀ ⟩ := hP₀ P ( by linarith );
      -- Choose $x$ large enough such that $x \geq \max(x₀, \max(200, 2M))$.
      obtain ⟨ x, hx₁, hx₂ ⟩ : ∃ x : ℝ, x ≥ x₀ ∧ x ≥ 200 ∧ x ≥ 2 * M := by
        exact ⟨ Max.max x₀ ( Max.max 200 ( 2 * M ) ), le_max_left _ _, le_max_of_le_right ( le_max_left _ _ ), le_max_of_le_right ( le_max_right _ _ ) ⟩;
      obtain ⟨ n, hn₁, hn₂, hn₃ ⟩ := lemma_exists_good_n_if_card_lt P x hx₂.1 ( hx₀ x hx₁ );
      exact ⟨ n, Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.ceil_le.mp <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hn₁ |>.1 ) |>.1 ] }, hn₂, hn₃ ⟩

/-
There exists a strictly increasing sequence n_j satisfying the conditions (a) and (b) with respect to P_seq K j.
-/
def P_seq (K j : ℕ) : ℕ := Nat.floor ((K : ℝ) * Real.exp (Real.exp j))

/-
The set A defined by the sequence n has property P_bar.
-/
def A_seq (n : ℕ → ℕ) : Set ℕ := { a | ∀ j, Squarefree (n j + a) }

lemma PropertyP_bar_A_seq (n : ℕ → ℕ) (h_mono : StrictMono n) : PropertyP_bar (A_seq n) := by
  refine Set.infinite_of_forall_exists_gt ?_;
  intro a; have := h_mono.id_le ( a + 1 ) ; aesop;

/-
If p > P_seq K j, then j < log log p.
-/
lemma P_seq_growth (K j : ℕ) (hK : K ≥ 3) (p : ℕ) (hp : p > P_seq K j) :
    (j : ℝ) < Real.log (Real.log p) := by
      -- Since $p > P_seq K j$, we have $p > K \exp(\exp(j))$.
      have hp_gt_exp_exp_j : (p : ℝ) > (K : ℝ) * Real.exp (Real.exp j) := by
        contrapose! hp;
        exact Nat.le_floor <| mod_cast hp;
      -- Since $p > K \exp(\exp(j))$, we have $\log p > \log (K \exp(\exp(j))) = \log K + \exp(j)$.
      have h_log_p : Real.log p > Real.log K + Real.exp j := by
        simpa [ Real.log_mul ( by positivity : ( K : ℝ ) ≠ 0 ) ( by positivity : Real.exp ( Real.exp j ) ≠ 0 ) ] using Real.log_lt_log ( by positivity ) hp_gt_exp_exp_j;
      rw [ Real.lt_log_iff_exp_lt ];
      · linarith [ Real.log_nonneg ( show ( K : ℝ ) ≥ 1 by norm_cast; linarith ) ];
      · exact lt_of_le_of_lt ( add_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ( Real.exp_nonneg _ ) ) h_log_p

/-
For any sufficiently large $P \ge 3$, there exist arbitrarily large natural numbers $n$ such that
(a) $n \equiv 0 \pmod{p^2}$ whenever $p \leq P$; and
(b) $n + a \not \equiv 0 \pmod{p^2}$ whenever $p>P$ and $1 \leq a \leq \frac{p}{(\log\log p)^2}$.
-/
lemma lemma_largeP_v2 (assumps : SieveAssumptions) :
    ∃ P₀ ≥ 3, ∀ P ≥ P₀, ∀ M : ℕ, ∃ n ≥ M,
    (∀ p, Nat.Prime p → p ≤ P → n % p^2 = 0) ∧
    (∀ p, Nat.Prime p → p > P → ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0) := by
      apply_rules [ lemma_largeP ]

/-
If a <= x and a > p / (log log p)^2, then p <= 4 x (log log x)^2.
-/
def p_upper_bound (x : ℝ) : ℝ := 4 * x * (Real.log (Real.log x))^2

lemma p_bound_lemma_v2 (x : ℝ) (hx : x ≥ 100) (p : ℕ) (a : ℕ) (ha : a ≤ x)
    (h_ineq : (a : ℝ) > (p : ℝ) / (Real.log (Real.log p))^2) :
    (p : ℝ) ≤ p_upper_bound x := by
      unfold p_upper_bound;
      -- Assume $f(Y) > x$.
      have h_fY_gt_x : (4 * x * (Real.log (Real.log x))^2 : ℝ) / (Real.log (Real.log (4 * x * (Real.log (Real.log x))^2)))^2 > x := by
        -- We'll use that $Real.log (Real.log (4 * x * (Real.log (Real.log x))^2)) \leq Real.log (Real.log x) + Real.log 4$.
        have h_log_bound : Real.log (Real.log (4 * x * (Real.log (Real.log x))^2)) ≤ Real.log (Real.log x) + Real.log 4 := by
          rw [ ← Real.log_mul ( by exact ne_of_gt <| Real.log_pos <| by linarith ) ( by positivity ) ];
          gcongr;
          · refine' Real.log_pos _;
            -- Since $x \geq 100$, we have $\log x \geq \log 100 = 2 \log 10$. Therefore, $\log (\log x) \geq \log (2 \log 10)$.
            have h_log_log_x_ge_log_2_log_10 : Real.log (Real.log x) ≥ Real.log (2 * Real.log 10) := by
              exact Real.log_le_log ( by positivity ) ( by rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_num <;> linarith );
            have h_log_log_x_sq_gt_1 : Real.log (2 * Real.log 10) > 1 := by
              rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ];
              · exact lt_of_le_of_lt ( Real.exp_one_lt_d9.le ) ( by have := Real.log_two_gt_d9; norm_num1 at *; rw [ show ( 10 : ℝ ) = 2 * 5 by norm_num, Real.log_mul ] <;> norm_num ; have := Real.log_lt_log ( by norm_num ) ( by norm_num : ( 5 : ℝ ) > 2 ) ; norm_num at * ; linarith );
              · positivity;
            nlinarith;
          · rw [ Real.log_le_iff_le_exp ( by exact mul_pos ( by positivity ) ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) ) ) ) ];
            rw [ Real.exp_mul, Real.exp_log ( by positivity ) ];
            -- We'll use that $Real.log (Real.log x) \leq Real.log x$ for $x \geq 100$.
            have h_log_bound : Real.log (Real.log x) ≤ Real.log x := by
              exact le_trans ( Real.log_le_sub_one_of_pos ( Real.log_pos ( by linarith ) ) ) ( by linarith );
            -- We'll use that $Real.log x \leq x^{1/2}$ for $x \geq 100$.
            have h_log_sqrt : Real.log x ≤ x^(1/2 : ℝ) := by
              rw [ ← Real.sqrt_eq_rpow ];
              have := Real.log_le_sub_one_of_pos ( by positivity : 0 < Real.sqrt x / 2 );
              rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] at this;
              have := Real.log_two_lt_d9 ; norm_num at * ; linarith;
            refine le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Real.log_nonneg <| show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith ) h_log_bound 2 ) <| by positivity ) ?_;
            refine le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Real.log_nonneg <| by linarith ) h_log_sqrt 2 ) <| by positivity ) ?_ ; ring_nf ; norm_num;
            rw [ ← Real.sqrt_eq_rpow, Real.sq_sqrt ] <;> nlinarith [ pow_le_pow_left₀ ( by positivity ) hx 3 ];
        -- Substitute the bound into the inequality.
        have h_subst : 4 * x * (Real.log (Real.log x))^2 / (Real.log (Real.log x) + Real.log 4)^2 > x := by
          -- We'll use that $Real.log (Real.log x) > Real.log 4$ for $x \geq 100$.
          have h_log_log_x_gt_log_4 : Real.log (Real.log x) > Real.log 4 := by
            gcongr;
            rw [ Real.lt_log_iff_exp_lt ( by positivity ) ];
            have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this 4 ) ( by norm_num; linarith );
          rw [ gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ show 0 < x by positivity, show 0 < Real.log ( Real.log x ) by exact Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith, show 0 < Real.log 4 by positivity, mul_lt_mul_of_pos_left h_log_log_x_gt_log_4 <| show 0 < x by positivity ];
        refine lt_of_lt_of_le h_subst ?_;
        gcongr;
        · refine' sq_pos_of_pos ( Real.log_pos _ );
          rw [ Real.lt_log_iff_exp_lt ];
          · -- Since $x \geq 100$, we have $\log x \geq \log 100 = 2 \log 10 \approx 4.605$.
            have h_log_x : Real.log x ≥ 4 := by
              rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ];
              exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this 4 ) ( by norm_num ) ) hx;
            exact lt_of_lt_of_le ( Real.exp_one_lt_d9.trans_le ( by norm_num ) ) ( mul_le_mul ( mul_le_mul_of_nonneg_left hx ( by norm_num ) ) ( pow_le_pow_left₀ ( by positivity ) ( show Real.log ( Real.log x ) ≥ 1 by rw [ ge_iff_le ] ; rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) 2 ) ( by positivity ) ( by positivity ) );
          · exact mul_pos ( by positivity ) ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) ) );
        · refine' Real.log_nonneg _;
          rw [ Real.le_log_iff_exp_le ( by exact mul_pos ( by positivity ) ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) ) ) ) ];
          have h_exp_log : Real.log (Real.log x) ≥ 1 / 2 := by
            have h_log_bound : Real.log x ≥ 4 := by
              rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ];
              exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this 4 ) ( by norm_num ) ) hx;
            exact le_trans ( Real.log_two_gt_d9.le.trans' <| by norm_num ) ( Real.log_le_log ( by norm_num ) <| show Real.log x ≥ 2 by linarith );
          have := Real.exp_one_lt_d9.le ; norm_num at * ; nlinarith [ Real.add_one_le_exp 1 ];
      -- If $p > Y$, then $f(p) \ge f(Y) > x$, since $f(t)$ is increasing for $t \ge 100$.
      have h_f_p_ge_f_Y : ∀ t₁ t₂ : ℝ, 100 ≤ t₁ → t₁ ≤ t₂ → (t₁ / (Real.log (Real.log t₁))^2 : ℝ) ≤ (t₂ / (Real.log (Real.log t₂))^2 : ℝ) := by
        -- To show that $f(t)$ is increasing for $t \geq 100$, we can compute its derivative and show that it is positive.
        have h_deriv_pos : ∀ t : ℝ, 100 ≤ t → deriv (fun t => t / (Real.log (Real.log t))^2) t > 0 := by
          intro t ht;
          have h_deriv_pos : deriv (fun t => t / (Real.log (Real.log t))^2) t = (1 / (Real.log (Real.log t))^2) * (1 - 2 / (Real.log t * Real.log (Real.log t))) := by
            norm_num [ show t ≠ 0 by linarith, show Real.log t ≠ 0 by exact ne_of_gt <| Real.log_pos <| by linarith, show Real.log ( Real.log t ) ≠ 0 by exact ne_of_gt <| Real.log_pos <| show 1 < Real.log t by rw [ Real.lt_log_iff_exp_lt <| by linarith ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith ] ; ring_nf;
            field_simp;
          refine' h_deriv_pos.symm ▸ mul_pos ( one_div_pos.mpr ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log t from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) ) ) ) ( sub_pos.mpr _ );
          rw [ div_lt_iff₀ ] <;> norm_num;
          · have h_log_log_t : Real.log t > 4 := by
              rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ( by positivity ) ];
              have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this 4 ) ( by norm_num; linarith );
            nlinarith [ show 1 < Real.log ( Real.log t ) from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ];
          · exact mul_pos ( Real.log_pos ( by linarith ) ) ( Real.log_pos ( show 1 < Real.log t from by rw [ Real.lt_log_iff_exp_lt ( by linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) ) );
        intros t₁ t₂ ht₁ ht₂; by_contra h_contra; push_neg at h_contra;
        have := exists_deriv_eq_slope ( fun t => t / Real.log ( Real.log t ) ^ 2 ) ( show t₁ < t₂ from ht₂.lt_of_ne ( by rintro rfl; linarith ) ) ; norm_num at this;
        exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun t ht => DifferentiableAt.continuousAt <| by exact differentiableAt_of_deriv_ne_zero <| ne_of_gt <| h_deriv_pos t <| by linarith [ ht.1 ] ) ( by exact fun t ht => DifferentiableAt.differentiableWithinAt <| by exact differentiableAt_of_deriv_ne_zero <| ne_of_gt <| h_deriv_pos t <| by linarith [ ht.1 ] ) ) ( by rintro ⟨ c, ⟨ h₁, h₂ ⟩, h₃ ⟩ ; rw [ eq_div_iff ] at h₃ <;> nlinarith [ h_deriv_pos c <| by linarith ] );
      contrapose! h_ineq;
      refine le_trans ?_ ( h_f_p_ge_f_Y _ _ ?_ h_ineq.le );
      · linarith;
      · -- Since $x \geq 100$, we have $\log x \geq \log 100 = 2 \log 10$.
        have h_log_x_ge_2_log_10 : Real.log x ≥ 2 * Real.log 10 := by
          rw [ ← Real.log_rpow, ge_iff_le, Real.log_le_log_iff ] <;> norm_num <;> linarith;
        -- Since $\log 10 \approx 2.3026$, we have $2 \log 10 \approx 4.6052$.
        have h_log_10_approx : Real.log 10 > 2 := by
          norm_num [ Real.lt_log_iff_exp_lt ];
          have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show ( 2 : ℝ ) = 1 + 1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ];
        nlinarith [ show 1 ≤ Real.log ( Real.log x ) from by rw [ Real.le_log_iff_exp_le ( Real.log_pos <| by linarith ) ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith ]

/-
The number of indices j such that P_j < p is at most log log p + 1.
-/
def relevant_indices (K p : ℕ) : Finset ℕ :=
  (Finset.range p).filter (fun j => P_seq K j < p)

lemma card_relevant_indices_bound (K p : ℕ) (hK : K ≥ 3) (hp : p > K) :
    (relevant_indices K p).card ≤ Real.log (Real.log p) + 1 := by
      -- The set of relevant indices is a subset of {0, 1, ..., ⌊log log p⌋}.
      have h_subset : relevant_indices K p ⊆ Finset.range (Nat.floor (Real.log (Real.log p)) + 1) := by
        intro j hj;
        have := P_seq_growth K j hK p ( Finset.mem_filter.mp hj |>.2 );
        exact Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_floor this.le ) );
      exact le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_subset ) <| by norm_num; linarith [ Nat.floor_le <| Real.log_nonneg <| show 1 ≤ Real.log p from by rw [ Real.le_log_iff_exp_le <| by norm_cast; linarith ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( p : ℝ ) ≥ 3 by norm_cast; linarith ] ] ;

/-
Definitions for the subset of [1, x] removed from A, and the bound on its size.
-/
def removed_subset (n : ℕ → ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun a => Squarefree a ∧ ∃ j, ¬ Squarefree (n j + a))

def bound_sum_term (x : ℝ) (p : ℕ) : ℝ := (Real.log (Real.log p) + 1) * (x / p^2 + 1)

def total_removed_bound (K : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ K < p ∧ (p : ℝ) ≤ p_upper_bound x) (Finset.range (Nat.floor (p_upper_bound x) + 1)), bound_sum_term x p

/-
The removed subset is contained in the union of bad_a_for_p over relevant primes.
-/
def relevant_primes_for_bound (K : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor (p_upper_bound x) + 1)).filter (fun p => Nat.Prime p ∧ p > K)

def bad_a_for_p (n : ℕ → ℕ) (K : ℕ) (x : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun a => ∃ j, P_seq K j < p ∧ (n j + a) % p^2 = 0)

/-
The number of bad a for a given p is bounded by the term in the sum.
-/
lemma card_bad_a_for_p_le (n : ℕ → ℕ) (K : ℕ) (x : ℝ) (p : ℕ) (hK : K ≥ 3) (hp : p > K) (hx : x ≥ 0) :
  (bad_a_for_p n K x p).card ≤ bound_sum_term x p := by
    -- The set `bad_a_for_p` consists of $a \in [1, \lfloor x \rfloor]$ such that $a \pmod{p^2}$ belongs to the set of residues $R = \{ (-n_j) \pmod{p^2} \mid P_j < p \}$.
    set R := Finset.image (fun j => (-n j : ZMod (p^2))) (Finset.filter (fun j => P_seq K j < p) (Finset.range p)) with hR_def
    have hR_card : R.card ≤ Real.log (Real.log p) + 1 := by
      refine' le_trans ( Nat.cast_le.mpr <| Finset.card_image_le ) _;
      convert card_relevant_indices_bound K p hK hp using 1;
    -- For each residue $r \in R$, the number of $a \in [1, \lfloor x \rfloor]$ with $a \equiv r \pmod{p^2}$ is at most $\lfloor x \rfloor / p^2 + 1 \le x/p^2 + 1$.
    have h_residue_count : ∀ r ∈ R, ((Finset.Icc 1 (Nat.floor x)).filter (fun a => a ≡ r.val [MOD p^2])).card ≤ x / p^2 + 1 := by
      intros r hr
      have h_residue_count : ((Finset.Icc 1 (Nat.floor x)).filter (fun a => a ≡ r.val [MOD p^2])).card ≤ (Nat.floor x) / p^2 + 1 := by
        -- The set of integers in [1, floor(x)] that are congruent to r modulo p^2 is contained in the set {r + kp^2 | k = 0, 1, ..., floor(x)/p^2}.
        have h_subset : Finset.filter (fun a => a ≡ r.val [MOD p^2]) (Finset.Icc 1 (Nat.floor x)) ⊆ Finset.image (fun k => r.val + k * p^2) (Finset.range (Nat.floor x / p^2 + 1)) := by
          intro a ha; simp_all +decide [ Nat.ModEq ] ;
          refine' ⟨ a / p ^ 2, _, _ ⟩;
          · exact Nat.lt_succ_of_le ( Nat.div_le_div_right ha.1.2 );
          · linarith [ Nat.mod_add_div a ( p ^ 2 ), Nat.mod_eq_of_lt ( show r.val < p ^ 2 from by { haveI := Fact.mk ( show p ^ 2 > 1 from one_lt_pow₀ ( by linarith ) two_ne_zero ) ; exact ZMod.val_lt r } ) ];
        exact le_trans ( Finset.card_le_card h_subset ) ( Finset.card_image_le.trans ( by norm_num ) );
      refine le_trans ( Nat.cast_le.mpr h_residue_count ) ?_;
      norm_num +zetaDelta at *;
      rw [ le_div_iff₀ ( by norm_cast; nlinarith ) ] ; exact le_trans ( mod_cast Nat.div_mul_le_self _ _ ) ( Nat.floor_le hx );
    -- The set `bad_a_for_p` is a subset of the union of the sets of $a$ for each residue $r \in R$.
    have h_bad_subset_union : bad_a_for_p n K x p ⊆ Finset.biUnion R (fun r => (Finset.Icc 1 (Nat.floor x)).filter (fun a => a ≡ r.val [MOD p^2])) := by
      intro a ha
      obtain ⟨j, hj₁, hj₂⟩ : ∃ j, P_seq K j < p ∧ (n j + a) % p^2 = 0 := by
        unfold bad_a_for_p at ha; aesop;
      have h_residue : a ≡ (-n j : ZMod (p^2)).val [MOD p^2] := by
        simp_all +decide [ ← ZMod.val_natCast, Nat.ModEq ];
        simp_all +decide [ add_eq_zero_iff_eq_neg ]
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_image.mpr ⟨j, by
        simp_all +decide [ P_seq ];
        contrapose! hj₁;
        exact Nat.le_floor <| by nlinarith [ Real.add_one_le_exp j, Real.add_one_le_exp ( Real.exp j ), show ( p : ℝ ) ≤ j by norm_cast, show ( K : ℝ ) ≥ 3 by norm_cast ] ;, rfl⟩, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by
      exact Nat.pos_of_ne_zero fun h => by have := Finset.mem_filter.mp ha; aesop;, by
        exact Finset.mem_filter.mp ha |>.1 |> Finset.mem_Icc.mp |>.2⟩, h_residue⟩⟩;
    refine le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_bad_subset_union ) ?_;
    refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
    push_cast [ bound_sum_term ];
    exact le_trans ( Finset.sum_le_sum h_residue_count ) ( by simpa [ mul_add ] using mul_le_mul_of_nonneg_right hR_card ( by positivity : 0 ≤ x / p ^ 2 + 1 ) )

/-
The total removed bound divided by x splits into two sums.
-/
def sum_part1 (K : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ K < p ∧ (p : ℝ) ≤ p_upper_bound x) (Finset.range (Nat.floor (p_upper_bound x) + 1)), (Real.log (Real.log p) + 1) / p^2

def sum_part2 (K : ℕ) (x : ℝ) : ℝ :=
  (1 / x) * ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ K < p ∧ (p : ℝ) ≤ p_upper_bound x) (Finset.range (Nat.floor (p_upper_bound x) + 1)), (Real.log (Real.log p) + 1)

lemma total_removed_bound_split (K : ℕ) (x : ℝ) (hx : x > 0) :
  total_removed_bound K x / x = sum_part1 K x + sum_part2 K x := by
    unfold total_removed_bound sum_part1 sum_part2;
    rw [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
    rw [ Finset.sum_mul _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; unfold bound_sum_term ; ring_nf;
    simp +decide [ sq, mul_assoc, mul_comm x, hx.ne' ]

/-
Definition of the tail sum of the error term (log log p + 1) / p^2 for p > K.
-/
def tail_sum_loglog_sq (K : ℕ) : ℝ :=
  ∑' p, if p > K ∧ Nat.Prime p then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0

/-
The tail sum of (log log p + 1) / p^2 is summable.
-/
lemma tail_sum_loglog_sq_summable (K : ℕ) :
  Summable (fun p : ℕ => if p > K ∧ Nat.Prime p then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0) := by
    have h_tail_sum_sq_summable : Summable (fun p : ℕ => if Nat.Prime p then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0) := by
      -- We'll use the comparison test. Since \( \frac{\log \log p + 1}{p^2} \leq \frac{2 \log \log p}{p^2} \) for sufficiently large \( p \), and the series \( \sum_{p} \frac{\log \log p}{p^2} \) converges, it follows that \( \sum_{p} \frac{\log \log p + 1}{p^2} \) also converges.
      have h_comparison : Summable (fun p : ℕ => if Nat.Prime p then (Real.log (Real.log p)) / (p : ℝ)^2 else 0) := by
        have h_summable : Summable (fun p : ℕ => (Real.log (Real.log p)) / p^2) := by
          have h_log_log_bound : ∀ p : ℕ, p ≥ 3 → Real.log (Real.log p) ≤ p^(1/2 : ℝ) := by
            intro p hp
            have h_log_log_bound : Real.log (Real.log p) ≤ Real.sqrt p := by
              have := Real.log_le_sub_one_of_pos ( show 0 < Real.sqrt p / Real.exp 1 by positivity );
              rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ), Real.log_exp ] at this ; nlinarith [ Real.add_one_le_exp 1, Real.sqrt_nonneg p, Real.sq_sqrt <| Nat.cast_nonneg p, mul_div_cancel₀ ( Real.sqrt p ) <| ne_of_gt <| Real.exp_pos 1, Real.log_le_sub_one_of_pos <| show 0 < Real.log p from Real.log_pos <| by norm_cast; linarith ];
            rwa [ Real.sqrt_eq_rpow ] at h_log_log_bound
          -- Using the bound $\log \log p \leq p^{1/2}$, we can show that $\frac{\log \log p}{p^2} \leq \frac{p^{1/2}}{p^2} = \frac{1}{p^{3/2}}$.
          have h_bound : ∀ p : ℕ, p ≥ 3 → (Real.log (Real.log p)) / p^2 ≤ 1 / p^(3/2 : ℝ) := by
            intro p hp; convert div_le_div_of_nonneg_right ( h_log_log_bound p hp ) ( sq_nonneg _ ) using 1 ; rw [ show ( p : ℝ ) ^ ( 3 / 2 : ℝ ) = p ^ ( 1 / 2 : ℝ ) * p by rw [ ← Real.rpow_add_one ] <;> norm_num ; linarith ] ; ring_nf;
            rw [ ← Real.sqrt_eq_rpow, ← Real.sqrt_div_self ] ; ring;
          rw [ ← summable_nat_add_iff 3 ];
          exact Summable.of_nonneg_of_le ( fun n => div_nonneg ( Real.log_nonneg <| Real.le_log_iff_exp_le ( by positivity ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith ) <| sq_nonneg _ ) ( fun n => h_bound _ <| by linarith ) <| by simpa using summable_nat_add_iff 3 |>.2 <| Real.summable_one_div_nat_rpow.2 <| by norm_num;
        -- Since the original series is summable, and the new series is a subseries of it, the new series must also be summable.
        have h_subseries : Summable (fun p : ℕ => Real.log (Real.log p) / p^2) → Summable (fun p : ℕ => if Nat.Prime p then Real.log (Real.log p) / p^2 else 0) := by
          intro h_summable
          have h_subseries : Summable (fun p : ℕ => if Nat.Prime p then Real.log (Real.log p) / p^2 else 0) := by
            have h_abs : ∀ p : ℕ, abs ((if Nat.Prime p then Real.log (Real.log p) / p^2 else 0)) ≤ abs (Real.log (Real.log p) / p^2) := by
              intro p; split_ifs <;> norm_num;
            -- Apply the comparison test with the original series.
            have h_comparison : Summable (fun p : ℕ => abs (Real.log (Real.log p) / p^2)) := by
              exact h_summable.abs;
            -- Apply the comparison test with the original series to conclude that the subseries is summable.
            have h_comparison : Summable (fun p : ℕ => abs ((if Nat.Prime p then Real.log (Real.log p) / p^2 else 0))) := by
              exact Summable.of_nonneg_of_le ( fun p => abs_nonneg _ ) h_abs h_comparison;
            exact h_comparison.of_abs;
          convert h_subseries using 1;
        exact h_subseries h_summable;
      have h_comparison : Summable (fun p : ℕ => if Nat.Prime p then (1 : ℝ) / (p : ℝ)^2 else 0) := by
        exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
      convert h_comparison.add ‹Summable fun p : ℕ => if Nat.Prime p then Real.log ( Real.log p ) / p ^ 2 else 0› using 2 ; ring_nf;
      split_ifs <;> ring;
    rw [ ← summable_nat_add_iff ( K + 1 ) ] at *;
    grind

/-
The partial sum `sum_part1` converges to the tail sum as x goes to infinity.
-/
lemma sum_part1_tendsto (K : ℕ) :
  Filter.Tendsto (fun x => sum_part1 K x) Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
    -- By definition of `sum_part1` and `tail_sum_loglog_sq`, we can rewrite the limit expression.
    have h_tail_limit : Filter.Tendsto (fun x => ∑' p, if Nat.Prime p ∧ K < p ∧ (p : ℝ) ≤ p_upper_bound x then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0) Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
      have h_tail_limit : Filter.Tendsto (fun x => ∑' p, if Nat.Prime p ∧ K < p ∧ p ≤ Nat.floor (p_upper_bound x) then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0) Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
        have h_tail_limit : Filter.Tendsto (fun x => ∑' p, if Nat.Prime p ∧ K < p ∧ p ≤ x then (Real.log (Real.log p) + 1) / (p : ℝ)^2 else 0) Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
          convert Summable.hasSum _ |> fun h => h.tendsto_sum_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) using 1;
          · ext; rw [ Function.comp_apply, tsum_eq_sum ];
            any_goals exact Finset.range ( Nat.succ ‹_› );
            · congr! 1;
              grind;
            · grind;
          · exact tail_sum_loglog_sq_summable K
        generalize_proofs at *; (
        refine h_tail_limit.comp ?_;
        have h_p_upper_bound_inf : Filter.Tendsto (fun x : ℝ => 4 * x * (Real.log (Real.log x))^2) Filter.atTop Filter.atTop := by
          have h_p_upper_bound_inf : Filter.Tendsto (fun x : ℝ => x * (Real.log (Real.log x))^2) Filter.atTop Filter.atTop := by
            have h_log_log_sq_inf : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)^2) Filter.atTop Filter.atTop := by
              exact Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) );
            exact Filter.tendsto_id.atTop_mul_atTop₀ h_log_log_sq_inf;
          simpa only [ mul_assoc ] using h_p_upper_bound_inf.const_mul_atTop zero_lt_four;
        exact tendsto_nat_floor_atTop.comp h_p_upper_bound_inf);
      refine h_tail_limit.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
      congr! 3;
      rw [ Nat.le_floor_iff ( by exact mul_nonneg ( mul_nonneg zero_le_four ( by positivity ) ) ( sq_nonneg _ ) ) ];
    refine' h_tail_limit.congr' _ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx ; simp +decide [ sum_part1, p_upper_bound ] ;
    rw [ tsum_eq_sum ];
    exact
      Eq.symm
        (Finset.sum_filter (fun a => Nat.Prime a ∧ K < a ∧ ↑a ≤ 4 * x * Real.log (Real.log x) ^ 2)
          fun a => (Real.log (Real.log ↑a) + 1) / ↑a ^ 2);
    exact fun p hp => if_neg fun h => hp <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_floor <| by simpa using h.2.2;

/-
The sum of log p for p <= x is O(x).
-/
lemma theta_bound (assumps : SieveAssumptions) :
  (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p) =O[Filter.atTop] (fun x => x) := by
    have := assumps.1;
    -- From `Bound_prod_primes_le_x_sq`, we have `log (prod_{p <= x} p^2) - 2x = o(x)`.
    -- `log (prod p^2) = sum_{p <= x} log (p^2) = 2 sum_{p <= x} log p`.
    -- So `2 sum log p - 2x = o(x)`.
    -- This implies `sum log p - x = o(x)`.
    -- Since `x = O(x)`, we have `sum log p = O(x)`.
    have h_sum_log_p : (fun x : ℝ => 2 * ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p - 2 * x) =o[Filter.atTop] (fun x : ℝ => x) := by
      have h_sum_log_p : (fun x : ℝ => Real.log (∏ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), ((p : ℝ)^2)) - 2 * x) =o[Filter.atTop] (fun x : ℝ => x) := by
        convert this using 1;
        unfold Bound_prod_primes_le_x_sq ;
        simp +decide only [and_comm];
      refine h_sum_log_p.congr' ?_ ?_;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_prod _ _ fun p hp => by norm_cast; aesop ] ; norm_num [ Finset.mul_sum _ _ _ ] ;
      · rfl;
    rw [ Asymptotics.isLittleO_iff ] at h_sum_log_p;
    rw [ Asymptotics.isBigO_iff ];
    obtain ⟨ c, hc ⟩ := Filter.eventually_atTop.mp ( h_sum_log_p zero_lt_one );
    refine' ⟨ 2, Filter.eventually_atTop.mpr ⟨ Max.max c 2, fun x hx => _ ⟩ ⟩ ; specialize hc x ( le_trans ( le_max_left _ _ ) hx ) ; norm_num at *;
    cases abs_cases x <;> cases abs_cases ( ∑ p ∈ Finset.range ( ⌊x⌋₊ + 1 ) with Nat.Prime p ∧ ( p : ℝ ) ≤ x, Real.log p ) <;> cases abs_cases ( 2 * ∑ p ∈ Finset.range ( ⌊x⌋₊ + 1 ) with Nat.Prime p ∧ ( p : ℝ ) ≤ x, Real.log p - 2 * x ) <;> linarith

/-
The prime counting function pi(x) is O(x / log x).
-/
lemma pi_bound (assumps : SieveAssumptions) :
  (fun x => ((Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card : ℝ)) =O[Filter.atTop] (fun x => x / Real.log x) := by
    -- By definition of $pi(x)$, we know that $\pi(x) \leq \theta(x) / \log(\sqrt{x}) + \sqrt{x}$.
    have h_pi_le_theta : ∀ x : ℝ, x ≥ 100 → (Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card ≤ (2 * (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p)) / Real.log x + Real.sqrt x := by
      intro x hx
      have h_pi_le_theta_step : (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p) ≥ (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log (Real.sqrt x)) := by
        have h_pi_le_theta_step : (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p) ≥ (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log (Real.sqrt x)) := by
          exact Finset.sum_le_sum fun p hp => Real.log_le_log ( Real.sqrt_pos.mpr <| by positivity ) <| by linarith [ Finset.mem_filter.mp hp ] ;
        exact h_pi_le_theta_step.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( fun p hp => by aesop ) fun _ _ _ => Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop );
      -- The number of primes in the interval $(\sqrt{x}, x]$ is at least $\pi(x) - \pi(\sqrt{x})$.
      have h_prime_count : (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), 1) ≥ (Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card - (Finset.filter Nat.Prime (Finset.range (Nat.floor (Real.sqrt x) + 1))).card := by
        have h_prime_count : Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)) ⊇ Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1)) \ Finset.filter Nat.Prime (Finset.range (Nat.floor (Real.sqrt x) + 1)) := by
          simp +contextual [ Finset.subset_iff ];
          exact fun p hp₁ hp₂ hp₃ => ⟨ Nat.lt_of_floor_lt hp₃, Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr ( Nat.le_of_lt_succ hp₁ ) ) ⟩;
        have := Finset.card_mono h_prime_count; simp_all +decide [ Finset.card_sdiff ] ;
        exact this.trans ( add_le_add_left ( Finset.card_mono <| Finset.inter_subset_left ) _ );
      -- Since $\pi(\sqrt{x}) \leq \sqrt{x}$, we have $\pi(x) \leq \theta(x) / \log(\sqrt{x}) + \sqrt{x}$.
      have h_pi_le_theta_step2 : (Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card ≤ (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) > Real.sqrt x ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), 1) + Real.sqrt x := by
        have h_pi_le_theta_step2 : (Finset.filter Nat.Prime (Finset.range (Nat.floor (Real.sqrt x) + 1))).card ≤ Real.sqrt x := by
          refine' le_trans _ ( Nat.floor_le <| Real.sqrt_nonneg x );
          exact_mod_cast le_trans ( Finset.card_le_card <| show Finset.filter Nat.Prime ( Finset.range ( ⌊Real.sqrt x⌋₊ + 1 ) ) ⊆ Finset.Ico 2 ( ⌊Real.sqrt x⌋₊ + 1 ) from fun p hp => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2, Finset.mem_range.mp <| Finset.mem_filter.mp hp |>.1 ⟩ ) <| by simp +arith +decide;
        norm_num at *;
        exact le_trans ( Nat.cast_le.mpr h_prime_count ) ( by push_cast; linarith );
      simp_all +decide [ Real.log_sqrt ( show 0 ≤ x by positivity ) ];
      exact le_trans h_pi_le_theta_step2 ( add_le_add_right ( by rw [ le_div_iff₀ ( Real.log_pos <| by linarith ) ] ; linarith ) _ );
    -- From `theta_bound`, we know $\theta(x) = O(x)$.
    have h_theta_bound : (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p) =O[Filter.atTop] (fun x => x) := by
      exact theta_bound assumps;
    -- Since $\sqrt{x} = o(x / \log x)$, we can conclude that $\pi(x) = O(x / \log x)$.
    have h_sqrt_o : (fun x => Real.sqrt x) =o[Filter.atTop] (fun x => x / Real.log x) := by
      -- We can simplify the expression $\frac{\sqrt{x} \cdot \log x}{x}$ to $\frac{\log x}{\sqrt{x}}$.
      suffices h_simplified : Filter.Tendsto (fun x => Real.log x / Real.sqrt x) Filter.atTop (nhds 0) by
        rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
        · grind;
        · exact ⟨ 2, by rintro x hx ( rfl | rfl | rfl ) <;> norm_num at hx ⟩;
      -- Let $y = \sqrt{x}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{\log(y^2)}{y} = \lim_{y \to \infty} \frac{2 \log y}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y => 2 * Real.log y / y) Filter.atTop (nhds 0) by
        have := h_log_y.comp ( show Filter.Tendsto ( fun x : ℝ => Real.sqrt x ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x ^ 2, fun y hy => Real.le_sqrt_of_sq_le <| by nlinarith ⟩ );
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.log_sqrt hx.le ] ; ring );
      -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
      suffices h_log_z : Filter.Tendsto (fun z => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_z.congr ( by simp +contextual [div_eq_mul_inv, mul_assoc, mul_comm] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
    -- By combining the results from h_pi_le_theta, h_theta_bound, and h_sqrt_o, we can conclude that the cardinality is O(x / log x).
    have h_card_O : (fun x => (2 * (∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), Real.log p)) / Real.log x) =O[Filter.atTop] (fun x => x / Real.log x) := by
      rw [ Asymptotics.isBigO_iff ] at *;
      obtain ⟨ c, hc ⟩ := h_theta_bound; use 2 * c; filter_upwards [ hc, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂; norm_num [ abs_div, abs_mul, abs_of_nonneg, Real.log_nonneg hx₂.le ] at *;
      convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left hx₁ zero_le_two ) ( inv_nonneg.mpr ( Real.log_nonneg hx₂.le ) ) using 1 ; ring;
    refine' Asymptotics.IsBigO.trans _ ( h_card_O.add h_sqrt_o.isBigO );
    rw [ Asymptotics.isBigO_iff ];
    use 1; filter_upwards [ Filter.eventually_ge_atTop 100 ] with x hx using by rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ), Real.norm_of_nonneg ( add_nonneg ( div_nonneg ( mul_nonneg zero_le_two <| Finset.sum_nonneg fun _ _ => Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.Prime.pos <| by aesop ) <| Real.log_nonneg <| by linarith ) <| Real.sqrt_nonneg _ ) ] ; linarith [ h_pi_le_theta x hx ] ;

/-
The sum of (log log p + 1) for p <= x is O(x log log x / log x).
-/
lemma sum_loglog_bound (assumps : SieveAssumptions) :
  (fun x => ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), (Real.log (Real.log p) + 1)) =O[Filter.atTop] (fun x => x * Real.log (Real.log x) / Real.log x) := by
    have h_sum_bound : (fun x => ((Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card : ℝ) * (Real.log (Real.log x) + 1)) =O[Filter.atTop] (fun x => x * Real.log (Real.log x) / Real.log x) := by
      have h_sum_bound : (fun x => ((Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card : ℝ)) =O[Filter.atTop] (fun x => x / Real.log x) := by
        exact pi_bound assumps;
      have h_mul_bound : (fun x => (Real.log (Real.log x) + 1)) =O[Filter.atTop] (fun x => Real.log (Real.log x)) := by
        norm_num [ Asymptotics.isBigO_iff ];
        exact ⟨ 2, Real.exp ( Real.exp 1 ), fun x hx => by rw [ abs_le ] ; constructor <;> cases abs_cases ( Real.log ( Real.log x ) ) <;> linarith [ show 1 ≤ Real.log ( Real.log x ) from by rw [ Real.le_log_iff_exp_le ( Real.log_pos <| by linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ) ] ; rw [ Real.le_log_iff_exp_le ] <;> linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ] ⟩;
      convert h_sum_bound.mul h_mul_bound using 2 ; ring;
    refine' Asymptotics.IsBigO.trans _ h_sum_bound;
    refine' Asymptotics.isBigO_iff.mpr _;
    refine' ⟨ 1, Filter.eventually_atTop.mpr ⟨ 3, fun x hx => _ ⟩ ⟩ ; norm_num;
    refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun i hi => _ ) _;
    use fun i => |Real.log ( Real.log x ) + 1|;
    · rw [ abs_of_nonneg, abs_of_nonneg ] <;> norm_num at *;
      · exact Real.log_le_log ( Real.log_pos <| Nat.one_lt_cast.mpr hi.2.1.one_lt ) ( Real.log_le_log ( Nat.cast_pos.mpr hi.2.1.pos ) hi.2.2 );
      · exact add_nonneg ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ) zero_le_one;
      · by_cases hi' : i ≤ 2;
        · interval_cases i <;> norm_num at *;
          have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ Real.log_inv ( Real.log 2 ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( Real.log_pos one_lt_two ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ];
        · exact add_nonneg ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( i : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) zero_le_one;
    · norm_num [ Finset.sum_filter ];
      exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_mono <| fun p hp => by aesop ) <| abs_nonneg _

/-
The ratio of log(p_upper_bound x) to log x tends to 1.
-/
lemma log_p_upper_bound_div_log_x_tendsto_one :
  Filter.Tendsto (fun x => Real.log (p_upper_bound x) / Real.log x) Filter.atTop (nhds 1) := by
    unfold p_upper_bound;
    -- We can simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun x => (Real.log 4 + Real.log x + 2 * Real.log (Real.log (Real.log x))) / Real.log x) Filter.atTop (nhds 1) by
      refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ using by rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ) ) ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] ; ring );
    -- We can use the fact that $\frac{\log(\log(\log(x)))}{\log(x)}$ tends to $0$ as $x$ tends to infinity.
    have h_log_log_log : Filter.Tendsto (fun x => Real.log (Real.log (Real.log x)) / Real.log x) Filter.atTop (nhds 0) := by
      -- Let $y = \log x$, therefore the expression becomes $\frac{\log (\log y)}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y => Real.log (Real.log y) / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop );
      -- Let $z = \log y$, therefore the expression becomes $\frac{\log z}{e^z}$.
      suffices h_log_z : Filter.Tendsto (fun z => Real.log z / Real.exp z) Filter.atTop (nhds 0) by
        have := h_log_z.comp Real.tendsto_log_atTop;
        exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
      have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
      refine' squeeze_zero_norm' _ this ; norm_num [ Real.exp_neg ];
      exact ⟨ 2, fun x hx => by rw [ ← div_eq_mul_inv ] ; gcongr ; rw [ abs_of_nonneg ( Real.log_nonneg ( by linarith ) ) ] ; linarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < x ) ] ⟩;
    ring_nf;
    simpa using Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) ) ) ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ) ( h_log_log_log.mul_const 2 ) |> fun h => h.trans ( by norm_num )

/-
The limit of (log log x)^k / log x as x tends to infinity is 0.
-/
lemma log_log_pow_div_log_tendsto_zero (k : ℝ) :
  Filter.Tendsto (fun x => (Real.log (Real.log x))^k / Real.log x) Filter.atTop (nhds 0) := by
    -- Let $y = \log x$, so we deal with $\lim_{y \to \infty} \frac{(\log y)^k}{y}$.
    suffices h_log : Filter.Tendsto (fun y => (Real.log y) ^ k / y) Filter.atTop (nhds 0) by
      exact h_log.comp ( Real.tendsto_log_atTop )
    generalize_proofs at *; (
    -- Let $z = \log y$, so we can rewrite the limit as $\lim_{z \to \infty} \frac{z^k}{e^z}$.
    suffices h_log : Filter.Tendsto (fun z => z ^ k / Real.exp z) Filter.atTop (nhds 0) by
      have := h_log.comp Real.tendsto_log_atTop
      generalize_proofs at *; (
      exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] ))
    generalize_proofs at *; (
    -- We can use the fact that the exponential function grows faster than any polynomial function.
    have h_exp_growth : Filter.Tendsto (fun z => z ^ k / Real.exp z) Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun z => z ^ (⌈k⌉₊ : ℝ) / Real.exp z) Filter.atTop (nhds 0) := by
        simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero ⌈k⌉₊ |> Filter.Tendsto.comp <| Filter.tendsto_id;
      refine' squeeze_zero_norm' _ this;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( by simpa using Real.rpow_le_rpow_of_exponent_le hx.le <| Nat.le_ceil k ) <| by positivity;
    generalize_proofs at *; (
    convert h_exp_growth using 1)))

/-
The asymptotic behavior of the term involving p_upper_bound.
-/
lemma p_upper_bound_term_asymptotics :
  (fun x => p_upper_bound x * Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x)) =O[Filter.atTop] (fun x => x * (Real.log (Real.log x))^3 / Real.log x) := by
    -- We can simplify the expression by dividing both sides by $x (\log \log x)^2$.
    suffices h_simplified : (fun x => Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x)) =O[Filter.atTop] (fun x => Real.log (Real.log x) / Real.log x) by
      convert h_simplified.mul ( show ( fun x => p_upper_bound x ) =O[Filter.atTop] ( fun x => x * ( Real.log ( Real.log x ) ) ^ 2 ) from _ ) using 2 ; ring;
      · ring;
      · unfold p_upper_bound; norm_num [ Asymptotics.isBigO_iff ] ; ring_nf ;
        exact ⟨ 4, 1, fun x hx => by norm_num ⟩;
    -- We know that $\log P(x) \sim \log x$ and $\log \log P(x) \sim \log \log x$.
    have h_log_P : Filter.Tendsto (fun x => Real.log (p_upper_bound x) / Real.log x) Filter.atTop (nhds 1) := by
      exact log_p_upper_bound_div_log_x_tendsto_one
    have h_log_log_P : Filter.Tendsto (fun x => Real.log (Real.log (p_upper_bound x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
      have h_log_log_P : Filter.Tendsto (fun x => Real.log (Real.log (p_upper_bound x) / Real.log x) / Real.log (Real.log x)) Filter.atTop (nhds 0) := by
        simpa using Filter.Tendsto.div_atTop ( Filter.Tendsto.log h_log_P one_ne_zero ) ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) );
      have h_log_log_P : Filter.Tendsto (fun x => (Real.log (Real.log (p_upper_bound x) / Real.log x) + Real.log (Real.log x)) / Real.log (Real.log x)) Filter.atTop (nhds 1) := by
        simpa [ add_div ] using h_log_log_P.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp ( Real.exp 1 ) ) ] with x hx₁ hx₂ using by rw [ div_self <| ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ] );
      refine h_log_log_P.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, h_log_P.eventually ( lt_mem_nhds one_pos ) ] with x hx₁ hx₂ using by rw [ Real.log_div ( by aesop ) ( by linarith [ Real.log_pos hx₁ ] ) ] ; ring );
    have h_ratio : Filter.Tendsto (fun x => (Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x)) / (Real.log (Real.log x) / Real.log x)) Filter.atTop (nhds 1) := by
      convert h_log_log_P.mul ( h_log_P.inv₀ one_ne_zero ) using 2 <;> ring;
    rw [ Asymptotics.isBigO_iff ];
    obtain ⟨ c, hc ⟩ := Metric.tendsto_atTop.mp h_ratio 1 zero_lt_one;
    use 2; filter_upwards [ Filter.eventually_ge_atTop c, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx₁ hx₂ hx₃; specialize hc x hx₁; rw [ Real.norm_eq_abs, Real.norm_eq_abs ] ; rw [ abs_le ] ; constructor <;> cases abs_cases ( Real.log ( Real.log ( p_upper_bound x ) ) / Real.log ( p_upper_bound x ) ) <;> cases abs_cases ( Real.log ( Real.log x ) / Real.log x ) <;> nlinarith [ abs_lt.mp hc, mul_div_cancel₀ ( Real.log ( Real.log ( p_upper_bound x ) ) / Real.log ( p_upper_bound x ) ) ( show ( Real.log ( Real.log x ) / Real.log x ) ≠ 0 from div_ne_zero ( ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith [ Real.add_one_le_exp 1 ] ) <| ne_of_gt <| Real.log_pos <| show 1 < x from by linarith [ Real.add_one_le_exp 1 ] ) ] ;

/-
p_upper_bound x tends to infinity as x tends to infinity.
-/
lemma p_upper_bound_tendsto_atTop : Filter.Tendsto p_upper_bound Filter.atTop Filter.atTop := by
  refine' Filter.Tendsto.atTop_mul_atTop₀ _ _;
  · exact Filter.tendsto_id.const_mul_atTop zero_lt_four;
  · exact Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) )

/-
Definition of S_loglog(x) as the sum of (log log p + 1) for primes p <= x.
-/
def S_loglog (x : ℝ) : ℝ := ∑ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x) (Finset.range (Nat.floor x + 1)), (Real.log (Real.log p) + 1)

/-
For any prime p, log(log p) + 1 is positive.
-/
lemma log_log_p_plus_one_pos (p : ℕ) (hp : Nat.Prime p) : Real.log (Real.log p) + 1 > 0 := by
  by_cases h₂ : p ≤ 2;
  · interval_cases p <;> norm_num at *;
    have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ Real.log_inv ( Real.log 2 ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( Real.log_pos one_lt_two ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ];
  · exact add_pos_of_nonneg_of_pos ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( p : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) zero_lt_one

/-
sum_part2 is bounded by (1/x) * S_loglog(p_upper_bound x).
-/
lemma sum_part2_le (K : ℕ) :
  ∀ᶠ x in Filter.atTop, sum_part2 K x ≤ (1/x) * S_loglog (p_upper_bound x) := by
    refine' Filter.eventually_atTop.mpr ⟨ 800, fun x hx => _ ⟩;
    unfold sum_part2 S_loglog;
    gcongr;
    · exact fun p hp₁ hp₂ => le_of_lt ( log_log_p_plus_one_pos p ( by aesop ) );
    · exact fun p hp => ⟨ hp.1, hp.2.2 ⟩

/-
S_loglog(x) is O(x log log x / log x).
-/
lemma S_loglog_is_BigO (assumps : SieveAssumptions) :
  S_loglog =O[Filter.atTop] (fun x => x * Real.log (Real.log x) / Real.log x) := by
  exact sum_loglog_bound assumps

/-
sum_part2 is non-negative for large x.
-/
lemma sum_part2_nonneg (K : ℕ) : ∀ᶠ x in Filter.atTop, 0 ≤ sum_part2 K x := by
  refine' Filter.eventually_atTop.mpr ⟨ 1, fun x hx => _ ⟩;
  unfold sum_part2;
  refine' mul_nonneg ( by positivity ) ( Finset.sum_nonneg fun p hp => _ );
  exact le_of_lt ( log_log_p_plus_one_pos p ( by aesop ) )

/-
The upper bound for sum_part2 has the correct asymptotic behavior.
-/
lemma bound_asymptotics (assumps : SieveAssumptions) :
  (fun x => (1/x) * S_loglog (p_upper_bound x)) =O[Filter.atTop] (fun x => (Real.log (Real.log x))^3 / Real.log x) := by
    have h_sum_part2_le : (fun x => (1 / x) * S_loglog (p_upper_bound x)) =O[Filter.atTop] (fun x => (1 / x) * (p_upper_bound x * Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x))) := by
      have h_S_loglog_bound : S_loglog =O[Filter.atTop] (fun x => x * Real.log (Real.log x) / Real.log x) := by
        exact S_loglog_is_BigO assumps;
      apply_rules [ Asymptotics.IsBigO.mul, h_S_loglog_bound.comp_tendsto ];
      · exact Asymptotics.isBigO_refl _ _;
      · exact Asymptotics.isBigO_refl _ _;
      · exact p_upper_bound_tendsto_atTop;
    refine' h_sum_part2_le.trans _;
    have h_sum_part2_le : (fun x => (p_upper_bound x * Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x)) / x) =O[Filter.atTop] (fun x => x * (Real.log (Real.log x))^3 / Real.log x * (1 / x)) := by
      have h_sum_part2_le : (fun x => p_upper_bound x * Real.log (Real.log (p_upper_bound x)) / Real.log (p_upper_bound x)) =O[Filter.atTop] (fun x => x * (Real.log (Real.log x))^3 / Real.log x) := by
        exact p_upper_bound_term_asymptotics;
      simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using h_sum_part2_le.mul ( Asymptotics.isBigO_refl ( fun x : ℝ => 1 / x ) Filter.atTop );
    convert h_sum_part2_le using 2 ; ring;
    by_cases h : ‹ℝ› = 0 <;> simp +decide [div_eq_mul_inv, mul_comm, mul_left_comm, h]

/-
sum_part2 tends to 0 as x goes to infinity.
-/
lemma sum_part2_tendsto (K : ℕ) (assumps : SieveAssumptions) :
  Filter.Tendsto (fun x => sum_part2 K x) Filter.atTop (nhds 0) := by
  have h1 : ∀ᶠ x in Filter.atTop, 0 ≤ sum_part2 K x := sum_part2_nonneg K
  have h2 : ∀ᶠ x in Filter.atTop, sum_part2 K x ≤ (1/x) * S_loglog (p_upper_bound x) := sum_part2_le K
  have h3 : (fun x => (1/x) * S_loglog (p_upper_bound x)) =O[Filter.atTop] (fun x => (Real.log (Real.log x))^3 / Real.log x) := bound_asymptotics assumps
  have h4 : Filter.Tendsto (fun x => (Real.log (Real.log x))^3 / Real.log x) Filter.atTop (nhds 0) := by
    convert log_log_pow_div_log_tendsto_zero 3 using 1
    norm_cast
  have h5 : Filter.Tendsto (fun x => (1/x) * S_loglog (p_upper_bound x)) Filter.atTop (nhds 0) := h3.trans_tendsto h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h5 h1 h2

/-
The density of the removed set converges to the tail sum.
-/
lemma total_removed_density (K : ℕ) (assumps : SieveAssumptions) :
  Filter.Tendsto (fun x => total_removed_bound K x / x) Filter.atTop (nhds (tail_sum_loglog_sq K)) := by
    rw [ Filter.tendsto_congr' ];
    convert Filter.Tendsto.add ( sum_part1_tendsto K ) ( sum_part2_tendsto K assumps ) using 2 ; ring;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using total_removed_bound_split K x hx ▸ rfl

/-
The cardinality of A_seq intersected with [1, x] is at least the cardinality of SF intersected with [1, x] minus the cardinality of the removed subset.
-/
lemma card_A_seq_ge (n : ℕ → ℕ) (x : ℝ):
  ((A_seq n ∩ Set.Icc 1 (Nat.floor x)).ncard : ℝ) ≥ ((SF ∩ Set.Icc 1 (Nat.floor x)).ncard : ℝ) - (removed_subset n x).card := by
    rw [ ge_iff_le, sub_le_iff_le_add ];
    norm_cast;
    rw [ ← Set.ncard_coe_finset ];
    have h_subset : (SF ∩ Set.Icc 1 ⌊x⌋₊) ⊆ (A_seq n ∩ Set.Icc 1 ⌊x⌋₊) ∪ (removed_subset n x) := by
      intro a ha;
      -- If $a$ is in $A_seq n$, then it is in the first part of the union.
      by_cases ha_A : a ∈ A_seq n;
      · exact Or.inl ⟨ ha_A, ha.2 ⟩;
      · unfold A_seq removed_subset at *; aesop;
    exact le_trans ( Set.ncard_le_ncard h_subset ) ( Set.ncard_union_le _ _ )

/-
If f >= g - h eventually, and g -> Lg, h -> Lh, and f is bounded above, then liminf f >= Lg - Lh.
-/
lemma liminf_ge_limit_sub_limit {f g h : ℕ → ℝ} {Lg Lh : ℝ}
    (h_ge : ∀ᶠ n in Filter.atTop, f n ≥ g n - h n)
    (hg : Filter.Tendsto g Filter.atTop (nhds Lg))
    (hh : Filter.Tendsto h Filter.atTop (nhds Lh))
    (hf_bdd_above : Filter.IsBoundedUnder LE.le Filter.atTop f) :
    Filter.liminf f Filter.atTop ≥ Lg - Lh := by
      have h_liminf_ge : Filter.liminf (fun n => g n - h n) Filter.atTop ≤ Filter.liminf f Filter.atTop := by
        apply_rules [ Filter.liminf_le_liminf ];
        · exact Filter.Tendsto.isBoundedUnder_ge ( hg.sub hh );
        · exact Filter.IsBoundedUnder.isCoboundedUnder_ge hf_bdd_above;
      refine' le_trans _ h_liminf_ge;
      rw [ Filter.Tendsto.liminf_eq ( hg.sub hh ) ]

/-
The sequence u_n converges to the expected limit.
-/
lemma u_tendsto (K : ℕ) (assumps : SieveAssumptions) :
  Filter.Tendsto (fun n : ℕ => ((SF ∩ Set.Icc 1 n).ncard : ℝ) / n - total_removed_bound K n / n) Filter.atTop (nhds (6 / Real.pi^2 - tail_sum_loglog_sq K)) := by
    have h_diff : Filter.Tendsto (fun n : ℕ => ((SF ∩ (Set.Icc 1 n)).ncard : ℝ) / n) Filter.atTop (nhds (6 / Real.pi^2)) := by
      have := @SF_density;
      convert this using 1;
    exact h_diff.sub ( total_removed_density K assumps |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop )

/-
The tail sum of (log log p + 1) / p^2 for p > K tends to 0 as K goes to infinity.
-/
lemma tail_sum_loglog_sq_tendsto_zero : Filter.Tendsto tail_sum_loglog_sq Filter.atTop (nhds 0) := by
  convert tendsto_sum_nat_add fun n => ( Real.log ( Real.log ( n + 1 ) ) + 1 ) / ( n + 1 ) ^ 2 * ( if Nat.Prime ( n + 1 ) then 1 else 0 ) using 1;
  ext; rw [ Summable.tsum_eq_zero_add ] ; norm_num;
  · rw [ tail_sum_loglog_sq ];
    rw [ ← Summable.sum_add_tsum_nat_add ];
    rotate_left;
    exact ‹_› + 1 + 1;
    · convert tail_sum_loglog_sq_summable _ using 1;
    · rw [ Finset.sum_eq_single ( ‹_› + 1 ) ] <;> norm_num ; ring_nf;
      · grind +ring;
      · intros; omega;
  · have h_summable : Summable (fun p : ℕ => (Real.log (Real.log p) + 1) / p^2 * (if Nat.Prime p then 1 else 0)) := by
      have := @tail_sum_loglog_sq_summable 0;
      exact this.congr fun p => by cases p <;> aesop;
    exact_mod_cast h_summable.comp_injective ( add_left_injective _ ) |> Summable.comp_injective <| add_left_injective _

/-
A sequence n is GoodSeqNat with respect to K if it is strictly increasing and satisfies the modular properties (a) and (b) with respect to P_seq K j, where a is a natural number.
-/
def GoodSeqNat (n : ℕ → ℕ) (K : ℕ) : Prop :=
  StrictMono n ∧
  (∀ j, ∀ p, Nat.Prime p → p ≤ P_seq K j → n j % p^2 = 0) ∧
  (∀ j, ∀ p, Nat.Prime p → p > P_seq K j → ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n j + a) % p^2 ≠ 0)

lemma P_seq_ge_K (K j : ℕ) : P_seq K j ≥ K := by
  -- Since $K$ is a natural number, multiplying it by $e^{e^j}$ (which is greater than 1) will give a value that's at least $K$. Taking the floor of that value should still be at least $K$.
  have h_floor : (K : ℝ) * Real.exp (Real.exp j) ≥ K := by
    exact le_mul_of_one_le_right ( Nat.cast_nonneg _ ) ( Real.one_le_exp ( by positivity ) );
  exact Nat.le_floor h_floor

/-
Existence of GoodSeqNat given sufficiently large K.
-/
lemma exists_sequence_n_nat (K P₀ : ℕ) (hK : K ≥ P₀)
    (h_prop : ∀ P ≥ P₀, ∀ M, ∃ n ≥ M, (∀ p, Nat.Prime p → p ≤ P → n % p^2 = 0) ∧ (∀ p, Nat.Prime p → p > P → ∀ (a : ℕ), 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n + a) % p^2 ≠ 0)) :
    ∃ n : ℕ → ℕ, GoodSeqNat n K := by
      obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ j, (∀ p : ℕ, Nat.Prime p → p ≤ P_seq K j → n j % p^2 = 0) ∧ (∀ p : ℕ, Nat.Prime p → P_seq K j < p → ∀ a : ℕ, 1 ≤ a → (a : ℝ) ≤ (p : ℝ) / (Real.log (Real.log p))^2 → (n j + a) % p^2 ≠ 0)) := by
        choose! f hf₁ hf₂ hf₃ using h_prop;
        use fun j => Nat.recOn j ( f ( P_seq K 0 ) 0 ) fun j ih => f ( P_seq K ( j + 1 ) ) ( ih + 1 );
        refine' ⟨ strictMono_nat_of_lt_succ fun j => _, fun j => _ ⟩;
        · exact lt_of_lt_of_le ( Nat.lt_succ_self _ ) ( hf₁ _ ( by linarith [ P_seq_ge_K K ( j + 1 ) ] ) _ );
        · induction j <;> simp_all +decide [ P_seq ];
          · refine' ⟨ fun p hp hp' => hf₂ _ _ _ _ hp hp', fun p hp hp' a ha ha' => hf₃ _ _ _ _ hp hp' _ ha ha' ⟩;
            · exact le_trans hK ( Nat.le_floor <| by nlinarith [ Real.add_one_le_exp 1 ] );
            · exact Nat.le_floor <| by nlinarith [ Real.add_one_le_exp 1, show ( K : ℝ ) ≥ P₀ by norm_cast ] ;
          · refine' ⟨ fun p hp hp' => hf₂ _ _ _ _ hp hp', fun p hp hp' a ha ha' => hf₃ _ _ _ _ hp hp' _ ha ha' ⟩;
            · exact le_trans hK ( Nat.le_floor <| by exact le_trans ( mod_cast by linarith ) <| le_mul_of_one_le_right ( by positivity ) <| Real.one_le_exp <| by positivity );
            · exact le_trans hK <| Nat.le_floor <| by exact le_trans ( by norm_num ) <| mul_le_mul_of_nonneg_left ( Real.one_le_exp <| by positivity ) <| by positivity;
      exact ⟨ n, hn.1, fun j p hp hle => hn.2 j |>.1 p hp hle, fun j p hp hgt a ha₁ ha₂ => hn.2 j |>.2 p hp hgt a ha₁ ha₂ ⟩

lemma bad_prime_properties_nat (n : ℕ → ℕ) (K : ℕ) (h_good : GoodSeqNat n K) (j : ℕ) (a : ℕ)
    (ha_sf : Squarefree a) (h_not_sf : ¬ Squarefree (n j + a)) :
    ∃ p, Nat.Prime p ∧ p^2 ∣ n j + a ∧ p > P_seq K j ∧ (a : ℝ) > (p : ℝ) / (Real.log (Real.log p))^2 := by
      obtain ⟨ p, hp_prime, hp_sq, hp_div ⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ n j + a := by
        rw [ Nat.squarefree_iff_prime_squarefree ] at h_not_sf;
        simpa [ sq ] using h_not_sf;
      by_cases hp_le : p ≤ P_seq K j;
      · have hp_div_n : p^2 ∣ n j := by
          exact h_good.2.1 j p hp_prime hp_le |> fun h => Nat.dvd_of_mod_eq_zero h;
        have hp_div_a : p^2 ∣ a := by
          simpa [ ← hp_div ] using Nat.dvd_sub ( dvd_of_mul_right_eq _ hp_div.symm ) hp_div_n;
        exact absurd ( ha_sf.squarefree_of_dvd hp_div_a ) ( by rw [ sq, Nat.squarefree_mul_iff ] ; aesop );
      · refine' ⟨ p, hp_prime, hp_div.symm ▸ dvd_mul_right _ _, not_le.mp hp_le, _ ⟩;
        have := h_good.2.2 j p hp_prime ( not_le.mp hp_le );
        exact not_le.mp fun h => this a ( Nat.pos_of_ne_zero fun ha => by subst ha; simp_all +decide ) h <| Nat.mod_eq_zero_of_dvd <| hp_div.symm ▸ dvd_mul_right _ _

/-
The removed subset is contained in the union of bad sets for relevant primes, using GoodSeqNat.
-/
lemma removed_subset_subset_union_nat (n : ℕ → ℕ) (K : ℕ) (x : ℝ) (h_good : GoodSeqNat n K) (hx : x ≥ 100) :
  removed_subset n x ⊆ (relevant_primes_for_bound K x).biUnion (fun p => bad_a_for_p n K x p) := by
    -- Let $a \in removed\_subset\ n\ x$.
    intro a ha
    obtain ⟨j, hj⟩ := Finset.mem_filter.mp ha |>.2.2
    generalize_proofs at *; (
    -- By `bad_prime_properties_nat`, there exists a prime $p$ such that $p^2 \mid n_j + a$, $p > P_{seq} K j$, and $a > p / (\log \log p)^2$.
    obtain ⟨p, hp_prime, hp_sq, hp_gt, ha_gt⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ n j + a ∧ p > P_seq K j ∧ (a : ℝ) > (p : ℝ) / (Real.log (Real.log p))^2 := by
      apply bad_prime_properties_nat n K h_good j a (by
      exact Finset.mem_filter.mp ha |>.2.1) hj
    -- Since $a \le x$, we have $p / (\log \log p)^2 < x$.
    have hp_le : (p : ℝ) ≤ p_upper_bound x := by
      apply p_bound_lemma_v2 x hx p a (by
      exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;) (by
      exact ha_gt)
    generalize_proofs at *;
    refine' Finset.mem_biUnion.mpr ⟨ p, _, _ ⟩ <;> simp_all +decide ;
    · exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_floor hp_le ) ), hp_prime, by linarith [ show K ≤ P_seq K j from Nat.le_floor <| by nlinarith [ Real.add_one_le_exp ( Real.exp j ), Real.add_one_le_exp j ] ] ⟩;
    · exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.1, Finset.mem_Icc.mp ( Finset.mem_filter.mp ha |>.1 ) |>.2 ⟩, j, hp_gt, Nat.mod_eq_zero_of_dvd hp_sq ⟩)

/-
Bound on the size of the removed subset for GoodSeqNat.
-/
lemma removed_subset_card_le_nat (n : ℕ → ℕ) (K : ℕ) (x : ℝ) (h_good : GoodSeqNat n K) (hx : x ≥ 100) (hK : K ≥ 3) :
  (removed_subset n x).card ≤ total_removed_bound K x := by
    refine' le_trans _ ( Finset.sum_le_sum fun p hp => _ );
    case refine'_2 => exact fun p => ( removed_subset n x ∩ bad_a_for_p n K x p |> Finset.card : ℝ );
    · have h_card_le : (removed_subset n x).card ≤ (Finset.biUnion (relevant_primes_for_bound K x) (fun p => removed_subset n x ∩ bad_a_for_p n K x p)).card := by
        refine Finset.card_le_card ?_;
        intro a ha;
        have := removed_subset_subset_union_nat n K x h_good hx;
        specialize this ha; aesop;
      refine' le_trans ( Nat.cast_le.mpr h_card_le ) _;
      convert Nat.cast_le.mpr ( Finset.card_biUnion_le ) using 1;
      · norm_num +zetaDelta at *;
        congr! 1;
        ext; simp [relevant_primes_for_bound];
        exact fun _ _ _ => le_trans ( Nat.cast_le.mpr ( Nat.le_of_lt_succ ‹_› ) ) ( Nat.floor_le ( by exact mul_nonneg ( by positivity ) ( sq_nonneg _ ) ) );
      · infer_instance;
      · infer_instance;
      · infer_instance;
    · refine' le_trans _ ( card_bad_a_for_p_le n K x p hK ( by aesop ) ( by linarith ) );
      exact_mod_cast Finset.card_le_card fun x hx => by aesop;

/-
If n is a GoodSeqNat with respect to K, then the lower density of A_seq n is at least 6/pi^2 - tail_sum_loglog_sq K.
-/
lemma lowerDensity_A_seq_bound_nat (n : ℕ → ℕ) (K : ℕ) (hK : K ≥ 3) (h_good : GoodSeqNat n K) (assumps : SieveAssumptions) :
  lowerDensity (A_seq n) ≥ 6 / Real.pi^2 - tail_sum_loglog_sq K := by
    apply le_of_forall_gt_imp_ge_of_dense;
    have := @liminf_ge_limit_sub_limit;
    contrapose! this;
    obtain ⟨ a, ha₁, ha₂ ⟩ := this;
    refine' ⟨ _, _, _, _, _, _, _, _, _ ⟩;
    use fun x => ( Set.ncard ( A_seq n ∩ Set.Icc 1 x ) : ℝ ) / x;
    use fun x => ( Set.ncard ( SF ∩ Set.Icc 1 x ) : ℝ ) / x - total_removed_bound K x / x;
    use fun x => 0;
    exact 6 / Real.pi ^ 2 - tail_sum_loglog_sq K;
    exact 0;
    · filter_upwards [ Filter.eventually_gt_atTop 100 ] with x hx;
      have := removed_subset_card_le_nat n K x h_good ( by norm_num; linarith ) ( by linarith );
      have := card_A_seq_ge n x;
      norm_num [ Nat.floor_natCast ] at *;
      rw [ ← add_div ] ; gcongr ; linarith;
    · convert u_tendsto K assumps using 1;
    · exact tendsto_const_nhds;
    · refine' ⟨ _, _ ⟩;
      · refine' ⟨ 1, Filter.eventually_atTop.mpr ⟨ 1, fun x hx => _ ⟩ ⟩;
        simp +zetaDelta at *;
        exact div_le_one_of_le₀ ( mod_cast le_trans ( Set.ncard_le_ncard ( show A_seq n ∩ Set.Icc 1 x ⊆ Set.Icc 1 x from fun y hy => hy.2 ) ) ( by norm_num [ Set.ncard_eq_toFinset_card' ] ) ) ( by positivity );
      · convert ha₁.trans_le _ using 1;
        linarith
/-
If A has property P_bar_infty (in particular, if it has property P_bar), then its upper density is strictly less than 6/pi^2.
-/
theorem theorem_overp_i (A : Set ℕ) (h : PropertyP_bar_infty A) :
    upperDensity A < 6 / Real.pi^2 := by
      obtain ⟨ n₁, n₂, h₁, h₂ ⟩ := P_bar_infty_implies_pair A h;
      -- By `upperDensity_finite_diff`, `upperDensity A = upperDensity A'`.
      have h_upperDensity_eq : upperDensity A = upperDensity {a ∈ A | Squarefree (n₁ + a) ∧ Squarefree (n₂ + a)} := by
        apply upperDensity_finite_diff;
        exact ⟨ h₂.subset fun x hx => by aesop, Set.finite_empty.subset fun x hx => by aesop ⟩;
      -- Apply `sieve_strict_bound` to $A'$ with $C = n_2 - n_1$.
      have h_sieve : ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ {a ∈ A | Squarefree (n₁ + a) ∧ Squarefree (n₂ + a)}, a % p^2 ≠ b := by
        intro p hp
        use (p^2 - n₁ % p^2) % p^2;
        refine' ⟨ Nat.mod_lt _ ( pow_pos hp.pos _ ), fun a ha ha' => _ ⟩;
        -- Since $a \equiv -n_1 \pmod{p^2}$, we have $n_1 + a \equiv 0 \pmod{p^2}$, which implies $p^2 \mid (n_1 + a)$.
        have h_div : p^2 ∣ (n₁ + a) := by
          rw [ Nat.dvd_iff_mod_eq_zero ];
          rw [ Nat.add_mod, ha' ];
          simp +decide [ Nat.add_sub_of_le ( Nat.mod_lt _ ( pow_pos hp.pos 2 ) |> Nat.le_of_lt ) ];
        exact absurd ( ha.2.1.squarefree_of_dvd h_div ) ( by rw [ sq, Nat.squarefree_mul_iff ] ; aesop );
      have h_sieve_strict : ∀ p, Nat.Prime p → p > n₂ - n₁ → ∃ b1 b2, b1 < p^2 ∧ b2 < p^2 ∧ b1 ≠ b2 ∧ (∀ a ∈ {a ∈ A | Squarefree (n₁ + a) ∧ Squarefree (n₂ + a)}, a % p^2 ≠ b1) ∧ (∀ a ∈ {a ∈ A | Squarefree (n₁ + a) ∧ Squarefree (n₂ + a)}, a % p^2 ≠ b2) := by
        intro p hp hp_gt
        use (p^2 - n₁ % p^2) % p^2, (p^2 - n₂ % p^2) % p^2;
        refine' ⟨ Nat.mod_lt _ ( pow_pos hp.pos _ ), Nat.mod_lt _ ( pow_pos hp.pos _ ), _, _, _ ⟩;
        · intro h_mod_eq
          have h_div : p^2 ∣ (n₂ - n₁) := by
            have h_div : n₂ % p^2 = n₁ % p^2 := by
              simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
              rw [ Nat.cast_sub ( Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ), Nat.cast_sub ( Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ) ] at h_mod_eq ; aesop;
            rw [ ← Nat.mod_add_div n₂ ( p ^ 2 ), ← Nat.mod_add_div n₁ ( p ^ 2 ), h_div ];
            norm_num [ Nat.add_sub_add_left, ← mul_tsub ];
          nlinarith [ Nat.le_of_dvd ( Nat.sub_pos_of_lt h₁ ) h_div, Nat.sub_add_cancel h₁.le ];
        · intro a ha H; have := Nat.mod_eq_of_lt ( show n₁ % p ^ 2 < p ^ 2 from Nat.mod_lt _ ( pow_pos hp.pos _ ) ) ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
          -- Since $a \equiv -n₁ \pmod{p^2}$, we have $n₁ + a \equiv 0 \pmod{p^2}$, which contradicts the assumption that $n₁ + a$ is squarefree.
          have h_contradiction : p^2 ∣ (n₁ + a) := by
            rw [ ← ZMod.natCast_eq_zero_iff ] ; simp_all +decide [ Nat.cast_sub ( show n₁ % p ^ 2 ≤ p ^ 2 from Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ) ] ;
          have := ha.1.2.squarefree_of_dvd h_contradiction; simp_all +decide [ sq, Nat.squarefree_mul_iff ] ;
        · intro a ha H; have := Nat.mod_eq_of_lt ( show n₂ % p ^ 2 < p ^ 2 from Nat.mod_lt _ ( pow_pos hp.pos _ ) ) ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
          -- Since $a \equiv -n₂ \pmod{p^2}$, we have $n₂ + a \equiv 0 \pmod{p^2}$, which contradicts the assumption that $n₂ + a$ is squarefree.
          have h_contradiction : p^2 ∣ (n₂ + a) := by
            rw [ ← ZMod.natCast_eq_zero_iff ] ; simp_all +decide [ Nat.cast_sub ( show n₂ % p ^ 2 ≤ p ^ 2 from Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ) ] ;
          have := ha.2.2.squarefree_of_dvd h_contradiction; simp_all +decide [ sq, Nat.squarefree_mul_iff ] ;
      exact h_upperDensity_eq.symm ▸ sieve_strict_bound _ _ h_sieve h_sieve_strict

/-
For any epsilon > 0, there exists a set A with property P_bar such that its lower density is at least 6/pi^2 - epsilon.
-/
theorem theorem_overp_ii (assumps : SieveAssumptions) :
    ∀ ε > 0, ∃ A : Set ℕ, PropertyP_bar A ∧ lowerDensity A ≥ 6 / Real.pi^2 - ε := by
      have := lemma_largeP_v2 assumps;
      -- By `tail_sum_loglog_sq_tendsto_zero`, there exists $K_1$ such that for all $K \ge K_1$, `tail_sum_loglog_sq K < \epsilon`.
      have h_tail : ∀ ε > 0, ∃ K₁ : ℕ, ∀ K ≥ K₁, tail_sum_loglog_sq K < ε := by
        exact fun ε ε_pos => by rcases Metric.tendsto_atTop.mp ( tail_sum_loglog_sq_tendsto_zero ) ε ε_pos with ⟨ K₁, hK₁ ⟩ ; exact ⟨ K₁, fun K hK => by linarith [ abs_lt.mp ( hK₁ K hK ) ] ⟩ ;
      intro ε hε_pos
      obtain ⟨K₁, hK₁⟩ := h_tail ε hε_pos
      obtain ⟨P₀, hP₀_ge_3, hP₀⟩ := this
      set K := max K₁ (max P₀ 3) with hK_def
      obtain ⟨n, hn⟩ := exists_sequence_n_nat K P₀ (by
      exact le_max_of_le_right ( le_max_left _ _ )) hP₀
      generalize_proofs at *;
      use A_seq n;
      refine' ⟨ _, _ ⟩;
      · exact PropertyP_bar_A_seq n hn.1;
      · refine' le_trans _ ( lowerDensity_A_seq_bound_nat n K _ hn assumps );
        · exact sub_le_sub_left ( le_of_lt ( hK₁ K ( le_max_left _ _ ) ) ) _;
        · exact le_trans ( by linarith ) ( le_max_right _ _ ) |> le_trans ( le_max_right _ _ )

#print axioms theorem_overp_i

#print axioms theorem_overp_ii
