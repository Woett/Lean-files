/-
We say that a sequence of positive integers $A$ has:

- property $P$ if, for all positive integers $n$, there are only finitely many $a \in A$ such that $n+a$ is squarefree.
- property $Q$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$ with $a < n$.
- property $\overline{P}$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all $a \in A$.
- property $\overline{P}_\infty$ if there exist infinitely many positive integers $n$ such that $n+a$ is squarefree for all but finitely many $a \in A$.

Solving Erdős Problem #1102 (https://www.erdosproblems.com/1102), Terence Tao and I managed to prove tight bounds on the possible densities of sequences with one of the above properties.

W. van Doorn and T. Tao, Growth rates of sequences governed by the squarefree properties of their translates. arXiv:2512.01087 (2025).

Define a sequence to be admissible if if avoids at least one residue class modulo $p^2$ for every prime $p$. Thanks to Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), the proof of the following theorem is formalized in the Lean file below:

There exists an absolute constant $C$ such that any admissible sequence $A = \{a_1 < a_2 < \cdots \}$ for which $a_j \ge \exp(C j/\log j)$ holds for infinitely many $j$, has property $Q$. In particular, the specific sequences $2^n \pm 1$ and $n! \pm 1$ all have property $Q$. 

The proof is conditional on asymptotic bounds on a sum and a product on primes, which both readily follow from the prime number theorem. These asymptotics are bundled as the structure SieveAssumptions that you can find at the start of the formalization.

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
A set A satisfies the growth condition with constant C if a_j >= exp(C j / log j) for infinitely many j.
-/
def GrowthCondition (A : Set ℕ) (C : ℝ) : Prop :=
  ∃ᶠ j in Filter.atTop, (Nat.nth (· ∈ A) (j - 1) : ℝ) ≥ Real.exp (C * j / Real.log j)

/-
The sequence A1 is admissible.
-/
lemma A1_admissible : Admissible A1 := by
  intro p hp; by_cases h_cases : p = 2; (
  use 0 ; simp +decide [h_cases];
  rintro a ⟨ j, hj, rfl ⟩ ; rcases j with ( _ | _ | j ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *);
  refine' ⟨ 1, _, _ ⟩ <;> norm_num +zetaDelta at *;
  · exact hp.one_lt;
  · rintro a ⟨ j, hj₁, rfl ⟩ ; intro H; have := Nat.dvd_of_mod_eq_zero ( show ( 2 ^ j ) % p ^ 2 = 0 from Nat.mod_eq_zero_of_dvd <| ?_ ) ; simp_all +decide ;
    · exact absurd ( hp.dvd_of_dvd_pow ( dvd_of_mul_left_dvd this ) ) ( by intro h; have := Nat.le_of_dvd ( by positivity ) h; interval_cases p <;> trivial );
    · exact ⟨ ( 2 ^ j + 1 ) / p ^ 2, by linarith [ Nat.mod_add_div ( 2 ^ j + 1 ) ( p ^ 2 ) ] ⟩

/-
The sequence A2 is admissible.
-/
lemma A2_admissible : Admissible A2 := by
  intro p hp; by_cases h_cases : p = 2; (
  use 2; norm_num [ h_cases ];
  rintro a ⟨ j, hj₁, rfl ⟩ ; rcases j with ( _ | _ | j ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *;
  grind);
  use p^2 - 1;
  refine' ⟨ Nat.sub_lt ( pow_pos hp.pos _ ) zero_lt_one, _ ⟩;
  rintro a ⟨ j, hj, rfl ⟩;
  intro h_mod
  have h_div : p^2 ∣ 2^j := by
    exact ⟨ ( 2 ^ j - 1 ) / p ^ 2 + 1, by linarith [ Nat.mod_add_div ( 2 ^ j - 1 ) ( p ^ 2 ), Nat.sub_add_cancel ( show 1 ≤ p ^ 2 from pow_pos hp.pos 2 ), Nat.sub_add_cancel ( show 1 ≤ 2 ^ j from Nat.one_le_pow _ _ ( by decide ) ) ] ⟩;
  exact absurd ( hp.dvd_of_dvd_pow ( dvd_of_mul_left_dvd h_div ) ) ( by intro h; have := Nat.le_of_dvd ( by positivity ) h; interval_cases p <;> trivial )

/-
The sequence A3 is admissible.
-/
lemma A3_admissible : Admissible A3 := by
  intro p hp_prime
  by_cases hp_odd : p % 2 = 1;
  · -- For odd primes p, the elements j! + 1 are congruent to 1 mod p^2 for all j >= 2p.
    have h_odd_primes : ∀ j ≥ 2 * p, (Nat.factorial j + 1) % p^2 = 1 := by
      intros j hj
      have h_factorial : p^2 ∣ Nat.factorial j := by
        have h_factorial : p^2 ∣ Nat.factorial (2 * p) := by
          have h_factorial : p^2 ∣ Nat.factorial p * Nat.factorial p := by
            simpa only [ sq ] using mul_dvd_mul ( Nat.dvd_factorial hp_prime.pos le_rfl ) ( Nat.dvd_factorial hp_prime.pos le_rfl );
          exact dvd_trans h_factorial ( Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| by rw [ two_mul ] );
        exact dvd_trans h_factorial ( Nat.factorial_dvd_factorial hj );
      norm_num [ Nat.add_mod, Nat.mod_eq_zero_of_dvd h_factorial ];
      rw [ Nat.mod_eq_of_lt ( by nlinarith [ hp_prime.two_le ] ) ];
    -- Therefore, for odd primes p, A3 occupies at most 2p < p^2 residue classes modulo p^2 (the values for j < 2p, plus the value 1).
    have h_odd_primes_bound : Finset.card (Finset.image (fun j => (Nat.factorial j + 1) % p^2) (Finset.range (2 * p)) ∪ {1}) < p^2 := by
      refine' lt_of_le_of_lt ( Finset.card_union_le _ _ ) _;
      exact lt_of_le_of_lt ( add_le_add ( Finset.card_image_le ) le_rfl ) ( by norm_num; nlinarith [ hp_prime.two_le, show p > 2 from lt_of_le_of_ne hp_prime.two_le ( Ne.symm <| by aesop_cat ) ] );
    -- Therefore, there exists a residue class modulo p^2 that A3 avoids.
    obtain ⟨b, hb⟩ : ∃ b < p^2, b ∉ Finset.image (fun j => (Nat.factorial j + 1) % p^2) (Finset.range (2 * p)) ∪ {1} := by
      contrapose! h_odd_primes_bound;
      exact le_trans ( by norm_num ) ( Finset.card_le_card ( show Finset.range ( p ^ 2 ) ⊆ Finset.image ( fun j => ( j ! + 1 ) % p ^ 2 ) ( Finset.range ( 2 * p ) ) ∪ { 1 } from fun x hx => h_odd_primes_bound x ( Finset.mem_range.mp hx ) ) );
    use b;
    simp_all +decide [ A3 ];
    grind +ring;
  · cases hp_prime.eq_two_or_odd <;> simp_all +decide;
    use 0; norm_num [ A3 ];
    intro a x hx ha; subst ha; rcases x with ( _ | _ | _ | x ) <;> norm_num [ Nat.factorial_succ ] at *;
    norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_mod ] ; have := Nat.mod_lt x zero_lt_four ; interval_cases x % 4 <;> have := Nat.mod_lt ( x ! ) zero_lt_four <;> interval_cases x ! % 4 <;> trivial;

/-
The sequence A4 is admissible.
-/
lemma A4_admissible : Admissible A4 := by
  intro p hp; by_cases h_cases : p % 2 = 1;
  · -- For odd primes p, the elements j! - 1 are congruent to -1 mod p^2 for all j >= 2p.
    have h_odd_primes : ∀ j ≥ 2 * p, (Nat.factorial j - 1) % p^2 = (p^2 - 1) % p^2 := by
      intro j hj
      have h_div : p^2 ∣ Nat.factorial j := by
        have h_div : p^2 ∣ Nat.factorial (2 * p) := by
          -- Since $p$ is prime and $p \geq 3$, we know that $p^2 \mid (2p)!$.
          have h_div : p^2 ∣ Nat.factorial p * Nat.factorial p := by
            simpa only [ sq ] using mul_dvd_mul ( Nat.dvd_factorial hp.pos le_rfl ) ( Nat.dvd_factorial hp.pos le_rfl );
          exact dvd_trans h_div ( Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| by rw [ two_mul ] );
        exact dvd_trans h_div ( Nat.factorial_dvd_factorial hj );
      refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_;
      obtain ⟨ k, hk ⟩ := h_div; use k - 1; rw [ Nat.cast_sub <| by nlinarith [ Nat.factorial_pos j, hp.two_le ], Nat.cast_sub <| by nlinarith [ hp.two_le ] ] ; push_cast ; linarith;
    -- Thus, for odd p, A4 occupies at most 2p residue classes modulo p^2 (the values for j < 2p, plus the value -1).
    have h_odd_primes_classes : Finset.image (fun j => (Nat.factorial j - 1) % p^2) (Finset.range (2 * p)) ∪ {p^2 - 1} ⊂ Finset.range (p^2) := by
      refine' ⟨ _, _ ⟩;
      · exact Finset.union_subset ( Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr <| Nat.mod_lt _ <| pow_pos hp.pos _ ) ( Finset.singleton_subset_iff.mpr <| Finset.mem_range.mpr <| Nat.sub_lt ( pow_pos hp.pos _ ) zero_lt_one );
      · intro h; have := Finset.card_le_card h; simp_all +decide [ Finset.subset_iff ] ;
        refine' this.not_gt ( lt_of_le_of_lt ( Finset.card_insert_le _ _ ) _ );
        refine' lt_of_le_of_lt ( add_le_add_right ( Finset.card_image_le ) _ ) _ ; norm_num;
        rcases p with ( _ | _ | _ | p ) <;> norm_num at * ; nlinarith;
    obtain ⟨ b, hb ⟩ := Finset.exists_of_ssubset h_odd_primes_classes;
    use b;
    simp +zetaDelta at *;
    exact ⟨ hb.1, fun a ha => by rcases ha with ⟨ j, hj, rfl ⟩ ; exact fun h => hb.2.2 j ( not_le.mp fun h' => by have := h_odd_primes j h'; omega ) <| by simpa [ Nat.factorial_pos ] using h ⟩;
  · cases hp.eq_two_or_odd <;> simp_all +decide;
    use 0; norm_num; intro a ha; rcases ha with ⟨ j, hj, rfl ⟩ ; rcases j with ( _ | _ | j ) <;> norm_num [ Nat.factorial_succ, Nat.add_mod, Nat.mul_mod ] at *;
    zify;
    rw [ Int.ofNat_sub ( Nat.one_le_iff_ne_zero.mpr <| by positivity ) ] ; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ];
    have := Int.emod_nonneg j four_ne_zero; have := Int.emod_lt_of_pos j four_pos; interval_cases ( j % 4 : ℤ ) <;> ( have := Int.emod_nonneg ( j ! ) four_ne_zero; have := Int.emod_lt_of_pos ( j ! ) four_pos; interval_cases ( j ! % 4 : ℤ ) <;> trivial; )

/-
A1 is infinite.
-/
lemma A1_infinite : A1.Infinite := by
  exact Set.infinite_of_injective_forall_mem ( fun i j hij => by simpa using hij ) fun j => ⟨ j + 1, by linarith, rfl ⟩

/-
The n-th element of A1 is 2^(n+1) + 1.
-/
lemma A1_nth (n : ℕ) : Nat.nth (· ∈ A1) n = 2^(n + 1) + 1 := by
  induction' n with n ih;
  · norm_num [ Nat.nth_zero, A1 ];
    exact le_antisymm ( Nat.sInf_le ⟨ 1, by norm_num, rfl ⟩ ) ( le_csInf ⟨ 3, ⟨ 1, by norm_num, rfl ⟩ ⟩ fun n hn => by obtain ⟨ j, hj, rfl ⟩ := hn; exact Nat.succ_le_succ ( Nat.succ_le_of_lt ( lt_of_lt_of_le ( by norm_num ) ( Nat.pow_le_pow_right ( by norm_num ) hj ) ) ) );
  · rw [ Nat.nth_eq_sInf ];
    refine' le_antisymm _ _;
    · refine' Nat.sInf_le ⟨ _, _ ⟩;
      · exact ⟨ n + 1 + 1, by norm_num, rfl ⟩;
      · intro k hk; exact lt_of_le_of_lt ( Nat.nth_monotone ( show { x | x ∈ A1 }.Infinite from A1_infinite ) ( Nat.le_of_lt_succ hk ) ) ( by rw [ ih ] ; exact Nat.succ_lt_succ ( pow_lt_pow_right₀ ( by decide ) ( by linarith ) ) ) ;
    · refine' le_csInf _ _ <;> norm_num;
      · refine' ⟨ 2 ^ ( n + 2 ) + 1, _, _ ⟩;
        · exact ⟨ n + 2, by norm_num, rfl ⟩;
        · intro k hk; exact lt_of_le_of_lt ( Nat.nth_monotone ( show { x | x ∈ A1 }.Infinite from A1_infinite ) ( Nat.le_of_lt_succ hk ) ) ( by rw [ ih ] ; exact by linarith [ pow_lt_pow_right₀ ( by decide : 1 < 2 ) ( by linarith : n + 1 < n + 2 ) ] ) ;
      · intro b hb h; contrapose! h;
        use n;
        obtain ⟨ j, hj₁, hj₂ ⟩ := hb;
        rcases j with ( _ | j ) <;> simp_all +decide [ pow_succ' ];
        rw [ ← pow_succ' ] at h ; exact le_of_not_gt fun h' => h.not_ge <| Nat.pow_le_pow_right ( by decide ) <| Nat.succ_le_of_lt <| Nat.lt_of_not_ge fun h'' => by linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) h'' ] ;

/-
A2 is infinite.
-/
lemma A2_infinite : A2.Infinite := by
  -- The function $j \mapsto 2^j - 1$ is injective, and the domain $\{1, 2, \ldots\}$ is infinite.
  have h_inj : Function.Injective (fun j : ℕ => 2^(j + 1) - 1) := by
    exact fun a b h => by zify at h; norm_num at h; linarith;
  exact Set.infinite_of_injective_forall_mem h_inj fun j => ⟨ j + 1, by norm_num, rfl ⟩

/-
The n-th element of A2 is 2^(n+1) - 1.
-/
lemma A2_nth (n : ℕ) : Nat.nth (· ∈ A2) n = 2^(n + 1) - 1 := by
  induction' n with n ih <;> norm_num [ Nat.succ_eq_add_one, Nat.nth_zero ];
  · exact le_antisymm ( csInf_le ⟨ 0, fun x hx => by rcases hx with ⟨ j, hj, rfl ⟩ ; exact Nat.zero_le _ ⟩ ⟨ 1, by norm_num, by norm_num ⟩ ) ( le_csInf ⟨ 1, ⟨ 1, by norm_num, by norm_num ⟩ ⟩ fun x hx => by rcases hx with ⟨ j, hj, rfl ⟩ ; exact Nat.le_sub_one_of_lt ( one_lt_pow₀ one_lt_two ( by linarith ) ) );
  · -- By definition of $A2$, we know that $2^{n+2} - 1$ is the smallest element in $A2$ greater than $2^{n+1} - 1$.
    have h_next : ∀ m ∈ A2, m > 2^(n+1) - 1 → m ≥ 2^(n+2) - 1 := by
      intros m hm hm_gt
      obtain ⟨j, hj⟩ : ∃ j : ℕ, m = 2^j - 1 ∧ j ≥ 1 := by
        cases hm ; aesop;
      exact hj.1.symm ▸ Nat.sub_le_sub_right ( pow_le_pow_right₀ ( by decide ) ( Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => hm_gt.not_ge <| by rw [ hj.1 ] ; exact Nat.sub_le_sub_right ( pow_le_pow_right₀ ( by decide ) h ) _ ) ) ) _;
    rw [ Nat.nth_eq_sInf ];
    refine' le_antisymm _ _;
    · refine' Nat.sInf_le ⟨ _, _ ⟩;
      · exact ⟨ n + 2, by norm_num, rfl ⟩;
      · intro k hk;
        refine' lt_of_le_of_lt ( Nat.nth_monotone _ ( Nat.le_of_lt_succ hk ) ) _;
        · exact A2_infinite;
        · exact ih.symm ▸ by rw [ tsub_lt_tsub_iff_right ( Nat.one_le_pow _ _ ( by decide ) ) ] ; ring_nf; norm_num;
    · refine' le_csInf _ _;
      · refine' ⟨ 2 ^ ( n + 2 ) - 1, _, _ ⟩;
        · exact ⟨ n + 2, by norm_num, rfl ⟩;
        · intro k hk;
          refine' lt_of_le_of_lt ( Nat.nth_monotone _ ( Nat.le_of_lt_succ hk ) ) _;
          · exact A2_infinite;
          · rw [ ih ];
            rw [ tsub_lt_tsub_iff_right ( Nat.one_le_pow _ _ ( by decide ) ) ] ; ring_nf ; norm_num;
      · exact fun x hx => h_next x hx.1 ( by linarith [ hx.2 n ( Nat.lt_succ_self n ) ] )

/-
A3 is infinite.
-/
lemma A3_infinite : A3.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_;
  exact fun a => ⟨ _, ⟨ a + 1, Nat.succ_pos _, rfl ⟩, by linarith [ Nat.self_le_factorial ( a + 1 ) ] ⟩

/-
The n-th element of A3 is (n+1)! + 1.
-/
lemma A3_nth (n : ℕ) : Nat.nth (· ∈ A3) n = Nat.factorial (n + 1) + 1 := by
  induction' n with n ih;
  · norm_num [ A3 ];
    rw [ Nat.nth_zero ];
    exact le_antisymm ( Nat.sInf_le ⟨ 1, by decide, rfl ⟩ ) ( le_csInf ⟨ 2, ⟨ 1, by decide, rfl ⟩ ⟩ fun n hn => by obtain ⟨ j, hj, rfl ⟩ := hn; linarith [ Nat.self_le_factorial j ] );
  · -- The (n+1)-th element of A3 is the smallest element in A3 that is greater than (n+1)! + 1.
    have h_next : Nat.nth (fun x => x ∈ A3) (n + 1) = sInf {x ∈ A3 | x > (n + 1)! + 1} := by
      rw [ ← ih, Nat.nth_eq_sInf ];
      congr with x;
      constructor <;> intro h <;> simp_all +decide;
      · exact ih ▸ h.2 _ ( Nat.lt_succ_self _ );
      · intro k hk; exact lt_of_le_of_lt ( Nat.nth_monotone ( show { x | x ∈ A3 }.Infinite from by exact Set.infinite_of_forall_exists_gt fun m => ⟨ ( m + 1 ) ! + 1, ⟨ m + 1, by linarith, rfl ⟩, by linarith [ Nat.self_le_factorial ( m + 1 ) ] ⟩ ) ( Nat.le_of_lt_succ hk ) ) ( lt_of_le_of_lt ( ih.le ) h.2 ) ;
    rw [ h_next, IsLeast.csInf_eq ];
    constructor;
    · exact ⟨ ⟨ n + 2, by norm_num, by norm_num [ Nat.factorial_succ ] ⟩, by gcongr ; linarith ⟩;
    · rintro x ⟨ hx₁, hx₂ ⟩;
      obtain ⟨ j, hj₁, rfl ⟩ := hx₁;
      exact Nat.succ_le_succ ( Nat.factorial_le ( Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => hx₂.not_ge <| Nat.succ_le_succ <| Nat.factorial_le h ) ) )

/-
The sequence A1 satisfies the growth condition for any constant C.
-/
lemma A1_growth (C : ℝ) : GrowthCondition A1 C := by
  -- We need to show that for infinitely many j, a_j ≥ exp(C j / log j).
  have h_exp_growth : ∀ᶠ j in Filter.atTop, (2^(j + 1) + 1 : ℝ) ≥ Real.exp (C * (j + 1) / Real.log (j + 1)) := by
    -- We want to show that for sufficiently large $j$, $\exp(j \log 2) \geq \exp(C j / \log j)$.
    have h_exp_growth : ∀ᶠ j in Filter.atTop, Real.exp ((j + 1) * Real.log 2) ≥ Real.exp (C * (j + 1) / Real.log (j + 1)) := by
      -- We can divide both sides by $(j + 1)$ (which is positive for $j \geq 1$) to get $C / \log (j + 1) \leq \log 2$.
      suffices h_div : ∀ᶠ j in Filter.atTop, C / Real.log (j + 1) ≤ Real.log 2 by
        filter_upwards [ h_div, Filter.eventually_gt_atTop 0 ] with j hj₁ hj₂ using Real.exp_le_exp.mpr ( by convert mul_le_mul_of_nonneg_left hj₁ ( add_nonneg hj₂.le zero_le_one ) using 1 ; ring );
      have h_div : Filter.Tendsto (fun j : ℝ => C / Real.log (j + 1)) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp <| Filter.tendsto_id.atTop_add tendsto_const_nhds );
      exact h_div.eventually ( ge_mem_nhds <| by positivity );
    filter_upwards [ h_exp_growth, Filter.eventually_gt_atTop 0 ] with j hj hj' using le_trans hj ( by rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf; norm_num );
  rw [ Filter.eventually_atTop ] at *;
  obtain ⟨ a, ha ⟩ := h_exp_growth;
  -- By definition of $A1$, we know that $Nat.nth (· ∈ A1) n = 2^(n + 1) + 1$ for all $n$.
  have h_nth_A1 : ∀ n : ℕ, Nat.nth (· ∈ A1) n = 2^(n + 1) + 1 := by
    exact fun n => A1_nth n;
  refine' Filter.frequently_atTop.mpr fun n => _;
  refine' ⟨ n + ⌈a⌉₊ + 1, _, _ ⟩ <;> norm_num [ h_nth_A1 ];
  · linarith;
  · exact_mod_cast ha ( n + ⌈a⌉₊ ) ( by linarith [ Nat.le_ceil a ] )

/-
The sequence A2 satisfies the growth condition for any constant C.
-/
lemma A2_growth (C : ℝ) : GrowthCondition A2 C := by
  -- We need to show that for infinitely many $j$, $a_j \geq \exp(Cj/\log j)$.
  suffices h_inf : ∀ᶠ j in Filter.atTop, (Nat.nth (· ∈ A2) (j - 1) : ℝ) ≥ Real.exp (C * j / Real.log j) by
    exact Filter.Eventually.frequently h_inf;
  -- We'll use that $2^j - 1 \geq \exp(Cj / \log j)$ for sufficiently large $j$.
  have h_exp_growth : ∀ᶠ j in Filter.atTop, (2 : ℝ) ^ j - 1 ≥ Real.exp (C * j / Real.log j) := by
    -- We'll use that exponential functions grow faster than polynomial functions.
    have h_exp_growth : Filter.Tendsto (fun j : ℝ => Real.exp (C * j / Real.log j) / 2^j) Filter.atTop (nhds 0) := by
      -- We can rewrite the limit expression using properties of exponents: $\frac{e^{C \cdot \frac{j}{\log j}}}{2^j} = e^{C \cdot \frac{j}{\log j} - j \log 2}$.
      suffices h_exp : Filter.Tendsto (fun j => Real.exp (C * j / Real.log j - j * Real.log 2)) Filter.atTop (nhds 0) by
        convert h_exp using 2 ; norm_num [ Real.rpow_def_of_pos, mul_comm, Real.exp_sub ];
      -- We can factor out $j$ in the exponent: $j \left( \frac{C}{\log j} - \log 2 \right)$.
      suffices h_factor : Filter.Tendsto (fun j => j * (C / Real.log j - Real.log 2)) Filter.atTop Filter.atBot by
        exact Real.tendsto_exp_atBot.comp ( h_factor.congr fun x => by ring );
      -- We can use the fact that $C / \log j - \log 2$ tends to $-\log 2$ as $j \to \infty$.
      have h_log : Filter.Tendsto (fun j : ℝ => C / Real.log j - Real.log 2) Filter.atTop (nhds (-Real.log 2)) := by
        exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) tendsto_const_nhds ) ( by norm_num );
      apply_rules [ Filter.Tendsto.atTop_mul_neg, h_log ];
      · norm_num [ Real.log_pos ];
      · exact Filter.tendsto_id;
    filter_upwards [ h_exp_growth.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num ), Filter.eventually_gt_atTop 1 ] with j hj₁ hj₂ using by rw [ div_lt_iff₀ <| by positivity ] at hj₁; nlinarith [ Real.rpow_le_rpow_of_exponent_le ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hj₂.le ] ;
  have h_nth_A2 : ∀ j : ℕ, j > 0 → (Nat.nth (· ∈ A2) (j - 1) : ℝ) = (2 : ℝ) ^ j - 1 := by
    intro j hj
    have h_def : Nat.nth (· ∈ A2) (j - 1) = 2 ^ j - 1 := by
      convert A2_nth ( j - 1 ) using 1;
      rw [ Nat.sub_add_cancel hj ]
    norm_num [ h_def ];
  filter_upwards [ Filter.eventually_gt_atTop 0, h_exp_growth.natCast_atTop ] with j hj₁ hj₂ using by simpa [ h_nth_A2 j hj₁ ] using hj₂;

/-
The sequence A3 satisfies the growth condition for any constant C.
-/
lemma A3_growth (C : ℝ) : GrowthCondition A3 C := by
  -- We need to show that for infinitely many j, a_j ≥ exp(C j / log j).
  have h_exp_growth : ∀ᶠ j in Filter.atTop, (Nat.nth (· ∈ A3) (j - 1) : ℝ) ≥ Real.exp (C * j / Real.log j) := by
    -- We'll use that $j! \geq e^{j \log j - j}$ for all $j \geq 1$.
    have h_factorial_bound : ∀ j : ℕ, j ≥ 1 → (Nat.factorial j : ℝ) ≥ Real.exp (j * Real.log j - j) := by
      field_simp;
      intro j hj; rw [ mul_sub, mul_one, Real.exp_sub, Real.exp_nat_mul, Real.exp_log ( by positivity ) ] ;
      rw [ div_le_iff₀ ( Real.exp_pos _ ) ];
      rw [ ← div_le_iff₀' ( by positivity ) ] ; rw [ Real.exp_eq_exp_ℝ ] ; norm_num [ NormedSpace.exp_eq_tsum_div ] ; exact Summable.le_tsum ( show Summable _ from Real.summable_pow_div_factorial _ ) j ( fun _ _ => by positivity ) ;
    -- By definition of $A3$, we have $Nat.nth (· ∈ A3) (j - 1) = Nat.factorial j + 1$.
    have h_nth_A3 : ∀ j : ℕ, j ≥ 1 → Nat.nth (· ∈ A3) (j - 1) = Nat.factorial j + 1 := by
      intro j hj; convert A3_nth ( j - 1 ) using 1; rcases j with ( _ | j ) <;> aesop;
    -- We'll use that $j \log j - j \geq C j / \log j$ for sufficiently large $j$.
    have h_log_bound : ∀ᶠ j in Filter.atTop, j * Real.log j - j ≥ C * j / Real.log j := by
      -- We can divide both sides by $j$ to get $\log j - 1 \geq \frac{C}{\log j}$.
      suffices h_div : ∀ᶠ j in Filter.atTop, Real.log j - 1 ≥ C / Real.log j by
        filter_upwards [ h_div, Filter.eventually_gt_atTop 1 ] with j hj₁ hj₂ using by ring_nf at *; nlinarith;
      filter_upwards [ Filter.eventually_gt_atTop ( Real.exp ( |C| + 1 ) ) ] with j hj using by rw [ ge_iff_le, div_le_iff₀ ] <;> cases abs_cases C <;> nlinarith [ Real.log_exp ( |C| + 1 ), Real.log_lt_log ( by positivity ) hj ] ;
    filter_upwards [ Filter.eventually_ge_atTop 1, h_log_bound.natCast_atTop ] with j hj₁ hj₂ using by simpa [ h_nth_A3 j hj₁ ] using le_add_of_le_of_nonneg ( le_trans ( Real.exp_le_exp.mpr <| by simpa using hj₂ ) ( h_factorial_bound j hj₁ ) ) zero_le_one;
  exact h_exp_growth.frequently

/-
A4 is infinite.
-/
lemma A4_infinite : A4.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_;
  exact fun n => ⟨ _, ⟨ n + 3, by linarith, rfl ⟩, lt_tsub_iff_right.mpr <| by linarith [ Nat.self_le_factorial ( n + 3 ) ] ⟩

/-
The n-th element of A4 is (n+2)! - 1.
-/
lemma A4_nth (n : ℕ) : Nat.nth (· ∈ A4) n = Nat.factorial (n + 2) - 1 := by
  -- By definition of $A4$, we know that every element in $A4$ is of the form $j! - 1$ for some $j \geq 2$.
  have hA4_def : ∀ x, x ∈ A4 ↔ ∃ j ≥ 2, x = Nat.factorial j - 1 := by
    unfold A4; aesop;
  induction' n with n ih <;> simp_all +decide [ Nat.nth_zero ];
  · exact le_antisymm ( Nat.sInf_le ⟨ 2, by decide, rfl ⟩ ) ( le_csInf ⟨ 1, ⟨ 2, by decide, rfl ⟩ ⟩ fun x hx => by obtain ⟨ j, hj, rfl ⟩ := hx; exact Nat.le_sub_one_of_lt ( by linarith [ Nat.self_le_factorial j ] ) );
  · rw [ Nat.nth_eq_sInf ];
    refine' le_antisymm _ _;
    · refine' Nat.sInf_le ⟨ ⟨ n + 3, by linarith, rfl ⟩, fun k hk => _ ⟩;
      refine' lt_of_le_of_lt ( Nat.nth_monotone _ ( Nat.le_of_lt_succ hk ) ) _;
      · exact Set.infinite_of_forall_exists_gt fun x => ⟨ _, ⟨ x + 2, by linarith, rfl ⟩, lt_tsub_iff_right.mpr <| by nlinarith [ Nat.self_le_factorial ( x + 2 ) ] ⟩;
      · exact ih.symm ▸ by rw [ tsub_lt_tsub_iff_right ( Nat.one_le_iff_ne_zero.mpr <| by positivity ) ] ; gcongr ; linarith;
    · refine' le_csInf _ _;
      · refine' ⟨ _, ⟨ ⟨ n + 3, by linarith, rfl ⟩, fun k hk => _ ⟩ ⟩;
        refine' lt_of_le_of_lt ( Nat.nth_monotone _ ( Nat.le_of_lt_succ hk ) ) _;
        · exact Set.infinite_of_forall_exists_gt fun x => ⟨ _, ⟨ x + 2, by linarith, rfl ⟩, lt_tsub_iff_right.mpr <| by nlinarith [ Nat.self_le_factorial ( x + 2 ) ] ⟩;
        · exact ih.symm ▸ by rw [ tsub_lt_tsub_iff_right ( Nat.one_le_iff_ne_zero.mpr <| by positivity ) ] ; gcongr ; linarith;
      · intro b hb; obtain ⟨ ⟨ j, hj₁, rfl ⟩, hb' ⟩ := hb; have := hb' n; simp_all +decide ;
        contrapose! this;
        rw [ tsub_le_tsub_iff_right ( Nat.one_le_iff_ne_zero.mpr <| Nat.factorial_ne_zero _ ) ];
        exact Nat.factorial_le ( Nat.le_of_not_lt fun h => by linarith [ Nat.sub_add_cancel ( Nat.factorial_pos j ), Nat.factorial_le h ] )

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
          simp_all +decide;
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
    (Finset.filter
        (fun (p : ℕ) =>
          0.1 * Real.log x < (p : ℝ)
          ∧ (p : ℝ) ≤ Real.sqrt (2 * x)
          ∧ Nat.Prime p)
        (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1))
    ).card
      * ((W_val x : ℝ) / x)
    ≤ 1 / (Real.log x * Real.log (Real.log x)) := by
    -- Let's simplify the expression using the bounds we have.
    suffices h_simp : ∀ᶠ x in Filter.atTop, (Finset.card (Finset.filter (fun p : ℕ => 0.1 * Real.log x < p ∧ p ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1))) : ℝ) ≤ Real.sqrt (2 * x) by
      -- By combining the results from h_simp and h_bound, we can conclude the proof.
      have h_final : ∀ᶠ x in Filter.atTop, Real.sqrt (2 * x) * (Real.exp (0.25 * Real.log x) / x) ≤ 1 / (Real.log x * Real.log (Real.log x)) := by
        -- Simplify the expression inside the limit.
        suffices h_simplify : Filter.Tendsto (fun x : ℝ => Real.sqrt (2 * x) * (Real.exp (0.25 * Real.log x) / x) * (Real.log x * Real.log (Real.log x))) Filter.atTop (nhds 0) by
          filter_upwards [ h_simplify.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ), Filter.eventually_gt_atTop ( Real.exp ( Real.exp 1 ) ) ] with x hx₁ hx₂ hx₃ hx₄ using by rw [ le_div_iff₀ ( mul_pos ( Real.log_pos hx₂ ) ( Real.log_pos ( show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith ) ) ) ] ; linarith;
        -- Simplify the expression inside the limit further.
        suffices h_simplify' : Filter.Tendsto (fun x : ℝ => Real.sqrt 2 * Real.exp (-0.25 * Real.log x) * (Real.log x * Real.log (Real.log x))) Filter.atTop (nhds 0) by
          refine h_simplify'.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx ; norm_num [ hx.le, Real.sqrt_mul, Real.exp_neg, Real.exp_log hx ] ; ring_nf;
          norm_num [ Real.exp_neg, Real.exp_mul, Real.exp_log hx, hx.le, hx.ne' ] ; ring_nf ; norm_num [ hx.ne' ];
          norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le, ← Real.rpow_add hx, mul_assoc, hx.ne' ];
          exact Or.inl ( by rw [ ← Real.rpow_neg_one, ← Real.rpow_add hx ] ; norm_num );
        -- Let $y = \log x$, therefore the expression becomes $\sqrt{2} \cdot e^{-0.25y} \cdot y \cdot \log y$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => Real.sqrt 2 * Real.exp (-0.25 * y) * y * Real.log y) Filter.atTop (nhds 0) by
          convert h_log.comp Real.tendsto_log_atTop using 2 ; norm_num ; ring;
        -- We can factor out $y$ and use the fact that $\exp(-0.25y) \cdot y \to 0$ as $y \to \infty$.
        suffices h_factor : Filter.Tendsto (fun y : ℝ => Real.exp (-0.25 * y) * y^2) Filter.atTop (nhds 0) by
          have h_log : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) := by
            -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
            suffices h_log_z : Filter.Tendsto (fun z : ℝ => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
              exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
          convert h_factor.const_mul ( Real.sqrt 2 ) |> Filter.Tendsto.mul <| h_log using 2 <;> ring_nf;
          by_cases h : ‹ℝ› = 0 <;> simp +decide [ sq, mul_assoc, mul_comm, mul_left_comm, h ];
        -- Let $z = 0.25y$, therefore the expression becomes $\exp(-z) \cdot (4z)^2$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => Real.exp (-z) * (4 * z)^2) Filter.atTop (nhds 0) by
          convert h_z.comp ( Filter.tendsto_id.const_mul_atTop ( show 0 < ( 0.25 : ℝ ) by norm_num ) ) using 2 ; norm_num ; ring;
        have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
        convert this.const_mul 16 using 2 <;> ring;
      filter_upwards [ h_simp, h_final, Filter.eventually_gt_atTop 1, W_bound h ] with x hx₁ hx₂ hx₃ hx₄;
      refine le_trans ?_ hx₂;
      gcongr;
    refine' Filter.eventually_atTop.mpr ⟨ 4, fun x hx => _ ⟩ ; norm_num [ Nat.floor_le ] at *;
    refine' le_trans _ ( Nat.floor_le <| by positivity );
    exact_mod_cast le_trans ( Finset.card_le_card <| show Finset.filter ( fun p : ℕ => 1 / 10 * Real.log x < ( p : ℝ ) ∧ ( p : ℝ ) ≤ Real.sqrt 2 * Real.sqrt x ∧ Nat.Prime p ) ( Finset.range ( ⌊Real.sqrt 2 * Real.sqrt x⌋₊ + 1 ) ) ⊆ Finset.Ico 1 ( ⌊Real.sqrt 2 * Real.sqrt x⌋₊ + 1 ) from fun p hp => Finset.mem_Ico.mpr ⟨ Nat.Prime.pos <| by aesop, Finset.mem_range.mp <| Finset.mem_filter.mp hp |>.1 ⟩ ) <| by simp +arith +decide;

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
failure_prob_sum_2(x) is the sum of (1/p^2 + 2W/x) for primes p in (0.1 log x, sqrt(2x)].
-/
def failure_prob_sum_2 (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1)), (1 / (p : ℝ)^2 + 2 * (W_val x : ℝ) / x)

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
              simp_all +decide [Nat.coprime_prod_left_iff];
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
            convert h_log_approx.inv₀ ( by positivity ) |> Filter.Tendsto.const_mul ( 1 / C ) using 2 <;> ring_nf;
            by_cases h : ‹ℝ› = 0 <;> aesop;
          convert h_bound_func_approx using 2 ; unfold bound_func ; norm_num ; ring_nf;
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
There exists a constant C such that for sufficiently large j, if x >= exp(C j / log j), then j * C_freq * failure_prob_sum_2(x) < 1.
-/
lemma prob_condition_of_growth_v2 (h : SieveAssumptions) :
  ∃ C > 0, ∀ᶠ j in Filter.atTop,
    ∀ x, x ≥ Real.exp (C * j / Real.log j) →
    (j : ℝ) * C_freq * failure_prob_sum_2 x < 1 := by
      apply_mod_cast prob_condition_of_growth h

/-
For sufficiently large x, the length of the interval [ceil(x/2), floor(x)] is at least W_val(x).
-/
lemma length_condition (h : SieveAssumptions) :
  ∀ᶠ x in Filter.atTop, (Nat.floor x - Nat.ceil (x / 2) + 1 : ℝ) ≥ (W_val x : ℝ) := by
    -- For large x, we have x/2 - 1 ≥ x^0.25.
    have h_x_half_minus_one_ge_x_pow : ∀ᶠ x in Filter.atTop, (x / 2 - 1 : ℝ) ≥ Real.exp (0.25 * Real.log x) := by
      -- We can divide both sides by $x^{0.25}$ to get $x^{0.75}/2 - 1/x^{0.25} \geq 1$, which simplifies to $x^{0.75}/2 \geq 1 + 1/x^{0.25}$.
      suffices h_div : ∀ᶠ x in Filter.atTop, (x : ℝ) ^ (3 / 4 : ℝ) / 2 ≥ 1 + 1 / (x : ℝ) ^ (1 / 4 : ℝ) by
        filter_upwards [ h_div, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
        rw [ show ( 3 / 4 : ℝ ) = 1 - 1 / 4 by norm_num, Real.rpow_sub ] at hx₁ <;> norm_num at * <;> try linarith;
        rw [ show ( 1 / 4 : ℝ ) * Real.log x = Real.log ( x ^ ( 1 / 4 : ℝ ) ) by rw [ Real.log_rpow ( by positivity ) ] ] ; rw [ Real.exp_log ( by positivity ) ] ; ring_nf at * ; nlinarith [ inv_mul_cancel₀ ( ne_of_gt ( Real.rpow_pos_of_pos ( zero_lt_one.trans hx₂ ) ( 1 / 4 : ℝ ) ) ), Real.rpow_pos_of_pos ( zero_lt_one.trans hx₂ ) ( 1 / 4 : ℝ ) ];
      -- As $x$ tends to infinity, $x^{3/4}/2$ grows without bound, while $1 + 1/x^{1/4}$ tends to $1$.
      have h_bound : Filter.Tendsto (fun x : ℝ => x ^ (3 / 4 : ℝ) / 2 - 1 - 1 / x ^ (1 / 4 : ℝ)) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.atTop_add ( Filter.Tendsto.atTop_add ( Filter.Tendsto.atTop_div_const ( by norm_num ) ( tendsto_rpow_atTop ( by norm_num ) ) ) tendsto_const_nhds ) ( Filter.Tendsto.neg ( tendsto_const_nhds.div_atTop ( tendsto_rpow_atTop ( by norm_num ) ) ) );
      filter_upwards [ h_bound.eventually_gt_atTop 0 ] with x hx using by linarith;
    filter_upwards [ h_x_half_minus_one_ge_x_pow, W_bound h, Filter.eventually_gt_atTop 2 ] with x hx₁ hx₂ hx₃;
    linarith [ Nat.le_ceil ( x / 2 ), Nat.ceil_lt_add_one ( show 0 ≤ x / 2 by positivity ), Nat.lt_floor_add_one x ]

/-
If L >= x/2, then W/L <= 2W/x.
-/
lemma W_div_L_le (x L W : ℝ) (hx : x > 0) (hL : L ≥ x / 2) (hW : W ≥ 0) : W / L ≤ 2 * W / x := by
  rw [ div_le_div_iff₀ ] <;> nlinarith

/-
If L >= x/2 and W = W_val(x), then the sum of (1/p^2 + W/L) is bounded by failure_prob_sum_2(x).
-/
lemma sum_bound_inequality (x : ℝ) (hx : x > 0) (L : ℝ) (hL : L ≥ x / 2) (W : ℝ) (hW_eq : W = W_val x) :
    let P := Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1))
    ∑ p ∈ P, (1 / (p : ℝ)^2 + W / L) ≤ failure_prob_sum_2 x := by
      refine Finset.sum_le_sum fun p hp => ?_;
      have := W_div_L_le x L ( ↑ ( W_val x ) ) hx hL;
      aesop

/-
Any interval of length at least m contains a number congruent to k modulo m.
-/
lemma exists_mod_in_interval (u L m k : ℕ) (hL : L ≥ m) (hm : m > 0) :
    ∃ n ∈ Finset.Icc u (u + L - 1), n ≡ k [MOD m] := by
      -- By the pigeonhole principle, since there are m consecutive integers and m possible residues modulo m, one of these integers must be congruent to k modulo m.
      have h_pigeonhole : ∃ n ∈ Finset.range m, (u + n) ≡ k [MOD m] := by
        use ( k + m - u % m ) % m;
        norm_num [ Nat.ModEq, Nat.mod_lt _ hm ];
        simp +decide [ ← ZMod.natCast_eq_natCast_iff', Nat.cast_sub ( show u % m ≤ k + m from le_trans ( Nat.le_of_lt <| Nat.mod_lt _ hm ) <| Nat.le_add_left _ _ ) ];
      exact ⟨ u + h_pigeonhole.choose, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_range.mp h_pigeonhole.choose_spec.1 ], Nat.le_sub_one_of_lt ( by linarith [ Finset.mem_range.mp h_pigeonhole.choose_spec.1 ] ) ⟩, h_pigeonhole.choose_spec.2 ⟩

/-
The set of candidate integers is non-empty if the interval length is at least W.
-/
def CandidateSet (x_nat : ℕ) (W : ℕ) (b : ℕ) : Finset ℕ :=
  (Finset.Icc (Nat.ceil ((x_nat : ℝ) / 2)) (Nat.floor (x_nat : ℝ))).filter (fun n => (n + b) % W = 0)

lemma CandidateSet_nonempty (x_nat : ℕ) (W : ℕ) (b : ℕ)
    (hL : Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1 ≥ W) (hW : W > 0) :
    (CandidateSet x_nat W b).Nonempty := by
      convert exists_mod_in_interval ( Nat.ceil ( x_nat / 2 : ℝ ) ) ( Nat.floor ( x_nat : ℝ ) - Nat.ceil ( x_nat / 2 : ℝ ) + 1 ) W ( W - b % W ) ?_ ?_ using 1;
      · unfold CandidateSet;
        constructor <;> intro h;
        · obtain ⟨ n, hn ⟩ := h; use n; simp_all +decide [Nat.ModEq] ;
          refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_;
          rw [ Int.ofNat_sub ( Nat.le_of_lt <| Nat.mod_lt _ hW ) ] ; norm_num ; obtain ⟨ k, hk ⟩ := Nat.modEq_zero_iff_dvd.mp hn.2 ; exact ⟨ k - ( b / W + 1 ), by linarith [ Nat.mod_add_div b W ] ⟩ ;
        · obtain ⟨ n, hn₁, hn₂ ⟩ := h; use n; simp_all +decide [Nat.ModEq] ;
          simp +decide [ Nat.add_mod, hn₂ ];
          simp +decide [ Nat.add_comm, Nat.add_sub_of_le ( Nat.mod_lt b hW |> Nat.le_of_lt ) ];
      · convert hL using 1;
      · assumption

/-
The set of integers n in the candidate set such that n+a is divisible by p^2.
-/
def BadSet (x_nat : ℕ) (W : ℕ) (b : ℕ) (a : ℕ) (p : ℕ) : Finset ℕ :=
  (CandidateSet x_nat W b).filter (fun n => (n + a) % p^2 = 0)

/-
The set of primes p such that 0.1 log x < p <= sqrt(2x).
-/
def PrimesInInterval (x : ℝ) : Finset ℕ :=
  Finset.filter (fun (p : ℕ) => 0.1 * Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * x) ∧ Nat.Prime p) (Finset.range (Nat.floor (Real.sqrt (2 * x)) + 1))

/-
CandidateSet is the set of n in the interval congruent to -b mod W.
-/
lemma CandidateSet_eq_modEq (x_nat W b : ℕ) (hW : W > 0) :
    CandidateSet x_nat W b = (Finset.Icc (Nat.ceil ((x_nat : ℝ) / 2)) (Nat.floor (x_nat : ℝ))).filter (fun n => n ≡ (W - (b % W)) % W [MOD W]) := by
      ext n; simp [CandidateSet];
      intro _ _; rw [ Nat.ModEq ] ; simp +decide [← ZMod.val_natCast] ;
      cases W <;> simp_all +decide [ ← eq_sub_iff_add_eq ];
      rw [ ← ZMod.natCast_eq_natCast_iff' ] ; aesop

lemma BadSet_card_bound (x_nat : ℕ) (W : ℕ) (b : ℕ) (a : ℕ) (p : ℕ)
    (hL : Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1 ≥ W) (hW : W > 0)
    (hp : Nat.Coprime W (p^2)) (hp_pos : p > 0) :
    let S := CandidateSet x_nat W b
    let B := BadSet x_nat W b a p
    let L_nat := Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1
    (B.card : ℝ) ≤ (S.card : ℝ) * C_freq * (1 / (p^2 : ℝ) + (W : ℝ) / (L_nat : ℝ)) := by
      convert C_freq_spec W ( p ^ 2 ) ( ( W - ( b % W ) ) % W ) ( ( p ^ 2 - ( a % p ^ 2 ) ) % p ^ 2 ) ( Nat.ceil ( ( x_nat : ℝ ) / 2 ) ) ( ⌊ ( x_nat : ℝ ) ⌋₊ - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) _ _ using 1;
      · constructor <;> intro h;
        · convert C_freq_spec W ( p ^ 2 ) ( ( W - b % W ) % W ) ( ( p ^ 2 - a % p ^ 2 ) % p ^ 2 ) ( Nat.ceil ( ( x_nat : ℝ ) / 2 ) ) ( ⌊ ( x_nat : ℝ ) ⌋₊ - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) _ _ using 1;
          · assumption;
          · convert hL using 1;
        · convert mul_le_mul_of_nonneg_left ( h ?_ ) ( Nat.cast_nonneg _ ) using 1;
          any_goals exact Finset.card ( Finset.filter ( fun n => n ≡ ( W - b % W ) % W [MOD W] ) ( Finset.Icc ⌈ ( x_nat : ℝ ) / 2⌉₊ ( ⌈ ( x_nat : ℝ ) / 2⌉₊ + ( ⌊ ( x_nat : ℝ ) ⌋₊ - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) - 1 ) ) );
          · rw [ mul_div_cancel₀ ];
            · congr! 2;
              ext; simp [BadSet, CandidateSet];
              simp +decide [Nat.ModEq, Nat.add_mod];
              constructor <;> intro h <;> simp_all +decide [← Nat.dvd_iff_mod_eq_zero];
              · constructor <;> rw [ Nat.ModEq.symm ];
                · rw [ Nat.modEq_iff_dvd ];
                  obtain ⟨ k, hk ⟩ := h.1.2; use k - ( b / W + 1 ) ; linarith [ Nat.div_add_mod b W, Nat.sub_add_cancel ( show b % W ≤ W from Nat.le_of_lt ( Nat.mod_lt _ hW ) ) ] ;
                · rw [ Nat.modEq_iff_dvd ];
                  rw [ Nat.cast_sub ( Nat.le_of_lt <| Nat.mod_lt _ <| by positivity ) ] ; push_cast ; obtain ⟨ k, hk ⟩ := h.2 ; exact ⟨ k - ( a / p ^ 2 ) - 1, by linarith [ Nat.mod_add_div a ( p ^ 2 ) ] ⟩;
              · exact ⟨ ⟨ b / W + 1, by linarith [ Nat.div_add_mod b W, Nat.sub_add_cancel ( show b % W ≤ W from Nat.le_of_lt ( Nat.mod_lt _ hW ) ) ] ⟩, ⟨ a / p ^ 2 + 1, by linarith [ Nat.div_add_mod a ( p ^ 2 ), Nat.sub_add_cancel ( show a % p ^ 2 ≤ p ^ 2 from Nat.le_of_lt ( Nat.mod_lt _ ( pow_pos hp_pos 2 ) ) ) ] ⟩ ⟩;
            · have := exists_mod_in_interval ⌈ ( x_nat : ℝ ) / 2⌉₊ ( x_nat - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) W ( ( W - b % W ) % W ) ?_ ?_ <;> aesop;
          · rw [ ← mul_assoc, mul_comm ];
            rw [ mul_comm ] ; norm_num [CandidateSet_eq_modEq, hW];
          · refine' Finset.card_pos.mpr _;
            obtain ⟨ n, hn ⟩ := exists_mod_in_interval ⌈ ( x_nat : ℝ ) / 2⌉₊ ( ⌊ ( x_nat : ℝ ) ⌋₊ - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) W ( ( W - b % W ) % W ) ( by linarith ) ( by linarith ) ; use n; aesop;
      · assumption;
      · exact hL

/-
The union of all bad sets for a in A and p in the relevant prime interval.
-/
def UnionBadSets (x_nat : ℕ) (W : ℕ) (b : ℕ) (A : Finset ℕ) : Finset ℕ :=
  Finset.biUnion A (fun a => Finset.biUnion (PrimesInInterval (x_nat : ℝ)) (fun p => BadSet x_nat W b a p))

/-
The size of the union of bad sets is bounded by the sum of the bounds.
-/
lemma UnionBadSets_card_bound (x_nat : ℕ) (W : ℕ) (b : ℕ) (A : Finset ℕ)
    (hL : Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1 ≥ W) (hW : W > 0)
    (hCoprime : ∀ p ∈ PrimesInInterval (x_nat : ℝ), Nat.Coprime W (p^2)) :
    let S := CandidateSet x_nat W b
    let U := UnionBadSets x_nat W b A
    let L_nat := Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1
    (U.card : ℝ) ≤ (S.card : ℝ) * C_freq * (A.card : ℝ) * ∑ p ∈ PrimesInInterval (x_nat : ℝ), (1 / (p^2 : ℝ) + (W : ℝ) / (L_nat : ℝ)) := by
      refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
      refine' le_trans ( Nat.cast_le.mpr <| Finset.sum_le_sum fun a ha => Finset.card_biUnion_le ) _;
      push_cast [ Finset.mul_sum _ _ _ ];
      rw [ Finset.sum_comm ];
      refine Finset.sum_le_sum fun p hp => ?_;
      have := BadSet_card_bound x_nat W b;
      convert Finset.sum_le_sum fun a ha => this a p hL hW ( hCoprime p hp ) ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2.2.2 ) ) using 1 ; norm_num ; ring

/-
W is coprime to p^2 for any p in the relevant interval.
-/
lemma W_coprime_primes (x_nat : ℕ) (W : ℕ) (hW : W = W_val x_nat) :
    ∀ p ∈ PrimesInInterval (x_nat : ℝ), Nat.Coprime W (p^2) := by
      unfold W_val at hW;
      -- Since $p$ is a prime in the interval $(0.1 \log x, \sqrt{2x}]$, it is greater than any prime factor of $W$.
      intros p hp
      have h_gt : ∀ q ∈ Finset.range (Nat.floor (0.1 * Real.log x_nat) + 1), Nat.Prime q → q < p := by
        intro q hq hq'; have := Finset.mem_filter.mp hp; norm_num at *;
        exact Nat.lt_of_lt_of_le hq ( Nat.succ_le_of_lt <| Nat.floor_lt ( by positivity ) |>.2 <| by linarith );
      simp_all +decide [Nat.coprime_prod_left_iff];
      exact fun q hq hq' => Nat.Coprime.symm <| Nat.Prime.coprime_iff_not_dvd ( by unfold PrimesInInterval at hp; aesop ) |>.2 <| Nat.not_dvd_of_pos_of_lt hq'.pos <| h_gt q hq hq'

/-
The size of the union of bad sets is strictly less than the size of the candidate set.
-/
lemma UnionBadSets_card_lt_S_card (x_nat : ℕ) (hx : (x_nat : ℝ) ≥ 100) (W : ℕ) (hW : W = W_val x_nat) (b : ℕ) (A : Finset ℕ)
    (hL : Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1 ≥ W)
    (h_prob : (A.card : ℝ) * C_freq * failure_prob_sum_2 x_nat < 1)
    (hS_pos : (CandidateSet x_nat W b).card > 0) :
    (UnionBadSets x_nat W b A).card < (CandidateSet x_nat W b).card := by
      have h_union_bad_sets_card_bound : (UnionBadSets x_nat W b A).card ≤ (CandidateSet x_nat W b).card * C_freq * (A.card : ℝ) * failure_prob_sum_2 x_nat := by
        refine le_trans ( UnionBadSets_card_bound x_nat W b A hL ?_ ?_ ) ?_;
        · exact hW.symm ▸ Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2;
        · exact fun p a => W_coprime_primes x_nat W hW p a;
        · gcongr;
          · exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( C_freq_pos ) ) ) ( Nat.cast_nonneg _ );
          · convert sum_bound_inequality x_nat ( by linarith ) ( ⌊ ( x_nat : ℝ ) ⌋₊ - ⌈ ( x_nat : ℝ ) / 2⌉₊ + 1 ) _ ( W : ℝ ) _ using 1;
            · unfold PrimesInInterval; norm_num;
            · norm_num +zetaDelta at *;
              linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( x_nat : ℝ ) / 2 by positivity ) ];
            · exact congrArg Nat.cast hW;
      exact_mod_cast ( by nlinarith [ ( by norm_cast : ( 0 :ℝ ) < Finset.card ( CandidateSet x_nat W b ) ) ] : ( Finset.card (UnionBadSets x_nat W b A) :ℝ ) < Finset.card ( CandidateSet x_nat W b ) )

lemma exists_good_n_final (x_nat : ℕ) (hx : (x_nat : ℝ) ≥ 100) (W : ℕ) (hW : W = W_val x_nat) (b : ℕ) (A : Finset ℕ)
    (hA_subset : ∀ a ∈ A, a ≤ x_nat)
    (hA_admissible : ∀ p, p ∣ W → Nat.Prime p → ∀ a ∈ A, a % p^2 ≠ b % p^2)
    (hL : Nat.floor (x_nat : ℝ) - Nat.ceil ((x_nat : ℝ) / 2) + 1 ≥ W)
    (h_prob : (A.card : ℝ) * C_freq * failure_prob_sum_2 x_nat < 1) :
    ∃ n ∈ Finset.Icc (Nat.ceil ((x_nat : ℝ) / 2)) (Nat.floor (x_nat : ℝ)), (n + b) % W = 0 ∧ ∀ a ∈ A, Squarefree (n + a) := by
      obtain ⟨n, hn⟩ : ∃ n ∈ CandidateSet x_nat W b, n ∉ UnionBadSets x_nat W b A := by
        have h_card_lt_S_card : (UnionBadSets x_nat W b A).card < (CandidateSet x_nat W b).card := by
          apply UnionBadSets_card_lt_S_card x_nat hx W hW b A hL h_prob (by
          convert CandidateSet_nonempty x_nat W b hL _;
          · exact Finset.card_pos;
          · exact hW.symm ▸ Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) 2);
        exact Finset.not_subset.mp fun h => h_card_lt_S_card.not_ge <| Finset.card_le_card h;
      refine' ⟨ n, _, _, _ ⟩ <;> simp_all +decide;
      · unfold CandidateSet at hn; aesop;
      · unfold CandidateSet at hn; aesop;
      · intro a ha
        have h_not_div : ∀ p, Nat.Prime p → p^2 ∣ (n + a) → False := by
          intro p hp hp_div
          by_cases hp_le : p ≤ Nat.floor (0.1 * Real.log x_nat);
          · -- Since $p \leq \lfloor 0.1 \log x_nat \rfloor$, we have $p^2 \mid W$.
            have hp_sq_div_W : p^2 ∣ W_val x_nat := by
              refine' Finset.dvd_prod_of_mem _ _;
              exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le hp_le ), hp ⟩;
            -- Since $p^2 \mid W$, we have $n \equiv -b \pmod{p^2}$.
            have hn_mod_p2 : n ≡ -b [ZMOD p^2] := by
              have hn_mod_p2 : (n + b) % p^2 = 0 := by
                exact Nat.mod_eq_zero_of_dvd ( dvd_trans hp_sq_div_W ( Nat.dvd_of_mod_eq_zero ( Finset.mem_filter.mp hn.1 |>.2 ) ) );
              exact Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using Nat.dvd_of_mod_eq_zero hn_mod_p2;
            have hn_mod_p2 : (n + a : ℤ) ≡ (a - b : ℤ) [ZMOD p^2] := by
              convert hn_mod_p2.add_right a using 1 ; ring;
            have hn_mod_p2 : (a - b : ℤ) ≡ 0 [ZMOD p^2] := by
              exact hn_mod_p2.symm.trans ( Int.modEq_zero_iff_dvd.mpr <| mod_cast hp_div );
            exact hA_admissible p ( dvd_trans ( dvd_pow_self _ two_ne_zero ) hp_sq_div_W ) hp a ha ( Nat.ModEq.symm <| Nat.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using hn_mod_p2.symm.dvd );
          · by_cases hp_ge : p ≤ Nat.floor (Real.sqrt (2 * x_nat));
            · contrapose! hn; simp_all +decide [ CandidateSet, UnionBadSets, BadSet ] ;
              refine' fun _ _ _ => ⟨ a, ha, p, _, _ ⟩ <;> norm_num [ PrimesInInterval ] at *;
              · exact ⟨ Nat.lt_succ_of_le hp_ge, Nat.lt_of_floor_lt hp_le, Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hp_ge ), hp ⟩;
              · exact Nat.mod_eq_zero_of_dvd hp_div;
            · have h_contra : p^2 > 2 * x_nat := by
                exact_mod_cast ( by nlinarith only [ Nat.lt_floor_add_one ( Real.sqrt ( 2 * x_nat ) ), Real.sqrt_nonneg ( 2 * x_nat ), Real.mul_self_sqrt ( show 0 ≤ 2 * ( x_nat : ℝ ) by positivity ), show ( p : ℝ ) ≥ ⌊Real.sqrt ( 2 * x_nat ) ⌋₊ + 1 by exact_mod_cast not_le.mp hp_ge ] : ( p : ℝ ) ^ 2 > 2 * x_nat );
              have h_contra : n + a ≤ 2 * x_nat := by
                have h_contra : n ≤ x_nat := by
                  exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hn.1 |>.1 ) |>.2.trans ( Nat.floor_le_of_le ( by norm_num ) );
                linarith [ hA_subset a ha ];
              have h_contra : n + a = 0 := by
                exact Nat.eq_zero_of_dvd_of_lt hp_div ( by linarith );
              simp_all +decide [ CandidateSet ];
              exact hn.1.1.not_gt ( by positivity );
        exact Nat.squarefree_iff_prime_squarefree.mpr fun p hp => fun h => h_not_div p hp <| by simpa only [ sq ] using h;

/-
If a set A satisfies the growth condition for a constant C, and C satisfies the probability condition, then A has Property Q.
-/
lemma sufficient_condition_for_Q (h : SieveAssumptions) (A : Set ℕ) (hA_adm : Admissible A) (hA_inf : A.Infinite) (C : ℝ) (hC_pos : C > 0)
    (h_prob : ∀ᶠ j in Filter.atTop, ∀ x, x ≥ Real.exp (C * j / Real.log j) → (j : ℝ) * C_freq * failure_prob_sum_2 x < 1)
    (h_growth : GrowthCondition A C) : PropertyQ A := by
      -- Let J be the set of such j. J is infinite.
      obtain ⟨J, hJ_inf, hJ⟩ : ∃ J : ℕ → ℕ, StrictMono J ∧ ∀ j, (Nat.nth (· ∈ A) (J j - 1) : ℝ) ≥ Real.exp (C * (J j) / Real.log (J j)) := by
        have hJ_inf : {j : ℕ | (Nat.nth (fun x => x ∈ A) (j - 1) : ℝ) ≥ Real.exp (C * j / Real.log j)}.Infinite := by
          exact Nat.frequently_atTop_iff_infinite.mp h_growth;
        exact ⟨ fun n => Nat.recOn n ( Nat.find <| hJ_inf.nonempty ) fun n ih => Nat.find <| hJ_inf.exists_gt ih, strictMono_nat_of_lt_succ fun n => Nat.find_spec ( hJ_inf.exists_gt _ ) |>.2, fun n => Nat.recOn n ( Nat.find_spec <| hJ_inf.nonempty ) fun n ih => Nat.find_spec ( hJ_inf.exists_gt _ ) |>.1 ⟩;
      -- By choosing a sufficiently large $j$, we can ensure that the conditions of `exists_good_n_final` are met.
      obtain ⟨j₀, hj₀⟩ : ∃ j₀, ∀ j ≥ j₀, (Nat.nth (· ∈ A) (J j - 1) : ℝ) ≥ 100 ∧ (Nat.floor (Nat.nth (· ∈ A) (J j - 1) : ℝ) - Nat.ceil ((Nat.nth (· ∈ A) (J j - 1) : ℝ) / 2) + 1 ≥ W_val (Nat.nth (· ∈ A) (J j - 1) : ℝ)) ∧ (J j : ℝ) * C_freq * failure_prob_sum_2 (Nat.nth (· ∈ A) (J j - 1) : ℝ) < 1 := by
        have h_cond : ∀ᶠ j in Filter.atTop, (Nat.nth (· ∈ A) (J j - 1) : ℝ) ≥ 100 ∧ (Nat.floor (Nat.nth (· ∈ A) (J j - 1) : ℝ) - Nat.ceil ((Nat.nth (· ∈ A) (J j - 1) : ℝ) / 2) + 1 ≥ W_val (Nat.nth (· ∈ A) (J j - 1) : ℝ)) := by
          have h_cond : Filter.Tendsto (fun j => (Nat.nth (· ∈ A) (J j - 1) : ℝ)) Filter.atTop Filter.atTop := by
            refine' Filter.tendsto_atTop_mono hJ _;
            have h_exp_growth : Filter.Tendsto (fun x : ℝ => Real.exp (C * x / Real.log x)) Filter.atTop Filter.atTop := by
              refine' Real.tendsto_exp_atTop.comp _;
              -- We can use the change of variables $u = \log x$ to transform the limit expression.
              suffices h_log : Filter.Tendsto (fun u : ℝ => C * Real.exp u / u) Filter.atTop Filter.atTop by
                have := h_log.comp Real.tendsto_log_atTop;
                exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
              simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop hC_pos ( Real.tendsto_exp_div_pow_atTop 1 );
            exact h_exp_growth.comp <| tendsto_natCast_atTop_atTop.comp hJ_inf.tendsto_atTop;
          have h_cond : ∀ᶠ j in Filter.atTop, (Nat.nth (· ∈ A) (J j - 1) : ℝ) ≥ 100 ∧ (Nat.floor (Nat.nth (· ∈ A) (J j - 1) : ℝ) - Nat.ceil ((Nat.nth (· ∈ A) (J j - 1) : ℝ) / 2) + 1 : ℝ) ≥ W_val (Nat.nth (· ∈ A) (J j - 1) : ℝ) := by
            filter_upwards [ h_cond.eventually_ge_atTop 100, length_condition h |> fun h => h.filter_mono h_cond ] with j hj₁ hj₂ using ⟨ hj₁, hj₂ ⟩;
          convert h_cond using 1;
          norm_cast;
          ext; rw [ Int.subNatNat_of_le ] ; norm_cast; aesop;
        have := h_prob.natCast_atTop;
        obtain ⟨ j₀, hj₀ ⟩ := Filter.eventually_atTop.mp ( this.and ( h_cond ) );
        exact ⟨ j₀, fun j hj => ⟨ hj₀ j hj |>.2.1, hj₀ j hj |>.2.2, hj₀ ( J j ) ( hJ_inf.id_le _ |> le_trans hj ) |>.1 _ ( hJ j ) ⟩ ⟩;
      -- For each $j \geq j₀$, let $x = \text{Nat.nth} (· ∈ A) (J j - 1)$.
      have h_exists_good_n : ∀ j ≥ j₀, ∃ n ∈ Finset.Icc (Nat.ceil ((Nat.nth (· ∈ A) (J j - 1) : ℝ) / 2)) (Nat.floor (Nat.nth (· ∈ A) (J j - 1) : ℝ)), (n + (Classical.choose (admissible_to_b_W_val A hA_adm (Nat.nth (· ∈ A) (J j - 1) : ℝ))) : ℕ) % W_val (Nat.nth (· ∈ A) (J j - 1) : ℝ) = 0 ∧ ∀ a ∈ Finset.filter (fun a => a ≤ Nat.nth (· ∈ A) (J j - 1)) (Finset.image (fun i => Nat.nth (· ∈ A) i) (Finset.range (J j))), Squarefree (n + a) := by
        intro j hj;
        convert exists_good_n_final ( Nat.nth ( fun x => x ∈ A ) ( J j - 1 ) ) ( hj₀ j hj |>.1 ) ( W_val ( Nat.nth ( fun x => x ∈ A ) ( J j - 1 ) : ℝ ) ) rfl ( Classical.choose ( admissible_to_b_W_val A hA_adm ( Nat.nth ( fun x => x ∈ A ) ( J j - 1 ) : ℝ ) ) ) ( Finset.filter ( fun a => a ≤ Nat.nth ( fun x => x ∈ A ) ( J j - 1 ) ) ( Finset.image ( fun i => Nat.nth ( fun x => x ∈ A ) i ) ( Finset.range ( J j ) ) ) ) _ _ _ _ using 1;
        · aesop;
        · intro p hp hp_prime a ha;
          have := Classical.choose_spec ( admissible_to_b_W_val A hA_adm ( Nat.nth ( fun x => x ∈ A ) ( J j - 1 ) : ℝ ) ) p hp hp_prime;
          norm_num +zetaDelta at *;
          exact this a ( by obtain ⟨ k, hk₁, rfl ⟩ := ha.1; exact Nat.nth_mem_of_infinite hA_inf _ );
        · exact hj₀ j hj |>.2.1;
        · refine' lt_of_le_of_lt _ ( hj₀ j hj |>.2.2 );
          gcongr;
          · exact Finset.sum_nonneg fun _ _ => add_nonneg ( one_div_nonneg.mpr ( sq_nonneg _ ) ) ( div_nonneg ( mul_nonneg zero_le_two ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ ) );
          · exact le_of_lt ( C_freq_pos );
          · exact le_trans ( Finset.card_filter_le _ _ ) ( Finset.card_image_le.trans ( by simp ) );
      choose! n hn using h_exists_good_n;
      -- Since $n_j$ is in the interval $[x/2, x]$ and $x \to \infty$, $n_j \to \infty$.
      have h_n_inf : Filter.Tendsto (fun j => n (j₀ + j)) Filter.atTop Filter.atTop := by
        have h_n_inf : Filter.Tendsto (fun j => Nat.nth (· ∈ A) (J (j₀ + j) - 1)) Filter.atTop Filter.atTop := by
          have h_n_inf : Filter.Tendsto (fun j => Real.exp (C * (J (j₀ + j)) / Real.log (J (j₀ + j)))) Filter.atTop Filter.atTop := by
            refine' Real.tendsto_exp_atTop.comp _;
            have h_log_growth : Filter.Tendsto (fun x : ℝ => x / Real.log x) Filter.atTop Filter.atTop := by
              -- We can use the change of variables $u = \log x$ to transform the limit expression.
              suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
                have := h_log.comp Real.tendsto_log_atTop;
                exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
              simpa using Real.tendsto_exp_div_pow_atTop 1;
            simpa only [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop hC_pos ( h_log_growth.comp <| tendsto_natCast_atTop_atTop.comp <| hJ_inf.tendsto_atTop.comp <| Filter.tendsto_atTop_mono ( fun _ => Nat.le_add_left _ _ ) Filter.tendsto_id );
          exact Filter.tendsto_atTop_atTop.mpr fun x => by rcases Filter.eventually_atTop.mp ( h_n_inf.eventually_ge_atTop x ) with ⟨ j, hj ⟩ ; exact ⟨ j, fun k hk => by exact_mod_cast le_trans ( hj k hk ) ( hJ _ ) ⟩ ;
        rw [ Filter.tendsto_atTop_atTop ] at *;
        exact fun b => by obtain ⟨ i, hi ⟩ := h_n_inf ( b * 2 ) ; exact ⟨ i, fun a ha => by have := hn ( j₀ + a ) ( by linarith ) ; exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( ( Nat.nth ( fun x => x ∈ A ) ( J ( j₀ + a ) - 1 ) : ℝ ) / 2 ), Nat.ceil_le.mp ( Finset.mem_Icc.mp this.1 |>.1 ), Nat.floor_le ( show ( Nat.nth ( fun x => x ∈ A ) ( J ( j₀ + a ) - 1 ) : ℝ ) ≥ 0 by positivity ), Nat.floor_le ( show ( Nat.nth ( fun x => x ∈ A ) ( J ( j₀ + a ) - 1 ) : ℝ ) ≥ 0 by positivity ), show ( Nat.nth ( fun x => x ∈ A ) ( J ( j₀ + a ) - 1 ) : ℝ ) ≥ b * 2 by exact_mod_cast hi a ha ] ⟩ ;
      refine' Set.infinite_of_forall_exists_gt _;
      intro a;
      obtain ⟨ j, hj ⟩ := Filter.eventually_atTop.mp ( h_n_inf.eventually_gt_atTop a );
      use n (j₀ + j);
      refine' ⟨ _, hj j le_rfl ⟩;
      intro a ha ha'; have := hn ( j₀ + j ) ( by linarith ) ; simp_all +decide ;
      -- Since $a \in A$ and $a < n (j₀ + j)$, there exists some $i$ such that $a = \text{Nat.nth} (· ∈ A) i$.
      obtain ⟨i, hi⟩ : ∃ i, a = Nat.nth (· ∈ A) i := by
        exact ⟨ Nat.count ( fun x => x ∈ A ) a, by rw [ Nat.nth_count ] ; aesop ⟩;
      by_cases hi' : i < J ( j₀ + j ) <;> simp_all +decide;
      · exact hn ( j₀ + j ) ( by linarith ) |>.2.2 i hi' ( Nat.nth_monotone ( show { x | x ∈ A }.Infinite from hA_inf ) ( Nat.le_sub_one_of_lt hi' ) );
      · contrapose! ha';
        refine' le_trans ( hn _ ( by linarith ) |>.1 |>.2 ) _;
        rw [ Nat.nth_le_nth _ ];
        · exact Nat.sub_le_of_le_add <| by linarith;
        · exact hA_inf

/-
There is an absolute constant C such that, if A is an admissible sequence with a_j >= exp(C j / log j) for infinitely many j, then A has property Q.
-/
theorem Theorem_suff (h : SieveAssumptions) :
  ∃ C > 0, ∀ A : Set ℕ, Admissible A → A.Infinite → GrowthCondition A C → PropertyQ A := by
    -- Apply the lemma prob_condition_of_growth_v2 to obtain the constant C.
    obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ᶠ j in Filter.atTop, ∀ x, x ≥ Real.exp (C * j / Real.log j) → (j : ℝ) * C_freq * failure_prob_sum_2 x < 1 := by
      exact prob_condition_of_growth_v2 h;
    refine' ⟨ C, hC_pos, _ ⟩;
    intro A hA_adm hA_inf h_growth
    apply sufficient_condition_for_Q h A hA_adm hA_inf C hC_pos;
    · exact hC;
    · assumption

#print axioms Theorem_suff

/-
The sequence A1 has property Q.
-/
theorem A1_PropertyQ (h : SieveAssumptions) : PropertyQ A1 := by
  obtain ⟨ C, hC_pos, hC ⟩ := Theorem_suff h;
  exact hC A1 A1_admissible A1_infinite ( A1_growth C )

/-
The sequence A2 has property Q.
-/
theorem A2_PropertyQ (h : SieveAssumptions) : PropertyQ A2 := by
  -- By Theorem_suff, there exists a constant C > 0 such that any admissible infinite sequence satisfying the growth condition for C has Property Q.
  obtain ⟨C, hC_pos, hC⟩ := Theorem_suff h;
  exact hC _ A2_admissible A2_infinite ( A2_growth C )

/-
The sequence A3 has property Q.
-/
theorem A3_PropertyQ (h : SieveAssumptions) : PropertyQ A3 := by
  -- By Theorem_suff, there exists a constant C > 0 such that any admissible infinite sequence satisfying the growth condition for C has Property Q.
  obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ A : Set ℕ, Admissible A → A.Infinite → GrowthCondition A C → PropertyQ A := by
    exact Theorem_suff h;
  exact hC A3 A3_admissible A3_infinite ( A3_growth C )

/-
The sequence A4 has property Q.
-/
theorem A4_PropertyQ (h : SieveAssumptions) : PropertyQ A4 := by
  obtain ⟨ C, hC_pos, hC ⟩ := Theorem_suff h;
  apply hC A4 A4_admissible A4_infinite;
  -- To show that A4 satisfies the growth condition with any constant C, we need to find infinitely many j such that the j-th element of A4 is at least exp(C*j/log j).
  have h_growth_A4 : ∀ C > 0, ∃ᶠ j in Filter.atTop, (Nat.nth (· ∈ A4) (j - 1) : ℝ) ≥ Real.exp (C * j / Real.log j) := by
    intro C hC_pos
    have h_growth_A4 : ∀ᶠ j in Filter.atTop, (Nat.factorial (j + 1) - 1 : ℝ) ≥ Real.exp (C * j / Real.log j) := by
      -- We'll use that $j!$ grows faster than any exponential function.
      have h_factorial_growth : Filter.Tendsto (fun j : ℕ => Real.exp (C * j / Real.log j) / (j ! : ℝ)) Filter.atTop (nhds 0) := by
        have h_factorial_growth : Filter.Tendsto (fun j : ℕ => Real.exp (C * j) / (j ! : ℝ)) Filter.atTop (nhds 0) := by
          have h_factorial_growth : Summable (fun j : ℕ => Real.exp (C * j) / (j ! : ℝ)) := by
            have := Real.summable_pow_div_factorial ( Real.exp C );
            simpa [ Real.exp_mul ] using this;
          convert h_factorial_growth.tendsto_atTop_zero;
        refine' squeeze_zero_norm' _ h_factorial_growth;
        norm_num +zetaDelta at *;
        exact ⟨ 3, fun n hn => by gcongr ; exact div_le_self ( by positivity ) ( Real.le_log_iff_exp_le ( by positivity ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ⟩;
      filter_upwards [ h_factorial_growth.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 0 ] with j hj₁ hj₂;
      rw [ div_lt_one ( by positivity ) ] at hj₁;
      exact le_trans hj₁.le ( le_tsub_of_add_le_right <| mod_cast by nlinarith [ Nat.factorial_pos j, Nat.factorial_succ j ] );
    refine' Filter.Eventually.frequently _;
    filter_upwards [ h_growth_A4, Filter.eventually_gt_atTop 1 ] with j hj₁ hj₂;
    rw [ A4_nth ];
    rw [ Nat.cast_sub <| Nat.factorial_pos _ ] ; cases j <;> norm_num [ Nat.factorial_succ ] at * ; linarith;
  exact h_growth_A4 C hC_pos

/-
All four sequences A1, A2, A3, A4 have property Q.
-/
theorem All_Sequences_PropertyQ (h : SieveAssumptions) : PropertyQ A1 ∧ PropertyQ A2 ∧ PropertyQ A3 ∧ PropertyQ A4 := by
  exact ⟨A1_PropertyQ h, A2_PropertyQ h, A3_PropertyQ h, A4_PropertyQ h⟩


#print axioms All_Sequences_PropertyQ
