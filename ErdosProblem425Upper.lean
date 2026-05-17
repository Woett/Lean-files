/-
Let F(n) be the largest cardinality of a subset of {1, 2, ..., n} such that the
products ab are distinct for all a < b in A. Erdős Problem #425
(https://www.erdosproblems.com/425) asks for the existence of a constant c such
that F(n) = π(n) + (c + o(1))n^{3/4}/(log n)^{3/2}.

Below you can find a formalization of the fact that if such a c exists, then c <
13.1. This formalization was obtained by Aristotle from Harmonic
(aristotle-harmonic@harmonic.fun), based on an improved version of Erdős'
original argument, which was written down by ChatGPT.

Erdős, P., On some applications of graph theory to number theoretic problems.
Publ. Ramanujan Inst. (1968/69), 131-136.

The proof uses various estimates on the distribution of prime numbers by Dusart.

Dusart, P. Explicit estimates of some functions over primes. Ramanujan J. 45,
227–251 (2018).

It furthermore uses an upper bound on the value of a certain integral, as well
as an estimate on the Buchstab function. Formalizations of these two results
(both conditional on prime bounds from the literature as well) can
also be found on my GitHub.

https://github.com/Woett/Lean-files/blob/main/ErdosProblem425UpperIntegral.lean

https://github.com/Woett/Lean-files/blob/main/ErdosProblem425UpperBuchstab.lean

Lean version: leanprover/lean4:v4.28.0
-/

import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

section Defs

open Finset BigOperators Real

noncomputable section

/-- A finite set of natural numbers is product-Sidon if whenever a*b = c*d
for a,b,c,d in the set, then {a,b} = {c,d} as unordered pairs. -/
def IsProductSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a * b = c * d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Φ(x, y) = #{m ∈ ℕ : 1 ≤ m ≤ x, P⁻(m) ≥ y}, i.e. the count of integers up to x
    whose smallest prime factor is ≥ y. -/
def sievePhi (x : ℕ) (y : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun m => ∀ p ∈ m.primeFactors, y ≤ p)).card

/-- A pair (u, v) is (n, α)-admissible for a if a = u*v, v ≤ u, v ≤ n^α,
    and either u is prime or u ≤ n^α. -/
def IsAdmissible (n : ℕ) (alpha : ℝ) (a u v : ℕ) : Prop :=
  a = u * v ∧ v ≤ u ∧ (v : ℝ) ≤ (n : ℝ) ^ alpha ∧
  (Nat.Prime u ∨ (u : ℝ) ≤ (n : ℝ) ^ alpha)

/-- H(x) = ∏_{p ≤ e^{2x}} (1 - 1/p)^{-1}. -/
def HFunc (x : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (Nat.floor (Real.exp (2 * x)) + 1)).filter Nat.Prime,
    (1 - 1 / (p : ℝ))⁻¹

/-- IsProductSidon is monotone: subsets of Sidon sets are Sidon. -/
lemma IsProductSidon.subset {A B : Finset ℕ} (hA : IsProductSidon A) (hBA : B ⊆ A) :
    IsProductSidon B :=
  fun a ha b hb c hc d hd h => hA a (hBA ha) b (hBA hb) c (hBA hc) d (hBA hd) h

/-- The set of primes up to a real number x. -/
def primesUpTo (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime

end

end Defs

section Dusart

/-! # Dusart Prime Estimates (axiomatized from Dusart 2018) -/

noncomputable section

open Finset BigOperators Nat Real

namespace DistinctProducts

/-! ## Dusart's prime counting estimate (Theorem 5.2) -/

/-- For x ≥ 88789, π(x) ≥ x/log x + x/log²x + 2x/log³x -/
axiom dusart_pi_lower (x : ℝ) (hx : x ≥ 88789) :
    x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 ≤
      ((primesUpTo x).card : ℝ)

/-- For x > 1, π(x) ≤ x/log x + x/log²x + 2.53816·x/log³x -/
axiom dusart_pi_upper (x : ℝ) (hx : x > 1) :
    ((primesUpTo x).card : ℝ) ≤
      x / Real.log x + x / Real.log x ^ 2 + 2.53816 * x / Real.log x ^ 3

end DistinctProducts
end

end Dusart

section MertensThird

open Finset ArithmeticFunction Real
open scoped BigOperators

noncomputable section

/-- ψ(n) = Σ_{m=1}^{n} Λ(m), the first Chebyshev function. -/
def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), vonMangoldt m

/-- L_n = lcm(1, 2, ..., n). -/
def lcmRange (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm _root_.id

/-- S(n) = Σ_{m=2}^{n} Λ(m)/m. -/
def sumS (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / m

/-- T(n) = Σ_{m=2}^{n} Λ(m)/(m * log m). -/
def sumT (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / (m * Real.log m)

/-- P(n) = ∏_{p ≤ n, p prime} (1 - 1/p). -/
def prodP (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

end

noncomputable section

/-! # Lemma: Central Binomial Coefficient Bounds -/

lemma centralBinom_le_four_pow (r : ℕ) (hr : 1 ≤ r) :
    Nat.choose (2 * r) r ≤ 4 ^ r := by
  rw [show 4 ^ r = (2 : ℕ) ^ (2 * r) by norm_num [pow_mul]]
  rw [← Nat.sum_range_choose]
  exact Finset.single_le_sum (fun x _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by linarith))

lemma choose_odd_le_four_pow (r : ℕ) (_hr : 1 ≤ r) :
    Nat.choose (2 * r + 1) r ≤ 4 ^ r := by
  exact Nat.choose_middle_le_pow r

/-! # LCM helpers -/

lemma lcmRange_pos (n : ℕ) (_hn : 1 ≤ n) : 0 < lcmRange n := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

lemma lcmRange_dvd_of_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    m ∣ lcmRange n := by
  exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hm, hmn ⟩ )

/-! # LCM Divisibility Lemmas -/

lemma lcmRange_dvd_even (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r) ∣ lcmRange r * Nat.choose (2 * r) r := by
  -- By definition of lcmRange, we need to show that for every prime power $p^a$ dividing $m \in (1, 2r]$, $p^a$ divides $lcmRange(r) * \binom{2r}{r}$.
  have h_div : ∀ m ∈ Finset.Icc 1 (2 * r), ∀ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm p hp
    by_cases hpa : p ^ Nat.factorization m p ≤ r;
    · exact dvd_mul_of_dvd_left ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.pos_of_mem_primeFactors hp ), hpa ⟩ ) ) _;
    · -- Since $p^a > r$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p ^ (Nat.factorization m p - 1) ≤ r := by
        rcases k : Nat.factorization m p with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
        nlinarith [ hp.1.two_le, Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), show m ≥ p ^ ( Nat.factorization m p ) from Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), show p ^ ( Nat.factorization m p ) = p * p ^ ‹_› from by rw [ ← pow_succ', k ] ];
      -- Since $p^{a-1} \leq r$, we have $p^{a-1} \mid lcmRange(r)$.
      have hpa_minus_one_div : p ^ (Nat.factorization m p - 1) ∣ lcmRange r := by
        exact lcmRange_dvd_of_le ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ ) hpa_minus_one;
      -- Since $p^a > r$, we have $p \mid \binom{2r}{r}$.
      have hpa_div_choose : p ∣ Nat.choose (2 * r) r := by
        have hpa_div_choose : Nat.factorization (Nat.choose (2 * r) r) p ≥ 1 := by
          have hpa_div_choose : Nat.factorization (Nat.choose (2 * r) r) p = (∑ k ∈ Finset.Ico 1 (Nat.log p (2 * r) + 1), (Nat.floor ((2 * r) / p ^ k) - 2 * Nat.floor (r / p ^ k))) := by
            haveI := Fact.mk ( Nat.prime_of_mem_primeFactors hp ) ; rw [ Nat.factorization_def ];
            · rw [ padicValNat_choose ];
              any_goals exact Nat.lt_succ_self _;
              · norm_num [ two_mul, Nat.add_div ];
                rw [ Finset.card_filter ];
                refine' Finset.sum_congr rfl fun x hx => _;
                rw [ Nat.add_div ( pow_pos ( Nat.Prime.pos ( Nat.prime_of_mem_primeFactors hp ) ) _ ) ] ; aesop;
              · linarith;
            · exact Nat.prime_of_mem_primeFactors hp;
          rw [hpa_div_choose];
          refine' le_trans _ ( Finset.single_le_sum ( fun x hx => Nat.zero_le _ ) ( Finset.mem_Ico.mpr ⟨ Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( show m.factorization p ≠ 0 from Finsupp.mem_support_iff.mp hp ) ), Nat.lt_succ_of_le ( Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) ( show p ^ m.factorization p ≤ 2 * r from _ ) ) ⟩ ) );
          · norm_num [ Nat.div_eq_of_lt ( show r < p ^ m.factorization p from lt_of_not_ge hpa ) ];
            exact Nat.div_pos ( by linarith [ Finset.mem_Icc.mp hm, Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd m p ) ] ) ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ );
          · exact le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd _ _ ) ) ( by linarith [ Finset.mem_Icc.mp hm ] );
        exact Nat.dvd_trans ( dvd_pow_self _ ( by linarith ) ) ( Nat.ordProj_dvd _ _ );
      convert Nat.mul_dvd_mul hpa_minus_one_div hpa_div_choose using 1 ; rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ) ) ];
  -- Since every prime power in the lcm divides the product, the lcm itself must divide the product.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r), m ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm
    have h_prod_div : ∏ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
      convert Finset.lcm_dvd fun p hp => h_div m hm p hp using 1;
      -- The least common multiple of a set of numbers is equal to their product divided by their greatest common divisor.
      have h_lcm_prod : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ p ∈ S, Nat.Prime p) → (∀ p q : ℕ, p ∈ S → q ∈ S → p ≠ q → Nat.gcd (p ^ f p) (q ^ f q) = 1) → Finset.lcm S (fun p => p ^ f p) = ∏ p ∈ S, p ^ f p := by
        intros S f hprime hgcd; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => hgcd _ _ ( Or.inl rfl ) ( Or.inr hp ) <| by aesop;
      rw [ h_lcm_prod ( fun p hp => Nat.prime_of_mem_primeFactors hp ) ( fun p q hp hq hpq => by simpa [ hpq ] using Nat.coprime_pow_primes _ _ ( Nat.prime_of_mem_primeFactors hp ) ( Nat.prime_of_mem_primeFactors hq ) ) ];
    rwa [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ];
  exact Finset.lcm_dvd h_lcm_div

lemma lcmRange_dvd_odd (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r + 1) ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
  -- For any prime power $p^a \leq 2r+1$, we need to show that $p^a$ divides $lcmRange(r+1) * (2r+1 choose r)$.
  have h_prime_power : ∀ p a : ℕ, Nat.Prime p → p^a ≤ 2 * r + 1 → p^a ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro p a hp ha
    by_cases hpa : p^a ≤ r + 1;
    · refine' dvd_mul_of_dvd_left _ _;
      exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, hpa ⟩ );
    · -- Since $p^a > r + 1$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p^(a-1) ≤ r := by
        rcases a <;> simp_all +decide [ pow_succ' ];
        nlinarith [ hp.two_le ];
      -- Since $p^{a-1} \leq r$, we have $p^a \mid \binom{2r+1}{r}$.
      have hpa_div_choose : p^a ∣ Nat.choose (2 * r + 1) r * p^(a-1) := by
        have hpa_div_choose : padicValNat p (Nat.choose (2 * r + 1) r) ≥ 1 := by
          haveI := Fact.mk hp; rw [ padicValNat_choose ];
          any_goals exact Nat.lt_succ_self _;
          · refine' Finset.card_pos.mpr ⟨ a, _ ⟩ ; norm_num;
            exact ⟨ ⟨ Nat.pos_of_ne_zero ( by rintro rfl; linarith ), Nat.le_log_of_pow_le hp.one_lt ha ⟩, by rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega ⟩;
          · linarith;
        have hpa_div_choose : p ∣ Nat.choose (2 * r + 1) r := by
          contrapose! hpa_div_choose; simp_all +decide ;
        rcases a with ( _ | a ) <;> simp_all +decide [ pow_succ', mul_dvd_mul ];
      -- Since $p^{a-1} \leq r$, we have $p^{a-1} \mid lcmRange(r+1)$.
      have hpa_minus_one_div_lcm : p^(a-1) ∣ lcmRange (r + 1) := by
        have hpa_minus_one_div_lcm : p^(a-1) ∈ Finset.Icc 1 (r + 1) := by
          exact Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, by linarith ⟩;
        exact Finset.dvd_lcm hpa_minus_one_div_lcm;
      exact dvd_trans hpa_div_choose ( by rw [ mul_comm ] ; exact mul_dvd_mul hpa_minus_one_div_lcm dvd_rfl );
  -- By definition of lcmRange, lcmRange (2 * r + 1) divides the product of all numbers in the range 1 to 2r+1.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r + 1), m ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro m hm; rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
    · intro p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ∣ m <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
      have := h_prime_power p ( Nat.factorization m p ) hp ( Nat.le_trans ( Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd _ _ ) ) hm.2 ) ; rw [ ← Nat.factorization_le_iff_dvd ] at this <;> simp_all +decide ;
      exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, Nat.ne_of_gt <| Nat.choose_pos <| by linarith ⟩;
    · linarith [ Finset.mem_Icc.mp hm ];
    · exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, Nat.ne_of_gt <| Nat.choose_pos <| by linarith ⟩;
  exact Finset.lcm_dvd fun x hx => h_lcm_div x hx

/-! # LCM Bound: L_n ≤ 4^n -/

lemma lcmRange_le_four_pow (n : ℕ) (hn : 1 ≤ n) :
    lcmRange n ≤ 4 ^ n := by
  induction' n using Nat.strong_induction_on with n ih;
  by_cases h₂ : n ≤ 4;
  · interval_cases n <;> decide;
  · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
    · -- By lcmRange_dvd_even, lcmRange(2k) | lcmRange(k) * choose(2k,k).
      have h_div : lcmRange (2 * k) ∣ lcmRange k * Nat.choose (2 * k) k := by
        exact lcmRange_dvd_even k ( by linarith );
      -- Since $\binom{2k}{k} \leq 4^k$, we have $lcmRange (2 * k) \leq lcmRange k * 4^k$.
      have h_bound : lcmRange (2 * k) ≤ lcmRange k * 4 ^ k := by
        refine' le_trans ( Nat.le_of_dvd ( Nat.mul_pos ( lcmRange_pos k ( by linarith ) ) ( Nat.choose_pos ( by linarith ) ) ) h_div ) _;
        exact Nat.mul_le_mul_left _ ( centralBinom_le_four_pow k ( by linarith ) );
      exact h_bound.trans ( by rw [ pow_mul' ] ; exact Nat.mul_le_mul_right _ ( ih k ( by linarith ) ( by linarith ) ) |> le_trans <| by ring_nf; norm_num );
    · -- By lcmRange_dvd_odd, lcmRange(2k+1) | lcmRange(k+1) * choose(2k+1,k).
      have h_div : lcmRange (2 * k + 1) ∣ lcmRange (k + 1) * Nat.choose (2 * k + 1) k := by
        convert lcmRange_dvd_odd k ( by linarith ) using 1;
      -- By choose_odd_le_four_pow, choose(2k+1,k) ≤ 4^k.
      have h_choose : Nat.choose (2 * k + 1) k ≤ 4 ^ k := by
        convert choose_odd_le_four_pow k ( by linarith ) using 1;
      refine' le_trans ( Nat.le_of_dvd _ h_div ) _;
      · exact mul_pos ( lcmRange_pos _ ( by linarith ) ) ( Nat.choose_pos ( by linarith ) );
      · exact le_trans ( Nat.mul_le_mul ( ih _ ( by linarith ) ( by linarith ) ) h_choose ) ( by ring_nf; norm_num )

/-! # Chebyshev ψ bound -/

lemma chebyshevPsi_eq_log_lcmRange (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi n = Real.log (lcmRange n) := by
  -- By definition of ψ, we know that ψ(n) = Σ_{m=0}^n Λ(m)
  have h_psi_def : chebyshevPsi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), Nat.log p n * Real.log p := by
    have h_psi_def : chebyshevPsi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (∑ k ∈ Finset.Icc 1 (Nat.log p n), Real.log p) := by
      unfold chebyshevPsi;
      have h_sum_floor : ∑ m ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (ArithmeticFunction.vonMangoldt (p ^ k)) := by
        have h_sum_floor : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.range (n + 1)) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => Finset.image (fun k => p ^ k) (Finset.Icc 1 (Nat.log p n))) := by
          ext m;
          simp [ArithmeticFunction.vonMangoldt];
          constructor;
          · intro hm;
            obtain ⟨ p, k, hp, hk, rfl ⟩ := hm.2.1;
            exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hm.1 ⟩, rfl ⟩;
          · rintro ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
            exact ⟨ Nat.pow_le_of_le_log ( by linarith ) hk₂, hp₂.isPrimePow.pow ( by linarith ), Nat.ne_of_gt ( Nat.minFac_pos _ ), ne_of_gt ( one_lt_pow₀ hp₂.one_lt ( by linarith ) ), by linarith ⟩;
        rw [ ← Finset.sum_filter_ne_zero, h_sum_floor, Finset.sum_biUnion ];
        · exact Finset.sum_congr rfl fun p hp => Finset.sum_image <| fun a ha b hb h => Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) h;
        · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
          intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
      convert h_sum_floor using 3;
      rw [ ArithmeticFunction.vonMangoldt_apply ];
      rw [ if_pos ];
      · rw [ Nat.Prime.pow_minFac ] <;> aesop;
      · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp ‹_› |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp ‹_› ] );
    aesop;
  -- By definition of $lcmRange$, we know that $lcmRange n = \prod_{p \leq n} p^{e_p(n)}$ where $e_p(n) = \lfloor \log_p n \rfloor$.
  have h_lcm_def : lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) := by
    clear h_psi_def;
    -- By definition of lcmRange, we know that lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n).
    have h_lcmRange_def : ∀ m ∈ Finset.Icc 1 n, m ∣ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) := by
      intro m hm; rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ] ;
      rw [ ← Finset.prod_sdiff <| show m.primeFactors ⊆ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ) from fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_trans ( Nat.le_of_mem_primeFactors hp ) <| Finset.mem_Icc.mp hm |>.2, Nat.prime_of_mem_primeFactors hp ⟩ ];
      exact dvd_mul_of_dvd_right ( Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p <| Nat.le_log_of_pow_le ( Nat.prime_of_mem_primeFactors hp |> Nat.Prime.one_lt ) <| Nat.le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) <| Nat.ordProj_dvd _ _ ) <| Finset.mem_Icc.mp hm |>.2 ) _;
    refine' Nat.dvd_antisymm _ _;
    · exact Finset.lcm_dvd fun x hx => h_lcmRange_def x hx;
    · -- By definition of lcmRange, we know that lcmRange n is divisible by each prime power p^k where p is prime and k is such that p^k ≤ n.
      have h_lcmRange_div : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) ∣ lcmRange n := by
        intros p hp
        have h_div : p ^ (Nat.log p n) ≤ n := by
          exact Nat.pow_log_le_self p ( by linarith );
        exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ), h_div ⟩ );
      convert Finset.lcm_dvd h_lcmRange_div using 1;
      -- The least common multiple of a set of numbers is equal to the product of the highest powers of all primes dividing any of the numbers.
      have h_lcm_eq_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Finset.lcm S (fun p => p ^ (Nat.log p n)) = ∏ p ∈ S, p ^ (Nat.log p n) := by
        intros S hS; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop;
      rw [ h_lcm_eq_prod fun p hp => Finset.mem_filter.mp hp |>.2 ];
  rw [ h_psi_def, h_lcm_def, Nat.cast_prod, Real.log_prod ] <;> aesop

lemma chebyshevPsi_le (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  have h_log : Real.log (lcmRange n) ≤ Real.log (4 ^ n) := by
    gcongr;
    · exact_mod_cast lcmRange_pos n hn;
    · exact_mod_cast lcmRange_le_four_pow n hn;
  rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, pow_right_comm ] at h_log ; norm_num at *;
  rw [ chebyshevPsi_eq_log_lcmRange n hn ] ; linarith

/-! # S(n) Upper Bound -/

/-- S(n) ≤ (log(n!) + ψ(n)) / n -/
lemma sumS_le_basic (n : ℕ) (hn : 2 ≤ n) :
    sumS n ≤ (Real.log (n.factorial) + chebyshevPsi n) / n := by
  -- By the properties of logarithms and the definition of S(n), we can rewrite the inequality.
  have h_rewrite : ∑ m ∈ Finset.Icc 2 n, (vonMangoldt m / m : ℝ) * n ≤ Real.log (Nat.factorial n) + ∑ m ∈ Finset.Icc 1 n, vonMangoldt m := by
    -- We'll use that $\sum_{m=1}^n \Lambda(m) \left\lfloor \frac{n}{m} \right\rfloor = \log(n!)$.
    have h_log_factorial : ∑ m ∈ Finset.Icc 1 n, (vonMangoldt m : ℝ) * Nat.floor (n / m) = Real.log (Nat.factorial n) := by
      -- By definition of von Mangoldt function, we know that $\sum_{d \mid m} \Lambda(d) = \log m$.
      have h_von_mangoldt : ∀ m : ℕ, 1 ≤ m → ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = Real.log m := by
        exact fun m a => vonMangoldt_sum;
      -- Applying the definition of von Mangoldt function to the sum.
      have h_sum_von_mangoldt : ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = ∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d : ℝ) * Nat.floor (n / d) := by
        have h_sum_von_mangoldt : ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = ∑ d ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d : ℝ) * (if d ∣ m then 1 else 0) := by
          rw [ Finset.sum_comm, Finset.sum_congr rfl ];
          simp +zetaDelta at *;
          intro x hx₁ hx₂; rw [ ← Finset.sum_filter ] ; congr; ext; simp +decide [ Nat.mem_divisors ] ;
          exact ⟨ fun h => ⟨ ⟨ Nat.pos_of_dvd_of_pos h.1 hx₁, Nat.le_trans ( Nat.le_of_dvd hx₁ h.1 ) hx₂ ⟩, h.1 ⟩, fun h => ⟨ h.2, by linarith ⟩ ⟩;
        simp_all +decide [ Finset.sum_ite ];
        refine' Finset.sum_congr rfl fun x hx => _;
        rw [ mul_comm, show Finset.filter ( fun y => x ∣ y ) ( Finset.Icc 1 n ) = Finset.image ( fun y => x * y ) ( Finset.Icc 1 ( n / x ) ) from ?_, Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( by linarith [ Finset.mem_Icc.mp hx ] ) h ];
        · norm_num;
        · ext y; simp [Finset.mem_image];
          exact ⟨ fun h => ⟨ y / x, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hx |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hx |>.1 ], by nlinarith [ Finset.mem_Icc.mp hx |>.2, Nat.div_mul_le_self n x ] ⟩, by simp +decide ⟩ ⟩;
      rw [ ← h_sum_von_mangoldt, Finset.sum_congr rfl fun m hm => h_von_mangoldt m <| Finset.mem_Icc.mp hm |>.1 ];
      erw [ ← Real.log_prod ] <;> norm_cast <;> norm_num;
      · erw [ ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial ];
      · grind;
    -- Applying the inequality $\frac{n}{m} \leq \left\lfloor \frac{n}{m} \right\rfloor + 1$ to each term in the sum, we get:
    have h_ineq : ∀ m ∈ Finset.Icc 2 n, (vonMangoldt m : ℝ) * (n / m) ≤ (vonMangoldt m : ℝ) * Nat.floor (n / m) + (vonMangoldt m : ℝ) := by
      intros m hm
      have h_floor : (n / m : ℝ) ≤ Nat.floor (n / m) + 1 := by
        rw [ div_le_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod n m, Nat.mod_lt n ( by linarith [ Finset.mem_Icc.mp hm ] : 0 < m ), Nat.lt_floor_add_one ( n / m ) ];
      simpa only [ mul_add, mul_one ] using mul_le_mul_of_nonneg_left h_floor <| by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ;
    refine le_trans ( Finset.sum_le_sum fun m hm => by convert h_ineq m hm using 1 ; ring ) ?_;
    rw [ ← h_log_factorial, Finset.sum_add_distrib ];
    exact add_le_add ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ) fun _ _ _ => mul_nonneg ( by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ) ( Nat.cast_nonneg _ ) ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ) fun _ _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg );
  convert div_le_div_of_nonneg_right h_rewrite ( Nat.cast_nonneg n ) using 1;
  · rw [ Finset.sum_div _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ mul_div_cancel_right₀ _ ( by positivity ) ] ;
  · unfold chebyshevPsi;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num

/-- log(n!) ≤ n*log(n) - n + 1 + log(n) -/
lemma log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≤ n * Real.log n - n + 1 + Real.log n := by
  induction hn <;> simp_all +decide [ Nat.factorial_succ ];
  rw [ Real.log_mul ( by positivity ) ( by positivity ), add_comm ];
  have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( ↑‹ℕ› : ℝ ) / ( ↑‹ℕ› + 1 ) );
  rw [ Real.log_div ] at this <;> first | positivity | nlinarith [ mul_div_cancel₀ ( ( ↑‹ℕ› : ℝ ) : ℝ ) ( by positivity : ( ↑‹ℕ› + 1 : ℝ ) ≠ 0 ) ] ;

lemma sumS_le_logn_plus (n : ℕ) (hn : 200 ≤ n) :
    sumS n ≤ Real.log n + 0.418 := by
  -- By combining the results from the previous steps, we conclude the proof.
  have h_final : Real.log (n.factorial) + chebyshevPsi n ≤ n * Real.log n + 2 * n * Real.log 2 - n + 1 + Real.log n := by
    linarith [ log_factorial_le n ( by linarith ), chebyshevPsi_le n ( by linarith ) ];
  -- Divide both sides by $n$ and simplify the expression.
  have h_div : sumS n ≤ Real.log n + 2 * Real.log 2 - 1 + (Real.log n + 1) / n := by
    convert sumS_le_basic n ( by linarith ) |> le_trans <| div_le_div_of_nonneg_right ( h_final ) ( Nat.cast_nonneg _ ) using 1 ; ring_nf;
    simpa [ show n ≠ 0 by linarith ] using by ring;
  -- We'll use that $Real.log n + 1 \leq Real.log 200 + 1$ for $n \geq 200$.
  have h_log_bound : (Real.log n + 1) / n ≤ (Real.log 200 + 1) / 200 := by
    rw [ div_le_div_iff₀ ] <;> try positivity;
    have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) / 200 );
    rw [ Real.log_div ] at this <;> norm_num at * <;> nlinarith [ ( by norm_cast : ( 200 :ℝ ) ≤ n ), Real.le_log_iff_exp_le ( by positivity : ( 0 :ℝ ) < 200 ) |>.2 <| show ( Real.exp 1 :ℝ ) ≤ 200 by exact le_of_lt <| Real.exp_one_lt_d9.trans_le <| by norm_num ];
  -- We'll use that $Real.log 200 < 5.3$.
  have h_log_200 : Real.log 200 < 5.3 := by
    norm_num [ Real.log_lt_iff_lt_exp ];
    -- We can raise both sides to the power of 10 to remove the fraction.
    suffices h_exp : (200 : ℝ) ^ 10 < Real.exp 53 by
      contrapose! h_exp;
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 10 );
    have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 53 = ( Real.exp 1 ) ^ 53 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_lt_of_le ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ );
  have := Real.log_two_lt_d9 ; norm_num at * ; linarith

/-! # Tail bound -/

/-- -log P(n) ≤ T(n) + 1/10 via log series truncation -/
lemma neg_log_prodP_le_sumT_plus (n : ℕ) (hn : 200 ≤ n) :
    -Real.log (prodP n) ≤ sumT n + 1/10 := by
  -- Let's rewrite the sum in terms of the prime number theorem and the bound we have.
  have h_sum_bound : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (-Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)) ≤ 1 / 10 := by
    -- For each prime $p$, the tail $\sum_{k > \lfloor \log_p n \rfloor} \frac{1}{k p^k}$ is bounded by $\frac{1}{(K+1)(p-1)p^K}$ where $K = \lfloor \log_p n \rfloor$.
    have h_tail_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k) ≤ 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) := by
      intro p hp
      have h_tail_bound : -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k) ≤ ∑' k : ℕ, 1 / ((Nat.log p n + k + 1) * (p : ℝ) ^ (Nat.log p n + k + 1)) := by
        have h_tail_bound : -Real.log (1 - 1 / (p : ℝ)) = ∑' k : ℕ, 1 / ((k + 1) * (p : ℝ) ^ (k + 1)) := by
          have := @Real.hasSum_pow_div_log_of_abs_lt_one ( 1 / ( p : ℝ ) ) ?_ <;> norm_num at *;
          · exact this.tsum_eq.symm ▸ rfl;
          · exact inv_lt_one_of_one_lt₀ <| mod_cast hp.2.one_lt;
        erw [ h_tail_bound, ← Summable.sum_add_tsum_nat_add ( Nat.log p n ) ];
        · erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ add_comm, add_left_comm, add_assoc ];
          norm_num [ Finset.sum_range_succ' ];
        · norm_num +zetaDelta at *;
          exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun k => mul_le_of_le_one_right ( by positivity ) <| inv_le_one_of_one_le₀ <| by linarith ) <| by simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_of_lt_one ( by positivity ) <| inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.2 hp.2.one_lt;
      -- We'll use the fact that $\sum_{k=K+1}^{\infty} \frac{1}{k p^k} \leq \frac{1}{(K+1)p^K} \sum_{k=0}^{\infty} \frac{1}{p^k}$.
      have h_sum_bound : ∑' k : ℕ, 1 / ((Nat.log p n + k + 1) * (p : ℝ) ^ (Nat.log p n + k + 1)) ≤ 1 / ((Nat.log p n + 1) * (p : ℝ) ^ (Nat.log p n + 1)) * ∑' k : ℕ, (1 / (p : ℝ)) ^ k := by
        rw [ ← tsum_mul_left ];
        refine' Summable.tsum_le_tsum _ _ _;
        · intro i; rw [ div_pow ] ; rw [ div_mul_div_comm ] ; rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> norm_num;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
        · norm_num +zetaDelta at *;
          exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun k => mul_le_of_le_one_right ( by positivity ) <| inv_le_one_of_one_le₀ <| by linarith ) <| by simpa using summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr hp.2.one_lt ) |> Summable.comp_injective <| by intros a b; aesop;
        · exact Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
      convert h_tail_bound.trans h_sum_bound using 1;
      rw [ tsum_geometric_of_lt_one ( by positivity ) ( by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) ] ; ring_nf;
      rw [ ← mul_inv ] ; congr ; nlinarith only [ inv_mul_cancel_left₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ) ( p ^ Nat.log p n ), inv_mul_cancel₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ), show ( p : ℝ ) ≥ 2 by norm_cast; exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ;
    -- Split the sum into two parts: one for primes $p \leq 13$ and one for primes $p > 13$.
    have h_split_sum : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (-Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)) ≤ (∑ p ∈ Finset.filter Nat.Prime (Finset.range 14), 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n))) + (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 17 (n)), 1 / ((1 + 1) * (p - 1) * (p : ℝ) ^ 1)) := by
      refine le_trans ( Finset.sum_le_sum h_tail_bound ) ?_;
      have h_split_sum : Finset.filter Nat.Prime (Finset.range (n + 1)) ⊆ Finset.filter Nat.Prime (Finset.range 14) ∪ Finset.filter Nat.Prime (Finset.Icc 17 n) := by
        simp +decide [ Finset.subset_iff ];
        exact fun p hp₁ hp₂ => if h : p < 14 then Or.inl ⟨ h, hp₂ ⟩ else Or.inr ⟨ ⟨ not_lt.mp fun h' => by interval_cases p <;> trivial, hp₁ ⟩, hp₂ ⟩;
      refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_split_sum ?_ ) ?_;
      · exact fun _ _ _ => one_div_nonneg.mpr ( mul_nonneg ( mul_nonneg ( by positivity ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ) ( by positivity ) );
      · rw [ Finset.sum_union ];
        · gcongr;
          all_goals norm_num at *;
          any_goals linarith [ Nat.Prime.one_lt ( by tauto ) ];
          · exact mul_pos ( mul_pos two_pos ( sub_pos.mpr ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ) ( Nat.cast_pos.mpr ( by linarith ) );
          · exact mul_nonneg ( by positivity ) ( sub_nonneg_of_le ( mod_cast Nat.Prime.pos ( by tauto ) ) );
          · exact Nat.le_log_of_pow_le ( by linarith ) ( by linarith );
          · exact Nat.le_log_of_pow_le ( by linarith ) ( by linarith );
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
    -- For primes $p \leq 13$, we can bound the sum individually.
    have h_small_primes : ∑ p ∈ Finset.filter Nat.Prime (Finset.range 14), 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) ≤ 1 / 50 := by
      norm_num [ Finset.sum_filter, Finset.sum_range_succ ];
      -- Since $n \geq 200$, we have $\log_2 n \geq 7$, $\log_3 n \geq 4$, $\log_5 n \geq 3$, $\log_7 n \geq 2$, $\log_{11} n \geq 2$, and $\log_{13} n \geq 2$.
      have h_log_bounds : Nat.log 2 n ≥ 7 ∧ Nat.log 3 n ≥ 4 ∧ Nat.log 5 n ≥ 3 ∧ Nat.log 7 n ≥ 2 ∧ Nat.log 11 n ≥ 2 ∧ Nat.log 13 n ≥ 2 := by
        exact ⟨ Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ⟩;
      refine' le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 2 n : ℝ ) + 1 ≥ 8 by norm_cast; linarith ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 3 n : ℝ ) + 1 ≥ 5 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 5 n : ℝ ) + 1 ≥ 4 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 7 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 11 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 13 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) _ ; norm_num;
      exact le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.1 ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.2.2 ) ) ( by positivity ) ) ) ( by norm_num );
    -- For primes $p > 13$, we can bound the sum using the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)} \leq \frac{1}{32}$.
    have h_large_primes : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 17 (n)), 1 / ((1 + 1) * (p - 1) * (p : ℝ)) ≤ 1 / 32 := by
      -- We'll use the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)} \leq \frac{1}{32}$.
      have h_large_primes_bound : ∑ p ∈ Finset.Icc 17 n, (1 / ((p - 1) * (p : ℝ))) ≤ 1 / 16 := by
        -- We'll use the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)}$ is a telescoping series.
        have h_telescoping : ∀ m : ℕ, 17 ≤ m → ∑ p ∈ Finset.Icc 17 m, (1 / ((p - 1) * (p : ℝ))) = 1 / 16 - 1 / (m : ℝ) := by
          intro m hm; induction hm <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
          rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Ioc 16 _, _ = _› ] ; norm_num;
          -- Combine and simplify the terms on the left-hand side.
          field_simp
          ring;
        exact h_telescoping n ( by linarith ) ▸ sub_le_self _ ( by positivity );
      norm_num [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] at *;
      exact le_trans ( mul_le_mul_of_nonneg_right ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( inv_nonneg.2 ( sub_nonneg.2 ( Nat.one_le_cast.2 ( by linarith [ Finset.mem_Icc.1 ‹_› ] ) ) ) ) ) ( by norm_num ) ) ( by linarith );
    norm_num at * ; linarith;
  convert add_le_add_left h_sum_bound ( ∑ p ∈ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ), ∑ k ∈ Finset.Icc 1 ( Nat.log p n ), 1 / ( k * ( p : ℝ ) ^ k ) ) using 1;
  · unfold prodP; rw [ Real.log_prod ] <;> norm_num;
    exact fun p hp hp' => sub_ne_zero_of_ne <| by aesop;
  · rw [ add_comm, sumT ];
    -- Let's rewrite the sum $\sum_{m=2}^n \frac{\Lambda(m)}{m \log m}$ using the definition of $\Lambda$.
    have h_sum_eq : ∑ m ∈ Finset.Icc 2 n, (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (ArithmeticFunction.vonMangoldt (p^k) : ℝ) / (p^k * Real.log (p^k)) := by
      have h_sum_eq : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 2 n) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => Finset.image (fun k => p^k) (Finset.Icc 1 (Nat.log p n))) := by
        ext m; simp [ArithmeticFunction.vonMangoldt];
        constructor;
        · rintro ⟨ ⟨ hm₁, hm₂ ⟩, hm₃, hm₄, hm₅, hm₆ ⟩;
          obtain ⟨ p, k, hp, hk, rfl ⟩ := hm₃;
          exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hm₂ ⟩, rfl ⟩;
        · rintro ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
          exact ⟨ ⟨ one_lt_pow₀ hp₂.one_lt ( by linarith ), Nat.pow_le_of_le_log ( by linarith ) hk₂ ⟩, hp₂.isPrimePow.pow ( by linarith ), Nat.ne_of_gt ( Nat.minFac_pos _ ), ne_of_gt ( one_lt_pow₀ hp₂.one_lt ( by linarith ) ), by linarith ⟩;
      have h_sum_eq : ∑ m ∈ Finset.Icc 2 n, (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) = ∑ m ∈ Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 2 n), (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) := by
        rw [ Finset.sum_filter_of_ne ] ; aesop;
      rw [ h_sum_eq, ‹ { m ∈ Icc 2 n | Λ m ≠ 0 } = _ ›, Finset.sum_biUnion ];
      · exact Finset.sum_congr rfl fun p hp => by rw [ Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) hab ] ; norm_cast;
      · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
        intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
    rw [ h_sum_eq ];
    refine' congr rfl ( Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun k hk => _ );
    rw [ ArithmeticFunction.vonMangoldt_apply ];
    rw [ if_pos ];
    · rw [ Nat.pow_minFac ] <;> norm_num [ Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ];
      · rw [ Nat.Prime.minFac_eq ( Finset.mem_filter.mp hp |>.2 ) ] ; ring_nf;
        rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ), one_mul ];
      · grind;
    · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp hp |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp hk ] )

/-! ### Helper lemmas for sumT_sub_199_bound -/

private lemma log_factorial_ge' (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≥ n * Real.log n - n + 1 := by
  induction hn <;> simp_all +decide [ Nat.factorial ]
  rw [ Real.log_mul ( by positivity ) ( by positivity ) ]
  have h_log : ∀ m : ℕ, 1 ≤ m → Real.log (m + 1) ≤ Real.log m + 1 / m := by
    intro m hm; rw [ Real.log_le_iff_le_exp ( by positivity ) ] ; rw [ Real.exp_add, Real.exp_log ( by positivity ) ]
    nlinarith [ Real.add_one_le_exp ( 1 / ( m : ℝ ) ), one_div_mul_cancel ( by positivity : ( m : ℝ ) ≠ 0 ) ]
  have := h_log _ ‹_›; norm_num at *; nlinarith [ inv_mul_cancel₀ ( by positivity : ( ( Nat.cast:ℕ →ℝ ) ‹_› ) ≠ 0 ) ]

private lemma sumS_ge_log_sub_one (n : ℕ) (hn : 2 ≤ n) :
    sumS n ≥ Real.log n - 1 := by
  have h_sum_floor : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m * Nat.floor (n / m) = Real.log (Nat.factorial n) := by
    have h_sum_floor : ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = Real.log (Nat.factorial n) := by
      have h_sum_floor : ∀ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = Real.log k := by
        exact fun _ _ => vonMangoldt_sum
      rw [ Finset.sum_congr rfl h_sum_floor ]
      exact Nat.recOn n ( by norm_num ) fun n ih => by simp_all +decide [ Nat.factorial_succ, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; linarith
    have h_interchange : ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, vonMangoldt d * (if d ∣ k then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ]
      simp +contextual [ Finset.sum_ite ]
      intro x hx₁ hx₂; rw [ ← Finset.sum_subset ( show x.divisors ⊆ Finset.filter ( fun d => d ∣ x ) ( Finset.Icc 1 n ) from fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_divisors hy, Nat.le_trans ( Nat.le_of_dvd hx₁ <| Nat.dvd_of_mem_divisors hy ) hx₂ ⟩, Nat.dvd_of_mem_divisors hy ⟩ ) ] ; aesop
    have h_inner : ∀ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (if d ∣ k then 1 else 0) = Nat.floor (n / d) := by
      intros d hd
      have h_divisors : Finset.filter (fun k => d ∣ k) (Finset.Icc 1 n) = Finset.image (fun k => d * k) (Finset.Icc 1 (n / d)) := by
        ext k; simp [Finset.mem_image]
        exact ⟨ fun h => ⟨ k / d, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hd |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hd |>.1 ], by nlinarith [ Finset.mem_Icc.mp hd |>.2, Nat.div_mul_le_self n d ] ⟩, by norm_num ⟩ ⟩
      simp_all +decide [ Finset.sum_ite ]
      rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( by linarith ) hxy ] ; aesop
    simp_all +decide [ Finset.sum_ite ]
    exact Eq.trans ( Finset.sum_congr rfl fun x hx => by rw [ h_inner x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ] ; ring ) h_sum_floor
  have h_floor_le : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m * Nat.floor (n / m) ≤ n * ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) := by
    rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_le_sum fun x hx => _ ; rcases eq_or_ne x 0 with rfl | hx' <;> simp_all +decide ; ring_nf
    rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( by rw [ ← div_eq_mul_inv ] ; exact ( by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast; linarith [ Nat.div_mul_le_self n x ] ) ) ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ) ) ) ) ) ) )
  have h_sum_eq : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) = sumS n := by
    rw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] ; aesop
  nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ), log_factorial_ge' n ( by linarith ) ]

private lemma div_sub_le_log_sub' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have h_mul : b - a ≤ b * (Real.log b - Real.log a) := by
    have := Real.log_le_sub_one_of_pos ( div_pos ha ( show 0 < b by linarith ) )
    rw [ Real.log_div ] at this <;> nlinarith [ mul_div_cancel₀ a ( by linarith : b ≠ 0 ) ]
  rwa [ div_le_iff₀' ( by linarith ) ]

private lemma sum_log_ratio_le_log_log' (a n : ℕ) (ha : 3 ≤ a) (hn : a ≤ n) :
    ∑ m ∈ Finset.Ico a n,
      (Real.log (↑m + 1) - Real.log m) / Real.log (↑m + 1) ≤
    Real.log (Real.log n) - Real.log (Real.log a) := by
  have h_term : ∀ m ∈ Finset.Ico a n, (Real.log (m + 1) - Real.log m) / Real.log (m + 1) ≤ Real.log (Real.log (m + 1)) - Real.log (Real.log m) := by
    intro m hm
    rw [ ← Real.log_div ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ]
    convert Real.one_sub_inv_le_log_of_pos _ using 1
    · rw [ inv_div, sub_div, div_self <| ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ]
    · exact div_pos ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) )
  convert Finset.sum_le_sum h_term ; induction hn <;> simp_all +decide [ Finset.sum_Ico_succ_top ]
  rename_i k hk ih; linarith [ ih fun m hm₁ hm₂ => h_term m hm₁ ( by linarith ) ]

private lemma log_200_ge' : Real.log 200 ≥ 1418 / 270 := by
  have h_log_200 : Real.log 200 = 3 * Real.log 2 + 2 * Real.log 5 := by
    norm_num [ ← Real.log_rpow, ← Real.log_mul ]
  rw [ h_log_200, show ( 5 : ℝ ) = 2 ^ 2 * 1.25 by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf <;> norm_num
  have := Real.log_two_gt_d9 ; norm_num at * ; have := Real.log_inv ( 5 / 4 ) ; norm_num at * ; linarith [ Real.log_le_sub_one_of_pos ( show 0 < 4 / 5 by norm_num ) ]

private lemma abel_identity_sumT (n : ℕ) (hn : 200 ≤ n) :
    ∑ m ∈ Finset.Icc 200 n, (Λ m) / (m * Real.log m) = ((sumS n) - (sumS 199)) / Real.log n + ∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
  induction' hn with k hk
  · simp [sumS]
    rw [ show ( Finset.Icc 2 200 : Finset ℕ ) = Finset.Icc 2 199 ∪ { 200 } by decide, Finset.sum_union ] <;> norm_num ; ring
  · simp_all +decide [(Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)]
    rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Ioc 199 k, _ = _› ]
    rw [ Finset.sum_Ico_succ_top ( by linarith ), show sumS ( k + 1 ) = sumS k + Λ ( k + 1 ) / ( k + 1 : ℝ ) from ?_ ]
    · norm_num [ div_eq_mul_inv ] ; ring
    · exact_mod_cast Finset.sum_Ioc_succ_top ( by linarith ) _

/-- T(n) - T(199) ≤ log(log n) - log(log 199) + 27/100, using Abel summation and S(m) ≤ log m + 0.418 -/
lemma sumT_sub_199_bound (n : ℕ) (hn : 200 ≤ n) :
    sumT n ≤ sumT 199 + Real.log (Real.log ↑n) - Real.log (Real.log 199) + 27/100 := by
  -- Step 1: Split sumT
  have h_split : sumT n = sumT 199 + ∑ m ∈ Finset.Icc 200 n, vonMangoldt m / (m * Real.log m) := by
    unfold sumT; erw [ Finset.sum_Ico_consecutive ] <;> norm_cast ; linarith
  rw [h_split]
  -- Step 2: Abel summation identity
  have h_identity := abel_identity_sumT n hn
  -- Step 3: Bound the Abel sum terms
  have h_bound : (∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1))) ≤ (∑ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1)))) := by
    refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_right ?_ ?_ <;> norm_num at *
    · have := sumS_le_logn_plus m ( by linarith ) ; ( have := sumS_ge_log_sub_one 199 ( by norm_num ) ; ( norm_num at * ; linarith ) )
    · exact inv_anti₀ ( Real.log_pos <| by norm_cast; linarith ) ( Real.log_le_log ( by norm_cast; linarith ) <| by linarith )
  -- Step 4: Expand and telescope the sum
  have h_expand : ∑ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1))) = ∑ m ∈ Finset.Ico 200 n, ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) + (1.418 - Real.log 199) * (1 / Real.log 200 - 1 / Real.log n) := by
    have h_expand : ∀ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1))) = ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) + (1.418 - Real.log 199) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
      intro m hm; ring_nf
      rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ) ] ; ring
    rw [ Finset.sum_congr rfl h_expand, Finset.sum_add_distrib ]
    norm_num [ Finset.sum_Ico_eq_sum_range ]
    rw [ ← Finset.mul_sum _ _ _ ]
    exact congrArg _ ( by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast [ Nat.cast_sub hn ] <;> ring_nf )
  -- Step 5: Apply log ratio telescoping bound
  have h_log_ratio : ∑ m ∈ Finset.Ico 200 n, ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) ≤ Real.log (Real.log n) - Real.log (Real.log 200) := by
    convert sum_log_ratio_le_log_log' 200 n ( by norm_num ) hn using 1
  -- Step 6: Bound the boundary term
  have h_sumS_le : (sumS n - sumS 199) / Real.log n ≤ (Real.log n + 0.418 - (Real.log 199 - 1)) / Real.log n := by
    gcongr
    · exact sumS_le_logn_plus n hn
    · exact sumS_ge_log_sub_one 199 ( by norm_num )
  -- Step 7: Numerical bound
  have h_num : 1 + (1.418 - Real.log 199) / Real.log 200 + Real.log (Real.log 199) - Real.log (Real.log 200) ≤ 27 / 100 := by
    have h_log_diff : Real.log (Real.log 200) - Real.log (Real.log 199) ≥ (Real.log 200 - Real.log 199) / Real.log 200 := by
      exact div_sub_le_log_sub' ( show 0 < Real.log 199 by positivity ) ( show Real.log 199 ≤ Real.log 200 by gcongr ; norm_num )
    ring_nf at *
    nlinarith [ inv_mul_cancel₀ ( show Real.log 200 ≠ 0 by positivity ), Real.log_pos ( show 199 > 1 by norm_num ), Real.log_lt_log ( by norm_num ) ( show 200 > 199 by norm_num ), show Real.log 200 ≥ 1418 / 270 from log_200_ge' ]
  -- Step 8: Combine all bounds
  ring_nf at *
  nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ), inv_pos.mpr ( Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ) ), Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ), Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ]

/-- Computational upper bound on T(199) -/
lemma sumT_199_lt : sumT 199 < 23/10 := by
  -- By definition of sumT, we can rewrite the sum as a sum over prime powers.
  have h_sum_prime_powers : ∀ n : ℕ, sumT n = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (1 / (p^k * k : ℝ)) := by
    intro n
    have h_sumT_prime_powers : ∀ m ∈ Finset.Icc 2 n, vonMangoldt m = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (if m = p^k then Real.log p else 0) := by
      intro m hm
      by_cases hm_prime_power : ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ m = p^k ∧ p^k ≤ n;
      · obtain ⟨ p, k, hp, hk, rfl, hk' ⟩ := hm_prime_power; simp +decide [Finset.sum_ite] ;
        rw [ Finset.sum_eq_single p ];
        · rw [ Finset.card_eq_one.mpr ] <;> norm_num [ hp, hk ];
          · grind +suggestions;
          · exact ⟨ k, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hk, Nat.le_log_of_pow_le hp.one_lt hk' ⟩, rfl ⟩, fun x hx => Nat.pow_right_injective hp.one_lt <| Finset.mem_filter.mp hx |>.2.symm ⟩ ⟩;
        · intro q hq hqp; simp_all +decide [ Finset.ext_iff ] ;
          exact Or.inl fun a ha₁ ha₂ ha₃ => hqp <| by have := congr_arg ( ·.factorization ( q : ℕ ) ) ha₃; norm_num at this; have := congr_arg ( ·.factorization ( p : ℕ ) ) ha₃; norm_num at this; aesop;
        · exact fun h => False.elim <| h <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.two_le, by linarith [ pow_le_pow_right₀ hp.one_lt.le hk ] ⟩, hp ⟩;
      · rw [ ArithmeticFunction.vonMangoldt_apply ];
        rw [ if_neg ];
        · exact Eq.symm ( Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun k hk => if_neg fun h => hm_prime_power ⟨ p, k, Finset.mem_filter.mp hp |>.2, Finset.mem_Icc.mp hk |>.1, h, by linarith [ Finset.mem_Icc.mp hm, Finset.mem_Icc.mp hk |>.2, Nat.pow_log_le_self p ( show m ≠ 0 by linarith [ Finset.mem_Icc.mp hm ] ) ] ⟩ );
        · contrapose! hm_prime_power;
          rw [ isPrimePow_nat_iff ] at hm_prime_power ; aesop;
    -- By interchanging the order of summation, we can rewrite the sum.
    have h_interchange : ∑ m ∈ Finset.Icc 2 n, (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (if m = p^k then Real.log p else 0)) / (m * Real.log m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (Real.log p) / (p^k * Real.log (p^k)) := by
      simp +decide only [Finset.sum_div _ _ _];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro p hp; rw [ Finset.sum_comm ] ; simp +decide [ div_eq_mul_inv ] ;
      exact Finset.sum_congr rfl fun x hx => if_pos ⟨ le_trans ( Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ) ( Nat.le_self_pow ( by linarith [ Finset.mem_Icc.mp hx ] ) _ ), Nat.pow_le_of_le_log ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ) ( by linarith [ Finset.mem_Icc.mp hx ] ) ⟩;
    convert h_interchange using 2;
    · exact Finset.sum_congr rfl fun x hx => h_sumT_prime_powers x hx ▸ rfl;
    · norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      exact Finset.sum_congr rfl fun _ _ => by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( by aesop ) ) ) ) ) ] ; ring;
  rw [ h_sum_prime_powers ];
  norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
  rw [ show ( Finset.filter Nat.Prime ( Finset.Ioc 1 199 ) ) = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199 } by decide ] ; simp +decide ;
  norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *

/-- Lower bound on log(log 199) -/
lemma log_log_199_gt : Real.log (Real.log 199) > 163/100 := by
  -- We'll use that $Real.log 199 > 5.11$.
  have h_log_199 : Real.log 199 > 5.11 := by
    norm_num [ Real.lt_log_iff_exp_lt ];
    -- We can raise both sides to the power of 100 to remove the fraction.
    suffices h_exp : Real.exp 511 < 199 ^ 100 by
      contrapose! h_exp;
      exact le_trans ( pow_le_pow_left₀ ( by norm_num ) h_exp 100 ) ( by norm_num [ ← Real.exp_nat_mul ] );
    have := Real.exp_one_lt_d9.le;
    -- We can raise both sides to the power of 511 to remove the fraction.
    have : Real.exp 511 ≤ (2.7182818286 : ℝ) ^ 511 := by
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) this _ );
    grind;
  refine' lt_of_lt_of_le _ ( Real.log_le_log ( by positivity ) h_log_199.le );
  rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
  have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 163 = ( Real.exp 1 ) ^ 163 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num )

lemma neg_log_prodP_bound (n : ℕ) (hn : 200 ≤ n) :
    -Real.log (prodP n) < Real.log (Real.log n) + 1.095 := by
  have h1 := neg_log_prodP_le_sumT_plus n hn
  have h2 := sumT_sub_199_bound n hn
  have h3 := sumT_199_lt
  have h4 := log_log_199_gt
  linarith

/-! # Finite Check -/

lemma prodP_le_of_le {m n : ℕ} (h : m ≤ n) : prodP n ≤ prodP m := by
  unfold prodP;
  rw [ ← Finset.prod_sdiff ( Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ h ) ];
  exact mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) <| Finset.prod_le_one ( fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => sub_le_self _ <| by positivity;

lemma mertens_finite_check (n : ℕ) (hn3 : 3 ≤ n) (hn199 : n ≤ 199) :
    1 / (3 * Real.log n) ≤ prodP n := by
  by_cases hn : n ≤ 10;
  · interval_cases n <;> norm_num [ Finset.prod_filter, Finset.prod_range_succ, prodP ];
    any_goals rw [ inv_mul_le_iff₀ ( by positivity ) ];
    any_goals rw [ inv_le_comm₀ ] <;> norm_num [ Real.le_log_iff_exp_le ];
    any_goals rw [ ← div_le_iff₀ ] <;> norm_num [ Real.le_log_iff_exp_le ];
    any_goals positivity;
    any_goals have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 5 : ℝ ) / 4 = 1 + 1 / 4 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 1 / 4 ), Real.exp_neg ( 1 / 4 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 1 / 4 ) ) ), Real.add_one_le_exp ( 1 / 4 ), Real.add_one_le_exp ( - ( 1 / 4 ) ) ];
    any_goals have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 35 / 24 : ℝ ) = 1 + 11 / 24 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 11 / 24 ), Real.exp_neg ( 11 / 24 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 11 / 24 ) ) ), Real.add_one_le_exp ( 11 / 24 ), Real.add_one_le_exp ( - ( 11 / 24 ) ) ];
    · exact Real.exp_one_lt_d9.le.trans <| by norm_num;
    · exact Real.exp_one_lt_d9.le.trans ( by norm_num );
  · by_cases hn : n ≤ 30;
    · -- For $11 \leq n \leq 30$, we use the fact that $prodP(n) \geq prodP(30)$ and $prodP(30) \geq 1/7$.
      have h_prod_bound : prodP n ≥ prodP 30 := by
        exact prodP_le_of_le hn
      have h_prod_30 : prodP 30 ≥ 1 / 7 := by
        unfold prodP; norm_num [ Finset.prod_filter, Finset.prod_range_succ ] ;
      have h_log_bound : 7 ≤ 3 * Real.log 11 := by
        norm_num [ ← Real.log_rpow, Real.le_log_iff_exp_le ] at *;
        have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 7 = ( Real.exp 1 ) ^ 7 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
      have h_final : 1 / (3 * Real.log n) ≤ 1 / 7 := by
        exact one_div_le_one_div_of_le ( by positivity ) ( by linarith [ Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≥ 11 by norm_cast; linarith ) ] )
      exact le_trans h_final (le_trans h_prod_30 h_prod_bound);
    · have h_prodP_199 : prodP 199 ≥ 1 / 10 := by
        unfold prodP; norm_num;
        norm_num [ Finset.prod_filter, Finset.prod_range_succ ];
      have h_log_bound : Real.log n ≥ 10 / 3 := by
        rw [ ge_iff_le, div_le_iff₀' ] <;> norm_num;
        rw [ ← Real.log_rpow, Real.le_log_iff_exp_le ] <;> norm_cast <;> try linarith;
        · exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 10 = ( Real.exp 1 ) ^ 10 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) ( Nat.cast_le.mpr ( Nat.pow_le_pow_left ( show n ≥ 31 by linarith ) 3 ) );
        · positivity;
      exact le_trans ( by rw [ div_le_iff₀ ] <;> linarith ) ( h_prodP_199.trans ( prodP_le_of_le ( by linarith ) ) )

/-! # Main Theorem -/

theorem mertens_third_theorem (n : ℕ) (hn : 3 ≤ n) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  by_cases hn2 : n ≥ 200;
  · have := neg_log_prodP_bound n hn2;
    -- Exponentiating both sides, we get $prodP n > \frac{1}{3 \log n}$.
    have h_exp : prodP n > 1 / (3 * Real.log n) := by
      have h_exp : Real.log (prodP n) > -Real.log (3 * Real.log n) := by
        rw [ Real.log_mul ] <;> norm_num;
        · have h_log3 : Real.log 3 > 1.095 := by
            norm_num [ Real.log_lt_log ];
            rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 219 = ( Real.exp 1 ) ^ 219 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
          linarith;
        · grind;
      rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ] at h_exp;
      · simpa [ Real.exp_neg, Real.exp_log ( show 0 < 3 * Real.log n by exact mul_pos zero_lt_three ( Real.log_pos ( by norm_cast; linarith ) ) ) ] using h_exp;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Finset.mem_filter.mp hp, Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    exact h_exp.le;
  · -- Apply the finite check lemma to conclude the proof.
    apply mertens_finite_check n hn (by linarith)

end

end MertensThird

section BipartiteC4

/-! Kővári–Sós–Turán bipartite C₄-free bound: e ≤ t + s√t. -/

open Finset BigOperators

/-! ### K_{2,2}-free bipartite graph bound -/

section C4Bound

/-- Kővári–Sós–Turán: no K_{2,2} implies e ≤ t + s√t. -/
theorem c4_free_bound_sqrt (s t e : ℕ) (ht : 0 < t)
    (h : e * e ≤ t * e + t * s * (s - 1)) :
    (e : ℝ) ≤ t + s * Real.sqrt t := by
  -- From the hypothesis, we know that $(e : ℝ)^2 \leq t * e + t * s * (s - 1)$.
  have h_real : (e : ℝ)^2 ≤ t * e + t * s * (s - 1) := by
    cases s <;> norm_num at * ; norm_cast;
    · linarith;
    · norm_cast ; linarith;
  -- We want $(e : ℝ) \leq t + s * \sqrt{t}$. From $h_real$, we get $(e : ℝ)^2 \leq t * e + t * s * s$.
  have h_ineq : (e : ℝ)^2 ≤ t * e + t * s^2 := by
    nlinarith;
  nlinarith only [ show 0 ≤ ( s : ℝ ) * Real.sqrt t by positivity, Real.mul_self_sqrt ( Nat.cast_nonneg t ), h_ineq ]

/-- Consequence: if s² ≤ t, then e ≤ t + s². -/
theorem c4_free_bound_sq (s t e : ℕ)
    (hs2t : s * s ≤ t)
    (h : e * e ≤ t * e + t * s * (s - 1)) :
    e ≤ t + s * s := by
  rcases s with ( _ | s ) <;> simp_all +decide;
  · nlinarith;
  · nlinarith [ sq_nonneg ( e - t - ( s + 1 ) * ( s + 1 ) : ℤ ) ]

end C4Bound

end BipartiteC4

section BuchstabEstimate

/-
Proof of the Buchstab estimate using Dusart's PNT bounds.
-/

open Finset BigOperators Real

noncomputable section

open DistinctProducts in
/-- From Dusart's bounds, π(x) = x/log x + O(x/(log x)²) for large x. -/
lemma pi_approx_error :
    ∃ C > 0, ∃ X₀ : ℝ, ∀ x : ℝ, x ≥ X₀ →
      |((primesUpTo x).card : ℝ) - x / Real.log x| ≤ C * x / (Real.log x) ^ 2 := by
  use 4, by norm_num, 88789, fun x hx => ?_;
  refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
  · have := dusart_pi_upper x ( by linarith );
    refine' le_trans ( sub_le_sub_right this _ ) _;
    ring_nf;
    have h_log_x_ge_11 : Real.log x ≥ 11 := by
      rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ];
      exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 11 = ( Real.exp 1 ) ^ 11 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) hx;
    nlinarith [ show 0 < x * ( Real.log x ) ⁻¹ ^ 2 by positivity, show 0 < x * ( Real.log x ) ⁻¹ ^ 3 by positivity, mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by linarith : 1 < x ) ) ), pow_two_nonneg ( ( Real.log x ) ⁻¹ - 1 / 11 ) ];
  · have := dusart_pi_lower x hx
    have := dusart_pi_upper x ( by linarith )
    norm_num at *;
    ring_nf at *;
    nlinarith [ show 0 < x * ( log x ) ⁻¹ by exact mul_pos ( by positivity ) ( inv_pos.mpr ( Real.log_pos ( by linarith ) ) ), show 0 < x * ( log x ) ⁻¹ ^ 2 by exact mul_pos ( by positivity ) ( sq_pos_of_pos ( inv_pos.mpr ( Real.log_pos ( by linarith ) ) ) ), show 0 < x * ( log x ) ⁻¹ ^ 3 by exact mul_pos ( by positivity ) ( pow_pos ( inv_pos.mpr ( Real.log_pos ( by linarith ) ) ) 3 ) ]

/-
The number of primes in [k, n] in terms of primesUpTo. -/
lemma primes_Icc_eq_pi_diff (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    ((Finset.Icc k n).filter Nat.Prime).card =
    (primesUpTo (n : ℝ)).card - (primesUpTo ((k : ℝ) - 1)).card := by
  rw [ Nat.sub_eq_of_eq_add ];
  rw [ ← Finset.card_union_of_disjoint ];
  · congr with x ; simp_all +decide [ primesUpTo ];
    grind;
  · norm_num [ Finset.disjoint_left, primesUpTo ];
    intros; omega;

/-- sievePhi is at most 1 + primes + 1 when k² ≥ n (handles edge case k² = n). -/
lemma sievePhi_le_primes_plus_two (n k : ℕ) (hk : k * k ≥ n) (hk2 : 2 ≤ k) (hn : 1 ≤ n) :
    sievePhi n k ≤ 2 + ((Finset.Icc k n).filter Nat.Prime).card := by
  -- Let's consider the set of integers $m \in [1, n]$ with all prime factors $\ge k$.
  set S := ((Finset.Icc 1 n).filter (fun m => ∀ p ∈ m.primeFactors, k ≤ p));
  -- We'll use that $S \subseteq \{1\} \cup \{ \text{primes in } [k, n] \} \cup \{ k^2 \}$.
  have h_subset : S ⊆ {1} ∪ ((Finset.Icc k n).filter Nat.Prime) ∪ if k * k = n then {k * k} else ∅ := by
    intro m hm; by_cases hm1 : m = 1 <;> by_cases hm2 : Nat.Prime m <;> simp_all +decide ;
    · exact Or.inl ⟨ by aesop, by aesop ⟩;
    · -- Since $m$ is composite and not prime, it must have a prime factor $p$ such that $p \leq \sqrt{m}$.
      obtain ⟨p, hp_prime, hp_div⟩ : ∃ p, Nat.Prime p ∧ p ∣ m ∧ p ≤ Nat.sqrt m := by
        obtain ⟨ p, hp₁, hp₂ ⟩ := Nat.exists_prime_and_dvd hm1;
        obtain ⟨ q, rfl ⟩ := hp₂;
        exact ⟨ Nat.minFac ( p * q ), Nat.minFac_prime hm1, Nat.minFac_dvd _, by rw [ Nat.le_sqrt ] ; nlinarith [ Nat.minFac_le_of_dvd ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩ ) ( dvd_mul_right p q ), Nat.minFac_le_of_dvd ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩ ) ( dvd_mul_left q p ) ] ⟩;
      simp +zetaDelta at *;
      split_ifs <;> simp_all +decide [ Nat.le_sqrt ];
      · nlinarith [ hm.2 p hp_prime hp_div.1 ( by linarith ) ];
      · exact ‹¬k * k = n› ( by nlinarith [ hm.2 p hp_prime hp_div.1 ( by linarith ), Nat.Prime.two_le hp_prime ] );
  refine le_trans ( Finset.card_mono h_subset ) ?_;
  grind +revert

/-- sievePhi is at least 1 + primes (always, not just when k² > n). -/
lemma sievePhi_ge_one_plus_primes (n k : ℕ) (hk2 : 2 ≤ k) (hn : 1 ≤ n) :
    sievePhi n k ≥ 1 + ((Finset.Icc k n).filter Nat.Prime).card := by
  -- The set {1} ∪ {p ∈ [k, n] : p prime} is a subset of the set of numbers in [1, n] with all prime factors ≥ k.
  have h_subset : {1} ∪ (Finset.Icc k n).filter Nat.Prime ⊆ ((Finset.Icc 1 n).filter (fun m => ∀ p ∈ m.primeFactors, k ≤ p)) := by
    simp +decide [ Finset.subset_iff ];
    exact ⟨ ⟨ hn, by aesop ⟩, fun a ha₁ ha₂ ha₃ => ⟨ ⟨ by linarith, ha₂ ⟩, fun p hp₁ hp₂ hp₃ => by rw [ Nat.prime_dvd_prime_iff_eq ] at hp₂ <;> aesop ⟩ ⟩;
  refine' le_trans _ ( Finset.card_mono h_subset );
  rw [ Finset.card_union_of_disjoint ] <;> norm_num

/-- For x ≥ X₀ and the u ∈ [1, 2] case, ⌈y⌉² ≥ ⌊x⌋ (floor/ceiling of the constraint x ≤ y²). -/
lemma ceil_sq_ge_floor_of_log_ratio_le_two (x y : ℝ) (hx : x ≥ 4) (hy : y ≥ 2)
    (h1 : Real.log x / Real.log y ≤ 2) :
    ⌈y⌉₊ * ⌈y⌉₊ ≥ ⌊x⌋₊ := by
  -- From the given bounds on $\log_x y$, we derive the inequalities on $x$ and $y$.
  have log_bounds : Real.log x ≤ 2 * Real.log y := by
    rwa [ div_le_iff₀ ( Real.log_pos ( by linarith ) ) ] at h1
  have le_y : x ≤ y^2 := by
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_pow ] ; norm_num ; linarith;
  exact Nat.le_of_lt_succ <| by rw [ Nat.floor_lt' ] <;> norm_num ; nlinarith [ Nat.le_ceil y ] ;

end

end BuchstabEstimate

section BuchstabAnalysis

/-! Helper lemmas bridging sievePhi and the prime counting function. -/

open Finset BigOperators Real

noncomputable section

/-! ### Floor/ceiling PNT approximations -/

/-- ⌊x⌋/log⌊x⌋ approximates x/log x with error O(x/(log x)²). -/
lemma floor_div_log_approx (x : ℝ) (hx : x ≥ 4) :
    |(⌊x⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ) - x / Real.log x| ≤ 2 / Real.log x := by
  refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
  · rw [ sub_le_iff_le_add' ];
    rw [ ← add_div, div_le_div_iff₀ ] <;> try linarith [ Real.log_pos ( by linarith : 1 < x ) ];
    · have h_log_bound : Real.log x ≤ Real.log ⌊x⌋₊ + 1 / ⌊x⌋₊ := by
        rw [ Real.log_le_iff_le_exp, Real.exp_add, Real.exp_log ] <;> try linarith [ Nat.lt_floor_add_one x ];
        nlinarith [ Nat.lt_floor_add_one x, Real.add_one_le_exp ( 1 / ( ⌊x⌋₊ : ℝ ) ), one_div_mul_cancel ( show ( ⌊x⌋₊ : ℝ ) ≠ 0 by norm_cast; exact Nat.ne_of_gt <| Nat.floor_pos.mpr <| by linarith ) ];
      have h_log_bound : Real.log ⌊x⌋₊ ≥ 1 := by
        exact Real.le_log_iff_exp_le ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( ⌊x⌋₊ : ℝ ) ≥ 4 by exact_mod_cast Nat.le_floor <| by norm_num; linarith ] ;
      nlinarith [ Nat.floor_le ( show 0 ≤ x by linarith ), Nat.lt_floor_add_one x, one_div_mul_cancel ( show ( ⌊x⌋₊ : ℝ ) ≠ 0 by norm_cast; exact Nat.ne_of_gt <| Nat.floor_pos.mpr <| by linarith ) ];
    · exact Real.log_pos <| Nat.one_lt_cast.2 <| Nat.le_floor <| by norm_num; linarith;
  · -- Since $x \geq 4$, we have $\lfloor x \rfloor \geq 3$ and $\log x \geq \log 4 > 1$.
    have h_floor_ge_3 : 3 ≤ ⌊x⌋₊ := by
      exact Nat.le_floor <| mod_cast hx.trans' <| by norm_num;
    have h_log_ge_1 : 1 < Real.log x := by
      exact Real.lt_log_iff_exp_lt ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith ) );
    -- Since $x \geq 4$, we have $\lfloor x \rfloor \geq 3$ and $\log x \geq \log 4 > 1$. Also, $x-1 \leq \lfloor x \rfloor \leq x$.
    have h_bounds : (x : ℝ) / Real.log x - ⌊x⌋₊ / Real.log ⌊x⌋₊ ≤ x / Real.log x - (x - 1) / Real.log x := by
      gcongr;
      · exact Real.log_pos <| Nat.one_lt_cast.2 <| by linarith;
      · linarith [ Nat.lt_floor_add_one x ];
      · exact Nat.floor_le ( by positivity );
    exact h_bounds.trans ( by ring_nf; nlinarith [ inv_mul_cancel₀ ( by linarith : Real.log x ≠ 0 ) ] )

/-- For y ≥ 4, |(⌈y⌉-1)/log(⌈y⌉-1) - y/log y| ≤ 2/log y. -/
lemma ceil_minus_one_div_log_approx (y : ℝ) (hy : y ≥ 4) :
    |((⌈y⌉₊ : ℝ) - 1) / Real.log ((⌈y⌉₊ : ℝ) - 1) - y / Real.log y| ≤ 2 / Real.log y := by
  rw [ abs_sub_le_iff ];
  constructor;
  · rw [ sub_le_iff_le_add' ];
    rw [ ← add_div, div_le_div_iff₀ ] <;> try linarith [ Real.log_pos <| show 1 < y by linarith ];
    · have h_log_bound : Real.log (⌈y⌉₊ - 1) ≥ Real.log y - 1 / (⌈y⌉₊ - 1) := by
        rw [ ge_iff_le, sub_le_iff_le_add ];
        rw [ Real.log_le_iff_le_exp, Real.exp_add, Real.exp_log ] <;> try linarith [ Nat.le_ceil y ];
        nlinarith [ Nat.le_ceil y, Real.add_one_le_exp ( 1 / ( ⌈y⌉₊ - 1 ) ), one_div_mul_cancel ( show ( ⌈y⌉₊ - 1 : ℝ ) ≠ 0 by linarith [ show ( ⌈y⌉₊ : ℝ ) ≥ 4 by exact_mod_cast Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; linarith ) ) ] ) ];
      rcases n : ⌈y⌉₊ with ( _ | _ | n ) <;> simp_all +decide;
      · linarith;
      · rw [ Nat.ceil_eq_iff ] at n <;> norm_num at *;
        have h_log_bound : Real.log (↑‹ℕ› + 1) ≥ 1 := by
          exact Real.le_log_iff_exp_le ( by linarith ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) );
        nlinarith [ inv_mul_cancel₀ ( by linarith : ( ( Nat.cast:ℕ →ℝ ) ‹_› ) + 1 ≠ 0 ) ];
    · exact Real.log_pos <| by linarith [ Nat.le_ceil y ];
  · have h_bound : y / Real.log y - (⌈y⌉₊ - 1) / Real.log (⌈y⌉₊ - 1) ≤ y / Real.log y - (y - 1) / Real.log y := by
      gcongr;
      · linarith [ Nat.le_ceil y ];
      · exact Real.log_pos <| by linarith [ Nat.le_ceil y ];
      · exact Nat.le_ceil _;
      · linarith [ Nat.le_ceil y ];
      · linarith [ Nat.ceil_lt_add_one ( by positivity : 0 ≤ y ) ];
    exact h_bound.trans ( by ring_nf; nlinarith [ inv_pos.mpr ( Real.log_pos ( show y > 1 by linarith ) ) ] )

/-- π(⌊x⌋) ≈ x/log x with error O(x/(log x)²). -/
lemma pi_of_floor_approx :
    ∃ C > 0, ∃ X₀ : ℝ, ∀ x : ℝ, x ≥ X₀ →
      |((primesUpTo (⌊x⌋₊ : ℝ)).card : ℝ) - x / Real.log x| ≤
        C * x / (Real.log x) ^ 2 := by
  -- By combining the approximations from Dusart's theorem and the floor/ceiling PNT approximations, we can conclude the proof.
  obtain ⟨C₀, hC₀_pos, X₀, hX₀⟩ : ∃ C₀ > 0, ∃ X₀ : ℝ, ∀ t : ℝ, t ≥ X₀ →
      |((primesUpTo t).card : ℝ) - t / Real.log t| ≤ C₀ * t / (Real.log t) ^ 2 := by
        exact pi_approx_error;
  refine' ⟨ 8 * C₀ + 8, by positivity, Max.max 4 ( X₀ + 1 ), fun x hx => _ ⟩ ; specialize hX₀ ⌊x⌋₊ _;
  · linarith [ Nat.lt_floor_add_one x, le_max_right 4 ( X₀ + 1 ) ];
  · -- Applying the approximations from Dusart's theorem and the floor/ceiling PNT approximations.
    have h_approx : |((primesUpTo ⌊x⌋₊).card : ℝ) - x / Real.log x| ≤ C₀ * ⌊x⌋₊ / (Real.log ⌊x⌋₊) ^ 2 + 2 / Real.log x := by
      have h_approx : |(⌊x⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ) - x / Real.log x| ≤ 2 / Real.log x := by
        apply floor_div_log_approx; linarith [le_max_left 4 (X₀ + 1), le_max_right 4 (X₀ + 1)];
      exact abs_sub_le_iff.mpr ⟨ by linarith [ abs_le.mp hX₀, abs_le.mp h_approx ], by linarith [ abs_le.mp hX₀, abs_le.mp h_approx ] ⟩;
    -- Since $\lfloor x \rfloor \leq x$ and $\log(\lfloor x \rfloor) \geq \log(x/2) \geq \log(x)/2$ for $x \geq 4$, we can bound the terms.
    have h_bounds : C₀ * ⌊x⌋₊ / (Real.log ⌊x⌋₊) ^ 2 ≤ C₀ * x / (Real.log x / 2) ^ 2 ∧ 2 / Real.log x ≤ 2 * x / (Real.log x) ^ 2 := by
      constructor;
      · gcongr;
        · exact mul_nonneg hC₀_pos.le ( by linarith [ le_max_left 4 ( X₀ + 1 ), le_max_right 4 ( X₀ + 1 ) ] );
        · exact sq_pos_of_pos ( div_pos ( Real.log_pos ( by linarith [ le_max_left 4 ( X₀ + 1 ) ] ) ) zero_lt_two );
        · exact Nat.floor_le ( by linarith [ le_max_left 4 ( X₀ + 1 ), le_max_right 4 ( X₀ + 1 ) ] );
        · exact div_nonneg ( Real.log_nonneg ( by linarith [ le_max_left 4 ( X₀ + 1 ) ] ) ) zero_le_two;
        · rw [ div_le_iff₀' ] <;> norm_num;
          rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> norm_num;
          · nlinarith [ Nat.lt_floor_add_one x, show ( 4 : ℝ ) ≤ x by exact le_trans ( le_max_left _ _ ) hx ];
          · linarith [ le_max_left 4 ( X₀ + 1 ), le_max_right 4 ( X₀ + 1 ) ];
          · exact pow_pos ( Nat.floor_pos.mpr ( by linarith [ le_max_left 4 ( X₀ + 1 ) ] ) ) _;
          · exact Nat.floor_pos.mpr ( by linarith [ le_max_left 4 ( X₀ + 1 ) ] );
      · rw [ div_le_div_iff₀ ] <;> nlinarith [ show 1 ≤ Real.log x from by rw [ Real.le_log_iff_exp_le ( by linarith [ le_max_left 4 ( X₀ + 1 ) ] ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ le_max_left 4 ( X₀ + 1 ) ] ), Real.log_le_sub_one_of_pos ( show 0 < x by linarith [ le_max_left 4 ( X₀ + 1 ) ] ) ];
    ring_nf at *;
    nlinarith [ show 0 ≤ x * ( Real.log x ) ⁻¹ ^ 2 by exact mul_nonneg ( by linarith [ le_max_left 4 ( 1 + X₀ ) ] ) ( sq_nonneg _ ) ]

/-- π(⌈y⌉-1) ≈ y/log y with error O(y/(log y)²). -/
lemma pi_of_ceil_approx :
    ∃ C > 0, ∃ X₀ : ℝ, ∀ y : ℝ, y ≥ X₀ →
      |((primesUpTo ((⌈y⌉₊ : ℝ) - 1)).card : ℝ) - y / Real.log y| ≤
        C * y / (Real.log y) ^ 2 := by
  -- First term: From pi_approx_error, ∃ C₀ > 0, X₀, ∀ t ≥ X₀, |π(t) - t/log t| ≤ C₀*t/(log t)².
  obtain ⟨C₀, hC₀_pos, X₀, hC₀⟩ : ∃ C₀ > 0, ∃ X₀ : ℝ, ∀ x : ℝ, x ≥ X₀ →
    |((primesUpTo x).card : ℝ) - x / Real.log x| ≤ C₀ * x / (Real.log x) ^ 2 := by
      exact pi_approx_error;
  refine' ⟨ 8 * C₀ + 8, by positivity, Max.max 4 ( X₀ + 1 ), fun y hy => _ ⟩ ; specialize hC₀ ( ⌈y⌉₊ - 1 ) _ <;> norm_num at *;
  · linarith [ Nat.le_ceil y ];
  · -- Apply ceil_minus_one_div_log_approx to bound the second term.
    have h_ceil_minus_one : |((⌈y⌉₊ : ℝ) - 1) / Real.log ((⌈y⌉₊ : ℝ) - 1) - y / Real.log y| ≤ 2 / Real.log y := by
      apply ceil_minus_one_div_log_approx; linarith;
    -- Since $\log(y-1) \geq \log(y/2) = \log y - \log 2 \geq \log y / 2$ for $y \geq 4$, we get $\frac{C₀ * (⌈y⌉₊ - 1)}{(\log(⌈y⌉₊ - 1))^2} \leq \frac{C₀ * y}{(\log y / 2)^2} = \frac{4 * C₀ * y}{(\log y)^2}$.
    have h_log_bound : (C₀ * (⌈y⌉₊ - 1) : ℝ) / (Real.log (⌈y⌉₊ - 1)) ^ 2 ≤ (4 * C₀ * y : ℝ) / (Real.log y) ^ 2 := by
      have h_log_bound : Real.log (⌈y⌉₊ - 1) ≥ Real.log y / 2 := by
        rw [ ge_iff_le, div_le_iff₀' ] <;> norm_num;
        erw [ ← Real.log_pow, Real.log_le_log_iff ] <;> nlinarith [ Nat.le_ceil y, show ( ⌈y⌉₊ : ℝ ) ≥ 4 by exact_mod_cast Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast ; linarith [ Nat.le_ceil y ] ];
      rw [ div_le_div_iff₀ ];
      · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( div_nonneg ( Real.log_nonneg ( by linarith ) ) zero_le_two ) h_log_bound 2 ) ( by nlinarith ) );
        nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ y by linarith ), show 0 ≤ C₀ * Real.log y ^ 2 by positivity ];
      · exact sq_pos_of_pos ( lt_of_lt_of_le ( div_pos ( Real.log_pos ( by linarith ) ) zero_lt_two ) h_log_bound );
      · exact sq_pos_of_pos <| Real.log_pos <| by linarith;
    -- Since $2 / \log y \leq 2 * y / (\log y)^2$ for $y \geq 4$, we can combine the bounds.
    have h_combined : 2 / Real.log y ≤ 2 * y / (Real.log y) ^ 2 := by
      rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.log_pos ( by linarith : 1 < y ), Real.log_le_sub_one_of_pos ( by linarith : 0 < y ) ];
    grind +splitImp

/-- When u ∈ [1,2], y/(log y)² ≤ 4x/(log x)². -/
lemma error_y_le_x (x y : ℝ) (hx : x ≥ 4) (hy : y ≥ 2)
    (h1 : 1 ≤ Real.log x / Real.log y) (h2 : Real.log x / Real.log y ≤ 2) :
    y / (Real.log y) ^ 2 ≤ 4 * x / (Real.log x) ^ 2 := by
  -- From h2: log x / log y ≤ 2, so log x ≤ 2 * log y, so (log x)² ≤ 4 * (log y)².
  have h_log_sq : (Real.log x) ^ 2 ≤ 4 * (Real.log y) ^ 2 := by
    rw [ div_le_iff₀ ] at h2 <;> nlinarith [ Real.log_pos <| show 1 < y by linarith, Real.log_pos <| show 1 < x by linarith ];
  -- From h1: log x ≥ log y, so x ≥ y.
  have h_x_ge_y : x ≥ y := by
    contrapose! h1;
    rw [ div_lt_one ( Real.log_pos <| by linarith ) ] ; exact Real.log_lt_log ( by linarith ) h1;
  rw [ div_le_div_iff₀ ] <;> nlinarith [ show 0 < Real.log x ^ 2 by exact sq_pos_of_pos <| Real.log_pos <| by linarith, show 0 < Real.log y ^ 2 by exact sq_pos_of_pos <| Real.log_pos <| by linarith ]

/-- sievePhi(⌊x⌋, ⌈y⌉) differs from π(⌊x⌋) - π(⌈y⌉-1) by at most 2. -/
lemma sievePhi_approx_pi_diff (x y : ℝ) (hx : x ≥ 4) (hy : y ≥ 2)
    (h1 : 1 ≤ Real.log x / Real.log y) (h2 : Real.log x / Real.log y ≤ 2) :
    |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) -
      ((primesUpTo (⌊x⌋₊ : ℝ)).card - (primesUpTo ((⌈y⌉₊ : ℝ) - 1)).card)| ≤ 2 := by
  by_cases h : ⌈y⌉₊ ≤ ⌊x⌋₊;
  · have h_sievePhi : sievePhi ⌊x⌋₊ ⌈y⌉₊ ≥ 1 + ((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card ∧ sievePhi ⌊x⌋₊ ⌈y⌉₊ ≤ 2 + ((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card := by
      apply And.intro;
      · apply sievePhi_ge_one_plus_primes;
        · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; linarith ) );
        · exact Nat.floor_pos.mpr ( by linarith );
      · apply sievePhi_le_primes_plus_two;
        · exact ceil_sq_ge_floor_of_log_ratio_le_two x y hx hy h2;
        · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; linarith ) );
        · exact Nat.floor_pos.mpr ( by linarith );
    have h_primes_Icc : ((Finset.Icc ⌈y⌉₊ ⌊x⌋₊).filter Nat.Prime).card = (primesUpTo ⌊x⌋₊).card - (primesUpTo (⌈y⌉₊ - 1)).card := by
      convert primes_Icc_eq_pi_diff ⌊x⌋₊ ⌈y⌉₊ _ _ using 1 <;> norm_num [ h ];
      exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; linarith ) );
    rw [ abs_le ] ; constructor <;> norm_cast at *;
    · grind +qlia;
    · rw [ Int.subNatNat_of_le ] <;> norm_cast;
      · rw [ Int.subNatNat_eq_coe ] ; omega;
      · refine Finset.card_mono ?_;
        unfold primesUpTo; norm_num;
        exact Finset.filter_subset_filter _ ( Finset.range_mono ( by omega ) );
  · -- Since ⌈y⌉₊ > ⌊x⌋₊, we have ⌈y⌉₊ = ⌊x⌋₊ + 1.
    have h_ceil_eq : ⌈y⌉₊ = ⌊x⌋₊ + 1 := by
      refine' le_antisymm _ _ <;> norm_num at *;
      · contrapose! h1;
        rw [ div_lt_one ( Real.log_pos <| by linarith ) ] ; exact Real.log_lt_log ( by positivity ) <| by linarith [ Nat.lt_floor_add_one x ] ;
      · exact Nat.lt_ceil.mpr h;
    -- Since ⌈y⌉₊ = ⌊x⌋₊ + 1, we have sievePhi ⌊x⌋₊ ⌈y⌉₊ = 1.
    have h_sievePhi : sievePhi ⌊x⌋₊ ⌈y⌉₊ = 1 := by
      refine' Finset.card_eq_one.mpr ⟨ 1, _ ⟩;
      ext m; simp [h_ceil_eq];
      constructor <;> intro hm <;> rcases m with ( _ | _ | m ) <;> simp_all +decide;
      · exact not_le_of_gt ( hm.2 _ ( Nat.minFac_prime ( by linarith ) ) ( Nat.minFac_dvd _ ) ) ( Nat.le_trans ( Nat.minFac_le ( by linarith ) ) ( by linarith ) );
      · exact ⟨ by linarith, by aesop ⟩;
    simp_all +decide [ primesUpTo ]

end

end BuchstabAnalysis

section Analysis

/-! Buchstab function, Mertens product bound, and integral convergence. -/

open Finset BigOperators Real MeasureTheory

noncomputable section

/-! ### Buchstab function -/

/-- The Buchstab function ω on [1, ∞).
    For 1 ≤ u ≤ 2: ω(u) = 1/u.
    For 2 < u: ω(u) = (1 + log(u-1))/u.
    This is the exact formula on [1,3]; beyond [1,3] the delay-differential
    equation gives a different expression, but we only use values in [2,3]. -/
noncomputable def buchstabOmega (u : ℝ) : ℝ :=
  if u < 1 then 0
  else if u ≤ 2 then 1 / u
  else (1 + Real.log (u - 1)) / u

/-- On [1,2], ω(u) = 1/u. -/
lemma buchstabOmega_eq (u : ℝ) (h1 : 1 ≤ u) (h2 : u ≤ 2) :
    buchstabOmega u = 1 / u := by
  unfold buchstabOmega
  split_ifs with h3
  · linarith
  · rfl

/-- For 2 ≤ u ≤ 3, uω(u) = 1 + log(u-1). -/
lemma buchstabOmega_formula_23 (u : ℝ) (h1 : 2 ≤ u) (h2 : u ≤ 3) :
    u * buchstabOmega u = 1 + Real.log (u - 1) := by
  unfold buchstabOmega
  split_ifs with h3 h4
  · linarith
  · have : u = 2 := le_antisymm h4 h1; subst this; norm_num
  · field_simp

/-- ω is positive on [1, ∞). -/
lemma buchstabOmega_pos (u : ℝ) (hu : 1 ≤ u) : buchstabOmega u > 0 := by
  unfold buchstabOmega
  split_ifs with h1 h2
  · linarith
  · positivity
  · apply div_pos
    · linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ u - 1)]
    · linarith

/-- ω is locally Lipschitz on [1, ∞). -/
lemma buchstabOmega_lipschitz_on (a b : ℝ) (ha : 1 ≤ a) (_hb : a ≤ b) :
    ∃ L > 0, ∀ u v : ℝ, a ≤ u → u ≤ b → a ≤ v → v ≤ b →
      |buchstabOmega u - buchstabOmega v| ≤ L * |u - v| := by
  -- On [1,2], ω(u) = 1/u which has derivative -1/u² bounded by 1 on [1,∞). So |ω(u) - ω(v)| ≤ |u-v| by the mean value theorem on [1,2].
  have h_lip_12 : ∃ L1 > 0, ∀ u v : ℝ, 1 ≤ u → u ≤ 2 → 1 ≤ v → v ≤ 2 → abs (buchstabOmega u - buchstabOmega v) ≤ L1 * abs (u - v) := by
    use 1; norm_num; intros u v hu hv hu' hv'; rw [ buchstabOmega_eq u hu hv, buchstabOmega_eq v hu' hv' ] ; rw [ div_sub_div, abs_div ] <;> try positivity;
    rw [ div_le_iff₀ ( by positivity ) ];
    cases abs_cases ( u - v ) <;> cases abs_cases ( 1 * v - u * 1 ) <;> cases abs_cases ( u * v ) <;> push_cast [ * ] <;> nlinarith [ mul_le_mul_of_nonneg_left hu' ( sub_nonneg_of_le hu ) ];
  -- On [2, ∞), ω(u) = (1 + log(u-1))/u. This is differentiable and its derivative is bounded on any compact interval [a,b]. So it's Lipschitz there.
  have h_lip_2_inf : ∃ L2 > 0, ∀ u v : ℝ, 2 ≤ u → u ≤ b → 2 ≤ v → v ≤ b → abs (buchstabOmega u - buchstabOmega v) ≤ L2 * abs (u - v) := by
    -- The derivative of ω(u) on [2, ∞) is bounded by 1/u² + 1/(u(u-1)), which is less than or equal to 3/4.
    have h_deriv_bound : ∀ u : ℝ, 2 ≤ u → abs (deriv (fun u => (1 + Real.log (u - 1)) / u) u) ≤ 3 / 4 := by
      intro u hu; norm_num [ show u ≠ 0 by linarith, show u - 1 ≠ 0 by linarith ];
      rw [ abs_le ];
      constructor <;> nlinarith [ inv_pos.mpr ( by linarith : 0 < u - 1 ), mul_inv_cancel₀ ( by linarith : ( u - 1 ) ≠ 0 ), sq_nonneg ( u - 2 ), Real.log_nonneg ( by linarith : ( u - 1 ) ≥ 1 ), Real.log_le_sub_one_of_pos ( by linarith : 0 < u - 1 ), mul_div_cancel₀ ( ( u - 1 ) ⁻¹ * u - ( 1 + Real.log ( u - 1 ) ) ) ( by positivity : ( u ^ 2 ) ≠ 0 ) ];
    -- Apply the mean value theorem to the interval [u, v] to find a point c where the derivative equals the difference quotient.
    have h_mvt : ∀ u v : ℝ, 2 ≤ u → u < v → v ≤ b → ∃ c ∈ Set.Ioo u v, deriv (fun u => (1 + Real.log (u - 1)) / u) c = (buchstabOmega v - buchstabOmega u) / (v - u) := by
      intros u v hu hv hb;
      have := exists_deriv_eq_slope ( f := fun u => ( 1 + Real.log ( u - 1 ) ) / u ) hv;
      convert this _ _ using 3;
      · unfold buchstabOmega; norm_num [ show u ≠ 0 by linarith, show v ≠ 0 by linarith, show u - 1 ≠ 0 by linarith, show v - 1 ≠ 0 by linarith ] ;
        split_ifs <;> try linarith;
        · norm_num [ show u = 2 by linarith ];
        · norm_cast;
      · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( continuousAt_const.add ( ContinuousAt.log ( continuousAt_id.sub continuousAt_const ) ( by linarith [ hx.1 ] ) ) ) continuousAt_id ( by linarith [ hx.1 ] );
      · exact DifferentiableOn.div ( DifferentiableOn.add ( differentiableOn_const _ ) ( DifferentiableOn.log ( differentiableOn_id.sub_const _ ) ( by intro x hx; linarith [ hx.1 ] ) ) ) differentiableOn_id ( by intro x hx; linarith [ hx.1 ] );
    refine' ⟨ 3 / 4, by norm_num, fun u v hu hv hu' hv' => _ ⟩;
    rcases lt_trichotomy u v with ( H | rfl | H ) <;> norm_num at *;
    · obtain ⟨ c, ⟨ h₁, h₂ ⟩, h₃ ⟩ := h_mvt u v hu H hv'; rw [ abs_le ] ; constructor <;> cases abs_cases ( u - v ) <;> nlinarith [ abs_le.mp ( h_deriv_bound c ( by linarith ) ), mul_div_cancel₀ ( buchstabOmega v - buchstabOmega u ) ( sub_ne_zero_of_ne H.ne' ) ] ;
    · obtain ⟨ c, ⟨ h₁, h₂ ⟩, h₃ ⟩ := h_mvt v u hu' H hv ; rw [ abs_le ] ; constructor <;> cases abs_cases ( u - v ) <;> nlinarith [ abs_le.mp ( h_deriv_bound c ( by linarith ) ), mul_div_cancel₀ ( buchstabOmega u - buchstabOmega v ) ( by linarith : ( u - v ) ≠ 0 ) ];
  -- On [1, ∞), ω is piecewise smooth (1/u on [1, 2] and (1+log(u-1))/u on (2, ∞)), so it's Lipschitz on any compact subinterval of [1, ∞).
  obtain ⟨L1, hL1_pos, hL1⟩ := h_lip_12
  obtain ⟨L2, hL2_pos, hL2⟩ := h_lip_2_inf
  use max L1 L2 + 1;
  refine' ⟨ by positivity, fun u v hu hv hu' hv' => _ ⟩;
  by_cases hu2 : u ≤ 2 <;> by_cases hv2 : v ≤ 2;
  · exact le_trans ( hL1 u v ( by linarith ) hu2 ( by linarith ) hv2 ) ( mul_le_mul_of_nonneg_right ( by linarith [ le_max_left L1 L2, le_max_right L1 L2 ] ) ( abs_nonneg _ ) );
  · have := hL1 u 2 ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ; have := hL2 2 v ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ; simp_all +decide [ abs_of_nonpos ] ;
    rw [ abs_le ] at *;
    constructor <;> cases abs_cases ( u - v ) <;> cases abs_cases ( 2 - v ) <;> nlinarith [ le_max_left L1 L2, le_max_right L1 L2 ];
  · have h_diff : abs (buchstabOmega u - buchstabOmega v) ≤ abs (buchstabOmega u - buchstabOmega 2) + abs (buchstabOmega 2 - buchstabOmega v) := by
      exact abs_sub_le _ _ _;
    have h_diff_u : abs (buchstabOmega u - buchstabOmega 2) ≤ L2 * abs (u - 2) := by
      exact hL2 u 2 ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith )
    have h_diff_v : abs (buchstabOmega 2 - buchstabOmega v) ≤ L1 * abs (2 - v) := by
      exact hL1 2 v ( by norm_num ) ( by norm_num ) ( by linarith ) ( by linarith );
    cases abs_cases ( u - v ) <;> cases abs_cases ( u - 2 ) <;> cases abs_cases ( 2 - v ) <;> nlinarith [ le_max_left L1 L2, le_max_right L1 L2 ];
  · exact le_trans ( hL2 u v ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ) ( mul_le_mul_of_nonneg_right ( by linarith [ le_max_right L1 L2 ] ) ( abs_nonneg _ ) )

/-- Buchstab estimate for u ∈ [1,2]: Φ(⌊x⌋,⌈y⌉) ≈ x/log x - y/log y. -/
lemma buchstab_estimate_12 :
    ∃ K > 0, ∃ X₀ : ℝ, ∀ x y : ℝ, x ≥ X₀ → y ≥ 2 →
      1 ≤ Real.log x / Real.log y → Real.log x / Real.log y ≤ 2 →
        |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) -
          (x / Real.log x - y / Real.log y)| ≤
          K * x / (Real.log x) ^ 2 := by
  have := pi_of_floor_approx;
  obtain ⟨ C₁, hC₁₀, X₁, h₁ ⟩ := this; obtain ⟨ C₂, hC₂₀, X₂, h₂ ⟩ := pi_of_ceil_approx; use C₁ + 4 * C₂ + 2; use by positivity; ; use Max.max ( Max.max X₁ ( X₂^2 + 1 ) ) 16; intros x y hx hy h1 h2; have := h₁ x ?_ <;> have := h₂ y ?_;
  · -- Apply the triangle inequality to the absolute value expression.
    have h_triangle : |(sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℝ) - (x / Real.log x - y / Real.log y)| ≤ 2 + |((primesUpTo (⌊x⌋₊ : ℝ)).card : ℝ) - x / Real.log x| + |((primesUpTo ((⌈y⌉₊ : ℝ) - 1)).card : ℝ) - y / Real.log y| := by
      have := sievePhi_approx_pi_diff x y ( by linarith [ le_max_left ( max X₁ ( X₂ ^ 2 + 1 ) ) 16, le_max_right ( max X₁ ( X₂ ^ 2 + 1 ) ) 16 ] ) hy h1 h2; norm_num at *;
      grind;
    -- Apply the error bound for y.
    have h_error_y : C₂ * y / (Real.log y) ^ 2 ≤ 4 * C₂ * x / (Real.log x) ^ 2 := by
      have := error_y_le_x x y ( by linarith [ le_max_left ( max X₁ ( X₂ ^ 2 + 1 ) ) 16, le_max_right ( max X₁ ( X₂ ^ 2 + 1 ) ) 16, le_max_left X₁ ( X₂ ^ 2 + 1 ), le_max_right X₁ ( X₂ ^ 2 + 1 ) ] ) hy h1 h2;
      convert mul_le_mul_of_nonneg_left this hC₂₀.le using 1 <;> ring;
    -- Apply the error bound for x.
    have h_error_x : 2 ≤ 2 * x / (Real.log x) ^ 2 := by
      rw [ le_div_iff₀ ] <;> norm_num at *;
      · -- Apply the inequality $\log x \leq \sqrt{x}$ for $x \geq 16$.
        have h_log_sqrt : Real.log x ≤ Real.sqrt x := by
          have := Real.log_le_sub_one_of_pos ( show 0 < Real.sqrt x / 2 by exact div_pos ( Real.sqrt_pos.mpr ( by linarith ) ) zero_lt_two );
          rw [ Real.log_div ( by linarith [ Real.sqrt_pos.mpr ( show 0 < x by linarith ) ] ) ( by linarith ), Real.log_sqrt ( by linarith ) ] at this ; linarith [ Real.log_le_sub_one_of_pos zero_lt_two ];
        exact le_trans ( pow_le_pow_left₀ ( Real.log_nonneg ( by linarith ) ) h_log_sqrt 2 ) ( by rw [ Real.sq_sqrt ( by linarith ) ] );
      · exact sq_pos_of_pos <| Real.log_pos <| by linarith;
    grind;
  · contrapose! h2;
    rw [ lt_div_iff₀ ( Real.log_pos <| by linarith ) ];
    rw [ ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_num <;> nlinarith [ le_max_left ( max X₁ ( X₂ ^ 2 + 1 ) ) 16, le_max_right ( max X₁ ( X₂ ^ 2 + 1 ) ) 16, le_max_left X₁ ( X₂ ^ 2 + 1 ), le_max_right X₁ ( X₂ ^ 2 + 1 ) ];
  · linarith [ le_max_left ( max X₁ ( X₂ ^ 2 + 1 ) ) 16, le_max_right ( max X₁ ( X₂ ^ 2 + 1 ) ) 16, le_max_left X₁ ( X₂ ^ 2 + 1 ), le_max_right X₁ ( X₂ ^ 2 + 1 ) ];
  · rw [ div_le_iff₀ ( Real.log_pos <| by linarith ) ] at h2;
    contrapose! h2;
    rw [ ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_num <;> nlinarith [ le_max_left ( max X₁ ( X₂ ^ 2 + 1 ) ) 16, le_max_right ( max X₁ ( X₂ ^ 2 + 1 ) ) 16, le_max_left X₁ ( X₂ ^ 2 + 1 ), le_max_right X₁ ( X₂ ^ 2 + 1 ) ]

axiom buchstab_estimate_23:
    ∃ K > 0, ∃ X₀ : ℝ, ∀ x y : ℝ, x ≥ X₀ → y ≥ 2 →
      2 ≤ Real.log x / Real.log y → Real.log x / Real.log y ≤ 3 →
        |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) -
          ((1 + Real.log (Real.log x / Real.log y - 1)) * x / Real.log x -
           y / Real.log y)| ≤
          K * x / (Real.log x) ^ 2

/-- Buchstab estimate:
    For every U ∈ [1, 3], there exist K_U > 0 and X_U such that for all x ≥ X_U and y ≥ 2
    with 1 ≤ log x / log y ≤ U, we have
    |Φ(⌊x⌋, ⌈y⌉) - (ω(log x / log y) · x / log y - y / log y)| ≤ K_U · x/(log x)².

    Note: U is restricted to [1, 3] because buchstabOmega only matches the true
    Buchstab function on [1, 3]. The downstream application only needs u values
    approaching UAlpha(α) ∈ (2, 3] from above, so U ≤ 3 suffices. -/
lemma buchstab_estimate (U : ℝ) (_hU : U ≥ 1) (hU3 : U ≤ 3) :
    ∃ K_U > 0, ∃ X_U : ℝ, ∀ x y : ℝ, x ≥ X_U → y ≥ 2 →
      1 ≤ Real.log x / Real.log y → Real.log x / Real.log y ≤ U →
        |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) -
          (buchstabOmega (Real.log x / Real.log y) * x / Real.log y -
           y / Real.log y)| ≤
          K_U * x / (Real.log x) ^ 2 := by
  obtain ⟨K₁, hK₁, X₁, h12⟩ := buchstab_estimate_12
  obtain ⟨K₂, hK₂, X₂, h23⟩ := buchstab_estimate_23
  refine ⟨max K₁ K₂, by positivity, max (max X₁ X₂) 4, fun x y hx hy hu1 huU => ?_⟩
  have hx4 : x ≥ 4 := le_trans (le_max_right (max X₁ X₂) 4) hx
  have hx_pos : (0 : ℝ) < x := by linarith
  have hly : Real.log y > 0 := Real.log_pos (by linarith)
  have hlx : Real.log x > 0 := by
    have h := (le_div_iff₀ hly).mp hu1; linarith
  set u := Real.log x / Real.log y with hu_def
  by_cases h_u2 : u ≤ 2
  · have h_est := h12 x y (le_trans (le_trans (le_max_left X₁ X₂) (le_max_left _ 4)) hx) hy hu1 h_u2
    have h_omega : buchstabOmega u = 1 / u := buchstabOmega_eq u hu1 h_u2
    have h_eq : buchstabOmega u * x / Real.log y - y / Real.log y =
                x / Real.log x - y / Real.log y := by
      rw [h_omega, hu_def]; field_simp
    rw [h_eq]
    calc |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) - (x / Real.log x - y / Real.log y)|
        ≤ K₁ * x / (Real.log x) ^ 2 := h_est
      _ ≤ max K₁ K₂ * x / (Real.log x) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left K₁ K₂) (by positivity)
  · push_neg at h_u2
    have h_est := h23 x y (le_trans (le_trans (le_max_right X₁ X₂) (le_max_left _ 4)) hx) hy h_u2.le (by linarith)
    have h_omega : buchstabOmega u = (1 + Real.log (u - 1)) / u := by
      unfold buchstabOmega
      simp only [show ¬(u < 1) by linarith, ↓reduceIte, show ¬(u ≤ 2) by linarith]
    have h_eq : buchstabOmega u * x / Real.log y - y / Real.log y =
                (1 + Real.log (u - 1)) * x / Real.log x - y / Real.log y := by
      rw [h_omega, hu_def]; field_simp
    rw [h_eq]
    calc |((sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℕ) : ℝ) - ((1 + Real.log (u - 1)) * x / Real.log x - y / Real.log y)|
        ≤ K₂ * x / (Real.log x) ^ 2 := h_est
      _ ≤ max K₁ K₂ * x / (Real.log x) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_right K₁ K₂) (by positivity)

/-! ### Ω_α and its limit -/

/-- U_α = 1/(2α - 1). -/
def UAlpha (alpha : ℝ) : ℝ := 1 / (2 * alpha - 1)

/-- Ω_α = 2 · U_α · ω(U_α) where U_α = 1/(2α - 1). -/
def OmegaAlpha (alpha : ℝ) : ℝ :=
  2 * UAlpha alpha * buchstabOmega (UAlpha alpha)

/-- For 2/3 ≤ α < 3/4, U_α ∈ (2, 3]. -/
lemma UAlpha_range (alpha : ℝ) (h1 : 2/3 ≤ alpha) (h2 : alpha < 3/4) :
    2 < UAlpha alpha ∧ UAlpha alpha ≤ 3 := by
  constructor
  · unfold UAlpha; rw [lt_div_iff₀ (by linarith)]; linarith
  · unfold UAlpha; rw [div_le_iff₀ (by linarith)]; linarith

/-- For 2/3 ≤ α < 3/4, Ω_α = 2(1 + log(U_α - 1)). -/
lemma OmegaAlpha_formula (alpha : ℝ) (h1 : 2/3 ≤ alpha) (h2 : alpha < 3/4) :
    OmegaAlpha alpha = 2 * (1 + Real.log (UAlpha alpha - 1)) := by
  unfold OmegaAlpha
  have hU := UAlpha_range alpha h1 h2
  rw [show 2 * UAlpha alpha * buchstabOmega (UAlpha alpha) =
    2 * (UAlpha alpha * buchstabOmega (UAlpha alpha)) by ring]
  rw [buchstabOmega_formula_23 (UAlpha alpha) hU.1.le hU.2]

/-- Ω_α → 2 as α → 3/4⁻. -/
lemma OmegaAlpha_tendsto_two :
    Filter.Tendsto (fun alpha => OmegaAlpha alpha)
      (nhdsWithin (3/4 : ℝ) (Set.Iio (3/4))) (nhds 2) := by
  -- For 2/3 ≤ α < 3/4, we have Ω_α = 2(1 + log(U_α - 1)).
  have h_eq : ∀ᶠ alpha in nhdsWithin (3 / 4) (Set.Iio (3 / 4)), OmegaAlpha alpha = 2 * (1 + Real.log (UAlpha alpha - 1)) := by
    refine' Filter.eventually_inf_principal.mpr _;
    filter_upwards [ lt_mem_nhds ( show 3 / 4 > 2 / 3 by norm_num ) ] with x hx₁ hx₂ using OmegaAlpha_formula x ( by linarith ) ( by linarith [ hx₂.out ] );
  rw [ Filter.tendsto_congr' h_eq ];
  convert tendsto_const_nhds.mul ( tendsto_const_nhds.add ( Filter.Tendsto.log ( Filter.Tendsto.sub ( tendsto_const_nhds.div ( tendsto_const_nhds.mul ( Filter.tendsto_id.mono_left inf_le_left ) |> Filter.Tendsto.sub_const <| 1 ) _ ) tendsto_const_nhds ) _ ) ) using 2 <;> norm_num

/-! ### Mertens product bound and H(x) growth -/

/-- Mertens product upper bound: ∏_{p ≤ z} (1 - 1/p)^{-1} ≤ K_M · log z for z ≥ 3. -/
lemma mertens_product_upper_bound :
    ∃ K_M : ℝ, K_M > 0 ∧ ∀ z : ℕ, 3 ≤ z →
      ∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹ ≤ K_M * Real.log z := by
  use 3
  norm_num +zetaDelta at *
  intro z hz
  have := mertens_third_theorem z hz
  simpa using inv_anti₀ (by exact one_div_pos.mpr (mul_pos zero_lt_three (Real.log_pos (by norm_cast; linarith)))) this

/-- H(x) ≤ K_H · (1 + x) for all x ≥ 0. -/
lemma HFunc_growth_bound :
    ∃ K_H : ℝ, K_H > 0 ∧ ∀ x : ℝ, 0 ≤ x → HFunc x ≤ K_H * (1 + x) := by
  obtain ⟨K_M, hK_M_pos, hK_M⟩ := mertens_product_upper_bound
  refine ⟨Max.max (K_M * 2) 2, by positivity, ?_⟩
  intro x hx_nonneg
  by_cases hx : x < Real.log 3 / 2
  · refine le_trans ?_ (le_mul_of_one_le_right ?_ ?_)
    · unfold HFunc
      have h_floor : ⌊Real.exp (2 * x)⌋₊ ≤ 2 := by
        apply Nat.lt_succ_iff.mp
        rw [Nat.floor_lt' (by norm_num)]
        rw [← Real.log_lt_log_iff (by positivity) (by positivity)]
        norm_num; linarith
      interval_cases ⌊Real.exp (2 * x)⌋₊ <;>
        norm_num [Finset.prod_filter, Finset.prod_range_succ]
    · positivity
    · linarith
  · refine le_trans (hK_M _ ?_) ?_
    · exact Nat.le_floor <| by
        norm_num
        linarith [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 3) |>.1 <| show Real.log 3 ≤ 2 * x by linarith]
    · refine le_trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| Real.one_le_exp <| by positivity) <|
          Nat.floor_le <| by positivity) hK_M_pos.le) ?_
      norm_num
      nlinarith [le_max_left (K_M * 2) 2, le_max_right (K_M * 2) 2]

/-- H is nonneg. -/
lemma HFunc_nonneg (x : ℝ) : 0 ≤ HFunc x := by
  unfold HFunc
  apply Finset.prod_nonneg
  intro p hp
  rw [Finset.mem_filter] at hp
  have hp2 := hp.2.two_le
  rw [inv_nonneg]
  have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) < 2) (by exact_mod_cast hp2)
  linarith

/-! ### The integral I and C_* -/

/-- The integrand F(x) = e^{-x} · √(H(x) · (e^x - e^{-x})). -/
def integrandF (x : ℝ) : ℝ :=
  Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x)))

/-- The integral I = ∫₀^∞ F(x) dx. -/
def integralI : ℝ := ∫ x in Set.Ici (0 : ℝ), integrandF x

/-- C_* = 2^{3/2} · I. -/
def Cstar : ℝ := 2 ^ (3/2 : ℝ) * integralI

/-- integrandF is nonneg. -/
lemma integrandF_nonneg (x : ℝ) : 0 ≤ integrandF x := by
  unfold integrandF
  exact mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)

/-- integrandF is bounded by C√(1+x)e^{-x/2} for some C > 0 and x ≥ 0. -/
lemma integrandF_decay_bound :
    ∃ C > 0, ∀ x : ℝ, 0 ≤ x → integrandF x ≤ C * Real.sqrt (1 + x) * Real.exp (-x / 2) := by
  obtain ⟨ K_H, hK_H_pos, hK_H_bound ⟩ := HFunc_growth_bound;
  -- Substitute the bound from HFunc_growth_bound into the expression for integrandF.
  have h_integrandF_bound : ∀ x : ℝ, 0 ≤ x → integrandF x ≤ Real.exp (-x) * Real.sqrt (K_H * (1 + x) * (Real.exp x)) := by
    intro x hx; refine' mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt _ ) ( Real.exp_nonneg _ ) ;
    exact mul_le_mul ( hK_H_bound x hx ) ( sub_le_self _ ( by positivity ) ) ( by exact sub_nonneg.2 <| Real.exp_le_exp.2 <| by linarith ) <| by positivity;
  refine' ⟨ Real.sqrt K_H, Real.sqrt_pos.mpr hK_H_pos, fun x hx => le_trans ( h_integrandF_bound x hx ) _ ⟩;
  rw [ Real.sqrt_mul <| by positivity, Real.sqrt_mul <| by positivity ];
  rw [ show Real.exp x = ( Real.exp ( x / 2 ) ) ^ 2 by rw [ ← Real.exp_nat_mul ] ; ring_nf, Real.sqrt_sq ( by positivity ) ] ; ring_nf ; norm_num;
  rw [ show - ( x * ( 1 / 2 ) ) = -x + x * ( 1 / 2 ) by ring, Real.exp_add ] ; ring_nf ; norm_num

/-- integrandF is integrable on [0, ∞). -/
lemma integrandF_integrable :
    MeasureTheory.IntegrableOn integrandF (Set.Ici 0) := by
  obtain ⟨ C, hC₀, hC ⟩ := integrandF_decay_bound;
  -- We'll use the fact that $(1 + x) e^{-x/2}$ is integrable on $[0, \infty)$.
  have h_integrable : MeasureTheory.IntegrableOn (fun x : ℝ => (1 + x) * Real.exp (-x / 2)) (Set.Ici 0) := by
    have h_integrable : ∫ x in Set.Ici 0, (1 + x) * Real.exp (-x / 2) = 2 * (1 + 2) := by
      have := @integral_rpow_mul_exp_neg_mul_rpow;
      rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ] ; ring_nf;
      rw [ MeasureTheory.integral_add ];
      · have := @this 1 1 ( 1 / 2 ) ; norm_num at *;
        have := integral_exp_neg_mul_rpow zero_lt_one ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) ; norm_num [ mul_comm ] at * ; linarith;
      · have := @this 1 1 ( 1 / 2 ) ?_ ?_ ?_ <;> norm_num at *;
        exact ( by contrapose! this; rw [ MeasureTheory.integral_undef ( by simpa [ mul_comm ] using this ) ] ; norm_num );
      · have := ( exp_neg_integrableOn_Ioi 0 ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) );
        simpa [ div_eq_mul_inv, mul_comm ] using this;
    exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; norm_num );
  refine' h_integrable.const_mul C |> fun h => h.mono' _ _;
  · refine' Measurable.aestronglyMeasurable _;
    unfold integrandF;
    unfold HFunc; norm_num [ Real.exp_neg, Real.exp_ne_zero, Real.differentiableAt_exp, mul_comm, mul_assoc, mul_left_comm, div_eq_mul_inv ] ;
    fun_prop;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ici ] with x hx using by rw [ Real.norm_of_nonneg ( integrandF_nonneg x ) ] ; exact le_trans ( hC x hx ) ( by rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_right ( Real.sqrt_le_iff.mpr ⟨ by linarith [ Set.mem_Ici.mp hx ], by nlinarith [ Set.mem_Ici.mp hx ] ⟩ ) ( Real.exp_nonneg _ ) ) hC₀.le ) ;

/-- The series defining the Riemann sum is summable for h > 0. -/
lemma riemann_sum_summable (h : ℝ) (hh : 0 < h) :
    Summable (fun r : ℕ =>
      Real.exp (-(↑(r + 1)) * h) *
      Real.sqrt (HFunc (↑(r + 1) * h) * (Real.exp (↑(r + 1) * h) - Real.exp (-(↑(r + 1)) * h)))) := by
  have h_bound : ∃ C > 0, ∀ x : ℝ, 0 ≤ x → Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x))) ≤ C * Real.sqrt (1 + x) * Real.exp (-x / 2) := by
    exact integrandF_decay_bound;
  -- We'll use the comparison test. Since \( \sqrt{1 + rh} \leq 1 + rh \), we have:
  have h_comparison : Summable (fun r : ℕ => (1 + (r + 1) * h) * Real.exp (-(r + 1) * h / 2)) := by
    -- We'll use the fact that the series $\sum_{r=1}^{\infty} r e^{-r h / 2}$ converges.
    have h_series_conv : Summable (fun r : ℕ => (r : ℝ) * Real.exp (-r * h / 2)) := by
      -- Apply the ratio test to show that the series converges.
      have h_ratio_test : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℝ) * Real.exp (-(n + 1) * h / 2)) / ((n : ℝ) * Real.exp (-n * h / 2))) Filter.atTop (nhds (Real.exp (-h / 2))) := by
        -- Simplify the expression inside the limit.
        suffices h_simplify : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℝ) / n) * Real.exp (-h / 2)) Filter.atTop (nhds (Real.exp (-h / 2))) by
          convert h_simplify using 2 ; ring_nf;
          norm_num [ Real.exp_add, Real.exp_neg, mul_assoc, mul_comm, mul_left_comm ];
        norm_num [ add_div ];
        exact le_trans ( Filter.Tendsto.mul ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; aesop ) ) ( tendsto_inv_atTop_nhds_zero_nat ) ) tendsto_const_nhds ) ( by norm_num );
      refine' summable_of_ratio_test_tendsto_lt_one _ _ _ <;> norm_num at *;
      exacts [ Real.exp ( -h / 2 ), by rw [ Real.exp_lt_one_iff ] ; linarith, ⟨ 1, fun n hn => by linarith ⟩, by simpa [ abs_of_nonneg, add_nonneg ] using h_ratio_test ];
    convert h_series_conv.comp_injective ( add_left_injective 1 ) |> Summable.mul_left h |> Summable.add <| summable_geometric_of_lt_one ( by positivity ) ( show Real.exp ( -h / 2 ) < 1 from Real.exp_lt_one_iff.mpr <| by linarith ) |> Summable.comp_injective <| add_left_injective 1 using 2 ; norm_num ; ring_nf;
    rw [ ← Real.exp_nat_mul ] ; rw [ ← Real.exp_add ] ; ring_nf;
  refine' .of_nonneg_of_le ( fun r => _ ) ( fun r => _ ) ( h_comparison.mul_left ( h_bound.choose : ℝ ) );
  · positivity;
  · convert le_trans ( h_bound.choose_spec.2 ( ( r + 1 ) * h ) ( by positivity ) ) _ using 1 ; norm_num ; ring_nf;
    rw [ mul_assoc ] ; gcongr;
    · exact le_of_lt h_bound.choose_spec.1;
    · exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ mul_nonneg ( Nat.cast_nonneg r ) hh.le ] ⟩;
    · linarith

/-- H is nondecreasing: more primes enter the product as x grows. -/
lemma HFunc_mono : Monotone HFunc := by
  intro x y hxy; simp +decide [ HFunc ] ;
  rw [ ← Finset.prod_sdiff <| show Finset.filter Nat.Prime ( Finset.range ( ⌊Real.exp ( 2 * x ) ⌋₊ + 1 ) ) ⊆ Finset.filter Nat.Prime ( Finset.range ( ⌊Real.exp ( 2 * y ) ⌋₊ + 1 ) ) from Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ <| Nat.floor_mono <| Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_left hxy zero_le_two ];
  gcongr;
  · refine' mul_pos ( Finset.prod_pos fun p hp => sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| by aesop ) ( Finset.prod_pos fun p hp => sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| by aesop );
  · refine' mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by aesop ) _;
    exact Finset.prod_le_one ( fun _ _ => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => sub_le_self _ <| inv_nonneg.2 <| Nat.cast_nonneg _

/-- The Riemann sum is an upper bound for the integral (because g is nondecreasing). -/
lemma riemann_sum_ge_integral (h : ℝ) (hh : 0 < h) :
    (Real.exp h - 1) * ∑' (r : ℕ),
      Real.exp (-(↑(r + 1)) * h) *
      Real.sqrt (HFunc (↑(r + 1) * h) * (Real.exp (↑(r + 1) * h) - Real.exp (-(↑(r + 1)) * h))) ≥
    integralI := by
  have h_upper_bound : (Real.exp h - 1) * ∑' r : ℕ, Real.exp (-(r + 1 : ℝ) * h) * Real.sqrt (HFunc ((r + 1 : ℝ) * h) * (Real.exp ((r + 1 : ℝ) * h) - Real.exp (-(r + 1 : ℝ) * h))) ≥ ∑' r : ℕ, ∫ x in Set.Ioc ((r : ℝ) * h) ((r + 1 : ℝ) * h), Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x))) := by
    have h_upper_bound : ∀ r : ℕ, ∫ x in Set.Ioc ((r : ℝ) * h) ((r + 1 : ℝ) * h), Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x))) ≤ (Real.exp h - 1) * Real.exp (-(r + 1 : ℝ) * h) * Real.sqrt (HFunc ((r + 1 : ℝ) * h) * (Real.exp ((r + 1 : ℝ) * h) - Real.exp (-(r + 1 : ℝ) * h))) := by
      intro r
      have h_integral_bound : ∫ x in Set.Ioc ((r : ℝ) * h) ((r + 1 : ℝ) * h), Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x))) ≤ ∫ x in Set.Ioc ((r : ℝ) * h) ((r + 1 : ℝ) * h), Real.exp (-x) * Real.sqrt (HFunc ((r + 1 : ℝ) * h) * (Real.exp ((r + 1 : ℝ) * h) - Real.exp (-(r + 1 : ℝ) * h))) := by
        refine' MeasureTheory.setIntegral_mono_on _ _ _ _ <;> norm_num;
        · exact MeasureTheory.IntegrableOn.mono_set ( integrandF_integrable ) ( Set.Ioc_subset_Icc_self.trans ( Set.Icc_subset_Ici_self.trans ( Set.Ici_subset_Ici.2 <| by nlinarith ) ) );
        · exact Continuous.integrableOn_Ioc ( by continuity );
        · intro x hx₁ hx₂; gcongr;
          · exact sub_nonneg_of_le ( Real.exp_le_exp.mpr ( by nlinarith ) );
          · exact HFunc_nonneg _;
          · exact HFunc_mono ( by linarith );
          · linarith;
      convert h_integral_bound using 1 ; rw [ ← intervalIntegral.integral_of_le ( by nlinarith ) ] ; norm_num [ intervalIntegral.integral_comp_neg ] ; ring_nf;
      exact Or.inl ( by rw [ ← Real.exp_add ] ; ring_nf );
    refine' le_trans ( Summable.tsum_le_tsum h_upper_bound _ _ ) _;
    · have h_summable : Summable (fun r : ℕ => (Real.exp h - 1) * Real.exp (-(r + 1 : ℝ) * h) * Real.sqrt (HFunc ((r + 1 : ℝ) * h) * (Real.exp ((r + 1 : ℝ) * h) - Real.exp (-(r + 1 : ℝ) * h)))) := by
        convert Summable.mul_left ( Real.exp h - 1 ) ( riemann_sum_summable h hh ) using 2 ; ring_nf;
        grobner;
      exact Summable.of_nonneg_of_le ( fun r => MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun x hx => mul_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ ) ) h_upper_bound h_summable;
    · convert Summable.mul_left ( Real.exp h - 1 ) ( riemann_sum_summable h hh ) using 2 ; ring_nf;
      grobner;
    · norm_num [ mul_assoc, tsum_mul_left ];
  convert h_upper_bound using 1;
  · norm_cast;
  · rw [ ← MeasureTheory.integral_iUnion ];
    · rw [ show ( ⋃ n : ℕ, Set.Ioc ( n * h ) ( ( n + 1 ) * h ) ) = Set.Ioi 0 from ?_ ];
      · unfold integralI; rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ] ;
        rfl;
      · ext x;
        simp +zetaDelta at *;
        constructor;
        · rintro ⟨ i, hi₁, hi₂ ⟩ ; nlinarith;
        · intro hx_pos
          by_cases hx : x = ⌊x / h⌋₊ * h;
          · exact ⟨ ⌊x / h⌋₊ - 1, by cases n : ⌊x / h⌋₊ <;> norm_num [ n ] at * <;> nlinarith, by cases n : ⌊x / h⌋₊ <;> norm_num [ n ] at * <;> nlinarith ⟩;
          · exact ⟨ ⌊x / h⌋₊, lt_of_le_of_ne ( by nlinarith [ Nat.floor_le ( show 0 ≤ x / h by positivity ), mul_div_cancel₀ x hh.ne' ] ) ( Ne.symm hx ), by nlinarith [ Nat.lt_floor_add_one ( x / h ), mul_div_cancel₀ x hh.ne' ] ⟩;
    · exact fun _ => measurableSet_Ioc;
    · exact fun i j hij => Set.disjoint_left.mpr fun x hx₁ hx₂ => hij <| Nat.le_antisymm ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2 ] } ) ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2 ] } );
    · refine' MeasureTheory.IntegrableOn.mono_set _ _;
      exact Set.Ici 0;
      · convert integrandF_integrable using 1;
      · exact Set.iUnion_subset fun i => Set.Ioc_subset_Icc_self.trans ( Set.Icc_subset_Ici_self.trans ( Set.Ici_subset_Ici.2 <| by nlinarith ) )

/-- The Riemann sum is at most e^h times the integral. -/
lemma riemann_sum_le_exp_integral (h : ℝ) (hh : 0 < h) :
    (Real.exp h - 1) * ∑' (r : ℕ),
      Real.exp (-(↑(r + 1)) * h) *
      Real.sqrt (HFunc (↑(r + 1) * h) * (Real.exp (↑(r + 1) * h) - Real.exp (-(↑(r + 1)) * h)))
    ≤ Real.exp h * integralI := by
  -- Real.exp h * ∫₀^∞ e^{-x}·g(x+h) dx = ∫₀^∞ e^{-(x+h)}·g(x+h) dx
  suffices h_suff : (Real.exp h - 1) * ∑' r : ℕ, Real.exp (-(r + 1) * h) * Real.sqrt (HFunc ((r + 1) * h) * (Real.exp ((r + 1) * h) - Real.exp (-(r + 1) * h))) ≤ ∫ x in Set.Ici 0, Real.exp (-x) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h)))) by
    -- By changing variables $y = x + h$, we can rewrite the integral.
    have h_change_var : ∫ x in Set.Ici 0, Real.exp (-x) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h)))) = ∫ y in Set.Ici h, Real.exp (-(y - h)) * Real.sqrt (HFunc y * (Real.exp y - Real.exp (-y))) := by
      rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
      rw [ ← MeasureTheory.integral_sub_right_eq_self _ h ] ; congr ; ext x ; split_ifs <;> ring_nf <;> aesop;
    -- Since $HFunc$ is non-decreasing, we have $\int_h^\infty e^{-(y-h)} g(y) dy \leq \int_0^\infty e^{-(y-h)} g(y) dy$.
    have h_integral_le : ∫ y in Set.Ici h, Real.exp (-(y - h)) * Real.sqrt (HFunc y * (Real.exp y - Real.exp (-y))) ≤ ∫ y in Set.Ici 0, Real.exp (-(y - h)) * Real.sqrt (HFunc y * (Real.exp y - Real.exp (-y))) := by
      refine' MeasureTheory.setIntegral_mono_set _ _ _;
      · have h_integrable : MeasureTheory.IntegrableOn (fun y => Real.exp (-y) * Real.sqrt (HFunc y * (Real.exp y - Real.exp (-y)))) (Set.Ici 0) := by
          convert integrandF_integrable using 1;
        simp_all +decide [ sub_eq_add_neg, Real.exp_add ];
        simpa only [ mul_assoc ] using h_integrable.const_mul _;
      · exact Filter.Eventually.of_forall fun x => mul_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ );
      · exact MeasureTheory.ae_of_all _ fun x hx => le_trans hh.le hx;
    convert h_suff.trans ( h_change_var.le.trans h_integral_le ) using 1;
    · norm_cast;
    · unfold integralI; rw [ ← MeasureTheory.integral_const_mul ] ; congr; ext; ring_nf;
      unfold integrandF; rw [ Real.exp_add ] ; ring_nf;
  -- By Fubini's theorem, we can interchange the sum and the integral.
  have h_fubini : ∫ x in Set.Ici 0, Real.exp (-x) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h)))) = ∑' r : ℕ, ∫ x in Set.Ico (r * h) ((r + 1) * h), Real.exp (-x) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h)))) := by
    rw [ ← MeasureTheory.integral_iUnion ];
    · congr with x;
      simp +zetaDelta at *;
      exact ⟨ fun hx => ⟨ ⌊x / h⌋₊, by nlinarith [ Nat.floor_le ( show 0 ≤ x / h by exact div_nonneg hx hh.le ), mul_div_cancel₀ x hh.ne' ], by nlinarith [ Nat.lt_floor_add_one ( x / h ), mul_div_cancel₀ x hh.ne' ] ⟩, fun ⟨ i, hi₁, hi₂ ⟩ => by nlinarith ⟩;
    · exact fun i => measurableSet_Ico;
    · exact fun i j hij => Set.disjoint_left.mpr fun x hx₁ hx₂ => hij <| Nat.le_antisymm ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2 ] } ) ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2 ] } );
    · have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h))))) (Set.Ici 0) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x)))) (Set.Ici h) := by
          have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x)))) (Set.Ici 0) := by
            convert integrandF_integrable using 1;
          exact h_integrable.mono_set <| Set.Ici_subset_Ici.mpr hh.le;
        have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-(x + h)) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h))))) (Set.Ici 0) := by
          rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_Ici ) ] at *;
          convert h_integrable.comp_add_right h using 1;
          ext; simp [Set.indicator];
        simp_all +decide [ Real.exp_add, mul_assoc, mul_comm ];
        have := h_integrable.div_const ( Real.exp ( -h ) );
        simpa [ mul_div_assoc, Real.exp_ne_zero ] using this;
      exact h_integrable.mono_set <| Set.iUnion_subset fun i => Set.Ico_subset_Ici_self.trans <| Set.Ici_subset_Ici.2 <| by nlinarith;
  rw [ h_fubini, ← tsum_mul_left ];
  refine' Summable.tsum_le_tsum _ _ _;
  · intro r;
    -- Apply the inequality $g((r+1)h) \leq g(x+h)$ for $x \in [rh, (r+1)h]$.
    have h_ineq : ∀ x ∈ Set.Ico (r * h) ((r + 1) * h), Real.sqrt (HFunc ((r + 1) * h) * (Real.exp ((r + 1) * h) - Real.exp (-(r + 1) * h))) ≤ Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h)))) := by
      intros x hx
      have h_g_le : HFunc ((r + 1) * h) ≤ HFunc (x + h) := by
        exact HFunc_mono ( by linarith [ hx.1, hx.2 ] );
      gcongr;
      · exact sub_nonneg_of_le <| Real.exp_le_exp.mpr <| by nlinarith;
      · exact Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
      · linarith [ hx.1 ];
      · linarith [ hx.1, hx.2 ];
    refine' le_trans _ ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ico fun x hx => mul_le_mul_of_nonneg_left ( h_ineq x hx ) ( Real.exp_nonneg _ ) );
    · rw [ ← MeasureTheory.integral_Icc_eq_integral_Ico, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ( by linarith ) ] ; norm_num [ intervalIntegral.integral_comp_neg ] ; ring_nf ; norm_num [ hh.ne' ] ;
      rw [ ← Real.exp_add ] ; ring_nf ; norm_num;
    · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set ( Set.Ico_subset_Icc_self );
    · refine' MeasureTheory.IntegrableOn.mono_set _ ( Set.Ico_subset_Ici_self );
      have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h))))) (Set.Ici 0) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x)))) (Set.Ici h) := by
          have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x)))) (Set.Ici 0) := by
            convert integrandF_integrable using 1;
          exact h_integrable.mono_set <| Set.Ici_subset_Ici.mpr hh.le;
        have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-(x + h)) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h))))) (Set.Ici 0) := by
          rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_Ici ) ] at *;
          convert h_integrable.comp_add_right h using 1;
          ext; simp [Set.indicator];
        have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h))))) (Set.Ici 0) := by
          have : ∀ x ∈ Set.Ici 0, Real.exp (-x) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h)))) = Real.exp (-(x + h)) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h)))) * Real.exp h := by
            intro x hx; rw [ mul_right_comm ] ; rw [ ← Real.exp_add ] ; ring_nf;
          rw [ MeasureTheory.integrableOn_congr_fun ( fun x hx => this x hx ) measurableSet_Ici ] ; exact h_integrable.mul_const _;
        convert h_integrable using 1;
      exact h_integrable.mono_set <| Set.Ici_subset_Ici.mpr <| by positivity;
  · refine' Summable.mul_left _ _;
    have := riemann_sum_summable h hh;
    aesop;
  · contrapose! h_fubini;
    rw [ tsum_eq_zero_of_not_summable h_fubini ];
    refine' ne_of_gt ( _ );
    rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
    · simp +decide [ Function.support, Real.exp_ne_zero ];
      refine' lt_of_lt_of_le _ ( MeasureTheory.measure_mono _ );
      rotate_left;
      exact Set.Ioo 0 h;
      · intro x hx; simp_all +decide [Real.sqrt_eq_zero'];
        refine' ⟨ mul_pos _ _, hx.1.le ⟩;
        · exact Finset.prod_pos fun p hp => inv_pos.mpr <| sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
        · exact sub_pos_of_lt ( Real.exp_lt_exp.mpr ( by linarith ) );
      · simp +decide [ hh ];
    · exact Filter.Eventually.of_forall fun x => mul_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ );
    · have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x)))) (Set.Ici 0) := by
        convert integrandF_integrable using 1;
      have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-(x + h)) * Real.sqrt (HFunc (x + h) * (Real.exp (x + h) - Real.exp (-(x + h))))) (Set.Ici 0) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x)))) (Set.Ici h) := by
          exact h_integrable.mono_set <| Set.Ici_subset_Ici.mpr hh.le;
        rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_Ici ) ] at *;
        convert h_integrable.comp_add_right h using 1;
        ext; simp [Set.indicator];
      convert h_integrable.mul_const ( Real.exp h ) using 2 ; ring_nf;
      rw [ mul_right_comm, ← Real.exp_add ] ; ring_nf

/-- The Riemann sum converges to I as h → 0⁺. -/
lemma riemann_sum_convergence :
    ∀ ε > 0, ∃ h₀ > 0, ∀ h : ℝ, 0 < h → h < h₀ →
      |(Real.exp h - 1) * ∑' (r : ℕ),
        Real.exp (-(↑(r + 1)) * h) *
        Real.sqrt (HFunc (↑(r + 1) * h) * (Real.exp (↑(r + 1) * h) - Real.exp (-(↑(r + 1)) * h)))
       - integralI| < ε := by
  intro ε hε
  have hI_nn : 0 ≤ integralI :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ici fun x _ => integrandF_nonneg x
  refine ⟨Real.log (1 + ε / (integralI + 1)), Real.log_pos (by linarith [div_pos hε (by linarith : (0:ℝ) < integralI + 1)]), fun h hh hh₀ => ?_⟩
  have h_ge := riemann_sum_ge_integral h hh
  have h_diff_nn : 0 ≤ (Real.exp h - 1) * ∑' (r : ℕ), Real.exp (-(↑(r + 1)) * h) *
    Real.sqrt (HFunc (↑(r + 1) * h) * (Real.exp (↑(r + 1) * h) - Real.exp (-(↑(r + 1)) * h)))
    - integralI := by linarith
  rw [abs_of_nonneg h_diff_nn]
  have h_upper := riemann_sum_le_exp_integral h hh
  have h_exp_bound : Real.exp h < 1 + ε / (integralI + 1) := by
    have := Real.exp_lt_exp.mpr hh₀
    rwa [Real.exp_log (by linarith [div_pos hε (by linarith : (0:ℝ) < integralI + 1)])] at this
  -- D ≤ (e^h - 1) · I < ε/(I+1) · I ≤ ε
  have heh : Real.exp h - 1 < ε / (integralI + 1) := by linarith
  calc _ ≤ (Real.exp h - 1) * integralI := by linarith
    _ ≤ ε / (integralI + 1) * integralI := mul_le_mul_of_nonneg_right heh.le hI_nn
    _ < ε := by
        have : ε / (integralI + 1) * integralI < ε / (integralI + 1) * (integralI + 1) := by
          gcongr; linarith
        linarith [div_mul_cancel₀ ε (ne_of_gt (show (0:ℝ) < integralI + 1 by linarith))]

/-- I < 9263/2000 -/
axiom integralI_upper_bound : integralI < 9263/2000

/-- C_* < 13.1. From I < 9263/2000 and 2^{3/2} · (9263/2000) < 13.1. -/
lemma Cstar_lt : Cstar < 13.1 := by
  have h_mul : Cstar < 2 ^ (3 / 2 : ℝ) * (9263/2000) := by
    exact mul_lt_mul_of_pos_left ( integralI_upper_bound ) ( by positivity );
  exact h_mul.trans_le ( by rw [ show ( 2 : ℝ ) ^ ( 3 / 2 : ℝ ) = 2 * Real.sqrt 2 by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] )

end

end Analysis

section SievePhiHelpers

/-! Helper lemmas for sievePhi and filter counts. -/

open Finset BigOperators Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Monotonicity of sievePhi -/

lemma sievePhi_mono_x (x₁ x₂ y : ℕ) (h : x₁ ≤ x₂) : sievePhi x₁ y ≤ sievePhi x₂ y := by
  unfold sievePhi
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right h))

/-! ### Filter to sievePhi relationship -/

/-- The count of integers in (X₀, X₁] ∩ [1, n] with P⁻(m) ≥ Y is at most
    sievePhi(⌊X₁⌋₊, ⌈Y⌉₊) - sievePhi(⌊X₀⌋₊, ⌈Y⌉₊). -/
lemma filter_interval_le_sievePhi_diff (n : ℕ) (X₀ X₁ Y : ℝ)
    (hX₀_nn : 0 ≤ X₀) (_hn : ⌊X₁⌋₊ ≤ n) :
    ((Finset.Icc 1 n).filter (fun m : ℕ =>
      X₀ < (m : ℝ) ∧ (m : ℝ) ≤ X₁ ∧
      ∀ p : ℕ, Nat.Prime p → p ∣ m → (p : ℝ) ≥ Y)).card
    ≤ sievePhi ⌊X₁⌋₊ ⌈Y⌉₊ - sievePhi ⌊X₀⌋₊ ⌈Y⌉₊ := by
  by_cases hle : X₀ < X₁
  · have h_sub : ∀ m, m ∈ (Finset.Icc 1 n).filter (fun m : ℕ =>
        X₀ < (m : ℝ) ∧ (m : ℝ) ≤ X₁ ∧
        ∀ p : ℕ, Nat.Prime p → p ∣ m → (p : ℝ) ≥ Y) →
      m ∈ (Finset.Icc 1 ⌊X₁⌋₊).filter (fun m => ∀ p ∈ m.primeFactors, ⌈Y⌉₊ ≤ p) ∧
      m ∉ (Finset.Icc 1 ⌊X₀⌋₊).filter (fun m => ∀ p ∈ m.primeFactors, ⌈Y⌉₊ ≤ p) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      constructor
      · rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨(Finset.mem_Icc.mp hm.1).1, Nat.le_floor hm.2.2.1⟩,
          fun p hp => Nat.ceil_le.mpr (hm.2.2.2 p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))⟩
      · intro hmB
        rw [Finset.mem_filter, Finset.mem_Icc] at hmB
        linarith [(Nat.cast_le.mpr hmB.1.2).trans (Nat.floor_le hX₀_nn), hm.2.1]
    set A := (Finset.Icc 1 ⌊X₁⌋₊).filter (fun m => ∀ p ∈ m.primeFactors, ⌈Y⌉₊ ≤ p)
    set B := (Finset.Icc 1 ⌊X₀⌋₊).filter (fun m => ∀ p ∈ m.primeFactors, ⌈Y⌉₊ ≤ p)
    have hBA : B ⊆ A := Finset.filter_subset_filter _
      (Finset.Icc_subset_Icc_right (Nat.floor_le_floor hle.le))
    calc ((Finset.Icc 1 n).filter _).card
        ≤ (A \ B).card := Finset.card_le_card (fun m hm => Finset.mem_sdiff.mpr (h_sub m hm))
      _ = A.card - (B ∩ A).card := Finset.card_sdiff
      _ = A.card - B.card := by rw [Finset.inter_eq_left.mpr hBA]
      _ = sievePhi ⌊X₁⌋₊ ⌈Y⌉₊ - sievePhi ⌊X₀⌋₊ ⌈Y⌉₊ := rfl
  · push_neg at hle
    convert Nat.zero_le _
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _ ⟨h1, h2, _⟩; linarith

/-- Real-valued version. -/
lemma filter_interval_le_sievePhi_diff_real (n : ℕ) (X₀ X₁ Y : ℝ)
    (hX₀_nn : 0 ≤ X₀) (hX₀X₁ : X₀ ≤ X₁) (hn : ⌊X₁⌋₊ ≤ n) :
    (((Finset.Icc 1 n).filter (fun m : ℕ =>
      X₀ < (m : ℝ) ∧ (m : ℝ) ≤ X₁ ∧
      ∀ p : ℕ, Nat.Prime p → p ∣ m → (p : ℝ) ≥ Y)).card : ℝ)
    ≤ (sievePhi ⌊X₁⌋₊ ⌈Y⌉₊ : ℝ) - (sievePhi ⌊X₀⌋₊ ⌈Y⌉₊ : ℝ) := by
  have h_nat := filter_interval_le_sievePhi_diff n X₀ X₁ Y hX₀_nn hn
  have h_mono : sievePhi ⌊X₀⌋₊ ⌈Y⌉₊ ≤ sievePhi ⌊X₁⌋₊ ⌈Y⌉₊ :=
    sievePhi_mono_x _ _ _ (Nat.floor_le_floor hX₀X₁)
  have : (sievePhi ⌊X₁⌋₊ ⌈Y⌉₊ - sievePhi ⌊X₀⌋₊ ⌈Y⌉₊ : ℕ) =
      (sievePhi ⌊X₁⌋₊ ⌈Y⌉₊ : ℤ) - (sievePhi ⌊X₀⌋₊ ⌈Y⌉₊ : ℤ) := by omega
  exact_mod_cast h_nat.trans (by omega)

/-! ### Buchstab upper and lower bounds -/

/-- The Buchstab estimate gives an upper bound on sievePhi. -/
lemma buchstab_upper (U : ℝ) (hU : U ≥ 1) (hU3 : U ≤ 3) :
    ∃ K > 0, ∃ X₀ : ℝ, ∀ x y : ℝ, x ≥ X₀ → y ≥ 2 →
      1 ≤ Real.log x / Real.log y → Real.log x / Real.log y ≤ U →
        (sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℝ) ≤
          buchstabOmega (Real.log x / Real.log y) * x / Real.log y -
          y / Real.log y + K * x / (Real.log x) ^ 2 := by
  obtain ⟨K, hK, X₀, hbuchstab⟩ := buchstab_estimate U hU hU3
  exact ⟨K, hK, X₀, fun x y hx hy h1 h2 => by
    linarith [abs_le.mp (hbuchstab x y hx hy h1 h2)]⟩

/-- The Buchstab estimate also gives a lower bound on sievePhi. -/
lemma buchstab_lower (U : ℝ) (hU : U ≥ 1) (hU3 : U ≤ 3) :
    ∃ K > 0, ∃ X₀ : ℝ, ∀ x y : ℝ, x ≥ X₀ → y ≥ 2 →
      1 ≤ Real.log x / Real.log y → Real.log x / Real.log y ≤ U →
        (sievePhi ⌊x⌋₊ ⌈y⌉₊ : ℝ) ≥
          buchstabOmega (Real.log x / Real.log y) * x / Real.log y -
          y / Real.log y - K * x / (Real.log x) ^ 2 := by
  obtain ⟨K, hK, X₀, hbuchstab⟩ := buchstab_estimate U hU hU3
  exact ⟨K, hK, X₀, fun x y hx hy h1 h2 => by
    linarith [abs_le.mp (hbuchstab x y hx hy h1 h2)]⟩

/-! ### Buchstab subtraction lemma -/

/-- Buchstab subtraction: sievePhi difference ≤ ω·x/log y main terms + error. -/
lemma buchstab_subtraction (U : ℝ) (hU : U ≥ 1) (hU3 : U ≤ 3) :
    ∃ K > 0, ∃ X_min : ℝ, ∀ x₀ x₁ y : ℝ,
      x₀ ≥ X_min → x₁ ≥ X_min → y ≥ 2 →
      1 ≤ Real.log x₀ / Real.log y → Real.log x₀ / Real.log y ≤ U →
      1 ≤ Real.log x₁ / Real.log y → Real.log x₁ / Real.log y ≤ U →
      x₀ ≤ x₁ →
        (sievePhi ⌊x₁⌋₊ ⌈y⌉₊ : ℝ) - (sievePhi ⌊x₀⌋₊ ⌈y⌉₊ : ℝ) ≤
          buchstabOmega (Real.log x₁ / Real.log y) * x₁ / Real.log y -
          buchstabOmega (Real.log x₀ / Real.log y) * x₀ / Real.log y +
          K * x₁ / (Real.log x₁) ^ 2 + K * x₀ / (Real.log x₀) ^ 2 := by
  obtain ⟨K, hK_pos, X₀, hK⟩ := buchstab_upper U hU hU3
  obtain ⟨K', hK'_pos, X₀', hK'⟩ := buchstab_lower U hU hU3;
  refine' ⟨ Max.max K K', by positivity, Max.max X₀ ( Max.max X₀' 3 ), fun x₀ x₁ y hx₀ hx₁ hy hx₀' hx₀'' hx₁' hx₁'' hx₀₁ => _ ⟩ ; simp_all +decide [ div_eq_mul_inv ];
  nlinarith [ hK x₁ y hx₁.1 hy hx₁' hx₁'', hK' x₀ y hx₀.2.1 hy hx₀' hx₀'', le_max_left K K', le_max_right K K', show 0 < x₀ * ( Real.log x₀ ^ 2 ) ⁻¹ by exact mul_pos ( by linarith ) ( inv_pos.mpr ( sq_pos_of_pos ( Real.log_pos ( by linarith ) ) ) ), show 0 < x₁ * ( Real.log x₁ ^ 2 ) ⁻¹ by exact mul_pos ( by linarith ) ( inv_pos.mpr ( sq_pos_of_pos ( Real.log_pos ( by linarith ) ) ) ) ]

end

end SievePhiHelpers

section BuchstabDiff

/-
Buchstab difference bound: the key asymptotic estimate for the sifted interval lemmas.
-/

open Finset BigOperators Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Log ratio estimates -/

/-- For large n and r ≤ λ log log n, log(X₁)/log(Y) → U_α. -/
lemma log_ratio_near_UAlpha (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hh : 0 < h_val) (delta : ℝ) (hdelta : 0 < delta) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        |Real.log (Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) /
         Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)) - UAlpha alpha| < delta ∧
        |Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) /
         Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)) - UAlpha alpha| < delta := by
  -- For large n, the term rh / log(n) tends to 0.
  have hrh_log_n_zero : Filter.Tendsto (fun n : ℕ => (Nat.floor (lambda * Real.log (Real.log n)) * h_val) / Real.log n) Filter.atTop (nhds 0) := by
    -- We'll use the fact that $\frac{\log \log n}{\log n}$ tends to $0$ as $n$ tends to infinity.
    have h_log_log : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) Filter.atTop (nhds 0) := by
      -- Let $y = \log n$, therefore the expression becomes $\frac{\log y}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
      suffices h_log_z : Filter.Tendsto (fun z : ℝ => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    -- We'll use the fact that $\frac{\lfloor \lambda \log \log n \rfloor}{\log n}$ tends to $0$ as $n$ tends to infinity.
    have h_floor_log_log : Filter.Tendsto (fun n : ℕ => (Nat.floor (lambda * Real.log (Real.log n)) : ℝ) / Real.log n) Filter.atTop (nhds 0) := by
      refine' squeeze_zero_norm' _ ( by simpa using h_log_log.const_mul ( lambda : ℝ ) );
      filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ⌈Real.exp 1⌉₊ ] with n hn hn' using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ mul_div ] ; exact div_le_div_of_nonneg_right ( Nat.floor_le ( by exact mul_nonneg hlambda.le ( Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact le_trans ( Nat.le_ceil _ ) <| mod_cast hn'.le ) ) ) <| Real.log_nonneg <| by norm_cast; linarith;
    convert h_floor_log_log.const_mul h_val using 2 <;> ring;
  -- For large n, the term (r-1)h / log(n) tends to 0.
  have hr_minus_one_h_log_n_zero : Filter.Tendsto (fun n : ℕ => ((Nat.floor (lambda * Real.log (Real.log n)) - 1) * h_val) / Real.log n) Filter.atTop (nhds 0) := by
    convert hrh_log_n_zero.sub ( show Filter.Tendsto ( fun n : ℕ => h_val / Real.log n ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) using 2 <;> ring;
  -- Using the fact that the ratios converge to UAlpha(alpha), we can find such an N.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℕ, 1 ≤ r → r ≤ Nat.floor (lambda * Real.log (Real.log n)) →
    |(1 / 2 - (r - 1) * h_val / Real.log n) / (alpha - 1 / 2 - r * h_val / Real.log n) - UAlpha alpha| < delta / 2 ∧
    |(1 / 2 - r * h_val / Real.log n) / (alpha - 1 / 2 - r * h_val / Real.log n) - UAlpha alpha| < delta / 2 := by
      have h_cont : Filter.Tendsto (fun (p : ℝ × ℝ) => (1 / 2 - p.1) / (alpha - 1 / 2 - p.2)) (nhds (0, 0)) (nhds (UAlpha alpha)) := by
        convert Filter.Tendsto.div ( tendsto_const_nhds.sub ( continuous_fst.tendsto _ ) ) ( tendsto_const_nhds.sub ( continuous_snd.tendsto _ ) ) _ using 2 <;> norm_num [ UAlpha ];
        exacts [ by rw [ inv_eq_one_div, div_div ] ; ring, by infer_instance, by infer_instance, by infer_instance, by infer_instance, by linarith ];
      have := Metric.tendsto_nhds_nhds.mp h_cont ( delta / 2 ) ( half_pos hdelta );
      obtain ⟨ δ, hδ, H ⟩ := this; rcases Metric.tendsto_atTop.mp hr_minus_one_h_log_n_zero δ hδ with ⟨ N₁, hN₁ ⟩ ; rcases Metric.tendsto_atTop.mp hrh_log_n_zero δ hδ with ⟨ N₂, hN₂ ⟩ ; refine' ⟨ Max.max N₁ N₂, fun n hn r hr₁ hr₂ => ⟨ _, _ ⟩ ⟩ <;> simp_all +decide [ Prod.dist_eq ] ;
      · convert H ( ( r - 1 ) * h_val / Real.log n ) ( r * h_val / Real.log n ) _ _ using 1 <;> norm_num [ abs_div, abs_mul ] at *;
        · refine' lt_of_le_of_lt _ ( hN₁ n hn.1 );
          gcongr ; norm_cast;
          exact Nat.zero_le _;
        · exact lt_of_le_of_lt ( by gcongr ) ( hN₂ n hn.2 );
      · convert H ( r * h_val / Real.log n ) ( r * h_val / Real.log n ) _ _ using 1 <;> norm_num [ abs_div, abs_mul, abs_of_pos hh ];
        · exact lt_of_le_of_lt ( by rw [ abs_of_pos hh ] ; exact div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hr₂ ) hh.le ) ( abs_nonneg _ ) ) ( hN₂ n hn.2 );
        · exact lt_of_le_of_lt ( by rw [ abs_of_pos hh ] ; exact div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hr₂ ) hh.le ) ( abs_nonneg _ ) ) ( hN₂ n hn.2 );
  refine' ⟨ N + 2, fun n hn r hr₁ hr₂ => _ ⟩ ; specialize hN n ( by linarith ) r hr₁ hr₂ ; norm_num [ Real.log_mul, Real.exp_ne_zero, show n ≠ 0 by linarith ] at *;
  rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ), Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ), Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ), Real.log_exp, Real.log_exp, Real.log_rpow ( by norm_cast; linarith ), Real.log_rpow ( by norm_cast; linarith ) ] at *;
  by_cases h : Real.log n = 0 <;> simp_all +decide [mul_assoc, mul_comm, mul_left_comm,
    div_eq_mul_inv];
  convert And.intro ( lt_of_lt_of_le hN.1 ( mul_le_of_le_one_right hdelta.le ( by norm_num ) ) ) ( lt_of_lt_of_le hN.2 ( mul_le_of_le_one_right hdelta.le ( by norm_num ) ) ) using 1 <;> ring_nf;
  · rw [ show ( - ( h_val * r ) + Real.log n * ( -1 / 2 ) + Real.log n * alpha ) = ( Real.log n ) * ( -1 / 2 - h_val * r * ( Real.log n ) ⁻¹ + alpha ) by nlinarith [ mul_inv_cancel_left₀ ( show Real.log n ≠ 0 from ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) ( h_val * r ) ] ] ; norm_num ; ring_nf;
    rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ) ] ; ring_nf;
  · field_simp;
    rw [ show ( - ( h_val * r * 2 ) + -Real.log n + Real.log n * 2 * alpha ) = Real.log n * ( -1 - h_val * r * 2 / Real.log n + 2 * alpha ) by nlinarith [ Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ), mul_div_cancel₀ ( h_val * r * 2 ) ( ne_of_gt ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ) ) ] ] ; ring_nf;
    rw [ show ( -1 - h_val * r * ( Real.log n ) ⁻¹ * 2 + alpha * 2 ) = ( - ( h_val * r * Real.log n * ( Real.log n ) ⁻¹ * 2 ) - Real.log n + Real.log n * alpha * 2 ) / Real.log n by rw [ eq_div_iff ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith ) ) ) ] ; ring ] ; norm_num ; ring_nf

/-
For large n and r ≤ λ·log(log n), X₁ and X₀ are large. -/
lemma X_values_large (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hh : 0 < h_val) (M : ℝ) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) ≥ M ∧
        Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) ≥ M := by
  -- Let's choose any $M > 0$.
  have h_exp_log : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) / Real.exp (lambda * h_val * Real.log (Real.log n))) Filter.atTop Filter.atTop := by
    -- We can rewrite the limit expression using properties of exponents and logarithms.
    suffices h_rewrite : Filter.Tendsto (fun n : ℕ => Real.exp ((1 / 2 : ℝ) * Real.log n - lambda * h_val * Real.log (Real.log n))) Filter.atTop Filter.atTop by
      refine h_rewrite.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; rw [ Real.exp_sub ] ; ring_nf );
    -- We can use the fact that $\log(n)$ grows faster than $\log(\log(n))$.
    have h_log_growth : Filter.Tendsto (fun n : ℕ => Real.log n / Real.log (Real.log n)) Filter.atTop Filter.atTop := by
      -- We can use the change of variables $u = \log n$ to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun u : ℝ => u / Real.log u) Filter.atTop Filter.atTop by
        exact h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      -- We can use the change of variables $v = \log u$ to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun v : ℝ => Real.exp v / v) Filter.atTop Filter.atTop by
        have := h_log.comp Real.tendsto_log_atTop;
        exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
      simpa using Real.tendsto_exp_div_pow_atTop 1;
    have h_log_growth : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n) * ((1 / 2 : ℝ) * (Real.log n / Real.log (Real.log n)) - lambda * h_val)) Filter.atTop Filter.atTop := by
      have h_log_growth : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (Real.log n / Real.log (Real.log n)) - lambda * h_val) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.atTop_add ( h_log_growth.const_mul_atTop ( by norm_num ) ) tendsto_const_nhds;
      exact Filter.Tendsto.atTop_mul_atTop₀ ( Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop ) h_log_growth;
    refine' Real.tendsto_exp_atTop.comp _;
    refine h_log_growth.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn; rw [ mul_sub, mul_left_comm, mul_div_cancel₀ _ ( ne_of_gt <| Real.log_pos <| show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ] ; ring );
  have := h_exp_log.eventually_gt_atTop ( Max.max M 1 );
  obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp this;
  refine' ⟨ N + 3, fun n hn r hr₁ hr₂ => ⟨ _, _ ⟩ ⟩ <;> have := hN n ( by linarith ) <;> norm_num at *;
  · refine' le_trans this.1.le _;
    rw [ div_le_iff₀ ( Real.exp_pos _ ) ];
    rw [ mul_right_comm, ← Real.exp_add ];
    exact le_mul_of_one_le_left ( by positivity ) ( Real.one_le_exp ( by nlinarith [ show ( r : ℝ ) ≤ lambda * Real.log ( Real.log n ) by exact le_trans ( Nat.cast_le.mpr hr₂ ) ( Nat.floor_le ( mul_nonneg hlambda.le ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) ) ) ] ) );
  · rw [ lt_div_iff₀ ( Real.exp_pos _ ) ] at this;
    refine' le_trans _ ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr <| show - ( ( r - 1 ) * h_val ) ≥ - ( lambda * h_val * Real.log ( Real.log n ) ) from _ ) <| by positivity );
    · rw [ Real.exp_neg ];
      rw [ ← div_eq_inv_mul, le_div_iff₀ ( Real.exp_pos _ ) ] ; linarith;
    · rw [ Nat.le_floor_iff ( mul_nonneg hlambda.le <| Real.log_nonneg <| show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le <| by norm_cast; linarith ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ] at hr₂ ; nlinarith [ show ( r : ℝ ) ≥ 1 by norm_cast ]

/-- For large n, Y = e^{-rh}·n^{α-1/2} ≥ 2. -/
lemma Y_large (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hh : 0 < h_val) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2) ≥ 2 := by
  -- Since $\exp(-r \cdot h) \geq \exp(-\lambda \cdot h \cdot \log(\log n)) = (\log n)^{-\lambda h}$, we have $Y = n^{\alpha - 1/2} / (\log n)^{\lambda h}$.
  suffices h_Y_ge_two : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (n : ℝ) ^ (alpha - 1/2) / (Real.log n) ^ (lambda * h_val) ≥ 2 by
    obtain ⟨ N, hN ⟩ := h_Y_ge_two;
    refine' ⟨ N + 3, fun n hn r hr₁ hr₂ => le_trans ( hN n <| by linarith ) _ ⟩ ; refine' le_trans _ ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr <| neg_le_neg <| mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hr₂ ) hh.le ) <| Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ );
    rw [ div_eq_mul_inv, mul_comm ];
    gcongr;
    rw [ ← Real.log_le_log_iff ( by exact inv_pos.mpr ( Real.rpow_pos_of_pos ( Real.log_pos ( by norm_cast; linarith ) ) _ ) ) ( by positivity ), Real.log_inv, Real.log_rpow ( Real.log_pos ( by norm_cast; linarith ) ), Real.log_exp ] ; nlinarith [ Nat.floor_le ( show 0 ≤ lambda * Real.log ( Real.log n ) by exact mul_nonneg hlambda.le ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) ) ];
  -- We'll use that $n^{1/6} / (\log n)^{\lambda h}$ grows faster than any power of $\log n$.
  have h_growth : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 6 : ℝ) / (Real.log n) ^ (lambda * h_val)) Filter.atTop Filter.atTop := by
    -- We can use the change of variables $u = \log n$ to transform the limit expression.
    suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp (u / 6) / u ^ (lambda * h_val)) Filter.atTop Filter.atTop by
      have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
    -- Let $y = \frac{u}{6}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{e^y}{(6y)^{\lambda h_val}}$.
    suffices h_y : Filter.Tendsto (fun y : ℝ => Real.exp y / (6 * y) ^ (lambda * h_val)) Filter.atTop Filter.atTop by
      convert h_y.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 6⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
    -- We can use the fact that $\exp(y) / y^{\lambda h_val}$ tends to infinity as $y$ tends to infinity.
    have h_exp_y : Filter.Tendsto (fun y : ℝ => Real.exp y / y ^ (lambda * h_val)) Filter.atTop Filter.atTop := by
      exact tendsto_exp_div_rpow_atTop (lambda * h_val);
    have h_exp_y : Filter.Tendsto (fun y : ℝ => Real.exp y / y ^ (lambda * h_val) * (1 / 6 ^ (lambda * h_val))) Filter.atTop Filter.atTop := by
      exact h_exp_y.atTop_mul_const ( by positivity );
    refine h_exp_y.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring );
  exact Filter.eventually_atTop.mp ( h_growth.eventually_ge_atTop 2 ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N + 2, fun n hn ↦ le_trans ( hN n ( by linarith ) ) ( by exact div_le_div_of_nonneg_right ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( by linarith ) ) ( Real.rpow_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) _ ) ) ⟩

/-- Buchstab error is small relative to (eʰ-1)e^{-rh}√n/log n. -/
lemma buchstab_error_small (alpha h_val : ℝ) (_hα1 : 2/3 ≤ alpha) (_hα2 : alpha < 3/4)
    (hh : 0 < h_val) (K : ℝ) (_hK : K > 0)
    (delta : ℝ) (hdelta : 0 < delta) (lambda : ℝ) (_hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        K * Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) / (Real.log n) ^ 2 +
        K * Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) / (Real.log n) ^ 2 ≤
        delta * (Real.exp h_val - 1) * Real.exp (-((r : ℝ) * h_val)) *
          (n : ℝ) ^ (1/2 : ℝ) / Real.log n := by
  -- We can factor out $e^{-rh} \cdot n^{1/2} / \log n$ from both sides of the inequality.
  suffices h_factor : ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
    K * (Real.exp h_val + 1) / Real.log n ≤ delta * (Real.exp h_val - 1) by
      obtain ⟨ N, hN ⟩ := h_factor; use N + 2; intros n hn r hr₁ hr₂; specialize hN n ( by linarith ) r hr₁ hr₂; rw [ div_le_iff₀ ] at hN <;> norm_num at *;
      · convert mul_le_mul_of_nonneg_right hN ( show 0 ≤ Real.exp ( - ( r * h_val ) ) * ( n : ℝ ) ^ ( 1 / 2 : ℝ ) / Real.log n ^ 2 by positivity ) using 1 <;> ring_nf;
        · rw [ Real.exp_add ] ; ring;
        · by_cases h : Real.log n = 0 <;> simp_all +decide [ sq, mul_assoc ];
      · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith;
  have h_factor : Filter.Tendsto (fun n : ℕ => K * (Real.exp h_val + 1) / Real.log n) Filter.atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
  exact Filter.eventually_atTop.mp ( h_factor.eventually ( ge_mem_nhds <| mul_pos hdelta <| sub_pos.mpr <| by norm_num; positivity ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N, fun n hn r hr₁ hr₂ ↦ hN n hn ⟩

/-! ### Log X bounds -/

/-- For large n, log(e^{-c*h}*n^{1/2}) ≥ (1/4)*log(n) when c*h ≤ λh*log(log n). -/
lemma log_X_lower (h_val : ℝ) (hh : 0 < h_val) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) ≥ (1/4) * Real.log n ∧
        Real.log (Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) ≥ (1/4) * Real.log n := by
  have h_bound : ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℕ, 1 ≤ r → r ≤ Nat.floor (lambda * Real.log (Real.log n)) → (lambda * h_val * Real.log (Real.log n)) ≤ (1/4) * Real.log n := by
    -- We'll use that $\frac{\log(\log n)}{\log n}$ tends to $0$ as $n$ tends to infinity.
    have h_log_log_div_log : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) Filter.atTop (nhds 0) := by
      have h_log_log : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
        suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
      exact h_log_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    have := h_log_log_div_log.eventually ( gt_mem_nhds <| show 0 < ( 1 / 4 ) / ( lambda * h_val ) by positivity );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; exact ⟨ N + 2, fun n hn r hr₁ hr₂ => by have := hN n ( by linarith ) ; rw [ div_lt_div_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ( by positivity ) ] at this; nlinarith ⟩ ;
  obtain ⟨ N, hN ⟩ := h_bound; use Max.max N 3; intro n hn r hr₁ hr₂; rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith [ le_max_right N 3 ] ) _ ) ), Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith [ le_max_right N 3 ] ) _ ) ) ] ; norm_num [ Real.log_rpow ( Nat.cast_pos.mpr <| by linarith [ le_max_right N 3 ] : 0 < ( n : ℝ ) ) ] ;
  constructor <;> nlinarith [ hN n ( le_trans ( le_max_left _ _ ) hn ) r hr₁ hr₂, show ( r : ℝ ) ≤ lambda * Real.log ( Real.log n ) from Nat.floor_le ( show 0 ≤ lambda * Real.log ( Real.log n ) from mul_nonneg hlambda.le ( Real.log_nonneg <| show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le <| Nat.cast_pos.mpr <| by linarith [ le_max_right N 3 ] ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith [ le_max_right N 3 ] ] ) ) |> le_trans ( Nat.cast_le.mpr hr₂ ) ]

/-- Bridge: for large n, K·X_i/(log X_i)² ≤ 16K·X_i/(log n)² -/
lemma error_log_bridge (h_val K : ℝ) (hh : 0 < h_val) (hK : K > 0) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        K * (Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) /
          (Real.log (Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ))) ^ 2 +
        K * (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) /
          (Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ))) ^ 2 ≤
        16 * K * (Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) / (Real.log n) ^ 2 +
        16 * K * (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) / (Real.log n) ^ 2 := by
  have := log_X_lower h_val hh lambda hlambda;
  obtain ⟨ N, hN ⟩ := this; use N + 2; intros n hn r hr₁ hr₂; specialize hN n ( by linarith ) r hr₁ hr₂; norm_num at *;
  refine' add_le_add _ _;
  · rw [ div_le_div_iff₀ ];
    · nlinarith [ show 0 ≤ K * ( Real.exp ( - ( ( r - 1 ) * h_val ) ) * n ^ ( 1 / 2 : ℝ ) ) by positivity, pow_le_pow_left₀ ( by positivity ) hN.2 2 ];
    · exact sq_pos_of_pos ( lt_of_lt_of_le ( by exact mul_pos ( by norm_num ) ( Real.log_pos ( by norm_cast; linarith ) ) ) hN.2 );
    · exact sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith;
  · rw [ div_le_div_iff₀ ] <;> try nlinarith [ show 0 < Real.log n from Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ];
    convert mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) hN.1 2 ) ( show 0 ≤ 16 * K * ( Real.exp ( - ( r * h_val ) ) * n ^ ( 1 / 2 : ℝ ) ) by positivity ) using 1 ; ring

/-! ### logY approximation -/

/-- For large n, log Y ≥ (α-1/2-δ)·log n. -/
lemma logY_lower (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hh : 0 < h_val) (delta : ℝ) (hdelta : 0 < delta) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)) ≥
          (alpha - 1/2 - delta) * Real.log n := by
  -- For large n, λh·log(log n) ≤ δ·log(n).
  have h_log_log : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (lambda * h_val * Real.log (Real.log n)) ≤ delta * Real.log n := by
    -- We can divide both sides by $\log n$ and use the fact that $\frac{\log \log n}{\log n} \to 0$ as $n \to \infty$.
    have h_log_log_div_log : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) Filter.atTop (nhds 0) := by
      -- Let $y = \log n$, therefore the expression becomes $\frac{\log y}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
      suffices h_log_z : Filter.Tendsto (fun z : ℝ => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    have := h_log_log_div_log.const_mul ( lambda * h_val );
    simp +zetaDelta at *;
    exact Filter.eventually_atTop.mp ( this.eventually ( gt_mem_nhds hdelta ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N + 2, fun n hn ↦ by have := hN n ( by linarith ) ; rw [ mul_div, div_lt_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ] at this; linarith ⟩;
  obtain ⟨ N, hN ⟩ := h_log_log;
  refine' ⟨ N + 3, fun n hn r hr₁ hr₂ => _ ⟩ ; rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ), Real.log_rpow ( Nat.cast_pos.mpr <| by linarith ), Real.log_exp ] ; ring_nf at *;
  nlinarith [ show ( r : ℝ ) ≤ lambda * Real.log ( Real.log n ) by exact le_trans ( Nat.cast_le.mpr hr₂ ) ( Nat.floor_le ( mul_nonneg hlambda.le ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) ) ), hN n ( by linarith ) ]

/-! ### Algebraic facts about OmegaAlpha -/

/-- OmegaAlpha(α) = ω(UAlpha(α)) / (α - 1/2) -/
lemma OmegaAlpha_div_eq (alpha : ℝ) (hα1 : 2/3 ≤ alpha) (_hα2 : alpha < 3/4) :
    OmegaAlpha alpha * (alpha - 1/2) = buchstabOmega (UAlpha alpha) := by
  unfold OmegaAlpha UAlpha;
  grind

/-- For large n, |ω(log X_i / log Y) - ω(UAlpha)| < δ uniformly for r ≤ λ·log(log n). -/
lemma buchstabOmega_near_UAlpha (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hh : 0 < h_val) (delta : ℝ) (hdelta : 0 < delta) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        |buchstabOmega (Real.log (Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) /
         Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2))) -
         buchstabOmega (UAlpha alpha)| < delta ∧
        |buchstabOmega (Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) /
         Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2))) -
         buchstabOmega (UAlpha alpha)| < delta := by
  obtain ⟨ L, hL_pos, hL ⟩ := buchstabOmega_lipschitz_on 1 4 ( by norm_num ) ( by norm_num );
  obtain ⟨ N₁, hN₁ ⟩ := log_ratio_near_UAlpha alpha h_val hα1 hα2 hh ( delta / L ) ( div_pos hdelta hL_pos ) lambda hlambda;
  obtain ⟨ N₂, hN₂ ⟩ := UAlpha_range alpha hα1 hα2;
  obtain ⟨ N₃, hN₃ ⟩ := log_ratio_near_UAlpha alpha h_val hα1 hα2 hh ( 1 : ℝ ) zero_lt_one lambda hlambda;
  use Max.max N₁ N₃;
  intro n hn r hr₁ hr₂; specialize hN₁ n ( le_trans ( le_max_left _ _ ) hn ) r hr₁ hr₂; specialize hN₃ n ( le_trans ( le_max_right _ _ ) hn ) r hr₁ hr₂;
  exact ⟨ lt_of_le_of_lt ( hL _ _ ( by linarith [ abs_lt.mp hN₃.1 ] ) ( by linarith [ abs_lt.mp hN₃.1 ] ) ( by linarith ) ( by linarith ) ) ( by nlinarith [ abs_lt.mp hN₁.1, mul_div_cancel₀ delta hL_pos.ne' ] ), lt_of_le_of_lt ( hL _ _ ( by linarith [ abs_lt.mp hN₃.2 ] ) ( by linarith [ abs_lt.mp hN₃.2 ] ) ( by linarith ) ( by linarith ) ) ( by nlinarith [ abs_lt.mp hN₁.2, mul_div_cancel₀ delta hL_pos.ne' ] ) ⟩

/-! ### Main term bound -/

/-- The Buchstab main term ω(u₁)·X₁/logY - ω(u₀)·X₀/logY is at most
    (Ω_α + ε)·(e^h-1)·e^{-rh}·n^{1/2}/log n for large n. -/
lemma buchstab_main_term_bound
    (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hh : 0 < h_val) (ε : ℝ) (hε : 0 < ε) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        let X₁ := Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)
        let X₀ := Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)
        let Y := Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)
        buchstabOmega (Real.log X₁ / Real.log Y) * X₁ / Real.log Y -
        buchstabOmega (Real.log X₀ / Real.log Y) * X₀ / Real.log Y ≤
        (OmegaAlpha alpha + ε / 2) * (Real.exp h_val - 1) * Real.exp (-((r : ℝ) * h_val)) *
          (n : ℝ) ^ (1/2 : ℝ) / Real.log n := by
  -- Choose approximation parameters
  set c := alpha - 1/2 with hc_def
  have hc_pos : c > 0 := by linarith
  set ωU := buchstabOmega (UAlpha alpha) with hωU_def
  have hωU_pos : ωU > 0 := buchstabOmega_pos _ (by rw [UAlpha]; rw [le_div_iff₀ (by linarith)]; linarith)
  have hOmega_eq : OmegaAlpha alpha * c = ωU := OmegaAlpha_div_eq alpha hα1 hα2
  have heh_pos : Real.exp h_val - 1 > 0 := by linarith [Real.add_one_le_exp h_val]
  have heh1_pos : Real.exp h_val + 1 > 0 := by linarith [Real.exp_pos h_val]
  set δ₁ := min (ε * c * (Real.exp h_val - 1) / (16 * (Real.exp h_val + 1))) (c / 2) with hδ₁_def
  have hδ₁_pos : δ₁ > 0 := lt_min (by positivity) (by positivity)
  set δ₂ := min (ε * c ^ 2 / (16 * (ωU + 1))) (c / 2) with hδ₂_def
  have hδ₂_pos : δ₂ > 0 := lt_min (by positivity) (by positivity)
  have hδ₂_lt_c : δ₂ < c := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- Get all the N values
  obtain ⟨N₁, hN₁⟩ := buchstabOmega_near_UAlpha alpha h_val hα1 hα2 hh δ₁ hδ₁_pos lambda hlambda
  obtain ⟨N₂, hN₂⟩ := logY_lower alpha h_val hα1 hα2 hh δ₂ hδ₂_pos lambda hlambda
  refine ⟨max (max N₁ N₂) 4, fun n hn r hr₁ hr₂ => ?_⟩
  -- Extract hypotheses
  have hn_ge : n ≥ 4 := le_trans (le_max_right _ _) hn
  have hN₁' := hN₁ n (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)) r hr₁ hr₂
  have hN₂' := hN₂ n (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)) r hr₁ hr₂
  -- Set up names
  set X₁ := Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)
  set X₀ := Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)
  set Y := Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)
  set u₁ := Real.log X₁ / Real.log Y
  set u₀ := Real.log X₀ / Real.log Y
  have hX₀_pos : X₀ > 0 := by positivity
  have hX₁_pos : X₁ > 0 := by positivity
  have hlogY_pos : Real.log Y > 0 := by
    calc Real.log Y ≥ (c - δ₂) * Real.log n := hN₂'
    _ > 0 := by
      apply mul_pos (by linarith)
      exact Real.log_pos (Nat.one_lt_cast.mpr (by linarith))
  have hlogn_pos : Real.log n > 0 := Real.log_pos (Nat.one_lt_cast.mpr (by linarith))
  -- Key fact: X₁ = e^h * X₀
  have hX₁_eq : X₁ = Real.exp h_val * X₀ := by
    simp only [X₁, X₀]
    rw [show -(((r : ℝ) - 1) * h_val) = h_val + -((r : ℝ) * h_val) by ring]
    rw [Real.exp_add]; ring
  -- Step 1: Algebraic decomposition
  have h_decomp : buchstabOmega u₁ * X₁ / Real.log Y - buchstabOmega u₀ * X₀ / Real.log Y =
    (buchstabOmega u₁ * (Real.exp h_val - 1) + (buchstabOmega u₁ - buchstabOmega u₀)) *
      X₀ / Real.log Y := by
    rw [hX₁_eq]; ring
  -- Step 2: Bound |ω(u₁) - ω(u₀)| ≤ 2δ₁
  have hω_diff : buchstabOmega u₁ - buchstabOmega u₀ ≤ 2 * δ₁ := by
    have h1 : buchstabOmega u₁ - ωU ≤ δ₁ := by linarith [abs_le.mp (le_of_lt hN₁'.1)]
    have h2 : ωU - buchstabOmega u₀ ≤ δ₁ := by linarith [abs_le.mp (le_of_lt hN₁'.2)]
    linarith
  -- Step 3: Bound ω(u₁) ≤ ωU + δ₁
  have hω_bound : buchstabOmega u₁ ≤ ωU + δ₁ := by
    linarith [abs_le.mp (le_of_lt hN₁'.1)]
  -- Step 4: logY ≥ (c - δ₂) * logn
  have hlogY_ge : Real.log Y ≥ (c - δ₂) * Real.log n := hN₂'
  -- Step 5: Combine
  simp only
  rw [h_decomp]
  -- Bound the expression
  -- Step A: Upper bound using ω bounds
  have h_step_a : (buchstabOmega u₁ * (Real.exp h_val - 1) + (buchstabOmega u₁ - buchstabOmega u₀)) * X₀ / Real.log Y
    ≤ ((ωU + δ₁) * (Real.exp h_val - 1) + 2 * δ₁) * X₀ / Real.log Y := by
        apply div_le_div_of_nonneg_right _ hlogY_pos.le
        apply mul_le_mul_of_nonneg_right _ hX₀_pos.le
        have := mul_le_mul_of_nonneg_right hω_bound heh_pos.le
        linarith
  -- Step B: Replace logY by (c - δ₂)*logn in denominator
  have h_coeff_nn : ((ωU + δ₁) * (Real.exp h_val - 1) + 2 * δ₁) ≥ 0 := by positivity
  have h_step_b : ((ωU + δ₁) * (Real.exp h_val - 1) + 2 * δ₁) * X₀ / Real.log Y
    ≤ ((ωU + δ₁) * (Real.exp h_val - 1) + 2 * δ₁) * X₀ / ((c - δ₂) * Real.log n) := by
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos (by linarith) hlogn_pos) hlogY_ge
  -- Step C: Core inequality
  have h_step_c : ((ωU + δ₁) * (Real.exp h_val - 1) + 2 * δ₁) * X₀ / ((c - δ₂) * Real.log n)
    ≤ (OmegaAlpha alpha + ε / 2) * (Real.exp h_val - 1) * X₀ / Real.log n := by
        rw [div_le_div_iff₀ (mul_pos (by linarith) hlogn_pos) hlogn_pos]
        -- Cancel X₀ * logn from both sides (both positive)
        have hX₀logn_pos : X₀ * Real.log n > 0 := mul_pos hX₀_pos hlogn_pos
        -- It suffices to show: (ωU + δ₁)*(e^h-1) + 2δ₁ ≤ (OmegaAlpha + ε/2)*(e^h-1)*(c-δ₂)
        suffices h_ineq : (ωU + δ₁) * (Real.exp h_val - 1) + 2 * δ₁ ≤
            (OmegaAlpha alpha + ε / 2) * (Real.exp h_val - 1) * (c - δ₂) by nlinarith
        -- Rewrite OmegaAlpha = ωU / c using hOmega_eq
        have hOmega_eq' : OmegaAlpha alpha = ωU / c := by
          rw [← hOmega_eq]; field_simp
        rw [hOmega_eq']
        have hδ₁_le1 : δ₁ ≤ ε * c * (Real.exp h_val - 1) / (16 * (Real.exp h_val + 1)) := min_le_left _ _
        have hδ₁_le2 : δ₁ ≤ c / 2 := min_le_right _ _
        have hδ₂_le1 : δ₂ ≤ ε * c ^ 2 / (16 * (ωU + 1)) := min_le_left _ _
        have hδ₂_le2 : δ₂ ≤ c / 2 := min_le_right _ _
        -- Key bounds:
        -- δ₁(e^h+1) ≤ εc(e^h-1)/16
        have h_d1eh : δ₁ * (Real.exp h_val + 1) ≤ ε * c * (Real.exp h_val - 1) / 16 := by
          calc δ₁ * (Real.exp h_val + 1)
              ≤ ε * c * (Real.exp h_val - 1) / (16 * (Real.exp h_val + 1)) * (Real.exp h_val + 1) := by
                nlinarith
            _ = ε * c * (Real.exp h_val - 1) / 16 := by
                field_simp
        -- ωUδ₂ ≤ εc²/16
        have h_wud : ωU * δ₂ ≤ ε * c ^ 2 / 16 := by
          have h1 : δ₂ ≤ ε * c ^ 2 / (16 * (ωU + 1)) := hδ₂_le1
          have h2 : ωU / (ωU + 1) ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          have h3 : ωU * δ₂ ≤ ωU * (ε * c ^ 2 / (16 * (ωU + 1))) := by nlinarith
          calc ωU * δ₂ ≤ ωU * (ε * c ^ 2 / (16 * (ωU + 1))) := h3
            _ ≤ (ωU + 1) * (ε * c ^ 2 / (16 * (ωU + 1))) := by nlinarith
            _ = ε * c ^ 2 / 16 := by field_simp
        -- ε(c-δ₂)/2 ≥ εc/4 (since δ₂ ≤ c/2)
        have h_ec2 : ε * (c - δ₂) / 2 ≥ ε * c / 4 := by nlinarith
        -- Expand (ωU/c + ε/2)(e^h-1)(c-δ₂) = ωU(c-δ₂)/c·(e^h-1) + ε/2·(c-δ₂)·(e^h-1)
        -- = [ωU - ωUδ₂/c + ε(c-δ₂)/2] · (e^h-1)
        -- RHS = ωU(e^h-1) + δ₁(e^h-1) + 2δ₁ = ωU(e^h-1) + δ₁(e^h+1)
        -- So need: [ε(c-δ₂)/2 - ωUδ₂/c](e^h-1) ≥ δ₁(e^h+1)
        -- From h_ec2 and h_wud: ε(c-δ₂)/2 - ωUδ₂/c ≥ εc/4 - εc/16 = 3εc/16
        -- So LHS ≥ 3εc/16 · (e^h-1) ≥ εc(e^h-1)/16 ≥ δ₁(e^h+1) from h_d1eh.
        -- Multiply by c to avoid divisions.
        -- Need c * [(ωU+δ₁)(e^h-1)+2δ₁] ≤ c * (ωU/c+ε/2)(e^h-1)(c-δ₂)
        -- = (ωU+εc/2)(e^h-1)(c-δ₂)
        suffices h_mul_c : c * ((ωU + δ₁) * (Real.exp h_val - 1) + 2 * δ₁) ≤
            (ωU + ε * c / 2) * (Real.exp h_val - 1) * (c - δ₂) by
          have h_rw : (ωU / c + ε / 2) * (Real.exp h_val - 1) * (c - δ₂) =
            (ωU + ε * c / 2) * (Real.exp h_val - 1) * (c - δ₂) / c := by field_simp
          rw [h_rw]
          rw [le_div_iff₀ hc_pos]
          linarith
        -- Expand: c*ωU*(e^h-1) + c*δ₁*(e^h+1) ≤ [ωU*c - ωU*δ₂ + εc²/2 - εcδ₂/2]*(e^h-1)
        -- Cancel c*ωU*(e^h-1), need: c*δ₁*(e^h+1) ≤ [-ωU*δ₂ + εc(c-δ₂)/2]*(e^h-1)
        have h_cd1 : c * δ₁ * (Real.exp h_val + 1) ≤ ε * c ^ 2 * (Real.exp h_val - 1) / 16 := by
          nlinarith [h_d1eh]
        have h_wud2 : ωU * δ₂ ≤ ε * c ^ 2 / 16 := h_wud
        have h_ec2' : ε * c * (c - δ₂) / 2 ≥ ε * c ^ 2 / 4 := by nlinarith [h_ec2]
        -- So [-ωUδ₂ + εc(c-δ₂)/2]*(e^h-1) ≥ [εc²/4 - εc²/16]*(e^h-1) = 3εc²/16*(e^h-1)
        -- And c*δ₁*(e^h+1) ≤ εc²(e^h-1)/16 ≤ 3εc²(e^h-1)/16
        nlinarith [sq_nonneg c, sq_nonneg δ₂, sq_nonneg (ωU * δ₂)]
  -- Final: Substitute X₀ = e^{-rh} * n^{1/2}
  have h_final : (OmegaAlpha alpha + ε / 2) * (Real.exp h_val - 1) * X₀ / Real.log n =
      (OmegaAlpha alpha + ε / 2) * (Real.exp h_val - 1) * Real.exp (-((r : ℝ) * h_val)) *
        (n : ℝ) ^ (1/2 : ℝ) / Real.log n := by
      simp only [X₀]; ring
  linarith [h_step_a, h_step_b, h_step_c]

/-! ### Main Buchstab difference estimate -/

/-- Core asymptotic estimate for the v-bound. -/
lemma buchstab_diff_v_estimate
    (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hU_strict : UAlpha alpha < 3)
    (hh : 0 < h_val) (ε : ℝ) (hε : 0 < ε) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        (sievePhi ⌊Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)⌋₊
          ⌈Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)⌉₊ : ℝ) -
        (sievePhi ⌊Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)⌋₊
          ⌈Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)⌉₊ : ℝ) ≤
        (OmegaAlpha alpha + ε) * (Real.exp h_val - 1) * Real.exp (-((r : ℝ) * h_val)) *
          (n : ℝ) ^ (1/2 : ℝ) / Real.log n := by
  -- Apply buchstab_subtraction with U = 3 to get K, X_min and:
  obtain ⟨K, hK_pos, X_min, hX_min⟩ := buchstab_subtraction 3 (by norm_num) (by norm_num);
  -- Choose N such that for all n ≥ N, the conditions for buchstab_subtraction are satisfied.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
    Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) ≥ X_min ∧
    Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) ≥ X_min ∧
    Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2) ≥ 2 ∧
    1 ≤ Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) / Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)) ∧
    Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) / Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)) ≤ 3 ∧
    1 ≤ Real.log (Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) / Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)) ∧
    Real.log (Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) / Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2)) ≤ 3 := by
      have := X_values_large alpha h_val hα1 hα2 hh X_min lambda hlambda
      obtain ⟨N₁, hN₁⟩ := this
      have := Y_large alpha h_val hα1 hα2 hh lambda hlambda
      obtain ⟨N₂, hN₂⟩ := this
      -- Use delta = 3 - UAlpha alpha > 0 (from hU_strict)
      have h_delta_pos : (0 : ℝ) < 3 - UAlpha alpha := by linarith
      have := log_ratio_near_UAlpha alpha h_val hα1 hα2 hh (3 - UAlpha alpha) h_delta_pos lambda hlambda
      obtain ⟨N₃, hN₃⟩ := this
      use max (max N₁ N₂) N₃
      intro n hn r hr₁ hr₂
      have hU_ge_2 : UAlpha alpha ≥ 2 := le_of_lt (UAlpha_range alpha hα1 hα2 |>.1)
      have hN1' := hN₁ n (le_of_max_le_left (le_of_max_le_left hn)) r hr₁ hr₂
      have hN2' := hN₂ n (le_of_max_le_right (le_of_max_le_left hn)) r hr₁ hr₂
      obtain ⟨hN3a, hN3b⟩ := hN₃ n (le_of_max_le_right hn) r hr₁ hr₂
      rw [abs_sub_lt_iff] at hN3a hN3b
      exact ⟨ hN1'.1, hN1'.2, hN2', by linarith, by linarith, by linarith, by linarith ⟩
  obtain ⟨N₁, hN₁⟩ := buchstab_main_term_bound alpha h_val hα1 hα2 hh (ε / 2) (half_pos hε) lambda hlambda;
  obtain ⟨N₂, hN₂⟩ := error_log_bridge h_val K hh hK_pos lambda hlambda;
  obtain ⟨N₃, hN₃⟩ := buchstab_error_small alpha h_val hα1 hα2 hh (16 * K) (by linarith) (ε / 2) (by linarith) lambda hlambda;
  use Max.max N ( Max.max N₁ ( Max.max N₂ N₃ ) ) ; intros n hn r hr₁ hr₂; specialize hN n ( le_trans ( le_max_left _ _ ) hn ) r hr₁ hr₂; specialize hN₁ n ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hn ) r hr₁ hr₂; specialize hN₂ n ( le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_left _ _ ) ) ) hn ) r hr₁ hr₂; specialize hN₃ n ( le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_right _ _ ) ) ) hn ) r hr₁ hr₂;
  refine le_trans ( hX_min _ _ _ hN.1 hN.2.1 hN.2.2.1 hN.2.2.2.1 hN.2.2.2.2.1 hN.2.2.2.2.2.1 hN.2.2.2.2.2.2 ?_ ) ?_;
  · exact mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr ( by linarith ) ) ( by positivity );
  · grind

end

end BuchstabDiff

section SmoothTailBound

/-! Rankin bound for smooth tails: log(n) · Σ_{d > n^η, smooth} 1/d → 0. -/

open Finset BigOperators Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Rankin's trick -/

/-- Rankin's trick: for δ > 0 and T > 0, if we sum 1/d over d > T in a finset S of
    positive naturals, the sum is at most T^{-δ} · ∑_{d ∈ S} d^{δ-1}. -/
lemma rankin_trick_sum (S : Finset ℕ) (_hS : ∀ d ∈ S, 0 < d)
    (T : ℝ) (hT : 0 < T) (δ : ℝ) (hδ : 0 < δ) :
    (∑ d ∈ S.filter (fun d => (d : ℝ) > T), ((d : ℝ))⁻¹) ≤
    T ^ (-δ) * (∑ d ∈ S, ((d : ℝ)) ^ (δ - 1)) := by
  rw [ Finset.mul_sum _ _ _ ];
  refine' le_trans ( Finset.sum_le_sum _ ) _;
  use fun x => T ^ ( -δ ) * x ^ ( δ - 1 );
  · intro x hx; rw [ Real.rpow_neg hT.le ] ; rw [ inv_eq_one_div, div_le_iff₀ ] <;> norm_num at *;
    · rw [ inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ ( by positivity ) ];
      rw [ ← Real.rpow_add_one ] <;> norm_num <;> nlinarith [ Real.rpow_le_rpow hT.le hx.2.le hδ.le ];
    · linarith;
  · norm_num [ Finset.sum_filter ];
    exact Finset.sum_le_sum fun x hx => by split_ifs <;> first | positivity | exact le_rfl;

/-! ### Power sum bound for smooth numbers (Euler product inequality) -/

/-- The inductive step for the Euler product bound. -/
lemma smooth_sum_insert_le (q : ℕ) (hq : Nat.Prime q)
    (S : Finset ℕ) (hqS : q ∉ S) (_hS : ∀ p ∈ S, Nat.Prime p)
    (δ : ℝ) (_hδ : 0 < δ) (hδ1 : δ < 1)
    (P : ℝ) (hP : 0 ≤ P)
    (M : ℕ)
    (hIH : (∑ d ∈ (Finset.Icc 1 M).filter (fun d => ∀ p ∈ Nat.primeFactors d, p ∈ S),
        ((d : ℝ)) ^ (δ - 1)) ≤ P) :
    (∑ d ∈ (Finset.Icc 1 M).filter (fun d => ∀ p ∈ Nat.primeFactors d, p ∈ insert q S),
      ((d : ℝ)) ^ (δ - 1)) ≤ (1 - ((q : ℝ)) ^ (δ - 1))⁻¹ * P := by
  -- We partition (insert q S)-smooth d's in [1,M] by their q-adic valuation a = d.factorization q.
  have h_partition : (∑ d ∈ Finset.filter (fun d => ∀ p ∈ Nat.primeFactors d, p ∈ insert q S) (Finset.Icc 1 M), (d : ℝ) ^ (δ - 1)) ≤ (∑ a ∈ Finset.range (Nat.log q M + 1), (∑ d ∈ Finset.filter (fun d => ∀ p ∈ Nat.primeFactors d, p ∈ S) (Finset.Icc 1 (M / q ^ a)), (q ^ a * d : ℝ) ^ (δ - 1))) := by
    have h_partition : Finset.filter (fun d => ∀ p ∈ Nat.primeFactors d, p ∈ insert q S) (Finset.Icc 1 M) ⊆ Finset.biUnion (Finset.range (Nat.log q M + 1)) (fun a => Finset.image (fun d => q ^ a * d) (Finset.filter (fun d => ∀ p ∈ Nat.primeFactors d, p ∈ S) (Finset.Icc 1 (M / q ^ a)))) := by
      intro d hd;
      simp +zetaDelta at *;
      refine' ⟨ Nat.factorization d q, _, d / q ^ Nat.factorization d q, _, _ ⟩;
      · exact Nat.le_log_of_pow_le hq.one_lt ( Nat.le_trans ( Nat.le_of_dvd hd.1.1 ( Nat.ordProj_dvd _ _ ) ) hd.1.2 );
      · refine' ⟨ ⟨ Nat.div_pos ( Nat.le_of_dvd hd.1.1 ( Nat.ordProj_dvd _ _ ) ) ( pow_pos hq.pos _ ), Nat.div_le_div_right hd.1.2 ⟩, _ ⟩;
        intro p pp dp _; specialize hd; have := hd.2 p pp ( dvd_trans dp ( Nat.div_dvd_of_dvd ( Nat.ordProj_dvd _ _ ) ) ) ( by linarith ) ; cases this <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
        exact dp <| hq.coprime_iff_not_dvd.mpr <| Nat.not_dvd_ordCompl ( by aesop ) <| by aesop;
      · rw [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ];
    refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_partition _ ) _;
    · exact fun _ _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _;
    · rw [ Finset.sum_biUnion ];
      · rw [ Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_image ] ; aesop;
        exact fun x hx y hy hxy => mul_left_cancel₀ ( pow_ne_zero _ hq.ne_zero ) hxy;
      · intros a ha b hb hab; simp_all +decide [ Finset.disjoint_left ] ;
        rintro _ x hx₁ hx₂ hx₃ rfl y hy₁ hy₂ hy₃; contrapose! hab;
        apply_fun fun n => n.factorization q at hab ; simp_all +decide [ Nat.factorization_mul, hq.ne_zero, ne_of_gt ( zero_lt_one.trans_le hx₁ ), ne_of_gt ( zero_lt_one.trans_le hy₁ ) ];
        rw [ Nat.factorization_eq_zero_of_not_dvd ( fun h => hqS <| hx₃ q hq h ), Nat.factorization_eq_zero_of_not_dvd ( fun h => hqS <| hy₃ q hq h ) ] at hab ; linarith;
  -- We bound each term in the sum by using the induction hypothesis.
  have h_bound : ∀ a ∈ Finset.range (Nat.log q M + 1), (∑ d ∈ Finset.filter (fun d => ∀ p ∈ Nat.primeFactors d, p ∈ S) (Finset.Icc 1 (M / q ^ a)), (q ^ a * d : ℝ) ^ (δ - 1)) ≤ (q ^ a : ℝ) ^ (δ - 1) * P := by
    intros a ha
    have h_bound : (∑ d ∈ Finset.filter (fun d => ∀ p ∈ Nat.primeFactors d, p ∈ S) (Finset.Icc 1 (M / q ^ a)), (d : ℝ) ^ (δ - 1)) ≤ P := by
      refine' le_trans _ hIH;
      exact Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, Nat.le_trans ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ( Nat.div_le_self _ _ ) ⟩, Finset.mem_filter.mp hx |>.2 ⟩ ) fun _ _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _;
    refine' le_trans _ ( mul_le_mul_of_nonneg_left h_bound <| by positivity );
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun x hx => by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ;
  -- We sum the geometric series ∑_{a=0}^{K} q^{a(δ-1)}.
  have h_geo_series : (∑ a ∈ Finset.range (Nat.log q M + 1), (q ^ a : ℝ) ^ (δ - 1)) ≤ (1 - (q : ℝ) ^ (δ - 1))⁻¹ := by
    have h_geo_series : (∑ a ∈ Finset.range (Nat.log q M + 1), (q ^ a : ℝ) ^ (δ - 1)) = (∑ a ∈ Finset.range (Nat.log q M + 1), ((q : ℝ) ^ (δ - 1)) ^ a) := by
      exact Finset.sum_congr rfl fun _ _ => by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), mul_comm, Real.rpow_mul ( Nat.cast_nonneg _ ), Real.rpow_natCast ] ;
    rw [ h_geo_series, ← tsum_geometric_of_lt_one ( by positivity ) ( by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr hq.one_lt ) ( show δ - 1 < 0 by linarith ) ) ];
    exact Summable.sum_le_tsum ( Finset.range ( Nat.log q M + 1 ) ) ( fun _ _ => by positivity ) ( summable_geometric_of_lt_one ( by positivity ) ( by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr hq.one_lt ) ( show δ - 1 < 0 by linarith ) ) );
  exact h_partition.trans ( le_trans ( Finset.sum_le_sum h_bound ) ( by simpa only [ Finset.sum_mul _ _ _ ] using mul_le_mul_of_nonneg_right h_geo_series hP ) )

/-- Euler product inequality for smooth numbers. -/
lemma smooth_power_sum_le_euler_product
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (M : ℕ) :
    (∑ d ∈ (Finset.Icc 1 M).filter (fun d => ∀ p ∈ Nat.primeFactors d, p ∈ S),
      ((d : ℝ)) ^ (δ - 1)) ≤
    ∏ p ∈ S, (1 - ((p : ℝ)) ^ (δ - 1))⁻¹ := by
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    have hsub : (Finset.Icc 1 M).filter (fun d => ∀ p ∈ Nat.primeFactors d, p ∈ (∅ : Finset ℕ)) ⊆ {1} := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      rw [Finset.mem_singleton]
      by_contra h
      have hp : d.minFac ∈ d.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd d, by omega⟩
      exact absurd (hd.2 d.minFac hp) (by simp)
    calc ∑ d ∈ _, _ ≤ ∑ d ∈ ({1} : Finset ℕ), ((d : ℝ)) ^ (δ - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 1 := by simp
  | insert q S' hqS' ih =>
    rw [Finset.prod_insert hqS']
    exact smooth_sum_insert_le q (hS q (Finset.mem_insert_self q S')) S' hqS'
      (fun p hp => hS p (Finset.mem_insert_of_mem hp)) δ hδ hδ1
      (∏ p ∈ S', (1 - ((p : ℝ)) ^ (δ - 1))⁻¹)
      (Finset.prod_nonneg fun p hp => by
        apply inv_nonneg.mpr; apply sub_nonneg.mpr
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast (hS p (Finset.mem_insert_of_mem hp)).one_le) (by linarith))
      M (ih (fun p hp => hS p (Finset.mem_insert_of_mem hp)))

/-! ### Euler product upper bound -/

lemma neg_log_one_sub_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 4) :
    -Real.log (1 - x) ≤ 4 * x := by
  nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ]

lemma euler_product_le_exp (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∏ p ∈ S, (1 - ((p : ℝ)) ^ (δ - 1))⁻¹ ≤
    Real.exp (4 * ∑ p ∈ S, ((p : ℝ)) ^ (δ - 1)) := by
  have h_ineq : ∀ p ∈ S, -Real.log (1 - (p : ℝ) ^ (δ - 1)) ≤ 4 * (p : ℝ) ^ (δ - 1) := by
    intros p hp
    have h_x_bounds : 0 ≤ (p : ℝ) ^ (δ - 1) ∧ (p : ℝ) ^ (δ - 1) ≤ 3 / 4 := by
      have h_bound : (p : ℝ) ^ (δ - 1) ≤ (2 : ℝ) ^ (-1 / 2 : ℝ) := by
        rw [ Real.rpow_def_of_pos, Real.rpow_def_of_pos ] <;> norm_num;
        · nlinarith [ show ( Real.log p : ℝ ) ≥ Real.log 2 by exact Real.log_le_log ( by norm_num ) ( mod_cast Nat.Prime.two_le ( hS p hp ) ), Real.log_pos one_lt_two ];
        · exact Nat.Prime.pos ( hS p hp );
      exact ⟨ by positivity, h_bound.trans <| by rw [ show ( 2 : ℝ ) ^ ( -1 / 2 : ℝ ) = ( Real.sqrt 2 ) ⁻¹ by rw [ Real.sqrt_eq_rpow, ← Real.rpow_neg ] <;> norm_num ] ; rw [ inv_le_comm₀ ] <;> norm_num [ Real.le_sqrt ] ⟩
    exact neg_log_one_sub_le _ h_x_bounds.1 h_x_bounds.2;
  convert Real.exp_le_exp.mpr ( Finset.sum_le_sum fun p hp => h_ineq p hp ) using 1;
  · rw [ Real.exp_sum, Finset.prod_congr rfl ] ; intros ; rw [ Real.exp_neg, Real.exp_log ] ; norm_num;
    exact lt_of_lt_of_le ( Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr ( hS _ ‹_› |> Nat.Prime.one_lt ) ) ( show δ - 1 < 0 by linarith ) ) ( by norm_num );
  · rw [ Finset.mul_sum _ _ _ ]

lemma prime_power_sum_le (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (Y₀ : ℝ) (hY₀ : 2 ≤ Y₀) (hS_bound : ∀ p ∈ S, (p : ℝ) ≤ Y₀)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (∑ p ∈ S, ((p : ℝ)) ^ (δ - 1)) ≤ Y₀ ^ δ / δ := by
  have h_sum_le_integral : ∀ M : ℕ, 1 < M → (∑ m ∈ Finset.Icc 2 M, ((m : ℝ)) ^ (δ - 1)) ≤ (M : ℝ) ^ δ / δ := by
    intros M hM
    have h_integral : ∀ m ∈ Finset.Icc 2 M, ((m : ℝ)) ^ (δ - 1) ≤ ∫ x in (m - 1 : ℝ)..m, x ^ (δ - 1) := by
      intros m hm
      have h_integral_bound : ∀ x ∈ Set.Icc (m - 1 : ℝ) m, x ^ (δ - 1) ≥ (m : ℝ) ^ (δ - 1) := by
        exact fun x hx => by rw [ ge_iff_le ] ; rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hx.1, hx.2, show ( m : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Icc.mp hm ] ] ;
      refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ h_integral_bound ) <;> norm_num;
      exact intervalIntegral.intervalIntegrable_rpow' ( by linarith );
    have h_sum_integral : ∑ m ∈ Finset.Icc 2 M, ∫ x in (m - 1 : ℝ)..m, x ^ (δ - 1) = ∫ x in (1 : ℝ)..M, x ^ (δ - 1) := by
      erw [ Finset.sum_Ico_eq_sum_range ];
      convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
      · ring;
      · rw [ Nat.cast_sub ] <;> push_cast <;> linarith;
      · exact fun k hk => intervalIntegral.intervalIntegrable_rpow' ( by linarith );
    refine le_trans ( Finset.sum_le_sum h_integral ) ?_;
    rw [ h_sum_integral, integral_rpow ] <;> norm_num [ hδ.ne' ];
    · bound;
    · exact Or.inl hδ;
  refine' le_trans _ ( le_trans ( h_sum_le_integral ( Nat.floor Y₀ ) ( Nat.le_floor <| by norm_num; linarith ) ) _ );
  · exact Finset.sum_le_sum_of_subset_of_nonneg ( fun p hp => Finset.mem_Icc.mpr ⟨ Nat.Prime.two_le ( hS p hp ), Nat.le_floor ( hS_bound p hp ) ⟩ ) fun _ _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _;
  · gcongr ; exact Nat.floor_le <| by positivity;

/-! ### Combined Rankin-Euler bound -/

lemma smooth_tail_combined_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (Y₀ : ℝ) (hY₀ : 2 ≤ Y₀) (hS_bound : ∀ p ∈ S, (p : ℝ) ≤ Y₀)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (T : ℝ) (hT : 0 < T) (M : ℕ) :
    (∑ d ∈ (Finset.Icc 1 M).filter (fun (d : ℕ) => (d : ℝ) > T ∧ ∀ p ∈ d.primeFactors, p ∈ S),
      ((d : ℝ))⁻¹) ≤
    T ^ (-δ) * Real.exp (4 * Y₀ ^ δ / δ) := by
  refine' le_trans _ ( mul_le_mul_of_nonneg_left ( euler_product_le_exp S hS δ hδ hδ1 |> le_trans <| Real.exp_le_exp.mpr ( show 4 * ∑ p ∈ S, ( p : ℝ ) ^ ( δ - 1 ) ≤ 4 * Y₀ ^ δ / δ from _ ) ) ( by positivity ) );
  · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( smooth_power_sum_le_euler_product S hS δ hδ ( by linarith ) M ) ( by positivity ) );
    convert rankin_trick_sum _ _ _ _ _ _ using 2;
    · refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +decide;
      · tauto;
      · exact fun b x hx₁ hx₂ hx₃ hx₄ hx₅ => ⟨ x, ⟨ ⟨ hx₁, hx₂ ⟩, hx₄ ▸ hx₅, hx₃ ⟩, hx₄ ⟩;
    · aesop;
    · lia;
    · grind;
  · convert mul_le_mul_of_nonneg_left ( prime_power_sum_le S hS Y₀ hY₀ hS_bound δ hδ ( by linarith ) ) zero_le_four using 1 ; ring

/-! ### Asymptotic dominance -/

/-- Polynomial · exp(K√(log n)) · n^{-c} → 0 for fixed c > 0. -/
lemma log_rpow_exp_sqrt_tendsto (c K : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ => Real.log n * (n : ℝ) ^ (-c) *
      Real.exp (K * (Real.log n) ^ (1/2 : ℝ))) Filter.atTop (nhds 0) := by
  -- Set $t := \log n$, so we can rewrite the limit in terms of $t$.
  suffices h_log : Filter.Tendsto (fun t : ℝ => t * Real.exp (-c * t) * Real.exp (K * Real.sqrt t)) Filter.atTop (nhds 0) by
    have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; rw [ Real.sqrt_eq_rpow ] ; ring_nf );
  -- For large $t$, the term $-ct/2$ dominates, so we can bound the expression.
  suffices h_bound : ∃ T : ℝ, ∀ t ≥ T, t * Real.exp (-c * t) * Real.exp (K * Real.sqrt t) ≤ t * Real.exp (-c * t / 2) by
    -- Since $t * \exp(-ct/2) \to 0$ as $t \to \infty$, we can use the squeeze theorem.
    have h_squeeze : Filter.Tendsto (fun t : ℝ => t * Real.exp (-c * t / 2)) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{ct}{2}$, so we can rewrite the limit in terms of $y$.
      suffices h_log : Filter.Tendsto (fun y : ℝ => (2 / c) * y * Real.exp (-y)) Filter.atTop (nhds 0) by
        convert h_log.comp ( Filter.tendsto_id.const_mul_atTop ( show 0 < c / 2 by positivity ) ) using 2 ; norm_num ; ring_nf;
        norm_num [ mul_assoc, mul_comm c, hc.ne' ];
      simpa [ mul_assoc ] using Filter.Tendsto.const_mul ( 2 / c ) ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
    refine' squeeze_zero_norm' _ h_squeeze;
    filter_upwards [ Filter.eventually_ge_atTop h_bound.choose, Filter.eventually_gt_atTop 0 ] with t ht₁ ht₂ using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_bound.choose_spec t ht₁;
  -- We can choose $T$ such that for all $t \geq T$, $K \sqrt{t} \leq \frac{c t}{2}$.
  obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ t ≥ T, K * Real.sqrt t ≤ c * t / 2 := by
    exact ⟨ ( 2 * |K| / c ) ^ 2 + 1, fun t ht => by cases abs_cases K <;> nlinarith [ show 0 ≤ c * t by nlinarith [ show 0 ≤ ( 2 * |K| / c ) ^ 2 by positivity ], Real.mul_self_sqrt ( show 0 ≤ t by nlinarith [ show 0 ≤ ( 2 * |K| / c ) ^ 2 by positivity ] ), mul_div_cancel₀ ( 2 * |K| ) hc.ne', sq_nonneg ( Real.sqrt t - ( 2 * |K| / c ) ), Real.sqrt_nonneg t, Real.mul_self_sqrt ( show 0 ≤ t by nlinarith [ show 0 ≤ ( 2 * |K| / c ) ^ 2 by positivity ] ) ] ⟩;
  exact ⟨ Max.max T 1, fun t ht => by rw [ mul_assoc, ← Real.exp_add ] ; exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by linarith [ hT t <| le_trans ( le_max_left _ _ ) ht ] ) <| by linarith [ le_max_right T 1 ] ⟩

/-! ### Main assembly: smooth_tail_bound -/

/-- Smooth tail: log(n) · Σ_{d > n^η, smooth} 1/d → 0. -/
lemma smooth_tail_bound_proof
    (h_val : ℝ) (hh : 0 < h_val) (lambda : ℝ) (hlambda : 0 < lambda)
    (η : ℝ) (hη : 0 < η) :
    ∀ C > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        Real.log n *
        (∑ d ∈ (Finset.Icc 1 (⌊(n : ℝ) ^ (1/2 : ℝ) * Real.exp ((r : ℝ) * h_val)⌋₊)).filter
          (fun d : ℕ => (d : ℝ) > (n : ℝ) ^ η ∧ ∀ p ∈ d.primeFactors,
            (p : ℝ) ≤ Real.exp (2 * (r : ℝ) * h_val)),
          ((d : ℕ) : ℝ)⁻¹) ≤ C := by
  -- Fix δ = min(1/4, min(η/2, 1/(4*h_val*lambda))).
  set δ := min (1 / 4) (min (η / 2) (1 / (4 * h_val * lambda))) with hδ_def
  have hδ_pos : 0 < δ := by
    positivity;
  -- Apply the smooth_tail_combined_bound lemma with the chosen δ.
  have h_smooth_tail : ∀ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
      (Real.log n) * (n ^ η : ℝ) ^ (-δ) * Real.exp (4 * (Real.exp (2 * r * h_val)) ^ δ / δ) ≤ C := by
        -- Apply the log_rpow_exp_sqrt_tendsto lemma with c = η * δ and K = 4 / δ.
        have h_log_rpow_exp_sqrt : Filter.Tendsto (fun n : ℕ => Real.log n * (n : ℝ) ^ (-η * δ) * Real.exp (4 * (Real.log n) ^ (1 / 2 : ℝ) / δ)) Filter.atTop (nhds 0) := by
          convert log_rpow_exp_sqrt_tendsto ( η * δ ) ( 4 / δ ) ( mul_pos hη hδ_pos ) using 2 ; ring_nf;
        -- Since $\exp(2rh) \leq (\log n)^{2h\lambda}$ for $r \leq \lfloor \lambda \log \log n \rfloor$, we have $(\exp(2rh))^δ \leq (\log n)^{2h\lambdaδ}$.
        have h_exp_bound : ∀ᶠ n in Filter.atTop, ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ → (Real.exp (2 * r * h_val)) ^ δ ≤ (Real.log n) ^ (1 / 2 : ℝ) := by
          have h_exp_bound : ∀ᶠ n in Filter.atTop, ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ → (Real.exp (2 * r * h_val)) ≤ (Real.log n) ^ (2 * h_val * lambda) := by
            filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with n hn hn' r hr₁ hr₂;
            rw [ Real.rpow_def_of_pos ( Real.log_pos hn ) ];
            exact Real.exp_le_exp.mpr ( by nlinarith [ show ( r : ℝ ) ≤ lambda * Real.log ( Real.log n ) by exact le_trans ( Nat.cast_le.mpr hr₂ ) ( Nat.floor_le ( mul_nonneg hlambda.le ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) ) ), mul_pos hh hlambda ] );
          filter_upwards [ h_exp_bound, Filter.eventually_gt_atTop 1 ] with n hn hn';
          intro r hr₁ hr₂; specialize hn r hr₁ hr₂; refine' le_trans ( Real.rpow_le_rpow ( by positivity ) hn ( by positivity ) ) _;
          rw [ ← Real.rpow_mul ( Real.log_nonneg hn'.le ) ];
          refine' Real.rpow_le_rpow_of_exponent_le ( Real.le_log_iff_exp_le ( by positivity ) |>.2 _ ) _;
          · contrapose! hn;
            exact lt_of_le_of_lt ( Real.rpow_le_one ( Real.log_nonneg hn'.le ) ( Real.log_le_iff_le_exp ( by positivity ) |>.2 hn.le ) ( by positivity ) ) ( by norm_num; positivity );
          · cases min_cases ( 1 / 4 ) ( min ( η / 2 ) ( 1 / ( 4 * h_val * lambda ) ) ) <;> cases min_cases ( η / 2 ) ( 1 / ( 4 * h_val * lambda ) ) <;> nlinarith [ mul_div_cancel₀ 1 ( by positivity : ( 4 * h_val * lambda ) ≠ 0 ) ];
        have h_exp_bound : ∀ᶠ n in Filter.atTop, ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ → Real.exp (4 * (Real.exp (2 * r * h_val)) ^ δ / δ) ≤ Real.exp (4 * (Real.log n) ^ (1 / 2 : ℝ) / δ) := by
          filter_upwards [ h_exp_bound ] with n hn r hr₁ hr₂ using Real.exp_le_exp.mpr ( by gcongr ; exact hn r hr₁ hr₂ );
        have h_combined_bound : ∀ᶠ n in Filter.atTop, ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
            (Real.log n) * (n ^ η : ℝ) ^ (-δ) * Real.exp (4 * (Real.exp (2 * r * h_val)) ^ δ / δ) ≤
            (Real.log n) * (n : ℝ) ^ (-η * δ) * Real.exp (4 * (Real.log n) ^ (1 / 2 : ℝ) / δ) := by
              filter_upwards [ h_exp_bound, Filter.eventually_gt_atTop 1 ] with n hn hn';
              intro r hr₁ hr₂; convert mul_le_mul_of_nonneg_left ( hn r hr₁ hr₂ ) ( show 0 ≤ Real.log n * ( n ^ η ) ^ ( -δ ) by exact mul_nonneg ( Real.log_nonneg hn'.le ) ( Real.rpow_nonneg ( by positivity ) _ ) ) using 1 ; rw [ ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
        intro C hC_pos
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (Real.log n) * (n : ℝ) ^ (-η * δ) * Real.exp (4 * (Real.log n) ^ (1 / 2 : ℝ) / δ) ≤ C := by
          simpa using h_log_rpow_exp_sqrt.eventually ( ge_mem_nhds hC_pos );
        obtain ⟨ M, hM ⟩ := Filter.eventually_atTop.mp h_combined_bound;
        exact ⟨ ⌈M⌉₊ + N, fun n hn r hr₁ hr₂ => le_trans ( hM n ( Nat.le_of_ceil_le ( by linarith ) ) r hr₁ hr₂ ) ( hN n ( by linarith ) ) ⟩;
  intro C hC_pos
  obtain ⟨N, hN⟩ := h_smooth_tail C hC_pos
  use max N 2
  intro n hn r hr1 hr2
  by_cases h_exp : Real.exp (2 * r * h_val) < 2;
  · rw [ Finset.sum_eq_zero ] <;> norm_num [ hC_pos.le ];
    intro x hx1 hx2 hx3 hx4; contrapose! hx3;
    -- Since $x$ is a product of primes less than or equal to $\exp(2rh)$, and $\exp(2rh) < 2$, it follows that $x$ must be 1.
    have hx_one : x = 1 := by
      exact Classical.not_not.1 fun hx5 => by obtain ⟨ p, hp₁, hp₂ ⟩ := Nat.exists_prime_and_dvd hx5; linarith [ hx4 p hp₁ hp₂ hx3, show ( p : ℝ ) ≥ 2 by exact_mod_cast hp₁.two_le ] ;
    norm_num [ hx_one ];
    exact Real.one_le_rpow ( by norm_cast; linarith [ le_max_right N 2 ] ) ( by positivity );
  · refine le_trans ?_ ( hN n ( le_trans ( le_max_left _ _ ) hn ) r hr1 hr2 );
    have := smooth_tail_combined_bound ( Finset.filter Nat.Prime ( Finset.range ( ⌊Real.exp ( 2 * r * h_val ) ⌋₊ + 1 ) ) ) ?_ ( Real.exp ( 2 * r * h_val ) ) ?_ ?_ δ hδ_pos ?_ ( n ^ η ) ?_ ⌊ ( n : ℝ ) ^ ( 1 / 2 : ℝ ) * Real.exp ( r * h_val ) ⌋₊;
    any_goals norm_num [ hδ_def ];
    · convert mul_le_mul_of_nonneg_left this ( Real.log_natCast_nonneg n ) using 1;
      · congr! 3;
        ext; simp ;
        exact fun _ => ⟨ fun h p hp hp' hp'' => ⟨ Nat.le_floor <| h p hp hp' hp'', hp ⟩, fun h p hp hp' hp'' => le_trans ( mod_cast h p hp hp' hp'' |>.1 ) <| Nat.floor_le <| by positivity ⟩;
      · grind;
    · linarith;
    · exact fun p hp hp' => le_trans ( Nat.cast_le.mpr hp ) ( Nat.floor_le ( by positivity ) );
    · exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ Nat.le_max_right N 2 ] ) ) _

end

end SmoothTailBound

section UBoundHelpers

/-! Smooth-rough decomposition: m = d·e with d smooth, P⁻(e) ≥ Z. -/

open Finset BigOperators Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### The reciprocal monoid homomorphism -/

/-- The function n ↦ 1/n as a multiplicative monoid homomorphism ℕ → ℝ. -/
def recipMonoidHom : ℕ →* ℝ where
  toFun n := ((n : ℕ) : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul]
    exact (mul_inv_rev _ _).trans (mul_comm _ _)


lemma recipMonoidHom_norm_lt_one {p : ℕ} (hp : Nat.Prime p) : ‖recipMonoidHom p‖ < 1 := by
  show ‖(p : ℝ)⁻¹‖ < 1
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact inv_lt_one_of_one_lt₀ this

/-! ### HFunc equals the Euler product over smooth numbers -/

/-- The Euler product ∏_{p < N, p prime} (1 - 1/p)⁻¹ equals the Mathlib primesBelow product
    using recipMonoidHom. -/
lemma HFunc_eq_primesBelow_prod (x : ℝ) :
    HFunc x = ∏ p ∈ (Nat.floor (Real.exp (2 * x)) + 1).primesBelow,
      (1 - recipMonoidHom p)⁻¹ := by
  unfold HFunc Nat.primesBelow recipMonoidHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  ext p
  simp

/-- Summability of 1/d over smooth numbers. -/
lemma summable_smooth_reciprocal (N : ℕ) :
    Summable (fun m : N.smoothNumbers => recipMonoidHom (m : ℕ)) :=
  (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (fun hp => recipMonoidHom_norm_lt_one hp) N).1.of_norm

/-- HasSum version: the sum of 1/d over smooth numbers has sum equal to the Euler product. -/
lemma hasSum_smooth_reciprocal (N : ℕ) :
    HasSum (fun m : N.smoothNumbers => recipMonoidHom (m : ℕ))
      (∏ p ∈ N.primesBelow, (1 - recipMonoidHom p)⁻¹) :=
  (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (fun hp => recipMonoidHom_norm_lt_one hp) N).2

/-- The sum of 1/d over all N-smooth positive integers d equals the Euler product. -/
lemma tsum_smooth_reciprocal_eq (N : ℕ) :
    ∑' (m : N.smoothNumbers), recipMonoidHom (m : ℕ) =
      ∏ p ∈ N.primesBelow, (1 - recipMonoidHom p)⁻¹ :=
  (hasSum_smooth_reciprocal N).tsum_eq

/-- The sum of 1/d over all (⌊e^{2x}⌋+1)-smooth positive integers d equals HFunc(x). -/
lemma tsum_smooth_reciprocal_eq_HFunc (x : ℝ) :
    ∑' (m : (Nat.floor (Real.exp (2 * x)) + 1).smoothNumbers),
      recipMonoidHom (m : ℕ) = HFunc x := by
  rw [HFunc_eq_primesBelow_prod, tsum_smooth_reciprocal_eq]

/-- Partial sums of 1/d over smooth numbers are bounded by HFunc. -/
lemma partial_sum_smooth_le_HFunc (x : ℝ) (S : Finset ℕ)
    (hS : ∀ d ∈ S, d ∈ (Nat.floor (Real.exp (2 * x)) + 1).smoothNumbers) :
    ∑ d ∈ S, (d : ℝ)⁻¹ ≤ HFunc x := by
  -- Since every $d \in S$ is smooth, we can apply the definition of $HFunc$.
  have h_sum_le : (∑ d ∈ S, (d : ℝ)⁻¹ : ℝ) ≤ ∑' (m : (Nat.floor (Real.exp (2 * x)) + 1).smoothNumbers), (m : ℝ)⁻¹ := by
    refine' le_trans _ ( Summable.sum_le_tsum _ _ _ );
    rotate_left;
    exact Finset.subtype (fun x_1 => x_1 ∈ (⌊rexp (2 * x)⌋₊ + 1).smoothNumbers) S;
    · exact fun _ _ => by positivity;
    · convert summable_smooth_reciprocal ( ⌊Real.exp ( 2 * x ) ⌋₊ + 1 ) using 1;
    · refine' le_of_eq _;
      refine' Finset.sum_bij ( fun d hd => ⟨ d, hS d hd ⟩ ) _ _ _ _ <;> aesop;
  exact le_trans h_sum_le (le_of_eq (tsum_smooth_reciprocal_eq_HFunc x))

/-! ### Smooth-rough decomposition counting bound -/

/-- The Y₀-smooth part of m: the largest divisor of m whose prime factors are all ≤ Y₀. -/
def smoothDivisorPart (m : ℕ) (Y₀ : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (· ≤ Y₀), p ^ m.factorization p

/-- The rough part of m: m divided by its Y₀-smooth part. -/
def roughPart (m : ℕ) (Y₀ : ℕ) : ℕ := m / smoothDivisorPart m Y₀

/-- The smooth part divides m. -/
lemma smoothDivisorPart_dvd (m : ℕ) (Y₀ : ℕ) : smoothDivisorPart m Y₀ ∣ m := by
  by_cases hm : m = 0;
  · aesop;
  · conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self hm ];
    apply_rules [ Finset.prod_dvd_prod_of_subset, Finset.filter_subset ]

/-- The smooth part is Y₀-smooth (all prime factors ≤ Y₀). -/
lemma smoothDivisorPart_smooth (m : ℕ) (Y₀ : ℕ) (hm : m ≠ 0) :
    ∀ p ∈ (smoothDivisorPart m Y₀).primeFactors, p ≤ Y₀ := by
  simp +contextual [ smoothDivisorPart ];
  intro p pp dp _; contrapose! dp; simp_all +decide [Nat.Prime.dvd_iff_not_coprime,
    Nat.coprime_prod_right_iff] ;
  exact fun q hq hq' hq'' => Nat.Coprime.pow_right _ <| pp.coprime_iff_not_dvd.mpr fun h => by have := Nat.le_of_dvd ( Nat.pos_of_ne_zero hq.ne_zero ) h; linarith;

/-- If m has no prime factor in (Y₀, Z), then the rough part has P⁻ ≥ Z. -/
lemma roughPart_min_prime (m : ℕ) (Y₀ Z : ℕ) (hm : m ≠ 0)
    (hno_gap : ∀ p ∈ m.primeFactors, p ≤ Y₀ ∨ Z ≤ p) :
    ∀ p ∈ (roughPart m Y₀).primeFactors, Z ≤ p := by
  intro p hp
  have h_div : p ∣ m := by
    exact Nat.dvd_trans ( Nat.dvd_of_mem_primeFactors hp ) ( Nat.div_dvd_of_dvd ( smoothDivisorPart_dvd m Y₀ ) );
  cases hno_gap p ( Nat.mem_primeFactors.mpr ⟨ Nat.prime_of_mem_primeFactors hp, h_div, hm ⟩ ) <;> simp_all +decide;
  contrapose! hp;
  intro pp dp; rw [ show roughPart m Y₀ = m / smoothDivisorPart m Y₀ from rfl ] at dp; simp_all +decide [ Nat.dvd_div_iff_mul_dvd ( smoothDivisorPart_dvd m Y₀ ) ] ;
  have h_contradiction : p ^ (Nat.factorization m p + 1) ∣ m := by
    refine' dvd_trans _ dp;
    rw [ smoothDivisorPart ];
    rw [ Finset.prod_eq_prod_diff_singleton_mul <| show p ∈ m.primeFactors.filter ( · ≤ Y₀ ) from ?_ ];
    · exact ⟨ ( ∏ x ∈ { x ∈ m.primeFactors | x ≤ Y₀ } \ { p }, x ^ m.factorization x ), by ring ⟩;
    · grind +qlia;
  exact absurd h_contradiction ( Nat.pow_succ_factorization_not_dvd hm pp )

/-- m = smoothDivisorPart m Y₀ * roughPart m Y₀. -/
lemma smooth_rough_product (m : ℕ) (Y₀ : ℕ) :
    m = smoothDivisorPart m Y₀ * roughPart m Y₀ := by
  exact Eq.symm ( Nat.mul_div_cancel' ( smoothDivisorPart_dvd m Y₀ ) )

/-! ### Main counting bound -/

/-- Interval smooth-rough decomposition: count ≤ Σ_d (Φ(M₁/d,Z) - Φ(M₀/d,Z)). -/
lemma no_prime_gap_interval_count_le_sievePhi_diff_sum
    (M₀ M₁ Y₀_nat Z_nat : ℕ) :
    ((Finset.Ioc M₀ M₁).filter (fun m : ℕ =>
      ∀ p ∈ m.primeFactors, p ≤ Y₀_nat ∨ Z_nat ≤ p)).card ≤
    ∑ d ∈ (Finset.Icc 1 M₁).filter (fun d => ∀ p ∈ d.primeFactors, p ≤ Y₀_nat),
      (sievePhi (M₁ / d) Z_nat - sievePhi (M₀ / d) Z_nat) := by
  -- Apply the lemma no_prime_gap_count_le_sievePhi_sum with Y₀_nat and Z_nat.
  have h_apply_lemma : (Finset.Ioc M₀ M₁).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ Y₀_nat ∨ Z_nat ≤ p) ⊆ Finset.biUnion (Finset.filter (fun d => ∀ p ∈ d.primeFactors, p ≤ Y₀_nat) (Finset.Icc 1 M₁)) (fun d => Finset.image (fun e => d * e) (Finset.Icc (M₀ / d + 1) (M₁ / d) |> Finset.filter (fun m => ∀ p ∈ m.primeFactors, Z_nat ≤ p))) := by
    intro m hm; simp_all +decide ;
    refine' ⟨ smoothDivisorPart m Y₀_nat, _, roughPart m Y₀_nat, _, _ ⟩;
    · refine' ⟨ ⟨ Nat.pos_of_dvd_of_pos ( smoothDivisorPart_dvd m Y₀_nat ) ( by linarith ), Nat.le_trans ( Nat.le_of_dvd ( by linarith ) ( smoothDivisorPart_dvd m Y₀_nat ) ) ( by linarith ) ⟩, _ ⟩;
      intro p pp dp _; have := smoothDivisorPart_smooth m Y₀_nat ( by linarith ) ; aesop;
    · refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
      · rw [ Nat.div_lt_iff_lt_mul <| Nat.pos_of_dvd_of_pos ( smoothDivisorPart_dvd m Y₀_nat ) <| pos_of_gt hm.1.1 ];
        rw [ mul_comm, ← smooth_rough_product ] ; linarith;
      · rw [ Nat.le_div_iff_mul_le ];
        · rw [ mul_comm, ← smooth_rough_product ] ; linarith;
        · exact Finset.prod_pos fun p hp => pow_pos ( Nat.pos_of_mem_primeFactors ( Finset.mem_filter.mp hp |>.1 ) ) _;
      · intro p pp dp _; have := roughPart_min_prime m Y₀_nat Z_nat ( by linarith ) ( fun p hp => by aesop ) p; aesop;
    · exact smooth_rough_product m Y₀_nat ▸ rfl;
  refine le_trans ( Finset.card_le_card h_apply_lemma ) ?_;
  refine' le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_sum fun x hx => Finset.card_image_le.trans _ );
  convert filter_interval_le_sievePhi_diff ( M₁ / x ) ( M₀ / x ) ( M₁ / x ) Z_nat _ _ using 1;
  · refine' Finset.card_bij ( fun m hm => m ) _ _ _ <;> norm_num;
    · intro a ha₁ ha₂ ha₃; refine' ⟨ ⟨ _, ha₂ ⟩, _, _, _ ⟩;
      · exact Nat.pos_of_ne_zero ( by aesop_cat );
      · rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod M₀ x, Nat.mod_lt M₀ ( show x > 0 from Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ];
      · rw [ le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_mul_le_self M₁ x, Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ];
      · exact fun p pp dp => ha₃ p pp dp ( by rintro rfl; norm_num at ha₁ );
    · intro b hb₁ hb₂ hb₃ hb₄ hb₅; rw [ div_lt_iff₀ ] at hb₃ <;> norm_cast at * ;
      · exact ⟨ ⟨ Nat.div_lt_of_lt_mul <| by linarith, hb₂ ⟩, fun p hp hp' hp'' => hb₅ p hp hp' ⟩;
      · linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ];
  · norm_num [ Nat.floor_div_natCast ];
  · positivity;
  · rw [ Nat.floor_div_natCast, Nat.floor_natCast ]

/-! ### Combining: u-sifted interval bound via Buchstab sum -/

/-! ### Sub-lemmas for the per-divisor Buchstab bound -/

/-- The ratio (1/2+a-c)/(α-1/2+b) ≈ U_α for small perturbations. -/
lemma ratio_perturbation_bound (alpha : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (delta : ℝ) (hdelta : 0 < delta) (η : ℝ) (hη_pos : 0 < η)
    (hη_small : η < delta * (alpha - 1/2) / 2) :
    ∃ ε > 0, ∀ a b c : ℝ, |a| < ε → |b| < ε → |c| ≤ η →
      |(1/2 + a - c) / (alpha - 1/2 + b) - UAlpha alpha| < delta ∧
      |(1/2 - a - c) / (alpha - 1/2 + b) - UAlpha alpha| < delta := by
  unfold UAlpha; norm_num;
  -- Choose ε = min(delta * (alpha - 1/2)^2 / 8, (alpha - 1/2) / 4).
  use min (delta * (alpha - 1 / 2) ^ 2 / 8) ((alpha - 1 / 2) / 4);
  refine' ⟨ _, _ ⟩;
  · exact lt_min ( div_pos ( mul_pos hdelta ( sq_pos_of_pos ( by linarith ) ) ) ( by norm_num ) ) ( div_pos ( by linarith ) ( by norm_num ) );
  · intro a b c ha hb hc;
    constructor <;> rw [ abs_lt ];
    · rw [ div_sub', lt_div_iff₀, div_lt_iff₀ ] <;> norm_num at *;
      · constructor <;> nlinarith [ abs_lt.mp ha.1, abs_lt.mp ha.2, abs_lt.mp hb.1, abs_lt.mp hb.2, abs_le.mp hc, mul_inv_cancel₀ ( by linarith : ( 2 * alpha - 1 ) ≠ 0 ), mul_pos hdelta ( by linarith : 0 < alpha - 1 / 2 ) ];
      · grind;
      · grind;
      · linarith [ abs_lt.mp ha.2, abs_lt.mp hb.2 ];
    · rw [ div_sub', lt_div_iff₀, div_lt_iff₀ ] <;> try nlinarith [ abs_lt.mp ha, abs_lt.mp hb, min_le_left ( delta * ( alpha - 1 / 2 ) ^ 2 / 8 ) ( ( alpha - 1 / 2 ) / 4 ), min_le_right ( delta * ( alpha - 1 / 2 ) ^ 2 / 8 ) ( ( alpha - 1 / 2 ) / 4 ) ];
      constructor <;> nlinarith [ abs_lt.mp ha, abs_lt.mp hb, abs_le.mp hc, min_le_left ( delta * ( alpha - 1 / 2 ) ^ 2 / 8 ) ( ( alpha - 1 / 2 ) / 4 ), min_le_right ( delta * ( alpha - 1 / 2 ) ^ 2 / 8 ) ( ( alpha - 1 / 2 ) / 4 ), mul_inv_cancel₀ ( by linarith : ( 2 * alpha - 1 ) ≠ 0 ) ]

/-- rh/log n → 0 for r ≤ λ log log n. -/
lemma rh_over_log_n_small (h_val : ℝ) (hh : 0 < h_val) (lambda : ℝ) (hlambda : 0 < lambda)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        (r : ℝ) * h_val / Real.log n < ε ∧
        ((r : ℝ) - 1) * h_val / Real.log n < ε := by
  have h_log_ratio : Filter.Tendsto (fun n : ℕ => (lambda * Real.log (Real.log n) * h_val) / Real.log n) Filter.atTop (nhds 0) := by
    -- We can factor out $h_val$ and use the fact that $\frac{\log \log n}{\log n} \to 0$ as $n \to \infty$.
    have h_log_log : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) Filter.atTop (nhds 0) := by
      -- Let $y = \log n$, therefore the expression becomes $\frac{\log y}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
      suffices h_log_z : Filter.Tendsto (fun z : ℝ => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    convert h_log_log.const_mul ( lambda * h_val ) using 2 <;> ring;
  have := h_log_ratio.eventually ( gt_mem_nhds hε );
  obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp this;
  refine' ⟨ N + 3, fun n hn r hr₁ hr₂ => ⟨ _, _ ⟩ ⟩ <;> refine' lt_of_le_of_lt _ ( hN n ( by linarith ) );
  · gcongr;
    exact le_trans ( Nat.cast_le.mpr hr₂ ) ( Nat.floor_le ( mul_nonneg hlambda.le ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) ) );
  · gcongr;
    exact le_trans ( sub_le_sub_right ( Nat.cast_le.mpr hr₂ ) _ ) ( by linarith [ Nat.floor_le ( show 0 ≤ lambda * Real.log ( Real.log n ) by exact mul_nonneg hlambda.le ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) ) ] )

/-- For smooth d and r ≤ λ log log n, the log ratio → U_α. -/
lemma log_ratio_u_near_UAlpha (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hh : 0 < h_val) (delta : ℝ) (hdelta : 0 < delta) (lambda : ℝ) (hlambda : 0 < lambda)
    (η : ℝ) (hη_pos : 0 < η) (hη_small : η < delta * (alpha - 1/2) / 2) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        ∀ d : ℕ, d ≥ 1 → (d : ℝ) ≤ (n : ℝ) ^ η →
          |Real.log (Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) / d) /
           Real.log (Real.exp (((r : ℝ) - 1) * h_val) * (n : ℝ) ^ (alpha - 1/2)) - UAlpha alpha| < delta ∧
          |Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) / d) /
           Real.log (Real.exp (((r : ℝ) - 1) * h_val) * (n : ℝ) ^ (alpha - 1/2)) - UAlpha alpha| < delta := by
  obtain ⟨ ε, hε_pos, hε ⟩ := ratio_perturbation_bound alpha hα1 hα2 delta hdelta η hη_pos hη_small;
  obtain ⟨ N₁, hN₁ ⟩ := rh_over_log_n_small h_val hh lambda hlambda ε hε_pos;
  refine' ⟨ N₁ + 4, fun n hn r hr₁ hr₂ d hd₁ hd₂ => _ ⟩ ; specialize hN₁ n ( by linarith ) r hr₁ hr₂;
  convert hε ( r * h_val / Real.log n ) ( ( r - 1 ) * h_val / Real.log n ) ( Real.log d / Real.log n ) _ _ _ using 1 <;> norm_num;
  · rw [ Real.log_div, Real.log_mul, Real.log_mul ] <;> norm_num <;> try positivity;
    · rw [ Real.log_rpow ( by norm_cast; linarith ), Real.log_rpow ( by norm_cast; linarith ) ] ; ring_nf;
      rw [ show ( r * h_val - h_val + Real.log n * ( -1 / 2 ) + Real.log n * alpha ) = ( Real.log n ) * ( -1 / 2 + ( r * h_val * ( Real.log n ) ⁻¹ - h_val * ( Real.log n ) ⁻¹ ) + alpha ) by nlinarith [ mul_inv_cancel_left₀ ( show Real.log n ≠ 0 by exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith ) ( r * h_val ), mul_inv_cancel_left₀ ( show Real.log n ≠ 0 by exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith ) h_val ] ] ; norm_num ; ring_nf;
      rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith ) ) ) ] ; ring_nf;
    · exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ );
    · linarith;
    · grind;
  · rw [ Real.log_div, Real.log_mul, Real.log_mul ] <;> norm_num <;> try positivity;
    · rw [ Real.log_rpow ( by norm_cast; linarith ), Real.log_rpow ( by norm_cast; linarith ) ] ; ring_nf;
      rw [ show ( r * h_val - h_val + Real.log n * ( -1 / 2 ) + Real.log n * alpha ) = ( Real.log n ) * ( -1 / 2 + ( r * h_val * ( Real.log n ) ⁻¹ - h_val * ( Real.log n ) ⁻¹ ) + alpha ) by nlinarith [ mul_inv_cancel_left₀ ( show Real.log n ≠ 0 by exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith ) ( r * h_val ), mul_inv_cancel_left₀ ( show Real.log n ≠ 0 by exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith ) h_val ] ] ; norm_num ; ring_nf;
      rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith ) ) ) ] ; ring_nf;
    · exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ );
    · linarith;
    · linarith;
  · rw [ abs_of_nonneg ( div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) hh.le ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ] ; linarith;
  · rw [ abs_of_nonneg ( div_nonneg ( mul_nonneg ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hr₁ ) ) hh.le ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ] ; linarith;
  · rw [ abs_of_nonneg ( div_nonneg ( Real.log_nonneg ( mod_cast hd₁ ) ) ( Real.log_nonneg ( mod_cast by linarith ) ) ) ];
    rw [ div_le_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ];
    simpa [ Real.log_rpow ( Nat.cast_pos.mpr <| pos_of_gt hn ) ] using Real.log_le_log ( by positivity ) hd₂

/-- For d ≤ n^{1/4}, the scaled endpoints M₁/d and M₀/d are large. -/
lemma X_div_d_large (h_val : ℝ) (hh : 0 < h_val)
    (M : ℝ) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        ∀ d : ℕ, d ≥ 1 → d ≤ ⌊(n : ℝ) ^ (1/4 : ℝ)⌋₊ →
          Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) / d ≥ M := by
  -- To bound the scaled endpoints, use the inequality $e^{-rh} n^{1/2}/d \geq e^{-rh} n^{1/2} / n^{1/4} = e^{-rh} n^{1/4}$.
  suffices h_bound : ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ → Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/4 : ℝ) ≥ M by
    obtain ⟨ N, hN ⟩ := h_bound; use N; intros n hn r hr₁ hr₂ d hd₁ hd₂; specialize hN n hn r hr₁ hr₂; rw [ show ( n : ℝ ) ^ ( 1 / 2 : ℝ ) = n ^ ( 1 / 4 : ℝ ) * n ^ ( 1 / 4 : ℝ ) by rw [ ← Real.rpow_add' ] <;> norm_num ] ; rw [ mul_div_assoc ] ;
    refine le_trans hN ?_;
    rw [ mul_div_assoc ];
    gcongr;
    exact le_mul_of_one_le_right ( by positivity ) ( by rw [ one_le_div ( by positivity ) ] ; exact Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hd₂ ) );
  -- Use the fact that $e^{-rh} \geq e^{-\lambda h \log \log n}$ and $n^{1/4} \geq (\log n)^{\lambda h}$ for sufficiently large $n$.
  have h_exp_bound : Filter.Tendsto (fun n : ℕ => Real.exp (-((lambda * Real.log (Real.log n) * h_val))) * (n : ℝ) ^ (1/4 : ℝ)) Filter.atTop Filter.atTop := by
    -- We can simplify the expression inside the exponential further by combining the exponents.
    suffices h_exp_neg_log_log' : Filter.Tendsto (fun n : ℕ => Real.exp (Real.log (n : ℝ) * (1/4 : ℝ) - lambda * Real.log (Real.log n) * h_val)) Filter.atTop Filter.atTop by
      refine h_exp_neg_log_log'.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; rw [ ← Real.exp_add ] ; ring_nf );
    -- We can factor out $\log n$ from the exponent.
    suffices h_factor : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) * (1/4 - lambda * h_val * Real.log (Real.log n) / Real.log n)) Filter.atTop Filter.atTop by
      refine Real.tendsto_exp_atTop.comp <| h_factor.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ mul_sub, mul_div_cancel₀ _ <| ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hn ] ; ring;
    -- We'll use the fact that $\frac{\log \log n}{\log n}$ tends to $0$ as $n$ tends to infinity.
    have h_log_log : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) Filter.atTop (nhds 0) := by
      -- Let $y = \log n$, therefore the expression becomes $\frac{\log y}{y}$.
      suffices h_log_y : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) by
        exact h_log_y.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      -- Let $z = \frac{1}{y}$, therefore the expression becomes $\frac{\log (1/z)}{1/z} = -z \log z$.
      suffices h_log_z : Filter.Tendsto (fun z : ℝ => -z * Real.log z) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_z.congr ( by simp +contextual [ div_eq_inv_mul ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    apply Filter.Tendsto.atTop_mul_pos;
    exacts [ show 0 < 1 / 4 by norm_num, Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop, by simpa [ mul_div_assoc ] using tendsto_const_nhds.sub ( h_log_log.const_mul ( lambda * h_val ) ) ];
  have := h_exp_bound.eventually_gt_atTop M;
  simp +zetaDelta at *;
  obtain ⟨ N, hN ⟩ := this; use N + 3; intros n hn r hr₁ hr₂; refine le_trans ( le_of_lt ( hN n ( by linarith ) ) ) ?_; gcongr;
  exact le_trans ( Nat.cast_le.mpr hr₂ ) ( Nat.floor_le ( mul_nonneg hlambda.le ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) ) )

/-- Z = e^{(r-1)h}·n^{α-1/2} ≥ 2 for large n. This follows from Y_large since Z ≥ Y. -/
lemma Z_large (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hh : 0 < h_val) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        Real.exp (((r : ℝ) - 1) * h_val) * (n : ℝ) ^ (alpha - 1/2) ≥ 2 := by
  -- By Y_large, we know that for large n, Y ≥ 2.
  have hY_large : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ → Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2) ≥ 2 := by
    exact Y_large alpha h_val hα1 hα2 hh lambda hlambda;
  exact ⟨ hY_large.choose, fun n hn r hr₁ hr₂ => le_trans ( hY_large.choose_spec n hn r hr₁ hr₂ ) ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr ( by nlinarith [ show ( r : ℝ ) ≥ 1 by norm_cast ] ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ⟩

/-- Per-d Buchstab main term ≤ (Ω_α + ε/2)(M₁-M₀)/(d·log n). -/
lemma buchstab_main_term_u
    (alpha : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (ε : ℝ) (_hε : 0 < ε)
    (n : ℕ) (hn : n ≥ 4) (d : ℕ) (hd : d ≥ 1)
    (x₁ x₀ M₁ M₀ Z : ℝ)
    (hx₁ : x₁ = M₁ / d) (hx₀ : x₀ = M₀ / d)
    (hM₁_pos : M₁ > 0) (hM₀_pos : M₀ > 0) (hM₁_ge_M₀ : M₁ ≥ M₀)
    (hlogZ_pos : Real.log Z > 0)
    (hlogZ_lower : Real.log Z ≥ (alpha - 1/2) * Real.log n)
    (δ_ω : ℝ) (hδ_nn : 0 ≤ δ_ω)
    (hω₁ : buchstabOmega (Real.log x₁ / Real.log Z) ≤
            buchstabOmega (UAlpha alpha) + δ_ω)
    (hω₀ : buchstabOmega (Real.log x₀ / Real.log Z) ≥
            buchstabOmega (UAlpha alpha) - δ_ω)
    (hδ_constraint : δ_ω * (M₁ + M₀) ≤ (ε / 2) * (alpha - 1/2) * (M₁ - M₀)) :
    buchstabOmega (Real.log x₁ / Real.log Z) * x₁ / Real.log Z -
    buchstabOmega (Real.log x₀ / Real.log Z) * x₀ / Real.log Z ≤
    (OmegaAlpha alpha + ε / 2) * (M₁ - M₀) / ((d : ℝ) * Real.log n) := by
  rw [ div_sub_div_same, div_le_div_iff₀ ] <;> try positivity;
  · -- Substitute the bounds from hω₁ and hω₀ into the left-hand side.
    have h_subst : (buchstabOmega (log x₁ / log Z) * x₁ - buchstabOmega (log x₀ / log Z) * x₀) * (d * log n) ≤ (buchstabOmega (UAlpha alpha) + δ_ω) * M₁ * log n - (buchstabOmega (UAlpha alpha) - δ_ω) * M₀ * log n := by
      convert mul_le_mul_of_nonneg_right ( sub_le_sub ( mul_le_mul_of_nonneg_right hω₁ <| show 0 ≤ M₁ / ( d : ℝ ) by positivity ) ( mul_le_mul_of_nonneg_right hω₀ <| show 0 ≤ M₀ / ( d : ℝ ) by positivity ) ) ( show 0 ≤ ( d : ℝ ) * log n by exact mul_nonneg ( Nat.cast_nonneg _ ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ) using 1 ; ring_nf;
      · grind;
      · field_simp;
    rw [ show OmegaAlpha alpha = buchstabOmega ( UAlpha alpha ) / ( alpha - 1 / 2 ) by rw [ eq_div_iff ] <;> linarith [ OmegaAlpha_div_eq alpha hα1 hα2 ] ];
    rw [ div_add', div_mul_eq_mul_div, div_mul_eq_mul_div ];
    · rw [ le_div_iff₀ ] <;> nlinarith [ mul_le_mul_of_nonneg_left hlogZ_lower <| show 0 ≤ buchstabOmega ( UAlpha alpha ) by exact le_of_lt <| buchstabOmega_pos _ <| by unfold UAlpha; rw [ le_div_iff₀ ] <;> linarith, mul_le_mul_of_nonneg_left hlogZ_lower <| show 0 ≤ δ_ω by positivity, Real.log_pos <| show ( n : ℝ ) > 1 by norm_cast; linarith ];
    · linarith;
  · exact mul_pos ( Nat.cast_pos.mpr hd ) ( Real.log_pos ( by norm_cast; linarith ) )

/-- Error bound for the u-Buchstab estimate. -/
lemma buchstab_error_u
    (h_val : ℝ) (hh : 0 < h_val) (ε K : ℝ) (hε : 0 < ε) (hK : K > 0)
    (n : ℕ) (hn : n ≥ 4) (r : ℕ) (hr : 1 ≤ r) (d : ℕ) (hd : d ≥ 1)
    (x₁ x₀ M₁ M₀ : ℝ)
    (hM₁ : M₁ = Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ))
    (hM₀ : M₀ = Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ))
    (hx₁ : x₁ = M₁ / d) (hx₀ : x₀ = M₀ / d)
    (hlog₁ : Real.log x₁ ≥ (1/5) * Real.log n)
    (hlog₀ : Real.log x₀ ≥ (1/5) * Real.log n)
    (herr : 50 * K / Real.log n ≤ (ε / 2) * (1 - Real.exp (-(2 * h_val)))) :
    K * x₁ / (Real.log x₁) ^ 2 + K * x₀ / (Real.log x₀) ^ 2 ≤
    (ε / 2) * (M₁ - M₀) / ((d : ℝ) * Real.log n) := by
  -- Apply the hypothesis `herr` and simplify the expression.
  have h_bound : 25 * K * (M₁ + M₀) / ((d : ℝ) * (Real.log n) ^ 2) ≤ (ε / 2) * (M₁ - M₀) / ((d : ℝ) * Real.log n) := by
    -- By simplifying, we can see that the inequality holds.
    have h_simplified : 25 * K * (Real.exp (r * h_val) + Real.exp (-r * h_val)) / (Real.log n ^ 2) ≤ (ε / 2) * (Real.exp (r * h_val) - Real.exp (-r * h_val)) / Real.log n := by
      have h_simplified : (Real.exp (r * h_val) + Real.exp (-r * h_val)) / (Real.exp (r * h_val) - Real.exp (-r * h_val)) ≤ 2 / (1 - Real.exp (-2 * h_val)) := by
        rw [ div_le_div_iff₀ ] <;> norm_num [ Real.exp_neg ] <;> ring_nf;
        · field_simp;
          rw [ show ( r : ℝ ) * h_val = h_val + ( r - 1 ) * h_val by ring, Real.exp_add ];
          norm_num [ Real.exp_mul ];
          nlinarith only [ show 1 ≤ Real.exp h_val ^ 2 by exact one_le_pow₀ ( Real.one_le_exp hh.le ), show 1 ≤ Real.exp ( r - 1 ) ^ h_val by exact Real.one_le_rpow ( Real.one_le_exp ( by linarith [ show ( r : ℝ ) ≥ 1 by norm_cast ] ) ) hh.le, mul_le_mul_of_nonneg_left ( show 1 ≤ Real.exp ( r - 1 ) ^ h_val by exact Real.one_le_rpow ( Real.one_le_exp ( by linarith [ show ( r : ℝ ) ≥ 1 by norm_cast ] ) ) hh.le ) ( sq_nonneg ( Real.exp h_val ) ) ];
        · rw [ ← Real.exp_neg ] ; norm_num ; positivity;
        · exact inv_lt_one_of_one_lt₀ ( by norm_num; positivity );
      rw [ div_le_iff₀ ] at *;
      · rw [ div_mul_eq_mul_div, le_div_iff₀ ] at *;
        · norm_num [ Real.exp_neg ] at *;
          nlinarith [ show 0 < ε * Real.log n ^ 2 by exact mul_pos hε ( sq_pos_of_pos ( Real.log_pos ( by norm_cast; linarith ) ) ), show 0 < ( Real.exp ( r * h_val ) + ( Real.exp ( r * h_val ) ) ⁻¹ ) * Real.log n by exact mul_pos ( by positivity ) ( Real.log_pos ( by norm_cast; linarith ) ) ];
        · exact sub_pos_of_lt ( by norm_num; positivity );
        · exact Real.log_pos <| by norm_cast; linarith;
      · exact Real.log_pos <| by norm_cast; linarith;
      · exact sub_pos_of_lt ( Real.exp_lt_exp.mpr ( by nlinarith [ show ( r : ℝ ) ≥ 1 by norm_cast ] ) );
      · exact sq_pos_of_pos <| Real.log_pos <| by norm_cast; linarith;
    convert mul_le_mul_of_nonneg_right h_simplified ( show ( 0 :ℝ ) ≤ ( n :ℝ ) ^ ( 1 / 2 :ℝ ) / d by positivity ) using 1 <;> push_cast [ * ] <;> ring_nf;
  refine le_trans ?_ h_bound;
  have h_bound : K * x₁ / (Real.log x₁) ^ 2 + K * x₀ / (Real.log x₀) ^ 2 ≤ K * x₁ / ((1 / 5 * Real.log n) ^ 2) + K * x₀ / ((1 / 5 * Real.log n) ^ 2) := by
    gcongr;
    · exact mul_nonneg hK.le ( hx₁.symm ▸ div_nonneg ( hM₁.symm ▸ by positivity ) ( Nat.cast_nonneg _ ) );
    · exact sq_pos_of_pos ( mul_pos ( by norm_num ) ( Real.log_pos ( by norm_cast; linarith ) ) );
    · exact mul_nonneg hK.le ( hx₀.symm ▸ div_nonneg ( hM₀.symm ▸ by positivity ) ( by positivity ) );
    · exact sq_pos_of_pos ( mul_pos ( by norm_num ) ( Real.log_pos ( by norm_cast; linarith ) ) );
  convert h_bound using 1 ; rw [ hx₁, hx₀ ] ; ring

/-- For d ≤ n^η with η ≤ 1/4, log(exp(±rh)·n^{1/2}/d) ≥ (1/5)·log n for large n. -/
lemma log_Md_lower (h_val : ℝ) (hh : 0 < h_val) (lambda : ℝ) (hlambda : 0 < lambda)
    (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1/4) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        ∀ d : ℕ, d ≥ 1 → (d : ℝ) ≤ (n : ℝ) ^ η →
          Real.log (Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) / d) ≥ (1/5) * Real.log n ∧
          Real.log (Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) / d) ≥ (1/5) * Real.log n := by
  -- Use rh_over_log_n_small to bound rh.
  obtain ⟨N_rh, hN_rh⟩ : ∃ N_rh : ℕ, ∀ n ≥ N_rh, ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ → (r : ℝ) * h_val / Real.log n < (1 / 20) / 2 ∧ ((r : ℝ) - 1) * h_val / Real.log n < (1 / 20) / 2 := by
    have := @rh_over_log_n_small h_val hh lambda hlambda ( 1 / 20 / 2 ) ( by norm_num ) ; aesop;
  refine' ⟨ N_rh + 4, fun n hn r hr₁ hr₂ d hd₁ hd₂ => ⟨ _, _ ⟩ ⟩ <;> rw [ Real.log_div, Real.log_mul, Real.log_exp, Real.log_rpow ] <;> norm_num <;> try positivity;
  any_goals linarith;
  · have := Real.log_le_log ( by positivity ) hd₂;
    rw [ Real.log_rpow ( by norm_cast; linarith ) ] at this ; nlinarith [ Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ];
  · have := hN_rh n ( by linarith ) r hr₁ hr₂;
    rw [ div_lt_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ] at this;
    have := Real.log_le_log ( by positivity ) hd₂;
    rw [ Real.log_rpow ( by norm_cast; linarith ) ] at this ; nlinarith [ Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ]

/-- tanh(h) ≤ tanh(rh) for h > 0, r ≥ 1. -/
lemma exp_tanh_monotone (h_val : ℝ) (hh : 0 < h_val) (r : ℕ) (hr : 1 ≤ r) :
    (Real.exp h_val - Real.exp (-h_val)) * (Real.exp ((r : ℝ) * h_val) + Real.exp (-((r : ℝ) * h_val))) ≤
    2 * (Real.exp h_val + Real.exp (-h_val)) * (Real.exp ((r : ℝ) * h_val) - Real.exp (-((r : ℝ) * h_val))) := by
  -- Set s = (r-1)*h_val. Substitute rh = h+s.
  set s := (r - 1) * h_val with hs
  have h1 : r * h_val = h_val + s := by
    linarith;
  rw [ h1 ] ; ring_nf ;
  norm_num [ ← Real.exp_add ] ; ring_nf;
  linarith [ Real.exp_le_exp.2 ( show -s ≤ s by nlinarith [ show ( r : ℝ ) ≥ 1 by norm_cast ] ), Real.exp_le_exp.2 ( show - ( h_val * 2 ) - s ≤ h_val * 2 + s by nlinarith [ show ( r : ℝ ) ≥ 1 by norm_cast ] ) ]

/-- δ_ω constraint ensuring the main term bound holds. -/
lemma delta_omega_constraint (h_val : ℝ) (hh : 0 < h_val) (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (n : ℕ) (_hn : n ≥ 4) (r : ℕ) (hr : 1 ≤ r)
    (δ_ω : ℝ) (_hδ_nn : 0 ≤ δ_ω)
    (hδ_bound : δ_ω ≤ ε * c * (Real.exp h_val - Real.exp (-h_val)) /
      (4 * (Real.exp h_val + Real.exp (-h_val)))) :
    δ_ω * (Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) +
           Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) ≤
    (ε / 2) * c * (Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) -
                   Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)) := by
  -- By multiplying both sides of the inequality from hδ_bound by the positive term exp(r*h_val)*n^(1/2) + exp(-r*h_val)*n^(1/2), we preserve the inequality.
  have h_mul : δ_ω * (Real.exp (r * h_val) * (n : ℝ) ^ (1 / 2 : ℝ) + Real.exp (-(r * h_val)) * (n : ℝ) ^ (1 / 2 : ℝ)) ≤ (ε * c * (Real.exp h_val - Real.exp (-h_val)) / (4 * (Real.exp h_val + Real.exp (-h_val)))) * (Real.exp (r * h_val) * (n : ℝ) ^ (1 / 2 : ℝ) + Real.exp (-(r * h_val)) * (n : ℝ) ^ (1 / 2 : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hδ_bound <| by positivity;
  refine le_trans h_mul ?_;
  field_simp;
  have := exp_tanh_monotone h_val hh r hr;
  grind +qlia

/-- The core u-sifted Buchstab estimate per divisor:
    for each Y₀-smooth d with d ≤ n^η and large n, the sievePhi difference is bounded by
    approximately (Ω_α + ε) · (M₁ - M₀) / (d · log n).
    Here η > 0 is fixed (small enough depending on ε and α) so that
    the log ratio stays close to U_α. -/
lemma buchstab_diff_u_per_d
    (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hU_strict : UAlpha alpha < 3)
    (hh : 0 < h_val) (ε : ℝ) (hε : 0 < ε) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ η > (0 : ℝ), η < 1/2 ∧ ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        ∀ d : ℕ, d ≥ 1 →
          (d : ℝ) ≤ (n : ℝ) ^ η →
          ((sievePhi (⌊Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) / d⌋₊)
              (⌈Real.exp (((r : ℝ) - 1) * h_val) * (n : ℝ) ^ (alpha - 1/2)⌉₊) : ℝ) -
           (sievePhi (⌊Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) / d⌋₊)
              (⌈Real.exp (((r : ℝ) - 1) * h_val) * (n : ℝ) ^ (alpha - 1/2)⌉₊) : ℝ)) ≤
          (OmegaAlpha alpha + ε) *
            (Real.exp ((r : ℝ) * h_val) - Real.exp (-((r : ℝ) * h_val))) *
            (n : ℝ) ^ (1/2 : ℝ) / ((d : ℝ) * Real.log n) := by
  -- Abbreviations
  set c := alpha - 1/2 with hc_def
  have hc_pos : c > 0 := by linarith
  have hU_range := UAlpha_range alpha hα1 hα2
  -- Step 0: Choose η and delta
  -- Get Lipschitz constant for ω on [1,4]
  obtain ⟨L_lip, hL_pos, hL_lip⟩ := buchstabOmega_lipschitz_on 1 4 (by norm_num) (by norm_num)
  -- Set tanh_h related quantities
  have heh_pos : Real.exp h_val > 0 := Real.exp_pos _
  have hemh_pos : Real.exp (-h_val) > 0 := Real.exp_pos _
  have heh_sum_pos : Real.exp h_val + Real.exp (-h_val) > 0 := by positivity
  have heh_diff_pos : Real.exp h_val - Real.exp (-h_val) > 0 := by
    have h1 : Real.exp h_val ≥ 1 + h_val := by linarith [Real.add_one_le_exp h_val]
    have h2 : Real.exp (-h_val) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  -- delta0 = ε*c*(e^h - e^{-h}) / (4*L*(e^h + e^{-h})), capped at 1
  set delta0 := min (min (ε * c * (Real.exp h_val - Real.exp (-h_val)) /
    (4 * L_lip * (Real.exp h_val + Real.exp (-h_val)))) 1) (3 - UAlpha alpha) with hdelta0_def
  have hdelta0_pos : delta0 > 0 := lt_min (lt_min (by positivity) (by norm_num)) (by linarith)
  have hdelta0_le_1 : delta0 ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hdelta0_le_gap : delta0 ≤ 3 - UAlpha alpha := min_le_right _ _
  -- η₀ = min(c/8, delta0*c/4)
  set η₀ := min (c / 8) (delta0 * c / 4) with hη₀_def
  have hη₀_pos : η₀ > 0 := lt_min (by positivity) (by positivity)
  have hη₀_le : η₀ ≤ 1/4 := le_trans (min_le_left _ _) (by nlinarith)
  have hη₀_small : η₀ < delta0 * c / 2 := by
    have : η₀ ≤ delta0 * c / 4 := min_le_right _ _
    nlinarith
  use η₀, hη₀_pos, by linarith [hη₀_le]
  -- Step 1: Get K, X_min from buchstab_subtraction
  obtain ⟨K, hK_pos, X_min, hBS⟩ := buchstab_subtraction 3 (by norm_num) (by norm_num)
  -- Step 2: Get N from log_ratio_u_near_UAlpha with delta = ε/4
  obtain ⟨N_ratio, hN_ratio⟩ := log_ratio_u_near_UAlpha alpha h_val hα1 hα2 hh
    delta0 hdelta0_pos lambda hlambda η₀ hη₀_pos hη₀_small
  -- Step 3: Get N from X_div_d_large
  obtain ⟨N_div, hN_div⟩ := X_div_d_large h_val hh X_min lambda hlambda
  -- Step 4: Get N from Z_large
  obtain ⟨N_Z, hN_Z⟩ := Z_large alpha h_val hα1 hα2 hh lambda hlambda
  -- Step 5: Get N from log_Md_lower
  obtain ⟨N_log, hN_log⟩ := log_Md_lower h_val hh lambda hlambda η₀ hη₀_pos hη₀_le
  -- Step 6: Get N for error bound: need 50K/(log n) ≤ (ε/2)*(1-exp(-2h))
  have h_err_limit : ∃ N_err : ℕ, ∀ n : ℕ, n ≥ N_err →
      50 * K / Real.log n ≤ (ε / 2) * (1 - Real.exp (-(2 * h_val))) := by
    have h_rhs_pos : (ε / 2) * (1 - Real.exp (-(2 * h_val))) > 0 := by
      apply mul_pos (by linarith)
      linarith [Real.exp_lt_one_iff.mpr (by linarith : -(2 * h_val) < 0)]
    have h_tend := (tendsto_const_nhds (x := 50 * K)).div_atTop
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact Filter.eventually_atTop.mp (h_tend.eventually (ge_mem_nhds h_rhs_pos))
  obtain ⟨N_err, hN_err⟩ := h_err_limit
  -- Assemble N
  refine ⟨max (max (max N_ratio N_div) (max N_Z N_log)) N_err + 4,
    fun n hn r hr₁ hr₂ d hd₁ hd₂ => ?_⟩
  -- Extract hypotheses
  have hn4 : n ≥ 4 := by omega
  have hn_ratio := hN_ratio n (by omega) r hr₁ hr₂ d hd₁ hd₂
  have hlogn_pos : Real.log n > 0 := Real.log_pos (by exact_mod_cast show (1 : ℕ) < n by omega)
  have hd_pos : (d : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  -- Key values
  set M₁ := Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) with hM₁_def
  set M₀ := Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) with hM₀_def
  set Z := Real.exp (((r : ℝ) - 1) * h_val) * (n : ℝ) ^ (alpha - 1/2) with hZ_def
  set x₁ := M₁ / d with hx₁_def
  set x₀ := M₀ / d with hx₀_def
  -- x₀ ≤ x₁
  have hx₀₁ : x₀ ≤ x₁ := by
    simp only [hx₁_def, hx₀_def, hM₁_def, hM₀_def]
    apply div_le_div_of_nonneg_right _ hd_pos.le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.exp_le_exp.mpr (by nlinarith [show (r : ℝ) ≥ 1 from Nat.one_le_cast.mpr hr₁])
  -- Z ≥ 2
  have hZ_ge_2 : Z ≥ 2 := hN_Z n (by omega) r hr₁ hr₂
  -- x₀ ≥ X_min (from X_div_d_large, noting d ≤ n^η ≤ n^{1/4})
  have hx₀_large : x₀ ≥ X_min := by
    have hd_le_n14 : d ≤ ⌊(n : ℝ) ^ (1/4 : ℝ)⌋₊ := by
      refine Nat.le_floor ?_
      exact le_trans hd₂ (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show n ≥ 1 by omega)) hη₀_le)
    exact hN_div n (by omega) r hr₁ hr₂ d hd₁ hd_le_n14
  have hx₁_large : x₁ ≥ X_min := le_trans hx₀_large hx₀₁
  -- Log ratios are in [1, 3]
  have hn_r1 := abs_lt.mp hn_ratio.1
  have hn_r2 := abs_lt.mp hn_ratio.2
  have h_log_ratio_x₁ : 1 ≤ Real.log x₁ / Real.log Z ∧
      Real.log x₁ / Real.log Z ≤ 3 := by
    constructor
    · linarith [hU_range.1, hdelta0_le_1]
    · linarith [hdelta0_le_gap]
  have h_log_ratio_x₀ : 1 ≤ Real.log x₀ / Real.log Z ∧
      Real.log x₀ / Real.log Z ≤ 3 := by
    constructor
    · linarith [hU_range.1, hdelta0_le_1]
    · linarith [hdelta0_le_gap]
  -- Apply buchstab_subtraction
  have hBS_applied := hBS x₀ x₁ Z hx₀_large hx₁_large hZ_ge_2
    h_log_ratio_x₀.1 h_log_ratio_x₀.2 h_log_ratio_x₁.1 h_log_ratio_x₁.2 hx₀₁
  -- Derive ω-level bounds using Lipschitz
  have hM₁_pos : M₁ > 0 := by rw [hM₁_def]; positivity
  have hM₀_pos : M₀ > 0 := by rw [hM₀_def]; positivity
  have hM₁_ge_M₀ : M₁ ≥ M₀ := by
    simp only [hM₁_def, hM₀_def]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.exp_le_exp.mpr (by nlinarith [show (r : ℝ) ≥ 1 from Nat.one_le_cast.mpr hr₁])
  have hlogZ_pos : Real.log Z > 0 := by
    have := hN_Z n (by omega) r hr₁ hr₂
    exact Real.log_pos (by linarith)
  -- log Z ≥ c * log n
  have hlogZ_lower : Real.log Z ≥ c * Real.log n := by
    rw [hZ_def, Real.log_mul (by positivity) (by positivity), Real.log_exp,
        Real.log_rpow (by positivity : (n : ℝ) > 0)]
    nlinarith [show (r : ℝ) ≥ 1 from Nat.one_le_cast.mpr hr₁,
              Real.log_nonneg (show (n : ℝ) ≥ 1 from by norm_cast; omega)]
  -- The log ratios u₁, u₀ are in [1, 4] (since UAlpha ∈ (2,3] and |u-UAlpha| < 1)
  have hu₁_in : 1 ≤ Real.log x₁ / Real.log Z ∧ Real.log x₁ / Real.log Z ≤ 4 := by
    constructor
    · nlinarith [abs_lt.mp hn_ratio.1, hU_range.1, hdelta0_le_1]
    · nlinarith [abs_lt.mp hn_ratio.1, hU_range.2, hdelta0_le_1]
  have hu₀_in : 1 ≤ Real.log x₀ / Real.log Z ∧ Real.log x₀ / Real.log Z ≤ 4 := by
    constructor
    · nlinarith [abs_lt.mp hn_ratio.2, hU_range.1, hdelta0_le_1]
    · nlinarith [abs_lt.mp hn_ratio.2, hU_range.2, hdelta0_le_1]
  have hUAlpha_in : (1 : ℝ) ≤ UAlpha alpha ∧ UAlpha alpha ≤ 4 := by
    exact ⟨by linarith [hU_range.1], by linarith [hU_range.2]⟩
  -- Lipschitz gives |ω(u) - ωU| ≤ L * |u - UAlpha|
  set δ_ω := L_lip * delta0 with hδω_def
  have hδ_nn : (0 : ℝ) ≤ δ_ω := by positivity
  have hω₁ : buchstabOmega (Real.log x₁ / Real.log Z) ≤
      buchstabOmega (UAlpha alpha) + δ_ω := by
    have hLip := hL_lip _ _ hu₁_in.1 hu₁_in.2 hUAlpha_in.1 hUAlpha_in.2
    have hratio := hn_ratio.1
    have habs_u := (abs_lt.mp (lt_of_lt_of_le hratio (le_refl _))).2
    have : |Real.log x₁ / Real.log Z - UAlpha alpha| ≤ delta0 := le_of_lt hratio
    have habs_omega : |buchstabOmega (Real.log x₁ / Real.log Z) - buchstabOmega (UAlpha alpha)| ≤ L_lip * delta0 := by
      calc |buchstabOmega (Real.log x₁ / Real.log Z) - buchstabOmega (UAlpha alpha)|
          ≤ L_lip * |Real.log x₁ / Real.log Z - UAlpha alpha| := hLip
        _ ≤ L_lip * delta0 := by
            apply mul_le_mul_of_nonneg_left (le_of_lt hratio) hL_pos.le
    linarith [abs_le.mp habs_omega]
  have hω₀ : buchstabOmega (Real.log x₀ / Real.log Z) ≥
      buchstabOmega (UAlpha alpha) - δ_ω := by
    have hLip := hL_lip _ _ hu₀_in.1 hu₀_in.2 hUAlpha_in.1 hUAlpha_in.2
    have hratio := hn_ratio.2
    have : |Real.log x₀ / Real.log Z - UAlpha alpha| ≤ delta0 := le_of_lt hratio
    have habs_omega : |buchstabOmega (Real.log x₀ / Real.log Z) - buchstabOmega (UAlpha alpha)| ≤ L_lip * delta0 := by
      calc |buchstabOmega (Real.log x₀ / Real.log Z) - buchstabOmega (UAlpha alpha)|
          ≤ L_lip * |Real.log x₀ / Real.log Z - UAlpha alpha| := hLip
        _ ≤ L_lip * delta0 := by
            apply mul_le_mul_of_nonneg_left (le_of_lt hratio) hL_pos.le
    linarith [abs_le.mp habs_omega]
  -- Verify the δ_ω constraint: δ_ω*(M₁+M₀) ≤ (ε/2)*c*(M₁-M₀)
  have hδ_constraint : δ_ω * (M₁ + M₀) ≤ (ε / 2) * c * (M₁ - M₀) := by
    -- First bound δ_ω
    have hδ_bound : δ_ω ≤ ε * c * (Real.exp h_val - Real.exp (-h_val)) /
        (4 * (Real.exp h_val + Real.exp (-h_val))) := by
      calc δ_ω = L_lip * delta0 := rfl
        _ ≤ L_lip * (ε * c * (Real.exp h_val - Real.exp (-h_val)) /
            (4 * L_lip * (Real.exp h_val + Real.exp (-h_val)))) := by
          apply mul_le_mul_of_nonneg_left (le_trans (min_le_left _ _) (min_le_left _ _)) hL_pos.le
        _ = ε * c * (Real.exp h_val - Real.exp (-h_val)) /
            (4 * (Real.exp h_val + Real.exp (-h_val))) := by
          field_simp
    -- Apply the constraint lemma
    exact delta_omega_constraint h_val hh ε c hε hc_pos n hn4 r hr₁ δ_ω hδ_nn hδ_bound
  -- Main term bound
  have h_main : buchstabOmega (Real.log x₁ / Real.log Z) * x₁ / Real.log Z -
      buchstabOmega (Real.log x₀ / Real.log Z) * x₀ / Real.log Z ≤
      (OmegaAlpha alpha + ε / 2) * (M₁ - M₀) / (d * Real.log n) := by
    exact buchstab_main_term_u alpha hα1 hα2 ε hε n hn4 d hd₁
      x₁ x₀ M₁ M₀ Z hx₁_def hx₀_def hM₁_pos hM₀_pos hM₁_ge_M₀
      hlogZ_pos hlogZ_lower δ_ω hδ_nn hω₁ hω₀ hδ_constraint
  -- Error bound
  have h_log_bounds := hN_log n (by omega) r hr₁ hr₂ d hd₁ hd₂
  have h_error : K * x₁ / (Real.log x₁) ^ 2 + K * x₀ / (Real.log x₀) ^ 2 ≤
      (ε / 2) * (M₁ - M₀) / (d * Real.log n) := by
    exact buchstab_error_u h_val hh ε K hε hK_pos n hn4 r hr₁ d hd₁
      x₁ x₀ M₁ M₀ hM₁_def hM₀_def hx₁_def hx₀_def
      h_log_bounds.1 h_log_bounds.2 (hN_err n (by omega))
  -- Combine
  have h_rhs_eq : (OmegaAlpha alpha + ε) * (Real.exp ((r : ℝ) * h_val) -
      Real.exp (-((r : ℝ) * h_val))) * (n : ℝ) ^ (1/2 : ℝ) / ((d : ℝ) * Real.log n) =
      (OmegaAlpha alpha + ε) * (M₁ - M₀) / (d * Real.log n) := by
    simp only [hM₁_def, hM₀_def]; ring
  rw [h_rhs_eq]
  calc (sievePhi ⌊x₁⌋₊ ⌈Z⌉₊ : ℝ) - (sievePhi ⌊x₀⌋₊ ⌈Z⌉₊ : ℝ)
      ≤ buchstabOmega (Real.log x₁ / Real.log Z) * x₁ / Real.log Z -
        buchstabOmega (Real.log x₀ / Real.log Z) * x₀ / Real.log Z +
        K * x₁ / (Real.log x₁) ^ 2 + K * x₀ / (Real.log x₀) ^ 2 := hBS_applied
    _ ≤ (OmegaAlpha alpha + ε / 2) * (M₁ - M₀) / (d * Real.log n) +
        (ε / 2) * (M₁ - M₀) / (d * Real.log n) := by linarith [h_main, h_error]
    _ = (OmegaAlpha alpha + ε) * (M₁ - M₀) / (d * Real.log n) := by ring

/-- Tail bound (strengthened): (log n) · ∑_{d > n^η, Y₀-smooth} 1/d → 0.
    For Y₀ = e^{2rh} ≤ (log n)^{2hλ} and d > n^η, the Rankin bound gives
    ∑_{d > n^η, Y₀-smooth} 1/d = o((log n)^{-1}). -/
lemma smooth_tail_bound
    (h_val : ℝ) (hh : 0 < h_val) (lambda : ℝ) (hlambda : 0 < lambda)
    (η : ℝ) (hη : 0 < η) :
    ∀ C > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        Real.log n *
        (∑ d ∈ (Finset.Icc 1 (⌊(n : ℝ) ^ (1/2 : ℝ) * Real.exp ((r : ℝ) * h_val)⌋₊)).filter
          (fun d : ℕ => (d : ℝ) > (n : ℝ) ^ η ∧ ∀ p ∈ d.primeFactors,
            (p : ℝ) ≤ Real.exp (2 * (r : ℝ) * h_val)),
          ((d : ℕ) : ℝ)⁻¹) ≤ C := by
  exact smooth_tail_bound_proof h_val hh lambda hlambda η hη

/-- HFunc is always ≥ 1 (since it is a product of factors ≥ 1). -/
lemma HFunc_ge_one (x : ℝ) : 1 ≤ HFunc x := by
  exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by norm_num ) fun p hp => inv_anti₀ ( sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) <| sub_le_self _ <| by positivity )

end

end UBoundHelpers

section UBoundProof

/-
Helpers for the proof of sifted_interval_u_bound.
-/

open Finset BigOperators Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Helper: exp(rh)·n^{1/2} ≤ n for large n -/

lemma exp_rh_sqrt_le_n (h_val : ℝ) (hh : 0 < h_val) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        ⌊Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ)⌋₊ ≤ n := by
          -- To find such an N, we solve the inequality $r * h_val \leq \frac{1}{2} \log n$ for $n$.
          have h_ineq : ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ → r * h_val ≤ (1 / 2) * Real.log n := by
            -- For large enough $n$, $\log \log n \leq \frac{1}{4 \lambda h_val} \log n$.
            have h_log_log_bound : ∃ N : ℕ, ∀ n ≥ N, Real.log (Real.log n) ≤ (1 / (4 * lambda * h_val)) * Real.log n := by
              have h_log_log_bound : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) Filter.atTop (nhds 0) := by
                have h_log_log_growth : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
                  -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
                  suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                    exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
                  norm_num;
                  exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
                exact h_log_log_growth.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
              exact Filter.eventually_atTop.mp ( h_log_log_bound.eventually ( gt_mem_nhds <| show 0 < 1 / ( 4 *lambda * h_val ) by positivity ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N + 2, fun n hn ↦ by have := hN n ( by linarith ) ; rw [ div_lt_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ] at this; linarith ⟩;
            obtain ⟨ N, hN ⟩ := h_log_log_bound;
            refine' ⟨ N + 3, fun n hn r hr₁ hr₂ => _ ⟩ ; specialize hN n ( by linarith ) ; rw [ div_mul_eq_mul_div ] at hN ; rw [ le_div_iff₀ <| by positivity ] at hN ; nlinarith [ show ( r :ℝ ) ≤ lambda * Real.log ( Real.log n ) from Nat.floor_le ( mul_nonneg hlambda.le <| Real.log_nonneg <| show ( Real.log n :ℝ ) ≥ 1 by rw [ ge_iff_le ] ; rw [ Real.le_log_iff_exp_le <| by norm_cast; linarith ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n :ℝ ) ≥ 3 by norm_cast; linarith ] ) |> le_trans ( Nat.cast_le.mpr hr₂ ), Real.log_nonneg <| show ( n :ℝ ) ≥ 1 by norm_cast; linarith ] ;
          obtain ⟨ N, hN ⟩ := h_ineq; use N + 1; intros n hn r hr₁ hr₂; refine Nat.le_of_lt_succ <| ?_; rw [ Nat.floor_lt' <| by positivity ] ; norm_num;
          rw [ ← Real.log_lt_log_iff ( by exact mul_pos ( Real.exp_pos _ ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ) ( by positivity ), Real.log_mul ( by positivity ) ( by exact ne_of_gt <| Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ), Real.log_exp, Real.log_rpow ( Nat.cast_pos.mpr <| by linarith ) ];
          have := hN n ( by linarith ) r hr₁ hr₂;
          -- Using the inequality $\log(1 + x) \geq \frac{x}{1 + x}$ for $x > 0$, we can show that $\log(n + 1) > \log n + \frac{1}{n + 1}$.
          have h_log_ineq : ∀ n : ℕ, 1 ≤ n → Real.log (n + 1) > Real.log n + 1 / (n + 1) := by
            intro n hn; rw [ gt_iff_lt ] ; rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; rw [ Real.exp_add, Real.exp_log ( by positivity ) ] ;
            nlinarith [ Real.exp_pos ( 1 / ( n + 1 : ℝ ) ), Real.exp_neg ( 1 / ( n + 1 : ℝ ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 1 / ( n + 1 : ℝ ) ) ) ), Real.add_one_lt_exp ( show ( 1 : ℝ ) / ( n + 1 ) ≠ 0 by positivity ), Real.add_one_lt_exp ( show ( - ( 1 / ( n + 1 : ℝ ) ) ) ≠ 0 by exact neg_ne_zero.mpr ( by positivity ) ), one_div_mul_cancel ( by positivity : ( n : ℝ ) + 1 ≠ 0 ) ];
          have := h_log_ineq n ( by linarith ) ; norm_num at * ; nlinarith [ inv_mul_cancel₀ ( by linarith : ( n : ℝ ) + 1 ≠ 0 ), Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ] ;

/-! ### Helper: n^η error is small -/

lemma n_eta_error_small (h_val : ℝ) (_hh : 0 < h_val) (eta : ℝ) (_heta : 0 < eta) (heta2 : eta < 1/2)
    (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (n : ℝ) ^ eta ≤ C * (n : ℝ) ^ (1/2 : ℝ) / Real.log n := by
        -- Divide both sides by $n^{1/2}$ to get $n^{\eta - 1/2} \log n \leq C$.
        suffices h_div : ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ (eta - 1 / 2) * Real.log n ≤ C by
          obtain ⟨ N, hN ⟩ := h_div; use N+2; intros n hn; rw [ le_div_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ] ; convert mul_le_mul_of_nonneg_right ( hN n <| by linarith ) ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( 1 / 2 : ℝ ) ) using 1 ; rw [ Real.rpow_sub <| Nat.cast_pos.mpr <| by linarith ] ; ring_nf;
          rw [ mul_assoc, mul_inv_cancel₀ ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ), mul_one ];
        -- We'll use the fact that $n^{\eta - 1/2} \log n \to 0$ as $n \to \infty$.
        have h_lim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (eta - 1 / 2) * Real.log n) Filter.atTop (nhds 0) := by
          -- Let $y = \log n$, therefore the expression becomes $y \cdot e^{(\eta - 1/2) y}$.
          suffices h_log : Filter.Tendsto (fun y : ℝ => y * Real.exp ((eta - 1 / 2) * y)) Filter.atTop (nhds 0) by
            have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
            refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
          -- Let $z = (\frac{1}{2} - \eta) y$, therefore the expression becomes $\frac{z}{\frac{1}{2} - \eta} e^{-z}$.
          suffices h_z : Filter.Tendsto (fun z : ℝ => z * Real.exp (-z) / (1 / 2 - eta)) Filter.atTop (nhds 0) by
            convert h_z.comp ( Filter.tendsto_id.const_mul_atTop ( show 0 < ( 1 / 2 - eta ) by linarith ) ) using 2 ; norm_num ; ring_nf;
            grind;
          simpa using Filter.Tendsto.div_const ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 ) _;
        simpa using h_lim.eventually ( ge_mem_nhds hC )

/-! ### Helper: the u-sifted count ≤ decomposition sum -/

/-- Bridge between real-valued sifted interval bound and ℕ decomposition. -/
lemma sifted_u_count_le_decomp (n : ℕ) (alpha h_val : ℝ) (r : ℕ)
    (_hh : 0 < h_val) (_hr : 1 ≤ r) (hn : 4 ≤ n)
    (_hn_le : ⌊Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ)⌋₊ ≤ n) :
    ((Finset.Icc 1 n).filter (fun m : ℕ =>
      Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) < (m : ℝ) ∧
      (m : ℝ) ≤ Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) ∧
      ∀ p : ℕ, Nat.Prime p → p ∣ m →
        ¬((p : ℝ) > Real.exp (2 * (r : ℝ) * h_val) ∧
          (p : ℝ) < Real.exp (((r : ℝ) - 1) * h_val) * (n : ℝ) ^ (alpha - 1/2)))).card ≤
    ∑ d ∈ (Finset.Icc 1 (⌊Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ)⌋₊)).filter
        (fun d => ∀ p ∈ d.primeFactors, p ≤ ⌊Real.exp (2 * (r : ℝ) * h_val)⌋₊),
      (sievePhi (⌊Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ)⌋₊ / d)
        (⌈Real.exp (((r : ℝ) - 1) * h_val) * (n : ℝ) ^ (alpha - 1/2)⌉₊) -
       sievePhi (⌊Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ)⌋₊ / d)
        (⌈Real.exp (((r : ℝ) - 1) * h_val) * (n : ℝ) ^ (alpha - 1/2)⌉₊)) := by
  -- The filter set is a subset of Ioc M₀_nat M₁_nat with the gap condition
  -- (using floor/ceil to translate real bounds to nat),
  -- then apply no_prime_gap_interval_count_le_sievePhi_diff_sum.
  refine' le_trans ( Finset.card_le_card _ ) ( no_prime_gap_interval_count_le_sievePhi_diff_sum _ _ _ _ );
  intro m hm; simp_all +decide ;
  refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
  · exact Nat.succ_le_of_lt ( Nat.floor_lt ( by positivity ) |>.2 hm.2.1 );
  · exact Nat.le_floor hm.2.2.1;
  · exact fun p pp dp _ => Classical.or_iff_not_imp_left.2 fun h => hm.2.2.2 p pp dp <| lt_of_not_ge fun h' => h <| Nat.le_floor <| by linarith;

end

end UBoundProof

section Combinatorics

/-! Admissible factorization and K₂,₂-free from Sidon. -/

open Finset BigOperators Real

noncomputable section

/-! ### Parametrized factorization -/

/-
If m ≤ n^α or m is prime, then (m, 1) is admissible. -/
lemma admissible_trivial (n : ℕ) (m : ℕ) (hm1 : 1 ≤ m)
    (alpha : ℝ) (_halpha1 : 0 < alpha)
    (hn1 : (1 : ℝ) ≤ (n : ℝ) ^ alpha)
    (h : Nat.Prime m ∨ (m : ℝ) ≤ (n : ℝ) ^ alpha) :
    IsAdmissible n alpha m m 1 := by
  constructor <;> aesop

/-- Composite m > n^α has a factorization with both factors ≤ n^α. -/
lemma composite_admissible_factorization (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (alpha : ℝ) (halpha1 : 2/3 ≤ alpha) (_halpha2 : alpha < 1)
    (_hnotprime : ¬Nat.Prime m) (hbig : (n : ℝ) ^ alpha < (m : ℝ)) :
    ∃ u v : ℕ, IsAdmissible n alpha m u v := by
  -- Let $w$ be the least divisor of $m$ that is $> n^\alpha$.
  obtain ⟨w, hw_div, hw_gt, hw_min⟩ : ∃ w, w ∣ m ∧ (n : ℝ) ^ alpha < w ∧ ∀ d, d ∣ m → (n : ℝ) ^ alpha < d → w ≤ d := by
    exact ⟨ Nat.find ( ⟨ m, dvd_rfl, hbig ⟩ : ∃ w : ℕ, w ∣ m ∧ ( n : ℝ ) ^ alpha < w ), Nat.find_spec ( ⟨ m, dvd_rfl, hbig ⟩ : ∃ w : ℕ, w ∣ m ∧ ( n : ℝ ) ^ alpha < w ) |>.1, Nat.find_spec ( ⟨ m, dvd_rfl, hbig ⟩ : ∃ w : ℕ, w ∣ m ∧ ( n : ℝ ) ^ alpha < w ) |>.2, fun d hd hd' => Nat.find_min' _ ⟨ hd, hd' ⟩ ⟩;
  -- If $w$ is prime, then $(w, m/w)$ is admissible.
  by_cases hw_prime : Nat.Prime w;
  · cases hw_div ; simp_all +decide [ IsAdmissible ];
    refine' ⟨ w, _, rfl, _, _, Or.inl hw_prime ⟩;
    · contrapose! hw_min;
      have h_contra : (n : ℝ) ^ alpha ≥ (n : ℝ) ^ (2 / 3 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le ( by norm_cast ) halpha1;
      have h_contra : (n : ℝ) ^ (2 / 3 : ℝ) ≥ Real.sqrt n := by
        rw [ Real.sqrt_eq_rpow ] ; exact Real.rpow_le_rpow_of_exponent_le ( mod_cast hn ) ( by norm_num );
      nlinarith [ Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ), ( by norm_cast : ( w :ℝ ) < ‹ℕ› ), ( by norm_cast : ( w :ℝ ) * ‹ℕ› ≤ n ) ];
    · contrapose! hw_gt;
      refine' le_trans _ ( Real.rpow_le_rpow_of_exponent_le ( mod_cast hn ) halpha1 );
      rw [ Real.le_rpow_iff_log_le ] <;> norm_cast;
      · rw [ div_mul_eq_mul_div, le_div_iff₀' ] <;> norm_num;
        rw [ ← Real.log_rpow, ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> try positivity;
        · rw [ pow_three ];
          rw [ sq ];
          gcongr;
          · nlinarith [ show 0 < ‹_› by nlinarith ];
          · rw [ ← @Nat.cast_le ℝ ] at * ; norm_num at *;
            nlinarith [ show ( w : ℝ ) ≥ 2 by exact_mod_cast hw_prime.two_le, show ( ↑‹ℕ› : ℝ ) ≥ w by exact_mod_cast hw_min _ ( dvd_mul_left _ _ ) ( by linarith ) ];
        · exact pow_pos hw_prime.pos _;
        · exact hw_prime.pos;
      · exact hw_prime.pos;
  · -- If $w$ is composite, then $w = r*s$ with $r \leq s$, $r \leq n^\alpha$, and $s \leq n^\alpha$.
    obtain ⟨r, s, hr, hs, hrs⟩ : ∃ r s, 1 < r ∧ 1 < s ∧ r * s = w ∧ r ≤ s ∧ r ≤ (n : ℝ) ^ alpha ∧ s ≤ (n : ℝ) ^ alpha := by
      -- Since $w$ is composite, we can write $w = r * s$ with $1 < r \leq s$.
      obtain ⟨r, s, hr, hs, hrs⟩ : ∃ r s, 1 < r ∧ 1 < s ∧ r * s = w ∧ r ≤ s := by
        have := Nat.exists_dvd_of_not_prime2 ( show 1 < w from ?_ ) hw_prime;
        · obtain ⟨ r, hr₁, hr₂, hr₃ ⟩ := this; exact if hr₄ : r ≤ w / r then ⟨ r, w / r, hr₂, by nlinarith [ Nat.div_mul_cancel hr₁ ], by rw [ Nat.mul_div_cancel' hr₁ ], hr₄ ⟩ else ⟨ w / r, r, by nlinarith [ Nat.div_mul_cancel hr₁ ], hr₂, by rw [ Nat.div_mul_cancel hr₁ ], by linarith ⟩ ;
        · contrapose! hw_gt; interval_cases w <;> norm_num at *;
          · positivity;
          · exact Real.one_le_rpow ( by norm_cast ) ( by positivity );
      refine' ⟨ r, s, hr, hs, hrs.1, hrs.2, _, _ ⟩ <;> contrapose! hw_min;
      · exact ⟨ r, dvd_trans ( by aesop ) hw_div, hw_min, by nlinarith ⟩;
      · exact ⟨ s, dvd_trans ( by aesop ) hw_div, hw_min, by nlinarith ⟩;
    -- Then $rz = m/(s) \leq n/s < n^{1-\alpha/2} \leq n^\alpha$.
    obtain ⟨rz, hrz⟩ : ∃ rz : ℕ, m = s * rz ∧ rz ≤ (n : ℝ) ^ alpha := by
      have hrz : (m : ℝ) / s ≤ (n : ℝ) ^ alpha := by
        refine' le_trans ( div_le_div_of_nonneg_left _ ( by positivity ) ( show ( s : ℝ ) ≥ n ^ ( alpha / 2 ) from _ ) ) _;
        · positivity;
        · rw [ show ( n : ℝ ) ^ ( alpha / 2 ) = Real.sqrt ( n ^ alpha ) by rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( by positivity ) ] ; ring_nf ];
          refine' Real.sqrt_le_iff.mpr _;
          norm_num +zetaDelta at *;
          exact le_trans ( show ( n : ℝ ) ^ alpha ≤ w by exact_mod_cast hw_gt.le ) ( by norm_cast; nlinarith only [ hr, hs, hrs ] );
        · rw [ div_le_iff₀ ( by positivity ) ];
          refine' le_trans ( Nat.cast_le.mpr hmn ) _;
          rw [ ← Real.rpow_add ( by positivity ) ] ; ring_nf;
          exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast ) ( show alpha * ( 3 / 2 ) ≥ 1 by linarith ) );
      exact ⟨ m / s, by rw [ Nat.mul_div_cancel' ( dvd_trans ( dvd_of_mul_left_eq _ hrs.1 ) hw_div ) ], by rwa [ Nat.cast_div ( dvd_trans ( dvd_of_mul_left_eq _ hrs.1 ) hw_div ) ( by positivity ) ] ⟩;
    -- Take $u = \max(s, rz)$ and $v = \min(s, rz)$.
    use max s rz, min s rz;
    cases le_total s rz <;> simp_all +decide [ IsAdmissible ];
    ring

/-- Every m ∈ {1, ..., n} admits an (n, α)-admissible factorization for 2/3 ≤ α < 1. -/
theorem exists_admissible_factorization (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (alpha : ℝ) (halpha1 : 2/3 ≤ alpha) (halpha2 : alpha < 1) :
    ∃ u v : ℕ, IsAdmissible n alpha m u v := by
  by_cases hp : Nat.Prime m
  · exact ⟨m, 1, admissible_trivial n m hm1 alpha (by linarith) (Real.one_le_rpow (by exact_mod_cast hn) (by linarith)) (Or.inl hp)⟩
  · by_cases hle : (m : ℝ) ≤ (n : ℝ) ^ alpha
    · exact ⟨m, 1, admissible_trivial n m hm1 alpha (by linarith) (Real.one_le_rpow (by exact_mod_cast hn) (by linarith)) (Or.inr hle)⟩
    · exact composite_admissible_factorization n hn m hm1 hmn alpha halpha1 halpha2 hp (not_le.mp hle)

/-- Given existence of an admissible pair, produce one with minimal v. -/
lemma exists_minimal_admissible (n : ℕ) (alpha : ℝ) (a : ℕ)
    (h : ∃ u v, IsAdmissible n alpha a u v) :
    ∃ u v, IsAdmissible n alpha a u v ∧ ∀ u' v', IsAdmissible n alpha a u' v' → v ≤ v' := by
  -- Among all v with ∃ u, IsAdmissible, pick the minimum using Nat.find
  have hv : ∃ v, ∃ u, IsAdmissible n alpha a u v := by
    obtain ⟨u, v, hadm⟩ := h; exact ⟨v, u, hadm⟩
  classical
  set v₀ := Nat.find hv with hv₀_def
  obtain ⟨u₀, hadm₀⟩ := Nat.find_spec hv
  exact ⟨u₀, v₀, hadm₀, fun u' v' hadm' => Nat.find_min' hv ⟨u', hadm'⟩⟩

/-! ### K_{2,2}-free from multiplicative Sidon -/

/-- No K₂,₂ in the bipartite (u,v)-graph of a Sidon set. -/
theorem sidon_no_K22 (A : Finset ℕ)
    (hA : IsProductSidon A) (hA0 : ∀ a ∈ A, a ≠ 0)
    (v₁ u₁ v₂ u₂ : ℕ)
    (hv : v₁ ≠ v₂) (hu : u₁ ≠ u₂)
    (h1 : v₁ * u₁ ∈ A) (h2 : v₁ * u₂ ∈ A)
    (h3 : v₂ * u₁ ∈ A) (h4 : v₂ * u₂ ∈ A) :
    False := by
  specialize hA _ h4 _ h1 _ h2 _ h3 ; simp_all +decide [ mul_comm ];
  grind

end

end Combinatorics

section GraphBound

/-! C₄-free bipartite graph bound: |A| ≤ t + s² when s² ≤ t. -/

open Finset BigOperators

noncomputable section

/-- The "collision set": ordered pairs (a₁, a₂) in A with a₁ ≠ a₂ and f(a₁) = f(a₂).
    The size of this set equals ∑_{u ∈ image(f)} deg(u)·(deg(u)-1). -/
def collisionPairs (A : Finset ℕ) (f : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ f p.1 = f p.2)

/-- The fiber of f at u within A. -/
def fiber (A : Finset ℕ) (f : ℕ → ℕ) (u : ℕ) : Finset ℕ :=
  A.filter (fun a => f a = u)

/-- Sum of deg(u)·(deg(u)-1) equals the collision pair count. -/
lemma collision_sum_eq_card (A : Finset ℕ) (f : ℕ → ℕ) :
    ∑ u ∈ A.image f, (fiber A f u).card * ((fiber A f u).card - 1) =
    (collisionPairs A f).card := by
  -- The collision pairs are exactly the pairs of distinct elements in the fibers of f.
  have h_collision_pairs : collisionPairs A f = Finset.biUnion (image f A) (fun u => Finset.offDiag (fiber A f u)) := by
    ext ⟨x, y⟩; simp [collisionPairs, fiber];
    grind;
  rw [ h_collision_pairs, Finset.card_biUnion ];
  · simp +decide [ mul_tsub, Finset.offDiag_card ];
  · intros u hu v hv huv; simp_all +decide [ Finset.disjoint_left, fiber ] ;

/-- Collision pairs ≤ s(s-1) from K₂,₂-free. -/
lemma collision_bound_from_K22 (A : Finset ℕ) (f g : ℕ → ℕ)
    (h_inj : ∀ a ∈ A, ∀ b ∈ A, f a = f b → g a = g b → a = b)
    (h_K22 : ∀ v₁ v₂ u₁ u₂ : ℕ, v₁ ≠ v₂ → u₁ ≠ u₂ →
      (∃ a ∈ A, g a = v₁ ∧ f a = u₁) → (∃ a ∈ A, g a = v₁ ∧ f a = u₂) →
      (∃ a ∈ A, g a = v₂ ∧ f a = u₁) → (∃ a ∈ A, g a = v₂ ∧ f a = u₂) → False) :
    (collisionPairs A f).card ≤ (A.image g).card * ((A.image g).card - 1) := by
  -- We show that |collisionPairs A f| ≤ |image g| · (|image g| - 1) by constructing an injection from collisionPairs to the off-diagonal pairs of image g.
  have h_inj : Finset.card (collisionPairs A f) ≤ Finset.card (Finset.offDiag (Finset.image g A)) := by
    refine' le_trans _ ( Finset.card_le_card _ );
    case refine'_2 => exact Finset.image ( fun p => ( g p.1, g p.2 ) ) ( collisionPairs A f );
    · rw [ Finset.card_image_of_injOn ];
      intros p hp q hq h_eq;
      specialize h_K22 ( g p.1 ) ( g p.2 ) ( f p.1 ) ( f q.1 ) ; simp_all +decide [ collisionPairs ];
      grind;
    · intro x hx; obtain ⟨ p, hp, rfl ⟩ := Finset.mem_image.mp hx; simp_all +decide [ collisionPairs ] ;
      exact ⟨ ⟨ p.1, hp.1.1, rfl ⟩, ⟨ p.2, hp.1.2, rfl ⟩, fun h => hp.2.1 <| h_inj _ hp.1.1 _ hp.1.2 hp.2.2 h ⟩;
  simpa [ mul_tsub, mul_one ] using h_inj

/-- Cauchy-Schwarz for Finset sums: (∑ f)² ≤ |S| · ∑ f². -/
lemma finset_cauchy_schwarz_sq (S : Finset ℕ) (w : ℕ → ℕ) :
    (∑ u ∈ S, w u) ^ 2 ≤ S.card * ∑ u ∈ S, (w u) ^ 2 := by
  -- By the Cauchy-Schwarz inequality, we have that for any vectors $u$ and $v$ of equal length, $(∑ i, u i * v i)^2 ≤ (∑ i, u i^2) * (∑ i, v i^2)$.
  have h_cauchy_schwarz : ∀ (u v : ℕ → ℝ), (∑ i ∈ S, u i * v i)^2 ≤ (∑ i ∈ S, u i^2) * (∑ i ∈ S, v i^2) := by
    exact fun u v => sum_mul_sq_le_sq_mul_sq S u v;
  simpa [ ← @Nat.cast_le ℝ ] using h_cauchy_schwarz 1 ( fun i => w i )

/-- The sum of fibers equals A.card. -/
lemma sum_fiber_card (A : Finset ℕ) (f : ℕ → ℕ) :
    ∑ u ∈ A.image f, (fiber A f u).card = A.card := by
  exact Eq.symm (card_eq_sum_card_image f A)

/-- The quadratic inequality: e² ≤ te + ts(s-1). -/
lemma quadratic_ineq_from_K22 (A : Finset ℕ) (f g : ℕ → ℕ)
    (h_inj : ∀ a ∈ A, ∀ b ∈ A, f a = f b → g a = g b → a = b)
    (h_K22 : ∀ v₁ v₂ u₁ u₂ : ℕ, v₁ ≠ v₂ → u₁ ≠ u₂ →
      (∃ a ∈ A, g a = v₁ ∧ f a = u₁) → (∃ a ∈ A, g a = v₁ ∧ f a = u₂) →
      (∃ a ∈ A, g a = v₂ ∧ f a = u₁) → (∃ a ∈ A, g a = v₂ ∧ f a = u₂) → False)
    (s t : ℕ) (hs : (A.image g).card ≤ s) (ht : (A.image f).card ≤ t) (_ht0 : 0 < t) :
    A.card * A.card ≤ t * A.card + t * s * (s - 1) := by
  -- By the lemma collision_bound_from_K22, we have ∑_{u ∈ image f} |fiber u|·(|fiber u|-1) ≤ s·(s-1).
  have h_bound : ∑ u ∈ A.image f, (fiber A f u).card * ((fiber A f u).card - 1) ≤ s * (s - 1) := by
    have h_collision_bound : (collisionPairs A f).card ≤ (A.image g).card * ((A.image g).card - 1) := by
      exact collision_bound_from_K22 A f g h_inj h_K22;
    exact le_trans ( by rw [ collision_sum_eq_card ] ) ( h_collision_bound.trans ( Nat.mul_le_mul hs ( Nat.sub_le_sub_right hs 1 ) ) );
  -- By the lemma sum_fiber_card, we have ∑_{u ∈ image f} |fiber u| = |A|.
  have h_sum : ∑ u ∈ A.image f, (fiber A f u).card = A.card := by
    exact sum_fiber_card A f;
  have h_cauchy_schwarz : (∑ u ∈ A.image f, (fiber A f u).card) ^ 2 ≤ (A.image f).card * ∑ u ∈ A.image f, (fiber A f u).card * (fiber A f u).card := by
    convert finset_cauchy_schwarz_sq ( A.image f ) ( fun u => # ( fiber A f u ) ) using 1;
    exact congrArg _ ( Finset.sum_congr rfl fun _ _ => by ring );
  -- By the lemma sum_fiber_card, we have ∑_{u ∈ image f} |fiber u|² = ∑_{u ∈ image f} |fiber u|·(|fiber u|-1) + ∑_{u ∈ image f} |fiber u|.
  have h_sum_sq : ∑ u ∈ A.image f, (fiber A f u).card * (fiber A f u).card = ∑ u ∈ A.image f, (fiber A f u).card * ((fiber A f u).card - 1) + ∑ u ∈ A.image f, (fiber A f u).card := by
    simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x hx => by cases h : # ( fiber A f x ) <;> simp +decide ; linarith;
  nlinarith [ Nat.zero_le ( ∑ u ∈ image f A, # ( fiber A f u ) * ( # ( fiber A f u ) - 1 ) ) ]

/-- Main result: C4-free bound for function pairs. -/
theorem c4_free_pair_bound (A : Finset ℕ) (f g : ℕ → ℕ)
    (h_inj : ∀ a ∈ A, ∀ b ∈ A, f a = f b → g a = g b → a = b)
    (h_K22 : ∀ v₁ v₂ u₁ u₂ : ℕ, v₁ ≠ v₂ → u₁ ≠ u₂ →
      (∃ a ∈ A, g a = v₁ ∧ f a = u₁) → (∃ a ∈ A, g a = v₁ ∧ f a = u₂) →
      (∃ a ∈ A, g a = v₂ ∧ f a = u₁) → (∃ a ∈ A, g a = v₂ ∧ f a = u₂) → False)
    (s t : ℕ)
    (hs : (A.image g).card ≤ s) (ht : (A.image f).card ≤ t)
    (ht0 : 0 < t) (hst : s * s ≤ t) :
    A.card ≤ t + s * s := by
  exact c4_free_bound_sq s t A.card hst
    (quadratic_ineq_from_K22 A f g h_inj h_K22 s t hs ht ht0)

end

end GraphBound

section MiddleBound

/-! Dyadic decomposition + C₄ bound for middle second factors. -/

open Finset BigOperators Real

noncomputable section


/-! ### Partition by binary level -/

/-- The binary level of a positive natural number: j = Nat.log 2 v, so v ∈ [2^j, 2^{j+1}). -/
def binLevel (v : ℕ) : ℕ := Nat.log 2 v

/-- Elements at binary level j have v ∈ [2^j, 2^{j+1}). -/
lemma binLevel_range (v : ℕ) (hv : v ≠ 0) :
    2 ^ binLevel v ≤ v ∧ v < 2 ^ (binLevel v + 1) := by
  constructor
  · exact Nat.pow_log_le_self 2 hv
  · exact Nat.lt_pow_succ_log_self (by omega) v

/-- Image of v at level j has card ≤ 2^j. -/
lemma image_v_card_le_level (B : Finset ℕ) (v_fn : ℕ → ℕ) (j : ℕ)
    (hv : ∀ a ∈ B, binLevel (v_fn a) = j)
    (hv_pos : ∀ a ∈ B, 0 < v_fn a) :
    (B.image v_fn).card ≤ 2 ^ j := by
  -- The image of B under v_fn is a subset of the interval [2^j, 2^(j+1)).
  have h_subset : image v_fn B ⊆ Finset.Ico (2^j) (2^(j+1)) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have h_level : binLevel (v_fn a) = j := hv a ha
    have h_range : 2^j ≤ v_fn a ∧ v_fn a < 2^(j+1) := by
      exact h_level ▸ binLevel_range _ ( ne_of_gt ( hv_pos a ha ) )
    exact Finset.mem_Ico.mpr h_range;
  convert Finset.card_le_card h_subset ; norm_num [ pow_succ' ];
  exact Eq.symm ( Nat.sub_eq_of_eq_add <| by ring )

/-- Image of u at level j has card ≤ n/2^j. -/
lemma image_u_card_le_level (B : Finset ℕ) (u_fn : ℕ → ℕ) (n j : ℕ)
    (hu_pos : ∀ a ∈ B, 0 < u_fn a)
    (hu : ∀ a ∈ B, u_fn a ≤ n / 2^j) :
    (B.image u_fn).card ≤ n / 2^j := by
  exact le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ hu_pos x hx, hu x hx ⟩ ) ( by simp )

/-! ### Geometric series bounds -/

/-- The geometric series ∑_{j=a}^{b} 2^{-j} ≤ 2^{1-a}. -/
lemma sum_pow_half_le (a b : ℕ) (_ha : 0 < a) :
    ∑ j ∈ Finset.Icc a b, ((1 : ℝ) / 2) ^ j ≤ 2 * (1 / 2 : ℝ) ^ a := by
  by_cases hab : b < a;
  · aesop;
  · erw [ geom_sum_Ico ] <;> ring_nf <;> norm_num;
    grind

/-- The geometric series ∑_{j=a}^{b} (√2)^j ≤ C · (√2)^b for some constant C. -/
lemma sum_sqrt2_pow_le (a b : ℕ) (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc a b, Real.sqrt 2 ^ j ≤ (2 + Real.sqrt 2) * Real.sqrt 2 ^ b := by
  erw [ geom_sum_Ico ] <;> norm_num;
  · rw [ div_le_iff₀ ] <;> ring_nf <;> norm_num;
    · linarith [ pow_pos ( Real.sqrt_pos.mpr zero_lt_two ) a ];
    · norm_num [ Real.lt_sqrt ];
  · grind

/-! ### C4 sqrt bound for Sidon sets -/

/-- C4 bound in sqrt form for Sidon subsets. -/
lemma sidon_c4_sqrt_bound' (A : Finset ℕ) (hSidon : IsProductSidon A) (_hA_pos : ∀ a ∈ A, 0 < a)
    (B : Finset ℕ) (hB : B ⊆ A) (u_fn v_fn : ℕ → ℕ)
    (hfact : ∀ a ∈ B, a = u_fn a * v_fn a)
    (_huv : ∀ a ∈ B, v_fn a ≤ u_fn a)
    (s t : ℕ) (hs : (B.image v_fn).card ≤ s) (ht : (B.image u_fn).card ≤ t) (ht0 : 0 < t) :
    (B.card : ℝ) ≤ (t : ℝ) + (s : ℝ) * Real.sqrt (t : ℝ) := by
  convert c4_free_bound_sqrt s t B.card ht0 _;
  convert quadratic_ineq_from_K22 B u_fn v_fn _ _ s t hs ht ht0;
  · grind;
  · rintro v₁ v₂ u₁ u₂ hv₁₂ hu₁₂ ⟨ a₁, ha₁, hv₁, hu₁ ⟩ ⟨ a₂, ha₂, hv₂, hu₂ ⟩ ⟨ a₃, ha₃, hv₃, hu₃ ⟩ ⟨ a₄, ha₄, hv₄, hu₄ ⟩;
    have := hSidon a₁ ( hB ha₁ ) a₄ ( hB ha₄ ) a₂ ( hB ha₂ ) a₃ ( hB ha₃ ) ?_ <;> simp +decide [ ← hv₁, ← hu₁, ← hu₂, ← hv₃] at *;
    · grind;
    · grind

/-! ### Single level C4 bound -/

/-- C4 bound for a single binary level: |B_j| ≤ n/2^j + 2^j·√(n/2^j). -/
lemma single_level_c4 (n : ℕ) (A : Finset ℕ)
    (hSidon : IsProductSidon A) (hA_pos : ∀ a ∈ A, 0 < a)
    (B : Finset ℕ) (hB : B ⊆ A)
    (u_fn v_fn : ℕ → ℕ)
    (hfact : ∀ a ∈ B, a = u_fn a * v_fn a)
    (huv : ∀ a ∈ B, v_fn a ≤ u_fn a)
    (hv_pos : ∀ a ∈ B, 0 < v_fn a)
    (j : ℕ) (_hj : 0 < j)
    (hv_level : ∀ a ∈ B, binLevel (v_fn a) = j)
    (hu_bound : ∀ a ∈ B, u_fn a * v_fn a ≤ n)
    (hn_pos : 0 < n / 2^j) :
    (B.card : ℝ) ≤ (n / 2^j : ℝ) + (2^j : ℝ) * Real.sqrt (n / 2^j : ℝ) := by
  -- Apply the C4 bound from the Sidon property with $s = 2^j$, $t = n / 2^j$.
  have h_c4_bound : (B.card : ℝ) ≤ (n / 2 ^ j : ℕ) + (2 ^ j : ℕ) * Real.sqrt (n / 2 ^ j : ℕ) := by
    convert sidon_c4_sqrt_bound' A hSidon hA_pos B hB u_fn v_fn hfact huv ( 2 ^ j ) ( n / 2 ^ j ) _ _ _ using 1;
    · exact image_v_card_le_level B v_fn j hv_level hv_pos;
    · refine' image_u_card_le_level B u_fn n j _ _;
      · grind;
      · intro a ha
        have h_v_bound : v_fn a ≥ 2 ^ j := by
          exact hv_level a ha ▸ Nat.pow_log_le_self 2 ( ne_of_gt ( hv_pos a ha ) );
        rw [ Nat.le_div_iff_mul_le ( by positivity ) ] ; nlinarith [ hu_bound a ha ];
    · exact hn_pos;
  refine le_trans h_c4_bound ?_;
  gcongr <;> norm_cast;
  · rw [ le_div_iff₀ ] <;> norm_cast <;> linarith [ Nat.div_mul_le_self n ( 2 ^ j ), Nat.one_le_pow j 2 zero_lt_two ];
  · rw [ le_div_iff₀ ] <;> norm_cast <;> linarith [ Nat.div_mul_le_self n ( 2 ^ j ), Nat.one_le_pow j 2 zero_lt_two ]

/-! ### Core dyadic bound -/

/-- Dyadic bound: |B| ≤ 4n/V₀ + 4√(nV₁) for Sidon sets. -/
lemma sidon_dyadic_bound (n : ℕ) (hn : 4 ≤ n) (A : Finset ℕ)
    (hSidon : IsProductSidon A) (hA_pos : ∀ a ∈ A, 0 < a)
    (B : Finset ℕ) (hB : B ⊆ A)
    (u_fn v_fn : ℕ → ℕ)
    (hfact : ∀ a ∈ B, a = u_fn a * v_fn a)
    (huv : ∀ a ∈ B, v_fn a ≤ u_fn a)
    (hv_pos : ∀ a ∈ B, 0 < v_fn a)
    (V₀ V₁ : ℕ) (hV₀ : 0 < V₀)
    (hv_lower : ∀ a ∈ B, V₀ < v_fn a)
    (hv_upper : ∀ a ∈ B, v_fn a ≤ V₁)
    (ha_upper : ∀ a ∈ B, u_fn a * v_fn a ≤ n) :
    (B.card : ℝ) ≤ 4 * (n : ℝ) / (V₀ : ℝ) + 4 * Real.sqrt ((n : ℝ) * (V₁ : ℝ)) := by
  -- Set levels = B.image (fun a => binLevel (v_fn a)), j_min = Nat.log 2 (V₀ + 1), j_max = Nat.log 2 V₁.
  set levels := B.image (fun a => binLevel (v_fn a))
  set j_min := Nat.log 2 (V₀ + 1)
  set j_max := Nat.log 2 V₁;
  -- If B is empty, the bound holds trivially.
  by_cases hB_empty : B = ∅;
  · norm_num [ hB_empty ] ; positivity;
  · -- For each level j, by single_level_c4:
    have h_level_bound : ∀ j ∈ levels, (B.filter (fun a => binLevel (v_fn a) = j)).card ≤ (n / 2^j : ℝ) + (2^j : ℝ) * Real.sqrt (n / 2^j : ℝ) := by
      intros j hj
      have h_level_bound : (B.filter (fun a => binLevel (v_fn a) = j)).card ≤ (n / 2^j : ℝ) + (2^j : ℝ) * Real.sqrt (n / 2^j : ℝ) := by
        have h_level_pos : 0 < j := by
          obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hj; exact Nat.log_pos one_lt_two ( by linarith [ hv_lower a ha ] ) ;
        convert single_level_c4 n A hSidon hA_pos ( B.filter ( fun a => binLevel ( v_fn a ) = j ) ) ( Finset.filter_subset _ _ |> Finset.Subset.trans <| hB ) u_fn v_fn _ _ _ j h_level_pos _ _ using 1;
        any_goals intro a ha; exact Finset.mem_filter.mp ha |>.2;
        · norm_num +zetaDelta at *;
          exact Or.inl ( by obtain ⟨ a, ha₁, ha₂ ⟩ := hj; have := binLevel_range ( v_fn a ) ( ne_of_gt ( hv_pos a ha₁ ) ) ; norm_num [ ha₂ ] at this; nlinarith [ huv a ha₁, ha_upper a ha₁ ] );
        · exact fun a ha => hfact a <| Finset.mem_filter.mp ha |>.1;
        · exact fun a ha => huv a <| Finset.mem_filter.mp ha |>.1;
        · exact fun a ha => hv_pos a <| Finset.mem_filter.mp ha |>.1;
        · exact fun a ha => ha_upper a <| Finset.mem_filter.mp ha |>.1;
      convert h_level_bound using 1;
    -- Summing over all levels, we get:
    have h_sum_bound : (B.card : ℝ) ≤ ∑ j ∈ Finset.Icc j_min j_max, (n / 2^j : ℝ) + ∑ j ∈ Finset.Icc j_min j_max, (2^j : ℝ) * Real.sqrt (n / 2^j : ℝ) := by
      have h_sum_bound : (B.card : ℝ) = ∑ j ∈ levels, (B.filter (fun a => binLevel (v_fn a) = j)).card := by
        rw [ Finset.card_eq_sum_ones, Finset.sum_image' ] ; simp +contextual ;
      rw [ h_sum_bound, Nat.cast_sum ];
      rw [ ← Finset.sum_add_distrib ];
      refine' le_trans ( Finset.sum_le_sum h_level_bound ) _;
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity;
      intro j hj;
      obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hj;
      exact Finset.mem_Icc.mpr ⟨ Nat.log_mono_right ( by linarith [ hv_lower a ha ] ), Nat.log_mono_right ( by linarith [ hv_upper a ha ] ) ⟩;
    -- For the first sum, we have:
    have h_first_sum : ∑ j ∈ Finset.Icc j_min j_max, (n / 2^j : ℝ) ≤ 2 * n / 2^j_min := by
      have h_first_sum : ∑ j ∈ Finset.Icc j_min j_max, (1 / 2 : ℝ) ^ j ≤ 2 * (1 / 2 : ℝ) ^ j_min := by
        convert sum_pow_half_le j_min j_max _ using 1;
        exact Nat.log_pos ( by norm_num ) ( by linarith );
      convert mul_le_mul_of_nonneg_left h_first_sum ( Nat.cast_nonneg n ) using 1 <;> ring_nf;
      · norm_num [ Finset.mul_sum _ _ _ ];
      · norm_num;
    -- For the second sum, we have:
    have h_second_sum : ∑ j ∈ Finset.Icc j_min j_max, (2^j : ℝ) * Real.sqrt (n / 2^j : ℝ) ≤ (2 + Real.sqrt 2) * Real.sqrt n * Real.sqrt (2^j_max) := by
      have h_second_sum : ∑ j ∈ Finset.Icc j_min j_max, (2^j : ℝ) * Real.sqrt (n / 2^j : ℝ) ≤ Real.sqrt n * ∑ j ∈ Finset.Icc j_min j_max, (Real.sqrt 2 : ℝ) ^ j := by
        rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_le_sum fun i hi => ?_; rw [ mul_comm ] ; norm_num [ mul_assoc, mul_left_comm, mul_comm, Real.sqrt_div_self ] ;
        rw [ show ( 2 : ℝ ) ^ i = ( Real.sqrt 2 ^ i ) ^ 2 by rw [ pow_right_comm, Real.sq_sqrt ( by norm_num ) ] ] ; norm_num ; ring_nf ; norm_num;
        norm_num [ pow_mul ];
        norm_num [ sq, mul_assoc, mul_comm, mul_left_comm ];
      have h_second_sum_bound : ∑ j ∈ Finset.Icc j_min j_max, (Real.sqrt 2 : ℝ) ^ j ≤ (2 + Real.sqrt 2) * (Real.sqrt 2 : ℝ) ^ j_max := by
        convert sum_sqrt2_pow_le j_min j_max _ using 1;
        exact Nat.log_mono_right ( by linarith [ hv_lower _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty hB_empty ) ), hv_upper _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty hB_empty ) ) ] );
      convert h_second_sum.trans ( mul_le_mul_of_nonneg_left h_second_sum_bound <| Real.sqrt_nonneg _ ) using 1 ; norm_num [ mul_assoc, mul_comm, mul_left_comm ];
      exact Or.inl <| Or.inl <| by rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num [ pow_mul', Real.sqrt_nonneg ] ;
    -- Since $2^{j_{\text{max}}} \leq V₁$, we have $\sqrt{2^{j_{\text{max}}}} \leq \sqrt{V₁}$.
    have h_second_sum_bound : Real.sqrt (2^j_max) ≤ Real.sqrt V₁ := by
      exact Real.sqrt_le_sqrt <| mod_cast Nat.pow_log_le_self 2 <| by linarith [ show V₁ > 0 from Nat.pos_of_ne_zero <| by rintro rfl; exact absurd ( hv_upper _ <| Classical.choose_spec <| Finset.nonempty_of_ne_empty hB_empty ) <| by linarith [ hv_lower _ <| Classical.choose_spec <| Finset.nonempty_of_ne_empty hB_empty ] ] ;
    refine le_trans h_sum_bound <| add_le_add ?_ ?_;
    · refine le_trans h_first_sum ?_;
      rw [ div_le_div_iff₀ ] <;> norm_cast <;> try positivity;
      have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) ( V₀ + 1 );
      rw [ pow_succ' ] at this ; nlinarith;
    · refine le_trans h_second_sum ?_;
      rw [ Real.sqrt_mul <| by positivity ];
      rw [ mul_assoc ];
      exact le_trans ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left h_second_sum_bound <| Real.sqrt_nonneg _ ) <| by positivity ) <| by nlinarith only [ show ( Real.sqrt n : ℝ ) * Real.sqrt V₁ ≥ 0 by positivity, show ( Real.sqrt 2 : ℝ ) ≤ 2 by rw [ Real.sqrt_le_left ] <;> norm_num, Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ ( n : ℝ ) by positivity ), Real.mul_self_sqrt ( show 0 ≤ ( V₁ : ℝ ) by positivity ) ] ;

end

end MiddleBound

section SiftedIntervals

/-! Sifted interval estimates combining Buchstab with C₄ bound. -/

open Finset BigOperators Real

noncomputable section


attribute [local instance] Classical.propDecidable

/-! ### Sifted interval estimates -/

/-- Per-level v-sifted count ≤ (Ω_α+ε)(eʰ-1)e^{-rh}√n/log n. -/
lemma sifted_interval_v_bound
    (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hU_strict : UAlpha alpha < 3)
    (hh : 0 < h_val) (ε : ℝ) (hε : 0 < ε) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        (((Finset.Icc 1 n).filter (fun m : ℕ =>
          Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) < (m : ℝ) ∧
          (m : ℝ) ≤ Real.exp (-(((r : ℝ) - 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) ∧
          ∀ p : ℕ, Nat.Prime p → p ∣ m →
            (p : ℝ) ≥ Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (alpha - 1/2))).card : ℝ) ≤
        (OmegaAlpha alpha + ε) * (Real.exp h_val - 1) * Real.exp (-((r : ℝ) * h_val)) *
          (n : ℝ) ^ (1/2 : ℝ) / Real.log n := by
  obtain ⟨N₁, hN₁⟩ := buchstab_diff_v_estimate alpha h_val hα1 hα2 hU_strict hh ε hε lambda hlambda;
  refine' ⟨ N₁ + 4, fun n hn r hr₁ hr₂ => le_trans ( filter_interval_le_sievePhi_diff_real n _ _ _ _ _ _ ) ( hN₁ n ( by linarith ) r hr₁ hr₂ ) ⟩;
  · positivity;
  · exact mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr ( by nlinarith ) ) ( by positivity );
  · refine' Nat.floor_le_of_le _;
    refine' le_trans ( mul_le_of_le_one_left ( by positivity ) ( Real.exp_le_one_iff.mpr _ ) ) _;
    · exact neg_nonpos_of_nonneg ( mul_nonneg ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hr₁ ) ) hh.le );
    · exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( show ( 1 : ℝ ) / 2 ≤ 1 by norm_num ) ) ( by norm_num )

/-- Per-level u-sifted count ≤ (Ω_α+ε)H(rh)(e^{rh}-e^{-rh})√n/log n. -/
lemma sifted_interval_u_bound
    (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hU_strict : UAlpha alpha < 3)
    (hh : 0 < h_val) (ε : ℝ) (hε : 0 < ε) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
        (((Finset.Icc 1 n).filter (fun m : ℕ =>
          Real.exp (-((r : ℝ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) < (m : ℝ) ∧
          (m : ℝ) ≤ Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) ∧
          ∀ p : ℕ, Nat.Prime p → p ∣ m →
            ¬((p : ℝ) > Real.exp (2 * (r : ℝ) * h_val) ∧
              (p : ℝ) < Real.exp (((r : ℝ) - 1) * h_val) * (n : ℝ) ^ (alpha - 1/2)))).card : ℝ) ≤
        (OmegaAlpha alpha + ε) * HFunc ((r : ℝ) * h_val) *
          (Real.exp ((r : ℝ) * h_val) - Real.exp (-((r : ℝ) * h_val))) *
          (n : ℝ) ^ (1/2 : ℝ) / Real.log n := by
  -- Decompose m = d·e, split d ≤ n^η vs d > n^η, apply Buchstab + Rankin tail.
  -- Step 0: Apply buchstab_diff_u_per_d with ε/2
  obtain ⟨η, hη_pos, hη_lt_half, N₁, hN₁⟩ := buchstab_diff_u_per_d alpha h_val hα1 hα2 hU_strict hh (ε/2) (by linarith) lambda hlambda
  -- Step 0b: Apply smooth_tail_bound
  have hC_tail : (0:ℝ) < ε / 4 * (1 - Real.exp (-(2 * h_val))) := by
    apply mul_pos (by linarith)
    linarith [Real.exp_lt_one_iff.mpr (by linarith : -(2 * h_val) < 0)]
  obtain ⟨N₂, hN₂⟩ := smooth_tail_bound h_val hh lambda hlambda η hη_pos
    (ε / 4 * (1 - Real.exp (-(2 * h_val)))) hC_tail
  obtain ⟨N₃, hN₃⟩ := n_eta_error_small h_val hh η hη_pos hη_lt_half
    (ε / 4 * (Real.exp h_val - Real.exp (-h_val)))
    (by apply mul_pos (by linarith)
        linarith [Real.add_one_le_exp h_val, Real.exp_le_one_iff.mpr (by linarith : -h_val ≤ 0)])
  -- Step 0d: exp(rh)*n^{1/2} ≤ n
  obtain ⟨N₄, hN₄⟩ := exp_rh_sqrt_le_n h_val hh lambda hlambda
  -- Combine N
  refine ⟨max (max N₁ N₂) (max N₃ N₄) + 4, fun n hn r hr₁ hr₂ => ?_⟩
  -- Extract hypotheses
  have hn1 : n ≥ N₁ := by omega
  have hn2 : n ≥ N₂ := by omega
  have hn3 : n ≥ N₃ := by omega
  have hn_ge4 : 4 ≤ n := by omega
  have hM₁_le_n : ⌊Real.exp ((r : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ)⌋₊ ≤ n :=
    hN₄ n (by omega) r hr₁ hr₂
  -- Key positivity facts
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast show 1 < n by omega)
  have heh_diff_pos : 0 < Real.exp h_val - Real.exp (-h_val) := by
    linarith [Real.add_one_le_exp h_val, Real.exp_le_one_iff.mpr (by linarith : -h_val ≤ 0)]
  have herh_diff_pos : 0 < Real.exp ((r:ℝ) * h_val) - Real.exp (-((r:ℝ) * h_val)) := by
    have hr_pos : (0:ℝ) < (r:ℝ) * h_val := by positivity
    linarith [Real.add_one_le_exp ((r:ℝ) * h_val),
              Real.exp_le_one_iff.mpr (show -((r:ℝ) * h_val) ≤ 0 by linarith)]
  -- Step 1: Decompose using sifted_u_count_le_decomp
  have h_decomp := sifted_u_count_le_decomp n alpha h_val r hh hr₁ hn_ge4 hM₁_le_n
  -- The count (as ℝ) is bounded by the decomposition sum (cast to ℝ)
  -- We prove the final bound by combining the decomposition with per-d bounds and tail bounds.
  -- This final assembly step is proven below.
  -- Apply the bound from hN₁ to each term in the sum.
  have h_sum_bound : ∑ d ∈ Finset.filter (fun d => ∀ p ∈ d.primeFactors, p ≤ ⌊Real.exp (2 * r * h_val)⌋₊) (Finset.Icc 1 ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ)⌋₊), (sievePhi ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ) / d⌋₊ ⌈Real.exp ((r - 1) * h_val) * n ^ (alpha - 1 / 2)⌉₊ - sievePhi ⌊Real.exp (-(r * h_val)) * n ^ (1 / 2 : ℝ) / d⌋₊ ⌈Real.exp ((r - 1) * h_val) * n ^ (alpha - 1 / 2)⌉₊) ≤ (OmegaAlpha alpha + ε / 2) * (Real.exp (r * h_val) - Real.exp (-(r * h_val))) * n ^ (1 / 2 : ℝ) / Real.log n * HFunc (r * h_val) + (ε / 4) * (Real.exp (r * h_val) - Real.exp (-(r * h_val))) * n ^ (1 / 2 : ℝ) / Real.log n := by
    have h_sum_bound : ∑ d ∈ Finset.filter (fun d => d ≤ ⌊(n : ℝ) ^ η⌋₊) (Finset.filter (fun d => ∀ p ∈ d.primeFactors, p ≤ ⌊Real.exp (2 * r * h_val)⌋₊) (Finset.Icc 1 ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ)⌋₊)), (sievePhi ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ) / d⌋₊ ⌈Real.exp ((r - 1) * h_val) * n ^ (alpha - 1 / 2)⌉₊ - sievePhi ⌊Real.exp (-(r * h_val)) * n ^ (1 / 2 : ℝ) / d⌋₊ ⌈Real.exp ((r - 1) * h_val) * n ^ (alpha - 1 / 2)⌉₊) ≤ (OmegaAlpha alpha + ε / 2) * (Real.exp (r * h_val) - Real.exp (-(r * h_val))) * n ^ (1 / 2 : ℝ) / Real.log n * HFunc (r * h_val) := by
      have h_sum_bound : ∑ d ∈ Finset.filter (fun d => d ≤ ⌊(n : ℝ) ^ η⌋₊) (Finset.filter (fun d => ∀ p ∈ d.primeFactors, p ≤ ⌊Real.exp (2 * r * h_val)⌋₊) (Finset.Icc 1 ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ)⌋₊)), (1 / (d : ℝ)) ≤ HFunc (r * h_val) := by
        convert partial_sum_smooth_le_HFunc ( r * h_val ) _ _ using 1;
        any_goals exact Finset.filter ( fun d => d ≤ ⌊ ( n : ℝ ) ^ η⌋₊ ) ( Finset.filter ( fun d => ∀ p ∈ d.primeFactors, p ≤ ⌊Real.exp ( 2 * r * h_val ) ⌋₊ ) ( Finset.Icc 1 ⌊Real.exp ( r * h_val ) * n ^ ( 1 / 2 : ℝ ) ⌋₊ ) );
        · grind +revert;
        · simp +decide [ Nat.smoothNumbers ];
          exact fun d hd₁ hd₂ hd₃ hd₄ => ⟨ by linarith, fun p hp₁ hp₂ hp₃ => by simpa only [ mul_assoc ] using hd₃ p hp₁ hp₂ hp₃ ⟩;
      refine' le_trans _ ( mul_le_mul_of_nonneg_left h_sum_bound _ );
      · push_cast [ Finset.mul_sum _ _ _ ];
        gcongr;
        rename_i d hd;
        rw [ Nat.cast_sub ];
        · convert hN₁ n hn1 r hr₁ hr₂ d ( Finset.mem_Icc.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp hd |>.1 ) |>.1 ) |>.1 ) _ using 1;
          · ring;
          · exact le_trans ( Nat.cast_le.mpr ( Finset.mem_filter.mp hd |>.2 ) ) ( Nat.floor_le ( by positivity ) );
        · apply_rules [ sievePhi_mono_x ];
          gcongr;
          nlinarith;
      · exact div_nonneg ( mul_nonneg ( mul_nonneg ( add_nonneg ( by
          exact mul_nonneg ( mul_nonneg zero_le_two ( one_div_nonneg.mpr ( by linarith ) ) ) ( buchstabOmega_pos _ ( by linarith [ show 1 ≤ UAlpha alpha from by rw [ UAlpha ] ; rw [ le_div_iff₀ ] <;> linarith ] ) |> le_of_lt ) ) ( by positivity ) ) ( by positivity ) ) ( by positivity ) ) ( by positivity );
    have h_sum_bound_tail : ∑ d ∈ Finset.filter (fun d => d > ⌊(n : ℝ) ^ η⌋₊) (Finset.filter (fun d => ∀ p ∈ d.primeFactors, p ≤ ⌊Real.exp (2 * r * h_val)⌋₊) (Finset.Icc 1 ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ)⌋₊)), (sievePhi ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ) / d⌋₊ ⌈Real.exp ((r - 1) * h_val) * n ^ (alpha - 1 / 2)⌉₊) ≤ (ε / 4) * (Real.exp (r * h_val) - Real.exp (-(r * h_val))) * n ^ (1 / 2 : ℝ) / Real.log n := by
      have h_sum_bound_tail : ∑ d ∈ Finset.filter (fun d => d > ⌊(n : ℝ) ^ η⌋₊) (Finset.filter (fun d => ∀ p ∈ d.primeFactors, p ≤ ⌊Real.exp (2 * r * h_val)⌋₊) (Finset.Icc 1 ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ)⌋₊)), (sievePhi ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ) / d⌋₊ ⌈Real.exp ((r - 1) * h_val) * n ^ (alpha - 1 / 2)⌉₊) ≤ Real.exp (r * h_val) * n ^ (1 / 2 : ℝ) * (∑ d ∈ Finset.filter (fun d => d > ⌊(n : ℝ) ^ η⌋₊ ∧ ∀ p ∈ d.primeFactors, p ≤ ⌊Real.exp (2 * r * h_val)⌋₊) (Finset.Icc 1 ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ)⌋₊), (d : ℝ)⁻¹) := by
        have h_sum_bound_tail : ∀ d ∈ Finset.filter (fun d => d > ⌊(n : ℝ) ^ η⌋₊ ∧ ∀ p ∈ d.primeFactors, p ≤ ⌊Real.exp (2 * r * h_val)⌋₊) (Finset.Icc 1 ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ)⌋₊), (sievePhi ⌊Real.exp (r * h_val) * n ^ (1 / 2 : ℝ) / d⌋₊ ⌈Real.exp ((r - 1) * h_val) * n ^ (alpha - 1 / 2)⌉₊) ≤ (Real.exp (r * h_val) * n ^ (1 / 2 : ℝ)) / d := by
          intros d hd;
          refine' le_trans _ ( Nat.floor_le <| by positivity );
          refine' mod_cast le_trans ( show sievePhi _ _ ≤ _ from _ ) ( Nat.le_refl _ );
          exact le_trans ( Finset.card_filter_le _ _ ) ( by norm_num );
        push_cast [ Finset.mul_sum _ _ _ ];
        convert Finset.sum_le_sum h_sum_bound_tail using 1;
        simp +decide only [filter_filter, and_comm];
      refine le_trans h_sum_bound_tail ?_;
      refine le_trans ( mul_le_mul_of_nonneg_left ( show ( ∑ d ∈ Icc 1 ⌊Real.exp ( r * h_val ) * n ^ ( 1 / 2 : ℝ ) ⌋₊ with d > ⌊ ( n : ℝ ) ^ η⌋₊ ∧ ∀ p ∈ d.primeFactors, p ≤ ⌊Real.exp ( 2 * r * h_val ) ⌋₊, ( d : ℝ ) ⁻¹ ) ≤ ( ε / 4 * ( 1 - Real.exp ( - ( 2 * h_val ) ) ) ) / Real.log n from ?_ ) <| by positivity ) ?_;
      · have := hN₂ n hn2 r hr₁ hr₂;
        rw [ le_div_iff₀' hlogn_pos ];
        refine le_trans ?_ this;
        refine' mul_le_mul_of_nonneg_left ( Finset.sum_le_sum_of_subset_of_nonneg _ _ ) hlogn_pos.le;
        · simp +contextual [ mul_comm, Finset.subset_iff ];
          exact fun x hx₁ hx₂ hx₃ hx₄ => ⟨ Nat.lt_of_floor_lt hx₃, fun p hp₁ hp₂ hp₃ => le_trans ( Nat.cast_le.mpr ( hx₄ p hp₁ hp₂ hp₃ ) ) ( Nat.floor_le ( by positivity ) ) ⟩;
        · exact fun _ _ _ => by positivity;
      · field_simp;
        rw [ show ( - ( r * h_val ) : ℝ ) = - ( h_val * 2 ) + ( - ( r * h_val ) + h_val * 2 ) by ring, Real.exp_add ] ; ring_nf ; norm_num;
        norm_num [ ← Real.exp_add ] ; ring_nf;
        linarith [ Real.exp_le_exp.mpr ( show - ( r * h_val ) ≤ r * h_val - h_val * 2 by nlinarith [ show ( r : ℝ ) ≥ 1 by norm_cast ] ) ];
    refine le_trans ?_ ( add_le_add h_sum_bound h_sum_bound_tail );
    norm_num [ Finset.sum_filter ];
    rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_le_sum fun x hx => _ ; split_ifs <;> norm_num ;
    grind;
  refine le_trans ( Nat.cast_le.mpr h_decomp ) ?_;
  convert h_sum_bound.trans _ using 1;
  · norm_num [ Nat.floor_div_natCast ];
  · field_simp;
    nlinarith [ show 1 ≤ HFunc ( r * h_val ) from HFunc_ge_one _ ]

/-! ### Minimality sifting conditions -/

/-- Minimal v at level r has all prime factors ≥ e^{-rh}n^{α-1/2}. -/
lemma v_sifting_condition (n : ℕ) (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha)
    (r : ℕ) (_hr : 1 ≤ r) (_hh : 0 < h_val)
    (a u v : ℕ) (ha : a ∈ Finset.Icc 1 n)
    (hadm : IsAdmissible n alpha a u v)
    (hmin : ∀ u' v' : ℕ, IsAdmissible n alpha a u' v' → v ≤ v')
    (hv_lower : Real.exp (-(↑r * h_val)) * (n : ℝ) ^ (1/2 : ℝ) < (v : ℝ))
    (p : ℕ) (hp : Nat.Prime p) (hpv : p ∣ v) :
    (p : ℝ) ≥ Real.exp (-(↑r * h_val)) * (n : ℝ) ^ (alpha - 1/2) := by
  contrapose! hmin;
  refine' ⟨ p * u, v / p, _, _ ⟩ <;> simp_all +decide [ IsAdmissible ];
  · refine' ⟨ _, _, _, _ ⟩;
    · nlinarith [ Nat.div_mul_cancel hpv ];
    · exact Nat.div_le_self _ _ |> le_trans <| by nlinarith [ hp.two_le ] ;
    · exact le_trans ( div_le_self ( Nat.cast_nonneg _ ) ( mod_cast hp.one_lt.le ) ) hadm.2.2.1;
    · refine' Or.inr _;
      refine' le_trans ( mul_le_mul_of_nonneg_left ( show ( u : ℝ ) ≤ n / v from _ ) ( Nat.cast_nonneg _ ) ) _;
      · rw [ le_div_iff₀ ] <;> norm_cast <;> nlinarith;
      · refine' le_trans ( mul_le_mul_of_nonneg_right hmin.le <| by positivity ) _;
        rw [ mul_div, div_le_iff₀ ];
        · convert mul_le_mul_of_nonneg_left hv_lower.le ( show ( 0 : ℝ ) ≤ n ^ alpha by positivity ) using 1 ; ring_nf;
          rw [ show ( -1 / 2 + alpha : ℝ ) = alpha - 1 / 2 by ring, Real.rpow_sub' ] <;> norm_num ; ring_nf;
          · rw [ mul_assoc, ← Real.rpow_neg ( Nat.cast_nonneg _ ), ← Real.rpow_add_one' ] <;> norm_num;
          · linarith;
        · exact lt_of_le_of_lt ( by positivity ) hv_lower;
  · exact Nat.div_lt_self ( Nat.pos_of_ne_zero ( by aesop_cat ) ) hp.one_lt

/-- Minimal v at level r means u has no prime in (e^{2rh}, e^{(r-1)h}n^{α-1/2}). -/
lemma u_sifting_condition (n : ℕ) (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha)
    (r : ℕ) (_hr : 1 ≤ r) (_hh : 0 < h_val)
    (a u v : ℕ) (ha : a ∈ Finset.Icc 1 n)
    (hadm : IsAdmissible n alpha a u v)
    (hmin : ∀ u' v' : ℕ, IsAdmissible n alpha a u' v' → v ≤ v')
    (hv_lower : Real.exp (-(↑r * h_val)) * (n : ℝ) ^ (1/2 : ℝ) < (v : ℝ))
    (hv_upper : (v : ℝ) ≤ Real.exp (-(↑(r-1 : ℕ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ))
    (hv_half : (v : ℝ) < (n : ℝ) ^ (1/2 : ℝ))
    (p : ℕ) (hp : Nat.Prime p) (hpu : p ∣ u)
    (hp_lower : (p : ℝ) > Real.exp (2 * ↑r * h_val))
    (hp_upper : (p : ℝ) < Real.exp (↑(r-1 : ℕ) * h_val) * (n : ℝ) ^ (alpha - 1/2)) :
    False := by
  -- Show that $u/p < v$ (as natural numbers).
  have hu_div_p_lt_v : u / p < v := by
    have hu_div_p_lt_v : (u / p : ℝ) < Real.exp (-(r * h_val)) * (n : ℝ) ^ (1 / 2 : ℝ) := by
      have hu_div_p_lt_exp : (u : ℝ) < Real.exp (r * h_val) * (n : ℝ) ^ (1 / 2 : ℝ) := by
        have hu_div_p_lt_exp : (u : ℝ) ≤ n / v := by
          rw [ le_div_iff₀ ] <;> norm_cast at *;
          · linarith [ hadm.1, Finset.mem_Icc.mp ha ];
          · exact Nat.cast_pos.mp ( lt_of_le_of_lt ( by positivity ) hv_lower );
        refine lt_of_le_of_lt hu_div_p_lt_exp ?_;
        rw [ div_lt_iff₀ ];
        · convert mul_lt_mul_of_pos_left hv_lower ( show 0 < Real.exp ( r * h_val ) * n ^ ( 1 / 2 : ℝ ) by exact mul_pos ( Real.exp_pos _ ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop_cat ) _ ) ) using 1 ; ring_nf;
          rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, ← Real.exp_add ];
        · exact lt_of_le_of_lt ( by positivity ) hv_lower;
      rw [ div_lt_iff₀ ] <;> norm_num [ Real.exp_neg ] at *;
      · refine lt_of_lt_of_le hu_div_p_lt_exp ?_;
        rw [ inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ ( by positivity ) ];
        convert mul_le_mul_of_nonneg_left hp_lower.le ( show ( 0 : ℝ ) ≤ n ^ ( 1 / 2 : ℝ ) by positivity ) using 1 ; ring_nf;
        rw [ ← Real.exp_nat_mul ] ; ring_nf;
      · exact hp.pos;
    exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( p : ℝ ) ≥ 1 by exact_mod_cast hp.pos, mul_div_cancel₀ ( u : ℝ ) ( show ( p : ℝ ) ≠ 0 by exact_mod_cast hp.ne_zero ) ] ;
  -- Construct (p*v, u/p) as admissible.
  have hadm_new : IsAdmissible n alpha a (p * v) (u / p) := by
    constructor <;> norm_num at *;
    · nlinarith [ Nat.div_mul_cancel hpu, hadm.1 ];
    · refine' ⟨ _, _, _ ⟩;
      · exact le_trans hu_div_p_lt_v.le ( Nat.le_of_lt ( lt_mul_of_one_lt_left ( Nat.pos_of_ne_zero ( by aesop_cat ) ) hp.one_lt ) );
      · refine' le_trans _ ( hadm.2.2.1 );
        exact_mod_cast hu_div_p_lt_v.le;
      · refine' Or.inr _;
        refine' le_trans ( mul_le_mul_of_nonneg_left hv_upper <| Nat.cast_nonneg _ ) _;
        convert mul_le_mul_of_nonneg_right hp_upper.le ( show 0 ≤ Real.exp ( - ( ( r - 1 : ℕ ) * h_val ) ) * ( n : ℝ ) ^ ( 1 / 2 : ℝ ) by positivity ) using 1 ; ring_nf;
        norm_num [ mul_assoc, mul_left_comm, ← Real.exp_add, ← Real.rpow_add' ];
        rw [ ← Real.rpow_add' ] <;> norm_num ; linarith;
  grind +extAll

/-! ### Level bound combining sifted intervals with C4 -/

/-- Combined level bound via C₄ + sifted intervals. -/
lemma level_bound_combined
    (alpha h_val : ℝ) (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hU_strict : UAlpha alpha < 3)
    (hh : 0 < h_val) (ε : ℝ) (hε : 0 < ε) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ N_level : ℕ, ∀ n : ℕ, n ≥ N_level →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → IsProductSidon A →
        ∀ r : ℕ, 1 ≤ r → r ≤ ⌊lambda * Real.log (Real.log n)⌋₊ →
          ∀ B : Finset ℕ, B ⊆ A →
            (∀ a ∈ B, ∃ u v : ℕ,
              IsAdmissible n alpha a u v ∧
              (∀ u' v' : ℕ, IsAdmissible n alpha a u' v' → v ≤ v') ∧
              Real.exp (-(↑r * h_val)) * (n : ℝ) ^ (1/2 : ℝ) < (v : ℝ) ∧
              (v : ℝ) ≤ Real.exp (-(↑(r-1 : ℕ) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) ∧
              (v : ℝ) < (n : ℝ) ^ (1/2 : ℝ)) →
            (B.card : ℝ) ≤
              (OmegaAlpha alpha + ε) * HFunc (↑r * h_val) *
                (Real.exp (↑r * h_val) - Real.exp (-(↑r * h_val))) *
                (n : ℝ) ^ (1/2 : ℝ) / Real.log n +
              (OmegaAlpha alpha + ε) ^ (3/2 : ℝ) *
                (Real.exp h_val - 1) * Real.exp (-(↑r * h_val)) *
                Real.sqrt (HFunc (↑r * h_val) *
                  (Real.exp (↑r * h_val) - Real.exp (-(↑r * h_val)))) *
                (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
  -- Step 1: Obtain N from sifted interval bounds
  obtain ⟨N_v, hN_v⟩ := sifted_interval_v_bound alpha h_val hα1 hα2 hU_strict hh ε hε lambda hlambda
  obtain ⟨N_u, hN_u⟩ := sifted_interval_u_bound alpha h_val hα1 hα2 hU_strict hh ε hε lambda hlambda
  refine ⟨max N_v N_u, fun n hn A hA hSidon r hr1 hr2 B hB hB_mem => ?_⟩
  -- Step 2: Handle empty B trivially
  by_cases hB_empty : B = ∅
  · subst hB_empty; simp; (
    refine' add_nonneg _ _ <;> norm_num;
    · grind +qlia;
    · refine' div_nonneg ( mul_nonneg _ _ ) ( Real.rpow_nonneg ( Real.log_natCast_nonneg _ ) _ );
      · refine' mul_nonneg _ _;
        · refine' mul_nonneg ( mul_nonneg _ _ ) ( Real.exp_nonneg _ ) <;> norm_num;
          · refine' Real.rpow_nonneg _ _;
            refine' add_nonneg _ hε.le;
            exact mul_nonneg ( mul_nonneg zero_le_two ( one_div_nonneg.mpr ( by linarith ) ) ) ( buchstabOmega_pos _ ( by linarith [ show 1 ≤ UAlpha alpha from by rw [ UAlpha ] ; rw [ le_div_iff₀ ] <;> linarith ] ) |> le_of_lt );
          · positivity;
        · positivity;
      · positivity)
  -- Step 3: Choose factorization functions
  have hB_ne : B.Nonempty := Finset.nonempty_of_ne_empty hB_empty
  choose! u_fn v_fn hu_fn using hB_mem
  -- Step 4: Set abbreviations
  set T₁ := (OmegaAlpha alpha + ε) * HFunc (↑r * h_val) *
    (Real.exp (↑r * h_val) - Real.exp (-(↑r * h_val))) *
    (n : ℝ) ^ (1/2 : ℝ) / Real.log n with T₁_def
  set S₁ := (OmegaAlpha alpha + ε) * (Real.exp h_val - 1) *
    Real.exp (-(↑r * h_val)) * (n : ℝ) ^ (1/2 : ℝ) / Real.log n with S₁_def
  -- Steps 5-7: Cardinality bounds
  -- The v-values are in the v-sifted interval (by v_sifting_condition)
  -- The u-values are in the u-sifted interval (by u_sifting_condition)
  -- So |image v_fn| ≤ |sifted_v| ≤ S₁ and |image u_fn| ≤ |sifted_u| ≤ T₁
  have h_s_bound : ((B.image v_fn).card : ℝ) ≤ S₁ := by
    refine' le_trans _ ( hN_v n ( le_trans ( le_max_left _ _ ) hn ) r hr1 hr2 );
    norm_num +zetaDelta at *;
    refine Finset.card_le_card ?_;
    simp +decide [ Finset.subset_iff ];
    intro a ha; specialize hu_fn a ha; rcases hu_fn with ⟨ ⟨ hu₁, hu₂, hu₃, hu₄ ⟩, hu₅, hu₆, hu₇, hu₈ ⟩ ; refine' ⟨ ⟨ _, _ ⟩, _, _, _ ⟩ <;> norm_num at *;
    · exact Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at hu₆; exact absurd hu₆ ( by norm_num; positivity ) );
    · contrapose! hu₈;
      exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast by linarith [ Finset.mem_Icc.mp ( hA ( hB ha ) ) ] ) ( show ( 1 : ℝ ) / 2 ≤ 1 by norm_num ) ) ( by norm_num; linarith [ show ( n : ℝ ) + 1 ≤ v_fn a from mod_cast hu₈ ] );
    · exact hu₆;
    · cases r <;> norm_num at * ; linarith;
    · intro p hp hpv; have := v_sifting_condition n alpha h_val hα1 r hr1 hh a ( u_fn a ) ( v_fn a ) ( hA ( hB ha ) ) ⟨ hu₁, hu₂, hu₃, hu₄ ⟩ hu₅ hu₆ p hp hpv; norm_num at * ;
      exact this
  have h_t_bound : ((B.image u_fn).card : ℝ) ≤ T₁ := by
    refine' le_trans _ ( hN_u n ( le_trans ( le_max_right _ _ ) hn ) r hr1 hr2 );
    refine' mod_cast Finset.card_le_card _;
    intro m hm
    obtain ⟨a, haB, rfl⟩ := Finset.mem_image.mp hm
    have hu_bounds := hu_fn a haB;
    have hu_bounds : u_fn a ≤ n ∧ Real.exp (-(↑r * h_val)) * ↑n ^ (1 / 2 : ℝ) < u_fn a ∧ u_fn a ≤ Real.exp (↑r * h_val) * ↑n ^ (1 / 2 : ℝ) := by
      have hu_bounds : u_fn a * v_fn a ≤ n := by
        have := hu_bounds.1.1;
        exact this ▸ Finset.mem_Icc.mp ( hA ( hB haB ) ) |>.2;
      refine' ⟨ _, _, _ ⟩;
      · by_cases hv : v_fn a = 0;
        · norm_num [ hv ] at *;
          exact absurd ( ‹IsAdmissible n alpha a ( u_fn a ) 0 ∧ Real.exp ( - ( r * h_val ) ) * n ^ ( 1 / 2 : ℝ ) < 0 ∧ _›.2.1 ) ( not_lt_of_ge ( by positivity ) );
        · nlinarith [ Nat.pos_of_ne_zero hv ];
      · have := hu_fn a haB;
        exact this.2.2.1.trans_le ( mod_cast this.1.2.1 );
      · have hu_bounds : (u_fn a : ℝ) * (v_fn a : ℝ) ≤ n := by
          exact_mod_cast hu_bounds;
        have hu_bounds : (u_fn a : ℝ) ≤ n / (Real.exp (-(↑r * h_val)) * ↑n ^ (1 / 2 : ℝ)) := by
          rw [ le_div_iff₀ ] <;> nlinarith [ hu_fn a haB, Real.exp_pos ( - ( r * h_val ) ), Real.rpow_pos_of_pos ( show 0 < ( n : ℝ ) by norm_cast; linarith [ Finset.mem_Icc.mp ( hA ( hB haB ) ) ] ) ( 1 / 2 : ℝ ) ];
        convert hu_bounds using 1 ; norm_num [ Real.exp_neg, Real.exp_mul, Real.exp_log ] ; ring_nf;
        norm_num [ ← Real.sqrt_eq_rpow ];
        grind;
    have := u_sifting_condition n alpha h_val hα1 r hr1 hh a ( u_fn a ) ( v_fn a ) ( Finset.mem_Icc.mpr ⟨ ?_, ?_ ⟩ ) ( hu_fn a haB |>.1 ) ( hu_fn a haB |>.2.1 ) ( hu_fn a haB |>.2.2.1 ) ( hu_fn a haB |>.2.2.2.1 ) ( hu_fn a haB |>.2.2.2.2 );
    · simp +zetaDelta at *;
      exact ⟨ ⟨ Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at hu_bounds; linarith [ show 0 < Real.exp ( - ( r * h_val ) ) * n ^ ( 2⁻¹ : ℝ ) by exact mul_pos ( Real.exp_pos _ ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) _ ) ] ), hu_bounds.1 ⟩, hu_bounds.2.1, hu_bounds.2.2, fun p hp hp' hp'' => by simpa [ Nat.cast_sub hr1 ] using this p hp hp' hp'' ⟩;
    · exact Finset.mem_Icc.mp ( hA ( hB haB ) ) |>.1;
    · exact Finset.mem_Icc.mp ( hA ( hB haB ) ) |>.2
  -- Step 8: C4 bound
  have ht_pos : 0 < (B.image u_fn).card :=
    Finset.card_pos.mpr (Finset.image_nonempty.mpr hB_ne)
  have hC4 : (B.card : ℝ) ≤ (B.image u_fn).card + (B.image v_fn).card *
      Real.sqrt (B.image u_fn).card :=
    sidon_c4_sqrt_bound' A hSidon (fun a ha => by
      have := hA ha; rw [Finset.mem_Icc] at this; exact this.1)
      B hB u_fn v_fn
      (fun a ha => (hu_fn a ha).1.1)
      (fun a ha => (hu_fn a ha).1.2.1)
      _ _ le_rfl le_rfl ht_pos
  -- Step 9: Monotonicity + algebraic identity
  have h_mono : (B.card : ℝ) ≤ T₁ + S₁ * Real.sqrt T₁ :=
    le_trans hC4 (add_le_add h_t_bound
      (mul_le_mul h_s_bound (Real.sqrt_le_sqrt h_t_bound)
        (Real.sqrt_nonneg _) (le_trans (Nat.cast_nonneg _) h_s_bound)))
  -- Step 10: Show S₁ * √T₁ equals the second term
  have h_eq : S₁ * Real.sqrt T₁ =
      (OmegaAlpha alpha + ε) ^ (3/2 : ℝ) *
      (Real.exp h_val - 1) * Real.exp (-(↑r * h_val)) *
      Real.sqrt (HFunc (↑r * h_val) *
        (Real.exp (↑r * h_val) - Real.exp (-(↑r * h_val)))) *
      (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
    rw [ S₁_def, T₁_def ];
    by_cases hn : n = 0 <;> by_cases hl : Real.log n = 0 <;> simp +decide [ hn, hl, Real.sqrt_eq_rpow ];
    rw [ Real.div_rpow ];
    · rw [ Real.mul_rpow, Real.mul_rpow ] <;> try positivity;
      · rw [ Real.mul_rpow, Real.mul_rpow ];
        · rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add' ] <;> norm_num ; ring_nf;
          · rw [ show ( 3 / 4 : ℝ ) = 1 / 2 + 1 / 4 by norm_num, Real.rpow_add' ] <;> norm_num ; ring_nf;
            rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add' ] <;> norm_num ; ring_nf;
            · rw [ ← Real.rpow_mul ( by positivity ) ] ; norm_num ; ring;
            · positivity;
          · exact add_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( one_div_nonneg.mpr ( by linarith ) ) ) ( buchstabOmega_pos _ ( by linarith [ show 1 ≤ UAlpha alpha from by rw [ UAlpha ] ; rw [ le_div_iff₀ ] <;> linarith ] ) |> le_of_lt ) ) hε.le;
        · exact Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
        · exact sub_nonneg_of_le ( Real.exp_le_exp.mpr ( by nlinarith ) );
        · exact add_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( one_div_nonneg.mpr ( by linarith ) ) ) ( buchstabOmega_pos _ ( by linarith [ show 1 ≤ UAlpha alpha from by rw [ UAlpha ] ; rw [ le_div_iff₀ ] <;> linarith ] ) |> le_of_lt ) ) hε.le;
        · exact Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
      · refine mul_nonneg ?_ ?_;
        · exact add_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( one_div_nonneg.mpr ( by linarith ) ) ) ( by unfold buchstabOmega; split_ifs <;> first | positivity | exact div_nonneg ( by linarith [ Real.log_nonneg ( show ( 1 : ℝ ) ≤ UAlpha alpha - 1 by linarith [ show ( 2 : ℝ ) < UAlpha alpha by exact UAlpha_range alpha hα1 hα2 |>.1 ] ) ] ) ( by linarith ) ) ) hε.le;
        · exact Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
      · exact sub_nonneg_of_le ( Real.exp_le_exp.mpr ( by nlinarith ) );
      · refine mul_nonneg ( mul_nonneg ?_ ?_ ) ?_ <;> norm_num;
        · exact add_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( one_div_nonneg.mpr ( by linarith ) ) ) ( by unfold buchstabOmega; split_ifs <;> first | positivity | exact div_nonneg ( by linarith [ Real.log_nonneg ( show ( 1 : ℝ ) ≤ UAlpha alpha - 1 by linarith [ show ( 2 : ℝ ) < UAlpha alpha by exact UAlpha_range alpha hα1 hα2 |>.1 ] ) ] ) ( by linarith ) ) ) hε.le;
        · exact Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
        · positivity;
    · refine' mul_nonneg _ _;
      · refine' mul_nonneg ( mul_nonneg _ _ ) _;
        · exact add_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( one_div_nonneg.mpr ( by linarith ) ) ) ( buchstabOmega_pos _ ( by linarith [ UAlpha_range alpha hα1 hα2 ] ) |> le_of_lt ) ) hε.le;
        · exact Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
        · exact sub_nonneg_of_le ( Real.exp_le_exp.mpr ( by nlinarith ) );
      · positivity;
    · positivity
  linarith

/-! ### Sum of t_r terms is little-o -/

lemma sum_t_r_is_little_o (alpha h_val lambda : ℝ)
    (hα1 : 2/3 ≤ alpha) (hα2 : alpha < 3/4)
    (hh : 0 < h_val) (hlambda : 0 < lambda)
    (_hlh : lambda * h_val > 3)
    (Ω_bound : ℝ) (hΩ : Ω_bound > 0) :
    ∀ δ > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      Ω_bound * (∑ r ∈ Finset.range (⌊lambda * Real.log (Real.log n)⌋₊),
        HFunc (↑(r + 1) * h_val) *
          (Real.exp (↑(r + 1) * h_val) - Real.exp (-(↑(r + 1) * h_val)))) *
        (n : ℝ) ^ (1/2 : ℝ) / Real.log n ≤
      δ * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
  intro δ hδ
  have h_bound : ∃ K_H > 0, ∀ x : ℝ, 0 ≤ x → HFunc x ≤ K_H * (1 + x) := HFunc_growth_bound;
  obtain ⟨K_H, hK_H_pos, hK_H⟩ := h_bound
  have h_sum_bound : ∃ C > 0, ∀ n : ℕ, n ≥ 3 → (∑ r ∈ Finset.range ⌊lambda * Real.log (Real.log n)⌋₊, HFunc ((r + 1) * h_val) * (Real.exp ((r + 1) * h_val) - Real.exp (-(r + 1) * h_val))) ≤ C * (Real.log n) * Real.exp (lambda * h_val * Real.log (Real.log n)) := by
    have h_sum_bound : ∃ C > 0, ∀ n : ℕ, n ≥ 3 → (∑ r ∈ Finset.range ⌊lambda * Real.log (Real.log n)⌋₊, (1 + (r + 1) * h_val) * (Real.exp ((r + 1) * h_val))) ≤ C * (Real.log n) * Real.exp (lambda * h_val * Real.log (Real.log n)) := by
      have h_sum_bound : ∃ C > 0, ∀ n : ℕ, n ≥ 3 → (∑ r ∈ Finset.range ⌊lambda * Real.log (Real.log n)⌋₊, (1 + (r + 1) * h_val)) ≤ C * (Real.log n) := by
        have h_sum_bound : ∃ C > 0, ∀ n : ℕ, n ≥ 3 → (∑ r ∈ Finset.range ⌊lambda * Real.log (Real.log n)⌋₊, (1 + (r + 1) * h_val)) ≤ C * (Real.log (Real.log n)) ^ 2 := by
          have h_sum_bound : ∃ C > 0, ∀ n : ℕ, n ≥ 3 → (∑ r ∈ Finset.range ⌊lambda * Real.log (Real.log n)⌋₊, (r + 1)) ≤ C * (Real.log (Real.log n)) ^ 2 := by
            have h_sum_bound : ∃ C > 0, ∀ n : ℕ, n ≥ 3 → (∑ r ∈ Finset.range ⌊lambda * Real.log (Real.log n)⌋₊, (r + 1)) ≤ C * (⌊lambda * Real.log (Real.log n)⌋₊) ^ 2 := by
              use 1;
              exact ⟨ by norm_num, fun n hn => by induction' ⌊lambda * Real.log ( Real.log n ) ⌋₊ with k hk <;> norm_num [ Finset.sum_range_succ ] at * ; nlinarith ⟩;
            obtain ⟨ C, hC₀, hC ⟩ := h_sum_bound;
            use C * lambda^2 + 1;
            refine' ⟨ by positivity, fun n hn => le_trans ( Nat.cast_le.mpr ( hC n hn ) ) _ ⟩;
            norm_num [ add_mul, mul_assoc ];
            exact le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_left ( by nlinarith [ Nat.floor_le ( show 0 ≤ lambda * Real.log ( Real.log n ) by exact mul_nonneg hlambda.le ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ) ) ), Nat.lt_floor_add_one ( lambda * Real.log ( Real.log n ) ) ] ) ( Nat.cast_nonneg _ ) ) ( sq_nonneg _ );
          obtain ⟨ C, hC₀, hC ⟩ := h_sum_bound; use C * ( 1 + h_val ) ; refine' ⟨ mul_pos hC₀ ( by positivity ), fun n hn => _ ⟩ ; simp_all +decide [ Finset.sum_add_distrib ] ;
          simp_all +decide [ Finset.sum_add_distrib, ← Finset.sum_mul _ _ _ ];
          nlinarith [ hC n hn, show ( ⌊lambda * Real.log ( Real.log n ) ⌋₊ : ℝ ) ≤ C * Real.log ( Real.log n ) ^ 2 by nlinarith [ hC n hn, show ( 0 : ℝ ) ≤ ∑ x ∈ Finset.range ⌊lambda * Real.log ( Real.log n ) ⌋₊, ( x : ℝ ) by exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ] ];
        have h_log_bound : ∃ C > 0, ∀ n : ℕ, n ≥ 3 → (Real.log (Real.log n)) ^ 2 ≤ C * Real.log n := by
          have h_log_bound : ∃ C > 0, ∀ x : ℝ, 1 ≤ x → (Real.log x) ^ 2 ≤ C * x := by
            use 4;
            norm_num +zetaDelta at *;
            intro x hx; have := Real.log_le_sub_one_of_pos ( by positivity : 0 < Real.sqrt x ) ; rw [ Real.log_sqrt ( by positivity ) ] at this; nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( by positivity : 0 ≤ x ), Real.log_nonneg hx ] ;
          exact ⟨ h_log_bound.choose, h_log_bound.choose_spec.1, fun n hn => h_log_bound.choose_spec.2 _ <| Real.le_log_iff_exp_le ( by positivity ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ⟩;
        obtain ⟨ C₁, hC₁_pos, hC₁ ⟩ := h_sum_bound; obtain ⟨ C₂, hC₂_pos, hC₂ ⟩ := h_log_bound; exact ⟨ C₁ * C₂, mul_pos hC₁_pos hC₂_pos, fun n hn => le_trans ( hC₁ n hn ) ( by nlinarith [ hC₂ n hn, show 0 ≤ C₁ by positivity, show 0 ≤ C₂ by positivity ] ) ⟩ ;
      obtain ⟨ C, hC₀, hC ⟩ := h_sum_bound;
      refine' ⟨ C, hC₀, fun n hn => _ ⟩;
      refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| show ( i + 1 : ℝ ) * h_val ≤ lambda * h_val * Real.log ( Real.log n ) from _ ) <| by positivity ) _;
      · nlinarith [ Nat.floor_le ( show 0 ≤ lambda * Real.log ( Real.log n ) by exact mul_nonneg hlambda.le ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ) ) ), show ( i : ℝ ) + 1 ≤ ⌊lambda * Real.log ( Real.log n ) ⌋₊ by exact_mod_cast Finset.mem_range.mp hi ];
      · simpa only [ ← Finset.sum_mul _ _ _ ] using mul_le_mul_of_nonneg_right ( hC n hn ) ( Real.exp_nonneg _ );
    obtain ⟨ C, hC_pos, hC ⟩ := h_sum_bound;
    refine' ⟨ C * K_H, mul_pos hC_pos hK_H_pos, fun n hn => _ ⟩;
    refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( hK_H _ <| by positivity ) <| sub_nonneg.mpr <| Real.exp_le_exp.mpr <| by nlinarith ) _;
    refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( sub_le_self _ <| by positivity ) <| by positivity ) _;
    simpa only [ mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] using mul_le_mul_of_nonneg_left ( hC n hn ) hK_H_pos.le;
  obtain ⟨C, hC_pos, hC⟩ := h_sum_bound
  have h_lim : Filter.Tendsto (fun n : ℕ => (Ω_bound * C * Real.log n * Real.exp (lambda * h_val * Real.log (Real.log n)) * (n : ℝ) ^ (1 / 2 : ℝ)) / (Real.log n) / ((n : ℝ) ^ (3 / 4 : ℝ) / (Real.log n) ^ (3 / 2 : ℝ))) Filter.atTop (nhds 0) := by
    suffices h_simplify : Filter.Tendsto (fun n : ℕ => (Ω_bound * C * (Real.log n) ^ (3 / 2 : ℝ) * (Real.log n) ^ (lambda * h_val) * (n : ℝ) ^ (-1 / 4 : ℝ))) Filter.atTop (nhds 0) by
      refine h_simplify.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
      norm_num [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr <| pos_of_gt hn ), Real.exp_neg, Real.exp_log ( Nat.cast_pos.mpr <| pos_of_gt hn ) ] ; ring_nf;
      norm_num [ Real.rpow_def_of_pos ( Real.log_pos <| Nat.one_lt_cast.mpr hn ), mul_assoc, mul_comm, mul_left_comm, ← Real.exp_add, ← Real.exp_neg ] ; ring_nf;
      exact Or.inl <| Or.inl <| by rw [ mul_inv_cancel₀ <| ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hn, one_mul ] ;
    have h_factor : Filter.Tendsto (fun n : ℕ => (Real.log n) ^ (3 / 2 + lambda * h_val) / (n : ℝ) ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) := by
      suffices h_log : Filter.Tendsto (fun y : ℝ => y ^ (3 / 2 + lambda * h_val) / Real.exp (y / 4)) Filter.atTop (nhds 0) by
        have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
      suffices h_z : Filter.Tendsto (fun z : ℝ => (4 * z) ^ (3 / 2 + lambda * h_val) / Real.exp z) Filter.atTop (nhds 0) by
        convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by positivity : 0 < ( 4 : ℝ ) ⁻¹ ) ) using 2 ; norm_num ; ring_nf;
      suffices h_factor : Filter.Tendsto (fun z : ℝ => z ^ (3 / 2 + lambda * h_val) / Real.exp z) Filter.atTop (nhds 0) by
        have := h_factor.const_mul ( 4 ^ ( 3 / 2 + lambda * h_val ) );
        simpa using this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring );
      have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero;
      specialize this ⌈3 / 2 + lambda * h_val⌉₊;
      refine' squeeze_zero_norm' _ this;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ Real.exp_neg ] ; exact mul_le_mul_of_nonneg_right ( by exact_mod_cast Real.rpow_le_rpow_of_exponent_le hx.le <| Nat.le_ceil _ ) <| by positivity;
    convert h_factor.const_mul ( Ω_bound * C ) using 2 <;> ring_nf;
    rw [ Real.rpow_add' ] <;> norm_num ; ring_nf;
    · norm_num [ Real.rpow_neg ];
    · positivity;
    · positivity;
  have := h_lim.eventually ( gt_mem_nhds <| show 0 < δ by positivity );
  obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp this;
  refine' ⟨ N + 3, fun n hn => _ ⟩ ; specialize hN n ( by linarith ) ; rw [ div_lt_iff₀ ] at hN <;> norm_num at *;
  · refine le_trans ?_ ( hN.le.trans ?_ ) <;> ring_nf <;> norm_num;
    convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( hC n ( by linarith ) ) hΩ.le ) ( show 0 ≤ ( n : ℝ ) ^ ( 1 / 2 : ℝ ) * ( Real.log n ) ⁻¹ by positivity ) using 1 <;> ring_nf;
    simpa only [ mul_sub, Finset.sum_sub_distrib ] using by ring;
  · exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( Real.rpow_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) _ )

end

end SiftedIntervals

section Main

/-! Main theorem: |A| ≤ π(n) + c·n^{3/4}/(log n)^{3/2} for c > C_*. Corollary: C_* < 13.1. -/

open Finset BigOperators Real

noncomputable section


/-! ### Sidon C4 bound -/

/-- C₄ bound for a Sidon subset with admissible factorizations. -/
lemma sidon_c4_bound (A : Finset ℕ) (hSidon : IsProductSidon A) (hA_pos : ∀ a ∈ A, 0 < a)
    (A₁ : Finset ℕ) (hA₁ : A₁ ⊆ A) (u_fn v_fn : ℕ → ℕ)
    (hfact : ∀ a ∈ A₁, a = u_fn a * v_fn a)
    (s t : ℕ) (hs : (A₁.image v_fn).card ≤ s) (ht : (A₁.image u_fn).card ≤ t)
    (ht0 : 0 < t) (hst : s * s ≤ t) :
    A₁.card ≤ t + s * s := by
  exact c4_free_pair_bound A₁ u_fn v_fn
    (fun a ha b hb huf hvf => by rw [hfact a ha, huf, hvf, ← hfact b hb])
    (fun v₁ v₂ u₁' u₂' hv hu h1 h2 h3 h4 => by
      obtain ⟨a1, ha1, hg1, hf1⟩ := h1
      obtain ⟨a2, ha2, hg2, hf2⟩ := h2
      obtain ⟨a3, ha3, hg3, hf3⟩ := h3
      obtain ⟨a4, ha4, hg4, hf4⟩ := h4
      have hSidon' := hSidon.subset hA₁
      have hne0 : ∀ a ∈ A₁, a ≠ 0 := fun a ha =>
        Nat.pos_iff_ne_zero.mp (hA_pos a (hA₁ ha))
      exact sidon_no_K22 A₁ hSidon' hne0 v₁ u₁' v₂ u₂' hv hu
        (by rw [show v₁ * u₁' = a1 from by rw [hfact a1 ha1, hf1, hg1, mul_comm]]; exact ha1)
        (by rw [show v₁ * u₂' = a2 from by rw [hfact a2 ha2, hf2, hg2, mul_comm]]; exact ha2)
        (by rw [show v₂ * u₁' = a3 from by rw [hfact a3 ha3, hf3, hg3, mul_comm]]; exact ha3)
        (by rw [show v₂ * u₂' = a4 from by rw [hfact a4 ha4, hf4, hg4, mul_comm]]; exact ha4))
    s t hs ht ht0 hst

/-! ### Small second factors bound -/

/-- Small second factors: |A₁| ≤ π(n) + O(n^α). -/
lemma small_second_factors_bound (alpha : ℝ)
    (halpha1 : 2/3 ≤ alpha) (_halpha2 : alpha < 3/4) :
    ∃ C₁ > 0, ∃ N₁ : ℕ, ∀ n : ℕ, n ≥ N₁ →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → IsProductSidon A →
        ∀ A₁ : Finset ℕ, A₁ ⊆ A →
          (∀ a ∈ A₁, ∃ u v : ℕ, IsAdmissible n alpha a u v ∧ (v : ℝ) ≤ (n : ℝ) ^ (1 - alpha)) →
            (A₁.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + C₁ * (n : ℝ) ^ alpha := by
  refine' ⟨ 2, by norm_num, 8, fun n hn A hA hSidon A₁ hA₁ hA₂ => _ ⟩;
  -- Use Classical.choose to pick, for each a ∈ A₁, an admissible pair.
  obtain ⟨u_fn, v_fn, hfact⟩ : ∃ u_fn v_fn : ℕ → ℕ, (∀ a ∈ A₁, IsAdmissible n alpha a (u_fn a) (v_fn a)) ∧ (∀ a ∈ A₁, (v_fn a : ℝ) ≤ (n : ℝ) ^ (1 - alpha)) := by
    choose! u v huv hv using hA₂;
    exact ⟨ u, v, huv, hv ⟩;
  -- Apply the sidon_c4_bound lemma with s = ⌊n^(1-α)⌋ and t = Nat.primeCounting n + ⌊n^α⌋.
  have h_bound : A₁.card ≤ (Nat.primeCounting n + Nat.floor ((n : ℝ) ^ alpha)) + (Nat.floor ((n : ℝ) ^ (1 - alpha))) ^ 2 := by
    have h_bound : (A₁.image u_fn).card ≤ Nat.primeCounting n + Nat.floor ((n : ℝ) ^ alpha) := by
      have h_image_u : (A₁.image u_fn).card ≤ (Finset.filter Nat.Prime (Finset.Icc 1 n)).card + (Finset.Icc 1 (Nat.floor ((n : ℝ) ^ alpha))).card := by
        have h_image_u_subset : A₁.image u_fn ⊆ (Finset.filter Nat.Prime (Finset.Icc 1 n)) ∪ (Finset.Icc 1 (Nat.floor ((n : ℝ) ^ alpha))) := by
          intro x hx
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
          have h_u_prime_or_le : Nat.Prime (u_fn a) ∨ u_fn a ≤ Nat.floor ((n : ℝ) ^ alpha) := by
            have := hfact.1 a ha;
            exact this.2.2.2.imp id fun h => Nat.le_floor <| mod_cast h
          have h_u_le_n : u_fn a ≤ n := by
            have := hfact.1 a ha;
            exact le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp ( hA ( hA₁ ha ) ) ] ) ( dvd_of_mul_right_eq _ this.1.symm ) ) ( by linarith [ Finset.mem_Icc.mp ( hA ( hA₁ ha ) ) ] )
          have h_u_ge_1 : 1 ≤ u_fn a := by
            have := hfact.1 a ha; obtain ⟨ h₁, h₂, h₃, h₄ ⟩ := this; nlinarith [ Finset.mem_Icc.mp ( hA ( hA₁ ha ) ) ] ;
          exact (by
          grind)
        exact le_trans ( Finset.card_le_card h_image_u_subset ) ( Finset.card_union_le _ _ );
      simp_all +decide [ Nat.primeCounting ];
      rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
      convert h_image_u using 2 ; rw [ Finset.range_eq_Ico ] ; rfl;
    have h_bound_v : (A₁.image v_fn).card ≤ Nat.floor ((n : ℝ) ^ (1 - alpha)) := by
      have h_bound_v : ∀ a ∈ A₁, v_fn a ≤ Nat.floor ((n : ℝ) ^ (1 - alpha)) := by
        exact fun a ha => Nat.le_floor <| hfact.2 a ha;
      have h_bound_v : (A₁.image v_fn) ⊆ Finset.Icc 1 (Nat.floor ((n : ℝ) ^ (1 - alpha))) := by
        intros x hx
        obtain ⟨a, ha₁, ha₂⟩ := Finset.mem_image.mp hx
        have ha₃ : 1 ≤ v_fn a := by
          have := hA ( hA₁ ha₁ ) ; norm_num at this ; nlinarith [ this.1, this.2, this.1, this.2, hfact.1 a ha₁ |>.1.symm ] ;
        have ha₄ : v_fn a ≤ Nat.floor ((n : ℝ) ^ (1 - alpha)) := by
          exact h_bound_v a ha₁
        aesop;
      exact le_trans ( Finset.card_le_card h_bound_v ) ( by simp );
    have := @sidon_c4_bound A hSidon (fun a ha => by
      linarith [ Finset.mem_Icc.mp ( hA ha ) ]) A₁ hA₁ u_fn v_fn (fun a ha => by
      exact hfact.1 a ha |>.1) (Nat.floor ((n : ℝ) ^ (1 - alpha))) (Nat.primeCounting n + Nat.floor ((n : ℝ) ^ alpha)) (by
    exact h_bound_v) (by
    exact h_bound) (by
    exact add_pos_of_pos_of_nonneg ( Nat.pos_of_ne_zero ( by norm_num; linarith ) ) ( Nat.zero_le _ )) (by
    have h_floor_sq : (Nat.floor ((n : ℝ) ^ (1 - alpha))) ^ 2 ≤ (n : ℝ) ^ (2 * (1 - alpha)) := by
      convert pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.floor_le ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) 2 using 1 ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
    have h_floor_sq_le : (n : ℝ) ^ (2 * (1 - alpha)) ≤ (n : ℝ) ^ alpha := by
      exact Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( by linarith );
    exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.lt_floor_add_one ( ( n : ℝ ) ^ alpha ) ] ;);
    grobner;
  -- Since $n^{2(1-\alpha)} \leq n^\alpha$ for $\alpha \geq 2/3$, we have $(\lfloor n^{1-\alpha} \rfloor)^2 \leq n^\alpha$.
  have h_floor_sq : (Nat.floor ((n : ℝ) ^ (1 - alpha))) ^ 2 ≤ (n : ℝ) ^ alpha := by
    have h_s_sq_le_n_alpha : (Nat.floor ((n : ℝ) ^ (1 - alpha))) ^ 2 ≤ (n : ℝ) ^ (2 * (1 - alpha)) := by
      rw [ mul_comm, Real.rpow_mul ] <;> norm_num;
      exact pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.floor_le ( by positivity ) ) _;
    exact h_s_sq_le_n_alpha.trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( by linarith ) );
  refine le_trans ( Nat.cast_le.mpr h_bound ) ?_;
  norm_num; linarith [ Nat.floor_le ( Real.rpow_nonneg ( Nat.cast_nonneg n ) alpha ) ] ;

/-! ### Middle second factors bound -/

/-- Crude bound: |A₂| ≤ C(n^α + n^{3/4}e^{-Lh/2}). -/
lemma middle_factors_crude_bound (alpha h_val lambda : ℝ)
    (halpha1 : 2/3 ≤ alpha) (halpha2 : alpha < 3/4) :
    ∃ C_mid > 0, ∃ N_mid : ℕ, ∀ n : ℕ, n ≥ N_mid →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → IsProductSidon A →
        ∀ A₂ : Finset ℕ, A₂ ⊆ A →
          (∀ a ∈ A₂, ∃ u v : ℕ, IsAdmissible n alpha a u v ∧
            (n : ℝ) ^ (1 - alpha) < (v : ℝ) ∧
            (v : ℝ) ≤ Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ)) →
          (A₂.card : ℝ) ≤ C_mid * ((n : ℝ) ^ alpha +
            (n : ℝ) ^ (3/4 : ℝ) * Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val / 2)) := by
  refine' ⟨ 8, by norm_num, 100, fun n hn A hA hSidon A₂ hA₂ h => _ ⟩;
  choose! u v hu hv using h;
  -- Apply the sidon_dyadic_bound lemma with the chosen $u$ and $v$ functions.
  have h_bound : (A₂.card : ℝ) ≤ 4 * (n : ℝ) / (Nat.floor ((n : ℝ) ^ (1 - alpha))) + 4 * Real.sqrt ((n : ℝ) * (Nat.floor ((Real.exp (-⌊lambda * Real.log (Real.log n)⌋₊ * h_val)) * (n : ℝ) ^ (1 / 2 : ℝ)))) := by
    apply sidon_dyadic_bound n (by
    linarith) A hSidon (by
    exact fun a ha => Finset.mem_Icc.mp ( hA ha ) |>.1) A₂ hA₂ u v (by
    exact fun a ha => hu a ha |>.1) (by
    exact fun a ha => hu a ha |>.2.1) (by
    exact fun a ha => Nat.cast_pos.mp ( lt_trans ( by positivity ) ( hv a ha |>.1 ) )) (Nat.floor ((n : ℝ) ^ (1 - alpha))) (Nat.floor ((Real.exp (-⌊lambda * Real.log (Real.log n)⌋₊ * h_val)) * (n : ℝ) ^ (1 / 2 : ℝ))) (by
    exact Nat.floor_pos.mpr ( Real.one_le_rpow ( by norm_cast; linarith ) ( by linarith ) )) (by
    exact fun a ha => Nat.succ_le_of_lt ( Nat.floor_lt ( by positivity ) |>.2 ( hv a ha |>.1 ) )) (by
    exact fun a ha => Nat.le_floor <| hv a ha |>.2) (by
    exact fun a ha => by have := hu a ha; exact this.1.symm ▸ Finset.mem_Icc.mp ( hA ( hA₂ ha ) ) |>.2;);
  -- Bound the first term: $4 * n / \lfloor n^{1-\alpha} \rfloor \leq 8 * n^\alpha$.
  have h_first_term : 4 * (n : ℝ) / (Nat.floor ((n : ℝ) ^ (1 - alpha))) ≤ 8 * (n : ℝ) ^ alpha := by
    have h_floor : (Nat.floor ((n : ℝ) ^ (1 - alpha))) ≥ (n : ℝ) ^ (1 - alpha) / 2 := by
      have h_floor : (Nat.floor ((n : ℝ) ^ (1 - alpha))) ≥ 1 := by
        exact Nat.floor_pos.mpr ( Real.one_le_rpow ( by norm_cast; linarith ) ( by linarith ) );
      nlinarith only [ Nat.lt_floor_add_one ( ( n : ℝ ) ^ ( 1 - alpha ) ), show ( ⌊ ( n : ℝ ) ^ ( 1 - alpha ) ⌋₊ : ℝ ) ≥ 1 by exact_mod_cast h_floor, show ( n : ℝ ) ^ ( 1 - alpha ) ≥ 1 by exact Real.one_le_rpow ( by norm_cast; linarith ) ( by linarith ) ];
    rw [ div_le_iff₀ ];
    · rw [ show ( n : ℝ ) ^ alpha = ( n : ℝ ) / ( n ^ ( 1 - alpha ) ) by rw [ ← Real.rpow_one_sub' ] <;> norm_num ; linarith ] ; nlinarith [ show ( n : ℝ ) ≥ 100 by norm_cast, Real.rpow_pos_of_pos ( by positivity : 0 < ( n : ℝ ) ) ( 1 - alpha ), mul_div_cancel₀ ( ( n : ℝ ) : ℝ ) ( ne_of_gt ( Real.rpow_pos_of_pos ( by positivity : 0 < ( n : ℝ ) ) ( 1 - alpha ) ) ) ];
    · exact lt_of_lt_of_le ( by positivity ) h_floor;
  -- Bound the second term: $4 * \sqrt{n * \lfloor e^{-Lh} * n^{1/2} \rfloor} \leq 4 * e^{-Lh/2} * n^{3/4}$.
  have h_second_term : 4 * Real.sqrt ((n : ℝ) * (Nat.floor ((Real.exp (-⌊lambda * Real.log (Real.log n)⌋₊ * h_val)) * (n : ℝ) ^ (1 / 2 : ℝ)))) ≤ 4 * (Real.exp (-⌊lambda * Real.log (Real.log n)⌋₊ * h_val / 2)) * (n : ℝ) ^ (3 / 4 : ℝ) := by
    have h_second_term : Real.sqrt ((n : ℝ) * (Real.exp (-⌊lambda * Real.log (Real.log n)⌋₊ * h_val)) * (n : ℝ) ^ (1 / 2 : ℝ)) ≤ (Real.exp (-⌊lambda * Real.log (Real.log n)⌋₊ * h_val / 2)) * (n : ℝ) ^ (3 / 4 : ℝ) := by
      rw [ Real.sqrt_le_iff ] ; ring_nf ; norm_num;
      norm_num [ sq, ← Real.exp_add, ← Real.rpow_add ( by positivity : 0 < ( n : ℝ ) ) ] ; ring_nf ; norm_num;
      exact ⟨ by positivity, by rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ( by positivity ), Real.rpow_one ] ; ring_nf; norm_num ⟩;
    rw [ mul_assoc ];
    gcongr;
    refine le_trans ?_ h_second_term;
    exact Real.sqrt_le_sqrt <| by rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( Nat.floor_le <| by positivity ) <| by positivity;
  linarith [ show ( n : ℝ ) ^ ( 3 / 4 : ℝ ) * Real.exp ( -⌊lambda * Real.log ( Real.log n ) ⌋₊ * h_val / 2 ) ≥ 0 by positivity ]

/-- The crude bound is o(n^{3/4}/(log n)^{3/2}). -/
lemma middle_crude_is_little_o (alpha h_val lambda : ℝ)
    (halpha1 : 2/3 ≤ alpha) (halpha2 : alpha < 3/4)
    (hh : 0 < h_val) (_hlambda : 0 < lambda) (hlh : lambda * h_val > 3)
    (C_mid : ℝ) (hC_mid : C_mid > 0) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      C_mid * ((n : ℝ) ^ alpha + (n : ℝ) ^ (3/4 : ℝ) *
        Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val / 2)) ≤
      ε * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
  -- hlambda used below in hlambda.le
  -- The second term is dominated by $n^{3/4} \cdot e^{-Lh/2}$, where $L \geq \lambda \cdot \log(\log n) - 1$.
  have h_term2_dominate : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, C_mid * (n : ℝ) ^ (3 / 4 : ℝ) * Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val / 2) ≤ ε * (n : ℝ) ^ (3 / 4 : ℝ) / (Real.log n) ^ (3 / 2 : ℝ) := by
    -- We'll use that $e^{-Lh/2} \leq e^{h/2} \cdot (\log n)^{-\lambda h/2}$.
    have h_exp_bound : ∀ n : ℕ, n ≥ 3 → Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val / 2) ≤ Real.exp (h_val / 2) * (Real.log n) ^ (-lambda * h_val / 2 : ℝ) := by
      intro n hn
      have h_exp_bound : Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val / 2) ≤ Real.exp (h_val / 2) * Real.exp (-lambda * h_val / 2 * Real.log (Real.log n)) := by
        rw [ ← Real.exp_add ];
        exact Real.exp_le_exp.mpr ( by nlinarith [ Nat.floor_le ( show 0 ≤ lambda * Real.log ( Real.log n ) by exact mul_nonneg _hlambda.le ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ) ) ), Nat.lt_floor_add_one ( lambda * Real.log ( Real.log n ) ) ] );
      convert h_exp_bound using 2 ; rw [ Real.rpow_def_of_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) ] ; ring_nf;
    -- We'll use that $(\log n)^{-\lambda h/2} = o((\log n)^{-3/2})$ since $\lambda h/2 > 3/2$.
    have h_log_bound : Filter.Tendsto (fun n : ℕ => (Real.log n) ^ (-lambda * h_val / 2 : ℝ) * (Real.log n) ^ (3 / 2 : ℝ)) Filter.atTop (nhds 0) := by
      have h_log_bound : Filter.Tendsto (fun n : ℕ => (Real.log n) ^ (-lambda * h_val / 2 + 3 / 2 : ℝ)) Filter.atTop (nhds 0) := by
        simpa using tendsto_rpow_neg_atTop ( show 0 < - ( -lambda * h_val / 2 + 3 / 2 ) by linarith ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop;
      refine h_log_bound.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ ← Real.rpow_add ( Real.log_pos <| Nat.one_lt_cast.mpr hn ) ] );
    intro ε hε_pos
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (Real.log n) ^ (-lambda * h_val / 2 : ℝ) * (Real.log n) ^ (3 / 2 : ℝ) ≤ ε / (C_mid * Real.exp (h_val / 2)) := by
      simpa using h_log_bound.eventually ( ge_mem_nhds <| by positivity );
    refine' ⟨ N + 3, fun n hn => _ ⟩ ; specialize hN n ( by linarith ) ; specialize h_exp_bound n ( by linarith ) ; rw [ le_div_iff₀ ] at * <;> norm_num at *;
    · refine le_trans ?_ ( mul_le_mul_of_nonneg_right hN <| by positivity );
      convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_exp_bound <| show 0 ≤ C_mid * ( n : ℝ ) ^ ( 3 / 4 : ℝ ) by positivity ) <| show 0 ≤ Real.log n ^ ( 3 / 2 : ℝ ) by exact Real.rpow_nonneg ( Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ) _ using 1 ; ring;
    · positivity;
    · exact Real.rpow_pos_of_pos ( Real.log_pos ( by norm_cast; linarith ) ) _;
  -- The first term is dominated by $n^\alpha$, which is $o(n^{3/4}/(\log n)^{3/2})$ since $\alpha < 3/4$.
  have h_term1_dominate : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, C_mid * (n : ℝ) ^ alpha ≤ ε * (n : ℝ) ^ (3 / 4 : ℝ) / (Real.log n) ^ (3 / 2 : ℝ) := by
    intros ε hε_pos
    have h_term1_dominate_aux : Filter.Tendsto (fun n : ℕ => C_mid * (n : ℝ) ^ alpha / ((n : ℝ) ^ (3 / 4 : ℝ) / (Real.log n) ^ (3 / 2 : ℝ))) Filter.atTop (nhds 0) := by
      -- Simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun n : ℕ => C_mid * (Real.log n) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (alpha - 3 / 4 : ℝ)) Filter.atTop (nhds 0) by
        refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_sub ( by positivity ) ] ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hn.ne' ] );
      -- We can use the fact that $(\log n)^{3/2} / n^{3/4 - \alpha}$ tends to $0$ as $n$ tends to infinity.
      have h_log_div_n : Filter.Tendsto (fun n : ℕ => (Real.log n) ^ (3 / 2 : ℝ) / (n : ℝ) ^ (3 / 4 - alpha)) Filter.atTop (nhds 0) := by
        -- Let $y = \log n$, therefore the expression becomes $\frac{y^{3/2}}{e^{(3/4 - \alpha)y}}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => y ^ (3 / 2 : ℝ) / Real.exp ((3 / 4 - alpha) * y)) Filter.atTop (nhds 0) by
          have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
        -- Let $z = (3/4 - \alpha)y$, therefore the expression becomes $\frac{z^{3/2}}{e^z}$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => z ^ (3 / 2 : ℝ) / Real.exp z) Filter.atTop (nhds 0) by
          have h_subst : Filter.Tendsto (fun y : ℝ => ((3 / 4 - alpha) * y) ^ (3 / 2 : ℝ) / Real.exp ((3 / 4 - alpha) * y)) Filter.atTop (nhds 0) := by
            exact h_z.comp <| Filter.tendsto_id.const_mul_atTop <| by linarith;
          have h_subst : Filter.Tendsto (fun y : ℝ => ((3 / 4 - alpha) ^ (3 / 2 : ℝ)) * (y ^ (3 / 2 : ℝ) / Real.exp ((3 / 4 - alpha) * y))) Filter.atTop (nhds 0) := by
            refine h_subst.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ Real.mul_rpow ( by linarith ) ( by linarith ) ] ; ring );
          convert h_subst.div_const ( ( 3 / 4 - alpha ) ^ ( 3 / 2 : ℝ ) ) using 2 <;> norm_num [ mul_div_cancel_left₀, ne_of_gt ( Real.rpow_pos_of_pos ( sub_pos.mpr halpha2 ) _ ) ];
        have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
        refine' squeeze_zero_norm' _ this;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ Real.exp_neg ] ; exact mul_le_mul_of_nonneg_right ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le hx.le <| show ( 3 : ℝ ) / 2 ≤ 2 by norm_num ) <| by norm_num ) <| by positivity;
      convert h_log_div_n.const_mul C_mid using 2 <;> ring_nf;
      rw [ ← Real.rpow_neg ( Nat.cast_nonneg _ ) ] ; ring_nf;
    have := h_term1_dominate_aux.eventually ( gt_mem_nhds <| show 0 < ε by positivity );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; exact ⟨ N + 2, fun n hn => by have := hN n ( by linarith ) ; rw [ div_lt_iff₀ ( div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) <| Real.rpow_pos_of_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) _ ) ] at this; ring_nf at *; linarith ⟩ ;
  intro ε hε; obtain ⟨ N₁, hN₁ ⟩ := h_term1_dominate ( ε / 2 ) ( half_pos hε ) ; obtain ⟨ N₂, hN₂ ⟩ := h_term2_dominate ( ε / 2 ) ( half_pos hε ) ; exact ⟨ Max.max N₁ N₂, fun n hn => by have := hN₁ n ( le_trans ( le_max_left _ _ ) hn ) ; have := hN₂ n ( le_trans ( le_max_right _ _ ) hn ) ; ring_nf at *; linarith ⟩ ;

/-- Middle second factors: |A₂| = o(n^{3/4}/(log n)^{3/2}). -/
lemma middle_second_factors_bound (alpha : ℝ) (h_val lambda : ℝ)
    (halpha1 : 2/3 ≤ alpha) (halpha2 : alpha < 3/4)
    (hh : 0 < h_val) (hlambda : 0 < lambda) (hlh : lambda * h_val > 3) :
    ∀ ε > 0, ∃ N₂ : ℕ, ∀ n : ℕ, n ≥ N₂ →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → IsProductSidon A →
        ∀ A₂ : Finset ℕ, A₂ ⊆ A →
          (∀ a ∈ A₂, ∃ u v : ℕ, IsAdmissible n alpha a u v ∧
            (n : ℝ) ^ (1 - alpha) < (v : ℝ) ∧
            (v : ℝ) ≤ Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ)) →
          (A₂.card : ℝ) ≤ ε * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
  intro ε hε
  obtain ⟨C_mid, hC_pos, N_mid, hN_mid⟩ := middle_factors_crude_bound alpha h_val lambda halpha1 halpha2
  obtain ⟨N_o, hN_o⟩ := middle_crude_is_little_o alpha h_val lambda halpha1 halpha2 hh hlambda hlh C_mid hC_pos ε hε
  exact ⟨max N_mid N_o, fun n hn A hA hSidon A₂ hA₂ hA₂' =>
    le_trans (hN_mid n (le_of_max_le_left hn) A hA hSidon A₂ hA₂ hA₂')
      (hN_o n (le_of_max_le_right hn))⟩

/-! ### Large second factors bound -/

/-- Parameter choice: find α, h, λ, ε with the Riemann sum coefficient < c. -/
lemma param_choice (c : ℝ) (hc : c > Cstar) :
    ∃ alpha h_val lambda ε₀ : ℝ,
      2/3 ≤ alpha ∧ 2/3 < alpha ∧ alpha < 3/4 ∧ 0 < h_val ∧ 0 < lambda ∧ lambda * h_val > 3 ∧ 0 < ε₀ ∧
      (OmegaAlpha alpha + ε₀) ^ (3/2 : ℝ) *
        ((Real.exp h_val - 1) * ∑' (r : ℕ),
          Real.exp (-(↑(r + 1)) * h_val) *
          Real.sqrt (HFunc (↑(r + 1) * h_val) *
            (Real.exp (↑(r + 1) * h_val) - Real.exp (-(↑(r + 1)) * h_val)))) < c := by
  -- By continuity, there exists a $\delta > 0$ such that $((2 + \delta)^{3/2} * (integralI + \delta)) < c$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ((2 + δ) ^ (3 / 2 : ℝ) * (integralI + δ)) < c := by
    have h_cont : Filter.Tendsto (fun δ : ℝ => (2 + δ) ^ (3 / 2 : ℝ) * (integralI + δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 ^ (3 / 2 : ℝ) * integralI)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by exact Continuous.mul ( Continuous.rpow ( continuous_const.add continuous_id' ) continuous_const <| by norm_num ) <| continuous_const.add continuous_id' ) _ _ <| by norm_num );
    have := h_cont.eventually ( gt_mem_nhds <| show 2 ^ ( 3 / 2 : ℝ ) * integralI < c from hc ) ; have := this.and self_mem_nhdsWithin; obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this.exists; exact ⟨ δ, hδ₂, hδ₁ ⟩ ;
  -- Choose $\alpha$ such that $\Omega_\alpha$ is close to 2.
  obtain ⟨alpha, halpha1, halpha1_strict, halpha2⟩ : ∃ alpha : ℝ, 2 / 3 ≤ alpha ∧ 2 / 3 < alpha ∧ alpha < 3 / 4 ∧ OmegaAlpha alpha < 2 + δ / 2 := by
    have := Metric.tendsto_nhdsWithin_nhds.1 ( OmegaAlpha_tendsto_two ) ( δ / 2 ) ( half_pos hδ_pos );
    obtain ⟨ ε, ε_pos, H ⟩ := this
    have hmin_pos : 0 < Min.min ε ( 3 / 4 - 2 / 3 ) := by positivity
    exact ⟨ 3 / 4 - Min.min ε ( 3 / 4 - 2 / 3 ) / 2,
      by linarith [min_le_left ε ( 3 / 4 - 2 / 3 ), min_le_right ε ( 3 / 4 - 2 / 3 )],
      by linarith [min_le_left ε ( 3 / 4 - 2 / 3 ), min_le_right ε ( 3 / 4 - 2 / 3 )],
      by linarith [min_le_left ε ( 3 / 4 - 2 / 3 ), min_le_right ε ( 3 / 4 - 2 / 3 )],
      by linarith [ abs_lt.mp ( H ( show 3 / 4 - Min.min ε ( 3 / 4 - 2 / 3 ) / 2 < 3 / 4 by linarith [min_le_left ε ( 3 / 4 - 2 / 3 ), min_le_right ε ( 3 / 4 - 2 / 3 )] ) ( by rw [ dist_eq_norm ] ; exact abs_lt.mpr ⟨ by linarith [min_le_left ε ( 3 / 4 - 2 / 3 ), min_le_right ε ( 3 / 4 - 2 / 3 )], by linarith [min_le_left ε ( 3 / 4 - 2 / 3 ), min_le_right ε ( 3 / 4 - 2 / 3 )] ⟩ ) ) ] ⟩;
  -- Choose $h$ such that $(e^h - 1) \sum_{r \geq 1} e^{-rh} \sqrt{H(rh)(e^{rh} - e^{-rh})}$ is close to $integralI$.
  obtain ⟨h_val, hh_pos, hh⟩ : ∃ h_val : ℝ, 0 < h_val ∧ (Real.exp h_val - 1) * ∑' r : ℕ, Real.exp (-(r + 1) * h_val) * Real.sqrt (HFunc ((r + 1) * h_val) * (Real.exp ((r + 1) * h_val) - Real.exp (-(r + 1) * h_val))) < integralI + δ / 2 := by
    have := riemann_sum_convergence ( δ / 2 ) ( half_pos hδ_pos );
    obtain ⟨ h₀, hh₀_pos, hh₀ ⟩ := this; exact ⟨ h₀ / 2, half_pos hh₀_pos, by have := hh₀ ( h₀ / 2 ) ( half_pos hh₀_pos ) ( by linarith ) ; norm_num at *; linarith [ abs_lt.mp this ] ⟩ ;
  refine' ⟨ alpha, h_val, 4 / h_val + 1, δ / 2, halpha1, halpha1_strict, halpha2.1, hh_pos, _, _, _, _ ⟩ <;> norm_num;
  · positivity;
  · nlinarith [ div_mul_cancel₀ 4 hh_pos.ne' ];
  · grind;
  · refine' lt_of_le_of_lt _ hδ;
    refine' mul_le_mul _ _ _ _;
    · exact Real.rpow_le_rpow ( by linarith [ show 0 ≤ OmegaAlpha alpha from mul_nonneg ( mul_nonneg zero_le_two ( one_div_nonneg.mpr ( by linarith ) ) ) ( buchstabOmega_pos _ ( by linarith [ show 2 < UAlpha alpha from by linarith [ UAlpha_range alpha halpha1 halpha2.1 ] ] ) |> le_of_lt ) ] ) ( by linarith ) ( by norm_num );
    · grind;
    · exact mul_nonneg ( sub_nonneg.2 <| Real.one_le_exp hh_pos.le ) <| tsum_nonneg fun _ => mul_nonneg ( Real.exp_nonneg _ ) <| Real.sqrt_nonneg _;
    · positivity

/-- Large second factors: |A₃| ≤ c' · n^{3/4} / (log n)^{3/2}. -/
lemma large_second_factors_bound (c : ℝ) (hc : c > Cstar) :
    ∃ alpha : ℝ, ∃ h_val : ℝ, ∃ lambda : ℝ,
      2/3 ≤ alpha ∧ alpha < 3/4 ∧ UAlpha alpha < 3 ∧ 0 < h_val ∧ 0 < lambda ∧ lambda * h_val > 3 ∧
      ∃ N₃ : ℕ, ∀ n : ℕ, n ≥ N₃ →
        ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → IsProductSidon A →
          ∀ A₃ : Finset ℕ, A₃ ⊆ A →
            (∀ a ∈ A₃, ∃ u v : ℕ, IsAdmissible n alpha a u v ∧
              (∀ u' v' : ℕ, IsAdmissible n alpha a u' v' → v ≤ v') ∧
              Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) < (v : ℝ) ∧
              (v : ℝ) < (n : ℝ) ^ (1/2 : ℝ)) →
            (A₃.card : ℝ) ≤ c * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
  -- Obtain parameters from param_choice
  obtain ⟨alpha, h_val, lambda, ε₀, hα1, hα1_strict, hα2, hh, hlambda, hlh, hε₀, h_coeff⟩ :=
    param_choice c hc
  have hU_strict : UAlpha alpha < 3 := by
    unfold UAlpha; rw [div_lt_iff₀ (by linarith)]; linarith
  refine ⟨alpha, h_val, lambda, hα1, hα2, hU_strict, hh, hlambda, hlh, ?_⟩
  -- Get the level bound
  obtain ⟨N_level, hN_level⟩ := level_bound_combined alpha h_val hα1 hα2 hU_strict hh ε₀ hε₀ lambda hlambda
  -- Get the sum_t_r little-o bound
  obtain ⟨N_sum, hN_sum⟩ := sum_t_r_is_little_o alpha h_val lambda hα1 hα2 hh hlambda hlh
    (OmegaAlpha alpha + ε₀) (by
      have : OmegaAlpha alpha > 0 := by
        unfold OmegaAlpha
        have hU := UAlpha_range alpha hα1 hα2
        exact mul_pos (mul_pos (by norm_num) (by linarith)) (buchstabOmega_pos _ (by linarith))
      linarith)
    ((c - (OmegaAlpha alpha + ε₀) ^ (3/2 : ℝ) *
        ((Real.exp h_val - 1) * ∑' (r : ℕ),
          Real.exp (-(↑(r + 1)) * h_val) *
          Real.sqrt (HFunc (↑(r + 1) * h_val) *
            (Real.exp (↑(r + 1) * h_val) - Real.exp (-(↑(r + 1)) * h_val))))) / 2)
    (by linarith)
  refine ⟨max N_level N_sum + 100, fun n hn A hA hSidon A₃ hA₃ hA₃_mem => ?_⟩
  -- Extract u_fn, v_fn from the existential
  choose! u_fn v_fn hu_fn using hA₃_mem
  set L := ⌊lambda * Real.log (Real.log n)⌋₊ with hL_def
  -- Abbreviations for the coefficient and the Riemann sum
  set coeff := (OmegaAlpha alpha + ε₀) ^ (3/2 : ℝ) *
    ((Real.exp h_val - 1) * ∑' (r : ℕ),
      Real.exp (-(↑(r + 1)) * h_val) *
      Real.sqrt (HFunc (↑(r + 1) * h_val) *
        (Real.exp (↑(r + 1) * h_val) - Real.exp (-(↑(r + 1)) * h_val))))
  set δ := (c - coeff) / 2
  -- We have n ≥ N_level and n ≥ N_sum + 3 by construction
  have hn_level : n ≥ N_level := by omega
  have hn_sum : n ≥ N_sum := by omega
  -- Apply the sum_t_r bound
  have h_sum_bound := hN_sum n (by omega)
  -- Abbreviate the level predicate
  let level_pred (r : ℕ) (a : ℕ) : Prop :=
    Real.exp (-(↑(r + 1) * h_val)) * (n : ℝ) ^ (1/2 : ℝ) < (v_fn a : ℝ) ∧
    (v_fn a : ℝ) ≤ Real.exp (-(↑r * h_val)) * (n : ℝ) ^ (1/2 : ℝ)
  -- Step 1: Every element of A₃ falls in some level r ∈ {0,...,L-1}
  have h_cover : ∀ a ∈ A₃, ∃ r ∈ Finset.range L, level_pred r a := by
    intro a ha;
    -- By definition of $L$, we know that $v_fn(a) > \exp(-L * h_val) * n^{1/2}$.
    have h_v_fn_gt : Real.exp (-L * h_val) * (n : ℝ) ^ (1 / 2 : ℝ) < (v_fn a : ℝ) := by
      exact hu_fn a ha |>.2.2.1;
    contrapose! h_v_fn_gt;
    have h_v_fn_le : ∀ r ∈ Finset.range (L + 1), (v_fn a : ℝ) ≤ Real.exp (-(r : ℝ) * h_val) * (n : ℝ) ^ (1 / 2 : ℝ) := by
      intro r hr;
      induction' r with r ih;
      · simpa using hu_fn a ha |>.2.2.2.le;
      · grind;
    exact h_v_fn_le L ( Finset.mem_range.mpr ( Nat.lt_succ_self _ ) )
  -- Step 2: |A₃| ≤ Σ_{r ∈ range L} |B_r|
  have h_card_sum : (A₃.card : ℝ) ≤ ∑ r ∈ Finset.range L,
      ((A₃.filter (level_pred r)).card : ℝ) := by
    have hsub : A₃ ⊆ Finset.biUnion (Finset.range L)
        (fun r => A₃.filter (level_pred r)) := by
      intro a ha
      obtain ⟨r, hr, hv⟩ := h_cover a ha
      exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨ha, hv⟩⟩
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  -- Step 3: Each |B_r| ≤ first_order + second_order via hN_level
  have h_per_level : ∀ r ∈ Finset.range L,
      ((A₃.filter (level_pred r)).card : ℝ) ≤
      (OmegaAlpha alpha + ε₀) * HFunc (↑(r + 1) * h_val) *
        (Real.exp (↑(r + 1) * h_val) - Real.exp (-(↑(r + 1) * h_val))) *
        (n : ℝ) ^ (1/2 : ℝ) / Real.log n +
      (OmegaAlpha alpha + ε₀) ^ (3/2 : ℝ) *
        (Real.exp h_val - 1) * Real.exp (-(↑(r + 1) * h_val)) *
        Real.sqrt (HFunc (↑(r + 1) * h_val) *
          (Real.exp (↑(r + 1) * h_val) - Real.exp (-(↑(r + 1) * h_val)))) *
        (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    apply hN_level n hn_level A hA hSidon (r + 1) (by omega)
      (by omega) (A₃.filter (level_pred r))
      (Finset.filter_subset _ _ |>.trans hA₃)
    intro a ha
    obtain ⟨hmem, hv⟩ := Finset.mem_filter.mp ha
    refine ⟨u_fn a, v_fn a, (hu_fn a hmem).1, (hu_fn a hmem).2.1, hv.1, ?_, (hu_fn a hmem).2.2.2⟩
    simp only [Nat.add_sub_cancel]; exact hv.2
  -- Step 4: Sum the per-level bounds
  have h_sum_ineq : (A₃.card : ℝ) ≤
      (∑ r ∈ Finset.range L,
        (OmegaAlpha alpha + ε₀) * HFunc (↑(r + 1) * h_val) *
          (Real.exp (↑(r + 1) * h_val) - Real.exp (-(↑(r + 1) * h_val))) *
          (n : ℝ) ^ (1/2 : ℝ) / Real.log n) +
      (∑ r ∈ Finset.range L,
        (OmegaAlpha alpha + ε₀) ^ (3/2 : ℝ) *
          (Real.exp h_val - 1) * Real.exp (-(↑(r + 1) * h_val)) *
          Real.sqrt (HFunc (↑(r + 1) * h_val) *
            (Real.exp (↑(r + 1) * h_val) - Real.exp (-(↑(r + 1) * h_val)))) *
          (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ)) := by
    calc (A₃.card : ℝ) ≤ _ := h_card_sum
      _ ≤ _ := Finset.sum_le_sum h_per_level
      _ = _ := Finset.sum_add_distrib
  -- Step 5: Bound the first sum using h_sum_bound
  have h_first_sum : ∑ r ∈ Finset.range L,
      (OmegaAlpha alpha + ε₀) * HFunc (↑(r + 1) * h_val) *
        (Real.exp (↑(r + 1) * h_val) - Real.exp (-(↑(r + 1) * h_val))) *
        (n : ℝ) ^ (1/2 : ℝ) / Real.log n ≤
      δ * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
    convert h_sum_bound using 1;
    simp +decide only [mul_assoc, Finset.mul_sum _ _ _, sum_mul, sum_div];
    rfl
  -- Step 6: Bound the second sum using finite_sum ≤ tsum
  have h_second_sum : ∑ r ∈ Finset.range L,
      (OmegaAlpha alpha + ε₀) ^ (3/2 : ℝ) *
        (Real.exp h_val - 1) * Real.exp (-(↑(r + 1) * h_val)) *
        Real.sqrt (HFunc (↑(r + 1) * h_val) *
          (Real.exp (↑(r + 1) * h_val) - Real.exp (-(↑(r + 1) * h_val)))) *
        (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) ≤
      coeff * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
    have h_second_sum : ∑ r ∈ Finset.range L, Real.exp (-(r + 1) * h_val) * Real.sqrt (HFunc ((r + 1) * h_val) * (Real.exp ((r + 1) * h_val) - Real.exp (-(r + 1) * h_val))) ≤ ∑' r : ℕ, Real.exp (-(r + 1) * h_val) * Real.sqrt (HFunc ((r + 1) * h_val) * (Real.exp ((r + 1) * h_val) - Real.exp (-(r + 1) * h_val))) := by
      refine' Summable.sum_le_tsum _ _ _;
      · exact fun _ _ => mul_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ );
      · -- We'll use the fact that if the series $\sum_{r=1}^{\infty} a_r$ converges, then $\sum_{r=1}^{\infty} c \cdot a_r$ also converges for any constant $c$.
        have h_series_conv : Summable (fun r : ℕ => Real.exp (-(r + 1) * h_val) * Real.sqrt ((HFunc ((r + 1) * h_val)) * (Real.exp ((r + 1) * h_val) - Real.exp (-(r + 1) * h_val)))) := by
          have h_bound : ∃ K_H > 0, ∀ x : ℝ, 0 ≤ x → HFunc x ≤ K_H * (1 + x) := by
            -- Apply the lemma HFunc_growth_bound to obtain the existence of K_H.
            apply HFunc_growth_bound
          obtain ⟨ K_H, hK_H_pos, hK_H ⟩ := h_bound;
          have h_bound : ∀ r : ℕ, Real.exp (-(r + 1) * h_val) * Real.sqrt (HFunc ((r + 1) * h_val) * (Real.exp ((r + 1) * h_val) - Real.exp (-(r + 1) * h_val))) ≤ Real.exp (-(r + 1) * h_val / 2) * Real.sqrt (K_H * (1 + (r + 1) * h_val)) := by
            intro r
            have h_bound : HFunc ((r + 1) * h_val) * (Real.exp ((r + 1) * h_val) - Real.exp (-(r + 1) * h_val)) ≤ K_H * (1 + (r + 1) * h_val) * Real.exp ((r + 1) * h_val) := by
              exact mul_le_mul ( hK_H _ ( by positivity ) ) ( sub_le_self _ ( by positivity ) ) ( by exact sub_nonneg_of_le ( Real.exp_le_exp.mpr ( by nlinarith ) ) ) ( by positivity );
            refine' le_trans ( mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt h_bound ) ( by positivity ) ) _;
            rw [ Real.sqrt_mul <| by positivity, Real.sqrt_mul <| by positivity ] ; ring_nf ; norm_num [ ← Real.exp_add, ← Real.exp_half ] ; ring_nf ; norm_num [ ← Real.exp_add, ← Real.exp_half ] ;
            rw [ show ( - ( r * h_val ) - h_val : ℝ ) = - ( r * h_val * ( 1 / 2 ) ) + - ( h_val * ( 1 / 2 ) ) - ( r * h_val * ( 1 / 2 ) + h_val * ( 1 / 2 ) ) by ring ] ; rw [ Real.exp_sub ] ; ring_nf ; norm_num [ Real.exp_ne_zero ] ;
          refine' Summable.of_nonneg_of_le ( fun r => mul_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ ) ) ( fun r => h_bound r ) _;
          have h_summable : Summable (fun r : ℕ => Real.exp (-(r + 1) * h_val / 2) * (r + 1)) := by
            have h_summable : Summable (fun r : ℕ => Real.exp (-r * h_val / 2) * r) := by
              have h_summable : Summable (fun r : ℕ => (r : ℝ) * (Real.exp (-h_val / 2)) ^ r) := by
                refine' summable_of_ratio_norm_eventually_le _ _;
                exact ( 1 + Real.exp ( -h_val / 2 ) ) / 2;
                · linarith [ Real.exp_lt_one_iff.mpr ( show -h_val / 2 < 0 by linarith ) ];
                · norm_num [ pow_succ, mul_assoc, mul_left_comm, mul_comm ];
                  norm_num [ abs_of_nonneg, add_nonneg ];
                  refine' ⟨ ⌈2 / ( 1 - Real.exp ( -h_val / 2 ) ) ⌉₊ + 1, fun n hn => _ ⟩;
                  have := Nat.lt_of_ceil_lt hn;
                  rw [ div_lt_iff₀ ] at this <;> nlinarith [ Real.exp_pos ( -h_val / 2 ), Real.exp_lt_one_iff.mpr ( show -h_val / 2 < 0 by linarith ), pow_pos ( Real.exp_pos ( -h_val / 2 ) ) n ];
              convert h_summable using 2 ; norm_num [ ← Real.exp_nat_mul, mul_div_assoc ] ; ring_nf;
            convert summable_nat_add_iff 1 |>.2 h_summable using 2 ; push_cast ; ring;
          have h_summable : Summable (fun r : ℕ => Real.exp (-(r + 1) * h_val / 2) * (r + 1) * Real.sqrt (K_H * (1 + h_val))) := by
            exact h_summable.mul_right _;
          refine' h_summable.of_nonneg_of_le ( fun r => mul_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ ) ) ( fun r => _ );
          rw [ mul_assoc ];
          gcongr;
          rw [ Real.sqrt_le_iff ];
          exact ⟨ by positivity, by rw [ mul_pow, Real.sq_sqrt <| by positivity ] ; nlinarith [ sq ( r : ℝ ), mul_nonneg hK_H_pos.le hh.le ] ⟩;
        convert h_series_conv using 1;
    convert mul_le_mul_of_nonneg_right h_second_sum ( show 0 ≤ ( OmegaAlpha alpha + ε₀ ) ^ ( 3 / 2 : ℝ ) * ( Real.exp h_val - 1 ) * ( n : ℝ ) ^ ( 3 / 4 : ℝ ) / Real.log n ^ ( 3 / 2 : ℝ ) by exact div_nonneg ( mul_nonneg ( mul_nonneg ( Real.rpow_nonneg ( by linarith [ show 0 ≤ OmegaAlpha alpha by
                                                                                                                                                                                                                                                                              exact mul_nonneg ( mul_nonneg zero_le_two ( one_div_nonneg.mpr ( by linarith ) ) ) ( buchstabOmega_pos _ ( by linarith [ UAlpha_range alpha hα1 hα2 ] ) |> le_of_lt ) ] ) _ ) ( sub_nonneg.mpr ( Real.one_le_exp hh.le ) ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( Real.rpow_nonneg ( Real.log_natCast_nonneg _ ) _ ) ) using 1 <;> norm_num [ Finset.sum_div _ _ _, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
    · exact Finset.sum_congr rfl fun _ _ => by ring;
    · grind
  -- Step 7: Combine
  calc (A₃.card : ℝ) ≤ _ := h_sum_ineq
    _ ≤ δ * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) +
         coeff * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) :=
      add_le_add h_first_sum h_second_sum
    _ = (δ + coeff) * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by ring
    _ ≤ c * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
      gcongr
      show δ + coeff ≤ c
      simp only [δ]
      linarith

/-! ### Auxiliary growth bound -/

/-- For any C > 0 and 0 < β < 3/4, C·n^β + √n = o(n^{3/4}/(log n)^{3/2}). -/
lemma lower_order_absorbed (C : ℝ) (_hC : C > 0) (beta : ℝ) (hbeta1 : 0 < beta) (hbeta2 : beta < 3/4)
    (delta : ℝ) (hdelta : delta > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C * (n : ℝ) ^ beta + Real.sqrt n ≤ delta * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
  -- We can divide both sides of the inequality by $n^{3/4}$ to simplify it.
  suffices h_div : ∃ N₀ : ℕ, ∀ n ≥ N₀, (C * (n : ℝ) ^ (beta - 3 / 4 : ℝ) + (n : ℝ) ^ (-1 / 4 : ℝ)) * (Real.log n) ^ (3 / 2 : ℝ) ≤ delta by
    obtain ⟨ N₀, hN₀ ⟩ := h_div; use N₀ + 2; intro n hn; specialize hN₀ n ( by linarith ) ; rw [ le_div_iff₀ ( Real.rpow_pos_of_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) _ ) ] ; convert mul_le_mul_of_nonneg_right hN₀ ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( 3/4 : ℝ ) ) using 1 ; ring_nf;
    norm_num [ Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add ( Nat.cast_pos.mpr <| by linarith : 0 < ( n : ℝ ) ) ] ; ring;
  -- We'll use the fact that $n^{beta - 3/4} \cdot (\log n)^{3/2}$ and $n^{-1/4} \cdot (\log n)^{3/2}$ tend to $0$ as $n \to \infty$.
  have h_tendsto_zero : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (beta - 3 / 4 : ℝ) * (Real.log n) ^ (3 / 2 : ℝ)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-1 / 4 : ℝ) * (Real.log n) ^ (3 / 2 : ℝ)) Filter.atTop (nhds 0) := by
    constructor;
    · -- Let $y = \log n$, therefore the expression becomes $e^{(\beta - 3/4)y} y^{3/2}$.
      suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp ((beta - 3 / 4) * y) * y ^ (3 / 2 : ℝ)) Filter.atTop (nhds 0) by
        have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
      -- Let $z = (\frac{3}{4} - \beta)y$, therefore the expression becomes $e^{-z} (\frac{z}{\frac{3}{4} - \beta})^{3/2}$.
      suffices h_z : Filter.Tendsto (fun z : ℝ => Real.exp (-z) * (z / (3 / 4 - beta)) ^ (3 / 2 : ℝ)) Filter.atTop (nhds 0) by
        convert h_z.comp ( Filter.tendsto_id.const_mul_atTop ( show 0 < 3 / 4 - beta by linarith ) ) using 2 ; norm_num;
        rw [ mul_div_cancel_left₀ _ ( by linarith ) ] ; ring_nf;
      -- We can factor out the constant $(3/4 - \beta)^{-3/2}$ from the limit.
      suffices h_factor : Filter.Tendsto (fun z : ℝ => Real.exp (-z) * z ^ (3 / 2 : ℝ)) Filter.atTop (nhds 0) by
        have h_factor : Filter.Tendsto (fun z : ℝ => Real.exp (-z) * z ^ (3 / 2 : ℝ) * (1 / (3 / 4 - beta)) ^ (3 / 2 : ℝ)) Filter.atTop (nhds 0) := by
          simpa using h_factor.mul tendsto_const_nhds;
        refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with z hz using by rw [ Real.div_rpow ( by positivity ) ( by linarith ) ] ; rw [ Real.div_rpow ( by positivity ) ( by linarith ) ] ; ring );
      have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
      refine' squeeze_zero_norm' _ this;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ mul_comm ] ; exact mul_le_mul_of_nonneg_right ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le hx.le <| show ( 3 : ℝ ) / 2 ≤ 2 by norm_num ) <| by norm_num ) <| by positivity;
    · -- Let $y = \log n$, therefore the expression becomes $y^{3/2} e^{-y/4}$.
      suffices h_log : Filter.Tendsto (fun y : ℝ => y ^ (3 / 2 : ℝ) * Real.exp (-y / 4)) Filter.atTop (nhds 0) by
        have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
      -- Let $z = \frac{y}{4}$, therefore the expression becomes $z^{3/2} \cdot e^{-z}$.
      suffices h_z : Filter.Tendsto (fun z : ℝ => (4 * z) ^ (3 / 2 : ℝ) * Real.exp (-z)) Filter.atTop (nhds 0) by
        convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 4 : ℝ ) ⁻¹ ) ) using 2 ; norm_num ; ring_nf;
      have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
      refine' squeeze_zero_norm' _ this;
      norm_num;
      exact ⟨ 64, fun x hx => by rw [ abs_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_right ( by rw [ show ( 4 * x ) ^ ( 3 / 2 : ℝ ) = ( 4 * x ) * Real.sqrt ( 4 * x ) by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ; linarith ] ; nlinarith [ Real.sqrt_nonneg ( 4 * x ), Real.mul_self_sqrt ( show 0 ≤ 4 * x by linarith ) ] ) ( by positivity ) ⟩;
  have := h_tendsto_zero.1.const_mul C |> Filter.Tendsto.add <| h_tendsto_zero.2; simp_all +decide [ add_mul ] ;
  simpa [ mul_assoc ] using this.eventually ( ge_mem_nhds hdelta )

/-! ### Main theorem -/

/-- For c > C_*, |A| ≤ π(n) + c·n^{3/4}/(log n)^{3/2} for large n. -/
theorem mult_sidon_upper_bound_parametric (c : ℝ) (hc : c > Cstar) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → IsProductSidon A →
        (A.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + c * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
  -- Set c' = (c + Cstar)/2.
  set c' : ℝ := (c + Cstar) / 2;
  -- Obtain α, h_val, λ, N₃ from large_second_factors_bound c'.
  obtain ⟨α, h_val, lambda, hα1, hα2, hU_strict, hh, hlambda, hlh, N₃, hN₃⟩ : ∃ α h_val lambda : ℝ, 2 / 3 ≤ α ∧ α < 3 / 4 ∧ UAlpha α < 3 ∧ 0 < h_val ∧ 0 < lambda ∧ lambda * h_val > 3 ∧ ∃ N₃ : ℕ, ∀ n : ℕ, n ≥ N₃ →
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → IsProductSidon A →
      ∀ A₃ : Finset ℕ, A₃ ⊆ A →
        (∀ a ∈ A₃, ∃ u v : ℕ, IsAdmissible n α a u v ∧
          (∀ u' v' : ℕ, IsAdmissible n α a u' v' → v ≤ v') ∧
          Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) < (v : ℝ) ∧
          (v : ℝ) < (n : ℝ) ^ (1/2 : ℝ)) →
        (A₃.card : ℝ) ≤ c' * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
          apply large_second_factors_bound c' (by
          exact lt_div_iff₀' ( by positivity ) |>.2 ( by linarith ));
  obtain ⟨ C₁, hC₁_pos, N₁, hN₁ ⟩ := small_second_factors_bound α hα1 hα2;
  obtain ⟨ N₂, hN₂ ⟩ := middle_second_factors_bound α h_val lambda hα1 hα2 hh hlambda hlh ((c - Cstar) / 4) (by linarith);
  obtain ⟨ N₀, hN₀ ⟩ := lower_order_absorbed C₁ hC₁_pos α ( by linarith ) ( by linarith ) ( ( c - Cstar ) / 4 ) ( by linarith );
  refine' ⟨ N₀ + N₁ + N₂ + N₃ + 200, fun n hn A hA hA' => _ ⟩;
  -- Let $A_{\text{sq}}$ be the set of perfect squares in $A$, and $A_{\text{rest}} = A \setminus A_{\text{sq}}$.
  set A_sq := A.filter (fun m => Nat.sqrt m * Nat.sqrt m = m)
  set A_rest := A \ A_sq;
  -- For each $a \in A_{\text{rest}}$, choose an admissible factorization $(u(a), v(a))$ with minimal v.
  obtain ⟨u, v, hu, hv_min⟩ : ∃ u v : ℕ → ℕ, (∀ a ∈ A_rest, IsAdmissible n α a (u a) (v a) ∧ (v a : ℝ) < (n : ℝ) ^ (1/2 : ℝ)) ∧ (∀ a ∈ A_rest, ∀ u' v' : ℕ, IsAdmissible n α a u' v' → v a ≤ v') := by
    have h_admissible : ∀ a ∈ A_rest, ∃ u v : ℕ, IsAdmissible n α a u v ∧ (∀ u' v' : ℕ, IsAdmissible n α a u' v' → v ≤ v') ∧ (v : ℝ) < (n : ℝ) ^ (1/2 : ℝ) := by
      intro a ha
      have hexists := exists_admissible_factorization n ( by linarith ) a ( Finset.mem_Icc.mp ( hA ( Finset.mem_sdiff.mp ha |>.1 ) ) |>.1 ) ( Finset.mem_Icc.mp ( hA ( Finset.mem_sdiff.mp ha |>.1 ) ) |>.2 ) α hα1 ( by linarith )
      obtain ⟨u₀, v₀, hadm₀, hmin₀⟩ := exists_minimal_admissible n α a hexists
      refine ⟨u₀, v₀, hadm₀, hmin₀, ?_⟩
      -- v₀ ≤ v for any admissible v, so v₀ < n^{1/2} follows from existence of some v < n^{1/2}
      -- v < n^{1/2} because a is not a perfect square, so v < u, hence v² < uv = a ≤ n
      have ⟨u₁, v₁, hadm₁, hv₁_lt⟩ : ∃ u v : ℕ, IsAdmissible n α a u v ∧ (v : ℝ) < (n : ℝ) ^ (1/2 : ℝ) := by
        obtain ⟨u, v, hadm⟩ := hexists; exact ⟨u, v, hadm, by
        have hvu : v < u := by
          rcases lt_or_eq_of_le hadm.2.1 with h | h; exact h
          exfalso; apply (Finset.mem_sdiff.mp ha).2; rw [Finset.mem_filter]
          exact ⟨(Finset.mem_sdiff.mp ha).1, by subst h; simp [hadm.1, Nat.sqrt_eq]⟩
        have hvsq : v * v < n := by nlinarith [hadm.1, (Finset.mem_Icc.mp (hA (Finset.mem_sdiff.mp ha).1)).2]
        have : (v : ℝ) ^ 2 < (n : ℝ) := by norm_cast; linarith
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ n by positivity), Real.sqrt_nonneg (n:ℝ), Real.sqrt_eq_rpow (n:ℝ)]⟩
      exact lt_of_le_of_lt (by exact_mod_cast hmin₀ u₁ v₁ hadm₁) hv₁_lt
    choose! u v huv using h_admissible
    exact ⟨u, v, fun a ha => ⟨(huv a ha).1, (huv a ha).2.2⟩, fun a ha => (huv a ha).2.1⟩
  -- Let $A₁ = \{a \in A_{\text{rest}} \mid v(a) \leq n^{1-\alpha}\}$, $A₂ = \{a \in A_{\text{rest}} \mid n^{1-\alpha} < v(a) \leq \exp(-Lh) \cdot n^{1/2}\}$, and $A₃ = \{a \in A_{\text{rest}} \mid \exp(-Lh) \cdot n^{1/2} < v(a)\}$.
  set A₁ := A_rest.filter (fun a => (v a : ℝ) ≤ (n : ℝ) ^ (1 - α))
  set A₂ := A_rest.filter (fun a => (n : ℝ) ^ (1 - α) < (v a : ℝ) ∧ (v a : ℝ) ≤ Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ))
  set A₃ := A_rest.filter (fun a => Real.exp (-(⌊lambda * Real.log (Real.log n)⌋₊ : ℝ) * h_val) * (n : ℝ) ^ (1/2 : ℝ) < (v a : ℝ));
  -- Then $|A| \leq |A_{\text{sq}}| + |A₁| + |A₂| + |A₃|$.
  have h_card : (A.card : ℝ) ≤ (A_sq.card : ℝ) + (A₁.card : ℝ) + (A₂.card : ℝ) + (A₃.card : ℝ) := by
    have h_card : A = A_sq ∪ A₁ ∪ A₂ ∪ A₃ := by
      grind +splitImp;
    exact mod_cast h_card ▸ Finset.card_union_le _ _ |> le_trans <| add_le_add ( Finset.card_union_le _ _ |> le_trans <| add_le_add ( Finset.card_union_le _ _ ) le_rfl ) le_rfl;
  -- By definition of $A₁$, $A₂$, and $A₃$, we have $|A₁| \leq \pi(n) + C₁ n^\alpha$, $|A₂| \leq \epsilon n^{3/4} / (\log n)^{3/2}$, and $|A₃| \leq c' n^{3/4} / (\log n)^{3/2}$.
  have hA₁ : (A₁.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + C₁ * (n : ℝ) ^ α := by
    apply hN₁ n (by linarith) A hA hA' A₁ (by
    exact fun x hx => Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1) (by
    exact fun a ha => ⟨ u a, v a, hu a ( Finset.mem_filter.mp ha |>.1 ) |>.1, Finset.mem_filter.mp ha |>.2 ⟩)
  have hA₂ : (A₂.card : ℝ) ≤ (c - Cstar) / 4 * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
    apply hN₂ n (by linarith) A hA hA' A₂ (by
    exact fun x hx => Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1) (by
    exact fun a ha => ⟨ u a, v a, hu a ( Finset.mem_filter.mp ha |>.1 ) |>.1, Finset.mem_filter.mp ha |>.2 ⟩)
  have hA₃ : (A₃.card : ℝ) ≤ c' * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
    apply hN₃ n (by linarith) A hA hA' A₃ (by
    exact fun x hx => Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1) (by
    exact fun a ha => ⟨ u a, v a, hu a ( Finset.mem_filter.mp ha |>.1 ) |>.1, hv_min a ( Finset.mem_filter.mp ha |>.1 ), Finset.mem_filter.mp ha |>.2, hu a ( Finset.mem_filter.mp ha |>.1 ) |>.2 ⟩);
  -- By definition of $A_{\text{sq}}$, we have $|A_{\text{sq}}| \leq \sqrt{n}$.
  have hA_sq : (A_sq.card : ℝ) ≤ Real.sqrt n := by
    have hA_sq : (A_sq.card : ℝ) ≤ Nat.sqrt n := by
      exact_mod_cast le_trans ( Finset.card_le_card <| show A_sq ⊆ Finset.image ( fun x => x * x ) ( Finset.Icc 1 ( Nat.sqrt n ) ) from fun x hx => Finset.mem_image.mpr ⟨ Nat.sqrt x, Finset.mem_Icc.mpr ⟨ Nat.sqrt_pos.mpr <| Finset.mem_Icc.mp ( hA <| Finset.mem_filter.mp hx |>.1 ) |>.1, Nat.le_of_lt_succ <| Nat.sqrt_lt.mpr <| by nlinarith [ Finset.mem_Icc.mp ( hA <| Finset.mem_filter.mp hx |>.1 ) |>.2, Nat.lt_succ_sqrt n ] ⟩, by nlinarith [ Finset.mem_filter.mp hx |>.2 ] ⟩ ) <| Finset.card_image_le.trans <| by norm_num;
    exact le_trans hA_sq <| Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' _;
  grind +revert

/-! ### Corollary with explicit constant -/

/-- There exists C_* < 13.1 such that for all c > C_*, the bound holds. -/
theorem mult_sidon_upper_bound :
    ∃ Cstar' : ℝ, Cstar' < 13.1 ∧
      ∀ c : ℝ, c > Cstar' →
        ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
          ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → IsProductSidon A →
            (A.card : ℝ) ≤ (Nat.primeCounting n : ℝ) +
              c * (n : ℝ) ^ (3/4 : ℝ) / (Real.log n) ^ (3/2 : ℝ) := by
  exact ⟨Cstar, Cstar_lt, fun c hc => mult_sidon_upper_bound_parametric c hc⟩

end

end Main

#print axioms mult_sidon_upper_bound
