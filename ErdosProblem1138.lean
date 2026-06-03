import Mathlib

/-!
Solving Erdős Problem #1138 (https://www.erdosproblems.com/1138), GPT-5.5 Pro,
prompted by Hrishi Sunder, Sourish Kumrawat and Kireet Cheri, showed that there
exist constants C > 1 such that, with d(x) = max{p_{n+1} - p_n : p_n < x}, the
asymptotic π(y + C·d(x)) - π(y) ~ C·d(x)/log y does not uniformly hold for y in
(x/2, x).

Let SetC be the set of all constants C for which the asymptotic does hold for y
with (1/2 + o(1))x < y < (1 + o(1))x. Extending the above result, Terence Tao
and I realised that either SetC = {0} or SetC = Cℤ for some C > 1.

Using this slightly amended range of y (see the notion of Admissible below for
the precise definition), Aristotle from Harmonic
(aristotle-harmonic@harmonic.fun) managed to formalize this classification
result in Lean, with the only unproven assumption being the Prime Number Theorem
in the form π(x) = (1 + o(1)) x / log x. The wording of this result is taken
verbatim from the PNT+ project, which can be found here:

https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/

The exact pi_alt statement that we use here is proven in their Lean file titled
'Consequences.lean'

Lean version: leanprover/lean4:v4.28.0
-/

open Nat Finset Real Filter Set

noncomputable section

/-! ## Definitions -/

/-- The prime-counting function for real arguments:
    `π(t) = #{p ∈ ℕ : p is prime and p ≤ t}`. -/
def piReal (t : ℝ) : ℕ := Nat.primeCounting (⌊t⌋₊)

/-- The `n`-th prime (0-indexed): `nthPrime' 0 = 2`, `nthPrime' 1 = 3`, etc. -/
def nthPrime' (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The prime gap `g_n = p_{n+1} - p_n`. -/
def primeGap (n : ℕ) : ℕ := nthPrime' (n + 1) - nthPrime' n

/-- `D(x) = max({0} ∪ {g_n : n ≥ 0 and p_n < x})`, the maximal prime gap
    among primes below `x`. -/
def D (x : ℝ) : ℕ :=
  sSup ({0} ∪ {g : ℕ | ∃ n : ℕ, (nthPrime' n : ℝ) < x ∧ g = primeGap n})

/-- `G(x) = max({0} ∪ {g_n : n ≥ 0 and p_{n+1} < x})`. -/
def G (x : ℝ) : ℕ :=
  sSup ({0} ∪ {g : ℕ | ∃ n : ℕ, (nthPrime' (n + 1) : ℝ) < x ∧ g = primeGap n})

/-- `Δ_c(x, y) = π(y + c·D(x)) - π(y)`. -/
def Delta (c : ℝ) (x y : ℝ) : ℤ :=
  (piReal (y + c * (D x : ℝ)) : ℤ) - (piReal y : ℤ)

/-- A real number `c` is **admissible** if there exists a `γ > 0` such that for
    every `δ ∈ (0, γ)` and every `ε > 0`, there exists `X` such that for every
    `x ≥ X` and every `y` with `(1/2 + δ)x < y < (1 + δ)x`, one has
    `|Δ_c(x,y) - c·D(x)/log(y)| ≤ ε·|c|·D(x)/log(y)`. -/
def Admissible (c : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧
  ∀ δ : ℝ, 0 < δ → δ < γ →
  ∀ ε : ℝ, 0 < ε →
  ∃ X : ℝ,
    ∀ x : ℝ, X ≤ x →
    ∀ y : ℝ, (1/2 + δ) * x < y → y < (1 + δ) * x →
    |((Delta c x y : ℤ) : ℝ) - c * (D x : ℝ) / Real.log y| ≤
      ε * |c| * (D x : ℝ) / Real.log y

/-- The set of admissible constants. -/
def SetC : Set ℝ := {c : ℝ | Admissible c}

/-- A gap `g_n` is a **strict record gap** if `g_n > g_m` for every `m < n`. -/
def IsStrictRecord (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → primeGap m < primeGap n

/-- **PNT** in the form: π(x) = (1 + o(1)) x / log x. Unproven assumption. -/
axiom pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x

/-! ## Primorial helpers -/

lemma prime_dvd_primorial {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    p ∣ primorial n := by
  exact Finset.dvd_prod_of_mem _ (by simp [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hp⟩)

lemma log_primorial_le (n : ℕ) :
    Real.log (primorial n : ℝ) ≤ n * Real.log 4 := by
  have h_primorial_le : (primorial n : ℝ) ≤ 4^n := by
    exact_mod_cast primorial_le_4_pow n
  simpa using Real.log_le_log (Nat.cast_pos.mpr <| primorial_pos _) h_primorial_le

/-! ## Odd prime factor of even non-power-of-2 -/

lemma odd_prime_factor_of_even_nonpow2 (d : ℤ) (y : ℕ)
    (hd1 : 1 - (y : ℤ) ≤ d) (hd2 : d ≤ 2 * y) (hd0 : d ≠ 0)
    (hdeven : 2 ∣ d) (hnotpow : ∀ a : ℕ, a ≥ 1 → d ≠ (2 : ℤ) ^ a ∧ d ≠ -(2 : ℤ) ^ a) :
    ∃ p : ℕ, p.Prime ∧ p % 2 = 1 ∧ (p : ℤ) ∣ d ∧ p ≤ y := by
  obtain ⟨a, m, ha, hm⟩ : ∃ a m : ℕ, a ≥ 1 ∧ d.natAbs = 2^a * m ∧ m > 1 ∧ m % 2 = 1 := by
    obtain ⟨a, m, ha, hm⟩ : ∃ a m : ℕ, a ≥ 1 ∧ d.natAbs = 2^a * m ∧ m % 2 = 1 := by
      use Nat.factorization (Int.natAbs d) 2;
      refine' ⟨ d.natAbs / 2 ^ d.natAbs.factorization 2, Nat.pos_of_ne_zero _, Eq.symm ( Nat.mul_div_cancel' <| Nat.ordProj_dvd _ _ ), _ ⟩;
      · simp_all +decide [ Nat.factorization, ← even_iff_two_dvd, parity_simps ];
      · exact Nat.mod_two_ne_zero.mp fun con => absurd ( Nat.dvd_of_mod_eq_zero con ) ( Nat.not_dvd_ordCompl ( by norm_num ) <| by aesop );
    rcases m with ( _ | _ | m ) <;> simp_all +decide;
    · grind +splitImp;
    · exact ⟨ a, ha, m + 1 + 1, rfl, by linarith, hm.2 ⟩;
  obtain ⟨p, hp_prime, hp_div⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ m ∧ p % 2 = 1 := by
    exact ⟨ Nat.minFac m, Nat.minFac_prime hm.2.1.ne', Nat.minFac_dvd m, Nat.mod_two_ne_zero.mp fun h => by have := Nat.dvd_trans ( Nat.dvd_of_mod_eq_zero h ) ( Nat.minFac_dvd m ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ⟩;
  refine' ⟨ p, hp_prime, hp_div.2, _, _ ⟩;
  · exact Int.dvd_trans ( Int.natCast_dvd_natCast.mpr hp_div.1 ) ( Int.dvd_trans ( Int.natCast_dvd_natCast.mpr ( dvd_of_mul_left_eq _ hm.1.symm ) ) ( by simp ) );
  · cases abs_cases d <;> nlinarith [ Nat.le_of_dvd ( by linarith ) hp_div.1, pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ha ]

/-! ## Compositeness verification -/

/-- If n : ℤ is positive and has a prime divisor p < n, then n.toNat > 1 and not prime. -/
lemma int_toNat_composite (n : ℤ) (hn_pos : 0 < n) (p : ℕ)
    (hp : p.Prime) (hdvd : (p : ℤ) ∣ n) (hlt : (p : ℤ) < n) :
    1 < n.toNat ∧ ¬n.toNat.Prime := by
  have h_gt_one : 1 < n.toNat := by
    linarith [ hp.two_le, Int.toNat_of_nonneg hn_pos.le ]
  have h_not_prime : ¬ Nat.Prime n.toNat := by
    intro H; have := Nat.dvd_of_mod_eq_zero ( show n.toNat % p = 0 from Nat.mod_eq_zero_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast, Int.toNat_of_nonneg hn_pos.le ] using hdvd ) ; rw [ H.dvd_iff_eq ] at this <;> aesop
  exact ⟨h_gt_one, h_not_prime⟩

/-- Case 1: d odd → B+d even and > 2, hence composite -/
lemma composite_case_odd (B y : ℕ) (hy : 30 ≤ y) (hBodd : B % 2 = 1)
    (hBgt : y ^ 3 < B) (d : ℤ) (hd1 : 1 - (y : ℤ) ≤ d)
    (hd_odd : ¬Even d) :
    1 < ((B : ℤ) + d).toNat ∧ ¬((B : ℤ) + d).toNat.Prime := by
  have h_even : 2 ∣ (B : ℤ) + d := by grind
  have h_composite : 2 < (B : ℤ) + d := by nlinarith only [sq y, hy, hBgt, hd1]
  convert int_toNat_composite (B + d) (by linarith) 2 Nat.prime_two (by simpa using h_even) (by simpa using h_composite) using 1

/-- Case 2: d = 0 → B divisible by 3 and > 3, hence composite -/
lemma composite_case_zero (B y : ℕ) (hy : 30 ≤ y)
    (hBdiv : ∀ p, p.Prime → p % 2 = 1 → p ≤ y → p ∣ B)
    (hBgt : y ^ 3 < B) :
    1 < ((B : ℤ) + 0).toNat ∧ ¬((B : ℤ) + 0).toNat.Prime := by
  convert int_toNat_composite (B : ℤ) (by norm_cast; nlinarith [pow_succ y 2]) 3 Nat.prime_three _ _ <;> norm_cast
  · exact hBdiv 3 Nat.prime_three rfl (by linarith)
  · nlinarith [pow_succ y 2]

/-- Case 3: d even, nonzero, not ±2^a → has odd prime factor p ≤ y dividing both B and d -/
lemma composite_case_even_nonpow (B y : ℕ) (hy : 30 ≤ y)
    (hBdiv : ∀ p, p.Prime → p % 2 = 1 → p ≤ y → p ∣ B)
    (hBgt : y ^ 3 < B) (d : ℤ) (hd1 : 1 - (y : ℤ) ≤ d) (hd2 : d ≤ 2 * ↑y)
    (hd0 : d ≠ 0) (hd_even : Even d)
    (hnotpow : ∀ a : ℕ, a ≥ 1 → d ≠ (2 : ℤ) ^ a ∧ d ≠ -(2 : ℤ) ^ a) :
    1 < ((B : ℤ) + d).toNat ∧ ¬((B : ℤ) + d).toNat.Prime := by
  obtain ⟨p, hp_prime, hp_odd, hp_div_d, hp_le_y⟩ : ∃ p : ℕ, p.Prime ∧ p % 2 = 1 ∧ (p : ℤ) ∣ d ∧ p ≤ y := by
    convert odd_prime_factor_of_even_nonpow2 d y hd1 hd2 hd0 (even_iff_two_dvd.mp hd_even) hnotpow using 1
  have h_gt_p : (p : ℤ) < (B : ℤ) + d := by nlinarith only [sq y, hy, hp_le_y, hBgt, hd1]
  have h_pos : 0 < (B : ℤ) + d := by nlinarith only [sq y, hy, hBgt, hd1, hd2]
  convert int_toNat_composite (B + d) h_pos p hp_prime (dvd_add (mod_cast hBdiv p hp_prime hp_odd hp_le_y) hp_div_d) h_gt_p using 1

/-
Case 4: d = ±2^a → exceptional prime q divides B+d.
-/
lemma composite_case_exc (B y : ℕ)
    (hBgt : y ^ 3 + y < B) (d : ℤ) (hd1 : 1 - (y : ℤ) ≤ d)
    (q : ℕ) (hq_prime : q.Prime) (hq_le : q ≤ y ^ 3)
    (hq_dvd : (q : ℤ) ∣ ((B : ℤ) + d)) :
    1 < ((B : ℤ) + d).toNat ∧ ¬((B : ℤ) + d).toNat.Prime := by
  convert int_toNat_composite ( B + d ) _ q hq_prime hq_dvd _ using 1;
  · grind;
  · linarith [ pow_succ y 2 ]

/-- Main compositeness lemma combining all cases. -/
lemma composite_of_construction (B y : ℕ) (hy : 30 ≤ y)
    (hBodd : B % 2 = 1)
    (hBdiv : ∀ p, p.Prime → p % 2 = 1 → p ≤ y → p ∣ B)
    (hBgt : y ^ 3 + y < B)
    (hexc : ∀ d : ℤ, (1 : ℤ) - ↑y ≤ d → d ≤ 2 * ↑y → d ≠ 0 →
      (∃ a : ℕ, a ≥ 1 ∧ (d = (2 : ℤ) ^ a ∨ d = -(2 : ℤ) ^ a)) →
      ∃ q : ℕ, q.Prime ∧ y < q ∧ q ≤ y ^ 3 ∧ (q : ℤ) ∣ ((B : ℤ) + d)) :
    ∀ d : ℤ, (1 : ℤ) - ↑y ≤ d → d ≤ 2 * ↑y →
      1 < ((B : ℤ) + d).toNat ∧ ¬((B : ℤ) + d).toNat.Prime := by
  intro d hd1 hd2
  by_cases hd0 : d = 0
  · subst hd0; exact composite_case_zero B y hy hBdiv (by linarith)
  · by_cases hd_even : Even d
    · by_cases hpow : ∃ a : ℕ, a ≥ 1 ∧ (d = (2 : ℤ) ^ a ∨ d = -(2 : ℤ) ^ a)
      · obtain ⟨q, hq1, hq2, hq3, hq4⟩ := hexc d hd1 hd2 hd0 hpow
        exact composite_case_exc B y hBgt d hd1 q hq1 hq3 hq4
      · exact composite_case_even_nonpow B y hy hBdiv (by linarith) d hd1 hd2 hd0 hd_even
          (fun a ha => ⟨fun h => hpow ⟨a, ha, Or.inl h⟩, fun h => hpow ⟨a, ha, Or.inr h⟩⟩)
    · exact composite_case_odd B y hy hBodd (by linarith) d hd1 hd_even

/-
For y ≥ 30, primorial(y) > 2y³ + y.
-/
set_option maxRecDepth 2000 in
lemma primorial_gt_double_cube (y : ℕ) (hy : 30 ≤ y) : 2 * y ^ 3 + y < primorial y := by
  have h_ind : ∀ y, 60 ≤ y → primorial y > 2 * y ^ 3 + y := by
    intro y hy
    induction' y using Nat.strong_induction_on with y ih
    by_cases hy60 : y ≤ 120;
    · interval_cases y <;> decide;
    · -- By Bertrand's postulate, there exists a prime $p$ such that $y/2 < p \leq y$.
      obtain ⟨p, hp_prime, hp_bounds⟩ : ∃ p, Nat.Prime p ∧ y / 2 < p ∧ p ≤ y := by
        exact Nat.exists_prime_lt_and_le_two_mul ( y / 2 ) ( by omega ) |> fun ⟨ p, hp₁, hp₂ ⟩ => ⟨ p, hp₁, by omega, by omega ⟩;
      -- By the induction hypothesis, we have $primorial(p-1) > 2(p-1)^3 + (p-1)$.
      have h_ind_hyp : primorial (p - 1) > 2 * (p - 1) ^ 3 + (p - 1) := by
        grind;
      -- Since $p$ is prime and $p \leq y$, we have $primorial y \geq p \cdot primorial (p - 1)$.
      have h_primorial_ge : primorial y ≥ p * primorial (p - 1) := by
        have h_primorial_ge : primorial y = primorial (p - 1) * ∏ q ∈ Finset.filter Nat.Prime (Finset.Icc p y), q := by
          have h_primorial_ge : primorial y = ∏ q ∈ Finset.filter Nat.Prime (Finset.Icc 1 y), q := by
            unfold primorial;
            congr 1 with ( _ | i ) <;> aesop;
          have h_primorial_ge : primorial (p - 1) = ∏ q ∈ Finset.filter Nat.Prime (Finset.Icc 1 (p - 1)), q := by
            refine' Finset.prod_bij ( fun q hq => q ) _ _ _ _ <;> simp_all +decide;
            exact fun a ha ha' => Nat.Prime.pos ha';
          rw [ ‹primorial y = _›, h_primorial_ge, ← Finset.prod_union ];
          · rcongr q ; norm_num;
            exact ⟨ fun h => if hq : q < p then Or.inl ⟨ ⟨ h.1.1, Nat.le_sub_one_of_lt hq ⟩, h.2 ⟩ else Or.inr ⟨ ⟨ not_lt.mp hq, h.1.2 ⟩, h.2 ⟩, fun h => h.elim ( fun h => ⟨ ⟨ h.1.1, by omega ⟩, h.2 ⟩ ) fun h => ⟨ ⟨ by linarith [ hp_prime.two_le ], by omega ⟩, h.2 ⟩ ⟩;
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ), Nat.sub_add_cancel hp_prime.pos ] ;
        rw [ h_primorial_ge, mul_comm ];
        exact Nat.mul_le_mul_right _ ( Nat.le_of_dvd ( Finset.prod_pos fun q hq => Nat.Prime.pos ( by aesop ) ) ( Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, hp_prime ⟩ ) ) );
      rcases p with ( _ | _ | p ) <;> simp_all +decide;
      rw [ Nat.div_le_iff_le_mul_add_pred ] at hp_bounds <;> norm_num at *;
      nlinarith only [ sq p, hp_bounds, h_ind_hyp, h_primorial_ge, hy60, pow_le_pow_left' hp_bounds.1 2 ];
  exact if h : 60 ≤ y then h_ind y h else by interval_cases y <;> decide;

/-
log(primorial(y)) ≤ (7/5)·y for y ≥ Y₂.
-/
lemma log_primorial_le_1p4 : ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
    Real.log (primorial y : ℝ) ≤ 7 / 5 * (y : ℝ) := by
  use 30;
  intro y hy;
  refine' le_trans ( log_primorial_le y ) _;
  rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] ; ring_nf ; norm_num;
  have := Real.log_two_lt_d9 ; norm_num at * ; nlinarith [ ( by norm_cast : ( 30 :ℝ ) ≤ y ) ]

/-! ## CRT construction -/
lemma basic_crt_solution (y : ℕ) (hy : 3 ≤ y) :
    ∃ R : ℕ, R < primorial y ∧
    R % 2 = 1 ∧
    ∀ p : ℕ, p.Prime → p % 2 = 1 → p ≤ y → p ∣ R := by
  refine' ⟨ primorial y / 2, _, _, _ ⟩;
  · refine' Nat.div_lt_self _ _ <;> norm_num;
    exact Nat.pos_of_ne_zero ( by exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) );
  · -- Since $y \geq 3$, we know that $primorial y$ is divisible by $2$ but not by $4$.
    have h_primorial_div : primorial y = 2 * (∏ p ∈ (Finset.filter Nat.Prime (Finset.Icc 3 y)), p) := by
      rw [ primorial ];
      rw [ show ( Finset.filter Nat.Prime ( Finset.range ( y + 1 ) ) ) = { 2 } ∪ Finset.filter Nat.Prime ( Finset.Icc 3 y ) from ?_, Finset.prod_union ] <;> norm_num;
      ext ( _ | _ | _ | p ) <;> simp +arith +decide;
      linarith;
    norm_num [ h_primorial_div, Nat.mul_mod, Finset.prod_nat_mod ];
    rw [ Finset.prod_eq_one ] <;> intros <;> norm_num ; exact Nat.Prime.eq_two_or_odd ( by aesop ) |> Or.resolve_left <| by linarith [ Finset.mem_Icc.mp <| Finset.mem_filter.mp ‹_› |>.1 ] ;
  · intro p pp p1 py; rw [ Nat.dvd_div_iff_mul_dvd ];
    · -- Since $p$ is an odd prime, $2p$ divides the product of all primes up to $y$.
      have h_div : 2 ∣ primorial y ∧ p ∣ primorial y := by
        exact ⟨ prime_dvd_primorial ( by norm_num ) ( by linarith ), prime_dvd_primorial pp py ⟩;
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( Nat.prime_two.coprime_iff_not_dvd.mpr fun h => by have := Nat.mod_eq_zero_of_dvd h; aesop ) h_div.1 h_div.2;
    · exact Nat.dvd_of_mod_eq_zero ( by rw [ Nat.mod_eq_zero_of_dvd ] ; exact Nat.dvd_trans ( by decide ) ( prime_dvd_primorial Nat.prime_two ( by linarith ) ) )
lemma enough_primes_above_y : ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
    4 * (Nat.log 2 (2 * y) + 1) < Nat.primeCounting (y ^ 3) - Nat.primeCounting y := by
  -- By Bertrand's postulate (Nat.exists_infinite_primes), the number of primes ≤ n is unbounded. For a concrete bound, we can use that π(n) ≥ n/(4·log n) for large n (this is available from the pi_lower bound proved in the project, or from similar Mathlib bounds).
  have h_pi_lower : ∃ N : ℕ, ∀ n ≥ N, (Nat.primeCounting n : ℝ) ≥ n / (4 * Real.log n) := by
    -- We'll use the fact that $\pi(n) \geq \frac{n}{4 \log n}$ for sufficiently large $n$.
    have h_lower_bound : ∃ N : ℕ, ∀ n ≥ N, (Nat.primeCounting n : ℝ) ≥ n / (4 * Real.log n) := by
      have h_aux : ∀ n : ℕ, n ≥ 2 → (Nat.primeCounting n : ℝ) ≥ Real.log (Nat.choose n (n / 2)) / Real.log n - 1 := by
        intro n hn
        have h_aux : (Nat.primeCounting n : ℝ) ≥ Real.log (Nat.choose n (n / 2)) / Real.log n - 1 := by
          have h_aux : (Nat.choose n (n / 2) : ℝ) ≤ (n ^ (Nat.primeCounting n + 1) : ℝ) := by
            -- Every prime factor of $\binom{n}{n/2}$ is less than or equal to $n$, and there are at most $\pi(n)$ such primes.
            have h_prime_factors : (Nat.choose n (n / 2) : ℝ) ≤ (∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (p : ℝ) ^ (Nat.factorization (Nat.choose n (n / 2)) p)) := by
              conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( Nat.ne_of_gt ( Nat.choose_pos ( Nat.div_le_self _ _ ) ) ) ];
              rw [ Finsupp.prod_of_support_subset ] <;> norm_num;
              congr! 1;
              intro p hp; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
              exact hp.1.dvd_factorial.mp ( dvd_trans ( Nat.dvd_of_mod_eq_zero hp.2.1 ) ( Nat.choose_mul_factorial_mul_factorial ( show n / 2 ≤ n from Nat.div_le_self _ _ ) ▸ dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _ ) );
            -- Each prime factor $p$ of $\binom{n}{n/2}$ satisfies $p \leq n$, and there are at most $\pi(n)$ such primes.
            have h_prime_factors_bound : (∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (p : ℝ) ^ (Nat.factorization (Nat.choose n (n / 2)) p)) ≤ (∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (n : ℝ)) := by
              apply Finset.prod_le_prod;
              · exact fun _ _ => by positivity;
              · intro p hp; norm_cast; exact Nat.pow_le_of_le_log ( by linarith [ Nat.choose_pos ( show n / 2 ≤ n from Nat.div_le_self _ _ ) ] ) ( by
                                                                                                    apply Nat.factorization_choose_le_log ) ;
            simp_all +decide [ Nat.primeCounting ];
            refine le_trans h_prime_factors <| h_prime_factors_bound.trans ?_;
            rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
            exact pow_le_pow_right₀ ( by norm_cast; linarith ) ( Nat.le_succ _ )
          rw [ ge_iff_le, sub_le_iff_le_add, div_le_iff₀ ];
          · simpa using Real.log_le_log ( Nat.cast_pos.mpr <| Nat.choose_pos <| Nat.div_le_self _ _ ) h_aux;
          · exact Real.log_pos <| Nat.one_lt_cast.mpr hn;
        exact h_aux
      -- We'll use the fact that $\log \binom{n}{n/2} \geq n \log 2 - \log(n+1)$.
      have h_log_binom : ∀ n : ℕ, n ≥ 2 → Real.log (Nat.choose n (n / 2)) ≥ n * Real.log 2 - Real.log (n + 1) := by
        -- We'll use the fact that $\binom{n}{n/2} \geq \frac{2^n}{n+1}$.
        have h_binom_bound : ∀ n : ℕ, n ≥ 2 → (Nat.choose n (n / 2) : ℝ) ≥ 2^n / (n + 1) := by
          intros n hn
          have h_binom_bound : (Nat.choose n (n / 2) : ℝ) ≥ 2^n / (n + 1) := by
            have h_sum : ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) = 2^n := by
              exact_mod_cast Nat.sum_range_choose n
            rw [ ← h_sum, ge_iff_le, div_le_iff₀ ] <;> norm_cast <;> norm_num;
            exact le_trans ( Finset.sum_le_sum fun _ _ => Nat.choose_le_middle _ _ ) ( by simp +decide [ mul_comm ] );
          exact h_binom_bound;
        intro n hn; have := h_binom_bound n hn; replace := Real.log_le_log ( by positivity ) this; rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_pow ] at this; aesop;
      -- We'll use the fact that $\log(n+1) \leq \log n + \log 2$ for $n \geq 2$.
      have h_log_bound : ∀ n : ℕ, n ≥ 2 → Real.log (n + 1) ≤ Real.log n + Real.log 2 := by
        intro n hn; rw [ ← Real.log_mul ( by positivity ) ( by positivity ) ] ; exact Real.log_le_log ( by positivity ) ( by norm_cast; linarith ) ;
      -- We'll use the fact that $\log 2 \approx 0.693$ and $\log n \geq 1$ for $n \geq 3$.
      have h_log_approx : ∃ N : ℕ, ∀ n ≥ N, (n * Real.log 2 - Real.log n - Real.log 2) / Real.log n - 1 ≥ n / (4 * Real.log n) := by
        -- We'll use the fact that $\log 2 \approx 0.693$ and $\log n \geq 1$ for $n \geq 3$ to find such an $N$.
        have h_log_approx : ∃ N : ℕ, ∀ n ≥ N, (n * Real.log 2 - Real.log n - Real.log 2) ≥ n / 4 + Real.log n := by
          have h_log_approx : ∃ N : ℕ, ∀ n ≥ N, (n * (Real.log 2 - 1 / 4)) ≥ 2 * Real.log n + Real.log 2 := by
            have h_log_approx : Filter.Tendsto (fun n : ℕ => (2 * Real.log n + Real.log 2) / n) Filter.atTop (nhds 0) := by
              -- We can use the fact that $\frac{\log n}{n}$ tends to $0$ as $n$ tends to infinity.
              have h_log_div_n : Filter.Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) Filter.atTop (nhds 0) := by
                -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
                suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                  exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
                norm_num;
                exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
              simpa [ add_div, mul_div_assoc ] using Filter.Tendsto.add ( h_log_div_n.const_mul 2 ) ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat );
            have := h_log_approx.eventually ( gt_mem_nhds <| show 0 < Real.log 2 - 1 / 4 by have := Real.log_two_gt_d9; norm_num1 at *; linarith );
            rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; exact ⟨ N + 1, fun n hn => by have := hN n ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩ ;
          exact ⟨ h_log_approx.choose, fun n hn => by linarith [ h_log_approx.choose_spec n hn ] ⟩;
        obtain ⟨ N, hN ⟩ := h_log_approx; use N + 2; intros n hn; rw [ div_sub_one, ge_iff_le, div_le_div_iff₀ ] <;> nlinarith [ hN n ( by linarith ), Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ), Real.log_le_sub_one_of_pos ( show ( n : ℝ ) > 0 by norm_cast; linarith ), mul_div_cancel₀ ( n : ℝ ) ( show ( 4 : ℝ ) ≠ 0 by norm_num ) ] ;
      obtain ⟨ N, hN ⟩ := h_log_approx; use Max.max N 2; intros n hn; specialize hN n ( le_trans ( le_max_left _ _ ) hn ) ; specialize h_aux n ( le_trans ( le_max_right _ _ ) hn ) ; specialize h_log_binom n ( le_trans ( le_max_right _ _ ) hn ) ; specialize h_log_bound n ( le_trans ( le_max_right _ _ ) hn ) ; ring_nf at *;
      by_cases h : Real.log n = 0 <;> simp_all +decide;
      · grobner;
      · nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ) ), Real.log_pos one_lt_two, Real.log_le_sub_one_of_pos zero_lt_two ];
    exact h_lower_bound;
  -- Using the lower bound for π(n), we can derive the required inequality for large y.
  obtain ⟨N, hN⟩ := h_pi_lower;
  have h_contradiction : ∃ Y : ℕ, ∀ y ≥ Y, (y ^ 3 : ℕ) / (4 * Real.log (y ^ 3)) - y > 4 * (Nat.log 2 (2 * y) + 1) := by
    -- We'll use that $Nat.log 2 (2 * y) \leq \log_2(2y) = \log_2(2) + \log_2(y) = 1 + \log_2(y)$.
    have h_log_bound : ∀ y : ℕ, y ≥ 1 → (Nat.log 2 (2 * y) : ℝ) ≤ 1 + Real.log y / Real.log 2 := by
      intro y hy; rw [ add_div', le_div_iff₀ ] <;> norm_num;
      · rw [ ← Real.log_rpow, ← Real.log_mul, Real.log_le_log_iff ] <;> norm_cast <;> try positivity;
        exact Nat.pow_log_le_self 2 ( by positivity );
      · positivity;
    -- Substitute the bound for $Nat.log 2 (2 * y)$ into the inequality.
    suffices h_subst : ∃ Y : ℕ, ∀ y ≥ Y, (y ^ 3 : ℝ) / (12 * Real.log y) - y > 4 * (1 + Real.log y / Real.log 2 + 1) by
      obtain ⟨ Y, hY ⟩ := h_subst; use Max.max Y 2; intros y hy; specialize hY y ( le_trans ( le_max_left _ _ ) hy ) ; specialize h_log_bound y ( by linarith [ le_max_right Y 2 ] ) ; norm_num at * ; ring_nf at * ; linarith;
    -- We'll use that $y^3 / (12 * \log y) - y$ grows faster than $4 * (1 + \log y / \log 2 + 1)$.
    have h_growth : Filter.Tendsto (fun y : ℕ => (y ^ 3 : ℝ) / (12 * Real.log y) / y) Filter.atTop Filter.atTop := by
      -- We can simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun y : ℕ => (y ^ 2 : ℝ) / (12 * Real.log y)) Filter.atTop Filter.atTop by
        refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ eq_div_iff ( by positivity ) ] ; ring );
      -- We can use the change of variables $u = \log y$ to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp (2 * u) / (12 * u)) Filter.atTop Filter.atTop by
        have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Function.comp_apply, mul_comm, Real.exp_mul, Real.exp_log ( Nat.cast_pos.mpr hx ) ] ; norm_cast );
      -- We can use the fact that $\exp(2u) / u$ tends to infinity as $u$ tends to infinity.
      have h_exp_div_u : Filter.Tendsto (fun u : ℝ => Real.exp (2 * u) / u) Filter.atTop Filter.atTop := by
        have := Real.tendsto_exp_div_pow_atTop 1;
        have := this.comp ( Filter.tendsto_id.const_mul_atTop zero_lt_two );
        convert this.const_mul_atTop ( show ( 0 : ℝ ) < 2 by norm_num ) using 2 ; norm_num ; ring;
      convert h_exp_div_u.const_mul_atTop ( by norm_num : ( 0 : ℝ ) < 1 / 12 ) using 2 ; ring;
    have h_growth : Filter.Tendsto (fun y : ℕ => (y ^ 3 : ℝ) / (12 * Real.log y) / y - 1 - 4 * (1 + Real.log y / Real.log 2 + 1) / y) Filter.atTop Filter.atTop := by
      have h_growth : Filter.Tendsto (fun y : ℕ => 4 * (1 + Real.log y / Real.log 2 + 1) / y) Filter.atTop (nhds 0) := by
        -- We can factor out the constant $4$ and use the fact that $\frac{\log y}{y}$ tends to $0$ as $y$ tends to infinity.
        have h_log_div_y : Filter.Tendsto (fun y : ℕ => Real.log y / (y : ℝ)) Filter.atTop (nhds 0) := by
          -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} z \log(1/z)$.
          suffices h_log_recip : Filter.Tendsto (fun z : ℝ => z * Real.log (1 / z)) (Filter.map (fun y => 1 / (y : ℝ)) Filter.atTop) (nhds 0) by
            exact h_log_recip.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
        ring_nf;
        simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using Filter.Tendsto.add ( h_log_div_y.mul_const ( Real.log 2 ) ⁻¹ |> Filter.Tendsto.mul_const 4 ) ( tendsto_inv_atTop_nhds_zero_nat.mul_const 8 );
      exact Filter.Tendsto.atTop_add ( Filter.Tendsto.atTop_add ‹_› tendsto_const_nhds ) ( h_growth.neg );
    have := h_growth.eventually_gt_atTop 0;
    simp +zetaDelta at *;
    obtain ⟨ Y, HY ⟩ := this; exact ⟨ Y + 1, fun y hy => by have := HY y ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; nlinarith [ show ( y : ℝ ) ≥ Y + 1 by exact_mod_cast hy, mul_div_cancel₀ ( ( y : ℝ ) ^ 3 / ( 12 * Real.log y ) ) ( by norm_cast; linarith : ( y : ℝ ) ≠ 0 ) ] ⟩ ;
  obtain ⟨ Y, hY ⟩ := h_contradiction;
  use Max.max N Y + 1; intros y hy; specialize hY y ( by linarith [ le_max_right N Y ] ) ; specialize hN ( y^3 ) ( by nlinarith [ le_max_left N Y, pow_succ y 2 ] ) ; norm_num at *;
  rw [ lt_tsub_iff_left ] at *;
  rw [ ← @Nat.cast_lt ℝ ] ; norm_num;
  refine' lt_of_le_of_lt _ ( lt_of_lt_of_le hY hN );
  norm_num [ Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
  exact le_trans ( Finset.card_le_card ( show Finset.filter Nat.Prime ( Finset.range ( y + 1 ) ) ⊆ Finset.Ico 2 ( y + 1 ) from fun x hx => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le ( Finset.mem_filter.mp hx |>.2 ), Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ⟩ ) ) ( by simp +arith +decide )

/-
For large y, there exists a Finset of distinct primes in (y, y³]
    with at least 2*(log₂(2y)+1) elements.
-/
lemma many_primes_in_range : ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
    ∃ qs : Finset ℕ,
    2 * (Nat.log 2 (2 * y) + 1) ≤ qs.card ∧
    (∀ q ∈ qs, Nat.Prime q ∧ y < q ∧ q ≤ y ^ 3) := by
  -- Use `enough_primes_above_y` which gives ∃ Y, ∀ y ≥ Y, 4*(Nat.log 2 (2*y) + 1) < π(y³) - π(y).
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → 4 * (Nat.log 2 (2 * y) + 1) < Nat.primeCounting (y ^ 3) - Nat.primeCounting y := enough_primes_above_y;
  use Y + 10000; (intro y hy; specialize hY y ( by linarith ) ; norm_num [ Nat.primeCounting, Nat.count_eq_card_filter_range ] at hY ⊢);
  refine' ⟨ Finset.filter Nat.Prime ( Finset.Icc ( y + 1 ) ( y ^ 3 ) ), _, _ ⟩ <;> norm_num [ Nat.primeCounting', Nat.count_eq_card_filter_range ] at *;
  · rw [ show Finset.filter Nat.Prime ( Finset.Icc ( y + 1 ) ( y ^ 3 ) ) = Finset.filter Nat.Prime ( Finset.range ( y ^ 3 + 1 ) ) \ Finset.filter Nat.Prime ( Finset.range ( y + 1 ) ) from ?_, Finset.card_sdiff ];
    · rw [ Finset.inter_eq_left.mpr ] ; linarith! [ Nat.sub_add_cancel <| le_of_lt <| Nat.lt_of_sub_pos <| pos_of_gt hY ] ;
      exact Finset.filter_subset_filter _ <| Finset.range_mono <| by nlinarith [ pow_succ y 2 ] ;
    · grind;
  · tauto

/-
CRT solution for primorial modulus combined with additional distinct primes > y.
-/
lemma crt_primorial_with_extras (y : ℕ) (hy : 3 ≤ y)
    (qs : Finset ℕ) (targets : ℕ → ℕ)
    (hqs_prime : ∀ q ∈ qs, Nat.Prime q)
    (hqs_gt : ∀ q ∈ qs, y < q) :
    ∃ R : ℕ,
    R < primorial y * ∏ q ∈ qs, q ∧
    R % 2 = 1 ∧
    (∀ p : ℕ, p.Prime → p % 2 = 1 → p ≤ y → p ∣ R) ∧
    (∀ q ∈ qs, R % q = targets q % q) := by
  -- Use basic_crt_solution to get R₀ with the basic properties.
  obtain ⟨R₀, hR₀⟩ := basic_crt_solution y hy;
  -- Use crt_coprime_finset with S = {primorial(y)} ∪ qs and target residues R₀ (mod primorial(y)) and targets(q) (mod q).
  obtain ⟨R, hR⟩ : ∃ R, R < primorial y * (∏ q ∈ qs, q) ∧ R % primorial y = R₀ % primorial y ∧ ∀ q ∈ qs, R % q = targets q % q := by
    have h_crt : ∃ R, R % primorial y = R₀ % primorial y ∧ ∀ q ∈ qs, R % q = targets q % q := by
      have h_crt : ∀ {S : Finset ℕ}, (∀ q ∈ S, Nat.Prime q) → (∀ q ∈ S, ¬(q ∣ primorial y)) → ∃ R : ℕ, R % primorial y = R₀ % primorial y ∧ ∀ q ∈ S, R % q = targets q % q := by
        intros S hS_prime hS_not_divorial
        have h_crt : ∀ {a b : ℕ}, Nat.gcd a b = 1 → ∀ {x y : ℕ}, ∃ R : ℕ, R ≡ x [MOD a] ∧ R ≡ y [MOD b] := by
          intros a b hab x y;
          have := Nat.chineseRemainder hab x y;
          exact ⟨ this.val, this.property ⟩;
        induction' S using Finset.induction with q S hqS ih;
        · exact ⟨ R₀, rfl, by simp +decide ⟩;
        · obtain ⟨ R, hR₁, hR₂ ⟩ := ih ( fun q hq => hS_prime q ( Finset.mem_insert_of_mem hq ) ) ( fun q hq => hS_not_divorial q ( Finset.mem_insert_of_mem hq ) );
          obtain ⟨ R', hR'₁, hR'₂ ⟩ := h_crt ( show Nat.gcd ( primorial y * ∏ x ∈ S, x ) q = 1 from Nat.Coprime.mul_left ( Nat.Coprime.symm <| hS_prime q ( Finset.mem_insert_self q S ) |> Nat.Prime.coprime_iff_not_dvd |> Iff.mpr <| hS_not_divorial q ( Finset.mem_insert_self q S ) ) <| Nat.Coprime.prod_left fun x hx => Nat.Coprime.symm <| hS_prime q ( Finset.mem_insert_self q S ) |> Nat.Prime.coprime_iff_not_dvd |> Iff.mpr <| fun h => hqS <| by have := Nat.prime_dvd_prime_iff_eq ( hS_prime q ( Finset.mem_insert_self q S ) ) ( hS_prime x ( Finset.mem_insert_of_mem hx ) ) ; aesop ) ( x := R ) ( y := targets q );
          use R';
          simp_all +decide [ Nat.ModEq ];
          exact ⟨ by simpa using Nat.ModEq.of_dvd ( dvd_mul_right _ _ ) hR'₁ |> Nat.ModEq.trans <| hR₁, fun a ha => by simpa using Nat.ModEq.of_dvd ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ ha ) _ ) hR'₁ |> Nat.ModEq.trans <| hR₂ a ha ⟩;
      apply h_crt hqs_prime;
      intro q hq; specialize hqs_gt q hq; intro hq_div; have := Nat.dvd_trans ( dvd_refl q ) hq_div; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
      contrapose! this; simp_all +decide [ primorial ] ;
      exact Nat.Coprime.prod_right fun p hp => Nat.Prime.coprime_iff_not_dvd ( hqs_prime q hq ) |>.2 fun h => by have := Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) h; linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hp |>.1 ) ] ;
    obtain ⟨ R, hR₁, hR₂ ⟩ := h_crt; use R % ( primorial y * ∏ q ∈ qs, q ) ; simp +decide [ hR₁] ;
    exact ⟨ Nat.mod_lt _ ( Nat.mul_pos ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Finset.prod_pos fun q hq => Nat.Prime.pos ( hqs_prime q hq ) ) ), fun q hq => by rw [ Nat.mod_mod_of_dvd _ ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ hq ) _ ), hR₂ q hq ] ⟩;
  refine' ⟨ R, hR.1, _, _, hR.2.2 ⟩;
  · rw [ ← Nat.mod_mod_of_dvd R ( show 2 ∣ primorial y from ?_ ), hR.2.1, Nat.mod_mod_of_dvd R₀ ( show 2 ∣ primorial y from ?_ ) ] ; aesop;
    · exact prime_dvd_primorial Nat.prime_two ( by linarith );
    · exact prime_dvd_primorial Nat.prime_two ( by linarith );
  · intro p pp p2 py; have := hR.2.1 ▸ Nat.mod_mod_of_dvd R ( prime_dvd_primorial pp py ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
    rw [ ← this, Nat.mod_mod_of_dvd _ ( prime_dvd_primorial pp py ), hR₀.2.2 p pp p2 py ]

/-
Log bound: for large y and primes q₁,...,qₖ ∈ (y, y³] with
    k ≤ 2*(log₂(2y)+1), log(2 * primorial(y) * ∏qᵢ) ≤ 1.42*y.
-/
lemma log_product_bound : ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
    ∀ qs : Finset ℕ,
    qs.card ≤ 2 * (Nat.log 2 (2 * y) + 1) →
    (∀ q ∈ qs, q ≤ y ^ 3) →
    Real.log (2 * (primorial y : ℝ) * ∏ q ∈ qs, (q : ℝ)) ≤ 142 / 100 * (y : ℝ) := by
  -- Use the provided Y from log_primorial_le_1p4.
  obtain ⟨Y₁, hY₁⟩ : ∃ Y₁ : ℕ, ∀ y : ℕ, Y₁ ≤ y → Real.log (primorial y : ℝ) ≤ 7 / 5 * (y : ℝ) := by
    convert log_primorial_le_1p4 using 1;
  -- Use the provided Y from enough_primes_above_y.
  obtain ⟨Y₂, hY₂⟩ : ∃ Y₂ : ℕ, ∀ y : ℕ, Y₂ ≤ y → 2 * (Nat.log 2 (2 * y) + 1) * Real.log (y^3) + Real.log 2 ≤ 142 / 100 * (y : ℝ) - 7 / 5 * (y : ℝ) := by
    -- We'll use that $\log(2y) \leq \log(y) + \log(2)$ and $\log(y^3) = 3\log(y)$ to simplify the expression.
    suffices h_simplified : ∃ Y₂ : ℕ, ∀ y : ℕ, Y₂ ≤ y → 2 * (Real.log (y * 2) / Real.log 2 + 1) * 3 * Real.log y + Real.log 2 ≤ 142 / 100 * (y : ℝ) - 7 / 5 * (y : ℝ) by
      refine' ⟨ h_simplified.choose + 2, fun y hy => le_trans _ ( h_simplified.choose_spec y ( by linarith ) ) ⟩ ; norm_num [ mul_comm ];
      have := Nat.pow_log_le_self 2 ( by linarith : y * 2 ≠ 0 );
      have := Real.log_le_log ( by positivity ) ( show ( 2 : ℝ ) ^ Nat.log 2 ( y * 2 ) ≤ y * 2 by exact_mod_cast this ) ; norm_num at * ; nlinarith [ Real.log_pos one_lt_two, Real.log_pos ( show ( y : ℝ ) > 1 by norm_cast; linarith ), mul_div_cancel₀ ( Real.log ( y * 2 ) ) ( ne_of_gt ( Real.log_pos one_lt_two ) ) ] ;
    -- We'll use that $\log(y) / y \to 0$ as $y \to \infty$.
    have h_log_div_y_zero : Filter.Tendsto (fun y : ℕ => Real.log y / (y : ℝ)) Filter.atTop (nhds 0) := by
      -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} z \log(1/z)$.
      suffices h_log_recip : Filter.Tendsto (fun z : ℝ => z * Real.log (1 / z)) (Filter.map (fun y => 1 / (y : ℝ)) Filter.atTop) (nhds 0) by
        exact h_log_recip.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    -- We'll use that $\log(y) / y \to 0$ as $y \to \infty$ to find such a $Y₂$.
    have h_log_div_y_zero : Filter.Tendsto (fun y : ℕ => (2 * (Real.log (y * 2) / Real.log 2 + 1) * 3 * Real.log y + Real.log 2) / (y : ℝ)) Filter.atTop (nhds 0) := by
      -- We can factor out $y$ in the numerator and use the fact that $\log(y) / y \to 0$.
      have h_factor : Filter.Tendsto (fun y : ℕ => (Real.log y / (y : ℝ)) * (2 * (Real.log y / Real.log 2 + Real.log 2 / Real.log 2 + 1) * 3) + Real.log 2 / (y : ℝ)) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $\log(y) / y \to 0$ as $y \to \infty$.
        have h_log_div_y_zero : Filter.Tendsto (fun y : ℕ => (Real.log y / (y : ℝ)) * (Real.log y / Real.log 2)) Filter.atTop (nhds 0) := by
          have h_log_div_y_zero : Filter.Tendsto (fun y : ℕ => (Real.log y ^ 2) / (y : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $z = \log y$, therefore the expression becomes $\frac{z^2}{e^z}$.
            suffices h_log_sq_div_exp : Filter.Tendsto (fun z : ℝ => z^2 / Real.exp z) Filter.atTop (nhds 0) by
              have := h_log_sq_div_exp.comp Real.tendsto_log_atTop;
              exact this.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.exp_log ( Nat.cast_pos.mpr hx ) ] );
            simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
          convert h_log_div_y_zero.div_const ( Real.log 2 ) using 2 <;> ring;
        convert Filter.Tendsto.add ( h_log_div_y_zero.mul_const ( 2 * 3 ) |> Filter.Tendsto.add <| ‹Filter.Tendsto ( fun y : ℕ => Real.log y / ( y : ℝ ) ) Filter.atTop ( nhds 0 ) ›.mul_const ( 2 * 3 * ( Real.log 2 / Real.log 2 + 1 ) ) ) ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) using 2 <;> ring;
      convert h_factor using 2 ; by_cases hy : ( ‹_› : ℕ ) = 0 <;> simp +decide [ hy, Real.log_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ; ring;
    exact Filter.eventually_atTop.mp ( h_log_div_y_zero.eventually ( gt_mem_nhds <| show 0 < 142 / 100 - 7 / 5 by norm_num ) ) |> fun ⟨ Y₂, hY₂ ⟩ ↦ ⟨ Y₂ + 1, fun y hy ↦ by have := hY₂ y ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩ ;
  refine' ⟨ Max.max Y₁ Y₂ + 1, fun y hy qs hqs₁ hqs₂ => _ ⟩ ; rcases eq_or_ne ( ∏ q ∈ qs, ( q : ℝ ) ) 0 with h | h <;> simp_all +decide [Finset.prod_eq_zero_iff];
  · rw [ Finset.prod_eq_zero h ] <;> norm_num;
  · rw [ Real.log_mul, Real.log_mul ] <;> norm_num;
    · nontriviality;
      refine' le_trans ( add_le_add_three le_rfl ( hY₁ y hy.1.le ) ( Real.log_le_log ( Finset.prod_pos fun q hq => Nat.cast_pos.mpr <| Nat.pos_of_ne_zero fun hq' => h <| by aesop ) <| show ( ∏ q ∈ qs, ( q : ℝ ) ) ≤ ( y ^ 3 ) ^ qs.card from _ ) ) _;
      · exact le_trans ( Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) fun _ _ => Nat.cast_le.mpr ( hqs₂ _ ‹_› ) ) ( by norm_num );
      · have := hY₂ y hy.2.le;
        norm_num [ Real.log_pow ] at * ; nlinarith [ ( by norm_cast : ( qs.card :ℝ ) ≤ 2 * ( Nat.log 2 ( 2 * y ) + 1 ) ), Real.log_nonneg ( show ( y :ℝ ) ≥ 1 by norm_cast; linarith ) ];
    · exact Nat.ne_of_gt <| primorial_pos _;
    · exact Nat.ne_of_gt <| primorial_pos _;
    · exact Finset.prod_ne_zero_iff.mpr fun q hq => Nat.cast_ne_zero.mpr <| by aesop;

/-
The number of integers d = ±2^a with a ≥ 1 and |d| ≤ 2y is at most
    2*(log₂(2y)+1).
-/
lemma injection_from_card_le {E : Finset ℤ} {qs : Finset ℕ}
    (hcard : E.card ≤ qs.card) :
    ∃ f : ℤ → ℕ, (∀ d ∈ E, f d ∈ qs) ∧
    (∀ d₁ ∈ E, ∀ d₂ ∈ E, d₁ ≠ d₂ → f d₁ ≠ f d₂) := by
  -- Since $E$ is finite, we can enumerate its elements and define $f$ accordingly.
  obtain ⟨f, hf⟩ : ∃ f : Fin (Finset.card E) → ℕ, (∀ i, f i ∈ qs) ∧ (∀ i j, i ≠ j → f i ≠ f j) := by
    exact ⟨ fun i => qs.orderEmbOfFin rfl ⟨ i, by linarith [ Fin.is_lt i ] ⟩, fun i => Finset.orderEmbOfFin_mem _ _ _, fun i j hij => by contrapose! hij; aesop ⟩;
  -- Since $E$ is finite, we can enumerate its elements and define $f$ accordingly. Use this enumeration to construct the desired function.
  obtain ⟨g, hg⟩ : ∃ g : E ≃ Fin (Finset.card E), True := by
    exact ⟨ Fintype.equivOfCardEq <| by simp +decide, trivial ⟩;
  use fun d => if hd : d ∈ E then f ( g ⟨ d, hd ⟩ ) else 0;
  simp_all +decide [ Fin.ext_iff ];
  exact fun d₁ hd₁ d₂ hd₂ h => hf.2 _ _ <| by simpa [ Fin.ext_iff ] using fun h' => h <| by simpa [ Fin.ext_iff ] using g.injective <| Fin.ext h';

/-
For d : ℤ and q : ℕ with q prime, if R % q = ((-d) % q).toNat then q | (R : ℤ) + d.
-/
lemma mod_neg_dvd_add (R : ℕ) (d : ℤ) (q : ℕ) (hq : Nat.Prime q)
    (h : R % q = ((-d) % (q : ℤ)).toNat % q) :
    (q : ℤ) ∣ ((R : ℤ) + d) := by
  have h_congr : (R : ℤ) % q = (-d) % q := by
    convert congr_arg ( ( ↑ ) : ℕ → ℤ ) h using 1;
    simp +decide [ Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hq.ne_zero ) ];
  exact Int.dvd_of_emod_eq_zero ( by rw [ Int.add_emod, h_congr ] ; norm_num )

/-- Given enough primes qs in (y, y³], construct R satisfying
    basic conditions and the exceptional d conditions. -/
lemma crt_exceptional_assignment (y : ℕ) (hy : 3 ≤ y)
    (qs : Finset ℕ)
    (hqs_card : 2 * (Nat.log 2 (2 * y) + 1) ≤ qs.card)
    (hqs_prime : ∀ q ∈ qs, Nat.Prime q)
    (hqs_gt : ∀ q ∈ qs, y < q) :
    ∃ R : ℕ,
    R < primorial y * ∏ q ∈ qs, q ∧
    R % 2 = 1 ∧
    (∀ p : ℕ, p.Prime → p % 2 = 1 → p ≤ y → p ∣ R) ∧
    (∀ d : ℤ, (1 : ℤ) - ↑y ≤ d → d ≤ 2 * ↑y → d ≠ 0 →
      (∃ a : ℕ, a ≥ 1 ∧ (d = (2 : ℤ) ^ a ∨ d = -(2 : ℤ) ^ a)) →
      ∃ q ∈ qs, (q : ℤ) ∣ ((R : ℤ) + d)) := by
  -- Define the exceptional set E (use bounded quantifier for decidability)
  set E : Finset ℤ := (Finset.Icc 1 (Nat.log 2 (2 * y))).image (fun a : ℕ => (2 : ℤ) ^ a) ∪
    (Finset.Icc 1 (Nat.log 2 (2 * y))).image (fun a : ℕ => -(2 : ℤ) ^ a)
  -- E.card ≤ qs.card
  have hE_card : E.card ≤ qs.card := by
    refine le_trans ?_ hqs_card
    refine le_trans (Finset.card_union_le _ _) ?_
    have h2_inj : Function.Injective (fun a : ℕ => (2 : ℤ) ^ a) := by
      intro a b h; exact Nat.pow_right_injective (by norm_num : 2 ≤ 2)
        (show (2 : ℕ)^a = 2^b by zify; simpa using h)
    have hn2_inj : Function.Injective (fun a : ℕ => -(2 : ℤ) ^ a) := by
      intro a b h; exact h2_inj (neg_injective h)
    rw [Finset.card_image_of_injective _ h2_inj, Finset.card_image_of_injective _ hn2_inj]
    simp [Nat.card_Icc]; ring_nf; linarith
  -- E contains all exceptional d values
  have hE_complete : ∀ d : ℤ, (1 : ℤ) - ↑y ≤ d → d ≤ 2 * ↑y → d ≠ 0 →
      (∃ a : ℕ, a ≥ 1 ∧ (d = (2 : ℤ) ^ a ∨ d = -(2 : ℤ) ^ a)) → d ∈ E := by
    intro d _ hd2 _ ⟨a, ha1, ha2⟩
    simp only [E, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    rcases ha2 with rfl | rfl
    · left; exact ⟨a, ⟨ha1, Nat.le_log_of_pow_le (by norm_num) (by exact_mod_cast hd2)⟩, rfl⟩
    · right; exact ⟨a, ⟨ha1, Nat.le_log_of_pow_le (by norm_num) (by linarith)⟩, rfl⟩
  -- Get injection f : ℤ → ℕ
  obtain ⟨f, hf_mem, hf_inj⟩ := injection_from_card_le hE_card
  -- Define targets using f (sum over preimage, which has exactly one element by injectivity)
  let targets : ℕ → ℕ := fun q =>
    (E.filter (fun d => decide (f d = q))).sum (fun d => ((-d : ℤ) % (↑q : ℤ)).toNat)
  -- Apply CRT
  obtain ⟨R, hR_lt, hR_odd, hR_div, hR_crt⟩ :=
    crt_primorial_with_extras y hy qs targets hqs_prime hqs_gt
  refine ⟨R, hR_lt, hR_odd, hR_div, ?_⟩
  -- Verify exceptional condition
  intro d hd1 hd2 hd3 hd4
  have hd_mem : d ∈ E := hE_complete d hd1 hd2 hd3 hd4
  refine ⟨f d, hf_mem d hd_mem, ?_⟩
  apply mod_neg_dvd_add R d (f d) (hqs_prime (f d) (hf_mem d hd_mem))
  have h_targets : targets (f d) = ((-d : ℤ) % (↑(f d) : ℤ)).toNat := by
    -- The filter E.filter(fun d' => f d' = f d) = {d} by injectivity of f on E
    have h_filter : E.filter (fun d' => decide (f d' = f d)) = {d} := by
      ext d'; simp only [Finset.mem_filter, Finset.mem_singleton, decide_eq_true_eq]
      constructor
      · intro ⟨hd'_mem, hd'_eq⟩
        by_contra h_ne
        exact absurd hd'_eq (hf_inj d' hd'_mem d hd_mem h_ne)
      · intro h; subst h; exact ⟨hd_mem, rfl⟩
    show (E.filter (fun d' => decide (f d' = f d))).sum
        (fun d' => ((-d' : ℤ) % (↑(f d) : ℤ)).toNat) = _
    rw [h_filter, Finset.sum_singleton]
  rw [hR_crt (f d) (hf_mem d hd_mem), h_targets]

/-
For large y, there exists B satisfying all necessary conditions.
-/
lemma full_crt_construction : ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
    ∃ B : ℕ,
    B % 2 = 1 ∧
    (∀ p : ℕ, p.Prime → p % 2 = 1 → p ≤ y → p ∣ B) ∧
    y ^ 3 + y < B ∧
    (∀ d : ℤ, (1 : ℤ) - ↑y ≤ d → d ≤ 2 * ↑y → d ≠ 0 →
      (∃ a : ℕ, a ≥ 1 ∧ (d = (2 : ℤ) ^ a ∨ d = -(2 : ℤ) ^ a)) →
      ∃ q : ℕ, q.Prime ∧ y < q ∧ q ≤ y ^ 3 ∧ (q : ℤ) ∣ ((B : ℤ) + d)) ∧
    Real.log (B : ℝ) ≤ 142 / 100 * (y : ℝ) := by
  -- Set Y = max(Y₁, max(Y₂, 30)).
  obtain ⟨Y₁, hY₁⟩ := many_primes_in_range
  obtain ⟨Y₂, hY₂⟩ := log_product_bound
  use max Y₁ (max Y₂ 30) + 1;
  intro y hy
  obtain ⟨qs, hqs_card, hqs_prime⟩ := hY₁ y (by
  linarith [ Nat.le_max_left Y₁ ( Max.max Y₂ 30 ) ])
  obtain ⟨qs', hqs'_card, hqs'_subset⟩ : ∃ qs' : Finset ℕ, qs'.card = 2 * (Nat.log 2 (2 * y) + 1) ∧ qs' ⊆ qs := by
    exact Exists.elim ( Finset.exists_subset_card_eq hqs_card ) fun s hs => ⟨ s, hs.2, hs.1 ⟩;
  obtain ⟨R, hR⟩ := crt_exceptional_assignment y (by
  linarith [ Nat.le_max_left Y₁ ( Max.max Y₂ 30 ), Nat.le_max_right Y₁ ( Max.max Y₂ 30 ), Nat.le_max_left Y₂ 30, Nat.le_max_right Y₂ 30 ]) qs' (by
  linarith) (by
  exact fun q hq => hqs_prime q ( hqs'_subset hq ) |>.1) (by
  exact fun q hq => hqs_prime q ( hqs'_subset hq ) |>.2.1);
  refine' ⟨ R + primorial y * ∏ q ∈ qs', q, _, _, _, _, _ ⟩ <;> simp_all +decide [Nat.dvd_add_right];
  · norm_num [ Nat.add_mod, Nat.mul_mod, hR.2.1 ];
    rw [ show primorial y % 2 = 0 from Nat.mod_eq_zero_of_dvd <| prime_dvd_primorial Nat.prime_two <| by linarith ] ; norm_num;
  · exact fun p pp p1 py => dvd_mul_of_dvd_left ( prime_dvd_primorial pp py ) _;
  · -- Since $primorial y > 2y^3 + y$ and $\prod_{q \in qs'} q \geq 1$, we have $primorial y * \prod_{q \in qs'} q > 2y^3 + y$.
    have h_primorial_prod : primorial y * ∏ q ∈ qs', q > 2 * y ^ 3 + y := by
      exact lt_of_lt_of_le ( primorial_gt_double_cube y ( by linarith ) ) ( Nat.le_mul_of_pos_right _ <| Finset.prod_pos fun q hq => Nat.Prime.pos <| by have := hqs_prime q ( hqs'_subset hq ) ; aesop );
    grind;
  · intro d hd₁ hd₂ hd₃ x hx₁ hx₂; obtain ⟨ q, hq₁, hq₂ ⟩ := hR.2.2.2 d hd₁ hd₂ hd₃ x hx₁ hx₂; use q; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
    simp_all +decide [ Finset.prod_eq_prod_diff_singleton_mul hq₁ ];
    exact hqs_prime q ( hqs'_subset hq₁ );
  · refine' le_trans _ ( hY₂ y ( by linarith ) qs' ( by linarith ) ( fun q hq => hqs_prime q ( hqs'_subset hq ) |>.2.2 ) );
    gcongr ; norm_cast;
    · exact add_pos_of_nonneg_of_pos ( Nat.cast_nonneg _ ) ( mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ( Finset.prod_pos fun q hq => Nat.cast_pos.mpr ( Nat.Prime.pos ( hqs_prime q ( hqs'_subset hq ) |>.1 ) ) ) );
    · rw [ ← Nat.cast_prod ] ; norm_cast ; nlinarith [ show 0 < primorial y * ∏ q ∈ qs', q from mul_pos ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Finset.prod_pos fun q hq => Nat.Prime.pos ( hqs_prime q ( hqs'_subset hq ) |>.1 ) ) ] ;

/-! ## Composite run existence -/

theorem composite_run_exists' : ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
    ∃ B : ℕ, (∀ d : ℤ, (1 : ℤ) - ↑y ≤ d → d ≤ 2 * ↑y →
      1 < ((B : ℤ) + d).toNat ∧ ¬((B : ℤ) + d).toNat.Prime) ∧
    (y : ℝ) ^ 3 < (B : ℝ) ∧
    Real.log (B : ℝ) ≤ 142 / 100 * (y : ℝ) := by
  obtain ⟨Y, hY⟩ := full_crt_construction
  use max Y 30
  intro y hy
  obtain ⟨B, hBodd, hBdiv, hBgt, hexc, hlog⟩ := hY y (le_of_max_le_left hy)
  exact ⟨B,
    composite_of_construction B y (le_of_max_le_right hy) hBodd hBdiv hBgt hexc,
    by exact_mod_cast show y ^ 3 < B by linarith,
    hlog⟩

/-- For sufficiently large y, there exists a natural number B such that:
1. All integers in [B+1-y, B+2y] are composite (> 1 and not prime)
2. B > y³
3. log B ≤ (142/100) * y
-/
theorem composite_run_exists : ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
    ∃ B : ℕ, (∀ d : ℤ, (1 : ℤ) - ↑y ≤ d → d ≤ 2 * ↑y →
      1 < ((B : ℤ) + d).toNat ∧ ¬((B : ℤ) + d).toNat.Prime) ∧
    (y : ℝ) ^ 3 < (B : ℝ) ∧
    Real.log (B : ℝ) ≤ 142 / 100 * (y : ℝ) := composite_run_exists'

/-- From a composite run, we can extract consecutive primes bounding it. -/
theorem gap_from_composite_run (B y : ℕ) (hy : 3 ≤ y)
    (hcomp : ∀ d : ℤ, (1 : ℤ) - ↑y ≤ d → d ≤ 2 * ↑y →
      1 < ((B : ℤ) + d).toNat ∧ ¬((B : ℤ) + d).toNat.Prime)
    (hB : y ^ 3 < B) :
    ∃ (p q : ℕ), p.Prime ∧ q.Prime ∧ p < q ∧
      (∀ r : ℕ, p < r → r < q → ¬r.Prime) ∧
      p ≤ B - y ∧ B + 2 * y < q ∧ 3 * y ≤ q - p := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ≤ B - y ∧ ∀ r : ℕ, Nat.Prime r → r ≤ B - y → r ≤ p := by
    exact ⟨ Finset.max' ( Finset.filter Nat.Prime ( Finset.Iic ( B - y ) ) ) ⟨ 2, Finset.mem_filter.mpr ⟨ Finset.mem_Iic.mpr ( Nat.le_sub_of_add_le ( by nlinarith [ pow_succ' y 2 ] ) ), Nat.prime_two ⟩ ⟩, Finset.mem_filter.mp ( Finset.max'_mem _ _ ) |>.2, Finset.mem_Iic.mp ( Finset.mem_filter.mp ( Finset.max'_mem _ _ ) |>.1 ), fun r hr hr' => Finset.le_max' _ _ ( by aesop ) ⟩;
  obtain ⟨q, hq⟩ : ∃ q : ℕ, Nat.Prime q ∧ B + 2 * y < q ∧ ∀ r : ℕ, Nat.Prime r → B + 2 * y < r → q ≤ r := by
    exact ⟨ Nat.find ( Nat.exists_infinite_primes ( B + 2 * y + 1 ) ), Nat.find_spec ( Nat.exists_infinite_primes ( B + 2 * y + 1 ) ) |>.2, Nat.find_spec ( Nat.exists_infinite_primes ( B + 2 * y + 1 ) ) |>.1, fun r hr hr' => Nat.find_min' ( Nat.exists_infinite_primes ( B + 2 * y + 1 ) ) ⟨ by linarith, hr ⟩ ⟩;
  refine' ⟨ p, q, hp.1, hq.1, _, _, hp.2.1, hq.2.1, _ ⟩;
  · omega;
  · intro r hr₁ hr₂ hr₃; contrapose! hr₂;
    by_cases hr₄ : r ≤ B + 2 * y;
    · have := hcomp ( r - B ) ?_ ?_ <;> norm_num at *;
      · tauto;
      · grind;
      · linarith;
    · exact hq.2.2 r hr₃ ( not_le.mp hr₄ );
  · have := hcomp ( 1 - y ) ( by linarith ) ( by linarith ) ; simp_all +decide [ add_comm ] ;
    grind +suggestions

/-
The maximal prime gap below x exceeds 2 log x for all sufficiently large x.
-/
theorem exists_large_prime_gap :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∃ (p q : ℕ), p.Prime ∧ q.Prime ∧
      p < q ∧ (∀ r : ℕ, p < r → r < q → ¬r.Prime) ∧
      (q : ℝ) < x ∧ 2 * Real.log x < (q - p : ℝ) := by
  -- From composite_run_exists, get Y₀.
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀ : ℕ, ∀ y : ℕ, Y₀ ≤ y →
      ∃ B : ℕ, (∀ d : ℤ, (1 : ℤ) - ↑y ≤ d → d ≤ 2 * ↑y →
        1 < ((B : ℤ) + d).toNat ∧ ¬((B : ℤ) + d).toNat.Prime) ∧
      (y : ℝ) ^ 3 < (B : ℝ) ∧ Real.log (B : ℝ) ≤ 142 / 100 * (y : ℝ) := composite_run_exists;
  -- Choose x₀ large enough that:
  -- - y = ⌊(7/10) log x⌋ ≥ Y₀
  -- - y ≥ 3
  -- - x^0.994 + 1.4 log x < x/2 (equivalently, 2·exp((142/100)y) + 4y < x)
  -- - 3y > 2 log x (equivalently, (21/10) log x - 3 > 2 log x, i.e., log x > 30)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, 10^30 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
    let y := Nat.floor ((7 / 10 : ℝ) * Real.log x)
    Y₀ ≤ y ∧ 3 ≤ y ∧
    2 * Real.exp ((142 / 100 : ℝ) * y) + 4 * y < x ∧
    3 * y > 2 * Real.log x := by
      -- Choose x₀ large enough such that for all x ≥ x₀, the conditions hold.
      obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, 10^30 ≤ x₁ ∧ ∀ x : ℝ, x₁ ≤ x →
        let y := Nat.floor ((7 / 10 : ℝ) * Real.log x)
        Y₀ ≤ y ∧ 3 ≤ y ∧ 3 * y > 2 * Real.log x := by
          have hx₁ : ∃ x₁ : ℝ, 10^30 ≤ x₁ ∧ ∀ x : ℝ, x₁ ≤ x →
            let y := Nat.floor ((7 / 10 : ℝ) * Real.log x)
            Y₀ ≤ y ∧ 3 ≤ y := by
              have hx₁ : Filter.Tendsto (fun x : ℝ => Nat.floor ((7 / 10 : ℝ) * Real.log x)) Filter.atTop Filter.atTop := by
                exact tendsto_nat_floor_atTop.comp <| Filter.Tendsto.const_mul_atTop ( by norm_num ) <| Real.tendsto_log_atTop;
              exact Filter.eventually_atTop.mp ( hx₁.eventually_ge_atTop ( Max.max Y₀ 3 ) ) |> fun ⟨ x₁, hx₁ ⟩ ↦ ⟨ Max.max x₁ ( 10^30 ), le_max_right _ _, fun x hx ↦ ⟨ le_trans ( le_max_left _ _ ) ( hx₁ x ( le_trans ( le_max_left _ _ ) hx ) ), le_trans ( le_max_right _ _ ) ( hx₁ x ( le_trans ( le_max_left _ _ ) hx ) ) ⟩ ⟩;
          obtain ⟨ x₁, hx₁₁, hx₁₂ ⟩ := hx₁; use Max.max x₁ ( Real.exp 30 ) ; norm_num at *;
          exact ⟨ Or.inl hx₁₁, fun x hx₁ hx₂ => ⟨ hx₁₂ x hx₁ |>.1, hx₁₂ x hx₁ |>.2, by linarith [ Nat.lt_floor_add_one ( 7 / 10 * Real.log x ), Real.log_exp 30, Real.log_le_log ( by positivity ) hx₂ ] ⟩ ⟩;
      -- Choose x₀ large enough such that for all x ≥ x₀, the condition 2 * exp((142/100)y) + 4y < x holds.
      obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ℝ, ∀ x : ℝ, x₂ ≤ x →
        2 * Real.exp ((142 / 100 : ℝ) * ((7 / 10 : ℝ) * Real.log x)) + 4 * ((7 / 10 : ℝ) * Real.log x) < x := by
          -- We'll use that exponential functions grow faster than linear functions.
          have h_exp_growth : Filter.Tendsto (fun x : ℝ => (2 * Real.exp ((142 / 100 : ℝ) * ((7 / 10 : ℝ) * Real.log x)) + 4 * ((7 / 10 : ℝ) * Real.log x)) / x) Filter.atTop (nhds 0) := by
            -- We can factor out $x^{0.994}$ from the numerator and denominator.
            suffices h_factor : Filter.Tendsto (fun x : ℝ => (2 * x ^ (142 / 100 * (7 / 10 : ℝ)) + 4 * (7 / 10 : ℝ) * Real.log x) / x) Filter.atTop (nhds 0) by
              refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.rpow_def_of_pos hx ] ; ring_nf );
            -- We can divide the numerator and the denominator by $x$.
            suffices h_div : Filter.Tendsto (fun x : ℝ => 2 * x ^ ((142 / 100 * (7 / 10) : ℝ) - 1) + 4 * (7 / 10) * (Real.log x) / x) Filter.atTop (nhds 0) by
              refine h_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.rpow_sub_one hx.ne' ] ; ring );
            -- We'll use the fact that $\frac{\log x}{x}$ tends to $0$ as $x$ tends to infinity.
            have h_log_x_over_x : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
              -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
              suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
              norm_num;
              exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
            simpa [ mul_div_assoc ] using Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop ( by norm_num : ( 0 : ℝ ) < - ( 142 / 100 * ( 7 / 10 ) - 1 ) ) ) ) ( h_log_x_over_x.const_mul _ );
          exact Filter.eventually_atTop.mp ( h_exp_growth.eventually ( gt_mem_nhds zero_lt_one ) ) |> fun ⟨ x₂, hx₂ ⟩ ↦ ⟨ Max.max x₂ 1, fun x hx ↦ by have := hx₂ x ( le_trans ( le_max_left _ _ ) hx ) ; rw [ div_lt_iff₀ ] at this <;> linarith [ le_max_right x₂ 1 ] ⟩;
      refine' ⟨ Max.max x₁ x₂, _, _ ⟩ <;> norm_num;
      · exact Or.inl <| mod_cast hx₁.1;
      · intro x hx₁' hx₂'; specialize hx₁; specialize hx₂ x hx₂'; norm_num at *;
        refine' ⟨ hx₁.2 x hx₁' |>.1, hx₁.2 x hx₁' |>.2.1, _, hx₁.2 x hx₁' |>.2.2 ⟩;
        refine' lt_of_le_of_lt _ hx₂;
        gcongr;
        · exact Nat.floor_le ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith ) ) );
        · exact Nat.floor_le ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith ) ) );
  refine' ⟨ x₀, by linarith, fun x hx => _ ⟩ ; specialize hx₀ ; have := hx₀.2 x hx ; norm_num at *;
  obtain ⟨ B, hB₁, hB₂, hB₃ ⟩ := hY₀ _ this.1;
  -- From the composite run, extract a prime gap.
  obtain ⟨ p, q, hp_prime, hq_prime, hpq, h_no_prime, hpB, hqB, hgap ⟩ := gap_from_composite_run B (Nat.floor ((7 / 10 : ℝ) * Real.log x)) (by linarith) (by
  grind) (by
  exact_mod_cast hB₂);
  refine' ⟨ p, hp_prime, q, hq_prime, hpq, h_no_prime, _, _ ⟩;
  · -- Since $q$ is the smallest prime greater than $B + 2y$, and $2(B + 2y) \leq x$, we have $q \leq 2(B + 2y)$.
    have hq_le_2B2y : (q : ℝ) ≤ 2 * (B + 2 * ⌊7 / 10 * Real.log x⌋₊) := by
      have hq_le_2B2y : ∃ r : ℕ, Nat.Prime r ∧ B + 2 * ⌊7 / 10 * Real.log x⌋₊ < r ∧ r ≤ 2 * (B + 2 * ⌊7 / 10 * Real.log x⌋₊) := by
        have := Nat.exists_prime_lt_and_le_two_mul ( B + 2 * ⌊7 / 10 * Real.log x⌋₊ ) ?_ <;> norm_num at *;
        · exact this;
        · norm_cast at * ; aesop;
      contrapose! h_no_prime;
      obtain ⟨ r, hr₁, hr₂, hr₃ ⟩ := hq_le_2B2y; exact ⟨ r, by linarith [ Nat.sub_le B ⌊7 / 10 * Real.log x⌋₊ ], by norm_cast at *; linarith, hr₁ ⟩ ;
    refine' lt_of_le_of_lt hq_le_2B2y _;
    have := Real.log_le_iff_le_exp ( by norm_cast; contrapose! hB₂; aesop ) |>.1 hB₃;
    linarith [ hx₀.2 x hx ];
  · refine' lt_of_lt_of_le this.2.2.2 _;
    exact le_tsub_of_add_le_left ( by norm_cast; omega )

/-! ## Key properties of primes -/

lemma primes_infinite : {p : ℕ | p.Prime}.Infinite := Nat.infinite_setOf_prime

lemma nthPrime'_prime (n : ℕ) : (nthPrime' n).Prime :=
  Nat.nth_mem_of_infinite primes_infinite n

lemma nthPrime'_strictMono : StrictMono nthPrime' :=
  Nat.nth_strictMono primes_infinite

lemma nthPrime'_lt_succ (n : ℕ) : nthPrime' n < nthPrime' (n + 1) :=
  nthPrime'_strictMono (Nat.lt_succ_self n)

lemma primeGap_pos (n : ℕ) : 0 < primeGap n :=
  Nat.sub_pos_of_lt (nthPrime'_lt_succ n)

lemma no_prime_between_consecutive (n : ℕ) (q : ℕ)
    (h1 : nthPrime' n < q) (h2 : q < nthPrime' (n + 1)) :
    ¬q.Prime := by
  contrapose! h2; have := Nat.exists_prime_lt_and_le_two_mul q; simp_all +decide ;
  unfold nthPrime' at *;
  rw [ Nat.nth_eq_sInf ];
  exact Nat.sInf_le ⟨ h2, fun k hk => lt_of_le_of_lt ( Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by linarith ) ) h1 ⟩

/-! ## Admissibility with enlarged threshold -/

lemma admissible_large_threshold {c : ℝ} {γ : ℝ}
    (hc : ∀ δ : ℝ, 0 < δ → δ < γ → ∀ ε : ℝ, 0 < ε →
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ y : ℝ, (1/2 + δ) * x < y → y < (1 + δ) * x →
        |((Delta c x y : ℤ) : ℝ) - c * (D x : ℝ) / Real.log y| ≤
          ε * |c| * (D x : ℝ) / Real.log y)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < γ)
    {ε : ℝ} (hε : 0 < ε) (W : ℝ) :
    ∃ X : ℝ, max W 3 ≤ X ∧
    ∀ x : ℝ, X ≤ x →
    ∀ y : ℝ, (1/2 + δ) * x < y → y < (1 + δ) * x →
    |((Delta c x y : ℤ) : ℝ) - c * (D x : ℝ) / Real.log y| ≤
      ε * |c| * (D x : ℝ) / Real.log y := by
  obtain ⟨X₀, hX₀⟩ := hc δ hδ0 hδ1 ε hε
  exact ⟨max (max W 3) X₀, le_max_left _ _, fun x hx y hy1 hy2 =>
    hX₀ x (le_trans (le_max_right _ _) hx) y hy1 hy2⟩

/-- **PNT epsilon form**.
    Derived from `pi_alt`. -/
lemma pnt_epsilon : ∀ ε : ℝ, 0 < ε →
  ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t →
    (1 - ε) * t / Real.log t ≤ (piReal t : ℝ) ∧
    (piReal t : ℝ) ≤ (1 + ε) * t / Real.log t := by
  obtain ⟨c, hc_small, hc_eq⟩ := pi_alt
  intro ε hε
  -- Since c =o[atTop] 1, for large t, |c(t)| < ε
  rw [Asymptotics.isLittleO_one_iff] at hc_small
  rw [Filter.Tendsto] at hc_small
  have hev := hc_small (Metric.ball_mem_nhds 0 hε)
  simp [Metric.mem_ball] at hev
  obtain ⟨T₀, hT₀⟩ := hev
  refine ⟨max T₀ (Real.exp 1), lt_of_lt_of_le (Real.exp_pos 1) (le_max_right _ _), fun t ht => ?_⟩
  have hT₀t : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht_pos : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) (le_trans (le_max_right _ _) ht)
  have hlog_pos : 0 < Real.log t := by
    exact Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < Real.exp 1) (le_trans (le_max_right _ _) ht))
  have hc_bound : |c t| < ε := hT₀ t hT₀t
  have hc_le : c t ≤ ε := le_of_lt (abs_lt.mp hc_bound).2
  have hc_ge : -ε ≤ c t := le_of_lt (abs_lt.mp hc_bound).1
  have hpi : (piReal t : ℝ) = (1 + c t) * t / Real.log t := by
    unfold piReal; exact_mod_cast hc_eq t
  rw [hpi]
  constructor
  · apply div_le_div_of_nonneg_right _ hlog_pos.le
    exact mul_le_mul_of_nonneg_right (by linarith) ht_pos.le
  · apply div_le_div_of_nonneg_right _ hlog_pos.le
    exact mul_le_mul_of_nonneg_right (by linarith) ht_pos.le

/-
For every `lam > 1`, for large enough `t`, there is a prime in `(t, lam*t]`.
-/
lemma multiplicative_prime_interval {lam : ℝ} (hlam : 1 < lam) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t →
    ∃ p : ℕ, p.Prime ∧ t < (p : ℝ) ∧ (p : ℝ) ≤ lam * t := by
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℝ, 0 < T₁ ∧ ∀ t : ℝ, T₁ ≤ t → (1 - (lam - 1) / (2 * lam)) * lam * t / Real.log (lam * t) > (1 + (lam - 1) / (2 * lam)) * t / Real.log t := by
    -- We can divide both sides by $t$ (since $t > 0$), yielding:
    suffices h_div : ∃ T₁ : ℝ, 0 < T₁ ∧ ∀ t : ℝ, T₁ ≤ t → (1 - (lam - 1) / (2 * lam)) * lam / Real.log (lam * t) > (1 + (lam - 1) / (2 * lam)) / Real.log t by
      exact ⟨ h_div.choose, h_div.choose_spec.1, fun t ht => by have := h_div.choose_spec.2 t ht; ring_nf at this ⊢; nlinarith [ show 0 < t by linarith [ h_div.choose_spec.1 ] ] ⟩;
    -- We can divide both sides by $log(t)$ (since $t > 1$), yielding:
    suffices h_div_log : ∃ T₁ : ℝ, 0 < T₁ ∧ ∀ t : ℝ, T₁ ≤ t → (1 - (lam - 1) / (2 * lam)) * lam / (Real.log lam + Real.log t) > (1 + (lam - 1) / (2 * lam)) / Real.log t by
      exact ⟨ h_div_log.choose, h_div_log.choose_spec.1, fun t ht => by rw [ Real.log_mul ( by positivity ) ( by linarith [ h_div_log.choose_spec.1 ] ) ] ; exact h_div_log.choose_spec.2 t ht ⟩;
    -- We can divide both sides by $log(t)$ (since $t > 1$), yielding a simpler inequality.
    suffices h_div_log : ∃ T₁ : ℝ, 0 < T₁ ∧ ∀ t : ℝ, T₁ ≤ t → (1 - (lam - 1) / (2 * lam)) * lam * Real.log t > (1 + (lam - 1) / (2 * lam)) * (Real.log lam + Real.log t) by
      obtain ⟨ T₁, hT₁₁, hT₁₂ ⟩ := h_div_log; exact ⟨ Max.max T₁ 2, by positivity, fun t ht => by rw [ gt_iff_lt ] ; rw [ div_lt_div_iff₀ ] <;> nlinarith [ hT₁₂ t ( le_trans ( le_max_left _ _ ) ht ), Real.log_pos hlam, Real.log_pos ( show 1 < t by linarith [ le_max_right T₁ 2 ] ), le_max_right T₁ 2 ] ⟩ ;
    -- We can divide both sides by $log(t)$ (since $t > 1$), yielding a simpler inequality. Let's simplify the inequality.
    suffices h_simplified : ∃ T₁ : ℝ, 0 < T₁ ∧ ∀ t : ℝ, T₁ ≤ t → Real.log t > (1 + (lam - 1) / (2 * lam)) * Real.log lam / ((1 - (lam - 1) / (2 * lam)) * lam - (1 + (lam - 1) / (2 * lam))) by
      obtain ⟨ T₁, hT₁₁, hT₁₂ ⟩ := h_simplified; use T₁; refine' ⟨ hT₁₁, fun t ht => _ ⟩ ; have := hT₁₂ t ht; rw [ gt_iff_lt, div_lt_iff₀ ] at this <;> nlinarith [ show 0 < ( 1 - ( lam - 1 ) / ( 2 * lam ) ) * lam - ( 1 + ( lam - 1 ) / ( 2 * lam ) ) by nlinarith [ show 0 < ( lam - 1 ) / ( 2 * lam ) by exact div_pos ( by linarith ) ( by linarith ), mul_div_cancel₀ ( lam - 1 ) ( by linarith : ( 2 * lam ) ≠ 0 ) ] ] ;
    exact ⟨ Real.exp ( ( 1 + ( lam - 1 ) / ( 2 * lam ) ) * Real.log lam / ( ( 1 - ( lam - 1 ) / ( 2 * lam ) ) * lam - ( 1 + ( lam - 1 ) / ( 2 * lam ) ) ) + 1 ), Real.exp_pos _, fun t ht => by linarith [ Real.log_exp ( ( 1 + ( lam - 1 ) / ( 2 * lam ) ) * Real.log lam / ( ( 1 - ( lam - 1 ) / ( 2 * lam ) ) * lam - ( 1 + ( lam - 1 ) / ( 2 * lam ) ) ) + 1 ), Real.log_le_log ( by positivity ) ht ] ⟩;
  -- By PNT (pnt_epsilon with η = (lam - 1) / (2 * lam)), for large enough t, we have π(lam*t) > π(t).
  obtain ⟨T₂, hT₂⟩ : ∃ T₂ : ℝ, 0 < T₂ ∧ ∀ t : ℝ, T₂ ≤ t → (piReal (lam * t) : ℝ) > (piReal t : ℝ) := by
    -- By PNT (pnt_epsilon with η = (lam - 1) / (2 * lam)), for large enough t, we have π(lam*t) ≥ (1-η)*lam*t/log(lam*t) and π(t) ≤ (1+η)*t/log(t).
    obtain ⟨T₃, hT₃⟩ : ∃ T₃ : ℝ, 0 < T₃ ∧ ∀ t : ℝ, T₃ ≤ t → (piReal (lam * t) : ℝ) ≥ (1 - (lam - 1) / (2 * lam)) * lam * t / Real.log (lam * t) ∧ (piReal t : ℝ) ≤ (1 + (lam - 1) / (2 * lam)) * t / Real.log t := by
      have := pnt_epsilon ( ( lam - 1 ) / ( 2 * lam ) ) ( div_pos ( sub_pos.mpr hlam ) ( by positivity ) );
      obtain ⟨ T, hT₁, hT₂ ⟩ := this; use Max.max T ( 2 * T / lam ) ; refine' ⟨ by positivity, fun t ht => ⟨ _, _ ⟩ ⟩ <;> simp_all +decide [ mul_assoc ] ;
      exact hT₂ _ ( by nlinarith [ mul_div_cancel₀ ( 2 * T ) ( by linarith : lam ≠ 0 ) ] ) |>.1;
    exact ⟨ Max.max T₁ T₃, lt_max_of_lt_left hT₁.1, fun t ht => by linarith [ hT₁.2 t ( le_trans ( le_max_left _ _ ) ht ), hT₃.2 t ( le_trans ( le_max_right _ _ ) ht ) ] ⟩;
  use T₂; simp_all +decide [ piReal ] ;
  intro t ht; have := hT₂.2 t ht; contrapose! this; simp_all +decide [ Nat.primeCounting ] ;
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range ];
  refine Finset.card_mono ?_;
  intro x hx; simp_all +decide ;
  exact Nat.le_of_not_lt fun h => by have := this x hx.2 ( Nat.lt_of_floor_lt h ) ; nlinarith [ Nat.floor_le ( show 0 ≤ lam * t by nlinarith ), Nat.lt_floor_add_one ( lam * t ), ( by norm_cast; linarith : ( x :ℝ ) ≤ ⌊lam * t⌋₊ ) ] ;

/-
D is sublinear.
-/
lemma D_sublinear {η : ℝ} (hη : 0 < η) :
    ∃ X : ℝ, 2 < X ∧ ∀ x : ℝ, X ≤ x → (D x : ℝ) ≤ η * x := by
  -- By multiplicative_prime_interval with lam = 1 + η, there exists T > 0 such that for t ≥ T, there is a prime in (t, (1+η)t].
  obtain ⟨T, hT_pos, hT⟩ : ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → ∃ p : ℕ, p.Prime ∧ t < (p : ℝ) ∧ (p : ℝ) ≤ (1 + η) * t := by
    exact multiplicative_prime_interval ( by linarith );
  -- Let B = max of all gaps g_n where p_n < T.
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ n : ℕ, (nthPrime' n : ℝ) < T → primeGap n ≤ B := by
    have h_finite : Set.Finite {n : ℕ | (nthPrime' n : ℝ) < T} := by
      -- The set of primes less than $T$ is finite.
      have h_finite_primes : Set.Finite {p : ℕ | p.Prime ∧ p < T} := by
        exact Set.finite_iff_bddAbove.mpr ⟨ ⌊T⌋₊, fun p hp => Nat.le_floor <| le_of_lt hp.2 ⟩;
      convert h_finite_primes.preimage _ using 1;
      rotate_left;
      use fun n => nthPrime' n;
      · exact fun a ha b hb hab => Nat.nth_injective ( Nat.infinite_setOf_prime ) hab;
      · exact Set.ext fun n => ⟨ fun hn => ⟨ nthPrime'_prime n, hn ⟩, fun hn => hn.2 ⟩;
    exact ⟨ h_finite.toFinset.sup fun n => primeGap n, fun n hn => Finset.le_sup ( f := fun n => primeGap n ) ( h_finite.mem_toFinset.mpr hn ) ⟩;
  -- Choose X > max(T, B/η, 2).
  obtain ⟨X, hX⟩ : ∃ X : ℝ, 2 < X ∧ T < X ∧ B / η < X := by
    exact ⟨ Max.max ( Max.max 3 ( T + 1 ) ) ( B / η + 1 ), by norm_num, by norm_num, by norm_num ⟩;
  refine' ⟨ X, hX.1, fun x hx => _ ⟩;
  -- For any gap g_n with p_n < x:
  have h_gap_bound : ∀ n : ℕ, (nthPrime' n : ℝ) < x → primeGap n ≤ η * x := by
    intro n hn
    by_cases h_case : (nthPrime' n : ℝ) < T;
    · rw [ div_lt_iff₀ ] at hX <;> nlinarith [ show ( primeGap n : ℝ ) ≤ B by exact_mod_cast hB n h_case ];
    · obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := hT ( nthPrime' n ) ( le_of_not_gt h_case );
      -- Since $p$ is a prime and $nthPrime' n$ is the $n$-th prime, we have $p \geq nthPrime' (n + 1)$.
      have hp_ge_nthPrime_succ : p ≥ nthPrime' (n + 1) := by
        norm_cast at *;
        grind +suggestions;
      unfold primeGap;
      rw [ Nat.cast_sub ( show nthPrime' n ≤ nthPrime' ( n + 1 ) from Nat.le_of_lt ( nthPrime'_lt_succ n ) ) ] ; nlinarith [ show ( nthPrime' ( n + 1 ) : ℝ ) ≤ p by exact_mod_cast hp_ge_nthPrime_succ ];
  refine' le_trans ( Nat.cast_le.mpr <| csSup_le _ _ ) _;
  exact ⌊η * x⌋₊;
  · exact ⟨ 0, Or.inl rfl ⟩;
  · rintro b ( rfl | ⟨ n, hn, rfl ⟩ ) <;> [ exact Nat.zero_le _; exact Nat.le_floor <| h_gap_bound n hn ];
  · exact Nat.floor_le ( mul_nonneg hη.le ( by linarith ) )

/-! ## G lower bound and record gaps -/

/-- The CRT construction gives a run of `3y + 1` consecutive composites
    near a number of size roughly `exp(1.4y)`. For `y = ⌊(7/10) log x⌋`,
    this gives `G(x) > 2 log x` for large `x`. -/
lemma G_lower_bound :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x → 2 * Real.log x < (G x : ℝ) := by
  obtain ⟨x₀, hx₀_pos, hx₀⟩ := exists_large_prime_gap
  refine ⟨x₀, hx₀_pos, fun x hx => ?_⟩
  obtain ⟨p, q, hp, hq, hpq, hno_prime, hq_lt_x, hgap⟩ := hx₀ x hx
  -- p and q are consecutive primes. Use Nat.nth_count to find the index.
  set n := Nat.count Nat.Prime p with n_def
  -- nthPrime' n = p
  have hn_eq : nthPrime' n = p := Nat.nth_count hp
  -- nthPrime'(n+1) = q (since q is the next prime after p)
  have hn1_eq : nthPrime' (n + 1) = q := by
    apply le_antisymm
    · -- nthPrime'(n+1) ≤ q: q is prime and q > nthPrime' n = p, so q ≥ nthPrime'(n+1)
      -- since nthPrime' is the (n+1)-th smallest prime
      by_contra h
      push_neg at h
      have : q < nthPrime' (n + 1) := h
      have : p < q := hpq
      -- q is prime, p = nthPrime' n, and p < q < nthPrime'(n+1)
      -- By Nat.nth_lt_nth, this means count q > n, so count q ≥ n+1
      -- But then nthPrime'(n+1) ≤ q by nth_count, contradiction
      have hq_count : n < Nat.count Nat.Prime q := by
        rw [n_def]
        exact Nat.count_strict_mono hp hpq
      have : nthPrime' (n + 1) ≤ q := by
        unfold nthPrime'
        calc Nat.nth Nat.Prime (n + 1)
            ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
              Nat.nth_monotone Nat.infinite_setOf_prime (by omega)
          _ = q := Nat.nth_count hq
      linarith
    · -- q ≤ nthPrime'(n+1): nthPrime'(n+1) is prime and p < nthPrime'(n+1),
      -- so by hno_prime, nthPrime'(n+1) ≥ q
      by_contra h
      push_neg at h
      have h1 : p < nthPrime' (n + 1) := by rw [← hn_eq]; exact nthPrime'_lt_succ n
      exact hno_prime (nthPrime' (n + 1)) h1 h (nthPrime'_prime (n + 1))
  -- The gap primeGap n = q - p
  have hgap_eq : primeGap n = q - p := by
    unfold primeGap; rw [hn_eq, hn1_eq]
  -- This gap contributes to G(x) since nthPrime'(n+1) = q < x
  have hgap_in_G : (primeGap n : ℝ) ≤ (G x : ℝ) := by
    apply Nat.cast_le.mpr
    apply le_csSup
    · -- G(x) is bounded
      use ⌊x⌋₊
      rintro g (rfl | ⟨m, hm, rfl⟩)
      · exact Nat.zero_le _
      · exact Nat.le_floor <| le_trans (Nat.cast_le.2 <| Nat.sub_le _ _) hm.le
    · -- primeGap n is in the set
      right
      exact ⟨n, by rw [hn1_eq]; exact_mod_cast hq_lt_x, rfl⟩
  -- Combine: 2 * log x < q - p = primeGap n ≤ G(x)
  calc 2 * Real.log x < (q - p : ℝ) := hgap
    _ = (primeGap n : ℝ) := by rw [hgap_eq, Nat.cast_sub (Nat.le_of_lt hpq)]
    _ ≤ (G x : ℝ) := hgap_in_G

lemma D_at_record {n : ℕ} (hrec : IsStrictRecord n) :
    D ((nthPrime' n : ℝ) + 1) = primeGap n := by
  refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ _ <;> norm_num;
  · intros a x hx ha
    have h_le : x ≤ n := by
      exact le_of_not_gt fun h => by linarith [ show ( nthPrime' x : ℝ ) ≥ nthPrime' n + 1 from mod_cast Nat.succ_le_of_lt <| nthPrime'_strictMono h ] ;
    cases eq_or_lt_of_le h_le <;> [ aesop; exact ha ▸ le_of_lt ( hrec _ ‹_› ) ];
  · exact fun w hw => ⟨ _, ⟨ n, mod_cast Nat.lt_succ_self _, rfl ⟩, hw ⟩

lemma long_strict_records (P : ℝ) :
    ∃ n : ℕ, (P : ℝ) < (nthPrime' n : ℝ) ∧
    IsStrictRecord n ∧
    2 * Real.log (nthPrime' n : ℝ) < (primeGap n : ℝ) := by
  by_contra h_contra;
  -- Let $H = H(P)$ be the maximum of all prime gaps $g_n$ with $p_n \leq P$.
  obtain ⟨H, hH⟩ : ∃ H : ℕ, ∀ n : ℕ, (nthPrime' n : ℝ) ≤ P → primeGap n ≤ H := by
    have h_finite : Set.Finite {n : ℕ | (nthPrime' n : ℝ) ≤ P} := by
      have h_finite : Set.Finite {p : ℕ | p ≤ P ∧ p.Prime} := by
        exact Set.finite_iff_bddAbove.mpr ⟨ ⌊P⌋₊, fun p hp => Nat.le_floor <| hp.1 ⟩;
      have h_finite : Set.Finite (Set.image (fun n => nthPrime' n) {n : ℕ | (nthPrime' n : ℝ) ≤ P}) := by
        exact h_finite.subset fun x hx => by obtain ⟨ n, hn, rfl ⟩ := hx; exact ⟨ hn, nthPrime'_prime n ⟩ ;
      convert h_finite.of_finite_image _;
      exact fun a ha b hb hab => Nat.nth_injective ( Nat.infinite_setOf_prime ) hab;
    exact ⟨ h_finite.toFinset.sup fun n => primeGap n, fun n hn => Finset.le_sup ( f := fun n => primeGap n ) ( h_finite.mem_toFinset.mpr hn ) ⟩;
  -- Choose $X$ large enough such that $2 \log X > \max(H, 2)$.
  obtain ⟨X, hX⟩ : ∃ X : ℝ, 2 < X ∧ 2 * Real.log X > max (H : ℝ) 2 ∧ ∀ x : ℝ, X ≤ x → 2 * Real.log x < (G x : ℝ) := by
    obtain ⟨ x₀, hx₀ ⟩ := G_lower_bound;
    -- Choose $X$ large enough such that $2 \log X > \max(H, 2)$ and $X > x₀$.
    obtain ⟨X, hX⟩ : ∃ X : ℝ, 2 < X ∧ 2 * Real.log X > max (H : ℝ) 2 ∧ X > x₀ := by
      have h_log_growth : Filter.Tendsto (fun x : ℝ => 2 * Real.log x) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop ( by norm_num ) ( Real.tendsto_log_atTop );
      exact Filter.eventually_atTop.mp ( h_log_growth.eventually_gt_atTop ( Max.max ( H : ℝ ) 2 ) ) |> fun ⟨ X, hX ⟩ ↦ ⟨ Max.max ( Max.max X 3 ) ( x₀ + 1 ), by norm_num, hX _ <| le_max_of_le_left <| le_max_left _ _, by norm_num ⟩;
    exact ⟨ X, hX.1, hX.2.1, fun x hx => hx₀.2 x <| by linarith ⟩;
  -- By definition of $G$, there exists $m$ such that $p_{m+1} < X$ and $g_m = G(X) > 2 \log X$.
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : ℕ, (nthPrime' (m + 1) : ℝ) < X ∧ primeGap m > 2 * Real.log X := by
    have hG : (G X : ℝ) > 2 * Real.log X := by
      exact hX.2.2 X le_rfl;
    contrapose! hG;
    refine' le_trans ( Nat.cast_le.mpr <| csSup_le _ _ ) _;
    exact ⌊2 * Real.log X⌋₊;
    · exact ⟨ 0, Or.inl rfl ⟩;
    · rintro b ( rfl | ⟨ n, hn, rfl ⟩ ) <;> [ exact Nat.zero_le _; exact Nat.le_floor <| hG n hn ];
    · exact Nat.floor_le ( by linarith [ le_max_left ( H : ℝ ) 2, le_max_right ( H : ℝ ) 2 ] );
  -- Let $k$ be the least index with $g_k = \max(g_0,...,g_m)$.
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k : ℕ, k ≤ m ∧ primeGap k = sSup {g : ℕ | ∃ n : ℕ, n ≤ m ∧ g = primeGap n} ∧ ∀ n : ℕ, n < k → primeGap n < primeGap k := by
    have h_sup : ∃ k : ℕ, k ≤ m ∧ primeGap k = sSup {g : ℕ | ∃ n : ℕ, n ≤ m ∧ g = primeGap n} := by
      have := ( IsCompact.sSup_mem ( show IsCompact { g : ℕ | ∃ n ≤ m, g = primeGap n } from Set.Finite.isCompact <| Set.finite_iff_bddAbove.mpr ⟨ ∑ n ∈ Finset.range ( m + 1 ), primeGap n, by rintro g ⟨ n, hn, rfl ⟩ ; exact Finset.single_le_sum ( fun a _ => Nat.zero_le ( primeGap a ) ) ( Finset.mem_range_succ_iff.mpr hn ) ⟩ ) <| Set.nonempty_of_mem <| ⟨ m, le_rfl, rfl ⟩ ) ; aesop;
    obtain ⟨ k, hk₁, hk₂ ⟩ := Nat.findX h_sup;
    exact ⟨ k, hk₁.1, hk₁.2, fun n hn => lt_of_le_of_ne ( hk₁.2.symm ▸ le_csSup ( by exact Set.Finite.bddAbove <| Set.Finite.subset ( Set.toFinite <| Finset.image ( fun n => primeGap n ) ( Finset.Iic m ) ) fun x hx => by aesop ) ⟨ n, by linarith, rfl ⟩ ) fun h => hk₂ n hn ⟨ by linarith, h.symm ▸ hk₁.2 ⟩ ⟩;
  refine' h_contra ⟨ k, _, _, _ ⟩;
  · contrapose! hm₂;
    refine' le_trans _ ( le_trans ( le_max_left _ _ ) hX.2.1.le );
    exact_mod_cast le_trans ( le_csSup ( show BddAbove { g : ℕ | ∃ n ≤ m, g = primeGap n } from ⟨ ∑ n ∈ Finset.range ( m + 1 ), primeGap n, by rintro g ⟨ n, hn, rfl ⟩ ; exact Finset.single_le_sum ( fun a _ => Nat.zero_le ( primeGap a ) ) ( Finset.mem_range_succ_iff.mpr hn ) ⟩ ) ⟨ m, le_rfl, rfl ⟩ ) ( hk₂.1.symm ▸ hH k hm₂ );
  · exact fun n hn => hk₂.2 n hn;
  · refine' lt_of_le_of_lt _ ( show ( primeGap k : ℝ ) > 2 * Real.log X from _ );
    · gcongr;
      · exact Nat.cast_pos.mpr ( Nat.Prime.pos ( nthPrime'_prime k ) );
      · exact le_trans ( Nat.cast_le.mpr ( show nthPrime' k ≤ nthPrime' ( m + 1 ) from Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by linarith ) ) ) hm₁.le;
    · exact hm₂.trans_le ( mod_cast hk₂.1.symm ▸ le_csSup ( by exact Set.Finite.bddAbove <| Set.Finite.subset ( Set.toFinite <| Finset.image ( fun n => primeGap n ) ( Finset.Iic m ) ) fun x hx => by aesop ) ⟨ m, by linarith, rfl ⟩ )

/-- `0 ∈ SetC`. -/
theorem SetC_zero_mem : (0 : ℝ) ∈ SetC := by
  refine ⟨1, one_pos, fun δ _hδ0 _hδ1 ε _hε => ⟨3, fun x _hx y _hy1 _hy2 => ?_⟩⟩
  simp only [Delta, mul_zero, zero_mul, add_zero, sub_self, Int.cast_zero, abs_zero,
    abs_zero, zero_div]
  exact le_refl 0

/-
For any `z ∈ (1/2, 1 + γ)`, there exists `δ ∈ (0, γ)` with
    `1/2 + δ < z < 1 + δ`.
-/
lemma finite_delta_cover (γ : ℝ) (hγ : 0 < γ) (z : ℝ) (hz1 : 1/2 < z) (hz2 : z < 1 + γ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < γ ∧ 1/2 + δ < z ∧ z < 1 + δ := by
  by_cases hle : z ≤ 1
  · refine ⟨min ((z - 1/2)/2) (γ/2), ?_, ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (by linarith)
    · linarith [min_le_right ((z - 1/2)/2) (γ/2)]
    · linarith [min_le_left ((z - 1/2)/2) (γ/2)]
    · linarith [lt_min (show (z - 1/2)/2 > 0 by linarith) (show γ/2 > 0 by linarith)]
  · push_neg at hle
    refine ⟨(z - 1 + min (z - 1/2) γ) / 2, ?_, ?_, ?_, ?_⟩
    · have h1 : 0 < z - 1 := by linarith
      have h2 : 0 < min (z - 1/2) γ := lt_min (by linarith) hγ
      linarith
    · have : min (z - 1/2) γ ≤ γ := min_le_right _ _
      linarith
    · have : min (z - 1/2) γ ≤ z - 1/2 := min_le_left _ _
      linarith
    · have : z - 1 < min (z - 1/2) γ := lt_min (by linarith) (by linarith)
      linarith

/-
Admissible estimates on compact multiplicative ranges.
-/
lemma admissible_compact_range {c : ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hc : ∀ δ : ℝ, 0 < δ → δ < γ → ∀ ε : ℝ, 0 < ε →
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ y : ℝ, (1/2 + δ) * x < y → y < (1 + δ) * x →
        |((Delta c x y : ℤ) : ℝ) - c * (D x : ℝ) / Real.log y| ≤
          ε * |c| * (D x : ℝ) / Real.log y)
    {lam mu : ℝ} (hlam : 1/2 < lam) (hmu : mu < 1 + γ) (hlm : lam < mu)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 2 < X ∧
    ∀ x : ℝ, X ≤ x →
    ∀ y : ℝ, lam * x < y → y < mu * x →
    |((Delta c x y : ℤ) : ℝ) - c * (D x : ℝ) / Real.log y| ≤
      ε * |c| * (D x : ℝ) / Real.log y := by
  -- Fix an arbitrary $z \in [lam, mu]$.
  have h_fixed_z : ∀ z ∈ Set.Icc lam mu, ∃ δ : ℝ, 0 < δ ∧ δ < γ ∧ 1 / 2 + δ < z ∧ z < 1 + δ := by
    exact fun z hz => finite_delta_cover γ hγ z ( by linarith [ hz.1 ] ) ( by linarith [ hz.2 ] );
  choose! δ hδ using h_fixed_z;
  -- By compactness of $[lam, mu]$, we can find a finite subcover of these intervals.
  obtain ⟨z_set, hz_set⟩ : ∃ z_set : Finset ℝ, (∀ z ∈ z_set, z ∈ Set.Icc lam mu) ∧ (∀ y ∈ Set.Icc lam mu, ∃ z ∈ z_set, y ∈ Set.Ioo (1 / 2 + δ z) (1 + δ z)) := by
    have h_compact : IsCompact (Set.Icc lam mu) := by
      exact CompactIccSpace.isCompact_Icc;
    have := h_compact.elim_nhds_subcover;
    exact Exists.elim ( this ( fun z => Set.Ioo ( 1 / 2 + δ z ) ( 1 + δ z ) ) fun z hz => Ioo_mem_nhds ( by linarith [ hδ z hz ] ) ( by linarith [ hδ z hz ] ) ) fun t ht => ⟨ t, ht.1, fun y hy => by rcases Set.mem_iUnion₂.mp ( ht.2 hy ) with ⟨ z, hz, hyz ⟩ ; exact ⟨ z, hz, hyz ⟩ ⟩;
  -- For each $z \in z_set$, apply admissible_large_threshold to get $X_z$.
  obtain ⟨X_z, hX_z⟩ : ∃ X_z : ℝ, ∀ z ∈ z_set, ∀ x : ℝ, X_z ≤ x → ∀ y : ℝ, (1 / 2 + δ z) * x < y → y < (1 + δ z) * x → |((Delta c x y : ℤ) : ℝ) - c * (D x : ℝ) / Real.log y| ≤ ε * |c| * (D x : ℝ) / Real.log y := by
    choose! X hX using fun z hz => admissible_large_threshold hc ( hδ z ( hz_set.1 z hz ) |>.1 ) ( hδ z ( hz_set.1 z hz ) |>.2.1 ) hε 3;
    exact ⟨ Finset.max' ( z_set.image X ) ⟨ _, Finset.mem_image_of_mem X ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by rintro rfl; exact absurd ( hz_set.2 lam ⟨ by linarith, by linarith ⟩ ) ( by norm_num ) ) ) ) ⟩, fun z hz x hx y hy₁ hy₂ => hX z hz |>.2 x ( le_trans ( Finset.le_max' _ _ ( Finset.mem_image_of_mem X hz ) ) hx ) y hy₁ hy₂ ⟩;
  refine' ⟨ Max.max X_z 3, _, _ ⟩ <;> norm_num;
  intro x hx₁ hx₂ y hy₁ hy₂; obtain ⟨ z, hz₁, hz₂ ⟩ := hz_set.2 ( y / x ) ⟨ by nlinarith [ mul_div_cancel₀ y ( by linarith : x ≠ 0 ) ], by nlinarith [ mul_div_cancel₀ y ( by linarith : x ≠ 0 ) ] ⟩ ; specialize hX_z z hz₁ x hx₁ ( y ) ; simp_all +decide ;
  exact hX_z ( by rw [ lt_div_iff₀ ( by linarith ) ] at hz₂; linarith ) ( by rw [ div_lt_iff₀ ( by linarith ) ] at hz₂; linarith )

/-
Small D-shift lemma.
-/
set_option maxHeartbeats 800000 in
lemma small_D_shift (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 < δ) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ δ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ X : ℝ, 2 < X ∧
    ∀ x : ℝ, X ≤ x →
    ∀ y : ℝ, (1/2 + δ) * x < y → y < (1 + δ) * x →
    ∀ t : ℝ, |t - y| ≤ B * (D x : ℝ) →
    (1/2 + δ - σ) * x < t ∧ t < (1 + δ + σ) * x ∧
    1 < y ∧ 1 < t ∧
    |Real.log y / Real.log t - 1| ≤ ρ ∧
    |Real.log t / Real.log y - 1| ≤ ρ := by
  obtain ⟨ X₁, hX₁, hX₁' ⟩ := D_sublinear ( show 0 < σ / ( B + 1 ) by positivity );
  obtain ⟨ X₂, hX₂ ⟩ := D_sublinear ( show 0 < 1 / 2 * ρ / ( B + 1 ) by positivity );
  refine' ⟨ Max.max X₁ ( Max.max X₂ ( 2 + Real.exp 1 * 2 ) ), _, _ ⟩ <;> norm_num;
  · exact Or.inl hX₁;
  · intro x hx₁ hx₂ hx₃ y hy₁ hy₂ t ht
    have h1 : (1 / 2 + δ - σ) * x < t := by
      nlinarith [ abs_le.mp ht, hX₁' x hx₁, mul_div_cancel₀ ( σ : ℝ ) ( by linarith : ( B + 1 ) ≠ 0 ) ]
    have h2 : t < (1 + δ + σ) * x := by
      nlinarith [ abs_le.mp ht, hX₁' x hx₁, mul_div_cancel₀ ( σ : ℝ ) ( by linarith : ( B + 1 ) ≠ 0 ) ]
    have h3 : 1 < y := by
      nlinarith [ Real.add_one_le_exp 1 ]
    have h4 : 1 < t := by
      nlinarith [ Real.add_one_le_exp 1 ]
    have h5 : |Real.log y / Real.log t - 1| ≤ ρ := by
      have h5 : |Real.log y - Real.log t| ≤ ρ := by
        have h5 : |Real.log y - Real.log t| ≤ |y - t| / min y t := by
          cases le_total y t <;> simp_all +decide ;
          · rw [ abs_of_nonpos ( sub_nonpos_of_le <| Real.log_le_log ( by linarith ) <| by linarith ), abs_of_nonpos ( sub_nonpos_of_le <| by linarith ) ];
            rw [ le_div_iff₀ ( by linarith ) ];
            have := Real.log_le_sub_one_of_pos ( show 0 < t / y by exact div_pos ( by linarith ) ( by linarith ) );
            rw [ Real.log_div ] at this <;> nlinarith [ mul_div_cancel₀ t ( by linarith : y ≠ 0 ) ];
          · rw [ abs_of_nonneg ( sub_nonneg_of_le <| Real.log_le_log ( by linarith ) <| by linarith ), abs_of_nonneg ( sub_nonneg_of_le <| by linarith ) ];
            rw [ ← Real.log_div ( by linarith ) ( by linarith ) ];
            exact le_trans ( Real.log_le_sub_one_of_pos ( div_pos ( by linarith ) ( by linarith ) ) ) ( by ring_nf; norm_num [ show t ≠ 0 by linarith ] );
        have h6 : |y - t| ≤ ρ * (1 / 2) * x := by
          rw [ abs_sub_comm ] at ht;
          exact ht.trans ( by have := hX₂.2 x hx₂; rw [ div_mul_eq_mul_div, le_div_iff₀ ] at this <;> nlinarith );
        have h7 : min y t ≥ (1 / 2) * x := by
          cases min_cases y t <;> nlinarith [ Real.add_one_le_exp 1 ];
        exact h5.trans ( by rw [ div_le_iff₀ ] <;> nlinarith [ abs_nonneg ( y - t ) ] );
      rw [ abs_le ] at *;
      constructor <;> nlinarith [ Real.log_exp 1, Real.log_lt_log ( by positivity ) ( show t > Real.exp 1 by nlinarith [ Real.add_one_le_exp 1 ] ), Real.log_pos h3, Real.log_pos h4, mul_div_cancel₀ ( Real.log y ) ( ne_of_gt ( Real.log_pos h4 ) ) ]
    have h6 : |Real.log t / Real.log y - 1| ≤ ρ := by
      have h6 : |Real.log t - Real.log y| ≤ ρ := by
        have h6 : |Real.log t - Real.log y| ≤ |t - y| / min t y := by
          cases le_total t y <;> simp_all +decide [ abs_sub_comm ];
          · rw [ abs_of_nonneg ( sub_nonneg_of_le <| Real.log_le_log ( by linarith ) <| by linarith ), abs_of_nonneg ( sub_nonneg_of_le <| by linarith ) ];
            rw [ ← Real.log_div ( by linarith ) ( by linarith ) ];
            exact le_trans ( Real.log_le_sub_one_of_pos ( div_pos ( by linarith ) ( by linarith ) ) ) ( by ring_nf; norm_num [ show t ≠ 0 by linarith ] );
          · rw [ abs_of_nonpos ( sub_nonpos_of_le <| Real.log_le_log ( by linarith ) <| by linarith ), abs_of_nonpos ( sub_nonpos_of_le <| by linarith ) ];
            rw [ le_div_iff₀ ( by linarith ) ];
            have := Real.log_le_sub_one_of_pos ( show 0 < t / y by positivity );
            rw [ Real.log_div ] at this <;> nlinarith [ mul_div_cancel₀ t ( by linarith : y ≠ 0 ) ];
        have h7 : |t - y| ≤ ρ * (1 / 2) * x := by
          have := hX₂.2 x hx₂;
          rw [ div_mul_eq_mul_div, le_div_iff₀ ] at this <;> nlinarith;
        have h8 : min t y ≥ (1 / 2) * x := by
          cases min_cases t y <;> nlinarith [ Real.add_one_le_exp 1 ];
        exact h6.trans ( by rw [ div_le_iff₀ ] <;> nlinarith [ abs_nonneg ( t - y ) ] );
      rw [ div_sub_one, abs_div ] <;> try linarith [ Real.log_pos h3, Real.log_pos h4 ];
      exact le_trans ( div_le_self ( abs_nonneg _ ) ( by rw [ abs_of_nonneg ( Real.log_nonneg h3.le ) ] ; exact Real.le_log_iff_exp_le ( by linarith ) |>.2 <| by nlinarith [ Real.add_one_le_exp 1 ] ) ) h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩

/-
Delta identity: Δ_{a-b}(x,y) = Δ_a(x,y) - Δ_b(x, y + (a-b)·D(x)).
-/
lemma Delta_sub_eq (a b : ℝ) (x y : ℝ) :
    Delta (a - b) x y = Delta a x y - Delta b x (y + (a - b) * ↑(D x)) := by
  unfold Delta
  have h : y + (a - b) * ↑(D x) + b * ↑(D x) = y + a * ↑(D x) := by ring
  simp only [h]
  omega

/-
Closure under subtraction.
-/
set_option maxHeartbeats 1600000 in
theorem SetC_sub_closed {a b : ℝ} (ha : a ∈ SetC) (hb : b ∈ SetC) :
    a - b ∈ SetC := by
  -- Trivial case
  by_cases hab : a = b
  · rw [hab, sub_self]; exact SetC_zero_mem
  have hab_pos : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hab)
  -- Extract admissibility data
  obtain ⟨γ_a, hγa_pos, hγa⟩ := ha
  obtain ⟨γ_b, hγb_pos, hγb⟩ := hb
  -- Choose γ for a - b
  refine ⟨min γ_a γ_b / 2, by positivity, ?_⟩
  intro δ hδ_pos hδ_γ ε hε_pos
  have hδ_γa : δ < γ_a := by nlinarith [min_le_left γ_a γ_b]
  have hδ_γb : δ < γ_b := by nlinarith [min_le_right γ_a γ_b]
  -- Set auxiliary parameters
  set σ := δ / 2
  have hσ_pos : 0 < σ := by positivity
  have hσ_le : σ ≤ δ := by simp only [σ]; linarith
  set ε₁ := ε / 4 * |a - b| / (|a| + 2 * |b| + 1)
  have hε₁_pos : 0 < ε₁ := by positivity
  set ρ := min (1/2) (ε / 4 * |a - b| / (2 * |b| + 1))
  have hρ_pos : 0 < ρ := by positivity
  have hρ_le_half : ρ ≤ 1/2 := min_le_left _ _
  have hρ_bound : 2 * |b| * ρ ≤ ε / 4 * |a - b| := by
    have hle : ρ ≤ ε / 4 * |a - b| / (2 * |b| + 1) := min_le_right _ _
    have hden : (0 : ℝ) < 2 * |b| + 1 := by positivity
    calc 2 * |b| * ρ ≤ 2 * |b| * (ε / 4 * |a - b| / (2 * |b| + 1)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ε / 4 * |a - b| * (2 * |b| / (2 * |b| + 1)) := by ring
      _ ≤ ε / 4 * |a - b| * 1 := by gcongr; rw [div_le_one hden]; linarith [abs_nonneg b]
      _ = ε / 4 * |a - b| := by ring
  -- Get X_a from admissibility of a at δ with ε₁
  obtain ⟨X_a, hX_a⟩ := hγa δ hδ_pos hδ_γa ε₁ hε₁_pos
  -- Get X_b from admissibility of b on wider range using admissible_compact_range
  have h_wide_lower : (1 : ℝ)/2 < 1/2 + δ - σ := by simp only [σ]; linarith
  have h_wide_upper : 1 + δ + σ < 1 + γ_b := by simp only [σ]; nlinarith [min_le_right γ_a γ_b]
  have h_wide_order : 1/2 + δ - σ < 1 + δ + σ := by simp only [σ]; linarith
  obtain ⟨X_b, hX_b_pos, hX_b⟩ := admissible_compact_range hγb_pos hγb
    h_wide_lower h_wide_upper h_wide_order hε₁_pos
  -- Get X_s from small_D_shift
  obtain ⟨X_s, hX_s_pos, hX_s⟩ := small_D_shift |a - b| (abs_nonneg _) δ hδ_pos σ hσ_pos hσ_le ρ hρ_pos
  -- Take X = max of all thresholds
  refine ⟨max X_a (max X_b X_s), fun x hx y hy_lo hy_hi => ?_⟩
  have hx_a : X_a ≤ x := le_trans (le_max_left _ _) hx
  have hx_b : X_b ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx_s : X_s ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  -- Set t = y + (a-b)*D(x)
  set t := y + (a - b) * ↑(D x)
  -- Shift bounds from small_D_shift
  have ht_shift : |t - y| ≤ |a - b| * ↑(D x) := by
    show |y + (a - b) * ↑(D x) - y| ≤ _
    rw [add_sub_cancel_left, abs_mul]
    exact le_of_eq (congrArg (|a - b| * ·) (abs_of_nonneg (Nat.cast_nonneg _)))
  obtain ⟨ht_lo, ht_hi, hy_gt1, ht_gt1, hlog_yt, hlog_ty⟩ :=
    hX_s x hx_s y hy_lo hy_hi t ht_shift
  -- Apply admissibility estimates
  have h_est_a : |((Delta a x y : ℤ) : ℝ) - a * (↑(D x) : ℝ) / Real.log y| ≤
      ε₁ * |a| * (↑(D x) : ℝ) / Real.log y := hX_a x hx_a y hy_lo hy_hi
  have h_est_b : |((Delta b x t : ℤ) : ℝ) - b * (↑(D x) : ℝ) / Real.log t| ≤
      ε₁ * |b| * (↑(D x) : ℝ) / Real.log t := hX_b x hx_b t ht_lo ht_hi
  -- Use Delta identity
  have hDelta_id : Delta (a - b) x y = Delta a x y - Delta b x t := Delta_sub_eq a b x y
  -- Log bounds
  have hlog_y_pos : 0 < Real.log y := Real.log_pos hy_gt1
  have hlog_t_pos : 0 < Real.log t := Real.log_pos ht_gt1
  have hlog_t_lower : (1/2 : ℝ) * Real.log y ≤ Real.log t := by
    have h1 := (abs_le.mp hlog_ty).1
    have h2 : 1 - ρ ≤ Real.log t / Real.log y := by linarith
    rw [le_div_iff₀ hlog_y_pos] at h2
    nlinarith
  -- D/log(t) ≤ 2*D/log(y)
  have hD_log_bound : ↑(D x) / Real.log t ≤ 2 * ↑(D x) / Real.log y := by
    rw [div_le_div_iff₀ hlog_t_pos hlog_y_pos]
    nlinarith [show (0 : ℝ) ≤ ↑(D x) from Nat.cast_nonneg _]
  -- Error from log ratio: |b*D/log(t) - b*D/log(y)| ≤ 2*|b|*ρ*D/log(y)
  have hlog_err : |b * ↑(D x) / Real.log t - b * ↑(D x) / Real.log y| ≤
      2 * |b| * ρ * ↑(D x) / Real.log y := by
    have h1 : b * ↑(D x) / Real.log t - b * ↑(D x) / Real.log y =
        b * ↑(D x) * (Real.log y - Real.log t) / (Real.log t * Real.log y) := by field_simp
    rw [h1]
    rw [show (2 : ℝ) * |b| * ρ * ↑(D x) / Real.log y =
      |b| * ↑(D x) * (2 * ρ) / Real.log y from by ring]
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ↑(D x) from Nat.cast_nonneg _),
        abs_of_pos (mul_pos hlog_t_pos hlog_y_pos)]
    have h3 : |Real.log y - Real.log t| ≤ ρ * Real.log y := by
      have hlr := abs_le.mp hlog_ty
      have h3a : Real.log t - Real.log y ≤ ρ * Real.log y := by
        have : Real.log t / Real.log y ≤ 1 + ρ := by linarith [hlr.2]
        rw [div_le_iff₀ hlog_y_pos] at this; linarith
      have h3b : Real.log y - Real.log t ≤ ρ * Real.log y := by
        have : 1 - ρ ≤ Real.log t / Real.log y := by linarith [hlr.1]
        rw [le_div_iff₀ hlog_y_pos] at this; linarith
      exact abs_le.mpr ⟨by linarith, h3b⟩
    rw [div_le_div_iff₀ (mul_pos hlog_t_pos hlog_y_pos) hlog_y_pos]
    nlinarith [abs_nonneg b,
              mul_le_mul_of_nonneg_left h3 (show 0 ≤ |b| * ↑(D x) from by positivity),
              mul_le_mul_of_nonneg_left hlog_t_lower
                (show 0 ≤ |b| * ↑(D x) * |Real.log y - Real.log t| from by positivity)]
  -- Main error bound: decompose as (err_a) - (err_b) - (log_shift_err) and use triangle ineq
  have hD_nonneg : (0 : ℝ) ≤ ↑(D x) := Nat.cast_nonneg _
  set E_a := ((Delta a x y : ℤ) : ℝ) - a * (↑(D x) : ℝ) / Real.log y
  set E_b := ((Delta b x t : ℤ) : ℝ) - b * (↑(D x) : ℝ) / Real.log t
  set E_log := b * (↑(D x) : ℝ) / Real.log t - b * (↑(D x) : ℝ) / Real.log y
  calc |((Delta (a - b) x y : ℤ) : ℝ) - (a - b) * (↑(D x) : ℝ) / Real.log y|
      = |E_a - E_b - E_log| := by
        show _ = |E_a - E_b - E_log|
        congr 1
        simp only [E_a, E_b, E_log]
        rw [show ((Delta (a - b) x y : ℤ) : ℝ) = ((Delta a x y : ℤ) : ℝ) - ((Delta b x t : ℤ) : ℝ) from by
          rw [hDelta_id]; push_cast; ring]
        ring
    _ ≤ |E_a| + |E_b| + |E_log| := by
        calc |E_a - E_b - E_log|
            ≤ |E_a - E_b| + |E_log| := by
              rw [show E_a - E_b - E_log = (E_a - E_b) + (-E_log) from by ring,
                  show |E_log| = |-E_log| from (abs_neg _).symm]
              exact abs_add_le _ _
          _ ≤ |E_a| + |E_b| + |E_log| := by
              linarith [show |E_a - E_b| ≤ |E_a| + |E_b| from by
                rw [show E_a - E_b = E_a + (-E_b) from by ring,
                    show |E_b| = |-E_b| from (abs_neg _).symm]
                exact abs_add_le _ _]
    _ ≤ ε₁ * |a| * ↑(D x) / Real.log y +
        ε₁ * |b| * ↑(D x) / Real.log t +
        2 * |b| * ρ * ↑(D x) / Real.log y := by
      gcongr
    _ ≤ ε₁ * |a| * ↑(D x) / Real.log y +
        ε₁ * |b| * (2 * ↑(D x) / Real.log y) +
        2 * |b| * ρ * ↑(D x) / Real.log y := by
      gcongr
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hD_log_bound (by positivity)
    _ = (ε₁ * (|a| + 2 * |b|) + 2 * |b| * ρ) * ↑(D x) / Real.log y := by ring
    _ ≤ ε * |a - b| * ↑(D x) / Real.log y := by
      gcongr
      have hden : 0 < |a| + 2 * |b| + 1 := by positivity
      have h1 : ε₁ * (|a| + 2 * |b|) ≤ ε / 4 * |a - b| := by
        show ε / 4 * |a - b| / (|a| + 2 * |b| + 1) * (|a| + 2 * |b|) ≤ ε / 4 * |a - b|
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        nlinarith [abs_nonneg a, abs_nonneg b]
      nlinarith

theorem SetC_addSubgroup : ∀ a ∈ SetC, ∀ b ∈ SetC, a - b ∈ SetC :=
  fun _ ha _ hb => SetC_sub_closed ha hb

/-
No c, c' ∈ SetC with 0 < c - c' < 1.
-/
set_option maxHeartbeats 3200000 in
theorem no_small_difference {c c' : ℝ} (hc : c ∈ SetC) (hc' : c' ∈ SetC)
    (hpos : 0 < c - c') (hlt : c - c' < 1) : False := by
  obtain ⟨γ_c, hγ_c_pos, hγ_c⟩ := hc
  obtain ⟨γ_c', hγ_c'_pos, hγ_c'⟩ := hc'
  set δ₀ := min (min γ_c γ_c') (1 / 4) / 2
  have hδ₀_pos : (0 : ℝ) < δ₀ := by positivity
  have hδ₀_lt_γ_c : δ₀ < γ_c := by
    show min (min γ_c γ_c') (1 / 4) / 2 < γ_c
    nlinarith [min_le_left (min γ_c γ_c') (1/4), min_le_left γ_c γ_c']
  have hδ₀_lt_γ_c' : δ₀ < γ_c' := by
    show min (min γ_c γ_c') (1 / 4) / 2 < γ_c'
    nlinarith [min_le_left (min γ_c γ_c') (1/4), min_le_right γ_c γ_c']
  set r := c - c'
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ε * (|c| + |c'|) < r := by
    exact ⟨ r / ( |c| + |c'| + 1 ), div_pos hpos ( by positivity ), by rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> nlinarith [ abs_nonneg c, abs_nonneg c' ] ⟩
  obtain ⟨X_c, hX_c⟩ := admissible_large_threshold hγ_c hδ₀_pos hδ₀_lt_γ_c hε_pos 0
  obtain ⟨X_c', hX_c'⟩ := admissible_large_threshold hγ_c' hδ₀_pos hδ₀_lt_γ_c' hε_pos 0
  -- Use D_sublinear to bound gap relative to δ₀
  obtain ⟨X_D, hX_D⟩ := D_sublinear (show 0 < δ₀ / (2 * (|c'| + 1)) by positivity)
  set X₀ := max 3 (max X_c (max X_c' X_D))
  obtain ⟨n, hn_P, hn_rec, hn_gap⟩ := long_strict_records X₀
  set d := primeGap n
  set x := (nthPrime' n : ℝ) + 1
  set y := (nthPrime' n : ℝ) - c' * d
  have hDx : D x = d := D_at_record hn_rec
  have hp_n_large : (nthPrime' n : ℝ) > 3 := by linarith [le_max_left (3 : ℝ) (max X_c (max X_c' X_D))]
  have hn_X_c : X_c ≤ (nthPrime' n : ℝ) + 1 := by linarith [le_max_left X_c (max X_c' X_D), le_max_right (3 : ℝ) (max X_c (max X_c' X_D))]
  have hn_X_c' : X_c' ≤ (nthPrime' n : ℝ) + 1 := by linarith [le_max_left X_c' X_D, le_max_right X_c (max X_c' X_D), le_max_right (3 : ℝ) (max X_c (max X_c' X_D))]
  have hn_X_D : X_D ≤ (nthPrime' n : ℝ) + 1 := by linarith [le_max_right X_c' X_D, le_max_right X_c (max X_c' X_D), le_max_right (3 : ℝ) (max X_c (max X_c' X_D))]
  -- Gap bound: g_n = D(p_n+1) ≤ δ₀/(2*(|c'|+1)) * (p_n+1) ≤ δ₀*p_n/(|c'|+1) for large p_n
  have hgap_bound : (d : ℝ) ≤ δ₀ / (2 * (|c'| + 1)) * ((nthPrime' n : ℝ) + 1) := by
    rw [← hDx]; exact hX_D.2 x hn_X_D
  have hgap_bound' : |c'| * (d : ℝ) ≤ δ₀ * ((nthPrime' n : ℝ) + 1) / 2 := by
    nlinarith [abs_nonneg c', mul_div_cancel₀ (δ₀ : ℝ) (by positivity : (2 * (|c'| + 1) : ℝ) ≠ 0)]
  have hp_n : (nthPrime' n : ℝ) ≥ 2 := by exact_mod_cast Nat.Prime.two_le (nthPrime'_prime n)
  have hd_pos : (primeGap n : ℝ) ≥ 1 := by exact_mod_cast primeGap_pos n
  have hy_bounds : (1 / 2 + δ₀) * x < y ∧ y < (1 + δ₀) * x := by
    have hshift_bound : c' * (d : ℝ) ≤ δ₀ * x / 2 ∧ -(δ₀ * x / 2) ≤ c' * (d : ℝ) := by
      cases abs_cases c' with
      | inl h => exact ⟨by nlinarith [h.1, show (d : ℝ) ≥ 0 from Nat.cast_nonneg _], by nlinarith [h.1]⟩
      | inr h => exact ⟨by nlinarith [h.1], by nlinarith [h.1, show (d : ℝ) ≥ 0 from Nat.cast_nonneg _]⟩
    constructor
    · -- Lower bound: (1/2+δ₀)*x < y. y = p_n - c'*d ≥ p_n - δ₀*x/2 > (1/2+δ₀)*x for large p_n.
      have hδ₀_le : δ₀ ≤ 1/8 := by
        show min (min γ_c γ_c') (1 / 4) / 2 ≤ 1/8
        nlinarith [min_le_right (min γ_c γ_c') (1/4)]
      nlinarith [hshift_bound.1]
    · -- Upper bound: y < (1+δ₀)*x. y = p_n - c'*d ≤ p_n + δ₀*x/2 < (1+δ₀)*x.
      nlinarith [hshift_bound.2]
  have hDelta_eq : Delta c x y = Delta c' x y := by
    have h_pi_eq : piReal (y + c * d) = piReal (y + c' * d) := by
      have h_pi_eq : ∀ t : ℝ, (nthPrime' n : ℝ) ≤ t ∧ t < (nthPrime' (n + 1) : ℝ) → piReal t = piReal (nthPrime' n) := by
        intros t ht
        have h_prime_count : ∀ m : ℕ, m ≤ t → m.Prime → m ≤ nthPrime' n := by
          intros m hm₁ hm₂
          contrapose! ht
          exact fun _ => le_trans ( mod_cast Nat.le_of_lt_succ <| by linarith [ show nthPrime' ( n + 1 ) ≤ m from Nat.le_of_not_lt fun h => no_prime_between_consecutive n m ( by linarith ) ( by linarith ) hm₂ ] ) hm₁
        refine Nat.le_antisymm ?_ ?_ <;> simp_all +decide [ piReal ]
        · rw [ Nat.primeCounting, Nat.primeCounting ]
          rw [ Nat.primeCounting', Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range ]
          exact Finset.card_mono fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( h_prime_count x ( Nat.floor_le ( by linarith ) |> le_trans ( Nat.cast_le.mpr ( Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hx |>.1 ) ) ) ) ( Finset.mem_filter.mp hx |>.2 ) ) ), Finset.mem_filter.mp hx |>.2 ⟩
        · exact Nat.monotone_primeCounting <| Nat.le_floor <| mod_cast ht.1
      convert h_pi_eq ( y + c * d ) _ using 1
      · exact congr_arg _ ( by ring )
      · constructor <;> nlinarith [ show ( primeGap n : ℝ ) > 0 from Nat.cast_pos.mpr ( primeGap_pos n ), show ( nthPrime' ( n + 1 ) : ℝ ) = nthPrime' n + primeGap n from mod_cast eq_comm.mp <| Nat.add_sub_of_le <| Nat.le_of_lt <| nthPrime'_lt_succ n ]
    grind +locals
  have h_adm_c : |((Delta c x y : ℤ) : ℝ) - c * (d : ℝ) / Real.log y| ≤ ε * |c| * (d : ℝ) / Real.log y := by
    grind
  have h_adm_c' : |((Delta c' x y : ℤ) : ℝ) - c' * (d : ℝ) / Real.log y| ≤ ε * |c'| * (d : ℝ) / Real.log y := by
    grind
  have h_contradiction : r * (d : ℝ) / Real.log y ≤ ε * (|c| + |c'|) * (d : ℝ) / Real.log y := by
    simp_all +decide [ abs_le ]
    ring_nf at *; linarith
  contrapose! h_contradiction
  gcongr
  · exact Real.log_pos <| by nlinarith [ show ( nthPrime' n : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le <| nthPrime'_prime n, hy_bounds.1, hδ₀_pos ]

/-
`1 ∉ SetC`.
-/
theorem one_not_mem_SetC : (1 : ℝ) ∉ SetC := by
  by_contra h_contra
  obtain ⟨γ, hγ⟩ : ∃ γ, 0 < γ ∧ ∀ δ, 0 < δ → δ < γ → ∀ ε, 0 < ε → ∃ X, ∀ x, X ≤ x → ∀ y, (1/2+δ)*x < y → y < (1+δ)*x → |((Delta 1 x y : ℤ) : ℝ) - (D x : ℝ) / Real.log y| ≤ ε*(D x : ℝ) / Real.log y := by
    obtain ⟨ γ, hγ₁, hγ₂ ⟩ := h_contra; use γ, hγ₁; intros δ hδ₁ hδ₂ ε hε; obtain ⟨ X, hX ⟩ := hγ₂ δ hδ₁ hδ₂ ε hε; use X; intros x hx y hy₁ hy₂; specialize hX x hx y hy₁ hy₂; simp_all +decide ;
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, 0 < δ₀ ∧ δ₀ < γ ∧ δ₀ < 1 / 4 := by
    exact ⟨ Min.min ( γ / 2 ) ( 1 / 8 ), by linarith [ lt_min ( half_pos hγ.1 ) ( by norm_num : ( 0 : ℝ ) < 1 / 8 ) ], by linarith [ min_le_left ( γ / 2 ) ( 1 / 8 ) ], by linarith [ min_le_right ( γ / 2 ) ( 1 / 8 ) ] ⟩;
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, max 3 8 ≤ X₀ ∧ ∀ x, X₀ ≤ x → ∀ y, (1/2+δ₀)*x < y → y < (1+δ₀)*x → |((Delta 1 x y : ℤ) : ℝ) - (D x : ℝ) / Real.log y| ≤ (1/4)*(D x : ℝ) / Real.log y := by
    exact Exists.elim ( hγ.2 δ₀ hδ₀.1 hδ₀.2.1 ( 1 / 4 ) ( by norm_num ) ) fun X hX => ⟨ Max.max X ( Max.max 3 8 ), le_max_right _ _, fun x hx y hy₁ hy₂ => hX x ( le_trans ( le_max_left _ _ ) hx ) y hy₁ hy₂ ⟩;
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (X₀ : ℝ) < (nthPrime' n : ℝ) ∧ IsStrictRecord n ∧ 2 * Real.log (nthPrime' n : ℝ) < (primeGap n : ℝ) := by
    exact long_strict_records X₀;
  have hD : D ((nthPrime' n : ℝ) + 1) = primeGap n := by
    apply D_at_record; exact hn.2.1;
  have hDelta : Delta 1 ((nthPrime' n : ℝ) + 1) (nthPrime' n : ℝ) = 1 := by
    unfold Delta;
    unfold piReal; norm_num [ hD ] ;
    rw [ show ⌊ ( nthPrime' n : ℝ ) + primeGap n⌋₊ = nthPrime' ( n + 1 ) from ?_ ];
    · rw [ Nat.primeCounting, Nat.primeCounting ];
      rw [ Nat.primeCounting', Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range ];
      rw [ show Finset.filter Nat.Prime ( Finset.range ( nthPrime' ( n + 1 ) + 1 ) ) = Finset.filter Nat.Prime ( Finset.range ( nthPrime' n + 1 ) ) ∪ { nthPrime' ( n + 1 ) } from ?_, Finset.card_union ] <;> norm_num;
      · rw [ Finset.inter_singleton ] ; norm_num [ Nat.Prime.ne_zero, Nat.Prime.ne_one, nthPrime'_prime ];
        rw [ if_neg ( not_le_of_gt ( nthPrime'_strictMono ( Nat.lt_succ_self _ ) ) ) ] ; norm_num;
      · ext; simp [Finset.mem_insert, Finset.mem_range];
        constructor <;> intro h;
        · grind +suggestions;
        · rcases h with ( rfl | ⟨ h₁, h₂ ⟩ ) <;> [ exact ⟨ le_rfl, Nat.prime_nth_prime _ ⟩ ; exact ⟨ le_trans h₁ ( Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( Nat.le_succ _ ) ), h₂ ⟩ ];
    · rw [ Nat.floor_eq_iff ] <;> norm_cast <;> norm_num [ primeGap ];
      exact ⟨ by rw [ Nat.add_sub_of_le ( Nat.le_of_lt ( nthPrime'_lt_succ n ) ) ], by rw [ Nat.add_sub_of_le ( Nat.le_of_lt ( nthPrime'_lt_succ n ) ) ] ⟩;
  have := hX₀.2 ( nthPrime' n + 1 ) ( by linarith ) ( nthPrime' n ) ?_ ?_ <;> norm_num at *;
  · norm_num [ hDelta, hD ] at this;
    rw [ abs_le ] at this;
    ring_nf at this;
    nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( nthPrime' n : ℝ ) > 1 by exact_mod_cast Nat.Prime.one_lt ( nthPrime'_prime n ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( nthPrime' n : ℝ ) > 1 by exact_mod_cast Nat.Prime.one_lt ( nthPrime'_prime n ) ) ) ) ];
  · nlinarith [ show ( nthPrime' n : ℝ ) ≥ 8 by exact_mod_cast le_trans ( by linarith ) ( Nat.cast_le.mpr ( show nthPrime' n ≥ 8 by exact le_of_not_gt fun h => by have := hn.1; linarith [ show ( nthPrime' n : ℝ ) ≤ 7 by exact_mod_cast Nat.le_of_lt_succ h ] ) ) ];
  · nlinarith [ show ( nthPrime' n : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le ( nthPrime'_prime n ) ]

/-- `SetC ∩ (0, 1] = ∅`. -/
theorem SetC_inter_Ioc_empty : SetC ∩ Ioc 0 1 = ∅ := by
  ext c
  constructor
  · intro hc_mem
    have hc := hc_mem.1
    have hc0 : 0 < c := hc_mem.2.1
    have hc1 : c ≤ 1 := hc_mem.2.2
    rcases lt_or_eq_of_le hc1 with h | h
    · exact absurd (no_small_difference hc SetC_zero_mem (by linarith) (by linarith)) id
    · rw [h] at hc; exact absurd (one_not_mem_SetC hc) id
  · intro h; exact h.elim

/-
**Discrete subgroup lemma**.
-/
theorem discrete_subgroup_classification
    (H : Set ℝ)
    (H_zero : (0 : ℝ) ∈ H)
    (H_sub : ∀ a ∈ H, ∀ b ∈ H, a - b ∈ H)
    (H_no_small : H ∩ Ioc 0 1 = ∅) :
    H = {0} ∨
    ∃ γ : ℝ, 1 < γ ∧
      H = {x : ℝ | ∃ k : ℤ, x = γ * k} ∧
      ∀ γ' : ℝ, 1 < γ' → H = {x : ℝ | ∃ k : ℤ, x = γ' * k} → γ' = γ := by
  by_cases h : H = { 0 };
  · exact Or.inl h;
  · obtain ⟨α, hα⟩ : ∃ α ∈ H, 0 < α ∧ ∀ β ∈ H, 0 < β → α ≤ β := by
      obtain ⟨α, hα⟩ : ∃ α ∈ H, 0 < α := by
        grind;
      obtain ⟨γ, hγ⟩ : ∃ γ ∈ H, 0 < γ ∧ γ ≤ α ∧ ∀ β ∈ H, 0 < β → β ≤ α → γ ≤ β := by
        have h_finite : Set.Finite {β ∈ H | 0 < β ∧ β ≤ α} := by
          have h_finite : ∀ n : ℕ, Set.Finite {β ∈ H | 0 < β ∧ β ≤ α ∧ ⌊β⌋₊ = n} := by
            intro n
            have h_finite : Set.Finite {β ∈ H | 0 < β ∧ β ≤ α ∧ ⌊β⌋₊ = n} := by
              have h_distinct : ∀ β₁ β₂ : ℝ, β₁ ∈ H → β₂ ∈ H → 0 < β₁ → 0 < β₂ → ⌊β₁⌋₊ = n → ⌊β₂⌋₊ = n → β₁ = β₂ := by
                intros β₁ β₂ hβ₁ hβ₂ hβ₁_pos hβ₂_pos hβ₁_floor hβ₂_floor
                have h_diff : β₁ - β₂ ∈ H := by
                  exact H_sub _ hβ₁ _ hβ₂
                have h_diff_pos : 0 < β₁ - β₂ → β₁ - β₂ > 1 := by
                  exact fun h => not_le.mp fun h' => H_no_small.subset ⟨ h_diff, h, h' ⟩
                have h_diff_neg : 0 < β₂ - β₁ → β₂ - β₁ > 1 := by
                  exact fun h => not_le.mp fun h' => H_no_small.subset ⟨ H_sub _ hβ₂ _ hβ₁, ⟨ by linarith, by linarith ⟩ ⟩
                have h_diff_zero : β₁ - β₂ = 0 := by
                  rw [ Nat.floor_eq_iff ] at * <;> try linarith;
                  exact le_antisymm ( le_of_not_gt fun h => by linarith [ h_diff_pos h ] ) ( le_of_not_gt fun h => by linarith [ h_diff_neg ( by linarith ) ] )
                linarith
              exact Set.Subsingleton.finite ( fun x hx y hy => h_distinct x y hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2.2 hy.2.2.2 );
            exact h_finite;
          refine' Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_Iic ⌊α⌋₊ ) fun n hn => h_finite n ) _;
          exact fun x hx => Set.mem_iUnion₂.mpr ⟨ ⌊x⌋₊, Nat.floor_mono hx.2.2, hx.1, hx.2.1, hx.2.2, rfl ⟩;
        exact ⟨ Finset.min' ( h_finite.toFinset ) ⟨ α, h_finite.mem_toFinset.mpr ⟨ hα.1, hα.2, le_rfl ⟩ ⟩, h_finite.mem_toFinset.mp ( Finset.min'_mem _ _ ) |>.1, h_finite.mem_toFinset.mp ( Finset.min'_mem _ _ ) |>.2.1, h_finite.mem_toFinset.mp ( Finset.min'_mem _ _ ) |>.2.2, fun β hβ hβ' hβ'' => Finset.min'_le _ _ ( h_finite.mem_toFinset.mpr ⟨ hβ, hβ', hβ'' ⟩ ) ⟩;
      grind +splitImp;
    -- For any h ∈ H, pick k ∈ ℤ with kα ≤ h < (k+1)α. Then r = h - kα ∈ H and 0 ≤ r < α. If r > 0, r ∈ H ∩ (0,1] contradicts H ∩ (0,1] = ∅. So r = 0 and h = kα. Thus H = {αk : k ∈ ℤ}.
    have h_eq : ∀ h ∈ H, ∃ k : ℤ, h = k * α := by
      intro h hh;
      -- By definition of $α$, we know that $h - kα ∈ H$ for any integer $k$.
      have h_diff : ∀ k : ℤ, h - k * α ∈ H := by
        intro k; induction k using Int.induction_on <;> simp_all +decide [ sub_mul ] ;
        · convert H_sub _ ‹_› _ hα.1 using 1 ; ring;
        · convert H_sub _ ‹_› _ ( H_sub _ H_zero _ hα.1 ) using 1 ; ring;
      -- Choose $k$ such that $0 \leq h - kα < α$.
      obtain ⟨k, hk⟩ : ∃ k : ℤ, 0 ≤ h - k * α ∧ h - k * α < α := by
        exact ⟨ ⌊h / α⌋, by nlinarith [ Int.floor_le ( h / α ), mul_div_cancel₀ h hα.2.1.ne' ], by nlinarith [ Int.lt_floor_add_one ( h / α ), mul_div_cancel₀ h hα.2.1.ne' ] ⟩;
      exact ⟨ k, by linarith [ show h - k * α = 0 by exact le_antisymm ( le_of_not_gt fun h' => by linarith [ hα.2.2 _ ( h_diff k ) h' ] ) hk.1 ] ⟩;
    refine Or.inr ⟨ α, ?_, ?_, ?_ ⟩;
    · exact lt_of_not_ge fun hα' => H_no_small.subset ⟨ hα.1, hα.2.1, hα' ⟩;
    · ext x; simp;
      constructor <;> intro hx;
      · simpa only [ mul_comm ] using h_eq x hx;
      · obtain ⟨ k, rfl ⟩ := hx;
        induction k using Int.induction_on <;> simp_all +decide [mul_add];
        · convert H_sub _ ‹_› _ ( H_sub _ H_zero _ hα.1 ) using 1 ; ring;
        · convert H_sub _ ‹_› _ hα.1 using 1 ; ring;
    · intro γ' hγ' hγ'_eq; have := hγ'_eq.subset hα.1; simp_all +decide ;
      obtain ⟨ k, hk ⟩ := this; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> try nlinarith;
      contrapose! hα;
      exact fun _ => ⟨ _, 1, rfl, by positivity, by norm_num; nlinarith ⟩

/-! ## Main theorem; Classification of admissible constants** . -/
theorem main_theorem :
    SetC = {0} ∨ ∃ γ : ℝ, 1 < γ ∧ SetC = {x : ℝ | ∃ k : ℤ, x = γ * k} := by
  rcases discrete_subgroup_classification
    SetC SetC_zero_mem SetC_addSubgroup SetC_inter_Ioc_empty with h | ⟨γ, hγ, hSetC, _⟩
  · exact Or.inl h
  · exact Or.inr ⟨γ, hγ, hSetC⟩

end

#show_unused main_theorem
#print axioms main_theorem
