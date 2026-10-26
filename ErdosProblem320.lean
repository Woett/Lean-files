import Mathlib

/-
Here we give bounds on the number of distinct sums of the form ∑_{n ∈ B} 1/n for
B ⊆ {1, …, N}, and on the size of the largest subset of {1, …, N} on which this
sum is injective. These bounds are based on the following two papers:

S. Bettin, L. Grenié, G. Molteni, and C. Sanna, A lower bound for the number of
Egyptian fractions. arXiv:2509.10030 (2025)

Y. Luo, R. Yang, and K. Zhu, Distinct Harmonic Subset Sums.
https://www.overleaf.com/project/6a520c740839682551d8bab9

The formalization was obtained by Aristotle from Harmonic
(aristotle-harmonic@harmonic.fun) and is completely self-contained.

Lean version: leanprover/lean4:v4.28.0
-/

@[expose] public section

open Finset MeasureTheory

noncomputable section

/-! ## Definitions -/

/-- The reciprocal subset sums `E(A) = { ∑_{n ∈ B} 1/n : B ⊆ A } ⊆ ℚ` of a finite set `A`. -/
def recipSubsetSums (A : Finset ℕ) : Finset ℚ :=
  A.powerset.image (fun B : Finset ℕ => ∑ n ∈ B, (1 : ℚ) / (n : ℚ))

/-- `S(N) = |E([N])|`, the number of distinct reciprocal subset sums of `{1, …, N}`. -/
def S (N : ℕ) : ℕ := (recipSubsetSums (Icc 1 N)).card

/-- A finite set `A` is *reciprocally dissociated* if `B ↦ ∑_{n ∈ B} 1/n` is injective on the
subsets of `A`. -/
def RecipDissociated (A : Finset ℕ) : Prop :=
  Set.InjOn (fun B : Finset ℕ => ∑ n ∈ B, (1 : ℚ) / (n : ℚ)) (A.powerset : Set (Finset ℕ))

open Classical in
/-- `R(N)`, the largest size of a reciprocally dissociated subset of `{1, …, N}`. -/
def R (N : ℕ) : ℕ := ((Icc 1 N).powerset.filter RecipDissociated).sup Finset.card

/-- The iterated logarithm `ℓ_j(x) = log (log (⋯ (log x)))` (`j` times), `ℓ_0(x) = x`. -/
def iterLog (j : ℕ) (x : ℝ) : ℝ := Real.log^[j] x

/-- The stopping index `k_A(x)`: the largest integer `k ≥ 3` such that `ℓ_j(x) ≥ A`
for every `3 ≤ j ≤ k`. -/
def stopIndex (A x : ℝ) : ℕ :=
  sSup {k : ℕ | 3 ≤ k ∧ ∀ j ∈ Icc 3 k, A ≤ iterLog j x}

/-- `P_A(x) = ∏_{j=3}^{k_A(x)} ℓ_j(x)`. -/
def stopProd (A x : ℝ) : ℝ := ∏ j ∈ Icc 3 (stopIndex A x), iterLog j x

/-- The comparison function `G(N) = N / log N · ∏_{j=3}^{k(N)} ℓ_j(N)`, with `k(N) = k_2(N)`. -/
def G (N : ℕ) : ℝ := (N / Real.log N) * stopProd 2 N

/-! ## Mertens' first theorem -/

/-- The primes `p ≤ n`. -/
def primesLE (n : ℕ) : Finset ℕ := (Ioc 0 n).filter Nat.Prime

lemma mem_primesLE {n p : ℕ} : p ∈ primesLE n ↔ p.Prime ∧ p ≤ n := by
  unfold primesLE
  rw [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨hp, h⟩
  · rintro ⟨hp, h⟩; exact ⟨⟨hp.pos, h⟩, hp⟩

/-- `B(x) = ∑_{p ≤ x} log p / p`. -/
def mertensB (x : ℝ) : ℝ := ∑ p ∈ primesLE ⌊x⌋₊, Real.log p / p

/-- `log n! = ∑_{p ≤ n} v_p(n!) log p`. -/
lemma log_factorial_eq_sum (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ p ∈ primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) *
      Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    exact mem_primesLE.2 ⟨hp.1, (Nat.Prime.dvd_factorial hp.1).1 hp.2.1⟩
  · intro p _; simp

lemma factorization_factorial_ge {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    n / p ≤ n.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_succ_self (Nat.log p n))]
  have h1 : 1 ≤ Nat.log p n := Nat.le_log_of_pow_le hp.one_lt (by simpa using hpn)
  have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _)
    (show 1 ∈ Ico 1 (Nat.log p n + 1) by simp; exact ⟨hpn, hp.one_lt⟩)
  simpa using this

lemma nat_div_ge (n p : ℕ) (hp : 0 < p) : (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := by
  have h := Nat.div_add_mod n p
  have hm := Nat.mod_lt n hp
  have : (n : ℝ) < p * ((n / p : ℕ) + 1) := by
    have : n < p * (n / p + 1) := by nlinarith
    exact_mod_cast this
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  nlinarith

/-- The series `∑ log k / (k (k-1))` converges. -/
def mertensTerm (k : ℕ) : ℝ := Real.log k / ((k : ℝ) * ((k : ℝ) - 1))

lemma mertensTerm_nonneg (k : ℕ) : 0 ≤ mertensTerm k := by
  unfold mertensTerm
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> simp
  · have : (2 : ℝ) ≤ k := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

lemma mertensTerm_le (k : ℕ) : mertensTerm k ≤ 4 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> simp [mertensTerm]
  · have hk : (2 : ℝ) ≤ k := by exact_mod_cast h
    have hk0 : (0 : ℝ) < k := by linarith
    unfold mertensTerm
    have hlog : Real.log k ≤ 2 * (k : ℝ) ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div hk0.le (show (0 : ℝ) < 1 / 2 by norm_num)
      linarith [show (k : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (k : ℝ) ^ (1 / 2 : ℝ) by ring]
    have hsplit : (k : ℝ) ^ (2 : ℝ) = (k : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hk0]; norm_num
    have hsq : (k : ℝ) ^ (2 : ℝ) = (k : ℝ) * k := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have h32 : 0 < (k : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hk0 _
    have h12 : 0 < (k : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hk0 _
    have hden : 0 < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
    rw [div_le_iff₀ hden]
    have : 4 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((k : ℝ) * ((k : ℝ) - 1)) ≥
        2 * (k : ℝ) ^ (1 / 2 : ℝ) := by
      rw [ge_iff_le, ← sub_nonneg]
      have e : 4 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((k : ℝ) * ((k : ℝ) - 1)) -
          2 * (k : ℝ) ^ (1 / 2 : ℝ) =
          ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ * (4 * (k * (k - 1)) - 2 * (k * k)) := by
        rw [← hsq, hsplit]; field_simp
      rw [e]
      apply mul_nonneg (inv_nonneg.2 h32.le)
      nlinarith
    linarith

lemma summable_mertensTerm : Summable mertensTerm := by
  have hs : Summable (fun k : ℕ => 4 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 4
  exact hs.of_nonneg_of_le mertensTerm_nonneg mertensTerm_le

/-- `∑_{p ≤ n} log p / (p (p-1)) ≤ K₀`. -/
lemma sum_primes_mertensTerm_le (n : ℕ) :
    ∑ p ∈ primesLE n, mertensTerm p ≤ ∑' k, mertensTerm k :=
  summable_mertensTerm.sum_le_tsum _ (fun k _ => mertensTerm_nonneg k)

lemma theta_eq_sum (n : ℕ) : Chebyshev.theta n = ∑ p ∈ primesLE n, Real.log p := by
  unfold Chebyshev.theta primesLE
  rw [Nat.floor_natCast]

/-- Upper bound `log n! ≤ n B(n) + n K₀`. -/
lemma log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ n * mertensB n + n * ∑' k, mertensTerm k := by
  rw [log_factorial_eq_sum]
  have h1 : ∀ p ∈ primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p ≤
      n * (Real.log p / p) + n * mertensTerm p := by
    intro p hp
    obtain ⟨hp, -⟩ := mem_primesLE.1 hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hv : ((n.factorial.factorization p : ℕ) : ℝ) ≤ n / ((p : ℝ) - 1) := by
      have := Nat.factorization_factorial_le_div_pred hp n
      have h2 : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
      rw [Nat.cast_sub hp.one_le, Nat.cast_one] at h2
      exact (Nat.cast_le.2 this).trans h2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    calc ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p ≤ n / ((p : ℝ) - 1) * Real.log p :=
          mul_le_mul_of_nonneg_right hv hlog
      _ = n * (Real.log p / p) + n * mertensTerm p := by
          unfold mertensTerm
          have : (p : ℝ) - 1 ≠ 0 := by linarith
          have : (p : ℝ) ≠ 0 := by linarith
          field_simp
          ring
  calc ∑ p ∈ primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p
      ≤ ∑ p ∈ primesLE n, (n * (Real.log p / p) + n * mertensTerm p) := Finset.sum_le_sum h1
    _ = n * mertensB n + n * ∑ p ∈ primesLE n, mertensTerm p := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, mertensB,
          Nat.floor_natCast]
    _ ≤ n * mertensB n + n * ∑' k, mertensTerm k := by
        gcongr
        exact sum_primes_mertensTerm_le n

/-- Lower bound `log n! ≥ n B(n) - θ(n)`. -/
lemma log_factorial_ge (n : ℕ) :
    n * mertensB n - Chebyshev.theta n ≤ Real.log (n.factorial : ℝ) := by
  rw [log_factorial_eq_sum, theta_eq_sum, mertensB, Nat.floor_natCast, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp, hpn⟩ := mem_primesLE.1 hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have h1 := nat_div_ge n p hp.pos
  have h2 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial.factorization p : ℕ) : ℝ) :=
    Nat.cast_le.2 (factorization_factorial_ge hp hpn)
  calc (n : ℝ) * (Real.log p / p) - Real.log p = ((n : ℝ) / p - 1) * Real.log p := by
        field_simp
    _ ≤ ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hlog

lemma log_factorial_ge' (n : ℕ) : n * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.pow_div_factorial_le_exp n hn0.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  have := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at this
  linarith

lemma log_factorial_le' (n : ℕ) : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
  exact_mod_cast Nat.factorial_le_pow n

/-- **Mertens' first theorem** in the form `|B(x) - log x| ≤ K` for `x ≥ 1`. -/
theorem mertens_first : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → |mertensB x - Real.log x| ≤ K := by
  set K₀ := ∑' k, mertensTerm k
  have hK₀ : 0 ≤ K₀ := tsum_nonneg mertensTerm_nonneg
  refine ⟨max (Real.log 4) (1 + K₀ + Real.log 2), le_max_of_le_left (Real.log_nonneg
    (by norm_num)), fun x hx => ?_⟩
  set n := ⌊x⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by simpa using hx)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hBn : mertensB x = mertensB n := by simp [mertensB, hn]
  rw [hBn]
  -- bounds on log x
  have hlx1 : Real.log n ≤ Real.log x := Real.log_le_log hn0 hnx
  have hlx2 : Real.log x ≤ Real.log n + Real.log 2 := by
    rw [← Real.log_mul hn0.ne' (by norm_num)]
    apply Real.log_le_log (by linarith)
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  -- upper bound on B
  have hup : mertensB n ≤ Real.log n + Real.log 4 := by
    have h1 := log_factorial_ge n
    have h2 := log_factorial_le' n
    have h3 := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ n by positivity)
    have : n * mertensB n ≤ n * (Real.log n + Real.log 4) := by nlinarith
    exact le_of_mul_le_mul_left this hn0
  have hlow : Real.log n - 1 - K₀ ≤ mertensB n := by
    have h1 := log_factorial_le n
    have h2 := log_factorial_ge' n
    have : n * (Real.log n - 1 - K₀) ≤ n * mertensB n := by nlinarith
    exact le_of_mul_le_mul_left this hn0
  rw [abs_le]
  constructor
  · have := le_max_right (Real.log 4) (1 + K₀ + Real.log 2)
    linarith
  · have := le_max_left (Real.log 4) (1 + K₀ + Real.log 2)
    linarith

/-! ## Partial summation against `∑ log p / p` -/

/-- The weight `c(k) = log k / k` on primes and `0` elsewhere. -/
def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log k / k else 0

lemma sum_Icc_primeWeight (t : ℝ) : ∑ k ∈ Icc 0 ⌊t⌋₊, primeWeight k = mertensB t := by
  unfold mertensB primesLE primeWeight
  rw [Finset.sum_filter, Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp [Nat.not_prime_zero]

theorem abel_mertens {K : ℝ} (hK : ∀ x : ℝ, 1 ≤ x → |mertensB x - Real.log x| ≤ K)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {w w' Φ : ℝ → ℝ}
    (hw : ∀ t ∈ Set.Icc a b, HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' (Set.Icc a b))
    (hΦ : ∀ t ∈ Set.Icc a b, HasDerivAt Φ (w t / t) t)
    (hsign : (∀ t ∈ Set.Icc a b, 0 ≤ w' t) ∨ (∀ t ∈ Set.Icc a b, w' t ≤ 0)) :
    |∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p / p * w p - (Φ b - Φ a)| ≤
      K * (|w a| + |w b| + |w b - w a|) := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  -- integrability facts
  have hwc : ContinuousOn w (Set.Icc a b) := fun t ht => (hw t ht).continuousAt.continuousWithinAt
  have hw'int : IntegrableOn w' (Set.Icc a b) := hw'.integrableOn_Icc
  have hderiv_eq : ∀ t ∈ Set.Icc a b, deriv w t = w' t := fun t ht => (hw t ht).deriv
  have hderiv_int : IntegrableOn (deriv w) (Set.Icc a b) :=
    hw'int.congr_fun (fun t ht => (hderiv_eq t ht).symm) measurableSet_Icc
  -- Abel summation
  have habel := sum_mul_eq_sub_sub_integral_mul primeWeight ha0 hab
    (fun t ht => (hw t ht).differentiableAt) hderiv_int
  simp only [sum_Icc_primeWeight] at habel
  have hlhs : ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, w k * primeWeight k =
      ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p / p * w p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    unfold primeWeight
    split_ifs <;> ring
  rw [hlhs] at habel
  have hint_congr : ∫ t in Set.Ioc a b, deriv w t * mertensB t =
      ∫ t in Set.Ioc a b, w' t * mertensB t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only
    rw [hderiv_eq t (Set.Ioc_subset_Icc_self ht)]
  rw [hint_congr] at habel
  -- integration by parts for the main term
  have hlog : ∀ t ∈ Set.uIcc a b, HasDerivAt Real.log (t⁻¹) t := by
    intro t ht
    rw [huIcc] at ht
    exact Real.hasDerivAt_log (by linarith [ht.1])
  have hinvint : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact continuousOn_inv₀.mono (fun t ht => by simp; linarith [ht.1])
  have hw'ii : IntervalIntegrable w' volume a b := hw'.intervalIntegrable_of_Icc hab
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hw t (huIcc ▸ ht)) hlog hw'ii hinvint
  have hΦint : ∫ t in a..b, w t * t⁻¹ = Φ b - Φ a := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hΦ t (huIcc ▸ ht))]
    · apply intervalIntegral.integral_congr
      intro t _
      simp [div_eq_mul_inv]
    · apply ContinuousOn.intervalIntegrable_of_Icc hab
      apply ContinuousOn.div hwc continuousOn_id
      intro t ht; simp; linarith [ht.1]
  rw [hΦint] at hparts
  -- integrability of w' * B and w' * log
  have hwB : IntegrableOn (fun t => w' t * mertensB t) (Set.Icc a b) := by
    have := integrableOn_mul_sum_Icc primeWeight (m := 0) ha0 hw'int
    simpa only [sum_Icc_primeWeight] using this
  have hwlog : IntegrableOn (fun t => w' t * Real.log t) (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    apply hw'.mul
    apply Real.continuousOn_log.mono
    intro t ht; simp; linarith [ht.1]
  have hwB' : IntegrableOn (fun t => w' t * mertensB t) (Set.Ioc a b) :=
    hwB.mono_set Set.Ioc_subset_Icc_self
  have hwlog' : IntegrableOn (fun t => w' t * Real.log t) (Set.Ioc a b) :=
    hwlog.mono_set Set.Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le hab] at hparts
  -- the difference
  have hdiff : ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p / p * w p - (Φ b - Φ a) =
      w b * (mertensB b - Real.log b) - w a * (mertensB a - Real.log a) -
        ∫ t in Set.Ioc a b, w' t * (mertensB t - Real.log t) := by
    rw [habel, hparts]
    have : ∫ t in Set.Ioc a b, w' t * (mertensB t - Real.log t) =
        (∫ t in Set.Ioc a b, w' t * mertensB t) - ∫ t in Set.Ioc a b, w' t * Real.log t := by
      rw [← integral_sub hwB' hwlog']
      congr 1; ext t; ring
    rw [this]; ring
  rw [hdiff]
  -- bound the integral
  have hKnn : 0 ≤ K := (abs_nonneg _).trans (hK a ha)
  have hint_bound : |∫ t in Set.Ioc a b, w' t * (mertensB t - Real.log t)| ≤
      K * |w b - w a| := by
    have habsint : IntegrableOn (fun t => K * |w' t|) (Set.Ioc a b) :=
      ((hw'int.mono_set Set.Ioc_subset_Icc_self).abs).const_mul K
    have h1 : |∫ t in Set.Ioc a b, w' t * (mertensB t - Real.log t)| ≤
        ∫ t in Set.Ioc a b, K * |w' t| := by
      have := norm_integral_le_of_norm_le habsint
        (f := fun t => w' t * (mertensB t - Real.log t))
        (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => by
          rw [Real.norm_eq_abs, abs_mul, mul_comm K]
          exact mul_le_mul_of_nonneg_left (hK t (by linarith [ht.1])) (abs_nonneg _)))
      simpa [Real.norm_eq_abs] using this
    have h2 : ∫ t in Set.Ioc a b, K * |w' t| = K * |w b - w a| := by
      rw [integral_const_mul]
      congr 1
      have hftc : ∫ t in a..b, w' t = w b - w a :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hw t (huIcc ▸ ht)) hw'ii
      rw [intervalIntegral.integral_of_le hab] at hftc
      rcases hsign with hs | hs
      · have : ∫ t in Set.Ioc a b, |w' t| = ∫ t in Set.Ioc a b, w' t := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          exact abs_of_nonneg (hs t (Set.Ioc_subset_Icc_self ht))
        rw [this, hftc, abs_of_nonneg]
        rw [← hftc]
        exact setIntegral_nonneg measurableSet_Ioc
          (fun t ht => hs t (Set.Ioc_subset_Icc_self ht))
      · have : ∫ t in Set.Ioc a b, |w' t| = -∫ t in Set.Ioc a b, w' t := by
          rw [← integral_neg]
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          exact abs_of_nonpos (hs t (Set.Ioc_subset_Icc_self ht))
        rw [this, hftc, abs_of_nonpos]
        rw [← hftc]
        exact setIntegral_nonpos measurableSet_Ioc
          (fun t ht => hs t (Set.Ioc_subset_Icc_self ht))
    linarith
  have hb1 : |w b * (mertensB b - Real.log b)| ≤ |w b| * K := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK b (by linarith)) (abs_nonneg _)
  have ha1 : |w a * (mertensB a - Real.log a)| ≤ |w a| * K := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK a ha) (abs_nonneg _)
  calc |w b * (mertensB b - Real.log b) - w a * (mertensB a - Real.log a) -
        ∫ t in Set.Ioc a b, w' t * (mertensB t - Real.log t)|
      ≤ |w b * (mertensB b - Real.log b)| + |w a * (mertensB a - Real.log a)| +
        |∫ t in Set.Ioc a b, w' t * (mertensB t - Real.log t)| := by
        have := abs_sub (w b * (mertensB b - Real.log b) - w a * (mertensB a - Real.log a))
          (∫ t in Set.Ioc a b, w' t * (mertensB t - Real.log t))
        have := abs_sub (w b * (mertensB b - Real.log b)) (w a * (mertensB a - Real.log a))
        linarith
    _ ≤ |w b| * K + |w a| * K + K * |w b - w a| := by linarith
    _ = K * (|w a| + |w b| + |w b - w a|) := by ring

/-! ## Elementary prime estimates -/

/-- `J(t) = ∑_{p ≤ t} 1/p`. -/
def primeRecipSum (t : ℝ) : ℝ := ∑ p ∈ primesLE ⌊t⌋₊, (1 : ℝ) / p

lemma primeCounting_eq_card (n : ℕ) : Nat.primeCounting n = (primesLE n).card := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
  congr 1
  ext p
  rw [mem_primesLE, Nat.mem_primesBelow]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

lemma primesLE_mono {m n : ℕ} (h : m ≤ n) : primesLE m ⊆ primesLE n := by
  intro p hp
  rw [mem_primesLE] at *
  exact ⟨hp.1, hp.2.trans h⟩

/-- `J(t) = 1/2 + ∑_{2 < p ≤ t} 1/p` for `t ≥ 2`. -/
lemma primeRecipSum_eq (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ primesLE n, (1 : ℝ) / p = 1 / 2 + ∑ p ∈ (Ioc 2 n).filter Nat.Prime, (1 : ℝ) / p := by
  unfold primesLE
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 2) hn]
  congr 1
  rw [show Ioc 0 2 = {1, 2} by decide]
  simp [Nat.prime_two, Nat.not_prime_one]

/-- **Mertens' second theorem**: `|∑_{p ≤ t} 1/p - log log t| ≤ C` for `t ≥ 2`. -/
theorem mertens_second : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
    |primeRecipSum t - Real.log (Real.log t)| ≤ C := by
  obtain ⟨K, hK0, hK⟩ := mertens_first
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K * (2 / Real.log 2) + 1 / 2 + |Real.log (Real.log 2)|, by positivity, fun t ht => ?_⟩
  have hab := abel_mertens hK (a := 2) (b := t) (by norm_num) ht
    (w := fun s => (Real.log s)⁻¹) (w' := fun s => -(s⁻¹) / Real.log s ^ 2)
    (Φ := fun s => Real.log (Real.log s))
    (fun s hs => by
      have hs0 : 0 < s := by linarith [hs.1]
      have hl : Real.log s ≠ 0 := (Real.log_pos (by linarith [hs.1])).ne'
      exact (Real.hasDerivAt_log hs0.ne').inv hl)
    (by
      apply ContinuousOn.div
      · exact (continuousOn_inv₀.mono (fun s hs => by simp; linarith [hs.1])).neg
      · exact (Real.continuousOn_log.mono (fun s hs => by simp; linarith [hs.1])).pow 2
      · intro s hs
        have : 0 < Real.log s := Real.log_pos (by linarith [hs.1])
        positivity)
    (fun s hs => by
      have hs0 : 0 < s := by linarith [hs.1]
      have hl : Real.log s ≠ 0 := (Real.log_pos (by linarith [hs.1])).ne'
      have := ((Real.hasDerivAt_log hs0.ne').log hl)
      convert this using 1
      field_simp)
    (Or.inr (fun s hs => by
      have hs0 : 0 < s := by linarith [hs.1]
      have : 0 < s⁻¹ := inv_pos.2 hs0
      have : 0 ≤ Real.log s ^ 2 := sq_nonneg _
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) this))
  simp only at hab
  -- simplify the weights
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hw : |(Real.log 2)⁻¹| + |(Real.log t)⁻¹| + |(Real.log t)⁻¹ - (Real.log 2)⁻¹| =
      2 / Real.log 2 := by
    have h1 : (Real.log t)⁻¹ ≤ (Real.log 2)⁻¹ :=
      inv_anti₀ hl2 (Real.log_le_log (by norm_num) ht)
    rw [abs_of_pos (inv_pos.2 hl2), abs_of_pos (inv_pos.2 hlt), abs_of_nonpos (by linarith)]
    ring
  rw [hw] at hab
  have hsum : ∑ p ∈ (Ioc ⌊(2 : ℝ)⌋₊ ⌊t⌋₊).filter Nat.Prime, Real.log p / p * (Real.log p)⁻¹ =
      ∑ p ∈ (Ioc 2 ⌊t⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
    rw [show ⌊(2 : ℝ)⌋₊ = 2 by norm_num]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    have : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp'.one_lt)).ne'
    field_simp
  rw [hsum] at hab
  have hn : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
  unfold primeRecipSum
  rw [primeRecipSum_eq _ hn]
  have := abs_le.1 hab
  rw [abs_le]
  have h1 := le_abs_self (Real.log (Real.log 2))
  have h2 := neg_abs_le (Real.log (Real.log 2))
  constructor <;> nlinarith [this.1, this.2]

/-- Consequence of Mertens' second theorem: for `2 ≤ a ≤ b`,
`∑_{a < p ≤ b} 1/p ≥ log log b - log log a - 2C`. -/
lemma sum_primes_Ioc_ge {C : ℝ}
    (hC : ∀ t : ℝ, 2 ≤ t → |primeRecipSum t - Real.log (Real.log t)| ≤ C)
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    Real.log (Real.log b) - Real.log (Real.log a) - 2 * C ≤
      ∑ p ∈ primesLE ⌊b⌋₊ \ primesLE ⌊a⌋₊, (1 : ℝ) / p := by
  have hsub : primesLE ⌊a⌋₊ ⊆ primesLE ⌊b⌋₊ := primesLE_mono (Nat.floor_le_floor hab)
  rw [Finset.sum_sdiff_eq_sub hsub]
  have h1 := abs_le.1 (hC a ha)
  have h2 := abs_le.1 (hC b (ha.trans hab))
  unfold primeRecipSum at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- `centralBinom n ≤ (2n)^{π(2n)}`. -/
lemma centralBinom_le_pow (n : ℕ) (hn : 0 < n) :
    Nat.centralBinom n ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  calc Nat.centralBinom n
      = ∏ p ∈ Finset.range (2 * n + 1), p ^ (Nat.centralBinom n).factorization p :=
        (Nat.prod_pow_factorization_centralBinom n).symm
    _ ≤ ∏ p ∈ Finset.range (2 * n + 1), (if p.Prime then 2 * n else 1) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro p _
        split_ifs with hp
        · exact Nat.pow_factorization_choose_le (by omega)
        · rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
    _ = (2 * n) ^ Nat.primeCounting (2 * n) := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
        congr 1
        rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
        rfl

/-- **Chebyshev's lower bound** `π(t) ≥ t / (4 log t)` for large `t`. -/
theorem chebyshev_lower : ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ t : ℝ, x₀ ≤ t →
    c * t / Real.log t ≤ Nat.primeCounting ⌊t⌋₊ := by
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
    (Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 8 by norm_num))
  refine ⟨1 / 4, by norm_num, max X 16, le_max_of_le_right (by norm_num), fun t ht => ?_⟩
  have ht16 : 16 ≤ t := le_of_max_le_right ht
  have hlogt : Real.log t ≤ t / 8 := by
    have := hX t (le_of_max_le_left ht)
    simp only [Real.norm_eq_abs, id] at this
    rw [abs_of_pos (Real.log_pos (by linarith)), abs_of_pos (by linarith)] at this
    linarith
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  set n := ⌊t / 2⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by norm_num; linarith)
  have hnt : (n : ℝ) ≤ t / 2 := Nat.floor_le (by linarith)
  have hnt' : t / 2 < n + 1 := Nat.lt_floor_add_one _
  have h2n : 2 * n ≤ ⌊t⌋₊ := by
    apply Nat.le_floor; push_cast; linarith
  have hmono : (Nat.primeCounting (2 * n) : ℝ) ≤ Nat.primeCounting ⌊t⌋₊ := by
    exact_mod_cast Nat.monotone_primeCounting h2n
  -- 4^n ≤ 2n * (2n)^π(2n)
  have hkey : (4 : ℝ) ^ n ≤ (2 * n) * (2 * n) ^ Nat.primeCounting (2 * n) := by
    have h1 := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn1
    have h2 := centralBinom_le_pow n hn1
    have : 4 ^ n ≤ 2 * n * (2 * n) ^ Nat.primeCounting (2 * n) :=
      h1.trans (Nat.mul_le_mul_left _ h2)
    exact_mod_cast this
  have h2n0 : (0 : ℝ) < 2 * n := by positivity
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_pow, Real.log_mul h2n0.ne' (by positivity), Real.log_pow] at hlog
  have hl2n : Real.log (2 * n) ≤ Real.log t := Real.log_le_log h2n0 (by linarith)
  have hl2n0 : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith)
  have hl4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9
    norm_num at this ⊢; linarith
  have hpc : 0 ≤ (Nat.primeCounting (2 * n) : ℝ) := by positivity
  -- n log 4 - log t ≤ π(2n) log t
  have h3 : (n : ℝ) * Real.log 4 - Real.log t ≤ (Nat.primeCounting (2 * n) : ℝ) * Real.log t := by
    have : (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * n) ≤
        (Nat.primeCounting (2 * n) : ℝ) * Real.log t := mul_le_mul_of_nonneg_left hl2n hpc
    linarith
  rw [div_le_iff₀ hlt]
  have : (n : ℝ) * Real.log 4 ≥ n := by
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  nlinarith

/-- An upper bound `π(x) ≤ 2x / log x` for large `x`. -/
theorem primeCounting_le_eventually : ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 2 * x / Real.log x := by
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 / 2 by norm_num))
  refine ⟨max X 2, le_max_right _ _, fun x hx => ?_⟩
  have h := hX x (le_of_max_le_left hx)
  have hx2 : 2 ≤ x := le_of_max_le_right hx
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  refine h.trans ?_
  have hl4 : Real.log 4 + 1 / 2 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    norm_num at this ⊢; linarith
  rw [div_le_div_iff_of_pos_right hlx]
  nlinarith

/-- Existence of a common multiple `L` of `1, …, m` with `L H_m ≤ e^{Cm}`. -/
theorem common_multiple_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → ∃ L : ℕ, 0 < L ∧
    (∀ j ∈ Icc 1 m, j ∣ L) ∧ (L : ℝ) * ∑ j ∈ Icc 1 m, (1 : ℝ) / j ≤ Real.exp (C * m) := by
  obtain ⟨X, hX2, hX⟩ := primeCounting_le_eventually
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  refine ⟨max 2 (Real.log X) + 1, by positivity, fun m hm => ?_⟩
  set L := ∏ p ∈ primesLE m, p ^ Nat.log p m with hL
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨L, ?_, ?_, ?_⟩
  · exact Finset.prod_pos (fun p hp => pow_pos (mem_primesLE.1 hp).1.pos _)
  · intro j hj
    rw [Finset.mem_Icc] at hj
    have hj0 : j ≠ 0 := by omega
    rw [← Nat.factorization_prod_pow_eq_self hj0]
    refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset j.primeFactors (primesLE m)
      (fun p => p ^ Nat.log p m) ?_)
    · apply Finset.prod_dvd_prod_of_dvd
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      apply pow_dvd_pow
      apply Nat.le_log_of_pow_le hp'.one_lt
      exact (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd j p)).trans hj.2
    · intro p hp
      rw [mem_primesLE]
      exact ⟨Nat.prime_of_mem_primeFactors hp,
        (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hj.2⟩
  · -- L ≤ m ^ π(m)
    have hLle : L ≤ m ^ Nat.primeCounting m := by
      rw [primeCounting_eq_card, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        (fun p _ => Nat.pow_log_le_self p (by omega))
    have hLpos : 0 < L := Finset.prod_pos (fun p hp => pow_pos (mem_primesLE.1 hp).1.pos _)
    have hlogL : Real.log L ≤ Nat.primeCounting m * Real.log m := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by exact_mod_cast hLpos)
      exact_mod_cast hLle
    have hπ : (Nat.primeCounting m : ℝ) * Real.log m ≤ max 2 (Real.log X) * m := by
      by_cases hmX : X ≤ m
      · have h := hX m hmX
        rw [Nat.floor_natCast] at h
        have hlm : 0 < Real.log m := Real.log_pos (by linarith)
        rw [le_div_iff₀ hlm] at h
        nlinarith [le_max_left 2 (Real.log X)]
      · push_neg at hmX
        have h1 : (Nat.primeCounting m : ℝ) ≤ m := by
          rw [primeCounting_eq_card]
          have := Finset.card_filter_le (Ioc 0 m) Nat.Prime
          simp only [Nat.card_Ioc, Nat.sub_zero] at this
          exact_mod_cast this
        have h2 : Real.log m ≤ Real.log X := Real.log_le_log hm0 hmX.le
        have h3 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
        have := le_max_right 2 (Real.log X)
        calc (Nat.primeCounting m : ℝ) * Real.log m ≤ m * Real.log X := by
              apply mul_le_mul h1 h2 h3 (by positivity)
          _ ≤ max 2 (Real.log X) * m := by nlinarith
    have hH : ∑ j ∈ Icc 1 m, (1 : ℝ) / j ≤ m := by
      calc ∑ j ∈ Icc 1 m, (1 : ℝ) / j ≤ ∑ _j ∈ Icc 1 m, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            have : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
            rw [div_le_one (by linarith)]; exact this
        _ = m := by simp
    have hL' : (L : ℝ) ≤ Real.exp (max 2 (Real.log X) * m) := by
      rw [← Real.exp_log (show (0 : ℝ) < L by exact_mod_cast hLpos)]
      exact Real.exp_le_exp.2 (hlogL.trans hπ)
    have hHe : ∑ j ∈ Icc 1 m, (1 : ℝ) / j ≤ Real.exp m :=
      hH.trans (by linarith [Real.add_one_le_exp (m : ℝ)])
    calc (L : ℝ) * ∑ j ∈ Icc 1 m, (1 : ℝ) / j
        ≤ Real.exp (max 2 (Real.log X) * m) * Real.exp m :=
          mul_le_mul hL' hHe (Finset.sum_nonneg (fun j _ => by positivity)) (by positivity)
      _ = Real.exp ((max 2 (Real.log X) + 1) * m) := by
          rw [← Real.exp_add]; ring_nf

/-! ## Finite reciprocal sums -/

lemma zero_mem_recipSubsetSums (A : Finset ℕ) : (0 : ℚ) ∈ recipSubsetSums A := by
  unfold recipSubsetSums
  exact Finset.mem_image.2 ⟨∅, by simp, by simp⟩

lemma card_recipSubsetSums_le (A : Finset ℕ) : (recipSubsetSums A).card ≤ 2 ^ A.card := by
  unfold recipSubsetSums
  exact (Finset.card_image_le).trans (by simp)

lemma one_le_card_recipSubsetSums (A : Finset ℕ) : 1 ≤ (recipSubsetSums A).card :=
  Finset.card_pos.2 ⟨0, zero_mem_recipSubsetSums A⟩

lemma recipSubsetSums_mono {A B : Finset ℕ} (h : A ⊆ B) :
    recipSubsetSums A ⊆ recipSubsetSums B := by
  unfold recipSubsetSums
  exact Finset.image_subset_image (Finset.powerset_mono.2 h)

/-- `1 ≤ S(N)`. -/
lemma one_le_S (N : ℕ) : 1 ≤ S N := one_le_card_recipSubsetSums _

/-- `S(N) ≤ 2^N`. -/
lemma S_le_two_pow (N : ℕ) : S N ≤ 2 ^ N := by
  have := card_recipSubsetSums_le (Icc 1 N)
  simpa [S] using this

lemma recipDissociated_empty : RecipDissociated ∅ := by
  intro B hB C hC _
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_empty] at hB hC
  simp_all

open Classical in
lemma le_R {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hd : RecipDissociated A) :
    A.card ≤ R N := by
  unfold R
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hA, hd⟩)

open Classical in
lemma exists_R (N : ℕ) : ∃ A ⊆ Icc 1 N, RecipDissociated A ∧ A.card = R N := by
  have hne : ((Icc 1 N).powerset.filter RecipDissociated).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, recipDissociated_empty⟩⟩
  obtain ⟨A, hA, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, by rw [R, hcard]⟩

/-- The signed-relation criterion for reciprocal dissociation. -/
theorem recipDissociated_iff_signed (A : Finset ℕ) :
    RecipDissociated A ↔ ∀ ε : ℕ → ℤ, (∀ n, ε n = -1 ∨ ε n = 0 ∨ ε n = 1) →
      ∑ n ∈ A, (ε n : ℚ) / n = 0 → ∀ n ∈ A, ε n = 0 := by
  classical
  constructor
  · intro hA ε hε hsum
    set P := A.filter (fun n => ε n = 1)
    set Q := A.filter (fun n => ε n = -1)
    have hsplit : ∑ n ∈ A, (ε n : ℚ) / n = ∑ n ∈ P, (1 : ℚ) / n - ∑ n ∈ Q, (1 : ℚ) / n := by
      have h1 : ∀ n ∈ A, (ε n : ℚ) / n = (if ε n = 1 then (1 : ℚ) / n else 0)
          - (if ε n = -1 then (1 : ℚ) / n else 0) := by
        intro n _
        rcases hε n with h | h | h <;> simp [h, neg_div]
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_filter, Finset.sum_filter]
    have hPQ : P = Q := by
      apply hA
      · simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
        exact Finset.filter_subset _ _
      · simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
        exact Finset.filter_subset _ _
      · simp only
        linarith
    intro n hn
    rcases hε n with h | h | h
    · have : n ∈ Q := Finset.mem_filter.2 ⟨hn, h⟩
      rw [← hPQ] at this
      have := (Finset.mem_filter.1 this).2
      omega
    · exact h
    · have : n ∈ P := Finset.mem_filter.2 ⟨hn, h⟩
      rw [hPQ] at this
      have := (Finset.mem_filter.1 this).2
      omega
  · intro h B hB C hC hBC
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hB hC
    simp only at hBC
    set ε : ℕ → ℤ := fun n => (if n ∈ B then 1 else 0) - (if n ∈ C then 1 else 0)
    have hε : ∀ n, ε n = -1 ∨ ε n = 0 ∨ ε n = 1 := by
      intro n; simp only [ε]; split_ifs <;> simp
    have hsum : ∑ n ∈ A, (ε n : ℚ) / n = 0 := by
      have h1 : ∀ n ∈ A, (ε n : ℚ) / n = (if n ∈ B then (1 : ℚ) / n else 0)
          - (if n ∈ C then (1 : ℚ) / n else 0) := by
        intro n _
        simp only [ε]; split_ifs <;> simp [neg_div]
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_filter,
        ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 hB, Finset.inter_eq_right.2 hC, hBC, sub_self]
    have h0 := h ε hε hsum
    ext n
    constructor
    · intro hn
      have := h0 n (hB hn)
      simp only [ε, hn, if_true] at this
      by_contra hc
      simp [hc] at this
    · intro hn
      have := h0 n (hC hn)
      simp only [ε, hn, if_true] at this
      by_contra hc
      simp [hc] at this

/-- `2^{R(N)} ≤ S(N)`. -/
theorem two_pow_R_le_S (N : ℕ) : 2 ^ R N ≤ S N := by
  obtain ⟨A, hA, hd, hc⟩ := exists_R N
  rw [← hc, ← Finset.card_powerset]
  unfold S recipSubsetSums
  rw [← Finset.card_image_of_injOn hd]
  exact Finset.card_le_card (Finset.image_subset_image (Finset.powerset_mono.2 hA))

/-- `R(N) ≤ log S(N) / log 2`. -/
theorem R_le_log_S_div_log_two (N : ℕ) : (R N : ℝ) ≤ Real.log (S N) / Real.log 2 := by
  rw [le_div_iff₀ (Real.log_pos (by norm_num)), ← Real.log_pow]
  apply Real.log_le_log (by positivity)
  exact_mod_cast two_pow_R_le_S N

/-- Subadditivity of `E` on disjoint unions. -/
lemma card_recipSubsetSums_union_le {A B : Finset ℕ} (h : Disjoint A B) :
    (recipSubsetSums (A ∪ B)).card ≤ (recipSubsetSums A).card * (recipSubsetSums B).card := by
  classical
  rw [← Finset.card_product]
  have : recipSubsetSums (A ∪ B) ⊆
      (recipSubsetSums A ×ˢ recipSubsetSums B).image (fun q => q.1 + q.2) := by
    intro r hr
    unfold recipSubsetSums at hr
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hr
    rw [Finset.mem_powerset] at hX
    refine Finset.mem_image.2 ⟨(∑ n ∈ X ∩ A, (1 : ℚ) / n, ∑ n ∈ X ∩ B, (1 : ℚ) / n), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨?_, ?_⟩
      · exact Finset.mem_image.2 ⟨X ∩ A, Finset.mem_powerset.2 Finset.inter_subset_right, rfl⟩
      · exact Finset.mem_image.2 ⟨X ∩ B, Finset.mem_powerset.2 Finset.inter_subset_right, rfl⟩
    · simp only
      rw [← Finset.sum_union]
      · congr 1
        rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.2 hX]
      · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right h)
  exact (Finset.card_le_card this).trans Finset.card_image_le

/-- Subadditivity of `E` on a pairwise disjoint union of blocks. -/
lemma card_recipSubsetSums_biUnion_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Finset ℕ) (h : (s : Set ι).PairwiseDisjoint f) :
    (recipSubsetSums (s.biUnion f)).card ≤ ∏ i ∈ s, (recipSubsetSums (f i)).card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.prod_empty]
    exact card_recipSubsetSums_le ∅ |>.trans (by simp)
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert hi]
    have hdisj : Disjoint (f i) (s.biUnion f) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact h (by simp) (by simp [hj]) (by rintro rfl; exact hi hj)
    refine (card_recipSubsetSums_union_le hdisj).trans ?_
    exact Nat.mul_le_mul_left _ (ih (h.subset (by simp)))

/-- `|E({p, 2p, …, mp})| = S(m)`. -/
lemma card_recipSubsetSums_multiples (p m : ℕ) (hp : 0 < p) :
    (recipSubsetSums ((Icc 1 m).image (fun j => p * j))).card = S m := by
  classical
  have hinj : Set.InjOn (fun j => p * j) (Icc 1 m : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hp hab
  have key : recipSubsetSums ((Icc 1 m).image (fun j => p * j)) =
      (recipSubsetSums (Icc 1 m)).image (fun r : ℚ => r / (p : ℚ)) := by
    unfold recipSubsetSums
    ext r
    simp only [Finset.mem_image, Finset.mem_powerset]
    constructor
    · rintro ⟨X, hX, rfl⟩
      refine ⟨_, ⟨(Icc 1 m).filter (fun j => p * j ∈ X), Finset.filter_subset _ _, rfl⟩, ?_⟩
      rw [Finset.sum_div]
      have : X = ((Icc 1 m).filter (fun j => p * j ∈ X)).image (fun j => p * j) := by
        ext n
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · intro hn
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (hX hn)
          exact ⟨j, ⟨hj, hn⟩, rfl⟩
        · rintro ⟨j, ⟨_, hj⟩, rfl⟩
          exact hj
      conv_rhs => rw [this]
      rw [Finset.sum_image (fun a ha b hb hab => hinj (Finset.mem_filter.1 ha).1
        (Finset.mem_filter.1 hb).1 hab)]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      field_simp
    · rintro ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
      refine ⟨Y.image (fun j => p * j), Finset.image_subset_image hY, ?_⟩
      rw [Finset.sum_div, Finset.sum_image (fun a ha b hb hab => hinj (hY ha) (hY hb) hab)]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      field_simp
  rw [key, Finset.card_image_of_injective]
  · rfl
  · intro a b hab
    have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
    simpa [hp'] using hab

/-- The harmonic-sum bound `H_m ≤ 1 + log m`. -/
lemma harmonic_sum_le_one_add_log (m : ℕ) :
    ∑ j ∈ Icc 1 m, (1 : ℝ) / j ≤ 1 + Real.log m := by
  have h := _root_.harmonic_le_one_add_log m
  have : (harmonic m : ℝ) = ∑ j ∈ Icc 1 m, (1 : ℝ) / j := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp
  rw [← this]
  exact h

/-! ## Iterated logarithms and the stopping index -/

lemma iterLog_zero (x : ℝ) : iterLog 0 x = x := rfl

lemma iterLog_succ (j : ℕ) (x : ℝ) : iterLog (j + 1) x = Real.log (iterLog j x) :=
  Function.iterate_succ_apply' _ _ _

lemma iterLog_succ' (j : ℕ) (x : ℝ) : iterLog (j + 1) x = iterLog j (Real.log x) :=
  Function.iterate_succ_apply _ _ _

lemma iterLog_add (i j : ℕ) (x : ℝ) : iterLog (i + j) x = iterLog i (iterLog j x) :=
  Function.iterate_add_apply _ _ _ _

lemma iterLog_one (x : ℝ) : iterLog 1 x = Real.log x := rfl

/-- `log t ≤ t / 2` for `t > 0`. -/
lemma log_le_half {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / 2 := by
  have h1 : 1 + t / 4 ≤ Real.exp (t / 4) := by linarith [Real.add_one_le_exp (t / 4)]
  have h2 : t ≤ Real.exp (t / 2) := by
    have : Real.exp (t / 2) = Real.exp (t / 4) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    rw [this]
    nlinarith [sq_nonneg (t / 4 - 1)]
  calc Real.log t ≤ Real.log (Real.exp (t / 2)) := Real.log_le_log ht h2
    _ = t / 2 := Real.log_exp _

/-- If `ℓ_j(x) > 0` then `ℓ_j(x) = exp ℓ_{j+1}(x)`. -/
lemma iterLog_eq_exp {j : ℕ} {x : ℝ} (h : 0 < iterLog j x) :
    iterLog j x = Real.exp (iterLog (j + 1) x) := by
  rw [iterLog_succ, Real.exp_log h]

/-- The set of admissible indices in the definition of `k_A(x)`. -/
def stopSet (A x : ℝ) : Set ℕ := {k : ℕ | 3 ≤ k ∧ ∀ j ∈ Icc 3 k, A ≤ iterLog j x}

lemma stopIndex_eq (A x : ℝ) : stopIndex A x = sSup (stopSet A x) := rfl

lemma stopSet_decay {A x : ℝ} (hA : 0 < A) {k : ℕ} (hk : k ∈ stopSet A x) :
    ∀ j, 3 ≤ j → j ≤ k → iterLog j x * 2 ^ (j - 3) ≤ iterLog 3 x := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; simp
  | succ j hj ih =>
    intro hjk
    have hpos : 0 < iterLog j x := lt_of_lt_of_le hA (hk.2 j (by simp; omega))
    have := ih (by omega)
    rw [iterLog_succ, show j + 1 - 3 = (j - 3) + 1 by omega, pow_succ]
    have h := log_le_half hpos
    have : (0 : ℝ) < 2 ^ (j - 3) := by positivity
    nlinarith

lemma stopSet_bddAbove {A x : ℝ} (hA : 0 < A) : BddAbove (stopSet A x) := by
  refine ⟨3 + ⌈iterLog 3 x / A⌉₊, fun k hk => ?_⟩
  have h := stopSet_decay hA hk k hk.1 le_rfl
  have hAk : A ≤ iterLog k x := hk.2 k (by simp [hk.1])
  have h2 : A * 2 ^ (k - 3) ≤ iterLog 3 x := by
    have : (0 : ℝ) ≤ 2 ^ (k - 3) := by positivity
    nlinarith
  have h3 : ((k - 3 : ℕ) : ℝ) ≤ iterLog 3 x / A := by
    rw [le_div_iff₀ hA]
    have : ((k - 3 : ℕ) : ℝ) < 2 ^ (k - 3) := by exact_mod_cast Nat.lt_two_pow_self
    nlinarith
  have h4 : k - 3 ≤ ⌈iterLog 3 x / A⌉₊ := by
    exact_mod_cast h3.trans (Nat.le_ceil _)
  omega

/-- Basic properties of `k = k_A(x)`: `3 ≤ k`, `ℓ_j(x) ≥ A` for `3 ≤ j ≤ k`,
and `ℓ_{k+1}(x) < A`. -/
lemma stopIndex_spec {A x : ℝ} (hA : 0 < A) (h3 : A ≤ iterLog 3 x) :
    3 ≤ stopIndex A x ∧ (∀ j ∈ Icc 3 (stopIndex A x), A ≤ iterLog j x) ∧
      iterLog (stopIndex A x + 1) x < A := by
  have hne : (stopSet A x).Nonempty := ⟨3, le_rfl, fun j hj => by
    rw [Finset.mem_Icc] at hj; rwa [show j = 3 by omega]⟩
  have hmem : stopIndex A x ∈ stopSet A x := Nat.sSup_mem hne (stopSet_bddAbove hA)
  refine ⟨hmem.1, hmem.2, ?_⟩
  by_contra hcon
  push_neg at hcon
  have : stopIndex A x + 1 ∈ stopSet A x := by
    refine ⟨by have := hmem.1; omega, fun j hj => ?_⟩
    rw [Finset.mem_Icc] at hj
    rcases eq_or_lt_of_le hj.2 with h | h
    · rw [h]; exact hcon
    · exact hmem.2 j (Finset.mem_Icc.2 ⟨hj.1, by omega⟩)
  have := le_csSup (stopSet_bddAbove hA) this
  rw [← stopIndex_eq] at this
  omega

/-- The threshold `T_A = exp(exp(exp A))`. -/
def towerThreshold (A : ℝ) : ℝ := Real.exp (Real.exp (Real.exp A))

lemma le_exp_self (t : ℝ) : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]

lemma iterLog_ge_of_threshold {A x : ℝ} (hx : towerThreshold A ≤ x) :
    ∀ j ≤ 3, A ≤ iterLog j x := by
  have h0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h1 : Real.exp (Real.exp A) ≤ iterLog 1 x := by
    rw [iterLog_one, Real.le_log_iff_exp_le h0]; exact hx
  have h1' : 0 < iterLog 1 x := lt_of_lt_of_le (Real.exp_pos _) h1
  have h2 : Real.exp A ≤ iterLog 2 x := by
    rw [iterLog_succ, Real.le_log_iff_exp_le h1']; exact h1
  have h2' : 0 < iterLog 2 x := lt_of_lt_of_le (Real.exp_pos _) h2
  have h3 : A ≤ iterLog 3 x := by
    rw [iterLog_succ, Real.le_log_iff_exp_le h2']; exact h2
  intro j hj
  interval_cases j
  · exact (le_exp_self A).trans ((le_exp_self _).trans ((le_exp_self _).trans hx))
  · exact (le_exp_self A).trans ((le_exp_self _).trans h1)
  · exact (le_exp_self A).trans h2
  · exact h3

section stop

variable {A x : ℝ} (hA : 0 < A) (hx : towerThreshold A ≤ x)
include hA hx

lemma stopIndex_three_le : 3 ≤ stopIndex A x :=
  (stopIndex_spec hA (iterLog_ge_of_threshold hx 3 le_rfl)).1

lemma stopIndex_ge : ∀ j ≤ stopIndex A x, A ≤ iterLog j x := by
  intro j hj
  rcases le_or_gt j 3 with h | h
  · exact iterLog_ge_of_threshold hx j h
  · exact (stopIndex_spec hA (iterLog_ge_of_threshold hx 3 le_rfl)).2.1 j
      (Finset.mem_Icc.2 ⟨h.le, hj⟩)

lemma stopIndex_pos : ∀ j ≤ stopIndex A x, 0 < iterLog j x :=
  fun j hj => lt_of_lt_of_le hA (stopIndex_ge hA hx j hj)

lemma stopIndex_next_lt : iterLog (stopIndex A x + 1) x < A :=
  (stopIndex_spec hA (iterLog_ge_of_threshold hx 3 le_rfl)).2.2

/-- `ℓ_k(x) < e^A`. -/
lemma stopIndex_last_lt : iterLog (stopIndex A x) x < Real.exp A := by
  have h := stopIndex_next_lt hA hx
  rw [iterLog_succ, Real.log_lt_iff_lt_exp (stopIndex_pos hA hx _ le_rfl)] at h
  exact h

/-- `ℓ_{k-1}(x) < exp(e^A)`. -/
lemma stopIndex_prev_lt : iterLog (stopIndex A x - 1) x < Real.exp (Real.exp A) := by
  have hk := stopIndex_three_le hA hx
  have hpos := stopIndex_pos hA hx (stopIndex A x - 1) (by omega)
  rw [iterLog_eq_exp hpos, show stopIndex A x - 1 + 1 = stopIndex A x by omega]
  exact Real.exp_lt_exp.2 (stopIndex_last_lt hA hx)

/-- `ℓ_j(x) ≥ T_A` for `j + 3 ≤ k`. -/
lemma stopIndex_ge_threshold : ∀ j, j + 3 ≤ stopIndex A x → towerThreshold A ≤ iterLog j x := by
  intro j hj
  have h3 := stopIndex_ge hA hx (j + 3) hj
  have p0 := stopIndex_pos hA hx j (by omega)
  have p1 := stopIndex_pos hA hx (j + 1) (by omega)
  have p2 := stopIndex_pos hA hx (j + 2) (by omega)
  rw [iterLog_eq_exp p0, iterLog_eq_exp p1, iterLog_eq_exp p2]
  unfold towerThreshold
  gcongr

end stop

/-- A geometric-series bound. -/
lemma sum_le_two_mul_last (s : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) (hs : ∀ j, 0 ≤ s j)
    (hdec : ∀ j, a ≤ j → j < b → 2 * s j ≤ s (j + 1)) :
    ∑ j ∈ Icc a b, s j ≤ 2 * s b := by
  induction b, hab using Nat.le_induction with
  | base => simp; linarith [hs a]
  | succ b hb ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := ih (fun j h1 h2 => hdec j h1 (by omega))
    have := hdec b hb (by omega)
    linarith

/-- `∑_{j=3}^{k} 1/ℓ_j(x) ≤ 2/A` for `A ≥ 2`. -/
lemma stopIndex_sum_inv_le {A x : ℝ} (hA : 2 ≤ A) (hx : towerThreshold A ≤ x) :
    ∑ j ∈ Icc 3 (stopIndex A x), 1 / iterLog j x ≤ 2 / A := by
  have hA0 : 0 < A := by linarith
  have hk := stopIndex_three_le hA0 hx
  set k := stopIndex A x
  have hb := sum_le_two_mul_last (fun j => if j ≤ k then 1 / iterLog j x else 0) 3 k hk
    (fun j => by
      simp only; split_ifs with h
      · exact (one_div_pos.2 (stopIndex_pos hA0 hx j h)).le
      · exact le_rfl)
    (fun j h1 h2 => by
      simp only [if_pos h2.le, if_pos (show j + 1 ≤ k by omega)]
      have hp := stopIndex_pos hA0 hx j h2.le
      have hp1 := stopIndex_pos hA0 hx (j + 1) (by omega)
      have hge : 2 ≤ iterLog j x := hA.trans (stopIndex_ge hA0 hx j h2.le)
      rw [iterLog_succ] at hp1 ⊢
      have := log_le_half hp
      rw [mul_one_div, div_le_div_iff₀ hp hp1]
      linarith)
  simp only [le_refl, if_true] at hb
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [if_pos (Finset.mem_Icc.1 hj).2])] at hb
  refine hb.trans ?_
  have hk' := stopIndex_ge hA0 hx k le_rfl
  rw [mul_one_div, div_le_div_iff₀ (stopIndex_pos hA0 hx k le_rfl) hA0]
  linarith

/-- `∏_{j=3}^{k} (ℓ_j(x) + c) ≤ P_A(x) exp(2c/A)`. -/
lemma stopIndex_prod_add_le {A x : ℝ} (hA : 2 ≤ A) (hx : towerThreshold A ≤ x) {c : ℝ}
    (hc : 0 ≤ c) :
    ∏ j ∈ Icc 3 (stopIndex A x), (iterLog j x + c) ≤
      stopProd A x * Real.exp (2 * c / A) := by
  have hA0 : 0 < A := by linarith
  have hprod : ∏ j ∈ Icc 3 (stopIndex A x), (iterLog j x + c) =
      stopProd A x * ∏ j ∈ Icc 3 (stopIndex A x), (1 + c / iterLog j x) := by
    rw [stopProd, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    have := stopIndex_pos hA0 hx j (Finset.mem_Icc.1 hj).2
    field_simp
  rw [hprod]
  have hP : 0 ≤ stopProd A x := Finset.prod_nonneg (fun j hj =>
    (stopIndex_pos hA0 hx j (Finset.mem_Icc.1 hj).2).le)
  apply mul_le_mul_of_nonneg_left _ hP
  calc ∏ j ∈ Icc 3 (stopIndex A x), (1 + c / iterLog j x)
      ≤ ∏ j ∈ Icc 3 (stopIndex A x), Real.exp (c * (1 / iterLog j x)) := by
        apply Finset.prod_le_prod
        · intro j hj
          have := stopIndex_pos hA0 hx j (Finset.mem_Icc.1 hj).2
          positivity
        · intro j _
          rw [mul_one_div]
          linarith [Real.add_one_le_exp (c / iterLog j x)]
    _ = Real.exp (c * ∑ j ∈ Icc 3 (stopIndex A x), 1 / iterLog j x) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (2 * c / A) := by
        apply Real.exp_le_exp.2
        have := stopIndex_sum_inv_le hA hx
        calc c * ∑ j ∈ Icc 3 (stopIndex A x), 1 / iterLog j x ≤ c * (2 / A) :=
              mul_le_mul_of_nonneg_left this hc
          _ = 2 * c / A := by ring

lemma stopProd_nonneg {A x : ℝ} (hA : 0 < A) (hx : towerThreshold A ≤ x) :
    0 ≤ stopProd A x :=
  Finset.prod_nonneg (fun j hj => (stopIndex_pos hA hx j (Finset.mem_Icc.1 hj).2).le)

lemma towerThreshold_mono {A B : ℝ} (h : A ≤ B) : towerThreshold A ≤ towerThreshold B := by
  unfold towerThreshold; gcongr

/-- Comparison of thresholds, `P_B(x) ≤ P_A(x) ≤ B^{⌈B⌉} P_B(x)`. -/
theorem stopProd_threshold_comparison {A B x : ℝ} (hA : 2 ≤ A) (hAB : A ≤ B)
    (hx : towerThreshold B ≤ x) :
    stopProd B x ≤ stopProd A x ∧ stopProd A x ≤ B ^ ⌈B⌉₊ * stopProd B x := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hxA : towerThreshold A ≤ x := (towerThreshold_mono hAB).trans hx
  set h := stopIndex B x with hh
  set k := stopIndex A x with hk
  have hh3 := stopIndex_three_le hB0 hx
  have hhk : h ≤ k := by
    have hmem : h ∈ stopSet A x := ⟨hh3, fun j hj =>
      hAB.trans (stopIndex_ge hB0 hx j (Finset.mem_Icc.1 hj).2)⟩
    exact le_csSup (stopSet_bddAbove hA0) hmem
  have hsplit : stopProd A x = stopProd B x * ∏ j ∈ Ioc h k, iterLog j x := by
    unfold stopProd
    rw [← hh, ← hk, show (3 : ℕ) = 2 + 1 from rfl, Finset.Icc_add_one_left_eq_Ioc,
      Finset.Icc_add_one_left_eq_Ioc, Finset.prod_Ioc_consecutive _ (by omega) hhk]
  have hge1 : ∀ j ∈ Ioc h k, A ≤ iterLog j x := fun j hj =>
    stopIndex_ge hA0 hxA j (Finset.mem_Ioc.1 hj).2
  have hPB := stopProd_nonneg hB0 hx
  have hone : 1 ≤ ∏ j ∈ Ioc h k, iterLog j x :=
    Finset.prod_induction _ (fun t => 1 ≤ t) (fun a b ha hb => by nlinarith)
      le_rfl (fun j hj => by linarith [hge1 j hj])
  refine ⟨?_, ?_⟩
  · rw [hsplit]; nlinarith
  · rw [hsplit, mul_comm (B ^ _)]
    apply mul_le_mul_of_nonneg_left _ hPB
    -- each factor is < B, and there are at most ⌈B⌉ factors
    have hlt : ∀ j ∈ Ioc h k, iterLog j x ≤ B := by
      intro j hj
      rw [Finset.mem_Ioc] at hj
      have hnext : iterLog (h + 1) x < B := stopIndex_next_lt hB0 hx
      -- ℓ is decreasing along j ≤ k
      have hdec : ∀ i, h + 1 + i ≤ k → iterLog (h + 1 + i) x ≤ iterLog (h + 1) x := by
        intro i
        induction i with
        | zero => intro _; simp
        | succ i ih =>
          intro hi
          have hp := stopIndex_pos hA0 hxA (h + 1 + i) (by omega)
          rw [show h + 1 + (i + 1) = (h + 1 + i) + 1 by ring, iterLog_succ]
          have := ih (by omega)
          linarith [Real.log_le_sub_one_of_pos hp]
      have := hdec (j - (h + 1)) (by omega)
      rw [show h + 1 + (j - (h + 1)) = j by omega] at this
      linarith
    have hcount : k - h ≤ ⌈B⌉₊ := by
      -- ℓ_j - ℓ_{j+1} ≥ 1 along h < j < k
      have hstep : ∀ i, h + 1 + i ≤ k → iterLog (h + 1 + i) x + i ≤ iterLog (h + 1) x := by
        intro i
        induction i with
        | zero => intro _; simp
        | succ i ih =>
          intro hi
          have hp := stopIndex_pos hA0 hxA (h + 1 + i) (by omega)
          rw [show h + 1 + (i + 1) = (h + 1 + i) + 1 by ring, iterLog_succ]
          have := ih (by omega)
          push_cast
          linarith [Real.log_le_sub_one_of_pos hp]
      rcases eq_or_lt_of_le hhk with heq | hlt'
      · omega
      have := hstep (k - (h + 1)) (by omega)
      rw [show h + 1 + (k - (h + 1)) = k by omega] at this
      have hkA := stopIndex_ge hA0 hxA k le_rfl
      have hnext : iterLog (h + 1) x < B := stopIndex_next_lt hB0 hx
      have : ((k - (h + 1) : ℕ) : ℝ) < B := by linarith
      have : ((k - h : ℕ) : ℝ) ≤ ⌈B⌉₊ := by
        have h1 : ((k - h : ℕ) : ℝ) = ((k - (h + 1) : ℕ) : ℝ) + 1 := by
          rw [show k - h = (k - (h + 1)) + 1 by omega]; push_cast; ring
        rw [h1]
        have := Nat.le_ceil B
        linarith
      exact_mod_cast this
    calc ∏ j ∈ Ioc h k, iterLog j x ≤ ∏ _j ∈ Ioc h k, B :=
          Finset.prod_le_prod (fun j hj => by linarith [hge1 j hj]) hlt
      _ = B ^ (k - h) := by simp
      _ ≤ B ^ ⌈B⌉₊ := pow_le_pow_right₀ (by linarith) hcount

/-! ## A dissociated set of reciprocals -/

/-- Membership in the set `𝒰`: `m ≥ 1` and `1/m ≠ ∑_{j=1}^{m-1} ε_j / j` for every
`ε ∈ {-1, 0, 1}^{m-1}`. -/
def InU (m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ ε : ℕ → ℤ, (∀ j, ε j = -1 ∨ ε j = 0 ∨ ε j = 1) →
    (1 : ℚ) / m ≠ ∑ j ∈ Ico 1 m, (ε j : ℚ) / j

open Classical in
/-- `𝒰 ∩ [1, x]`. -/
def Uset (x : ℝ) : Finset ℕ := (Icc 1 ⌊x⌋₊).filter InU

/-- `u(x) = |{m ∈ 𝒰 : m ≤ x}|`. -/
def uCount (x : ℝ) : ℕ := (Uset x).card

/-- `W(x) = ∑_{m ∈ 𝒰, m ≤ x} 1/m`. -/
def Wsum (x : ℝ) : ℝ := ∑ m ∈ Uset x, (1 : ℝ) / m

lemma mem_Uset {x : ℝ} {m : ℕ} : m ∈ Uset x ↔ (1 ≤ m ∧ m ≤ ⌊x⌋₊) ∧ InU m := by
  classical
  unfold Uset
  rw [Finset.mem_filter, Finset.mem_Icc]

lemma mem_Uset' {x : ℝ} (hx : 0 ≤ x) {m : ℕ} : m ∈ Uset x ↔ InU m ∧ (m : ℝ) ≤ x := by
  rw [mem_Uset]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, (Nat.le_floor_iff hx).1 h2⟩
  · rintro ⟨h3, h2⟩; exact ⟨⟨h3.1, Nat.le_floor h2⟩, h3⟩

lemma Wsum_nonneg (x : ℝ) : 0 ≤ Wsum x := Finset.sum_nonneg (fun _ _ => by positivity)

lemma Uset_mono {x y : ℝ} (h : x ≤ y) : Uset x ⊆ Uset y := by
  intro m hm
  rw [mem_Uset] at *
  exact ⟨⟨hm.1.1, hm.1.2.trans (Nat.floor_le_floor h)⟩, hm.2⟩

lemma Wsum_mono : Monotone Wsum := by
  intro x y h
  exact Finset.sum_le_sum_of_subset_of_nonneg (Uset_mono h) (fun _ _ _ => by positivity)

lemma one_InU : InU 1 := ⟨le_rfl, fun ε _ => by simp⟩

/-- Amplification: if `m ∈ 𝒰`, `L` is a common multiple of
`1, …, m` and `p > L H_m` is prime, then `mp ∈ 𝒰`. -/
theorem InU_mul_prime {m L p : ℕ} (hm : InU m) (hL : 0 < L) (hdvd : ∀ j ∈ Icc 1 m, j ∣ L)
    (hp : p.Prime) (hLp : (L : ℝ) * ∑ j ∈ Icc 1 m, (1 : ℝ) / j < p) : InU (m * p) := by
  classical
  have hm1 := hm.1
  refine ⟨Nat.mul_pos hm1 hp.pos, fun ε hε heq => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  -- cast the relation to ℝ
  have heqR : (1 : ℝ) / (m * p : ℕ) = ∑ n ∈ Ico 1 (m * p), (ε n : ℝ) / n := by
    have := congrArg (fun q : ℚ => (q : ℝ)) heq
    push_cast at this ⊢
    exact this
  -- split according to divisibility by p
  set F := (Ico 1 (m * p)).filter (fun n => ¬ p ∣ n) with hF
  have himage : (Ico 1 (m * p)).filter (fun n => p ∣ n) = (Ico 1 m).image (fun j => p * j) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, j, rfl⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with h | h
        · subst h; omega
        · exact h
      · have : p * j < p * m := by rw [mul_comm p m]; exact h2
        exact Nat.lt_of_mul_lt_mul_left this
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hp.pos h1, ?_⟩, dvd_mul_right p j⟩
      rw [mul_comm m p]
      exact Nat.mul_lt_mul_of_pos_left h2 hp.pos
  have hsplit : ∑ n ∈ Ico 1 (m * p), (ε n : ℝ) / n =
      ∑ j ∈ Ico 1 m, (ε (p * j) : ℝ) / (p * j : ℕ) + ∑ n ∈ F, (ε n : ℝ) / n := by
    rw [← Finset.sum_filter_add_sum_filter_not (Ico 1 (m * p)) (fun n => p ∣ n), himage,
      Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp.pos hab)]
  -- the integer b
  set b : ℤ := ((L / m : ℕ) : ℤ) - ∑ j ∈ Ico 1 m, ε (p * j) * ((L / j : ℕ) : ℤ) with hb
  have hbR : (b : ℝ) = L * (1 / m - ∑ j ∈ Ico 1 m, (ε (p * j) : ℝ) / j) := by
    rw [hb, Int.cast_sub, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hdvd m (Finset.mem_Icc.2 ⟨hm1, le_rfl⟩)) hm0.ne', mul_sub, Finset.mul_sum]
    congr 1
    · field_simp
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
      rw [Nat.cast_div (hdvd j (Finset.mem_Icc.2 ⟨hj.1, hj.2.le⟩)) hj0]
      field_simp
  -- b = p L R
  have hbpR : (b : ℝ) = p * L * ∑ n ∈ F, (ε n : ℝ) / n := by
    rw [hbR]
    have h1 : ∑ n ∈ F, (ε n : ℝ) / n =
        1 / (m * p) - ∑ j ∈ Ico 1 m, (ε (p * j) : ℝ) / (p * j : ℕ) := by
      have e := heqR.trans hsplit
      push_cast at e ⊢
      linarith
    rw [h1]
    have : ∑ j ∈ Ico 1 m, (ε (p * j) : ℝ) / (p * j : ℕ) =
        (1 / p) * ∑ j ∈ Ico 1 m, (ε (p * j) : ℝ) / j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      field_simp
    rw [this]
    field_simp
  -- b ≠ 0
  have hb0 : b ≠ 0 := by
    intro h0
    apply hm.2 (fun j => ε (p * j)) (fun j => hε _)
    have : (1 : ℝ) / m = ∑ j ∈ Ico 1 m, (ε (p * j) : ℝ) / j := by
      have h' : (b : ℝ) = 0 := by exact_mod_cast h0
      rw [hbR] at h'
      have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      have := (mul_eq_zero.1 h').resolve_left hL0
      linarith
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact this
  -- |b| < p
  have hbabs : |b| < (p : ℤ) := by
    have h1 : |(b : ℝ)| ≤ L * ∑ j ∈ Icc 1 m, (1 : ℝ) / j := by
      rw [hbR, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ L)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hIcc : ∑ j ∈ Icc 1 m, (1 : ℝ) / j = ∑ j ∈ Ico 1 m, (1 : ℝ) / j + 1 / m := by
        rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top hm1]
      rw [hIcc]
      have habs : |∑ j ∈ Ico 1 m, (ε (p * j) : ℝ) / j| ≤ ∑ j ∈ Ico 1 m, (1 : ℝ) / j := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j hj => ?_))
        rw [Finset.mem_Ico] at hj
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
        rw [abs_div, abs_of_pos hj0]
        apply div_le_div_of_nonneg_right _ hj0.le
        rcases hε (p * j) with h | h | h <;> simp [h]
      have := abs_sub (1 / (m : ℝ)) (∑ j ∈ Ico 1 m, (ε (p * j) : ℝ) / j)
      rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / m)] at this
      linarith
    have h2 : |(b : ℝ)| < p := lt_of_le_of_lt h1 hLp
    have : ((|b| : ℤ) : ℝ) < ((p : ℤ) : ℝ) := by push_cast; exact h2
    exact_mod_cast this
  -- the product of the integers in F
  set Q : ℕ := ∏ n ∈ F, n with hQ
  have hFpos : ∀ n ∈ F, 0 < n := fun n hn => by
    rw [hF, Finset.mem_filter, Finset.mem_Ico] at hn; omega
  set A : ℤ := ∑ n ∈ F, ε n * ((Q / n : ℕ) : ℤ) with hA
  have hAR : (A : ℝ) = Q * ∑ n ∈ F, (ε n : ℝ) / n := by
    rw [hA, Int.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Int.cast_mul, Int.cast_natCast]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (hFpos n hn).ne'
    rw [Nat.cast_div (Finset.dvd_prod_of_mem _ hn) hn0, hQ]
    field_simp
  have hkey : b * (Q : ℤ) = p * L * A := by
    have : (b : ℝ) * (Q : ℝ) = p * L * A := by rw [hbpR, hAR]; ring
    exact_mod_cast this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hdvdb : (p : ℤ) ∣ b * (Q : ℤ) := ⟨L * A, by rw [hkey]; ring⟩
  rcases hpZ.dvd_or_dvd hdvdb with h | h
  · exact hb0 (Int.eq_zero_of_abs_lt_dvd h hbabs)
  · have h' : p ∣ Q := Int.natCast_dvd_natCast.1 h
    rw [hQ] at h'
    obtain ⟨n, hn, hpn⟩ := (Prime.dvd_finset_prod_iff (Nat.prime_iff.1 hp) _).1 h'
    rw [hF, Finset.mem_filter] at hn
    exact hn.2 hpn

/-- Uniqueness of the factorisation `mp` with `p > m`. -/
theorem mul_prime_unique {m m' p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hm : m < p)
    (hm' : m' < p') (h : m * p = m' * p') (hm0 : 0 < m) (hm0' : 0 < m') :
    m = m' ∧ p = p' := by
  by_cases hpp : p = p'
  · subst hpp
    exact ⟨Nat.eq_of_mul_eq_mul_right hp.pos h, rfl⟩
  · exfalso
    have h1 : p ∣ m' * p' := ⟨m, by rw [← h]; ring⟩
    have h1' : p ∣ m' := by
      rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · exact h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hp').1 h2) hpp
    have h2 : p' ∣ m * p := ⟨m', by rw [h]; ring⟩
    have h2' : p' ∣ m := by
      rcases (Nat.Prime.dvd_mul hp').1 h2 with h3 | h3
      · exact h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp' hp).1 h3).symm hpp
    have := Nat.le_of_dvd hm0' h1'
    have := Nat.le_of_dvd hm0 h2'
    omega

/-- Every prime belongs to `𝒰`. -/
theorem InU_prime {p : ℕ} (hp : p.Prime) : InU p := by
  have h := InU_mul_prime one_InU (L := 1) one_pos (fun j hj => by
    rw [Finset.mem_Icc] at hj; rw [show j = 1 by omega]) hp (by
      simp only [Nat.cast_one, one_mul, Finset.Icc_self, Finset.sum_singleton, div_one]
      exact_mod_cast hp.one_lt)
  rwa [one_mul] at h

/-- The primes up to `x` lie in `𝒰 ∩ [1, x]`, so `W(x) ≥ ∑_{p ≤ x} 1/p`. -/
lemma primeRecipSum_le_Wsum (x : ℝ) : primeRecipSum x ≤ Wsum x := by
  unfold primeRecipSum Wsum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [mem_primesLE] at hp
    rw [mem_Uset]
    exact ⟨⟨hp.1.one_le, hp.2⟩, InU_prime hp.1⟩
  · intro _ _ _; positivity

/-- `𝒰 ∩ [1, N]` is reciprocally dissociated. -/
theorem recipDissociated_Uset (x : ℝ) : RecipDissociated (Uset x) := by
  classical
  rw [recipDissociated_iff_signed]
  intro ε hε hsum
  by_contra hne
  push_neg at hne
  set T := (Uset x).filter (fun n => ε n ≠ 0) with hT
  have hTne : T.Nonempty := by
    obtain ⟨n, hn, hεn⟩ := hne
    exact ⟨n, Finset.mem_filter.2 ⟨hn, hεn⟩⟩
  set r := T.max' hTne with hr
  have hrT : r ∈ T := Finset.max'_mem T hTne
  rw [hT, Finset.mem_filter] at hrT
  have hrU := (mem_Uset.1 hrT.1).2
  have hr1 := hrU.1
  have hbig : ∀ n ∈ Uset x, r < n → ε n = 0 := by
    intro n hn hrn
    by_contra h
    have : n ≤ r := Finset.le_max' T n (Finset.mem_filter.2 ⟨hn, h⟩)
    omega
  -- decompose the relation
  have hdecomp : ∑ n ∈ Uset x, (ε n : ℚ) / n =
      ∑ n ∈ (Uset x).filter (· < r), (ε n : ℚ) / n + (ε r : ℚ) / r := by
    rw [← Finset.sum_filter_add_sum_filter_not (Uset x) (· < r)]
    congr 1
    have : (Uset x).filter (fun n => ¬ n < r) =
        {r} ∪ ((Uset x).filter (fun n => r < n)) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hn, hnr⟩
        rcases eq_or_lt_of_le (not_lt.1 hnr) with h | h
        · left; exact h.symm
        · right; exact ⟨hn, h⟩
      · rintro (rfl | ⟨hn, h⟩)
        · exact ⟨hrT.1, lt_irrefl _⟩
        · exact ⟨hn, not_lt.2 h.le⟩
    rw [this, Finset.sum_union (by simp), Finset.sum_singleton]
    rw [Finset.sum_eq_zero (fun n hn => by
      rw [Finset.mem_filter] at hn
      rw [hbig n hn.1 hn.2]; simp)]
    ring
  rw [hdecomp] at hsum
  -- build a forbidden relation for r
  set δ : ℕ → ℤ := fun j => if j ∈ Uset x ∧ j < r then -ε r * ε j else 0 with hδ
  have hδval : ∀ j, δ j = -1 ∨ δ j = 0 ∨ δ j = 1 := by
    intro j
    simp only [hδ]
    split_ifs
    · rcases hε r with h1 | h1 | h1 <;> rcases hε j with h2 | h2 | h2 <;> simp [h1, h2]
    · simp
  apply hrU.2 δ hδval
  have hεr2 : (ε r : ℚ) * ε r = 1 := by
    rcases hε r with h | h | h
    · rw [h]; norm_num
    · exact absurd h hrT.2
    · rw [h]; norm_num
  have hsumδ : ∑ j ∈ Ico 1 r, (δ j : ℚ) / j =
      -(ε r : ℚ) * ∑ n ∈ (Uset x).filter (· < r), (ε n : ℚ) / n := by
    rw [Finset.mul_sum]
    have : (Uset x).filter (· < r) = (Ico 1 r).filter (fun j => j ∈ Uset x ∧ j < r) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨hj, hjr⟩
        exact ⟨⟨(mem_Uset.1 hj).1.1, hjr⟩, hj, hjr⟩
      · rintro ⟨_, hj, hjr⟩
        exact ⟨hj, hjr⟩
    rw [this, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hδ]
    split_ifs
    · push_cast; ring
    · simp
  rw [hsumδ]
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have : ∑ n ∈ (Uset x).filter (· < r), (ε n : ℚ) / n = -((ε r : ℚ) / r) := by linarith
  rw [this]
  field_simp
  linarith [hεr2]

/-- `u(N) ≤ R(N)`. -/
theorem uCount_le_R (N : ℕ) : uCount N ≤ R N := by
  apply le_R _ (recipDissociated_Uset N)
  intro m hm
  rw [mem_Uset, Nat.floor_natCast] at hm
  exact Finset.mem_Icc.2 hm.1

/-! ## The upper bound: the functions `F`, `M` and a weighted prime sum -/

/-- `F(N) = (log N / N) log S(N)`. -/
def Fval (N : ℕ) : ℝ := Real.log N / N * Real.log (S N)

/-- `M(x) = max({1} ∪ {F(n) : 3 ≤ n ≤ x})`. -/
def Mval (x : ℝ) : ℝ := (Icc 3 ⌊x⌋₊).fold max 1 Fval

lemma one_le_Mval (x : ℝ) : 1 ≤ Mval x := by
  unfold Mval; rw [Finset.le_fold_max]; left; exact le_rfl

lemma Fval_le_Mval {n : ℕ} {x : ℝ} (hn : 3 ≤ n) (hnx : (n : ℝ) ≤ x) : Fval n ≤ Mval x := by
  unfold Mval; rw [Finset.le_fold_max]; right
  refine ⟨n, Finset.mem_Icc.2 ⟨hn, Nat.le_floor hnx⟩, le_rfl⟩

lemma Mval_mono {x y : ℝ} (h : x ≤ y) : Mval x ≤ Mval y := by
  unfold Mval
  rw [Finset.fold_max_le]
  refine ⟨one_le_Mval y, fun n hn => ?_⟩
  rw [Finset.mem_Icc] at hn
  refine Fval_le_Mval hn.1 ?_
  have : (n : ℝ) ≤ x := by
    have := Nat.cast_le (α := ℝ).2 hn.2
    refine this.trans (Nat.floor_le ?_)
    by_contra hx
    push_neg at hx
    rw [Nat.floor_of_nonpos hx.le] at hn
    omega
  linarith

lemma log_S_le (n : ℕ) : Real.log (S n) ≤ n * Real.log 2 := by
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast one_le_S n)
  exact_mod_cast S_le_two_pow n

lemma Fval_le (n : ℕ) (hn : 1 ≤ n) : Fval n ≤ Real.log 2 * Real.log n := by
  unfold Fval
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  calc Real.log n / n * Real.log (S n) ≤ Real.log n / n * (n * Real.log 2) :=
        mul_le_mul_of_nonneg_left (log_S_le n) (div_nonneg hl hn0.le)
    _ = Real.log 2 * Real.log n := by field_simp

lemma Mval_le (x : ℝ) (hx : 1 ≤ x) : Mval x ≤ max 1 (Real.log 2 * Real.log x) := by
  unfold Mval
  rw [Finset.fold_max_le]
  refine ⟨le_max_left _ _, fun n hn => ?_⟩
  rw [Finset.mem_Icc] at hn
  have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hn.2).trans (Nat.floor_le (by linarith))
  refine (Fval_le n (by omega)).trans (le_max_of_le_right ?_)
  have : Real.log n ≤ Real.log x := Real.log_le_log (by norm_cast; omega) hnx
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

lemma log_S_eq (N : ℕ) (hN : 2 ≤ N) : Real.log (S N) = N / Real.log N * Fval N := by
  unfold Fval
  have hN0 : (0 : ℝ) < N := by norm_cast; omega
  have hl : 0 < Real.log N := Real.log_pos (by norm_cast)
  field_simp

/-- `L² ≤ e^{L/2}` for `L ≥ 48`. -/
lemma sq_le_exp_half {L : ℝ} (hL : 48 ≤ L) : L ^ 2 ≤ Real.exp (L / 2) := by
  have h := Real.pow_div_factorial_le_exp (L / 2) (by linarith) 3
  have : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [this] at h
  have : L ^ 2 ≤ (L / 2) ^ 3 / 6 := by nlinarith
  linarith

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  norm_num at this ⊢; linarith

/-- Weighted prime sum: for `L = log x ≥ 48`,
`L ∑_{x/L < p ≤ x/3} 1/(p log(x/p)) ≤ log log L + K_w`. -/
theorem weighted_prime_sum : ∃ Kw : ℝ, 0 ≤ Kw ∧ ∀ x : ℝ, 0 < x → 48 ≤ Real.log x →
    Real.log x * ∑ p ∈ (Ioc ⌊x / Real.log x⌋₊ ⌊x / 3⌋₊).filter Nat.Prime,
      (1 : ℝ) / (p * Real.log (x / p)) ≤ Real.log (Real.log (Real.log x)) + Kw := by
  obtain ⟨K, hK0, hK⟩ := mertens_first
  refine ⟨Real.log 2 + 4 * K, by positivity, fun x hx hL => ?_⟩
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hl3 := one_lt_log_three
  have hl3' : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)]
  have hlogL : Real.log L ≤ L / 2 := log_le_half hL0
  have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
  set a := x / L with ha
  set b := x / 3 with hb
  have hxL : x = Real.exp L := by rw [hLdef, Real.exp_log hx]
  have hla : Real.log a = L - Real.log L := by
    rw [ha, Real.log_div hx.ne' hL0.ne']
  have hlb : Real.log b = L - Real.log 3 := by
    rw [hb, Real.log_div hx.ne' (by norm_num)]
  have ha1 : 1 ≤ a := by
    rw [ha, le_div_iff₀ hL0, one_mul, hxL]
    linarith [Real.add_one_le_exp L]
  have hab : a ≤ b := by
    rw [ha, hb]
    exact div_le_div_of_nonneg_left hx.le (by norm_num) (by linarith)
  -- bounds on log t for t ∈ [a, b]
  have hlt : ∀ t ∈ Set.Icc a b, L - Real.log L ≤ Real.log t ∧ Real.log t ≤ L - Real.log 3 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact ⟨hla ▸ Real.log_le_log (by linarith) ht.1, hlb ▸ Real.log_le_log ht0 ht.2⟩
  set w : ℝ → ℝ := fun t => (Real.log t * (L - Real.log t))⁻¹ with hw
  set w' : ℝ → ℝ := fun t => -(t⁻¹ * (L - Real.log t) + Real.log t * -t⁻¹) /
    (Real.log t * (L - Real.log t)) ^ 2 with hw'
  set Φ : ℝ → ℝ := fun t => (Real.log (Real.log t) - Real.log (L - Real.log t)) / L with hΦ
  have hpos : ∀ t ∈ Set.Icc a b, 0 < Real.log t ∧ 0 < L - Real.log t ∧ 0 < t := by
    intro t ht
    have := hlt t ht
    exact ⟨by linarith, by linarith, by linarith [ht.1]⟩
  have habel := abel_mertens hK ha1 hab (w := w) (w' := w') (Φ := Φ)
    (fun t ht => by
      obtain ⟨h1, h2, h3⟩ := hpos t ht
      have hd := (Real.hasDerivAt_log h3.ne').mul ((Real.hasDerivAt_log h3.ne').const_sub L)
      exact hd.inv (mul_pos h1 h2).ne')
    (by
      intro t ht
      obtain ⟨h1, h2, h3⟩ := hpos t ht
      apply ContinuousAt.continuousWithinAt
      have hlc : ContinuousAt Real.log t := Real.continuousAt_log h3.ne'
      apply ContinuousAt.div
      · exact (((continuousAt_inv₀ h3.ne').mul (continuousAt_const.sub hlc)).add
          (hlc.mul (continuousAt_inv₀ h3.ne').neg)).neg
      · exact (hlc.mul (continuousAt_const.sub hlc)).pow 2
      · positivity)
    (fun t ht => by
      obtain ⟨h1, h2, h3⟩ := hpos t ht
      have hd1 := (Real.hasDerivAt_log h3.ne').log h1.ne'
      have hd2 := ((Real.hasDerivAt_log h3.ne').const_sub L).log h2.ne'
      have hd := (hd1.sub hd2).div_const L
      convert hd using 1
      simp only [hw]
      field_simp
      ring)
    (Or.inl (fun t ht => by
      obtain ⟨h1, h2, h3⟩ := hpos t ht
      have := hlt t ht
      simp only [hw']
      apply div_nonneg _ (sq_nonneg _)
      have : 0 < t⁻¹ := inv_pos.2 h3
      nlinarith))
  -- simplify
  have hwa : 0 < w a := by
    obtain ⟨h1, h2, _⟩ := hpos a ⟨le_rfl, hab⟩
    simp only [hw]; positivity
  have hwab : w a ≤ w b := by
    obtain ⟨h1, h2, _⟩ := hpos a ⟨le_rfl, hab⟩
    obtain ⟨h1', h2', _⟩ := hpos b ⟨hab, le_rfl⟩
    simp only [hw]
    apply inv_anti₀ (by positivity)
    have hla' := hlt a ⟨le_rfl, hab⟩
    have hlb' := hlt b ⟨hab, le_rfl⟩
    have hmono : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
    nlinarith
  have hwb : w b ≤ 2 / L := by
    simp only [hw]
    rw [hlb, show L - (L - Real.log 3) = Real.log 3 by ring]
    rw [inv_le_comm₀ (by nlinarith) (by positivity), inv_div]
    nlinarith
  have herr : |w a| + |w b| + |w b - w a| = 2 * w b := by
    rw [abs_of_pos hwa, abs_of_pos (lt_of_lt_of_le hwa hwab), abs_of_nonneg (by linarith)]
    ring
  rw [herr] at habel
  have hsum : ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p / p * w p =
      ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / (p * Real.log (x / p)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have hlp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.2.one_lt)).ne'
    simp only [hw]
    rw [Real.log_div hx.ne' hp0.ne', ← hLdef]
    have hpa : a < p := Nat.lt_of_floor_lt hp.1.1
    have hpb : (p : ℝ) ≤ b := (Nat.le_floor_iff (by positivity)).1 hp.1.2
    have := (hpos p ⟨hpa.le, hpb⟩).2.1
    field_simp
  rw [hsum] at habel
  have hΦab : L * (Φ b - Φ a) ≤ Real.log (Real.log L) + Real.log 2 := by
    simp only [hΦ]
    rw [hla, hlb, show L - (L - Real.log 3) = Real.log 3 by ring,
      show L - (L - Real.log L) = Real.log L by ring]
    have e : L * ((Real.log (L - Real.log 3) - Real.log (Real.log 3)) / L -
        (Real.log (L - Real.log L) - Real.log (Real.log L)) / L) =
        Real.log (L - Real.log 3) - Real.log (Real.log 3) - Real.log (L - Real.log L) +
          Real.log (Real.log L) := by field_simp; ring
    rw [e]
    have h1 : Real.log (L - Real.log 3) ≤ Real.log L := Real.log_le_log (by linarith) (by linarith)
    have h2 : 0 ≤ Real.log (Real.log 3) := Real.log_nonneg hl3.le
    have h3 : Real.log (L / 2) ≤ Real.log (L - Real.log L) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div hL0.ne' (by norm_num)] at h3
    linarith
  have := (abs_le.1 habel).2
  have hS : ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / (p * Real.log (x / p)) ≤
      (Φ b - Φ a) + K * (2 * (2 / L)) := by
    have : K * (2 * w b) ≤ K * (2 * (2 / L)) := by gcongr
    linarith
  calc L * ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / (p * Real.log (x / p))
      ≤ L * ((Φ b - Φ a) + K * (2 * (2 / L))) := mul_le_mul_of_nonneg_left hS hL0.le
    _ = L * (Φ b - Φ a) + 4 * K := by field_simp; ring
    _ ≤ Real.log (Real.log L) + (Real.log 2 + 4 * K) := by linarith

/-! ## The upper bound: smooth part and decomposition -/

/-- If every element of `A` divides `D`, then `|E(A)| ≤ D ∑_{n ∈ A} 1/n + 1`. -/
lemma card_recipSubsetSums_le_of_dvd (A : Finset ℕ) (D : ℕ) (hD : 0 < D)
    (hA : ∀ n ∈ A, n ∣ D) (h0 : ∀ n ∈ A, 0 < n) :
    ((recipSubsetSums A).card : ℝ) ≤ D * ∑ n ∈ A, (1 : ℝ) / n + 1 := by
  classical
  set H : ℚ := ∑ n ∈ A, (1 : ℚ) / n with hH
  have hint : ∀ r ∈ recipSubsetSums A, ∃ k : ℕ, r * D = k ∧ r ≤ H := by
    intro r hr
    unfold recipSubsetSums at hr
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hr
    rw [Finset.mem_powerset] at hB
    refine ⟨∑ n ∈ B, D / n, ?_, ?_⟩
    · push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (h0 n (hB hn)).ne'
      rw [Nat.cast_div (hA n (hB hn)) hn0]
      field_simp
    · exact Finset.sum_le_sum_of_subset_of_nonneg hB (fun _ _ _ => by positivity)
  have hmaps : ∀ r ∈ recipSubsetSums A, ⌊r * D⌋₊ ∈ Finset.range (⌊H * D⌋₊ + 1) := by
    intro r hr
    obtain ⟨k, hk, hle⟩ := hint r hr
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hle (by positivity))
  have hinj : Set.InjOn (fun r : ℚ => ⌊r * D⌋₊) (recipSubsetSums A : Set ℚ) := by
    intro r hr s hs hrs
    obtain ⟨k, hk, -⟩ := hint r hr
    obtain ⟨l, hl, -⟩ := hint s hs
    simp only at hrs
    rw [hk, hl, Nat.floor_natCast, Nat.floor_natCast] at hrs
    have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have : r * D = s * D := by rw [hk, hl, hrs]
    exact mul_right_cancel₀ hD' this
  have hcard := Finset.card_le_card_of_injOn (t := Finset.range (⌊H * D⌋₊ + 1)) _
    (fun r hr => Finset.mem_coe.2 (hmaps r hr)) hinj
  rw [Finset.card_range] at hcard
  have hH0 : 0 ≤ H * D := by positivity
  have h1 : (⌊H * D⌋₊ : ℚ) ≤ H * D := Nat.floor_le hH0
  have h3 : ((H * D : ℚ) : ℝ) = D * ∑ n ∈ A, (1 : ℝ) / n := by
    rw [hH]; push_cast; ring
  have : ((recipSubsetSums A).card : ℝ) ≤ (⌊H * D⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
  have h2' : (⌊H * D⌋₊ : ℝ) ≤ D * ∑ n ∈ A, (1 : ℝ) / n := by
    rw [← h3]; exact_mod_cast h1
  linarith

open Classical in
/-- The set of `Q`-smooth integers in `[1, N]`. -/
def smoothPart (N : ℕ) (Q : ℝ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => ∀ p, p.Prime → p ∣ n → (p : ℝ) ≤ Q)

lemma mem_smoothPart {N n : ℕ} {Q : ℝ} :
    n ∈ smoothPart N Q ↔ (1 ≤ n ∧ n ≤ N) ∧ ∀ p, p.Prime → p ∣ n → (p : ℝ) ≤ Q := by
  classical
  unfold smoothPart
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- Real inequalities used in the core estimate, for `L = log N ≥ 48`. -/
lemma core_real_ineqs {N : ℝ} (hN : 0 < N) (hL : 48 ≤ Real.log N) :
    Real.log N * Real.sqrt N ≤ N / Real.log N ∧ Real.log N < Real.sqrt N ∧
      Real.log (Real.log N + 2) ≤ N / Real.log N := by
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by linarith
  have hsq : Real.sqrt N = Real.exp (L / 2) := by
    rw [← Real.sqrt_sq (Real.exp_pos (L / 2)).le, ← Real.exp_nat_mul, hLdef]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * (Real.log N / 2) = Real.log N by push_cast; ring, Real.exp_log hN]
  have h1 := sq_le_exp_half hL
  have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hL0]
    rw [← hsq] at h1
    nlinarith
  · rw [← hsq] at h1
    nlinarith
  · have h2 := log_le_half (show 0 < L + 2 by linarith)
    rw [le_div_iff₀ hL0]
    rw [← hsq] at h1
    have h1' : 1 ≤ Real.sqrt N := by nlinarith
    have hNs : Real.sqrt N ≤ N := by nlinarith
    have : Real.log (L + 2) ≤ L := by linarith
    nlinarith

/-- The smooth part: for `L = log N ≥ 48` and `Q = N / L`,
`log |E(A₀)| ≤ 4 N / L`. -/
theorem log_card_smoothPart_le (N : ℕ) (hL : 48 ≤ Real.log N) :
    Real.log ((recipSubsetSums (smoothPart N (N / Real.log N))).card) ≤
      4 * (N / Real.log N) := by
  set L := Real.log N with hLdef
  set Q := (N : ℝ) / L with hQ
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by
    by_contra h
    push_neg at h
    have : (N : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg N)
    rw [hLdef, this, Real.log_zero] at hL
    linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hN0
  have hQ0 : 0 ≤ Q := by positivity
  obtain ⟨hr1, hr2, hr3⟩ := core_real_ineqs hN0 hL
  set D := ∏ p ∈ primesLE ⌊Q⌋₊, p ^ Nat.log p N with hD
  have hDpos : 0 < D := Finset.prod_pos (fun p hp => pow_pos (mem_primesLE.1 hp).1.pos _)
  -- every smooth number divides D
  have hdvd : ∀ n ∈ smoothPart N Q, n ∣ D := by
    intro n hn
    rw [mem_smoothPart] at hn
    have hn0 : n ≠ 0 := by omega
    rw [← Nat.factorization_prod_pow_eq_self hn0]
    refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset n.primeFactors (primesLE ⌊Q⌋₊)
      (fun p => p ^ Nat.log p N) ?_)
    · apply Finset.prod_dvd_prod_of_dvd
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      apply pow_dvd_pow
      apply Nat.le_log_of_pow_le hp'.one_lt
      exact (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)).trans hn.1.2
    · intro p hp
      rw [mem_primesLE]
      exact ⟨Nat.prime_of_mem_primeFactors hp, Nat.le_floor
        (hn.2 p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))⟩
  have hcard := card_recipSubsetSums_le_of_dvd (smoothPart N Q) D hDpos hdvd
    (fun n hn => by rw [mem_smoothPart] at hn; omega)
  -- the harmonic sum
  have hH : ∑ n ∈ smoothPart N Q, (1 : ℝ) / n ≤ 1 + L := by
    refine le_trans ?_ (harmonic_sum_le_one_add_log N)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => by rw [mem_smoothPart] at hn; exact Finset.mem_Icc.2 hn.1)
      (fun _ _ _ => by positivity)
  have hH0 : 0 ≤ ∑ n ∈ smoothPart N Q, (1 : ℝ) / n := Finset.sum_nonneg (fun _ _ => by positivity)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hDpos
  have hcard2 : ((recipSubsetSums (smoothPart N Q)).card : ℝ) ≤ D * (L + 2) := by
    nlinarith
  have hcpos : (0 : ℝ) < (recipSubsetSums (smoothPart N Q)).card := by
    exact_mod_cast one_le_card_recipSubsetSums _
  have hlog1 : Real.log ((recipSubsetSums (smoothPart N Q)).card) ≤
      Real.log D + Real.log (L + 2) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log hcpos hcard2
  -- bound on log D
  have hlogD : Real.log D ≤ Real.log 4 * Q + L * Real.sqrt N := by
    rw [hD]
    push_cast
    rw [Real.log_prod (fun p hp => by
      have := (mem_primesLE.1 hp).1.pos; positivity)]
    have hterm : ∀ p ∈ primesLE ⌊Q⌋₊, Real.log ((p : ℝ) ^ Nat.log p N) ≤
        Real.log p + (if p * p ≤ N then L else 0) := by
      intro p hp
      have hpp := (mem_primesLE.1 hp).1
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
      have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
      split_ifs with hpN
      · have : Real.log ((p : ℝ) ^ Nat.log p N) ≤ L := by
          rw [hLdef]
          apply Real.log_le_log (by positivity)
          exact_mod_cast Nat.pow_log_le_self p (by omega)
        linarith
      · push_neg at hpN
        have hlt : Nat.log p N < 2 := Nat.log_lt_of_lt_pow (by omega) (by rw [sq]; exact hpN)
        rw [Real.log_pow]
        have : (Nat.log p N : ℝ) ≤ 1 := by exact_mod_cast (show Nat.log p N ≤ 1 by omega)
        nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib]
    have hθ : ∑ p ∈ primesLE ⌊Q⌋₊, Real.log p ≤ Real.log 4 * Q := by
      rw [← theta_eq_sum]
      refine (Chebyshev.theta_le_log4_mul_x (by positivity)).trans ?_
      exact mul_le_mul_of_nonneg_left (Nat.floor_le hQ0) (Real.log_nonneg (by norm_num))
    have hsqrt : ∑ p ∈ primesLE ⌊Q⌋₊, (if p * p ≤ N then L else 0) ≤ L * Real.sqrt N := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_left _ hL0.le
      have hsub : (primesLE ⌊Q⌋₊).filter (fun p => p * p ≤ N) ⊆ Icc 1 (Nat.sqrt N) := by
        intro p hp
        rw [Finset.mem_filter, mem_primesLE] at hp
        rw [Finset.mem_Icc]
        exact ⟨hp.1.1.one_le, Nat.le_sqrt.2 hp.2⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc, Nat.add_sub_cancel] at this
      exact (Nat.cast_le.2 this).trans Real.nat_sqrt_le_real_sqrt
    linarith
  have hl4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    norm_num at this ⊢; linarith
  have : Real.log 4 * Q ≤ 2 * Q := mul_le_mul_of_nonneg_right hl4 hQ0
  linarith

/-- Decomposition: for `L = log N ≥ 48`,
`log S(N) ≤ 4N/L + ∑_{N/L < p ≤ N} log S(⌊N/p⌋)`. -/
theorem log_S_decomposition (N : ℕ) (hL : 48 ≤ Real.log N) :
    Real.log (S N) ≤ 4 * (N / Real.log N) +
      ∑ p ∈ (Ioc ⌊(N : ℝ) / Real.log N⌋₊ N).filter Nat.Prime, Real.log (S (N / p)) := by
  classical
  set L := Real.log N with hLdef
  set Q := (N : ℝ) / L with hQ
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by
    by_contra h
    push_neg at h
    have : (N : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg N)
    rw [hLdef, this, Real.log_zero] at hL
    linarith
  have hQ0 : 0 ≤ Q := by positivity
  obtain ⟨hr1, hr2, hr3⟩ := core_real_ineqs hN0 hL
  -- Q > √N, hence Q² > N
  have hQsq : N < Q * Q := by
    have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    have hQs : Real.sqrt N < Q := by
      rw [hQ, lt_div_iff₀ hL0]
      nlinarith
    nlinarith
  set P := (Ioc ⌊Q⌋₊ N).filter Nat.Prime with hP
  set blk : ℕ → Finset ℕ := fun p => (Icc 1 (N / p)).image (fun j => p * j) with hblk
  have hmemP : ∀ p ∈ P, p.Prime ∧ Q < p ∧ p ≤ N := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.2, (Nat.floor_lt hQ0).1 hp.1.1, hp.1.2⟩
  have hmemblk : ∀ p ∈ P, ∀ m ∈ blk p, p ∣ m ∧ m ≤ N := by
    intro p hp m hm
    simp only [hblk, Finset.mem_image, Finset.mem_Icc] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    exact ⟨dvd_mul_right p j, by
      have := Nat.mul_le_mul_left p hj.2
      exact this.trans (Nat.mul_div_le N p)⟩
  -- covering
  have hcover : Icc 1 N ⊆ smoothPart N Q ∪ P.biUnion blk := by
    intro n hn
    by_cases h : ∀ p, p.Prime → p ∣ n → (p : ℝ) ≤ Q
    · exact Finset.mem_union_left _ (mem_smoothPart.2 ⟨Finset.mem_Icc.1 hn, h⟩)
    · push_neg at h
      obtain ⟨p, hp, hpn, hpQ⟩ := h
      rw [Finset.mem_Icc] at hn
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
      refine ⟨p, ?_, ?_⟩
      · rw [hP, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨(Nat.floor_lt hQ0).2 hpQ, hple.trans hn.2⟩, hp⟩
      · simp only [hblk, Finset.mem_image, Finset.mem_Icc]
        obtain ⟨j, rfl⟩ := hpn
        refine ⟨j, ⟨?_, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos j with h0 | h0
          · subst h0; omega
          · exact h0
        · rw [Nat.le_div_iff_mul_le hp.pos, mul_comm]; exact hn.2
  -- disjointness
  have hpd : (P : Set ℕ).PairwiseDisjoint blk := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro m hmp hmq
    obtain ⟨hp', hpQ, -⟩ := hmemP p hp
    obtain ⟨hq', hqQ, -⟩ := hmemP q hq
    obtain ⟨hdp, hmN⟩ := hmemblk p hp m hmp
    obtain ⟨hdq, -⟩ := hmemblk q hq m hmq
    have hpq' : p * q ∣ m :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp' hq').2 hpq) hdp hdq
    have hm0 : 0 < m := by
      simp only [hblk, Finset.mem_image, Finset.mem_Icc] at hmp
      obtain ⟨j, hj, rfl⟩ := hmp
      exact Nat.mul_pos hp'.pos (by omega)
    have h1 : p * q ≤ N := (Nat.le_of_dvd hm0 hpq').trans hmN
    have h2 : ((p * q : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
    push_cast at h2
    nlinarith
  have hdisj : Disjoint (smoothPart N Q) (P.biUnion blk) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    rw [Finset.mem_biUnion] at hm'
    obtain ⟨p, hp, hmp⟩ := hm'
    obtain ⟨hp', hpQ, -⟩ := hmemP p hp
    obtain ⟨hdp, -⟩ := hmemblk p hp m hmp
    have := (mem_smoothPart.1 hm).2 p hp' hdp
    linarith
  -- combine
  have hS : (S N : ℝ) ≤ (recipSubsetSums (smoothPart N Q)).card * ∏ p ∈ P, (S (N / p) : ℝ) := by
    have h1 : S N ≤ (recipSubsetSums (smoothPart N Q ∪ P.biUnion blk)).card :=
      Finset.card_le_card (recipSubsetSums_mono hcover)
    have h2 := card_recipSubsetSums_union_le hdisj
    have h3 := card_recipSubsetSums_biUnion_le P blk hpd
    have h4 : ∏ i ∈ P, (recipSubsetSums (blk i)).card = ∏ p ∈ P, S (N / p) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact card_recipSubsetSums_multiples p (N / p) (hmemP p hp).1.pos
    rw [h4] at h3
    have : S N ≤ (recipSubsetSums (smoothPart N Q)).card * ∏ p ∈ P, S (N / p) :=
      h1.trans (h2.trans (Nat.mul_le_mul_left _ h3))
    exact_mod_cast this
  have hSpos : ∀ p ∈ P, (0 : ℝ) < S (N / p) := fun p _ => by exact_mod_cast one_le_S _
  have hcpos : (0 : ℝ) < (recipSubsetSums (smoothPart N Q)).card := by
    exact_mod_cast one_le_card_recipSubsetSums _
  have hlog := Real.log_le_log (by exact_mod_cast one_le_S N) hS
  rw [Real.log_mul hcpos.ne' (Finset.prod_pos hSpos).ne',
    Real.log_prod (fun p hp => (hSpos p hp).ne')] at hlog
  have := log_card_smoothPart_le N hL
  linarith

/-! ## The upper estimate -/

lemma iterLog_three (x : ℝ) : iterLog 3 x = Real.log (Real.log (Real.log x)) := rfl

/-- `s / log s ≤ t / log t` for `e ≤ s ≤ t` (here: `3 ≤ s`). -/
lemma div_log_mono {s t : ℝ} (hs : 3 ≤ s) (hst : s ≤ t) : s / Real.log s ≤ t / Real.log t := by
  have hs0 : 0 < s := by linarith
  have hls : 1 < Real.log s := lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hs)
  have hlt : 1 < Real.log t := lt_of_lt_of_le hls (Real.log_le_log hs0 hst)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : Real.log t - Real.log s ≤ t / s - 1 := by
    rw [← Real.log_div (by linarith) hs0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) hs0)
  have h2 : s * (Real.log t - Real.log s) ≤ t - s := by
    have := mul_le_mul_of_nonneg_left h1 hs0.le
    have e : s * (t / s - 1) = t - s := by field_simp
    linarith
  nlinarith

/-- The recursion for `F`. -/
theorem Fval_recursion : ∃ K : ℝ, 0 ≤ K ∧ ∃ L₀ : ℝ, 48 ≤ L₀ ∧ ∀ N : ℕ, L₀ ≤ Real.log N →
    Fval N ≤ K + (iterLog 3 N + K) * Mval (Real.log N) := by
  obtain ⟨Kw, hKw0, hKw⟩ := weighted_prime_sum
  obtain ⟨X, hX2, hX⟩ := primeCounting_le_eventually
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨4 + 2 * Real.log 4 + Kw, by positivity, max 48 (Real.log X), le_max_left _ _,
    fun N hN => ?_⟩
  set L := Real.log N with hLdef
  have hL48 : 48 ≤ L := le_trans (le_max_left _ _) hN
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by
    by_contra h
    push_neg at h
    have : (N : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg N)
    rw [hLdef, this, Real.log_zero] at hL48
    linarith
  have hNX : X ≤ N := by
    have := le_trans (le_max_right _ _) hN
    rw [hLdef] at this
    calc X = Real.exp (Real.log X) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (Real.log N) := Real.exp_le_exp.2 this
      _ = N := Real.exp_log hN0
  have hdec := log_S_decomposition N hL48
  have hM1 := one_le_Mval L
  -- split the prime sum at N/3
  have hfl1 : ⌊(N : ℝ) / L⌋₊ ≤ ⌊(N : ℝ) / 3⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_left hN0.le (by norm_num) (by linarith))
  have hfl2 : ⌊(N : ℝ) / 3⌋₊ ≤ N := by
    apply Nat.floor_le_of_le
    linarith
  have hsplit : ∑ p ∈ (Ioc ⌊(N : ℝ) / L⌋₊ N).filter Nat.Prime, Real.log (S (N / p)) =
      ∑ p ∈ (Ioc ⌊(N : ℝ) / L⌋₊ ⌊(N : ℝ) / 3⌋₊).filter Nat.Prime, Real.log (S (N / p)) +
      ∑ p ∈ (Ioc ⌊(N : ℝ) / 3⌋₊ N).filter Nat.Prime, Real.log (S (N / p)) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      Finset.sum_Ioc_consecutive _ hfl1 hfl2]
  -- large primes
  have hbig : ∑ p ∈ (Ioc ⌊(N : ℝ) / 3⌋₊ N).filter Nat.Prime, Real.log (S (N / p)) ≤
      2 * (N / L) * Real.log 4 := by
    have h1 : ∀ p ∈ (Ioc ⌊(N : ℝ) / 3⌋₊ N).filter Nat.Prime, Real.log (S (N / p)) ≤
        Real.log 4 := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      have hp3 : (N : ℝ) / 3 < p := (Nat.floor_lt (by positivity)).1 hp.1.1
      have hNp : N / p ≤ 2 := by
        have : N < 3 * p := by
          have : (N : ℝ) < 3 * p := by linarith
          exact_mod_cast this
        have := Nat.div_lt_of_lt_mul (show N < p * 3 by linarith)
        omega
      refine (log_S_le _).trans ?_
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have : ((N / p : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hNp
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      push_cast
      nlinarith
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Ioc ⌊(N : ℝ) / 3⌋₊ N).filter Nat.Prime).card : ℝ) ≤ 2 * N / L := by
      have hsub : (Ioc ⌊(N : ℝ) / 3⌋₊ N).filter Nat.Prime ⊆ primesLE N := by
        intro p hp
        rw [Finset.mem_filter, Finset.mem_Ioc] at hp
        exact mem_primesLE.2 ⟨hp.2, hp.1.2⟩
      have := hX N hNX
      rw [Nat.floor_natCast, primeCounting_eq_card] at this
      exact (Nat.cast_le.2 (Finset.card_le_card hsub)).trans this
    have : 2 * N / L = 2 * (N / L) := by ring
    rw [this] at hcard
    exact mul_le_mul_of_nonneg_right hcard hl4
  -- middle primes
  have hmid : ∑ p ∈ (Ioc ⌊(N : ℝ) / L⌋₊ ⌊(N : ℝ) / 3⌋₊).filter Nat.Prime, Real.log (S (N / p)) ≤
      Mval L * (N * ∑ p ∈ (Ioc ⌊(N : ℝ) / L⌋₊ ⌊(N : ℝ) / 3⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p * Real.log (N / p))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have hpL : (N : ℝ) / L < p := (Nat.floor_lt (by positivity)).1 hp.1.1
    have hp3 : (p : ℝ) ≤ N / 3 := (Nat.le_floor_iff (by positivity)).1 hp.1.2
    set m := N / p with hm
    have hm3 : 3 ≤ m := by
      rw [hm, Nat.le_div_iff_mul_le hp.2.pos]
      have : (3 * p : ℝ) ≤ N := by linarith
      have : 3 * p ≤ N := by exact_mod_cast this
      linarith
    have hmNp : (m : ℝ) ≤ N / p := Nat.cast_div_le
    have hNpL : (N : ℝ) / p < L := by
      rw [div_lt_iff₀ hp0]
      rw [div_lt_iff₀ hL0] at hpL
      linarith
    have hm3' : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hlm : 0 < Real.log m := Real.log_pos (by linarith)
    have hF : Fval m ≤ Mval L := Fval_le_Mval hm3 (by linarith)
    rw [log_S_eq m (by omega)]
    have hdl := div_log_mono hm3' hmNp
    have hpos : 0 ≤ (m : ℝ) / Real.log m := div_nonneg (by linarith) hlm.le
    calc (m : ℝ) / Real.log m * Fval m ≤ (m : ℝ) / Real.log m * Mval L :=
          mul_le_mul_of_nonneg_left hF hpos
      _ ≤ (N / p) / Real.log (N / p) * Mval L :=
          mul_le_mul_of_nonneg_right hdl (by linarith)
      _ = Mval L * (N * (1 / (p * Real.log (N / p)))) := by
          field_simp
  have hw := hKw N hN0 hL48
  rw [← hLdef] at hw
  -- assemble
  unfold Fval
  rw [← hLdef]
  have hS : Real.log (S N) ≤ 4 * (N / L) + Mval L *
      (N * ∑ p ∈ (Ioc ⌊(N : ℝ) / L⌋₊ ⌊(N : ℝ) / 3⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p * Real.log (N / p))) + 2 * (N / L) * Real.log 4 := by
    rw [hsplit] at hdec; linarith
  have hfac : 0 ≤ L / N := by positivity
  calc L / N * Real.log (S N)
      ≤ L / N * (4 * (N / L) + Mval L *
          (N * ∑ p ∈ (Ioc ⌊(N : ℝ) / L⌋₊ ⌊(N : ℝ) / 3⌋₊).filter Nat.Prime,
            (1 : ℝ) / (p * Real.log (N / p))) + 2 * (N / L) * Real.log 4) :=
        mul_le_mul_of_nonneg_left hS hfac
    _ = 4 + 2 * Real.log 4 + Mval L * (L *
          ∑ p ∈ (Ioc ⌊(N : ℝ) / L⌋₊ ⌊(N : ℝ) / 3⌋₊).filter Nat.Prime,
            (1 : ℝ) / (p * Real.log (N / p))) := by
        field_simp
        ring
    _ ≤ 4 + 2 * Real.log 4 + Mval L * (iterLog 3 N + Kw) := by
        rw [iterLog_three, ← hLdef]
        gcongr
    _ ≤ 4 + 2 * Real.log 4 + Kw + (iterLog 3 N + (4 + 2 * Real.log 4 + Kw)) * Mval L := by
        nlinarith

/-- The recursion for `M`. -/
theorem Mval_recursion : ∃ K : ℝ, 1 ≤ K ∧ ∃ X₀ : ℝ, Real.exp 48 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    Mval x ≤ (iterLog 3 x + K) * Mval (Real.log x) := by
  obtain ⟨K, hK0, L₀, hL₀, hrec⟩ := Fval_recursion
  refine ⟨2 * K + L₀, by linarith, Real.exp L₀, Real.exp_le_exp.2 hL₀, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlx : L₀ ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hx
  have h48 : 48 ≤ Real.log x := le_trans hL₀ hlx
  have hl1 : 0 < Real.log (Real.log x) := Real.log_pos (by linarith)
  have hl2 : 0 < iterLog 3 x := by
    rw [iterLog_three]
    apply Real.log_pos
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    calc Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
      _ ≤ 48 := by norm_num
      _ ≤ Real.log x := h48
  have hM1 := one_le_Mval (Real.log x)
  refine (Finset.fold_max_le _).2 ⟨by nlinarith, fun n hn => ?_⟩
  rw [Finset.mem_Icc] at hn
  have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hn.2).trans (Nat.floor_le hx0.le)
  have hn0 : (0 : ℝ) < n := by norm_cast; omega
  by_cases hnL : L₀ ≤ Real.log n
  · have h := hrec n hnL
    have hn48 : 48 ≤ Real.log n := le_trans hL₀ hnL
    have hll : Real.log n ≤ Real.log x := Real.log_le_log hn0 hnx
    have hlln0 : 0 < Real.log (Real.log n) := Real.log_pos (by linarith)
    have hlll : iterLog 3 n ≤ iterLog 3 x := by
      rw [iterLog_three, iterLog_three]
      apply Real.log_le_log hlln0
      exact Real.log_le_log (by linarith) hll
    have hl3n : 0 < iterLog 3 n := by
      rw [iterLog_three]
      apply Real.log_pos
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      calc Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
        _ ≤ 48 := by norm_num
        _ ≤ Real.log n := hn48
    have hMm : Mval (Real.log n) ≤ Mval (Real.log x) := Mval_mono hll
    have hM1' := one_le_Mval (Real.log n)
    calc Fval n ≤ K + (iterLog 3 n + K) * Mval (Real.log n) := h
      _ ≤ K + (iterLog 3 x + K) * Mval (Real.log x) := by gcongr
      _ ≤ (iterLog 3 x + (2 * K + L₀)) * Mval (Real.log x) := by nlinarith
  · push_neg at hnL
    have h := Fval_le n (by omega)
    have hl2' : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
    have hln : 0 ≤ Real.log n := Real.log_nonneg (by norm_cast; omega)
    have : Fval n ≤ L₀ := by nlinarith
    nlinarith

/-- Iterating the recursion for `M`. -/
theorem Mval_le_stopProd : ∃ A : ℝ, 2 ≤ A ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, towerThreshold A ≤ x →
    Mval x ≤ C * stopProd A x := by
  obtain ⟨K, hK1, X₀, hX₀, hrec⟩ := Mval_recursion
  set A := max 2 X₀ with hA
  have hA2 : 2 ≤ A := le_max_left _ _
  have hA0 : 0 < A := by linarith
  have hTA : X₀ ≤ towerThreshold A := by
    unfold towerThreshold
    exact (le_max_right 2 X₀).trans ((le_exp_self _).trans ((le_exp_self _).trans
      (Real.exp_le_exp.2 (le_exp_self _))))
  refine ⟨A, hA2, Real.exp (Real.exp A) * Real.exp (2 * K / A), by positivity,
    fun x hx => ?_⟩
  set k := stopIndex A x with hk
  have hk3 := stopIndex_three_le hA0 hx
  have hstep : ∀ i, i + 2 ≤ k → Mval x ≤ Mval (iterLog i x) *
      ∏ j ∈ Icc 3 (i + 2), (iterLog j x + K) := by
    intro i
    induction i with
    | zero => intro _; simp [iterLog_zero]
    | succ i ih =>
      intro hi
      have h := ih (by omega)
      have hthr := stopIndex_ge_threshold hA0 hx i (by omega)
      have hr := hrec (iterLog i x) (hTA.trans hthr)
      rw [← iterLog_add, ← iterLog_succ, show 3 + i = i + 1 + 2 by ring] at hr
      have hprod0 : 0 ≤ ∏ j ∈ Icc 3 (i + 2), (iterLog j x + K) :=
        Finset.prod_nonneg (fun j hj => by
          have := stopIndex_pos hA0 hx j (by rw [Finset.mem_Icc] at hj; omega)
          linarith)
      rw [show i + 1 + 2 = (i + 2) + 1 by ring, Finset.prod_Icc_succ_top (by omega)]
      calc Mval x ≤ Mval (iterLog i x) * ∏ j ∈ Icc 3 (i + 2), (iterLog j x + K) := h
        _ ≤ ((iterLog (i + 2 + 1) x + K) * Mval (iterLog (i + 1) x)) *
            ∏ j ∈ Icc 3 (i + 2), (iterLog j x + K) := by
          apply mul_le_mul_of_nonneg_right _ hprod0
          rw [show i + 2 + 1 = i + 1 + 2 by ring]; exact hr
        _ = Mval (iterLog (i + 1) x) * ((∏ j ∈ Icc 3 (i + 2), (iterLog j x + K)) *
            (iterLog (i + 2 + 1) x + K)) := by ring
  have hmain := hstep (k - 2) (by omega)
  rw [show k - 2 + 2 = k by omega] at hmain
  -- bound on the starting value
  have hstart : Mval (iterLog (k - 2) x) ≤ Real.exp (Real.exp A) := by
    have hpos := stopIndex_pos hA0 hx (k - 2) (by omega)
    have hge := stopIndex_ge hA0 hx (k - 2) (by omega)
    refine (Mval_le _ (by linarith)).trans (max_le ?_ ?_)
    · exact Real.one_le_exp (Real.exp_pos A).le
    · have h1 : Real.log (iterLog (k - 2) x) = iterLog (k - 1) x := by
        rw [← iterLog_succ, show k - 2 + 1 = k - 1 by omega]
      rw [h1]
      have h2 := stopIndex_prev_lt hA0 hx
      have h3 := stopIndex_pos hA0 hx (k - 1) (by omega)
      have hl2' : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith
  have hprod := stopIndex_prod_add_le hA2 hx (show 0 ≤ K by linarith)
  have hprod0 : 0 ≤ ∏ j ∈ Icc 3 k, (iterLog j x + K) :=
    Finset.prod_nonneg (fun j hj => by
      have := stopIndex_pos hA0 hx j (by rw [Finset.mem_Icc] at hj; omega)
      linarith)
  have hP0 := stopProd_nonneg hA0 hx
  calc Mval x ≤ Mval (iterLog (k - 2) x) * ∏ j ∈ Icc 3 k, (iterLog j x + K) := hmain
    _ ≤ Real.exp (Real.exp A) * (stopProd A x * Real.exp (2 * K / A)) :=
        mul_le_mul hstart hprod hprod0 (by positivity)
    _ = Real.exp (Real.exp A) * Real.exp (2 * K / A) * stopProd A x := by ring

/-- **The upper estimate**: `log S(N) ≪ G(N)`. -/
theorem log_S_le_G : ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, Real.log (S N) ≤ C * G N := by
  obtain ⟨A, hA2, C, hC, hM⟩ := Mval_le_stopProd
  refine ⟨C, hC, ⌈towerThreshold A⌉₊, fun N hN => ?_⟩
  have hNT : towerThreshold A ≤ N := (Nat.ceil_le.1 hN)
  have hT3 : (3 : ℝ) ≤ towerThreshold A := by
    unfold towerThreshold
    have : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp 2; nlinarith [Real.add_one_le_exp (1 : ℝ),
        Real.exp_one_gt_d9, show Real.exp 2 = Real.exp 1 * Real.exp 1 by
          rw [← Real.exp_add]; norm_num]
    calc (3 : ℝ) ≤ Real.exp 2 := this
      _ ≤ Real.exp A := Real.exp_le_exp.2 hA2
      _ ≤ Real.exp (Real.exp A) := le_exp_self _
      _ ≤ Real.exp (Real.exp (Real.exp A)) := le_exp_self _
  have hN3' : (3 : ℝ) ≤ N := hT3.trans hNT
  have hN3 : 3 ≤ N := by exact_mod_cast hN3'
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  rw [log_S_eq N (by omega)]
  have hF : Fval N ≤ C * stopProd A N := (Fval_le_Mval hN3 le_rfl).trans (hM N hNT)
  have hcmp := (stopProd_threshold_comparison (le_refl 2) hA2 hNT).1
  have hfac : 0 ≤ (N : ℝ) / Real.log N := by positivity
  unfold G
  calc (N : ℝ) / Real.log N * Fval N ≤ N / Real.log N * (C * stopProd A N) :=
        mul_le_mul_of_nonneg_left hF hfac
    _ ≤ N / Real.log N * (C * stopProd 2 N) := by gcongr
    _ = C * (N / Real.log N * stopProd 2 N) := by ring

/-! ## The lower bound: recurrences for `W` and `u` -/

/-- The hypothesis on a constant `C` providing common multiples `L_m` of `1, …, m`
with `L_m H_m ≤ e^{Cm}`. -/
def CommonMultipleBound (C : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ L : ℕ, 0 < L ∧ (∀ j ∈ Icc 1 m, j ∣ L) ∧
    (L : ℝ) * ∑ j ∈ Icc 1 m, (1 : ℝ) / j ≤ Real.exp (C * m)

/-- Amplification: if `m ∈ 𝒰` and `p > e^{Cm}` is prime then `mp ∈ 𝒰`. -/
theorem InU_mul_prime_of_bound {C : ℝ} (hC : CommonMultipleBound C) {m p : ℕ} (hm : InU m)
    (hp : p.Prime) (hmp : Real.exp (C * m) < p) : InU (m * p) := by
  obtain ⟨L, hL0, hdvd, hLb⟩ := hC m hm.1
  exact InU_mul_prime hm hL0 hdvd hp (lt_of_le_of_lt hLb hmp)

/-- The pairs `(m, p)` with `m ∈ 𝒰 ∩ [1, y]` and `e^{Cm} < p ≤ x/m` prime. -/
def pairSet (C x y : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (Uset y).sigma (fun m => primesLE ⌊x / m⌋₊ \ primesLE ⌊Real.exp (C * m)⌋₊)

lemma mem_pairSet_prop {C x y : ℝ} {q : Σ _ : ℕ, ℕ} (hq : q ∈ pairSet C x y) :
    q.1 ∈ Uset y ∧ q.2.Prime ∧ Real.exp (C * q.1) < q.2 ∧ (q.2 : ℝ) ≤ x / q.1 := by
  unfold pairSet at hq
  rw [Finset.mem_sigma, Finset.mem_sdiff, mem_primesLE, mem_primesLE] at hq
  obtain ⟨h1, ⟨hp, hpx⟩, hnot⟩ := hq
  refine ⟨h1, hp, ?_, ?_⟩
  · have : ⌊Real.exp (C * q.1)⌋₊ < q.2 := by
      by_contra h; push_neg at h; exact hnot ⟨hp, h⟩
    exact Nat.lt_of_floor_lt this
  · have hm := (mem_Uset.1 h1).1.1
    by_contra h
    push_neg at h
    have hx : 0 ≤ x / q.1 := by
      by_contra hx; push_neg at hx
      rw [Nat.floor_of_nonpos hx.le] at hpx
      have := hp.pos; omega
    exact absurd ((Nat.le_floor_iff hx).1 hpx) (not_le.2 h)

lemma pairSet_injOn {C x y : ℝ} (hC : 1 ≤ C) :
    Set.InjOn (fun q : Σ _ : ℕ, ℕ => q.1 * q.2) (pairSet C x y : Set (Σ _ : ℕ, ℕ)) := by
  intro q hq q' hq' heq
  obtain ⟨h1, hp, hlt, -⟩ := mem_pairSet_prop hq
  obtain ⟨h1', hp', hlt', -⟩ := mem_pairSet_prop hq'
  have hm := (mem_Uset.1 h1).1.1
  have hm' := (mem_Uset.1 h1').1.1
  have hmp : q.1 < q.2 := by
    have : (q.1 : ℝ) < q.2 := by
      have := Real.add_one_le_exp (C * q.1)
      have : (q.1 : ℝ) ≤ C * q.1 := by nlinarith [(Nat.cast_nonneg q.1 : (0 : ℝ) ≤ q.1)]
      linarith
    exact_mod_cast this
  have hmp' : q'.1 < q'.2 := by
    have : (q'.1 : ℝ) < q'.2 := by
      have := Real.add_one_le_exp (C * q'.1)
      have : (q'.1 : ℝ) ≤ C * q'.1 := by nlinarith [(Nat.cast_nonneg q'.1 : (0 : ℝ) ≤ q'.1)]
      linarith
    exact_mod_cast this
  obtain ⟨e1, e2⟩ := mul_prime_unique hp hp' hmp hmp' heq hm hm'
  exact Sigma.ext e1 (heq_of_eq e2)

lemma pairSet_image_subset {C x y : ℝ} (hC : CommonMultipleBound C) :
    (pairSet C x y).image (fun q : Σ _ : ℕ, ℕ => q.1 * q.2) ⊆ Uset x := by
  intro n hn
  rw [Finset.mem_image] at hn
  obtain ⟨q, hq, rfl⟩ := hn
  obtain ⟨h1, hp, hlt, hpx⟩ := mem_pairSet_prop hq
  have hm := (mem_Uset.1 h1).1.1
  have hm0 : (0 : ℝ) < q.1 := by exact_mod_cast hm
  have hx : 0 ≤ x := by
    have : (0 : ℝ) ≤ x / q.1 := le_trans (Nat.cast_nonneg _) hpx
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => by linarith [h.2])
  rw [mem_Uset' hx]
  refine ⟨InU_mul_prime_of_bound hC (mem_Uset.1 h1).2 hp hlt, ?_⟩
  push_cast
  rw [le_div_iff₀ hm0] at hpx
  linarith

/-- `W(x) ≥ ∑_{m ∈ 𝒰, m ≤ y} (1/m) ∑_{e^{Cm} < p ≤ x/m} 1/p`. -/
lemma Wsum_ge_pairs {C x y : ℝ} (hC1 : 1 ≤ C) (hC : CommonMultipleBound C) :
    ∑ m ∈ Uset y, (1 : ℝ) / m *
      ∑ p ∈ primesLE ⌊x / m⌋₊ \ primesLE ⌊Real.exp (C * m)⌋₊, (1 : ℝ) / p ≤ Wsum x := by
  classical
  have h1 : ∑ n ∈ (pairSet C x y).image (fun q : Σ _ : ℕ, ℕ => q.1 * q.2), (1 : ℝ) / n ≤
      Wsum x :=
    Finset.sum_le_sum_of_subset_of_nonneg (pairSet_image_subset hC) (fun _ _ _ => by positivity)
  rw [Finset.sum_image (pairSet_injOn hC1)] at h1
  unfold pairSet at h1
  rw [Finset.sum_sigma] at h1
  refine le_of_eq_of_le ?_ h1
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  push_cast
  field_simp

/-- `u(x) ≥ ∑_{m ∈ 𝒰, m ≤ y} #{e^{Cm} < p ≤ x/m}`. -/
lemma uCount_ge_pairs {C x y : ℝ} (hC1 : 1 ≤ C) (hC : CommonMultipleBound C) :
    ∑ m ∈ Uset y, (primesLE ⌊x / m⌋₊ \ primesLE ⌊Real.exp (C * m)⌋₊).card ≤ uCount x := by
  classical
  have h1 := Finset.card_le_card (pairSet_image_subset (x := x) (y := y) hC)
  rw [Finset.card_image_of_injOn (pairSet_injOn hC1)] at h1
  unfold pairSet at h1
  rw [Finset.card_sigma] at h1
  exact h1

/-- The constant `D = 2 C e^{2C}`. -/
def Dconst (C : ℝ) : ℝ := 2 * C * Real.exp (2 * C)

lemma Dconst_ge {C : ℝ} (hC : 2 ≤ C) : 4 ≤ Dconst C := by
  unfold Dconst
  have : 1 ≤ Real.exp (2 * C) := Real.one_le_exp (by linarith)
  nlinarith

/-- If `x ≥ e^D` and `y = log x / D`, then
`W(x) ≥ ∑_{m ∈ 𝒰, m ≤ y} (1/m) log(y/m)`. -/
theorem Wsum_recurrence {C : ℝ} (hC2 : 2 ≤ C) (hC : CommonMultipleBound C)
    (hmert : ∀ t : ℝ, 2 ≤ t → |primeRecipSum t - Real.log (Real.log t)| ≤ C)
    {x : ℝ} (hx : Real.exp (Dconst C) ≤ x) :
    ∑ m ∈ Uset (Real.log x / Dconst C), (1 : ℝ) / m * Real.log (Real.log x / Dconst C / m) ≤
      Wsum x := by
  set D := Dconst C with hD
  have hD4 := Dconst_ge hC2
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set lx := Real.log x with hlx
  have hlxD : D ≤ lx := by rw [hlx, Real.le_log_iff_exp_le hx0]; exact hx
  have hlx0 : 0 < lx := by linarith
  set y := lx / D with hy
  set s := Real.exp (lx / 2) with hs
  have hss : s * s = x := by rw [hs, ← Real.exp_add, hlx]; ring_nf; exact Real.exp_log hx0
  have hs0 : 0 < s := Real.exp_pos _
  refine le_trans (Finset.sum_le_sum (fun m hm => ?_)) (Wsum_ge_pairs (by linarith) hC)
  have hm1 : 1 ≤ m := (mem_Uset.1 hm).1.1
  have hmy : (m : ℝ) ≤ y := (Nat.le_floor_iff (by positivity)).1 (mem_Uset.1 hm).1.2
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have he2C : 1 ≤ Real.exp (2 * C) := Real.one_le_exp (by linarith)
  -- C m ≤ lx / 2
  have hCm : C * m ≤ lx / 2 := by
    have : C * m ≤ C * y := mul_le_mul_of_nonneg_left hmy (by linarith)
    have hCy : C * y = lx / (2 * Real.exp (2 * C)) := by
      rw [hy, hD, Dconst]; field_simp
    rw [hCy] at this
    have : lx / (2 * Real.exp (2 * C)) ≤ lx / 2 :=
      div_le_div_of_nonneg_left hlx0.le (by norm_num) (by linarith)
    linarith
  have hexpCm : Real.exp (C * m) ≤ s := Real.exp_le_exp.2 hCm
  have hmlx : (m : ℝ) ≤ lx / 2 := by
    have : y ≤ lx / 2 := by
      rw [hy]; exact div_le_div_of_nonneg_left hlx0.le (by norm_num) (by linarith)
    linarith
  have hms : (m : ℝ) ≤ s := hmlx.trans (le_exp_self _)
  have hxm : s ≤ x / m := by
    rw [le_div_iff₀ hm0, ← hss]
    exact mul_le_mul_of_nonneg_left hms hs0.le
  have hexp2 : 2 ≤ Real.exp (C * m) := by
    have : 2 ≤ C * m := by nlinarith
    linarith [Real.add_one_le_exp (C * m)]
  have hsum := sum_primes_Ioc_ge hmert hexp2 (hexpCm.trans hxm)
  refine mul_le_mul_of_nonneg_left (le_trans ?_ hsum) (by positivity)
  -- the real inequality
  rw [Real.log_exp]
  have hlogxm : lx / 2 ≤ Real.log (x / m) := by
    rw [← Real.log_exp (lx / 2)]
    exact Real.log_le_log (Real.exp_pos _) hxm
  have h1 : Real.log (lx / 2) ≤ Real.log (Real.log (x / m)) :=
    Real.log_le_log (by positivity) hlogxm
  rw [Real.log_div hlx0.ne' (by norm_num)] at h1
  have hC0 : 0 < C := by linarith
  have h2 : Real.log (C * m) = Real.log C + Real.log m :=
    Real.log_mul hC0.ne' hm0.ne'
  have h3 : Real.log (y / m) = Real.log lx - Real.log 2 - Real.log C - 2 * C - Real.log m := by
    rw [hy, hD, Dconst, Real.log_div (by positivity) hm0.ne',
      Real.log_div hlx0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) hC0.ne', Real.log_exp]
    ring
  rw [h3]
  linarith

/-- `H(v) = W(e^{v - a})`. -/
def Hf (a v : ℝ) : ℝ := Wsum (Real.exp (v - a))

lemma Hf_nonneg (a v : ℝ) : 0 ≤ Hf a v := Wsum_nonneg _

lemma Hf_mono (a : ℝ) : Monotone (Hf a) := by
  intro v w h
  exact Wsum_mono (Real.exp_le_exp.2 (by linarith))

/-- `∫_0^S 1_{[c, ∞)} = S - c` for `0 ≤ c ≤ S`. -/
lemma integral_indicator_Ici {c S : ℝ} (hc : 0 ≤ c) (hcS : c ≤ S) :
    ∫ v in (0 : ℝ)..S, (if c ≤ v then (1 : ℝ) else 0) = S - c := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun v : ℝ => if c ≤ v then (1 : ℝ) else 0)
      volume a b := by
    intro a b
    apply Monotone.intervalIntegrable
    intro v w hvw
    simp only
    split_ifs with h1 h2 <;> (try push_neg at *) <;> linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 c) (hint c S)]
  have h1 : ∫ v in (0 : ℝ)..c, (if c ≤ v then (1 : ℝ) else 0) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards [(Set.countable_singleton c).ae_notMem volume] with v hv hv'
      rw [Set.uIoc_of_le hc] at hv'
      have : v ≠ c := fun h => hv (by simp [h])
      have : ¬ c ≤ v := fun h => this (le_antisymm hv'.2 h)
      simp [this]
  have h2 : ∫ v in c..S, (if c ≤ v then (1 : ℝ) else 0) = S - c := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (1 : ℝ))]
    · simp
    · filter_upwards with v hv'
      rw [Set.uIoc_of_le hcS] at hv'
      simp [hv'.1.le]
  rw [h1, h2, zero_add]

/-- The identity `∑_{m ∈ 𝒰, m ≤ y} (1/m) log(y/m) = ∫_0^{a + log y} H`. -/
theorem integral_Hf {a y : ℝ} (ha : 0 ≤ a) (hy : 1 ≤ y) :
    ∫ v in (0 : ℝ)..(a + Real.log y), Hf a v =
      ∑ m ∈ Uset y, (1 : ℝ) / m * Real.log (y / m) := by
  have hy0 : 0 < y := by linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hS : 0 ≤ a + Real.log y := by linarith
  have hEq : Set.EqOn (Hf a) (fun v => ∑ m ∈ Uset y, (1 : ℝ) / m *
      (if a + Real.log m ≤ v then (1 : ℝ) else 0)) (Set.uIcc 0 (a + Real.log y)) := by
    intro v hv
    rw [Set.uIcc_of_le hS] at hv
    simp only [Hf, Wsum]
    have hsub : Uset (Real.exp (v - a)) =
        (Uset y).filter (fun m : ℕ => a + Real.log (m : ℝ) ≤ v) := by
      ext m
      rw [Finset.mem_filter, mem_Uset' (Real.exp_pos _).le]
      constructor
      · rintro ⟨hm, hmv⟩
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
        have hlog : Real.log m ≤ v - a := by
          rw [← Real.log_exp (v - a)]; exact Real.log_le_log hm0 hmv
        refine ⟨(mem_Uset' hy0.le).2 ⟨hm, ?_⟩, by linarith⟩
        refine hmv.trans ?_
        rw [← Real.exp_log hy0]
        exact Real.exp_le_exp.2 (by linarith [hv.2])
      · rintro ⟨hm, hmv⟩
        obtain ⟨hmU, -⟩ := (mem_Uset' hy0.le).1 hm
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hmU.1
        refine ⟨hmU, ?_⟩
        rw [← Real.exp_log hm0]
        exact Real.exp_le_exp.2 (by linarith)
    rw [hsub, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> simp
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Uset.1 hm).1.1
    have hmy : (m : ℝ) ≤ y := (Nat.le_floor_iff hy0.le).1 (mem_Uset.1 hm).1.2
    have hm0 : (0 : ℝ) < m := by linarith
    rw [intervalIntegral.integral_const_mul,
      integral_indicator_Ici (by linarith [Real.log_nonneg hm1])
        (by linarith [Real.log_le_log hm0 hmy]),
      Real.log_div hy0.ne' hm0.ne']
    ring_nf
  · intro m _
    apply IntervalIntegrable.const_mul
    apply Monotone.intervalIntegrable
    intro v w hvw
    simp only
    split_ifs with h1 h2 <;> (try push_neg at *) <;> linarith

/-- `H(z) ≥ ∫_0^{log(z-a)} H` for `z ≥ z₀ = a + D`,
where `a = log D`. -/
theorem Hf_recurrence {C : ℝ} (hC2 : 2 ≤ C) (hC : CommonMultipleBound C)
    (hmert : ∀ t : ℝ, 2 ≤ t → |primeRecipSum t - Real.log (Real.log t)| ≤ C)
    {z : ℝ} (hz : Real.log (Dconst C) + Dconst C ≤ z) :
    ∫ v in (0 : ℝ)..(Real.log (z - Real.log (Dconst C))), Hf (Real.log (Dconst C)) v ≤
      Hf (Real.log (Dconst C)) z := by
  set D := Dconst C with hD
  set a := Real.log D with ha
  have hD4 := Dconst_ge hC2
  have hD0 : 0 < D := by linarith
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
  have hza : D ≤ z - a := by linarith
  have hza0 : 0 < z - a := by linarith
  set x := Real.exp (z - a) with hx
  have hlx : Real.log x = z - a := Real.log_exp _
  have hy1 : 1 ≤ (z - a) / D := by rw [le_div_iff₀ hD0]; linarith
  have hlog : a + Real.log ((z - a) / D) = Real.log (z - a) := by
    rw [Real.log_div hza0.ne' hD0.ne', ha]; ring
  have hrec := Wsum_recurrence hC2 hC hmert (x := x) (Real.exp_le_exp.2 hza)
  rw [hlx] at hrec
  rw [← hlog, integral_Hf ha0 hy1]
  exact hrec

/-- `H(z) ≥ log z - a₁` for `z > 0`, with
`a₁ = z₀ + 2a + 2C + 10`. -/
theorem Hf_ge_log {C : ℝ} (hC2 : 2 ≤ C)
    (hmert : ∀ t : ℝ, 2 ≤ t → |primeRecipSum t - Real.log (Real.log t)| ≤ C)
    {z : ℝ} (hz : 0 < z) :
    Real.log z - (3 * Real.log (Dconst C) + Dconst C + 2 * C + 10) ≤
      Hf (Real.log (Dconst C)) z := by
  set D := Dconst C with hD
  set a := Real.log D with ha
  have hD4 := Dconst_ge hC2
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
  set a₁ := 3 * a + D + 2 * C + 10 with ha₁
  by_cases hlz : Real.log z ≤ a₁
  · have := Hf_nonneg a z; linarith
  push_neg at hlz
  have hz1 : a₁ + 1 ≤ z := by
    have := Real.add_one_le_exp a₁
    have h2 : Real.exp a₁ < z := by rwa [Real.lt_log_iff_exp_lt hz] at hlz
    linarith
  have hza : 1 ≤ z - a := by linarith
  have h2 : 2 ≤ Real.exp (z - a) := by linarith [Real.add_one_le_exp (z - a)]
  have h3 := (abs_le.1 (hmert _ h2)).1
  rw [Real.log_exp] at h3
  have h4 : primeRecipSum (Real.exp (z - a)) ≤ Hf a z := primeRecipSum_le_Wsum _
  have h5 : Real.log (z / 2) ≤ Real.log (z - a) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_div hz.ne' (by norm_num)] at h5
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  linarith

/-- For large `x`, `u(x) ≥ (c/2) (x / log x) W(log x / D)`. -/
theorem uCount_ge {C c x₀ : ℝ} (hC2 : 2 ≤ C) (hC : CommonMultipleBound C) (hc : 0 < c)
    (hx₀ : 2 ≤ x₀) (hcheb : ∀ t : ℝ, x₀ ≤ t → c * t / Real.log t ≤ Nat.primeCounting ⌊t⌋₊) :
    ∃ X : ℝ, 1 < X ∧ ∀ x : ℝ, X ≤ x →
      c / 2 * (x / Real.log x) * Wsum (Real.log x / Dconst C) ≤ uCount x := by
  set D := Dconst C with hD
  have hD4 := Dconst_ge hC2
  have hD0 : 0 < D := by linarith
  have hk : 0 < c * D / 2 := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)).bound hk
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1 hlo
  refine ⟨max (max X₁ (Real.exp D)) (max (x₀ ^ 2) 2), lt_of_lt_of_le (by norm_num)
    (le_max_of_le_right (le_max_right _ _)), fun x hx => ?_⟩
  have hxX₁ : X₁ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hxD : Real.exp D ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hxx₀ : x₀ ^ 2 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxD
  set lx := Real.log x with hlx
  have hlxD : D ≤ lx := by rw [hlx, Real.le_log_iff_exp_le hx0]; exact hxD
  have hlx0 : 0 < lx := by linarith
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hsx₀ : x₀ ≤ s := by
    rw [hs]; exact Real.le_sqrt_of_sq_le hxx₀
  -- the key real inequality (log x)^2 ≤ (cD/2) √x
  have hkey : lx ^ 2 ≤ c * D / 2 * s := by
    have := hX₁ x hxX₁
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _),
      abs_of_nonneg (Real.rpow_nonneg hlx0.le _), ← Real.sqrt_eq_rpow] at this
    rw [show lx ^ 2 = lx ^ (2 : ℝ) by norm_cast]
    exact this
  set y := lx / D with hy
  refine le_trans ?_ (Nat.cast_le.2 (uCount_ge_pairs (x := x) (y := y) (by linarith) hC))
  push_cast
  unfold Wsum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hm1 : 1 ≤ m := (mem_Uset.1 hm).1.1
  have hmy : (m : ℝ) ≤ y := (Nat.le_floor_iff (by positivity)).1 (mem_Uset.1 hm).1.2
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have he2C : 1 ≤ Real.exp (2 * C) := Real.one_le_exp (by linarith)
  -- as in the W recurrence
  have hCm : C * m ≤ lx / 2 := by
    have : C * m ≤ C * y := mul_le_mul_of_nonneg_left hmy (by linarith)
    have hCy : C * y = lx / (2 * Real.exp (2 * C)) := by
      rw [hy, hD, Dconst]; field_simp
    rw [hCy] at this
    have : lx / (2 * Real.exp (2 * C)) ≤ lx / 2 :=
      div_le_div_of_nonneg_left hlx0.le (by norm_num) (by linarith)
    linarith
  have hsexp : s = Real.exp (lx / 2) := by
    rw [hs, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, hlx]; ring_nf
  have hexpCm : Real.exp (C * m) ≤ s := by rw [hsexp]; exact Real.exp_le_exp.2 hCm
  have hmlx : (m : ℝ) ≤ lx / 2 := by
    have : y ≤ lx / 2 := by
      rw [hy]; exact div_le_div_of_nonneg_left hlx0.le (by norm_num) (by linarith)
    linarith
  have hms : (m : ℝ) ≤ s := by rw [hsexp]; exact hmlx.trans (le_exp_self _)
  have hxm : s ≤ x / m := by
    rw [le_div_iff₀ hm0, ← hss]
    exact mul_le_mul_of_nonneg_left hms hs0.le
  -- counting
  have hsub : primesLE ⌊Real.exp (C * m)⌋₊ ⊆ primesLE ⌊x / m⌋₊ :=
    primesLE_mono (Nat.floor_le_floor (hexpCm.trans hxm))
  rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub),
    ← primeCounting_eq_card, ← primeCounting_eq_card]
  have h1 := hcheb (x / m) (hsx₀.trans hxm)
  have h2 : (Nat.primeCounting ⌊Real.exp (C * m)⌋₊ : ℝ) ≤ s := by
    rw [primeCounting_eq_card]
    have : (primesLE ⌊Real.exp (C * m)⌋₊).card ≤ ⌊Real.exp (C * m)⌋₊ := by
      have := Finset.card_filter_le (Ioc 0 ⌊Real.exp (C * m)⌋₊) Nat.Prime
      simpa [Nat.card_Ioc] using this
    exact (Nat.cast_le.2 this).trans ((Nat.floor_le (Real.exp_pos _).le).trans hexpCm)
  have hlxm0 : 0 < Real.log (x / m) := by
    apply Real.log_pos
    have : 1 < s := by linarith
    linarith
  have hlxm : Real.log (x / m) ≤ lx := Real.log_le_log (by positivity) (div_le_self hx0.le
    (by exact_mod_cast hm1))
  have h3 : c * x / (m * lx) ≤ c * (x / m) / Real.log (x / m) := by
    rw [div_le_div_iff₀ (by positivity) hlxm0]
    have : c * x * Real.log (x / m) ≤ c * x * lx := mul_le_mul_of_nonneg_left hlxm (by positivity)
    have e : c * (x / m) * (m * lx) = c * x * lx := by field_simp
    rw [e]; exact this
  have h4 : s ≤ c / 2 * x / (m * lx) := by
    rw [le_div_iff₀ (by positivity)]
    have hmlxD : (m : ℝ) * lx ≤ lx ^ 2 / D := by
      rw [le_div_iff₀ hD0]
      have hmD : (m : ℝ) * D ≤ lx := by rw [hy, le_div_iff₀ hD0] at hmy; exact hmy
      calc (m : ℝ) * lx * D = (m * D) * lx := by ring
        _ ≤ lx * lx := mul_le_mul_of_nonneg_right hmD hlx0.le
        _ = lx ^ 2 := by ring
    have h5 : lx ^ 2 / D ≤ c / 2 * s := by
      rw [div_le_iff₀ hD0]
      have : c * D / 2 * s = c / 2 * s * D := by ring
      linarith
    calc s * (m * lx) ≤ s * (lx ^ 2 / D) := mul_le_mul_of_nonneg_left hmlxD hs0.le
      _ ≤ s * (c / 2 * s) := mul_le_mul_of_nonneg_left h5 hs0.le
      _ = c / 2 * x := by rw [← hss]; ring
  have : c / 2 * (x / lx) * (1 / m) = c / 2 * x / (m * lx) := by field_simp
  rw [this]
  have : c * x / (m * lx) = 2 * (c / 2 * x / (m * lx)) := by ring
  linarith

/-! ## Towers and integral estimates -/

/-- The tower `e_0 = 1`, `e_{j+1} = exp(e_j)`. -/
def tower : ℕ → ℝ
  | 0 => 1
  | j + 1 => Real.exp (tower j)

/-- `Q_k(v) = ∏_{j=1}^{k} ℓ_j(v)`, defined recursively by `Q_{k+1}(v) = log v · Q_k(log v)`. -/
def Qf : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, v => Real.log v * Qf k (Real.log v)

/-- `R_k(v) = v Q_k'(v) = ∑_{i=1}^{k} ∏_{j=i+1}^{k} ℓ_j(v)`. -/
def Rf : ℕ → ℝ → ℝ
  | 0, _ => 0
  | k + 1, v => Qf k (Real.log v) + Rf k (Real.log v)

/-- Thresholds: `thr 0 = 0`, `thr (k+1) = exp (thr k)` (so `thr (k+1) = e_k`). -/
def thr : ℕ → ℝ
  | 0 => 0
  | k + 1 => Real.exp (thr k)

lemma tower_succ (j : ℕ) : tower (j + 1) = Real.exp (tower j) := rfl
lemma Qf_succ (k : ℕ) (v : ℝ) : Qf (k + 1) v = Real.log v * Qf k (Real.log v) := rfl
lemma Rf_succ (k : ℕ) (v : ℝ) : Rf (k + 1) v = Qf k (Real.log v) + Rf k (Real.log v) := rfl

lemma one_le_tower (j : ℕ) : 1 ≤ tower j := by
  induction j with
  | zero => simp [tower]
  | succ j ih => rw [tower_succ]; linarith [Real.add_one_le_exp (tower j)]

lemma tower_pos (j : ℕ) : 0 < tower j := by linarith [one_le_tower j]

lemma tower_succ_ge (j : ℕ) : tower j + 1 ≤ tower (j + 1) := by
  rw [tower_succ]; linarith [Real.add_one_le_exp (tower j)]

lemma tower_mono : Monotone tower := by
  apply monotone_nat_of_le_succ
  intro j; linarith [tower_succ_ge j]

lemma two_pow_le_tower (j : ℕ) : (2 : ℝ) ^ j ≤ tower j := by
  induction j with
  | zero => simp [tower]
  | succ j ih =>
    rw [tower_succ, pow_succ]
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ tower j by linarith [one_le_tower j])
    nlinarith [sq_nonneg (tower j - 1)]

lemma thr_succ_eq (k : ℕ) : thr (k + 1) = tower k := by
  induction k with
  | zero => simp [thr, tower]
  | succ k ih => rw [thr, ih, tower_succ]

lemma thr_nonneg (k : ℕ) : 0 ≤ thr k := by
  cases k with
  | zero => simp [thr]
  | succ k => rw [thr_succ_eq]; exact (tower_pos k).le

lemma thr_le_tower (k : ℕ) : thr k ≤ tower k := by
  cases k with
  | zero => simp [thr, tower]
  | succ k => rw [thr_succ_eq]; exact tower_mono (Nat.le_succ k)

/-- `ℓ_j(e_i) = e_{i-j}` for `j ≤ i`. -/
lemma iterLog_tower : ∀ j i, j ≤ i → iterLog j (tower i) = tower (i - j) := by
  intro j
  induction j with
  | zero => intro i _; simp [iterLog_zero]
  | succ j ih =>
    intro i hji
    rw [iterLog_succ, ih i (by omega), show i - j = (i - (j + 1)) + 1 by omega, tower_succ,
      Real.log_exp]

lemma iterLog_tower_self_succ (k : ℕ) : iterLog (k + 1) (tower k) = 0 := by
  rw [iterLog_succ, iterLog_tower k k le_rfl, Nat.sub_self]; simp [tower]

/-- Nonnegativity and monotonicity of `ℓ_j` on `[thr j, ∞)`. -/
lemma iterLog_nonneg_mono : ∀ j : ℕ, (∀ v, thr j ≤ v → 0 ≤ iterLog j v) ∧
    (∀ v w, thr j ≤ v → v ≤ w → iterLog j v ≤ iterLog j w) := by
  intro j
  induction j with
  | zero =>
    refine ⟨fun v hv => ?_, fun v w _ h => h⟩
    simpa [thr, iterLog_zero] using hv
  | succ j ih =>
    have hlog : ∀ v, thr (j + 1) ≤ v → thr j ≤ Real.log v ∧ 0 < v := by
      intro v hv
      rw [thr] at hv
      have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos _) hv
      exact ⟨(Real.le_log_iff_exp_le hv0).2 hv, hv0⟩
    refine ⟨fun v hv => ?_, fun v w hv hvw => ?_⟩
    · rw [iterLog_succ']; exact ih.1 _ (hlog v hv).1
    · rw [iterLog_succ', iterLog_succ']
      obtain ⟨h1, h2⟩ := hlog v hv
      exact ih.2 _ _ h1 (Real.log_le_log h2 hvw)

lemma Qf_eq_prod : ∀ k v, Qf k v = ∏ j ∈ range k, iterLog (j + 1) v := by
  intro k
  induction k with
  | zero => intro v; simp [Qf]
  | succ k ih =>
    intro v
    rw [Qf_succ, ih, Finset.prod_range_succ']
    simp only [iterLog_succ' _ v, zero_add]
    rw [mul_comm]
    rfl

lemma Qf_succ' (k : ℕ) (v : ℝ) : Qf (k + 1) v = Qf k v * iterLog (k + 1) v := by
  rw [Qf_eq_prod, Qf_eq_prod, Finset.prod_range_succ]

/-- `Q_k` and `R_k` are nonnegative and monotone on `[thr k, ∞)`. -/
lemma QR_nonneg_mono : ∀ k : ℕ,
    (∀ v, thr k ≤ v → 0 ≤ Qf k v ∧ 0 ≤ Rf k v) ∧
    (∀ v w, thr k ≤ v → v ≤ w → Qf k v ≤ Qf k w ∧ Rf k v ≤ Rf k w) := by
  intro k
  induction k with
  | zero =>
    exact ⟨fun v _ => ⟨by simp [Qf], by simp [Rf]⟩, fun v w _ _ => ⟨by simp [Qf], by simp [Rf]⟩⟩
  | succ k ih =>
    have hlog : ∀ v, thr (k + 1) ≤ v → thr k ≤ Real.log v ∧ 0 < v := by
      intro v hv
      rw [thr] at hv
      have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos _) hv
      exact ⟨(Real.le_log_iff_exp_le hv0).2 hv, hv0⟩
    refine ⟨fun v hv => ?_, fun v w hv hvw => ?_⟩
    · obtain ⟨h1, h2⟩ := hlog v hv
      obtain ⟨hq, hr⟩ := ih.1 _ h1
      have hl : 0 ≤ Real.log v := (thr_nonneg k).trans h1
      exact ⟨by rw [Qf_succ]; positivity, by rw [Rf_succ]; positivity⟩
    · obtain ⟨h1, h2⟩ := hlog v hv
      have hlw : Real.log v ≤ Real.log w := Real.log_le_log h2 hvw
      obtain ⟨hq, hr⟩ := ih.2 _ _ h1 hlw
      obtain ⟨hq0, hr0⟩ := ih.1 _ h1
      have hl : 0 ≤ Real.log v := (thr_nonneg k).trans h1
      refine ⟨?_, ?_⟩
      · rw [Qf_succ, Qf_succ]
        exact mul_le_mul hlw hq hq0 (hl.trans hlw)
      · rw [Rf_succ, Rf_succ]; linarith

lemma Qf_nonneg {k : ℕ} {v : ℝ} (hv : thr k ≤ v) : 0 ≤ Qf k v := ((QR_nonneg_mono k).1 v hv).1
lemma Rf_nonneg {k : ℕ} {v : ℝ} (hv : thr k ≤ v) : 0 ≤ Rf k v := ((QR_nonneg_mono k).1 v hv).2
lemma Qf_mono {k : ℕ} {v w : ℝ} (hv : thr k ≤ v) (hvw : v ≤ w) : Qf k v ≤ Qf k w :=
  ((QR_nonneg_mono k).2 v w hv hvw).1
lemma Rf_mono {k : ℕ} {v w : ℝ} (hv : thr k ≤ v) (hvw : v ≤ w) : Rf k v ≤ Rf k w :=
  ((QR_nonneg_mono k).2 v w hv hvw).2

/-- Derivative of `Q_k`: `Q_k'(v) = R_k(v)/v` for `v > thr k`. -/
lemma hasDerivAt_Qf : ∀ k : ℕ, ∀ v, thr k < v → HasDerivAt (Qf k) (Rf k v / v) v := by
  intro k
  induction k with
  | zero =>
    intro v _
    have : Qf 0 = fun _ => 1 := rfl
    rw [this]
    simpa [Rf] using hasDerivAt_const v (1 : ℝ)
  | succ k ih =>
    intro v hv
    rw [thr] at hv
    have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos _) hv.le
    have hlv : thr k < Real.log v := (Real.lt_log_iff_exp_lt hv0).2 hv
    have hl0 : 0 < Real.log v := lt_of_le_of_lt (thr_nonneg k) hlv
    have hfun : Qf (k + 1) = fun v => Real.log v * Qf k (Real.log v) := rfl
    rw [hfun]
    have h1 := Real.hasDerivAt_log hv0.ne'
    have h2 := (ih (Real.log v) hlv).comp v h1
    have h3 := h1.mul h2
    convert h3 using 1
    rw [Rf_succ]
    simp only [Function.comp_apply]
    field_simp

lemma continuousAt_Qf : ∀ k : ℕ, ∀ v, thr k ≤ v → ContinuousAt (Qf k) v := by
  intro k
  induction k with
  | zero => intro v _; exact continuousAt_const
  | succ k ih =>
    intro v hv
    rw [thr] at hv
    have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos _) hv
    have hlv : thr k ≤ Real.log v := (Real.le_log_iff_exp_le hv0).2 hv
    have hfun : Qf (k + 1) = fun v => Real.log v * Qf k (Real.log v) := rfl
    rw [hfun]
    have hlc : ContinuousAt Real.log v := Real.continuousAt_log hv0.ne'
    exact hlc.mul ((ih _ hlv).comp hlc)

lemma Qf_tower_eq_zero (k : ℕ) : Qf (k + 1) (tower k) = 0 := by
  rw [Qf_succ', iterLog_tower_self_succ, mul_zero]

/-- `log s / s` is antitone on `[e, ∞)`. -/
lemma log_div_antitone {s u : ℝ} (hs0 : 0 < s) (hs : 1 ≤ Real.log s) (hsu : s ≤ u) :
    Real.log u / u ≤ Real.log s / s := by
  have hu0 : 0 < u := by linarith
  rw [div_le_div_iff₀ hu0 hs0]
  have h1 : Real.log u - Real.log s ≤ u / s - 1 := by
    rw [← Real.log_div hu0.ne' hs0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hu0 hs0)
  have h2 : s * (Real.log u - Real.log s) ≤ u - s := by
    have := mul_le_mul_of_nonneg_left h1 hs0.le
    have e : s * (u / s - 1) = u - s := by field_simp
    linarith
  nlinarith

/-- `ℓ_j(u) ≤ u / e_j` for `u ≥ e_j`. -/
lemma iterLog_le_div_tower : ∀ j : ℕ, ∀ u, tower j ≤ u → iterLog j u ≤ u / tower j := by
  intro j
  induction j with
  | zero => intro u _; simp [iterLog_zero, tower]
  | succ j ih =>
    intro u hu
    rw [tower_succ] at hu
    have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
    have hlu : tower j ≤ Real.log u := (Real.le_log_iff_exp_le hu0).2 hu
    rw [iterLog_succ']
    refine (ih _ hlu).trans ?_
    have ht1 := one_le_tower j
    have htp := tower_pos j
    have key := log_div_antitone (s := Real.exp (tower j)) (u := u) (Real.exp_pos _)
      (by rw [Real.log_exp]; exact ht1) hu
    rw [Real.log_exp] at key
    rw [tower_succ, div_le_div_iff₀ htp (Real.exp_pos _)]
    rw [div_le_div_iff₀ hu0 (Real.exp_pos _)] at key
    linarith

/-- `R_k(w) log w ≤ k Q_k(w)` for `w ≥ e_k`. -/
lemma Rf_mul_log_le : ∀ k : ℕ, ∀ w, tower k ≤ w → Rf k w * Real.log w ≤ k * Qf k w := by
  intro k
  induction k with
  | zero => intro w _; simp [Rf]
  | succ k ih =>
    intro w hw
    rw [tower_succ] at hw
    have hw0 : 0 < w := lt_of_lt_of_le (Real.exp_pos _) hw
    set u := Real.log w with hu
    have hu1 : tower k ≤ u := (Real.le_log_iff_exp_le hw0).2 hw
    have hthr : thr k ≤ u := (thr_le_tower k).trans hu1
    have hQ := Qf_nonneg hthr
    have hR := Rf_nonneg hthr
    have hu0 : 0 ≤ u := le_trans (by linarith [one_le_tower k]) hu1
    have hRk : Rf k u ≤ k * Qf k u := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp [Rf]
      · have hlu : 1 ≤ Real.log u := by
          have : Real.exp 1 ≤ u := by
            calc Real.exp 1 ≤ Real.exp (tower (k - 1)) :=
                  Real.exp_le_exp.2 (one_le_tower _)
              _ = tower k := by rw [← tower_succ, Nat.sub_add_cancel h]
              _ ≤ u := hu1
          rwa [Real.le_log_iff_exp_le (by linarith [Real.add_one_le_exp (1 : ℝ)])]
        have := ih u hu1
        nlinarith
    rw [Rf_succ, Qf_succ]
    push_cast
    nlinarith

/-- `Q_k(log w) ≤ Q_k(w) / e_k` for `w ≥ e_{k+1}`. -/
lemma Qf_log_le (k : ℕ) {w : ℝ} (hw : tower (k + 1) ≤ w) :
    Qf k (Real.log w) ≤ Qf k w / tower k := by
  rw [tower_succ] at hw
  have hw0 : 0 < w := lt_of_lt_of_le (Real.exp_pos _) hw
  have hlw : tower k ≤ Real.log w := (Real.le_log_iff_exp_le hw0).2 hw
  have hl0 : 0 < Real.log w := lt_of_lt_of_le (tower_pos k) hlw
  have hthr : thr k ≤ w := (thr_le_tower k).trans
    (le_trans (by linarith [Real.add_one_le_exp (tower k)]) hw)
  have hQ := Qf_nonneg hthr
  have h1 : Qf k (Real.log w) * Real.log w = Qf k w * iterLog (k + 1) w := by
    rw [mul_comm, ← Qf_succ, Qf_succ']
  have h2 : iterLog (k + 1) w ≤ Real.log w / tower k := by
    rw [iterLog_succ']; exact iterLog_le_div_tower k _ hlw
  have h3 : Qf k (Real.log w) * Real.log w ≤ Qf k w / tower k * Real.log w := by
    rw [h1, div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h2 hQ
  exact le_of_mul_le_mul_right h3 hl0

/-- `0 ≤ ℓ_{k+1}(v) ≤ 1` on `[e_k, e_{k+1}]`. -/
lemma iterLog_succ_mem_unit {k : ℕ} {v : ℝ} (h1 : tower k ≤ v) (h2 : v ≤ tower (k + 1)) :
    0 ≤ iterLog (k + 1) v ∧ iterLog (k + 1) v ≤ 1 := by
  have hthr : thr (k + 1) ≤ v := by rw [thr_succ_eq]; exact h1
  refine ⟨(iterLog_nonneg_mono (k + 1)).1 v hthr, ?_⟩
  have := (iterLog_nonneg_mono (k + 1)).2 v (tower (k + 1)) hthr h2
  rw [iterLog_tower (k + 1) (k + 1) le_rfl, Nat.sub_self] at this
  simpa [tower] using this

/-- `ℓ_k(z) ≤ log z` for `k ≥ 1` and `z ≥ e_k`. -/
lemma iterLog_le_log {k : ℕ} (hk : 1 ≤ k) {z : ℝ} (hz : tower k ≤ z) :
    iterLog k z ≤ Real.log z := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [tower_succ] at hz
  have hz0 : 0 < z := lt_of_lt_of_le (Real.exp_pos _) hz
  have hlz : tower j ≤ Real.log z := (Real.le_log_iff_exp_le hz0).2 hz
  rw [iterLog_succ']
  refine (iterLog_le_div_tower j _ hlz).trans ?_
  have hl0 : 0 ≤ Real.log z := le_trans (tower_pos j).le hlz
  exact div_le_self hl0 (one_le_tower j)

/-- If `ℓ_i(z) ≥ 1` for all `i ≤ k`, then `z ≥ e_k`. -/
lemma tower_le_of_iterLog : ∀ k : ℕ, ∀ z, (∀ i ≤ k, 1 ≤ iterLog i z) → tower k ≤ z := by
  intro k
  induction k with
  | zero => intro z h; simpa [tower, iterLog_zero] using h 0 le_rfl
  | succ k ih =>
    intro z h
    have hz : 0 < z := by have := h 0 (Nat.zero_le _); rw [iterLog_zero] at this; linarith
    have := ih (Real.log z) (fun i hi => by rw [← iterLog_succ']; exact h (i + 1) (by omega))
    rw [tower_succ]
    rw [Real.le_log_iff_exp_le hz] at this
    exact this

/-- Integral estimate: with `q = log(z - a)`,
`∫_{e_k}^q Q_{k+1} ≥ Q_{k+2}(z) - b_{k+2} Q_{k+1}(z)`. -/
theorem integral_Qf_lower (k : ℕ) {a z : ℝ} (ha : 0 ≤ a) (hz : tower (k + 2) ≤ z)
    (hza : 2 * a ≤ z) :
    Qf (k + 2) z - ((k + 1) / tower k + 2 * a / (tower (k + 2) * tower (k + 1))) *
      Qf (k + 1) z ≤ ∫ v in (tower k)..(Real.log (z - a)), Qf (k + 1) v := by
  have hz0 : 0 < z := lt_of_lt_of_le (tower_pos _) hz
  set w := Real.log z with hw
  set q := Real.log (z - a) with hq
  have hw1 : tower (k + 1) ≤ w := by
    rw [hw, Real.le_log_iff_exp_le hz0]; exact hz
  have htk := tower_pos k
  have htk1 := tower_succ_ge k
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hza0 : z / 2 ≤ z - a := by linarith
  have hza1 : 0 < z - a := by linarith
  have hqw : q ≤ w := Real.log_le_log hza1 (by linarith)
  have hqk : tower k ≤ q := by
    have : Real.log (z / 2) ≤ q := Real.log_le_log (by linarith) hza0
    rw [Real.log_div hz0.ne' (by norm_num)] at this
    linarith
  have hthr : thr (k + 1) = tower k := thr_succ_eq k
  -- integrability
  have hQint : ∀ s t, tower k ≤ s → s ≤ t → IntervalIntegrable (Qf (k + 1)) volume s t := by
    intro s t hs hst
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hst]
    intro v hv v' hv' hvv'
    exact Qf_mono (by rw [hthr]; exact hs.trans hv.1) hvv'
  have hRint : IntervalIntegrable (Rf (k + 1)) volume (tower k) w := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le (hqk.trans hqw)]
    intro v hv v' hv' hvv'
    exact Rf_mono (by rw [hthr]; exact hv.1) hvv'
  -- Step 1: FTC on [e_k, w]
  set Rw := Rf (k + 1) w with hRw
  have hstep1 : Qf (k + 2) z - w * Rw ≤ ∫ v in (tower k)..w, Qf (k + 1) v := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (hqk.trans hqw)
      (f := fun v => v * Qf (k + 1) v - Rw * v)
      (f' := fun v => Qf (k + 1) v + Rf (k + 1) v - Rw)
      (by
        intro v hv
        apply ContinuousAt.continuousWithinAt
        exact (continuousAt_id.mul (continuousAt_Qf (k + 1) v (by rw [hthr]; exact hv.1))).sub
          (continuousAt_const.mul continuousAt_id))
      (by
        intro v hv
        have hv0 : 0 < v := lt_of_lt_of_le htk hv.1.le
        have hd := hasDerivAt_Qf (k + 1) v (by rw [hthr]; exact hv.1)
        have := ((hasDerivAt_id v).mul hd).sub ((hasDerivAt_id v).const_mul Rw)
        convert this using 1
        simp only [id]
        field_simp)
      (((hQint _ _ le_rfl (hqk.trans hqw)).add hRint).sub intervalIntegrable_const)
    have hmono : ∫ v in (tower k)..w, (Qf (k + 1) v + Rf (k + 1) v - Rw) ≤
        ∫ v in (tower k)..w, Qf (k + 1) v := by
      apply intervalIntegral.integral_mono_on (hqk.trans hqw)
        (((hQint _ _ le_rfl (hqk.trans hqw)).add hRint).sub intervalIntegrable_const)
        (hQint _ _ le_rfl (hqk.trans hqw))
      intro v hv
      have := Rf_mono (k := k + 1) (by rw [hthr]; exact hv.1) hv.2
      linarith
    rw [hftc] at hmono
    simp only at hmono
    rw [Qf_tower_eq_zero] at hmono
    have hQz : Qf (k + 2) z = w * Qf (k + 1) w := by rw [Qf_succ]
    have hR0 : 0 ≤ Rw := Rf_nonneg (by rw [hthr]; exact hqk.trans hqw)
    rw [hQz]
    nlinarith
  -- Step 2: w R_{k+1}(w) ≤ ((k+1)/e_k) Q_{k+1}(z)
  have hstep2 : w * Rw ≤ (k + 1) / tower k * Qf (k + 1) z := by
    have hlw : 0 < Real.log w := lt_of_lt_of_le (tower_pos k)
      ((Real.le_log_iff_exp_le (lt_of_lt_of_le (tower_pos _) hw1)).2 hw1)
    have h1 := Rf_mul_log_le (k + 1) w hw1
    rw [Qf_succ] at h1
    have h2 : Rw ≤ (k + 1) * Qf k (Real.log w) := by
      have : Rw * Real.log w ≤ ((k + 1) * Qf k (Real.log w)) * Real.log w := by
        push_cast at h1; nlinarith
      exact le_of_mul_le_mul_right this hlw
    have h3 := Qf_log_le k hw1
    have hw0 : 0 ≤ w := le_trans (tower_pos _).le hw1
    have hQz : Qf (k + 1) z = w * Qf k w := by rw [Qf_succ]
    rw [hQz]
    calc w * Rw ≤ w * ((k + 1) * Qf k (Real.log w)) := mul_le_mul_of_nonneg_left h2 hw0
      _ ≤ w * ((k + 1) * (Qf k w / tower k)) := by gcongr
      _ = (k + 1) / tower k * (w * Qf k w) := by ring
  -- Step 3: the omitted interval
  have hstep3 : ∫ v in q..w, Qf (k + 1) v ≤
      2 * a / (tower (k + 2) * tower (k + 1)) * Qf (k + 1) z := by
    have h1 : ∫ v in q..w, Qf (k + 1) v ≤ ∫ _v in q..w, Qf (k + 1) w := by
      apply intervalIntegral.integral_mono_on hqw (hQint _ _ hqk hqw) intervalIntegrable_const
      intro v hv
      exact Qf_mono (by rw [hthr]; exact hqk.trans hv.1) hv.2
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have h2 : w - q ≤ 2 * a / z := by
      rw [hw, hq, ← Real.log_div hz0.ne' hza1.ne']
      refine (Real.log_le_sub_one_of_pos (div_pos hz0 hza1)).trans ?_
      rw [div_sub_one hza1.ne', div_le_div_iff₀ hza1 hz0]
      nlinarith
    have h3 := Qf_log_le (k + 1) hz
    have hQw0 : 0 ≤ Qf (k + 1) w := Qf_nonneg (by rw [hthr]; exact hqk.trans hqw)
    have h4 : 2 * a / z ≤ 2 * a / tower (k + 2) := div_le_div_of_nonneg_left (by linarith)
      (tower_pos _) hz
    have hQz0 : 0 ≤ Qf (k + 1) z := Qf_nonneg (by
      rw [hthr]; exact (tower_mono (by omega : k ≤ k + 2)).trans hz)
    calc ∫ v in q..w, Qf (k + 1) v ≤ (w - q) * Qf (k + 1) w := h1
      _ ≤ (2 * a / tower (k + 2)) * (Qf (k + 1) z / tower (k + 1)) := by
          apply mul_le_mul (h2.trans h4) h3 hQw0 (div_nonneg (by linarith) (tower_pos _).le)
      _ = 2 * a / (tower (k + 2) * tower (k + 1)) * Qf (k + 1) z := by
          field_simp
  -- combine
  have hsplit := intervalIntegral.integral_interval_sub_left (hQint _ _ le_rfl (hqk.trans hqw))
    (hQint _ _ le_rfl hqk)
  linarith

/-- Integral estimate: `∫_{e_k}^q Q_k ≤ Q_{k+1}(z)`. -/
theorem integral_Qf_upper (k : ℕ) {a z : ℝ} (hz : tower (k + 1) ≤ z) (ha : 0 ≤ a)
    (hza2 : 2 * a ≤ z) (hza : tower k ≤ Real.log (z - a)) :
    ∫ v in (tower k)..(Real.log (z - a)), Qf k v ≤ Qf (k + 1) z := by
  have hz0 : 0 < z := lt_of_lt_of_le (tower_pos _) hz
  set q := Real.log (z - a) with hq
  have hza1 : 0 < z - a := by linarith
  have hqw : q ≤ Real.log z := Real.log_le_log hza1 (by linarith)
  have hthr : thr k ≤ tower k := thr_le_tower k
  have hint : IntervalIntegrable (Qf k) volume (tower k) q := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hza]
    intro v hv v' hv' hvv'
    exact Qf_mono (hthr.trans hv.1) hvv'
  have h1 : ∫ v in (tower k)..q, Qf k v ≤ ∫ _v in (tower k)..q, Qf k q := by
    apply intervalIntegral.integral_mono_on hza hint intervalIntegrable_const
    intro v hv
    exact Qf_mono (hthr.trans hv.1) hv.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  have hQq0 : 0 ≤ Qf k q := Qf_nonneg (hthr.trans hza)
  have hQq : Qf k q ≤ Qf k (Real.log z) := Qf_mono (hthr.trans hza) hqw
  rw [Qf_succ]
  have htk := tower_pos k
  calc ∫ v in (tower k)..q, Qf k v ≤ (q - tower k) * Qf k q := h1
    _ ≤ Real.log z * Qf k (Real.log z) := by
        apply mul_le_mul (by linarith) hQq hQq0 (by linarith)

/-- The constants `b_{k+2} = (k+1)/e_k + 2a/(e_{k+2} e_{k+1})`. -/
def bSeq (a : ℝ) (k : ℕ) : ℝ := (k + 1) / tower k + 2 * a / (tower (k + 2) * tower (k + 1))

/-- `∑_{j<k} b_{j+2} ≤ 4 + a`. -/
lemma sum_bSeq_le (a : ℝ) (ha : 0 ≤ a) (k : ℕ) : ∑ j ∈ range k, bSeq a j ≤ 4 + a := by
  have h1 : ∀ k, ∑ j ∈ range k, ((j : ℝ) + 1) / 2 ^ j = 4 - (2 * k + 4) / 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      field_simp
      ring
  have h2 : ∀ k, ∑ j ∈ range k, (1 : ℝ) / 2 ^ (j + 1) = 1 - 1 / 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp
      ring
  have hb : ∀ j, bSeq a j ≤ ((j : ℝ) + 1) / 2 ^ j + a * (1 / 2 ^ (j + 1)) := by
    intro j
    unfold bSeq
    have ht1 := two_pow_le_tower j
    have ht2 := two_pow_le_tower (j + 2)
    have ht3 := one_le_tower (j + 1)
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    gcongr ?_ + ?_
    · exact div_le_div_of_nonneg_left (by positivity) hp ht1
    · rw [mul_one_div, div_le_div_iff₀ (mul_pos (tower_pos _) (tower_pos _)) (by positivity)]
      have : (2 : ℝ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
      rw [this] at ht2
      have h0 : (0 : ℝ) ≤ 2 ^ (j + 1) := by positivity
      nlinarith [mul_le_mul ht2 ht3 (by norm_num) (tower_pos (j + 2)).le]
  calc ∑ j ∈ range k, bSeq a j ≤ ∑ j ∈ range k, (((j : ℝ) + 1) / 2 ^ j + a * (1 / 2 ^ (j + 1))) :=
        Finset.sum_le_sum (fun j _ => hb j)
    _ = (4 - (2 * k + 4) / 2 ^ k) + a * (1 - 1 / 2 ^ k) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
    _ ≤ 4 + a := by
        have : 0 ≤ (2 * (k : ℝ) + 4) / 2 ^ k := by positivity
        have : 0 ≤ a * (1 / 2 ^ k) := by positivity
        nlinarith

section induction

variable {C : ℝ} (hC2 : 2 ≤ C) (hC : CommonMultipleBound C)
  (hmert : ∀ t : ℝ, 2 ≤ t → |primeRecipSum t - Real.log (Real.log t)| ≤ C)

/-! ## The lower estimate -/

/-- The constant `a₁ = z₀ + 2a + 2C + 10`. -/
def aOne (C : ℝ) : ℝ := 3 * Real.log (Dconst C) + Dconst C + 2 * C + 10

/-- The constants `a_{k+1} = a₁ + ∑_{j=2}^{k+1} b_j`. -/
def aSeq (C : ℝ) (k : ℕ) : ℝ := aOne C + ∑ j ∈ range k, bSeq (Real.log (Dconst C)) j

/-- `a_* = a₁ + 4 + a`. -/
def aStar (C : ℝ) : ℝ := aOne C + 4 + Real.log (Dconst C)

include hC2 in
lemma logD_nonneg : 0 ≤ Real.log (Dconst C) :=
  Real.log_nonneg (by linarith [Dconst_ge hC2])

include hC2 in
lemma bSeq_nonneg (j : ℕ) : 0 ≤ bSeq (Real.log (Dconst C)) j := by
  unfold bSeq
  have := logD_nonneg hC2
  have h1 := tower_pos j
  have h2 := tower_pos (j + 1)
  have h3 := tower_pos (j + 2)
  positivity

include hC2 in
lemma one_le_aSeq (k : ℕ) : 1 ≤ aSeq C k := by
  unfold aSeq aOne
  have := logD_nonneg hC2
  have := Dconst_ge hC2
  have : 0 ≤ ∑ j ∈ range k, bSeq (Real.log (Dconst C)) j :=
    Finset.sum_nonneg (fun j _ => bSeq_nonneg hC2 j)
  linarith

include hC2 in
lemma aSeq_le_aStar (k : ℕ) : aSeq C k ≤ aStar C := by
  unfold aSeq aStar
  have := sum_bSeq_le (Real.log (Dconst C)) (logD_nonneg hC2) k
  linarith

include hC2 in
lemma aOne_le_aSeq (k : ℕ) : aOne C ≤ aSeq C k := by
  unfold aSeq
  have : 0 ≤ ∑ j ∈ range k, bSeq (Real.log (Dconst C)) j :=
    Finset.sum_nonneg (fun j _ => bSeq_nonneg hC2 j)
  linarith

include hC2 hC hmert in
/-- `H(z) ≥ Q_{k+1}(z) - a_{k+1} Q_k(z)` for `z ≥ e_{k+1}`. -/
theorem Hf_ge_Qf : ∀ k : ℕ, ∀ z : ℝ, tower (k + 1) ≤ z →
    Qf (k + 1) z - aSeq C k * Qf k z ≤ Hf (Real.log (Dconst C)) z := by
  set D := Dconst C with hD
  set a := Real.log D with ha
  have ha0 : 0 ≤ a := logD_nonneg hC2
  have hD4 := Dconst_ge hC2
  intro k
  induction k with
  | zero =>
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le (tower_pos 1) hz
    have := Hf_ge_log hC2 hmert hz0
    simp only [Qf, mul_one, aSeq, Finset.range_zero, Finset.sum_empty, add_zero]
    unfold aOne
    linarith
  | succ k ih =>
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le (tower_pos _) hz
    -- extended inductive hypothesis
    have hext : ∀ v, tower k ≤ v → Qf (k + 1) v - aSeq C k * Qf k v ≤ Hf a v := by
      intro v hv
      by_cases hv1 : tower (k + 1) ≤ v
      · exact ih v hv1
      · push_neg at hv1
        obtain ⟨h0, h1⟩ := iterLog_succ_mem_unit hv hv1.le
        have hQ : 0 ≤ Qf k v := Qf_nonneg ((thr_le_tower k).trans hv)
        have hA := one_le_aSeq hC2 (C := C) k
        rw [Qf_succ']
        have : Qf k v * iterLog (k + 1) v ≤ aSeq C k * Qf k v := by nlinarith
        have := Hf_nonneg a v
        linarith
    have hQk1 : 0 ≤ Qf (k + 1) z := Qf_nonneg ((thr_le_tower (k + 1)).trans
      ((tower_mono (Nat.le_succ (k + 1))).trans hz))
    have haSeq : aSeq C (k + 1) = aSeq C k + bSeq a k := by
      unfold aSeq; rw [Finset.sum_range_succ]; ring
    by_cases hsmall : iterLog (k + 2) z ≤ aSeq C (k + 1)
    · rw [Qf_succ' (k + 1)]
      have := Hf_nonneg a z
      nlinarith
    push_neg at hsmall
    have hlz : iterLog (k + 2) z ≤ Real.log z := iterLog_le_log (by omega) hz
    have ha1 : aOne C < Real.log z := lt_of_le_of_lt (aOne_le_aSeq hC2 (k + 1))
      (lt_of_lt_of_le hsmall hlz)
    have hz1 : aOne C + 1 ≤ z := by
      have := Real.add_one_le_exp (aOne C)
      have : Real.exp (aOne C) < z := by rwa [Real.lt_log_iff_exp_lt hz0] at ha1
      linarith
    have hz0' : a + D ≤ z := by unfold aOne at hz1; linarith
    have hza : 2 * a ≤ z := by unfold aOne at hz1; linarith [hD4]
    -- the recursion
    have hrec := Hf_recurrence hC2 hC hmert hz0'
    set q := Real.log (z - a) with hq
    have hqk : tower k ≤ q := by
      have hz2 : tower (k + 1) ≤ Real.log z := by
        rw [Real.le_log_iff_exp_le hz0, ← tower_succ]; exact hz
      have : Real.log (z / 2) ≤ q := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_div hz0.ne' (by norm_num)] at this
      have hl2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
      linarith [tower_succ_ge k]
    have htk0 : 0 ≤ tower k := (tower_pos k).le
    have hHint : ∀ s t, IntervalIntegrable (Hf a) volume s t :=
      fun s t => (Hf_mono a).intervalIntegrable
    have hQint1 : IntervalIntegrable (Qf (k + 1)) volume (tower k) q := by
      apply MonotoneOn.intervalIntegrable
      rw [Set.uIcc_of_le hqk]
      intro v hv w _ hvw
      exact Qf_mono (by rw [thr_succ_eq]; exact hv.1) hvw
    have hQint0 : IntervalIntegrable (Qf k) volume (tower k) q := by
      apply MonotoneOn.intervalIntegrable
      rw [Set.uIcc_of_le hqk]
      intro v hv w _ hvw
      exact Qf_mono ((thr_le_tower k).trans hv.1) hvw
    -- drop [0, e_k]
    have h1 : ∫ v in (tower k)..q, Hf a v ≤ ∫ v in (0 : ℝ)..q, Hf a v := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hHint 0 (tower k)) (hHint _ q)]
      have : 0 ≤ ∫ v in (0 : ℝ)..(tower k), Hf a v :=
        intervalIntegral.integral_nonneg htk0 (fun v _ => Hf_nonneg a v)
      linarith
    -- compare with the inductive lower bound
    have h2 : ∫ v in (tower k)..q, (Qf (k + 1) v - aSeq C k * Qf k v) ≤
        ∫ v in (tower k)..q, Hf a v :=
      intervalIntegral.integral_mono_on hqk ((hQint1.sub (hQint0.const_mul _)))
        (hHint _ _) (fun v hv => hext v hv.1)
    rw [intervalIntegral.integral_sub hQint1 (hQint0.const_mul _),
      intervalIntegral.integral_const_mul] at h2
    have h3 := integral_Qf_lower k ha0 hz hza
    have h4 := integral_Qf_upper k ((tower_mono (Nat.le_succ (k + 1))).trans hz) ha0 hza hqk
    have hA0 : 0 ≤ aSeq C k := by linarith [one_le_aSeq hC2 (C := C) k]
    have h5 : aSeq C k * ∫ v in (tower k)..q, Qf k v ≤ aSeq C k * Qf (k + 1) z :=
      mul_le_mul_of_nonneg_left h4 hA0
    rw [haSeq]
    unfold bSeq at haSeq
    have : bSeq a k = (k + 1) / tower k + 2 * a / (tower (k + 2) * tower (k + 1)) := rfl
    push_cast at h3 ⊢
    rw [this] at *
    nlinarith

include hC2 hC hmert in
/-- If `z ≥ e_{k+1}` and `ℓ_{k+1}(z) ≥ T = 2a_* + 2`, then
`H(z) ≥ Q_{k+1}(z) / 2`. -/
theorem Hf_ge_half_Qf (k : ℕ) {z : ℝ} (hz : tower (k + 1) ≤ z)
    (hT : 2 * aStar C + 2 ≤ iterLog (k + 1) z) :
    Qf (k + 1) z / 2 ≤ Hf (Real.log (Dconst C)) z := by
  have h := Hf_ge_Qf hC2 hC hmert k z hz
  have hA := aSeq_le_aStar hC2 (C := C) k
  have hQ : 0 ≤ Qf k z := Qf_nonneg ((thr_le_tower k).trans
    ((tower_mono (Nat.le_succ k)).trans hz))
  rw [Qf_succ'] at h ⊢
  have : aSeq C k * Qf k z ≤ Qf k z * iterLog (k + 1) z / 2 := by
    have : aSeq C k ≤ iterLog (k + 1) z / 2 := by linarith
    calc aSeq C k * Qf k z ≤ iterLog (k + 1) z / 2 * Qf k z :=
          mul_le_mul_of_nonneg_right this hQ
      _ = Qf k z * iterLog (k + 1) z / 2 := by ring
  linarith

end induction

/-- `Q_{K-2}(ℓ_2 x) = ∏_{j=3}^{K} ℓ_j(x)`. -/
lemma Qf_iterLog_two (K : ℕ) (hK : 3 ≤ K) (x : ℝ) :
    Qf (K - 2) (iterLog 2 x) = ∏ j ∈ Icc 3 K, iterLog j x := by
  rw [Qf_eq_prod]
  have : Icc 3 K = Ico 3 (K + 1) := rfl
  rw [this, Finset.prod_Ico_eq_prod_range, show K + 1 - 3 = K - 2 by omega]
  apply Finset.prod_congr rfl
  intro j _
  rw [← iterLog_add]
  congr 1
  omega

/-- **The lower estimate**: `G(N) ≪ R(N)`. -/
theorem G_le_R : ∃ b : ℝ, 0 < b ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, b * G N ≤ R N := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := mertens_second
  obtain ⟨C₂, hC₂0, hC₂⟩ := common_multiple_bound
  obtain ⟨c, hc, x₀, hx₀, hcheb⟩ := chebyshev_lower
  set C := max 2 (max C₁ C₂) with hCdef
  have hC2 : 2 ≤ C := le_max_left _ _
  have hC : CommonMultipleBound C := by
    intro m hm
    obtain ⟨L, hL0, hdvd, hLb⟩ := hC₂ m hm
    refine ⟨L, hL0, hdvd, hLb.trans (Real.exp_le_exp.2 ?_)⟩
    have : C₂ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg m)
  have hmert : ∀ t : ℝ, 2 ≤ t → |primeRecipSum t - Real.log (Real.log t)| ≤ C := fun t ht =>
    (hC₁ t ht).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  obtain ⟨X, hX1, hX⟩ := uCount_ge hC2 hC hc hx₀ hcheb
  set D := Dconst C with hD
  set a := Real.log D with ha
  have hD4 := Dconst_ge hC2
  have ha0 : 0 ≤ a := logD_nonneg hC2
  set T := 2 * aStar C + 2 with hT
  have hT2 : 2 ≤ T := by
    have : 0 ≤ aStar C := by
      unfold aStar aOne; rw [← hD, ← ha]; linarith
    linarith
  have hT0 : 0 < T := by linarith
  have hTpow : 0 < T ^ ⌈T⌉₊ := by positivity
  refine ⟨c / 4 / T ^ ⌈T⌉₊, by positivity, ⌈max X (towerThreshold T)⌉₊, fun N hN => ?_⟩
  have hN' : max X (towerThreshold T) ≤ N := Nat.ceil_le.1 hN
  have hNX : X ≤ N := le_trans (le_max_left _ _) hN'
  have hNT : towerThreshold T ≤ N := le_trans (le_max_right _ _) hN'
  have hN1 : (1 : ℝ) < N := lt_of_lt_of_le hX1 hNX
  have hlN : 0 < Real.log N := Real.log_pos hN1
  -- the stopping index for T
  set K := stopIndex T N with hK
  have hK3 := stopIndex_three_le hT0 hNT
  have hKge := stopIndex_ge hT0 hNT
  -- u(N) ≥ (c/2) (N/log N) W(log N / D)
  have hu := hX N hNX
  have hW : Wsum (Real.log N / D) = Hf a (iterLog 2 N) := by
    unfold Hf
    congr 1
    rw [Real.exp_sub, show iterLog 2 (N : ℝ) = Real.log (Real.log N) from rfl,
      Real.exp_log hlN, ha, Real.exp_log (by linarith)]
  -- H(ℓ₂ N) ≥ P_T(N) / 2
  have hz : tower (K - 3 + 1) ≤ iterLog 2 N := by
    apply tower_le_of_iterLog
    intro i hi
    rw [← iterLog_add]
    exact le_trans (by linarith) (hKge (i + 2) (by omega))
  have hTz : T ≤ iterLog (K - 3 + 1) (iterLog 2 N) := by
    rw [← iterLog_add, show K - 3 + 1 + 2 = K by omega]
    exact hKge K le_rfl
  have hH := Hf_ge_half_Qf hC2 hC hmert (K - 3) hz hTz
  rw [show K - 3 + 1 = K - 2 by omega, Qf_iterLog_two K hK3] at hH
  have hP : stopProd T N = ∏ j ∈ Icc 3 K, iterLog j N := rfl
  rw [← hP] at hH
  -- threshold comparison
  have hcmp := (stopProd_threshold_comparison (le_refl 2) hT2 hNT).2
  have hR := uCount_le_R N
  have hfac : 0 ≤ (N : ℝ) / Real.log N := by positivity
  have hPT0 := stopProd_nonneg hT0 hNT
  calc c / 4 / T ^ ⌈T⌉₊ * G N = c / 4 / T ^ ⌈T⌉₊ * ((N : ℝ) / Real.log N * stopProd 2 N) := rfl
    _ ≤ c / 4 / T ^ ⌈T⌉₊ * ((N : ℝ) / Real.log N * (T ^ ⌈T⌉₊ * stopProd T N)) := by
        gcongr
    _ = c / 2 * ((N : ℝ) / Real.log N) * (stopProd T N / 2) := by
        field_simp
        ring
    _ ≤ c / 2 * ((N : ℝ) / Real.log N) * Wsum (Real.log N / D) := by
        rw [hW]
        exact mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ uCount N := hu
    _ ≤ R N := by exact_mod_cast hR

/-! ## Main results -/

/-- **Main theorem.** There are constants `b₁, b₂ > 0` and `N₀` such that for every `N ≥ N₀`,
`b₁ G(N) ≤ R(N) ≤ log S(N) / log 2 ≤ b₂ G(N)`. -/
theorem main_theorem : ∃ b₁ b₂ : ℝ, 0 < b₁ ∧ 0 < b₂ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    b₁ * G N ≤ R N ∧ (R N : ℝ) ≤ Real.log (S N) / Real.log 2 ∧
      Real.log (S N) / Real.log 2 ≤ b₂ * G N := by
  obtain ⟨C, hC, N₁, hN₁⟩ := log_S_le_G
  obtain ⟨b, hb, N₂, hN₂⟩ := G_le_R
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨b, C / Real.log 2, hb, div_pos hC hl2, max N₁ N₂, fun N hN => ⟨?_, ?_, ?_⟩⟩
  · exact hN₂ N (le_of_max_le_right hN)
  · exact R_le_log_S_div_log_two N
  · rw [div_le_iff₀ hl2]
    have := hN₁ N (le_of_max_le_left hN)
    calc Real.log (S N) ≤ C * G N := this
      _ = C / Real.log 2 * G N * Real.log 2 := by field_simp

/-- The number of distinct reciprocal subset sums of `{1, …, N}`
satisfies `exp(d₁ G(N)) ≤ |E_N| ≤ exp(d₂ G(N))` for large `N`. -/
theorem card_recipSubsetSums_bounds : ∃ d₁ d₂ : ℝ, 0 < d₁ ∧ 0 < d₂ ∧ ∃ N₁ : ℕ, ∀ N ≥ N₁,
    Real.exp (d₁ * G N) ≤ (recipSubsetSums (Icc 1 N)).card ∧
      ((recipSubsetSums (Icc 1 N)).card : ℝ) ≤ Real.exp (d₂ * G N) := by
  obtain ⟨b₁, b₂, hb₁, hb₂, N₀, h⟩ := main_theorem
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨b₁ * Real.log 2, b₂ * Real.log 2, mul_pos hb₁ hl2, mul_pos hb₂ hl2, N₀,
    fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h N hN
  have hS : (0 : ℝ) < S N := by exact_mod_cast one_le_S N
  have hlow : b₁ * Real.log 2 * G N ≤ Real.log (S N) := by
    have := h1.trans h2
    rw [le_div_iff₀ hl2] at this
    linarith
  have hup : Real.log (S N) ≤ b₂ * Real.log 2 * G N := by
    rw [div_le_iff₀ hl2] at h3
    linarith
  refine ⟨?_, ?_⟩
  · have := Real.exp_le_exp.2 hlow
    rw [Real.exp_log hS] at this
    simpa [S] using this
  · have := Real.exp_le_exp.2 hup
    rw [Real.exp_log hS] at this
    simpa [S] using this

/-- For large `N` there is a reciprocally dissociated
`A ⊆ {1, …, N}` with `|A| ≥ d₃ G(N)`, and every reciprocally dissociated `A ⊆ {1, …, N}`
has `|A| ≤ d₄ G(N)`. -/
theorem recipDissociated_card_bounds : ∃ d₃ d₄ : ℝ, 0 < d₃ ∧ 0 < d₄ ∧ ∃ N₂ : ℕ, ∀ N ≥ N₂,
    (∃ A ⊆ Icc 1 N, RecipDissociated A ∧ d₃ * G N ≤ A.card) ∧
      ∀ A ⊆ Icc 1 N, RecipDissociated A → (A.card : ℝ) ≤ d₄ * G N := by
  obtain ⟨b₁, b₂, hb₁, hb₂, N₀, h⟩ := main_theorem
  refine ⟨b₁, b₂, hb₁, hb₂, N₀, fun N hN => ⟨?_, ?_⟩⟩
  · obtain ⟨A, hA, hd, hc⟩ := exists_R N
    refine ⟨A, hA, hd, ?_⟩
    rw [hc]
    exact (h N hN).1
  · intro A hA hd
    obtain ⟨_, h2, h3⟩ := h N hN
    have : (A.card : ℝ) ≤ R N := by exact_mod_cast le_R hA hd
    linarith

#print axioms main_theorem
#print axioms card_recipSubsetSums_bounds
#print axioms recipDissociated_card_bounds
