import Mathlib

open MeasureTheory Finset BigOperators Real Set
open scoped Nat

set_option maxHeartbeats 32000000
set_option maxRecDepth 8000

/-! # Proof that I < 9263/2000

The integral `I = ∫₀^∞ e^{-x}·√(H(x)·(eˣ-e^{-x})) dx`, where `H(x) = ∏_{p ≤
e^{2x}, prime} (1-1/p)⁻¹`, satisfies `I < 9263/2000` conditional on an explicit
version of Mertens' theorem by Rosser–Schoenfeld.

J. Barkley Rosser, Lowell Schoenfeld, Approximate formulas for some functions of
prime numbers, Illinois J. Math. 6 (1962), 64–94.

This integral is used in an upper bound on Erdős Problem #425
(https://www.erdosproblems.com/425). For the formalization of this upper bound,
see my GitHub

https://github.com/Woett/Lean-files/blob/main/ErdosProblem425Upper.lean

The formalization (done by Aristotle from Harmonic
(aristotle-harmonic@harmonic.fun)) uses the tactic native_decide a bunch of
times, so that the used axioms not only include the Rosser-Schoenfeld result,
but also Lean.ofReduceBool and Lean.trustCompiler, which are used to justify the
correctness of native_decide.

Lean version: leanprover/lean4:v4.28.0
-/

-- =====================================================================
/-! ## §1. Core definitions -/
-- =====================================================================

/-- The prime product `H(x) = ∏_{p ≤ e^{2x}, p prime} (1-1/p)⁻¹`. -/
noncomputable def HFunc (x : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊Real.exp (2 * x)⌋₊ + 1)).filter Nat.Prime,
    (1 - (1 : ℝ) / (p : ℝ))⁻¹

/-- The integrand `F(x) = e^{-x} · √(H(x) · (eˣ - e^{-x}))`. -/
noncomputable def integrandF (x : ℝ) : ℝ :=
  Real.exp (-x) * Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x)))

/-- The integral `I = ∫₀^∞ F(x) dx`. -/
noncomputable def integralI : ℝ := ∫ x in Set.Ici (0 : ℝ), integrandF x

lemma integrandF_nonneg (x : ℝ) : 0 ≤ integrandF x := by
  unfold integrandF; exact mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

-- =====================================================================
/-! ## §2. Computational primitives -/
-- =====================================================================

/-- Upper bound on `exp(-t)`: even Taylor truncation. -/
def expNegUpper (t : ℚ) (n : ℕ) : ℚ :=
  (Finset.range (2*n + 1)).sum (fun k => (-t) ^ k / (k.factorial : ℚ))

/-- Lower bound on `exp(-t)`: odd Taylor truncation. -/
def expNegLower (t : ℚ) (n : ℕ) : ℚ :=
  (Finset.range (2*n + 2)).sum (fun k => (-t) ^ k / (k.factorial : ℚ))

/-- Rational upper bound on `√q`. -/
def sqrtUpperQ (q : ℚ) (S : ℕ) : ℚ :=
  let scaled := (q.num.toNat * S * S + q.den - 1) / q.den
  let n := Nat.sqrt scaled + 1
  (n : ℚ) / S

/-- Ceiling: `⌈B·q⌉/B`. -/
def ceilBQ (B : ℕ) (q : ℚ) : ℚ :=
  let n : ℤ := ((B : ℤ) * q.num + (q.den : ℤ) - 1) / (q.den : ℤ)
  (n : ℚ) / (B : ℚ)

/-- Rosser–Schoenfeld prime product lower bound. -/
axiom RosserSchoenfeld :
  ∀ z : ℝ, z ≥ 285 →
    ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) >
      Real.exp (-Real.eulerMascheroniConstant) / Real.log z *
        (1 - 1 / (2 * (Real.log z) ^ 2))

-- =====================================================================
/-! ## §3. 2 · exp(γ) < 891/250

Uses the harmonic number `H₁₀₀₀`, decomposed as `7 + frac`, together with
Taylor upper bounds on `exp(1)` and `exp(frac)` to bound `exp(H₁₀₀₀)`. -/
-- =====================================================================

def expTaylorUpperQ (x : ℚ) (m : ℕ) : ℚ :=
  (Finset.range m).sum (fun j => x ^ j / (j.factorial : ℚ)) +
    x ^ m * ((m : ℚ) + 1) / ((m.factorial : ℚ) * m)

def H1000Q : ℚ := (Finset.range 1000).sum (fun k => (1 : ℚ) / (k + 1))
def H1000frac : ℚ := H1000Q - 7

lemma H1000frac_nonneg : 0 ≤ H1000frac := by native_decide
lemma H1000frac_lt_one : H1000frac < 1 := by native_decide
lemma H1000frac_le_one : H1000frac ≤ 1 := le_of_lt H1000frac_lt_one
lemma H1000Q_eq : H1000Q = 7 + H1000frac := by simp [H1000frac]

def expH1000Upper : ℚ :=
  expTaylorUpperQ 1 20 ^ 7 * expTaylorUpperQ H1000frac 20

lemma H1000Q_eq_harmonic : H1000Q = harmonic 1000 := by
  simp only [H1000Q, harmonic]; grind +revert

lemma exp_le_taylorUpperQ (x : ℚ) (hx0 : (0 : ℝ) ≤ x) (hx1 : (x : ℝ) ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    Real.exp (x : ℝ) ≤ (expTaylorUpperQ x m : ℝ) := by
  suffices h : Real.exp (x : ℝ) ≤
      (∑ j ∈ Finset.range m, (x : ℝ) ^ j / (j.factorial : ℝ)) +
      (x : ℝ) ^ m * ((m : ℝ) + 1) / ((m.factorial : ℝ) * (m : ℝ)) by
    convert h using 1; unfold expTaylorUpperQ; norm_num
  exact exp_bound' hx0 hx1 hm

lemma exp_harmonic_1000_le :
    Real.exp ((H1000Q : ℚ) : ℝ) ≤ (expH1000Upper : ℝ) := by
  have hf : Real.exp H1000frac ≤ (expTaylorUpperQ H1000frac 20 : ℝ) :=
    exp_le_taylorUpperQ _ (mod_cast H1000frac_nonneg) (mod_cast H1000frac_le_one) 20 (by norm_num)
  have h7 : Real.exp 7 ≤ (expTaylorUpperQ 1 20 : ℝ) ^ 7 := by
    convert pow_le_pow_left₀ (by positivity)
      (exp_le_taylorUpperQ 1 (by norm_num) (by norm_num) 20 (by norm_num)) 7 using 1; norm_num
  convert mul_le_mul h7 hf _ _ using 1 <;> norm_num [H1000Q_eq]
  · rw [Real.exp_add]
  · norm_cast
  · positivity
  · exact pow_nonneg (mod_cast by native_decide) _

theorem two_exp_gamma_lt :
    2 * Real.exp Real.eulerMascheroniConstant < (891 : ℝ) / 250 := by
  have trans : 2 * Real.exp eulerMascheroniConstant < 2 * Real.exp ((H1000Q : ℚ) : ℝ) / 1000 := by
    have h_euler_lt_harmonic : eulerMascheroniConstant < (harmonic 1000 : ℝ) - Real.log 1000 := by
      convert eulerMascheroniConstant_lt_eulerMascheroniSeq' 1000 using 1;
    convert mul_lt_mul_of_pos_left ( Real.exp_lt_exp.mpr h_euler_lt_harmonic ) zero_lt_two using 1;
    rw [ H1000Q_eq_harmonic, Real.exp_sub, Real.exp_log ] <;> ring_nf ; norm_num;
  have upper_bound : 2 * (expH1000Upper : ℝ) / 1000 < (891 : ℝ) / 250 := by
    unfold expH1000Upper;
    unfold expTaylorUpperQ H1000frac;
    norm_num [ Finset.sum_range_succ, Nat.factorial_succ, H1000Q ];
  exact trans.trans_le ( by linarith [ exp_harmonic_1000_le ] )

-- =====================================================================
/-! ## §4. Taylor majorant for √(1-y)

`√(1-y) ≤ P₁₀₀(y)` for `y ∈ [0,1]`, where `P₁₀₀` is the degree-100
Taylor polynomial of `√(1-y)` at `y=0`. Proved via the algebraic
identity `P₁₀₀(y)² - (1-y) ≥ 0` (all coefficients are nonneg). -/
-- =====================================================================

/-- Taylor coefficient `c_k` for `√(1-y)`: `c_0=1`, `c_{k+1}=c_k·(2k-1)/(2k+2)`. -/
def sqrtCoeffQ : ℕ → ℚ
  | 0 => 1
  | k + 1 => sqrtCoeffQ k * ((2 * (k : ℚ)) - 1) / (2 * (k : ℚ) + 2)

noncomputable def sqrtTaylorEval (m : ℕ) (y : ℝ) : ℝ :=
  (Finset.range (m + 1)).sum (fun k => (sqrtCoeffQ k : ℝ) * y ^ k)

/-- Coefficient of `y^k` in `P₁₀₀² - (1-y)`, computable version. -/
def sqMinusCoeff (k : ℕ) : ℚ :=
  let raw := (Finset.range (k + 1)).sum (fun i =>
    if i ≤ 100 ∧ k - i ≤ 100 then sqrtCoeffQ i * sqrtCoeffQ (k - i) else 0)
  raw + (if k = 0 then -1 else if k = 1 then 1 else 0)

noncomputable def sqrtPoly100 : Polynomial ℚ :=
  (Finset.range 101).sum (fun k => Polynomial.C (sqrtCoeffQ k) * Polynomial.X ^ k)

noncomputable def sqMinusPoly : Polynomial ℚ :=
  sqrtPoly100 ^ 2 - (Polynomial.C 1 - Polynomial.X)

lemma sqMinusCoeff_nonneg : ∀ k, k ≤ 200 → 0 ≤ sqMinusCoeff k := by native_decide

lemma sqrtTaylor100_at_one_pos :
    (Finset.range 101).sum (fun k => sqrtCoeffQ k) > 0 := by native_decide

lemma sqrtCoeffQ_nonpos (k : ℕ) (hk : 1 ≤ k) : sqrtCoeffQ k ≤ 0 := by
  induction hk <;> simp_all +decide [sqrtCoeffQ]
  · grind
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg ‹_› (sub_nonneg_of_le (by norm_cast; linarith)))
      (by positivity)

lemma sqrtTaylor100_nonneg (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ sqrtTaylorEval 100 y := by
  have h : ∀ k ∈ Finset.Icc 1 100,
      (sqrtCoeffQ k : ℝ) * y ^ k ≥ (sqrtCoeffQ k : ℝ) := by
    intros k hk
    nlinarith [show (sqrtCoeffQ k : ℝ) ≤ 0 from by
      exact_mod_cast sqrtCoeffQ_nonpos k (Finset.mem_Icc.mp hk |>.1),
      pow_le_one₀ (n := k) hy0 hy1]
  refine le_trans ?_ (Finset.sum_le_sum fun k hk =>
    show (sqrtCoeffQ k : ℝ) * y ^ k ≥ sqrtCoeffQ k from ?_)
  · exact_mod_cast sqrtTaylor100_at_one_pos.le
  · by_cases hk1 : k = 0
    · norm_num [hk1]
    · exact h k <| Finset.mem_Icc.mpr
        ⟨Nat.pos_of_ne_zero hk1, Finset.mem_range_succ_iff.mp hk⟩

lemma sqrtTaylorEval_eq_aeval (y : ℝ) :
    sqrtTaylorEval 100 y = Polynomial.aeval y sqrtPoly100 := by
  simp [sqrtTaylorEval, sqrtPoly100, Polynomial.aeval_def,
    map_sum, map_mul, map_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]

lemma sqrtPoly100_coeff (k : ℕ) :
    sqrtPoly100.coeff k = if k ≤ 100 then sqrtCoeffQ k else 0 := by
  unfold sqrtPoly100
  split_ifs <;> simp_all +decide <;> grind

lemma sqMinusPoly_coeff (k : ℕ) (hk : k ≤ 200) :
    sqMinusPoly.coeff k = sqMinusCoeff k := by
  unfold sqMinusPoly sqMinusCoeff
  simp +decide [pow_two]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Polynomial.coeff_one, Polynomial.coeff_X, sqrtPoly100_coeff]
  grind

lemma sqrtTaylor100_sq_ge (y : ℝ) (hy0 : 0 ≤ y) :
    1 - y ≤ sqrtTaylorEval 100 y ^ 2 := by
  have h_nonneg : Polynomial.aeval (R := ℚ) y sqMinusPoly ≥ 0 := by
    have h_zero : ∀ k > 200, Polynomial.coeff sqMinusPoly k = 0 := by
      unfold sqMinusPoly sqrtPoly100
      norm_num [Polynomial.coeff_one, Polynomial.coeff_X, pow_succ]
      intro k hk; rw [Polynomial.coeff_mul]
      rw [Finset.sum_eq_zero] <;> norm_num
      · grind
      · intros; omega
    rw [Polynomial.aeval_eq_sum_range']
    refine' Finset.sum_nonneg fun i hi => _
    any_goals exact Nat.lt_succ_self _
    by_cases hi' : i ≤ 200 <;>
      simp_all +decide
    exact mul_nonneg
      (by rw [sqMinusPoly_coeff i hi']; exact mod_cast sqMinusCoeff_nonneg i hi')
      (pow_nonneg hy0 _)
  unfold sqMinusPoly at h_nonneg
  simp_all +decide [sqrtTaylorEval_eq_aeval]

/-- `√(1-y) ≤ P₁₀₀(y)` for `y ∈ [0,1]`. -/
lemma sqrt_one_sub_le_taylor100 (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.sqrt (1 - y) ≤ sqrtTaylorEval 100 y :=
  Real.sqrt_le_iff.mpr ⟨sqrtTaylor100_nonneg y hy0 hy1, sqrtTaylor100_sq_ge y hy0⟩

-- =====================================================================
/-! ## §5. Rational arithmetic helpers -/
-- =====================================================================

lemma ceilBQ_le (B : ℕ) (hB : 0 < B) (q : ℚ) : q ≤ ceilBQ B q := by
  unfold ceilBQ
  field_simp
  rw [← Rat.num_div_den q, div_mul_eq_mul_div, div_le_iff₀] <;> norm_cast
  · rw [Rat.divInt_eq_div, Rat.num_div_eq_of_coprime, Rat.den_div_eq_of_coprime] <;>
      norm_num [q.reduced]
    · linarith [Int.mul_ediv_add_emod (B * q.num + q.den - 1) q.den,
        Int.emod_lt_of_pos (B * q.num + q.den - 1) (Nat.cast_pos.mpr q.pos)]
    · exact q.pos
    · exact q.reduced
    · exact q.pos
    · exact q.reduced
  · exact q.pos

lemma sqrt_le_sqrtUpperQ (q : ℚ) (hq : 0 ≤ q) (S : ℕ) (hS : 0 < S) :
    Real.sqrt (q : ℝ) ≤ (sqrtUpperQ q S : ℝ) := by
  unfold sqrtUpperQ
  have h_sq : (Nat.sqrt ((q.num.toNat * S * S + q.den - 1) / q.den) + 1 : ℝ) ^ 2 ≥
      q.num.toNat * S * S / q.den := by
    rw [ge_iff_le, div_le_iff₀] <;> norm_cast
    · nlinarith [Nat.lt_succ_sqrt ((q.num.toNat * S * S + q.den - 1) / q.den),
        Nat.div_add_mod (q.num.toNat * S * S + q.den - 1) q.den,
        Nat.mod_lt (q.num.toNat * S * S + q.den - 1)
          (Nat.pos_of_ne_zero q.pos.ne'),
        Nat.sub_add_cancel (show 1 ≤ q.num.toNat * S * S + q.den from
          Nat.succ_le_of_lt (by positivity))]
    · exact q.pos
  rw [Real.sqrt_le_iff]
  simp_all +decide [mul_div_right_comm]
  rw [div_pow, le_div_iff₀] <;> first | positivity | simp_all +decide [Rat.cast_def]
  rw [le_div_iff₀ (by positivity)]
  exact ⟨by positivity, by convert h_sq using 1; rw [show (q.num : ℝ) = q.num.toNat by
    exact_mod_cast Eq.symm <| Int.toNat_of_nonneg <| Rat.num_nonneg.mpr hq]; ring⟩

/-- Even Taylor truncation is an upper bound on `exp(-t)` for `t ≥ 0`. -/
lemma exp_neg_le_expNegUpper (t : ℚ) (ht : 0 ≤ t) (n : ℕ) :
    Real.exp (-(t : ℝ)) ≤ (expNegUpper t n : ℝ) := by
  have h_taylor : Real.exp (-t) =
      ∑ k ∈ Finset.range (2 * n + 1), (-t : ℝ)^k / (k.factorial : ℝ) +
      (-1)^(2 * n + 1) * ∫ x in (0 : ℝ)..t,
        (t - x)^(2 * n) / (2 * n)! * Real.exp (-x) := by
    induction' 2 * n with n ih <;>
      simp_all +decide [pow_succ, Finset.sum_range_succ]
    have h_parts : ∀ a b : ℝ, ∫ x in a..b, (t - x) ^ (n + 1) / (n + 1)! * Real.exp (-x) = (t - b) ^ (n + 1) / (n + 1)! * (-Real.exp (-b)) - (t - a) ^ (n + 1) / (n + 1)! * (-Real.exp (-a)) - ∫ x in a..b, (t - x) ^ n / n ! * (-Real.exp (-x)) * (-1) := by
      intro a b; rw [ intervalIntegral.integral_mul_deriv_eq_deriv_mul ];
      rotate_left;
      exact fun x _ => HasDerivAt.div_const ( HasDerivAt.comp x ( hasDerivAt_pow _ _ ) ( hasDerivAt_id' x |> HasDerivAt.const_sub _ ) ) _;
      exact fun x _ => by simpa using HasDerivAt.neg ( HasDerivAt.exp ( hasDerivAt_neg x ) );
      · exact Continuous.intervalIntegrable ( by continuity ) _ _;
      · exact Continuous.intervalIntegrable ( by continuity ) _ _;
      · norm_num [ Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
        exact Or.inl <| by rw [ ← mul_assoc, mul_inv_cancel₀ <| by positivity, one_mul ] ;
    simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_succ, Nat.factorial_succ ]; ring;
  unfold expNegUpper; norm_num [h_taylor]
  exact intervalIntegral.integral_nonneg (by positivity) fun x hx =>
    mul_nonneg (div_nonneg (pow_mul (t - x) 2 n ▸ by positivity) (by positivity))
      (Real.exp_nonneg _)

/-- Odd Taylor truncation is a lower bound on `exp(-t)` for `t ≥ 0`. -/
lemma expNegLower_le_exp_neg (t : ℚ) (ht : 0 ≤ t) (n : ℕ) :
    (expNegLower t n : ℝ) ≤ Real.exp (-(t : ℝ)) := by
  have h_remainder : ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      Real.exp (-t) ≥ ∑ k ∈ Finset.range (2 * n + 2), (-t) ^ k / (k.factorial : ℝ) := by
    intros n t ht
    have h_rem : Real.exp (-t) -
        ∑ k ∈ Finset.range (2 * n + 2), (-t) ^ k / (k.factorial : ℝ) =
        (-1) ^ (2 * n + 2) * ∫ u in (0 : ℝ)..t,
          (t - u) ^ (2 * n + 1) / (2 * n + 1)! * Real.exp (-u) := by
      have h_gen : ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
          Real.exp (-t) - ∑ k ∈ Finset.range (n + 1), (-t) ^ k / (k.factorial : ℝ) =
          (-1) ^ (n + 1) * ∫ u in (0 : ℝ)..t,
            (t - u) ^ n / (n.factorial : ℝ) * Real.exp (-u) := by
        intros n t ht
        induction' n with n ih generalizing t <;>
          simp_all +decide [Finset.sum_range_succ, pow_succ']
        have h_parts : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∫ u in a..b, (t - u) ^ (n + 1) / (n + 1)! * Real.exp (-u) = - (t - b) ^ (n + 1) / (n + 1)! * Real.exp (-b) + (t - a) ^ (n + 1) / (n + 1)! * Real.exp (-a) - ∫ u in a..b, (t - u) ^ n / (n ! : ℝ) * Real.exp (-u) := by
          intros a b ha hb;
          rw [ intervalIntegral.integral_mul_deriv_eq_deriv_mul ];
          any_goals intro x hx; exact HasDerivAt.div_const ( HasDerivAt.comp x ( hasDerivAt_pow ( n + 1 ) _ ) ( hasDerivAt_id' x |> HasDerivAt.const_sub _ ) ) _;
          rotate_right;
          use fun x => -Real.exp ( -x );
          · norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Nat.factorial_succ ];
            norm_num [ Nat.cast_add_one_ne_zero ];
          · exact fun x hx => by simpa using HasDerivAt.neg ( HasDerivAt.exp ( hasDerivAt_neg x ) ) ;
          · exact Continuous.intervalIntegrable ( by continuity ) _ _;
          · exact Continuous.intervalIntegrable ( by continuity ) _ _;
        simp_all +decide [ ← pow_succ', mul_assoc, div_eq_mul_inv ];
        linear_combination' ih t ht
      exact h_gen _ _ ht
    simp_all +decide [pow_succ']
    exact le_of_sub_nonneg (h_rem.symm ▸ intervalIntegral.integral_nonneg (by positivity)
      fun u hu => mul_nonneg
        (div_nonneg (mul_nonneg (sub_nonneg.2 hu.2) (pow_nonneg (sub_nonneg.2 hu.2) _))
          (by positivity))
        (Real.exp_nonneg _))
  exact le_trans
    (by norm_num [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat, expNegLower])
    (h_remainder n t (mod_cast ht))

lemma HFunc_nonneg (x : ℝ) : 0 ≤ HFunc x :=
  Finset.prod_nonneg fun _p hp => inv_nonneg.2 <| sub_nonneg.2 <|
    div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2

/-- Pointwise tail bound: `integrandF(x) ≤ exp(-x/2)·√(C₀·x)` for `x ≥ 9/2`. -/
lemma integrandF_le_tail (x : ℝ) (hx : 9/2 ≤ x) :
    integrandF x ≤ Real.exp (-x/2) * Real.sqrt ((891 * 162 : ℝ)/(250 * 161) * x) := by
  rw [ integrandF ];
  refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| show ( HFunc x : ℝ ) ≤ 891 * 162 / ( 250 * 161 ) * x from _ ) <| by positivity );
  · suffices h_simp : Real.sqrt (HFunc x * (Real.exp x - Real.exp (-x))) ≤ Real.sqrt (HFunc x) * Real.exp (x / 2) by
      convert mul_le_mul_of_nonneg_left h_simp ( Real.exp_nonneg ( -x ) ) using 1 ; rw [ show -x / 2 = -x + x / 2 by ring ] ; rw [ Real.exp_add ] ; ring;
    rw [ Real.sqrt_mul ( HFunc_nonneg x ) ];
    exact mul_le_mul_of_nonneg_left ( Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ ← Real.exp_nat_mul ] ; ring_nf; norm_num; linarith [ Real.exp_pos ( -x ), Real.exp_pos x ] ⟩ ) ( Real.sqrt_nonneg _ );
  · nontriviality;
    unfold HFunc;
    have := RosserSchoenfeld ( Real.exp ( 2 * x ) ) ?_;
    · rw [ Finset.prod_inv_distrib ];
      refine' le_trans ( inv_anti₀ _ this.le ) _;
      · norm_num;
        exact mul_pos ( div_pos ( Real.exp_pos _ ) ( by positivity ) ) ( sub_pos_of_lt ( by nlinarith [ inv_mul_cancel₀ ( by positivity : ( 2 * x ) ^ 2 ≠ 0 ) ] ) );
      · norm_num [ Real.exp_neg ];
        rw [ inv_mul_eq_div, div_le_iff₀ ] <;> ring_nf <;> norm_num;
        · have := two_exp_gamma_lt;
          nlinarith [ inv_mul_cancel₀ ( by positivity : ( x ^ 2 ) ≠ 0 ), pow_two_nonneg ( x - 9 / 2 ) ];
        · rw [ inv_mul_lt_iff₀ ] <;> nlinarith
    · have h_exp : Real.exp (2 * x) ≥ Real.exp 9 := Real.exp_le_exp.mpr ( by linarith );
      exact le_trans ( by have := Real.exp_one_gt_d9.le; norm_num1 at *; rw [ show Real.exp 9 = ( Real.exp 1 ) ^ 9 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ ) ) h_exp

-- =====================================================================
/-! ## §6. Integration formulas -/
-- =====================================================================

/-- Rewrite `integrandF` in factored form for `x ≥ 0`. -/
lemma integrandF_eq_rewrite (x : ℝ) (hx : 0 ≤ x) :
    integrandF x =
      Real.exp (-x/2) * Real.sqrt (HFunc x) * Real.sqrt (1 - Real.exp (-2*x)) := by
  unfold integrandF HFunc
  rw [Real.sqrt_mul']
  · rw [show (Real.exp x - Real.exp (-x)) = Real.exp x * (1 - Real.exp (-2 * x)) by
      rw [mul_sub, ← Real.exp_add]; ring_nf]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.exp_mul]; ring_nf
    norm_num [mul_assoc, mul_comm, mul_left_comm, ← Real.exp_add]
    rw [← mul_assoc, ← Real.exp_add]; ring_nf
  · exact sub_nonneg_of_le <| Real.exp_le_exp.mpr <| by linarith

/-- Taylor bound on the integrand for `x ≥ 0`. -/
lemma integrandF_le_taylor_bound (x : ℝ) (hx : 0 ≤ x) :
    integrandF x ≤
      Real.exp (-x/2) * Real.sqrt (HFunc x) *
        sqrtTaylorEval 100 (Real.exp (-2*x)) := by
  rw [integrandF_eq_rewrite x hx]
  exact mul_le_mul_of_nonneg_left
    (sqrt_one_sub_le_taylor100 _ (by positivity) (by norm_num; positivity))
    (by positivity)

/-- Integration formula for `∫_a^b exp(-x/2) · P₁₀₀(exp(-2x)) dx`. -/
lemma integral_exp_taylor_poly (a b : ℝ) :
    ∫ x in a..b,
      Real.exp (-x / 2) * sqrtTaylorEval 100 (Real.exp (-2 * x)) =
    (Finset.range 101).sum (fun k =>
      (sqrtCoeffQ k : ℝ) * (2 / (4 * ↑k + 1)) *
      (Real.exp (-(4 * ↑k + 1) * a / 2) -
       Real.exp (-(4 * ↑k + 1) * b / 2))) := by
  have h_expand : ∀ x : ℝ,
      Real.exp (-x / 2) * sqrtTaylorEval 100 (Real.exp (-2 * x)) =
      ∑ k ∈ Finset.range 101,
        (sqrtCoeffQ k : ℝ) * Real.exp (-(↑(4 * k + 1 : ℕ) / 2) * x) := by
    unfold sqrtTaylorEval
    norm_num [Finset.mul_sum _ _ _, mul_assoc, mul_left_comm,
      ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf; norm_num
  rw [intervalIntegral.integral_congr fun x _ => h_expand x,
    intervalIntegral.integral_finset_sum]
  · refine' Finset.sum_congr rfl fun i hi => _
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left] <;> norm_num; ring_nf; linarith
  · exact fun _ _ => Continuous.intervalIntegrable (by continuity) _ _

-- =====================================================================
/-! ## §7. Finite part: definitions and computational verification

The interval `[0, 9/2]` is partitioned into 1020 subintervals keyed on
primes up to 8103. On each subinterval, `HFunc` is piecewise constant
(equal to a cumulative product of `p/(p-1)` over primes), and the integral
of the Taylor-bounded integrand is evaluated in rational arithmetic. -/
-- =====================================================================

/-- Primes up to 8103. -/
def primesUpTo8103 : List ℕ :=
  (List.range 8104).filter (fun n => n ≥ 2 && Nat.Prime n)

/-- Taylor coefficients for `√(1-y)`, imperative version. -/
def sqrtTaylorCoeffs (m : ℕ) : Array ℚ := Id.run do
  let mut result : Array ℚ := #[(1 : ℚ)]
  for k in [:m] do
    let ck := result[result.size - 1]!
    result := result.push (ck * ((2 * (k : ℚ)) - 1) / (2 * (k : ℚ) + 2))
  return result

/-- Integral coefficients `a_k = 2·c_k/(4k+1)`. -/
def integralCoeffs (m : ℕ) : Array ℚ :=
  (sqrtTaylorCoeffs m).mapIdx (fun k c => 2 * c / (4 * (k : ℚ) + 1))

/-- Cumulative products `R_j = ∏_{p ≤ p_j} p/(p-1)`. -/
def cumulativeProducts : Array ℚ := Id.run do
  let primes := primesUpTo8103
  let mut result : Array ℚ := #[(1 : ℚ)]
  for p in primes do
    let prev := result[result.size - 1]!
    result := result.push (prev * (p : ℚ) / ((p : ℚ) - 1))
  return result

/-- Integer 4th-root bound. -/
def fourthRootBound (p S : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (S * S * S * S / p))

/-- Upper bound on `∫₀^{9/2} integrandF(x) dx`. -/
def computeSFin : ℚ := Id.run do
  let primes := primesUpTo8103
  let N := primes.length
  let m := 100
  let B : ℕ := 10 ^ 12
  let S : ℕ := 10 ^ 10
  let nT := 20
  let ac := integralCoeffs m
  let Rj := cumulativeProducts
  let Vj : Array ℚ := Rj.map (fun r =>
    let numQ := r.num.toNat * S * S
    let denQ := r.den
    let scaled := (numQ + denQ - 1) / denQ
    let sqrtScaled := Nat.sqrt scaled + 1
    (sqrtScaled : ℚ) / S)
  let el9 := expNegLower 9 nT
  let eu9 := expNegUpper 9 nT
  let el94 := expNegLower (9 / 4) nT
  let eu94 := expNegUpper (9 / 4) nT
  let mut totalSum : ℚ := 0
  for j in [:N + 1] do
    let (sj_lo, sj_hi) : ℚ × ℚ :=
      if j == 0 then (1, 1)
      else
        let p := primes[j - 1]!
        let b := fourthRootBound p S
        ((b : ℚ) / S, ((b + 1 : ℕ) : ℚ) / S)
    let (sj1_lo, sj1_hi) : ℚ × ℚ :=
      if j < N then
        let p := primes[j]!
        let b := fourthRootBound p S
        ((b : ℚ) / S, ((b + 1 : ℕ) : ℚ) / S)
      else (el94, eu94)
    let mut Tj : ℚ := 0
    for k in [:m + 1] do
      let ak := ac[k]!
      let (sj_pow_lo, sj_pow_hi) : ℚ × ℚ :=
        if j == 0 then (1, 1)
        else
          let p := primes[j - 1]!
          (sj_lo / (p : ℚ) ^ k, sj_hi / (p : ℚ) ^ k)
      let (sj1_pow_lo, sj1_pow_hi) : ℚ × ℚ :=
        if j < N then
          let p := primes[j]!
          (sj1_lo / (p : ℚ) ^ k, sj1_hi / (p : ℚ) ^ k)
        else
          (el94 * el9 ^ k, eu94 * eu9 ^ k)
      let delta_plus : ℚ :=
        if k == 0 then sj_pow_hi - sj1_pow_lo
        else sj_pow_lo - sj1_pow_hi
      Tj := Tj + ak * delta_plus
    totalSum := totalSum + ceilBQ B (Vj[j]! * Tj)
  return totalSum

/-- Per-interval bound matching the `j`-th term of `computeSFin`. -/
def intervalBoundQ (j : ℕ) : ℚ := Id.run do
  let primes := primesUpTo8103
  let N := primes.length
  let m := 100
  let B : ℕ := 10 ^ 12
  let S : ℕ := 10 ^ 10
  let nT := 20
  let ac := integralCoeffs m
  let Rj := cumulativeProducts
  let V :=
    let r := Rj[j]!
    let numQ := r.num.toNat * S * S
    let denQ := r.den
    let scaled := (numQ + denQ - 1) / denQ
    let sqrtScaled := Nat.sqrt scaled + 1
    (sqrtScaled : ℚ) / S
  let el9 := expNegLower 9 nT
  let eu9 := expNegUpper 9 nT
  let el94 := expNegLower (9 / 4) nT
  let eu94 := expNegUpper (9 / 4) nT
  let (sj_lo, sj_hi) : ℚ × ℚ :=
    if j == 0 then (1, 1)
    else
      let p := primes[j - 1]!
      let b := fourthRootBound p S
      ((b : ℚ) / S, ((b + 1 : ℕ) : ℚ) / S)
  let (sj1_lo, sj1_hi) : ℚ × ℚ :=
    if j < N then
      let p := primes[j]!
      let b := fourthRootBound p S
      ((b : ℚ) / S, ((b + 1 : ℕ) : ℚ) / S)
    else (el94, eu94)
  let mut Tj : ℚ := 0
  for k in [:m + 1] do
    let ak := ac[k]!
    let (sj_pow_lo, sj_pow_hi) : ℚ × ℚ :=
      if j == 0 then (1, 1)
      else
        let p := primes[j - 1]!
        (sj_lo / (p : ℚ) ^ k, sj_hi / (p : ℚ) ^ k)
    let (sj1_pow_lo, sj1_pow_hi) : ℚ × ℚ :=
      if j < N then
        let p := primes[j]!
        (sj1_lo / (p : ℚ) ^ k, sj1_hi / (p : ℚ) ^ k)
      else
        (el94 * el9 ^ k, eu94 * eu9 ^ k)
    let delta_plus : ℚ :=
      if k == 0 then sj_pow_hi - sj1_pow_lo
      else sj_pow_lo - sj1_pow_hi
    Tj := Tj + ak * delta_plus
  return ceilBQ B (V * Tj)

/-- Finset-based prime product for computational verification. -/
def finsetPrimeProd (n : ℕ) : ℚ :=
  ((Finset.range (n + 1)).filter Nat.Prime).prod
    (fun p => (p : ℚ) / ((p : ℚ) - 1))

/-- Partition points: `partPt(0)=0`, `partPt(j)=log(p_j)/2`, `partPt(1020)=9/2`. -/
noncomputable def partPt (j : ℕ) : ℝ :=
  if j = 0 then 0
  else if j ≤ 1019 then
    Real.log (primesUpTo8103[j - 1]! : ℝ) / 2
  else 9 / 2

/-- Rational lower bound on `exp(-(4k+1)·partPt(j)/2)`. -/
def expLoBound (j k : ℕ) : ℚ :=
  if j = 0 then 1
  else if j ≤ 1019 then
    let p := primesUpTo8103[j-1]!
    (fourthRootBound p (10^10) : ℚ) / ((10^10 : ℚ) * (p : ℚ)^k)
  else
    expNegLower (9/4) 20 * (expNegLower 9 20)^k

/-- Rational upper bound on `exp(-(4k+1)·partPt(j)/2)`. -/
def expHiBound (j k : ℕ) : ℚ :=
  if j = 0 then 1
  else if j ≤ 1019 then
    let p := primesUpTo8103[j-1]!
    ((fourthRootBound p (10^10) + 1 : ℕ) : ℚ) / ((10^10 : ℚ) * (p : ℚ)^k)
  else
    expNegUpper (9/4) 20 * (expNegUpper 9 20)^k

/-- Lower incomplete gamma series partial sum. -/
def gammaSeriesPartialSum (nTerms : ℕ) : ℚ :=
  let x : ℚ := 9/4
  (27 : ℚ) / 8 * (Finset.range nTerms).sum (fun k =>
    (-x) ^ k / ((k.factorial : ℚ) * ((3 : ℚ) / 2 + k)))

/-- Tail bound via incomplete gamma function. -/
def tailBoundGamma : ℚ :=
  let S : ℕ := 10^10
  let C₀ : ℚ := (891 * 162 : ℚ) / (250 * 161)
  let sqrtC₀ := sqrtUpperQ C₀ S
  let sqrt2 := sqrtUpperQ 2 S
  let piUpper : ℚ := 3141593 / 1000000
  let sqrtPiUpper := sqrtUpperQ piUpper S
  let gammaLower := gammaSeriesPartialSum 12
  let GammaUpper := sqrtPiUpper / 2 - gammaLower
  sqrtC₀ * 2 * sqrt2 * GammaUpper

noncomputable def C0 : ℝ := (891 * 162 : ℝ) / (250 * 161)

/-- Overall bound: `computeSFin + tailBoundGamma`. -/
def overallBoundGamma : ℚ := computeSFin + tailBoundGamma

-- =====================================================================
/-! ## §7a. Computational verifications -/
-- =====================================================================

lemma numPrimes_val : primesUpTo8103.length = 1019 := by native_decide
lemma primeList_pairwise : primesUpTo8103.Pairwise (· < ·) := by native_decide

lemma primeList_mem_prime {p : ℕ} (hp : p ∈ primesUpTo8103) : Nat.Prime p := by
  unfold primesUpTo8103 at hp
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact hp.2.2

lemma primeList_mem_le {p : ℕ} (hp : p ∈ primesUpTo8103) : p ≤ 8103 := by
  unfold primesUpTo8103 at hp
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hp
  omega

lemma getElemBang_mem (i : ℕ) (hi : i < 1019) :
    primesUpTo8103[i]! ∈ primesUpTo8103 := by
  have : ∀ i < 1019, primesUpTo8103[i]! ∈ primesUpTo8103 := by native_decide
  exact this i hi

lemma intervalBoundQ_sum_eq :
    (List.range 1020).foldl (fun acc j => acc + intervalBoundQ j) 0 = computeSFin := by
  native_decide

lemma cumProd_eq_finset :
    ∀ j, j < 1020 →
      finsetPrimeProd (if j = 0 then 1 else primesUpTo8103[j-1]!) =
        cumulativeProducts[j]! := by
  native_decide

lemma no_prime_between_consecutive (j : ℕ) (hj : j + 1 < 1019)
    (k : ℕ) (hk1 : primesUpTo8103[j]! < k) (hk2 : k < primesUpTo8103[j + 1]!) :
    ¬ Nat.Prime k := by
  have : ∀ j < 1018, ∀ n ∈ Finset.Ioo (primesUpTo8103[j]!) (primesUpTo8103[j + 1]!),
      ¬Nat.Prime n := by native_decide
  exact this j (by omega) k (Finset.mem_Ioo.mpr ⟨hk1, hk2⟩)

lemma integralCoeffs_eq : ∀ k, k ≤ 100 →
    (integralCoeffs 100)[k]! = sqrtCoeffQ k * 2 / (4 * (k : ℚ) + 1) := by
  native_decide

lemma overall_bound_gamma_check : overallBoundGamma < (9263 : ℚ) / 2000 := by
  native_decide

-- =====================================================================
/-! ## §8. Finite part: analytical bounds

This section proves `∫₀^{9/2} integrandF ≤ computeSFin` by:
1. Splitting `[0, 9/2]` into 1020 subintervals via `partPt`.
2. Bounding `HFunc` on each subinterval by a rational cumulative product.
3. Bounding each sub-integral analytically, then rationally.
4. Summing and verifying the sum equals `computeSFin`. -/
-- =====================================================================

lemma partPt_zero : partPt 0 = 0 := by simp [partPt]
lemma partPt_1020 : partPt 1020 = 9 / 2 := by simp [partPt]

lemma partPt_nonneg (j : ℕ) (hj : j ≤ 1020) : 0 ≤ partPt j := by
  by_cases hj' : j = 0
  · aesop
  · unfold partPt; split_ifs
    · exact div_nonneg (Real.log_nonneg (mod_cast Nat.Prime.pos
        (primeList_mem_prime (getElemBang_mem (j - 1) (by omega))))) zero_le_two
    · norm_num

set_option maxRecDepth 16000 in
lemma partPt_mono {i j : ℕ} (hi : i ≤ 1020) (hj : j ≤ 1020) (hij : i ≤ j) :
    partPt i ≤ partPt j := by
  by_cases hi0 : i = 0
  · exact hi0.symm ▸ partPt_nonneg j hj
  · by_cases hj0 : j = 0
    · aesop
    · by_cases hi1 : i ≤ 1019 <;> by_cases hj1 : j ≤ 1019 <;>
        simp_all +decide only [partPt]
      · have h_log_mono : primesUpTo8103[i - 1]! ≤ primesUpTo8103[j - 1]! := by
          have h_prime_mono : ∀ {i j : ℕ}, i < j → i < primesUpTo8103.length →
              j < primesUpTo8103.length →
              primesUpTo8103[i]! < primesUpTo8103[j]! := by
            intros i j hij hi hj
            have := List.pairwise_iff_get.mp primeList_pairwise
            specialize this ⟨i, hi⟩ ⟨j, hj⟩ hij; aesop
          by_cases hij' : i - 1 < j - 1
          · exact le_of_lt (h_prime_mono hij'
              (by rw [numPrimes_val]; omega) (by rw [numPrimes_val]; omega))
          · grind
        exact div_le_div_of_nonneg_right
          (Real.log_le_log (Nat.cast_pos.mpr <| Nat.Prime.pos <|
            primeList_mem_prime <| getElemBang_mem _ <| by omega) <|
            Nat.cast_le.mpr h_log_mono)
          zero_le_two
      · have h_log_bound : Real.log (primesUpTo8103[i - 1]! : ℝ) ≤ 9 := by
          rw [Real.log_le_iff_le_exp]
          · have h_exp : Real.exp 9 > 8103 := by
              have := Real.exp_one_gt_d9.le; norm_num at *
              rw [show Real.exp 9 = (Real.exp 1) ^ 9 by rw [← Real.exp_nat_mul]; norm_num]
              exact lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by positivity) this _)
            exact le_trans (Nat.cast_le.mpr (primeList_mem_le
              (getElemBang_mem _ (by omega)))) h_exp.le
          · exact Nat.cast_pos.mpr (Nat.Prime.pos (primeList_mem_prime
              (getElemBang_mem _ (by omega))))
        grind +revert
      · omega
      · grind

/-- `HFunc` is monotone. -/
lemma HFunc_mono : Monotone HFunc := by
  intros x y hxy
  have h_floor : ⌊Real.exp (2 * x)⌋₊ ≤ ⌊Real.exp (2 * y)⌋₊ :=
    Nat.floor_mono <| Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_left hxy zero_le_two
  unfold HFunc
  rw [← Finset.prod_sdiff <| Finset.filter_subset_filter _ <|
    Finset.range_mono <| Nat.succ_le_succ h_floor]
  refine' le_mul_of_one_le_left
    (Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <|
      div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop) _
  exact le_trans (by norm_num) (Finset.prod_le_prod (fun _ _ => by positivity) fun p hp =>
    inv_anti₀ (sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <|
      Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by aesop) <|
      sub_le_self _ <| by positivity)

/-- `integrandF` is interval-integrable on any bounded interval. -/
lemma integrandF_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable integrandF volume a b := by
  apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ]
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun x => Real.exp ( -x ) * Real.sqrt ( HFunc ( Max.max a b ) ) * Real.sqrt ( Real.exp x - Real.exp ( -x ) );
  · exact Continuous.integrableOn_Icc ( by continuity );
  · have h_meas : Measurable HFunc := by
      apply_rules [ Monotone.measurable, HFunc_mono ];
    exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.continuous_exp.measurable.comp ( measurable_neg ) ) ( Real.continuous_sqrt.measurable.comp ( h_meas.mul ( Real.continuous_exp.measurable.sub ( Real.continuous_exp.measurable.comp ( measurable_neg ) ) ) ) ) );
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx;
    rw [ Real.norm_of_nonneg ( integrandF_nonneg x ) ];
    unfold integrandF;
    rw [ mul_assoc, Real.sqrt_mul ( HFunc_nonneg _ ) ];
    exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_right ( Real.sqrt_le_sqrt <| HFunc_mono <| by cases max_cases a b <;> cases Set.mem_uIcc.mp hx <;> linarith ) <| Real.sqrt_nonneg _ ) <| Real.exp_nonneg _

/-- A.e. interval bound: if `HFunc ≤ R` a.e. on `[a,b]`, bound the integral. -/
lemma integrandF_interval_le_ae (a b : ℝ) (R : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hH : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), HFunc x ≤ R) :
    ∫ x in Set.Icc a b, integrandF x ≤
      Real.sqrt R * (Finset.range 101).sum (fun k =>
        (sqrtCoeffQ k : ℝ) * (2 / (4 * ↑k + 1)) *
        (Real.exp (-(4 * ↑k + 1) * a / 2) -
         Real.exp (-(4 * ↑k + 1) * b / 2))) := by
  by_cases hR : 0 ≤ R
  · refine' le_trans (MeasureTheory.integral_mono_of_nonneg _ _ _) _
    refine' fun x => Real.exp (-x / 2) * Real.sqrt R *
      sqrtTaylorEval 100 (Real.exp (-2 * x))
    · exact Filter.Eventually.of_forall fun x => integrandF_nonneg x
    · refine' Continuous.integrableOn_Icc _
      unfold sqrtTaylorEval; fun_prop
    · filter_upwards [hH, MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx₁ hx₂
      refine' le_trans _ (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx₁) (Real.exp_nonneg _)) _)
      · convert integrandF_le_taylor_bound x (by linarith [hx₂.1]) using 1
      · apply sqrtTaylor100_nonneg; exact Real.exp_nonneg _
        exact Real.exp_le_one_iff.mpr (by linarith [hx₂.1, hx₂.2])
    · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab]
      rw [intervalIntegral.integral_congr fun x hx => by
        rw [show Real.exp (-x / 2) * Real.sqrt R *
          sqrtTaylorEval 100 (Real.exp (-2 * x)) =
          Real.sqrt R * (Real.exp (-x / 2) *
            sqrtTaylorEval 100 (Real.exp (-2 * x))) by ring]]
      rw [intervalIntegral.integral_const_mul, integral_exp_taylor_poly]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hR)]; norm_num
    rw [MeasureTheory.integral_eq_zero_of_ae]
    filter_upwards [hH] with x hx using
      le_antisymm (le_trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
        (Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [HFunc_nonneg x]⟩))
        (by norm_num))
        (integrandF_nonneg x)


lemma floor_exp_lt_nat (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : x < Real.log n / 2) :
    ⌊Real.exp (2 * x)⌋₊ < n := by
  rw [Nat.floor_lt]
  · rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_exp]; linarith
  · positivity

lemma finsetPrimeProd_eq_real (n : ℕ) :
    (finsetPrimeProd n : ℝ) =
      ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
  unfold finsetPrimeProd
  push_cast [Finset.prod_div_distrib]
  rw [← Finset.prod_div_distrib, Finset.prod_congr rfl]
  intros; rw [one_sub_div] <;> aesop

lemma nat_le_floor_exp_ge (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : Real.log n / 2 ≤ x) :
    n ≤ ⌊Real.exp (2 * x)⌋₊ :=
  Nat.le_floor <| by rw [← Real.log_le_iff_le_exp (by positivity)]; linarith

lemma filter_prime_stable (j : ℕ) (hj : j < 1020) (n : ℕ)
    (hn_lo : (if j = 0 then 1 else primesUpTo8103[j-1]!) ≤ n)
    (hn_hi : n < (if j < 1019 then primesUpTo8103[j]! else 8104)) :
    (Finset.range (n + 1)).filter Nat.Prime =
      (Finset.range ((if j = 0 then 1 else primesUpTo8103[j-1]!) + 1)).filter Nat.Prime := by
  split_ifs at * <;> norm_num at *
  · subst_vars; norm_num [primesUpTo8103] at *
    rw [show (List.filter (fun n => decide (2 ≤ n) && decide (Nat.Prime n))
      (List.range 8104))[0]?.getD 0 = 2 by native_decide] at hn_hi
    interval_cases n; native_decide
  · grind
  · have h_no_prime : ∀ k, primesUpTo8103[j - 1]?.getD 0 < k →
        k < primesUpTo8103[j]?.getD 0 → ¬Nat.Prime k := by
      intros k hk₁ hk₂ hk₃
      convert no_prime_between_consecutive (j - 1) (by omega) k _ _ hk₃
      · aesop
      · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero ‹_›)]; aesop
    grind
  · norm_num [show j = 1019 by linarith] at *
    rw [show primesUpTo8103[1018]?.getD 0 = 8101 by native_decide] at *
    interval_cases n <;> native_decide

/-- `HFunc` is bounded by the cumulative product on each partition interval. -/
lemma HFunc_le_on_interval (j : ℕ) (hj : j < 1020) (x : ℝ)
    (hx_lo : partPt j ≤ x) (hx_hi : x < partPt (j + 1)) :
    HFunc x ≤ (cumulativeProducts[j]! : ℝ) := by
  set m₀ := if j = 0 then 1 else primesUpTo8103[j-1]!
  have h_lo : m₀ ≤ ⌊Real.exp (2 * x)⌋₊ := by
    by_cases hj0 : j = 0
    · subst hj0; simp only [m₀, ite_true]
      apply Nat.le_floor; push_cast
      exact Real.one_le_exp (by linarith [partPt_nonneg 0 (by omega)])
    · simp only [m₀, hj0, ite_false]
      apply nat_le_floor_exp_ge
      · exact (primeList_mem_prime (getElemBang_mem _ (by omega))).two_le
      · have hp : partPt j = Real.log (primesUpTo8103[j-1]! : ℝ) / 2 := by
          simp only [partPt, hj0, ite_false, show j ≤ 1019 from by omega, ite_true]
        linarith
  have h_hi : ⌊Real.exp (2 * x)⌋₊ <
      (if j < 1019 then primesUpTo8103[j]! else 8104) := by
    by_cases hj1019 : j < 1019
    · simp only [hj1019, ite_true]
      apply floor_exp_lt_nat
      · exact (primeList_mem_prime (getElemBang_mem _ hj1019)).two_le
      · have hp : partPt (j + 1) = Real.log (primesUpTo8103[j]! : ℝ) / 2 := by
          simp only [partPt, show j + 1 ≠ 0 from by omega, ite_false,
            show j + 1 ≤ 1019 from by omega, ite_true, show j + 1 - 1 = j from by omega]
        linarith
    · simp only [hj1019, ite_false]
      have hj_eq : j = 1019 := by omega
      rw [Nat.floor_lt (by positivity)]
      have hp1020 : partPt (j + 1) = 9 / 2 := by subst hj_eq; exact partPt_1020
      calc Real.exp (2 * x) < Real.exp (2 * (9/2)) :=
            Real.exp_lt_exp.mpr (by linarith)
        _ = Real.exp 9 := by ring_nf
        _ < 8104 := by
          have h1 := Real.exp_one_lt_d9
          rw [show (9 : ℝ) = (9 : ℕ) * 1 from by norm_num, Real.exp_nat_mul]
          calc (Real.exp 1) ^ 9 < (2.7182818286 : ℝ) ^ 9 :=
                pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
            _ < 8104 := by norm_num
  have h_filter := filter_prime_stable j hj (⌊Real.exp (2 * x)⌋₊) h_lo h_hi
  unfold HFunc
  rw [h_filter, ← finsetPrimeProd_eq_real, cumProd_eq_finset j hj]

lemma interval_eq_Icc (j : ℕ) (hj : j < 1020) :
    ∫ x in partPt j..partPt (j + 1), integrandF x =
      ∫ x in Set.Icc (partPt j) (partPt (j + 1)), integrandF x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (partPt_mono (by omega) (by omega) (by omega))]

/-- Analytical bound on each subinterval. -/
lemma subinterval_analytical (j : ℕ) (hj : j < 1020) :
    ∫ x in Set.Icc (partPt j) (partPt (j + 1)), integrandF x ≤
      Real.sqrt (cumulativeProducts[j]! : ℝ) *
        (Finset.range 101).sum (fun k =>
          (sqrtCoeffQ k : ℝ) * (2 / (4 * ↑k + 1)) *
          (Real.exp (-(4 * ↑k + 1) * partPt j / 2) -
           Real.exp (-(4 * ↑k + 1) * partPt (j+1) / 2))) := by
  apply_rules [integrandF_interval_le_ae]
  · exact partPt_nonneg j (by linarith)
  · exact partPt_mono (by linarith) (by linarith) (by linarith)
  · rw [MeasureTheory.ae_restrict_iff']
    · filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
        (MeasureTheory.measure_singleton (partPt (j + 1)))] with x hx
      exact fun hx' => HFunc_le_on_interval j hj x hx'.1
        (lt_of_le_of_ne hx'.2 hx)
    · exact measurableSet_Icc

-- =====================================================================
/-! ## §8a. Fourth root and rational partition bounds -/
-- =====================================================================

lemma nat_double_sqrt_pow4_le (n : ℕ) : Nat.sqrt (Nat.sqrt n) ^ 4 ≤ n := by
  have h1 : Nat.sqrt (Nat.sqrt n) * Nat.sqrt (Nat.sqrt n) ≤ Nat.sqrt n := Nat.sqrt_le _
  have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le _
  nlinarith [sq_nonneg (Nat.sqrt (Nat.sqrt n))]

lemma fourthRootBound_div_le_exp (p S : ℕ) (hp : 1 < p) (hS : 0 < S) :
    (fourthRootBound p S : ℝ) / S ≤ Real.exp (-Real.log p / 4) := by
  have h4 : ((fourthRootBound p S : ℝ) / S) ^ 4 ≤ 1 / p := by
    have h4 : ((fourthRootBound p S : ℝ) ^ 4) ≤ (S ^ 4 : ℝ) / p := by
      rw [le_div_iff₀] <;> norm_cast
      · convert Nat.mul_le_mul_right p
            (nat_double_sqrt_pow4_le (S * S * S * S / p)) |> le_trans <|
          Nat.div_mul_le_self _ _ using 1; ring
      · positivity
    rw [div_pow, div_le_iff₀] <;> first | positivity | ring_nf at *; aesop
  convert Real.rpow_le_rpow (by positivity) h4
    (show (1 / 4 : ℝ) ≥ 0 by positivity) using 1 <;>
    norm_num [Real.exp_neg, Real.exp_log (by positivity : 0 < (p : ℝ))]
  · rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity)]; norm_num
  · rw [Real.rpow_def_of_pos (by positivity), Real.log_inv]; ring_nf

lemma exp_lt_fourthRootBound_succ_div (p S : ℕ) (hp : 1 < p) (hS : 0 < S) :
    Real.exp (-Real.log p / 4) < ((fourthRootBound p S + 1 : ℕ) : ℝ) / S := by
  have h_exp_inv : Real.exp (-Real.log p / 4) ^ 4 <
      ((fourthRootBound p S + 1 : ℝ) / S) ^ 4 := by
    rw [← Real.exp_nat_mul]; ring_nf; norm_num [Real.exp_neg, Real.exp_log, hp, hS]
    field_simp; rw [Real.exp_log (by positivity)]; norm_cast
    unfold fourthRootBound; ring_nf
    have := Nat.lt_succ_sqrt (Nat.sqrt (S ^ 4 / p))
    have := Nat.lt_succ_sqrt (S ^ 4 / p)
    rw [Nat.sqrt_lt] at *
    nlinarith [Nat.div_add_mod (S ^ 4) p, Nat.mod_lt (S ^ 4) hp.le]
  exact lt_of_pow_lt_pow_left₀ _ (by positivity) (h_exp_inv.trans_eq (by push_cast; ring))

lemma exp_partPt_lower_interior (j k : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 1019) :
    let p := primesUpTo8103[j - 1]!
    let S : ℕ := 10 ^ 10
    (fourthRootBound p S : ℝ) / ((S : ℝ) * (p : ℝ) ^ k) ≤
      Real.exp (-(4 * ↑k + 1) * partPt j / 2) := by
  have := @getElemBang_mem
  specialize this (j - 1) (by omega)
  unfold partPt; split_ifs
  · grind
  · convert mul_le_mul_of_nonneg_right
      (fourthRootBound_div_le_exp (primesUpTo8103[j - 1]!) (10^10)
        (Nat.Prime.one_lt (primeList_mem_prime this)) (by norm_num))
      (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg (primesUpTo8103[j - 1]!))) k) using 1; ring
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos
      (inv_pos.mpr (Nat.cast_pos.mpr (Nat.Prime.pos (primeList_mem_prime this))))]; ring_nf
    rw [← Real.exp_add, Real.log_inv]; ring_nf

lemma exp_partPt_upper_interior (j k : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 1019) :
    let p := primesUpTo8103[j - 1]!
    let S : ℕ := 10 ^ 10
    Real.exp (-(4 * ↑k + 1) * partPt j / 2) ≤
      ((fourthRootBound p S + 1 : ℕ) : ℝ) / ((S : ℝ) * (p : ℝ) ^ k) := by
  have h_exp : Real.exp (-(4 * k + 1) * Real.log (primesUpTo8103[j - 1]!) / 4) <
      ((fourthRootBound (primesUpTo8103[j - 1]!) (10 ^ 10) + 1 : ℕ) : ℝ) /
        (10 ^ 10 * (primesUpTo8103[j - 1]! : ℝ) ^ k) := by
    have h : Real.exp (-Real.log (primesUpTo8103[j - 1]!) / 4) <
        ((fourthRootBound (primesUpTo8103[j - 1]!) (10 ^ 10) + 1 : ℕ) : ℝ) /
          (10 ^ 10 : ℝ) := by
      convert exp_lt_fourthRootBound_succ_div _ _ _ _ using 1 <;> norm_num
      convert rfl
      · native_decide +revert
      · norm_num
    convert mul_lt_mul_of_pos_right h
      (inv_pos.mpr (pow_pos (Nat.cast_pos.mpr (Nat.Prime.pos
        (primeList_mem_prime (getElemBang_mem (j - 1) (by omega))))) k)) using 1 <;> ring_nf
    rw [Real.exp_add, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log (Nat.cast_pos.mpr (Nat.Prime.pos
        (primeList_mem_prime (getElemBang_mem (j - 1) (by omega)))))]
    ring
  unfold partPt; grind

lemma exp_boundary_lower (k : ℕ) :
    (expNegLower (9/4) 20 : ℝ) * (expNegLower 9 20 : ℝ) ^ k ≤
      Real.exp (-(4 * ↑k + 1) * (9/2 : ℝ) / 2) := by
  convert mul_le_mul (expNegLower_le_exp_neg _ _ _)
    (pow_le_pow_left₀ (?_) (expNegLower_le_exp_neg _ _ _) _) (?_) (?_) using 1 <;> norm_num
  · rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  · native_decide +revert
  · exact pow_nonneg (mod_cast by native_decide) _
  · positivity

lemma exp_boundary_upper (k : ℕ) :
    Real.exp (-(4 * ↑k + 1) * (9/2 : ℝ) / 2) ≤
      (expNegUpper (9/4) 20 : ℝ) * (expNegUpper 9 20 : ℝ) ^ k := by
  convert mul_le_mul ?_ ?_ ?_ ?_ using 1
  convert Real.exp_add _ _ using 2; ring_nf
  rotate_left; exact -9 / 4; exact -9 * k
  all_goals try infer_instance
  · convert exp_neg_le_expNegUpper (9 / 4) (by norm_num) 20 using 1; norm_num
  · convert pow_le_pow_left₀ (by positivity) (exp_neg_le_expNegUpper 9 (by norm_num) 20) k
      using 1
    norm_num [← Real.exp_nat_mul]; ring
  · positivity
  · exact_mod_cast by native_decide
  · ring

/-- The Taylor polynomial sum is nonneg on `[a,b]` with `0 ≤ a ≤ b`. -/
lemma taylor_sum_nonneg (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ (Finset.range 101).sum (fun k =>
      (sqrtCoeffQ k : ℝ) * (2 / (4 * ↑k + 1)) *
      (Real.exp (-(4 * ↑k + 1) * a / 2) -
       Real.exp (-(4 * ↑k + 1) * b / 2))) := by
  rw [← integral_exp_taylor_poly a b]
  refine' intervalIntegral.integral_nonneg (by linarith) fun x hx =>
    mul_nonneg (Real.exp_nonneg _) (sqrtTaylor100_nonneg _ _ _)
  · positivity
  · exact Real.exp_le_one_iff.mpr (by linarith [hx.1])

lemma expLoBound_le (j k : ℕ) (hj : j ≤ 1020) :
    (expLoBound j k : ℝ) ≤ Real.exp (-(4 * ↑k + 1) * partPt j / 2) := by
  unfold expLoBound; split_ifs
  · unfold partPt; aesop
  · convert exp_partPt_lower_interior j k (Nat.pos_of_ne_zero ‹_›) ‹_› using 1
    convert Rat.cast_div _ _
    · norm_cast
    · infer_instance
  · norm_num [show j = 1020 by linarith] at *
    convert exp_boundary_lower k using 1; norm_num [partPt_1020]

lemma le_expHiBound (j k : ℕ) (hj : j ≤ 1020) :
    Real.exp (-(4 * ↑k + 1) * partPt j / 2) ≤ (expHiBound j k : ℝ) := by
  unfold expHiBound; split_ifs
  · unfold partPt; aesop
  · convert exp_partPt_upper_interior j k (Nat.pos_of_ne_zero ‹_›) ‹_› using 1
    push_cast; ring
  · norm_num [show j = 1020 by linarith] at *
    convert exp_boundary_upper k using 1; ring_nf
    rw [show partPt 1020 = 9 / 2 by rfl]; ring_nf

/-- The per-k analytical term ≤ the rational bound term. -/
lemma per_k_bound (j k : ℕ) (hj : j < 1020) (hk : k ≤ 100) :
    (sqrtCoeffQ k : ℝ) * (2 / (4 * ↑k + 1)) *
    (Real.exp (-(4 * ↑k + 1) * partPt j / 2) -
     Real.exp (-(4 * ↑k + 1) * partPt (j+1) / 2))
    ≤ ((integralCoeffs 100)[k]! : ℝ) *
      (if k = 0 then (expHiBound j 0 : ℝ) - (expLoBound (j+1) 0 : ℝ)
       else (expLoBound j k : ℝ) - (expHiBound (j+1) k : ℝ)) := by
  split_ifs
  · subst_vars; norm_num [integralCoeffs_eq]
    gcongr
    · norm_num [sqrtCoeffQ]
    · convert le_expHiBound j 0 (by linarith) using 1; ring_nf
    · convert expLoBound_le (j + 1) 0 (by linarith) using 1; ring_nf
  · rw [integralCoeffs_eq k hk]
    convert mul_le_mul_of_nonpos_left _ _ using 1
    any_goals try infer_instance
    rotate_left
    exact (expLoBound j k : ℝ) - (expHiBound (j + 1) k : ℝ)
    · gcongr
      · exact expLoBound_le j k (by linarith)
      · exact le_expHiBound _ _ (by linarith)
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mod_cast sqrtCoeffQ_nonpos k (Nat.pos_of_ne_zero ‹_›)) (by positivity)
    · norm_num [mul_div_assoc]

/-- Rational bound on each subinterval. -/
lemma subinterval_rational (j : ℕ) (hj : j < 1020) :
    Real.sqrt (cumulativeProducts[j]! : ℝ) *
      (Finset.range 101).sum (fun k =>
        (sqrtCoeffQ k : ℝ) * (2 / (4 * ↑k + 1)) *
        (Real.exp (-(4 * ↑k + 1) * partPt j / 2) -
         Real.exp (-(4 * ↑k + 1) * partPt (j+1) / 2)))
      ≤ (intervalBoundQ j : ℝ) := by
  refine' le_trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.mpr _) (_)) (_)
  exact (sqrtUpperQ (cumulativeProducts[j]!) (10^10) : ℝ)
  · have h := @sqrt_le_sqrtUpperQ
    convert h (cumulativeProducts[j]!) _ (10^10) (by norm_num) using 1
    · rw [Real.sqrt_le_iff]
    · native_decide +revert
  · convert taylor_sum_nonneg (partPt j) (partPt (j + 1))
      (partPt_nonneg j (by linarith))
      (partPt_mono (by linarith) (by linarith) (by linarith)) using 1
  · refine' le_trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun k hk => _) (_)) _
    use fun k => (integralCoeffs 100)[k]! *
      (if k = 0 then (expHiBound j 0 : ℝ) - (expLoBound (j + 1) 0 : ℝ)
       else (expLoBound j k : ℝ) - (expHiBound (j + 1) k : ℝ))
    · convert per_k_bound j k hj (Finset.mem_range_succ_iff.mp hk) using 1
    · unfold sqrtUpperQ; norm_num; positivity
    · have h_ceil : ∀ j < 1020, ceilBQ (10^12) (sqrtUpperQ (cumulativeProducts[j]!) (10^10) *
          (∑ k ∈ Finset.range 101, (integralCoeffs 100)[k]! *
            (if k = 0 then expHiBound j 0 - expLoBound (j + 1) 0
             else expLoBound j k - expHiBound (j + 1) k))) ≤
          intervalBoundQ j := by
        native_decide +revert
      refine' le_trans _ (Rat.cast_le.mpr (h_ceil j hj))
      convert Rat.cast_le.mpr (ceilBQ_le _ _ _) using 1
      · norm_num [Finset.sum_ite]
      · infer_instance
      · norm_num

lemma subinterval_bound (j : ℕ) (hj : j < 1020) :
    ∫ x in partPt j..partPt (j + 1), integrandF x ≤ (intervalBoundQ j : ℝ) := by
  rw [interval_eq_Icc j hj]
  exact le_trans (subinterval_analytical j hj) (subinterval_rational j hj)

/-- **Finite analytical bound**: `∫₀^{9/2} integrandF ≤ computeSFin`. -/
lemma finite_analytical_bound :
    ∫ x in Set.Icc (0 : ℝ) (9/2), integrandF x ≤ (computeSFin : ℝ) := by
  have h_sum : ∑ j ∈ Finset.range 1020,
      ∫ x in partPt j..partPt (j + 1), integrandF x ≤
      ∑ j ∈ Finset.range 1020, (intervalBoundQ j : ℝ) :=
    Finset.sum_le_sum fun i hi => subinterval_bound i <| Finset.mem_range.mp hi
  convert h_sum using 1
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le]
    · rw [intervalIntegral.sum_integral_adjacent_intervals]
      · rw [partPt_zero, partPt_1020]
      · exact fun k hk => integrandF_intervalIntegrable _ _
    · norm_num
  · rw [← intervalBoundQ_sum_eq]
    induction' 1020 with n ih <;> simp +decide [*, Finset.sum_range_succ]
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    norm_num [ih]

-- =====================================================================
/-! ## §9. Tail bound via incomplete gamma function

For `x ≥ 9/2`, using `H(x) ≤ C₀·x` (from Rosser–Schoenfeld and
`2·exp(γ) < 891/250`), we bound the tail integral by the upper
incomplete gamma function `Γ(3/2) - γ(3/2, 9/4)`. -/
-- =====================================================================

lemma C0_pos : (0 : ℝ) < C0 := by unfold C0; positivity

/-- `x ↦ e^{-x/2}·√(C₀·x)` is integrable on `[9/2, ∞)`. -/
lemma exp_sqrt_integrableOn :
    IntegrableOn (fun x => Real.exp (-x/2) * √(C0 * x)) (Ici (9/2 : ℝ)) := by
  have h_bound : ∀ x ∈ Ici (9/2 : ℝ),
      Real.exp (-x / 2) * √(C0 * x) ≤ √C0 * x * Real.exp (-x / 2) := by
    intro x hx; rw [mul_comm]; gcongr
    rw [Real.sqrt_mul (by exact div_nonneg (by norm_num) (by norm_num))]
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_iff.mpr ⟨by linarith [Set.mem_Ici.mp hx],
        by nlinarith [Set.mem_Ici.mp hx]⟩)
      (Real.sqrt_nonneg _)
  have h_int : IntegrableOn (fun x : ℝ => x * Real.exp (-x / 2)) (Ici (9/2)) := by
    have h : IntegrableOn (fun x => x * Real.exp (-x / 2)) (Ioi 0) := by
      have h_val : ∫ x in Ioi 0, x * Real.exp (-x / 2) = 4 := by
        have := @integral_rpow_mul_exp_neg_mul_rpow
        convert @this 1 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num) using 1 <;>
          norm_num [div_eq_mul_inv, mul_comm]
      exact (by contrapose! h_val; rw [integral_undef h_val]; norm_num)
    exact h.mono_set <| Ici_subset_Ioi.mpr <| by norm_num
  refine h_int.const_mul (√C0) |>.mono' ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable
      (ContinuousOn.mul (ContinuousOn.rexp (continuousOn_id.neg.div_const _))
        (ContinuousOn.sqrt (continuousOn_const.mul continuousOn_id)))
      measurableSet_Ici
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx using by
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _))]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h_bound x hx

/-- Taylor lower bound for `exp(-t)` (real-valued). -/
lemma exp_neg_ge_taylor_sum (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 2), (-t) ^ k / (k.factorial : ℝ) ≤
      Real.exp (-t) := by
  have h_taylor : ∀ m : ℕ, Real.exp (-t) =
      ∑ k ∈ Finset.range (m + 1), (-t)^k / (k.factorial : ℝ) +
      (-1)^(m + 1) * ∫ u in (0 : ℝ)..t,
        (t - u)^m / (m.factorial : ℝ) * Real.exp (-u) := by
    intro m; induction' m with m ih <;>
      simp_all +decide [Finset.sum_range_succ, pow_succ']
    have h_parts : ∀ a b : ℝ, ∫ u in a..b, (t - u) ^ (m + 1) / (m + 1)! * Real.exp (-u) = - (t - b) ^ (m + 1) / (m + 1)! * Real.exp (-b) + (t - a) ^ (m + 1) / (m + 1)! * Real.exp (-a) - ∫ u in a..b, (t - u) ^ m / (m ! : ℝ) * Real.exp (-u) := by
      intro a b;
      rw [ intervalIntegral.integral_mul_deriv_eq_deriv_mul ];
      any_goals intro x hx; exact HasDerivAt.div_const ( HasDerivAt.comp x ( hasDerivAt_pow _ _ ) ( hasDerivAt_id' x |> HasDerivAt.const_sub _ ) ) _;
      rotate_right;
      use fun x => -Real.exp ( -x );
      · norm_num [ Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
        norm_num [ Nat.cast_add_one_ne_zero ];
      · exact fun x hx => by simpa using HasDerivAt.neg ( HasDerivAt.exp ( hasDerivAt_neg x ) ) ;
      · exact Continuous.intervalIntegrable ( by continuity ) _ _;
      · exact Continuous.intervalIntegrable ( by continuity ) _ _;
    simp_all +decide [ ← pow_succ', mul_assoc, div_eq_mul_inv ];
    norm_num [ Nat.factorial_succ ] ; ring;
  specialize h_taylor (2 * n + 1); norm_num at *
  exact h_taylor ▸ le_add_of_nonneg_right (intervalIntegral.integral_nonneg (by positivity)
    fun u hu => mul_nonneg
      (div_nonneg (pow_nonneg (by linarith [hu.1, hu.2]) _) (by positivity))
      (Real.exp_nonneg _))

/-- Lower bound on the lower incomplete gamma function. -/
lemma lower_incomplete_gamma_bound :
    (gammaSeriesPartialSum 12 : ℝ) ≤
      ∫ x in Ioc (0 : ℝ) (9/4), Real.exp (-x) * x ^ (1/2 : ℝ) := by
  have h_taylor_bound : ∫ x in (0 : ℝ).. (9 / 4), Real.exp (-x) * x ^ (1 / 2 : ℝ) ≥ ∑ k ∈ Finset.range 12, (-1)^k / (k.factorial : ℝ) * ∫ x in (0 : ℝ).. (9 / 4), x ^ (k + 1 / 2 : ℝ) := by
    have h_taylor_bound : ∫ x in (0 : ℝ).. (9 / 4), Real.exp (-x) * x ^ (1 / 2 : ℝ) ≥ ∫ x in (0 : ℝ).. (9 / 4), (∑ k ∈ Finset.range 12, (-x) ^ k / (k.factorial : ℝ)) * x ^ (1 / 2 : ℝ) := by
      refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
      · exact Continuous.intervalIntegrable ( by exact Continuous.mul ( by continuity ) ( continuous_id.rpow_const <| by norm_num ) ) _ _;
      · exact Continuous.intervalIntegrable ( by exact Continuous.mul ( Real.continuous_exp.comp <| ContinuousNeg.continuous_neg ) <| continuous_id.rpow_const <| by norm_num ) _ _;
      · exact fun x hx₁ hx₂ => mul_le_mul_of_nonneg_right ( by have := exp_neg_ge_taylor_sum x hx₁ 5; norm_num [ Finset.sum_range_succ, Nat.factorial ] at *; linarith ) ( by positivity );
    convert h_taylor_bound using 1 ; norm_num [ Finset.sum_mul _ _ _, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul ];
    rw [ intervalIntegral.integral_finset_sum ] <;> norm_num;
    · refine' Finset.sum_congr rfl fun x hx => _ ; ring_nf;
      norm_num [ mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul ];
      refine' intervalIntegral.integral_congr fun y hy => _ ; rw [ Real.rpow_add' ] <;> norm_num ; ring;
      · norm_num at hy ; linarith;
      · positivity;
    · exact fun i hi => Continuous.intervalIntegrable ( by exact Continuous.mul ( continuous_const ) ( by exact Continuous.mul ( by continuity ) ( by exact Continuous.rpow continuous_id' continuous_const <| by norm_num ) ) ) _ _;
  convert h_taylor_bound.le using 1 <;> norm_num [ ← intervalIntegral.integral_of_le ];
  norm_num [ Finset.sum_range_succ, integral_rpow, gammaSeriesPartialSum ]

/-- The tail integral `∫_{9/2}^∞ e^{-x/2}·√x dx`. -/
lemma integral_exp_sqrt_le :
    ∫ x in Ioi (9/2 : ℝ), Real.exp (-x/2) * √x ≤
      2 * √2 * (√Real.pi / 2 - (gammaSeriesPartialSum 12 : ℝ)) := by
  have h_subst : ∫ x in Ioi (9 / 2), Real.exp (-x / 2) * Real.sqrt x =
      2 * Real.sqrt 2 * ∫ t in Ioi (9 / 4), Real.exp (-t) * Real.sqrt t := by
    have h1 : ∫ x in Ioi (9 / 2), Real.exp (-x / 2) * Real.sqrt x =
        2 * ∫ t in Ioi (9 / 4), Real.exp (-t) * Real.sqrt (2 * t) := by
      have : ∀ {f : ℝ → ℝ}, ∫ x in Set.Ioi (9 / 2), f x =
          2 * ∫ t in Set.Ioi (9 / 4), f (2 * t) := by
        intro f; rw [MeasureTheory.integral_comp_mul_left_Ioi] <;> norm_num; ring
      convert this using 4; ring_nf
    convert h1 using 1
    norm_num [mul_assoc, mul_comm, mul_left_comm, ← MeasureTheory.integral_const_mul]
  rw [h_subst]
  have h_split : ∫ t in Ioi (9 / 4 : ℝ), Real.exp (-t) * Real.sqrt t =
      (∫ t in Ioi (0 : ℝ), Real.exp (-t) * Real.sqrt t) -
      (∫ t in Ioc (0 : ℝ) (9 / 4), Real.exp (-t) * Real.sqrt t) := by
    rw [← MeasureTheory.integral_diff] <;> norm_num
    · rcongr x; norm_num
      exact ⟨fun hx => ⟨by linarith, fun _ => hx⟩, fun hx => hx.2 hx.1⟩
    · have h_gamma : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * Real.sqrt t =
          Real.Gamma (3 / 2) := by
        rw [Real.Gamma_eq_integral (by norm_num)]
        norm_num [Real.sqrt_eq_rpow]
      exact (by contrapose! h_gamma; rw [MeasureTheory.integral_undef h_gamma]; positivity)
    · exact Set.Ioc_subset_Ioi_self
  rw [h_split]
  gcongr
  · have := @Real.Gamma_eq_integral (3 / 2) ?_ <;> norm_num at *
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq] at this
    norm_num [Real.sqrt_eq_rpow] at *; linarith
  · convert lower_incomplete_gamma_bound using 1
    norm_num [Real.sqrt_eq_rpow]

/-- Numerical bound: `√C₀ · 2√2 · (√π/2 - γ_lower) ≤ tailBoundGamma`. -/
lemma gamma_bound_le_tailBoundGamma :
    √C0 * (2 * √2 * (√Real.pi / 2 - (gammaSeriesPartialSum 12 : ℝ))) ≤
      (tailBoundGamma : ℝ) := by
  have h_num :
      Real.sqrt C0 ≤ (sqrtUpperQ (891 * 162 / (250 * 161) : ℚ) (10^10) : ℝ) ∧
      Real.sqrt 2 ≤ (sqrtUpperQ 2 (10^10) : ℝ) ∧
      Real.sqrt Real.pi ≤ (sqrtUpperQ (3141593 / 1000000) (10^10) : ℝ) := by
    refine' ⟨_, _, _⟩
    · convert sqrt_le_sqrtUpperQ _ _ _ _ using 1 <;> norm_num; unfold C0; norm_num
    · convert sqrt_le_sqrtUpperQ 2 (by norm_num) (10^10) (by norm_num) using 1
    · refine' le_trans _ (sqrt_le_sqrtUpperQ _ _ _ _)
      · exact Real.sqrt_le_sqrt <| le_of_lt <| Real.pi_lt_d6.trans_le <| by norm_num
      · norm_num
      · grind
  convert mul_le_mul
    (mul_le_mul h_num.1
      (mul_le_mul_of_nonneg_left h_num.2.1 (by positivity : (0 : ℝ) ≤ 2)) ?_ ?_)
    (sub_le_sub_right (div_le_div_of_nonneg_right h_num.2.2
      (by positivity : (0 : ℝ) ≤ 2)) _) ?_ ?_ using 1 <;>
    norm_num [tailBoundGamma]
  any_goals exact (gammaSeriesPartialSum 12 : ℝ)
  · ring
  · ring
  · native_decide +revert
  · refine' le_trans _ (div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt <| Real.pi_gt_d2.le) zero_le_two)
    norm_num [gammaSeriesPartialSum]
    rw [div_div, le_div_iff₀] <;> nlinarith [Real.sqrt_nonneg 157, Real.sqrt_nonneg 50,
      Real.sq_sqrt (show 0 ≤ 157 by norm_num), Real.sq_sqrt (show 0 ≤ 50 by norm_num)]
  · exact mul_nonneg (mod_cast by native_decide)
      (mul_nonneg zero_le_two (mod_cast by native_decide))

/-- **Tail bound**: `∫_{9/2}^∞ integrandF ≤ tailBoundGamma`. -/
lemma tail_integral_gamma_bound :
    ∫ x in Ici (9/2 : ℝ), integrandF x ≤ (tailBoundGamma : ℝ) := by
  by_cases hint : IntegrableOn integrandF (Ici (9/2 : ℝ))
  · have h1 : ∫ x in Ici (9/2 : ℝ), integrandF x ≤
        ∫ x in Ici (9/2 : ℝ), Real.exp (-x/2) * √(C0 * x) :=
      setIntegral_mono_on hint exp_sqrt_integrableOn measurableSet_Ici
        (fun x hx => integrandF_le_tail x (Set.mem_Ici.mp hx))
    have h2 : ∫ x in Ici (9/2 : ℝ), Real.exp (-x/2) * √(C0 * x) =
        √C0 * ∫ x in Ioi (9/2 : ℝ), Real.exp (-x/2) * √x := by
      have : ∫ x in Ici (9/2 : ℝ), Real.exp (-x/2) * √(C0 * x) =
          ∫ x in Ici (9/2 : ℝ), √C0 * (Real.exp (-x/2) * √x) := by
        congr 1; ext x; rw [Real.sqrt_mul (le_of_lt C0_pos)]; ring
      rw [this, MeasureTheory.integral_const_mul,
        setIntegral_congr_set Ioi_ae_eq_Ici.symm]
    have h4 : √C0 * ∫ x in Ioi (9/2 : ℝ), Real.exp (-x/2) * √x ≤
        √C0 * (2 * √2 * (√Real.pi / 2 - (gammaSeriesPartialSum 12 : ℝ))) :=
      mul_le_mul_of_nonneg_left integral_exp_sqrt_le (Real.sqrt_nonneg _)
    linarith [gamma_bound_le_tailBoundGamma]
  · rw [integral_undef hint]
    exact_mod_cast (show (0 : ℚ) ≤ tailBoundGamma by native_decide)

-- =====================================================================
/-! ## §10. Main theorem -/
-- =====================================================================

/-- Integral splitting: `∫₀^∞ ≤ ∫₀^{9/2} + ∫_{9/2}^∞`. -/
lemma integral_split_le :
    (∫ x in Set.Ici (0 : ℝ), integrandF x) ≤
      (∫ x in Set.Icc (0 : ℝ) (9/2), integrandF x) +
      (∫ x in Set.Ici (9/2 : ℝ), integrandF x) := by
  by_cases h_int : MeasureTheory.IntegrableOn (fun x => integrandF x) (Set.Ici 0)
    MeasureTheory.volume
  · rw [MeasureTheory.integral_Icc_eq_integral_Ico, ← MeasureTheory.setIntegral_union] <;>
      norm_num
    · grind
    · exact h_int.mono_set <| Set.Ico_subset_Ici_self
    · exact h_int.mono_set <| Set.Ici_subset_Ici.mpr <| by norm_num
  · rw [MeasureTheory.integral_undef h_int]; norm_num
    exact add_nonneg
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x _ => integrandF_nonneg x)
      (MeasureTheory.setIntegral_nonneg measurableSet_Ici fun x _ => integrandF_nonneg x)

/-- **Main theorem**: `I < 9263/2000`, using Rosser–Schoenfeld. -/
theorem integralI_lt_9263_div_2000 :
    integralI < 9263 / 2000 := by
  unfold integralI
  by_cases hint : MeasureTheory.IntegrableOn integrandF (Set.Ici 0)
  · calc (∫ x in Set.Ici (0 : ℝ), integrandF x)
        ≤ (∫ x in Set.Icc (0 : ℝ) (9/2), integrandF x) +
          (∫ x in Set.Ici (9/2 : ℝ), integrandF x) := integral_split_le
      _ ≤ (computeSFin : ℝ) + (tailBoundGamma : ℝ) :=
          add_le_add finite_analytical_bound tail_integral_gamma_bound
      _ < 9263 / 2000 := by
          have h := overall_bound_gamma_check
          have : (overallBoundGamma : ℝ) < ((9263 : ℚ) / 2000 : ℚ) := by exact_mod_cast h
          simp only [overallBoundGamma, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at this
          linarith
  · rw [MeasureTheory.integral_undef hint]
    norm_num

#show_unused integralI_lt_9263_div_2000
#print axioms integralI_lt_9263_div_2000
