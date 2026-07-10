import Mathlib

open scoped BigOperators
open Finset

/-!
Let `r : ℕ → ℤ` be a bounded sequence of integers.  For `a ≤ b` write the sum
`r_a/a + r_{a+1}/(a+1) + ⋯ + r_b/b` as a reduced fraction `u_{a,b}/v_{a,b}` with
`v_{a,b} > 0`. The main theorem below states that for all sufficiently large `a`
and every `b` with `a < b` and `b < a + log a / 20`, either `r_b = 0`, or
`v_{a,b-1} < v_{a,b}`.

With `1/20` replaced by `1/2`, this is proven in

W. van Doorn, On the non-monotonicity of the denominator of generalized harmonic
sums. arXiv:2411.03073 (2024).

The reason that we prove the slightly weaker version here is that we can avoid
the prime number theorem that way.

Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) deserves the credit
for obtaining this formalization.

Lean version: leanprover/lean4:v4.28.0
-/

/-! ## Definitions -/

/-- The partial sum `S_{a,b} = ∑_{i=a}^{b} r_i / i ∈ ℚ`. -/
noncomputable def Ssum (r : ℕ → ℤ) (a b : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc a b, (r i : ℚ) / (i : ℚ)

/-- The reduced positive denominator `v_{a,b}` of `S_{a,b}`. -/
noncomputable def vden (r : ℕ → ℤ) (a b : ℕ) : ℕ := (Ssum r a b).den

/-- `Mlcm n = lcm(1, 2, …, n)` (with `Mlcm 0 = 1`). -/
noncomputable def Mlcm (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-- `L_{a,b} = lcm { i : a ≤ i ≤ b and r_i ≠ 0 }` (empty lcm `= 1`). -/
noncomputable def Lden (r : ℕ → ℤ) (a b : ℕ) : ℕ :=
  ((Finset.Icc a b).filter (fun i => r i ≠ 0)).lcm id

/-- The integer `X_{a,b} = L_{a,b} · S_{a,b} = ∑_{i} (L_{a,b}/i) r_i`. -/
noncomputable def Xnum (r : ℕ → ℤ) (a b : ℕ) : ℤ :=
  ∑ i ∈ (Finset.Icc a b).filter (fun i => r i ≠ 0),
    ((Lden r a b : ℤ) / (i : ℤ)) * r i

/-- `g_{a,b} = gcd(L_{a,b}, X_{a,b})`. -/
noncomputable def gfun (r : ℕ → ℤ) (a b : ℕ) : ℕ :=
  Nat.gcd (Lden r a b) (Xnum r a b).natAbs

/-! ## The lcm growth input (Chebyshev) -/

/-- `Real.log (Mlcm n)` equals the Chebyshev function `ψ n`. -/
lemma log_Mlcm_eq_psi (n : ℕ) : Real.log (Mlcm n) = Chebyshev.psi n := by
  rcases n.eq_zero_or_pos with hn | hn;
  · simp +decide [ hn, Mlcm, Chebyshev.psi ];
  · -- By definition of Mlcm, we have Mlcm n = lcm(1, 2, ..., n).
    have hMlcm_def : Mlcm n = ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n), p ^ Nat.log p n := by
      refine' Nat.dvd_antisymm _ _;
      · have h_lcm_div : ∀ i ∈ Finset.Icc 1 n, i ∣ ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n), p ^ (Nat.log p n) := by
          intro i hi;
          conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hi ] : i ≠ 0 ) ];
          rw [ ← Finset.prod_sdiff <| show i.factorization.support ⊆ Finset.filter Nat.Prime ( Finset.Icc 1 n ) from ?_ ];
          · exact dvd_mul_of_dvd_right ( Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p <| Nat.le_log_of_pow_le ( Nat.Prime.one_lt <| by aesop ) <| Nat.le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hi ] ) <| Nat.ordProj_dvd _ _ ) <| by linarith [ Finset.mem_Icc.mp hi ] ) _;
          · exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_primeFactors hp, Nat.le_trans ( Nat.le_of_mem_primeFactors hp ) ( Finset.mem_Icc.mp hi |>.2 ) ⟩, Nat.prime_of_mem_primeFactors hp ⟩;
        exact Finset.lcm_dvd h_lcm_div;
      · -- Every prime power `p^k` with `k ≤ log_p n` divides `Mlcm n`.
        have h_prime_power_div : ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n), p ^ Nat.log p n ∣ Mlcm n := by
          intro p hp; exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ), Nat.pow_log_le_self p hn.ne' ⟩ ) ;
        convert Finset.lcm_dvd h_prime_power_div using 1;
        -- The lcm of pairwise-coprime prime powers equals their product.
        have h_lcm_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Finset.lcm S (fun p => p ^ Nat.log p n) = ∏ p ∈ S, p ^ Nat.log p n := by
          intros S hS; induction S using Finset.induction <;> simp_all +decide ;
          exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop;
        rw [ h_lcm_prod fun p hp => Finset.mem_filter.mp hp |>.2 ];
    -- `ψ(n) = ∑ p ≤ n, log(p) * floor(log_p n)`.
    have hpsi_def : Chebyshev.psi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n), Real.log p * Nat.log p n := by
      rw [ Chebyshev.psi_eq_sum_Icc ];
      have hpsi_def : ∑ n ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt n = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), Real.log p := by
        have hpsi_def : ∀ m ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt m = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), if m = p^k then Real.log p else 0 := by
          intro m hm; by_cases hm' : IsPrimePow m <;> simp_all +decide [ ArithmeticFunction.vonMangoldt_apply ] ;
          · obtain ⟨ p, k, hp, hk, rfl ⟩ := hm';
            rw [ Finset.sum_eq_single p ] <;> simp_all +decide [ ← Nat.prime_iff ];
            · rw [ Finset.sum_eq_single k ] <;> simp_all +decide ;
              · rw [ Nat.pow_minFac ] ; aesop;
                grind +splitIndPred;
              · exact fun b hb₁ hb₂ hb₃ hb₄ => False.elim <| hb₃ <| Nat.pow_right_injective hp.one_lt hb₄.symm;
              · exact fun h => absurd ( h hk ) ( not_lt_of_ge ( Nat.le_log_of_pow_le hp.one_lt hm.2 ) );
            · intro q hq₁ hq₂ hq₃ hq₄; rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide ;
              intro h; have := congr_arg ( ·.factorization p ) h; norm_num at this; have := congr_arg ( ·.factorization q ) h; norm_num at this; aesop;
            · exact fun h => absurd ( h hp.pos ) ( not_lt_of_ge ( Nat.le_trans ( Nat.le_self_pow hk.ne' _ ) hm.2 ) );
          · rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ IsPrimePow ];
            exact Finset.sum_eq_zero fun x hx => if_neg <| Ne.symm <| hm' _ ( Nat.prime_iff.mp <| by tauto ) _ <| Finset.mem_Icc.mp hx |>.1;
        rw [ Finset.sum_congr rfl hpsi_def, Finset.sum_comm ];
        refine' Finset.sum_congr rfl fun p hp => _;
        rw [ Finset.sum_comm, Finset.sum_congr rfl ];
        simp +zetaDelta at *;
        exact fun x hx₁ hx₂ hx₃ => absurd ( hx₃ ( Nat.one_le_pow _ _ hp.2.pos ) ) ( not_lt_of_ge ( Nat.pow_le_of_le_log ( by linarith ) ( by linarith ) ) );
      simp_all +decide [ mul_comm, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
      rw [ ← hpsi_def, Finset.Icc_eq_cons_Ioc, Finset.sum_cons ] <;> aesop;
    rw [ hMlcm_def, Nat.cast_prod, Real.log_prod ] <;> norm_num;
    · simpa only [ mul_comm ] using hpsi_def.symm;
    · aesop

/-- `Mlcm n ≤ exp((log 4 + 4) · n)`, from Chebyshev's bound on `ψ`. -/
lemma Mlcm_le_exp (n : ℕ) :
    (Mlcm n : ℝ) ≤ Real.exp ((Real.log 4 + 4) * n) := by
  convert Real.exp_le_exp.mpr ( log_Mlcm_eq_psi n ▸ Chebyshev.psi_le_const_mul_self _ ) using 1;
  · rw [ Real.exp_log ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero _ ) ];
    exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
  · positivity

/-! ## Algebraic lemmas -/

/-- The lcm defining `L_{a,b}` is positive when `a ≥ 1`. -/
lemma Lden_pos {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℤ) (b : ℕ) : 0 < Lden r a b := by
  exact Nat.pos_of_ne_zero ( by exact mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

/-- `L_{a,b} · S_{a,b} = X_{a,b}` as rationals. -/
lemma Ssum_mul_Lden_eq_Xnum {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℤ) (b : ℕ) :
    (Lden r a b : ℚ) * Ssum r a b = (Xnum r a b : ℚ) := by
  unfold Ssum Xnum; simp +decide [ Finset.sum_filter ] ;
  rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; by_cases hi' : r i = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm ] ;
  rw [ Int.cast_div ] <;> norm_num;
  · ring;
  · exact_mod_cast Finset.dvd_lcm ( Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr hi, hi' ⟩ );
  · grind +splitImp

/-- `S_{a,b} = X_{a,b} / L_{a,b}` as a `divInt`. -/
lemma Ssum_eq_divInt {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℤ) (b : ℕ) :
    Ssum r a b = Rat.divInt (Xnum r a b) (Lden r a b) := by
  convert congr_arg ( fun x : ℚ => x / ( Lden r a b : ℚ ) ) ( Ssum_mul_Lden_eq_Xnum ha r b ) using 1;
  · rw [ mul_div_cancel_left₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| Lden_pos ha r b ) ];
  · convert Rat.divInt_eq_div _ _ using 1

/-- Denominator formula: `v_{a,b} = L_{a,b} / g_{a,b}`. -/
lemma vden_eq {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℤ) (b : ℕ) :
    vden r a b = Lden r a b / gfun r a b := by
  unfold vden gfun;
  rw [ Ssum_eq_divInt ha r b, Rat.den_divInt ];
  split_ifs <;> simp_all +decide [ Int.gcd ];
  exact absurd ‹_› ( ne_of_gt ( Lden_pos ha r b ) )

/-- The denominator of `S_{a,b}` divides `L_{a,b}`. -/
lemma den_S_dvd_Lden {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℤ) (b : ℕ) :
    (Ssum r a b).den ∣ Lden r a b := by
  have h_frac : ∃ (num : ℤ), Ssum r a b = num / (Lden r a b : ℚ) := by
    use Xnum r a b; rw [Ssum]; simp +decide [Xnum];
    rw [ Finset.sum_filter, Finset.sum_div ] ; refine' Finset.sum_congr rfl fun x hx => _ ; by_cases hx' : r x = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm ] ;
    rw [ Int.cast_div ] <;> norm_num;
    · rw [ mul_comm, inv_mul_eq_div, div_eq_mul_inv ] ; ring_nf ; norm_num [ show Lden r a b ≠ 0 from Nat.ne_of_gt <| Lden_pos ha r b ] ;
    · exact_mod_cast Finset.dvd_lcm ( Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr hx, hx' ⟩ );
    · grind;
  rcases h_frac with ⟨ num, h_frac ⟩ ; rw [ h_frac ] ;
  norm_num [ div_eq_mul_inv, Rat.mul_den ];
  split_ifs <;> [ simp +decide [ * ] ; exact Nat.div_dvd_of_dvd <| Nat.gcd_dvd_right _ _ ]

/-- `g_{a,b}` divides `L_{a,b}`. -/
lemma gfun_dvd_Lden (r : ℕ → ℤ) (a b : ℕ) : gfun r a b ∣ Lden r a b := by
  exact Nat.gcd_dvd_left _ _

/-- `g_{a,b} ≥ 1`. -/
lemma gfun_pos {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℤ) (b : ℕ) : 0 < gfun r a b := by
  apply Nat.gcd_pos_of_pos_left; exact Lden_pos ha r b;

/-- `L`-recursion: if `r_b ≠ 0` and `a < b`, then `L_{a,b} = lcm(L_{a,b-1}, b)`. -/
lemma Lden_succ {a b : ℕ} (hab : a < b) (r : ℕ → ℤ) (hrb : r b ≠ 0) :
    Lden r a b = Nat.lcm (Lden r a (b - 1)) b := by
  rcases b <;> simp_all +decide [ Lden ];
  rw [ show ( Finset.filter ( fun i => ¬r i = 0 ) ( Finset.Icc a ( Nat.succ _ ) ) ) = Finset.filter ( fun i => ¬r i = 0 ) ( Finset.Icc a ‹_› ) ∪ { ( Nat.succ ‹_› ) } from ?_, Finset.lcm_union ] ; aesop;
  grind

/-- Incremental common divisor bound: `gcd(L_{a,b-1}, b) ∣ Mlcm(b-a)`. -/
lemma gcd_Lden_dvd_Mlcm {a b : ℕ} (hab : a < b) (r : ℕ → ℤ) (hrb : r b ≠ 0) :
    Nat.gcd (Lden r a (b - 1)) b ∣ Mlcm (b - a) := by
  set g := Nat.gcd (Lden r a (b - 1)) b
  have hg_div : g ∣ Mlcm (b - a) := by
    have h_cases : ∀ p, Nat.Prime p → Nat.factorization g p ≤ Nat.factorization (Mlcm (b - a)) p := by
      intro p pp
      by_cases h : Nat.factorization g p = 0;
      · exact h.symm ▸ Nat.zero_le _;
      · -- Since `p` divides `g`, some `i` in the filter is divisible by `p^k`.
        obtain ⟨i, hi⟩ : ∃ i ∈ Finset.filter (fun i => r i ≠ 0) (Finset.Icc a (b - 1)), (p ^ (Nat.factorization g p)) ∣ i := by
          have h_div : p ^ (Nat.factorization g p) ∣ Lden r a (b - 1) := by
            exact Nat.dvd_trans ( Nat.ordProj_dvd _ _ ) ( Nat.gcd_dvd_left _ _ );
          contrapose! h_div;
          simp_all +decide [ Lden ];
          rw [ Nat.Prime.pow_dvd_iff_le_factorization ] <;> norm_num [ pp ];
          · have h_lcm_factorization : ∀ {S : Finset ℕ}, (∀ i ∈ S, ¬p ^ (Nat.factorization g p) ∣ i) → (Finset.lcm S id).factorization p < Nat.factorization g p := by
              intros S hS; induction S using Finset.induction <;> simp_all +decide ;
              · exact Nat.pos_of_ne_zero h;
              · by_cases h : ‹ℕ› = 0 <;> by_cases h' : Finset.lcm ‹Finset ℕ› id = 0 <;> simp_all +decide [ GCDMonoid.lcm, Nat.factorization_lcm ];
                · exact False.elim <| hS.2 0 h' <| by simp +decide ;
                · exact lt_of_not_ge fun h'' => hS.1 <| Nat.dvd_trans ( pow_dvd_pow _ h'' ) <| Nat.ordProj_dvd _ _;
            exact h_lcm_factorization fun i hi => h_div i ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hi |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hi |>.1 ) |>.2 ) ( Finset.mem_filter.mp hi |>.2 );
          · intro ha; specialize h_div 0; aesop;
        -- Since `p^k ∣ i` and `p^k ∣ b`, we get `p^k ∣ b - i`.
        have h_div_diff : (p ^ (Nat.factorization g p)) ∣ (b - i) := by
          exact Nat.dvd_sub ( Nat.dvd_trans ( pow_dvd_pow _ ( show Nat.factorization ( Nat.gcd ( Lden r a ( b - 1 ) ) b ) p ≤ Nat.factorization b p from Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 ( Nat.gcd_dvd_right _ _ ) p ) ) ( Nat.ordProj_dvd _ _ ) ) hi.2;
        -- Since `b - i ∈ {1, …, b - a}`, `p^k ∣ Mlcm(b - a)`.
        have h_div_Mlcm : (p ^ (Nat.factorization g p)) ∣ (Finset.Icc 1 (b - a)).lcm id := by
          refine' dvd_trans h_div_diff ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.sub_pos_of_lt ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hi.1 |>.1 ), Nat.sub_add_cancel ( by linarith : 1 ≤ b ) ] ), Nat.sub_le_sub_left ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hi.1 |>.1 ), Nat.sub_add_cancel ( by linarith : 1 ≤ b ) ] ) _ ⟩ ) );
        rw [ ← Nat.factorization_le_iff_dvd ] at h_div_Mlcm <;> simp_all +decide [ Mlcm ];
        exact pp.ne_zero
    rw [ ← Nat.factorization_le_iff_dvd ];
    · exact fun p => if hp : Nat.Prime p then h_cases p hp else by aesop;
    · exact Nat.ne_of_gt ( Nat.gcd_pos_of_pos_right _ ( pos_of_gt hab ) );
    · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
  exact hg_div

/-! ## The upper bound `R` on the values `|r_i|` -/

/-- For a nonzero `r_i` with `|r_i| ≤ Rval`, `|r_i|` divides `Mlcm Rval`. -/
lemma abs_r_dvd_MR_bdd (r : ℕ → ℤ) {Rval : ℕ} (hbound : ∀ i, (r i).natAbs ≤ Rval)
    {i : ℕ} (hi : r i ≠ 0) : (r i).natAbs ∣ Mlcm Rval := by
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hi, hbound i⟩)

/-- Global bound for `g_{a,b}` under an upper bound `Rval` on `|r_i|`:
`g_{a,b} ≤ Mlcm(b-a) · Mlcm Rval`. -/
lemma gfun_le_bdd (r : ℕ → ℤ) {Rval : ℕ} (hbound : ∀ i, (r i).natAbs ≤ Rval)
    {a : ℕ} (ha : 1 ≤ a) (b : ℕ) :
    gfun r a b ≤ Mlcm (b - a) * Mlcm Rval := by
  by_contra! h_contra;
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ (Nat.factorization (gfun r a b)) p > (Nat.factorization (Mlcm (b - a))) p + (Nat.factorization (Mlcm Rval)) p := by
    contrapose! h_contra;
    refine' Nat.le_of_dvd ( Nat.mul_pos ( Nat.pos_of_ne_zero _ ) ( Nat.pos_of_ne_zero _ ) ) _;
    · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
    · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
    · rw [ ← Nat.factorization_le_iff_dvd ];
      · rw [ Nat.factorization_mul ] <;> norm_num;
        · exact fun p => if hp : Nat.Prime p then h_contra p hp else by aesop;
        · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
        · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
      · exact Nat.ne_of_gt ( gfun_pos ha r b );
      · simp +decide [ Mlcm ];
  set A := (Lden r a b).factorization p
  set Dp := (Mlcm (b - a)).factorization p
  set Ep := (Mlcm Rval).factorization p
  have hA : A ≥ Dp + Ep + 1 := by
    refine' le_trans hp.2 ( Nat.factorization_le_iff_dvd ( _ ) ( _ ) |>.2 ( Nat.gcd_dvd_left _ _ ) p );
    · exact Nat.ne_of_gt ( Nat.gcd_pos_of_pos_left _ ( Lden_pos ha r b ) );
    · exact ne_of_gt ( Lden_pos ha r b );
  obtain ⟨i, hi⟩ : ∃ i ∈ (Finset.Icc a b).filter (fun i => r i ≠ 0), (i.factorization p) = A := by
    have h_lcm_factorization : ∀ {S : Finset ℕ}, (∀ i ∈ S, i ≠ 0) → (Finset.lcm S id).factorization p = Finset.sup S (fun i => (i.factorization p)) := by
      intros S hS_nonzero; induction S using Finset.induction <;> simp_all +decide ;
      erw [ Nat.factorization_lcm ] <;> simp_all +decide;
    have h_lcm_factorization : (Finset.filter (fun i => r i ≠ 0) (Finset.Icc a b)).sup (fun i => (i.factorization p)) = A := by
      convert h_lcm_factorization _ |> Eq.symm using 1;
      exact fun i hi => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hi |>.1 ) ] ;
    have h_lcm_factorization : ∃ i ∈ Finset.filter (fun i => r i ≠ 0) (Finset.Icc a b), ∀ j ∈ Finset.filter (fun i => r i ≠ 0) (Finset.Icc a b), (j.factorization p) ≤ (i.factorization p) := by
      apply_rules [ Finset.exists_max_image ];
      by_cases h_empty : Finset.filter (fun i => r i ≠ 0) (Finset.Icc a b) = ∅;
      · simp_all +decide;
        linarith;
      · exact Finset.nonempty_of_ne_empty h_empty;
    obtain ⟨ i, hi₁, hi₂ ⟩ := h_lcm_factorization; use i; simp_all +decide ;
    exact le_antisymm ( h_lcm_factorization ▸ Finset.le_sup ( f := fun i => i.factorization p ) ( Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr hi₁.1, hi₁.2 ⟩ ) ) ( h_lcm_factorization ▸ Finset.sup_le fun j hj => hi₂ j ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hj |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hj |>.1 ) |>.2 ) ( Finset.mem_filter.mp hj |>.2 ) );
  -- For each `j ≠ i` in the filter, `ν_p j ≤ Dp`.
  have h_div : ∀ j ∈ (Finset.Icc a b).filter (fun i => r i ≠ 0), j ≠ i → (p : ℤ) ^ (Ep + 1) ∣ ((Lden r a b : ℤ) / (j : ℤ)) * r j := by
    intros j hj_mem hj_ne_i
    have h_j_factorization : (j.factorization p) ≤ Dp := by
      by_cases h_cases : p ^ (Dp + 1) ∣ Int.natAbs (j - i);
      · have h_contra : p ^ (Dp + 1) ∣ Mlcm (b - a) := by
          refine' Nat.dvd_trans _ ( Finset.dvd_lcm ( show Int.natAbs ( j - i ) ∈ Finset.Icc 1 ( b - a ) from _ ) );
          · exact h_cases;
          · grind;
        exact absurd h_contra ( Nat.pow_succ_factorization_not_dvd ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ( by
          simp_all +decide [ Mlcm ] ) ) ) hp.1 );
      · contrapose! h_cases;
        have h_div : p ^ (Dp + 1) ∣ j ∧ p ^ (Dp + 1) ∣ i := by
          exact ⟨ Nat.dvd_trans ( pow_dvd_pow _ h_cases ) ( Nat.ordProj_dvd _ _ ), Nat.dvd_trans ( pow_dvd_pow _ ( by linarith ) ) ( Nat.ordProj_dvd _ _ ) ⟩;
        exact Int.natAbs_dvd_natAbs.mpr ( dvd_sub ( Int.natCast_dvd_natCast.mpr h_div.1 ) ( Int.natCast_dvd_natCast.mpr h_div.2 ) );
    have h_div : (p : ℤ) ^ (A - j.factorization p) ∣ ((Lden r a b : ℤ) / (j : ℤ)) := by
      norm_cast;
      rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
      · rw [ Nat.factorization_div ];
        · intro q; by_cases hq : p = q <;> aesop;
        · exact Finset.dvd_lcm hj_mem;
      · aesop;
      · exact ⟨ by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hj_mem |>.1 ) ], Nat.le_of_dvd ( Lden_pos ha r b ) ( Finset.dvd_lcm ( Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hj_mem |>.1 ) ], by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hj_mem |>.1 ) ] ⟩, by aesop ⟩ ) ) ⟩;
    refine' dvd_mul_of_dvd_left ( dvd_trans _ h_div ) _;
    exact pow_dvd_pow _ ( by omega );
  -- For `j = i`: the term is not divisible by `p^{Ep+1}`.
  have h_not_div : ¬((p : ℤ) ^ (Ep + 1) ∣ ((Lden r a b : ℤ) / (i : ℤ)) * r i) := by
    have h_not_div : (r i).natAbs.factorization p ≤ Ep := by
      have h_not_div : (r i).natAbs ∣ Mlcm Rval := by
        apply abs_r_dvd_MR_bdd r hbound (by
        grind);
      exact Nat.factorization_le_iff_dvd ( by aesop ) ( by exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by exact mt Finset.lcm_eq_zero_iff.mp <| by aesop ) |>.2 h_not_div p;
    have h_not_div : (Nat.factorization (Int.natAbs ((Lden r a b : ℤ) / (i : ℤ) * r i))) p ≤ Ep := by
      rw [ Int.natAbs_mul, Nat.factorization_mul ] <;> norm_num;
      · norm_cast;
        rw [ Nat.factorization_div ] <;> norm_num;
        · grind;
        · exact Finset.dvd_lcm hi.1;
      · norm_cast;
        exact Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Lden_pos ha r b ) ( Finset.dvd_lcm hi.1 ) ) ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hi.1 |>.1 ) ] ) );
      · aesop;
    rw [ ← Int.natAbs_dvd_natAbs, Int.natAbs_pow ];
    rw [ Nat.Prime.pow_dvd_iff_le_factorization ] <;> norm_num [ hp.1 ] ; linarith;
    exact ⟨ ne_of_gt <| Int.le_ediv_of_mul_le ( by linarith [ Finset.mem_Icc.mp <| Finset.mem_filter.mp hi.1 |>.1 ] ) <| by nlinarith [ Finset.mem_Icc.mp <| Finset.mem_filter.mp hi.1 |>.1, show Lden r a b ≥ i from Nat.le_of_dvd ( Lden_pos ha r b ) <| Finset.dvd_lcm <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp <| Finset.mem_filter.mp hi.1 |>.1 ], by linarith [ Finset.mem_Icc.mp <| Finset.mem_filter.mp hi.1 |>.1 ] ⟩, by aesop ⟩ ], by aesop ⟩;
  -- Therefore `Xnum` is not divisible by `p^{Ep+1}`.
  have h_Xnum_not_div : ¬((p : ℤ) ^ (Ep + 1) ∣ Xnum r a b) := by
    rw [ Xnum ];
    rw [ Finset.sum_eq_add_sum_diff_singleton hi.1 ];
    rw [ Int.dvd_add_left ( Finset.dvd_sum fun x hx => h_div x ( Finset.mem_sdiff.mp hx |>.1 ) ( by aesop ) ) ] ; aesop;
  have h_gfun_le_Ep : (gfun r a b).factorization p ≤ Ep := by
    have h_gfun_le_Ep : (gfun r a b).factorization p ≤ (Xnum r a b).natAbs.factorization p := by
      exact Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 ( Nat.gcd_dvd_right _ _ ) p;
    exact h_gfun_le_Ep.trans ( Nat.le_of_not_lt fun h => h_Xnum_not_div <| by simpa [ ← Int.natCast_dvd_natCast ] using Int.natCast_dvd.mpr <| Nat.dvd_trans ( pow_dvd_pow _ h ) <| Nat.ordProj_dvd _ _ );
  linarith

/-! ## No (strict) denominator drop before the threshold -/

/-- Strict no-drop: if `a < b`, `r_b ≠ 0`, `|r_i| ≤ Rval`, and
`Mlcm(b-a)^2 · Mlcm Rval < b`, then `v_{a,b-1} < v_{a,b}`. -/
lemma no_drop_strict (r : ℕ → ℤ) {Rval : ℕ} (hbound : ∀ i, (r i).natAbs ≤ Rval)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hrb : r b ≠ 0)
    (hthr : Mlcm (b - a) ^ 2 * Mlcm Rval < b) :
    vden r a (b - 1) < vden r a b := by
  set L' := Lden r a (b - 1)
  set g := gfun r a b
  set d := Nat.gcd L' b
  set m := Mlcm (b - a)
  set MR := Mlcm Rval
  -- It suffices to show `L' < vden r a b` (then `vden r a (b-1) ≤ L' < vden r a b`).
  suffices h_suff : L' < vden r a b by
    refine lt_of_le_of_lt ?_ h_suff
    exact Nat.le_of_dvd ( Lden_pos ha _ _ ) ( den_S_dvd_Lden ha _ _ )
  -- Because `g > 0`, this is equivalent to `L' * g < Lden r a b`.
  suffices h_equiv : L' * g < Lden r a b by
    have h_equiv2 : vden r a b * g = Lden r a b := by
      convert Nat.div_mul_cancel ( gfun_dvd_Lden r a b ) using 1;
      rw [ vden_eq ha ]
    nlinarith [ show 0 < g from gfun_pos ha r b ]
  -- Multiply by `d` and use `d * Lden r a b = L' * b`.
  have h_equiv : L' * g * d < L' * b := by
    have hg_d_lt_b : g * d ≤ m * MR * m := by
      have h1 : g ≤ m * MR := gfun_le_bdd r hbound ha b
      have h2 : d ≤ m := Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( gcd_Lden_dvd_Mlcm hab r hrb )
      calc g * d ≤ (m * MR) * m := Nat.mul_le_mul h1 h2
        _ = m * MR * m := rfl
    nlinarith [ show 0 < L' from Lden_pos ha r ( b - 1 ) ]
  have h_equiv2 : d * Lden r a b = L' * b := by
    rw [ Lden_succ hab r hrb, Nat.gcd_mul_lcm ]
  nlinarith [ show 0 < d by exact Nat.gcd_pos_of_pos_right _ ( by linarith ) ]

/-- `Real.log 4 ≤ 8/3`. -/
lemma log_four_le : Real.log 4 ≤ 8 / 3 := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog : Real.log 4 = 2 * Real.log 2 := by
    rw [ show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow ] ; push_cast ; ring
  rw [ hlog ] ; nlinarith [ h2 ]

/-- **No early denominator drop.**

Let `r : ℕ → ℤ` be a bounded sequence of integers.  Then for all sufficiently
large `a` and every `b` with `a < b` and `(b : ℝ) < a + log a / 20`, the reduced
positive denominator `v_{a,b}` of `r_a/a + ⋯ + r_b/b` satisfies either `r_b = 0`
or `v_{a,b-1} < v_{a,b}` (equivalently, the denominator strictly increases at
the last step).
-/
theorem no_early_drop (r : ℕ → ℤ)
    (hbdd : BddAbove (Set.range fun i => (r i).natAbs)) :
    ∀ᶠ (a : ℕ) in Filter.atTop, ∀ (b : ℕ), a < b → (b : ℝ) < a + Real.log a / 20 →
      r b = 0 ∨ vden r a (b - 1) < vden r a b := by
  obtain ⟨Rval, hRvalub⟩ := hbdd
  have hbound : ∀ i, (r i).natAbs ≤ Rval := fun i => hRvalub (Set.mem_range_self i)
  filter_upwards [Filter.eventually_ge_atTop 2,
      Filter.eventually_ge_atTop (Mlcm Rval ^ 3 + 1)] with a ha2 ha3
  intro b hb hblog
  rcases eq_or_ne (r b) 0 with hrb | hrb
  · exact Or.inl hrb
  · refine Or.inr (no_drop_strict r hbound (by linarith) hb hrb ?_)
    -- threshold: `Mlcm (b-a)^2 * Mlcm Rval < b`
    have hab_real : (a : ℝ) ≤ b := by exact_mod_cast hb.le
    have ha1 : (1 : ℝ) < a := by have h : (1 : ℕ) < a := by omega
                                 exact_mod_cast h
    have hloga : 0 < Real.log a := Real.log_pos ha1
    have h_bound : (Mlcm (b - a) : ℝ) ^ 2 * Mlcm Rval < b := by
      have e1 : (Mlcm (b - a) : ℝ) ≤ Real.exp ((Real.log 4 + 4) * ((b : ℝ) - a)) := by
        convert Mlcm_le_exp (b - a) using 1
        norm_num [Nat.cast_sub hb.le]
      have e2 : (Mlcm (b - a) : ℝ) ^ 2 * Mlcm Rval
          ≤ Real.exp (2 * (Real.log 4 + 4) * ((b : ℝ) - a)) * Mlcm Rval := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        calc (Mlcm (b - a) : ℝ) ^ 2
              ≤ (Real.exp ((Real.log 4 + 4) * ((b : ℝ) - a))) ^ 2 :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) e1 2
          _ = Real.exp (2 * (Real.log 4 + 4) * ((b : ℝ) - a)) := by
                rw [← Real.exp_nat_mul]; push_cast; ring_nf
      have e3 : Real.exp (2 * (Real.log 4 + 4) * ((b : ℝ) - a)) * Mlcm Rval
          ≤ (a : ℝ) ^ (2 / 3 : ℝ) * Mlcm Rval := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        rw [Real.rpow_def_of_pos (by norm_cast; linarith)]
        refine Real.exp_le_exp.mpr ?_
        have hc : Real.log 4 + 4 ≤ 20 / 3 := by linarith [log_four_le]
        have hlog4nn : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        have hx : (b : ℝ) - a ≤ Real.log a / 20 := by linarith
        have hxpos : (0 : ℝ) ≤ (b : ℝ) - a := by linarith
        calc 2 * (Real.log 4 + 4) * ((b : ℝ) - a)
              = 2 * ((Real.log 4 + 4) * ((b : ℝ) - a)) := by ring
          _ ≤ 2 * ((20 / 3) * (Real.log a / 20)) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact mul_le_mul hc hx hxpos (by norm_num)
          _ = Real.log a * (2 / 3) := by ring
      have e4 : (a : ℝ) ^ (2 / 3 : ℝ) * Mlcm Rval < a := by
        have hMlt : (Mlcm Rval : ℝ) < (a : ℝ) ^ (1 / 3 : ℝ) := by
          have hcube : (Mlcm Rval : ℝ) ^ 3 < a := by exact_mod_cast Nat.lt_of_succ_le ha3
          calc (Mlcm Rval : ℝ) = ((Mlcm Rval : ℝ) ^ 3) ^ (1 / 3 : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
            _ < (a : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_lt_rpow (by positivity) hcube (by positivity)
        calc (a : ℝ) ^ (2 / 3 : ℝ) * Mlcm Rval
              < (a : ℝ) ^ (2 / 3 : ℝ) * (a : ℝ) ^ (1 / 3 : ℝ) :=
                mul_lt_mul_of_pos_left hMlt (Real.rpow_pos_of_pos (by norm_cast; linarith) _)
          _ = a := by rw [← Real.rpow_add (by norm_cast; linarith)]; norm_num
      calc (Mlcm (b - a) : ℝ) ^ 2 * Mlcm Rval
            ≤ Real.exp (2 * (Real.log 4 + 4) * ((b : ℝ) - a)) * Mlcm Rval := e2
        _ ≤ (a : ℝ) ^ (2 / 3 : ℝ) * Mlcm Rval := e3
        _ < a := e4
        _ ≤ b := hab_real
    exact_mod_cast h_bound

#print axioms no_early_drop
