import Mathlib

/-
Let p(x) be an integer polynomial of degree d with positive leading coefficient,
and such that gcd(p(1), p(2), …, ) = 1. With S the sum of the absolute values of
the coefficients of p(x), this file contains a formalization of the fact that
every N ≥ (Sd^d)^(2d^2 + 10d) can be written as a sum of p(i) with all i
distinct. This makes results by Roth-Szekeres and Graham explicit.

K. F. Roth and G. Szekeres, Some asymptotic formulae in the theory of
partitions, Quarterly Journal of Mathematics, Volume 5 (1954), 241-259.

R. L. Graham, Complete Sequences of Polynomial Values, Duke Math. Jour., Volume
31 (1964), 275-286.

In 2017 Kim already made these results explicit in the case p(x) = x^d,
obtaining a bound of d^(cd^4) for some constant c.

D. Kim. On the largest integer that is not a sum of distinct positive nth
powers, Journal of Integer Sequences, Volume 20 (2017).

Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) did the formalization
based on an improved version of Kim's proof, which was written down by ChatGPT.

Lean version: leanprover/lean4:v4.28.0
-/

open Polynomial Finset BigOperators

noncomputable section

/-- Leading coefficient times d!. -/
def polyA (p : Polynomial ℤ) : ℤ := p.leadingCoeff * (p.natDegree.factorial : ℤ)
structure SignedBlock (p : Polynomial ℤ) (a : ℤ) where
  P : Finset ℕ
  N : Finset ℕ
  L : ℕ
  hP_bound : ∀ u ∈ P, u < L
  hN_bound : ∀ v ∈ N, v < L
  hBlock : ∀ x : ℤ,
    ∑ u ∈ P, p.eval (x + u) - ∑ v ∈ N, p.eval (x + v) = a

end

open Polynomial BigOperators Finset

/-- The defining property of τ_p(G): for all u, v with T ≤ u < v ≤ u + G,
    we have 0 < p(u) < p(v) ≤ 2·p(u). -/
def TauProp (p : Polynomial ℤ) (G T : ℕ) : Prop :=
  ∀ u v : ℕ, T ≤ u → u < v → v ≤ u + G →
    (0 < p.eval (u : ℤ)) ∧ (p.eval (u : ℤ) < p.eval (v : ℤ)) ∧
    (p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ))

def RepresentsInterval (b : ℕ → ℤ) (I : Finset ℕ) (C : ℤ) (K : ℕ) : Prop :=
  ∀ N : ℤ, C ≤ N → N < C + K →
    ∃ J : Finset ℕ, J ⊆ I ∧ ∑ i ∈ J, b i = N

/-
Helper: inductive step. If I_m represents [C, C + K - 1 + S_m] where
    S_m = ∑_{ν=1}^m b(t_ν), and b(t_{m+1}) ≤ K + S_m, and t_{m+1} ∉ I_m,
    then I_{m+1} = I_m ∪ {t_{m+1}} represents [C, C + K - 1 + S_{m+1}].
-/
theorem interval_extension
    (b : ℕ → ℤ) (I : Finset ℕ) (C : ℤ) (K : ℕ) (S : ℤ) (idx : ℕ)
    (hI : ∀ N : ℤ, C ≤ N → N ≤ C + K - 1 + S →
      ∃ J : Finset ℕ, J ⊆ I ∧ ∑ i ∈ J, b i = N)
    (hidx : idx ∉ I)
    (_hpos : 0 < b idx)
    (hbound : b idx ≤ K + S) :
    ∀ N : ℤ, C ≤ N → N ≤ C + K - 1 + S + b idx →
      ∃ J : Finset ℕ, J ⊆ I ∪ {idx} ∧ ∑ i ∈ J, b i = N := by
  intro N hN₁ hN₂;
  by_cases hN₃ : N ≤ C + K - 1 + S;
  · exact Exists.elim ( hI N hN₁ hN₃ ) fun J hJ => ⟨ J, Finset.Subset.trans hJ.1 ( Finset.subset_union_left ), hJ.2 ⟩;
  · obtain ⟨ J, hJ₁, hJ₂ ⟩ := hI ( N - b idx ) ( by linarith ) ( by linarith );
    exact ⟨ Insert.insert idx J, Finset.insert_subset_iff.mpr ⟨ Finset.mem_union_right _ ( Finset.mem_singleton_self _ ), Finset.Subset.trans hJ₁ ( Finset.subset_union_left ) ⟩, by rw [ Finset.sum_insert ( Finset.notMem_mono hJ₁ hidx ), hJ₂ ] ; ring ⟩

/-
The indexed interval completion lemma. Simplified version using
    natural number indexing.
-/
theorem interval_completion_nat
    (b : ℕ → ℤ) (I : Finset ℕ) (C : ℤ) (K : ℕ)
    (t : ℕ → ℕ)  -- 0-indexed sequence of tail indices
    (hI : RepresentsInterval b I C K)
    (ht_notI : ∀ m, t m ∉ I)
    (ht_disj : ∀ m n, m ≠ n → t m ≠ t n)
    (ht_pos : ∀ m, 0 < b (t m))
    (ht_bound : ∀ m, b (t m) ≤ K + ∑ ν ∈ Finset.range m, b (t ν)) :
    ∀ N : ℤ, C ≤ N →
      ∃ J : Finset ℕ, (∀ j ∈ J, j ∈ I ∨ ∃ m, j = t m) ∧
        ∑ i ∈ J, b i = N := by
  -- By induction on m, show that I_m represents [C, C+K-1 + ∑_{ν<m} b(t ν)]
  have h_ind : ∀ m : ℕ, ∀ N : ℤ, C ≤ N → N ≤ C + K - 1 + ∑ ν ∈ Finset.range m, b (t ν) → ∃ J : Finset ℕ, J ⊆ I ∪ Finset.image t (Finset.range m) ∧ ∑ i ∈ J, b i = N := by
    intro m
    induction' m with m ih
    generalize_proofs at *; (
    exact fun N hN₁ hN₂ => by obtain ⟨ J, hJ₁, hJ₂ ⟩ := hI N hN₁ ( by norm_num at *; linarith ) ; exact ⟨ J, by aesop ⟩ ;);
    convert interval_extension b ( I ∪ Finset.image t ( Finset.range m ) ) C K ( ∑ ν ∈ Finset.range m, b ( t ν ) ) ( t m ) ?_ ?_ ?_ ?_ using 1;
    · rw [ Finset.sum_range_succ, add_assoc ] ; simp +decide [ Finset.range_add_one ] ;
    · exact ih;
    · grind +qlia;
    · exact ht_pos m;
    · exact ht_bound m
  generalize_proofs at *; (
  -- For any N ≥ C, since S m → ∞ (each b(t m) ≥ 1), there exists m with N ≤ C + K - 1 + S m.
  have h_exists_m : ∀ N : ℤ, C ≤ N → ∃ m : ℕ, N ≤ C + K - 1 + ∑ ν ∈ Finset.range m, b (t ν) := by
    intro N hN
    have h_sum_inf : Filter.Tendsto (fun m => ∑ ν ∈ Finset.range m, b (t ν)) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop_mono ( fun m => by exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => ht_pos _ ) ) tendsto_natCast_atTop_atTop;
    generalize_proofs at *; (
    exact Filter.Eventually.exists ( h_sum_inf.eventually_ge_atTop ( N - ( C + K - 1 ) ) ) |> fun ⟨ m, hm ⟩ => ⟨ m, by linarith ⟩)
  generalize_proofs at *; (
  exact fun N hN => by obtain ⟨ m, hm ⟩ := h_exists_m N hN; obtain ⟨ J, hJ₁, hJ₂ ⟩ := h_ind m N hN hm; exact ⟨ J, fun j hj => by have := hJ₁ hj; aesop, hJ₂ ⟩ ;))

open Polynomial BigOperators

/-
If m ∈ ℕ, x ≡ y (mod m), then p(x) ≡ p(y) (mod m).
-/
set_option maxHeartbeats 800000 in
theorem unit_value_mod_a (p : Polynomial ℤ) (a : ℕ) (ha : 1 < a)
    (hgcd : ∀ (ℓ : ℕ), Nat.Prime ℓ → (ℓ : ℤ) ∣ (a : ℤ) →
      ∃ n : ℕ, 0 < n ∧ ¬ (ℓ : ℤ) ∣ p.eval (n : ℤ)) :
    ∃ u : ℕ, 0 < u ∧ u ≤ a ∧ Nat.Coprime (Int.natAbs (p.eval (u : ℤ))) a := by
  choose! N hN₁ hN₂ using hgcd;
  -- By the Chinese Remainder Theorem, there exists $u \in \{1, \ldots, a\}$ such that $u \equiv N(\ell) \pmod{\ell}$ for all primes $\ell \mid a$.
  obtain ⟨u, hu⟩ : ∃ u : ℕ, 0 < u ∧ u ≤ a ∧ ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ a → u ≡ N ℓ [MOD ℓ] := by
    obtain ⟨u, hu⟩ : ∃ u : ℕ, ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ a → u ≡ N ℓ [MOD ℓ] := by
      -- Applying the Chinese Remainder Theorem.
      have h_crt : ∀ ℓ ∈ Nat.primeFactors a, ∃ x : ℕ, x ≡ N ℓ [MOD ℓ] ∧ ∀ ℓ' ∈ Nat.primeFactors a, ℓ' ≠ ℓ → x ≡ 0 [MOD ℓ'] := by
        -- For each prime factor $\ell$ of $a$, let $y_\ell$ be the multiplicative inverse of $\prod_{\ell' \neq \ell} \ell'$ modulo $\ell$.
        intro ℓ hℓ
        obtain ⟨y_ℓ, hy_ℓ⟩ : ∃ y_ℓ : ℕ, y_ℓ * (∏ ℓ' ∈ Nat.primeFactors a \ {ℓ}, ℓ') ≡ 1 [MOD ℓ] := by
          have := Nat.exists_mul_mod_eq_one_of_coprime ( show Nat.Coprime ( ∏ ℓ' ∈ a.primeFactors \ { ℓ }, ℓ' ) ℓ from Nat.Coprime.prod_left fun x hx => Nat.coprime_comm.mp <| Nat.Prime.coprime_iff_not_dvd ( Nat.prime_of_mem_primeFactors hℓ ) |>.2 fun h => ?_ );
          · exact Exists.elim ( this ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hℓ ) ) ) fun m hm => ⟨ m, by rw [ mul_comm, ← Nat.mod_add_div ( ( ∏ ℓ' ∈ a.primeFactors \ { ℓ }, ℓ' ) * m ) ℓ, hm.2 ] ; norm_num [ Nat.ModEq, Nat.mod_eq_of_lt ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hℓ ) ) ] ⟩;
          · simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
        use y_ℓ * (∏ ℓ' ∈ Nat.primeFactors a \ {ℓ}, ℓ') * N ℓ;
        exact ⟨ by simpa using hy_ℓ.mul_right _, fun ℓ' hℓ' hℓ'' => Nat.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩;
      choose! x hx₁ hx₂ using h_crt;
      use ∑ ℓ ∈ Nat.primeFactors a, x ℓ;
      intro ℓ hℓ₁ hℓ₂; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
      rw [ Finset.sum_eq_single ℓ ] <;> aesop;
    refine' ⟨ if u % a = 0 then a else u % a, _, _, _ ⟩ <;> split_ifs <;> simp_all +decide [ Nat.ModEq ];
    · grind;
    · exact Nat.pos_of_ne_zero ‹_›;
    · exact Nat.le_of_lt ( Nat.mod_lt _ ha.le );
    · intro ℓ hℓ₁ hℓ₂; specialize hu ℓ hℓ₁ hℓ₂; simp_all +decide [ Nat.mod_eq_zero_of_dvd ] ;
      rw [ ← hu, Nat.mod_eq_zero_of_dvd ( dvd_trans hℓ₂ ( Nat.dvd_of_mod_eq_zero ‹u % a = 0› ) ) ];
  refine' ⟨ u, hu.1, hu.2.1, Nat.coprime_of_dvd' _ ⟩;
  intro k hk hk₁ hk₂; specialize hN₂ k hk ( mod_cast hk₂ ) ; simp_all +decide [ ← Int.natCast_dvd_natCast, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Polynomial.eval_eq_sum_range ] ;
  simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]

/-
If R ≡ 0 (mod a), then ∑_{e ∈ F_r} p(R + e) ≡ r (mod a).
-/
theorem elementary_ratio_bound (d : ℕ) (hd : 1 ≤ d) :
    (1 + 1 / (6 * (d : ℚ))) ^ d ≤ 6 / 5 := by
  -- Let's rewrite the inequality as $(1 + 1/(6d))^d \leq 6/5$.
  suffices h_ineq : (1 + 1 / (6 * (d : ℝ))) ^ d ≤ (6 / 5 : ℝ) by
    convert h_ineq using 1 ; ring_nf;
    norm_num [ ← @Rat.cast_inj ℝ ];
    norm_num [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity : 0 < ( 1 + ( d : ℝ ) ⁻¹ * ( 1 / 6 ) ) ) ];
    rw [ Real.exp_mul, Real.exp_log ( by positivity ) ] ; norm_cast;
    field_simp;
    rw [ div_pow, div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast <;> norm_num [ Nat.succ_eq_add_one, mul_add ];
    · rw [ div_pow, div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast ; ring_nf ; positivity;
    · positivity
  generalize_proofs at *; (
  -- We can raise both sides to the power of $d$ and use the binomial theorem to expand the left-hand side.
  have h_binom : (1 + 1 / (6 * (d : ℝ))) ^ d ≤ ∑ j ∈ range (d + 1), (1 : ℝ) / 6 ^ j := by
    rw [ add_comm, add_pow ] ; norm_num ; ring_nf ; norm_num;
    gcongr;
    exact mul_le_of_le_one_left ( by positivity ) ( by rw [ inv_mul_le_iff₀ ( by positivity ) ] ; norm_cast; linarith [ Nat.choose_le_pow d ‹_› ] )
  generalize_proofs at *; (
  exact h_binom.trans ( by ring_nf; rw [ geom_sum_eq ] <;> ring_nf <;> norm_num ) ;))

/-- For a polynomial p with integer coefficients, define p_+(x) = ∑ max(a_i, 0) * x^i -/
noncomputable def posMajorant (p : Polynomial ℤ) : Polynomial ℤ :=
  p.sum (fun n a => Polynomial.monomial n (max a 0))
noncomputable def Hzero (p : Polynomial ℤ) : ℤ :=
  p.leadingCoeff + ∑ i ∈ Finset.range p.natDegree, |p.coeff i|

/-
For x ≥ 1, p(x) ≤ p_+(x)
-/
theorem eval_le_posMajorant (p : Polynomial ℤ) (x : ℤ) (hx : 1 ≤ x) :
    p.eval x ≤ (posMajorant p).eval x := by
  unfold posMajorant;
  simp +decide [ Polynomial.eval_finset_sum, Polynomial.sum_def ];
  rw [ Polynomial.eval_eq_sum, Polynomial.sum_def ];
  exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity )

/-
p_+ is nondecreasing on ℕ
-/
theorem posMajorant_nondecreasing (p : Polynomial ℤ) (x y : ℕ) (hxy : x ≤ y) :
    (posMajorant p).eval (x : ℤ) ≤ (posMajorant p).eval (y : ℤ) := by
  unfold posMajorant;
  simp +decide [ Polynomial.eval_finset_sum, Polynomial.sum_def ];
  gcongr
noncomputable def diffOp (h : ℤ) (f : Polynomial ℤ) : Polynomial ℤ :=
  f.comp (Polynomial.X + Polynomial.C h) - f

/-
A single application of the difference operator reduces degree by 1 and
    multiplies the leading coefficient by deg · h.
-/
set_option maxHeartbeats 800000 in
theorem diffOp_leadingCoeff (f : Polynomial ℤ) (h : ℤ) (hh : h ≠ 0)
    (hf : 1 ≤ f.natDegree) :
    (diffOp h f).natDegree = f.natDegree - 1 ∧
    (diffOp h f).leadingCoeff = f.leadingCoeff * f.natDegree * h := by
  unfold diffOp;
  -- By definition of polynomial composition and subtraction, we know that
  have h_deg : (f.comp (Polynomial.X + Polynomial.C h) - f).natDegree = f.natDegree - 1 := by
    rw [ Polynomial.natDegree_eq_of_degree_eq_some ] ; erw [ Polynomial.degree_eq_of_le_of_coeff_ne_zero ] <;> norm_num [ Polynomial.coeff_X_add_C_pow ];
    · rw [ Polynomial.degree_le_iff_coeff_zero ];
      intros m hm; rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ] ; simp +decide ;
      rw [ Finset.sum_eq_single m ] <;> norm_num;
      · erw [ Polynomial.coeff_X_add_C_pow ] ; aesop;
      · exact fun n hn hnm => Or.inr <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by erw [ Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C ] ; norm_cast at * ; omega;
      · exact fun h => Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt h;
    · erw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
      norm_num [ Polynomial.coeff_X_add_one_pow, Finset.sum_range_succ ];
      erw [ Finset.sum_eq_single ( f.natDegree - 1 ) ] <;> norm_num [ Polynomial.coeff_X_add_C_pow ];
      · erw [ Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_add_C_pow ];
        aesop;
      · exact fun n hn hn' => Or.inr <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by erw [ Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C ] ; norm_num ; contrapose! hn' ; omega;
      · aesop;
  rw [ Polynomial.leadingCoeff, h_deg ];
  rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
  norm_num [ Polynomial.coeff_X_add_C_pow, Finset.sum_range_succ ];
  erw [ Finset.sum_eq_single ( f.natDegree - 1 ) ] <;> norm_num [ Polynomial.coeff_X_add_C_pow ];
  · erw [ Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_add_C_pow ] ; norm_num ; ring_nf;
    rcases k : f.natDegree with ( _ | _ | k ) <;> simp_all +decide [mul_assoc];
  · exact fun n hn hn' => Or.inr <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by erw [ Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C ] ; norm_num ; omega;
  · aesop

/-
The iterated difference operator applied d times to a degree-d polynomial
    with leading coefficient A gives the constant A · d! · ∏ hᵢ.

    ∇_{h_{d-1}} ∘ ... ∘ ∇_{h_0} p(X) = A · d! · ∏ hᵢ

    We state this for the composed operator.
-/
set_option maxHeartbeats 800000 in
theorem iterated_diff_const (p : Polynomial ℤ) (d : ℕ) (hd : p.natDegree = d)
    (hd_pos : 0 < d)
    (h : Fin d → ℤ) (hh : ∀ i, h i ≠ 0) :
    (List.ofFn (fun i => h i)).foldl (fun f hi => diffOp hi f) p =
      Polynomial.C (p.leadingCoeff * (d.factorial : ℤ) * ∏ i, h i) := by
  have h_ind : ∀ (d : ℕ) (p : Polynomial ℤ) (h : ℤ), p.natDegree = d → 0 < d → h ≠ 0 → (diffOp h p).natDegree = d - 1 ∧ (diffOp h p).leadingCoeff = p.leadingCoeff * d * h := by
    exact fun d p h hd hd_pos hh => diffOp_leadingCoeff p h hh ( by linarith ) |> fun h => ⟨ by aesop, by aesop ⟩;
  -- By induction on $d$, we can show that the $d$-fold difference of $p$ is a constant polynomial with the given value.
  have h_induction : ∀ (d : ℕ) (p : Polynomial ℤ) (h : Fin d → ℤ), p.natDegree = d → (∀ i, h i ≠ 0) →
    (List.foldl (fun f hi => diffOp hi f) p (List.ofFn h)) =
    Polynomial.C (p.leadingCoeff * Nat.factorial d * (∏ i, h i)) := by
      intros d p h hp hh; induction' d with d hd generalizing p <;> simp_all +decide [ Nat.factorial_succ ] ;
      · rw [ Polynomial.eq_C_of_natDegree_eq_zero hp, Polynomial.leadingCoeff_C ];
        rfl;
      · rw [ Fin.prod_univ_succ ] ; ring;
  exact h_induction d p h hd hh

/-
A tuple h = (h₀, ..., h_{d-1}) ∈ ℕ^d is dissociated if the map
ε ↦ ∑ εᵢhᵢ is injective on {0,1}^d.
-/

noncomputable def explicitTailParam (p : Polynomial ℤ) (G : ℕ) : ℕ :=
  max (6 * p.natDegree * G) (Int.toNat ⌈(4 * Hzero p : ℚ) / p.leadingCoeff⌉)

/-- p(x) ≥ Ax^d - H₀(p)x^{d-1} for x ≥ 1. -/
theorem eval_lower_bound (p : Polynomial ℤ) (x : ℕ) (hx : 1 ≤ x)
    (hA : 0 < p.leadingCoeff) :
    (p.leadingCoeff * (x : ℤ) ^ p.natDegree - Hzero p * (x : ℤ) ^ (p.natDegree - 1)
      : ℤ) ≤ p.eval (x : ℤ) := by
  have h_bound : |∑ i ∈ Finset.range p.natDegree, p.coeff i * (x : ℤ) ^ i| ≤ ∑ i ∈ Finset.range p.natDegree, |p.coeff i| * (x : ℤ) ^ (p.natDegree - 1) := by
    exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i hi => by rw [ abs_mul, abs_pow, abs_of_nonneg ( by positivity : ( 0 : ℤ ) ≤ x ) ] ; exact mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by norm_cast ) ( Nat.le_sub_one_of_lt ( Finset.mem_range.mp hi ) ) ) ( by positivity ) );
  rw [ Polynomial.eval_eq_sum_range ];
  rw [ Finset.sum_range_succ_comm ];
  unfold Hzero; simp_all +decide [ ← Finset.sum_mul _ _ _ ] ;
  nlinarith [ abs_le.mp h_bound, pow_pos ( by positivity : 0 < ( x : ℤ ) ) ( p.natDegree - 1 ) ]

/-- p(x) ≤ Ax^d + H₀(p)x^{d-1} for x ≥ 1. -/
theorem eval_upper_bound (p : Polynomial ℤ) (x : ℕ) (hx : 1 ≤ x)
    (hA : 0 < p.leadingCoeff) :
    p.eval (x : ℤ) ≤
      p.leadingCoeff * (x : ℤ) ^ p.natDegree + Hzero p * (x : ℤ) ^ (p.natDegree - 1) := by
  unfold Hzero;
  rw [ Polynomial.eval_eq_sum_range ];
  rw [ Finset.sum_range_succ_comm ];
  norm_num [ add_mul ];
  exact le_add_of_nonneg_of_le ( mul_nonneg hA.le ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( by rw [ Finset.sum_mul _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by cases abs_cases ( p.coeff i ) <;> nlinarith [ pow_pos ( by positivity : 0 < ( x : ℤ ) ) i, pow_le_pow_right₀ ( by linarith : 1 ≤ ( x : ℤ ) ) ( show i ≤ p.natDegree - 1 from Nat.le_sub_one_of_lt ( Finset.mem_range.mp hi ) ) ] )

/-- If u ≥ 4H₀/A and u ≥ 1, then p(u) > 0. -/
theorem eval_pos_of_large (p : Polynomial ℤ) (u : ℕ)
    (hA : 0 < p.leadingCoeff) (hd : 1 ≤ p.natDegree)
    (hu : 1 ≤ u) (hH : 4 * Hzero p ≤ p.leadingCoeff * u) :
    0 < p.eval (u : ℤ) := by
  have h_lower_bound : p.eval (u : ℤ) ≥ p.leadingCoeff * (u : ℤ) ^ p.natDegree - Hzero p * (u : ℤ) ^ (p.natDegree - 1) := by
    exact eval_lower_bound p u hu hA
  rcases n : p.natDegree with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
  · nlinarith;
  · nlinarith [ show 0 < ( u : ℤ ) * u ^ ‹_› by positivity, show 0 < ( u : ℤ ) ^ 2 * u ^ ‹_› by positivity ]

/-
The explicit tau bound: τ_p(G) ≤ 𝔗_p(G).

  That is, explicitTailParam p G satisfies the TauProp for gap G.
-/
set_option maxHeartbeats 1600000 in
theorem explicit_tau_bound (p : Polynomial ℤ) (G : ℕ)
    (hA : 0 < p.leadingCoeff) (hd : 1 ≤ p.natDegree) :
    TauProp p G (explicitTailParam p G) := by
  -- Let T = explicitTailParam p G = max(6dG, ⌈4H₀/A⌉). We need TauProp p G T, i.e., for all u v with T ≤ u < v ≤ u + G: 0 < p(u), p(u) < p(v), p(v) ≤ 2p(u).
  -- Since T ≥ ⌈4H₀/A⌉ and T ≥ 6dG, we have u ≥ ⌈4H₀/A⌉ ≥ 1, so 4H₀ ≤ Au. Also u ≥ 6dG.
  have h_u_ge_4H0_div_A : ∀ u : ℕ, u ≥ explicitTailParam p G → 4 * Hzero p ≤ p.leadingCoeff * u := by
    unfold explicitTailParam;
    norm_num +zetaDelta at *;
    intro u hu₁ hu₂; rw [ Int.ceil_le ] at hu₂; rw [ div_le_iff₀ ] at hu₂ <;> norm_cast at * ; linarith;
  intro u v hu hv hvG
  have h_pos : 0 < p.eval (u : ℤ) := by
    apply eval_pos_of_large p u hA hd (by linarith [hu, show 1 ≤ explicitTailParam p G from Nat.one_le_iff_ne_zero.mpr (by
    exact ne_of_gt ( lt_max_of_lt_left ( by nlinarith ) ))]) (h_u_ge_4H0_div_A u hu)
  have h_mono : p.eval (u : ℤ) < p.eval (v : ℤ) := by
    by_cases hd_ge_2 : 2 ≤ p.natDegree;
    · -- For degree ≥ 2: p(v) - p(u) = A(v^d - u^d) + lower terms. And v^d - u^d ≥ d·u^{d-1}(v-u) (by convexity or just algebraic identity).
      have h_diff : p.eval (v : ℤ) - p.eval (u : ℤ) ≥ p.leadingCoeff * (v ^ p.natDegree - u ^ p.natDegree) - Hzero p * (v ^ (p.natDegree - 1) - u ^ (p.natDegree - 1)) := by
        have h_diff : p.eval (v : ℤ) - p.eval (u : ℤ) ≥ p.leadingCoeff * (v ^ p.natDegree - u ^ p.natDegree) - ∑ i ∈ Finset.range p.natDegree, |p.coeff i| * (v ^ i - u ^ i) := by
          have h_diff : p.eval (v : ℤ) - p.eval (u : ℤ) = p.leadingCoeff * (v ^ p.natDegree - u ^ p.natDegree) + ∑ i ∈ Finset.range p.natDegree, p.coeff i * (v ^ i - u ^ i) := by
            simp +decide [ Polynomial.eval_eq_sum_range, Finset.sum_range_succ_comm ];
            simpa only [ mul_sub, Finset.sum_sub_distrib ] using by ring;
          rw [h_diff];
          norm_num [ sub_eq_add_neg ];
          rw [ ← Finset.sum_neg_distrib ] ; exact Finset.sum_le_sum fun i hi => by cases abs_cases ( p.coeff i ) <;> nlinarith [ pow_le_pow_left' hv.le i ] ;
        refine le_trans ?_ h_diff;
        gcongr;
        refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( show ( v ^ i - u ^ i : ℤ ) ≤ v ^ ( p.natDegree - 1 ) - u ^ ( p.natDegree - 1 ) from _ ) ( abs_nonneg _ ) ) _;
        · rw [ ← geom_sum₂_mul, ← geom_sum₂_mul ];
          refine' mul_le_mul_of_nonneg_right _ ( sub_nonneg.mpr <| Nat.cast_le.mpr hv.le );
          refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( show i ≤ p.natDegree - 1 from Nat.le_sub_one_of_lt ( Finset.mem_range.mp hi ) ) ) fun _ _ _ => mul_nonneg ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) );
          refine' Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left _ ( pow_nonneg ( Nat.cast_nonneg _ ) _ );
          exact pow_le_pow_right₀ ( by linarith [ show 1 ≤ u from by linarith [ show 1 ≤ explicitTailParam p G from Nat.one_le_iff_ne_zero.mpr <| by
                                                                                  exact ne_of_gt ( lt_max_of_lt_left ( by nlinarith ) ) ] ] ) ( by norm_num at *; omega );
        · rw [ ← Finset.sum_mul _ _ _ ];
          exact mul_le_mul_of_nonneg_right ( le_add_of_nonneg_left <| by positivity ) <| sub_nonneg_of_le <| by gcongr;
      -- Since $v > u$, we have $v^d - u^d \geq d \cdot u^{d-1} \cdot (v - u)$.
      have h_diff_bound : (v : ℤ) ^ p.natDegree - (u : ℤ) ^ p.natDegree ≥ p.natDegree * (u : ℤ) ^ (p.natDegree - 1) * (v - u) := by
        have h_diff_bound : (v : ℤ) ^ p.natDegree - (u : ℤ) ^ p.natDegree = (v - u) * ∑ i ∈ Finset.range p.natDegree, (v : ℤ) ^ i * (u : ℤ) ^ (p.natDegree - 1 - i) := by
          rw [ ← geom_sum₂_mul, mul_comm ];
        rw [ h_diff_bound, mul_comm ];
        gcongr;
        · linarith;
        · refine' le_trans _ ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( show ( v : ℤ ) ≥ u by norm_cast; linarith ) _ ) ( pow_nonneg ( by positivity ) _ ) );
          simp +decide [ ← pow_add, add_comm, ← Finset.sum_range_reflect ];
      -- Since $v > u$, we have $v^{d-1} - u^{d-1} \leq (d-1) \cdot v^{d-2} \cdot (v - u)$.
      have h_diff_bound_lower : (v : ℤ) ^ (p.natDegree - 1) - (u : ℤ) ^ (p.natDegree - 1) ≤ (p.natDegree - 1) * (v : ℤ) ^ (p.natDegree - 2) * (v - u) := by
        have h_diff_bound_lower : ∀ {x y : ℕ}, x < y → ∀ {k : ℕ}, 1 ≤ k → (y : ℤ) ^ k - (x : ℤ) ^ k ≤ k * (y : ℤ) ^ (k - 1) * (y - x) := by
          intros x y hxy k hk; induction hk <;> simp_all +decide [ pow_succ' ] ;
          rcases ‹1 ≤ _› <;> simp_all +decide [ pow_succ' ];
          · nlinarith only [ hxy ];
          · nlinarith [ show ( y : ℤ ) ^ ‹_› ≥ 0 by positivity, show ( x : ℤ ) ^ ‹_› ≥ 0 by positivity, show ( y : ℤ ) * y ^ ‹_› ≥ 0 by positivity, show ( x : ℤ ) * x ^ ‹_› ≥ 0 by positivity, show ( y : ℤ ) * y ^ ‹_› ≥ ( x : ℤ ) * x ^ ‹_› by gcongr ];
        convert h_diff_bound_lower hv ( Nat.sub_pos_of_lt hd_ge_2 ) using 1 ; cases p_natDegree : p.natDegree <;> aesop;
      -- Since $v \leq u + G$, we have $v^{d-2} \leq (6/5)u^{d-2}$.
      have h_v_bound : (v : ℤ) ^ (p.natDegree - 2) ≤ (6 / 5 : ℚ) * (u : ℚ) ^ (p.natDegree - 2) := by
        have h_v_bound : (v : ℚ) ≤ (1 + 1 / (6 * p.natDegree : ℚ)) * (u : ℚ) := by
          field_simp;
          norm_cast;
          nlinarith [ show explicitTailParam p G ≥ 6 * p.natDegree * G by exact le_max_left _ _ ];
        have h_v_bound_pow : (v : ℚ) ^ (p.natDegree - 2) ≤ ((1 + 1 / (6 * p.natDegree : ℚ)) * (u : ℚ)) ^ (p.natDegree - 2) := by
          exact pow_le_pow_left₀ ( Nat.cast_nonneg _ ) h_v_bound _;
        have h_v_bound_pow_simplified : ((1 + 1 / (6 * p.natDegree : ℚ)) ^ (p.natDegree - 2)) ≤ (6 / 5 : ℚ) := by
          have h_v_bound_pow_simplified : (1 + 1 / (6 * p.natDegree : ℚ)) ^ (p.natDegree) ≤ 6 / 5 := by
            convert elementary_ratio_bound p.natDegree hd using 1;
          exact le_trans ( pow_le_pow_right₀ ( le_add_of_nonneg_right <| by positivity ) <| Nat.sub_le _ _ ) h_v_bound_pow_simplified;
        simp_all +decide [ mul_pow ];
        exact h_v_bound_pow.trans ( mul_le_mul_of_nonneg_right h_v_bound_pow_simplified <| by positivity );
      -- Substitute the bounds into the inequality.
      have h_subst : p.eval (v : ℤ) - p.eval (u : ℤ) ≥ p.leadingCoeff * p.natDegree * (u : ℤ) ^ (p.natDegree - 1) * (v - u) - Hzero p * (p.natDegree - 1) * (6 / 5 : ℚ) * (u : ℚ) ^ (p.natDegree - 2) * (v - u) := by
        have h_subst : p.eval (v : ℤ) - p.eval (u : ℤ) ≥ p.leadingCoeff * p.natDegree * (u : ℤ) ^ (p.natDegree - 1) * (v - u) - Hzero p * (p.natDegree - 1) * (v : ℤ) ^ (p.natDegree - 2) * (v - u) := by
          nlinarith [ show 0 ≤ Hzero p from by
                        exact add_nonneg hA.le ( Finset.sum_nonneg fun _ _ => abs_nonneg _ ) ];
        have h_subst : Hzero p * (p.natDegree - 1) * (v : ℤ) ^ (p.natDegree - 2) * (v - u) ≤ Hzero p * (p.natDegree - 1) * (6 / 5 : ℚ) * (u : ℚ) ^ (p.natDegree - 2) * (v - u) := by
          have h_subst : Hzero p * (p.natDegree - 1) * (v : ℚ) ^ (p.natDegree - 2) ≤ Hzero p * (p.natDegree - 1) * (6 / 5 : ℚ) * (u : ℚ) ^ (p.natDegree - 2) := by
            convert mul_le_mul_of_nonneg_left h_v_bound ( show ( 0 : ℚ ) ≤ Hzero p * ( p.natDegree - 1 ) by exact mul_nonneg ( mod_cast by
                                                            exact add_nonneg hA.le ( Finset.sum_nonneg fun _ _ => abs_nonneg _ ) ) ( sub_nonneg.mpr ( mod_cast hd ) ) ) using 1 ; ring;
          exact mul_le_mul_of_nonneg_right ( mod_cast h_subst ) ( sub_nonneg_of_le ( mod_cast hv.le ) );
        norm_num [ ← @Int.cast_le ℚ ] at * ; linarith;
      -- Factor out $(v - u)$ from the right-hand side.
      have h_factor : p.leadingCoeff * p.natDegree * (u : ℤ) ^ (p.natDegree - 1) - Hzero p * (p.natDegree - 1) * (6 / 5 : ℚ) * (u : ℚ) ^ (p.natDegree - 2) > 0 := by
        have h_factor : p.leadingCoeff * p.natDegree * (u : ℚ) > Hzero p * (p.natDegree - 1) * (6 / 5 : ℚ) := by
          have h_factor : p.leadingCoeff * (u : ℚ) ≥ 4 * Hzero p := by
            exact_mod_cast h_u_ge_4H0_div_A u hu;
          by_cases hHzero : Hzero p = 0;
          · exact absurd hHzero ( by exact ne_of_gt ( add_pos_of_pos_of_nonneg hA ( Finset.sum_nonneg fun _ _ => abs_nonneg _ ) ) );
          · nlinarith [ show ( p.natDegree : ℚ ) ≥ 2 by norm_cast, show ( Hzero p : ℚ ) > 0 by exact_mod_cast lt_of_le_of_ne ( by
                                                                    exact add_nonneg hA.le ( Finset.sum_nonneg fun _ _ => abs_nonneg _ ) ) ( Ne.symm hHzero ) ];
        rcases k : p.natDegree with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
        convert mul_lt_mul_of_pos_right h_factor ( pow_pos ( Nat.cast_pos.mpr ( show 0 < u from Nat.pos_of_ne_zero ( by rintro rfl; exact absurd hu ( by unfold explicitTailParam; aesop ) ) ) ) _ ) using 1 ; ring;
      exact_mod_cast lt_of_sub_pos ( h_subst.trans_lt' ( by nlinarith [ ( by norm_cast : ( u : ℚ ) < v ) ] ) );
    · interval_cases _ : p.natDegree ; simp_all +decide [ Polynomial.eval_eq_sum_range ];
      simp_all +decide [ Finset.sum_range_succ, Polynomial.leadingCoeff, Polynomial.natDegree ]
  have h_bound : p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ) := by
    -- Using the upper bound for $p(v)$ and the lower bound for $p(u)$, we get:
    have h_upper_bound : p.eval (v : ℤ) ≤ p.leadingCoeff * (v : ℤ) ^ p.natDegree + Hzero p * (v : ℤ) ^ (p.natDegree - 1) := by
      apply eval_upper_bound p v (by linarith) hA
    have h_lower_bound : p.eval (u : ℤ) ≥ p.leadingCoeff * (u : ℤ) ^ p.natDegree - Hzero p * (u : ℤ) ^ (p.natDegree - 1) := by
      apply eval_lower_bound p u (by
      contrapose! hu; interval_cases u ; simp_all +decide [ explicitTailParam ] ;
      exact Or.inl ⟨ hd, by linarith ⟩) hA;
    -- Using the fact that $v \leq u + G$ and $u \geq 6dG$, we can bound $v^d$ and $v^{d-1}$.
    have h_v_bound : (v : ℚ) ^ p.natDegree ≤ (6 / 5 : ℚ) * (u : ℚ) ^ p.natDegree := by
      have h_v_bound : (v : ℚ) ≤ (1 + 1 / (6 * p.natDegree : ℚ)) * (u : ℚ) := by
        field_simp;
        norm_cast;
        nlinarith [ show explicitTailParam p G ≥ 6 * p.natDegree * G by exact le_max_left _ _ ];
      refine le_trans ( pow_le_pow_left₀ ( by positivity ) h_v_bound _ ) ?_;
      rw [ mul_pow ];
      exact mul_le_mul_of_nonneg_right ( by exact le_trans ( elementary_ratio_bound _ hd ) ( by norm_num ) ) ( by positivity );
    -- Using the fact that $v \leq u + G$ and $u \geq 6dG$, we can bound $v^{d-1}$.
    have h_v_bound_prev : (v : ℚ) ^ (p.natDegree - 1) ≤ (u : ℚ) ^ (p.natDegree - 1) * (1 + 1 / (6 * p.natDegree : ℚ)) ^ (p.natDegree - 1) := by
      have h_v_bound_prev : (v : ℚ) ≤ (u : ℚ) * (1 + 1 / (6 * p.natDegree : ℚ)) := by
        field_simp;
        norm_cast;
        nlinarith [ show explicitTailParam p G ≥ 6 * p.natDegree * G by exact le_max_left _ _ ];
      simpa only [ ← mul_pow ] using pow_le_pow_left₀ ( by positivity ) h_v_bound_prev _;
    -- Using the fact that $(1 + 1/(6d))^{d-1} \leq 6/5$, we can further bound $v^{d-1}$.
    have h_v_bound_prev_final : (v : ℚ) ^ (p.natDegree - 1) ≤ (u : ℚ) ^ (p.natDegree - 1) * (6 / 5 : ℚ) := by
      refine le_trans h_v_bound_prev ?_;
      gcongr;
      have := elementary_ratio_bound ( p.natDegree ) hd;
      exact le_trans ( pow_le_pow_right₀ ( le_add_of_nonneg_right <| by positivity ) ( Nat.pred_le _ ) ) this;
    -- Substitute the bounds into the inequality.
    have h_subst : p.leadingCoeff * (6 / 5 : ℚ) * (u : ℚ) ^ p.natDegree + Hzero p * (u : ℚ) ^ (p.natDegree - 1) * (6 / 5 : ℚ) ≤ 2 * (p.leadingCoeff * (u : ℚ) ^ p.natDegree - Hzero p * (u : ℚ) ^ (p.natDegree - 1)) := by
      have := h_u_ge_4H0_div_A u hu; norm_num [ ← @Int.cast_le ℚ ] at *; rcases k : p.natDegree with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ] ;
      · linarith [ h_u_ge_4H0_div_A u hu ];
      · nlinarith [ h_u_ge_4H0_div_A u hu, show ( 0 : ℚ ) ≤ u * u ^ ‹_› by positivity ];
    rw [ ← @Int.cast_le ℚ ] at * ; norm_num at *;
    refine le_trans h_upper_bound ?_;
    refine le_trans ?_ ( h_subst.trans ?_ );
    · refine add_le_add ?_ ?_;
      · simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left h_v_bound <| by positivity;
      · rw [ mul_assoc ] ; gcongr;
        exact_mod_cast add_nonneg ( le_of_lt hA ) ( Finset.sum_nonneg fun _ _ => abs_nonneg _ );
    · exact mul_le_mul_of_nonneg_left ( by linarith [ ( by norm_cast : ( p.leadingCoeff : ℚ ) * u ^ p.natDegree ≤ eval ( u : ℤ ) p + Hzero p * u ^ ( p.natDegree - 1 ) ) ] ) zero_le_two
  exact ⟨h_pos, h_mono, h_bound⟩

/-
Construction of signed a-blocks via iterated finite differences and Bézout's identity.
-/

open Polynomial BigOperators Finset

/-! ## Evaluation lemma for diffOp -/

def stepPN (h : ℕ) (pn : Finset ℕ × Finset ℕ) : Finset ℕ × Finset ℕ :=
  (pn.1.image (· + h) ∪ pn.2, pn.1 ∪ pn.2.image (· + h))

/-- Build the (P, N) pair from a list of shifts, starting from ({0}, ∅). -/
def buildPN (shifts : List ℕ) : Finset ℕ × Finset ℕ :=
  shifts.foldl (fun pn h => stepPN h pn) ({0}, ∅)

/-
Evaluation identity for a single stepPN step.
-/
lemma stepPN_eval (p : Polynomial ℤ) (h : ℕ) (f : Polynomial ℤ) (P N : Finset ℕ)
    (hf : ∀ x : ℤ, f.eval x = ∑ u ∈ P, p.eval (x + ↑u) - ∑ v ∈ N, p.eval (x + ↑v))
    (hh : ∀ u ∈ P ∪ N, u < h) :
    ∀ x : ℤ, (diffOp (↑h) f).eval x =
      ∑ u ∈ (stepPN h (P, N)).1, p.eval (x + ↑u) -
      ∑ v ∈ (stepPN h (P, N)).2, p.eval (x + ↑v) := by
  intro x
  unfold stepPN;
  rw [ Finset.sum_union, Finset.sum_union ] <;> norm_num [ hf ];
  · unfold diffOp; simp +decide [ hf ] ; ring_nf;
  · simp_all +decide [ Finset.disjoint_right ];
    exact fun u hu => fun hu' => by linarith [ hh _ ( Or.inl hu' ), hh _ ( Or.inr hu ) ] ;
  · simp_all +decide [ Finset.disjoint_left ];
    grind

/-
Disjointness is preserved by stepPN when the shift is large enough.
-/
lemma stepPN_disjoint (h : ℕ) (P N : Finset ℕ) (hPN : Disjoint P N)
    (hh : ∀ u ∈ P ∪ N, u < h) :
    Disjoint (stepPN h (P, N)).1 (stepPN h (P, N)).2 := by
  simp_all +decide [ Finset.disjoint_left, stepPN ];
  grind
theorem foldl_eval_eq_pn (p : Polynomial ℤ) (shifts : List ℕ)
    (h_inc : ∀ i : Fin shifts.length,
      ∀ u ∈ (buildPN (shifts.take i)).1 ∪ (buildPN (shifts.take i)).2,
        u < shifts[i]) :
    let pn := buildPN shifts
    (Disjoint pn.1 pn.2) ∧
    (∀ x : ℤ,
      ((shifts.map (fun h => (h : ℤ))).foldl (fun f hi => diffOp hi f) p).eval x =
        ∑ u ∈ pn.1, p.eval (x + ↑u) - ∑ v ∈ pn.2, p.eval (x + ↑v)) := by
  induction' shifts using List.reverseRecOn with shifts' shifts_ih <;> simp_all +decide [ buildPN ];
  rename_i h; specialize h ( fun i u hu => ?_ ) ; simp_all +decide [ List.take_append ] ;
  · specialize h_inc ⟨ i, by simp +decide ⟩ u ; simp_all +decide ;
  · refine' ⟨ stepPN_disjoint _ _ _ h.1 _, fun x => _ ⟩;
    · specialize h_inc ⟨ shifts'.length, by simp +decide ⟩ ; aesop;
    · convert stepPN_eval p shifts_ih _ _ _ h.2 _ x using 1;
      specialize h_inc ⟨ shifts'.length, by simp +decide ⟩ ; aesop;

/-- The canonical r-shifts: [1, 2, 4, ..., 2^{d-1}] -/
def canonicalR (d : ℕ) : List ℕ := List.ofFn (fun i : Fin d => 2 ^ (i : ℕ))

/-- The canonical s-shifts: [1, 3, 7, ..., 2^d - 1] -/
def canonicalS (d : ℕ) : List ℕ := List.ofFn (fun i : Fin d => 2 ^ ((i : ℕ) + 1) - 1)

/-
The r-shifts satisfy the increasing condition needed for buildPN.
-/
lemma canonicalR_inc (d : ℕ) (i : Fin (canonicalR d).length)
    (u : ℕ) (hu : u ∈ (buildPN ((canonicalR d).take i)).1 ∪
                      (buildPN ((canonicalR d).take i)).2) :
    u < (canonicalR d)[i] := by
  -- By definition of `buildPN`, all elements of `buildPN (List.take i (canonicalR d))` are less than `2^i`.
  have h_bound : ∀ i : ℕ, (∀ u ∈ (buildPN (List.take i (canonicalR d))).1 ∪ (buildPN (List.take i (canonicalR d))).2, u < 2 ^ i) := by
    intro i;
    induction' i with i ih;
    · grind +locals;
    · rcases d with ( _ | d ) <;> simp_all +decide [ List.take_add_one ];
      · fin_cases i;
      · grind +locals;
  unfold canonicalR at *; aesop;

/-
The s-shifts satisfy the increasing condition needed for buildPN.
-/
lemma canonicalS_inc (d : ℕ) (i : Fin (canonicalS d).length)
    (u : ℕ) (hu : u ∈ (buildPN ((canonicalS d).take i)).1 ∪
                      (buildPN ((canonicalS d).take i)).2) :
    u < (canonicalS d)[i] := by
  have h_ind : ∀ k, ∀ u ∈ (buildPN ((canonicalS d).take k)).1 ∪ (buildPN ((canonicalS d).take k)).2, u < 2 ^ (k + 1) - 1 := by
    intro k;
    induction' k with k ih;
    · simp +decide [ buildPN ];
    · rw [ List.take_add_one ];
      cases h : ( canonicalS d)[k]? <;> simp_all +decide [ buildPN ];
      · exact fun u hu => lt_of_lt_of_le ( ih u hu ) ( Nat.sub_le_sub_right ( pow_le_pow_right₀ ( by decide ) ( Nat.le_succ _ ) ) _ );
      · grind +locals;
  grind +locals

/-
Using canonicalR, we get a signed block for a * ∏ 2^i = a * 2^{d(d-1)/2}.
-/
theorem signed_block_r (p : Polynomial ℤ) (hd : 1 ≤ p.natDegree) :
    let d := p.natDegree
    let a := p.leadingCoeff * (d.factorial : ℤ)
    let pn := buildPN (canonicalR d)
    Disjoint pn.1 pn.2 ∧
    (∀ x : ℤ,
      ∑ u ∈ pn.1, p.eval (x + ↑u) - ∑ v ∈ pn.2, p.eval (x + ↑v) =
        a * ∏ i : Fin d, (2 ^ (i : ℕ) : ℤ)) := by
  have := @foldl_eval_eq_pn;
  specialize this p (canonicalR p.natDegree) (canonicalR_inc p.natDegree);
  have := iterated_diff_const p p.natDegree rfl hd ( fun i => 2 ^ ( i : ℕ ) ) ; simp_all +decide ;
  have h_foldl_eq : List.foldl (fun f hi => diffOp hi f) p (List.flatMap (fun a => [↑a]) (canonicalR p.natDegree)) = List.foldl (fun f hi => diffOp hi f) p (List.ofFn (fun i : Fin p.natDegree => (2 ^ (i : ℕ) : ℤ))) := by
    unfold canonicalR; simp +decide [ List.ofFn_eq_map ] ;
    induction ( List.finRange p.natDegree ) using List.reverseRecOn <;> aesop;
  simp_all +decide [ Polynomial.eval_mul, Polynomial.eval_prod ];
  exact fun x => Eq.symm ( by rename_i h; exact h.2 x )

/-
Using canonicalS, we get a signed block for a * ∏ (2^{i+1} - 1).
-/
theorem signed_block_s (p : Polynomial ℤ) (hd : 1 ≤ p.natDegree) :
    let d := p.natDegree
    let a := p.leadingCoeff * (d.factorial : ℤ)
    let pn := buildPN (canonicalS d)
    Disjoint pn.1 pn.2 ∧
    (∀ x : ℤ,
      ∑ u ∈ pn.1, p.eval (x + ↑u) - ∑ v ∈ pn.2, p.eval (x + ↑v) =
        a * ∏ i : Fin d, ((2 ^ ((i : ℕ) + 1) : ℤ) - 1)) := by
  refine' ⟨ _, _ ⟩;
  · convert foldl_eval_eq_pn p ( canonicalS p.natDegree ) ( canonicalS_inc p.natDegree ) |>.1;
  · -- Apply the foldl_eval_eq_pn theorem to the canonicalS shifts.
    have h_foldl : (List.foldl (fun f hi => diffOp hi f) p (canonicalS p.natDegree |>.map (fun h => (h : ℤ)))) = Polynomial.C (p.leadingCoeff * (p.natDegree.factorial : ℤ) * ∏ i : Fin p.natDegree, (2 ^ ((i : ℕ) + 1) - 1 : ℤ)) := by
      convert iterated_diff_const p p.natDegree rfl hd _ _ using 1;
      · unfold canonicalS;
        norm_num [ List.ofFn_eq_map ];
        induction ( List.finRange p.natDegree ) using List.reverseRecOn <;> aesop;
      · exact fun i => ne_of_gt ( sub_pos_of_lt ( one_lt_pow₀ one_lt_two ( Nat.succ_ne_zero _ ) ) );
    convert foldl_eval_eq_pn p ( canonicalS p.natDegree ) ( canonicalS_inc p.natDegree ) using 1;
    constructor <;> intro h <;> simp_all +decide;
    · exact ⟨ by exact ( foldl_eval_eq_pn p ( canonicalS p.natDegree ) ( canonicalS_inc p.natDegree ) ) |>.1, fun x => Or.inl <| by simp +decide [ Polynomial.eval_prod ] ⟩;
    · intro x; specialize h; replace h := h.2 x; simp_all +decide [ Polynomial.eval_prod ] ;

/-! ## Bézout step -/
lemma buildPN_canonicalR_bound (d : ℕ) :
    (∀ u ∈ (buildPN (canonicalR d)).1, u < 2 ^ d) ∧
    (∀ u ∈ (buildPN (canonicalR d)).2, u < 2 ^ d) := by
  induction' d with d ih;
  · decide +revert;
  · -- By definition of `buildPN`, we have:
    have h_buildPN_succ : buildPN (canonicalR (d + 1)) = stepPN (2 ^ d) (buildPN (canonicalR d)) := by
      unfold buildPN canonicalR;
      rw [ List.ofFn_succ' ] ; aesop;
    simp_all +decide [ stepPN, pow_succ' ];
    grind

/-
All elements produced by buildPN with canonicalS shifts are < 2^(d+1).
-/
lemma buildPN_canonicalS_bound (d : ℕ) :
    (∀ u ∈ (buildPN (canonicalS d)).1, u < 2 ^ (d + 1)) ∧
    (∀ u ∈ (buildPN (canonicalS d)).2, u < 2 ^ (d + 1)) := by
  induction' d with d ih;
  · decide +revert;
  · -- By definition of `canonicalS`, we have `canonicalS (d + 1) = canonicalS d ++ [2 ^ (d + 1) - 1]`.
    have h_canonicalS_succ : canonicalS (d + 1) = canonicalS d ++ [2 ^ (d + 1) - 1] := by
      unfold canonicalS;
      rw [ List.ofFn_succ' ] ; aesop;
    -- Apply the buildPN function to the list `canonicalS d ++ [2 ^ (d + 1) - 1]`.
    have h_buildPN_succ : buildPN (canonicalS d ++ [2 ^ (d + 1) - 1]) = stepPN (2 ^ (d + 1) - 1) (buildPN (canonicalS d)) := by
      unfold buildPN; aesop;
    simp_all +decide [ stepPN ];
    grind +qlia

/-
For coprime positive naturals m, n, there exist a ≤ n and b < m with a*m = b*n + 1.
-/
lemma nat_bezout_bounded (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n) :
    ∃ (a b : ℕ), a * m = b * n + 1 ∧ a ≤ n ∧ b < m := by
  -- Let $a$ be the smallest positive integer such that $a * m \equiv 1 \mod n$.
  obtain ⟨a, ha⟩ : ∃ a : ℕ, 0 < a ∧ a ≤ n ∧ a * m ≡ 1 [MOD n] := by
    have := Nat.exists_mul_mod_eq_one_of_coprime hcop;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ mul_comm, Nat.ModEq ];
    · exact ⟨ 1, by norm_num, by norm_num, Nat.mod_one _ ⟩;
    · exact ⟨ this.choose, Nat.pos_of_ne_zero fun h => by simpa [ h ] using this.choose_spec.2, Nat.le_succ_of_le this.choose_spec.1, this.choose_spec.2 ⟩;
  exact ⟨ a, ( a * m - 1 ) / n, by linarith [ Nat.div_mul_cancel ( show n ∣ a * m - 1 from by rw [ ← Int.natCast_dvd_natCast ] ; simpa [ Nat.cast_sub ( show 1 ≤ a * m from Nat.mul_pos ha.1 hm ) ] using ha.2.2.symm.dvd ), Nat.sub_add_cancel ( show 1 ≤ a * m from Nat.mul_pos ha.1 hm ) ], ha.2.1, Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.sub_add_cancel ( show 1 ≤ a * m from Nat.mul_pos ha.1 hm ) ] ⟩

/-
The products ∏ 2^i and ∏ (2^{i+1}-1) are coprime (one is a power of 2, the other is odd).
-/
lemma prod_r_s_coprime (d : ℕ) :
    Nat.Coprime (∏ i : Fin d, 2 ^ (i : ℕ)) (∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1)) := by
  norm_num [ Nat.coprime_prod_left_iff, Nat.coprime_prod_right_iff ];
  exact fun i j => Nat.Coprime.pow_left _ ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by rw [ ← even_iff_two_dvd ] ; simp +decide [ Nat.one_le_iff_ne_zero, parity_simps ] )

/-
∏_{i<d} 2^i = 2^{d(d-1)/2}
-/
lemma prod_r_eq (d : ℕ) : ∏ i : Fin d, 2 ^ (i : ℕ) = 2 ^ (d * (d - 1) / 2) := by
  rw [ Finset.prod_pow_eq_pow_sum ];
  exact congrArg _ ( Eq.symm <| Nat.div_eq_of_eq_mul_left zero_lt_two <| Nat.recOn d ( by norm_num ) fun n ih => by cases n <;> norm_num [ Fin.sum_univ_castSucc ] at * ; linarith )

/-
∏_{i<d} (2^{i+1}-1) ≤ 2^{d(d+1)/2}
-/
lemma prod_s_bound (d : ℕ) :
    ∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1) ≤ 2 ^ (d * (d + 1) / 2) := by
  refine' le_trans ( Finset.prod_le_prod' fun i _ => show ( 2 ^ ( i + 1 : ℕ ) - 1 : ℕ ) ≤ 2 ^ ( i + 1 : ℕ ) from Nat.sub_le _ _ ) _;
  rw [ Finset.prod_pow_eq_pow_sum ];
  exact pow_le_pow_right₀ ( by decide ) ( Nat.le_div_iff_mul_le zero_lt_two |>.2 <| Nat.recOn d ( by norm_num ) fun n ih => by norm_num [ Fin.sum_univ_castSucc ] at * ; linarith )

/-
∏_{i<d} (2^{i+1}-1) + 2^{d(d-1)/2} < 2^{d(d-1)/2+d+1} for d ≥ 1
-/
lemma prod_sum_bound (d : ℕ) (hd : 1 ≤ d) :
    ∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1) + 2 ^ (d * (d - 1) / 2) <
    2 ^ (d * (d - 1) / 2 + d + 1) := by
  have prod_s_bound' : ∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1 : ℕ) ≤ 2 ^ (d * (d + 1) / 2) :=
    prod_s_bound d
  rw [ show d * ( d + 1 ) / 2 = d * ( d - 1 ) / 2 + d by
        cases d <;> norm_num [ Nat.mul_succ, Nat.add_mul_div_left ] ; omega ] at prod_s_bound';
  norm_num [ pow_add ] at *;
  nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( d * ( d - 1 ) / 2 ), pow_le_pow_right₀ ( show 1 ≤ 2 by norm_num ) hd ]

/-
Bounded Bézout coefficients for canonical products:
    ∃ λ μ : ℕ, λ·Π(r) - μ·Π(s) = 1 and λ+μ < 2^{d(d-1)/2+d+1}.
-/
lemma bounded_bezout_canonical (d : ℕ) (hd : 1 ≤ d) :
    ∃ (lam mu : ℕ),
      (lam : ℤ) * ∏ i : Fin d, (2 ^ (i : ℕ) : ℤ) -
      (mu : ℤ) * ∏ i : Fin d, ((2 ^ ((i : ℕ) + 1) : ℤ) - 1) = 1 ∧
      lam + mu < 2 ^ (d * (d - 1) / 2 + d + 1) := by
  -- Use nat_bezout_bounded with m = ∏ 2^i (= 2^{d(d-1)/2} by prod_r_eq) and n = ∏(2^{i+1}-1), which are coprime by prod_r_s_coprime.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, a * (∏ i : Fin d, 2 ^ (i : ℕ)) = b * (∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1)) + 1 ∧ a ≤ (∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1)) ∧ b < (∏ i : Fin d, 2 ^ (i : ℕ)) := by
    apply nat_bezout_bounded;
    · exact Finset.prod_pos fun _ _ => pow_pos ( by decide ) _;
    · exact Finset.prod_pos fun i _ => Nat.sub_pos_of_lt ( by norm_num );
    · exact prod_r_s_coprime d;
  refine' ⟨ a, b, _, _ ⟩ <;> norm_cast;
  · rw [ Finset.prod_congr rfl fun _ _ => Int.subNatNat_of_le ( Nat.one_le_pow _ _ ( by decide ) ) ] ; norm_num [ hab ];
  · refine' lt_of_le_of_lt ( add_le_add hab.2.1 hab.2.2.le ) _;
    convert prod_sum_bound d hd using 1;
    exact congrArg _ ( mod_cast prod_r_eq d )

/-! ===== Main Theorem Infrastructure ===== -/

/-
Every N ≥ C(p; R, B) is a sum of distinct positive values p(n).
This establishes the existence of thresholds and the bound θ_p ≤ C(p; R, B).

We formalize the key components:
1. The notion of a "threshold" for a polynomial
2. The existence of thresholds given residue data and signed blocks
3. The optimized explicit bound
-/

open Polynomial BigOperators Finset

/-! ## Threshold definition -/

/-- A threshold for p: every N ≥ C is representable as a sum of distinct
    positive values p(n) with distinct indices. -/
def IsThreshold (p : Polynomial ℤ) (C : ℕ) : Prop :=
  ∀ N : ℕ, C ≤ N →
    ∃ J : Finset ℕ, (∀ j ∈ J, 0 < j) ∧
      (N : ℤ) = ∑ i ∈ J, p.eval (i : ℤ)

/-! ## Residue datum definition -/

/-- A residue datum modulo a for p is:
    - A finite set E ⊆ ℕ
    - For each r ∈ {0, ..., a-1}, a subset F_r ⊆ E
    - Such that ∑_{e ∈ F_r} p(e) ≡ r (mod a) -/
structure ResidueDatum (p : Polynomial ℤ) (a : ℕ) where
  E : Finset ℕ
  F : Fin a → Finset ℕ
  hF_sub : ∀ r, F r ⊆ E
  hF_mod : ∀ r, (a : ℤ) ∣ (∑ e ∈ F r, p.eval (e : ℤ) - (r : ℤ))

/-- e(R) = max(E ∪ {0}) -/
noncomputable def ResidueDatum.eMax {p : Polynomial ℤ} {a : ℕ} (R : ResidueDatum p a) : ℕ :=
  R.E.sup id

/-! ## Signed a-block: uses SignedBlock from Defs.lean -/
theorem tauProp_pos' {p : Polynomial ℤ} {G T : ℕ} (hG : 1 ≤ G)
    (hT : TauProp p G T) {u : ℕ} (hu : T ≤ u) :
    0 < p.eval (u : ℤ) :=
  (hT u (u + 1) hu (by omega) (by omega)).1

theorem polyA_pos {p : Polynomial ℤ} (hA : 0 < p.leadingCoeff) :
    0 < polyA p := by
  unfold polyA; exact mul_pos hA (Nat.cast_pos.mpr (Nat.factorial_pos _))

theorem polyA_natAbs_pos {p : Polynomial ℤ} (hA : 0 < p.leadingCoeff) : 0 < (polyA p).natAbs :=
  Int.natAbs_pos.mpr (ne_of_gt (polyA_pos hA))

/-! ## Key construction lemma

The construction uses:
- Shifted residue sums at R₀ = a*(T+1)
- Q-1 copies of the signed block at positions Y, Y+(L+1), ...
- The index set I = (shifted E) ∪ (block copies)
- The threshold C₀ = M - a + 1 + Σ β_i
-/

noncomputable def residueM
    (p : Polynomial ℤ) (a : ℕ) (ha : 0 < a)
    (R : ResidueDatum p a) (R₀ : ℕ) : ℤ :=
  Finset.univ.sup' ⟨⟨0, ha⟩, Finset.mem_univ _⟩
    (fun r => ∑ e ∈ R.F r, p.eval ((R₀ : ℤ) + e))

/-
Bound on residue M: if |F_r| ≤ card_bound and all indices ≤ X_bound,
    then M ≤ card_bound * p_+(X_bound).
-/
theorem residueM_le (p : Polynomial ℤ) (a : ℕ) (ha : 0 < a)
    (R : ResidueDatum p a) (R₀ : ℕ)
    (X_bound : ℕ) (hX : ∀ e ∈ R.E, R₀ + e ≤ X_bound)
    (card_bound : ℕ) (hcard : ∀ r : Fin a, (R.F r).card ≤ card_bound) :
    residueM p a ha R R₀ ≤ ↑card_bound * (posMajorant p).eval (X_bound : ℤ) := by
  have h_eval_le : ∀ r : Fin a, ∑ e ∈ R.F r, p.eval ((R₀ : ℤ) + e) ≤ card_bound * (posMajorant p).eval (X_bound : ℤ) := by
    intros r
    have h_eval_le : ∀ e ∈ R.F r, p.eval ((R₀ : ℤ) + e) ≤ (posMajorant p).eval (X_bound : ℤ) := by
      intros e he
      have h_eval_le : p.eval ((R₀ : ℤ) + e) ≤ (posMajorant p).eval ((R₀ : ℤ) + e) := by
        unfold posMajorant;
        simp +decide [ Polynomial.eval_finset_sum, Polynomial.sum_def ];
        rw [ Polynomial.eval_eq_sum, Polynomial.sum_def ];
        exact Finset.sum_le_sum fun i hi => by cases max_cases ( p.coeff i ) 0 <;> nlinarith [ pow_nonneg ( by positivity : 0 ≤ ( R₀ : ℤ ) + e ) i ] ;
      have h_eval_le' : (posMajorant p).eval ((R₀ : ℤ) + e) ≤ (posMajorant p).eval (X_bound : ℤ) := by
        convert posMajorant_nondecreasing p ( R₀ + e ) X_bound ( by linarith [ hX e ( R.hF_sub r he ) ] ) using 1
      exact le_trans h_eval_le h_eval_le';
    exact le_trans ( Finset.sum_le_sum h_eval_le ) ( by simpa using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr ( hcard r ) ) ( show 0 ≤ eval ( X_bound : ℤ ) ( posMajorant p ) from by
                                                                                                                                  unfold posMajorant;
                                                                                                                                  simp +decide [ Polynomial.eval_finset_sum, Polynomial.sum_def ];
                                                                                                                                  exact Finset.sum_nonneg fun _ _ => mul_nonneg ( le_max_right _ _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ) );
  unfold residueM; aesop;

/-
For the canonical one-generator residue datum, elements of E are
    spaced by at least a. This gives g(E) ≤ 2.

    More precisely: if E = image (fun j => u + j*a) (range (a-1)),
    then for e, f ∈ E with e < f, we have f - e ≥ a ≥ 2.
-/
set_option maxHeartbeats 1600000 in
theorem canonical_residue_spaced (p : Polynomial ℤ) (a : ℕ) (ha : 0 < a)
    (hgcd : ∀ ℓ, Nat.Prime ℓ → (ℓ : ℤ) ∣ (a : ℤ) →
      ∃ n : ℕ, 0 < n ∧ ¬ (ℓ : ℤ) ∣ p.eval (n : ℤ)) :
    ∃ R : ResidueDatum p a,
      R.eMax ≤ a * a ∧
      (∀ r, (R.F r).card ≤ a) ∧
      -- Gap property: in the shifted set R₀ + E, no two elements are consecutive
      -- (when a ≥ 2), because elements of E are spaced by multiples of a
      (∀ e ∈ R.E, ∀ f ∈ R.E, e < f → a ≤ f - e) := by
  by_contra! h_contra;
  obtain ⟨u, hu_pos, hu_le, hu_coprime⟩ : ∃ u : ℕ, 0 < u ∧ u ≤ a ∧ Nat.Coprime (Int.natAbs (p.eval (u : ℤ))) a := by
    by_cases ha1 : a = 1;
    · aesop;
    · convert unit_value_mod_a p a ( lt_of_le_of_ne ha ( Ne.symm ha1 ) ) hgcd using 1;
  obtain ⟨c, hc⟩ : ∃ c : Fin a → ℕ, (∀ r : Fin a, ∑ e ∈ Finset.range (c r), p.eval ((u + e * a : ℤ)) ≡ r [ZMOD a]) ∧ (∀ r : Fin a, c r ≤ a - 1) := by
    have h_sum_mod : ∀ k : ℕ, ∑ e ∈ Finset.range k, p.eval ((u + e * a : ℤ)) ≡ k * p.eval (u : ℤ) [ZMOD a] := by
      intro k; induction k <;> simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, Finset.sum_range_succ ] ;
      simp_all +decide [ add_mul, Polynomial.eval_eq_sum_range ];
    -- Since $p(u)$ is coprime to $a$, there exists an integer $k$ such that $k * p(u) \equiv r \pmod{a}$ for each $r$.
    have h_exists_k : ∀ r : Fin a, ∃ k : ℕ, k < a ∧ k * p.eval (u : ℤ) ≡ r [ZMOD a] := by
      intro r
      obtain ⟨k, hk⟩ : ∃ k : ℤ, k * p.eval (u : ℤ) ≡ r [ZMOD a] := by
        have := Int.gcd_eq_gcd_ab ( p.eval ( u : ℤ ) ) a;
        exact ⟨ r * Int.gcdA ( p.eval ( u : ℤ ) ) a, by rw [ Int.modEq_iff_dvd ] ; use Int.gcdB ( p.eval ( u : ℤ ) ) a * r; nlinarith [ show Int.gcd ( p.eval ( u : ℤ ) ) a = 1 from by simpa [ Int.gcd_eq_natAbs ] using hu_coprime ] ⟩;
      exact ⟨ Int.toNat ( k % a ), by linarith [ Int.emod_lt_of_pos k ( by positivity : 0 < ( a : ℤ ) ), Int.toNat_of_nonneg ( Int.emod_nonneg k ( by positivity : ( a : ℤ ) ≠ 0 ) ) ], by simpa [ Int.ModEq, Int.mul_emod, Int.toNat_of_nonneg ( Int.emod_nonneg k ( by positivity : ( a : ℤ ) ≠ 0 ) ) ] using hk ⟩;
    choose k hk₁ hk₂ using h_exists_k;
    exact ⟨ k, fun r => Eq.trans ( h_sum_mod _ ) ( hk₂ _ ), fun r => Nat.le_sub_one_of_lt ( hk₁ _ ) ⟩;
  refine' absurd ( h_contra ⟨ Finset.image ( fun e : ℕ => u + e * a ) ( Finset.range ( a - 1 ) ), fun r => Finset.image ( fun e : ℕ => u + e * a ) ( Finset.range ( c r ) ), _, _ ⟩ _ _ ) _;
  all_goals norm_num [ Finset.subset_iff, ResidueDatum.eMax ];
  · exact fun r i hi => ⟨ i, lt_of_lt_of_le hi ( hc.2 r ), Or.inl rfl ⟩;
  · intro r; specialize hc; have := hc.1 r; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_eq_intCast_iff ] ;
    rw [ Finset.sum_image ] <;> norm_num [ hc.1 ];
    exact fun x hx y hy hxy => by nlinarith;
  · exact fun b hb => by nlinarith [ Nat.sub_add_cancel ha ] ;
  · exact fun r => Finset.card_image_le.trans ( by simpa using hc.2 r |> le_trans <| Nat.pred_le _ );
  · exact fun x hx y hy hxy => by rw [ Nat.le_sub_iff_add_le ] <;> nlinarith [ show x < y from by nlinarith ] ;

/-- Monotonicity of TauProp in the gap parameter G. -/
theorem tauProp_mono_G {p : Polynomial ℤ} {G G' T : ℕ}
    (hT : TauProp p G' T) (hle : G ≤ G') : TauProp p G T :=
  fun u v hu hv hvG => hT u v hu hv (by omega)

/-
Monotonicity of explicitTailParam in G.
-/
theorem explicitTailParam_mono (p : Polynomial ℤ) (G G' : ℕ) (hle : G ≤ G') :
    explicitTailParam p G ≤ explicitTailParam p G' := by
  exact max_le_max ( by gcongr ) le_rfl

/-
For the refined construction: if R₀ is a multiple of a with
    R₀ = a * ((T₁+1+a-1)/a), then R₀ ≤ T₁ + a and T₁ + 1 ≤ R₀.
-/
theorem ceil_mul_bound (a T₁ : ℕ) (ha : 0 < a) :
    let R₀ := a * ((T₁ + 1 + a - 1) / a)
    T₁ + 1 ≤ R₀ ∧ R₀ ≤ T₁ + a ∧ a ∣ R₀ := by
  norm_num +zetaDelta at *;
  exact ⟨ by linarith [ Nat.div_add_mod ( T₁ + a ) a, Nat.mod_lt ( T₁ + a ) ha ], by linarith [ Nat.div_mul_le_self ( T₁ + a ) a ] ⟩

open Polynomial BigOperators Finset

noncomputable section

/-
Given an initial interval I covering [C₀, C₀+K-1] with all indices ≥ T+1,
positivity of p on [T, ∞), and a doubling property for consecutive non-I elements,
every N ≥ C₀ is representable.
-/
theorem isThreshold_of_data
    (p : Polynomial ℤ)
    (T : ℕ) (hT : 0 < T) (K : ℕ) (hK_val : (K : ℤ) = p.eval (T : ℤ))
    (I : Finset ℕ) (C₀ : ℤ)
    (hI_ge : ∀ i ∈ I, T + 1 ≤ i)
    (hI_rep : RepresentsInterval (fun j => p.eval (j : ℤ)) I C₀ K)
    (h_pos : ∀ n : ℕ, T ≤ n → 0 < p.eval (n : ℤ))
    (hDoubling : ∀ u v : ℕ, T ≤ u → u ∉ I → v ∉ I → u < v →
      (∀ w, u < w → w < v → w ∈ I) → p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ)) :
    IsThreshold p C₀.toNat := by
  -- Enumerate non-I elements ≥ T
  have hT_notI : T ∉ I := fun h => by linarith [hI_ge T h]
  obtain ⟨t, ht_ge, ht_notI, ht_mono, ht_surj⟩ :
      ∃ t : ℕ → ℕ, (∀ m, t m ≥ T) ∧ (∀ m, t m ∉ I) ∧
        (∀ m n, m < n → t m < t n) ∧ (∀ j, T ≤ j → j ∉ I → ∃ m, t m = j) := by
    have h_inf : Set.Infinite {j : ℕ | T ≤ j ∧ j ∉ I} :=
      Set.Infinite.diff (Set.Ici_infinite T) (Finset.finite_toSet I)
    exact ⟨fun m => Nat.nth (fun j => T ≤ j ∧ j ∉ I) m,
      fun m => (Nat.nth_mem_of_infinite h_inf m).1,
      fun m => (Nat.nth_mem_of_infinite h_inf m).2,
      fun m n mn => Nat.nth_strictMono h_inf mn,
      fun j hj1 hj2 => ⟨_, Nat.nth_count ⟨hj1, hj2⟩⟩⟩
  -- Apply interval_completion_nat
  have h_completion : ∀ N : ℤ, C₀ ≤ N → ∃ J : Finset ℕ,
      (∀ j ∈ J, j ∈ I ∨ ∃ m, j = t m) ∧ ∑ i ∈ J, p.eval (i : ℤ) = N := by
    apply interval_completion_nat _ I C₀ K t hI_rep ht_notI
    · exact fun m n mn h => mn (le_antisymm
        (le_of_not_gt fun hmn => by linarith [ht_mono _ _ hmn])
        (le_of_not_gt fun hmn => by linarith [ht_mono _ _ hmn]))
    · intro m; exact h_pos (t m) (ht_ge m)
    · intro m
      induction m with
      | zero =>
        have ht0 : t 0 = T := by
          obtain ⟨m, hm⟩ := ht_surj T le_rfl hT_notI
          exact le_antisymm (hm ▸ monotone_nat_of_le_succ
            (fun n => le_of_lt (ht_mono _ _ n.lt_succ_self)) (Nat.zero_le _)) (ht_ge 0)
        simp only [ht0, Finset.sum_range_zero, add_zero]
        omega
      | succ m ih =>
        rw [Finset.sum_range_succ]
        have h_doub := hDoubling (t m) (t (m + 1)) (ht_ge m) (ht_notI m) (ht_notI (m + 1))
          (ht_mono m (m + 1) m.lt_succ_self) (fun w hw1 hw2 => by
            by_contra hw3
            obtain ⟨k, hk⟩ := ht_surj w (by linarith [ht_ge m]) hw3
            have : m + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge fun h =>
              by linarith [ht_mono _ _ (lt_of_le_of_ne h (Ne.symm (by
                intro heq; rw [← heq] at hk; linarith)))])
            linarith [hk ▸ monotone_nat_of_le_succ
              (fun n => le_of_lt (ht_mono n (n+1) n.lt_succ_self)) this])
        linarith [ih]
  -- Conclude IsThreshold
  intro N hN
  obtain ⟨J, hJ1, hJ2⟩ := h_completion N (by linarith [Int.self_le_toNat C₀])
  exact ⟨J, fun j hj => by
    rcases hJ1 j hj with h | ⟨m, rfl⟩
    · exact Nat.lt_of_lt_of_le hT (by linarith [hI_ge j h])
    · exact Nat.lt_of_lt_of_le hT (ht_ge m),
    hJ2.symm⟩

/-
Given a residue datum R, signed block B, and parameters R₀, Y, K,
construct the initial interval set I and threshold C₀, and prove
RepresentsInterval.
-/
set_option maxHeartbeats 3200000 in
theorem represents_interval_construction
    (p : Polynomial ℤ)
    (a : ℕ) (ha : 0 < a) (ha_eq : (a : ℤ) = polyA p)
    (R : ResidueDatum p a) (B : SignedBlock p (polyA p))
    (R₀ : ℕ) (hR₀_div : (a : ℤ) ∣ (R₀ : ℤ))
    (Y : ℕ) (hY : R₀ + R.E.sup id + 2 ≤ Y)
    (K : ℕ) (_hK_pos : 0 < K)
    (hR₀_nonneg : ∀ r : Fin a, 0 ≤ ∑ e ∈ R.F r, p.eval ((R₀ : ℤ) + ↑e)) :
    let k : Fin a → ℤ := fun r => ∑ e ∈ R.F r, p.eval ((R₀ : ℤ) + ↑e)
    let M : ℤ := Finset.univ.sup' ⟨⟨0, ha⟩, Finset.mem_univ _⟩ k
    let Q : ℕ := (M + ↑K).toNat / a + 2
    let I_res : Finset ℕ := R.E.image (R₀ + ·)
    let I_block : Finset ℕ := (Finset.range (Q - 1)).biUnion
      (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·))
    let I : Finset ℕ := I_res ∪ I_block
    let C₁ : ℤ := ∑ i ∈ Finset.range (Q - 1),
      ∑ v ∈ B.N, p.eval ((↑Y + ↑i * (↑B.L + 1) : ℤ) + ↑v)
    let C₀ : ℤ := M - ↑a + 1 + C₁
    RepresentsInterval (fun j => p.eval (j : ℤ)) I C₀ K := by
  intro k M Q I_res I_block I C₁ C₀ N hN₁ hN₂;
  obtain ⟨r, hr⟩ : ∃ r : Fin a, ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q - 1 ∧ N = k r + (q - 1) * a + C₁ := by
    -- Since $N$ is in the interval $[C₀, C₀ + K - 1]$, we can find $r$ such that $k(r) \equiv N - C₁ \pmod{a}$.
    obtain ⟨r, hr⟩ : ∃ r : Fin a, k r ≡ N - C₁ [ZMOD a] ∧ k r ≤ M := by
      have h_residue : ∀ r : Fin a, ∃ r' : Fin a, k r' ≡ r [ZMOD a] := by
        intro r
        have h_residue : ∃ r' : Fin a, k r' ≡ r [ZMOD a] := by
          have h_cong : ∀ r : Fin a, ∃ r' : Fin a, k r' ≡ r [ZMOD a] := by
            intro r
            have h_cong : ∑ e ∈ R.F r, p.eval (R₀ + e : ℤ) ≡ r [ZMOD a] := by
              have h_cong : ∀ e ∈ R.F r, p.eval (R₀ + e : ℤ) ≡ p.eval (e : ℤ) [ZMOD a] := by
                intro e he; rw [ Int.modEq_comm, Int.modEq_iff_dvd ] ;
                exact dvd_trans hR₀_div ( by simpa using Polynomial.sub_dvd_eval_sub ( R₀ + e : ℤ ) e p );
              have := R.hF_mod r; simp_all +decide ;
              exact Int.ModEq.trans ( Int.ModEq.sum <| fun x hx => h_cong x hx ) ( Int.ModEq.symm <| Int.modEq_of_dvd this )
            exact ⟨ r, h_cong ⟩
          exact h_cong r;
        exact h_residue;
      obtain ⟨ r, hr ⟩ := h_residue ⟨ Int.toNat ( ( N - C₁ ) % a ), by linarith [ Int.emod_lt_of_pos ( N - C₁ ) ( by positivity : 0 < ( a : ℤ ) ), Int.toNat_of_nonneg ( Int.emod_nonneg ( N - C₁ ) ( by positivity : ( a : ℤ ) ≠ 0 ) ) ] ⟩;
      exact ⟨ r, by simpa [ Int.ModEq, Int.emod_nonneg _ ( by positivity : ( a : ℤ ) ≠ 0 ) ] using hr, Finset.le_sup' ( fun r => k r ) ( Finset.mem_univ r ) ⟩;
    obtain ⟨q, hq⟩ : ∃ q : ℤ, N = k r + (q - 1) * a + C₁ ∧ 1 ≤ q ∧ q ≤ Q - 1 := by
      obtain ⟨q, hq⟩ : ∃ q : ℤ, N = k r + (q - 1) * a + C₁ := by
        obtain ⟨ q, hq ⟩ := hr.1.symm.dvd;
        exact ⟨ -q + 1, by linarith ⟩;
      refine' ⟨ q, hq, _, _ ⟩ <;> norm_num [ Q ] at *;
      · nlinarith [ hR₀_nonneg r ];
      · rw [ max_eq_left ];
        · nlinarith [ Int.mul_ediv_add_emod ( M + K ) a, Int.emod_nonneg ( M + K ) ( by positivity : ( a : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( M + K ) ( by positivity : ( a : ℤ ) > 0 ), hR₀_nonneg r ];
        · exact add_nonneg ( le_trans ( hR₀_nonneg r ) hr.2 ) ( Nat.cast_nonneg _ );
    exact ⟨ r, Int.toNat q, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ q ) ], by omega, by simpa [ Int.toNat_of_nonneg ( by linarith : 0 ≤ q ) ] using hq.1 ⟩;
  obtain ⟨ q, hq₁, hq₂, rfl ⟩ := hr;
  refine' ⟨ Finset.image ( fun x => R₀ + x ) ( R.F r ) ∪ Finset.biUnion ( Finset.range ( q - 1 ) ) ( fun i => Finset.image ( fun x => Y + i * ( B.L + 1 ) + x ) B.P ) ∪ Finset.biUnion ( Finset.Ico ( q - 1 ) ( Q - 1 ) ) ( fun i => Finset.image ( fun x => Y + i * ( B.L + 1 ) + x ) B.N ), _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  · rintro x ( ⟨ y, hy, rfl ⟩ | ⟨ i, hi, y, hy, rfl ⟩ | ⟨ i, ⟨ hi₁, hi₂ ⟩, y, hy, rfl ⟩ ) <;> simp +decide [ I, I_res, I_block ];
    · exact Or.inl ( R.hF_sub r hy );
    · exact Or.inr ⟨ i, by omega, y, Or.inl hy, rfl ⟩;
    · exact Or.inr ⟨ i, hi₂, y, Or.inr hy, rfl ⟩;
  · rw [ Finset.sum_union, Finset.sum_union ];
    · rw [ Finset.sum_biUnion, Finset.sum_biUnion ];
      · rw [ Finset.sum_image, Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ ];
        · have h_block_sum : ∀ x : ℤ, ∑ u ∈ B.P, p.eval (x + u) - ∑ v ∈ B.N, p.eval (x + v) = polyA p := by
            exact B.hBlock;
          have h_block_sum : ∀ i : ℕ, ∑ u ∈ B.P, p.eval (Y + i * (B.L + 1) + u : ℤ) = ∑ v ∈ B.N, p.eval (Y + i * (B.L + 1) + v : ℤ) + polyA p := by
            exact fun i => by linear_combination h_block_sum ( Y + i * ( B.L + 1 ) ) ;
          simp_all +decide [ Finset.sum_add_distrib ];
          ring!;
        · linarith;
      · intros i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
        intro a ha x hx; contrapose! hij; nlinarith [ B.hN_bound a ha, B.hN_bound x hx ] ;
      · intros i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
        intro a ha x hx; contrapose! hij; nlinarith [ B.hP_bound a ha, B.hP_bound x hx ] ;
    · simp +decide [ Finset.disjoint_left ];
      rintro a x hx₁ y hy₁ rfl z hz₁ hz₂ w hw₁;
      nlinarith [ show x < z by omega, show y < B.L from B.hP_bound y hy₁, show w < B.L from B.hN_bound w hw₁ ];
    · simp +decide [ Finset.disjoint_left ];
      intro x hx; refine' ⟨ _, _ ⟩ <;> intros <;> nlinarith [ show x ≤ R.E.sup id from Finset.le_sup ( f := id ) ( R.hF_sub r hx ) ] ;

/-! ## Index bound -/

theorem construction_indices_ge
    (p : Polynomial ℤ)
    (a : ℕ) (_ha : 0 < a)
    (R : ResidueDatum p a) (B : SignedBlock p (polyA p))
    (R₀ Y Q T_min : ℕ)
    (hR₀_ge : T_min + 1 ≤ R₀)
    (hY : R₀ + R.E.sup id + 2 ≤ Y) :
    let I_res : Finset ℕ := R.E.image (R₀ + ·)
    let I_block : Finset ℕ := (Finset.range (Q - 1)).biUnion
      (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·))
    let I : Finset ℕ := I_res ∪ I_block
    ∀ i ∈ I, T_min + 1 ≤ i := by
  grind

end

open Polynomial BigOperators Finset

noncomputable section

/-- Λ_d = 2^{d(d-1)/2 + 2d + 2}, an upper bound for the signed block parameter L. -/
def lambdaD (d : ℕ) : ℕ := 2 ^ (d * (d - 1) / 2 + 2 * d + 2)

/-- X_p = 𝔗_p(2) + a² + a, bounding the largest residue index. -/
def coeffXp (p : Polynomial ℤ) : ℕ :=
  explicitTailParam p 2 + (polyA p).natAbs ^ 2 + (polyA p).natAbs

/-- M_p = a · p_+(X_p), bounding the maximum residue sum. -/
def coeffMp (p : Polynomial ℤ) : ℤ :=
  (polyA p).natAbs * (posMajorant p).eval (coeffXp p : ℤ)

/-- K_p = p_+(𝔗_p(2)), bounding K = p(τ_p(2)). -/
def coeffKp (p : Polynomial ℤ) : ℤ :=
  (posMajorant p).eval (explicitTailParam p 2 : ℤ)

/-- Q_p = ⌈(M_p + K_p)/a⌉, bounding the number of block copies needed. -/
def coeffQp (p : Polynomial ℤ) : ℕ :=
  (coeffMp p + coeffKp p).toNat / (polyA p).natAbs + 1

/-- Y_p = max(X_p + 2, 𝔗_p(Λ_d + 1) + 1), bounding the block start position. -/
def coeffYp (p : Polynomial ℤ) : ℕ :=
  max (coeffXp p + 2)
      (explicitTailParam p (lambdaD p.natDegree + 1) + 1)

/-- Z_p = Y_p + Q_p · (Λ_d + 1), bounding the largest block index. -/
def coeffZp (p : Polynomial ℤ) : ℕ :=
  coeffYp p + coeffQp p * (lambdaD p.natDegree + 1)

/-- U_coeff(p) = M_p + Q_p · Λ_d · p_+(Z_p) -/
def coeffBound (p : Polynomial ℤ) : ℤ :=
  coeffMp p + ↑(coeffQp p * lambdaD p.natDegree) * (posMajorant p).eval (coeffZp p : ℤ)

/-! ## Monotonicity of IsThreshold -/

theorem isThreshold_mono {p : Polynomial ℤ} {C C' : ℕ}
    (h : IsThreshold p C) (hle : C ≤ C') : IsThreshold p C' :=
  fun N hN => h N (le_trans hle hN)

/-! ## Parametrized threshold existence

This is the same as threshold_exists but takes residue datum R and signed block B
as parameters, rather than constructing them internally. The resulting threshold
value depends on R and B.
-/
set_option maxHeartbeats 6400000 in
theorem canonical_signed_block_bound (p : Polynomial ℤ)
    (hd : 1 ≤ p.natDegree):
    ∃ B : SignedBlock p (polyA p),
      B.L ≤ lambdaD p.natDegree := by
  have := bounded_bezout_canonical p.natDegree hd;
  obtain ⟨ lam, mu, h₁, h₂ ⟩ := this;
  use ⟨ Finset.biUnion ( Finset.range lam ) ( fun j => Finset.image ( fun u => u + j * 2 ^ ( p.natDegree + 1 ) ) ( buildPN ( canonicalR p.natDegree ) |>.1 ) ) ∪ Finset.biUnion ( Finset.range mu ) ( fun j => Finset.image ( fun u => u + ( lam + j ) * 2 ^ ( p.natDegree + 1 ) ) ( buildPN ( canonicalS p.natDegree ) |>.2 ) ), Finset.biUnion ( Finset.range lam ) ( fun j => Finset.image ( fun u => u + j * 2 ^ ( p.natDegree + 1 ) ) ( buildPN ( canonicalR p.natDegree ) |>.2 ) ) ∪ Finset.biUnion ( Finset.range mu ) ( fun j => Finset.image ( fun u => u + ( lam + j ) * 2 ^ ( p.natDegree + 1 ) ) ( buildPN ( canonicalS p.natDegree ) |>.1 ) ), lambdaD p.natDegree, by
    simp +zetaDelta at *;
    rintro u ( ⟨ a, ha, b, hb, rfl ⟩ | ⟨ a, ha, b, hb, rfl ⟩ ) <;> norm_num [ lambdaD ];
    · have := buildPN_canonicalR_bound p.natDegree |>.1 b hb;
      rcases k : p.natDegree with ( _ | _ | k ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
      · linarith;
      · ring_nf at *;
        norm_num [ pow_mul ] at *;
        nlinarith [ pow_pos ( zero_lt_two' ℕ ) ‹_›, pow_pos ( zero_lt_two' ℕ ) ( ( 2 + ‹_› * 3 + ‹_› ^ 2 ) / 2 ) ];
    · have := buildPN_canonicalS_bound p.natDegree |>.2 b hb;
      ring_nf at *;
      rw [ pow_mul ] ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) p.natDegree ], by
    unfold lambdaD; simp +decide [ Finset.mem_biUnion, Finset.mem_image ] ;
    rintro v ( ⟨ a, ha, b, hb, rfl ⟩ | ⟨ a, ha, b, hb, rfl ⟩ );
    · have := buildPN_canonicalR_bound p.natDegree |>.2 b hb;
      rw [ show p.natDegree * ( p.natDegree - 1 ) / 2 + 2 * p.natDegree + 2 = p.natDegree * ( p.natDegree - 1 ) / 2 + p.natDegree + 1 + ( p.natDegree + 1 ) by ring ];
      rw [ pow_add ];
      rw [ pow_add ];
      nlinarith [ pow_pos ( zero_lt_two' ℕ ) p.natDegree, pow_succ' ( 2 : ℕ ) p.natDegree ];
    · have := buildPN_canonicalS_bound p.natDegree;
      rw [ show 2 ^ ( p.natDegree * ( p.natDegree - 1 ) / 2 + 2 * p.natDegree + 2 ) = 2 ^ ( p.natDegree * ( p.natDegree - 1 ) / 2 + p.natDegree + 1 ) * 2 ^ ( p.natDegree + 1 ) by ring ];
      nlinarith [ this.1 b hb, pow_pos ( zero_lt_two' ℕ ) ( p.natDegree + 1 ) ], by
    intro x
    have h_sum : ∑ u ∈ Finset.biUnion (Finset.range lam) (fun j => Finset.image (fun u => u + j * 2 ^ (p.natDegree + 1)) (buildPN (canonicalR p.natDegree)).1), p.eval (x + u) - ∑ v ∈ Finset.biUnion (Finset.range lam) (fun j => Finset.image (fun u => u + j * 2 ^ (p.natDegree + 1)) (buildPN (canonicalR p.natDegree)).2), p.eval (x + v) = lam * polyA p * ∏ i : Fin p.natDegree, (2 ^ (i : ℕ) : ℤ) := by
      rw [ Finset.sum_biUnion, Finset.sum_biUnion ];
      · have h_sum : ∀ j : ℕ, ∑ u ∈ (buildPN (canonicalR p.natDegree)).1, p.eval (x + u + j * 2 ^ (p.natDegree + 1)) - ∑ v ∈ (buildPN (canonicalR p.natDegree)).2, p.eval (x + v + j * 2 ^ (p.natDegree + 1)) = polyA p * ∏ i : Fin p.natDegree, (2 ^ (i : ℕ) : ℤ) := by
          intro j
          have := signed_block_r p hd
          simp_all +decide [ add_assoc ];
          convert this.2 ( x + j * 2 ^ ( p.natDegree + 1 ) ) using 1 ; ring_nf!;
          grind;
        simp_all +decide [ add_assoc, mul_assoc ];
        rw [ ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun _ _ => h_sum _, Finset.sum_const, Finset.card_range, nsmul_eq_mul ];
      · intros i hi j hj hij;
        simp +decide [ Finset.disjoint_left ];
        intro a ha x hx; contrapose! hij; nlinarith [ show 2 ^ ( p.natDegree + 1 ) > 0 by positivity, show a < 2 ^ ( p.natDegree + 1 ) by exact lt_of_lt_of_le ( buildPN_canonicalR_bound p.natDegree |>.2 a ha ) ( Nat.pow_le_pow_right ( by decide ) ( by linarith ) ), show x < 2 ^ ( p.natDegree + 1 ) by exact lt_of_lt_of_le ( buildPN_canonicalR_bound p.natDegree |>.2 x hx ) ( Nat.pow_le_pow_right ( by decide ) ( by linarith ) ) ] ;
      · intros i hi j hj hij;
        simp +decide [ Finset.disjoint_left ];
        intro a ha x hx; contrapose! hij; nlinarith [ show 2 ^ ( p.natDegree + 1 ) > 0 by positivity, show a < 2 ^ p.natDegree by exact buildPN_canonicalR_bound p.natDegree |>.1 a ha, show x < 2 ^ p.natDegree by exact buildPN_canonicalR_bound p.natDegree |>.1 x hx, pow_pos ( zero_lt_two' ℕ ) ( p.natDegree + 1 ), pow_le_pow_right₀ ( show 1 ≤ 2 by decide ) ( show p.natDegree + 1 ≥ p.natDegree by linarith ) ] ;
    have h_sum2 : ∑ u ∈ Finset.biUnion (Finset.range mu) (fun j => Finset.image (fun u => u + (lam + j) * 2 ^ (p.natDegree + 1)) (buildPN (canonicalS p.natDegree)).2), p.eval (x + u) - ∑ v ∈ Finset.biUnion (Finset.range mu) (fun j => Finset.image (fun u => u + (lam + j) * 2 ^ (p.natDegree + 1)) (buildPN (canonicalS p.natDegree)).1), p.eval (x + v) = -mu * polyA p * ∏ i : Fin p.natDegree, ((2 ^ ((i : ℕ) + 1) : ℤ) - 1) := by
      have h_sum2 : ∀ j < mu, ∑ u ∈ Finset.image (fun u => u + (lam + j) * 2 ^ (p.natDegree + 1)) (buildPN (canonicalS p.natDegree)).2, p.eval (x + u) - ∑ v ∈ Finset.image (fun u => u + (lam + j) * 2 ^ (p.natDegree + 1)) (buildPN (canonicalS p.natDegree)).1, p.eval (x + v) = -polyA p * ∏ i : Fin p.natDegree, ((2 ^ ((i : ℕ) + 1) : ℤ) - 1) := by
        intro j hj
        have h_sum2 : ∑ u ∈ (buildPN (canonicalS p.natDegree)).2, p.eval (x + u + (lam + j) * 2 ^ (p.natDegree + 1)) - ∑ v ∈ (buildPN (canonicalS p.natDegree)).1, p.eval (x + v + (lam + j) * 2 ^ (p.natDegree + 1)) = -polyA p * ∏ i : Fin p.natDegree, ((2 ^ ((i : ℕ) + 1) : ℤ) - 1) := by
          have := signed_block_s p hd;
          have := this.2 ( x + ( lam + j ) * 2 ^ ( p.natDegree + 1 ) ) ; simp_all +decide [ add_assoc ] ;
          simp_all +decide [ add_comm, polyA ]; linarith;
        convert h_sum2 using 1;
        norm_num [ add_assoc ];
      rw [ Finset.sum_biUnion, Finset.sum_biUnion ];
      · rw [ ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun i hi => h_sum2 i ( Finset.mem_range.mp hi ) ] ; norm_num ; ring;
      · intros j hj k hk hjk;
        simp +decide [ Finset.disjoint_left ];
        intro a ha x hx; contrapose! hjk; nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( p.natDegree + 1 ), show a < 2 ^ ( p.natDegree + 1 ) from buildPN_canonicalS_bound p.natDegree |>.1 a ha, show x < 2 ^ ( p.natDegree + 1 ) from buildPN_canonicalS_bound p.natDegree |>.1 x hx ] ;
      · intros i hi j hj hij;
        simp +decide [ Finset.disjoint_left ];
        intro a ha x hx; contrapose! hij; nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( p.natDegree + 1 ), show a < 2 ^ ( p.natDegree + 1 ) from buildPN_canonicalS_bound p.natDegree |>.2 a ha, show x < 2 ^ ( p.natDegree + 1 ) from buildPN_canonicalS_bound p.natDegree |>.2 x hx ] ;
    rw [ Finset.sum_union, Finset.sum_union ];
    · linear_combination' h_sum + h_sum2 + h₁ * polyA p;
    · simp +decide [ Finset.disjoint_left ];
      rintro a x hx y hy rfl z hz t ht; nlinarith [ Nat.pow_le_pow_right two_pos ( show p.natDegree + 1 ≥ 1 by linarith ), show y < 2 ^ ( p.natDegree + 1 ) from by
                                                                                                                            exact lt_of_lt_of_le ( buildPN_canonicalR_bound p.natDegree |>.2 y hy ) ( Nat.pow_le_pow_right ( by decide ) ( by linarith ) ), show t < 2 ^ ( p.natDegree + 1 ) from by
                                                                                                                                                                            exact buildPN_canonicalS_bound p.natDegree |>.1 t ht ] ;
    · norm_num [ Finset.disjoint_left ];
      rintro a x hx₁ y hy₁ rfl z hz₁ w hw₁;
      have := buildPN_canonicalR_bound p.natDegree;
      have := buildPN_canonicalS_bound p.natDegree;
      nlinarith [ this.2 _ hw₁, ‹ ( ∀ u ∈ ( buildPN ( canonicalR p.natDegree ) ).1, u < 2 ^ p.natDegree ) ∧ ∀ u ∈ ( buildPN ( canonicalR p.natDegree ) ).2, u < 2 ^ p.natDegree ›.1 _ hy₁, pow_pos ( zero_lt_two' ℕ ) p.natDegree, pow_succ' ( 2 : ℕ ) p.natDegree ] ⟩ ;

/-! ## Helper: bound on posMajorant eval -/

theorem coeffKp_bound (p : Polynomial ℤ) (_hA : 0 < p.leadingCoeff) (_hd : 1 ≤ p.natDegree) :
    p.eval (explicitTailParam p 2 : ℤ) ≤ coeffKp p := by
  apply eval_le_posMajorant;
  exact_mod_cast le_max_of_le_left ( by nlinarith )

end

open Polynomial BigOperators Finset

noncomputable section

/-
For the construction I = I_res ∪ I_block with R elements spaced by a ≥ 2
    and blocks of width L, consecutive non-I elements u, v satisfy:
    - If u + 1 < Y: v ≤ u + 2 (residue/transition gap)
    - If u + 1 ≥ Y: v ≤ u + B.L + 1 (block gap)
    In either case, the appropriate TauProp gives p(v) ≤ 2·p(u).
-/
theorem separated_doubling
    (p : Polynomial ℤ)
    (a : ℕ) (ha : 0 < a)
    (R : ResidueDatum p a)
    (B : SignedBlock p (polyA p))
    (hR_gap : ∀ e ∈ R.E, ∀ f ∈ R.E, e < f → a ≤ f - e)
    (ha_ge_2 : 2 ≤ a)
    (T₁ : ℕ) (hT₁ : TauProp p 2 T₁)
    (T₂ : ℕ) (hT₂ : TauProp p (B.L + 1) T₂) (_hT₁_le : T₁ ≤ T₂)
    (R₀ : ℕ) (_hR₀_ge : T₁ + 1 ≤ R₀)
    (Y : ℕ) (hY_res : R₀ + R.E.sup id + 2 ≤ Y) (hY_blk : T₂ + 1 ≤ Y)
    (Q : ℕ) :
    let I := R.E.image (R₀ + ·) ∪ (Finset.range (Q - 1)).biUnion
      (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·))
    ∀ u v : ℕ, T₁ ≤ u → u ∉ I → v ∉ I → u < v →
      (∀ w, u < w → w < v → w ∈ I) → p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ) := by
  intros I u v hu huI hvI huv hbetween
  by_cases huY : u + 1 < Y;
  · -- Since $u$ and $v$ are not in $I$ and $u + 1 < Y$, all elements between $u$ and $v$ must be in $I_res$.
    have h_between_res : ∀ w, u < w → w < v → w ∈ R.E.image (R₀ + ·) := by
      intros w hw₁ hw₂;
      simp +zetaDelta at *;
      obtain ⟨ x, hx₁, hx₂ ⟩ | ⟨ x, hx₁, y, hy₁, hy₂ ⟩ := hbetween w hw₁ hw₂ <;> simp_all +decide [ add_assoc ];
      · use x;
      · contrapose! hbetween;
        use Y - 1;
        refine' ⟨ _, _, _, _ ⟩;
        · exact lt_tsub_iff_right.mpr huY;
        · omega;
        · intro e he; specialize hR_gap e he; contrapose! hR_gap;
          exact absurd hR_gap ( by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ Y ), show R.E.sup id ≥ e from Finset.le_sup ( f := id ) he ] );
        · intro a ha b hb; rcases Y with ( _ | Y ) <;> simp_all +decide ;
          grind;
    have h_card_res : Finset.card (Finset.Ico (u + 1) v) ≤ Finset.card (R.E.image (R₀ + ·)) := by
      exact Finset.card_le_card fun x hx => h_between_res x ( Finset.mem_Ico.mp hx |>.1 ) ( Finset.mem_Ico.mp hx |>.2 );
    have h_card_res : Finset.card (Finset.Ico (u + 1) v) ≤ 1 := by
      have h_card_res : ∀ e ∈ R.E, ∀ f ∈ R.E, e < f → R₀ + e + 2 ≤ R₀ + f := by
        grind;
      have h_card_res : ∀ w₁ w₂, w₁ ∈ R.E.image (R₀ + ·) → w₂ ∈ R.E.image (R₀ + ·) → w₁ < w₂ → w₂ ≥ w₁ + 2 := by
        grind;
      contrapose! h_card_res;
      obtain ⟨ w₁, hw₁, w₂, hw₂, hne ⟩ := Finset.one_lt_card.mp h_card_res;
      grind +extAll;
    simp +zetaDelta at *;
    exact hT₁ u v hu huv ( by linarith ) |>.2.2;
  · -- Since $u + 1 \geq Y$, we have $u \geq Y - 1 \geq T₂$.
    have hu_ge_T₂ : T₂ ≤ u := by
      linarith;
    by_cases hv_bound : v ≤ u + B.L + 1;
    · exact hT₂ u v hu_ge_T₂ huv hv_bound |>.2.2;
    · -- The position $u + B.L + 1$ is not in $I_res$ (since it's $\geq Y > R₀ + \maxE$) and not in $I_block$ (since $B.L$ is not in $B.P ∪ B.N$ as $B.P, B.N ⊆ \{0, ..., B.L-1\}$). But $u < u + B.L + 1 < v$, contradicting $hbetween$.
      have h_contradiction : u + B.L + 1 ∉ I := by
        simp [I];
        constructor;
        · intro x hx H; have := Finset.le_sup ( f := id ) hx; simp_all +decide ;
          grind;
        · intro i hi j hj; contrapose! huI; simp_all +decide [ I ] ;
          exact Or.inr ⟨ i - 1, by
            exact lt_of_le_of_lt ( Nat.pred_le _ ) hi, j, hj, by
            rcases i with ( _ | i ) <;> norm_num at *;
            · linarith [ show j < B.L from by cases hj <;> [ exact B.hP_bound _ ‹_›; exact B.hN_bound _ ‹_› ] ];
            · nlinarith only [ huI, huY, hY_blk, hY_res, show j < B.L from by cases hj <;> [ exact B.hP_bound _ ‹_› ; exact B.hN_bound _ ‹_› ] ] ⟩;
      grind
theorem M_le_coeffMp
    (p : Polynomial ℤ) (_hd : 1 ≤ p.natDegree) (_hA : 0 < p.leadingCoeff)
    (a : ℕ) (ha : 0 < a)
    (R : ResidueDatum p a)
    (hR_emax : R.eMax ≤ a * a)
    (hR_card : ∀ r, (R.F r).card ≤ a)
    (R₀ : ℕ) (hR₀_le : R₀ ≤ explicitTailParam p 2 + a)
    (ha_eq : (a : ℤ) = polyA p) :
    residueM p a ha R R₀ ≤ coeffMp p := by
  convert residueM_le p a ha R R₀ ( explicitTailParam p 2 + a ^ 2 + a ) _ ( a ) hR_card using 1;
  · -- Substitute ha_eq into the definition of coeffMp and then simplify the terms.
    simp [coeffMp, ha_eq];
    unfold coeffXp; simp +decide [ ← ha_eq ] ;
  · exact fun e he => by linarith [ show e ≤ R.eMax from Finset.le_sup ( f := id ) he ] ;

/-
Q - 1 from the construction is bounded by coeffQp.
-/
theorem Q_le_coeffQp
    (p : Polynomial ℤ) (hd : 1 ≤ p.natDegree) (hA : 0 < p.leadingCoeff)
    (a : ℕ) (ha : 0 < a)
    (R : ResidueDatum p a)
    (hR_emax : R.eMax ≤ a * a)
    (hR_card : ∀ r, (R.F r).card ≤ a)
    (R₀ : ℕ) (hR₀_le : R₀ ≤ explicitTailParam p 2 + a)
    (ha_eq : (a : ℤ) = polyA p)
    (K : ℕ) (hK_le : (K : ℤ) ≤ coeffKp p) :
    (residueM p a ha R R₀ + ↑K).toNat / a + 1 ≤ coeffQp p := by
  refine' Nat.succ_le_of_lt ( Nat.div_lt_of_lt_mul _ );
  have h_div : (residueM p a ha R R₀ + K).toNat ≤ (coeffMp p + coeffKp p).toNat := by
    have hM_le_coeffMp : residueM p a ha R R₀ ≤ coeffMp p := by
      apply M_le_coeffMp;
      all_goals assumption;
    grind;
  unfold coeffQp; norm_num [ ha_eq.symm ] ;
  linarith [ Nat.div_add_mod ( Int.toNat ( coeffMp p + coeffKp p ) ) a, Nat.mod_lt ( Int.toNat ( coeffMp p + coeffKp p ) ) ha ]

end

/-! ===== Height Bound Assembly ===== -/

/-
Helper lemmas for assembling the proof of height_only_bound from
the construction and bound tracking infrastructure.
-/

open Polynomial BigOperators Finset

noncomputable section

/-! ## Y bound: construction Y ≤ coeffYp -/

theorem Y_le_coeffYp (p : Polynomial ℤ)
    (a : ℕ) (ha : 0 < a) (ha_eq : (a : ℤ) = polyA p)
    (R : ResidueDatum p a) (hR_emax : R.eMax ≤ a * a)
    (R₀ : ℕ) (hR₀_le : R₀ ≤ explicitTailParam p 2 + a) :
    max (R₀ + R.eMax + 2) (explicitTailParam p (lambdaD p.natDegree + 1) + 1) ≤ coeffYp p := by
  simp [coeffYp, coeffXp];
  grind +qlia

/-
Bound on C₁ (block negative contribution sum).
    C₁ ≤ coeffQp * lambdaD * p_+(coeffZp).
-/
theorem c1_le_bound (p : Polynomial ℤ)
    (B : SignedBlock p (polyA p))
    (Y Q : ℕ)
    (hB_L : B.L ≤ lambdaD p.natDegree)
    (hY : Y ≤ coeffYp p)
    (hQ : Q - 1 ≤ coeffQp p) :
    ∑ i ∈ Finset.range (Q - 1), ∑ v ∈ B.N, p.eval ((↑Y + ↑i * (↑B.L + 1) : ℤ) + ↑v) ≤
    ↑(coeffQp p * lambdaD p.natDegree) * (posMajorant p).eval (coeffZp p : ℤ) := by
  -- For each i < Q-1 and v ∈ B.N, the index Y + i*(L+1) + v satisfies v < B.L ≤ lambdaD and i < Q-1 ≤ coeffQp, so Y + i*(L+1) + v ≤ Y + (coeffQp-1)*(lambdaD+1) + lambdaD - 1 ≤ coeffYp + coeffQp*(lambdaD+1) - 2 < coeffZp (since coeffZp = coeffYp + coeffQp*(lambdaD+1)).
  have h_index_bound : ∀ i : ℕ, i < Q - 1 → ∀ v : ℕ, v ∈ B.N → Y + i * (B.L + 1) + v < coeffZp p := by
    intros i hi v hv;
    have h_v_bound : v < B.L := by
      exact B.hN_bound v hv;
    unfold coeffZp;
    nlinarith;
  -- By the properties of the polynomial and its positive majorant, we have $p(Y + i * (B.L + 1) + v) \leq \text{posMajorant}(p)(Y + i * (B.L + 1) + v)$.
  have h_eval_le_posMajorant : ∀ i : ℕ, i < Q - 1 → ∀ v : ℕ, v ∈ B.N → p.eval (Y + i * (B.L + 1) + v : ℤ) ≤ (posMajorant p).eval (coeffZp p : ℤ) := by
    intros i hi v hv
    have h_eval_le_posMajorant : p.eval (Y + i * (B.L + 1) + v : ℤ) ≤ (posMajorant p).eval (Y + i * (B.L + 1) + v : ℤ) := by
      unfold posMajorant;
      simp +decide [ Polynomial.eval_finset_sum, Polynomial.sum_def ];
      rw [ Polynomial.eval_eq_sum, Polynomial.sum_def ];
      exact Finset.sum_le_sum fun n hn => by cases max_cases ( p.coeff n ) 0 <;> nlinarith [ pow_nonneg ( by positivity : 0 ≤ ( Y : ℤ ) + i * ( B.L + 1 ) + v ) n ] ;
    exact le_trans h_eval_le_posMajorant ( posMajorant_nondecreasing p _ _ <| mod_cast h_index_bound i hi v hv |> Nat.le_of_lt );
  refine' le_trans ( Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun v hv => h_eval_le_posMajorant i ( Finset.mem_range.mp hi ) v hv ) _;
  simp +zetaDelta at *;
  rw [ ← mul_assoc ];
  gcongr;
  · unfold posMajorant ;
    norm_num [ Polynomial.eval_finset_sum, Polynomial.sum_def ];
    exact Finset.sum_nonneg fun _ _ => mul_nonneg ( le_max_right _ _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ );
  · exact Nat.sub_le_of_le_add <| by linarith;
  · exact le_trans ( Finset.card_le_card ( show B.N ⊆ Finset.range B.L from fun x hx => Finset.mem_range.mpr ( B.hN_bound x hx ) ) ) ( by simpa )

/-! ## Nonneg residue sums -/

theorem nonneg_residue_sums (p : Polynomial ℤ)
    (a : ℕ) (_ha : 0 < a)
    (R : ResidueDatum p a)
    (R₀ T : ℕ) (hR₀_ge : T + 1 ≤ R₀) (hT_tau : TauProp p 2 T) :
    ∀ r : Fin a, 0 ≤ ∑ e ∈ R.F r, p.eval ((R₀ : ℤ) + ↑e) := by
  intro r
  have h_eval_pos : ∀ e ∈ R.F r, 0 < p.eval (R₀ + e : ℤ) := by
    exact fun e he => tauProp_pos' ( by norm_num ) hT_tau ( by linarith )
  exact Finset.sum_nonneg (fun e he => by linarith [h_eval_pos e he])

/-! ## Assembling C₀ ≤ coeffBound -/

theorem c0_le_coeffBound (p : Polynomial ℤ)
    (a : ℕ) (ha : 0 < a)
    (B : SignedBlock p (polyA p))
    (hB_L : B.L ≤ lambdaD p.natDegree)
    (Y : ℕ) (hY : Y ≤ coeffYp p)
    (Q : ℕ) (hQ : Q - 1 ≤ coeffQp p)
    (M : ℤ) (hM : M ≤ coeffMp p)
    (C₁ : ℤ) (hC₁_def : C₁ = ∑ i ∈ Finset.range (Q - 1),
      ∑ v ∈ B.N, p.eval ((↑Y + ↑i * (↑B.L + 1) : ℤ) + ↑v))
    (C₀ : ℤ) (hC₀_def : C₀ = M - ↑a + 1 + C₁) :
    C₀ ≤ coeffBound p := by
  -- By definition of $C₁$, we have $C₁ \leq coeffQp p * lambdaD p.natDegree * (posMajorant p).eval (coeffZp p : ℤ)$.
  have hC₁_le : C₁ ≤ coeffQp p * lambdaD p.natDegree * (posMajorant p).eval (coeffZp p : ℤ) := by
    exact hC₁_def.symm ▸ mod_cast c1_le_bound p B Y Q hB_L hY hQ;
  -- By definition of $coeffBound$, we have $coeffBound p = coeffMp p + coeffQp p * lambdaD p.natDegree * (posMajorant p).eval (coeffZp p : ℤ)$.
  simp [coeffBound];
  linarith [ show ( a : ℤ ) ≥ 1 by norm_cast ]

end

open Polynomial BigOperators Finset

noncomputable section

/-
When I_res = ∅ (empty residue set), the doubling property holds
    using TauProp p 2 T₁ for the pre-block region and TauProp p (B.L+1) T₂
    for the block region.
-/
theorem doubling_empty_res (p : Polynomial ℤ)
    (B : SignedBlock p (polyA p))
    (T₁ : ℕ) (hT₁ : TauProp p 2 T₁)
    (T₂ : ℕ) (hT₂ : TauProp p (B.L + 1) T₂) (_hT₁_le : T₁ ≤ T₂)
    (Y : ℕ) (hY_blk : T₂ + 1 ≤ Y)
    (Q : ℕ) :
    let I := (Finset.range (Q - 1)).biUnion
      (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·))
    ∀ u v : ℕ, T₁ ≤ u → u ∉ I → v ∉ I → u < v →
      (∀ w, u < w → w < v → w ∈ I) → p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ) := by
  intros I u v hu huI hvI huv hbetween
  by_cases huY : u + 1 < Y;
  · have h_consecutive : v = u + 1 := by
      contrapose! hbetween;
      use u + 1;
      grind;
    have := hT₁ u ( u + 1 ) hu ( by linarith ) ( by linarith ) ; aesop;
  · -- Since $u \geq Y - 1$ and $v \notin I$, we have $v \leq u + B.L + 1$.
    have hv_le : v ≤ u + B.L + 1 := by
      contrapose! hbetween;
      use u + B.L + 1;
      simp +zetaDelta at *;
      refine ⟨ hbetween, fun x hx y hy => ?_ ⟩;
      by_cases hx_eq : x = 0;
      · cases hy <;> simp_all +decide [ add_assoc ];
        · linarith [ B.hP_bound _ ‹_› ];
        · linarith [ B.hN_bound _ ‹_› ];
      · nontriviality;
        exact fun h => huI ( x - 1 ) ( by omega ) y hy <| by cases x <;> norm_num at * ; linarith;
    exact hT₂ u v ( by linarith ) ( by linarith ) ( by linarith ) |>.2.2

/-! ## Main theorem -/

set_option maxHeartbeats 6400000 in
theorem height_only_bound (p : Polynomial ℤ)
    (hd : 1 ≤ p.natDegree) (hA : 0 < p.leadingCoeff)
    (hgcd : ∀ ℓ, Nat.Prime ℓ → (ℓ : ℤ) ∣ polyA p →
      ∃ n : ℕ, 0 < n ∧ ¬ (ℓ : ℤ) ∣ p.eval (n : ℤ)) :
    IsThreshold p (coeffBound p).toNat := by
  -- === Setup ===
  set a := (polyA p).natAbs with ha_def
  have ha_pos : 0 < a := polyA_natAbs_pos hA
  have ha_eq : (a : ℤ) = polyA p :=
    Int.natAbs_of_nonneg (le_of_lt (polyA_pos hA))
  have hgcd' : ∀ ℓ, Nat.Prime ℓ → (ℓ : ℤ) ∣ (a : ℤ) →
      ∃ n : ℕ, 0 < n ∧ ¬ (ℓ : ℤ) ∣ p.eval (n : ℤ) :=
    fun ℓ hℓ hℓa => hgcd ℓ hℓ (ha_eq ▸ hℓa)
  -- === Get canonical B ===
  obtain ⟨B, hB_L⟩ := canonical_signed_block_bound p hd
  -- === Get R (case split on a) ===
  -- For a ≥ 2: use canonical_residue_spaced
  -- For a = 1: use trivial R with E = ∅ (to ensure residue gap ≤ 1 ≤ 2)
  obtain ⟨R, hR_emax, hR_card, hR_gap, hR_emptyOr⟩ :
      ∃ R : ResidueDatum p a,
        R.eMax ≤ a * a ∧ (∀ r, (R.F r).card ≤ a) ∧
        (∀ e ∈ R.E, ∀ f ∈ R.E, e < f → a ≤ f - e) ∧
        (a = 1 → R.E = ∅) := by
    by_cases ha2 : 2 ≤ a
    · obtain ⟨R, h1, h2, h3⟩ := canonical_residue_spaced p a ha_pos hgcd'
      exact ⟨R, h1, h2, h3, fun h => absurd h (by omega)⟩
    · -- a = 1
      have ha1 : a = 1 := by omega
      refine ⟨⟨∅, fun _ => ∅, fun _ => Finset.empty_subset _, fun r => ?_⟩,
             by simp [ResidueDatum.eMax], by simp, by simp, fun _ => rfl⟩
      simp only [Finset.sum_empty]
      have : r = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [this]; simp [ha1]
  -- === Tau parameters ===
  set T₁ := explicitTailParam p 2 with hT₁_def
  have hT₁_tau : TauProp p 2 T₁ := explicit_tau_bound p 2 hA hd
  set T₂ := explicitTailParam p (lambdaD p.natDegree + 1) with hT₂_def
  have hT₂_tau : TauProp p (lambdaD p.natDegree + 1) T₂ :=
    explicit_tau_bound p (lambdaD p.natDegree + 1) hA hd
  have hT₂_block : TauProp p (B.L + 1) T₂ := tauProp_mono_G hT₂_tau (by omega)
  have hT₁_le_T₂ : T₁ ≤ T₂ := by
    apply explicitTailParam_mono
    have : 1 ≤ 2 ^ (p.natDegree * (p.natDegree - 1) / 2 + 2 * p.natDegree + 2) :=
      Nat.one_le_pow _ _ (by norm_num)
    unfold lambdaD; omega
  -- === R₀ ===
  set R₀ := a * ((T₁ + 1 + a - 1) / a) with hR₀_def
  have hceil := ceil_mul_bound a T₁ ha_pos
  have hR₀_ge : T₁ + 1 ≤ R₀ := hceil.1
  have hR₀_le : R₀ ≤ T₁ + a := hceil.2.1
  have hR₀_div : (a : ℤ) ∣ (R₀ : ℤ) := by exact_mod_cast hceil.2.2
  -- === Y ===
  set Y := max (R₀ + R.eMax + 2) (T₂ + 1) with hY_def
  have hY_ge_res : R₀ + R.E.sup id + 2 ≤ Y := le_max_left _ _
  have hY_ge_blk : T₂ + 1 ≤ Y := le_max_right _ _
  have hY_le : Y ≤ coeffYp p := Y_le_coeffYp p a ha_pos ha_eq R hR_emax R₀ hR₀_le
  -- === K ===
  have hT₁_pos : 0 < p.eval (T₁ : ℤ) := tauProp_pos' (by omega) hT₁_tau le_rfl
  set K := (p.eval (T₁ : ℤ)).toNat with hK_def
  have hK_pos : 0 < K := by omega
  have hK_eq : (K : ℤ) = p.eval (T₁ : ℤ) := Int.toNat_of_nonneg (le_of_lt hT₁_pos)
  have hK_le : (K : ℤ) ≤ coeffKp p := by rw [hK_eq]; exact coeffKp_bound p hA hd
  -- === Nonneg residue sums ===
  have hR₀_nonneg := nonneg_residue_sums p a ha_pos R R₀ T₁ hR₀_ge hT₁_tau
  -- === Build the construction ===
  set k : Fin a → ℤ := fun r => ∑ e ∈ R.F r, p.eval ((R₀ : ℤ) + ↑e) with hk_def
  set M : ℤ := Finset.univ.sup' ⟨⟨0, ha_pos⟩, Finset.mem_univ _⟩ k with hM_def
  set Q := (M + ↑K).toNat / a + 2 with hQ_def
  set I_res : Finset ℕ := R.E.image (R₀ + ·) with hI_res_def
  set I_block : Finset ℕ := (Finset.range (Q - 1)).biUnion
    (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·)) with hI_block_def
  set I : Finset ℕ := I_res ∪ I_block with hI_def
  set C₁ : ℤ := ∑ i ∈ Finset.range (Q - 1),
    ∑ v ∈ B.N, p.eval ((↑Y + ↑i * (↑B.L + 1) : ℤ) + ↑v) with hC₁_def
  set C₀ : ℤ := M - ↑a + 1 + C₁ with hC₀_def
  -- === RepresentsInterval ===
  have hI_rep : RepresentsInterval (fun j => p.eval (j : ℤ)) I C₀ K :=
    represents_interval_construction p a ha_pos ha_eq R B R₀ hR₀_div
      Y hY_ge_res K hK_pos hR₀_nonneg
  -- === Index bound ===
  have hI_ge : ∀ i ∈ I, T₁ + 1 ≤ i :=
    construction_indices_ge p a ha_pos R B R₀ Y Q T₁ hR₀_ge hY_ge_res
  -- === Positivity ===
  have h_pos : ∀ n : ℕ, T₁ ≤ n → 0 < p.eval (n : ℤ) :=
    fun n hn => tauProp_pos' (by omega) hT₁_tau hn
  -- === Doubling property ===
  have hDoubling : ∀ u v : ℕ, T₁ ≤ u → u ∉ I → v ∉ I → u < v →
      (∀ w, u < w → w < v → w ∈ I) → p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ) := by
    by_cases ha2 : 2 ≤ a
    · exact separated_doubling p a ha_pos R B hR_gap ha2
        T₁ hT₁_tau T₂ hT₂_block hT₁_le_T₂
        R₀ hR₀_ge Y hY_ge_res hY_ge_blk Q
    · -- a = 1, so R.E = ∅ and I_res = ∅
      have ha1 : a = 1 := by omega
      have hR_E_empty : R.E = ∅ := hR_emptyOr ha1
      have hI_res_empty : I_res = ∅ := by simp [I_res, hR_E_empty]
      have hI_eq : I = I_block := by simp [I, hI_res_empty]
      intro u v hu huI hvI huv hbetween
      rw [hI_eq] at huI hvI hbetween
      exact doubling_empty_res p B T₁ hT₁_tau T₂ hT₂_block hT₁_le_T₂ Y hY_ge_blk Q
        u v hu huI hvI huv hbetween
  -- === Apply isThreshold_of_data ===
  have hT₁_pos : 0 < T₁ := by
    simp only [hT₁_def, explicitTailParam]
    exact Nat.lt_of_lt_of_le (by omega) (le_max_left _ _)
  have hThreshold : IsThreshold p C₀.toNat :=
    isThreshold_of_data p T₁ hT₁_pos K hK_eq I C₀ hI_ge hI_rep h_pos hDoubling
  -- === Bound tracking ===
  have hM_le : M ≤ coeffMp p := by
    show residueM p a ha_pos R R₀ ≤ coeffMp p
    exact M_le_coeffMp p hd hA a ha_pos R hR_emax hR_card R₀ hR₀_le ha_eq
  have hQ_le : Q - 1 ≤ coeffQp p := by
    show (residueM p a ha_pos R R₀ + ↑K).toNat / a + 1 ≤ coeffQp p
    exact Q_le_coeffQp p hd hA a ha_pos R hR_emax hR_card R₀ hR₀_le ha_eq K hK_le
  have hC₀_le : C₀ ≤ coeffBound p :=
    c0_le_coeffBound p a ha_pos B hB_L Y hY_le Q hQ_le M hM_le C₁ rfl C₀ rfl
  -- === Conclude ===
  exact isThreshold_mono hThreshold (by omega)

end

section NatScope
open Nat

open Polynomial BigOperators Finset

noncomputable section

/-
For each prime power factor q = ℓ^e of d! (d ≥ 1):
  - e ≤ d
  - q ≤ 2^d
  - The number of distinct prime factors of d! is ≤ d.
-/
def coeffSum (p : Polynomial ℤ) : ℕ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).natAbs

theorem coeffSum_pos (p : Polynomial ℤ) (_hd : 1 ≤ p.natDegree) (_hA : 0 < p.leadingCoeff) :
    1 ≤ coeffSum p := by
  exact le_trans ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Finset.single_le_sum ( fun i _ => Nat.zero_le ( Int.natAbs ( p.coeff i ) ) ) ( Finset.mem_range.mpr ( Nat.lt_succ_self _ ) ) )

/-- For x ≥ 1, the positive majorant is bounded by S · x^d. -/
theorem posMajorant_eval_le (p : Polynomial ℤ) (x : ℕ) (hx : 1 ≤ x) :
    (posMajorant p).eval (x : ℤ) ≤ (coeffSum p : ℤ) * (x : ℤ) ^ p.natDegree := by
  have h_posMajorant_eval : ∀ x : ℤ, 1 ≤ x → (posMajorant p).eval x ≤ (∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).natAbs) * x ^ p.natDegree := by
    intro x hx
    have h_posMajorant_eval : (posMajorant p).eval x = ∑ i ∈ Finset.range (p.natDegree + 1), (max (p.coeff i) 0) * x ^ i := by
      unfold posMajorant;
      simp +decide [ Polynomial.eval_finset_sum, Polynomial.sum_def ];
      rw [ Finset.sum_subset ( show p.support ⊆ Finset.range ( p.natDegree + 1 ) from fun i hi => Finset.mem_range_succ_iff.mpr ( Polynomial.le_natDegree_of_mem_supp _ hi ) ) ] ; aesop;
    push_cast [ h_posMajorant_eval ];
    rw [ Finset.sum_mul _ _ _ ];
    exact Finset.sum_le_sum fun i hi => mul_le_mul ( by cases max_cases ( p.coeff i ) 0 <;> cases abs_cases ( p.coeff i ) <;> linarith ) ( pow_le_pow_right₀ hx ( Finset.mem_range_succ_iff.mp hi ) ) ( by positivity ) ( by positivity );
  exact h_posMajorant_eval x ( mod_cast hx )

/-- polyA(p).natAbs ≤ coeffSum(p) * d!. -/
theorem polyA_le_coeffSum (p : Polynomial ℤ) (_hA : 0 < p.leadingCoeff) :
    (polyA p).natAbs ≤ coeffSum p * p.natDegree.factorial := by
  unfold polyA coeffSum;
  rw [ Int.natAbs_mul, Int.natAbs_natCast ];
  exact Nat.mul_le_mul_right _ ( Finset.single_le_sum ( fun i _ => Nat.zero_le ( Int.natAbs ( p.coeff i ) ) ) ( Finset.mem_range.mpr ( Nat.lt_succ_self _ ) ) )

/-- explicitTailParam p G ≤ max(6dG, 4S). -/
theorem explicitTailParam_le (p : Polynomial ℤ) (G : ℕ) (hA : 0 < p.leadingCoeff) :
    explicitTailParam p G ≤ max (6 * p.natDegree * G) (4 * coeffSum p) := by
  refine' max_le_max le_rfl _;
  have hHzero_eq_coeffSum : Hzero p = coeffSum p := by
    unfold Hzero coeffSum;
    simp +decide [ Finset.sum_range_succ, abs_of_pos hA ];
    ring;
  norm_num [ hHzero_eq_coeffSum ];
  exact Int.ceil_le.mpr ( by rw [ div_le_iff₀ ] <;> norm_cast ; nlinarith [ show p.leadingCoeff ≥ 1 by linarith ] )

end

open Polynomial BigOperators Finset

/-
Bridge lemma: the simplified gcd condition implies the internal gcd condition.
-/
theorem gcd_condition_bridge (p : Polynomial ℤ)
    (hgcd : ∀ q, Nat.Prime q → ∃ n : ℕ, ¬ ((q : ℤ) ∣ p.eval (n : ℤ))) :
    ∀ ℓ, Nat.Prime ℓ → (ℓ : ℤ) ∣ polyA p →
      ∃ n : ℕ, 0 < n ∧ ¬ (ℓ : ℤ) ∣ p.eval (n : ℤ) := by
  intro ℓ hℓ hdiv
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ¬(ℓ : ℤ) ∣ p.eval (n₀ : ℤ) := hgcd ℓ hℓ;
  by_cases h_zero : p.eval (0 : ℤ) % ℓ = 0;
  · exact ⟨ n₀, Nat.pos_of_ne_zero fun h => hn₀ <| by aesop, hn₀ ⟩;
  · exact ⟨ ℓ, hℓ.pos, by haveI := Fact.mk hℓ; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, Polynomial.eval_eq_sum_range ] ⟩

/-
coeffXp ≤ 8 * S² * (d!)² for d ≥ 2
-/
theorem coeffXp_le_8S2fact2 (p : Polynomial ℤ)
    (hd : 2 ≤ p.natDegree) (hA : 0 < p.leadingCoeff) :
    coeffXp p ≤ 8 * (coeffSum p) ^ 2 * (p.natDegree !) ^ 2 := by
  -- Applying the bounds from the provided solution
  have h_bound : coeffXp p ≤ 6 * (p.natDegree !)^2 * (coeffSum p)^2 + (coeffSum p * p.natDegree !)^2 + (coeffSum p * p.natDegree !) := by
    have h_bound : coeffXp p ≤ max (6 * p.natDegree * 2) (4 * coeffSum p) + (coeffSum p * p.natDegree !)^2 + (coeffSum p * p.natDegree !) := by
      apply_rules [ add_le_add, pow_le_pow_left₀, polyA_le_coeffSum ];
      · exact explicitTailParam_le p 2 hA;
      · positivity;
    refine le_trans h_bound ?_;
    gcongr;
    refine' max_le _ _;
    · nontriviality;
      refine' le_trans _ ( Nat.mul_le_mul_left _ <| Nat.pow_le_pow_left ( show coeffSum p ≥ 1 from _ ) 2 );
      · nlinarith only [ hd, Nat.self_le_factorial p.natDegree, Nat.pow_le_pow_left ( show p.natDegree ≥ 2 by assumption ) 2 ];
      · exact Nat.pos_of_ne_zero ( by unfold coeffSum; aesop );
    · rcases k : coeffSum p with ( _ | _ | k ) <;> simp_all +decide [ sq, mul_assoc ];
      · nlinarith only [ hd, Nat.self_le_factorial p.natDegree ];
      · nlinarith only [ show 0 < p.natDegree ! * p.natDegree ! from by positivity, show 0 < p.natDegree ! * p.natDegree ! * ( ‹_› + 1 + 1 ) from by positivity, show 0 < p.natDegree ! * p.natDegree ! * ( ‹_› + 1 + 1 ) * ( ‹_› + 1 + 1 ) from by positivity ];
  -- Since $coeffSum p \geq 1$, we have $coeffSum p * p.natDegree ! \leq coeffSum p ^ 2 * p.natDegree ! ^ 2$.
  have h_le : coeffSum p * p.natDegree ! ≤ coeffSum p ^ 2 * p.natDegree ! ^ 2 := by
    gcongr;
    · exact Nat.le_self_pow ( by norm_num ) _;
    · nlinarith only [ Nat.factorial_pos p.natDegree ];
  grind +ring

/-
coeffQp ≤ 2 * S * X^d for d ≥ 2
-/
theorem coeffQp_le_2SXd (p : Polynomial ℤ)
    (hd : 2 ≤ p.natDegree) (hA : 0 < p.leadingCoeff) :
    coeffQp p ≤ 2 * coeffSum p * (coeffXp p) ^ p.natDegree := by
  -- By definition of $coeffQp$, we have $coeffQp p = (coeffMp p + coeffKp p).toNat / (polyA p).natAbs + 1$.
  set a := (polyA p).natAbs
  set X := coeffXp p
  set S := coeffSum p
  have h_coeffQp : coeffQp p = (coeffMp p + coeffKp p).toNat / a + 1 := by
    rfl;
  have h_coeffMp_le : coeffMp p ≤ a * S * X ^ p.natDegree := by
    refine' le_trans ( mul_le_mul_of_nonneg_left ( posMajorant_eval_le p X ( Nat.pos_of_ne_zero _ ) ) ( Nat.cast_nonneg _ ) ) _;
    · grind +locals;
    · grind
  have h_coeffKp_le : coeffKp p ≤ S * X ^ p.natDegree := by
    have h_coeffKp_le : coeffKp p ≤ S * (explicitTailParam p 2) ^ p.natDegree := by
      convert posMajorant_eval_le p ( explicitTailParam p 2 ) _ using 1;
      exact le_max_of_le_left ( by nlinarith [ Nat.self_le_factorial p.natDegree ] );
    exact h_coeffKp_le.trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( by exact_mod_cast Nat.le_add_right _ _ |> Nat.le_trans <| Nat.le_add_right _ _ ) _ ) <| by positivity )
  have h_a_ge_2 : 2 ≤ a := by
    have h_a_ge_2 : 2 ≤ p.leadingCoeff * p.natDegree ! := by
      exact le_trans ( by nlinarith [ Nat.self_le_factorial p.natDegree ] ) ( mul_le_mul_of_nonneg_right hA ( Nat.cast_nonneg _ ) );
    unfold a polyA ;
    linarith [ abs_of_nonneg ( by positivity : 0 ≤ p.leadingCoeff * p.natDegree ! ) ];
  have h_coeffQp_le : (coeffMp p + coeffKp p).toNat / a + 1 ≤ (a * S * X ^ p.natDegree + S * X ^ p.natDegree) / a + 1 := by
    gcongr;
    grind +splitImp;
  have h_coeffQp_le_final : (a * S * X ^ p.natDegree + S * X ^ p.natDegree) / a + 1 ≤ 2 * S * X ^ p.natDegree := by
    have h_div : (a * S * X ^ p.natDegree + S * X ^ p.natDegree) / a ≤ S * X ^ p.natDegree + S * X ^ p.natDegree / 2 := by
      rw [ Nat.div_le_iff_le_mul_add_pred ];
      · nlinarith [ Nat.div_add_mod ( S * X ^ p.natDegree ) 2, Nat.mod_lt ( S * X ^ p.natDegree ) two_pos, Nat.sub_add_cancel ( by linarith : 1 ≤ a ), _root_.mul_le_mul_right h_a_ge_2 ( S * X ^ p.natDegree ) ];
      · grind
    have h_div_final : S * X ^ p.natDegree / 2 + 1 ≤ S * X ^ p.natDegree := by
      have h_div_final : S * X ^ p.natDegree ≥ 2 := by
        have h_div_final : S ≥ 1 := by
          exact coeffSum_pos p ( by linarith ) ( by linarith )
        have h_div_final : X ≥ 2 := by
          exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( le_max_of_le_left <| by nlinarith ) <| Nat.zero_le _ ) <| Nat.zero_le _;
        have h_div_final : S * X ^ p.natDegree ≥ 1 * 2 ^ p.natDegree := by
          gcongr
        have h_div_final : 1 * 2 ^ p.natDegree ≥ 2 := by
          exact le_trans ( by norm_num ) ( Nat.mul_le_mul_left 1 ( pow_le_pow_right₀ ( by norm_num ) hd ) )
        linarith [h_div_final];
      omega;
    linarith;
  exact h_coeffQp ▸ h_coeffQp_le.trans h_coeffQp_le_final

/-
coeffZp ≤ 4 * S * X^d * (Λ + 1) for d ≥ 2
-/
theorem coeffZp_le_bound (p : Polynomial ℤ)
    (hd : 2 ≤ p.natDegree) (hA : 0 < p.leadingCoeff) :
    coeffZp p ≤ 4 * coeffSum p * (coeffXp p) ^ p.natDegree * (lambdaD p.natDegree + 1) := by
  unfold coeffZp;
  -- By Lemma `coeffYp_le`, we have `coeffYp ≤ 2 * coeffSum p * (coeffXp p) ^ p.natDegree * (lambdaD p.natDegree + 1)`.
  have h_coeffYp_le : coeffYp p ≤ 2 * coeffSum p * (coeffXp p) ^ p.natDegree * (lambdaD p.natDegree + 1) := by
    refine' max_le _ _;
    · -- By Lemma `coeffXp_le_8S2fact2`, we have `coeffXp p ≤ 8 * (coeffSum p) ^ 2 * (p.natDegree !) ^ 2`.
      have h_coeffXp_le : coeffXp p ≤ 2 * coeffSum p * coeffXp p ^ p.natDegree := by
        refine' le_trans _ ( Nat.mul_le_mul_right _ <| Nat.mul_le_mul_left _ <| coeffSum_pos p ( by linarith ) hA );
        rcases k : coeffXp p with ( _ | _ | k ) <;> simp_all +decide;
        nlinarith [ Nat.pow_le_pow_right ( by linarith : 1 ≤ ‹ℕ› + 1 + 1 ) hd ];
      nlinarith [ show 0 < 2 * coeffSum p * coeffXp p ^ p.natDegree from mul_pos ( mul_pos two_pos ( coeffSum_pos p ( by linarith ) hA ) ) ( pow_pos ( by
                    grind +locals ) _ ), show lambdaD p.natDegree ≥ 2 by
                                                                                                                                                                        exact le_trans ( by norm_num ) ( Nat.pow_le_pow_right ( by norm_num ) ( Nat.le_add_left _ _ ) ) ];
    · refine' le_trans ( Nat.succ_le_of_lt ( lt_of_le_of_lt ( explicitTailParam_le p _ hA ) _ ) ) _;
      exact 2 * coeffSum p * ( 12 * p.natDegree ) ^ p.natDegree * ( lambdaD p.natDegree + 1 );
      · refine' max_lt _ _;
        · refine' mul_lt_mul_of_pos_right _ ( Nat.succ_pos _ );
          refine' lt_of_lt_of_le _ ( Nat.mul_le_mul_right _ ( Nat.mul_le_mul_left _ ( show coeffSum p ≥ 1 from _ ) ) );
          · nlinarith [ Nat.pow_le_pow_right ( by linarith : 1 ≤ 12 * p.natDegree ) hd ];
          · exact coeffSum_pos p ( by linarith ) hA;
        · refine' lt_of_lt_of_le _ ( Nat.mul_le_mul_left _ ( Nat.le_add_left _ _ ) );
          nlinarith [ show 0 < coeffSum p from coeffSum_pos p ( by linarith ) hA, show ( 12 * p.natDegree ) ^ p.natDegree > 2 by exact lt_of_lt_of_le ( by nlinarith ) ( Nat.le_self_pow ( by linarith ) _ ) ];
      · gcongr;
        refine' le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg _ _ ) _ <;> norm_num;
        exact le_max_of_le_left ( by linarith );
  nlinarith [ coeffQp_le_2SXd p hd hA, show 0 < coeffSum p * ( lambdaD p.natDegree + 1 ) by exact mul_pos ( coeffSum_pos p ( by linarith ) hA ) ( Nat.succ_pos _ ) ]

/-
Intermediate: coeffBound ≤ 4^(d+1) * S^(d+2) * X^(d²+d) * (Λ+1)^(d+1) for d ≥ 2
-/
theorem coeffBound_le_intermediate (p : Polynomial ℤ)
    (hd : 2 ≤ p.natDegree) (hA : 0 < p.leadingCoeff) :
    (coeffBound p : ℤ) ≤
      4 ^ (p.natDegree + 1) * (coeffSum p : ℤ) ^ (p.natDegree + 2) *
      (coeffXp p : ℤ) ^ (p.natDegree ^ 2 + p.natDegree) *
      ((lambdaD p.natDegree + 1 : ℕ) : ℤ) ^ (p.natDegree + 1) := by
  have h_coeffBound_def : coeffBound p = coeffMp p + ↑(coeffQp p * lambdaD p.natDegree) * (posMajorant p).eval (coeffZp p : ℤ) := by
    exact Eq.symm ((fun {a b} => Int.neg_inj.mp) rfl);
  have h_coeffMp_bound : coeffMp p ≤ (coeffSum p : ℤ) ^ 2 * (p.natDegree ! : ℤ) * (coeffXp p : ℤ) ^ p.natDegree := by
    have h_coeffMp_bound : coeffMp p ≤ (coeffSum p : ℤ) * (p.natDegree ! : ℤ) * (posMajorant p).eval (coeffXp p : ℤ) := by
      exact mul_le_mul_of_nonneg_right ( mod_cast polyA_le_coeffSum p hA ) ( by exact ( show 0 ≤ eval ( ↑ ( coeffXp p ) ) ( posMajorant p ) from by
                                                                                          unfold posMajorant;
                                                                                          norm_num [ Polynomial.eval_finset_sum, Polynomial.sum_def ];
                                                                                          exact Finset.sum_nonneg fun _ _ => mul_nonneg ( le_max_right _ _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ) );
    refine le_trans h_coeffMp_bound ?_;
    convert mul_le_mul_of_nonneg_left ( posMajorant_eval_le p ( coeffXp p ) ( show 1 ≤ coeffXp p from ?_ ) ) ( show ( 0 : ℤ ) ≤ coeffSum p * p.natDegree ! from mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) using 1 ; ring;
    grind +locals;
  have h_coeffQp_bound : (coeffQp p : ℤ) * (lambdaD p.natDegree : ℤ) * (posMajorant p).eval (coeffZp p : ℤ) ≤ 2 * (coeffSum p : ℤ) * (coeffXp p : ℤ) ^ p.natDegree * (lambdaD p.natDegree : ℤ) * (coeffSum p : ℤ) * (coeffZp p : ℤ) ^ p.natDegree := by
    have h_coeffQp_bound : (coeffQp p : ℤ) ≤ 2 * (coeffSum p : ℤ) * (coeffXp p : ℤ) ^ p.natDegree := by
      exact_mod_cast coeffQp_le_2SXd p hd hA;
    have h_posMajorant_bound : (posMajorant p).eval (coeffZp p : ℤ) ≤ (coeffSum p : ℤ) * (coeffZp p : ℤ) ^ p.natDegree := by
      apply posMajorant_eval_le;
      grind +locals;
    convert mul_le_mul ( mul_le_mul h_coeffQp_bound ( show ( lambdaD p.natDegree : ℤ ) ≤ lambdaD p.natDegree from le_rfl ) ?_ ?_ ) h_posMajorant_bound ?_ ?_ using 1 <;> ring_nf <;> norm_num;
    · positivity;
    · unfold posMajorant ;
      norm_num [ Polynomial.eval_finset_sum, Polynomial.sum_def ];
      exact Finset.sum_nonneg fun _ _ => mul_nonneg ( le_max_right _ _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ );
    · exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( Nat.cast_nonneg _ );
  have h_coeffZp_bound : (coeffZp p : ℤ) ≤ 4 * (coeffSum p : ℤ) * (coeffXp p : ℤ) ^ p.natDegree * (lambdaD p.natDegree + 1) := by
    exact_mod_cast coeffZp_le_bound p hd hA;
  have h_coeffBound_bound : coeffBound p ≤ (coeffSum p : ℤ) ^ 2 * (p.natDegree ! : ℤ) * (coeffXp p : ℤ) ^ p.natDegree + 2 * (coeffSum p : ℤ) ^ 2 * (coeffXp p : ℤ) ^ p.natDegree * (lambdaD p.natDegree : ℤ) * (4 * (coeffSum p : ℤ) * (coeffXp p : ℤ) ^ p.natDegree * (lambdaD p.natDegree + 1)) ^ p.natDegree := by
    have h_coeffZp_bound_pow : (coeffZp p : ℤ) ^ p.natDegree ≤ (4 * (coeffSum p : ℤ) * (coeffXp p : ℤ) ^ p.natDegree * (lambdaD p.natDegree + 1)) ^ p.natDegree := by
      gcongr;
    convert add_le_add h_coeffMp_bound ( h_coeffQp_bound.trans _ ) using 1;
    convert mul_le_mul_of_nonneg_left h_coeffZp_bound_pow ( show ( 0 : ℤ ) ≤ 2 * ( coeffSum p : ℤ ) * ( coeffXp p : ℤ ) ^ p.natDegree * ( lambdaD p.natDegree : ℤ ) * ( coeffSum p : ℤ ) by positivity ) using 1 ; ring;
  refine le_trans h_coeffBound_bound ?_;
  refine' le_trans ( add_le_add_left _ _ ) _;
  exact 2 * ( coeffSum p : ℤ ) ^ 2 * ( coeffXp p : ℤ ) ^ p.natDegree * ( lambdaD p.natDegree : ℤ ) * ( 4 * ( coeffSum p : ℤ ) * ( coeffXp p : ℤ ) ^ p.natDegree * ( lambdaD p.natDegree + 1 ) ) ^ p.natDegree;
  · refine' le_trans _ ( le_mul_of_one_le_right _ _ );
    · have h_lambdaD_bound : (p.natDegree ! : ℤ) ≤ 2 * (lambdaD p.natDegree : ℤ) := by
        unfold lambdaD; norm_cast; induction' p.natDegree with d hd <;> simp_all +decide [ Nat.factorial_succ, pow_succ' ] ;
        rcases d with ( _ | _ | d ) <;> simp_all +decide [Nat.mul_succ];
        refine le_trans ( Nat.mul_le_mul_left _ hd ) ?_;
        ring_nf;
        rw [ show ( 6 + d * 5 + d ^ 2 ) / 2 = ( 2 + d * 3 + d ^ 2 ) / 2 + ( d + 2 ) by exact Nat.div_eq_of_eq_mul_left zero_lt_two <| by linarith [ Nat.div_mul_cancel ( show 2 ∣ 2 + d * 3 + d ^ 2 from even_iff_two_dvd.mp <| by simp +arith +decide [ parity_simps ] ) ] ] ; ring_nf;
        norm_num [ pow_mul ];
        nlinarith only [ show 0 < ( 2 ^ d ) ^ 2 * 2 ^ ( ( 2 + d * 3 + d ^ 2 ) / 2 ) by positivity, show 0 < ( 2 ^ d ) ^ 3 * 2 ^ ( ( 2 + d * 3 + d ^ 2 ) / 2 ) by positivity, show 2 ^ d ≥ d + 1 by exact Nat.recOn d ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; nlinarith only [ ihn ] ];
      nlinarith only [ show 0 ≤ ( coeffSum p : ℤ ) ^ 2 * ( coeffXp p : ℤ ) ^ p.natDegree by positivity, h_lambdaD_bound ];
    · grind;
    · refine' one_le_pow₀ _;
      grind +locals;
  · ring_nf;
    rw [ show ( coeffSum p * coeffXp p ^ p.natDegree * 4 + coeffSum p * coeffXp p ^ p.natDegree * lambdaD p.natDegree * 4 : ℤ ) = ( coeffSum p * coeffXp p ^ p.natDegree * 4 ) * ( 1 + lambdaD p.natDegree ) by ring ] ; rw [ mul_pow ] ; ring_nf ;
    grind +splitIndPred

/-
d^d ≥ d! * 2^(d/2) for d ≥ 2.
-/
private lemma dd_ge_factorial_mul_pow2 (d : ℕ) (hd : 2 ≤ d) : d.factorial * 2 ^ (d / 2) ≤ d ^ d := by
  -- We'll use that $d^d = d \times d \times \cdots \times d$ (d times) and $d! = d \times (d-1) \times \cdots \times 1$.
  have h_prod : d ^ d = d ! * (∏ k ∈ Finset.Icc 1 d, (d / k : ℚ)) := by
    erw [ Finset.prod_Ico_eq_prod_range ];
    norm_num [ add_comm, Finset.prod_range_succ' ];
    norm_cast ; norm_num [ Nat.factorial_ne_zero, mul_div_cancel₀ ];
  -- We'll use that $\prod_{k=1}^d \frac{d}{k} \geq 2^{d/2}$.
  have h_prod_ge : ∏ k ∈ Finset.Icc 1 d, (d / k : ℚ) ≥ 2 ^ (d / 2) := by
    nontriviality;
    -- We'll use that $\prod_{k=1}^{\lfloor d/2 \rfloor} \frac{d}{k} \geq 2^{\lfloor d/2 \rfloor}$.
    have h_prod_floor : ∏ k ∈ Finset.Icc 1 (d / 2), (d / k : ℚ) ≥ 2 ^ (d / 2) := by
      exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by positivity ) fun x hx => show ( d : ℚ ) / x ≥ 2 by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;> norm_cast <;> linarith [ Finset.mem_Icc.mp hx, Nat.div_mul_le_self d 2 ] );
    refine le_trans h_prod_floor ?_;
    rw [ ← Finset.prod_sdiff <| Finset.Icc_subset_Icc_right <| Nat.div_le_self d 2 ];
    refine' le_mul_of_one_le_left ( Finset.prod_nonneg fun _ _ => by positivity ) _;
    exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by positivity ) fun x hx => show ( d : ℚ ) / x ≥ 1 from by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;> norm_cast <;> linarith [ Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hx |>.1 ), Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hx |>.1 ), Nat.div_mul_le_self d 2, Finset.mem_sdiff.mp hx |>.2 |> fun h => show x > d / 2 from lt_of_not_ge fun h' => h <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hx |>.1 ) ], h' ⟩ ] );
  exact_mod_cast ( by nlinarith [ pow_pos ( zero_lt_two' ℚ ) ( d / 2 ) ] : ( d ! : ℚ ) * 2 ^ ( d / 2 ) ≤ d ^ d )

/-
For d ≥ 2: lambdaD d + 1 ≤ 2^((d²+3d+6)/2)
-/
private lemma lambdaD_succ_le_pow2 (d : ℕ) (hd : 2 ≤ d) :
    lambdaD d + 1 ≤ 2 ^ ((d ^ 2 + 3 * d + 6) / 2) := by
  -- We need to show that $2^{d*(d-1)/2 + 2*d + 3} \leq 2^{(d^2+3d+6)/2}$.
  suffices h_exp : d*(d-1)/2 + 2*d + 3 ≤ (d^2+3*d+6)/2 by
    refine' le_trans _ ( pow_le_pow_right₀ ( by decide ) h_exp );
    exact Nat.succ_le_of_lt ( pow_lt_pow_right₀ ( by decide ) ( Nat.lt_succ_self _ ) );
  rw [ Nat.le_div_iff_mul_le ] <;> nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ d ), Nat.div_mul_le_self ( d * ( d - 1 ) ) 2 ]

/-
For d ≥ 3: the intermediate bound implies the improved bound.
-/
private theorem coeffBound_le_improved_d_ge3 (p : Polynomial ℤ)
    (hd : 3 ≤ p.natDegree) (hA : 0 < p.leadingCoeff) :
    (coeffBound p).toNat ≤
      (coeffSum p * p.natDegree ^ p.natDegree) ^ (2 * p.natDegree ^ 2 + 10 * p.natDegree) := by
  -- By Lemma~\ref{lem:coeff_bound_le_intermediate}, we have:
  have h_intermediate : coeffBound p ≤ 4 ^ (p.natDegree + 1) * (coeffSum p) ^ (p.natDegree + 2) * (coeffXp p) ^ (p.natDegree ^ 2 + p.natDegree) * ((lambdaD p.natDegree + 1) : ℤ) ^ (p.natDegree + 1) := by
    convert coeffBound_le_intermediate p ( by linarith ) hA using 1;
  have h_coeffXp : coeffXp p ≤ 8 * (coeffSum p) ^ 2 * (p.natDegree !) ^ 2 := by
    convert coeffXp_le_8S2fact2 p ( by linarith ) hA using 1
  have h_lambdaD : (lambdaD p.natDegree + 1 : ℤ) ≤ 2 ^ ((p.natDegree ^ 2 + 3 * p.natDegree + 6) / 2) := by
    exact_mod_cast lambdaD_succ_le_pow2 p.natDegree ( by linarith );
  -- By Lemma~\ref{lem:dd_ge_factorial_mul_pow2}, we have $d^d \geq d! \cdot 2^{d/2}$.
  have h_dd_ge_factorial_mul_pow2 : (p.natDegree ! : ℤ) ^ (2 * p.natDegree ^ 2 + 2 * p.natDegree) * 2 ^ ((p.natDegree ^ 3 - p.natDegree) + 8 * p.natDegree ^ 2) ≤ (p.natDegree ^ p.natDegree) ^ (2 * p.natDegree ^ 2 + 10 * p.natDegree) := by
    have h_dd_ge_factorial_mul_pow2 : (p.natDegree ! : ℤ) ^ (2 * p.natDegree ^ 2 + 2 * p.natDegree) * 2 ^ ((p.natDegree ^ 3 - p.natDegree) + 8 * p.natDegree ^ 2) ≤ (p.natDegree ^ p.natDegree) ^ (2 * p.natDegree ^ 2 + 2 * p.natDegree) * 2 ^ (8 * p.natDegree ^ 2) := by
      have h_dd_ge_factorial_mul_pow2 : (p.natDegree ! : ℤ) ^ (2 * p.natDegree ^ 2 + 2 * p.natDegree) * 2 ^ ((p.natDegree ^ 3 - p.natDegree)) ≤ (p.natDegree ^ p.natDegree) ^ (2 * p.natDegree ^ 2 + 2 * p.natDegree) := by
        have h_dd_ge_factorial_mul_pow2 : (p.natDegree ! : ℤ) * 2 ^ (p.natDegree / 2) ≤ p.natDegree ^ p.natDegree := by
          exact_mod_cast dd_ge_factorial_mul_pow2 p.natDegree ( by linarith );
        refine le_trans ?_ ( pow_le_pow_left₀ ( by positivity ) h_dd_ge_factorial_mul_pow2 _ );
        rw [ mul_pow ];
        rw [ ← pow_mul ];
        exact mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by decide ) ( Nat.sub_le_of_le_add <| by nlinarith [ Nat.div_add_mod p.natDegree 2, Nat.mod_lt p.natDegree two_pos ] ) ) ( by positivity );
      convert mul_le_mul_of_nonneg_right h_dd_ge_factorial_mul_pow2 ( pow_nonneg ( by norm_num : ( 0 : ℤ ) ≤ 2 ) ( 8 * p.natDegree ^ 2 ) ) using 1 ; ring;
    refine le_trans h_dd_ge_factorial_mul_pow2 ?_;
    rw [ show ( 2 * p.natDegree ^ 2 + 10 * p.natDegree : ℕ ) = ( 2 * p.natDegree ^ 2 + 2 * p.natDegree ) + ( 8 * p.natDegree ) by ring, pow_add ];
    rw [ pow_add, pow_add ];
    gcongr;
    rw [ ← pow_mul ];
    exact_mod_cast Nat.pow_le_pow_left ( show 2 ≤ p.natDegree by linarith ) _ |> le_trans <| Nat.pow_le_pow_right ( by linarith ) <| by nlinarith;
  -- By combining the inequalities from h_intermediate, h_coeffXp, and h_lambdaD, we can bound the coefficient bound.
  have h_combined : coeffBound p ≤ (coeffSum p) ^ (2 * p.natDegree ^ 2 + 3 * p.natDegree + 2) * 2 ^ (3 * p.natDegree ^ 2 + 5 * p.natDegree + 2) * (p.natDegree ! : ℤ) ^ (2 * p.natDegree ^ 2 + 2 * p.natDegree) * 2 ^ ((p.natDegree ^ 2 + 3 * p.natDegree + 6) / 2 * (p.natDegree + 1)) := by
    refine le_trans h_intermediate ?_;
    refine' le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) h_lambdaD _ ) ( by positivity ) ) _;
    refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( Nat.cast_le.mpr h_coeffXp ) _ ) ( by positivity ) ) ( by positivity ) ) _;
    norm_num [ pow_mul ] ; ring_nf ; norm_num;
    norm_num [ pow_mul', ← mul_pow ];
    norm_num [ mul_assoc, ← mul_pow ];
  have h_final_bound : coeffBound p ≤ (coeffSum p) ^ (2 * p.natDegree ^ 2 + 3 * p.natDegree + 2) * (p.natDegree ^ p.natDegree) ^ (2 * p.natDegree ^ 2 + 10 * p.natDegree) := by
    refine le_trans h_combined ?_;
    refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_dd_ge_factorial_mul_pow2 <| by positivity );
    rw [ mul_assoc, mul_assoc ];
    refine' mul_le_mul_of_nonneg_left _ ( by positivity );
    rw [ mul_left_comm, ← pow_add ];
    exact mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by decide ) ( by nlinarith only [ hd, Nat.div_mul_le_self ( p.natDegree ^ 2 + 3 * p.natDegree + 6 ) 2, Nat.sub_add_cancel ( show p.natDegree ≤ p.natDegree ^ 3 from Nat.le_self_pow ( by linarith ) _ ) ] ) ) ( by positivity );
  rw [ mul_pow ];
  refine' le_trans _ ( Nat.mul_le_mul_right _ ( pow_le_pow_right₀ ( show 1 ≤ coeffSum p from _ ) ( show 2 * p.natDegree ^ 2 + 3 * p.natDegree + 2 ≤ 2 * p.natDegree ^ 2 + 10 * p.natDegree from by nlinarith only [ hd ] ) ) );
  · grind +extAll;
  · exact coeffSum_pos p ( by linarith ) ( by linarith )

/-
For d = 2: direct bound on coeffBound.
-/
set_option maxHeartbeats 1600000 in
private theorem coeffBound_le_improved_d2 (p : Polynomial ℤ)
    (hd : p.natDegree = 2) (hA : 0 < p.leadingCoeff) :
    (coeffBound p).toNat ≤
      (coeffSum p * p.natDegree ^ p.natDegree) ^ (2 * p.natDegree ^ 2 + 10 * p.natDegree) := by
  -- Split into two cases: polySum p = 1 and polySum p ≥ 2.
  by_cases hS : coeffSum p = 1;
  · -- Since $p$ is a monic polynomial of degree 2 with positive leading coefficient, we have $p = X^2$.
    have hp : p = Polynomial.X^2 := by
      unfold coeffSum at hS; simp_all +decide [ Finset.sum_range_succ' ] ;
      have h_coeff2 : p.coeff 2 = 1 := by
        simp_all +decide [ Polynomial.leadingCoeff, Polynomial.natDegree ];
        grind
      have h_coeff1 : p.coeff 1 = 0 := by
        omega
      have h_coeff0 : p.coeff 0 = 0 := by
        omega
      exact Polynomial.as_sum_range_C_mul_X_pow p ▸ by simp_all +decide [ Finset.sum_range_succ' ] ;
    unfold coeffBound coeffSum at * ; simp_all +decide;
    unfold coeffMp coeffQp coeffZp posMajorant; norm_num [ Finset.sum_range_succ', lambdaD ] ;
    unfold polyA coeffXp coeffMp coeffKp coeffYp coeffQp; norm_num [ Polynomial.sum_over_range ] ;
    unfold polyA posMajorant coeffXp coeffMp coeffKp; norm_num [ Finset.sum_range_succ', Polynomial.eval_finset_sum ] ;
    unfold polyA posMajorant coeffXp; norm_num [ Polynomial.sum_over_range ] ;
    unfold polyA explicitTailParam; norm_num [ Finset.sum_range_succ', Polynomial.eval_finset_sum ] ;
    unfold Hzero; norm_num [ Polynomial.natDegree_X_pow, Polynomial.leadingCoeff_X_pow ] ;
    norm_num [ Finset.sum_range_succ, lambdaD ];
  · -- Apply the intermediate bound with S ≥ 2.
    have h_intermediate : (coeffBound p : ℤ) ≤ 4 ^ (p.natDegree + 1) * (coeffSum p : ℤ) ^ (p.natDegree + 2) * (coeffXp p : ℤ) ^ (p.natDegree ^ 2 + p.natDegree) * ((lambdaD p.natDegree + 1 : ℕ) : ℤ) ^ (p.natDegree + 1) := by
      convert coeffBound_le_intermediate p ( by linarith ) hA using 1;
    -- Substitute the bounds for coeffXp and lambdaD into the intermediate bound.
    have h_subst : (coeffBound p : ℤ) ≤ 4 ^ (p.natDegree + 1) * (coeffSum p : ℤ) ^ (p.natDegree + 2) * (8 * (coeffSum p) ^ 2 * (p.natDegree !) ^ 2) ^ (p.natDegree ^ 2 + p.natDegree) * (129 : ℤ) ^ (p.natDegree + 1) := by
      refine le_trans h_intermediate ?_;
      gcongr;
      · exact_mod_cast coeffXp_le_8S2fact2 p ( by linarith ) hA;
      · norm_num [ hd, lambdaD ];
    simp_all +decide;
    refine le_trans h_subst ?_;
    rcases n : coeffSum p with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> simp_all +decide;
    grind

/-- For d ≥ 2, the coefficient bound is at most (S * d^d)^(2d²+10d). -/
theorem coeffBound_le_improved (p : Polynomial ℤ)
    (hd : 2 ≤ p.natDegree) (hA : 0 < p.leadingCoeff) :
    (coeffBound p).toNat ≤
      (coeffSum p * p.natDegree ^ p.natDegree) ^ (2 * p.natDegree ^ 2 + 10 * p.natDegree) := by
  by_cases h2 : p.natDegree = 2
  · exact coeffBound_le_improved_d2 p h2 hA
  · exact coeffBound_le_improved_d_ge3 p (by omega) hA

/-
There exist k distinct positive naturals summing to T, provided T ≥ k(k+1)/2 and k ≥ 1.
-/
theorem exists_distinct_pos_sum (k T : ℕ) (hk : 0 < k) (hT : k * (k + 1) / 2 ≤ T) :
    ∃ J : Finset ℕ, J.card = k ∧ (∀ j ∈ J, 0 < j) ∧ (∑ j ∈ J, j : ℕ) = T := by
  induction' k with k ih generalizing T;
  · contradiction;
  · rcases k with ( _ | k ) <;> simp_all +decide;
    · exact ⟨ { T }, by aesop ⟩;
    · obtain ⟨ J, hJ₁, hJ₂, hJ₃ ⟩ := ih ( T - ( k + 2 ) ) ( Nat.le_sub_of_add_le ( by linarith [ Nat.div_add_mod ( ( k + 1 + 1 ) * ( k + 1 + 1 + 1 ) ) 2, Nat.mod_lt ( ( k + 1 + 1 ) * ( k + 1 + 1 + 1 ) ) two_pos, Nat.div_mul_le_self ( ( k + 1 ) * ( k + 1 + 1 ) ) 2 ] ) );
      use J.image ( fun x => x + 1 ) ∪ { 1 } ; simp_all +decide;
      rw [ Finset.sum_insert, Finset.sum_image ] <;> norm_num;
      · rw [ Finset.card_insert_of_notMem ] <;> norm_num [ Finset.sum_add_distrib, hJ₁ ];
        · exact ⟨ by rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ] ; linarith, by linarith [ Nat.sub_add_cancel ( show k + 2 ≤ T from by nlinarith [ Nat.div_mul_cancel ( show 2 ∣ ( k + 1 + 1 ) * ( k + 1 + 1 + 1 ) from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ) ] ) ] ⟩;
        · exact fun h => by simpa using hJ₂ 0 h;
      · exact fun h => by simpa using hJ₂ 0 h;

/-
Degree-1 case: direct proof that every N ≥ S^12 is representable.
-/
theorem degree_one_case (p : Polynomial ℤ)
    (hd : p.natDegree = 1) (hA : 0 < p.leadingCoeff)
    (hgcd : ∀ q, Nat.Prime q → ∃ n : ℕ, ¬ ((q : ℤ) ∣ p.eval (n : ℤ))) :
    ∀ N : ℕ, coeffSum p ^ 12 ≤ N →
      ∃ J : Finset ℕ, (∀ j ∈ J, 0 < j) ∧ (N : ℤ) = ∑ i ∈ J, p.eval (i : ℤ) := by
  -- Write p as A * X + B, where A > 0 and B is an integer.
  obtain ⟨A, B, hA_pos, hB⟩ : ∃ A B : ℤ, 0 < A ∧ p = Polynomial.C A * Polynomial.X + Polynomial.C B := by
    exact ⟨ p.leadingCoeff, p.coeff 0, hA, by nth_rw 1 [ Polynomial.eq_X_add_C_of_natDegree_le_one ( le_of_eq hd ) ] ; simp +decide [ Polynomial.leadingCoeff, hd ] ⟩;
  -- Since $\gcd(A, B) = 1$, we can find a positive integer $k$ such that $1 \leq k \leq A$ and $A \mid (N - kB)$.
  have h_exists_k : ∀ N : ℕ, (A.natAbs + B.natAbs) ^ 12 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k ≤ A.natAbs ∧ A ∣ (N - k * B) := by
    -- Since $\gcd(A, B) = 1$, we can find a positive integer $k$ such that $1 \leq k \leq A$ and $kB \equiv N \pmod{A}$.
    have h_exists_k : ∀ N : ℕ, (A.natAbs + B.natAbs) ^ 12 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k ≤ A.natAbs ∧ k * B ≡ N [ZMOD A] := by
      -- Since $\gcd(A, B) = 1$, we can find a positive integer $k$ such that $kB \equiv N \pmod{A}$.
      have h_exists_k : ∀ N : ℕ, (A.natAbs + B.natAbs) ^ 12 ≤ N → ∃ k : ℤ, k * B ≡ N [ZMOD A] := by
        -- Since $\gcd(A, B) = 1$, we can find a positive integer $k$ such that $kB \equiv 1 \pmod{A}$.
        have h_exists_k : Int.gcd A B = 1 := by
          contrapose! hgcd;
          obtain ⟨ q, hq₁, hq₂, hq₃ ⟩ := Nat.Prime.not_coprime_iff_dvd.mp hgcd;
          exact ⟨ q, hq₁, fun n => by simpa [ hB ] using dvd_add ( dvd_mul_of_dvd_left ( Int.natCast_dvd.mpr hq₂ ) _ ) ( Int.natCast_dvd.mpr hq₃ ) ⟩;
        have := Int.gcd_eq_gcd_ab A B;
        exact fun N hN => ⟨ N * Int.gcdB A B, by rw [ Int.modEq_iff_dvd ] ; use Int.gcdA A B * N; nlinarith ⟩;
      intros N hN
      obtain ⟨k, hk⟩ := h_exists_k N hN
      use Int.toNat (k % A) + if Int.toNat (k % A) = 0 then A.natAbs else 0;
      split_ifs <;> simp_all +decide [Int.ModEq, Int.emod_nonneg _ hA_pos.ne'];
      · simp_all +decide [ abs_of_pos hA_pos ];
        exact ⟨ by linarith [ abs_of_pos hA_pos, Int.emod_nonneg k hA_pos.ne' ], by simpa [ Int.add_emod, Int.mul_emod ] using hk ⟩;
      · exact ⟨ by linarith, by rw [ abs_of_pos hA_pos ] ; exact Int.le_of_lt ( Int.emod_lt_of_pos _ hA_pos ), by simpa [ Int.mul_emod ] using hk ⟩;
    exact fun N hN => by obtain ⟨ k, hk₁, hk₂, hk₃ ⟩ := h_exists_k N hN; exact ⟨ k, hk₁, hk₂, hk₃.dvd ⟩ ;
  -- Let $T = \frac{N - kB}{A}$, then $T \geq k(k + 1) / 2$.
  intros N hN
  obtain ⟨k, hk1, hk2, hk3⟩ := h_exists_k N (by
  unfold coeffSum at hN; simp_all +decide ;
  convert hN using 2 ; norm_num [ Finset.sum_range_succ', Polynomial.coeff_eq_zero_of_natDegree_lt ])
  set T := (N - k * B) / A with hT_def
  have hT_ge : T ≥ k * (k + 1) / 2 := by
    -- Since $N \geq (A.natAbs + B.natAbs)^{12}$ and $A \geq 1$, we have $N - k * B \geq (A.natAbs + B.natAbs)^{12} - k * |B|$.
    have hN_minus_kB_ge : (N : ℤ) - k * B ≥ (A.natAbs + B.natAbs) ^ 12 - k * B.natAbs := by
      have hN_minus_kB_ge : (N : ℤ) ≥ (A.natAbs + B.natAbs) ^ 12 := by
        norm_cast;
        unfold coeffSum at hN;
        simp_all +decide [ Finset.sum_range_succ', Polynomial.coeff_eq_zero_of_natDegree_lt ];
      cases abs_cases B <;> simp +decide [ * ] at * <;> nlinarith;
    -- Since $A \geq 1$, we have $(A.natAbs + B.natAbs)^{12} - k * B.natAbs \geq A.natAbs * (k * (k + 1) / 2)$.
    have h_div_ge : (A.natAbs + B.natAbs) ^ 12 - k * B.natAbs ≥ A.natAbs * (k * (k + 1) / 2) := by
      refine' Nat.le_sub_of_add_le' _;
      refine' le_trans _ ( Nat.pow_le_pow_right ( by positivity ) ( show 12 ≥ 3 by decide ) );
      nlinarith [ Nat.div_mul_le_self ( k * ( k + 1 ) ) 2, Nat.zero_le ( B.natAbs * k ), Nat.zero_le ( B.natAbs * A.natAbs ), Nat.zero_le ( B.natAbs ^ 2 * k ), Nat.zero_le ( B.natAbs ^ 2 * A.natAbs ), Nat.zero_le ( B.natAbs ^ 3 ), Nat.zero_le ( A.natAbs ^ 2 * k ), Nat.zero_le ( A.natAbs ^ 2 * B.natAbs ), Nat.zero_le ( A.natAbs ^ 3 ) ];
    rw [ ge_iff_le, Int.le_ediv_iff_mul_le ] <;> norm_num at *;
    · rw [ Nat.le_sub_iff_add_le ] at h_div_ge;
      · grind +qlia;
      · contrapose! h_div_ge;
        rw [ Nat.sub_eq_zero_of_le h_div_ge.le ] ; norm_num;
        exact ⟨ by linarith, by nlinarith only [ hk1 ] ⟩;
    · positivity;
  -- By the lemma `exists_distinct_pos_sum`, there exists a set $J$ of $k$ distinct positive integers such that $\sum_{j \in J} j = T$.
  obtain ⟨J, hJ_card, hJ_pos, hJ_sum⟩ : ∃ J : Finset ℕ, J.card = k ∧ (∀ j ∈ J, 0 < j) ∧ (∑ j ∈ J, j : ℤ) = T := by
    have := exists_distinct_pos_sum k ( Int.toNat T ) hk1 ?_ <;> norm_num at *;
    · obtain ⟨ J, hJ₁, hJ₂, hJ₃ ⟩ := this; use J;
      exact ⟨ hJ₁, hJ₂, by rw [ ← Nat.cast_sum, hJ₃, Int.toNat_of_nonneg ( by exact Int.le_ediv_of_mul_le ( by positivity ) ( by nlinarith [ Int.mul_ediv_cancel' hk3, show ( k : ℤ ) * ( k + 1 ) / 2 ≥ 0 by positivity ] ) ) ] ⟩;
    · grind;
  use J; simp_all +decide [ Finset.sum_add_distrib, mul_comm ] ;
  rw [ ← Finset.mul_sum _ _ _, hJ_sum ] ; nlinarith [ Int.ediv_mul_cancel hk3 ] ;

/-
Degree-0 case: if p is a positive constant with gcd condition,
    then p = 1 and every N ≥ 1 is representable.
-/
theorem degree_zero_case (p : Polynomial ℤ)
    (hd : p.natDegree = 0) (hA : 0 < p.leadingCoeff)
    (hgcd : ∀ q, Nat.Prime q → ∃ n : ℕ, ¬ ((q : ℤ) ∣ p.eval (n : ℤ))) :
    ∀ N : ℕ, 1 ≤ N →
      ∃ J : Finset ℕ, (∀ j ∈ J, 0 < j) ∧ (N : ℤ) = ∑ i ∈ J, p.eval (i : ℤ) := by
  -- Since p is a constant polynomial, we can write p(x) = c for some constant c.
  obtain ⟨c, hc⟩ : ∃ c : ℤ, p = Polynomial.C c := by
    exact ⟨ p.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hd ⟩;
  simp_all +decide [ Polynomial.leadingCoeff, Polynomial.natDegree ];
  -- Since $c$ is a positive constant and satisfies the gcd condition, we must have $c = 1$.
  have hc_one : c = 1 := by
    contrapose! hgcd;
    exact ⟨ Nat.minFac ( Int.natAbs c ), Nat.minFac_prime ( mt Int.natAbs_eq_iff.mp <| by aesop ), Int.natCast_dvd.mpr <| Nat.minFac_dvd _ ⟩;
  exact fun N hN => ⟨ Finset.Icc 1 N, fun j hj => by linarith [ Finset.mem_Icc.mp hj ], by simp +decide [ hc_one ] ⟩

theorem general_polynomial_bound (p : Polynomial ℤ)
    (hA : 0 < p.leadingCoeff)
    (hgcd : ∀ q, Nat.Prime q → ∃ n : ℕ, ¬ ((q : ℤ) ∣ p.eval (n : ℤ))) :
    let d := p.natDegree
    let S := ∑ i ∈ Finset.range (d + 1), (p.coeff i).natAbs
    ∀ N : ℕ, (S * d^d)^(2 * d^2 + 10 * d) ≤ N →
      ∃ J : Finset ℕ, (∀ j ∈ J, 0 < j) ∧ N = ∑ i ∈ J, p.eval (i : ℤ) := by
  intro d S N hN
  by_cases hd0 : p.natDegree = 0
  · -- Degree 0 case
    simp [show d = 0 from hd0] at hN
    exact degree_zero_case p hd0 hA hgcd N hN
  · have hd_nat : d = p.natDegree := rfl
    by_cases hd1 : p.natDegree = 1
    · -- Degree 1 case
      have hN' : coeffSum p ^ 12 ≤ N := by simp [show d = 1 from hd1] at hN; exact hN
      exact degree_one_case p hd1 hA hgcd N hN'
    · -- Degree ≥ 2 case
      have hgcd' := gcd_condition_bridge p hgcd
      have hd_ge : 1 ≤ p.natDegree := by omega
      have hd2 : 2 ≤ p.natDegree := by omega
      have hbound : (coeffBound p).toNat ≤
          (coeffSum p * p.natDegree ^ p.natDegree) ^ (2 * p.natDegree ^ 2 + 10 * p.natDegree) :=
        coeffBound_le_improved p hd2 hA
      exact height_only_bound p hd_ge hA hgcd' N (le_trans hbound hN)

#print axioms general_polynomial_bound
