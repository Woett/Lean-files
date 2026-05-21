import Mathlib

/-
In this file we prove that if d ≥ 9, then every N ≥ 2^{6d²+9d+5} can be written
as a sum of distinct d-th powers of natural numbers. The assumption d ≥ 9 is
fine, as the exact bound for d < 9 is already known; https://oeis.org/A001661.
With the bound below we strengthen a result by Kim.

Kim, D. On the largest integer that is not a sum of distinct positive nth
powers, Journal of Integer Sequences, Volume 20, Issue 7 (2017).

In principle, sufficiently good bounds on this quantity could answer Erdős
Problem #345 (https://www.erdosproblems.com/345) in the negative.

Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) did the formalization
based on an improved version of Kim's proof, which was written down by ChatGPT.

Lean version: leanprover/lean4:v4.28.0
-/

open Polynomial Finset BigOperators

noncomputable section

/-- Leading coefficient times d!. For monomials X^d, this equals d!. -/
def polyA (p : Polynomial ℤ) : ℤ := p.leadingCoeff * (p.natDegree.factorial : ℤ)

/-- The defining property of τ_p(G): for all u, v with T ≤ u < v ≤ u + G,
    we have 0 < p(u) < p(v) ≤ 2·p(u). -/
def TauProp (p : Polynomial ℤ) (G T : ℕ) : Prop :=
  ∀ u v : ℕ, T ≤ u → u < v → v ≤ u + G →
    (0 < p.eval (u : ℤ)) ∧ (p.eval (u : ℤ) < p.eval (v : ℤ)) ∧
    (p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ))

theorem tauProp_pos {p : Polynomial ℤ} {G T : ℕ} (hG : 1 ≤ G)
    (hT : TauProp p G T) {u : ℕ} (hu : T ≤ u) :
    0 < p.eval (u : ℤ) :=
  (hT u (u + 1) hu (by omega) (by omega)).1

/-
If a finite index set I represents K consecutive integers starting at C,
and we have an infinite sequence of positive "tail" values b(t_m) satisfying
b(t_m) ≤ K + ∑_{ν=1}^{m-1} b(t_ν), then every N ≥ C is representable.
-/

/-- The interval [C, C+K-1] is contained in the set of subset sums of b over I. -/
def RepresentsInterval (b : ℕ → ℤ) (I : Finset ℕ) (C : ℤ) (K : ℕ) : Prop :=
  ∀ N : ℤ, C ≤ N → N < C + K →
    ∃ J : Finset ℕ, J ⊆ I ∧ ∑ i ∈ J, b i = N

/-
Inductive step; if I_m represents [C, C + K - 1 + S_m] where
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

/-
For every d ≥ 1, (1 + 1/(6d))^d ≤ 6/5.
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

/-- H_0(p) = A + ∑_{i=0}^{d-1} |a_i| where A = leading coefficient -/
noncomputable def Hzero (p : Polynomial ℤ) : ℤ :=
  p.leadingCoeff + ∑ i ∈ Finset.range p.natDegree, |p.coeff i|

/-- The difference operator Δ_h f(X) = f(X + h) - f(X). -/
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

/-- The explicit tail parameter 𝔗_p(G) = max(6dG, ⌈4H₀(p)/A⌉). -/
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
The explicit tau bound: τ_p(G) ≤ 𝔗_p(G). That is, explicitTailParam p G satisfies the TauProp for gap G.
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
We build disjoint Finset pairs (P, N) tracking which offsets get positive
vs negative signs when expanding the iterated difference operator.
-/

/-- One step of the P/N construction: applying diffOp with shift h
    transforms (P, N) to (P.image(·+h) ∪ N, P ∪ N.image(·+h)). -/
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

/-
The foldl evaluation equals the P/N sum. We prove this together
    with disjointness and bounds as an inductive package.
-/
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

/-- A threshold for p: every N ≥ C is representable as a sum of distinct
    positive values p(n) with distinct indices. -/
def IsThreshold (p : Polynomial ℤ) (C : ℕ) : Prop :=
  ∀ N : ℕ, C ≤ N →
    ∃ J : Finset ℕ, (∀ j ∈ J, 0 < p.eval (j : ℤ)) ∧
      (N : ℤ) = ∑ i ∈ J, p.eval (i : ℤ)

/-- A residue datum modulo a for p is a finite set E ⊆ ℕ -/
structure ResidueDatum (p : Polynomial ℤ) (a : ℕ) where
  E : Finset ℕ

/-- e(R) = max(E ∪ {0}) -/
noncomputable def ResidueDatum.eMax {p : Polynomial ℤ} {a : ℕ} (R : ResidueDatum p a) : ℕ :=
  R.E.sup id

/-
Monotonicity of explicitTailParam in G.
-/
theorem explicitTailParam_mono (p : Polynomial ℤ) (G G' : ℕ) (hle : G ≤ G') :
    explicitTailParam p G ≤ explicitTailParam p G' := by
  exact max_le_max ( by gcongr ) le_rfl

theorem isThreshold_of_data
    (p : Polynomial ℤ)
    (T : ℕ) (K : ℕ) (hK_val : (K : ℤ) = p.eval (T : ℤ))
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
    · exact h_pos j (by linarith [hI_ge j h])
    · exact h_pos (t m) (ht_ge m),
    hJ2.symm⟩

theorem isThreshold_mono {p : Polynomial ℤ} {C C' : ℕ}
    (h : IsThreshold p C) (hle : C ≤ C') : IsThreshold p C' :=
  fun N hN => h N (le_trans hle hN)

def monomialPoly (d : ℕ) : Polynomial ℤ := Polynomial.X ^ d

theorem monomialPoly_natDegree (d : ℕ) (_hd : 1 ≤ d) :
    (monomialPoly d).natDegree = d := by
  simp [monomialPoly]

theorem monomialPoly_polyA (d : ℕ) (_hd : 1 ≤ d) :
    polyA (monomialPoly d) = d.factorial := by
  simp [polyA, monomialPoly]

theorem monomialPoly_leadingCoeff_pos (d : ℕ) (_hd : 1 ≤ d) :
    0 < (monomialPoly d).leadingCoeff := by
  simp [monomialPoly]

theorem monomialPoly_natDegree_pos (d : ℕ) (hd : 1 ≤ d) :
    1 ≤ (monomialPoly d).natDegree := by
  simp [monomialPoly]; exact hd

/-
The subset sums of d-th powers from an interval of length 4^d cover all residues modulo d!.
-/

/-- An interval of L consecutive integers starting at b. -/
def Intv (b : ℤ) (L : ℕ) : Finset ℤ := Finset.Ico b (b + (L : ℤ))

/-- A finite set A of integers is (e, m)-complete if the subset sums of e-th powers
    from A cover all residue classes modulo m. We require m ≥ 1 (via NeZero). -/
def IsEMComplete (A : Finset ℤ) (e : ℕ) (m : ℕ) [NeZero m] : Prop :=
  ∀ r : ZMod m, ∃ B : Finset ℤ, B ⊆ A ∧
    (↑(∑ x ∈ B, x ^ e) : ZMod m) = r

/-- The p-adic valuation of n!, denoted a_p(n) in the proof. -/
def ap (p n : ℕ) : ℕ := padicValNat p n.factorial

/-- The primorial below p: product of all primes less than p.
    P_p = ∏_{q < p, q prime} q. -/
def primeProdBelow (p : ℕ) : ℕ := primorial (p - 1)

/-- The geometric sum G_p(d) = ∑_{j=0}^{a_p(d)-1} p^j. -/
def geomSumAp (p d : ℕ) : ℕ := ∑ j ∈ Finset.range (ap p d), p ^ j

/-- L_p(d) = p · P_p · G_p(d). -/
def Lp (p d : ℕ) : ℕ := p * primeProdBelow p * geomSumAp p d

/-- Rad(d) = max over primes p ≤ d of L_p(d), or 1 if d ≤ 1. -/
noncomputable def Rad (d : ℕ) : ℕ :=
  if h : d ≤ 1 then 1
  else ((Finset.Icc 2 d).filter Nat.Prime).sup' (by
    exact ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 2, by omega⟩, by decide⟩⟩) (fun p => Lp p d)

/-- The set of usable elements for prime p in a set J:
    {n ∈ J : primeProdBelow p | n ∧ ¬(p | n)}. -/
def usableSet (p : ℕ) (J : Finset ℤ) : Finset ℤ :=
  J.filter (fun n => (primeProdBelow p : ℤ) ∣ n ∧ ¬((p : ℤ) ∣ n))

theorem mem_Intv_iff (b : ℤ) (L : ℕ) (x : ℤ) :
    x ∈ Intv b L ↔ b ≤ x ∧ x < b + (L : ℤ) := by
  simp [Intv]

theorem Intv_subset_of_le (b : ℤ) (L L' : ℕ) (h : L ≤ L') :
    Intv b L ⊆ Intv b L' := by
  intro x hx; simp [mem_Intv_iff] at *; omega

theorem sharpened_valuation_bound (p n : ℕ) (hp : Nat.Prime p) (hn : 1 ≤ n) :
    ap p n * (p - 1) ≤ n - 1 := by
  nontriviality;
  induction' n using Nat.strongRecOn with n ih;
  -- By Legendre's formula, we have $ap p n = n / p + ap p (n / p)$.
  have h_legendre : ap p n = n / p + ap p (n / p) := by
    unfold ap;
    haveI := Fact.mk hp; rw [ padicValNat_factorial, padicValNat_factorial ];
    any_goals exact Nat.lt_succ_self _;
    rcases k : Nat.log p n with ( _ | k ) <;> simp_all +decide [ Nat.div_div_eq_div_mul, Finset.sum_Ico_eq_sum_range ];
    · rw [ Nat.log_of_lt ] <;> cases k <;> simp_all +decide [ Nat.div_eq_of_lt ];
      · interval_cases p <;> trivial;
      · interval_cases p <;> trivial;
    · simp +arith +decide [ add_comm 1, Finset.sum_range_succ', pow_add ];
      ac_rfl;
  rcases p with ( _ | _ | p ) <;> simp_all +decide;
  by_cases h₂ : n / (p + 1 + 1) = 0;
  · simp_all +decide [ ap ];
    norm_num [ Nat.div_eq_of_lt ( by linarith : n < p + 1 + 1 ) ];
  · nlinarith [ Nat.div_mul_le_self n ( p + 1 + 1 ), ih ( n / ( p + 1 + 1 ) ) ( Nat.div_lt_self hn ( by linarith ) ) ( Nat.pos_of_ne_zero h₂ ), Nat.sub_add_cancel ( show 1 ≤ n from hn ), Nat.sub_add_cancel ( show 1 ≤ n / ( p + 1 + 1 ) from Nat.pos_of_ne_zero h₂ ) ]

/-
For prime p ≤ d with d ≥ 1, a_p(d) ≥ 1.
-/
theorem ap_pos_of_prime_le (p d : ℕ) (hp : Nat.Prime p) (hpd : p ≤ d) :
    1 ≤ ap p d := by
  refine' Nat.pos_of_ne_zero _;
  unfold ap;
  simp +zetaDelta at *;
  exact ⟨ hp.ne_one, Nat.factorial_ne_zero _, Nat.dvd_factorial hp.pos hpd ⟩

/-
a_p(d) ≤ d for any prime p and d ≥ 1.
-/
theorem ap_le_d (p d : ℕ) (hp : Nat.Prime p) (hn : 1 ≤ d) :
    ap p d ≤ d := by
  -- From the sharpened valuation bound: ap p d * (p - 1) ≤ d - 1.
  have h_bound : ap p d * (p - 1) ≤ d - 1 := by
    exact sharpened_valuation_bound p d hp hn;
  nlinarith [ Nat.sub_pos_of_lt hp.one_lt, Nat.sub_add_cancel hn ]

/-
Power bound: p^{a_p(d) - 1} ≤ 2^{d - p} for prime p ≤ d.
-/
theorem power_bound_from_valuation (p d : ℕ) (hp : Nat.Prime p) (hpd : p ≤ d) (hd : 1 ≤ d) :
    p ^ (ap p d - 1) ≤ 2 ^ (d - p) := by
  have h_sharpened_bound : ap p d * (p - 1) ≤ d - 1 := by
    exact sharpened_valuation_bound p d hp hd;
  -- From the inequality $(ap p d - 1) * (p - 1) \leq d - p$, we can exponentiate both sides with base 2.
  have h_exp : 2 ^ ((ap p d - 1) * (p - 1)) ≤ 2 ^ (d - p) := by
    exact pow_le_pow_right₀ ( by decide ) ( by nlinarith [ Nat.sub_add_cancel ( show 1 ≤ d from hd ), Nat.sub_add_cancel ( show 1 ≤ p from hp.pos ), Nat.sub_add_cancel ( show 1 ≤ ap p d from ap_pos_of_prime_le p d hp hpd ), Nat.sub_add_cancel ( show p ≤ d from hpd ) ] );
  refine le_trans ?_ h_exp;
  rw [ pow_mul' ] ; gcongr;
  exact Nat.le_of_pred_lt ( Nat.recOn p ( by norm_num ) fun n ihn => by cases n <;> simp_all +decide [ Nat.pow_succ' ] ; linarith )

/-
p ≤ 2^(p-1) for any prime p.
-/
theorem residue_count_in_Intv (M L : ℕ) (hM : 1 ≤ M) (b : ℤ) (r : ℤ) :
    L / M ≤ ((Intv b L).filter (fun n => (M : ℤ) ∣ (n - r))).card := by
  -- Let $k = \lfloor L / M \rfloor$. Then $kM \leq L$, so $\text{Intv}(b, kM) \subseteq \text{Intv}(b, L)$.
  set k := L / M with hk
  have hkM : k * M ≤ L := by
    exact Nat.div_mul_le_self _ _;
  -- The set $\{n \in \text{Intv}(b, kM) \mid (M : \mathbb{Z}) \mid (n - r)\}$ contains at least $k$ elements.
  have h_set_card : Finset.card (Finset.filter (fun n : ℤ => (M : ℤ) ∣ (n - r)) (Finset.Ico b (b + k * M))) = k := by
    -- The set $\{n \in \text{Intv}(b, kM) \mid (M : \mathbb{Z}) \mid (n - r)\}$ is exactly the set of integers $n$ in the interval $[b, b + kM)$ such that $n \equiv r \pmod{M}$.
    have h_set_eq : Finset.filter (fun n : ℤ => (M : ℤ) ∣ (n - r)) (Finset.Ico b (b + k * M)) = Finset.image (fun i : ℕ => b + ((r - b) % M + i * M : ℤ)) (Finset.range k) := by
      ext n
      simp [Finset.mem_image, Finset.mem_filter];
      constructor;
      · intro hn
        obtain ⟨hn_range, hn_div⟩ := hn
        obtain ⟨a, ha⟩ : ∃ a : ℤ, n = b + ((r - b) % M + a * M : ℤ) := by
          obtain ⟨ a, ha ⟩ := hn_div;
          exact ⟨ a + ( r - b ) / M, by linarith [ Int.emod_add_mul_ediv ( r - b ) M ] ⟩;
        exact ⟨ Int.toNat a, by nlinarith [ Int.emod_nonneg ( r - b ) ( by positivity : ( M : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( r - b ) ( by positivity : ( M : ℤ ) > 0 ), Int.toNat_of_nonneg ( by nlinarith [ Int.emod_nonneg ( r - b ) ( by positivity : ( M : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( r - b ) ( by positivity : ( M : ℤ ) > 0 ) ] : 0 ≤ a ) ], by rw [ ha, Int.toNat_of_nonneg ( by nlinarith [ Int.emod_nonneg ( r - b ) ( by positivity : ( M : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( r - b ) ( by positivity : ( M : ℤ ) > 0 ) ] ) ] ⟩;
      · rintro ⟨ a, ha, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Int.emod_nonneg ( r - b ) ( by positivity : ( M : ℤ ) ≠ 0 ) ], by nlinarith [ Int.emod_lt_of_pos ( r - b ) ( by positivity : ( M : ℤ ) > 0 ) ] ⟩, by exact ⟨ - ( ( r - b ) / M ) + a, by linarith [ Int.emod_add_mul_ediv ( r - b ) M ] ⟩ ⟩ ;
    rw [ h_set_eq, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, * ];
    grind;
  refine' h_set_card ▸ Finset.card_mono _;
  exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) ], by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) ] ⟩, Finset.mem_filter.mp hx |>.2 ⟩

/-
The number of usable elements in an interval of length ≥ L_p(d) is at least p^{a_p(d)} - 1.
-/
theorem count_usable_elements (p d : ℕ) (hp : Nat.Prime p) (hpd : p ≤ d)
    (b : ℤ) (L : ℕ) (hL : Lp p d ≤ L) :
    p ^ ap p d - 1 ≤ (usableSet p (Intv b L)).card := by
  -- Set $M = p \cdot P_p$, $G = \sum_{j=0}^{a_p(d)-1} p^j$, and $a = ap p d$.
  set M : ℕ := p * primeProdBelow p
  set G : ℕ := geomSumAp p d
  set a := ap p d
  have hLm : L / M ≥ G := by
    refine Nat.le_div_iff_mul_le ( Nat.mul_pos hp.pos ( Nat.pos_of_ne_zero ?_ ) ) |>.2 ?_;
    · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by unfold primeProdBelow; exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by unfold primorial; exact Finset.prod_ne_zero_iff.mpr fun q hq => Nat.Prime.ne_zero <| Finset.mem_filter.mp hq |>.2;
    · convert hL using 1;
      exact mul_comm _ _
  generalize_proofs at *;
  -- The usable elements are exactly those $n$ with $P_p | n$ and $p \nmid n$. The count is $\ge (p-1) \cdot G = (p-1) \cdot (1+p+\cdots+p^{a-1}) = p^a - 1$.
  have h_count : (Intv b L).filter (fun n => (primeProdBelow p : ℤ) ∣ n ∧ ¬((p : ℤ) ∣ n)) ⊇ Finset.biUnion (Finset.Ico 1 p) (fun r => (Intv b L).filter (fun n => (M : ℤ) ∣ (n - r * primeProdBelow p))) := by
    simp +zetaDelta at *;
    intro x hx₁ hx₂ n hn; simp_all +decide ;
    constructor;
    · obtain ⟨ k, hk ⟩ := hn.2; exact ⟨ k * p + x, by linarith ⟩ ;
    · intro h; have := dvd_sub h ( dvd_of_mul_right_dvd hn.2 ) ; simp_all +decide ;
      -- Since $p$ is prime and $p \mid x \cdot \text{primeProdBelow } p$, it must divide either $x$ or $\text{primeProdBelow } p$.
      have h_div : (p : ℤ) ∣ primeProdBelow p := by
        exact Or.resolve_left ( Int.Prime.dvd_mul' hp this ) ( by norm_cast; exact Nat.not_dvd_of_pos_of_lt hx₁ hx₂ );
      norm_cast at *; simp_all +decide [ primeProdBelow ] ;
      rcases p with ( _ | _ | p ) <;> simp_all +decide [ primorial ];
      simp_all +decide [ Nat.Prime.dvd_iff_not_coprime hp, Nat.coprime_prod_right_iff ];
      exact h_div.elim fun x hx => hx.2.2 <| hp.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt hx.2.1.pos <| by linarith;
  -- Each of the $p-1$ residue classes contributes at least $G$ elements.
  have h_card : (Finset.biUnion (Finset.Ico 1 p) (fun r => (Intv b L).filter (fun n => (M : ℤ) ∣ (n - r * primeProdBelow p)))).card ≥ (p - 1) * G := by
    have h_card : ∀ r ∈ Finset.Ico 1 p, ((Intv b L).filter (fun n => (M : ℤ) ∣ (n - r * primeProdBelow p))).card ≥ G := by
      intros r hr
      have h_card : ((Intv b L).filter (fun n => (M : ℤ) ∣ (n - r * primeProdBelow p))).card ≥ L / M := by
        apply residue_count_in_Intv M L (by
        exact Nat.mul_pos hp.pos ( Nat.pos_of_ne_zero ( by exact _root_.ne_of_gt ( Nat.pos_of_ne_zero ( by exact Nat.ne_of_gt ( primorial_pos _ ) ) ) ) )) b (r * primeProdBelow p)
      exact le_trans hLm h_card;
    rw [ Finset.card_biUnion ];
    · exact le_trans ( by norm_num [ Nat.card_Ico ] ) ( Finset.sum_le_sum h_card );
    · intros r hr s hs hrs; simp_all +decide [ Finset.disjoint_left ] ;
      intro n hn hn' hn''; have := dvd_sub hn' hn''; simp_all +decide ;
      -- Since $M = p \cdot P_p$, we have $p \cdot P_p \mid (s - r) \cdot P_p$, which simplifies to $p \mid (s - r)$.
      have h_div : (p : ℤ) ∣ (s - r) := by
        simp +zetaDelta at *;
        obtain ⟨ k, hk ⟩ := this; exact ⟨ k, by nlinarith [ show ( primeProdBelow p : ℤ ) > 0 from mod_cast Nat.pos_of_ne_zero ( by exact _root_.ne_of_gt <| Nat.pos_of_ne_zero <| by exact _root_.ne_of_gt <| Nat.pos_of_ne_zero <| by exact _root_.ne_of_gt <| primorial_pos _ ) ] ⟩ ;
      exact hrs ( by obtain ⟨ k, hk ⟩ := h_div; nlinarith [ show k = 0 by nlinarith ] );
  -- Since $(p-1) \cdot G = p^a - 1$, we conclude that the number of usable elements is at least $p^a - 1$.
  have h_final : (p - 1) * G = p ^ a - 1 := by
    zify [ G ];
    norm_num [ hp.pos, geomSumAp ];
    rw [ mul_comm, geom_sum_mul ];
  exact h_final ▸ h_card.trans ( Finset.card_mono h_count )

/-
Vanishing at earlier prime powers: if q < p are primes ≤ d and n ∈ U_p(J),
    then n^d ≡ 0 (mod q^{a_q(d)}).
-/
theorem vanishing_at_earlier_primes (p q d : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hqp : q < p) (hpd : p ≤ d) (hd : 1 ≤ d)
    (J : Finset ℤ) (n : ℤ) (hn : n ∈ usableSet p J) :
    (q ^ ap q d : ℤ) ∣ n ^ d := by
  -- Since $q$ divides $primeProdBelow p$ and $n \in usableSet p J$, it follows that $q \mid n$.
  have hq_div_n : (q : ℤ) ∣ n := by
    refine dvd_trans ?_ ( Finset.mem_filter.mp hn |>.2.1 );
    unfold primeProdBelow;
    rcases p with ( _ | _ | p ) <;> simp_all +decide [ primorial ];
    exact_mod_cast Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), hq ⟩ );
  exact dvd_trans ( pow_dvd_pow_of_dvd hq_div_n _ ) ( pow_dvd_pow _ ( ap_le_d q d hq hd ) )

/-
Units at the current prime power: if n ∈ U_p(J), then n^d is a unit mod p^{a_p(d)}.
-/
theorem units_at_current_prime (p d : ℕ) (hp : Nat.Prime p) (J : Finset ℤ) (n : ℤ) (hn : n ∈ usableSet p J) :
    IsUnit ((↑(n ^ d) : ZMod (p ^ ap p d))) := by
  unfold usableSet at hn; simp_all +decide ;
  -- Since $p$ does not divide $n$, $n$ is coprime to $p$, hence $n$ is a unit modulo $p^{a_p(d)}$.
  have h_unit : IsUnit (n : ZMod (p ^ ap p d)) := by
    have h_unit : Int.gcd n (p ^ ap p d) = 1 := by
      exact mod_cast Nat.Coprime.pow_right _ <| Nat.Coprime.symm <| hp.coprime_iff_not_dvd.mpr fun h => hn.2.2 <| Int.natCast_dvd.mpr h;
    have h_unit : ∃ x : ℤ, n * x ≡ 1 [ZMOD p ^ ap p d] := by
      have := Int.gcd_eq_gcd_ab n ( p ^ ap p d );
      exact ⟨ Int.gcdA n ( p ^ ap p d ), Int.modEq_iff_dvd.mpr ⟨ Int.gcdB n ( p ^ ap p d ), by linarith ⟩ ⟩;
    obtain ⟨ x, hx ⟩ := h_unit;
    exact isUnit_iff_exists_inv.mpr ⟨ x, by erw [ ← ZMod.intCast_eq_intCast_iff ] at *; aesop ⟩;
  exact h_unit.pow _

/-
Disjointness of usable sets for distinct primes.
-/
theorem usableSet_disjoint (p q : ℕ) (hp : Nat.Prime p) (hpq : p < q)
    (J : Finset ℤ) : Disjoint (usableSet p J) (usableSet q J) := by
  rw [ Finset.disjoint_left ];
  intro n hn hpq; simp_all +decide [ usableSet ] ;
  refine' hn.2.2 ( dvd_trans _ hpq.1 );
  refine' mod_cast Nat.dvd_trans _ ( Nat.dvd_of_mod_eq_zero _ );
  rotate_left;
  exact primorial ( q - 1 );
  · exact Nat.mod_eq_zero_of_dvd <| dvd_rfl;
  · refine' Finset.dvd_prod_of_mem _ _;
    exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by omega ), hp ⟩

/-
Invariant subsets lemma: if A ⊆ ZMod m is nonempty with A + {u} = A and u is a
unit, then A = univ.
-/
theorem invariant_subset_is_full (m : ℕ) [NeZero m] (u : ZMod m)
    (hu : IsUnit u) (A : Finset (ZMod m)) (hA : A.Nonempty)
    (hInv : ∀ a ∈ A, a + u ∈ A) : A = Finset.univ := by
  -- Since $u$ is a unit, there exists some $k$ such that $ku \equiv 1 \pmod{m}$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k * u = 1 := by
    obtain ⟨ k, rfl ⟩ := hu;
    exact ⟨ k.val⁻¹.val, by simp +decide ⟩;
  -- Since $A$ is closed under addition by $u$, we have $a + ku \in A$ for any $a \in A$ and $k \in \mathbb{N}$.
  have h_closed : ∀ a ∈ A, ∀ k : ℕ, a + k • u ∈ A := by
    intro a ha k; induction k <;> simp_all +decide [ add_mul, ← add_assoc ] ;
  refine' Finset.eq_univ_of_forall _;
  intro x; obtain ⟨ a, ha ⟩ := hA; specialize h_closed a ha ( ( x - a ) |> ZMod.val |> fun z => z * k ) ; simp_all +decide [ ← mul_assoc, mul_comm ] ;
  convert h_closed using 1 ; linear_combination' -hk * ( x - a )

/-
Subset sums of m-1 units modulo m cover all residues.
-/
set_option maxHeartbeats 800000 in
theorem subset_sums_of_units_cover (m : ℕ) [NeZero m] (hm : 2 ≤ m)
    (u : Fin (m - 1) → ZMod m)
    (hu : ∀ i, IsUnit (u i)) :
    ∀ r : ZMod m, ∃ S : Finset (Fin (m - 1)),
      ∑ i ∈ S, u i = r := by
  -- By induction on $i$, we show that for each $0 \leq i \leq m-2$, the set $\{ \sum_{j \in S} u(j) : S \subseteq \{0,...,i\}\}$ has size at least $i+2$.
  have h_ind : ∀ i : Fin (m - 1), (Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i) (Finset.powerset (Finset.Iic i))).card ≥ i.val + 2 := by
    intro i
    induction' i with i ih;
    induction' i with i ih;
    · refine' Finset.one_lt_card.mpr ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_powerset.mpr <| Finset.empty_subset _ ), _, Finset.mem_image_of_mem _ ( Finset.mem_powerset.mpr <| Finset.Subset.refl _ ), _ ⟩ ; simp +decide;
      rw [ eq_comm ] ; intro H; have := hu ⟨ 0, ih ⟩ ; simp_all +decide ;
      rw [ show ( Iic ⟨ 0, ih ⟩ : Finset ( Fin ( m - 1 ) ) ) = { ⟨ 0, ih ⟩ } by ext ⟨ i, hi ⟩ ; aesop ] at H ; simp_all +decide;
      have := hu ⟨ 0, ih ⟩ ; simp_all +decide [ isUnit_iff_exists_inv ] ;
      rcases m with ( _ | _ | m ) <;> cases this ; contradiction;
    · -- Consider the set $\{ \sum_{j \in S} u(j) : S \subseteq \{0,...,i+1\}\}$.
      -- It can be written as $\{ \sum_{j \in S} u(j) : S \subseteq \{0,...,i\}\} \cup \{ \sum_{j \in S} u(j) + u(i+1) : S \subseteq \{0,...,i\}\}$.
      have h_union : Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i) (Finset.powerset (Finset.Iic ⟨i + 1, ih⟩)) = Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i) (Finset.powerset (Finset.Iic ⟨i, by linarith⟩)) ∪ Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i + u ⟨i + 1, ih⟩) (Finset.powerset (Finset.Iic ⟨i, by linarith⟩)) := by
        ext; simp [Finset.mem_union, Finset.mem_image];
        constructor;
        · rintro ⟨ S, hS₁, hS₂ ⟩;
          by_cases h : ⟨ i + 1, ih ⟩ ∈ S;
          · refine' Or.inr ⟨ S.erase ⟨ i + 1, ih ⟩, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
            exact fun x hx₁ hx₂ => Nat.le_of_lt_succ <| lt_of_le_of_ne ( hS₁ hx₂ ) <| by simpa [ Fin.ext_iff ] using hx₁;
          · grind;
        · rintro ( ⟨ S, hS, rfl ⟩ | ⟨ S, hS, rfl ⟩ );
          · exact ⟨ S, Finset.Subset.trans hS <| Finset.Iic_subset_Iic.mpr <| Nat.le_succ _, rfl ⟩;
          · refine' ⟨ Insert.insert ⟨ i + 1, ih ⟩ S, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
            · exact fun x hx => le_trans ( hS hx ) ( Nat.le_succ _ );
            · rw [ Finset.sum_insert ];
              · ring;
              · exact fun h => not_lt_of_ge ( hS h ) ( Nat.lt_succ_self _ );
      by_cases h : Finset.image ( fun S : Finset ( Fin ( m - 1 ) ) => ∑ i ∈ S, u i + u ⟨ i + 1, ih ⟩ ) ( Finset.powerset ( Finset.Iic ⟨ i, by linarith ⟩ ) ) ⊆ Finset.image ( fun S : Finset ( Fin ( m - 1 ) ) => ∑ i ∈ S, u i ) ( Finset.powerset ( Finset.Iic ⟨ i, by linarith ⟩ ) ) <;> simp_all +decide [ Finset.subset_iff ];
      · have h_inv : ∀ a ∈ Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i) (Finset.powerset (Finset.Iic ⟨i, by linarith⟩)), a + u ⟨i + 1, by linarith⟩ ∈ Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i) (Finset.powerset (Finset.Iic ⟨i, by linarith⟩)) := by
          simp +zetaDelta at *;
          exact fun a ha => by obtain ⟨ b, hb₁, hb₂ ⟩ := h a fun x hx => Finset.mem_Iic.mp ( ha hx ) ; exact ⟨ b, fun x hx => Finset.mem_Iic.mpr ( hb₁ hx ), hb₂ ⟩ ;
        have h_inv : Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i) (Finset.powerset (Finset.Iic ⟨i, by linarith⟩)) = Finset.univ := by
          apply_rules [ invariant_subset_is_full ];
          exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_powerset_self _ ) ⟩;
        simp_all +decide [ Finset.ext_iff ];
        rw [ show ( Finset.image ( fun S : Finset ( Fin ( m - 1 ) ) => ∑ i ∈ S, u i ) ( Finset.powerset ( Finset.Iic ⟨ i, by linarith ⟩ ) ) ∪ Finset.image ( fun S : Finset ( Fin ( m - 1 ) ) => ∑ i ∈ S, u i + u ⟨ i + 1, by linarith ⟩ ) ( Finset.powerset ( Finset.Iic ⟨ i, by linarith ⟩ ) ) ) = Finset.univ from Finset.eq_univ_of_forall fun x => by obtain ⟨ S, hS₁, hS₂ ⟩ := h_inv x; aesop ] ; simp +decide [ Finset.card_univ ];
        omega;
      · have h_card_union : Finset.card (Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i) (Finset.powerset (Finset.Iic ⟨i, by linarith⟩)) ∪ Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i + u ⟨i + 1, by linarith⟩) (Finset.powerset (Finset.Iic ⟨i, by linarith⟩))) ≥ Finset.card (Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i) (Finset.powerset (Finset.Iic ⟨i, by linarith⟩))) + 1 := by
          refine' Finset.card_lt_card _;
          simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
          exact ⟨ _, Or.inr ⟨ h.choose, h.choose_spec.1, rfl ⟩, h.choose_spec.2 ⟩;
        linarith [ ih ( Nat.lt_of_succ_lt ‹_› ) ];
  -- Since $A_{m-2}$ has size at least $m$, it must contain all elements of $ZMod m$.
  have h_all : Finset.image (fun S : Finset (Fin (m - 1)) => ∑ i ∈ S, u i) (Finset.powerset (Finset.univ : Finset (Fin (m - 1)))) = Finset.univ := by
    refine' Finset.eq_of_subset_of_card_le ( Finset.subset_univ _ ) _;
    rcases m with ( _ | _ | m ) <;> simp_all +decide [ Finset.card_univ ];
    exact lt_of_lt_of_le ( by norm_num ) ( h_ind ⟨ m, Nat.lt_succ_self _ ⟩ |> le_trans <| Finset.card_mono <| Finset.image_subset_image <| Finset.powerset_mono.mpr <| Finset.subset_univ _ );
  exact fun r => by simpa using Finset.ext_iff.mp h_all r;

/-
Completeness from many units: if |A| ≥ m-1 and all x^e are units mod m,
    then A is (e,m)-complete.
-/
theorem completeness_from_many_units (A : Finset ℤ) (e m : ℕ) [NeZero m] (hm : 2 ≤ m)
    (hcard : m - 1 ≤ A.card)
    (hunits : ∀ x ∈ A, IsUnit ((↑(x ^ e) : ZMod m))) :
    IsEMComplete A e m := by
  -- Choose m-1 distinct elements x_1,...,x_{m-1} from A (possible since |A| ≥ m-1).
  obtain ⟨x, hx⟩ : ∃ x : Fin (m - 1) → ℤ, (∀ i, x i ∈ A) ∧ Function.Injective x := by
    exact ⟨ fun i => A.orderEmbOfFin rfl ⟨ i, by linarith [ Fin.is_lt i ] ⟩, fun i => by simp +decide, fun i j hij => by simpa [ Fin.ext_iff ] using hij ⟩;
  intro r
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (m - 1)), ∑ i ∈ S, (x i ^ e : ZMod m) = r := by
    -- By subset_sums_of_units_cover, for every r : ZMod m, there exists S ⊆ {0,...,m-2} with ∑_{i ∈ S} u_i = r.
    have := subset_sums_of_units_cover m hm (fun i => (x i : ZMod m) ^ e) (fun i => by
      simpa using hunits ( x i ) ( hx.1 i )) r;
    aesop;
  use Finset.image x S;
  simp_all +decide [ Finset.subset_iff, hx.2.eq_iff ]

/-
For prime p ≤ d with d ≥ 1, p^{a_p(d)} ≥ 2.
-/
theorem ppow_ap_ge_two (p d : ℕ) (hp : Nat.Prime p) (hpd : p ≤ d) :
    2 ≤ p ^ ap p d := by
  exact le_trans hp.two_le ( Nat.le_self_pow ( by linarith [ ap_pos_of_prime_le p d hp hpd ] ) _ )

/-
Completeness for one prime: U_p(Intv(b,L)) is (d, p^{a_p(d)})-complete
    when L ≥ L_p(d).
-/
theorem completeness_for_one_prime (p d : ℕ) (hp : Nat.Prime p) (hpd : p ≤ d)
    (b : ℤ) (L : ℕ) (hL : Lp p d ≤ L)
    (hne : NeZero (p ^ ap p d) := ⟨by exact Nat.ne_of_gt (Nat.one_le_pow _ _ hp.pos)⟩) :
    @IsEMComplete (usableSet p (Intv b L)) d (p ^ ap p d) hne := by
  convert completeness_from_many_units _ _ _ _ _;
  rotate_left;
  exact usableSet p ( Intv b L );
  exact d;
  exact p ^ ap p d;
  grind +splitImp;
  · exact ppow_ap_ge_two p d hp hpd;
  · exact count_usable_elements p d hp hpd b L hL;
  · exact ⟨ fun h => fun _ => h, fun h => h fun x hx => units_at_current_prime p d hp _ x hx ⟩

/-
Triangular Chinese-remainder construction.
-/
set_option maxHeartbeats 1600000 in
theorem triangular_crt {t : ℕ} {e : ℕ}
    (m : Fin t → ℕ) (hm_ne : ∀ i, NeZero (m i))
    (A : Fin t → Finset ℤ)
    (hcoprime : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hcomplete : ∀ i, @IsEMComplete (A i) e (m i) (hm_ne i))
    (hvanish : ∀ i j : Fin t, j < i → ∀ x ∈ A i,
      (m j : ℤ) ∣ x ^ e)
    (hprod_ne : NeZero (∏ i, m i)) :
    @IsEMComplete (Finset.univ.biUnion A) e (∏ i, m i) hprod_ne := by
  -- We prove this by induction on $t$.
  induction' t with t ih;
  · simp +decide [ IsEMComplete ];
    exact fun r => by rcases r with ⟨ _ | _ | r ⟩ <;> trivial;
  · simp +decide only [Fin.prod_univ_castSucc] at hprod_ne ⊢;
    have := ih ( fun i => m i.castSucc ) ( fun i => hm_ne _ ) ( fun i => A i.castSucc ) ( fun i j hij => hcoprime _ _ <| by simpa [ Fin.ext_iff ] using hij ) ( fun i j hij => hdisjoint _ _ <| by simpa [ Fin.ext_iff ] using hij ) ( fun i => hcomplete _ ) ( fun i j hij x hx => hvanish _ _ ( by simpa [ Fin.ext_iff ] using hij ) _ hx ) ?_;
    swap;
    exact ⟨ by intro h; simpa [ h ] using hprod_ne.1 ⟩;
    intro r;
    -- By the Chinese Remainder Theorem, we can find such a subset $B$.
    obtain ⟨B₁, hB₁⟩ : ∃ B₁ : Finset ℤ, B₁ ⊆ Finset.biUnion Finset.univ (fun i => A (Fin.castSucc i)) ∧ (∑ x ∈ B₁, x ^ e) ≡ r.val [ZMOD ∏ i : Fin t, m (Fin.castSucc i)] := by
      have := this ( r.val : ZMod ( ∏ i : Fin t, m ( Fin.castSucc i ) ) );
      obtain ⟨ B, hB₁, hB₂ ⟩ := this;
      use B;
      norm_cast at *;
      erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
    obtain ⟨B₂, hB₂⟩ : ∃ B₂ : Finset ℤ, B₂ ⊆ A (Fin.last t) ∧ (∑ x ∈ B₂, x ^ e) ≡ r.val - ∑ x ∈ B₁, x ^ e [ZMOD m (Fin.last t)] := by
      have := hcomplete ( Fin.last t );
      have := this ( r.val - ∑ x ∈ B₁, x ^ e );
      obtain ⟨ B₂, hB₂₁, hB₂₂ ⟩ := this; use B₂; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
    refine' ⟨ B₁ ∪ B₂, _, _ ⟩;
    · simp +decide [ Finset.subset_iff ] at *;
      rintro x ( hx | hx ) <;> [ exact Exists.elim ( hB₁.1 hx ) fun i hi => ⟨ Fin.castSucc i, hi ⟩ ; exact ⟨ Fin.last t, hB₂.1 hx ⟩ ];
    · have h_crt : (∑ x ∈ B₁ ∪ B₂, x ^ e) ≡ r.val [ZMOD (∏ i : Fin t, m (Fin.castSucc i)) * m (Fin.last t)] := by
        rw [ Int.modEq_iff_dvd ] at *;
        convert Int.coe_lcm_dvd ( show ( ∏ i : Fin t, ( m ( Fin.castSucc i ) : ℤ ) ) ∣ ↑r.val - ∑ x ∈ B₁ ∪ B₂, x ^ e from ?_ ) ( show ( m ( Fin.last t ) : ℤ ) ∣ ↑r.val - ∑ x ∈ B₁ ∪ B₂, x ^ e from ?_ ) using 1;
        · norm_cast;
          exact Eq.symm ( Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_left fun i _ => hcoprime _ _ <| ne_of_lt <| Fin.castSucc_lt_last i );
        · rw [ Finset.sum_union ];
          · convert dvd_sub hB₁.2 ( show ( ∏ i : Fin t, ( m ( Fin.castSucc i ) : ℤ ) ) ∣ ∑ x ∈ B₂, x ^ e from ?_ ) using 1 ; ring;
            exact Finset.dvd_sum fun x hx => Finset.prod_dvd_of_coprime ( fun i _ j _ hij => by simpa [ Fin.ext_iff ] using hcoprime _ _ <| by simpa [ Fin.ext_iff ] using hij ) fun i _ => hvanish _ _ ( Fin.castSucc_lt_last i ) _ <| hB₂.1 hx;
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp ( hdisjoint _ _ <| ne_of_lt <| Fin.castSucc_lt_last <| Classical.choose <| Finset.mem_biUnion.mp <| hB₁.1 hx₁ ) ( Classical.choose_spec ( Finset.mem_biUnion.mp <| hB₁.1 hx₁ ) |>.2 ) ( hB₂.1 hx₂ );
        · convert hB₂.2 using 1;
          rw [ Finset.sum_union ];
          · ring;
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp ( hdisjoint _ _ <| ne_of_lt <| Fin.castSucc_lt_last <| Classical.choose <| Finset.mem_biUnion.mp <| hB₁.1 hx₁ ) ( Classical.choose_spec ( Finset.mem_biUnion.mp <| hB₁.1 hx₁ ) |>.2 ) ( hB₂.1 hx₂ );
      erw [ ← ZMod.intCast_eq_intCast_iff ] at * ; aesop

instance factorial_neZero (d : ℕ) : NeZero d.factorial :=
  ⟨Nat.factorial_ne_zero d⟩

/-
For d ≥ 2, Intv(b, Rad(d)) is (d, d!)-complete.
-/
theorem exact_covering (d : ℕ) (hd : 2 ≤ d) (b : ℤ) :
    IsEMComplete (Intv b (Rad d)) d d.factorial := by
  -- Set S = (Finset.Icc 2 d).filter Nat.Prime, let t = S.card
  set S := (Finset.Icc 2 d).filter Nat.Prime
  set t := S.card with ht_def;
  -- Use S.orderIsoOfFin to get an order-preserving bijection Fin t → S
  obtain ⟨f, hf⟩ : ∃ f : Fin t ≃o S, True := by
    exact ⟨ Finset.orderIsoOfFin _ <| by aesop, trivial ⟩;
  -- Define m i = (S.sort (·≤·)).get i |> fun p => p ^ ap p d
  set m : Fin t → ℕ := fun i => (f i).val ^ ap (f i).val d with hm_def;
  -- Define A i = usableSet(f i, Intv(b, Rad(d)))
  set A : Fin t → Finset ℤ := fun i => usableSet (f i).val (Intv b (Rad d)) with hA_defA_def;
  -- By completeness_for_one_prime, A i is (d, m i)-complete.
  have h_complete : ∀ i, @IsEMComplete (A i) d (m i) (by
  exact ⟨ pow_ne_zero _ <| Nat.Prime.ne_zero <| Finset.mem_filter.mp ( f i |>.2 ) |>.2 ⟩) := by
    all_goals generalize_proofs at *;
    intro i
    apply completeness_for_one_prime (f i).val d (by
    exact Finset.mem_filter.mp ( f i |>.2 ) |>.2) (by
    exact Finset.mem_Icc.mp ( Finset.mem_filter.mp ( f i |>.2 ) |>.1 ) |>.2) b (Rad d) (by
    unfold Rad;
    split_ifs <;> norm_num at *;
    · linarith;
    · exact ⟨ _, ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp ( f i |>.2 ) |>.1 ), Finset.mem_filter.mp ( f i |>.2 ) |>.2 ⟩, le_rfl ⟩) (by
    grind +extAll)
  generalize_proofs at *;
  -- The sets A i are pairwise disjoint by usableSet_disjoint.
  have h_disjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij; cases lt_or_gt_of_ne hij <;> [ exact usableSet_disjoint _ _ ( f i |>.2 |> Finset.mem_filter.mp |>.2 )  ( by aesop ) _ ; exact Disjoint.symm ( usableSet_disjoint _ _ ( f j |>.2 |> Finset.mem_filter.mp |>.2 ) ( by aesop ) _ ) ] ;
  -- The vanishing condition follows from vanishing_at_earlier_primes.
  have h_vanish : ∀ i j : Fin t, j < i → ∀ x ∈ A i, (m j : ℤ) ∣ x ^ d := by
    intros i j hij x hx
    have h_prime : (f j).val < (f i).val := by
      exact f.lt_iff_lt.mpr hij;
    have := vanishing_at_earlier_primes ( f i |>.1 ) ( f j |>.1 ) d ( f i |>.2 |> Finset.mem_filter.mp |>.2 ) ( f j |>.2 |> Finset.mem_filter.mp |>.2 ) h_prime ( f i |>.2 |> Finset.mem_filter.mp |>.1 |> Finset.mem_Icc.mp |>.2 ) ( by linarith ) ( Intv b ( Rad d ) ) x hx; aesop;
  -- By factorial_eq_prod_prime_pow, ∏ m i = d!.
  have h_prod : ∏ i, m i = d.factorial := by
    have h_prod : ∏ p ∈ S, p ^ ap p d = d.factorial := by
      have h_prod : ∏ p ∈ Nat.primeFactors d.factorial, p ^ padicValNat p d.factorial = d.factorial := by
        conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self ( Nat.factorial_ne_zero d ) ] ;
        exact Finset.prod_congr rfl fun p hp => by rw [ Nat.factorization_def ] ; aesop;
      convert h_prod using 2;
      ext; simp [S];
      exact ⟨ fun h => ⟨ h.2, Nat.dvd_factorial ( Nat.Prime.pos h.2 ) h.1.2, Nat.factorial_ne_zero _ ⟩, fun h => ⟨ ⟨ Nat.Prime.two_le h.1, Nat.le_of_not_lt fun h' => absurd ( Nat.dvd_trans ( Nat.dvd_refl _ ) h.2.1 ) ( by rw [ Nat.Prime.dvd_factorial h.1 ] ; linarith ) ⟩, h.1 ⟩ ⟩;
    rw [ ← h_prod, ← Finset.prod_coe_sort ];
    refine' Finset.prod_bij ( fun i _ => f i ) _ _ _ _ <;> simp +decide;
    · exact fun x hx => ⟨ f.symm ⟨ x, hx ⟩, by simp +decide ⟩;
    · lia;
  -- By triangular_crt, ⋃ A i is (d, d!)-complete.
  have h_union_complete : @IsEMComplete (Finset.univ.biUnion A) d (d.factorial) (by
  assumption) := by
    convert triangular_crt m _ A _ _ _ _ _;
    all_goals try assumption;
    · exact h_prod.symm;
    · intro i j hij; have := Nat.coprime_primes ( show Nat.Prime ( f i : ℕ ) from by exact Finset.mem_filter.mp ( f i |>.2 ) |>.2 ) ( show Nat.Prime ( f j : ℕ ) from by exact Finset.mem_filter.mp ( f j |>.2 ) |>.2 ) ; simp_all +decide ;
      exact this.pow _ _;
    · exact h_prod.symm ▸ by assumption;
  generalize_proofs at *;
  refine' fun r => _;
  obtain ⟨ B, hB₁, hB₂ ⟩ := h_union_complete r;
  refine' ⟨ B, _, hB₂ ⟩;
  exact fun x hx => by have := hB₁ hx; obtain ⟨ i, _, hi ⟩ := Finset.mem_biUnion.mp this; exact Finset.mem_filter.mp hi |>.1;

/-
Rad(d) ≤ 4^d for d ≥ 1.
-/
theorem Rad_le_4_pow (d : ℕ) (hd : 1 ≤ d) : Rad d ≤ 4 ^ d := by
  -- We are going to prove that $L_p(d) < 4^d$ for every prime $p \le d$.
  have hp_bound (p d : ℕ) (hp : Nat.Prime p) (hpd : p ≤ d) : Lp p d ≤ 4 ^ d := by
    by_cases h : p = d;
    · -- If p = d, then a_p(d) = 1, G = 1, Lp = p * primeProdBelow p = primorial p ≤ 4^p by primorial_le_4_pow.
      have hLp_eq_primorial : Lp p d = primorial p := by
        subst h;
        -- By definition of $ap$, we know that $ap p p = 1$.
        have hap_pp : ap p p = 1 := by
          unfold ap;
          haveI := Fact.mk hp; rw [ padicValNat_factorial ] ;
          any_goals exact Nat.lt_succ_self _;
          rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.log_eq_one_iff.mpr ];
        -- By definition of $Lp$, we know that $Lp p p = p * primeProdBelow p * geomSumAp p p$.
        simp [Lp, hap_pp, primeProdBelow, geomSumAp];
        rcases p with ( _ | _ | p ) <;> simp_all +decide [ primorial ];
        simp +decide [ Finset.prod_filter, Finset.prod_range_succ, hp ];
        grind;
      exact hLp_eq_primorial.symm ▸ h.symm ▸ primorial_le_4_pow _;
    · -- Since p ≠ d, we have p < d. We use the upper bound Lp p d ≤ 2 * primeProdBelow p * p ^ ap p d.
      have h_bound : Lp p d ≤ 2 * primeProdBelow p * p ^ ap p d := by
        -- Since $p \neq d$, we have $p < d$. We use the upper bound $p \cdot G_p(d) \leq 2 \cdot p^{a_p(d)}$.
        have h_bound : p * geomSumAp p d ≤ 2 * p ^ ap p d := by
          have hpg_le_2pa : p * (∑ j ∈ Finset.range (ap p d), p ^ j) ≤ 2 * p ^ ap p d := by
            nlinarith [ hp.two_le, pow_pos hp.pos ( ap p d ), geom_sum_mul_neg ( p : ℤ ) ( ap p d ) ];
          exact hpg_le_2pa;
        convert Nat.mul_le_mul_right ( primeProdBelow p ) h_bound using 1 ; ring_nf;
        · exact mul_right_comm _ _ _;
        · ring;
      -- We use the upper bound primeProdBelow p * p ^ ap p d ≤ 4^p * 2^{d-p}.
      have h_bound2 : primeProdBelow p * p ^ ap p d ≤ 4 ^ p * 2 ^ (d - p) := by
        have h_bound2 : primeProdBelow p * p ^ ap p d ≤ primorial p * 2 ^ (d - p) := by
          have h_bound2 : p ^ ap p d ≤ p * 2 ^ (d - p) := by
            have h_bound2 : p ^ (ap p d - 1) ≤ 2 ^ (d - p) := by
              apply power_bound_from_valuation p d hp hpd (by linarith [hp.two_le]);
            convert Nat.mul_le_mul_left p h_bound2 using 1;
            rw [ ← _root_.pow_succ', Nat.sub_add_cancel ( ap_pos_of_prime_le p d hp hpd ) ];
          convert Nat.mul_le_mul_left ( primeProdBelow p ) h_bound2 using 1 ; ring_nf!;
          rcases p with ( _ | _ | p ) <;> simp_all +decide [ primorial, primeProdBelow ];
          simp +decide [ Finset.prod_filter, Finset.prod_range_succ, hp ];
        exact h_bound2.trans ( Nat.mul_le_mul_right _ ( primorial_le_4_pow p ) );
      rw [ show 4 ^ d = 4 ^ p * 4 ^ ( d - p ) by rw [ ← pow_add, Nat.add_sub_of_le hpd ] ];
      rw [ show 4 ^ ( d - p ) = 2 ^ ( d - p ) * 2 ^ ( d - p ) by rw [ ← mul_pow ] ; norm_num ] ; nlinarith [ pow_pos ( show 0 < 4 by norm_num ) p, pow_pos ( show 0 < 2 by norm_num ) ( d - p ), show 2 ^ ( d - p ) ≥ 2 by exact le_self_pow₀ ( by norm_num ) ( Nat.sub_ne_zero_of_lt ( lt_of_le_of_ne hpd h ) ) ];
  unfold Rad;
  split_ifs <;> simp_all +decide [ Finset.sup'_le_iff ];
  interval_cases d ; trivial

/-- IsEMComplete is monotone in the set. -/
theorem IsEMComplete_mono {A B : Finset ℤ} {e m : ℕ} [NeZero m]
    (h : A ⊆ B) (hA : IsEMComplete A e m) : IsEMComplete B e m := by
  intro r; obtain ⟨C, hC, hsum⟩ := hA r
  exact ⟨C, hC.trans h, hsum⟩

/-
Every interval of 4^d consecutive integers is (d, d!)-complete for d ≥ 1.
-/
theorem interval_4d_complete (d : ℕ) (hd : 1 ≤ d) (b : ℤ) :
    IsEMComplete (Intv b (4 ^ d)) d d.factorial := by
  by_cases h : 2 ≤ d;
  · exact IsEMComplete_mono ( Intv_subset_of_le _ _ _ ( Rad_le_4_pow _ ( by linarith ) ) ) ( exact_covering _ h _ );
  · interval_cases d ; simp_all +decide [ IsEMComplete ];
    simp +decide [ ZMod, Fin.eq_zero ];
    exact ⟨ ∅, Finset.empty_subset _ ⟩

theorem monomial_tau_eq (d G : ℕ) (hd : 1 ≤ d) :
    explicitTailParam (monomialPoly d) G = max (6 * d * G) 4 := by
  unfold explicitTailParam;
  unfold monomialPoly Hzero; norm_num;
  rw [ Finset.sum_eq_zero ] <;> aesop

theorem monomial_tau_eq' (d G : ℕ) (hd : 2 ≤ d) (hG : 1 ≤ G) :
    explicitTailParam (monomialPoly d) G = 6 * d * G := by
  rw [monomial_tau_eq]
  · exact max_eq_left ( by nlinarith )
  · linarith

theorem monomial_K_eq (d : ℕ) (hd : 2 ≤ d) :
    (monomialPoly d).eval (explicitTailParam (monomialPoly d) 1 : ℤ) = (6 * d : ℤ) ^ d := by
  simp [monomialPoly]
  have h_explicitTailParam : explicitTailParam (Polynomial.X ^ d) 1 = 6 * d := by
    convert monomial_tau_eq' d 1 hd ( by linarith ) using 1; ring
  rw [h_explicitTailParam]; norm_cast

/-
6d ≤ 2^d for d ≥ 6
-/
lemma six_d_pow_le (d : ℕ) (hd : 6 ≤ d) : (6 * d) ^ d ≤ 2 ^ (d ^ 2 + 3 * d) := by
  rw [ show 2 ^ ( d ^ 2 + 3 * d ) = ( 2 ^ ( d + 3 ) ) ^ d by rw [ ← pow_mul ] ; ring ];
  exact Nat.pow_le_pow_left ( by rw [ pow_add ] ; norm_num; nlinarith [ show 2 ^ d ≥ d + 1 by exact Nat.recOn d ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ ihn, Nat.one_le_pow n 2 zero_lt_two ] ] ) d

/-
M ≤ 2^(3d²+2d) follows from M ≤ 4^d * (8^d)^d
-/
lemma M_bound_exponent (d : ℕ) :
    (4 : ℤ) ^ d * ((8 : ℤ) ^ d) ^ d = 2 ^ (3 * d ^ 2 + 2 * d) := by
  ring_nf;
  norm_num [ pow_mul' ]

/-
K = (6d)^d for the monomial polynomial
-/
lemma monomial_K_value (d : ℕ) (hd : 2 ≤ d) (K : ℕ)
    (hK_eq : (↑K : ℤ) = (monomialPoly d).eval (↑(explicitTailParam (monomialPoly d) 1) : ℤ)) :
    K = (6 * d) ^ d := by
  exact_mod_cast hK_eq.trans ( monomial_K_eq d hd )

/-
Conversion lemmas
-/
noncomputable def smallEmaxDatum (d : ℕ) :
    ResidueDatum (monomialPoly d) d.factorial where
  E := Finset.Icc 1 (4 ^ d)

theorem smallEmaxDatum_eMax (d : ℕ) (hd : 1 ≤ d) :
    (smallEmaxDatum d).eMax = 4 ^ d := by
  simp only [smallEmaxDatum, ResidueDatum.eMax]
  apply le_antisymm
  · apply Finset.sup_le; intro x hx; simp at hx; exact hx.2
  · apply Finset.le_sup (f := id); simp
    exact Nat.one_le_of_lt (Nat.one_lt_pow (by omega) (by omega))

theorem smallEmaxDatum_ePos (d : ℕ):
    ∀ e ∈ (smallEmaxDatum d).E, 1 ≤ e := by
  intro e he; simp [smallEmaxDatum] at he; exact he.1

/-
Shifted congruence
-/
theorem shifted_coverage_nat (d : ℕ) (hd : 1 ≤ d) (R₀ : ℕ)
    (r : Fin d.factorial) :
    ∃ F : Finset ℕ, F ⊆ Finset.Icc 1 (4 ^ d) ∧
      (d.factorial : ℤ) ∣
        (∑ e ∈ F, ((R₀ : ℤ) + ↑e) ^ d - ↑(r : ℕ)) := by
  have := @interval_4d_complete d hd ( R₀ + 1 );
  obtain ⟨ F, hF₁, hF₂ ⟩ := this r;
  refine' ⟨ Finset.image ( fun x : ℤ => Int.toNat ( x - R₀ ) ) F, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  · intro x hx; specialize hF₁ hx; simp_all +decide [ Intv ] ;
    grind;
  · rw [ Finset.sum_image ];
    · rw [ Finset.sum_congr rfl fun x hx => by rw [ Nat.cast_sub ( by linarith [ Int.toNat_of_nonneg ( by linarith [ Finset.mem_Ico.mp ( hF₁ hx ) ] : 0 ≤ x ), Finset.mem_Ico.mp ( hF₁ hx ) ] ) ] ] ; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
      rw [ ← hF₂, sub_eq_zero ];
      exact Finset.sum_congr rfl fun x hx => by rw [ max_eq_left ( by linarith [ Finset.mem_Ico.mp ( hF₁ hx ) ] ) ] ;
    · intro x hx y hy; have := hF₁ hx; have := hF₁ hy; simp_all +decide [ Intv ] ;
      exact fun h => by linarith [ Int.toNat_of_nonneg ( by linarith [ hF₁ hx ] : 0 ≤ x ), Int.toNat_of_nonneg ( by linarith [ hF₁ hy ] : 0 ≤ y ), Nat.sub_add_cancel ( show R₀ ≤ Int.toNat x from by linarith [ Int.toNat_of_nonneg ( by linarith [ hF₁ hx ] : 0 ≤ x ), hF₁ hx ] ), Nat.sub_add_cancel ( show R₀ ≤ Int.toNat y from by linarith [ Int.toNat_of_nonneg ( by linarith [ hF₁ hy ] : 0 ≤ y ), hF₁ hy ] ) ] ;

noncomputable def shiftedF (d : ℕ) (hd : 1 ≤ d) (R₀ : ℕ)
    (r : Fin d.factorial) : Finset ℕ :=
  (shifted_coverage_nat d hd R₀ r).choose

theorem shiftedF_sub (d : ℕ) (hd : 1 ≤ d) (R₀ : ℕ)
    (r : Fin d.factorial) :
    shiftedF d hd R₀ r ⊆ Finset.Icc 1 (4 ^ d) :=
  (shifted_coverage_nat d hd R₀ r).choose_spec.1

theorem shiftedF_cong (d : ℕ) (hd : 1 ≤ d) (R₀ : ℕ)
    (r : Fin d.factorial) :
    (d.factorial : ℤ) ∣
      (∑ e ∈ shiftedF d hd R₀ r,
        ((R₀ : ℤ) + ↑e) ^ d - ↑(r : ℕ)) :=
  (shifted_coverage_nat d hd R₀ r).choose_spec.2

/-
For d ≥ 10, 6d + 2 ≤ 2^d.
-/
lemma residue_sum_bound (d : ℕ) (hd : 9 ≤ d) (R₀ : ℕ)
    (hR₀ : R₀ ≤ 6 * d * (4 ^ d + 1) + 1)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 (4 ^ d)) :
    (∑ e ∈ S, ((↑R₀ : ℤ) + ↑e) ^ d) ≤ (↑((4 : ℕ) ^ d) : ℤ) * (↑((8 : ℕ) ^ d) : ℤ) ^ d := by
  refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg hS _ ) _;
  · exact fun _ _ _ => by positivity;
  · refine' le_trans ( Finset.sum_le_sum fun i hi => pow_le_pow_left₀ ( by positivity ) ( show ( R₀ : ℤ ) + i ≤ 8 ^ d by
                                                                                            have h_bound : 6 * d * (4 ^ d + 1) + 1 + 4 ^ d ≤ (8 : ℕ) ^ d := by
                                                                                              refine' Nat.le_induction _ _ d hd <;> intros <;> norm_num [ Nat.pow_succ' ] at *;
                                                                                              nlinarith [ pow_pos ( show 0 < 4 by norm_num ) ‹_›, pow_le_pow_left' ( show 4 ≤ 8 by norm_num ) ‹_› ];
                                                                                            grind +extAll ) _ ) _ ; norm_num

end

open Polynomial Finset BigOperators
open Polynomial Finset BigOperators Nat

noncomputable section

/-
V_d = ∏(2^{i+1}-1) is odd.
-/
lemma V_d_odd (d : ℕ) : Odd (∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1)) := by
  exact Nat.odd_iff.mpr ( by norm_num [ Nat.pow_mod, Finset.prod_nat_mod ] )

/-
B = U_d * V_d < 2^{d²} for d ≥ 1.
-/
lemma UV_lt_pow_sq (d : ℕ) (hd : 1 ≤ d) :
    2 ^ (d * (d - 1) / 2) * (∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1)) < 2 ^ (d ^ 2) := by
  refine' lt_of_lt_of_le ( mul_lt_mul_of_pos_left ( show ∏ i : Fin d, ( 2 ^ ( i.val + 1 ) - 1 ) < 2 ^ ( d * ( d + 1 ) / 2 ) from _ ) ( pow_pos ( by decide ) _ ) ) _;
  · refine' lt_of_lt_of_le ( Finset.prod_lt_prod _ _ _ ) _;
    use fun i => 2 ^ ( i.val + 1 );
    · exact fun i _ => Nat.sub_pos_of_lt ( one_lt_pow₀ ( by decide ) ( by linarith ) );
    · exact fun i _ => Nat.sub_le _ _;
    · exact ⟨ ⟨ 0, hd ⟩, Finset.mem_univ _, Nat.sub_lt ( by norm_num ) ( by norm_num ) ⟩;
    · rw [ Finset.prod_pow_eq_pow_sum ];
      exact pow_le_pow_right₀ ( by decide ) ( Nat.le_div_iff_mul_le zero_lt_two |>.2 <| Nat.recOn d ( by norm_num ) fun n ih => by norm_num [ Fin.sum_univ_castSucc ] at * ; linarith );
  · rw [ ← pow_add ];
    exact pow_le_pow_right₀ ( by decide ) ( by nlinarith [ Nat.sub_add_cancel hd, Nat.div_mul_cancel ( show 2 ∣ d * ( d - 1 ) from even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ), Nat.div_mul_cancel ( show 2 ∣ d * ( d + 1 ) from even_iff_two_dvd.mp ( by simp +arith +decide [ mul_add, parity_simps ] ) ) ] )

/-
d! * B ≤ 2^{2d²} for d ≥ 1.
-/
lemma factorial_UV_le (d : ℕ) (hd : 1 ≤ d) :
    d.factorial * (2 ^ (d * (d - 1) / 2) * (∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1))) ≤
    2 ^ (2 * d ^ 2) := by
  -- By multiplying the inequalities $d! \leq 2^{d^2}$ and $U/V < 2^{d^2}$, we get the desired result.
  have h_mul : d ! * (2 ^ (d * (d - 1) / 2) * (∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1))) ≤ (2 ^ (d ^ 2)) * (2 ^ (d ^ 2)) := by
    gcongr;
    · -- By induction on $d$, we can show that $d! \leq d^d$.
      have h_ind : ∀ d : ℕ, 1 ≤ d → d ! ≤ d ^ d := by
        exact fun n hn => Nat.recOn n ( by norm_num ) fun n ih => by rw [ pow_succ' ] ; exact le_trans ( Nat.mul_le_mul_left _ ih ) ( by gcongr ; nlinarith ) ;
      exact le_trans ( h_ind d hd ) ( by rw [ sq, pow_mul ] ; gcongr ; nlinarith [ show 2 ^ d ≥ d + 1 from Nat.recOn d ( by norm_num ) fun n ih => by rw [ pow_succ' ] ; nlinarith ] );
    · convert Nat.le_of_lt ( UV_lt_pow_sq d hd ) using 1;
  convert h_mul using 1 ; ring

/-
For d ≥ 9: 6d² ≤ 2^{d+3}.
-/
lemma six_dsq_le (d : ℕ) (hd : 9 ≤ d) : 6 * d ^ 2 ≤ 2 ^ (d + 3) := by
  -- We proceed by induction on $d$.
  induction' hd with d hd iharith;
  · decide +revert;
  · norm_num [ pow_succ' ] at * ; nlinarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ ( 2:ℕ ) ) hd ]

/-
If C_neg ≤ 2^{6d²+9d+3}, d!B ≤ 2^{2d²}, M ≤ 2^{3d²+2d},
then C_neg + d!B + M + 1 ≤ 2^{6d²+9d+5} for d ≥ 9.
-/
lemma improved_bound_assembly (d : ℕ) (hd : 9 ≤ d)
    (C_neg M aB : ℤ)
    (h1 : C_neg ≤ 2 ^ (6 * d ^ 2 + 9 * d + 3))
    (h2 : aB ≤ 2 ^ (2 * d ^ 2))
    (h3 : M ≤ 2 ^ (3 * d ^ 2 + 2 * d)) :
    C_neg + aB + M + 1 ≤ 2 ^ (6 * d ^ 2 + 9 * d + 5) := by
  -- Since $2d^2 \leq 6d^2 + 9d + 3$ and $3d^2 + 2d \leq 6d^2 + 9d + 3$ for $d \geq 1$, all three terms $C_neg$, $aB$, $M$ are $\leq 2^{6d^2 + 9d + 3}$.
  have h_bounds : aB ≤ 2^(6 * d^2 + 9 * d + 3) ∧ M ≤ 2^(6 * d^2 + 9 * d + 3) := by
    exact ⟨ h2.trans ( pow_le_pow_right₀ ( by decide ) ( by nlinarith ) ), h3.trans ( pow_le_pow_right₀ ( by decide ) ( by nlinarith ) ) ⟩;
  ring_nf at *;
  nlinarith [ pow_le_pow_right₀ ( show 1 ≤ 2 by norm_num ) ( show d * 9 ≥ 0 by positivity ), pow_le_pow_right₀ ( show 1 ≤ 2 by norm_num ) ( show d ^ 2 * 6 ≥ 0 by positivity ) ]

/-
A general signed block from any shift list satisfying the buildPN increasing condition.
    This generalizes signed_block_r and signed_block_s to arbitrary shifts.
-/
theorem signed_block_general (d : ℕ) (hd : 1 ≤ d) (shifts : List ℕ)
    (hl : shifts.length = d)
    (h_inc : ∀ i : Fin shifts.length,
      ∀ u ∈ (buildPN (shifts.take i)).1 ∪ (buildPN (shifts.take i)).2,
        u < shifts[i])
    (h_nz : ∀ i : Fin shifts.length, 0 < shifts[i]) :
    let pn := buildPN shifts
    Disjoint pn.1 pn.2 ∧
    (∀ x : ℤ,
      ∑ u ∈ pn.1, (x + (↑u : ℤ)) ^ d -
      ∑ v ∈ pn.2, (x + (↑v : ℤ)) ^ d =
      (d.factorial : ℤ) * ∏ i : Fin d, ((shifts[i.val]'(by omega) : ℤ))) := by
  have := foldl_eval_eq_pn ( monomialPoly d ) shifts ?_; simp_all +decide [ monomialPoly ] ;
  · -- By Lemma 2, the foldl of the shifts list is a constant polynomial.
    have h_const : List.foldl (fun f hi => diffOp hi f) (X ^ d) (List.flatMap (fun a => [↑a]) shifts) = Polynomial.C (d ! * ∏ i : Fin shifts.length, (shifts[i] : ℤ)) := by
      convert iterated_diff_const ( X ^ d ) d _ _ _ using 1 <;> norm_num [ hl ];
      rotate_right;
      use fun i => shifts[i]!;
      · rw [ ← hl ] ; simp +decide ;
        simp +decide [ Function.comp, List.map_eq_flatMap ];
        grind;
      · linarith;
    simp_all +decide ;
    convert this.2 using 2;
    · exact this.2 _ ▸ rfl;
    · convert this.2 ‹_› using 1;
      simp +decide [ Polynomial.eval_list_prod ];
      exact Or.inl ( by rw [ ← List.prod_ofFn ] ; exact congr_arg _ ( by exact List.ext_get ( by aesop ) ( by aesop ) ) );
  · assumption

/-
All elements of buildPN are ≤ the sum of shifts (they are subset sums).
-/
lemma buildPN_elements_le_sum (shifts : List ℕ)
    (h_inc : ∀ i : Fin shifts.length,
      ∀ u ∈ (buildPN (shifts.take i)).1 ∪ (buildPN (shifts.take i)).2,
        u < shifts[i]) :
    ∀ u ∈ (buildPN shifts).1 ∪ (buildPN shifts).2,
      u ≤ shifts.sum := by
        induction' shifts using List.reverseRecOn with shifts h ih <;> simp +decide [ buildPN ] at *;
        unfold stepPN; simp_all +decide ;
        rintro u ( ( ⟨ a, ha, rfl ⟩ | ha ) | ha | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ stepPN ];
        · refine' ih _ a ( Or.inl ha );
          intro i u hu; specialize h_inc ⟨ i, by simp +decide ⟩ u; simp_all +decide ;
          simp_all +decide [ List.take_append_of_le_length, i.2.le ];
        · specialize h_inc ⟨ shifts.length, by simp +decide ⟩ u ; simp_all +decide ;
          exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) h_inc.le;
        · refine' le_add_right ( ih _ u ( Or.inl ha ) |> le_trans <| _ );
          · intro i u hu; specialize h_inc ⟨ i, by simp +decide ⟩ u; simp_all +decide [ List.take_append_of_le_length ] ;
          · norm_num;
        · convert ih _ _ ( Or.inr ha ) using 1;
          intro i u hu; specialize h_inc ⟨ i, by simp +decide ⟩ u; simp_all +decide [ List.take_append_of_le_length ] ;

/-
The N-set of buildPN has card 2^{length-1} when length ≥ 1.
-/
lemma buildPN_N_card_eq (shifts : List ℕ) (hlen : 1 ≤ shifts.length)
    (h_inc : ∀ i : Fin shifts.length,
      ∀ u ∈ (buildPN (shifts.take i)).1 ∪ (buildPN (shifts.take i)).2,
        u < shifts[i]) :
    (buildPN shifts).2.card = 2 ^ (shifts.length - 1) := by
      have h_card : ∀ shifts : List ℕ, 1 ≤ shifts.length → (∀ i : Fin shifts.length, ∀ u ∈ (buildPN (shifts.take i)).1 ∪ (buildPN (shifts.take i)).2, u < shifts[i]) → (buildPN shifts).1.card = 2 ^ (shifts.length - 1) ∧ (buildPN shifts).2.card = 2 ^ (shifts.length - 1) := by
        intro shifts hlen h_inc; induction' shifts using List.reverseRecOn with shifts ih <;> simp_all +decide ;
        have h_card : (buildPN (shifts ++ [ih])).1 = (buildPN shifts).1.image (· + ih) ∪ (buildPN shifts).2 ∧ (buildPN (shifts ++ [ih])).2 = (buildPN shifts).1 ∪ (buildPN shifts).2.image (· + ih) := by
          unfold buildPN; aesop;
        rcases shifts <;> simp_all +decide ;
        · simp +decide [ buildPN ];
        · rename_i k hk hk₂;
          have := hk₂ ( fun i u hu => ?_ ) ; simp_all +decide [ Fin.forall_fin_succ, pow_succ' ] ;
          · rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;> norm_num [ this, Finset.disjoint_right ];
            · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> simp +decide [ Function.Injective, * ] ; ring;
            · intro a ha hb; have := h_inc.2 ⟨ hk.length, by simp +decide ⟩ ( a + ih ) ; simp_all +decide ;
            · intro a ha x hx; have := h_inc.2 ⟨ hk.length, by simp +decide ⟩ a; simp_all +decide ;
              linarith;
          · convert h_inc ⟨ i, by simp +arith +decide [ List.length_append ] ⟩ u _ using 1;
            · grind;
            · rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide [ List.take_append ];
              simp_all +decide [ Nat.sub_eq_zero_of_le ( by linarith : i ≤ hk.length ) ];
      exact h_card shifts hlen h_inc |>.2

/-
Sum of distinct powers of 2 with exponents in S, all < n, is < 2^n.
-/
lemma sum_distinct_pow2_lt (S : Finset ℕ) (n : ℕ) (h : ∀ s ∈ S, s < n) :
    ∑ s ∈ S, 2 ^ s < 2 ^ n := by
      -- Sum of distinct powers of 2 with exponents < n is at most sum of all powers of 2 up to 2^(n-1).
      have : ∑ s ∈ S, 2 ^ s ≤ ∑ s ∈ Finset.range n, 2 ^ s := by
        exact Finset.sum_le_sum_of_subset fun x hx => Finset.mem_range.mpr ( h x hx );
      exact lt_of_le_of_lt this ( Nat.geomSum_lt ( by norm_num ) ( by aesop ) )

/-
For strictly increasing exponents, the powers of 2 satisfy the buildPN increasing
    condition: all elements of buildPN from the first i shifts are < 2^(exps i).
-/
lemma pow2_buildPN_inc (d : ℕ) (exps : Fin d → ℕ) (hm : StrictMono exps) :
    let shifts := List.ofFn (fun i : Fin d => 2 ^ exps i)
    ∀ i : Fin shifts.length,
      ∀ u ∈ (buildPN (shifts.take i)).1 ∪ (buildPN (shifts.take i)).2,
        u < shifts[i] := by
          -- By strong induction on i (the Fin index).
          intro shifts i
          induction' i with k hk;
          have h_ind : ∀ j : Fin (k + 1), ∀ u ∈ (buildPN (shifts.take j)).1 ∪ (buildPN (shifts.take j)).2, u < shifts[j] := by
            intro j
            induction' j with j ih;
            induction' j using Nat.strong_induction_on with j ih;
            intro u hu;
            have h_sum_lt : ∑ s ∈ Finset.image exps (Finset.univ.filter (fun i => i.val < j)), 2 ^ s < 2 ^ (exps ⟨j, by
              grind +qlia⟩) := by
              convert sum_distinct_pow2_lt _ _ _ using 1;
              simp +decide [ hm.lt_iff_lt ];
              exact fun a ha => ha
            generalize_proofs at *;
            have h_sum_le : u ≤ ∑ s ∈ Finset.image exps (Finset.univ.filter (fun i => i.val < j)), 2 ^ s := by
              have h_sum_le : u ≤ (shifts.take j).sum := by
                apply buildPN_elements_le_sum;
                · grind +locals;
                · exact hu;
              convert h_sum_le using 1;
              rw [ Finset.sum_image <| by intros i hi j hj hij; exact hm.injective hij ];
              rw [ List.sum_take_ofFn ];
            grind;
          exact h_ind ⟨ k, Nat.lt_succ_self k ⟩

/-
For d ≥ 1 and j ≤ 4d², there exists a signed block of value d!·2^{D_d+j}
    with support in {0,...,2^{5d+2}-1}.
-/
set_option maxHeartbeats 800000 in
theorem u_block_exists (d j : ℕ) (hd : 1 ≤ d) (hj : j ≤ 4 * d ^ 2) :
    ∃ (P N : Finset ℕ),
      Disjoint P N ∧
      (∀ u ∈ P ∪ N, u < 2 ^ (5 * d + 2)) ∧
      N.card ≤ 2 ^ (d - 1) ∧
      (∀ x : ℤ,
        ∑ u ∈ P, (x + (↑u : ℤ)) ^ d -
        ∑ v ∈ N, (x + (↑v : ℤ)) ^ d =
        (d.factorial : ℤ) * 2 ^ (d * (d - 1) / 2 + j)) := by
  revert d j hd hj;
  intro d j hd hj
  set exps : Fin d → ℕ := fun i => j / d + i.val + (if d - j % d ≤ i.val then 1 else 0) with h_exp_def
  set shifts : List ℕ := List.ofFn (fun i : Fin d => 2 ^ exps i) with h_shifts_def
  have h_shifts_length : shifts.length = d := by
    grind
  have h_shifts_inc : ∀ i : Fin shifts.length, ∀ u ∈ (buildPN (shifts.take i)).1 ∪ (buildPN (shifts.take i)).2, u < shifts[i] := by
    convert pow2_buildPN_inc d exps _ using 1;
    intro i j hij; simp +decide [ exps ] ; split_ifs <;> omega;
  have h_shifts_nz : ∀ i : Fin shifts.length, 0 < shifts[i] := by
    simp +zetaDelta at *
  have h_shifts_prod : ∏ i : Fin d, ((shifts[i.val]'(by omega) : ℤ)) = 2 ^ (d * (d - 1) / 2 + j) := by
    have h_exp_sum : ∑ i : Fin d, exps i = d * (d - 1) / 2 + j := by
      have h_sum_exps : ∑ i : Fin d, exps i = d * (j / d) + d * (d - 1) / 2 + (j % d) := by
        have h_sum_exps : ∑ i : Fin d, (if d - j % d ≤ i.val then 1 else 0) = j % d := by
          simp +zetaDelta at *;
          rw [ Finset.card_eq_of_bijective ];
          use fun i hi => ⟨ d - j % d + i, by linarith [ Nat.sub_add_cancel ( show j % d ≤ d from Nat.le_of_lt ( Nat.mod_lt _ hd ) ), Nat.mod_lt j hd ] ⟩;
          · simp +zetaDelta at *;
            exact fun a ha => ⟨ a - ( d - j % d ), by omega, by erw [ Fin.ext_iff ] ; norm_num; omega ⟩;
          · grind;
          · grind +locals
        simp_all +decide [ Finset.sum_add_distrib ];
        convert Finset.sum_range_id d using 1 ; rw [ Finset.sum_range ];
      linarith [ Nat.mod_add_div j d ]
    generalize_proofs at *; (
    rw [ ← h_exp_sum ] ; norm_cast ; simp +decide [ h_shifts_def ] ; ring_nf;
    rw [ Finset.prod_pow_eq_pow_sum ])
  have h_shifts_sum : shifts.sum ≤ 2 ^ (5 * d + 1) := by
    nontriviality;
    have h_shifts_sum : shifts.sum ≤ ∑ i ∈ Finset.range d, 2 ^ (j / d + i + 1) := by
      rw [ List.sum_ofFn ];
      rw [ Finset.sum_range ] ; exact Finset.sum_le_sum fun i _ => pow_le_pow_right₀ ( by decide ) ( by aesop ) ;
    refine le_trans h_shifts_sum ?_;
    norm_num [ pow_add, Finset.mul_sum _ _ _, Finset.sum_mul ];
    norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    rw [ Nat.geomSum_eq ] <;> norm_num;
    refine' le_trans ( Nat.mul_le_mul_right _ ( pow_le_pow_right₀ ( by decide ) ( show j / d ≤ 4 * d by nlinarith [ Nat.div_mul_le_self j d ] ) ) ) _;
    rw [ show 5 * d = 4 * d + d by ring, pow_add ] ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( 4 * d ), pow_pos ( zero_lt_two' ℕ ) d, Nat.sub_add_cancel ( Nat.one_le_pow d 2 zero_lt_two ) ]
  have h_buildPN_card : (buildPN shifts).2.card = 2 ^ (d - 1) := by
    convert buildPN_N_card_eq shifts ( by linarith ) h_shifts_inc using 1;
    rw [ h_shifts_length ]
  have h_buildPN_le : ∀ u ∈ (buildPN shifts).1 ∪ (buildPN shifts).2, u < 2 ^ (5 * d + 2) := by
    intros u hu
    have h_u_le_sum : u ≤ shifts.sum := by
      apply buildPN_elements_le_sum shifts h_shifts_inc u hu
    have h_sum_lt : shifts.sum < 2 ^ (5 * d + 2) := by
      exact lt_of_le_of_lt h_shifts_sum ( pow_lt_pow_right₀ ( by decide ) ( Nat.lt_succ_self _ ) )
    exact lt_of_le_of_lt h_u_le_sum h_sum_lt
  use (buildPN shifts).1, (buildPN shifts).2
  simp_all +decide [ Finset.disjoint_left ];
  convert signed_block_general d hd ( List.ofFn fun i : Fin d => 2 ^ ( j / d + i.val + if d ≤ i.val + j % d then 1 else 0 ) ) _ _ _ using 1 <;> norm_num [ h_shifts_length, h_shifts_inc, h_shifts_prod ];
  · exact ⟨ fun h => Finset.disjoint_left.mpr fun x hx₁ hx₂ => h hx₁ hx₂, fun h x hx₁ hx₂ => Finset.disjoint_left.mp h hx₁ hx₂ ⟩;
  · convert h_shifts_inc using 1;
    grind

/-
If each shift strictly exceeds the sum of all previous shifts,
    the buildPN increasing condition holds.
-/
lemma superincreasing_buildPN_inc (shifts : List ℕ)
    (h_super : ∀ k : Fin shifts.length, (shifts.take k).sum < shifts[k]) :
    ∀ i : Fin shifts.length,
      ∀ u ∈ (buildPN (shifts.take i)).1 ∪ (buildPN (shifts.take i)).2,
        u < shifts[i] := by
          intro i
          induction' i with i ih;
          have h_ind : ∀ j : Fin (i + 1), ∀ u ∈ (buildPN (List.take j shifts)).1 ∪ (buildPN (List.take j shifts)).2, u < shifts[j] := by
            intro j
            induction' j with j ih_j;
            induction' j using Nat.strong_induction_on with j ih_j;
            have h_ind : ∀ u ∈ (buildPN (List.take j shifts)).1 ∪ (buildPN (List.take j shifts)).2, u ≤ (List.take j shifts).sum := by
              apply buildPN_elements_le_sum;
              grind;
            exact fun u hu => lt_of_le_of_lt ( h_ind u hu ) ( h_super ⟨ j, by linarith ⟩ );
          exact h_ind ⟨ i, Nat.lt_succ_self i ⟩

/-
The v-shifts v_k = 2^{q+ε_k} * (2^{k+1}-1) are superincreasing.
-/
lemma vShifts_superincreasing (d q r : ℕ):
    let shifts := List.ofFn (fun k : Fin d =>
      2 ^ (q + if d - r ≤ k.val then 1 else 0) * (2 ^ (k.val + 1) - 1))
    ∀ k : Fin shifts.length, (shifts.take k).sum < shifts[k] := by
      intro shifts k
      have h_sum_lt : (List.take k.val shifts).sum ≤ 2^(q + if d - r ≤ k.val then 1 else 0) * (∑ j ∈ Finset.range k.val, (2^(j+1) - 1)) := by
        have h_sum_lt : (List.take k.val shifts).sum ≤ ∑ j ∈ Finset.range k.val, 2^(q + if d - r ≤ j then 1 else 0) * (2^(j+1) - 1) := by
          rw [ List.sum_take_ofFn ];
          refine' le_of_eq _;
          refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +decide [ Fin.ext_iff ];
          exact fun b hb => ⟨ ⟨ b, by linarith [ Fin.is_lt k, show k.val < d from by simpa [ shifts ] using k.2 ] ⟩, hb, rfl ⟩;
        rw [ Finset.mul_sum _ _ _ ];
        refine le_trans h_sum_lt <| Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ?_ <| Nat.zero_le _;
        grind;
      -- The sum of the terms up to k is less than the term at k because each term is larger than the sum of the previous terms.
      have h_sum_lt_term : ∑ j ∈ Finset.range k.val, (2^(j+1) - 1) < 2^(k.val + 1) - 1 := by
        exact Nat.recOn k ( by norm_num ) fun n ihn => by norm_num [ Finset.sum_range_succ, pow_succ' ] at * ; omega;
      simp +zetaDelta at *;
      exact lt_of_le_of_lt h_sum_lt ( mul_lt_mul_of_pos_left h_sum_lt_term ( by positivity ) )

/-
Product of v-shifts equals V_d * 2^{dq+r}.
-/
lemma vShifts_product (d : ℕ) (q r : ℕ) (hr : r < d) :
    ∏ k : Fin d,
      ((2 ^ (q + if d - r ≤ k.val then 1 else 0) * (2 ^ (k.val + 1) - 1) : ℕ) : ℤ) =
      (∏ k : Fin d, (2 ^ ((k : ℕ) + 1) - 1 : ℤ)) * 2 ^ (d * q + r) := by
        norm_num [ Finset.prod_mul_distrib ];
        norm_num [ Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, mul_comm, mul_assoc, Finset.prod_ite ];
        rw [ mul_comm, show ( Finset.univ.filter fun x : Fin d => d ≤ ( x : ℕ ) + r ).card = r from ?_ ];
        rw [ Finset.card_eq_of_bijective ];
        use fun i hi => ⟨ d - r + i, by linarith [ Nat.sub_add_cancel hr.le ] ⟩;
        · exact fun x hx => ⟨ x - ( d - r ), by rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt x, Nat.sub_add_cancel hr.le, Finset.mem_filter.mp hx ], by erw [ Fin.ext_iff ] ; simp +decide [ Nat.add_sub_of_le ( show d - r ≤ x from by linarith [ Finset.mem_filter.mp hx, Nat.sub_add_cancel hr.le ] ) ] ⟩;
        · grind;
        · grind

/-
For d ≥ 1 and i < d(d-1)/2, there exists a signed block of value d!·V_d·2^i
    with support in {0,...,2^{5d+2}-1}.
-/
theorem v_block_exists (d i : ℕ) (hd : 1 ≤ d) (hi : i < d * (d - 1) / 2) :
    ∃ (P N : Finset ℕ),
      Disjoint P N ∧
      (∀ u ∈ P ∪ N, u < 2 ^ (5 * d + 2)) ∧
      N.card ≤ 2 ^ (d - 1) ∧
      (∀ x : ℤ,
        ∑ u ∈ P, (x + (↑u : ℤ)) ^ d -
        ∑ v ∈ N, (x + (↑v : ℤ)) ^ d =
        (d.factorial : ℤ) * (∏ k : Fin d, (2 ^ ((k : ℕ) + 1) - 1)) * 2 ^ i) := by
  -- Set q = i / d and r = i % d (so i = d*q + r, r < d).
  obtain ⟨q, r, hr⟩ : ∃ q r : ℕ, i = d * q + r ∧ r < d := by
    exact ⟨ i / d, i % d, by rw [ Nat.div_add_mod ], Nat.mod_lt _ hd ⟩;
  -- Define shifts = List.ofFn (fun k : Fin d => 2^(q + if d-r ≤ k then 1 else 0) * (2^(k+1)-1)).
  set shifts : List ℕ :=
    List.ofFn (fun k : Fin d =>
      2 ^ (q + if d - r ≤ k.val then 1 else 0) * (2 ^ (k.val + 1) - 1));
  -- By signed_block_general, these shifts satisfy the buildPN increasing condition.
  have h_inc : ∀ i : Fin shifts.length, ∀ u ∈ (buildPN (shifts.take i)).1 ∪ (buildPN (shifts.take i)).2, u < shifts[i] := by
    apply superincreasing_buildPN_inc;
    convert vShifts_superincreasing d q r ;
  -- By buildPN_elements_le_sum, all elements ≤ sum of shifts < 2^{q+d+2}.
  have h_sum_le : ∀ u ∈ (buildPN shifts).1 ∪ (buildPN shifts).2, u < 2 ^ (q + d + 2) := by
    have h_sum_le : shifts.sum < 2 ^ (q + d + 2) := by
      have h_sum_shifts : shifts.sum ≤ ∑ k ∈ Finset.range d, 2 ^ (q + k + 2) := by
        have h_sum_shifts : ∀ k : Fin d, shifts[k]! ≤ 2 ^ (q + k.val + 2) := by
          intro k; simp +decide [ shifts ] ; split_ifs <;> ring_nf ;
          · nlinarith [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ ( k : ℕ ) * 2 from Nat.one_le_iff_ne_zero.mpr <| by positivity ), pow_pos ( show 0 < 2 by decide ) q, pow_pos ( show 0 < 2 by decide ) ( k : ℕ ) ];
          · nlinarith [ Nat.sub_le ( 2 ^ ( k : ℕ ) * 2 ) 1, pow_pos ( zero_lt_two' ℕ ) q, pow_pos ( zero_lt_two' ℕ ) ( k : ℕ ) ];
        convert Finset.sum_le_sum fun k ( hk : k ∈ Finset.univ ) => h_sum_shifts k using 1;
        · simp +zetaDelta at *;
          exact List.sum_ofFn;
        · rw [ Finset.sum_range ];
      refine lt_of_le_of_lt h_sum_shifts ?_;
      norm_num [ pow_add, Finset.mul_sum _ _ _, geom_sum_eq ];
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
      rw [ Nat.geomSum_eq ] <;> norm_num;
    exact fun u hu => lt_of_le_of_lt ( buildPN_elements_le_sum shifts h_inc u hu ) h_sum_le;
  refine' ⟨ buildPN shifts |>.1, buildPN shifts |>.2, _, _, _, _ ⟩;
  · apply (signed_block_general d hd shifts (by
    simp [shifts]) h_inc (by
    simp +zetaDelta at *)).left;
  · refine' fun u hu => lt_of_lt_of_le ( h_sum_le u hu ) _;
    gcongr <;> norm_num;
    nlinarith [ Nat.div_mul_le_self ( d * ( d - 1 ) ) 2, Nat.sub_add_cancel hd ];
  · have h_card_N : (buildPN shifts).2.card = 2 ^ (shifts.length - 1) := by
      apply buildPN_N_card_eq;
      · simp +zetaDelta at *;
        linarith;
      · assumption;
    grind;
  · have h_prod : ∏ k : Fin d, ((shifts[k.val]'(by
    grind) : ℕ) : ℤ) = (∏ k : Fin d, (2 ^ ((k : ℕ) + 1) - 1 : ℤ)) * 2 ^ (d * q + r) := by
      convert vShifts_product d q r hr.2 using 1;
      grind
    generalize_proofs at *;
    have := signed_block_general d hd shifts ( by simp +decide [ shifts ] ) h_inc ( by
      simp +zetaDelta at * ) ; simp_all +decide [ mul_assoc ] ;

/-
Binary coverage: for V odd, every n ∈ [U·V, U·V+Q] (with Q < U·2^J)
    is a subset sum of {V·2^i : i < D} ∪ {U·2^j : j < J}.
-/
theorem binary_coverage (D J : ℕ) (V : ℕ) (hV_odd : Odd V) (hV_pos : 0 < V)
    (Q : ℕ) (hQ : V * 2 ^ D + Q < 2 ^ D * 2 ^ J) :
    ∀ n : ℕ, V * 2 ^ D ≤ n → n ≤ V * 2 ^ D + Q →
      ∃ (S_V : Finset (Fin D)) (S_U : Finset (Fin J)),
        (n : ℤ) = ↑V * ∑ i ∈ S_V, (2 ^ (i : ℕ) : ℤ) +
                   2 ^ D * ∑ j ∈ S_U, (2 ^ (j : ℕ) : ℤ) := by
  -- Let t = (V⁻¹ * n) mod 2^D.
  intro n hn₁ hn₂
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t < 2 ^ D ∧ (n : ℤ) ≡ V * t [ZMOD 2 ^ D] := by
    -- Since V is odd, gcd(V, 2^D) = 1, so V has a multiplicative inverse mod 2^D.
    obtain ⟨t, ht⟩ : ∃ t : ℕ, t < 2 ^ D ∧ V * t ≡ n [MOD 2 ^ D] := by
      have h_inv : ∃ t, V * t ≡ 1 [MOD 2 ^ D] := by
        have := Nat.exists_mul_mod_eq_one_of_coprime ( show Nat.Coprime V ( 2 ^ D ) from ?_ );
        · rcases D with ( _ | D ) <;> simp_all +decide [ Nat.ModEq, Nat.mod_one ];
          exact ⟨ this.choose, this.choose_spec.2 ⟩;
        · cases D <;> cases hV_odd <;> aesop;
      obtain ⟨ t, ht ⟩ := h_inv; use t * n % ( 2 ^ D ) ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
      exact ⟨ Nat.mod_lt _ ( by positivity ), by linear_combination' ht * n ⟩;
    exact ⟨ t, mod_cast ht.1, Int.natCast_modEq_iff.mpr ht.2.symm ⟩;
  -- Let m = (n - V*t) / 2^D.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = V * t + 2 ^ D * m := by
    obtain ⟨ m, hm ⟩ := ht.2.symm.dvd;
    exact ⟨ Int.toNat m, by nlinarith [ Int.toNat_of_nonneg ( by nlinarith [ pow_pos ( zero_lt_two' ℤ ) D ] : ( 0 : ℤ ) ≤ m ) ] ⟩;
  -- Let S_V be the set of indices where the binary representation of t has a 1.
  obtain ⟨S_V, hS_V⟩ : ∃ S_V : Finset (Fin D), t = ∑ i ∈ S_V, 2 ^ (i : ℕ) := by
    have h_binary : ∀ t : ℕ, t < 2 ^ D → ∃ S_V : Finset (Fin D), t = ∑ i ∈ S_V, 2 ^ (i : ℕ) := by
      intro t ht
      have h_binary : ∃ S_V : Finset (Fin D), t = ∑ i ∈ S_V, 2 ^ (i : ℕ) := by
        have h_binary_rep : ∀ t : ℕ, t < 2 ^ D → ∃ S_V : Finset (Fin D), t = ∑ i ∈ S_V, 2 ^ (i : ℕ) := by
          intro t ht
          have h_binary_rep : t = ∑ i ∈ Finset.range D, (t / 2 ^ i) % 2 * 2 ^ i := by
            have h_binary_rep : ∀ t : ℕ, t < 2 ^ D → t = ∑ i ∈ Finset.range D, (t / 2 ^ i) % 2 * 2 ^ i := by
              intro t ht
              have h_binary_rep : t = ∑ i ∈ Finset.range D, (t / 2 ^ i) % 2 * 2 ^ i := by
                have h_binary_rep : ∀ n : ℕ, t = ∑ i ∈ Finset.range n, (t / 2 ^ i) % 2 * 2 ^ i + (t / 2 ^ n) * 2 ^ n := by
                  intro n; induction' n with n ih <;> simp +decide [ Finset.sum_range_succ, pow_succ, ← Nat.div_div_eq_div_mul ] at *;
                  nlinarith [ Nat.mod_add_div ( t / 2 ^ n ) 2, pow_pos ( zero_lt_two' ℕ ) n ]
                specialize h_binary_rep D; norm_num [ Nat.div_eq_of_lt ht ] at h_binary_rep; linarith;
              exact h_binary_rep;
            exact h_binary_rep t ht
          use Finset.univ.filter (fun i => (t / 2 ^ (i : ℕ)) % 2 = 1);
          convert h_binary_rep using 1;
          rw [ Finset.sum_filter, Finset.sum_range ];
          exact Finset.sum_congr rfl fun i hi => by rcases Nat.mod_two_eq_zero_or_one ( t / 2 ^ ( i : ℕ ) ) with h | h <;> simp +decide [ h ] ;
        exact h_binary_rep t ht;
      exact h_binary;
    exact h_binary t ht.1;
  -- Let S_U be the set of indices where the binary representation of m has a 1.
  obtain ⟨S_U, hS_U⟩ : ∃ S_U : Finset (Fin J), m = ∑ j ∈ S_U, 2 ^ (j : ℕ) := by
    have h_binary : ∀ m : ℕ, m < 2 ^ J → ∃ S_U : Finset (Fin J), m = ∑ j ∈ S_U, 2 ^ (j : ℕ) := by
      intro m hm
      have h_binary : m = ∑ j ∈ Finset.filter (fun j => (m / 2 ^ j.val) % 2 = 1) (Finset.univ : Finset (Fin J)), 2 ^ (j : ℕ) := by
        have h_binary : m = ∑ j ∈ Finset.range J, (m / 2 ^ j) % 2 * 2 ^ j := by
          have h_binary : ∀ m J : ℕ, m = ∑ j ∈ Finset.range J, (m / 2 ^ j) % 2 * 2 ^ j + (m / 2 ^ J) * 2 ^ J := by
            intro m J; induction' J with J ih <;> simp +decide [ Finset.sum_range_succ, pow_succ, ← Nat.div_div_eq_div_mul ] ;
            nlinarith [ Nat.mod_add_div ( m / 2 ^ J ) 2, pow_pos ( zero_lt_two' ℕ ) J ];
          nlinarith [ h_binary m J, Nat.div_eq_of_lt hm ];
        convert h_binary using 1;
        rw [ Finset.sum_filter, Finset.sum_range ];
        exact Finset.sum_congr rfl fun x hx => by rcases Nat.mod_two_eq_zero_or_one ( m / 2 ^ ( x : ℕ ) ) with h | h <;> simp +decide [ h ] ;
      exact ⟨ _, h_binary ⟩;
    exact h_binary m ( by nlinarith [ pow_pos ( zero_lt_two' ℕ ) D ] );
  exact ⟨ S_V, S_U, by push_cast [ hm, hS_V, hS_U ] ; ring ⟩

/-
The total number of block indices (u-blocks + v-blocks) is at most 6d²
-/
lemma block_count_le (d : ℕ) (hd : 1 ≤ d) :
    4 * d ^ 2 + 1 + d * (d - 1) / 2 ≤ 6 * d ^ 2 := by
  nlinarith [ Nat.div_mul_le_self ( d * ( d - 1 ) ) 2, Nat.sub_add_cancel hd ]

/-
Maximum position in the bank is bounded by 2^{6d+7}
-/
lemma bank_max_position_bound (d : ℕ) (hd : 9 ≤ d) (Y W : ℕ)
    (hW : W = 2 ^ (5 * d + 2))
    (hY : Y ≤ 6 * d * (W + 2) + 1)
    (T : ℕ) (hT : T ≤ 6 * d ^ 2) (e : ℕ) (he : e < W) :
    Y + T * (W + 1) + e < 2 ^ (6 * d + 7) := by
  -- We'll use that $W \geq 980$ and $d \geq 9$ to show the bounds.
  have hW_large : 980 ≤ W := by
    exact hW.symm ▸ le_trans ( by decide ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.add_le_add ( Nat.mul_le_mul_left 5 hd ) le_rfl ) )
  have hd_large : 9 ≤ d := by
    linarith;
  -- We'll use that $W \geq 980$ and $d \geq 9$ to show the bounds on $Y + T * (W + 1) + e$.
  have h_bound : (6 * d * (W + 2) + 1) + 6 * d ^ 2 * (W + 1) + W < 2 ^ (6 * d + 7) := by
    subst hW;
    induction' hd_large with d hd ih <;> norm_num [ Nat.pow_succ', Nat.pow_mul ] at *;
    exact Nat.recOn d ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; nlinarith only [ ihn, pow_pos ( show 0 < 32 by norm_num ) n, pow_le_pow_left' ( show 64 ≥ 32 by norm_num ) n ] ;
  exact lt_of_le_of_lt ( by nlinarith only [ hY, hT, he ] ) h_bound

/-
(6d²) * 2^{d-1} ≤ 2^{2d+2} for d ≥ 9, using six_dsq_le
-/
lemma neg_count_bound (d : ℕ) (hd : 9 ≤ d) :
    6 * d ^ 2 * 2 ^ (d - 1) ≤ 2 ^ (2 * d + 2) := by
  -- By multiplying both sides of the inequality $6d^2 \leq 2^{d+3}$ by $2^{d-1}$, we get the desired result.
  have h_mul : 6 * d ^ 2 * 2 ^ (d - 1) ≤ 2 ^ (d + 3) * 2 ^ (d - 1) := by
    gcongr;
    exact six_dsq_le d hd;
  exact h_mul.trans_eq ( by rw [ ← pow_add ] ; rw [ show 2 * d + 2 = d + 3 + ( d - 1 ) by omega ] )

/-
C_neg is bounded when all N-sets have bounded cardinality and all positions
    are less than 2^{6d+7}.
-/
lemma C_neg_le_pow (d Jb Dd : ℕ) (hd : 9 ≤ d)
    (hJbDd : Jb + Dd ≤ 6 * d ^ 2)
    (Y W : ℕ) (hW : W = 2 ^ (5 * d + 2))
    (hY : Y ≤ 6 * d * (W + 2) + 1)
    (Nu : Fin Jb → Finset ℕ) (Nv : Fin Dd → Finset ℕ)
    (hNu_card : ∀ j, (Nu j).card ≤ 2 ^ (d - 1))
    (hNu_bound : ∀ j, ∀ v ∈ Nu j, v < W)
    (hNv_card : ∀ i, (Nv i).card ≤ 2 ^ (d - 1))
    (hNv_bound : ∀ i, ∀ v ∈ Nv i, v < W) :
    (∑ j : Fin Jb, ∑ v ∈ Nu j, ((↑Y + ↑j.val * (↑W + 1) : ℤ) + ↑v) ^ d +
     ∑ i : Fin Dd, ∑ v ∈ Nv i, ((↑Y + (↑Jb + ↑i.val) * (↑W + 1) : ℤ) + ↑v) ^ d)
      ≤ 2 ^ (6 * d ^ 2 + 9 * d + 3) := by
  have h_sum_bound : ∀ j : Fin Jb, ∑ v ∈ Nu j, (Y + (j : ℕ) * (W + 1) + v : ℤ) ^ d ≤ 2 ^ (d - 1) * (2 ^ (6 * d + 7) - 1) ^ d := by
    intro j
    have h_sum_bound : ∀ v ∈ Nu j, (Y + (j : ℕ) * (W + 1) + v : ℤ) ^ d ≤ (2 ^ (6 * d + 7) - 1) ^ d := by
      intro v hv
      have h_pos : Y + (j : ℕ) * (W + 1) + v < 2 ^ (6 * d + 7) := by
        convert bank_max_position_bound d hd Y W hW hY ( j : ℕ ) ( by linarith [ Fin.is_lt j ] ) v ( hNu_bound j v hv ) using 1;
      exact pow_le_pow_left₀ ( by positivity ) ( by linarith ) _;
    refine' le_trans ( Finset.sum_le_sum h_sum_bound ) _ ; norm_num [ hNu_card j ];
    exact mul_le_mul_of_nonneg_right ( mod_cast hNu_card j ) ( pow_nonneg ( sub_nonneg_of_le ( one_le_pow₀ ( by norm_num ) ) ) _ );
  have h_sum_bound_v : ∀ i : Fin Dd, ∑ v ∈ Nv i, (Y + (Jb + i : ℕ) * (W + 1) + v : ℤ) ^ d ≤ 2 ^ (d - 1) * (2 ^ (6 * d + 7) - 1) ^ d := by
    intros i
    have h_sum_bound_v_i : ∀ v ∈ Nv i, (Y + (Jb + i : ℕ) * (W + 1) + v : ℤ) ^ d ≤ (2 ^ (6 * d + 7) - 1) ^ d := by
      intros v hv
      have h_pos : Y + (Jb + i : ℕ) * (W + 1) + v < 2 ^ (6 * d + 7) := by
        apply bank_max_position_bound d hd Y W hW hY (Jb + i) (by
        linarith [ Fin.is_lt i ]) v (hNv_bound i v hv);
      exact pow_le_pow_left₀ ( by positivity ) ( by exact le_tsub_of_add_le_right ( mod_cast h_pos ) ) _;
    refine' le_trans ( Finset.sum_le_sum h_sum_bound_v_i ) _ ; norm_num [ mul_comm ];
    exact mul_le_mul_of_nonneg_right ( mod_cast hNv_card i ) ( pow_nonneg ( sub_nonneg_of_le ( one_le_pow₀ ( by norm_num ) ) ) _ );
  have h_sum_bound_total : (Jb + Dd) * 2 ^ (d - 1) * (2 ^ (6 * d + 7) - 1) ^ d ≤ 2 ^ (6 * d ^ 2 + 9 * d + 3) := by
    have h_sum_bound_total : (Jb + Dd) * 2 ^ (d - 1) ≤ 2 ^ (2 * d + 2) := by
      exact le_trans ( Nat.mul_le_mul_right _ hJbDd ) ( neg_count_bound d hd );
    refine le_trans ( Nat.mul_le_mul_right _ h_sum_bound_total ) ?_;
    refine' le_trans ( Nat.mul_le_mul_left _ ( Nat.pow_le_pow_left ( Nat.sub_le _ _ ) _ ) ) _;
    rw [ ← pow_mul ] ; ring_nf ; norm_num;
  refine le_trans ?_ ( Nat.cast_le.mpr h_sum_bound_total );
  convert add_le_add ( Finset.sum_le_sum fun j _ => h_sum_bound j ) ( Finset.sum_le_sum fun i _ => h_sum_bound_v i ) using 1 ; norm_num ; ring

/-
For d ≥ 9, if a*n < a*Vn*2^Dd + M + K + 1 and M + K ≤ 2^{3d²+2d+1},
    then n < 2^Dd * 2^Jb.
-/
lemma n_upper_bound_helper (d : ℕ) (hd : 9 ≤ d)
    (a n Vn : ℕ) (ha : 0 < a) (M K : ℤ)
    (Dd : ℕ) (hDd : Dd = d * (d - 1) / 2)
    (Jb : ℕ) (hJb : Jb = 4 * d ^ 2 + 1)
    (h_an : (a : ℤ) * n < (a : ℤ) * Vn * 2 ^ Dd + M + K + 1)
    (hMK : M + K ≤ 2 ^ (3 * d ^ 2 + 2 * d + 1))
    (hVn_lt : Vn < 2 ^ (d * (d + 1) / 2)) :
    n < 2 ^ Dd * 2 ^ Jb := by
  -- By dividing both sides of the inequality $a * n < a * Vn * 2^Dd + M + K + 1$ by $a$, we get $n < Vn * 2^Dd + (M + K + 1) / a$.
  have h_div : n < Vn * 2^Dd + (2^(3*d^2 + 2*d + 1) + 1) := by
    nlinarith [ pow_pos ( zero_lt_two' ℤ ) ( 3 * d ^ 2 + 2 * d + 1 ) ];
  -- We'll use that $Dd + Jb = d*(d-1)/2 + 4d^2 + 1$ and simplify the exponent.
  have h_exp : Dd + Jb ≥ 3 * d^2 + 2 * d + 2 := by
    nlinarith only [ hd, hDd, hJb, Nat.div_add_mod ( d * ( d - 1 ) ) 2, Nat.mod_lt ( d * ( d - 1 ) ) two_pos, Nat.sub_add_cancel ( by linarith : 1 ≤ d ) ];
  -- By combining the inequalities, we get $n < 2^{d^2} + 2^{3d^2 + 2d + 2}$.
  have h_combined : n < 2^(d^2) + 2^(3*d^2 + 2*d + 1) + 1 := by
    have h_combined : Vn * 2^Dd < 2^(d^2) := by
      convert Nat.mul_lt_mul_of_pos_right hVn_lt ( pow_pos ( by decide : 0 < 2 ) Dd ) using 1 ; rw [ hDd ] ; ring_nf;
      rw [ ← pow_add, show ( d + d ^ 2 ) / 2 + d * ( d - 1 ) / 2 = d ^ 2 by nlinarith only [ Nat.div_mul_cancel ( show 2 ∣ d + d ^ 2 from even_iff_two_dvd.mp ( by simp +arith +decide [ parity_simps ] ) ), Nat.div_mul_cancel ( show 2 ∣ d * ( d - 1 ) from even_iff_two_dvd.mp ( by rcases d with ( _ | _ | d ) <;> simp +arith +decide [ mul_add, parity_simps ] ) ), Nat.sub_add_cancel ( by linarith : 1 ≤ d ) ] ];
    grind;
  refine lt_of_lt_of_le h_combined ?_;
  rw [ ← pow_add ];
  refine' le_trans _ ( pow_le_pow_right₀ ( by decide ) h_exp );
  ring_nf;
  nlinarith only [ show 2 ^ ( d * 2 ) > 0 by positivity, show 2 ^ ( d ^ 2 * 3 ) > 0 by positivity, show 2 ^ d ^ 2 > 0 by positivity, show 2 ^ ( d * 2 ) * 2 ^ ( d ^ 2 * 3 ) > 2 ^ d ^ 2 by exact lt_of_lt_of_le ( pow_lt_pow_right₀ ( by decide ) ( by nlinarith only [ hd ] ) ) ( Nat.le_mul_of_pos_left _ ( by positivity ) ) ]

set_option maxHeartbeats 3200000 in
/-- For d ≥ 9, there exists I and C₀ ≤ 2^{6d²+9d+5}
    such that I represents [C₀, C₀+K) and the doubling condition holds. -/
theorem improved_seed_interval (d : ℕ) (hd : 9 ≤ d) :
    let p := monomialPoly d
    let T₀ := explicitTailParam p 1
    let K := (p.eval (T₀ : ℤ)).toNat
    ∃ (I : Finset ℕ) (C₀ : ℤ),
      (∀ i ∈ I, T₀ + 1 ≤ i) ∧
      RepresentsInterval (fun j => p.eval (j : ℤ)) I C₀ K ∧
      (∀ u v : ℕ, T₀ ≤ u → u ∉ I → v ∉ I → u < v →
        (∀ w, u < w → w < v → w ∈ I) → p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ)) ∧
      C₀.toNat ≤ 2 ^ (6 * d ^ 2 + 9 * d + 5) := by
  set p := monomialPoly d with hp_def
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hA : 0 < p.leadingCoeff := monomialPoly_leadingCoeff_pos d hd1
  have hd_nat : 1 ≤ p.natDegree := monomialPoly_natDegree_pos d hd1
  have hnd : p.natDegree = d := monomialPoly_natDegree d hd1
  set a := d.factorial with ha_def
  have ha_pos : 0 < a := Nat.factorial_pos d
  have ha_eq : (a : ℤ) = polyA p := by rw [ha_def, hp_def, monomialPoly_polyA d hd1]
  set R := smallEmaxDatum d with hR_def
  have hR_eMax : R.eMax = 4 ^ d := smallEmaxDatum_eMax d hd1
  have hE_pos : ∀ e ∈ R.E, 1 ≤ e := smallEmaxDatum_ePos d
  set T₀ := explicitTailParam p 1 with hT₀_def
  have hT₀_tau : TauProp p 1 T₀ := explicit_tau_bound p 1 hA hd_nat
  set T_res := explicitTailParam p (R.eMax + 1) with hT_res_def
  have hT_res_tau : TauProp p (R.eMax + 1) T_res := explicit_tau_bound p (R.eMax + 1) hA hd_nat
  have hT₀_le_res : T₀ ≤ T_res := explicitTailParam_mono p 1 (R.eMax + 1) (by omega)
  set R₀ := T_res + 1 with hR₀_def
  set K := (p.eval (T₀ : ℤ)).toNat with hK_def
  have hT₀_pos : 0 < p.eval (T₀ : ℤ) := tauProp_pos (by omega) hT₀_tau le_rfl
  have hK_pos : 0 < K := by omega
  have hK_eq : (K : ℤ) = p.eval (T₀ : ℤ) := Int.toNat_of_nonneg (le_of_lt hT₀_pos)
  set F : Fin a → Finset ℕ := shiftedF d hd1 R₀ with hF_def
  have hF_sub : ∀ r, F r ⊆ R.E := fun r => shiftedF_sub d hd1 R₀ r
  have hp_eval : ∀ x : ℤ, p.eval x = x ^ d := by intro x; simp [hp_def, monomialPoly]
  have hR₀_nonneg : ∀ r : Fin a, 0 ≤ ∑ e ∈ F r, p.eval ((↑R₀ : ℤ) + ↑e) := by
    intro r; exact Finset.sum_nonneg fun e he => le_of_lt
      (tauProp_pos (by omega) hT₀_tau (by omega : T₀ ≤ R₀ + e))
  have hR₀_cong : ∀ r : Fin a,
      (a : ℤ) ∣ (∑ e ∈ F r, p.eval ((↑R₀ : ℤ) + ↑e) - ↑(r : ℕ)) := by
    intro r; have h := shiftedF_cong d hd1 R₀ r
    convert h using 2; apply Finset.sum_congr rfl
    intro e _; simp [hp_def, monomialPoly]
  set k : Fin a → ℤ := fun r => ∑ e ∈ F r, p.eval ((↑R₀ : ℤ) + ↑e) with hk_def
  set M : ℤ := Finset.univ.sup' ⟨⟨0, ha_pos⟩, Finset.mem_univ _⟩ k with hM_def
  have hM_nn : 0 ≤ M :=
    Finset.le_sup'_of_le k (Finset.mem_univ ⟨0, ha_pos⟩) (hR₀_nonneg ⟨0, ha_pos⟩)
  have h_pos : ∀ n : ℕ, T₀ ≤ n → 0 < p.eval (n : ℤ) :=
    fun n hn => tauProp_pos (by omega) hT₀_tau hn
  -- ── Bank-specific parameters ────────────────────────────────────────────
  set W := 2 ^ (5 * d + 2) with hW_def
  set Dd := d * (d - 1) / 2 with hDd_def
  set Vz : ℤ := ∏ kk : Fin d, (2 ^ ((kk : ℕ) + 1) - 1 : ℤ) with hVz_def
  set Vn : ℕ := ∏ kk : Fin d, (2 ^ ((kk : ℕ) + 1) - 1 : ℕ) with hVn_def
  have hVn_pos : 0 < Vn := Finset.prod_pos fun kk _ => Nat.sub_pos_of_lt (one_lt_pow₀ one_lt_two (by omega))
  have hVn_odd : Odd Vn := V_d_odd d
  set Jb := 4 * d ^ 2 + 1 with hJb_def
  set T_blk := explicitTailParam p (W + 2) with hT_blk_def
  have hT_blk_tau : TauProp p (W + 2) T_blk := explicit_tau_bound p (W + 2) hA hd_nat
  have hT₀_le_blk : T₀ ≤ T_blk := explicitTailParam_mono p 1 (W + 2) (by simp [hW_def])
  set Y := max (R₀ + R.eMax + 2) (T_blk + 1) with hY_def
  have hY_res : R₀ + R.E.sup id + 2 ≤ Y := by
    show R₀ + R.E.sup id + 2 ≤ max (R₀ + R.eMax + 2) (T_blk + 1)
    simp only [ResidueDatum.eMax]; exact le_max_left _ _
  have hY_blk : T_blk + 1 ≤ Y := le_max_right _ _
  -- ── Get blocks ──────────────────────────────────────────────────────────
  have h_u_ex : ∀ j : Fin Jb, ∃ P N : Finset ℕ,
      Disjoint P N ∧ (∀ u ∈ P ∪ N, u < W) ∧ N.card ≤ 2 ^ (d - 1) ∧
      (∀ x : ℤ, ∑ u ∈ P, (x + (↑u : ℤ)) ^ d -
        ∑ v ∈ N, (x + (↑v : ℤ)) ^ d =
        (d.factorial : ℤ) * 2 ^ (Dd + j.val)) :=
    fun ⟨j, hj⟩ => u_block_exists d j hd1 (by omega)
  choose Pu Nu hu using h_u_ex
  have h_v_ex : ∀ i : Fin Dd, ∃ P N : Finset ℕ,
      Disjoint P N ∧ (∀ u ∈ P ∪ N, u < W) ∧ N.card ≤ 2 ^ (d - 1) ∧
      (∀ x : ℤ, ∑ u ∈ P, (x + (↑u : ℤ)) ^ d -
        ∑ v ∈ N, (x + (↑v : ℤ)) ^ d =
        (d.factorial : ℤ) * Vz * 2 ^ i.val) :=
    fun ⟨i, hi⟩ => v_block_exists d i hd1 (by omega)
  choose Pv Nv hv using h_v_ex
  -- ── Define I ────────────────────────────────────────────────────────────
  set I_res := R.E.image (R₀ + ·)
  set I_u := (Finset.univ : Finset (Fin Jb)).biUnion fun j =>
    (Pu j ∪ Nu j).image (Y + j.val * (W + 1) + ·)
  set I_v := (Finset.univ : Finset (Fin Dd)).biUnion fun i =>
    (Pv i ∪ Nv i).image (Y + (Jb + i.val) * (W + 1) + ·)
  set I := I_res ∪ (I_u ∪ I_v) with hI_def
  -- ── Define C₀ ───────────────────────────────────────────────────────────
  set C_neg : ℤ :=
    ∑ j : Fin Jb, ∑ v ∈ Nu j, ((↑Y + ↑j.val * (↑W + 1) : ℤ) + ↑v) ^ d +
    ∑ i : Fin Dd, ∑ v ∈ Nv i, ((↑Y + (↑Jb + ↑i.val) * (↑W + 1) : ℤ) + ↑v) ^ d
  set aBz : ℤ := ↑(a : ℕ) * Vz * (2 : ℤ) ^ Dd
  set C₀ := C_neg + aBz + M - ↑(a : ℕ) + 1 with hC₀_def
  -- ── Provide the witness ─────────────────────────────────────────────────
  have hCond1 : ∀ i ∈ I, T₀ + 1 ≤ i := by
    simp +zetaDelta at *;
    rintro i ( ⟨ a, ha, rfl ⟩ | ⟨ a, b, hb, rfl ⟩ | ⟨ a, b, hb, rfl ⟩ );
    · linarith [ hE_pos a ha ];
    · exact lt_add_of_lt_of_nonneg ( lt_add_of_lt_of_nonneg ( lt_max_of_lt_left ( by linarith ) ) ( Nat.zero_le _ ) ) ( Nat.zero_le _ );
    · exact lt_add_of_lt_of_nonneg ( lt_add_of_lt_of_nonneg ( lt_max_of_lt_left ( by linarith ) ) ( Nat.zero_le _ ) ) ( Nat.zero_le _ )
  -- Condition 4: bound
  have hCond4 : C₀.toNat ≤ 2 ^ (6 * d ^ 2 + 9 * d + 5) := by
    rw [Int.toNat_le]
    -- Step 1: Bound M
    have hT_res_eq : T_res = 6 * d * (R.eMax + 1) := by
      rw [hT_res_def, hp_def]; exact monomial_tau_eq' d _ (by omega) (by omega)
    have hR₀_le : R₀ ≤ 6 * d * (4 ^ d + 1) + 1 := by
      rw [hR₀_def, hT_res_eq, hR_eMax]
    have hM_le : M ≤ 2 ^ (3 * d ^ 2 + 2 * d) := by
      rw [← M_bound_exponent]
      exact Finset.sup'_le _ _ fun r _ => by
        rw [hk_def]; simp only [hp_eval]
        exact residue_sum_bound d hd R₀ hR₀_le (F r) (hF_sub r)
    -- Step 2: Bound aBz
    have haBz_le : aBz ≤ 2 ^ (2 * d ^ 2) := by
      convert factorial_UV_le d hd1 using 1;
      rw [ ← Int.ofNat_le ] ; norm_num [ aBz, Vz ] ; ring_nf;
      grind
    -- Step 3: Bound C_neg
    have hY_le : Y ≤ 6 * d * (W + 2) + 1 := by
      rw [ hY_def ];
      rw [ monomial_tau_eq' d ( W + 2 ) ( by linarith ) ( by linarith ) ] at *;
      rw [ hT_blk_def, max_le_iff ];
      refine' ⟨ _, le_rfl ⟩;
      rw [ hR₀_def, hT_res_eq, hR_eMax ];
      rw [ hW_def ];
      ring_nf;
      rw [ show 4 ^ d = 2 ^ ( d * 2 ) by rw [ pow_mul' ] ; norm_num ] ; ring_nf;
      nlinarith only [ hd, pow_pos ( zero_lt_two' ℕ ) ( d * 2 ), pow_le_pow_right₀ ( show 1 ≤ 2 by norm_num ) ( show d * 2 ≤ d * 5 by linarith ), pow_pos ( zero_lt_two' ℕ ) ( d * 5 ) ]
    have hC_neg_le : C_neg ≤ 2 ^ (6 * d ^ 2 + 9 * d + 3) := by
      exact C_neg_le_pow d Jb Dd hd
        (by rw [hJb_def, hDd_def]; exact block_count_le d hd1)
        Y W hW_def hY_le
        (fun j => Nu j) (fun i => Nv i)
        (fun j => (hu j).2.2.1)
        (fun j v hv => (hu j).2.1 v (Finset.mem_union_right _ hv))
        (fun i => (hv i).2.2.1)
        (fun i v hv' => (hv i).2.1 v (Finset.mem_union_right _ hv'))
    -- Step 4: Assembly
    have h_assembly := improved_bound_assembly d hd C_neg M aBz hC_neg_le haBz_le hM_le
    have ha_nn : (0 : ℤ) ≤ ↑(a : ℕ) := Nat.cast_nonneg _
    push_cast at *
    linarith
  -- Condition 3: doubling
  -- Gap position g_t is NOT in I (offset W is not < W)
  have hGap_notI : ∀ t : ℕ, Y + t * (W + 1) + W ∉ I := by
    -- Since $W$ is a power of 2 and $t$ is a natural number, $Y + t * (W + 1) + W$ is strictly greater than any element in $I$.
    intros t
    simp [I, I_res, I_u, I_v];
    refine' ⟨ _, _, _ ⟩;
    · intro x hx
      have h_bound : x ≤ R.eMax := by
        exact Finset.le_sup ( f := id ) hx;
      grind;
    · intro j u hu_mem hu_eq
      have h_eq : j.val * (W + 1) + u = t * (W + 1) + W := by
        linarith;
      have := congr_arg ( · % ( W + 1 ) ) h_eq ; norm_num [ Nat.add_mod, Nat.mul_mod ] at this;
      rw [ Nat.mod_eq_of_lt ] at this <;> linarith [ hu j |>.2.1 u ( by simpa using hu_mem ) ];
    · intro i x hx H;
      nlinarith only [ H, show t = Jb + i from by nlinarith only [ H, show x < W from by cases hx <;> [ exact hv i |>.2.1 _ ( Finset.mem_union_left _ ‹_› ) ; exact hv i |>.2.1 _ ( Finset.mem_union_right _ ‹_› ) ], show W > 0 from by positivity ], show x < W from by cases hx <;> [ exact hv i |>.2.1 _ ( Finset.mem_union_left _ ‹_› ) ; exact hv i |>.2.1 _ ( Finset.mem_union_right _ ‹_› ) ], show W > 0 from by positivity ]
  have hCond3 : ∀ u v : ℕ, T₀ ≤ u → u ∉ I → v ∉ I → u < v →
      (∀ w, u < w → w < v → w ∈ I) → p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ) := by
    intro u v hu huI hvI huv hbetween
    -- Case 1: v = u + 1
    by_cases hv1 : v = u + 1
    · exact hv1 ▸ (hT₀_tau u (u + 1) hu (by omega) (by omega)).2.2
    -- Case 2: u + 1 < Y (residue region)
    · by_cases huY : u + 1 < Y
      · -- Gap is at most R.eMax + 1, use hT_res_tau
        have hv_gap : v ≤ u + R.E.sup id + 1 := by
          apply Classical.byContradiction
          intro h_contra;
          have hw' : u + 1 ∈ I_res := by
            have := hbetween ( u + 1 ) ( by linarith ) ( by omega ) ; simp +decide [ hI_def ] at this;
            rcases this with ( h | h | h );
            · exact h;
            · simp +zetaDelta at *;
              bv_omega;
            · obtain ⟨ i, hi, hi' ⟩ := Finset.mem_biUnion.mp h;
              obtain ⟨ x, hx, hx' ⟩ := Finset.mem_image.mp hi';
              nlinarith only [ huY, hx', show ( Jb : ℕ ) + i ≥ 1 from Nat.succ_le_of_lt ( by positivity ), show ( W : ℕ ) + 1 > 0 from Nat.succ_pos _, show ( x : ℕ ) ≥ 0 from Nat.zero_le _ ]
          have hw'_lt : u + 1 < Y := by
            exact huY
          have hw'_not_in_I : R₀ + R.E.sup id + 1 ∉ I := by
            simp [hI_def, I_res, I_u, I_v];
            refine' ⟨ _, _, _ ⟩;
            · exact fun x hx => by linarith [ show x ≤ R.E.sup id from Finset.le_sup ( f := id ) hx ] ;
            · bv_omega;
            · intro i x hx;
              nlinarith only [ hY_res, hY_blk, show ( i : ℕ ) < Dd from i.2, show ( Jb : ℕ ) ≥ 1 from Nat.succ_pos _, show ( W : ℕ ) ≥ 1 from Nat.one_le_pow _ _ ( by decide ), show ( x : ℕ ) < W from by cases hx <;> [ exact hv i |>.2.1 _ ( Finset.mem_union_left _ ‹_› ) ; exact hv i |>.2.1 _ ( Finset.mem_union_right _ ‹_› ) ] ]
          have hw'_between : u < R₀ + R.E.sup id + 1 ∧ R₀ + R.E.sup id + 1 < v := by
            have hw'_lt : u + 1 ≤ R₀ + R.E.sup id := by
              rw [ Finset.mem_image ] at hw' ; obtain ⟨ x, hx, hx' ⟩ := hw' ; linarith [ show x ≤ R.E.sup id from Finset.le_sup ( f := id ) hx ] ;
            grind
          have hw'_in_I : R₀ + R.E.sup id + 1 ∈ I := by
            exact hbetween _ hw'_between.1 hw'_between.2
          contradiction
        have hu_ge_Tres : T_res ≤ u := by
          contrapose! hbetween;
          use u + 1;
          refine' ⟨ Nat.lt_succ_self _, lt_of_le_of_ne huv ( Ne.symm hv1 ), _ ⟩;
          -- Since $u + 1 < Y$, it cannot be in $I_u$ or $I_v$ because those elements are at least $Y$.
          have h_not_in_Iu_Iv : u + 1 ∉ I_u ∧ u + 1 ∉ I_v := by
            constructor <;> intro h <;> obtain ⟨ j, hj ⟩ := Finset.mem_biUnion.mp h <;> obtain ⟨ x, hx ⟩ := Finset.mem_image.mp hj.2 <;> simp +decide at hx ⊢;
            · nlinarith only [ huY, hx.2, show ( j : ℕ ) ≥ 0 by positivity, show ( x : ℕ ) ≥ 0 by positivity ];
            · nlinarith only [ huY, hx.2, show ( Jb : ℕ ) ≥ 1 by exact Nat.succ_pos _, show ( W : ℕ ) ≥ 1 by exact Nat.one_le_pow _ _ ( by decide ), show ( x : ℕ ) ≥ 0 by exact Nat.zero_le _ ];
          grind +splitIndPred
        exact (hT_res_tau u v hu_ge_Tres huv hv_gap).2.2
      -- Case 3: Y ≤ u + 1 (block region)
      · push_neg at huY
        -- Gap position g_t = Y + t*(W+1) + W where t = (u+1-Y)/(W+1)
        -- Satisfies u < g_t ≤ u + W + 1, and g_t ∉ I
        have hv_gap : v ≤ u + (W + 2) := by
          contrapose! hGap_notI;
          use (u + 1 - Y) / (W + 1);
          refine' hbetween _ _ _;
          · linarith [ Nat.div_add_mod ( u + 1 - Y ) ( W + 1 ), Nat.mod_lt ( u + 1 - Y ) ( by positivity : 0 < W + 1 ), Nat.sub_add_cancel ( by linarith : Y ≤ u + 1 ) ];
          · linarith [ Nat.div_mul_le_self ( u + 1 - Y ) ( W + 1 ), Nat.sub_add_cancel ( by linarith : Y ≤ u + 1 ) ]
        have hu_ge_Tblk : T_blk ≤ u := by omega
        exact (hT_blk_tau u v hu_ge_Tblk huv hv_gap).2.2
  -- Condition 2: RepresentsInterval
  -- For each N, find r with k_r ≡ N - C_neg mod a, then decompose quotient via binary_coverage
  -- Cast lemma: (Vn : ℤ) = Vz
  have hVn_cast : (Vn : ℤ) = Vz := by
    simp only [Vn, Vz]; push_cast
    exact Finset.prod_congr rfl fun kk _ => by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; push_cast; ring
  -- Block identities in terms of p.eval
  have hu_block : ∀ j : Fin Jb, ∀ x : ℤ,
      ∑ u ∈ Pu j, p.eval (x + ↑u) - ∑ v ∈ Nu j, p.eval (x + ↑v) =
      (a : ℤ) * 2 ^ (Dd + j.val) := by
    intro j x; simp only [hp_eval]; exact (hu j).2.2.2 x
  have hv_block : ∀ i : Fin Dd, ∀ x : ℤ,
      ∑ u ∈ Pv i, p.eval (x + ↑u) - ∑ v ∈ Nv i, p.eval (x + ↑v) =
      (a : ℤ) * Vz * 2 ^ i.val := by
    intro i x; simp only [hp_eval]; exact (hv i).2.2.2 x
  -- M is a sup of k
  have hk_le_M : ∀ r : Fin a, k r ≤ M :=
    fun r => Finset.le_sup' k (Finset.mem_univ r)
  have hCond2 : RepresentsInterval (fun j => p.eval (j : ℤ)) I C₀ K := by
    intro N hN₁ hN₂
    -- Step 1: Find r with k r ≡ N - C_neg (mod a)
    obtain ⟨r, hr_cong, hr_le⟩ : ∃ r : Fin a, k r ≡ N - C_neg [ZMOD a] ∧ k r ≤ M := by
      have h_cong : ∀ s : Fin a, ∃ r : Fin a, k r ≡ s.val [ZMOD a] := by
        exact fun s => ⟨ s, Int.ModEq.symm <| Int.modEq_of_dvd <| hR₀_cong s ⟩;
      exact Exists.elim ( h_cong ⟨ Int.toNat ( ( N - C_neg ) % a ), by linarith [ Int.emod_lt_of_pos ( N - C_neg ) ( by positivity : 0 < ( a : ℤ ) ), Int.toNat_of_nonneg ( Int.emod_nonneg ( N - C_neg ) ( by positivity : ( a : ℤ ) ≠ 0 ) ) ] ⟩ ) fun r hr => ⟨ r, by simpa [ Int.ModEq, Int.emod_nonneg _ ( by positivity : ( a : ℤ ) ≠ 0 ) ] using hr, hk_le_M r ⟩
    -- Step 2: divisibility and quotient
    have hdvd : (a : ℤ) ∣ (N - C_neg - k r) := by
      exact hr_cong.dvd
    have hVz_pos : 0 < Vz := by rw [← hVn_cast]; exact_mod_cast hVn_pos
    have haBz_ge_a : (a : ℤ) ≤ aBz := by
      show (a : ℤ) ≤ ↑a * Vz * 2 ^ Dd
      have h2Dd : (1 : ℤ) ≤ 2 ^ Dd := by exact_mod_cast Nat.one_le_pow Dd 2 (by norm_num)
      have : (1 : ℤ) ≤ Vz * 2 ^ Dd := by nlinarith
      have : (0 : ℤ) ≤ ↑a := by exact_mod_cast Nat.zero_le a
      nlinarith
    have hN_ge : 0 ≤ N - C_neg - k r := by linarith [hC₀_def, haBz_ge_a]
    set n := Int.toNat ((N - C_neg - k r) / a) with hn_def
    have ha_pos_z : (0 : ℤ) < a := by exact_mod_cast ha_pos
    have hn_eq : N - C_neg - k r = a * n := by
      rw [hn_def, Int.toNat_of_nonneg (Int.ediv_nonneg hN_ge (le_of_lt ha_pos_z))]
      linarith [Int.ediv_mul_cancel hdvd]
    -- Step 3: Show n is in range for binary_coverage
    have hn_lower : Vn * 2 ^ Dd ≤ n := by
      -- Substitute hn_eq into hN_ge and simplify.
      have h_simplified : a * Vn * 2 ^ Dd ≤ a * n + a := by
        grind;
      by_contra h_contra;
      have h_eq : a * Vn * 2 ^ Dd = a * n + a := by
        exact le_antisymm h_simplified ( by nlinarith only [ h_contra, ha_pos ] );
      grind
    -- Bound for Vn
    have hVn_lt : Vn < 2 ^ (d * (d + 1) / 2) := by
      have hVz_lt : ∏ i : Fin d, (2 ^ ((i : ℕ) + 1) - 1) < ∏ i : Fin d, 2 ^ ((i : ℕ) + 1) := by
        apply Finset.prod_lt_prod;
        · exact fun i _ => Nat.sub_pos_of_lt ( one_lt_pow₀ one_lt_two ( Nat.succ_ne_zero _ ) );
        · exact fun _ _ => Nat.sub_le _ _;
        · exact ⟨ ⟨ 0, by linarith ⟩, Finset.mem_univ _, Nat.sub_lt ( by norm_num ) ( by norm_num ) ⟩;
      convert hVz_lt using 1;
      rw [ Finset.prod_pow_eq_pow_sum ];
      exact congr_arg _ ( Nat.div_eq_of_eq_mul_left zero_lt_two <| Nat.recOn d ( by norm_num ) fun n ih => by norm_num [ Fin.sum_univ_castSucc ] at * ; linarith )
    -- Bound for M + K
    have hMK_bound : M + (K : ℤ) ≤ 2 ^ (3 * d ^ 2 + 2 * d + 1) := by
      have hM_le : M ≤ 2 ^ (3 * d ^ 2 + 2 * d) := by
        have hM_le : ∀ r : Fin a, k r ≤ 2 ^ (3 * d ^ 2 + 2 * d) := by
          intros r
          have h_sum_bound : ∑ e ∈ F r, ((R₀ : ℤ) + e) ^ d ≤ (4 ^ d : ℤ) * (8 ^ d : ℤ) ^ d := by
            convert residue_sum_bound d hd R₀ _ ( F r ) ( hF_sub r ) using 1;
            rw [ hR₀_def, hT_res_def, hR_eMax ];
            rw [ monomial_tau_eq' ] <;> norm_num ; linarith [ pow_pos ( by decide : 0 < 4 ) d ] ;
          convert h_sum_bound using 1;
          · exact Finset.sum_congr rfl fun _ _ => hp_eval _ ▸ rfl;
          · norm_num [ pow_add, pow_mul ] ; ring;
        exact Finset.sup'_le _ _ fun x hx => hM_le x;
      have hK_le : K ≤ 2 ^ (d ^ 2 + 3 * d) := by
        have hK_le : K = (6 * d) ^ d := by
          convert monomial_K_value d hd2 K _;
          convert hK_eq using 1;
        exact hK_le.symm ▸ six_d_pow_le d ( by linarith );
      -- By combining the inequalities for M and K, we get the desired bound.
      have h_sum_bound : M + K ≤ 2 ^ (3 * d ^ 2 + 2 * d) + 2 ^ (d ^ 2 + 3 * d) := by
        exact add_le_add hM_le ( mod_cast hK_le );
      refine le_trans h_sum_bound ?_;
      rw [ pow_add ] ; ring_nf;
      nlinarith only [ show 2 ^ ( d * 2 ) * 2 ^ ( d ^ 2 * 3 ) > 0 by positivity, show 2 ^ ( d * 3 ) * 2 ^ d ^ 2 ≤ 2 ^ ( d * 2 ) * 2 ^ ( d ^ 2 * 3 ) by rw [ ← pow_add, ← pow_add ] ; exact pow_le_pow_right₀ ( by decide ) ( by nlinarith only [ hd ] ) ]
    have h_an_bound : (a : ℤ) * n < (a : ℤ) * Vn * 2 ^ Dd + M + K + 1 := by
      have haBz_eq : aBz = (a : ℤ) * Vn * 2 ^ Dd := by
        simp only [aBz, hVn_cast]
      linarith [hC₀_def, hR₀_nonneg r, haBz_eq]
    have hn_lt : n < 2 ^ Dd * 2 ^ Jb :=
      n_upper_bound_helper d hd a n Vn ha_pos M K Dd hDd_def Jb hJb_def h_an_bound hMK_bound hVn_lt
    have hn_upper_Q : ∃ Q : ℕ, Vn * 2 ^ Dd + Q < 2 ^ Dd * 2 ^ Jb ∧ n ≤ Vn * 2 ^ Dd + Q := by
      exact ⟨n - Vn * 2 ^ Dd, by omega, by omega⟩
    obtain ⟨Q, hQ_bound, hn_upper⟩ := hn_upper_Q
    -- Step 4: Apply binary_coverage
    obtain ⟨S_V, S_U, hn_decomp⟩ := binary_coverage Dd Jb Vn hVn_odd hVn_pos Q hQ_bound n hn_lower hn_upper
    -- Step 5: Construct J
    set J_res := (F r).image (R₀ + ·) with hJ_res_def
    set J_u := Finset.univ.biUnion fun j : Fin Jb =>
      if j ∈ S_U then (Pu j).image (Y + j.val * (W + 1) + ·)
      else (Nu j).image (Y + j.val * (W + 1) + ·)
    set J_v := Finset.univ.biUnion fun i : Fin Dd =>
      if i ∈ S_V then (Pv i).image (Y + (Jb + i.val) * (W + 1) + ·)
      else (Nv i).image (Y + (Jb + i.val) * (W + 1) + ·)
    set J := J_res ∪ (J_u ∪ J_v) with hJ_def
    use J
    refine ⟨?_, ?_⟩
    -- Step 6: J ⊆ I
    ·
      refine Finset.union_subset ( Finset.image_subset_iff.mpr ?_ ) ( Finset.union_subset ( Finset.biUnion_subset.mpr ?_ ) ( Finset.biUnion_subset.mpr ?_ ) ) <;> simp +decide [ * ];
      · exact fun x hx => Or.inl <| Finset.mem_image_of_mem _ <| hF_sub r hx;
      · intro j; split_ifs <;> simp +decide [ *, Finset.subset_iff ] ;
        · exact fun x hx => Or.inr <| Or.inl <| Finset.mem_biUnion.mpr ⟨ j, Finset.mem_univ _, Finset.mem_image.mpr ⟨ x, Finset.mem_union_left _ hx, rfl ⟩ ⟩;
        · intro x hx; exact Or.inr <| Or.inl <| Finset.mem_biUnion.mpr ⟨ j, Finset.mem_univ _, Finset.mem_image.mpr ⟨ x, by
            exact Finset.mem_union_right _ hx, rfl ⟩ ⟩ ;
      · intro i; split_ifs <;> simp +decide [ *, Finset.subset_iff ] ;
        · intro x hx; right; right; exact Finset.mem_biUnion.mpr ⟨ i, Finset.mem_univ _, Finset.mem_image.mpr ⟨ x, by
            exact Finset.mem_union_left _ hx, rfl ⟩ ⟩ ;
        · exact fun x hx => Or.inr <| Or.inr <| Finset.mem_biUnion.mpr ⟨ i, Finset.mem_univ _, Finset.mem_image.mpr ⟨ x, Finset.mem_union_right _ hx, rfl ⟩ ⟩
    -- Step 7: ∑ J = N
    · -- Rewrite p.eval as power
      simp_rw [show ∀ (n : ℕ), (fun j => p.eval (↑j : ℤ)) n = (n : ℤ) ^ d from
        fun n => by simp [hp_eval]]
      -- Disjointness
      have h_disj1 : Disjoint J_res (J_u ∪ J_v) := by
        rw [ Finset.disjoint_left ];
        -- Since $R₀ + x < Y$ for all $x \in F r$, and $Y$ is the starting point for $J_u$ and $J_v$, $J_res$ and $J_u ∪ J_v$ are disjoint.
        intros a ha
        have h_a_lt_Y : a < Y := by
          obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp ha;
          linarith [ Finset.mem_Icc.mp ( shiftedF_sub d hd1 R₀ r hx ), hY_res, show ( R.eMax : ℕ ) = 4 ^ d from mod_cast hR_eMax, show ( R₀ : ℕ ) + R.eMax + 2 ≤ Y from mod_cast hY_res ];
        -- Since $a < Y$ and all elements in $J_u$ and $J_v$ are at least $Y$, $a$ cannot be in $J_u$ or $J_v$.
        have h_a_not_in_Ju : a ∉ J_u := by
          simp [J_u];
          intro x hx; split_ifs at hx <;> simp +decide [ Finset.mem_image ] at hx ⊢ <;> omega;
        have h_a_not_in_Jv : a ∉ J_v := by
          simp [J_v];
          intro i; split_ifs <;> simp +decide [ Finset.mem_image ] ;
          · exact fun x hx => by nlinarith only [ h_a_lt_Y, hx, show 0 ≤ x from Nat.zero_le x, show 0 ≤ ( Jb + i : ℕ ) * ( W + 1 ) from Nat.zero_le _ ] ;
          · exact fun x hx => by nlinarith only [ h_a_lt_Y, show 0 ≤ x from Nat.zero_le x ] ;
        exact fun h => by cases Finset.mem_union.mp h <;> tauto;
      have h_disj2 : Disjoint J_u J_v := by
        simp +decide [ Finset.disjoint_left ] at *;
        simp +decide [ J_u, J_v ] at *;
        intro a j hj i hi; split_ifs at hj hi <;> simp +decide [ *, Finset.mem_image ] at hj hi ⊢;
        · obtain ⟨ x, hx₁, hx₂ ⟩ := hj
          obtain ⟨ y, hy₁, hy₂ ⟩ := hi
          have h_eq : j.val * (W + 1) + x = (Jb + i.val) * (W + 1) + y := by
            grind +extAll;
          nlinarith only [ h_eq, hu j |>.2.1 x ( Or.inl hx₁ ), hv i |>.2.1 y ( Or.inl hy₁ ), show ( j : ℕ ) < Jb from j.2, show ( i : ℕ ) < Dd from i.2, show ( Jb : ℕ ) = 4 * d ^ 2 + 1 from rfl, show ( Dd : ℕ ) = d * ( d - 1 ) / 2 from rfl ];
        · obtain ⟨ x, hx₁, hx₂ ⟩ := hj
          obtain ⟨ y, hy₁, hy₂ ⟩ := hi
          have h_eq : j.val * (W + 1) + x = (Jb + i.val) * (W + 1) + y := by
            grind +qlia;
          nlinarith only [ h_eq, hu j |>.2.1 x ( Or.inl hx₁ ), hv i |>.2.1 y ( Or.inr hy₁ ), show ( j : ℕ ) < Jb from j.2, show ( i : ℕ ) < Dd from i.2, show ( Jb : ℕ ) = 4 * d ^ 2 + 1 from rfl, show ( Dd : ℕ ) = d * ( d - 1 ) / 2 from rfl ];
        · obtain ⟨ x, hx₁, hx₂ ⟩ := hj
          obtain ⟨ y, hy₁, hy₂ ⟩ := hi
          have h_eq : j.val * (W + 1) + x = (Jb + i.val) * (W + 1) + y := by
            grind +splitImp;
          nlinarith only [ h_eq, hu j |>.2.1 x ( Or.inr hx₁ ), hv i |>.2.1 y ( Or.inl hy₁ ), Fin.is_lt j, Fin.is_lt i, show Jb > j.val from j.2 ];
        · obtain ⟨ x, hx₁, hx₂ ⟩ := hj
          obtain ⟨ y, hy₁, hy₂ ⟩ := hi
          have h_eq : j.val * (W + 1) + x = (Jb + i.val) * (W + 1) + y := by
            grind +qlia;
          nlinarith only [ h_eq, hu j |>.2.1 x ( Or.inr hx₁ ), hv i |>.2.1 y ( Or.inr hy₁ ), show ( j : ℕ ) < Jb from j.2, show ( i : ℕ ) < Dd from i.2, show ( Jb : ℕ ) + i ≥ Jb from Nat.le_add_right _ _ ]
      -- Split the sum
      rw [hJ_def, Finset.sum_union h_disj1, Finset.sum_union h_disj2]
      -- Sum over J_res = k r
      have h_sum_J_res : ∑ j ∈ J_res, (j : ℤ) ^ d = k r := by
        simp only [J_res, Finset.sum_image
          (fun a _ b _ h => by omega : ∀ a ∈ F r, ∀ b ∈ F r, R₀ + a = R₀ + b → a = b)]
        simp only [hk_def, hp_eval]
        exact Finset.sum_congr rfl fun e _ => by push_cast; ring_nf
      -- Sum over J_u
      have h_sum_J_u : ∑ j ∈ J_u, (j : ℤ) ^ d =
          ∑ j : Fin Jb, ∑ v ∈ Nu j, ((↑Y + ↑j.val * (↑W + 1) : ℤ) + ↑v) ^ d +
          ∑ j ∈ S_U, (a : ℤ) * 2 ^ (Dd + j.val) := by
            rw [ Finset.sum_biUnion ];
            · rw [ Finset.sum_congr rfl fun j hj => ?_ ];
              any_goals exact fun j => if j ∈ S_U then ∑ u ∈ Pu j, ( Y + j * ( W + 1 ) + u : ℤ ) ^ d else ∑ u ∈ Nu j, ( Y + j * ( W + 1 ) + u : ℤ ) ^ d;
              · simp +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_not ];
                rw [ add_comm, ← Finset.sum_congr rfl fun x hx => ?_ ];
                any_goals exact fun j => ∑ u ∈ Nu j, ( Y + j * ( W + 1 ) + u : ℤ ) ^ d;
                · rw [ sub_add_eq_add_sub, sub_eq_iff_eq_add ];
                  rw [ add_assoc, ← Finset.sum_add_distrib ];
                  refine' congr rfl ( Finset.sum_congr rfl fun x hx => _ );
                  have := hu_block x ( Y + x * ( W + 1 ) ) ; simp +decide [ hp_eval ] at this ⊢; linarith;
                · convert rfl;
              · split_ifs <;> simp +decide [ *, Finset.sum_image ];
            · intros i hi j hj hij; simp +decide [ Finset.disjoint_left ] at *; (
              intro x hx hy; split_ifs at hx hy <;> simp +decide at hx hy ⊢;
              · obtain ⟨ a, ha, rfl ⟩ := hx; obtain ⟨ b, hb, hab ⟩ := hy; simp +decide [ Fin.ext_iff ] at hij; (
                exact hij ( by nlinarith only [ hab, hu i |>.2.1 a ( Or.inl ha ), hu j |>.2.1 b ( Or.inl hb ), hW_def, pow_pos ( zero_lt_two' ℕ ) ( 5 * d + 2 ) ] ));
              · obtain ⟨ a, ha, rfl ⟩ := hx; obtain ⟨ b, hb, hab ⟩ := hy; simp +decide [ Fin.ext_iff ] at *;
                exact hij ( by nlinarith only [ hab, hu i |>.2.1 a ( Or.inl ha ), hu j |>.2.1 b ( Or.inr hb ), hW_def, pow_pos ( zero_lt_two' ℕ ) ( 5 * d + 2 ) ] );
              · obtain ⟨ a, ha₁, ha₂ ⟩ := hx; obtain ⟨ b, hb₁, hb₂ ⟩ := hy; simp +decide [ Fin.ext_iff ] at *;
                exact hij ( by nlinarith only [ ha₂, hb₂, hu i |>.2.1 a ( Or.inr ha₁ ), hu j |>.2.1 b ( Or.inl hb₁ ), hW_def, pow_pos ( zero_lt_two' ℕ ) ( 5 * d + 2 ) ] );
              · obtain ⟨ a, ha₁, ha₂ ⟩ := hx; obtain ⟨ b, hb₁, hb₂ ⟩ := hy; simp +decide [ Fin.ext_iff ] at *;
                exact hij ( by nlinarith only [ ha₂, hb₂, hu i |>.2.1 a ( Or.inr ha₁ ), hu j |>.2.1 b ( Or.inr hb₁ ), hW_def, pow_pos ( zero_lt_two' ℕ ) ( 5 * d + 2 ) ] ));
      -- Sum over J_v
      have h_sum_J_v : ∑ j ∈ J_v, (j : ℤ) ^ d =
          ∑ i : Fin Dd, ∑ v ∈ Nv i, ((↑Y + (↑Jb + ↑i.val) * (↑W + 1) : ℤ) + ↑v) ^ d +
          ∑ i ∈ S_V, (a : ℤ) * Vz * 2 ^ i.val := by
            rw [ Finset.sum_biUnion ];
            · rw [ Finset.sum_congr rfl fun i hi => ?_ ];
              any_goals exact fun i => if i ∈ S_V then ∑ u ∈ Pv i, (Y + (Jb + i.val) * (W + 1) + u : ℤ) ^ d else ∑ v ∈ Nv i, (Y + (Jb + i.val) * (W + 1) + v : ℤ) ^ d;
              · simp +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_not ];
                rw [ show ∑ x ∈ S_V, ∑ u ∈ Pv x, ( Y + ( Jb + x.val ) * ( W + 1 ) + u : ℤ ) ^ d = ∑ x ∈ S_V, ( ∑ v ∈ Nv x, ( Y + ( Jb + x.val ) * ( W + 1 ) + v : ℤ ) ^ d + a * Vz * 2 ^ ( x : ℕ ) ) from Finset.sum_congr rfl fun x hx => ?_ ] ; ring_nf;
                · norm_num [ Finset.sum_add_distrib ] ; ring_nf;
                · convert hv_block x using 1;
                  constructor <;> intro h;
                  · convert hv_block x using 1;
                  · specialize h ( Y + ( Jb + x ) * ( W + 1 ) ) ; simp +decide [ hp_eval ] at h ⊢ ; linarith;
              · split_ifs <;> simp +decide [ *, Finset.sum_image ];
            · intro i hi j hj hij; simp +decide [ Finset.disjoint_left ] at *;
              intro x hx₁ hx₂; split_ifs at hx₁ hx₂ <;> simp +decide at hx₁ hx₂ ⊢;
              · obtain ⟨ a, ha₁, ha₂ ⟩ := hx₁
                obtain ⟨ b, hb₁, hb₂ ⟩ := hx₂
                have h_eq : (Jb + i.val) * (W + 1) + a = (Jb + j.val) * (W + 1) + b := by
                  grind;
                exact hij ( Fin.ext <| by nlinarith only [ h_eq, hv i |>.2.1 a <| Or.inl ha₁, hv j |>.2.1 b <| Or.inl hb₁ ] );
              · obtain ⟨ a, ha₁, ha₂ ⟩ := hx₁; obtain ⟨ b, hb₁, hb₂ ⟩ := hx₂; simp +decide [ Fin.ext_iff ] at *;
                exact hij ( by nlinarith only [ ha₂, hb₂, hv i |>.2.1 a ( Or.inl ha₁ ), hv j |>.2.1 b ( Or.inr hb₁ ), hW_def, pow_pos ( zero_lt_two' ℕ ) ( 5 * d + 2 ) ] );
              · obtain ⟨ a, ha₁, ha₂ ⟩ := hx₁; obtain ⟨ b, hb₁, hb₂ ⟩ := hx₂; simp +decide [ Fin.ext_iff ] at *;
                exact hij ( by nlinarith only [ ha₂, hb₂, hv i |>.2.1 a ( Or.inr ha₁ ), hv j |>.2.1 b ( Or.inl hb₁ ), hW_def, pow_pos ( zero_lt_two' ℕ ) ( 5 * d + 2 ) ] );
              · obtain ⟨ a, ha₁, ha₂ ⟩ := hx₁; obtain ⟨ b, hb₁, hb₂ ⟩ := hx₂; simp +decide [ Fin.ext_iff ] at *;
                exact hij ( by nlinarith only [ ha₂, hb₂, hv i |>.2.1 a ( Or.inr ha₁ ), hv j |>.2.1 b ( Or.inr hb₁ ), hW_def, pow_pos ( zero_lt_two' ℕ ) ( 5 * d + 2 ) ] )
      rw [h_sum_J_res, h_sum_J_u, h_sum_J_v]
      -- Now algebra: kr + (C_neg_u + extra_u) + (C_neg_v + extra_v) = N
      have h_C_neg_eq : C_neg = ∑ j : Fin Jb, ∑ v ∈ Nu j, ((↑Y + ↑j.val * (↑W + 1) : ℤ) + ↑v) ^ d +
          ∑ i : Fin Dd, ∑ v ∈ Nv i, ((↑Y + (↑Jb + ↑i.val) * (↑W + 1) : ℤ) + ↑v) ^ d := by
        simp only [C_neg]
      -- Factor the extra sums
      have h_u_extra : ∑ j ∈ S_U, (a : ℤ) * 2 ^ (Dd + j.val) =
          (a : ℤ) * (2 ^ Dd * ∑ j ∈ S_U, (2 ^ (j : ℕ) : ℤ)) := by
        simp only [← Finset.mul_sum, pow_add]
      have h_v_extra : ∑ i ∈ S_V, (a : ℤ) * Vz * 2 ^ i.val =
          (a : ℤ) * (Vz * ∑ i ∈ S_V, (2 ^ (i : ℕ) : ℤ)) := by
        simp only [← Finset.mul_sum]; ring
      rw [h_u_extra, h_v_extra]
      -- Use hn_decomp and hn_eq
      have h_an : (a : ℤ) * (2 ^ Dd * ∑ j ∈ S_U, (2 ^ (j : ℕ) : ℤ)) +
          (a : ℤ) * (Vz * ∑ i ∈ S_V, (2 ^ (i : ℕ) : ℤ)) = (a : ℤ) * n := by
        rw [← mul_add]; congr 1
        have h_decomp := hn_decomp
        rw [hVn_cast] at h_decomp
        linarith
      linarith [h_C_neg_eq, h_an, hn_eq]
  exact ⟨I, C₀, hCond1, hCond2, hCond3, hCond4⟩

/-- **Main Theorem**
For every d ≥ 9 and every N ≥ 2^{6d²+9d+5}, N can be written as a sum of distinct
d-th powers of natural numbers. -/
theorem main_theorem (d : ℕ) (hd : 9 ≤ d) :
    ∀ N : ℕ, 2 ^ (6 * d ^ 2 + 9 * d + 5) ≤ N →
      ∃ J : Finset ℕ, N = ∑ i ∈ J, i ^ d := by
  obtain ⟨I, C₀, hI_ge, hI_rep, hDoubling, hC₀⟩ := improved_seed_interval d hd
  set p := monomialPoly d with hp_def
  set T₀ := explicitTailParam p 1
  set K := (p.eval (T₀ : ℤ)).toNat
  have h_pos : ∀ n : ℕ, T₀ ≤ n → 0 < p.eval (n : ℤ) :=
    fun n hn => tauProp_pos (by omega) (explicit_tau_bound p 1
      (monomialPoly_leadingCoeff_pos d (by omega))
      (monomialPoly_natDegree_pos d (by omega))) hn
  have hK_eq : (K : ℤ) = p.eval (T₀ : ℤ) :=
    Int.toNat_of_nonneg (le_of_lt (h_pos T₀ le_rfl))
  have hThreshold : IsThreshold p C₀.toNat :=
    isThreshold_of_data p T₀ K hK_eq I C₀ hI_ge hI_rep h_pos hDoubling
  have hThreshold2 : IsThreshold p (2 ^ (6 * d ^ 2 + 9 * d + 5)) :=
    isThreshold_mono hThreshold hC₀
  intro N hN
  obtain ⟨J, _, hJ2⟩ := hThreshold2 N hN
  exact ⟨J, by simpa [hp_def, monomialPoly, ← @Nat.cast_inj ℤ] using hJ2⟩

#print axioms main_theorem
