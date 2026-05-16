import Mathlib

/-
In this file we prove that every N ≥ (200d)^(d³) can be written as a sum of
distinct d-th powers of natural numbers. This is a strengthening of a result by
Kim.

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

/-- A signed a-block for p is:
    - Sets P, N ⊆ {0, ..., L-1}, disjoint
    - ∑_{u ∈ P} p(X + u) - ∑_{v ∈ N} p(X + v) = a as polynomial identity -/
structure SignedBlock (p : Polynomial ℤ) (a : ℤ) where
  P : Finset ℕ
  N : Finset ℕ
  L : ℕ
  hP_bound : ∀ u ∈ P, u < L
  hN_bound : ∀ v ∈ N, v < L
  hBlock : ∀ x : ℤ,
    ∑ u ∈ P, p.eval (x + u) - ∑ v ∈ N, p.eval (x + v) = a

end

/-! ===== Tail Lemmas ===== -/

open Polynomial BigOperators Finset

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

/-! ===== Interval Completion =====

If a finite index set I represents K consecutive integers starting at C,
and we have an infinite sequence of positive "tail" values b(t_m) satisfying
b(t_m) ≤ K + ∑_{ν=1}^{m-1} b(t_ν), then every N ≥ C is representable.
-/

open Finset BigOperators

/-- The interval [C, C+K-1] is contained in the set of subset sums of b over I. -/
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

/-! ===== Elementary Bounds ===== -/

open Polynomial BigOperators Finset

/-! ## Elementary ratio bound

For every d ≥ 1, (1 + 1/(6d))^d ≤ 6/5. -/

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

open Polynomial BigOperators Finset

/-! ## Iterated additive difference

For h = (h₀, ..., h_{d-1}) ∈ ℕ^d,
  ∑_{ε ∈ {0,1}^d} (-1)^{d - ∑ εᵢ} p(X + ∑ εᵢhᵢ) = A·d!·∏hᵢ
as a polynomial identity in ℤ[X].

We formalize the key special case: for a single difference operator. -/

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

open Polynomial BigOperators Finset

/-! ## The explicit tail parameter -/

/-- The explicit tail parameter 𝔗_p(G) = max(6dG, ⌈4H₀(p)/A⌉). -/
noncomputable def explicitTailParam (p : Polynomial ℤ) (G : ℕ) : ℕ :=
  max (6 * p.natDegree * G) (Int.toNat ⌈(4 * Hzero p : ℚ) / p.leadingCoeff⌉)

/-! ## Coefficient bounds -/

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

/-! ## Helper lemmas for explicit tau bound -/

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
# Signed Block Construction

Construction of signed a-blocks via iterated finite differences and Bézout's identity.
-/

open Polynomial BigOperators Finset

/-! ## Inductive P/N construction

We build disjoint Finset pairs (P, N) tracking which offsets get positive
vs negative signs when expanding the iterated difference operator. -/

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

/-
# Bounded Signed Block Construction

Helper lemmas for proving that the canonical signed block has L ≤ Λ_d.
Key ingredients:
1. Elements of buildPN(canonicalR d) are < 2^d
2. Elements of buildPN(canonicalS d) are < 2^(d+1)
3. Bounded Bézout coefficients: λ+μ < 2^{d(d-1)/2+d+1}
4. Construction of signed block with L ≤ Λ_d = 2^{d(d-1)/2+2d+2}
-/

open Polynomial BigOperators Finset

noncomputable section

/-
All elements produced by buildPN with canonicalR shifts are < 2^d.
-/
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

end

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
    ∃ J : Finset ℕ, (∀ j ∈ J, 0 < p.eval (j : ℤ)) ∧
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

/-
# Height Bound Construction

Generic construction lemmas for proving IsThreshold with explicit bound tracking.
Used by height_only_bound in HeightOnlyBound.lean.
-/

open Polynomial BigOperators Finset

noncomputable section

/-! Given an initial interval I covering [C₀, C₀+K-1] with all indices ≥ T+1,
positivity of p on [T, ∞), and a doubling property for consecutive non-I elements,
every N ≥ C₀ is representable. -/

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

/-! Given a residue datum R, signed block B, and parameters R₀, Y, K,
construct the initial interval set I and threshold C₀, and prove
RepresentsInterval. -/

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

/-! ===== Height-Only Bound Definitions ===== -/

open Polynomial BigOperators Finset

noncomputable section

/-- Λ_d = 2^{d(d-1)/2 + 2d + 2}, an upper bound for the signed block parameter L. -/
def lambdaD (d : ℕ) : ℕ := 2 ^ (d * (d - 1) / 2 + 2 * d + 2)

theorem isThreshold_mono {p : Polynomial ℤ} {C C' : ℕ}
    (h : IsThreshold p C) (hle : C ≤ C') : IsThreshold p C' :=
  fun N hN => h N (le_trans hle hN)

/-! ## Canonical signed block bound

The canonical signed block B_d satisfies L ≤ Λ_d.
This requires bounding the Bézout coefficients and block element sizes.
-/

set_option maxHeartbeats 1600000 in
theorem canonical_signed_block_bound (p : Polynomial ℤ)
    (hd : 1 ≤ p.natDegree):
    ∃ B : SignedBlock p (polyA p),
      B.L ≤ lambdaD p.natDegree := by
        have := bounded_bezout_canonical p.natDegree hd;
        obtain ⟨ lam, mu, h₁, h₂ ⟩ := this
        use ⟨(Finset.range lam).biUnion (fun j => (buildPN (canonicalR p.natDegree)).1.image (· + j * 2 ^ p.natDegree)) ∪ (Finset.range mu).biUnion (fun j => (buildPN (canonicalS p.natDegree)).2.image (lam * 2 ^ p.natDegree + j * 2 ^ (p.natDegree + 1) + ·)), (Finset.range lam).biUnion (fun j => (buildPN (canonicalR p.natDegree)).2.image (· + j * 2 ^ p.natDegree)) ∪ (Finset.range mu).biUnion (fun j => (buildPN (canonicalS p.natDegree)).1.image (lam * 2 ^ p.natDegree + j * 2 ^ (p.natDegree + 1) + ·)), lam * 2 ^ p.natDegree + mu * 2 ^ (p.natDegree + 1), by
          simp +zetaDelta at *;
          rintro u ( ⟨ a, ha, b, hb, rfl ⟩ | ⟨ a, ha, b, hb, rfl ⟩ );
          · nlinarith [ show 2 ^ p.natDegree > 0 by positivity, show 2 ^ ( p.natDegree + 1 ) > 0 by positivity, show b < 2 ^ p.natDegree from buildPN_canonicalR_bound p.natDegree |>.1 b hb ];
          · nlinarith [ Nat.pow_le_pow_right two_pos ( show p.natDegree + 1 ≥ 1 by linarith ), show b < 2 ^ ( p.natDegree + 1 ) from buildPN_canonicalS_bound p.natDegree |>.2 b hb ], by
          simp +zetaDelta at *;
          rintro v ( ⟨ a, ha, b, hb, rfl ⟩ | ⟨ a, ha, b, hb, rfl ⟩ );
          · nlinarith [ buildPN_canonicalR_bound p.natDegree |>.2 b hb, pow_pos ( zero_lt_two' ℕ ) p.natDegree, pow_succ' ( 2 : ℕ ) p.natDegree ];
          · nlinarith [ buildPN_canonicalS_bound p.natDegree |>.1 b hb, pow_pos ( zero_lt_two' ℕ ) p.natDegree, pow_succ' ( 2 : ℕ ) p.natDegree ], by
          intro x
          have h_sum : (∑ u ∈ (Finset.range lam).biUnion (fun j => (buildPN (canonicalR p.natDegree)).1.image (· + j * 2 ^ p.natDegree)), p.eval (x + u)) - (∑ v ∈ (Finset.range lam).biUnion (fun j => (buildPN (canonicalR p.natDegree)).2.image (· + j * 2 ^ p.natDegree)), p.eval (x + v)) = lam * (∏ i : Fin p.natDegree, (2 ^ (i : ℕ) : ℤ)) * polyA p := by
            have h_sum : ∀ j : ℕ, (∑ u ∈ (buildPN (canonicalR p.natDegree)).1, p.eval (x + j * 2 ^ p.natDegree + u)) - (∑ v ∈ (buildPN (canonicalR p.natDegree)).2, p.eval (x + j * 2 ^ p.natDegree + v)) = (∏ i : Fin p.natDegree, (2 ^ (i : ℕ) : ℤ)) * polyA p := by
              intro j
              have := signed_block_r p hd
              simp_all +decide [ mul_comm ];
              exact Or.inl rfl;
            rw [ Finset.sum_biUnion, Finset.sum_biUnion ];
            · simp_all +decide [ add_assoc, mul_comm ];
              simp_all +decide [add_comm, Finset.sum_add_distrib, sub_eq_iff_eq_add];
              linear_combination' h₁ * polyA p;
            · intros j hj k hk hjk; simp_all +decide [ Finset.disjoint_left ] ;
              intro a ha b hb; contrapose! hjk; nlinarith [ show 2 ^ p.natDegree > 0 by positivity, show a < 2 ^ p.natDegree by exact buildPN_canonicalR_bound p.natDegree |>.2 a ha, show b < 2 ^ p.natDegree by exact buildPN_canonicalR_bound p.natDegree |>.2 b hb ] ;
            · intros j hj k hk hjk; simp_all +decide [ Finset.disjoint_left ] ;
              intro a ha b hb; contrapose! hjk; nlinarith [ show 2 ^ p.natDegree > 0 by positivity, show a < 2 ^ p.natDegree by exact buildPN_canonicalR_bound p.natDegree |>.1 a ha, show b < 2 ^ p.natDegree by exact buildPN_canonicalR_bound p.natDegree |>.1 b hb ] ;
          have h_sum_s : (∑ u ∈ (Finset.range mu).biUnion (fun j => (buildPN (canonicalS p.natDegree)).2.image (lam * 2 ^ p.natDegree + j * 2 ^ (p.natDegree + 1) + ·)), p.eval (x + u)) - (∑ v ∈ (Finset.range mu).biUnion (fun j => (buildPN (canonicalS p.natDegree)).1.image (lam * 2 ^ p.natDegree + j * 2 ^ (p.natDegree + 1) + ·)), p.eval (x + v)) = -mu * (∏ i : Fin p.natDegree, ((2 ^ ((i : ℕ) + 1) : ℤ) - 1)) * polyA p := by
            have h_sum_s : ∀ j : ℕ, (∑ u ∈ (buildPN (canonicalS p.natDegree)).2.image (lam * 2 ^ p.natDegree + j * 2 ^ (p.natDegree + 1) + ·), p.eval (x + u)) - (∑ v ∈ (buildPN (canonicalS p.natDegree)).1.image (lam * 2 ^ p.natDegree + j * 2 ^ (p.natDegree + 1) + ·), p.eval (x + v)) = - (∏ i : Fin p.natDegree, ((2 ^ ((i : ℕ) + 1) : ℤ) - 1)) * polyA p := by
              intro j
              have := signed_block_s p hd
              simp_all +decide [Finset.sum_image];
              have := this.2 ( x + lam * 2 ^ p.natDegree + j * 2 ^ ( p.natDegree + 1 ) ) ; simp_all +decide [ add_assoc, mul_comm, mul_assoc, mul_left_comm, polyA ] ;
              linarith;
            rw [ Finset.sum_biUnion, Finset.sum_biUnion ];
            · rw [ ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun _ _ => h_sum_s _, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc ] ; ring;
            · intros j hj k hk hjk;
              simp +decide [ Finset.disjoint_left, Function.onFun ];
              intro a ha x hx; contrapose! hjk; nlinarith [ pow_pos ( zero_lt_two' ℕ ) p.natDegree, pow_succ' ( 2 : ℕ ) p.natDegree, show a < 2 ^ ( p.natDegree + 1 ) from buildPN_canonicalS_bound p.natDegree |>.1 a ha, show x < 2 ^ ( p.natDegree + 1 ) from buildPN_canonicalS_bound p.natDegree |>.1 x hx ] ;
            · intros j hj k hk hjk; simp_all +decide [ Finset.disjoint_left ] ;
              intro a ha x hx; contrapose! hjk; nlinarith [ pow_pos ( zero_lt_two' ℕ ) p.natDegree, pow_succ' ( 2 : ℕ ) p.natDegree, buildPN_canonicalS_bound p.natDegree |>.2 a ha, buildPN_canonicalS_bound p.natDegree |>.2 x hx ] ;
          rw [ Finset.sum_union, Finset.sum_union ];
          · linear_combination' h_sum + h_sum_s + h₁ * polyA p;
          · simp +decide [ Finset.disjoint_left ];
            rintro a x hx y hy rfl z hz t ht; nlinarith [ pow_pos ( zero_lt_two' ℕ ) p.natDegree, pow_succ' ( 2 : ℕ ) p.natDegree, buildPN_canonicalR_bound p.natDegree |>.2 y hy, buildPN_canonicalS_bound p.natDegree |>.1 t ht ] ;
          · simp +decide [ Finset.disjoint_left ];
            rintro a x hx₁ y hy₁ rfl z hz₁ w hw₁;
            nlinarith [ pow_pos ( zero_lt_two' ℕ ) p.natDegree, pow_succ' ( 2 : ℕ ) p.natDegree, show y < 2 ^ p.natDegree from buildPN_canonicalR_bound p.natDegree |>.1 y hy₁, show w < 2 ^ ( p.natDegree + 1 ) from buildPN_canonicalS_bound p.natDegree |>.2 w hw₁ ]⟩;
        all_goals generalize_proofs at *;
        unfold lambdaD; ring_nf at *;
        rw [ show p.natDegree * 2 = p.natDegree + p.natDegree by ring, pow_add ] ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) p.natDegree ]

end

/-! ===== Monomial Bound ===== -/

section NatScope
open Nat
open Polynomial BigOperators Finset

noncomputable section

/-!
For each prime power factor q = ℓ^e of d! (d ≥ 1):
  - e ≤ d
  - q ≤ 2^d
  - The number of distinct prime factors of d! is ≤ d.
-/

theorem factorial_prime_valuation_le (d : ℕ) (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    (d.factorial.factorization ℓ) ≤ d := by
  have h_val : Nat.factorization (Nat.factorial d) ℓ = ∑ k ∈ Finset.Ico 1 (Nat.log ℓ d + 1), d / ℓ^k := by
    grind +suggestions;
  have h_geo_series : ∑ k ∈ Finset.Ico 1 (Nat.log ℓ d + 1), d / ℓ^k ≤ d * (∑ k ∈ Finset.Ico 1 (Nat.log ℓ d + 1), (1 / ℓ^k : ℚ)) := by
    push_cast [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun _ _ => by rw [ mul_one_div, le_div_iff₀ ( pow_pos ( Nat.cast_pos.mpr hℓ.pos ) _ ) ] ; norm_cast; linarith [ Nat.div_mul_le_self d ( ℓ ^ ‹_› ) ] ;
  have h_geo_series_sum : ∑ k ∈ Finset.Ico 1 (Nat.log ℓ d + 1), (1 / ℓ^k : ℚ) ≤ 1 / (ℓ - 1) := by
    ring_nf;
    rw [ geom_sum_Ico ] <;> norm_num;
    · rcases ℓ with ( _ | _ | ℓ ) <;> norm_num at *;
      rw [ div_le_iff_of_neg ] <;> nlinarith only [ inv_pos.mpr ( by positivity : 0 < ( ℓ : ℚ ) + 1 + 1 ), inv_pos.mpr ( by positivity : 0 < ( ℓ : ℚ ) + 1 ), inv_pos.mpr ( by positivity : 0 < ( ℓ + 1 + 1 : ℚ ) ^ ( 1 + log ( ℓ + 1 + 1 ) d ) ), mul_inv_cancel₀ ( by positivity : ( ℓ : ℚ ) + 1 + 1 ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( ℓ : ℚ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( ℓ + 1 + 1 : ℚ ) ^ ( 1 + log ( ℓ + 1 + 1 ) d ) ≠ 0 ) ];
    · exact hℓ.ne_one;
  rcases ℓ with ( _ | _ | ℓ ) <;> simp_all +decide;
  exact_mod_cast h_geo_series.trans ( mul_le_of_le_one_right ( Nat.cast_nonneg _ ) ( h_geo_series_sum.trans ( inv_le_one_of_one_le₀ ( by linarith ) ) ) )

theorem factorial_prime_power_le (d : ℕ) (_hd : 1 ≤ d) (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    ℓ ^ (d.factorial.factorization ℓ) ≤ 2 ^ d := by
  have h_factorial_val : (d.factorial.factorization ℓ) ≤ d / (ℓ - 1) := by
    exact factorization_factorial_le_div_pred hℓ d
  have h_ineq : ℓ ≤ 2 ^ (ℓ - 1) := by
    exact Nat.le_of_pred_lt ( Nat.recOn ℓ ( by norm_num ) fun n ihn => by cases n <;> norm_num [ Nat.pow_succ ] at * ; linarith );
  refine' le_trans ( Nat.pow_le_pow_left h_ineq _ ) _;
  rw [ ← pow_mul ] ; exact pow_le_pow_right₀ ( by decide ) ( by nlinarith [ Nat.div_mul_le_self d ( ℓ - 1 ) ] ) ;

/-- The monomial polynomial X^d. -/
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

/-! ## Explicit monomial bound constants

  Λ_d = 2^{d(d-1)/2+2d+2}
  M_d* = d·2^d · (8d·d!·2^d)^d
  K_d* = (6d)^d
  Q_d* = ⌈(M_d* + K_d*)/d!⌉
  Y_d* = 8d·(d!·2^d + Λ_d)
  U_mon(d) = M_d* + Q_d* · Λ_d · (Y_d* + Q_d* · Λ_d)^d
-/

/-- M_d* = d·2^d · (8d·d!·2^d)^d, bounding M_{R_d*}. -/
def monMstar (d : ℕ) : ℕ := d * 2 ^ d * (8 * d * d.factorial * 2 ^ d) ^ d

/-- K_d* = (6d)^d, bounding p(τ_p(1)). -/
def monKstar (d : ℕ) : ℕ := (6 * d) ^ d

/-- Q_d* = ⌈(M_d* + K_d*)/d!⌉, bounding Q_{R_d*}. -/
def monQstar (d : ℕ) : ℕ := (monMstar d + monKstar d) / d.factorial + 1

/-- Y_d* = 8d·(d!·2^d + Λ_d), bounding Y_{R_d*,B_d}. -/
def monYstar (d : ℕ) : ℕ := 8 * d * (d.factorial * 2 ^ d + lambdaD d)

/-- U_mon(d) = M_d* + Q_d* · (Λ_d+1) · (Y_d* + Q_d* · (Λ_d+1))^d,
    the explicit monomial threshold bound. -/
def monBound (d : ℕ) : ℕ :=
  monMstar d + monQstar d * (lambdaD d + 1) * (monYstar d + monQstar d * (lambdaD d + 1)) ^ d

/-! ## Explicit monomial bound -/

end

open Nat

/-
For p(X) = X^d with d ≥ 2, we construct a residue datum modulo d! with
sharper bounds: eMax ≤ d!·2^d, |F_r| ≤ d·2^d.

The construction uses orthogonal generators from the prime factorization of d!.
-/

open Polynomial BigOperators Finset

noncomputable section

/-! ## Definitions -/

/-- The set of distinct primes dividing d!. Equal to primes ≤ d for d ≥ 1. -/
abbrev factPrimes (d : ℕ) : Finset ℕ := d.factorial.primeFactors

/-- The prime power factor q_ℓ = ℓ^{v_ℓ(d!)}. -/
def ppFactor (d ℓ : ℕ) : ℕ := ℓ ^ (d.factorial.factorization ℓ)

/-- The orthogonal generator m_ℓ = ∏_{p | d!, p ≠ ℓ} p. -/
def orthoGen (d ℓ : ℕ) : ℕ := ∏ p ∈ (factPrimes d).erase ℓ, p

/-! ## Basic facts about factPrimes -/

theorem factPrimes_prime {d ℓ : ℕ} (h : ℓ ∈ factPrimes d) : Nat.Prime ℓ :=
  (Nat.mem_primeFactors.mp h).1

theorem factPrimes_le' {d ℓ : ℕ} (h : ℓ ∈ factPrimes d) : ℓ ≤ d :=
  (factPrimes_prime h).dvd_factorial.mp (Nat.mem_primeFactors.mp h).2.1

/-! ## Properties of ppFactor -/

theorem ppFactor_pos (d ℓ : ℕ) (h : ℓ ∈ factPrimes d) : 0 < ppFactor d ℓ :=
  pos_of_ne_zero (pow_ne_zero _ (factPrimes_prime h).pos.ne')

theorem ppFactor_le_two_pow' (d : ℕ) (hd : 1 ≤ d) (ℓ : ℕ) (h : ℓ ∈ factPrimes d) :
    ppFactor d ℓ ≤ 2 ^ d :=
  factorial_prime_power_le d hd ℓ (factPrimes_prime h)

theorem factorial_eq_prod_ppFactor (d : ℕ) :
    d.factorial = ∏ ℓ ∈ factPrimes d, ppFactor d ℓ :=
  (Nat.factorization_prod_pow_eq_self (Nat.factorial_pos d).ne').symm

/-! ## Properties of orthoGen -/

theorem orthoGen_pos' (d : ℕ) (ℓ : ℕ) (_hℓ : ℓ ∈ factPrimes d) :
    0 < orthoGen d ℓ :=
  Finset.prod_pos fun _p hp => (factPrimes_prime (Finset.mem_of_mem_erase hp)).pos

/-
gcd(m_ℓ, ℓ) = 1. m_ℓ is a product of primes ≠ ℓ, so ℓ ∤ m_ℓ.
-/
theorem orthoGen_coprime' (d : ℕ) (ℓ : ℕ) (hℓ : ℓ ∈ factPrimes d) :
    Nat.Coprime (orthoGen d ℓ) ℓ := by
  exact Nat.Coprime.prod_left fun p hp => by have := Nat.coprime_primes ( factPrimes_prime <| Finset.mem_of_mem_erase hp ) ( factPrimes_prime hℓ ) ; aesop;

/-
For p ≠ ℓ with p prime dividing d!, p ∣ m_ℓ (since p appears in the product).
-/
theorem prime_dvd_orthoGen' (d : ℕ) (ℓ p : ℕ)
    (hp : p ∈ factPrimes d) (hne : p ≠ ℓ) :
    p ∣ orthoGen d ℓ := by
  exact Finset.dvd_prod_of_mem _ ( by aesop )

/-
m_ℓ ≤ d!.
-/
theorem orthoGen_le_factorial' (d : ℕ) (_hd : 1 ≤ d) (ℓ : ℕ) (_hℓ : ℓ ∈ factPrimes d) :
    orthoGen d ℓ ≤ d.factorial := by
  exact Nat.le_of_dvd ( Nat.factorial_pos _ ) ( Nat.prod_primeFactors_dvd _ |> dvd_trans ( by apply_rules [ Finset.prod_dvd_prod_of_subset, Finset.erase_subset ] ) )

/-
m_ℓ^d ≡ 0 (mod q_p) for p ≠ ℓ.
-/
theorem orthoGen_pow_zero_mod' (d : ℕ) (_hd : 1 ≤ d) (ℓ p : ℕ)
    (_hℓ : ℓ ∈ factPrimes d) (hp : p ∈ factPrimes d) (hne : p ≠ ℓ) :
    ppFactor d p ∣ (orthoGen d ℓ) ^ d := by
  -- Since p ≠ ℓ, we have p ∈ (factPrimes d).erase ℓ, so p ∣ orthoGen d ℓ.
  have h_p_div_orthoGen : p ∣ orthoGen d ℓ :=
    prime_dvd_orthoGen' d ℓ p hp hne
  exact dvd_trans ( pow_dvd_pow_of_dvd h_p_div_orthoGen _ ) ( pow_dvd_pow _ ( show d.factorial.factorization p ≤ d from factorial_prime_valuation_le d p ( factPrimes_prime hp ) ) )

/-
m_ℓ^d is coprime to q_ℓ.
-/
theorem orthoGen_pow_coprime' (d : ℕ) (ℓ : ℕ) (hℓ : ℓ ∈ factPrimes d) :
    Nat.Coprime ((orthoGen d ℓ) ^ d) (ppFactor d ℓ) := by
  exact Nat.Coprime.pow_left _ ( orthoGen_coprime' d ℓ hℓ ) |> Nat.Coprime.pow_right _

/-
For each prime ℓ | d! and residue r, there exists c < q_ℓ
    with c · m_ℓ^d ≡ r (mod q_ℓ).
-/
theorem crt_coeff_exists' (d : ℕ) (_hd : 1 ≤ d) (ℓ : ℕ) (hℓ : ℓ ∈ factPrimes d) (r : ℕ) :
    ∃ c : ℕ, c < ppFactor d ℓ ∧ c * (orthoGen d ℓ) ^ d ≡ r [MOD ppFactor d ℓ] := by
  -- Since $m_ℓ^d$ is coprime to $q_ℓ$ (by orthoGen_pow_coprime'), there exists an inverse of $m_ℓ^d$ modulo $q_ℓ$.
  obtain ⟨inv_mℓd, hinv_mℓd⟩ : ∃ inv_mℓd : ℕ, inv_mℓd * (orthoGen d ℓ) ^ d ≡ 1 [MOD ppFactor d ℓ] := by
    have h_coprime : Nat.Coprime ((orthoGen d ℓ) ^ d) (ppFactor d ℓ) :=
      orthoGen_pow_coprime' d ℓ hℓ
    have := Nat.exists_mul_mod_eq_one_of_coprime h_coprime;
    rcases k : ppFactor d ℓ with ( _ | _ | k ) <;> simp_all +decide [ mul_comm, Nat.ModEq, Nat.mod_one ];
    exact ⟨ _, this.choose_spec.2 ⟩;
  use ( inv_mℓd * r ) % ppFactor d ℓ;
  exact ⟨ Nat.mod_lt _ ( ppFactor_pos d ℓ hℓ ), by simpa [ mul_assoc, mul_comm, mul_left_comm, ← ZMod.natCast_eq_natCast_iff ] using hinv_mℓd.mul_right r ⟩

/-- CRT coefficient, defined for all ℓ (returns 0 if ℓ ∉ factPrimes d). -/
noncomputable def crtCoeffFun (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (ℓ : ℕ) : ℕ :=
  if h : ℓ ∈ factPrimes d then (crt_coeff_exists' d hd ℓ h r).choose else 0

theorem crtCoeffFun_lt (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (ℓ : ℕ) (hℓ : ℓ ∈ factPrimes d) :
    crtCoeffFun d hd r ℓ < ppFactor d ℓ := by
  simp only [crtCoeffFun, hℓ, dite_true]
  exact (crt_coeff_exists' d hd ℓ hℓ r).choose_spec.1

theorem crtCoeffFun_spec (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (ℓ : ℕ) (hℓ : ℓ ∈ factPrimes d) :
    crtCoeffFun d hd r ℓ * (orthoGen d ℓ) ^ d ≡ r [MOD ppFactor d ℓ] := by
  simp only [crtCoeffFun, hℓ, dite_true]
  exact (crt_coeff_exists' d hd ℓ hℓ r).choose_spec.2

/-
The ppFactors are pairwise coprime.
-/
theorem ppFactor_pairwise_coprime (d : ℕ) :
    Set.Pairwise (↑(factPrimes d))
      (fun ℓ₁ ℓ₂ => Nat.Coprime (ppFactor d ℓ₁) (ppFactor d ℓ₂)) := by
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hne; simp +decide [ *, ppFactor ] ;
  apply_mod_cast Nat.coprime_pow_primes <;> simp_all +decide [ Nat.factorial_ne_zero ]

/-
For p(X) = X^d with d ≥ 2, there exists a residue datum modulo d! with eMax ≤
    d!·2^d and |F_r| ≤ d·2^d.

    The construction uses orthogonal generators m_ℓ = ∏_{p|d!,p≠ℓ} p.
    For each residue r, CRT coefficients c_ℓ are chosen so that
    c_ℓ · m_ℓ^d ≡ r (mod q_ℓ). The families F_r = ∪_ℓ {m_ℓ + t·d! : t < c_ℓ}
    give ∑_{e ∈ F_r} e^d ≡ r (mod d!) by CRT.
-/
set_option maxHeartbeats 800000 in
theorem monomial_crt_residue_datum (d : ℕ) (hd : 2 ≤ d) :
    ∃ R : ResidueDatum (monomialPoly d) d.factorial,
      R.eMax ≤ d.factorial * 2 ^ d ∧
      (∀ r, (R.F r).card ≤ d * 2 ^ d) ∧
      (∀ e ∈ R.E, 1 ≤ e) := by
  refine' ⟨ _, _, _, _ ⟩;
  refine' ⟨ _, _, _, _ ⟩
  all_goals generalize_proofs at *;
  exact Finset.biUnion ( factPrimes d ) ( fun ℓ => ( Finset.range ( ppFactor d ℓ - 1 ) ).image ( fun t => orthoGen d ℓ + t * d ! ) );
  use fun r => Finset.biUnion ( factPrimes d ) ( fun ℓ => if h : ℓ ∈ factPrimes d then Finset.image ( fun t => orthoGen d ℓ + t * d ! ) ( Finset.range ( crtCoeffFun d ( by linarith ) ( r.val % ppFactor d ℓ ) ℓ ) ) else ∅ );
  · simp +decide [ Finset.subset_iff ];
    intro r x p hp hpd hne hx; split_ifs at hx ; simp_all +decide [ Finset.mem_image ] ;
    · rcases hx with ⟨ a, ha, rfl ⟩ ; exact ⟨ p, ⟨ by tauto, by tauto ⟩, a, lt_of_lt_of_le ha ( Nat.le_sub_one_of_lt ( crtCoeffFun_lt _ _ _ _ ( by aesop ) ) ), rfl ⟩ ;
    · contradiction;
  · intro r
    have h_sum : ∑ e ∈ Finset.biUnion (factPrimes d) (fun ℓ => if h : ℓ ∈ factPrimes d then Finset.image (fun t => orthoGen d ℓ + t * d !) (Finset.range (crtCoeffFun d (by linarith) (r.val % ppFactor d ℓ) ℓ)) else ∅), (e : ℤ) ^ d ≡ r.val [ZMOD d !] := by
      have h_sum : ∑ e ∈ Finset.biUnion (factPrimes d) (fun ℓ => if h : ℓ ∈ factPrimes d then Finset.image (fun t => orthoGen d ℓ + t * d !) (Finset.range (crtCoeffFun d (by linarith) (r.val % ppFactor d ℓ) ℓ)) else ∅), (e : ℤ) ^ d ≡ ∑ ℓ ∈ factPrimes d, crtCoeffFun d (by linarith) (r.val % ppFactor d ℓ) ℓ * (orthoGen d ℓ) ^ d [ZMOD d !] := by
        rw [ Finset.sum_biUnion ];
        · refine' Int.ModEq.sum fun ℓ hℓ => _;
          split_ifs ; simp_all +decide [ Int.ModEq ];
          simp +decide [ ← ZMod.intCast_eq_intCast_iff', Int.mul_emod ];
        · intros ℓ hℓ ℓ' hℓ' hne; simp_all +decide [ Finset.disjoint_left ] ;
          intro a ha x hx H; have := congr_arg ( · % ℓ ) H; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hℓ.2.1, Nat.mod_eq_zero_of_dvd hℓ'.2 ] at this;
          have h_contra : orthoGen d ℓ' % ℓ = 0 := by
            exact Nat.mod_eq_zero_of_dvd <| Finset.dvd_prod_of_mem _ <| by aesop;
          have h_contra : Nat.Coprime (orthoGen d ℓ) ℓ := by
            exact orthoGen_coprime' d ℓ ( by aesop );
          exact absurd ( h_contra.gcd_eq_one ▸ Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero ( show orthoGen d ℓ % ℓ = 0 from this.symm.trans ‹orthoGen d ℓ' % ℓ = 0› ) ) ( Nat.dvd_refl ℓ ) ) ( by aesop );
      refine h_sum.trans <| Int.modEq_of_dvd ?_;
      have h_crt : ∀ ℓ ∈ factPrimes d, (r.val : ℤ) - ∑ ℓ' ∈ factPrimes d, crtCoeffFun d (by linarith) (r.val % ppFactor d ℓ') ℓ' * (orthoGen d ℓ') ^ d ≡ 0 [ZMOD ppFactor d ℓ] := by
        intro ℓ hℓ
        have h_crt : (r.val : ℤ) - crtCoeffFun d (by linarith) (r.val % ppFactor d ℓ) ℓ * (orthoGen d ℓ) ^ d ≡ 0 [ZMOD ppFactor d ℓ] := by
          have := crtCoeffFun_spec d ( by linarith ) ( r.val % ppFactor d ℓ ) ℓ hℓ; simp_all +decide [ ← Int.natCast_modEq_iff ] ;
          exact Int.ModEq.sub ( Int.ModEq.refl _ ) ( this.trans ( Int.mod_modEq _ _ ) ) |> Int.ModEq.trans <| Int.modEq_zero_iff_dvd.mpr <| by norm_num;
        have h_crt : ∀ ℓ' ∈ factPrimes d, ℓ' ≠ ℓ → (crtCoeffFun d (by linarith) (r.val % ppFactor d ℓ') ℓ') * (orthoGen d ℓ') ^ d ≡ 0 [ZMOD ppFactor d ℓ] := by
          intros ℓ' hℓ' hne
          have h_div : ppFactor d ℓ ∣ (orthoGen d ℓ') ^ d := by
            grind +suggestions;
          exact Int.modEq_zero_iff_dvd.mpr ( dvd_mul_of_dvd_right ( mod_cast h_div ) _ );
        simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
        rw [ Finset.sum_eq_single ℓ ] <;> aesop;
      have h_crt : (∏ ℓ ∈ factPrimes d, ppFactor d ℓ : ℤ) ∣ (r.val : ℤ) - ∑ ℓ' ∈ factPrimes d, crtCoeffFun d (by linarith) (r.val % ppFactor d ℓ') ℓ' * (orthoGen d ℓ') ^ d := by
        convert Finset.prod_dvd_of_coprime _ _ <;> norm_num +zetaDelta at *;
        · intros ℓ hℓ ℓ' hℓ' hne; exact (by
          have := ppFactor_pairwise_coprime d; aesop;);
        · exact fun ℓ hℓ hℓ' hℓ'' => Int.modEq_zero_iff_dvd.mp ( h_crt ℓ hℓ hℓ' hℓ'' );
      convert h_crt using 1;
      · exact_mod_cast factorial_eq_prod_ppFactor d;
      · norm_cast
    generalize_proofs at *;
    convert h_sum.symm.dvd using 1 ; norm_num [ monomialPoly ];
  · simp +decide [ ResidueDatum.eMax ];
    intro p hp hpd hd b hb
    have h_orthoGen : orthoGen d p ≤ d ! := by
      apply orthoGen_le_factorial' d (by linarith) p (by
      exact Nat.mem_primeFactors.mpr ⟨ hp, hpd, hd ⟩)
    have h_ppFactor : ppFactor d p ≤ 2 ^ d := by
      apply ppFactor_le_two_pow' d (by linarith) p (by
      exact Nat.mem_primeFactors.mpr ⟨ hp, hpd, hd ⟩)
    have h_b : b < 2 ^ d := by
      grind
    generalize_proofs at *;
    nlinarith [ Nat.factorial_pos d ];
  · intro r
    have h_card : (Finset.biUnion (factPrimes d) (fun ℓ => if h : ℓ ∈ factPrimes d then Finset.image (fun t => orthoGen d ℓ + t * d !) (Finset.range (crtCoeffFun d (by linarith) (r.val % ppFactor d ℓ) ℓ)) else ∅)).card ≤ ∑ ℓ ∈ factPrimes d, (ppFactor d ℓ - 1) := by
      refine' le_trans ( Finset.card_biUnion_le ) _;
      refine' Finset.sum_le_sum fun ℓ hℓ => _;
      split_ifs ; simp_all +decide [ Finset.card_image_of_injective, Function.Injective, Nat.factorial_ne_zero ];
      exact Nat.le_sub_one_of_lt ( crtCoeffFun_lt d ( by linarith ) ( r.val % ppFactor d ℓ ) ℓ ( by
        exact Nat.mem_primeFactors.mpr ⟨ hℓ.1, hℓ.2, by positivity ⟩ ) );
    refine' le_trans h_card _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => Nat.sub_le _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => ppFactor_le_two_pow' d ( by linarith ) x hx ) _ ; norm_num [ Finset.sum_const, nsmul_eq_mul ];
    exact le_trans ( Finset.card_le_card ( show factPrimes d ⊆ Finset.Icc 1 d from fun x hx => Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_primeFactors hx, factPrimes_le' hx ⟩ ) ) ( by simp )
  · -- All elements of E are ≥ 1 since orthoGen ≥ 1
    intro e he
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at he
    obtain ⟨ℓ, hℓ, t, _, rfl⟩ := he
    have := orthoGen_pos' d ℓ (by exact Nat.mem_primeFactors.mpr ⟨factPrimes_prime hℓ, (factPrimes_prime hℓ).dvd_factorial.mpr (factPrimes_le' hℓ), Nat.factorial_pos d |>.ne'⟩)
    omega

end

open Nat

/-
Provides the general doubling lemma for CRT-type residue data and
monomial-specific parameter estimates needed for monomial_crt_bound.
-/

open Polynomial BigOperators Finset

noncomputable section

/-! For the CRT residue datum, residue elements are not spaced ≥ a apart, so we
cannot use `separated_doubling`. Instead, we use the fact that consecutive non-I
elements have gaps bounded by max(1, eMax+1, L+1), and each gap type is handled
by the appropriate τ parameter.

The hypothesis `hE_pos : ∀ e ∈ R.E, 1 ≤ e` ensures that the longest run in E has
length ≤ eMax (not eMax+1), giving a gap bound of eMax+1. For the CRT datum,
this holds because all generators orthoGen ≥ 1.
-/

theorem crt_doubling_block_gap
    (p : Polynomial ℤ) (a : ℕ)
    (R : ResidueDatum p a)
    (B : SignedBlock p (polyA p))
    (R₀ Y Q : ℕ)
    (hY_res : R₀ + R.E.sup id + 2 ≤ Y)
    (u v : ℕ) (huI : u ∉ R.E.image (R₀ + ·) ∪ (Finset.range (Q - 1)).biUnion
      (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·)))
    (_huv : u < v) (hbetween : ∀ w, u < w → w < v →
      w ∈ R.E.image (R₀ + ·) ∪ (Finset.range (Q - 1)).biUnion
      (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·)))
    (huY : Y ≤ u + 1) :
    v ≤ u + B.L + 1 := by
  contrapose! hbetween;
  refine' ⟨ u + B.L + 1, _, _, _ ⟩ <;> norm_num [ huY, hbetween ];
  constructor;
  · intro x hx; have := Finset.le_sup ( f := id ) hx; simp_all +decide ;
    linarith [ B.hP_bound, B.hN_bound ];
  · intro i hi x hx; rcases hx with ( hx | hx ) <;> intro H <;> have := B.hP_bound x <;> have := B.hN_bound x <;> simp_all +decide ;
    · rcases i with ( _ | i ) <;> simp_all +decide [ Nat.succ_mul ];
      · grind;
      · exact huI.2 i ( by linarith ) x ( Or.inl hx ) ( by linarith );
    · rcases i with ( _ | i ) <;> simp_all +decide [ Nat.succ_mul ];
      · grind;
      · exact huI.2 i ( by linarith ) x ( Or.inr hx ) ( by linarith )

theorem crt_doubling_res_gap
    (p : Polynomial ℤ) (a : ℕ)
    (R : ResidueDatum p a)
    (B : SignedBlock p (polyA p))
    (R₀ Y Q : ℕ)
    (hY_res : R₀ + R.E.sup id + 2 ≤ Y)
    (hE_pos : ∀ e ∈ R.E, 1 ≤ e)
    (u v : ℕ)
    (_hvI : v ∉ R.E.image (R₀ + ·) ∪ (Finset.range (Q - 1)).biUnion
      (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·)))
    (huv : u < v) (hbetween : ∀ w, u < w → w < v →
      w ∈ R.E.image (R₀ + ·) ∪ (Finset.range (Q - 1)).biUnion
      (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·)))
    (huY : u + 1 < Y) (hv1 : v ≠ u + 1) :
    v ≤ u + (R.E.sup id + 1) := by
  -- Assume v > u + R.E.sup id + 1. Then take w = R₀ + R.E.sup id + 1.
  by_contra hv_contra
  set w := R₀ + R.E.sup id + 1 with hw_def;
  have hw_in_I : w ∈ R.E.image (R₀ + ·) ∪ (Finset.range (Q - 1)).biUnion (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·)) := by
    apply hbetween w;
    · contrapose! hbetween;
      use u + 1;
      simp +zetaDelta at *;
      exact ⟨ by omega, fun x hx => by linarith [ show x ≤ R.E.sup id from Finset.le_sup ( f := id ) hx ], fun x hx y hy => by linarith [ show x * ( B.L + 1 ) ≥ 0 by positivity ] ⟩;
    · linarith [ show u ≥ R₀ from by
                  have hu_ge_R₀ : u + 1 ∈ R.E.image (R₀ + ·) ∪ (Finset.range (Q - 1)).biUnion (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·)) := by
                    exact hbetween _ ( Nat.lt_succ_self _ ) ( lt_of_le_of_ne huv hv1.symm );
                  grind ];
  simp +zetaDelta at *;
  rcases hw_in_I with ( ⟨ x, hx, hx' ⟩ | ⟨ x, hx, y, hy, hy' ⟩ ) <;> simp_all +decide [ add_assoc ];
  · exact not_le_of_gt ( Nat.lt_succ_self _ ) ( Finset.le_sup ( f := id ) hx );
  · grind

theorem crt_doubling (p : Polynomial ℤ)
    (a : ℕ) (_ha : 0 < a)
    (R : ResidueDatum p a)
    (B : SignedBlock p (polyA p))
    (hE_pos : ∀ e ∈ R.E, 1 ≤ e)
    (T₀ : ℕ) (hT₀ : TauProp p 1 T₀)
    (T_res : ℕ) (hT_res : TauProp p (R.E.sup id + 1) T_res)
    (T_blk : ℕ) (hT_blk : TauProp p (B.L + 1) T_blk)
    (_hT₀_le_res : T₀ ≤ T_res) (_hT₀_le_blk : T₀ ≤ T_blk)
    (R₀ : ℕ) (hR₀_ge : T_res + 1 ≤ R₀)
    (Y : ℕ) (hY_res : R₀ + R.E.sup id + 2 ≤ Y) (hY_blk : T_blk + 1 ≤ Y)
    (Q : ℕ) :
    let I := R.E.image (R₀ + ·) ∪ (Finset.range (Q - 1)).biUnion
      (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·))
    ∀ u v : ℕ, T₀ ≤ u → u ∉ I → v ∉ I → u < v →
      (∀ w, u < w → w < v → w ∈ I) → p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ) := by
  intros I u v hu huI hvI huv hbetween
  by_cases hv1 : v = u + 1
  · exact hv1 ▸ (hT₀ u (u + 1) hu (by omega) (by omega)).2.2
  · by_cases huY : u + 1 < Y
    · have hgap := crt_doubling_res_gap p a R B R₀ Y Q hY_res hE_pos u v hvI huv hbetween huY hv1
      have hu1 : u + 1 ∈ R.E.image (R₀ + ·) := by
        have h := hbetween (u + 1) (by omega) (by omega)
        simp only [I, Finset.mem_union] at h
        rcases h with h | h
        · exact h
        · simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
              Finset.mem_union] at h
          obtain ⟨i, _, x, _, hxeq⟩ := h; omega
      simp only [Finset.mem_image] at hu1
      obtain ⟨e, he, heq⟩ := hu1
      have hu_ge : T_res ≤ u := by omega
      exact (hT_res u v hu_ge huv hgap).2.2
    · push_neg at huY
      have hgap := crt_doubling_block_gap p a R B R₀ Y Q hY_res u v huI huv hbetween huY
      have hu_blk : T_blk ≤ u := by omega
      exact (hT_blk u v hu_blk huv hgap).2.2

/-! ## Monomial-specific helpers -/

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

theorem crt_index_bound (d : ℕ) (hd : 2 ≤ d)
    (R : ResidueDatum (monomialPoly d) d.factorial)
    (hR_emax : R.eMax ≤ d.factorial * 2 ^ d)
    (R₀ : ℕ) (hR₀_le : R₀ ≤ explicitTailParam (monomialPoly d) (R.eMax + 1) + d.factorial) :
    R₀ + R.eMax ≤ 8 * d * d.factorial * 2 ^ d := by
  -- By definition of $explicitTailParam$, we know that $explicitTailParam(X^d, eMax+1) \leq 6d(eMax+1)$ since $eMax+1 \geq 1$.
  have h_explicitTailParam : explicitTailParam (monomialPoly d) (R.eMax + 1) ≤ 6 * d * (R.eMax + 1) := by
    unfold explicitTailParam;
    unfold monomialPoly; norm_num;
    unfold Hzero; norm_num;
    norm_num [ Finset.sum_range, ne_of_lt ];
    nlinarith;
  nlinarith [ Nat.zero_le ( d ! * 2 ^ d ), Nat.self_le_factorial d, Nat.pow_le_pow_right two_pos hd ]

/-
Each residue sum k(r) = ∑_{e ∈ F_r} (R₀+e)^d is bounded by
    d·2^d · (8d·d!·2^d)^d = monMstar d.
-/
theorem crt_residue_sum_bound (d : ℕ) (hd : 2 ≤ d)
    (R : ResidueDatum (monomialPoly d) d.factorial)
    (hR_emax : R.eMax ≤ d.factorial * 2 ^ d)
    (hR_card : ∀ r, (R.F r).card ≤ d * 2 ^ d)
    (R₀ : ℕ) (hR₀_le : R₀ ≤ explicitTailParam (monomialPoly d) (R.eMax + 1) + d.factorial)
    (r : Fin d.factorial) :
    ∑ e ∈ R.F r, (monomialPoly d).eval ((↑R₀ : ℤ) + ↑e) ≤ ↑(monMstar d) := by
  -- By definition of $monMstar$, we know that $(R₀ + e)^d \le (8d * d.factorial * 2^d)^d$ for each $e \in F_r$.
  have h_monomial_bound : ∀ e ∈ R.F r, (R₀ + e : ℤ) ^ d ≤ (8 * d * d.factorial * 2 ^ d) ^ d := by
    have h_monomial_bound : R₀ + R.eMax ≤ 8 * d * d.factorial * 2 ^ d := by
      convert crt_index_bound d hd R hR_emax R₀ hR₀_le using 1;
    exact fun e he => pow_le_pow_left₀ ( by positivity ) ( mod_cast by linarith [ show e ≤ R.eMax from Finset.le_sup ( f := id ) ( R.hF_sub r he ) ] ) _;
  refine' le_trans ( Finset.sum_le_sum fun e he => show ( monomialPoly d |> Polynomial.eval _ ) ≤ _ from _ ) _;
  use fun e => ( 8 * d * d ! * 2 ^ d ) ^ d;
  · convert h_monomial_bound e he using 1 ; norm_num [ monomialPoly ];
  · simp_all +decide [ monMstar ];
    exact mul_le_mul_of_nonneg_right ( mod_cast hR_card r ) ( by positivity )

theorem crt_M_bound (d : ℕ) (hd : 2 ≤ d)
    (R : ResidueDatum (monomialPoly d) d.factorial)
    (hR_emax : R.eMax ≤ d.factorial * 2 ^ d)
    (hR_card : ∀ r, (R.F r).card ≤ d * 2 ^ d)
    (R₀ : ℕ) (hR₀_le : R₀ ≤ explicitTailParam (monomialPoly d) (R.eMax + 1) + d.factorial)
    (_hR₀_ge : explicitTailParam (monomialPoly d) (R.eMax + 1) + 1 ≤ R₀)
    (_hR₀_nonneg : ∀ r : Fin d.factorial, 0 ≤ ∑ e ∈ R.F r, (monomialPoly d).eval ((R₀ : ℤ) + ↑e)) :
    (Finset.univ.sup' ⟨⟨0, Nat.factorial_pos d⟩, Finset.mem_univ _⟩
      (fun r : Fin d.factorial => ∑ e ∈ R.F r, (monomialPoly d).eval ((R₀ : ℤ) + ↑e))) ≤
    ↑(monMstar d) := by
  simp +zetaDelta at *;
  convert crt_residue_sum_bound d hd R hR_emax hR_card R₀ hR₀_le

theorem crt_Y_bound (d : ℕ) (hd : 2 ≤ d)
    (R : ResidueDatum (monomialPoly d) d.factorial)
    (hR_emax : R.eMax ≤ d.factorial * 2 ^ d)
    (R₀ : ℕ) (hR₀_le : R₀ ≤ explicitTailParam (monomialPoly d) (R.eMax + 1) + d.factorial)
    (B : SignedBlock (monomialPoly d) (polyA (monomialPoly d)))
    (hB_L : B.L ≤ lambdaD d) :
    max (R₀ + R.eMax + 2) (explicitTailParam (monomialPoly d) (B.L + 1) + 1) ≤ monYstar d := by
  have := @crt_index_bound d hd R hR_emax R₀ hR₀_le
  simp [monYstar] at *;
  constructor;
  · nlinarith [ show 0 < d ! * 2 ^ d by positivity, show 0 < d ! * 2 ^ d * d by positivity, show 0 < d ! * 2 ^ d * d ^ 2 by positivity, show 0 < lambdaD d by unfold lambdaD; positivity ];
  · rw [ monomial_tau_eq' ];
    · nlinarith [ Nat.zero_le ( d ! * 2 ^ d ), Nat.zero_le ( lambdaD d ), Nat.self_le_factorial d, Nat.pow_le_pow_right two_pos hd ];
    · linarith;
    · grind

/-
Each block term (Y+i*(L+1)+v)^d ≤ (monYstar+monQstar*(Λ+1))^d
-/
theorem crt_block_term_bound (d : ℕ) (_hd : 2 ≤ d)
    (B : SignedBlock (monomialPoly d) (polyA (monomialPoly d)))
    (hB_L : B.L ≤ lambdaD d)
    (Y : ℕ) (hY : Y ≤ monYstar d)
    (Q : ℕ) (hQ : Q - 1 ≤ monQstar d)
    (i : ℕ) (hi : i < Q - 1) (v : ℕ) (hv : v ∈ B.N) :
    (monomialPoly d).eval ((↑Y + ↑i * (↑B.L + 1) : ℤ) + ↑v) ≤
    (↑(monYstar d + monQstar d * (lambdaD d + 1)) : ℤ) ^ d := by
  -- By definition of $monomialPoly$, we know that $(monomialPoly d).eval (x : ℤ) = x^d$.
  have h_eval_monomial : ∀ x : ℤ, (monomialPoly d).eval x = x^d := by
    exact fun x => by rw [ monomialPoly ] ; norm_num;
  -- Since $v \in B.N$, we have $v < B.L \leq \lambdaD d$.
  have hv_lt_lambdaD : v < B.L := by
    exact B.hN_bound v hv;
  rw [ h_eval_monomial ];
  gcongr;
  norm_cast;
  nlinarith

theorem crt_C0_bound (d : ℕ) (hd : 2 ≤ d)
    (B : SignedBlock (monomialPoly d) (polyA (monomialPoly d)))
    (hB_L : B.L ≤ lambdaD d)
    (Y : ℕ) (hY : Y ≤ monYstar d)
    (Q : ℕ) (hQ : Q - 1 ≤ monQstar d)
    (M : ℤ) (hM : M ≤ ↑(monMstar d))
    (C₁ : ℤ) (hC₁_def : C₁ = ∑ i ∈ Finset.range (Q - 1),
      ∑ v ∈ B.N, (monomialPoly d).eval ((↑Y + ↑i * (↑B.L + 1) : ℤ) + ↑v))
    (C₀ : ℤ) (hC₀_def : C₀ = M - ↑d.factorial + 1 + C₁) :
    C₀ ≤ ↑(monBound d) := by
  -- Substitute the bounds for M and C₁ into the expression for C₀.
  have hC₀_bound : C₀ ≤ monMstar d - d.factorial + 1 + monQstar d * (lambdaD d + 1) * (monYstar d + monQstar d * (lambdaD d + 1))^d := by
    refine' hC₀_def.le.trans ( add_le_add ( add_le_add ( add_le_add hM le_rfl ) le_rfl ) _ );
    refine' hC₁_def.le.trans _;
    refine' le_trans ( Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun v hv => _ ) _;
    use fun i v => ( monYstar d + monQstar d * ( lambdaD d + 1 ) ) ^ d;
    · convert crt_block_term_bound d hd B hB_L Y hY Q hQ i ( Finset.mem_range.mp hi ) v hv using 1;
    · simp +zetaDelta at *;
      rw [ mul_assoc ];
      gcongr;
      · lia;
      · exact_mod_cast Nat.le_succ_of_le ( le_trans ( Finset.card_le_card ( show B.N ⊆ Finset.range ( B.L ) from fun x hx => Finset.mem_range.mpr ( B.hN_bound x hx ) ) ) ( by simpa ) );
  refine le_trans hC₀_bound ?_;
  unfold monBound;
  norm_num [ sub_add ];
  exact Nat.factorial_pos _

end

/-
Q bound helper: floor((M+K)/a) + 1 ≤ monQstar when M ≤ monMstar and K ≤ monKstar.
-/
theorem crt_Q_bound (d : ℕ) (_hd : 2 ≤ d)
    (M : ℤ) (hM : M ≤ ↑(monMstar d)) (hM_nn : 0 ≤ M)
    (K : ℕ) (hK : (K : ℤ) ≤ ↑(monKstar d)) (_hK_pos : 0 < K) :
    (M + ↑K).toNat / d.factorial + 1 ≤ monQstar d := by
  exact Nat.succ_le_succ ( Nat.div_le_div_right <| by linarith [ Int.toNat_of_nonneg ( add_nonneg hM_nn ( Nat.cast_nonneg K ) ) ] )

set_option maxHeartbeats 6400000 in
/-- The sharper monomial bound using the CRT residue datum.
    For d ≥ 2, θ_{X^d} ≤ monBound d. -/
theorem monomial_crt_bound (d : ℕ) (hd : 2 ≤ d) :
    IsThreshold (monomialPoly d) (monBound d) := by
  set p := monomialPoly d with hp_def
  have hd1 : 1 ≤ d := by omega
  have hA : 0 < p.leadingCoeff := monomialPoly_leadingCoeff_pos d hd1
  have hd_nat : 1 ≤ p.natDegree := monomialPoly_natDegree_pos d hd1
  have hnd : p.natDegree = d := monomialPoly_natDegree d hd1
  set a := d.factorial with ha_def
  have ha_pos : 0 < a := Nat.factorial_pos d
  have ha_eq : (a : ℤ) = polyA p := by
    rw [ha_def, hp_def, monomialPoly_polyA d hd1]
  -- === Get CRT datum ===
  obtain ⟨R, hR_emax, hR_card, hE_pos⟩ := monomial_crt_residue_datum d hd
  -- === Get canonical signed block ===
  obtain ⟨B, hB_L'⟩ := canonical_signed_block_bound p hd_nat
  have hB_L : B.L ≤ lambdaD d := hnd ▸ hB_L'
  -- === Tau parameters ===
  set T₀ := explicitTailParam p 1 with hT₀_def
  have hT₀_tau : TauProp p 1 T₀ := explicit_tau_bound p 1 hA hd_nat
  set T_res := explicitTailParam p (R.eMax + 1) with hT_res_def
  have hT_res_tau : TauProp p (R.eMax + 1) T_res := explicit_tau_bound p (R.eMax + 1) hA hd_nat
  set T_blk := explicitTailParam p (B.L + 1) with hT_blk_def
  have hT_blk_tau : TauProp p (B.L + 1) T_blk := explicit_tau_bound p (B.L + 1) hA hd_nat
  have hT₀_le_res : T₀ ≤ T_res := explicitTailParam_mono p 1 (R.eMax + 1) (by omega)
  have hT₀_le_blk : T₀ ≤ T_blk := explicitTailParam_mono p 1 (B.L + 1) (by omega)
  -- === R₀ ===
  set R₀ := a * ((T_res + 1 + a - 1) / a) with hR₀_def
  have hceil := ceil_mul_bound a T_res ha_pos
  have hR₀_ge : T_res + 1 ≤ R₀ := hceil.1
  have hR₀_le : R₀ ≤ T_res + a := hceil.2.1
  have hR₀_div : (a : ℤ) ∣ (R₀ : ℤ) := by exact_mod_cast hceil.2.2
  -- === K ===
  set K := (p.eval (T₀ : ℤ)).toNat with hK_def
  have hT₀_pos : 0 < p.eval (T₀ : ℤ) := tauProp_pos (by omega) hT₀_tau le_rfl
  have hK_pos : 0 < K := by omega
  have hK_eq : (K : ℤ) = p.eval (T₀ : ℤ) := Int.toNat_of_nonneg (le_of_lt hT₀_pos)
  have hK_val : (K : ℤ) = (monKstar d : ℤ) := by
    rw [hK_eq]; show (monomialPoly d).eval (explicitTailParam (monomialPoly d) 1 : ℤ) = _
    rw [monomial_K_eq d hd]; simp [monKstar]
  -- === Nonneg residue sums ===
  have hR₀_nonneg : ∀ r : Fin a, 0 ≤ ∑ e ∈ R.F r, p.eval ((R₀ : ℤ) + ↑e) := by
    intro r
    exact Finset.sum_nonneg fun e he => le_of_lt
      (tauProp_pos (by omega) hT₀_tau (by omega))
  -- === Y ===
  set Y := max (R₀ + R.eMax + 2) (T_blk + 1) with hY_def
  have hY_res : R₀ + R.E.sup id + 2 ≤ Y := le_max_left _ _
  have hY_blk : T_blk + 1 ≤ Y := le_max_right _ _
  have hY_le : Y ≤ monYstar d := crt_Y_bound d hd R hR_emax R₀ hR₀_le B hB_L
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
      Y hY_res K hK_pos hR₀_nonneg
  -- === Index bound ===
  have hI_ge : ∀ i ∈ I, T₀ + 1 ≤ i :=
    construction_indices_ge p a ha_pos R B R₀ Y Q T₀ (by omega) hY_res
  -- === Positivity ===
  have h_pos : ∀ n : ℕ, T₀ ≤ n → 0 < p.eval (n : ℤ) :=
    fun n hn => tauProp_pos (by omega) hT₀_tau hn
  -- === Doubling ===
  have hDoubling : ∀ u v : ℕ, T₀ ≤ u → u ∉ I → v ∉ I → u < v →
      (∀ w, u < w → w < v → w ∈ I) → p.eval (v : ℤ) ≤ 2 * p.eval (u : ℤ) :=
    crt_doubling p a ha_pos R B hE_pos T₀ hT₀_tau T_res hT_res_tau T_blk hT_blk_tau
      hT₀_le_res hT₀_le_blk R₀ hR₀_ge Y hY_res hY_blk Q
  -- === Apply isThreshold_of_data ===
  have hThreshold : IsThreshold p C₀.toNat :=
    isThreshold_of_data p T₀ K hK_eq I C₀ hI_ge hI_rep h_pos hDoubling
  -- === Bound tracking ===
  have hM_nn : 0 ≤ M := by
    exact Finset.le_sup'_of_le k (Finset.mem_univ ⟨0, ha_pos⟩) (hR₀_nonneg ⟨0, ha_pos⟩)
  have hM_le : M ≤ ↑(monMstar d) :=
    crt_M_bound d hd R hR_emax hR_card R₀ hR₀_le hR₀_ge hR₀_nonneg
  have hK_le : (K : ℤ) ≤ ↑(monKstar d) := by omega
  have hQ_le : Q - 1 ≤ monQstar d := by
    show (M + ↑K).toNat / a + 1 ≤ monQstar d
    exact crt_Q_bound d hd M hM_le hM_nn K hK_le hK_pos
  have hC₀_le : C₀ ≤ ↑(monBound d) :=
    crt_C0_bound d hd B hB_L Y hY_le Q hQ_le M hM_le C₁ rfl C₀ rfl
  -- === Conclude ===
  exact isThreshold_mono hThreshold (by omega)

end NatScope


/-! ===== Numerical Bound: monBound d ≤ (200 * d) ^ (d ^ 3) ===== -/

open Finset BigOperators

/-
If d ≥ 3, then d · 2^(4d) ≤ 3^(d²).
-/
theorem d_mul_pow4d_le_pow_sq (d : ℕ) (hd : 3 ≤ d) : d * 2 ^ (4 * d) ≤ 3 ^ (d ^ 2) := by
  induction' hd with k hk <;> norm_num [ Nat.pow_succ', pow_mul', Nat.pow_mul ] at *;
  ring_nf at *;
  nlinarith [ show 3 ^ k > k by exact Nat.recOn k ( by norm_num ) fun n ihn ↦ by rw [ pow_succ' ] ; nlinarith [ ihn, Nat.one_le_pow n 3 zero_lt_three ], show 2 ^ ( k * 4 ) > 0 by positivity, show 3 ^ k ^ 2 > 0 by positivity, show 3 ^ k * 3 ^ k ^ 2 > 0 by positivity ]

/-
If d ≥ 3, then 32d ≤ 5^d.
-/
theorem thirtytwo_d_le_pow5 (d : ℕ) (hd : 3 ≤ d) : 32 * d ≤ 5 ^ d := by
  induction' hd with k hk <;> norm_num [ Nat.pow_succ' ] at * ; linarith [ pow_pos ( show 0 < 5 by norm_num ) k ]

/-
If n ≥ 3, then 16^n + 32^n ≤ 34^n.
-/
theorem pow16_add_pow32_le (n : ℕ) (hn : 3 ≤ n) : 16 ^ n + 32 ^ n ≤ 34 ^ n := by
  induction hn <;> simp_all +decide [ pow_succ' ];
  grind +revert

/-
For d ≥ 1, d! ≤ d^d.
-/
theorem factorial_le_self_pow (d : ℕ) (_hd : 1 ≤ d) : d.factorial ≤ d ^ d :=
  Nat.factorial_le_pow d

/-
M_d := d(d-1)/2 + 2d + 2. Then M_d + 1 ≤ 2d² for d ≥ 3.
-/
theorem Md_add_one_le (d : ℕ) (hd : 3 ≤ d) :
    d * (d - 1) / 2 + 2 * d + 2 + 1 ≤ 2 * d ^ 2 := by
  nlinarith [ Nat.div_mul_le_self ( d * ( d - 1 ) ) 2, Nat.sub_add_cancel ( by linarith : 1 ≤ d ) ]

/-
2^(M_d) + 1 ≤ 4^(d²) for d ≥ 3.
-/
theorem pow2_Md_add_one_le (d : ℕ) (hd : 3 ≤ d) :
    2 ^ (d * (d - 1) / 2 + 2 * d + 2) + 1 ≤ 4 ^ (d ^ 2) := by
  have h_bound : 2 ^ (d * (d - 1) / 2 + 2 * d + 2) + 1 ≤ 2 ^ (d * (d - 1) / 2 + 2 * d + 3) := by
    grind +extAll;
  refine le_trans h_bound ?_;
  convert Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( show d * ( d - 1 ) / 2 + 2 * d + 3 ≤ 2 * d ^ 2 by linarith [ Md_add_one_le d hd ] ) using 1 ; norm_num [ pow_mul ]

/-! ## Section 4: Component bounds for d ≥ 3 -/

/-
A_d ≤ d! · (6d)^(d²) for d ≥ 3.
-/
theorem monMstar_le (d : ℕ) (hd : 3 ≤ d) :
    monMstar d ≤ d.factorial * (6 * d) ^ (d ^ 2) := by
  unfold monMstar;
  suffices h_cancel : d * 2 ^ d * (8 * d * 2 ^ d) ^ d * (d.factorial) ^ (d - 1) ≤ (6 * d) ^ (d ^ 2) by
    convert Nat.mul_le_mul_left ( d.factorial ) h_cancel using 1 ; ring_nf;
    cases d <;> simp_all +decide [ pow_succ', mul_assoc ];
  have h_factorial_bound : (d.factorial) ^ (d - 1) ≤ d ^ (d * (d - 1)) := by
    rw [ pow_mul ];
    gcongr;
    exact Nat.factorial_le_pow d;
  have h_subst : d * 2 ^ d * (8 * d * 2 ^ d) ^ d * d ^ (d * (d - 1)) ≤ (6 * d) ^ (d ^ 2) := by
    suffices h_simplify : d ^ (d ^ 2 + 1) * 2 ^ (d ^ 2 + 4 * d) ≤ (6 * d) ^ (d ^ 2) by
      convert h_simplify using 1 ; ring_nf;
      rw [ show d ^ 2 = d + d * ( d - 1 ) by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ d ) ] ] ; norm_num [ pow_add, pow_mul', mul_assoc ] ; ring_nf;
      norm_num [ pow_mul', ← mul_pow ] ; ring_nf ; norm_num;
    have h_exp_bound : d ^ (d ^ 2 + 1) * 2 ^ (d ^ 2 + 4 * d) ≤ d ^ (d ^ 2) * 3 ^ (d ^ 2) * 2 ^ (d ^ 2) := by
      convert Nat.mul_le_mul_left ( d ^ d ^ 2 * 2 ^ d ^ 2 ) ( d_mul_pow4d_le_pow_sq d hd ) using 1 ; ring;
      ring;
    convert h_exp_bound using 1 ; ring_nf;
    norm_num [ mul_assoc, ← mul_pow ];
  exact le_trans ( Nat.mul_le_mul_left _ h_factorial_bound ) h_subst

/-
B_d ≤ (8d)^(d²) for d ≥ 3.
-/
theorem monQstar_le (d : ℕ) (hd : 3 ≤ d) :
    monQstar d ≤ (8 * d) ^ (d ^ 2) := by
  have h_monMstar_le : monMstar d ≤ d.factorial * (6 * d) ^ (d ^ 2) := by
    exact monMstar_le d hd;
  nontriviality;
  have h_three_mul_6_pow_le : 3 * (6 * d) ^ (d ^ 2) ≤ (8 * d) ^ (d ^ 2) := by
    have h_div : 3 ≤ (4 / 3 : ℝ) ^ (d ^ 2) := by
      exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) ( Nat.pow_le_pow_left hd 2 ) );
    convert mul_le_mul_of_nonneg_right h_div ( pow_nonneg ( by positivity : 0 ≤ ( 6 * d : ℝ ) ) ( d ^ 2 ) ) using 1 ; norm_num [ ← mul_pow ] ; ring_nf;
    norm_cast;
  have h_monKstar_le : (6 * d) ^ d ≤ (6 * d) ^ (d ^ 2) := by
    exact Nat.pow_le_pow_right ( by positivity ) ( by nlinarith );
  unfold monQstar;
  unfold monKstar;
  exact Nat.succ_le_of_lt ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.factorial_pos d, pow_pos ( by linarith : 0 < 6 * d ) d, pow_pos ( by linarith : 0 < 6 * d ) ( d ^ 2 ) ] )

/-
B_d · E_d ≤ (32d)^(d²) for d ≥ 3.
-/
theorem monQE_le (d : ℕ) (hd : 3 ≤ d) :
    monQstar d * (lambdaD d + 1) ≤ (32 * d) ^ (d ^ 2) := by
  have h_subst : monQstar d * (lambdaD d + 1) ≤ (8 * d) ^ (d ^ 2) * 4 ^ (d ^ 2) := by
    apply Nat.mul_le_mul;
    · convert monQstar_le d hd using 1;
    · exact pow2_Md_add_one_le d hd;
  exact h_subst.trans_eq ( by rw [ ← mul_pow ] ; ring )

/-
D_d ≤ (16d)^(d²) for d ≥ 3.
-/
theorem monYstar_le (d : ℕ) (hd : 3 ≤ d) :
    monYstar d ≤ (16 * d) ^ (d ^ 2) := by
  have h_step2 : monYstar d ≤ 8 * d * (2 * (4 * d) ^ (d ^ 2)) := by
    have h_step2 : d.factorial * 2 ^ d + lambdaD d ≤ 2 * (4 * d) ^ (d ^ 2) := by
      have h_bound : d.factorial * 2 ^ d ≤ (4 * d) ^ (d ^ 2) ∧ lambdaD d ≤ (4 * d) ^ (d ^ 2) := by
        constructor;
        · refine' le_trans ( Nat.mul_le_mul ( factorial_le_self_pow d ( by linarith ) ) ( Nat.pow_le_pow_left ( show 2 ≤ 4 by decide ) _ ) ) _;
          rw [ ← mul_pow ];
          exact Nat.pow_le_pow_left ( by nlinarith ) _ |> le_trans <| Nat.pow_le_pow_right ( by positivity ) <| by nlinarith;
        · have h_exp : 2 ^ (d * (d - 1) / 2 + 2 * d + 2) ≤ 4 ^ (d ^ 2) := by
            exact Nat.le_of_lt ( pow2_Md_add_one_le d hd |> lt_of_lt_of_le ( Nat.lt_succ_self _ ) );
          exact h_exp.trans ( Nat.pow_le_pow_left ( by linarith ) _ );
      linarith;
    exact Nat.mul_le_mul_left _ h_step2;
  refine le_trans h_step2 ?_;
  rw [ show ( 16 * d ) = 4 * d * 4 by ring, mul_pow ];
  rw [ show ( 4 * d * 4 ) = 4 * ( 4 * d ) by ring, mul_pow ];
  rw [ mul_pow ];
  suffices h_div : 16 * d ≤ 4 ^ (d ^ 2) by
    nlinarith [ show 0 < 4 ^ d ^ 2 * d ^ d ^ 2 by positivity ];
  induction hd <;> norm_num [ Nat.pow_succ, Nat.pow_mul ] at *;
  rename_i k hk ih;
  refine' le_trans _ ( Nat.mul_le_mul ( Nat.pow_le_pow_left ( Nat.mul_le_mul ( Nat.pow_le_pow_right ( by decide ) hk ) le_rfl ) _ ) ( Nat.mul_le_mul ( Nat.pow_le_pow_right ( by decide ) hk ) le_rfl ) );
  exact Nat.recOn k ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; nlinarith;

/-
D_d + B_d · E_d ≤ (34d)^(d²) for d ≥ 3.
-/
theorem monYQE_le (d : ℕ) (hd : 3 ≤ d) :
    monYstar d + monQstar d * (lambdaD d + 1) ≤ (34 * d) ^ (d ^ 2) := by
  have h_bound : monYstar d + monQstar d * (lambdaD d + 1) ≤ (16 * d) ^ (d ^ 2) + (32 * d) ^ (d ^ 2) := by
    exact add_le_add ( monYstar_le d hd ) ( monQE_le d hd );
  refine le_trans h_bound ?_;
  suffices h_factor : 16 ^ (d ^ 2) + 32 ^ (d ^ 2) ≤ 34 ^ (d ^ 2) by
    convert Nat.mul_le_mul_right ( d ^ d ^ 2 ) h_factor using 1 <;> ring;
  exact pow16_add_pow32_le _ ( by nlinarith )

/-
C_d ≤ (200d)^(d³) for d ≥ 3.
-/
theorem monBound_le_200d_pow_ge3 (d : ℕ) (hd : 3 ≤ d) :
    monBound d ≤ (200 * d) ^ (d ^ 3) := by
  set n := d ^ 2
  set r := d ^ 3
  have hn_le_r : n ≤ r := by
    exact Nat.pow_le_pow_right ( by linarith ) ( by linarith );
  have hA : monMstar d ≤ (6 * d) ^ r := by
    have hA : monMstar d ≤ d.factorial * (6 * d) ^ n := by
      exact monMstar_le d hd;
    refine le_trans hA ?_;
    refine' le_trans ( Nat.mul_le_mul_right _ ( show d.factorial ≤ ( 6 * d ) ^ ( d ^ 3 - d ^ 2 ) from _ ) ) _;
    · refine' le_trans _ ( Nat.pow_le_pow_right ( by positivity ) ( show d ^ 3 - d ^ 2 ≥ d by exact le_tsub_of_add_le_left ( by nlinarith only [ hd, pow_succ' d 2 ] ) ) );
      refine' le_trans ( factorial_le_self_pow d ( by linarith ) ) _;
      gcongr ; linarith;
    · rw [ ← pow_add, Nat.sub_add_cancel hn_le_r ]
  have hBE : monQstar d * (lambdaD d + 1) ≤ (32 * d) ^ n := by
    exact monQE_le d hd
  have hDY : monYstar d + monQstar d * (lambdaD d + 1) ≤ (34 * d) ^ n := by
    convert monYQE_le d hd using 1;
  have hC : monBound d ≤ (6 * d) ^ r + (32 * d) ^ n * (34 * d) ^ r := by
    have hC : monBound d ≤ (6 * d) ^ r + (32 * d) ^ n * ((34 * d) ^ n) ^ d := by
      exact add_le_add hA ( Nat.mul_le_mul hBE ( Nat.pow_le_pow_left hDY _ ) );
    convert hC using 2 ; ring;
  have hBE_r : (32 * d) ^ n * (34 * d) ^ r ≤ (170 * d) ^ r := by
    have hBE_r : (32 * d) ^ n ≤ 5 ^ r := by
      have hBE_r : (32 * d) ^ n ≤ 5 ^ (d * n) := by
        rw [ pow_mul ] ; gcongr ; nlinarith [ thirtytwo_d_le_pow5 d hd ];
      grind;
    exact le_trans ( Nat.mul_le_mul_right _ hBE_r ) ( by rw [ ← mul_pow ] ; ring_nf; norm_num );
  have hC_final : monBound d ≤ 2 * (170 * d) ^ r := by
    linarith [ pow_le_pow_left' ( show 6 * d ≤ 170 * d by linarith ) r ];
  have h_final : 2 * (170 * d) ^ r ≤ (200 * d) ^ r := by
    have h_final : 2 * 170 ^ r ≤ 200 ^ r := by
      exact Nat.le_induction ( by decide ) ( fun k hk ih ↦ by rw [ pow_succ' ] ; rw [ pow_succ' ] ; linarith [ pow_pos ( by decide : 0 < 170 ) k, pow_le_pow_left' ( by decide : 170 ≤ 200 ) k ] ) _ ( show r ≥ 5 by exact le_trans ( by decide ) ( Nat.pow_le_pow_left hd 3 ) );
    rw [ mul_pow, mul_pow ] ; nlinarith [ pow_pos ( by linarith : 0 < d ) r ] ;
  exact hC_final.trans h_final

/-
C_2 ≤ 400^8 = (200·2)^(2³).
-/
theorem monBound_le_200d_pow_eq2 : monBound 2 ≤ (200 * 2) ^ (2 ^ 3) := by
  decide

/-- For d ≥ 2, monBound d ≤ (200d)^(d³). -/
theorem monBound_le_200d_pow (d : ℕ) (hd : 2 ≤ d) :
    monBound d ≤ (200 * d) ^ (d ^ 3) := by
  obtain rfl | hd3 := hd.eq_or_lt
  · exact monBound_le_200d_pow_eq2
  · exact monBound_le_200d_pow_ge3 d hd3

/-! ## Helper lemmas for the d ≥ 9 bound -/

/-
For n ≥ k ≥ 1, 2·k^n ≤ (k+1)^n. Follows from (k+1)^k ≥ 2·k^k by the binomial theorem.
-/
theorem two_mul_pow_le_succ_pow (k n : ℕ) (hk : 1 ≤ k) (hn : k ≤ n) :
    2 * k ^ n ≤ (k + 1) ^ n := by
      have h_ind : ∀ m ≥ k, 2 * k ^ m ≤ (k + 1) ^ m := by
        intro m hm
        induction' hm with m ih;
        · rw [ two_mul, add_pow ];
          rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.sum_range_succ ];
          simp +decide [pow_succ', Nat.mul_comm] at *;
        · simpa only [ pow_succ' ] using by nlinarith [ pow_pos ( zero_lt_one.trans_le hk ) m ] ;
      exact h_ind n hn

/-
Factorial compression for d ≥ 9: 2^{d+1} · d! ≤ d^d.
-/
theorem factorial_compression_ge9 (d : ℕ) (hd : 9 ≤ d) :
    2 ^ (d + 1) * d.factorial ≤ d ^ d := by
      induction hd <;> simp_all +decide [ Nat.factorial_succ, pow_succ' ];
      rename_i k hk ih;
      -- By the binomial theorem, $(k + 1)^k \geq k^k + k \cdot k^{k-1} = k^k + k^k = 2k^k$.
      have h_binom : (k + 1) ^ k ≥ 2 * k ^ k := by
        exact two_mul_pow_le_succ_pow k k ( by linarith ) ( by linarith );
      nlinarith [ Nat.zero_le ( 2 ^ k * k.factorial ) ]

/-
Exponential absorption: 5d · 2^{d-1} ≤ 3^d for d ≥ 9.
-/
theorem exp_absorption_ge9 (d : ℕ) (hd : 9 ≤ d) :
    5 * d * 2 ^ (d - 1) ≤ 3 ^ d := by
      induction' hd with k hk <;> norm_num [ Nat.pow_succ', pow_add ] at *;
      rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ' ] at * ; nlinarith [ pow_pos ( show 0 < 2 by decide ) k ]

/-
Comparison with 3^{d²}: d · 2^{d²+4d+3} ≤ 3^{d²} for d ≥ 9.
-/
theorem comparison_3_sq_ge9 (d : ℕ) (hd : 9 ≤ d) :
    d * 2 ^ (d ^ 2 + 4 * d + 3) ≤ 3 ^ (d ^ 2) := by
      induction' hd with k hk <;> norm_num [ Nat.pow_succ' ] at *;
      -- It suffices to show that $(k + 1) / k * 2^{2k + 5} ≤ 3^{2k + 1}$.
      suffices h_suff : (k + 1 : ℝ) / k * 2 ^ (2 * k + 5) ≤ 3 ^ (2 * k + 1) by
        rw [ div_mul_eq_mul_div, div_le_iff₀ ] at h_suff <;> norm_cast at * <;> ring_nf at * <;> try linarith;
        norm_num [ pow_mul ] at *;
        nlinarith [ show 0 < ( 2 ^ k ) ^ 4 * 2 ^ k ^ 2 by positivity, show 0 < ( 2 ^ k ) ^ 2 * 2 ^ k ^ 2 by positivity ];
      -- Since $(k + 1) / k \leq 2$ for $k \geq 9$, it suffices to show that $2 * 2^{2k + 5} \leq 3^{2k + 1}$.
      suffices h_suff' : 2 * 2 ^ (2 * k + 5) ≤ 3 ^ (2 * k + 1) by
        exact le_trans ( mul_le_mul_of_nonneg_right ( show ( k + 1 : ℝ ) / k ≤ 2 by rw [ div_le_iff₀ ] <;> norm_cast <;> linarith ) ( by positivity ) ) ( mod_cast h_suff' );
      rcases k with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> norm_num [ Nat.pow_succ', Nat.pow_mul ] at *;
      linarith [ pow_pos ( show 0 < 4 by norm_num ) k, pow_le_pow_left' ( show 4 ≤ 9 by norm_num ) k ]

/-
The A_d bound for d ≥ 9: monMstar d · 2^{d²} ≤ (5d)^{d²}.
-/
theorem monMstar_le_ge9 (d : ℕ) (hd : 9 ≤ d) :
    monMstar d * 2 ^ (d ^ 2) ≤ (5 * d) ^ (d ^ 2) := by
      have h_bound : d * 2 ^ d * (8 * d * d.factorial * 2 ^ d) ^ d * 2 ^ d ^ 2 ≤ (5 * d) ^ d ^ 2 := by
        have h1 : 8 * d * d.factorial * 2 ^ d ≤ 4 * d ^ (d + 1) := by
          have h_factorial : 2 ^ (d + 1) * d.factorial ≤ d ^ d := by
            exact factorial_compression_ge9 d hd;
          convert Nat.mul_le_mul_right ( 4 * d ) h_factorial using 1 <;> ring
        have h2 : d * 2 ^ d * (4 * d ^ (d + 1)) ^ d * 2 ^ d ^ 2 ≤ (5 * d) ^ d ^ 2 := by
          -- We can divide both sides by $d^{d^2}$ to get $d^{d+1} * 2^{d^2 + 3d} \leq 5^{d^2}$.
          suffices h_div : d ^ (d + 1) * 2 ^ (d ^ 2 + 3 * d) ≤ 5 ^ d ^ 2 by
            convert Nat.mul_le_mul_right ( d ^ d ^ 2 ) h_div using 1 <;> ring_nf;
            norm_num [ pow_mul', mul_assoc, mul_comm, mul_left_comm ];
            exact Or.inl ( by rw [ show ( 8 : ℕ ) = 2 * 4 by norm_num, mul_pow ] ; ring );
          -- We can divide both sides by $2^{d^2}$ to get $d^{d+1} * 2^{3d} \leq (5/2)^{d^2}$.
          suffices h_div : d ^ (d + 1) * 2 ^ (3 * d) ≤ (5 / 2 : ℝ) ^ (d ^ 2) by
            rw [ div_pow, le_div_iff₀ ] at h_div <;> norm_cast at * ; ring_nf at * ; aesop;
            positivity;
          -- We can divide both sides by $2^{d^2}$ to get $d^{d+1} * 2^{3d} \leq (5/2)^{d^2}$, which simplifies to $d^{d+1} \leq (5/2)^{d^2 - 3d}$.
          suffices h_div : d ^ (d + 1) ≤ (5 / 2 : ℝ) ^ (d ^ 2 - 3 * d) by
            rw [ show ( 5 / 2 : ℝ ) ^ d ^ 2 = ( 5 / 2 : ℝ ) ^ ( d ^ 2 - 3 * d ) * ( 5 / 2 : ℝ ) ^ ( 3 * d ) by rw [ ← pow_add, Nat.sub_add_cancel ( by nlinarith ) ] ] ; gcongr ; norm_num;
          -- We can take the natural logarithm of both sides to get $(d + 1) \ln d \leq (d^2 - 3d) \ln (5/2)$.
          suffices h_ln : (d + 1) * Real.log d ≤ (d ^ 2 - 3 * d) * Real.log (5 / 2) by
            rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_pow, Real.log_pow ];
            rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith;
          -- We'll use that $Real.log d \leq Real.log 9 + (d - 9) / 9$ for $d \geq 9$.
          have h_log_bound : Real.log d ≤ Real.log 9 + (d - 9) / 9 := by
            rw [ Real.log_le_iff_le_exp, Real.exp_add, Real.exp_log ] <;> norm_num <;> try linarith;
            linarith [ Real.add_one_le_exp ( ( d - 9 ) / 9 ) ];
          -- We'll use that $Real.log 9 \leq 2.2$ and $Real.log (5 / 2) \geq 0.9$.
          have h_log_approx : Real.log 9 ≤ 2.2 ∧ Real.log (5 / 2) ≥ 0.9 := by
            norm_num [ Real.log_le_iff_le_exp, Real.le_log_iff_exp_le ];
            constructor <;> rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
            · rw [ le_div_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_le_iff_le_exp ];
              have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 11 = ( Real.exp 1 ) ^ 11 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ );
            · rw [ div_le_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.le_log_iff_exp_le ];
              have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 9 = ( Real.exp 1 ) ^ 9 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
          nlinarith [ show ( d : ℝ ) ≥ 9 by norm_cast, sq_nonneg ( d - 9 : ℝ ) ];
        exact le_trans ( Nat.mul_le_mul_right _ ( Nat.mul_le_mul_left _ ( Nat.pow_le_pow_left h1 _ ) ) ) h2;
      exact h_bound

/-
Helper: monMstar d / d! ≤ d^{d²+1} * 2^{4d+1} for d ≥ 9.
-/
theorem monMstar_div_factorial_le_ge9 (d : ℕ) (hd : 9 ≤ d) :
    monMstar d / d.factorial ≤ d ^ (d ^ 2 + 1) * 2 ^ (4 * d + 1) := by
      -- Simplify the expression by cancelling out common terms.
      have h_simp : d * 2 ^ d * (8 * d * d.factorial * 2 ^ d) ^ d / d.factorial = d * 2 ^ d * (8 * d * 2 ^ d) ^ d * d.factorial ^ (d - 1) := by
        rcases d with ( _ | _ | d ) <;> simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm ];
        exact Nat.div_eq_of_eq_mul_left ( Nat.factorial_pos _ ) ( by push_cast [ pow_succ' ] ; ring );
      -- Use factorial compression to bound $d!^{d-1}$
      have h_factorialCompression : d.factorial ^ (d - 1) ≤ (d ^ d / 2 ^ (d + 1)) ^ (d - 1) := by
        gcongr;
        exact Nat.le_div_iff_mul_le ( by positivity ) |>.2 ( by linarith [ factorial_compression_ge9 d hd ] );
      -- Substitute the factorial compression bound into the simplified expression.
      have h_subst : d * 2 ^ d * (8 * d * 2 ^ d) ^ d * (d ^ d / 2 ^ (d + 1)) ^ (d - 1) ≤ d ^ (d ^ 2 + 1) * 2 ^ (4 * d + 1) := by
        -- Simplify the expression by cancelling out common terms and using properties of exponents.
        have h_simp : d * 2 ^ d * (8 * d * 2 ^ d) ^ d * (d ^ d / 2 ^ (d + 1)) ^ (d - 1) ≤ d * 2 ^ d * (8 * d * 2 ^ d) ^ d * (d ^ d) ^ (d - 1) / 2 ^ ((d + 1) * (d - 1)) := by
          rw [ Nat.le_div_iff_mul_le ( by positivity ) ];
          rw [ mul_assoc ];
          rw [ pow_mul ];
          rw [ ← mul_pow ] ; gcongr ; exact Nat.div_mul_le_self _ _;
        refine le_trans h_simp ?_;
        rw [ Nat.div_le_iff_le_mul_add_pred ] <;> norm_num;
        ring_nf;
        rw [ show d ^ 2 = d * ( d - 1 ) + d by nlinarith only [ Nat.sub_add_cancel ( by linarith : 1 ≤ d ) ] ] ; ring_nf;
        rcases d with ( _ | _ | d ) <;> simp_all +decide [ pow_succ, pow_mul ] ; ring_nf;
        norm_num [ pow_mul', ← mul_pow ] ; ring_nf;
        norm_num [ pow_mul' ];
      exact h_simp.symm ▸ le_trans ( Nat.mul_le_mul_left _ h_factorialCompression ) h_subst

/-
Helper: 8 * (6d)^d ≤ d^{d²} for d ≥ 9.
-/
theorem eight_mul_monKstar_le_ge9 (d : ℕ) (hd : 9 ≤ d) :
    8 * monKstar d ≤ d ^ (d ^ 2) := by
      have h_bound : 8 * (6 * d) ^ d ≤ d ^ (d + 3) * d ^ d := by
        ring_nf;
        rw [ pow_mul ];
        nlinarith [ show 0 < d ^ d by positivity, show 6 ^ d ≤ d ^ d by gcongr ; linarith, show d ^ 3 ≥ 8 * 6 by nlinarith [ pow_succ' d 2 ] ];
      exact le_trans h_bound ( by rw [ ← pow_add ] ; exact pow_le_pow_right₀ ( by linarith ) ( by nlinarith only [ hd ] ) )

/-
The B_d bound for d ≥ 9: monQstar d · 2^{d²} ≤ (3d)^{d²}.
-/
theorem monQstar_le_ge9 (d : ℕ) (hd : 9 ≤ d) :
    monQstar d * 2 ^ (d ^ 2) ≤ (3 * d) ^ (d ^ 2) := by
      -- By definition of $monQstar$, we have $monQstar d = (monMstar d + monKstar d) / d.factorial + 1$.
      have h_monQstar_def : monQstar d = (monMstar d + monKstar d) / d.factorial + 1 := by
        rfl;
      -- By monMstar_div_factorial_le_ge9 and eight_mul_monKstar_le_ge9, we have:
      have h_bounds : (monMstar d / d.factorial) * 2 ^ (d ^ 2) ≤ (d ^ (d ^ 2 + 1) * 2 ^ (4 * d + 1)) * 2 ^ (d ^ 2) ∧ (monKstar d + 1) * 2 ^ (d ^ 2) ≤ (d ^ (d ^ 2) / 4) * 2 ^ (d ^ 2) := by
        apply And.intro;
        · exact Nat.mul_le_mul_right _ ( monMstar_div_factorial_le_ge9 d hd );
        · gcongr;
          refine' Nat.le_div_iff_mul_le zero_lt_four |>.2 _;
          have := eight_mul_monKstar_le_ge9 d hd;
          nlinarith [ Nat.pow_le_pow_right ( by linarith : 1 ≤ d ) ( by nlinarith : d ^ 2 ≥ 2 ) ];
      -- By combining the bounds, we get:
      have h_combined : (monMstar d / d.factorial + monKstar d + 1) * 2 ^ (d ^ 2) ≤ (3 * d) ^ (d ^ 2) / 2 := by
        have h_combined : d ^ (d ^ 2 + 1) * 2 ^ (4 * d + 1) * 2 ^ (d ^ 2) ≤ (3 * d) ^ (d ^ 2) / 4 := by
          have h_term1 : d * 2 ^ (d ^ 2 + 4 * d + 3) ≤ 3 ^ (d ^ 2) := by
            apply comparison_3_sq_ge9 d hd;
          rw [ Nat.le_div_iff_mul_le ] <;> ring_nf at * <;> norm_num at *;
          nlinarith [ pow_pos ( by linarith : 0 < d ) ( d ^ 2 ) ];
        have h_combined : d ^ (d ^ 2) / 4 * 2 ^ (d ^ 2) ≤ (3 * d) ^ (d ^ 2) / 4 := by
          rw [ Nat.le_div_iff_mul_le ] <;> norm_num [ mul_pow ];
          nlinarith [ Nat.div_mul_le_self ( d ^ d ^ 2 ) 4, pow_pos ( show 0 < d by linarith ) ( d ^ 2 ), pow_pos ( show 0 < 2 by decide ) ( d ^ 2 ), pow_le_pow_left' ( show 2 ≤ 3 by decide ) ( d ^ 2 ) ];
        grind;
      refine le_trans ?_ ( h_combined.trans ( Nat.div_le_self _ _ ) );
      rw [ h_monQstar_def ];
      gcongr;
      exact Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.div_add_mod ( monMstar d ) ( d.factorial ), Nat.mod_lt ( monMstar d ) ( Nat.factorial_pos d ), Nat.factorial_pos d ] ;

/-
The E_d bound for d ≥ 9: (lambdaD d + 1) · 3^{d²} ≤ 5^{d²}.
-/
theorem lambdaD_succ_le_ge9 (d : ℕ) (hd : 9 ≤ d) :
    (lambdaD d + 1) * 3 ^ (d ^ 2) ≤ 5 ^ (d ^ 2) := by
      nontriviality;
      -- By induction on $d$ starting from $d=9$.
      have h_ind : ∀ d ≥ 9, 2 ^ (d * (d - 1) / 2 + 2 * d + 3) * 3 ^ (d ^ 2) ≤ 5 ^ (d ^ 2) := by
        intro d hd
        induction' hd with d hd ih;
        · decide +revert;
        · -- We'll use that $2^{d+2} * 3^{2d+1} \leq 5^{2d+1}$ for $d \geq 9$.
          have h_exp : 2 ^ (d + 2) * 3 ^ (2 * d + 1) ≤ 5 ^ (2 * d + 1) := by
            -- We can divide both sides by $3^{2d+1}$ to get $2^{d+2} \leq \left(\frac{5}{3}\right)^{2d+1}$.
            suffices h_div : 2 ^ (d + 2) ≤ (5 / 3 : ℝ) ^ (2 * d + 1) by
              rw [ div_pow, le_div_iff₀ ] at h_div <;> norm_cast at * ; aesop;
            -- We can take the natural logarithm of both sides to simplify the inequality.
            suffices h_ln : (d + 2) * Real.log 2 ≤ (2 * d + 1) * Real.log (5 / 3) by
              rw [ ← @Real.log_le_log_iff ( 2 ^ ( d + 2 ) ) ( ( 5 / 3 ) ^ ( 2 * d + 1 ) ) ( by positivity ) ( by positivity ), Real.log_pow, Real.log_pow ] ; aesop;
            have h_ln : Real.log (5 / 3) ≥ (2 / 3) * Real.log 2 := by
              rw [ div_mul_eq_mul_div, ge_iff_le, div_le_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_le_log ];
            nlinarith [ Real.log_pos one_lt_two, show ( d : ℝ ) ≥ 9 by norm_cast ];
          convert Nat.mul_le_mul ih h_exp using 1 <;> norm_num [ Nat.succ_eq_add_one, Nat.mul_succ, pow_succ' ] <;> ring_nf;
          rw [ show ( d + d ^ 2 ) / 2 = d * ( d - 1 ) / 2 + d by exact Nat.div_eq_of_eq_mul_left zero_lt_two <| by nlinarith only [ Nat.sub_add_cancel ( by linarith [ Nat.succ_le_iff.mp hd ] : 1 ≤ d ), Nat.div_mul_cancel ( show 2 ∣ d * ( d - 1 ) from even_iff_two_dvd.mp <| Nat.even_mul_pred_self _ ) ] ] ; ring;
      refine le_trans ?_ ( h_ind d hd );
      gcongr;
      exact Nat.succ_le_of_lt ( pow_lt_pow_right₀ ( by decide ) ( Nat.lt_succ_self _ ) )

/-
The D_d bound for d ≥ 9: monYstar d ≤ d^{d²}.
-/
theorem monYstar_le_ge9 (d : ℕ) (hd : 9 ≤ d) :
    monYstar d ≤ d ^ (d ^ 2) := by
      -- First, we need to establish that $8d \cdot d! \cdot 2^d \leq \frac{d^{d^2}}{2}$ for $d \geq 9$.
      have h1 : 8 * d * d.factorial * 2 ^ d ≤ d ^ (d ^ 2) / 2 := by
        -- Using the factorial compression lemma, we have $d! \leq \frac{d^d}{2^{d+1}}$.
        have h_factorial_compression : d.factorial ≤ d ^ d / 2 ^ (d + 1) := by
          exact Nat.le_div_iff_mul_le ( by positivity ) |>.2 ( by linarith [ factorial_compression_ge9 d hd ] );
        nontriviality;
        rw [ Nat.le_div_iff_mul_le ] at * <;> norm_num [ pow_succ' ] at *;
        -- We'll use that $d \geq 9$ to show that $8d \cdot d^d \leq d^{d^2}$.
        have h_exp : 8 * d * d ^ d ≤ d ^ (d ^ 2) := by
          -- We can divide both sides by $d^d$ to get $8d \leq d^{d^2 - d}$.
          have h_div : 8 * d ≤ d ^ (d ^ 2 - d) := by
            exact le_trans ( by nlinarith ) ( Nat.pow_le_pow_right ( by linarith ) ( show d ^ 2 - d ≥ 2 by exact le_tsub_of_add_le_left ( by nlinarith ) ) );
          exact le_trans ( Nat.mul_le_mul_right _ h_div ) ( by rw [ ← pow_add, Nat.sub_add_cancel ( by nlinarith ) ] );
        ring_nf at *; nlinarith;
      -- Next, we need to establish that $8d \cdot 2^{d(d-1)/2 + 2d + 2} \leq \frac{d^{d^2}}{2}$ for $d \geq 9$.
      have h2 : 8 * d * 2 ^ (d * (d - 1) / 2 + 2 * d + 2) ≤ d ^ (d ^ 2) / 2 := by
        rw [ Nat.le_div_iff_mul_le ] <;> norm_num;
        -- We'll use that $8d \cdot 2^{d(d-1)/2 + 2d + 3} \leq d^{d^2}$ for $d \geq 9$.
        have h_exp : 8 * d * 2 ^ (d * (d - 1) / 2 + 2 * d + 3) ≤ d ^ (d * (d - 1) / 2 + 2 * d + 3) := by
          -- We can divide both sides by $2^{d(d-1)/2 + 2d + 3}$ to get $8d \leq (d/2)^{d(d-1)/2 + 2d + 3}$.
          suffices h_div : 8 * d ≤ (d / 2 : ℝ) ^ (d * (d - 1) / 2 + 2 * d + 3) by
            rw [ div_pow, le_div_iff₀ ] at h_div <;> norm_cast at * ; positivity;
          refine' le_trans _ ( pow_le_pow_right₀ ( by linarith [ show ( d : ℝ ) ≥ 9 by norm_cast ] ) ( show d * ( d - 1 ) / 2 + 2 * d + 3 ≥ d + 3 by nlinarith [ Nat.div_add_mod ( d * ( d - 1 ) ) 2, Nat.mod_lt ( d * ( d - 1 ) ) two_pos, Nat.sub_add_cancel ( by linarith : 1 ≤ d ) ] ) );
          refine' le_trans _ ( pow_le_pow_right₀ ( by linarith [ show ( d : ℝ ) ≥ 9 by norm_cast ] ) ( show d + 3 ≥ 6 by linarith ) ) ; ring_nf ; norm_num;
          nlinarith [ show ( d : ℝ ) ≥ 9 by norm_cast, pow_pos ( show ( d : ℝ ) > 0 by positivity ) 2, pow_pos ( show ( d : ℝ ) > 0 by positivity ) 3, pow_pos ( show ( d : ℝ ) > 0 by positivity ) 4, pow_pos ( show ( d : ℝ ) > 0 by positivity ) 5 ];
        refine le_trans ?_ ( h_exp.trans ?_ );
        · ring_nf; norm_num;
        · exact Nat.pow_le_pow_right ( by linarith ) ( by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ d ), Nat.div_mul_le_self ( d * ( d - 1 ) ) 2 ] );
      grind +locals

/-
For d ≥ 9, monBound d ≤ (4d)^{d³}.
-/
theorem monBound_le_4d_pow (d : ℕ) (hd : 9 ≤ d) :
    monBound d ≤ (4 * d) ^ (d ^ 3) := by
      have h_step1 : monQstar d * (lambdaD d + 1) * 2 ^ (d ^ 2) ≤ (5 * d) ^ (d ^ 2) := by
        have h_step4 : monQstar d * 2 ^ (d ^ 2) ≤ (3 * d) ^ (d ^ 2) := by
          apply monQstar_le_ge9 d hd
        have h_step5 : (lambdaD d + 1) * 3 ^ (d ^ 2) ≤ 5 ^ (d ^ 2) := by
          -- Apply the lemma `lambdaD_succ_le_ge9` with the given `hd`.
          apply lambdaD_succ_le_ge9 d hd
        have h_step6 : monQstar d * (lambdaD d + 1) * 2 ^ (d ^ 2) ≤ (5 * d) ^ (d ^ 2) := by
          have h_step6 : monQstar d * (lambdaD d + 1) * 2 ^ (d ^ 2) * 3 ^ (d ^ 2) ≤ (3 * d) ^ (d ^ 2) * 5 ^ (d ^ 2) := by
            convert Nat.mul_le_mul h_step4 h_step5 using 1 ; ring;
          convert Nat.le_div_iff_mul_le ( by positivity ) |>.2 h_step6 using 1 ; ring_nf;
          exact Eq.symm ( Nat.div_eq_of_eq_mul_left ( by positivity ) ( by ring ) )
        exact h_step6
      have h_step2 : (monYstar d + monQstar d * (lambdaD d + 1)) * 5 ^ (d ^ 2) ≤ (13 * d) ^ (d ^ 2) := by
        have h_step2 : monYstar d + monQstar d * (lambdaD d + 1) ≤ (2 * (5 * d) ^ (d ^ 2)) / 2 ^ (d ^ 2) := by
          have h_step2 : monYstar d ≤ d ^ (d ^ 2) := by
            apply monYstar_le_ge9; assumption
          have h_step3 : monQstar d * (lambdaD d + 1) * 2 ^ (d ^ 2) ≤ (5 * d) ^ (d ^ 2) := by
            exact h_step1
          have h_step4 : monYstar d * 2 ^ (d ^ 2) ≤ (2 * d) ^ (d ^ 2) := by
            exact le_trans ( Nat.mul_le_mul_right _ h_step2 ) ( by rw [ mul_pow ] ; ring_nf; norm_num )
          have h_step5 : monYstar d * 2 ^ (d ^ 2) + monQstar d * (lambdaD d + 1) * 2 ^ (d ^ 2) ≤ 2 * (5 * d) ^ (d ^ 2) := by
            linarith [ show ( 2 * d ) ^ d ^ 2 ≤ ( 5 * d ) ^ d ^ 2 by gcongr ; linarith ]
          have h_step6 : monYstar d + monQstar d * (lambdaD d + 1) ≤ 2 * (5 * d) ^ (d ^ 2) / 2 ^ (d ^ 2) := by
            rw [ Nat.le_div_iff_mul_le ( by positivity ) ] ; linarith;
          exact h_step6;
        have h_step2 : (2 * (5 * d) ^ (d ^ 2) / 2 ^ (d ^ 2)) * 5 ^ (d ^ 2) ≤ (13 * d) ^ (d ^ 2) := by
          have h_step2 : 2 * (5 * d) ^ (d ^ 2) * 5 ^ (d ^ 2) ≤ (13 * d) ^ (d ^ 2) * 2 ^ (d ^ 2) := by
            have h_step2 : 2 * 25 ^ (d ^ 2) ≤ 26 ^ (d ^ 2) := by
              exact Nat.le_induction ( by norm_num ) ( fun k hk ih ↦ by norm_num [ Nat.pow_succ' ] at * ; nlinarith [ pow_pos ( show 0 < 25 by norm_num ) k ] ) _ ( show d ^ 2 ≥ 81 by nlinarith );
            convert Nat.mul_le_mul_right ( d ^ d ^ 2 ) h_step2 using 1 <;> ring_nf;
            · norm_num [ pow_mul' ];
            · norm_num [ mul_assoc, ← mul_pow ];
          nlinarith [ Nat.div_mul_le_self ( 2 * ( 5 * d ) ^ d ^ 2 ) ( 2 ^ d ^ 2 ), pow_pos ( show 0 < 2 by decide ) ( d ^ 2 ), pow_pos ( show 0 < 5 by decide ) ( d ^ 2 ) ];
        exact le_trans ( Nat.mul_le_mul_right _ ‹_› ) h_step2
      have h_step3 : (5 * d) ^ (d ^ 2) * 2 ^ (d ^ 3 - d ^ 2) ≤ 3 ^ (d ^ 3) := by
        have h_step3 : (5 * d) * 2 ^ (d - 1) ≤ 3 ^ d := by
          exact exp_absorption_ge9 d hd;
        convert Nat.pow_le_pow_left h_step3 ( d ^ 2 ) using 1 <;> ring_nf;
        rw [ show d ^ 3 - d ^ 2 = d ^ 2 * ( d - 1 ) by rw [ Nat.mul_sub_left_distrib ] ; ring_nf ]
      have h_step4 : monQstar d * (lambdaD d + 1) * (monYstar d + monQstar d * (lambdaD d + 1)) ^ d * 10 ^ (d ^ 3) ≤ (39 * d) ^ (d ^ 3) := by
        have h_step4 : monQstar d * (lambdaD d + 1) * 2 ^ (d ^ 2) * (monYstar d + monQstar d * (lambdaD d + 1)) ^ d * 5 ^ (d ^ 3) ≤ (5 * d) ^ (d ^ 2) * (13 * d) ^ (d ^ 3) := by
          convert Nat.mul_le_mul h_step1 ( show ( monYstar d + monQstar d * ( lambdaD d + 1 ) ) ^ d * 5 ^ d ^ 3 ≤ ( 13 * d ) ^ d ^ 3 from ?_ ) using 1 ; ring;
          convert Nat.pow_le_pow_left h_step2 d using 1 <;> ring_nf;
          rw [ show monYstar d * 5 ^ d ^ 2 + monQstar d * lambdaD d * 5 ^ d ^ 2 + monQstar d * 5 ^ d ^ 2 = 5 ^ d ^ 2 * ( monYstar d + monQstar d + monQstar d * lambdaD d ) by ring, mul_pow ] ; ring;
        have h_step4 : (5 * d) ^ (d ^ 2) * (13 * d) ^ (d ^ 3) * 2 ^ (d ^ 3 - d ^ 2) ≤ (39 * d) ^ (d ^ 3) := by
          convert Nat.mul_le_mul_right ( ( 13 * d ) ^ d ^ 3 ) h_step3 using 1 <;> ring_nf;
          norm_num [ mul_assoc, ← mul_pow ];
        convert le_trans _ h_step4 using 1;
        convert Nat.mul_le_mul_right _ ‹monQstar d * ( lambdaD d + 1 ) * 2 ^ d ^ 2 * ( monYstar d + monQstar d * ( lambdaD d + 1 ) ) ^ d * 5 ^ d ^ 3 ≤ ( 5 * d ) ^ d ^ 2 * ( 13 * d ) ^ d ^ 3› using 1 ; ring_nf;
        rw [ show 10 = 2 * 5 by norm_num, mul_pow ] ; rw [ show 2 ^ d ^ 3 = 2 ^ d ^ 2 * 2 ^ ( d ^ 3 - d ^ 2 ) by rw [ ← pow_add, Nat.add_sub_of_le ( by nlinarith ) ] ] ; ring;
      have h_step5 : monMstar d * 10 ^ (d ^ 3) ≤ (39 * d) ^ (d ^ 3) := by
        have h_step5 : monMstar d * 2 ^ (d ^ 2) * 5 ^ (d ^ 3) * 2 ^ (d ^ 3 - d ^ 2) ≤ 3 ^ (d ^ 3) * 5 ^ (d ^ 3) := by
          have h_step5 : monMstar d * 2 ^ (d ^ 2) ≤ (5 * d) ^ (d ^ 2) := by
            convert monMstar_le_ge9 d hd using 1;
          convert Nat.mul_le_mul_right ( 5 ^ d ^ 3 ) ( Nat.mul_le_mul h_step5 ( Nat.le_refl ( 2 ^ ( d ^ 3 - d ^ 2 ) ) ) ) |> le_trans <| Nat.mul_le_mul_right _ h_step3 using 1 ; ring;
        refine le_trans ?_ ( h_step5.trans ?_ );
        · rw [ show ( 10 : ℕ ) = 2 * 5 by norm_num, mul_pow ] ; ring_nf ;
          rw [ show 2 ^ d ^ 3 = 2 ^ d ^ 2 * 2 ^ ( d ^ 3 - d ^ 2 ) by rw [ ← pow_add, Nat.add_sub_of_le ( by nlinarith ) ] ] ; ring_nf ; norm_num;
        · rw [ ← mul_pow ] ; gcongr ; linarith only [ hd ] ;
          linarith
      have h_step6 : monBound d * 10 ^ (d ^ 3) ≤ 2 * (39 * d) ^ (d ^ 3) := by
        unfold monBound; linarith;
      have h_step7 : 2 * (39 * d) ^ (d ^ 3) ≤ (40 * d) ^ (d ^ 3) := by
        have h_step7 : 2 * 39 ^ (d ^ 3) ≤ 40 ^ (d ^ 3) := by
          exact two_mul_pow_le_succ_pow 39 ( d ^ 3 ) ( by norm_num ) ( by nlinarith [ pow_succ' d 2 ] );
        convert Nat.mul_le_mul_right ( d ^ d ^ 3 ) h_step7 using 1 <;> ring
      have h_step8 : monBound d ≤ (4 * d) ^ (d ^ 3) := by
        contrapose! h_step6;
        refine' lt_of_le_of_lt h_step7 _;
        convert mul_lt_mul_of_pos_right h_step6 ( pow_pos ( by decide : 0 < 10 ) ( d ^ 3 ) ) using 1 ; ring_nf;
        norm_num [ mul_assoc, ← mul_pow ]
      exact h_step8

/-! ## Main Theorem

For every d and every N ≥ (200d)^(d³), N can be written as a sum of
distinct d-th powers of natural numbers.
-/
theorem main_theorem (d : ℕ) :
    ∀ N : ℕ, (200 * d) ^ (d ^ 3) ≤ N →
      ∃ J : Finset ℕ, N = ∑ i ∈ J, i ^ d := by
  by_cases hd : 2 ≤ d;
  · -- Apply the monomial_crt_bound theorem to conclude the proof.
    have := monomial_crt_bound d hd;
    simp_all +decide [ monomialPoly ];
    -- Apply the monomial_crt_bound theorem to conclude the proof for N ≥ (200*d)^(d^3).
    intros N hN
    obtain ⟨J, hJ⟩ := this N (by
    refine' le_trans _ hN;
    convert monBound_le_200d_pow d hd using 1);
    exact ⟨ J, by simpa [ ← @Nat.cast_inj ℤ ] using hJ.2 ⟩;
  · interval_cases d <;> simp_all +decide;
    · exact fun N hN => ⟨ Finset.range N, by simp ⟩;
    · exact fun N hN => ⟨ { N }, by simp +decide ⟩

#print axioms main_theorem

/-! As the exact bound for d < 9 is already known from the literature (see
https://oeis.org/A001661/list), here a small improvement on the bound is given
for d ≥ 9;

For every d ≥ 9 and every N ≥ (4d)^(d³), N can be written as a sum of distinct
d-th powers of natural numbers.
-/
theorem main_dge9 (d : ℕ) (hd: 9 ≤ d) :
    ∀ N : ℕ, (4 * d) ^ (d ^ 3) ≤ N →
      ∃ J : Finset ℕ, N = ∑ i ∈ J, i ^ d := by
  have h2 : 2 ≤ d := by omega
  have hbound := monomial_crt_bound d h2
  simp only [monomialPoly] at hbound
  intro N hN
  obtain ⟨J, _, hJ2⟩ := hbound N (le_trans (monBound_le_4d_pow d hd) hN)
  exact ⟨J, by simpa [← @Nat.cast_inj ℤ] using hJ2⟩

#print axioms main_dge9
