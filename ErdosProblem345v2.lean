import Mathlib

/-
In this file we prove that if d ≥ 9, then every N ≥ 32^{d³} can be written as a
sum of distinct d-th powers of natural numbers. The assumption d ≥ 9 is fine, as
the exact bound for d < 9 is already known; https://oeis.org/A001661. With the
bound below we strengthen a result by Kim.

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

/-
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

open Polynomial BigOperators Finset

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

open Polynomial BigOperators Finset

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

open Polynomial BigOperators Finset

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

open Polynomial BigOperators Finset

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

noncomputable section

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

/-
Index bound
-/
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

theorem isThreshold_mono {p : Polynomial ℤ} {C C' : ℕ}
    (h : IsThreshold p C) (hle : C ≤ C') : IsThreshold p C' :=
  fun N hN => h N (le_trans hle hN)

/-
The canonical signed block B_d satisfies L ≤ Λ_d.
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

open Nat Polynomial BigOperators Finset

noncomputable section

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

end

/-
The subset sums of d-th powers from an interval of length 4^d cover all residues modulo d!.
-/
open Finset BigOperators

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

open Nat Polynomial BigOperators Finset

noncomputable section

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

end

open Polynomial Finset BigOperators

noncomputable section

/-
6d ≤ 2^d for d ≥ 6
-/
lemma six_d_pow_le (d : ℕ) (hd : 6 ≤ d) : (6 * d) ^ d ≤ 2 ^ (d ^ 2 + 3 * d) := by
  rw [ show 2 ^ ( d ^ 2 + 3 * d ) = ( 2 ^ ( d + 3 ) ) ^ d by rw [ ← pow_mul ] ; ring ];
  exact Nat.pow_le_pow_left ( by rw [ pow_add ] ; norm_num; nlinarith [ show 2 ^ d ≥ d + 1 by exact Nat.recOn d ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ ihn, Nat.one_le_pow n 2 zero_lt_two ] ] ) d

/-- For d ≥ 4, d(d-1)/2 + 2d + 2 ≤ d² -/
lemma lambdaD_exp_le_sq' (d : ℕ) (hd : 4 ≤ d) :
    d * (d - 1) / 2 + 2 * d + 2 ≤ d ^ 2 := by
  nlinarith [Nat.div_mul_le_self (d * (d - 1)) 2, Nat.sub_add_cancel (by linarith : 1 ≤ d)]

/-
lambdaD d ≤ 2^(d²) for d ≥ 4
-/
lemma lambdaD_le_pow_sq (d : ℕ) (hd : 4 ≤ d) : lambdaD d ≤ 2 ^ (d ^ 2) := by
  exact Nat.pow_le_pow_right ( by decide ) ( lambdaD_exp_le_sq' d hd )

lemma bound_assembly (d : ℕ) (hd : 7 ≤ d)
    (M C₁ : ℤ)
    (hM_le : M ≤ 2 ^ (3 * d ^ 2 + 2 * d))
    (hC₁_le : C₁ ≤ 2 ^ (4 * d ^ 3 + 6 * d ^ 2 + 5 * d + 1)) :
    M + C₁ + 1 ≤ (32 : ℤ) ^ (d ^ 3) := by
  -- Since $3d² + 2d \leq 4d³ + 6d² + 5d + 1$ for $d \geq 1$, we have $M \leq C₁$'s bound.
  have hM_le_C₁ : M ≤ 2 ^ (4 * d ^ 3 + 6 * d ^ 2 + 5 * d + 1) := by
    exact hM_le.trans ( pow_le_pow_right₀ ( by decide ) ( by nlinarith ) );
  -- Since $32^{d^3} = 2^{5d^3}$, we need to show that $4d^3 + 6d^2 + 5d + 2 + 1 \leq 5d^3$.
  have h_exp : 4 * d ^ 3 + 6 * d ^ 2 + 5 * d + 2 + 1 ≤ 5 * d ^ 3 := by
    nlinarith only [ hd ];
  have h_final : M + C₁ + 1 ≤ 2 ^ (4 * d ^ 3 + 6 * d ^ 2 + 5 * d + 2) + 1 := by
    grind;
  refine le_trans h_final ?_;
  rw [ show ( 32 : ℤ ) = 2 ^ 5 by norm_num, ← pow_mul ] ; exact Int.add_one_le_of_lt ( pow_lt_pow_right₀ ( by norm_num ) ( by linarith ) ) ;

/-
Each block term is bounded: if BL ≤ 2^(d²), Qm1 ≤ 2^(3d²+2d+1),
    Y ≤ 2^(d²+d+2), then (Q-1)BL(Y + (Q-1)*(BL+1))^d ≤ 2^(4d³+6d²+5d+1).
-/
lemma C1_bound_from_components (d Qm1 BL Y : ℕ)
    (hBL : BL ≤ 2 ^ (d ^ 2))
    (hQm1 : Qm1 ≤ 2 ^ (3 * d ^ 2 + 2 * d + 1))
    (hY : Y ≤ 2 ^ (d ^ 2 + d + 2)) :
    (Qm1 : ℤ) * ↑BL * (↑Y + ↑Qm1 * (↑BL + 1)) ^ d
    ≤ 2 ^ (4 * d ^ 3 + 6 * d ^ 2 + 5 * d + 1) := by
  -- Step 1: $Y + Qm1 * (BL + 1) \leq 2^{d^2 + d + 2} + 2^{3d^2 + 2d + 1} * (2^{d^2} + 1) \leq 2^{4d^2 + 2d + 3}$.
  have step1 : (Y + Qm1 * (BL + 1) : ℤ) ≤ 2 ^ (4 * d ^ 2 + 2 * d + 3) := by
    refine le_trans ( add_le_add ( Nat.cast_le.mpr hY ) ( mul_le_mul ( Nat.cast_le.mpr hQm1 ) ( add_le_add ( Nat.cast_le.mpr hBL ) le_rfl ) ( by positivity ) ( by positivity ) ) ) ?_;
    norm_num [ pow_add, pow_mul' ];
    nlinarith only [ show 0 < ( 2 ^ d ^ 2 ) ^ 3 * ( 2 ^ d ) ^ 2 by positivity, show 0 < ( 2 ^ d ^ 2 ) ^ 2 * ( 2 ^ d ) ^ 2 by positivity, show 0 < ( 2 ^ d ^ 2 ) * ( 2 ^ d ) ^ 2 by positivity, show 0 < ( 2 ^ d ^ 2 ) ^ 3 * ( 2 ^ d ) by positivity, show 0 < ( 2 ^ d ^ 2 ) ^ 2 * ( 2 ^ d ) by positivity, show 0 < ( 2 ^ d ^ 2 ) * ( 2 ^ d ) by positivity, show 0 < ( 2 ^ d ^ 2 ) ^ 3 by positivity, show 0 < ( 2 ^ d ^ 2 ) ^ 2 by positivity, show 0 < ( 2 ^ d ^ 2 ) by positivity, show 0 < ( 2 ^ d ) by positivity ];
  refine le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) step1 _ ) <| by positivity ) ?_;
  refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul ( Nat.cast_le.mpr hQm1 ) ( Nat.cast_le.mpr hBL ) ( by positivity ) ( by positivity ) ) ( by positivity ) ) _ ; ring_nf;
  norm_num [ mul_assoc, ← pow_add ] ; ring_nf;
  rw [ show ( 8 : ℤ ) = 2 ^ 3 by norm_num, pow_right_comm ] ; ring_nf ; norm_num

/-
M ≤ 2^(3d²+2d) follows from M ≤ 4^d * (8^d)^d
-/
lemma M_bound_exponent (d : ℕ) :
    (4 : ℤ) ^ d * ((8 : ℤ) ^ d) ^ d = 2 ^ (3 * d ^ 2 + 2 * d) := by
  ring_nf;
  norm_num [ pow_mul' ]

/-
T_res = 6d(4^d+1) for the monomialPoly, and R₀ + 4^d + 2 ≤ 2^(3d+3) for d ≥ 6
-/
lemma R0_eMax_bound (d : ℕ) (hd : 6 ≤ d) :
    6 * d * (4 ^ d + 1) + 1 + 4 ^ d + 2 ≤ 2 ^ (3 * d + 3) := by
  rw [ pow_add, pow_mul ] ; ring_nf;
  induction hd <;> norm_num [ Nat.pow_succ' ] at *;
  nlinarith [ pow_pos ( by decide : 0 < 4 ) ‹_›, pow_le_pow_left' ( show 4 ≤ 8 by decide ) ‹_› ]

/-
T_blk + 1 ≤ 2^(d²+d+2) for d ≥ 6 when B.L ≤ 2^(d²)
-/
lemma Tblk_bound (d : ℕ) (hd : 6 ≤ d) (BL : ℕ) (hBL : BL ≤ 2 ^ (d ^ 2)) :
    6 * d * (BL + 1) + 1 ≤ 2 ^ (d ^ 2 + d + 2) := by
  -- We'll use that $6d \leq 2^d$ for $d \geq 6$ to bound the term $6d(BL + 1)$.
  have h_bound : 6 * d * (BL + 1) ≤ 2 ^ d * (2 ^ (d ^ 2) + 1) := by
    exact Nat.mul_le_mul ( show 6 * d ≤ 2 ^ d by exact Nat.le_induction ( by norm_num ) ( fun k hk ih ↦ by norm_num [ Nat.pow_succ', Nat.pow_mul ] at * ; nlinarith ) _ hd ) ( Nat.succ_le_succ hBL );
  ring_nf at *;
  nlinarith [ Nat.pow_le_pow_right ( show 1 ≤ 2 by decide ) hd, Nat.pow_le_pow_right ( show 1 ≤ 2 by decide ) ( show d ^ 2 ≥ d by nlinarith ) ]

/-
Q-1 ≤ 2^(3d²+2d+1) when M ≤ 2^(3d²+2d) and K ≤ (6d)^d, for d ≥ 6
-/
lemma Q_bound (d : ℕ) (hd : 6 ≤ d) (M : ℤ) (K : ℕ)
    (hM_nn : 0 ≤ M) (hM_le : M ≤ 2 ^ (3 * d ^ 2 + 2 * d))
    (hK_le : K ≤ (6 * d) ^ d) :
    (M + ↑K).toNat / d.factorial + 1 ≤ 2 ^ (3 * d ^ 2 + 2 * d + 1) := by
  -- Since $d \geq 6$, we have $2^{3d^2 + 2d} + (6d)^d \leq 2^{3d^2 + 2d + 1}$.
  have h_sum_le : 2 ^ (3 * d ^ 2 + 2 * d) + (6 * d) ^ d ≤ 2 ^ (3 * d ^ 2 + 2 * d + 1) := by
    have h_sum_bound : 2 ^ (3 * d ^ 2 + 2 * d) + (6 * d) ^ d ≤ 2 ^ (3 * d ^ 2 + 2 * d) + 2 ^ (d ^ 2 + 3 * d) := by
      exact Nat.add_le_add_left ( by exact_mod_cast six_d_pow_le d hd ) _;
    refine le_trans h_sum_bound ?_;
    rw [ pow_succ' ] ; ring_nf;
    nlinarith [ show 2 ^ ( d * 2 ) * 2 ^ ( d ^ 2 * 3 ) > 0 by positivity, show 2 ^ ( d * 3 ) * 2 ^ d ^ 2 ≤ 2 ^ ( d * 2 ) * 2 ^ ( d ^ 2 * 3 ) by rw [ ← pow_add, ← pow_add ] ; exact pow_le_pow_right₀ ( by decide ) ( by nlinarith ) ];
  refine' le_trans ( Nat.succ_le_of_lt ( Nat.div_lt_of_lt_mul _ ) ) _;
  exact 2 ^ ( 3 * d ^ 2 + 2 * d + 1 );
  · nlinarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ M + K ), Nat.self_le_factorial d, pow_pos ( by linarith : 0 < 2 ) ( 3 * d ^ 2 + 2 * d + 1 ) ];
  · norm_num

/-- The complete bound tracking: given abstract bounds on M, K, Q-1, B.L, Y, and C₁,
    prove M + C₁ + 1 ≤ 32^(d³). -/
lemma bound_tracking_final_abstract (d : ℕ) (hd : 7 ≤ d) (M C₁ : ℤ)
    (hM_le : M ≤ (4 : ℤ) ^ d * ((8 : ℤ) ^ d) ^ d)
    (Qm1 BL Y : ℕ)
    (hBL : BL ≤ 2 ^ (d ^ 2))
    (hQm1 : Qm1 ≤ 2 ^ (3 * d ^ 2 + 2 * d + 1))
    (hY : Y ≤ 2 ^ (d ^ 2 + d + 2))
    (hC₁_le : C₁ ≤ ↑Qm1 * ↑BL * (↑Y + ↑Qm1 * (↑BL + 1)) ^ d) :
    M + C₁ + 1 ≤ (32 : ℤ) ^ (d ^ 3) := by
  have hM_le' : M ≤ 2 ^ (3 * d ^ 2 + 2 * d) := by rw [← M_bound_exponent]; exact hM_le
  have hC₁_le' : C₁ ≤ 2 ^ (4 * d ^ 3 + 6 * d ^ 2 + 5 * d + 1) :=
    le_trans hC₁_le (C1_bound_from_components d Qm1 BL Y hBL hQm1 hY)
  exact bound_assembly d hd M C₁ hM_le' hC₁_le'

end

open Polynomial Finset BigOperators

noncomputable section

lemma C1_sum_bound (d n L Y : ℕ) (S : Finset ℕ)
    (hS : ∀ v ∈ S, v < L) :
    (∑ i ∈ Finset.range n, ∑ v ∈ S, ((↑Y + ↑i * (↑L + 1) : ℤ) + ↑v) ^ d) ≤
    ↑n * ↑S.card * (↑Y + ↑n * (↑L + 1)) ^ d := by
  refine' le_trans ( Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => pow_le_pow_left₀ ( by positivity ) ( show ( Y : ℤ ) + i * ( L + 1 ) + j ≤ Y + n * ( L + 1 ) by nlinarith [ Finset.mem_range.mp hi, hS j hj ] ) _ ) _;
  norm_num [ mul_assoc ]

/-
|B.N| ≤ B.L for any signed block
-/
lemma signed_block_N_card_le {p : Polynomial ℤ} {a : ℤ} (B : SignedBlock p a) :
    B.N.card ≤ B.L := by
  exact le_trans ( Finset.card_le_card ( show B.N ⊆ Finset.range B.L from fun x hx => Finset.mem_range.mpr ( B.hN_bound x hx ) ) ) ( by simp )

/-
Y bound: max(R₀+eMax+2, T_blk+1) ≤ 2^(d²+d+2) under the given conditions.
-/
lemma Y_bound_combined (d : ℕ) (hd : 6 ≤ d)
    (R₀ eMax T_blk : ℕ)
    (hR₀ : R₀ ≤ 6 * d * (eMax + 1) + 1)
    (hR_eMax : eMax = 4 ^ d)
    (BL : ℕ) (hBL : BL ≤ 2 ^ (d ^ 2))
    (hT_blk : T_blk ≤ 6 * d * (BL + 1)) :
    max (R₀ + eMax + 2) (T_blk + 1) ≤ 2 ^ (d ^ 2 + d + 2) := by
  refine' max_le _ _;
  · -- We can use the fact that $6d \cdot (4^d + 1) + 1 + 4^d + 2 \leq 2^{3d + 3}$ from `R0_eMax_bound`.
    have h_bound : 6 * d * (4 ^ d + 1) + 1 + 4 ^ d + 2 ≤ 2 ^ (3 * d + 3) := by
      exact R0_eMax_bound d hd;
    refine' le_trans _ ( h_bound.trans _ );
    · grind;
    · exact pow_le_pow_right₀ ( by decide ) ( by nlinarith only [ hd ] );
  · exact Tblk_bound d hd BL hBL |> le_trans ( Nat.succ_le_succ hT_blk )

/-
K = (6d)^d for the monomial polynomial
-/
lemma monomial_K_value (d : ℕ) (hd : 2 ≤ d) (K : ℕ)
    (hK_eq : (↑K : ℤ) = (monomialPoly d).eval (↑(explicitTailParam (monomialPoly d) 1) : ℤ)) :
    K = (6 * d) ^ d := by
  exact_mod_cast hK_eq.trans ( monomial_K_eq d hd )

end

open Polynomial Finset BigOperators

noncomputable section

/-
Generalized represents_interval_construction
-/
set_option maxHeartbeats 3200000 in
theorem represents_interval_construction_gen
    (p : Polynomial ℤ)
    (a : ℕ) (ha : 0 < a) (ha_eq : (a : ℤ) = polyA p)
    (E : Finset ℕ) (F : Fin a → Finset ℕ) (hF_sub : ∀ r, F r ⊆ E)
    (B : SignedBlock p (polyA p))
    (R₀ : ℕ)
    (hR₀_cong : ∀ r : Fin a,
      (a : ℤ) ∣ (∑ e ∈ F r, p.eval ((R₀ : ℤ) + ↑e) - ↑(r : ℕ)))
    (Y : ℕ) (hY : R₀ + E.sup id + 2 ≤ Y)
    (K : ℕ) (_hK_pos : 0 < K)
    (hR₀_nonneg : ∀ r : Fin a,
      0 ≤ ∑ e ∈ F r, p.eval ((R₀ : ℤ) + ↑e)) :
    let k : Fin a → ℤ := fun r => ∑ e ∈ F r, p.eval ((R₀ : ℤ) + ↑e)
    let M : ℤ := Finset.univ.sup' ⟨⟨0, ha⟩, Finset.mem_univ _⟩ k
    let Q : ℕ := (M + ↑K).toNat / a + 2
    let I_res : Finset ℕ := E.image (R₀ + ·)
    let I_block : Finset ℕ := (Finset.range (Q - 1)).biUnion
      (fun i => (B.P ∪ B.N).image (Y + i * (B.L + 1) + ·))
    let I : Finset ℕ := I_res ∪ I_block
    let C₁ : ℤ := ∑ i ∈ Finset.range (Q - 1),
      ∑ v ∈ B.N, p.eval ((↑Y + ↑i * (↑B.L + 1) : ℤ) + ↑v)
    let C₀ : ℤ := M - ↑a + 1 + C₁
    RepresentsInterval (fun j => p.eval (j : ℤ)) I C₀ K := by
  intro k M Q I_res I_block I C₁ C₀ N hN₁ hN₂
  obtain ⟨r, hr⟩ : ∃ r : Fin a, ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q - 1 ∧ N = k r + (q - 1) * a + C₁ := by
    obtain ⟨r, hr⟩ : ∃ r : Fin a, k r ≡ N - C₁ [ZMOD a] ∧ k r ≤ M := by
      have h_residue : ∀ r : Fin a, ∃ r' : Fin a, k r' ≡ r [ZMOD a] := by
        exact fun r => ⟨ r, Int.ModEq.symm <| Int.modEq_of_dvd <| hR₀_cong r ⟩
      generalize_proofs at *; (
      obtain ⟨r, hr⟩ : ∃ r : Fin a, k r ≡ N - C₁ [ZMOD a] := by
        obtain ⟨ r, hr ⟩ := h_residue ⟨ Int.toNat ( ( N - C₁ ) % a ), by linarith [ Int.emod_lt_of_pos ( N - C₁ ) ( by positivity : 0 < ( a : ℤ ) ), Int.toNat_of_nonneg ( Int.emod_nonneg ( N - C₁ ) ( by positivity : ( a : ℤ ) ≠ 0 ) ) ] ⟩ ; exact ⟨ r, by simpa [ Int.ModEq, Int.emod_nonneg _ ( by positivity : ( a : ℤ ) ≠ 0 ) ] using hr ⟩ ;
      exact ⟨ r, hr, Finset.le_sup' ( fun r => k r ) ( Finset.mem_univ r ) ⟩)
    generalize_proofs at *; (
    obtain ⟨q, hq⟩ : ∃ q : ℤ, N = k r + (q - 1) * a + C₁ ∧ 1 ≤ q ∧ q ≤ Q - 1 := by
      obtain ⟨q, hq⟩ : ∃ q : ℤ, N = k r + (q - 1) * a + C₁ := by
        obtain ⟨ q, hq ⟩ := hr.1.symm.dvd; exact ⟨ -q + 1, by linarith ⟩ ;
      refine' ⟨ q, hq, _, _ ⟩ <;> norm_num [ Q ] at *;
      · nlinarith [ hR₀_nonneg r, Int.toNat_of_nonneg ( show 0 ≤ M + ↑K by linarith [ hR₀_nonneg r, show 0 ≤ M by exact le_trans ( hR₀_nonneg r ) hr.2 ] ), Nat.div_add_mod ( Int.toNat ( M + K ) ) a, Nat.mod_lt ( Int.toNat ( M + K ) ) ha ];
      · rw [ max_eq_left ];
        · nlinarith [ Int.mul_ediv_add_emod ( M + K ) a, Int.emod_nonneg ( M + K ) ( by positivity : ( a : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( M + K ) ( by positivity : ( a : ℤ ) > 0 ), hR₀_nonneg r ];
        · exact add_nonneg ( le_trans ( hR₀_nonneg r ) hr.2 ) ( Nat.cast_nonneg _ );
    exact ⟨ r, Int.toNat q, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ q ) ], by omega, by simpa [ Int.toNat_of_nonneg ( by linarith : 0 ≤ q ) ] using hq.1 ⟩)
  generalize_proofs at *; (
  obtain ⟨ q, hq₁, hq₂, rfl ⟩ := hr; use Finset.image ( fun x => R₀ + x ) ( F r ) ∪ Finset.biUnion ( Finset.range ( q - 1 ) ) ( fun i => Finset.image ( fun x => Y + i * ( B.L + 1 ) + x ) B.P ) ∪ Finset.biUnion ( Finset.Ico ( q - 1 ) ( Q - 1 ) ) ( fun i => Finset.image ( fun x => Y + i * ( B.L + 1 ) + x ) B.N ) ; simp +decide [ Finset.subset_iff ] ;
  refine' ⟨ _, _ ⟩;
  · rintro x ( ⟨ y, hy, rfl ⟩ | ⟨ i, hi, y, hy, rfl ⟩ | ⟨ i, ⟨ hi₁, hi₂ ⟩, y, hy, rfl ⟩ ) <;> simp +decide [ I, I_res, I_block ];
    · exact Or.inl <| hF_sub r hy;
    · exact Or.inr ⟨ i, by omega, y, Or.inl hy, rfl ⟩;
    · exact Or.inr ⟨ i, hi₂, y, Or.inr hy, rfl ⟩;
  · rw [ Finset.sum_union, Finset.sum_union ] <;> norm_num [ Finset.sum_image ];
    · rw [ Finset.sum_biUnion, Finset.sum_biUnion ] <;> norm_num [ Finset.sum_image ];
      · have h_block_sum : ∀ x : ℤ, ∑ u ∈ B.P, p.eval (x + u) - ∑ v ∈ B.N, p.eval (x + v) = polyA p := by
          exact fun x => B.hBlock x
        generalize_proofs at *; (
        have h_block_sum : ∀ i : ℕ, ∑ u ∈ B.P, p.eval (Y + i * (B.L + 1) + u : ℤ) = ∑ v ∈ B.N, p.eval (Y + i * (B.L + 1) + v : ℤ) + polyA p := by
          exact fun i => by linear_combination h_block_sum ( Y + i * ( B.L + 1 ) ) ;
        generalize_proofs at *; (
        simp_all +decide [ Finset.sum_add_distrib ];
        rw [ Finset.sum_Ico_eq_sub _ ( by omega ) ] ; ring!;));
      · intros i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
        intro x hx y hy; contrapose! hij; nlinarith [ B.hN_bound x hx, B.hN_bound y hy ] ;
      · intros i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
        intro a ha x hx; contrapose! hij; nlinarith [ B.hP_bound a ha, B.hP_bound x hx ] ;
    · simp +decide [ Finset.disjoint_left ];
      rintro a x hx₁ y hy₁ rfl z hz₁ hz₂ w hw₁; nlinarith [ show x < z by omega, show y < B.L from B.hP_bound y hy₁, show w < B.L from B.hN_bound w hw₁ ] ;
    · constructor <;> rw [ Finset.disjoint_left ] <;> simp +decide [ Finset.mem_biUnion ];
      · intro x hx y hy z hz; nlinarith [ show x ≤ E.sup id from Finset.le_sup ( f := id ) ( hF_sub r hx ), show z < B.L from B.hP_bound z hz ] ;
      · intro a ha x hx₁ hx₂ y hy; nlinarith [ show a ≤ E.sup id from Finset.le_sup ( f := id ) ( hF_sub r ha ), show y < B.L from B.hN_bound y hy ] ;)

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

lemma C0_toNat_le_32 (d : ℕ) (M C₁ : ℤ) (a : ℕ)
    (h : M + C₁ + 1 ≤ (32 : ℤ) ^ (d ^ 3)) :
    (M - ↑a + 1 + C₁).toNat ≤ 32 ^ (d ^ 3) := by
  grind

-- Main result: IsThreshold for d ≥ 9

set_option maxHeartbeats 12800000 in
theorem isThreshold_32_pow_ge9 (d : ℕ) (hd : 9 ≤ d) :
    IsThreshold (monomialPoly d) (32 ^ (d ^ 3)) := by
  set p := monomialPoly d with hp_def
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hA : 0 < p.leadingCoeff := monomialPoly_leadingCoeff_pos d hd1
  have hd_nat : 1 ≤ p.natDegree := monomialPoly_natDegree_pos d hd1
  have hnd : p.natDegree = d := monomialPoly_natDegree d hd1
  set a := d.factorial with ha_def
  have ha_pos : 0 < a := Nat.factorial_pos d
  have ha_eq : (a : ℤ) = polyA p := by
    rw [ha_def, hp_def, monomialPoly_polyA d hd1]
  -- Residue datum (for crt_doubling / construction_indices_ge)
  set R := smallEmaxDatum d with hR_def
  have hE_pos : ∀ e ∈ R.E, 1 ≤ e := smallEmaxDatum_ePos d
  -- Signed block
  obtain ⟨B, hB_L'⟩ := canonical_signed_block_bound p hd_nat
  have hB_L : B.L ≤ lambdaD d := hnd ▸ hB_L'
  -- Tau parameters
  set T₀ := explicitTailParam p 1 with hT₀_def
  have hT₀_tau : TauProp p 1 T₀ := explicit_tau_bound p 1 hA hd_nat
  have hR_eMax : R.eMax = 4 ^ d := smallEmaxDatum_eMax d hd1
  set T_res := explicitTailParam p (R.eMax + 1) with hT_res_def
  have hT_res_tau : TauProp p (R.eMax + 1) T_res := explicit_tau_bound p (R.eMax + 1) hA hd_nat
  set T_blk := explicitTailParam p (B.L + 1) with hT_blk_def
  have hT_blk_tau : TauProp p (B.L + 1) T_blk := explicit_tau_bound p (B.L + 1) hA hd_nat
  have hT₀_le_res : T₀ ≤ T_res := explicitTailParam_mono p 1 (R.eMax + 1) (by omega)
  have hT₀_le_blk : T₀ ≤ T_blk := explicitTailParam_mono p 1 (B.L + 1) (by omega)
  -- R₀ (no divisibility constraint!)
  set R₀ := T_res + 1 with hR₀_def
  -- K
  set K := (p.eval (T₀ : ℤ)).toNat with hK_def
  have hT₀_pos : 0 < p.eval (T₀ : ℤ) := tauProp_pos (by omega) hT₀_tau le_rfl
  have hK_pos : 0 < K := by omega
  have hK_eq : (K : ℤ) = p.eval (T₀ : ℤ) := Int.toNat_of_nonneg (le_of_lt hT₀_pos)
  -- Shifted covering functions
  set F : Fin a → Finset ℕ := shiftedF d hd1 R₀ with hF_def
  have hF_sub : ∀ r, F r ⊆ R.E := fun r => shiftedF_sub d hd1 R₀ r
  -- Nonneg residue sums
  have hR₀_nonneg : ∀ r : Fin a, 0 ≤ ∑ e ∈ F r, p.eval ((↑R₀ : ℤ) + ↑e) := by
    intro r
    exact Finset.sum_nonneg fun e he => le_of_lt
      (tauProp_pos (by omega) hT₀_tau (by omega : T₀ ≤ R₀ + e))
  -- Congruence from shiftedF
  have hR₀_cong : ∀ r : Fin a,
      (a : ℤ) ∣ (∑ e ∈ F r, p.eval ((↑R₀ : ℤ) + ↑e) - ↑(r : ℕ)) := by
    intro r
    have h := shiftedF_cong d hd1 R₀ r
    convert h using 2
    apply Finset.sum_congr rfl
    intro e _; simp [hp_def, monomialPoly]
  -- Y
  set Y := max (R₀ + R.eMax + 2) (T_blk + 1) with hY_def
  have hY_res : R₀ + R.E.sup id + 2 ≤ Y := by
    show R₀ + R.E.sup id + 2 ≤ max (R₀ + R.eMax + 2) (T_blk + 1)
    simp only [ResidueDatum.eMax]
    exact le_max_left _ _
  have hY_blk : T_blk + 1 ≤ Y := le_max_right _ _
  -- Build construction quantities
  set k : Fin a → ℤ := fun r => ∑ e ∈ F r, p.eval ((↑R₀ : ℤ) + ↑e) with hk_def
  set M : ℤ := Finset.univ.sup' ⟨⟨0, ha_pos⟩, Finset.mem_univ _⟩ k with hM_def
  set Q := (M + ↑K).toNat / a + 2 with hQ_def
  -- RepresentsInterval via generalized construction
  have hI_rep := represents_interval_construction_gen p a ha_pos ha_eq R.E F hF_sub B R₀
    hR₀_cong Y hY_res K hK_pos hR₀_nonneg
  -- Index bound
  have hI_ge := construction_indices_ge p a ha_pos R B R₀ Y Q T₀ (by omega) hY_res
  -- Positivity
  have h_pos : ∀ n : ℕ, T₀ ≤ n → 0 < p.eval (n : ℤ) :=
    fun n hn => tauProp_pos (by omega) hT₀_tau hn
  -- Doubling
  have hDoubling := crt_doubling p a ha_pos R B hE_pos T₀ hT₀_tau T_res hT_res_tau
    T_blk hT_blk_tau hT₀_le_res hT₀_le_blk R₀ (by omega : T_res + 1 ≤ R₀) Y hY_res hY_blk Q
  -- IsThreshold at C₀.toNat
  set C₁ : ℤ := ∑ i ∈ Finset.range (Q - 1),
    ∑ v ∈ B.N, p.eval ((↑Y + ↑i * (↑B.L + 1) : ℤ) + ↑v) with hC₁_def
  set C₀ : ℤ := M - ↑a + 1 + C₁ with hC₀_def
  have hThreshold : IsThreshold p C₀.toNat :=
    isThreshold_of_data p T₀ K hK_eq _ C₀ hI_ge hI_rep h_pos hDoubling
  apply isThreshold_mono hThreshold
  -- C₀.toNat ≤ (M + C₁ + 1).toNat
  have hM_nn : 0 ≤ M :=
    Finset.le_sup'_of_le k (Finset.mem_univ ⟨0, ha_pos⟩) (hR₀_nonneg ⟨0, ha_pos⟩)
  have hC₁_nn : 0 ≤ C₁ := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun v hv =>
      le_of_lt (h_pos (Y + i * (B.L + 1) + v) (by omega))
  -- M + C₁ + 1 ≤ 32^{d³}
  have hp_eval : ∀ x : ℤ, p.eval x = x ^ d := by intro x; simp [hp_def, monomialPoly]
  have hp_eval : ∀ x : ℤ, p.eval x = x ^ d := by intro x; simp [hp_def, monomialPoly]
  -- M bound
  have hT_res_eq : T_res = 6 * d * (4 ^ d + 1) := by
    have : T_res = explicitTailParam (monomialPoly d) (4 ^ d + 1) := by
      simp only [hT_res_def, hp_def, hR_eMax]
    rw [this]; exact monomial_tau_eq' d _ (by omega) (by omega)
  have hR₀_le : R₀ ≤ 6 * d * (4 ^ d + 1) + 1 := by omega
  have hM_le : M ≤ (4 : ℤ) ^ d * ((8 : ℤ) ^ d) ^ d := by
    rw [hM_def]; apply Finset.sup'_le; intro r _
    rw [hk_def]; simp only [hp_eval]
    exact residue_sum_bound d (by omega) R₀ hR₀_le (F r) (shiftedF_sub d hd1 R₀ r)
  -- BL bound
  have hBL_le : B.L ≤ 2 ^ (d ^ 2) := le_trans hB_L (lambdaD_le_pow_sq d (by omega))
  -- K bound
  have hK_val : K = (6 * d) ^ d := by
    have : (↑K : ℤ) = (monomialPoly d).eval (↑(explicitTailParam (monomialPoly d) 1) : ℤ) := by
      rw [hK_eq, hT₀_def, hp_def]
    exact monomial_K_value d (by omega) K this
  -- Q-1 bound
  have hM_le' : M ≤ 2 ^ (3 * d ^ 2 + 2 * d) := by rw [← M_bound_exponent]; exact hM_le
  have hQm1_le : Q - 1 ≤ 2 ^ (3 * d ^ 2 + 2 * d + 1) := by
    have h1 : Q - 1 = (M + ↑K).toNat / a + 1 := by
      show (M + ↑K).toNat / a + 2 - 1 = (M + ↑K).toNat / a + 1
      exact Nat.succ_sub_one _
    rw [h1, ha_def]
    exact Q_bound d (by omega) M K hM_nn hM_le' (by rw [hK_val])
  -- T_blk bound
  have hT_blk_eq : T_blk = 6 * d * (B.L + 1) := by
    have : T_blk = explicitTailParam (monomialPoly d) (B.L + 1) := by
      simp only [hT_blk_def, hp_def]
    rw [this]; exact monomial_tau_eq' d _ (by omega) (by omega)
  -- Y bound
  have hY_le : Y ≤ 2 ^ (d ^ 2 + d + 2) := by
    rw [hY_def]
    exact Y_bound_combined d (by omega) R₀ R.eMax T_blk
      (by rw [hR_eMax]; exact hR₀_le) (by rw [hR_eMax]) B.L hBL_le (by omega)
  -- C₁ bound
  have hC₁_le : C₁ ≤ ↑(Q - 1) * ↑B.L * (↑Y + ↑(Q - 1) * (↑B.L + 1)) ^ d := by
    rw [hC₁_def]; simp only [hp_eval]
    calc ∑ i ∈ Finset.range (Q - 1), ∑ v ∈ B.N, ((↑Y + ↑i * (↑B.L + 1) : ℤ) + ↑v) ^ d
        ≤ ↑(Q - 1) * ↑B.N.card * (↑Y + ↑(Q - 1) * (↑B.L + 1)) ^ d :=
          C1_sum_bound d (Q - 1) B.L Y B.N B.hN_bound
      _ ≤ ↑(Q - 1) * ↑B.L * (↑Y + ↑(Q - 1) * (↑B.L + 1)) ^ d := by
          gcongr; exact_mod_cast signed_block_N_card_le B
  -- Assembly
  exact C0_toNat_le_32 d M C₁ a
    (bound_tracking_final_abstract d (by omega) M C₁ hM_le
      (Q - 1) B.L Y hBL_le hQm1_le hY_le hC₁_le)

end

open Polynomial Finset BigOperators

/-- **Main Theorem**
For every d ≥ 9 and every N ≥ 32^{d³}, N can be written as a sum of distinct
d-th powers of natural numbers -/
theorem main_theorem_constant_exp (d : ℕ) (hd : 9 ≤ d) :
    ∀ N : ℕ, 32 ^ (d ^ 3) ≤ N →
      ∃ J : Finset ℕ, N = ∑ i ∈ J, i ^ d := by
  have hthresh := isThreshold_32_pow_ge9 d hd
  simp only [monomialPoly] at hthresh
  intro N hN
  obtain ⟨J, _, hJ2⟩ := hthresh N hN
  exact ⟨J, by simpa [← @Nat.cast_inj ℤ] using hJ2⟩

#show_unused main_theorem_constant_exp
#print axioms main_theorem_constant_exp
