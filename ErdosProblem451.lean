import Mathlib

/-
In this Lean file, produced by Aristotle from Harmonic
(aristotle-harmonic@harmonic.fun), we give a proof of the best known lower bound
for Erdős Problem 451 (https://www.erdosproblems.com/451). More precisely, we
show the following result (titled `main_theorem` all the way at the
bottom of the file):

For all sufficiently large integers `k` and all integers `n` with

`2k < n ≤ exp(log²k / (20 log log k))`,

the product `(n-k)(n-k+1)⋯(n-1)` is, with `θ = 21/40`, divisible by some prime
`p ∈ (k, k + 3k^θ)`.

The proof relies on a well-known result by Baker, Harman and Pintz on primes in
short intervals, which is stated as `axiom bhp` down below. Apart from this
single axiom, the formalization is completely self-contained.

In particular, as the proof uses a result by Konyagin on function values close
to rationals, this result is also proved along the way as `konyagin_thm`.

ChatGPT came up with the proof of `main_theorem`, and for more
information one can check out the short paper that Quanyu Tang and I wrote.

W. van Doorn and Q. Tang, Consecutive integers free of certain prime factors. 
arXiv:2606.19863 (2026).

Lean version: leanprover/lean4:v4.28.0
-/

noncomputable section

open scoped BigOperators
open Finset Filter
open scoped BigOperators Nat

/-- The product `(n-k)(n-k+1)⋯(n-1) = ∏_{i=1}^{k} (n - i)`. -/
def Pprod (k : ℕ) (n : ℤ) : ℤ := ∏ i ∈ Finset.Icc 1 k, (n - (i : ℤ))

/-- The exponent `θ = 21/40`. -/
def theta : ℝ := 21 / 40

/-- The number of primes `p` (as positive integers) with `a < p < b`. -/
def primeCard (a b : ℝ) : ℕ :=
  ((Finset.Ioo ⌊a⌋ ⌈b⌉).filter
    (fun p : ℤ => 0 < p ∧ (p.natAbs).Prime ∧ a < (p : ℝ) ∧ (p : ℝ) < b)).card

/-- **Baker–Harman–Pintz.** There is an absolute constant `C > 0`
such that for all sufficiently large `k`, the interval `(k, k + k^θ)` contains
at least `C k^θ / log k` primes.
-/
axiom bhp : ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    C * (k : ℝ) ^ theta / Real.log k ≤ (primeCard (k : ℝ) ((k : ℝ) + (k : ℝ) ^ theta) : ℝ)

lemma theta_pos : (0 : ℝ) < theta := by unfold theta; norm_num
lemma theta_lt_one : theta < 1 := by unfold theta; norm_num

/-- If a prime `p` divides one of the factors `n - i` with `1 ≤ i ≤ k`, then it
divides `P`. -/
lemma dvd_Pprod_of_factor (k : ℕ) (n : ℤ) (p : ℤ) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 k) (hp : p ∣ (n - (i : ℤ))) : p ∣ Pprod k n := by
  unfold Pprod
  exact hp.trans (Finset.dvd_prod_of_mem (fun i : ℕ => (n - (i : ℤ))) hi)

/-
If `p ∣ t` for some integer `t` strictly between `n - k` and `n`, then `p`
divides `P` (as `t` equals one of the factors `n - i`).
-/
lemma dvd_Pprod_of_mem (k : ℕ) (n : ℤ) (p : ℤ) (t : ℤ)
    (h1 : n - (k : ℤ) < t) (h2 : t < n) (hpt : p ∣ t) : p ∣ Pprod k n := by
  convert dvd_Pprod_of_factor k n p ( Int.toNat ( n - t ) ) ?_ ?_ using 1 <;> norm_num [ Int.toNat_of_nonneg ( sub_nonneg.mpr h2.le ) ];
  · omega;
  · assumption

/-
If a prime `p ∈ (k, k + k^θ)` is such that `n/p` is far from any integer
(distance `≥ 1/k^{1-θ}`), then `p` divides `P`.
-/
lemma dvd_from_far (k : ℕ) (n : ℤ) (p : ℕ) (hk1 : 1 ≤ k) (hp0 : 0 < p)
    (hkp : (k : ℝ) < p) (hpk : (p : ℝ) < (k : ℝ) + (k : ℝ) ^ theta)
    (hfar : 1 / (k : ℝ) ^ (1 - theta) ≤ |(n : ℝ) / (p : ℝ) - round ((n : ℝ) / (p : ℝ))|) :
    (p : ℤ) ∣ Pprod k n := by
  -- Set `i := n % (p : ℤ)` and `j := i.toNat`.
  set i := n % (p : ℤ)
  set j := i.toNat
  have hj : (j : ℤ) = i := by
    exact Int.toNat_of_nonneg <| Int.emod_nonneg _ <| by positivity;
  -- From `hfar`, we have `(p:ℝ)/(k:ℝ)^(1-theta) ≤ (min i (p-i) : ℝ)`.
  have h_frac : (p : ℝ) / (k : ℝ) ^ (1 - theta) ≤ min (i : ℝ) ((p : ℝ) - i) := by
    have h_frac : |(n : ℝ) / p - round ((n : ℝ) / p)| = min ((i : ℝ) / p) (1 - (i : ℝ) / p) := by
      have h_frac : Int.fract ((n : ℝ) / p) = (i : ℝ) / p := by
        rw [ Int.fract_eq_iff ];
        field_simp;
        norm_cast;
        exact ⟨ by norm_num; exact Int.emod_nonneg _ ( by positivity ), Int.emod_lt_of_pos _ ( by positivity ), n / p, by linarith [ Int.emod_add_mul_ediv n p ] ⟩;
      rw [ ← h_frac, abs_sub_round_eq_min ];
    convert mul_le_mul_of_nonneg_left hfar ( Nat.cast_nonneg p ) using 1 <;> push_cast [ h_frac ] <;> ring_nf;
    rw [ mul_min_of_nonneg _ _ ( by positivity ), mul_sub, mul_one, mul_left_comm, mul_inv_cancel₀ ( by positivity ), mul_one ];
  -- So `1 ≤ i ≤ k`.
  have h_i_bounds : 1 ≤ i ∧ i ≤ k := by
    have h_i_bounds : (p : ℝ) / (k : ℝ) ^ (1 - theta) > (k : ℝ) ^ theta := by
      rw [ gt_iff_lt, lt_div_iff₀ ] <;> norm_num at *;
      · rw [ ← Real.rpow_add ] <;> norm_num ; linarith [ ( by norm_cast : ( k : ℝ ) + 1 ≤ p ) ];
        grind +extAll;
      · positivity;
    constructor <;> norm_num at *;
    · exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ show ( k : ℝ ) ^ theta ≥ 1 by exact Real.one_le_rpow ( mod_cast hk1 ) ( by exact div_nonneg ( by norm_num ) ( by norm_num ) ) ] );
    · exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith );
  convert dvd_Pprod_of_factor k n ( p : ℤ ) j _ _ using 1;
  · grind;
  · exact ⟨ n / p, by linarith [ Int.emod_add_mul_ediv n p ] ⟩

/-- The set of integers `m ∈ (k, k + k^θ)` such that `n/m` is within `1/k^{1-θ}`
of an integer. Its cardinality is exactly the quantity `K` bounded by
`konyagin_application`. -/
def badSet (k : ℕ) (n : ℤ) : Finset ℤ :=
  (Finset.Ioo (k : ℤ) ((k : ℤ) + ⌊(k : ℝ) ^ theta⌋ + 2)).filter
    (fun m : ℤ => (m : ℝ) < (k : ℝ) + (k : ℝ) ^ theta ∧
      |(n : ℝ) / (m : ℝ) - round ((n : ℝ) / (m : ℝ))| < 1 / (k : ℝ) ^ (1 - theta))

/-- The integer interval `[0, M]_ℤ = {n ∈ ℤ : 0 ≤ n ≤ M}`. -/
def intIcc (M : ℝ) : Finset ℤ := Finset.Icc 0 ⌊M⌋

/-- A point `u` is `(f, W, δ)`-good if there exist `v ∈ ℤ` and `w ∈ ℕ` with
    `w > 0`, `w ≤ W`, and `|f(u) - v/w| < δ`. -/
def IsGood (f : ℝ → ℝ) (W δ : ℝ) (u : ℤ) : Prop :=
  ∃ (v : ℤ) (w : ℕ), 0 < w ∧ (w : ℝ) ≤ W ∧ |f (u : ℝ) - (v : ℝ) / (w : ℝ)| < δ

/-
Hadamard's inequality
-/
set_option maxHeartbeats 800000 in
lemma hadamard_inequality (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    A.det ^ 2 ≤ ∏ i : Fin n, ∑ j : Fin n, A i j ^ 2 := by
  set M := A * A.transpose with hM_def
  have hM_pos_semidef : Matrix.PosSemidef M := by
    constructor;
    · simp +decide [ hM_def, Matrix.IsHermitian, Matrix.transpose_mul ];
    · intro x
      have h_sum : ∑ i, ∑ j, x i * M i j * x j = ∑ k, (∑ i, x i * A i k) ^ 2 := by
        simp +zetaDelta at *;
        simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, sq, Finset.mul_sum _ _ _ ];
        exact sum_comm_cycle;
      simp_all +decide [ Finsupp.sum_fintype ];
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _;
  obtain ⟨U, D, hU, hD⟩ : ∃ U : Matrix (Fin n) (Fin n) ℝ, ∃ D : Fin n → ℝ, U.transpose * U = 1 ∧ (∀ i, D i ≥ 0) ∧ M = U * Matrix.diagonal D * U.transpose := by
    have := Matrix.IsHermitian.spectral_theorem hM_pos_semidef.1;
    refine' ⟨ _, _, _, _, this ⟩;
    · have := hM_pos_semidef.1.eigenvectorUnitary.2.1;
      convert this using 1;
    · exact fun i => hM_pos_semidef.eigenvalues_nonneg i;
  have h_det_M : Matrix.det M = ∏ i, D i := by
    apply_fun Matrix.det at hM_def ; simp_all +decide [ Matrix.det_mul, Matrix.det_diagonal ];
    have := congr_arg Matrix.det hU; norm_num at this; cases le_or_gt 0 ( U.det ) <;> nlinarith;
  have h_diag_M : ∀ i, M i i = ∑ j, U i j ^ 2 * D j := by
    simp +decide [ hD, Matrix.mul_apply, sq ];
    simp +decide [Matrix.diagonal, mul_comm, mul_left_comm];
  have h_am_gm : ∀ i, M i i ≥ ∏ j, D j ^ (U i j ^ 2) := by
    intro i;
    have := @Real.geom_mean_le_arith_mean;
    specialize this Finset.univ ( fun j => U i j ^ 2 ) ( fun j => D j ) ; simp_all +decide [ Matrix.mul_apply ];
    have h_sum_one : ∑ j, U i j ^ 2 = 1 := by
      simpa [ sq ] using congr_arg ( fun m => m i i ) ( show U * U.transpose = 1 from by rw [ ← mul_eq_one_comm, hU ] );
    simpa [ h_sum_one ] using this ( fun j => sq_nonneg _ ) ( by rw [ h_sum_one ] ; norm_num );
  have h_prod_am_gm : ∏ i, M i i ≥ ∏ j, D j := by
    refine le_trans ?_ ( Finset.prod_le_prod ?_ fun i _ => h_am_gm i );
    · rw [ Finset.prod_comm, ← Finset.prod_congr rfl fun _ _ => Real.rpow_sum_of_nonneg ( hD.1 _ ) _ ];
      · simp_all +decide [← Matrix.ext_iff, sq];
        simp_all +decide [ Matrix.mul_apply, Matrix.one_apply ];
      · exact fun _ _ _ _ => sq_nonneg _;
    · exact fun i _ => Finset.prod_nonneg fun j _ => Real.rpow_nonneg ( hD.1 j ) _;
  simp_all +decide [ sq, Matrix.mul_apply ]

/-
Gram determinant
-/
def gramDet (m s : ℕ) (v : Fin m → (Fin s → ℝ)) : ℝ :=
  Matrix.det (Matrix.of (fun i j : Fin m => ∑ k : Fin s, v i k * v j k))

open scoped MatrixOrder

lemma gramDet_le_prod_sq_norms (m s : ℕ) (v : Fin m → (Fin s → ℝ)) :
    gramDet m s v ≤ ∏ j : Fin m, ∑ k : Fin s, v j k ^ 2 := by
  set B : Matrix (Fin m) (Fin s) ℝ := Matrix.of (fun i j => v i j) with hB_def
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin m) (Fin m) ℝ, U * U.transpose = B * B.transpose := by
    have h_pos_semidef : Matrix.PosSemidef (B * B.transpose) := by
      exact Matrix.posSemidef_conjTranspose_mul_self _
    have : 0 ≤ B * B.transpose := h_pos_semidef.nonneg
    obtain ⟨U, hU⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp this
    use U.transpose
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hU.symm
  convert hadamard_inequality m U using 1
  · convert congr_arg Matrix.det hU.symm using 1
    norm_num [sq, Matrix.det_mul]
  · simp_all +decide [← Matrix.ext_iff, Matrix.mul_apply, sq]

/-
gramDet invariance under unimodular change of basis
-/
lemma gramDet_unimodular_change (m s : ℕ)
    (z : Fin m → (Fin s → ℤ))
    (U : Matrix (Fin m) (Fin m) ℤ)
    (hU : Int.natAbs U.det = 1) :
    gramDet m s (fun k i => ((∑ j, U k j * z j i : ℤ) : ℝ)) =
    gramDet m s (fun k i => ((z k i : ℤ) : ℝ)) := by
  convert congr_arg ( fun x : ℤ => ( x : ℝ ) ) ( show Matrix.det ( ( U * Matrix.of ( fun k j => ∑ i, z k i * z j i ) ) * U.transpose ) = Matrix.det ( Matrix.of ( fun k j => ∑ i, z k i * z j i ) ) from ?_ ) using 1;
  · unfold gramDet;
    norm_num [ Matrix.mul_apply, Matrix.det_apply' ];
    simp +decide only [Finset.mul_sum _ _ _, mul_comm, mul_left_comm, mul_assoc];
    exact Finset.sum_congr rfl fun _ _ => congr_arg _ ( Finset.prod_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => by ac_rfl ) ) );
  · unfold gramDet;
    norm_num [ Matrix.det_apply' ];
  · cases Int.natAbs_eq_iff.mp hU <;> simp_all +decide [ Matrix.det_mul ]

/-
Integer vectors with bounded squared norm form a finite set.
-/
lemma finite_integer_vectors_bounded (s : ℕ) (C : ℝ) :
    Set.Finite {a : Fin s → ℤ | ∑ i : Fin s, ((a i : ℤ) : ℝ) ^ 2 ≤ C} := by
  -- Each coordinate a(i) satisfies |a(i)| ≤ √C.
  have h_bound : ∀ (a : Fin s → ℤ), (∑ i, (a i : ℝ) ^ 2) ≤ C → ∀ i, abs (a i : ℝ) ≤ Real.sqrt C := by
    exact fun a ha i => Real.abs_le_sqrt ( le_trans ( Finset.single_le_sum ( fun i _ => sq_nonneg ( a i : ℝ ) ) ( Finset.mem_univ i ) ) ha );
  exact Set.Finite.subset ( Set.finite_Icc _ _ ) fun a ha => ⟨ fun i => ( show a i ≥ - ⌈Real.sqrt C⌉₊ by exact_mod_cast neg_le_of_abs_le <| le_trans ( h_bound a ha i ) <| Nat.le_ceil _ ), fun i => ( show a i ≤ ⌈Real.sqrt C⌉₊ by exact_mod_cast le_of_abs_le <| le_trans ( h_bound a ha i ) <| Nat.le_ceil _ ) ⟩

/-
In a nonzero lattice (span_ℤ of linearly independent vectors), there exists
    a shortest nonzero vector.
-/
lemma shortest_lattice_vector_exists
    (m s : ℕ) (hm : 1 ≤ m)
    (z : Fin m → (Fin s → ℤ))
    (hz_indep : LinearIndependent ℤ z) :
    ∃ v : Fin s → ℤ, v ∈ Submodule.span ℤ (Set.range z) ∧ v ≠ 0 ∧
      ∀ w : Fin s → ℤ, w ∈ Submodule.span ℤ (Set.range z) → w ≠ 0 →
        ∑ i, ((v i : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((w i : ℤ) : ℝ) ^ 2 := by
  have h_finite : Set.Finite {w ∈ Submodule.span ℤ (Set.range z) | ∑ i, (w i : ℝ) ^ 2 ≤ ∑ i, (z ⟨0, by linarith⟩ i : ℝ) ^ 2} := by
    refine' Set.Finite.subset ( finite_integer_vectors_bounded s ( ∑ i, ( z ⟨ 0, by linarith ⟩ i : ℝ ) ^ 2 ) ) _;
    grind;
  obtain ⟨v, hv⟩ : ∃ v ∈ {w ∈ Submodule.span ℤ (Set.range z) | w ≠ 0 ∧ ∑ i, (w i : ℝ) ^ 2 ≤ ∑ i, (z ⟨0, by linarith⟩ i : ℝ) ^ 2}, ∀ w ∈ {w ∈ Submodule.span ℤ (Set.range z) | w ≠ 0 ∧ ∑ i, (w i : ℝ) ^ 2 ≤ ∑ i, (z ⟨0, by linarith⟩ i : ℝ) ^ 2}, ∑ i, (v i : ℝ) ^ 2 ≤ ∑ i, (w i : ℝ) ^ 2 := by
    apply_rules [ Set.exists_min_image ];
    · exact h_finite.subset fun x hx => ⟨ hx.1, hx.2.2 ⟩;
    · exact ⟨ z ⟨ 0, hm ⟩, Submodule.subset_span ( Set.mem_range_self _ ), hz_indep.ne_zero _, le_rfl ⟩;
  exact ⟨ v, hv.1.1, hv.1.2.1, fun w hw hw' => if hw'' : ∑ i, ( w i : ℝ ) ^ 2 ≤ ∑ i, ( z ⟨ 0, by linarith ⟩ i : ℝ ) ^ 2 then hv.2 w ⟨ hw, hw', hw'' ⟩ else by linarith [ hv.1.2.2 ] ⟩

/-
The shortest nonzero vector in a lattice is primitive: it cannot be written
    as n·w for w in the lattice and |n| ≥ 2.
-/
lemma shortest_is_primitive
    (m s : ℕ) (z : Fin m → (Fin s → ℤ))
    (v : Fin s → ℤ)
    (hv_mem : v ∈ Submodule.span ℤ (Set.range z))
    (hv_ne : v ≠ 0)
    (hv_min : ∀ w : Fin s → ℤ, w ∈ Submodule.span ℤ (Set.range z) → w ≠ 0 →
        ∑ i, ((v i : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((w i : ℤ) : ℝ) ^ 2) :
    ∀ n : ℤ, ∀ w : Fin s → ℤ, w ∈ Submodule.span ℤ (Set.range z) →
      v = n • w → n = 1 ∨ n = -1 := by
  intros n w hw hv_eq_nw
  by_contra h_contra
  have h_abs_n : |n| ≥ 2 := by
    exact not_lt.mp fun contra => h_contra <| eq_or_eq_neg_of_abs_eq <| le_antisymm ( Int.le_of_lt_add_one contra ) <| abs_pos.mpr <| show n ≠ 0 from fun h => hv_ne <| by simpa [ h ] using hv_eq_nw;
  specialize hv_min w hw ; simp_all +decide ;
  simp_all +decide [mul_pow, ← Finset.mul_sum _ _ _];
  exact absurd ( hv_min ( by aesop_cat ) ) ( by nlinarith [ show ( n : ℝ ) ^ 2 ≥ 4 by norm_cast; nlinarith [ abs_mul_abs_self n ], show 0 < ∑ i : Fin s, ( w i : ℝ ) ^ 2 from lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( Ne.symm <| by intro h; exact hv_ne <| by ext i; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ) ] )

/-
Generalized Bezout identity: if the entries of c have gcd 1 (any common divisor is ±1),
    then there exist integer coefficients a with ∑ a_i c_i = 1.
-/
lemma bezout_generalized (m : ℕ) (c : Fin m → ℤ)
    (hc : ∀ d : ℤ, (∀ i, d ∣ c i) → (d = 1 ∨ d = -1)) :
    ∃ a : Fin m → ℤ, ∑ i, a i * c i = 1 := by
  -- By the definition of gcd, we know that 1 is in the ideal generated by the c_i's.
  have h_one_in_ideal : 1 ∈ Ideal.span (Set.range c) := by
    contrapose! hc with h;
    obtain ⟨ d, hd ⟩ := IsPrincipalIdealRing.principal ( Ideal.span ( Set.range c ) );
    refine' ⟨ d, _, _, _ ⟩ <;> simp_all +decide;
    · exact fun i => Ideal.mem_span_singleton.mp ( hd ▸ Ideal.subset_span ( Set.mem_range_self i ) );
    · aesop;
    · aesop;
  exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp h_one_in_ideal

/-
A primitive integer vector can be extended to a unimodular matrix as the first row.
-/
lemma int_vector_primitive_extends_unimodular (m : ℕ) (hm : 1 ≤ m) (c : Fin m → ℤ)
    (hc_prim : ∀ d : ℤ, (∀ i, d ∣ c i) → (d = 1 ∨ d = -1)) :
    ∃ U : Matrix (Fin m) (Fin m) ℤ,
      (∀ j, U ⟨0, by omega⟩ j = c j) ∧
      (U.det = 1 ∨ U.det = -1) := by
  -- Apply the lemma `bezkout_generalized` to find the coefficients a such that a • c = 1.
  obtain ⟨a, ha⟩ := bezout_generalized m c hc_prim;
  rcases m with ( _ | m ) <;> simp_all +decide [ Fin.sum_univ_succ ];
  -- Let $B$ be a basis of the kernel of $\phi$.
  obtain ⟨B, hB⟩ : ∃ B : Fin m → Fin (m + 1) → ℤ, LinearIndependent ℤ B ∧ ∀ x : Fin (m + 1) → ℤ, (∑ i, a i * x i = 0) ↔ ∃ y : Fin m → ℤ, x = ∑ i, y i • B i := by
    have h_kernel : ∃ B : Fin m → Fin (m + 1) → ℤ, LinearIndependent ℤ B ∧ ∀ x : Fin (m + 1) → ℤ, (∑ i, a i * x i = 0) ↔ ∃ y : Fin m → ℤ, x = ∑ i, y i • B i := by
      have h_submodule : ∃ M : Submodule ℤ (Fin (m + 1) → ℤ), M = {x : Fin (m + 1) → ℤ | ∑ i, a i * x i = 0} ∧ Module.finrank ℤ M = m := by
        have h_submodule : ∃ M : Submodule ℤ (Fin (m + 1) → ℤ), M = {x : Fin (m + 1) → ℤ | ∑ i, a i * x i = 0} ∧ Module.finrank ℤ M = m := by
          have h_map : ∃ f : (Fin (m + 1) → ℤ) →ₗ[ℤ] ℤ, ∀ x : Fin (m + 1) → ℤ, f x = ∑ i, a i * x i := by
            exact ⟨ ∑ i, a i • LinearMap.proj i, fun x => by simp +decide ⟩
          obtain ⟨f, hf⟩ := h_map
          have h_surjective : Function.Surjective f := by
            intro y
            use fun i => y * c i
            simp [hf];
            simp_all +decide [ mul_comm, mul_left_comm, Fin.sum_univ_succ ];
            rw [ ← Finset.mul_sum _ _ _, ← mul_add, ha, mul_one ];
          have h_rank_nullity : Module.finrank ℤ (LinearMap.ker f) + Module.finrank ℤ (LinearMap.range f) = Module.finrank ℤ (Fin (m + 1) → ℤ) := by
            have := Submodule.finrank_quotient_add_finrank ( LinearMap.ker f );
            rw [ add_comm, ← this ];
            rw [ ← ( LinearMap.quotKerEquivRange f ).finrank_eq ];
          rw [ show f.range = ⊤ from LinearMap.range_eq_top.mpr h_surjective ] at h_rank_nullity ; aesop;
        exact h_submodule
      obtain ⟨ M, hM₁, hM₂ ⟩ := h_submodule
      have h_basis : ∃ B : Fin m → M, LinearIndependent ℤ B ∧ Submodule.span ℤ (Set.range B) = ⊤ := by
        have := ( Module.finBasis ℤ M );
        refine' ⟨ _, _, _ ⟩;
        exact fun i => this ⟨ i, by linarith [ Fin.is_lt i ] ⟩
        all_goals generalize_proofs at *;
        · exact this.linearIndependent.comp _ ( fun i j hij => by simpa [ Fin.ext_iff ] using hij );
        · convert this.span_eq
          generalize_proofs at *; (
          linarith);
          linarith
      generalize_proofs at *; (
      obtain ⟨ B, hB₁, hB₂ ⟩ := h_basis; use fun i => B i; simp_all +decide [ SetLike.ext_iff ] ;
      refine' ⟨ _, _ ⟩
      all_goals generalize_proofs at *;
      · exact hB₁.map' ( Submodule.subtype M ) ( by aesop );
      · intro x; specialize hB₂ x; simp_all +decide [ Submodule.mem_span_range_iff_exists_fun ] ;
        exact ⟨ fun hx => by obtain ⟨ y, hy ⟩ := hB₂ ( hM₁.symm.subset hx ) ; exact ⟨ y, by simpa [ Subtype.ext_iff ] using hy.symm ⟩, fun hx => by obtain ⟨ y, hy ⟩ := hx; exact hM₁.subset <| by simpa [ Subtype.ext_iff ] using hy.symm ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( B i |>.2 ) ⟩ ;);
    exact h_kernel;
  -- Let $U$ be the matrix with rows $c$ and $B$.
  use Matrix.of (Fin.cons c B);
  -- Since $B$ is a basis of the kernel of $\phi$, the matrix $U$ is unimodular.
  have h_unimodular : ∀ x : Fin (m + 1) → ℤ, (∃ y : Fin (m + 1) → ℤ, x = ∑ i, y i • (Fin.cons c B i)) := by
    intro x
    obtain ⟨y, hy⟩ : ∃ y : Fin m → ℤ, x - (∑ i, a i * x i) • c = ∑ i, y i • B i := by
      have h_kernel : ∑ i, a i * (x i - (∑ i, a i * x i) * c i) = 0 := by
        simp +decide [ mul_sub, Finset.sum_sub_distrib ];
        simp +decide [ mul_comm, mul_left_comm, Fin.sum_univ_succ ] at ha ⊢;
        simp +decide [← mul_assoc, ← Finset.sum_mul _ _ _];
        grind +splitImp;
      exact hB.2 _ |>.1 h_kernel;
    use Fin.cons (∑ i, a i * x i) y;
    simp +decide [ Fin.sum_univ_succ, Fin.cons ] at hy ⊢;
    exact eq_add_of_sub_eq' hy;
  have h_unimodular : ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ, U * Matrix.of (Fin.cons c B) = 1 := by
    choose f hf using h_unimodular;
    use Matrix.of (fun i j => f (Pi.single i 1) j);
    ext i j; specialize hf ( Pi.single i 1 ) ; replace hf := congr_fun hf j; simp +decide [Matrix.mul_apply,
      Finset.sum_apply] at hf ⊢;
    simp +decide [ ← hf, Pi.single_apply ];
    simp +decide [ Matrix.one_apply, eq_comm ];
  obtain ⟨ U, hU ⟩ := h_unimodular; have := congr_arg Matrix.det hU; norm_num at this; exact ⟨ fun j => rfl, Int.isUnit_iff.mp <| isUnit_iff_dvd_one.mpr <| by use U.det; linarith ⟩ ;

/-
A primitive element of a free ℤ-module extends to a basis.
-/
lemma primitive_extends_to_basis
    (m s : ℕ) (hm : 2 ≤ m) (hms : m ≤ s)
    (z : Fin m → (Fin s → ℤ))
    (hz_indep : LinearIndependent ℤ z)
    (v : Fin s → ℤ)
    (hv_mem : v ∈ Submodule.span ℤ (Set.range z))
    (hv_prim : ∀ n : ℤ, ∀ w : Fin s → ℤ, w ∈ Submodule.span ℤ (Set.range z) →
      v = n • w → n = 1 ∨ n = -1) :
    ∃ w : Fin (m - 1) → (Fin s → ℤ),
      LinearIndependent ℤ (Fin.cons v w) ∧
      Submodule.span ℤ (Set.range (Fin.cons v w)) = Submodule.span ℤ (Set.range z) := by
  have h_basis : ∃ (u : Fin m → (Fin s → ℤ)), LinearIndependent ℤ u ∧ Submodule.span ℤ (Set.range u) = Submodule.span ℤ (Set.range z) ∧ u ⟨0, by linarith⟩ = v := by
    obtain ⟨c, hc⟩ : ∃ c : Fin m → ℤ, v = ∑ k, c k • z k := by
      rw [ Submodule.mem_span_range_iff_exists_fun ] at hv_mem ; tauto;
    -- Let $U$ be a unimodular matrix with first row $c$.
    obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin m) (Fin m) ℤ, (∀ j, U ⟨0, by linarith⟩ j = c j) ∧ (U.det = 1 ∨ U.det = -1) := by
      apply int_vector_primitive_extends_unimodular m (by linarith) c;
      intro d hd; specialize hv_prim d ( ∑ k, ( c k / d ) • z k ) ; simp_all +decide [Finset.smul_sum] ;
      refine' hv_prim _ _;
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_range_self _ ) );
      · exact Finset.sum_congr rfl fun i _ => by rw [ ← mul_assoc, ← Int.cast_mul, Int.mul_ediv_cancel' ( hd i ) ] ;
    refine' ⟨ fun i => ∑ j, U i j • z j, _, _, _ ⟩;
    · rw [ Fintype.linearIndependent_iff ] at *;
      intro g hg;
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ j, (∑ i, g i * U i j) • z j = 0 := by
        convert hg using 1;
        simp +decide only [mul_comm, sum_smul, smul_sum, smul_smul];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      -- Since $U$ is unimodular, the only solution to $\sum_{i} g_i U_{ij} = 0$ for all $j$ is $g_i = 0$ for all $i$.
      have h_unimodular : ∀ (g : Fin m → ℤ), (∀ j, ∑ i, g i * U i j = 0) → ∀ i, g i = 0 := by
        intro g hg i
        have h_unimodular : Matrix.mulVec (Matrix.transpose U) g = 0 := by
          exact funext fun j => by simpa [ Matrix.mulVec, dotProduct, mul_comm ] using hg j;
        have h_unimodular : Matrix.det (Matrix.transpose U) ≠ 0 := by
          cases hU.2 <;> simp +decide [ * ];
        exact Matrix.eq_zero_of_mulVec_eq_zero h_unimodular ‹_› ▸ rfl;
      exact h_unimodular g fun j => hz_indep _ h_fubini j;
    · refine' le_antisymm _ _ <;> rw [ Submodule.span_le ] <;> simp +decide [ Set.range_subset_iff ];
      · exact fun i => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_range_self _ ) );
      · intro i
        have h_inv : ∃ V : Matrix (Fin m) (Fin m) ℤ, V * U = 1 := by
          exact ⟨ U⁻¹, Matrix.nonsing_inv_mul _ <| isUnit_iff_dvd_one.mpr <| by rcases hU.2 with h | h <;> norm_num [ h ] ⟩;
        obtain ⟨ V, hV ⟩ := h_inv;
        have h_inv : z i = ∑ j, V i j • (∑ k, U j k • z k) := by
          have h_inv : ∀ i, ∑ j, V i j • (∑ k, U j k • z k) = ∑ k, (∑ j, V i j * U j k) • z k := by
            simp +decide [ Finset.smul_sum, Finset.sum_smul ];
            exact fun i => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
          simp_all +decide [ ← Matrix.mul_apply, ← Matrix.ext_iff ];
          simp +decide [ Matrix.one_apply ];
        exact h_inv.symm ▸ Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ j, rfl ⟩ );
    · grind;
  obtain ⟨u, hu_indep, hu_span, hu_v⟩ := h_basis;
  use fun i => u ⟨i.val + 1, by
    exact Nat.succ_lt_of_lt_pred i.2⟩;
  generalize_proofs at *;
  rcases m with ( _ | _ | m ) <;> simp_all +decide;
  refine' ⟨ _, _ ⟩;
  · convert hu_indep using 1;
    ext i; induction i using Fin.inductionOn <;> aesop;
  · convert hu_span using 2;
    ext x; simp;
    exact ⟨ fun hx => hx.elim ( fun hx => ⟨ 0, hx.symm ▸ hu_v ⟩ ) fun ⟨ y, hy ⟩ => ⟨ _, hy ⟩, fun hx => by rcases hx with ⟨ y, rfl ⟩ ; exact Fin.cases ( Or.inl <| by aesop ) ( fun y => Or.inr ⟨ y, rfl ⟩ ) y ⟩

/-
The projected integer vectors w'_j = ‖v‖²·w_j - ⟨w_j,v⟩·v are ℤ-linearly independent
    when (v, w₁,...,w_{m-1}) are ℤ-linearly independent and v ≠ 0.
-/
lemma projected_int_vectors_indep
    (n s : ℕ)
    (v : Fin s → ℤ) (hv_ne : v ≠ 0)
    (w : Fin n → (Fin s → ℤ))
    (hw_indep : LinearIndependent ℤ (Fin.cons v w)) :
    LinearIndependent ℤ (fun j : Fin n => fun i : Fin s =>
      (∑ k, v k * v k) * w j i - (∑ k, w j k * v k) * v i) := by
  rw [ Fintype.linearIndependent_iff ] at hw_indep ⊢;
  intro g hg;
  convert hw_indep ( Fin.cons ( -∑ i, g i * ∑ k, w i k * v k ) ( fun i => g i * ∑ k, v k * v k ) ) _ using 1;
  · simp +decide [ Fin.forall_fin_succ ];
    exact ⟨ fun h => ⟨ by simp +decide [ h ], fun i => Or.inl ( h i ) ⟩, fun h => h.2 |> fun h' => fun i => Or.resolve_right ( h' i ) ( by intro h''; exact hv_ne <| funext fun x => by simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_self_nonneg ] ) ⟩;
  · convert hg using 1;
    ext i; simp +decide [ Fin.sum_univ_succ, mul_sub, mul_comm, mul_left_comm ] ; ring_nf;
    simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _] ; ring

/-
gramDet(w') = ‖v‖^{4n-2} · gramDet(v, w₁,...,w_n) where w'_j = ‖v‖²·w_j - ⟨w_j,v⟩·v.
-/
set_option maxHeartbeats 800000 in
lemma gramDet_projected_identity
    (n s : ℕ) (hn : 1 ≤ n)
    (v : Fin s → ℤ) (hv_ne : v ≠ 0)
    (w : Fin n → (Fin s → ℤ))
    (hw_indep : LinearIndependent ℤ (Fin.cons v w)) :
    let nsq : ℝ := ∑ i, ((v i : ℤ) : ℝ) ^ 2
    let w'_real : Fin n → (Fin s → ℝ) := fun j i =>
      nsq * ((w j i : ℤ) : ℝ) - (∑ k, ((w j k : ℤ) : ℝ) * ((v k : ℤ) : ℝ)) * ((v i : ℤ) : ℝ)
    gramDet n s w'_real =
      nsq ^ (2 * n - 1) *
      gramDet (n + 1) s (Fin.cons (fun i => ((v i : ℤ) : ℝ)) (fun j i => ((w j i : ℤ) : ℝ))) := by
  obtain ⟨nsq, hnsq⟩ : ∃ nsq : ℤ, nsq > 0 ∧ nsq = ∑ i, (v i : ℤ) ^ 2 := by
    exact ⟨ ∑ i, v i ^ 2, lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( Ne.symm <| by contrapose! hv_ne; ext i; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ), rfl ⟩;
  -- Let $N = \sum_{i=0}^{s-1} v_i^2$, $a_j = \sum_{k=0}^{s-1} w_j k \cdot v k$ (the inner products).
  set N := nsq
  set a : Fin n → ℤ := fun j => ∑ k, w j k * v k;
  -- So det(Gram(w')) = det(N²·G_w - N·a·aᵀ) where G_w is the Gram matrix of w and a = (a_1,...,a_n).
  have h_det : gramDet n s (fun j i => (N : ℝ) * (w j i : ℝ) - (a j : ℝ) * (v i : ℝ)) = N ^ n * Matrix.det (Matrix.of (fun i j : Fin n => N * (∑ k, (w i k : ℝ) * (w j k : ℝ)) - (a i : ℝ) * (a j : ℝ))) := by
    have h_det : ∀ i j : Fin n, ∑ k : Fin s, ((N : ℝ) * (w i k : ℝ) - (a i : ℝ) * (v k : ℝ)) * ((N : ℝ) * (w j k : ℝ) - (a j : ℝ) * (v k : ℝ)) = N ^ 2 * (∑ k : Fin s, (w i k : ℝ) * (w j k : ℝ)) - N * (a i : ℝ) * (a j : ℝ) := by
      intro i j; simp +decide [ sub_mul, mul_sub, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, sq ] ; ring_nf;
      simp +zetaDelta at *;
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, sq ] ; ring_nf;
      norm_cast ; simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hnsq.2 ] ; ring;
    unfold gramDet; simp +decide [ h_det ] ;
    rw [ show ( Matrix.of fun i j : Fin n => ( N : ℝ ) ^ 2 * ∑ k : Fin s, ( w i k : ℝ ) * ( w j k : ℝ ) - ( N : ℝ ) * ( a i : ℝ ) * ( a j : ℝ ) ) = ( N : ℝ ) • ( Matrix.of fun i j : Fin n => ( N : ℝ ) * ∑ k : Fin s, ( w i k : ℝ ) * ( w j k : ℝ ) - ( a i : ℝ ) * ( a j : ℝ ) ) by ext i j; simp +decide [ mul_sub, mul_assoc, pow_two ] ] ; rw [ Matrix.det_smul ] ; norm_num;
  -- By the Schur complement formula, we have det(N·G_w - aaᵀ) = N^{n-1} · det(Gram_full).
  have h_schur : Matrix.det (Matrix.of (fun i j : Fin n => N * (∑ k, (w i k : ℝ) * (w j k : ℝ)) - (a i : ℝ) * (a j : ℝ))) = N ^ (n - 1) * Matrix.det (Matrix.of (fun i j : Fin (n + 1) => ∑ k, (Fin.cases (fun i => (v i : ℝ)) (fun j i => (w j i : ℝ)) i k) * (Fin.cases (fun i => (v i : ℝ)) (fun j i => (w j i : ℝ)) j k))) := by
    -- By the properties of determinants, we can factor out $N$ from the determinant.
    have h_factor : Matrix.det (Matrix.of (fun i j : Fin (n + 1) => ∑ k, (Fin.cases (fun i => (v i : ℝ)) (fun j i => (w j i : ℝ)) i k) * (Fin.cases (fun i => (v i : ℝ)) (fun j i => (w j i : ℝ)) j k))) = N * Matrix.det (Matrix.of (fun i j : Fin n => (∑ k, (w i k : ℝ) * (w j k : ℝ)) - (a i : ℝ) * (a j : ℝ) / N)) := by
      have h_schur : ∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), A 0 0 ≠ 0 → Matrix.det A = A 0 0 * Matrix.det (Matrix.of (fun i j : Fin n => A (Fin.succ i) (Fin.succ j) - A (Fin.succ i) 0 * A 0 (Fin.succ j) / A 0 0)) := by
        intro A hA_nonzero
        have h_schur : Matrix.det A = Matrix.det (Matrix.of (fun i j : Fin (n + 1) => if i = 0 then A i j else if j = 0 then 0 else A i j - A i 0 * A 0 j / A 0 0)) := by
          have h_schur : ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, P.det = 1 ∧ P * A = Matrix.of (fun i j : Fin (n + 1) => if i = 0 then A i j else if j = 0 then 0 else A i j - A i 0 * A 0 j / A 0 0) := by
            refine' ⟨ Matrix.of ( fun i j => if i = 0 then if j = 0 then 1 else 0 else if j = 0 then -A i 0 / A 0 0 else if i = j then 1 else 0 ), _, _ ⟩ <;> norm_num [ Matrix.det_succ_row_zero ];
            · erw [ Matrix.det_of_upperTriangular ] <;> norm_num;
              intro i j hij; aesop;
            · ext i j; simp +decide [ Matrix.mul_apply, Fin.sum_univ_succ ] ; ring_nf;
              rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> norm_num [ Fin.ext_iff, Fin.sum_univ_succ ] at *; all_goals rw [ Finset.sum_eq_single ⟨ i, by linarith ⟩ ] <;> aesop;
          obtain ⟨ P, hP₁, hP₂ ⟩ := h_schur; rw [ ← hP₂, Matrix.det_mul, hP₁, one_mul ] ;
        rw [ h_schur, Matrix.det_succ_column_zero ];
        simp +decide [Matrix.submatrix]
      convert h_schur _ _ using 3 <;> norm_num [ Fin.sum_univ_succ, hnsq ];
      · exact Finset.sum_congr rfl fun _ _ => by ring;
      · simp +zetaDelta at *;
        simp +decide only [mul_comm];
        norm_num [ ← sq ];
      · norm_cast ; simp_all +decide [ ← sq ];
        linarith;
    have h_factor : Matrix.det (Matrix.of (fun i j : Fin n => N * (∑ k, (w i k : ℝ) * (w j k : ℝ)) - (a i : ℝ) * (a j : ℝ))) = N ^ n * Matrix.det (Matrix.of (fun i j : Fin n => (∑ k, (w i k : ℝ) * (w j k : ℝ)) - (a i : ℝ) * (a j : ℝ) / N)) := by
      have h_factor : Matrix.det (Matrix.of (fun i j : Fin n => N * (∑ k, (w i k : ℝ) * (w j k : ℝ)) - (a i : ℝ) * (a j : ℝ))) = Matrix.det (Matrix.diagonal (fun _ => (N : ℝ)) * Matrix.of (fun i j : Fin n => (∑ k, (w i k : ℝ) * (w j k : ℝ)) - (a i : ℝ) * (a j : ℝ) / N)) := by
        congr with i j ; simp +decide [ mul_sub, mul_div_cancel₀, hnsq.1.ne' ];
      rw [ h_factor, Matrix.det_mul, Matrix.det_diagonal ] ; norm_num;
    cases n <;> simp_all +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm ];
  convert h_det.trans ( congr_arg _ h_schur ) using 1;
  · norm_cast ; aesop;
  · rw [ ← mul_assoc, ← pow_add, show 2 * n - 1 = n + ( n - 1 ) by omega ] ; norm_num [ hnsq.2 ];
    exact Or.inl rfl

/-
For any integer vector l and nonzero integer vector v,
    there exists n ∈ ℤ such that |⟨l + n·v, v⟩| ≤ ‖v‖²/2.
-/
lemma integer_centering_exists
    (s : ℕ) (v l : Fin s → ℤ) (hv_ne : v ≠ 0) :
    ∃ n : ℤ, |(∑ i, (l i + n * v i) * v i : ℤ)| * 2 ≤ ∑ i, v i * v i := by
  norm_num [ add_mul, Finset.sum_add_distrib, mul_assoc ];
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  -- Let $a = \langle l, v \rangle$ and $d = \|v\|^2$.
  set a := ∑ i, l i * v i
  set d := ∑ i, v i * v i
  have hd_pos : 0 < d := by
    exact lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) ( Ne.symm <| by intro H; exact hv_ne <| funext fun i => by simpa [ sq ] using Finset.sum_eq_zero_iff_of_nonneg ( fun _ _ => mul_self_nonneg _ ) |>.1 H i );
  -- By the division algorithm, there exists an integer $q$ such that $a = qd + r$ with $0 \leq r < d$.
  obtain ⟨q, r, hr⟩ : ∃ q r : ℤ, a = q * d + r ∧ 0 ≤ r ∧ r < d := by
    exact ⟨ a / d, a % d, by rw [ Int.ediv_mul_add_emod ], Int.emod_nonneg _ hd_pos.ne', Int.emod_lt_of_pos _ hd_pos ⟩;
  by_cases hr_case : 2 * r ≤ d;
  · exact ⟨ -q, by rw [ abs_of_nonneg ] <;> nlinarith ⟩;
  · exact ⟨ -q - 1, by rw [ abs_of_nonpos ] <;> linarith ⟩

/-
The norm of the projected vector: ‖π_v(l)‖² = ‖ytil‖²/‖v‖⁴
    where ytil = ‖v‖²·l - ⟨l,v⟩·v.
-/
lemma projection_norm_via_scaled
    (s : ℕ) (v l : Fin s → ℤ) (hv_ne : v ≠ 0) :
    let nsq : ℝ := ∑ i, ((v i : ℤ) : ℝ) ^ 2
    let ytilde : Fin s → ℝ := fun i =>
      nsq * ((l i : ℤ) : ℝ) - (∑ k, ((l k : ℤ) : ℝ) * ((v k : ℤ) : ℝ)) * ((v i : ℤ) : ℝ)
    -- ‖z‖² - ⟨z,v⟩²/‖v‖² = ‖ytil‖²/‖v‖⁴
    (∑ i, ((l i : ℤ) : ℝ) ^ 2) -
      (∑ i, ((l i : ℤ) : ℝ) * ((v i : ℤ) : ℝ)) ^ 2 / nsq =
    (∑ i, ytilde i ^ 2) / nsq ^ 2 := by
  by_cases h : ∑ i, ( v i : ℝ ) ^ 2 = 0 <;> simp_all +decide [ Finset.sum_div _ _ _ ];
  · exact False.elim <| hv_ne <| funext fun i => by norm_cast at h; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ;
  · rw [ ← Finset.sum_div, sub_div' ];
    · simp +decide [ ← Finset.sum_mul _, mul_pow, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib, sub_sq ];
      norm_num [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] ; rw [ div_eq_div_iff ] <;> first | positivity | ring;
    · exact_mod_cast h

/-
If ∃ vectors with the product bound (without monotonicity),
    then ∃ vectors with monotone norms and the same bound.
-/
lemma add_monotone
    (m s : ℕ) (z : Fin m → (Fin s → ℤ))
    (y : Fin m → (Fin s → ℤ))
    (hy_mem : ∀ k, y k ∈ Submodule.span ℤ (Set.range z))
    (hy_indep : LinearIndependent ℝ (fun k : Fin m => (fun i : Fin s => ((y k i : ℤ) : ℝ))))
    (hy_bound : ∏ k : Fin m, (∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (m * (m - 1)) *
        gramDet m s (fun k i => ((z k i : ℤ) : ℝ))) :
    ∃ y' : Fin m → (Fin s → ℤ),
      (∀ k, y' k ∈ Submodule.span ℤ (Set.range z)) ∧
      LinearIndependent ℝ (fun k : Fin m => (fun i : Fin s => ((y' k i : ℤ) : ℝ))) ∧
      Monotone (fun k : Fin m => ∑ i : Fin s, ((y' k i : ℤ) : ℝ) ^ 2) ∧
      ∏ k : Fin m, (∑ i : Fin s, ((y' k i : ℤ) : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (m * (m - 1)) *
        gramDet m s (fun k i => ((z k i : ℤ) : ℝ)) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin m), Monotone (fun k => ∑ i, ((y (σ k) i : ℤ) : ℝ) ^ 2) := by
    have h_exists_perm : ∃ σ : Fin m → Fin m, Function.Injective σ ∧ ∀ i j, i < j → ∑ k, ((y (σ i) k : ℤ) : ℝ) ^ 2 ≤ ∑ k, ((y (σ j) k : ℤ) : ℝ) ^ 2 := by
      have h_exists_perm : ∀ (n : ℕ) (f : Fin n → ℝ), ∃ σ : Fin n → Fin n, Function.Injective σ ∧ ∀ i j, i < j → f (σ i) ≤ f (σ j) := by
        intro n f;
        induction' n with n ih;
        · simp +decide [ Function.Injective ];
        · -- Let $m$ be the index of the minimum element in $f$.
          obtain ⟨m, hm⟩ : ∃ m : Fin (n + 1), ∀ i : Fin (n + 1), f m ≤ f i := by
            simpa using Finset.exists_min_image Finset.univ ( fun i => f i ) ⟨ 0, Finset.mem_univ 0 ⟩;
          obtain ⟨ σ, hσ₁, hσ₂ ⟩ := ih ( fun i => f ( Fin.succAbove m i ) );
          use Fin.cons m ( fun i => Fin.succAbove m ( σ i ) );
          simp +decide [ Fin.forall_fin_succ, Function.Injective, * ];
          exact ⟨ hσ₁, hσ₂ ⟩;
      exact h_exists_perm m fun k => ∑ i, ( y k i : ℝ ) ^ 2;
    obtain ⟨ σ, hσ₁, hσ₂ ⟩ := h_exists_perm; exact ⟨ Equiv.ofBijective σ ⟨ hσ₁, Finite.injective_iff_surjective.mp hσ₁ ⟩, fun i j hij => by cases hij.lt_or_eq <;> aesop ⟩ ;
  refine' ⟨ fun k ↦ y ( σ k ), _, _, hσ, _ ⟩;
  · exact fun k => hy_mem _;
  · exact hy_indep.comp σ σ.injective;
  · convert hy_bound using 1;
    conv_rhs => rw [ ← Equiv.prod_comp σ ] ;

/-
The projection onto v⊥ is invariant under adding a multiple of v:
    ‖z + t·v‖² - ⟨z+t·v,v⟩²/‖v‖² = ‖z‖² - ⟨z,v⟩²/‖v‖²
-/
lemma projection_add_multiple_invariant
    (s : ℕ) (v z : Fin s → ℤ) (t : ℤ) :
    let nsq : ℝ := ∑ i, ((v i : ℤ) : ℝ) ^ 2
    (∑ i, ((z i + t * v i : ℤ) : ℝ) ^ 2) -
      (∑ i, ((z i + t * v i : ℤ) : ℝ) * ((v i : ℤ) : ℝ)) ^ 2 / nsq =
    (∑ i, ((z i : ℤ) : ℝ) ^ 2) -
      (∑ i, ((z i : ℤ) : ℝ) * ((v i : ℤ) : ℝ)) ^ 2 / nsq := by
  norm_num [ Finset.sum_add_distrib, add_sq, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
  norm_num [ mul_pow, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_add, add_mul, add_assoc ] ; ring_nf;
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  by_cases h : ∑ i : Fin s, ( v i : ℝ ) ^ 2 = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ];
  · simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_self_nonneg ];
  · simpa [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] using by ring;

/-
Given two ℤ-bases of the same free ℤ-module (as subsets of ℤ^s),
    their Gram determinants are equal.
-/
set_option maxHeartbeats 800000 in
lemma gramDet_eq_of_same_span
    (m s : ℕ)
    (b1 b2 : Fin m → (Fin s → ℤ))
    (h1 : LinearIndependent ℤ b1)
    (h_span : Submodule.span ℤ (Set.range b1) = Submodule.span ℤ (Set.range b2)) :
    gramDet m s (fun k i => ((b1 k i : ℤ) : ℝ)) = gramDet m s (fun k i => ((b2 k i : ℤ) : ℝ)) := by
  -- Since b1 and b2 are both ℤ-linearly independent and span the same ℤ-submodule, there exists a unimodular change of basis matrix U with b1 k = ∑ j, U k j • b2 j and det(U) = ±1.
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin m) (Fin m) ℤ, (∀ k, b1 k = ∑ j, U k j • b2 j) ∧ Int.natAbs U.det = 1 := by
    obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin m) (Fin m) ℤ, (∀ k, b1 k = ∑ j, U k j • b2 j) := by
      have h_basis : ∀ k, b1 k ∈ Submodule.span ℤ (Set.range b2) := by
        exact fun k => h_span ▸ Submodule.subset_span ( Set.mem_range_self k );
      choose! U hU using fun k => Submodule.mem_span_range_iff_exists_fun ℤ |>.1 ( h_basis k );
      exact ⟨ U, fun k => hU k ▸ rfl ⟩;
    obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin m) (Fin m) ℤ, (∀ k, b2 k = ∑ j, V k j • b1 j) := by
      have hV : ∀ k, b2 k ∈ Submodule.span ℤ (Set.range b1) := by
        exact fun k => h_span.symm ▸ Submodule.subset_span ( Set.mem_range_self k );
      choose V hV using fun k => ( Finsupp.mem_span_range_iff_exists_finsupp.mp ( hV k ) );
      exact ⟨ fun k j => V k j, fun k => by simpa [ Finsupp.sum_fintype ] using hV k |> Eq.symm ⟩;
    have hUV : U * V = 1 := by
      have hUV : ∀ k, b1 k = ∑ j, (U * V) k j • b1 j := by
        intro k
        rw [hU k]
        simp [Matrix.mul_apply, hV];
        simp +decide only [Finset.mul_sum _ _ _, sum_mul, mul_assoc];
        rw [ Finset.sum_comm ];
      have hUV : ∀ k j, (U * V) k j = if k = j then 1 else 0 := by
        intro k j;
        have := Fintype.linearIndependent_iff.mp h1 ( fun i => ( U * V ) k i - if k = i then 1 else 0 ) ?_;
        · exact eq_of_sub_eq_zero ( this j );
        · simp +decide [ sub_smul, Finset.sum_sub_distrib, hUV k ];
      exact Matrix.ext fun i j => by simpa using hUV i j;
    have := congr_arg Matrix.det hUV; norm_num at this;
    exact ⟨ U, hU, by rw [ Int.mul_eq_one_iff_eq_one_or_neg_one ] at this; omega ⟩;
  convert gramDet_unimodular_change m s b2 U hU.2 using 3 ; aesop

set_option maxHeartbeats 1600000 in
lemma successive_minima_inductive_step
    (m s : ℕ) (hm : 2 ≤ m) (hms : m ≤ s)
    (z : Fin m → (Fin s → ℤ))
    (hz_indep : LinearIndependent ℤ z)
    (ih : ∀ (m' : ℕ), m' < m → 1 ≤ m' → m' ≤ s →
      ∀ (z' : Fin m' → (Fin s → ℤ)), LinearIndependent ℤ z' →
        ∃ y : Fin m' → (Fin s → ℤ),
          (∀ k, y k ∈ Submodule.span ℤ (Set.range z')) ∧
          LinearIndependent ℝ (fun k : Fin m' => (fun i : Fin s => ((y k i : ℤ) : ℝ))) ∧
          Monotone (fun k : Fin m' => ∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ∧
          ∏ k : Fin m', (∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ≤
            (2 : ℝ) ^ (m' * (m' - 1)) *
            gramDet m' s (fun k i => ((z' k i : ℤ) : ℝ))) :
    ∃ y : Fin m → (Fin s → ℤ),
      (∀ k, y k ∈ Submodule.span ℤ (Set.range z)) ∧
      LinearIndependent ℝ (fun k : Fin m => (fun i : Fin s => ((y k i : ℤ) : ℝ))) ∧
      Monotone (fun k : Fin m => ∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ∧
      ∏ k : Fin m, (∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (m * (m - 1)) *
        gramDet m s (fun k i => ((z k i : ℤ) : ℝ)) := by
  -- Step 1: Find shortest nonzero vector
  obtain ⟨v, hv_mem, hv_ne, hv_min⟩ := shortest_lattice_vector_exists m s (by omega) z hz_indep
  -- Step 2: v is primitive
  have hv_prim := shortest_is_primitive m s z v hv_mem hv_ne hv_min
  -- Step 3: Extend to basis
  obtain ⟨w, hw_indep, hw_span⟩ := primitive_extends_to_basis m s hm hms z hz_indep v hv_mem hv_prim
  -- Step 4: Define projected integer vectors
  set w' : Fin (m - 1) → (Fin s → ℤ) := fun j i =>
    (∑ k, v k * v k) * w j i - (∑ k, w j k * v k) * v i with w'_def
  -- Step 5: w' are ℤ-linearly independent
  have hw'_indep : LinearIndependent ℤ w' := projected_int_vectors_indep (m - 1) s v hv_ne w hw_indep
  -- Step 6: Apply IH
  obtain ⟨ytil, hytil_mem, hytil_indep, _, hytil_bound⟩ :=
    ih (m - 1) (by omega) (by omega) (by omega) w' hw'_indep
  -- Step 7: Extract coefficients for each ytil_j
  have hytil_coeffs : ∀ j, ∃ a : Fin (m - 1) → ℤ, ytil j = ∑ k, a k • w' k := by
    intro j
    have := hytil_mem j
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨c, hc⟩ := this; exact ⟨c, hc.symm⟩
  choose a ha using hytil_coeffs
  -- Step 8: Define lifts
  set l : Fin (m - 1) → (Fin s → ℤ) := fun j i => ∑ k, a j k * w k i with l_def
  -- Step 9: Center using integer rounding
  have h_center : ∀ j, ∃ n : ℤ, |(∑ i, (l j i + n * v i) * v i : ℤ)| * 2 ≤ ∑ i, v i * v i := by
    intro j; exact integer_centering_exists s v (l j) hv_ne
  choose ctr hctr using h_center
  -- Step 10: Define centered vectors
  set zc : Fin (m - 1) → (Fin s → ℤ) := fun j i => l j i + ctr j * v i with zc_def
  -- Step 11: Define output (v, zc_0, ..., zc_{m-2})
  set out : Fin m → (Fin s → ℤ) := fun k =>
    if h : k.val = 0 then v
    else zc ⟨k.val - 1, by omega⟩ with out_def
  -- Key relationships
  have hytil_perp_v : ∀ j, ∑ i, (ytil j i : ℝ) * (v i : ℝ) = 0 := by
    intro j; rw [ ha j ] ; simp +decide [ Finset.sum_mul _ _ _, mul_comm ] ;
    rw [ Finset.sum_comm ] ; simp +decide [ w'_def, mul_sub, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    exact sub_eq_zero_of_eq ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) )
  have hzc_ne : ∀ j, zc j ≠ 0 := by
    intro j hj_zero
    have hytil_zero : ytil j = 0 := by
      convert congr_arg ( fun x : Fin s → ℤ => fun i => ( ∑ k, ( v k * v k ) ) * x i - ( ∑ k, ( x k * v k ) ) * ( v i ) ) hj_zero using 1;
      · convert ha j using 1;
        ext i; simp +decide [ zc_def, l_def, w'_def ] ; ring_nf;
        simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_comm, mul_left_comm, sq ] ; ring_nf;
        simp +decide [ mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring_nf;
        exact congrArg₂ _ rfl ( Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
      · norm_num [ funext_iff ];
    exact hytil_indep.ne_zero j <| by ext i; simp +decide [ hytil_zero ] ;
  have hzc_not_mul_v : ∀ j, ¬ ∃ n : ℤ, ∀ i, zc j i = n * v i := by
    intro j hj
    obtain ⟨n, hn⟩ := hj
    have h_l_eq : l j = (n - ctr j) • v := by
      ext i; specialize hn i; norm_num at *; linarith;
    have h_ytil_zero : ytil j = 0 := by
      have h_ytil_zero : ytil j = (∑ k, v k * v k) • l j - (∑ k, l j k * v k) • v := by
        convert ha j using 1;
        ext i; simp +decide [ l_def, w'_def ] ; ring_nf;
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      simp +decide [ h_ytil_zero, h_l_eq ];
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    exact hytil_indep.ne_zero j ( by ext i; simp +decide [ h_ytil_zero ] )
  -- Sub-goal 1: membership in span_ℤ(z)
  have h_mem : ∀ k, out k ∈ Submodule.span ℤ (Set.range z) := by
    intro k; by_cases hk : k.val = 0 <;> simp +decide [ hk, out_def, hv_mem ] ;
    refine' hw_span ▸ Submodule.add_mem _ _ _;
    · rw [ Submodule.mem_span ];
      intro p hp;
      convert p.sum_mem fun i _ => p.smul_mem ( a ⟨ k - 1, by omega ⟩ i ) ( hp <| Set.mem_range_self <| Fin.succ i ) using 1;
      any_goals exact Finset.univ;
      exact funext fun i => by simp +decide [ l_def, Fin.cons ] ;
    · exact Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_range_self 0 ) )
  -- Sub-goal 2: ℝ-linear independence
  have h_indep : LinearIndependent ℝ (fun k : Fin m => (fun i : Fin s => ((out k i : ℤ) : ℝ))) := by
    have h_linearInd : ∀ (c : Fin m → ℝ), (∑ k : Fin m, c k • (fun i : Fin s => ((out k i : ℤ) : ℝ))) = 0 → c = 0 := by
      intro c hc
      have h_sum : ∑ j : Fin (m - 1), c ⟨j + 1, by omega⟩ • (fun i : Fin s => ((ytil j i : ℤ) : ℝ)) = 0 := by
        have h_sum : ∑ j : Fin (m - 1), c ⟨j + 1, by omega⟩ • (fun i : Fin s => ((ytil j i : ℤ) : ℝ)) = (fun i : Fin s => ((∑ k, v k * v k) : ℝ) * (∑ j : Fin (m - 1), c ⟨j + 1, by omega⟩ * (zc j i : ℝ)) - (∑ j : Fin (m - 1), c ⟨j + 1, by omega⟩ * (∑ i : Fin s, (zc j i : ℝ) * (v i : ℝ))) * (v i : ℝ)) := by
          ext i; simp +decide [ *, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
          simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, pow_two ] ; ring_nf;
          exact congrArg₂ _ ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) ) ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
        have h_sum_zero : ∑ j : Fin (m - 1), c ⟨j + 1, by omega⟩ • (fun i : Fin s => ((zc j i : ℤ) : ℝ)) = -c ⟨0, by omega⟩ • (fun i : Fin s => ((v i : ℤ) : ℝ)) := by
          rcases m with ( _ | _ | m ) <;> norm_num [ Fin.sum_univ_succ ] at *;
          · contradiction;
          · contradiction;
          · convert eq_neg_of_add_eq_zero_right hc using 1;
            erw [ Fin.sum_univ_succ ] ; norm_num [ Fin.sum_univ_succ ] ; ring!;
        have h_sum_zero : ∑ j : Fin (m - 1), c ⟨j + 1, by omega⟩ * (∑ i : Fin s, (zc j i : ℝ) * (v i : ℝ)) = -c ⟨0, by omega⟩ * (∑ i : Fin s, (v i : ℝ) * (v i : ℝ)) := by
          convert congr_arg ( fun f : Fin s → ℝ => ∑ i, f i * ( v i : ℝ ) ) h_sum_zero using 1 <;> norm_num [ Finset.sum_mul _ _ _ ];
          · rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring;
          · simp +decide only [Finset.mul_sum _ _ _, mul_assoc];
        convert h_sum using 1;
        ext i; simp +decide [ h_sum_zero ] ; ring_nf;
        rename_i h; replace h := congr_fun h i; simp +decide [ mul_comm] at h;
        simp +decide [ add_comm, h ] ; ring;
      have h_c_zero : ∀ j : Fin (m - 1), c ⟨j + 1, by omega⟩ = 0 := by
        exact fun j => Fintype.linearIndependent_iff.mp hytil_indep _ h_sum j;
      ext ⟨ i, hi ⟩ ; induction i <;> simp +decide [ * ] at *;
      · rw [ Finset.sum_eq_single ⟨ 0, hi ⟩ ] at hc <;> simp +decide at hc ⊢;
        · exact hc.resolve_right fun h => hv_ne <| funext fun i => by simpa using congr_fun h i;
        · intro b hb; rcases b with ⟨ _ | b, hb ⟩ <;> simp +decide [ Fin.ext_iff ] at hb ⊢;
          exact Or.inl <| h_c_zero ⟨ b, Nat.lt_pred_iff.mpr ‹_› ⟩;
      · exact h_c_zero ⟨ _, Nat.lt_pred_iff.mpr hi ⟩;
    rw [ Fintype.linearIndependent_iff ] ; tauto
  -- Sub-goal 3: product bound
  have product_bound_qed : ∏ k : Fin m, (∑ i : Fin s, ((out k i : ℤ) : ℝ) ^ 2) ≤
      (2 : ℝ) ^ (m * (m - 1)) * gramDet m s (fun k i => ((z k i : ℤ) : ℝ)) := by
    -- Apply the centering_sq_norm_bound lemma to each zc j.
    have hzc_bound : ∀ j, (∑ i, (zc j i : ℝ) ^ 2) ≤ 4 * (∑ i, (ytil j i : ℝ) ^ 2) / (∑ i, (v i : ℝ) ^ 2) ^ 2 := by
      intro j
      have h_centering : (∑ i, ((zc j i : ℤ) : ℝ) ^ 2) - (∑ i, ((zc j i : ℤ) : ℝ) * ((v i : ℤ) : ℝ)) ^ 2 / (∑ i, ((v i : ℤ) : ℝ) ^ 2) = (∑ i, ((ytil j i : ℤ) : ℝ) ^ 2) / (∑ i, ((v i : ℤ) : ℝ) ^ 2) ^ 2 := by
        convert projection_norm_via_scaled s v ( l j ) hv_ne using 1;
        · convert projection_add_multiple_invariant s v ( l j ) ( ctr j ) using 1;
        · simp +decide [ ha, l_def, w'_def ];
          simp +decide [ mul_sub, mul_assoc, mul_comm, Finset.mul_sum _ _ _ ];
          simp +decide only [sq, mul_comm, mul_left_comm];
          simp +decide only [← mul_assoc];
          congr! 3; all_goals exact congrArg₂ _ rfl ( Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
      have h_centering_bound : (∑ i, ((zc j i : ℤ) : ℝ) ^ 2) - (∑ i, ((zc j i : ℤ) : ℝ) * ((v i : ℤ) : ℝ)) ^ 2 / (∑ i, ((v i : ℤ) : ℝ) ^ 2) ≥ (∑ i, ((zc j i : ℤ) : ℝ) ^ 2) / 4 := by
        have h_centering_bound : (∑ i, ((zc j i : ℤ) : ℝ) * ((v i : ℤ) : ℝ)) ^ 2 ≤ (∑ i, ((v i : ℤ) : ℝ) ^ 2) ^ 2 / 4 := by
          have h_centering_bound : |∑ i, ((zc j i : ℤ) : ℝ) * ((v i : ℤ) : ℝ)| ≤ (∑ i, ((v i : ℤ) : ℝ) ^ 2) / 2 := by
            norm_cast;
            rw [ Rat.divInt_eq_div, le_div_iff₀ ] <;> norm_cast;
            simpa only [ sq ] using hctr j;
          nlinarith only [ abs_le.mp h_centering_bound ];
        have h_centering_bound : (∑ i, ((zc j i : ℤ) : ℝ) ^ 2) ≥ (∑ i, ((v i : ℤ) : ℝ) ^ 2) := by
          apply hv_min;
          · convert h_mem ⟨ j + 1, by omega ⟩ using 1;
          · exact hzc_ne j;
        rw [ sub_div', ge_iff_le, div_le_div_iff₀ ] <;> nlinarith [ show 0 < ∑ i : Fin s, ( v i : ℝ ) ^ 2 from lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( Ne.symm <| by intro h; exact hv_ne <| by ext i; simpa [ sq ] using Finset.sum_eq_zero_iff_of_nonneg ( fun _ _ => sq_nonneg _ ) |>.1 h i ) ];
      ring_nf at *; linarith;
    -- Combine the bounds to conclude the proof.
    have h_combined : (∏ k : Fin m, (∑ i : Fin s, ((out k i : ℤ) : ℝ) ^ 2)) ≤
      (∑ i : Fin s, ((v i : ℤ) : ℝ) ^ 2) * (4 / (∑ i : Fin s, ((v i : ℤ) : ℝ) ^ 2) ^ 2) ^ (m - 1) *
      (∏ k : Fin (m - 1), (∑ i : Fin s, ((ytil k i : ℤ) : ℝ) ^ 2)) := by
        -- Split the product into the term for v and the product of the terms for zc j.
        have h_split : (∏ k : Fin m, (∑ i : Fin s, ((out k i : ℤ) : ℝ) ^ 2)) = (∑ i : Fin s, ((v i : ℤ) : ℝ) ^ 2) * (∏ j : Fin (m - 1), (∑ i : Fin s, ((zc j i : ℤ) : ℝ) ^ 2)) := by
          rcases m with ⟨ ⟩ <;> norm_num [ Fin.prod_univ_succ ] at *;
          · contradiction;
          · simp +decide [ out_def ];
        rw [ h_split, mul_assoc ];
        gcongr;
        convert Finset.prod_le_prod ?_ fun j _ => hzc_bound j using 1;
        · norm_num [ div_eq_mul_inv, mul_pow, mul_assoc, mul_comm, mul_left_comm, Finset.prod_mul_distrib ];
        · exact fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _;
    -- Apply the gramDet_projected_identity lemma to bound the gram determinant of w'.
    have hw'_gramDet : gramDet (m - 1) s (fun k i => ((w' k i : ℤ) : ℝ)) =
      (∑ i : Fin s, ((v i : ℤ) : ℝ) ^ 2) ^ (2 * (m - 1) - 1) *
      gramDet m s (fun k i => ((z k i : ℤ) : ℝ)) := by
        convert gramDet_projected_identity ( m - 1 ) s ( by omega ) v hv_ne w hw_indep using 1;
        · norm_num [ w'_def, sq ];
        · rcases m with ( _ | _ | m ) <;> norm_num at *;
          · contradiction;
          · contradiction;
          · left;
            convert gramDet_eq_of_same_span ( m + 1 + 1 ) s z ( Fin.cons v w ) hz_indep _ using 1;
            · congr! 2;
              rename_i k; induction k using Fin.inductionOn <;> simp +decide [ * ] ;
            · convert hw_span.symm using 1;
              congr with x ; simp +decide [ Fin.exists_fin_succ ];
    refine le_trans h_combined ?_;
    convert mul_le_mul_of_nonneg_left hytil_bound _ using 1;
    · rcases m with ( _ | _ | m ) <;> simp +decide [ Nat.mul_succ, pow_succ' ] at *;
      · contradiction;
      · contradiction;
      · rw [ hw'_gramDet ] ; ring_nf;
        field_simp;
        by_cases h : ∑ x : Fin s, ( v x : ℝ ) ^ 2 = 0 <;> simp +decide [h, mul_comm,
          mul_left_comm, pow_mul', div_eq_mul_inv];
        · exact False.elim <| hv_ne <| funext fun i => by norm_cast at h; simpa [ sq ] using Finset.sum_eq_zero_iff_of_nonneg ( fun _ _ => sq_nonneg _ ) |>.1 h i;
        · norm_num [ ← mul_assoc, ← mul_pow ];
    · exact mul_nonneg ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( pow_nonneg ( div_nonneg zero_le_four ( sq_nonneg _ ) ) _ )
  exact add_monotone m s z out h_mem h_indep product_bound_qed

lemma successive_minima_product_bound_abstract
    (m s : ℕ) (hm : 1 ≤ m) (hms : m ≤ s)
    (z : Fin m → (Fin s → ℤ))
    (hz_indep : LinearIndependent ℤ z) :
    ∃ y : Fin m → (Fin s → ℤ),
      (∀ k, y k ∈ Submodule.span ℤ (Set.range z)) ∧
      LinearIndependent ℝ (fun k : Fin m => (fun i : Fin s => ((y k i : ℤ) : ℝ))) ∧
      Monotone (fun k : Fin m => ∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ∧
      ∏ k : Fin m, (∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (m * (m - 1)) *
        gramDet m s (fun k i => ((z k i : ℤ) : ℝ)) := by
  induction' m using Nat.strongRecOn with m ih generalizing s;
  by_cases hm2 : m ≥ 2;
  · exact successive_minima_inductive_step m s hm2 hms z hz_indep ( fun m' hm' hm1 hm2 z' hz' => ih m' hm' s hm1 hm2 z' hz' );
  · interval_cases m;
    refine' ⟨ fun _ => z 0, _, _, _, _ ⟩ <;> norm_num [ Monotone ];
    · exact Submodule.subset_span ( Set.mem_range_self _ );
    · intro h; have := hz_indep.ne_zero 0; simp_all +decide [ funext_iff ] ;
    · unfold gramDet; norm_num [ Fin.eq_zero ] ;
      norm_num [ sq ]

/-
If b and z are mutually orthogonal (∑ b_j(i) z_k(i) = 0), then the Gram determinant of [b; z] factors.
-/
set_option maxHeartbeats 800000 in
lemma gramDet_orthogonal_factorization
    (r s : ℕ) (hs : s = 2 * r)
    (b z : Fin r → (Fin s → ℝ))
    (h_orth : ∀ j k : Fin r, ∑ i : Fin s, b j i * z k i = 0) :
    let C : Fin (2 * r) → (Fin s → ℝ) := fun idx =>
      if h : idx.val < r then b ⟨idx.val, h⟩ else z ⟨idx.val - r, by omega⟩
    Matrix.det (Matrix.of (fun i j : Fin (2 * r) => ∑ k : Fin s, C i k * C j k)) =
    Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, b i k * b j k)) *
    Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, z i k * z j k)) := by
  generalize_proofs at *;
  convert Matrix.det_fromBlocks_zero₂₁ _ _ _ using 1;
  swap;
  exact 0;
  rw [ ← Matrix.det_submatrix_equiv_self ( Equiv.ofBijective ( fun i : Fin ( 2 * r ) => if h : i.val < r then Sum.inl ⟨ i.val, h ⟩ else Sum.inr ⟨ i.val - r, by solve_by_elim ⟩ ) ⟨ fun i => ?_, fun i => ?_ ⟩ ) ];
  congr! 1;
  ext i j; simp +decide ;
  · split_ifs <;> simp +decide [ * ];
    simpa only [ mul_comm ] using h_orth _ _;
  · grind;
  · rcases i with ( i | i ) <;> [ exact ⟨ ⟨ i, by linarith [ Fin.is_lt i ] ⟩, by aesop ⟩ ; exact ⟨ ⟨ i + r, by linarith [ Fin.is_lt i ] ⟩, by aesop ⟩ ]

/-
If b ⊥ z (integer vectors, s = 2r), then
  gramDet(b) · gramDet(z) = d² for some nonzero integer d.
-/
set_option maxHeartbeats 1600000 in
lemma gramDet_product_is_square
    (r s : ℕ) (hs : s = 2 * r)
    (b z : Fin r → (Fin s → ℤ))
    (h_orth : ∀ j k : Fin r, ∑ i : Fin s, (b j i : ℝ) * (z k i : ℝ) = 0)
    (h_indep_b : LinearIndependent ℝ (fun j : Fin r => (fun i : Fin s => ((b j i : ℤ) : ℝ))))
    (h_indep_z : LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((z k i : ℤ) : ℝ)))) :
    ∃ d : ℤ, d ≠ 0 ∧
    Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, (b i k : ℝ) * (b j k : ℝ))) *
    Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, (z i k : ℝ) * (z j k : ℝ))) =
    (d : ℝ) ^ 2 := by
  -- Define the matrix C with rows b_0, ..., b_{r-1}, z_0, ..., z_{r-1}.
  set C : Matrix (Fin (2 * r)) (Fin s) ℤ := Matrix.of (fun i j =>
    if h : i.val < r then b ⟨i.val, h⟩ j else z ⟨i.val - r, by omega⟩ j);
  -- By definition of C, we have det(C·C^T) = det(C)^2.
  have h_det_C_sq : Matrix.det (Matrix.of (fun i j : Fin (2 * r) => ∑ k : Fin s, C i k * C j k)) = (Matrix.det (Matrix.of (fun i j : Fin (2 * r) => C i (Fin.cast hs.symm j)))) ^ 2 := by
    have h_det_C_sq : Matrix.of (fun i j : Fin (2 * r) => ∑ k : Fin s, C i k * C j k) = (Matrix.of (fun i j : Fin (2 * r) => C i (Fin.cast hs.symm j))) * (Matrix.of (fun i j : Fin (2 * r) => C i (Fin.cast hs.symm j))).transpose := by
      ext i j; simp +decide [ Matrix.mul_apply ] ;
      refine' Finset.sum_bij ( fun k _ => ⟨ k, by linarith [ Fin.is_lt k ] ⟩ ) _ _ _ _ <;> simp +decide [ Fin.ext_iff ];
      exact fun i => ⟨ ⟨ i, by linarith [ Fin.is_lt i ] ⟩, rfl ⟩;
    rw [ h_det_C_sq, Matrix.det_mul, Matrix.det_transpose, sq ];
  -- By definition of C, we have det(C·C^T) = det(b) · det(z).
  have h_det_C_prod : Matrix.det (Matrix.of (fun i j : Fin (2 * r) => ∑ k : Fin s, C i k * C j k)) = Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, b i k * b j k)) * Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, z i k * z j k)) := by
    convert gramDet_orthogonal_factorization r s hs ( fun i j => ( b i j : ℝ ) ) ( fun i j => ( z i j : ℝ ) ) _ using 1;
    · norm_num [ ← @Int.cast_inj ℝ ];
      norm_num [ Matrix.det_apply' ];
      norm_num +zetaDelta at *;
      congr!; all_goals split_ifs <;> rfl;
    · convert h_orth using 1;
  -- Since $b$ and $z$ are linearly independent, their determinants are non-zero.
  have h_det_b_nonzero : Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, b i k * b j k)) ≠ 0 := by
    have h_det_b_nonzero : Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, (b i k : ℝ) * (b j k : ℝ))) ≠ 0 := by
      have h_det_b_nonzero : ∀ (v : Fin r → ℝ), v ≠ 0 → ∑ i, ∑ j, v i * v j * (∑ k, (b i k : ℝ) * (b j k : ℝ)) > 0 := by
        intro v hv_nonzero
        have h_sum_pos : ∑ i, ∑ j, v i * v j * (∑ k, (b i k : ℝ) * (b j k : ℝ)) = ∑ k, (∑ i, v i * (b i k : ℝ)) ^ 2 := by
          simp +decide only [Finset.mul_sum _ _ _, pow_two, mul_comm, mul_left_comm];
          exact Eq.symm ( by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
        contrapose! hv_nonzero;
        have h_sum_zero : ∀ k, ∑ i, v i * (b i k : ℝ) = 0 := by
          exact fun k => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( ∑ i : Fin r, v i * ( b i a : ℝ ) ) ) ( Finset.mem_univ k ) ) ( h_sum_pos ▸ hv_nonzero ) ) ( sq_nonneg _ ) );
        rw [ Fintype.linearIndependent_iff ] at h_indep_b;
        exact funext fun i => h_indep_b v ( by ext k; simpa [ mul_comm ] using h_sum_zero k ) i;
      contrapose! h_det_b_nonzero;
      obtain ⟨ v, hv ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h_det_b_nonzero;
      use v;
      simp_all +decide [ funext_iff, Matrix.mulVec, dotProduct ];
      simp_all +decide [ ← Finset.mul_sum _ _ _, mul_assoc, mul_comm];
    norm_num [ Matrix.det_apply' ] at *;
    exact_mod_cast h_det_b_nonzero
  have h_det_z_nonzero : Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, z i k * z j k)) ≠ 0 := by
    have h_det_z_nonzero : Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, (z i k : ℝ) * (z j k : ℝ))) ≠ 0 := by
      have h_det_z_nonzero : ∀ (v : Fin r → ℝ), v ≠ 0 → ∑ i, ∑ j, v i * v j * ∑ k, (z i k : ℝ) * (z j k : ℝ) > 0 := by
        intros v hv_nonzero
        have h_sum_pos : ∑ i, ∑ j, v i * v j * ∑ k, (z i k : ℝ) * (z j k : ℝ) = ∑ k, (∑ i, v i * (z i k : ℝ)) ^ 2 := by
          simp +decide only [Finset.mul_sum _ _ _, pow_two, mul_comm, mul_left_comm];
          exact Eq.symm ( by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
        contrapose! hv_nonzero;
        have h_sum_zero : ∀ k, ∑ i, v i * (z i k : ℝ) = 0 := by
          exact fun k => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( ∑ i, v i * ( z i a : ℝ ) ) ) ( Finset.mem_univ k ) ) ( h_sum_pos ▸ hv_nonzero ) ) ( sq_nonneg _ ) );
        rw [ Fintype.linearIndependent_iff ] at h_indep_z;
        exact funext fun i => h_indep_z v ( by ext k; simpa [ mul_comm ] using h_sum_zero k ) i;
      contrapose! h_det_z_nonzero;
      obtain ⟨ v, hv ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h_det_z_nonzero;
      use v;
      simp_all +decide [ funext_iff, Matrix.mulVec, dotProduct ];
      simp_all +decide [← Finset.mul_sum _ _ _, mul_assoc, mul_comm];
    norm_num [ Matrix.det_apply' ] at *;
    exact_mod_cast h_det_z_nonzero;
  norm_cast at *;
  refine' ⟨ _, _, _ ⟩;
  exact Matrix.det ( Matrix.of fun i j => C i ( Fin.cast hs.symm j ) );
  · intro h; simp_all +decide [ sq ] ;
  · norm_num [ ← h_det_C_sq, ← h_det_C_prod ];
    convert congr_arg ( ( ↑ ) : ℤ → ℝ ) h_det_C_prod.symm using 1;
    norm_num [ Matrix.det_apply' ]

/-
ℤ-linear independence of integer vectors implies ℝ-linear independence.
-/
lemma int_linearIndependent_implies_real
    (r s : ℕ) (z : Fin r → (Fin s → ℤ))
    (hz : LinearIndependent ℤ z) :
    LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((z k i : ℤ) : ℝ))) := by
  convert Fintype.linearIndependent_iff.mpr _;
  exact inferInstance;
  intro g hg i
  by_contra h_nonzero
  have h_det : Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin s, (z i k : ℝ) * (z j k : ℝ))) = 0 := by
    rw [ ← Matrix.exists_vecMul_eq_zero_iff ];
    refine' ⟨ g, _, _ ⟩ <;> simp_all +decide [ funext_iff, Matrix.vecMul, dotProduct ];
    · use i;
    · intro i; simp +decide only [Finset.mul_sum _ _ _] ;
      rw [ Finset.sum_comm ] ; simp_all +decide [ ← mul_assoc, ← Finset.sum_mul ] ;
  generalize_proofs at *; (
  -- By the properties of the Gram determinant, if the determinant is zero, then the vectors are linearly dependent over the integers.
  have h_lin_dep_int : ∃ d : Fin r → ℤ, d ≠ 0 ∧ ∑ i, d i • z i = 0 := by
    -- By the properties of the Gram determinant, if the determinant is zero, then the vectors are linearly dependent over the rationals.
    have h_lin_dep_rat : ∃ d : Fin r → ℚ, d ≠ 0 ∧ ∑ i, d i • (fun i_1 => (z i i_1 : ℚ)) = 0 := by
      have h_lin_dep_rat : ∃ d : Fin r → ℚ, d ≠ 0 ∧ Matrix.mulVec (Matrix.of (fun i j : Fin r => ∑ k : Fin s, (z i k : ℚ) * (z j k : ℚ))) d = 0 := by
        convert Matrix.exists_mulVec_eq_zero_iff.mpr _;
        all_goals try infer_instance
        generalize_proofs at *; (
        convert h_det using 1
        generalize_proofs at *; (
        norm_num [ Matrix.det_apply' ];
        norm_cast))
      generalize_proofs at *; (
      obtain ⟨ d, hd_ne_zero, hd_eq_zero ⟩ := h_lin_dep_rat
      use d
      generalize_proofs at *; (
      have h_lin_dep_rat : ∑ i, d i • (fun i_1 => (z i i_1 : ℚ)) = 0 := by
        have h_inner : ∀ i, ∑ j, d j * (∑ k, (z i k : ℚ) * (z j k : ℚ)) = 0 := by
          exact fun i => by simpa [ Matrix.mulVec, dotProduct, mul_comm ] using congr_fun hd_eq_zero i;
        have h_inner : ∑ i, ∑ j, d i * d j * (∑ k, (z i k : ℚ) * (z j k : ℚ)) = 0 := by
          simp_all +decide [ ← Finset.mul_sum _ _ _, mul_assoc ]
        generalize_proofs at *; (
        have h_inner : ∑ k, (∑ i, d i * (z i k : ℚ)) ^ 2 = 0 := by
          convert h_inner using 1
          generalize_proofs at *; (
          simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_comm, mul_left_comm];
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) ))
        generalize_proofs at *; (
        exact funext fun k => by simpa [ sq ] using Finset.sum_eq_zero_iff_of_nonneg ( fun _ _ => sq_nonneg _ ) |>.1 h_inner k;))
      generalize_proofs at *; (
      exact ⟨ hd_ne_zero, h_lin_dep_rat ⟩)))
    generalize_proofs at *; (
    obtain ⟨ d, hd₁, hd₂ ⟩ := h_lin_dep_rat
    generalize_proofs at *; (
    -- Let $q$ be the least common multiple of the denominators of the coefficients $d_i$.
    obtain ⟨q, hq⟩ : ∃ q : ℕ, q > 0 ∧ ∀ i, ∃ k : ℤ, d i = k / q := by
      use ∏ i, (d i).den, Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Rat.pos _), fun i => ⟨(d i).num * (∏ j ∈ Finset.univ.erase i, (d j).den), by
        simp +decide [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i ) ];
        rw [ mul_div_mul_right _ _ <| Finset.prod_ne_zero_iff.mpr fun j hj => Nat.cast_ne_zero.mpr <| Rat.den_nz _, Rat.num_div_den ]⟩
    generalize_proofs at *; (
    choose k hk using hq.2; use fun i => k i; simp_all +decide [funext_iff] ;
    simp_all +decide [ div_mul_eq_mul_div, ← Finset.sum_div _ _ _, ne_of_gt hq ];
    exact_mod_cast hd₂;)))
  generalize_proofs at *; (
  exact h_lin_dep_int.elim fun d hd => hd.1 <| by simpa [ funext_iff ] using Fintype.linearIndependent_iff.mp hz d hd.2;))

/-
The kernel of a ℤ-linear map from ℤ^n is a direct summand.
-/
lemma kernel_has_complement
    (n m : ℕ) (phi : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)) :
    ∃ W : Submodule ℤ (Fin n → ℤ), IsCompl (LinearMap.ker phi) W := by
  obtain ⟨sec, hsec⟩ : ∃ sec : (Fin n → ℤ) ⧸ phi.ker →ₗ[ℤ] (Fin n → ℤ), Submodule.mkQ phi.ker ∘ₗ sec = LinearMap.id := by
    convert Module.projective_lifting_property ( Submodule.mkQ phi.ker ) LinearMap.id ( Submodule.Quotient.mk_surjective _ );
    convert Module.Projective.of_equiv ( phi.quotKerEquivRange ).symm;
  refine' ⟨ LinearMap.range sec, _, _ ⟩;
  · simp_all +decide [ Submodule.disjoint_def, LinearMap.ext_iff ];
    intro x hx y hy; specialize hsec y; simp_all +decide ;
    rw [ ← hy, show y = 0 from by rw [ ← hsec, show Submodule.Quotient.mk x = 0 from by rw [ Submodule.Quotient.mk_eq_zero ] ; aesop ] ] ; aesop;
  · rw [ codisjoint_iff ];
    ext x; simp ;
    rw [ Submodule.mem_sup ];
    refine' ⟨ x - sec ( Submodule.mkQ phi.ker x ), _, sec ( Submodule.mkQ phi.ker x ), _, _ ⟩ <;> norm_num;
    replace hsec := LinearMap.congr_fun hsec ( Submodule.Quotient.mk x ) ; simp_all +decide ;
    rw [ ← eq_comm, ← sub_eq_zero ] ; erw [ Submodule.Quotient.eq ] at hsec ; aesop;

/-
The Gram determinant of ℤ-linearly independent integer vectors is a positive
integer, hence ≥ 1.
-/
lemma gramDet_int_ge_one
    (r s : ℕ) (z : Fin r → (Fin s → ℤ))
    (hz : LinearIndependent ℤ z) :
    1 ≤ gramDet r s (fun k i => ((z k i : ℤ) : ℝ)) := by
  -- Since the vectors $z$ are $\mathbb{Z}$-linearly independent, they are also $\mathbb{R}$-linearly independent.
  have h_real_indep : LinearIndependent ℝ (fun k => fun i => ((z k i : ℤ) : ℝ)) := by
    convert int_linearIndependent_implies_real r s z hz using 1;
  -- Since the vectors $z$ are $\mathbb{R}$-linearly independent, the Gram matrix $G$ is positive definite.
  have h_pos_def : Matrix.PosDef (Matrix.of (fun i j => ∑ k, (z i k : ℝ) * (z j k : ℝ))) := by
    have h_pos_def : ∀ (v : Fin r → ℝ), v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * ∑ k, (z i k : ℝ) * (z j k : ℝ) := by
      intro v hv_ne_zero
      have h_pos_def : 0 < ∑ k, (∑ i, v i * (z i k : ℝ)) ^ 2 := by
        contrapose! hv_ne_zero
        generalize_proofs at *; (
        have h_zero : ∀ k, ∑ i, v i * (z i k : ℝ) = 0 := by
          exact fun k => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( ∑ i, v i * ( z i a : ℝ ) ) ) ( Finset.mem_univ k ) ) hv_ne_zero ) ( sq_nonneg _ ) )
        generalize_proofs at *; (
        rw [ Fintype.linearIndependent_iff ] at h_real_indep
        generalize_proofs at *; (
        exact funext fun i => h_real_indep v ( by ext k; simpa [ mul_comm ] using h_zero k ) i)))
      generalize_proofs at *; (
      convert h_pos_def using 1 ; simp +decide [ pow_two, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _] ; ring_nf!;
      exact sum_comm_cycle)
    generalize_proofs at *; (
    constructor <;> norm_num [ Matrix.PosDef ];
    · ext i j; simp +decide [ mul_comm ] ;
    · intro x hx; specialize h_pos_def ( fun i => x i ) ; simp_all +decide [ Finsupp.sum_fintype, mul_assoc, mul_comm, mul_left_comm ] ;);
  -- Since the determinant of a positive definite matrix with integer entries is a positive integer, we have $\det(G) \geq 1$.
  have h_det_int : ∃ d : ℤ, Matrix.det (Matrix.of (fun i j => ∑ k, (z i k : ℝ) * (z j k : ℝ))) = d := by
    norm_num [ Matrix.det_apply' ];
    exact ⟨ ∑ x : Equiv.Perm ( Fin r ), Equiv.Perm.sign x * ∏ x_1 : Fin r, ∑ k : Fin s, z ( x x_1 ) k * z x_1 k, by push_cast; rfl ⟩;
  obtain ⟨ d, hd ⟩ := h_det_int; have := h_pos_def.det_pos; simp_all +decide [ gramDet ] ;
  exact_mod_cast this

/-
The kernel of a ℤ-linear map ℤ^{2r} → ℤ^r has rank ≥ r.
-/
lemma ker_rank_ge_r
    (r : ℕ) (phi : (Fin (2 * r) → ℤ) →ₗ[ℤ] (Fin r → ℤ)) :
    r ≤ Module.finrank ℤ (LinearMap.ker phi) := by
  -- By rank-nullity, we have that the dimension of the domain is equal to the dimension of the kernel plus the dimension of the range.
  have h_rank_nullity : Module.finrank ℤ (Fin (2 * r) → ℤ) = Module.finrank ℤ (↥phi.ker) + Module.finrank ℤ (↥(LinearMap.range phi)) := by
    have := Submodule.finrank_quotient_add_finrank phi.ker;
    rw [ ← this, add_comm, ← LinearEquiv.finrank_eq ( phi.quotKerEquivRange ) ];
  norm_num +zetaDelta at *;
  linarith [ show Module.finrank ℤ ( LinearMap.range phi ) ≤ r from le_trans ( Submodule.finrank_le _ ) ( by norm_num ) ]

/-
For a ℤ-linear map phi : ℤ^{2r} → ℤ^r, there exist z (in ker) and w (complement)
    such that [z|w] is a unimodular matrix. The z are ℤ-linearly independent kernel vectors
    and [z|w] forms a basis of ℤ^{2r}.
-/
set_option maxHeartbeats 1600000 in
lemma kernel_and_complement_exist
    (r : ℕ) (hr : 0 < r)
    (phi : (Fin (2 * r) → ℤ) →ₗ[ℤ] (Fin r → ℤ)) :
    ∃ (z w : Fin r → (Fin (2 * r) → ℤ)),
      (∀ k : Fin r, phi (z k) = 0) ∧
      LinearIndependent ℤ z ∧
      let Q : Matrix (Fin (2 * r)) (Fin (2 * r)) ℤ :=
        Matrix.of (fun i j =>
          if h : j.val < r then z ⟨j.val, h⟩ i
          else w ⟨j.val - r, by omega⟩ i)
      Q.det = 1 ∨ Q.det = -1 := by
  have h_basis : ∃ (b : Module.Basis (Fin (2 * r)) ℤ (Fin (2 * r) → ℤ)), (∀ k : Fin r, phi (b (Fin.castLE (by omega) k)) = 0) := by
    -- Let $K = \ker(\phi)$ and $W$ be a complement of $K$ in $\mathbb{Z}^{2r}$.
    obtain ⟨K, W, hK, hW, h_compl⟩ : ∃ K W : Submodule ℤ (Fin (2 * r) → ℤ), K = LinearMap.ker phi ∧ IsCompl K W := by
      exact ⟨ _, _, rfl, kernel_has_complement _ _ _ |> Classical.choose_spec ⟩;
    obtain ⟨bK, hbK⟩ : ∃ bK : Module.Basis (Fin (Module.finrank ℤ K)) ℤ K, True := by
      exact ⟨ Module.finBasis ℤ K, trivial ⟩
    obtain ⟨bW, hbW⟩ : ∃ bW : Module.Basis (Fin (Module.finrank ℤ W)) ℤ W, True := by
      exact ⟨ Module.finBasis ℤ W, trivial ⟩;
    -- Combine the bases of K and W to form a basis of ℤ^{2r}.
    obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin (Module.finrank ℤ K + Module.finrank ℤ W)) ℤ (Fin (2 * r) → ℤ), (∀ k : Fin (Module.finrank ℤ K), b (Fin.castLE (by omega) k) ∈ K) ∧ (∀ k : Fin (Module.finrank ℤ W), b (Fin.castLE (by omega) (Fin.addNat k (Module.finrank ℤ K))) ∈ W) := by
      have h_combined_basis : ∃ b : Module.Basis (Fin (Module.finrank ℤ K) ⊕ Fin (Module.finrank ℤ W)) ℤ (Fin (2 * r) → ℤ), (∀ k : Fin (Module.finrank ℤ K), b (Sum.inl k) ∈ K) ∧ (∀ k : Fin (Module.finrank ℤ W), b (Sum.inr k) ∈ W) := by
        refine' ⟨ _, _, _ ⟩;
        refine' ( bK.prod bW ).map _;
        refine' ( Submodule.prodEquivOfIsCompl K W _ );
        exact ⟨ hW, h_compl ⟩;
        · simp +decide [ Submodule.prodEquivOfIsCompl ];
        · simp +decide [ Module.Basis.map ];
      obtain ⟨ b, hb₁, hb₂ ⟩ := h_combined_basis;
      refine' ⟨ b.reindex ( Equiv.ofBijective _ ⟨ _, _ ⟩ ), _, _ ⟩;
      use fun x => x.elim ( fun k => Fin.castLE ( by omega ) k ) ( fun k => Fin.castLE ( by omega ) ( k.addNat ( Module.finrank ℤ K ) ) );
      all_goals norm_num [ Function.Injective, Function.Surjective ];
      all_goals norm_num [ Fin.ext_iff, Fin.val_add ];
      exact ⟨ fun a b h => False.elim <| by linarith [ Fin.is_lt a, Fin.is_lt b ], fun b a h => False.elim <| by linarith [ Fin.is_lt a, Fin.is_lt b ] ⟩;
      exact fun x => if hx : x.val < Module.finrank ℤ K then Or.inl ⟨ ⟨ x.val, hx ⟩, rfl ⟩ else Or.inr ⟨ ⟨ x.val - Module.finrank ℤ K, by omega ⟩, by simp +decide [ Nat.sub_add_cancel ( show Module.finrank ℤ K ≤ x.val from le_of_not_gt hx ) ] ⟩;
      · intro k; convert hb₁ k using 1;
        congr! 1;
        simp +decide [ Equiv.symm_apply_eq ];
      · intro k; convert hb₂ k using 1;
        congr! 1;
        simp +decide [ Equiv.symm_apply_eq ];
    have h_rank : Module.finrank ℤ K + Module.finrank ℤ W = 2 * r := by
      convert Module.finrank_eq_card_basis b |> Eq.symm; all_goals norm_num;
    use b.reindex (finCongr h_rank);
    intro k; specialize hb; have := hb.1 ⟨ k, by linarith [ Fin.is_lt k, show Module.finrank ℤ K ≥ r from by
                                                                          have := ker_rank_ge_r r phi; aesop; ] ⟩ ; aesop;
  obtain ⟨ b, hb ⟩ := h_basis;
  refine' ⟨ fun k => b ( Fin.castLE ( by omega ) k ), fun k => b ( Fin.castLE ( by omega ) ( Fin.addNat k r ) ), _, _, _ ⟩ <;> simp_all +decide [ Fintype.linearIndependent_iff ];
  · intro g hg i; have := b.linearIndependent; simp_all +decide [ Fintype.linearIndependent_iff ] ;
    convert this ( fun x => if hx : x.val < r then g ⟨ x.val, hx ⟩ else 0 ) _ ⟨ i, by linarith [ Fin.is_lt i ] ⟩ using 1 ; simp +decide ;
    rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun x : Fin r => Fin.castLE ( by omega ) x ) Finset.univ ) ) ] <;> norm_num [ Finset.sum_image ];
    · rw [ Finset.sum_image ] ; aesop;
      exact fun x _ y _ h => by simpa [ Fin.ext_iff ] using h;
    · intro x hx; split_ifs <;> simp_all +decide [ Fin.ext_iff ] ;
      exact False.elim <| hx ⟨ x, by linarith ⟩ rfl;
  · have h_det : Matrix.det (Matrix.of (fun i j => b j i)) = 1 ∨ Matrix.det (Matrix.of (fun i j => b j i)) = -1 := by
      have h_det : IsUnit (Matrix.det (Matrix.of (fun i j => b j i))) := by
        have h_det : IsUnit (Matrix.det (Matrix.of (fun i j => b j i))) := by
          have h_basis : ∀ (v : Fin (2 * r) → ℤ), ∃ (c : Fin (2 * r) → ℤ), v = ∑ i, c i • b i := by
            exact fun v => ⟨ _, Eq.symm ( b.sum_repr v ) ⟩
          have h_det : ∀ (v : Fin (2 * r) → ℤ), ∃ (c : Fin (2 * r) → ℤ), v = Matrix.mulVec (Matrix.of (fun i j => b j i)) c := by
            intro v; obtain ⟨ c, hc ⟩ := h_basis v; use c; ext i; simp +decide [ hc, Matrix.mulVec, dotProduct ] ;
            grind +revert
          generalize_proofs at *;
          have h_det : Function.Surjective (Matrix.mulVec (Matrix.of (fun i j => b j i))) := by
            exact fun v => by obtain ⟨ c, rfl ⟩ := h_det v; exact ⟨ c, rfl ⟩ ;
          generalize_proofs at *;
          have h_det : ∃ (A : Matrix (Fin (2 * r)) (Fin (2 * r)) ℤ), Matrix.of (fun i j => b j i) * A = 1 := by
            exact Matrix.mulVec_surjective_iff_exists_right_inverse.mp h_det
          generalize_proofs at *;
          exact isUnit_iff_exists_inv.mpr ⟨ h_det.choose.det, by simpa using congr_arg Matrix.det h_det.choose_spec ⟩
        generalize_proofs at *;
        exact h_det;
      exact Int.isUnit_iff.mp h_det;
    convert h_det using 1;
    · congr! 2;
      ext i j; aesop;
    · congr! 2;
      ext i j; aesop

/-
Annihilator determinant bound
-/
set_option maxHeartbeats 3200000 in
lemma det_block_zero_upper_left (r : ℕ)
    (B C D : Matrix (Fin r) (Fin r) ℤ) :
    Matrix.det (Matrix.fromBlocks 0 B C D) =
    (-1) ^ (r * r) * Matrix.det B * Matrix.det C := by
  -- The swap matrix is a permutation matrix with sign (-1)^r.
  have h_swap_sign : Matrix.det (Matrix.fromBlocks 0 (1 : Matrix (Fin r) (Fin r) ℤ) 1 0) = (-1 : ℤ) ^ r := by
    convert Matrix.det_permutation ( Equiv.sumComm ( Fin r ) ( Fin r ) ) using 1;
    all_goals try infer_instance;
    · congr ; ext i j ; aesop;
    · -- The permutation sumComm (Fin r) (Fin r) can be decomposed into r transpositions.
      have h_decomp : ∃ σ : Equiv.Perm (Fin r ⊕ Fin r), σ = Equiv.sumComm (Fin r) (Fin r) ∧ σ.support.card = 2 * r := by
        simp +decide [ two_mul, Equiv.Perm.support ];
        rw [ Finset.filter_true_of_mem ] <;> simp +decide [ Finset.card_univ ];
      obtain ⟨ σ, hσ₁, hσ₂ ⟩ := h_decomp; rw [ ← hσ₁ ] ; rw [ Equiv.Perm.sign_of_cycleType ] ; simp +decide ;
      have := Equiv.Perm.sum_cycleType σ; simp_all +decide [ two_mul ] ;
      have h_cycle_type : ∀ c ∈ Equiv.Perm.cycleType (Equiv.sumComm (Fin r) (Fin r)), c = 2 := by
        intro c hc; have := Equiv.Perm.two_le_of_mem_cycleType hc; (
        have h_cycle_type : ∀ c ∈ Equiv.Perm.cycleType (Equiv.sumComm (Fin r) (Fin r)), c ≤ 2 := by
          intros c hc; exact (by
          have h_cycle_type : ∀ c ∈ Equiv.Perm.cycleType (Equiv.sumComm (Fin r) (Fin r)), c ∣ 2 := by
            intros c hc; exact (by
            have h_cycle_type : ∀ c ∈ Equiv.Perm.cycleType (Equiv.sumComm (Fin r) (Fin r)), c ∣ orderOf (Equiv.sumComm (Fin r) (Fin r)) := by
              exact fun c a => Equiv.Perm.dvd_of_mem_cycleType a;
            exact dvd_trans ( h_cycle_type c hc ) ( orderOf_dvd_of_pow_eq_one ( by aesop ) ));
          exact Nat.le_of_dvd ( by decide ) ( h_cycle_type c hc ));
        exact le_antisymm ( h_cycle_type c hc ) this);
      rw [ Multiset.eq_replicate_of_mem fun x hx => h_cycle_type x hx ] at this ⊢ ; norm_num at this ⊢ ; ring_nf at this ⊢ ; aesop;
  convert congr_arg ( fun x : ℤ => x * Matrix.det ( Matrix.fromBlocks C D 0 B ) ) h_swap_sign using 1;
  · convert Matrix.det_mul _ _ using 2 ; norm_num [ Matrix.fromBlocks_multiply ];
  · rw [ Matrix.det_fromBlocks_zero₂₁ ] ; ring_nf;
    rcases Nat.even_or_odd' r with ⟨ k, rfl | rfl ⟩ <;> ring_nf <;> norm_num

set_option maxHeartbeats 3200000 in
lemma gramDet_divides_combined_det
    (r : ℕ) (hr : 0 < r)
    (b z w : Fin r → (Fin (2 * r) → ℤ))
    (h_orth : ∀ j k : Fin r, ∑ i, b j i * z k i = 0)
    (h_unimod : let Q : Matrix (Fin (2 * r)) (Fin (2 * r)) ℤ :=
        Matrix.of (fun i j =>
          if h : j.val < r then z ⟨j.val, h⟩ i
          else w ⟨j.val - r, by omega⟩ i)
      Q.det = 1 ∨ Q.det = -1) :
    (Matrix.det (Matrix.of (fun i j : Fin r => ∑ k, z i k * z j k))) ∣
    (Matrix.det (Matrix.of (fun i j : Fin (2 * r) =>
      if h : i.val < r then b ⟨i.val, h⟩ j
      else z ⟨i.val - r, by omega⟩ j))) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin (2 * r)) (Fin (2 * r)) ℤ, (∀ i j : Fin (2 * r), Q i j = if h : j.val < r then (z (Fin.mk j.val h)) i else (w (Fin.mk (j.val - r) (by omega))) i) ∧ (Q.det = 1 ∨ Q.det = -1) := by
    exact ⟨ _, fun i j => rfl, h_unimod ⟩;
  set C : Matrix (Fin (2 * r)) (Fin (2 * r)) ℤ := Matrix.of (fun i j => if h : i.val < r then b (Fin.mk i.val h) j else z (Fin.mk (i.val - r) (by omega)) j);
  have h_det_CQ : Matrix.det (C * Q) = (-1) ^ (r * r) * Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin (2 * r), b i k * w j k)) * Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin (2 * r), z i k * z j k)) := by
    convert det_block_zero_upper_left r ( Matrix.of ( fun i j => ∑ k, b i k * w j k ) ) ( Matrix.of ( fun i j => ∑ k, z i k * z j k ) ) ( Matrix.of ( fun i j => ∑ k, z i k * w j k ) ) using 1;
    rw [ ← Matrix.det_submatrix_equiv_self ( Equiv.ofBijective ( fun i : Fin r ⊕ Fin r => Sum.elim ( fun i => ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ) ( fun i => ⟨ i + r, by linarith [ Fin.is_lt i ] ⟩ ) i ) ⟨ fun i => ?_, fun i => ?_ ⟩ ) ];
    congr! 1;
    ext i j;
    all_goals norm_num [ Fin.ext_iff, Matrix.mul_apply ];
    · rcases i with ( i | i ) <;> rcases j with ( j | j ) <;> simp +decide [ *, Matrix.fromBlocks ];
      · aesop;
      · aesop;
      · simp +zetaDelta at *;
      · simp +zetaDelta at *;
    · grind;
    · exact if hi : ( i : ℕ ) < r then Or.inl ⟨ ⟨ i, hi ⟩, rfl ⟩ else Or.inr ⟨ ⟨ i - r, by omega ⟩, by rw [ Nat.sub_add_cancel ( by linarith ) ] ⟩;
  cases hQ.2 <;> simp_all +decide [ Matrix.det_mul ];
  exact ⟨ - ( -1 ) ^ ( r * r ) * Matrix.det ( Matrix.of fun i j => ∑ k, b i k * w j k ), by linarith ⟩

set_option maxHeartbeats 3200000 in
lemma annihilator_det_bound
    (r : ℕ) (hr : 1 ≤ r) (s : ℕ) (hs : s = 2 * r)
    (b : Fin r → (Fin s → ℤ))
    (hb_indep : LinearIndependent ℝ (fun j : Fin r => (fun i : Fin s => ((b j i : ℤ) : ℝ)))) :
    ∃ z : Fin r → (Fin s → ℤ),
      (∀ k j : Fin r, ∑ i : Fin s, (z k i : ℝ) * (b j i : ℝ) = 0) ∧
      LinearIndependent ℤ z ∧
      gramDet r s (fun k i => ((z k i : ℤ) : ℝ)) ≤
        gramDet r s (fun j i => ((b j i : ℤ) : ℝ)) := by
  subst hs
  -- Define the linear map phi
  set phi : (Fin (2 * r) → ℤ) →ₗ[ℤ] (Fin r → ℤ) :=
    { toFun := fun x j => ∑ i, b j i * x i,
      map_add' := fun x y => funext fun j => by simp [mul_add, Finset.sum_add_distrib],
      map_smul' := fun c x => funext fun j => by simp [mul_left_comm, Finset.mul_sum] }
  -- Get z, w from kernel_and_complement_exist
  obtain ⟨z, w, hz_ker, hz_indep, h_unimod⟩ := kernel_and_complement_exist r (by omega) phi
  -- Orthogonality (integer version)
  have h_orth_int : ∀ k j : Fin r, ∑ i, b j i * z k i = 0 := by
    intro k j; have := congr_fun (hz_ker k) j; simp [phi] at this; exact this
  -- Orthogonality (real version, with b*z)
  have h_orth_bz : ∀ j k : Fin r, ∑ i, (b j i : ℝ) * (z k i : ℝ) = 0 := by
    intro j k; exact_mod_cast h_orth_int k j
  -- Orthogonality (real version, with z*b)
  have h_orth_zb : ∀ k j : Fin r, ∑ i, (z k i : ℝ) * (b j i : ℝ) = 0 := by
    intro k j; rw [← h_orth_bz j k]; congr 1; ext; ring
  refine ⟨z, h_orth_zb, hz_indep, ?_⟩
  -- gramDet bound
  -- z is ℝ-linearly independent
  have h_z_real_indep := int_linearIndependent_implies_real r (2 * r) z hz_indep
  -- gramDet(z) as integer and ≥ 1
  have hgz_ge_one := gramDet_int_ge_one r (2 * r) z hz_indep
  -- Get D from gramDet_product_is_square
  obtain ⟨D, hD_ne, hD_sq⟩ := gramDet_product_is_square r (2 * r) rfl b z h_orth_bz hb_indep h_z_real_indep
  -- gramDet_int(z) | det(C)
  have h_div := gramDet_divides_combined_det r (by omega) b z w (fun j k => h_orth_int k j) h_unimod
  have hD_eq_detC : (Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin (2 * r), (b i k : ℝ) * (b j k : ℝ)))) * (Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin (2 * r), (z i k : ℝ) * (z j k : ℝ)))) = (Matrix.det (Matrix.of (fun i j : Fin (2 * r) => if h : i.val < r then (b ⟨i.val, h⟩ j : ℝ) else (z ⟨i.val - r, by omega⟩ j : ℝ)))) ^ 2 := by
    have h_detC_sq : Matrix.det (Matrix.of (fun i j : Fin (2 * r) => if h : i.val < r then (b ⟨i.val, h⟩ j : ℝ) else (z ⟨i.val - r, by omega⟩ j : ℝ))) ^ 2 = Matrix.det (Matrix.of (fun i j : Fin (2 * r) => ∑ k : Fin (2 * r), (if h : i.val < r then (b ⟨i.val, h⟩ k : ℝ) else (z ⟨i.val - r, by omega⟩ k : ℝ)) * (if h : j.val < r then (b ⟨j.val, h⟩ k : ℝ) else (z ⟨j.val - r, by omega⟩ k : ℝ)))) := by
      have h_detC_sq : Matrix.det (Matrix.of (fun i j : Fin (2 * r) => if h : i.val < r then (b ⟨i.val, h⟩ j : ℝ) else (z ⟨i.val - r, by omega⟩ j : ℝ))) ^ 2 = Matrix.det (Matrix.of (fun i j : Fin (2 * r) => ∑ k : Fin (2 * r), (if h : i.val < r then (b ⟨i.val, h⟩ k : ℝ) else (z ⟨i.val - r, by omega⟩ k : ℝ)) * (if h : j.val < r then (b ⟨j.val, h⟩ k : ℝ) else (z ⟨j.val - r, by omega⟩ k : ℝ)))) := by
        have h_detC_sq : Matrix.of (fun i j : Fin (2 * r) => ∑ k : Fin (2 * r), (if h : i.val < r then (b ⟨i.val, h⟩ k : ℝ) else (z ⟨i.val - r, by omega⟩ k : ℝ)) * (if h : j.val < r then (b ⟨j.val, h⟩ k : ℝ) else (z ⟨j.val - r, by omega⟩ k : ℝ))) = Matrix.of (fun i j : Fin (2 * r) => if h : i.val < r then (b ⟨i.val, h⟩ j : ℝ) else (z ⟨i.val - r, by omega⟩ j : ℝ)) * Matrix.transpose (Matrix.of (fun i j : Fin (2 * r) => if h : i.val < r then (b ⟨i.val, h⟩ j : ℝ) else (z ⟨i.val - r, by omega⟩ j : ℝ))) := by
          ext i j; simp +decide [ Matrix.mul_apply ] ;
        rw [ h_detC_sq, Matrix.det_mul, Matrix.det_transpose, sq ];
      convert h_detC_sq using 1;
    rw [ h_detC_sq ];
    convert gramDet_orthogonal_factorization r ( 2 * r ) rfl ( fun i k => ( b i k : ℝ ) ) ( fun i k => ( z i k : ℝ ) ) h_orth_bz |> Eq.symm using 1;
    congr! 3;
    ext j; split_ifs <;> simp +decide [ * ] ;
  obtain ⟨ k, hk ⟩ := h_div;
  have hD_eq_k_detz : (D : ℝ) ^ 2 = (k : ℝ) ^ 2 * (Matrix.det (Matrix.of (fun i j : Fin r => ∑ k : Fin (2 * r), (z i k : ℝ) * (z j k : ℝ)))) ^ 2 := by
    rw [ ← hD_sq, hD_eq_detC ];
    convert congr_arg ( · ^ 2 ) ( congr_arg ( ( ↑ ) : ℤ → ℝ ) hk ) using 1 ; norm_num [ Matrix.det_apply' ] ; ring_nf;
    · exact congr_arg ( · ^ 2 ) ( Finset.sum_congr rfl fun _ _ => by congr; ext; split_ifs <;> norm_cast );
    · norm_num [ Matrix.det_apply' ] ; ring;
  unfold gramDet at *;
  norm_num [ Matrix.det_apply' ] at *;
  norm_cast at *;
  nlinarith [ show k ^ 2 > 0 by exact sq_pos_of_ne_zero ( show k ≠ 0 by rintro rfl; exact hD_ne <| by nlinarith ) ]

/-
Combined result: orthogonal lattice short vectors
-/
set_option maxHeartbeats 800000 in
lemma orthogonal_lattice_short_vectors
    (r : ℕ) (hr : 1 ≤ r) (s : ℕ) (hs : s = 2 * r)
    (b : Fin r → (Fin s → ℤ))
    (hb_indep : LinearIndependent ℝ (fun j : Fin r => (fun i : Fin s => ((b j i : ℤ) : ℝ)))) :
    ∃ y : Fin r → (Fin s → ℤ),
      (∀ k j : Fin r, ∑ i : Fin s, (y k i : ℝ) * (b j i : ℝ) = 0) ∧
      LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((y k i : ℤ) : ℝ))) ∧
      Monotone (fun k : Fin r => ∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ∧
      ∏ k : Fin r, (∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (r * (r - 1)) *
        ∏ j : Fin r, (∑ i : Fin s, ((b j i : ℤ) : ℝ) ^ 2) := by
  have := @annihilator_det_bound r hr s hs b hb_indep;
  obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := this; have := successive_minima_product_bound_abstract r s hr ( by omega ) z hz₂; simp_all +decide [ Monotone ] ;
  refine' ⟨ this.choose, _, this.choose_spec.2.1, this.choose_spec.2.2.1, this.choose_spec.2.2.2.trans _ ⟩;
  · intro k j
    have h_span : this.choose k ∈ Submodule.span ℤ (Set.range z) := by
      exact this.choose_spec.1 k
    have h_kernel : ∀ v ∈ Submodule.span ℤ (Set.range z), ∀ j, ∑ i, (v i : ℝ) * (b j i : ℝ) = 0 := by
      intro v hv j; induction hv using Submodule.span_induction <;> simp_all +decide [ Finset.sum_add_distrib, add_mul ] ;
      · aesop;
      · simp_all +decide [ mul_assoc, ← Finset.mul_sum _ _ _ ]
    exact h_kernel (this.choose k) h_span j;
  · exact mul_le_mul_of_nonneg_left ( hz₃.trans ( gramDet_le_prod_sq_norms r s _ ) ) ( by positivity )

/-! ## Vandermonde kernel lemma -/

/-- If u : Fin s → ℤ is strictly monotone and w_i > 0, and
a is in ℤ^s with ∑ a_i w_i u_i^j = 0 for ALL j < s, then a = 0. -/
lemma weighted_vandermonde_trivial_kernel
    (s : ℕ)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i)
    (a : Fin s → ℤ)
    (ha : ∀ j : ℕ, j < s → ∑ i, (a i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) :
    a = 0 := by
  have h_vandermonde : Matrix.det (Matrix.of (fun i j : Fin s => (w j : ℝ) * (u j : ℝ) ^ (i : ℕ))) ≠ 0 := by
    have h_vandermonde_det : Matrix.det (Matrix.of (fun i j : Fin s => (u j : ℝ) ^ (i : ℕ))) ≠ 0 := by
      erw [ Matrix.det_transpose, Matrix.det_vandermonde ]
      exact Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero_of_ne <| mod_cast hu_strict.injective.ne <| ne_of_gt <| Finset.mem_Ioi.mp hj
    convert mul_ne_zero h_vandermonde_det ( show ( ∏ i : Fin s, ( w i : ℝ ) ) ≠ 0 from Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr <| ne_of_gt <| hw_pos i ) using 1
    simp +decide [ Matrix.det_apply', mul_comm, Finset.prod_mul_distrib ]
    simp +decide only [mul_assoc, Finset.mul_sum _ _ _]
  have h_mulvec : Matrix.mulVec (Matrix.of (fun i j : Fin s => (w j : ℝ) * (u j : ℝ) ^ (i : ℕ))) (fun i => (a i : ℝ)) = 0 := by
    ext i; simp_all +decide [ Matrix.mulVec, dotProduct, mul_comm, mul_left_comm ]
  exact funext fun i => by simpa [ funext_iff ] using Matrix.eq_zero_of_mulVec_eq_zero ‹_› h_mulvec |> fun h => by simpa [ funext_iff ] using congr_fun h i

/-
Among r linearly independent integer kernel vectors, at least one has nonzero r-th moment.
-/
set_option maxHeartbeats 800000 in
lemma excess_zero_among_independent
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i)
    (v : Fin r → (Fin s → ℤ))
    (hv_kernel : ∀ (k : Fin r) (j : ℕ), j < r →
      ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0)
    (hv_indep : LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((v k i : ℤ) : ℝ)))) :
    ∃ m : Fin r, ∑ i, (v m i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0 := by
  by_contra h_contra
  push_neg at h_contra
  have h_all_zero : ∀ k : Fin r, ∑ i, ((v k i) : ℝ) * (w i : ℝ) * ((u i) : ℝ) ^ r = 0 := by
    exact h_contra
  have h_contra : r ≤ r - 1 := by
    have h_contra : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun k : Fin r => fun i : Fin s => (v k i : ℝ)))) ≤ Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (Matrix.of (fun (j : Fin (r + 1)) (i : Fin s) => (w i : ℝ) * ((u i) : ℝ) ^ (j : ℕ))))) := by
      refine' Submodule.finrank_mono _;
      rw [ Submodule.span_le ];
      rintro _ ⟨ k, rfl ⟩ ; ext j; simp +decide [ Matrix.mulVec, dotProduct, mul_comm, mul_left_comm] ;
      by_cases hj : j.val < r <;> simp_all +decide [ mul_comm];
      rw [ show ( j : ℕ ) = r by linarith [ Fin.is_lt j ] ] ; exact h_contra k;
    have h_contra : Matrix.rank (Matrix.of (fun (j : Fin (r + 1)) (i : Fin s) => (w i : ℝ) * ((u i) : ℝ) ^ (j : ℕ))) = r + 1 := by
      have h_contra : LinearIndependent ℝ (fun j : Fin (r + 1) => fun i : Fin s => (w i : ℝ) * ((u i) : ℝ) ^ (j : ℕ)) := by
        refine' Fintype.linearIndependent_iff.2 _;
        intro g hg i
        have h_poly : ∀ x : ℝ, ∑ j : Fin (r + 1), g j * x ^ (j : ℕ) = 0 := by
          have h_poly : ∀ x : ℝ, ∑ j : Fin (r + 1), g j * x ^ (j : ℕ) = 0 := by
            intro x
            have h_poly_eq : ∀ i : Fin s, ∑ j : Fin (r + 1), g j * (u i : ℝ) ^ (j : ℕ) = 0 := by
              intro i; replace hg := congr_fun hg i; simp_all +decide [ mul_comm ] ;
              simp_all +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _ ];
              exact hg.resolve_right ( ne_of_gt ( hw_pos i ) )
            have h_poly_eq : ∀ p : Polynomial ℝ, p.degree ≤ r → (∀ i : Fin s, p.eval (u i : ℝ) = 0) → p = 0 := by
              intros p hp h_eval_zero
              have h_card_roots : p.roots.toFinset.card ≤ r := by
                exact le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) ( Polynomial.natDegree_le_of_degree_le hp ) );
              exact Classical.not_not.1 fun h => by have := Finset.card_le_card ( show Finset.image ( fun i : Fin s => ( u i : ℝ ) ) Finset.univ ⊆ p.roots.toFinset from Finset.image_subset_iff.2 fun i _ => by aesop ) ; rw [ Finset.card_image_of_injective _ fun i j hij => by simpa [ hu_strict.injective.eq_iff ] using hij ] at this ; norm_num at this ; linarith;
            specialize h_poly_eq ( ∑ j : Fin ( r + 1 ), g j • Polynomial.X ^ ( j : ℕ ) ) ; simp_all +decide [ Polynomial.eval_finset_sum ];
            replace h_poly_eq := congr_arg ( Polynomial.eval x ) ( h_poly_eq <| le_trans ( Polynomial.degree_sum_le _ _ ) <| Finset.sup_le fun i _ => Polynomial.degree_smul_le _ _ |> le_trans <| Polynomial.degree_X_pow_le _ |> le_trans <| WithBot.coe_le_coe.mpr <| Nat.le_of_lt_succ <| Fin.is_lt i ) ; simp_all +decide [ Polynomial.eval_finset_sum ] ;
          exact h_poly;
        -- Since $\sum_{j=0}^{r} g_j x^j = 0$ for all $x$, the polynomial $\sum_{j=0}^{r} g_j x^j$ is the zero polynomial.
        have h_poly_zero : ∑ j : Fin (r + 1), Polynomial.C (g j) * Polynomial.X ^ (j : ℕ) = 0 := by
          exact Polynomial.funext fun x => by simpa [ Polynomial.eval_finset_sum ] using h_poly x;
        replace h_poly_zero := congr_arg ( fun p => p.coeff ( i : ℕ ) ) h_poly_zero ; simp_all +decide [ Polynomial.coeff_X_pow ] ;
        simp_all +decide [ Fin.val_inj ];
      rw [ ← Matrix.rank_transpose, Matrix.rank ];
      rw [ @LinearMap.finrank_range_of_inj ] <;> norm_num [ Function.Injective ];
      intro a₁ a₂ h; simp_all +decide [ funext_iff, Matrix.vecMul, dotProduct ] ;
      rw [ Fintype.linearIndependent_iff ] at h_contra;
      exact fun i => sub_eq_zero.mp ( h_contra ( fun j => a₁ j - a₂ j ) ( by ext x; simpa [ sub_mul ] using sub_eq_zero.mpr ( h x ) ) i );
    have := LinearMap.finrank_range_add_finrank_ker ( Matrix.mulVecLin ( Matrix.of ( fun ( j : Fin ( r + 1 ) ) ( i : Fin s ) => ( w i : ℝ ) * ( u i : ℝ ) ^ ( j : ℕ ) ) ) ) ; simp_all +decide [ Matrix.rank ] ;
    linarith [ show Module.finrank ℝ ( Submodule.span ℝ ( Set.range fun k i => ( v k i : ℝ ) ) ) = r from by rw [ finrank_span_eq_card ] <;> aesop ]
  linarith [Nat.sub_add_cancel (by linarith : 1 ≤ r)]

/-
Binomial coefficient bound: choose(n, j) ≤ n^j / j! for natural numbers.
..(n-j+1)/j! ≤ n^j/j!.
-/
lemma choose_le_pow_div_factorial (n j : ℕ) :
    (Nat.choose n j : ℝ) ≤ (n : ℝ) ^ j / (Nat.factorial j : ℝ) := by
  rw [ le_div_iff₀ ( by positivity ) ];
  rw_mod_cast [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ] ; exact Nat.descFactorial_le_pow n j;

/-
Squared norm bound for the defining vectors b_j = (w_i · choose(u_i, j)).
‖b_j‖² ≤ s · W² · (M^j/j!)².
-/
lemma norm_sq_defining_vector_bound
    (s : ℕ) (M : ℝ) (W : ℝ) (hW : 1 ≤ W)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M)
    (hw_bound : ∀ i, (w i : ℝ) ≤ W)
    (j : ℕ) :
    ∑ i : Fin s, ((w i : ℝ) * (Nat.choose (u i).toNat j : ℝ)) ^ 2 ≤
      (s : ℝ) * W ^ 2 * ((M : ℝ) ^ j / (Nat.factorial j : ℝ)) ^ 2 := by
  -- Each term in the sum is ((w i) * choose(u_i.toNat, j))^2. We have:
  have h_term_bound : ∀ i : Fin s, ((w i : ℝ) * Nat.choose (u i).toNat j) ^ 2 ≤ (W * (M ^ j / (Nat.factorial j))) ^ 2 := by
    -- By the properties of binomial coefficients and the given bounds, we have:
    have h_binom_bound : ∀ i : Fin s, (Nat.choose (u i).toNat j : ℝ) ≤ (M ^ j / (Nat.factorial j)) := by
      intro i
      have h_choose_bound : (Nat.choose (u i).toNat j : ℝ) ≤ (u i).toNat ^ j / (Nat.factorial j : ℝ) := by
        convert choose_le_pow_div_factorial ( Int.toNat ( u i ) ) j using 1
      generalize_proofs at *; (
      exact h_choose_bound.trans ( by gcongr ; linarith [ hu_range i, show ( u i |> Int.toNat : ℝ ) ≤ M from by linarith [ hu_range i, show ( u i |> Int.toNat : ℝ ) = u i from mod_cast Int.toNat_of_nonneg ( hu_range i |>.1 ) ] ] ));
    exact fun i => pow_le_pow_left₀ ( by positivity ) ( mul_le_mul ( hw_bound i ) ( h_binom_bound i ) ( by positivity ) ( by positivity ) ) _;
  convert Finset.sum_le_sum fun i _ => h_term_bound i using 1 ; norm_num ; ring

/-
The integer kernel of the moment system has rank r.
-/
lemma integer_kernel_has_r_independent_vectors
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i) :
    ∃ v : Fin r → (Fin s → ℤ),
      (∀ (k : Fin r) (j : ℕ), j < r →
        ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((v k i : ℤ) : ℝ))) := by
  -- Define the r × r integer matrix B₀ with B₀(j,k) = w(⟨r+k, ...⟩) * u(⟨r+k, ...⟩)^j for j,k : Fin r.
  set B₀ : Matrix (Fin r) (Fin r) ℤ := fun j k => w ⟨r + k.val, by omega⟩ * (u ⟨r + k.val, by omega⟩ : ℤ) ^ j.val;
  -- Define the vectors v(j₀) as described in the provided solution.
  obtain ⟨v, hv⟩ : ∃ v : Fin r → Fin s → ℤ, (∀ j₀ : Fin r, ∀ j : ℕ, j < r → ∑ i, (v j₀ i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧ (∀ j₀ j₁ : Fin r, j₀ ≠ j₁ → v j₀ ⟨j₁.val, by omega⟩ = 0) ∧ (∀ j₀ : Fin r, v j₀ ⟨j₀.val, by omega⟩ = B₀.det) := by
    refine' ⟨ fun j₀ i => if h : i.val < r then if h' : i.val = j₀.val then B₀.det else 0 else -Matrix.det ( Matrix.updateCol B₀ ( ⟨ i.val - r, by omega ⟩ : Fin r ) ( fun j => w ⟨ j₀.val, by omega ⟩ * ( u ⟨ j₀.val, by omega ⟩ : ℤ ) ^ j.val ) ), _, _, _ ⟩ <;> simp +decide ;
    · intro j₀ j hj;
      -- Split the sum into two parts: one over the first r elements and one over the last r elements.
      have h_split_sum : ∑ x : Fin s, (if h : x.val < r then if h' : x.val = j₀.val then B₀.det else 0 else -Matrix.det (Matrix.updateCol B₀ (⟨x.val - r, by omega⟩ : Fin r) (fun j => w ⟨j₀.val, by omega⟩ * (u ⟨j₀.val, by omega⟩ : ℤ) ^ j.val))) * (w x : ℝ) * ((u x : ℝ)) ^ j = ∑ x : Fin r, (B₀.det : ℝ) * (w ⟨x.val, by omega⟩ : ℝ) * ((u ⟨x.val, by omega⟩ : ℝ)) ^ j * (if x.val = j₀.val then 1 else 0) + ∑ x : Fin r, (-Matrix.det (Matrix.updateCol B₀ x (fun j => w ⟨j₀.val, by omega⟩ * (u ⟨j₀.val, by omega⟩ : ℤ) ^ j.val))) * (w ⟨r + x.val, by omega⟩ : ℝ) * ((u ⟨r + x.val, by omega⟩ : ℝ)) ^ j := by
        rw [ show ( Finset.univ : Finset ( Fin s ) ) = Finset.image ( fun x : Fin r => ⟨ x.val, by omega ⟩ ) Finset.univ ∪ Finset.image ( fun x : Fin r => ⟨ r + x.val, by omega ⟩ ) Finset.univ from ?_, Finset.sum_union ];
        · rw [ Finset.sum_image, Finset.sum_image ] <;> simp +decide ;
          · exact fun x y h => by simpa [ Fin.ext_iff ] using h;
          · exact fun x y h => Fin.ext <| by simpa using congr_arg Fin.val h;
        · norm_num [ Finset.disjoint_left ];
          exact fun a x => by linarith [ Fin.is_lt a, Fin.is_lt x ] ;
        · ext ⟨ x, hx ⟩ ; simp +decide [ Fin.ext_iff ];
          exact if h : x < r then Or.inl ⟨ ⟨ x, by linarith ⟩, rfl ⟩ else Or.inr ⟨ ⟨ x - r, by omega ⟩, by rw [ add_tsub_cancel_of_le ( by linarith ) ] ⟩;
      -- By definition of $B₀$, we know that $\sum_{x : Fin r} \det(B₀.updateCol x (fun j => w ⟨j₀.val, by omega⟩ * (u ⟨j₀.val, by omega⟩ : ℤ) ^ j.val)) * (w ⟨r + x.val, by omega⟩ : ℝ) * ((u ⟨r + x.val, by omega⟩ : ℝ)) ^ j = \det(B₀) * (w ⟨j₀.val, by omega⟩ : ℝ) * ((u ⟨j₀.val, by omega⟩ : ℝ)) ^ j$.
      have h_det_sum : ∑ x : Fin r, Matrix.det (Matrix.updateCol B₀ x (fun j => w ⟨j₀.val, by omega⟩ * (u ⟨j₀.val, by omega⟩ : ℤ) ^ j.val)) * (w ⟨r + x.val, by omega⟩ : ℝ) * ((u ⟨r + x.val, by omega⟩ : ℝ)) ^ j = Matrix.det B₀ * (w ⟨j₀.val, by omega⟩ : ℝ) * ((u ⟨j₀.val, by omega⟩ : ℝ)) ^ j := by
        have h_det_sum : Matrix.mulVec B₀ (fun x : Fin r => Matrix.det (Matrix.updateCol B₀ x (fun j => w ⟨j₀.val, by omega⟩ * (u ⟨j₀.val, by omega⟩ : ℤ) ^ j.val))) = Matrix.det B₀ • (fun j => w ⟨j₀.val, by omega⟩ * (u ⟨j₀.val, by omega⟩ : ℤ) ^ j.val) := by
          convert Matrix.mulVec_cramer B₀ _ using 1;
        convert congr_arg ( fun x : Fin r → ℤ => ( x ⟨ j, by linarith ⟩ : ℝ ) ) h_det_sum using 1 <;> norm_num [ Matrix.mulVec, dotProduct ] ; ring_nf;
        · exact Finset.sum_congr rfl fun _ _ => by push_cast [ B₀ ] ; ring;
        · ring;
      simp_all +decide [ Fin.val_inj ];
    · exact fun j₀ j₁ hij h => False.elim <| hij <| Fin.ext h.symm;
  have h_det_B₀ : B₀.det ≠ 0 := by
    -- The determinant of B₀ is non-zero because it is a Vandermonde determinant with distinct nodes.
    have h_det_B₀ : Matrix.det B₀ = Matrix.det (Matrix.of (fun j k : Fin r => (u ⟨r + k.val, by omega⟩ : ℤ) ^ j.val)) * ∏ k : Fin r, (w ⟨r + k.val, by omega⟩ : ℤ) := by
      erw [ Matrix.det_mul_row ];
      ring!;
    rw [ h_det_B₀ ];
    erw [ Matrix.det_transpose, Matrix.det_vandermonde ];
    exact mul_ne_zero ( Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero_of_ne <| hu_strict.injective.ne <| by simpa [ Fin.ext_iff ] using ne_of_gt <| Finset.mem_Ioi.mp hj ) <| Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| ne_of_gt <| hw_pos _;
  refine' ⟨ v, hv.1, Fintype.linearIndependent_iff.2 _ ⟩;
  intro g hg i; replace hg := congr_fun hg ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ; simp_all +decide [ Finset.sum_eq_single i ] ;

/-
Finite integer vectors with bounded norm: the set of integer vectors a ∈ ℤ^s
with ∑ a_i² ≤ C is finite. Used to show minimum-norm integer vectors exist.
-/
lemma finite_integer_vectors_bounded_norm (s : ℕ) (C : ℝ) :
    Set.Finite {a : Fin s → ℤ | ∑ i : Fin s, ((a i : ℤ) : ℝ) ^ 2 ≤ C} := by
  -- For each $i$, the set of integers $a_i$ with $|a_i| \leq \sqrt{C}$ is finite.
  have h_finite_components : ∀ (i : Fin s), Set.Finite {a : ℤ | (a : ℝ) ^ 2 ≤ C} := by
    exact fun i => Set.Finite.subset ( Set.finite_Icc ( -⌈C⌉₊ : ℤ ) ⌈C⌉₊ ) fun x hx => ⟨ by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ hx.out, Nat.le_ceil C ] ), by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ hx.out, Nat.le_ceil C ] ) ⟩ ;
  exact Set.Finite.subset ( Set.Finite.pi fun i => h_finite_components i ) fun x hx => by simpa using fun i => hx.trans' ( Finset.single_le_sum ( fun a _ => sq_nonneg ( x a : ℝ ) ) ( Finset.mem_univ i ) ) ;

/-- Integer squared norm (as a natural number, since entries are integers) -/
def int_sq_norm (s : ℕ) (x : Fin s → ℤ) : ℕ := ∑ i : Fin s, (x i).natAbs ^ 2

lemma int_sq_norm_eq_real_sq_norm (s : ℕ) (x : Fin s → ℤ) :
    (int_sq_norm s x : ℝ) = ∑ i : Fin s, ((x i : ℤ) : ℝ) ^ 2 := by
  unfold int_sq_norm;
  norm_num [ ← @Int.cast_inj ℝ ]

/-
Among kernel vectors not in a given subspace, there exists one with minimum
squared norm.
-/
lemma min_norm_kernel_vector_exists
    (r s : ℕ) (hr : 2 ≤ r) (hs : s = 2 * r)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_strict : StrictMono u) (hw_pos : ∀ i, 0 < w i)
    (V : Submodule ℝ (Fin s → ℝ)) (hV_dim : Module.finrank ℝ V < r) :
    ∃ x : Fin s → ℤ,
      (∀ j : ℕ, j < r → ∑ i, (x i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      (fun i : Fin s => (x i : ℝ)) ∉ V ∧
      (∀ y : Fin s → ℤ,
        (∀ j : ℕ, j < r → ∑ i, (y i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) →
        (fun i : Fin s => (y i : ℝ)) ∉ V →
        int_sq_norm s x ≤ int_sq_norm s y) := by
  obtain ⟨x, hx_kernel, hx_not_in_V⟩ : ∃ x : Fin s → ℤ, (∀ j < r, ∑ i, (x i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧ (fun i => (x i : ℝ)) ∉ V := by
    obtain ⟨ v, hv ⟩ := integer_kernel_has_r_independent_vectors r hr s hs u w hu_strict hw_pos;
    contrapose! hV_dim;
    have hV_dim : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun k : Fin r => (fun i => ((v k i : ℤ) : ℝ))))) ≤ Module.finrank ℝ V := by
      exact Submodule.finrank_mono <| Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun k => hV_dim _ <| hv.1 k;
    rw [ finrank_span_eq_card ] at hV_dim <;> aesop;
  have h_finite : Set.Finite {y : Fin s → ℤ | (∀ j < r, ∑ i, (y i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧ (fun i => (y i : ℝ)) ∉ V ∧ int_sq_norm s y ≤ int_sq_norm s x} := by
    have h_finite : Set.Finite {y : Fin s → ℤ | int_sq_norm s y ≤ int_sq_norm s x} := by
      convert finite_integer_vectors_bounded_norm s ( int_sq_norm s x ) using 1;
      norm_num [ ← int_sq_norm_eq_real_sq_norm ];
    exact h_finite.subset fun y hy => hy.2.2;
  obtain ⟨y, hy⟩ : ∃ y ∈ {y : Fin s → ℤ | (∀ j < r, ∑ i, (y i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧ (fun i => (y i : ℝ)) ∉ V ∧ int_sq_norm s y ≤ int_sq_norm s x}, ∀ z ∈ {y : Fin s → ℤ | (∀ j < r, ∑ i, (y i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧ (fun i => (y i : ℝ)) ∉ V ∧ int_sq_norm s y ≤ int_sq_norm s x}, int_sq_norm s y ≤ int_sq_norm s z := by
    apply_rules [ Set.exists_min_image ];
    exact ⟨ x, hx_kernel, hx_not_in_V, le_rfl ⟩;
  exact ⟨ y, hy.1.1, hy.1.2.1, fun z hz₁ hz₂ => if hz₃ : int_sq_norm s z ≤ int_sq_norm s x then hy.2 z ⟨ hz₁, hz₂, hz₃ ⟩ else by linarith [ hy.1.2.2 ] ⟩

/-
The span of image of a Fin-indexed family restricted to {j | j.val < k} has
finrank at most k.
-/
lemma finrank_span_image_lt (s r : ℕ) (k : Fin r)
    (f : Fin r → (Fin s → ℝ)) :
    Module.finrank ℝ (Submodule.span ℝ (f '' {j | j.val < k.val})) ≤ k.val := by
  refine' le_trans ( finrank_span_le_card _ ) _ ; norm_num;
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact Finset.image f ( Finset.Iio k );
  · grind;
  · exact Finset.card_image_le.trans ( by simp )

lemma successive_minima_in_kernel
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_strict : StrictMono u) (hw_pos : ∀ i, 0 < w i) :
    ∃ v : Fin r → (Fin s → ℤ),
      (∀ (k : Fin r) (j : ℕ), j < r →
        ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      (LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((v k i : ℤ) : ℝ)))) ∧
      (Monotone (fun k : Fin r => ∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2)) ∧
      (∀ k : Fin r, ∀ x : Fin s → ℤ,
        (∀ j : ℕ, j < r → ∑ i, (x i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) →
        (fun i : Fin s => (x i : ℝ)) ∉
          Submodule.span ℝ ((fun j : Fin r => fun i : Fin s => (v j i : ℝ)) ''
            { j | j.val < k.val }) →
        ∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2 ≤ ∑ i : Fin s, ((x i : ℤ) : ℝ) ^ 2) := by
  have := @integer_kernel_has_r_independent_vectors r hr s hs u w hu_strict hw_pos;
  -- By induction on $k$, we can construct the desired basis.
  have h_ind : ∀ k : Fin (r + 1), ∃ v : Fin k → (Fin s → ℤ), (∀ j : Fin k, ∀ l < r, ∑ i, (v j i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ l = 0) ∧ LinearIndependent ℝ (fun j : Fin k => (fun i : Fin s => ((v j i : ℤ) : ℝ))) ∧ Monotone (fun j : Fin k => ∑ i, ((v j i : ℤ) : ℝ) ^ 2) ∧ ∀ j : Fin k, ∀ x : Fin s → ℤ, (∀ l < r, ∑ i, (x i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ l = 0) → (fun i : Fin s => (x i : ℝ)) ∉ Submodule.span ℝ (Set.image (fun l : Fin k => (fun i : Fin s => ((v l i : ℤ) : ℝ))) {l | l.val < j.val}) → ∑ i, ((v j i : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((x i : ℤ) : ℝ) ^ 2 := by
    intro k;
    induction' k using Fin.induction with k ih;
    · simp +decide [ Monotone ];
    · obtain ⟨ v, hv₁, hv₂, hv₃, hv₄ ⟩ := ih;
      obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := min_norm_kernel_vector_exists r s hr hs u w hu_strict hw_pos ( Submodule.span ℝ ( Set.range ( fun j : Fin k.castSucc => fun i : Fin s => ( v j i : ℝ ) ) ) ) ( by
        rw [ finrank_span_eq_card ] <;> norm_num [ hv₂ ] );
      refine' ⟨ Fin.snoc v x, _, _, _, _ ⟩;
      · intro j l hl; refine' Fin.lastCases _ _ j <;> simp +decide [ * ] ;
      · rw [ Fintype.linearIndependent_iff ] at *;
        intro g hg;
        simp +decide [ Fin.sum_univ_castSucc, funext_iff ] at hg ⊢;
        -- By definition of $g$, we know that $g (Fin.last k) = 0$.
        have hg_last : g (Fin.last k) = 0 := by
          contrapose! hx₂;
          rw [ Submodule.mem_span ];
          intro p hp;
          convert p.smul_mem ( - ( g ( Fin.last k ) ) ⁻¹ ) ( p.add_mem ( p.sum_mem fun i _ => p.smul_mem ( g ( Fin.castSucc i ) ) ( hp <| Set.mem_range_self i ) ) ( p.zero_mem ) ) using 1 ; ext i ; simp +decide ;
          rw [ inv_mul_eq_div, neg_div', eq_div_iff hx₂ ] ; linarith [ hg i ];
        intro i; induction i using Fin.lastCases <;> simp +decide [ * ] at *;
        exact hv₂ _ ( by ext; simpa [ Finset.sum_apply, mul_comm ] using hg _ ) _;
      · intro i j hij;
        by_cases hi : i.val < k.val <;> by_cases hj : j.val < k.val <;> simp +decide [ *, Fin.snoc ] at hij ⊢;
        · exact hv₃ ( by simpa [ Fin.ext_iff ] using hij );
        · convert hv₄ ( Fin.castLT i hi ) x hx₁ _ using 1;
          refine' fun h => hx₂ _;
          exact Submodule.span_mono ( Set.image_subset_range _ _ ) h;
        · grind;
      · intro j y hy₁ hy₂;
        by_cases hj : j.val < k.val;
        · convert hv₄ ⟨ j, hj ⟩ y hy₁ _ using 1;
          · simp +decide [ Fin.snoc, hj ];
            congr!;
          · contrapose! hy₂;
            refine' Submodule.span_le.mpr _ hy₂;
            rintro _ ⟨ l, hl, rfl ⟩;
            exact Submodule.subset_span ⟨ ⟨ l, by
              exact lt_of_lt_of_le l.2 ( Nat.le_succ _ ) ⟩, by
              exact hl, by
              simp +decide [ Fin.snoc ] ⟩;
        · convert hx₃ y hy₁ _ using 1;
          · simp +decide [ Fin.eq_last_of_not_lt hj, int_sq_norm ];
            norm_cast;
            norm_num [ ← Int.ofNat_le, Int.natAbs_pow ];
          · contrapose! hy₂;
            refine' Submodule.span_le.mpr _ hy₂;
            rintro _ ⟨ j, rfl ⟩;
            refine' Submodule.subset_span ⟨ Fin.castSucc j, _, _ ⟩ <;> simp +decide [ Fin.snoc ];
            exact lt_of_lt_of_le ( Fin.castSucc_lt_last j ) ( Nat.le_of_not_lt hj );
  exact h_ind ⟨ r, Nat.lt_succ_self r ⟩

/-
Successive minima product is bounded by any independent kernel basis product.
If v has the successive minima property and y is any linearly independent kernel family,
then ∏ N(v_k) ≤ ∏ N(y_k).
-/
lemma succ_min_product_le_basis_product
    (r s : ℕ)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (v : Fin r → (Fin s → ℤ))
    (hv_succ : ∀ k : Fin r, ∀ x : Fin s → ℤ,
      (∀ j : ℕ, j < r → ∑ i, (x i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) →
      (fun i : Fin s => (x i : ℝ)) ∉
        Submodule.span ℝ ((fun j : Fin r => fun i : Fin s => (v j i : ℝ)) ''
          { j | j.val < k.val }) →
      ∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2 ≤ ∑ i : Fin s, ((x i : ℤ) : ℝ) ^ 2)
    (y : Fin r → (Fin s → ℤ))
    (hy_kernel : ∀ (k : Fin r) (j : ℕ), j < r →
      ∑ i, (y k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0)
    (hy_indep : LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((y k i : ℤ) : ℝ))))
    (hy_sorted : Monotone (fun k : Fin r => ∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2)) :
    ∏ k : Fin r, (∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2) ≤
      ∏ k : Fin r, (∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) := by
  apply Finset.prod_le_prod;
  · exact fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _;
  · intro k hk
    obtain ⟨j, hj⟩ : ∃ j ≤ k, (fun i => (y j i : ℝ)) ∉ Submodule.span ℝ (Set.image (fun l : Fin r => (fun i => ((v l i : ℝ))) ) {l | l.val < k.val}) := by
      by_contra h_contra;
      have h_subspace : Module.finrank ℝ (Submodule.span ℝ (Set.image (fun l : Fin r => (fun i => ((y l i : ℝ))) ) (Finset.Iic k))) ≤ k.val := by
        have h_subspace : Submodule.span ℝ (Set.image (fun l : Fin r => (fun i => ((y l i : ℝ))) ) (Finset.Iic k)) ≤ Submodule.span ℝ (Set.image (fun l : Fin r => (fun i => ((v l i : ℝ))) ) {l | l.val < k.val}) := by
          exact Submodule.span_le.mpr ( Set.image_subset_iff.mpr fun l hl => by aesop );
        refine' le_trans ( Submodule.finrank_mono h_subspace ) _;
        convert finrank_span_image_lt s r k ( fun l i => ( v l i : ℝ ) ) using 1;
      rw [ Set.image_eq_range ] at h_subspace;
      rw [ finrank_span_eq_card ] at h_subspace <;> norm_num at *;
      convert hy_indep.comp _ _;
      exact Subtype.coe_injective;
    exact le_trans ( hv_succ k ( y j ) ( hy_kernel j ) hj.2 ) ( hy_sorted hj.1 )

/-
There exist r linearly independent integer kernel vectors (sorted by norm) with
product ≤ the RHS.
-/
set_option maxHeartbeats 1600000 in
lemma annihilator_short_vectors
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_nonneg : ∀ i, 0 ≤ u i)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i) :
    ∃ y : Fin r → (Fin s → ℤ),
      (∀ (k : Fin r) (j : ℕ), j < r →
        ∑ i, (y k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      (LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((y k i : ℤ) : ℝ)))) ∧
      (Monotone (fun k : Fin r => ∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2)) ∧
      ∏ k : Fin r, (∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (r * (r - 1)) *
        ∏ j ∈ Finset.range r,
          (∑ i : Fin s, ((w i : ℝ) * (Nat.choose (u i).toNat j : ℝ)) ^ 2) := by
  obtain ⟨y, hy⟩ := orthogonal_lattice_short_vectors r (by linarith) s (by
  omega) (fun j => fun i => ((w i : ℤ) * (Nat.choose (u i).toNat j : ℤ))) (by
  refine' Fintype.linearIndependent_iff.2 _;
  intro g hg i
  have h_poly : ∀ i_1 : Fin s, ∑ j : Fin r, g j * (Nat.choose (u i_1).toNat j : ℝ) = 0 := by
    intro i_1; replace hg := congr_fun hg i_1; simp_all +decide [ mul_comm] ;
    convert congr_arg ( fun x : ℝ => x / ( w i_1 : ℝ ) ) hg using 1 <;> norm_num [ Finset.sum_div _ _ _, mul_div_assoc, ne_of_gt ( hw_pos i_1 ) ];
  -- Since $u$ is strictly monotone, the values $u_i$ are distinct, and thus the polynomial $\sum_{j=0}^{r-1} g_j \binom{x}{j}$ has $r$ distinct roots.
  have h_poly_roots : ∀ x : ℕ, x ∈ Finset.image (fun i => (u i).toNat) Finset.univ → ∑ j : Fin r, g j * (Nat.choose x j : ℝ) = 0 := by
    aesop;
  -- Since the polynomial $\sum_{j=0}^{r-1} g_j \binom{x}{j}$ has $r$ distinct roots, it must be the zero polynomial.
  have h_poly_zero : ∀ x : ℕ, ∑ j : Fin r, g j * (Nat.choose x j : ℝ) = 0 := by
    intro x
    by_contra h_nonzero_poly
    have h_poly_roots_card : Finset.card (Finset.image (fun i => (u i).toNat) Finset.univ) ≥ r := by
      rw [ Finset.card_image_of_injective _ fun i j hij => _ ] <;> norm_num [ Fin.ext_iff, hu_strict.injective.eq_iff ] at * ; linarith;
      exact fun i j hij => by simpa [ Fin.ext_iff ] using hu_strict.injective ( by linarith [ Int.toNat_of_nonneg ( hu_nonneg i ), Int.toNat_of_nonneg ( hu_nonneg j ) ] : u i = u j ) ;
    have h_poly_roots_card : Finset.card (Finset.filter (fun x => ∑ j : Fin r, g j * (Nat.choose x j : ℝ) = 0) (Finset.range (Finset.sup (Finset.image (fun i => (u i).toNat) Finset.univ) id + 1))) ≥ r := by
      refine' le_trans h_poly_roots_card ( Finset.card_le_card _ );
      exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Finset.le_sup ( f := id ) hx ) ), h_poly_roots x hx ⟩
    have h_poly_roots_card : Finset.card (Finset.filter (fun x => ∑ j : Fin r, g j * (Nat.choose x j : ℝ) = 0) (Finset.range (Finset.sup (Finset.image (fun i => (u i).toNat) Finset.univ) id + 1))) < r := by
      have h_poly_roots_card : ∃ p : Polynomial ℝ, p.degree < r ∧ ∀ x : ℕ, ∑ j : Fin r, g j * (Nat.choose x j : ℝ) = p.eval (x : ℝ) := by
        use ∑ j : Fin r, Polynomial.C (g j) * (Polynomial.C (1 / (Nat.factorial j : ℝ)) * ∏ k ∈ Finset.range j, (Polynomial.X - Polynomial.C (k : ℝ)));
        refine' ⟨ lt_of_le_of_lt ( Polynomial.degree_sum_le _ _ ) _, _ ⟩;
        · erw [ Finset.sup_lt_iff ] ; norm_num [ Polynomial.degree_prod ];
          · intro j; by_cases hj : g j = 0 <;> simp +decide [ hj, Polynomial.degree_C ] ;
            exact lt_of_le_of_lt ( add_le_add ( Polynomial.degree_C_le ) ( Finset.sum_le_sum fun _ _ => Polynomial.degree_X_sub_C_le _ ) ) ( by norm_cast; simp );
          · exact WithBot.bot_lt_coe r;
        · intro x; simp +decide [ Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C ] ;
          refine' Finset.sum_congr rfl fun j hj => _;
          by_cases hx : x < j.val <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ];
          · exact Or.inr <| Or.inr <| Finset.prod_eq_zero ( Finset.mem_range.mpr hx ) <| sub_self _;
          · field_simp;
            rw_mod_cast [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
            rw [ Nat.descFactorial_eq_prod_range ] ; norm_num [ Int.subNatNat_eq_coe ];
            exact Or.inl ( Finset.prod_congr rfl fun i hi => by rw [ Nat.cast_sub ( by linarith [ Finset.mem_range.mp hi ] ) ] );
      obtain ⟨ p, hp_deg, hp_eval ⟩ := h_poly_roots_card; simp_all +decide [ Polynomial.eval_eq_sum_range ] ;
      have h_poly_roots_card : Finset.card (Finset.filter (fun x : ℕ => p.eval (x : ℝ) = 0) (Finset.range (Finset.sup (Finset.image (fun i => (u i).toNat) Finset.univ) id + 1))) ≤ p.natDegree := by
        have h_poly_roots_card : Finset.card (Finset.image (fun x : ℕ => (x : ℝ)) (Finset.filter (fun x : ℕ => p.eval (x : ℝ) = 0) (Finset.range (Finset.sup (Finset.image (fun i => (u i).toNat) Finset.univ) id + 1)))) ≤ p.natDegree := by
          exact le_trans ( Finset.card_le_card <| show _ ⊆ p.roots.toFinset from by aesop_cat ) <| by exact le_trans ( Multiset.toFinset_card_le _ ) <| Polynomial.card_roots' _;
        rwa [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ] at h_poly_roots_card;
      simp_all +decide [ Polynomial.eval_eq_sum_range ];
      exact lt_of_le_of_lt h_poly_roots_card ( Nat.lt_of_not_ge fun h => hp_deg.not_ge <| by rw [ Polynomial.degree_eq_natDegree <| by aesop_cat ] ; exact_mod_cast h )
    exact absurd h_poly_roots_card (by linarith);
  induction' i with i ih;
  induction' i using Nat.strong_induction_on with i ih;
  have := h_poly_zero i;
  rw [ Finset.sum_eq_single ⟨ i, ih ⟩ ] at this <;> simp_all +decide ;
  intro j hj; cases lt_or_gt_of_ne ( show j.val ≠ i from by simpa [ Fin.ext_iff ] using hj ) <;> [ exact Or.inl ( ih _ ‹_› <| by linarith [ Fin.is_lt j ] ) ; exact Or.inr <| Nat.choose_eq_zero_of_lt ‹_› ] ;);
  refine' ⟨ y, _, hy.2.1, hy.2.2.1, _ ⟩ <;> simp_all +decide [ Finset.prod_range ];
  -- By definition of $u$, we know that $u_i^j$ can be written as an integer linear combination of $C(u_i, 0), ..., C(u_i, j)$.
  have h_poly : ∀ j : ℕ, j < r → ∃ c : Fin (j + 1) → ℤ, ∀ i : Fin s, (u i : ℝ) ^ j = ∑ l : Fin (j + 1), (c l : ℝ) * (Nat.choose (u i).toNat l : ℝ) := by
    intro j hj;
    -- By definition of binomial coefficients, we know that $u_i^j$ can be written as a linear combination of $\binom{u_i}{l}$ for $l \leq j$.
    have h_poly : ∀ j : ℕ, ∃ c : Fin (j + 1) → ℤ, ∀ x : ℕ, x ^ j = ∑ l : Fin (j + 1), (c l : ℤ) * Nat.choose x l := by
      intro j;
      induction' j with j ih;
      · exact ⟨ fun l => if l = 0 then 1 else 0, fun x => by simp +decide ⟩;
      · obtain ⟨ c, hc ⟩ := ih;
        -- We'll use the fact that $x^{j+1} = x \cdot x^j$ and the induction hypothesis to express $x^{j+1}$ in terms of binomial coefficients.
        have h_expand : ∀ x : ℕ, (x : ℤ) ^ (j + 1) = ∑ l : Fin (j + 1), (c l : ℤ) * (x * Nat.choose x l : ℤ) := by
          simp +decide [ pow_succ', mul_left_comm, Finset.mul_sum _ _ _, hc ];
        -- We'll use the fact that $x \cdot \binom{x}{l} = (l+1) \cdot \binom{x}{l+1} + l \cdot \binom{x}{l}$.
        have h_identity : ∀ x : ℕ, ∀ l : Fin (j + 1), (x * Nat.choose x l : ℤ) = (l.val + 1) * Nat.choose x (l.val + 1) + l.val * Nat.choose x l := by
          intro x l; norm_cast;
          nlinarith [ Nat.add_one_mul_choose_eq x l, Nat.choose_succ_succ x l ];
        use fun l => ∑ k : Fin (j + 1), c k * (if l.val = k.val + 1 then (k.val + 1 : ℤ) else if l.val = k.val then (k.val : ℤ) else 0);
        intro x; rw [ h_expand x ] ; simp +decide [ h_identity, Finset.sum_mul _ _ _ ] ;
        rw [ Finset.sum_comm ];
        refine' Finset.sum_congr rfl fun i hi => _;
        rw [ Finset.sum_eq_add ( ⟨ i + 1, by linarith [ Fin.is_lt i ] ⟩ : Fin ( j + 2 ) ) ( ⟨ i, by linarith [ Fin.is_lt i ] ⟩ : Fin ( j + 2 ) ) ] <;> norm_num ; ring;
        simp +contextual [ Fin.ext_iff ];
    obtain ⟨ c, hc ⟩ := h_poly j; use c; intro i; specialize hc ( Int.toNat ( u i ) ) ; simp_all +decide [ Int.toNat_of_nonneg ( hu_nonneg i ) ] ;
    exact_mod_cast hc;
  intro k j hj; obtain ⟨ c, hc ⟩ := h_poly j hj; simp +decide [ hc, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] ;
  rw [ Finset.sum_comm ];
  refine' Finset.sum_eq_zero fun l hl => _;
  convert congr_arg ( fun x : ℝ => x * c l ) ( hy.1 k ⟨ l, by linarith [ Fin.is_lt l ] ⟩ ) using 1 <;> ring_nf;
  simp +decide only [mul_assoc, Finset.mul_sum _ _ _, mul_left_comm]

lemma kernel_basis_product_bound
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (M : ℝ)
    (W : ℝ) (hW : 1 ≤ W)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i)
    (hw_bound : ∀ i, (w i : ℝ) ≤ W) :
    ∃ y : Fin r → (Fin s → ℤ),
      (∀ (k : Fin r) (j : ℕ), j < r →
        ∑ i, (y k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      (LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((y k i : ℤ) : ℝ)))) ∧
      (Monotone (fun k : Fin r => ∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2)) ∧
      ∏ k : Fin r, (∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (r * (r - 1)) * (2 * (r : ℝ)) ^ r * W ^ (2 * r) *
        (∏ j ∈ Finset.range r, ((M : ℝ) ^ j / (Nat.factorial j : ℝ))) ^ 2 := by
  obtain ⟨y, hy_kernel, hy_indep, hy_mono, hy_prod⟩ :=
    annihilator_short_vectors r hr s hs u w (fun i => (hu_range i).1) hu_strict hw_pos
  refine ⟨y, hy_kernel, hy_indep, hy_mono, ?_⟩
  calc ∏ k : Fin r, (∑ i : Fin s, ((y k i : ℤ) : ℝ) ^ 2)
      ≤ (2 : ℝ) ^ (r * (r - 1)) *
        ∏ j ∈ Finset.range r,
          (∑ i : Fin s, ((w i : ℝ) * (Nat.choose (u i).toNat j : ℝ)) ^ 2) := hy_prod
    _ ≤ (2 : ℝ) ^ (r * (r - 1)) *
        ∏ j ∈ Finset.range r,
          ((s : ℝ) * W ^ 2 * ((M : ℝ) ^ j / (Nat.factorial j : ℝ)) ^ 2) := by
        gcongr with j hj
        exact norm_sq_defining_vector_bound s M W hW u w hu_range hw_bound j
    _ = (2 : ℝ) ^ (r * (r - 1)) * (2 * (r : ℝ)) ^ r * W ^ (2 * r) *
        (∏ j ∈ Finset.range r, ((M : ℝ) ^ j / (Nat.factorial j : ℝ))) ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_range, Finset.prod_pow]
        rw [hs]; push_cast; ring

/-
For successive minima vectors of the kernel lattice,
∏ N(v_k) ≤ 2^{r(r-1)} (2r)^r W^{2r} (∏ M^j/j!)^2.
-/
lemma successive_minima_product_bound
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (M : ℝ)
    (W : ℝ) (hW : 1 ≤ W)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i)
    (hw_bound : ∀ i, (w i : ℝ) ≤ W)
    (v : Fin r → (Fin s → ℤ))
    (hv_succ : ∀ k : Fin r, ∀ x : Fin s → ℤ,
      (∀ j : ℕ, j < r → ∑ i, (x i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) →
      (fun i : Fin s => (x i : ℝ)) ∉
        Submodule.span ℝ ((fun j : Fin r => fun i : Fin s => (v j i : ℝ)) ''
          { j | j.val < k.val }) →
      ∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2 ≤ ∑ i : Fin s, ((x i : ℤ) : ℝ) ^ 2) :
    ∏ k : Fin r, (∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2) ≤
      (2 : ℝ) ^ (r * (r - 1)) * (2 * (r : ℝ)) ^ r * W ^ (2 * r) *
      (∏ j ∈ Finset.range r, ((M : ℝ) ^ j / (Nat.factorial j : ℝ))) ^ 2 := by
  obtain ⟨y, hy_kernel, hy_indep, hy_sorted, hy_prod⟩ := kernel_basis_product_bound r hr s hs M W hW u w hu_range hu_strict hw_pos hw_bound;
  refine le_trans ?_ hy_prod;
  convert succ_min_product_le_basis_product r s u w v hv_succ y hy_kernel hy_indep hy_sorted using 1

/-
Successive kernel vectors with product bound.
-/
lemma successive_kernel_vectors_exist
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (M : ℝ)
    (W : ℝ) (hW : 1 ≤ W)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i)
    (hw_bound : ∀ i, (w i : ℝ) ≤ W) :
    ∃ v : Fin r → (Fin s → ℤ),
      (∀ (k : Fin r) (j : ℕ), j < r →
        ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      (LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((v k i : ℤ) : ℝ)))) ∧
      (Monotone (fun k : Fin r => ∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2)) ∧
      (∏ k : Fin r, (∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (r * (r - 1)) * (2 * (r : ℝ)) ^ r * W ^ (2 * r) *
        (∏ j ∈ Finset.range r, ((M : ℝ) ^ j / (Nat.factorial j : ℝ))) ^ 2) ∧
      -- Successive minima property: v_k minimizes squared norm among kernel
      -- vectors not in the span of v_0,...,v_{k-1}
      (∀ k : Fin r, ∀ x : Fin s → ℤ,
        (∀ j : ℕ, j < r → ∑ i, (x i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) →
        (fun i : Fin s => (x i : ℝ)) ∉
          Submodule.span ℝ ((fun j : Fin r => fun i : Fin s => (v j i : ℝ)) ''
            { j | j.val < k.val }) →
        ∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2 ≤ ∑ i : Fin s, ((x i : ℤ) : ℝ) ^ 2) := by
  obtain ⟨ v, hv₁, hv₂, hv₃, hv₄ ⟩ := successive_minima_in_kernel r hr s hs u w hu_strict hw_pos;
  refine' ⟨ v, hv₁, hv₂, hv₃, _, hv₄ ⟩;
  convert successive_minima_product_bound r hr s hs M W hW u w hu_range hu_strict hw_pos hw_bound v hv₄ using 1

/-
If v has all moments L_0,...,L_{n+ℓ-1} vanishing, then b_i = choose(u_i, ℓ) * v_i
has all moments L_0,...,L_{n-1} vanishing.
-/
lemma kernel_binomial_multiply
    (s : ℕ) (u : Fin s → ℤ) (w : Fin s → ℕ) (v : Fin s → ℤ)
    (hu_nonneg : ∀ i, 0 ≤ u i) (ℓ : ℕ) :
    ∀ n : ℕ, (∀ t : ℕ, t < n + ℓ → ∑ i, (v i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ t = 0) →
    ∀ j : ℕ, j < n →
      ∑ i, ((Nat.choose (u i).toNat ℓ : ℤ) * v i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0 := by
  intro n hn j hj
  induction' ℓ with ℓ ih generalizing n j;
  · aesop;
  · -- Use the identity: (ℓ+1) * choose(n, ℓ+1) = choose(n, ℓ) * (n - ℓ) for natural numbers.
    have h_identity : ∀ i, ((u i).toNat.choose (ℓ + 1) : ℝ) * (ℓ + 1) = ((u i).toNat.choose ℓ : ℝ) * ((u i : ℝ) - ℓ) := by
      intro i; norm_cast; have := Nat.choose_succ_right_eq ( Int.toNat ( u i ) ) ℓ; simp_all +decide [add_comm] ;
      by_cases h : ℓ ≤ Int.toNat ( u i ) <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ];
    -- Apply the identity to rewrite the sum.
    have h_sum_rewrite : ∑ i, ((u i).toNat.choose (ℓ + 1) : ℝ) * (v i : ℝ) * (w i : ℝ) * (u i : ℝ) ^ j * (ℓ + 1) = ∑ i, ((u i).toNat.choose ℓ : ℝ) * (v i : ℝ) * (w i : ℝ) * (u i : ℝ) ^ (j + 1) - ℓ * ∑ i, ((u i).toNat.choose ℓ : ℝ) * (v i : ℝ) * (w i : ℝ) * (u i : ℝ) ^ j := by
      rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_sub_distrib ] ; congr ; ext i ; linear_combination' h_identity i * v i * w i * u i ^ j;
    simp_all +decide [ ← Finset.sum_mul _ _ _ ];
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero ( by positivity ) ( h_sum_rewrite.trans ( by rw [ ih ( n + 1 ) ( fun t ht => hn t ( by linarith ) ) ( j + 1 ) ( by linarith ), ih n ( fun t ht => hn t ( by linarith ) ) j hj ] ; ring ) )

/-
Norm bound for binomial-multiplied vector: ‖choose(u,ℓ)·v‖² ≤ (M^ℓ/ℓ!)²·‖v‖².
-/
lemma binomial_multiply_norm_bound
    (s : ℕ) (M : ℝ) (u : Fin s → ℤ) (v : Fin s → ℤ) (ℓ : ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M) :
    ∑ i : Fin s, ((Nat.choose (u i).toNat ℓ : ℤ) * v i : ℝ) ^ 2 ≤
      (M ^ ℓ / (Nat.factorial ℓ : ℝ)) ^ 2 * ∑ i : Fin s, ((v i : ℤ) : ℝ) ^ 2 := by
  -- By the properties of binomial coefficients and the given bounds on $u_i$, we have $\binom{u_i}{\ell} \leq \frac{M^\ell}{\ell!}$.
  have h_binom_bound : ∀ i, ((Nat.choose (u i).toNat ℓ) : ℝ) ≤ (M ^ ℓ / (Nat.factorial ℓ)) := by
    intro i
    have h_choose_bound : (Nat.choose (u i).toNat ℓ : ℝ) ≤ (↑(u i).toNat) ^ ℓ / (Nat.factorial ℓ) := by
      convert choose_le_pow_div_factorial ( Int.toNat ( u i ) ) ℓ using 1;
    refine le_trans h_choose_bound ?_;
    gcongr;
    exact le_trans ( mod_cast Int.toNat_of_nonneg ( hu_range i |>.1 ) |> le_of_eq ) ( hu_range i |>.2 );
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => by simpa [ mul_pow ] using mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( h_binom_bound i ) 2 ) ( sq_nonneg _ ) ;

/-
M^j/j! is nondecreasing for j ≤ k ≤ M (for M ≥ 0).
-/
lemma pow_div_factorial_mono {M : ℝ} (hM : 0 ≤ M) {j k : ℕ}
    (hjk : j ≤ k) (hkM : (k : ℝ) ≤ M) :
    M ^ j / (Nat.factorial j : ℝ) ≤ M ^ k / (Nat.factorial k : ℝ) := by
  induction hjk <;> simp_all +decide [ Nat.factorial_succ, pow_succ ];
  rename_i k hk ih;
  exact le_trans ( ih ( by linarith ) ) ( by rw [ div_le_div_iff₀ ] <;> first | positivity | nlinarith [ pow_nonneg hM k, show ( k.factorial : ℝ ) > 0 by positivity, mul_le_mul_of_nonneg_right hkM ( show ( 0 : ℝ ) ≤ M ^ k by positivity ) ] )

set_option maxHeartbeats 800000 in
/-- At most r-e linearly independent kernel vectors can have all moments
0,...,r+e-1 vanishing. The kernel of L_0,...,L_{r+e-1} has dimension r-e
(by the Vandermonde argument, since r+e ≤ s = 2r and the u_i are distinct). -/
lemma kernel_high_excess_count
    (r s e : ℕ) (hs : s = 2 * r) (he : e ≤ r)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_strict : StrictMono u) (hw_pos : ∀ i, 0 < w i)
    (t : ℕ) (v : Fin t → (Fin s → ℤ))
    (hv : ∀ (k : Fin t) (j : ℕ), j < r + e →
      ∑ i, (v k i : ℝ) * (w i : ℝ) * (u i : ℝ) ^ j = 0)
    (hv_indep : LinearIndependent ℝ (fun k : Fin t => fun i : Fin s => (v k i : ℝ))) :
    t ≤ r - e := by
  -- By the Vandermonde argument, the (r+e) × s matrix A with A(j,i) = w_i * u_i^j has rank r+e.
  have h_rank : Matrix.rank (Matrix.of (fun (j : Fin (r + e)) (i : Fin s) => (w i : ℝ) * ((u i : ℝ)) ^ j.val)) = r + e := by
    -- The rows of the matrix are linearly independent because the Vandermonde matrix with distinct nodes is invertible.
    have h_vandermonde_indep : LinearIndependent ℝ (fun j : Fin (r + e) => fun i : Fin s => (w i : ℝ) * ((u i : ℝ)) ^ j.val) := by
      refine' Fintype.linearIndependent_iff.2 _;
      intro g hg i
      have h_poly : ∀ i_1 : Fin s, ∑ j : Fin (r + e), g j * ((u i_1 : ℝ)) ^ (j : ℕ) = 0 := by
        intro i_1; replace hg := congr_fun hg i_1; simp_all +decide ;
        convert congr_arg ( fun x : ℝ => x / ( w i_1 : ℝ ) ) hg using 1 <;> norm_num [ Finset.sum_div _ _ _, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( hw_pos i_1 ) ];
        exact Finset.sum_congr rfl fun _ _ => by rw [ mul_div_assoc, mul_div_cancel_right₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| hw_pos i_1 ) ] ;
      -- Since $u$ is strictly monotone, the polynomial $\sum_{j=0}^{r+e-1} g_j x^j$ has $s$ distinct roots, which implies it is the zero polynomial.
      have h_poly_zero : ∑ j : Fin (r + e), g j • (Polynomial.monomial j.val (1 : ℝ)) = 0 := by
        refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
        exact Finset.image ( fun i : Fin s => ( u i : ℝ ) ) Finset.univ;
        · rw [ Finset.card_image_of_injective _ fun i j hij => hu_strict.injective <| by simpa using hij ] ; norm_num [ Polynomial.degree_lt_iff_coeff_zero ];
          simp +decide [ Polynomial.coeff_monomial ];
          exact fun m hm => Finset.sum_eq_zero fun i hi => if_neg <| by linarith [ Fin.is_lt i ] ;
        · simp_all +decide [ Polynomial.eval_finset_sum ];
      replace h_poly_zero := congr_arg ( fun p => p.coeff i ) h_poly_zero ; simp_all +decide [ Polynomial.coeff_monomial ];
      simp_all +decide [ Fin.val_inj ];
    convert Matrix.rank_transpose _;
    any_goals try infer_instance;
    convert ( finrank_span_eq_card <| h_vandermonde_indep ) |> Eq.symm;
    · norm_num;
    · rw [ Matrix.rank ];
      congr;
      · simp +decide [ funext_iff, Matrix.mulVec, Submodule.mem_span_range_iff_exists_fun ];
        simp +decide [ dotProduct, mul_comm ];
      · ext; simp [Matrix.mulVecLin];
        simp +decide [ funext_iff, Matrix.mulVec, Submodule.mem_span_range_iff_exists_fun ];
        simp +decide [ dotProduct, mul_comm ];
      · ext; simp [Matrix.mulVecLin];
        simp +decide [ funext_iff, Matrix.mulVec, Submodule.mem_span_range_iff_exists_fun ];
        simp +decide [ dotProduct, mul_comm ];
  -- By the rank-nullity theorem, the dimension of the kernel of A is s - (r + e).
  have h_ker_dim : Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (Matrix.of (fun (j : Fin (r + e)) (i : Fin s) => (w i : ℝ) * ((u i : ℝ)) ^ j.val)))) = s - (r + e) := by
    have := LinearMap.finrank_range_add_finrank_ker ( Matrix.mulVecLin ( Matrix.of ( fun ( j : Fin ( r + e ) ) ( i : Fin s ) => ( w i : ℝ ) * ( u i : ℝ ) ^ j.val ) ) );
    simp_all +decide [ Matrix.rank ];
    exact eq_tsub_of_add_eq ( by linarith );
  -- Since the vectors $v_k$ lie in the kernel of $A$, their span is a subspace of the kernel.
  have h_span_ker : Submodule.span ℝ (Set.range (fun k : Fin t => (fun i : Fin s => ((v k i : ℤ) : ℝ)))) ≤ LinearMap.ker (Matrix.mulVecLin (Matrix.of (fun (j : Fin (r + e)) (i : Fin s) => (w i : ℝ) * ((u i : ℝ)) ^ j.val))) := by
    rw [ Submodule.span_le ];
    rintro _ ⟨ k, rfl ⟩ ; ext j; simp +decide [ Matrix.mulVec, dotProduct, mul_comm, mul_left_comm ] ;
    simpa only [ mul_assoc, mul_comm, mul_left_comm ] using hv k j ( Fin.is_lt j );
  have := Submodule.finrank_mono h_span_ker;
  rw [ finrank_span_eq_card ] at this <;> norm_num [ hv_indep ] at * ; omega

set_option maxHeartbeats 400000 in
/-
If v has excess e (moments vanishing up to r+e-1, moment r+e nonzero),
then choose(u, e) · v has nonzero r-th moment.
-/
lemma binomial_multiply_moment
    (s : ℕ) (u : Fin s → ℤ) (w : Fin s → ℕ) (v : Fin s → ℤ)
    (hu_nonneg : ∀ i, 0 ≤ u i) (e : ℕ) :
    ∀ r : ℕ,
    (∀ t : ℕ, t < r + e → ∑ i, (v i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ t = 0) →
    (∑ i, (v i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ (r + e) ≠ 0) →
    ∑ i, ((Nat.choose (u i).toNat e : ℤ) * v i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0 := by
  induction' e with e ih;
  · aesop;
  · intro r hr₁ hr₂;
    have h_identity : ∑ i, (Nat.choose (u i).toNat (e + 1) * v i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r = (1 / (e + 1 : ℝ)) * (∑ i, (Nat.choose (u i).toNat e * v i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ (r + 1)) - (e / (e + 1 : ℝ)) * (∑ i, (Nat.choose (u i).toNat e * v i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r) := by
      have h_identity : ∀ i, (Nat.choose (u i).toNat (e + 1) : ℝ) = (Nat.choose (u i).toNat e : ℝ) * ((u i : ℝ) - e) / (e + 1) := by
        intro i; rw [ eq_div_iff ] <;> norm_cast ;
        cases h : u i <;> simp_all +decide [ Nat.choose_succ_right_eq ];
        · exact Classical.or_iff_not_imp_right.2 fun h' => by rw [ Nat.cast_sub ( le_of_not_gt fun h'' => h' <| Nat.choose_eq_zero_of_lt h'' ) ] ;
        · linarith [ hu_nonneg i, Int.negSucc_lt_zero ‹_› ];
      rw [ Finset.mul_sum _ _ _, Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_sub_distrib ] ; congr ; ext i ; rw [ h_identity i ] ; ring;
    have h_ind : ∑ i, (Nat.choose (u i).toNat e * v i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ (r + 1) ≠ 0 := by
      apply ih (r + 1);
      · exact fun t ht => hr₁ t ( by linarith );
      · convert hr₂ using 1 ; ring_nf;
    have h_ind : ∑ i, (Nat.choose (u i).toNat e * v i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r = 0 := by
      convert kernel_binomial_multiply s u w v hu_nonneg e ( r + 1 ) ( fun t ht => hr₁ t ( by linarith ) ) r ( by linarith ) using 1;
    simp_all +decide [ Nat.cast_add_one_ne_zero ]

/-
Given m excess values in {1,...,r-1}, with the dimension constraint that
for each e, at most r-e of the values are ≥ e, the product of M^{e_k}/e_k!
is at most P = ∏_{j=0}^{r-1} M^j/j!.
-/
lemma excess_product_bound
    (r : ℕ) (hr : 2 ≤ r)
    (m : ℕ) (hm : m ≤ r)
    (M : ℝ) (hM : 0 ≤ M) (hrM : (r : ℝ) - 1 ≤ M)
    (e : Fin m → ℕ)
    (he_pos : ∀ k, 1 ≤ e k)
    (he_bound : ∀ k, e k ≤ r - 1)
    -- Dimension constraint: for each e₀ ≥ 1, at most r-e₀ indices have excess ≥ e₀
    (he_dim : ∀ e₀ : ℕ, 1 ≤ e₀ →
      (Finset.univ.filter (fun k : Fin m => e₀ ≤ e k)).card ≤ r - e₀) :
    ∏ k : Fin m, (M ^ (e k) / (Nat.factorial (e k) : ℝ)) ≤
      ∏ j ∈ Finset.range r, (M ^ j / (Nat.factorial j : ℝ)) := by
  -- By sorting the excesses, we can apply the induction hypothesis.
  have h_sorted : ∃ σ : Fin m ≃ Fin m, ∀ k l : Fin m, k < l → e (σ k) ≤ e (σ l) := by
    have h_sort : ∃ σ : Fin m → Fin m, Function.Injective σ ∧ ∀ k l : Fin m, k < l → e (σ k) ≤ e (σ l) := by
      have h_exists_min : ∀ (S : Finset (Fin m)), S.Nonempty → ∃ k ∈ S, ∀ j ∈ S, e k ≤ e j := by
        exact fun S hS => Finset.exists_min_image _ _ hS
      have h_sort : ∀ (n : ℕ) (hn : n ≤ m), ∀ (S : Finset (Fin m)), S.card = n → ∃ σ : Fin n → Fin m, Function.Injective σ ∧ (∀ k : Fin n, σ k ∈ S) ∧ (∀ k l : Fin n, k < l → e (σ k) ≤ e (σ l)) := by
        intro n hn S hS_card
        induction' n with n ih generalizing S;
        · simp +decide [ Function.Injective ];
        · obtain ⟨ k, hk₁, hk₂ ⟩ := h_exists_min S ( Finset.card_pos.mp ( by linarith ) ) ; obtain ⟨ σ, hσ₁, hσ₂, hσ₃ ⟩ := ih ( by linarith ) ( S.erase k ) ( by rw [ Finset.card_erase_of_mem hk₁, hS_card ] ; simp +decide ) ; use Fin.cons k σ; simp_all +decide [ Fin.forall_fin_succ, Function.Injective ] ;
          exact ⟨ fun i hi => False.elim <| hσ₂ i |>.1 <| hi.symm, fun i j hij => hσ₁ hij ⟩;
      exact Exists.elim ( h_sort m le_rfl Finset.univ ( by simp ) ) fun σ hσ => ⟨ σ, hσ.1, hσ.2.2 ⟩;
    exact ⟨ Equiv.ofBijective h_sort.choose ( ⟨ h_sort.choose_spec.1, Finite.injective_iff_surjective.mp h_sort.choose_spec.1 ⟩ ), h_sort.choose_spec.2 ⟩;
  obtain ⟨σ, hσ⟩ := h_sorted
  have h_prod_sorted : ∏ k, M ^ (e (σ k)) / (Nat.factorial (e (σ k)) : ℝ) ≤ ∏ j ∈ Finset.range m, M ^ (r - m + j) / (Nat.factorial (r - m + j) : ℝ) := by
    have h_prod_sorted : ∀ k : Fin m, e (σ k) ≤ r - m + k := by
      intro k
      have h_card : Finset.card (Finset.filter (fun l => e (σ k) ≤ e (σ l)) Finset.univ) ≥ m - k := by
        refine' le_trans _ ( Finset.card_mono <| show Finset.image ( fun l : Fin m => l ) ( Finset.Ici k ) ⊆ Finset.filter ( fun l => e ( σ k ) ≤ e ( σ l ) ) Finset.univ from _ );
        · simp +decide ;
        · grind;
      have h_card : Finset.card (Finset.filter (fun l => e (σ k) ≤ e l) Finset.univ) ≥ m - k := by
        convert h_card using 1;
        rw [ Finset.card_filter, Finset.card_filter ];
        conv_lhs => rw [ ← Equiv.sum_comp σ ] ;
      grind +suggestions;
    have h_prod_sorted : ∀ k : Fin m, M ^ (e (σ k)) / (Nat.factorial (e (σ k)) : ℝ) ≤ M ^ (r - m + k) / (Nat.factorial (r - m + k) : ℝ) := by
      intros k
      apply pow_div_factorial_mono hM (h_prod_sorted k);
      rw [ Nat.cast_add, Nat.cast_sub hm ] ; linarith [ show ( k : ℝ ) + 1 ≤ m by norm_cast; linarith [ Fin.is_lt k ] ];
    simpa only [ Finset.prod_range ] using Finset.prod_le_prod ( fun _ _ => div_nonneg ( pow_nonneg hM _ ) ( Nat.cast_nonneg _ ) ) fun _ _ => h_prod_sorted _;
  have h_prod_split : ∏ j ∈ Finset.range r, M ^ j / (Nat.factorial j : ℝ) = (∏ j ∈ Finset.range (r - m), M ^ j / (Nat.factorial j : ℝ)) * (∏ j ∈ Finset.range m, M ^ (r - m + j) / (Nat.factorial (r - m + j) : ℝ)) := by
    convert Finset.prod_range_add _ _ _ using 3 ; omega;
  have h_prod_ge_one : ∀ j ∈ Finset.range (r - m), 1 ≤ M ^ j / (Nat.factorial j : ℝ) := by
    intros j hj; rw [ one_le_div ( by positivity ) ] ; induction' j with j ih <;> norm_num [ pow_succ, Nat.factorial_succ ] at *;
    nlinarith [ ih ( Nat.lt_of_succ_lt hj ), show ( j : ℝ ) + 1 ≤ r - 1 by exact le_tsub_of_add_le_right ( by norm_cast; omega ), pow_nonneg hM j ];
  rw [ ← Equiv.prod_comp σ ];
  exact h_prod_sorted.trans ( h_prod_split.symm ▸ le_mul_of_one_le_left ( Finset.prod_nonneg fun _ _ => div_nonneg ( pow_nonneg hM _ ) ( Nat.cast_nonneg _ ) ) ( le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by positivity ) h_prod_ge_one ) ) )

/-
Combined comparison + vanishing moments: for each k < m, extract excess e with
both vanishing moments (for dimension constraint) and comparison bound.
-/
set_option maxHeartbeats 800000 in
lemma comparison_with_vanishing
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (M : ℝ) (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M)
    (hu_strict : StrictMono u) (hw_pos : ∀ i, 0 < w i)
    (v : Fin r → (Fin s → ℤ))
    (hv_kernel : ∀ (k : Fin r) (j : ℕ), j < r →
      ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0)
    (hv_indep : LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((v k i : ℤ) : ℝ))))
    (hv_succ : ∀ k : Fin r, ∀ x : Fin s → ℤ,
      (∀ j : ℕ, j < r → ∑ i, (x i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) →
      (fun i : Fin s => (x i : ℝ)) ∉
        Submodule.span ℝ ((fun j : Fin r => fun i : Fin s => (v j i : ℝ)) ''
          { j | j.val < k.val }) →
      ∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2 ≤ ∑ i : Fin s, ((x i : ℤ) : ℝ) ^ 2)
    (m : Fin r)
    (hm_nonzero : ∑ i, (v m i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0)
    (hm_min : ∀ k : Fin r, k.val < m.val →
      ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r = 0)
    (k : Fin r) (hk : k.val < m.val) :
    ∃ e : ℕ, 1 ≤ e ∧ e ≤ r - 1 ∧
      (∀ j : ℕ, j < r + e → ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      ∑ i : Fin s, ((v m i : ℤ) : ℝ) ^ 2 ≤
        (M ^ e / (Nat.factorial e : ℝ)) ^ 2 *
        ∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2 := by
  obtain ⟨e, he_pos, he_bound, he_vanish⟩ : ∃ e : ℕ, 1 ≤ e ∧ e ≤ r - 1 ∧ (∀ j : ℕ, j < r + e → ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧ (∑ i, ((Nat.choose (u i).toNat e : ℤ) * v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0) := by
    -- Let $t$ be the smallest index such that $L_t(v_k) \neq 0$.
    obtain ⟨t, ht⟩ : ∃ t : ℕ, r < t ∧ t < s ∧ (∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ t ≠ 0) ∧ (∀ j : ℕ, r < j → j < t → (∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0)) := by
      have ht_exists : ∃ t, r < t ∧ t < s ∧ (∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ t ≠ 0) := by
        have ht_exists : ∃ t, t < s ∧ (∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ t ≠ 0) := by
          contrapose! hv_indep;
          have := weighted_vandermonde_trivial_kernel s u w hu_strict hw_pos ( v k ) hv_indep; simp_all +decide [ funext_iff ] ;
          exact fun h => by have := h.ne_zero k; simp_all +decide [ funext_iff ] ;
        obtain ⟨ t, ht₁, ht₂ ⟩ := ht_exists;
        by_cases ht₃ : t < r;
        · exact False.elim <| ht₂ <| hv_kernel k t ht₃;
        · exact ⟨ t, lt_of_le_of_ne ( le_of_not_gt ht₃ ) ( Ne.symm <| by rintro rfl; exact ht₂ <| hm_min k hk ), ht₁, ht₂ ⟩;
      exact ⟨ Nat.find ht_exists, Nat.find_spec ht_exists |>.1, Nat.find_spec ht_exists |>.2.1, Nat.find_spec ht_exists |>.2.2, fun j hj₁ hj₂ => Classical.not_not.1 fun hj₃ => Nat.find_min ht_exists hj₂ ⟨ hj₁, by linarith [ Nat.find_spec ht_exists |>.2.1 ], hj₃ ⟩ ⟩;
    refine' ⟨ t - r, _, _, _, _ ⟩ <;> norm_num at *;
    · exact Nat.sub_pos_of_lt ht.1;
    · omega;
    · intro j hj; by_cases hj' : j < r <;> simp_all +decide [ Nat.add_sub_of_le ht.1.le ] ;
      cases hj'.eq_or_lt <;> [ aesop; exact ht.2.2.2 _ ‹_› ‹_› ];
    · convert binomial_multiply_moment s u w ( v k ) ( fun i => hu_range i |>.1 ) ( t - r ) r _ _ using 1;
      · intro j hj; by_cases hj' : j < r <;> simp_all +decide [ Nat.add_sub_of_le ht.1.le ] ;
        cases hj'.eq_or_lt <;> [ aesop; exact ht.2.2.2 _ ‹_› ‹_› ];
      · simpa only [ add_tsub_cancel_of_le ht.1.le ] using ht.2.2.1;
  refine' ⟨ e, he_pos, he_bound, he_vanish.1, le_trans ( hv_succ m _ _ _ ) _ ⟩;
  use fun i => Nat.choose ( u i |> Int.toNat ) e * v k i;
  · convert kernel_binomial_multiply s u w ( v k ) ( fun i => hu_range i |>.1 ) e r ( fun j hj => he_vanish.1 j ( by linarith ) ) using 1;
    norm_cast;
  · intro h;
    refine' he_vanish.2 _;
    rw [ Submodule.mem_span ] at h;
    specialize h ( LinearMap.ker ( show ( Fin s → ℝ ) →ₗ[ℝ] ℝ from { toFun := fun x => ∑ i, x i * ( w i : ℝ ) * ( u i : ℝ ) ^ r, map_add' := fun x y => by simp +decide [ Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm ], map_smul' := fun c x => by simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ] } ) ) ; simp_all +decide [ Set.subset_def ];
  · convert binomial_multiply_norm_bound s M u ( v k ) e hu_range using 1;
    norm_cast

/-
Dimension constraint from vanishing moments: used to apply excess_product_bound.
-/
lemma dim_constraint_from_vanishing
    (r s : ℕ) (_hr : 2 ≤ r) (hs : s = 2 * r)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_strict : StrictMono u) (hw_pos : ∀ i, 0 < w i)
    (m : ℕ) (_hm : m ≤ r)
    (v : Fin m → (Fin s → ℤ))
    (hv_indep : LinearIndependent ℝ (fun k : Fin m => fun i : Fin s => (v k i : ℝ)))
    (e : Fin m → ℕ)
    (he_vanish : ∀ k : Fin m, ∀ j : ℕ, j < r + e k →
      ∑ i, (v k i : ℝ) * (w i : ℝ) * (u i : ℝ) ^ j = 0) :
    ∀ e₀ : ℕ, 1 ≤ e₀ →
      (Finset.univ.filter (fun k : Fin m => e₀ ≤ e k)).card ≤ r - e₀ := by
  intro e₀ he₀_pos;
  by_cases he₀_le_r : e₀ ≤ r;
  · convert kernel_high_excess_count r s e₀ hs he₀_le_r u w hu_strict hw_pos _ _ _ _;
    use fun k i => v ( Finset.orderEmbOfFin ( Finset.univ.filter fun k => e₀ ≤ e k ) ( by simp +decide ) k ) i;
    · exact fun k j hj => he_vanish _ _ <| by linarith [ Finset.mem_filter.mp ( Finset.orderEmbOfFin_mem ( Finset.univ.filter fun k => e₀ ≤ e k ) ( by simp +decide ) k ) ] ;
    · exact hv_indep.comp _ ( fun k l hkl => by simpa [ Fin.ext_iff ] using hkl );
  · have h_empty : ∀ k : Fin m, e k < r := by
      intro k;
      contrapose! hv_indep;
      have h_zero : ∀ i : Fin s, v k i = 0 := by
        have h_zero : ∀ j : ℕ, j < s → ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0 := by
          exact fun j hj => he_vanish k j ( by linarith );
        have := weighted_vandermonde_trivial_kernel s u w hu_strict hw_pos ( v k ) h_zero; aesop;
      rw [ Fintype.not_linearIndependent_iff ];
      exact ⟨ fun i => if i = k then 1 else 0, by aesop ⟩;
    exact Finset.card_eq_zero.mpr ( Finset.eq_empty_of_forall_notMem fun k hk => by linarith [ Finset.mem_filter.mp hk, h_empty k ] ) |> fun h => h.symm ▸ Nat.zero_le _

/-
Product of comparison bounds: N(m)^r ≤ (∏ excess factors)² · ∏ N(k).
Pure arithmetic helper for multiplying comparison + monotonicity inequalities.
-/
lemma multiply_comparison_bounds
    (r : ℕ)
    (N : Fin r → ℝ) (hN_nonneg : ∀ k, 0 ≤ N k)
    (N_mono : Monotone N)
    (m : Fin r)
    (f : Fin m.val → ℝ) (hf_nonneg : ∀ k, 0 ≤ f k)
    (h_comp : ∀ k : Fin m.val, N m ≤ f k * N ⟨k.val, by omega⟩)
    : N m ^ r ≤ (∏ k : Fin m.val, f k) * ∏ k : Fin r, N k := by
  have h_prod_mono : N m ^ (r - m.val) ≤ ∏ k : Fin (r - m.val), N (⟨m.val + k.val, by
    linarith [ Fin.is_lt m, Fin.is_lt k, Nat.sub_add_cancel ( show ( m : ℕ ) ≤ r from m.2.le ) ]⟩) := by
    exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => hN_nonneg _ ) fun _ _ => N_mono <| Fin.le_iff_val_le_val.mpr <| Nat.le_add_right _ _ )
  generalize_proofs at *;
  convert mul_le_mul ( show N m ^ m.val ≤ ∏ k : Fin m, f k * N ⟨ k.val, by linarith [ Fin.is_lt k, m.2 ] ⟩ from ?_ ) h_prod_mono ( ?_ ) ( Finset.prod_nonneg fun _ _ => mul_nonneg ( hf_nonneg _ ) ( hN_nonneg _ ) ) using 1;
  · rw [ ← pow_add, Nat.add_sub_of_le ( Nat.le_of_lt m.2 ) ];
  · rw [ Finset.prod_mul_distrib ];
    rw [ mul_assoc, ← Finset.prod_image ];
    · rw [ ← Finset.prod_mul_prod_compl ];
      congr! 2;
      any_goals exact Finset.univ.filter fun i => i.val < m.val;
      · refine' Finset.prod_bij ( fun x hx => ⟨ x, by linarith [ Fin.is_lt x, Fin.is_lt m, Finset.mem_filter.mp hx ] ⟩ ) _ _ _ _ <;> simp +decide [ Fin.ext_iff ];
        exact fun k => ⟨ ⟨ k, by linarith [ Fin.is_lt k, Fin.is_lt m ] ⟩, k.2, rfl ⟩;
      · refine' Finset.prod_bij ( fun i hi => ⟨ i - m, by
          grind ⟩ ) _ _ _ _ <;> simp +decide [Fin.ext_iff]
        all_goals generalize_proofs at *;
        · grind;
        · exact fun k => ⟨ ⟨ m + k, by linarith [ Fin.is_lt k, Nat.sub_add_cancel ( show ( m : ℕ ) ≤ r from m.2.le ) ] ⟩, Nat.le_add_right _ _, by simp +decide ⟩;
        · exact fun a ha => congr_arg N ( Fin.ext <| by simp +decide [ Nat.add_sub_of_le <| show ( m : ℕ ) ≤ a from ha ] );
    · exact fun x _ y _ h => by simpa [ Fin.ext_iff ] using h;
  · exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => hN_nonneg _ ) fun _ _ => h_comp _ );
  · exact pow_nonneg ( hN_nonneg _ ) _

/-
Excess zero with comparison bound.
-/
lemma excess_zero_with_comparison_bound
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (M : ℝ) (hM : (s : ℝ) - 1 ≤ M)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i)
    (v : Fin r → (Fin s → ℤ))
    (hv_kernel : ∀ (k : Fin r) (j : ℕ), j < r →
      ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0)
    (hv_indep : LinearIndependent ℝ (fun k : Fin r => (fun i : Fin s => ((v k i : ℤ) : ℝ))))
    (hv_mono : Monotone (fun k : Fin r => ∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2))
    -- Successive minima property
    (hv_succ : ∀ k : Fin r, ∀ x : Fin s → ℤ,
      (∀ j : ℕ, j < r → ∑ i, (x i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) →
      (fun i : Fin s => (x i : ℝ)) ∉
        Submodule.span ℝ ((fun j : Fin r => fun i : Fin s => (v j i : ℝ)) ''
          { j | j.val < k.val }) →
      ∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2 ≤ ∑ i : Fin s, ((x i : ℤ) : ℝ) ^ 2) :
    ∃ m : Fin r,
      (∑ i, (v m i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0) ∧
      (∑ i : Fin s, ((v m i : ℤ) : ℝ) ^ 2) ^ r ≤
        (∏ j ∈ Finset.range r, ((M : ℝ) ^ j / (Nat.factorial j : ℝ))) ^ 2 *
        ∏ k : Fin r, (∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2) := by
  obtain ⟨m, hm⟩ : ∃ m : Fin r, ∑ i, (v m i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0 ∧ ∀ k : Fin r, k.val < m.val → ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r = 0 := by
    obtain ⟨m, hm⟩ : ∃ m : Fin r, ∑ i, (v m i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0 := by
      apply excess_zero_among_independent r hr s hs u w hu_strict hw_pos v hv_kernel hv_indep;
    obtain ⟨m, hm⟩ : ∃ m : Fin r, ∑ i, (v m i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0 ∧ ∀ k : Fin r, k.val < m.val → ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r = 0 := by
      have h_exists_min : ∃ m : Fin r, ∑ i, (v m i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0 ∧ ∀ k : Fin r, k.val < m.val → ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r = 0 := by
        have h_nonempty : ∃ k : Fin r, ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0 := by
          use m
        obtain ⟨m, hm⟩ : ∃ m : Fin r, ∑ i, (v m i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0 ∧ ∀ k : Fin r, k.val < m.val → ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r = 0 := by
          have h_nonempty : ∃ k : Fin r, ∑ i, (v k i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0 := h_nonempty
          have h_well_founded : WellFounded (fun k l : Fin r => k.val < l.val) := by
            exact wellFounded_lt
          have := h_well_founded.has_min { k : Fin r | ∑ i, ( v k i : ℝ ) * w i * u i ^ r ≠ 0 } ⟨ m, hm ⟩;
          exact ⟨ this.choose, this.choose_spec.1, fun k hk => Classical.not_not.1 fun hk' => this.choose_spec.2 k hk' hk ⟩;
        use m
      exact h_exists_min;
    use m;
  obtain ⟨e, he_pos, he_bound, he_vanish, he_comp⟩ : ∃ e : Fin m.val → ℕ, (∀ k, 1 ≤ e k) ∧ (∀ k, e k ≤ r - 1) ∧ (∀ k, ∀ j, j < r + e k → ∑ i, (v ⟨k.val, by omega⟩ i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧ (∀ k, ∑ i, ((v m i : ℤ) : ℝ) ^ 2 ≤ (M ^ (e k) / (Nat.factorial (e k) : ℝ)) ^ 2 * ∑ i, ((v ⟨k.val, by omega⟩ i : ℤ) : ℝ) ^ 2) := by
    choose! e he₁ he₂ he₃ he₄ using comparison_with_vanishing r hr s hs M u w hu_range hu_strict hw_pos v hv_kernel hv_indep hv_succ m hm.1 hm.2;
    exact ⟨ _, fun k => he₁ _ <| k.2, fun k => he₂ _ <| k.2, fun k => he₃ _ <| k.2, fun k => he₄ _ <| k.2 ⟩;
  have h_prod_bound : (∏ k : Fin m.val, (M ^ (e k) / (Nat.factorial (e k) : ℝ))) ≤ (∏ j ∈ Finset.range r, (M ^ j / (Nat.factorial j : ℝ))) := by
    apply_rules [ excess_product_bound ];
    · exact Nat.le_of_lt m.2;
    · linarith [ show ( s : ℝ ) ≥ 2 by norm_cast; linarith ];
    · exact le_trans ( by norm_num [ hs ] ; linarith ) hM;
    · apply_rules [ dim_constraint_from_vanishing ];
      · exact Nat.le_of_lt m.2;
      · exact hv_indep.comp _ ( fun a b h => by simpa [ Fin.ext_iff ] using h );
  refine' ⟨ m, hm.1, _ ⟩;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( Finset.prod_nonneg fun _ _ => div_nonneg ( pow_nonneg ( by linarith [ show ( s : ℝ ) ≥ 2 by norm_cast; linarith ] ) _ ) ( Nat.cast_nonneg _ ) ) h_prod_bound 2 ) ?_ );
  · convert multiply_comparison_bounds r ( fun k => ∑ i, ( v k i : ℝ ) ^ 2 ) ( fun k => Finset.sum_nonneg fun _ _ => sq_nonneg _ ) hv_mono m ( fun k => ( M ^ e k / ( e k |> Nat.factorial : ℝ ) ) ^ 2 ) ( fun k => sq_nonneg _ ) ( fun k => he_comp k ) using 1;
    rw [ Finset.prod_pow ];
  · exact Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-
Successive minima bounds, Hadamard's inequality for the annihilator lattice
determinant, the "excess" analysis, and the comparison inequalities.
-/
lemma lattice_core
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (M : ℝ) (hM : (s : ℝ) - 1 ≤ M)
    (W : ℝ) (hW : 1 ≤ W)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i)
    (hw_bound : ∀ i, (w i : ℝ) ≤ W) :
    ∃ a : Fin s → ℤ,
      (∀ (j : ℕ), j < r → ∑ i, (a i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      (∑ i, (a i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0) ∧
      ((∑ i : Fin s, ((a i : ℤ) : ℝ) ^ 2) ^ r ≤
        (∏ j ∈ Finset.range r, ((M : ℝ) ^ j / (Nat.factorial j : ℝ))) ^ 4 *
        (2 : ℝ) ^ (r * (r - 1)) * (2 * (r : ℝ)) ^ r * W ^ (2 * r)) := by
  obtain ⟨v, hv_kernel, hv_indep, hv_mono, hv_prod, hv_succ⟩ :=
    successive_kernel_vectors_exist r hr s hs M W hW u w hu_range hu_strict hw_pos hw_bound
  obtain ⟨m, hm_nonzero, hm_bound⟩ :=
    excess_zero_with_comparison_bound r hr s hs M hM u w hu_range hu_strict hw_pos
      v hv_kernel hv_indep hv_mono hv_succ
  refine ⟨v m, fun j hj => hv_kernel m j hj, hm_nonzero, ?_⟩
  set P := ∏ j ∈ Finset.range r, ((M : ℝ) ^ j / (Nat.factorial j : ℝ))
  set Q := (2 : ℝ) ^ (r * (r - 1)) * (2 * (r : ℝ)) ^ r * W ^ (2 * r)
  calc (∑ i : Fin s, ((v m i : ℤ) : ℝ) ^ 2) ^ r
      ≤ P ^ 2 * ∏ k : Fin r, (∑ i : Fin s, ((v k i : ℤ) : ℝ) ^ 2) := hm_bound
    _ ≤ P ^ 2 * (Q * P ^ 2) := by
        gcongr
    _ = P ^ 4 * Q := by ring
    _ = P ^ 4 * (2 : ℝ) ^ (r * (r - 1)) * (2 * (r : ℝ)) ^ r * W ^ (2 * r) := by ring

/-
For r ≥ 2 we have ∏_{j=0}^{r-1} j! ≥ (r/64)^{r(r-1)/2}.
-/
set_option exponentiation.threshold 10000 in
lemma factorial_product_lower_bound (r : ℕ) (hr : 2 ≤ r) :
    ((r : ℝ) / 64) ^ (r * (r - 1) / 2) ≤
    ∏ j ∈ Finset.range r, (Nat.factorial j : ℝ) := by
  induction' r with r ih <;> norm_num [ Finset.prod_range_succ ] at *;
  by_cases hr : r ≤ 64;
  · interval_cases r <;> norm_num [ Nat.factorial_succ, Finset.prod_range_succ ];
  · -- For the inductive step, we can use the fact that $r! \geq \left(\frac{r}{e}\right)^r$.
    have h_factorial_bound : (r.factorial : ℝ) ≥ (r / Real.exp 1) ^ r := by
      rw [ div_pow, ge_iff_le, div_le_iff₀ ] <;> norm_cast <;> norm_num [ Nat.factorial_pos ];
      · rw [ ← div_le_iff₀' ( by positivity ) ] ; rw [ Real.exp_eq_exp_ℝ ] ; norm_num [ NormedSpace.exp_eq_tsum_div ] ; exact Summable.le_tsum ( show Summable _ from Real.summable_pow_div_factorial _ ) r ( fun _ _ => by positivity ) ;
      · positivity;
    -- We can divide both sides by $(r / 64)^{r(r-1)/2}$ to simplify the inequality.
    suffices h_div : ((r + 1) / r : ℝ) ^ (r * (r - 1) / 2) * ((r + 1) / 64 : ℝ) ^ r ≤ (r / Real.exp 1) ^ r by
      refine le_trans ?_ ( mul_le_mul ( ih <| by linarith ) h_factorial_bound ?_ ?_ ) <;> try positivity;
      convert mul_le_mul_of_nonneg_left h_div ( show ( 0 :ℝ ) ≤ ( r / 64 ) ^ ( r * ( r - 1 ) / 2 ) by positivity ) using 1;
      rw [ ← mul_assoc, ← mul_pow ];
      rw [ show ( r + 1 ) * r / 2 = r * ( r - 1 ) / 2 + r by exact Nat.div_eq_of_eq_mul_left zero_lt_two <| by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ r ), Nat.div_mul_cancel ( show 2 ∣ r * ( r - 1 ) from even_iff_two_dvd.mp <| Nat.even_mul_pred_self _ ) ] ] ; rw [ pow_add ] ; ring_nf;
      norm_num [ sq, mul_assoc, ne_of_gt ( by linarith : 0 < r ) ];
    -- We can simplify the inequality by taking the $r$-th root of both sides.
    suffices h_root : ((r + 1) / r : ℝ) ^ ((r - 1) / 2 : ℝ) * ((r + 1) / 64 : ℝ) ≤ (r / Real.exp 1) by
      convert pow_le_pow_left₀ ( by positivity ) h_root r using 1 ; norm_num [ mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity : 0 ≤ ( r + 1 : ℝ ) / r ) ] ; ring_nf ; norm_num [ Nat.cast_sub ( show 1 ≤ r by linarith ) ] ; ring_nf;
      exact Or.inl ( by rw [ ← Real.rpow_natCast ] ; rw [ Nat.cast_div ( show 2 ∣ r * ( r - 1 ) from even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ) ( by positivity ) ] ; cases r <;> norm_num ; ring_nf ) ;
    -- We'll use that $(1 + \frac{1}{r})^{(r-1)/2} \leq e^{1/2}$ for $r \geq 65$.
    have h_exp_bound : ((r + 1) / r : ℝ) ^ ((r - 1) / 2 : ℝ) ≤ Real.exp (1 / 2) := by
      rw [ Real.rpow_def_of_pos ( by exact div_pos ( by positivity ) ( by norm_cast; linarith ) ) ];
      norm_num +zetaDelta at *;
      exact le_trans ( mul_le_mul_of_nonneg_right ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by linarith [ show ( r : ℝ ) ≥ 65 by norm_cast ] ) ) ( by nlinarith [ show ( r : ℝ ) ≥ 65 by norm_cast, div_mul_cancel₀ ( ( r : ℝ ) + 1 ) ( by positivity : ( r : ℝ ) ≠ 0 ) ] );
    refine le_trans ( mul_le_mul_of_nonneg_right h_exp_bound <| by positivity ) ?_;
    rw [ le_div_iff₀ ( Real.exp_pos _ ) ];
    have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show ( 1 : ℝ ) = 1 / 2 + 1 / 2 by norm_num, Real.exp_add ] at * ; norm_num at *;
    nlinarith [ Real.add_one_le_exp ( 1 / 2 ), show ( r : ℝ ) ≥ 65 by norm_cast, mul_le_mul_of_nonneg_left ( show ( r : ℝ ) ≥ 65 by norm_cast ) ( Real.exp_nonneg ( 1 / 2 ) ) ]

/-
Simple numerical bound: 2r ≤ 8^{r-1} for r ≥ 2.
-/
lemma two_mul_r_le_eight_pow (r : ℕ) (hr : 2 ≤ r) :
    2 * (r : ℝ) ≤ (8 : ℝ) ^ (r - 1) := by
  rcases r with ( _ | _ | r ) <;> norm_num at *;
  exact mod_cast Nat.recOn r ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ ] at ihn ⊢ ; linarith;

/-
The product ∏_{j<r} M^j/j! is at most (64M/r)^{r(r-1)/2} for M ≥ 0 and r ≥ 2.
-/
lemma moment_product_upper_bound (r : ℕ) (hr : 2 ≤ r) (M : ℝ) (hM : 0 ≤ M) :
    ∏ j ∈ Finset.range r, (M ^ j / (Nat.factorial j : ℝ)) ≤
    (64 * M / (r : ℝ)) ^ (r * (r - 1) / 2) := by
  convert div_le_div_of_nonneg_left _ _ ( factorial_product_lower_bound r hr ) using 1;
  rw [ Finset.prod_div_distrib ];
  · rw [ Finset.prod_pow_eq_pow_sum, Finset.sum_range_id ] ; ring_nf;
    norm_num;
  · exact Finset.prod_nonneg fun _ _ => pow_nonneg hM _;
  · positivity

/-
The lattice core bound implies the desired coordinate bound.
-/
lemma lattice_bound_implies_coord_bound (r : ℕ) (hr : 2 ≤ r) (M W : ℝ)
    (hM : 0 ≤ M) (hW : 0 ≤ W) :
    (∏ j ∈ Finset.range r, (M ^ j / (Nat.factorial j : ℝ))) ^ 4 *
    (2 : ℝ) ^ (r * (r - 1)) * (2 * (r : ℝ)) ^ r * W ^ (2 * r) ≤
    ((256 * M / (r : ℝ)) ^ (r - 1 : ℕ) * W) ^ (2 * r) := by
  -- Apply the moment_product_upper_bound and two_mul_r_le_eight_pow lemmas to bound the terms.
  have h1 : (∏ j ∈ Finset.range r, (M ^ j / (Nat.factorial j : ℝ))) ^ 4 ≤ (64 * M / r) ^ (2 * r * (r - 1)) := by
    convert pow_le_pow_left₀ ( Finset.prod_nonneg fun _ _ => by positivity ) ( moment_product_upper_bound r hr M hM ) 4 using 1 ; ring_nf;
    rw [ show r * ( r - 1 ) * 2 = r * ( r - 1 ) / 2 * 4 by linarith [ Nat.div_mul_cancel ( show 2 ∣ r * ( r - 1 ) from even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ) ] ];
  have h2 : (2 * r : ℝ) ^ r ≤ 8 ^ (r * (r - 1)) := by
    convert pow_le_pow_left₀ ( by positivity ) ( two_mul_r_le_eight_pow r hr ) r using 1 ; ring
  have h3 : (2 : ℝ) ^ (r * (r - 1)) * (2 * r) ^ r ≤ 4 ^ (2 * r * (r - 1)) := by
    convert mul_le_mul_of_nonneg_left h2 ( pow_nonneg zero_le_two ( r * ( r - 1 ) ) ) using 1 ; ring_nf;
    norm_num [ pow_mul', ← mul_pow ];
  convert mul_le_mul_of_nonneg_right ( mul_le_mul h1 h3 ( by positivity ) ( by positivity ) ) ( by positivity : 0 ≤ W ^ ( 2 * r ) ) using 1 ; ring;
  rw [ show ( 256 * M / r : ℝ ) = ( 64 * M / r ) * 4 by ring ] ; rw [ mul_pow ] ; ring_nf;
  norm_num [ mul_assoc, ← mul_pow ]

/-
Main lattice case (r ≥ 2)
-/
lemma silr_lattice_case
    (r : ℕ) (hr : 2 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (M : ℝ) (hM : (s : ℝ) - 1 ≤ M)
    (W : ℝ) (hW : 1 ≤ W)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i)
    (hw_bound : ∀ i, (w i : ℝ) ≤ W) :
    ∃ a : Fin s → ℤ,
      (∀ (j : ℕ), j < r → ∑ i, (a i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      (∑ i, (a i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0) ∧
      (∀ i, |(a i : ℝ)| ≤ (256 * M / (r : ℝ)) ^ (r - 1 : ℕ) * W) := by
  obtain ⟨a, ha⟩ := lattice_core r hr s hs M hM W hW u w hu_range hu_strict hw_pos hw_bound;
  refine' ⟨ a, ha.1, ha.2.1, _ ⟩;
  intro i
  have h_sq : (a i : ℝ) ^ 2 ≤ (∑ j : Fin s, (a j : ℝ) ^ 2) := by
    exact_mod_cast Finset.single_le_sum ( fun i _ => sq_nonneg ( a i ) ) ( Finset.mem_univ i );
  have h_abs : (a i : ℝ) ^ (2 * r) ≤ ((256 * M / r) ^ (r - 1) * W) ^ (2 * r) := by
    convert le_trans _ ( ha.2.2.trans _ ) using 1;
    · simpa only [ pow_mul ] using pow_le_pow_left₀ ( sq_nonneg _ ) h_sq _;
    · convert lattice_bound_implies_coord_bound r hr M W ( by linarith [ show ( s : ℝ ) ≥ 2 * 2 by norm_cast; linarith ] ) ( by linarith ) using 1;
  contrapose! h_abs;
  convert pow_lt_pow_left₀ h_abs ( mul_nonneg ( pow_nonneg ( div_nonneg ( mul_nonneg ( by norm_num ) ( show 0 ≤ M by linarith [ show ( s : ℝ ) ≥ 2 by norm_cast; linarith ] ) ) ( Nat.cast_nonneg _ ) ) _ ) ( by positivity ) ) ( by positivity : ( 2 * r ) ≠ 0 ) using 1 ; norm_num [ pow_mul ]

theorem small_integer_linear_relation_proof
    (r : ℕ) (hr : 1 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (M : ℝ) (hM : (s : ℝ) - 1 ≤ M)
    (W : ℝ) (hW : 1 ≤ W)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i)
    (hw_bound : ∀ i, (w i : ℝ) ≤ W) :
    ∃ a : Fin s → ℤ,
      (∀ (j : ℕ), j < r → ∑ i, (a i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      (∑ i, (a i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0) ∧
      (∀ i, |(a i : ℝ)| ≤ (256 * M / (r : ℝ)) ^ (r - 1 : ℕ) * W) := by
  by_cases hr2 : r ≥ 2;
  · convert silr_lattice_case r hr2 s hs M hM W hW u w hu_range hu_strict hw_pos hw_bound using 1;
  · interval_cases r ; subst hs;
    refine' ⟨ fun i => if i = 0 then w 1 else -w 0, _, _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_succ ];
    · ring;
    · nlinarith [ show ( w 0 : ℝ ) * w 1 > 0 by exact mul_pos ( Nat.cast_pos.mpr hw_pos.1 ) ( Nat.cast_pos.mpr hw_pos.2 ), show ( u 0 : ℝ ) < u 1 by exact_mod_cast hu_strict ( by decide ) ]

/-- Definitions of some constants that we use -/
def c₉ : ℝ := 256
def K_const : ℝ := max 4 c₉
def B_const : ℝ := 16 * K_const
def C₀_const : ℝ := 4 * B_const
def c₆ : ℝ := 4 * C₀_const

/-
Properties of constants
-/
lemma four_le_K : (4 : ℝ) ≤ K_const := le_max_left _ _
lemma K_pos : (0 : ℝ) < K_const := lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) four_le_K
lemma B_pos : (0 : ℝ) < B_const := by unfold B_const; linarith [K_pos]
lemma C₀_pos : (0 : ℝ) < C₀_const := by unfold C₀_const; linarith [B_pos]
lemma c₆_pos : (0 : ℝ) < c₆ := by unfold c₆; linarith [C₀_pos]

lemma mem_intIcc_iff (M : ℝ) (u : ℤ) :
    u ∈ intIcc M ↔ 0 ≤ u ∧ u ≤ ⌊M⌋ := by
  simp [intIcc, Finset.mem_Icc]

lemma intIcc_nonneg {M : ℝ} {u : ℤ} (hu : u ∈ intIcc M) : 0 ≤ u :=
  ((mem_intIcc_iff M u).mp hu).1

lemma intIcc_le_M {M : ℝ} {u : ℤ} (hu : u ∈ intIcc M) : (u : ℝ) ≤ M := by
  have h := ((mem_intIcc_iff M u).mp hu).2
  exact le_trans (Int.cast_le.mpr h) (Int.floor_le M)

lemma short_cardinality (s : ℕ) (M : ℝ) (hMs : M < (s : ℝ) - 1) :
    (intIcc M).card ≤ s - 1 := by
  -- Since $M < s - 1$, we have $\lfloor M \rfloor \leq s - 2$.
  have h_floor_le : ⌊M⌋ ≤ s - 2 := by
    exact Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; linarith;
  unfold intIcc; cases s <;> norm_num at * ; omega;
  linarith

/-
Given `2r` points with positive integer weights bounded by `W`, there exist integer
coefficients that annihilate the first `r` moments, have nonzero `r`-th moment,
and are bounded by `(c₉ M / r)^{r-1} · W`.
-/
theorem small_integer_linear_relation
    (r : ℕ) (hr : 1 ≤ r)
    (s : ℕ) (hs : s = 2 * r)
    (M : ℝ) (hM : (s : ℝ) - 1 ≤ M)
    (W : ℝ) (hW : 1 ≤ W)
    (u : Fin s → ℤ) (w : Fin s → ℕ)
    (hu_range : ∀ i, 0 ≤ u i ∧ (u i : ℝ) ≤ M)
    (hu_strict : StrictMono u)
    (hw_pos : ∀ i, 0 < w i)
    (hw_bound : ∀ i, (w i : ℝ) ≤ W) :
    ∃ a : Fin s → ℤ,
      (∀ (j : ℕ), j < r → ∑ i, (a i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ j = 0) ∧
      (∑ i, (a i : ℝ) * (w i : ℝ) * ((u i : ℝ)) ^ r ≠ 0) ∧
      (∀ i, |(a i : ℝ)| ≤ (c₉ * M / (r : ℝ)) ^ (r - 1 : ℕ) * W) := by
  have := small_integer_linear_relation_proof r hr s hs M hM W hW u w hu_range hu_strict hw_pos hw_bound
  simp only [c₉] at *
  exact this

/-- Translation rule: `(d/dx)^n f(a + x) = f^{(n)}(a + x)`. -/
lemma iteratedDeriv_comp_translate (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x => f (a + x)) = fun x => iteratedDeriv n f (a + x) :=
  iteratedDeriv_comp_const_add n f a

/-- Affine chain rule: `(d/dx)^n f(a + bx) = b^n · f^{(n)}(a + bx)`.
    Requires `f` to be `C^n`. -/
lemma iteratedDeriv_comp_affine (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (x : ℝ)
    (hf : ContDiff ℝ n f) :
    iteratedDeriv n (fun x => f (a + b * x)) x =
      b ^ n * iteratedDeriv n f (a + b * x) := by
  have hg : ContDiff ℝ n (fun y => f (a + y)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have h1 := congr_fun (iteratedDeriv_comp_const_mul hg b) x
  have h2 := congr_fun (iteratedDeriv_comp_const_add n f a) (b * x)
  rw [show (fun x => f (a + b * x)) = (fun x => (fun y => f (a + y)) (b * x)) from rfl]
  rw [h1, h2]

/-- Smoothness is preserved under affine composition. -/
lemma isGood_comp_affine {f : ℝ → ℝ} {W δ : ℝ} {u : ℤ} {a : ℤ} {b : ℕ}
    (hgood : IsGood f W δ (a + b * u)) :
    IsGood (fun x => f (↑a + ↑b * x)) W δ u := by
  obtain ⟨v, w, hw_pos, hw_le, happrox⟩ := hgood
  refine ⟨v, w, hw_pos, hw_le, ?_⟩
  convert happrox using 2
  push_cast
  ring

set_option maxHeartbeats 8000000

/-
For positive reals, 1/min(min(a,b),c) ≤ 1/a + 1/b + 1/c
-/
lemma one_div_min_le_sum_inv {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / min (min a b) c ≤ 1 / a + 1 / b + 1 / c := by
  field_simp;
  rw [ min_def, min_def ] ; split_ifs <;> nlinarith [ mul_pos ha hb, mul_pos ha hc, mul_pos hb hc ] ;

/-
(2r-1)/r ≤ 2 for r ≥ 1
-/
lemma finset_card_eq_sum_residue_classes (S : Finset ℤ) (ell : ℕ) (hell : 0 < ell) :
    S.card = ∑ j ∈ Finset.range ell,
      (S.filter (fun u => u % (ell : ℤ) = ↑j)).card := by
  rw [ ← Finset.card_biUnion ];
  · congr with u ; simp +decide;
    exact ⟨ fun hu => ⟨ Int.toNat ( u % ell ), by linarith [ Int.emod_lt_of_pos u ( by positivity : 0 < ( ell : ℤ ) ), Int.toNat_of_nonneg ( Int.emod_nonneg u ( by positivity : ( ell : ℤ ) ≠ 0 ) ) ], hu, by rw [ Int.toNat_of_nonneg ( Int.emod_nonneg u ( by positivity : ( ell : ℤ ) ≠ 0 ) ) ] ⟩, by aesop ⟩;
  · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;

lemma iteratedDeriv_comp_affine_lower_bound
    (f : ℝ → ℝ) (a : ℝ) (b : ℝ) (hb : 0 < b)
    (r : ℕ) (D_r : ℝ)
    (N' : ℝ)
    (hf_smooth : ContDiff ℝ (↑(r + 1) : ℕ∞) f)
    (hf_lower : ∀ x ∈ Set.Icc 0 (a + b * N'), D_r / 2 ≤ |iteratedDeriv r f x|)
    (x : ℝ) (hx : x ∈ Set.Icc 0 N')
    (ha_range : 0 ≤ a) :
    b ^ r * D_r / 2 ≤ |iteratedDeriv r (fun x => f (a + b * x)) x| := by
  rw [ iteratedDeriv_comp_affine ];
  · rw [ abs_mul, abs_of_nonneg ( by positivity ) ] ; nlinarith [ hf_lower ( a + b * x ) ⟨ by nlinarith [ hx.1 ], by nlinarith [ hx.2 ] ⟩, pow_pos hb r ] ;
  · exact hf_smooth.of_le (by exact_mod_cast Nat.le_succ r)

/-
Upper bound on r-th derivative of f(a + b·x)
-/
lemma good_point_transfer
    (f : ℝ → ℝ) (W δ : ℝ) (u : ℤ) (ell : ℕ)
    (j : ℕ) (hmod : u % (ell : ℤ) = ↑j)
    (hgood : IsGood f W δ u) :
    IsGood (fun x => f (↑j + ↑ell * x)) W δ (u / ↑ell) := by
  convert isGood_comp_affine _;
  convert hgood using 2 ; rw [ ← hmod, Int.emod_add_mul_ediv ]

/-
If every sub-interval of length M contains fewer than B elements of S,
    then |S| ≤ (N/M + 1) * (B-1).
-/
lemma block_subdivision_count
    (N M : ℝ) (hN : 0 < N) (hM : 0 < M)
    (B : ℕ) (hB : 1 ≤ B)
    (S : Finset ℤ)
    (hS_sub : ↑S ⊆ ↑(intIcc N))
    (h_per_block : ∀ (k : ℕ), (S.filter (fun u : ℤ =>
      (k : ℝ) * M ≤ (u : ℝ) ∧ (u : ℝ) < ((k : ℝ) + 1) * M)).card < B) :
    (S.card : ℝ) ≤ (N / M + 1) * ((B : ℝ) - 1) := by
  -- By partitioning S into blocks of length M, we can bound the cardinality of S by the sum of the cardinalities of these blocks.
  have h_partition : S.card ≤ ∑ k ∈ Finset.range (Nat.floor (N / M) + 1), (S.filter (fun u : ℤ => k * M ≤ (u : ℝ) ∧ (u : ℝ) < (k + 1) * M)).card := by
    refine le_trans ?_ ( Finset.card_biUnion_le );
    refine Finset.card_le_card ?_;
    intro u hu; specialize hS_sub hu; simp_all +decide [ intIcc ] ;
    refine' ⟨ ⌊ ( u : ℝ ) / M⌋₊, _, _, _ ⟩;
    · gcongr;
      exact Int.le_floor.mp hS_sub.2;
    · nlinarith [ Nat.floor_le ( show 0 ≤ ( u : ℝ ) / M by exact div_nonneg ( mod_cast hS_sub.1 ) hM.le ), mul_div_cancel₀ ( u : ℝ ) hM.ne' ];
    · nlinarith [ Nat.lt_floor_add_one ( ( u : ℝ ) / M ), mul_div_cancel₀ ( u : ℝ ) hM.ne' ];
  refine' le_trans ( Nat.cast_le.mpr h_partition ) _;
  refine' le_trans ( Nat.cast_le.mpr <| Finset.sum_le_sum fun _ _ => Nat.le_sub_one_of_lt <| h_per_block _ ) _ ; norm_num;
  gcongr <;> cases B <;> norm_num at * ; linarith [ Nat.floor_le ( by positivity : 0 ≤ N / M ) ]

/-
For j < ℓ and x ∈ [0, (N-j)/ℓ], j + ℓx ∈ [0, N]
-/
lemma sum_N_sub_j_div_ell_le (N : ℝ) (ell : ℕ) (hell : 0 < ell) :
    ∑ j ∈ Finset.range ell, ((N - ↑j) / ↑ell) ≤ N := by
  rw [ ← Finset.sum_div _ _ _, div_le_iff₀ ] <;> norm_num [ hell ];
  exact le_add_of_le_of_nonneg ( by linarith ) ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ )

/-
(N - j)/ℓ > 0 when j < ℓ ≤ N
-/
lemma ediv_in_intIcc {u : ℤ} {N : ℝ} {ell : ℕ} {j : ℕ}
    (hell : 0 < ell) (hu_mem : u ∈ intIcc N)
    (hmod : u % (ell : ℤ) = ↑j) :
    u / (ell : ℤ) ∈ intIcc ((N - ↑j) / ↑ell) := by
  unfold intIcc at *;
  norm_num at *;
  rw [ Int.le_floor ] at *;
  rw [ le_div_iff₀ ( by positivity ) ];
  exact ⟨ Int.ediv_nonneg hu_mem.1 ( by positivity ), by linarith [ show ( u : ℝ ) = ( u / ell : ℤ ) * ell + j by exact mod_cast by linarith [ Int.emod_add_mul_ediv u ell ] ] ⟩

/-
The algebraic part of lambda_one_case: given |S| ≤ (N/M + 1)(2r-1),
    derive the final C₀ bound.
-/
lemma block_count_to_C0_bound
    (r : ℕ) (hr : 2 ≤ r)
    (N : ℝ) (hN : 0 < N)
    (D_r D_r1 W δ : ℝ) (hDr : 0 < D_r) (hDr1 : 0 < D_r1)
    (hW : 1 ≤ W) (hδ : 0 < δ)
    (card_bound : ℝ)
    (h_card : card_bound ≤ (N / ((r : ℝ) / B_const * min (min
      ((D_r * W ^ 2) ^ (-(1 : ℝ) / ((2 : ℝ) * r - 1)))
      ((D_r / (D_r1 * W ^ 2)) ^ ((1 : ℝ) / ((2 : ℝ) * r))))
      ((D_r / (δ * W ^ 2)) ^ ((1 : ℝ) / ((r : ℝ) - 1)))) + 1) *
      (2 * (r : ℝ) - 1)) :
    card_bound < C₀_const * N *
      ((D_r * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
       (δ * W ^ 2 / D_r) ^ (((r : ℝ) - 1)⁻¹) +
       (D_r1 * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹)) +
    2 * (r : ℝ) := by
  -- Let's simplify the expression.
  suffices h_simp : (N / ((r : ℝ) / B_const * min (min ((D_r * W ^ 2) ^ (-1 / (2 * r - 1) : ℝ)) ((D_r / (D_r1 * W ^ 2)) ^ (1 / (2 * r) : ℝ))) ((D_r / (δ * W ^ 2)) ^ (1 / (r - 1) : ℝ)))) * (2 * r - 1) ≤ C₀_const * N * ((D_r * W ^ 2) ^ (2 * r - 1 : ℝ)⁻¹ + (δ * W ^ 2 / D_r) ^ (r - 1 : ℝ)⁻¹ + (D_r1 * W ^ 2 / D_r) ^ (2 * r : ℝ)⁻¹) by
    linarith [ show ( r : ℝ ) ≥ 2 by norm_cast ];
  -- By simplifying, we can see that the left-hand side is less than or equal to the right-hand side.
  have h_simp : (1 / (min (min ((D_r * W ^ 2) ^ (-1 / (2 * r - 1) : ℝ)) ((D_r / (D_r1 * W ^ 2)) ^ (1 / (2 * r) : ℝ))) ((D_r / (δ * W ^ 2)) ^ (1 / (r - 1) : ℝ)))) ≤ ((D_r * W ^ 2) ^ (2 * r - 1 : ℝ)⁻¹ + (δ * W ^ 2 / D_r) ^ (r - 1 : ℝ)⁻¹ + (D_r1 * W ^ 2 / D_r) ^ (2 * r : ℝ)⁻¹) := by
    convert one_div_min_le_sum_inv _ _ _ using 1;
    · norm_num [ neg_div, Real.rpow_neg_eq_inv_rpow ];
      rw [ ← Real.inv_rpow ( by positivity ), ← Real.inv_rpow ( by positivity ), ← Real.inv_rpow ( by positivity ) ] ; ring_nf;
      norm_num ; ring_nf;
    · positivity;
    · positivity;
    · positivity;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_simp <| by exact mul_nonneg ( by exact le_of_lt <| by exact show 0 < C₀_const by exact C₀_pos ) <| by positivity );
  field_simp [mul_comm, mul_assoc, mul_left_comm] at *;
  unfold B_const C₀_const; ring_nf; norm_num;
  unfold B_const; nlinarith [ show ( r : ℝ ) ≥ 2 by norm_cast, show ( K_const : ℝ ) ≥ 4 by exact_mod_cast four_le_K ] ;

lemma int_abs_lt_one_imp_zero (L : ℤ) (h : |(L : ℝ)| < 1) : L = 0 := by
  norm_cast at h; aesop;

/-
If intIcc M has at least n elements (n ≥ 1), then M ≥ n - 1.
-/
lemma eight_r_le_sixteen_pow (r : ℕ) (hr : 2 ≤ r) : (8 : ℝ) * r ≤ 16 ^ (r - 1) := by
  rcases r with ( _ | _ | r ) <;> norm_num at *;
  exact mod_cast Nat.recOn r ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith;

/-
Constant inequality (i): Under M bound from T₁,
    2r D_r W² (K_const M/r)^{2r-1} ≤ 1/2.
-/
lemma constant_ineq_i
    (r : ℕ) (hr : 2 ≤ r)
    (M : ℝ) (hM : 0 < M)
    (W : ℝ) (hW : 1 ≤ W)
    (D_r : ℝ) (hDr : 0 < D_r)
    (hM_le : M ≤ (r : ℝ) / B_const * (D_r * W ^ 2) ^ (-(1 : ℝ) / ((2 : ℝ) * r - 1))) :
    2 * (r : ℝ) * D_r * W ^ 2 * (K_const * M / (r : ℝ)) ^ (2 * r - 1) ≤ 1 / 2 := by
  -- From hM_le: KM/r ≤ 1/16 · (D_r W²)^{-1/(2r-1)} (since K = B/16)
  have hKM_div_r_le : (K_const * M / r) ^ (2 * r - 1) ≤ (1 / 16) ^ (2 * r - 1) * (D_r * W ^ 2) ^ (-1 : ℝ) := by
    have hKM_div_r_pow : (K_const * M / r) ≤ (1 / 16) * (D_r * W ^ 2) ^ (-1 / (2 * r - 1) : ℝ) := by
      rw [ div_le_iff₀ ( by positivity ) ];
      convert mul_le_mul_of_nonneg_left hM_le ( show 0 ≤ K_const by exact le_trans ( by norm_num ) ( le_max_left _ _ ) ) using 1 ; ring_nf;
      unfold K_const B_const; ring_nf;
      unfold K_const; norm_num [ c₉ ] ;
      ring;
    convert pow_le_pow_left₀ ( by exact div_nonneg ( mul_nonneg ( by exact le_of_lt K_pos ) hM.le ) ( Nat.cast_nonneg _ ) ) hKM_div_r_pow _ using 1;
    rw [ mul_pow, ← Real.rpow_natCast _ ( 2 * r - 1 ), ← Real.rpow_natCast _ ( 2 * r - 1 ), ← Real.rpow_mul ( by positivity ) ] ; norm_num [ Nat.cast_sub ( show 1 ≤ 2 * r by linarith ) ];
    exact Or.inl ( by rw [ div_mul_cancel₀ _ ( sub_ne_zero_of_ne ( by norm_cast; linarith ) ) ] );
  refine le_trans ( mul_le_mul_of_nonneg_left hKM_div_r_le <| by positivity ) ?_;
  norm_cast ; norm_num [ mul_assoc, mul_comm, mul_left_comm, hDr.ne', show W ≠ 0 by positivity ];
  rw [ show r * 2 - 1 = 2 * r - 1 by ring_nf ] ; rcases r with ( _ | _ | r ) <;> norm_num [ Nat.mul_succ, pow_succ' ] at *;
  exact Nat.recOn r ( by norm_num ) fun n ihn => by norm_num [ Nat.mul_succ, pow_succ' ] at ihn ⊢ ; nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 16 ) n ] ;

/-
Constant inequality (ii): Under M bound from T₂,
    2r D_{r+1} W² (K_const M/r)^{2r} ≤ D_r/4.
-/
lemma constant_ineq_ii
    (r : ℕ) (hr : 2 ≤ r)
    (M : ℝ) (hM : 0 < M)
    (W : ℝ) (hW : 1 ≤ W)
    (D_r : ℝ) (hDr : 0 < D_r)
    (D_r1 : ℝ) (hDr1 : 0 < D_r1)
    (hM_le : M ≤ (r : ℝ) / B_const * (D_r / (D_r1 * W ^ 2)) ^ ((1 : ℝ) / ((2 : ℝ) * r))) :
    2 * (r : ℝ) * D_r1 * W ^ 2 * (K_const * M / (r : ℝ)) ^ (2 * r) ≤ D_r / 4 := by
  -- Since $B = 16K$, $M \le r/B T₂$ gives $KM/r \le T₂/16$ where $T₂ = (D_r/(D_{r+1}W²))^{1/(2r)}$.
  have hKM_le_T2_div_16 : K_const * M / r ≤ (D_r / (D_r1 * W ^ 2)) ^ (1 / (2 * r) : ℝ) / 16 := by
    convert div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_left hM_le <| show ( 0 : ℝ ) ≤ K_const by exact le_of_lt K_pos ) ( show ( 0 : ℝ ) ≤ r by positivity ) using 1 ; ring_nf! ; norm_num [ show B_const = 16 * K_const by rfl ] ; ring_nf!;
    norm_num [ show r ≠ 0 by positivity, show K_const ≠ 0 by exact ne_of_gt ( lt_max_of_lt_left ( by norm_num ) ) ];
  -- So $2r D_{r+1} W² (KM/r)^{2r} ≤ 2r D_r / 16^{2r}$.
  have h_bound : 2 * r * D_r1 * W ^ 2 * (K_const * M / r) ^ (2 * r) ≤ 2 * r * D_r / 16 ^ (2 * r) := by
    refine le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by exact div_nonneg ( mul_nonneg ( by exact le_of_lt ( show 0 < K_const by exact lt_max_of_lt_left ( by norm_num ) ) ) hM.le ) ( Nat.cast_nonneg _ ) ) hKM_le_T2_div_16 _ ) ( by positivity ) ) ?_;
    rw [ div_pow, ← Real.rpow_natCast _ ( 2 * r ), ← Real.rpow_natCast _ ( 2 * r ), ← Real.rpow_mul ( by positivity ) ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_two.trans_le hr ) ];
    field_simp;
    norm_num;
  refine le_trans h_bound ?_;
  rw [ div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ pow_mul ];
  nlinarith [ show ( 256 : ℝ ) ^ r ≥ 2 * r * 4 by exact mod_cast Nat.le_induction ( by norm_num ) ( fun k hk ih ↦ by norm_num [ Nat.pow_succ ] at * ; nlinarith ) r hr ]

/-
Constant inequality (iii): Under M bound from T₃,
    2r δ W² (K_const M/r)^{r-1} ≤ D_r/4.
-/
lemma constant_ineq_iii
    (r : ℕ) (hr : 2 ≤ r)
    (M : ℝ) (hM : 0 < M)
    (W : ℝ) (hW : 1 ≤ W)
    (δ : ℝ) (hδ : 0 < δ)
    (D_r : ℝ) (hDr : 0 < D_r)
    (hM_le : M ≤ (r : ℝ) / B_const * (D_r / (δ * W ^ 2)) ^ ((1 : ℝ) / ((r : ℝ) - 1))) :
    2 * (r : ℝ) * δ * W ^ 2 * (K_const * M / (r : ℝ)) ^ (r - 1) ≤ D_r / 4 := by
  -- By multiplying both sides of the inequality $K_const * M / r \leq 1/16 * (D_r / (δ * W ^ 2)) ^ (1 / (r - 1))$ by $r$, we get $K_const * M \leq 1/16 * (D_r / (δ * W ^ 2)) ^ (1 / (r - 1)) * r$.
  have h_mul : (K_const * M / r) ^ (r - 1) ≤ (1 / 16) ^ (r - 1) * (D_r / (δ * W ^ 2)) := by
    convert pow_le_pow_left₀ ( by exact div_nonneg ( mul_nonneg ( by exact le_max_of_le_left ( by norm_num ) ) hM.le ) ( Nat.cast_nonneg _ ) ) ( show K_const * M / r ≤ ( 1 / 16 ) * ( D_r / ( δ * W ^ 2 ) ) ^ ( 1 / ( r - 1 : ℝ ) ) by
                                                                                                                                                  rw [ div_le_iff₀ ] <;> norm_num [ B_const ] at *;
                                                                                                                                                  · rw [ div_mul_eq_mul_div, le_div_iff₀ ] at hM_le <;> nlinarith [ show ( 0 : ℝ ) < K_const by exact lt_max_of_lt_left ( by norm_num ) ];
                                                                                                                                                  · linarith ) ( r - 1 ) using 1;
    rw [ mul_pow, ← Real.rpow_natCast _ ( r - 1 ), ← Real.rpow_natCast _ ( r - 1 ), ← Real.rpow_mul ( by positivity ), Nat.cast_sub ( by linarith ), Nat.cast_one, div_mul_cancel₀ _ ( sub_ne_zero_of_ne ( by norm_cast; linarith ) ) ] ; norm_num;
  refine le_trans ( mul_le_mul_of_nonneg_left h_mul <| by positivity ) ?_;
  -- We can divide both sides by $δ * W^2$ to simplify the inequality.
  suffices h_div : 2 * (r : ℝ) * (1 / 16) ^ (r - 1) ≤ 1 / 4 by
    convert mul_le_mul_of_nonneg_right h_div ( show 0 ≤ D_r by positivity ) using 1 <;> ring_nf;
    grind;
  have := eight_r_le_sixteen_pow r hr;
  rw [ one_div, inv_pow ] ; nlinarith [ show ( 0 : ℝ ) < 16 ^ ( r - 1 ) by positivity, mul_inv_cancel₀ ( show ( 16 : ℝ ) ^ ( r - 1 ) ≠ 0 by positivity ) ] ;

/-
For r ≥ 1: 1/r! ≤ (4/r)^r.
-/
lemma factorial_inv_le (r : ℕ) (hr : 1 ≤ r) :
    (1 : ℝ) / (r.factorial : ℝ) ≤ (4 / (r : ℝ)) ^ r := by
  -- We'll use the fact that $r! \geq (r/4)^r$ for $r \geq 1$.
  have h_factorial : ∀ r : ℕ, 1 ≤ r → (r.factorial : ℝ) ≥ (r / 4) ^ r := by
    intro r hr;
    induction hr <;> norm_num [ Nat.factorial ] at *;
    -- We'll use the fact that $(1 + 1/m)^m \leq 4$ for all $m \geq 1$.
    have h_exp : ∀ m : ℕ, 1 ≤ m → (1 + 1 / (m : ℝ)) ^ m ≤ 4 := by
      -- We'll use the fact that $(1 + 1/m)^m \leq e$ for all $m \geq 1$.
      have h_exp : ∀ m : ℕ, 1 ≤ m → (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp 1 := by
        intro m hm; rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ] ; norm_num;
        nlinarith [ Real.log_le_sub_one_of_pos ( by positivity : 0 < 1 + ( m : ℝ ) ⁻¹ ), mul_inv_cancel₀ ( by positivity : ( m : ℝ ) ≠ 0 ) ];
      exact fun m hm => le_trans ( h_exp m hm ) ( Real.exp_one_lt_d9.le.trans ( by norm_num ) );
    have := h_exp _ ‹_›; rw [ one_add_div ( by positivity ) ] at this; rw [ div_pow, div_le_iff₀ ( by positivity ) ] at *; ring_nf at *; nlinarith;
  convert one_div_le_one_div_of_le ( by positivity ) ( h_factorial r hr ) using 1 ; ring_nf;
  norm_num

/-
The Taylor polynomial of degree r at 0 approximates f with error ≤ D_{r+1} (4M/r)^{r+1}.
    More precisely, if f ∈ C^{r+1}[0,M] and |f^{(r+1)}| ≤ D_{r+1}, then
    |f(x) - ∑_{j=0}^r f^{(j)}(0)/j! x^j| ≤ D_{r+1} (4M/r)^{r+1} for x ∈ [0,M].

    We actually bound by D_{r+1} (K·M/r)^{r+1} since K ≥ 4.
-/
lemma taylor_degree_r_remainder
    (r : ℕ) (hr : 1 ≤ r) (M : ℝ) (_ : 0 < M)
    (D_r1 : ℝ) (hDr1 : 0 < D_r1)
    (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ (↑(r + 1) : ℕ∞) f)
    (hf_r1 : ∀ x ∈ Set.Icc (0 : ℝ) M, |iteratedDeriv (r + 1) f x| ≤ D_r1)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) M) :
    |f x - ∑ j ∈ Finset.range (r + 1), iteratedDeriv j f 0 / (j.factorial : ℝ) * x ^ j| ≤
      D_r1 * (K_const * M / (r : ℝ)) ^ (r + 1) := by
  -- By Taylor's theorem with remainder, we have |f(x) - ∑_{j=0}^r f^(j)(0)/j! x^j| ≤ D_{r+1} x^{r+1}/(r+1)!.
  have h_taylor_remainder : abs (f x - ∑ j ∈ Finset.range (r + 1), iteratedDeriv j f 0 / Nat.factorial j * x ^ j) ≤ D_r1 * x ^ (r + 1) / Nat.factorial (r + 1) := by
    by_cases hx0 : x = 0;
    · simp_all +decide [ Finset.sum_range_succ' ];
    · obtain ⟨x', hx'⟩ : ∃ x' ∈ Set.Ioo 0 x, f x - ∑ j ∈ Finset.range (r + 1), iteratedDeriv j f 0 / Nat.factorial j * x ^ j = iteratedDeriv (r + 1) f x' * x ^ (r + 1) / Nat.factorial (r + 1) := by
        have := @taylor_mean_remainder_lagrange_iteratedDeriv;
        convert this ( show 0 < x from lt_of_le_of_ne hx.1 ( Ne.symm hx0 ) ) ( hf_smooth.contDiffOn ) using 1;
        simp +decide [ taylorWithinEval ];
        simp +decide [ taylorWithin ];
        simp +decide [ taylorCoeffWithin, mul_comm ];
        congr! 3;
        refine' congr rfl ( Finset.sum_congr rfl fun i hi => _ );
        rw [ iteratedDerivWithin_eq_iteratedDeriv ];
        · ring;
        · exact uniqueDiffOn_Icc ( by linarith [ hx.1, hx.2, show x > 0 from lt_of_le_of_ne hx.1 ( Ne.symm hx0 ) ] );
        · exact hf_smooth.contDiffAt.of_le (by exact_mod_cast (Finset.mem_range.mp hi).le);
        · exact ⟨ le_rfl, hx.1 ⟩;
      rw [ hx'.2, abs_div, abs_mul, abs_of_nonneg ( by exact pow_nonneg hx.1 _ : ( 0 : ℝ ) ≤ x ^ ( r + 1 ) ), abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ ( r + 1 ).factorial ) ];
      gcongr ; aesop;
      exact hf_r1 x' ⟨ hx'.1.1.le, hx'.1.2.le.trans hx.2 ⟩;
  -- By the factorial estimate, we have 1/(r+1)! ≤ (4/(r+1))^{r+1} ≤ (4/r)^{r+1} ≤ (K/r)^{r+1}.
  have h_factorial_estimate : (1 : ℝ) / Nat.factorial (r + 1) ≤ (4 / r) ^ (r + 1) := by
    convert factorial_inv_le ( r + 1 ) ( by linarith ) |> le_trans <| ?_ using 1;
    gcongr ; norm_num;
  -- Substitute the factorial estimate into the Taylor remainder bound.
  have h_substitute : abs (f x - ∑ j ∈ Finset.range (r + 1), iteratedDeriv j f 0 / Nat.factorial j * x ^ j) ≤ D_r1 * x ^ (r + 1) * (4 / r) ^ (r + 1) := by
    exact h_taylor_remainder.trans ( by rw [ div_eq_mul_one_div ] ; exact mul_le_mul_of_nonneg_left ( by simpa using h_factorial_estimate ) ( mul_nonneg hDr1.le ( pow_nonneg hx.1 _ ) ) );
  -- Since $x \leq M$, we have $x^{r+1} \leq M^{r+1}$.
  have h_x_le_M : x ^ (r + 1) ≤ M ^ (r + 1) := by
    exact pow_le_pow_left₀ hx.1 hx.2 _;
  refine le_trans h_substitute ?_
  have h4K : (4 : ℝ) ≤ K_const := le_max_left 4 c₉
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have key : (4 * x / ↑r) ^ (r + 1) ≤ (K_const * M / ↑r) ^ (r + 1) := by
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ ↑r)
    exact mul_le_mul h4K hx.2 hx0 (by positivity)
  nlinarith [show D_r1 * x ^ (r + 1) * (4 / ↑r) ^ (r + 1) = D_r1 * (4 * x / ↑r) ^ (r + 1) from by ring]

/-
The approximation error: |∑ aᵢ(vᵢ - wᵢf(uᵢ))| ≤ ∑ |aᵢ| · δ · wᵢ
-/
lemma coeff_sum_bound'
    {s : ℕ} {a : Fin s → ℤ} {w : Fin s → ℕ}
    {W C_a : ℝ} (hCa : 0 ≤ C_a)
    (hw_bound : ∀ i, (w i : ℝ) ≤ W)
    (ha_bound : ∀ i, |(a i : ℝ)| ≤ C_a) :
    ∑ i, |(a i : ℝ)| * (w i : ℝ) ≤ (s : ℝ) * C_a * W := by
  exact le_trans ( Finset.sum_le_sum fun _ _ => mul_le_mul ( ha_bound _ ) ( hw_bound _ ) ( by positivity ) ( by positivity ) ) ( by norm_num; nlinarith )

/-- The "binomial polynomial" P_r(n) = n!/(r!(n-r)!) = C(n,r) is a nonneg integer for n ≥ 0. -/
lemma binomial_poly_eq_choose (n r : ℕ) :
    (1 : ℝ) / (r.factorial : ℝ) * ∏ m ∈ Finset.range r, ((n : ℝ) - m) = Nat.choose n r := by
  by_cases hn : n < r;
  · rw [ Nat.choose_eq_zero_of_lt hn, eq_comm ];
    rw [ Finset.prod_eq_zero ( Finset.mem_range.mpr hn ) ] <;> aesop;
  · field_simp;
    rw_mod_cast [ ← Nat.descFactorial_eq_factorial_mul_choose ];
    rw [ Nat.descFactorial_eq_prod_range ];
    rw [ Nat.cast_prod, Finset.prod_congr rfl fun x hx => Int.subNatNat_of_le ( by linarith [ Finset.mem_range.mp hx ] ) ]

/-
If ∑ aᵢwᵢuᵢ^j = 0 for j < r and ∑ aᵢwᵢuᵢ^r ≠ 0,
    then Z₀ = ∑ aᵢwᵢP_r(uᵢ) is a nonzero integer, so |Z₀| ≥ 1.
    Here Z₀ = 1/r! ∑ aᵢwᵢuᵢ^r (by moment annihilation applied to P_r - X^r/r!).
-/
lemma Z0_nonzero_integer
    {s r : ℕ}
    {a : Fin s → ℤ} {w : Fin s → ℕ} {u : Fin s → ℤ}
    (hu_nonneg : ∀ i, 0 ≤ u i)
    (h_vanish : ∀ j : ℕ, j < r → ∑ i, (a i : ℝ) * (w i : ℝ) * (u i : ℝ) ^ j = 0)
    (h_nonzero : ∑ i, (a i : ℝ) * (w i : ℝ) * (u i : ℝ) ^ r ≠ 0) :
    ∃ Z₀ : ℤ, Z₀ ≠ 0 ∧ (Z₀ : ℝ) = (1 : ℝ) / (r.factorial : ℝ) * ∑ i, (a i : ℝ) * (w i : ℝ) * (u i : ℝ) ^ r := by
  -- Define Z₀ as the sum of a_i w_i binom(u_i, r).
  set Z₀ : ℤ := ∑ i, (a i : ℤ) * (w i : ℤ) * Nat.choose (u i).toNat r;
  -- By definition of $Z₀$, we know that
  have hZ₀ : (Z₀ : ℝ) = (1 : ℝ) / (r.factorial : ℝ) * ∑ i, (a i : ℝ) * (w i : ℝ) * (u i : ℝ) ^ r := by
    have hZ₀ : (Z₀ : ℝ) = (1 : ℝ) / (r.factorial : ℝ) * ∑ i, (a i : ℝ) * (w i : ℝ) * (∏ j ∈ Finset.range r, ((u i : ℝ) - j)) := by
      have hZ₀ : ∀ i, (Nat.choose (u i).toNat r : ℝ) = (1 : ℝ) / (r.factorial : ℝ) * (∏ j ∈ Finset.range r, ((u i : ℝ) - j)) := by
        intro i; specialize hu_nonneg i
        obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hu_nonneg
        simp only [hn]; exact (binomial_poly_eq_choose n r).symm
      simp +zetaDelta at *;
      simp +decide only [hZ₀, Finset.mul_sum _ _ _, mul_left_comm];
    -- By definition of polynomial interpolation, we know that $\prod_{j=0}^{r-1} (u_i - j)$ is a polynomial of degree $r$.
    have h_poly_interpolate : ∃ p : Polynomial ℝ, p.degree ≤ r ∧ ∀ i, (∏ j ∈ Finset.range r, ((u i : ℝ) - j)) = p.eval (u i : ℝ) ∧ p.coeff r = 1 := by
      refine' ⟨ ∏ j ∈ Finset.range r, ( Polynomial.X - Polynomial.C ( j : ℝ ) ), _, _ ⟩;
      · norm_num [ Polynomial.degree_prod ];
        erw [ Finset.sum_congr rfl fun _ _ => Polynomial.degree_X_sub_C _ ] ; norm_num;
      · refine' fun i => ⟨ _, _ ⟩;
        · simp +decide [ Polynomial.eval_prod ];
        · have h_coeff : Polynomial.leadingCoeff (∏ j ∈ Finset.range r, (Polynomial.X - Polynomial.C (j : ℝ))) = 1 := by
            rw [ Polynomial.leadingCoeff_prod ] ; exact Finset.prod_eq_one fun _ _ => Polynomial.leadingCoeff_X_sub_C _;
          rw [ Polynomial.leadingCoeff, Polynomial.natDegree_prod _ _ fun x hx => Polynomial.X_sub_C_ne_zero _ ] at h_coeff;
          simpa [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] using h_coeff;
    obtain ⟨ p, hp₁, hp₂ ⟩ := h_poly_interpolate;
    have h_poly_interpolate : ∑ i, (a i : ℝ) * (w i : ℝ) * p.eval (u i : ℝ) = ∑ j ∈ Finset.range (r + 1), p.coeff j * ∑ i, (a i : ℝ) * (w i : ℝ) * (u i : ℝ) ^ j := by
      simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Polynomial.eval_eq_sum_range' ] ; ring_nf;
      exacts [ by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring, by linarith [ Polynomial.natDegree_le_of_degree_le hp₁ ] ];
    simp_all +decide [ Finset.sum_range_succ ];
    exact Or.inl ( by rw [ Finset.sum_eq_zero fun j hj => by rw [ h_vanish j ( Finset.mem_range.mp hj ) ] ; ring ] ; rw [ hp₂ ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩ |>.2 ] ; ring );
  exact ⟨ Z₀, by contrapose! h_nonzero; simp_all +decide [ Nat.factorial_ne_zero ], hZ₀ ⟩

/-
Short interval bound.
-/
theorem short_interval
    (r : ℕ) (hr : 2 ≤ r)
    (M : ℝ) (hM : 0 < M)
    (W : ℝ) (hW : 1 ≤ W)
    (δ : ℝ) (hδ : 0 < δ)
    (D_r : ℝ) (hDr : 0 < D_r)
    (D_r1 : ℝ) (hDr1 : 0 < D_r1)
    (f : ℝ → ℝ)
    (hf_smooth : ContDiff ℝ (↑(r + 1) : ℕ∞) f)
    (hf_r_lower : ∀ x ∈ Set.Icc (0 : ℝ) M, D_r / 2 ≤ |iteratedDeriv r f x|)
    (hf_r_upper : ∀ x ∈ Set.Icc (0 : ℝ) M, |iteratedDeriv r f x| ≤ D_r)
    (hf_r1 : ∀ x ∈ Set.Icc (0 : ℝ) M, |iteratedDeriv (r + 1) f x| ≤ D_r1)
    (S : Finset ℤ)
    (hS_sub : ↑S ⊆ ↑(intIcc M))
    (hS_good : ∀ u ∈ S, IsGood f W δ u)
    (hM_le : M ≤ (r : ℝ) / B_const * min (min
      ((D_r * W ^ 2) ^ (-(1 : ℝ) / ((2 : ℝ) * r - 1)))
      ((D_r / (D_r1 * W ^ 2)) ^ ((1 : ℝ) / ((2 : ℝ) * r))))
      ((D_r / (δ * W ^ 2)) ^ ((1 : ℝ) / ((r : ℝ) - 1)))) :
    S.card < 2 * r := by
  -- Convert hS_sub to Finset subset
  have hS_sub' : S ⊆ intIcc M := Finset.coe_subset.mp hS_sub
  -- If M < 2r - 1, use short_cardinality
  by_cases h_small : M < (2 * r : ℝ) - 1
  · have h1 := Finset.card_le_card hS_sub'
    have h2 := short_cardinality (2 * r) M (by push_cast; exact h_small)
    omega
  push_neg at h_small
  -- Suppose for contradiction |S| ≥ 2r
  by_contra h_contra; push_neg at h_contra
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.le_card_iff_exists_subset_card.mp h_contra
  set e := Finset.orderIsoOfFin T hT_card
  set u_fn := fun (i : Fin (2 * r)) => (e i : ℤ)
  have h_strict : StrictMono u_fn := fun i j hij => by exact_mod_cast (e.strictMono hij)
  have h_range : ∀ i, 0 ≤ u_fn i ∧ (u_fn i : ℝ) ≤ M := by
    intro i; have := hS_sub' (hT_sub (Finset.coe_mem (e i)))
    exact ⟨intIcc_nonneg this, intIcc_le_M this⟩
  have h_good : ∀ i, IsGood f W δ (u_fn i) := by
    intro i; exact hS_good _ (hT_sub (Finset.coe_mem (e i)))
  choose v_fn w_fn hw_pos hw_le h_approx using h_good
  have h_small' : ((2 * r : ℕ) : ℝ) - 1 ≤ M := by push_cast; exact h_small
  obtain ⟨a_fn, h_moment_zero, h_moment_r, h_coeff_bound⟩ :=
    small_integer_linear_relation r (by linarith) (2 * r) rfl M h_small' W hW
      u_fn w_fn h_range h_strict hw_pos hw_le
  -- Define key quantities
  set I : ℤ := ∑ i, a_fn i * v_fn i
  set I₁ : ℝ := iteratedDeriv r f 0 / (r.factorial : ℝ) *
    ∑ i, (a_fn i : ℝ) * (w_fn i : ℝ) * (u_fn i : ℝ) ^ r
  set R₁ : ℝ := ∑ i, (a_fn i : ℝ) * (w_fn i : ℝ) *
    (f (u_fn i : ℝ) - ∑ j ∈ Finset.range (r + 1),
      iteratedDeriv j f 0 / (j.factorial : ℝ) * (u_fn i : ℝ) ^ j)
  set R₂ : ℝ := ∑ i, (a_fn i : ℝ) * ((v_fn i : ℝ) - (w_fn i : ℝ) * f (u_fn i : ℝ))
  -- I = I₁ + R₁ + R₂ (splitting the integer into three real parts)
  have hI_split : (I : ℝ) = I₁ + R₁ + R₂ := by
    have hI : ∑ i, (a_fn i : ℝ) * (w_fn i : ℝ) * (∑ j ∈ Finset.range (r + 1), iteratedDeriv j f 0 / (j.factorial : ℝ) * (u_fn i : ℝ) ^ j) = I₁ := by
      simp +zetaDelta at *;
      simp +decide [Finset.mul_sum _ _ _, mul_assoc, mul_left_comm];
      rw [ Finset.sum_comm ];
      simp +decide [ Finset.sum_range_succ ];
      exact Finset.sum_eq_zero fun i hi => by simpa [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using mul_eq_zero_of_right ( iteratedDeriv i f 0 / ( i.factorial : ℝ ) ) ( h_moment_zero i ( Finset.mem_range.mp hi ) ) ;
    convert congr_arg₂ ( · + · ) ( congr_arg₂ ( · + · ) hI rfl ) rfl using 1;
    simp +zetaDelta at *;
    rw [ ← Finset.sum_add_distrib, ← Finset.sum_add_distrib ] ; congr ; ext ; ring;
  -- Key bounds
  have hI₁_upper : |I₁| ≤ 1 / 2 := by
    -- By the properties of the derivative and the bounds on the coefficients, we have:
    have hI1_bound : |I₁| ≤ D_r / (r.factorial : ℝ) * (2 * r * (c₉ * M / r) ^ (r - 1) * W * W) * M ^ r := by
      have hI1_bound : |∑ i, (a_fn i : ℝ) * (w_fn i : ℝ) * (u_fn i : ℝ) ^ r| ≤ (2 * r * (c₉ * M / r) ^ (r - 1) * W * W) * M ^ r := by
        have hI1_bound : ∀ i, |(a_fn i : ℝ) * (w_fn i : ℝ) * (u_fn i : ℝ) ^ r| ≤ (c₉ * M / r) ^ (r - 1) * W * W * M ^ r := by
          intros i
          have h_abs : |(a_fn i : ℝ) * (w_fn i : ℝ) * (u_fn i : ℝ) ^ r| ≤ |(a_fn i : ℝ)| * (w_fn i : ℝ) * M ^ r := by
            norm_num [ abs_mul ];
            exact mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( abs_nonneg _ ) ( by rw [ abs_of_nonneg ( mod_cast h_range i |>.1 ) ] ; exact h_range i |>.2 ) _ ) ( by positivity );
          exact h_abs.trans ( mul_le_mul_of_nonneg_right ( mul_le_mul ( h_coeff_bound i ) ( hw_le i ) ( by positivity ) ( by exact mul_nonneg ( pow_nonneg ( by exact div_nonneg ( mul_nonneg ( by norm_num [ c₉ ] ) hM.le ) ( Nat.cast_nonneg _ ) ) _ ) ( by positivity ) ) ) ( by positivity ) );
        exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum fun _ _ => hI1_bound _ ) ( by norm_num; linarith ) );
      have := hf_r_upper 0 ⟨ by norm_num, by linarith ⟩;
      rw [ abs_mul, abs_div ];
      rw [ abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ r.factorial ) ] ; convert mul_le_mul ( div_le_div_of_nonneg_right this ( by positivity : ( 0 : ℝ ) ≤ r.factorial ) ) hI1_bound ( by positivity ) ( by positivity ) using 1 ; ring;
    -- Using the factorial bound and the fact that $c₉ \leq K$, we can simplify the expression.
    have h_factorial_bound : D_r / (r.factorial : ℝ) * (2 * r * (c₉ * M / r) ^ (r - 1) * W * W) * M ^ r ≤ D_r * 2 * r * W ^ 2 * (K_const * M / r) ^ (2 * r - 1) := by
      have h_factorial_bound : M ^ r / (r.factorial : ℝ) ≤ (K_const * M / r) ^ r := by
        have hM_r_bound : M ^ r / (r.factorial : ℝ) ≤ (4 * M / r) ^ r := by
          have := factorial_inv_le r ( by linarith );
          convert mul_le_mul_of_nonneg_left this ( pow_nonneg hM.le r ) using 1 <;> ring;
        exact hM_r_bound.trans ( pow_le_pow_left₀ ( by positivity ) ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; exact mul_le_mul_of_nonneg_right ( by exact le_max_left _ _ ) hM.le ) _ );
      have h_factorial_bound : (c₉ * M / r) ^ (r - 1) * M ^ r / (r.factorial : ℝ) ≤ (K_const * M / r) ^ (2 * r - 1) := by
        rw [ show 2 * r - 1 = r - 1 + r by omega, pow_add ];
        rw [ mul_div_assoc ];
        gcongr;
        · exact pow_nonneg ( div_nonneg ( mul_nonneg ( by exact le_max_of_le_left ( by norm_num ) ) hM.le ) ( Nat.cast_nonneg _ ) ) _;
        · exact div_nonneg ( mul_nonneg ( by norm_num [ c₉ ] ) hM.le ) ( Nat.cast_nonneg _ );
        · exact le_max_right _ _;
      convert mul_le_mul_of_nonneg_left h_factorial_bound ( show 0 ≤ D_r * 2 * r * W ^ 2 by positivity ) using 1 ; ring;
    refine le_trans hI1_bound <| h_factorial_bound.trans ?_;
    convert constant_ineq_i r hr M hM W hW D_r hDr _ using 1;
    · ring;
    · exact hM_le.trans ( mul_le_mul_of_nonneg_left ( min_le_left _ _ |> le_trans <| min_le_left _ _ ) <| by exact div_nonneg ( Nat.cast_nonneg _ ) <| by exact mul_nonneg ( by norm_num ) <| le_max_of_le_left <| by norm_num )
  have hI₁_lower : D_r / 2 ≤ |I₁| := by
    -- By definition of $Z₀$, we have $Z₀ = 1/r! \sum a_i w_i u_i^r$.
    obtain ⟨Z₀, hZ₀_nonzero, hZ₀_eq⟩ : ∃ Z₀ : ℤ, Z₀ ≠ 0 ∧ (Z₀ : ℝ) = (1 : ℝ) / (r.factorial : ℝ) * ∑ i, (a_fn i : ℝ) * (w_fn i : ℝ) * u_fn i ^ r := by
      convert Z0_nonzero_integer ( fun i => h_range i |>.1 ) h_moment_zero h_moment_r using 1;
    -- By definition of $I₁$, we have $I₁ = f^{(r)}(0) \cdot Z₀$.
    have hI₁_def : I₁ = iteratedDeriv r f 0 * Z₀ := by
      grind;
    rw [ hI₁_def, abs_mul ];
    exact le_trans ( hf_r_lower 0 ⟨ by norm_num, by linarith ⟩ ) ( le_mul_of_one_le_right ( abs_nonneg _ ) ( mod_cast abs_pos.mpr hZ₀_nonzero ) )
  have hR_sum : |R₁ + R₂| < D_r / 2 := by
    -- We bound |R₁| using taylor_degree_r_remainder and constant_ineq_ii.
    have hR₁_bound : |R₁| ≤ 2 * r * D_r1 * W ^ 2 * (K_const * M / r) ^ (2 * r) := by
      have hR₁_bound : |R₁| ≤ D_r1 * (K_const * M / r) ^ (r + 1) * (∑ i, |(a_fn i : ℝ)| * (w_fn i : ℝ)) := by
        have hR₁_upper : ∀ i, |(a_fn i : ℝ) * (w_fn i : ℝ) * (f (u_fn i : ℝ) - ∑ j ∈ Finset.range (r + 1), iteratedDeriv j f 0 / (j.factorial : ℝ) * (u_fn i : ℝ) ^ j)| ≤ |(a_fn i : ℝ)| * (w_fn i : ℝ) * D_r1 * (K_const * M / r) ^ (r + 1) := by
          intros i
          have h_remainder_bound : |f (u_fn i : ℝ) - ∑ j ∈ Finset.range (r + 1), iteratedDeriv j f 0 / (j.factorial : ℝ) * (u_fn i : ℝ) ^ j| ≤ D_r1 * (K_const * M / r) ^ (r + 1) := by
            apply taylor_degree_r_remainder;
            grind;
            · linarith;
            · positivity;
            · exact hf_smooth;
            · exact hf_r1;
            · exact ⟨ mod_cast h_range i |>.1, h_range i |>.2 ⟩;
          rw [ abs_mul, abs_mul, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ w_fn i ) ] ; nlinarith [ show ( 0 : ℝ ) ≤ |↑ ( a_fn i )| * ↑ ( w_fn i ) by positivity ] ;
        exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => by convert hR₁_upper i using 1 ; ring );
      have hR₁_bound : |R₁| ≤ D_r1 * (K_const * M / r) ^ (r + 1) * (2 * r) * (c₉ * M / r) ^ (r - 1) * W ^ 2 := by
        have hR₁_bound : ∑ i, |(a_fn i : ℝ)| * (w_fn i : ℝ) ≤ (2 * r) * (c₉ * M / r) ^ (r - 1) * W ^ 2 := by
          convert coeff_sum_bound' ( show 0 ≤ ( c₉ * M / r ) ^ ( r - 1 ) * W by exact mul_nonneg ( pow_nonneg ( div_nonneg ( mul_nonneg ( by norm_num [ c₉ ] ) hM.le ) ( Nat.cast_nonneg _ ) ) _ ) ( by positivity ) ) ( fun i => hw_le i ) ( fun i => h_coeff_bound i ) using 1 ; norm_num [ mul_assoc, mul_comm, mul_left_comm ];
          ring;
        exact le_trans ‹_› ( by nlinarith [ show 0 ≤ D_r1 * ( K_const * M / r ) ^ ( r + 1 ) by exact mul_nonneg hDr1.le ( pow_nonneg ( div_nonneg ( mul_nonneg ( by norm_num [ K_const ] ) hM.le ) ( Nat.cast_nonneg _ ) ) _ ) ] );
      refine le_trans hR₁_bound ?_;
      rcases r <;> simp_all +decide [ Nat.mul_succ, pow_succ' ] ; ring_nf;
      simp only [c₉, K_const]; norm_num [pow_mul]; ring_nf; norm_num;
    -- We bound |R₂| using approx_error_bound' and constant_ineq_iii.
    have hR₂_bound : |R₂| < 2 * r * δ * W ^ 2 * (K_const * M / r) ^ (r - 1) := by
      have hR₂_bound : |R₂| < δ * ∑ i, |(a_fn i : ℝ)| * (w_fn i : ℝ) := by
        have hR₂_bound : |R₂| ≤ ∑ i, |(a_fn i : ℝ)| * (w_fn i : ℝ) * |f (u_fn i : ℝ) - (v_fn i : ℝ) / (w_fn i : ℝ)| := by
          convert Finset.abs_sum_le_sum_abs _ _ using 2 ; norm_num [ abs_mul, abs_sub_comm, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, ne_of_gt ( hw_pos _ ) ];
          · field_simp;
            exact Or.inl ( by rw [ show ( v_fn _ : ℝ ) / w_fn _ - f ( u_fn _ : ℝ ) = ( v_fn _ - w_fn _ * f ( u_fn _ : ℝ ) ) / w_fn _ by rw [ sub_div, mul_div_cancel_left₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| hw_pos _ ) ] ] ; rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ w_fn _ ) ] ; rw [ mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| hw_pos _ ) ] );
          · infer_instance;
        rw [ Finset.mul_sum _ _ _ ];
        refine' lt_of_le_of_lt hR₂_bound ( Finset.sum_lt_sum _ _ );
        · exact fun i _ => by nlinarith only [ h_approx i, show 0 ≤ |( a_fn i : ℝ )| * ( w_fn i : ℝ ) by positivity ] ;
        · obtain ⟨i, hi⟩ : ∃ i, a_fn i ≠ 0 := by
            exact not_forall.mp fun h => h_moment_r <| by simp +decide [ h ] ;
          exact ⟨ i, Finset.mem_univ _, by nlinarith only [ show 0 < |( a_fn i : ℝ )| * w_fn i by exact mul_pos ( abs_pos.mpr ( Int.cast_ne_zero.mpr hi ) ) ( Nat.cast_pos.mpr ( hw_pos i ) ), h_approx i ] ⟩;
      refine lt_of_lt_of_le hR₂_bound ?_;
      refine' le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ( hw_le i ) ( abs_nonneg _ ) ) hδ.le ) _;
      refine' le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ( h_coeff_bound i ) ( by positivity ) ) hδ.le ) _ ; norm_num ; ring_nf ; norm_num;
      simp only [c₉, K_const]; norm_num [pow_mul]; ring_nf; norm_num;
    -- We use constant_ineq_ii and constant_ineq_iii to bound |R₁| and |R₂|.
    have hR₁_bound' : |R₁| ≤ D_r / 4 := by
      refine le_trans hR₁_bound ?_;
      apply_rules [ constant_ineq_ii ];
      exact hM_le.trans ( mul_le_mul_of_nonneg_left ( min_le_left _ _ |> le_trans <| min_le_right _ _ ) <| by exact div_nonneg ( Nat.cast_nonneg _ ) <| by exact le_of_lt <| by exact B_pos )
    have hR₂_bound' : |R₂| < D_r / 4 := by
      refine lt_of_lt_of_le hR₂_bound ?_;
      convert constant_ineq_iii r hr M hM W hW δ hδ D_r hDr ( show M ≤ ( r : ℝ ) / B_const * ( D_r / ( δ * W ^ 2 ) ) ^ ( ( 1 : ℝ ) / ( r - 1 ) ) from le_trans hM_le <| mul_le_mul_of_nonneg_left ( min_le_right _ _ ) <| by exact div_nonneg ( Nat.cast_nonneg _ ) <| by exact le_of_lt <| by exact B_pos ) using 1;
    exact abs_lt.mpr ⟨ by linarith [ abs_le.mp hR₁_bound', abs_lt.mp hR₂_bound' ], by linarith [ abs_le.mp hR₁_bound', abs_lt.mp hR₂_bound' ] ⟩
  -- Contradiction: I ≠ 0 but |I| < 1
  have hI_ne_zero : I ≠ 0 := by
    intro hI_zero
    have : (I : ℝ) = 0 := by exact_mod_cast hI_zero
    rw [hI_split] at this
    have : I₁ = -(R₁ + R₂) := by linarith
    have : |I₁| = |R₁ + R₂| := by rw [this, abs_neg]
    linarith
  have hI_bound : |(I : ℝ)| < 1 := by
    rw [hI_split]
    have : |I₁ + (R₁ + R₂)| ≤ |I₁| + |R₁ + R₂| := abs_add_le _ _
    linarith [show |I₁ + R₁ + R₂| = |I₁ + (R₁ + R₂)| from by ring_nf]
  exact hI_ne_zero (int_abs_lt_one_imp_zero I hI_bound)

/-
For each block [kM, (k+1)M), translating f and applying short_interval gives < 2r good points.
-/
lemma per_block_bound
    (r : ℕ) (hr : 2 ≤ r)
    (M N : ℝ) (hM : 0 < M)
    (W : ℝ) (hW : 1 ≤ W)
    (δ : ℝ) (hδ : 0 < δ)
    (D_r : ℝ) (hDr : 0 < D_r)
    (D_r1 : ℝ) (hDr1 : 0 < D_r1)
    (f : ℝ → ℝ)
    (hf_smooth : ContDiff ℝ (↑(r + 1) : ℕ∞) f)
    (hf_r_lower : ∀ x ∈ Set.Icc (0 : ℝ) N, D_r / 2 ≤ |iteratedDeriv r f x|)
    (hf_r_upper : ∀ x ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv r f x| ≤ D_r)
    (hf_r1 : ∀ x ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv (r + 1) f x| ≤ D_r1)
    (hM_le : M ≤ (r : ℝ) / B_const * min (min
      ((D_r * W ^ 2) ^ (-(1 : ℝ) / ((2 : ℝ) * r - 1)))
      ((D_r / (D_r1 * W ^ 2)) ^ ((1 : ℝ) / ((2 : ℝ) * r))))
      ((D_r / (δ * W ^ 2)) ^ ((1 : ℝ) / ((r : ℝ) - 1))))
    (S : Finset ℤ)
    (hS_sub : ↑S ⊆ ↑(intIcc N))
    (hS_good : ∀ u ∈ S, IsGood f W δ u)
    (k : ℕ) :
    (S.filter (fun u : ℤ =>
      (k : ℝ) * M ≤ (u : ℝ) ∧ (u : ℝ) < ((k : ℝ) + 1) * M)).card < 2 * r := by
  by_contra h_contra;
  -- Let $a$ be the minimum element in the set $\{u \in S \mid kM \leq u < (k+1)M\}$.
  obtain ⟨a, ha⟩ : ∃ a ∈ S, (k : ℝ) * M ≤ (a : ℝ) ∧ (a : ℝ) < ((k : ℝ) + 1) * M ∧ ∀ u ∈ S, (k : ℝ) * M ≤ (u : ℝ) ∧ (u : ℝ) < ((k : ℝ) + 1) * M → a ≤ u := by
    obtain ⟨a, ha⟩ : ∃ a ∈ S, (k : ℝ) * M ≤ (a : ℝ) ∧ (a : ℝ) < ((k : ℝ) + 1) * M := by
      exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, Finset.mem_filter.mp hx |>.1, Finset.mem_filter.mp hx |>.2 ⟩;
    exact ⟨ Finset.min' ( S.filter fun u : ℤ => ( k : ℝ ) * M ≤ u ∧ u < ( k + 1 ) * M ) ⟨ a, by aesop ⟩, Finset.mem_filter.mp ( Finset.min'_mem ( S.filter fun u : ℤ => ( k : ℝ ) * M ≤ u ∧ u < ( k + 1 ) * M ) ⟨ a, by aesop ⟩ ) |>.1, Finset.mem_filter.mp ( Finset.min'_mem ( S.filter fun u : ℤ => ( k : ℝ ) * M ≤ u ∧ u < ( k + 1 ) * M ) ⟨ a, by aesop ⟩ ) |>.2.1, Finset.mem_filter.mp ( Finset.min'_mem ( S.filter fun u : ℤ => ( k : ℝ ) * M ≤ u ∧ u < ( k + 1 ) * M ) ⟨ a, by aesop ⟩ ) |>.2.2, fun u hu hu' => Finset.min'_le _ _ <| by aesop ⟩;
  -- Define $T = \{u - a \mid u \in S, kM \leq u < (k+1)M\}$.
  set T := Finset.image (fun u => u - a) (S.filter (fun u => (k : ℝ) * M ≤ (u : ℝ) ∧ (u : ℝ) < ((k : ℝ) + 1) * M)) with hT;
  -- Apply the short_interval lemma to the set $T$.
  have hT_short : T.card < 2 * r := by
    apply short_interval r hr (min M (N - a)) (by
    have := Finset.exists_mem_ne ( by linarith ) a; obtain ⟨ u, hu, hu' ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
    exact lt_of_lt_of_le ( show ( a : ℝ ) < u from mod_cast lt_of_le_of_ne ( ha.2.2.2 u hu.1 hu.2.1 hu.2.2 ) ( Ne.symm hu' ) ) ( mod_cast intIcc_le_M ( hS_sub hu.1 ) )) W hW δ hδ D_r hDr D_r1 hDr1 (fun x => f (a + x)) (by
    exact hf_smooth.comp ((contDiff_const.add contDiff_id).of_le le_top)) (by
    intro x hx
    have h_deriv : iteratedDeriv r (fun x => f (a + x)) x = iteratedDeriv r f (a + x) := by
      rw [ iteratedDeriv_comp_translate ];
    convert hf_r_lower ( a + x ) ⟨ by linarith [ hx.1, show ( a : ℝ ) ≥ 0 from mod_cast intIcc_nonneg ( hS_sub ha.1 ) ], by linarith [ hx.2, min_le_left M ( N - a ), min_le_right M ( N - a ) ] ⟩ using 1 ; aesop) (by
    intro x hx; rw [ iteratedDeriv_comp_translate ] ;
    exact hf_r_upper _ ⟨ by linarith [ hx.1, show ( a : ℝ ) ≥ 0 by exact_mod_cast intIcc_nonneg ( hS_sub ha.1 ) ], by linarith [ hx.2, min_le_left M ( N - a ), min_le_right M ( N - a ) ] ⟩) (by
    intro x hx; rw [ iteratedDeriv_comp_translate ] ; norm_num;
    exact hf_r1 _ ⟨ by linarith [ hx.1, show ( a : ℝ ) ≥ 0 by exact_mod_cast intIcc_nonneg ( hS_sub ha.1 ) ], by linarith [ hx.2, min_le_left M ( N - a ), min_le_right M ( N - a ) ] ⟩) T (by
    simp_all +decide [ Finset.subset_iff ];
    rintro _ u hu hu₁ hu₂ rfl; specialize hS_sub hu; simp_all +decide [ intIcc ] ;
    exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; cases min_cases M ( N - a ) <;> linarith [ Int.floor_le ( min M ( N - a ) ), Int.lt_floor_add_one ( min M ( N - a ) ), show ( u : ℝ ) ≤ ⌊N⌋ from mod_cast hS_sub.2, Int.floor_le N, Int.lt_floor_add_one N ] )) (by
    simp +zetaDelta at *;
    rintro u x hx hx₁ hx₂ rfl; specialize hS_good x hx; obtain ⟨ v, w, hw₁, hw₂, hw₃ ⟩ := hS_good; use v, w; aesop;) (by
    exact le_trans ( min_le_left _ _ ) hM_le);
  rw [ Finset.card_image_of_injective _ ( sub_left_injective ) ] at hT_short ; linarith

/-
The `λ = 1` case
-/
theorem lambda_one_case
    (r : ℕ) (hr : 2 ≤ r)
    (N : ℝ) (hN : 0 < N)
    (W : ℝ) (hW : 1 ≤ W)
    (δ : ℝ) (hδ : 0 < δ)
    (D_r : ℝ) (hDr : 0 < D_r)
    (D_r1 : ℝ) (hDr1 : 0 < D_r1)
    (f : ℝ → ℝ)
    (hf_smooth : ContDiff ℝ (↑(r + 1) : ℕ∞) f)
    (hf_r_lower : ∀ x ∈ Set.Icc (0 : ℝ) N, D_r / 2 ≤ |iteratedDeriv r f x|)
    (hf_r_upper : ∀ x ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv r f x| ≤ D_r)
    (hf_r1 : ∀ x ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv (r + 1) f x| ≤ D_r1)
    (S : Finset ℤ)
    (hS_sub : ↑S ⊆ ↑(intIcc N))
    (hS_good : ∀ u ∈ S, IsGood f W δ u) :
    (S.card : ℝ) < C₀_const * N *
      ((D_r * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
       (δ * W ^ 2 / D_r) ^ (((r : ℝ) - 1)⁻¹) +
       (D_r1 * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹)) +
    2 * (r : ℝ) := by
  -- Let $M = (r/B_const) * \min(\min(T₁, T₂), T₃)$.
  set M := (r : ℝ) / B_const * min (min ((D_r * W ^ 2) ^ (-(1 : ℝ) / ((2 : ℝ) * r - 1))) ((D_r / (D_r1 * W ^ 2)) ^ ((1 : ℝ) / ((2 : ℝ) * r)))) ((D_r / (δ * W ^ 2)) ^ ((1 : ℝ) / ((r : ℝ) - 1))) with hM_def;
  by_cases hM_pos : 0 < M;
  · have h_card_bound : (S.card : ℝ) ≤ (N / M + 1) * (2 * r - 1) := by
      convert block_subdivision_count N M hN hM_pos ( 2 * r ) ( by linarith ) S ( fun u hu => hS_sub hu ) _ using 1;
      · norm_cast;
      · convert per_block_bound r hr M N hM_pos W hW δ hδ D_r hDr D_r1 hDr1 f hf_smooth _ _ _ _ S ( fun u hu => hS_sub hu ) hS_good using 1;
        · exact hf_r_lower;
        · exact hf_r_upper;
        · exact hf_r1;
        · rfl;
    convert block_count_to_C0_bound r hr N hN D_r D_r1 W δ hDr hDr1 hW hδ _ h_card_bound using 1;
  · contrapose! hM_pos;
    refine' mul_pos ( div_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( by exact mul_pos ( by norm_num ) ( by exact lt_max_of_lt_left ( by norm_num ) ) ) ) ( lt_min ( lt_min ( Real.rpow_pos_of_pos ( by positivity ) _ ) ( Real.rpow_pos_of_pos ( by positivity ) _ ) ) ( Real.rpow_pos_of_pos ( by positivity ) _ ) )

/-- When `N ≤ λ`, the cardinality of `S` is at most `2rλ`. -/
lemma konyagin_case_small_N
    (r : ℕ) (hr : 2 ≤ r) (N lam : ℝ) (hN : 0 < N) (hlam : 1 ≤ lam)
    (hN_lam : N ≤ lam)
    (S : Finset ℤ) (hS_sub : ↑S ⊆ ↑(intIcc N)) :
    (S.card : ℝ) ≤ 2 * (r : ℝ) * lam := by
  -- Since $S$ is a subset of $\{0, 1, \ldots, \lfloor N \rfloor\}$, we have $|S| \leq \lfloor N \rfloor + 1$.
  have h_card_le : (S.card : ℝ) ≤ ⌊N⌋ + 1 := by
    have := Finset.card_le_card hS_sub; simp_all +decide [ intIcc ] ;
    norm_cast ; linarith [ Int.toNat_of_nonneg ( show 0 ≤ ⌊N⌋ + 1 by positivity ) ] ;
  nlinarith [ show ( r : ℝ ) ≥ 2 by norm_cast, show ( ⌊N⌋ : ℝ ) ≤ N by exact Int.floor_le N ]

/-- The main rpow term is positive. -/
lemma konyagin_main_term_pos
    (r : ℕ) (N W δ lam D_r D_r1 : ℝ)
    (hN : 0 < N) (hW : 1 ≤ W) (hδ : 0 < δ) (hlam : 1 ≤ lam)
    (hDr : 0 < D_r) (hDr1 : 0 < D_r1) :
    0 < c₆ * N *
      ((D_r * lam ^ (r : ℕ) * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
       (δ * W ^ 2 / (D_r * lam ^ (r : ℕ))) ^ (((r : ℝ) - 1)⁻¹) +
       (D_r1 * lam * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹)) := by
  refine' mul_pos _ ( add_pos_of_pos_of_nonneg ( add_pos_of_pos_of_nonneg _ _ ) _ )
  · exact mul_pos ( c₆_pos ) hN
  · positivity
  · positivity
  · positivity

/-- `A + 4B + C ≤ 4(A + B + C)` for nonneg reals. -/
lemma two_rpow_le_four (r : ℕ) (hr : 2 ≤ r) :
    (2 : ℝ) ^ ((r : ℝ) / ((r : ℝ) - 1)) ≤ 4 := by
  exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_num ) ( show ( r : ℝ ) / ( r - 1 ) ≤ 2 by rw [ div_le_iff₀ ] <;> linarith [ show ( r : ℝ ) ≥ 2 by norm_cast ] ) ) ( by norm_num )

/-
The term `(δW²/(ℓ^r D_r))^{1/(r-1)}` is at most
    `4 · (δW²/(λ^r D_r))^{1/(r-1)}` when `ℓ > λ/2` and `r ≥ 2`.
-/
lemma term2_comparison
    (r : ℕ) (hr : 2 ≤ r)
    (D_r W δ : ℝ) (hDr : 0 < D_r) (hW : 1 ≤ W) (hδ : 0 < δ)
    (ell : ℕ) (lam : ℝ) (hell : 0 < ell)
    (hell_le : (ell : ℝ) ≤ lam) (hlam_lt : lam < 2 * (ell : ℝ)) :
    (δ * W ^ 2 / ((ell : ℝ) ^ (r : ℕ) * D_r)) ^ (((r : ℝ) - 1)⁻¹) ≤
    4 * (δ * W ^ 2 / (D_r * lam ^ (r : ℕ))) ^ (((r : ℝ) - 1)⁻¹) := by
  -- Since ℓ > λ/2, we have ℓ^r > (λ/2)^r, so 1/(ℓ^r) < 1/((λ/2)^r) = 2^r/λ^r.
  have h_bound : 1 / (ell : ℝ) ^ r < (2 : ℝ) ^ r / (lam : ℝ) ^ r := by
    rw [ div_lt_div_iff₀ ] <;> try positivity;
    · simpa only [ one_mul, ← mul_pow ] using pow_lt_pow_left₀ hlam_lt ( by linarith ) ( by linarith );
    · exact pow_pos ( by linarith [ show ( ell : ℝ ) ≥ 1 by norm_cast ] ) _;
  -- Therefore, δW²/(ℓ^r D_r) < 2^r δW²/(λ^r D_r).
  have h_bound' : δ * W ^ 2 / ((ell : ℝ) ^ r * D_r) < 2 ^ r * δ * W ^ 2 / (lam ^ r * D_r) := by
    convert mul_lt_mul_of_pos_left h_bound ( show 0 < δ * W ^ 2 / D_r by positivity ) using 1 <;> ring;
  refine' le_trans ( Real.rpow_le_rpow ( by positivity ) h_bound'.le ( inv_nonneg.mpr ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ) _;
  rw [ show ( 2 ^ r * δ * W ^ 2 / ( lam ^ r * D_r ) ) = ( δ * W ^ 2 / ( D_r * lam ^ r ) ) * ( 2 ^ r ) by ring, Real.mul_rpow ( by exact div_nonneg ( by positivity ) ( by exact mul_nonneg hDr.le ( pow_nonneg ( by linarith ) _ ) ) ) ( by positivity ) ];
  rw [ mul_comm ] ; gcongr;
  · exact Real.rpow_nonneg ( div_nonneg ( mul_nonneg hδ.le ( sq_nonneg _ ) ) ( mul_nonneg hDr.le ( pow_nonneg ( by linarith ) _ ) ) ) _;
  · convert two_rpow_le_four r hr using 1;
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_comm ] ; ring_nf

/-
The `C₀ · (terms with ℓ) ≤ c₆ · (terms with λ)` algebraic comparison.
-/
lemma algebraic_comparison
    (r : ℕ) (hr : 2 ≤ r)
    (D_r D_r1 W δ : ℝ) (hDr : 0 < D_r) (hDr1 : 0 < D_r1)
    (hW : 1 ≤ W) (hδ : 0 < δ)
    (ell : ℕ) (lam : ℝ) (hell : 0 < ell)
    (hell_le : (ell : ℝ) ≤ lam) (hlam_lt : lam < 2 * (ell : ℝ)) :
    C₀_const *
      (((ell : ℝ) ^ (r : ℕ) * D_r * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
       (δ * W ^ 2 / ((ell : ℝ) ^ (r : ℕ) * D_r)) ^ (((r : ℝ) - 1)⁻¹) +
       ((ell : ℝ) * D_r1 * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹)) ≤
    c₆ *
      ((D_r * lam ^ (r : ℕ) * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
       (δ * W ^ 2 / (D_r * lam ^ (r : ℕ))) ^ (((r : ℝ) - 1)⁻¹) +
       (D_r1 * lam * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹)) := by
  -- Apply the term2_comparison lemma.
  have h_term2 : (δ * W ^ 2 / (ell ^ r * D_r)) ^ (1 / (r - 1 : ℝ)) ≤ 4 * (δ * W ^ 2 / (D_r * lam ^ r)) ^ (1 / (r - 1 : ℝ)) := by
    convert term2_comparison r hr D_r W δ hDr hW hδ ell lam hell hell_le hlam_lt using 1 ; ring_nf;
    norm_num;
  -- Apply the term1_comparison lemma.
  have h_term1 : (ell ^ r * D_r * W ^ 2) ^ (1 / (2 * r - 1 : ℝ)) ≤ (D_r * lam ^ r * W ^ 2) ^ (1 / (2 * r - 1 : ℝ)) := by
    exact Real.rpow_le_rpow ( by positivity ) ( by nlinarith [ show ( ell : ℝ ) ^ r ≤ lam ^ r by gcongr, show ( 0 : ℝ ) < D_r * W ^ 2 by positivity ] ) ( by exact one_div_nonneg.mpr ( by linarith [ show ( r : ℝ ) ≥ 2 by norm_cast ] ) );
  -- Apply the term3_comparison lemma.
  have h_term3 : (ell * D_r1 * W ^ 2 / D_r) ^ (1 / (2 * r : ℝ)) ≤ (D_r1 * lam * W ^ 2 / D_r) ^ (1 / (2 * r : ℝ)) := by
    exact Real.rpow_le_rpow ( by positivity ) ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; nlinarith [ show 0 < D_r1 * W ^ 2 by positivity ] ) ( by positivity );
  rw [ show c₆ = 4 * C₀_const by rfl ];
  norm_num at *;
  nlinarith [ show 0 < C₀_const by exact C₀_pos, show 0 ≤ ( D_r * lam ^ r * W ^ 2 ) ^ ( 2 * r - 1 : ℝ ) ⁻¹ by exact Real.rpow_nonneg ( by exact mul_nonneg ( mul_nonneg hDr.le ( pow_nonneg ( by linarith ) _ ) ) ( sq_nonneg _ ) ) _, show 0 ≤ ( δ * W ^ 2 / ( D_r * lam ^ r ) ) ^ ( r - 1 : ℝ ) ⁻¹ by exact Real.rpow_nonneg ( by exact div_nonneg ( mul_nonneg hδ.le ( sq_nonneg _ ) ) ( mul_nonneg hDr.le ( pow_nonneg ( by linarith ) _ ) ) ) _, show 0 ≤ ( D_r1 * lam * W ^ 2 / D_r ) ^ ( ( r : ℝ ) ⁻¹ * ( 1 / 2 ) ) by exact Real.rpow_nonneg ( by exact div_nonneg ( mul_nonneg ( mul_nonneg hDr1.le ( by linarith ) ) ( sq_nonneg _ ) ) hDr.le ) _ ]

/-
Sum over residue classes.
-/
lemma residue_class_sum_bound
    (r : ℕ) (hr : 2 ≤ r)
    (N : ℝ)
    (W : ℝ) (hW : 1 ≤ W)
    (δ : ℝ) (hδ : 0 < δ)
    (lam : ℝ)
    (hN_lam : lam < N)
    (D_r : ℝ) (hDr : 0 < D_r)
    (D_r1 : ℝ) (hDr1 : 0 < D_r1)
    (f : ℝ → ℝ)
    (hf_smooth : ContDiff ℝ (↑(r + 1) : ℕ∞) f)
    (hf_r_lower : ∀ x ∈ Set.Icc (0 : ℝ) N, D_r / 2 ≤ |iteratedDeriv r f x|)
    (hf_r_upper : ∀ x ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv r f x| ≤ D_r)
    (hf_r1 : ∀ x ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv (r + 1) f x| ≤ D_r1)
    (S : Finset ℤ)
    (hS_sub : ↑S ⊆ ↑(intIcc N))
    (hS_good : ∀ u ∈ S, IsGood f W δ u)
    (ell : ℕ) (hell : 0 < ell) (hell_le : (ell : ℝ) ≤ lam) :
    (S.card : ℝ) <
      C₀_const * N *
        (((ell : ℝ) ^ (r : ℕ) * D_r * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
         (δ * W ^ 2 / ((ell : ℝ) ^ (r : ℕ) * D_r)) ^ (((r : ℝ) - 1)⁻¹) +
         ((ell : ℝ) * D_r1 * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹)) +
      2 * (r : ℝ) * (ell : ℝ) := by
  -- Apply the partition lemma to split S into residue classes modulo ell.
  have h_partition : S.card = ∑ j ∈ Finset.range ell, (S.filter (fun u => u % (ell : ℤ) = ↑j)).card := by
    exact finset_card_eq_sum_residue_classes S ell hell
  -- Apply the lambda_one_case lemma to each residue class.
  have h_lambda_one_case : ∀ j ∈ Finset.range ell, (Finset.card (S.filter (fun u => u % (ell : ℤ) = ↑j))) < C₀_const * ((N - ↑j) / ↑ell) *
    (((ell : ℝ) ^ (r : ℕ) * D_r * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
     (δ * W ^ 2 / ((ell : ℝ) ^ (r : ℕ) * D_r)) ^ (((r : ℝ) - 1)⁻¹) +
     ((ell : ℝ) * D_r1 * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹)) + 2 * (r : ℝ) := by
       intro j hj;
       have := @lambda_one_case r hr ((N - j) / ell) (by
       exact div_pos ( sub_pos.mpr ( by linarith [ show ( j : ℝ ) + 1 ≤ ell by norm_cast; linarith [ Finset.mem_range.mp hj ] ] ) ) ( by positivity )) W hW δ hδ (ell^r * D_r) (by
       positivity) (ell^(r+1) * D_r1) (by
       positivity) (fun x => f (j + ell * x)) (by
       exact hf_smooth.comp ((contDiff_const.add (contDiff_const.mul contDiff_id)).of_le le_top)) (by
       intro x hx;
       convert iteratedDeriv_comp_affine_lower_bound f j ell ( by positivity ) r D_r ( ( N - j ) / ell ) hf_smooth ( fun y hy => hf_r_lower y <| by
         constructor <;> nlinarith [ hy.1, hy.2, show ( ell : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( N - j : ℝ ) ( by positivity : ( ell : ℝ ) ≠ 0 ) ] ) x hx ( by positivity ) using 1) (by
       intro x hx; rw [ iteratedDeriv_comp_affine ] ; norm_num;
       · exact mul_le_mul_of_nonneg_left ( hf_r_upper _ ⟨ by nlinarith [ hx.1, show ( j : ℝ ) + 1 ≤ ell by norm_cast; linarith [ Finset.mem_range.mp hj ] ], by nlinarith [ hx.2, show ( j : ℝ ) + 1 ≤ ell by norm_cast; linarith [ Finset.mem_range.mp hj ], mul_div_cancel₀ ( N - j : ℝ ) ( by positivity : ( ell : ℝ ) ≠ 0 ) ] ⟩ ) ( by positivity );
       · exact hf_smooth.of_le (by exact_mod_cast Nat.le_succ r)) (by
       intro x hx;
       rw [ iteratedDeriv_comp_affine ];
       · rw [ abs_mul, abs_of_nonneg ( by positivity ) ];
         exact mul_le_mul_of_nonneg_left ( hf_r1 _ ⟨ by nlinarith [ hx.1, show ( j : ℝ ) + 1 ≤ ell by norm_cast; linarith [ Finset.mem_range.mp hj ] ], by nlinarith [ hx.2, show ( j : ℝ ) + 1 ≤ ell by norm_cast; linarith [ Finset.mem_range.mp hj ], mul_div_cancel₀ ( N - j : ℝ ) ( by positivity : ( ell : ℝ ) ≠ 0 ) ] ⟩ ) ( by positivity );
       · exact hf_smooth);
       convert this ( Finset.image ( fun u : ℤ => u / ell ) ( S.filter ( fun u : ℤ => u % ell = j ) ) ) _ _ using 1;
       · rw [ Finset.card_image_of_injOn ];
         intro u hu v hv; have := Int.emod_add_mul_ediv u ell; have := Int.emod_add_mul_ediv v ell; aesop;
       · norm_num [ pow_succ', mul_assoc, mul_div_mul_left, hell.ne' ];
         exact Or.inl <| Or.inl <| by rw [ ← mul_div_mul_left _ _ <| pow_ne_zero r <| Nat.cast_ne_zero.mpr hell.ne' ] ; ring_nf;
       · grind +suggestions;
       · simp +zetaDelta at *;
         rintro u x hx hx' rfl; exact good_point_transfer f W δ x ell j hx' ( hS_good x hx ) ;
  have := Finset.sum_lt_sum_of_nonempty ⟨ _, Finset.mem_range.mpr hell ⟩ h_lambda_one_case; simp_all +decide [ Finset.sum_add_distrib, mul_add, mul_assoc, mul_comm, mul_left_comm ] ;
  convert this.trans_le _ using 1 ; norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ; ring_nf ;
  gcongr;
  any_goals exact C₀_pos.le;
  · convert sum_N_sub_j_div_ell_le N ell hell using 1 ; ring_nf;
  · convert sum_N_sub_j_div_ell_le N ell hell using 1 ; ring_nf;
  · convert sum_N_sub_j_div_ell_le N ell hell using 1 ; ring_nf

/-- When `N > λ`, decompose into residue classes modulo `ℓ = ⌊λ⌋`. -/
lemma konyagin_case_large_N
    (r : ℕ) (hr : 2 ≤ r)
    (N : ℝ) (hN : 0 < N)
    (W : ℝ) (hW : 1 ≤ W)
    (δ : ℝ) (hδ : 0 < δ)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hN_lam : lam < N)
    (D_r : ℝ) (hDr : 0 < D_r)
    (D_r1 : ℝ) (hDr1 : 0 < D_r1)
    (f : ℝ → ℝ)
    (hf_smooth : ContDiff ℝ (↑(r + 1) : ℕ∞) f)
    (hf_r_lower : ∀ x ∈ Set.Icc (0 : ℝ) N, D_r / 2 ≤ |iteratedDeriv r f x|)
    (hf_r_upper : ∀ x ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv r f x| ≤ D_r)
    (hf_r1 : ∀ x ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv (r + 1) f x| ≤ D_r1)
    (S : Finset ℤ)
    (hS_sub : ↑S ⊆ ↑(intIcc N))
    (hS_good : ∀ u ∈ S, IsGood f W δ u) :
    (S.card : ℝ) < c₆ * N *
      ((D_r * lam ^ (r : ℕ) * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
       (δ * W ^ 2 / (D_r * lam ^ (r : ℕ))) ^ (((r : ℝ) - 1)⁻¹) +
       (D_r1 * lam * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹)) +
    2 * (r : ℝ) * lam := by
  -- Define ℓ = ⌊λ⌋ as a natural number
  set ell := ⌊lam⌋.toNat with hell_def
  have hlam_floor_pos : 0 < ⌊lam⌋ := Int.floor_pos.mpr hlam
  have hell_pos : 0 < ell := by rw [hell_def]; omega
  have hell_cast_pos : (0 : ℝ) < (ell : ℝ) := Nat.cast_pos.mpr hell_pos
  have hell_eq_floor : (ell : ℤ) = ⌊lam⌋ := by
    rw [hell_def]; exact Int.toNat_of_nonneg (le_of_lt hlam_floor_pos)
  have hell_le_lam : (ell : ℝ) ≤ lam := by
    have : (⌊lam⌋ : ℝ) ≤ lam := Int.floor_le lam
    have : (ell : ℝ) = (⌊lam⌋ : ℝ) := by exact_mod_cast hell_eq_floor
    linarith
  have hlam_lt_2ell : lam < 2 * (ell : ℝ) := by
    have h1 : lam < (⌊lam⌋ : ℝ) + 1 := Int.lt_floor_add_one lam
    have h2 : (ell : ℝ) = (⌊lam⌋ : ℝ) := by exact_mod_cast hell_eq_floor
    have h3 : (ell : ℝ) ≥ 1 := by
      have : (ell : ℤ) ≥ 1 := by omega
      exact_mod_cast this
    linarith
  -- Abbreviate the rpow terms
  set T_ell :=
    ((ell : ℝ) ^ (r : ℕ) * D_r * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
    (δ * W ^ 2 / ((ell : ℝ) ^ (r : ℕ) * D_r)) ^ (((r : ℝ) - 1)⁻¹) +
    ((ell : ℝ) * D_r1 * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹) with hT_ell_def
  set T_lam :=
    (D_r * lam ^ (r : ℕ) * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
    (δ * W ^ 2 / (D_r * lam ^ (r : ℕ))) ^ (((r : ℝ) - 1)⁻¹) +
    (D_r1 * lam * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹) with hT_lam_def
  -- Step 1: |S| < C₀ N T_ell + 2rℓ (from residue class sum bound)
  have hS_bound := residue_class_sum_bound r hr N W hW δ hδ lam hN_lam
    D_r hDr D_r1 hDr1 f hf_smooth hf_r_lower hf_r_upper hf_r1 S hS_sub hS_good
    ell hell_pos hell_le_lam
  -- Step 2: C₀ T_ell ≤ c₆ T_lam (algebraic comparison)
  have hT_compare := algebraic_comparison r hr D_r D_r1 W δ hDr hDr1 hW hδ
    ell lam hell_pos hell_le_lam hlam_lt_2ell
  -- Step 3: 2rℓ ≤ 2rλ
  have h2rell : 2 * (r : ℝ) * (ell : ℝ) ≤ 2 * (r : ℝ) * lam := by
    have : (0 : ℝ) ≤ 2 * (r : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hell_le_lam this
  -- Combine: |S| < C₀ N T_ell + 2rℓ ≤ c₆ N T_lam + 2rλ
  calc (S.card : ℝ)
      < C₀_const * N * T_ell + 2 * (r : ℝ) * (ell : ℝ) := hS_bound
    _ = N * (C₀_const * T_ell) + 2 * (r : ℝ) * (ell : ℝ) := by ring
    _ ≤ N * (c₆ * T_lam) + 2 * (r : ℝ) * lam :=
        add_le_add (mul_le_mul_of_nonneg_left hT_compare (le_of_lt hN)) h2rell
    _ = c₆ * N * T_lam + 2 * (r : ℝ) * lam := by ring

/-- Let `r ≥ 2`, `N > 0`, `W ≥ 1`, `δ > 0`, `λ ≥ 1`, `D_r > 0`, `D_{r+1} > 0`.
    Let `f` be a smooth function satisfying `D_r/2 ≤ |f^{(r)}(x)| ≤ D_r` and
    `|f^{(r+1)}(x)| ≤ D_{r+1}` for `x ∈ [0, N]`. If `S ⊆ [0, N]_ℤ` consists
    of `(f, W, δ)`-good points, then `|S| < c₆ N ((D_r λ^r W²)^{1/(2r-1)} +
    (δW²/(D_r λ^r))^{1/(r-1)} + (D_{r+1} λ W²/D_r)^{1/(2r)}) + 2rλ`. -/
theorem konyagin_thm
    (r : ℕ) (hr : 2 ≤ r)
    (N : ℝ) (hN : 0 < N)
    (W : ℝ) (hW : 1 ≤ W)
    (δ : ℝ) (hδ : 0 < δ)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (D_r : ℝ) (hDr : 0 < D_r)
    (D_r1 : ℝ) (hDr1 : 0 < D_r1)
    (f : ℝ → ℝ)
    (hf_smooth : ContDiff ℝ (↑(r + 1) : ℕ∞) f)
    (hf_r_lower : ∀ x ∈ Set.Icc (0 : ℝ) N, D_r / 2 ≤ |iteratedDeriv r f x|)
    (hf_r_upper : ∀ x ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv r f x| ≤ D_r)
    (hf_r1 : ∀ x ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv (r + 1) f x| ≤ D_r1)
    (S : Finset ℤ)
    (hS_sub : ↑S ⊆ ↑(intIcc N))
    (hS_good : ∀ u ∈ S, IsGood f W δ u) :
    (S.card : ℝ) < c₆ * N *
      ((D_r * lam ^ (r : ℕ) * W ^ 2) ^ ((2 * (r : ℝ) - 1)⁻¹) +
       (δ * W ^ 2 / (D_r * lam ^ (r : ℕ))) ^ (((r : ℝ) - 1)⁻¹) +
       (D_r1 * lam * W ^ 2 / D_r) ^ ((2 * (r : ℝ))⁻¹)) +
    2 * (r : ℝ) * lam := by
  -- Case split: N ≤ λ vs N > λ
  by_cases hN_lam : N ≤ lam
  · -- Case 1: N ≤ λ. |S| ≤ 2rλ and the main term is positive.
    have hle := konyagin_case_small_N r hr N lam hN hlam hN_lam S hS_sub
    have hpos := konyagin_main_term_pos r N W δ lam D_r D_r1 hN hW hδ hlam hDr hDr1
    linarith
  · -- Case 2: N > λ. Decompose into residue classes.
    push_neg at hN_lam
    exact konyagin_case_large_N r hr N hN W hW δ hδ lam hlam hN_lam D_r hDr D_r1 hDr1
      f hf_smooth hf_r_lower hf_r_upper hf_r1 S hS_sub hS_good

end

open scoped BigOperators Nat
open Finset

noncomputable section

/-- A globally smooth, strictly positive function of `x` that equals `k + x`
for `x ≥ -k/4`.  Built by blending `k + x` with the constant `k/2` via a smooth
transition. -/
def smoothDenom (k x : ℝ) : ℝ :=
  k / 2 + (x + k / 2) * Real.smoothTransition ((4 * x + 2 * k) / k)

/-- The globally smooth modification of `f(x) = (-1)^r n / (k + x)`. -/
def fK (n k : ℝ) (r : ℕ) (x : ℝ) : ℝ := ((-1 : ℝ) ^ r * n) / smoothDenom k x

/-
`smoothDenom k` is positive everywhere when `k > 0`.
-/
lemma smoothDenom_pos (k : ℝ) (hk : 0 < k) (x : ℝ) : 0 < smoothDenom k x := by
  unfold smoothDenom;
  by_cases h : x + k / 2 ≥ 0 <;> simp_all +decide;
  · exact add_pos_of_pos_of_nonneg ( half_pos hk ) ( mul_nonneg h ( Real.smoothTransition.nonneg _ ) );
  · rw [ Real.smoothTransition.zero_of_nonpos ] <;> nlinarith [ mul_div_cancel₀ ( 4 * x + 2 * k ) hk.ne' ]

/-
`smoothDenom k x = k + x` for `x ≥ -k/4`.
-/
lemma smoothDenom_eq (k : ℝ) (hk : 0 < k) (x : ℝ) (hx : -k / 4 ≤ x) :
    smoothDenom k x = k + x := by
  unfold smoothDenom; rw [ Real.smoothTransition.one_of_one_le ( by rw [ le_div_iff₀ hk ] ; linarith ) ] ; ring;

/-
`smoothDenom k` is smooth.
-/
lemma smoothDenom_contDiff (k : ℝ) (m : ℕ∞) :
    ContDiff ℝ (m : WithTop ℕ∞) (smoothDenom k) := by
  refine' ContDiff.add contDiff_const _;
  refine' ContDiff.mul ( contDiff_id.add contDiff_const ) _;
  exact ContDiff.comp ( Real.smoothTransition.contDiff ) ( by exact ContDiff.div_const ( by exact ContDiff.add ( contDiff_const.mul contDiff_id ) contDiff_const ) _ )

/-
`fK n k r` is smooth, given `k > 0`.
-/
lemma fK_contDiff (n k : ℝ) (hk : 0 < k) (r : ℕ) (m : ℕ∞) :
    ContDiff ℝ (m : WithTop ℕ∞) (fK n k r) := by
  exact ContDiff.div ( contDiff_const ) ( smoothDenom_contDiff k m ) fun x => ne_of_gt ( smoothDenom_pos k hk x )

/-
The iterated derivatives of `fK` on `[0, ∞)` are given by the explicit formula
for `(-1)^r n / (k + x)`.
-/
lemma iteratedDeriv_fK (n k : ℝ) (hk : 0 < k) (r j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv j (fK n k r) x
      = ((-1 : ℝ) ^ r * n) * ((-1) ^ j * (j ! : ℝ) * (k + x) ^ (-1 - (j : ℤ))) := by
  -- Apply the equality we've shown in the neighborhood to the specific point x.
  have h_eq_at_x : iteratedDeriv j (fK n k r) x = iteratedDeriv j (fun y => (-1 : ℝ) ^ r * n / (k + y)) x := by
    apply Filter.EventuallyEq.iteratedDeriv_eq
    generalize_proofs at *; (
    filter_upwards [ lt_mem_nhds ( show x > -k / 4 by linarith ) ] with y hy using by unfold fK; rw [ smoothDenom_eq k hk y ( by linarith ) ] ;)
  generalize_proofs at *; (
  -- Apply the chain rule to compute the derivative.
  have h_chain : iteratedDeriv j (fun y => (-1 : ℝ) ^ r * n / (k + y)) x = (-1 : ℝ) ^ r * n * iteratedDeriv j (fun y => 1 / (k + y)) x := by
    convert iteratedDeriv_const_mul ( ( -1 ) ^ r * n ) _ using 1 ; norm_num [ div_eq_mul_inv ];
    exact ContDiffAt.inv ( contDiffAt_const.add contDiffAt_id ) ( by linarith )
  generalize_proofs at *; (
  convert h_eq_at_x.trans h_chain using 1
  generalize_proofs at *; (
  -- By definition of $fK$, we know that its $j$-th derivative is given by the formula.
  have h_deriv : iteratedDeriv j (fun y => 1 / (k + y)) x = (-1 : ℝ) ^ j * (Nat.factorial j) * (k + x) ^ (-1 - j : ℤ) := by
    have hs : IsOpen {y : ℝ | (0:ℝ) < y} := isOpen_lt continuous_const continuous_id
    have hmem : k + x ∈ {y : ℝ | (0:ℝ) < y} := by simp; linarith
    have heq := iteratedDerivWithin_of_isOpen (n := j) (f := fun y : ℝ => 1/y) hs hmem
    rw [show (fun y : ℝ => 1 / (k + y)) = (fun z : ℝ => (fun y : ℝ => 1/y) (k + z)) from rfl,
        iteratedDeriv_comp_const_add]
    simp only []
    rw [← heq]
    exact iteratedDerivWithin_one_div j hs hmem
  generalize_proofs at *; (
  grind +splitIndPred))))

/-
Absolute value of the `r`-th derivative of `fK` on `[0, ∞)`.
-/
lemma abs_iteratedDeriv_r (n k : ℝ) (hk : 0 < k) (hn : 0 < n) (r : ℕ) (x : ℝ)
    (hx : 0 ≤ x) :
    |iteratedDeriv r (fK n k r) x| = (n * (r ! : ℝ)) / (k + x) ^ (r + 1) := by
  rw [ iteratedDeriv_fK n k hk r r x hx ] ; norm_num [ abs_mul, abs_div, abs_pow, abs_of_pos hn, abs_of_pos ( add_pos_of_pos_of_nonneg hk hx ) ] ; ring_nf;
  rw [ show ( -1 - r : ℤ ) = - ( r + 1 ) by ring, zpow_neg ] ; norm_cast ; ring;

/-
Absolute value of the `(r+1)`-th derivative of `fK` on `[0, ∞)`.
-/
lemma abs_iteratedDeriv_r1 (n k : ℝ) (hk : 0 < k) (hn : 0 < n) (r : ℕ) (x : ℝ)
    (hx : 0 ≤ x) :
    |iteratedDeriv (r + 1) (fK n k r) x| = (n * ((r + 1)! : ℝ)) / (k + x) ^ (r + 2) := by
  convert abs_iteratedDeriv_r n k hk hn ( r + 1 ) x hx using 1;
  unfold fK;
  norm_num [ pow_succ', div_eq_mul_inv ]

/-
The key ratio inequality: `(1 + u)^{r+1} ≤ 2` when `2 r u ≤ 1`.
-/
lemma key_ratio (r : ℕ) (hr : 2 ≤ r) (u : ℝ) (hu : 0 ≤ u) (hru : 2 * (r : ℝ) * u ≤ 1) :
    (1 + u) ^ (r + 1) ≤ 2 := by
  -- For r ≥ 3, we have u ≤ 1/(2*r) ≤ 1/6, and (1+u)^4 ≤ 2.
  by_cases hr_ge_3 : r ≥ 3;
  · -- Using the exponential bound, we have $(1 + u)^{r+1} \leq \exp(u(r+1))$.
    have h_exp_bound : (1 + u) ^ (r + 1) ≤ Real.exp (u * (r + 1)) := by
      rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ];
      exact Real.exp_le_exp.mpr ( by push_cast; nlinarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 + u ) ] );
    refine le_trans h_exp_bound ?_;
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
    exact le_trans ( by nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) ( Real.log_two_gt_d9.le );
  · interval_cases r ; norm_num at * ; nlinarith [ sq_nonneg u ]

/-
A good-point witness: if `n/(k+u)` is close to an integer, then `u` is
`(fK, 1, δ)`-good.
-/
lemma isGood_fK (n k δ : ℝ) (hk : 0 < k) (r : ℕ) (u : ℤ) (hu : 0 ≤ u)
    (hdist : |(n : ℝ) / (k + (u : ℝ)) - round ((n : ℝ) / (k + (u : ℝ)))| < δ) :
    IsGood (fK n k r) 1 δ u := by
  refine' ⟨ _, _ ⟩;
  exact ( -1 ) ^ r * round ( n / ( k + u ) );
  refine' ⟨ 1, _, _, _ ⟩ <;> norm_num [ fK, smoothDenom_eq _ hk _ _ ];
  convert hdist using 1 ; rw [ smoothDenom_eq _ hk _ ( by linarith [ show ( u : ℝ ) ≥ 0 by positivity ] ) ] ; ring_nf;
  norm_num [ ← sub_mul, abs_mul ]

/-
The bound `(k + k^θ)^{r+1} ≤ 2 k^{r+1}`, which makes the lower and upper bounds
on `|f^{(r)}|` differ by a factor of at most 2.
-/
lemma KplusN_pow_le (k : ℝ) (hk : 0 < k) (theta : ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hr_le : (r : ℝ) ≤ (1 / 2) * k ^ (1 - theta)) :
    (k + k ^ theta) ^ (r + 1) ≤ 2 * k ^ (r + 1) := by
  -- Note that $k + k^\theta = k * (1 + k^{\theta-1})$.
  have h_factor : k + k ^ theta = k * (1 + k ^ (theta - 1)) := by
    rw [ Real.rpow_sub hk, Real.rpow_one ] ; ring_nf ; norm_num [ hk.ne' ];
    rw [ mul_right_comm, mul_inv_cancel₀ hk.ne', one_mul ];
  rw [ h_factor, mul_pow ];
  rw [ mul_comm ];
  exact mul_le_mul_of_nonneg_right ( key_ratio r hr _ ( Real.rpow_nonneg hk.le _ ) ( by rw [ show ( 1 - theta : ℝ ) = - ( theta - 1 ) by ring, Real.rpow_neg hk.le ] at hr_le; nlinarith [ Real.rpow_pos_of_pos hk ( theta - 1 ), mul_inv_cancel₀ ( ne_of_gt ( Real.rpow_pos_of_pos hk ( theta - 1 ) ) ) ] ) ) ( by positivity )

lemma nat_k_ge_one (theta : ℝ) (htheta1 : theta < 1) (k r : ℕ) (hr2 : 2 ≤ r)
    (hr_le : (r : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (1 - theta)) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.cast_zero] at hr_le
    rw [Real.zero_rpow (by linarith)] at hr_le
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    linarith
  · exact hk

/-
We apply `konyagin_thm` to the function `f(x) = (-1)^r n / (k + x)` on the
interval `[0, k^θ]` with `W = 1`.

The number of integers `m ∈ (k, k + k^θ)` with `‖n/m‖ < 1/k^{1-θ}` is bounded by
`c₆·k^θ·((n·r!·λ^r/k^{r+1})^{1/(2r-1)} + (k^{r+θ}/(n·r!·λ^r))^{1/(r-1)}
  + ((r+1)·λ/k)^{1/(2r)}) + 2·r·λ`.
-/
theorem konyagin_application
    (lam theta : ℝ) (hlam : 1 ≤ lam) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (n : ℤ) (k r : ℕ) (hkn : (k : ℤ) < n) (hr2 : 2 ≤ r)
    (hr_le : (r : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (1 - theta)) :
    (((Finset.Ioo (k : ℤ) ((k : ℤ) + ⌊(k : ℝ) ^ theta⌋ + 2)).filter
        (fun m : ℤ => (m : ℝ) < (k : ℝ) + (k : ℝ) ^ theta ∧
          |(n : ℝ) / (m : ℝ) - round ((n : ℝ) / (m : ℝ))| < 1 / (k : ℝ) ^ (1 - theta))).card : ℝ)
      < c₆ * (k : ℝ) ^ theta *
          (((n : ℝ) * (r ! : ℝ) * lam ^ r / (k : ℝ) ^ (r + 1)) ^ ((2 * (r : ℝ) - 1)⁻¹) +
           ((k : ℝ) ^ ((r : ℝ) + theta) / ((n : ℝ) * (r ! : ℝ) * lam ^ r)) ^ (((r : ℝ) - 1)⁻¹) +
           (((r : ℝ) + 1) * lam / (k : ℝ)) ^ ((2 * (r : ℝ))⁻¹)) +
        2 * (r : ℝ) * lam := by
  have hk : (1 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast nat_k_ge_one theta htheta1 k r hr2 hr_le
  have hr_leK : (r : ℝ) ≤ (1 / 2) * ((k : ℤ) : ℝ) ^ (1 - theta) := by
    push_cast; exact hr_le
  rw [show (k : ℝ) = ((k : ℤ) : ℝ) from by norm_cast]
  set K : ℤ := (k : ℤ) with hKdef
  clear_value K
  clear hKdef
  -- Apply the Konyagin theorem with the given parameters.
  have hh := @konyagin_thm r hr2 (K ^ theta) (by
  positivity) 1 (by
  norm_num) (1 / K ^ (1 - theta)) (by
  positivity) lam hlam (n * (r ! : ℝ) / K ^ (r + 1)) (by
  exact div_pos ( mul_pos ( by norm_cast; linarith ) ( by positivity ) ) ( by positivity )) (n * ((r + 1)! : ℝ) / K ^ (r + 2)) (by
  exact div_pos ( mul_pos ( by norm_cast; linarith ) ( by positivity ) ) ( by positivity )) (fK n K r) (by
  exact fK_contDiff _ _ ( by positivity ) _ _) (by
  intro x hx
  have h_abs : |iteratedDeriv r (fK n K r) x| = (n * (r ! : ℝ)) / (K + x) ^ (r + 1) := by
    convert abs_iteratedDeriv_r n K ( by positivity ) ( by norm_cast; linarith ) r x hx.1 using 1
  rw [h_abs];
  rw [ div_div, div_le_div_iff₀ ] <;> try positivity;
  · have := KplusN_pow_le K (by positivity) theta r hr2 hr_leK; simp_all +decide [ mul_assoc, mul_comm ] ;
    exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( le_trans ( pow_le_pow_left₀ ( by linarith [ show ( K : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith ) _ ) this ) ( by positivity ) ) ( by norm_cast; linarith );
  · exact pow_pos ( by linarith [ hx.1, show ( K : ℝ ) ≥ 1 by norm_cast ] ) _) (by
  intro x hx
  have h_abs : |iteratedDeriv r (fK n K r) x| = (n * (r ! : ℝ)) / (K + x) ^ (r + 1) := by
    convert abs_iteratedDeriv_r n K ( by positivity ) ( by norm_cast; linarith ) r x hx.1 using 1;
  exact h_abs.symm ▸ div_le_div_of_nonneg_left ( by exact mul_nonneg ( by norm_cast; linarith ) ( by positivity ) ) ( by positivity ) ( by exact pow_le_pow_left₀ ( by positivity ) ( by linarith [ hx.1 ] ) _ )) (by
  intro x hx
  have h_abs : |iteratedDeriv (r + 1) (fK n K r) x| = n * ((r + 1)! : ℝ) / (K + x) ^ (r + 2) := by
    convert abs_iteratedDeriv_r1 n K ( by positivity ) ( by norm_cast; linarith ) r x hx.1 using 1;
  exact h_abs.symm ▸ div_le_div_of_nonneg_left ( by exact mul_nonneg ( by norm_cast; linarith ) ( by positivity ) ) ( by positivity ) ( by exact pow_le_pow_left₀ ( by positivity ) ( by linarith [ hx.1 ] ) _ ));
  convert hh ( Finset.image ( fun m : ℤ => m - K ) ( Finset.filter ( fun m : ℤ => ( m : ℝ ) < K + K ^ theta ∧ |( n : ℝ ) / m - round ( n / m : ℝ )| < 1 / K ^ ( 1 - theta ) ) ( Finset.Ioo K ( K + ⌊ ( K : ℝ ) ^ theta⌋ + 2 ) ) ) ) _ _ using 1 <;> norm_num [ Finset.card_image_of_injOn ];
  · field_simp;
    refine Or.inl <| congr_arg₂ _ ( congr_arg₂ _ rfl ?_ ) ?_ <;> norm_num [ Nat.factorial_succ ] ; ring_nf;
    · norm_num [ Real.rpow_add ( by positivity : 0 < ( K : ℝ ) ), Real.rpow_sub ( by positivity : 0 < ( K : ℝ ) ) ] ; ring_nf;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hk ) ];
    · congr 1 ; rw [ div_eq_div_iff ] <;> ring_nf <;> norm_cast <;> norm_num [ Nat.factorial_ne_zero, show K ≠ 0 by linarith, show n ≠ 0 by linarith ];
  · norm_num [ Finset.subset_iff, intIcc ];
    rintro x y hy₁ hy₂ hy₃ hy₄ rfl; exact ⟨ by linarith, by exact Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( ( K : ℝ ) ^ theta ), Int.lt_floor_add_one ( ( K : ℝ ) ^ theta ) ] ⟩ ;
  · rintro u x hx₁ hx₂ hx₃ hx₄ rfl; exact isGood_fK n K ( ( K ^ ( 1 - theta ) ) ⁻¹ ) ( by positivity ) r ( x - K ) ( by linarith ) ( by simpa using hx₄ ) ;

/-
**Pigeonhole.** If the number of "bad" integers in `(k, k + k^θ)` is strictly
less than the number of primes in `(k, k + k^θ)`, then there is a prime
`p ∈ (k, k + k^θ)` dividing `P`.
-/
lemma exists_far_prime (k : ℕ) (n : ℤ) (hk1 : 1 ≤ k)
    (hcount : ((badSet k n).card : ℝ) < (primeCard (k : ℝ) ((k : ℝ) + (k : ℝ) ^ theta) : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) < p ∧ (p : ℝ) < (k : ℝ) + (k : ℝ) ^ theta ∧
      (p : ℤ) ∣ Pprod k n := by
  norm_cast at *;
  contrapose! hcount;
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact Finset.image ( fun m : ℤ => m ) ( Finset.filter ( fun m : ℤ => ( m : ℝ ) < ( k : ℝ ) + ( k : ℝ ) ^ theta ∧ |( n : ℝ ) / m - round ( ( n : ℝ ) / m )| < 1 / ( k : ℝ ) ^ ( 1 - theta ) ) ( Finset.Ioo ( k : ℤ ) ( ( k : ℤ ) + ⌊ ( k : ℝ ) ^ theta⌋ + 2 ) ) );
  · intro p hp; simp_all +decide ;
    refine' ⟨ _, _ ⟩;
    · linarith [ show ⌈ ( k : ℝ ) ^ theta⌉ ≤ ⌊ ( k : ℝ ) ^ theta⌋ + 1 by exact Int.ceil_le_floor_add_one _ ];
    · exact Classical.not_not.1 fun h => hcount ( Int.natAbs p ) hp.2.2.1 ( by linarith [ abs_of_pos hp.2.1 ] ) ( by simpa [ abs_of_pos hp.2.1 ] using hp.2.2.2.2 ) ( by simpa [ abs_of_pos hp.2.1 ] using dvd_from_far k n ( Int.natAbs p ) hk1 ( by linarith [ abs_of_pos hp.2.1 ] ) ( by simpa [ abs_of_pos hp.2.1 ] using hp.2.2.2.1 ) ( by simpa [ abs_of_pos hp.2.1 ] using hp.2.2.2.2 ) ( by simpa [ abs_of_pos hp.2.1 ] using h ) );
  · unfold badSet; aesop;

/-
Core asymptotic fact: `(log x)^b · x^{-c} → 0` for `c > 0`.
-/
lemma tendsto_log_rpow_mul_rpow_neg (b c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun x : ℝ => (Real.log x) ^ b * x ^ (-c)) Filter.atTop (nhds 0) := by
  -- Use the fact that `Real.log x ^ b` is little-o of `x ^ c` as `x` tends to infinity.
  have h_log : (fun x : ℝ => Real.log x ^ b) =o[Filter.atTop] (fun x : ℝ => x ^ c) :=
    isLittleO_log_rpow_rpow_atTop b hc
  convert h_log.tendsto_div_nhds_zero.congr' _ using 1;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ div_eq_mul_inv, Real.rpow_neg hx.le ] ;

/-
A sub-`tt` power times any log-power is eventually dominated by
`C · k^tt / log k`, for `C > 0` and `α < tt`.
-/
lemma poly_log_lt (A α β tt : ℝ) (hα : α < tt) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ k : ℕ in Filter.atTop,
      A * (k : ℝ) ^ α * (Real.log k) ^ β ≤ C * (k : ℝ) ^ tt / Real.log k := by
  -- Let's choose any $C > 0$ and derive a contradiction.
  have h_lim : Filter.Tendsto (fun k : ℕ => (A * (k : ℝ) ^ α * (Real.log k) ^ β) / ((k : ℝ) ^ tt / (Real.log k))) Filter.atTop (nhds 0) := by
    -- Simplify the expression inside the limit.
    suffices h_simp : Filter.Tendsto (fun k : ℕ => A * (Real.log k) ^ (β + 1) * (k : ℝ) ^ (α - tt)) Filter.atTop (nhds 0) by
      refine h_simp.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with k hk ; rw [ Real.rpow_sub ( by positivity ) ] ; ring_nf;
      rw [ Real.rpow_add ( Real.log_pos ( Nat.one_lt_cast.mpr hk ) ), Real.rpow_one ] ; norm_num ; ring;
    have := @tendsto_log_rpow_mul_rpow_neg ( β + 1 ) ( tt - α ) ?_;
    · convert this.const_mul A |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop using 2 <;> norm_num ; ring;
    · linarith;
  filter_upwards [ h_lim.eventually ( gt_mem_nhds hC ), Filter.eventually_gt_atTop 1 ] with k hk₁ hk₂;
  rw [ div_lt_iff₀ ( div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hk₂.le ) _ ) ( Real.log_pos ( Nat.one_lt_cast.mpr hk₂ ) ) ) ] at hk₁ ; ring_nf at hk₁ ⊢ ; linarith

/-
The `θ`-power times `(log k)^{-2}` is eventually dominated by `C · k^tt / log k`.
-/
lemma poly_log_lt_eq (A tt : ℝ) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ k : ℕ in Filter.atTop,
      A * (k : ℝ) ^ tt * (Real.log k) ^ (-(2 : ℝ)) ≤ C * (k : ℝ) ^ tt / Real.log k := by
  -- We'll use that $A \leq C \cdot \log k$ for sufficiently large $k$.
  have h_log_bound : ∀ᶠ k : ℕ in Filter.atTop, A ≤ C * Real.log k := by
    exact Filter.eventually_atTop.mpr ⟨ ⌈Real.exp ( A / C ) ⌉₊ + 1, fun k hk => by nlinarith [ Nat.le_ceil ( Real.exp ( A / C ) ), Real.log_exp ( A / C ), Real.log_le_log ( by positivity ) ( show ( k :ℝ ) ≥ Real.exp ( A / C ) by exact le_of_lt ( Nat.lt_of_ceil_lt hk ) ), mul_div_cancel₀ A hC.ne' ] ⟩;
  filter_upwards [ h_log_bound, Filter.eventually_gt_atTop 1 ] with k hk₁ hk₂;
  norm_cast ; norm_num ; ring_nf ; norm_num;
  convert mul_le_mul_of_nonneg_right hk₁ ( show 0 ≤ ( k : ℝ ) ^ tt * ( Real.log k ^ 2 ) ⁻¹ by positivity ) using 1 ; ring;
  grind

/-
The `tt`-power times `(log k)^β` with `β < -1` is eventually dominated by
`C · k^tt / log k`.
-/
lemma poly_log_lt_logpow (A tt β : ℝ) (hβ : β < -1) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ k : ℕ in Filter.atTop,
      A * (k : ℝ) ^ tt * (Real.log k) ^ β ≤ C * (k : ℝ) ^ tt / Real.log k := by
  have h_log_pow : Filter.Tendsto (fun k : ℕ => A * (Real.log k) ^ (β + 1)) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop ( by linarith : 0 < - ( β + 1 ) ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
  filter_upwards [ h_log_pow.eventually ( gt_mem_nhds hC ), Filter.eventually_gt_atTop 1 ] with k hk₁ hk₂ ; rw [ le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr hk₂ ) ] ; ring_nf at *;
  convert mul_le_mul_of_nonneg_left hk₁.le ( Real.rpow_nonneg ( Nat.cast_nonneg k ) tt ) using 1 ; rw [ show ( 1 + β ) = β + 1 by ring, Real.rpow_add ( Real.log_pos <| Nat.one_lt_cast.mpr hk₂ ), Real.rpow_one ] ; ring

/-
If the count of primes in `(a, b)` is positive, there is a prime in `(a, b)`.
-/
lemma exists_prime_of_primeCard_pos (a b : ℝ) (h : 0 < primeCard a b) :
    ∃ p : ℕ, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) < b := by
  obtain ⟨ p, hp ⟩ := Finset.card_pos.mp h;
  cases p <;> aesop

/-
Monotone-difference bound for `primeCard`: extending the upper endpoint from `b`
to `c ≥ b` adds at most the number of integers in `[b, c)`, which is at most
`c - b + 1`.
-/
lemma primeCard_le_add (a b c : ℝ) (hbc : b ≤ c) :
    (primeCard a c : ℝ) ≤ (primeCard a b : ℝ) + (c - b + 1) := by
  -- Let S(t) := (Finset.Ioo ⌊a⌋ ⌈t⌉).filter (fun p : ℤ => 0 < p ∧ p.natAbs.Prime ∧ a < (p:ℝ) ∧ (p:ℝ) < t).
  set S := fun t : ℝ => Finset.filter (fun p : ℤ => 0 < p ∧ p.natAbs.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) < t) (Finset.Ioo ⌊a⌋ ⌈t⌉);
  -- Show `S(c) ⊆ S(b) ∪ Finset.Ico ⌈b⌉ ⌈c⌉`.
  have h_subset : S c ⊆ S b ∪ Finset.Ico ⌈b⌉ ⌈c⌉ := by
    intro p hp; by_cases h : ( p : ℝ ) < b <;> simp_all +decide ;
    · exact Or.inl <| Finset.mem_filter.mpr ⟨ Finset.mem_Ioo.mpr ⟨ Finset.mem_Ioo.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1, Int.lt_ceil.mpr h ⟩, Finset.mem_filter.mp hp |>.2.1, Finset.mem_filter.mp hp |>.2.2.1, Finset.mem_filter.mp hp |>.2.2.2.1, h ⟩;
    · exact Or.inr ⟨ Int.ceil_le.mpr h, Finset.mem_Ioo.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ⟩;
  -- Thus by `Finset.card_le_card` and `Finset.card_union_le`, `S(c).card ≤ S(b).card + (Finset.Ico ⌈b⌉ ⌈c⌉).card`.
  have h_card : (S c).card ≤ (S b).card + (Finset.Ico ⌈b⌉ ⌈c⌉).card := by
    exact le_trans ( Finset.card_le_card h_subset ) ( Finset.card_union_le _ _ );
  refine' le_trans ( Nat.cast_le.mpr h_card ) _;
  simp +zetaDelta at *;
  exact add_le_add ( by rfl ) ( by linarith [ Int.ceil_lt_add_one c, Int.le_ceil b, show ( Int.toNat ( ⌈c⌉ - ⌈b⌉ ) : ℝ ) ≤ ⌈c⌉ - ⌈b⌉ by exact_mod_cast Int.toNat_of_nonneg ( sub_nonneg.mpr <| Int.ceil_mono hbc ) |> le_of_eq ] )

/-
Algebraic excess bound: for `k ≥ 1` and `k ≤ N ≤ k + 2 k^θ + 1`, the difference
`N^θ - k^θ` is at most `3^θ · k^{θ²}` (using subadditivity of `x ↦ x^θ`).
-/
lemma excess_le (k N : ℕ) (hk : 1 ≤ k) (hkN : (k : ℝ) ≤ (N : ℝ))
    (hNk : (N : ℝ) ≤ (k : ℝ) + 2 * (k : ℝ) ^ theta + 1) :
    (N : ℝ) ^ theta - (k : ℝ) ^ theta ≤ (3 : ℝ) ^ theta * (k : ℝ) ^ (theta * theta) := by
  -- Subexcess bound: `(N:ℝ)^theta - (k:ℝ)^theta ≤ ((N:ℝ) - k)^theta`
  have h_subex : (N : ℝ) ^ theta - (k : ℝ) ^ theta ≤ ((N : ℝ) - k) ^ theta := by
    rw [ sub_le_iff_le_add' ];
    convert Real.rpow_add_le_add_rpow _ _ _ _ using 1 <;> norm_num;
    · exact_mod_cast hkN;
    · exact div_nonneg ( by norm_num ) ( by norm_num );
    · exact le_of_lt theta_lt_one;
  refine le_trans h_subex ?_;
  refine' le_trans ( Real.rpow_le_rpow ( sub_nonneg.mpr hkN ) ( show ( N : ℝ ) - k ≤ 3 * ( k : ℝ ) ^ theta by linarith [ show ( k : ℝ ) ^ theta ≥ 1 by exact Real.one_le_rpow ( by norm_cast ) ( by norm_num [ theta ] ) ] ) ( by norm_num [ theta ] ) ) _;
  rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ) ]

end

noncomputable section

open scoped BigOperators
open Finset Filter
open scoped BigOperators Nat

/-
For large `k`, the BHP prime count `C N^θ / log N` strictly exceeds the
"excess width" `N^θ - k^θ + 2`, uniformly over `N` with `k ≤ N ≤ k + 2 k^θ + 1`.
-/
lemma count_beats_excess (C : ℝ) (hC : 0 < C) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ N : ℕ, (k : ℝ) ≤ (N : ℝ) →
      (N : ℝ) ≤ (k : ℝ) + 2 * (k : ℝ) ^ theta + 1 →
      (N : ℝ) ^ theta - (k : ℝ) ^ theta + 2 < C * (N : ℝ) ^ theta / Real.log N := by
  -- Step 1: produce a purely-k bound and then specialize to N.
  have step1 : ∀ᶠ k : ℕ in atTop, (3 : ℝ) ^ theta * (k : ℝ) ^ (theta * theta) + 3 ≤ (C / 2) * (k : ℝ) ^ theta / Real.log k := by
    -- Apply `poly_log_lt` to each term separately.
    have hA : ∀ᶠ k : ℕ in Filter.atTop, (3 : ℝ) ^ theta * (k : ℝ) ^ (theta * theta) ≤ (C / 4) * (k : ℝ) ^ theta / Real.log k := by
      have := poly_log_lt ( ( 3 : ℝ ) ^ theta ) ( theta * theta ) 0 theta ( by nlinarith [ show 0 < theta by exact theta_pos, show theta < 1 by exact theta_lt_one ] ) ( C / 4 ) ( by positivity );
      aesop
    have hB : ∀ᶠ k : ℕ in Filter.atTop, 3 ≤ (C / 4) * (k : ℝ) ^ theta / Real.log k := by
      have := poly_log_lt ( 3 : ℝ ) 0 0 theta ( by norm_num [ theta ] ) ( C / 4 ) ( by positivity ) ; aesop;
    filter_upwards [ hA, hB ] with k hk₁ hk₂ using by ring_nf at *; linarith;
  -- Step 2: Filter_upwards on [step1, eventually_ge_atTop 4] with k, hkA, hk4.
  filter_upwards [step1, Filter.eventually_ge_atTop 4] with k hkA hk4;
  intro N hkN hNk
  have hN_le_4k : (N : ℝ) ≤ 4 * (k : ℝ) := by
    linarith [ show ( k : ℝ ) ^ theta ≤ k by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) <| show theta ≤ 1 by exact le_of_lt <| theta_lt_one ) <| by norm_num, show ( k : ℝ ) ≥ 4 by norm_cast ]
  have h_logN_le_2logk : Real.log (N : ℝ) ≤ 2 * Real.log (k : ℝ) := by
    erw [ ← Real.log_pow ] ; gcongr ; norm_cast at *;
    · linarith;
    · norm_cast at *; nlinarith;
  have h_logN_pos : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos <| by norm_cast at *; linarith;
  have h_exp_bound : (N : ℝ) ^ theta - (k : ℝ) ^ theta + 2 < (C / 2) * (k : ℝ) ^ theta / Real.log k := by
    have h_exp_bound : (N : ℝ) ^ theta - (k : ℝ) ^ theta ≤ (3 : ℝ) ^ theta * (k : ℝ) ^ (theta * theta) := by
      apply excess_le k N (by linarith) hkN hNk;
    linarith
  have h_rhs_bound : (C / 2) * (k : ℝ) ^ theta / Real.log k ≤ C * (N : ℝ) ^ theta / Real.log N := by
    rw [ div_le_div_iff₀ ] <;> try positivity;
    · have h_rhs_bound : (k : ℝ) ^ theta * Real.log N ≤ 2 * (N : ℝ) ^ theta * Real.log k := by
        have h_rhs_bound : (k : ℝ) ^ theta ≤ (N : ℝ) ^ theta := by
          exact Real.rpow_le_rpow ( by positivity ) hkN ( by exact div_nonneg ( by norm_num ) ( by norm_num ) );
        nlinarith [ Real.rpow_pos_of_pos ( by positivity : 0 < ( k : ℝ ) ) theta ];
      nlinarith;
    · exact Real.log_pos <| by norm_cast; linarith;
  linarith [h_exp_bound, h_rhs_bound]

/-
Existence of a prime in a length-`k^θ` window with base in `[k, k + 2 k^θ]`,
derived from `bhp`.  Although `bhp` only guarantees primes in the base-`k`
window `(k, k + k^θ)`, applying it at `N := ⌈a⌉` gives `≥ C N^θ / log N` primes
in `(N, N + N^θ)`; the excess width `N^θ - k^θ` is smaller than this count, so a
prime survives in `(a, a + k^θ)`.
-/
lemma exists_prime_in_window : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a : ℝ,
    (k : ℝ) ≤ a → a ≤ (k : ℝ) + 2 * (k : ℝ) ^ theta →
    ∃ p : ℕ, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) < a + (k : ℝ) ^ theta := by
  obtain ⟨ C, hC, k₀, hk₀ ⟩ := bhp;
  -- Choose `k₀' := max (max k₀ k₁) 2`.
  obtain ⟨ k₁, hk₁ ⟩ := Filter.eventually_atTop.mp (count_beats_excess C hC)
  use max (max k₀ k₁) 2;
  intros k hk a ha₁ ha₂
  set N := ⌈a⌉₊ with hN
  have hN₁ : (k : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast ha₁.trans <| Nat.le_ceil _
  have hN₂ : (N : ℝ) ≤ (k : ℝ) + 2 * (k : ℝ) ^ theta + 1 := by
    exact le_trans ( Nat.ceil_lt_add_one ( by linarith ) |> le_of_lt ) ( by linarith )
  have hN₃ : (N : ℝ) < a + 1 := by
    exact Nat.ceil_lt_add_one ( by linarith [ show ( k : ℝ ) ≥ 2 by norm_cast; linarith [ le_max_right ( max k₀ k₁ ) 2 ] ] )
  have hN₄ : (k : ℝ) ≤ N := by
    exact_mod_cast hN₁
  have hN₅ : (N : ℝ) ≤ (k : ℝ) + 2 * (k : ℝ) ^ theta + 1 := by
    convert hN₂ using 1;
  -- Apply `hk₀` to get `bhpN : C*(N:ℝ)^theta/Real.log N ≤ primeCard (N:ℝ) ((N:ℝ)+(N:ℝ)^theta)`.
  have h_bhpN : C * (N : ℝ) ^ theta / Real.log N ≤ primeCard (N : ℝ) ((N : ℝ) + (N : ℝ) ^ theta) := by
    exact hk₀ N ( by norm_cast at *; linarith [ Nat.le_max_left ( max k₀ k₁ ) 2, Nat.le_max_right ( max k₀ k₁ ) 2, Nat.le_max_left k₀ k₁, Nat.le_max_right k₀ k₁ ] );
  -- Apply `primeCard_le_add` to bound the prime count in `(N, a + k^θ)`.
  have h_primeCard_le_add : primeCard (N : ℝ) (a + (k : ℝ) ^ theta) ≥ primeCard (N : ℝ) ((N : ℝ) + (N : ℝ) ^ theta) - ((N : ℝ) ^ theta - (k : ℝ) ^ theta + 2) := by
    have h_primeCard_le_add : primeCard (N : ℝ) ((N : ℝ) + (N : ℝ) ^ theta) ≤ primeCard (N : ℝ) (a + (k : ℝ) ^ theta) + ((N : ℝ) + (N : ℝ) ^ theta - (a + (k : ℝ) ^ theta) + 1) := by
      convert primeCard_le_add ( N : ℝ ) ( a + ( k : ℝ ) ^ theta ) ( N + ( N : ℝ ) ^ theta ) _ using 1;
      exact add_le_add ( Nat.le_ceil _ ) ( Real.rpow_le_rpow ( by linarith ) ( by linarith ) ( by exact div_nonneg ( by norm_num ) ( by norm_num ) ) );
    linarith;
  -- Therefore, `primeCard (N:ℝ) (a + k^θ) > 0`.
  have h_primeCard_pos : 0 < primeCard (N : ℝ) (a + (k : ℝ) ^ theta) := by
    exact_mod_cast ( by linarith [ hk₁ k ( by linarith [ le_max_left ( max k₀ k₁ ) 2, le_max_right ( max k₀ k₁ ) 2, le_max_left k₀ k₁, le_max_right k₀ k₁ ] ) N hN₄ hN₅ ] : ( 0 : ℝ ) < primeCard ( N : ℝ ) ( a + k ^ theta ) );
  exact exists_prime_of_primeCard_pos _ _ h_primeCard_pos |> fun ⟨ p, hp₁, hp₂, hp₃ ⟩ => ⟨ p, hp₁, by linarith [ Nat.le_ceil a, show ( p : ℝ ) ≥ N by exact_mod_cast hp₂.le ], hp₃ ⟩

/-
**Small `n`:** `2k < n ≤ ½ k^{2-θ}`.
-/
lemma case_small : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ,
    2 * (k : ℤ) < n → (n : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (2 - theta) →
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) < p ∧ (p : ℝ) < (k : ℝ) + 3 * (k : ℝ) ^ theta ∧
      (p : ℤ) ∣ Pprod k n := by
  -- Set `k₀ := max kw 2`. Intro `k`, `hk`, `n`, `hn1 : 2k < n`, `hn2 : n ≤ ½ k^{2-θ}`.
  obtain ⟨kw, hw⟩ := exists_prime_in_window
  use max kw 2;
  intro k hk n hn1 hn2
  set m := (n - 1).natAbs / k
  have hm : (m : ℤ) * k ≤ n - 1 ∧ n - 1 < ((m + 1) : ℤ) * k := by
    norm_num +zetaDelta at *;
    constructor <;> nlinarith [ Int.mul_ediv_add_emod ( |n - 1| ) k, Int.emod_nonneg ( |n - 1| ) ( by linarith : ( k : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( |n - 1| ) ( by linarith : ( k : ℤ ) > 0 ), abs_of_nonneg ( by linarith : 0 ≤ n - 1 ) ]
  have hm_ge2 : 2 ≤ m := by
    exact Nat.le_div_iff_mul_le ( by linarith [ le_max_right kw 2 ] ) |>.2 ( by cases abs_cases ( n - 1 ) <;> nlinarith [ le_max_right kw 2 ] )
  have hm_lt : (m : ℝ) < (1 / 2) * (k : ℝ) ^ (1 - theta) := by
    rw [ show ( 2 - theta : ℝ ) = 1 - theta + 1 by ring, Real.rpow_add ] at * <;> norm_num at *;
    · nlinarith [ ( by norm_cast : ( 2 : ℝ ) * k < n ), ( by norm_cast : ( m : ℝ ) * k < n ∧ n ≤ ( m + 1 ) * k ) ];
    · linarith
  have hkey : (2 * (m : ℝ) - 1) * (k : ℝ) ^ theta < (k : ℝ) := by
    have hkey : (2 * (m : ℝ) - 1) * (k : ℝ) ^ theta < (k : ℝ) ^ (1 - theta) * (k : ℝ) ^ theta := by
      exact mul_lt_mul_of_pos_right ( by linarith ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ Nat.le_max_right kw 2 ] ) ) _ );
    convert hkey using 1 ; rw [ ← Real.rpow_add' ] <;> norm_num;
  by_cases h_case : (n : ℝ) < (m : ℝ) * k + (m : ℝ) * (k : ℝ) ^ theta;
  · -- Apply `hw` to obtain a prime `p` in the interval `(a, a + k^θ)`.
    obtain ⟨p, hp_prime, hp_bounds⟩ := hw k (by
    linarith [ Nat.le_max_left kw 2, Nat.le_max_right kw 2 ]) (k + (m : ℝ) / (m - 1) * (k : ℝ) ^ theta) (by
    exact le_add_of_nonneg_right ( mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) )) (by
    gcongr;
    rw [ div_le_iff₀ ] <;> linarith [ show ( m : ℝ ) ≥ 2 by norm_cast ]);
    refine' ⟨ p, hp_prime, _, _, _ ⟩;
    · exact lt_of_le_of_lt ( le_add_of_nonneg_right <| mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) <| Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) hp_bounds.1;
    · refine' lt_of_lt_of_le hp_bounds.2 _;
      rw [ div_mul_eq_mul_div, add_div', div_add', div_le_iff₀ ] <;> nlinarith only [ show ( m : ℝ ) ≥ 2 by norm_cast, show ( k : ℝ ) ^ theta > 0 by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith [ Nat.le_max_right kw 2 ] ) _, hkey ];
    · apply dvd_Pprod_of_mem k n p ((m - 1) * p);
      · rw [ ← @Int.cast_lt ℝ ] ; push_cast ; nlinarith [ show ( m : ℝ ) ≥ 2 by norm_cast, show ( k : ℝ ) ≥ 2 by norm_cast; linarith [ Nat.le_max_right kw 2 ], Real.rpow_pos_of_pos ( show ( k : ℝ ) > 0 by norm_cast; linarith [ Nat.le_max_right kw 2 ] ) theta, mul_div_cancel₀ ( ( m : ℝ ) : ℝ ) ( show ( m - 1 : ℝ ) ≠ 0 by linarith [ show ( m : ℝ ) ≥ 2 by norm_cast ] ) ];
      · rcases m with ( _ | _ | m ) <;> norm_num at *;
        rw [ ← @Int.cast_lt ℝ ] at * ; push_cast at * ; nlinarith [ mul_div_cancel₀ ( ( m : ℝ ) + 1 + 1 ) ( by linarith : ( m : ℝ ) + 1 ≠ 0 ) ];
      · exact dvd_mul_left _ _;
  · obtain ⟨p, hp_prime, hp_bounds⟩ : ∃ p : ℕ, p.Prime ∧ (k : ℝ) < p ∧ p < (k : ℝ) + (k : ℝ) ^ theta := by
      exact hw k ( le_trans ( le_max_left _ _ ) hk ) k ( by norm_num ) ( by linarith [ Real.rpow_nonneg ( Nat.cast_nonneg k ) theta ] );
    refine' ⟨ p, hp_prime, hp_bounds.1, _, _ ⟩;
    · grind +splitIndPred;
    · apply dvd_Pprod_of_mem k n p ((m : ℤ) * p) (by
      nlinarith [ show ( m : ℤ ) ≥ 2 by norm_cast, show ( p : ℤ ) ≥ k + 1 by exact_mod_cast hp_bounds.1 ]) (by
      exact_mod_cast ( by nlinarith [ show ( m : ℝ ) ≥ 2 by norm_cast, show ( k : ℝ ) ^ theta > 0 by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith [ Nat.le_max_right kw 2 ] ) _ ] : ( m : ℝ ) * p < n )) (by
      exact dvd_mul_left _ _)

/-- Combine the Konyagin count bound with the BHP lower bound to extract a
prime dividing `P`. -/
lemma konyagin_finish (k : ℕ) (n : ℤ) (hk1 : 1 ≤ k) (C : ℝ)
    (hbhp : C * (k : ℝ) ^ theta / Real.log k ≤
      (primeCard (k : ℝ) ((k : ℝ) + (k : ℝ) ^ theta) : ℝ))
    (hcard : ((badSet k n).card : ℝ) < C * (k : ℝ) ^ theta / Real.log k) :
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) < p ∧ (p : ℝ) < (k : ℝ) + 3 * (k : ℝ) ^ theta ∧
      (p : ℤ) ∣ Pprod k n := by
  obtain ⟨p, hp, hpk, hpb, hdvd⟩ := exists_far_prime k n hk1 (lt_of_lt_of_le hcard hbhp)
  refine ⟨p, hp, hpk, ?_, hdvd⟩
  have : (0 : ℝ) ≤ (k : ℝ) ^ theta := Real.rpow_nonneg (by positivity) _
  linarith

/-- The Konyagin parameter `λ` for the medium-large range: `λ = √(k^{2+θ}/(2n))·log k`. -/
def lamML (k : ℕ) (n : ℤ) : ℝ := Real.sqrt ((k : ℝ) ^ (2 + theta) / (2 * (n : ℝ))) * Real.log k

/-- An `n`-free upper bound for `lamML` on the medium-large range. -/
def lamUB (k : ℕ) : ℝ := (1 / Real.sqrt 2) * (k : ℝ) ^ (theta / 2) * (Real.log k) ^ 2


/-- The `n`-free upper bound for the Konyagin estimate on the medium-large range. -/
def g_ml (k : ℕ) : ℝ :=
  c₆ * (k : ℝ) ^ theta * (
    ((k : ℝ) ^ (theta - 1) * (Real.log k) ^ 2) ^ ((1 : ℝ) / 3) +
    (Real.log k) ^ (-(2 : ℝ)) +
    (3 * lamUB k / (k : ℝ)) ^ ((1 : ℝ) / 4)) + 4 * lamUB k

/-
For `p > 0`, `(k:ℝ)^p` eventually exceeds any constant `A`.
-/
lemma eventually_le_rpow (p A : ℝ) (hp : 0 < p) :
    ∀ᶠ k : ℕ in Filter.atTop, A ≤ (k : ℝ) ^ p := by
  exact Filter.Tendsto.eventually_ge_atTop ( tendsto_rpow_atTop hp |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) A

/-
`(log k)^2 < k` for all sufficiently large `k`.
-/
lemma log_sq_lt_self : ∀ᶠ k : ℕ in Filter.atTop, (Real.log k) ^ 2 < (k : ℝ) := by
  have h_log_sq_lt_k : Filter.Tendsto (fun k : ℕ => (Real.log k) ^ 2 / (k : ℝ)) Filter.atTop (nhds 0) := by
    have h_log_sq_lt_k : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) Filter.atTop (nhds 0) := by
      convert tendsto_log_rpow_mul_rpow_neg 2 1 ( by norm_num ) using 2 ; norm_num;
      rw [ Real.rpow_neg_one, div_eq_mul_inv ];
    exact h_log_sq_lt_k.comp tendsto_natCast_atTop_atTop;
  filter_upwards [ h_log_sq_lt_k.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 0 ] with k hk₁ hk₂ using by rw [ div_lt_one ( by positivity ) ] at hk₁; exact hk₁;

/-
On the medium-large range, `lamML ≥ 1`.
-/
lemma lamML_ge_one (k : ℕ) (n : ℤ) (hk : 3 ≤ k) (hnpos : 0 < n)
    (hn : (n : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (2 + theta)) : 1 ≤ lamML k n := by
  refine' one_le_mul_of_one_le_of_one_le ( Real.le_sqrt_of_sq_le _ ) ( Real.le_log_iff_exp_le _ |>.2 _ );
  · rw [ le_div_iff₀ ] <;> first | positivity | linarith;
  · positivity;
  · exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num; linarith [ show ( k : ℝ ) ≥ 3 by norm_cast ] )

/-
On the medium-large range, `lamML ≤ lamUB`.
-/
lemma lamML_le_lamUB (k : ℕ) (n : ℤ) (hk : 2 ≤ k)
    (hn : (k : ℝ) ^ 2 / (Real.log k) ^ 2 < (n : ℝ)) : lamML k n ≤ lamUB k := by
  have h_lamML : Real.sqrt ((k : ℝ) ^ (2 + theta) / (2 * (n : ℝ))) ≤ (1 / Real.sqrt 2) * (k : ℝ) ^ (theta / 2) * Real.log k := by
    have h_sqrt : (k : ℝ) ^ (2 + theta) / (2 * (n : ℝ)) ≤ (k : ℝ) ^ theta * (Real.log k) ^ 2 / 2 := by
      rw [ div_le_iff₀ ] <;> norm_num [ Real.rpow_add ( by positivity : 0 < ( k : ℝ ) ) ] at *;
      · rw [ div_lt_iff₀ ] at hn <;> nlinarith [ show 0 < ( k : ℝ ) ^ theta by positivity, show 0 < ( Real.log k ) ^ 2 by exact sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr hk ];
      · exact_mod_cast hn.trans_le' ( div_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) );
    convert Real.sqrt_le_sqrt h_sqrt using 1 ; norm_num [ Real.sqrt_div_self ] ; ring_nf;
    rw [ Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ( by positivity ) ] ; ring;
  unfold lamML lamUB; convert mul_le_mul_of_nonneg_right h_lamML ( Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ) using 1 ; ring;

/-
`lamML^2 = k^{2+θ}/(2n) · (log k)^2`.
-/
lemma lamML_sq (k : ℕ) (n : ℤ) (hn0 : 0 < n) :
    (lamML k n) ^ 2 = (k : ℝ) ^ (2 + theta) / (2 * (n : ℝ)) * (Real.log k) ^ 2 := by
  unfold lamML
  rw [mul_pow, Real.sq_sqrt (by positivity)]

/-
Konyagin's theorem, applied with `r = 2`, `λ = lamML`, gives this `n`-free
bound on the bad count for the medium-large range.
-/
lemma ml_card_bound : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ,
    (k : ℝ) ^ 2 / (Real.log k) ^ 2 < (n : ℝ) →
    (n : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (2 + theta) →
    ((badSet k n).card : ℝ) < g_ml k := by
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ∀ k ≥ k₀, 2 ≤ (1 / 2) * (k : ℝ) ^ (1 - theta) ∧ (Real.log k) ^ 2 < k ∧ 3 ≤ k := by
        obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, ∀ k ≥ k₁, 2 ≤ (1 / 2) * (k : ℝ) ^ (1 - theta) := by
          have := @eventually_le_rpow ( 1 - theta ) 4 ( by norm_num [ theta ] );
          exact Filter.eventually_atTop.mp ( this.mono fun k hk => by linarith )
        obtain ⟨k₂, hk₂⟩ : ∃ k₂ : ℕ, ∀ k ≥ k₂, (Real.log k) ^ 2 < k := by
          exact Filter.eventually_atTop.mp ( log_sq_lt_self )
        use max k₁ (max k₂ 3);
        exact fun k hk => ⟨ hk₁ k ( le_trans ( le_max_left _ _ ) hk ), hk₂ k ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hk ), le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hk ⟩;
      refine' ⟨ k₀ + 3, fun k hk n hn₁ hn₂ => _ ⟩;
      have hKon : ((badSet k n).card : ℝ) < c₆ * (k : ℝ) ^ theta * (((n : ℝ) * ((2 : ℕ)!) * (lamML k n) ^ 2 / (k : ℝ) ^ (2 + 1)) ^ ((1 : ℝ) / 3) + ((k : ℝ) ^ ((2 : ℝ) + theta) / ((n : ℝ) * ((2 : ℕ)!) * (lamML k n) ^ 2)) ^ 1 + ((3 * lamML k n) / (k : ℝ)) ^ ((1 : ℝ) / 4)) + 2 * (2 : ℝ) * (lamML k n) := by
        convert konyagin_application ( lamML k n ) theta ( lamML_ge_one k n ( by linarith [ hk₀ k ( by linarith ) ] ) ( by
          exact_mod_cast hn₁.trans_le' ( div_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ) ( by
          exact hn₂ ) ) theta_pos theta_lt_one n k 2 ( by
          rw [ div_lt_iff₀ ] at hn₁;
          · exact_mod_cast ( by nlinarith [ hk₀ k ( by linarith ), show ( k : ℝ ) ≥ 3 by norm_cast; linarith ] : ( k : ℝ ) < n );
          · exact sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ hk₀ k <| by linarith ] ; ) ( by norm_num ) ( by
          exact hk₀ k ( by linarith ) |>.1 ) using 1 ; norm_num [ Nat.factorial ];
      have hT1 : ((n : ℝ) * ((2 : ℕ)!) * (lamML k n) ^ 2 / (k : ℝ) ^ (2 + 1)) ^ ((1 : ℝ) / 3) = ((k : ℝ) ^ (theta - 1) * (Real.log k) ^ 2) ^ ((1 : ℝ) / 3) := by
        have hT1 : (n : ℝ) * ((2 : ℕ)!) * (lamML k n) ^ 2 = (k : ℝ) ^ (2 + theta) * (Real.log k) ^ 2 := by
          rw [ lamML_sq ] ; ring_nf;
          · simp +decide [ mul_comm, show n ≠ 0 by rintro rfl; exact absurd hn₁ ( by norm_num; positivity ) ];
          · exact_mod_cast hn₁.trans_le' ( div_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) );
        rw [ hT1, mul_div_right_comm ];
        rw [ ← Real.rpow_natCast, ← Real.rpow_sub ( by norm_cast; linarith ) ] ; ring_nf
      have hT2 : ((k : ℝ) ^ ((2 : ℝ) + theta) / ((n : ℝ) * ((2 : ℕ)!) * (lamML k n) ^ 2)) ^ 1 = (Real.log k) ^ (-(2 : ℝ)) := by
        rw [ show ( n : ℝ ) * 2! * lamML k n ^ 2 = ( k : ℝ ) ^ ( 2 + theta ) * ( Real.log k ) ^ 2 by
              rw [ lamML_sq ] ; ring_nf;
              · by_cases hn : n = 0 <;> simp_all +decide [ mul_comm ];
                exact absurd hT1 ( ne_of_lt ( Real.rpow_pos_of_pos ( mul_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith [ hk₀ k ( by linarith ) ] ) ) ) ) ) _ ) );
              · exact_mod_cast hn₁.trans_le' ( div_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ] ; norm_cast ; norm_num;
        rw [ ← div_div, div_self ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ), one_div ]
      have hT3 : ((3 * lamML k n) / (k : ℝ)) ^ ((1 : ℝ) / 4) ≤ (3 * lamUB k / (k : ℝ)) ^ ((1 : ℝ) / 4) := by
        gcongr;
        · exact div_nonneg ( mul_nonneg zero_le_three ( show 0 ≤ lamML k n from mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.log_natCast_nonneg _ ) ) ) ( Nat.cast_nonneg _ );
        · have h := lamML_le_lamUB k n ( by linarith ) hn₁; gcongr
      have hLast : 2 * (2 : ℝ) * (lamML k n) ≤ 4 * (lamUB k) := by
        have := lamML_le_lamUB k n ( by linarith ) hn₁; norm_num at *; linarith;
      unfold g_ml; nlinarith [ show 0 < c₆ * ( k : ℝ ) ^ theta by exact mul_pos ( by exact lt_of_lt_of_le ( by norm_num ) ( show ( 256 : ℝ ) ≤ c₆ by unfold c₆; unfold C₀_const; unfold B_const; unfold K_const; unfold c₉; norm_num ) ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ] ;
/-
The medium-large bound `g_ml` is eventually dominated by `C · k^θ / log k`.
-/
lemma ml_rhs_le (C : ℝ) (hC : 0 < C) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → g_ml k ≤ C * (k : ℝ) ^ theta / Real.log k := by
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k → (c₆ * (k : ℝ) ^ theta * ((k : ℝ) ^ (theta - 1) * (Real.log k) ^ 2) ^ ((1 : ℝ) / 3)) ≤ C / 4 * (k : ℝ) ^ theta / Real.log k := by
    have h_poly_log : ∀ᶠ k : ℕ in Filter.atTop, c₆ * (k : ℝ) ^ ((4 * theta - 1) / 3 : ℝ) * (Real.log k) ^ (2 / 3 : ℝ) ≤ C / 4 * (k : ℝ) ^ theta / Real.log k := by
      have := poly_log_lt c₆ ( ( 4 * theta - 1 ) / 3 ) ( 2 / 3 ) theta ?_ ( C / 4 ) ( by linarith ) <;> norm_num at *;
      · exact this;
      · unfold theta; norm_num;
    obtain ⟨ k₁, hk₁ ⟩ := Filter.eventually_atTop.mp h_poly_log;
    refine' ⟨ k₁ + 2, fun k hk => le_trans _ ( hk₁ k ( by linarith ) ) ⟩ ; norm_num [ Real.rpow_def_of_pos, show k > 0 by linarith ] ; ring_nf ; norm_num;
    rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.exp_mul ] ; ring_nf ; norm_num [ Real.exp_add, Real.exp_neg, Real.exp_mul, Real.exp_log ( show 0 < ( k : ℝ ) by norm_cast; linarith ) ] ; ring_nf ; norm_num;
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf ; norm_num [ ← Real.rpow_mul ( Nat.cast_nonneg _ ), ← Real.rpow_neg ( Nat.cast_nonneg _ ) ] ; ring_nf ; norm_num;
    rw [ show ( theta * ( 4 / 3 ) : ℝ ) = theta + theta * ( 1 / 3 ) by ring, Real.rpow_add ( by norm_cast; linarith ) ] ; ring_nf ; norm_num;
  -- Apply the asymptotic lemmas to get the bounds for E2, E3, and E4.
  obtain ⟨k₂, hk₂⟩ : ∃ k₂ : ℕ, ∀ k : ℕ, k₂ ≤ k → c₆ * (k : ℝ) ^ theta * (Real.log k) ^ (-(2 : ℝ)) ≤ C / 4 * (k : ℝ) ^ theta / Real.log k := by
    have := poly_log_lt_eq c₆ theta ( C / 4 ) ( by linarith );
    exact Filter.eventually_atTop.mp this;
  obtain ⟨k₃, hk₃⟩ : ∃ k₃ : ℕ, ∀ k : ℕ, k₃ ≤ k → c₆ * (k : ℝ) ^ theta * (3 * (1 / Real.sqrt 2) * (k : ℝ) ^ (theta / 2) * (Real.log k) ^ 2 / (k : ℝ)) ^ (1 / 4 : ℝ) ≤ C / 4 * (k : ℝ) ^ theta / Real.log k := by
    have := poly_log_lt ( c₆ * ( 3 * ( 1 / Real.sqrt 2 ) ) ^ ( 1 / 4 : ℝ ) ) ( ( 9 * theta - 2 ) / 8 ) ( 1 / 2 ) theta ?_ ( C / 4 ) ( by linarith ) <;> norm_num at *;
    · obtain ⟨ k₃, hk₃ ⟩ := this; use k₃ + 2; intros k hk; convert hk₃ k ( by linarith ) using 1; rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
      rw [ ← Real.rpow_mul ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      rw [ show ( -1 / 4 + theta * ( 9 / 8 ) : ℝ ) = theta + theta * ( 1 / 8 ) - 1 / 4 by ring ] ; norm_num [ Real.rpow_add ( by norm_cast; linarith : 0 < ( k : ℝ ) ), Real.rpow_sub ( by norm_cast; linarith : 0 < ( k : ℝ ) ) ] ; ring;
    · unfold theta; norm_num;
  obtain ⟨k₄, hk₄⟩ : ∃ k₄ : ℕ, ∀ k : ℕ, k₄ ≤ k → 4 * (1 / Real.sqrt 2) * (k : ℝ) ^ (theta / 2) * (Real.log k) ^ 2 ≤ C / 4 * (k : ℝ) ^ theta / Real.log k := by
    have := poly_log_lt ( 4 * ( 1 / Real.sqrt 2 ) ) ( theta / 2 ) 2 theta ?_ ( C / 4 ) ?_ <;> norm_num at *;
    · exact this;
    · linarith [theta_pos];
    · positivity;
  refine' ⟨ Max.max k₁ ( Max.max k₂ ( Max.max k₃ k₄ ) ), fun k hk => _ ⟩ ; simp_all +decide [ g_ml, lamUB ];
  convert add_le_add ( add_le_add ( add_le_add ( hk₁ k hk.1 ) ( hk₂ k hk.2.1 ) ) ( hk₃ k hk.2.2.1 ) ) ( hk₄ k hk.2.2.2 ) using 1 <;> ring_nf

/-- **Medium-large `n`:** `k² / log²k < n ≤ ½ k^{2+θ}`. -/
lemma case_mediumlarge : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ,
    (k : ℝ) ^ 2 / (Real.log k) ^ 2 < (n : ℝ) →
    (n : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (2 + theta) →
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) < p ∧ (p : ℝ) < (k : ℝ) + 3 * (k : ℝ) ^ theta ∧
      (p : ℤ) ∣ Pprod k n := by
  obtain ⟨C, hC, kb, hb⟩ := bhp
  obtain ⟨k1, hk1card⟩ := ml_card_bound
  obtain ⟨k2, hk2rhs⟩ := ml_rhs_le C hC
  refine ⟨max (max kb k1) (max k2 2), ?_⟩
  intro k hk n hlow hhigh
  have hkb : kb ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hki1 : k1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hki2 : k2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk2le : 2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hk1 : 1 ≤ k := by omega
  have hbhp : C * (k : ℝ) ^ theta / Real.log k ≤
      (primeCard (k : ℝ) ((k : ℝ) + (k : ℝ) ^ theta) : ℝ) := by
    exact hb k hkb
  have hcard : ((badSet k n).card : ℝ) < C * (k : ℝ) ^ theta / Real.log k :=
    lt_of_lt_of_le (hk1card k hki1 n hlow hhigh) (hk2rhs k hki2)
  exact konyagin_finish k n hk1 C hbhp hcard

/-! ### Medium case machinery (elementary counting) -/

/-- The integer window `(k, k + k^θ)`. -/
def medWindow (k : ℕ) : Finset ℤ :=
  (Finset.Ioo (k : ℤ) ((k : ℤ) + ⌊(k : ℝ) ^ theta⌋ + 2)).filter
    (fun m : ℤ => (m : ℝ) < (k : ℝ) + (k : ℝ) ^ theta)

/-- The `h`-fiber: window integers `m` with `n/m` within `1/k^{1-θ}` of `h`. -/
def medFiber (k : ℕ) (n : ℤ) (h : ℤ) : Finset ℤ :=
  (medWindow k).filter (fun m : ℤ => |(n : ℝ) / (m : ℝ) - (h : ℝ)| < 1 / (k : ℝ) ^ (1 - theta))

/-- The set of integers `h` between `⌊n/(k+k^θ)⌋` and `⌈n/k⌉`. -/
def medJ (k : ℕ) (n : ℤ) : Finset ℤ :=
  Finset.Icc ⌊(n : ℝ) / ((k : ℝ) + (k : ℝ) ^ theta)⌋ ⌈(n : ℝ) / (k : ℝ)⌉

/-
At most `2L+1` integers `m` (within any finset) satisfy `|m - x| < L`.
-/
lemma card_int_abs_sub_lt_le (x L : ℝ) (hL : 0 ≤ L) (S : Finset ℤ) :
    ((S.filter (fun m : ℤ => |(m : ℝ) - x| < L)).card : ℝ) ≤ 2 * L + 1 := by
  -- Every integer `m` with `|(m:ℝ) - x| < L` satisfies `x - L < m < x + L`.
  have h_filter_subset : S.filter (fun m : ℤ => |(m : ℝ) - x| < L) ⊆ Finset.Ioo (⌊x - L⌋) (⌈x + L⌉) := by
    intro m hm; simp_all +decide [ abs_lt ] ;
    exact ⟨ Int.floor_lt.2 ( by linarith ), Int.lt_ceil.2 ( by linarith ) ⟩;
  refine' le_trans _ ( show 2 * L + 1 ≥ ↑ ( Int.toNat ( ⌈x + L⌉ - ⌊x - L⌋ - 1 ) ) from _ );
  · refine' mod_cast le_trans ( Finset.card_le_card h_filter_subset ) _ ; simp +decide [ Int.card_Ioo ];
  · rcases n : ⌈x + L⌉ - ⌊x - L⌋ - 1 with ( _ | _ | n ) <;> simp_all +decide [ Int.toNat ];
    · rw [ ← @Int.cast_inj ℝ ] at * ; norm_num at * ; linarith [ Int.floor_le ( x - L ), Int.lt_floor_add_one ( x - L ), Int.le_ceil ( x + L ), Int.ceil_lt_add_one ( x + L ) ];
    · linarith;
    · linarith

/-
Every bad integer lies in some fiber indexed by `h ∈ medJ`.
-/
lemma badSet_subset_biUnion (k : ℕ) (n : ℤ) (hk1 : 1 ≤ k) (hn : 0 < n) :
    badSet k n ⊆ (medJ k n).biUnion (medFiber k n) := by
  intro m hm; simp_all +decide ;
  refine' ⟨ round ( ( n : ℝ ) / m ), _, _ ⟩ <;> simp_all +decide [ medJ, medFiber ];
  · -- From `hmW` (unfold `medWindow`, `Finset.mem_filter`, `Finset.mem_Ioo`): `(k:ℤ) < m` and `(m:ℝ) < (k:ℝ)+(k:ℝ)^theta`. So `(k:ℝ) < (m:ℝ)` and `(m:ℝ) > 0`.
    have hm_bounds : (k : ℝ) < m ∧ m < (k : ℝ) + (k : ℝ) ^ theta := by
      exact ⟨ mod_cast Finset.mem_Ioo.mp ( Finset.mem_filter.mp hm |>.1 ) |>.1, Finset.mem_filter.mp hm |>.2.1 ⟩;
    constructor <;> rw [ round_eq ] <;> norm_num [ Int.floor_le, Int.le_ceil ] at *;
    · exact Int.floor_mono <| le_add_of_le_of_nonneg ( div_le_div_of_nonneg_left ( by positivity ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) <| by linarith ) <| by positivity;
    · refine' Int.le_of_lt_add_one ( Int.floor_lt.mpr _ );
      norm_num +zetaDelta at *;
      linarith [ show ( n : ℝ ) / m < ( n : ℝ ) / k by gcongr ; linarith, Int.le_ceil ( ( n : ℝ ) / k ) ];
  · unfold badSet at hm; unfold medWindow at *; aesop;

/-
`|medJ| ≤ 3 + n / k^{2-θ}`.
-/
lemma medJ_card_le (k : ℕ) (n : ℤ) (hk1 : 1 ≤ k) (hn : 0 < n) :
    ((medJ k n).card : ℝ) ≤ 3 + (n : ℝ) / (k : ℝ) ^ (2 - theta) := by
  -- By definition of медJ, we have
  have cei : (medJ k n).card ≤ (⌈(n : ℝ) / k⌉ - ⌊(n : ℝ) / (k + (k : ℝ) ^ theta)⌋ + 1) := by
    simp +decide [ medJ ];
    constructor <;> linarith [ show ⌊ ( n : ℝ ) / ( k + k ^ theta ) ⌋ ≤ ⌈ ( n : ℝ ) / k ⌉ from Int.floor_le_ceil _ |> le_trans <| Int.ceil_mono <| by gcongr ; linarith [ Real.rpow_nonneg ( Nat.cast_nonneg k ) theta ] ];
  -- By definition of ceiling and floor functions, we have:
  have h_ceil_floor : (⌈(n : ℝ) / k⌉ : ℝ) < (n : ℝ) / k + 1 ∧ (⌊(n : ℝ) / (k + (k : ℝ) ^ theta)⌋ : ℝ) > (n : ℝ) / (k + (k : ℝ) ^ theta) - 1 := by
    exact ⟨ Int.ceil_lt_add_one _, Int.sub_one_lt_floor _ ⟩;
  -- Now bound the difference:
  have h_diff : (n : ℝ) / k - (n : ℝ) / (k + (k : ℝ) ^ theta) ≤ (n : ℝ) / (k : ℝ) ^ (2 - theta) := by
    rw [ Real.rpow_sub ] <;> norm_num;
    · field_simp;
      nlinarith only [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( k : ℝ ) ^ theta ≥ 0 by positivity ];
    · linarith;
  push_cast [ ← @Int.cast_le ℝ ] at * ; linarith

/-
Each fiber has at most `1 + 8 k^{1+θ}/n` elements.
-/
lemma medFiber_card_le : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ,
    (1 / 2) * (k : ℝ) ^ (2 - theta) < (n : ℝ) → ∀ h : ℤ,
    ((medFiber k n h).card : ℝ) ≤ 1 + 8 * (k : ℝ) ^ (1 + theta) / (n : ℝ) := by
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → 8 ≤ (k : ℝ) ^ (1 - theta) := by
    convert Filter.eventually_atTop.mp ( eventually_le_rpow ( 1 - theta ) 8 ( by linarith [ theta_lt_one ] ) ) using 1;
  refine' ⟨ k₀ + 2, fun k hk n hn h => _ ⟩ ; norm_num at *;
  by_cases h_empty : medFiber k n h = ∅;
  · norm_num [ h_empty ];
    exact add_nonneg zero_le_one ( div_nonneg ( by positivity ) ( by exact_mod_cast ( by linarith [ show ( 0 :ℝ ) ≤ k ^ ( 2 - theta ) by positivity ] : ( 0 :ℝ ) ≤ n ) ) );
  · -- Since `medFiber k n h` is nonempty, we can pick any `m₀ ∈ medFiber k n h`.
    obtain ⟨m₀, hm₀⟩ : ∃ m₀ ∈ medFiber k n h, (k : ℝ) < m₀ ∧ (m₀ : ℝ) < (k : ℝ) + (k : ℝ) ^ theta ∧ |(n : ℝ) / m₀ - (h : ℝ)| < 1 / (k : ℝ) ^ (1 - theta) := by
      obtain ⟨ m₀, hm₀ ⟩ := Finset.nonempty_of_ne_empty h_empty; use m₀; simp_all +decide [ medFiber, medWindow ] ;
      exact_mod_cast hm₀.1.1.1;
    -- We'll use that $h \geq \frac{n}{2k}$ to bound $m/h$.
    have h_h_ge : (h : ℝ) ≥ (n : ℝ) / (2 * (k : ℝ)) := by
      have h_h_ge : (h : ℝ) > (n : ℝ) / ((k : ℝ) + (k : ℝ) ^ theta) - 1 := by
        have h_h_ge : (n : ℝ) / m₀ > (n : ℝ) / ((k : ℝ) + (k : ℝ) ^ theta) := by
          gcongr <;> norm_cast at *;
          · exact_mod_cast hn.trans_le' ( mul_nonneg ( by norm_num ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) );
          · linarith;
          · exact_mod_cast hm₀.2.2.1;
        linarith [ abs_lt.mp hm₀.2.2.2, show ( 1 : ℝ ) / k ^ ( 1 - theta ) ≤ 1 by exact div_le_self zero_le_one <| Real.one_le_rpow ( by norm_cast; linarith ) <| by linarith [ show theta < 1 by exact theta_lt_one ] ];
      have h_h_ge : (n : ℝ) / ((k : ℝ) + (k : ℝ) ^ theta) - (n : ℝ) / (2 * (k : ℝ)) ≥ 1 := by
        rw [ div_sub_div, ge_iff_le, le_div_iff₀ ];
        · have h_h_ge : (k : ℝ) ^ (2 - theta) ≥ 8 * (k : ℝ) := by
            have := hk₀ k ( by linarith );
            exact le_trans ( mul_le_mul_of_nonneg_right this ( Nat.cast_nonneg _ ) ) ( by rw [ ← Real.rpow_add_one ( by norm_cast; linarith ) ] ; ring_nf; norm_num );
          rw [ Real.rpow_sub ] at * <;> norm_num at *;
          · nlinarith [ show ( k : ℝ ) ^ theta > 0 by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _, show ( k : ℝ ) ^ theta ≤ k by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( show theta ≤ 1 by exact le_of_lt ( by norm_num [ theta ] ) ) ) ( by norm_num ), mul_div_cancel₀ ( ( k : ℝ ) ^ 2 ) ( show ( k : ℝ ) ^ theta ≠ 0 by exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ) ];
          · linarith;
          · lia;
          · linarith;
        · exact mul_pos ( add_pos_of_pos_of_nonneg ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( mul_pos zero_lt_two ( Nat.cast_pos.mpr ( by linarith ) ) );
        · exact ne_of_gt ( add_pos_of_pos_of_nonneg ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) );
        · norm_cast ; linarith;
      linarith;
    -- Using the bound on $m/h$, we can show that $|m - n/h| < 4k^{1+\theta}/n$.
    have h_abs_lt : ∀ m ∈ medFiber k n h, |(m : ℝ) - (n : ℝ) / (h : ℝ)| < 4 * (k : ℝ) ^ (1 + theta) / (n : ℝ) := by
      intro m hm
      have h_abs_lt_step : |(m : ℝ) - (n : ℝ) / (h : ℝ)| ≤ (m : ℝ) / (h : ℝ) * |(n : ℝ) / (m : ℝ) - (h : ℝ)| := by
        by_cases hm_pos : 0 < m <;> by_cases hh_pos : 0 < h <;> simp_all +decide [div_mul_eq_mul_div];
        · field_simp;
          rw [ abs_div, abs_div, abs_of_pos ( by positivity : 0 < ( h : ℝ ) ), abs_of_pos ( by positivity : 0 < ( m : ℝ ) ) ];
          rw [ mul_div_cancel₀ _ ( by positivity ), mul_div_cancel₀ _ ( by positivity ), abs_sub_comm ];
        · contrapose! h_h_ge;
          exact lt_of_le_of_lt ( Int.cast_nonpos.mpr hh_pos ) ( div_pos ( by exact lt_of_le_of_lt ( by positivity ) hn ) ( by norm_cast; linarith ) );
        · grind +locals;
        · contrapose! hn;
          exact le_trans ( show ( n : ℝ ) ≤ 0 by exact_mod_cast le_of_not_gt fun hn => by { exact absurd h_h_ge ( by { exact not_le_of_gt <| lt_of_le_of_lt ( by norm_cast ) <| div_pos ( by positivity ) <| by norm_cast; linarith } ) } ) <| by positivity;
      -- Using the bound on $m/h$, we can show that $m/h \leq 4k^2/n$.
      have h_m_div_h_le : (m : ℝ) / (h : ℝ) ≤ 4 * (k : ℝ) ^ 2 / (n : ℝ) := by
        have h_m_div_h_le : (m : ℝ) ≤ 2 * (k : ℝ) := by
          have h_m_le : (m : ℝ) < (k : ℝ) + (k : ℝ) ^ theta := by
            exact Finset.mem_filter.mp ( Finset.mem_filter.mp hm |>.1 ) |>.2;
          exact_mod_cast Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ show ( k : ℝ ) ^ theta ≤ k by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( show theta ≤ 1 by exact le_of_lt theta_lt_one ) ) ( by norm_num ) ] );
        rw [ div_le_div_iff₀ ] <;> norm_num at *;
        · rw [ div_le_iff₀ ] at h_h_ge <;> nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast; linarith, show ( n : ℝ ) > 0 by exact lt_of_le_of_lt ( by positivity ) hn ];
        · exact_mod_cast h_h_ge.trans_lt' ( div_pos ( show ( 0 : ℝ ) < n by exact lt_of_le_of_lt ( by positivity ) hn ) ( by norm_cast; linarith ) );
        · exact_mod_cast hn.trans_le' ( mul_nonneg ( by norm_num ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) );
      -- Using the bound on $|n/m - h|$, we can show that $|n/m - h| < 1/k^{1-\theta}$.
      have h_abs_lt_step2 : |(n : ℝ) / (m : ℝ) - (h : ℝ)| < 1 / (k : ℝ) ^ (1 - theta) := by
        exact Finset.mem_filter.mp hm |>.2;
      refine lt_of_le_of_lt h_abs_lt_step <| lt_of_le_of_lt ( mul_le_mul_of_nonneg_right h_m_div_h_le <| abs_nonneg _ ) ?_;
      convert mul_lt_mul_of_pos_left h_abs_lt_step2 ( show ( 0 : ℝ ) < 4 * k ^ 2 / n by exact div_pos ( by norm_cast; nlinarith ) ( by exact_mod_cast ( by linarith [ show ( 0 :ℝ ) < n by exact lt_of_le_of_lt ( by positivity ) hn ] : ( 0 :ℝ ) < n ) ) ) using 1 ; ring_nf;
      rw [ show ( 1 + theta : ℝ ) = 2 - ( 1 - theta ) by ring, Real.rpow_sub ] <;> norm_num ; ring ; linarith;
    have h_card_le : ((medFiber k n h).card : ℝ) ≤ 2 * (4 * (k : ℝ) ^ (1 + theta) / (n : ℝ)) + 1 := by
      have := card_int_abs_sub_lt_le ( ( n : ℝ ) / h ) ( 4 * ( k : ℝ ) ^ ( 1 + theta ) / n ) ?_ ( medFiber k n h );
      · convert this using 2 ; rw [ Finset.filter_true_of_mem h_abs_lt ];
      · exact div_nonneg ( mul_nonneg zero_le_four ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( by linarith [ show ( 0 : ℝ ) ≤ n by exact_mod_cast Int.le_of_lt_add_one ( by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ show ( 0 : ℝ ) ≤ k ^ ( 2 - theta ) by positivity ] } ) ] );
    exact h_card_le.trans_eq ( by ring )

/-- The `n`-free upper bound for the bad count on the medium range. -/
def g_med (k : ℕ) : ℝ :=
  3 + 56 * (k : ℝ) ^ (2 * theta - 1) + (k : ℝ) ^ theta * (Real.log k) ^ (-(2 : ℝ))

/-
The elementary counting bound for the bad count on the medium range.
-/
lemma med_card_bound : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ,
    (1 / 2) * (k : ℝ) ^ (2 - theta) < (n : ℝ) →
    (n : ℝ) ≤ (k : ℝ) ^ 2 / (Real.log k) ^ 2 →
    ((badSet k n).card : ℝ) < g_med k := by
  -- By definition of $g_{\text{med}}$, we know that for sufficiently large $k$, $g_{\text{med}}(k)$ is greater than the bound given by the lemma.
  have h_bound : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ,
    (1 / 2) * (k : ℝ) ^ (2 - theta) < (n : ℝ) →
    (n : ℝ) ≤ (k : ℝ) ^ 2 / (Real.log k) ^ 2 →
    ((badSet k n).card : ℝ) ≤ (3 + (n : ℝ) / (k : ℝ) ^ (2 - theta)) * (1 + 8 * (k : ℝ) ^ (1 + theta) / (n : ℝ)) := by
      have := @medFiber_card_le;
      obtain ⟨k₀, hk₀⟩ := this
      use max k₀ 2
      intro k hk n hn hhigh
      have hk0 : k₀ ≤ k := by
        exact le_trans ( le_max_left _ _ ) hk
      have hk1 : 1 ≤ k := by
        linarith [ le_max_right k₀ 2 ]
      have hn0 : 0 < n := by
        exact_mod_cast hn.trans_le' ( mul_nonneg ( by norm_num ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) )
      have h_card : ((badSet k n).card : ℝ) ≤ ∑ h ∈ medJ k n, ((medFiber k n h).card : ℝ) := by
        exact_mod_cast Finset.card_le_card ( badSet_subset_biUnion k n hk1 hn0 ) |> le_trans <| Finset.card_biUnion_le;
      refine le_trans h_card <| le_trans ( Finset.sum_le_sum fun x hx => hk₀ k hk0 n hn x ) ?_;
      have := medJ_card_le k n hk1 hn0; norm_num at *; nlinarith [ show ( 0 :ℝ ) ≤ 8 * k ^ ( 1 + theta ) / n by positivity ] ;
  obtain ⟨ k₀, hk₀ ⟩ := h_bound; use Max.max k₀ 2; intros k hk n hn hn'; refine lt_of_le_of_lt ( hk₀ k ( le_trans ( le_max_left _ _ ) hk ) n hn hn' ) ?_ ; unfold g_med; ring_nf; norm_num;
  -- Simplify the expression by cancelling out common terms.
  have h_simp : (n : ℝ) * (k : ℝ) ^ (1 + theta) / (k : ℝ) ^ (2 - theta) = (n : ℝ) * (k : ℝ) ^ (2 * theta - 1) ∧ (k : ℝ) ^ (1 + theta) / (n : ℝ) < 2 * (k : ℝ) ^ (2 * theta - 1) ∧ (n : ℝ) / (k : ℝ) ^ (2 - theta) ≤ (k : ℝ) ^ theta * (Real.log k) ^ (-2 : ℝ) := by
    refine' ⟨ _, _, _ ⟩;
    · rw [ mul_div_assoc, ← Real.rpow_sub ( by norm_cast; linarith [ le_max_right k₀ 2 ] ) ] ; ring_nf;
    · rw [ div_lt_iff₀ ];
      · refine' lt_of_le_of_lt _ ( mul_lt_mul_of_pos_left hn ( by exact mul_pos zero_lt_two ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ le_max_right k₀ 2 ] ) ) _ ) ) ) ; ring_nf ; norm_num [ theta ];
        rw [ ← Real.rpow_add' ] <;> norm_num;
      · exact lt_of_le_of_lt ( by positivity ) hn;
    · convert div_le_div_of_nonneg_right hn' ( Real.rpow_nonneg ( Nat.cast_nonneg k ) _ ) using 1 ; norm_cast ; norm_num ; ring_nf;
      rw [ show ( k : ℝ ) ^ theta = ( k : ℝ ) ^ ( 2 - ( 2 - theta ) ) by ring_nf, Real.rpow_sub ] <;> norm_num ; ring ; linarith [ le_max_right k₀ 2 ];
  ring_nf at *;
  by_cases hn : n = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · exact absurd ‹_› ( not_lt_of_ge ( by positivity ) );
  · linarith

/-
The medium bound `g_med` is eventually dominated by `C · k^θ / log k`.
-/
lemma med_rhs_le (C : ℝ) (hC : 0 < C) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → g_med k ≤ C * (k : ℝ) ^ theta / Real.log k := by
  -- Apply `poly_log_lt` three times to get each term's bound, then combine them.
  have h1 : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → 3 ≤ (C / 3) * (k : ℝ) ^ theta / Real.log k := by
    have := poly_log_lt 3 0 0 theta theta_pos ( C / 3 ) ( by linarith ) ; aesop;
  have h2 : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → 56 * (k : ℝ) ^ (2 * theta - 1) ≤ (C / 3) * (k : ℝ) ^ theta / Real.log k := by
    convert poly_log_lt 56 ( 2 * theta - 1 ) 0 theta ( by linarith [ theta_pos, theta_lt_one ] ) ( C / 3 ) ( by linarith ) using 1;
    norm_num [ Filter.eventually_atTop ]
  have h3 : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → (k : ℝ) ^ theta * (Real.log k) ^ (-(2 : ℝ)) ≤ (C / 3) * (k : ℝ) ^ theta / Real.log k := by
    convert poly_log_lt_eq 1 theta ( C / 3 ) ( by linarith ) using 1;
    norm_num [ Filter.eventually_atTop ];
  exact ⟨ Max.max h1.choose ( Max.max h2.choose h3.choose ), fun k hk => by convert add_le_add_three ( h1.choose_spec k ( le_trans ( le_max_left _ _ ) hk ) ) ( h2.choose_spec k ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hk ) ) ( h3.choose_spec k ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hk ) ) using 1 ; ring ⟩

/-- **Medium `n`:** `½ k^{2-θ} < n ≤ k² / log²k`. -/
lemma case_medium : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ,
    (1 / 2) * (k : ℝ) ^ (2 - theta) < (n : ℝ) →
    (n : ℝ) ≤ (k : ℝ) ^ 2 / (Real.log k) ^ 2 →
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) < p ∧ (p : ℝ) < (k : ℝ) + 3 * (k : ℝ) ^ theta ∧
      (p : ℤ) ∣ Pprod k n := by
  obtain ⟨C, hC, kb, hb⟩ := bhp
  obtain ⟨k1, hk1card⟩ := med_card_bound
  obtain ⟨k2, hk2rhs⟩ := med_rhs_le C hC
  refine ⟨max (max kb k1) (max k2 2), ?_⟩
  intro k hk n hlow hhigh
  have hkb : kb ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hki1 : k1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hki2 : k2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk2le : 2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hk1 : 1 ≤ k := by omega
  have hbhp : C * (k : ℝ) ^ theta / Real.log k ≤
      (primeCard (k : ℝ) ((k : ℝ) + (k : ℝ) ^ theta) : ℝ) := by
    exact hb k hkb
  have hcard : ((badSet k n).card : ℝ) < C * (k : ℝ) ^ theta / Real.log k :=
    lt_of_lt_of_le (hk1card k hki1 n hlow hhigh) (hk2rhs k hki2)
  exact konyagin_finish k n hk1 C hbhp hcard

/-! ### Large case machinery (Konyagin with variable `r`) -/

/-- The exponent `E₁ = (1-θ)(2r-1)/(3r-2)`. -/
def E1exp (r : ℕ) : ℝ := (1 - theta) * (2 * (r : ℝ) - 1) / (3 * (r : ℝ) - 2)

/-- The Konyagin parameter `λ` for the large range. -/
def lamLarge (k : ℕ) (n : ℤ) (r : ℕ) : ℝ :=
  ((k : ℝ) ^ ((r : ℝ) + 1 - E1exp r) / ((n : ℝ) * (Nat.factorial r : ℝ))) ^ ((1 : ℝ) / (r : ℝ))

/-
`λ^r = k^{r+1-E₁}/(n r!)`.
-/
lemma lamLarge_pow (k : ℕ) (n : ℤ) (r : ℕ) (hn0 : 0 < n) (hk0 : 0 < k) (hr1 : 1 ≤ r) :
    (lamLarge k n r) ^ r =
      (k : ℝ) ^ ((r : ℝ) + 1 - E1exp r) / ((n : ℝ) * (Nat.factorial r : ℝ)) := by
  unfold lamLarge; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( ?_ ) ] ; norm_num [ show r ≠ 0 by linarith ] ;
  positivity

/-
`λ ≥ 1` on the large range.
-/
lemma lamLarge_ge_one (k : ℕ) (n : ℤ) (r : ℕ) (hn0 : 0 < n) (hk : 1 < k) (hr3 : 3 ≤ r)
    (hub : (n : ℝ) * (Nat.factorial r : ℝ) ≤ (k : ℝ) ^ ((r : ℝ) + theta)) :
    1 ≤ lamLarge k n r := by
  refine' Real.one_le_rpow _ _;
  · rw [ one_le_div ];
    · refine' le_trans hub ( Real.rpow_le_rpow_of_exponent_le ( mod_cast hk.le ) _ );
      unfold E1exp; rw [ le_sub_comm ] ; rw [ div_le_iff₀ ] <;> nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast, show ( theta : ℝ ) < 1 by exact_mod_cast theta_lt_one ] ;
    · positivity;
  · positivity

/-
`λ < k^{(2-θ)/r}` from minimality of `r`.
-/
lemma lamLarge_lt (k : ℕ) (n : ℤ) (r : ℕ) (hn0 : 0 < n) (hk : 1 < k) (hr3 : 3 ≤ r)
    (hmin : (k : ℝ) ^ (((r : ℝ) - 1) + theta) < (n : ℝ) * (Nat.factorial (r - 1) : ℝ)) :
    lamLarge k n r < (k : ℝ) ^ ((2 - theta) / (r : ℝ)) := by
  refine' lt_of_lt_of_le ( Real.rpow_lt_rpow ( _ ) _ ( by positivity ) ) _;
  exact ( k : ℝ ) ^ ( 2 - E1exp r - theta );
  · positivity;
  · rw [ div_lt_iff₀ ( by positivity ) ];
    refine' lt_of_le_of_lt _ ( mul_lt_mul_of_pos_left ( show ( n : ℝ ) * r.factorial > k ^ ( r - 1 + theta ) * r from _ ) ( by positivity ) );
    · rw [ ← mul_assoc, ← Real.rpow_add ( by positivity ) ] ; ring_nf;
      exact le_mul_of_one_le_left ( by positivity ) ( by norm_cast; linarith );
    · rcases r <;> simp_all +decide [ Nat.factorial_succ ];
      nlinarith [ show ( k : ℝ ) ^ ( ( ↑‹ℕ› : ℝ ) + theta ) > 0 by positivity ];
  · rw [ ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
    exact Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( by nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast, inv_pos.mpr ( by positivity : 0 < ( r : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( r : ℝ ) ≠ 0 ), show ( E1exp r : ℝ ) ≥ 0 by exact div_nonneg ( mul_nonneg ( sub_nonneg.mpr <| by linarith [ show ( theta : ℝ ) ≤ 1 by exact le_of_lt <| by norm_num [ theta ] ] ) <| by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) <| by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ] )

/-
Konyagin's theorem with the balanced choice of `λ` makes the first two terms
equal to `k^{(θ-1)/(3r-2)}`.
-/
lemma large_card_raw (k : ℕ) (n : ℤ) (r : ℕ) (hk : 1 < k) (hn0 : 0 < n) (hr3 : 3 ≤ r)
    (hrle : (r : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (1 - theta)) (hkn : (k : ℤ) < n)
    (hub : (n : ℝ) * (Nat.factorial r : ℝ) ≤ (k : ℝ) ^ ((r : ℝ) + theta)) :
    ((badSet k n).card : ℝ) <
      c₆ * (k : ℝ) ^ theta *
        (2 * (k : ℝ) ^ ((theta - 1) / (3 * (r : ℝ) - 2)) +
          (((r : ℝ) + 1) * lamLarge k n r / (k : ℝ)) ^ ((2 * (r : ℝ))⁻¹)) +
      2 * (r : ℝ) * lamLarge k n r := by
  -- Let `l := lamLarge k n r`. By `hr3`, `lamLarge_ge_one` applies, so try `Let's choose `l := lamLarge k n r` and `Let's choose `l := lamLarge k n r`.
  set l := lamLarge k n r with hl;
  have hT1 : ((n : ℝ) * (Nat.factorial r : ℝ) * l ^ r / (k : ℝ) ^ (r + 1)) ^ ((2 * (r : ℝ) - 1)⁻¹) = (k : ℝ) ^ ((theta - 1) / (3 * (r : ℝ) - 2)) := by
    have hT1 : ((n : ℝ) * (Nat.factorial r : ℝ) * l ^ r / (k : ℝ) ^ (r + 1)) = (k : ℝ) ^ (-(E1exp r)) := by
      have hT1 : ((n : ℝ) * (Nat.factorial r : ℝ) * l ^ r) = (k : ℝ) ^ ((r : ℝ) + 1 - E1exp r) := by
        rw [ lamLarge_pow k n r hn0 ( by positivity ) ( by linarith ) ];
        rw [ mul_div_cancel₀ _ ( by positivity ) ];
      rw [ hT1, div_eq_iff ( by positivity ) ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_add ( by positivity ) ] ; push_cast ; ring_nf;
    rw [ hT1, ← Real.rpow_mul ] <;> norm_num [ E1exp ];
    field_simp;
    exact congr_arg _ ( by rw [ neg_div', div_eq_div_iff ] <;> nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast, show ( k : ℝ ) ≥ 2 by norm_cast ] );
  have hT2 : ((k : ℝ) ^ ((r : ℝ) + theta) / ((n : ℝ) * (Nat.factorial r : ℝ) * l ^ r)) ^ (((r : ℝ) - 1)⁻¹) = (k : ℝ) ^ ((theta - 1) / (3 * (r : ℝ) - 2)) := by
    have hT2_base : ((k : ℝ) ^ ((r : ℝ) + theta) / ((n : ℝ) * (Nat.factorial r : ℝ) * l ^ r)) = (k : ℝ) ^ (theta - 1 + E1exp r) := by
      rw [ lamLarge_pow k n r hn0 ( by positivity ) ( by linarith ) ];
      rw [ mul_div_cancel₀ _ ( by positivity ) ];
      rw [ ← Real.rpow_sub ( by positivity ) ] ; ring_nf;
    rw [ hT2_base, ← Real.rpow_mul ( by positivity ) ];
    congr 1;
    unfold E1exp;
    rw [ ← div_eq_mul_inv, div_eq_div_iff ] <;> nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast, mul_div_cancel₀ ( ( 1 - theta ) * ( 2 * r - 1 ) ) ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] : ( 3 * r - 2 : ℝ ) ≠ 0 ) ];
  have := @konyagin_application;
  convert this l theta ( lamLarge_ge_one k n r hn0 hk hr3 hub ) theta_pos theta_lt_one n k r hkn ( by linarith ) hrle using 1 ; norm_num [ hT1, hT2 ] ; exact Or.inl (by ring)

/-
Pointwise bound for the first Konyagin term in the large range.
-/
lemma large_term1_le (k r : ℕ) (hk : 1 < k) (hr3 : 3 ≤ r) (hlog1 : 1 < Real.log k)
    (h3r2 : (3 * (r : ℝ) - 2) < 7 * (1 / 20) * Real.log k / Real.log (Real.log k)) :
    (k : ℝ) ^ ((theta - 1) / (3 * (r : ℝ) - 2)) ≤ (Real.log k) ^ (-(19 : ℝ) / 14) := by
  rw [ Real.rpow_def_of_pos, Real.rpow_def_of_pos ] <;> try positivity;
  -- By simplifying, we can see that the inequality holds.
  have h_simplified : (20 * Real.log (Real.log k) * (3 * (r : ℝ) - 2)) / 7 < Real.log k := by
    rw [ lt_div_iff₀ ] at h3r2 <;> nlinarith [ Real.log_pos hlog1 ];
  unfold theta; norm_num; rw [ mul_div, div_le_iff₀ ] <;> nlinarith [ ( by norm_cast : ( 3 :ℝ ) ≤ r ) ] ;

/-
Pointwise bound for the third Konyagin term in the large range.
-/
lemma large_term3_le (k : ℕ) (n : ℤ) (r : ℕ) (hk : 1 < k) (hn0 : 0 < n) (hr3 : 3 ≤ r)
    (hlog1 : 1 < Real.log k)
    (hmin : (k : ℝ) ^ (((r : ℝ) - 1) + theta) < (n : ℝ) * (Nat.factorial (r - 1) : ℝ))
    (hrk : ((r : ℝ) + 1) ≤ (k : ℝ) ^ (theta / (r : ℝ)))
    (hrconv : (r : ℝ) ≤ 3 * (1 / 20) * Real.log k / Real.log (Real.log k)) :
    (((r : ℝ) + 1) * lamLarge k n r / (k : ℝ)) ^ ((2 * (r : ℝ))⁻¹) ≤
      (Real.log k) ^ (-(10 : ℝ) / 9) := by
  -- Step 1: the base `((r:ℝ)+1)*λ/(k:ℝ) < (k:ℝ)^(2/(r:ℝ) - 1)`.
  have h_base : ((r + 1 : ℝ) * lamLarge k n r / k) < (k : ℝ) ^ (2 / (r : ℝ) - 1) := by
    have h_base : ((r + 1 : ℝ) * lamLarge k n r) < (k : ℝ) ^ (2 / (r : ℝ)) := by
      refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_right hrk ( Real.rpow_nonneg ( by positivity ) _ ) ) _;
      convert mul_lt_mul_of_pos_left ( lamLarge_lt k n r hn0 hk hr3 hmin ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hk.le ) _ ) using 1 ; ring_nf;
      rw [ ← Real.rpow_add ( by positivity ) ] ; ring_nf;
    convert div_lt_div_iff_of_pos_right ( by positivity : 0 < ( k : ℝ ) ) |>.2 h_base using 1 ; rw [ Real.rpow_sub_one ( by positivity ) ];
  refine le_trans ( Real.rpow_le_rpow ( ?_ ) h_base.le ( ?_ ) ) ?_;
  · unfold lamLarge; positivity;
  · positivity;
  · rw [ ← Real.rpow_mul ( by positivity ), mul_comm ];
    rw [ Real.rpow_def_of_pos ( by positivity ), Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf at * ; norm_num at *;
    field_simp at *;
    rw [ le_div_iff₀ ( Real.log_pos hlog1 ) ] at hrconv ; nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast ]

/-
The Konyagin estimate on the large range is eventually dominated by
`C · k^θ / log k`.
-/
lemma large_asym (C : ℝ) (hC : 0 < C) : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ, ∀ r : ℕ,
    3 ≤ r → 0 < n →
    (k : ℝ) ^ (((r : ℝ) - 1) + theta) < (n : ℝ) * (Nat.factorial (r - 1) : ℝ) →
    (3 * (r : ℝ) - 2) < 7 * (1 / 20) * Real.log k / Real.log (Real.log k) →
    ((r : ℝ) + 1) ≤ (k : ℝ) ^ (theta / (r : ℝ)) →
    (r : ℝ) ≤ 3 * (1 / 20) * Real.log k / Real.log (Real.log k) →
    (r : ℝ) ≤ Real.log k →
    c₆ * (k : ℝ) ^ theta *
        (2 * (k : ℝ) ^ ((theta - 1) / (3 * (r : ℝ) - 2)) +
          (((r : ℝ) + 1) * lamLarge k n r / (k : ℝ)) ^ ((2 * (r : ℝ))⁻¹)) +
      2 * (r : ℝ) * lamLarge k n r ≤ C * (k : ℝ) ^ theta / Real.log k := by
  revert hC;
  intro hC_pos
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    2 * c₆ * (k : ℝ) ^ theta * (Real.log k) ^ (-(19 : ℝ) / 14) +
    c₆ * (k : ℝ) ^ theta * (Real.log k) ^ (-(10 : ℝ) / 9) +
    2 * (k : ℝ) ^ ((2 - theta) / 3) * (Real.log k) ^ (1 : ℝ) ≤ C * (k : ℝ) ^ theta / Real.log k := by
      obtain ⟨k₀₁, hk₀₁⟩ : ∃ k₀₁ : ℕ, ∀ k : ℕ, k₀₁ ≤ k →
          2 * c₆ * (k : ℝ) ^ theta * (Real.log k) ^ (-(19 : ℝ) / 14) ≤ C / 3 * (k : ℝ) ^ theta / Real.log k := by
            have := poly_log_lt_logpow ( 2 * c₆ ) theta ( -19 / 14 ) ( by norm_num ) ( C / 3 ) ( by linarith ) ; aesop;
      obtain ⟨k₀₂, hk₀₂⟩ : ∃ k₀₂ : ℕ, ∀ k : ℕ, k₀₂ ≤ k →
          c₆ * (k : ℝ) ^ theta * (Real.log k) ^ (-(10 : ℝ) / 9) ≤ C / 3 * (k : ℝ) ^ theta / Real.log k := by
            have := poly_log_lt_logpow ( c₆ ) theta ( - ( 10 : ℝ ) / 9 ) ( by norm_num ) ( C / 3 ) ( by linarith ) ; aesop;
      obtain ⟨k₀₃, hk₀₃⟩ : ∃ k₀₃ : ℕ, ∀ k : ℕ, k₀₃ ≤ k →
          2 * (k : ℝ) ^ ((2 - theta) / 3) * (Real.log k) ^ (1 : ℝ) ≤ C / 3 * (k : ℝ) ^ theta / Real.log k := by
            have := poly_log_lt ( 2 : ℝ ) ( ( 2 - theta ) / 3 ) 1 theta ( by linarith [ show theta > 1 / 2 by norm_num [ theta ] ] ) ( C / 3 ) ( by linarith ) ; aesop;
      exact ⟨ Max.max k₀₁ ( Max.max k₀₂ k₀₃ ), fun k hk => by convert add_le_add_three ( hk₀₁ k ( le_trans ( le_max_left _ _ ) hk ) ) ( hk₀₂ k ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hk ) ) ( hk₀₃ k ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hk ) ) using 1 ; ring ⟩;
  refine' ⟨ k₀ + 2, fun k hk n r hr hn hmin h3r2 hrk hrconv hrlog => le_trans _ ( hk₀ k ( by linarith ) ) ⟩;
  refine' add_le_add _ _;
  · refine' le_trans ( mul_le_mul_of_nonneg_left ( add_le_add ( mul_le_mul_of_nonneg_left ( large_term1_le k r ( by linarith ) ( by linarith ) ( by
      linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) ( by
      exact h3r2 ) ) zero_le_two ) ( large_term3_le k n r ( by linarith ) ( by linarith ) ( by linarith ) ( by
      linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) ( by
      convert hmin using 1 ) ( by
      exact_mod_cast hrk ) ( by
      exact hrconv ) ) ) ( by
      exact mul_nonneg ( by unfold c₆; norm_num [ B_const, K_const, C₀_const ] ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ) _;
    linarith;
  · have h_lamLarge_lt : lamLarge k n r < (k : ℝ) ^ ((2 - theta) / 3) := by
      refine' lt_of_lt_of_le ( lamLarge_lt k n r hn ( by linarith ) hr hmin ) _;
      exact Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( by rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast, show ( theta : ℝ ) > 0 by exact_mod_cast theta_pos, show ( theta : ℝ ) < 1 by exact_mod_cast theta_lt_one ] );
    norm_num at *;
    nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast, show ( k : ℝ ) ^ ( ( 2 - theta ) / 3 : ℝ ) ≥ 0 by positivity ]

/-
`log k / log log k → ∞`.
-/
lemma tendsto_log_div_loglog_atTop :
    Filter.Tendsto (fun k : ℕ => Real.log k / Real.log (Real.log k)) Filter.atTop Filter.atTop := by
  -- We'll use the change of variables $u = \log k$.
  suffices h_log : Filter.Tendsto (fun u : ℝ => u / Real.log u) Filter.atTop Filter.atTop by
    exact h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
  -- We can use the change of variables $v = \log u$ to transform the limit expression.
  suffices h_log : Filter.Tendsto (fun v : ℝ => Real.exp v / v) Filter.atTop Filter.atTop by
    have := h_log.comp Real.tendsto_log_atTop;
    exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
  simpa using Real.tendsto_exp_div_pow_atTop 1

/-- The reference exponent `r₀ = ⌈log k / (10 log log k)⌉`. -/
def r0L (k : ℕ) : ℕ := ⌈Real.log k / (10 * Real.log (Real.log k))⌉₊

/-
Bounds on the reference exponent `r₀`.
-/
lemma large_r0_bounds : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    1 ≤ r0L k ∧
    3 * (r0L k : ℝ) - 2 < 7 * (1 / 20) * Real.log k / Real.log (Real.log k) ∧
    (r0L k : ℝ) ≤ 3 * (1 / 20) * Real.log k / Real.log (Real.log k) ∧
    (r0L k : ℝ) ≤ Real.log k ∧
    (r0L k : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (1 - theta) ∧
    (r0L k : ℝ) + 1 ≤ (k : ℝ) ^ (theta / (r0L k : ℝ)) := by
  -- By combining the results from the provided solution, we can choose a sufficiently large $k₀$ such that all conditions hold.
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    100 ≤ Real.log k ∧ 200 ≤ Real.log k / Real.log (Real.log k) ∧ Real.log k ≤ (1/2) * (k:ℝ)^(1-theta) := by
      obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k → 100 ≤ Real.log k := by
        exact ⟨ Nat.ceil ( Real.exp 100 ), fun k hk => by simpa using Real.log_le_log ( by positivity ) ( Nat.ceil_le.mp hk ) ⟩
      obtain ⟨k₂, hk₂⟩ : ∃ k₂ : ℕ, ∀ k : ℕ, k₂ ≤ k → 200 ≤ Real.log k / Real.log (Real.log k) := by
        have := tendsto_log_div_loglog_atTop.eventually_ge_atTop 200; aesop;
      obtain ⟨k₃, hk₃⟩ : ∃ k₃ : ℕ, ∀ k : ℕ, k₃ ≤ k → Real.log k ≤ (1/2) * (k:ℝ)^(1-theta) := by
        have := isLittleO_log_rpow_atTop ( show ( 0 : ℝ ) < 1 - theta by norm_num [ theta ] );
        rw [ Asymptotics.isLittleO_iff ] at this;
        obtain ⟨ k₃, hk₃ ⟩ := Filter.eventually_atTop.mp ( this ( show 0 < ( 1 / 2 : ℝ ) by norm_num ) ) ; use ⌈k₃⌉₊ + 1; intros k hk; specialize hk₃ k ( Nat.le_of_ceil_le ( by linarith ) ) ; rw [ Real.norm_of_nonneg ( Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ), Real.norm_of_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ] at hk₃; linarith;
      use max k₁ (max k₂ k₃);
      grind;
  refine' ⟨ k₀ + 3, fun k hk => _ ⟩ ; specialize hk₀ k ( by linarith ) ; norm_num [ r0L ] at *;
  refine' ⟨ _, _, _, _, _, _ ⟩;
  any_goals ring_nf at *; nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ Real.log k / ( 10 * Real.log ( Real.log k ) ) by exact div_nonneg ( by linarith ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith ) ) ) ) ];
  · ring_nf at *;
    linarith [ Nat.ceil_lt_add_one ( show 0 ≤ Real.log k * ( Real.log ( Real.log k ) ) ⁻¹ * ( 1 / 10 ) by exact mul_nonneg ( mul_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( by linarith ) ) ) ) ( by norm_num ) ) ];
  · rw [ le_div_iff₀ ( Real.log_pos <| show 1 < Real.log k from by linarith ) ] at *;
    nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ Real.log k / ( 10 * Real.log ( Real.log k ) ) by exact div_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith ) ) ) ), Real.log_pos ( show 1 < Real.log k from by linarith ), mul_div_cancel₀ ( Real.log k ) ( show ( 10 * Real.log ( Real.log k ) ) ≠ 0 by linarith [ Real.log_pos ( show 1 < Real.log k from by linarith ) ] ) ];
  · refine' le_trans ( Nat.ceil_lt_add_one _ |> le_of_lt ) _;
    · exact div_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith ) ) );
    · rw [ div_add_one, div_le_iff₀ ] <;> nlinarith [ show 1 ≤ Real.log ( Real.log k ) from by rw [ Real.le_log_iff_exp_le ( by linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ];
  · refine' le_trans ( Nat.ceil_lt_add_one ( by exact div_nonneg ( by linarith ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith ) ) ) ) |> le_of_lt ) _;
    rw [ div_add_one, div_le_iff₀ ] <;> nlinarith [ show 1 ≤ Real.log ( Real.log k ) from by rw [ Real.le_log_iff_exp_le ( by linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ];
  · -- We'll use that $Real.exp M \leq Real.exp (theta * L / (r0L k))$ since $M \leq theta * L / (r0L k)$.
    have h_exp : Real.exp (Real.log (Real.log k)) ≤ Real.exp (theta * Real.log k / (Nat.ceil (Real.log k / (10 * Real.log (Real.log k)))) ) := by
      refine' Real.exp_le_exp.mpr _;
      rw [ le_div_iff₀ ];
      · have hM_le : (Nat.ceil (Real.log k / (10 * Real.log (Real.log k)))) * Real.log (Real.log k) < theta * Real.log k := by
          have hM_le : (Real.log k / (10 * Real.log (Real.log k)) + 1) * Real.log (Real.log k) < theta * Real.log k := by
            rw [ div_add_one, div_mul_eq_mul_div, div_lt_iff₀ ] <;> norm_num [ theta ];
            · rw [ le_div_iff₀ ] at hk₀ <;> nlinarith [ Real.log_pos ( show 1 < Real.log k from by linarith ) ];
            · exact Real.log_pos ( by linarith );
            · exact ⟨ ⟨ by linarith, by linarith, by linarith ⟩, by linarith, by linarith ⟩;
          exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_right ( Nat.ceil_lt_add_one ( by exact div_nonneg ( by linarith ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith ) ) ) ) |> le_of_lt ) ( Real.log_nonneg ( by linarith ) ) ) hM_le;
        linarith;
      · exact Nat.cast_pos.mpr ( Nat.ceil_pos.mpr ( div_pos ( by linarith ) ( mul_pos ( by norm_num ) ( Real.log_pos ( by linarith ) ) ) ) );
    rw [ Real.exp_log ( Real.log_pos <| by norm_cast; linarith ) ] at h_exp;
    -- Since $\lceil x \rceil + 1 \leq L$, we have $\lceil x \rceil + 1 \leq \exp(\theta \cdot L / \lceil x \rceil)$.
    have h_ceil : (⌈Real.log k / (10 * Real.log (Real.log k))⌉₊ : ℝ) + 1 ≤ Real.log k := by
      have := Nat.ceil_lt_add_one ( show 0 ≤ Real.log k / ( 10 * Real.log ( Real.log k ) ) by exact div_nonneg ( by linarith ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith ) ) ) );
      rw [ div_add_one, lt_div_iff₀ ] at this <;> nlinarith [ show 1 ≤ Real.log ( Real.log k ) from by rw [ Real.le_log_iff_exp_le ( by linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ];
    convert h_ceil.trans h_exp using 1;
    rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) ] ; ring_nf

/-
The reference exponent `r₀` satisfies the Konyagin admissibility `n r₀! ≤ k^{r₀+θ}`.
-/
lemma large_r0_P : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ, 0 < n →
    (n : ℝ) ≤ Real.exp ((Real.log k) ^ 2 / (20 * Real.log (Real.log k))) →
    (n : ℝ) * (Nat.factorial (r0L k) : ℝ) ≤ (k : ℝ) ^ ((r0L k : ℝ) + theta) := by
  -- For sufficiently large $k$, we have $L \geq 6M$.
  obtain ⟨k₀₁, hk₀₁⟩ : ∃ k₀₁ : ℕ, ∀ k : ℕ, k₀₁ ≤ k → Real.log k ≥ 10 ∧ Real.log (Real.log k) ≥ 1 ∧ Real.log k ≥ 6 * Real.log (Real.log k) := by
    have h_log_log : Filter.Tendsto (fun k : ℕ => Real.log k / Real.log (Real.log k)) Filter.atTop Filter.atTop :=
      tendsto_log_div_loglog_atTop
    have h_log_log : ∃ k₀₁ : ℕ, ∀ k : ℕ, k₀₁ ≤ k → Real.log k ≥ 10 ∧ Real.log (Real.log k) ≥ 1 := by
      have h_log_log : Filter.Tendsto (fun k : ℕ => Real.log k) Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun k : ℕ => Real.log (Real.log k)) Filter.atTop Filter.atTop := by
        exact ⟨ Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop, Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ⟩;
      exact Filter.eventually_atTop.mp ( h_log_log.1.eventually_ge_atTop 10 |> Filter.Eventually.and <| h_log_log.2.eventually_ge_atTop 1 );
    have := ‹Tendsto ( fun k : ℕ => Real.log k / Real.log ( Real.log k ) ) Filter.atTop Filter.atTop›.eventually_gt_atTop 6;
    obtain ⟨ k₀₁, hk₀₁ ⟩ := Filter.eventually_atTop.mp this; obtain ⟨ k₀₂, hk₀₂ ⟩ := h_log_log; exact ⟨ Max.max k₀₁ k₀₂, fun k hk => ⟨ hk₀₂ k ( le_trans ( le_max_right _ _ ) hk ) |>.1, hk₀₂ k ( le_trans ( le_max_right _ _ ) hk ) |>.2, by have := hk₀₂ k ( le_trans ( le_max_right _ _ ) hk ) |>.1; have := hk₀₂ k ( le_trans ( le_max_right _ _ ) hk ) |>.2; have := hk₀₁ k ( le_trans ( le_max_left _ _ ) hk ) ; rw [ lt_div_iff₀ ] at this <;> linarith ⟩ ⟩ ;
  use k₀₁ + 2;
  intros k hk n hn h_exp
  have h_log_bound : (Real.log k) ^ 2 / (20 * Real.log (Real.log k)) + (r0L k : ℝ) * Real.log (Real.log k) ≤ (r0L k : ℝ) * Real.log k := by
    have h_log_bound : (r0L k : ℝ) ≥ Real.log k / (10 * Real.log (Real.log k)) := by
      exact Nat.le_ceil _;
    rw [ ge_iff_le, div_le_iff₀ ] at h_log_bound <;> nlinarith [ hk₀₁ k ( by linarith ), Real.log_pos ( show ( k : ℝ ) > 1 by norm_cast; linarith ), Real.log_pos ( show ( Real.log k : ℝ ) > 1 by linarith [ hk₀₁ k ( by linarith ) ] ), mul_div_cancel₀ ( Real.log k ^ 2 ) ( by linarith [ hk₀₁ k ( by linarith ) ] : ( 20 * Real.log ( Real.log k ) ) ≠ 0 ) ];
  have h_log_bound : Real.log (n : ℝ) + Real.log (Nat.factorial (r0L k) : ℝ) ≤ (r0L k : ℝ) * Real.log k + theta * Real.log k := by
    have h_log_bound : Real.log (Nat.factorial (r0L k) : ℝ) ≤ (r0L k : ℝ) * Real.log (r0L k) := by
      rw [ ← Real.log_pow ] ; gcongr ; norm_cast ; exact Nat.recOn ( r0L k ) ( by norm_num ) fun n ihn => by rw [ Nat.factorial_succ, pow_succ' ] ; exact le_trans ( Nat.mul_le_mul_left _ ihn ) ( by gcongr ; linarith ) ;
    have h_log_bound : Real.log (n : ℝ) ≤ (Real.log k) ^ 2 / (20 * Real.log (Real.log k)) := by
      exact Real.log_le_iff_le_exp ( by positivity ) |>.2 h_exp;
    have h_log_bound : Real.log (r0L k : ℝ) ≤ Real.log (Real.log k) := by
      gcongr;
      · exact Nat.cast_pos.mpr ( Nat.ceil_pos.mpr ( div_pos ( Real.log_pos ( by norm_cast; linarith ) ) ( mul_pos ( by norm_num ) ( Real.log_pos ( show 1 < Real.log k from by linarith [ hk₀₁ k ( by linarith ) ] ) ) ) ) );
      · have := Nat.ceil_lt_add_one ( show 0 ≤ Real.log k / ( 10 * Real.log ( Real.log k ) ) by exact div_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith [ hk₀₁ k ( by linarith ) ] ) ) ) );
        exact le_trans this.le ( by rw [ div_add_one, div_le_iff₀ ] <;> nlinarith [ hk₀₁ k ( by linarith ) ] );
    nlinarith [ show 0 ≤ theta * Real.log k from mul_nonneg ( by norm_num [ theta ] ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ];
  rw [ ← Real.log_le_log_iff ( by positivity ) ( by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( Nat.cast_pos.mpr <| by linarith ) ] ; linarith

/-
Existence of the minimal `r` with `n r! ≤ k^{r+θ}` and all its bounds.
-/
lemma large_r_data : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ,
    (1 / 2) * (k : ℝ) ^ (2 + theta) < (n : ℝ) →
    (n : ℝ) ≤ Real.exp ((Real.log k) ^ 2 / (20 * Real.log (Real.log k))) →
    ∃ r : ℕ, 3 ≤ r ∧ (r : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (1 - theta) ∧
      (n : ℝ) * (Nat.factorial r : ℝ) ≤ (k : ℝ) ^ ((r : ℝ) + theta) ∧
      (k : ℝ) ^ (((r : ℝ) - 1) + theta) < (n : ℝ) * (Nat.factorial (r - 1) : ℝ) ∧
      (3 * (r : ℝ) - 2) < 7 * (1 / 20) * Real.log k / Real.log (Real.log k) ∧
      ((r : ℝ) + 1) ≤ (k : ℝ) ^ (theta / (r : ℝ)) ∧
      (r : ℝ) ≤ 3 * (1 / 20) * Real.log k / Real.log (Real.log k) ∧
      (r : ℝ) ≤ Real.log k := by
  obtain ⟨kb, hb⟩ := large_r0_bounds
  obtain ⟨kp, hp⟩ := large_r0_P
  use max (max kb kp) 2;
  intro k hk n hn hn'; rcases lt_trichotomy n 0 with hn0 | rfl | hn0 <;> norm_num at *;
  · linarith [ show ( n : ℝ ) < 0 by exact_mod_cast hn0, show ( 0 : ℝ ) ≤ k ^ ( 2 + theta ) by positivity ];
  · exact False.elim <| hn.not_ge <| by positivity;
  · refine' ⟨ Nat.find ( show ∃ r : ℕ, ( n : ℝ ) * r.factorial ≤ k ^ ( r + theta ) from ⟨ r0L k, hp k hk.2.1 n hn0 hn' ⟩ ), _, _, _, _, _ ⟩ <;> norm_num at *;
    · intro m hm; interval_cases m <;> norm_num at * <;> try linarith;
      · refine' lt_of_le_of_lt _ hn;
        rw [ show ( 2 + theta : ℝ ) = theta + 2 by ring, Real.rpow_add ] <;> norm_num <;> try linarith;
        nlinarith [ show ( k : ℝ ) ^ theta > 0 by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _, show ( k : ℝ ) ^ 2 ≥ 4 by norm_cast; nlinarith ];
      · rw [ show ( 2 + theta : ℝ ) = 1 + theta + 1 by ring, Real.rpow_add ] at hn <;> norm_num at * <;> try linarith;
        nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast; linarith, show ( k : ℝ ) ^ ( 1 + theta ) > 0 by exact Real.rpow_pos_of_pos ( by norm_cast; linarith ) _ ];
    · exact le_trans ( Nat.cast_le.mpr <| Nat.find_min' _ <| hp k hk.2.1 n hn0 hn' ) <| hb k hk.1 |>.2.2.2.2.1;
    · exact Nat.find_spec ( ⟨ r0L k, hp k hk.2.1 n hn0 hn' ⟩ : ∃ r : ℕ, ( n : ℝ ) * r.factorial ≤ k ^ ( r + theta ) );
    · have := Nat.find_min ( show ∃ r : ℕ, ( n : ℝ ) * r.factorial ≤ k ^ ( r + theta ) from ⟨ r0L k, hp k hk.2.1 n hn0 hn' ⟩ ) ( show Nat.find ( show ∃ r : ℕ, ( n : ℝ ) * r.factorial ≤ k ^ ( r + theta ) from ⟨ r0L k, hp k hk.2.1 n hn0 hn' ⟩ ) - 1 < Nat.find ( show ∃ r : ℕ, ( n : ℝ ) * r.factorial ≤ k ^ ( r + theta ) from ⟨ r0L k, hp k hk.2.1 n hn0 hn' ⟩ ) from Nat.sub_lt ( Nat.pos_of_ne_zero ( by
                                                                                                                                                                                                                                                                      norm_num [ Nat.find_eq_zero ];
                                                                                                                                                                                                                                                                      refine' lt_of_le_of_lt _ hn;
                                                                                                                                                                                                                                                                      rw [ Real.rpow_add ] <;> norm_num <;> try linarith;
                                                                                                                                                                                                                                                                      nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast; linarith, show ( k : ℝ ) ^ theta > 0 by exact Real.rpow_pos_of_pos ( by norm_cast; linarith ) _, show ( k : ℝ ) ^ 2 ≥ 4 by norm_cast; nlinarith ] ) ) zero_lt_one ) ; norm_num at *;
      convert this using 2 ; rw [ Nat.cast_sub ] <;> norm_num;
      refine' lt_of_le_of_lt _ hn;
      rw [ show ( 2 + theta : ℝ ) = theta + 2 by ring, Real.rpow_add ] <;> norm_num <;> try linarith;
      nlinarith [ show ( k : ℝ ) ^ theta > 0 by exact Real.rpow_pos_of_pos ( by norm_cast; linarith ) _, show ( k : ℝ ) ^ 2 ≥ 4 by norm_cast; nlinarith ];
    · refine' ⟨ _, _, _, _ ⟩;
      · refine' lt_of_le_of_lt _ ( hb k hk.1 |>.2.1 );
        gcongr;
        exact Nat.find_min' _ ( hp k hk.2.1 n hn0 hn' );
      · refine' le_trans _ ( Real.rpow_le_rpow_of_exponent_le _ <| div_le_div_of_nonneg_left _ _ <| Nat.cast_le.mpr <| Nat.find_le _ ) <;> norm_num [ hb k hk.1 ];
        any_goals exact r0L k;
        · refine' le_trans _ ( hb k hk.1 |>.2.2.2.2.2 );
          gcongr;
          exact Nat.find_min' _ ( hp k hk.2.1 n hn0 hn' );
        · linarith;
        · exact le_of_lt ( by norm_num : ( 0 : ℝ ) < 21 / 40 );
        · refine' lt_of_le_of_lt _ hn;
          rw [ show ( 2 + theta : ℝ ) = theta + 2 by ring, Real.rpow_add ] <;> norm_num <;> try linarith;
          nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast; linarith, show ( k : ℝ ) ^ theta > 0 by exact Real.rpow_pos_of_pos ( by norm_cast; linarith ) _, show ( k : ℝ ) ^ 2 ≥ 4 by norm_cast; nlinarith ];
        · exact hp k hk.2.1 n hn0 hn';
      · exact le_trans ( Nat.cast_le.mpr ( Nat.find_min' _ ( hp k hk.2.1 n hn0 hn' ) ) ) ( hb k hk.1 |>.2.2.1 );
      · exact le_trans ( Nat.cast_le.mpr ( Nat.find_min' _ ( hp k hk.2.1 n hn0 hn' ) ) ) ( hb k hk.1 |>.2.2.2.1 )

/-- **Large `n`:** `½ k^{2+θ} < n ≤ exp(log²k / (20 log log k))`. -/
lemma case_large : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ,
    (1 / 2) * (k : ℝ) ^ (2 + theta) < (n : ℝ) →
    (n : ℝ) ≤ Real.exp ((Real.log k) ^ 2 / (20 * Real.log (Real.log k))) →
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) < p ∧ (p : ℝ) < (k : ℝ) + 3 * (k : ℝ) ^ theta ∧
      (p : ℤ) ∣ Pprod k n := by
  obtain ⟨C, hC, kb, hb⟩ := bhp
  obtain ⟨k1, hasym⟩ := large_asym C hC
  obtain ⟨k2, hrdata⟩ := large_r_data
  refine ⟨max (max kb k1) (max k2 2), ?_⟩
  intro k hk n hlow hhigh
  have hkb : kb ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hki1 : k1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hki2 : k2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk2le : 2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hk1 : 1 ≤ k := by omega
  have hk1' : 1 < k := by omega
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk1'
  -- `n > 0` and `(k:ℤ) < n`
  have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2le
  have hkpow : (k : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (2 + theta) := by
    have h1 : (k : ℝ) ^ (2 + theta) = (k : ℝ) ^ 2 * (k : ℝ) ^ theta := by
      rw [show (2 + theta : ℝ) = (2 : ℕ) + theta by norm_num,
        Real.rpow_add (by linarith), Real.rpow_natCast]
    have h2 : (1 : ℝ) ≤ (k : ℝ) ^ theta :=
      Real.one_le_rpow (le_of_lt hkR) (le_of_lt theta_pos)
    rw [h1]
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (by linarith : (0:ℝ) ≤ (k : ℝ) ^ theta - 1)]
  have hknR : (k : ℝ) < (n : ℝ) := lt_of_le_of_lt hkpow hlow
  have hkn : (k : ℤ) < n := by exact_mod_cast hknR
  have hn0 : 0 < n := lt_trans (by exact_mod_cast hk1) hkn
  obtain ⟨r, hr3, hrle, hub, hmin, h3r2, hrk, hrconv, hrlog⟩ :=
    hrdata k hki2 n hlow hhigh
  have hraw := large_card_raw k n r hk1' hn0 hr3 hrle hkn hub
  have hbnd := hasym k hki1 n r hr3 hn0 hmin h3r2 hrk hrconv hrlog
  have hbhp : C * (k : ℝ) ^ theta / Real.log k ≤
      (primeCard (k : ℝ) ((k : ℝ) + (k : ℝ) ^ theta) : ℝ) := by
    exact hb k hkb
  exact konyagin_finish k n hk1 C hbhp (lt_of_lt_of_le hraw hbnd)

/-- **Main theorem.** For all sufficiently large `k` and all `n` with
`2k < n ≤ exp(log²k / (20 log log k))`, the product `(n-k)⋯(n-1)` is
divisible by some prime `p ∈ (k, k + 3 k^θ)`. -/
theorem main_theorem : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℤ,
    2 * (k : ℤ) < n →
    (n : ℝ) ≤ Real.exp ((Real.log k) ^ 2 / (20 * Real.log (Real.log k))) →
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) < p ∧ (p : ℝ) < (k : ℝ) + 3 * (k : ℝ) ^ theta ∧
      (p : ℤ) ∣ Pprod k n := by
  obtain ⟨k1, h1⟩ := case_small
  obtain ⟨k2, h2⟩ := case_medium
  obtain ⟨k3, h3⟩ := case_mediumlarge
  obtain ⟨k4, h4⟩ := case_large
  refine ⟨max (max k1 k2) (max k3 k4), ?_⟩
  intro k hk n hn1 hn2
  have hk1 : k1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk2 : k2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hk3 : k3 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk4 : k4 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  by_cases c1 : (n : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (2 - theta)
  · exact h1 k hk1 n hn1 c1
  · push_neg at c1
    by_cases c2 : (n : ℝ) ≤ (k : ℝ) ^ 2 / (Real.log k) ^ 2
    · exact h2 k hk2 n c1 c2
    · push_neg at c2
      by_cases c3 : (n : ℝ) ≤ (1 / 2) * (k : ℝ) ^ (2 + theta)
      · exact h3 k hk3 n c2 c3
      · push_neg at c3
        exact h4 k hk4 n c3 hn2

end

#print axioms main_theorem
