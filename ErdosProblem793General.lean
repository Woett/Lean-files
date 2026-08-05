import Mathlib

/-!
Let `k` be a fixed integer, and let `F_k(n)` be defined as the size of the
largest set `A ⊆ {1, …, n}` with the property that for every `a ∈ A`, there are
no `k` elements `b₁, …, b_k ∈ A \ {a}` with `a ∣ b₁ ⋯ b_k`.  Erdős
conjectured that there exists a constant `c_k` such that

`F_k(n) = π(n) + (c_k + o(1))n^{2/(k+1)}/(log n)²` as `n → ∞`.

This is a generalization of Erdős Problem 793 (https://www.erdosproblems.com/793).

Below you can find a formalization, obtained by Aristotle from Harmonic
(aristotle-harmonic@harmonic.fun), that such a `c_k` indeed exists, and that
we furthermore have `c_k → e^2` as `k → ∞`.

Because our main theorem requires some definitions to be set up, at the end I
added the following two corollaries, which are completely self-contained and
can be checked without verifying the other 10k+ lines:

Theorem large_k_upper:
For every `ε > 0` there is a `K` such that for every `k ≥ K` there is an `N`
such that for all `n ≥ N`, every set `A ⊆ {1, …, n}` with
`|A| ≥ π(n) + (e² + ε)·n^{2/(k+1)}/(log n)²` contains `k + 1` distinct elements
`a, b₁, …, b_k` with `a ∣ b₁ ⋯ b_k`.

Theorem large_k_lower:
For every `ε > 0` there is a `K` such that for every `k ≥ K` there is an `N`
such that for all `n ≥ N` there is a set `A ⊆ {1, …, n}` with
`|A| ≥ π(n) + (e² - ε)·n^{2/(k+1)}/(log n)²` and for which `a ∣ b₁ ⋯ b_k`
implies `a = b_i` for some `i`.

We note that the upper bound result is slightly stronger than required, as we
can even guarantee that all the `b_i` are distinct.

The formalization, which was based on a write-up by ChatGPT, depends on two
external axioms. We first of all use the prime number theorem as it is stated
in the PNT+ Project.

https://github.com/AlexKontorovich/PrimeNumberTheoremAnd

Secondly, we assume a hypergraph matching theorem of Delcourt and Postle. This
is Theorem 1.11 in the following paper.

M. Delcourt and L. Postle, Finding an almost perfect matching in a hypergraph
avoiding forbidden submatchings. arXiv:2204.08981 (2022).

PNT is used in both the lower and the upper bound. The hypergraph matching
theorem is only required for the lower bound.

Lean version: leanprover/lean4:v4.28.0
-/

open Filter Topology Real MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option maxHeartbeats 4000000

/-- Prime number theorem. -/
axiom pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x

/-- **Delcourt–Postle, empty-configuration specialization**.
For every integer `q ≥ 2` there is a threshold `D_q` such that for all `D ≥ D_q`,
any bipartite `q`-bounded multi-hypergraph with codegrees at most `(log D)²`,
every `A`-vertex of degree at least `(1 + D^{-1/(20q)}) D`, and every `B`-vertex
of degree at most `D`, has an `A`-perfect matching.  Black box. -/
axiom DP_empty (q : ℕ) (hq : 2 ≤ q) :
    ∃ Dq : ℝ, ∀ D : ℝ, Dq ≤ D →
      ∀ (A B E : Type) [Fintype A] [Fintype B] [Fintype E] [DecidableEq A] [DecidableEq B]
        (aV : E → A) (bV : E → Finset B),
        (∀ e, 1 + (bV e).card ≤ q) →
        (∀ (v : A) (w : B),
          ((Finset.univ.filter (fun e => aV e = v ∧ w ∈ bV e)).card : ℝ) ≤ (Real.log D) ^ 2) →
        (∀ (w w' : B), w ≠ w' →
          ((Finset.univ.filter (fun e => w ∈ bV e ∧ w' ∈ bV e)).card : ℝ) ≤ (Real.log D) ^ 2) →
        (∀ v : A,
          (1 + D ^ (-(1 : ℝ) / (20 * q))) * D ≤
            ((Finset.univ.filter (fun e => aV e = v)).card : ℝ)) →
        (∀ w : B, ((Finset.univ.filter (fun e => w ∈ bV e)).card : ℝ) ≤ D) →
        ∃ M : Finset E,
          (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → aV e ≠ aV e' ∧ Disjoint (bV e) (bV e')) ∧
          (∀ v : A, ∃ e ∈ M, aV e = v)

/-! ## Core definitions -/

/-- `A` is repeated-factor `k`-primitive: for every `a ∈ A` and every choice
`b₁, …, b_k ∈ A \ {a}` (repetitions allowed), `a ∤ b₁ ⋯ b_k`. -/
def RepPrimitive (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ f : Fin k → ℕ, (∀ i, f i ∈ A.erase a) → ¬ (a ∣ ∏ i, f i)

/-- `A` is distinct-factor `k`-primitive: for every `a ∈ A` and every subset
`B ⊆ A \ {a}` with `|B| = k`, `a ∤ ∏_{b ∈ B} b`. -/
def DistPrimitive (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ B : Finset ℕ, B ⊆ A.erase a → B.card = k → ¬ (a ∣ ∏ b ∈ B, b)

/--
Every repeated-factor `k`-primitive set is distinct-factor `k`-primitive.
-/
theorem RepPrimitive.distPrimitive {k : ℕ} {A : Finset ℕ}
    (h : RepPrimitive k A) : DistPrimitive k A := by
  intro a ha B hB_sub hB_card;
  obtain ⟨f, hf⟩ : ∃ f : Fin k → ℕ, (∀ i, f i ∈ B) ∧ Function.Injective f ∧ B = Finset.image f (Finset.univ : Finset (Fin k)) := by
    obtain ⟨f, hf⟩ : ∃ f : Fin k → ℕ, (∀ i, f i ∈ B) ∧ Function.Injective f := by
      exact ⟨ fun i => B.orderEmbOfFin ( by aesop ) i, fun i => by aesop, fun i j hij => by simpa [ Fin.ext_iff ] using hij ⟩;
    exact ⟨ f, hf.1, hf.2, by rw [ Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hf.1 i ) ( by rw [ Finset.card_image_of_injective _ hf.2, Finset.card_fin, hB_card ] ) ] ⟩;
  rw [ hf.2.2, Finset.prod_image <| by tauto ];
  exact h a ha f fun i => hB_sub ( hf.1 i )

/-- The maximal size of a repeated-factor `k`-primitive subset of `[n] = {1,…,n}`. -/
noncomputable def Fkrep (k n : ℕ) : ℕ :=
  sSup {m | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ RepPrimitive k A ∧ A.card = m}

/-- The maximal size of a distinct-factor `k`-primitive subset of `[n] = {1,…,n}`. -/
noncomputable def Fkdist (k n : ℕ) : ℕ :=
  sSup {m | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ DistPrimitive k A ∧ A.card = m}

/-- The number of dyadic bins at level `Q`: `N_Q = Q · 2^Q`. -/
def NQ (Q : ℕ) : ℕ := Q * 2 ^ Q

/-- The dyadic mesh at level `Q`: `d_Q = 2^{-Q}`. -/
noncomputable def dQ (Q : ℕ) : ℝ := (1 : ℝ) / 2 ^ Q

/--
Refining the dyadic grid halves its mesh.
-/
theorem dQ_succ (Q : ℕ) : dQ (Q + 1) = dQ Q / 2 := by
  unfold dQ; ring;

/-- The (finite) set of level-`Q` `r`-types: functions `J_Q → ℕ` summing to `r`. -/
def types (r Q : ℕ) : Finset (Fin (NQ Q) → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (r + 1))).filter (fun t => ∑ j, t j = r)

/-- Admissibility of a type: `∏_j (j+1)^{τ(j)} ≤ 2^{Qr}`. -/
def admissible (r Q : ℕ) (t : Fin (NQ Q) → ℕ) : Prop :=
  ∏ j, (j.val + 1) ^ (t j) ≤ 2 ^ (Q * r)

noncomputable instance (r Q : ℕ) : DecidablePred (admissible r Q) := fun _ => Classical.dec _

/-- The finite set `𝒜_{r,Q}` of admissible level-`Q` `r`-types. -/
noncomputable def admTypes (r Q : ℕ) : Finset (Fin (NQ Q) → ℕ) :=
  (types r Q).filter (admissible r Q)

/-- The value `val_Q(z) = ∑_τ z_τ` of a level-`Q` weighting. -/
noncomputable def valQ (r Q : ℕ) (z : (Fin (NQ Q) → ℕ) → ℝ) : ℝ :=
  ∑ t ∈ admTypes r Q, z t

/-- A nonnegative weighting `z` satisfying the off-diagonal and diagonal
  capacity constraints. -/
def IsPacking (r Q : ℕ) (z : (Fin (NQ Q) → ℕ) → ℝ) : Prop :=
  (∀ t, 0 ≤ z t) ∧
  (∀ i j : Fin (NQ Q), i < j →
      ∑ t ∈ admTypes r Q, ((t i : ℝ) * t j) * z t ≤ (r : ℝ) ^ 2 * dQ Q ^ 2) ∧
  (∀ i : Fin (NQ Q),
      ∑ t ∈ admTypes r Q, ((t i).choose 2 : ℝ) * z t ≤ (r : ℝ) ^ 2 / 2 * dQ Q ^ 2)

/-- `λ_{r,Q}`: the supremum of `val_Q` over level-`Q` packings. -/
noncomputable def lamQ (r Q : ℕ) : ℝ :=
  sSup {v | ∃ z, IsPacking r Q z ∧ valQ r Q z = v}

/-- The dyadic packing constant `Λ_r = sup_{Q ≥ 1} λ_{r,Q}`. -/
noncomputable def Lam (r : ℕ) : ℝ :=
  sSup {v | ∃ Q, 1 ≤ Q ∧ lamQ r Q = v}

/-! ## Elementary analytic preliminaries -/

/--
For `a > 0` and `b : ℝ`, `x ^ a / (log x) ^ b → +∞` as `x → ∞`.
-/
theorem powers_dominate_logs (a : ℝ) (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => x ^ a / (Real.log x) ^ b) atTop atTop := by
  -- Use the variable substitution $t = \log x$, then $x = \exp(t)$.
  suffices h_subst : Filter.Tendsto (fun t => (Real.exp t)^a / (t^b)) Filter.atTop Filter.atTop by
    convert h_subst.comp ( Real.tendsto_log_atTop ) |> Filter.Tendsto.congr' _ using 2;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] ;
  convert tendsto_exp_mul_div_rpow_atTop ( b := a ) ( s := b ) ha using 2 ; rw [ ← Real.exp_mul ] ; ring_nf;

/--
Consequence of `powers_dominate_logs`: `x ^ (-a) * (log x) ^ b → 0`.
-/
theorem rpow_neg_mul_log_rpow_tendsto_zero (a : ℝ) (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => x ^ (-a) * (Real.log x) ^ b) atTop (nhds 0) := by
  -- We show x^(-a) * (log x)^b → 0. Note that x^(-a) * (log x)^b is the reciprocal of x^a/(log x)^b eventually (for x large where log x > 0).
  have h_eq : ∀ᶠ x : ℝ in atTop, x ^ (-a) * (Real.log x) ^ b = (x ^ a / (Real.log x) ^ b)⁻¹ := by
    filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.rpow_neg ( by positivity ) ] ; group;
  rw [ Filter.tendsto_congr' h_eq ] ; exact ( powers_dominate_logs a ha b ) |> Filter.Tendsto.inv_tendsto_atTop;

/--
For every integer `r ≥ 2`,
`r log r - r + 1 ≤ log (r!) ≤ r log r - r + 1 + log r`.
-/
theorem log_factorial_bounds (r : ℕ) (hr : 2 ≤ r) :
    (r : ℝ) * Real.log r - r + 1 ≤ Real.log (Nat.factorial r) ∧
    Real.log (Nat.factorial r) ≤ (r : ℝ) * Real.log r - r + 1 + Real.log r := by
  induction hr <;> simp_all +decide [ Nat.factorial_succ ];
  · exact ⟨ by have := Real.log_two_lt_d9; norm_num1 at *; linarith, by have := Real.log_two_gt_d9; norm_num1 at *; linarith ⟩;
  · rw [ Real.log_mul ( by positivity ) ( by positivity ) ];
    constructor;
    · rename_i k hk ih;
      have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( k + 1 : ℝ ) / k );
      rw [ Real.log_div ] at this <;> first | positivity | ring_nf at * ; nlinarith [ inv_mul_cancel₀ ( by positivity : ( k : ℝ ) ≠ 0 ) ] ;
    · have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( ↑‹ℕ› : ℝ ) / ( ↑‹ℕ› + 1 ) );
      rw [ Real.log_div ] at this <;> first | positivity | nlinarith [ mul_div_cancel₀ ( ( ↑‹ℕ› : ℝ ) : ℝ ) ( by positivity : ( ↑‹ℕ› + 1 : ℝ ) ≠ 0 ) ] ;

/--
Consequence of `log_factorial_bounds`: `r² / (r!)^(2/r) → e²` as `r → ∞`.
-/
theorem factorial_ratio_tendsto_exp_sq :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 / ((Nat.factorial r) : ℝ) ^ ((2 : ℝ) / r)) atTop
      (nhds (Real.exp 2)) := by
  -- We'll use the fact that $(r!)^{1/r} \approx r/e$ for large $r$. This follows from Stirling's approximation.
  have h_stirling : Filter.Tendsto (fun r : ℕ => (Nat.factorial r : ℝ) ^ (1 / (r : ℝ)) / r) Filter.atTop (nhds (1 / Real.exp 1)) := by
    have h_lim : Filter.Tendsto (fun r : ℕ => Real.exp ((Real.log (Nat.factorial r) / (r : ℝ)) - Real.log r)) Filter.atTop (nhds (1 / Real.exp 1)) := by
      -- We'll use the fact that $\frac{\log(r!)}{r} - \log(r)$ converges to $-1$.
      have h_log_factorial : Filter.Tendsto (fun r : ℕ => (Real.log (Nat.factorial r) - r * Real.log r + r) / (r : ℝ)) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $\log(r!) = r \log r - r + O(\log r)$.
        have h_log_factorial : ∀ r : ℕ, r ≥ 2 → abs (Real.log (Nat.factorial r) - (r * Real.log r - r)) ≤ Real.log r + 1 := by
          intro r hr; rw [ abs_le ] ; constructor <;> linarith [ log_factorial_bounds r hr ] ;
        -- We'll use the fact that $\frac{\log r}{r}$ tends to $0$ as $r$ tends to infinity.
        have h_log_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / (r : ℝ)) Filter.atTop (nhds 0) := by
          -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
          suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
            exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
        refine' squeeze_zero_norm' _ _;
        use fun r => ( Real.log r + 1 ) / r;
        · filter_upwards [ Filter.eventually_ge_atTop 2 ] with r hr using by rw [ Real.norm_eq_abs, abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ r ) ] ; convert div_le_div_of_nonneg_right ( h_log_factorial r hr ) ( Nat.cast_nonneg r ) using 1 ; ring_nf;
        · simpa [ add_div ] using h_log_div_r.add ( tendsto_inv_atTop_nhds_zero_nat );
      have := h_log_factorial.sub_const 1;
      simpa [ Real.exp_neg ] using Filter.Tendsto.comp ( Real.continuous_exp.tendsto _ ) ( this.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp [ hx.ne', mul_div_cancel_left₀, sub_div, add_div ] );
    refine h_lim.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr; rw [ Real.rpow_def_of_pos ( by positivity ), Real.exp_sub, Real.exp_log ( by positivity ) ] ; ring_nf );
  convert h_stirling.inv₀ ( by positivity ) |> Filter.Tendsto.pow <| 2 using 2 <;> norm_num ; ring_nf;
  rw [ Real.rpow_mul ( by positivity ), Real.rpow_two ] ; norm_num

/--
The set of achievable sizes of repeated-factor primitive subsets of `[n]`.
-/
theorem Fkrep_le_Fkdist (k n : ℕ) : Fkrep k n ≤ Fkdist k n := by
  refine' csSup_le _ _;
  · exact ⟨ 0, ⟨ ∅, by norm_num, by unfold RepPrimitive; aesop ⟩ ⟩;
  · simp +zetaDelta at *;
    intro b x hx hx' hx''; subst hx''; exact le_csSup ⟨ n, by rintro m ⟨ y, hy, hy', rfl ⟩ ; exact le_trans ( Finset.card_le_card hy ) ( by simp ) ⟩ ⟨ x, hx, RepPrimitive.distPrimitive hx', rfl ⟩ ;

/-! ## Elementary combinatorial and arithmetic lemmas -/

/--
Binomial splitting identities.
-/
theorem binomial_splitting (s : ℕ) :
    (∑ a ∈ Finset.range (s + 1), (2 : ℝ) ^ (-(s : ℤ)) * (s.choose a)) = 1 ∧
    (∑ a ∈ Finset.range (s + 1), (2 : ℝ) ^ (-(s : ℤ)) * (s.choose a) * (a : ℝ)) = (s : ℝ) / 2 ∧
    (∑ a ∈ Finset.range (s + 1), (2 : ℝ) ^ (-(s : ℤ)) * (s.choose a) * (a.choose 2 : ℝ))
        = (1 / 4) * (s.choose 2 : ℝ) ∧
    (∑ a ∈ Finset.range (s + 1),
        (2 : ℝ) ^ (-(s : ℤ)) * (s.choose a) * ((a : ℝ) * ((s : ℝ) - a)))
        = (1 / 2) * (s.choose 2 : ℝ) := by
  refine' ⟨ _, _, _, _ ⟩;
  · norm_cast ; norm_num [ ← Finset.mul_sum _ _ _, Nat.sum_range_choose ];
    rw [ inv_mul_eq_div, div_eq_iff ] <;> norm_cast <;> norm_num [ Nat.sum_range_choose ];
  · -- We'll use the fact that $\sum_{a=0}^{s} \binom{s}{a} a = s \cdot 2^{s-1}$.
    have h_sum_a : ∑ a ∈ Finset.range (s + 1), (Nat.choose s a : ℝ) * a = s * 2^(s - 1) := by
      rw_mod_cast [ ← Nat.sum_range_choose, Finset.mul_sum ];
      cases s <;> simp +arith +decide [ Finset.sum_range_succ', mul_comm, Nat.add_one_mul_choose_eq ];
    convert congr_arg ( fun x : ℝ => x * 2 ^ ( -s : ℝ ) ) h_sum_a using 1 <;> norm_num [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Real.rpow_neg ];
    cases s <;> norm_num [ pow_succ', div_eq_mul_inv ];
  · -- We'll use the fact that $\sum_{a=0}^{s} \binom{s}{a} \binom{a}{2} = \binom{s}{2} 2^{s-2}$.
    have h_sum : ∑ a ∈ Finset.range (s + 1), (Nat.choose s a : ℝ) * (Nat.choose a 2 : ℝ) = (Nat.choose s 2 : ℝ) * 2 ^ (s - 2) := by
      norm_cast;
      rw [ ← Nat.sum_range_choose ];
      rw [ Finset.mul_sum _ _ _ ];
      rcases s with ( _ | _ | s ) <;> simp +arith +decide [ Finset.sum_range_succ' ];
      grind +suggestions;
    rcases s with ( _ | _ | s ) <;> simp_all +decide [ mul_assoc ];
    · norm_num [ Finset.sum_range_succ ];
    · rw [ ← Finset.mul_sum _ _ _, h_sum ] ; norm_num [ zpow_add₀, zpow_neg ] ; ring_nf;
      norm_num [ mul_assoc, mul_comm, mul_left_comm ];
      norm_num [ ← mul_assoc, ← mul_pow ];
  · -- We'll use the fact that $\sum_{a=0}^{s} \binom{s}{a} a (s - a) = s(s-1) 2^{s-2}$.
    have h_sum : ∑ a ∈ Finset.range (s + 1), (Nat.choose s a : ℝ) * a * (s - a) = s * (s - 1) * 2 ^ (s - 2) := by
      rcases s with ( _ | _ | s ) <;> norm_num at *;
      · norm_cast;
      · have h_sum : ∑ a ∈ Finset.range (s + 3), (Nat.choose (s + 2) a : ℝ) * a * (s + 2 - a) = (s + 2) * (s + 1) * 2 ^ s := by
          have h_sum : ∑ a ∈ Finset.range (s + 3), (Nat.choose (s + 2) a : ℝ) * a * (s + 2 - a) = (s + 2) * ∑ a ∈ Finset.range (s + 2), (Nat.choose (s + 1) a : ℝ) * (s + 1 - a) := by
            rw [ Finset.sum_range_succ' ] ; norm_num [ Finset.mul_sum _ _ _ ] ; ring_nf;
            refine Finset.sum_congr rfl fun x hx => ?_;
            rw [ show 2 + s = 1 + s + 1 by ring, show 1 + x = x + 1 by ring ] ; rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith [ Finset.mem_range.mp hx ];
            field_simp;
            rw [ show 1 + s + 1 = 1 + s + 1 from rfl, show 1 + s + 1 - ( x + 1 ) = 1 + s - x from by rw [ Nat.add_sub_add_right ] ] ; push_cast [ Nat.factorial_succ ] ; ring;
          have h_sum : ∑ a ∈ Finset.range (s + 2), (Nat.choose (s + 1) a : ℝ) * (s + 1 - a) = (s + 1) * 2 ^ s := by
            have h_sum : ∑ a ∈ Finset.range (s + 2), (Nat.choose (s + 1) a : ℝ) * (s + 1 - a) = ∑ a ∈ Finset.range (s + 2), (Nat.choose (s + 1) a : ℝ) * a := by
              rw [ ← Finset.sum_flip ];
              exact Finset.sum_congr rfl fun x hx => by rw [ Nat.choose_symm ( Finset.mem_range_succ_iff.mp hx ), Nat.cast_sub ( Finset.mem_range_succ_iff.mp hx ) ] ; push_cast; ring;
            have h_sum : ∑ a ∈ Finset.range (s + 2), (Nat.choose (s + 1) a : ℝ) * a = (s + 1) * ∑ a ∈ Finset.range (s + 1), (Nat.choose s a : ℝ) := by
              rw [ Finset.mul_sum _ _ _ ];
              rw [ Finset.sum_range_succ' ] ; norm_cast ; simp +decide [ Nat.add_one_mul_choose_eq ];
            rw_mod_cast [ ← Nat.sum_range_choose ] at * ; aesop;
          simp_all +decide [ mul_assoc ];
        grind;
    convert congr_arg ( fun x : ℝ => x * 2 ^ ( -s : ℝ ) ) h_sum using 1 <;> norm_num [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Nat.choose_two_right ] ; ring_nf;
    rcases s with ( _ | _ | s ) <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] ; ring_nf;
    norm_num [ mul_assoc, ← mul_pow ] ; ring

/--
If `d₁, …, dₘ` are pairwise coprime with `dᵢ ∣ bᵢ`, then their product divides
the product of the *distinct* values among the `bᵢ`.
-/
theorem dedup {m : ℕ} (d b : Fin m → ℕ)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (d i) (d j))
    (hdvd : ∀ i, d i ∣ b i) :
    (∏ i, d i) ∣ ∏ c ∈ Finset.image b Finset.univ, c := by
  -- For each $c \in \text{image } b$, let $I_c = \{i \mid b i = c\}$. The $d i$ for $i \in I_c$ are pairwise coprime and each divides $b i = c$, so their product $\prod_{i \in I_c} d i$ divides $c$.
  have h_prod_div : ∀ c ∈ Finset.image b Finset.univ, (∏ i ∈ Finset.filter (fun i => b i = c) Finset.univ, d i) ∣ c := by
    intros c hc
    have h_prod_div_c : (∏ i ∈ Finset.filter (fun i => b i = c) Finset.univ, d i) ∣ c := by
      have h_div_c : ∀ i ∈ Finset.filter (fun i => b i = c) Finset.univ, d i ∣ c := by
        grind
      have h_coprime : ∀ s : Finset (Fin m), (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (d i) (d j)) → (∀ i ∈ s, d i ∣ c) → (∏ i ∈ s, d i) ∣ c := by
        intro s hs h_div_c; induction s using Finset.induction <;> simp_all +decide [ Nat.Coprime  ] ;
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by exact Nat.Coprime.prod_right fun i hi => hcop _ _ <| by aesop ) h_div_c.1 ‹_›;
      exact h_coprime _ ( fun i hi j hj hij => hcop i j hij ) h_div_c;
    exact h_prod_div_c;
  refine' dvd_trans _ ( Finset.prod_dvd_prod_of_dvd _ _ h_prod_div );
  rw [ Finset.prod_image' ] ; aesop

/--
Let `B` be a finite set of positive integers, and `C` a finite set such that no
`a ∈ C` divides a product of at most `k` distinct members of `C \ {a}`.  Suppose
each `a ∈ C` is given a factorization `a = ∏_{x ∈ B} x^{μ a x}` with
`∑_{x ∈ B} μ a x = k`.  Then there is an injective map `φ : ℕ → ℕ` on `C` into
`B` such that for every `a ∈ C`, `μ a (φ a) > μ b (φ a)` for all `b ∈ C \ {a}`.
-/
theorem private_factor {k : ℕ} (B C : Finset ℕ) (mu : ℕ → ℕ → ℕ)
    (hfact : ∀ a ∈ C, (∏ x ∈ B, x ^ mu a x) = a ∧ (∑ x ∈ B, mu a x) = k)
    (hprim : ∀ a ∈ C, ∀ D : Finset ℕ, D ⊆ C.erase a → D.card ≤ k → ¬ (a ∣ ∏ d ∈ D, d)) :
    ∃ φ : ℕ → ℕ, Set.InjOn φ C ∧ (∀ a ∈ C, φ a ∈ B) ∧
      ∀ a ∈ C, ∀ b ∈ C, b ≠ a → mu b (φ a) < mu a (φ a) := by
  -- By the lemma, for every $a \in C$, there exists $x \in B$ such that $\mu(a, x) > \mu(b, x)$ for all $b \in C \setminus \{a\}$.
  have h_lemma : ∀ a ∈ C, ∃ x ∈ B, ∀ b ∈ C, b ≠ a → mu b x < mu a x := by
    intro a ha;
    contrapose! hprim;
    -- Let $Bsupp := B.filter (fun x => 0 < mu a x)$. For each $x ∈ Bsupp$, pick $w x ∈ C.erase a$ with $mu a x ≤ mu (w x) x$.
    set Bsupp := B.filter (fun x => 0 < mu a x)
    obtain ⟨w, hw⟩ : ∃ w : ℕ → ℕ, (∀ x ∈ Bsupp, w x ∈ C.erase a ∧ mu a x ≤ mu (w x) x) := by
      choose! w hw₁ hw₂ hw₃ using hprim; use fun x => w x; aesop;
    refine' ⟨ a, ha, Finset.image w Bsupp, _, _, _ ⟩;
    · exact Finset.image_subset_iff.mpr fun x hx => hw x hx |>.1;
    · refine' le_trans ( Finset.card_image_le ) _;
      have := hfact a ha;
      rw [ ← this.2, Finset.card_filter ];
      exact Finset.sum_le_sum fun x hx => by cases mu a x <;> simp +decide ;
    · -- For each $d \in D$, $\prod_{x \in Bsupp, w x = d} x^{mu a x}$ divides $d$.
      have h_div : ∀ d ∈ Finset.image w Bsupp, (∏ x ∈ Finset.filter (fun x => w x = d) Bsupp, x ^ mu a x) ∣ d := by
        intros d hd
        have h_div : (∏ x ∈ Finset.filter (fun x => w x = d) Bsupp, x ^ mu a x) ∣ (∏ x ∈ Finset.filter (fun x => w x = d) Bsupp, x ^ mu d x) := by
          exact Finset.prod_dvd_prod_of_dvd _ _ fun x hx => pow_dvd_pow _ <| by have := hw x ( Finset.mem_filter.mp hx |>.1 ) ; aesop;
        have h_div : (∏ x ∈ Finset.filter (fun x => w x = d) Bsupp, x ^ mu d x) ∣ (∏ x ∈ B, x ^ mu d x) := by
          apply_rules [ Finset.prod_dvd_prod_of_subset ];
          exact fun x hx => Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1;
        exact dvd_trans ‹_› ( h_div.trans ( by rw [ hfact d ( by aesop ) |>.1 ] ) );
      -- Therefore, $\prod_{x \in Bsupp} x^{mu a x}$ divides $\prod_{d \in D} d$.
      have h_prod_div : (∏ x ∈ Bsupp, x ^ mu a x) ∣ (∏ d ∈ Finset.image w Bsupp, d) := by
        convert Finset.prod_dvd_prod_of_dvd _ _ h_div using 1;
        rw [ Finset.prod_image' ] ; aesop;
      convert h_prod_div using 1;
      rw [ ← hfact a ha |>.1, Finset.prod_filter_of_ne ] ; aesop;
      intro x hx hx'; contrapose! hx'; simp_all +decide ;
  choose! φ hφ₁ hφ₂ using h_lemma;
  refine' ⟨ φ, _, hφ₁, hφ₂ ⟩;
  intros a ha b hb hab;
  grind

/-- A pair cover of order `r`. -/
def IsPairCover (r : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ x y, f x y = f y x) ∧ (∀ x y, 0 ≤ f x y) ∧
  Integrable (fun p : ℝ × ℝ => f p.1 p.2) (volume.restrict (Set.Ioi 0 ×ˢ Set.Ioi 0)) ∧
  (∀ x : Fin r → ℝ, (∀ i, 0 < x i) → (∏ i, x i ≤ 1) →
    1 ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2), f (x p.1) (x p.2))

/-- The integral `∬_{(0,∞)²} f` of a pair cover. -/
noncomputable def coverIntegral (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p in Set.Ioi 0 ×ˢ Set.Ioi 0, f p.1 p.2

/-- The `i`th half-open bin in the level-`Q` dyadic grid. -/
def dyadicBin (Q : ℕ) (i : Fin (NQ Q)) : Set ℝ :=
  Set.Ioc ((i : ℝ) * dQ Q) (((i : ℝ) + 1) * dQ Q)

/-- The average of a two-variable function on a pair of dyadic bins. -/
noncomputable def dyadicPairAverage (Q : ℕ) (f : ℝ → ℝ → ℝ)
    (i j : Fin (NQ Q)) : ℝ :=
  (dQ Q)⁻¹ ^ 2 * ∫ p in dyadicBin Q i ×ˢ dyadicBin Q j, f p.1 p.2

/--
A finite multiplicity vector of total mass `r` can be represented by a
labeling of `Fin r`, with the prescribed fiber cardinalities.
-/
theorem exists_labeling_of_sum {α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (t : α → ℕ) (ht : ∑ a, t a = r) :
    ∃ b : Fin r → α,
      ∀ a, (Finset.univ.filter fun k => b k = a).card = t a := by
  by_contra! h_contra;
  have h_multiset : ∃ M : Multiset α, Multiset.card M = r ∧ ∀ a, Multiset.count a M = t a := by
    use ∑ a, Multiset.replicate (t a) a; simp_all +decide ;
    intro a; rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ a ) ] ; simp +decide [ Multiset.count_add  ] ;
    exact fun x hx => fun h => hx <| by rw [ Multiset.mem_replicate ] at h; aesop;
  obtain ⟨ M, hM₁, hM₂ ⟩ := h_multiset;
  obtain ⟨b, hb⟩ : ∃ b : Fin r → α, M = Multiset.ofList (List.ofFn b) := by
    have h_list : ∃ l : List α, l.length = r ∧ M = Multiset.ofList l := by
      exact ⟨ M.toList, by simpa using hM₁, by simp ⟩;
    obtain ⟨ l, hl₁, hl₂ ⟩ := h_list; use fun i => l.get ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ; simp +decide [ hl₂ ] ;
    convert List.Perm.refl l;
    refine' List.ext_get _ _ <;> simp +decide [ hl₁ ];
  simp_all +decide [ List.ofFn_eq_map ];
  simp_all +decide [ List.count ];
  simp_all +decide [ List.countP_eq_length_filter ];
  exact h_contra b |> fun ⟨ a, ha ⟩ => ha <| by simpa [ List.filter_eq ] using hM₂ a;

/-
Grouping unordered pairs in a labeled finite set by their labels gives
the off-diagonal products and diagonal binomial coefficients.
-/
set_option maxHeartbeats 800000 in
theorem sum_pairs_group_by_label {r n : ℕ} (b : Fin r → Fin n)
    (t : Fin n → ℕ)
    (hb : ∀ a, (Finset.univ.filter fun k => b k = a).card = t a)
    (w : Fin n → Fin n → ℝ) (hw : ∀ i j, w i j = w j i) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2),
        w (b p.1) (b p.2) =
      (∑ i, ∑ j ∈ Finset.Ioi i, ((t i : ℝ) * t j) * w i j) +
      ∑ i, ((t i).choose 2 : ℝ) * w i i := by
  revert b t;
  induction' r with r ih;
  · simp +zetaDelta at *;
    exact fun t ht => by simp +decide [ ← ht ] ;
  · intro b t ht
    set b' : Fin r → Fin n := fun k => b (Fin.castSucc k)
    set a := b (Fin.last r);
    -- By definition of $t$, we know that $t a = t' a + 1$ and $t i = t' i$ for all $i \neq a$.
    obtain ⟨t', ht'⟩ : ∃ t' : Fin n → ℕ, (∀ i, t i = t' i + if i = a then 1 else 0) ∧ (∀ i, Finset.card (Finset.filter (fun k => b' k = i) Finset.univ) = t' i) := by
      refine' ⟨ fun i => t i - if i = a then 1 else 0, _, _ ⟩ <;> simp +decide [ ← ht ];
      · intro i; split_ifs <;> simp_all +decide ;
        rw [ Nat.sub_add_cancel ( ht a ▸ Finset.card_pos.mpr ⟨ Fin.last r, by aesop ⟩ ) ];
      · intro i; split_ifs <;> simp_all +decide ;
        · rw [ ← ht ];
          rw [ Finset.card_filter, Finset.card_filter ];
          rw [ Fin.sum_univ_castSucc ] ; aesop;
        · rw [ ← ht i, Finset.card_filter ];
          rw [ Finset.card_filter ];
          rw [ Fin.sum_univ_castSucc ] ; aesop;
    convert congr_arg ( fun x : ℝ => x + ∑ i : Fin r, w ( b' i ) a ) ( ih b' t' ht'.2 ) using 1;
    · rw [ show ( Finset.univ.filter fun p : Fin ( r + 1 ) × Fin ( r + 1 ) => p.1 < p.2 ) = Finset.image ( fun p : Fin r × Fin r => ( Fin.castSucc p.1, Fin.castSucc p.2 ) ) ( Finset.univ.filter fun p : Fin r × Fin r => p.1 < p.2 ) ∪ Finset.image ( fun i : Fin r => ( Fin.castSucc i, Fin.last r ) ) Finset.univ from ?_, Finset.sum_union ];
      · rw [ Finset.sum_image, Finset.sum_image ] <;> simp +decide [ Fin.ext_iff ];
        exact fun i j h => by simpa [ Fin.ext_iff ] using h;
      · norm_num [ Finset.disjoint_right ];
      · ext ⟨i, j⟩; simp [Finset.mem_union, Finset.mem_image];
        constructor;
        · intro hij;
          cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp +decide [ * ] at hij ⊢;
          · grind;
          · exact Or.inl hij;
        · rintro ( ⟨ a, b, hab, rfl, rfl ⟩ | ⟨ ⟨ a, rfl ⟩, rfl ⟩ ) <;> [ exact Fin.castSucc_lt_castSucc_iff.mpr hab; exact Fin.castSucc_lt_last _ ];
    · simp +decide [ ht'.1 ];
      simp +decide [ Finset.sum_add_distrib, add_mul, mul_add, Finset.sum_ite, Nat.choose_two_right, hw ];
      rw [ show ( ∑ i : Fin r, w ( b' i ) a ) = ∑ i : Fin n, ∑ j ∈ Finset.filter ( fun k => b' k = i ) Finset.univ, w i a from ?_ ];
      · simp +decide [ ht'.2 ];
        rw [ show ( ∑ x : Fin n, ↑ ( t' x ) * w x a ) = ∑ x ∈ Finset.Ioi a, ↑ ( t' x ) * w x a + ∑ x with x < a, ↑ ( t' x ) * w x a + ↑ ( t' a ) * w a a from ?_ ];
        · rw [ show ( ∑ x : Fin n, ↑ ( ( t' x * ( ( t' x + if x = a then 1 else 0 ) - 1 ) + if x = a then ( t' x + if x = a then 1 else 0 ) - 1 else 0 ) / 2 ) * w x x ) = ∑ x : Fin n, ↑ ( t' x * ( t' x - 1 ) / 2 ) * w x x + ↑ ( t' a ) * w a a from ?_ ];
          · ring;
          · rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ a ) ];
            rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ a ) ];
            rw [ add_right_comm ];
            congr! 1;
            · cases t' a <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] ; ring;
            · exact Finset.sum_congr rfl fun x hx => by aesop;
        · rw [ ← Finset.sum_union ];
          · rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ a ), add_comm ];
            rw [ add_comm, show ( Finset.univ.erase a : Finset ( Fin n ) ) = Finset.Ioi a ∪ Finset.filter ( fun x => x < a ) Finset.univ from ?_ ];
            grind;
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => lt_asymm ( Finset.mem_Ioi.mp hx₁ ) ( Finset.mem_filter.mp hx₂ |>.2 );
      · simp +decide only [Finset.sum_filter];
        rw [ Finset.sum_comm ] ; simp +decide

/-- Lebesgue probability measure, normalized on one dyadic bin. -/
noncomputable def dyadicBinMeasure (Q : ℕ) (i : Fin (NQ Q)) : Measure ℝ :=
  ENNReal.ofReal (dQ Q)⁻¹ • volume.restrict (dyadicBin Q i)

lemma dyadicBinMeasure_isProbability (Q : ℕ) (i : Fin (NQ Q)) :
    IsProbabilityMeasure (dyadicBinMeasure Q i) := by
  have h_volume : (dyadicBinMeasure Q i).real Set.univ = 1 := by
    simp +decide [ dyadicBinMeasure  ];
    unfold dyadicBin; erw [ Real.volume_real_Ioc ] ; norm_num [ dQ ] ; ring_nf; norm_num;
    norm_num [ ← mul_pow ];
  constructor;
  rw [ ← ENNReal.toReal_eq_one_iff ] ; aesop

lemma dyadicBinMeasure_pair_integral (Q : ℕ) (f : ℝ → ℝ → ℝ)
    (i j : Fin (NQ Q)) :
    ∫ p : ℝ × ℝ, f p.1 p.2 ∂((dyadicBinMeasure Q i).prod (dyadicBinMeasure Q j)) =
      dyadicPairAverage Q f i j := by
  unfold dyadicBinMeasure dyadicPairAverage;
  convert MeasureTheory.integral_smul_measure _ _ using 1;
  rw [ MeasureTheory.Measure.prod_smul_left, MeasureTheory.Measure.prod_smul_right ];
  rw [ ENNReal.toReal_ofReal ( by exact inv_nonneg.mpr ( by exact div_nonneg zero_le_one ( pow_nonneg zero_le_two _ ) ) ) ] ; norm_num [ MeasureTheory.Measure.prod_restrict ] ; ring_nf;
  rw [ ENNReal.toReal_ofReal ( by exact inv_nonneg.mpr ( by exact div_nonneg zero_le_one ( pow_nonneg zero_le_two _ ) ) ) ] ; ring!

lemma dyadicBinMeasure_ae_mem (Q : ℕ) (i : Fin (NQ Q)) :
    ∀ᵐ x ∂dyadicBinMeasure Q i, x ∈ dyadicBin Q i := by
  unfold dyadicBinMeasure;
  rw [ MeasureTheory.ae_iff ] ; norm_num [ dyadicBin ];
  refine' Or.inr ( MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_singleton ( ( i + 1 : ℝ ) * dQ Q ) ) );
  grind

lemma dyadicPi_map_pair (r Q : ℕ) (b : Fin r → Fin (NQ Q))
    (a c : Fin r) (hac : a ≠ c) :
    Measure.map (fun x : Fin r → ℝ => (x a, x c))
        (Measure.pi (fun k => dyadicBinMeasure Q (b k))) =
      (dyadicBinMeasure Q (b a)).prod (dyadicBinMeasure Q (b c)) := by
  haveI : ∀ k, IsProbabilityMeasure (dyadicBinMeasure Q (b k)) := fun k =>
    dyadicBinMeasure_isProbability Q (b k)
  have hmeas : Measurable (fun x : Fin r → ℝ => (x a, x c)) :=
    (measurable_pi_apply a).prodMk (measurable_pi_apply c)
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hmeas (hs.prod ht)]
  have hpre : (fun x : Fin r → ℝ => (x a, x c)) ⁻¹' (s ×ˢ t)
      = Set.pi Set.univ (fun k => if k = a then s else if k = c then t else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨hxs, hxt⟩ k
      by_cases hk : k = a
      · subst hk; simpa using hxs
      · by_cases hk' : k = c
        · subst hk'; simp [hk]; exact hxt
        · simp [hk, hk']
    · intro h
      exact ⟨by have := h a; simpa using this, by have := h c; simp [hac.symm] at this; exact this⟩
  rw [hpre, Measure.pi_pi]
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ a),
      Finset.prod_eq_mul_prod_diff_singleton (show c ∈ Finset.univ \ {a} by simp [hac.symm])]
  have hrest : ∏ k ∈ (Finset.univ \ {a}) \ {c}, (dyadicBinMeasure Q (b k))
      (if k = a then s else if k = c then t else Set.univ) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hk
    rw [if_neg hk.1.2, if_neg hk.2]
    exact measure_univ
  rw [hrest, mul_one]
  have hba : (if a = a then s else if a = c then t else Set.univ) = s := by simp
  have hbc : (if c = a then s else if c = c then t else Set.univ) = t := by simp [hac.symm]
  rw [hba, hbc]

lemma dyadicPi_ae_admissible (r Q : ℕ) (b : Fin r → Fin (NQ Q))
    (hprod : ∏ k, (((b k : ℕ) + 1 : ℝ) * dQ Q) ≤ 1) :
    ∀ᵐ x ∂Measure.pi (fun k => dyadicBinMeasure Q (b k)),
      (∀ k, 0 < x k) ∧ ∏ k, x k ≤ 1 := by
  letI (k : Fin r) : IsProbabilityMeasure (dyadicBinMeasure Q (b k)) :=
    dyadicBinMeasure_isProbability Q (b k)
  have hd : 0 < dQ Q := by simp [dQ]
  have hmem : ∀ᵐ x ∂Measure.pi (fun k => dyadicBinMeasure Q (b k)),
      ∀ k, x k ∈ dyadicBin Q (b k) := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact (Measure.tendsto_eval_ae_ae.eventually (dyadicBinMeasure_ae_mem Q (b k)))
  filter_upwards [hmem] with x hx
  constructor
  · intro k
    exact lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) hd.le) (hx k).1
  · calc
      ∏ k, x k ≤ ∏ k, (((b k : ℕ) + 1 : ℝ) * dQ Q) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact le_of_lt (lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) hd.le) (hx i).1)
        · intro i hi
          exact (hx i).2
      _ ≤ 1 := hprod

/-- The pointwise pair-cover inequality remains true after independently
averaging each coordinate over its labeled dyadic bin. -/
theorem labeled_dyadic_average_cover (r Q : ℕ) (b : Fin r → Fin (NQ Q))
    (hprod : ∏ k, (((b k : ℕ) + 1 : ℝ) * dQ Q) ≤ 1)
    (f : ℝ → ℝ → ℝ) (hf : IsPairCover r f) :
    1 ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2),
      dyadicPairAverage Q f (b p.1) (b p.2) := by
  classical
  haveI hprob : ∀ k, IsProbabilityMeasure (dyadicBinMeasure Q (b k)) := fun k =>
    dyadicBinMeasure_isProbability Q (b k)
  set μ := Measure.pi (fun k => dyadicBinMeasure Q (b k)) with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hfbin : ∀ i j : Fin (NQ Q),
      Integrable (fun p : ℝ × ℝ => f p.1 p.2) ((dyadicBinMeasure Q i).prod (dyadicBinMeasure Q j)) := by
    intro i j
    have hsub : dyadicBin Q i ×ˢ dyadicBin Q j ⊆ Set.Ioi 0 ×ˢ Set.Ioi 0 := by
      apply Set.prod_mono <;>
        · intro x hx
          have hd : (0:ℝ) ≤ dQ Q := by unfold dQ; positivity
          simp only [dyadicBin, Set.mem_Ioc] at hx
          exact lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) hd) hx.1
    have heq : (dyadicBinMeasure Q i).prod (dyadicBinMeasure Q j)
        = (ENNReal.ofReal (dQ Q)⁻¹ * ENNReal.ofReal (dQ Q)⁻¹) • volume.restrict (dyadicBin Q i ×ˢ dyadicBin Q j) := by
      unfold dyadicBinMeasure
      rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict,
          ← Measure.volume_eq_prod]
    rw [heq]
    exact (hf.2.2.1.mono_measure (Measure.restrict_mono hsub le_rfl)).smul_measure (by simp [ENNReal.mul_eq_top])
  have key : ∀ p : Fin r × Fin r, p.1 < p.2 →
      Integrable (fun x : Fin r → ℝ => f (x p.1) (x p.2)) μ ∧
      ∫ x, f (x p.1) (x p.2) ∂μ = dyadicPairAverage Q f (b p.1) (b p.2) := by
    intro p hlt
    have hne : p.1 ≠ p.2 := ne_of_lt hlt
    have hφmeas : Measurable (fun x : Fin r → ℝ => (x p.1, x p.2)) :=
      (measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)
    have hmap : Measure.map (fun x : Fin r → ℝ => (x p.1, x p.2)) μ
        = (dyadicBinMeasure Q (b p.1)).prod (dyadicBinMeasure Q (b p.2)) := by
      rw [hμ]; exact dyadicPi_map_pair r Q b p.1 p.2 hne
    have hg : AEStronglyMeasurable (fun q : ℝ × ℝ => f q.1 q.2)
        (Measure.map (fun x : Fin r → ℝ => (x p.1, x p.2)) μ) := by
      rw [hmap]; exact (hfbin (b p.1) (b p.2)).aestronglyMeasurable
    have hcomp : (fun x : Fin r → ℝ => f (x p.1) (x p.2))
        = (fun q : ℝ × ℝ => f q.1 q.2) ∘ (fun x : Fin r → ℝ => (x p.1, x p.2)) := rfl
    refine ⟨?_, ?_⟩
    · rw [hcomp, ← integrable_map_measure hg hφmeas.aemeasurable, hmap]
      exact hfbin (b p.1) (b p.2)
    · have h2 := integral_map (μ := μ) (φ := fun x : Fin r → ℝ => (x p.1, x p.2)) hφmeas.aemeasurable hg
      rw [hmap, dyadicBinMeasure_pair_integral Q f (b p.1) (b p.2)] at h2
      exact h2.symm
  set S := Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2) with hS
  have hterm_int : ∀ p ∈ S, Integrable (fun x : Fin r → ℝ => f (x p.1) (x p.2)) μ := by
    intro p hp; exact (key p (Finset.mem_filter.mp hp).2).1
  have hGint : Integrable (fun x => ∑ p ∈ S, f (x p.1) (x p.2)) μ :=
    integrable_finset_sum _ hterm_int
  have hae : ∀ᵐ x ∂μ, (1:ℝ) ≤ ∑ p ∈ S, f (x p.1) (x p.2) := by
    filter_upwards [dyadicPi_ae_admissible r Q b hprod] with x hx
    exact hf.2.2.2 x hx.1 hx.2
  have h1 : (1:ℝ) ≤ ∫ x, ∑ p ∈ S, f (x p.1) (x p.2) ∂μ := by
    calc (1:ℝ) = ∫ _x, (1:ℝ) ∂μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const 1) hGint hae
  rw [integral_finset_sum _ hterm_int] at h1
  calc (1:ℝ) ≤ ∑ p ∈ S, ∫ x, f (x p.1) (x p.2) ∂μ := h1
    _ = ∑ p ∈ S, dyadicPairAverage Q f (b p.1) (b p.2) :=
        Finset.sum_congr rfl (fun p hp => (key p (Finset.mem_filter.mp hp).2).2)

/--
Averaging the pair-cover inequality over the rectangle represented by an
admissible type gives a finite cover of that type.  This is the analytic core
of dyadic weak duality.
-/
theorem admissible_dyadic_average_cover (r Q : ℕ)
    (t : Fin (NQ Q) → ℕ) (ht : t ∈ admTypes r Q)
    (f : ℝ → ℝ → ℝ) (hf : IsPairCover r f) :
    1 ≤
      (∑ i, ∑ j ∈ Finset.Ioi i,
        ((t i : ℝ) * t j) * dyadicPairAverage Q f i j) +
      ∑ i, ((t i).choose 2 : ℝ) * dyadicPairAverage Q f i i := by
  obtain ⟨b, hb⟩ : ∃ b : Fin r → Fin (NQ Q), ∀ a, (Finset.univ.filter fun k => b k = a).card = t a := by
    apply exists_labeling_of_sum;
    exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.2;
  convert labeled_dyadic_average_cover r Q b _ f hf using 1;
  · convert sum_pairs_group_by_label b t hb ( fun i j => dyadicPairAverage Q f i j ) _ |> Eq.symm using 1;
    intro i j; simp +decide [ dyadicPairAverage ] ;
    left;
    rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    · erw [ ← MeasureTheory.integral_prod_swap ] ; congr ; ext ; simp +decide [ dyadicBin ] ; ring_nf;
      split_ifs <;> simp_all +decide [ hf.1 ];
    · exact measurableSet_Ioc.prod measurableSet_Ioc;
    · exact measurableSet_Ioc.prod measurableSet_Ioc;
  · convert div_le_one_of_le₀ ( show ( ∏ k : Fin r, ( ( b k : ℝ ) + 1 ) ) ≤ 2 ^ ( Q * r ) from ?_ ) ( by positivity : ( 0 : ℝ ) ≤ 2 ^ ( Q * r ) ) using 1;
    · norm_num [ div_eq_mul_inv, pow_mul, Finset.prod_mul_distrib, dQ ];
    · have h_prod_le : ∏ j : Fin (NQ Q), ((j.val + 1) : ℝ) ^ (t j) ≤ 2 ^ (Q * r) := by
        exact_mod_cast Finset.mem_filter.mp ht |>.2;
      convert h_prod_le using 1;
      simp +decide only [← hb, Finset.card_filter];
      simp +decide only [← Finset.prod_pow_eq_pow_sum];
      rw [ Finset.prod_comm ] ; simp +decide

/--
Summing the averaged bin costs against the packing capacities is bounded
by the integral cost of the pair cover.
-/
theorem packing_dyadic_average_bound (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : IsPacking r Q z)
    (f : ℝ → ℝ → ℝ) (hf : IsPairCover r f) :
    (∑ i, ∑ j ∈ Finset.Ioi i,
        (∑ t ∈ admTypes r Q, ((t i : ℝ) * t j) * z t) *
          dyadicPairAverage Q f i j) +
      ∑ i, (∑ t ∈ admTypes r Q, ((t i).choose 2 : ℝ) * z t) *
        dyadicPairAverage Q f i i
      ≤ (r : ℝ) ^ 2 / 2 * coverIntegral f := by
  -- By definition of `IsPairCover`, we know that `f` is symmetric and nonnegative.
  have h_symm : ∀ x y, f x y = f y x := by
    exact hf.1
  have h_nonneg : ∀ x y, 0 ≤ f x y := by
    exact hf.2.1
  have h_integrable : Integrable (fun p : ℝ × ℝ => f p.1 p.2) (volume.restrict (Set.Ioi 0 ×ˢ Set.Ioi 0)) := by
    exact hf.2.2.1;
  -- By definition of `IsPacking`, we know that the off-diagonal and diagonal capacities are satisfied.
  have h_off_diag : ∀ i j : Fin (NQ Q), i < j → (∑ t ∈ admTypes r Q, (t i : ℝ) * (t j : ℝ) * z t) ≤ (r : ℝ) ^ 2 * dQ Q ^ 2 := by
    exact hz.2.1
  have h_diag : ∀ i : Fin (NQ Q), (∑ t ∈ admTypes r Q, ((t i).choose 2 : ℝ) * z t) ≤ (r : ℝ) ^ 2 / 2 * dQ Q ^ 2 := by
    exact hz.2.2;
  -- By definition of `dyadicPairAverage`, we know that it is nonnegative.
  have h_dyadicPairAverage_nonneg : ∀ i j : Fin (NQ Q), 0 ≤ dyadicPairAverage Q f i j := by
    exact fun i j => mul_nonneg ( sq_nonneg _ ) ( MeasureTheory.integral_nonneg fun p => h_nonneg _ _ );
  -- By definition of `coverIntegral`, we know that it is the integral of `f` over the unit square.
  have h_coverIntegral : coverIntegral f ≥ ∑ i : Fin (NQ Q), ∑ j : Fin (NQ Q), dyadicPairAverage Q f i j * dQ Q ^ 2 := by
    have h_coverIntegral : coverIntegral f ≥ ∑ i : Fin (NQ Q), ∑ j : Fin (NQ Q), ∫ p in dyadicBin Q i ×ˢ dyadicBin Q j, f p.1 p.2 := by
      rw [ ← Finset.sum_product' ];
      rw [ ← MeasureTheory.integral_biUnion_finset ];
      · refine' MeasureTheory.setIntegral_mono_set _ _ _;
        · exact h_integrable;
        · exact Filter.Eventually.of_forall fun x => h_nonneg _ _;
        · refine' MeasureTheory.ae_of_all _ _;
          simp +decide [ dyadicBin ];
          rintro a b ⟨ i, hi ⟩;
          rcases hi with ⟨ ⟨ ⟨ i, j ⟩, rfl ⟩, hi ⟩ ; exact ⟨ show 0 < a by exact lt_of_le_of_lt ( by exact mul_nonneg ( Nat.cast_nonneg _ ) ( show 0 ≤ dQ Q by exact div_nonneg zero_le_one ( pow_nonneg zero_le_two _ ) ) ) hi.1.1, show 0 < b by exact lt_of_le_of_lt ( by exact mul_nonneg ( Nat.cast_nonneg _ ) ( show 0 ≤ dQ Q by exact div_nonneg zero_le_one ( pow_nonneg zero_le_two _ ) ) ) hi.2.1 ⟩ ;
      · exact fun _ _ => measurableSet_Ioc.prod measurableSet_Ioc;
      · intros x hx y hy hxy; simp_all +decide [ Set.disjoint_left ] ;
        intro a b ha hb ha' hb'; contrapose! hxy; ext <;> simp_all +decide [ dyadicBin ] ;
        · exact Nat.le_antisymm ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( 0 : ℝ ) < dQ Q from by exact one_div_pos.mpr <| pow_pos zero_lt_two _ ] } ) ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( 0 : ℝ ) < dQ Q from by exact one_div_pos.mpr <| pow_pos zero_lt_two _ ] } );
        · exact Nat.le_antisymm ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( 0 : ℝ ) < dQ Q from by exact one_div_pos.mpr <| pow_pos zero_lt_two _ ] } ) ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( 0 : ℝ ) < dQ Q from by exact one_div_pos.mpr <| pow_pos zero_lt_two _ ] } );
      · intro i hi;
        refine' h_integrable.mono_measure _;
        refine' MeasureTheory.Measure.restrict_mono _ le_rfl;
        exact Set.prod_mono ( Set.Ioc_subset_Ioi_self.trans ( Set.Ioi_subset_Ioi ( by exact mul_nonneg ( Nat.cast_nonneg _ ) ( by exact one_div_nonneg.mpr ( pow_nonneg zero_le_two _ ) ) ) ) ) ( Set.Ioc_subset_Ioi_self.trans ( Set.Ioi_subset_Ioi ( by exact mul_nonneg ( Nat.cast_nonneg _ ) ( by exact one_div_nonneg.mpr ( pow_nonneg zero_le_two _ ) ) ) ) );
    convert h_coverIntegral using 3 ; norm_num [ dyadicPairAverage ] ; ring_nf;
    norm_num [ show dQ Q ≠ 0 by exact ne_of_gt ( by exact div_pos zero_lt_one ( pow_pos zero_lt_two _ ) ) ];
  have h_coverIntegral : ∑ i : Fin (NQ Q), ∑ j : Fin (NQ Q), dyadicPairAverage Q f i j * dQ Q ^ 2 = 2 * ∑ i : Fin (NQ Q), ∑ j ∈ Finset.Ioi i, dyadicPairAverage Q f i j * dQ Q ^ 2 + ∑ i : Fin (NQ Q), dyadicPairAverage Q f i i * dQ Q ^ 2 := by
    have h_coverIntegral : ∀ (n : ℕ) (g : Fin n → Fin n → ℝ), (∀ i j, g i j = g j i) → ∑ i : Fin n, ∑ j : Fin n, g i j = 2 * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, g i j + ∑ i : Fin n, g i i := by
      intro n g hg; induction' n with n ih <;> simp +decide [ Fin.sum_univ_succ, * ] ; ring_nf;
      simp +decide [ Finset.sum_add_distrib, mul_two, ih ( fun i j => g i.succ j.succ ) fun i j => hg _ _ ] ; ring;
    apply h_coverIntegral;
    unfold dyadicPairAverage; simp +decide ;
    intro i j; left; rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ] ;
    · erw [ ← MeasureTheory.integral_prod_swap ] ; congr ; ext ; simp +decide [ h_symm ] ;
      grind;
    · exact measurableSet_Ioc.prod measurableSet_Ioc;
    · exact measurableSet_Ioc.prod measurableSet_Ioc;
  have h_coverIntegral : ∑ i : Fin (NQ Q), ∑ j ∈ Finset.Ioi i, (∑ t ∈ admTypes r Q, (t i : ℝ) * (t j : ℝ) * z t) * dyadicPairAverage Q f i j ≤ (r : ℝ) ^ 2 * dQ Q ^ 2 * ∑ i : Fin (NQ Q), ∑ j ∈ Finset.Ioi i, dyadicPairAverage Q f i j := by
    simpa only [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ( h_off_diag i j <| Finset.mem_Ioi.mp hj ) <| h_dyadicPairAverage_nonneg i j;
  have h_coverIntegral : ∑ i : Fin (NQ Q), (∑ t ∈ admTypes r Q, ((t i).choose 2 : ℝ) * z t) * dyadicPairAverage Q f i i ≤ (r : ℝ) ^ 2 / 2 * dQ Q ^ 2 * ∑ i : Fin (NQ Q), dyadicPairAverage Q f i i := by
    simpa only [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ( h_diag i ) ( h_dyadicPairAverage_nonneg i i );
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
  nlinarith [ show 0 ≤ ( r : ℝ ) ^ 2 * dQ Q ^ 2 by positivity ]

/--
Dyadic weak duality.
-/
theorem dyadic_weak_duality (r Q : ℕ) (z : (Fin (NQ Q) → ℕ) → ℝ)
    (hz : IsPacking r Q z) (f : ℝ → ℝ → ℝ) (hf : IsPairCover r f) :
    valQ r Q z ≤ (r : ℝ) ^ 2 / 2 * coverIntegral f := by
  have := @admissible_dyadic_average_cover r Q;
  have h_sum : ∑ t ∈ admTypes r Q, z t ≤ ∑ i, ∑ j ∈ Finset.Ioi i, (∑ t ∈ admTypes r Q, (t i : ℝ) * (t j : ℝ) * z t) * dyadicPairAverage Q f i j + ∑ i, (∑ t ∈ admTypes r Q, ((t i).choose 2 : ℝ) * z t) * dyadicPairAverage Q f i i := by
    have h_sum : ∑ t ∈ admTypes r Q, z t ≤ ∑ t ∈ admTypes r Q, z t * (∑ i, ∑ j ∈ Finset.Ioi i, (t i : ℝ) * (t j : ℝ) * dyadicPairAverage Q f i j + ∑ i, ((t i).choose 2 : ℝ) * dyadicPairAverage Q f i i) := by
      exact Finset.sum_le_sum fun t ht => le_mul_of_one_le_right ( hz.1 t ) ( this t ht f hf );
    have hmul : ∀ t : Fin (NQ Q) → ℕ,
        z t * (∑ i, ∑ j ∈ Finset.Ioi i, (t i : ℝ) * (t j : ℝ) * dyadicPairAverage Q f i j
            + ∑ i, ((t i).choose 2 : ℝ) * dyadicPairAverage Q f i i)
          = (∑ i, ∑ j ∈ Finset.Ioi i, (t i : ℝ) * (t j : ℝ) * z t * dyadicPairAverage Q f i j)
            + ∑ i, ((t i).choose 2 : ℝ) * z t * dyadicPairAverage Q f i i := by
      intro t
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
        (Finset.sum_congr rfl fun i _ => by ring)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    convert h_sum using 1
    rw [Finset.sum_congr rfl fun t _ => hmul t, Finset.sum_add_distrib]
    refine congrArg₂ (· + ·) ?_ ?_
    · have hswap : ∀ i : Fin (NQ Q),
          ∑ j ∈ Finset.Ioi i, ∑ t ∈ admTypes r Q,
              (t i : ℝ) * (t j : ℝ) * z t * dyadicPairAverage Q f i j
            = ∑ t ∈ admTypes r Q, ∑ j ∈ Finset.Ioi i,
              (t i : ℝ) * (t j : ℝ) * z t * dyadicPairAverage Q f i j := fun _ => Finset.sum_comm
      simp only [Finset.sum_mul, hswap]
      exact Finset.sum_comm
    · simp only [Finset.sum_mul]
      exact Finset.sum_comm
  exact h_sum.trans ( packing_dyadic_average_bound r Q z hz f hf )

/--
Every pair cover gives an upper bound for the packing constant.  This is
    the “consequently” clause of dyadic weak duality.
-/
theorem Lam_le_cover (r : ℕ) (f : ℝ → ℝ → ℝ) (hf : IsPairCover r f) :
    Lam r ≤ (r : ℝ) ^ 2 / 2 * coverIntegral f := by
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ 1, by norm_num, rfl ⟩ ⟩;
  · rintro _ ⟨ Q, hQ, rfl ⟩;
    refine' csSup_le _ _;
    · refine' ⟨ _, ⟨ fun _ => 0, _, rfl ⟩ ⟩ ; norm_num [ IsPacking ];
      exact ⟨ fun _ _ _ => by positivity, fun _ => by positivity ⟩;
    · rintro _ ⟨ z, hz, rfl ⟩ ; exact dyadic_weak_duality r Q z hz f hf;

/-- The uniform pair cover `g_r(x,y) = 𝟙[min(x,y)·max(x,y)^{r-1} ≤ 1]`. -/
noncomputable def gCover (r : ℕ) : ℝ → ℝ → ℝ :=
  fun x y => if min x y * (max x y) ^ (r - 1) ≤ 1 then 1 else 0

/-
`g_r` is a pair cover of order `r`.
-/
set_option maxHeartbeats 800000 in
theorem gCover_isPairCover (r : ℕ) (hr : 3 ≤ r) : IsPairCover r (gCover r) := by
  constructor;
  · unfold gCover; simp +decide [ min_comm, max_comm ] ;
  · unfold gCover;
    refine' ⟨ fun x y => by split_ifs <;> norm_num, _, _ ⟩;
    · refine' MeasureTheory.integrable_indicator_iff ( _ ) |>.2 _;
      · exact measurableSet_le ( Measurable.mul ( measurable_fst.min measurable_snd ) ( Measurable.pow_const ( measurable_fst.max measurable_snd ) _ ) ) measurable_const;
      · -- The set where $\min(x, y) \cdot \max(x, y)^{r-1} \leq 1$ has finite measure.
        have h_finite_measure : MeasureTheory.volume {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ min p.1 p.2 * max p.1 p.2 ^ (r - 1) ≤ 1} < ⊤ := by
          refine' lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) _;
          exact Set.Ioc 0 1 ×ˢ Set.Ioc 0 1 ∪ { p : ℝ × ℝ | 1 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ p.1 ^ ( - ( r - 1 ) : ℝ ) } ∪ { p : ℝ × ℝ | 1 < p.2 ∧ 0 < p.1 ∧ p.1 ≤ p.2 ^ ( - ( r - 1 ) : ℝ ) };
          · intro p hp; cases le_total p.1 p.2 <;> simp_all +decide ;
            · by_cases h : p.2 ≤ 1 <;> simp_all +decide [ Real.rpow_sub ];
              · exact Or.inl <| Or.inl <| by linarith;
              · rcases r with ( _ | _ | r ) <;> simp_all +decide [ pow_succ' ];
                exact Or.inr ( by rw [ le_div_iff₀ ( by positivity ) ] ; nlinarith [ pow_pos hp.2.1 r, pow_pos hp.2.1 2, pow_pos hp.2.1 3 ] );
            · rcases lt_trichotomy p.1 1 with h | h | h <;> rcases lt_trichotomy p.2 1 with i | i | i <;> try exact Or.inl <| Or.inl ⟨ by nlinarith [ pow_le_pow_right₀ ( by linarith : 1 ≤ p.1 ) ( Nat.le_sub_one_of_lt hr ) ], by nlinarith [ pow_le_pow_right₀ ( by linarith : 1 ≤ p.1 ) ( Nat.le_sub_one_of_lt hr ) ] ⟩;
              · exact Or.inl <| Or.inl ⟨ by linarith, by linarith ⟩;
              · refine' Or.inl <| Or.inr ⟨ h, _ ⟩;
                rw [ Real.rpow_sub ] <;> norm_num <;> try linarith;
                rw [ le_div_iff₀ ( by positivity ) ];
                cases r <;> simp_all +decide [ pow_succ' ] ; nlinarith;
          · refine' lt_of_le_of_lt ( MeasureTheory.measure_union_le _ _ ) _;
            refine' ENNReal.add_lt_top.mpr ⟨ _, _ ⟩;
            · refine' lt_of_le_of_lt ( MeasureTheory.measure_union_le _ _ ) _;
              refine' ENNReal.add_lt_top.mpr ⟨ _, _ ⟩;
              · erw [ MeasureTheory.Measure.prod_prod ] ; norm_num;
              · -- The volume of the set where $1 < x$ and $0 < y \leq x^{-(r-1)}$ is finite.
                have h_volume_finite : MeasureTheory.volume {p : ℝ × ℝ | 1 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ p.1 ^ (-(r - 1) : ℝ)} ≤ ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (x ^ (-(r - 1) : ℝ)) := by
                  erw [ MeasureTheory.Measure.prod_apply ];
                  · rw [ ← MeasureTheory.lintegral_indicator ];
                    · refine' MeasureTheory.lintegral_mono fun x => _;
                      by_cases hx : 1 < x <;> simp +decide [ hx ];
                      erw [ Real.volume_Ioc ] ; norm_num;
                    · norm_num;
                  · exact MeasurableSet.inter ( measurableSet_lt measurable_const measurable_fst ) ( MeasurableSet.inter ( measurableSet_lt measurable_const measurable_snd ) ( measurableSet_le measurable_snd ( measurable_fst.pow_const _ ) ) );
                refine' lt_of_le_of_lt h_volume_finite _;
                refine' MeasureTheory.Integrable.lintegral_lt_top _;
                exact ( integrableOn_Ioi_rpow_of_lt ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) );
            · have h_volume_finite : ∫⁻ (p : ℝ × ℝ) in {p : ℝ × ℝ | 1 < p.2 ∧ 0 < p.1 ∧ p.1 ≤ p.2 ^ (-(r - 1) : ℝ)}, 1 = ∫⁻ (y : ℝ) in Set.Ioi 1, ∫⁻ (x : ℝ) in Set.Ioc 0 (y ^ (-(r - 1) : ℝ)), 1 := by
                erw [ ← MeasureTheory.lintegral_indicator ];
                · erw [ ← MeasureTheory.lintegral_prod_swap ];
                  simp +decide [ Set.indicator, ← MeasureTheory.lintegral_indicator ];
                  erw [ MeasureTheory.lintegral_prod ];
                  · congr with x ; by_cases hx : 1 < x <;> simp +decide [ hx ];
                    rw [ show ( ∫⁻ y : ℝ, if 0 < y ∧ y ≤ x ^ ( 1 - r : ℝ ) then 1 else 0 ) = ∫⁻ y : ℝ in Set.Ioc 0 ( x ^ ( 1 - r : ℝ ) ), 1 by rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ] ] ; norm_num;
                  · refine' Measurable.aemeasurable _;
                    exact Measurable.ite ( MeasurableSet.inter ( measurableSet_lt measurable_const measurable_fst ) ( MeasurableSet.inter ( measurableSet_lt measurable_const measurable_snd ) ( measurableSet_le measurable_snd ( measurable_fst.pow_const _ ) ) ) ) measurable_const measurable_const;
                · exact MeasurableSet.inter ( measurableSet_lt measurable_const measurable_snd ) ( MeasurableSet.inter ( measurableSet_lt measurable_const measurable_fst ) ( measurableSet_le measurable_fst ( measurable_snd.pow_const _ ) ) );
              simp_all +decide [ ENNReal.ofReal ];
              refine' MeasureTheory.Integrable.lintegral_lt_top _;
              exact ( integrableOn_Ioi_rpow_of_lt ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) );
        simp_all +decide [ Set.Ioi  ];
        erw [ MeasureTheory.Measure.restrict_apply' ];
        · convert h_finite_measure using 2 ; ext ; aesop;
        · exact measurableSet_Ioi.prod measurableSet_Ioi;
    · intro x hx_pos hx_prod
      obtain ⟨i, j, hij, h_min⟩ : ∃ i j : Fin r, i < j ∧ min (x i) (x j) * max (x i) (x j) ^ (r - 1) ≤ 1 := by
        -- Let $i$ and $j$ be indices such that $x_i$ is the minimum and $x_j$ is the second minimum among $x_1, \dots, x_r$.
        obtain ⟨i, hi⟩ : ∃ i : Fin r, ∀ j : Fin r, x j ≥ x i := by
          cases r <;> [ tauto; simpa using Finset.exists_min_image Finset.univ ( fun i => x i ) ⟨ ⟨ 0, by linarith ⟩, Finset.mem_univ _ ⟩ ]
        obtain ⟨j, hj, hij⟩ : ∃ j : Fin r, j ≠ i ∧ ∀ k : Fin r, k ≠ i → x k ≥ x j := by
          have := Finset.exists_min_image ( Finset.univ.erase i ) ( fun k => x k ) ⟨ if i = ⟨ 0, by linarith ⟩ then ⟨ 1, by linarith ⟩ else ⟨ 0, by linarith ⟩, Finset.mem_erase_of_ne_of_mem ( by aesop ) ( Finset.mem_univ _ ) ⟩ ; aesop;
        have h_min_max : min (x i) (x j) * max (x i) (x j) ^ (r - 1) ≤ 1 := by
          have h_prod : ∏ k ∈ Finset.univ \ {i}, x k ≥ x j ^ (r - 1) := by
            exact le_trans ( by norm_num [ Finset.card_sdiff, * ] ) ( Finset.prod_le_prod ( fun _ _ => le_of_lt ( hx_pos _ ) ) fun k hk => hij k <| by aesop );
          simp_all +decide [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ i ) ];
          exact le_trans ( mul_le_mul_of_nonneg_left h_prod ( le_of_lt ( hx_pos i ) ) ) hx_prod
        use if i < j then i else j, if i < j then j else i
        generalize_proofs at *; (
        grind);
      refine' le_trans _ ( Finset.single_le_sum ( fun a _ => by positivity ) ( show ( i, j ) ∈ Finset.filter ( fun p : Fin r × Fin r => p.1 < p.2 ) Finset.univ from Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hij ⟩ ) ) ; aesop

/--
Nonnegativity of `λ_{r,Q}`.
-/
theorem lamQ_nonneg (r Q : ℕ) : 0 ≤ lamQ r Q := by
  apply Real.sSup_nonneg;
  rintro _ ⟨ z, hz, rfl ⟩ ; exact Finset.sum_nonneg fun _ _ => hz.1 _;

/--
Nonnegativity of the dyadic packing constant.
-/
theorem Lam_nonneg (r : ℕ) : 0 ≤ Lam r := by
  by_contra h_neg;
  convert lamQ_nonneg r 1 using 1;
  constructor <;> intro <;> contrapose! h_neg;
  · contradiction;
  · exact Real.sSup_nonneg fun x hx => by obtain ⟨ Q, hQ, rfl ⟩ := hx; exact lamQ_nonneg r Q;

/--
The set of `λ_{r,Q}` values (`Q ≥ 1`) is bounded above (from weak duality).
-/
theorem lamQ_le_Lam (r Q : ℕ) (hr : 3 ≤ r) (hQ : 1 ≤ Q) : lamQ r Q ≤ Lam r := by
  refine' le_csSup _ _;
  · have h_bdd_above : ∀ Q ≥ 1, lamQ r Q ≤ (r : ℝ) ^ 2 / 2 * coverIntegral (gCover r) := by
      intros Q hQ
      apply csSup_le;
      · refine' ⟨ _, ⟨ fun _ => 0, _, rfl ⟩ ⟩ ; norm_num [ IsPacking ];
        exact ⟨ fun _ _ _ => by positivity, fun _ => by positivity ⟩;
      · rintro _ ⟨ z, hz, rfl ⟩ ; exact dyadic_weak_duality r Q z hz ( gCover r ) ( gCover_isPairCover r hr ) ;
    exact ⟨ _, by rintro x ⟨ Q, hQ, rfl ⟩ ; exact h_bdd_above Q hQ ⟩;
  · use Q

/-- The old dyadic grid occupies the first half of the refined grid. -/
theorem two_mul_NQ_le (Q : ℕ) : 2 * NQ Q ≤ NQ (Q + 1) := by
  simp [NQ, pow_succ]
  nlinarith [Nat.zero_le (2 ^ Q)]

/-- The even child of a coarse dyadic bin. -/
def evenChild (Q : ℕ) (i : Fin (NQ Q)) : Fin (NQ (Q + 1)) :=
  ⟨2 * i.val, lt_of_lt_of_le (by omega) (two_mul_NQ_le Q)⟩

/-- The odd child of a coarse dyadic bin. -/
def oddChild (Q : ℕ) (i : Fin (NQ Q)) : Fin (NQ (Q + 1)) :=
  ⟨2 * i.val + 1, lt_of_lt_of_le (by omega) (two_mul_NQ_le Q)⟩

/-- A choice of how many occurrences in each coarse bin go to its even child. -/
def splitChoices (Q : ℕ) (t : Fin (NQ Q) → ℕ) : Finset (Fin (NQ Q) → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (t i + 1))

/-- The refined type associated with a coarse type and a choice of splits. -/
def refinedType (Q : ℕ) (t a : Fin (NQ Q) → ℕ) : Fin (NQ (Q + 1)) → ℕ := fun q =>
  ∑ i, if q = evenChild Q i then a i else if q = oddChild Q i then t i - a i else 0

/-- The binomial coefficient attached to a split. -/
noncomputable def splitWeight (r Q : ℕ) (t a : Fin (NQ Q) → ℕ) : ℝ :=
  (2 : ℝ) ^ (-(r : ℤ)) * ∏ i, (t i).choose (a i)

lemma refinedType_even (Q : ℕ) (t a : Fin (NQ Q) → ℕ) (i : Fin (NQ Q)) :
    refinedType Q t a (evenChild Q i) = a i := by
  convert Finset.sum_eq_single i _ _ <;> simp +decide [ evenChild, oddChild ];
  grind

lemma refinedType_odd (Q : ℕ) (t a : Fin (NQ Q) → ℕ) (i : Fin (NQ Q)) :
    refinedType Q t a (oddChild Q i) = t i - a i := by
  unfold refinedType;
  rw [ Finset.sum_eq_single i ] <;> simp +decide [ oddChild, evenChild ];
  grind

lemma refinedType_other (Q : ℕ) (t a : Fin (NQ Q) → ℕ) (q : Fin (NQ (Q + 1)))
    (hq : ∀ i, q ≠ evenChild Q i ∧ q ≠ oddChild Q i) : refinedType Q t a q = 0 := by
  unfold refinedType; aesop;

lemma refinedType_mem_admTypes (r Q : ℕ) (t : Fin (NQ Q) → ℕ)
    (ht : t ∈ admTypes r Q) (a : Fin (NQ Q) → ℕ) (ha : a ∈ splitChoices Q t) :
    refinedType Q t a ∈ admTypes r (Q + 1) := by
  refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
  · refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
    · simp +decide [ Fintype.mem_piFinset ];
      have h_sum : ∑ i, (a i + (t i - a i)) = r := by
        rw [ Finset.sum_congr rfl fun i _ => Nat.add_sub_of_le <| by simpa using Fintype.mem_piFinset.mp ha i ];
        exact Finset.mem_filter.mp ht |>.1 |> Finset.mem_filter.mp |>.2;
      intro q; rw [ ← h_sum ] ; simp +decide [ Finset.sum_add_distrib, refinedType ] ;
      rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_le_sum fun i _ => by split_ifs <;> omega;
    · convert Finset.sum_congr rfl fun i _ => show refinedType Q t a ( evenChild Q i ) + refinedType Q t a ( oddChild Q i ) = t i from ?_ using 1;
      any_goals exact Finset.univ;
      · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun i => evenChild Q i ) Finset.univ ∪ Finset.image ( fun i => oddChild Q i ) Finset.univ ) ) ];
        · rw [ Finset.sum_union ];
          · rw [ Finset.sum_add_distrib, Finset.sum_image, Finset.sum_image ] <;> norm_num [ evenChild, oddChild ]; all_goals exact fun i j h => by simpa [ Fin.ext_iff ] using h;
          · norm_num [ Finset.disjoint_left, evenChild, oddChild ];
            exact fun a x => ne_of_apply_ne ( fun n => n % 2 ) ( by norm_num [ Nat.add_mod, Nat.mul_mod ] );
        · grind +suggestions;
      · exact Eq.symm ( Finset.mem_filter.mp ht |>.2 |> fun h => by simpa using Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.2 );
      · rw [ refinedType_even, refinedType_odd ];
        exact Nat.add_sub_of_le ( Finset.mem_range_succ_iff.mp ( Fintype.mem_piFinset.mp ha i ) );
  · -- The sum of the counts of the refined type is equal to the sum of the counts of the original type.
    have h_sum : ∑ i, t i = r := by
      exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.2;
    have h_prod : ∏ q, (q.val + 1) ^ (refinedType Q t a q) ≤ ∏ i, (2 * (i.val + 1)) ^ (t i) := by
      have h_prod : ∏ q, (q.val + 1) ^ (refinedType Q t a q) ≤ ∏ i, ((evenChild Q i).val + 1) ^ (a i) * ((oddChild Q i).val + 1) ^ (t i - a i) := by
        have h_prod : ∏ q, (q.val + 1) ^ (refinedType Q t a q) ≤ ∏ q ∈ Finset.image (fun i => evenChild Q i) Finset.univ ∪ Finset.image (fun i => oddChild Q i) Finset.univ, (q.val + 1) ^ (refinedType Q t a q) := by
          rw [ ← Finset.prod_subset ( Finset.subset_univ _ ) ];
          intro x hx hx'; rw [ refinedType_other ] ; aesop;
          grind +locals;
        rw [ Finset.prod_union ] at h_prod;
        · rw [ Finset.prod_image, Finset.prod_image ] at h_prod;
          · simp_all +decide [ Finset.prod_mul_distrib, refinedType_even, refinedType_odd ];
          · intro i hi j hj hij; simp_all +decide [ Fin.ext_iff, oddChild ] ;
          · exact fun i _ j _ hij => Fin.ext <| by simpa [ evenChild ] using congr_arg Fin.val hij;
        · norm_num [ Finset.disjoint_left, evenChild, oddChild ];
          exact fun a x => ne_of_apply_ne ( fun n => n % 2 ) ( by norm_num [ Nat.add_mod, Nat.mul_mod ] );
      refine le_trans h_prod ?_;
      refine Finset.prod_le_prod' fun i _ => ?_;
      refine' le_trans ( Nat.mul_le_mul ( pow_le_pow_left' ( show ( evenChild Q i : ℕ ) + 1 ≤ 2 * ( i + 1 ) from _ ) _ ) ( pow_le_pow_left' ( show ( oddChild Q i : ℕ ) + 1 ≤ 2 * ( i + 1 ) from _ ) _ ) ) _;
      · exact Nat.succ_le_of_lt ( Nat.mul_lt_mul_of_pos_left ( Nat.lt_succ_self _ ) zero_lt_two );
      · simp +arith +decide [ oddChild ];
      · rw [ ← pow_add, Nat.add_sub_of_le ];
        exact Finset.mem_range_succ_iff.mp ( Fintype.mem_piFinset.mp ha i );
    simp_all +decide [ Finset.prod_mul_distrib, mul_pow, Finset.prod_pow_eq_pow_sum ];
    refine' le_trans h_prod _;
    have h_prod_le : ∏ x : Fin (NQ Q), (x.val + 1) ^ (t x) ≤ 2 ^ (Q * r) := by
      exact Finset.mem_filter.mp ht |>.2;
    exact le_trans ( Nat.mul_le_mul_left _ h_prod_le ) ( by ring_nf; norm_num )

lemma splitWeight_sum (r Q : ℕ) (t : Fin (NQ Q) → ℕ)
    (ht : t ∈ types r Q) :
    ∑ a ∈ splitChoices Q t, splitWeight r Q t a = 1 := by
  -- The sum over `a` is the product of binomial coefficients for each `i`, which equals $(2^{t i})$.
  have hsum : ∑ a ∈ splitChoices Q t, (splitWeight r Q t a) = (2 ^ (-r : ℤ)) * (∏ i, (∑ a_i ∈ Finset.range (t i + 1), (t i).choose a_i)) := by
    simp +decide [ splitWeight, splitChoices ];
    simp +decide only [Fintype.piFinset, ← Finset.mul_sum _ _ _];
    simp +decide [ Finset.prod_sum, Finset.sum_map ];
  simp_all +decide [ Nat.sum_range_choose ];
  rw [ Finset.prod_pow_eq_pow_sum, inv_mul_eq_div, div_eq_iff ] <;> norm_cast <;> norm_num [ Finset.mem_filter.mp ht |>.2 ]

set_option maxHeartbeats 5000000 in
lemma splitWeight_even_diag (r Q : ℕ) (t : Fin (NQ Q) → ℕ)
    (ht : t ∈ types r Q) (i : Fin (NQ Q)) :
    ∑ a ∈ splitChoices Q t, splitWeight r Q t a * (a i).choose 2 =
      (1 / 4 : ℝ) * (t i).choose 2 := by
  -- Let's simplify the expression inside the sum.
  have h_simp : (∑ a ∈ splitChoices Q t, (splitWeight r Q t a : ℝ) * ((a i).choose 2)) = (2 : ℝ) ^ (-(r : ℤ)) * (∏ j, (∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j * (if j = i then (a_j.choose 2 : ℝ) else 1))) := by
    rw [ Finset.prod_sum ];
    simp +decide [ splitWeight, splitChoices, Finset.mul_sum _ _ _ ];
    refine' Finset.sum_bij ( fun x hx => fun j _ => x j ) _ _ _ _ <;> simp +decide [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
    · simp +contextual [ funext_iff ];
    · exact fun b hb => ⟨ fun j => b j ( Finset.mem_univ j ), hb, rfl ⟩;
    · intro a ha; rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i ) ] ; ring;
  -- Let's simplify the expression inside the product.
  have h_prod : (∏ j, (∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j * (if j = i then (a_j.choose 2 : ℝ) else 1))) = (∑ a_i ∈ Finset.range (t i + 1), (t i).choose a_i * (a_i.choose 2 : ℝ)) * (∏ j ∈ Finset.univ.erase i, (∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j)) := by
    rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i ) ] ; norm_num [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ] ;
  -- Let's simplify the expression inside the sum further.
  have h_sum : (∑ a_i ∈ Finset.range (t i + 1), (t i).choose a_i * (a_i.choose 2 : ℝ)) = (t i).choose 2 * 2 ^ (t i - 2) * (if t i ≥ 2 then 1 else 0) := by
    have := binomial_splitting ( t i );
    split_ifs <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, zpow_neg  ];
    · convert congr_arg ( · * ( 2 ^ t i : ℝ ) ) this.2.2.1 using 1 <;> norm_num [ Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, pow_add ];
      exact Or.inl ( by rw [ show ( 2 : ℝ ) ^ t i = 2 ^ ( t i - 2 ) * 2 ^ 2 by rw [ ← pow_add, Nat.sub_add_cancel ‹2 ≤ t i› ] ] ; ring );
    · interval_cases t i <;> norm_num [ Finset.sum_range_succ ];
  -- Let's simplify the expression inside the product further.
  have h_prod_simp : (∏ j ∈ Finset.univ.erase i, (∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j)) = 2 ^ (r - t i) := by
    have h_prod_simp : (∏ j ∈ Finset.univ.erase i, (∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j)) = (∏ j ∈ Finset.univ.erase i, 2 ^ (t j)) := by
      exact Finset.prod_congr rfl fun _ _ => by rw [ Nat.sum_range_choose ] ;
    rw [ h_prod_simp, Finset.prod_pow_eq_pow_sum ];
    exact congr_arg _ ( eq_tsub_of_add_eq <| by rw [ Finset.sum_erase_add _ _ ( Finset.mem_univ _ ) ] ; linarith [ Finset.mem_filter.mp ht |>.2 ] );
  split_ifs at * <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ];
  field_simp;
  rw [ show r = t i + ( r - t i ) by rw [ Nat.add_sub_of_le ( show t i ≤ r from by { have := Finset.mem_filter.mp ht; exact this.2 ▸ Finset.single_le_sum ( fun a _ => Nat.zero_le ( t a ) ) ( Finset.mem_univ i ) } ) ] ] ; ring_nf;
  rw [ show t i = 2 + ( t i - 2 ) by rw [ Nat.add_sub_cancel' ‹2 ≤ t i› ] ] ; norm_num [ pow_add, pow_mul ] ; ring

set_option maxHeartbeats 5000000 in
lemma splitWeight_odd_diag (r Q : ℕ) (t : Fin (NQ Q) → ℕ)
    (ht : t ∈ types r Q) (i : Fin (NQ Q)) :
    ∑ a ∈ splitChoices Q t, splitWeight r Q t a * (t i - a i).choose 2 =
      (1 / 4 : ℝ) * (t i).choose 2 := by
  convert splitWeight_even_diag r Q t ht i using 1;
  apply Finset.sum_bij (fun a _ => fun j => t j - a j);
  · simp +decide [ splitChoices ];
  · simp +contextual [ funext_iff  ];
    intro a₁ ha₁ a₂ ha₂ h x; specialize h x; rw [ tsub_right_inj ] at h <;> simp_all +decide [ splitChoices ] ;
  · intro b hb; use fun j => t j - b j; simp_all +decide [ splitChoices ] ;
    exact funext fun j => Nat.sub_sub_self ( hb j );
  · unfold splitWeight;
    simp +zetaDelta at *;
    exact fun a ha => Or.inl <| Finset.prod_congr rfl fun i _ => by rw [ Nat.choose_symm ( Finset.mem_range_succ_iff.mp <| Fintype.mem_piFinset.mp ha i ) ] ;

set_option maxHeartbeats 5000000 in
lemma splitWeight_sibling (r Q : ℕ) (t : Fin (NQ Q) → ℕ)
    (ht : t ∈ types r Q) (i : Fin (NQ Q)) :
    ∑ a ∈ splitChoices Q t,
      splitWeight r Q t a * (a i : ℝ) * (t i - a i : ℕ) =
      (1 / 2 : ℝ) * (t i).choose 2 := by
  have h_prod : (∏ j, (∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j * (if j = i then (a_j : ℝ) * (t j - a_j) else 1))) = (∑ a_i ∈ Finset.range (t i + 1), (t i).choose a_i * (a_i : ℝ) * (t i - a_i)) * (∏ j ∈ Finset.univ.erase i, (∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j)) := by
    simp +decide [ mul_assoc, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq' ];
  have h_sum : (∑ a_i ∈ Finset.range (t i + 1), (t i).choose a_i * (a_i : ℝ) * (t i - a_i)) = (t i).choose 2 * 2 ^ (t i - 1) := by
    have := binomial_splitting ( t i );
    rcases n : t i with ( _ | _ | k ) <;> simp_all +decide [ Nat.choose_two_right, pow_succ' ];
    · norm_num [ Finset.sum_range_succ ];
    · convert congr_arg ( · * ( 2 ^ k * 2 ^ 2 : ℝ ) ) this.2.2.2 using 1 <;> norm_num [ zpow_add₀, zpow_neg ] ; ring_nf;
      · rw [ Finset.sum_mul _ _ _ ] ; rw [ Finset.sum_mul _ _ _ ] ; congr ; ext ; ring_nf;
        norm_num [ mul_assoc, ← mul_pow ] ; ring;
      · ring;
  convert congr_arg ( fun x : ℝ => ( 2 ^ ( -r : ℤ ) ) * x ) h_prod using 1;
  · rw [ Finset.prod_sum ];
    simp +decide [ splitWeight, splitChoices, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm  ];
    refine' Finset.sum_bij ( fun x hx => fun j _ => x j ) _ _ _ _ <;> simp +decide [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
    · simp +contextual [ funext_iff ];
    · exact fun b hb => ⟨ fun j => b j ( Finset.mem_univ j ), hb, rfl ⟩;
    · intro a ha; rw [ Nat.cast_sub ( ha i ) ] ; rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i ) ] ; ring;
  · rw [ h_sum ] ; norm_num [ zpow_sub₀, zpow_add₀ ] ; ring_nf;
    rw [ show ( ∏ x ∈ Finset.univ.erase i, ∑ x_1 ∈ Finset.range ( 1 + t x ), ( t x |> Nat.choose ) x_1 : ℝ ) = 2 ^ ( r - t i ) from ?_ ] ; ring_nf;
    · rcases k : t i with ( _ | _ | k ) <;> simp_all +decide [ pow_add ];
      field_simp;
      rw [ show r = ( ‹_› + 1 + 1 ) + ( r - ( ‹_› + 1 + 1 ) ) by rw [ Nat.add_sub_of_le ( by linarith [ Finset.mem_filter.mp ht |>.2, Finset.single_le_sum ( fun a _ => Nat.zero_le ( t a ) ) ( Finset.mem_univ i ) ] ) ] ] ; norm_num [ pow_add, pow_mul ] ; ring;
    · norm_cast;
      rw [ Finset.prod_congr rfl fun _ _ => by rw [ add_comm, Nat.sum_range_choose ] ] ; norm_num [ Finset.prod_pow_eq_pow_sum, Finset.sum_erase ];
      exact eq_tsub_of_add_eq <| by rw [ Finset.sum_erase_add _ _ ( Finset.mem_univ _ ) ] ; linarith [ Finset.mem_filter.mp ht |>.2 ] ;

def childCount (t a : Fin (NQ Q) → ℕ) (even : Bool) (i : Fin (NQ Q)) : ℕ :=
  if even then a i else t i - a i

set_option maxHeartbeats 5000000 in
lemma splitWeight_distinct (r Q : ℕ) (t : Fin (NQ Q) → ℕ)
    (ht : t ∈ types r Q) (i j : Fin (NQ Q)) (hij : i ≠ j) (ei ej : Bool) :
    ∑ a ∈ splitChoices Q t,
      splitWeight r Q t a * (childCount t a ei i : ℝ) * (childCount t a ej j : ℝ) =
      (1 / 4 : ℝ) * (t i : ℝ) * (t j : ℝ) := by
  by_cases h_cases : ei = true ∧ ej = true ∨ ei = true ∧ ej = false ∨ ei = false ∧ ej = true ∨ ei = false ∧ ej = false;
  · rcases h_cases with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num [ splitWeight, splitChoices, childCount ] at *;
    · have h_split : ∑ a ∈ Fintype.piFinset (fun i => Finset.range (t i + 1)), (∏ i, (t i).choose (a i)) * (a i : ℝ) * (a j : ℝ) = (∏ k ∈ Finset.univ \ {i, j}, (∑ a_k ∈ Finset.range (t k + 1), (t k).choose a_k)) * (∑ a_i ∈ Finset.range (t i + 1), (t i).choose a_i * (a_i : ℝ)) * (∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j * (a_j : ℝ)) := by
        have h_split : ∑ a ∈ Fintype.piFinset (fun i => Finset.range (t i + 1)), (∏ i, (t i).choose (a i)) * (a i : ℝ) * (a j : ℝ) = ∏ k, (∑ a_k ∈ Finset.range (t k + 1), (t k).choose a_k * (if k = i then (a_k : ℝ) else if k = j then (a_k : ℝ) else 1)) := by
          rw [ Finset.prod_sum ];
          refine' Finset.sum_bij ( fun a ha => fun k _ => a k ) _ _ _ _ <;> simp +decide [ Finset.prod_ite   ];
          · simp +contextual [ funext_iff ];
          · exact fun b hb => ⟨ fun k => b k ( Finset.mem_univ k ), hb, rfl ⟩;
          · intro a ha; simp +decide [ Finset.prod_filter, Finset.prod_mul_distrib, mul_assoc, mul_comm, mul_left_comm  ] ;
            simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', mul_comm, mul_left_comm  ];
            split_ifs <;> simp_all +decide;
            rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i ), ← Finset.mul_prod_erase _ _ ( Finset.mem_erase_of_ne_of_mem ‹_› ( Finset.mem_univ j ) ) ] ; ring_nf ; aesop;
        rw [ h_split, ← Finset.prod_sdiff ( Finset.subset_univ { i, j } ) ];
        simp +decide [ Finset.prod_pair hij, mul_assoc ];
        exact Or.inl ( Finset.prod_congr rfl fun x hx => by aesop );
      have h_sum : (∑ a_i ∈ Finset.range (t i + 1), (t i).choose a_i * (a_i : ℝ)) = (t i : ℝ) * 2 ^ (t i - 1) ∧ (∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j * (a_j : ℝ)) = (t j : ℝ) * 2 ^ (t j - 1) := by
        have h_sum : ∀ n : ℕ, ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * a = n * 2 ^ (n - 1) := by
          intro n; rw_mod_cast [ ← Nat.sum_range_choose ] ;
          rw [ Finset.mul_sum _ _ _ ];
          cases n <;> simp +decide [ Finset.sum_range_succ', Nat.add_one_mul_choose_eq ];
        exact ⟨ h_sum _, h_sum _ ⟩;
      convert congr_arg ( fun x : ℝ => ( 2 ^ r : ℝ ) ⁻¹ * x ) h_split using 1 <;> norm_num [ h_sum ] ; ring_nf;
      · simp +decide only [mul_assoc, Finset.mul_sum _ _ _];
      · have h_prod : (∏ x ∈ Finset.univ \ {i, j}, ∑ x_1 ∈ Finset.range (t x + 1), (t x).choose x_1 : ℝ) = 2 ^ (r - t i - t j) := by
          have h_prod : (∏ x ∈ Finset.univ \ {i, j}, ∑ x_1 ∈ Finset.range (t x + 1), (t x).choose x_1 : ℝ) = 2 ^ (∑ x ∈ Finset.univ \ {i, j}, t x) := by
            rw [ ← Finset.prod_pow_eq_pow_sum ] ; exact Finset.prod_congr rfl fun x hx => mod_cast Nat.sum_range_choose _;
          have h_sum : ∑ x ∈ Finset.univ, t x = r := by
            exact Finset.mem_filter.mp ht |>.2;
          rw [ h_prod, ← h_sum, ← Finset.sum_sdiff ( Finset.subset_univ { i, j } ) ] ; simp +decide [ Finset.sum_pair hij ] ; ring_nf;
          exact eq_tsub_of_add_eq <| eq_tsub_of_add_eq <| by ring;
        by_cases hi : t i = 0 <;> by_cases hj : t j = 0 <;> simp_all +decide [ Nat.sub_sub ];
        field_simp;
        rw [ show r = ( t i + t j ) + ( r - ( t i + t j ) ) by rw [ Nat.add_sub_of_le ( show t i + t j ≤ r from by { have := Finset.mem_filter.mp ht; exact this.2 ▸ Finset.sum_le_sum_of_subset ( Finset.subset_univ { i, j } ) |> le_trans ( by simp +decide [ *  ] ) } ) ] ] ; ring_nf;
        cases k : t i <;> cases l : t j <;> simp_all +decide [ pow_add ] ; ring;
    · have h_split : ∑ x ∈ Fintype.piFinset (fun i => Finset.range (t i + 1)), (∏ i, (t i).choose (x i) : ℝ) * (x i : ℝ) * (t j - x j : ℕ) = (∑ a_i ∈ Finset.range (t i + 1), (t i).choose a_i * (a_i : ℝ)) * (∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j * (t j - a_j : ℕ)) * (∏ k ∈ Finset.univ \ {i, j}, (∑ a_k ∈ Finset.range (t k + 1), (t k).choose a_k)) := by
        have h_split : ∑ x ∈ Fintype.piFinset (fun i => Finset.range (t i + 1)), (∏ i, (t i).choose (x i) : ℝ) * (x i : ℝ) * (t j - x j : ℕ) = ∏ k, (∑ a_k ∈ Finset.range (t k + 1), (t k).choose a_k * (if k = i then (a_k : ℝ) else if k = j then (t j - a_k : ℕ) else 1)) := by
          rw [ Finset.prod_sum ];
          refine' Finset.sum_bij ( fun x hx => fun k _ => x k ) _ _ _ _ <;> simp +decide [ Finset.prod_mul_distrib, Finset.prod_ite   ];
          · simp +contextual [ funext_iff ];
          · exact fun b hb => ⟨ fun k => b k ( Finset.mem_univ k ), hb, rfl ⟩;
          · intro a ha; simp +decide [ Finset.prod_filter, mul_assoc, mul_comm, mul_left_comm   ] ;
            simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', mul_comm, mul_left_comm   ];
            rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i ), ← Finset.mul_prod_erase _ _ ( Finset.mem_erase_of_ne_of_mem ( by tauto ) ( Finset.mem_univ j ) ) ] ; aesop;
        rw [ h_split, ← Finset.prod_sdiff ( Finset.subset_univ { i, j } ) ];
        simp +decide [ Finset.prod_pair hij    ] ; ring_nf;
        rw [ if_neg ( Ne.symm hij ) ] ; rw [ Finset.prod_congr rfl fun x hx => by rw [ if_neg ( by aesop ), if_neg ( by aesop ) ] ] ; ring;
      have h_sum_i : ∑ a_i ∈ Finset.range (t i + 1), (t i).choose a_i * (a_i : ℝ) = (t i : ℝ) * 2 ^ (t i - 1) := by
        rw_mod_cast [ ← Nat.sum_range_choose, Finset.mul_sum _ _ _ ];
        cases t_i : t i <;> simp_all +decide [ Nat.add_one_mul_choose_eq, Finset.sum_range_succ' ]
      have h_sum_j : ∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j * (t j - a_j : ℕ) = (t j : ℝ) * 2 ^ (t j - 1) := by
        have h_sum_j : ∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j * (t j - a_j : ℕ) = ∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j * a_j := by
          rw [ ← Finset.sum_flip ];
          exact Finset.sum_congr rfl fun x hx => by rw [ Nat.choose_symm ( Finset.mem_range_succ_iff.mp hx ), tsub_tsub_cancel_of_le ( Finset.mem_range_succ_iff.mp hx ) ] ;
        have h_sum_j : ∑ a_j ∈ Finset.range (t j + 1), (t j).choose a_j * a_j = t j * 2 ^ (t j - 1) := by
          rw [ ← Nat.sum_range_choose, Finset.mul_sum _ _ _ ];
          cases t_j : t j <;> simp_all +decide [ Nat.add_one_mul_choose_eq, Finset.sum_range_succ' ];
        aesop
      have h_prod : ∏ k ∈ Finset.univ \ {i, j}, (∑ a_k ∈ Finset.range (t k + 1), (t k).choose a_k) = 2 ^ (r - t i - t j) := by
        have h_prod : ∏ k ∈ Finset.univ \ {i, j}, (∑ a_k ∈ Finset.range (t k + 1), (t k).choose a_k) = 2 ^ (∑ k ∈ Finset.univ \ {i, j}, t k) := by
          rw [ ← Finset.prod_pow_eq_pow_sum ] ; exact Finset.prod_congr rfl fun x hx => by rw [ Nat.sum_range_choose ] ;
        have h_sum : ∑ k ∈ Finset.univ, t k = r := by
          exact Finset.mem_filter.mp ht |>.2
        have h_sum_ij : ∑ k ∈ {i, j}, t k = t i + t j := by
          rw [ Finset.sum_pair hij ]
        have h_sum_rest : ∑ k ∈ Finset.univ \ {i, j}, t k = r - t i - t j := by
          exact eq_tsub_of_add_eq <| eq_tsub_of_add_eq <| by rw [ ← h_sum, ← Finset.sum_sdiff <| Finset.subset_univ { i, j } ] ; simp +decide [ *  ] ; ring;
        rw [h_prod, h_sum_rest];
      simp_all +decide [ mul_assoc  ];
      rw [ ← Finset.mul_sum _ _ _, h_split ];
      field_simp;
      rw [ show r = t i + t j + ( r - t i - t j ) by rw [ Nat.sub_sub, add_tsub_cancel_of_le ] ; linarith [ Finset.mem_filter.mp ht |>.2, show t i + t j ≤ r from by { have := Finset.mem_filter.mp ht; exact this.2 ▸ by { rw [ ← Finset.sum_pair hij ] ; exact Finset.sum_le_sum_of_subset ( Finset.subset_univ { i, j } ) } } ] ] ; norm_num [ pow_add, pow_mul ] ; ring_nf;
      rcases k : t i with ( _ | k ) <;> rcases l : t j with ( _ | l ) <;> simp_all +decide [ pow_add ] ; ring_nf;
      grind;
    · have h_sum : ∑ x ∈ Fintype.piFinset fun i => Finset.range (t i + 1), (∏ i, (Nat.choose (t i) (x i) : ℝ)) * (t i - x i) * x j = (t i) * (t j) * 2 ^ (r - 2) := by
        have h_sum : ∑ x ∈ Fintype.piFinset fun i => Finset.range (t i + 1), (∏ i, (Nat.choose (t i) (x i) : ℝ)) * (t i - x i) * x j = (∑ x_i ∈ Finset.range (t i + 1), (Nat.choose (t i) x_i : ℝ) * (t i - x_i)) * (∑ x_j ∈ Finset.range (t j + 1), (Nat.choose (t j) x_j : ℝ) * x_j) * (∏ k ∈ Finset.univ \ {i, j}, (∑ x_k ∈ Finset.range (t k + 1), (Nat.choose (t k) x_k : ℝ))) := by
          have h_sum : ∑ x ∈ Fintype.piFinset fun i => Finset.range (t i + 1), (∏ i, (Nat.choose (t i) (x i) : ℝ)) * (t i - x i) * x j = ∏ k, (∑ x_k ∈ Finset.range (t k + 1), (Nat.choose (t k) x_k : ℝ) * (if k = i then (t i - x_k : ℝ) else if k = j then x_k else 1)) := by
            rw [ Finset.prod_sum ];
            refine' Finset.sum_bij ( fun x hx => fun k _ => x k ) _ _ _ _ <;> simp +decide [ Finset.prod_ite   ];
            · simp +contextual [ funext_iff ];
            · exact fun b hb => ⟨ fun k => b k ( Finset.mem_univ k ), hb, rfl ⟩;
            · intro a ha; simp +decide [ Finset.prod_filter, Finset.prod_mul_distrib  ] ;
              simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', mul_assoc, mul_comm, mul_left_comm, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', mul_assoc, mul_comm, mul_left_comm, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', mul_assoc, mul_comm, mul_left_comm, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', mul_assoc, mul_comm, mul_left_comm, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', mul_assoc, mul_comm, mul_left_comm, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', mul_assoc, mul_comm, mul_left_comm, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', mul_assoc, mul_comm, mul_left_comm, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', mul_assoc, mul_comm, mul_left_comm ];
              split_ifs <;> simp_all +decide;
              rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i ), ← Finset.mul_prod_erase _ _ ( Finset.mem_erase_of_ne_of_mem ‹_› ( Finset.mem_univ j ) ) ] ; aesop;
          rw [ h_sum, ← Finset.prod_sdiff <| Finset.subset_univ { i, j } ];
          simp +decide [ Finset.prod_pair hij, mul_comm ];
          rw [ if_neg ( Ne.symm hij ) ] ; exact congr_arg₂ _ rfl ( Finset.prod_congr rfl fun x hx => by aesop ) ;
        have h_sum_i : ∑ x_i ∈ Finset.range (t i + 1), (Nat.choose (t i) x_i : ℝ) * (t i - x_i) = t i * 2 ^ (t i - 1) := by
          have h_sum_i : ∑ x_i ∈ Finset.range (t i + 1), (Nat.choose (t i) x_i : ℝ) * x_i = (t i : ℝ) * 2 ^ (t i - 1) := by
            rw_mod_cast [ ← Nat.sum_range_choose, Finset.mul_sum _ _ _ ];
            cases k : t i <;> simp_all +decide [ Nat.add_one_mul_choose_eq, Finset.sum_range_succ' ];
          simp_all +decide [ mul_sub, Finset.sum_sub_distrib ];
          rw [ ← Finset.sum_mul _ _ _ ] ; norm_cast ; simp +decide [ Nat.sum_range_choose ] ; ring_nf;
          rw [ Int.subNatNat_eq_coe ] ; cases t_i : t i <;> simp_all +decide [ pow_succ' ] ; ring
        have h_sum_j : ∑ x_j ∈ Finset.range (t j + 1), (Nat.choose (t j) x_j : ℝ) * x_j = t j * 2 ^ (t j - 1) := by
          rw_mod_cast [ ← Nat.sum_range_choose ];
          rw [ Finset.mul_sum _ _ _ ];
          cases k : t j <;> simp_all +decide [ Nat.add_one_mul_choose_eq, Finset.sum_range_succ' ]
        have h_prod : ∏ k ∈ Finset.univ \ {i, j}, (∑ x_k ∈ Finset.range (t k + 1), (Nat.choose (t k) x_k : ℝ)) = 2 ^ (r - t i - t j) := by
          have h_prod : ∏ k ∈ Finset.univ \ {i, j}, (∑ x_k ∈ Finset.range (t k + 1), (Nat.choose (t k) x_k : ℝ)) = 2 ^ (∑ k ∈ Finset.univ \ {i, j}, t k) := by
            rw [ ← Finset.prod_pow_eq_pow_sum ] ; exact Finset.prod_congr rfl fun x hx => mod_cast Nat.sum_range_choose _;
          have h_sum : ∑ k ∈ Finset.univ, t k = r := by
            exact Finset.mem_filter.mp ht |>.2;
          rw [ h_prod, ← h_sum, ← Finset.sum_sdiff ( Finset.subset_univ { i, j } ) ];
          simp +decide [ Finset.sum_pair hij, Nat.sub_sub ]
        simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        rcases k : t i with ( _ | k ) <;> rcases l : t j with ( _ | l ) <;> simp_all +decide [ ← pow_add ];
        have := Finset.mem_filter.mp ht |>.2; simp_all +decide [ Finset.sum_range_succ ] ;
        rw [ ← this, ← Finset.sum_sdiff ( Finset.subset_univ { i, j } ) ] ; simp +decide [ *, Finset.sum_pair hij ] ; ring_nf;
        omega;
      convert congr_arg ( fun x : ℝ => ( 2 ^ r ) ⁻¹ * x ) h_sum using 1 <;> norm_num [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, pow_add ] ; ring_nf;
      · refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Nat.cast_sub ( by linarith [ Finset.mem_range.mp ( Fintype.mem_piFinset.mp hx i ) ] ) ] ; ring;
      · rcases r with ( _ | _ | r ) <;> norm_num [ pow_succ' ] at *;
        · simp_all +decide [ types ];
        · have := Finset.mem_filter.mp ht; simp_all +decide ;
          have := Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ( fun a => t a ) ; simp_all +decide ;
          exact Classical.or_iff_not_imp_left.2 fun h => by linarith [ Finset.single_le_sum ( fun a _ => Nat.zero_le ( t a ) ) ( Finset.mem_sdiff.2 ⟨ Finset.mem_univ j, by aesop ⟩ : j ∈ Finset.univ \ { i } ), Nat.pos_of_ne_zero h ] ;
        · ring_nf;
          norm_num [ ← mul_pow ];
    · -- Apply the binomial splitting lemma to simplify the sum.
      have h_split : ∑ x ∈ Fintype.piFinset (fun i => Finset.range (t i + 1)), (∏ i, (Nat.choose (t i) (x i) : ℝ)) * ((t i - x i) : ℝ) * ((t j - x j) : ℝ) = (Nat.choose (t i) 1 : ℝ) * (Nat.choose (t j) 1 : ℝ) * 2 ^ (r - 2) := by
        have h_split : ∑ x ∈ Fintype.piFinset (fun i => Finset.range (t i + 1)), (∏ i, (Nat.choose (t i) (x i) : ℝ)) * ((t i - x i) : ℝ) * ((t j - x j) : ℝ) = (∑ x_i ∈ Finset.range (t i + 1), (Nat.choose (t i) x_i : ℝ) * ((t i - x_i) : ℝ)) * (∑ x_j ∈ Finset.range (t j + 1), (Nat.choose (t j) x_j : ℝ) * ((t j - x_j) : ℝ)) * (∏ k ∈ Finset.univ \ {i, j}, (∑ x_k ∈ Finset.range (t k + 1), (Nat.choose (t k) x_k : ℝ))) := by
          have h_split : ∑ x ∈ Fintype.piFinset (fun i => Finset.range (t i + 1)), (∏ i, (Nat.choose (t i) (x i) : ℝ)) * ((t i - x i) : ℝ) * ((t j - x j) : ℝ) = (∏ k, (∑ x_k ∈ Finset.range (t k + 1), (Nat.choose (t k) x_k : ℝ) * (if k = i then (t i - x_k : ℝ) else if k = j then (t j - x_k : ℝ) else 1))) := by
            rw [ Finset.prod_sum ];
            refine' Finset.sum_bij ( fun x hx => fun k _ => x k ) _ _ _ _ <;> simp +decide [ Finset.prod_ite   ];
            · simp +contextual [ funext_iff ];
            · exact fun b hb => ⟨ fun k => b k ( Finset.mem_univ k ), hb, rfl ⟩;
            · intro a ha; simp +decide [ Finset.prod_filter, Finset.prod_mul_distrib  ] ; ring_nf;
              simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq'      ] ; ring_nf;
              rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i ), ← Finset.mul_prod_erase _ _ ( Finset.mem_erase_of_ne_of_mem ( by aesop ) ( Finset.mem_univ j ) ) ] ; ring_nf;
              grind;
          rw [ h_split, ← Finset.prod_sdiff <| Finset.subset_univ { i, j } ];
          simp +decide [ Finset.prod_pair hij, mul_comm ];
          rw [ if_neg ( Ne.symm hij ) ] ; exact congr_arg₂ _ rfl ( Finset.prod_congr rfl fun x hx => by aesop ) ;
        have h_split : ∀ k, ∑ x_k ∈ Finset.range (t k + 1), (Nat.choose (t k) x_k : ℝ) = 2 ^ (t k) := by
          exact fun k => mod_cast Nat.sum_range_choose _;
        have h_split : ∀ k, ∑ x_k ∈ Finset.range (t k + 1), (Nat.choose (t k) x_k : ℝ) * ((t k - x_k) : ℝ) = (t k : ℝ) * 2 ^ (t k - 1) := by
          intro k; have := binomial_splitting ( t k ) ; simp_all +decide [ mul_comm, Finset.mul_sum _ _ _ ] ;
          convert congr_arg ( fun x : ℝ => x * 2 ^ t k ) this.2.1 using 1 <;> norm_num [ Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, pow_succ' ] ; ring_nf;
          · rw [ add_comm, ← Finset.sum_flip ];
            exact Finset.sum_congr rfl fun x hx => by rw [ Nat.choose_symm ( Finset.mem_range_succ_iff.mp hx ), Nat.cast_sub ( Finset.mem_range_succ_iff.mp hx ) ] ; ring;
          · cases n : t k <;> simp_all +decide [ pow_succ' ] ; ring;
        simp_all +decide [ Finset.prod_pow_eq_pow_sum ];
        have h_sum : ∑ i ∈ Finset.univ, t i = r := by
          exact Finset.mem_filter.mp ht |>.2;
        rw [ ← h_sum, ← Finset.sum_sdiff ( Finset.subset_univ { i, j } ) ] ; simp +decide [ Finset.sum_pair hij ] ; ring_nf;
        rcases k : t i with ( _ | k ) <;> rcases l : t j with ( _ | l ) <;> simp_all +decide ; ring_nf;
        norm_num [ add_assoc, add_tsub_assoc_of_le ] ; ring;
      convert congr_arg ( fun x : ℝ => ( 2 ^ r : ℝ ) ⁻¹ * x ) h_split using 1 <;> norm_num [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ];
      · exact Finset.sum_congr rfl fun x hx => by rw [ Nat.cast_sub ( Finset.mem_range_succ_iff.mp ( Fintype.mem_piFinset.mp hx i ) ), Nat.cast_sub ( Finset.mem_range_succ_iff.mp ( Fintype.mem_piFinset.mp hx j ) ) ] ;
      · rcases r with ( _ | _ | r ) <;> norm_num [ pow_succ' ] at *;
        · simp_all +decide [ types ];
        · have := Finset.mem_filter.mp ht |>.2; simp_all +decide [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ] ;
          exact Classical.or_iff_not_imp_left.2 fun h => by linarith [ Nat.pos_of_ne_zero h, Finset.single_le_sum ( fun a _ => Nat.zero_le ( t a ) ) ( Finset.mem_sdiff.2 ⟨ Finset.mem_univ j, by aesop ⟩ : j ∈ Finset.univ \ { i } ) ] ;
        · ring_nf; norm_num;
          norm_num [ ← mul_pow ];
  · cases ei <;> cases ej <;> tauto

/-- The weighting obtained by distributing every coarse type among all its
binomially weighted refinements. -/
noncomputable def refinementWeighting (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) : (Fin (NQ (Q + 1)) → ℕ) → ℝ := fun s =>
  ∑ t ∈ admTypes r Q, ∑ a ∈ splitChoices Q t,
    if refinedType Q t a = s then splitWeight r Q t a * z t else 0

lemma refinementWeighting_nonneg (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : ∀ t, 0 ≤ z t) (s : Fin (NQ (Q + 1)) → ℕ) :
    0 ≤ refinementWeighting r Q z s := by
  unfold refinementWeighting
  exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun a _ => by
    split_ifs
    · exact mul_nonneg (by unfold splitWeight; positivity) (hz t)
    · exact le_rfl

lemma refinementWeighting_sum (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (F : (Fin (NQ (Q + 1)) → ℕ) → ℝ) :
    ∑ s ∈ admTypes r (Q + 1), F s * refinementWeighting r Q z s =
      ∑ t ∈ admTypes r Q, ∑ a ∈ splitChoices Q t,
        F (refinedType Q t a) * (splitWeight r Q t a * z t) := by
  simp +decide only [refinementWeighting, Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro t ht; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ;
  rw [ Finset.filter_true_of_mem ];
  exact fun x hx => refinedType_mem_admTypes r Q t ht x hx

lemma refinementWeighting_value (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) :
    valQ r (Q + 1) (refinementWeighting r Q z) = valQ r Q z := by
  unfold valQ
  have h := refinementWeighting_sum r Q z (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [← Finset.sum_mul, splitWeight_sum r Q t (Finset.mem_filter.mp ht).1]
  simp

lemma fineIndex_child_or_other (Q : ℕ) (q : Fin (NQ (Q + 1))) :
    (∃ i, q = evenChild Q i) ∨ (∃ i, q = oddChild Q i) ∨
      (∀ i, q ≠ evenChild Q i ∧ q ≠ oddChild Q i) := by
  by_cases he : ∃ i, q = evenChild Q i
  · exact Or.inl he
  by_cases ho : ∃ i, q = oddChild Q i
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr fun i => ⟨fun h => he ⟨i, h⟩, fun h => ho ⟨i, h⟩⟩)

def fineChild (Q : ℕ) (even : Bool) (i : Fin (NQ Q)) : Fin (NQ (Q + 1)) :=
  if even then evenChild Q i else oddChild Q i

lemma refinedType_fineChild (Q : ℕ) (t a : Fin (NQ Q) → ℕ) (even : Bool)
    (i : Fin (NQ Q)) :
    refinedType Q t a (fineChild Q even i) = childCount t a even i := by
  cases even <;> simp [fineChild, childCount, refinedType_even, refinedType_odd]

lemma refinementWeighting_distinct_moment (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (i j : Fin (NQ Q)) (hij : i ≠ j)
    (ei ej : Bool) :
    ∑ s ∈ admTypes r (Q + 1),
        ((s (fineChild Q ei i) : ℝ) * s (fineChild Q ej j)) *
          refinementWeighting r Q z s =
      (1 / 4 : ℝ) * ∑ t ∈ admTypes r Q, ((t i : ℝ) * t j) * z t := by
  rw [refinementWeighting_sum]
  simp only [refinedType_fineChild]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    ∑ a ∈ splitChoices Q t,
        (childCount t a ei i : ℝ) * childCount t a ej j *
          (splitWeight r Q t a * z t) =
        (∑ a ∈ splitChoices Q t,
          splitWeight r Q t a * (childCount t a ei i : ℝ) *
            childCount t a ej j) * z t := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro a ha
              ring
    _ = (1 / 4 : ℝ) * ((t i : ℝ) * t j * z t) := by
      rw [splitWeight_distinct r Q t (Finset.mem_filter.mp ht).1 i j hij ei ej]
      ring

lemma refinementWeighting_sibling_moment (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (i : Fin (NQ Q)) :
    ∑ s ∈ admTypes r (Q + 1),
        ((s (evenChild Q i) : ℝ) * s (oddChild Q i)) *
          refinementWeighting r Q z s =
      (1 / 2 : ℝ) * ∑ t ∈ admTypes r Q, ((t i).choose 2 : ℝ) * z t := by
  rw [refinementWeighting_sum]
  simp only [refinedType_even, refinedType_odd]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    ∑ a ∈ splitChoices Q t,
        (a i : ℝ) * (t i - a i : ℕ) * (splitWeight r Q t a * z t) =
        (∑ a ∈ splitChoices Q t,
          splitWeight r Q t a * (a i : ℝ) * (t i - a i : ℕ)) * z t := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a ha
            ring
    _ = (1 / 2 : ℝ) * (((t i).choose 2 : ℝ) * z t) := by
      rw [splitWeight_sibling r Q t (Finset.mem_filter.mp ht).1 i]
      ring

lemma refinementWeighting_diag_moment (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (i : Fin (NQ Q)) (even : Bool) :
    ∑ s ∈ admTypes r (Q + 1),
        (((s (fineChild Q even i)).choose 2 : ℝ)) * refinementWeighting r Q z s =
      (1 / 4 : ℝ) * ∑ t ∈ admTypes r Q, ((t i).choose 2 : ℝ) * z t := by
  rw [refinementWeighting_sum]
  simp only [refinedType_fineChild]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    ∑ a ∈ splitChoices Q t,
        ((childCount t a even i).choose 2 : ℝ) * (splitWeight r Q t a * z t) =
        (∑ a ∈ splitChoices Q t,
          splitWeight r Q t a * ((childCount t a even i).choose 2 : ℝ)) * z t := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a ha
            ring
    _ = (1 / 4 : ℝ) * (((t i).choose 2 : ℝ) * z t) := by
      cases even
      · simp only [childCount, Bool.false_eq_true, ↓reduceIte]
        rw [splitWeight_odd_diag r Q t (Finset.mem_filter.mp ht).1 i]
        ring
      · simp only [childCount, ↓reduceIte]
        rw [splitWeight_even_diag r Q t (Finset.mem_filter.mp ht).1 i]
        ring

lemma refinementWeighting_other_offdiag (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (q q' : Fin (NQ (Q + 1)))
    (hq : ∀ i, q ≠ evenChild Q i ∧ q ≠ oddChild Q i) :
    ∑ s ∈ admTypes r (Q + 1), ((s q : ℝ) * s q') * refinementWeighting r Q z s = 0 := by
  rw [refinementWeighting_sum]
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.sum_eq_zero
  intro a ha
  rw [refinedType_other Q t a q hq]
  norm_num

lemma refinementWeighting_other_diag (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (q : Fin (NQ (Q + 1)))
    (hq : ∀ i, q ≠ evenChild Q i ∧ q ≠ oddChild Q i) :
    ∑ s ∈ admTypes r (Q + 1), ((s q).choose 2 : ℝ) * refinementWeighting r Q z s = 0 := by
  rw [refinementWeighting_sum]
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.sum_eq_zero
  intro a ha
  rw [refinedType_other Q t a q hq]
  norm_num

lemma refinementWeighting_child_offdiag_le (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : IsPacking r Q z)
    (i j : Fin (NQ Q)) (ei ej : Bool)
    (hij : fineChild Q ei i < fineChild Q ej j) :
    ∑ s ∈ admTypes r (Q + 1),
        ((s (fineChild Q ei i) : ℝ) * s (fineChild Q ej j)) *
          refinementWeighting r Q z s ≤
      (r : ℝ) ^ 2 * dQ (Q + 1) ^ 2 := by
  by_cases hsame : i = j
  · subst j
    have heo : ei = true ∧ ej = false := by
      cases ei <;> cases ej <;> simp [fineChild, evenChild, oddChild, Fin.lt_def] at hij ⊢
    rcases heo with ⟨rfl, rfl⟩
    change (∑ s ∈ admTypes r (Q + 1),
      ((s (evenChild Q i) : ℝ) * s (oddChild Q i)) *
        refinementWeighting r Q z s) ≤ _
    rw [refinementWeighting_sibling_moment]
    rw [dQ_succ]
    have hc := hz.2.2 i
    nlinarith [sq_nonneg (dQ Q), sq_nonneg (r : ℝ)]
  · have hile : i.val ≤ j.val := by
      cases ei <;> cases ej
      · change oddChild Q i < oddChild Q j at hij
        simp only [Fin.lt_def, oddChild] at hij
        omega
      · change oddChild Q i < evenChild Q j at hij
        simp only [Fin.lt_def, evenChild, oddChild] at hij
        omega
      · change evenChild Q i < oddChild Q j at hij
        simp only [Fin.lt_def, evenChild, oddChild] at hij
        omega
      · change evenChild Q i < evenChild Q j at hij
        simp only [Fin.lt_def, evenChild] at hij
        omega
    have hij' : i < j := Fin.lt_def.mpr (lt_of_le_of_ne hile (by
      intro h
      apply hsame
      exact Fin.ext h))
    rw [refinementWeighting_distinct_moment r Q z i j hsame ei ej]
    rw [dQ_succ]
    have hc := hz.2.1 i j hij'
    nlinarith [sq_nonneg (dQ Q), sq_nonneg (r : ℝ)]

lemma refinementWeighting_isPacking (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : IsPacking r Q z) :
    IsPacking r (Q + 1) (refinementWeighting r Q z) := by
  refine ⟨refinementWeighting_nonneg r Q z hz.1, ?_, ?_⟩
  · intro q q' hqq'
    rcases fineIndex_child_or_other Q q with ⟨i, rfl⟩ | ⟨i, rfl⟩ | hq
    · rcases fineIndex_child_or_other Q q' with ⟨j, rfl⟩ | ⟨j, rfl⟩ | hq'
      · exact refinementWeighting_child_offdiag_le r Q z hz i j true true hqq'
      · exact refinementWeighting_child_offdiag_le r Q z hz i j true false hqq'
      · have hzero := refinementWeighting_other_offdiag r Q z q' (evenChild Q i) hq'
        simpa [mul_comm] using hzero.le.trans (by positivity : (0 : ℝ) ≤ (r : ℝ) ^ 2 * dQ (Q + 1) ^ 2)
    · rcases fineIndex_child_or_other Q q' with ⟨j, rfl⟩ | ⟨j, rfl⟩ | hq'
      · exact refinementWeighting_child_offdiag_le r Q z hz i j false true hqq'
      · exact refinementWeighting_child_offdiag_le r Q z hz i j false false hqq'
      · have hzero := refinementWeighting_other_offdiag r Q z q' (oddChild Q i) hq'
        simpa [mul_comm] using hzero.le.trans (by positivity : (0 : ℝ) ≤ (r : ℝ) ^ 2 * dQ (Q + 1) ^ 2)
    · rw [refinementWeighting_other_offdiag r Q z q q' hq]
      positivity
  · intro q
    rcases fineIndex_child_or_other Q q with ⟨i, rfl⟩ | ⟨i, rfl⟩ | hq
    · change (∑ s ∈ admTypes r (Q + 1),
        ((s (fineChild Q true i)).choose 2 : ℝ) * refinementWeighting r Q z s) ≤ _
      rw [refinementWeighting_diag_moment]
      rw [dQ_succ]
      have hc := hz.2.2 i
      nlinarith [sq_nonneg (dQ Q), sq_nonneg (r : ℝ)]
    · change (∑ s ∈ admTypes r (Q + 1),
        ((s (fineChild Q false i)).choose 2 : ℝ) * refinementWeighting r Q z s) ≤ _
      rw [refinementWeighting_diag_moment]
      rw [dQ_succ]
      have hc := hz.2.2 i
      nlinarith [sq_nonneg (dQ Q), sq_nonneg (r : ℝ)]
    · rw [refinementWeighting_other_diag r Q z q hq]
      positivity

/-- Every feasible packing on a dyadic grid has a value-preserving packing
on the once-refined grid.  This is the constructive core of
`grid_monotone`. -/
theorem packing_refinement (r Q : ℕ)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : IsPacking r Q z) :
    ∃ z' : (Fin (NQ (Q + 1)) → ℕ) → ℝ,
      IsPacking r (Q + 1) z' ∧ valQ r (Q + 1) z' = valQ r Q z := by
  exact ⟨refinementWeighting r Q z, refinementWeighting_isPacking r Q z hz,
    refinementWeighting_value r Q z⟩

/--
For `r ≥ 2`, the feasible values at a fixed grid level are bounded above.
-/
theorem packing_values_bddAbove (r Q : ℕ) (hr : 2 ≤ r) :
    BddAbove {v | ∃ z, IsPacking r Q z ∧ valQ r Q z = v} := by
  by_contra h;
  -- Fix Q and let t be any r-type.
  have h_bound : ∃ M > 0, ∀ z : (Fin (NQ Q) → ℕ) → ℝ, IsPacking r Q z → ∀ t ∈ admTypes r Q, z t ≤ M := by
    -- For any type `t` in `admTypes r Q`, either `t` has a coordinate `i` with `t i ≥ 2` (diagonal), or `t` has two distinct indices `i < j` with `t i > 0` and `t j > 0` (off-diagonal).
    have h_type_bound : ∀ t ∈ admTypes r Q, ∃ i j : Fin (NQ Q), i ≤ j ∧ (i = j → 2 ≤ t i) ∧ (i < j → 0 < t i ∧ 0 < t j) := by
      intro t ht;
      by_cases h_diag : ∃ i : Fin (NQ Q), 2 ≤ t i;
      · exact ⟨ h_diag.choose, h_diag.choose, le_rfl, fun _ => h_diag.choose_spec, fun _ => False.elim <| lt_irrefl _ ‹_› ⟩;
      · -- Since there's no i with t i ≥ 2, all t i are either 0 or 1. But since the sum of t i is r and r ≥ 2, there must be at least two indices where t i is 1.
        obtain ⟨i, hi⟩ : ∃ i : Fin (NQ Q), t i = 1 := by
          have h_sum : ∑ i, t i = r := by
            exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.2;
          exact not_forall_not.mp fun h => by have := h_sum ▸ Finset.sum_eq_zero fun i _ => Nat.eq_zero_of_not_pos fun hi => h i <| by linarith [ show t i ≤ 1 from Nat.le_of_not_lt fun hi' => h_diag ⟨ i, hi' ⟩ ] ; ; linarith;
        obtain ⟨j, hj, hij⟩ : ∃ j : Fin (NQ Q), j ≠ i ∧ t j = 1 := by
          have h_sum : ∑ j, t j = r := by
            exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.2;
          rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ] at h_sum;
          exact Exists.elim ( Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ∑ x ∈ Finset.univ \ { i }, t x ≠ 0 ) ) fun x hx => ⟨ x, by aesop_cat, by linarith [ show t x = 1 from le_antisymm ( not_lt.mp fun contra => h_diag ⟨ x, contra ⟩ ) ( Nat.pos_of_ne_zero hx.2 ) ] ⟩;
        cases le_total i j <;> [ exact ⟨ i, j, ‹_›, by aesop ⟩ ; exact ⟨ j, i, ‹_›, by aesop ⟩ ];
    -- By the capacity constraints, each term in the sum is bounded by `r^2 dQ^2`.
    have h_capacity_bound : ∀ z : (Fin (NQ Q) → ℕ) → ℝ, IsPacking r Q z → ∀ t ∈ admTypes r Q, ∀ i j : Fin (NQ Q), i ≤ j → (i = j → 2 ≤ t i) → (i < j → 0 < t i ∧ 0 < t j) → z t ≤ (r : ℝ) ^ 2 * dQ Q ^ 2 := by
      intros z hz t ht i j hij h_eq h_lt
      by_cases h_eq_i : i = j;
      · have := hz.2.2 i;
        refine' le_trans _ ( le_trans this _ );
        · refine' le_trans _ ( Finset.single_le_sum ( fun x _ => mul_nonneg ( Nat.cast_nonneg _ ) ( hz.1 x ) ) ht );
          exact le_mul_of_one_le_left ( hz.1 t ) ( mod_cast Nat.choose_pos ( h_eq h_eq_i ) );
        · exact mul_le_mul_of_nonneg_right ( div_le_self ( by positivity ) ( by norm_num ) ) ( sq_nonneg _ );
      · have := hz.2.1 i j ( lt_of_le_of_ne hij h_eq_i );
        refine' le_trans _ this;
        refine' le_trans _ ( Finset.single_le_sum ( fun x _ => mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( hz.1 x ) ) ht );
        exact le_mul_of_one_le_left ( hz.1 t ) ( mod_cast Nat.mul_pos ( h_lt ( lt_of_le_of_ne hij h_eq_i ) |>.1 ) ( h_lt ( lt_of_le_of_ne hij h_eq_i ) |>.2 ) );
    exact ⟨ r ^ 2 * dQ Q ^ 2 + 1, by positivity, fun z hz t ht => by obtain ⟨ i, j, hij, hi, hj ⟩ := h_type_bound t ht; linarith [ h_capacity_bound z hz t ht i j hij hi hj ] ⟩;
  obtain ⟨ M, hM_pos, hM ⟩ := h_bound; refine' h ⟨ ∑ t ∈ admTypes r Q, M, fun v hv => _ ⟩ ; rcases hv with ⟨ z, hz, rfl ⟩ ; exact Finset.sum_le_sum fun t ht => hM z hz t ht;

/--
Monotonicity under dyadic refinement.
-/
theorem grid_monotone (r Q : ℕ) (hQ : 1 ≤ Q) : lamQ r Q ≤ lamQ r (Q + 1) := by
  by_cases hr : r ≥ 2;
  · refine' csSup_le _ _;
    · refine' ⟨ _, ⟨ fun _ => 0, _, rfl ⟩ ⟩;
      constructor <;> norm_num;
      exact ⟨ fun _ _ _ => by positivity, fun _ => by positivity ⟩;
    · rintro _ ⟨ z, hz, rfl ⟩ ; obtain ⟨ z', hz', hz'' ⟩ := packing_refinement r Q z hz; exact hz''.symm ▸ le_csSup ( packing_values_bddAbove r ( Q + 1 ) hr ) ⟨ z', hz', rfl ⟩ ;
  · interval_cases r <;> norm_num [ lamQ ];
    · unfold IsPacking valQ;
      unfold admTypes; norm_num [ types ] ;
      unfold admissible; norm_num [ Finset.filter_singleton ] ;
      rw [ csSup_of_not_bddAbove ];
      · norm_num;
        apply_rules [ Real.sSup_nonneg ] ; aesop;
      · norm_num [ bddAbove_def ];
        exact fun x => ⟨ fun _ => Max.max x 1 + 1, fun _ => by positivity, by norm_num; linarith [ le_max_left x 1, le_max_right x 1 ] ⟩;
    · rw [ csSup_of_not_bddAbove ];
      · exact le_trans ( by norm_num ) ( show 0 ≤ sSup { v | ∃ z : ( Fin ( NQ ( Q + 1 ) ) → ℕ ) → ℝ, IsPacking 1 ( Q + 1 ) z ∧ valQ 1 ( Q + 1 ) z = v } from by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ z, hz, rfl ⟩ ; exact Finset.sum_nonneg fun _ _ => hz.1 _ );
      · norm_num [ bddAbove_def ];
        intro x;
        refine' ⟨ fun _ => Max.max x 1 + 1, _, _ ⟩ <;> norm_num [ IsPacking, valQ ];
        · refine' ⟨ by positivity, _, _ ⟩ <;> norm_num [ admTypes ];
          · intro i j hij; rw [ Finset.sum_eq_zero ] <;> norm_num;
            · positivity;
            · intro t ht ht'; have := Finset.mem_filter.mp ht; simp_all +decide [ types ] ;
              contrapose! this; simp_all +decide [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ] ;
              exact fun h => by linarith [ h i, h j, Nat.pos_of_ne_zero this.1.1, Nat.pos_of_ne_zero this.1.2, Finset.single_le_sum ( fun a _ => Nat.zero_le ( t a ) ) ( Finset.mem_sdiff.mpr ⟨ Finset.mem_univ j, by aesop ⟩ : j ∈ Finset.univ \ { i } ) ] ;
          · intro i; rw [ Finset.sum_eq_zero ] <;> norm_num;
            · positivity;
            · intro t ht ht'; have := Finset.mem_filter.mp ht; simp_all +decide [ types ] ;
              exact Or.inl ( Nat.choose_eq_zero_of_lt ( this.1 i ) );
        · rcases k : Finset.card ( admTypes 1 Q ) with ( _ | _ | k ) <;> simp_all +decide;
          · unfold admTypes at k;
            unfold types at k; simp_all +decide [ Finset.ext_iff ] ;
            contrapose! k;
            refine' ⟨ fun i => if i = ⟨ 0, by
              exact Nat.mul_pos hQ ( pow_pos ( by decide ) _ ) ⟩ then 1 else 0, _, _, _ ⟩ <;> simp +decide [ admissible ]
            generalize_proofs at *;
            · exact fun a => by split_ifs <;> norm_num;
            · exact one_le_pow₀ ( by norm_num );
          · linarith [ le_max_left x 1, le_max_right x 1 ];
          · nlinarith [ le_max_left x 1, le_max_right x 1 ]

/--
Canonical limit formula: `λ_{r,Q} → Λ_r`.
-/
theorem canonical_limit (r : ℕ) (hr : 3 ≤ r) :
    Tendsto (fun Q => lamQ r Q) atTop (nhds (Lam r)) := by
  refine' tendsto_atTop_isLUB _ _ |> Filter.Tendsto.congr' _;
  rotate_left;
  use fun Q => if Q = 0 then 0 else lamQ r Q;
  · intro Q₁ Q₂ hQ; rcases Q₁ with ( _ | Q₁ ) <;> rcases Q₂ with ( _ | Q₂ ) <;> norm_num at *;
    · exact lamQ_nonneg _ _;
    · induction hQ <;> simp_all +decide [ Nat.succ_eq_add_one  ];
      exact le_trans ‹_› ( grid_monotone _ _ ( Nat.succ_pos _ ) );
  · constructor;
    · rintro _ ⟨ Q, rfl ⟩ ; by_cases hQ : Q = 0 <;> simp +decide [ hQ ] ;
      · exact le_trans ( lamQ_nonneg r 1 ) ( lamQ_le_Lam r 1 hr ( by norm_num ) );
      · exact lamQ_le_Lam r Q hr ( Nat.pos_of_ne_zero hQ );
    · intro x hx;
      refine' csSup_le _ _ <;> norm_num;
      · exact ⟨ _, ⟨ 1, by norm_num, rfl ⟩ ⟩;
      · exact fun Q hQ => hx ⟨ Q, by aesop ⟩;
  · filter_upwards [ Filter.eventually_ne_atTop 0 ] with Q hQ using if_neg hQ

/--
Near-optimal finite packing.
-/
theorem near_optimal_grid (r : ℕ) (hr : 3 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : ℕ) (z : (Fin (NQ Q) → ℕ) → ℝ), 1 ≤ Q ∧ IsPacking r Q z ∧
      Lam r - ε < valQ r Q z := by
  -- By the canonical limit theorem, there exists a Q such that lamQ r Q > Lam r - ε/2.
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, 1 ≤ Q ∧ lamQ r Q > Lam r - ε / 2 := by
    have := canonical_limit r hr;
    exact Filter.eventually_atTop.mp ( this.eventually ( lt_mem_nhds ( by linarith ) ) ) |> fun ⟨ Q, hQ ⟩ ↦ ⟨ Q + 1, by linarith, hQ _ ( by linarith ) ⟩;
  -- By the definition of `lamQ`, there exists a packing `z` such that `valQ r Q z > lamQ r Q - ε / 2`.
  obtain ⟨z, hz⟩ : ∃ z : (Fin (NQ Q) → ℕ) → ℝ, IsPacking r Q z ∧ valQ r Q z > lamQ r Q - ε / 2 := by
    contrapose! hQ;
    intro hQ';
    refine' csSup_le _ _ <;> norm_num;
    · refine' ⟨ _, ⟨ fun _ => 0, _, rfl ⟩ ⟩ ; norm_num [ IsPacking ];
      exact ⟨ fun _ _ _ => by positivity, fun _ => by positivity ⟩;
    · exact fun z hz => le_trans ( hQ z hz ) ( sub_le_sub_right ( lamQ_le_Lam r Q hr hQ' ) _ );
  exact ⟨ Q, z, hQ.1, hz.1, by linarith ⟩

/-! ## Explicit packings, pair covers, and the limit `Λ_r → e²` -/

/-- `L = (r!)^{-1/r}`. -/
noncomputable def facL (r : ℕ) : ℝ := (Nat.factorial r : ℝ) ^ (-(1 / (r:ℝ)))

lemma facL_pos (r : ℕ) : 0 < facL r := by unfold facL; positivity

/-- The dyadic bins fully contained in the `j`-th block `(jL, (j+1)L]`. -/
noncomputable def facBlock (r Q : ℕ) (j : Fin r) : Finset (Fin (NQ Q)) :=
  Finset.univ.filter (fun i =>
    (j:ℝ) * facL r ≤ (i:ℝ) * dQ Q ∧ ((i:ℝ)+1) * dQ Q ≤ ((j:ℝ)+1) * facL r)

/-- The selection type associated with a one-bin-per-block choice `s`. -/
noncomputable def facTypeOf (r Q : ℕ) (s : Fin r → Fin (NQ Q)) : Fin (NQ Q) → ℕ :=
  fun i => (Finset.univ.filter (fun k => s k = i)).card

/-- The minimal block length `ℓ_Q = min_j b_{Q,j} d_Q`. -/
noncomputable def facEll (r Q : ℕ) : ℝ :=
  if h : (Finset.univ : Finset (Fin r)).Nonempty then
    (Finset.univ).inf' h (fun j => ((facBlock r Q j).card : ℝ) * dQ Q) else 0

/-- The common weight `facC = r² ℓ_Q² / ∏_j b_{Q,j}`. -/
noncomputable def facC (r Q : ℕ) : ℝ :=
  (r:ℝ)^2 * facEll r Q ^ 2 / ∏ j : Fin r, ((facBlock r Q j).card : ℝ)

/-- The factorial packing weighting: every selection type gets weight `facC`. -/
noncomputable def facWeight (r Q : ℕ) (t : Fin (NQ Q) → ℕ) : ℝ :=
  ((Fintype.piFinset (fun j => facBlock r Q j)).filter (fun s => facTypeOf r Q s = t)).card
    * facC r Q

/-- Fiberwise reduction: a moment of `facWeight` against `g` over the admissible
types equals `facC` times the sum of `g ∘ facTypeOf` over all selections
(provided every selection type is admissible). -/
lemma facWeight_moment (r Q : ℕ) (g : (Fin (NQ Q) → ℕ) → ℝ)
    (himg : ∀ s ∈ Fintype.piFinset (fun j => facBlock r Q j), facTypeOf r Q s ∈ admTypes r Q) :
    ∑ t ∈ admTypes r Q, g t * facWeight r Q t
      = facC r Q * ∑ s ∈ Fintype.piFinset (fun j => facBlock r Q j), g (facTypeOf r Q s) := by
  have key : ∑ t ∈ admTypes r Q, g t * ((((Fintype.piFinset (fun j => facBlock r Q j)).filter (fun s => facTypeOf r Q s = t)).card : ℝ))
      = ∑ s ∈ Fintype.piFinset (fun j => facBlock r Q j), g (facTypeOf r Q s) := by
    rw [← Finset.sum_fiberwise_of_maps_to himg (fun s => g (facTypeOf r Q s))]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2])]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc ∑ t ∈ admTypes r Q, g t * facWeight r Q t
      = facC r Q * ∑ t ∈ admTypes r Q, g t * ((((Fintype.piFinset (fun j => facBlock r Q j)).filter (fun s => facTypeOf r Q s = t)).card : ℝ)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun t _ => by unfold facWeight; ring)
    _ = facC r Q * ∑ s ∈ Fintype.piFinset (fun j => facBlock r Q j), g (facTypeOf r Q s) := by rw [key]

/-- `facWeight` is nonnegative. -/
lemma facWeight_nonneg (r Q : ℕ) (t : Fin (NQ Q) → ℕ) : 0 ≤ facWeight r Q t := by
  unfold facWeight
  apply mul_nonneg
  · exact Nat.cast_nonneg _
  · unfold facC
    apply div_nonneg
    · apply mul_nonneg <;> positivity
    · exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _

/-- Distinct blocks contain disjoint bins. -/
lemma facBlock_disjoint (r Q : ℕ) {j j' : Fin r} (hjj' : j ≠ j') :
    Disjoint (facBlock r Q j) (facBlock r Q j') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [facBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
  -- hi : (j : ℝ) * facL r ≤ i * dQ Q ∧ (i + 1) * dQ Q ≤ (j + 1) * facL r
  -- hi' : (j' : ℝ) * facL r ≤ i * dQ Q ∧ (i + 1) * dQ Q ≤ (j' + 1) * facL r
  rcases hjj' with hjj'
  -- We need to derive a contradiction
  rcases Nat.lt_or_gt_of_ne (Fin.val_injective.ne hjj') with hlt | hgt
  · -- j < j' case
    have hij : (j.val + 1 : ℕ) ≤ j'.val := Nat.succ_le_of_lt hlt
    have hfacLpos : 0 < facL r := facL_pos r
    have hdQpos : 0 < dQ Q := by unfold dQ; positivity
    obtain ⟨hj1, hj2⟩ := hi
    obtain ⟨hj'1, hj'2⟩ := hi'
    -- j * L ≤ i * dQ and (i+1) * dQ ≤ (j+1) * L
    -- j' * L ≤ i * dQ and (i+1) * dQ ≤ (j'+1) * L
    -- Since j + 1 ≤ j', (j+1) * L ≤ j' * L
    have h1 : ((j.val : ℝ) + 1) * facL r ≤ j'.val * facL r := by
      gcongr
      exact_mod_cast hij
    linarith
  · -- j > j' case
    have hij : (j'.val + 1 : ℕ) ≤ j.val := Nat.succ_le_of_lt hgt
    have hfacLpos : 0 < facL r := facL_pos r
    have hdQpos : 0 < dQ Q := by unfold dQ; positivity
    obtain ⟨hj1, hj2⟩ := hi
    obtain ⟨hj'1, hj'2⟩ := hi'
    -- j' * L ≤ i * dQ and (i+1) * dQ ≤ (j'+1) * L
    -- j * L ≤ i * dQ and (i+1) * dQ ≤ (j+1) * L
    -- Since j' + 1 ≤ j, (j'+1) * L ≤ j * L
    have h1 : ((j'.val : ℝ) + 1) * facL r ≤ j.val * facL r := by
      gcongr
      exact_mod_cast hij
    linarith

/-- A selection type has total multiplicity `r`. -/
lemma facTypeOf_sum (r Q : ℕ) (s : Fin r → Fin (NQ Q)) :
    ∑ i, facTypeOf r Q s i = r := by
  unfold facTypeOf
  have : (Fintype.card (Fin r)) = ∑ i : Fin (NQ Q), Fintype.card {k : Fin r // s k = i} := by
    rw [Fintype.card_eq_sum_ones]
    rw [show (∑ _a : Fin r, (1 : ℕ)) = ∑ x : Σ i : Fin (NQ Q), { k : Fin r // s k = i }, 1 from
        (Equiv.sum_comp (Equiv.sigmaFiberEquiv s) (fun x => 1)).symm]
    rw [← Fintype.card_eq_sum_ones]
    rw [Fintype.card_sigma]
  have h2 : ∀ i, (Finset.univ.filter (fun k => s k = i)).card = Fintype.card {k : Fin r // s k = i} := by
    intro i
    exact (Fintype.card_ofFinset _ _).symm
  simp_all

/-- A selection type has multiplicity at most one in each bin. -/
lemma facTypeOf_le_one (r Q : ℕ) (s : Fin r → Fin (NQ Q))
    (hs : s ∈ Fintype.piFinset (fun j => facBlock r Q j)) (i : Fin (NQ Q)) :
    facTypeOf r Q s i ≤ 1 := by
  unfold facTypeOf
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hai : s a = i := ha
  have hbi : s b = i := hb
  have hamem : s a ∈ facBlock r Q a := Fintype.mem_piFinset.mp hs a
  have hbmem : s b ∈ facBlock r Q b := Fintype.mem_piFinset.mp hs b
  by_contra hne
  have hdisj := facBlock_disjoint r Q hne
  rw [Finset.disjoint_left] at hdisj
  exact hdisj (hai ▸ hamem) (hbi ▸ hbmem)

/-- Reindexing: the product `∏_j f(j)^{multiplicity}` over bins equals the
product `∏_k f(s k)` over the chosen selection. -/
lemma reindex_prod (r Q : ℕ) (s : Fin r → Fin (NQ Q)) (f : Fin (NQ Q) → ℕ) :
    ∏ j : Fin (NQ Q), (f j) ^ (facTypeOf r Q s j) = ∏ k : Fin r, f (s k) := by
  unfold facTypeOf
  rw [Finset.prod_comp f s]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro j _ hj
  rw [Finset.mem_image] at hj
  have : (Finset.univ.filter (fun a => s a = j)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a _ ha
    exact hj ⟨a, Finset.mem_univ a, ha⟩
  rw [this, pow_zero]

/-- Every selection type is admissible. -/
lemma facTypeOf_mem_admTypes (r Q : ℕ) (hr : 3 ≤ r)
    (s : Fin r → Fin (NQ Q)) (hs : s ∈ Fintype.piFinset (fun j => facBlock r Q j)) :
    facTypeOf r Q s ∈ admTypes r Q := by
  have hrpos : 0 < r := by omega
  have hrne : (r:ℝ) ≠ 0 := by positivity
  have hLpos : 0 < facL r := facL_pos r
  rw [admTypes, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [types, Finset.mem_filter]
    refine ⟨?_, facTypeOf_sum r Q s⟩
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    have : facTypeOf r Q s j ≤ r := by
      unfold facTypeOf
      calc (Finset.univ.filter (fun k => s k = j)).card ≤ (Finset.univ : Finset (Fin r)).card :=
            Finset.card_filter_le _ _
        _ = r := by simp
    omega
  · rw [admissible, reindex_prod r Q s (fun j => (j:ℕ)+1)]
    have hmem : ∀ k, s k ∈ facBlock r Q k := fun k => Fintype.mem_piFinset.mp hs k
    have hkbound : ∀ k : Fin r, ((s k : ℕ) + 1 : ℝ) ≤ ((k:ℝ)+1) * facL r * 2^Q := by
      intro k
      have hk := hmem k
      simp only [facBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have h2Q : (0:ℝ) < 2^Q := by positivity
      have hdd : dQ Q * 2^Q = 1 := by unfold dQ; field_simp
      have key := mul_le_mul_of_nonneg_right hk.2 h2Q.le
      rw [mul_assoc, hdd, mul_one] at key
      exact key
    have hfact : (∏ k : Fin r, ((k:ℝ)+1)) = (Nat.factorial r : ℝ) := by
      rw [Fin.prod_univ_eq_prod_range (fun k => ((k:ℝ)+1)) r]
      rw [show (∏ i ∈ Finset.range r, ((i:ℝ)+1)) = ((∏ i ∈ Finset.range r, (i+1) : ℕ):ℝ) by push_cast; rfl]
      rw [Finset.prod_range_add_one_eq_factorial]
    have hLr : (Nat.factorial r : ℝ) * (facL r)^r = 1 := by
      unfold facL
      rw [← Real.rpow_natCast ((Nat.factorial r : ℝ) ^ (-(1/(r:ℝ)))) r, ← Real.rpow_mul (by positivity)]
      rw [show (-(1/(r:ℝ)))*(r:ℝ) = -1 by field_simp]
      rw [Real.rpow_neg_one]
      field_simp
    have hprod_real : (∏ k : Fin r, ((s k : ℕ) + 1 : ℝ)) ≤ ∏ k : Fin r, (((k:ℝ)+1) * facL r * 2^Q) := by
      apply Finset.prod_le_prod
      · intro k _; positivity
      · intro k _; exact hkbound k
    have hRHS : (∏ k : Fin r, (((k:ℝ)+1) * facL r * 2^Q)) = 2^(Q*r) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
      simp only [Finset.card_univ, Fintype.card_fin]
      rw [hfact, ← pow_mul, hLr, one_mul]
    rw [hRHS] at hprod_real
    exact_mod_cast hprod_real

/-- The number of selections is `∏_j b_{Q,j}`. -/
lemma facPiFinset_card (r Q : ℕ) :
    (Fintype.piFinset (fun j => facBlock r Q j)).card = ∏ j : Fin r, (facBlock r Q j).card := by
  exact Fintype.card_piFinset _

/-- Each block contains at least `L/d_Q - 2` bins: `b_{Q,j} d_Q ≥ L - 2 d_Q`.
The block interval `(jL, (j+1)L]` has length `L`, so it fully contains all bins
`(i d_Q, (i+1) d_Q]` with index `i` in a real interval of length `L/d_Q - 1`,
which contains at least `L/d_Q - 2` integers; and these all lie in the grid
`Fin (NQ Q)` since `(j+1)L ≤ rL < r ≤ Q` (using `hQ`). -/
lemma facBlock_card_ge (r Q : ℕ) (hr : 3 ≤ r) (hQ : r ≤ Q) (hd : 2 * dQ Q < facL r)
    (j : Fin r) :
    facL r - 2 * dQ Q ≤ ((facBlock r Q j).card : ℝ) * dQ Q := by
  have hdQpos : 0 < dQ Q := by unfold dQ; positivity
  have hfacLpos : 0 < facL r := facL_pos r
  -- Define m = ⌈j * L / dQ⌉, the smallest index in facBlock
  set m : ℕ := Nat.ceil ((j : ℝ) * facL r / dQ Q) with hm_def
  -- Define n = ⌈(L - 2*dQ) / dQ⌉, a lower bound on the cardinality
  set n : ℕ := Nat.ceil ((facL r - 2 * dQ Q) / dQ Q) with hn_def
  have hn_nonneg : 0 ≤ n := Nat.zero_le _
  -- Key: we'll show that indices m, m+1, ..., m+n-1 (if they exist in Fin (NQ Q)) are in facBlock
  -- But we need to be careful about bounds. Let's instead directly show the card bound.
  -- The valid range is [m, M] where M = ⌊((j+1)*L - dQ)/dQ⌋
  -- Card = max(0, M - m + 1) ≥ ⌈(L - 2*dQ)/dQ⌉ = n (by careful analysis)
  -- Actually, let's just show card ≥ n directly by finding n elements
  have h_card_ge_n : n ≤ (facBlock r Q j).card := by
    -- We'll construct an injection from Fin n to facBlock r Q j
    -- The k-th element is ⟨m + k, _⟩
    -- First, show m + n ≤ NQ Q (all indices are valid)
    have hrpos : 0 < r := by linarith
    haveI : NeZero r := ⟨hrpos.ne'⟩
    have hm_le : (m : ℝ) ≤ (j : ℝ) * facL r / dQ Q + 1 := by
      by_cases hj : j = (0 : Fin r)
      · simp_all [Nat.ceil_zero]
      · have hpos : 0 < (j : ℝ) * facL r / dQ Q := mul_pos (Nat.cast_pos.mpr (Fin.pos_iff_ne_zero.mpr hj)) hfacLpos |> div_pos <| hdQpos
        linarith [Nat.ceil_lt_add_one (le_of_lt hpos)]
    have hn_le : (n : ℝ) ≤ (facL r - 2 * dQ Q) / dQ Q + 1 := by
      have hnn : 0 < (facL r - 2 * dQ Q) / dQ Q := by
        apply div_pos
        · linarith
        · exact hdQpos
      linarith [Nat.ceil_lt_add_one (le_of_lt hnn)]
    -- Now show m + n ≤ NQ Q
    have hmn_le : (m + n : ℝ) ≤ ((j : ℝ) + 1) * facL r / dQ Q := by
      have h1 : (m + n : ℝ) ≤ (j : ℝ) * facL r / dQ Q + 1 + ((facL r - 2 * dQ Q) / dQ Q + 1) := by linarith
      have h2 : (j : ℝ) * facL r / dQ Q + 1 + ((facL r - 2 * dQ Q) / dQ Q + 1) = ((j : ℝ) + 1) * facL r / dQ Q := by field_simp; ring
      linarith
    -- We have (j+1) * L ≤ r * L ≤ r (since L ≤ 1 for r! ≥ 1)
    -- And r / dQ Q = r * 2^Q ≤ Q * 2^Q = NQ Q
    have hL_le_one : facL r ≤ 1 := by
      unfold facL
      have h1 : (1 : ℝ) ≤ (Nat.factorial r : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)
      have h2 : -(1 / (r:ℝ)) ≤ 0 := by linarith [one_div_pos.mpr (show (0:ℝ) < r by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos h1 h2
    have hmn_le_Q : (m + n : ℝ) ≤ (r : ℝ) / dQ Q := by
      have h_step : ((j : ℝ) + 1) * facL r ≤ (r : ℝ) := by
        have hj_bound : (j : ℕ) + 1 ≤ r := Nat.succ_le_of_lt j.is_lt
        have h1 : ((j : ℝ) + 1) * facL r ≤ (r : ℝ) * facL r := by
          gcongr
          exact_mod_cast hj_bound
        have h2 : (r : ℝ) * facL r ≤ (r : ℝ) := by
          exact mul_le_of_le_one_right (by positivity : 0 ≤ (r : ℝ)) hL_le_one
        linarith
      calc (m + n : ℝ) ≤ ((j : ℝ) + 1) * facL r / dQ Q := hmn_le
        _ ≤ (r : ℝ) / dQ Q := by gcongr
    have hr_le_Q : (r : ℝ) ≤ Q := by exact_mod_cast hQ
    have hdQ_le : (1 : ℝ) / dQ Q = 2 ^ Q := by unfold dQ; norm_num
    have hmn_le_NQ : (m + n : ℝ) ≤ (NQ Q : ℝ) := by
      calc (m + n : ℝ) ≤ (r : ℝ) / dQ Q := hmn_le_Q
        _ = (r : ℝ) * (1 / dQ Q) := by ring
        _ = (r : ℝ) * (2 : ℝ) ^ Q := by rw [hdQ_le]
        _ ≤ (Q : ℝ) * (2 : ℝ) ^ Q := by gcongr
        _ = (NQ Q : ℝ) := by unfold NQ; push_cast; ring
    -- Construct injection from Fin n to facBlock r Q j
    -- Map k : Fin n to ⟨m + k, _⟩
    have hmn_bound : ∀ k : Fin n, m + k.val < NQ Q := by
      intro k
      have h1 : (m + k.val : ℝ) < m + n := by norm_cast; exact Nat.add_lt_add_left k.is_lt m
      have h2 : (m + n : ℝ) ≤ (NQ Q : ℝ) := hmn_le_NQ
      exact_mod_cast (h1.trans_le h2)
    -- Now show each element is in facBlock
    have hin_facBlock : ∀ k : Fin n, (⟨m + k.val, hmn_bound k⟩ : Fin (NQ Q)) ∈ facBlock r Q j := by
      intro k
      simp only [facBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      -- Need: j * L ≤ (m + k) * dQ and (m + k + 1) * dQ ≤ (j + 1) * L
      have hk_bound : (k.val : ℝ) < n := by exact_mod_cast k.is_lt
      -- First condition: j * L ≤ (m + k) * dQ
      -- Since m ≥ j * L / dQ, we have m * dQ ≥ j * L
      have h1 : (j : ℝ) * facL r ≤ (m : ℝ) * dQ Q := by
        have := Nat.le_ceil ((j : ℝ) * facL r / dQ Q)
        calc (j : ℝ) * facL r = ((j : ℝ) * facL r / dQ Q) * dQ Q := by field_simp
          _ ≤ (m : ℝ) * dQ Q := by gcongr
      have h2 : (j : ℝ) * facL r ≤ ((m : ℝ) + k.val) * dQ Q := by
        have : (m : ℝ) * dQ Q ≤ ((m : ℝ) + k.val) * dQ Q := by nlinarith
        linarith
      -- Second condition: (m + k + 1) * dQ ≤ (j + 1) * L
      have h3 : ((m : ℝ) + k.val + 1) * dQ Q ≤ ((j : ℝ) + 1) * facL r := by
        have hmnk : (m : ℝ) + k.val + 1 ≤ m + n := by
          norm_cast
          linarith [k.is_lt]
        calc ((m : ℝ) + k.val + 1) * dQ Q ≤ (m + n : ℝ) * dQ Q := by gcongr
          _ ≤ ((j : ℝ) + 1) * facL r / dQ Q * dQ Q := by gcongr
          _ = ((j : ℝ) + 1) * facL r := by field_simp
      simp +decide [h2, h3]
    -- Use injection to show n ≤ card
    -- Define an injection f : Fin n → facBlock r Q j by f k = ⟨m + k, _⟩
    let f : Fin n → { x // x ∈ facBlock r Q j } := fun k => ⟨⟨m + k.val, hmn_bound k⟩, hin_facBlock k⟩
    have hf_inj : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      have h : (⟨m + a.val, hmn_bound a⟩ : Fin (NQ Q)) = ⟨m + b.val, hmn_bound b⟩ := by
        exact Subtype.ext_iff.mp hab
      simp only [Fin.ext_iff] at h
      omega
    have := Fintype.card_le_of_injective f hf_inj
    rw [Fintype.card_fin] at this
    convert this using 1
    exact (Fintype.card_coe _).symm
  have h_card_bound : (n : ℝ) * dQ Q ≥ facL r - 2 * dQ Q := by
    have := Nat.le_ceil ((facL r - 2 * dQ Q) / dQ Q)
    calc (facL r - 2 * dQ Q : ℝ) = ((facL r - 2 * dQ Q) / dQ Q) * dQ Q := by field_simp
      _ ≤ (n : ℝ) * dQ Q := by gcongr
  calc facL r - 2 * dQ Q ≤ (n : ℝ) * dQ Q := h_card_bound
    _ ≤ ((facBlock r Q j).card : ℝ) * dQ Q := by gcongr

/-- Every block is nonempty when `2 d_Q < L`. -/
lemma facBlock_card_pos (r Q : ℕ) (hr : 3 ≤ r) (hQ : r ≤ Q) (hd : 2 * dQ Q < facL r) (j : Fin r) :
    0 < (facBlock r Q j).card := by
  have hdQpos : 0 < dQ Q := by unfold dQ; positivity
  have h := facBlock_card_ge r Q hr hQ hd j
  have hpos : 0 < ((facBlock r Q j).card : ℝ) * dQ Q := by linarith [hd]
  have hcard : 0 < ((facBlock r Q j).card : ℝ) := by
    by_contra h'
    push_neg at h'
    nlinarith [hpos, hdQpos, h', Nat.cast_nonneg (α := ℝ) (facBlock r Q j).card]
  exact_mod_cast hcard

/-- `ℓ_Q` is a lower bound for each block length. -/
lemma facEll_le_block (r Q : ℕ) (j : Fin r) :
    facEll r Q ≤ ((facBlock r Q j).card : ℝ) * dQ Q := by
  unfold facEll
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j, Finset.mem_univ j⟩
  simp only [dif_pos hne]
  exact Finset.inf'_le _ (Finset.mem_univ j)

/-- `ℓ_Q ≥ L - 2 d_Q`. -/
lemma facEll_lower (r Q : ℕ) (hr : 3 ≤ r) (hQ : r ≤ Q) (hd : 2 * dQ Q < facL r) :
    facL r - 2 * dQ Q ≤ facEll r Q := by
  unfold facEll
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, by linarith⟩, Finset.mem_univ _⟩
  simp only [dif_pos hne]
  apply Finset.le_inf' hne
  intro j _
  exact facBlock_card_ge r Q hr hQ hd j

/-- For a fixed index `i`, at most one block contains it (blocks are disjoint),
so the sum of block-membership indicators over blocks is at most one. -/
lemma facBlock_indicator_sum_le_one (r Q : ℕ) (i : Fin (NQ Q)) :
    ∑ k : Fin r, (if i ∈ facBlock r Q k then (1:ℝ) else 0) ≤ 1 := by
  have hcard : (Finset.univ.filter (fun k : Fin r => i ∈ facBlock r Q k)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hne
    exact (Finset.disjoint_left.mp (facBlock_disjoint r Q hne)) ha hb
  calc ∑ k : Fin r, (if i ∈ facBlock r Q k then (1:ℝ) else 0)
      = ((Finset.univ.filter (fun k : Fin r => i ∈ facBlock r Q k)).card : ℝ) := by
        rw [Finset.card_filter]; push_cast; rfl
    _ ≤ 1 := by exact_mod_cast hcard

/-- The common weight times the product of the remaining block cardinalities is
at most `r² d_Q²`.  Indeed it equals `r² ℓ_Q² / (b_k b_{k'})`, and
`ℓ_Q ≤ b_k d_Q`, `ℓ_Q ≤ b_{k'} d_Q`. -/
lemma facC_prod_erase_le (r Q : ℕ) (hr : 3 ≤ r) (hQ : r ≤ Q) (hd : 2 * dQ Q < facL r)
    (k k' : Fin r) (hkk' : k ≠ k') :
    0 ≤ facC r Q * ∏ m ∈ (Finset.univ.erase k).erase k', ((facBlock r Q m).card : ℝ) ∧
    facC r Q * ∏ m ∈ (Finset.univ.erase k).erase k', ((facBlock r Q m).card : ℝ)
      ≤ (r:ℝ)^2 * dQ Q ^ 2 := by
  have hdpos : 0 < dQ Q := by unfold dQ; positivity
  have hb : ∀ m, 0 < ((facBlock r Q m).card : ℝ) := fun m => by
    exact_mod_cast facBlock_card_pos r Q hr hQ hd m
  set E := ∏ m ∈ (Finset.univ.erase k).erase k', ((facBlock r Q m).card : ℝ) with hE
  have hEpos : 0 < E := Finset.prod_pos (fun m _ => hb m)
  have hsplit : (∏ j : Fin r, ((facBlock r Q j).card : ℝ))
      = ((facBlock r Q k).card : ℝ) * ((facBlock r Q k').card : ℝ) * E := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    rw [← Finset.mul_prod_erase (Finset.univ.erase k) _ (Finset.mem_erase.mpr ⟨hkk'.symm, Finset.mem_univ k'⟩)]
    rw [hE]; ring
  have hellpos : 0 < facEll r Q := lt_of_lt_of_le (by linarith [hd]) (facEll_lower r Q hr hQ hd)
  have hellk : facEll r Q ≤ ((facBlock r Q k).card : ℝ) * dQ Q := facEll_le_block r Q k
  have hellk' : facEll r Q ≤ ((facBlock r Q k').card : ℝ) * dQ Q := facEll_le_block r Q k'
  have hval : facC r Q * E = (r:ℝ)^2 * facEll r Q ^ 2 / (((facBlock r Q k).card : ℝ) * ((facBlock r Q k').card : ℝ)) := by
    unfold facC
    rw [hsplit]
    field_simp
  constructor
  · rw [hval]; positivity
  · rw [hval]
    rw [div_le_iff₀ (mul_pos (hb k) (hb k'))]
    have hsq : facEll r Q ^ 2 ≤ (((facBlock r Q k).card : ℝ) * dQ Q) * (((facBlock r Q k').card : ℝ) * dQ Q) := by
      have := mul_le_mul hellk hellk' hellpos.le (mul_nonneg (Nat.cast_nonneg _) hdpos.le)
      nlinarith [hellpos, this]
    nlinarith [hsq, sq_nonneg (dQ Q), hb k, hb k']

/-- The two-coordinate count over selections: for `k ≠ k'`, the number of
selections with `s k = i` and `s k' = j` is `[i ∈ B_k] · [j ∈ B_{k'}] ·
∏_{m ≠ k, k'} b_m`. -/
lemma facPair_coord_count (r Q : ℕ) (i j : Fin (NQ Q)) (k k' : Fin r) (hkk' : k ≠ k') :
    (∑ s ∈ Fintype.piFinset (fun m => facBlock r Q m),
        ((if s k = i then (1:ℝ) else 0) * (if s k' = j then 1 else 0)))
      = (if i ∈ facBlock r Q k then (1:ℝ) else 0) * (if j ∈ facBlock r Q k' then 1 else 0)
        * ∏ m ∈ (Finset.univ.erase k).erase k', ((facBlock r Q m).card : ℝ) := by
  set f : Fin r → Fin (NQ Q) → ℝ := fun m x =>
    if m = k then (if x = i then (1:ℝ) else 0)
    else if m = k' then (if x = j then (1:ℝ) else 0) else 1 with hf
  have hsummand : ∀ s : Fin r → Fin (NQ Q),
      (if s k = i then (1:ℝ) else 0) * (if s k' = j then 1 else 0) = ∏ m : Fin r, f m (s m) := by
    intro s
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ k)]
    rw [Finset.prod_eq_mul_prod_diff_singleton (show k' ∈ Finset.univ \ {k} by
      simp [Finset.mem_sdiff, hkk'.symm])]
    have hrest : ∏ m ∈ (Finset.univ \ {k}) \ {k'}, f m (s m) = 1 := by
      apply Finset.prod_eq_one
      intro m hm
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hm
      rw [hf]; simp only []; rw [if_neg hm.1.2, if_neg hm.2]
    rw [hrest, mul_one]
    simp [hf, hkk'.symm]
  rw [Finset.sum_congr rfl (fun s _ => hsummand s)]
  rw [← Finset.prod_univ_sum]
  have hg : ∀ m : Fin r, (∑ x ∈ facBlock r Q m, f m x)
      = if m = k then (if i ∈ facBlock r Q k then (1:ℝ) else 0)
        else if m = k' then (if j ∈ facBlock r Q k' then (1:ℝ) else 0)
        else ((facBlock r Q m).card : ℝ) := by
    intro m
    rw [hf]; simp only []
    rw [Finset.sum_ite_irrel, Finset.sum_ite_irrel]
    by_cases hmk : m = k
    · subst hmk
      rw [if_pos rfl, if_pos rfl, Finset.sum_ite_eq']
    · rw [if_neg hmk, if_neg hmk]
      by_cases hmk' : m = k'
      · subst hmk'
        rw [if_pos rfl, if_pos rfl, Finset.sum_ite_eq']
      · rw [if_neg hmk', if_neg hmk', Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.prod_congr rfl (fun m _ => hg m)]
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ k)]
  rw [Finset.prod_eq_mul_prod_diff_singleton (show k' ∈ Finset.univ \ {k} by
    simp [Finset.mem_sdiff, hkk'.symm])]
  have hrest2 : ∏ m ∈ (Finset.univ \ {k}) \ {k'},
      (if m = k then (if i ∈ facBlock r Q k then (1:ℝ) else 0)
       else if m = k' then (if j ∈ facBlock r Q k' then (1:ℝ) else 0)
       else ((facBlock r Q m).card : ℝ))
      = ∏ m ∈ (Finset.univ.erase k).erase k', ((facBlock r Q m).card : ℝ) := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_singleton_eq_erase]
    apply Finset.prod_congr rfl
    intro m hm
    simp only [Finset.mem_erase] at hm
    rw [if_neg hm.2.1, if_neg hm.1]
  rw [hrest2, if_pos rfl, if_neg hkk'.symm, if_pos rfl]
  ring

/-- The diagonal two-coordinate count vanishes when `i ≠ j`. -/
lemma facPair_coord_diag (r Q : ℕ) (i j : Fin (NQ Q)) (hij : i ≠ j) (k : Fin r) :
    (∑ s ∈ Fintype.piFinset (fun m => facBlock r Q m),
        ((if s k = i then (1:ℝ) else 0) * (if s k = j then 1 else 0))) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  by_cases h1 : s k = i
  · by_cases h2 : s k = j
    · exact absurd (h1 ▸ h2 : i = j) hij
    · simp [h2]
  · simp [h1]

/-- The off-diagonal pair load is at most `r² d_Q²`. -/
lemma facOffDiag_bound (r Q : ℕ) (hr : 3 ≤ r) (hQ : r ≤ Q) (hd : 2 * dQ Q < facL r)
    (i j : Fin (NQ Q)) (hij : i ≠ j) :
    facC r Q * (∑ s ∈ Fintype.piFinset (fun j => facBlock r Q j),
        ((facTypeOf r Q s i : ℝ) * (facTypeOf r Q s j : ℝ))) ≤ (r:ℝ)^2 * dQ Q ^ 2 := by
  set P := Fintype.piFinset (fun m => facBlock r Q m) with hP
  set indi : Fin r → ℝ := fun k => (if i ∈ facBlock r Q k then (1:ℝ) else 0) with hindi
  set indj : Fin r → ℝ := fun k => (if j ∈ facBlock r Q k then (1:ℝ) else 0) with hindj
  have hRnn : (0:ℝ) ≤ (r:ℝ)^2 * dQ Q ^ 2 := by positivity
  have hindi_nn : ∀ k, 0 ≤ indi k := fun k => by rw [hindi]; dsimp only; split <;> norm_num
  have hindj_nn : ∀ k, 0 ≤ indj k := fun k => by rw [hindj]; dsimp only; split <;> norm_num
  have hexp : ∀ s, (facTypeOf r Q s i : ℝ) * (facTypeOf r Q s j : ℝ)
      = ∑ k : Fin r, ∑ k' : Fin r, ((if s k = i then (1:ℝ) else 0) * (if s k' = j then 1 else 0)) := by
    intro s
    have h1 : (facTypeOf r Q s i : ℝ) = ∑ k : Fin r, (if s k = i then (1:ℝ) else 0) := by
      unfold facTypeOf; rw [Finset.card_filter]; push_cast; rfl
    have h2 : (facTypeOf r Q s j : ℝ) = ∑ k' : Fin r, (if s k' = j then (1:ℝ) else 0) := by
      unfold facTypeOf; rw [Finset.card_filter]; push_cast; rfl
    rw [h1, h2, Finset.sum_mul_sum]
  have hS : (∑ s ∈ P, ((facTypeOf r Q s i : ℝ) * (facTypeOf r Q s j : ℝ)))
      = ∑ k : Fin r, ∑ k' : Fin r,
          (∑ s ∈ P, ((if s k = i then (1:ℝ) else 0) * (if s k' = j then 1 else 0))) := by
    rw [Finset.sum_congr rfl (fun s _ => hexp s)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
  have hterm : ∀ k k' : Fin r,
      facC r Q * (∑ s ∈ P, ((if s k = i then (1:ℝ) else 0) * (if s k' = j then 1 else 0)))
        ≤ indi k * indj k' * ((r:ℝ)^2 * dQ Q ^ 2) := by
    intro k k'
    by_cases hk : k = k'
    · subst hk
      rw [facPair_coord_diag r Q i j hij k, mul_zero]
      have : 0 ≤ indi k * indj k := mul_nonneg (hindi_nn k) (hindj_nn k)
      positivity
    · rw [facPair_coord_count r Q i j k k' hk]
      have hcount := facC_prod_erase_le r Q hr hQ hd k k' hk
      rw [show facC r Q * (indi k * indj k' * ∏ m ∈ (Finset.univ.erase k).erase k', ((facBlock r Q m).card : ℝ))
            = indi k * indj k' * (facC r Q * ∏ m ∈ (Finset.univ.erase k).erase k', ((facBlock r Q m).card : ℝ)) by
              rw [hindi, hindj]; ring]
      exact mul_le_mul_of_nonneg_left hcount.2 (mul_nonneg (hindi_nn k) (hindj_nn k'))
  rw [hS, Finset.mul_sum]
  calc ∑ k : Fin r, facC r Q * ∑ k' : Fin r, (∑ s ∈ P, ((if s k = i then (1:ℝ) else 0) * (if s k' = j then 1 else 0)))
      = ∑ k : Fin r, ∑ k' : Fin r, facC r Q * (∑ s ∈ P, ((if s k = i then (1:ℝ) else 0) * (if s k' = j then 1 else 0))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_); rw [Finset.mul_sum]
    _ ≤ ∑ k : Fin r, ∑ k' : Fin r, indi k * indj k' * ((r:ℝ)^2 * dQ Q ^ 2) := by
        refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun k' _ => hterm k k'))
    _ = ((r:ℝ)^2 * dQ Q ^ 2) * ((∑ k : Fin r, indi k) * (∑ k' : Fin r, indj k')) := by
        rw [Finset.sum_mul_sum]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k' _ => ?_); ring
    _ ≤ ((r:ℝ)^2 * dQ Q ^ 2) * (1 * 1) := by
        apply mul_le_mul_of_nonneg_left _ hRnn
        have hi := facBlock_indicator_sum_le_one r Q i
        have hj := facBlock_indicator_sum_le_one r Q j
        have hj0 : 0 ≤ ∑ k : Fin r, indj k := Finset.sum_nonneg (fun k _ => hindj_nn k)
        exact mul_le_mul hi hj hj0 zero_le_one
    _ = (r:ℝ)^2 * dQ Q ^ 2 := by ring

/-- Selection types have vanishing diagonal contribution. -/
lemma facDiag_zero (r Q : ℕ)
    (s : Fin r → Fin (NQ Q)) (hs : s ∈ Fintype.piFinset (fun j => facBlock r Q j)) (i : Fin (NQ Q)) :
    ((facTypeOf r Q s i).choose 2 : ℝ) = 0 := by
  have h := facTypeOf_le_one r Q s hs i
  interval_cases h' : facTypeOf r Q s i <;> simp_all

/-- The factorial packing exists with value `≥ r² (L - 2 d_Q)²`. -/
lemma facPacking_exists (r Q : ℕ) (hr : 3 ≤ r) (hQ : r ≤ Q) (hd : 2 * dQ Q < facL r) :
    ∃ z : (Fin (NQ Q) → ℕ) → ℝ, IsPacking r Q z ∧
      (r:ℝ)^2 * (facL r - 2 * dQ Q)^2 ≤ valQ r Q z := by
  have hdQpos : 0 < dQ Q := by unfold dQ; positivity
  have himg := facTypeOf_mem_admTypes r Q hr
  have hbpos : ∀ j : Fin r, 0 < ((facBlock r Q j).card : ℝ) := fun j => by
    exact_mod_cast facBlock_card_pos r Q hr hQ hd j
  have hprodpos : 0 < ∏ j : Fin r, ((facBlock r Q j).card : ℝ) := Finset.prod_pos (fun j _ => hbpos j)
  refine ⟨facWeight r Q, ⟨facWeight_nonneg r Q, ?_, ?_⟩, ?_⟩
  · intro i j hijlt
    have := facWeight_moment r Q (fun t => (t i : ℝ) * (t j : ℝ)) himg
    rw [this]
    exact facOffDiag_bound r Q hr hQ hd i j (ne_of_lt hijlt)
  · intro i
    have := facWeight_moment r Q (fun t => ((t i).choose 2 : ℝ)) himg
    rw [this]
    have hz : ∑ s ∈ Fintype.piFinset (fun j => facBlock r Q j), ((facTypeOf r Q s i).choose 2 : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      exact facDiag_zero r Q s hs i
    rw [hz, mul_zero]
    positivity
  · unfold valQ
    have := facWeight_moment r Q (fun _ => (1:ℝ)) himg
    simp only [one_mul] at this
    rw [this]
    rw [Finset.sum_const, facPiFinset_card, nsmul_eq_mul, mul_one]
    have hcast : ((∏ j : Fin r, (facBlock r Q j).card : ℕ) : ℝ) = ∏ j : Fin r, ((facBlock r Q j).card : ℝ) := by
      push_cast; ring
    rw [hcast]
    have hval : facC r Q * ∏ j : Fin r, ((facBlock r Q j).card : ℝ) = (r:ℝ)^2 * facEll r Q ^ 2 := by
      unfold facC; field_simp
    rw [hval]
    have hell : facL r - 2 * dQ Q ≤ facEll r Q := facEll_lower r Q hr hQ hd
    have hell0 : 0 ≤ facL r - 2 * dQ Q := by linarith [hd]
    have hsq : (facL r - 2 * dQ Q)^2 ≤ facEll r Q ^ 2 := by nlinarith [hell, hell0]
    nlinarith [hsq, sq_nonneg (facEll r Q)]

/-- Dyadic factorial packing. -/
theorem Lambda_factorial_lower (r : ℕ) (hr : 3 ≤ r) :
    (r : ℝ) ^ 2 / ((Nat.factorial r) : ℝ) ^ ((2 : ℝ) / r) ≤ Lam r := by
  have hpos : (0:ℝ) < Nat.factorial r := by positivity
  have htarget : (r:ℝ)^2 / (Nat.factorial r : ℝ)^((2:ℝ)/r) = (r:ℝ)^2 * (facL r)^2 := by
    unfold facL
    rw [← Real.rpow_natCast ((Nat.factorial r : ℝ) ^ (-(1 / (r:ℝ)))) 2, ← Real.rpow_mul hpos.le]
    rw [show (-(1 / (r:ℝ))) * (2:ℕ) = -((2:ℝ)/r) by push_cast; ring]
    rw [Real.rpow_neg hpos.le, div_eq_mul_inv]
  rw [htarget]
  have hdQ : Tendsto (fun Q : ℕ => dQ Q) atTop (nhds 0) := by
    unfold dQ
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)
    exact this.congr (fun n => by rw [div_pow, one_pow])
  set g : ℕ → ℝ := fun Q => (r:ℝ)^2 * (facL r - 2 * dQ Q)^2 with hg_def
  have hg : Tendsto g atTop (nhds ((r:ℝ)^2 * (facL r)^2)) := by
    have h1 : Tendsto (fun Q : ℕ => facL r - 2 * dQ Q) atTop (nhds (facL r)) := by
      have := (hdQ.const_mul (2:ℝ))
      simpa using tendsto_const_nhds.sub this
    have := (tendsto_const_nhds (x := (r:ℝ)^2)).mul (h1.pow 2)
    simpa [hg_def] using this
  have hev : ∀ᶠ Q : ℕ in atTop, g Q ≤ Lam r := by
    have hlt : ∀ᶠ Q : ℕ in atTop, 2 * dQ Q < facL r := by
      have := (hdQ.const_mul (2:ℝ)).eventually (gt_mem_nhds (by simpa using facL_pos r))
      simpa using this
    filter_upwards [hlt, eventually_ge_atTop r] with Q hQlt hQr
    obtain ⟨z, hz, hval⟩ := facPacking_exists r Q hr hQr hQlt
    have h1 : valQ r Q z ≤ lamQ r Q :=
      le_csSup (packing_values_bddAbove r Q (by omega)) ⟨z, hz, rfl⟩
    have h2 : lamQ r Q ≤ Lam r := lamQ_le_Lam r Q hr (by omega)
    calc g Q ≤ valQ r Q z := hval
      _ ≤ lamQ r Q := h1
      _ ≤ Lam r := h2
  exact le_of_tendsto hg hev

/-- The truncated logarithmic profile used in the asymptotically sharp
pair cover. -/
noncomputable def truncatedPhi (T x : ℝ) : ℝ := min T (max (1 - Real.log x) 0)

/-- The truncated logarithmic pair cover. -/
noncomputable def truncatedCover (r : ℕ) (T : ℝ) : ℝ → ℝ → ℝ := fun x y =>
  2 * truncatedPhi T x * truncatedPhi T y / ((r : ℝ) * ((r : ℝ) - T)) +
    if min x y ≤ Real.exp (1 - T) ∧
        min x y * max x y ^ (r - 1) ≤ 1 then 1 else 0

/--
Elementary bounds for the truncated logarithmic profile.
-/
theorem truncatedPhi_nonneg (T x : ℝ) (hT : 0 ≤ T) : 0 ≤ truncatedPhi T x := by
  exact le_min hT ( le_max_right _ _ )

theorem truncatedPhi_le (T x : ℝ) : truncatedPhi T x ≤ T := by
  exact min_le_left _ _

theorem truncatedPhi_ge_one_sub_log (T x : ℝ) (hxδ : Real.exp (1 - T) < x) :
    1 - Real.log x ≤ truncatedPhi T x := by
  exact le_min ( by linarith [ Real.log_exp ( 1 - T ), Real.log_lt_log ( by positivity ) hxδ ] ) ( le_max_left _ _ )

/--
The truncated logarithmic profile is integrable on the positive half-line.
-/
theorem truncatedPhi_integrableOn (T : ℝ) (hT : 1 < T) :
    MeasureTheory.IntegrableOn (truncatedPhi T) (Set.Ioi 0) := by
  -- Divide the integral into two parts: one over $(0, \exp(1-T)]$ and one over $(\exp(1-T), \exp(1)]$.
  have h_integrable_split : MeasureTheory.IntegrableOn (fun x => min T (max (1 - Real.log x) 0)) (Set.Ioc 0 (Real.exp 1)) := by
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => T;
    · norm_num;
    · exact Measurable.aestronglyMeasurable ( by exact Measurable.min measurable_const ( Measurable.max ( measurable_const.sub ( Real.measurable_log ) ) measurable_const ) );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact min_le_left _ _;
  have h_integrable_split : MeasureTheory.IntegrableOn (fun x => min T (max (1 - Real.log x) 0)) (Set.Ioi (Real.exp 1)) := by
    rw [ MeasureTheory.integrableOn_congr_fun ( fun x hx => by rw [ max_eq_right ( by linarith [ Real.log_exp 1, Real.log_le_log ( by positivity ) hx.out.le ] ), min_eq_right ( by linarith [ Real.log_exp 1, Real.log_le_log ( by positivity ) hx.out.le ] ) ] ) measurableSet_Ioi ] ; norm_num;
  convert MeasureTheory.IntegrableOn.union ‹IntegrableOn ( fun x => min T ( max ( 1 - Real.log x ) 0 ) ) ( Set.Ioc 0 ( Real.exp 1 ) ) volume› ‹IntegrableOn ( fun x => min T ( max ( 1 - Real.log x ) 0 ) ) ( Set.Ioi ( Real.exp 1 ) ) volume› using 1;
  exact Eq.symm ( Set.Ioc_union_Ioi_eq_Ioi ( by positivity ) )

/--
The integral of the truncated logarithmic function.
-/
theorem truncatedPhi_integral (T : ℝ) (hT : 1 < T) :
    ∫ x in Set.Ioi (0 : ℝ), truncatedPhi T x = Real.exp 1 - Real.exp (1 - T) := by
  -- Split the integral into two parts: one over $(0, \exp(1-T)]$ and the other over $(\exp(1-T), \exp 1]$.
  have h_split : ∫ x in Set.Ioi 0, truncatedPhi T x = (∫ x in Set.Ioc 0 (Real.exp (1 - T)), T) + (∫ x in Set.Ioc (Real.exp (1 - T)) (Real.exp 1), (1 - Real.log x)) := by
    rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ];
    · rw [ ← MeasureTheory.integral_add ];
      · congr with x ; by_cases hx : 0 < x <;> by_cases hx' : x ≤ Real.exp ( 1 - T ) <;> simp +decide [ hx, hx', Set.indicator ];
        · rw [ if_neg ( not_and_of_not_left _ ( by linarith ) ) ] ; unfold truncatedPhi ;
          rw [ min_eq_left ] <;> cases max_cases ( 1 - Real.log x ) 0 <;> linarith [ Real.log_exp ( 1 - T ), Real.log_le_log hx hx' ];
        · split_ifs <;> simp_all +decide [ truncatedPhi ];
          · rw [ min_eq_right ];
            · exact max_eq_left ( sub_nonneg.2 <| Real.log_le_iff_le_exp ( by linarith ) |>.2 <| by linarith );
            · cases max_cases ( 1 - Real.log x ) 0 <;> linarith [ Real.log_exp ( 1 - T ), Real.log_le_log ( by positivity ) ( by linarith : x ≥ Real.exp ( 1 - T ) ) ];
          · rw [ min_eq_right ] <;> norm_num;
            · exact Real.log_exp 1 ▸ Real.log_le_log ( by positivity ) ( le_of_lt ‹_› );
            · exact ⟨ by linarith [ Real.log_exp 1, Real.log_lt_log ( by positivity ) ‹Real.exp 1 < x› ], by linarith ⟩;
        · linarith [ Real.exp_pos ( 1 - T ) ];
      · rw [ MeasureTheory.integrable_indicator_iff ] <;> norm_num;
      · rw [ MeasureTheory.integrable_indicator_iff ];
        · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub continuousAt_const ( Real.continuousAt_log ( ne_of_gt <| lt_of_lt_of_le ( by positivity ) hx.1 ) ) ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
        · norm_num;
    · norm_num;
    · norm_num;
    · norm_num;
  rw [ h_split, ← intervalIntegral.integral_of_le, ← intervalIntegral.integral_of_le, intervalIntegral.integral_sub ] <;> norm_num;
  · ring;
  · linarith;
  · positivity

/--
The standard expansion of the square of a finite sum, arranged over
unordered pairs.
-/
theorem two_mul_sum_pairs_eq_sq_sub_sum_sq (r : ℕ) (a : Fin r → ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2),
        2 * a p.1 * a p.2 =
      (∑ i, a i) ^ 2 - ∑ i, (a i) ^ 2 := by
  induction' r with r ih <;> simp_all +decide [ Fin.sum_univ_succ, Finset.sum_filter ] ; ring_nf!;
  rw [ ← ih ] ; ring_nf;
  erw [ Finset.sum_product ] ; simp +decide [ Fin.sum_univ_succ  ] ; ring_nf;
  erw [ Finset.sum_product ] ; simp +decide [ Finset.mul_sum _ _ _, mul_assoc, Finset.sum_mul ] ;

/--
A useful quadratic lower bound for pair sums.
-/
theorem sum_pairs_ge_of_sum_ge_of_bounded (r : ℕ) (T : ℝ) (a : Fin r → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (haT : ∀ i, a i ≤ T)
    (hsum : (r : ℝ) ≤ ∑ i, a i) :
    (r : ℝ) * ((r : ℝ) - T) ≤
      ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2),
        2 * a p.1 * a p.2 := by
  rcases r with ( _ | r ) <;> norm_num at *;
  have := two_mul_sum_pairs_eq_sq_sub_sum_sq ( r + 1 ) a;
  have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => mul_le_mul_of_nonneg_left ( haT i ) ( ha0 i );
  simp_all +decide [ ← sq, ← Finset.sum_mul _ _ _ ];
  by_cases hT : T ≤ ∑ i, a i;
  · nlinarith;
  · nlinarith [ show ( ∑ i, a i ^ 2 ) ≤ ( ∑ i, a i ) ^ 2 by simpa only [ sq, Finset.sum_mul _ _ _ ] using Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun i _ => ha0 i ) ( Finset.mem_univ i ) ) ( ha0 i ) ]

/--
If one coordinate is below the truncation threshold, the product
constraint supplies a second coordinate forming an indicator-cover pair.
-/
theorem exists_indicator_pair_of_small (r : ℕ) (hr : 3 ≤ r) (T : ℝ)
    (x : Fin r → ℝ) (hx : ∀ i, 0 < x i) (hprod : ∏ i, x i ≤ 1)
    (i : Fin r) (hi : x i ≤ Real.exp (1 - T)) :
    ∃ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2),
      min (x p.1) (x p.2) ≤ Real.exp (1 - T) ∧
        min (x p.1) (x p.2) * max (x p.1) (x p.2) ^ (r - 1) ≤ 1 := by
  -- Choose `i0` globally minimizing x and `j0` minimizing among indices other than i0.
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin r, ∀ j : Fin r, x j ≥ x i0 := by
    simpa using Finset.exists_min_image Finset.univ ( fun i => x i ) ⟨ i, Finset.mem_univ i ⟩
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin r, j0 ≠ i0 ∧ ∀ k : Fin r, k ≠ i0 → x k ≥ x j0 := by
    have := Finset.exists_min_image ( Finset.univ.erase i0 ) ( fun k => x k ) ⟨ if i0 = ⟨ 0, by linarith ⟩ then ⟨ 1, by linarith ⟩ else ⟨ 0, by linarith ⟩, by aesop ⟩ ; aesop;
  refine' ⟨ if i0 < j0 then ( i0, j0 ) else ( j0, i0 ), _, _, _ ⟩ <;> split_ifs <;> simp_all +decide;
  · exact lt_of_le_of_ne ‹_› hj0.1;
  · exact le_trans ( hi0 i ) hi;
  · exact le_trans ( hi0 i ) hi;
  · have h_prod_le_one : ∏ k ∈ Finset.univ.erase i0, x k ≥ x j0 ^ (r - 1) := by
      exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => le_of_lt ( hx _ ) ) fun k hk => hj0.2 k <| Finset.ne_of_mem_erase hk );
    rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i0 ) ] at hprod ; nlinarith [ hx i0, hx j0 ];
  · refine' le_trans _ hprod;
    rw [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ i0 ) ];
    gcongr;
    · linarith [ hx i0 ];
    · refine' le_trans _ ( Finset.prod_le_prod _ fun k hk => hj0.2 k <| by aesop ) <;> norm_num;
      · simp +decide [ Finset.card_sdiff, * ];
      · exact fun _ _ => le_of_lt ( hx _ )

/--
If every coordinate is above the truncation threshold, the sum of the
truncated logarithmic profiles is at least `r`.
-/
theorem sum_truncatedPhi_ge (r : ℕ) (T : ℝ) (x : Fin r → ℝ)
    (hx : ∀ i, 0 < x i) (hthreshold : ∀ i, Real.exp (1 - T) < x i)
    (hprod : ∏ i, x i ≤ 1) :
    (r : ℝ) ≤ ∑ i, truncatedPhi T (x i) := by
  -- Applying the inequality `1 - \log x_i \leq \text{truncatedPhi } T (x_i)` for each $i$.
  have h_truncatedPhi_ge_one_sub_log : ∀ i, 1 - Real.log (x i) ≤ truncatedPhi T (x i) := by
    intros i
    apply truncatedPhi_ge_one_sub_log T (x i) (hthreshold i);
  refine' le_trans _ ( Finset.sum_le_sum fun i _ => h_truncatedPhi_ge_one_sub_log i );
  have h_log_prod : Real.log (∏ i, x i) = ∑ i, Real.log (x i) := by
    apply Real.log_prod; intro i _; exact ne_of_gt (hx i);
  norm_num at *;
  exact h_log_prod ▸ Real.log_nonpos ( Finset.prod_nonneg fun _ _ => le_of_lt ( hx _ ) ) hprod

/--
The truncated logarithmic construction satisfies the pair-cover
constraint.
-/
theorem truncatedCover_isPairCover (r : ℕ) (hr : 3 ≤ r) (T : ℝ)
    (hT1 : 1 < T) (hTr : T < r) : IsPairCover r (truncatedCover r T) := by
  refine' ⟨ _, _, _, _ ⟩;
  · unfold truncatedCover;
    grind;
  · intro x y; unfold truncatedCover;
    exact add_nonneg ( div_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( truncatedPhi_nonneg T x ( by linarith ) ) ) ( truncatedPhi_nonneg T y ( by linarith ) ) ) ( mul_nonneg ( by positivity ) ( by linarith ) ) ) ( by positivity );
  · refine' MeasureTheory.Integrable.add _ _;
    · refine' MeasureTheory.Integrable.div_const _ _;
      convert MeasureTheory.Integrable.mul_prod ( MeasureTheory.Integrable.const_mul ( truncatedPhi_integrableOn T hT1 ) 2 ) ( truncatedPhi_integrableOn T hT1 ) using 1;
      erw [ ← MeasureTheory.Measure.prod_restrict ];
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun p => gCover r p.1 p.2;
      · exact gCover_isPairCover r hr |>.2.2.1;
      · refine' Measurable.aestronglyMeasurable _;
        exact Measurable.ite ( MeasurableSet.inter ( measurableSet_le ( measurable_fst.min measurable_snd ) measurable_const ) ( measurableSet_le ( measurable_fst.min measurable_snd |> Measurable.mul <| measurable_fst.max measurable_snd |> Measurable.pow_const <| r - 1 ) measurable_const ) ) measurable_const measurable_const;
      · refine' MeasureTheory.ae_of_all _ _;
        intro p; split_ifs <;> norm_num [ gCover ] ;
        · aesop;
        · split_ifs <;> norm_num;
  · intro x hx hprod
    by_cases h_exists : ∃ i, x i ≤ Real.exp (1 - T);
    · obtain ⟨ i, hi ⟩ := h_exists;
      obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := exists_indicator_pair_of_small r hr T x hx hprod i hi;
      refine' le_trans _ ( Finset.single_le_sum ( fun p _ => _ ) hp₁ );
      · unfold truncatedCover; norm_num [ hp₂, hp₃ ] ;
        exact div_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( truncatedPhi_nonneg _ _ ( by linarith ) ) ) ( truncatedPhi_nonneg _ _ ( by linarith ) ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( by linarith ) );
      · refine' add_nonneg _ _;
        · exact div_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( truncatedPhi_nonneg _ _ ( by linarith ) ) ) ( truncatedPhi_nonneg _ _ ( by linarith ) ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( by linarith ) );
        · split_ifs <;> norm_num;
    · -- Otherwise all exceed threshold; sum_truncatedPhi_ge gives sum φ≥r and each 0≤φ≤T; sum_pairs_ge... gives numerator pair sum≥r(r-T), then divide by positive denominator and sum termwise, ignoring nonnegative indicators.
      have h_sum_truncatedPhi : r ≤ ∑ i, truncatedPhi T (x i) := by
        apply sum_truncatedPhi_ge r T x hx (fun i => not_le.mp (fun hi => h_exists ⟨i, hi⟩)) hprod
      have h_sum_pairs : r * (r - T) ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2), 2 * truncatedPhi T (x p.1) * truncatedPhi T (x p.2) := by
        apply sum_pairs_ge_of_sum_ge_of_bounded r T (fun i => truncatedPhi T (x i)) (fun i => truncatedPhi_nonneg T (x i) (by linarith)) (fun i => truncatedPhi_le T (x i)) h_sum_truncatedPhi;
      refine' le_trans _ ( Finset.sum_le_sum fun p hp => show truncatedCover r T ( x p.1 ) ( x p.2 ) ≥ 2 * truncatedPhi T ( x p.1 ) * truncatedPhi T ( x p.2 ) / ( r * ( r - T ) ) from _ );
      · rw [ ← Finset.sum_div _ _ _, le_div_iff₀ ] <;> nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast ];
      · exact le_add_of_nonneg_right ( by positivity )

/--
Evaluation of the one-dimensional integral arising from the symmetric
indicator region in the truncated cover.
-/
theorem truncated_indicator_outer_integral (r : ℕ) (hr : 3 ≤ r) (T : ℝ) :
    ∫ x in Set.Ioc (0 : ℝ) (Real.exp (1 - T)),
        (x ^ (-1 / ((r : ℝ) - 1)) - x) =
      ((r : ℝ) - 1) / ((r : ℝ) - 2) *
          Real.exp ((1 - T) * ((r : ℝ) - 2) / ((r : ℝ) - 1)) -
        (1 / 2 : ℝ) * Real.exp (2 * (1 - T)) := by
  rw [ ← intervalIntegral.integral_of_le ( by positivity ), intervalIntegral.integral_sub, integral_rpow ] <;> norm_num;
  · rw [ ← Real.exp_mul, ← Real.exp_nat_mul ] ; norm_num ; ring_nf;
    field_simp;
    rw [ Real.zero_rpow ( by nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast, div_mul_cancel₀ ( 1 : ℝ ) ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] : ( -1 + r : ℝ ) ≠ 0 ) ] ) ] ; rw [ one_sub_div ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) ] ; norm_num ; ring_nf;
    grind;
  · rw [ lt_div_iff₀ ] <;> linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ];
  · exact intervalIntegral.intervalIntegrable_rpow' ( by rw [ lt_div_iff₀ ] <;> linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] )

/--
The indicator part of the truncated cover has the expected symmetric
one-dimensional integral.
-/
theorem truncated_indicator_integral (r : ℕ) (hr : 3 ≤ r) (T : ℝ) (hT : 1 < T) :
    ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ),
        (if min p.1 p.2 ≤ Real.exp (1 - T) ∧
            min p.1 p.2 * max p.1 p.2 ^ (r - 1) ≤ 1 then (1 : ℝ) else 0) =
      2 * ∫ x in Set.Ioc (0 : ℝ) (Real.exp (1 - T)),
        (x ^ (-1 / ((r : ℝ) - 1)) - x) := by
  have h_integrable : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => if min p.1 p.2 ≤ Real.exp (1 - T) ∧ min p.1 p.2 * max p.1 p.2 ^ (r - 1) ≤ 1 then (1 : ℝ) else 0) (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun p => gCover r p.1 p.2;
    · have := gCover_isPairCover r hr;
      exact this.2.2.1;
    · refine' Measurable.aestronglyMeasurable _;
      exact Measurable.ite ( MeasurableSet.inter ( measurableSet_le ( measurable_fst.min measurable_snd ) measurable_const ) ( measurableSet_le ( measurable_fst.min measurable_snd |> Measurable.mul <| measurable_fst.max measurable_snd |> Measurable.pow_const <| r - 1 ) measurable_const ) ) measurable_const measurable_const;
    · filter_upwards [ MeasureTheory.ae_restrict_mem ( measurableSet_Ioi.prod measurableSet_Ioi ) ] with p hp;
      split_ifs <;> norm_num [ gCover ];
      · grind;
      · split_ifs <;> norm_num;
  have h_split : ∫ p in Set.Ioi 0 ×ˢ Set.Ioi 0, (if min p.1 p.2 ≤ Real.exp (1 - T) ∧ min p.1 p.2 * max p.1 p.2 ^ (r - 1) ≤ 1 then (1 : ℝ) else 0) = 2 * ∫ x in Set.Ioi 0, ∫ y in Set.Ioi x, (if x ≤ Real.exp (1 - T) ∧ x * y ^ (r - 1) ≤ 1 then (1 : ℝ) else 0) := by
    have h_split : ∫ p in Set.Ioi 0 ×ˢ Set.Ioi 0, (if min p.1 p.2 ≤ Real.exp (1 - T) ∧ min p.1 p.2 * max p.1 p.2 ^ (r - 1) ≤ 1 then (1 : ℝ) else 0) = (∫ p in Set.Ioi 0 ×ˢ Set.Ioi 0, (if p.1 < p.2 ∧ p.1 ≤ Real.exp (1 - T) ∧ p.1 * p.2 ^ (r - 1) ≤ 1 then (1 : ℝ) else 0)) + (∫ p in Set.Ioi 0 ×ˢ Set.Ioi 0, (if p.2 < p.1 ∧ p.2 ≤ Real.exp (1 - T) ∧ p.2 * p.1 ^ (r - 1) ≤ 1 then (1 : ℝ) else 0)) := by
      rw [ ← MeasureTheory.integral_add ];
      · refine' MeasureTheory.setIntegral_congr_ae _ _;
        · exact measurableSet_Ioi.prod measurableSet_Ioi;
        · refine' MeasureTheory.measure_mono_null _ _;
          exact { p : ℝ × ℝ | p.1 = p.2 };
          · grind;
          · erw [ show { p : ℝ × ℝ | p.1 = p.2 } = ( Set.range fun x : ℝ => ( x, x ) ) by ext ; aesop, MeasureTheory.Measure.prod_apply ];
            · simp +decide [ Set.preimage ];
            · exact ( by rw [ show ( Set.range fun x : ℝ => ( x, x ) ) = { p : ℝ × ℝ | p.1 = p.2 } by ext ; aesop ] ; exact measurableSet_eq_fun measurable_fst measurable_snd );
      · refine' h_integrable.mono' _ _;
        · refine' Measurable.aestronglyMeasurable _;
          exact Measurable.ite ( MeasurableSet.inter ( measurableSet_lt measurable_fst measurable_snd ) ( MeasurableSet.inter ( measurableSet_le measurable_fst measurable_const ) ( measurableSet_le ( measurable_fst.mul ( measurable_snd.pow_const _ ) ) measurable_const ) ) ) measurable_const measurable_const;
        · filter_upwards [ MeasureTheory.ae_restrict_mem ( measurableSet_Ioi.prod measurableSet_Ioi ) ] with p hp ; split_ifs <;> norm_num;
          grind;
      · refine' h_integrable.mono' _ _;
        · refine' Measurable.aestronglyMeasurable _;
          exact Measurable.ite ( MeasurableSet.inter ( measurableSet_lt measurable_snd measurable_fst ) ( MeasurableSet.inter ( measurableSet_le measurable_snd measurable_const ) ( measurableSet_le ( measurable_snd.mul ( measurable_fst.pow_const _ ) ) measurable_const ) ) ) measurable_const measurable_const;
        · filter_upwards [ MeasureTheory.ae_restrict_mem ( measurableSet_Ioi.prod measurableSet_Ioi ) ] with p hp ; split_ifs <;> norm_num;
          grind;
    have h_symm : ∫ p in Set.Ioi 0 ×ˢ Set.Ioi 0, (if p.2 < p.1 ∧ p.2 ≤ Real.exp (1 - T) ∧ p.2 * p.1 ^ (r - 1) ≤ 1 then (1 : ℝ) else 0) = ∫ p in Set.Ioi 0 ×ˢ Set.Ioi 0, (if p.1 < p.2 ∧ p.1 ≤ Real.exp (1 - T) ∧ p.1 * p.2 ^ (r - 1) ≤ 1 then (1 : ℝ) else 0) := by
      rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ];
      · erw [ ← MeasureTheory.integral_prod_swap ];
        simp +decide [ Set.indicator ];
        ac_rfl;
      · exact measurableSet_Ioi.prod measurableSet_Ioi;
      · exact measurableSet_Ioi.prod measurableSet_Ioi;
    convert h_split.trans ( congr_arg₂ ( · + · ) rfl h_symm ) using 1 ; ring_nf;
    erw [ MeasureTheory.setIntegral_prod ];
    · norm_num [ ← MeasureTheory.integral_indicator, Set.indicator_apply ];
      congr with x ; split_ifs <;> simp_all +decide;
      grind;
    · refine' h_integrable.mono' _ _;
      · refine' Measurable.aestronglyMeasurable _;
        exact Measurable.ite ( MeasurableSet.inter ( measurableSet_lt measurable_fst measurable_snd ) ( MeasurableSet.inter ( measurableSet_le measurable_fst measurable_const ) ( measurableSet_le ( measurable_fst.mul ( measurable_snd.pow_const _ ) ) measurable_const ) ) ) measurable_const measurable_const;
      · filter_upwards [ MeasureTheory.ae_restrict_mem ( measurableSet_Ioi.prod measurableSet_Ioi ) ] with p hp ; split_ifs <;> norm_num;
        grind;
  have h_inner : ∀ x ∈ Set.Ioc 0 (Real.exp (1 - T)), ∫ y in Set.Ioi x, (if x * y ^ (r - 1) ≤ 1 then (1 : ℝ) else 0) = x ^ (-1 / (r - 1) : ℝ) - x := by
    intro x hx
    have h_inner_set : {y : ℝ | x < y ∧ x * y ^ (r - 1) ≤ 1} = Set.Ioc x (x ^ (-1 / (r - 1) : ℝ)) := by
      ext y;
      constructor <;> intro hy <;> rcases hy with ⟨ hy₁, hy₂ ⟩ <;> refine' ⟨ hy₁, _ ⟩;
      · have h_y_le : y ^ (r - 1) ≤ 1 / x := by
          rw [ le_div_iff₀ ] <;> linarith [ hx.1 ];
        have h_y_le : y ≤ (1 / x) ^ (1 / (r - 1) : ℝ) := by
          exact le_trans ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith [ hx.1 ] ), Nat.cast_sub ( by linarith ), Nat.cast_one, mul_one_div_cancel ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ), Real.rpow_one ] ) ( Real.rpow_le_rpow ( by exact pow_nonneg ( by linarith [ hx.1 ] ) _ ) h_y_le ( by exact one_div_nonneg.mpr ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) ) );
        convert h_y_le using 1 ; norm_num [ neg_div, Real.rpow_neg_eq_inv_rpow ];
      · refine' le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by linarith [ hx.1 ] ) hy₂ _ ) hx.1.le ) _;
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul hx.1.le, Nat.cast_sub ( by linarith ), Nat.cast_one, div_mul_cancel₀ _ ( sub_ne_zero_of_ne ( by norm_cast; linarith ) ), Real.rpow_neg_one, mul_inv_cancel₀ hx.1.ne' ];
    rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    rw [ show ( ∫ y : ℝ, if x < y then if x * y ^ ( r - 1 ) ≤ 1 then ( 1 : ℝ ) else 0 else 0 ) = ( ∫ y in Set.Ioc x ( x ^ ( -1 / ( r - 1 ) : ℝ ) ), ( 1 : ℝ ) ) from ?_ ];
    · norm_num [ hx.1.le ];
      exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_ge hx.1 ( show x ≤ 1 by exact hx.2.trans ( Real.exp_le_one_iff.mpr ( by linarith ) ) ) ( show ( -1 : ℝ ) / ( r - 1 ) ≤ 1 by rw [ div_le_iff₀ ] <;> linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) );
    · rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
      congr with y ; replace h_inner_set := Set.ext_iff.mp h_inner_set y ; aesop;
  rw [ h_split, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
  rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
  congr with x ; by_cases hx : 0 < x <;> by_cases hx' : x ≤ Real.exp ( 1 - T ) <;> simp +decide [ hx, hx', h_inner ]

/--
Exact integral cost of the truncated logarithmic cover.
-/
theorem truncatedCover_cost (r : ℕ) (hr : 3 ≤ r) (T : ℝ)
    (hT1 : 1 < T) (hTr : T < r) :
    (r : ℝ) ^ 2 / 2 * coverIntegral (truncatedCover r T) =
      (r : ℝ) / ((r : ℝ) - T) * (Real.exp 1 - Real.exp (1 - T)) ^ 2 +
      (r : ℝ) ^ 2 *
        (((r : ℝ) - 1) / ((r : ℝ) - 2) *
            Real.exp ((1 - T) * ((r : ℝ) - 2) / ((r : ℝ) - 1)) -
          (1 / 2 : ℝ) * Real.exp (2 * (1 - T))) := by
  convert congr_arg ( fun x : ℝ => ( r : ℝ ) ^ 2 / 2 * ( x ) ) ( MeasureTheory.integral_add ?_ ?_ ) using 1;
  · rw [ truncated_indicator_integral r hr T hT1 ];
    erw [ MeasureTheory.setIntegral_prod ];
    · norm_num [ MeasureTheory.integral_div, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, truncatedPhi_integral T hT1 ];
      rw [ truncated_indicator_outer_integral r hr T ] ; ring_nf;
      grind;
    · refine' MeasureTheory.Integrable.div_const _ _;
      have h_integrable : MeasureTheory.IntegrableOn (fun x : ℝ => truncatedPhi T x) (Set.Ioi 0) := by
        convert truncatedPhi_integrableOn T hT1 using 1;
      simpa only [ mul_assoc, MeasureTheory.Measure.prod_restrict ] using MeasureTheory.Integrable.mul_prod ( h_integrable.const_mul 2 ) h_integrable;
  · refine' MeasureTheory.Integrable.div_const _ _;
    convert MeasureTheory.Integrable.mul_prod ( MeasureTheory.Integrable.const_mul ( truncatedPhi_integrableOn T hT1 ) 2 ) ( truncatedPhi_integrableOn T hT1 ) using 1;
    erw [ ← MeasureTheory.Measure.prod_restrict ];
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun p => ( gCover r p.1 p.2 : ℝ );
    · exact gCover_isPairCover r hr |>.2.2.1;
    · refine' Measurable.aestronglyMeasurable _;
      exact Measurable.ite ( MeasurableSet.inter ( measurableSet_le ( measurable_fst.min measurable_snd ) measurable_const ) ( measurableSet_le ( measurable_fst.min measurable_snd |> Measurable.mul <| measurable_fst.max measurable_snd |> Measurable.pow_const <| r - 1 ) measurable_const ) ) measurable_const measurable_const;
    · filter_upwards [ MeasureTheory.ae_restrict_mem ( measurableSet_Ioi.prod measurableSet_Ioi ) ] with p hp ; split_ifs <;> norm_num [ gCover ];
      · aesop;
      · split_ifs <;> norm_num

/--
The factorial packing bound gives the lower half of the limit theorem: every
number strictly below `e²` is eventually a strict lower bound for `Λ_r`.
-/
theorem Lambda_eventually_gt {a : ℝ} (ha : a < Real.exp 2) :
    ∀ᶠ r : ℕ in atTop, a < Lam r := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ r ≥ N₁, a < (r : ℝ) ^ 2 / ((Nat.factorial r) : ℝ) ^ ((2 : ℝ) / r) := by
    exact Filter.eventually_atTop.mp ( factorial_ratio_tendsto_exp_sq.eventually ( lt_mem_nhds ha ) );
  filter_upwards [ Filter.eventually_ge_atTop N₁, Filter.eventually_ge_atTop 3 ] with r hr₁ hr₂ using lt_of_lt_of_le ( hN₁ r hr₁ ) ( Lambda_factorial_lower r hr₂ )

/-! ## Elementary consequences of the prime number theorem -/

/--
There are constants `x₀ ≥ 3` and `C > 0` with `π(x) ≤ C x / log x` for `x ≥ x₀`.
-/
theorem pi_crude : ∃ (x₀ C : ℝ), 3 ≤ x₀ ∧ 0 < C ∧
    ∀ x : ℝ, x₀ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * x / log x := by
  -- By definition of $c$, we know that for all $x \ge X$, $|c(x)| \le 1$.
  obtain ⟨c, hc⟩ := pi_alt
  obtain ⟨X, hX⟩ : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |c x| ≤ 1 := by
    simpa [ abs_mul ] using hc.1.def one_pos;
  exact ⟨ Max.max X 3, 2, le_max_right _ _, by norm_num, fun x hx => by rw [ hc.2 x ] ; exact div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_right ( by linarith [ abs_le.mp ( hX x ( le_trans ( le_max_left _ _ ) hx ) ) ] ) ( by linarith [ le_max_right X 3 ] ) ) ( Real.log_nonneg ( by linarith [ le_max_right X 3 ] ) ) ⟩

/-- The number of primes in the half-open interval `(a, b]`, as a real number. -/
noncomputable def primesIn (a b : ℝ) : ℝ :=
  (Nat.primeCounting ⌊b⌋₊ : ℝ) - (Nat.primeCounting ⌊a⌋₊ : ℝ)

/--
Fix an integer `r ≥ 2` and `0 ≤ a < b`. With `y = n^{1/r}` and `M = y / log n`,
the number of primes in `(a y, b y]` is `(r (b - a) + o(1)) M`; equivalently the
ratio to `M` tends to `r (b - a)`.
-/
theorem prime_bin (r : ℕ) (hr : 2 ≤ r) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    Tendsto
      (fun n : ℕ =>
        primesIn (a * (n : ℝ) ^ ((1 : ℝ) / r)) (b * (n : ℝ) ^ ((1 : ℝ) / r)) /
          ((n : ℝ) ^ ((1 : ℝ) / r) / log n))
      atTop (nhds ((r : ℝ) * (b - a))) := by
  -- By definition of $c$, we know that $c(x) = o(1)$ as $x \to \infty$.
  obtain ⟨c, hc⟩ := pi_alt
  have hc_zero : Filter.Tendsto c Filter.atTop (nhds 0) := by
    simpa using hc.1.tendsto_div_nhds_zero;
  -- Apply the prime number theorem to the intervals $(a y, b y]$ and $(0, b y]$.
  have h_prime_number_theorem : Filter.Tendsto (fun n : ℕ => ((1 + c (b * (n : ℝ) ^ (1 / r : ℝ))) * (b * (n : ℝ) ^ (1 / r : ℝ)) / Real.log (b * (n : ℝ) ^ (1 / r : ℝ)) - (1 + c (a * (n : ℝ) ^ (1 / r : ℝ))) * (a * (n : ℝ) ^ (1 / r : ℝ)) / Real.log (a * (n : ℝ) ^ (1 / r : ℝ))) / ((n : ℝ) ^ (1 / r : ℝ) / Real.log n)) Filter.atTop (nhds (r * (b - a))) := by
    by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> simp_all +decide [ division_def ];
    · -- Simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun n : ℕ => (1 + c (b * (n : ℝ) ^ (1 / r : ℝ))) * b / (Real.log b / Real.log n + 1 / r)) Filter.atTop (nhds (r * b)) by
        refine h_simplify.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
        rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ] ; ring_nf;
        field_simp;
        rw [ one_add_div ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hn ), div_div_eq_mul_div ] ; ring;
      convert Filter.Tendsto.div ( Filter.Tendsto.mul ( tendsto_const_nhds.add ( hc_zero.comp _ ) ) tendsto_const_nhds ) ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) tendsto_const_nhds ) _ using 2 <;> norm_num;
      · ring;
      · exact Filter.Tendsto.const_mul_atTop hab ( tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      · linarith;
    · linarith;
    · -- Simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun n : ℕ => ((1 + c (b * (n : ℝ) ^ (1 / r : ℝ))) * b / (Real.log b + (1 / r : ℝ) * Real.log n) - (1 + c (a * (n : ℝ) ^ (1 / r : ℝ))) * a / (Real.log a + (1 / r : ℝ) * Real.log n)) * Real.log n) Filter.atTop (nhds (r * (b - a))) by
        refine h_simplify.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
        rw [ Real.log_mul, Real.log_mul ] <;> norm_num [ hn.ne', ha0, hb0 ] ; ring_nf;
        · norm_num [ Real.log_rpow ( Nat.cast_pos.mpr hn ), mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn ) _ ) ] ; ring;
        · positivity;
        · positivity;
      -- We can divide the numerator and the denominator by $\log n$.
      suffices h_divide : Filter.Tendsto (fun n : ℕ => ((1 + c (b * (n : ℝ) ^ (1 / r : ℝ))) * b / ((Real.log b / Real.log n) + (1 / r : ℝ)) - (1 + c (a * (n : ℝ) ^ (1 / r : ℝ))) * a / ((Real.log a / Real.log n) + (1 / r : ℝ)))) Filter.atTop (nhds (r * (b - a))) by
        refine h_divide.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
        field_simp [mul_comm, mul_assoc, mul_left_comm];
        rw [ show ( r : ℝ ) * log b / log n + 1 = ( r * log b + log n ) / log n by rw [ div_add_one ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) ], show ( r : ℝ ) * log a / log n + 1 = ( r * log a + log n ) / log n by rw [ div_add_one ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) ] ] ; norm_num [ mul_sub, mul_div_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hn ] ;
      -- As $n \to \infty$, $\frac{\log b}{\log n} \to 0$ and $\frac{\log a}{\log n} \to 0$.
      have h_log_div : Filter.Tendsto (fun n : ℕ => Real.log b / Real.log n) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun n : ℕ => Real.log a / Real.log n) Filter.atTop (nhds 0) := by
        exact ⟨ tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ), tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ⟩;
      convert Filter.Tendsto.sub ( Filter.Tendsto.div ( Filter.Tendsto.mul ( tendsto_const_nhds.add ( hc_zero.comp _ ) ) tendsto_const_nhds ) ( h_log_div.1.add tendsto_const_nhds ) _ ) ( Filter.Tendsto.div ( Filter.Tendsto.mul ( tendsto_const_nhds.add ( hc_zero.comp _ ) ) tendsto_const_nhds ) ( h_log_div.2.add tendsto_const_nhds ) _ ) using 2 <;> norm_num;
      · ring;
      · exact Filter.Tendsto.const_mul_atTop ( by linarith ) ( tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      · linarith;
      · exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      · linarith;
  convert h_prime_number_theorem using 2 ; unfold primesIn ; aesop;

/--
A version of the crude prime-counting estimate with the fixed threshold `3`.
The constant can be enlarged to absorb the compact interval between `3` and
`x₀` in `pi_crude`.
-/
theorem pi_crude_from_three : ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 3 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * x / log x := by
  obtain ⟨ x₀, C, hx₀₁, hx₀₂, hx₀₃ ⟩ := pi_crude;
  -- Define K as the maximum of C and (Nat.primeCounting ⌊x₀⌋₊ + 1).
  set K := max C ((Nat.primeCounting ⌊x₀⌋₊ : ℝ) + 1) with hK_def
  use K
  simp [hK_def, hx₀₂ ];
  intro x hx; by_cases hx' : x < x₀ <;> simp_all +decide [ mul_div_assoc ] ;
  · refine' le_trans _ ( le_mul_of_one_le_right ( by positivity ) _ );
    · exact le_trans ( Nat.cast_le.mpr <| Nat.monotone_primeCounting <| Nat.floor_mono hx'.le ) <| le_max_of_le_right <| le_add_of_nonneg_right zero_le_one;
    · rw [ one_le_div ( Real.log_pos ( by linarith ) ) ] ; linarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < x ) ];
  · exact le_trans ( hx₀₃ x hx' ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( div_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ) ) )

/--
The pointwise PNT estimate needed in the prime-pair tail argument, uniformly
for primes in the truncated range.
-/
theorem prime_pair_summand_eventually (r : ℕ) (hr : 3 ≤ r) (δ C : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hC : ∀ x : ℝ, 3 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * x / log x) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈
      (Finset.range (⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ + 1)).filter Nat.Prime,
      (Nat.primeCounting ⌊((n : ℝ) / p) ^ ((1 : ℝ) / (r - 1))⌋₊ : ℝ) ≤
        C * r * ((n : ℝ) / p) ^ ((1 : ℝ) / (r - 1)) / log n := by
  -- For sufficiently large n, the denominator grows faster than the numerator, hence the fraction tends to zero.
  have h_bound : ∀ᶠ n in atTop, ∀ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ (1 / r : ℝ)⌋₊ + 1)).filter Nat.Prime, (n / p : ℝ) ^ (1 / (r - 1 : ℝ)) ≥ 3 := by
    -- For sufficiently large n, the denominator grows faster than the numerator, hence the fraction tends to zero. Use this fact.
    have h_bound : ∀ᶠ n in atTop, ∀ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ (1 / r : ℝ)⌋₊ + 1)).filter Nat.Prime, (n / p : ℝ) ≥ 3 ^ (r - 1 : ℝ) := by
      -- For sufficiently large n, we have n / (δ * n ^ (1 / r)) ≥ 3 ^ (r - 1).
      have h_bound : ∀ᶠ n in atTop, n / (δ * (n : ℝ) ^ (1 / r : ℝ)) ≥ 3 ^ (r - 1 : ℝ) := by
        -- Simplify the expression $n / (δ * n ^ (1 / r))$ to $n^{1 - 1/r} / δ$.
        suffices h_simplified : ∀ᶠ n in atTop, (n : ℝ) ^ (1 - 1 / (r : ℝ)) / δ ≥ 3 ^ (r - 1 : ℝ) by
          filter_upwards [ h_simplified, Filter.eventually_gt_atTop 0 ] with n hn hn' using by rw [ Real.rpow_sub hn' ] at hn; norm_num at *; ring_nf at *; linarith;
        have h_simplified : Filter.Tendsto (fun n : ℝ => (n : ℝ) ^ (1 - 1 / (r : ℝ)) / δ) Filter.atTop Filter.atTop := by
          exact Filter.Tendsto.atTop_div_const ( by positivity ) ( tendsto_rpow_atTop ( by exact sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) );
        exact h_simplified.eventually_ge_atTop _;
      filter_upwards [ h_bound, Filter.eventually_gt_atTop 0 ] with n hn hn';
      intro p hp; refine le_trans hn ?_; gcongr;
      · exact Nat.cast_pos.mpr ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) );
      · exact le_trans ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp <| Finset.mem_filter.mp hp |>.1 ) <| Nat.floor_le <| by positivity;
    filter_upwards [ h_bound, Filter.eventually_gt_atTop 0 ] with n hn hn' p hp using le_trans ( by rw [ ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( sub_ne_zero_of_ne ( by norm_cast; linarith ) ), Real.rpow_one ] ) ( Real.rpow_le_rpow ( by positivity ) ( hn p hp ) ( by exact one_div_nonneg.mpr ( sub_nonneg.mpr ( by norm_cast; linarith ) ) ) );
  have h_log_bound : ∀ᶠ n in atTop, ∀ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ (1 / r : ℝ)⌋₊ + 1)).filter Nat.Prime, Real.log ((n / p : ℝ) ^ (1 / (r - 1 : ℝ))) ≥ Real.log n / r := by
    filter_upwards [ h_bound, Filter.eventually_gt_atTop 1 ] with n hn hn';
    intros p hp
    have h_log_bound : Real.log ((n / p : ℝ) ^ (1 / (r - 1 : ℝ))) ≥ (1 / (r - 1 : ℝ)) * (Real.log n - Real.log (δ * (n : ℝ) ^ (1 / r : ℝ))) := by
      rw [ Real.log_rpow ( by exact div_pos ( by positivity ) ( Nat.cast_pos.mpr ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) ) ), Real.log_div ( by positivity ) ( by exact Nat.cast_ne_zero.mpr ( Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ) ) ];
      gcongr;
      · exact div_nonneg zero_le_one ( by norm_num; linarith );
      · exact Nat.cast_pos.mpr ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) );
      · exact le_trans ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp <| Finset.mem_filter.mp hp |>.1 ) <| Nat.floor_le <| by positivity;
    have h_log_bound : Real.log (δ * (n : ℝ) ^ (1 / r : ℝ)) ≤ (1 / r : ℝ) * Real.log n := by
      rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ];
      linarith [ Real.log_le_sub_one_of_pos hδ0 ];
    rcases r with ( _ | _ | r ) <;> norm_num at *;
    field_simp at *;
    nlinarith [ Real.log_pos hn' ];
  filter_upwards [ h_bound.natCast_atTop, h_log_bound.natCast_atTop, Filter.eventually_gt_atTop 1 ] with n hn hn' hn'';
  intro p hp; specialize hC ( ( n / p : ℝ ) ^ ( 1 / ( r - 1 : ℝ ) ) ) ( hn p hp ) ; specialize hn' p hp; rw [ le_div_iff₀ ] at *;
  · rw [ ge_iff_le, div_le_iff₀ ( by positivity ) ] at hn';
    nlinarith [ show 0 ≤ C * ( n / p : ℝ ) ^ ( 1 / ( r - 1 : ℝ ) ) by exact le_trans ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg <| by linarith [ hn p hp ] ) ) hC ];
  · exact lt_of_lt_of_le ( div_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hn'' ) ) ( by positivity ) ) hn';
  · exact Real.log_pos <| Nat.one_lt_cast.mpr hn''

/-
A logarithmically sharp cumulative weighted-prime estimate. Abel summation
turns the crude prime-counting bound into the required estimate; its integral
is split at the square-root scale, and finitely many small primes are absorbed
into the constant.
-/
set_option maxHeartbeats 800000 in
theorem prime_rpow_neg_sum_eventually_le {a C : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC0 : 0 < C)
    (hC : ∀ x : ℝ, 3 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * x / log x) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ m : ℕ in atTop,
      ∑ p ∈ (Finset.range (m + 1)).filter Nat.Prime, (p : ℝ) ^ (-a) ≤
        D * (m : ℝ) ^ (1 - a) / log m := by
  -- By Abel/partial summation, we have:
  have h_abel : ∀ m : ℕ, (3 ≤ m → (∑ p ∈ Finset.filter Nat.Prime (Finset.range (m + 1)), ((p : ℝ) ^ (-a))) ≤ 2 ^ (-a) + 3 ^ (-a) + m ^ (-a) * (Nat.primeCounting m : ℝ) + a * ∫ t in (3 : ℝ)..m, (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (-a - 1)) := by
    intro m hm
    have h_abel : (∑ p ∈ Finset.filter Nat.Prime (Finset.range (m + 1)), ((p : ℝ) ^ (-a))) - 2 ^ (-a) - 3 ^ (-a) ≤ m ^ (-a) * (Nat.primeCounting m : ℝ) - 3 ^ (-a) * (Nat.primeCounting 3 : ℝ) + a * ∫ t in (3 : ℝ)..m, (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (-a - 1) := by
      have h_abel : ∀ {n m : ℕ}, 3 ≤ n → n ≤ m → (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (n + 1) m), ((p : ℝ) ^ (-a))) ≤ m ^ (-a) * (Nat.primeCounting m : ℝ) - n ^ (-a) * (Nat.primeCounting n : ℝ) + a * ∫ t in (n : ℝ)..m, (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (-a - 1) := by
        intros n m hn hm
        have h_abel : (∑ p ∈ Finset.Icc (n + 1) m, (if Nat.Prime p then ((p : ℝ) ^ (-a)) else 0)) ≤ m ^ (-a) * (∑ k ∈ Finset.Icc 0 m, (if Nat.Prime k then 1 else 0)) - n ^ (-a) * (∑ k ∈ Finset.Icc 0 n, (if Nat.Prime k then 1 else 0)) + a * ∫ t in (n : ℝ)..m, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if Nat.Prime k then 1 else 0)) * t ^ (-a - 1) := by
          have := @sum_mul_eq_sub_sub_integral_mul';
          specialize @this ℝ _ ( fun k => if Nat.Prime k then 1 else 0 ) ( fun x => x ^ ( -a ) ) n m hm;
          convert this _ _ |> le_of_eq using 1;
          · erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, mul_comm ];
            refine' Finset.sum_bij ( fun x hx => x + ( n + 1 ) ) _ _ _ _ <;> norm_num;
            · exact fun x hx => ⟨ by linarith, by omega ⟩;
            · exact fun b hb₁ hb₂ => ⟨ b - ( n + 1 ), by omega, by omega ⟩;
          · rw [ intervalIntegral.integral_of_le ( by norm_cast ) ];
            rw [ show ( fun t : ℝ => deriv ( fun x : ℝ => x ^ ( -a ) ) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, if Nat.Prime k then 1 else 0 ) = fun t : ℝ => -a * t ^ ( -a - 1 ) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, if Nat.Prime k then 1 else 0 from funext fun x => ?_ ];
            · norm_num [ mul_assoc, mul_comm, mul_left_comm, ← MeasureTheory.integral_const_mul ];
              rw [ MeasureTheory.integral_neg ] ; ring;
            · by_cases hx : x = 0 <;> simp +decide [ hx   ];
          · exact fun x hx => DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) ( by linarith [ hx.1, show ( n : ℝ ) ≥ 3 by norm_cast ] );
          · refine' ContinuousOn.integrableOn_Icc _;
            refine' ContinuousOn.congr _ _;
            use fun x => -a * x ^ (-a - 1);
            · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul continuousAt_const ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 3 by norm_cast ] );
            · intro x hx; norm_num [ show x ≠ 0 by linarith [ hx.1, show ( n : ℝ ) ≥ 3 by norm_cast ] ] ;
        simp_all +decide [ Finset.sum_ite, Nat.primeCounting ];
        convert h_abel using 3 <;> norm_num [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
        · exact Or.inl ( by rw [ Finset.range_eq_Ico ] ; rfl );
        · exact Or.inl ( by rw [ Finset.range_eq_Ico ] ; rfl );
        · exact intervalIntegral.integral_congr fun x hx => by rw [ Finset.range_eq_Ico ] ; rfl;
      have h_split : (∑ p ∈ Finset.filter Nat.Prime (Finset.range (m + 1)), ((p : ℝ) ^ (-a))) = (∑ p ∈ Finset.filter Nat.Prime (Finset.range 4), ((p : ℝ) ^ (-a))) + (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 4 m), ((p : ℝ) ^ (-a))) := by
        erw [ Finset.sum_filter, Finset.sum_filter, Finset.sum_filter ];
        erw [ Finset.sum_range_add_sum_Ico _ ( by linarith ) ];
      have := @h_abel 3 m ( by norm_num ) hm; norm_num [ Finset.sum_filter, Finset.sum_range_succ ] at * ; linarith;
    norm_num [ Nat.primeCounting ] at *;
    norm_num [ Nat.primeCounting' ] at *;
    norm_num [ Nat.count_succ ] at *;
    linarith [ show ( 3 : ℝ ) ^ ( -a ) ≥ 0 by positivity ];
  -- Apply the crude bound to the integral term.
  have h_integral_bound : ∀ m : ℕ, (3 ≤ m → (∫ t in (3 : ℝ)..m, (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (-a - 1)) ≤ C * (∫ t in (3 : ℝ)..m, t ^ (-a) / Real.log t)) := by
    intros m hm
    have h_integral_bound : ∀ t ∈ Set.Icc (3 : ℝ) m, (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (-a - 1) ≤ C * t ^ (-a) / Real.log t := by
      intro t ht; convert mul_le_mul_of_nonneg_right ( hC t ht.1 ) ( Real.rpow_nonneg ( by linarith [ ht.1 ] : 0 ≤ t ) ( -a - 1 ) ) using 1 ; ring_nf;
      rw [ show -a = -1 - a + 1 by ring, Real.rpow_add_one ( by linarith [ ht.1 ] ) ] ; ring;
    rw [ intervalIntegral.integral_of_le ( by norm_cast ), intervalIntegral.integral_of_le ( by norm_cast ) ];
    rw [ ← MeasureTheory.integral_const_mul ];
    refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using mul_nonneg ( Nat.cast_nonneg _ ) ( Real.rpow_nonneg ( by linarith [ hx.1 ] ) _ );
    · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.mul continuousAt_const <| ContinuousAt.div ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hx.1 ] ) ( Real.continuousAt_log <| by linarith [ hx.1 ] ) <| ne_of_gt <| Real.log_pos <| by linarith [ hx.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by simpa only [ mul_div_assoc ] using h_integral_bound x <| Set.Ioc_subset_Icc_self hx;
  -- Split the integral at sqrt m.
  have h_integral_split : ∀ m : ℕ, (3 ≤ m → (∫ t in (3 : ℝ)..m, t ^ (-a) / Real.log t) ≤ (∫ t in (3 : ℝ)..Real.sqrt m, t ^ (-a) / Real.log t) + (∫ t in (Real.sqrt m)..m, t ^ (-a) / Real.log t)) := by
    intro m hm; rw [ intervalIntegral.integral_add_adjacent_intervals ] ; all_goals apply_rules [ ContinuousOn.intervalIntegrable ] ;; all_goals exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.sqrt_nonneg m, Real.sq_sqrt <| Nat.cast_nonneg m, ( by norm_cast : ( 3 :ℝ ) ≤ m ) ] ) ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.sqrt_nonneg m, Real.sq_sqrt <| Nat.cast_nonneg m, ( by norm_cast : ( 3 :ℝ ) ≤ m ) ] ) <| ne_of_gt <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.sqrt_nonneg m, Real.sq_sqrt <| Nat.cast_nonneg m, ( by norm_cast : ( 3 :ℝ ) ≤ m ) ] ;
  -- Bound the first integral by a constant.
  have h_integral_first_bound : ∃ D1 : ℝ, 0 < D1 ∧ ∀ᶠ m : ℕ in atTop, (∫ t in (3 : ℝ)..Real.sqrt m, t ^ (-a) / Real.log t) ≤ D1 * m ^ ((1 - a) / 2) := by
    -- Bound the first integral by a constant using the fact that $t^{-a} / \log t$ is bounded on $[3, \sqrt{m}]$.
    have h_integral_first_bound : ∃ D1 : ℝ, 0 < D1 ∧ ∀ᶠ m : ℕ in atTop, (∫ t in (3 : ℝ)..Real.sqrt m, t ^ (-a) / Real.log t) ≤ D1 * (∫ t in (3 : ℝ)..Real.sqrt m, t ^ (-a)) := by
      refine' ⟨ 1 / Real.log 3, _, _ ⟩ <;> norm_num;
      · positivity;
      · refine' ⟨ 9, fun n hn => _ ⟩ ; rw [ ← intervalIntegral.integral_const_mul ] ; refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
        · exact Real.le_sqrt_of_sq_le ( by norm_cast );
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, ( by norm_cast : ( 9 :ℝ ) ≤ n ) ] ) ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, ( by norm_cast : ( 9 :ℝ ) ≤ n ) ] ) <| ne_of_gt <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, ( by norm_cast : ( 9 :ℝ ) ≤ n ) ] ;
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul continuousAt_const ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> nlinarith [ Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, ( by norm_cast : ( 9 :ℝ ) ≤ n ) ] );
        · exact fun x hx₁ hx₂ => by rw [ inv_mul_eq_div, div_le_div_iff₀ ( Real.log_pos <| by linarith ) ( Real.log_pos <| by linarith ) ] ; nlinarith [ Real.log_le_log ( by linarith ) hx₁, Real.rpow_pos_of_pos ( by linarith : 0 < x ) ( -a ) ] ;
    -- Evaluate the integral $\int_{3}^{\sqrt{m}} t^{-a} \, dt$.
    have h_integral_first_eval : ∀ m : ℕ, (3 ≤ m → (∫ t in (3 : ℝ)..Real.sqrt m, t ^ (-a)) ≤ (Real.sqrt m) ^ (1 - a) / (1 - a)) := by
      intro m hm; rw [ integral_rpow ] <;> norm_num;
      · ring_nf;
        exact sub_le_self _ ( mul_nonneg ( Real.rpow_nonneg ( by norm_num ) _ ) ( inv_nonneg.2 ( by linarith ) ) );
      · exact Or.inl ha1;
    obtain ⟨ D1, hD1_pos, hD1 ⟩ := h_integral_first_bound;
    refine' ⟨ D1 / ( 1 - a ), div_pos hD1_pos ( by linarith ), _ ⟩;
    filter_upwards [ hD1, Filter.eventually_ge_atTop 3 ] with m hm₁ hm₂ using le_trans hm₁ <| by convert mul_le_mul_of_nonneg_left ( h_integral_first_eval m hm₂ ) hD1_pos.le using 1 ; rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
  -- Bound the second integral by a constant.
  have h_integral_second_bound : ∃ D2 : ℝ, 0 < D2 ∧ ∀ᶠ m : ℕ in atTop, (∫ t in (Real.sqrt m)..m, t ^ (-a) / Real.log t) ≤ D2 * m ^ (1 - a) / Real.log m := by
    -- Bound the second integral by a constant using the fact that $1 / \log t \leq 2 / \log m$ for $t \geq \sqrt{m}$.
    have h_integral_second_bound : ∀ m : ℕ, (3 ≤ m → (∫ t in (Real.sqrt m)..m, t ^ (-a) / Real.log t) ≤ (2 / Real.log m) * (∫ t in (Real.sqrt m)..m, t ^ (-a))) := by
      intros m hm
      have h_log_bound : ∀ t ∈ Set.Icc (Real.sqrt m) m, 1 / Real.log t ≤ 2 / Real.log m := by
        intros t ht
        have h_log_bound : Real.log t ≥ Real.log (Real.sqrt m) := by
          exact Real.log_le_log ( by positivity ) ht.1;
        rw [ Real.log_sqrt ( by positivity ) ] at h_log_bound ; rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.log_pos ( show ( m : ℝ ) > 1 by norm_cast; linarith ), Real.log_pos ( show ( t : ℝ ) > 1 by exact lt_of_lt_of_le ( Real.lt_sqrt_of_sq_lt ( by norm_cast; linarith ) ) ht.1 ) ];
      rw [ intervalIntegral.integral_of_le ( Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; nlinarith ⟩ ), intervalIntegral.integral_of_le ( Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; nlinarith ⟩ ) ];
      rw [ ← MeasureTheory.integral_const_mul ];
      refine' MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun x hx => by simpa [ div_eq_mul_inv, mul_comm ] using mul_le_mul_of_nonneg_left ( h_log_bound x <| Set.Ioc_subset_Icc_self hx ) <| Real.rpow_nonneg ( show 0 ≤ x by exact le_trans ( Real.sqrt_nonneg _ ) hx.1.le ) _;
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by nlinarith [ hx.1, Real.sqrt_nonneg m, Real.sq_sqrt <| Nat.cast_nonneg m, ( by norm_cast : ( 3 :ℝ ) ≤ m ) ] ) ( Real.continuousAt_log <| by nlinarith [ hx.1, Real.sqrt_nonneg m, Real.sq_sqrt <| Nat.cast_nonneg m, ( by norm_cast : ( 3 :ℝ ) ≤ m ) ] ) <| ne_of_gt <| Real.log_pos <| by nlinarith [ hx.1, Real.sqrt_nonneg m, Real.sq_sqrt <| Nat.cast_nonneg m, ( by norm_cast : ( 3 :ℝ ) ≤ m ) ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.mul continuousAt_const <| ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by nlinarith [ hx.1, Real.sqrt_nonneg m, Real.sq_sqrt <| Nat.cast_nonneg m, show ( m : ℝ ) ≥ 3 by norm_cast ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
    -- Evaluate the integral $\int_{\sqrt{m}}^{m} t^{-a} \, dt$.
    have h_integral_eval : ∀ m : ℕ, (3 ≤ m → (∫ t in (Real.sqrt m)..m, t ^ (-a)) ≤ (m ^ (1 - a)) / (1 - a)) := by
      intro m hm; rw [ integral_rpow ] <;> norm_num;
      · rw [ show ( -a + 1 : ℝ ) = 1 - a by ring ] ; exact div_le_div_of_nonneg_right ( sub_le_self _ <| by positivity ) <| by linarith;
      · exact Or.inl ha1;
    refine' ⟨ 2 / ( 1 - a ), div_pos zero_lt_two ( by linarith ), _ ⟩;
    filter_upwards [ Filter.eventually_ge_atTop 3 ] with m hm using le_trans ( h_integral_second_bound m hm ) ( by convert mul_le_mul_of_nonneg_left ( h_integral_eval m hm ) ( show 0 ≤ 2 / Real.log m by exact div_nonneg zero_le_two ( Real.log_nonneg ( by norm_cast; linarith ) ) ) using 1 ; ring );
  -- Combine the bounds from the integral estimates.
  obtain ⟨D1, hD1_pos, hD1_bound⟩ := h_integral_first_bound
  obtain ⟨D2, hD2_pos, hD2_bound⟩ := h_integral_second_bound
  have h_combined_bound : ∃ D : ℝ, 0 < D ∧ ∀ᶠ m : ℕ in atTop, (∫ t in (3 : ℝ)..m, (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (-a - 1)) ≤ D * m ^ (1 - a) / Real.log m := by
    -- Combine the bounds from the integral estimates to get the final bound.
    obtain ⟨D3, hD3_pos, hD3_bound⟩ : ∃ D3 : ℝ, 0 < D3 ∧ ∀ᶠ m : ℕ in atTop, D1 * m ^ ((1 - a) / 2) ≤ D3 * m ^ (1 - a) / Real.log m := by
      -- Choose $D3$ such that $D1 * m^{(1 - a) / 2} \leq D3 * m^{1 - a} / \log m$ for sufficiently large $m$.
      have h_choose_D3 : ∃ D3 : ℝ, 0 < D3 ∧ ∀ᶠ m : ℕ in atTop, D1 * Real.log m ≤ D3 * m ^ ((1 - a) / 2) := by
        have h_choose_D3 : Filter.Tendsto (fun m : ℕ => D1 * Real.log m / m ^ ((1 - a) / 2)) Filter.atTop (nhds 0) := by
          -- Let $y = \log m$, therefore the expression becomes $\frac{D1 \cdot y}{e^{((1 - a) / 2) \cdot y}}$.
          suffices h_log : Filter.Tendsto (fun y : ℝ => D1 * y / Real.exp (((1 - a) / 2) * y)) Filter.atTop (nhds 0) by
            have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
            refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm using by rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hm ) ] ; ring_nf );
          -- Let $z = \frac{(1 - a)}{2} y$, therefore the expression becomes $\frac{D1 \cdot \frac{2z}{1 - a}}{e^z}$.
          suffices h_z : Filter.Tendsto (fun z : ℝ => D1 * (2 * z / (1 - a)) / Real.exp z) Filter.atTop (nhds 0) by
            convert h_z.comp ( Filter.tendsto_id.const_mul_atTop ( show 0 < ( 1 - a ) / 2 by linarith ) ) using 2 ; norm_num ; ring_nf;
            grind;
          -- We can factor out $D1$ and use the fact that $\frac{z}{e^z}$ tends to $0$ as $z$ tends to infinity.
          suffices h_factor : Filter.Tendsto (fun z : ℝ => z / Real.exp z) Filter.atTop (nhds 0) by
            convert h_factor.const_mul ( D1 * 2 / ( 1 - a ) ) using 2 <;> ring;
          simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
        exact ⟨ 1, zero_lt_one, by filter_upwards [ h_choose_D3.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 0 ] with m hm₁ hm₂ using by rw [ div_lt_iff₀ ( by positivity ) ] at hm₁; linarith ⟩;
      obtain ⟨ D3, hD3_pos, hD3_bound ⟩ := h_choose_D3; use D3; refine' ⟨ hD3_pos, _ ⟩ ; filter_upwards [ hD3_bound, Filter.eventually_gt_atTop 1 ] with m hm₁ hm₂; rw [ le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr hm₂ ) ] ; convert mul_le_mul_of_nonneg_right hm₁ <| Real.rpow_nonneg ( Nat.cast_nonneg m ) <| ( 1 - a ) / 2 using 1 ; ring;
      rw [ mul_assoc, ← Real.rpow_add ( by positivity ) ] ; ring_nf;
    refine' ⟨ C * ( D3 + D2 ), mul_pos hC0 ( add_pos hD3_pos hD2_pos ), _ ⟩;
    filter_upwards [ hD1_bound, hD2_bound, hD3_bound, Filter.eventually_ge_atTop 3 ] with m hm1 hm2 hm3 hm4 using le_trans ( h_integral_bound m hm4 ) ( by convert mul_le_mul_of_nonneg_left ( h_integral_split m hm4 |> le_trans <| add_le_add ( hm1.trans hm3 ) hm2 ) hC0.le using 1 ; ring ) ;
  obtain ⟨ D, hD_pos, hD_bound ⟩ := h_combined_bound;
  -- Apply the crude bound to the term $m^{-a} \pi(m)$.
  have h_term_bound : ∃ D3 : ℝ, 0 < D3 ∧ ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ (-a) * (Nat.primeCounting m : ℝ) ≤ D3 * m ^ (1 - a) / Real.log m := by
    refine' ⟨ C, hC0, _ ⟩;
    filter_upwards [ Filter.eventually_ge_atTop 3 ] with m hm;
    convert mul_le_mul_of_nonneg_left ( hC m ( mod_cast hm ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg m ) ( -a ) ) using 1 ; ring_nf;
    · norm_num [ Nat.floor_natCast ];
    · rw [ show ( 1 - a : ℝ ) = -a + 1 by ring, Real.rpow_add ] <;> norm_num ; ring ; positivity;
  obtain ⟨ D3, hD3_pos, hD3_bound ⟩ := h_term_bound;
  -- Combine the bounds from the integral estimates and the term bound.
  obtain ⟨D4, hD4_pos, hD4_bound⟩ : ∃ D4 : ℝ, 0 < D4 ∧ ∀ᶠ m : ℕ in atTop, (2 ^ (-a) + 3 ^ (-a)) ≤ D4 * m ^ (1 - a) / Real.log m := by
    have h_term_bound : Filter.Tendsto (fun m : ℕ => (2 ^ (-a) + 3 ^ (-a)) * Real.log m / (m : ℝ) ^ (1 - a)) Filter.atTop (nhds 0) := by
      -- Let $y = \log m$, therefore the expression becomes $\frac{(2^{-a} + 3^{-a}) y}{e^{(1-a)y}}$.
      suffices h_log : Filter.Tendsto (fun y : ℝ => (2 ^ (-a) + 3 ^ (-a)) * y / Real.exp ((1 - a) * y)) Filter.atTop (nhds 0) by
        have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm using by rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hm ) ] ; ring_nf );
      -- Let $z = (1 - a) y$, therefore the expression becomes $\frac{(2^{-a} + 3^{-a}) z}{e^z}$.
      suffices h_z : Filter.Tendsto (fun z : ℝ => (2 ^ (-a) + 3 ^ (-a)) * z / Real.exp z) Filter.atTop (nhds 0) by
        have := h_z.comp ( Filter.tendsto_id.const_mul_atTop ( by linarith : 0 < ( 1 - a ) ) );
        convert this.div_const ( 1 - a ) using 2 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( sub_pos.mpr ha1 ) ];
      simpa [ Real.exp_neg, mul_div_assoc ] using tendsto_const_nhds.mul ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
    have := h_term_bound.eventually ( gt_mem_nhds zero_lt_one );
    exact ⟨ 1, zero_lt_one, by filter_upwards [ this, Filter.eventually_gt_atTop 1 ] with m hm₁ hm₂ using by rw [ le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr hm₂ ) ] ; rw [ div_lt_iff₀ ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| pos_of_gt hm₂ ) _ ) ] at hm₁; linarith ⟩;
  use D4 + D3 + a * D;
  refine' ⟨ by positivity, _ ⟩;
  filter_upwards [ hD4_bound, hD3_bound, hD_bound, Filter.eventually_ge_atTop 3 ] with m hm1 hm2 hm3 hm4 using le_trans ( h_abel m hm4 ) ( by convert add_le_add_three hm1 hm2 ( mul_le_mul_of_nonneg_left hm3 ha0.le ) using 1 ; ring )

/--
Fix an integer `r ≥ 3`, put `y = n^{1/r}`, `M = y / log n`, `S = M²`,
`β = (r-2)/(r-1)`. There is a constant `C_r > 0` such that for every fixed
`δ ∈ (0,1)`, the tail sum `∑_{p ≤ δy} π((n/p)^{1/(r-1)})` is at most
`(C_r δ^β + o(1)) S`.  We in fact establish the stronger eventual pointwise
bound `∑_{p ≤ δy} π((n/p)^{1/(r-1)}) / S ≤ C_r δ^β` for all large `n`, which
implies the corresponding `limsup` form.
-/
theorem prime_pair_tail (r : ℕ) (hr : 3 ≤ r) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ᶠ n : ℕ in atTop,
          (∑ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ + 1)).filter Nat.Prime,
              (Nat.primeCounting ⌊((n : ℝ) / p) ^ ((1 : ℝ) / (r - 1))⌋₊ : ℝ)) /
            ((n : ℝ) ^ ((1 : ℝ) / r) / log n) ^ 2
          ≤ Cr * δ ^ (((r : ℝ) - 2) / ((r : ℝ) - 1)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * x / log x := by
    convert pi_crude_from_three;
  obtain ⟨D, hD⟩ : ∃ D : ℝ, 0 < D ∧ ∀ᶠ m : ℕ in atTop, ∑ p ∈ (Finset.range (m + 1)).filter Nat.Prime, (p : ℝ) ^ (-(1 / (r - 1) : ℝ)) ≤ D * (m : ℝ) ^ (1 - (1 / (r - 1) : ℝ)) / log m := by
    have := @prime_rpow_neg_sum_eventually_le;
    exact this ( show 0 < ( 1 : ℝ ) / ( r - 1 ) by exact one_div_pos.mpr ( by norm_num; linarith ) ) ( show ( 1 : ℝ ) / ( r - 1 ) < 1 by rw [ div_lt_iff₀ ] <;> linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) hC.1 hC.2;
  -- For each fixed δ, put m_n=floor(δ*n^(1/r)). The weighted estimate holds eventually after composition because m_n→∞.
  have h_weighted_estimate : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ᶠ n : ℕ in atTop, ∑ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ + 1)).filter Nat.Prime, (p : ℝ) ^ (-(1 / (r - 1) : ℝ)) ≤ D * (δ * (n : ℝ) ^ ((1 : ℝ) / r)) ^ (1 - (1 / (r - 1) : ℝ)) / (log n / (2 * r)) := by
    intro δ hδ_pos hδ_lt_1
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ ≥ 3 := by
      have h_floor : Filter.Tendsto (fun n : ℕ => δ * (n : ℝ) ^ ((1 : ℝ) / r)) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop hδ_pos ( tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      exact Filter.eventually_atTop.mp ( h_floor.eventually_ge_atTop 3 ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn => Nat.le_floor <| hN n hn ⟩;
    have h_weighted_estimate : ∀ᶠ n : ℕ in atTop, ∑ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ + 1)).filter Nat.Prime, (p : ℝ) ^ (-(1 / (r - 1) : ℝ)) ≤ D * (⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ : ℝ) ^ (1 - (1 / (r - 1) : ℝ)) / (log ⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊) := by
      have h_weighted_estimate : Filter.Tendsto (fun n : ℕ => ⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊) Filter.atTop Filter.atTop := by
        exact tendsto_nat_floor_atTop.comp <| Filter.Tendsto.const_mul_atTop hδ_pos <| tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop;
      exact hD.2.filter_mono h_weighted_estimate;
    have h_log_bound : ∀ᶠ n : ℕ in atTop, log ⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ ≥ log n / (2 * r) := by
      have h_log_bound : ∀ᶠ n : ℕ in atTop, ⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ ≥ (n : ℝ) ^ ((1 : ℝ) / (2 * r)) := by
        have h_log_bound : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ) ^ ((1 : ℝ) / r) ≥ 2 * (n : ℝ) ^ ((1 : ℝ) / (2 * r)) := by
          have h_log_bound : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ) ^ ((1 : ℝ) / r - (1 : ℝ) / (2 * r)) ≥ 2 := by
            have h_log_bound : Filter.Tendsto (fun n : ℕ => δ * (n : ℝ) ^ ((1 : ℝ) / r - (1 : ℝ) / (2 * r))) Filter.atTop Filter.atTop := by
              exact Filter.Tendsto.const_mul_atTop hδ_pos ( tendsto_rpow_atTop ( by nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast, one_div_mul_cancel ( by positivity : ( r : ℝ ) ≠ 0 ), one_div_mul_cancel ( by positivity : ( 2 * r : ℝ ) ≠ 0 ) ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
            exact h_log_bound.eventually_ge_atTop 2;
          filter_upwards [ h_log_bound, Filter.eventually_gt_atTop 0 ] with n hn hn' using by rw [ show ( 1 / ( r : ℝ ) ) = ( 1 / ( r : ℝ ) - 1 / ( 2 * r : ℝ ) ) + 1 / ( 2 * r : ℝ ) by ring ] ; rw [ Real.rpow_add ( by positivity ) ] ; nlinarith [ Real.rpow_pos_of_pos ( by positivity : 0 < ( n : ℝ ) ) ( 1 / ( 2 * r : ℝ ) ) ] ;
        filter_upwards [ h_log_bound, Filter.eventually_gt_atTop 0 ] with n hn hn' using le_trans ( by linarith [ show ( n : ℝ ) ^ ( 1 / ( 2 * r : ℝ ) ) ≥ 1 by exact Real.one_le_rpow ( mod_cast hn' ) ( by positivity ) ] ) ( Nat.sub_one_lt_floor _ |> le_of_lt );
      filter_upwards [ h_log_bound, Filter.eventually_gt_atTop 1 ] with n hn hn' using le_trans ( by rw [ Real.log_rpow ( by positivity ) ] ; ring_nf; norm_num ) ( Real.log_le_log ( by positivity ) hn );
    filter_upwards [ h_weighted_estimate, h_log_bound, Filter.eventually_gt_atTop N ] with n hn hn' hn'';
    refine le_trans hn ?_;
    gcongr;
    · exact mul_nonneg hD.1.le ( Real.rpow_nonneg ( mul_nonneg hδ_pos.le ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) _ );
    · exact div_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith [ show n > 1 from lt_of_le_of_ne ( by linarith ) ( Ne.symm <| by rintro rfl; exact absurd ( hN 1 <| by linarith ) <| by norm_num [ show ⌊δ⌋₊ = 0 from Nat.floor_eq_zero.mpr <| by linarith ] ) ] ) ) ) ( by positivity );
    · linarith;
    · exact sub_nonneg_of_le ( div_le_self zero_le_one ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] ) );
    · exact Nat.floor_le ( by positivity );
  -- Bound m_n^b/log m_n by a constant times (δ*n^(1/r))^b/log n: floor bound handles power, and eventually log(m_n) ≥ log n/(2r) since δ fixed positive.
  have h_bound : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ᶠ n : ℕ in atTop, (∑ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ + 1)).filter Nat.Prime, (Nat.primeCounting ⌊((n : ℝ) / p) ^ ((1 : ℝ) / (r - 1))⌋₊ : ℝ)) ≤ (C * r / log n) * (n ^ ((1 : ℝ) / (r - 1)) * (D * (δ * (n : ℝ) ^ ((1 : ℝ) / r)) ^ (1 - (1 / (r - 1) : ℝ)) / (log n / (2 * r)))) := by
    intro δ hδ0 hδ1
    have h_summand_bound : ∀ᶠ n : ℕ in atTop, ∀ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ + 1)).filter Nat.Prime, (Nat.primeCounting ⌊((n : ℝ) / p) ^ ((1 : ℝ) / (r - 1))⌋₊ : ℝ) ≤ (C * r / log n) * ((n : ℝ) / p) ^ ((1 : ℝ) / (r - 1)) := by
      convert prime_pair_summand_eventually r hr δ C hδ0 hδ1 hC.2 using 1;
      exact funext fun n => by congr! 2; ring_nf;
    filter_upwards [ h_summand_bound, h_weighted_estimate δ hδ0 hδ1 ] with n hn hn';
    refine le_trans ( Finset.sum_le_sum hn ) ?_;
    convert mul_le_mul_of_nonneg_left hn' ( show 0 ≤ C * r / Real.log n * ( n : ℝ ) ^ ( 1 / ( r - 1 : ℝ ) ) by exact mul_nonneg ( div_nonneg ( mul_nonneg hC.1.le ( Nat.cast_nonneg _ ) ) ( Real.log_natCast_nonneg _ ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) using 1;
    · rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Real.div_rpow ( by positivity ) ( by positivity ) ] ; rw [ Real.rpow_neg ( by positivity ) ] ; ring;
    · ring;
  -- Use `prime_pair_rpow_identity` to simplify the expression.
  have h_simplify : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ᶠ n : ℕ in atTop, (∑ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ + 1)).filter Nat.Prime, (Nat.primeCounting ⌊((n : ℝ) / p) ^ ((1 : ℝ) / (r - 1))⌋₊ : ℝ)) ≤ (C * r * D * 2 * r) * δ ^ ((r - 2) / (r - 1) : ℝ) * (n ^ ((1 : ℝ) / r) / log n) ^ 2 := by
    intro δ hδ_pos hδ_lt_1
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (∑ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ + 1)).filter Nat.Prime, (Nat.primeCounting ⌊((n : ℝ) / p) ^ ((1 : ℝ) / (r - 1))⌋₊ : ℝ)) ≤ (C * r / log n) * (n ^ ((1 : ℝ) / (r - 1)) * (D * (δ * (n : ℝ) ^ ((1 : ℝ) / r)) ^ (1 - (1 / (r - 1) : ℝ)) / (log n / (2 * r)))) := by
      exact Filter.eventually_atTop.mp ( h_bound δ hδ_pos hδ_lt_1 );
    filter_upwards [ Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 1 ] with n hn hn';
    convert hN n hn using 1;
    rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
    field_simp;
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
    rw [ show ( r : ℝ ) * ( -1 + r : ℝ ) ⁻¹ - ( -1 + r : ℝ ) ⁻¹ * 2 = 1 - ( -1 + r : ℝ ) ⁻¹ by nlinarith [ mul_inv_cancel₀ ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] : ( -1 + r : ℝ ) ≠ 0 ) ] ] ; ring_nf;
    rw [ show ( -1 + r : ℝ ) ⁻¹ = ( r - 1 : ℝ ) ⁻¹ by ring ] ; rw [ show ( r : ℝ ) ⁻¹ * 2 = ( r - 1 : ℝ ) ⁻¹ + ( - ( ( r - 1 : ℝ ) ⁻¹ * ( r : ℝ ) ⁻¹ ) + ( r : ℝ ) ⁻¹ ) by nlinarith [ inv_pos.mpr ( by positivity : 0 < ( r : ℝ ) ), inv_pos.mpr ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] : 0 < ( r - 1 : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( r : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by linarith [ show ( r : ℝ ) ≥ 3 by norm_cast ] : ( r - 1 : ℝ ) ≠ 0 ) ] ] ; rw [ Real.rpow_add ( by positivity ) ] ; ring;
  refine ⟨ C * r * D * 2 * r, ?_, ?_ ⟩
  · exact mul_pos ( mul_pos ( mul_pos ( mul_pos hC.1 ( by positivity ) ) hD.1 ) ( by positivity ) ) ( by positivity )
  · intro δ hδ_pos hδ_lt_1
    filter_upwards [ h_simplify δ hδ_pos hδ_lt_1, Filter.eventually_gt_atTop 1 ] with n hn hn' using by rw [ div_le_iff₀ ( sq_pos_of_pos <| div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| pos_of_gt hn' ) _ ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn' ) ] ; linarith

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Elementary concentration inequalities -/

/-- Finite union bound. -/
theorem union_bound [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι) (E : ι → Set Ω) :
    μ.real (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, μ.real (E i) :=
  measureReal_biUnion_finset_le s E

/--
Exponential moment for a sum of independent Bernoulli variables:
`E e^{tX} ≤ exp(μ(e^t - 1))` where `μ = E X`.
-/
theorem mgf_bernoulli_sum [IsProbabilityMeasure μ] {N : ℕ} (ξ : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ μ)
    (hber : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1) (t : ℝ) :
    mgf (∑ i, ξ i) μ t ≤ Real.exp ((∫ ω, (∑ i, ξ i) ω ∂μ) * (Real.exp t - 1)) := by
  have h_mgf_sum : mgf (∑ i, ξ i) μ t = ∏ i, mgf (ξ i) μ t := by
    convert ProbabilityTheory.iIndepFun.mgf_sum hindep hmeas Finset.univ using 1;
  -- For each $i$, since $\xi_i$ is a Bernoulli variable, we have $mgf(\xi_i) \leq \exp((e^t - 1) \cdot \mathbb{E}[\xi_i])$.
  have h_mgf_bernoulli : ∀ i, mgf (ξ i) μ t ≤ Real.exp ((Real.exp t - 1) * (∫ ω, (ξ i) ω ∂μ)) := by
    intro i
    have h_mgf_bernoulli_i : mgf (ξ i) μ t = ∫ ω, (1 + (Real.exp t - 1) * (ξ i) ω) ∂μ := by
      exact congr_arg _ ( funext fun ω => by cases hber i ω <;> simp +decide [ * ] );
    rw [ h_mgf_bernoulli_i, MeasureTheory.integral_add, MeasureTheory.integral_const_mul ] <;> norm_num;
    · linarith [ Real.add_one_le_exp ( ( Real.exp t - 1 ) * ∫ ω, ξ i ω ∂μ ) ];
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      exacts [ fun _ => 1, MeasureTheory.integrable_const _, ( hmeas i |> Measurable.aestronglyMeasurable ), Filter.Eventually.of_forall fun ω => by cases hber i ω <;> simp +decide [ * ] ];
  convert Finset.prod_le_prod ?_ fun i _ => h_mgf_bernoulli i <;> simp +decide [ *, mul_comm   ];
  · rw [ ← Real.exp_sum, ← Finset.sum_mul _ _ _, MeasureTheory.integral_finset_sum ];
    · ring_nf;
    · intro i _; exact MeasureTheory.Integrable.mono' ( MeasureTheory.integrable_const 1 ) ( by measurability ) ( by filter_upwards [ ] using fun ω => by cases hber i ω <;> simp +decide [ * ] ) ;
  · exact fun i => MeasureTheory.integral_nonneg fun ω => Real.exp_nonneg _

/--
Lower-tail Chernoff bound.
-/
theorem chernoff_lower [IsProbabilityMeasure μ] {N : ℕ} (ξ : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ μ)
    (hber : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | (∑ i, ξ i) ω ≤ (1 - δ) * (∫ ω, (∑ i, ξ i) ω ∂μ)}
      ≤ Real.exp (-(δ ^ 2 * (∫ ω, (∑ i, ξ i) ω ∂μ)) / 2) := by
  by_contra h_contra';
  have h_exp : Integrable (fun ω => Real.exp ((Real.log (1 - δ)) * (∑ i, ξ i) ω)) μ := by
    refine' MeasureTheory.Integrable.mono' ( MeasureTheory.integrable_const ( Real.exp ( |Real.log ( 1 - δ )| * N ) ) ) _ _;
    · exact Measurable.aestronglyMeasurable ( by measurability );
    · simp +zetaDelta at *;
      filter_upwards [ ] with ω using by cases abs_cases ( Real.log ( 1 - δ ) ) <;> nlinarith [ show ( ∑ i : Fin N, ξ i ω ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => by cases hber ‹_› ω <;> linarith, show ( ∑ i : Fin N, ξ i ω ) ≤ N by exact le_trans ( Finset.sum_le_sum fun _ _ => show ξ _ _ ≤ 1 by cases hber ‹_› ω <;> linarith ) ( by norm_num ) ] ;
  have h_measure_bound : μ.real {ω | (∑ i, ξ i) ω ≤ (1 - δ) * ∫ ω, (∑ i, ξ i) ω ∂μ} ≤ Real.exp (-Real.log (1 - δ) * (1 - δ) * (∫ ω, (∑ i, ξ i) ω ∂μ)) * mgf (∑ i, ξ i) μ (Real.log (1 - δ)) := by
    convert ProbabilityTheory.measure_le_le_exp_mul_mgf ( ( 1 - δ ) * ∫ ω, ( ∑ i, ξ i ) ω ∂μ ) ( Real.log_nonpos ( by linarith ) ( by linarith ) ) h_exp using 1;
    ring_nf;
  have h_mgf_bound : mgf (∑ i, ξ i) μ (Real.log (1 - δ)) ≤ Real.exp ((∫ ω, (∑ i, ξ i) ω ∂μ) * (-δ)) := by
    convert mgf_bernoulli_sum ξ hmeas hindep hber ( Real.log ( 1 - δ ) ) using 1 ; norm_num [ Real.exp_log ( by linarith : 0 < 1 - δ ) ];
  refine h_contra' <| h_measure_bound.trans <| le_trans ( mul_le_mul_of_nonneg_left h_mgf_bound <| by positivity ) ?_;
  rw [ ← Real.exp_add ] ; ring_nf ; norm_num;
  have h_log_bound : ∀ δ : ℝ, 0 < δ ∧ δ < 1 → δ + (1 - δ) * Real.log (1 - δ) ≥ δ^2 / 2 := by
    intros δ hδ
    have h_deriv_nonneg : ∀ x ∈ Set.Ioo 0 1, deriv (fun x => x + (1 - x) * Real.log (1 - x) - x^2 / 2) x ≥ 0 := by
      intro x hx; norm_num [ sub_mul, mul_sub, hx.1.ne', hx.2.ne', Real.differentiableAt_log, show ( 1 - x ) ≠ 0 from by linarith [ hx.1, hx.2 ] ] ; ring_nf; norm_num;
      have h_deriv : deriv (fun x => x - x * Real.log (1 - x) + -(x ^ 2 * (1 / 2)) + Real.log (1 - x)) x = -Real.log (1 - x) - x := by
        convert HasDerivAt.deriv ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.sub ( hasDerivAt_id x ) ( HasDerivAt.mul ( hasDerivAt_id x ) ( HasDerivAt.log ( hasDerivAt_id x |> HasDerivAt.const_sub 1 ) ( by linarith [ hx.1, hx.2 ] : ( 1 - x ) ≠ 0 ) ) ) ) ( HasDerivAt.neg ( HasDerivAt.mul ( hasDerivAt_pow 2 x ) ( hasDerivAt_const _ _ ) ) ) ) ( HasDerivAt.log ( hasDerivAt_id x |> HasDerivAt.const_sub 1 ) ( by linarith [ hx.1, hx.2 ] : ( 1 - x ) ≠ 0 ) ) ) using 1 ; ring_nf;
        grind;
      linarith [ Real.log_le_sub_one_of_pos ( by linarith [ hx.1, hx.2 ] : 0 < 1 - x ) ];
    have := exists_deriv_eq_slope ( f := fun x => x + ( 1 - x ) * Real.log ( 1 - x ) - x ^ 2 / 2 ) hδ.1; norm_num at *;
    contrapose! this;
    exact ⟨ ContinuousOn.sub ( ContinuousOn.add continuousOn_id <| ContinuousOn.mul ( continuousOn_const.sub continuousOn_id ) <| ContinuousOn.log ( continuousOn_const.sub continuousOn_id ) fun x hx => by linarith [ hx.1, hx.2 ] ) <| ContinuousOn.div_const ( continuousOn_pow 2 ) _, fun x hx => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.sub ( DifferentiableAt.add differentiableAt_id <| DifferentiableAt.mul ( differentiableAt_id.const_sub _ ) <| DifferentiableAt.log ( differentiableAt_id.const_sub _ ) <| by linarith [ hx.1, hx.2 ] ) <| by norm_num, fun c hc => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_deriv_nonneg c hc.1 <| by linarith ] ⟩;
  nlinarith [ h_log_bound δ ⟨ hδ0, hδ1 ⟩, show 0 ≤ ∫ ω, ∑ c, ξ c ω ∂μ from MeasureTheory.integral_nonneg fun ω => Finset.sum_nonneg fun _ _ => by cases hber ‹_› ω <;> linarith ]

/--
A fixed-gap upper-tail bound.
-/
theorem chernoff_gap [IsProbabilityMeasure μ] {N : ℕ} (ξ : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ μ)
    (hber : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1) {ρ D : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hD : 0 < D)
    (hμ : (∫ ω, (∑ i, ξ i) ω ∂μ) ≤ (1 - 3 * ρ / 4) * D) :
    μ.real {ω | (1 - ρ / 2) * D ≤ (∑ i, ξ i) ω} ≤ Real.exp (-(ρ ^ 2 * D) / 32) := by
  -- Let $X = \sum_{i=1}^N \xi_i$, $m = \int X \, d\mu$, and $a = (1 - \rho / 2)D$.
  set X : Ω → ℝ := fun ω => (∑ i, (ξ i ω))
  set m := ∫ ω, X ω ∂μ
  set a := (1 - ρ / 2) * D;
  by_cases hm : m = 0;
  · -- Since $m = 0$, we have $X = 0$ almost everywhere.
    have hX_zero : ∀ᵐ ω ∂μ, X ω = 0 := by
      rwa [ MeasureTheory.integral_eq_zero_iff_of_nonneg_ae ] at hm;
      · exact Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun i _ => by cases hber i ω <;> linarith;
      · refine' MeasureTheory.integrable_finset_sum _ fun i _ => _;
        refine' MeasureTheory.Integrable.mono' _ _ _;
        exacts [ fun _ => 1, MeasureTheory.integrable_const _, ( hmeas i |> Measurable.aestronglyMeasurable ), Filter.Eventually.of_forall fun ω => by cases hber i ω <;> simp +decide [ * ] ];
    rw [ MeasureTheory.measureReal_def ];
    rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr ] <;> norm_num;
    · positivity;
    · filter_upwards [ hX_zero ] with ω hω using by rw [ show ∑ i, ξ i ω = 0 from hω ] ; exact mul_pos ( by linarith ) hD;
  · -- Apply the Chernoff bound with $t = \log(a/m)$.
    have h_chernoff : μ.real {ω | a ≤ X ω} ≤ Real.exp (-Real.log (a / m) * a + m * (a / m - 1)) := by
      have h_chernoff : μ.real {ω | a ≤ X ω} ≤ Real.exp (-Real.log (a / m) * a) * mgf X μ (Real.log (a / m)) := by
        apply ProbabilityTheory.measure_ge_le_exp_mul_mgf;
        · refine' Real.log_nonneg _;
          rw [ le_div_iff₀ ] <;> norm_num +zetaDelta at *;
          · nlinarith;
          · exact lt_of_le_of_ne ( MeasureTheory.integral_nonneg fun ω => Finset.sum_nonneg fun _ _ => by cases hber ‹_› ω <;> linarith ) ( Ne.symm hm );
        · refine' MeasureTheory.Integrable.mono' ( MeasureTheory.integrable_const ( Real.exp ( |Real.log ( a / m )| * N ) ) ) _ _;
          · exact Measurable.aestronglyMeasurable ( by measurability );
          · simp +zetaDelta at *;
            filter_upwards [ ] with ω using mul_le_mul ( le_abs_self _ ) ( le_trans ( Finset.sum_le_sum fun _ _ => show ξ _ _ ≤ 1 by cases hber ‹_› ω <;> linarith ) ( by norm_num ) ) ( Finset.sum_nonneg fun _ _ => show 0 ≤ ξ _ _ by cases hber ‹_› ω <;> linarith ) ( abs_nonneg _ );
      have h_mgf : mgf X μ (Real.log (a / m)) ≤ Real.exp (m * (Real.exp (Real.log (a / m)) - 1)) := by
        convert mgf_bernoulli_sum ξ hmeas hindep hber ( Real.log ( a / m ) ) using 1;
        · simp +decide [ X, mgf ];
        · aesop;
      convert h_chernoff.trans ( mul_le_mul_of_nonneg_left h_mgf <| Real.exp_nonneg _ ) using 1 ; rw [ Real.exp_add ] ; rw [ Real.exp_log <| div_pos ?_ <| lt_of_le_of_ne ( MeasureTheory.integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => by cases hber ‹_› ‹_› <;> linarith ) <| Ne.symm hm ];
      exact mul_pos ( by linarith ) hD;
    -- Simplify the exponent in the Chernoff bound.
    have h_exp_simplified : -Real.log (a / m) * a + m * (a / m - 1) ≤ -(a - m) ^ 2 / (2 * a) := by
      have h_log_bound : ∀ q : ℝ, 0 < q ∧ q < 1 → Real.log q ≤ -(1 - q) - (1 - q)^2 / 2 := by
        intros q hq
        have h_log_bound : ∀ u : ℝ, 0 ≤ u ∧ u < 1 → Real.log (1 - u) ≤ -u - u^2 / 2 := by
          intros u hu
          have h_deriv : ∀ u : ℝ, 0 ≤ u ∧ u < 1 → deriv (fun u => Real.log (1 - u) + u + u^2 / 2) u ≤ 0 := by
            intros u hu
            have h_deriv : deriv (fun u => Real.log (1 - u) + u + u^2 / 2) u = -1 / (1 - u) + 1 + u := by
              convert HasDerivAt.deriv ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.log ( hasDerivAt_id' u |> HasDerivAt.const_sub 1 ) ( by linarith : ( 1 - u ) ≠ 0 ) ) ( hasDerivAt_id' u ) ) ( HasDerivAt.div_const ( hasDerivAt_pow 2 u ) _ ) ) using 1 ; ring;
            rw [ h_deriv, div_add_one, div_add', div_le_iff₀ ] <;> nlinarith;
          by_contra h_contra;
          have := exists_deriv_eq_slope ( f := fun u => Real.log ( 1 - u ) + u + u ^ 2 / 2 ) ( show u > 0 from hu.1.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at this;
          exact absurd ( this ( by exact ContinuousOn.add ( ContinuousOn.add ( ContinuousOn.log ( continuousOn_const.sub continuousOn_id ) fun x hx => by linarith [ hx.1, hx.2 ] ) continuousOn_id ) ( ContinuousOn.div_const ( continuousOn_pow 2 ) _ ) ) ( by exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( DifferentiableAt.add ( DifferentiableAt.log ( differentiableAt_id.const_sub _ ) ( by linarith [ hx.1, hx.2 ] ) ) differentiableAt_id ) ( by norm_num ) ) ) ) ( by rintro ⟨ c, ⟨ hc0, hcu ⟩, hcd ⟩ ; nlinarith [ h_deriv c ⟨ by linarith, by linarith ⟩, mul_div_cancel₀ ( Real.log ( 1 - u ) + u + u ^ 2 / 2 ) ( by linarith : u ≠ 0 ) ] );
        simpa using h_log_bound ( 1 - q ) ⟨ by linarith, by linarith ⟩;
      have h_q_bound : 0 < m / a ∧ m / a < 1 := by
        have h_q_bound : 0 < m ∧ m < a := by
          simp +zetaDelta at *;
          exact ⟨ lt_of_le_of_ne ( MeasureTheory.integral_nonneg fun ω => Finset.sum_nonneg fun _ _ => by cases hber ‹_› ω <;> linarith ) ( Ne.symm hm ), by nlinarith ⟩;
        exact ⟨ div_pos h_q_bound.1 ( by nlinarith ), by rw [ div_lt_iff₀ ] <;> nlinarith ⟩;
      have := h_log_bound ( m / a ) h_q_bound;
      rw [ Real.log_div ] at this <;> norm_num at *;
      · rw [ Real.log_div ] <;> norm_num at *;
        · field_simp at *;
          rw [ le_div_iff₀ ( mul_pos ( by linarith ) hD ) ];
          rw [ div_eq_mul_inv ] at this;
          rw [ show a = ( 1 - ρ / 2 ) * D by rfl ] at *;
          nlinarith [ mul_inv_cancel_left₀ ( by nlinarith : ( 1 - ρ / 2 ) * D ≠ 0 ) m, mul_inv_cancel₀ ( by nlinarith : ( 1 - ρ / 2 ) * D ≠ 0 ) ];
        · exact mul_ne_zero ( by linarith ) hD.ne';
        · exact hm;
      · exact hm;
      · exact mul_ne_zero ( by linarith ) hD.ne';
    -- Substitute the simplified exponent back into the Chernoff bound.
    have h_final_bound : μ.real {ω | a ≤ X ω} ≤ Real.exp (-(ρ ^ 2 * D) / 32) := by
      have h_exp_bound : -(a - m) ^ 2 / (2 * a) ≤ -(ρ ^ 2 * D) / 32 := by
        rw [ div_le_iff₀ ] <;> norm_num +zetaDelta at *;
        · nlinarith [ mul_pos hρ0 hD, mul_le_mul_of_nonneg_left hμ hD.le, mul_le_mul_of_nonneg_left hμ hρ0.le, show 0 ≤ ∫ ω, ∑ i, ξ i ω ∂μ from MeasureTheory.integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => by cases hber ‹_› ‹_› <;> linarith ];
        · nlinarith
      exact h_chernoff.trans ( Real.exp_le_exp.mpr ( h_exp_simplified.trans h_exp_bound ) );
    convert h_final_bound using 1;
    simp +zetaDelta at *

/--
Large upper tail.
-/
theorem chernoff_large [IsProbabilityMeasure μ] {N : ℕ} (ξ : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ μ)
    (hber : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1) {s : ℝ}
    (hs : (∫ ω, (∑ i, ξ i) ω ∂μ) ≤ s) (hs0 : 0 < s) :
    μ.real {ω | s ≤ (∑ i, ξ i) ω}
      ≤ (Real.exp 1 * (∫ ω, (∑ i, ξ i) ω ∂μ) / s) ^ s := by
  by_cases hm : ∫ ω, ( ∑ i : Fin N, ξ i ) ω ∂μ = 0 <;> simp_all +decide [ mul_div_assoc ];
  · rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg ( fun _ => Finset.sum_nonneg fun _ _ => by cases hber _ _ <;> linarith ) ] at hm;
    · simp_all +decide [ Filter.EventuallyEq  ];
      rw [ MeasureTheory.measureReal_def, MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr ] <;> simp_all +decide [ ne_of_gt hs0 ];
      filter_upwards [ hm ] with ω hω using by linarith;
    · refine' MeasureTheory.integrable_finset_sum _ _;
      intro i _; exact ( MeasureTheory.Integrable.mono' ( MeasureTheory.integrable_const 1 ) ( by measurability ) ( by filter_upwards [ ] using fun ω => by cases hber i ω <;> simp +decide [ * ] ) ) ;
  · -- Apply the Chernoff bound with $t = \log(s/m)$.
    have h_chernoff : μ.real {ω | s ≤ (∑ i, ξ i) ω} ≤ Real.exp (-s * Real.log (s / (∫ ω, (∑ i, ξ i) ω ∂μ)) + (∫ ω, (∑ i, ξ i) ω ∂μ) * (s / (∫ ω, (∑ i, ξ i) ω ∂μ) - 1)) := by
      have h_mgf : mgf (∑ i, ξ i) μ (Real.log (s / (∫ ω, (∑ i, ξ i) ω ∂μ))) ≤ Real.exp ((∫ ω, (∑ i, ξ i) ω ∂μ) * (Real.exp (Real.log (s / (∫ ω, (∑ i, ξ i) ω ∂μ))) - 1)) := by
        apply_rules [ mgf_bernoulli_sum ];
      have h_chernoff : μ.real {ω | s ≤ (∑ i, ξ i) ω} ≤ Real.exp (-s * Real.log (s / (∫ ω, (∑ i, ξ i) ω ∂μ))) * mgf (∑ i, ξ i) μ (Real.log (s / (∫ ω, (∑ i, ξ i) ω ∂μ))) := by
        convert ProbabilityTheory.measure_ge_le_exp_mul_mgf _ _ _ using 1;
        any_goals exact Real.log ( s / ∫ ω, ∑ i, ξ i ω ∂μ );
        · simp +decide [ mul_comm, mgf ];
        · infer_instance;
        · exact Real.log_nonneg ( by rw [ le_div_iff₀ ( lt_of_le_of_ne ( MeasureTheory.integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => by cases hber ‹_› ‹_› <;> linarith ) ( Ne.symm hm ) ) ] ; linarith );
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun ω => Real.exp ( Real.log ( s / ∫ ω, ∑ i, ξ i ω ∂μ ) * N );
          · fun_prop;
          · exact Measurable.aestronglyMeasurable ( by measurability );
          · simp +zetaDelta at *;
            filter_upwards [ ] with ω using mul_le_mul_of_nonneg_left ( le_trans ( Finset.sum_le_sum fun _ _ => show ξ _ _ ≤ 1 by cases hber ‹_› ω <;> linarith ) ( by norm_num ) ) ( Real.log_nonneg <| by rw [ le_div_iff₀ <| lt_of_le_of_ne ( MeasureTheory.integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => by cases hber ‹_› ‹_› <;> linarith ) ( Ne.symm hm ) ] ; linarith );
      refine le_trans h_chernoff ?_;
      rw [ Real.exp_add ] ; gcongr ; simp_all +decide ;
      rwa [ Real.exp_log ( div_pos hs0 ( lt_of_le_of_ne ( MeasureTheory.integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => by cases hber ‹_› ‹_› <;> linarith ) ( Ne.symm hm ) ) ) ] at h_mgf;
    convert h_chernoff.trans _ using 1;
    · simp +decide [ Finset.sum_apply ];
    · rw [ Real.rpow_def_of_pos ( mul_pos ( Real.exp_pos _ ) ( div_pos ( lt_of_le_of_ne ( MeasureTheory.integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => by cases hber ‹_› ‹_› <;> linarith ) ( Ne.symm hm ) ) hs0 ) ) ] ; ring_nf ; norm_num [ hm, hs0.ne' ];
      norm_num [ Real.log_mul, Real.exp_ne_zero, hs0.ne', hm ] ; ring_nf;
      linarith [ show 0 ≤ ∫ ω, ∑ c, ξ c ω ∂μ from MeasureTheory.integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => by cases hber ‹_› ‹_› <;> linarith ]

end

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Chernoff bounds for families indexed by a finite type -/

/-- Reindexing an independent family along the canonical equivalence with `Fin`
preserves independence. -/
lemma iIndepFun_equivFin {ι : Type*} [Fintype ι] (ξ : ι → Ω → ℝ) (hindep : iIndepFun ξ μ) :
    iIndepFun (fun i : Fin (Fintype.card ι) => ξ ((Fintype.equivFin ι).symm i)) μ := by
  set e := Fintype.equivFin ι
  intro s f hf
  have h := hindep (s.map ⟨e.symm, e.symm.injective⟩) (f := fun i => f (e i)) (by
    intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    simp [hf j hj])
  refine h.congr ?_
  filter_upwards [ ] with a
  have heq_inter : (⋂ i ∈ Finset.map ⟨e.symm, e.symm.injective⟩ s, (fun i => f (e i)) i)
      = ⋂ j ∈ s, f j := by
    ext x
    simp only [Set.mem_iInter, Finset.mem_map]
    constructor
    · intro hx j hj
      have := hx (e.symm j) ⟨j, hj, rfl⟩
      simp at this
      exact this
    · intro hx i hi
      rcases hi with ⟨j, hj, hji⟩
      rw [← hji]
      convert hx j hj using 1
      exact congrArg f (Equiv.apply_symm_apply e j)
  have heq_prod : ∏ i ∈ Finset.map ⟨e.symm, e.symm.injective⟩ s,
      ((Kernel.const Unit μ) a) (f (e i)) = ∏ j ∈ s, ((Kernel.const Unit μ) a) (f j) := by
    rw [Finset.prod_map]
    simp
  rw [heq_inter, heq_prod]

/-- Lower-tail Chernoff bound for a family indexed by a finite type. -/
theorem chernoff_lower_fintype [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (ξ : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ μ)
    (hber : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | (∑ i, ξ i ω) ≤ (1 - δ) * (∫ ω, (∑ i, ξ i ω) ∂μ)}
      ≤ Real.exp (-(δ ^ 2 * (∫ ω, (∑ i, ξ i ω) ∂μ)) / 2) := by
  let e := Fintype.equivFin ι
  let ξ' : Fin (Fintype.card ι) → Ω → ℝ := fun i ω => ξ (e.symm i) ω
  have hmeas' : ∀ i, Measurable (ξ' i) := fun i => hmeas _
  have hindep' : iIndepFun ξ' μ := iIndepFun_equivFin ξ hindep
  have hber' : ∀ i ω, ξ' i ω = 0 ∨ ξ' i ω = 1 := fun i ω => hber _ ω
  have heq_sum : ∀ ω, (∑ i : ι, ξ i) ω = (∑ i : Fin (Fintype.card ι), ξ' i) ω := by
    intro ω
    simp_rw [Finset.sum_apply]
    exact (Fintype.sum_equiv e.symm (fun j : Fin _ => ξ' j ω) (fun i : ι => ξ i ω) (fun _ => rfl)).symm
  have heq_sum' : (∫ ω, (∑ i : ι, ξ i) ω ∂μ) = (∫ ω, (∑ i : Fin (Fintype.card ι), ξ' i) ω ∂μ) := by
    congr 1; ext ω; exact heq_sum ω
  have hchernoff := chernoff_lower ξ' hmeas' hindep' hber' hδ0 hδ1
  convert hchernoff using 2
  · congr 1; ext ω; simp_rw [← Finset.sum_apply, heq_sum ω, heq_sum']
  · simp_rw [← Finset.sum_apply]
    rw [heq_sum']

/-- Fixed-gap upper-tail bound for a family indexed by a finite type. -/
theorem chernoff_gap_fintype [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (ξ : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ μ)
    (hber : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1) {ρ D : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hD : 0 < D) (hμ : (∫ ω, (∑ i, ξ i ω) ∂μ) ≤ (1 - 3 * ρ / 4) * D) :
    μ.real {ω | (1 - ρ / 2) * D ≤ (∑ i, ξ i ω)} ≤ Real.exp (-(ρ ^ 2 * D) / 32) := by
  let e := Fintype.equivFin ι
  let ξ' : Fin (Fintype.card ι) → Ω → ℝ := fun i ω => ξ (e.symm i) ω
  have hmeas' : ∀ i, Measurable (ξ' i) := fun i => hmeas _
  have hindep' : iIndepFun ξ' μ := by
    intro s f hf
    have h := hindep (s.map ⟨e.symm, e.symm.injective⟩) (f := fun i => f (e i)) (by
      intro i hi
      rw [Finset.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      simp [hf j hj])
    refine h.congr ?_
    filter_upwards [ ] with a
    have heq_inter : (⋂ i ∈ Finset.map ⟨e.symm, e.symm.injective⟩ s, (fun i => f (e i)) i) = ⋂ j ∈ s, f j := by
      ext x
      simp only [Set.mem_iInter, Finset.mem_map]
      constructor
      · intro hx j hj
        have := hx (e.symm j) ⟨j, hj, rfl⟩
        simp at this
        exact this
      · intro hx i hi
        rcases hi with ⟨j, hj, hji⟩
        rw [← hji]
        convert hx j hj using 1
        exact congrArg f (Equiv.apply_symm_apply e j)
    have heq_prod : ∏ i ∈ Finset.map ⟨e.symm, e.symm.injective⟩ s, ((Kernel.const Unit μ) a) (f (e i)) = ∏ j ∈ s, ((Kernel.const Unit μ) a) (f j) := by
      rw [Finset.prod_map]
      simp
    rw [heq_inter, heq_prod]
  have hber' : ∀ i ω, ξ' i ω = 0 ∨ ξ' i ω = 1 := fun i ω => hber _ ω
  have heq_sum : ∀ ω, (∑ i : ι, ξ i) ω = (∑ i : Fin (Fintype.card ι), ξ' i) ω := by
    intro ω
    simp_rw [Finset.sum_apply]
    exact (Fintype.sum_equiv e.symm (fun j : Fin _ => ξ' j ω) (fun i : ι => ξ i ω) (fun _ => rfl)).symm
  have heq_sum' : (∫ ω, (∑ i : ι, ξ i) ω ∂μ) = (∫ ω, (∑ i : Fin (Fintype.card ι), ξ' i) ω ∂μ) := by
    congr 1; ext ω; exact heq_sum ω
  have heq₁ : (∫ ω, (∑ i : ι, ξ i) ω ∂μ) = (∫ ω, ∑ i, ξ i ω ∂μ) := by
    simp only [← Finset.sum_apply]
  have hμ' : (∫ ω, (∑ i : ι, ξ i) ω ∂μ) ≤ (1 - 3 * ρ / 4) * D := by rw [heq₁]; exact hμ
  have hμ_bound : (∫ ω, (∑ i, ξ' i) ω ∂μ) ≤ (1 - 3 * ρ / 4) * D := by rw [← heq_sum']; exact hμ'
  have hset_eq : ∀ ω, (1 - ρ / 2) * D ≤ (∑ i, ξ i) ω ↔ (1 - ρ / 2) * D ≤ (∑ i, ξ' i) ω := by
    intro ω; rw [heq_sum]
  have hchernoff := chernoff_gap ξ' hmeas' hindep' hber' hρ0 hρ1 hD hμ_bound
  convert hchernoff using 2
  simp [Set.ext_iff]; intro x
  have h1 : ∑ i, ξ i x = (∑ i, ξ i) x := by simp [Finset.sum_apply]
  have h2 : ∑ c, ξ' c x = (∑ i, ξ' i) x := by simp [Finset.sum_apply]
  rw [h1, h2]; rw [heq_sum x]

/-- Large upper-tail bound for a family indexed by a finite type. -/
theorem chernoff_large_fintype [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (ξ : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ μ)
    (hber : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1) {s : ℝ}
    (hs : (∫ ω, (∑ i, ξ i ω) ∂μ) ≤ s) (hs0 : 0 < s) :
    μ.real {ω | s ≤ (∑ i, ξ i ω)}
      ≤ (Real.exp 1 * (∫ ω, (∑ i, ξ i ω) ∂μ) / s) ^ s := by
  let e := Fintype.equivFin ι
  let ξ' : Fin (Fintype.card ι) → Ω → ℝ := fun i ω => ξ (e.symm i) ω
  have hmeas' : ∀ i, Measurable (ξ' i) := fun i => hmeas _
  have hindep' : iIndepFun ξ' μ := by
    intro s f hf
    have h := hindep (s.map ⟨e.symm, e.symm.injective⟩) (f := fun i => f (e i)) (by
      intro i hi
      rw [Finset.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      simp [hf j hj])
    refine h.congr ?_
    filter_upwards [ ] with a
    have heq_inter : (⋂ i ∈ Finset.map ⟨e.symm, e.symm.injective⟩ s, (fun i => f (e i)) i) = ⋂ j ∈ s, f j := by
      ext x
      simp only [Set.mem_iInter, Finset.mem_map]
      constructor
      · intro hx j hj
        have := hx (e.symm j) ⟨j, hj, rfl⟩
        simp at this
        exact this
      · intro hx i hi
        rcases hi with ⟨j, hj, hji⟩
        rw [← hji]
        convert hx j hj using 1
        exact congrArg f (Equiv.apply_symm_apply e j)
    have heq_prod : ∏ i ∈ Finset.map ⟨e.symm, e.symm.injective⟩ s, ((Kernel.const Unit μ) a) (f (e i)) = ∏ j ∈ s, ((Kernel.const Unit μ) a) (f j) := by
      rw [Finset.prod_map]
      simp
    rw [heq_inter, heq_prod]
  have hber' : ∀ i ω, ξ' i ω = 0 ∨ ξ' i ω = 1 := fun i ω => hber _ ω
  have heq_sum : ∀ ω, (∑ i : ι, ξ i) ω = (∑ i : Fin (Fintype.card ι), ξ' i) ω := by
    intro ω
    simp_rw [Finset.sum_apply]
    exact (Fintype.sum_equiv e.symm (fun j : Fin _ => ξ' j ω) (fun i : ι => ξ i ω) (fun _ => rfl)).symm
  have heq_sum' : (∫ ω, (∑ i : ι, ξ i) ω ∂μ) = (∫ ω, (∑ i : Fin (Fintype.card ι), ξ' i) ω ∂μ) := by
    congr 1; ext ω; exact heq_sum ω
  have hs' : (∫ ω, (∑ i, ξ i) ω ∂μ) ≤ s := by simp_all [Finset.sum_apply]
  have hchernoff := chernoff_large ξ' hmeas' hindep' hber' (by rw [← heq_sum']; simp_all [Finset.sum_apply]) hs0
  convert hchernoff using 2
  · ext ω; simp [← Finset.sum_apply, heq_sum ω]
  · simp_rw [← Finset.sum_apply]; rw [heq_sum']

/-- If the total failure probability of finitely many events is less than one,
some outcome avoids all of them. -/
lemma exists_avoiding_of_sum_lt_one [IsProbabilityMeasure μ] {ι : Type*}
    (s : Finset ι) (E : ι → Set Ω) (h : ∑ i ∈ s, μ.real (E i) < 1) :
    ∃ ω : Ω, ∀ i ∈ s, ω ∉ E i := by
  have h_union : μ.real (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, μ.real (E i) := union_bound s E
  have h_union_lt : μ.real (⋃ i ∈ s, E i) < 1 := lt_of_le_of_lt h_union h
  have h_univ : μ.real Set.univ = 1 := by simp [MeasureTheory.Measure.real]
  by_contra h_empty
  push_neg at h_empty
  have h_union_univ : (⋃ i ∈ s, E i) = Set.univ := by
    ext ω
    simp only [Set.mem_univ, iff_true]
    by_contra h_not_in
    obtain ⟨i, hi, hωi⟩ := h_empty ω
    exact h_not_in (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hωi⟩⟩)
  rw [h_union_univ] at h_union_lt
  rw [h_univ] at h_union_lt
  linarith

/-- Four finite families of bad events with total probability less than one are
simultaneously avoidable. -/
lemma exists_avoiding_four_families [IsProbabilityMeasure μ]
    {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₄]
    (E₁ : ι₁ → Set Ω) (E₂ : ι₂ → Set Ω) (E₃ : ι₃ → Set Ω) (E₄ : ι₄ → Set Ω)
    {a₁ a₂ a₃ a₄ : ℝ}
    (h₁ : ∀ i, μ.real (E₁ i) ≤ a₁) (h₂ : ∀ i, μ.real (E₂ i) ≤ a₂)
    (h₃ : ∀ i, μ.real (E₃ i) ≤ a₃) (h₄ : ∀ i, μ.real (E₄ i) ≤ a₄)
    (h : (Fintype.card ι₁ : ℝ) * a₁ + (Fintype.card ι₂ : ℝ) * a₂ +
      (Fintype.card ι₃ : ℝ) * a₃ + (Fintype.card ι₄ : ℝ) * a₄ < 1) :
    ∃ ω : Ω, (∀ i, ω ∉ E₁ i) ∧ (∀ i, ω ∉ E₂ i) ∧ (∀ i, ω ∉ E₃ i) ∧ (∀ i, ω ∉ E₄ i) := by
  -- Define combined index type and events
  let ι : Type := ι₁ ⊕ ι₂ ⊕ ι₃ ⊕ ι₄
  let E₁' : ι₁ → Set Ω := E₁
  let E₂' : ι₂ → Set Ω := E₂
  let E₃' : ι₃ → Set Ω := E₃
  let E₄' : ι₄ → Set Ω := E₄
  let E : ι → Set Ω := Sum.rec E₁' (Sum.rec E₂' (Sum.rec E₃' E₄'))
  -- The finset is the universal set
  let s : Finset ι := Finset.univ
  -- Helper equalities
  have hE₁ : ∀ i, E (Sum.inl i) = E₁ i := fun i => rfl
  have hE₂ : ∀ i, E (Sum.inr (Sum.inl i)) = E₂ i := fun i => rfl
  have hE₃ : ∀ i, E (Sum.inr (Sum.inr (Sum.inl i))) = E₃ i := fun i => rfl
  have hE₄ : ∀ i, E (Sum.inr (Sum.inr (Sum.inr i))) = E₄ i := fun i => rfl
  -- Bound on each part
  have h₁sum : ∑ i : ι₁, μ.real (E₁ i) ≤ (Fintype.card ι₁ : ℝ) * a₁ := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => μ.real (E₁ i)) a₁ (fun i _ => h₁ i)
    simp at this
    exact this
  have h₂sum : ∑ i : ι₂, μ.real (E₂ i) ≤ (Fintype.card ι₂ : ℝ) * a₂ := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => μ.real (E₂ i)) a₂ (fun i _ => h₂ i)
    simp at this
    exact this
  have h₃sum : ∑ i : ι₃, μ.real (E₃ i) ≤ (Fintype.card ι₃ : ℝ) * a₃ := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => μ.real (E₃ i)) a₃ (fun i _ => h₃ i)
    simp at this
    exact this
  have h₄sum : ∑ i : ι₄, μ.real (E₄ i) ≤ (Fintype.card ι₄ : ℝ) * a₄ := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => μ.real (E₄ i)) a₄ (fun i _ => h₄ i)
    simp at this
    exact this
  -- Bound on the total sum
  have hsum : ∑ i ∈ s, μ.real (E i) < 1 := by
    have hle : ∑ i ∈ s, μ.real (E i) ≤
        ∑ i : ι₁, μ.real (E₁ i) + ∑ i : ι₂, μ.real (E₂ i) +
        ∑ i : ι₃, μ.real (E₃ i) + ∑ i : ι₄, μ.real (E₄ i) := by
      simp only [s]
      rw [Fintype.sum_sum_type (f := fun x => μ.real (E x))]
      rw [Fintype.sum_sum_type (f := fun x => μ.real (E (Sum.inr x)))]
      rw [Fintype.sum_sum_type (f := fun x => μ.real (E (Sum.inr (Sum.inr x))))]
      simp only [hE₁, hE₂, hE₃, hE₄]
      ring_nf
      exact le_refl _
    linarith
  obtain ⟨ω, hω⟩ := exists_avoiding_of_sum_lt_one s E hsum
  refine ⟨ω, ?_, ?_, ?_, ?_⟩
  · intro i hi; exact hω (Sum.inl i) (Finset.mem_univ _) (hE₁ i ▸ hi)
  · intro i hi; exact hω (Sum.inr (Sum.inl i)) (Finset.mem_univ _) (hE₂ i ▸ hi)
  · intro i hi; exact hω (Sum.inr (Sum.inr (Sum.inl i))) (Finset.mem_univ _) (hE₃ i ▸ hi)
  · intro i hi; exact hω (Sum.inr (Sum.inr (Sum.inr i))) (Finset.mem_univ _) (hE₄ i ▸ hi)

end

/-! ## Independent coin flips indexed by a finite type -/

/-- The Bernoulli measure on `Bool` with success probability `p`. -/
noncomputable def bern (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

lemma bern_isProbabilityMeasure {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (bern p) := by
  constructor
  unfold bern
  simp [Measure.add_apply, Measure.smul_apply]
  rw [← ENNReal.ofReal_add (by linarith : 0 ≤ p) (by linarith : 0 ≤ 1 - p)]
  simp

lemma integral_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (f : Bool → ℝ) :
    ∫ b, f b ∂(bern p) = p * f true + (1 - p) * f false := by
  unfold bern
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure,
      MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
  · simp [ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (sub_nonneg.mpr h1)]
  · refine ⟨?_, ?_⟩
    · exact measurable_of_finite _ |> Measurable.aestronglyMeasurable
    · rw [MeasureTheory.HasFiniteIntegral, MeasureTheory.lintegral_smul_measure,
          MeasureTheory.lintegral_dirac]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top
  · refine ⟨?_, ?_⟩
    · exact measurable_of_finite _ |> Measurable.aestronglyMeasurable
    · rw [MeasureTheory.HasFiniteIntegral, MeasureTheory.lintegral_smul_measure,
          MeasureTheory.lintegral_dirac]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top

/-- The product of Bernoulli measures: independent coin flips indexed by `I`. -/
noncomputable def coins (I : Type) [Fintype I] (p : I → ℝ) : Measure (I → Bool) :=
  Measure.pi (fun i => bern (p i))

lemma coins_isProbabilityMeasure {I : Type} [Fintype I] {p : I → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : IsProbabilityMeasure (coins I p) := by
  constructor
  show (Measure.pi fun i => bern (p i)) Set.univ = 1
  have h : Set.univ = Set.pi Set.univ (fun _ : I => Set.univ : I → Set Bool) := by ext; simp
  haveI : ∀ i, MeasureTheory.SigmaFinite (bern (p i)) := by
    intro i
    have := bern_isProbabilityMeasure (hp i).1 (hp i).2
    infer_instance
  rw [h, Measure.pi_pi]
  have : ∀ i, (bern (p i)) {false, true} = 1 := by
    intro i
    haveI := bern_isProbabilityMeasure (hp i |>.1) (hp i |>.2)
    have : ({false, true} : Set Bool) = Set.univ := by ext x; cases x <;> simp
    rw [this]
    exact MeasureTheory.IsProbabilityMeasure.measure_univ
  simp [this]

/-- The indicator that coin `i` came up heads, restricted to the coins in `S`. -/
noncomputable def coinVar {I : Type} [DecidableEq I] (S : Finset I) (i : I) :
    (I → Bool) → ℝ :=
  fun ω => if i ∈ S ∧ ω i = true then 1 else 0

lemma coinVar_measurable {I : Type} [Fintype I] [DecidableEq I] (S : Finset I) (i : I) :
    Measurable (coinVar S i) := by
  unfold coinVar
  apply Measurable.ite
  · simp only [Set.setOf_and]
    apply MeasurableSet.inter
    · by_cases hi : i ∈ S <;> simp [hi]
    · exact measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  · apply measurable_const
  · apply measurable_const

lemma coinVar_bernoulli {I : Type} [DecidableEq I] (S : Finset I) (i : I)
    (ω : I → Bool) : coinVar S i ω = 0 ∨ coinVar S i ω = 1 := by
  unfold coinVar; split <;> simp

-- Hint: `ProbabilityTheory.iIndepFun_pi` gives independence of coordinatewise
-- functions for a product of probability measures.
lemma coinVar_indep {I : Type} [Fintype I] [DecidableEq I] {p : I → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset I) :
    iIndepFun (coinVar S) (coins I p) := by
  have hpi : ∀ i, IsProbabilityMeasure (bern (p i)) := fun i => bern_isProbabilityMeasure (hp i).1 (hp i).2
  haveI : ∀ i, IsProbabilityMeasure (bern (p i)) := hpi
  have : coins I p = Measure.pi (fun i => bern (p i)) := rfl
  -- coinVar S i = g_i ∘ Pi.eval i where g_i : Bool → ℝ
  -- Define g i : Bool → ℝ
  let g : I → (Bool → ℝ) := fun i b => if i ∈ S ∧ b = true then 1 else 0
  -- Show coinVar S i = g i ∘ (fun ω => ω i)
  have heq : ∀ i, coinVar S i = g i ∘ (fun ω : I → Bool => ω i) := by
    intro i
    ext ω
    simp [coinVar, g]
  -- Show g i is measurable
  have hg : ∀ i, Measurable (g i) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, g]
      apply Measurable.ite
      · exact measurableSet_singleton (true : Bool)
      · exact measurable_const
      · exact measurable_const
    · simp only [hi, g]
      exact measurable_const
  rw [this]
  rw [funext heq]
  apply iIndepFun_pi (fun i => (hg i).aemeasurable)

lemma coinVar_sum {I : Type} [Fintype I] [DecidableEq I] (S : Finset I)
    (ω : I → Bool) :
    (∑ i, coinVar S i ω) = ((S.filter fun i => ω i = true).card : ℝ) := by
  simp [coinVar]
  congr 1
  ext x
  simp

-- Hint: `MeasureTheory.integral_comp_eval` reduces the integral of a
-- coordinatewise function over `Measure.pi` to a one-coordinate integral, and
-- `integral_bern` evaluates the latter.
lemma coinVar_integral {I : Type} [Fintype I] [DecidableEq I] {p : I → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset I) :
    (∫ ω, (∑ i, coinVar S i ω) ∂(coins I p)) = ∑ i ∈ S, p i := by
  rw [MeasureTheory.integral_finset_sum]
  · have key : ∀ i : I, ∫ (a : I → Bool), coinVar S i a ∂coins I p = if i ∈ S then p i else 0 := by
      intro i
      by_cases hi : i ∈ S
      · have hcoin : coinVar S i = fun ω => if ω i = true then (1 : ℝ) else 0 := by
          ext ω; simp [coinVar, hi]
        simp_rw [hcoin]
        simp_rw [coins]
        haveI : IsProbabilityMeasure (coins I p) := coins_isProbabilityMeasure hp
        haveI (j : I) : IsProbabilityMeasure (bern (p j)) := bern_isProbabilityMeasure (hp j).1 (hp j).2
        -- Use integral_comp_eval to reduce to integral over the i-th coordinate
        have h := MeasureTheory.integral_comp_eval (μ := fun j : I => bern (p j)) (i := i)
                  (f := fun b => if b = true then (1 : ℝ) else 0)
                  (by measurability)
        rw [h]
        rw [integral_bern (hp i).1 (hp i).2]
        simp [hi]
      · simp [coinVar, hi]
    simp_rw [key]
    simp []
  · intro i _
    haveI : IsProbabilityMeasure (coins I p) := coins_isProbabilityMeasure hp
    have hbdd : ∀ ω, ‖coinVar S i ω‖ ≤ 1 := by
      intro ω; exact (coinVar_bernoulli S i ω).elim (fun h => by simp [h]) (fun h => by simp [h])
    apply Integrable.mono (integrable_const (1 : ℝ)) (coinVar_measurable S i).aestronglyMeasurable
    filter_upwards with ω
    simpa using hbdd ω

/-- Lower tail for the number of retained coins of a finite set. -/
lemma coin_count_lower_tail {I : Type} [Fintype I] [DecidableEq I] {p : I → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset I) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (coins I p).real
        {ω | ((S.filter fun i => ω i = true).card : ℝ) ≤ (1 - δ) * ∑ i ∈ S, p i}
      ≤ Real.exp (-(δ ^ 2 * ∑ i ∈ S, p i) / 2) := by
  haveI := coins_isProbabilityMeasure hp
  have h_int := coinVar_integral hp S
  have h_sum : ∀ ω : I → Bool, (∑ i, coinVar S i ω) = ((S.filter fun i => ω i = true).card : ℝ) := coinVar_sum S
  have h_int' : ∫ (ω : I → Bool), ((S.filter fun i => ω i = true).card : ℝ) ∂(coins I p) = ∑ i ∈ S, p i := by
    simp_rw [← h_sum]; exact h_int
  have := chernoff_lower_fintype (fun i => coinVar S i) (fun i => coinVar_measurable S i)
    (coinVar_indep hp S) (fun i ω => coinVar_bernoulli S i ω) hδ0 hδ1
  simp only [h_sum] at this
  simp_rw [h_int'] at this
  exact this

/-- Fixed-gap upper tail for the number of retained coins of a finite set. -/
lemma coin_count_gap_tail {I : Type} [Fintype I] [DecidableEq I] {p : I → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset I) {ρ D : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hD : 0 < D)
    (hmean : ∑ i ∈ S, p i ≤ (1 - 3 * ρ / 4) * D) :
    (coins I p).real
        {ω | (1 - ρ / 2) * D ≤ ((S.filter fun i => ω i = true).card : ℝ)}
      ≤ Real.exp (-(ρ ^ 2 * D) / 32) := by
  haveI := coins_isProbabilityMeasure hp
  have h_sum : ∀ ω : I → Bool, (∑ i, coinVar S i ω) = ((S.filter fun i => ω i = true).card : ℝ) :=
    coinVar_sum S
  have h_int' : ∫ (ω : I → Bool), ((S.filter fun i => ω i = true).card : ℝ) ∂(coins I p)
      = ∑ i ∈ S, p i := by
    simp_rw [← h_sum]; exact coinVar_integral hp S
  have hmean' : (∫ (ω : I → Bool), (∑ i, coinVar S i ω) ∂(coins I p)) ≤ (1 - 3 * ρ / 4) * D := by
    simp_rw [h_sum, h_int']; exact hmean
  have := chernoff_gap_fintype (fun i => coinVar S i) (fun i => coinVar_measurable S i)
    (coinVar_indep hp S) (fun i ω => coinVar_bernoulli S i ω) hρ0 hρ1 hD hmean'
  simpa only [h_sum] using this

/-- Large upper tail for the number of retained coins of a finite set. -/
lemma coin_count_large_tail {I : Type} [Fintype I] [DecidableEq I] {p : I → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset I) {s : ℝ}
    (hs : ∑ i ∈ S, p i ≤ s) (hs0 : 0 < s) :
    (coins I p).real
        {ω | s ≤ ((S.filter fun i => ω i = true).card : ℝ)}
      ≤ (Real.exp 1 * (∑ i ∈ S, p i) / s) ^ s := by
  haveI := coins_isProbabilityMeasure hp
  have h_sum : ∀ ω : I → Bool, (∑ i, coinVar S i ω) = ((S.filter fun i => ω i = true).card : ℝ) :=
    coinVar_sum S
  have h_int' : ∫ (ω : I → Bool), ((S.filter fun i => ω i = true).card : ℝ) ∂(coins I p)
      = ∑ i ∈ S, p i := by
    simp_rw [← h_sum]; exact coinVar_integral hp S
  have hmean' : (∫ (ω : I → Bool), (∑ i, coinVar S i ω) ∂(coins I p)) = ∑ i ∈ S, p i := by
    simp_rw [h_sum]; exact h_int'
  have := chernoff_large_fintype (fun i => coinVar S i) (fun i => coinVar_measurable S i)
    (coinVar_indep hp S) (fun i ω => coinVar_bernoulli S i ω) (by rw [hmean']; exact hs) hs0
  rw [hmean'] at this
  simpa only [h_sum] using this

/-! ## Token realization from the matching theorem -/

/-- Counting a predicate over a sigma type of finite fibers. -/
lemma card_filter_sigma {L : Type} [Fintype L] [DecidableEq L] {β : L → Type}
    [∀ t, Fintype (β t)] (P : (Σ t, β t) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = ∑ t, (Finset.univ.filter fun b : β t => P ⟨t, b⟩).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

/-- Counting a predicate over the coercion of a finset to a type. -/
lemma card_filter_subtype {α : Type} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun b : {x // x ∈ s} => p (b : α)).card = (s.filter p).card := by
  rw [← Finset.card_attach (s := s.filter p)]
  apply Finset.card_bij (fun b _ => (⟨b.1, by simp_all [Finset.mem_filter]⟩ :
    {x // x ∈ s.filter p}))
  · intro a ha; simp
  · intro a ha b hb h; simp at h; exact h
  · intro b hb
    have hb1 : b.1 ∈ s.filter p := b.2
    rw [Finset.mem_filter] at hb1
    exact ⟨⟨b.1, hb1.1⟩, by simp [hb1.2], by simp⟩

/-! ### Vertex pairs as the second side of the incidence bipartite graph -/

/-- The two-element subsets of the ground set `Vset`, as a type. -/
abbrev pairSub {α : Type} [DecidableEq α] (Vset : Finset α) : Type :=
  {w : Finset α // w ∈ Vset.powersetCard 2}

/-- The two-element subsets of an edge, as vertex pairs of the ground set. -/
def edgePairs {α : Type} [DecidableEq α] (Vset E : Finset α) : Finset (pairSub Vset) :=
  (E.powersetCard 2).subtype (fun w => w ∈ Vset.powersetCard 2)

lemma mem_edgePairs {α : Type} [DecidableEq α] {Vset E : Finset α}
    (w : pairSub Vset) : w ∈ edgePairs Vset E ↔ (w : Finset α) ⊆ E := by
  simp [edgePairs, Finset.mem_subtype, Finset.mem_powersetCard]
  have hwcard : (w : Finset α).card = 2 := (Finset.mem_powersetCard.mp w.2).2
  simp [hwcard]

lemma card_edgePairs {α : Type} [DecidableEq α] {Vset E : Finset α} (hE : E ⊆ Vset)
    {r : ℕ} (hcard : E.card = r) : (edgePairs Vset E).card = r.choose 2 := by
  simp only [edgePairs]
  have hfilter : ∀ w ∈ E.powersetCard 2, w ∈ Vset.powersetCard 2 := by
    intro w hw
    simp only [Finset.mem_powersetCard] at hw ⊢
    exact ⟨Finset.Subset.trans hw.1 hE, hw.2⟩
  simp [Finset.subtype]
  have heq : {w ∈ E.powersetCard 2 | w ⊆ Vset ∧ w.card = 2} = E.powersetCard 2 :=
    Finset.filter_eq_self.mpr fun w hw => by simp_all [Finset.mem_powersetCard]
  rw [heq, Finset.card_powersetCard, hcard]

/-- Two edges of the ground set sharing no vertex pair meet in at most one
vertex. -/
lemma inter_card_le_one_of_disjoint_edgePairs {α : Type} [DecidableEq α]
    {Vset E E' : Finset α} (hE : E ⊆ Vset)
    (h : Disjoint (edgePairs Vset E) (edgePairs Vset E')) : (E ∩ E').card ≤ 1 := by
  by_contra hcontra
  push_neg at hcontra
  -- There exists a 2-element subset of E ∩ E'
  have h2 : (E ∩ E').powersetCard 2 ≠ ∅ := by
    contrapose! hcontra with hcontra
    have := Finset.card_powersetCard 2 (E ∩ E')
    simp [hcontra] at this
    have := Nat.choose_eq_zero_iff.mp (this.symm)
    omega
  obtain ⟨w, hw⟩ : ∃ w, w ∈ (E ∩ E').powersetCard 2 := Finset.nonempty_of_ne_empty h2
  -- w is a 2-element subset of E ∩ E', so w ⊆ E and w ⊆ E'
  have hw_sub : w ⊆ E ∩ E' := (Finset.mem_powersetCard.mp hw).1
  have hwE : w ⊆ E := Finset.Subset.trans hw_sub Finset.inter_subset_left
  have hwE' : w ⊆ E' := Finset.Subset.trans hw_sub Finset.inter_subset_right
  -- w has 2 elements and w ⊆ Vset
  have hwcard : w.card = 2 := (Finset.mem_powersetCard.mp hw).2
  have hwVset : w ⊆ Vset := Finset.Subset.trans (Finset.Subset.trans hw_sub Finset.inter_subset_left) hE
  have hw_pairSub : w ∈ Vset.powersetCard 2 := by simp [Finset.mem_powersetCard]; exact ⟨hwVset, hwcard⟩
  -- Construct the pairSub element
  let w' : pairSub Vset := ⟨w, hw_pairSub⟩
  -- Show it's in both edgePairs
  have hwa : w' ∈ edgePairs Vset E := by
    rw [mem_edgePairs]
    exact hwE
  have hwa' : w' ∈ edgePairs Vset E' := by
    simp only [edgePairs, Finset.mem_subtype, Finset.mem_powersetCard]
    exact ⟨hwE', hwcard⟩
  exact Finset.disjoint_left.mp h hwa hwa'

/-- For a retained family `G t` of `r`-element edges inside the ground set
   `Vset` attached to every token `t`, with

* every token degree at least `(1 + D^{-1/(20 q₀)}) D`,
* every vertex-pair degree at most `D`,
* every token/vertex-pair codegree at most `(log D)²`, and
* every vertex-pair/vertex-pair codegree at most `(log D)²`,

the Delcourt–Postle theorem provides an edge `f t ∈ G t` for every token such
that distinct tokens receive edges sharing at most one vertex. -/
lemma exists_linear_token_assignment (r : ℕ) (hr : 2 ≤ r) :
    ∃ Dq : ℝ, ∀ D : ℝ, Dq ≤ D → 0 < D →
      ∀ (α : Type) [DecidableEq α] (Vset : Finset α) (L : Type) [Fintype L] [DecidableEq L]
        (G : L → Finset (Finset α)),
        (∀ t : L, ∀ E ∈ G t, E.card = r ∧ E ⊆ Vset) →
        (∀ t : L,
          (1 + D ^ (-(1 : ℝ) / (20 * (1 + r.choose 2)))) * D ≤ ((G t).card : ℝ)) →
        (∀ w ∈ Vset.powersetCard 2,
          (∑ t : L, (((G t).filter fun E => w ⊆ E).card : ℝ)) ≤ D) →
        (∀ (t : L), ∀ w ∈ Vset.powersetCard 2,
          (((G t).filter fun E => w ⊆ E).card : ℝ) ≤ (Real.log D) ^ 2) →
        (∀ w ∈ Vset.powersetCard 2, ∀ w' ∈ Vset.powersetCard 2, w ≠ w' →
          (∑ t : L, (((G t).filter fun E => w ⊆ E ∧ w' ⊆ E).card : ℝ)) ≤
            (Real.log D) ^ 2) →
        ∃ f : L → Finset α, (∀ t, f t ∈ G t) ∧
          ∀ t t' : L, t ≠ t' → ((f t) ∩ (f t')).card ≤ 1 := by
  classical
  have hq2 : 2 ≤ 1 + r.choose 2 := by
    have : 1 ≤ r.choose 2 := Nat.choose_pos hr
    omega
  obtain ⟨Dq, hDq⟩ := DP_empty (1 + r.choose 2) hq2
  refine ⟨Dq, ?_⟩
  intro D hD hD0 α _ Vset L _ _ G hedge hdegL hdegR hcod1 hcod2
  classical
  set Etype := Σ t : L, {E : Finset α // E ∈ G t} with hEtype
  set aV : Etype → L := fun e => e.1 with haV
  set bV : Etype → Finset (pairSub Vset) := fun e => edgePairs Vset (e.2 : Finset α) with hbV
  -- basic counting identities
  have hgen : ∀ (P : L → Finset α → Prop) (_ : ∀ t, DecidablePred (P t)),
      (Finset.univ.filter fun e : Etype => P e.1 (e.2 : Finset α)).card
        = ∑ t : L, ((G t).filter (P t)).card := by
    intro P _
    classical
    rw [card_filter_sigma]
    exact Finset.sum_congr rfl fun t _ => card_filter_subtype (G t) (P t)
  have hcardA : ∀ t : L, (Finset.univ.filter fun e : Etype => aV e = t).card = (G t).card := by
    intro t
    have hg := hgen (fun t' _ => t' = t) (by intro t'; infer_instance)
    rw [haV]
    rw [hg, Finset.sum_eq_single t]
    · simp
    · intro t' _ ht'; simp [ht']
    · intro h; simp at h
  have hcardB : ∀ w : pairSub Vset,
      (Finset.univ.filter fun e : Etype => w ∈ bV e).card
        = ∑ t : L, ((G t).filter fun E => (w : Finset α) ⊆ E).card := by
    intro w
    have hg := hgen (fun _ E => w ∈ edgePairs Vset E) (by intro t'; infer_instance)
    rw [hbV, hg]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine congrArg Finset.card (Finset.filter_congr fun E hE => ?_)
    simp [mem_edgePairs w]
  have hcardAB : ∀ (t : L) (w : pairSub Vset),
      (Finset.univ.filter fun e : Etype => aV e = t ∧ w ∈ bV e).card
        = ((G t).filter fun E => (w : Finset α) ⊆ E).card := by
    intro t w
    have hg := hgen (fun t' E => t' = t ∧ w ∈ edgePairs Vset E) (by intro t'; infer_instance)
    rw [haV, hbV, hg, Finset.sum_eq_single t]
    · refine congrArg Finset.card (Finset.filter_congr fun E hE => ?_)
      simp [mem_edgePairs w]
    · intro t' _ ht'; simp [ht']
    · intro h; simp at h
  have hcardBB : ∀ w w' : pairSub Vset,
      (Finset.univ.filter fun e : Etype => w ∈ bV e ∧ w' ∈ bV e).card
        = ∑ t : L, ((G t).filter fun E => (w : Finset α) ⊆ E ∧ (w' : Finset α) ⊆ E).card := by
    intro w w'
    have hg := hgen (fun _ E => w ∈ edgePairs Vset E ∧ w' ∈ edgePairs Vset E)
      (by intro t'; infer_instance)
    rw [hbV, hg]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine congrArg Finset.card (Finset.filter_congr fun E hE => ?_)
    simp [mem_edgePairs w, mem_edgePairs w']
  have hspec := hDq D hD L (pairSub Vset) Etype aV bV ?_ ?_ ?_ ?_ ?_
  · obtain ⟨M, hMdisj, hMcov⟩ := hspec
    choose e he hev using hMcov
    have hfst : ∀ t, (e t).1 = t := by
      intro t; simpa [haV] using hev t
    have key : ∀ (x : Etype) (t : L), x.1 = t → ((x.2 : Finset α)) ∈ G t := by
      rintro ⟨t', b⟩ t rfl
      exact b.2
    have hmem : ∀ t, ((e t).2 : Finset α) ∈ G t := fun t => key (e t) t (hfst t)
    refine ⟨fun t => ((e t).2 : Finset α), hmem, ?_⟩
    intro t t' htt'
    have hne : e t ≠ e t' := by
      intro h
      apply htt'
      rw [← hev t, ← hev t', h]
    have hdisj := (hMdisj _ (he t) _ (he t') hne).2
    exact inter_card_le_one_of_disjoint_edgePairs (hedge t _ (hmem t)).2 hdisj
  · -- q-boundedness
    intro e
    simp only [hbV]
    rw [card_edgePairs (hedge e.1 _ (e.2).2).2 (hedge e.1 _ (e.2).2).1]
  · -- token/pair codegrees
    intro t w
    rw [hcardAB t w]
    exact hcod1 t (w : Finset α) w.2
  · -- pair/pair codegrees
    intro w w' hww'
    rw [hcardBB w w']
    push_cast
    exact hcod2 (w : Finset α) w.2 (w' : Finset α) w'.2
      (fun h => hww' (Subtype.coe_injective h))
  · -- token degrees
    intro t
    rw [hcardA t]
    have := hdegL t
    have hcast : ((20 : ℝ) * ((1 + r.choose 2 : ℕ) : ℝ)) = 20 * (1 + (r.choose 2 : ℝ)) := by
      push_cast; ring
    rw [hcast]
    exact this
  · -- pair degrees
    intro w
    rw [hcardB w]
    push_cast
    exact hdegR (w : Finset α) w.2

/-- Retain each candidate edge `E ∈ F t` independently with probability `p t`.
  If the expected token degrees equal `D`, the expected vertex-pair degrees are
  at most `(1 - 3ρ/4) D`, all expected codegrees are at most `κ`, and the total
  failure probability is less than one, then some retention is good: token
  degrees exceed `(1 - ρ/4) D`, vertex-pair degrees are below `(1 - ρ/2) D`, and
  all codegrees are below `K`. -/
lemma exists_good_retention (α : Type) [DecidableEq α] (Vset : Finset α)
    (L : Type) [Fintype L] [DecidableEq L]
    (F : L → Finset (Finset α)) (p : L → ℝ) (hp : ∀ t, 0 ≤ p t ∧ p t ≤ 1)
    (D ρ κ K : ℝ) (hD : 0 < D) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hK : 0 < K)
    (hmeanL : ∀ t, ((F t).card : ℝ) * p t = D)
    (hmeanR : ∀ w ∈ Vset.powersetCard 2,
      ∑ t, (((F t).filter fun E => w ⊆ E).card : ℝ) * p t ≤ (1 - 3 * ρ / 4) * D)
    (hmeanC1 : ∀ (t : L), ∀ w ∈ Vset.powersetCard 2,
      (((F t).filter fun E => w ⊆ E).card : ℝ) * p t ≤ κ)
    (hmeanC2 : ∀ w ∈ Vset.powersetCard 2, ∀ w' ∈ Vset.powersetCard 2, w ≠ w' →
      ∑ t, (((F t).filter fun E => w ⊆ E ∧ w' ⊆ E).card : ℝ) * p t ≤ κ)
    (hfail : ((Fintype.card L : ℝ) + ((Vset.powersetCard 2).card : ℝ)) *
          Real.exp (-(ρ ^ 2 * D) / 32) +
        ((Fintype.card L : ℝ) + ((Vset.powersetCard 2).card : ℝ)) ^ 2 *
          (Real.exp 1 * κ / K) ^ K < 1) :
    ∃ G : L → Finset (Finset α), (∀ t, G t ⊆ F t) ∧
      (∀ t, (1 - ρ / 4) * D ≤ ((G t).card : ℝ)) ∧
      (∀ w ∈ Vset.powersetCard 2,
        (∑ t, (((G t).filter fun E => w ⊆ E).card : ℝ)) ≤ (1 - ρ / 2) * D) ∧
      (∀ (t : L), ∀ w ∈ Vset.powersetCard 2,
        (((G t).filter fun E => w ⊆ E).card : ℝ) ≤ K) ∧
      (∀ w ∈ Vset.powersetCard 2, ∀ w' ∈ Vset.powersetCard 2, w ≠ w' →
        (∑ t, (((G t).filter fun E => w ⊆ E ∧ w' ⊆ E).card : ℝ)) ≤ K) := by
  classical
  -- The degenerate cases: if there are no vertex pairs, or no tokens, the
  -- whole family `F` already works.
  have hFcard : ∀ t, (1 - ρ / 4) * D ≤ ((F t).card : ℝ) := by
    intro t
    have h := hmeanL t
    have hpt : 0 < p t := by
      rcases lt_or_eq_of_le (hp t).1 with hpos | h0
      · exact hpos
      · exfalso; rw [← h0] at h; simp at h; linarith
    have hle : ((F t).card : ℝ) * p t ≤ ((F t).card : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (hp t).2 (by positivity)
    rw [h, mul_one] at hle
    nlinarith
  by_cases hpairs : (Vset.powersetCard 2) = ∅
  · refine ⟨F, fun t => Finset.Subset.refl _, hFcard, ?_, ?_, ?_⟩ <;>
      simp [hpairs]
  by_cases hLne : Nonempty L
  swap
  · rw [not_nonempty_iff] at hLne
    refine ⟨F, fun t => Finset.Subset.refl _, hFcard, ?_, ?_, ?_⟩
    · intro w _
      simp [Finset.univ_eq_empty]
      nlinarith
    · intro t; exact (hLne.false t).elim
    · intro w _ w' _ _
      simp [Finset.univ_eq_empty]
      linarith
  -- The main case.
  obtain ⟨w₀, hw₀⟩ := Finset.nonempty_of_ne_empty hpairs
  obtain ⟨t₀⟩ := hLne
  have hκ : 0 ≤ κ := by
    refine le_trans ?_ (hmeanC1 t₀ w₀ hw₀)
    exact mul_nonneg (by positivity) (hp t₀).1
  have hanonneg : (0 : ℝ) ≤ (Real.exp 1 * κ / K) ^ K :=
    Real.rpow_nonneg (by positivity) K
  -- one coin per candidate edge of every token
  let I : Type := Σ t : L, {E : Finset α // E ∈ F t}
  let q : I → ℝ := fun i => p i.1
  have hq' : ∀ i, 0 ≤ q i ∧ q i ≤ 1 := fun i => hp i.1
  haveI : IsProbabilityMeasure (coins I q) := coins_isProbabilityMeasure hq'
  -- expected values of the coin sums
  have hsum : ∀ (S : Finset I) (P : L → Finset α → Prop) (A : L → Finset (Finset α)),
      (∀ i : I, i ∈ S ↔ P i.1 (i.2 : Finset α)) →
      (∀ (t : L) (E : Finset α), E ∈ A t ↔ (E ∈ F t ∧ P t E)) →
      ∑ i ∈ S, q i = ∑ t, ((A t).card : ℝ) * p t := by
    intro S P A hS hA
    have hS' : S = Finset.univ.filter (fun i : I => P i.1 (i.2 : Finset α)) := by
      ext i; simpa using hS i
    have hA' : ∀ t, A t = (F t).filter (P t) := by
      intro t; ext E; simpa using hA t E
    subst hS'
    simp only [hA']
    rw [Finset.sum_filter, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hstep : ∀ b : {E : Finset α // E ∈ F t},
        (if P t (b : Finset α) then q (⟨t, b⟩ : I) else 0)
          = (if P t (b : Finset α) then p t else 0) := fun b => rfl
    simp only [hstep]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      card_filter_subtype (F t) (P t)]
  -- retained families
  let Gof : (I → Bool) → L → Finset (Finset α) := fun ω t =>
    (F t).filter (fun E => ∃ h : E ∈ F t, ω ⟨t, ⟨E, h⟩⟩ = true)
  have hGsub : ∀ (ω : I → Bool) (t : L), Gof ω t ⊆ F t := fun ω t => Finset.filter_subset _ _
  have hcount : ∀ (ω : I → Bool) (S : Finset I) (P : L → Finset α → Prop)
      (A : L → Finset (Finset α)),
      (∀ i : I, i ∈ S ↔ P i.1 (i.2 : Finset α)) →
      (∀ (t : L) (E : Finset α), E ∈ A t ↔ (E ∈ Gof ω t ∧ P t E)) →
      ((S.filter fun i => ω i = true).card : ℝ) = ∑ t, ((A t).card : ℝ) := by
    intro ω S P A hS hA
    have hS' : S = Finset.univ.filter (fun i : I => P i.1 (i.2 : Finset α)) := by
      ext i; simpa using hS i
    have hA' : ∀ t, A t = (Gof ω t).filter (P t) := by
      intro t; ext E; simpa using hA t E
    subst hS'
    simp only [hA']
    rw [Finset.filter_filter,
      card_filter_sigma (fun i : I => P i.1 (i.2 : Finset α) ∧ ω i = true)]
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    have hfil : ((Gof ω t).filter (P t))
        = (F t).filter (fun E => P t E ∧ ∃ h : E ∈ F t, ω ⟨t, ⟨E, h⟩⟩ = true) := by
      simp only [Gof, Finset.filter_filter]
      exact Finset.filter_congr (fun E _ => by tauto)
    rw [hfil, ← card_filter_subtype (F t)
      (fun E => P t E ∧ ∃ h : E ∈ F t, ω ⟨t, ⟨E, h⟩⟩ = true)]
    refine congrArg Finset.card (Finset.filter_congr fun b _ => ?_)
    constructor
    · rintro ⟨hP, hω⟩; exact ⟨hP, b.2, by simpa using hω⟩
    · rintro ⟨hP, h, hω⟩; exact ⟨hP, by simpa using hω⟩
  -- the four families of bad events
  let P2 : Type := {w : Finset α // w ∈ Vset.powersetCard 2}
  let E1 : L → Set (I → Bool) := fun t =>
    {ω | (((Finset.univ.filter (fun i : I => i.1 = t)).filter fun i => ω i = true).card : ℝ)
        ≤ (1 - ρ / 4) * ∑ i ∈ Finset.univ.filter (fun i : I => i.1 = t), q i}
  let E2 : P2 → Set (I → Bool) := fun w =>
    {ω | (1 - ρ / 2) * D ≤
      (((Finset.univ.filter (fun i : I => (w : Finset α) ⊆ (i.2 : Finset α))).filter
        fun i => ω i = true).card : ℝ)}
  let E3 : L × P2 → Set (I → Bool) := fun tw =>
    {ω | K ≤ (((Finset.univ.filter
      (fun i : I => i.1 = tw.1 ∧ (tw.2 : Finset α) ⊆ (i.2 : Finset α))).filter
        fun i => ω i = true).card : ℝ)}
  let E4 : {ww : P2 × P2 // (ww.1 : Finset α) ≠ (ww.2 : Finset α)} → Set (I → Bool) := fun ww =>
    {ω | K ≤ (((Finset.univ.filter (fun i : I =>
        ((ww : P2 × P2).1 : Finset α) ⊆ (i.2 : Finset α) ∧
        ((ww : P2 × P2).2 : Finset α) ⊆ (i.2 : Finset α))).filter
        fun i => ω i = true).card : ℝ)}
  -- the mean of the token coin set
  have hmean1 : ∀ t : L, ∑ i ∈ Finset.univ.filter (fun i : I => i.1 = t), q i = D := by
    intro t
    rw [hsum _ (fun t' _ => t' = t) (fun t' => if t' = t then F t' else ∅)
      (by intro i; simp) (by intro t' E; by_cases h : t' = t <;> simp [h])]
    rw [Finset.sum_eq_single t]
    · simpa using hmeanL t
    · intro t' _ ht'; simp [ht']
    · intro h; simp at h
  -- tail bounds for the four families
  have hb1 : ∀ t : L, (coins I q).real (E1 t) ≤ Real.exp (-(ρ ^ 2 * D) / 32) := by
    intro t
    have h := coin_count_lower_tail hq' (Finset.univ.filter (fun i : I => i.1 = t))
      (δ := ρ / 4) (by linarith) (by linarith)
    refine le_trans h ?_
    rw [hmean1 t]
    apply le_of_eq
    congr 1
    ring
  have hb2 : ∀ w : P2, (coins I q).real (E2 w) ≤ Real.exp (-(ρ ^ 2 * D) / 32) := by
    intro w
    refine coin_count_gap_tail hq' _ hρ0 hρ1 hD ?_
    rw [hsum _ (fun _ E => (w : Finset α) ⊆ E) (fun t => (F t).filter fun E => (w : Finset α) ⊆ E)
      (by intro i; simp) (by intro t E; simp)]
    exact hmeanR (w : Finset α) w.2
  have hlarge : ∀ S : Finset I, ∑ i ∈ S, q i ≤ κ →
      (coins I q).real {ω | K ≤ ((S.filter fun i => ω i = true).card : ℝ)}
        ≤ (Real.exp 1 * κ / K) ^ K := by
    intro S hS
    have hnn : (0 : ℝ) ≤ ∑ i ∈ S, q i := Finset.sum_nonneg fun i _ => (hq' i).1
    rcases le_or_gt κ K with hle | hlt
    · refine (coin_count_large_tail hq' S (hS.trans hle) hK).trans ?_
      refine Real.rpow_le_rpow (by positivity) ?_ (le_of_lt hK)
      exact (div_le_div_iff_of_pos_right hK).mpr
        (mul_le_mul_of_nonneg_left hS (Real.exp_pos 1).le)
    · have hexp2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have h1 : (1 : ℝ) < Real.exp 1 * κ / K := by
        rw [lt_div_iff₀ hK]
        nlinarith
      have h2 : (1 : ℝ) < (Real.exp 1 * κ / K) ^ K :=
        Real.one_lt_rpow_iff_of_pos (by linarith) |>.mpr (Or.inl ⟨h1, hK⟩)
      exact le_trans (measureReal_le_one) (le_of_lt h2)
  have hb3 : ∀ tw : L × P2, (coins I q).real (E3 tw) ≤ (Real.exp 1 * κ / K) ^ K := by
    rintro ⟨t, w⟩
    refine hlarge _ ?_
    rw [hsum _ (fun t' E => t' = t ∧ (w : Finset α) ⊆ E)
      (fun t' => if t' = t then (F t').filter (fun E => (w : Finset α) ⊆ E) else ∅)
      (by intro i; simp) (by intro t' E; by_cases h : t' = t <;> simp [h])]
    rw [Finset.sum_eq_single t]
    · simpa using hmeanC1 t (w : Finset α) w.2
    · intro t' _ ht'; simp [ht']
    · intro h; simp at h
  have hb4 : ∀ ww : {ww : P2 × P2 // (ww.1 : Finset α) ≠ (ww.2 : Finset α)},
      (coins I q).real (E4 ww) ≤ (Real.exp 1 * κ / K) ^ K := by
    rintro ⟨⟨w, w'⟩, hne⟩
    refine hlarge _ ?_
    rw [hsum _ (fun _ E => (w : Finset α) ⊆ E ∧ (w' : Finset α) ⊆ E)
      (fun t => (F t).filter fun E => (w : Finset α) ⊆ E ∧ (w' : Finset α) ⊆ E)
      (by intro i; simp) (by intro t E; simp)]
    exact hmeanC2 (w : Finset α) w.2 (w' : Finset α) w'.2 hne
  -- the union bound
  have hcardP2 : Fintype.card P2 = (Vset.powersetCard 2).card := Fintype.card_coe _
  have hnum : (Fintype.card L : ℝ) * Real.exp (-(ρ ^ 2 * D) / 32) +
      (Fintype.card P2 : ℝ) * Real.exp (-(ρ ^ 2 * D) / 32) +
      (Fintype.card (L × P2) : ℝ) * (Real.exp 1 * κ / K) ^ K +
      (Fintype.card {ww : P2 × P2 // (ww.1 : Finset α) ≠ (ww.2 : Finset α)} : ℝ) *
        (Real.exp 1 * κ / K) ^ K < 1 := by
    have h4le : (Fintype.card {ww : P2 × P2 // (ww.1 : Finset α) ≠ (ww.2 : Finset α)} : ℝ)
        ≤ (Fintype.card P2 : ℝ) * (Fintype.card P2 : ℝ) := by
      have hsub := Fintype.card_subtype_le
        (fun ww : P2 × P2 => (ww.1 : Finset α) ≠ (ww.2 : Finset α))
      have hcast : (Fintype.card (P2 × P2) : ℝ)
          = (Fintype.card P2 : ℝ) * (Fintype.card P2 : ℝ) := by
        rw [Fintype.card_prod]; push_cast; ring
      calc (Fintype.card {ww : P2 × P2 // (ww.1 : Finset α) ≠ (ww.2 : Finset α)} : ℝ)
          ≤ (Fintype.card (P2 × P2) : ℝ) := by exact_mod_cast hsub
        _ = _ := hcast
    have hprod : (Fintype.card (L × P2) : ℝ)
        = (Fintype.card L : ℝ) * (Fintype.card P2 : ℝ) := by
      rw [Fintype.card_prod]; push_cast; ring
    have hcast2 : (Fintype.card P2 : ℝ) = ((Vset.powersetCard 2).card : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hcardP2
    rw [hprod, hcast2]
    rw [hcast2] at h4le
    have hX : (0 : ℝ) ≤ (Fintype.card L : ℝ) := by positivity
    have hY : (0 : ℝ) ≤ ((Vset.powersetCard 2).card : ℝ) := by positivity
    have hstep : (Fintype.card L : ℝ) * ((Vset.powersetCard 2).card : ℝ) *
          (Real.exp 1 * κ / K) ^ K +
        (Fintype.card {ww : P2 × P2 // (ww.1 : Finset α) ≠ (ww.2 : Finset α)} : ℝ) *
          (Real.exp 1 * κ / K) ^ K
        ≤ ((Fintype.card L : ℝ) + ((Vset.powersetCard 2).card : ℝ)) ^ 2 *
          (Real.exp 1 * κ / K) ^ K := by
      nlinarith [mul_le_mul_of_nonneg_right h4le hanonneg,
        mul_nonneg (mul_nonneg hX hX) hanonneg, mul_nonneg (mul_nonneg hX hY) hanonneg]
    have hexpand : ((Fintype.card L : ℝ) + ((Vset.powersetCard 2).card : ℝ)) *
        Real.exp (-(ρ ^ 2 * D) / 32)
        = (Fintype.card L : ℝ) * Real.exp (-(ρ ^ 2 * D) / 32) +
          ((Vset.powersetCard 2).card : ℝ) * Real.exp (-(ρ ^ 2 * D) / 32) := by ring
    linarith [hfail]
  obtain ⟨ω, hav1, hav2, hav3, hav4⟩ :=
    exists_avoiding_four_families (μ := coins I q) E1 E2 E3 E4 hb1 hb2 hb3 hb4 hnum
  -- read off the retained family
  refine ⟨Gof ω, hGsub ω, ?_, ?_, ?_, ?_⟩
  · intro t
    have hc := hcount ω (Finset.univ.filter (fun i : I => i.1 = t)) (fun t' _ => t' = t)
      (fun t' => if t' = t then Gof ω t' else ∅)
      (by intro i; simp) (by intro t' E; by_cases h : t' = t <;> simp [h])
    have hnot := hav1 t
    simp only [E1, Set.mem_setOf_eq, not_le, hmean1 t] at hnot
    rw [hc, Finset.sum_eq_single t] at hnot
    · simp only [if_true] at hnot; linarith
    · intro t' _ ht'; simp [ht']
    · intro h; simp at h
  · intro w hw
    have hnot := hav2 ⟨w, hw⟩
    simp only [E2, Set.mem_setOf_eq, not_le] at hnot
    rw [hcount ω _ (fun _ E => w ⊆ E) (fun t => (Gof ω t).filter fun E => w ⊆ E)
      (by intro i; simp) (by intro t E; simp)] at hnot
    linarith
  · intro t w hw
    have hnot := hav3 ⟨t, ⟨w, hw⟩⟩
    simp only [E3, Set.mem_setOf_eq, not_le] at hnot
    rw [hcount ω _ (fun t' E => t' = t ∧ w ⊆ E)
      (fun t' => if t' = t then (Gof ω t').filter (fun E => w ⊆ E) else ∅)
      (by intro i; simp) (by intro t' E; by_cases h : t' = t <;> simp [h]),
      Finset.sum_eq_single t] at hnot
    · simp only [if_true] at hnot; linarith
    · intro t' _ ht'; simp [ht']
    · intro h; simp at h
  · intro w hw w' hw' hne
    have hnot := hav4 ⟨⟨⟨w, hw⟩, ⟨w', hw'⟩⟩, hne⟩
    simp only [E4, Set.mem_setOf_eq, not_le] at hnot
    rw [hcount ω _ (fun _ E => w ⊆ E ∧ w' ⊆ E)
      (fun t => (Gof ω t).filter fun E => w ⊆ E ∧ w' ⊆ E)
      (by intro i; simp) (by intro t E; simp)] at hnot
    linarith

/-! ## Linear prime hypergraphs, the construction, and scale inequalities -/

/-- The scale `S_r(n) = n^{2/(k+1)} / (log n)²` with `r = k+1`. -/
noncomputable def Sr (k n : ℕ) : ℝ := (n : ℝ) ^ ((2 : ℝ) / (k + 1)) / (Real.log n) ^ 2

/-- Primes at most `n`, as a `Finset`. -/
def primesLE (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime

/--
`Nat.primeCounting n` is the number of primes `≤ n`.
-/
theorem primeCounting_eq_card (n : ℕ) :
    Nat.primeCounting n = (primesLE n).card := by
  rw [ Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
  rfl

/-- A linear `r`-uniform prime hypergraph with edge-products at most `n`:
edges are `r`-element sets of primes `≤ n`, edge-products are `≤ n`, and any two
distinct edges meet in at most one vertex. -/
def IsLinearPrimeHG (r n : ℕ) (H : Finset (Finset ℕ)) : Prop :=
  (∀ E ∈ H, E.card = r ∧ (∀ p ∈ E, p.Prime ∧ p ≤ n) ∧ (∏ p ∈ E, p) ≤ n) ∧
  (∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1)

/-- The vertex set of a hypergraph. -/
def vertices (H : Finset (Finset ℕ)) : Finset ℕ := H.biUnion id

/-- The set of composite edge-products. -/
noncomputable def compositeSet (H : Finset (Finset ℕ)) : Finset ℕ :=
  H.image (fun E => ∏ p ∈ E, p)

/-- The set `A_{ℋ}`: retained primes together with edge-products. -/
noncomputable def AH (n : ℕ) (H : Finset (Finset ℕ)) : Finset ℕ :=
  (primesLE n \ vertices H) ∪ compositeSet H

/--
For `k ≥ 2`, `r = k + 1`, and a linear `r`-uniform prime hypergraph `H` with
edge-products at most `n`, the set `A_ℋ` is repeated-factor `k`-primitive and has
cardinality `π(n) - |V(ℋ)| + |ℋ|`.
-/
theorem linear_construction (k n : ℕ) (hk : 2 ≤ k) (H : Finset (Finset ℕ))
    (hH : IsLinearPrimeHG (k + 1) n H) :
    RepPrimitive k (AH n H) ∧
      (AH n H).card = Nat.primeCounting n - (vertices H).card + H.card := by
  constructor;
  · intro a ha;
    by_cases ha_ret : a ∈ primesLE n \ vertices H;
    · intro f hf
      have h_not_div : ∀ i, ¬(a ∣ f i) := by
        intro i hi
        have h_f_i_composite : ∃ E ∈ H, f i = ∏ p ∈ E, p := by
          have h_f_i_composite : f i ∈ compositeSet H := by
            have h_f_i_composite : f i ∈ primesLE n \ vertices H → False := by
              intro h_f_i_composite
              have h_f_i_prime : Nat.Prime (f i) := by
                exact Finset.mem_filter.mp ( Finset.mem_sdiff.mp h_f_i_composite |>.1 ) |>.2;
              have h_f_i_prime : a = f i := by
                exact Nat.prime_dvd_prime_iff_eq ( Finset.mem_filter.mp ( Finset.mem_sdiff.mp ha_ret |>.1 ) |>.2 ) h_f_i_prime |>.1 hi;
              grind;
            exact Or.resolve_left ( Finset.mem_union.mp ( Finset.mem_of_mem_erase ( hf i ) ) ) h_f_i_composite;
          unfold compositeSet at h_f_i_composite; aesop;
        obtain ⟨ E, hE₁, hE₂ ⟩ := h_f_i_composite; simp_all +decide ;
        have h_prime_div : ∀ p ∈ E, Nat.Prime p := by
          exact fun p hp => hH.1 E hE₁ |>.2.1 p hp |>.1;
        have h_prime_div : a ∈ E := by
          haveI := Fact.mk ( show Nat.Prime a from by { unfold primesLE at ha_ret; aesop } ) ; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Finset.prod_eq_zero_iff ] ;
          obtain ⟨ p, hp₁, hp₂ ⟩ := hi; rw [ ZMod.natCast_eq_zero_iff ] at hp₂; have := Nat.prime_dvd_prime_iff_eq ( show Nat.Prime a from by { unfold primesLE at ha_ret; aesop } ) ( h_prime_div p hp₁ ) ; aesop;
        exact ha_ret.2 ( Finset.mem_biUnion.mpr ⟨ E, hE₁, h_prime_div ⟩ );
      haveI := Fact.mk ( show Nat.Prime a from Finset.mem_filter.mp ( Finset.mem_sdiff.mp ha_ret |>.1 ) |>.2 ) ; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Finset.prod_eq_zero_iff ] ;
    · obtain ⟨E, hE⟩ : ∃ E ∈ H, a = ∏ p ∈ E, p := by
        unfold AH at ha;
        unfold compositeSet at ha; aesop;
      intro f hf hdiv
      have h_prime_factors : ∀ p ∈ E, p ∣ ∏ i, f i := by
        exact fun p hp => dvd_trans ( hE.2.symm ▸ Finset.dvd_prod_of_mem _ hp ) hdiv;
      have h_prime_factors : ∀ p ∈ E, ∃ i, p ∣ f i := by
        intro p hp; specialize h_prime_factors p hp; simp_all +decide ;
        haveI := Fact.mk ( show Nat.Prime p from by have := hH.1 E hE.1; aesop ) ; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Finset.prod_eq_zero_iff ] ;
      have h_prime_factors : ∀ i, (Finset.filter (fun p => p ∣ f i) E).card ≤ 1 := by
        intro i
        by_cases hfi : f i ∈ compositeSet H;
        · obtain ⟨E', hE'⟩ : ∃ E' ∈ H, f i = ∏ p ∈ E', p := by
            unfold compositeSet at hfi; aesop;
          have h_prime_factors : (E ∩ E').card ≤ 1 := by
            have := hH.2 E hE.1 E' hE'.1; aesop;
          refine le_trans ?_ h_prime_factors;
          refine Finset.card_le_card ?_;
          simp_all +decide [ Finset.subset_iff ];
          intro p hp hp'; have := hH.1 E hE.1; have := hH.1 E' hE'.1; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
          contrapose! hp';
          exact Nat.Coprime.prod_right fun q hq => by have := Nat.coprime_primes ( by aesop : Nat.Prime p ) ( by aesop : Nat.Prime q ) ; aesop;
        · have h_prime_factors : ∀ p ∈ E, p ∣ f i → p = f i := by
            intros p hp hdiv
            have h_prime : Nat.Prime p := by
              have := hH.1 E hE.1; aesop;
            have h_prime_factors : f i ∈ primesLE n \ vertices H := by
              have := hf i; simp_all +decide [ AH ] ;
            simp_all +decide [ primesLE, vertices ];
            exact Nat.prime_dvd_prime_iff_eq h_prime h_prime_factors.1.2 |>.1 hdiv;
          exact Finset.card_le_one.mpr fun p hp q hq => h_prime_factors p ( Finset.filter_subset _ _ hp ) ( Finset.mem_filter.mp hp |>.2 ) ▸ h_prime_factors q ( Finset.filter_subset _ _ hq ) ( Finset.mem_filter.mp hq |>.2 ) ▸ rfl;
      have h_prime_factors : (Finset.biUnion Finset.univ (fun i => Finset.filter (fun p => p ∣ f i) E)).card ≤ k := by
        exact le_trans ( Finset.card_biUnion_le ) ( le_trans ( Finset.sum_le_sum fun _ _ => h_prime_factors _ ) ( by norm_num ) );
      have h_prime_factors : (Finset.biUnion Finset.univ (fun i => Finset.filter (fun p => p ∣ f i) E)).card = E.card := by
        congr with p ; aesop;
      have := hH.1 E hE.1; aesop;
  · rw [ AH, Finset.card_union_of_disjoint ];
    · rw [ Finset.card_sdiff, primeCounting_eq_card ];
      rw [ show vertices H ∩ primesLE n = vertices H from ?_, show compositeSet H = H.image ( fun E => ∏ p ∈ E, p ) from rfl, Finset.card_image_of_injOn ];
      · intro E hE E' hE' h_eq; have := hH.1 E hE; have := hH.1 E' hE'; simp_all +decide ;
        apply_fun fun x => x.primeFactors at h_eq ; simp_all +decide [ Nat.primeFactors_prod ];
      · refine' Finset.inter_eq_left.mpr _;
        intro p hp; obtain ⟨ E, hE, hpE ⟩ := Finset.mem_biUnion.mp hp; have := hH.1 E hE; simp_all +decide [ primesLE ] ;
    · simp +decide [ Finset.disjoint_left, compositeSet ];
      intro p hp hp' x hx H; have := hH.1 x hx; simp_all +decide ;
      unfold vertices at hp'; simp_all +decide [ primesLE ] ;
      replace H := congr_arg ( fun z => z.primeFactors ) H ; simp_all +decide [ Nat.primeFactors_prod ] ;

/--
Fix `η > 0` and `k ≥ 2`; put `R = η n^{2/(k+1)} / (log n)²`.  For all sufficiently
large `n`, the four scale inequalities below hold.
-/
theorem scale_inequalities (k : ℕ) (hk : 2 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      let R : ℝ := η * (n : ℝ) ^ ((2 : ℝ) / (k + 1)) / (Real.log n) ^ 2
      ((R ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1)) > (n : ℝ) ^ ((1 : ℝ) / (k + 2))) ∧
      ((n : ℝ) / R ^ ((k : ℝ) / 2) < R) ∧
      (((n : ℝ) / R) ^ ((1 : ℝ) / (k - 1)) * ((n : ℝ) / R ^ (((k : ℝ) + 1) / 2)) < R) ∧
      ((n : ℝ) / R ^ (((k : ℝ) + 1) / 2) < (R ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1))) := by
  -- The first scale inequality.
  have h_inq1 : ∀ᶠ (n : ℕ) in Filter.atTop, let R := η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2; (R ^ (k : ℝ) / (n : ℝ)) ^ (1 / (k - 1 : ℝ)) > (n : ℝ) ^ (1 / (k + 2 : ℝ)) := by
    -- We simplify the expression inside the limit.
    suffices h_simp : Filter.Tendsto (fun n : ℕ => ((η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2) ^ (k : ℝ) / (n : ℝ)) ^ (1 / (k - 1 : ℝ)) / (n : ℝ) ^ (1 / (k + 2 : ℝ))) Filter.atTop Filter.atTop by
      filter_upwards [ h_simp.eventually_gt_atTop 1, Filter.eventually_gt_atTop 1 ] with n hn hn' using by rw [ gt_iff_lt ] ; rw [ lt_div_iff₀ ( by positivity ) ] at *; linarith;
    -- Simplify the expression inside the limit.
    suffices h_simp : Filter.Tendsto (fun n : ℕ => η ^ (k / (k - 1) : ℝ) * (n : ℝ) ^ ((2 * k / (k + 1) - 1) / (k - 1) - 1 / (k + 2) : ℝ) / (Real.log n) ^ (2 * k / (k - 1) : ℝ)) Filter.atTop Filter.atTop by
      refine h_simp.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
      rw [ Real.div_rpow, Real.div_rpow ] <;> try positivity;
      rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ];
      rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ), ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      rw [ ← Real.rpow_natCast ] ; repeat rw [ ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      norm_num [ Real.rpow_add ( by positivity : 0 < ( n : ℝ ) ), Real.rpow_sub ( by positivity : 0 < ( n : ℝ ) ) ] ; ring_nf;
      norm_num [ Real.rpow_neg ( by positivity : 0 ≤ ( n : ℝ ) ) ] ; ring;
    have h_exp_pos : (2 * k / (k + 1 : ℝ) - 1) / (k - 1) - 1 / (k + 2 : ℝ) > 0 := by
      field_simp;
      rw [ lt_sub_iff_add_lt, lt_div_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast ];
    have h_lim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((2 * k / (k + 1 : ℝ) - 1) / (k - 1) - 1 / (k + 2 : ℝ)) / (Real.log n) ^ (2 * k / (k - 1) : ℝ)) Filter.atTop Filter.atTop := by
      convert powers_dominate_logs _ h_exp_pos _ |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop using 2;
    simpa only [ mul_div_assoc ] using h_lim.const_mul_atTop ( by positivity );
  -- The second scale inequality.
  have h_inq2 : ∀ᶠ (n : ℕ) in Filter.atTop, let R := η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2; (n : ℝ) / R ^ (k / 2 : ℝ) < R := by
    -- We simplify the expression for the ratio.
    suffices h_ratio : Filter.Tendsto (fun n : ℕ => (n : ℝ) / ((η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2) ^ ((k / 2 : ℝ) + 1))) Filter.atTop (nhds 0) by
      filter_upwards [ h_ratio.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 1 ] with n hn hn';
      rw [ div_lt_iff₀ ] at *;
      · convert hn using 1 ; rw [ Real.rpow_add ( by exact div_pos ( mul_pos hη ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn'.le ) _ ) ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hn' ) ) ) ), Real.rpow_one ] ; ring;
      · exact Real.rpow_pos_of_pos ( div_pos ( mul_pos hη ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn'.le ) _ ) ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hn' ) ) ) ) _;
      · exact Real.rpow_pos_of_pos ( div_pos ( mul_pos hη ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn'.le ) _ ) ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hn' ) ) ) ) _;
    -- Simplify the expression inside the limit.
    suffices h_simp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - (2 / (k + 1 : ℝ)) * ((k / 2 : ℝ) + 1)) * (Real.log n) ^ (2 * ((k / 2 : ℝ) + 1)) / η ^ ((k / 2 : ℝ) + 1)) Filter.atTop (nhds 0) by
      refine h_simp.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
      rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ), Real.rpow_sub ( by positivity ), Real.rpow_mul ( by positivity ) ] ; norm_num ; ring_nf;
      rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( Real.log_nonneg ( by norm_cast; linarith ) ) ] ; norm_num ; ring_nf;
    -- We can factor out $n^{1 - (2 / (k + 1)) * ((k / 2) + 1)}$ and use the fact that $(\log n)^{2 * ((k / 2) + 1)}$ grows slower than any polynomial.
    have h_factor : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - (2 / (k + 1 : ℝ)) * ((k / 2 : ℝ) + 1)) * (Real.log n) ^ (2 * ((k / 2 : ℝ) + 1))) Filter.atTop (nhds 0) := by
      convert rpow_neg_mul_log_rpow_tendsto_zero ( ( 2 : ℝ ) / ( k + 1 ) * ( k / 2 + 1 ) - 1 ) _ ( 2 * ( k / 2 + 1 ) ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop using 2 ; norm_num;
      rw [ div_mul_eq_mul_div, lt_sub_iff_add_lt, lt_div_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast ];
    simpa using h_factor.div_const _;
  -- The third scale inequality.
  have h_inq3 : ∀ᶠ (n : ℕ) in Filter.atTop, let R := η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2; ((n : ℝ) / R) ^ (1 / (k - 1 : ℝ)) * ((n : ℝ) / R ^ ((k + 1) / 2 : ℝ)) < R := by
    -- We simplify the expression for the ratio.
    suffices h_simp : Filter.Tendsto (fun n : ℕ => ((n : ℝ) / (η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2)) ^ (1 / (k - 1 : ℝ)) * ((n : ℝ) / (η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2) ^ ((k + 1) / 2 : ℝ)) / (η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2)) Filter.atTop (nhds 0) by
      filter_upwards [ h_simp.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 1 ] with n hn hn';
      rw [ div_lt_one ( by exact div_pos ( mul_pos hη ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn'.le ) _ ) ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hn' ) ) ) ) ] at hn ; aesop;
    -- We simplify the expression inside the limit.
    suffices h_simp : Filter.Tendsto (fun n : ℕ => (η⁻¹ * (n : ℝ) ^ (1 - 2 / (k + 1 : ℝ)) * (Real.log n) ^ 2) ^ (1 / (k - 1 : ℝ)) * (η⁻¹ ^ ((k + 1) / 2 : ℝ) * (n : ℝ) ^ (1 - (k + 1) / (k + 1 : ℝ)) * (Real.log n) ^ (k + 1)) / (η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2)) Filter.atTop (nhds 0) by
      refine h_simp.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
      congr 2;
      · rw [ Real.rpow_sub ( by positivity ), Real.rpow_one ] ; ring_nf;
        norm_num;
      · rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
        rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( Real.log_nonneg ( Nat.one_le_cast.mpr hn.le ) ) ] ; norm_num ; ring_nf;
        rw [ ← Real.inv_rpow ( by positivity ) ] ; norm_cast ; norm_num ; ring_nf;
        rw [ show ( 1 + ( - ( k * ( 1 + k : ℝ ) ⁻¹ ) - ( 1 + k : ℝ ) ⁻¹ ) ) = 1 - ( k * ( 1 + k : ℝ ) ⁻¹ + ( 1 + k : ℝ ) ⁻¹ ) by ring, Real.rpow_sub ( by positivity ), Real.rpow_one ] ; ring;
    -- We simplify the expression inside the limit further.
    suffices h_simp' : Filter.Tendsto (fun n : ℕ => (η⁻¹ ^ (1 / (k - 1 : ℝ)) * (n : ℝ) ^ ((1 - 2 / (k + 1 : ℝ)) / (k - 1 : ℝ)) * (Real.log n) ^ (2 / (k - 1 : ℝ))) * (η⁻¹ ^ ((k + 1) / 2 : ℝ) * (Real.log n) ^ (k + 1)) / (η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2)) Filter.atTop (nhds 0) by
      refine h_simp'.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
      rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ] ; norm_num [ show ( k : ℝ ) + 1 ≠ 0 by positivity ] ; ring_nf;
      rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( Real.log_nonneg ( Nat.one_le_cast.mpr hn.le ) ) ] ; ring_nf;
    -- We can factor out the common terms and simplify the expression.
    suffices h_simp'' : Filter.Tendsto (fun n : ℕ => (η⁻¹ ^ (1 / (k - 1 : ℝ) + (k + 1) / 2 : ℝ) / η) * (n : ℝ) ^ ((1 - 2 / (k + 1 : ℝ)) / (k - 1 : ℝ) - 2 / (k + 1 : ℝ)) * (Real.log n) ^ (2 / (k - 1 : ℝ) + k + 1 + 2)) Filter.atTop (nhds 0) by
      refine h_simp''.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
      rw [ Real.rpow_add ( by positivity ), Real.rpow_sub ( by positivity ) ] ; ring_nf;
      norm_num [ Real.rpow_add ( Real.log_pos <| Nat.one_lt_cast.mpr hn ), Real.rpow_sub ( Real.log_pos <| Nat.one_lt_cast.mpr hn ) ] ; ring;
    -- We can use the fact that $n^a / (\log n)^b \to 0$ as $n \to \infty$ for any $a < 0$ and $b > 0$.
    have h_lim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 - 2 / (k + 1 : ℝ)) / (k - 1 : ℝ) - 2 / (k + 1 : ℝ)) * (Real.log n) ^ (2 / (k - 1 : ℝ) + k + 1 + 2)) Filter.atTop (nhds 0) := by
      -- We simplify the exponent of $n$.
      suffices h_exp_n : ((1 - 2 / (k + 1 : ℝ)) / (k - 1 : ℝ) - 2 / (k + 1 : ℝ)) < 0 by
        convert rpow_neg_mul_log_rpow_tendsto_zero ( - ( ( 1 - 2 / ( k + 1 : ℝ ) ) / ( k - 1 : ℝ ) - 2 / ( k + 1 : ℝ ) ) ) ( by linarith ) ( 2 / ( k - 1 : ℝ ) + k + 1 + 2 ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop using 2 ; norm_num;
      rw [ div_sub_div, div_lt_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast, div_mul_cancel₀ ( 2 : ℝ ) ( by positivity : ( k : ℝ ) + 1 ≠ 0 ) ];
    convert h_lim.const_mul ( η⁻¹ ^ ( 1 / ( k - 1 : ℝ ) + ( k + 1 ) / 2 ) / η ) using 2 <;> ring;
  -- The fourth scale inequality.
  have h_inq4 : ∀ᶠ (n : ℕ) in Filter.atTop, let R := η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2; (n : ℝ) / R ^ ((k + 1) / 2 : ℝ) < (R ^ (k : ℝ) / (n : ℝ)) ^ (1 / (k - 1 : ℝ)) := by
    -- We simplify the expression for the ratio.
    suffices h_ratio : Filter.Tendsto (fun n : ℕ => (n : ℝ) / ((η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2) ^ ((k + 1) / 2 : ℝ)) / ((η * (n : ℝ) ^ (2 / (k + 1 : ℝ)) / (Real.log n) ^ 2) ^ (k / (k - 1 : ℝ)) / (n : ℝ) ^ (1 / (k - 1 : ℝ)))) Filter.atTop (nhds 0) by
      filter_upwards [ h_ratio.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 1 ] with n hn hn';
      rw [ div_lt_iff₀ ] at hn;
      · convert hn using 1;
        rw [ Real.div_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      · exact div_pos ( Real.rpow_pos_of_pos ( div_pos ( mul_pos hη ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn'.le ) _ ) ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hn' ) ) ) ) _ ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn'.le ) _ );
    -- We simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 + 1 / (k - 1 : ℝ) - (k + 1) / 2 * (2 / (k + 1 : ℝ)) - k / (k - 1 : ℝ) * (2 / (k + 1 : ℝ))) * (Real.log n) ^ (2 * (k + 1) / 2 + 2 * k / (k - 1 : ℝ)) / η ^ ((k + 1) / 2 + k / (k - 1 : ℝ))) Filter.atTop (nhds 0) by
      refine h_simplify.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
      rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.div_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
      rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
      rw [ ← Real.rpow_natCast ] ; repeat rw [ ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      norm_num [ Real.rpow_add ( by positivity : 0 < ( n : ℝ ) ), Real.rpow_add ( by exact Real.log_pos ( Nat.one_lt_cast.mpr hn ) : 0 < Real.log n ), Real.rpow_neg ( by positivity : 0 ≤ ( n : ℝ ) ), Real.rpow_neg ( by exact Real.log_nonneg ( Nat.one_le_cast.mpr hn.le ) : 0 ≤ Real.log n ) ] ; ring_nf;
      norm_num [ Real.rpow_def_of_pos ( by positivity : 0 < ( n : ℝ ) ), Real.rpow_def_of_pos ( by positivity : 0 < ( η : ℝ ) ) ] ; ring_nf;
      norm_num [ mul_assoc, ← Real.exp_add, ← Real.exp_neg ] ; ring_nf;
      exact Or.inl <| Or.inl <| Or.inl <| by rw [ mul_right_comm ] ; rw [ ← Real.exp_add ] ; ring_nf;
    -- We simplify the exponent of $n$.
    suffices h_exp : 1 + 1 / (k - 1 : ℝ) - (k + 1) / 2 * (2 / (k + 1 : ℝ)) - k / (k - 1 : ℝ) * (2 / (k + 1 : ℝ)) < 0 by
      have := rpow_neg_mul_log_rpow_tendsto_zero ( - ( 1 + 1 / ( k - 1 : ℝ ) - ( k + 1 ) / 2 * ( 2 / ( k + 1 : ℝ ) ) - k / ( k - 1 : ℝ ) * ( 2 / ( k + 1 : ℝ ) ) ) ) ( neg_pos.mpr h_exp ) ( 2 * ( k + 1 ) / 2 + 2 * k / ( k - 1 : ℝ ) );
      simpa using Filter.Tendsto.div_const ( this.comp tendsto_natCast_atTop_atTop ) _;
    field_simp;
    rw [ mul_sub, mul_add, mul_div_assoc' ] ; ring_nf ; nlinarith [ inv_mul_cancel₀ ( by linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] : ( -1 + k : ℝ ) ≠ 0 ), show ( k : ℝ ) ≥ 2 by norm_cast ];
  filter_upwards [ h_inq1, h_inq2, h_inq3, h_inq4 ] with n hn1 hn2 hn3 hn4 using ⟨ hn1, hn2, hn3, hn4 ⟩

/-! ## Assignment lemmas for the extraction theorem -/

/-- A divisor of `a` which divides no other member of `A`. -/
def PrivateDivisor (A : Finset ℕ) (a d : ℕ) : Prop :=
  d ∣ a ∧ ∀ b ∈ A.erase a, ¬ d ∣ b

/-- Stage I has at most `π(⌊R⌋)` members when all assigned primes are at
most the cutoff. -/
lemma privatePrimePower_card_le_primeCounting (A C : Finset ℕ) (R : ℝ)
    (hCA : C ⊆ A)
    (hpriv : ∀ a ∈ C, ∃ p α : ℕ,
      p.Prime ∧ 1 ≤ α ∧ p ^ α ∣ a ∧
        (p : ℝ) ≤ R ∧ ∀ b ∈ A.erase a, ¬ p ^ α ∣ b) :
    C.card ≤ Nat.primeCounting ⌊R⌋₊ := by
  -- Construct hypothesis that tracks p ≤ R
  -- We use a subtype to carry the bound
  let T := { q : ℕ // q ≤ ⌊R⌋₊ ∧ Nat.Prime q }
  have hprivT : ∀ a : C, ∃ (q : T) (α : ℕ),
      1 ≤ α ∧ (q : ℕ) ^ α ∣ a.val ∧ ∀ b ∈ A.erase a.val, ¬ (q : ℕ) ^ α ∣ b := fun ⟨a, ha⟩ => by
    obtain ⟨p, α, hp, hα, hdvd, hle, hnotdiv⟩ := hpriv a ha
    refine ⟨⟨p, Nat.le_floor hle, hp⟩, α, hα, hdvd, hnotdiv⟩
  -- Get injective assignment using the bounded primes
  -- We'll adapt privatePrimePower_assignment
  let f₁ : C → T := fun a => Classical.choose (hprivT a)
  let f₂ : C → ℕ := fun a => (Classical.choose_spec (hprivT a)).choose
  have hf₂ : ∀ a, 1 ≤ f₂ a := fun a => (Classical.choose_spec (hprivT a)).choose_spec.1
  have hf₃ : ∀ a, (f₁ a : ℕ) ^ f₂ a ∣ a.val := fun a => (Classical.choose_spec (hprivT a)).choose_spec.2.1
  have hf₄ : ∀ a b hb, ¬ (f₁ a : ℕ) ^ f₂ a ∣ b := fun a b hb => (Classical.choose_spec (hprivT a)).choose_spec.2.2 b hb
  let p : ℕ → ℕ := fun n => if h : n ∈ C then (f₁ ⟨n, h⟩).val else 2
  -- Prove injectivity of p on C
  have hinj : Set.InjOn p C := by
    intro a ha a' ha' hpa
    have hp_a : p a = (f₁ ⟨a, ha⟩).val := dif_pos ha
    have hp_a' : p a' = (f₁ ⟨a', ha'⟩).val := dif_pos ha'
    have hpa' : (f₁ ⟨a, ha⟩).val = (f₁ ⟨a', ha'⟩).val := hp_a ▸ hp_a' ▸ hpa
    by_contra hne
    have ha'_erase : a' ∈ A.erase a := by
      rw [Finset.mem_erase]
      exact ⟨fun h => hne h.symm, hCA ha'⟩
    have hdvd_a : (f₁ ⟨a, ha⟩).val ^ f₂ ⟨a, ha⟩ ∣ a := hf₃ ⟨a, ha⟩
    have hdvd_a' : (f₁ ⟨a', ha'⟩).val ^ f₂ ⟨a', ha'⟩ ∣ a' := hf₃ ⟨a', ha'⟩
    rcases le_or_gt (f₂ ⟨a, ha⟩) (f₂ ⟨a', ha'⟩) with hle | hgt
    · have hdiv : (f₁ ⟨a, ha⟩).val ^ f₂ ⟨a, ha⟩ ∣ (f₁ ⟨a', ha'⟩).val ^ f₂ ⟨a', ha'⟩ := by
        rw [hpa']; exact pow_dvd_pow _ hle
      exact hf₄ ⟨a, ha⟩ a' ha'_erase (dvd_trans hdiv hdvd_a')
    · have hdiv : (f₁ ⟨a', ha'⟩).val ^ f₂ ⟨a', ha'⟩ ∣ (f₁ ⟨a, ha⟩).val ^ f₂ ⟨a, ha⟩ := by
        rw [← hpa']; exact pow_dvd_pow _ (le_of_lt hgt)
      exact hf₄ ⟨a', ha'⟩ a (by rw [Finset.mem_erase]; exact ⟨hne, hCA ha⟩) (dvd_trans hdiv hdvd_a)
  -- Define the set of primes ≤ ⌊R⌋
  let S := Finset.filter Nat.Prime (Finset.Icc 2 ⌊R⌋₊)
  -- Show C injects into S via p
  have hmaps : ∀ a ∈ C, p a ∈ S := by
    intro a ha
    simp only [p, dif_pos ha, S, Finset.mem_filter, Finset.mem_Icc]
    have hle : (f₁ ⟨a, ha⟩ : ℕ) ≤ ⌊R⌋₊ := (f₁ ⟨a, ha⟩).property.1
    refine ⟨⟨(f₁ ⟨a, ha⟩).property.2.two_le, ?_⟩, (f₁ ⟨a, ha⟩).property.2⟩
    exact le_trans (Nat.cast_le.mpr hle) (Nat.floor_le (by positivity))
  -- Use cardinality bound
  calc C.card = (C.image p).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ S.card := Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)
    _ = Nat.primeCounting ⌊R⌋₊ := by
        rw [Nat.primeCounting]
        simp only [S]
        unfold Nat.primeCounting'
        rw [Nat.count_eq_card_filter_range]
        congr 1
        apply Finset.ext
        intro x
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
        constructor
        · intro ⟨⟨hx2, hxle⟩, hxP⟩
          exact ⟨Nat.lt_succ_of_le hxle, hxP⟩
        · intro ⟨hxltp1, hxP⟩
          exact ⟨⟨hxP.two_le, Nat.le_of_lt_succ hxltp1⟩, hxP⟩

section
open Classical

/-! ## The three extraction stages -/

/-- An element has a private prime power with base at most `R`. -/
def HasPrivatePrimePowerBelow (A : Finset ℕ) (R a : ℕ) : Prop :=
  ∃ p α : ℕ, p.Prime ∧ 1 ≤ α ∧ p ^ α ∣ a ∧ p ≤ R ∧
    ∀ b ∈ A.erase a, ¬ p ^ α ∣ b

/-- An element has a private divisor at most `R`. -/
def HasPrivateDivisorBelow (A : Finset ℕ) (R a : ℕ) : Prop :=
  ∃ d : ℕ, d ≤ R ∧ PrivateDivisor A a d

/-- Stage I consists of elements possessing a private small prime power. -/
noncomputable def extractionStageOne (A : Finset ℕ) (R : ℕ) : Finset ℕ :=
  A.filter (HasPrivatePrimePowerBelow A R)

/-- Stage II consists of the still-unassigned elements representable as a
product of `k` basis members. -/
noncomputable def extractionStageTwo (A : Finset ℕ) (B : Finset ℕ)
    (k R : ℕ) : Finset ℕ :=
  (A.filter (fun a => ∃ f : Fin k → ℕ,
    (∀ i, f i ∈ B) ∧ ∏ i, f i = a)) \ extractionStageOne A R

/-- Stage III consists of the still-unassigned elements possessing a private
small divisor. -/
noncomputable def extractionStageThree (A : Finset ℕ) (B : Finset ℕ)
    (k R : ℕ) : Finset ℕ :=
  (A \ (extractionStageOne A R ∪ extractionStageTwo A B k R)).filter
    (HasPrivateDivisorBelow A R)

/-- Elements surviving all three extraction stages. -/
noncomputable def extractionStageHard (A : Finset ℕ) (B : Finset ℕ)
    (k R : ℕ) : Finset ℕ :=
  A \ (extractionStageOne A R ∪ extractionStageTwo A B k R ∪
    extractionStageThree A B k R)

/-- The four canonical parts partition `A`; the first three are pairwise
disjoint, and a survivor is neither basis-representable nor equipped with any
of the private factors tested in Stages I and III. -/
lemma extractionStages_partition (A B : Finset ℕ) (k R : ℕ) :
    A = extractionStageOne A R ∪ extractionStageTwo A B k R ∪
        extractionStageThree A B k R ∪ extractionStageHard A B k R ∧
    Disjoint (extractionStageOne A R) (extractionStageTwo A B k R) ∧
    Disjoint (extractionStageOne A R) (extractionStageThree A B k R) ∧
    Disjoint (extractionStageTwo A B k R) (extractionStageThree A B k R) ∧
    (∀ a ∈ extractionStageHard A B k R,
      ¬ (∃ f : Fin k → ℕ, (∀ i, f i ∈ B) ∧ ∏ i, f i = a)) ∧
    (∀ a ∈ extractionStageHard A B k R,
      ¬ HasPrivatePrimePowerBelow A R a) ∧
    (∀ a ∈ extractionStageHard A B k R,
      ¬ HasPrivateDivisorBelow A R a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Goal 1: Partition
  · ext a
    simp [extractionStageOne, extractionStageTwo, extractionStageThree, extractionStageHard]
    tauto
  -- Goal 2: Disjoint StageOne StageTwo
  · exact Finset.disjoint_sdiff
  -- Goal 3: Disjoint StageOne StageThree
  · apply Finset.disjoint_left.mpr
    intro a ha ha'
    simp [extractionStageThree] at ha'
    exact ha'.1.2.1 ha
  -- Goal 4: Disjoint StageTwo StageThree
  · apply Finset.disjoint_left.mpr
    intro a ha ha'
    simp [extractionStageThree] at ha'
    exact ha'.1.2.2 ha
  -- Goal 5: StageHard not basis representable
  · intro a ha
    simp [extractionStageHard] at ha
    intro ⟨f, hf, hprod⟩
    have : a ∈ extractionStageTwo A B k R := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨ha.1, f, hf, hprod⟩, ha.2.1⟩
    exact ha.2.2.1 this
  -- Goal 6: StageHard no private prime power
  · intro a ha
    simp [extractionStageHard, extractionStageOne] at ha
    exact ha.2.1 ha.1
  -- Goal 7: StageHard no private divisor
  · intro a ha
    simp [extractionStageHard] at ha
    obtain ⟨haA, ha1, ha2, ha3⟩ := ha
    intro hpriv
    have hs12 : a ∉ extractionStageOne A R ∪ extractionStageTwo A B k R := fun h => by
      rcases Finset.mem_union.mp h with h1 | h2 <;> [exact ha1 h1; exact ha2 h2]
    have h3 : a ∈ extractionStageThree A B k R :=
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨haA, hs12⟩, hpriv⟩
    exact ha3 h3

/-- Stage I has at most `π(R)` elements. -/
lemma extractionStageOne_card_le (A : Finset ℕ) (R : ℕ) :
    (extractionStageOne A R).card ≤ Nat.primeCounting R := by
  have hCA : extractionStageOne A R ⊆ A := Finset.filter_subset _ _
  have hpriv : ∀ a ∈ extractionStageOne A R, ∃ p α : ℕ,
      p.Prime ∧ 1 ≤ α ∧ p ^ α ∣ a ∧ (p : ℝ) ≤ R ∧ ∀ b ∈ A.erase a, ¬ p ^ α ∣ b := by
    intro a ha
    rw [extractionStageOne, Finset.mem_filter] at ha
    obtain ⟨p, α, hp, hα, hdvd, hle, hnotdiv⟩ := ha.2
    exact ⟨p, α, hp, hα, hdvd, by norm_cast, hnotdiv⟩
  have := privatePrimePower_card_le_primeCounting A (extractionStageOne A R) (R : ℝ) hCA hpriv
  simp [Nat.primeCounting] at this
  exact this

end

/-! ## Greedy box-packing infrastructure for extraction -/

/-- `Mulk B k a` means that `a` is a product of exactly `k` members of `B`,
with repetitions allowed. -/
def Mulk (B : Finset ℕ) (k a : ℕ) : Prop :=
  ∃ f : Fin k → ℕ, (∀ i, f i ∈ B) ∧ ∏ i, f i = a

/-- A family of `k` box products lying in `B` witnesses membership in
`Mul_k(B)` when their total product is `a`. -/
lemma mulk_of_boxes {B : Finset ℕ} {k a : ℕ} (boxes : Fin k → ℕ)
    (hboxes : ∀ i, boxes i ∈ B) (hprod : ∏ i, boxes i = a) : Mulk B k a := by
  exact ⟨boxes, hboxes, hprod⟩

/-- One greedy step: multiply the current prime `p` into a box of minimal
product. -/
noncomputable def gstep (k : ℕ) (hk : 0 < k) (boxes : Fin k → ℕ) (p : ℕ) : Fin k → ℕ :=
  let j := (Finset.univ.exists_min_image boxes ⟨⟨0, hk⟩, Finset.mem_univ _⟩).choose
  Function.update boxes j (boxes j * p)

/-- The greedy step multiplies the total product by `p`. -/
lemma gstep_prod (k : ℕ) (hk : 0 < k) (boxes : Fin k → ℕ) (p : ℕ) :
    ∏ i, gstep k hk boxes p i = (∏ i, boxes i) * p := by
  unfold gstep
  set j := (Finset.univ.exists_min_image boxes ⟨⟨0, hk⟩, Finset.mem_univ _⟩).choose
  rw [Finset.prod_update_of_mem (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ boxes (Finset.mem_univ j), Finset.erase_eq]
  ring

/-- The greedy step preserves positivity of all boxes. -/
lemma gstep_pos (k : ℕ) (hk : 0 < k) (boxes : Fin k → ℕ) (p : ℕ)
    (hb : ∀ i, 0 < boxes i) (hp : 0 < p) : ∀ i, 0 < gstep k hk boxes p i := by
  intro i; unfold gstep
  set j := (Finset.univ.exists_min_image boxes ⟨⟨0, hk⟩, Finset.mem_univ _⟩).choose
  by_cases h : i = j
  · subst h; rw [Function.update_self]; exact Nat.mul_pos (hb _) hp
  · rw [Function.update_of_ne h]; exact hb i

/-- The box chosen by `gstep` is of minimal product, and `gstep` updates exactly
that box.  This is the process fact needed to thread the greedy invariant through
a `List.foldl`. -/
lemma gstep_min (k : ℕ) (hk : 0 < k) (boxes : Fin k → ℕ) (p : ℕ) :
    ∃ j, (∀ i, boxes j ≤ boxes i) ∧
      gstep k hk boxes p = Function.update boxes j (boxes j * p) := by
  refine ⟨(Finset.univ.exists_min_image boxes ⟨⟨0, hk⟩, Finset.mem_univ _⟩).choose, ?_, rfl⟩
  intro i
  exact (Finset.univ.exists_min_image boxes ⟨⟨0, hk⟩, Finset.mem_univ _⟩).choose_spec.2 i
    (Finset.mem_univ _)

/-- If every box is currently “in `B`” (product `≤ R` or a prime) and the chosen
  minimal box either does not overflow past `R` when multiplied by the prime
  `p`, or was empty (product `1`, becoming the single prime `p`), then the
  invariant is preserved by one greedy step. -/
lemma gstep_good (R : ℕ) (k : ℕ) (hk : 0 < k) (boxes : Fin k → ℕ) (p : ℕ) (hp : p.Prime)
    (hgood : ∀ i, boxes i ≤ R ∨ (boxes i).Prime)
    (hno : ∀ j, (∀ i, boxes j ≤ boxes i) → boxes j * p ≤ R ∨ boxes j = 1) :
    ∀ i, gstep k hk boxes p i ≤ R ∨ (gstep k hk boxes p i).Prime := by
  obtain ⟨j, hjmin, hjeq⟩ := gstep_min k hk boxes p
  rw [hjeq]; intro i
  rcases eq_or_ne i j with h | h
  · rw [h, Function.update_self]
    rcases hno j hjmin with hR | h1
    · exact Or.inl hR
    · rw [h1, one_mul]; exact Or.inr hp
  · rw [Function.update_of_ne h]; exact hgood i

/-- Greedy fold: process a whole list of primes, inserting each into a currently
minimal box. -/
noncomputable def gfold (k : ℕ) (hk : 0 < k) (b0 : Fin k → ℕ) (L : List ℕ) : Fin k → ℕ :=
  L.foldl (fun boxes p => gstep k hk boxes p) b0

/-- The greedy fold multiplies the total product by the product of the list. -/
lemma gfold_prod (k : ℕ) (hk : 0 < k) (b0 : Fin k → ℕ) (L : List ℕ) :
    ∏ i, gfold k hk b0 L i = (∏ i, b0 i) * L.prod := by
  induction L generalizing b0 with
  | nil => simp [gfold]
  | cons p t ih =>
    simp only [gfold, List.foldl_cons, List.prod_cons] at *
    rw [ih (gstep k hk b0 p), gstep_prod]
    ring

/-- The greedy fold preserves positivity of all boxes. -/
lemma gfold_pos (k : ℕ) (hk : 0 < k) (b0 : Fin k → ℕ) (L : List ℕ)
    (hb0 : ∀ i, 0 < b0 i) (hL : ∀ p ∈ L, 0 < p) : ∀ i, 0 < gfold k hk b0 L i := by
  induction L generalizing b0 with
  | nil => simpa [gfold] using hb0
  | cons p t ih =>
    simp only [gfold, List.foldl_cons]
    apply ih (gstep k hk b0 p) (gstep_pos k hk b0 p hb0 (hL p (List.mem_cons_self)))
    intro q hq; exact hL q (List.mem_cons_of_mem _ hq)

/-- The adjustable cutoff `R = η S_r(n)` tends to infinity. -/
lemma extraction_cutoff_tendsto_atTop (k : ℕ) (hk : 2 ≤ k) (η : ℝ) (hη : 0 < η) :
    Filter.Tendsto (fun n : ℕ => η * Sr k n) Filter.atTop Filter.atTop := by
  have ha : 0 < (2 : ℝ) / ((k : ℝ) + 1) := by positivity
  have h := powers_dominate_logs (2 / ((k : ℝ) + 1)) ha 2
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (2 / ((k : ℝ) + 1)) / Real.log n ^ 2) Filter.atTop Filter.atTop := by
    convert h.comp tendsto_natCast_atTop_atTop using 1
    ext n; simp
  exact h1.const_mul_atTop hη |>.congr fun n => by rfl

/-- Eventually the adjustable cutoff is at least one, as required by the
three-stage assignment argument. -/
lemma extraction_cutoff_eventually_one (k : ℕ) (hk : 2 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ η * Sr k n := by
  exact (extraction_cutoff_tendsto_atTop k hk η hη).eventually_ge_atTop 1

/-- Eventually the numerical easy-part allowance is large enough to absorb any
set of cardinality at most `k`. -/
lemma extraction_small_card_eventually (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (k : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η *
        ((n : ℝ) ^ ((2 : ℝ) / (k + 1)) / (Real.log n) ^ 2)) := by
  -- Since Nat.primeCounting n → ∞, eventually π(n) ≥ k
  -- The additional term is non-negative for n ≥ 2
  have h_inf : Filter.Tendsto Nat.primeCounting Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    -- Since primes are infinite, for any b there exists n with at least b primes ≤ n
    have h_inf_primes : Set.Infinite {p : ℕ | p.Prime} := Nat.infinite_setOf_prime
    -- Use that infinite sets have arbitrarily large finite subsets
    obtain ⟨S, hSsub, hScard⟩ : ∃ S : Finset ℕ, ↑S ⊆ {p | Nat.Prime p} ∧ S.card = b + 1 :=
      h_inf_primes.exists_subset_card_eq (b + 1)
    have hSprime : ∀ p ∈ S, p.Prime := fun p hp => hSsub hp
    -- Let i = max S, then for a ≥ i, all primes in S are ≤ a
    obtain ⟨i, hi⟩ : ∃ i, ∀ p ∈ S, p ≤ i := ⟨Finset.sup S id, fun p hp => Finset.le_sup (f := id) hp⟩
    use i
    intro a ha
    -- All primes in S are ≤ a, so primeCounting a ≥ S.card
    have hSub : S ⊆ Finset.filter Nat.Prime (Finset.range (a + 1)) := by
      intro p hp
      simp [Finset.mem_filter, Finset.mem_range]
      exact ⟨by linarith [hi p hp], hSprime p hp⟩
    calc b ≤ b + 1 := Nat.le_succ b
      _ = S.card := hScard.symm
      _ ≤ (Finset.filter Nat.Prime (Finset.range (a + 1))).card := Finset.card_le_card hSub
      _ = Nat.primeCounting a := by
          rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  -- The additional term is non-negative for n ≥ 2
  have h_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ 2 * (η * ((n : ℝ) ^ ((2 : ℝ) / (k + 1)) / (Real.log n) ^ 2)) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn_pos : (0 : ℝ) < n := by norm_cast; linarith
    have hlog_pos : 0 < Real.log n := Real.log_pos (by norm_cast)
    positivity
  -- Use that primeCounting n → ∞ and the second term is eventually non-negative
  filter_upwards [h_inf.eventually_ge_atTop k, h_nonneg] with n hn₁ hn₂
  have hn₁' : (k : ℝ) ≤ (Nat.primeCounting n : ℝ) := by exact_mod_cast hn₁
  linarith

/-- The extraction conclusion is immediate for a set with at most `k` elements,
provided the eventual numerical bound has already made room for those elements.
This isolates the small-cardinality branch of `extraction`; all hypergraph
conditions are vacuous because the hard part is empty. -/
lemma extraction_small_card (k n : ℕ) (η : ℝ) (A : Finset ℕ)
    (hcard : A.card ≤ k)
    (hnum : (k : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η *
      ((n : ℝ) ^ ((2 : ℝ) / (k + 1)) / (Real.log n) ^ 2))) :
    ∃ (Aeasy Ahard : Finset ℕ) (T : ℕ → Finset ℕ),
      A = Aeasy ∪ Ahard ∧ Disjoint Aeasy Ahard ∧
      (Aeasy.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η *
        ((n : ℝ) ^ ((2 : ℝ) / (k + 1)) / (Real.log n) ^ 2)) ∧
      (∀ a ∈ Ahard, (T a).card = k + 1 ∧
        (∀ p ∈ T a, p.Prime ∧ p ∣ a) ∧ (∏ p ∈ T a, p) ≤ a ∧ a ≤ n) ∧
      (∀ a ∈ Ahard, ∀ b ∈ Ahard, a ≠ b → ((T a) ∩ (T b)).card ≤ 1) := by
  refine ⟨A, ∅, fun _ => ∅, by simp, by simp, ?_⟩
  refine ⟨le_trans ?_ hnum, by simp, by simp⟩
  exact_mod_cast hcard

/-- A direct assignment form of `private_factor` for elements represented as
products of exactly `k` members of `B`.  Each element receives injectively a
member of `B` which divides it. -/
theorem mulk_private_assignment {k : ℕ} (B C : Finset ℕ)
    (hMulk : ∀ a ∈ C, Mulk B k a)
    (hprim : ∀ a ∈ C, ∀ D : Finset ℕ, D ⊆ C.erase a → D.card ≤ k →
      ¬ (a ∣ ∏ d ∈ D, d)) :
    ∃ φ : ℕ → ℕ, Set.InjOn φ C ∧
      (∀ a ∈ C, φ a ∈ B) ∧ (∀ a ∈ C, φ a ∣ a) := by
  -- For each a ∈ C, choose a factorization f a : Fin k → B with ∏ i, f a i = a
  choose! f hfB hfprod using fun a ha => hMulk a ha
  -- Define mu a x = #{i | f a i = x}
  let mu : ℕ → ℕ → ℕ := fun a x => (Finset.univ.filter (fun i => f a i = x)).card
  -- Verify mu satisfies the conditions for private_factor
  have hmu_fact : ∀ a ∈ C, (∏ x ∈ B, x ^ mu a x = a ∧ ∑ x ∈ B, mu a x = k) := by
    intro a ha
    constructor
    · -- ∏ x ∈ B, x ^ mu a x = a
      -- We need: ∏ x ∈ B, x ^ #{i | f a i = x} = ∏ i, f a i
      have himage : Finset.image (f a) Finset.univ ⊆ B := by
        intro y hy
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
        exact hfB a ha i
      have h1 : ∏ x ∈ B, x ^ mu a x = ∏ x ∈ Finset.image (f a) Finset.univ, x ^ mu a x := by
        rw [← Finset.prod_subset himage]
        intro x _ hx
        have hx0 : mu a x = 0 := by
          simp only [mu]
          rw [Finset.card_eq_zero]
          ext i
          by_cases h : f a i = x
          · exact absurd (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩) hx
          · simp [h]
        simp [hx0]
      have h2 : ∏ x ∈ Finset.image (f a) Finset.univ, x ^ mu a x = ∏ i, f a i := by
        simp only [mu]
        have hmaps : ∀ i ∈ Finset.univ, f a i ∈ Finset.image (f a) Finset.univ := fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)
        rw [← Finset.prod_fiberwise_of_maps_to hmaps (fun i => f a i)]
        refine Finset.prod_congr rfl ?_
        intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨j, rfl⟩ := hx
        rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
        simp [Finset.prod_const]
      rw [h1, h2, hfprod a ha]
    · -- ∑ x ∈ B, mu a x = k
      -- ∑ x ∈ B, #{i | f a i = x} = #{(i, x) | f a i = x} = k
      simp only [mu]
      -- Rewrite card as sum of indicator functions
      have h1 : ∑ x ∈ B, (Finset.univ.filter (fun i => f a i = x)).card =
                ∑ x ∈ B, ∑ i : Fin k, (if f a i = x then 1 else 0) := by
        congr 1; ext x
        rw [Finset.card_eq_sum_ones]
        simp
      rw [h1]
      -- Swap the order of summation
      rw [Finset.sum_comm]
      -- For each i, ∑ x ∈ B, if f a i = x then 1 else 0 = 1
      have h2 : ∀ i : Fin k, ∑ x ∈ B, (if f a i = x then 1 else 0) = 1 := by
        intro i
        have hmem : f a i ∈ B := hfB a ha i
        rw [Finset.sum_ite_eq]
        simp [hmem]
      simp [h2]
  -- Check if C is empty, a singleton, or has ≥ 2 elements
  by_cases hCempty : C = ∅
  · -- C is empty: trivial
    use fun _ => 1
    simp [hCempty]
  by_cases hCsingle : ∃ a, C = {a}
  · -- C is a singleton: construct φ directly
    obtain ⟨a₀, ha₀⟩ := hCsingle
    -- First show k ≥ 1 (otherwise hprim is contradicted)
    have hk_pos : k ≥ 1 := by
      by_contra hk0
      push_neg at hk0
      have hk0' : k = 0 := by omega
      have ha₀mem : a₀ ∈ C := by simp [ha₀]
      have hprod := (hmu_fact a₀ ha₀mem).1
      have hk' : ∑ x ∈ B, mu a₀ x = 0 := hk0' ▸ (hmu_fact a₀ ha₀mem).2
      have hall : ∀ x ∈ B, mu a₀ x = 0 := by
        intro x hx
        exact Nat.eq_zero_of_le_zero (le_trans (Finset.single_le_sum (fun y _ => Nat.zero_le (mu a₀ y)) hx) hk'.le)
      rw [Finset.prod_congr rfl (fun x hx => by rw [hall x hx])] at hprod
      simp at hprod
      have := hprim a₀ ha₀mem ∅ (by simp) (by simp [hk0'])
      simp [hprod] at this
    have ha₀mem : a₀ ∈ C := by simp [ha₀]
    use fun a => if a = a₀ then f a₀ ⟨0, hk_pos⟩ else 1
    refine ⟨?_, ?_, ?_⟩
    · -- InjOn
      simp [Set.InjOn, ha₀]
    · -- φ a ∈ B
      intro a ha
      have heq : a = a₀ := by rw [ha₀] at ha; simp at ha; exact ha
      simp [heq]
      exact hfB a₀ ha₀mem ⟨0, hk_pos⟩
    · -- φ a ∣ a
      intro a ha
      have heq : a = a₀ := by rw [ha₀] at ha; simp at ha; exact ha
      simp [heq]
      have hprod := hfprod a₀ ha₀mem
      conv_rhs => rw [hprod.symm]
      have hmem : (⟨0, hk_pos⟩ : Fin k) ∈ Finset.univ := Finset.mem_univ _
      calc f a₀ ⟨0, hk_pos⟩
          = ∏ i ∈ ({⟨0, hk_pos⟩} : Finset (Fin k)), f a₀ i := by simp
        _ ∣ ∏ i ∈ (Finset.univ : Finset (Fin k)), f a₀ i := by
            apply Finset.prod_dvd_prod_of_subset
            exact Finset.singleton_subset_iff.mpr hmem
  · -- C has ≥ 2 elements: use private_factor
    -- We already have private_factor available
    obtain ⟨φ, hφinj, hφB, hφprivate⟩ := private_factor B C mu hmu_fact hprim
    refine ⟨φ, hφinj, hφB, ?_⟩
    intro a ha
    -- Since C has ≥ 2 elements, there exists b ≠ a
    push_neg at hCsingle
    have hcard : 1 < C.card := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hCempty))) (Ne.symm (by intros h; obtain ⟨a', ha'⟩ := Finset.card_eq_one.mp h; exact hCsingle a' ha'))
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
    have hC2 : ∃ b ∈ C, b ≠ a := by
      by_cases hxa : x = a
      · exact ⟨y, hy, fun hya => hxy (hya ▸ hxa)⟩
      · exact ⟨x, hx, hxa⟩
    -- Since there exists b ≠ a, we have mu b (φ a) ≥ 0, so mu a (φ a) > mu b (φ a) ≥ 0
    obtain ⟨b, hbC, hbne⟩ := hC2
    have hprivate := hφprivate a ha b hbC hbne
    have hmu_pos : mu a (φ a) ≥ 1 := by omega
    -- Since phi a ∈ B and mu a (phi a) ≥ 1, we have phi a ^ (mu a (phi a)) ∣ a
    have hdiv : (φ a) ^ (mu a (φ a)) ∣ ∏ x ∈ B, x ^ mu a x := by
      apply Finset.dvd_prod_of_mem
      exact hφB a ha
    rw [hmu_fact a ha |>.1] at hdiv
    exact Nat.dvd_trans (dvd_pow_self _ (by linarith)) hdiv

/-- The finite basis used in the three-stage extraction assignment: all primes
at most `n`, together with all positive integers at most the real cutoff `R`. -/
noncomputable def extractionBasis (n : ℕ) (R : ℝ) : Finset ℕ :=
  primesLE n ∪ Finset.Icc 1 ⌊R⌋₊

lemma extractionBasis_pos {n : ℕ} {R : ℝ} {x : ℕ}
    (hx : x ∈ extractionBasis n R) : 0 < x := by
  rw [extractionBasis, Finset.mem_union] at hx
  rcases hx with hp | hx
  · exact (Finset.mem_filter.mp hp).2.pos
  · exact (Finset.mem_Icc.mp hx).1

lemma prime_mem_extractionBasis {n : ℕ} {R : ℝ} {p : ℕ}
    (hp : p.Prime) (hpn : p ≤ n) : p ∈ extractionBasis n R := by
  rw [extractionBasis, Finset.mem_union]
  left
  simp [primesLE, hp, hpn]

lemma small_mem_extractionBasis {n d : ℕ} {R : ℝ}
    (hd1 : 1 ≤ d) (hdR : (d : ℝ) ≤ R) : d ∈ extractionBasis n R := by
  rw [extractionBasis, Finset.mem_union]
  right
  rw [Finset.mem_Icc]
  exact ⟨hd1, Nat.le_floor hdR⟩

/-- The extraction basis has at most `π(n) + R` elements. -/
lemma extractionBasis_card_le (n : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    ((extractionBasis n R).card : ℝ) ≤ Nat.primeCounting n + R := by
  have hc : (extractionBasis n R).card ≤
      (primesLE n).card + (Finset.Icc 1 ⌊R⌋₊).card := by
    unfold extractionBasis
    exact Finset.card_union_le _ _
  have hfloor : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le (by positivity)
  have hicc : (Finset.Icc 1 ⌊R⌋₊).card ≤ ⌊R⌋₊ := by simp
  rw [primeCounting_eq_card]
  calc
    ((extractionBasis n R).card : ℝ) ≤
        ((primesLE n).card : ℝ) + (⌊R⌋₊ : ℝ) := by
      exact_mod_cast hc.trans (Nat.add_le_add_left hicc _)
    _ ≤ ((primesLE n).card : ℝ) + R := by linarith

/-- If, at some point in the greedy process, the minimal box `j0` would overflow
  past `R` when multiplied by the current prime `p` (`R < boxes j0 * p`), while
  the total product stays `≤ n`, then `R^k / p^{k-1} < n`. -/
lemma greedy_overflow (k : ℕ) (hk : 1 ≤ k) (R n : ℝ) (boxes : Fin k → ℝ) (p : ℝ)
    (j0 : Fin k) (hR : 0 < R) (hp : 0 < p)
    (hmin : ∀ i, boxes j0 ≤ boxes i)
    (hover : R < boxes j0 * p)
    (hprodle : (∏ i, boxes i) * p ≤ n) :
    R ^ k / p ^ (k - 1) < n := by
  haveI : NeZero k := ⟨by omega⟩
  have hm : R / p < boxes j0 := by rw [div_lt_iff₀ hp]; linarith
  have hall : ∀ i, R / p < boxes i := fun i => lt_of_lt_of_le hm (hmin i)
  have hprod_gt : (R / p) ^ k < ∏ i, boxes i := by
    calc (R / p) ^ k = ∏ _i : Fin k, (R / p) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ < ∏ i, boxes i :=
          Finset.prod_lt_prod_of_nonempty (fun i _ => by positivity)
            (fun i _ => hall i) Finset.univ_nonempty
  have h1 : (R / p) ^ k * p < n :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hprod_gt hp) hprodle
  have h2 : (R / p) ^ k * p = R ^ k / p ^ (k - 1) := by
    have hpk : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [div_pow, hpk]; field_simp
  rw [h2] at h1; exact h1

/-- If a positive integer has at most `k` prime factors with multiplicity, then
it is a product of exactly `k` members of the extraction basis: use its prime
factors and pad the remaining slots with `1`. -/
lemma primeFactors_mulk_extractionBasis {k n a : ℕ} {R : ℝ}
    (ha : 0 < a) (han : a ≤ n) (hR : 1 ≤ R)
    (hlen : a.primeFactorsList.length ≤ k) :
    Mulk (extractionBasis n R) k a := by
  -- Pad the prime factors list with 1s to get exactly k elements
  let m := a.primeFactorsList.length
  let pad := List.replicate (k - m) 1
  let factors := pad ++ a.primeFactorsList
  have hflen : factors.length = k := by
    simp [factors, pad]
    omega
  -- Show each factor is in extractionBasis n R
  have hfactors_mem : ∀ f ∈ factors, f ∈ extractionBasis n R := by
    intro f hf
    simp [factors] at hf
    rcases hf with hfpad | hfprime
    · -- f is a padding 1
      have : f = 1 := List.eq_of_mem_replicate hfpad
      rw [this]
      exact small_mem_extractionBasis (by norm_num) (by norm_num; linarith)
    · -- f is a prime factor
      have hfp : Nat.Prime f := hfprime.1
      have hfa : f ∣ a := hfprime.2.1
      apply prime_mem_extractionBasis hfp
      exact Nat.le_trans (Nat.le_of_dvd ha hfa) han
  -- Show the product of factors equals a
  have hfactors_prod : factors.prod = a := by
    simp [factors, pad]
    exact Nat.prod_primeFactorsList ha.ne'
  -- Construct the function from the list
  let boxes : Fin k → ℕ := fun i => factors[i]!
  -- Show that the product over boxes equals factors.prod
  have hboxes_prod : ∏ i : Fin k, boxes i = factors.prod := by
    simp only [boxes]
    rw [hflen.symm]
    simp [List.prod_eq_foldr]
  refine mulk_of_boxes boxes ?_ ?_
  · intro i
    simp only [boxes]
    apply hfactors_mem
    have hi : (i : ℕ) < factors.length := by rw [hflen]; exact i.is_lt
    simp [hi]
  · rw [hboxes_prod, hfactors_prod]

/-- A positive integer outside `Mul_k` has at least `k+1` prime factors,
counted with multiplicity. -/
lemma primeFactors_length_gt_of_not_mulk {k n a : ℕ} {R : ℝ}
    (ha : 0 < a) (han : a ≤ n) (hR : 1 ≤ R)
    (hnot : ¬ Mulk (extractionBasis n R) k a) :
    k < a.primeFactorsList.length := by
  contrapose! hnot
  exact primeFactors_mulk_extractionBasis ha han hR hnot

/-- Stages II and III admit compatible assignments into the common basis.
Stage II inherits the private-factor assignment on all basis-representable
members.  Stage III uses its defining private divisor; privacy makes the two
assignment images disjoint. -/
lemma extractionStages_later_assignments {A B : Finset ℕ} {k R : ℕ}
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    (hApos : ∀ a ∈ A, 0 < a)
    (hsmall : ∀ d : ℕ, 0 < d → d ≤ R → d ∈ B) :
    ∃ φ₂ φ₃ : ℕ → ℕ,
      Set.InjOn φ₂ (extractionStageTwo A B k R) ∧
      Set.InjOn φ₃ (extractionStageThree A B k R) ∧
      (∀ a ∈ extractionStageTwo A B k R, φ₂ a ∈ B ∧ φ₂ a ∣ a) ∧
      (∀ a ∈ extractionStageThree A B k R,
        φ₃ a ∈ B ∧ PrivateDivisor A a (φ₃ a)) ∧
      Disjoint ((extractionStageTwo A B k R).image φ₂)
        ((extractionStageThree A B k R).image φ₃) := by
  -- First, get the Stage III assignment using privateDivisor_assignment
  have hStageIII_subset : extractionStageThree A B k R ⊆ A := by
    intro a ha
    simp [extractionStageThree] at ha
    exact ha.1.1
  -- For each a ∈ Stage III, obtain the small private divisor (≤ R)
  have hStageIII_priv_small : ∀ a ∈ extractionStageThree A B k R,
      ∃ d ≤ R, d ∈ B ∧ PrivateDivisor A a d := by
    intro a ha
    simp [extractionStageThree] at ha
    obtain ⟨d, hdR, hpriv⟩ := ha.2
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hpriv.1 (hApos a ha.1.1)
    exact ⟨d, hdR, hsmall d hdpos hdR, hpriv⟩
  choose! φ₃ hφ₃_R hφ₃_B hφ₃_priv using hStageIII_priv_small
  -- φ₃ is injective on Stage III: if φ₃ a = φ₃ b, then a = b (by privacy)
  have hφ₃_inj : Set.InjOn φ₃ (extractionStageThree A B k R) := by
    intro a ha b hb hab
    by_contra hne
    -- φ₃ a = φ₃ b = d is a private divisor of both a and b
    have hd_a := (hφ₃_priv a ha).1
    have hd_b := (hφ₃_priv b hb).1
    have hd_b' : φ₃ a ∣ b := by rw [hab]; exact hd_b
    -- b ∈ A.erase a since b ∈ A and a ≠ b
    have hbEA : b ∈ A.erase a := by
      rw [Finset.mem_erase]
      exact ⟨fun h => hne h.symm, hStageIII_subset hb⟩
    -- φ₃ a is private to a, so ¬(φ₃ a ∣ b)
    have hnotdiv := (hφ₃_priv a ha).2 b hbEA
    exact hnotdiv hd_b'
  -- For Stage II, each element is a product of k elements from B
  -- We need to assign each to a factor in B injectively
  -- Use the fact that for a = ∏ i, f i with f i ∈ B, each f i divides a
  -- Define φ₂ by picking a canonical factor
  -- Handle the case k = 0 separately: Stage II has at most one element (all products are 1)
  by_cases hk0 : k = 0
  · -- When k = 0, Stage II ⊆ {1}, so trivially injective
    have hStageII_sub_one : extractionStageTwo A B 0 R ⊆ {1} := by
      intro a ha
      rw [extractionStageTwo] at ha
      simp only [Finset.sdiff_eq_filter, Finset.mem_filter] at ha
      obtain ⟨⟨_, ⟨f, _, rfl⟩⟩, _⟩ := ha
      exact Finset.mem_singleton.mpr rfl
    -- Any function is injective on a singleton or empty set
    have hcard_II_le_one : (extractionStageTwo A B 0 R).card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
      have ha1 : a = 1 := Finset.mem_singleton.mp (hStageII_sub_one ha)
      have hb1 : b = 1 := Finset.mem_singleton.mp (hStageII_sub_one hb)
      rw [ha1, hb1])
    -- For k = 0, Stage II ⊆ {1}. We need 1 ∈ B (from hsmall if R ≥ 1)
    -- First, show 1 ∈ B: we have 0 < 1, and if R ≥ 1 then 1 ≤ R
    -- If R = 0, then Stage I = ∅ (no element has private prime power ≤ 0), so Stage II = A.filter (· = 1)
    -- which is either ∅ or {1}. If {1}, then 1 ∈ A and 1 ∉ Stage I.
    -- We need to handle this carefully.
    -- Key insight: when k = 0, DistPrimitive 0 A implies 1 ∉ A (since 1 ∣ 1)
    -- Therefore Stage II = A ∩ {1} = ∅, making the statement vacuously true
    have h1_notin_A : 1 ∉ A := by
      intro h1in
      have := hprim 1 h1in (∅ : Finset ℕ) (by simp) (by rw [hk0]; simp)
      simp at this
    have hStageII_empty : extractionStageTwo A B 0 R = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro ⟨a, ha⟩
      have ha1 : a = 1 := Finset.mem_singleton.mp (hStageII_sub_one ha)
      have hSub : extractionStageTwo A B 0 R ⊆ A := by
        intro x hx
        simp [extractionStageTwo] at hx
        exact hx.1.1
      exact h1_notin_A (ha1 ▸ hSub ha)
    -- With Stage II = ∅, all Stage II conditions are vacuously true
    use fun _ => 1, φ₃
    simp_all
  · -- When k ≥ 1 (i.e., k > 0)
    -- Stage II elements are products of k ≥ 1 elements from B (i.e., Mulk B k)
    -- Use mulk_private_assignment to get an injective φ₂
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    -- First, show Stage II ⊆ A
    have hStageII_sub : extractionStageTwo A B k R ⊆ A := by
      intro a ha
      simp [extractionStageTwo] at ha
      exact ha.1.1
    -- Every Stage II element is Mulk B k
    have hMulk : ∀ a ∈ extractionStageTwo A B k R, Mulk B k a := by
      intro a ha
      simp [extractionStageTwo] at ha
      obtain ⟨⟨_, f, hfB, rfl⟩, _⟩ := ha
      exact mulk_of_boxes f hfB rfl
    -- Use mulk_private_assignment
    obtain ⟨φ₂, hφ₂_inj, hφ₂_B, hφ₂_dvd⟩ := mulk_private_assignment B (extractionStageTwo A B k R)
      hMulk (by
        -- Need: ∀ a ∈ Stage II, ∀ D ⊆ Stage II.erase a, D.card ≤ k → ¬(a ∣ ∏ d ∈ D, d)
        -- This follows from DistPrimitive k A since Stage II ⊆ A
        intro a ha D hD_sub hDcard
        have haA : a ∈ A := hStageII_sub ha
        have hD_sub_A : D ⊆ A.erase a := by
          intro d hd
          exact Finset.mem_erase.mpr ⟨fun heq => Finset.mem_erase.mp (hD_sub hd) |>.1 heq, hStageII_sub (Finset.mem_erase.mp (hD_sub hd) |>.2)⟩
        -- DistPrimitive requires card = k, but we have card ≤ k
        -- We use monotonicity: if a ∣ ∏ d ∈ D, d and D ⊆ D', then a ∣ ∏ d ∈ D', d
        -- So if D.card < k, extend D to D' with D'.card = k
        have hcard_A_erase : (A.erase a).card ≥ k := by
          have : (A.erase a).card = A.card - 1 := Finset.card_erase_of_mem haA
          omega
        by_cases hDk : D.card = k
        · exact hprim a haA D hD_sub_A hDk
        · -- D.card < k, extend D to D' with D'.card = k
          have hDk' : D.card < k := lt_of_le_of_ne hDcard hDk
          have hdiff_card : (k - D.card) ≤ ((A.erase a) \ D).card := by
            have h1 : (A.erase a \ D).card = (A.erase a).card - D.card := by
              rw [Finset.card_sdiff]
              congr 1
              rw [Finset.inter_comm, Finset.inter_eq_right.mpr hD_sub_A]
            rw [h1]
            omega
          obtain ⟨E, hED, hEcard⟩ := Finset.exists_subset_card_eq hdiff_card
          -- D' = D ∪ E has card k and D' ⊆ A.erase a
          let D' := D ∪ E
          have hDD' : D ⊆ D' := Finset.subset_union_left
          have hD'sub : D' ⊆ A.erase a := Finset.union_subset hD_sub_A (hED.trans Finset.sdiff_subset)
          have hD'disj : Disjoint D E := by
            rw [Finset.disjoint_left]
            intro x hxD hxE
            exact Finset.mem_sdiff.mp (hED hxE) |>.2 hxD
          have hD'card : D'.card = k := by
            rw [show D'.card = D.card + E.card from Finset.card_union_of_disjoint hD'disj]
            rw [hEcard]
            omega
          -- Apply hprim to D'
          have hnotdiv' := hprim a haA D' hD'sub hD'card
          -- If a ∣ ∏ d ∈ D, d, then a ∣ ∏ d ∈ D', d (monotonicity)
          have hdvd' : ∏ d ∈ D, d ∣ ∏ d ∈ D', d := by
            apply Finset.prod_dvd_prod_of_subset
            exact hDD'
          exact fun havd => hnotdiv' (dvd_trans havd hdvd')
  )
    -- Package φ₂ and φ₃ into the existential
    use φ₂, φ₃
    refine ⟨hφ₂_inj, hφ₃_inj, ?_, ?_, ?_⟩
    · exact fun a ha => ⟨hφ₂_B a ha, hφ₂_dvd a ha⟩
    · exact fun a ha => ⟨hφ₃_B a ha, hφ₃_priv a ha⟩
    · -- Disjointness: Stage III images are private divisors, which don't divide Stage II elements
      rw [Finset.disjoint_left]
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      intro hxD
      obtain ⟨b, hb, hxb⟩ := Finset.mem_image.mp hxD
      -- φ₃ b is a private divisor of b, so ¬(φ₃ b ∣ a) if a ≠ b
      have hne : a ≠ b := by
        intro heq
        rw [heq] at ha
        -- a ∈ Stage II and a ∈ Stage III, but Stage II ∩ Stage III = ∅
        have hdisj := (extractionStages_partition A B k R).2.2.2.1
        exact Finset.disjoint_left.mp hdisj ha hb
      have haEA : a ∈ A.erase b := by
        rw [Finset.mem_erase]
        exact ⟨hne, hStageII_sub ha⟩
      have hnotdiv := (hφ₃_priv b hb).2 a haEA
      exact hnotdiv (hxb ▸ hφ₂_dvd a ha)

/-- Cardinality bookkeeping for the canonical three-stage extraction.
Once Stages II and III have injective assignments into the common basis with
disjoint images, the union of all assigned elements has size at most the number
of primes below the cutoff plus the size of the basis.  Stage I is bounded
directly by `extractionStageOne_card_le`. -/
lemma extractionStages_easy_card_le (A B : Finset ℕ) (k R : ℕ)
    (φ₂ φ₃ : ℕ → ℕ)
    (hi₂ : Set.InjOn φ₂ (extractionStageTwo A B k R))
    (hi₃ : Set.InjOn φ₃ (extractionStageThree A B k R))
    (hm₂ : ∀ a ∈ extractionStageTwo A B k R, φ₂ a ∈ B)
    (hm₃ : ∀ a ∈ extractionStageThree A B k R, φ₃ a ∈ B)
    (himg : Disjoint ((extractionStageTwo A B k R).image φ₂)
      ((extractionStageThree A B k R).image φ₃)) :
    (extractionStageOne A R ∪ extractionStageTwo A B k R ∪
      extractionStageThree A B k R).card ≤ Nat.primeCounting R + B.card := by
  -- Bound the union of Stages I, II, III
  have h1 : (extractionStageOne A R ∪ extractionStageTwo A B k R ∪ extractionStageThree A B k R).card
      ≤ (extractionStageOne A R).card + (extractionStageTwo A B k R).card + (extractionStageThree A B k R).card := by
    calc (extractionStageOne A R ∪ extractionStageTwo A B k R ∪ extractionStageThree A B k R).card
        ≤ (extractionStageOne A R ∪ extractionStageTwo A B k R).card + (extractionStageThree A B k R).card :=
            Finset.card_union_le _ _
      _ ≤ (extractionStageOne A R).card + (extractionStageTwo A B k R).card + (extractionStageThree A B k R).card := by
            gcongr; exact Finset.card_union_le _ _
  have h2 : (extractionStageTwo A B k R).card + (extractionStageThree A B k R).card
      ≤ B.card := by
    calc (extractionStageTwo A B k R).card + (extractionStageThree A B k R).card
        = ((extractionStageTwo A B k R).image φ₂).card + ((extractionStageThree A B k R).image φ₃).card := by
            rw [Finset.card_image_of_injOn hi₂, Finset.card_image_of_injOn hi₃]
      _ = ((extractionStageTwo A B k R).image φ₂ ∪ (extractionStageThree A B k R).image φ₃).card := by
            rw [Finset.card_union_of_disjoint himg]
      _ ≤ B.card := by
            exact Finset.card_le_card (Finset.union_subset
              (Finset.image_subset_iff.mpr hm₂) (Finset.image_subset_iff.mpr hm₃))
  calc (extractionStageOne A R ∪ extractionStageTwo A B k R ∪ extractionStageThree A B k R).card
      ≤ (extractionStageOne A R).card + (extractionStageTwo A B k R).card + (extractionStageThree A B k R).card := h1
    _ = (extractionStageOne A R).card + ((extractionStageTwo A B k R).card + (extractionStageThree A B k R).card) := by ring
    _ ≤ (extractionStageOne A R).card + B.card := by gcongr
    _ ≤ Nat.primeCounting R + B.card := by gcongr; exact extractionStageOne_card_le A R

/-- The canonical three-stage construction gives a bounded easy part and a
hard remainder satisfying exactly the three survivor properties used by the
number-theoretic core of extraction. -/
lemma extractionStages_prepartition {A B : Finset ℕ} {k R : ℕ}
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    (hApos : ∀ a ∈ A, 0 < a)
    (hsmall : ∀ d : ℕ, 0 < d → d ≤ R → d ∈ B) :
    let Aeasy := extractionStageOne A R ∪ extractionStageTwo A B k R ∪
      extractionStageThree A B k R
    let Ahard := extractionStageHard A B k R
    A = Aeasy ∪ Ahard ∧ Disjoint Aeasy Ahard ∧
      Aeasy.card ≤ Nat.primeCounting R + B.card ∧
      (∀ a ∈ Ahard,
        ¬ (∃ f : Fin k → ℕ, (∀ i, f i ∈ B) ∧ ∏ i, f i = a)) ∧
      (∀ a ∈ Ahard, ¬ HasPrivatePrimePowerBelow A R a) ∧
      (∀ a ∈ Ahard, ¬ HasPrivateDivisorBelow A R a) := by
  -- Extract properties from extractionStages_partition
  have part := extractionStages_partition A B k R
  obtain ⟨hpart, hdisj12, hdisj13, hdisj23, hhard2, hhard1, hhard3⟩ := part
  -- Define Aeasy and Ahard
  let Aeasy := extractionStageOne A R ∪ extractionStageTwo A B k R ∪ extractionStageThree A B k R
  let Ahard := extractionStageHard A B k R
  -- The partition gives A = Aeasy ∪ Ahard
  have heq : A = Aeasy ∪ Ahard := by
    simp only [Aeasy, Ahard]
    exact hpart
  -- Disjointness of Aeasy and Ahard
  have hdisj : Disjoint Aeasy Ahard := by
    rw [show Ahard = A \ (extractionStageOne A R ∪ extractionStageTwo A B k R ∪ extractionStageThree A B k R) from rfl]
    exact Finset.disjoint_sdiff
  -- Cardinality bound
  have hcard : Aeasy.card ≤ Nat.primeCounting R + B.card := by
    obtain ⟨φ₂, φ₃, hi₂, hi₃, hm₂, hm₃, himg⟩ := extractionStages_later_assignments hprim hcard hApos hsmall
    exact extractionStages_easy_card_le A B k R φ₂ φ₃ hi₂ hi₃ (fun a ha => (hm₂ a ha).1) (fun a ha => (hm₃ a ha).1) himg
  -- Properties of hard elements
  have hhard2' : ∀ a ∈ Ahard, ¬∃ f : Fin k → ℕ, (∀ i, f i ∈ B) ∧ ∏ i, f i = a := hhard2
  have hhard1' : ∀ a ∈ Ahard, ¬HasPrivatePrimePowerBelow A R a := hhard1
  have hhard3' : ∀ a ∈ Ahard, ¬HasPrivateDivisorBelow A R a := hhard3
  exact ⟨heq, hdisj, hcard, hhard2', hhard1', hhard3'⟩

/-- Applying the canonical three extraction stages with integer cutoff `⌊R⌋₊`
and basis `extractionBasis n R` gives the required real cardinality estimate.
Every hard survivor is outside `Mul_k` and therefore has more than `k` prime
factors, counted with multiplicity. -/
lemma extraction_prepartition_at_real_cutoff {k n : ℕ} {R : ℝ}
    (hR : 1 ≤ R) (A : Finset ℕ) (hprim : DistPrimitive k A)
    (hcard : k + 1 ≤ A.card) (hsub : A ⊆ Finset.Icc 1 n) :
    let B := extractionBasis n R
    ∃ Aeasy Ahard : Finset ℕ,
      A = Aeasy ∪ Ahard ∧ Disjoint Aeasy Ahard ∧
      (Aeasy.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * R ∧
      (∀ a ∈ Ahard, ¬ Mulk B k a) ∧
      (∀ a ∈ Ahard, k < a.primeFactorsList.length) ∧
      (∀ a ∈ Ahard, ¬ HasPrivatePrimePowerBelow A ⌊R⌋₊ a) ∧
      (∀ a ∈ Ahard, ¬ HasPrivateDivisorBelow A ⌊R⌋₊ a) := by
  classical
  let B := extractionBasis n R
  have hApos : ∀ a ∈ A, 0 < a := by
    intro a ha
    exact (Finset.mem_Icc.mp (hsub ha)).1
  have hBpos : ∀ x ∈ B, 0 < x := by
    intro x hx
    exact extractionBasis_pos hx
  have hsmall : ∀ d : ℕ, 0 < d → d ≤ ⌊R⌋₊ → d ∈ B := by
    intro d hd hdR
    apply small_mem_extractionBasis (n := n) (R := R) hd
    exact (Nat.cast_le.mpr hdR).trans (Nat.floor_le (by linarith))
  obtain ⟨hpart, hdisj, hcardEasy, hnot, hpow, hdiv⟩ :=
    extractionStages_prepartition (A := A) (B := B) (k := k)
      (R := ⌊R⌋₊) hprim hcard hApos hsmall
  let Aeasy := extractionStageOne A ⌊R⌋₊ ∪
    extractionStageTwo A B k ⌊R⌋₊ ∪ extractionStageThree A B k ⌊R⌋₊
  let Ahard := extractionStageHard A B k ⌊R⌋₊
  refine ⟨Aeasy, Ahard, hpart, hdisj, ?_, ?_, ?_, ?_, ?_⟩
  · have hb := extractionBasis_card_le n R hR
    have hpiNat : Nat.primeCounting ⌊R⌋₊ ≤ ⌊R⌋₊ := by
      rw [primeCounting_eq_card]
      have hs : primesLE ⌊R⌋₊ ⊆ Finset.Icc 1 ⌊R⌋₊ := by
        intro p hp
        simp [primesLE] at hp ⊢
        exact ⟨hp.2.pos, hp.1⟩
      exact (Finset.card_le_card hs).trans_eq (by simp)
    have hpi : (Nat.primeCounting ⌊R⌋₊ : ℝ) ≤ R := by
      exact (Nat.cast_le.mpr hpiNat).trans (Nat.floor_le (by linarith))
    have hcardEasyR :
        ((extractionStageOne A ⌊R⌋₊ ∪ extractionStageTwo A B k ⌊R⌋₊ ∪
          extractionStageThree A B k ⌊R⌋₊).card : ℝ) ≤
          Nat.primeCounting ⌊R⌋₊ + B.card := by
      exact_mod_cast hcardEasy
    dsimp only [Aeasy]
    linarith
  · simpa only [Ahard, Mulk] using hnot
  · intro a ha
    have haA : a ∈ A := by
      rw [hpart]
      exact Finset.mem_union_right _ ha
    exact primeFactors_length_gt_of_not_mulk (hApos a haA)
      ((Finset.mem_Icc.mp (hsub haA)).2) hR (hnot a ha)
  · simpa only [Ahard] using hpow
  · simpa only [Ahard] using hdiv

/-- Eventual three-stage decomposition at the adjustable extraction cutoff.  This
reduces `extraction_large_card` to proving distinctness and pairwise linearity of
the selected prime factors of the hard survivors. -/
lemma extraction_prepartition_eventually (k : ℕ) (hk : 2 ≤ k)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → DistPrimitive k A → k + 1 ≤ A.card →
      ∃ Aeasy Ahard : Finset ℕ,
        A = Aeasy ∪ Ahard ∧ Disjoint Aeasy Ahard ∧
        (Aeasy.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η * Sr k n) ∧
        (∀ a ∈ Ahard, ¬ Mulk (extractionBasis n (η * Sr k n)) k a) ∧
        (∀ a ∈ Ahard, k < a.primeFactorsList.length) ∧
        (∀ a ∈ Ahard,
          ¬ HasPrivatePrimePowerBelow A ⌊η * Sr k n⌋₊ a) ∧
        (∀ a ∈ Ahard, ¬ HasPrivateDivisorBelow A ⌊η * Sr k n⌋₊ a) := by
  filter_upwards [extraction_cutoff_eventually_one k hk η hη] with n hR
  intro A hsub hprim hcard
  simpa only using
    (extraction_prepartition_at_real_cutoff (R := η * Sr k n)
      hR A hprim hcard hsub)

/-- Failure of Stage III supplies another member divisible by every small
divisor of the survivor. -/
lemma witness_of_no_private_divisor {A : Finset ℕ} {R a d : ℕ}
    (hno : ¬ HasPrivateDivisorBelow A R a)
    (hdR : d ≤ R) (hda : d ∣ a) :
    ∃ b ∈ A.erase a, d ∣ b := by
  by_contra h
  push_neg at h
  refine hno ⟨d, hdR, ⟨hda, h⟩⟩

/-- A hard element cannot be decomposed into at most `k` pairwise coprime
factors if every factor divides some other member of the primitive set.  This
packages the repeated `dedup`/`padding` contradiction used in both the
selected-factor distinctness and pairwise-linearity arguments. -/
lemma no_coprime_witnessed_factorization {k m : ℕ} {A : Finset ℕ}
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    {a : ℕ} (ha : a ∈ A) (d : Fin m → ℕ)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (d i) (d j))
    (hprod : ∏ i, d i = a)
    (hwitness : ∀ i, ∃ b ∈ A.erase a, d i ∣ b)
    (hm : m ≤ k) : False := by
  -- For each i, choose a witness b_i ∈ A.erase a such that d i ∣ b_i
  choose f hf using hwitness
  -- Define B' := image f univ, a subset of A.erase a
  let B' := Finset.image f Finset.univ
  -- Use dedup: since d i are pairwise coprime and d i ∣ f i, we have ∏ d i ∣ ∏ c ∈ image f univ, c
  have hdedup : ∏ i, d i ∣ ∏ c ∈ B', c := dedup d f hcop (fun i => (hf i).2)
  -- B' ⊆ A.erase a
  have hB'_sub : B' ⊆ A.erase a := Finset.image_subset_iff.mpr (fun i _ => (hf i).1)
  -- Pad B' to get a set of size k
  have hcard_erase : (A.erase a).card = A.card - 1 := Finset.card_erase_of_mem ha
  have hB'_card_le : B'.card ≤ k := by
    have : B'.card ≤ Finset.card (Finset.univ : Finset (Fin m)) := Finset.card_image_le
    simp at this
    linarith
  have hk_le_erase : k ≤ (A.erase a).card := by omega
  obtain ⟨B'', hB'_sub_B'', hB''_sub, hB''_card⟩ : ∃ B'' : Finset ℕ, B' ⊆ B'' ∧ B'' ⊆ A.erase a ∧ B''.card = k :=
    Finset.exists_subsuperset_card_eq hB'_sub hB'_card_le hk_le_erase
  -- Extend divisibility: ∏ c ∈ B', c ∣ ∏ c ∈ B'', c
  have hdiv : ∏ c ∈ B', c ∣ ∏ c ∈ B'', c := by
    apply Finset.prod_dvd_prod_of_subset (f := fun c => c) (s := B') (t := B'') hB'_sub_B''
  -- So a ∣ ∏ c ∈ B'', c
  have ha_div : a ∣ ∏ c ∈ B'', c := by rw [← hprod]; exact dvd_trans hdedup hdiv
  -- Apply DistPrimitive to get contradiction
  exact hprim a ha B'' hB''_sub hB''_card ha_div

/-- The witnessed-factorization contradiction with an arbitrary finite index
 type.  This avoids repeatedly transporting naturally indexed collections to
 `Fin m` when the factors are canonically indexed by a finite set. -/
lemma no_coprime_witnessed_factorization_fintype {k : ℕ} {A : Finset ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    {a : ℕ} (ha : a ∈ A) (d : ι → ℕ)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (d i) (d j))
    (hprod : ∏ i, d i = a)
    (hwitness : ∀ i, ∃ b ∈ A.erase a, d i ∣ b)
    (hm : Fintype.card ι ≤ k) : False := by
  let e := Fintype.equivFin ι
  let d' : Fin (Fintype.card ι) → ℕ := fun i => d (e.symm i)
  have hcop' : ∀ i j, i ≠ j → Nat.Coprime (d' i) (d' j) := by
    intro i j hij
    simp only [d']
    have : e.symm i ≠ e.symm j := by
      intro heq
      apply hij
      exact e.symm.injective heq
    exact hcop _ _ this
  have hprod' : ∏ i : Fin (Fintype.card ι), d' i = a := by
    rw [← hprod]
    apply Finset.prod_equiv e.symm
    · intro i; simp
    · intro i _; simp [d']
  have hwitness' : ∀ i, ∃ b ∈ A.erase a, d' i ∣ b := by
    intro i
    exact hwitness (e.symm i)
  exact no_coprime_witnessed_factorization hprim hcard ha d' hcop' hprod' hwitness' hm

/-- If the distinct primes occurring in a selected prefix number fewer than
`k`, grouping equal primes into prime powers and adjoining a coprime small
remainder gives at most `k` witnessed factors.  Hence this configuration is
impossible for a hard survivor. -/
lemma no_small_grouped_prefix_of_card_lt {k R : ℕ} {A : Finset ℕ}
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    {a rem : ℕ} (ha : a ∈ A) (L : List ℕ)
    (hprime : ∀ p ∈ L, p.Prime)
    (hprod : L.prod * rem = a)
    (hcop : Nat.Coprime L.prod rem)
    (hprimeSmall : ∀ p ∈ L, p ≤ R)
    (hremSmall : rem ≤ R)
    (hnoPow : ¬ HasPrivatePrimePowerBelow A R a)
    (hnoDiv : ¬ HasPrivateDivisorBelow A R a)
    (hcardDistinct : L.toFinset.card < k) : False := by
  -- Let S = L.toFinset, the set of distinct primes in L
  let S := L.toFinset
  -- For each p ∈ S, let d(p) = p ^ (multiplicity of p in L)
  let d : S → ℕ := fun ⟨p, hp⟩ => p ^ L.count p
  -- d is pairwise coprime (distinct primes)
  have hd_cop : ∀ i j : S, i ≠ j → Nat.Coprime (d i) (d j) := by
    intro ⟨p, hp⟩ ⟨q, hq⟩ hij
    have hp' : p ∈ L := List.mem_toFinset.mp hp
    have hq' : q ∈ L := List.mem_toFinset.mp hq
    have hpq : p ≠ q := by
      rintro rfl
      exact hij rfl
    exact Nat.coprime_pow_primes _ _ (hprime p hp') (hprime q hq') hpq
  -- The product of d over S equals L.prod
  -- Helper: product of x^(L.count x) over L.toFinset equals L.prod
  have list_prod_eq_pow_count : ∀ (l : List ℕ), ∏ x ∈ l.toFinset, x ^ l.count x = l.prod := by
    intro l
    induction l with
    | nil => simp
    | cons head tail ih =>
      simp only [List.prod_cons, List.toFinset_cons]
      by_cases hhead : head ∈ tail.toFinset
      · -- head ∈ tail
        rw [Finset.insert_eq_of_mem hhead]
        -- We need to show: ∏ x ∈ tail.toFinset, x ^ (head :: tail).count x = head * tail.prod
        -- Split tail.toFinset = {head} ∪ (tail.toFinset \ {head})
        have h1 : tail.toFinset = insert head (tail.toFinset \ {head}) := by
          ext x; simp [Finset.mem_insert, Finset.mem_sdiff]
          by_cases hx : x = head <;> simp [hx]
          · exact List.mem_toFinset.mp hhead
        rw [h1, Finset.prod_insert (by simp)]
        -- Now goal: head ^ (head :: tail).count head * ∏ x ∈ tail.toFinset \ {head}, x ^ (head :: tail).count x = head * tail.prod
        have hcount_succ : (head :: tail).count head = tail.count head + 1 := by simp
        rw [hcount_succ]; simp [pow_succ, mul_comm]
        -- For x ≠ head, (head :: tail).count x = tail.count x
        have h2 : ∏ x ∈ tail.toFinset \ {head}, x ^ (head :: tail).count x =
            ∏ x ∈ tail.toFinset \ {head}, x ^ tail.count x := by
          apply Finset.prod_congr rfl
          intro x hx
          have hx_ne : head ≠ x := by
            simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
            exact Ne.symm hx.2
          simp only [List.count_cons_of_ne hx_ne]
        rw [h2]
        -- Also split tail.prod
        have h3 : tail.prod = head ^ tail.count head * ∏ x ∈ tail.toFinset \ {head}, x ^ tail.count x := by
          rw [← ih]
          have hsimpl : insert head (tail.toFinset \ {head}) \ {head} = tail.toFinset \ {head} := by
            ext x; simp [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
          conv_lhs => rw [h1, Finset.prod_insert (by simp : head ∉ tail.toFinset \ {head})]
        rw [h3]
        ring
      · -- head ∉ tail
        rw [Finset.prod_insert (by simpa using hhead)]
        have hcount_zero : tail.count head = 0 := List.count_eq_zero.mpr (by simpa using hhead)
        have hcount_succ : (head :: tail).count head = 1 := by simp [hcount_zero]
        have hprod_eq : ∏ x ∈ tail.toFinset, x ^ (head :: tail).count x =
            ∏ x ∈ tail.toFinset, x ^ tail.count x := by
          apply Finset.prod_congr rfl
          intro x hx
          have hx_ne : x ≠ head := fun heq => hhead (heq ▸ hx)
          simp [List.count_cons_of_ne hx_ne.symm]
        rw [hcount_succ, hprod_eq, ← ih]; simp [pow_one]
  have hd_prod : ∏ p : S, d p = L.prod := by
    simp only [d]
    rw [Finset.prod_coe_sort (f := fun x : ℕ => x ^ List.count x L)]
    exact list_prod_eq_pow_count L
  -- Each d(p) divides L.prod
  have hd_dvd_L : ∀ p : S, d p ∣ L.prod := by
    intro ⟨p, hp⟩
    simp only [d]
    have h1 : p ^ L.count p ∣ L.prod := by
      have aux : ∀ (l : List ℕ) (q : ℕ), q ^ l.count q ∣ l.prod := by
        intro l
        induction l with
        | nil => simp
        | cons x l ih =>
          intro q
          have hcount : (x :: l).count q = l.count q + (if x = q then 1 else 0) := by
            simp [List.count_cons, beq_iff_eq]
          rw [hcount, List.prod_cons]
          split_ifs with hqx
          · -- x = q, so q^(l.count q + 1) = q * q^(l.count q)
            rw [Nat.pow_add, Nat.pow_one]
            rw [hqx]
            ring_nf
            exact Nat.mul_dvd_mul_left q (ih q)
          · -- x ≠ q, so q^(l.count q + 0) = q^(l.count q) divides x * l.prod
            simp only [add_zero]
            exact dvd_trans (ih q) (dvd_mul_left _ _)
      exact aux L p
    exact h1
  -- Each d(p) divides a
  have hd_dvd : ∀ p : S, d p ∣ a := by
    intro ⟨p, hp⟩
    exact dvd_trans (hd_dvd_L ⟨p, hp⟩) (hprod ▸ dvd_mul_right _ _)
  -- By hnoPow, each d(p) divides some element of A.erase a
  have hd_witness : ∀ p : S, ∃ b ∈ A.erase a, d p ∣ b := by
    intro ⟨p, hp⟩
    simp only [d]
    have hp' : p ∈ L := List.mem_toFinset.mp hp
    by_contra hno_witness
    push_neg at hno_witness
    apply hnoPow
    refine ⟨p, L.count p, hprime p hp', ?_, hd_dvd ⟨p, hp⟩, hprimeSmall p hp', hno_witness⟩
    exact Nat.pos_of_ne_zero (by simp [List.count_eq_zero, hp'])
  -- We have |S| < k, so |S| + 1 ≤ k if needed
  -- Case split on whether rem = 1
  by_cases Hem : rem = 1
  · -- If rem = 1, then a = L.prod, and we have |S| < k factors
    have ha_eq : a = L.prod := by rw [← hprod, Hem]; ring
    have hcardS : Fintype.card S ≤ k := by
      simp only [S, Fintype.card_coe]
      omega
    exact no_coprime_witnessed_factorization_fintype hprim hcard ha d hd_cop (by rw [ha_eq]; rw [hd_prod]) hd_witness hcardS
  · -- If rem > 1, then we need to add rem as an additional factor
    -- rem is a private divisor by hnoDiv
    have hrem_gt : 1 < rem := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨by
      by_contra hrem0
      rw [hrem0] at hprod
      have ha_zero : a = 0 := hprod.symm
      -- If 0 ∈ A, then DistPrimitive is violated since 0 divides everything
      have hcard_erase : (A.erase 0).card ≥ k := by
        have h0mem : 0 ∈ A := ha_zero ▸ ha
        have := Finset.card_erase_of_mem h0mem
        omega
      obtain ⟨B, hB_sub, hB_card⟩ : ∃ B : Finset ℕ, B ⊆ A.erase 0 ∧ B.card = k := by
        exact Finset.exists_subset_card_eq hcard_erase
      have hprod_ne : ∏ b ∈ B, b ≠ 0 := by
        intro h
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨b, hb, hb'⟩ := h
        have hb'' : b ∈ A.erase 0 := hB_sub hb
        simp at hb''
        exact hb''.1 hb'
      -- hcop : Nat.Coprime L.prod 0 means L.prod = 1
      have hLprod : L.prod = 1 := by
        have : L.prod.gcd 0 = L.prod := Nat.gcd_zero_right L.prod
        rw [Nat.coprime_iff_gcd_eq_one] at hcop
        simp_all
      -- a = L.prod * 0 = 0, but also a = L.prod * rem (from hprod)
      -- Actually hprod : L.prod * rem = a, so a = 1 * 0 = 0
      -- We need to derive False from the fact that a = 0 contradicts something
      -- Since L.prod = 1, L is empty or L consists of 1s. But L consists of primes ≥ 2.
      -- So L must be empty.
      have hL_empty : L = [] := by
        by_contra hL_ne
        have hL_prod_ge : L.prod ≥ 2 := by
          rcases L with _ | ⟨x, xs⟩
          · contradiction
          · have hx : x ∈ x :: xs := by simp
            have hx2 := (hprime x hx).two_le
            have hxsp : xs.prod ≥ 1 := by
              have hne : 0 ∉ xs := fun h => (hprime 0 (List.mem_cons_of_mem _ h)).ne_zero rfl
              exact Nat.one_le_iff_ne_zero.mpr (List.prod_ne_zero hne)
            rw [List.prod_cons]
            exact Nat.mul_le_mul hx2 hxsp
        linarith
      -- If L = [], then S = ∅, so we can't use the original approach
      -- But we still have a = 0 ∈ A, which should be impossible
      exfalso
      -- 0 cannot be in a DistPrimitive set of positive integers
      -- Because if 0 ∈ A, take B = any k elements from A.erase 0
      -- When rem = 0, we need a witness b ∈ A.erase a with 0 ∣ b
      -- But 0 ∣ b iff b = 0, and b ∈ A.erase 0 means b ≠ 0
      -- So no such witness exists, contradiction
      have hdvd_a : 0 ∣ a := by rw [← hprod]; exact dvd_mul_left _ _
      -- hdvd_a : 0 ∣ 0, which is true
      -- But witness_of_no_private_divisor requires rem ∣ a and rem > 0 implicitly
      -- Actually, let's just show that no element of A.erase 0 is divisible by 0
      have hno_zero_in_erase : ∀ b ∈ A.erase 0, ¬(0 ∣ b) := by
        intro b hb
        simp at hb
        intro h
        exact hb.1 (Nat.eq_zero_of_zero_dvd h)
      -- We have ha : 0 ∈ A, so A.card ≥ 1
      -- We need to show False
      -- The issue is that the theorem structure doesn't immediately give us False
      -- Let's use that if a = 0, then for any d dividing a, we need d to divide some b ∈ A.erase a
      -- But d = 0 divides a = 0, and 0 ∣ b iff b = 0
      -- Since b ∈ A.erase 0, b ≠ 0, so 0 doesn't divide any b ∈ A.erase 0
      -- If L is nonempty, we have a prime p ≤ R, so R ≥ 2 ≥ 1
      -- If L is empty, L.prod = 1, so a = 1 * 0 = 0
      -- In either case, 1 ≤ R or L = []
      have hR_ge_one : 1 ≤ R := by
        by_contra hR0
        have hR_eq_zero : R = 0 := Nat.le_zero.mp (le_of_not_gt hR0)
        -- All primes in L are ≤ 0, so L must be empty
        have hL_empty' : L = [] := by
          by_contra hL_ne
          match L with
          | [] => contradiction
          | p :: ps =>
            have hp_prime := hprime p (by simp)
            have hp_le : p ≤ R := hprimeSmall p (by simp)
            rw [hR_eq_zero] at hp_le
            exact hp_prime.ne_zero (by linarith)
        -- L = [] means L.prod = 1
        simp [hL_empty'] at hprod
        have hk_pos : 0 < k := by
          have hLfin_empty : L.toFinset = ∅ := by simp [hL_empty']
          have hcard' : L.toFinset.card < k := hcardDistinct
          rw [hLfin_empty] at hcard'
          omega
        -- With k ≥ 1 and A.card ≥ k + 1 ≥ 2, A has at least 2 elements
        have hA_card_ge_two : 2 ≤ A.card := by omega
        -- If 0 ∈ A and A.card ≥ 2, there exists b ∈ A.erase 0
        have hA_erase_nonempty : Finset.Nonempty (A.erase 0) := by
          by_contra h_empty
          rw [Finset.not_nonempty_iff_eq_empty] at h_empty
          have hA_sub : A ⊆ {0} := by
            intro x hx
            by_contra hx0
            have : x ∈ A.erase 0 := Finset.mem_erase_of_ne_of_mem (by simp [Finset.mem_singleton] at hx0; exact hx0) hx
            simp [h_empty] at this
          have : A.card ≤ 1 := Finset.card_le_card hA_sub
          omega
        obtain ⟨b, hb⟩ := hA_erase_nonempty
        have hb_mem : b ∈ A := Finset.mem_of_mem_erase hb
        have hb_ne : b ≠ 0 := Finset.mem_erase.mp hb |>.1
        -- Show DistPrimitive is violated: for a = b, B ⊆ A.erase b with |B| = k, we have b ∣ ∏ B
        -- Since 0 ∈ A.erase b, we can choose B containing 0
        have h0_in_Aerb : 0 ∈ A.erase b := by
          rw [Finset.mem_erase]
          exact ⟨hb_ne.symm, ha_zero ▸ ha⟩
        have hAerb_card : (A.erase b).card ≥ k := by
          have := Finset.card_erase_of_mem hb_mem
          omega
        -- Add 0 to a k-1 sized subset of (A.erase b) \ {0}
        have h_card_minus_0 : (A.erase b \ {0}).card = (A.erase b).card - 1 := by
          have h0_in_A : 0 ∈ A := ha_zero ▸ ha
          have hsub : {0} ⊆ A.erase b := by simp [hb_ne.symm, h0_in_A]
          rw [Finset.card_sdiff_of_subset hsub, Finset.card_singleton]
        have hk1 : k - 1 + 1 = k := by omega
        have h_subset_card : (A.erase b \ {0}).card ≥ k - 1 := by
          simp only [h_card_minus_0]
          omega
        obtain ⟨C, hC_sub, hC_card⟩ := Finset.exists_subset_card_eq h_subset_card
        let B := C ∪ {0}
        have hB_sub : B ⊆ A.erase b := by
          rw [Finset.union_subset_iff]
          exact ⟨hC_sub.trans (by simp), by simp [h0_in_Aerb]⟩
        have hB_card : B.card = k := by
          have h0_not_in_C : 0 ∉ C := by
            intro hc
            have := hC_sub hc
            simp at this
          rw [Finset.card_union_of_disjoint (by simp [h0_not_in_C] : Disjoint C {0}), Finset.card_singleton, hC_card]
          omega
        have hdiv : b ∣ ∏ b ∈ B, b := by
          have h0_in_B : 0 ∈ B := by simp [B]
          exact dvd_trans (Nat.dvd_zero b) (Finset.dvd_prod_of_mem _ h0_in_B)
        exact (hprim b hb_mem B hB_sub hB_card) hdiv
      -- Now we have hR_ge_one : 1 ≤ R
      -- We can use witness_of_no_private_divisor: since rem = 0, we need rem ∣ a
      -- But HasPrivateDivisorBelow A R 0 requires d ≤ R, d ∣ 0, and ¬(d ∣ b) for all b ∈ A.erase 0
      -- Since R ≥ 1, we can take d = 1: 1 ≤ R, 1 ∣ 0, and 1 ∣ b for all b
      -- Actually 1 divides everything, so 1 is not a private divisor
      -- We need a different approach: rem = 0 means a = 0, and 0 divides everything
      -- But witness_of_no_private_divisor needs a nonzero divisor
      -- Actually the issue is that rem = 0 is not a valid private divisor
      -- Let's derive False from ha_zero : a = 0 directly
      -- Since a = 0 ∈ A and R ≥ 1, we check HasPrivateDivisorBelow A R 0
      -- d is a private divisor if d ≤ R, d ∣ 0, and ∀ b ∈ A.erase 0, ¬(d ∣ b)
      -- Since R ≥ 1, any d ≤ R divides 0
      -- But for d to NOT divide some b ∈ A.erase 0, we need d > 1 and b not divisible by d
      -- Actually 1 divides everything, so 1 is never a private divisor
      -- For d > 1, if A.erase 0 contains only multiples of d, then d is a private divisor
      -- But A.erase 0 is nonempty (since A.card ≥ 2 and 0 ∈ A), and contains various elements
      -- Let's just show that 0 ∈ A leads to contradiction via a different route
      -- Actually: if a = 0 ∈ A, then we already have a contradiction from the theorem setup
      -- because the theorem assumes a is a "hard survivor" which shouldn't include 0
      -- Let's derive False by showing rem = 0 leads to issues with hnoDiv
      -- HasPrivateDivisorBelow A R 0: ∃ d ≤ R, d ∣ 0, ∀ b ∈ A.erase 0, ¬(d ∣ b)
      -- For R ≥ 1 and nonempty A.erase 0, we can find such d if A.erase 0 is finite
      -- Actually this is getting complicated. Let's just note that a = 0 is problematic.
      -- Since L = [] (from hL_empty), S = ∅, and S.card = 0 < k means k ≥ 1
      -- A.card ≥ k + 1 ≥ 2, so A.erase 0 is nonempty
      -- Let b be some element of A.erase 0
      -- Then b ∈ A and b ≠ 0
      -- We need to derive False
      -- The key insight: a = 0 ∈ A contradicts the spirit of the theorem
      -- But formally, we need to find the contradiction
      -- Let's check: does HasPrivateDivisorBelow A R 0 hold?
      -- We need d ≤ R with d ∣ 0 (always true) and ¬(d ∣ b) for some b ∈ A.erase 0
      -- Since R ≥ 1 and A.erase 0 is nonempty, pick any b ∈ A.erase 0 with b > 0
      -- Take d = b: d ≤ R (from hremSmall? no, b is not necessarily ≤ R)
      -- Hmm, we don't have that b ≤ R
      -- Actually the structure of the proof suggests a = 0 should be impossible
      -- Let me check if there's a simpler contradiction
      -- 0 is a private divisor below R: 0 ≤ R, 0 ∣ 0, and 0 ∣ b is false for all b ∈ A.erase 0
      rw [ha_zero] at hnoDiv
      exact hnoDiv ⟨0, by omega, dvd_zero 0, hno_zero_in_erase⟩
    , Hem⟩
    have hrem_witness : ∃ b ∈ A.erase a, rem ∣ b := by
      have hdvd_a : rem ∣ a := by rw [← hprod]; exact dvd_mul_left _ _
      exact witness_of_no_private_divisor hnoDiv hremSmall hdvd_a
    -- Define extended index type T = S ⊕ Unit
    let T := S ⊕ Unit
    let d' : T → ℕ := fun t => match t with
      | Sum.inl p => d p
      | Sum.inr _ => rem
    -- d' is pairwise coprime
    have hd'_cop : ∀ i j : T, i ≠ j → Nat.Coprime (d' i) (d' j) := by
      intro i j hij
      cases i with
      | inl p =>
        cases j with
        | inl q =>
          simp only [d']
          apply hd_cop p q
          intro heq
          exact hij (by simp [heq])
        | inr _ =>
          simp only [d']
          exact Nat.Coprime.coprime_dvd_left (hd_dvd_L p) hcop
      | inr _ =>
        cases j with
        | inl q =>
          simp only [d']
          exact (Nat.Coprime.coprime_dvd_left (hd_dvd_L q) hcop).symm
        | inr _ => exact absurd rfl hij
    -- ∏ t : T, d' t = a
    have hd'_prod : ∏ t : T, d' t = a := by
      have hsplit : ∏ t : T, d' t = (∏ p : S, d p) * rem := by
        conv_lhs => rw [Fintype.prod_sum_type]
        simp [d']
      rw [hsplit, hd_prod, hprod]
    -- Each d'(t) has a witness
    have hd'_witness : ∀ t : T, ∃ b ∈ A.erase a, d' t ∣ b := by
      intro t
      cases t with
      | inl p => exact hd_witness p
      | inr _ => exact hrem_witness
    -- Fintype.card T ≤ k
    have hcardT : Fintype.card T ≤ k := by
      simp only [T, Fintype.card_sum, Fintype.card_unit, Fintype.card_coe]
      linarith
    exact no_coprime_witnessed_factorization_fintype hprim hcard ha d' hd'_cop hd'_prod hd'_witness hcardT

/-- Two selected primes cannot both divide another member once the selected
prime set has size `k+1` and one of the remaining selected primes can absorb the
coprime remainder below the Stage-III cutoff.  The factors are `p*q`, the
single selected primes other than `p,q,ell`, and `ell*rem`. -/
lemma no_two_selected_primes_witnessed {k R : ℕ} {A : Finset ℕ}
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    {a b rem p q ell : ℕ} (ha : a ∈ A) (hb : b ∈ A.erase a)
    (S : Finset ℕ) (hScard : S.card = k + 1)
    (hSprime : ∀ x ∈ S, x.Prime)
    (hprod : (∏ x ∈ S, x) * rem = a)
    (hcop : Nat.Coprime (∏ x ∈ S, x) rem)
    (hp : p ∈ S) (hq : q ∈ S) (hell : ell ∈ S)
    (hpq : p ≠ q) (hpell : p ≠ ell) (hqell : q ≠ ell)
    (hpq_b : p * q ∣ b)
    (hsmall : ∀ x ∈ S, x ≤ R)
    (hellrem : ell * rem ≤ R)
    (hnoDiv : ¬ HasPrivateDivisorBelow A R a) : False := by
  -- Key observation: ell * rem ≤ R and ell * rem ∣ a, so by hnoDiv,
  -- ell * rem must divide some b' ∈ A.erase a
  have hell_rem_dvd_a : ell * rem ∣ a := by
    rw [← hprod]
    apply mul_dvd_mul_right
    exact Finset.dvd_prod_of_mem _ hell
  have hell_rem_le_R : ell * rem ≤ R := hellrem
  -- Get a witness for ell * rem
  obtain ⟨b', hb'_erase, hb'_div⟩ := witness_of_no_private_divisor hnoDiv hell_rem_le_R hell_rem_dvd_a
  -- Define T = S \ {p, q, ell}
  let T := S \ {p, q, ell}
  -- |T| = k - 2
  have hp_S : p ∈ S := hp
  have hq_S : q ∈ S := hq
  have hell_S : ell ∈ S := hell
  have hcard_pqell : ({p, q, ell} : Finset ℕ).card = 3 := by
    have h1 : ({p, q, ell} : Finset ℕ) = ((({p, q} : Finset ℕ) ∪ ({ell} : Finset ℕ))) := by ext x; simp
    rw [h1, Finset.card_union_of_disjoint]
    · rw [Finset.card_pair hpq, Finset.card_singleton]
    · rw [Finset.disjoint_singleton_right]
      simp [Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hpell.symm, hqell.symm⟩
  have hsub : {p, q, ell} ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hTcard : T.card = k - 2 := by
    have := Finset.card_sdiff (s := {p, q, ell}) (t := S)
    have hinter : ({p, q, ell} : Finset ℕ) ∩ S = {p, q, ell} := Finset.inter_eq_left.mpr hsub
    rw [hinter, hcard_pqell] at this
    rw [this, hScard]
    rfl
  -- k ≥ 2 because S has k+1 ≥ 3 elements (p, q, ell are distinct)
  have hk_ge_2 : 2 ≤ k := by
    have : S.card ≥ 3 := by
      calc S.card ≥ ({p, q, ell} : Finset ℕ).card := Finset.card_le_card hsub
        _ = 3 := hcard_pqell
    omega
  -- Build the witness function: for each element, find a witness in A.erase a
  -- For primes x ∈ S: x ≤ R and x ∣ a, so witness_of_no_private_divisor applies
  have hwitness_all : ∀ x ∈ S, ∃ c ∈ A.erase a, x ∣ c := by
    intro x hx
    have hx_dvd : x ∣ (∏ x ∈ S, x) * rem := dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hx) _
    rw [hprod] at hx_dvd
    exact witness_of_no_private_divisor hnoDiv (hsmall x hx) hx_dvd
  -- Define the factors:
  -- d 0 = p * q
  -- d 1 = ell * rem
  -- d (2 + i) = the i-th element of T
  -- For this, we need an enumeration of T
  have hT_card : T.card = k - 2 := hTcard
  haveI : Fintype T := Fintype.ofFinset T (by simp)
  -- Use Finset.orderEmbOfFin to get an embedding
  -- Define the factor function
  let Temb : Fin (k - 2) → ℕ := fun i => T.orderEmbOfFin (by simp [hT_card] : T.card = k - 2) i
  let idx : ∀ i : Fin k, (i.val ≥ 2) → Fin (k - 2)
    | i, hi => ⟨i.val - 2, by omega⟩
  let d : Fin k → ℕ := fun i =>
    if hi2 : (i : ℕ) < 2 then
      if hi0 : (i : ℕ) = 0 then p * q else ell * rem
    else
      Temb (idx i (by omega : (i : ℕ) ≥ 2))
  -- Now prove the three key properties:
  -- 1. The factors are pairwise coprime
  -- 2. Their product equals a
  -- 3. Each factor witnesses divisibility
  have hd_coprime : ∀ i j, i ≠ j → Nat.Coprime (d i) (d j) := by
    intro i j hij
    -- First establish some useful facts
    have hp_prime : p.Prime := hSprime p hp_S
    have hq_prime : q.Prime := hSprime q hq_S
    have hell_prime : ell.Prime := hSprime ell hell_S
    have hcop_rem : Nat.Coprime (∏ x ∈ S, x) rem := hcop
    have hrem_coprime_to_each : ∀ x ∈ S, Nat.Coprime x rem := by
      intro x hx
      exact Nat.Coprime.coprime_dvd_left (Finset.dvd_prod_of_mem _ hx) hcop_rem
    have Temb_mem : (∀ i : Fin (k - 2), Temb i ∈ T) := fun i => by simp [Temb]
    have hT_disjoint : Disjoint T {p, q, ell} := Finset.disjoint_left.mpr (fun x hx => (Finset.mem_sdiff.mp hx).2)

    have hell_not_in_T : ell ∉ T := by simp [T]
    have hp_not_in_T : p ∉ T := by simp [T]
    have hq_not_in_T : q ∉ T := by simp [T]
    -- Helper: d 0 = p * q
    have hd0 : d ⟨0, by omega⟩ = p * q := by simp [d]
    -- Helper: d 1 = ell * rem
    have hd1 : d ⟨1, by omega⟩ = ell * rem := by simp [d]
    -- Coprimality of distinct primes
    have hcop_p_ell : Nat.Coprime p ell := Nat.coprime_primes hp_prime hell_prime |>.mpr (by intro heq; exact hpell heq)
    have hcop_q_ell : Nat.Coprime q ell := Nat.coprime_primes hq_prime hell_prime |>.mpr (by intro heq; exact hqell heq)
    -- Coprime to rem for each prime in S
    have hcop_p_rem : Nat.Coprime p rem := hrem_coprime_to_each p hp_S
    have hcop_q_rem : Nat.Coprime q rem := hrem_coprime_to_each q hq_S
    -- d 0 = p * q, d 1 = ell * rem
    have hd0_eq : ∀ i : Fin k, (i : ℕ) = 0 → d i = p * q := fun i hi => by simp [d, hi]
    have hd1_eq : ∀ i : Fin k, (i : ℕ) = 1 → d i = ell * rem := fun i hi => by simp [d, hi]
    -- Coprime products
    have hcop_p_ellrem : Nat.Coprime p (ell * rem) := Nat.Coprime.mul_right hcop_p_ell hcop_p_rem
    have hcop_q_ellrem : Nat.Coprime q (ell * rem) := Nat.Coprime.mul_right hcop_q_ell hcop_q_rem
    have hcop_pq_ellrem : Nat.Coprime (p * q) (ell * rem) := Nat.Coprime.mul_left hcop_p_ellrem hcop_q_ellrem
    -- Coprimality with T elements
    have hcop_to_T : ∀ x ∈ T, Nat.Coprime (p * q) x := by
      intro x hx
      have hx_S : x ∈ S := Finset.mem_sdiff.mp hx |>.1
      have hx_prime : x.Prime := hSprime x hx_S
      have hx_ne_p : p ≠ x := fun h => hp_not_in_T (h ▸ hx)
      have hx_ne_q : q ≠ x := fun h => hq_not_in_T (h ▸ hx)
      exact Nat.Coprime.mul_left (Nat.coprime_primes hp_prime hx_prime |>.mpr hx_ne_p)
        (Nat.coprime_primes hq_prime hx_prime |>.mpr hx_ne_q)
    -- Coprimality of T elements with ell and rem
    have hcop_T_ell : ∀ x ∈ T, Nat.Coprime ell x := by
      intro x hx
      have hx_S : x ∈ S := Finset.mem_sdiff.mp hx |>.1
      have hx_prime : x.Prime := hSprime x hx_S
      exact Nat.coprime_primes hell_prime hx_prime |>.mpr (fun h => hell_not_in_T (h ▸ hx))
    have hcop_T_rem : ∀ x ∈ T, Nat.Coprime x rem := fun x hx => hrem_coprime_to_each x (Finset.mem_sdiff.mp hx |>.1)
    have hcop_ellrem_to_T : ∀ x ∈ T, Nat.Coprime (ell * rem) x := by
      intro x hx
      exact Nat.Coprime.mul_left (hcop_T_ell x hx) (hcop_T_rem x hx |>.symm)
    -- Distinctness of T elements
    have hdist_T : ∀ i j : Fin (k - 2), i ≠ j → Temb i ≠ Temb j := by
      intro i j hij heq
      apply hij
      simp [Temb] at heq
      exact heq
    have hcop_T_T : ∀ i j : Fin (k - 2), i ≠ j → Nat.Coprime (Temb i) (Temb j) := by
      intro i j hij
      have hi_T := Temb_mem i
      have hj_T := Temb_mem j
      have hne := hdist_T i j hij
      have hi_prime : (Temb i).Prime := hSprime _ (Finset.mem_sdiff.mp hi_T |>.1)
      have hj_prime : (Temb j).Prime := hSprime _ (Finset.mem_sdiff.mp hj_T |>.1)
      exact Nat.coprime_primes hi_prime hj_prime |>.mpr hne
    -- Now do case analysis on i and j
    rcases Nat.lt_or_ge (i : ℕ) 2 with hi2 | hi2
    · rcases Nat.lt_or_ge (j : ℕ) 2 with hj2 | hj2
      · -- Both < 2
        have hi0_or_1 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
        have hj0_or_1 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
        rcases hi0_or_1 with hi0 | hi1
        · rcases hj0_or_1 with hj0 | hj1
          · exact absurd (Fin.ext (hi0.trans hj0.symm)) hij
          · rw [hd0_eq i hi0, hd1_eq j hj1]
            exact hcop_pq_ellrem
        · rcases hj0_or_1 with hj0 | hj1
          · rw [hd1_eq i hi1, hd0_eq j hj0]
            exact hcop_pq_ellrem.symm
          · exact absurd (Fin.ext (hi1.trans hj1.symm)) hij
      · -- i < 2, j ≥ 2
        have hj_ge2 : (j : ℕ) ≥ 2 := hj2
        have hdj : d j = Temb (idx j hj_ge2) := by simp [d, dif_neg (by omega : ¬(j : ℕ) < 2)]
        rcases Nat.lt_or_ge (i : ℕ) 1 with hi1 | hi1
        · have hi0 : (i : ℕ) = 0 := by omega
          rw [hd0_eq i hi0, hdj]
          apply hcop_to_T
          exact Temb_mem _
        · have hi1' : (i : ℕ) = 1 := by omega
          rw [hd1_eq i hi1', hdj]
          apply hcop_ellrem_to_T
          exact Temb_mem _
    · -- i ≥ 2
      have hi_ge2 : (i : ℕ) ≥ 2 := hi2
      have hdi : d i = Temb (idx i hi_ge2) := by simp [d, dif_neg (by omega : ¬(i : ℕ) < 2)]
      rcases Nat.lt_or_ge (j : ℕ) 2 with hj2 | hj2
      · rcases Nat.lt_or_ge (j : ℕ) 1 with hj1 | hj1
        · have hj0 : (j : ℕ) = 0 := by omega
          rw [hdi, hd0_eq j hj0]
          exact (hcop_to_T _ (Temb_mem _)).symm
        · have hj1' : (j : ℕ) = 1 := by omega
          rw [hdi, hd1_eq j hj1']
          exact (hcop_ellrem_to_T _ (Temb_mem _)).symm
      · -- Both ≥ 2
        have hj_ge2 : (j : ℕ) ≥ 2 := hj2
        have hdj : d j = Temb (idx j hj_ge2) := by simp [d, dif_neg (by omega : ¬(j : ℕ) < 2)]
        have hne : idx i hi_ge2 ≠ idx j hj_ge2 := by simp [idx]; omega
        rw [hdi, hdj]
        exact hcop_T_T _ _ hne
  have hd_prod : ∏ i, d i = a := by
    -- Rewrite `a` using `hprod`
    rw [← hprod]
    -- Key: ∏ x ∈ S, x = p * q * ell * ∏ x ∈ T, x
    have hS_eq : S = {p, q, ell} ∪ T := by
      conv_lhs => rw [← Finset.union_sdiff_of_subset hsub]
    -- Product over S
    have hprodS : ∏ x ∈ S, x = p * q * ell * ∏ x ∈ T, x := by
      rw [hS_eq]
      rw [Finset.prod_union]
      · simp [Finset.prod_insert, hpq, hpell, hqell]; left; ring_nf
      · exact Finset.disjoint_sdiff
    -- Product over T equals product over Temb
    have hTprod_eq : ∏ x ∈ T, x = ∏ i : Fin (k - 2), Temb i := by
      symm
      set emb := T.orderEmbOfFin hT_card with emb_def
      have h1 : ∀ i : Fin (k - 2), Temb i = emb i := fun i => rfl
      simp_rw [h1]
      have himage : Finset.image emb Finset.univ = T := by
        ext x
        simp [emb]
      rw [← himage, Finset.prod_image emb.injective.injOn]
    -- Now show ∏ i, d i = (p * q) * (ell * rem) * ∏ i, Temb i
    have hd_split : ∏ i : Fin k, d i = (p * q) * (ell * rem) * ∏ i : Fin (k - 2), Temb i := by
      -- d at key indices
      have hd0 : d ⟨0, by omega⟩ = p * q := by simp [d]
      have hd1 : d ⟨1, by omega⟩ = ell * rem := by simp [d]
      have hdi_ge2 : ∀ i : Fin (k - 2), d ⟨i + 2, by omega⟩ = Temb i := by
        intro i
        simp [d, Temb]
        rfl
      -- Define sets for partitioning
      let s01 : Finset (Fin k) := {⟨0, by omega⟩, ⟨1, by omega⟩}
      let sge2 : Finset (Fin k) := Finset.image (fun i : Fin (k-2) => ⟨i + 2, by omega⟩) Finset.univ
      have hunion : (Finset.univ : Finset (Fin k)) = s01 ∪ sge2 := by
        ext i
        simp [s01, sge2]
        have hik : i.val < k := i.isLt
        by_cases hi2 : i.val < 2
        · have : i.val = 0 ∨ i.val = 1 := by omega
          rcases this with h0 | h1
          · exact Or.inl (Fin.ext h0)
          · exact Or.inr (Or.inl (Fin.ext h1))
        · have hi2' : i.val ≥ 2 := by omega
          have heq : i.val = i.val - 2 + 2 := by omega
          exact Or.inr (Or.inr ⟨⟨i.val - 2, by omega⟩, Fin.ext heq.symm⟩)
      have hdisj : Disjoint s01 sge2 := by
        simp [Finset.disjoint_left, s01, sge2]
      rw [show ∏ i : Fin k, d i = ∏ i ∈ s01 ∪ sge2, d i by rw [hunion]]
      rw [Finset.prod_union hdisj]
      rw [show ∏ i ∈ s01, d i = d ⟨0, by omega⟩ * d ⟨1, by omega⟩ by simp [s01, hd0, hd1]]
      rw [Finset.prod_image]
      · simp_rw [hd0, hd1, hdi_ge2]
      · intro i _ j _ hij
        exact Fin.ext (by simpa using hij)
    rw [hd_split, ← hTprod_eq, hprodS]
    ring
  have hd_witness : ∀ i, ∃ c ∈ A.erase a, d i ∣ c := by
    intro i
    -- Case analysis on i
    have hTB : ∀ x ∈ T, x ∈ S := by
      intro x hx
      exact Finset.mem_sdiff.mp hx |>.1
    -- d 0 = p * q witnesses via b
    -- d 1 = ell * rem witnesses via b'
    -- d (2+i) = element of T witnesses via hwitness_all
    by_cases hi2 : (i : ℕ) < 2
    · -- i = 0 or i = 1
      by_cases hi0 : (i : ℕ) = 0
      · -- i = 0: d 0 = p * q, witnesses via b
        have hdi : d i = p * q := by
          simp only [d, hi0]
          rfl
        use b
        exact ⟨hb, hdi ▸ hpq_b⟩
      · -- i = 1: d 1 = ell * rem, witnesses via b'
        have hi1 : (i : ℕ) = 1 := by omega
        have hi2' : (i : ℕ) < 2 := by simp [hi1]
        have hdi : d i = ell * rem := by
          simp only [d, hi2', dif_pos]
          simp [hi0]
        use b'
        exact ⟨hb'_erase, hdi ▸ hb'_div⟩
    · -- i ≥ 2: d i = Temb (idx i hi_ge_2) ∈ T
      push_neg at hi2
      have hi_ge_2 : (i : ℕ) ≥ 2 := hi2
      have hdi : d i = Temb (idx i hi_ge_2) := by
        simp only [d, dif_neg (by omega : ¬(i : ℕ) < 2)]
      have hx_in_T : Temb (idx i hi_ge_2) ∈ T := by simp [Temb]
      have hx_in_S : Temb (idx i hi_ge_2) ∈ S := hTB _ hx_in_T
      rw [hdi]
      exact hwitness_all _ hx_in_S
  exact no_coprime_witnessed_factorization hprim hcard ha d hd_coprime hd_prod hd_witness le_rfl

/-- The local two-prime contradiction yields pairwise linearity for a whole
family once every selected pair leaves a third selected prime that can absorb
the corresponding coprime remainder below the cutoff. -/
lemma selected_prime_sets_pairwise_linear_of_absorbing
    {k R : ℕ} {A H : Finset ℕ} (S : ℕ → Finset ℕ) (rem : ℕ → ℕ)
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    (hHA : H ⊆ A)
    (hScard : ∀ a ∈ H, (S a).card = k + 1)
    (hSprime : ∀ a ∈ H, ∀ p ∈ S a, p.Prime)
    (hprod : ∀ a ∈ H, (∏ p ∈ S a, p) * rem a = a)
    (hcop : ∀ a ∈ H, Nat.Coprime (∏ p ∈ S a, p) (rem a))
    (hsmall : ∀ a ∈ H, ∀ p ∈ S a, p ≤ R)
    (hnoDiv : ∀ a ∈ H, ¬ HasPrivateDivisorBelow A R a)
    (habsorb : ∀ a ∈ H, ∀ p ∈ S a, ∀ q ∈ S a, p ≠ q →
      ∃ ell ∈ S a, ell ≠ p ∧ ell ≠ q ∧ ell * rem a ≤ R) :
    ∀ a ∈ H, ∀ b ∈ H, a ≠ b → ((S a) ∩ (S b)).card ≤ 1 := by
  intro a ha b hb hab
  by_contra hle
  have hinter : 1 < ((S a) ∩ (S b)).card := lt_of_not_ge hle
  rw [Finset.one_lt_card_iff] at hinter
  obtain ⟨p, q, hpq, hp, hq⟩ := hinter
  have hpa := (Finset.mem_inter.mp hpq).1
  have hpb := (Finset.mem_inter.mp hpq).2
  have hqa := (Finset.mem_inter.mp hp).1
  have hqb := (Finset.mem_inter.mp hp).2
  have hqp : q ≠ p := hq.symm
  obtain ⟨ell, hella, hellp, hellq, hellrem⟩ :=
    habsorb a ha p hpa q hqa hqp.symm
  have hbA : b ∈ A.erase a := Finset.mem_erase.mpr ⟨hab.symm, hHA hb⟩
  have hp_dvd_b : p ∣ b := by
    rw [← hprod b hb]
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hpb) _
  have hq_dvd_b : q ∣ b := by
    rw [← hprod b hb]
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hqb) _
  have hpq_cop : Nat.Coprime p q :=
    (Nat.coprime_primes (hSprime a ha p hpa) (hSprime a ha q hqa)).mpr hqp.symm
  exact no_two_selected_primes_witnessed hprim hcard (hHA ha) hbA (S a)
    (hScard a ha) (hSprime a ha) (hprod a ha) (hcop a ha)
    hpa hqa hella hqp.symm hellp.symm hellq.symm
    (hpq_cop.mul_dvd_of_dvd_of_dvd hp_dvd_b hq_dvd_b)
    (hsmall a ha) hellrem (hnoDiv a ha)

/-- Prime factors with multiplicity in the nonincreasing order used in the
argument.  Mathlib's `primeFactorsList` is nondecreasing, so it must be reversed. -/
def descendingPrimeFactors (a : ℕ) : List ℕ := a.primeFactorsList.reverse

lemma descendingPrimeFactors_length (a : ℕ) :
    (descendingPrimeFactors a).length = a.primeFactorsList.length := by
  simp [descendingPrimeFactors]

lemma descendingPrimeFactors_prod (a : ℕ) :
    (descendingPrimeFactors a).prod = a.primeFactorsList.prod := by
  simp [descendingPrimeFactors]

/-- The reversed prime-factor list is nonincreasing, matching the ordering used
in the extraction argument. -/
lemma descendingPrimeFactors_sortedGE (a : ℕ) :
    (descendingPrimeFactors a).SortedGE := by
  rw [descendingPrimeFactors, List.sortedGE_reverse]
  exact Nat.primeFactorsList_sorted a

/-- Later entries of the descending prime-factor list are no larger than earlier
entries.  This index-level form is convenient for the prefix estimates. -/
lemma descendingPrimeFactors_get_le {a : ℕ}
    {i j : Fin (descendingPrimeFactors a).length} (hij : i ≤ j) :
    (descendingPrimeFactors a).get j ≤ (descendingPrimeFactors a).get i := by
  exact (List.sortedGE_iff_antitone_get.mp (descendingPrimeFactors_sortedGE a)) hij

/-- Splitting the descending factor list after `r` terms gives an exact
factorization of a positive integer into the selected prefix and its remainder. -/
lemma descendingPrimeFactors_take_mul_drop {a r : ℕ} (ha : 0 < a) :
    ((descendingPrimeFactors a).take r).prod *
        ((descendingPrimeFactors a).drop r).prod = a := by
  rw [← List.prod_append, List.take_append_drop]
  rw [descendingPrimeFactors_prod, Nat.prod_primeFactorsList ha.ne']

/-- Every member of the descending factor list is a prime divisor of the
original positive integer. -/
lemma mem_descendingPrimeFactors {a p : ℕ}
    (hp : p ∈ descendingPrimeFactors a) : p.Prime ∧ p ∣ a := by
  have hp' : p ∈ a.primeFactorsList := by
    simpa [descendingPrimeFactors] using hp
  exact ⟨Nat.prime_of_mem_primeFactorsList hp',
    Nat.dvd_of_mem_primeFactorsList hp'⟩

/-- A prime-factor prefix is coprime to the remaining suffix when every
suffix factor is strictly smaller than every prefix factor.  This is the
abstract coprimality step underlying the coprimality of prefix and remainder. -/
lemma prime_list_take_coprime_drop {L : List ℕ} {r : ℕ}
    (hprime : ∀ p ∈ L, p.Prime)
    (hsep : ∀ p ∈ L.take r, ∀ q ∈ L.drop r, q < p) :
    Nat.Coprime (L.take r).prod (L.drop r).prod := by
  have hlist_coprime : ∀ (n : ℕ) (ys : List ℕ),
      (∀ q ∈ ys, Nat.Coprime n q) → Nat.Coprime n ys.prod := by
    intro n ys hys
    induction ys with
    | nil => simp
    | cons q ys ih =>
      simp only [List.prod_cons]
      refine Nat.Coprime.mul_right (hys q ?_) (ih fun q' hq' => hys q' ?_)
      · simp
      · simp [hq']
  have h_coprime : ∀ p ∈ L.take r, Nat.Coprime p (L.drop r).prod := by
    intro p hp
    apply hlist_coprime
    intro q hq
    have hp' : p.Prime := hprime p (List.mem_of_mem_take hp)
    have hq' : q.Prime := hprime q (List.mem_of_mem_drop hq)
    exact Nat.coprime_primes hp' hq' |>.mpr (ne_of_gt (hsep p hp q hq))
  have hprod : ∀ (xs : List ℕ),
      (∀ p ∈ xs, Nat.Coprime p (L.drop r).prod) →
      Nat.Coprime xs.prod (L.drop r).prod := by
    intro xs hxs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.prod_cons]
      refine Nat.Coprime.mul_left (hxs x ?_) (ih fun p hp => hxs p ?_)
      · simp
      · simp [hp]
  exact hprod _ h_coprime

/-- Coprimality in the form needed by extraction: if the product of the
unselected factors is smaller than the last selected factor, then the selected
prefix and the remainder are coprime. -/
lemma descendingPrimeFactors_take_coprime_drop {a r : ℕ}
    (hr : 0 < r) (hlen : r ≤ (descendingPrimeFactors a).length)
    (hsmall : ((descendingPrimeFactors a).drop r).prod <
      (descendingPrimeFactors a).get ⟨r - 1, by omega⟩) :
    Nat.Coprime ((descendingPrimeFactors a).take r).prod
      ((descendingPrimeFactors a).drop r).prod := by
  apply prime_list_take_coprime_drop
  · intro p hp
    exact (mem_descendingPrimeFactors hp).1
  · intro p hp q hq
    have hq_prime : q.Prime := (mem_descendingPrimeFactors (List.mem_of_mem_drop hq)).1
    have hq_dvd : q ∣ (List.drop r (descendingPrimeFactors a)).prod := List.dvd_prod hq
    have hq_pos : 0 < q := hq_prime.pos
    have hdrop_prod_pos : 0 < (List.drop r (descendingPrimeFactors a)).prod := by
      apply List.prod_pos
      intro x hx
      exact (mem_descendingPrimeFactors (List.mem_of_mem_drop hx)).1.pos
    have hq_le_prod : q ≤ (List.drop r (descendingPrimeFactors a)).prod := Nat.le_of_dvd hdrop_prod_pos hq_dvd
    have hq_lt_get : q < (descendingPrimeFactors a).get ⟨r - 1, by omega⟩ := Nat.lt_of_le_of_lt hq_le_prod hsmall
    rw [List.mem_iff_get] at hp
    obtain ⟨j, hj⟩ := hp
    have hj_lt : (j : ℕ) < r := by
      have : (j : ℕ) < (List.take r (descendingPrimeFactors a)).length := Fin.is_lt j
      simp only [List.length_take, min_eq_left hlen] at this
      exact this
    -- (take r).get j equals the original list's get j
    have hp_eq : (descendingPrimeFactors a).get ⟨j, by omega⟩ = p := by
      rw [← hj, List.get_eq_getElem, List.get_eq_getElem]
      rw [List.getElem_take]
    -- Since j < r, we have j ≤ r - 1
    have hj_le : (j : ℕ) ≤ r - 1 := Nat.le_sub_one_of_lt hj_lt
    -- Use SortedGE to get get (r-1) ≤ get j
    have hget_le : (descendingPrimeFactors a).get ⟨r - 1, by omega⟩ ≤ (descendingPrimeFactors a).get ⟨j, by omega⟩ := by
      exact descendingPrimeFactors_get_le hj_le
    -- Conclude
    calc q < (descendingPrimeFactors a).get ⟨r - 1, by omega⟩ := hq_lt_get
      _ ≤ (descendingPrimeFactors a).get ⟨j, by omega⟩ := hget_le
      _ = p := hp_eq

/-- The first `r` largest prime factors (with multiplicity), viewed as a finite
set.  When the corresponding list has no repetitions this is the canonical
selected prime set used in the extraction theorem. -/
noncomputable def selectedPrimeFactors (a r : ℕ) : Finset ℕ :=
  ((descendingPrimeFactors a).take r).toFinset

/-- Basic readout facts for a repetition-free canonical selected prefix.  This
packages the list-to-finset conversion used repeatedly in the final extraction
argument. -/
lemma selectedPrimeFactors_spec {a r : ℕ}
    (hnodup : ((descendingPrimeFactors a).take r).Nodup) :
    (selectedPrimeFactors a r).card = ((descendingPrimeFactors a).take r).length ∧
      (∀ p ∈ selectedPrimeFactors a r, p.Prime ∧ p ∣ a) ∧
      (∏ p ∈ selectedPrimeFactors a r, p) =
        ((descendingPrimeFactors a).take r).prod := by
  constructor
  · simpa [selectedPrimeFactors] using
      List.toFinset_card_of_nodup hnodup
  constructor
  · intro p hp
    apply mem_descendingPrimeFactors
    exact List.mem_of_mem_take (by simpa [selectedPrimeFactors] using hp)
  · rw [selectedPrimeFactors, List.prod_toFinset _ hnodup]
    simp

/-- Deterministic readout of the extraction conclusion once distinctness and
pairwise linearity of the canonical selected prime factors have been proved.
This isolates those two genuinely number-theoretic steps from the routine
choice and cardinality bookkeeping. -/
lemma extraction_readout_of_selected_factors {k n : ℕ} {R : ℝ}
    (A Aeasy Ahard : Finset ℕ)
    (hpart : A = Aeasy ∪ Ahard) (hdisj : Disjoint Aeasy Ahard)
    (hcard : (Aeasy.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * R)
    (hpos : ∀ a ∈ Ahard, 0 < a)
    (hlen : ∀ a ∈ Ahard, k + 1 ≤ a.primeFactorsList.length)
    (hnodup : ∀ a ∈ Ahard, ((descendingPrimeFactors a).take (k + 1)).Nodup)
    (han : ∀ a ∈ Ahard, a ≤ n)
    (hlinear : ∀ a ∈ Ahard, ∀ b ∈ Ahard, a ≠ b →
      ((selectedPrimeFactors a (k + 1)) ∩
        (selectedPrimeFactors b (k + 1))).card ≤ 1) :
    ∃ (T : ℕ → Finset ℕ),
      A = Aeasy ∪ Ahard ∧ Disjoint Aeasy Ahard ∧
      (Aeasy.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * R ∧
      (∀ a ∈ Ahard, (T a).card = k + 1 ∧
        (∀ p ∈ T a, p.Prime ∧ p ∣ a) ∧ (∏ p ∈ T a, p) ≤ a ∧ a ≤ n) ∧
      (∀ a ∈ Ahard, ∀ b ∈ Ahard, a ≠ b → ((T a) ∩ (T b)).card ≤ 1) := by
  use fun a => if a ∈ Ahard then selectedPrimeFactors a (k + 1) else ∅
  refine ⟨hpart, hdisj, hcard, ?_, ?_⟩
  · intro a ha
    simp [ha]
    have hnodup_a := hnodup a ha
    have hlen_a := hlen a ha
    have key : ((descendingPrimeFactors a).take (k + 1)).toFinset.card = k + 1 := by
      rw [List.toFinset_card_of_nodup hnodup_a]
      exact List.length_take_of_le (descendingPrimeFactors_length a ▸ hlen_a)
    refine ⟨key, ?_, ?_, han a ha⟩
    · intro p hp
      simp [selectedPrimeFactors] at hp
      have hmem_desc : p ∈ descendingPrimeFactors a := List.mem_of_mem_take hp
      have hmem : p ∈ a.primeFactorsList := by simpa [descendingPrimeFactors] using hmem_desc
      exact ⟨Nat.prime_of_mem_primeFactorsList hmem, Nat.dvd_of_mem_primeFactorsList hmem⟩
    · -- Need to show ∏ x ∈ selectedPrimeFactors a (k + 1), x ≤ a
      have ha_pos := hpos a ha
      have hprod_eq : (List.take (k + 1) (descendingPrimeFactors a)).prod =
          ∏ x ∈ selectedPrimeFactors a (k + 1), x := by
        rw [selectedPrimeFactors, List.prod_toFinset _ hnodup_a]
        simp
      -- The product of take divides the full product which equals a
      rw [← hprod_eq]
      have hfull : a.primeFactorsList.prod = a := Nat.prod_primeFactorsList ha_pos.ne'
      have hdvd : (List.take (k + 1) (descendingPrimeFactors a)).prod ∣ a.primeFactorsList.prod := by
        have h := List.take_append_drop (k + 1 : ℕ) (descendingPrimeFactors a)
        have hd : (List.take (k + 1) (descendingPrimeFactors a)).prod ∣
            (descendingPrimeFactors a).prod := by
          conv_rhs => rw [← h, List.prod_append]
          exact dvd_mul_right _ _
        simpa [descendingPrimeFactors_prod] using hd
      rw [hfull] at hdvd
      exact Nat.le_of_dvd ha_pos hdvd
  · intro a ha b hb hab
    simp [ha, hb]
    exact hlinear a ha b hb hab

/-- The selected prefix of a hard survivor contains at least `k` distinct
primes.  Otherwise its equal entries can be grouped into fewer than `k`
prime-power factors, and the small coprime remainder supplies one final factor,
contradicting distinct primitivity. -/
lemma selected_prefix_card_ge {k R : ℕ} {A : Finset ℕ}
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    {a rem : ℕ} (ha : a ∈ A) (L : List ℕ)
    (hprime : ∀ p ∈ L, p.Prime)
    (hprod : L.prod * rem = a)
    (hcop : Nat.Coprime L.prod rem)
    (hprimeSmall : ∀ p ∈ L, p ≤ R)
    (hremSmall : rem ≤ R)
    (hnoPow : ¬ HasPrivatePrimePowerBelow A R a)
    (hnoDiv : ¬ HasPrivateDivisorBelow A R a) :
    k ≤ L.toFinset.card := by
  by_contra hnot
  exact no_small_grouped_prefix_of_card_lt hprim hcard ha L hprime hprod hcop
    hprimeSmall hremSmall hnoPow hnoDiv (by omega)

/-- If a list of length `k+1` has at least `k` distinct entries but is not
repetition-free, then it has exactly `k` distinct entries.  This isolates the
finite-cardinality step in the final repeated-prime case of extraction. -/
lemma toFinset_card_eq_of_length_succ_and_not_nodup {α : Type*} [DecidableEq α]
    {L : List α} {k : ℕ} (hlen : L.length = k + 1)
    (hcard : k ≤ L.toFinset.card) (hdup : ¬ L.Nodup) :
    L.toFinset.card = k := by
  have hle : L.toFinset.card ≤ L.length := List.toFinset_card_le L
  have hne : L.toFinset.card ≠ L.length := by
    have hnodup_iff : ∀ {M : List α}, M.Nodup ↔ M.toFinset.card = M.length := by
      intro M
      induction M with
      | nil => simp
      | cons y ys ih =>
        simp only [List.toFinset_cons, List.length_cons]
        constructor
        · intro hnod
          rw [List.nodup_cons] at hnod
          have hys : ys.toFinset.card = ys.length := ih.mp hnod.2
          have hnotin : y ∉ ys.toFinset := by simpa using hnod.1
          have heq : (insert y ys.toFinset) = {y} ∪ ys.toFinset := by simp
          rw [heq, Finset.card_union_of_disjoint]
          · simp [hys]; ring
          · simp [hnotin]
        · intro hcard
          have hnotin : y ∉ ys.toFinset := by
            intro hin
            rw [Finset.insert_eq_self.mpr hin] at hcard
            have := List.toFinset_card_le ys
            omega
          have hysnod : ys.toFinset.card = ys.length := by
            have hinot : ¬y ∈ ys.toFinset := hnotin
            have : insert y ys.toFinset = ys.toFinset ∪ {y} := by simp
            rw [this, Finset.card_union_of_disjoint] at hcard
            · simp at hcard; exact hcard
            · simp [hnotin]
          exact List.nodup_cons.mpr ⟨fun h => hnotin (by simpa using h), ih.mpr hysnod⟩
    rw [hnodup_iff] at hdup
    exact hdup
  omega

/-- In the repeated-prime case, a selected prefix of length `k+1` has
exactly `k` distinct primes.  The lower bound comes from the grouped-prefix
primitivity contradiction, while non-nodup rules out `k+1` distinct entries. -/
lemma selected_prefix_card_eq_of_not_nodup {k R : ℕ} {A : Finset ℕ}
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    {a rem : ℕ} (ha : a ∈ A) (L : List ℕ)
    (hlen : L.length = k + 1) (hdup : ¬ L.Nodup)
    (hprime : ∀ p ∈ L, p.Prime)
    (hprod : L.prod * rem = a)
    (hcop : Nat.Coprime L.prod rem)
    (hprimeSmall : ∀ p ∈ L, p ≤ R)
    (hremSmall : rem ≤ R)
    (hnoPow : ¬ HasPrivatePrimePowerBelow A R a)
    (hnoDiv : ¬ HasPrivateDivisorBelow A R a) :
    L.toFinset.card = k := by
  apply toFinset_card_eq_of_length_succ_and_not_nodup hlen
  · exact selected_prefix_card_ge hprim hcard ha L hprime hprod hcop
      hprimeSmall hremSmall hnoPow hnoDiv
  · exact hdup

/-- A list of length `k+1` with exactly `k` distinct entries has a
singleton among its final three positions.  This is the finite combinatorial
pigeonhole fact used to choose the absorber in the repeated-prime case. -/
lemma exists_count_one_mem_drop_of_length_succ_card_eq {α : Type*} [DecidableEq α]
    {L : List α} {k : ℕ} (hk : 2 ≤ k) (hlen : L.length = k + 1)
    (hcard : L.toFinset.card = k) :
    ∃ x ∈ L.drop (k - 2), L.count x = 1 := by
  have hsum : ∑ x ∈ L.toFinset, L.count x = L.length := by
    have h : ∀ x, L.count x = (L : Multiset α).count x := fun x => by simp
    simp_rw [h]
    rw [Multiset.sum_count_eq_card]
    · rfl
    · exact fun a ha => List.mem_toFinset.mpr (Multiset.mem_coe.mp ha)
  -- Since L.length = k + 1 and L.toFinset.card = k, exactly one element appears twice
  -- L.drop (k - 2) contains the last 3 elements
  -- At least one of those 3 must be a singleton
  have hdrop_len : (L.drop (k - 2)).length = 3 := by
    rw [List.length_drop]
    omega
  -- Let's denote the drop as D
  set D := L.drop (k - 2) with hD
  -- Consider the set of elements in D that have count = 1 in L
  set S := D.toFinset.filter (fun x => L.count x = 1) with hS
  -- We need to show S is nonempty
  by_contra hS_empty
  push_neg at hS_empty
  -- Every element in D has count ≥ 2
  have hcount_ge_two : ∀ x ∈ D.toFinset, 2 ≤ L.count x := by
    intro x hx
    have hxD : x ∈ D := List.mem_toFinset.mp hx
    have := hS_empty x hxD
    have hpos : L.count x ≥ 1 := by
      have : x ∈ L := List.mem_of_mem_drop hxD
      exact List.count_pos_iff.mpr this
    exact Nat.lt_of_le_of_ne hpos (Ne.symm this)
  -- The sum of (count x - 1) over L.toFinset equals 1
  -- If all elements in D have count ≥ 2, then sum over D.toFinset of (count x - 1) ≥ D.toFinset.card
  -- Since D has length 3, D.toFinset.card ≥ 1, but actually we can show sum ≥ 3
  have hexcess : ∑ x ∈ L.toFinset, (L.count x - 1) = 1 := by
    have h_count_ge_one : ∀ x ∈ L.toFinset, 1 ≤ L.count x := by
      intro x hx
      exact List.count_pos_iff.mpr (List.mem_toFinset.mp hx)
    have h1 : ∑ x ∈ L.toFinset, L.count x = ∑ x ∈ L.toFinset, (L.count x - 1) + ∑ x ∈ L.toFinset, 1 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Nat.sub_add_cancel (h_count_ge_one x hx)]
    rw [hsum, hlen] at h1
    simp only [Finset.sum_const, smul_eq_mul, mul_one, hcard] at h1
    omega
  -- Since every element in D has count ≥ 2, and D has 3 elements,
  -- sum of excess over D.toFinset ≥ D.toFinset.card
  -- But D has 3 elements, so D.toFinset.card ∈ {1, 2, 3}
  -- Each element in D.toFinset has excess = count - 1 ≥ 1
  -- If D.toFinset.card ≥ 2, sum of excess ≥ 2 > 1 = total excess. Contradiction!
  -- If D.toFinset.card = 1, all 3 elements of D are the same, so count ≥ 3, excess ≥ 2 > 1. Contradiction!
  have hD_subset : D.toFinset ⊆ L.toFinset := by
    intro x hx
    exact List.mem_toFinset.mpr (List.mem_of_mem_drop (List.mem_toFinset.mp hx))
  -- Sum of excess over D.toFinset is at least D.toFinset.card
  -- Since D has length 3, D.toFinset.card ∈ {1, 2, 3}
  -- Case analysis on D.toFinset.card
  have hcard_D_pos : 0 < D.toFinset.card := Finset.card_pos.mpr ⟨D.get ⟨0, by omega⟩, List.mem_toFinset.mpr (D.get_mem ⟨0, by omega⟩)⟩
  have hcard_D_le : D.toFinset.card ≤ 3 := by
    calc D.toFinset.card ≤ D.length := List.toFinset_card_le D
      _ = 3 := hdrop_len
  -- Sum over D.toFinset of (count - 1) ≥ D.toFinset.card (since each excess ≥ 1)
  have hexcess_D_ge_card : ∑ x ∈ D.toFinset, (L.count x - 1) ≥ D.toFinset.card := by
    have : ∀ x ∈ D.toFinset, 1 ≤ L.count x - 1 := fun x hx => Nat.sub_pos_of_lt (hcount_ge_two x hx)
    calc D.toFinset.card = ∑ _ ∈ D.toFinset, 1 := by simp
      _ ≤ ∑ x ∈ D.toFinset, (L.count x - 1) := Finset.sum_le_sum this
  -- Sum over D.toFinset ≤ sum over L.toFinset = 1
  have hexcess_D_le : ∑ x ∈ D.toFinset, (L.count x - 1) ≤ ∑ x ∈ L.toFinset, (L.count x - 1) := by
    exact Finset.sum_le_sum_of_subset hD_subset
  rw [hexcess] at hexcess_D_le
  -- So D.toFinset.card ≤ 1, combined with ≥ 1, we get D.toFinset.card = 1
  have hcard_D_eq_one : D.toFinset.card = 1 := by omega
  -- D has only one distinct element, say x
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard_D_eq_one
  -- All elements of D are x, so count x D = D.length = 3
  have hall_x : ∀ y ∈ D, y = x := by
    intro y hy
    have h1 : y ∈ D.toFinset := List.mem_toFinset.mpr hy
    rw [hx] at h1
    exact Finset.mem_singleton.mp h1
  have hcount_x_D : D.count x = 3 := by
    rw [← hdrop_len, List.count_eq_length]
    intro b hb
    exact (hall_x b hb).symm
  -- count x L ≥ count x D = 3 since D is a sublist of L
  have hcount_x_L_ge_3 : L.count x ≥ 3 := by
    have hsub := List.drop_sublist (k - 2) L
    have := hsub.count_le x
    simp only [] at this
    linarith [hcount_x_D]
  -- Since D.toFinset = {x}, sum over D.toFinset of (count - 1) = count x L - 1 ≥ 2
  -- But hexcess_D_le says sum ≤ 1. Contradiction!
  have hsum_eq : ∑ y ∈ D.toFinset, (L.count y - 1) = L.count x - 1 := by
    rw [hx]
    simp
  omega

/-- If every entry in the last three positions can absorb the remainder,
the singleton supplied by the length/cardinality pigeonhole lemma gives the
prime-power absorber needed in the repeated-prefix argument. -/
lemma exists_prime_power_absorber_of_last_three
    {L : List ℕ} {k rem R : ℕ} (hk : 2 ≤ k)
    (hlen : L.length = k + 1) (hcard : L.toFinset.card = k)
    (hsmall : ∀ x ∈ L.drop (k - 2), x * rem ≤ R) :
    ∃ ell ∈ L, ell ^ L.count ell * rem ≤ R := by
  obtain ⟨ell, hell, hcount⟩ :=
    exists_count_one_mem_drop_of_length_succ_card_eq hk hlen hcard
  refine ⟨ell, List.mem_of_mem_drop hell, ?_⟩
  simpa [hcount] using hsmall ell hell

/-- An abstract grouped-prime-power factorization with one component absorbing
an external coprime remainder contradicts distinct primitivity when all ordinary
components are witnessed by Stage I and the absorbing component by Stage III. -/
lemma no_grouped_prime_power_factorization_with_absorber {k R : ℕ}
    {A S : Finset ℕ} {a rem ell : ℕ} (hprim : DistPrimitive k A)
    (hcardA : k + 1 ≤ A.card) (ha : a ∈ A) (hcardS : S.card = k)
    (hell : ell ∈ S) (e : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hepos : ∀ p ∈ S, 1 ≤ e p)
    (hprod : (∏ p ∈ S, p ^ e p) * rem = a)
    (hcop : Nat.Coprime (∏ p ∈ S, p ^ e p) rem)
    (hsmall : ∀ p ∈ S, p ≤ R)
    (hellSmall : ell ^ e ell * rem ≤ R)
    (hnoPow : ¬ HasPrivatePrimePowerBelow A R a)
    (hnoDiv : ¬ HasPrivateDivisorBelow A R a) : False := by
  -- Define d' : S → ℕ where d' p = p ^ e p for p ≠ ell, and d' ell = ell ^ e ell * rem
  -- This allows us to use p ^ e p as the divisor (since p ≤ R) while maintaining the key property
  let d' : S → ℕ := fun ⟨p, hp⟩ => if p = ell then ell ^ e ell * rem else p ^ e p
  -- d' is pairwise coprime
  have hd'_cop : ∀ i j : S, i ≠ j → Nat.Coprime (d' i) (d' j) := by
    intro ⟨p, hp⟩ ⟨q, hq⟩ hij
    simp only [d']
    by_cases hpe : p = ell <;> by_cases hqe : q = ell
    · -- Both equal ell, impossible since i ≠ j
      exfalso; simp_all
    · -- p = ell, q ≠ ell
      simp [hpe, hqe]
      have hcopq' : Nat.Coprime (ell ^ e ell) (q ^ e q) :=
        Nat.coprime_pow_primes _ _ (hprime ell hell) (hprime q hq) (fun h => hqe (by rw [h]))
      have hqcop : Nat.Coprime rem q := by
        have hq_dvd_prod : q ∣ ∏ p ∈ S, p ^ e p :=
          dvd_trans (dvd_pow_self q (Nat.ne_of_gt (hepos q hq))) (Finset.dvd_prod_of_mem _ hq)
        have hcop' := Nat.Coprime.coprime_dvd_left hq_dvd_prod hcop
        exact Nat.coprime_comm.mpr hcop'
      exact Nat.Coprime.mul_left hcopq' (hqcop.pow_right _)
    · -- p ≠ ell, q = ell
      simp [hpe, hqe]
      have hcopp' : Nat.Coprime (p ^ e p) (ell ^ e ell) :=
        Nat.coprime_pow_primes _ _ (hprime p hp) (hprime ell hell) (fun h => hpe (by rw [h]))
      have hp_cop : Nat.Coprime p rem := by
        have hp_dvd_prod : p ∣ ∏ p ∈ S, p ^ e p :=
          dvd_trans (dvd_pow_self p (Nat.ne_of_gt (hepos p hp))) (Finset.dvd_prod_of_mem _ hp)
        exact Nat.Coprime.coprime_dvd_left hp_dvd_prod hcop
      exact Nat.Coprime.mul_right hcopp' (hp_cop.pow_left _)
    · -- p ≠ ell, q ≠ ell
      simp [hpe, hqe]
      exact Nat.coprime_pow_primes _ _ (hprime p hp) (hprime q hq) (fun h => hij (Subtype.ext h))
  -- Each d' i divides a
  have hd'_dvd : ∀ i : S, d' i ∣ a := by
    intro ⟨p, hp⟩
    simp only [d']
    split_ifs with hpe
    · subst hpe
      have hdiv : p ^ e p ∣ ∏ q ∈ S, q ^ e q := Finset.dvd_prod_of_mem _ hp
      have : p ^ e p * rem ∣ (∏ q ∈ S, q ^ e q) * rem := Nat.mul_dvd_mul hdiv dvd_rfl
      exact hprod ▸ this
    · -- p ≠ ell, so d' p = p ^ e p, and p ^ e p ∣ ∏ p ∈ S, p ^ e p ∣ a
      have h1 : p ^ e p ∣ ∏ p ∈ S, p ^ e p := Finset.dvd_prod_of_mem _ hp
      have h2 : (∏ p ∈ S, p ^ e p) ∣ a := hprod ▸ dvd_mul_right _ _
      exact dvd_trans h1 h2
  -- Witnesses for d'
  have hd'witness : ∀ i : S, ∃ b ∈ A.erase a, d' i ∣ b := by
    intro ⟨p, hp⟩
    by_cases hpe : p = ell
    · -- For ell, we use witness_of_no_private_divisor
      simp only [d', hpe, reduceIte]
      have hdiv_ell : ell ^ e ell ∣ ∏ p ∈ S, p ^ e p := Finset.dvd_prod_of_mem _ hell
      have hdvla : ell ^ e ell * rem ∣ a := hprod ▸ Nat.mul_dvd_mul hdiv_ell dvd_rfl
      exact witness_of_no_private_divisor hnoDiv hellSmall hdvla
    · -- For p ≠ ell, try to find witness; if not, p^e p is private, contradicting hnoPow
      simp only [d', hpe, reduceIte]
      by_contra hno_witness
      push_neg at hno_witness
      -- p^e p has no witness in A.erase a, so it's a private prime power
      have hdvd2 : p ^ e p ∣ ∏ q ∈ S, q ^ e q := Finset.dvd_prod_of_mem _ hp
      have hdvd3 : (∏ q ∈ S, q ^ e q) ∣ a := hprod ▸ dvd_mul_right _ _
      exact hnoPow ⟨p, e p, hprime p hp, hepos p hp, dvd_trans hdvd2 hdvd3, hsmall p hp, hno_witness⟩
  -- Product equals a
  have hd'prod : ∏ i : S, d' i = a := by
    simp only [d']
    rw [Finset.prod_coe_sort (f := fun p => if p = ell then ell ^ e ell * rem else p ^ e p)]
    -- Split out ell from the product
    have h1 : ∏ p ∈ S.erase ell, (if p = ell then ell ^ e ell * rem else p ^ e p) =
              ∏ p ∈ S.erase ell, (p ^ e p) := by
      apply Finset.prod_congr rfl
      intro x hx
      simp only [Finset.mem_erase] at hx
      simp [hx.1]
    have h2 : ∏ p ∈ S, (if p = ell then ell ^ e ell * rem else p ^ e p) =
              (ell ^ e ell * rem) * ∏ p ∈ S.erase ell, (p ^ e p) := by
      rw [← Finset.mul_prod_erase _ _ hell]
      simp only [if_true]
      rw [h1]
    rw [h2]
    -- Now use hprod: (∏ p ∈ S, p ^ e p) * rem = a
    -- Note: ∏ p ∈ S, p ^ e p = ell ^ e ell * ∏ p ∈ S.erase ell, p ^ e p
    have h3 : ∏ p ∈ S, p ^ e p = ell ^ e ell * ∏ p ∈ S.erase ell, p ^ e p := by
      rw [← Finset.mul_prod_erase _ _ hell]
    rw [h3] at hprod
    have : ell ^ e ell * rem * ∏ x ∈ S.erase ell, x ^ e x =
           (ell ^ e ell * ∏ x ∈ S.erase ell, x ^ e x) * rem := by ring
    rw [this, hprod.symm]
  -- Apply no_coprime_witnessed_factorization_fintype
  exact no_coprime_witnessed_factorization_fintype hprim hcardA ha d' hd'_cop hd'prod hd'witness (by simp [hcardS])

/-- If a prime-factor prefix has exactly `k` distinct primes, one selected
prime power can absorb the coprime remainder below the Stage-III cutoff.  The
resulting `k` pairwise coprime factors all have witnesses outside `a`, which
contradicts distinct primitivity.  This packages the exceptional `s = k` case
in the distinctness argument. -/
lemma no_grouped_prefix_of_card_eq_with_absorber {k R : ℕ} {A : Finset ℕ}
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    {a rem ell : ℕ} (ha : a ∈ A) (L : List ℕ)
    (hprime : ∀ p ∈ L, p.Prime)
    (hprod : L.prod * rem = a)
    (hcop : Nat.Coprime L.prod rem)
    (hprimeSmall : ∀ p ∈ L, p ≤ R)
    (hcardDistinct : L.toFinset.card = k)
    (hell : ell ∈ L)
    (hellSmall : ell ^ L.count ell * rem ≤ R)
    (hnoPow : ¬ HasPrivatePrimePowerBelow A R a)
    (hnoDiv : ¬ HasPrivateDivisorBelow A R a) : False := by
  apply no_grouped_prime_power_factorization_with_absorber hprim hcard ha
    hcardDistinct (List.mem_toFinset.mpr hell) (fun p => L.count p)
  · intro p hp
    exact hprime p (List.mem_toFinset.mp hp)
  · intro p hp
    exact List.count_pos_iff.mpr (List.mem_toFinset.mp hp)
  · rw [← Finset.prod_list_count]
    exact hprod
  · rw [← Finset.prod_list_count]
    exact hcop
  · intro p hp
    exact hprimeSmall p (List.mem_toFinset.mp hp)
  · exact hellSmall
  · exact hnoPow
  · exact hnoDiv

/-- The two local consequences of the numerical estimates—an
absorber for a repeated prefix and an absorber away from any chosen pair—are
sufficient to establish both distinctness and pairwise linearity.  This lemma
separates the final combinatorial argument from the real-valued estimates. -/
lemma selected_factor_properties_of_local_absorbers
    {k R : ℕ} {A H : Finset ℕ}
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    (hHA : H ⊆ A)
    (hpos : ∀ a ∈ H, 0 < a)
    (hlen : ∀ a ∈ H, k + 1 ≤ (descendingPrimeFactors a).length)
    (hsmall : ∀ a ∈ H, ∀ p ∈ (descendingPrimeFactors a).take (k + 1), p ≤ R)
    (hcop : ∀ a ∈ H,
      Nat.Coprime ((descendingPrimeFactors a).take (k + 1)).prod
        ((descendingPrimeFactors a).drop (k + 1)).prod)
    (hnoPow : ∀ a ∈ H, ¬ HasPrivatePrimePowerBelow A R a)
    (hnoDiv : ∀ a ∈ H, ¬ HasPrivateDivisorBelow A R a)
    (hdupAbsorb : ∀ a ∈ H,
      ¬ ((descendingPrimeFactors a).take (k + 1)).Nodup →
      ∃ ell ∈ (descendingPrimeFactors a).take (k + 1),
        ell ^ ((descendingPrimeFactors a).take (k + 1)).count ell *
          ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R)
    (hpairAbsorb : ∀ a ∈ H,
      ((descendingPrimeFactors a).take (k + 1)).Nodup →
      ∀ p ∈ selectedPrimeFactors a (k + 1),
      ∀ q ∈ selectedPrimeFactors a (k + 1), p ≠ q →
      ∃ ell ∈ selectedPrimeFactors a (k + 1), ell ≠ p ∧ ell ≠ q ∧
        ell * ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R) :
    (∀ a ∈ H, ((descendingPrimeFactors a).take (k + 1)).Nodup) ∧
    (∀ a ∈ H, ∀ b ∈ H, a ≠ b →
      ((selectedPrimeFactors a (k + 1)) ∩
        (selectedPrimeFactors b (k + 1))).card ≤ 1) := by
  have hnoddup : ∀ a, a ∈ H → ((descendingPrimeFactors a).take (k + 1)).Nodup := fun a ha => by
    by_contra hnod
    let L := (descendingPrimeFactors a).take (k + 1)
    have hLa_len : (descendingPrimeFactors a).length ≥ k + 1 := hlen a ha
    have hLlen : L.length = k + 1 := by simp [L, List.length_take, hLa_len]
    obtain ⟨ell, hell_mem, hell_prod⟩ := hdupAbsorb a ha hnod
    have hell_mem' : ell ∈ descendingPrimeFactors a := List.mem_of_mem_take hell_mem
    have hell_pos : 0 < ell := (mem_descendingPrimeFactors hell_mem').1.pos
    have hell_count_pos : 0 < L.count ell := by
      rw [Nat.pos_iff_ne_zero, ne_eq, List.count_eq_zero]
      exact fun h => h hell_mem
    have hremSmall : ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R := by
      have hell_pow_pos : 0 < ell ^ L.count ell := Nat.pow_pos hell_pos
      have hle : ell ^ L.count ell * ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R := hell_prod
      exact Nat.le_trans (Nat.le_mul_of_pos_left _ hell_pow_pos) hle
    have hcard_eq : L.toFinset.card = k := selected_prefix_card_eq_of_not_nodup hprim hcard (hHA ha) L hLlen hnod
      (fun p hp => (mem_descendingPrimeFactors (List.mem_of_mem_take hp)).1)
      (descendingPrimeFactors_take_mul_drop (hpos a ha)) (hcop a ha) (hsmall a ha) hremSmall (hnoPow a ha) (hnoDiv a ha)
    exact no_grouped_prefix_of_card_eq_with_absorber hprim hcard (hHA ha) L
      (fun p hp => (mem_descendingPrimeFactors (List.mem_of_mem_take hp)).1)
      (descendingPrimeFactors_take_mul_drop (hpos a ha)) (hcop a ha)
      (hsmall a ha) hcard_eq hell_mem hell_prod (hnoPow a ha) (hnoDiv a ha)
  constructor
  · exact hnoddup
  · apply selected_prime_sets_pairwise_linear_of_absorbing
      (fun a => selectedPrimeFactors a (k + 1))
      (fun a => ((descendingPrimeFactors a).drop (k + 1)).prod)
      hprim hcard hHA
      (fun a ha => by
        have hspec := selectedPrimeFactors_spec (hnoddup a ha)
        have hlen : (List.take (k + 1) (descendingPrimeFactors a)).length = k + 1 := by
          simp [List.length_take, hlen a ha]
        exact hspec.1.trans hlen)
      (fun a ha p hp => (selectedPrimeFactors_spec (hnoddup a ha)).2.1 p hp |>.1)
      (fun a ha => by
        have hspec := selectedPrimeFactors_spec (hnoddup a ha)
        rw [hspec.2.2]
        exact descendingPrimeFactors_take_mul_drop (hpos a ha))
      (fun a ha => by
        have hspec := selectedPrimeFactors_spec (hnoddup a ha)
        rw [hspec.2.2]
        exact hcop a ha)
      (fun a ha p hp => hsmall a ha p (List.mem_toFinset.mp hp))
      hnoDiv
      (fun a ha => hpairAbsorb a ha (hnoddup a ha))

/-- The final finite-combinatorial assembly from the common numerical
estimate on the last three selected factors.  In the repeated case it produces
a prime-power absorber; in the nodup case it produces an absorber away from any
prescribed pair. -/
lemma local_absorbers_of_last_three
    {k R : ℕ} (hk : 2 ≤ k) {A H : Finset ℕ}
    (hprim : DistPrimitive k A) (hcard : k + 1 ≤ A.card)
    (hHA : H ⊆ A)
    (hpos : ∀ a ∈ H, 0 < a)
    (hlen : ∀ a ∈ H, k + 1 ≤ (descendingPrimeFactors a).length)
    (hsmall : ∀ a ∈ H, ∀ p ∈ (descendingPrimeFactors a).take (k + 1), p ≤ R)
    (hcop : ∀ a ∈ H,
      Nat.Coprime ((descendingPrimeFactors a).take (k + 1)).prod
        ((descendingPrimeFactors a).drop (k + 1)).prod)
    (hnoPow : ∀ a ∈ H, ¬ HasPrivatePrimePowerBelow A R a)
    (hnoDiv : ∀ a ∈ H, ¬ HasPrivateDivisorBelow A R a)
    (htrail : ∀ a ∈ H,
      ∀ p ∈ ((descendingPrimeFactors a).take (k + 1)).drop (k - 2),
        p * ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R) :
    (∀ a ∈ H,
      ¬ ((descendingPrimeFactors a).take (k + 1)).Nodup →
      ∃ ell ∈ (descendingPrimeFactors a).take (k + 1),
        ell ^ ((descendingPrimeFactors a).take (k + 1)).count ell *
          ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R) ∧
    (∀ a ∈ H,
      ((descendingPrimeFactors a).take (k + 1)).Nodup →
      ∀ p ∈ selectedPrimeFactors a (k + 1),
      ∀ q ∈ selectedPrimeFactors a (k + 1), p ≠ q →
      ∃ ell ∈ selectedPrimeFactors a (k + 1), ell ≠ p ∧ ell ≠ q ∧
        ell * ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R) := by
  refine ⟨?_, ?_⟩
  · intro a ha hnodup
    -- The take has length k+1 and is not nodup, so toFinset.card = k
    have hlen_take : ((descendingPrimeFactors a).take (k + 1)).length = k + 1 := by
      simp [List.length_take, hlen a ha]
    -- Consider two cases: drop is empty or non-empty
    by_cases hdrop_empty : (descendingPrimeFactors a).drop (k + 1) = []
    · -- When drop is empty, drop.prod = 1, need ell^count ≤ R
      simp [hdrop_empty]
      -- Need R ≥ 1. Since list is non-empty, pick any element p, p ≤ R and p ≥ 2, so R ≥ 2.
      have ha_pos : 0 < a := hpos a ha
      have hne : (descendingPrimeFactors a).take (k + 1) ≠ [] := by
        intro heq
        simp [heq] at hlen_take
      have ⟨p, hp⟩ : ∃ p, p ∈ (descendingPrimeFactors a).take (k + 1) := List.length_pos_iff_exists_mem.mp (by linarith [hlen_take] : 0 < ((descendingPrimeFactors a).take (k + 1)).length)
      have hp_small := hsmall a ha p hp
      have hp_prime := (mem_descendingPrimeFactors (List.mem_of_mem_take hp)).1
      have hp_ge_two : 2 ≤ p := hp_prime.two_le
      have hR_ge_two : 2 ≤ R := le_trans hp_ge_two hp_small
      have hdrop_prod : ((descendingPrimeFactors a).drop (k + 1)).prod = 1 := by simp [hdrop_empty]
      have hremSmall : ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R := by simp [hdrop_prod]; omega
      -- Now we can apply selected_prefix_card_ge
      have hcard_ge : k ≤ ((descendingPrimeFactors a).take (k + 1)).toFinset.card :=
        selected_prefix_card_ge hprim hcard (hHA ha)
          ((descendingPrimeFactors a).take (k + 1))
          (fun p hp => (mem_descendingPrimeFactors (List.mem_of_mem_take hp)).1)
          (descendingPrimeFactors_take_mul_drop ha_pos) (hcop a ha) (hsmall a ha) hremSmall
          (hnoPow a ha) (hnoDiv a ha)
      -- And not_nodup gives us card ≤ k (since card < k+1)
      have hcard_le : ((descendingPrimeFactors a).take (k + 1)).toFinset.card ≤ k :=
        (toFinset_card_eq_of_length_succ_and_not_nodup hlen_take hcard_ge hnodup).le
      have hcard_eq : ((descendingPrimeFactors a).take (k + 1)).toFinset.card = k := by omega
      -- Now use exists_prime_power_absorber_of_last_three with rem = 1
      have htrail' : ∀ x ∈ ((descendingPrimeFactors a).take (k + 1)).drop (k - 2), x * 1 ≤ R := by
        intro x hxdrop
        have := htrail a ha x hxdrop
        rw [hdrop_empty] at this
        simp at this
        simpa using this
      obtain ⟨ell, hell, hellSmall⟩ := exists_prime_power_absorber_of_last_three hk hlen_take hcard_eq (rem := 1) htrail'
      simp at hellSmall
      exact ⟨ell, hell, hellSmall⟩
    · -- Drop is non-empty
      -- take.length = k+1 ≥ 3, so take.drop(k-2) has length 3 and is non-empty
      have hk3 : k + 1 ≥ 3 := by omega
      have hdrop_k2_nonempty : ((descendingPrimeFactors a).take (k + 1)).drop (k - 2) ≠ [] := by
        simp only [ne_eq, List.drop_eq_nil_iff]
        have h : ((descendingPrimeFactors a).take (k + 1)).length = k + 1 := hlen_take
        omega
      obtain ⟨p, hp⟩ : ∃ p, p ∈ ((descendingPrimeFactors a).take (k + 1)).drop (k - 2) := by
        apply List.length_pos_iff_exists_mem.mp
        rw [List.length_drop, hlen_take]
        omega
      have hp_prime := (mem_descendingPrimeFactors (List.mem_of_mem_take (List.mem_of_mem_drop hp))).1
      have hp_ge_two : 2 ≤ p := hp_prime.two_le
      have htrail_p := htrail a ha p hp
      -- p * drop.prod ≤ R, and p ≥ 2, so drop.prod ≤ R
      have hremSmall : ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R := by
        have : p * ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R := htrail_p
        nlinarith
      -- Now proceed as in the empty case
      have ha_pos : 0 < a := hpos a ha
      have hne : (descendingPrimeFactors a).take (k + 1) ≠ [] := by
        intro heq; simp [heq] at hlen_take
      have ⟨q, hq⟩ : ∃ q, q ∈ (descendingPrimeFactors a).take (k + 1) := List.length_pos_iff_exists_mem.mp (by linarith [hlen_take] : 0 < ((descendingPrimeFactors a).take (k + 1)).length)
      have hq_small := hsmall a ha q hq
      have hq_prime := (mem_descendingPrimeFactors (List.mem_of_mem_take hq)).1
      have hq_ge_two : 2 ≤ q := hq_prime.two_le
      have hR_ge_two : 2 ≤ R := le_trans hq_ge_two hq_small
      -- selected_prefix_card_ge requires hremSmall
      have hcard_ge : k ≤ ((descendingPrimeFactors a).take (k + 1)).toFinset.card :=
        selected_prefix_card_ge hprim hcard (hHA ha)
          ((descendingPrimeFactors a).take (k + 1))
          (fun p hp => (mem_descendingPrimeFactors (List.mem_of_mem_take hp)).1)
          (descendingPrimeFactors_take_mul_drop ha_pos) (hcop a ha) (hsmall a ha) hremSmall
          (hnoPow a ha) (hnoDiv a ha)
      -- And not_nodup gives us card ≤ k
      have hcard_le : ((descendingPrimeFactors a).take (k + 1)).toFinset.card ≤ k :=
        (toFinset_card_eq_of_length_succ_and_not_nodup hlen_take hcard_ge hnodup).le
      have hcard_eq : ((descendingPrimeFactors a).take (k + 1)).toFinset.card = k := by omega
      -- Now use exists_prime_power_absorber_of_last_three
      have htrail' : ∀ x ∈ ((descendingPrimeFactors a).take (k + 1)).drop (k - 2), x * ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R := by
        intro x hxdrop
        exact htrail a ha x hxdrop
      exact exists_prime_power_absorber_of_last_three hk hlen_take hcard_eq htrail'
  · intro a ha hnoddup p hp q hq hpq
    -- The take has k+1 elements, the drop (k-2) gives the last 3 elements
    -- Since we exclude at most 2 elements (p and q), one of the last 3 works
    have hlen_take : ((descendingPrimeFactors a).take (k + 1)).length = k + 1 := by
      simp [List.length_take, hlen a ha]
    -- An element of the drop that differs from p and q
    have hdrop_not_empty : ∃ ell ∈ ((descendingPrimeFactors a).take (k + 1)).drop (k - 2), ell ≠ p ∧ ell ≠ q := by
      -- The drop has length 3
      have hdrop_len : (((descendingPrimeFactors a).take (k + 1)).drop (k - 2)).length = 3 := by
        rw [List.length_drop, hlen_take]
        omega
      -- The drop is a sublist of a nodup list, so it's also nodup
      have hdrop_nodup : (((descendingPrimeFactors a).take (k + 1)).drop (k - 2)).Nodup := hnoddup.drop
      -- The finset of the drop has 3 elements
      have hdrop_card : (((descendingPrimeFactors a).take (k + 1)).drop (k - 2)).toFinset.card = 3 := by
        rw [List.toFinset_card_of_nodup hdrop_nodup, hdrop_len]
      -- The drop's finset minus {p, q} is non-empty since 3 > 2
      have hne : (((descendingPrimeFactors a).take (k + 1)).drop (k - 2)).toFinset \ {p, q} ≠ ∅ := by
        by_contra hempty
        rw [Finset.sdiff_eq_empty_iff_subset] at hempty
        have hpq_card : ({p, q} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _
        have hsub : (((descendingPrimeFactors a).take (k + 1)).drop (k - 2)).toFinset ⊆ {p, q} := hempty
        have hle : (((descendingPrimeFactors a).take (k + 1)).drop (k - 2)).toFinset.card ≤ ({p, q} : Finset ℕ).card := Finset.card_le_card hsub
        linarith
      -- Extract an element from the nonempty difference
      have hne' : ( (((descendingPrimeFactors a).take (k + 1)).drop (k - 2)).toFinset \ {p, q} ).Nonempty := Finset.nonempty_of_ne_empty hne
      obtain ⟨ell, hell⟩ := hne'
      have hell_drop : ell ∈ (((descendingPrimeFactors a).take (k + 1)).drop (k - 2)).toFinset := Finset.mem_sdiff.mp hell |>.1
      have hnot_pq : ell ∉ ({p, q} : Finset ℕ) := Finset.mem_sdiff.mp hell |>.2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot_pq
      exact ⟨ell, List.mem_toFinset.mp hell_drop, hnot_pq⟩
    obtain ⟨ell, hell_drop, helle_p, helle_q⟩ := hdrop_not_empty
    -- ell is in the take (since drop is a sublist of take), hence in selectedPrimeFactors
    have hell_take : ell ∈ ((descendingPrimeFactors a).take (k + 1)) := List.mem_of_mem_drop hell_drop
    have hell_selected : ell ∈ selectedPrimeFactors a (k + 1) := by
      rw [selectedPrimeFactors]
      exact List.mem_toFinset.mpr hell_take
    -- ell is in the drop, so htrail applies
    have hell_trail := htrail a ha ell hell_drop
    exact ⟨ell, hell_selected, helle_p, helle_q, hell_trail⟩

/-! ### The greedy box argument -/

/-! ## The numerical core of the extraction theorem -/

/-- Every unselected prime factor is at most every selected one. -/
lemma descendingPrimeFactors_drop_le_take {a r p q : ℕ}
    (hp : p ∈ (descendingPrimeFactors a).take r)
    (hq : q ∈ (descendingPrimeFactors a).drop r) : q ≤ p := by
  let L := descendingPrimeFactors a
  -- p is in take r, so there exists index i < r with p = L.get i
  obtain ⟨i, hi, hp_eq⟩ : ∃ i : Fin L.length, i.val < r ∧ L.get i = p := by
    obtain ⟨i, hp_eq⟩ := List.mem_iff_get.mp hp
    have hi1 : (i : ℕ) < r := by
      have := i.isLt
      simp only [List.length_take] at this
      exact lt_of_lt_of_le this (min_le_left ..)
    have hi2 : (i : ℕ) < L.length := by
      have := i.isLt
      simp only [List.length_take] at this
      exact lt_of_lt_of_le this (min_le_right ..)
    exact ⟨⟨(i : ℕ), hi2⟩, hi1, by rw [← hp_eq]; exact (List.getElem_take ..).symm⟩
  -- q is in drop r, so there exists index j ≥ r with q = L.get j
  obtain ⟨j, hj, hq_eq⟩ : ∃ j : Fin L.length, r ≤ j.val ∧ L.get j = q := by
    obtain ⟨k, hq_eq⟩ := List.mem_iff_get.mp hq
    -- k is an index into L.drop r, so the index into L is r + k
    use ⟨r + k, by
      have : (k : ℕ) < (List.drop r L).length := k.isLt
      simp only [List.length_drop] at this
      omega⟩
    refine ⟨by simp, ?_⟩
    rw [← hq_eq]
    simp [List.getElem_drop]
    rfl
  -- Since i.val < r ≤ j.val, we have i ≤ j
  have hij : i ≤ j := by
    exact Nat.le_of_lt_add_one (by omega : (i : ℕ) < j + 1)
  -- By descendingPrimeFactors_get_le, q = L.get j ≤ L.get i = p
  rw [← hp_eq, ← hq_eq]
  exact descendingPrimeFactors_get_le hij

/-- If the boxes are already large enough that each of the remaining primes `p`
  satisfies `p ^ (k+1) ≤ ∏ boxes`, then the greedy process never overflows the
  cutoff `Rn`: the final boxes are each at most `Rn` or prime. -/
lemma gfold_good_of_overflow (k Rn n : ℕ) (hk : 0 < k) (hRn : 0 < Rn)
    (hscale : ∀ q : ℕ, 0 < q → (Rn : ℝ) ^ k < (n : ℝ) * (q : ℝ) ^ (k - 1) →
      (n : ℝ) < (q : ℝ) ^ (k + 2)) :
    ∀ (L : List ℕ) (b : Fin k → ℕ), (∀ p ∈ L, p.Prime) → (∀ i, 0 < b i) →
      (∀ i, b i ≤ Rn ∨ (b i).Prime) → (∀ p ∈ L, p ^ (k + 1) ≤ ∏ i, b i) →
      (∏ i, b i) * L.prod ≤ n →
      ∀ i, gfold k hk b L i ≤ Rn ∨ (gfold k hk b L i).Prime := by
  intro L b hLprime hbpos hbgood hLprod hprod
  -- Prove a generalized statement by induction on L
  have hgen : ∀ (L : List ℕ) (b' : Fin k → ℕ),
      (∀ p ∈ L, Nat.Prime p) →
      (∀ i, 0 < b' i) →
      (∀ i, b' i ≤ Rn ∨ Nat.Prime (b' i)) →
      (∀ p ∈ L, p ^ (k + 1) ≤ ∏ i, b' i) → (∏ i, b' i) * L.prod ≤ n →
      ∀ i, gfold k hk b' L i ≤ Rn ∨ (gfold k hk b' L i).Prime := by
    intro L
    induction L with
    | nil =>
      intro b' _ hb'pos hb'good _ _
      simp [gfold]
      exact hb'good
    | cons q t ih =>
      intro b' hLprime hb'pos hb'good hb'Lprod hb'Lprod_n
      -- gfold k hk b' (q :: t) = gfold k hk (gstep k hk b' q) t
      simp only [gfold, List.foldl_cons]
      -- Need to show gfold k hk (gstep k hk b' q) t is good
      -- First, establish conditions for gstep_good
      -- We need the no-overflow condition: for minimal j, boxes j * q ≤ Rn or boxes j = 1
      have hn_pos : 0 < n := by
        have hpos : 0 < ∏ i, b' i := Finset.prod_pos fun i _ => hb'pos i
        have hqt_pos : 0 < (q :: t).prod := by
          rw [List.prod_cons]
          exact Nat.mul_pos (Nat.Prime.pos (hLprime q (List.mem_cons_self)))
            (List.prod_pos fun p hp => Nat.Prime.pos (hLprime p (List.mem_cons_of_mem _ hp)))
        nlinarith [hb'Lprod_n]
      have hscaleRn : (Rn : ℝ) ^ k ≥ (n : ℝ) := by
        have h1 := hscale 1 Nat.one_pos
        have h1' : (Rn : ℝ) ^ k < (n : ℝ) * (((1 : ℕ) : ℝ) ^ (k - 1)) → ((n : ℕ) : ℝ) < (((1 : ℕ) : ℝ) ^ (k + 2)) := h1
        norm_num at h1'
        by_contra h
        push_neg at h
        have hn_lt_one := h1' h
        norm_cast at hn_lt_one
        omega
      -- Use gfold_invariant or apply ih directly
      -- Need: (1) gstep is good, (2) overflow invariant for t, (3) product bound
      apply ih (gstep k hk b' q)
      · -- primality for t
        exact fun p hp => hLprime p (List.mem_cons_of_mem _ hp)
      · -- gstep preserves positivity
        exact gstep_pos k hk b' q hb'pos (Nat.Prime.pos (hLprime q (List.mem_cons_self)))
      · -- gstep preserves goodness (via gstep_good)
        -- Need no-overflow: for minimal j, boxes j * q ≤ Rn or boxes j = 1
        apply gstep_good Rn k hk b' q (hLprime q (List.mem_cons_self)) hb'good
        -- Prove no-overflow by contradiction
        intro j hjmin
        by_contra h_bad
        push_neg at h_bad
        obtain ⟨h_mult_gt_Rn, hj_ne_1⟩ := h_bad
        -- j is minimal, so boxes j ≥ 1, and since boxes j ≠ 1, boxes j ≥ 2
        have hj_ge_2 : 2 ≤ b' j := by
          have hj_pos : 1 ≤ b' j := Nat.one_le_iff_ne_zero.mpr (fun h0 => absurd h0 (hb'pos j).ne')
          omega
        -- q is prime, so q ≥ 2
        have hq_ge_2 : 2 ≤ q := Nat.Prime.two_le (hLprime q (List.mem_cons_self))
        -- boxes j * q > Rn means overflow
        -- We need (∏ b') * q ≤ n to apply greedy_overflow
        have hprod_q_le_n : (∏ i, b' i) * q ≤ n := by
          simp only [List.prod_cons] at hb'Lprod_n
          have ht_pos : 1 ≤ t.prod := List.prod_pos fun p hp => Nat.Prime.pos (hLprime p (List.mem_cons_of_mem _ hp))
          nlinarith
        -- Apply greedy_overflow
        have hprod_q_le_n' : (∏ i : Fin k, (b' i : ℝ)) * (q : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hprod_q_le_n
        have h_mult_gt_Rn' : (Rn : ℝ) < (b' j : ℝ) * (q : ℝ) := by
          norm_cast
        have hoverflow := greedy_overflow k (by omega : 1 ≤ k) (Rn : ℝ) (n : ℝ)
          (fun i => (b' i : ℝ)) q j (Nat.cast_pos.mpr hRn) (Nat.cast_pos.mpr (Nat.Prime.pos (hLprime q (List.mem_cons_self))))
          (fun i => Nat.cast_le.mpr (hjmin i)) h_mult_gt_Rn' hprod_q_le_n'
        -- hoverflow : (Rn : ℝ) ^ k / q ^ (k - 1) < n
        -- By scale: Rn ^ k < n * q ^ (k - 1) implies n < q ^ (k + 2)
        have hscale_q := hscale q (Nat.Prime.pos (hLprime q (List.mem_cons_self)))
        have hscale_trigger : (Rn : ℝ) ^ k < (n : ℝ) * (q : ℝ) ^ (k - 1) := by
          rw [div_lt_iff₀ (pow_pos (Nat.cast_pos.mpr (Nat.Prime.pos (hLprime q (List.mem_cons_self)))) _) ] at hoverflow
          linarith
        have hn_lt : (n : ℝ) < (q : ℝ) ^ (k + 2) := hscale_q hscale_trigger
        norm_cast at hn_lt
        -- But q ^ (k + 1) ≤ ∏ b' (overflow invariant for q)
        have hq_inv : q ^ (k + 1) ≤ ∏ i, b' i := hb'Lprod q (List.mem_cons_self)
        -- boxes j^k ≤ ∏ b' (since j is minimal)
        have hj_pow_le : b' j ^ k ≤ ∏ i, b' i := by
          have := Finset.prod_le_prod' (s := Finset.univ) (fun i _ => hjmin i)
          simp at this
          exact this
        -- q^(k+1) * q = q^(k+2) ≤ (∏ b') * q ≤ n
        have hq_sq_le_n : q ^ (k + 2) ≤ n := by
          calc q ^ (k + 2) = q * q ^ (k + 1) := by ring
            _ ≤ q * (∏ i, b' i) := Nat.mul_le_mul_left q hq_inv
            _ = (∏ i, b' i) * q := Nat.mul_comm _ _
            _ ≤ n := hprod_q_le_n
        omega
      · -- overflow invariant for t after gstep
        intro p hp
        have hp_bound := hb'Lprod p (List.mem_cons_of_mem _ hp)
        rw [gstep_prod]
        exact Nat.le_trans hp_bound (Nat.le_mul_of_pos_right _ (Nat.Prime.pos (hLprime q (List.mem_cons_self))))
      · -- product bound for t after gstep
        rw [gstep_prod]
        simp only [List.prod_cons] at hb'Lprod_n
        convert hb'Lprod_n using 1
        ring
  exact hgen L b hLprime hbpos hbgood hLprod hprod

/-- A family of `k` positive boxes, each at most the cutoff or prime, whose
product is `a`, exhibits `a` as a product of exactly `k` basis elements. -/
lemma mulk_of_good_boxes {k n a : ℕ} {R : ℝ} (ha : 0 < a) (han : a ≤ n)
    (b : Fin k → ℕ) (hpos : ∀ i, 0 < b i) (hgood : ∀ i, b i ≤ ⌊R⌋₊ ∨ (b i).Prime)
    (hprod : ∏ i, b i = a) : Mulk (extractionBasis n R) k a := by
  refine mulk_of_boxes b ?_ hprod
  intro i
  have hmem : b i ∈ extractionBasis n R := by
    rcases hgood i with hbR | hprime
    · rw [extractionBasis, Finset.mem_union, Finset.mem_Icc]
      exact Or.inr ⟨hpos i, hbR⟩
    · rw [extractionBasis, Finset.mem_union]
      have hbdiv : b i ∣ a := hprod ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have hbale : b i ≤ n := Nat.le_trans (Nat.le_of_dvd ha hbdiv) han
      simp [primesLE, Finset.mem_filter, Finset.mem_range, hprime, hbale]
  exact hmem

/-- The scale inequality in the arithmetic form required by the greedy
overflow estimate.  A factor `2` of slack absorbs the rounding of the cutoff. -/
lemma scale1_overflow_bound {k n : ℕ} {R : ℝ} (hk : 2 ≤ k) (hR : 2 ≤ R) (hn : 0 < n)
    (hscale1 : (n : ℝ) ^ ((1 : ℝ) / (k + 2)) <
      ((R / 2) ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1))) :
    ∀ q : ℕ, 0 < q → ((⌊R⌋₊ : ℕ) : ℝ) ^ k < (n : ℝ) * (q : ℝ) ^ (k - 1) →
      (n : ℝ) < (q : ℝ) ^ (k + 2) := by
  intro q hq hoverflow
  by_contra hne
  push_neg at hne
  have hR_pos : 0 < R := by linarith
  have hR2_pos : 0 < R / 2 := by linarith
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hexp_k2 : 0 < (k : ℝ) + 2 := by positivity
  have hexp_k1 : 0 < (k : ℝ) - 1 := by linarith [show (k : ℝ) ≥ 2 by norm_cast]
  -- From hscale1: raise both sides to power (k-1)
  have h1 : ((n : ℝ) ^ (1 / ((k : ℝ) + 2))) ^ ((k : ℝ) - 1) < (((R / 2) ^ (k : ℝ) / n) ^ (1 / ((k : ℝ) - 1))) ^ ((k : ℝ) - 1) :=
    Real.rpow_lt_rpow (by positivity) hscale1 hexp_k1
  rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ)), ← Real.rpow_mul (by positivity : 0 ≤ (R / 2) ^ (k : ℝ) / n)] at h1
  -- Simplify 1/(k-1) * (k-1) = 1
  have hinv : (1 : ℝ) / ((k : ℝ) - 1) * ((k : ℝ) - 1) = 1 := by field_simp
  rw [hinv] at h1
  -- Now h1 : n ^ ((k-1)/(k+2)) < (R/2)^k / n
  simp only [Real.rpow_one] at h1
  -- Multiply both sides by n to get n ^ ((k-1)/(k+2) + 1) < (R/2)^k
  have h2 : (n : ℝ) ^ ((1 / ((k : ℝ) + 2)) * ((k : ℝ) - 1)) * n < (R / 2) ^ (k : ℝ) := by
    calc (n : ℝ) ^ ((1 / ((k : ℝ) + 2)) * ((k : ℝ) - 1)) * n < ((R / 2) ^ (k : ℝ) / n) * n := by
           apply mul_lt_mul_of_pos_right h1 hn_pos
      _ = (R / 2) ^ (k : ℝ) := div_mul_cancel₀ _ hn_pos.ne'
  -- Simplify exponent: (1/(k+2))*(k-1) + 1 = (2k+1)/(k+2)
  have hexp : (1 : ℝ) / ((k : ℝ) + 2) * ((k : ℝ) - 1) + 1 = (2 * (k : ℝ) + 1) / ((k : ℝ) + 2) := by
    field_simp
    ring
  have h3 : (n : ℝ) ^ ((2 * (k : ℝ) + 1) / ((k : ℝ) + 2)) < (R / 2) ^ (k : ℝ) := by
    rwa [← hexp, Real.rpow_add hn_pos, Real.rpow_one]
  -- From hne: q^(k+2) ≤ n, so q^(2k+1) ≤ n ^ ((2k+1)/(k+2))
  have hq_pos : 0 < (q : ℝ) := by positivity
  have hq_pow : (q : ℝ) ^ ((2 * (k : ℝ) + 1)) ≤ (n : ℝ) ^ ((2 * (k : ℝ) + 1) / ((k : ℝ) + 2)) := by
    have hqk2 : (q : ℝ) ^ (k + 2) ≤ n := by
      norm_cast at hne
      exact_mod_cast hne
    calc (q : ℝ) ^ (2 * (k : ℝ) + 1) = ((q : ℝ) ^ (k + 2)) ^ ((2 * (k : ℝ) + 1) / ((k : ℝ) + 2)) := by
           rw [← Real.rpow_natCast (q : ℝ) (k + 2), ← Real.rpow_mul (by positivity : 0 ≤ (q : ℝ))]
           congr 1
           field_simp
           norm_cast
      _ ≤ (n : ℝ) ^ ((2 * (k : ℝ) + 1) / ((k : ℝ) + 2)) := by
           apply Real.rpow_le_rpow (by positivity) hqk2 (by positivity : (0 : ℝ) ≤ (2 * (k : ℝ) + 1) / ((k : ℝ) + 2))
  -- So q^(2k+1) < (R/2)^k
  have h4 : (q : ℝ) ^ (2 * (k : ℝ) + 1) < (R / 2) ^ (k : ℝ) := lt_of_le_of_lt hq_pow h3
  -- From floor: R - 1 < ⌊R⌋₊
  have hfloor : R - 1 < ⌊R⌋₊ := Nat.sub_one_lt_floor R
  -- So (R-1)^k < ⌊R⌋₊^k
  have h5 : (R - 1) ^ (k : ℝ) < (⌊R⌋₊ : ℝ) ^ (k : ℝ) := by
    apply Real.rpow_lt_rpow
    · linarith [show (⌊R⌋₊ : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr (Nat.floor_pos.mpr (by linarith : 1 ≤ R))]
    · exact hfloor
    · linarith
  -- n ≥ q^(k+2)
  have hqk2 : (q : ℝ) ^ (k + 2) ≤ n := by
    norm_cast at hne
    exact_mod_cast hne
  -- n * q^(k-1) ≥ q^(k+2) * q^(k-1) = q^(2k+1)
  have h6 : (n : ℝ) * (q : ℝ) ^ ((k : ℝ) - 1) ≥ (q : ℝ) ^ (2 * (k : ℝ) + 1) := by
    have hksub : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      simp
    rw [hksub, Real.rpow_natCast]
    have hqexp : (2 : ℝ) * (k : ℝ) + 1 = ((2 * k + 1 : ℕ) : ℝ) := by norm_cast
    rw [hqexp, Real.rpow_natCast]
    have hqadd : (q : ℝ) ^ (k - 1 : ℕ) * (q : ℝ) ^ (k + 2 : ℕ) = (q : ℝ) ^ (2 * k + 1 : ℕ) := by
      rw [← pow_add]; congr 1; omega
    rw [mul_comm (n : ℝ) _, ← hqadd]
    gcongr
  -- From h3: n < (R/2)^(k(k+2)/(2k+1))
  -- From h4: q^(2k+1) < (R/2)^k, so q^(k-1) < (R/2)^(k(k-1)/(2k+1))
  -- Thus n * q^(k-1) < (R/2)^k
  -- Combined with h5: (R-1)^k < (R/2)^k, so R - 1 < R/2, i.e., R < 2, contradicting hR
  -- First, let's show n * q^(k-1) < (R/2)^k
  have h7 : (n : ℝ) * (q : ℝ) ^ ((k : ℝ) - 1) < (R / 2) ^ (k : ℝ) := by
    have hn_bound : (n : ℝ) < (R / 2) ^ ((k : ℝ) * ((k : ℝ) + 2) / ((2 : ℝ) * (k : ℝ) + 1)) := by
      have h3' : (n : ℝ) ^ ((2 * (k : ℝ) + 1) / ((k : ℝ) + 2)) < (R / 2) ^ (k : ℝ) := h3
      have hexp_pos : 0 < ((2 : ℝ) * (k : ℝ) + 1) / ((k : ℝ) + 2) := by positivity
      have hak : (0 : ℝ) < k := by positivity
      have h2k1 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have hexp_eq : (k : ℝ) * ((k : ℝ) + 2) / ((2 : ℝ) * (k : ℝ) + 1) = (k : ℝ) / (((2 : ℝ) * (k : ℝ) + 1) / ((k : ℝ) + 2)) := by
        rw [div_div_eq_mul_div]
      calc (n : ℝ) = ((n : ℝ) ^ ((2 * (k : ℝ) + 1) / ((k : ℝ) + 2))) ^ ((((2 * (k : ℝ) + 1) / ((k : ℝ) + 2))⁻¹ : ℝ)) := by
             rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ)), mul_comm, inv_mul_cancel₀ hexp_pos.ne', Real.rpow_one]
        _ < ((R / 2) ^ (k : ℝ)) ^ ((((2 * (k : ℝ) + 1) / ((k : ℝ) + 2))⁻¹ : ℝ)) := by
             apply Real.rpow_lt_rpow (by positivity) h3' (by positivity)
        _ = (R / 2) ^ ((k : ℝ) * (((2 * (k : ℝ) + 1) / ((k : ℝ) + 2))⁻¹ : ℝ)) := by
             rw [← Real.rpow_mul (by positivity : 0 ≤ R / 2)]
        _ = (R / 2) ^ ((k : ℝ) * ((k : ℝ) + 2) / ((2 : ℝ) * (k : ℝ) + 1)) := by
             congr 1; rw [hexp_eq]; rw [mul_comm, div_eq_mul_inv]; field_simp
    -- From h4: q^(2k+1) < (R/2)^k, so q < (R/2)^(k/(2k+1))
    have hq_bound : (q : ℝ) < (R / 2) ^ ((k : ℝ) / ((2 : ℝ) * (k : ℝ) + 1)) := by
      have h4' : (q : ℝ) ^ ((2 * (k : ℝ) + 1)) < (R / 2) ^ (k : ℝ) := h4
      have h2k1_pos : 0 < (2 : ℝ) * (k : ℝ) + 1 := by positivity
      calc (q : ℝ) = ((q : ℝ) ^ ((2 * (k : ℝ) + 1))) ^ (1 / ((2 * (k : ℝ) + 1) : ℝ)) := by
             rw [← Real.rpow_mul (by positivity : 0 ≤ (q : ℝ)), mul_comm, one_div, inv_mul_cancel₀ h2k1_pos.ne', Real.rpow_one]
        _ < ((R / 2) ^ (k : ℝ)) ^ (1 / ((2 * (k : ℝ) + 1) : ℝ)) := by
             apply Real.rpow_lt_rpow (by positivity) h4' (by positivity)
        _ = (R / 2) ^ ((k : ℝ) / ((2 : ℝ) * (k : ℝ) + 1)) := by rw [← Real.rpow_mul (by positivity : 0 ≤ R / 2)]; congr 1; ring
    -- From hq_bound: q^(k-1) < (R/2)^(k*(k-1)/(2k+1))
    -- First, R > 2 since h4: q^(2k+1) < (R/2)^k and q ≥ 1
    have hR_gt2 : R > 2 := by
      by_contra hR2
      push_neg at hR2
      have hR2' : (R / 2 : ℝ) ≤ 1 := by linarith
      have hR2_pow : (R / 2 : ℝ) ^ (k : ℝ) ≤ 1 := Real.rpow_le_one (by linarith) hR2' (by positivity)
      have hq_pow_ge1 : (q : ℝ) ^ (2 * (k : ℝ) + 1) ≥ 1 := by
        have : (1 : ℝ) ≤ q := by norm_cast
        exact Real.one_le_rpow this (by positivity)
      linarith
    have hq_pow_bound : (q : ℝ) ^ ((k : ℝ) - 1) < (R / 2) ^ ((k : ℝ) * ((k : ℝ) - 1) / ((2 : ℝ) * (k : ℝ) + 1)) := by
      have hksub_pos : 0 < (k : ℝ) - 1 := by linarith [show (k : ℝ) ≥ 2 by norm_cast]
      have hbase_gt1 : 1 < (R / 2) ^ ((k : ℝ) / ((2 : ℝ) * (k : ℝ) + 1)) := by
        apply Real.one_lt_rpow (by linarith : 1 < R / 2) (by positivity)
      calc (q : ℝ) ^ ((k : ℝ) - 1) < ((R / 2) ^ ((k : ℝ) / ((2 : ℝ) * (k : ℝ) + 1))) ^ ((k : ℝ) - 1) := by
             exact Real.rpow_lt_rpow (le_of_lt hq_pos) hq_bound hksub_pos
        _ = (R / 2) ^ ((k : ℝ) / ((2 : ℝ) * (k : ℝ) + 1) * ((k : ℝ) - 1)) := by rw [← Real.rpow_mul (by positivity : 0 ≤ R / 2)]
        _ = (R / 2) ^ ((k : ℝ) * ((k : ℝ) - 1) / ((2 : ℝ) * (k : ℝ) + 1)) := by congr 1; field_simp
    -- Now combine: n * q^(k-1) < (R/2)^(k*(k+2)/(2k+1)) * (R/2)^(k*(k-1)/(2k+1)) = (R/2)^k
    have hexp_sum : (k : ℝ) * ((k : ℝ) + 2) / ((2 : ℝ) * (k : ℝ) + 1) + (k : ℝ) * ((k : ℝ) - 1) / ((2 : ℝ) * (k : ℝ) + 1) = (k : ℝ) := by
      field_simp
      ring
    have hprod : (R / 2) ^ ((k : ℝ) * ((k : ℝ) + 2) / ((2 : ℝ) * (k : ℝ) + 1)) *
                 (R / 2) ^ ((k : ℝ) * ((k : ℝ) - 1) / ((2 : ℝ) * (k : ℝ) + 1)) = (R / 2) ^ ((k : ℝ)) := by
      rw [← Real.rpow_add hR2_pos, hexp_sum]
    calc (n : ℝ) * (q : ℝ) ^ ((k : ℝ) - 1) <
           (R / 2) ^ ((k : ℝ) * ((k : ℝ) + 2) / ((2 : ℝ) * (k : ℝ) + 1)) * (R / 2) ^ ((k : ℝ) * ((k : ℝ) - 1) / ((2 : ℝ) * (k : ℝ) + 1)) := by
           gcongr
      _ = (R / 2) ^ ((k : ℝ)) := hprod
  -- Now derive contradiction: (R-1)^k < ⌊R⌋₊^k < n * q^(k-1) < (R/2)^k
  -- So (R-1)^k < (R/2)^k, hence R - 1 < R/2, i.e., R < 2, contradicting hR_gt2
  -- Convert hoverflow to match types
  have hoverflow' : (⌊R⌋₊ : ℝ) ^ (k : ℝ) < (n : ℝ) * (q : ℝ) ^ ((k : ℝ) - 1) := by
    have eq1 : (⌊R⌋₊ : ℝ) ^ (k : ℝ) = (⌊R⌋₊ : ℝ) ^ k := Real.rpow_natCast (⌊R⌋₊ : ℝ) k
    have eq2 : (q : ℝ) ^ ((k : ℝ) - 1) = (q : ℝ) ^ (k - 1 : ℕ) := by
      have : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
      rw [this]
      norm_cast
    rw [eq1, eq2]
    convert hoverflow using 2
  have hchain : (R - 1) ^ (k : ℝ) < (R / 2) ^ (k : ℝ) := lt_trans (lt_trans h5 hoverflow') h7
  have hRm1_pos : 0 < R - 1 := by linarith
  have hR2_pos' : 0 < R / 2 := by linarith
  have hchain' : R - 1 < R / 2 := by
    by_contra hge
    push_neg at hge
    have : (R / 2) ^ (k : ℝ) ≤ (R - 1) ^ (k : ℝ) := by
      apply Real.rpow_le_rpow (by linarith) hge (by positivity)
    linarith
  linarith

/-- If every entry of a list is at least `x`, the product dominates `x` to the
length. -/
lemma pow_length_le_prod {L : List ℕ} {x : ℕ} (h : ∀ y ∈ L, x ≤ y) :
    x ^ L.length ≤ L.prod := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.length_cons, List.prod_cons]
    rw [pow_succ']
    have hhd : x ≤ hd := h hd (List.Mem.head tl)
    have htl := ih (fun y hy => h y (List.mem_cons_of_mem hd hy))
    calc x * x ^ tl.length ≤ x * tl.prod := Nat.mul_le_mul_left x htl
      _ ≤ hd * tl.prod := Nat.mul_le_mul_right tl.prod hhd

/-- The product of the first `m` entries as a product over `Finset.range`. -/
lemma prod_range_getD_eq_take_prod (L : List ℕ) :
    ∀ m : ℕ, m ≤ L.length → ∏ i ∈ Finset.range m, L.getD i 1 = (L.take m).prod := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    rw [Finset.prod_range_succ, ih (by omega)]
    have hmlt : m < L.length := by omega
    rw [List.prod_take_succ L m hmlt, List.getD_eq_getElem _ _ hmlt]

/-- The initial greedy boxes: the `k-1` largest prime factors, together with a
final box holding the product of the `k`-th and `(k+1)`-st largest ones.  Under
the assumption that this product is at most the cutoff, all boxes are good, and
they are already large enough to satisfy the greedy invariant. -/
lemma exists_initial_greedy_boxes {k a Rn : ℕ} (hk : 2 ≤ k)
    (hlen : k + 1 ≤ (descendingPrimeFactors a).length)
    (hxy : (descendingPrimeFactors a).get ⟨k - 1, by omega⟩ *
      (descendingPrimeFactors a).get ⟨k, by omega⟩ ≤ Rn) :
    ∃ b : Fin k → ℕ, (∀ i, 0 < b i) ∧ (∀ i, b i ≤ Rn ∨ (b i).Prime) ∧
      (∏ i, b i) = ((descendingPrimeFactors a).take (k + 1)).prod ∧
      (∀ p ∈ (descendingPrimeFactors a).drop (k + 1), p ^ (k + 1) ≤ ∏ i, b i) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set L := descendingPrimeFactors a with hL
  have hm1 : m + 1 < L.length := by omega
  have hm : m < L.length := by omega
  have hprime : ∀ i (hi : i < L.length), (L.getD i 1).Prime := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact (mem_descendingPrimeFactors (List.getElem_mem hi)).1
  have hxy' : L.getD m 1 * L.getD (m + 1) 1 ≤ Rn := by
    rw [List.getD_eq_getElem _ _ hm, List.getD_eq_getElem _ _ hm1]
    simpa [List.get_eq_getElem] using hxy
  refine ⟨fun i => if (i : ℕ) = m then L.getD m 1 * L.getD (m + 1) 1 else L.getD (i : ℕ) 1,
    ?_, ?_, ?_, ?_⟩
  · intro i
    have hi : (i : ℕ) < L.length := lt_of_lt_of_le i.2 (by omega)
    by_cases h : (i : ℕ) = m
    · simp only [h, if_true]
      exact Nat.mul_pos (hprime _ hm).pos (hprime _ hm1).pos
    · simp only [if_neg h]
      exact (hprime _ hi).pos
  · intro i
    have hi : (i : ℕ) < L.length := lt_of_lt_of_le i.2 (by omega)
    by_cases h : (i : ℕ) = m
    · exact Or.inl (by simp only [h, if_true]; exact hxy')
    · exact Or.inr (by simp only [if_neg h]; exact hprime _ hi)
  · rw [Fin.prod_univ_eq_prod_range
      (fun i => if i = m then L.getD m 1 * L.getD (m + 1) 1 else L.getD i 1) (m + 1)]
    rw [Finset.prod_range_succ]
    have hcongr : (∏ i ∈ Finset.range m,
          (if i = m then L.getD m 1 * L.getD (m + 1) 1 else L.getD i 1))
        = ∏ i ∈ Finset.range m, L.getD i 1 := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hik : i < m := Finset.mem_range.mp hi
      simp only [if_neg (by omega : ¬ i = m)]
    rw [hcongr, prod_range_getD_eq_take_prod L m (by omega)]
    simp only [if_true]
    have h1 : (L.take (m + 1)).prod = (L.take m).prod * L.getD m 1 := by
      rw [List.prod_take_succ L m hm, List.getD_eq_getElem _ _ hm]
    have h2 : (L.take (m + 1 + 1)).prod = (L.take (m + 1)).prod * L.getD (m + 1) 1 := by
      rw [List.prod_take_succ L (m + 1) hm1, List.getD_eq_getElem _ _ hm1]
    rw [h2, h1]
    ring
  · intro p hp
    have hprodeq : (∏ i : Fin (m + 1),
        (if (i : ℕ) = m then L.getD m 1 * L.getD (m + 1) 1 else L.getD (i : ℕ) 1))
        = (L.take (m + 1 + 1)).prod := by
      rw [Fin.prod_univ_eq_prod_range
        (fun i => if i = m then L.getD m 1 * L.getD (m + 1) 1 else L.getD i 1) (m + 1)]
      rw [Finset.prod_range_succ]
      have hcongr : (∏ i ∈ Finset.range m,
            (if i = m then L.getD m 1 * L.getD (m + 1) 1 else L.getD i 1))
          = ∏ i ∈ Finset.range m, L.getD i 1 := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hik : i < m := Finset.mem_range.mp hi
        simp only [if_neg (by omega : ¬ i = m)]
      rw [hcongr, prod_range_getD_eq_take_prod L m (by omega)]
      simp only [if_true]
      have h1 : (L.take (m + 1)).prod = (L.take m).prod * L.getD m 1 := by
        rw [List.prod_take_succ L m hm, List.getD_eq_getElem _ _ hm]
      have h2 : (L.take (m + 1 + 1)).prod = (L.take (m + 1)).prod * L.getD (m + 1) 1 := by
        rw [List.prod_take_succ L (m + 1) hm1, List.getD_eq_getElem _ _ hm1]
      rw [h2, h1]
      ring
    rw [hprodeq]
    have hlenTake : (L.take (m + 1 + 1)).length = m + 1 + 1 := by
      rw [List.length_take]
      omega
    have hall : ∀ y ∈ L.take (m + 1 + 1), p ≤ y := by
      intro y hy
      exact descendingPrimeFactors_drop_le_take (r := m + 1 + 1) hy hp
    have hpow := pow_length_le_prod hall
    rwa [hlenTake] at hpow

/-- For an element that is not a product of `k` basis
elements, the product of the `k`-th and `(k+1)`-st largest prime factors exceeds
the cutoff. -/
lemma cutoff_lt_selected_pair {k n a : ℕ} {R : ℝ} (hk : 2 ≤ k) (hR : 2 ≤ R)
    (ha : 0 < a) (han : a ≤ n)
    (hscale1 : (n : ℝ) ^ ((1 : ℝ) / (k + 2)) <
      ((R / 2) ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1)))
    (hlen : k + 1 ≤ (descendingPrimeFactors a).length)
    (hnot : ¬ Mulk (extractionBasis n R) k a) :
    R < (((descendingPrimeFactors a).get ⟨k - 1, by omega⟩ : ℕ) : ℝ) *
      (((descendingPrimeFactors a).get ⟨k, by omega⟩ : ℕ) : ℝ) := by
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : p_{k-1} * p_k ≤ R
  -- Use scale1_overflow_bound to get the overflow condition
  have hn_pos : 0 < n := by
    by_contra h
    push_neg at h
    interval_cases n
    simp_all
  have hscale_overflow := scale1_overflow_bound hk hR hn_pos hscale1
  -- Get initial boxes via exists_initial_greedy_boxes
  have h_floor_R_pos : 0 < ⌊R⌋₊ := Nat.floor_pos.mpr (by linarith)
  obtain ⟨b, hbpos, hbgood, hbprod, hbrest⟩ := exists_initial_greedy_boxes hk hlen
    (by simpa using Nat.floor_le <| by positivity)
  -- Adjust hbgood: since p_{k-1} * p_k ≤ R, we have p_{k-1} * p_k ≤ ⌊R⌋₊
  have hb_le_floor : ∀ i, b i ≤ ⌊R⌋₊ ∨ (b i).Prime := by
    intro i
    rcases hbgood i with hbi | hprime
    · left
      have h_neg' : ((descendingPrimeFactors a).get ⟨k - 1, by omega⟩ *
          (descendingPrimeFactors a).get ⟨k, by omega⟩ : ℕ) ≤ R := by simpa using h_neg
      have hpk_le : (descendingPrimeFactors a).get ⟨k - 1, by omega⟩ *
          (descendingPrimeFactors a).get ⟨k, by omega⟩ ≤ ⌊R⌋₊ := Nat.le_floor h_neg'
      exact Nat.le_trans hbi hpk_le
    · right
      exact hprime
  -- Define the remaining primes to fold in
  have hk_pos : 0 < k := by omega
  let L := descendingPrimeFactors a
  let Lrest := L.drop (k + 1)
  -- Initial boxes have product = (take (k+1) L).prod
  -- Fold in the remaining primes
  let b_final := gfold k hk_pos b Lrest
  -- Need to show all final boxes are ≤ ⌊R⌋₊ or prime
  have hb_final_good := gfold_good_of_overflow k ⌊R⌋₊ n hk_pos h_floor_R_pos hscale_overflow
    Lrest b (fun p hp => (mem_descendingPrimeFactors (List.mem_of_mem_drop hp)).1) hbpos hb_le_floor
    hbrest (by
      simp only [L, Lrest]
      rw [hbprod]
      have hprod_eq := @descendingPrimeFactors_take_mul_drop a (k + 1) ha
      exact Nat.le_trans hprod_eq.le han)
  -- Show the product of b_final equals a
  have hb_final_prod : ∏ i, b_final i = a := by
    simp only [b_final, Lrest]
    have hinit_prod : ∏ i, b i = (L.take (k + 1)).prod := hbprod
    -- gfold preserves product: (∏ b) * Lrest.prod = a
    rw [gfold_prod]
    rw [hbprod]
    exact @descendingPrimeFactors_take_mul_drop a (k + 1) ha
  -- Show all boxes are in extractionBasis n R
  have hb_final_pos : ∀ i, 0 < b_final i :=
    gfold_pos k hk_pos b Lrest hbpos (fun p hp => Nat.Prime.pos (mem_descendingPrimeFactors (List.mem_of_mem_drop hp)).1)
  have hb_final_mem : ∀ i, b_final i ∈ extractionBasis n R := by
    intro i
    rcases hb_final_good i with hbR | hprime
    · -- Box is ≤ ⌊R⌋₊, so it's in extractionBasis (as a small composite)
      apply small_mem_extractionBasis
      · exact Nat.one_le_iff_ne_zero.mpr (hb_final_pos i).ne'
      · have : (b_final i : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast hbR
        exact le_trans this (Nat.floor_le (by linarith : 0 ≤ R))
    · -- Box is prime, need p ≤ n
      -- Since ∏ i, b_final i = a and b_final i divides the product, and b_final i is prime,
      -- we have b_final i ∈ a.primeFactors, so b_final i ≤ a ≤ n
      have hdvd : b_final i ∣ a := by
        have h1 : b_final i ∣ ∏ j : Fin k, b_final j := by
          exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
        rwa [hb_final_prod] at h1
      simp only [b_final] at hdvd
      have hle : b_final i ≤ a := Nat.le_of_dvd ha hdvd
      exact prime_mem_extractionBasis hprime (Nat.le_trans hle han)
  -- Now we have all boxes in extractionBasis and product = a, so Mulk
  have hmulK := mulk_of_good_boxes ha han b_final hb_final_pos hb_final_good hb_final_prod
  exact hnot hmulK

/-! ### Product bounds for the selected prefix -/

/-- Splitting a list product at two indices. -/
lemma list_prod_split_three (M : List ℕ) (a b : ℕ) (hab : a ≤ b) :
    ((M.take a).prod) * (((M.take b).drop a).prod) * ((M.drop b).prod) = M.prod := by
  have h1 : (M.take b).take a = M.take a := by simp [List.take_take, hab]
  have key : M.take b = M.take a ++ (M.take b).drop a := by
    conv_lhs => rw [← List.take_append_drop a (M.take b)]
    simp [h1]
  conv_rhs =>
    rw [← List.take_append_drop b M, List.prod_append, key, List.prod_append]

/-- For a nonincreasing list, the product of the entries with indices in
`[a, b)` is at least `M[b-1] ^ (b - a)`. -/
lemma sortedGE_segment_pow_le {M : List ℕ} (hsorted : M.SortedGE)
    {a b : ℕ} (hab : a < b) (hb : b ≤ M.length) :
    (M.get ⟨b - 1, by omega⟩) ^ (b - a) ≤ ((M.take b).drop a).prod := by
  -- The segment has length (b - a)
  have hlen : ((M.take b).drop a).length = b - a := by
    simp [List.length_drop, List.length_take]
    omega
  -- Use length to rewrite
  rw [← hlen]
  -- Key lemma: for a list where all elements are ≥ x, we have x^(length) ≤ prod
  have hkey : ∀ (L : List ℕ) (x : ℕ), (∀ y ∈ L, x ≤ y) → x ^ L.length ≤ L.prod := by
    intro L x hmem
    induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.length_cons, List.prod_cons]
      rw [pow_succ']
      have hhd : x ≤ hd := hmem hd (List.Mem.head tl)
      have htl := ih (fun y hy => hmem y (List.mem_cons_of_mem hd hy))
      calc x * x ^ tl.length ≤ x * tl.prod := Nat.mul_le_mul_left x htl
        _ ≤ hd * tl.prod := Nat.mul_le_mul_right tl.prod hhd
  apply hkey
  intro y hy
  -- y is in (M.take b).drop a, so y = M[i] for some a ≤ i < b
  have hy_take : y ∈ M.take b := List.mem_of_mem_drop hy
  -- Get the index i of y in M.take b
  obtain ⟨i, hi, hy_eq⟩ := List.mem_iff_get.mp hy_take
  -- Convert (M.take b).get i to M.get ⟨i, _⟩
  have hi_lt_b : (i : ℕ) < b := by
    have := i.isLt
    simp at this
    omega
  have hget_eq : (M.take b).get i = M.get ⟨i, by omega⟩ := by simp [List.getElem_take]
  rw [hget_eq]
  -- Need to show M.get ⟨b-1, _⟩ ≤ M.get ⟨i, _⟩ where i < b, so i ≤ b-1
  -- For SortedGE, smaller indices have larger values
  have hihelper : ∀ (L : List ℕ) (hL : L.SortedGE), ∀ {i j : Fin L.length}, i ≤ j → L.get j ≤ L.get i := by
    intro L hL i j hij
    exact (List.sortedGE_iff_antitone_get.mp hL) hij
  -- i ≤ b - 1
  have hi_le : (i : ℕ) ≤ b - 1 := Nat.le_pred_of_lt hi_lt_b
  -- Need to show b - 1 < M.length for the Fin
  have hb1_lt : b - 1 < M.length := by omega
  exact hihelper M hsorted (by exact hi_le)

/-- Product estimates for a nonincreasing list of `k+1` positive integers, in
the exact shape needed by the prefix estimates. -/
lemma sortedGE_prefix_prod_bounds {k : ℕ} (hk : 2 ≤ k) {M : List ℕ}
    (hlen : M.length = k + 1) (hsorted : M.SortedGE) :
    (∀ p ∈ M, p ≤ M.get ⟨0, by omega⟩) ∧
    (∀ p ∈ M.drop (k - 2), p ≤ M.get ⟨k - 2, by omega⟩) ∧
    M.get ⟨k, by omega⟩ ≤ M.get ⟨k - 1, by omega⟩ ∧
    M.get ⟨k - 1, by omega⟩ ≤ M.get ⟨k - 2, by omega⟩ ∧
    (M.get ⟨k - 1, by omega⟩) ^ k * M.get ⟨k, by omega⟩ ≤ M.prod ∧
    M.get ⟨0, by omega⟩ * ((M.get ⟨k - 1, by omega⟩) ^ (k - 1) * M.get ⟨k, by omega⟩)
      ≤ M.prod ∧
    (M.get ⟨k - 2, by omega⟩) ^ (k - 1) *
      (M.get ⟨k - 1, by omega⟩ * M.get ⟨k, by omega⟩) ≤ M.prod := by
  have hantitone : ∀ {i j : Fin M.length}, i ≤ j → M.get j ≤ M.get i :=
    fun {i j} hij => (List.sortedGE_iff_antitone_get.mp hsorted) hij
  have hkk : k < M.length := by omega
  have hk1 : k - 1 < M.length := by omega
  have hk2 : k - 2 < M.length := by omega
  have h0 : 0 < M.length := by omega
  -- every entry from position `t` on is at most the `t`-th entry
  have hdrop_le : ∀ (t : ℕ) (ht : t < M.length), ∀ p ∈ M.drop t, p ≤ M.get ⟨t, ht⟩ := by
    intro t ht p hp
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
    have hj' : (j : ℕ) < M.length - t := by
      have hjj := j.isLt
      simp [List.length_drop] at hjj
      omega
    have hidx : t + (j : ℕ) < M.length := by omega
    have hget : (M.drop t).get j = M.get ⟨t + (j : ℕ), hidx⟩ := by
      simp [List.getElem_drop]
    rw [← hj, hget]
    exact hantitone (by simp)
  -- the tail products
  have hdropk : (M.drop k).prod = M.get ⟨k, hkk⟩ := by
    have h1 : M.drop k = M[k] :: M.drop (k + 1) := List.drop_eq_getElem_cons hkk
    have h2 : M.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [h1, h2]
    simp [List.get_eq_getElem]
  have hdropk1 : (M.drop (k - 1)).prod = M.get ⟨k - 1, hk1⟩ * M.get ⟨k, hkk⟩ := by
    have h1 : M.drop (k - 1) = M[k - 1] :: M.drop (k - 1 + 1) :=
      List.drop_eq_getElem_cons hk1
    have h2 : k - 1 + 1 = k := by omega
    rw [h1, h2, List.prod_cons, hdropk]
    simp [List.get_eq_getElem]
  have htake1 : (M.take 1).prod = M.get ⟨0, h0⟩ := by
    have h1 : M.take 1 = [M[0]] := by
      rw [List.take_one]
      rw [List.head?_eq_getElem?]
      simp [List.getElem?_eq_getElem h0]
    rw [h1]
    simp [List.get_eq_getElem]
  -- (1) and (2)
  have hmax : ∀ p ∈ M, p ≤ M.get ⟨0, by omega⟩ := by
    intro p hp
    have := hdrop_le 0 h0 p (by simpa using hp)
    simpa using this
  have hmax2 : ∀ p ∈ M.drop (k - 2), p ≤ M.get ⟨k - 2, by omega⟩ := hdrop_le (k - 2) hk2
  -- (3) and (4)
  have h34 : M.get ⟨k, by omega⟩ ≤ M.get ⟨k - 1, by omega⟩ :=
    hantitone (show (⟨k - 1, hk1⟩ : Fin M.length) ≤ ⟨k, hkk⟩ by
      simp only [Fin.mk_le_mk]; omega)
  have h45 : M.get ⟨k - 1, by omega⟩ ≤ M.get ⟨k - 2, by omega⟩ :=
    hantitone (show (⟨k - 2, hk2⟩ : Fin M.length) ≤ ⟨k - 1, hk1⟩ by
      simp only [Fin.mk_le_mk]; omega)
  -- (5)
  have hsplit0 := list_prod_split_three M 0 k (by omega)
  have hseg0 : (M.get ⟨k - 1, by omega⟩) ^ k ≤ ((M.take k).drop 0).prod := by
    have := sortedGE_segment_pow_le hsorted (a := 0) (b := k) (by omega) (by omega)
    simpa using this
  have h5 : (M.get ⟨k - 1, by omega⟩) ^ k * M.get ⟨k, by omega⟩ ≤ M.prod := by
    have hprod : ((M.take k).drop 0).prod * M.get ⟨k, hkk⟩ = M.prod := by
      rw [← hdropk]
      simp
    calc (M.get ⟨k - 1, by omega⟩) ^ k * M.get ⟨k, by omega⟩
        ≤ ((M.take k).drop 0).prod * M.get ⟨k, hkk⟩ :=
          Nat.mul_le_mul_right _ hseg0
      _ = M.prod := hprod
  -- (6)
  have hsplit1 := list_prod_split_three M 1 k (by omega)
  have hseg1 : (M.get ⟨k - 1, by omega⟩) ^ (k - 1) ≤ ((M.take k).drop 1).prod := by
    have := sortedGE_segment_pow_le hsorted (a := 1) (b := k) (by omega) (by omega)
    exact this
  have h6 : M.get ⟨0, by omega⟩ *
      ((M.get ⟨k - 1, by omega⟩) ^ (k - 1) * M.get ⟨k, by omega⟩) ≤ M.prod := by
    have hprod : M.get ⟨0, h0⟩ * ((M.take k).drop 1).prod * M.get ⟨k, hkk⟩ = M.prod := by
      rw [← htake1, ← hdropk]
      exact hsplit1
    calc M.get ⟨0, by omega⟩ * ((M.get ⟨k - 1, by omega⟩) ^ (k - 1) * M.get ⟨k, by omega⟩)
        = M.get ⟨0, h0⟩ * (M.get ⟨k - 1, hk1⟩) ^ (k - 1) * M.get ⟨k, hkk⟩ := by ring
      _ ≤ M.get ⟨0, h0⟩ * ((M.take k).drop 1).prod * M.get ⟨k, hkk⟩ := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hseg1)
      _ = M.prod := hprod
  -- (7)
  have hsplit2 := list_prod_split_three M (k - 1) (k + 1) (by omega)
  have hsegk : (M.get ⟨k - 2, by omega⟩) ^ (k - 1) ≤ ((M.take (k - 1)).drop 0).prod := by
    have hseg := sortedGE_segment_pow_le hsorted (a := 0) (b := k - 1) (by omega) (by omega)
    have heq : (⟨k - 1 - 1, by omega⟩ : Fin M.length) = ⟨k - 2, hk2⟩ := by
      apply Fin.ext; simp only []; omega
    rw [heq] at hseg
    simpa using hseg
  have h7 : (M.get ⟨k - 2, by omega⟩) ^ (k - 1) *
      (M.get ⟨k - 1, by omega⟩ * M.get ⟨k, by omega⟩) ≤ M.prod := by
    have htakeall : M.take (k + 1) = M := by
      rw [← hlen]; exact List.take_length
    have hdropall : M.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have hprod : (M.take (k - 1)).prod *
        (M.get ⟨k - 1, hk1⟩ * M.get ⟨k, hkk⟩) = M.prod := by
      rw [← hdropk1, ← htakeall] at *
      simp
    calc (M.get ⟨k - 2, by omega⟩) ^ (k - 1) *
          (M.get ⟨k - 1, by omega⟩ * M.get ⟨k, by omega⟩)
        ≤ (M.take (k - 1)).prod * (M.get ⟨k - 1, hk1⟩ * M.get ⟨k, hkk⟩) := by
          refine Nat.mul_le_mul_right _ ?_
          simpa using hsegk
      _ = M.prod := hprod
  exact ⟨hmax, hmax2, h34, h45, h5, h6, h7⟩

/-! ### The real estimates for selected prefixes -/

/-- The unselected part is small. -/
lemma prefix_rem_upper {k : ℕ} (hk : 2 ≤ k) {R n P rem v w : ℝ}
    (hR : 1 < R) (hw : 1 ≤ w) (hwv : w ≤ v) (hrem : 1 ≤ rem)
    (h52 : R < v * w) (hF1 : v ^ k * w ≤ P) (hPn : P * rem ≤ n) :
    rem < n / R ^ (((k : ℝ) + 1) / 2) := by
  have hv : 0 < v := by linarith
  have hwpos : 0 < w := by linarith
  have hvw : 0 < v * w := by positivity
  have hRpos : 0 < R := by linarith
  -- Get rem * (v^k * w) ≤ n
  have hrem_bound : rem * (v ^ k * w) ≤ n := by nlinarith
  -- We need R ^ ((k+1)/2) * rem < n
  -- It suffices to show R ^ ((k+1)/2) < v ^ k * w (so R ^ ((k+1)/2) * rem < v^k * w * rem ≤ n)
  have hexp_pos : 0 < ((k : ℝ) + 1) / 2 := by positivity
  -- First show R ^ ((k+1)/2) < (v * w) ^ ((k+1)/2)
  have hRpow_lt : R ^ (((k : ℝ) + 1) / 2) < (v * w) ^ (((k : ℝ) + 1) / 2) :=
    Real.rpow_lt_rpow (by linarith) h52 hexp_pos
  -- Now show (v * w) ^ ((k+1)/2) ≤ v ^ k * w when w ≤ v and k ≥ 2
  have hvw_pow : (v * w) ^ (((k : ℝ) + 1) / 2) ≤ v ^ (k : ℝ) * w := by
    rw [Real.mul_rpow (le_of_lt hv) (le_of_lt hwpos)]
    have hv_rpow_pos : 0 < v ^ (((k : ℝ) - 1) / 2) := Real.rpow_pos_of_pos hv _
    have hw_rpow_pos : 0 < w ^ (((k : ℝ) - 1) / 2) := Real.rpow_pos_of_pos hwpos _
    have hk1_half : ((k : ℝ) - 1) / 2 ≥ 0 := by linarith [show (k : ℝ) ≥ 2 by norm_cast]
    have h1 : v ^ (((k : ℝ) + 1) / 2) * w * w ^ (((k : ℝ) - 1) / 2) ≤
              v ^ (((k : ℝ) + 1) / 2) * w * v ^ (((k : ℝ) - 1) / 2) := by
      gcongr
    have hw_split : w ^ (((k : ℝ) + 1) / 2) = w * w ^ (((k : ℝ) - 1) / 2) := by
      have hsum : (1 : ℝ) + ((k : ℝ) - 1) / 2 = ((k : ℝ) + 1) / 2 := by ring
      rw [← hsum, Real.rpow_add hwpos, Real.rpow_one]
    have hv_split : v ^ (k : ℝ) = v ^ (((k : ℝ) + 1) / 2) * v ^ (((k : ℝ) - 1) / 2) := by
      rw [← Real.rpow_add hv]; congr 1; ring
    calc v ^ (((k : ℝ) + 1) / 2) * w ^ (((k : ℝ) + 1) / 2)
        = v ^ (((k : ℝ) + 1) / 2) * (w * w ^ (((k : ℝ) - 1) / 2)) := by rw [hw_split]
      _ = v ^ (((k : ℝ) + 1) / 2) * w * w ^ (((k : ℝ) - 1) / 2) := by ring
      _ ≤ v ^ (((k : ℝ) + 1) / 2) * w * v ^ (((k : ℝ) - 1) / 2) := h1
      _ = v ^ (((k : ℝ) + 1) / 2) * v ^ (((k : ℝ) - 1) / 2) * w := by ring
      _ = v ^ (k : ℝ) * w := by rw [hv_split]
  -- Main goal: rem < n / R ^ ((k+1)/2)
  have hvk : v ^ (k : ℝ) = v ^ k := by rw [Real.rpow_natCast]
  have hR_pow_lt_vkw : R ^ (((k : ℝ) + 1) / 2) < v ^ k * w := by rw [← hvk]; exact lt_of_lt_of_le hRpow_lt hvw_pow
  rw [lt_div_iff₀ (Real.rpow_pos_of_pos hRpos _)]
  have hrem_pos : 0 < rem := by linarith
  have hmul : rem * R ^ (((k : ℝ) + 1) / 2) < rem * (v ^ k * w) :=
    mul_lt_mul_of_pos_left hR_pow_lt_vkw hrem_pos
  linarith

/-- The largest prime factor is below the cutoff. -/
lemma prefix_max_lt {k : ℕ} (hk : 2 ≤ k) {R n P rem p1 v w : ℝ}
    (hR : 1 < R) (hw : 1 ≤ w) (hwv : w ≤ v) (hrem : 1 ≤ rem) (hp1 : 0 ≤ p1)
    (h52 : R < v * w) (hF2 : p1 * (v ^ (k - 1) * w) ≤ P) (hPn : P * rem ≤ n)
    (hscale2 : n / R ^ ((k : ℝ) / 2) < R) :
    p1 < R := by
  -- From hscale2: n / R ^ (k/2) < R, so n < R * R ^ (k/2) = R ^ (k/2 + 1)
  have hRpos : 0 < R := by linarith
  have hR_pow_pos : 0 < R ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hRpos _
  have hn_lt : n < R * R ^ ((k : ℝ) / 2) := by
    rwa [div_lt_iff₀ hR_pow_pos] at hscale2
  -- v > 0 and w > 0
  have hwpos : 0 < w := by linarith
  have hvpos : 0 < v := by nlinarith
  -- If p1 = 0, then p1 < R since R > 0
  by_cases hp1_zero : p1 = 0
  · simp [hp1_zero, hRpos]
  -- Otherwise p1 > 0
  have hp1_pos : 0 < p1 := lt_of_le_of_ne hp1 (Ne.symm hp1_zero)
  have hP_pos : 0 < P := by
    have : 0 < p1 * (v ^ (k - 1) * w) := mul_pos hp1_pos (mul_pos (pow_pos hvpos _) hwpos)
    linarith
  -- From hrem ≥ 1: P ≤ n
  have hP_le_n : P ≤ n := by nlinarith
  -- We prove by contradiction: assume p1 ≥ R
  by_contra hle
  push_neg at hle
  -- From hle and hF2: R * (v ^ (k-1) * w) ≤ P
  have hvk_1_w_pos : 0 < v ^ (k - 1) * w := mul_pos (pow_pos hvpos _) hwpos
  have hprod_ge_R : R * (v ^ (k - 1) * w) ≤ P := by nlinarith
  -- So R * (v ^ (k-1) * w) ≤ n
  have hprod_le_n : R * (v ^ (k - 1) * w) ≤ n := by linarith
  -- Combined with n < R * R ^ (k/2): v ^ (k-1) * w < R ^ (k/2)
  have hvw_lt : v ^ (k - 1) * w < R ^ ((k : ℝ) / 2) := by
    nlinarith
  -- But v ^ (k-1) * w ≥ v * w > R (since v ≥ 1, w ≥ 1, k ≥ 2)
  have hv_ge_1 : 1 ≤ v := by linarith
  have hw_ge_1 : 1 ≤ w := by linarith
  have hvk_1_ge_v : v ≤ v ^ (k - 1) := by
    have := pow_le_pow_right₀ hv_ge_1 (by omega : k - 1 ≥ 1)
    simp only [pow_one] at this
    exact this
  have hvw_prod_ge : v ^ (k - 1) * w ≥ v * w := by nlinarith
  -- From h52: v * w > R
  have hvw_gt : v * w > R := h52
  -- So v ^ (k-1) * w > R
  have hw_pos : 0 < w := hwpos
  -- Key: R^(k/2) < (v*w)^(k/2) ≤ v^(k-1) * w for k ≥ 2
  have hvw_pos : 0 < v * w := by linarith
  have hRvwl : R ^ ((k : ℝ) / 2) < (v * w) ^ ((k : ℝ) / 2) :=
    Real.rpow_lt_rpow (by linarith) h52 (by positivity)
  -- (v*w)^(k/2) ≤ v^(k-1) * w for k ≥ 2 (since v ≥ w ≥ 1)
  have hvw_le : (v * w) ^ ((k : ℝ) / 2) ≤ v ^ (k - 1) * w := by
    rw [Real.mul_rpow (by linarith : 0 ≤ v) hwpos.le]
    have hexp : (k - 2 : ℝ) / 2 ≥ 0 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have h1 : w ^ ((k : ℝ) / 2) = w ^ ((k - 2 : ℝ) / 2) * w := by
      rw [← Real.rpow_add_one hwpos.ne']
      congr 1
      ring
    rw [h1]
    have h2 : w ^ ((k - 2 : ℝ) / 2) ≤ v ^ ((k - 2 : ℝ) / 2) :=
      Real.rpow_le_rpow (by linarith) hwv hexp
    calc v ^ ((k : ℝ) / 2) * (w ^ ((k - 2 : ℝ) / 2) * w)
        = v ^ ((k : ℝ) / 2) * w ^ ((k - 2 : ℝ) / 2) * w := by ring_nf
      _ ≤ v ^ ((k : ℝ) / 2) * v ^ ((k - 2 : ℝ) / 2) * w := by gcongr
      _ = v ^ ((k : ℝ) / 2 + (k - 2 : ℝ) / 2) * w := by rw [← Real.rpow_add (by linarith : 0 < v)]
      _ = v ^ (k - 1) * w := by
        congr 1
        rw [show (k : ℝ) / 2 + ((k : ℝ) - 2) / 2 = (k - 1 : ℕ) by
          have hk1 : 1 ≤ k := by omega
          rw [Nat.cast_sub hk1]
          field_simp
          ring]
        norm_cast
  linarith

/-- The third-from-last selected prime factor is below `(n/R)^{1/(k-1)}`. -/
lemma prefix_third_last_lt {k : ℕ} (hk : 2 ≤ k) {R n P rem u v w : ℝ}
    (hn : 0 < n) (hR : 1 < R) (hu : 0 < u) (hrem : 1 ≤ rem)
    (h52 : R < v * w) (hF3 : u ^ (k - 1) * (v * w) ≤ P) (hPn : P * rem ≤ n) :
    u < (n / R) ^ ((1 : ℝ) / (k - 1)) := by
  have hR_pos : 0 < R := by linarith
  have hvw_pos : 0 < v * w := by linarith
  -- P ≤ n / rem
  have hP_le : P ≤ n / rem := by
    have hrem_pos : 0 < rem := by linarith
    rwa [le_div_iff₀ hrem_pos]
  -- u^(k-1) * (v*w) ≤ n/rem
  have hF3_le : u ^ (k - 1) * (v * w) ≤ n / rem := by linarith
  -- u^(k-1) * R < u^(k-1) * (v*w) ≤ n/rem
  have hR_lt_vw : R < v * w := h52
  have hu_pow_pos : 0 < u ^ (k - 1) := pow_pos hu _
  have huR_lt : u ^ (k - 1) * R < u ^ (k - 1) * (v * w) := by nlinarith
  have huR_lt_rem : u ^ (k - 1) * R < n / rem := lt_of_lt_of_le huR_lt hF3_le
  have hrem_pos : 0 < rem := by linarith
  have hnR_pos : 0 < n / R := div_pos hn hR_pos
  have hu_pow_lt : u ^ (k - 1) < n / R := by
    have hdiv : u ^ (k - 1) < (n / rem) / R := by
      rw [lt_div_iff₀ hR_pos]
      linarith
    have hnrem_le_n : n / rem ≤ n := by
      have : (1 : ℝ) ≤ rem := hrem
      have : n / rem ≤ n / 1 := by gcongr
      simp at this
      linarith
    calc u ^ (k - 1) < (n / rem) / R := hdiv
      _ ≤ n / R := div_le_div_of_nonneg_right hnrem_le_n (le_of_lt hR_pos)
  -- Take (k-1)-th root
  -- Let k' = k - 1 as ℕ
  set k' := k - 1 with hk'_def
  have hk1_eq : (k' : ℝ) = (k : ℝ) - 1 := by
    rw [hk'_def]
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    simp
  have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith [show (k : ℝ) ≥ 2 by norm_cast]
  -- Goal: u < (n / R) ^ (1 / (k - 1))
  -- We have: u ^ (k - 1) < n / R
  -- Since u > 0, u = (u ^ (k-1)) ^ (1/(k-1))
  have hu_rpow : u = (u ^ k') ^ (1 / ((k : ℝ) - 1)) := by
    have h1 : (u ^ k' : ℝ) = u ^ (k' : ℝ) := (Real.rpow_natCast u k').symm
    rw [h1, hk1_eq, ← Real.rpow_mul (le_of_lt hu)]
    have hmul : (k : ℝ) - 1 ≠ 0 := by linarith
    rw [mul_div_cancel₀ _ hmul]
    simp
  have hu_pow_pos' : 0 < u ^ k' := pow_pos hu _
  rw [hu_rpow]
  refine Real.rpow_lt_rpow (le_of_lt hu_pow_pos') hu_pow_lt ?_
  have hk1_ne : (k : ℝ) - 1 ≠ 0 := by linarith
  positivity

/-- The last three selected prime factors absorb the
unselected part. -/
lemma prefix_absorb_lt {k : ℕ} {R n rem u : ℝ}
    (hR : 1 < R) (hu : 0 < u) (hrem : 1 ≤ rem) (hn : 0 < n)
    (hult : u < (n / R) ^ ((1 : ℝ) / (k - 1)))
    (hremlt : rem < n / R ^ (((k : ℝ) + 1) / 2))
    (hscale3 : ((n : ℝ) / R) ^ ((1 : ℝ) / (k - 1)) * (n / R ^ (((k : ℝ) + 1) / 2)) < R) :
    u * rem < R := by
  have hu_pos : 0 < u := hu
  have hrem_pos : 0 < rem := by linarith
  have h1 : ((n : ℝ) / R) ^ ((1 : ℝ) / (k - 1)) > 0 := by positivity
  have h2 : n / R ^ (((k : ℝ) + 1) / 2) > 0 := by positivity
  calc u * rem < (n / R) ^ ((1 : ℝ) / (k - 1)) * (n / R ^ (((k : ℝ) + 1) / 2)) := by nlinarith
    _ < R := hscale3

/-- The unselected part is smaller than the last
selected prime factor. -/
lemma prefix_last_gt {k : ℕ} (hk : 2 ≤ k) {R n rem u v w : ℝ}
    (hn : 0 < n) (hR : 1 < R) (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) (hrem : 1 ≤ rem)
    (h52 : R < v * w)
    (hult : u < (n / R) ^ ((1 : ℝ) / (k - 1)))
    (hremlt : rem < n / R ^ (((k : ℝ) + 1) / 2))
    (hscale4 : (n : ℝ) / R ^ (((k : ℝ) + 1) / 2) < (R ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1))) :
    rem < w := by
  -- First prove u * rem < R using hult, hremlt, and hscale4
  have habsorb : u * rem < R := by
    have h1 : u * rem < (n / R) ^ ((1 : ℝ) / (k - 1)) * (n / R ^ (((k : ℝ) + 1) / 2)) := by
      exact mul_lt_mul'' hult hremlt (le_of_lt hu) (by positivity)
    have h2 : (n / R) ^ ((1 : ℝ) / (k - 1)) * (n / R ^ (((k : ℝ) + 1) / 2)) <
              (n / R) ^ ((1 : ℝ) / (k - 1)) * ((R ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1))) := by
      apply mul_lt_mul_of_pos_left hscale4
      exact Real.rpow_pos_of_pos (div_pos hn (lt_trans zero_lt_one hR)) _
    have h3 : (n / R) ^ ((1 : ℝ) / (k - 1)) * ((R ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1))) ≤ R := by
      rw [← Real.mul_rpow (by positivity : 0 ≤ n / R) (by positivity : 0 ≤ R ^ (k : ℝ) / n)]
      have hsimp : n / R * (R ^ (k : ℝ) / n) = R ^ ((k : ℝ) - 1) := by
        have h1 : n / R * (R ^ (k : ℝ) / n) = R ^ (k : ℝ) / R := by field_simp [ne_of_gt hn]
        rw [h1]
        rw [div_eq_mul_inv, ← Real.rpow_neg_one R, ← Real.rpow_add (by linarith : 0 < R)]
        congr 1
      rw [hsimp]
      rw [← Real.rpow_mul (by linarith : 0 ≤ R)]
      have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith [show (k : ℝ) ≥ 2 by norm_cast]
      field_simp
      simp [Real.rpow_one]
    exact lt_of_lt_of_le (h1.trans h2) h3
  -- Now prove rem < w from habsorb, h52, and hvu
  have h53 : u * rem < v * w := lt_trans habsorb h52
  have hvrem : v * rem < v * w := by nlinarith
  exact (mul_lt_mul_iff_right₀ hv).mp hvrem

/-! ### Assembly -/

/-- Prefixes of a nonincreasing list are nonincreasing. -/
lemma sortedGE_take {L : List ℕ} (h : L.SortedGE) (r : ℕ) : (L.take r).SortedGE := by
  intro i j hij
  have hle : (L.take r).length ≤ L.length := by simp [List.length_take]
  have hi : (i : ℕ) < L.length := lt_of_lt_of_le i.2 hle
  have hj : (j : ℕ) < L.length := lt_of_lt_of_le j.2 hle
  have key := h (a := (⟨i, hi⟩ : Fin L.length)) (b := ⟨j, hj⟩) (by simpa using hij)
  simpa [List.get_eq_getElem, List.getElem_take] using key

/-- The numerical core of the prefix estimates.  Under the four
scale inequalities, every hard element has all of its first `k+1` prime factors
below the integer cutoff, its selected prefix is coprime to the remaining
factor, and each of its final three selected factors can absorb that remainder. -/
lemma hard_factor_numerical_estimates
    {k n a : ℕ} (hk : 2 ≤ k) {R : ℝ} (hR : 2 ≤ R)
    (hscale :
      ((n : ℝ) ^ ((1 : ℝ) / (k + 2)) <
          ((R / 2) ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1))) ∧
      ((n : ℝ) / R ^ ((k : ℝ) / 2) < R) ∧
      (((n : ℝ) / R) ^ ((1 : ℝ) / (k - 1)) *
          ((n : ℝ) / R ^ (((k : ℝ) + 1) / 2)) < R) ∧
      ((n : ℝ) / R ^ (((k : ℝ) + 1) / 2) <
          (R ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1))))
    (ha : 0 < a) (han : a ≤ n)
    (hnot : ¬ Mulk (extractionBasis n R) k a) :
    let L := descendingPrimeFactors a
    let rem := (L.drop (k + 1)).prod
    (∀ p ∈ L.take (k + 1), p ≤ ⌊R⌋₊) ∧
    Nat.Coprime (L.take (k + 1)).prod rem ∧
    (∀ p ∈ (L.take (k + 1)).drop (k - 2), p * rem ≤ ⌊R⌋₊) := by
  obtain ⟨hscale1, hscale2, hscale3, hscale4⟩ := hscale
  intro L rem
  have hR1 : (1 : ℝ) < R := by linarith
  have hR0 : (0 : ℝ) ≤ R := by linarith
  -- the descending prime factor list is long enough
  have hlen : k + 1 ≤ L.length := by
    have h := primeFactors_length_gt_of_not_mulk ha han (by linarith) hnot
    rw [descendingPrimeFactors_length]
    omega
  set M : List ℕ := L.take (k + 1) with hM
  have hMlen : M.length = k + 1 := by
    rw [hM, List.length_take]
    omega
  have hMsorted : M.SortedGE := sortedGE_take (descendingPrimeFactors_sortedGE a) _
  have hMprime : ∀ p ∈ M, p.Prime := fun p hp =>
    (mem_descendingPrimeFactors (List.mem_of_mem_take hp)).1
  have hMpos : ∀ p ∈ M, 0 < p := fun p hp => (hMprime p hp).pos
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ :=
    sortedGE_prefix_prod_bounds hk hMlen hMsorted
  -- notation for the relevant factors
  set p1 : ℕ := M.get ⟨0, by omega⟩ with hp1def
  set u : ℕ := M.get ⟨k - 2, by omega⟩ with hudef
  set v : ℕ := M.get ⟨k - 1, by omega⟩ with hvdef
  set w : ℕ := M.get ⟨k, by omega⟩ with hwdef
  set P : ℕ := M.prod with hPdef
  have hmemp1 : p1 ∈ M := by rw [hp1def]; exact List.get_mem _ _
  have hmemu : u ∈ M := by rw [hudef]; exact List.get_mem _ _
  have hmemv : v ∈ M := by rw [hvdef]; exact List.get_mem _ _
  have hmemw : w ∈ M := by rw [hwdef]; exact List.get_mem _ _
  -- the factorization `P * rem = a`
  have hPrem : P * rem = a := descendingPrimeFactors_take_mul_drop ha
  have hrem_pos : 0 < rem := by
    apply List.prod_pos
    intro x hx
    exact (mem_descendingPrimeFactors (List.mem_of_mem_drop hx)).1.pos
  -- the real-valued data
  have hw1R : (1 : ℝ) ≤ (w : ℝ) := by
    have := (hMprime w hmemw).two_le
    exact_mod_cast Nat.one_le_of_lt this
  have hwvR : (w : ℝ) ≤ (v : ℝ) := by exact_mod_cast hb3
  have hvuR : (v : ℝ) ≤ (u : ℝ) := by exact_mod_cast hb4
  have hremR : (1 : ℝ) ≤ (rem : ℝ) := by exact_mod_cast hrem_pos
  have hu0R : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (hMpos u hmemu)
  have hv0R : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (hMpos v hmemv)
  have hp1R : (0 : ℝ) ≤ (p1 : ℝ) := by positivity
  have hn0R : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := lt_of_lt_of_le ha han
    exact_mod_cast this
  have hPnR : (P : ℝ) * (rem : ℝ) ≤ (n : ℝ) := by
    have : (P * rem : ℕ) ≤ n := by rw [hPrem]; exact han
    exact_mod_cast this
  have hF1R : (v : ℝ) ^ k * (w : ℝ) ≤ (P : ℝ) := by exact_mod_cast hb5
  have hF2R : (p1 : ℝ) * ((v : ℝ) ^ (k - 1) * (w : ℝ)) ≤ (P : ℝ) := by exact_mod_cast hb6
  have hF3R : (u : ℝ) ^ (k - 1) * ((v : ℝ) * (w : ℝ)) ≤ (P : ℝ) := by exact_mod_cast hb7

  have h52 : R < (v : ℝ) * (w : ℝ) := by
    have hcut := cutoff_lt_selected_pair hk hR ha han hscale1 hlen hnot
    have hgv : (L.get ⟨k - 1, by omega⟩ : ℕ) = v := by
      simp [hvdef, hM, List.get_eq_getElem, List.getElem_take]
    have hgw : (L.get ⟨k, by omega⟩ : ℕ) = w := by
      simp [hwdef, hM, List.get_eq_getElem, List.getElem_take]
    rw [hgv, hgw] at hcut
    exact hcut
  -- the five estimates
  have hremlt : (rem : ℝ) < (n : ℝ) / R ^ (((k : ℝ) + 1) / 2) :=
    prefix_rem_upper hk hR1 hw1R hwvR hremR h52 hF1R hPnR
  have hp1lt : (p1 : ℝ) < R :=
    prefix_max_lt hk hR1 hw1R hwvR hremR hp1R h52 hF2R hPnR hscale2
  have hult : (u : ℝ) < ((n : ℝ) / R) ^ ((1 : ℝ) / (k - 1)) :=
    prefix_third_last_lt hk hn0R hR1 hu0R hremR h52 hF3R hPnR
  have habs : (u : ℝ) * (rem : ℝ) < R :=
    prefix_absorb_lt hR1 hu0R hremR hn0R hult hremlt hscale3
  have hlast : (rem : ℝ) < (w : ℝ) :=
    prefix_last_gt hk hn0R hR1 hu0R hv0R hvuR hremR h52 hult hremlt hscale4
  refine ⟨?_, ?_, ?_⟩
  · -- every selected factor is below the integer cutoff
    intro p hp
    have hple : p ≤ p1 := hb1 p hp
    have : (p : ℝ) ≤ R := by
      have : (p : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast hple
      linarith
    exact Nat.le_floor this
  · -- the selected prefix is coprime to the remainder
    have hsmall : rem < L.get ⟨k + 1 - 1, by omega⟩ := by
      have hgw : (L.get ⟨k + 1 - 1, by omega⟩ : ℕ) = w := by
        simp [hwdef, hM, List.get_eq_getElem, List.getElem_take]
      rw [hgw]
      exact_mod_cast hlast
    exact descendingPrimeFactors_take_coprime_drop (by omega) hlen hsmall
  · -- each of the last three selected factors absorbs the remainder
    intro p hp
    have hple : p ≤ u := hb2 p hp
    have hlt : ((p * rem : ℕ) : ℝ) ≤ R := by
      have h1 : ((p : ℝ)) ≤ (u : ℝ) := by exact_mod_cast hple
      have h2 : (p : ℝ) * (rem : ℝ) ≤ (u : ℝ) * (rem : ℝ) := by
        apply mul_le_mul_of_nonneg_right h1 (by positivity)
      push_cast
      linarith
    exact Nat.le_floor hlt

/-- Eventually the adjustable cutoff is at least two. -/
lemma extraction_cutoff_eventually_two (k : ℕ) (hk : 2 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ η * Sr k n :=
  (extraction_cutoff_tendsto_atTop k hk η hη).eventually_ge_atTop 2

/-- The large-cardinality extraction theorem follows once the numerical
estimates supply the exact local hypotheses of
`selected_factor_properties_of_local_absorbers`.  This packages the final
prepartition and readout assembly separately from the real-valued estimates. -/
lemma extraction_large_card_of_local_absorbers
    (k : ℕ) (hk : 2 ≤ k) (η : ℝ) (hη : 0 < η)
    (hlocal : ∀ᶠ n : ℕ in Filter.atTop, ∀ A Aeasy Ahard : Finset ℕ,
      A ⊆ Finset.Icc 1 n → DistPrimitive k A → k + 1 ≤ A.card →
      A = Aeasy ∪ Ahard → Disjoint Aeasy Ahard →
      (∀ a ∈ Ahard, ¬ Mulk (extractionBasis n (η * Sr k n)) k a) →
      (∀ a ∈ Ahard, k < a.primeFactorsList.length) →
      (∀ a ∈ Ahard,
        ¬ HasPrivatePrimePowerBelow A ⌊η * Sr k n⌋₊ a) →
      (∀ a ∈ Ahard, ¬ HasPrivateDivisorBelow A ⌊η * Sr k n⌋₊ a) →
      let R := ⌊η * Sr k n⌋₊
      (∀ a ∈ Ahard, ∀ p ∈ (descendingPrimeFactors a).take (k + 1), p ≤ R) ∧
      (∀ a ∈ Ahard,
        Nat.Coprime ((descendingPrimeFactors a).take (k + 1)).prod
          ((descendingPrimeFactors a).drop (k + 1)).prod) ∧
      (∀ a ∈ Ahard,
        ¬ ((descendingPrimeFactors a).take (k + 1)).Nodup →
        ∃ ell ∈ (descendingPrimeFactors a).take (k + 1),
          ell ^ ((descendingPrimeFactors a).take (k + 1)).count ell *
            ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R) ∧
      (∀ a ∈ Ahard,
        ((descendingPrimeFactors a).take (k + 1)).Nodup →
        ∀ p ∈ selectedPrimeFactors a (k + 1),
        ∀ q ∈ selectedPrimeFactors a (k + 1), p ≠ q →
        ∃ ell ∈ selectedPrimeFactors a (k + 1), ell ≠ p ∧ ell ≠ q ∧
          ell * ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → DistPrimitive k A → k + 1 ≤ A.card →
      ∃ (Aeasy Ahard : Finset ℕ) (T : ℕ → Finset ℕ),
        A = Aeasy ∪ Ahard ∧ Disjoint Aeasy Ahard ∧
        (Aeasy.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η * Sr k n) ∧
        (∀ a ∈ Ahard, (T a).card = k + 1 ∧
          (∀ p ∈ T a, p.Prime ∧ p ∣ a) ∧ (∏ p ∈ T a, p) ≤ a ∧ a ≤ n) ∧
        (∀ a ∈ Ahard, ∀ b ∈ Ahard, a ≠ b →
          ((T a) ∩ (T b)).card ≤ 1) := by
  -- First establish eventual prepartition
  have hpart := extraction_prepartition_eventually k hk η hη
  filter_upwards [hlocal, hpart] with n hlocal hpart
  intro A hAsub hAprim hAk
  obtain ⟨Aeasy, Ahard, hAeq, hdisj, hAeasy_card, hAhard_cond⟩ := hpart A hAsub hAprim hAk
  -- Apply hlocal to get properties of selectedPrimeFactors
  specialize hlocal A Aeasy Ahard hAsub hAprim hAk hAeq hdisj
    hAhard_cond.1 hAhard_cond.2.1 hAhard_cond.2.2.1 hAhard_cond.2.2.2
  -- Set up arguments for selected_factor_properties_of_local_absorbers
  let R := ⌊η * Sr k n⌋₊
  have hHA : Ahard ⊆ A := by rw [hAeq]; exact Finset.subset_union_right
  have hpos : ∀ a ∈ Ahard, 0 < a := fun a ha => (Finset.mem_Icc.mp (hAsub (hAeq ▸ Finset.mem_union_right _ ha))).1
  have hlen : ∀ a ∈ Ahard, k + 1 ≤ (descendingPrimeFactors a).length := by
    intro a ha
    rw [descendingPrimeFactors_length]
    exact Nat.succ_le_of_lt (hAhard_cond.2.1 a ha)
  have hsmall : ∀ a ∈ Ahard, ∀ p ∈ (descendingPrimeFactors a).take (k + 1), p ≤ R := hlocal.1
  have hcop : ∀ a ∈ Ahard, Nat.Coprime ((descendingPrimeFactors a).take (k + 1)).prod
      ((descendingPrimeFactors a).drop (k + 1)).prod := hlocal.2.1
  have hnoPow : ∀ a ∈ Ahard, ¬ HasPrivatePrimePowerBelow A R a := hAhard_cond.2.2.1
  have hnoDiv : ∀ a ∈ Ahard, ¬ HasPrivateDivisorBelow A R a := hAhard_cond.2.2.2
  have hdupAbsorb : ∀ a ∈ Ahard,
      ¬ ((descendingPrimeFactors a).take (k + 1)).Nodup →
      ∃ ell ∈ (descendingPrimeFactors a).take (k + 1),
        ell ^ ((descendingPrimeFactors a).take (k + 1)).count ell *
          ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R := hlocal.2.2.1
  have hpairAbsorb : ∀ a ∈ Ahard,
      ((descendingPrimeFactors a).take (k + 1)).Nodup →
      ∀ p ∈ selectedPrimeFactors a (k + 1),
      ∀ q ∈ selectedPrimeFactors a (k + 1), p ≠ q →
      ∃ ell ∈ selectedPrimeFactors a (k + 1), ell ≠ p ∧ ell ≠ q ∧
        ell * ((descendingPrimeFactors a).drop (k + 1)).prod ≤ R := hlocal.2.2.2
  -- Apply the selected-factor assembly theorem.
  obtain ⟨hnoddup, hlin⟩ := selected_factor_properties_of_local_absorbers
    hAprim hAk hHA hpos hlen hsmall hcop hnoPow hnoDiv hdupAbsorb hpairAbsorb
  -- Convert to the form extraction_readout_of_selected_factors needs
  have hlen' : ∀ a ∈ Ahard, k + 1 ≤ a.primeFactorsList.length := by
    intro a ha
    rw [← descendingPrimeFactors_length]
    exact hlen a ha
  -- Use extraction_readout_of_selected_factors
  obtain ⟨T, hT⟩ := extraction_readout_of_selected_factors A Aeasy Ahard hAeq hdisj hAeasy_card hpos
    hlen' hnoddup
    (fun a ha => (Finset.mem_Icc.mp (hAsub (hAeq ▸ Finset.mem_union_right _ ha))).2) hlin
  exact ⟨Aeasy, Ahard, T, hT⟩

/-- The four scale inequalities in the slack form required by
`hard_factor_numerical_estimates`: the first one is applied with the halved
cutoff, which absorbs the rounding of `R` to `⌊R⌋₊`. -/
lemma scale_inequalities_halved (k : ℕ) (hk : 2 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop,
      let R : ℝ := η * Sr k n
      ((n : ℝ) ^ ((1 : ℝ) / (k + 2)) <
          ((R / 2) ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1))) ∧
      ((n : ℝ) / R ^ ((k : ℝ) / 2) < R) ∧
      (((n : ℝ) / R) ^ ((1 : ℝ) / (k - 1)) *
          ((n : ℝ) / R ^ (((k : ℝ) + 1) / 2)) < R) ∧
      ((n : ℝ) / R ^ (((k : ℝ) + 1) / 2) <
          (R ^ (k : ℝ) / n) ^ ((1 : ℝ) / (k - 1))) := by
  have h1 := scale_inequalities k hk (η / 2) (half_pos hη)
  have h2 := scale_inequalities k hk η hη
  filter_upwards [h1, h2] with n hn1 hn2
  simp only at hn1 hn2
  show let R : ℝ := η * Sr k n; _
  simp only [Sr]
  have h_eq : η / 2 * n ^ (2 / (k + 1 : ℝ)) / Real.log n ^ 2 = η * (n ^ (2 / (k + 1 : ℝ)) / Real.log n ^ 2 / 2) := by ring
  rw [h_eq] at hn1
  simp only [mul_div_assoc] at hn2 ⊢
  exact ⟨hn1.1, hn2.2.1, hn2.2.2.1, hn2.2.2.2⟩

/-- Large-cardinality core of the adjustable-cutoff extraction theorem.
The separate `extraction_small_card` lemma handles `A.card ≤ k`; this statement
isolates the genuine number-theoretic assignment and prime-factor argument. -/
theorem extraction_large_card (k : ℕ) (hk : 2 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → DistPrimitive k A → k + 1 ≤ A.card →
      ∃ (Aeasy Ahard : Finset ℕ) (T : ℕ → Finset ℕ),
        A = Aeasy ∪ Ahard ∧ Disjoint Aeasy Ahard ∧
        (Aeasy.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η * Sr k n) ∧
        (∀ a ∈ Ahard, (T a).card = k + 1 ∧
          (∀ p ∈ T a, p.Prime ∧ p ∣ a) ∧ (∏ p ∈ T a, p) ≤ a ∧ a ≤ n) ∧
        (∀ a ∈ Ahard, ∀ b ∈ Ahard, a ≠ b → ((T a) ∩ (T b)).card ≤ 1) := by
  apply extraction_large_card_of_local_absorbers k hk η hη
  filter_upwards [scale_inequalities_halved k hk η hη,
    extraction_cutoff_eventually_two k hk η hη] with n hscale hR
  intro A Aeasy Ahard hAsub hprim hcard hpart hdisj hnot hlen hnoPow hnoDiv
  have hHA : Ahard ⊆ A := by
    rw [hpart]
    exact Finset.subset_union_right
  have hpos : ∀ a ∈ Ahard, 0 < a := by
    intro a ha
    exact (Finset.mem_Icc.mp (hAsub (hHA ha))).1
  have hle : ∀ a ∈ Ahard, a ≤ n := by
    intro a ha
    exact (Finset.mem_Icc.mp (hAsub (hHA ha))).2
  have hnum : ∀ a ∈ Ahard,
      let L := descendingPrimeFactors a
      let rem := (L.drop (k + 1)).prod
      (∀ p ∈ L.take (k + 1), p ≤ ⌊η * Sr k n⌋₊) ∧
      Nat.Coprime (L.take (k + 1)).prod rem ∧
      (∀ p ∈ (L.take (k + 1)).drop (k - 2),
        p * rem ≤ ⌊η * Sr k n⌋₊) := by
    intro a ha
    exact hard_factor_numerical_estimates hk hR hscale (hpos a ha) (hle a ha) (hnot a ha)
  refine ⟨fun a ha => (hnum a ha).1, fun a ha => (hnum a ha).2.1, ?_⟩
  exact local_absorbers_of_last_three hk hprim hcard hHA hpos
    (fun a ha => by
      rw [descendingPrimeFactors_length]
      exact Nat.succ_le_of_lt (hlen a ha))
    (fun a ha => (hnum a ha).1)
    (fun a ha => (hnum a ha).2.1) hnoPow hnoDiv
    (fun a ha => (hnum a ha).2.2)

/-! ## The central dyadic-grid bound -/

/-- Bin index of a prime `p` at cutoff `c`, level `Q`, uniformity `r`, size `n`:
the unique `j` with `j d < c p / y ≤ (j+1) d`, where `d = 2^{-Q}` and
`y = n^{1/r}`.  (Concretely `j = ⌈c p 2^Q / y⌉ - 1`.) -/
noncomputable def binOf (c : ℝ) (Q r n : ℕ) (p : ℕ) : ℕ :=
  ⌈c * (p : ℝ) * (2 : ℝ) ^ Q / (n : ℝ) ^ ((1 : ℝ) / r)⌉₊ - 1

/-- The type of an edge `E`: the vector counting, for each bin `j`, how many
vertices of `E` lie in bin `j`. -/
noncomputable def typeOf (c : ℝ) (Q r n : ℕ) (E : Finset ℕ) : Fin (NQ Q) → ℕ :=
  fun j => (E.filter (fun p => binOf c Q r n p = (j : ℕ))).card

/-- The primes `≤ n` lying in bin `i`. -/
noncomputable def primeBin (c : ℝ) (Q r n : ℕ) (i : Fin (NQ Q)) : Finset ℕ :=
  (primesLE n).filter (fun p => binOf c Q r n p = (i : ℕ))

/-- The central edges of a hypergraph at cutoff `(c, Q, δ)`: those whose
vertices all lie in `(δ y, (Q/c) y]` with `y = n^{1/r}`. -/
noncomputable def centralEdges (c : ℝ) (Q : ℕ) (δ : ℝ) (r n : ℕ)
    (H : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  H.filter (fun E => ∀ p ∈ E,
    δ * (n : ℝ) ^ ((1 : ℝ) / r) < (p : ℝ) ∧
      (p : ℝ) ≤ ((Q : ℝ) / c) * (n : ℝ) ^ ((1 : ℝ) / r))

/-- The scale `S` equals `M²` with `M = y / log n`. -/
theorem Sr_eq_M_sq (k n : ℕ) :
    Sr k n = ((n : ℝ) ^ ((1 : ℝ) / (k + 1)) / Real.log n) ^ 2 := by
  unfold Sr; rw [div_pow]; congr 1
  rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / (k + 1))) 2, ← Real.rpow_mul (by positivity)]
  norm_num; ring_nf

/-- Key per-vertex mesh bound: for a central prime `p` the upper endpoint of its
bin scaled coordinate is at most `p / y`. -/
theorem binOf_upper_le (c : ℝ) (Q r n : ℕ) (hc0 : 0 < c) (hc1 : c < 1) (δ : ℝ)
    (hmesh : (1 : ℝ) / (2 : ℝ) ^ Q ≤ (1 - c) * δ) (hn : 1 ≤ n) (p : ℕ)
    (hlo : δ * (n : ℝ) ^ ((1 : ℝ) / r) < (p : ℝ)) :
    ((binOf c Q r n p : ℝ) + 1) ≤ (2 : ℝ) ^ Q * (p : ℝ) / (n : ℝ) ^ ((1 : ℝ) / r) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hy : (0:ℝ) < (n:ℝ) ^ ((1:ℝ)/r) := Real.rpow_pos_of_pos hn' _
  have h2 : (0:ℝ) < (2:ℝ)^Q := by positivity
  have hc' : (0:ℝ) < 1 - c := by linarith
  have hδpos : 0 < δ := by nlinarith [one_div_pos.mpr h2, hmesh]
  set y := (n:ℝ) ^ ((1:ℝ)/r) with hydef
  have hp : (0:ℝ) < (p:ℝ) := lt_trans (by positivity) hlo
  set x := c * (p:ℝ) * (2:ℝ)^Q / y with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx0
  have hcast : ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈x⌉₊ : ℝ) := by
    rw [Nat.cast_sub hceil1]; ring
  show ((binOf c Q r n p : ℝ) + 1) ≤ (2:ℝ)^Q * (p:ℝ) / y
  unfold binOf
  rw [← hydef, ← hxdef, hcast, le_div_iff₀ hy]
  have hlt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (le_of_lt hx0)
  have hxy : x * y = c * (p:ℝ) * (2:ℝ)^Q := by rw [hxdef]; field_simp
  have e1 : (1:ℝ) ≤ (1 - c) * δ * 2 ^ Q := by
    have h := mul_le_mul_of_nonneg_right hmesh (le_of_lt h2)
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt h2)] at h
  have hy2 : y ≤ (1 - c) * (p:ℝ) * 2^Q := by
    nlinarith [mul_lt_mul_of_pos_left hlo (mul_pos hc' h2), e1, hy]
  nlinarith [mul_lt_mul_of_pos_right hlt hy, hxy, hy2]

/-- For a central prime `p`, its bin index is a valid index in `Fin (NQ Q)`. -/
theorem binOf_lt_NQ (c : ℝ) (Q r n : ℕ) (hc0 : 0 < c) (hQ : 1 ≤ Q) (hn : 1 ≤ n) (p : ℕ)
    (hhi : (p : ℝ) ≤ ((Q : ℝ) / c) * (n : ℝ) ^ ((1 : ℝ) / r)) :
    binOf c Q r n p < NQ Q := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hy : (0:ℝ) < (n:ℝ) ^ ((1:ℝ)/r) := Real.rpow_pos_of_pos hn' _
  have h2 : (0:ℝ) < (2:ℝ)^Q := by positivity
  set y := (n:ℝ) ^ ((1:ℝ)/r) with hydef
  have hNQcast : ((NQ Q : ℕ) : ℝ) = (Q:ℝ) * (2:ℝ)^Q := by push_cast [NQ]; ring
  have hcp : c * (p:ℝ) ≤ (Q:ℝ) * y := by
    have h := mul_le_mul_of_nonneg_left hhi hc0.le
    have e : c * ((Q:ℝ)/c*y) = (Q:ℝ)*y := by field_simp
    rwa [e] at h
  have hx_le : c * (p:ℝ) * (2:ℝ)^Q / y ≤ ((NQ Q : ℕ):ℝ) := by
    rw [div_le_iff₀ hy, hNQcast]; nlinarith [hcp, h2, hy]
  have hceil_le : ⌈c * (p:ℝ) * (2:ℝ)^Q / y⌉₊ ≤ NQ Q := Nat.ceil_le.mpr hx_le
  have hNQpos : 0 < NQ Q := Nat.mul_pos hQ (pow_pos (by norm_num) Q)
  unfold binOf
  rw [← hydef]
  omega

/-- The type of a central edge sums to its cardinality. -/
theorem typeOf_sum (c : ℝ) (Q r n : ℕ) (hc0 : 0 < c) (hQ : 1 ≤ Q) (hn : 1 ≤ n) (E : Finset ℕ)
    (hcen : ∀ p ∈ E, (p : ℝ) ≤ ((Q : ℝ) / c) * (n : ℝ) ^ ((1 : ℝ) / r)) :
    ∑ j, typeOf c Q r n E j = E.card := by
  have hmaps : Set.MapsTo (fun p => binOf c Q r n p) (E : Set ℕ) (Finset.range (NQ Q) : Set ℕ) := by
    intro p hp
    simp only [Finset.coe_range, Set.mem_Iio]
    exact binOf_lt_NQ c Q r n hc0 hQ hn p (hcen p (Finset.mem_coe.mp hp))
  rw [eq_comm, Finset.card_eq_sum_card_fiberwise hmaps]
  simp only [typeOf]
  rw [Fin.sum_univ_eq_sum_range (fun b => (E.filter (fun p => binOf c Q r n p = b)).card)]

/-- The type of a central edge is admissible. -/
theorem typeOf_admissible (c : ℝ) (Q r n : ℕ) (hr : 1 ≤ r) (hc0 : 0 < c) (hc1 : c < 1) (hQ : 1 ≤ Q) (δ : ℝ)
    (hmesh : (1 : ℝ) / (2 : ℝ) ^ Q ≤ (1 - c) * δ) (hn : 1 ≤ n) (E : Finset ℕ)
    (hcard : E.card = r)
    (hlo : ∀ p ∈ E, δ * (n : ℝ) ^ ((1 : ℝ) / r) < (p : ℝ))
    (hhi : ∀ p ∈ E, (p : ℝ) ≤ ((Q : ℝ) / c) * (n : ℝ) ^ ((1 : ℝ) / r))
    (hprod : (∏ p ∈ E, p) ≤ n) :
    admissible r Q (typeOf c Q r n E) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hy : (0:ℝ) < (n:ℝ) ^ ((1:ℝ)/r) := Real.rpow_pos_of_pos hn' _
  have hmaps : ∀ p ∈ E, binOf c Q r n p ∈ Finset.range (NQ Q) := by
    intro p hp; rw [Finset.mem_range]
    exact binOf_lt_NQ c Q r n hc0 hQ hn p (hhi p hp)
  have key : (∏ j : Fin (NQ Q), (((j:ℕ):ℝ)+1)^(typeOf c Q r n E j))
      = ∏ p ∈ E, ((binOf c Q r n p : ℝ)+1) := by
    simp only [typeOf]
    rw [Fin.prod_univ_eq_prod_range
      (fun y => ((y:ℝ)+1)^((E.filter (fun p => binOf c Q r n p = y)).card))]
    rw [← Finset.prod_fiberwise_of_maps_to hmaps (fun p => ((binOf c Q r n p:ℝ)+1))]
    apply Finset.prod_congr rfl
    intro y hy
    rw [Finset.prod_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
      Finset.prod_const]
  have hyr : ((n:ℝ)^((1:ℝ)/r))^r = (n:ℝ) := by
    rw [← Real.rpow_natCast ((n:ℝ)^((1:ℝ)/r)) r, ← Real.rpow_mul hn'.le,
      one_div, inv_mul_cancel₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr), Real.rpow_one]
  have hprodR : (∏ p ∈ E, (p:ℝ)) ≤ (n:ℝ) := by
    rw [← Nat.cast_prod]; exact_mod_cast hprod
  have e2 : ∏ p ∈ E, ((2:ℝ)^Q * (p:ℝ) / (n:ℝ)^((1:ℝ)/r))
      = ((2:ℝ)^Q/(n:ℝ)^((1:ℝ)/r))^E.card * ∏ p ∈ E, (p:ℝ) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro p hp; ring
  have hbound : ∏ p ∈ E, ((binOf c Q r n p:ℝ)+1) ≤ (2:ℝ)^(Q*r) := by
    calc ∏ p ∈ E, ((binOf c Q r n p:ℝ)+1)
        ≤ ∏ p ∈ E, ((2:ℝ)^Q * (p:ℝ) / (n:ℝ)^((1:ℝ)/r)) := by
          apply Finset.prod_le_prod
          · intro p hp; positivity
          · intro p hp; exact binOf_upper_le c Q r n hc0 hc1 δ hmesh hn p (hlo p hp)
      _ = ((2:ℝ)^Q / (n:ℝ)^((1:ℝ)/r))^E.card * ∏ p ∈ E, (p:ℝ) := e2
      _ ≤ (2:ℝ)^(Q*r) := by
          rw [hcard, div_pow, ← pow_mul, hyr, div_mul_eq_mul_div, div_le_iff₀ hn']
          nlinarith [hprodR, pow_pos (show (0:ℝ)<2 by norm_num) (Q*r)]
  unfold admissible
  rw [← @Nat.cast_le ℝ]
  push_cast
  rw [key]
  exact hbound

/-- The type of a central edge of a linear `r`-uniform hypergraph lies in
`admTypes r Q`. -/
theorem typeOf_mem_admTypes (c : ℝ) (Q r n : ℕ) (hr : 1 ≤ r) (hc0 : 0 < c) (hc1 : c < 1) (hQ : 1 ≤ Q) (δ : ℝ)
    (hmesh : (1 : ℝ) / (2 : ℝ) ^ Q ≤ (1 - c) * δ) (hn : 1 ≤ n) (E : Finset ℕ)
    (hcard : E.card = r)
    (hlo : ∀ p ∈ E, δ * (n : ℝ) ^ ((1 : ℝ) / r) < (p : ℝ))
    (hhi : ∀ p ∈ E, (p : ℝ) ≤ ((Q : ℝ) / c) * (n : ℝ) ^ ((1 : ℝ) / r))
    (hprod : (∏ p ∈ E, p) ≤ n) :
    typeOf c Q r n E ∈ admTypes r Q := by
  rw [admTypes, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [types, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro j; rw [Finset.mem_range]
      calc typeOf c Q r n E j ≤ E.card := Finset.card_filter_le _ _
        _ = r := hcard
        _ < r + 1 := Nat.lt_succ_self r
    · rw [typeOf_sum c Q r n hc0 hQ hn E hhi, hcard]
  · exact typeOf_admissible c Q r n hr hc0 hc1 hQ δ hmesh hn E hcard hlo hhi hprod

/-- Off-diagonal pair-load bound: the total load on a pair of distinct bins is at
most the product of the two bin sizes, by linearity. -/
theorem central_offdiag_load_le (c : ℝ) (Q : ℕ) (δ : ℝ) (r n : ℕ)
    (H : Finset (Finset ℕ)) (hH : IsLinearPrimeHG r n H) (i j : Fin (NQ Q))
    (hij : i ≠ j) :
    ∑ E ∈ centralEdges c Q δ r n H, (typeOf c Q r n E i * typeOf c Q r n E j)
      ≤ (primeBin c Q r n i).card * (primeBin c Q r n j).card := by
  set cen := centralEdges c Q δ r n H with hcen
  set Fi := fun (E : Finset ℕ) => E.filter (fun p => binOf c Q r n p = (i:ℕ)) with hFi
  set Fj := fun (E : Finset ℕ) => E.filter (fun p => binOf c Q r n p = (j:ℕ)) with hFj
  have hsum : ∑ E ∈ cen, (typeOf c Q r n E i * typeOf c Q r n E j)
      = (cen.sigma (fun E => (Fi E) ×ˢ (Fj E))).card := by
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro E hE
    rw [Finset.card_product]; rfl
  rw [hsum, ← Finset.card_product (primeBin c Q r n i) (primeBin c Q r n j)]
  apply Finset.card_le_card_of_injOn (fun x => (x.2.1, x.2.2))
  · rintro ⟨E, p, q⟩ hx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.coe_product,
      Set.mem_prod] at hx
    obtain ⟨hEcen, hpq⟩ := hx
    simp only [hFi, hFj, Finset.mem_filter] at hpq
    obtain ⟨⟨hpE, hpi⟩, ⟨hqE, hqj⟩⟩ := hpq
    have hEH : E ∈ H := (Finset.mem_filter.mp hEcen).1
    have hprimes := (hH.1 E hEH).2.1
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, primeBin, Finset.mem_filter,
      primesLE, Finset.mem_range]
    refine ⟨⟨⟨?_, ?_⟩, hpi⟩, ⟨⟨?_, ?_⟩, hqj⟩⟩
    · exact Nat.lt_succ_of_le (hprimes p hpE).2
    · exact (hprimes p hpE).1
    · exact Nat.lt_succ_of_le (hprimes q hqE).2
    · exact (hprimes q hqE).1
  · rintro ⟨E, p, q⟩ hx ⟨E', p', q'⟩ hx' heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.coe_product,
      Set.mem_prod] at hx hx'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hpp, hqq⟩ := heq
    subst hpp; subst hqq
    obtain ⟨hEcen, hpq⟩ := hx
    obtain ⟨hE'cen, hpq'⟩ := hx'
    simp only [hFi, hFj, Finset.mem_filter] at hpq hpq'
    have hEH : E ∈ H := (Finset.mem_filter.mp hEcen).1
    have hE'H : E' ∈ H := (Finset.mem_filter.mp hE'cen).1
    have hpne : p ≠ q := by
      intro h; apply hij; apply Fin.ext
      rw [← hpq.1.2, h, hpq.2.2]
    have hEE' : E = E' := by
      by_contra hne
      have hcard := hH.2 E hEH E' hE'H hne
      have h2 : ({p, q} : Finset ℕ) ⊆ E ∩ E' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hpq.1.1, hpq'.1.1⟩
        · exact Finset.mem_inter.mpr ⟨hpq.2.1, hpq'.2.1⟩
      have := Finset.card_le_card h2
      rw [Finset.card_pair hpne] at this
      omega
    subst hEE'
    rfl

/-- Diagonal pair-load bound. -/
theorem central_diag_load_le (c : ℝ) (Q : ℕ) (δ : ℝ) (r n : ℕ)
    (H : Finset (Finset ℕ)) (hH : IsLinearPrimeHG r n H) (i : Fin (NQ Q)) :
    ∑ E ∈ centralEdges c Q δ r n H, (typeOf c Q r n E i).choose 2
      ≤ (primeBin c Q r n i).card.choose 2 := by
  set cen := centralEdges c Q δ r n H with hcen
  set Fi := fun (E : Finset ℕ) => E.filter (fun p => binOf c Q r n p = (i:ℕ)) with hFi
  have hsum : ∑ E ∈ cen, (typeOf c Q r n E i).choose 2
      = (cen.sigma (fun E => (Fi E).powersetCard 2)).card := by
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro E hE
    rw [Finset.card_powersetCard]; rfl
  rw [hsum, ← Finset.card_powersetCard 2 (primeBin c Q r n i)]
  apply Finset.card_le_card_of_injOn (fun x => x.2)
  · rintro ⟨E, s⟩ hx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hx
    obtain ⟨hEcen, hs⟩ := hx
    rw [Finset.mem_powersetCard] at hs
    obtain ⟨hsub, hscard⟩ := hs
    have hEH : E ∈ H := (Finset.mem_filter.mp hEcen).1
    have hprimes := (hH.1 E hEH).2.1
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨?_, hscard⟩
    intro x hx
    have hxFi := hsub hx
    simp only [hFi, Finset.mem_filter] at hxFi
    simp only [primeBin, Finset.mem_filter, primesLE, Finset.mem_range]
    exact ⟨⟨Nat.lt_succ_of_le (hprimes x hxFi.1).2, (hprimes x hxFi.1).1⟩, hxFi.2⟩
  · rintro ⟨E, s⟩ hx ⟨E', s'⟩ hx' heq
    simp only at heq
    subst heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hx hx'
    obtain ⟨hEcen, hs⟩ := hx
    obtain ⟨hE'cen, hs'⟩ := hx'
    rw [Finset.mem_powersetCard] at hs hs'
    have hEH : E ∈ H := (Finset.mem_filter.mp hEcen).1
    have hE'H : E' ∈ H := (Finset.mem_filter.mp hE'cen).1
    have hEE' : E = E' := by
      by_contra hne
      have hcard := hH.2 E hEH E' hE'H hne
      have h2 : s ⊆ E ∩ E' := Finset.subset_inter
        (hs.1.trans (Finset.filter_subset _ _)) (hs'.1.trans (Finset.filter_subset _ _))
      have := Finset.card_le_card h2
      rw [hs.2] at this
      omega
    subst hEE'
    rfl

/-- Weighted fiberwise sum: summing a weight over admissible types (weighted by
the number of central edges of that type) equals summing the weight of each
edge's type over the central edges. -/
theorem fiber_weight_sum (c : ℝ) (Q r n : ℕ) (cen : Finset (Finset ℕ))
    (hmaps : ∀ E ∈ cen, typeOf c Q r n E ∈ admTypes r Q) (f : (Fin (NQ Q) → ℕ) → ℝ) :
    ∑ t ∈ admTypes r Q, f t * ((cen.filter (fun E => typeOf c Q r n E = t)).card : ℝ)
      = ∑ E ∈ cen, f (typeOf c Q r n E) := by
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun E => f (typeOf c Q r n E))]
  apply Finset.sum_congr rfl
  intro t ht
  have h1 : ∑ E ∈ cen.filter (fun E => typeOf c Q r n E = t), f (typeOf c Q r n E)
       = ∑ E ∈ cen.filter (fun E => typeOf c Q r n E = t), f t := by
    apply Finset.sum_congr rfl; intro E hE; rw [(Finset.mem_filter.mp hE).2]
  rw [h1, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Membership in bin `i` is equivalent to lying in the scaled half-open
interval `(a, b]`. -/
theorem binOf_eq_iff (c : ℝ) (Q r n : ℕ) (hc0 : 0 < c) (hn1 : 1 ≤ n) (i : Fin (NQ Q))
    (p : ℕ) (hp : 1 ≤ p) :
    binOf c Q r n p = (i:ℕ) ↔
      ((i:ℕ):ℝ) * dQ Q / c * (n:ℝ)^((1:ℝ)/r) < (p:ℝ) ∧
      (p:ℝ) ≤ (((i:ℕ):ℝ)+1) * dQ Q / c * (n:ℝ)^((1:ℝ)/r) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hy : (0:ℝ) < (n:ℝ) ^ ((1:ℝ)/r) := Real.rpow_pos_of_pos hn' _
  have h2 : (0:ℝ) < (2:ℝ)^Q := by positivity
  have hpp : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  set y := (n:ℝ)^((1:ℝ)/r) with hydef
  set x := c * (p:ℝ) * (2:ℝ)^Q / y with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx0
  have hbeq : binOf c Q r n p = ⌈x⌉₊ - 1 := by rw [binOf, ← hydef, ← hxdef]
  rw [hbeq]
  have hstep : (⌈x⌉₊ - 1 = (i:ℕ)) ↔ (⌈x⌉₊ = (i:ℕ) + 1) := by omega
  rw [hstep, Nat.ceil_eq_iff (by omega : (i:ℕ)+1 ≠ 0)]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hAeq : ((i:ℕ):ℝ) * dQ Q / c * y = ((i:ℕ):ℝ)*y/(c*(2:ℝ)^Q) := by rw [dQ]; field_simp
  have hBeq : (((i:ℕ):ℝ)+1) * dQ Q / c * y = (((i:ℕ):ℝ)+1)*y/(c*(2:ℝ)^Q) := by rw [dQ]; field_simp
  rw [hAeq, hBeq]
  have hlt1 : ((i:ℕ):ℝ) < x ↔ ((i:ℕ):ℝ)*y/(c*(2:ℝ)^Q) < ↑p := by
    rw [hxdef, lt_div_iff₀ hy, div_lt_iff₀ (by positivity : (0:ℝ)<c*(2:ℝ)^Q)]
    constructor <;> intro h <;> nlinarith [h]
  have hle1 : x ≤ ((i:ℕ):ℝ)+1 ↔ (↑p:ℝ) ≤ (((i:ℕ):ℝ)+1)*y/(c*(2:ℝ)^Q) := by
    rw [hxdef, div_le_iff₀ hy, le_div_iff₀ (by positivity : (0:ℝ)<c*(2:ℝ)^Q)]
    constructor <;> intro h <;> nlinarith [h]
  rw [hlt1, hle1]

/-- Counting core: the number of primes `≤ n` in `(A, B]` equals
`π(B) - π(A)` when `A ≤ B ≤ n`. -/
theorem primeBin_card_count (c : ℝ) (Q r n : ℕ) (i : Fin (NQ Q)) (A B : ℕ)
    (hAB : A ≤ B) (hBn : B ≤ n)
    (hequiv : ∀ p ∈ primesLE n, (binOf c Q r n p = (i:ℕ) ↔ A < p ∧ p ≤ B)) :
    ((primeBin c Q r n i).card : ℝ)
      = (Nat.primeCounting B : ℝ) - (Nat.primeCounting A : ℝ) := by
  have e0 : primeBin c Q r n i = (primesLE n).filter (fun p => A < p ∧ p ≤ B) := by
    unfold primeBin
    apply Finset.filter_congr
    intro p hp; exact hequiv p hp
  have e1 : (primesLE n).filter (fun p => A < p ∧ p ≤ B)
      = (primesLE B).filter (fun p => A < p) := by
    ext p
    simp only [primesLE, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hpr⟩, hA, hB⟩; exact ⟨⟨by omega, hpr⟩, hA⟩
    · rintro ⟨⟨hpB, hpr⟩, hA⟩; exact ⟨⟨by omega, hpr⟩, hA, by omega⟩
  have e2 : (primesLE B).filter (fun p => ¬ (A < p)) = primesLE A := by
    ext p
    simp only [primesLE, Finset.mem_filter, Finset.mem_range, not_lt]
    constructor
    · rintro ⟨⟨_, hpr⟩, hA⟩; exact ⟨by omega, hpr⟩
    · rintro ⟨hpA, hpr⟩; exact ⟨⟨by omega, hpr⟩, by omega⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := primesLE B) (p := fun p => A < p)
  rw [e2] at hsplit
  have hAB' : (primesLE A).card ≤ (primesLE B).card := by
    apply Finset.card_le_card
    intro p; simp only [primesLE, Finset.mem_filter, Finset.mem_range]
    rintro ⟨hpA, hpr⟩; exact ⟨by omega, hpr⟩
  rw [e0, e1, primeCounting_eq_card, primeCounting_eq_card]
  have hcard : ((primesLE B).filter (fun p => A < p)).card
      = (primesLE B).card - (primesLE A).card := by omega
  rw [hcard, Nat.cast_sub hAB']

/-- Bridge: for large `n`, the number of primes in bin `i` equals the
prime-counting difference over the corresponding scaled interval. -/
theorem primeBin_card_eq_primesIn (c : ℝ) (Q r : ℕ) (hc0 : 0 < c) (hr : 2 ≤ r) (i : Fin (NQ Q)) :
    ∀ᶠ n : ℕ in atTop, ((primeBin c Q r n i).card : ℝ)
      = primesIn (((i:ℕ):ℝ) * dQ Q / c * (n:ℝ)^((1:ℝ)/r))
                 ((((i:ℕ):ℝ)+1) * dQ Q / c * (n:ℝ)^((1:ℝ)/r)) := by
  have hdq : 0 < dQ Q := by unfold dQ; positivity
  set K := (((i:ℕ):ℝ)+1) * dQ Q / c with hKdef
  have hbn : ∀ᶠ n : ℕ in atTop, K * (n:ℝ)^((1:ℝ)/r) ≤ (n:ℝ) := by
    have hexp : (0:ℝ) < 1 - 1/r := by
      have hr1 : (2:ℝ) ≤ r := by exact_mod_cast hr
      have : (1:ℝ)/r ≤ 1/2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr1
      linarith
    have htend : Tendsto (fun x : ℝ => x ^ (1 - 1/(r:ℝ))) atTop atTop :=
      tendsto_rpow_atTop hexp
    have h2 := (htend.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
    filter_upwards [h2, eventually_gt_atTop 0] with n hn hn0
    have hn' : (0:ℝ) < n := by exact_mod_cast hn0
    simp only [Function.comp] at hn
    rw [Real.rpow_sub hn', Real.rpow_one] at hn
    have hrpow : (0:ℝ) < (n:ℝ)^((1:ℝ)/r) := Real.rpow_pos_of_pos hn' _
    rw [le_div_iff₀ hrpow] at hn
    exact hn
  filter_upwards [hbn, eventually_ge_atTop 1] with n hev hn1
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hy : (0:ℝ) < (n:ℝ) ^ ((1:ℝ)/r) := Real.rpow_pos_of_pos hn' _
  set a := ((i:ℕ):ℝ) * dQ Q / c * (n:ℝ)^((1:ℝ)/r) with hadef
  set b := (((i:ℕ):ℝ)+1) * dQ Q / c * (n:ℝ)^((1:ℝ)/r) with hbdef
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hab : a ≤ b := by rw [hadef, hbdef]; gcongr; linarith
  have hAB : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hBn : ⌊b⌋₊ ≤ n := by
    have : ⌊b⌋₊ ≤ ⌊(n:ℝ)⌋₊ := Nat.floor_le_floor (by rw [hbdef, ← hKdef]; exact hev)
    rwa [Nat.floor_natCast] at this
  have hequiv : ∀ p ∈ primesLE n, (binOf c Q r n p = (i:ℕ) ↔ ⌊a⌋₊ < p ∧ p ≤ ⌊b⌋₊) := by
    intro p hp
    simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hp
    have hp1 : 1 ≤ p := hp.2.pos
    rw [binOf_eq_iff c Q r n hc0 hn1 i p hp1, ← hadef, ← hbdef]
    rw [Nat.floor_lt ha0, Nat.le_floor_iff hb0]
  rw [primesIn]
  exact primeBin_card_count c Q r n i ⌊a⌋₊ ⌊b⌋₊ hAB hBn hequiv

/-- Asymptotics for a single bin size: `N_i / M → r d / c`. -/
theorem primeBin_ratio_tendsto (c : ℝ) (Q r : ℕ) (hc0 : 0 < c) (hr : 2 ≤ r)
    (i : Fin (NQ Q)) :
    Tendsto (fun n : ℕ =>
        ((primeBin c Q r n i).card : ℝ) /
          ((n : ℝ) ^ ((1 : ℝ) / r) / Real.log n))
      atTop (nhds ((r : ℝ) * dQ Q / c)) := by
  have hdQ : 0 < dQ Q := by unfold dQ; positivity
  have ha : (0:ℝ) ≤ ((i:ℕ):ℝ) * dQ Q / c := by positivity
  have hab : ((i:ℕ):ℝ) * dQ Q / c < (((i:ℕ):ℝ)+1) * dQ Q / c := by
    apply div_lt_div_of_pos_right _ hc0
    apply mul_lt_mul_of_pos_right _ hdQ
    linarith
  have hb := prime_bin r hr (((i:ℕ):ℝ) * dQ Q / c) ((((i:ℕ):ℝ)+1) * dQ Q / c) ha hab
  have hlim : (r : ℝ) * ((((i:ℕ):ℝ)+1) * dQ Q / c - ((i:ℕ):ℝ) * dQ Q / c)
      = (r : ℝ) * dQ Q / c := by field_simp; ring
  rw [hlim] at hb
  refine hb.congr' ?_
  filter_upwards [primeBin_card_eq_primesIn c Q r hc0 hr i] with n hn
  rw [hn]

/-- For a fixed large `n` with the bin-size product bounds, the normalized
  central-edge count is at most `(1+γ) c^{-2} Λ_r`. -/
theorem central_bound_pointwise (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (Q : ℕ) (hQ : 1 ≤ Q) (δ : ℝ) (hmesh : (1:ℝ)/2^Q ≤ (1-c)*δ)
    (n : ℕ) (hn2 : 2 ≤ n) (H : Finset (Finset ℕ)) (hH : IsLinearPrimeHG (k+1) n H)
    (γ : ℝ) (hγ : 0 < γ)
    (hbound : ∀ i j : Fin (NQ Q),
        ((primeBin c Q (k+1) n i).card : ℝ) * (primeBin c Q (k+1) n j).card
          ≤ (1+γ) * (((k:ℝ)+1)*dQ Q/c)^2 * Sr k n) :
    ((centralEdges c Q δ (k+1) n H).card : ℝ) / Sr k n ≤ (1+γ) * c^(-2:ℤ) * Lam (k+1) := by
  have hn1 : 1 ≤ n := by omega
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hSpos : 0 < Sr k n := by rw [Sr_eq_M_sq]; positivity
  have h1γ : 0 < 1 + γ := by linarith
  have hc2pos : (0:ℝ) < c^2 := by positivity
  set cen := centralEdges c Q δ (k+1) n H with hcen
  set S := Sr k n with hSdef
  set r := k + 1 with hrdef
  have hmaps : ∀ E ∈ cen, typeOf c Q r n E ∈ admTypes r Q := by
    intro E hE
    rw [hcen, centralEdges, Finset.mem_filter] at hE
    obtain ⟨hEH, hpred⟩ := hE
    have hEspec := hH.1 E hEH
    exact typeOf_mem_admTypes c Q r n (by omega) hc0 hc1 hQ δ hmesh hn1 E hEspec.1
      (fun p hp => (hpred p hp).1) (fun p hp => (hpred p hp).2) hEspec.2.2
  set z : (Fin (NQ Q) → ℕ) → ℝ :=
    fun t => c^2 * ((cen.filter (fun E => typeOf c Q r n E = t)).card : ℝ) / ((1+γ)*S) with hzdef
  have hznn : ∀ t, 0 ≤ z t := by intro t; rw [hzdef]; positivity
  have hcoef : 0 ≤ c^2/((1+γ)*S) := by positivity
  have hoff : ∀ i j : Fin (NQ Q), i < j →
      ∑ t ∈ admTypes r Q, ((t i : ℝ) * t j) * z t ≤ (r : ℝ) ^ 2 * dQ Q ^ 2 := by
    intro i j hij
    rw [Finset.sum_congr rfl (fun t _ => by rw [hzdef]; ring :
        ∀ t ∈ admTypes r Q, ((t i:ℝ)*t j) * z t
          = c^2/((1+γ)*S) * (((t i:ℝ)*t j) * ((cen.filter (fun E => typeOf c Q r n E = t)).card:ℝ))),
      ← Finset.mul_sum, fiber_weight_sum c Q r n cen hmaps (fun t => (t i:ℝ)*t j)]
    have hload : (∑ E ∈ cen, ((typeOf c Q r n E i:ℝ) * (typeOf c Q r n E j)))
        ≤ ((primeBin c Q r n i).card : ℝ) * (primeBin c Q r n j).card := by
      have hcast : (∑ E ∈ cen, ((typeOf c Q r n E i:ℝ) * (typeOf c Q r n E j)))
          = ((∑ E ∈ cen, (typeOf c Q r n E i * typeOf c Q r n E j) : ℕ):ℝ) := by push_cast; rfl
      rw [hcast]; exact_mod_cast central_offdiag_load_le c Q δ r n H hH i j (ne_of_lt hij)
    calc c^2/((1+γ)*S) * (∑ E ∈ cen, ((typeOf c Q r n E i:ℝ) * (typeOf c Q r n E j)))
        ≤ c^2/((1+γ)*S) * (((primeBin c Q r n i).card : ℝ) * (primeBin c Q r n j).card) :=
          mul_le_mul_of_nonneg_left hload hcoef
      _ ≤ c^2/((1+γ)*S) * ((1+γ) * (((k:ℝ)+1)*dQ Q/c)^2 * S) :=
          mul_le_mul_of_nonneg_left (hbound i j) hcoef
      _ = (r : ℝ) ^ 2 * dQ Q ^ 2 := by rw [hrdef]; push_cast; field_simp
  have hdiag : ∀ i : Fin (NQ Q),
      ∑ t ∈ admTypes r Q, ((t i).choose 2 : ℝ) * z t ≤ (r : ℝ) ^ 2 / 2 * dQ Q ^ 2 := by
    intro i
    rw [Finset.sum_congr rfl (fun t _ => by rw [hzdef]; ring :
        ∀ t ∈ admTypes r Q, ((t i).choose 2 : ℝ) * z t
          = c^2/((1+γ)*S) * (((t i).choose 2:ℝ) * ((cen.filter (fun E => typeOf c Q r n E = t)).card:ℝ))),
      ← Finset.mul_sum, fiber_weight_sum c Q r n cen hmaps (fun t => ((t i).choose 2:ℝ))]
    have hload : (∑ E ∈ cen, ((typeOf c Q r n E i).choose 2 : ℝ))
        ≤ ((primeBin c Q r n i).card.choose 2 : ℝ) := by
      have hcast : (∑ E ∈ cen, ((typeOf c Q r n E i).choose 2 : ℝ))
          = ((∑ E ∈ cen, (typeOf c Q r n E i).choose 2 : ℕ):ℝ) := by push_cast; rfl
      rw [hcast]; exact_mod_cast central_diag_load_le c Q δ r n H hH i
    have hchoose2 : ((primeBin c Q r n i).card.choose 2 : ℝ)
        ≤ ((primeBin c Q r n i).card : ℝ)^2/2 := by
      rw [Nat.cast_choose_two]; nlinarith [Nat.cast_nonneg (α:=ℝ) (primeBin c Q r n i).card]
    have hNi2 : ((primeBin c Q r n i).card : ℝ)^2 ≤ (1+γ) * (((k:ℝ)+1)*dQ Q/c)^2 * S := by
      have := hbound i i; nlinarith [this]
    calc c^2/((1+γ)*S) * (∑ E ∈ cen, ((typeOf c Q r n E i).choose 2 : ℝ))
        ≤ c^2/((1+γ)*S) * (((primeBin c Q r n i).card : ℝ)^2/2) := by
          apply mul_le_mul_of_nonneg_left (le_trans hload hchoose2) hcoef
      _ ≤ c^2/((1+γ)*S) * ((1+γ) * (((k:ℝ)+1)*dQ Q/c)^2 * S / 2) := by
          apply mul_le_mul_of_nonneg_left _ hcoef; linarith [hNi2]
      _ = (r : ℝ) ^ 2 / 2 * dQ Q ^ 2 := by rw [hrdef]; push_cast; field_simp
  have hval : valQ r Q z = c^2/((1+γ)*S) * (cen.card:ℝ) := by
    unfold valQ
    rw [Finset.sum_congr rfl (fun t _ => by rw [hzdef]; ring :
        ∀ t ∈ admTypes r Q, z t
          = c^2/((1+γ)*S) * (1 * ((cen.filter (fun E => typeOf c Q r n E = t)).card:ℝ))),
      ← Finset.mul_sum, fiber_weight_sum c Q r n cen hmaps (fun _ => (1:ℝ))]
    simp
  have hpack : IsPacking r Q z := ⟨hznn, hoff, hdiag⟩
  have hle : valQ r Q z ≤ Lam r := by
    have h1 : valQ r Q z ≤ lamQ r Q :=
      le_csSup (packing_values_bddAbove r Q (by omega)) ⟨z, hpack, rfl⟩
    exact le_trans h1 (lamQ_le_Lam r Q (by omega) hQ)
  rw [hval] at hle
  have key : c^2 * (cen.card:ℝ) ≤ Lam r * ((1+γ)*S) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hle; linarith
  have hc2eq : c^(-2:ℤ) = (c^2)⁻¹ := by rw [zpow_neg, zpow_two, sq]
  rw [hc2eq, div_le_iff₀ hSpos]
  have goal2 : c^2 * (cen.card:ℝ) ≤ c^2 * ((1+γ)*(c^2)⁻¹*Lam r * S) := by
    have e : c^2 * ((1+γ)*(c^2)⁻¹*Lam r * S) = (1+γ)*Lam r*S := by field_simp
    rw [e]; nlinarith [key]
  exact le_of_mul_le_mul_left goal2 hc2pos

/-- Central dyadic-grid bound. -/
theorem central_bound_core (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (Q : ℕ) (hQ : 1 ≤ Q) (δ : ℝ)
    (hmesh : (1 : ℝ) / 2 ^ Q ≤ (1 - c) * δ)
    (H : ℕ → Finset (Finset ℕ)) (hH : ∀ n, IsLinearPrimeHG (k + 1) n (H n))
    (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ n in atTop,
      ((centralEdges c Q δ (k + 1) n (H n)).card : ℝ) / Sr k n
        ≤ c ^ (-2 : ℤ) * Lam (k + 1) + ε' := by
  set Λ := Lam (k+1) with hΛdef
  have hΛ : 0 ≤ Λ := Lam_nonneg _
  have hc2pos : (0:ℝ) < c^2 := by positivity
  set γ := ε' * c^2 / (Λ + 1) with hγdef
  have hγ : 0 < γ := by rw [hγdef]; positivity
  have hc2eq : c^(-2:ℤ) = (c^2)⁻¹ := by rw [zpow_neg, zpow_two, sq]
  have hfin : (1+γ) * c^(-2:ℤ) * Λ ≤ c^(-2:ℤ) * Λ + ε' := by
    rw [hc2eq, hγdef]
    have h1 : Λ / (Λ+1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have expand : (1 + ε' * c^2/(Λ+1)) * (c^2)⁻¹ * Λ
        = (c^2)⁻¹ * Λ + ε' * (Λ/(Λ+1)) := by field_simp
    rw [expand]
    have : ε' * (Λ/(Λ+1)) ≤ ε' := by nlinarith [h1, hε']
    linarith
  set L := ((k:ℝ)+1)*dQ Q/c with hLdef
  have hdq : 0 < dQ Q := by unfold dQ; positivity
  have hLpos : 0 < L := by rw [hLdef]; exact div_pos (mul_pos (by positivity) hdq) hc0
  have hpair : ∀ i j : Fin (NQ Q), ∀ᶠ n : ℕ in atTop,
      ((primeBin c Q (k+1) n i).card : ℝ) * (primeBin c Q (k+1) n j).card
        ≤ (1+γ) * L^2 * Sr k n := by
    intro i j
    have hi := primeBin_ratio_tendsto c Q (k+1) hc0 (by omega) i
    have hj := primeBin_ratio_tendsto c Q (k+1) hc0 (by omega) j
    simp only [Nat.cast_add, Nat.cast_one] at hi hj
    have hprod := hi.mul hj
    have hlt : L * L < (1+γ)*L^2 := by rw [pow_two]; nlinarith [mul_pos hLpos hLpos, hγ]
    have hev1 := hprod.eventually_lt_const hlt
    filter_upwards [hev1, eventually_gt_atTop 1] with n hn hn1
    have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
    have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    set M := (n:ℝ)^((1:ℝ)/((k:ℝ)+1))/Real.log n with hMdef
    have hMpos : 0 < M := by rw [hMdef]; positivity
    rw [Sr_eq_M_sq, ← hMdef]
    have expand : ((primeBin c Q (k+1) n i).card : ℝ) * (primeBin c Q (k+1) n j).card
        = (((primeBin c Q (k+1) n i).card : ℝ)/M) * (((primeBin c Q (k+1) n j).card : ℝ)/M) * M^2 := by
      field_simp
    rw [expand]
    exact mul_le_mul_of_nonneg_right (le_of_lt hn) (sq_nonneg M)
  have hall : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin (NQ Q),
      ((primeBin c Q (k+1) n i).card : ℝ) * (primeBin c Q (k+1) n j).card
        ≤ (1+γ) * L^2 * Sr k n :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun j => hpair i j))
  filter_upwards [hall, eventually_ge_atTop 2] with n hn hn2
  have hpt := central_bound_pointwise k hk c hc0 hc1 Q hQ δ hmesh n hn2 (H n) (hH n) γ hγ
    (fun i j => hn i j)
  calc ((centralEdges c Q δ (k + 1) n (H n)).card : ℝ) / Sr k n
      ≤ (1+γ) * c^(-2:ℤ) * Λ := hpt
    _ ≤ c ^ (-2 : ℤ) * Λ + ε' := hfin

/-! ## The extraction theorem and the upper-bound edge counts -/

/-- Fix `η > 0`; put `R = η S`.  For all sufficiently large `n`, every
  distinct-factor `k`-primitive `A ⊆ [n]` decomposes as `A = A_easy ⊔ A_hard`
  with `|A_easy| ≤ π(n) + 2R`, and every `a ∈ A_hard` has a set `T a` of
  `r = k+1` distinct prime divisors with `∏_{p ∈ T a} p ≤ a ≤ n` and
  `|T a ∩ T b| ≤ 1` for `a ≠ b`. -/
theorem extraction (k : ℕ) (hk : 2 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → DistPrimitive k A →
      ∃ (Aeasy Ahard : Finset ℕ) (T : ℕ → Finset ℕ),
        A = Aeasy ∪ Ahard ∧ Disjoint Aeasy Ahard ∧
        (Aeasy.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η * Sr k n) ∧
        (∀ a ∈ Ahard, (T a).card = k + 1 ∧
          (∀ p ∈ T a, p.Prime ∧ p ∣ a) ∧ (∏ p ∈ T a, p) ≤ a ∧ a ≤ n) ∧
        (∀ a ∈ Ahard, ∀ b ∈ Ahard, a ≠ b → ((T a) ∩ (T b)).card ≤ 1) := by
  filter_upwards [extraction_small_card_eventually k η hη,
    extraction_large_card k hk η hη] with n hsmall hlarge
  intro A hAsub hAprim
  by_cases hcard : A.card ≤ k
  · exact extraction_small_card k n η A hcard (by simpa [Sr] using hsmall)
  · exact hlarge A hAsub hAprim (by omega)

/-- The number of central edges is at most `(c^{-2} Λ_r + o(1)) S`. -/
theorem central_bound (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (Q : ℕ) (hQ : 1 ≤ Q) (δ : ℝ)
    (hmesh : (1 : ℝ) / 2 ^ Q ≤ (1 - c) * δ)
    (H : ℕ → Finset (Finset ℕ)) (hH : ∀ n, IsLinearPrimeHG (k + 1) n (H n))
    (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ n in atTop,
      ((centralEdges c Q δ (k + 1) n (H n)).card : ℝ) / Sr k n
        ≤ c ^ (-2 : ℤ) * Lam (k + 1) + ε' :=
  central_bound_core k hk c hc0 hc1 Q hQ δ hmesh H hH ε' hε'

/-- With `y = n^{1/(k+1)}`, every edge `E ∈ H` that is not central has a vertex
  `p ≤ δ y`. -/
theorem tail_edge_small_prime (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc0 : 0 < c)
    (Q : ℕ) (hQ : 1 ≤ Q) (δ : ℝ)
    (hcut : ((c : ℝ) / Q) ^ ((1 : ℝ) / (k : ℝ)) ≤ δ)
    (n : ℕ) (hn : 1 ≤ n) (H : Finset (Finset ℕ)) (hH : IsLinearPrimeHG (k + 1) n H)
    (E : Finset ℕ) (hE : E ∈ H \ centralEdges c Q δ (k + 1) n H) :
    ∃ p ∈ E, (p : ℝ) ≤ δ * (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) + 1)) := by
  have hkR : ((k:ℝ)+1) ≠ 0 := by positivity
  set y : ℝ := (n : ℝ) ^ ((1:ℝ)/((k:ℝ)+1)) with hy
  have hnR : (n:ℝ) > 0 := by exact_mod_cast hn
  have hy0 : 0 < y := Real.rpow_pos_of_pos hnR _
  have hyn : y ^ (k+1) = (n:ℝ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hnR)]
    push_cast
    rw [one_div_mul_cancel hkR, Real.rpow_one]
  rw [Finset.mem_sdiff] at hE
  obtain ⟨hEH, hEnc⟩ := hE
  obtain ⟨hcard, hprimes, hprod⟩ := hH.1 E hEH
  by_contra hcon
  push_neg at hcon
  have hall : ∀ p ∈ E, δ * y < (p:ℝ) := hcon
  have hnc : ¬ (∀ p ∈ E, δ * y < (p:ℝ) ∧ (p:ℝ) ≤ ((Q:ℝ)/c) * y) := by
    intro hcen
    apply hEnc
    rw [centralEdges, Finset.mem_filter]
    exact ⟨hEH, fun p hp => by simpa [hy] using hcen p hp⟩
  push_neg at hnc
  obtain ⟨p₀, hp₀E, hp₀⟩ := hnc
  have hp₀big : ((Q:ℝ)/c) * y < (p₀:ℝ) := hp₀ (hall p₀ hp₀E)
  set F := E.erase p₀ with hF
  have hFcard : F.card = k := by rw [hF, Finset.card_erase_of_mem hp₀E, hcard]; rfl
  have hFne : F.Nonempty := by rw [← Finset.card_pos, hFcard]; omega
  have hprodF : (p₀ : ℕ) * (∏ p ∈ F, p) = ∏ p ∈ E, p :=
    Finset.mul_prod_erase E (fun p => p) hp₀E
  have hp₀pos : 0 < (p₀:ℝ) := by
    have := (hprimes p₀ hp₀E).1; exact_mod_cast this.pos
  have hprodEle : ((∏ p ∈ E, p : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hprod
  have hprodFle : ((∏ p ∈ F, p : ℕ) : ℝ) ≤ (n:ℝ) / (p₀:ℝ) := by
    rw [le_div_iff₀ hp₀pos]
    have : ((p₀ * ∏ p ∈ F, p : ℕ):ℝ) ≤ (n:ℝ) := by rw [hprodF]; exact hprodEle
    push_cast at this ⊢; nlinarith [this]
  have hnp0 : (n:ℝ) / (p₀:ℝ) < (c/Q) * y ^ k := by
    have h1 : (n:ℝ) / (p₀:ℝ) < (n:ℝ) / (((Q:ℝ)/c) * y) :=
      div_lt_div_of_pos_left hnR (by positivity) hp₀big
    have h2 : (n:ℝ) / (((Q:ℝ)/c) * y) = (c/Q) * y ^ k := by
      rw [← hyn]; field_simp; ring
    rwa [h2] at h1
  set w := F.min' hFne with hw
  have hwF : w ∈ F := F.min'_mem hFne
  have hwmin : ∀ x ∈ F, w ≤ x := fun x hx => Finset.min'_le F x hx
  have hpow : w ^ k ≤ ∏ p ∈ F, p := by
    have := Finset.pow_card_le_prod F (fun x => x) w hwmin
    rwa [hFcard] at this
  have hpowR : (w:ℝ) ^ k ≤ ((∏ p ∈ F, p : ℕ):ℝ) := by exact_mod_cast hpow
  have hchain : (w:ℝ) ^ k < (c/Q) * y ^ k :=
    lt_of_le_of_lt hpowR (lt_of_le_of_lt hprodFle hnp0)
  set A := ((c:ℝ)/Q) ^ ((1:ℝ)/(k:ℝ)) with hA
  have hAnn : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hAk : A ^ k = c/Q := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [one_div_mul_cancel (by positivity : (k:ℝ) ≠ 0), Real.rpow_one]
  have hAy : (A * y) ^ k = (c/Q) * y ^ k := by rw [mul_pow, hAk]
  have hchain2 : (w:ℝ) ^ k < (A * y) ^ k := by rw [hAy]; exact hchain
  have hwlt : (w:ℝ) < A * y := lt_of_pow_lt_pow_left₀ k (by positivity) hchain2
  have hwlt2 : (w:ℝ) < δ * y := lt_of_lt_of_le hwlt (by nlinarith [hcut, hy0, hAnn])
  have : δ * y < (w:ℝ) := hall w (Finset.mem_of_mem_erase hwF)
  linarith

/--
Every tail edge contains a prime `p ≤ δ n^{1/(k+1)}`. -/
theorem tail_edge_card_le (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc0 : 0 < c)
    (Q : ℕ) (hQ : 1 ≤ Q) (δ : ℝ)
    (hcut : ((c : ℝ) / Q) ^ ((1 : ℝ) / (k : ℝ)) ≤ δ)
    (n : ℕ) (H : Finset (Finset ℕ)) (hH : IsLinearPrimeHG (k + 1) n H) :
    ((H \ centralEdges c Q δ (k + 1) n H).card : ℝ) ≤
      ∑ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) + 1))⌋₊ + 1)).filter Nat.Prime,
        (Nat.primeCounting ⌊((n : ℝ) / p) ^ ((1 : ℝ) / (((k : ℝ) + 1) - 1))⌋₊ : ℝ) := by
  classical
  set y : ℝ := (n : ℝ) ^ ((1:ℝ)/((k:ℝ)+1)) with hy
  set P := (Finset.range (⌊δ * y⌋₊ + 1)).filter Nat.Prime with hP
  set M : ℕ → ℕ := fun p => ⌊((n : ℝ) / p) ^ ((1 : ℝ) / (((k : ℝ) + 1) - 1))⌋₊ with hM
  set T := H \ centralEdges c Q δ (k + 1) n H with hT
  have key : ∀ E ∈ T, ∃ p q : ℕ, p ∈ E ∧ q ∈ E ∧ p ≠ q ∧ p ∈ P ∧ q ∈ primesLE (M p) := by
    intro E hET
    have hEH : E ∈ H := (Finset.mem_sdiff.mp hET).1
    obtain ⟨hcard, hprimes, hprod⟩ := hH.1 E hEH
    have hEne : E.Nonempty := by rw [← Finset.card_pos, hcard]; omega
    set pE := sInf (E : Set ℕ) with hpE'
    have hpE : pE ∈ E := Finset.mem_coe.mp (Nat.sInf_mem (Finset.coe_nonempty.mpr hEne))
    have hple : ∀ x ∈ E, pE ≤ x := fun x hx => Nat.sInf_le (Finset.mem_coe.mpr hx)
    have hpprime : pE.Prime := (hprimes _ hpE).1
    have hpn : pE ≤ n := (hprimes _ hpE).2
    have hn1 : 1 ≤ n := le_trans hpprime.one_lt.le hpn
    have hEene : (E.erase pE).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hpE, hcard]; omega
    set qE := sInf ((E.erase pE) : Set ℕ) with hqE'
    have hqEe : qE ∈ E.erase pE := Finset.mem_coe.mp (Nat.sInf_mem (Finset.coe_nonempty.mpr hEene))
    have hqle : ∀ x ∈ E.erase pE, qE ≤ x := fun x hx => Nat.sInf_le (Finset.mem_coe.mpr hx)
    have hqmem : qE ∈ E := Finset.mem_of_mem_erase hqEe
    have hne : pE ≠ qE := fun h => (Finset.ne_of_mem_erase hqEe) h.symm
    have hqprime : qE.Prime := (hprimes _ hqmem).1
    obtain ⟨p', hp'E, hp'le⟩ := tail_edge_small_prime k hk c hc0 Q hQ δ hcut n hn1 H hH E hET
    have hpREle : (pE : ℝ) ≤ δ * y := by
      have h1 : (pE : ℝ) ≤ (p' : ℝ) := by exact_mod_cast hple p' hp'E
      exact le_trans h1 (by simpa [hy] using hp'le)
    have hp_in_P : pE ∈ P := by
      rw [hP, Finset.mem_filter]
      have hfl : pE ≤ ⌊δ * y⌋₊ := Nat.le_floor hpREle
      exact ⟨Finset.mem_range.mpr (by omega), hpprime⟩
    have hppos : 0 < pE := hpprime.pos
    have hpposR : 0 < (pE:ℝ) := by exact_mod_cast hppos
    have hprodq : qE ^ k ≤ ∏ x ∈ E.erase pE, x := by
      have := Finset.pow_card_le_prod (E.erase pE) (fun x => x) qE hqle
      rwa [Finset.card_erase_of_mem hpE, hcard, Nat.add_sub_cancel] at this
    have hprodsplit : pE * (∏ x ∈ E.erase pE, x) = ∏ x ∈ E, x :=
      Finset.mul_prod_erase E (fun x => x) hpE
    have hpq : pE * qE ^ k ≤ n :=
      calc pE * qE ^ k ≤ pE * (∏ x ∈ E.erase pE, x) := Nat.mul_le_mul_left _ hprodq
        _ = ∏ x ∈ E, x := hprodsplit
        _ ≤ n := hprod
    have hqkR : (qE:ℝ) ^ k ≤ (n:ℝ) / (pE:ℝ) := by
      rw [le_div_iff₀ hpposR]
      have : ((pE * qE ^ k : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hpq
      push_cast at this ⊢; nlinarith [this]
    have hqleM : qE ≤ M pE := by
      rw [hM]; apply Nat.le_floor
      rw [show (((k:ℝ)+1) - 1) = (k:ℝ) by ring]
      have h1 : (qE : ℝ) = ((qE:ℝ) ^ k) ^ ((1:ℝ)/(k:ℝ)) := by
        rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]
      rw [h1]; exact Real.rpow_le_rpow (by positivity) hqkR (by positivity)
    have hq_in : qE ∈ primesLE (M pE) := by
      rw [primesLE, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr (by omega), hqprime⟩
    exact ⟨pE, qE, hpE, hqmem, hne, hp_in_P, hq_in⟩
  choose! p q hpE hqE hpne hpP hqP using key
  set S := P.biUnion (fun p0 => (primesLE (M p0)).image (fun q0 => (p0, q0))) with hS
  set f : Finset ℕ → ℕ × ℕ := fun E => (p E, q E) with hf
  have hmapsto : ∀ E ∈ T, f E ∈ S := by
    intro E hET
    rw [hS, Finset.mem_biUnion]
    exact ⟨p E, hpP E hET, Finset.mem_image.mpr ⟨q E, hqP E hET, rfl⟩⟩
  have hinj : Set.InjOn f T := by
    intro E hE F hF hEF
    simp only [hf, Prod.mk.injEq] at hEF
    obtain ⟨h1, h2⟩ := hEF
    by_contra hEFne
    have hEH : E ∈ H := (Finset.mem_sdiff.mp hE).1
    have hFH : F ∈ H := (Finset.mem_sdiff.mp hF).1
    have hcap : (E ∩ F).card ≤ 1 := hH.2 E hEH F hFH hEFne
    have hpin : p E ∈ E ∩ F := Finset.mem_inter.mpr ⟨hpE E hE, h1 ▸ hpE F hF⟩
    have hqin : q E ∈ E ∩ F := Finset.mem_inter.mpr ⟨hqE E hE, h2 ▸ hqE F hF⟩
    have : 1 < (E ∩ F).card := Finset.one_lt_card.mpr ⟨p E, hpin, q E, hqin, hpne E hE⟩
    omega
  have hcard_le : T.card ≤ S.card := Finset.card_le_card_of_injOn f hmapsto hinj
  have hScard : S.card = ∑ p0 ∈ P, Nat.primeCounting (M p0) := by
    rw [hS, Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun p0 hp0 => ?_)
      rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.injEq _ _ _ _ |>.mp hab).2)]
      exact (primeCounting_eq_card (M p0)).symm
    · intro x hx z hz hxz
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      rintro w hw1 hw2
      rw [Finset.mem_image] at hw1 hw2
      obtain ⟨a, ha, rfl⟩ := hw1
      obtain ⟨b, hb, hbeq⟩ := hw2
      rw [Prod.mk.injEq] at hbeq
      exact hxz hbeq.1.symm
  rw [hScard] at hcard_le
  calc ((T.card : ℝ)) ≤ ((∑ p0 ∈ P, Nat.primeCounting (M p0) : ℕ) : ℝ) := by exact_mod_cast hcard_le
    _ = ∑ p0 ∈ P, (Nat.primeCounting (M p0) : ℝ) := by push_cast; rfl

/-- With the additional cutoff condition `(c/Q)^{1/(r-1)} ≤ δ`, the number of
  tail edges is at most `(C_r δ^{(r-2)/(r-1)} + o(1)) S`, where `C_r` is the
  constant from `prime_pair_tail`. -/
theorem tail_edge_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ (c : ℝ), 0 < c → c < 1 → ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (δ : ℝ), 0 < δ → δ < 1 → (1 : ℝ) / 2 ^ Q ≤ (1 - c) * δ →
      ((c : ℝ) / Q) ^ ((1 : ℝ) / (k : ℝ)) ≤ δ →
      ∀ (H : ℕ → Finset (Finset ℕ)), (∀ n, IsLinearPrimeHG (k + 1) n (H n)) →
      ∀ᶠ n in atTop,
        (((H n) \ centralEdges c Q δ (k + 1) n (H n)).card : ℝ) / Sr k n
          ≤ Cr * δ ^ (((k : ℝ) - 1) / (k : ℝ)) := by
  obtain ⟨Cr, hCr0, hCr⟩ := prime_pair_tail (k + 1) (by omega)
  refine ⟨Cr, hCr0, ?_⟩
  intro c hc0 hc1 Q hQ δ hδ0 hδ1 hmesh hcut H hH
  have hev := hCr δ hδ0 hδ1
  simp only [Nat.cast_add, Nat.cast_one] at hev
  have hSrEq : ∀ n : ℕ, Sr k n = ((n:ℝ)^((1:ℝ)/((k:ℝ)+1))/Real.log n)^2 := by
    intro n
    rw [Sr, div_pow, ← Real.rpow_natCast ((n:ℝ)^((1:ℝ)/((k:ℝ)+1))) 2, ← Real.rpow_mul (by positivity)]
    norm_num; ring_nf
  have hexp : (((k:ℝ)+1) - 2)/(((k:ℝ)+1) - 1) = ((k:ℝ)-1)/(k:ℝ) := by
    rw [show ((k:ℝ)+1) - 1 = (k:ℝ) by ring, show ((k:ℝ)+1) - 2 = (k:ℝ)-1 by ring]
  filter_upwards [hev, Filter.eventually_gt_atTop 1] with n hn hn'
  have htail := tail_edge_card_le k hk c hc0 Q hQ δ hcut n (H n) (hH n)
  rw [hSrEq n]
  rw [hexp] at hn
  have hS'pos : 0 < ((n:ℝ)^((1:ℝ)/((k:ℝ)+1))/Real.log n)^2 :=
    sq_pos_of_pos (div_pos (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _)
      (Real.log_pos (by exact_mod_cast hn')))
  calc (((H n) \ centralEdges c Q δ (k + 1) n (H n)).card : ℝ) / ((n:ℝ)^((1:ℝ)/((k:ℝ)+1))/Real.log n)^2
      ≤ (∑ p ∈ (Finset.range (⌊δ * (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) + 1))⌋₊ + 1)).filter Nat.Prime,
          (Nat.primeCounting ⌊((n : ℝ) / p) ^ ((1 : ℝ) / (((k : ℝ) + 1) - 1))⌋₊ : ℝ))
          / ((n:ℝ)^((1:ℝ)/((k:ℝ)+1))/Real.log n)^2 := by gcongr
    _ ≤ Cr * δ ^ (((k : ℝ) - 1) / (k : ℝ)) := hn

/-! ## Realization of dyadic packings -/

/-- The `j`th prime bin used in the finite realization argument.  It consists
of the primes in `(j d_Q n^(1/r), (j+1)d_Q n^(1/r)]`. -/
noncomputable def realizationBin (r Q n : ℕ) (j : Fin (NQ Q)) : Finset ℕ :=
  primesLE ⌊(((j : ℕ) : ℝ) + 1) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ \
    primesLE ⌊((j : ℕ) : ℝ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊

/-- Every member of a realization bin is prime. -/
lemma realizationBin_prime {r Q n : ℕ} {j : Fin (NQ Q)} {p : ℕ}
    (hp : p ∈ realizationBin r Q n j) : p.Prime := by
  unfold realizationBin at hp
  have hp' := (Finset.mem_sdiff.mp hp).1
  exact (Finset.mem_filter.mp hp').2

/-- A prime in the `j`th realization bin satisfies its defining real upper bound. -/
lemma realizationBin_le_scale {r Q n : ℕ} {j : Fin (NQ Q)} {p : ℕ}
    (hp : p ∈ realizationBin r Q n j) :
    (p : ℝ) ≤ (((j : ℕ) : ℝ) + 1) * dQ Q *
      (n : ℝ) ^ ((1 : ℝ) / r) := by
  unfold realizationBin at hp
  rw [Finset.mem_sdiff] at hp
  unfold primesLE at hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  have hle : p ≤ ⌊(((j : ℕ) : ℝ) + 1) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ :=
    Nat.lt_add_one_iff.mp hp.1.1
  have hnonneg : 0 ≤ (((j : ℕ) : ℝ) + 1) * dQ Q *
      (n : ℝ) ^ ((1 : ℝ) / r) := by
    exact mul_nonneg (mul_nonneg (by positivity) (by unfold dQ; positivity))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact le_trans (Nat.cast_le.mpr hle) (Nat.floor_le hnonneg)

/-- The finite union of all realization bins. -/
noncomputable def realizationVertices (r Q n : ℕ) : Finset ℕ :=
  Finset.univ.biUnion (realizationBin r Q n)

/-- Every realization vertex is prime. -/
lemma realizationVertices_prime {r Q n p : ℕ}
    (hp : p ∈ realizationVertices r Q n) : p.Prime := by
  simp only [realizationVertices, Finset.mem_biUnion] at hp
  obtain ⟨j, hj⟩ := hp
  exact realizationBin_prime hj.2

/-- Every realization vertex lies below the global cutoff `Q n^(1/r)`. -/
lemma realizationVertices_le_scale {r Q n p : ℕ}
    (hp : p ∈ realizationVertices r Q n) :
    (p : ℝ) ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r) := by
  simp only [realizationVertices] at hp
  obtain ⟨j, hj⟩ := Finset.mem_biUnion.mp hp
  have hj' := hj.2
  have h1 := realizationBin_le_scale hj'
  have h2 : (((j : ℕ) : ℝ) + 1) ≤ (Q : ℝ) * 2 ^ Q := by
    have hjlt : (j : ℕ) < NQ Q := j.2
    simp only [NQ] at hjlt
    norm_cast
  have hdQ : dQ Q = 1 / 2 ^ Q := by simp [dQ]
  have hdQpos : 0 ≤ dQ Q := by simp [dQ]
  have hscale : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / r) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hmul : (((j : ℕ) : ℝ) + 1) * dQ Q ≤ (Q : ℝ) := by
    rw [hdQ]
    have h2' : (((j : ℕ) : ℝ) + 1) ≤ (Q : ℝ) * 2 ^ Q := by exact_mod_cast h2
    rw [mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ Q)]
    simp [h2']
  calc (p : ℝ) ≤ (((j : ℕ) : ℝ) + 1) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r) := h1
    _ ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r) := by gcongr

/-- Every vertex of a family of realization-vertex edges obeys the global cutoff. -/
lemma realization_family_vertex_bound {r Q n : ℕ} {H : Finset (Finset ℕ)}
    (hsub : ∀ E ∈ H, E ⊆ realizationVertices r Q n) :
    ∀ p ∈ vertices H, (p : ℝ) ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r) := by
  intro p hp
  simp only [vertices] at hp
  obtain ⟨E, hE, hEp⟩ := Finset.mem_biUnion.mp hp
  exact realizationVertices_le_scale (hsub E hE hEp)

/-- Exact cardinality of a realization prime bin. -/
lemma card_realizationBin (r Q n : ℕ) (j : Fin (NQ Q)) :
    ((realizationBin r Q n j).card : ℝ) =
      primesIn (((j : ℕ) : ℝ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r))
        ((((j : ℕ) : ℝ) + 1) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)) := by
  unfold realizationBin primesIn
  -- Let l and m be the floor values
  set l := ⌊((j : ℕ) : ℝ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊
  set m := ⌊(((j : ℕ) : ℝ) + 1) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊
  -- First show l ≤ m
  have hlm : l ≤ m := by
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_right
    apply mul_le_mul_of_nonneg_right
    · simp
    · simp only [dQ]
      positivity
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  -- Show the cardinality equals primeCounting m - primeCounting l
  have hsub : primesLE l ⊆ primesLE m := by
    intro x hx
    simp [primesLE] at hx ⊢
    exact ⟨by omega, hx.2⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hge := Finset.card_mono hsub
  simp [primeCounting_eq_card] at hcard hge ⊢
  have heq : (primesLE m \ primesLE l).card = (primesLE m).card - (primesLE l).card := by omega
  rw [heq, Nat.cast_sub hge]

/-- Distinct realization bins are disjoint. -/
lemma realizationBin_disjoint (r Q n : ℕ) (i j : Fin (NQ Q)) (hij : i ≠ j) :
    Disjoint (realizationBin r Q n i) (realizationBin r Q n j) := by
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · rw [Finset.disjoint_left]
    intro p hpi hpj
    unfold realizationBin at hpi hpj
    rw [Finset.mem_sdiff] at hpi hpj
    apply hpj.2
    unfold primesLE at *
    simp only [Finset.mem_filter, Finset.mem_range] at *
    refine ⟨?_, hpi.1.2⟩
    have hcoef : (((i : ℕ) : ℝ) + 1) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hijlt
    have hscale : 0 ≤ dQ Q * (n : ℝ) ^ ((1 : ℝ) / r) :=
      mul_nonneg (by unfold dQ; positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hflo : ⌊(((i : ℕ) : ℝ) + 1) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ ≤
        ⌊((j : ℕ) : ℝ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ := by
      apply Nat.floor_mono
      nlinarith
    omega
  · rw [Finset.disjoint_left]
    intro p hpi hpj
    unfold realizationBin at hpi hpj
    rw [Finset.mem_sdiff] at hpi hpj
    apply hpi.2
    unfold primesLE at *
    simp only [Finset.mem_filter, Finset.mem_range] at *
    refine ⟨?_, hpj.1.2⟩
    have hcoef : (((j : ℕ) : ℝ) + 1) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hjilt
    have hscale : 0 ≤ dQ Q * (n : ℝ) ^ ((1 : ℝ) / r) :=
      mul_nonneg (by unfold dQ; positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hflo : ⌊(((j : ℕ) : ℝ) + 1) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ ≤
        ⌊((i : ℕ) : ℝ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)⌋₊ := by
      apply Nat.floor_mono
      nlinarith
    omega

/-- Each fixed realization bin has the prime-number-theorem asymptotic
required below: its cardinality divided by `n^(1/r)/log n` tends to `r d_Q`. -/
lemma realizationBin_card_tendsto (r Q : ℕ) (hr : 2 ≤ r) (j : Fin (NQ Q)) :
    Tendsto (fun n : ℕ => ((realizationBin r Q n j).card : ℝ) /
      ((n : ℝ) ^ ((1 : ℝ) / r) / Real.log n)) atTop
      (nhds ((r : ℝ) * dQ Q)) := by
  simp_rw [card_realizationBin]
  have hdQ_pos : 0 < dQ Q := by unfold dQ; positivity
  convert prime_bin r hr (j * dQ Q) ((j + 1) * dQ Q) _ _ using 2
  · ring
  · positivity
  · nlinarith

/-- The family of subsets `E` of the disjoint bins `(P j)_{j ∈ J}` with
`|E ∩ P j| = τ j` for every `j ∈ J`. -/
noncomputable def setsOfType {α : Type*} [DecidableEq α] (P : ℕ → Finset α)
    (J : Finset ℕ) (τ : ℕ → ℕ) : Finset (Finset α) :=
  (J.biUnion P).powerset.filter (fun E => ∀ j ∈ J, (E ∩ P j).card = τ j)

/-- The number of type-`τ` sets is `∏_j C(N_j, τ_j)`. -/
theorem card_setsOfType {α : Type*} [DecidableEq α] (P : ℕ → Finset α) (J : Finset ℕ)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (P i) (P j)) (τ : ℕ → ℕ) :
    (setsOfType P J τ).card = ∏ j ∈ J, ((P j).card).choose (τ j) := by
  induction' J using Finset.induction with a J' ha ih generalizing τ;
  · unfold setsOfType; aesop;
  · -- By definition of `setsOfType`, we can write
    have h_def : setsOfType P (insert a J') τ = Finset.biUnion (Finset.powersetCard (τ a) (P a)) (fun S => Finset.image (fun T => S ∪ T) (setsOfType P J' (fun j => τ j))) := by
      ext E;
      constructor;
      · simp +decide [ setsOfType ];
        intro x hx y hy hxy hE hE';
        refine' ⟨ x, ⟨ hx, _ ⟩, y, ⟨ hy, _ ⟩, hxy ⟩;
        · rw [ ← hE, ← hxy, Finset.union_inter_distrib_right ];
          rw [ Finset.inter_eq_left.mpr hx, Finset.union_eq_left.mpr ];
          intro z hz; specialize hy; have := hy ( Finset.mem_of_mem_inter_left hz ) ; simp_all +decide [ Finset.disjoint_left ] ;
          grind;
        · intro j hj;
          convert hE' j hj using 2;
          ext z; simp +decide [ ← hxy ] ;
          exact fun hz hxz => False.elim ( Finset.disjoint_left.mp ( hdisj _ ( Finset.mem_insert_self _ _ ) _ ( Finset.mem_insert_of_mem hj ) ( by aesop ) ) ( hx hxz ) hz );
      · simp +decide [ setsOfType ];
        rintro x hx hx' y hy hy' rfl;
        refine' ⟨ ⟨ x, hx, y, hy, rfl ⟩, _, _ ⟩;
        · convert hx' using 2;
          ext z; simp +decide [ Finset.subset_iff ] at *;
          by_cases hz : z ∈ x <;> simp_all +decide [ Finset.disjoint_left ];
          grind;
        · intro j hj; rw [ ← hy' j hj ] ; rw [ Finset.union_inter_distrib_right ] ;
          rw [ Finset.union_eq_right.mpr ];
          intro z hz; specialize hdisj a ( Finset.mem_insert_self _ _ ) j ( Finset.mem_insert_of_mem hj ) ; simp_all +decide [ Finset.disjoint_left ] ;
          exact False.elim ( hdisj ( by rintro rfl; exact ha hj ) ( hx hz.1 ) hz.2 );
    rw [ h_def, Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl fun x hx => Finset.card_image_of_injOn ?_ ];
      · rw [ Finset.prod_insert ha, ih fun i hi j hj hij => hdisj i ( Finset.mem_insert_of_mem hi ) j ( Finset.mem_insert_of_mem hj ) hij ] ; simp +decide [ Finset.card_powersetCard ];
      · intro T hT T' hT' h_eq; simp_all +decide [ Finset.ext_iff ] ;
        intro y; specialize h_eq y; simp_all +decide [ Finset.subset_iff  ] ;
        by_cases hy : y ∈ x <;> simp_all +decide [ Finset.disjoint_left ];
        grind +locals;
    · intro S hS T hT hST; simp_all +decide [ Finset.disjoint_left ] ;
      intro x hx y hy; contrapose! hST; simp_all +decide [ Finset.ext_iff ] ;
      grind +locals

/-- The number of type-`τ` sets containing a fixed `W ⊆ ⋃_j P j`, with
  `σ j = |W ∩ P j| ≤ τ j`, is `∏_j C(N_j - σ_j, τ_j - σ_j)`. -/
theorem general_completion {α : Type*} [DecidableEq α] (P : ℕ → Finset α) (J : Finset ℕ)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (P i) (P j)) (τ : ℕ → ℕ)
    (W : Finset α) (hW : W ⊆ J.biUnion P) (hcompat : ∀ j ∈ J, (W ∩ P j).card ≤ τ j) :
    ((setsOfType P J τ).filter (fun E => W ⊆ E)).card
      = ∏ j ∈ J, ((P j).card - (W ∩ P j).card).choose (τ j - (W ∩ P j).card) := by
  -- Define the function that maps each set in the filter to its intersection with the bins
  set Q := fun j => P j \ (W ∩ P j)
  set τ' := fun j => τ j - (W ∩ P j).card;
  convert card_setsOfType Q J ( fun i hi j hj hij => ?_ ) τ' using 1;
  · refine' Finset.card_bij ( fun E hE => E \ W ) _ _ _;
    · simp +contextual [ setsOfType ];
      intro a ha hτ hW; simp_all +decide [ Finset.subset_iff  ] ;
      refine' ⟨ fun x hx hx' => _, fun j hj => _ ⟩;
      · grind +revert;
      · rw [ show a \ W ∩ Q j = ( a ∩ P j ) \ ( W ∩ P j ) from ?_, Finset.card_sdiff ];
        · rw [ show W ∩ P j ∩ ( a ∩ P j ) = W ∩ P j from by ext x; aesop ] ; aesop;
        · grind;
    · simp +contextual [ Finset.ext_iff ];
      grind;
    · intro b hb;
      refine' ⟨ b ∪ W, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, setsOfType ];
      · refine' ⟨ _, _ ⟩;
        · grind;
        · intro j hj; specialize hb; have := hb.2 j hj; simp_all +decide [ Finset.inter_comm   ] ;
          rw [ show P j ∩ ( b ∪ W ) = ( b ∩ Q j ) ∪ ( W ∩ P j ) from ?_, Finset.card_union_of_disjoint ];
          · rw [ hb.2 j hj, Nat.sub_add_cancel ( hcompat j hj ) ];
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp ( Finset.mem_inter.mp hx₁ |>.2 ) |>.2 hx₂;
          · grind;
      · simp +decide [ Finset.ext_iff, setsOfType ] at hb ⊢;
        grind;
  · grind;
  · exact Disjoint.mono ( Finset.sdiff_subset ) ( Finset.sdiff_subset ) ( hdisj i hi j hj hij )

/-- The scale `S = (n^{1/r} / log n)²`. -/
noncomputable def Sval (r n : ℕ) : ℝ := ((n : ℝ) ^ ((1 : ℝ) / r) / Real.log n) ^ 2

/--
The realization scale agrees with the main-theorem scale when `r = k+1`.
-/
theorem Sval_succ_eq_Sr (k n : ℕ) : Sval (k + 1) n = Sr k n := by
  unfold Sval Sr; ring_nf;
  rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ; ring

/-- The family of all prime sets having the prescribed realization-bin type. -/
noncomputable def realizationTypeFamily (r Q n : ℕ) (τ : Fin (NQ Q) → ℕ) :
    Finset (Finset ℕ) :=
  setsOfType
    (fun j : ℕ => if hj : j < NQ Q then realizationBin r Q n ⟨j, hj⟩ else ∅)
    (Finset.range (NQ Q))
    (fun j => if hj : j < NQ Q then τ ⟨j, hj⟩ else 0)

/-- The exact number of prime sets of a prescribed realization-bin type. -/
lemma card_realizationTypeFamily (r Q n : ℕ) (τ : Fin (NQ Q) → ℕ) :
    (realizationTypeFamily r Q n τ).card =
      ∏ j : Fin (NQ Q), (realizationBin r Q n j).card.choose (τ j) := by
  unfold realizationTypeFamily
  rw [card_setsOfType]
  · rw [Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  · intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    simp [hi, hj, realizationBin_disjoint r Q n ⟨i, hi⟩ ⟨j, hj⟩ (ne_of_apply_ne Fin.val hij)]

/-- Exact completion count inside a realization type.  This is the
realization-bin specialization of `general_completion`; in particular, taking
`W` to have two elements gives the pair-completion count used to control
codegrees in the probabilistic construction. -/
lemma realizationTypeFamily_completion (r Q n : ℕ) (τ : Fin (NQ Q) → ℕ)
    (W : Finset ℕ) (hW : W ⊆ realizationVertices r Q n)
    (hcompat : ∀ j : Fin (NQ Q), (W ∩ realizationBin r Q n j).card ≤ τ j) :
    ((realizationTypeFamily r Q n τ).filter (fun E => W ⊆ E)).card =
      ∏ j : Fin (NQ Q),
        ((realizationBin r Q n j).card - (W ∩ realizationBin r Q n j).card).choose
          (τ j - (W ∩ realizationBin r Q n j).card) := by
  -- Set up the parameters for general_completion
  let P : ℕ → Finset ℕ := fun j => if hj : j < NQ Q then realizationBin r Q n ⟨j, hj⟩ else ∅
  let J : Finset ℕ := Finset.range (NQ Q)
  let τ' : ℕ → ℕ := fun j => if hj : j < NQ Q then τ ⟨j, hj⟩ else 0
  -- Unfold realizationTypeFamily to match setsOfType P J τ'
  unfold realizationTypeFamily
  -- Apply general_completion
  have hP_disj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (P i) (P j) := by
    intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    have hi' : P i = realizationBin r Q n ⟨i, hi⟩ := by simp [P, hi]
    have hj' : P j = realizationBin r Q n ⟨j, hj⟩ := by simp [P, hj]
    rw [hi', hj']
    exact realizationBin_disjoint r Q n ⟨i, hi⟩ ⟨j, hj⟩ (ne_of_apply_ne Fin.val hij)
  have hW_sub : W ⊆ J.biUnion P := by
    intro w hw
    have hw' := hW hw
    simp only [realizationVertices] at hw'
    rw [Finset.mem_biUnion] at hw'
    simp only [Finset.mem_univ, true_and] at hw'
    obtain ⟨j, hj⟩ := hw'
    have hj' : j.val ∈ J := Finset.mem_range.mpr j.2
    have hwj : w ∈ P j.val := by simp [P, hj]
    exact Finset.mem_biUnion.mpr ⟨j.val, hj', hwj⟩
  have hcompat : ∀ j ∈ J, (W ∩ P j).card ≤ τ' j := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp [τ', P, hj]
    exact hcompat ⟨j, hj⟩
  rw [general_completion P J hP_disj τ' W hW_sub hcompat]
  -- Now convert the product from Finset.range to Fin (NQ Q)
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [i.2, P, τ']

/-- Exact incidence ratio for completions of a compatible fixed set.  After
multiplying by the number of ways to choose the binwise profile of `W`, the
completion count is the full type-family count multiplied by the corresponding
binwise profile count inside an edge.  The pair case is the sharp counting
identity used in the realization selection estimates. -/
lemma realizationTypeFamily_completion_mul_profile
    (r Q n : ℕ) (τ : Fin (NQ Q) → ℕ) (W : Finset ℕ)
    (hW : W ⊆ realizationVertices r Q n)
    (hcompat : ∀ j : Fin (NQ Q),
      (W ∩ realizationBin r Q n j).card ≤ τ j) :
    ((realizationTypeFamily r Q n τ).filter (fun E => W ⊆ E)).card *
        (∏ j : Fin (NQ Q),
          (realizationBin r Q n j).card.choose
            (W ∩ realizationBin r Q n j).card) =
      (realizationTypeFamily r Q n τ).card *
        (∏ j : Fin (NQ Q), (τ j).choose
          (W ∩ realizationBin r Q n j).card) := by
  rw [realizationTypeFamily_completion r Q n τ W hW hcompat,
    card_realizationTypeFamily]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  symm
  simpa [mul_comm] using
    (Nat.choose_mul (n := (realizationBin r Q n j).card)
      (k := τ j) (s := (W ∩ realizationBin r Q n j).card) (hcompat j))

/-- Every set of an admissible realization type has exactly `r` vertices. -/
lemma realizationTypeFamily_card {r Q n : ℕ} {τ : Fin (NQ Q) → ℕ}
    (hτ : τ ∈ admTypes r Q) {E : Finset ℕ}
    (hE : E ∈ realizationTypeFamily r Q n τ) : E.card = r := by
  -- E is in realizationTypeFamily, so it's a member of setsOfType for some P, J, τ'
  unfold realizationTypeFamily at hE
  -- τ ∈ admTypes means τ ∈ types, which means ∑ j, τ j = r
  have hsum : ∑ j : Fin (NQ Q), τ j = r := by
    simp only [admTypes, types, Finset.mem_filter] at hτ
    exact hτ.1.2
  -- Unfold setsOfType to extract properties of E
  unfold setsOfType at hE
  have hE_prop := Finset.mem_filter.mp hE
  have hE_sub : E ⊆ (Finset.range (NQ Q)).biUnion (fun j : ℕ => if hj : j < NQ Q then realizationBin r Q n ⟨j, hj⟩ else ∅) :=
    Finset.mem_powerset.mp hE_prop.1
  have hE_type : ∀ j ∈ Finset.range (NQ Q), (E ∩ (if hj : j < NQ Q then realizationBin r Q n ⟨j, hj⟩ else ∅)).card = (if hj : j < NQ Q then τ ⟨j, hj⟩ else 0) :=
    hE_prop.2
  -- For j in range (NQ Q), simplify the if-then-else
  have hE_type_simp : ∀ j (hj : j ∈ Finset.range (NQ Q)), (E ∩ realizationBin r Q n ⟨j, Finset.mem_range.mp hj⟩).card = τ ⟨j, Finset.mem_range.mp hj⟩ := by
    intro j hj
    have := hE_type j hj
    simp [Finset.mem_range] at hj ⊢
    simp [hj] at this
    exact this
  -- E ⊆ ⋃ bin_j, and bins are disjoint, so E.card = ∑ (E ∩ bin_j).card
  set P := fun j : ℕ => if hj : j < NQ Q then realizationBin r Q n ⟨j, hj⟩ else ∅ with hP_def
  have hE_eq : E = Finset.biUnion (Finset.range (NQ Q)) (fun j => E ∩ P j) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hx
      have hxsub := hE_sub hx
      simp only [Finset.mem_biUnion] at hxsub
      obtain ⟨j, hj, hxj⟩ := hxsub
      exact ⟨j, hj, hx, hxj⟩
    · rintro ⟨j, hj, hx, _⟩
      exact hx
  -- The sets (E ∩ P j) are pairwise disjoint because the bins P j are disjoint
  have hdisj : ∀ i ∈ Finset.range (NQ Q), ∀ j ∈ Finset.range (NQ Q), i ≠ j →
      Disjoint (E ∩ P i) (E ∩ P j) := by
    intro i hi j hj hij
    simp only [Finset.disjoint_left, Finset.mem_inter]
    intro x ⟨_, hxi⟩ ⟨_, hxj⟩
    -- x ∈ P i and x ∈ P j, but P i and P j are disjoint for i ≠ j
    have hi' : i < NQ Q := Finset.mem_range.mp hi
    have hj' : j < NQ Q := Finset.mem_range.mp hj
    have hxi' : x ∈ realizationBin r Q n ⟨i, hi'⟩ := by
      simp only [hP_def] at hxi
      simp [hi'] at hxi
      exact hxi
    have hxj' : x ∈ realizationBin r Q n ⟨j, hj'⟩ := by
      simp only [hP_def] at hxj
      simp [hj'] at hxj
      exact hxj
    exact Finset.disjoint_left.mp (realizationBin_disjoint r Q n ⟨i, hi'⟩ ⟨j, hj'⟩ (by simpa)) hxi' hxj'
  -- Now compute E.card
  rw [hE_eq]
  rw [Finset.card_biUnion fun i hi j hj hij => hdisj i hi j hj hij]
  -- Simplify each term to τ and convert to sum over Fin
  have heq_sum : ∑ i ∈ Finset.range (NQ Q), (E ∩ P i).card = ∑ j : Fin (NQ Q), τ j := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have := hE_type_simp j.val (Finset.mem_range.mpr j.2)
    simp only [hP_def]
    simp [j.2] at this ⊢
    exact this
  rw [heq_sum, hsum]

/-- Every set of an admissible realization type has product at most `n`.
This is the deterministic product bound needed when the probabilistic construction
selects edges from the typed realization families. -/
lemma realizationTypeFamily_product_le {r Q n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    {τ : Fin (NQ Q) → ℕ} (hτ : τ ∈ admTypes r Q) {E : Finset ℕ}
    (hE : E ∈ realizationTypeFamily r Q n τ) :
    (∏ p ∈ E, p) ≤ n := by
  -- τ is admissible
  rw [admTypes] at hτ
  have hadm := Finset.mem_filter.mp hτ |>.2
  -- E ⊆ realizationVertices
  have hsub : E ⊆ realizationVertices r Q n := by
    rw [realizationTypeFamily] at hE
    unfold setsOfType at hE
    have h := Finset.mem_powerset.mp (Finset.mem_filter.mp hE).1
    apply h.trans
    rw [realizationVertices]
    refine Finset.subset_iff.mpr ?_
    intro x hx
    simp only [Finset.mem_biUnion] at hx ⊢
    obtain ⟨j, hj, hxj⟩ := hx
    simp only [Finset.mem_range] at hj
    use ⟨j, hj⟩
    simp_all
  -- Define the bins P and J
  set P : ℕ → Finset ℕ := fun j => if hj : j < NQ Q then realizationBin r Q n ⟨j, hj⟩ else ∅
  set J : Finset ℕ := Finset.range (NQ Q)
  -- P i are pairwise disjoint
  have hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (P i) (P j) := by
    intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    simp only [P]
    simp [hi, hj, realizationBin_disjoint r Q n ⟨i, hi⟩ ⟨j, hj⟩ (ne_of_apply_ne Fin.val hij)]
  -- E ∩ P j has cardinality τ j for each j ∈ J
  have hE_card : ∀ j hj, j ∈ J → (E ∩ P j).card = τ ⟨j, hj⟩ := by
    intro j hj hjin
    rw [Finset.mem_range] at hjin
    unfold realizationTypeFamily setsOfType at hE
    have hjin' : j ∈ Finset.range (NQ Q) := Finset.mem_range.mpr hjin
    have hcond := (Finset.mem_filter.mp hE).2 j hjin'
    convert hcond using 1
    simp [hjin]
  -- E is a subset of the union of bins
  have hE_sub_union : E ⊆ J.biUnion P := by
    rw [realizationTypeFamily] at hE
    unfold setsOfType at hE
    have h := Finset.mem_powerset.mp (Finset.mem_filter.mp hE).1
    exact h
  -- The product over E factors through the bins
  have hprod_le : (∏ p ∈ E, (p : ℝ)) ≤
      ∏ j : Fin (NQ Q), (((j.val + 1) : ℕ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)) ^ (τ j) := by
    -- Factor E as a disjoint union over bins
    have hE_disj_union : E = Finset.biUnion Finset.univ (fun j => E ∩ realizationBin r Q n j) := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · intro hp
        have hp_mem := hsub hp
        simp only [realizationVertices] at hp_mem
        rw [Finset.mem_biUnion] at hp_mem
        obtain ⟨j, _, hj⟩ := hp_mem
        exact ⟨j, Finset.mem_inter.mpr ⟨hp, hj⟩⟩
      · intro ⟨j, hpj⟩
        exact (Finset.mem_inter.mp hpj).1
    have hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin (NQ Q)))
        (fun j => ((E ∩ realizationBin r Q n j : Finset ℕ) : Set ℕ)) := by
      intro i _ j _ hij
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      intro x hx
      have hd := realizationBin_disjoint r Q n i j hij
      intro hxj
      rw [Finset.coe_inter] at hx hxj
      rw [Set.mem_inter_iff] at hx hxj
      have hxi : x ∈ realizationBin r Q n i := by simpa using hx.2
      have hxj' : x ∈ realizationBin r Q n j := by simpa using hxj.2
      exact Finset.disjoint_left.mp hd hxi hxj'
    rw [hE_disj_union]
    rw [Finset.prod_biUnion (by
      apply Finset.pairwiseDisjoint_iff.mpr
      intro i hi j hj hnempty
      by_contra hij
      rw [Finset.nonempty_iff_ne_empty] at hnempty
      have hne := Finset.nonempty_of_ne_empty hnempty
      obtain ⟨x, hx⟩ := hne
      simp only [Finset.mem_inter] at hx
      have hd := realizationBin_disjoint r Q n i j hij
      exact Finset.disjoint_left.mp hd hx.1.2 hx.2.2)]
    apply Finset.prod_le_prod
    · intro j _
      apply Finset.prod_nonneg
      intro p _
      positivity
    · intro j _
      -- Each element in E ∩ P_j is bounded by (j+1) * dQ Q * n^(1/r)
      have hcard : (E ∩ realizationBin r Q n j).card = τ j := by
        rw [realizationTypeFamily] at hE
        have hE' := Finset.mem_filter.mp hE
        have hcond := hE'.2 j.val (Finset.mem_range.mpr j.2)
        simp [j.2] at hcond
        exact hcond
      calc ∏ p ∈ E ∩ realizationBin r Q n j, (p : ℝ)
          ≤ ∏ _p ∈ E ∩ realizationBin r Q n j, (((j.val + 1) : ℕ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)) := by
            apply Finset.prod_le_prod
            · intro p _
              positivity
            · intro p hp
              have hp_bin := (Finset.mem_inter.mp hp).2
              have := realizationBin_le_scale hp_bin
              norm_cast at this
        _ = (((j.val + 1) : ℕ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)) ^ (E ∩ realizationBin r Q n j).card := by
            rw [Finset.prod_const, Finset.card_eq_sum_ones]
        _ = (((j.val + 1) : ℕ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)) ^ (τ j) := by rw [hcard]
  -- Now we show ∏ j, ((j+1) * dQ Q * n^(1/r))^(τ j) ≤ n
  have hprod_bound : (∏ j : Fin (NQ Q), (((j.val + 1) : ℕ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)) ^ (τ j)) ≤ (n : ℝ) := by
    -- τ sums to r (from being in types)
    have htypes : τ ∈ types r Q := (Finset.mem_filter.mp hτ).1
    have hsum : ∑ j : Fin (NQ Q), τ j = r := by
      unfold types at htypes
      exact Finset.mem_filter.mp htypes |>.2
    -- Split the product
    have hsplit : ∏ j : Fin (NQ Q), (((j.val + 1) : ℕ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)) ^ (τ j) =
        (∏ j : Fin (NQ Q), ((j.val + 1) : ℝ) ^ (τ j)) * (dQ Q) ^ r * (n : ℝ) := by
      have h1 : ∀ j : Fin (NQ Q), (((j.val + 1) : ℕ) * dQ Q * (n : ℝ) ^ ((1 : ℝ) / r)) ^ (τ j) =
          ((j.val + 1) : ℝ) ^ (τ j) * (dQ Q) ^ (τ j) * (n : ℝ) ^ ((τ j : ℝ) / (r : ℝ)) := by
        intro j
        rw [mul_pow, mul_pow]
        have : ((n : ℝ) ^ ((1 : ℝ) / r)) ^ (τ j) = (n : ℝ) ^ (((τ j : ℕ) : ℝ) / (r : ℝ)) := by
          rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / r)) (τ j)]
          rw [← Real.rpow_mul (Nat.cast_nonneg n)]
          congr 1
          ring
        rw [this]
        ring_nf
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      rw [Finset.prod_congr rfl fun j _ => h1 j]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      congr 1
      · rw [show (∏ x : Fin (NQ Q), dQ Q ^ τ x) = dQ Q ^ (∑ x : Fin (NQ Q), τ x) by rw [← Finset.prod_pow_eq_pow_sum]]
        rw [hsum]
      · rw [← Real.rpow_sum_of_pos (Nat.cast_pos.mpr (by linarith : 0 < n))]
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        have hsum' : (∑ i : Fin (NQ Q), (τ i : ℝ)) = (r : ℝ) := by exact_mod_cast hsum
        rw [hsum']
        rw [mul_inv_cancel₀ (by positivity : (r : ℝ) ≠ 0)]
        rw [Real.rpow_one]
    -- Use admissibility: ∏ j (j+1)^(τ j) ≤ 2^(Q*r)
    have hadm_prod : ∏ j : Fin (NQ Q), ((j.val + 1) : ℝ) ^ (τ j) ≤ (2 : ℝ) ^ (Q * r) := by
      have := hadm
      exact_mod_cast this
    -- dQ Q = 1 / 2^Q, so (dQ Q)^r = 2^(-Q*r)
    have hdQ_pow : (dQ Q) ^ r = (2 : ℝ) ^ (-(Q * r : ℤ)) := by
      unfold dQ
      simp [zpow_neg, zpow_mul, pow_right_comm]
    -- Combine: product ≤ 2^(Qr) * 2^(-Qr) * n = n
    rw [hsplit, hdQ_pow]
    have h1 : ((2 : ℝ) ^ (Q * r)) * (2 : ℝ) ^ (-(Q * r : ℤ)) = 1 := by
      simp [zpow_neg]
      norm_cast
      rw [mul_inv_cancel₀ (by positivity)]
    calc (∏ j : Fin (NQ Q), ((j.val + 1) : ℝ) ^ (τ j)) * (2 : ℝ) ^ (-(Q * r : ℤ)) * (n : ℝ)
        ≤ (2 : ℝ) ^ (Q * r) * (2 : ℝ) ^ (-(Q * r : ℤ)) * (n : ℝ) := by gcongr
      _ = 1 * (n : ℝ) := by rw [h1]
      _ = (n : ℝ) := by ring
  have hE_prod_nat : (∏ p ∈ E, (p : ℝ)) ≤ (n : ℝ) := le_trans hprod_le hprod_bound
  rw [← Nat.cast_prod, Nat.cast_le] at hE_prod_nat
  exact hE_prod_nat

/-- A family assembled from admissible realization types is uniformly `r`-element. -/
lemma typed_realization_uniform {r Q n : ℕ} {H : Finset (Finset ℕ)}
    (htyped : ∀ E ∈ H, ∃ τ ∈ admTypes r Q, E ∈ realizationTypeFamily r Q n τ) :
    ∀ E ∈ H, E.card = r := by
  intro E hE
  obtain ⟨τ, hτ, hEt⟩ := htyped E hE
  exact realizationTypeFamily_card hτ hEt

/-- Every set of a realization type is supported on the realization vertices. -/
lemma realizationTypeFamily_subset {r Q n : ℕ} {τ : Fin (NQ Q) → ℕ}
    {E : Finset ℕ} (hE : E ∈ realizationTypeFamily r Q n τ) :
    E ⊆ realizationVertices r Q n := by
  rw [realizationTypeFamily] at hE
  unfold setsOfType at hE
  have h := Finset.mem_powerset.mp (Finset.mem_filter.mp hE).1
  apply h.trans
  rw [realizationVertices]
  refine Finset.subset_iff.mpr ?_
  intro x hx
  simp only [Finset.mem_biUnion] at hx ⊢
  obtain ⟨j, hj, hxj⟩ := hx
  simp only [Finset.mem_range] at hj
  use ⟨j, hj⟩
  simp_all

/-- Membership in a realization type records the prescribed cardinality in
    every prime bin. -/
lemma realizationTypeFamily_bin_card {r Q n : ℕ} {τ : Fin (NQ Q) → ℕ}
    {E : Finset ℕ} (hE : E ∈ realizationTypeFamily r Q n τ)
    (j : Fin (NQ Q)) : (E ∩ realizationBin r Q n j).card = τ j := by
  rw [realizationTypeFamily] at hE
  have hE' := Finset.mem_filter.mp hE
  have hcond := hE'.2 j.val (Finset.mem_range.mpr j.2)
  simp only [] at hcond
  simp [j.2] at hcond
  exact hcond

/-- A pairwise-linear family assembled from admissible realization types is a
linear prime hypergraph. -/
lemma typed_realization_isLinearPrimeHG {r Q n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    {H : Finset (Finset ℕ)}
    (htyped : ∀ E ∈ H, ∃ τ ∈ admTypes r Q, E ∈ realizationTypeFamily r Q n τ)
    (hlin : ∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1) :
    IsLinearPrimeHG r n H := by
  refine ⟨fun E hE => ?_, hlin⟩
  obtain ⟨τ, hτ, hEt⟩ := htyped E hE
  have hcard := typed_realization_uniform htyped E hE
  have hprod := realizationTypeFamily_product_le hr hn hτ hEt
  have hsub := realizationTypeFamily_subset hEt
  refine ⟨hcard, ?_, hprod⟩
  intro p hp
  have hp_mem := hsub hp
  refine ⟨realizationVertices_prime hp_mem, ?_⟩
  have hdiv : p ∣ ∏ q ∈ E, q := by
    apply Finset.dvd_prod_of_mem
    exact hp
  exact Nat.le_trans (Nat.le_of_dvd (Finset.prod_pos fun x hx => (realizationVertices_prime (hsub hx)).pos) hdiv) hprod

/-- Such a typed realization also satisfies the required global vertex cutoff. -/
lemma typed_realization_vertex_bound {r Q n : ℕ} {H : Finset (Finset ℕ)}
    (htyped : ∀ E ∈ H, ∃ τ ∈ admTypes r Q, E ∈ realizationTypeFamily r Q n τ) :
    ∀ p ∈ vertices H, (p : ℝ) ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r) := by
  apply realization_family_vertex_bound
  intro E hE
  obtain ⟨τ, hτ, hEt⟩ := htyped E hE
  exact realizationTypeFamily_subset hEt

/-- Two different realization types define disjoint families. -/
lemma realizationTypeFamily_disjoint {r Q n : ℕ}
    {τ σ : Fin (NQ Q) → ℕ} (hτσ : τ ≠ σ) :
    Disjoint (realizationTypeFamily r Q n τ) (realizationTypeFamily r Q n σ) := by
  by_contra h
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨E, hEτ, hEσ⟩ := h
  unfold realizationTypeFamily at hEτ hEσ
  simp only [setsOfType, Finset.mem_filter] at hEτ hEσ
  have hEτ_cond := hEτ.2
  have hEσ_cond := hEσ.2
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hτσ
  have hj_lt : (j : ℕ) < NQ Q := j.is_lt
  have eq1 := hEτ_cond j (Finset.mem_range.mpr hj_lt)
  have eq2 := hEσ_cond j (Finset.mem_range.mpr hj_lt)
  simp [hj_lt] at eq1 eq2
  exact hj (eq1.symm.trans eq2)

/-- A typed family is partitioned by its realization types, so its cardinality
is the sum of the corresponding type counts. -/
lemma typed_realization_card_eq_sum {r Q n : ℕ} {H : Finset (Finset ℕ)}
    (htyped : ∀ E ∈ H, ∃ τ ∈ admTypes r Q, E ∈ realizationTypeFamily r Q n τ) :
    (H.card : ℝ) = ∑ τ ∈ admTypes r Q,
      ((H.filter fun E => E ∈ realizationTypeFamily r Q n τ).card : ℝ) := by
  choose! f hf using htyped
  have hmaps : ∀ E ∈ H, f E ∈ admTypes r Q := fun E hE => (hf E hE).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  rw [Nat.cast_sum]
  -- E determines its type uniquely via bin counts
  have huniq : ∀ E ∈ H, ∀ τ₁ τ₂, τ₁ ∈ admTypes r Q → τ₂ ∈ admTypes r Q →
      E ∈ realizationTypeFamily r Q n τ₁ → E ∈ realizationTypeFamily r Q n τ₂ → τ₁ = τ₂ := by
    intro E hE τ₁ τ₂ hτ₁ hτ₂ hE1 hE2
    ext j
    exact Eq.symm (by rw [← realizationTypeFamily_bin_card hE1 j, ← realizationTypeFamily_bin_card hE2 j])
  apply Finset.sum_congr rfl
  intro τ hτ
  have heq : {a ∈ H | f a = τ} = {E ∈ H | E ∈ realizationTypeFamily r Q n τ} := by
    apply Finset.filter_congr
    intro E hEH
    constructor
    · intro hEf
      have := hf E hEH
      rw [hEf] at this
      exact this.2
    · intro hEτ
      rw [huniq E hEH _ _ (hf E hEH).1 hτ (hf E hEH).2 hEτ]
  rw [heq]

/-- Rounding each prescribed type count down loses less than one edge per
admissible type. -/
lemma realization_floor_sum_lower {r Q : ℕ}
    (z : (Fin (NQ Q) → ℕ) → ℝ) (S ρ : ℝ) (hz : ∀ τ, 0 ≤ z τ)
    (hS : 0 ≤ S) (hρ : ρ ≤ 1) :
    (1 - ρ) * valQ r Q z * S - ((admTypes r Q).card : ℝ) ≤
      ∑ τ ∈ admTypes r Q, (⌊(1 - ρ) * z τ * S⌋₊ : ℝ) := by
  have h_nonneg : ∀ τ ∈ admTypes r Q, 0 ≤ (1 - ρ) * z τ * S := by
    intro τ _
    apply mul_nonneg
    apply mul_nonneg
    · linarith
    · exact hz τ
    · exact hS
  calc (1 - ρ) * valQ r Q z * S - ((admTypes r Q).card : ℝ)
      = ∑ τ ∈ admTypes r Q, ((1 - ρ) * z τ * S) - ((admTypes r Q).card : ℝ) := by
        simp only [valQ]
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
    _ = ∑ τ ∈ admTypes r Q, ((1 - ρ) * z τ * S - 1) := by
        rw [show ((admTypes r Q).card : ℝ) = ∑ _ ∈ admTypes r Q, (1 : ℝ) from by simp]
        rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ τ ∈ admTypes r Q, (⌊(1 - ρ) * z τ * S⌋₊ : ℝ) := by
        gcongr with τ _
        linarith [Nat.floor_le (h_nonneg τ ‹_›), Nat.lt_floor_add_one ((1 - ρ) * z τ * S)]

/-- Deterministic assembly of the finite-realization conclusion from a typed,
pairwise-linear family with the prescribed rounded number of edges of each type.
This isolates the output-reading step after the probabilistic matching argument. -/
lemma finite_realization_of_exact_type_counts {r Q n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : ∀ τ, 0 ≤ z τ) {ρ : ℝ}
    (hρ : ρ ≤ 1) {H : Finset (Finset ℕ)}
    (htyped : ∀ E ∈ H, ∃ τ ∈ admTypes r Q, E ∈ realizationTypeFamily r Q n τ)
    (hlin : ∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1)
    (hcount : ∀ τ ∈ admTypes r Q,
      (H.filter fun E => E ∈ realizationTypeFamily r Q n τ).card =
        ⌊(1 - ρ) * z τ * Sval r n⌋₊) :
    IsLinearPrimeHG r n H ∧
      (∀ p ∈ vertices H, (p : ℝ) ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r)) ∧
      ((1 - ρ) * valQ r Q z * Sval r n - ((admTypes r Q).card : ℝ) ≤
        (H.card : ℝ)) := by
  refine ⟨typed_realization_isLinearPrimeHG hr hn htyped hlin,
          typed_realization_vertex_bound htyped, ?_⟩
  have hcard_eq : (H.card : ℝ) = ∑ τ ∈ admTypes r Q,
      ((H.filter fun E => E ∈ realizationTypeFamily r Q n τ).card : ℝ) :=
    typed_realization_card_eq_sum htyped
  rw [hcard_eq]
  have hS_nonneg : 0 ≤ Sval r n := by rw [Sval]; positivity
  have hsum_le : ∑ τ ∈ admTypes r Q, (⌊(1 - ρ) * z τ * Sval r n⌋₊ : ℝ) ≤
      ∑ τ ∈ admTypes r Q, ((H.filter fun E => E ∈ realizationTypeFamily r Q n τ).card : ℝ) := by
    apply Finset.sum_le_sum
    intro τ hτ
    rw [← hcount τ hτ]
  linarith [@realization_floor_sum_lower r Q z (Sval r n) ρ hz hS_nonneg hρ]

/-! ## The probabilistic realization step -/

/-- The basic scale `M = n^{1/r} / log n`; the realization scale is `S = M²`. -/
noncomputable def Mval (r n : ℕ) : ℝ := (n : ℝ) ^ ((1 : ℝ) / r) / Real.log n

lemma Sval_eq_Mval_sq (r n : ℕ) : Sval r n = (Mval r n) ^ 2 := rfl

lemma Mval_tendsto_atTop (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => Mval r n) atTop atTop := by
  unfold Mval
  have ha : (0 : ℝ) < 1 / r := by positivity
  have := powers_dominate_logs (1 / r) ha 1
  simp only [Real.rpow_one] at this
  exact this.comp tendsto_natCast_atTop_atTop

/-- Uniform two-sided bin-count estimates with an arbitrary relative error. -/
lemma realizationBin_card_eventually_close (r Q : ℕ) (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Fin (NQ Q),
      (1 - ε) * ((r : ℝ) * dQ Q) * Mval r n ≤ ((realizationBin r Q n j).card : ℝ) ∧
      ((realizationBin r Q n j).card : ℝ) ≤ (1 + ε) * ((r : ℝ) * dQ Q) * Mval r n := by
  have hr_pos : 0 < (r : ℝ) := by exact Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
  have hdQ_pos : 0 < dQ Q := by unfold dQ; positivity
  have hr_prod_pos : 0 < (r : ℝ) * dQ Q := mul_pos hr_pos hdQ_pos
  have hj : ∀ j : Fin (NQ Q), ∀ᶠ n : ℕ in atTop,
      (1 - ε) * ((r : ℝ) * dQ Q) * Mval r n ≤ ((realizationBin r Q n j).card : ℝ) ∧
      ((realizationBin r Q n j).card : ℝ) ≤ (1 + ε) * ((r : ℝ) * dQ Q) * Mval r n := by
    intro j
    have htend := realizationBin_card_tendsto r Q hr j
    unfold Mval at *
    have habs : ∀ᶠ n : ℕ in atTop, |((realizationBin r Q n j).card : ℝ) / ((n : ℝ) ^ ((1 : ℝ) / r) / Real.log n) - (r : ℝ) * dQ Q| < ε * ((r : ℝ) * dQ Q) :=
      htend.eventually (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [habs, eventually_gt_atTop 1] with n hn hn1
    have hn1' : (1 : ℝ) < n := by exact_mod_cast hn1
    have hlog_pos : 0 < Real.log n := Real.log_pos hn1'
    have hrpow_pos : 0 < (n : ℝ) ^ ((1 : ℝ) / r) := Real.rpow_pos_of_pos (by linarith) _
    have hMval_pos : 0 < (n : ℝ) ^ ((1 : ℝ) / r) / Real.log n := div_pos hrpow_pos hlog_pos
    rw [abs_lt] at hn
    constructor
    · have h1 : (1 - ε) * ((r : ℝ) * dQ Q) < ((realizationBin r Q n j).card : ℝ) / ((n : ℝ) ^ ((1 : ℝ) / r) / Real.log n) := by linarith
      have h1' : (1 - ε) * ((r : ℝ) * dQ Q) * ((n : ℝ) ^ ((1 : ℝ) / r) / Real.log n) < ((realizationBin r Q n j).card : ℝ) := by
        rwa [lt_div_iff₀ hMval_pos] at h1
      exact le_of_lt h1'
    · have h2 : ((realizationBin r Q n j).card : ℝ) / ((n : ℝ) ^ ((1 : ℝ) / r) / Real.log n) < (1 + ε) * ((r : ℝ) * dQ Q) := by linarith
      have h2' : ((realizationBin r Q n j).card : ℝ) < (1 + ε) * ((r : ℝ) * dQ Q) * ((n : ℝ) ^ ((1 : ℝ) / r) / Real.log n) := by
        rwa [div_lt_iff₀ hMval_pos] at h2
      exact le_of_lt h2'
  exact Filter.eventually_all.mpr hj

/-- Eventually every bin has at least `(r d_Q / 2) M` elements, and that
quantity exceeds `8`. -/
lemma bins_uniformly_large_eventually (r Q : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ n : ℕ in atTop, (8 : ℝ) ≤ (r : ℝ) * dQ Q / 2 * Mval r n ∧
      ∀ l : Fin (NQ Q),
        (r : ℝ) * dQ Q / 2 * Mval r n ≤ ((realizationBin r Q n l).card : ℝ) := by
  have hr_pos : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hdQ_pos : (0 : ℝ) < dQ Q := by unfold dQ; positivity
  have hc_pos : (0 : ℝ) < (r : ℝ) * dQ Q / 2 := by positivity
  have hclose := realizationBin_card_eventually_close r Q hr (ε := 1 / 2) (by norm_num)
  have hM : Filter.Tendsto (fun n : ℕ => (r : ℝ) * dQ Q / 2 * Mval r n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc_pos (Mval_tendsto_atTop r (by omega))
  have h8 : ∀ᶠ n : ℕ in atTop, (8 : ℝ) ≤ (r : ℝ) * dQ Q / 2 * Mval r n :=
    hM.eventually_ge_atTop 8
  filter_upwards [hclose, h8] with n hn h8n
  refine ⟨h8n, fun l => ?_⟩
  have := (hn l).1
  have heq : (1 - 1 / 2 : ℝ) * ((r : ℝ) * dQ Q) * Mval r n
      = (r : ℝ) * dQ Q / 2 * Mval r n := by ring
  linarith [heq ▸ this]

/-- The token type of the realization argument: `m τ` tokens of every admissible
type `τ`. -/
abbrev tokenType (r Q : ℕ) (m : (Fin (NQ Q) → ℕ) → ℕ) : Type :=
  Σ τ : {τ : Fin (NQ Q) → ℕ // τ ∈ admTypes r Q}, Fin (m τ.1)

/-- Deterministic readout: a token-indexed assignment of pairwise almost
disjoint edges of the prescribed types yields a linear family with exactly the
prescribed number of edges of every type. -/
lemma typed_selection_of_token_assignment (r Q n : ℕ) (hr : 3 ≤ r)
    (m : (Fin (NQ Q) → ℕ) → ℕ)
    (f : tokenType r Q m → Finset ℕ)
    (hmem : ∀ t, f t ∈ realizationTypeFamily r Q n t.1.1)
    (hlin : ∀ t t', t ≠ t' → ((f t) ∩ (f t')).card ≤ 1) :
    ∃ H : Finset (Finset ℕ),
      (∀ E ∈ H, ∃ τ ∈ admTypes r Q, E ∈ realizationTypeFamily r Q n τ) ∧
      (∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1) ∧
      (∀ τ ∈ admTypes r Q,
        (H.filter fun E => E ∈ realizationTypeFamily r Q n τ).card = m τ) := by
  use Finset.image f Finset.univ
  constructor
  · intro E hE
    rw [Finset.mem_image] at hE
    obtain ⟨t, _, rfl⟩ := hE
    exact ⟨t.1.1, t.1.2, hmem t⟩
  constructor
  · intro E hE E' hE' hEE'
    rw [Finset.mem_image] at hE hE'
    obtain ⟨t, _, rfl⟩ := hE
    obtain ⟨t', _, rfl⟩ := hE'
    exact hlin t t' (fun h => hEE' (h ▸ rfl))
  · -- First show f is injective
    have hinj : Function.Injective f := by
      intro t t' h_eq
      by_contra h_ne
      have hcard := hlin t t' h_ne
      rw [h_eq] at hcard
      simp at hcard
      have hf_t := hmem t
      have := realizationTypeFamily_card t.1.2 hf_t
      rw [h_eq.symm] at hcard
      omega
    intro τ hτ
    -- The filter on H is the image under f of tokens of type τ
    have hfilter : Finset.filter (fun E => E ∈ realizationTypeFamily r Q n τ) (Finset.image f Finset.univ) =
        Finset.image f (Finset.filter (fun t => t.1.1 = τ) Finset.univ) := by
      have : ∀ E, E ∈ Finset.filter (fun E => E ∈ realizationTypeFamily r Q n τ) (Finset.image f Finset.univ) ↔
                   E ∈ Finset.image f (Finset.filter (fun t => t.1.1 = τ) Finset.univ) := by
        intro E
        rw [Finset.mem_filter, Finset.mem_image, Finset.mem_image]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨ht1, hE⟩
          obtain ⟨t, rfl⟩ := ht1
          have ht2 := hmem t
          have htype : t.1.1 = τ := by
            by_contra hne
            have := realizationTypeFamily_disjoint (r := r) (n := n) hne
            exact Finset.disjoint_left.mp this ht2 hE
          exact ⟨t, htype, rfl⟩
        · rintro ⟨t, htype, rfl⟩
          refine ⟨⟨t, rfl⟩, ?_⟩
          rw [← htype]
          exact hmem t
      exact Finset.ext this
    rw [hfilter]
    -- Since f is injective, cardinality of image equals cardinality of domain
    rw [Finset.card_image_of_injective _ hinj]
    -- The filter {t | t.1.1 = τ} has cardinality m τ
    -- Tokens are Σ τ : {τ ∈ admTypes r Q}, Fin (m τ.1)
    -- For τ ∈ admTypes, there's exactly one subtype element ⟨τ, hτ⟩ with m τ values
    have hcard : (Finset.univ.filter (fun t : tokenType r Q m => t.1.1 = τ)).card = m τ := by
      have h1 : Fintype.card {t : tokenType r Q m // t.1.1 = τ} = m τ := by
        have heq : {t : tokenType r Q m // t.1.1 = τ} ≃ Fin (m τ) := {
          toFun := fun ⟨⟨⟨v, hv⟩, a⟩, h⟩ => Fin.cast (by rw [h]) a
          invFun := fun a => ⟨⟨⟨τ, hτ⟩, a⟩, rfl⟩
          left_inv := fun x => by
            obtain ⟨⟨⟨v, hv⟩, a⟩, h⟩ := x
            simp only
            have hv_eq : v = τ := h
            subst hv_eq
            rfl
          right_inv := fun a => by simp
        }
        rw [Fintype.card_congr heq, Fintype.card_fin]
      rw [← Fintype.card_coe]
      let e : ↥(Finset.univ.filter (fun t : tokenType r Q m => t.1.1 = τ)) ≃ {t : tokenType r Q m // t.1.1 = τ} := {
        toFun := fun x => ⟨x.val, (Finset.mem_filter.mp x.property).2⟩
        invFun := fun x => ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩⟩
        left_inv := fun x => by simp
        right_inv := fun x => by simp
      }
      exact Fintype.card_congr e ▸ h1
    exact hcard

/-! ### Completion counts -/

/-- For any set `W` of realization vertices with bin profile `σ`, the number of
  type-`τ` sets containing `W` satisfies
  `#comp · ∏_l C(N_l, σ_l) = E_τ · ∏_l C(τ_l, σ_l)`. -/
lemma realizationTypeFamily_completion_identity (r Q n : ℕ) (τ : Fin (NQ Q) → ℕ)
    (W : Finset ℕ) (hW : W ⊆ realizationVertices r Q n) :
    (((realizationTypeFamily r Q n τ).filter fun E => W ⊆ E).card) *
        (∏ l, ((realizationBin r Q n l).card).choose ((W ∩ realizationBin r Q n l).card)) =
      (realizationTypeFamily r Q n τ).card *
        (∏ l, (τ l).choose ((W ∩ realizationBin r Q n l).card)) := by
  by_cases hcompat : ∀ j : Fin (NQ Q), (W ∩ realizationBin r Q n j).card ≤ τ j
  · exact realizationTypeFamily_completion_mul_profile r Q n τ W hW hcompat
  · push_neg at hcompat
    obtain ⟨j, hj⟩ := hcompat
    have h_rhs_zero : (∏ l, (τ l).choose ((W ∩ realizationBin r Q n l).card)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact Nat.choose_eq_zero_of_lt hj
    rw [h_rhs_zero, mul_zero]
    have h_filter_empty : {E ∈ realizationTypeFamily r Q n τ | W ⊆ E} = ∅ := by
      ext E
      simp [Finset.mem_filter]
      intro hE hEW
      have hEW_j : W ∩ realizationBin r Q n j ⊆ E ∩ realizationBin r Q n j := by
        apply Finset.inter_subset_inter_right
        exact hEW
      have hcard : (W ∩ realizationBin r Q n j).card ≤ (E ∩ realizationBin r Q n j).card :=
        Finset.card_le_card hEW_j
      have hE_bin_j : (E ∩ realizationBin r Q n j).card ≤ τ j := by
        unfold realizationTypeFamily at hE
        simp only [setsOfType, Finset.mem_filter] at hE
        have h1 := hE.2 j (Finset.mem_range.mpr j.2)
        have hj_lt : j.val < NQ Q := j.2
        simp [hj_lt] at h1
        linarith
      linarith
    rw [h_filter_empty, Finset.card_empty, zero_mul]

/-- Crude lower bound for a single binomial coefficient with small lower index. -/
lemma choose_ge_pow_div {N s : ℕ} (hs : s ≤ 4) (hN : 8 ≤ N) :
    ((N : ℝ) / 48) ^ s ≤ (N.choose s : ℝ) := by
  interval_cases s
  · simp
  · simp; linarith
  · rw [Nat.choose_two_right]
    have hNpos : (0 : ℝ) < N := by positivity
    have hN2 : (N : ℝ) ≥ 8 := by norm_cast
    have hdiv : (2 : ℕ) ∣ N * (N - 1) := even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ )
    rw [Nat.cast_div hdiv]
    · have hN3 : (N : ℝ) ≥ 8 := by norm_cast
      have hN1 : N ≥ 1 := by linarith
      rw [show ((N * (N - 1) : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) by simp [Nat.cast_pred hN1]]
      ring_nf
      nlinarith [sq_nonneg ((N : ℝ) - 1)]
    · norm_num
  · have hN3 : (N : ℝ) ≥ 8 := by norm_cast
    have hge3 : N ≥ 3 := by linarith
    have heq : (N.choose 3 : ℝ) = N * (N - 1) * (N - 2) / 6 := by
      have h2 : ∀ m : ℕ, (m.choose 2 : ℝ) = m * (m - 1) / 2 := by
        intro m
        induction m with
        | zero => simp
        | succ n ih =>
          simp [Nat.choose_succ_succ, ih]
          ring
      have h3 : ∀ m : ℕ, (m.choose 3 : ℝ) = m * (m - 1) * (m - 2) / 6 := by
        intro m
        induction m with
        | zero => simp
        | succ n ih =>
          simp [Nat.choose_succ_succ, ih, h2]
          ring
      exact h3 N
    rw [heq]
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  · have hN4 : (N : ℝ) ≥ 8 := by norm_cast
    have hge4 : N ≥ 4 := by linarith
    have heq : (N.choose 4 : ℝ) = N * (N - 1) * (N - 2) * (N - 3) / 24 := by
      have h2 : ∀ m : ℕ, (m.choose 2 : ℝ) = m * (m - 1) / 2 := by
        intro m
        induction m with
        | zero => simp
        | succ n ih =>
          simp [Nat.choose_succ_succ, ih]
          ring
      have h3 : ∀ m : ℕ, (m.choose 3 : ℝ) = m * (m - 1) * (m - 2) / 6 := by
        intro m
        induction m with
        | zero => simp
        | succ n ih =>
          simp [Nat.choose_succ_succ, ih, h2]
          ring
      have h4 : ∀ m : ℕ, (m.choose 4 : ℝ) = m * (m - 1) * (m - 2) * (m - 3) / 24 := by
        intro m
        induction m with
        | zero => simp
        | succ n ih =>
          simp [Nat.choose_succ_succ, ih, h3 ]
          ring
      exact h4 N
    rw [heq]
    nlinarith [sq_nonneg ((N : ℝ) - 1)]

/-- The bin profile of a set of realization vertices has total mass `|W|`. -/
lemma profile_sum_card (r Q n : ℕ) (W : Finset ℕ) (hW : W ⊆ realizationVertices r Q n) :
    ∑ l, (W ∩ realizationBin r Q n l).card = W.card := by
  have hunion : W = Finset.biUnion Finset.univ (fun l => W ∩ realizationBin r Q n l) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have hx' := hW hx
      simp only [realizationVertices, Finset.mem_biUnion] at hx'
      obtain ⟨l, hl⟩ := hx'
      exact ⟨l, hx, hl.2⟩
    · intro ⟨l, hx, _⟩
      exact hx
  conv_rhs => rw [hunion]
  rw [Finset.card_biUnion]
  intro i _ j _ hij
  exact Disjoint.mono inf_le_right inf_le_right (realizationBin_disjoint r Q n i j hij)

/-- Crude lower bound for the profile normalizer `∏_l C(N_l, σ_l)`. -/
lemma profile_normalizer_lower (r Q n : ℕ) (W : Finset ℕ)
    (hW : W ⊆ realizationVertices r Q n) (hWcard : W.card ≤ 4) {Nmin : ℝ}
    (hNmin : ∀ l, Nmin ≤ ((realizationBin r Q n l).card : ℝ)) (h8 : 8 ≤ Nmin) :
    (Nmin / 2) ^ (W.card) / 24 ^ 4 ≤
      ((∏ l, ((realizationBin r Q n l).card).choose
        ((W ∩ realizationBin r Q n l).card) : ℕ) : ℝ) := by
  -- Use choose_ge_pow_div to bound each term in the product
  have h_choose_bound : ∀ l : Fin (NQ Q),
      ((realizationBin r Q n l).card).choose ((W ∩ realizationBin r Q n l).card) ≥
      ((Nmin / 48) ^ ((W ∩ realizationBin r Q n l).card) : ℝ) := by
    intro l
    have hN_cast : (8 : ℝ) ≤ ((realizationBin r Q n l).card : ℝ) := by linarith [hNmin l, h8]
    have hN_nat : 8 ≤ (realizationBin r Q n l).card := by exact_mod_cast hN_cast
    have hs : (W ∩ realizationBin r Q n l).card ≤ W.card := Finset.card_le_card (Finset.inter_subset_left)
    have hs' : (W ∩ realizationBin r Q n l).card ≤ 4 := Nat.le_trans hs hWcard
    have h_choose := choose_ge_pow_div hs' hN_nat
    have hl : ((realizationBin r Q n l).card : ℝ) / 48 ≥ Nmin / 48 := by linarith [hNmin l]
    exact le_trans (pow_le_pow_left₀ (by linarith : 0 ≤ Nmin / 48) hl _) h_choose
  -- Sum of intersection cardinalities equals W.card
  have h_sum_card := profile_sum_card r Q n W hW
  -- Product bound: ∏_l C(N_l, σ_l) ≥ ∏_l (Nmin/48)^σ_l = (Nmin/48)^(∑ σ_l) = (Nmin/48)^|W|
  have h_prod_bound : (∏ l : Fin (NQ Q), ((realizationBin r Q n l).card).choose
      ((W ∩ realizationBin r Q n l).card) : ℝ) ≥ (Nmin / 48) ^ W.card := by
    calc (∏ l : Fin (NQ Q), ((realizationBin r Q n l).card).choose
          ((W ∩ realizationBin r Q n l).card) : ℝ)
        ≥ ∏ l : Fin (NQ Q), (Nmin / 48) ^ ((W ∩ realizationBin r Q n l).card) := by
            exact Finset.prod_le_prod (fun _ _ => by positivity) (fun l _ => h_choose_bound l)
      _ = (Nmin / 48) ^ (∑ l : Fin (NQ Q), (W ∩ realizationBin r Q n l).card) := by
            rw [Finset.prod_pow_eq_pow_sum]
      _ = (Nmin / 48) ^ W.card := by rw [h_sum_card]
  -- Final comparison: (Nmin/48)^|W| ≥ (Nmin/2)^|W| / 24^4
  have h8_pos : 0 < (8 : ℝ) := by norm_num
  have hNmin_pos : 0 < Nmin := by linarith
  have hdiv2_pos : 0 < Nmin / 2 := by linarith
  have hdiv48_pos : 0 < Nmin / 48 := by linarith
  have h_ratio : (Nmin / 48) ^ W.card = (Nmin / 2) ^ W.card / 24 ^ W.card := by
    have : (Nmin / 2) / 24 = Nmin / 48 := by field_simp; norm_num
    rw [← this, div_pow]
  rw [h_ratio] at h_prod_bound
  -- Since W.card ≤ 4, we have 24^W.card ≤ 24^4, so (Nmin/2)^|W| / 24^|W| ≥ (Nmin/2)^|W| / 24^4
  have h24_pos : (0 : ℝ) < 24 := by norm_num
  have h24_pow : (24 : ℝ) ^ W.card ≤ 24 ^ 4 := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 24) hWcard
  have h24_pow_4 : (24 : ℝ) ^ 4 > 0 := by positivity
  have h24_pow_W : (24 : ℝ) ^ W.card > 0 := by positivity
  simp only [← Nat.cast_prod] at *
  exact le_trans (div_le_div_of_nonneg_left (by positivity : 0 ≤ (Nmin / 2) ^ W.card) h24_pow_W h24_pow) (ge_iff_le.mp h_prod_bound)

/-- Crude upper bound for the type profile factor `∏_l C(τ_l, σ_l)`. -/
lemma profile_type_upper (r Q n : ℕ) {τ : Fin (NQ Q) → ℕ} (hτ : τ ∈ admTypes r Q)
    (W : Finset ℕ) (hW : W ⊆ realizationVertices r Q n) :
    ((∏ l, (τ l).choose ((W ∩ realizationBin r Q n l).card) : ℕ) : ℝ) ≤ (r : ℝ) ^ (W.card) := by
  -- τ ∈ admTypes means τ ∈ types, so ∑ j, τ j = r
  have hsum : ∑ j, τ j = r := by
    rw [admTypes] at hτ
    have htypes := (Finset.mem_filter.mp hτ).1
    simp only [types, Finset.mem_filter] at htypes
    exact htypes.2
  -- First bound: (τ l).choose k ≤ (τ l) ^ k
  have hchoose : ∀ l, (τ l).choose ((W ∩ realizationBin r Q n l).card) ≤ (τ l) ^ ((W ∩ realizationBin r Q n l).card) := by
    intro l
    exact Nat.choose_le_pow _ _
  -- Product bound
  have hprod : (∏ l, (τ l).choose ((W ∩ realizationBin r Q n l).card)) ≤ ∏ l, (τ l) ^ ((W ∩ realizationBin r Q n l).card) := by
    exact Finset.prod_le_prod' (fun i _ => hchoose i)
  -- τ l ≤ r for each l since ∑ j, τ j = r
  have htau_le : ∀ l, τ l ≤ r := by
    intro l
    calc τ l ≤ ∑ j, τ j := Finset.single_le_sum (fun j _ => Nat.zero_le (τ j)) (Finset.mem_univ l)
      _ = r := hsum
  -- τ l ^ k ≤ r ^ k for each l
  have hpow_le : ∀ l, (τ l) ^ ((W ∩ realizationBin r Q n l).card) ≤ r ^ ((W ∩ realizationBin r Q n l).card) := by
    intro l
    exact Nat.pow_le_pow_left (htau_le l) _
  -- Product bound: ∏ l, τ l ^ k_l ≤ ∏ l, r ^ k_l = r ^ (∑ l k_l)
  have hprod2 : (∏ l, (τ l) ^ ((W ∩ realizationBin r Q n l).card)) ≤ ∏ l, (r) ^ ((W ∩ realizationBin r Q n l).card) := by
    exact Finset.prod_le_prod' (fun i _ => hpow_le i)
  -- ∏ l, r ^ k_l = r ^ (∑ l k_l)
  have hprod3 : (∏ l, (r) ^ ((W ∩ realizationBin r Q n l).card)) = (r) ^ (∑ l, ((W ∩ realizationBin r Q n l).card)) := by
    rw [Finset.prod_pow_eq_pow_sum]
  -- The bins partition W, so ∑ l (W ∩ bin l).card = W.card
  have hsum_card : ∑ l, ((W ∩ realizationBin r Q n l).card) = W.card := by
    -- Use that realization bins are pairwise disjoint and cover realizationVertices
    have hunion : realizationVertices r Q n = Finset.univ.biUnion (realizationBin r Q n) := rfl
    have hW' : W = Finset.biUnion Finset.univ (fun l => W ∩ realizationBin r Q n l) := by
      apply Finset.ext
      intro x
      show x ∈ W ↔ x ∈ Finset.biUnion Finset.univ (fun l => W ∩ realizationBin r Q n l)
      rw [Finset.mem_biUnion]
      simp only [Finset.mem_univ, true_and]
      constructor
      · intro hx
        have hx' := hW hx
        rw [hunion] at hx'
        simp only [Finset.mem_biUnion] at hx'
        obtain ⟨l, _, hl⟩ := hx'
        exact ⟨l, Finset.mem_inter.mpr ⟨hx, hl⟩⟩
      · intro hx
        obtain ⟨l, hxl⟩ := hx
        exact (Finset.mem_inter.mp hxl).1
    symm
    conv_lhs => rw [hW']
    apply Finset.card_biUnion
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x
    simp only [Finset.mem_inter]
    intro ⟨_, hiB⟩ ⟨_, hjB⟩
    exact Finset.disjoint_left.mp (realizationBin_disjoint r Q n i j hij) hiB hjB
  -- Chain the inequalities
  have hfinal : (∏ l, (τ l).choose ((W ∩ realizationBin r Q n l).card) : ℕ) ≤ (r) ^ W.card := by
    calc (∏ l, (τ l).choose ((W ∩ realizationBin r Q n l).card) : ℕ)
        ≤ ∏ l, (τ l) ^ ((W ∩ realizationBin r Q n l).card) := hprod
      _ ≤ ∏ l, (r) ^ ((W ∩ realizationBin r Q n l).card) := hprod2
      _ = (r) ^ (∑ l, ((W ∩ realizationBin r Q n l).card)) := hprod3
      _ = (r) ^ W.card := by rw [hsum_card]
  exact_mod_cast hfinal

/-- The bin profile of a two-element set of realization vertices is either two
distinct bins or a single bin used twice. -/
lemma pair_profile_cases (r Q n : ℕ) (w : Finset ℕ)
    (hw : w ⊆ realizationVertices r Q n) (hw2 : w.card = 2) :
    (∃ i j : Fin (NQ Q), i ≠ j ∧
       (∀ τ : Fin (NQ Q) → ℕ,
          (∏ l, (τ l).choose ((w ∩ realizationBin r Q n l).card)) = τ i * τ j) ∧
       (∏ l, ((realizationBin r Q n l).card).choose ((w ∩ realizationBin r Q n l).card))
          = (realizationBin r Q n i).card * (realizationBin r Q n j).card)
    ∨ (∃ i : Fin (NQ Q),
       (∀ τ : Fin (NQ Q) → ℕ,
          (∏ l, (τ l).choose ((w ∩ realizationBin r Q n l).card)) = (τ i).choose 2) ∧
       (∏ l, ((realizationBin r Q n l).card).choose ((w ∩ realizationBin r Q n l).card))
          = ((realizationBin r Q n i).card).choose 2) := by
  -- Each vertex belongs to exactly one bin; get the bin for each element of w
  have hw_mem : ∀ p ∈ w, ∃ j : Fin (NQ Q), p ∈ realizationBin r Q n j := by
    intro p hp
    have hp' : p ∈ realizationVertices r Q n := hw hp
    rw [realizationVertices] at hp'
    rw [Finset.mem_biUnion] at hp'
    exact ⟨hp'.choose, hp'.choose_spec.2⟩
  -- Define a function that gives the bin of each vertex
  choose bin_of bin_in using hw_mem
  -- w has 2 elements, so we can extract them
  rw [Finset.card_eq_two] at hw2
  obtain ⟨a, b, hab, rfl⟩ := hw2
  -- Case split on whether a and b are in the same bin
  let ia := bin_of a (by simp)
  let ib := bin_of b (by simp)
  -- Key: determine the intersection size for each bin l
  have haint : a ∈ realizationBin r Q n ia := bin_in a (by simp)
  have hbin : b ∈ realizationBin r Q n ib := bin_in b (by simp)
  -- For any l ≠ ia, a is not in bin l (by disjointness)
  have anotin : ∀ l, l ≠ ia → a ∉ realizationBin r Q n l := by
    intro l hne hmem
    have := realizationBin_disjoint r Q n ia l hne.symm
    exact Finset.disjoint_left.mp this haint hmem
  -- For any l ≠ ib, b is not in bin l (by disjointness)
  have bnotin : ∀ l, l ≠ ib → b ∉ realizationBin r Q n l := by
    intro l hne hmem
    have := realizationBin_disjoint r Q n ib l (Ne.symm hne)
    exact Finset.disjoint_left.mp this hbin hmem
  -- Helper: compute intersection card for each bin
  have hint_card : ∀ l : Fin (NQ Q), ({a, b} ∩ realizationBin r Q n l).card =
      if l = ia then if l = ib then 2 else 1 else if l = ib then 1 else 0 := by
    intro l
    by_cases hla : l = ia <;> by_cases hlb : l = ib <;> simp_all
  by_cases heq : ia = ib
  · -- Case 2: same bin
    right
    use ia
    have hsimp : ∀ l, ({a, b} ∩ realizationBin r Q n l).card = if l = ia then 2 else 0 := by
      intro l
      rw [hint_card]
      by_cases hla : l = ia <;> (simp [hla, heq]; try rfl)
      simp [show l ≠ ib from fun h => hla (heq ▸ h)]
    constructor
    · intro τ
      simp_rw [hsimp]
      have h2 : ∀ x, (τ x).choose (if x = ia then 2 else 0) = if x = ia then (τ x).choose 2 else 1 := by
        intro x; split_ifs <;> simp
      simp_rw [h2]
      rw [Fintype.prod_ite_eq']
    · simp_rw [hsimp]
      have h2 : ∀ x, (realizationBin r Q n x).card.choose (if x = ia then 2 else 0) =
          if x = ia then (realizationBin r Q n x).card.choose 2 else 1 := by
        intro x; split_ifs <;> simp
      simp_rw [h2]
      rw [Fintype.prod_ite_eq']
  · -- Case 1: different bins
    left
    have hne : ia ≠ ib := heq
    use ia, ib
    refine ⟨hne, ?_, ?_⟩
    · have hsimp : ∀ l, ({a, b} ∩ realizationBin r Q n l).card = if l = ia then 1 else if l = ib then 1 else 0 := by
        intro l
        rw [hint_card]
        by_cases hla : l = ia <;> by_cases hlb : l = ib <;> simp_all
      intro τ
      simp_rw [hsimp]
      have key : ∏ x, (τ x).choose (if x = ia then 1 else if x = ib then 1 else 0) =
          (∏ x, if x = ia then τ x else 1) * (∏ x, if x = ib then τ x else 1) := by
        rw [← Finset.prod_mul_distrib]
        congr 1 with x
        by_cases hax : x = ia <;> by_cases hbx : x = ib <;> simp_all
      rw [key]
      simp [Finset.mem_univ]
    · have hsimp : ∀ l, ({a, b} ∩ realizationBin r Q n l).card = if l = ia then 1 else if l = ib then 1 else 0 := by
        intro l
        rw [hint_card]
        by_cases hla : l = ia <;> by_cases hlb : l = ib <;> simp_all
      simp_rw [hsimp]
      have key : ∏ x, ((realizationBin r Q n x).card).choose (if x = ia then 1 else if x = ib then 1 else 0) =
          (∏ x, if x = ia then (realizationBin r Q n x).card else 1) *
          (∏ x, if x = ib then (realizationBin r Q n x).card else 1) := by
        rw [← Finset.prod_mul_distrib]
        congr 1 with x
        by_cases hax : x = ia <;> by_cases hbx : x = ib <;> simp_all
      rw [key]
      simp [Finset.mem_univ]

/-- Sums over tokens reduce to weighted sums over types. -/
lemma sum_over_tokens {r Q : ℕ} (m : (Fin (NQ Q) → ℕ) → ℕ)
    (g : (Fin (NQ Q) → ℕ) → ℝ) :
    ∑ t : tokenType r Q m, g t.1.1 = ∑ τ ∈ admTypes r Q, (m τ : ℝ) * g τ := by
  simp only [tokenType]
  rw [Fintype.sum_sigma]
  erw [← Finset.sum_attach (f := fun τ => (m τ : ℝ) * g τ)]
  congr 1 with τ
  simp

/-- The proportion of type-`τ` sets that contain a fixed small set `W` of
  realization vertices is at most a constant times `Nmin^{-|W|}`. -/
lemma completion_ratio_le (r Q n : ℕ) {τ : Fin (NQ Q) → ℕ} (hτ : τ ∈ admTypes r Q)
    (W : Finset ℕ) (hW : W ⊆ realizationVertices r Q n) (hWcard : W.card ≤ 4)
    {Nmin : ℝ} (hNmin : ∀ l, Nmin ≤ ((realizationBin r Q n l).card : ℝ)) (h8 : 8 ≤ Nmin)
    (hne : (realizationTypeFamily r Q n τ).Nonempty) :
    ((((realizationTypeFamily r Q n τ).filter fun E => W ⊆ E).card : ℝ)) /
        ((realizationTypeFamily r Q n τ).card : ℝ)
      ≤ (r : ℝ) ^ (W.card) * 24 ^ 4 / (Nmin / 2) ^ (W.card) := by
  -- Let's denote the products for convenience
  set P_τ := ∏ l, (τ l).choose ((W ∩ realizationBin r Q n l).card) with hP_τ
  set P_N := ∏ l, ((realizationBin r Q n l).card).choose ((W ∩ realizationBin r Q n l).card) with hP_N
  -- From completion identity: (#comp) * P_N = E_τ * P_τ
  have h_id := realizationTypeFamily_completion_identity r Q n τ W hW
  -- So (#comp) / E_τ = P_τ / P_N (when E_τ ≠ 0)
  -- First establish non-zeroness of E_τ
  have hE_pos : 0 < (realizationTypeFamily r Q n τ).card := Finset.card_pos.mpr hne
  -- We need P_N > 0 and P_τ ≥ 0
  -- P_N ≥ 0 always (it's a product of naturals)
  -- From bounds: P_τ ≤ r^(W.card) and P_N ≥ (Nmin/2)^(W.card) / 24^4 > 0
  have h_upper := profile_type_upper r Q n hτ W hW
  have h_lower := profile_normalizer_lower r Q n W hW hWcard hNmin h8
  -- (Nmin/2)^(W.card) / 24^4 > 0 since Nmin ≥ 8 > 0
  have hNmin_pos : 0 < Nmin := by linarith
  have hNM_pos : 0 < Nmin / 2 := by linarith
  have hNM_pow_pos : 0 < (Nmin / 2) ^ W.card := pow_pos hNM_pos _
  have h24_pow_pos : (0 : ℝ) < 24 ^ 4 := by norm_num
  have h_bound_pos : 0 < (Nmin / 2) ^ W.card / 24 ^ 4 := by positivity
  have hP_N_pos : 0 < (P_N : ℝ) := lt_of_lt_of_le h_bound_pos h_lower
  -- From h_id: (#comp) * P_N = E_τ * P_τ
  -- So (#comp) / E_τ = P_τ / P_N
  have h_ratio : (({E ∈ realizationTypeFamily r Q n τ | W ⊆ E}.card : ℝ) /
                  (realizationTypeFamily r Q n τ).card) = (P_τ : ℝ) / (P_N : ℝ) := by
    rw [div_eq_div_iff (by positivity) (ne_of_gt hP_N_pos)]
    have h : (({E ∈ realizationTypeFamily r Q n τ | W ⊆ E}.card : ℕ) * P_N : ℝ) =
             ((realizationTypeFamily r Q n τ).card * P_τ : ℝ) := by exact_mod_cast h_id
    simp only [] at h
    linarith
  rw [h_ratio]
  -- Now need: P_τ / P_N ≤ r^(W.card) * 24^4 / (Nmin/2)^(W.card)
  -- This follows from P_τ ≤ r^(W.card) and P_N ≥ (Nmin/2)^(W.card) / 24^4
  -- Rewrite as P_τ / P_N ≤ r^(W.card) / ((Nmin/2)^(W.card) / 24^4)
  have h_rewrite : (r : ℝ) ^ W.card * 24 ^ 4 / (Nmin / 2) ^ W.card =
                   (r : ℝ) ^ W.card / ((Nmin / 2) ^ W.card / 24 ^ 4) := by
    field_simp
  rw [h_rewrite]
  calc (P_τ : ℝ) / P_N ≤ (r : ℝ) ^ W.card / P_N := by
        apply div_le_div_of_nonneg_right h_upper (le_of_lt hP_N_pos)
    _ ≤ (r : ℝ) ^ W.card / ((Nmin / 2) ^ W.card / 24 ^ 4) := by
        apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ r ^ W.card) h_bound_pos h_lower

/-- Every bin is eventually larger than any prescribed constant. -/
lemma bins_ge_eventually (r Q : ℕ) (hr : 2 ≤ r) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ l : Fin (NQ Q), C ≤ ((realizationBin r Q n l).card : ℝ) := by
  have hr_pos : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hdQ_pos : (0 : ℝ) < dQ Q := by unfold dQ; positivity
  have hc_pos : (0 : ℝ) < (r : ℝ) * dQ Q / 2 := by positivity
  have hclose := realizationBin_card_eventually_close r Q hr (ε := 1 / 2) (by norm_num)
  have hM : Filter.Tendsto (fun n : ℕ => (r : ℝ) * dQ Q / 2 * Mval r n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc_pos (Mval_tendsto_atTop r (by omega))
  filter_upwards [hclose, hM.eventually_ge_atTop C] with n hn hCn l
  have h := (hn l).1
  have heq : (1 - 1 / 2 : ℝ) * ((r : ℝ) * dQ Q) * Mval r n
      = (r : ℝ) * dQ Q / 2 * Mval r n := by ring
  linarith [heq ▸ h]

/-- Eventually the total prescribed number of edges through two distinct bins
  stays below the number of available vertex pairs, with the slack `1 - 3ρ/4`.
  -/
lemma capacity_offdiag_eventually (r Q : ℕ) (hr : 2 ≤ r) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ i j : Fin (NQ Q),
      (1 - ρ) * Sval r n * ((r : ℝ) ^ 2 * dQ Q ^ 2) ≤
        (1 - 3 * ρ / 4) * (((realizationBin r Q n i).card : ℝ) *
          ((realizationBin r Q n j).card : ℝ)) := by
  -- Choose ε = ρ/8; then (1 - 3ρ/4) * (1 - ε)^2 > 1 - ρ
  set ε := ρ / 8 with hε_def
  have hε_pos : 0 < ε := by linarith
  have hε_lt_1 : ε < 1 := by linarith
  -- Get the eventual closeness of bin sizes
  have hclose := realizationBin_card_eventually_close r Q hr hε_pos
  -- Filter for n >= 2 to ensure Mval r n > 0
  have hge2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  filter_upwards [hclose, hge2] with n hbin hn2
  intro i j
  -- We have bounds on bin i and bin j
  have hi := hbin i
  have hj := hbin j
  -- Lower bounds
  have hi_lo := hi.1
  have hj_lo := hj.1
  -- Sval = Mval^2
  rw [Sval_eq_Mval_sq]
  have hr_pos : (0 : ℝ) < r := by positivity
  have hdQ_pos : (0 : ℝ) < dQ Q := by unfold dQ; positivity
  have hr_dQ_pos : (0 : ℝ) < r * dQ Q := mul_pos hr_pos hdQ_pos
  have h1_emulti_pos : (0 : ℝ) < (1 - ε) * (r * dQ Q) := by
    apply mul_pos
    · linarith
    · exact hr_dQ_pos
  -- Mval r n > 0 for n >= 2
  have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn_pos : (0 : ℝ) < n := by linarith
  have hMval_pos : (0 : ℝ) < Mval r n := by
    unfold Mval
    apply div_pos
    · exact Real.rpow_pos_of_pos hn_pos _
    · exact Real.log_pos (by linarith : (1 : ℝ) < n)
  -- Multiply the lower bounds
  have h_term_nonneg : (0 : ℝ) ≤ (1 - ε) * (r * dQ Q) * Mval r n :=
    mul_nonneg (le_of_lt h1_emulti_pos) (le_of_lt hMval_pos)
  have hprod_lo : ((1 - ε) * (r * dQ Q) * Mval r n) ^ 2 ≤
                  ((realizationBin r Q n i).card : ℝ) * ((realizationBin r Q n j).card : ℝ) := by
    have hi_nonneg : (0 : ℝ) ≤ ((realizationBin r Q n i).card : ℝ) := by positivity
    nlinarith [mul_le_mul hi_lo hj_lo h_term_nonneg hi_nonneg]
  -- Need: (1 - ρ) ≤ (1 - 3ρ/4) * (1 - ε)^2 with ε = ρ/8
  have h1_em_pos : (0 : ℝ) < 1 - ε := by linarith
  have h1_3rho4_pos : (0 : ℝ) < 1 - 3 * ρ / 4 := by linarith
  have hkey : (1 - ρ) ≤ (1 - 3 * ρ / 4) * (1 - ε) ^ 2 := by
    simp only [hε_def]
    nlinarith [sq_nonneg ρ]
  have hprod_rewrite : ((1 - ε) * (r * dQ Q) * Mval r n) ^ 2 = (1 - ε) ^ 2 * (r * dQ Q) ^ 2 * Mval r n ^ 2 := by ring
  rw [hprod_rewrite] at hprod_lo
  -- Now: (1 - ε)^2 * (r * dQ Q)^2 * Mval^2 ≤ bin_prod
  -- Goal: (1 - ρ) * Mval^2 * (r^2 * dQ^2) ≤ (1 - 3ρ/4) * bin_prod
  -- We have: (1 - ρ) ≤ (1 - 3ρ/4) * (1 - ε)^2
  -- So: (1 - ρ) * Mval^2 * (r * dQ)^2 ≤ (1 - 3ρ/4) * (1 - ε)^2 * (r * dQ)^2 * Mval^2
  --     ≤ (1 - 3ρ/4) * bin_prod
  have h1 : (1 - ρ) * Mval r n ^ 2 * ((r : ℝ) * dQ Q) ^ 2
          ≤ (1 - 3 * ρ / 4) * ((1 - ε) ^ 2 * (r * dQ Q) ^ 2 * Mval r n ^ 2) := by
    have hmul : (1 - ρ) * ((r * dQ Q) ^ 2 * Mval r n ^ 2)
              ≤ (1 - 3 * ρ / 4) * (1 - ε) ^ 2 * ((r * dQ Q) ^ 2 * Mval r n ^ 2) := by
      exact mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ (r * dQ Q) ^ 2 * Mval r n ^ 2)
    linarith
  have h2 : (1 - 3 * ρ / 4) * ((1 - ε) ^ 2 * (r * dQ Q) ^ 2 * Mval r n ^ 2)
          ≤ (1 - 3 * ρ / 4) * (((realizationBin r Q n i).card : ℝ) * ((realizationBin r Q n j).card : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hprod_lo (le_of_lt h1_3rho4_pos)
  linarith

/-- The same estimate for two vertices in the same bin. -/
lemma capacity_diag_eventually (r Q : ℕ) (hr : 2 ≤ r) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (NQ Q),
      (1 - ρ) * Sval r n * ((r : ℝ) ^ 2 / 2 * dQ Q ^ 2) ≤
        (1 - 3 * ρ / 4) * ((((realizationBin r Q n i).card).choose 2 : ℕ) : ℝ) := by
  have hr_pos : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hdQ_pos : (0 : ℝ) < dQ Q := by unfold dQ; positivity
  have hclose := realizationBin_card_eventually_close r Q hr (ε := ρ / 16) (by linarith)
  have hbig := bins_ge_eventually r Q hr (16 / ρ + 1)
  filter_upwards [hclose, hbig, eventually_ge_atTop 2] with n hbin hNbig hn2
  intro i
  have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hMval_pos : (0 : ℝ) < Mval r n := by
    unfold Mval
    exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos (by linarith))
  set N : ℝ := ((realizationBin r Q n i).card : ℝ) with hN
  have hlo : (1 - ρ / 16) * ((r : ℝ) * dQ Q) * Mval r n ≤ N := (hbin i).1
  have hNbig' : 16 / ρ + 1 ≤ N := hNbig i
  have hNlarge : (33 : ℝ) ≤ N := by
    have : (32 : ℝ) ≤ 16 / ρ := by
      rw [le_div_iff₀ hρ0]; linarith
    linarith
  have hchoose : ((((realizationBin r Q n i).card).choose 2 : ℕ) : ℝ) = N * (N - 1) / 2 := by
    rw [hN]
    exact_mod_cast Nat.cast_choose_two (K := ℝ) _
  rw [hchoose, Sval_eq_Mval_sq]
  -- basic positivity
  have hA : (0 : ℝ) < (1 - ρ / 16) * ((r : ℝ) * dQ Q) * Mval r n := by
    have : (0 : ℝ) < 1 - ρ / 16 := by linarith
    positivity
  have hkey16 : (16 : ℝ) ≤ ρ * N := by
    have h := mul_le_mul_of_nonneg_left hNbig' hρ0.le
    have heq : ρ * (16 / ρ + 1) = 16 + ρ := by field_simp
    rw [heq] at h
    linarith
  have h1 : (1 - ρ / 16) * N ≤ N - 1 := by nlinarith
  have h2 : (1 - ρ / 16) * ((1 - ρ / 16) * ((r : ℝ) * dQ Q) * Mval r n) ^ 2 ≤ N * (N - 1) := by
    have hsq : ((1 - ρ / 16) * ((r : ℝ) * dQ Q) * Mval r n) ^ 2 ≤ N ^ 2 := by
      nlinarith
    nlinarith
  have hscal : (1 - ρ) ≤ (1 - 3 * ρ / 4) * (1 - ρ / 16) ^ 3 := by nlinarith [sq_nonneg ρ, pow_pos hρ0 3]
  have hMr : (0 : ℝ) ≤ ((r : ℝ) * dQ Q * Mval r n) ^ 2 := by positivity
  have hkey : (1 - ρ) * ((r : ℝ) * dQ Q * Mval r n) ^ 2
      ≤ (1 - 3 * ρ / 4) * ((1 - ρ / 16) * ((1 - ρ / 16) * ((r : ℝ) * dQ Q) * Mval r n) ^ 2) := by
    have hexp : (1 - ρ / 16) * ((1 - ρ / 16) * ((r : ℝ) * dQ Q) * Mval r n) ^ 2
        = (1 - ρ / 16) ^ 3 * ((r : ℝ) * dQ Q * Mval r n) ^ 2 := by ring
    rw [hexp]
    nlinarith [mul_le_mul_of_nonneg_right hscal hMr]
  have hfinal : (1 - ρ) * ((r : ℝ) * dQ Q * Mval r n) ^ 2 ≤ (1 - 3 * ρ / 4) * (N * (N - 1)) := by
    have h3 : (1 - 3 * ρ / 4) * ((1 - ρ / 16) * ((1 - ρ / 16) * ((r : ℝ) * dQ Q) * Mval r n) ^ 2)
        ≤ (1 - 3 * ρ / 4) * (N * (N - 1)) := by
      apply mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  nlinarith [hfinal]

/-- Eventually every admissible type family is nonempty. -/
lemma family_card_pos_eventually (r Q : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ τ ∈ admTypes r Q, 0 < ((realizationTypeFamily r Q n τ).card) := by
  filter_upwards [bins_ge_eventually r Q hr r] with n hn τ hτ
  rw [card_realizationTypeFamily]
  refine Finset.prod_pos fun l _ => Nat.choose_pos ?_
  have htypes : τ ∈ types r Q := (Finset.mem_filter.mp hτ).1
  have hsum : ∑ j : Fin (NQ Q), τ j = r := by
    unfold types at htypes
    exact Finset.mem_filter.mp htypes |>.2
  have hle : τ l ≤ r := by
    have h := Finset.single_le_sum (f := fun j : Fin (NQ Q) => τ j)
      (fun j _ => Nat.zero_le (τ j)) (Finset.mem_univ l)
    simpa [hsum] using h
  have hNl : (r : ℝ) ≤ ((realizationBin r Q n l).card : ℝ) := hn l
  have : r ≤ (realizationBin r Q n l).card := by exact_mod_cast hNl
  omega

/-- The expected number of retained incidence edges at a fixed vertex pair,
    normalized by `D`, is eventually at most `1 - 3ρ/4`. -/
lemma pair_degree_bound (r Q : ℕ) (hr : 3 ≤ r)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : IsPacking r Q z) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ w ∈ (realizationVertices r Q n).powersetCard 2,
      ∑ τ ∈ admTypes r Q, (⌊(1 - ρ) * z τ * Sval r n⌋₊ : ℝ) *
          ((((realizationTypeFamily r Q n τ).filter fun E => w ⊆ E).card : ℝ) /
            ((realizationTypeFamily r Q n τ).card : ℝ))
        ≤ 1 - 3 * ρ / 4 := by
  have hr2 : 2 ≤ r := by omega
  -- the packing constraints, in the symmetric off-diagonal form
  have hpack_off : ∀ i j : Fin (NQ Q), i ≠ j →
      ∑ τ ∈ admTypes r Q, ((τ i : ℝ) * (τ j : ℝ)) * z τ ≤ (r : ℝ) ^ 2 * dQ Q ^ 2 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hz.2.1 i j h
    · have hji := hz.2.1 j i h
      have hsw : ∑ τ ∈ admTypes r Q, ((τ i : ℝ) * (τ j : ℝ)) * z τ
          = ∑ τ ∈ admTypes r Q, ((τ j : ℝ) * (τ i : ℝ)) * z τ :=
        Finset.sum_congr rfl fun τ _ => by ring
      rw [hsw]; exact hji
  filter_upwards [capacity_offdiag_eventually r Q hr2 hρ0 hρ1,
    capacity_diag_eventually r Q hr2 hρ0 hρ1,
    family_card_pos_eventually r Q hr2,
    bins_ge_eventually r Q hr2 1, eventually_ge_atTop 2] with
    n hoff hdiag hfam hbin1 hn2
  intro w hw
  rw [Finset.mem_powersetCard] at hw
  obtain ⟨hwsub, hw2⟩ := hw
  have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hSpos : (0 : ℝ) < Sval r n := by
    rw [Sval_eq_Mval_sq]
    have hMval_pos : (0 : ℝ) < Mval r n := by
      unfold Mval
      exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos (by linarith))
    positivity
  have hz0 : ∀ τ, 0 ≤ z τ := hz.1
  have hfloor : ∀ τ, (⌊(1 - ρ) * z τ * Sval r n⌋₊ : ℝ) ≤ (1 - ρ) * z τ * Sval r n := by
    intro τ
    exact Nat.floor_le (mul_nonneg (mul_nonneg (by linarith) (hz0 τ)) hSpos.le)
  rcases pair_profile_cases r Q n w hwsub hw2 with ⟨i, j, hij, hτprod, hNprod⟩ | ⟨i, hτprod, hNprod⟩
  · -- two distinct bins
    have hcap := hoff i j
    set Ni : ℝ := ((realizationBin r Q n i).card : ℝ) with hNi
    set Nj : ℝ := ((realizationBin r Q n j).card : ℝ) with hNj
    have hNipos : (0 : ℝ) < Ni := lt_of_lt_of_le (by norm_num) (hbin1 i)
    have hNjpos : (0 : ℝ) < Nj := lt_of_lt_of_le (by norm_num) (hbin1 j)
    have hratio : ∀ τ ∈ admTypes r Q,
        ((((realizationTypeFamily r Q n τ).filter fun E => w ⊆ E).card : ℝ) /
          ((realizationTypeFamily r Q n τ).card : ℝ))
          = ((τ i : ℝ) * (τ j : ℝ)) / (Ni * Nj) := by
      intro τ hτ
      have hid := realizationTypeFamily_completion_identity r Q n τ w hwsub
      rw [hNprod, hτprod τ] at hid
      have hcast : ((((realizationTypeFamily r Q n τ).filter fun E => w ⊆ E).card : ℝ)) *
          (Ni * Nj) = ((realizationTypeFamily r Q n τ).card : ℝ) * ((τ i : ℝ) * (τ j : ℝ)) := by
        rw [hNi, hNj]
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hid
      have hcardpos : (0 : ℝ) < ((realizationTypeFamily r Q n τ).card : ℝ) := by
        exact_mod_cast hfam τ hτ
      field_simp
      linarith [hcast]
    have hsum_le : ∑ τ ∈ admTypes r Q, (⌊(1 - ρ) * z τ * Sval r n⌋₊ : ℝ) *
        ((((realizationTypeFamily r Q n τ).filter fun E => w ⊆ E).card : ℝ) /
          ((realizationTypeFamily r Q n τ).card : ℝ))
        ≤ ∑ τ ∈ admTypes r Q, ((1 - ρ) * Sval r n / (Ni * Nj)) *
            (((τ i : ℝ) * (τ j : ℝ)) * z τ) := by
      refine Finset.sum_le_sum fun τ hτ => ?_
      rw [hratio τ hτ]
      have hnn : (0 : ℝ) ≤ ((τ i : ℝ) * (τ j : ℝ)) / (Ni * Nj) :=
        div_nonneg (by positivity) (mul_pos hNipos hNjpos).le
      have := mul_le_mul_of_nonneg_right (hfloor τ) hnn
      refine this.trans ?_
      apply le_of_eq
      field_simp
      try ring
    refine hsum_le.trans ?_
    rw [← Finset.mul_sum]
    have hbound : ∑ τ ∈ admTypes r Q, ((τ i : ℝ) * (τ j : ℝ)) * z τ ≤ (r : ℝ) ^ 2 * dQ Q ^ 2 :=
      hpack_off i j hij
    have hcoef : (0 : ℝ) ≤ (1 - ρ) * Sval r n / (Ni * Nj) := by
      have : (0 : ℝ) < 1 - ρ := by linarith
      positivity
    refine (mul_le_mul_of_nonneg_left hbound hcoef).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith [hcap]
  · -- a single bin, used twice
    have hcapd := hdiag i
    set Ni : ℝ := ((realizationBin r Q n i).card : ℝ) with hNi
    have hNipos : (0 : ℝ) < Ni := lt_of_lt_of_le (by norm_num) (hbin1 i)
    set C : ℝ := ((((realizationBin r Q n i).card).choose 2 : ℕ) : ℝ) with hC
    have hCpos : (0 : ℝ) < C := by
      by_contra hle
      push_neg at hle
      have hCnn : (0 : ℝ) ≤ C := by positivity
      have hC0 : C = 0 := le_antisymm hle hCnn
      rw [hC0, mul_zero] at hcapd
      have : (0 : ℝ) < (1 - ρ) * Sval r n * ((r : ℝ) ^ 2 / 2 * dQ Q ^ 2) := by
        have h1 : (0 : ℝ) < 1 - ρ := by linarith
        have h2 : (0 : ℝ) < (r : ℝ) := by
          have : 0 < r := by omega
          exact_mod_cast this
        have h3 : (0 : ℝ) < dQ Q := by unfold dQ; positivity
        positivity
      linarith
    have hratio : ∀ τ ∈ admTypes r Q,
        ((((realizationTypeFamily r Q n τ).filter fun E => w ⊆ E).card : ℝ) /
          ((realizationTypeFamily r Q n τ).card : ℝ))
          = (((τ i).choose 2 : ℕ) : ℝ) / C := by
      intro τ hτ
      have hid := realizationTypeFamily_completion_identity r Q n τ w hwsub
      rw [hNprod, hτprod τ] at hid
      have hcast : ((((realizationTypeFamily r Q n τ).filter fun E => w ⊆ E).card : ℝ)) * C
          = ((realizationTypeFamily r Q n τ).card : ℝ) * (((τ i).choose 2 : ℕ) : ℝ) := by
        rw [hC]
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hid
      have hcardpos : (0 : ℝ) < ((realizationTypeFamily r Q n τ).card : ℝ) := by
        exact_mod_cast hfam τ hτ
      field_simp
      linarith [hcast]
    have hsum_le : ∑ τ ∈ admTypes r Q, (⌊(1 - ρ) * z τ * Sval r n⌋₊ : ℝ) *
        ((((realizationTypeFamily r Q n τ).filter fun E => w ⊆ E).card : ℝ) /
          ((realizationTypeFamily r Q n τ).card : ℝ))
        ≤ ∑ τ ∈ admTypes r Q, ((1 - ρ) * Sval r n / C) *
            ((((τ i).choose 2 : ℕ) : ℝ) * z τ) := by
      refine Finset.sum_le_sum fun τ hτ => ?_
      rw [hratio τ hτ]
      have hnn : (0 : ℝ) ≤ (((τ i).choose 2 : ℕ) : ℝ) / C :=
        div_nonneg (by positivity) hCpos.le
      have := mul_le_mul_of_nonneg_right (hfloor τ) hnn
      refine this.trans ?_
      apply le_of_eq
      field_simp
      try ring
    refine hsum_le.trans ?_
    rw [← Finset.mul_sum]
    have hbound : ∑ τ ∈ admTypes r Q, (((τ i).choose 2 : ℕ) : ℝ) * z τ
        ≤ (r : ℝ) ^ 2 / 2 * dQ Q ^ 2 := hz.2.2 i
    have hcoef : (0 : ℝ) ≤ (1 - ρ) * Sval r n / C := by
      have : (0 : ℝ) < 1 - ρ := by linarith
      positivity
    refine (mul_le_mul_of_nonneg_left hbound hcoef).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hCpos]
    exact hcapd

/-! ## The probabilistic core of finite realization -/

/-- The proportion of type-`τ` sets containing a fixed set `W`. -/
noncomputable def compRatio (r Q n : ℕ) (τ : Fin (NQ Q) → ℕ) (W : Finset ℕ) : ℝ :=
  (((realizationTypeFamily r Q n τ).filter fun E => W ⊆ E).card : ℝ) /
    ((realizationTypeFamily r Q n τ).card : ℝ)

/-- The number of tokens is the total prescribed number of edges. -/
lemma card_tokenType (r Q : ℕ) (m : (Fin (NQ Q) → ℕ) → ℕ) :
    (Fintype.card (tokenType r Q m) : ℝ) = ∑ τ ∈ admTypes r Q, (m τ : ℝ) := by
  simp [tokenType, Fintype.card_sigma, Finset.sum_attach]

/-- At a fixed scale `n`, the random retention of incidence edges together with
  the Delcourt–Postle matching theorem produces a linear family with exactly `m
  τ` edges of every admissible type, provided the expected-degree, codegree and
  union-bound hypotheses hold. -/
lemma typed_selection_of_hypotheses (r Q : ℕ) (hr : 3 ≤ r) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∃ Dq : ℝ, ∀ (n : ℕ) (m : (Fin (NQ Q) → ℕ) → ℕ) (D κ : ℝ),
      0 < D → Dq ≤ (1 - ρ / 2) * D → 0 < κ →
      1 ≤ (Real.log ((1 - ρ / 2) * D)) ^ 2 →
      (∀ τ ∈ admTypes r Q, D ≤ ((realizationTypeFamily r Q n τ).card : ℝ)) →
      (∀ τ ∈ admTypes r Q, ∀ E ∈ realizationTypeFamily r Q n τ,
        E.card = r ∧ E ⊆ realizationVertices r Q n) →
      (∀ w ∈ (realizationVertices r Q n).powersetCard 2,
        ∑ τ ∈ admTypes r Q, (m τ : ℝ) * compRatio r Q n τ w ≤ 1 - 3 * ρ / 4) →
      (∀ τ ∈ admTypes r Q, ∀ w ∈ (realizationVertices r Q n).powersetCard 2,
        D * compRatio r Q n τ w ≤ κ) →
      (∀ w ∈ (realizationVertices r Q n).powersetCard 2,
        ∀ w' ∈ (realizationVertices r Q n).powersetCard 2, w ≠ w' →
        ∑ τ ∈ admTypes r Q, (m τ : ℝ) * (D * compRatio r Q n τ (w ∪ w')) ≤ κ) →
      (((∑ τ ∈ admTypes r Q, (m τ : ℝ)) +
            (((realizationVertices r Q n).powersetCard 2).card : ℝ)) *
            Real.exp (-(ρ ^ 2 * D) / 32) +
          ((∑ τ ∈ admTypes r Q, (m τ : ℝ)) +
            (((realizationVertices r Q n).powersetCard 2).card : ℝ)) ^ 2 *
            (Real.exp 1 * κ / (Real.log ((1 - ρ / 2) * D)) ^ 2) ^
              ((Real.log ((1 - ρ / 2) * D)) ^ 2) < 1) →
      ((1 + ((1 - ρ / 2) * D) ^ (-(1 : ℝ) / (20 * (1 + r.choose 2)))) *
          ((1 - ρ / 2) * D) ≤ (1 - ρ / 4) * D) →
      ∃ H : Finset (Finset ℕ),
        (∀ E ∈ H, ∃ τ ∈ admTypes r Q, E ∈ realizationTypeFamily r Q n τ) ∧
        (∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1) ∧
        (∀ τ ∈ admTypes r Q,
          (H.filter fun E => E ∈ realizationTypeFamily r Q n τ).card = m τ) := by
  classical
  obtain ⟨Dq, hDq⟩ := exists_linear_token_assignment r (by omega)
  refine ⟨Dq, ?_⟩
  intro n m D κ hD hDq' hκ hK hfam hedges hpair hcod1 hcod2 hfail hgap
  set L := tokenType r Q m with hL
  set Vset := realizationVertices r Q n with hVset
  set F : L → Finset (Finset ℕ) := fun t => realizationTypeFamily r Q n t.1.1 with hF
  set K : ℝ := (Real.log ((1 - ρ / 2) * D)) ^ 2 with hKdef
  have hDpos : 0 < D := hD
  have hFcard : ∀ t : L, D ≤ ((F t).card : ℝ) := fun t => hfam t.1.1 t.1.2
  have hFpos : ∀ t : L, (0 : ℝ) < ((F t).card : ℝ) := fun t => lt_of_lt_of_le hD (hFcard t)
  set p : L → ℝ := fun t => D / ((F t).card : ℝ) with hp
  have hp01 : ∀ t, 0 ≤ p t ∧ p t ≤ 1 := by
    intro t
    constructor
    · exact div_nonneg hD.le (hFpos t).le
    · rw [hp, div_le_one (hFpos t)]
      exact hFcard t
  have hmeanL : ∀ t : L, ((F t).card : ℝ) * p t = D := by
    intro t
    rw [hp]
    field_simp
    exact div_self (ne_of_gt (hFpos t))
  -- the completion ratio rewritten as a proportion
  have hratio : ∀ (t : L) (w : Finset ℕ),
      (((F t).filter fun E => w ⊆ E).card : ℝ) * p t = D * compRatio r Q n t.1.1 w := by
    intro t w
    rw [hp, compRatio]
    field_simp [hF]
    ring
  have hmeanR : ∀ w ∈ Vset.powersetCard 2,
      ∑ t : L, (((F t).filter fun E => w ⊆ E).card : ℝ) * p t ≤ (1 - 3 * ρ / 4) * D := by
    intro w hw
    have hrw : ∑ t : L, (((F t).filter fun E => w ⊆ E).card : ℝ) * p t
        = ∑ t : L, D * compRatio r Q n t.1.1 w := by
      exact Finset.sum_congr rfl fun t _ => hratio t w
    rw [hrw, sum_over_tokens m (fun τ => D * compRatio r Q n τ w)]
    have hb := hpair w hw
    have : ∑ τ ∈ admTypes r Q, (m τ : ℝ) * (D * compRatio r Q n τ w)
        = D * ∑ τ ∈ admTypes r Q, (m τ : ℝ) * compRatio r Q n τ w := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
    rw [this]
    calc D * ∑ τ ∈ admTypes r Q, (m τ : ℝ) * compRatio r Q n τ w
        ≤ D * (1 - 3 * ρ / 4) := by
          exact mul_le_mul_of_nonneg_left hb hD.le
      _ = (1 - 3 * ρ / 4) * D := by ring
  have hmeanC1 : ∀ (t : L), ∀ w ∈ Vset.powersetCard 2,
      (((F t).filter fun E => w ⊆ E).card : ℝ) * p t ≤ κ := by
    intro t w hw
    rw [hratio t w]
    exact hcod1 t.1.1 t.1.2 w hw
  have hmeanC2 : ∀ w ∈ Vset.powersetCard 2, ∀ w' ∈ Vset.powersetCard 2, w ≠ w' →
      ∑ t : L, (((F t).filter fun E => w ⊆ E ∧ w' ⊆ E).card : ℝ) * p t ≤ κ := by
    intro w hw w' hw' hne
    have hrw : ∀ t : L, (((F t).filter fun E => w ⊆ E ∧ w' ⊆ E).card : ℝ) * p t
        = D * compRatio r Q n t.1.1 (w ∪ w') := by
      intro t
      have hfil : ((F t).filter fun E => w ⊆ E ∧ w' ⊆ E)
          = ((F t).filter fun E => w ∪ w' ⊆ E) :=
        Finset.filter_congr (fun E _ => by simp [Finset.union_subset_iff])
      rw [hfil, hratio t (w ∪ w')]
    rw [Finset.sum_congr rfl (fun t _ => hrw t), sum_over_tokens m
      (fun τ => D * compRatio r Q n τ (w ∪ w'))]
    have hb := hcod2 w hw w' hw' hne
    calc ∑ τ ∈ admTypes r Q, (m τ : ℝ) * (D * compRatio r Q n τ (w ∪ w'))
        = ∑ τ ∈ admTypes r Q, (m τ : ℝ) * (D * compRatio r Q n τ (w ∪ w')) := rfl
      _ ≤ κ := hb
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hcardL : (Fintype.card L : ℝ) = ∑ τ ∈ admTypes r Q, (m τ : ℝ) := card_tokenType r Q m
  have hρ1' : ρ < 1 := by linarith
  obtain ⟨G, hGsub, hGdeg, hGpair, hGcod1, hGcod2⟩ :=
    exists_good_retention ℕ Vset L F p hp01 D ρ κ K hD hρ0 hρ1' hKpos hmeanL hmeanR
      hmeanC1 hmeanC2 (by rw [hcardL]; exact hfail)
  -- now apply the Delcourt-Postle assignment
  have hD' : (0 : ℝ) < (1 - ρ / 2) * D := by nlinarith
  obtain ⟨f, hfmem, hflin⟩ := hDq ((1 - ρ / 2) * D) hDq' hD' ℕ Vset L G
    (by
      intro t E hE
      have hEF := hGsub t hE
      exact ⟨realizationTypeFamily_card t.1.2 hEF, realizationTypeFamily_subset hEF⟩)
    (by
      intro t
      exact le_trans hgap (hGdeg t))
    (by
      intro w hw
      exact hGpair w hw)
    (by
      intro t w hw
      exact hGcod1 t w hw)
    (by
      intro w hw w' hw' hne
      exact hGcod2 w hw w' hw' hne)
  refine typed_selection_of_token_assignment r Q n hr m f (fun t => hGsub t (hfmem t)) ?_
  intro t t' htt'
  exact hflin t t' htt'

/-! ### The concrete parameters of the construction -/

/-- The retention degree parameter `D = √M`. -/
noncomputable def Dval (r n : ℕ) : ℝ := Real.sqrt (Mval r n)

/-- The codegree mean bound `κ = M^{-1/4}`. -/
noncomputable def kapVal (r n : ℕ) : ℝ := (Mval r n) ^ (-(1 : ℝ) / 4)

/-- The prescribed number of edges of type `τ`. -/
noncomputable def edgeCount (r Q n : ℕ) (ρ : ℝ) (z : (Fin (NQ Q) → ℕ) → ℝ)
    (τ : Fin (NQ Q) → ℕ) : ℕ := ⌊(1 - ρ) * z τ * Sval r n⌋₊

/-- Every realization vertex set is small: at most `Q n^{1/r}` primes. -/
lemma card_realizationVertices_le (r Q n : ℕ) :
    ((realizationVertices r Q n).card : ℝ) ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r) := by
  have hsub : realizationVertices r Q n ⊆ Finset.Ico 1 (Nat.floor ((Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r)) + 1) := by
    intro p hp
    simp [Finset.mem_Ico]
    constructor
    · have := realizationVertices_prime hp
      linarith [Nat.Prime.one_lt this]
    · have h := realizationVertices_le_scale hp
      have h2 : p ≤ Nat.floor ((Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r)) := by
        rw [Nat.le_floor_iff (by positivity)]
        exact h
      simp only [one_div] at h2 ⊢
      linarith
  calc ((realizationVertices r Q n).card : ℝ) ≤ (Finset.Ico 1 (Nat.floor ((Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r)) + 1)).card := by
        exact_mod_cast Finset.card_mono hsub
    _ = Nat.floor ((Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r)) := by simp
    _ ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r) := Nat.floor_le (by positivity)

/-- Every type family consists of `r`-element subsets of the realization
vertices. -/
lemma realizationTypeFamily_edges (r Q n : ℕ) :
    ∀ τ ∈ admTypes r Q, ∀ E ∈ realizationTypeFamily r Q n τ,
      E.card = r ∧ E ⊆ realizationVertices r Q n :=
  fun _ hτ _ hE => ⟨realizationTypeFamily_card hτ hE, realizationTypeFamily_subset hE⟩

/-- A binomial coefficient with a positive lower index is at least `N - t + 1`. -/
lemma choose_ge_sub_succ (N t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ N) : N - t + 1 ≤ N.choose t := by
  have choose_ge_self : ∀ n k, 1 ≤ k → k < n → n ≤ n.choose k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk1 hkn
      rcases k with _ | k
      · omega
      · rcases n with _ | n
        · omega
        · simp [Nat.choose_succ_succ]
          by_cases hkN : k + 1 = n
          · -- k + 1 = n: n+1 ≤ n.choose n + n.choose (n-1) = 1 + n
            subst hkN
            simp
          · have hkN' : k + 1 < n + 1 := hkn
            have hkN_lt : k + 1 < n := lt_of_le_of_ne (by omega) hkN
            have h1 : n ≤ n.choose (k + 1) := ih n (by omega) (k + 1) (by omega) hkN_lt
            by_cases hk0 : k = 0
            · simp [hk0]
            · have hk1' : 1 ≤ k := by omega
              have hkN'' : k < n := by omega
              have h2 : n ≤ n.choose k := ih n (by omega) k hk1' hkN''
              omega
  rcases eq_or_lt_of_le h2 with rfl | ht
  · simp
  · exact le_trans (by omega : N - t + 1 ≤ N) (choose_ge_self N t h1 ht)

/-- If every bin has at least `K ≥ r` elements, then every admissible type
family has at least `K - r + 1` members. -/
lemma family_card_ge_of_bins_large (r Q n : ℕ) {τ : Fin (NQ Q) → ℕ}
    (hτ : τ ∈ admTypes r Q) {K : ℝ}
    (hbins : ∀ j : Fin (NQ Q), K ≤ ((realizationBin r Q n j).card : ℝ))
    (hK : (r : ℝ) ≤ K) (hr : 1 ≤ r) :
    K - r + 1 ≤ ((realizationTypeFamily r Q n τ).card : ℝ) := by
  -- τ ∈ admTypes r Q implies ∑ i, τ i = r
  have hsum : ∑ i, τ i = r :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hτ).1).2
  -- Since τ sums to r ≥ 1, there exists some j with τ j ≥ 1
  have hexists : ∃ j : Fin (NQ Q), τ j ≥ 1 := by
    by_contra h
    push_neg at h
    have : ∑ i, τ i = 0 := Finset.sum_eq_zero fun i _ => Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (h i))
    omega
  obtain ⟨j, hj_pos⟩ := hexists
  -- For any j, bin_j.card ≥ K ≥ r ≥ τ j
  have hK_nat : ∀ i : Fin (NQ Q), (r : ℕ) ≤ ((realizationBin r Q n i).card : ℕ) := by
    intro i
    have hi := hbins i
    have hrK : (r : ℝ) ≤ K := hK
    have hKpos : 0 ≤ K := le_trans (by positivity : (0 : ℝ) ≤ r) hrK
    exact_mod_cast (by linarith : (r : ℝ) ≤ ((realizationBin r Q n i).card : ℝ))
  have hτj_le_K : τ j ≤ ((realizationBin r Q n j).card : ℕ) := by
    have h_le : τ j ≤ ∑ i, τ i := Finset.single_le_sum (fun i _ => Nat.zero_le (τ i)) (Finset.mem_univ j)
    linarith [hsum, hK_nat j]
  -- By choose_ge_sub_succ: bin_j.card.choose (τ j) ≥ bin_j.card - τ j + 1
  have hchoose : ((realizationBin r Q n j).card).choose (τ j) ≥ ((realizationBin r Q n j).card : ℕ) - τ j + 1 := by
    exact choose_ge_sub_succ _ _ hj_pos hτj_le_K
  -- The product is at least this value
  rw [card_realizationTypeFamily]
  have hprod_ge : (∏ i : Fin (NQ Q), (realizationBin r Q n i).card.choose (τ i)) ≥
      ((realizationBin r Q n j).card).choose (τ j) := by
    have hall_ge_one : ∀ i : Fin (NQ Q), 1 ≤ (realizationBin r Q n i).card.choose (τ i) := by
      intro i
      apply Nat.choose_pos
      have hbin_i := hbins i
      have hτi_le_r : τ i ≤ r := by
        have : τ i ≤ ∑ k, τ k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        rw [hsum] at this
        exact this
      exact Nat.le_trans hτi_le_r (hK_nat i)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    apply Nat.le_mul_of_pos_right
    exact Finset.prod_pos fun i _ => hall_ge_one i
  have hfinal : ((realizationBin r Q n j).card.choose (τ j) : ℝ) ≥ K - r + 1 := by
    have hcast : ((realizationBin r Q n j).card.choose (τ j) : ℝ) ≥
        ((realizationBin r Q n j).card : ℝ) - τ j + 1 := by
      exact_mod_cast Nat.cast_le.mpr hchoose
    have hbin_ge : ((realizationBin r Q n j).card : ℝ) ≥ K := hbins j
    have hτj_le_r : (τ j : ℝ) ≤ r := by
      have h_le : τ j ≤ ∑ i, τ i := Finset.single_le_sum (fun i _ => Nat.zero_le (τ i)) (Finset.mem_univ j)
      exact_mod_cast (by linarith [hsum] : τ j ≤ r)
    linarith
  exact le_trans hfinal (mod_cast hprod_ge)

/-- Eventually every type family is larger than the degree parameter. -/
lemma Dval_le_family_card_eventually (r Q : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ τ ∈ admTypes r Q,
      Dval r n ≤ ((realizationTypeFamily r Q n τ).card : ℝ) := by
  have hr_pos : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hdQ_pos : (0 : ℝ) < dQ Q := by unfold dQ; positivity
  set a : ℝ := 4 / ((r : ℝ) * dQ Q) with ha
  have hapos : (0 : ℝ) < a := by positivity
  have hM := Mval_tendsto_atTop r (by omega)
  filter_upwards [bins_uniformly_large_eventually r Q (by omega),
    hM.eventually_ge_atTop (a ^ 2),
    hM.eventually_ge_atTop (4 * (r : ℝ) / ((r : ℝ) * dQ Q))] with n hbins hMa hMr τ hτ
  obtain ⟨h8, hbin⟩ := hbins
  have hMpos : (0 : ℝ) < Mval r n := lt_of_lt_of_le (by positivity) hMa
  -- `√M ≤ (r d_Q / 4) M`
  have h1 : a ≤ Real.sqrt (Mval r n) := by
    have := Real.sqrt_le_sqrt hMa
    rwa [Real.sqrt_sq hapos.le] at this
  have hs : Real.sqrt (Mval r n) * a ≤ Mval r n := by
    have hmul := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Mval r n))
    rwa [Real.mul_self_sqrt hMpos.le] at hmul
  have hsqrt : Real.sqrt (Mval r n) ≤ (r : ℝ) * dQ Q / 4 * Mval r n := by
    have hdiv : Real.sqrt (Mval r n) ≤ Mval r n / a := by
      rw [le_div_iff₀ hapos]; exact hs
    have heq : Mval r n / a = (r : ℝ) * dQ Q / 4 * Mval r n := by
      rw [ha]; field_simp
    linarith [heq ▸ hdiv]
  -- the quarter-scale already dominates `r`
  have hquarter : (r : ℝ) ≤ (r : ℝ) * dQ Q / 4 * Mval r n := by
    have h := mul_le_mul_of_nonneg_left hMr (le_of_lt (by positivity : (0:ℝ) < (r : ℝ) * dQ Q / 4))
    have heq : (r : ℝ) * dQ Q / 4 * (4 * (r : ℝ) / ((r : ℝ) * dQ Q)) = r := by
      field_simp
    linarith [heq ▸ h]
  have hK : (r : ℝ) ≤ (r : ℝ) * dQ Q / 2 * Mval r n := by
    have : (r : ℝ) * dQ Q / 4 * Mval r n ≤ (r : ℝ) * dQ Q / 2 * Mval r n := by
      have : (0 : ℝ) ≤ Mval r n := hMpos.le
      nlinarith [hMpos, hr_pos, hdQ_pos]
    linarith
  have hfam := family_card_ge_of_bins_large r Q n hτ hbin hK (by omega)
  have hDval : Dval r n = Real.sqrt (Mval r n) := rfl
  rw [hDval]
  have hstep : (r : ℝ) * dQ Q / 2 * Mval r n - r + 1
      ≥ (r : ℝ) * dQ Q / 4 * Mval r n := by
    have hhalf : (r : ℝ) * dQ Q / 2 * Mval r n
        = (r : ℝ) * dQ Q / 4 * Mval r n + (r : ℝ) * dQ Q / 4 * Mval r n := by ring
    linarith [hquarter, hhalf]
  linarith

/-- Uniform eventual bound for the completion ratio at a set of `c ≤ 4`
prescribed vertices. -/
lemma compRatio_le_eventually (r Q c : ℕ) (hr : 3 ≤ r) (hc : c ≤ 4) :
    ∀ᶠ n : ℕ in atTop, ∀ τ ∈ admTypes r Q, ∀ W : Finset ℕ,
      W ⊆ realizationVertices r Q n → W.card = c →
        compRatio r Q n τ W ≤
          (r : ℝ) ^ c * 24 ^ 4 / ((r : ℝ) * dQ Q / 4 * Mval r n) ^ c := by
  filter_upwards [bins_uniformly_large_eventually r Q (by omega),
    family_card_pos_eventually r Q (by omega)] with n hbins hfam τ hτ W hW hWc
  obtain ⟨h8, hbin⟩ := hbins
  have hne : (realizationTypeFamily r Q n τ).Nonempty :=
    Finset.card_pos.mp (hfam τ hτ)
  have h := completion_ratio_le r Q n hτ W hW (by omega) hbin h8 hne
  rw [compRatio]
  rw [hWc] at h
  have heq : ((r : ℝ) * dQ Q / 2 * Mval r n) / 2 = (r : ℝ) * dQ Q / 4 * Mval r n := by ring
  rw [heq] at h
  exact h

/-- The codegree parameter in terms of iterated square roots. -/
lemma kapVal_eq_sqrt (r n : ℕ) (hM : 0 ≤ Mval r n) :
    kapVal r n = 1 / Real.sqrt (Real.sqrt (Mval r n)) := by
  rw [kapVal, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hM, one_div,
    ← Real.rpow_neg hM]
  norm_num

/-- A square root is at most the number itself, above one. -/
lemma sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ x), Real.sqrt_nonneg x,
    Real.one_le_sqrt.mpr hx]

/-- Iterated square roots stay below the scale itself. -/
lemma sqrt_sqrt_le_self {x : ℝ} (hx : 1 ≤ x) : Real.sqrt (Real.sqrt x) ≤ x := by
  have h1 : Real.sqrt x ≤ x := sqrt_le_self_of_one_le hx
  have h2 : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  exact le_trans (sqrt_le_self_of_one_le h2) h1

/-- Eventual token/vertex-pair codegree mean bound. -/
lemma codegree_token_pair_eventually (r Q : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ τ ∈ admTypes r Q,
      ∀ w ∈ (realizationVertices r Q n).powersetCard 2,
        Dval r n * compRatio r Q n τ w ≤ kapVal r n := by
  have hr_pos : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hdQ_pos : (0 : ℝ) < dQ Q := by unfold dQ; positivity
  set c : ℝ := (r : ℝ) * dQ Q / 4 with hc
  have hcpos : (0 : ℝ) < c := by rw [hc]; positivity
  set C : ℝ := (r : ℝ) ^ 2 * 24 ^ 4 / c ^ 2 with hC
  have hCpos : (0 : ℝ) < C := by rw [hC]; positivity
  have hM := Mval_tendsto_atTop r (by omega)
  filter_upwards [compRatio_le_eventually r Q 2 hr (by norm_num),
    hM.eventually_ge_atTop 1, hM.eventually_ge_atTop (C ^ 2)] with n hratio hM1 hMC τ hτ w hw
  rw [Finset.mem_powersetCard] at hw
  have hMpos : (0 : ℝ) < Mval r n := by linarith
  have hsqrtpos : (0 : ℝ) < Real.sqrt (Mval r n) := Real.sqrt_pos.mpr hMpos
  have hCle : C ≤ Real.sqrt (Mval r n) := by
    have := Real.sqrt_le_sqrt hMC
    rwa [Real.sqrt_sq hCpos.le] at this
  have hcomp : compRatio r Q n τ w ≤ C / Mval r n ^ 2 := by
    have h := hratio τ hτ w hw.1 hw.2
    have heq : (r : ℝ) ^ 2 * 24 ^ 4 / (c * Mval r n) ^ 2 = C / Mval r n ^ 2 := by
      rw [hC]; field_simp
    rw [heq] at h
    exact h
  have hDval : Dval r n = Real.sqrt (Mval r n) := rfl
  have hprod : Dval r n * compRatio r Q n τ w
      ≤ Real.sqrt (Mval r n) * (C / Mval r n ^ 2) := by
    rw [hDval]
    exact mul_le_mul_of_nonneg_left hcomp (Real.sqrt_nonneg _)
  have hkey : Real.sqrt (Mval r n) * (C / Mval r n ^ 2) ≤ 1 / Mval r n := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hMpos]
    have hsq : Real.sqrt (Mval r n) * Real.sqrt (Mval r n) = Mval r n :=
      Real.mul_self_sqrt hMpos.le
    have hstep : Real.sqrt (Mval r n) * C * Mval r n
        ≤ Real.sqrt (Mval r n) * Real.sqrt (Mval r n) * Mval r n := by
      have := mul_le_mul_of_nonneg_left hCle hsqrtpos.le
      nlinarith [hMpos]
    calc Real.sqrt (Mval r n) * C * Mval r n
        ≤ Real.sqrt (Mval r n) * Real.sqrt (Mval r n) * Mval r n := hstep
      _ = Mval r n ^ 2 := by rw [hsq]; ring
      _ = 1 * Mval r n ^ 2 := by ring
  have hkap : 1 / Mval r n ≤ kapVal r n := by
    rw [kapVal_eq_sqrt r n hMpos.le]
    apply one_div_le_one_div_of_le
    · exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hMpos)
    · exact sqrt_sqrt_le_self hM1
  linarith

/-- Eventual vertex-pair/vertex-pair codegree mean bound. -/
lemma codegree_pair_pair_eventually (r Q : ℕ) (hr : 3 ≤ r)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : IsPacking r Q z) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ w ∈ (realizationVertices r Q n).powersetCard 2,
      ∀ w' ∈ (realizationVertices r Q n).powersetCard 2, w ≠ w' →
        ∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ) *
            (Dval r n * compRatio r Q n τ (w ∪ w')) ≤ kapVal r n := by
  have hr_pos : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hdQ_pos : (0 : ℝ) < dQ Q := by unfold dQ; positivity
  set c : ℝ := (r : ℝ) * dQ Q / 4 with hc
  have hcpos : (0 : ℝ) < c := by rw [hc]; positivity
  set V : ℝ := ∑ τ ∈ admTypes r Q, z τ with hV
  have hVnn : 0 ≤ V := Finset.sum_nonneg fun τ _ => hz.1 τ
  set C : ℝ := (r : ℝ) ^ 3 * 24 ^ 4 / c ^ 3 + (r : ℝ) ^ 4 * 24 ^ 4 / c ^ 4 with hC
  have hCpos : (0 : ℝ) < C := by rw [hC]; positivity
  have hM := Mval_tendsto_atTop r (by omega)
  filter_upwards [compRatio_le_eventually r Q 3 hr (by norm_num),
    compRatio_le_eventually r Q 4 hr (by norm_num),
    hM.eventually_ge_atTop 1, hM.eventually_ge_atTop ((V * C + 1) ^ 4)] with
    n hratio3 hratio4 hM1 hMC w hw w' hw' hne
  rw [Finset.mem_powersetCard] at hw hw'
  have hMpos : (0 : ℝ) < Mval r n := by linarith
  have hsqrtpos : (0 : ℝ) < Real.sqrt (Mval r n) := Real.sqrt_pos.mpr hMpos
  have hUsub : w ∪ w' ⊆ realizationVertices r Q n := Finset.union_subset hw.1 hw'.1
  have hUcard : (w ∪ w').card = 3 ∨ (w ∪ w').card = 4 := by
    have hle : (w ∪ w').card ≤ 4 := by
      have := Finset.card_union_le w w'
      omega
    have hge : 3 ≤ (w ∪ w').card := by
      by_contra hlt
      push_neg at hlt
      have hsubw : w ⊆ w ∪ w' := Finset.subset_union_left
      have hsubw' : w' ⊆ w ∪ w' := Finset.subset_union_right
      have h2 : (w ∪ w').card = 2 := by
        have := Finset.card_le_card hsubw
        omega
      have hww : w = w ∪ w' := Finset.eq_of_subset_of_card_le hsubw (by omega)
      have hww' : w' = w ∪ w' := Finset.eq_of_subset_of_card_le hsubw' (by omega)
      exact hne (hww.trans hww'.symm)
    omega
  -- a uniform bound for the completion ratio at the union
  have hcomp : ∀ τ ∈ admTypes r Q, compRatio r Q n τ (w ∪ w') ≤ C / Mval r n ^ 3 := by
    intro τ hτ
    rcases hUcard with h3 | h4
    · have h := hratio3 τ hτ (w ∪ w') hUsub h3
      have heq : (r : ℝ) ^ 3 * 24 ^ 4 / (c * Mval r n) ^ 3
          = ((r : ℝ) ^ 3 * 24 ^ 4 / c ^ 3) / Mval r n ^ 3 := by
        field_simp
      rw [heq] at h
      refine h.trans ?_
      apply div_le_div_of_nonneg_right ?_ (by positivity)
      · rw [hC]; nlinarith [(by positivity : (0:ℝ) < (r : ℝ) ^ 4 * 24 ^ 4 / c ^ 4)]
    · have h := hratio4 τ hτ (w ∪ w') hUsub h4
      have heq : (r : ℝ) ^ 4 * 24 ^ 4 / (c * Mval r n) ^ 4
          = ((r : ℝ) ^ 4 * 24 ^ 4 / c ^ 4) / Mval r n ^ 4 := by
        field_simp
      rw [heq] at h
      refine h.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hMle : Mval r n ^ 3 ≤ Mval r n ^ 4 := pow_le_pow_right₀ hM1 (by norm_num)
      have h2 : (r : ℝ) ^ 4 * 24 ^ 4 / c ^ 4 ≤ C := by
        rw [hC]; nlinarith [(by positivity : (0:ℝ) < (r : ℝ) ^ 3 * 24 ^ 4 / c ^ 3)]
      calc (r : ℝ) ^ 4 * 24 ^ 4 / c ^ 4 * Mval r n ^ 3
          ≤ C * Mval r n ^ 3 := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ C * Mval r n ^ 4 := mul_le_mul_of_nonneg_left hMle hCpos.le
  -- the number of edges of each type is bounded by the total weight
  have hedge : ∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ) ≤ V * Mval r n ^ 2 := by
    have hS : Sval r n = Mval r n ^ 2 := Sval_eq_Mval_sq r n
    calc ∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)
        ≤ ∑ τ ∈ admTypes r Q, z τ * Mval r n ^ 2 := by
          refine Finset.sum_le_sum fun τ hτ => ?_
          rw [edgeCount]
          have hnn : (0:ℝ) ≤ (1 - ρ) * z τ * Sval r n := by
            have h1 : (0:ℝ) ≤ 1 - ρ := by linarith
            have h2 : (0:ℝ) ≤ Sval r n := by rw [hS]; positivity
            exact mul_nonneg (mul_nonneg h1 (hz.1 τ)) h2
          have hfl := Nat.floor_le hnn
          have : (1 - ρ) * z τ * Sval r n ≤ z τ * Mval r n ^ 2 := by
            rw [hS]
            nlinarith [mul_nonneg (mul_nonneg hρ0.le (hz.1 τ))
              (by positivity : (0:ℝ) ≤ Mval r n ^ 2)]
          linarith
      _ = V * Mval r n ^ 2 := by rw [hV, Finset.sum_mul]
  -- assemble
  have hterm : ∀ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ) *
      (Dval r n * compRatio r Q n τ (w ∪ w'))
      ≤ (edgeCount r Q n ρ z τ : ℝ) * (Real.sqrt (Mval r n) * (C / Mval r n ^ 3)) := by
    intro τ hτ
    have hDval : Dval r n = Real.sqrt (Mval r n) := rfl
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hDval]
    exact mul_le_mul_of_nonneg_left (hcomp τ hτ) (Real.sqrt_nonneg _)
  have hsum : ∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ) *
      (Dval r n * compRatio r Q n τ (w ∪ w'))
      ≤ (V * Mval r n ^ 2) * (Real.sqrt (Mval r n) * (C / Mval r n ^ 3)) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hedge (by positivity)
  refine hsum.trans ?_
  -- `V C √M / M ≤ M^{-1/4}`
  have hVC : V * C ≤ Real.sqrt (Real.sqrt (Mval r n)) := by
    have h1 : (V * C + 1) ^ 4 ≤ Mval r n := hMC
    have h2 : Real.sqrt ((V * C + 1) ^ 4) ≤ Real.sqrt (Mval r n) := Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt ((V * C + 1) ^ 4) = (V * C + 1) ^ 2 := by
      rw [show ((V * C + 1) ^ 4 : ℝ) = ((V * C + 1) ^ 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [h3] at h2
    have h4 : Real.sqrt (((V * C + 1)) ^ 2) ≤ Real.sqrt (Real.sqrt (Mval r n)) :=
      Real.sqrt_le_sqrt h2
    rw [Real.sqrt_sq (by positivity)] at h4
    linarith
  have hquad : Real.sqrt (Real.sqrt (Mval r n)) * Real.sqrt (Real.sqrt (Mval r n))
      = Real.sqrt (Mval r n) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hq_pos : (0:ℝ) < Real.sqrt (Real.sqrt (Mval r n)) :=
    Real.sqrt_pos.mpr hsqrtpos
  rw [kapVal_eq_sqrt r n hMpos.le]
  rw [le_div_iff₀ hq_pos]
  have hsq : Real.sqrt (Mval r n) * Real.sqrt (Mval r n) = Mval r n :=
    Real.mul_self_sqrt hMpos.le
  have hgoal : V * Mval r n ^ 2 * (Real.sqrt (Mval r n) * C) *
      Real.sqrt (Real.sqrt (Mval r n)) ≤ Mval r n ^ 3 := by
    have hmul : (V * C) * Real.sqrt (Real.sqrt (Mval r n))
        ≤ Real.sqrt (Real.sqrt (Mval r n)) * Real.sqrt (Real.sqrt (Mval r n)) :=
      mul_le_mul_of_nonneg_right hVC hq_pos.le
    rw [hquad] at hmul
    calc V * Mval r n ^ 2 * (Real.sqrt (Mval r n) * C) * Real.sqrt (Real.sqrt (Mval r n))
        = (Mval r n ^ 2 * Real.sqrt (Mval r n)) *
            (V * C * Real.sqrt (Real.sqrt (Mval r n))) := by ring
      _ ≤ (Mval r n ^ 2 * Real.sqrt (Mval r n)) * Real.sqrt (Mval r n) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = Mval r n ^ 3 := by rw [mul_assoc, hsq]; ring
  calc V * Mval r n ^ 2 * (Real.sqrt (Mval r n) * (C / Mval r n ^ 3)) *
        Real.sqrt (Real.sqrt (Mval r n))
      = (V * Mval r n ^ 2 * (Real.sqrt (Mval r n) * C) *
          Real.sqrt (Real.sqrt (Mval r n))) / Mval r n ^ 3 := by
        field_simp
    _ ≤ Mval r n ^ 3 / Mval r n ^ 3 := by
        apply div_le_div_of_nonneg_right hgoal (by positivity)
    _ = 1 := by field_simp

/-- Exponential decay beats a fixed polynomial. -/
lemma poly_mul_exp_neg_le {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) :
    ∀ᶠ s : ℝ in atTop, A * s ^ 8 * Real.exp (-(c * s)) ≤ 1 / 4 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (4 * (Nat.factorial 9 : ℝ) * A / c ^ 9 + 1)] with s hs1 hs2
  have hspos : (0 : ℝ) < s := by linarith
  have hexp : (c * s) ^ 9 / (Nat.factorial 9 : ℝ) ≤ Real.exp (c * s) :=
    Real.pow_div_factorial_le_exp _ (by positivity) 9
  have hc9 : 4 * (Nat.factorial 9 : ℝ) * A ≤ c ^ 9 * s := by
    have h := mul_le_mul_of_nonneg_left hs2 (le_of_lt (by positivity : (0:ℝ) < c ^ 9))
    have heq : c ^ 9 * (4 * (Nat.factorial 9 : ℝ) * A / c ^ 9 + 1)
        = 4 * (Nat.factorial 9 : ℝ) * A + c ^ 9 := by
      field_simp
    rw [heq] at h
    nlinarith [(by positivity : (0:ℝ) < c ^ 9)]
  have h4 : 4 * A * s ^ 8 ≤ Real.exp (c * s) := by
    refine le_trans ?_ hexp
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (Nat.factorial 9 : ℝ))]
    have hs8 : (0 : ℝ) ≤ s ^ 8 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hc9 hs8
    calc 4 * A * s ^ 8 * (Nat.factorial 9 : ℝ)
        = (4 * (Nat.factorial 9 : ℝ) * A) * s ^ 8 := by ring
      _ ≤ (c ^ 9 * s) * s ^ 8 := hmul
      _ = (c * s) ^ 9 := by ring
  have hexppos : (0 : ℝ) < Real.exp (c * s) := Real.exp_pos _
  have hrw : A * s ^ 8 * Real.exp (-(c * s)) = A * s ^ 8 / Real.exp (c * s) := by
    rw [Real.exp_neg]; ring
  rw [hrw, div_le_iff₀ hexppos]
  linarith

/-- A quadratic exponent eventually dominates a linear one. -/
lemma quad_exp_dominates {A : ℝ} (hA : 0 < A) :
    ∀ᶠ u : ℝ in atTop, 4 * A * Real.exp (8 * u) ≤ Real.exp (u ^ 2 / 16 * Real.log 2) := by
  set X : ℝ := max (Real.log (4 * A)) 0 with hX
  have hXnn : 0 ≤ X := le_max_right _ _
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (16 * (X + 8) / Real.log 2)] with u hu1 hu2
  have hstep : X + 8 ≤ u * Real.log 2 / 16 := by
    rw [div_le_iff₀ hlog2] at hu2
    linarith
  have hquad : Real.log (4 * A) + 8 * u ≤ u ^ 2 / 16 * Real.log 2 := by
    have h1 : u * (X + 8) ≤ u * (u * Real.log 2 / 16) :=
      mul_le_mul_of_nonneg_left hstep (by linarith)
    have h2 : X + 8 * u ≤ u * (X + 8) := by nlinarith
    have h3 : Real.log (4 * A) ≤ X := le_max_left _ _
    have h4 : u * (u * Real.log 2 / 16) = u ^ 2 / 16 * Real.log 2 := by ring
    linarith
  have hexp : Real.exp (Real.log (4 * A) + 8 * u) ≤ Real.exp (u ^ 2 / 16 * Real.log 2) :=
    Real.exp_le_exp.mpr hquad
  rwa [Real.exp_add, Real.exp_log (by positivity)] at hexp

/-- The total number of prescribed edges is controlled by the total weight. -/
lemma edgeCount_sum_le (r Q n : ℕ) (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : IsPacking r Q z)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)
      ≤ (∑ τ ∈ admTypes r Q, z τ) * Mval r n ^ 2 := by
  have hS : Sval r n = Mval r n ^ 2 := Sval_eq_Mval_sq r n
  calc ∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)
      ≤ ∑ τ ∈ admTypes r Q, z τ * Mval r n ^ 2 := by
        refine Finset.sum_le_sum fun τ hτ => ?_
        rw [edgeCount]
        have hnn : (0:ℝ) ≤ (1 - ρ) * z τ * Sval r n := by
          have h1 : (0:ℝ) ≤ 1 - ρ := by linarith
          have h2 : (0:ℝ) ≤ Sval r n := by rw [hS]; positivity
          exact mul_nonneg (mul_nonneg h1 (hz.1 τ)) h2
        have hfl := Nat.floor_le hnn
        have hle : (1 - ρ) * z τ * Sval r n ≤ z τ * Mval r n ^ 2 := by
          rw [hS]
          nlinarith [mul_nonneg (mul_nonneg hρ0.le (hz.1 τ))
            (by positivity : (0:ℝ) ≤ Mval r n ^ 2)]
        linarith
    _ = (∑ τ ∈ admTypes r Q, z τ) * Mval r n ^ 2 := by rw [Finset.sum_mul]

/-- Eventually the logarithm is dominated by the basic scale. -/
lemma log_le_Mval_eventually (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ Mval r n := by
  have hpow := powers_dominate_logs ((1 : ℝ) / r) (by positivity) 2
  have hnat : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / r) / (Real.log n) ^ (2 : ℝ)) atTop atTop :=
    hpow.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually_ge_atTop 1, eventually_ge_atTop 2] with n hn hn2
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlogpos : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  have hlog2 : (0 : ℝ) < (Real.log n) ^ (2 : ℝ) := Real.rpow_pos_of_pos hlogpos 2
  have hge : (Real.log n) ^ (2 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / r) := by
    have := (le_div_iff₀ hlog2).mp hn
    linarith
  have hsq : (Real.log n) ^ (2 : ℝ) = Real.log n * Real.log n := by
    rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [hsq] at hge
  rw [Mval, le_div_iff₀ hlogpos]
  exact hge

set_option maxHeartbeats 1000000 in
/-- Eventual union bound over all bad events. -/
lemma union_bound_eventually (r Q : ℕ) (hr : 3 ≤ r)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : IsPacking r Q z) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      ((∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)) +
            (((realizationVertices r Q n).powersetCard 2).card : ℝ)) *
            Real.exp (-(ρ ^ 2 * Dval r n) / 32) +
          ((∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)) +
            (((realizationVertices r Q n).powersetCard 2).card : ℝ)) ^ 2 *
            (Real.exp 1 * kapVal r n / (Real.log ((1 - ρ / 2) * Dval r n)) ^ 2) ^
              ((Real.log ((1 - ρ / 2) * Dval r n)) ^ 2) < 1 := by
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := by positivity
  set V : ℝ := ∑ τ ∈ admTypes r Q, z τ with hV
  have hVnn : 0 ≤ V := Finset.sum_nonneg fun τ _ => hz.1 τ
  set A : ℝ := V + (Q : ℝ) ^ 2 + 1 with hA
  have hApos : (0 : ℝ) < A := by rw [hA]; linarith
  set c : ℝ := ρ ^ 2 / 32 with hc
  have hcpos : (0 : ℝ) < c := by rw [hc]; positivity
  have hγ : Real.log (1 - ρ / 2) < 0 := Real.log_neg (by linarith) (by linarith)
  set γ : ℝ := Real.log (1 - ρ / 2) with hγdef
  have hM := Mval_tendsto_atTop r (by omega)
  have hlogM : Filter.Tendsto (fun n : ℕ => Real.log (Mval r n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hM
  -- the two decay statements, transported to the scale `n`
  have hdecay : ∀ᶠ n : ℕ in atTop,
      A * (Real.sqrt (Mval r n)) ^ 8 * Real.exp (-(c * Real.sqrt (Mval r n))) ≤ 1 / 4 := by
    obtain ⟨S₀, hS₀⟩ := (poly_mul_exp_neg_le hcpos hApos.le).exists_forall_of_atTop
    filter_upwards [hM.eventually_ge_atTop (S₀ ^ 2 + 1), hM.eventually_ge_atTop 1] with n hMn hM1
    refine hS₀ _ ?_
    have hs : S₀ ≤ Real.sqrt (Mval r n) := by
      rcases le_or_gt S₀ 0 with h | h
      · exact le_trans h (Real.sqrt_nonneg _)
      · have h2 : Real.sqrt (S₀ ^ 2) ≤ Real.sqrt (Mval r n) := Real.sqrt_le_sqrt (by linarith)
        rwa [Real.sqrt_sq h.le] at h2
    exact hs
  have hquad : ∀ᶠ n : ℕ in atTop,
      4 * A ^ 2 * Real.exp (8 * Real.log (Mval r n))
        ≤ Real.exp ((Real.log (Mval r n)) ^ 2 / 16 * Real.log 2) := by
    obtain ⟨U₀, hU₀⟩ := (quad_exp_dominates (by positivity : (0:ℝ) < A ^ 2)).exists_forall_of_atTop
    filter_upwards [hlogM.eventually_ge_atTop U₀] with n hun
    exact hU₀ _ hun
  filter_upwards [hdecay, hquad,
    log_le_Mval_eventually r (by omega),
    hM.eventually_ge_atTop 1,
    hM.eventually_ge_atTop ((2 * Real.exp 1) ^ 4),
    hlogM.eventually_ge_atTop (4 * (-γ) + 4),
    eventually_ge_atTop 2] with n hdec hqd hlogn hM1 hMe hu hn2
  -- notation
  set M : ℝ := Mval r n with hMdef
  set u : ℝ := Real.log M with hudef
  have hMpos : (0 : ℝ) < M := by linarith
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlogn_pos : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  have hsqrtM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hMpos.le
  have hsqrtpos : (0 : ℝ) < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  -- the size of the ground set
  have hP : ((((realizationVertices r Q n).powersetCard 2).card : ℝ)) ≤ (Q : ℝ) ^ 2 * M ^ 4 := by
    have hcard : (((realizationVertices r Q n).powersetCard 2).card : ℝ)
        = (((realizationVertices r Q n).card.choose 2 : ℕ) : ℝ) := by
      rw [Finset.card_powersetCard]
    have hchoose : ((((realizationVertices r Q n).card).choose 2 : ℕ) : ℝ)
        ≤ ((realizationVertices r Q n).card : ℝ) ^ 2 := by
      have hcast : ((((realizationVertices r Q n).card).choose 2 : ℕ) : ℝ)
          = ((realizationVertices r Q n).card : ℝ) *
            (((realizationVertices r Q n).card : ℝ) - 1) / 2 := by
        exact_mod_cast Nat.cast_choose_two (K := ℝ) _
      rw [hcast]
      nlinarith [(by positivity : (0:ℝ) ≤ ((realizationVertices r Q n).card : ℝ))]
    have hV2 : ((realizationVertices r Q n).card : ℝ) ≤ (Q : ℝ) * M ^ 2 := by
      have h1 := card_realizationVertices_le r Q n
      have hlogne : Real.log n ≠ 0 := ne_of_gt hlogn_pos
      have h2 : (n : ℝ) ^ ((1 : ℝ) / r) = M * Real.log n := by
        rw [hMdef, Mval, div_mul_cancel₀ _ hlogne]
      rw [h2] at h1
      have h3 : (Q : ℝ) * (M * Real.log n) ≤ (Q : ℝ) * (M * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogn hMpos.le) (by positivity)
      calc ((realizationVertices r Q n).card : ℝ) ≤ (Q : ℝ) * (M * Real.log n) := h1
        _ ≤ (Q : ℝ) * (M * M) := h3
        _ = (Q : ℝ) * M ^ 2 := by ring
    rw [hcard]
    calc ((((realizationVertices r Q n).card).choose 2 : ℕ) : ℝ)
        ≤ ((realizationVertices r Q n).card : ℝ) ^ 2 := hchoose
      _ ≤ ((Q : ℝ) * M ^ 2) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) hV2
      _ = (Q : ℝ) ^ 2 * M ^ 4 := by ring
  have hT : ∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ) ≤ V * M ^ 2 :=
    edgeCount_sum_le r Q n z hz hρ0 hρ1
  have hTP : (∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)) +
      ((((realizationVertices r Q n).powersetCard 2).card : ℝ)) ≤ A * M ^ 4 := by
    have hM24 : M ^ 2 ≤ M ^ 4 := pow_le_pow_right₀ hM1 (by norm_num)
    have hVM : V * M ^ 2 ≤ V * M ^ 4 := mul_le_mul_of_nonneg_left hM24 hVnn
    have : V * M ^ 4 + (Q : ℝ) ^ 2 * M ^ 4 ≤ A * M ^ 4 := by
      rw [hA]; nlinarith [(by positivity : (0:ℝ) ≤ M ^ 4)]
    linarith
  have hTPnn : (0 : ℝ) ≤ (∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)) +
      ((((realizationVertices r Q n).powersetCard 2).card : ℝ)) := by positivity
  -- the first term
  have hterm1 : ((∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)) +
      ((((realizationVertices r Q n).powersetCard 2).card : ℝ))) *
      Real.exp (-(ρ ^ 2 * Dval r n) / 32) ≤ 1 / 4 := by
    have hDval : Dval r n = Real.sqrt M := rfl
    have hexpeq : Real.exp (-(ρ ^ 2 * Dval r n) / 32) = Real.exp (-(c * Real.sqrt M)) := by
      rw [hDval, hc]; congr 1; ring
    have hM4 : M ^ 4 = (Real.sqrt M) ^ 8 := by
      rw [show (Real.sqrt M) ^ 8 = ((Real.sqrt M) * (Real.sqrt M)) ^ 4 by ring, hsqrtM]
    rw [hexpeq]
    calc ((∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)) +
          ((((realizationVertices r Q n).powersetCard 2).card : ℝ))) *
          Real.exp (-(c * Real.sqrt M))
        ≤ (A * M ^ 4) * Real.exp (-(c * Real.sqrt M)) :=
          mul_le_mul_of_nonneg_right hTP (Real.exp_pos _).le
      _ = A * (Real.sqrt M) ^ 8 * Real.exp (-(c * Real.sqrt M)) := by rw [hM4]
      _ ≤ 1 / 4 := hdec
  -- the second term
  have hlogsqrt : Real.log (Real.sqrt M) = u / 2 := by
    rw [Real.log_sqrt hMpos.le, hudef]
  have hKeq : Real.log ((1 - ρ / 2) * Dval r n) = γ + u / 2 := by
    have hDval : Dval r n = Real.sqrt M := rfl
    rw [hDval, Real.log_mul (by linarith) (ne_of_gt hsqrtpos), hlogsqrt, hγdef]
  set K : ℝ := (Real.log ((1 - ρ / 2) * Dval r n)) ^ 2 with hKdef
  have hu4 : u / 4 ≤ γ + u / 2 := by linarith
  have hu4pos : (0 : ℝ) < u / 4 := by linarith
  have hKge : u ^ 2 / 16 ≤ K := by
    rw [hKdef, hKeq]
    have := pow_le_pow_left₀ hu4pos.le hu4 2
    calc u ^ 2 / 16 = (u / 4) ^ 2 := by ring
      _ ≤ (γ + u / 2) ^ 2 := this
  have hK1 : (1 : ℝ) ≤ K := by
    have hu1 : (1 : ℝ) ≤ u / 4 := by linarith
    have h1 : (1 : ℝ) ≤ (u / 4) ^ 2 := one_le_pow₀ hu1
    have h2 : (u / 4) ^ 2 = u ^ 2 / 16 := by ring
    rw [h2] at h1
    linarith
  have hKpos : (0 : ℝ) < K := by linarith
  -- the base of the large-deviation factor is at most `1/2`
  have hbase : Real.exp 1 * kapVal r n / K ≤ 1 / 2 := by
    have hkap : kapVal r n = 1 / Real.sqrt (Real.sqrt M) := kapVal_eq_sqrt r n hMpos.le
    have hqq : (2 * Real.exp 1) ≤ Real.sqrt (Real.sqrt M) := by
      have h1 : Real.sqrt ((2 * Real.exp 1) ^ 4) ≤ Real.sqrt M := Real.sqrt_le_sqrt hMe
      have h2 : Real.sqrt ((2 * Real.exp 1) ^ 4) = (2 * Real.exp 1) ^ 2 := by
        rw [show ((2 * Real.exp 1) ^ 4 : ℝ) = ((2 * Real.exp 1) ^ 2) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
      rw [h2] at h1
      have h3 : Real.sqrt (((2 * Real.exp 1)) ^ 2) ≤ Real.sqrt (Real.sqrt M) :=
        Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (by positivity)] at h3
    have hqpos : (0 : ℝ) < Real.sqrt (Real.sqrt M) := Real.sqrt_pos.mpr hsqrtpos
    rw [hkap]
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    have hstep : Real.exp 1 * (1 / Real.sqrt (Real.sqrt M)) * 2 ≤ 1 := by
      rw [mul_comm, ← mul_assoc]
      rw [mul_one_div, div_le_one hqpos]
      linarith
    linarith [hstep, hK1]
  have hbasenn : (0 : ℝ) ≤ Real.exp 1 * kapVal r n / K := by
    have : (0 : ℝ) < kapVal r n := Real.rpow_pos_of_pos hMpos _
    positivity
  have hpow : (Real.exp 1 * kapVal r n / K) ^ K ≤ (1 / 2 : ℝ) ^ K :=
    Real.rpow_le_rpow hbasenn hbase hKpos.le
  have hhalf : ((1 : ℝ) / 2) ^ K = Real.exp (-(K * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1/2)]
    congr 1
    rw [show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have hterm2 : ((∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)) +
      ((((realizationVertices r Q n).powersetCard 2).card : ℝ))) ^ 2 *
      (Real.exp 1 * kapVal r n / K) ^ K ≤ 1 / 4 := by
    have hsq : ((∑ τ ∈ admTypes r Q, (edgeCount r Q n ρ z τ : ℝ)) +
        ((((realizationVertices r Q n).powersetCard 2).card : ℝ))) ^ 2 ≤ (A * M ^ 4) ^ 2 :=
      pow_le_pow_left₀ hTPnn hTP 2
    have hMexp : M ^ 8 = Real.exp (8 * u) := by
      have hlogpow : (8 : ℝ) * Real.log M = Real.log (M ^ 8) := by
        rw [Real.log_pow]; push_cast; ring
      rw [hudef, hlogpow, Real.exp_log (by positivity)]
    have h4A : 4 * A ^ 2 * M ^ 8 ≤ Real.exp (K * Real.log 2) := by
      rw [hMexp]
      refine le_trans hqd ?_
      apply Real.exp_le_exp.mpr
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      exact mul_le_mul_of_nonneg_right hKge hlog2.le
    have hstep : (A * M ^ 4) ^ 2 * (1 / 2 : ℝ) ^ K ≤ 1 / 4 := by
      rw [hhalf]
      have hexppos : (0 : ℝ) < Real.exp (K * Real.log 2) := Real.exp_pos _
      have hrw : Real.exp (-(K * Real.log 2)) = 1 / Real.exp (K * Real.log 2) := by
        rw [Real.exp_neg]; ring
      rw [hrw]
      rw [mul_one_div, div_le_iff₀ hexppos]
      have : (A * M ^ 4) ^ 2 = A ^ 2 * M ^ 8 := by ring
      rw [this]
      linarith [h4A]
    refine le_trans (mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hbasenn K)) ?_
    exact le_trans (mul_le_mul_of_nonneg_left hpow (by positivity)) hstep
  linarith

/-- Eventual Delcourt–Postle degree condition. -/
lemma dp_degree_condition_eventually (r : ℕ) (hr : 3 ≤ r) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (Dq : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      0 < Dval r n ∧ Dq ≤ (1 - ρ / 2) * Dval r n ∧
      1 ≤ (Real.log ((1 - ρ / 2) * Dval r n)) ^ 2 ∧
      (1 + ((1 - ρ / 2) * Dval r n) ^ (-(1 : ℝ) / (20 * (1 + r.choose 2)))) *
          ((1 - ρ / 2) * Dval r n) ≤ (1 - ρ / 4) * Dval r n := by
  -- Dval tends to infinity since Mval tends to infinity
  have hMval := Mval_tendsto_atTop r (by omega : 1 ≤ r)
  have hDval : Tendsto (fun n => Dval r n) atTop atTop := by
    unfold Dval
    exact Real.tendsto_sqrt_atTop.comp hMval
  -- Define x = (1 - ρ/2) * Dval
  let coeff := (1 - ρ / 2)
  have hcoeff_pos : 0 < coeff := by
    simp only [coeff]
    linarith
  -- Eventually Dval > 0
  have h0 : ∀ᶠ n in atTop, 0 < Dval r n := by
    exact hDval.eventually_gt_atTop 0
  -- Eventually Dq ≤ coeff * Dval
  have h1 : ∀ᶠ n in atTop, Dq ≤ coeff * Dval r n := by
    have h := Filter.Tendsto.atTop_mul_const hcoeff_pos hDval
    rw [Filter.eventually_atTop]
    obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp h Dq
    exact ⟨N, fun n hn => by linarith [hN n hn]⟩
  -- Condition 3: 1 ≤ (log(coeff * Dval))^2
  -- Eventually coeff * Dval ≥ e, so log(coeff * Dval) ≥ 1
  have h3 : ∀ᶠ n in atTop, 1 ≤ (Real.log (coeff * Dval r n)) ^ 2 := by
    have hexp := Real.tendsto_exp_atTop
    have hx_tendsto : Tendsto (fun n => coeff * Dval r n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hcoeff_pos hDval
    have h := hx_tendsto.eventually_ge_atTop (Real.exp 1)
    filter_upwards [h] with n hn
    have hlog : Real.log (coeff * Dval r n) ≥ 1 := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (by positivity) hn
    nlinarith
  -- Condition 4: (1 + x^(-c)) * x ≤ (1 - ρ/4) * Dval
  -- where x = coeff * Dval and c = 1/(20*(1+r.choose 2))
  -- Equivalently: x^(1-c) ≤ (ρ/4) * Dval
  -- i.e., coeff^(1-c) * Dval^(1-c) ≤ (ρ/4) * Dval
  -- i.e., coeff^(1-c) * Dval^(-c) ≤ ρ/4
  let c := (1 : ℝ) / (20 * (1 + (r.choose 2)))
  have hc_pos : 0 < c := by
    simp only [c]
    positivity
  have hc_lt_1 : c < 1 := by
    simp only [c]
    have h1 : (1 : ℝ) ≤ r.choose 2 := by
      norm_cast
      exact Nat.choose_pos (by omega : 2 ≤ r)
    have h2 : (20 : ℝ) * (1 + (r.choose 2)) ≥ 20 := by linarith
    rw [div_lt_iff₀] <;> linarith
  -- Dval^(-c) → 0 as Dval → ∞
  have hDval_negc : Tendsto (fun n => Dval r n ^ (-c)) atTop (nhds 0) := by
    have h := tendsto_rpow_atTop hc_pos
    have h2 := h.comp hDval
    have hDval_nonneg : ∀ n, 0 ≤ Dval r n := by
      intro n
      unfold Dval
      exact Real.sqrt_nonneg _
    have heq : ∀ n, Dval r n ^ (-c) = (Dval r n ^ c)⁻¹ := by
      intro n
      exact Real.rpow_neg (hDval_nonneg n) c
    simp_rw [heq]
    exact Tendsto.inv_tendsto_atTop h2
  -- Eventually coeff^(1-c) * Dval^(-c) ≤ ρ/4
  have h4_aux : ∀ᶠ n in atTop, coeff ^ (1 - c) * (Dval r n) ^ (-c) ≤ ρ / 4 := by
    have hcoeff_rpow : Tendsto (fun _ : ℕ => coeff ^ (1 - c)) atTop (nhds (coeff ^ (1 - c))) :=
      tendsto_const_nhds
    have hprod : Tendsto (fun n => coeff ^ (1 - c) * (Dval r n) ^ (-c)) atTop (nhds (coeff ^ (1 - c) * 0)) :=
      Filter.Tendsto.mul hcoeff_rpow hDval_negc
    simp only [mul_zero] at hprod
    exact hprod.eventually (ge_mem_nhds (by linarith : ρ / 4 > 0))
  -- Combine all conditions
  have h4 : ∀ᶠ n in atTop, (1 + ((1 - ρ / 2) * Dval r n) ^ (-(1 : ℝ) / (20 * (1 + ↑(r.choose 2))))) *
      ((1 - ρ / 2) * Dval r n) ≤ (1 - ρ / 4) * Dval r n := by
    -- Note: -(1 : ℝ) / (20 * (1 + r.choose 2)) = -c
    have hexp_eq : ∀ n, ((1 - ρ / 2) * Dval r n) ^ (-(1 : ℝ) / (20 * (1 + ↑(r.choose 2)))) =
        ((1 - ρ / 2) * Dval r n) ^ (-c) := by
      intro n
      simp only [c]
      rw [neg_div]
    filter_upwards [h4_aux, h0] with n hn hnpos
    have hxn_nonneg : 0 ≤ (1 - ρ / 2) * Dval r n := by
      apply mul_nonneg
      · linarith
      · exact Real.sqrt_nonneg _
    -- x = coeff * Dval
    let x := (1 - ρ / 2) * Dval r n
    -- We have coeff^(1-c) * Dval^(-c) ≤ ρ/4
    -- Need: (1 + x^(-c)) * x ≤ (1 - ρ/4) * Dval
    have hx : x = coeff * Dval r n := rfl
    -- x^(1-c) = coeff^(1-c) * Dval^(1-c)
    have hx_rpow : x ^ (1 - c) = coeff ^ (1 - c) * (Dval r n) ^ (1 - c) := by
      rw [hx]
      exact Real.mul_rpow (le_of_lt hcoeff_pos) (Real.sqrt_nonneg _)
    -- Dval^(1-c) = Dval^(-c) * Dval
    have hDval_rpow : (Dval r n) ^ (1 - c) = (Dval r n) ^ (-c) * (Dval r n) := by
      rw [← Real.rpow_add_one (ne_of_gt hnpos)]
      congr 1
      ring
    -- Now prove the main inequality
    -- LHS = (1 + x^(-c)) * x = x + x^(1-c)
    -- We need x + x^(1-c) ≤ (1 - ρ/4) * Dval
    have hx_pos : 0 < x := mul_pos hcoeff_pos hnpos
    rw [hexp_eq]
    -- (1 + x^(-c)) * x = x + x^(1-c)
    have hlhs : (1 + x ^ (-c)) * x = x + x ^ (1 - c) := by
      have h1 : x ^ (-c) * x = x ^ (1 - c) := by
        have := Real.rpow_add_one (ne_of_gt hx_pos) (-c)
        rw [show -c + 1 = 1 - c by ring] at this
        exact this.symm
      linarith [h1]
    rw [hlhs, hx_rpow, hDval_rpow]
    -- coeff * Dval + coeff^(1-c) * Dval^(-c) * Dval ≤ (1 - ρ/4) * Dval
    -- Dval * (coeff + coeff^(1-c) * Dval^(-c)) ≤ (1 - ρ/4) * Dval
    have hfactor : Dval r n * (coeff + coeff ^ (1 - c) * (Dval r n) ^ (-c)) ≤
        (1 - ρ / 4) * Dval r n := by
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hnpos)
      -- coeff + coeff^(1-c) * Dval^(-c) ≤ 1 - ρ/4
      have : coeff + coeff ^ (1 - c) * (Dval r n) ^ (-c) ≤ coeff + ρ / 4 := by
        have := add_le_add_left hn coeff
        linarith
      calc coeff + coeff ^ (1 - c) * (Dval r n) ^ (-c) ≤ coeff + ρ / 4 := this
        _ = (1 - ρ / 2) + ρ / 4 := by simp [coeff]
        _ = 1 - ρ / 4 := by ring
    linarith
  exact Filter.eventually_and.mpr ⟨h0, Filter.eventually_and.mpr ⟨h1, Filter.eventually_and.mpr ⟨h3, h4⟩⟩⟩

/-- Probabilistic matching core of finite realization.  For all sufficiently
large scales, one can choose the prescribed rounded number of sets of every
admissible type so that distinct chosen sets meet in at most one prime.

This is the sole place where the Delcourt–Postle black box and the concentration
estimates are used; `finite_realization_of_exact_type_counts` performs all
remaining deterministic readout. -/
lemma typed_linear_selection_eventually (r Q : ℕ) (hr : 3 ≤ r)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : IsPacking r Q z)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∃ H : Finset (Finset ℕ),
      (∀ E ∈ H, ∃ τ ∈ admTypes r Q, E ∈ realizationTypeFamily r Q n τ) ∧
      (∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1) ∧
      (∀ τ ∈ admTypes r Q,
        (H.filter fun E => E ∈ realizationTypeFamily r Q n τ).card =
          ⌊(1 - ρ) * z τ * Sval r n⌋₊) := by
  obtain ⟨Dq, hDq⟩ := typed_selection_of_hypotheses r Q hr hρ0 hρ1
  have hM := Mval_tendsto_atTop r (by omega)
  filter_upwards [Dval_le_family_card_eventually r Q hr,
    pair_degree_bound r Q hr z hz hρ0 hρ1,
    codegree_token_pair_eventually r Q hr,
    codegree_pair_pair_eventually r Q hr z hz hρ0 hρ1,
    union_bound_eventually r Q hr z hz hρ0 hρ1,
    dp_degree_condition_eventually r hr hρ0 hρ1 Dq,
    hM.eventually_gt_atTop 0] with n hfam hpair hcod1 hcod2 hfail hdp hMpos
  obtain ⟨hD0, hDq', hlog, hgap⟩ := hdp
  have hκ : 0 < kapVal r n := Real.rpow_pos_of_pos hMpos _
  exact hDq n (edgeCount r Q n ρ z) (Dval r n) (kapVal r n) hD0 hDq' hκ hlog hfam
    (realizationTypeFamily_edges r Q n) hpair hcod1 hcod2 hfail hgap

/-- Given `r ≥ 3`, `Q ≥ 1`, a level-`Q` packing `z` of value `V`, and `0 < ρ < 1/2`,
for all sufficiently large `n` there is a linear `r`-uniform prime hypergraph
`Hₙ` with edge-products at most `n`, whose vertices are bounded by `Q · n^{1/r}`,
and with `|Hₙ| ≥ (1-ρ) V S - |𝒜_{r,Q}|`. -/
theorem finite_realization (r Q : ℕ) (hr : 3 ≤ r)
    (z : (Fin (NQ Q) → ℕ) → ℝ) (hz : IsPacking r Q z) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∃ H : Finset (Finset ℕ),
      IsLinearPrimeHG r n H ∧
      (∀ p ∈ vertices H, (p : ℝ) ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / r)) ∧
      ((1 - ρ) * valQ r Q z * Sval r n - ((admTypes r Q).card : ℝ) ≤ (H.card : ℝ)) := by
  filter_upwards [typed_linear_selection_eventually r Q hr z hz hρ0 hρ1,
    Filter.eventually_ge_atTop 1] with n hn hnpos
  obtain ⟨H, htyped, hlin, hcount⟩ := hn
  refine ⟨H, finite_realization_of_exact_type_counts (by omega) hnpos z ?_ ?_ htyped hlin hcount⟩
  · exact fun τ => hz.1 τ
  · linarith

/-- Any distinct-factor `k`-primitive subset of `{1,…,n}` has at most `Fkdist k n`
elements. -/
theorem card_le_Fkdist {k n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n)
    (hprim : DistPrimitive k A) : A.card ≤ Fkdist k n := by
  refine le_csSup ⟨n, ?_⟩ ⟨A, hA, hprim, rfl⟩
  rintro m ⟨B, hB, -, rfl⟩
  simpa using Finset.card_le_card hB

/-- The supremum defining `Fkrep k n` is attained. -/
theorem exists_repPrimitive_card_eq_Fkrep (k n : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ RepPrimitive k A ∧ A.card = Fkrep k n := by
  have hne : {m | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ RepPrimitive k A ∧ A.card = m}.Nonempty :=
    ⟨0, ∅, by simp, by simp [RepPrimitive], by simp⟩
  have hbdd : BddAbove {m | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ RepPrimitive k A ∧ A.card = m} := by
    refine ⟨n, ?_⟩
    rintro m ⟨B, hB, -, rfl⟩
    simpa using Finset.card_le_card hB
  obtain ⟨A, hA, hprim, hcard⟩ := Nat.sSup_mem hne hbdd
  exact ⟨A, hA, hprim, hcard⟩

/-- If a set contains no `k+1` distinct elements `a, b₁, …, b_k` with `a ∣ b₁⋯b_k`,
then it is distinct-factor `k`-primitive. -/
theorem distPrimitive_of_not_exists {k : ℕ} {A : Finset ℕ}
    (h : ¬ ∃ a ∈ A, ∃ b : Fin k → ℕ,
      (∀ i, b i ∈ A) ∧ (∀ i, b i ≠ a) ∧ Function.Injective b ∧ a ∣ ∏ i, b i) :
    DistPrimitive k A := by
  intro a ha B hB hBcard hdvd
  refine h ⟨a, ha, B.orderEmbOfFin hBcard, ?_, ?_, (B.orderEmbOfFin hBcard).injective, ?_⟩
  · exact fun i => Finset.mem_of_mem_erase (hB (B.orderEmbOfFin_mem hBcard i))
  · exact fun i => Finset.ne_of_mem_erase (hB (B.orderEmbOfFin_mem hBcard i))
  · have hBimg : B = Finset.image (B.orderEmbOfFin hBcard) Finset.univ := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · exact Finset.image_subset_iff.mpr fun i _ => B.orderEmbOfFin_mem hBcard i
      · rw [Finset.card_image_of_injective _ (B.orderEmbOfFin hBcard).injective,
          Finset.card_fin, hBcard]
    rwa [hBimg, Finset.prod_image (fun i _ j _ h => (B.orderEmbOfFin hBcard).injective h)] at hdvd

/-- The maximal distinct-factor `k`-primitive size in `[n]` is attained by some
subset `A ⊆ [n]`. -/
theorem Fkdist_achieved (k n : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ DistPrimitive k A ∧ A.card = Fkdist k n := by
  have hne : {m | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ DistPrimitive k A ∧ A.card = m}.Nonempty :=
    ⟨0, ∅, by simp, by intro a ha; simp at ha, by simp⟩
  have hbdd : BddAbove {m | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ DistPrimitive k A ∧ A.card = m} := by
    refine ⟨n, ?_⟩
    rintro m ⟨A, hA, _, rfl⟩
    calc A.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hA
      _ = n := by simp
  exact Nat.sSup_mem hne hbdd

/-- For every `η > 0` there is a family `H` of linear `(k+1)`-uniform prime
hypergraphs such that, for all large `n`, `F_k^{dist}(n) ≤ π(n) + 2η S + |H n|`. -/
theorem upper_bound_family (k : ℕ) (hk : 2 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∃ H : ℕ → Finset (Finset ℕ), (∀ n, IsLinearPrimeHG (k + 1) n (H n)) ∧
      ∀ᶠ n in atTop, (Fkdist k n : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η * Sr k n) + (H n).card := by
  have hEx : ∀ᶠ n in atTop, ∃ He : Finset (Finset ℕ), IsLinearPrimeHG (k+1) n He ∧
      (Fkdist k n : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η * Sr k n) + He.card := by
    filter_upwards [extraction k hk η hη] with n hextr
    obtain ⟨A, hAsub, hAprim, hAcard⟩ := Fkdist_achieved k n
    obtain ⟨Aeasy, Ahard, T, hunion, hdisj, heasy, hTprops, hTcap⟩ := hextr A hAsub hAprim
    have hAhardsub : Ahard ⊆ A := by rw [hunion]; exact Finset.subset_union_right
    refine ⟨Ahard.image T, ⟨?_, ?_⟩, ?_⟩
    · intro E hE
      rw [Finset.mem_image] at hE
      obtain ⟨a, haH, rfl⟩ := hE
      obtain ⟨hTc, hTp, hTprod, han⟩ := hTprops a haH
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hAsub (hAhardsub haH))).1
      refine ⟨hTc, ?_, le_trans hTprod han⟩
      intro p hp
      obtain ⟨hpp, hpa⟩ := hTp p hp
      exact ⟨hpp, le_trans (Nat.le_of_dvd (by omega) hpa) han⟩
    · intro E hE E' hE' hne
      rw [Finset.mem_image] at hE hE'
      obtain ⟨a, haH, rfl⟩ := hE
      obtain ⟨b, hbH, rfl⟩ := hE'
      exact hTcap a haH b hbH (fun h => hne (by rw [h]))
    · have hinj : Set.InjOn T Ahard := by
        intro a ha b hb hTab
        by_contra hab
        have h1 : (k + 1) ≤ (T a ∩ T b).card := by
          rw [hTab, Finset.inter_self]; exact le_of_eq (hTprops b hb).1.symm
        have h2 := hTcap a ha b hb hab
        omega
      have hcardimg : (Ahard.image T).card = Ahard.card := Finset.card_image_of_injOn hinj
      have hAunion : A.card = Aeasy.card + Ahard.card := by
        rw [hunion, Finset.card_union_of_disjoint hdisj]
      rw [← hAcard, hAunion, hcardimg]
      push_cast
      linarith [heasy]
  classical
  refine ⟨fun n => if h : (∃ He : Finset (Finset ℕ), IsLinearPrimeHG (k+1) n He ∧
      (Fkdist k n : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η * Sr k n) + He.card) then h.choose else ∅,
    ?_, ?_⟩
  · intro n
    by_cases h : (∃ He : Finset (Finset ℕ), IsLinearPrimeHG (k+1) n He ∧
        (Fkdist k n : ℝ) ≤ (Nat.primeCounting n : ℝ) + 2 * (η * Sr k n) + He.card)
    · simp only [dif_pos h]; exact h.choose_spec.1
    · simp only [dif_neg h]
      refine ⟨?_, ?_⟩ <;> intro E hE <;> simp at hE
  · filter_upwards [hEx] with n hn
    simp only [dif_pos hn]
    exact hn.choose_spec.2

/-- For every `ε > 0`, for all sufficiently large `n`,
  `F_k^{dist}(n) ≤ π(n) + (Λ_{k+1} + ε) S_r(n)`. -/
theorem upper_bound (k : ℕ) (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Fkdist k n : ℝ) ≤ (Nat.primeCounting n : ℝ) + (Lam (k + 1) + ε) * Sr k n := by
  obtain ⟨Cr, hCr0, hCr⟩ := tail_edge_bound k hk
  obtain ⟨c, hc0, hc1, hc⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ c ^ (-2 : ℤ) * Lam (k+1) < Lam (k+1) + ε/4 := by
    have hΛ : 0 ≤ Lam (k+1) := Lam_nonneg _
    set Λ := Lam (k+1) with hΛdef
    set d := Real.sqrt (Λ / (Λ + ε/4)) with hd
    have hden : 0 < Λ + ε/4 := by positivity
    have hratio : Λ / (Λ + ε/4) < 1 := by rw [div_lt_one hden]; linarith
    have hd0 : 0 ≤ d := Real.sqrt_nonneg _
    have hd1 : d < 1 := by
      rw [hd, show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by positivity) hratio
    refine ⟨(d+1)/2, by positivity, by linarith, ?_⟩
    have hc2 : 0 < ((d+1)/2)^2 := by positivity
    have hcsq : Λ / (Λ + ε/4) < ((d+1)/2)^2 := by
      have hdsq : d^2 = Λ / (Λ + ε/4) := Real.sq_sqrt (by positivity)
      nlinarith [hd0, hd1]
    rw [zpow_neg, inv_mul_eq_div]
    have hcsq' : Λ < ((d+1)/2)^2 * (Λ + ε/4) := by rw [div_lt_iff₀ hden] at hcsq; linarith
    exact (div_lt_iff₀ hc2).mpr (by nlinarith [hcsq'])
  obtain ⟨δ, hδ0, hδ1, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ Cr * δ ^ (((k:ℝ)-1)/(k:ℝ)) < ε/4 := by
    have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
    have hβ : 0 < ((k:ℝ)-1)/(k:ℝ) := by apply div_pos <;> linarith
    have htend : Tendsto (fun δ:ℝ => Cr * δ ^ (((k:ℝ)-1)/(k:ℝ))) (𝓝[>] 0) (nhds 0) := by
      have h : Tendsto (fun x:ℝ => x ^ (((k:ℝ)-1)/(k:ℝ))) (𝓝[>] (0:ℝ)) (nhds 0) := by
        have hc' := (Real.continuousAt_rpow_const 0 (((k:ℝ)-1)/(k:ℝ)) (Or.inr (le_of_lt hβ))).tendsto
        rw [Real.zero_rpow (ne_of_gt hβ)] at hc'
        exact hc'.mono_left nhdsWithin_le_nhds
      simpa using h.const_mul Cr
    have hev2 : ∀ᶠ δ in 𝓝[>] (0:ℝ), Cr * δ ^ (((k:ℝ)-1)/(k:ℝ)) < ε/4 := htend (Iio_mem_nhds (by positivity))
    have hpos : ∀ᶠ δ in 𝓝[>] (0:ℝ), (0:ℝ) < δ := eventually_of_mem self_mem_nhdsWithin (fun x hx => hx)
    have hlt1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < 1 :=
      (eventually_of_mem (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)) (fun x hx => hx)).filter_mono nhdsWithin_le_nhds
    obtain ⟨δ, ⟨hδlt, hδ0⟩, hδ1⟩ := ((hev2.and hpos).and hlt1).exists
    exact ⟨δ, hδ0, hδ1, hδlt⟩
  obtain ⟨Q, hQ, hmesh, hcut⟩ : ∃ Q : ℕ, 1 ≤ Q ∧ (1:ℝ) / 2 ^ Q ≤ (1 - c) * δ ∧ ((c : ℝ) / Q) ^ ((1 : ℝ) / (k : ℝ)) ≤ δ := by
    have hy : 0 < (1:ℝ)/(k:ℝ) := by positivity
    have htend1 : Tendsto (fun Q:ℕ => (1:ℝ)/2^Q) atTop (nhds 0) := by
      simpa [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)
    have htend2 : Tendsto (fun Q:ℕ => ((c:ℝ)/(Q:ℝ)) ^ ((1:ℝ)/(k:ℝ))) atTop (nhds 0) := by
      have hinner : Tendsto (fun Q:ℕ => (c:ℝ)/(Q:ℝ)) atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat c
      have hc' := (Real.continuousAt_rpow_const 0 ((1:ℝ)/(k:ℝ)) (Or.inr (le_of_lt hy))).tendsto
      rw [Real.zero_rpow (ne_of_gt hy)] at hc'
      exact hc'.comp hinner
    have he1 : ∀ᶠ Q:ℕ in atTop, (1:ℝ)/2^Q ≤ (1-c)*δ := htend1.eventually_le_const (mul_pos (by linarith) hδ0)
    have he2 : ∀ᶠ Q:ℕ in atTop, ((c:ℝ)/(Q:ℝ)) ^ ((1:ℝ)/(k:ℝ)) ≤ δ := htend2.eventually_le_const hδ0
    obtain ⟨Q, ⟨hQ1, hQ2⟩, hQ3⟩ := ((he1.and he2).and (eventually_ge_atTop 1)).exists
    exact ⟨Q, hQ3, hQ1, hQ2⟩
  obtain ⟨H, hHlin, hHfam⟩ := upper_bound_family k hk (ε/16) (by positivity)
  have hcen := central_bound k hk c hc0 hc1 Q hQ δ hmesh H hHlin (ε/8) (by positivity)
  have htail := hCr c hc0 hc1 Q hQ δ hδ0 hδ1 hmesh hcut H hHlin
  filter_upwards [hHfam, hcen, htail, eventually_gt_atTop 1] with n hfam hcn htl hn1
  have hsr : 0 < Sr k n := by
    rw [Sr]; exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _)
      (pow_pos (Real.log_pos (by exact_mod_cast hn1)) 2)
  have hsub : centralEdges c Q δ (k+1) n (H n) ⊆ H n := Finset.filter_subset _ _
  have hsplitN := Finset.card_sdiff_add_card_eq_card hsub
  have hsplit : ((H n).card:ℝ) = (centralEdges c Q δ (k+1) n (H n)).card + ((H n) \ centralEdges c Q δ (k+1) n (H n)).card := by
    rw [← hsplitN]; push_cast; ring
  rw [div_le_iff₀ hsr] at hcn htl
  nlinarith [hfam, hsplit, hcn, htl, hc, hδ, hsr,
    mul_le_mul_of_nonneg_right (le_of_lt hc) (le_of_lt hsr),
    mul_le_mul_of_nonneg_right (le_of_lt hδ) (le_of_lt hsr)]

/--
For every `ε > 0`, for all sufficiently large `n`,
`π(n) + (Λ_{k+1} - ε) S_r(n) ≤ F_k^{rep}(n)`.
-/
theorem lower_bound (k : ℕ) (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) + (Lam (k + 1) - ε) * Sr k n ≤ (Fkrep k n : ℝ) := by
  -- Use near_optimal_grid with a small error ε/4 to get Q,z whose value is near Lam.
  obtain ⟨Q, z, hQ, hz, hval⟩ : ∃ Q : ℕ, ∃ z : (Fin (NQ Q) → ℕ) → ℝ, 1 ≤ Q ∧ IsPacking (k + 1) Q z ∧ Lam (k + 1) - ε / 4 < valQ (k + 1) Q z := by
    exact near_optimal_grid _ ( by linarith ) ( by linarith );
  -- Apply finite_realization with small rho to obtain H for each n.
  obtain ⟨rho, hrho⟩ : ∃ rho : ℝ, 0 < rho ∧ rho < 1 / 2 ∧ (1 - rho) * valQ (k + 1) Q z > Lam (k + 1) - ε / 2 := by
    by_cases h₂ : valQ (k + 1) Q z > 0;
    · exact ⟨ Min.min ( 1 / 4 ) ( ( valQ ( k + 1 ) Q z - ( Lam ( k + 1 ) - ε / 2 ) ) / ( 2 * valQ ( k + 1 ) Q z ) ), lt_min ( by norm_num ) ( div_pos ( by linarith ) ( by linarith ) ), lt_of_le_of_lt ( min_le_left _ _ ) ( by norm_num ), by nlinarith [ min_le_right ( 1 / 4 ) ( ( valQ ( k + 1 ) Q z - ( Lam ( k + 1 ) - ε / 2 ) ) / ( 2 * valQ ( k + 1 ) Q z ) ), mul_div_cancel₀ ( valQ ( k + 1 ) Q z - ( Lam ( k + 1 ) - ε / 2 ) ) ( by linarith : ( 2 * valQ ( k + 1 ) Q z ) ≠ 0 ) ] ⟩;
    · exact ⟨ 1 / 4, by norm_num, by norm_num, by linarith ⟩;
  -- By finite_realization, for large n there exists H satisfying the conditions.
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ H : Finset (Finset ℕ), IsLinearPrimeHG (k + 1) n H ∧ (∀ p ∈ vertices H, (p : ℝ) ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / (k + 1))) ∧ ((1 - rho) * valQ (k + 1) Q z * Sr k n - ((admTypes (k + 1) Q).card : ℝ) ≤ (H.card : ℝ)) := by
    convert finite_realization ( k + 1 ) Q ( by linarith ) z hz hrho.1 hrho.2.1 using 1;
    norm_num [ Sval_succ_eq_Sr ];
  -- By linear_construction, AH is repeated-factor k-primitive and has card π(n)-|vertices H|+|H|.
  have hAH : ∀ n ≥ n₀, ∀ H : Finset (Finset ℕ), IsLinearPrimeHG (k + 1) n H → (Fkrep k n : ℝ) ≥ (Nat.primeCounting n : ℝ) - (vertices H).card + H.card := by
    intros n hn H hH
    have hAH_card : (AH n H).card = (Nat.primeCounting n : ℝ) - (vertices H).card + H.card := by
      have := linear_construction k n hk H hH;
      rw [ this.2, Nat.cast_add, Nat.cast_sub ];
      rw [ primeCounting_eq_card ];
      refine Finset.card_le_card ?_;
      exact Finset.biUnion_subset.mpr fun x hx => Finset.subset_iff.mpr fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( hH.1 x hx |>.2.1 y hy |>.2 ) ), hH.1 x hx |>.2.1 y hy |>.1 ⟩;
    refine' hAH_card ▸ mod_cast le_csSup _ _;
    · exact ⟨ _, fun m hm => hm.choose_spec.2.2 ▸ Finset.card_le_card hm.choose_spec.1 ⟩;
    · refine' ⟨ AH n H, _, _, rfl ⟩;
      · intro x hx; simp_all +decide [ AH, compositeSet ] ;
        rcases hx with ( ⟨ hx₁, hx₂ ⟩ | ⟨ a, ha₁, rfl ⟩ ) <;> simp_all +decide [ primesLE ];
        · exact hx₁.2.pos;
        · exact ⟨ Finset.prod_pos fun p hp => Nat.Prime.pos ( by have := hH.1 a ha₁; aesop ), hH.1 a ha₁ |>.2.2 ⟩;
      · exact linear_construction k n hk H hH |>.1;
  -- Bound |vertices H| ≤ (k+1)|H| is too costly; instead use the realization vertex bound and prime counting/PNT to show vertex count is o(S), as Q is fixed and vertices are primes ≤ Q*n^(1/(k+1)).
  have hvertex_bound : ∀ᶠ n in atTop, ∀ H : Finset (Finset ℕ), IsLinearPrimeHG (k + 1) n H → (∀ p ∈ vertices H, (p : ℝ) ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / (k + 1))) → (vertices H).card ≤ (primesIn 0 ((Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / (k + 1)))) := by
    refine' Filter.eventually_atTop.mpr ⟨ 2, fun n hn H hH hH' => _ ⟩ ; simp_all +decide [ primesIn ];
    rw [ primeCounting_eq_card ];
    refine Finset.card_le_card ?_;
    intro p hp; specialize hH' p hp; simp_all +decide [ primesLE ] ;
    exact ⟨ Nat.le_floor hH', by obtain ⟨ E, hE, hpE ⟩ := Finset.mem_biUnion.mp hp; have := hH.1 E hE; aesop ⟩;
  -- By prime_bin, primesIn 0 ((Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / (k + 1))) is o(Sr k n).
  have hprime_bin : Filter.Tendsto (fun n : ℕ => primesIn 0 ((Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / (k + 1))) / Sr k n) atTop (nhds 0) := by
    have := prime_bin ( k + 1 ) ( by linarith ) 0 ( Q : ℝ ) ?_ ?_ <;> norm_num at *;
    · convert this.div_atTop ( show Filter.Tendsto ( fun n : ℕ => ( n : ℝ ) ^ ( ( k + 1 : ℝ ) ⁻¹ ) / Real.log n ) Filter.atTop ( Filter.atTop ) from ?_ ) using 2;
      · unfold Sr; ring_nf;
        norm_num [ Real.rpow_mul ] ; ring;
      · have := powers_dominate_logs ( ( k + 1 : ℝ ) ⁻¹ ) ( by positivity ) 1;
        simpa using this.comp tendsto_natCast_atTop_atTop;
    · bv_omega;
  -- By combining the results from hvertex_bound and hprime_bin, we can conclude that the vertex count is o(Sr k n).
  have hvertex_o : ∀ᶠ n in atTop, ∀ H : Finset (Finset ℕ), IsLinearPrimeHG (k + 1) n H → (∀ p ∈ vertices H, (p : ℝ) ≤ (Q : ℝ) * (n : ℝ) ^ ((1 : ℝ) / (k + 1))) → (vertices H).card ≤ (ε / 4) * Sr k n := by
    have := hprime_bin.eventually ( gt_mem_nhds <| show 0 < ε / 4 by positivity );
    filter_upwards [ this, hvertex_bound, Filter.eventually_gt_atTop 1 ] with n hn hn' hn'' H hH hH';
    rw [ div_lt_iff₀ ] at hn <;> nlinarith [ hn' H hH hH', show 0 < Sr k n from div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| pos_of_gt hn'' ) _ ) ( sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr hn'' ) ];
  filter_upwards [ hvertex_o, Filter.eventually_ge_atTop n₀, show ∀ᶠ n in atTop, ( admTypes ( k + 1 ) Q |> Finset.card : ℝ ) ≤ ε / 4 * Sr k n from by
                                                              have hSr_inf : Filter.Tendsto (fun n : ℕ => Sr k n) atTop Filter.atTop := by
                                                                have := powers_dominate_logs ( 2 / ( k + 1 ) : ℝ ) ( by positivity ) 2;
                                                                convert this.comp tendsto_natCast_atTop_atTop using 2 ; norm_num [ Sr ];
                                                              exact hSr_inf.eventually_gt_atTop ( ( admTypes ( k + 1 ) Q |> Finset.card : ℝ ) / ( ε / 4 ) ) |> fun h => h.mono fun n hn => by nlinarith [ mul_div_cancel₀ ( ( admTypes ( k + 1 ) Q |> Finset.card : ℝ ) ) ( by positivity : ( ε / 4 ) ≠ 0 ) ] ; ] with n hn hn' hn'';
  obtain ⟨ H, hH₁, hH₂, hH₃ ⟩ := hn₀ n hn';
  nlinarith [ hAH n hn' H hH₁, hn H hH₁ hH₂, show 0 ≤ Sr k n from div_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( sq_nonneg _ ) ]

/--
Main theorem.
-/
theorem main (k : ℕ) (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Nat.primeCounting n : ℝ) + (Lam (k + 1) - ε) * Sr k n ≤ (Fkrep k n : ℝ) ∧
      (Fkrep k n : ℝ) ≤ (Fkdist k n : ℝ) ∧
      (Fkdist k n : ℝ) ≤ (Nat.primeCounting n : ℝ) + (Lam (k + 1) + ε) * Sr k n := by
  convert Filter.eventually_atTop.mp ( Filter.Eventually.and ( lower_bound k hk hε ) ( Filter.Eventually.and ( Filter.Eventually.of_forall fun n => show ( Fkrep k n : ℝ ) ≤ Fkdist k n from mod_cast Fkrep_le_Fkdist k n ) ( upper_bound k hk hε ) ) ) using 1

/--
Limit of the packing constants: `Λ_r → e²`.
-/
theorem Lambda_limit : Tendsto (fun r : ℕ => Lam r) atTop (nhds (Real.exp 2)) := by
  refine' tendsto_order.2 ⟨ (fun a ha => Lambda_eventually_gt ha), fun b hb => _ ⟩;
  · -- Choose $T = 3 \log r$.
    have hT : ∀ᶠ r in atTop, Lam r ≤ (r : ℝ) / (r - 3 * Real.log r) * (Real.exp 1 - Real.exp (1 - 3 * Real.log r)) ^ 2 + (r : ℝ) ^ 2 * (((r : ℝ) - 1) / ((r : ℝ) - 2) * Real.exp ((1 - 3 * Real.log r) * ((r : ℝ) - 2) / ((r : ℝ) - 1)) - (1 / 2 : ℝ) * Real.exp (2 * (1 - 3 * Real.log r))) := by
      refine' Filter.eventually_atTop.mpr ⟨ 20, fun r hr => _ ⟩;
      refine' le_trans ( Lam_le_cover r ( truncatedCover r ( 3 * Real.log r ) ) _ ) _;
      · apply truncatedCover_isPairCover;
        · linarith;
        · exact lt_of_lt_of_le ( by norm_num ) ( mul_le_mul_of_nonneg_left ( Real.log_two_gt_d9.le.trans ( Real.log_le_log ( by norm_num ) ( by norm_cast; linarith ) ) ) zero_le_three );
        · have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( r : ℝ ) / 10 );
          rw [ Real.log_div ] at this <;> norm_num at *;
          · linarith [ show ( r : ℝ ) ≥ 20 by norm_cast, show Real.log 10 < 3 by rw [ Real.log_lt_iff_lt_exp ( by norm_num ) ] ; exact by have := Real.exp_one_gt_d9.le; norm_num1 at *; rw [ show Real.exp 3 = ( Real.exp 1 ) ^ 3 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ Real.add_one_le_exp 1, pow_pos ( Real.exp_pos 1 ) 2 ] ];
          · linarith;
      · convert truncatedCover_cost r ( by linarith ) ( 3 * Real.log r ) _ _ |> le_of_eq using 1;
        · exact lt_of_lt_of_le ( by norm_num ) ( mul_le_mul_of_nonneg_left ( Real.log_two_gt_d9.le.trans ( Real.log_le_log ( by norm_num ) ( by norm_cast; linarith ) ) ) zero_le_three );
        · have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( r : ℝ ) / 10 );
          rw [ Real.log_div ] at this <;> norm_num at *;
          · linarith [ show ( r : ℝ ) ≥ 20 by norm_cast, show Real.log 10 < 3 by rw [ Real.log_lt_iff_lt_exp ( by norm_num ) ] ; exact by have := Real.exp_one_gt_d9.le; norm_num1 at *; rw [ show Real.exp 3 = ( Real.exp 1 ) ^ 3 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ Real.add_one_le_exp 1, pow_pos ( Real.exp_pos 1 ) 2 ] ];
          · linarith;
    -- Show that the right-hand side of the inequality tends to $e^2$ as $r \to \infty$.
    have h_rhs_tendsto : Filter.Tendsto (fun r : ℕ => (r : ℝ) / (r - 3 * Real.log r) * (Real.exp 1 - Real.exp (1 - 3 * Real.log r)) ^ 2 + (r : ℝ) ^ 2 * (((r : ℝ) - 1) / ((r : ℝ) - 2) * Real.exp ((1 - 3 * Real.log r) * ((r : ℝ) - 2) / ((r : ℝ) - 1)) - (1 / 2 : ℝ) * Real.exp (2 * (1 - 3 * Real.log r)))) Filter.atTop (nhds (Real.exp 2)) := by
      -- Let's simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * (((r : ℝ) - 1) / ((r : ℝ) - 2) * Real.exp ((1 - 3 * Real.log r) * ((r : ℝ) - 2) / ((r : ℝ) - 1)) - (1 / 2 : ℝ) * Real.exp (2 * (1 - 3 * Real.log r)))) Filter.atTop (nhds 0) by
        -- We'll use the fact that $r / (r - 3 \log r) \to 1$ as $r \to \infty$.
        have h_frac : Filter.Tendsto (fun r : ℕ => (r : ℝ) / (r - 3 * Real.log r)) Filter.atTop (nhds 1) := by
          -- We can divide the numerator and the denominator by $r$ and then take the limit as $r \to \infty$.
          suffices h_frac_simplified : Filter.Tendsto (fun r : ℕ => 1 / (1 - 3 * (Real.log r / r))) Filter.atTop (nhds 1) by
            refine h_frac_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with r hr using by rw [ show ( r : ℝ ) - 3 * Real.log r = r * ( 1 - 3 * ( Real.log r / r ) ) by rw [ mul_sub, mul_one, mul_left_comm, mul_div_cancel₀ _ ( by positivity ) ] ] ; rw [ div_mul_eq_div_div ] ; ring_nf; norm_num [ hr.ne' ] );
          -- We'll use the fact that $\frac{\log r}{r} \to 0$ as $r \to \infty$.
          have h_log_r_div_r : Filter.Tendsto (fun r : ℕ => Real.log r / r) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
          convert tendsto_const_nhds.div ( tendsto_const_nhds.sub ( h_log_r_div_r.const_mul 3 ) ) _ using 2 <;> norm_num;
        convert Filter.Tendsto.add ( h_frac.mul ( Filter.Tendsto.pow ( tendsto_const_nhds.sub ( Real.tendsto_exp_atBot.comp _ ) ) 2 ) ) h_simplify using 2 <;> norm_num;
        exact Filter.tendsto_atTop_atBot.mpr fun x => ⟨ Nat.ceil ( Real.exp ( ( 1 - x ) / 3 ) ), fun n hn => by linarith [ Nat.ceil_le.mp hn, Real.log_exp ( ( 1 - x ) / 3 ), Real.log_le_log ( by positivity ) ( Nat.le_of_ceil_le hn ) ] ⟩;
      -- We'll use the fact that $r^2 \cdot \exp(-3 \log r \cdot (r-2)/(r-1))$ tends to $0$ as $r \to \infty$.
      have h_exp : Filter.Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * Real.exp (-3 * Real.log r * (r - 2) / (r - 1))) Filter.atTop (nhds 0) := by
        -- We can rewrite the expression as $r^2 \cdot r^{-3 \cdot \frac{r-2}{r-1}} = r^{2 - 3 \cdot \frac{r-2}{r-1}}$.
        suffices h_exp' : Filter.Tendsto (fun r : ℕ => (r : ℝ) ^ (2 - 3 * (r - 2) / (r - 1) : ℝ)) Filter.atTop (nhds 0) by
          refine h_exp'.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr;
          rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
          rw [ show ( Real.log r * 2 - Real.log r * r * ( -1 + r : ℝ ) ⁻¹ * 3 + Real.log r * ( -1 + r : ℝ ) ⁻¹ * 6 ) = Real.log r * 2 + ( - ( Real.log r * r * ( -1 + r : ℝ ) ⁻¹ * 3 ) + Real.log r * ( -1 + r : ℝ ) ⁻¹ * 6 ) by ring, Real.exp_add, Real.exp_mul, Real.exp_log ( by positivity ) ] ; norm_cast;
        -- We can rewrite the expression as $r^{2 - 3 \cdot \frac{r-2}{r-1}} = r^{-1 + \frac{3}{r-1}}$.
        suffices h_exp'' : Filter.Tendsto (fun r : ℕ => (r : ℝ) ^ (-1 + 3 / (r - 1) : ℝ)) Filter.atTop (nhds 0) by
          refine h_exp''.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr using congr_arg _ ( by rw [ add_div', sub_div', div_eq_div_iff ] <;> nlinarith [ show ( r : ℝ ) ≥ 2 by norm_cast ] );
        -- We can rewrite the expression as $r^{-1 + \frac{3}{r-1}} = \frac{1}{r^{1 - \frac{3}{r-1}}}$.
        suffices h_exp''' : Filter.Tendsto (fun r : ℕ => (1 : ℝ) / (r : ℝ) ^ (1 - 3 / (r - 1) : ℝ)) Filter.atTop (nhds 0) by
          refine h_exp'''.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with r hr; rw [ one_div, ← Real.rpow_neg ( Nat.cast_nonneg _ ) ] ; ring_nf );
        refine' tendsto_const_nhds.div_atTop _;
        -- We can use the fact that $r^{1 - \frac{3}{r-1}} \geq r^{1/2}$ for sufficiently large $r$.
        have h_lower_bound : ∀ᶠ r : ℕ in atTop, (r : ℝ) ^ (1 - 3 / (r - 1) : ℝ) ≥ (r : ℝ) ^ (1 / 2 : ℝ) := by
          filter_upwards [ Filter.eventually_gt_atTop 7 ] with r hr using Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( by rw [ sub_div', div_le_div_iff₀ ] <;> nlinarith [ show ( r : ℝ ) ≥ 8 by norm_cast ] );
        exact Filter.tendsto_atTop_mono' Filter.atTop h_lower_bound ( tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      -- We'll use the fact that $r^2 \cdot \exp(-3 \log r \cdot (r-2)/(r-1))$ tends to $0$ as $r \to \infty$ to bound the second term.
      have h_second_term : Filter.Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * Real.exp ((1 - 3 * Real.log r) * (r - 2) / (r - 1))) Filter.atTop (nhds 0) := by
        have h_second_term : Filter.Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * Real.exp (-3 * Real.log r * (r - 2) / (r - 1)) * Real.exp ((r - 2) / (r - 1))) Filter.atTop (nhds 0) := by
          convert h_exp.mul ( Real.continuous_exp.continuousAt.tendsto.comp ( show Filter.Tendsto ( fun r : ℕ => ( r - 2 : ℝ ) / ( r - 1 ) ) Filter.atTop ( nhds 1 ) from ?_ ) ) using 2 <;> norm_num;
          rw [ Metric.tendsto_nhds ] ; norm_num;
          exact fun ε hε => ⟨ ⌈ε⁻¹ * 3⌉₊ + 2, fun n hn => abs_lt.mpr ⟨ by nlinarith [ Nat.le_ceil ( ε⁻¹ * 3 ), mul_inv_cancel₀ ( ne_of_gt hε ), show ( n : ℝ ) ≥ ⌈ε⁻¹ * 3⌉₊ + 2 by exact_mod_cast hn, div_mul_cancel₀ ( ( n : ℝ ) - 2 ) ( show ( n : ℝ ) - 1 ≠ 0 by linarith [ show ( n : ℝ ) ≥ ⌈ε⁻¹ * 3⌉₊ + 2 by exact_mod_cast hn ] ) ], by nlinarith [ Nat.le_ceil ( ε⁻¹ * 3 ), mul_inv_cancel₀ ( ne_of_gt hε ), show ( n : ℝ ) ≥ ⌈ε⁻¹ * 3⌉₊ + 2 by exact_mod_cast hn, div_mul_cancel₀ ( ( n : ℝ ) - 2 ) ( show ( n : ℝ ) - 1 ≠ 0 by linarith [ show ( n : ℝ ) ≥ ⌈ε⁻¹ * 3⌉₊ + 2 by exact_mod_cast hn ] ) ] ⟩ ⟩;
        convert h_second_term using 2 ; rw [ mul_assoc, ← Real.exp_add ] ; ring_nf;
      -- We'll use the fact that $r^2 \cdot \exp(-3 \log r \cdot (r-2)/(r-1))$ tends to $0$ as $r \to \infty$ to bound the first term.
      have h_first_term : Filter.Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * ((r - 1) / (r - 2) * Real.exp ((1 - 3 * Real.log r) * (r - 2) / (r - 1)))) Filter.atTop (nhds 0) := by
        convert h_second_term.mul ( show Filter.Tendsto ( fun r : ℕ => ( r - 1 : ℝ ) / ( r - 2 ) ) Filter.atTop ( nhds 1 ) from ?_ ) using 2 <;> ring_nf;
        rw [ Metric.tendsto_nhds ] ; norm_num;
        exact fun ε hε => ⟨ ⌈ε⁻¹ * 3⌉₊ + 3, fun n hn => by rw [ dist_eq_norm ] ; rw [ Real.norm_of_nonneg ] <;> nlinarith [ Nat.le_ceil ( ε⁻¹ * 3 ), mul_inv_cancel₀ ( show ε ≠ 0 by linarith ), show ( n : ℝ ) ≥ ⌈ε⁻¹ * 3⌉₊ + 3 by exact_mod_cast hn, inv_mul_cancel₀ ( show ( -2 + n : ℝ ) ≠ 0 by linarith [ show ( n : ℝ ) ≥ ⌈ε⁻¹ * 3⌉₊ + 3 by exact_mod_cast hn ] ) ] ⟩;
      convert h_first_term.sub ( show Filter.Tendsto ( fun r : ℕ => ( r : ℝ ) ^ 2 * ( 1 / 2 * Real.exp ( 2 * ( 1 - 3 * Real.log r ) ) ) ) Filter.atTop ( nhds 0 ) from ?_ ) using 2 <;> ring_nf;
      norm_num [ Real.exp_sub, Real.exp_mul, Real.exp_log ];
      rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.exp_log ( Nat.cast_pos.mpr hx ) ] ) ] ; ring_nf ; norm_num;
      field_simp;
      exact tendsto_const_nhds.div_atTop ( Filter.Tendsto.atTop_mul_const ( by norm_num ) ( Filter.tendsto_pow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) );
    filter_upwards [ hT, h_rhs_tendsto.eventually ( gt_mem_nhds hb ) ] with r hr₁ hr₂ using lt_of_le_of_lt hr₁ hr₂

/--
Large-`k` upper bound without any definitions: For every `ε > 0` there is a `K`
such that for every `k ≥ K` there is an `N` such that for all `n ≥ N`, every set
`A ⊆ {1, …, n}` with `|A| ≥ π(n) + (e² + ε)·n^{2/(k+1)}/(log n)²` contains
`k + 1` distinct elements `a, b₁, …, b_k` with `a ∣ b₁⋯b_k`.
-/
theorem large_k_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
        (Nat.primeCounting n : ℝ) + (Real.exp 2 + ε) * ((n : ℝ) ^ ((2 : ℝ) / (k + 1)) / (Real.log n) ^ 2) ≤ (A.card : ℝ) →
        ∃ a ∈ A, ∃ b : Fin k → ℕ, (∀ i, b i ∈ A) ∧ (∀ i, b i ≠ a) ∧ Function.Injective b ∧ a ∣ ∏ i, b i := by
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp
    (Lambda_limit.eventually (gt_mem_nhds (show Real.exp 2 < Real.exp 2 + ε / 2 by linarith)))
  refine ⟨max K₀ 2, fun k hk => ?_⟩
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (upper_bound k hk2 (show (0:ℝ) < ε / 2 by linarith))
  refine ⟨max N 2, fun n hn A hA hcard => ?_⟩
  by_contra hcon
  have hprim : DistPrimitive k A := distPrimitive_of_not_exists hcon
  have hle : (A.card : ℝ) ≤ (Fkdist k n : ℝ) := by
    exact_mod_cast card_le_Fkdist hA hprim
  have hupper := hN n (le_trans (le_max_left _ _) hn)
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hSpos : 0 < Sr k n := by
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
    have : (0:ℝ) < (n : ℝ) ^ ((2 : ℝ) / (k + 1)) :=
      Real.rpow_pos_of_pos (by positivity) _
    exact div_pos this (by positivity)
  have hLam : Lam (k + 1) < Real.exp 2 + ε / 2 :=
    hK₀ (k + 1) (le_trans (le_trans (le_max_left _ _) hk) (Nat.le_succ k))
  have hSeq : Sr k n = (n : ℝ) ^ ((2 : ℝ) / (k + 1)) / (Real.log n) ^ 2 := rfl
  rw [hSeq] at hSpos hupper
  nlinarith [hSpos, hcard, hle, hupper, hLam]

/--
Large-`k` lower bound without any definitions: For every `ε > 0` there is a `K`
such that for every `k ≥ K` there is an `N` such that for all `n ≥ N` there is a
set `A ⊆ {1, …, n}` with `|A| ≥ π(n) + (e² - ε)·n^{2/(k+1)}/(log n)²` in which
no element divides a product of `k` elements other than itself.
-/
theorem large_k_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧
        (Nat.primeCounting n : ℝ) + (Real.exp 2 - ε) * ((n : ℝ) ^ ((2 : ℝ) / (k + 1)) / (Real.log n) ^ 2) ≤ (A.card : ℝ) ∧
        ∀ a ∈ A, ∀ b : Fin k → ℕ, (∀ i, b i ∈ A) → a ∣ ∏ i, b i → ∃ i, b i = a := by
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp
    (Lambda_limit.eventually (lt_mem_nhds (show Real.exp 2 - ε / 2 < Real.exp 2 by linarith)))
  refine ⟨max K₀ 2, fun k hk => ?_⟩
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨N, hN⟩ := main k hk2 (show (0:ℝ) < ε / 2 by linarith)
  refine ⟨max N 2, fun n hn => ?_⟩
  obtain ⟨A, hA, hprim, hcard⟩ := exists_repPrimitive_card_eq_Fkrep k n
  refine ⟨A, hA, ?_, ?_⟩
  · obtain ⟨hlower, -, -⟩ := hN n (le_trans (le_max_left _ _) hn)
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hSpos : 0 < Sr k n := by
      have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
      have : (0:ℝ) < (n : ℝ) ^ ((2 : ℝ) / (k + 1)) :=
        Real.rpow_pos_of_pos (by positivity) _
      exact div_pos this (by positivity)
    have hLam : Real.exp 2 - ε / 2 < Lam (k + 1) :=
      hK₀ (k + 1) (le_trans (le_trans (le_max_left _ _) hk) (Nat.le_succ k))
    have hSeq : Sr k n = (n : ℝ) ^ ((2 : ℝ) / (k + 1)) / (Real.log n) ^ 2 := rfl
    rw [hSeq] at hSpos hlower
    rw [hcard]
    nlinarith [hSpos, hlower, hLam]
  · intro a ha b hb hdvd
    by_contra hcon
    push_neg at hcon
    exact hprim a ha b (fun i => Finset.mem_erase.mpr ⟨hcon i, hb i⟩) hdvd

#print axioms large_k_lower
#print axioms large_k_upper
