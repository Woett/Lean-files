import Mathlib

set_option maxHeartbeats 6400000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
We say that a set A of natural numbers is a multiplicative Sidon set if whenever
a,b,c,d ∈ A satisfy ab = cd, then {a,b} = {c,d} as unordered pairs. In 1938,
Erdős proved that for all large enough n, there exists a multiplicative Sidon
set A ⊆ {1,...,n} with

|A| ≥ π(n) + c · n^(3/4) / (log n)^(3/2),

for some absolute constant c > 0. In fact, he explicitly notes that c = 1/36
works, although this can be tightened.

P. Erdős, On sequences of integers no one of which divides the product of two
others and on some related problems, Mitt. Forsch.-Inst. Math. Mech. Univ. Tomsk
2 (1938), 74--82

I have asked ChatGPT to optimize Erdős' construction, and it came up with a more
efficient construction that achieves any c < 2^(11/4) / 3^(3/4) ≈ 2.95.

Below you can find a formalization of this improvement, which was obtained by
Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

The only external input is the prime number theorem (PNT), assumed as `pi_alt`.

Finding the optimal constant c is still open and is referenced as Erdős Problem
#425 on Bloom's website; https://www.erdosproblems.com/425.

Lean version: leanprover/lean4:v4.28.0
Mathlib version: 8f9d9cff6bd728b17a24e163c9402775d9e6a365
-/

open Finset Real Filter Asymptotics
open scoped Nat

-- ============================================================
-- § 1. Main definitions
-- ============================================================

/-- A finite set of natural numbers is multiplicative Sidon if whenever ab = cd
  for a,b,c,d in the set, then {a,b} = {c,d} as unordered pairs. -/
def IsMultiplicativeSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a * b = c * d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The constant Λ = 2^(11/4) / 3^(3/4) -/
noncomputable def Lambda : ℝ := (2 : ℝ) ^ ((11 : ℝ) / 4) / (3 : ℝ) ^ ((3 : ℝ) / 4)

-- ============================================================
-- § 2. Extracting primes from intervals
-- ============================================================

/-- The set of primes in the range (a, b]. -/
noncomputable def primesInRange (a b : ℕ) : Finset ℕ :=
  (Finset.Icc (a + 1) b).filter Nat.Prime

lemma primesInRange_card (a b : ℕ) (hab : a ≤ b) :
    (primesInRange a b).card = Nat.primeCounting b - Nat.primeCounting a := by
  rw [ tsub_eq_of_eq_add ];
  rw [ Nat.primeCounting, Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range ];
  rw [ ← Finset.card_union_of_disjoint, add_comm ];
  · congr with x ; simp +arith +decide [ primesInRange ];
    grind;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_range.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;

lemma primesInRange_mem (a b : ℕ) {p : ℕ} (hp : p ∈ primesInRange a b) :
    Nat.Prime p ∧ a < p ∧ p ≤ b := by
  simp [primesInRange, Finset.mem_filter, Finset.mem_Icc] at hp
  exact ⟨hp.2, by omega, by omega⟩

lemma extract_primes (a b m : ℕ) (hab : a ≤ b)
    (hm : m ≤ Nat.primeCounting b - Nat.primeCounting a) :
    ∃ S : Finset ℕ, S.card = m ∧ (∀ p ∈ S, Nat.Prime p ∧ a < p ∧ p ≤ b) := by
  obtain ⟨ S, hS₁, hS₂ ⟩ := Finset.exists_subset_card_eq ( show m ≤ Finset.card ( primesInRange a b ) from by rw [ primesInRange_card a b hab ] ; exact hm );
  exact ⟨ S, hS₂, fun p hp => primesInRange_mem a b ( hS₁ hp ) ⟩

-- ============================================================
-- § 3. Finite projective plane block system
-- ============================================================

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- Points of the projective plane PG(2, F_p). -/
abbrev PGPoint := (ZMod p × ZMod p) ⊕ ZMod p ⊕ Unit

/-- Lines of the projective plane PG(2, F_p). -/
abbrev PGLine := (ZMod p × ZMod p) ⊕ ZMod p ⊕ Unit

/-- Points on a line in PG(2, F_p) -/
noncomputable def pgLinePoints (l : PGLine p) : Finset (PGPoint p) :=
  match l with
  | .inl (m, b) =>
    (Finset.univ.image fun x => (Sum.inl (x, m * x + b) : PGPoint p)) ∪
    {Sum.inr (Sum.inl m)}
  | .inr (Sum.inl a) =>
    (Finset.univ.image fun y => (Sum.inl (a, y) : PGPoint p)) ∪
    {Sum.inr (Sum.inr ())}
  | .inr (Sum.inr ()) =>
    (Finset.univ.image fun m => (Sum.inr (Sum.inl m) : PGPoint p)) ∪
    {Sum.inr (Sum.inr ())}

/-- Lines through a point in PG(2, F_p) -/
noncomputable def pgPointLines (pt : PGPoint p) : Finset (PGLine p) :=
  match pt with
  | .inl (x, y) =>
    (Finset.univ.image fun m => (Sum.inl (m, y - m * x) : PGLine p)) ∪
    {Sum.inr (Sum.inl x)}
  | .inr (Sum.inl m) =>
    (Finset.univ.image fun b => (Sum.inl (m, b) : PGLine p)) ∪
    {Sum.inr (Sum.inr ())}
  | .inr (Sum.inr ()) =>
    (Finset.univ.image fun a => (Sum.inr (Sum.inl a) : PGLine p)) ∪
    {Sum.inr (Sum.inr ())}

set_option maxHeartbeats 3200000 in
lemma pgLinePoints_card (l : PGLine p) : (pgLinePoints p l).card = p + 1 := by
  unfold pgLinePoints;
  rcases l with ( ⟨ m, b ⟩ | ⟨ a ⟩ | ⟨ ⟩ ) <;> simp +decide [ Finset.card_image_of_injective, Function.Injective ]

set_option maxHeartbeats 3200000 in
lemma pgLines_meet_le_one (l₁ l₂ : PGLine p) (h : l₁ ≠ l₂) :
    (pgLinePoints p l₁ ∩ pgLinePoints p l₂).card ≤ 1 := by
  revert l₁ l₂;
  simp +decide only [card_le_one_iff];
  simp +decide [ pgLinePoints ];
  constructor;
  · grind +qlia;
  · grind

set_option maxHeartbeats 3200000 in
lemma pgPointLines_card (pt : PGPoint p) : (pgPointLines p pt).card = p + 1 := by
  unfold pgPointLines;
  rcases pt with ( ⟨ x, y ⟩ | ⟨ m ⟩ | ⟨ ⟩ ) <;> simp +decide [ Finset.card_image_of_injective, Function.Injective ]

set_option maxHeartbeats 3200000 in
lemma pgIncidence_iff (pt : PGPoint p) (l : PGLine p) :
    pt ∈ pgLinePoints p l ↔ l ∈ pgPointLines p pt := by
  rcases pt with ( ⟨ x, y ⟩ | m | _ ) <;> rcases l with ( ⟨ m', b' ⟩ | a | _ ) <;> simp +decide [ pgLinePoints, pgPointLines ];
  grind +qlia

variable {p}

set_option maxHeartbeats 3200000 in
theorem projective_plane_blocks_nat
    (X : Finset ℕ) (hX : X.card = p * (p + 1) + 1) :
    ∃ (I : Finset ℕ) (C : ℕ → Finset ℕ),
      I.card = p * (p + 1) + 1 ∧
      (∀ i ∈ I, C i ⊆ X) ∧
      (∀ i ∈ I, (C i).card = p + 1) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → (C i ∩ C j).card ≤ 1) ∧
      (∀ x ∈ X, (I.filter (fun i => x ∈ C i)).card = p + 1) := by
  have h_proj_plane : ∃ (f : PGLine p → Fin (p * (p + 1) + 1)) (g : PGPoint p → Fin (p * (p + 1) + 1)), Function.Bijective f ∧ Function.Bijective g := by
    have h_card : Fintype.card (PGLine p) = p * (p + 1) + 1 ∧ Fintype.card (PGPoint p) = p * (p + 1) + 1 := by
      simp +decide [ PGLine, PGPoint ];
      ring;
    have h_equiv : Nonempty (PGLine p ≃ Fin (p * (p + 1) + 1)) ∧ Nonempty (PGPoint p ≃ Fin (p * (p + 1) + 1)) := by
      exact ⟨ ⟨ Fintype.equivOfCardEq <| by simp +decide [ h_card.1 ] ⟩, ⟨ Fintype.equivOfCardEq <| by simp +decide [ h_card.2 ] ⟩ ⟩;
    exact ⟨ _, _, Equiv.bijective h_equiv.1.some, Equiv.bijective h_equiv.2.some ⟩;
  obtain ⟨f, g, hf, hg⟩ := h_proj_plane;
  use Finset.univ.image (fun i => X.orderEmbOfFin hX i);
  obtain ⟨C, hC⟩ : ∃ C : Fin (p * (p + 1) + 1) → Finset (Fin (p * (p + 1) + 1)), (∀ i, (C i).card = p + 1) ∧ (∀ i j, i ≠ j → (C i ∩ C j).card ≤ 1) ∧ (∀ x, (Finset.card (Finset.filter (fun i => x ∈ C i) Finset.univ)) = p + 1) := by
    use fun i => Finset.image g (pgLinePoints p (hf.2 i).choose);
    refine' ⟨ _, _, _ ⟩;
    · intro i; rw [ Finset.card_image_of_injective _ hg.injective ] ; exact pgLinePoints_card p _;
    · intro i j hij;
      rw [ ← Finset.image_inter ];
      · rw [ Finset.card_image_of_injective _ hg.injective ];
        convert pgLines_meet_le_one p _ _ _;
        grind;
      · exact hg.injective;
    · intro x;
      obtain ⟨ y, hy ⟩ := hg.2 x;
      have h_card : Finset.card (Finset.filter (fun i => y ∈ pgLinePoints p (hf.2 i).choose) Finset.univ) = p + 1 := by
        have h_card : Finset.card (Finset.filter (fun l => y ∈ pgLinePoints p l) Finset.univ) = p + 1 := by
          convert pgPointLines_card p y using 1;
          exact congr_arg Finset.card ( Finset.ext fun l => by simp +decide [ pgIncidence_iff ] );
        convert h_card using 1;
        refine' Finset.card_bij ( fun i hi => ( hf.2 i ).choose ) _ _ _ <;> simp +decide;
        · grind +extAll;
        · exact ⟨ fun a b hab => ⟨ f ( Sum.inl ( a, b ) ), by simpa [ hf.1.eq_iff ] using hab ⟩, fun a ha => ⟨ f ( Sum.inr ( Sum.inl a ) ), by simpa [ hf.1.eq_iff ] using ha ⟩, fun b hb => ⟨ f ( Sum.inr ( Sum.inr b ) ), by simpa [ hf.1.eq_iff ] using hb ⟩ ⟩;
      convert h_card using 2;
      ext i; simp +decide [ ← hy, hg.injective.eq_iff ] ;
  refine' ⟨ fun i => if hi : i ∈ Finset.image ( fun i => X.orderEmbOfFin hX i ) Finset.univ then Finset.image ( fun j => X.orderEmbOfFin hX j ) ( C ( Classical.choose ( Finset.mem_image.mp hi ) ) ) else ∅, _, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
  · exact fun i hi => Finset.image_subset_iff.mpr fun j hj => Finset.orderEmbOfFin_mem _ _ _;
  · intro i hi j hj hij; rw [ ← Finset.image_inter ] ; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
    · grind +qlia;
    · exact fun i j hij => by simpa [ Fin.ext_iff ] using hij;
  · intro x hx;
    obtain ⟨ i, hi ⟩ := Finset.mem_image.mp ( show x ∈ Finset.image ( fun j => X.orderEmbOfFin hX j ) Finset.univ from by aesop ) ; simp_all +decide ;
    convert hC.2.2 i using 1;
    refine' Finset.card_bij ( fun j hj => Classical.choose ( Finset.mem_image.mp ( show j ∈ Finset.image ( fun i => X.orderEmbOfFin hX i ) Finset.univ from by aesop ) ) ) _ _ _ <;> simp +decide ;
    · intro a ha hq; split_ifs at hq ; simp_all +decide [ Finset.mem_image ] ;
      obtain ⟨ j, hj, hj' ⟩ := hq; have := X.orderEmbOfFin hX |>.injective ( hj'.trans hi.symm ) ; aesop;
    · grind;
    · intro j hj; use X.orderEmbOfFin hX j; aesop;

-- ============================================================
-- § 4. Layered block-product construction
-- ============================================================

/-- Standard set of hypotheses for the layered block-product construction. -/
structure BlockProductData (k : ℕ) where
  I : Fin k → Finset ℕ
  Q : Fin k → Finset ℕ
  r : Fin k → ℕ → ℕ
  C : Fin k → ℕ → Finset ℕ
  S : Finset ℕ
  hS_prime : ∀ s ∈ S, Nat.Prime s
  hQ_prime : ∀ j, ∀ q ∈ Q j, Nat.Prime q
  hr_prime : ∀ j, ∀ i ∈ I j, Nat.Prime (r j i)
  hr_inj : ∀ j, ∀ i₁ ∈ I j, ∀ i₂ ∈ I j, r j i₁ = r j i₂ → i₁ = i₂
  hC_sub : ∀ j, ∀ i ∈ I j, C j i ⊆ Q j
  hC_inter : ∀ j, ∀ i₁ ∈ I j, ∀ i₂ ∈ I j, i₁ ≠ i₂ →
    (C j i₁ ∩ C j i₂).card ≤ 1
  hSQ : ∀ j, Disjoint S (Q j)
  hSR : ∀ j, ∀ i ∈ I j, r j i ∉ S
  hQQ : ∀ j₁ j₂ : Fin k, j₁ ≠ j₂ → Disjoint (Q j₁) (Q j₂)
  hQR : ∀ j₁ j₂ : Fin k, ∀ i ∈ I j₂, r j₂ i ∉ Q j₁
  hRR : ∀ j₁ j₂ : Fin k, j₁ ≠ j₂ →
    ∀ i₁ ∈ I j₁, ∀ i₂ ∈ I j₂, r j₁ i₁ ≠ r j₂ i₂

variable {k : ℕ} (D : BlockProductData k)

noncomputable def BlockProductData.productSet : Finset ℕ :=
  Finset.biUnion Finset.univ
    (fun j => (D.I j).biUnion (fun i => (D.C j i).image (fun q => D.r j i * q)))

noncomputable def BlockProductData.fullSet : Finset ℕ :=
  D.S ∪ D.productSet

lemma BlockProductData.productSet_mem {x : ℕ} (hx : x ∈ D.productSet) :
    ∃ j : Fin k, ∃ i ∈ D.I j, ∃ q ∈ D.C j i, x = D.r j i * q := by
  simp only [BlockProductData.productSet, mem_biUnion, mem_univ, mem_image, true_and] at hx
  obtain ⟨j, i, hi, q, hq, rfl⟩ := hx
  exact ⟨j, i, hi, q, hq, rfl⟩

lemma BlockProductData.product_unique {j j' : Fin k}
    {i i' : ℕ} {q q' : ℕ}
    (hi : i ∈ D.I j) (hi' : i' ∈ D.I j') (_hq : q ∈ D.C j i) (hq' : q' ∈ D.C j' i')
    (heq : D.r j i * q = D.r j' i' * q') :
    j = j' ∧ i = i' ∧ q = q' := by
  have h_div : D.r j i ∣ D.r j' i' ∨ D.r j i ∣ q' := by
    exact Nat.Prime.dvd_mul ( D.hr_prime j i hi ) |>.1 ( heq ▸ dvd_mul_right _ _ );
  cases' h_div with h_div h_div;
  · have h_eq : D.r j i = D.r j' i' := by
      exact Nat.prime_dvd_prime_iff_eq ( D.hr_prime j i hi ) ( D.hr_prime j' i' hi' ) |>.1 h_div;
    by_cases hj : j = j' <;> simp_all +decide [ D.hRR ];
    by_cases hi'' : i = i' <;> simp_all +decide ;
    · exact heq.resolve_right ( Nat.Prime.ne_zero ( D.hr_prime _ _ hi' ) );
    · exact hi'' ( D.hr_inj _ _ hi _ hi' h_eq );
  · have h_contra : D.r j i = q' := by
      have h_contra : Nat.Prime (D.r j i) ∧ Nat.Prime q' := by
        exact ⟨ D.hr_prime j i hi, D.hQ_prime j' q' ( D.hC_sub j' i' hi' hq' ) ⟩;
      exact Nat.prime_dvd_prime_iff_eq h_contra.1 h_contra.2 |>.1 h_div;
    have := D.hQR j' j i hi; simp_all +decide ;
    exact False.elim <| this <| D.hC_sub _ _ hi' hq'

lemma BlockProductData.productSet_disjoint_S : Disjoint D.S D.productSet := by
  rw [ Finset.disjoint_left ];
  intro x hx hx';
  obtain ⟨ j, i, hi, q, hq, rfl ⟩ := D.productSet_mem hx';
  have := D.hS_prime _ hx; simp_all +decide [ Nat.prime_mul_iff ] ;
  cases this <;> have := D.hC_sub j i hi hq <;> simp_all +decide;
  · exact absurd ( D.hQ_prime j 1 this ) ( by norm_num );
  · exact absurd ( D.hr_prime j i hi ) ( by aesop )

lemma BlockProductData.S_prime_not_dvd_product {s : ℕ} (hs : s ∈ D.S)
    {j : Fin k} {i : ℕ} (hi : i ∈ D.I j) {q : ℕ} (hq : q ∈ D.C j i) :
    s ≠ D.r j i ∧ s ≠ q := by
  constructor;
  · exact fun h => D.hSR j i hi <| h ▸ hs;
  · exact fun h => Finset.disjoint_left.mp ( D.hSQ j ) hs ( h.symm ▸ D.hC_sub j i hi hq )

lemma BlockProductData.R_primes_match
    {j₁ j₂ j₃ j₄ : Fin k}
    {i₁ i₂ i₃ i₄ : ℕ} {q₁ q₂ q₃ q₄ : ℕ}
    (hi₁ : i₁ ∈ D.I j₁) (hi₂ : i₂ ∈ D.I j₂) (hi₃ : i₃ ∈ D.I j₃) (hi₄ : i₄ ∈ D.I j₄)
    (hq₃ : q₃ ∈ D.C j₃ i₃) (hq₄ : q₄ ∈ D.C j₄ i₄)
    (heq : D.r j₁ i₁ * q₁ * (D.r j₂ i₂ * q₂) =
           D.r j₃ i₃ * q₃ * (D.r j₄ i₄ * q₄)) :
    (D.r j₁ i₁ = D.r j₃ i₃ ∧ D.r j₂ i₂ = D.r j₄ i₄) ∨
    (D.r j₁ i₁ = D.r j₄ i₄ ∧ D.r j₂ i₂ = D.r j₃ i₃) := by
  have h_div : D.r j₁ i₁ ∣ D.r j₃ i₃ ∨ D.r j₁ i₁ ∣ D.r j₄ i₄ := by
    have h_div : D.r j₁ i₁ ∣ D.r j₃ i₃ * q₃ * (D.r j₄ i₄ * q₄) := by
      exact heq ▸ dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _;
    have h_not_div_q : ¬(D.r j₁ i₁ ∣ q₃) ∧ ¬(D.r j₁ i₁ ∣ q₄) := by
      constructor <;> intro h <;> have := Nat.prime_dvd_prime_iff_eq ( D.hr_prime j₁ i₁ hi₁ ) ( D.hQ_prime j₃ q₃ ( D.hC_sub j₃ i₃ hi₃ hq₃ ) ) <;> have := Nat.prime_dvd_prime_iff_eq ( D.hr_prime j₁ i₁ hi₁ ) ( D.hQ_prime j₄ q₄ ( D.hC_sub j₄ i₄ hi₄ hq₄ ) ) <;> simp_all +decide ;
      · have := D.hQR j₃ j₁ i₁ hi₁; simp_all +decide ;
        exact this ( D.hC_sub j₃ i₃ hi₃ hq₃ );
      · have := D.hQR j₄ j₁ i₁ hi₁; simp_all +decide ;
        exact this ( D.hC_sub j₄ i₄ hi₄ hq₄ );
    have h_div_r : Nat.Prime (D.r j₁ i₁) := by
      exact D.hr_prime _ _ hi₁;
    simp_all +decide [ mul_assoc, Nat.Prime.dvd_mul ];
  cases' h_div with h_div_case1 h_div_case2;
  · have := Nat.prime_dvd_prime_iff_eq ( D.hr_prime j₁ i₁ hi₁ ) ( D.hr_prime j₃ i₃ hi₃ ) ; simp_all +decide ;
    have h_div : D.r j₂ i₂ ∣ D.r j₄ i₄ ∨ D.r j₂ i₂ ∣ q₃ := by
      have h_div : D.r j₂ i₂ ∣ D.r j₄ i₄ * q₃ * q₄ := by
        exact ⟨ q₁ * q₂, by nlinarith [ show 0 < D.r j₃ i₃ by exact Nat.Prime.pos ( D.hr_prime j₃ i₃ hi₃ ) ] ⟩;
      have h_div : D.r j₂ i₂ ∣ D.r j₄ i₄ * q₃ := by
        refine' Nat.Coprime.dvd_of_dvd_mul_right _ h_div;
        refine' Nat.Prime.coprime_iff_not_dvd ( D.hr_prime j₂ i₂ hi₂ ) |>.2 _;
        intro h; have := Nat.prime_dvd_prime_iff_eq ( D.hr_prime j₂ i₂ hi₂ ) ( D.hQ_prime j₄ q₄ ( D.hC_sub j₄ i₄ hi₄ hq₄ ) ) ; simp_all +decide ;
        have := D.hQR j₄ j₂ i₂ hi₂; simp_all +decide ;
        exact this ( D.hC_sub j₄ i₄ hi₄ hq₄ );
      exact Nat.Prime.dvd_mul ( D.hr_prime j₂ i₂ hi₂ ) |>.1 h_div;
    cases' h_div with h_div_case2 h_div_case3;
    · have := Nat.prime_dvd_prime_iff_eq ( D.hr_prime j₂ i₂ hi₂ ) ( D.hr_prime j₄ i₄ hi₄ ) ; aesop;
    · have := Nat.prime_dvd_prime_iff_eq ( D.hr_prime j₂ i₂ hi₂ ) ( D.hQ_prime j₃ q₃ ( D.hC_sub j₃ i₃ hi₃ hq₃ ) ) ; simp_all +decide ;
      have := D.hQR j₃ j₂ i₂ hi₂; simp_all +decide ;
      exact False.elim <| this <| D.hC_sub j₃ i₃ hi₃ hq₃;
  · have := Nat.prime_dvd_prime_iff_eq ( D.hr_prime j₁ i₁ hi₁ ) ( D.hr_prime j₄ i₄ hi₄ ) ; simp_all +decide ;
    have h_div2 : D.r j₂ i₂ ∣ D.r j₃ i₃ := by
      have h_div2 : D.r j₂ i₂ ∣ D.r j₃ i₃ * q₃ * q₄ := by
        exact ⟨ q₁ * q₂, by nlinarith [ show 0 < D.r j₄ i₄ by exact Nat.Prime.pos ( D.hr_prime j₄ i₄ hi₄ ) ] ⟩;
      have h_div2 : D.r j₂ i₂ ∣ D.r j₃ i₃ * q₃ := by
        have h_div2 : ¬(D.r j₂ i₂ ∣ q₄) := by
          intro h_div2
          have h_contra : D.r j₂ i₂ ∈ D.Q j₄ := by
            have h_contra : q₄ ∈ D.Q j₄ := by
              exact D.hC_sub j₄ i₄ hi₄ hq₄;
            have := Nat.prime_dvd_prime_iff_eq ( D.hr_prime j₂ i₂ hi₂ ) ( D.hQ_prime j₄ q₄ h_contra ) ; aesop;
          exact absurd ( D.hQR j₄ j₂ i₂ hi₂ ) ( by aesop );
        exact Or.resolve_right ( Nat.Prime.dvd_mul ( D.hr_prime j₂ i₂ hi₂ ) |>.1 <| by simpa only [ mul_assoc ] using ‹D.r j₂ i₂ ∣ D.r j₃ i₃ * q₃ * q₄› ) h_div2;
      have h_div2 : ¬(D.r j₂ i₂ ∣ q₃) := by
        intro h; have := Nat.prime_dvd_prime_iff_eq ( D.hr_prime j₂ i₂ hi₂ ) ( D.hQ_prime j₃ q₃ ( D.hC_sub j₃ i₃ hi₃ hq₃ ) ) ; simp_all +decide ;
        have := D.hQR j₃ j₂ i₂ hi₂; simp_all +decide ;
        exact this ( D.hC_sub j₃ i₃ hi₃ hq₃ );
      exact Or.resolve_right ( Nat.Prime.dvd_mul ( D.hr_prime j₂ i₂ hi₂ ) |>.1 ‹_› ) h_div2;
    have := Nat.prime_dvd_prime_iff_eq ( D.hr_prime j₂ i₂ hi₂ ) ( D.hr_prime j₃ i₃ hi₃ ) ; aesop;

lemma BlockProductData.S_prime_not_dvd_product_elt {s : ℕ} (hs : s ∈ D.S)
    {x : ℕ} (hx : x ∈ D.productSet) : ¬(s ∣ x) := by
  obtain ⟨ j, i, hi, q, hq, rfl ⟩ := D.productSet_mem hx;
  rw [ Nat.Prime.dvd_mul ];
  · have := D.S_prime_not_dvd_product hs hi hq; simp_all +decide ;
    exact ⟨ fun h => this.1 <| Nat.prime_dvd_prime_iff_eq ( D.hS_prime s hs ) ( D.hr_prime j i hi ) |>.1 h, fun h => this.2 <| Nat.prime_dvd_prime_iff_eq ( D.hS_prime s hs ) ( D.hQ_prime j q ( D.hC_sub j i hi hq ) ) |>.1 h ⟩;
  · exact D.hS_prime s hs

lemma BlockProductData.S_prime_dvd_fullSet {s : ℕ} (hs : s ∈ D.S)
    {a : ℕ} (ha : a ∈ D.fullSet) (h : s ∣ a) : a ∈ D.S := by
  contrapose! h;
  exact D.S_prime_not_dvd_product_elt hs ( by rw [ BlockProductData.fullSet ] at ha; exact Finset.mem_union.mp ha |> Or.resolve_left <| by aesop )

lemma BlockProductData.sidon_case_all_product
    {a b c d : ℕ}
    (ha : a ∈ D.productSet) (hb : b ∈ D.productSet)
    (hc : c ∈ D.productSet) (hd : d ∈ D.productSet)
    (heq : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  obtain ⟨j₁, i₁, hi₁, q₁, hq₁, rfl⟩ := D.productSet_mem ha
  obtain ⟨j₂, i₂, hi₂, q₂, hq₂, rfl⟩ := D.productSet_mem hb
  obtain ⟨j₃, i₃, hi₃, q₃, hq₃, rfl⟩ := D.productSet_mem hc
  obtain ⟨j₄, i₄, hi₄, q₄, hq₄, rfl⟩ := D.productSet_mem hd;
  obtain h|h := D.R_primes_match hi₁ hi₂ hi₃ hi₄ hq₃ hq₄ heq;
  · have h_unique : j₁ = j₃ ∧ i₁ = i₃ ∧ j₂ = j₄ ∧ i₂ = i₄ := by
      grind +suggestions;
    have h_unique : q₁ * q₂ = q₃ * q₄ := by
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      exact mul_right_cancel₀ ( mul_ne_zero ( Nat.Prime.ne_zero ( D.hr_prime _ _ hi₃ ) ) ( Nat.Prime.ne_zero ( D.hr_prime _ _ hi₄ ) ) ) ( by linarith );
    have h_prime : Nat.Prime q₁ ∧ Nat.Prime q₂ ∧ Nat.Prime q₃ ∧ Nat.Prime q₄ := by
      exact ⟨ D.hQ_prime _ _ ( D.hC_sub _ _ hi₁ hq₁ ), D.hQ_prime _ _ ( D.hC_sub _ _ hi₂ hq₂ ), D.hQ_prime _ _ ( D.hC_sub _ _ hi₃ hq₃ ), D.hQ_prime _ _ ( D.hC_sub _ _ hi₄ hq₄ ) ⟩;
    have h_unique : q₁ = q₃ ∨ q₁ = q₄ := by
      have := h_prime.1.dvd_mul.mp ( h_unique ▸ dvd_mul_right _ _ ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
    cases h_unique <;> simp_all +decide ;
    · aesop;
    · by_cases h : j₃ = j₄ <;> simp_all +decide [ mul_comm, mul_left_comm ];
      · by_cases hi : i₃ = i₄ <;> simp_all +decide [ Nat.Prime.ne_zero ];
        have := D.hC_inter j₄ i₃ hi₃ i₄ hi₄ hi; simp_all +decide [ Finset.card_le_one ] ;
        exact Or.inl ⟨ Or.inl <| this _ hq₁ hq₄ _ hq₃ hq₂, Or.inl <| this _ hq₃ hq₂ _ hq₁ hq₄ ⟩;
      · have := D.hQQ j₃ j₄ h; simp_all +decide [ Finset.disjoint_left ] ;
        exact False.elim <| this ( D.hC_sub j₃ i₃ hi₃ hq₁ ) ( D.hC_sub j₄ i₄ hi₄ hq₄ );
  · have h_q_cases : q₁ = q₃ ∧ q₂ = q₄ ∨ q₁ = q₄ ∧ q₂ = q₃ := by
      have h_q_cases : q₁ * q₂ = q₃ * q₄ := by
        simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        exact mul_left_cancel₀ ( mul_ne_zero ( Nat.Prime.ne_zero ( D.hr_prime j₃ i₃ hi₃ ) ) ( Nat.Prime.ne_zero ( D.hr_prime j₄ i₄ hi₄ ) ) ) ( by linarith );
      have h_q_cases : Nat.Prime q₁ ∧ Nat.Prime q₂ ∧ Nat.Prime q₃ ∧ Nat.Prime q₄ := by
        exact ⟨ D.hQ_prime _ _ ( D.hC_sub _ _ hi₁ hq₁ ), D.hQ_prime _ _ ( D.hC_sub _ _ hi₂ hq₂ ), D.hQ_prime _ _ ( D.hC_sub _ _ hi₃ hq₃ ), D.hQ_prime _ _ ( D.hC_sub _ _ hi₄ hq₄ ) ⟩;
      have := Nat.Prime.dvd_mul h_q_cases.1 |>.1 ( dvd_of_mul_right_eq _ ‹q₁ * q₂ = q₃ * q₄› ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
      cases this <;> simp_all +decide ;
      · aesop;
      · exact Or.inr ( mul_left_cancel₀ h_q_cases.1.ne_zero <| by linarith );
    cases h_q_cases <;> simp_all +decide [ mul_comm ];
    have h_contra : q₃ ∈ D.Q j₁ ∧ q₃ ∈ D.Q j₃ := by
      exact ⟨ D.hC_sub j₁ i₁ hi₁ hq₁, D.hC_sub j₃ i₃ hi₃ hq₃ ⟩;
    have := D.hQQ j₁ j₃; simp_all +decide [ Finset.disjoint_left ] ;
    by_cases h : j₁ = j₃ <;> simp_all +decide;
    · have := D.hC_inter j₃ i₁ hi₁ i₃ hi₃; simp_all +decide [ Finset.card_le_one ] ;
      grind +suggestions;
    · exact False.elim <| this h_contra.1 h_contra.2

set_option maxHeartbeats 1600000 in
theorem layered_block_product_sidon :
    IsMultiplicativeSidon D.fullSet := by
  intros a ha b hb c hc d hd h;
  by_cases haS : a ∈ D.S;
  · by_cases hcS : c ∈ D.S;
    · by_cases h_div_c : a ∣ c;
      · obtain ⟨ k, hk ⟩ := h_div_c;
        rcases k with ( _ | _ | k ) <;> simp_all +decide;
        · exact absurd ( D.hS_prime 0 hcS ) ( by norm_num );
        · have := D.hS_prime a haS; aesop;
        · have := D.hS_prime a haS; have := D.hS_prime ( a * ( k + 1 + 1 ) ) hcS; simp_all +decide [ Nat.prime_mul_iff ] ;
      · have h_div_d : a ∣ d := by
          exact Or.resolve_left ( Nat.Prime.dvd_mul ( D.hS_prime a haS ) |>.1 ( h ▸ dvd_mul_right _ _ ) ) h_div_c;
        have hdS : d ∈ D.S := by
          apply D.S_prime_dvd_fullSet haS hd h_div_d;
        have := D.hS_prime a haS; have := D.hS_prime c hcS; have := D.hS_prime d hdS; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
        nlinarith [ this.two_le ];
    · have h_ad : a ∣ d := by
        have h_ad : a ∣ c * d := by
          exact h ▸ dvd_mul_right _ _;
        by_cases hc_prod : c ∈ D.productSet;
        · exact Or.resolve_left ( Nat.Prime.dvd_mul ( D.hS_prime a haS ) |>.1 h_ad ) ( D.S_prime_not_dvd_product_elt haS hc_prod );
        · unfold BlockProductData.fullSet at hc; aesop;
      have := D.S_prime_dvd_fullSet haS hd h_ad;
      cases eq_or_ne a d <;> simp_all +decide [ BlockProductData.fullSet ];
      · exact Or.inr ( mul_left_cancel₀ ( Nat.ne_of_gt ( Nat.Prime.pos ( D.hS_prime _ ‹_› ) ) ) <| by linarith );
      · have := Nat.prime_dvd_prime_iff_eq ( D.hS_prime a haS ) ( D.hS_prime d ‹_› ) ; aesop;
  · by_cases hbS : b ∈ D.S;
    · have h_div : b ∣ c ∨ b ∣ d := by
        exact Nat.Prime.dvd_mul ( D.hS_prime b hbS ) |>.1 ( h ▸ dvd_mul_left _ _ );
      cases h_div <;> have := D.S_prime_dvd_fullSet hbS hc <;> have := D.S_prime_dvd_fullSet hbS hd <;> simp_all +decide ;
      · cases ‹b ∣ c› ; simp_all +decide ;
        have := D.hS_prime _ ‹_›; simp_all +decide [ Nat.prime_mul_iff ] ;
        cases this <;> simp_all +decide [ mul_comm b ];
        · aesop;
        · exact absurd ( D.hS_prime 1 hbS ) ( by norm_num );
      · cases ‹b ∣ d› ; simp_all +decide ;
        have := D.hS_prime _ this; simp_all +decide [ Nat.prime_mul_iff ] ;
        cases this <;> simp_all +decide;
        · aesop;
        · exact absurd ( D.hS_prime 1 hbS ) ( by norm_num );
    · by_cases hcS : c ∈ D.S;
      · have h_div : c ∣ a ∨ c ∣ b := by
          exact Nat.Prime.dvd_mul ( D.hS_prime c hcS ) |>.1 ( h.symm ▸ dvd_mul_right _ _ );
        have h_contra : a ∈ D.S ∧ b ∈ D.S := by
          exact ⟨ D.S_prime_dvd_fullSet hcS ha ( h_div.resolve_right fun h => hbS <| D.S_prime_dvd_fullSet hcS hb h ), D.S_prime_dvd_fullSet hcS hb ( h_div.resolve_left fun h => haS <| D.S_prime_dvd_fullSet hcS ha h ) ⟩;
        tauto;
      · by_cases hdS : d ∈ D.S;
        · have h_div : d ∣ a ∨ d ∣ b := by
            exact Nat.Prime.dvd_mul ( D.hS_prime d hdS ) |>.1 ( h.symm ▸ dvd_mul_left _ _ );
          cases h_div <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
          · have := D.S_prime_dvd_fullSet hdS ha ( Nat.dvd_of_mod_eq_zero ‹_› ) ; aesop;
          · have := D.S_prime_dvd_fullSet hdS hb ( Nat.dvd_of_mod_eq_zero ‹_› ) ; aesop;
        · simp_all +decide [ BlockProductData.fullSet ];
          exact D.sidon_case_all_product ‹_› ‹_› ‹_› ‹_› h

theorem layered_block_product_card :
    D.fullSet.card = D.S.card + ∑ j : Fin k, ∑ i ∈ D.I j, (D.C j i).card := by
  erw [ Finset.card_union_of_disjoint D.productSet_disjoint_S ];
  rw [ BlockProductData.productSet, Finset.card_biUnion ];
  · rw [ Finset.sum_congr rfl ];
    intro j hj; rw [ Finset.card_biUnion ] ;
    · rw [ Finset.sum_congr rfl ] ; intros ; rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( Nat.Prime.ne_zero ( D.hr_prime j _ ‹_› ) ) hxy ];
    · intros i hi i' hi' hij; simp_all +decide [ Finset.disjoint_left ] ;
      intro a ha x hx H; have := D.product_unique hi' hi hx ha; aesop;
  · intros j hj j' hj' hij; simp_all +decide [ Finset.disjoint_left ] ;
    rintro a x hx y hy rfl z hz t ht; have := D.product_unique hx ( hz ) hy ht; aesop;

-- ============================================================
-- § 5. Cutoff recursion and functional identity
-- ============================================================

/-- The cutoff recursion sequence -/
noncomputable def cutoffSeq : ℕ → ℝ
  | 0 => 2 / 3
  | n + 1 => 1 - Real.sqrt ((1 - cutoffSeq n) / (2 - cutoffSeq n))

lemma cutoffSeq_bounds : ∀ m : ℕ, 0 < cutoffSeq m ∧ cutoffSeq m < 1 := by
  intro m
  induction' m with m ih;
  · exact ⟨ by rw [ show cutoffSeq 0 = 2 / 3 by rfl ] ; norm_num, by rw [ show cutoffSeq 0 = 2 / 3 by rfl ] ; norm_num ⟩;
  · exact ⟨ sub_pos.2 <| by rw [ Real.sqrt_lt' ] <;> nlinarith [ mul_div_cancel₀ ( 1 - cutoffSeq m ) ( by linarith : ( 2 - cutoffSeq m ) ≠ 0 ) ], sub_lt_self _ <| Real.sqrt_pos.2 <| div_pos ( by linarith ) <| by linarith ⟩

lemma cutoffSeq_pos (m : ℕ) : 0 < cutoffSeq m := (cutoffSeq_bounds m).1

lemma cutoffSeq_lt_one (m : ℕ) : cutoffSeq m < 1 := (cutoffSeq_bounds m).2

lemma cutoffSeq_one : cutoffSeq 1 = 1 / 2 := by
  norm_num [ show cutoffSeq 1 = 1 - Real.sqrt ( ( 1 - cutoffSeq 0 ) / ( 2 - cutoffSeq 0 ) ) by rfl, show cutoffSeq 0 = 2 / 3 by rfl ]

lemma cutoffSeq_le_half : ∀ m : ℕ, 1 ≤ m → cutoffSeq m ≤ 1 / 2 := by
  intro m hm; induction hm <;> norm_num [ *, Nat.succ_eq_add_one ] ;
  · rw [ show cutoffSeq 1 = 1 / 2 from cutoffSeq_one ];
  · rw [ show cutoffSeq ( _ + 1 ) = 1 - Real.sqrt ( ( 1 - cutoffSeq _ ) / ( 2 - cutoffSeq _ ) ) by rfl ];
    rw [ sub_le_comm ];
    exact Real.le_sqrt_of_sq_le ( by rw [ le_div_iff₀ ] <;> linarith [ cutoffSeq_bounds ‹_› ] )

/-- F(x) = √(2-x) -/
noncomputable def bigF (x : ℝ) : ℝ := Real.sqrt (2 - x)

/-- f(x) = 1 - √((1-x)/(2-x)) -/
noncomputable def littlef (x : ℝ) : ℝ := 1 - Real.sqrt ((1 - x) / (2 - x))

theorem cutoff_functional_identity (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    bigF x = (1 - littlef x) * Real.sqrt (1 - x) +
      Real.sqrt (littlef x) * bigF (littlef x) := by
  unfold bigF littlef;
  rw [ ← Real.sqrt_mul ];
  · rw [ show ( 1 - Real.sqrt ( ( 1 - x ) / ( 2 - x ) ) ) * ( 2 - ( 1 - Real.sqrt ( ( 1 - x ) / ( 2 - x ) ) ) ) = ( 2 - x ) ⁻¹ by
          nlinarith [ Real.mul_self_sqrt ( show 0 ≤ ( 1 - x ) / ( 2 - x ) by exact div_nonneg ( by linarith ) ( by linarith ) ), Real.sqrt_nonneg ( ( 1 - x ) / ( 2 - x ) ), mul_div_cancel₀ ( 1 - x ) ( by linarith : ( 2 - x ) ≠ 0 ), inv_mul_cancel₀ ( by linarith : ( 2 - x ) ≠ 0 ) ] ] ; ring_nf;
    rw [ ← Real.sqrt_mul ( by nlinarith [ mul_inv_cancel₀ ( by linarith : ( 2 - x ) ≠ 0 ) ] ) ] ; ring_nf;
    rw [ show - ( x * ( 2 - x ) ⁻¹ * 2 ) + x ^ 2 * ( 2 - x ) ⁻¹ + ( 2 - x ) ⁻¹ = ( 2 - x ) ⁻¹ * ( 1 - x ) ^ 2 by nlinarith [ mul_inv_cancel₀ ( by linarith : ( 2 - x ) ≠ 0 ) ], Real.sqrt_mul ( by nlinarith [ mul_inv_cancel₀ ( by linarith : ( 2 - x ) ≠ 0 ) ] ), Real.sqrt_sq ( by nlinarith ) ] ; ring_nf;
    rw [ Real.sqrt_inv ] ; ring_nf;
    grind;
  · exact sub_nonneg.2 <| Real.sqrt_le_iff.2 ⟨ by norm_num, by rw [ div_le_iff₀ ] <;> linarith ⟩

-- ============================================================
-- § 6. Cutoff constants approaching the limit
-- ============================================================

/-- The partial product x_1 · x_2 · … · x_m -/
noncomputable def xProd : ℕ → ℝ
  | 0 => 1
  | m + 1 => xProd m * cutoffSeq (m + 1)

/-- The cutoff sequence a_j for a given k. -/
noncomputable def cutoffA (k : ℕ) (j : ℕ) : ℝ :=
  if j = 0 then 0
  else if j ≤ k then Real.sqrt (cutoffSeq 0) * xProd (k - j)
  else 0

lemma xProd_pos : ∀ m : ℕ, 0 < xProd m := by
  intro m;
  induction' m with m ih;
  · exact zero_lt_one;
  · exact mul_pos ih ( cutoffSeq_pos _ )

lemma cutoffA_pos (k : ℕ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    0 < cutoffA k j := by
  unfold cutoffA;
  rw [ if_neg ( by linarith ), if_pos hjk ] ; exact mul_pos ( Real.sqrt_pos.mpr ( by norm_num [ show cutoffSeq 0 = 2 / 3 by rfl ] ) ) ( xProd_pos _ ) ;

lemma cutoffA_lt_one (k : ℕ) (hk : 2 ≤ k) : cutoffA k k < 1 := by
  unfold cutoffA;
  norm_num [ show cutoffSeq 0 = 2 / 3 by rfl, show xProd 0 = 1 by rfl ];
  rw [ if_neg ( by linarith ), div_lt_one ] <;> norm_num

lemma cutoffA_increasing (k : ℕ) (j : ℕ) (hj : j < k) :
    cutoffA k j < cutoffA k (j + 1) := by
  unfold cutoffA;
  split_ifs <;> try linarith;
  · contradiction;
  · exact mul_pos ( Real.sqrt_pos.mpr ( cutoffSeq_pos _ ) ) ( xProd_pos _ );
  · contradiction;
  · rw [ show k - j = k - ( j + 1 ) + 1 by omega, show xProd ( k - ( j + 1 ) + 1 ) = xProd ( k - ( j + 1 ) ) * cutoffSeq ( k - ( j + 1 ) + 1 ) by rfl ] ; exact mul_lt_mul_of_pos_left ( mul_lt_of_lt_one_right ( xProd_pos _ ) ( cutoffSeq_lt_one _ ) ) ( Real.sqrt_pos.mpr ( show 0 < cutoffSeq 0 from by norm_num [ cutoffSeq ] ) ) ;

lemma cutoffA_zero : ∀ k, cutoffA k 0 = 0 := by
  intro; simp [cutoffA]

set_option maxHeartbeats 3200000 in
lemma cutoffA_db (k : ℕ) (hk : 2 ≤ k) (j : ℕ) (hj : j < k) :
    let a := cutoffA k
    let d := a (j + 1) - a j
    let b := if j < k - 1
      then 1 / a (j + 1) - 1 / a (j + 2)
      else 1 / a k - a k
    d ≤ b := by
  by_cases h : j < k - 1 <;> simp_all +decide;
  · by_cases hj0 : j = 0;
    · have h_case0 : (cutoffA k 1)^2 ≤ 1 - cutoffSeq (k - 1) := by
        have h_case0_bound : (cutoffA k 1)^2 ≤ (2 / 3) * (1 / 2)^(2 * (k - 1)) := by
          have h_case0_bound : (xProd (k - 1))^2 ≤ (1 / 2)^(2 * (k - 1)) := by
            have h_xProd_sq : ∀ m ≥ 1, xProd m ≤ (1 / 2)^m := by
              intro m hm; induction hm <;> simp_all +decide [ pow_succ, xProd ] ;
              · norm_num [ cutoffSeq_one ];
              · gcongr;
                · exact le_of_lt ( cutoffSeq_pos _ );
                · exact le_trans ( cutoffSeq_le_half _ ( by linarith ) ) ( by norm_num );
            simpa only [ pow_mul' ] using pow_le_pow_left₀ ( xProd_pos _ |> le_of_lt ) ( h_xProd_sq _ ( Nat.sub_pos_of_lt hk ) ) _;
          unfold cutoffA; norm_num [ h_case0_bound ] ; ring_nf; norm_num;
          rw [ if_pos ( by linarith ), Real.sq_sqrt ] <;> norm_num [ cutoffSeq ] ; ring_nf at * ; linarith;
        have h_case0_ge_half : 1 - cutoffSeq (k - 1) ≥ 1 / 2 := by
          linarith [ cutoffSeq_le_half ( k - 1 ) ( Nat.sub_pos_of_lt hk ) ];
        exact h_case0_bound.trans ( by linarith [ pow_le_pow_of_le_one ( by norm_num : ( 0 : ℝ ) ≤ 1 / 2 ) ( by norm_num ) ( show 2 * ( k - 1 ) ≥ 2 by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ] ) ] );
      have h_sub : cutoffA k 1 ≤ (1 - cutoffSeq (k - 1)) / cutoffA k 1 := by
        rw [ le_div_iff₀ ( cutoffA_pos k 1 ( by norm_num ) ( by linarith ) ) ] ; linarith;
      simp_all +decide [ cutoffA ];
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ xProd ];
      convert h_sub using 1 ; ring_nf;
      rw [ mul_inv_cancel₀ ( ne_of_gt ( cutoffSeq_pos _ ) ) ] ; ring;
    · have h_a_j1 : cutoffA k (j + 1) = Real.sqrt (cutoffSeq 0) * xProd (k - j - 1) := by
        unfold cutoffA; aesop;
      have h_a_j : cutoffA k j = Real.sqrt (cutoffSeq 0) * xProd (k - j) := by
        unfold cutoffA;
        rw [ if_neg hj0, if_pos hj.le ];
      have h_simplify : (cutoffA k (j + 1))^2 * (1 - cutoffSeq (k - j)) ≤ 1 - cutoffSeq (k - j - 1) := by
        have h_prod_bound : (cutoffA k (j + 1))^2 ≤ cutoffSeq 0 * (1 / 2)^(2 * (k - j - 1)) := by
          have h_prod_bound : xProd (k - j - 1) ≤ (1 / 2)^(k - j - 1) := by
            have h_prod_bound : ∀ m ≥ 1, xProd m ≤ (1 / 2)^m := by
              intro m hm; induction hm <;> simp_all +decide [ pow_succ, xProd ] ;
              · norm_num [ cutoffSeq_one ];
              · gcongr;
                · exact le_of_lt ( cutoffSeq_pos _ );
                · exact le_trans ( cutoffSeq_le_half _ ( by linarith ) ) ( by norm_num );
            exact h_prod_bound _ ( Nat.sub_pos_of_lt ( by omega ) );
          rw [ h_a_j1, mul_pow, Real.sq_sqrt <| by exact div_nonneg zero_le_two <| by norm_num ] ; convert mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by exact le_of_lt <| xProd_pos _ ) h_prod_bound 2 ) ( show 0 ≤ cutoffSeq 0 by exact div_nonneg zero_le_two <| by norm_num ) using 1 ; ring;
        have h_bounds : 1 - cutoffSeq (k - j) ≤ 1 ∧ 1 - cutoffSeq (k - j - 1) ≥ 1 / 2 := by
          exact ⟨ sub_le_self _ ( by exact le_of_lt ( cutoffSeq_pos _ ) ), by linarith [ show cutoffSeq ( k - j - 1 ) ≤ 1 / 2 from cutoffSeq_le_half _ ( Nat.sub_pos_of_lt ( by omega ) ) ] ⟩;
        refine le_trans ( mul_le_of_le_one_right ( sq_nonneg _ ) h_bounds.1 ) ?_;
        refine le_trans h_prod_bound ?_;
        refine le_trans ?_ h_bounds.2;
        exact le_trans ( mul_le_mul_of_nonneg_right ( show cutoffSeq 0 ≤ 1 by norm_num [ show cutoffSeq 0 = 2 / 3 by rfl ] ) ( by positivity ) ) ( by exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_of_le_one ( by positivity ) ( by norm_num ) ( show 2 * ( k - j - 1 ) ≥ 1 by omega ) ) ( by positivity ) ) ( by norm_num ) );
      have h_simplify_further : (cutoffA k (j + 1))^2 * (1 - cutoffSeq (k - j)) ≤ (cutoffA k (j + 1)) * (1 / cutoffA k (j + 1) - 1 / cutoffA k (j + 2)) := by
        have h_simplify_further : 1 / cutoffA k (j + 2) = cutoffSeq (k - j - 1) / cutoffA k (j + 1) := by
          rw [ div_eq_div_iff ] <;> norm_num [ h_a_j1, h_a_j ];
          · rw [ show cutoffA k ( j + 2 ) = Real.sqrt ( cutoffSeq 0 ) * xProd ( k - ( j + 2 ) ) from ?_ ];
            · rw [ show k - j - 1 = k - ( j + 2 ) + 1 by omega, show xProd ( k - ( j + 2 ) + 1 ) = xProd ( k - ( j + 2 ) ) * cutoffSeq ( k - ( j + 2 ) + 1 ) by rfl ] ; ring;
            · exact if_neg ( by linarith ) |> fun h => h.trans ( if_pos ( by omega ) );
          · exact ne_of_gt ( cutoffA_pos k ( j + 2 ) ( by linarith ) ( by omega ) );
          · exact ⟨ ne_of_gt <| Real.sqrt_pos.mpr <| by norm_num [ show cutoffSeq 0 = 2 / 3 by rfl ], ne_of_gt <| xProd_pos _ ⟩;
        rw [ h_simplify_further, div_sub_div, mul_div, le_div_iff₀ ] <;> nlinarith [ show 0 < cutoffA k ( j + 1 ) from cutoffA_pos k ( j + 1 ) ( by linarith ) ( by linarith ) ];
      have h_simplify_further : cutoffA k (j + 1) * (1 - cutoffSeq (k - j)) = cutoffA k (j + 1) - cutoffA k j := by
        rw [ h_a_j1, h_a_j ];
        rw [ show xProd ( k - j ) = xProd ( k - j - 1 ) * cutoffSeq ( k - j ) from ?_ ] ; ring;
        rcases n : k - j with ( _ | _ | n ) <;> simp_all +decide;
        · omega;
        · omega;
        · rfl;
      norm_num at *;
      nlinarith [ show 0 < cutoffA k ( j + 1 ) from cutoffA_pos k ( j + 1 ) ( by linarith ) ( by linarith ), mul_inv_cancel₀ ( ne_of_gt ( show 0 < cutoffA k ( j + 1 ) from cutoffA_pos k ( j + 1 ) ( by linarith ) ( by linarith ) ) ) ];
  · cases h.eq_or_lt <;> first | linarith | simp_all +decide ;
    unfold cutoffA; norm_num [ xProd ] ; ring_nf ;
    rw [ if_neg ( by linarith ) ] ; rw [ show cutoffSeq 0 = 2 / 3 by rfl ] ; rw [ show cutoffSeq 1 = 1 / 2 from cutoffSeq_one ] ; norm_num ; ring_nf ; norm_num;
    field_simp;
    norm_num

-- ============================================================
-- § 7. Convergence of the cutoff sum to Λ
-- ============================================================

lemma xProd_le_half_pow (m : ℕ) (hm : 1 ≤ m) : xProd m ≤ (1 / 2) ^ m := by
  induction' hm with m ih <;> norm_num [ pow_succ, mul_assoc ] at *;
  · norm_num [ xProd, cutoffSeq_one ];
  · exact mul_le_mul ‹_› ( cutoffSeq_le_half _ ( Nat.le_add_left _ _ ) ) ( by exact le_of_lt ( cutoffSeq_pos _ ) ) ( by positivity )

lemma iterated_bigF (n : ℕ) :
    bigF (cutoffSeq 0) =
      ∑ m ∈ Finset.range n,
        Real.sqrt (xProd m) * ((1 - cutoffSeq (m + 1)) * Real.sqrt (1 - cutoffSeq m)) +
      Real.sqrt (xProd n) * bigF (cutoffSeq n) := by
  induction' n with n ih;
  · norm_num [ xProd ];
  · rw [ Finset.sum_range_succ, ih ];
    have := cutoff_functional_identity ( cutoffSeq n ) ( show 0 ≤ cutoffSeq n from le_of_lt ( cutoffSeq_pos n ) ) ( show cutoffSeq n < 1 from cutoffSeq_lt_one n );
    rw [ this, show littlef ( cutoffSeq n ) = cutoffSeq ( n + 1 ) from ?_ ];
    · rw [ show xProd ( n + 1 ) = xProd n * cutoffSeq ( n + 1 ) by rfl, Real.sqrt_mul ( le_of_lt ( xProd_pos n ) ) ] ; ring;
    · rfl

lemma Lambda_eq_bigF :
    Lambda = 2 * Real.sqrt 2 * (cutoffSeq 0) ^ ((1 : ℝ) / 4) *
      bigF (cutoffSeq 0) := by
  unfold Lambda bigF cutoffSeq; norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul ] ; ring_nf;
  norm_num [ Real.div_rpow ] ; ring_nf;
  norm_num [ ← Real.rpow_add, ← Real.rpow_neg ] ; ring_nf;
  rw [ show ( 11 / 4 : ℝ ) = 3 / 4 + 2 by norm_num, show ( -3 / 4 : ℝ ) = -1 / 4 + -1 / 2 by norm_num, Real.rpow_add, Real.rpow_add ] <;> ring_nf <;> norm_num

lemma cutoffA_term_middle (k : ℕ) (hk : 2 ≤ k) (j : ℕ) (hj0 : 0 < j) (hjk : j < k - 1) :
    let m := k - j - 1
    (cutoffA k (j + 1) - cutoffA k j) *
      Real.sqrt (1 / cutoffA k (j + 1) - 1 / cutoffA k (j + 2)) =
    (cutoffSeq 0) ^ ((1 : ℝ) / 4) * Real.sqrt (xProd m) *
      (1 - cutoffSeq (m + 1)) * Real.sqrt (1 - cutoffSeq m) := by
  unfold cutoffA; norm_num;
  split_ifs <;> try omega;
  rw [ show k - j = k - ( j + 1 ) + 1 by omega ];
  rw [ show xProd ( k - ( j + 1 ) + 1 ) = xProd ( k - ( j + 1 ) ) * cutoffSeq ( k - ( j + 1 ) + 1 ) from rfl ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( xProd_pos _ ), ne_of_gt ( cutoffSeq_pos _ ) ];
  rw [ show xProd ( k - ( j + 2 ) ) = xProd ( k - ( j + 1 ) ) / cutoffSeq ( k - ( j + 1 ) ) from ?_ ];
  · field_simp;
    rw [ Real.sqrt_div ( by linarith [ show cutoffSeq ( k - ( j + 1 ) ) ≤ 1 from by linarith [ show cutoffSeq ( k - ( j + 1 ) ) < 1 from cutoffSeq_lt_one _ ] ] ) ];
    rw [ Real.sqrt_mul ( le_of_lt ( xProd_pos _ ) ) ];
    rw [ show ( cutoffSeq 0 : ℝ ) ^ ( 1 / 4 : ℝ ) = Real.sqrt ( Real.sqrt ( cutoffSeq 0 ) ) by rw [ Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ( by exact le_of_lt ( cutoffSeq_pos 0 ) ) ] ; norm_num ] ; ring_nf;
    grind;
  · rw [ eq_div_iff ( ne_of_gt ( cutoffSeq_pos _ ) ) ];
    rw [ show k - ( j + 1 ) = k - ( j + 2 ) + 1 by omega, show xProd ( k - ( j + 2 ) + 1 ) = xProd ( k - ( j + 2 ) ) * cutoffSeq ( k - ( j + 2 ) + 1 ) from rfl ]

lemma cutoffA_term_first (k : ℕ) (hk : 2 ≤ k) :
    cutoffA k 1 * Real.sqrt (1 / cutoffA k 1 - 1 / cutoffA k 2) =
    (cutoffSeq 0) ^ ((1 : ℝ) / 4) * Real.sqrt (xProd (k - 1)) *
      Real.sqrt (1 - cutoffSeq (k - 1)) := by
  rcases k with ( _ | _ | k ) <;> norm_num [ cutoffA, xProd ] at *;
  rw [ ← sq_eq_sq₀ ];
  · norm_num [ mul_pow, Real.sq_sqrt ( show 0 ≤ cutoffSeq 0 by exact le_of_lt ( cutoffSeq_pos _ ) ) ];
    rw [ Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt ];
    · rw [ show ( cutoffSeq 0 ^ ( 1 / 4 : ℝ ) ) ^ 2 = cutoffSeq 0 ^ ( 1 / 2 : ℝ ) by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by exact le_of_lt ( cutoffSeq_pos 0 ) ) ] ; norm_num ] ; rw [ show ( cutoffSeq 0 ^ ( 1 / 2 : ℝ ) ) = Real.sqrt ( cutoffSeq 0 ) by rw [ Real.sqrt_eq_rpow ] ] ; ring_nf;
      grind;
    · exact sub_nonneg.2 ( le_of_lt ( cutoffSeq_lt_one _ ) );
    · exact mul_nonneg ( le_of_lt ( xProd_pos k ) ) ( le_of_lt ( cutoffSeq_pos _ ) );
    · norm_num [ sub_nonneg ];
      exact mul_le_mul_of_nonneg_right ( le_mul_of_one_le_left ( by exact inv_nonneg.2 ( xProd_pos _ |> le_of_lt ) ) ( by rw [ inv_eq_one_div, le_div_iff₀ ( cutoffSeq_pos _ ) ] ; linarith [ show cutoffSeq ( k + 1 ) ≤ 1 / 2 from cutoffSeq_le_half _ ( Nat.succ_pos _ ) ] ) ) ( by exact inv_nonneg.2 ( Real.sqrt_nonneg _ ) );
  · exact mul_nonneg ( mul_nonneg ( Real.sqrt_nonneg _ ) ( mul_nonneg ( le_of_lt ( xProd_pos _ ) ) ( le_of_lt ( cutoffSeq_pos _ ) ) ) ) ( Real.sqrt_nonneg _ );
  · exact mul_nonneg ( mul_nonneg ( Real.rpow_nonneg ( by exact le_of_lt ( cutoffSeq_pos _ ) ) _ ) ( Real.sqrt_nonneg _ ) ) ( Real.sqrt_nonneg _ )

lemma cutoffA_term_last (k : ℕ) (hk : 2 ≤ k) :
    (cutoffA k k - cutoffA k (k - 1)) *
      Real.sqrt (1 / cutoffA k k - cutoffA k k) =
    (cutoffSeq 0) ^ ((1 : ℝ) / 4) * (1 - cutoffSeq 1) *
      Real.sqrt (1 - cutoffSeq 0) := by
  unfold cutoffA; rcases k with ( _ | _ | k ) <;> norm_num at *;
  rw [ show xProd 1 = xProd 0 * cutoffSeq 1 from rfl, show xProd 0 = 1 from rfl ] ; ring_nf;
  rw [ show cutoffSeq 0 = 2 / 3 by rfl, show cutoffSeq 1 = 1 / 2 from cutoffSeq_one ] ; norm_num ; ring_nf;
  rw [ ← sq_eq_sq₀ ] <;> ring_nf <;> norm_num;
  · rw [ Real.sq_sqrt ] <;> ring_nf <;> norm_num;
    · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ; ring_nf;
      rw [ ← Real.sqrt_eq_rpow ] ; norm_num [ ← div_eq_mul_inv, ← Real.sqrt_div_self ] ; ring_nf;
      rw [ ← Real.sqrt_div_self ] ; ring;
    · rw [ ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ ] <;> norm_num;
  · positivity

lemma cutoffA_sum_formula (k : ℕ) (hk : 2 ≤ k) :
    ∑ j ∈ Finset.range k,
      (cutoffA k (j + 1) - cutoffA k j) *
      Real.sqrt (if j < k - 1
        then 1 / cutoffA k (j + 1) - 1 / cutoffA k (j + 2)
        else 1 / cutoffA k k - cutoffA k k) =
    (cutoffSeq 0) ^ ((1 : ℝ) / 4) *
      (∑ m ∈ Finset.range (k - 1),
        Real.sqrt (xProd m) * ((1 - cutoffSeq (m + 1)) *
          Real.sqrt (1 - cutoffSeq m)) +
      Real.sqrt (xProd (k - 1)) * Real.sqrt (1 - cutoffSeq (k - 1))) := by
  have h_split : ∑ j ∈ Finset.range k, (cutoffA k (j + 1) - cutoffA k j) * Real.sqrt (if j < k - 1 then 1 / cutoffA k (j + 1) - 1 / cutoffA k (j + 2) else 1 / cutoffA k k - cutoffA k k) = (∑ j ∈ Finset.range (k - 1), (cutoffA k (j + 1) - cutoffA k j) * Real.sqrt (1 / cutoffA k (j + 1) - 1 / cutoffA k (j + 2))) + (cutoffA k k - cutoffA k (k - 1)) * Real.sqrt (1 / cutoffA k k - cutoffA k k) := by
    cases k <;> simp_all +decide [ Finset.sum_range_succ ];
    exact Finset.sum_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_range.mp hx ) ] ;
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.sum_range_succ' ];
  have h_middle : ∀ j ∈ Finset.range k, (cutoffA (k + 2) (j + 2) - cutoffA (k + 2) (j + 1)) * Real.sqrt ((cutoffA (k + 2) (j + 2))⁻¹ - (cutoffA (k + 2) (j + 3))⁻¹) = (cutoffSeq 0) ^ (1 / 4 : ℝ) * Real.sqrt (xProd (k - j)) * (1 - cutoffSeq (k - j + 1)) * Real.sqrt (1 - cutoffSeq (k - j)) := by
    intros j hj;
    convert cutoffA_term_middle ( k + 2 ) ( by linarith ) ( j + 1 ) ( by linarith [ Finset.mem_range.mp hj ] ) ( by linarith [ Finset.mem_range.mp hj, Nat.sub_add_cancel ( by linarith [ Finset.mem_range.mp hj ] : 1 ≤ k + 2 ) ] ) using 1 ; ring_nf;
    grind;
  rw [ Finset.sum_congr rfl h_middle ];
  rw [ show ( ∑ x ∈ Finset.range k, cutoffSeq 0 ^ ( 1 / 4 : ℝ ) * Real.sqrt ( xProd ( k - x ) ) * ( 1 - cutoffSeq ( k - x + 1 ) ) * Real.sqrt ( 1 - cutoffSeq ( k - x ) ) ) = ( ∑ x ∈ Finset.range k, cutoffSeq 0 ^ ( 1 / 4 : ℝ ) * Real.sqrt ( xProd ( x + 1 ) ) * ( 1 - cutoffSeq ( x + 1 + 1 ) ) * Real.sqrt ( 1 - cutoffSeq ( x + 1 ) ) ) from ?_ ];
  · rw [ show ( cutoffA ( k + 1 + 1 ) 1 - cutoffA ( k + 1 + 1 ) 0 ) * Real.sqrt ( ( cutoffA ( k + 1 + 1 ) 1 ) ⁻¹ - ( cutoffA ( k + 1 + 1 ) 2 ) ⁻¹ ) = cutoffSeq 0 ^ ( 1 / 4 : ℝ ) * Real.sqrt ( xProd ( k + 1 ) ) * Real.sqrt ( 1 - cutoffSeq ( k + 1 ) ) from ?_ ];
    · rw [ show ( cutoffA ( k + 1 + 1 ) ( k + 1 + 1 ) - cutoffA ( k + 1 + 1 ) ( k + 1 ) ) * Real.sqrt ( ( cutoffA ( k + 1 + 1 ) ( k + 1 + 1 ) ) ⁻¹ - cutoffA ( k + 1 + 1 ) ( k + 1 + 1 ) ) = cutoffSeq 0 ^ ( 1 / 4 : ℝ ) * ( 1 - cutoffSeq 1 ) * Real.sqrt ( 1 - cutoffSeq 0 ) from ?_ ];
      · norm_num [ mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        norm_num [ xProd ] ; ring;
      · grind +suggestions;
    · convert cutoffA_term_first ( k + 2 ) ( by linarith ) using 1;
      unfold cutoffA; norm_num;
      exact Or.inl rfl;
  · rw [ ← Finset.sum_range_reflect ];
    exact Finset.sum_congr rfl fun x hx => by rw [ tsub_tsub, tsub_tsub_cancel_of_le ( by linarith [ Finset.mem_range.mp hx ] ) ] ; ring_nf;

lemma cutoffA_sum_eq_Lambda_minus_error (k : ℕ) (hk : 2 ≤ k) :
    2 * ∑ j ∈ Finset.range k,
      (cutoffA k (j + 1) - cutoffA k j) *
      Real.sqrt (2 * (if j < k - 1
        then 1 / cutoffA k (j + 1) - 1 / cutoffA k (j + 2)
        else 1 / cutoffA k k - cutoffA k k)) =
    Lambda - 2 * Real.sqrt 2 * (cutoffSeq 0) ^ ((1 : ℝ) / 4) *
      Real.sqrt (xProd (k - 1)) *
      (bigF (cutoffSeq (k - 1)) - Real.sqrt (1 - cutoffSeq (k - 1))) := by
  convert congr_arg ( fun x : ℝ => 2 * Real.sqrt 2 * x ) ( cutoffA_sum_formula k hk ) using 1;
  · norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    exact Finset.sum_congr rfl fun x hx => by split_ifs <;> norm_num;
  · rw [ Lambda_eq_bigF, iterated_bigF ] ; ring

private lemma bigF_minus_sqrt_le_sqrt2 (m : ℕ) :
    bigF (cutoffSeq m) - Real.sqrt (1 - cutoffSeq m) ≤ Real.sqrt 2 := by
  exact le_trans ( sub_le_self _ <| Real.sqrt_nonneg _ ) <| Real.sqrt_le_sqrt <| by linarith [ cutoffSeq_pos m, cutoffSeq_lt_one m ] ;

lemma cutoffA_sum_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    Lambda - 4 * (2 / 3 : ℝ) ^ ((1 : ℝ) / 4) * ((1 : ℝ) / Real.sqrt 2) ^ (k - 1) ≤
    2 * ∑ j ∈ Finset.range k,
      (cutoffA k (j + 1) - cutoffA k j) *
      Real.sqrt (2 * (if j < k - 1
        then 1 / cutoffA k (j + 1) - 1 / cutoffA k (j + 2)
        else 1 / cutoffA k k - cutoffA k k)) := by
  have h_Sk_ge_Lambda_minus_error : 2 * ∑ j ∈ Finset.range k, (cutoffA k (j + 1) - cutoffA k j) * Real.sqrt (2 * (if j < k - 1 then 1 / cutoffA k (j + 1) - 1 / cutoffA k (j + 2) else 1 / cutoffA k k - cutoffA k k)) ≥ Lambda - 2 * Real.sqrt 2 * (cutoffSeq 0) ^ ((1 : ℝ) / 4) * Real.sqrt (xProd (k - 1)) * Real.sqrt 2 := by
    rw [cutoffA_sum_eq_Lambda_minus_error k hk];
    gcongr;
    · exact mul_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( Real.sqrt_nonneg _ ) ) ( Real.rpow_nonneg ( by norm_num [ show cutoffSeq 0 = 2 / 3 by rfl ] ) _ ) ) ( Real.sqrt_nonneg _ );
    · exact bigF_minus_sqrt_le_sqrt2 _;
  refine le_trans ?_ h_Sk_ge_Lambda_minus_error;
  have h_sqrt_xProd_le : Real.sqrt (xProd (k - 1)) ≤ (1 / Real.sqrt 2) ^ (k - 1) := by
    have h_xProd_le_pow : xProd (k - 1) ≤ (1 / 2) ^ (k - 1) := by
      exact xProd_le_half_pow _ ( Nat.sub_pos_of_lt hk );
    convert Real.sqrt_le_sqrt h_xProd_le_pow using 1 ; norm_num;
    norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul, ← Real.rpow_natCast ];
    norm_num [ Real.div_rpow, mul_comm ];
  rw [ show cutoffSeq 0 = 2 / 3 by rfl ] ; ring_nf at * ; norm_num at *;
  nlinarith [ show 0 < ( 2 / 3 : ℝ ) ^ ( 1 / 4 : ℝ ) by positivity ]

theorem cutoff_constants_exist (γ : ℝ) (hγ : γ < Lambda) :
    ∃ (k : ℕ) (a : ℕ → ℝ),
      2 ≤ k ∧
      a 0 = 0 ∧
      (∀ j : ℕ, j < k → a j < a (j + 1)) ∧
      a k < 1 ∧
      (∀ j : ℕ, j < k → 0 < a (j + 1)) ∧
      (∀ j : ℕ, j < k →
        let d := a (j + 1) - a j
        let b := if j < k - 1
          then 1 / a (j + 1) - 1 / a (j + 2)
          else 1 / a k - a k
        d ≤ b) ∧
      γ < 2 * ∑ j ∈ Finset.range k,
        (a (j + 1) - a j) * Real.sqrt (2 * (
          if j < k - 1
          then 1 / a (j + 1) - 1 / a (j + 2)
          else 1 / a k - a k)) := by
  have hε : 0 < Lambda - γ := by linarith
  have hr : (1 : ℝ) / Real.sqrt 2 < 1 := by
    rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  have hr0 : 0 ≤ (1 : ℝ) / Real.sqrt 2 := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr
  have hC : 0 < 4 * (2 / 3 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (div_pos hε hC) hr
  set k := max (M + 1) 2 with hk_def
  refine ⟨k, cutoffA k, le_max_right _ _, cutoffA_zero k, fun j hj => cutoffA_increasing k j hj,
    cutoffA_lt_one k (le_max_right _ _), fun j hj => cutoffA_pos k (j+1) (by omega) (by omega),
    fun j hj => cutoffA_db k (le_max_right _ _) j hj, ?_⟩
  calc γ = Lambda - (Lambda - γ) := by ring
    _ < Lambda - 4 * (2 / 3 : ℝ) ^ ((1:ℝ)/4) * ((1:ℝ) / Real.sqrt 2) ^ (k - 1) := by
        have hk1 : M ≤ k - 1 := by omega
        have hpow : ((1:ℝ) / Real.sqrt 2) ^ (k - 1) ≤ ((1:ℝ) / Real.sqrt 2) ^ M :=
          pow_le_pow_of_le_one hr0 hr.le hk1
        have : ((1:ℝ) / Real.sqrt 2) ^ (k - 1) * (4 * (2/3:ℝ)^((1:ℝ)/4)) < Lambda - γ := by
          calc _ ≤ ((1:ℝ) / Real.sqrt 2) ^ M * (4 * (2/3:ℝ)^((1:ℝ)/4)) := by
                  exact mul_le_mul_of_nonneg_right hpow (by positivity)
            _ < (Lambda - γ) / (4 * (2/3:ℝ)^((1:ℝ)/4)) * (4 * (2/3:ℝ)^((1:ℝ)/4)) := by
                  exact mul_lt_mul_of_pos_right hM hC
            _ = Lambda - γ := by field_simp
        linarith
    _ ≤ _ := cutoffA_sum_lower_bound k (le_max_right _ _)

-- ============================================================
-- § 8. Near-square prime values
-- ============================================================

lemma primes_in_interval_large (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (pnt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x) :
    ∀ᶠ (y : ℝ) in atTop,
      ∃ p : ℕ, Nat.Prime p ∧ α * y ≤ (p : ℝ) ∧ (p : ℝ) ≤ y := by
  obtain ⟨ c, hc, h ⟩ := pnt;
  have h_diff : ∀ᶠ y in atTop, (Nat.primeCounting ⌊y⌋₊ - Nat.primeCounting ⌊α * y⌋₊ : ℝ) > 0 := by
    have h_approx : Filter.Tendsto (fun y : ℝ => ((1 + c y) * y / Real.log y - (1 + c (α * y)) * α * y / Real.log (α * y)) / (y / Real.log y)) Filter.atTop (nhds (1 - α)) := by
      suffices h_simplify : Filter.Tendsto (fun y : ℝ => (1 + c y) - (1 + c (α * y)) * α * (Real.log y / Real.log (α * y))) Filter.atTop (nhds (1 - α)) by
        refine h_simplify.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with y hy;
        field_simp;
        rw [ mul_sub, mul_div_cancel₀ _ ( ne_of_gt ( Real.log_pos hy ) ) ] ; ring;
      have h_log_ratio : Filter.Tendsto (fun y : ℝ => Real.log y / Real.log (α * y)) Filter.atTop (nhds 1) := by
        suffices h_log_simplified : Filter.Tendsto (fun y : ℝ => Real.log y / (Real.log α + Real.log y)) Filter.atTop (nhds 1) by
          refine h_log_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ Real.log_mul hα0.ne' hy.ne' ] );
        suffices h_div : Filter.Tendsto (fun y : ℝ => 1 / (Real.log α / Real.log y + 1)) Filter.atTop (nhds 1) by
          refine h_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with y hy using by rw [ div_add_one, div_div_eq_mul_div ] ; ring ; linarith [ Real.log_pos hy ] );
        exact le_trans ( tendsto_const_nhds.div ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) tendsto_const_nhds ) ( by norm_num ) ) ( by norm_num );
      have h_c_alpha_y : Filter.Tendsto (fun y : ℝ => c (α * y)) Filter.atTop (nhds 0) := by
        rw [ Asymptotics.isLittleO_iff_tendsto' ] at hc;
        · simpa using hc.comp ( Filter.tendsto_id.const_mul_atTop hα0 );
        · norm_num;
      convert Filter.Tendsto.sub ( tendsto_const_nhds.add ( hc.tendsto_div_nhds_zero ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.mul ( tendsto_const_nhds.add h_c_alpha_y ) tendsto_const_nhds ) h_log_ratio ) using 2 ; norm_num;
      exacts [ rfl, by ring ];
    have := h_approx.eventually ( lt_mem_nhds <| show 1 - α > 0 by linarith );
    filter_upwards [ this, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
    rw [ lt_div_iff₀ ( div_pos ( by positivity ) ( Real.log_pos hx₂ ) ) ] at hx₁;
    grind;
  filter_upwards [ h_diff, Filter.eventually_gt_atTop 1 ] with y hy₁ hy₂;
  contrapose! hy₁;
  simp +decide [ Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range ];
  refine Finset.card_mono ?_;
  intro p hp; simp_all +decide;
  exact Nat.le_floor <| le_of_not_gt fun h => by linarith [ hy₁ p hp.2 <| by linarith, Nat.floor_le <| show 0 ≤ y by positivity, show ( p : ℝ ) ≤ ⌊y⌋₊ by exact_mod_cast hp.1 ] ;

theorem near_square_prime_values (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (pnt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ p : ℕ, Nat.Prime p ∧
        (1 - δ) * T ≤ ↑(p * (p + 1) + 1) ∧
        ↑(p * (p + 1) + 1) ≤ T := by
  obtain ⟨α, hα0, hα1, hαδ⟩ : ∃ α : ℝ, 0 < α ∧ α < 1 ∧ α^2 ≥ 1 - δ := by
    exact ⟨ Real.sqrt ( 1 - δ ), Real.sqrt_pos.2 ( by linarith ), by rw [ Real.sqrt_lt' ] <;> linarith, by rw [ Real.sq_sqrt ] ; linarith ⟩;
  have h_y : ∀ᶠ T in atTop, ∃ p : ℕ, Nat.Prime p ∧ α * ((-1 + Real.sqrt (4 * T - 3)) / 2) ≤ p ∧ p ≤ ((-1 + Real.sqrt (4 * T - 3)) / 2) := by
    have := primes_in_interval_large α hα0 hα1 pnt;
    rw [ Filter.eventually_atTop ] at *;
    obtain ⟨ a, ha ⟩ := this; use ( a + 1 ) ^ 2 + 1; intro b hb; specialize ha ( ( -1 + Real.sqrt ( 4 * b - 3 ) ) / 2 ) ( by nlinarith [ Real.sqrt_nonneg ( 4 * b - 3 ), Real.mul_self_sqrt ( show 0 <= 4 * b - 3 by nlinarith ) ] ) ; aesop;
  simp +zetaDelta at *;
  obtain ⟨ T₀, hT₀ ⟩ := h_y; use Max.max T₀ 3; intro T hT; obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := hT₀ T ( le_trans ( le_max_left _ _ ) hT ) ; refine' ⟨ p, hp₁, _, _ ⟩;
  · have h_lower_bound : (p : ℝ) * (p + 1) + 1 ≥ α^2 * ((-1 + Real.sqrt (4 * T - 3)) / 2)^2 + α * ((-1 + Real.sqrt (4 * T - 3)) / 2) + 1 := by
      nlinarith [ show 0 ≤ α * ( ( -1 + Real.sqrt ( 4 * T - 3 ) ) / 2 ) by exact mul_nonneg hα0.le ( div_nonneg ( by nlinarith [ Real.sqrt_nonneg ( 4 * T - 3 ), Real.mul_self_sqrt ( show 0 ≤ 4 * T - 3 by linarith [ le_max_right T₀ 3 ] ) ] ) zero_le_two ) ];
    nlinarith [ Real.sqrt_nonneg ( 4 * T - 3 ), Real.mul_self_sqrt ( show 0 ≤ 4 * T - 3 by linarith [ le_max_right T₀ 3 ] ) ];
  · nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 4 * T - 3 by linarith [ le_max_right T₀ 3 ] ) ]

-- ============================================================
-- § 9. PNT consequences
-- ============================================================

lemma pnt_lower_bound (α : ℝ) (hα : 0 < α) (ε : ℝ) (hε : 0 < ε)
    (pnt : ∃ c : ℝ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      (2 * α - ε) * Real.sqrt n / Real.log n ≤
        (Nat.primeCounting ⌊α * Real.sqrt n⌋₊ : ℝ) := by
  obtain ⟨ c, hc, h ⟩ := pnt;
  have h_bound : Filter.Tendsto (fun n : ℕ => (Nat.primeCounting (Nat.floor (α * Real.sqrt n)) : ℝ) * Real.log n / (Real.sqrt n)) Filter.atTop (nhds (2 * α)) := by
    have h_pnt : Filter.Tendsto (fun n : ℕ => (Nat.primeCounting (Nat.floor (α * Real.sqrt n)) : ℝ) * Real.log (α * Real.sqrt n) / (α * Real.sqrt n)) Filter.atTop (nhds 1) := by
      have h_pnt : Filter.Tendsto (fun x : ℝ => (Nat.primeCounting (Nat.floor x) : ℝ) * Real.log x / x) Filter.atTop (nhds 1) := by
        have h_c_zero : Filter.Tendsto c Filter.atTop (nhds 0) := by
          simpa using hc.tendsto_div_nhds_zero;
        rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ h x, div_mul_cancel₀ _ ( ne_of_gt <| Real.log_pos hx ), mul_div_cancel_right₀ _ <| ne_of_gt <| zero_lt_one.trans hx ] ) ] ; simpa using h_c_zero.const_add 1;
      exact h_pnt.comp <| Filter.Tendsto.const_mul_atTop hα <| by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop;
    have h_log : Filter.Tendsto (fun n : ℕ => Real.log (α * Real.sqrt n) / Real.log n) Filter.atTop (nhds (1 / 2)) := by
      have h_log : Filter.Tendsto (fun n : ℕ => (Real.log α + (1 / 2) * Real.log n) / Real.log n) Filter.atTop (nhds (1 / 2)) := by
        ring_nf;
        exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ( Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx; rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hx ) ) ) ] ) tendsto_const_nhds ) ) ( by norm_num );
      refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] ; ring );
    have := h_pnt.div h_log;
    convert this ( by norm_num ) |> Filter.Tendsto.const_mul ( α : ℝ ) using 2 <;> norm_num ; ring_nf;
    · grind +suggestions;
    · ring;
  have := h_bound.eventually ( lt_mem_nhds <| show 2 * α > 2 * α - ε by linarith );
  filter_upwards [ this, Filter.eventually_gt_atTop 1 ] with n hn hn' using by rw [ div_le_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr hn' ) ] ; rw [ lt_div_iff₀ ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| pos_of_gt hn' ) ] at hn; linarith;

set_option maxHeartbeats 3200000 in
private lemma pnt_upper_bound (α : ℝ) (hα : 0 < α) (ε : ℝ) (hε : 0 < ε)
    (pnt : ∃ c : ℝ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      (Nat.primeCounting ⌊α * Real.sqrt n⌋₊ : ℝ) ≤
        (2 * α + ε) * Real.sqrt n / Real.log n := by
  obtain ⟨c, hc_o, hc⟩ := pnt;
  have h_c_zero : Filter.Tendsto (fun n : ℕ => c (α * Real.sqrt n)) Filter.atTop (nhds 0) := by
    rw [ Asymptotics.isLittleO_iff_tendsto' ] at hc_o;
    · simpa using hc_o.comp ( Filter.Tendsto.const_mul_atTop hα <| by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
    · norm_num;
  have h_log_bound : ∀ᶠ n : ℕ in Filter.atTop, Real.log (α * Real.sqrt n) ≥ (1 - ε / (4 * α + 2 * ε)) * (1 / 2) * Real.log n := by
    suffices h_log_bound : ∀ᶠ n : ℕ in Filter.atTop, Real.log α + (1 / 2) * Real.log n ≥ (1 - ε / (4 * α + 2 * ε)) * (1 / 2) * Real.log n by
      filter_upwards [ h_log_bound, Filter.eventually_gt_atTop 0 ] with n hn hn' using by rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] ; linarith;
    have h_log_growth : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop := by
      exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop;
    filter_upwards [ h_log_growth.eventually_gt_atTop ( 2 * |Real.log α| / ( ε / ( 4 * α + 2 * ε ) ) ) ] with n hn using by cases abs_cases ( Real.log α ) <;> nlinarith [ show 0 < ε / ( 4 * α + 2 * ε ) by positivity, mul_div_cancel₀ ( 2 * |Real.log α| ) ( show ε / ( 4 * α + 2 * ε ) ≠ 0 by positivity ) ] ;
  have h_c_bound : ∀ᶠ n : ℕ in Filter.atTop, 1 + c (α * Real.sqrt n) ≤ 1 + ε / (4 * α + 2 * ε) := by
    exact h_c_zero.eventually ( ge_mem_nhds <| show 0 < ε / ( 4 * α + 2 * ε ) by positivity ) |> fun h => h.mono fun n hn => by linarith;
  filter_upwards [ h_log_bound, h_c_bound, Filter.eventually_gt_atTop 1 ] with n hn₁ hn₂ hn₃;
  rw [ hc, div_le_div_iff₀ ];
  · field_simp at *;
    nlinarith [ mul_pos hα hε, mul_pos hα ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast ) ), mul_pos hε ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast ) ) ];
  · exact lt_of_lt_of_le ( mul_pos ( mul_pos ( sub_pos.mpr <| by rw [ div_lt_iff₀ <| by positivity ] ; linarith ) <| by positivity ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn₃ ) hn₁;
  · exact Real.log_pos <| Nat.one_lt_cast.mpr hn₃

lemma pnt_interval_lower (α β : ℝ) (hα : 0 < α) (hβ : α < β) (ε : ℝ) (hε : 0 < ε)
    (pnt : ∃ c : ℝ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      (2 * (β - α) - ε) * Real.sqrt n / Real.log n ≤
        ((Nat.primeCounting ⌊β * Real.sqrt n⌋₊ : ℝ) -
         (Nat.primeCounting ⌊α * Real.sqrt n⌋₊ : ℝ)) := by
  have h_pnt_lower_bound := pnt_lower_bound β ( by linarith ) ( ε / 2 ) ( half_pos hε ) pnt;
  have h_pnt_upper_bound := pnt_upper_bound α hα ( ε / 2 ) ( half_pos hε ) pnt;
  filter_upwards [ h_pnt_lower_bound, h_pnt_upper_bound ] with n hn₁ hn₂ using by ring_nf at *; linarith;

-- ============================================================
-- § 10. Helper lemmas for prime supply
-- ============================================================

lemma choose_epsilon_for_sum
    (k : ℕ) (hk : 1 ≤ k)
    (d b : Fin k → ℝ)
    (hd : ∀ j, 0 < d j)
    (hb : ∀ j, 0 < b j)
    (L η : ℝ) (hη : 0 < η)
    (hL : L = 2 * ∑ j : Fin k, d j * Real.sqrt (2 * b j)) :
    ∃ ε > 0,
      (∀ j, 2 * d j - 2 * ε > 0) ∧
      (∀ j, 2 * b j - ε / 2 > 0) ∧
      (∀ j, d j - ε > 0) ∧
      L - η < 2 * ∑ j : Fin k, (d j - ε) * Real.sqrt (2 * b j - ε / 2) := by
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ > 0, (∀ j, 2 * d j - 2 * ε₁ > 0) ∧ (∀ j, 2 * b j - ε₁ / 2 > 0) ∧ (∀ j, d j - ε₁ > 0) := by
    obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ > 0, ∀ j, ε₁ < min (d j) (min (2 * b j) (d j)) := by
      obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ > 0, ∀ j, ε₁ ≤ min (d j) (min (2 * b j) (d j)) := by
        exact ⟨ Finset.min' ( Finset.univ.image fun j => Min.min ( d j ) ( Min.min ( 2 * b j ) ( d j ) ) ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ⟨ 0, hk ⟩ ) ⟩, by have := Finset.min'_mem ( Finset.univ.image fun j => Min.min ( d j ) ( Min.min ( 2 * b j ) ( d j ) ) ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ⟨ 0, hk ⟩ ) ⟩ ; aesop, fun j => Finset.min'_le _ _ <| Finset.mem_image_of_mem _ <| Finset.mem_univ _ ⟩;
      exact ⟨ ε₁ / 2, half_pos hε₁.1, fun j => by linarith [ hε₁.2 j, show 0 < min ( d j ) ( min ( 2 * b j ) ( d j ) ) from lt_min ( hd j ) ( lt_min ( mul_pos zero_lt_two ( hb j ) ) ( hd j ) ) ] ⟩;
    exact ⟨ ε₁, hε₁.1, fun j => by linarith [ hε₁.2 j, min_le_left ( d j ) ( min ( 2 * b j ) ( d j ) ), min_le_right ( d j ) ( min ( 2 * b j ) ( d j ) ), min_le_left ( 2 * b j ) ( d j ), min_le_right ( 2 * b j ) ( d j ) ], fun j => by linarith [ hε₁.2 j, min_le_left ( d j ) ( min ( 2 * b j ) ( d j ) ), min_le_right ( d j ) ( min ( 2 * b j ) ( d j ) ), min_le_left ( 2 * b j ) ( d j ), min_le_right ( 2 * b j ) ( d j ) ], fun j => by linarith [ hε₁.2 j, min_le_left ( d j ) ( min ( 2 * b j ) ( d j ) ), min_le_right ( d j ) ( min ( 2 * b j ) ( d j ) ), min_le_left ( 2 * b j ) ( d j ), min_le_right ( 2 * b j ) ( d j ) ] ⟩;
  have h_cont : Filter.Tendsto (fun ε => 2 * ∑ j, (d j - ε) * Real.sqrt (2 * b j - ε / 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * ∑ j, d j * Real.sqrt (2 * b j))) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
  have := h_cont.eventually ( lt_mem_nhds <| show 2 * ∑ j, d j * Real.sqrt ( 2 * b j ) > L - η by linarith );
  rcases ( this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, hε₁.1 ⟩ ) ) with h ; obtain ⟨ ε₂, hε₂₁, hε₂₂ ⟩ := h.exists ; exact ⟨ ε₂, hε₂₂.1, fun j => by linarith [ hε₁.2.1 j, hε₂₂.2 ], fun j => by linarith [ hε₁.2.2.1 j, hε₂₂.2 ], fun j => by linarith [ hε₁.2.2.2 j, hε₂₂.2 ], hε₂₁ ⟩

lemma sqrt_div_log_tendsto_atTop :
    Filter.Tendsto (fun n : ℕ => Real.sqrt n / Real.log n) Filter.atTop Filter.atTop := by
  suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp (u / 2) / u) Filter.atTop Filter.atTop by
    have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
  suffices h_y : Filter.Tendsto (fun y : ℝ => Real.exp y / (2 * y)) Filter.atTop Filter.atTop by
    convert h_y.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 2 : ℝ ) ⁻¹ ) ) using 2 ; norm_num ; ring_nf;
  ring_nf;
  exact Filter.Tendsto.atTop_mul_const ( by norm_num ) ( by simpa using Real.tendsto_exp_div_pow_atTop 1 )

-- ============================================================
-- § 11. Supply conditions verification helpers
-- ============================================================

lemma nat_le_sub_of_real_le {v π_upper π_lower : ℕ}
    (h_le : π_lower ≤ π_upper)
    (h : (v : ℝ) ≤ (π_upper : ℝ) - (π_lower : ℝ)) :
    v ≤ π_upper - π_lower := by
  have : (v : ℝ) ≤ (π_upper - π_lower : ℕ) := by
    push_cast [Nat.cast_sub h_le]; exact h
  exact_mod_cast this

lemma prime_plus_one_gt_sqrt_rho (p₀ : ℕ) (hp : Nat.Prime p₀) :
    Real.sqrt (p₀ * (p₀ + 1) + 1 : ℕ) < (p₀ : ℝ) + 1 := by
  rw [ Real.sqrt_lt' ] <;> norm_cast <;> nlinarith [ hp.two_le ]

-- ============================================================
-- § 12. Sum bound
-- ============================================================

private lemma product_term_lower_bound
    (d_j b_j : ℝ) (v_j p_j : ℕ) (ε Xn : ℝ)
    (hXn_pos : 0 < Xn)
    (hε_Xn : 1 ≤ ε * Xn)
    (hd_ε : 0 < d_j - ε)
    (hb_ε : 0 < 2 * b_j - ε / 2)
    (hvs : (v_j : ℝ) ≥ (2 * d_j - ε) * Xn - 1)
    (hps : (p_j : ℝ) + 1 > Real.sqrt ((2 * b_j - ε / 2) * Xn)) :
    (v_j : ℝ) * ((p_j : ℝ) + 1) ≥
      2 * (d_j - ε) * Real.sqrt (2 * b_j - ε / 2) * Xn * Real.sqrt Xn := by
  refine' le_trans _ ( mul_le_mul_of_nonneg_right ( show ( v_j : ℝ ) ≥ 2 * ( d_j - ε ) * Xn from _ ) ( by positivity ) );
  · rw [ show ( 2 * ( d_j - ε ) * Real.sqrt ( 2 * b_j - ε / 2 ) * Xn * Real.sqrt Xn ) = ( 2 * ( d_j - ε ) * Xn ) * ( Real.sqrt ( 2 * b_j - ε / 2 ) * Real.sqrt Xn ) by ring ];
    exact mul_le_mul_of_nonneg_left ( by rw [ ← Real.sqrt_mul hb_ε.le ] ; exact hps.le ) ( by nlinarith );
  · nlinarith

lemma sum_bound_from_parts
    (k : ℕ)
    (d b : Fin k → ℝ)
    (vs ps : Fin k → ℕ)
    (ε Xn L η : ℝ)
    (hXn_pos : 0 < Xn)
    (hε_Xn : 1 ≤ ε * Xn)
    (hd_ε : ∀ j : Fin k, 0 < d j - ε)
    (hb_ε : ∀ j : Fin k, 0 < 2 * b j - ε / 2)
    (hvs : ∀ j : Fin k, (vs j : ℝ) ≥ (2 * d j - ε) * Xn - 1)
    (hps : ∀ j : Fin k, (ps j : ℝ) + 1 > Real.sqrt ((2 * b j - ε / 2) * Xn))
    (hε_sum : L - η < 2 * ∑ j : Fin k, (d j - ε) * Real.sqrt (2 * b j - ε / 2))
    (n : ℕ) (hn : 2 ≤ n)
    (hXn_eq : Xn = Real.sqrt n / Real.log n) :
    (L - η) * (n : ℝ) ^ ((3:ℝ)/4) / (Real.log n) ^ ((3:ℝ)/2) ≤
      ∑ j : Fin k, ((vs j : ℝ) * ((ps j : ℝ) + 1)) := by
  have h_term_bound : ∀ j, (vs j * (ps j + 1) : ℝ) ≥ 2 * (d j - ε) * Real.sqrt (2 * b j - ε / 2) * Xn * Real.sqrt Xn := by
    intro j; exact product_term_lower_bound (d j) (b j) (vs j) (ps j) ε Xn hXn_pos hε_Xn (hd_ε j) (hb_ε j) (hvs j) (hps j);
  refine le_trans ?_ ( Finset.sum_le_sum fun j _ => h_term_bound j );
  convert mul_le_mul_of_nonneg_right hε_sum.le ( show 0 ≤ Xn * Real.sqrt Xn by positivity ) using 1 <;> ring_nf;
  · rw [ hXn_eq, Real.sqrt_div ( by positivity ), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
    rw [ show ( 3 / 4 : ℝ ) = 1 / 2 + 1 / 4 by norm_num, show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.sqrt_eq_rpow, Real.rpow_add ( by positivity ), Real.rpow_add ( by exact Real.log_pos <| Nat.one_lt_cast.mpr hn ) ] ; norm_num ; ring;
  · rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by ring;

-- ============================================================
-- § 13. Layered prime supply
-- ============================================================

private lemma choose_delta_for_bounds
    (k : ℕ) (hk : 1 ≤ k) (b : Fin k → ℝ) (hb : ∀ j, 0 < b j)
    (ε : ℝ) (hε : 0 < ε) (hbε : ∀ j, 2 * b j - ε / 2 > 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ j : Fin k, (1 - δ) * (2 * b j - ε / 4) ≥ 2 * b j - ε / 2 := by
  use ε / (8 * (sSup (Set.range b)) + 1)
  refine' ⟨ div_pos hε ( by linarith [ show 0 ≤ sSup ( Set.range b ) by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ j, rfl ⟩ ; exact le_of_lt ( hb j ) ] ), _, _ ⟩
  · rw [ div_lt_iff₀ ] <;> linarith [ show sSup ( Set.range b ) ≥ b ⟨ 0, hk ⟩ from le_csSup ( Set.finite_range b |> Set.Finite.bddAbove ) ( Set.mem_range_self _ ), hbε ⟨ 0, hk ⟩ ]
  · intro j; nlinarith [ hbε j, hb j, show ( sSup ( Set.range b ) : ℝ ) ≥ b j from le_csSup ( Set.finite_range b |> Set.Finite.bddAbove ) ( Set.mem_range_self j ), mul_div_cancel₀ ε ( by linarith [ show ( sSup ( Set.range b ) : ℝ ) ≥ b j from le_csSup ( Set.finite_range b |> Set.Finite.bddAbove ) ( Set.mem_range_self j ), hb j ] : ( 8 * sSup ( Set.range b ) + 1 ) ≠ 0 ) ]

private lemma all_d_intervals_eventually_large
    (k : ℕ) (hk : 1 ≤ k) (a : ℕ → ℝ)
    (ha_pos : ∀ j : ℕ, j < k → 0 < a (j + 1))
    (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    (ha0 : a 0 = 0)
    (ε : ℝ) (hε : 0 < ε)
    (pnt : ∃ c : ℝ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ j : Fin k,
        (2 * (a (j.val + 1) - a j.val) - ε) * Real.sqrt n / Real.log n ≤
          ((Nat.primeCounting ⌊a (j.val + 1) * Real.sqrt n⌋₊ : ℝ) -
           (Nat.primeCounting ⌊a j.val * Real.sqrt n⌋₊ : ℝ)) := by
  have h_pnt_lower_bound : ∀ j : Fin k, ∀ᶠ (n : ℕ) in Filter.atTop, (2 * (a (j.val + 1) - a j.val) - ε) * Real.sqrt n / Real.log n ≤ (Nat.primeCounting ⌊a (j.val + 1) * Real.sqrt n⌋₊ : ℝ) - (Nat.primeCounting ⌊a j.val * Real.sqrt n⌋₊ : ℝ) := by
    intro j
    by_cases hj : j.val = 0
    · have := pnt_lower_bound ( a 1 ) ( by linarith [ ha_pos 0 hk ] ) ε hε pnt; aesop
    · apply_rules [ pnt_interval_lower ]
      · induction' j with j ih
        induction' j with j ih
        · contradiction
        · exact ha_pos _ ( Nat.lt_of_succ_lt ih )
      · exact j.2
  exact Filter.eventually_all.mpr h_pnt_lower_bound

private lemma all_R_intervals_eventually_large
    (k : ℕ) (hk : 1 ≤ k) (a : ℕ → ℝ)
    (ha_pos : ∀ j : ℕ, j < k → 0 < a (j + 1))
    (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    (hak : a k < 1)
    (T : ℝ)
    (pnt : ∃ c : ℝ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ j : Fin k,
        T ≤ (Nat.primeCounting ⌊(if (j : ℕ) < k - 1
          then 1 / a (j.val + 1)
          else 1 / a k) * Real.sqrt n⌋₊ : ℝ) -
        (Nat.primeCounting ⌊(if (j : ℕ) < k - 1
          then 1 / a (j.val + 2)
          else a k) * Real.sqrt n⌋₊ : ℝ) := by
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ j : Fin k, 2 * (if j.val < k - 1 then 1 / a (j.val + 1) - 1 / a (j.val + 2) else 1 / a k - a k) - ε > 0 := by
    have h_pos : ∀ j : Fin k, 0 < 2 * (if j.val < k - 1 then 1 / a (j.val + 1) - 1 / a (j.val + 2) else 1 / a k - a k) := by
      intro j; split_ifs <;> simp_all +decide
      · exact inv_strictAnti₀ ( ha_pos _ ( by linarith [ Fin.is_lt j ] ) ) ( ha_inc _ ( by linarith [ Fin.is_lt j, Nat.sub_add_cancel hk ] ) )
      · rcases k with ( _ | _ | k ) <;> simp_all +decide
        · nlinarith [ inv_mul_cancel₀ ha_pos.ne' ]
        · nlinarith [ ha_pos ( k + 1 ) le_rfl, mul_inv_cancel₀ ( ne_of_gt ( ha_pos ( k + 1 ) le_rfl ) ) ]
    have h_min_pos : ∃ j : Fin k, ∀ i : Fin k, 2 * (if i.val < k - 1 then 1 / a (i.val + 1) - 1 / a (i.val + 2) else 1 / a k - a k) ≥ 2 * (if j.val < k - 1 then 1 / a (j.val + 1) - 1 / a (j.val + 2) else 1 / a k - a k) := by
      simpa using Finset.exists_min_image Finset.univ ( fun i : Fin k => 2 * if i.val < k - 1 then 1 / a ( i.val + 1 ) - 1 / a ( i.val + 2 ) else 1 / a k - a k ) ⟨ ⟨ 0, hk ⟩, Finset.mem_univ _ ⟩
    exact ⟨ ( 2 * if h_min_pos.choose.val < k - 1 then 1 / a ( h_min_pos.choose.val + 1 ) - 1 / a ( h_min_pos.choose.val + 2 ) else 1 / a k - a k ) / 2, half_pos ( h_pos _ ), fun j => by linarith [ h_min_pos.choose_spec j, h_pos j ] ⟩
  have h_eventually : ∀ j : Fin k, ∀ᶠ (n : ℕ) in Filter.atTop, T ≤ (Nat.primeCounting ⌊(if j.val < k - 1 then 1 / a (j.val + 1) else 1 / a k) * Real.sqrt n⌋₊ : ℝ) - (Nat.primeCounting ⌊(if j.val < k - 1 then 1 / a (j.val + 2) else a k) * Real.sqrt n⌋₊ : ℝ) := by
    intro j
    have h_eventually : ∀ᶠ (n : ℕ) in Filter.atTop, (2 * (if j.val < k - 1 then 1 / a (j.val + 1) - 1 / a (j.val + 2) else 1 / a k - a k) - ε) * Real.sqrt n / Real.log n ≥ T := by
      have h_eventually : Filter.Tendsto (fun n : ℕ => (Real.sqrt n / Real.log n)) Filter.atTop Filter.atTop := by
        exact sqrt_div_log_tendsto_atTop
      simpa only [ mul_div_assoc ] using h_eventually.const_mul_atTop ( hε j ) |> fun h => h.eventually_ge_atTop T
    filter_upwards [ h_eventually, pnt_interval_lower ( if j.val < k - 1 then 1 / a ( j.val + 2 ) else a k ) ( if j.val < k - 1 then 1 / a ( j.val + 1 ) else 1 / a k ) ( by
      split_ifs <;> simp_all +decide
      · exact ha_pos _ ( by omega )
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ Fin.forall_fin_succ ] ) ( by
      grind +locals ) ε hε_pos pnt ] with n hn hn'
    split_ifs at * <;> linarith
  exact Filter.eventually_all.mpr h_eventually

private lemma all_R_intervals_quantitative_lower
    (k : ℕ) (hk : 1 ≤ k) (a : ℕ → ℝ)
    (ha_pos : ∀ j : ℕ, j < k → 0 < a (j + 1))
    (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    (hak : a k < 1)
    (ε : ℝ) (hε : 0 < ε)
    (pnt : ∃ c : ℝ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x)
    (b : Fin k → ℝ)
    (hb_def : ∀ j : Fin k, b j = if (j : ℕ) < k - 1
      then 1 / a (j.val + 1) - 1 / a (j.val + 2)
      else 1 / a k - a k) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ j : Fin k,
        (2 * b j - ε) * Real.sqrt n / Real.log n ≤
          ((Nat.primeCounting ⌊(if (j : ℕ) < k - 1
            then 1 / a (j.val + 1)
            else 1 / a k) * Real.sqrt n⌋₊ : ℝ) -
           (Nat.primeCounting ⌊(if (j : ℕ) < k - 1
            then 1 / a (j.val + 2)
            else a k) * Real.sqrt n⌋₊ : ℝ)) := by
  refine' Filter.eventually_all.mpr fun j => _
  split_ifs <;> simp_all +decide
  · convert pnt_interval_lower ( ( a ( j + 2 ) ) ⁻¹ ) ( ( a ( j + 1 ) ) ⁻¹ ) _ _ ε hε using 1
    · aesop
    · exact inv_pos.mpr ( ha_pos _ ( by omega ) )
    · exact inv_strictAnti₀ ( ha_pos _ ( by linarith [ Fin.is_lt j, Nat.sub_add_cancel hk ] ) ) ( ha_inc _ ( by linarith [ Fin.is_lt j, Nat.sub_add_cancel hk ] ) )
  · split_ifs
    · omega
    · have := pnt_interval_lower ( a k ) ( ( a k ) ⁻¹ ) ?_ ?_ ε hε ?_
      · exact Filter.eventually_atTop.mp this
      · grind
      · nlinarith [ inv_mul_cancel₀ ( show a k ≠ 0 from ne_of_gt ( show 0 < a k from by
                                                                    rcases k with ( _ | _ | k ) <;> aesop ) ), show 0 < a k from by
                                                                                                    rcases k with ( _ | _ | k ) <;> aesop ]
      · exact ⟨ pnt.choose, by simpa using pnt.choose_spec.1, pnt.choose_spec.2 ⟩

private lemma b_pos_of_d_le_b (k : ℕ) (a : ℕ → ℝ)
    (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    (hdb : ∀ j : ℕ, j < k →
      let d := a (j + 1) - a j
      let b := if j < k - 1
        then 1 / a (j + 1) - 1 / a (j + 2)
        else 1 / a k - a k
      d ≤ b)
    (b : Fin k → ℝ)
    (hb_def : ∀ j : Fin k, b j = if (j : ℕ) < k - 1
      then 1 / a (j.val + 1) - 1 / a (j.val + 2)
      else 1 / a k - a k) :
    ∀ j : Fin k, 0 < b j := by
  intro j
  rw [hb_def]
  have hd_pos : 0 < a (j.val + 1) - a j.val := by linarith [ha_inc j.val j.isLt]
  have := hdb j.val j.isLt
  simp only at this
  split_ifs at this ⊢ <;> linarith

theorem layered_prime_supply
    (k : ℕ) (hk : 1 ≤ k)
    (a : ℕ → ℝ)
    (ha0 : a 0 = 0)
    (ha_pos : ∀ j : ℕ, j < k → 0 < a (j + 1))
    (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    (hak : a k < 1)
    (hdb : ∀ j : ℕ, j < k →
      let d := a (j + 1) - a j
      let b := if j < k - 1
        then 1 / a (j + 1) - 1 / a (j + 2)
        else 1 / a k - a k
      d ≤ b)
    (L : ℝ)
    (hL : L = 2 * ∑ j ∈ Finset.range k,
      (a (j + 1) - a j) * Real.sqrt (2 * (
        if j < k - 1
        then 1 / a (j + 1) - 1 / a (j + 2)
        else 1 / a k - a k)))
    (η : ℝ) (hη : 0 < η)
    (pnt : ∃ c : ℝ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ (ps vs : Fin k → ℕ),
        (∀ j, Nat.Prime (ps j)) ∧
        (∀ j, vs j ≤ Nat.primeCounting ⌊a (j.val + 1) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊a j.val * Real.sqrt n⌋₊) ∧
        (∀ j, vs j ≤ ps j * (ps j + 1) + 1) ∧
        (∀ j : Fin k, (j : ℕ) < k - 1 →
          ps j * (ps j + 1) + 1 ≤
          Nat.primeCounting ⌊(1 / a (j.val + 1)) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊(1 / a (j.val + 2)) * Real.sqrt n⌋₊) ∧
        (ps ⟨k-1, by omega⟩ * (ps ⟨k-1, by omega⟩ + 1) + 1 ≤
          Nat.primeCounting ⌊(1 / a k) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊a k * Real.sqrt n⌋₊) ∧
        ((L - η) * (n : ℝ) ^ ((3:ℝ)/4) / (Real.log n) ^ ((3:ℝ)/2) ≤
          ∑ j : Fin k, ((vs j : ℝ) * ((ps j : ℝ) + 1))) := by
  set d : Fin k → ℝ := fun j => a (j.val + 1) - a j.val with hd_def
  set b : Fin k → ℝ := fun j => if (j : ℕ) < k - 1
    then 1 / a (j.val + 1) - 1 / a (j.val + 2)
    else 1 / a k - a k with hb_def_eq
  have hb_def : ∀ j : Fin k, b j = if (j : ℕ) < k - 1
    then 1 / a (j.val + 1) - 1 / a (j.val + 2)
    else 1 / a k - a k := by intro j; rfl
  have hd_pos : ∀ j : Fin k, 0 < d j := by
    intro j; simp [hd_def]; linarith [ha_inc j.val j.isLt]
  have hb_pos : ∀ j : Fin k, 0 < b j :=
    b_pos_of_d_le_b k a ha_inc hdb b hb_def
  have hdb_fin : ∀ j : Fin k, d j ≤ b j := by
    intro j
    have := hdb j.val j.isLt
    simp only [hd_def, hb_def_eq]
    split_ifs with h
    all_goals (split_ifs at this; omega)
  have hL' : L = 2 * ∑ j : Fin k, d j * Real.sqrt (2 * b j) := by
    rw [hL, Finset.sum_range]
  obtain ⟨ε, hε_pos, hε_d, hε_b, hε_dε, hε_sum⟩ :=
    choose_epsilon_for_sum k hk d b hd_pos hb_pos L η hη hL'
  obtain ⟨δ, hδ_pos, hδ_lt1, hδ_bound⟩ :=
    choose_delta_for_bounds k hk b hb_pos ε hε_pos hε_b
  obtain ⟨T₀, hT₀⟩ := near_square_prime_values δ hδ_pos hδ_lt1 pnt
  have h_ev1 := all_R_intervals_eventually_large k hk a ha_pos ha_inc hak T₀ pnt
  have h_ev2 := all_d_intervals_eventually_large k hk a ha_pos ha_inc ha0 (ε / 2) (by linarith) pnt
  have h_ev3 := all_R_intervals_quantitative_lower k hk a ha_pos ha_inc hak (ε / 4) (by linarith) pnt b hb_def
  have h_ev4 : ∀ᶠ (n : ℕ) in Filter.atTop, 1 ≤ ε * (Real.sqrt n / Real.log n) := by
    have := sqrt_div_log_tendsto_atTop.const_mul_atTop hε_pos
    simpa [mul_div_assoc] using (this.eventually_ge_atTop 1)
  rw [Filter.eventually_atTop] at h_ev1 h_ev2 h_ev3 h_ev4
  obtain ⟨N₁, hN₁⟩ := h_ev1
  obtain ⟨N₂, hN₂⟩ := h_ev2
  obtain ⟨N₃, hN₃⟩ := h_ev3
  obtain ⟨N₄, hN₄⟩ := h_ev4
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) 2), fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ ≤ n := by omega
  have hn₃ : N₃ ≤ n := by omega
  have hn₄ : N₄ ≤ n := by omega
  have hn_ge2 : 2 ≤ n := by omega
  have h_R_large := hN₁ n hn₁
  have h_d_large := hN₂ n hn₂
  have h_R_quant := hN₃ n hn₃
  set R : Fin k → ℝ := fun j =>
    (Nat.primeCounting ⌊(if (j : ℕ) < k - 1
      then 1 / a (j.val + 1) else 1 / a k) * Real.sqrt n⌋₊ : ℝ) -
    (Nat.primeCounting ⌊(if (j : ℕ) < k - 1
      then 1 / a (j.val + 2) else a k) * Real.sqrt n⌋₊ : ℝ) with hR_def
  have h_prime_exists : ∀ j : Fin k, ∃ p : ℕ, Nat.Prime p ∧
      (1 - δ) * R j ≤ ↑(p * (p + 1) + 1) ∧ ↑(p * (p + 1) + 1) ≤ R j := by
    intro j; exact hT₀ (R j) (h_R_large j)
  set ps : Fin k → ℕ := fun j => (h_prime_exists j).choose with hps_def
  have hps_prime : ∀ j, Nat.Prime (ps j) := fun j => (h_prime_exists j).choose_spec.1
  have hps_lower : ∀ j, (1 - δ) * R j ≤ ↑(ps j * (ps j + 1) + 1) :=
    fun j => (h_prime_exists j).choose_spec.2.1
  have hps_upper : ∀ j, ↑(ps j * (ps j + 1) + 1) ≤ R j :=
    fun j => (h_prime_exists j).choose_spec.2.2
  set Xn := Real.sqrt n / Real.log n with hXn_def
  set vs : Fin k → ℕ := fun j => ⌊(2 * d j - ε) * Xn⌋₊ with hvs_def
  have hXn_pos : 0 < Xn := by
    exact div_pos (Real.sqrt_pos.mpr (by positivity)) (Real.log_pos (by exact_mod_cast hn_ge2))
  have hd_ε_pos : ∀ j : Fin k, 0 < 2 * d j - ε := by
    intro j; linarith [hε_dε j]
  have hR_lower : ∀ j : Fin k, (2 * b j - ε / 4) * Xn ≤ R j := by
    intro j; have := h_R_quant j; simp [hR_def, mul_div_assoc] at this ⊢; linarith
  have hρ_lower : ∀ j : Fin k, (2 * b j - ε / 2) * Xn ≤ ↑(ps j * (ps j + 1) + 1) := by
    intro j
    calc (2 * b j - ε / 2) * Xn
        ≤ (1 - δ) * ((2 * b j - ε / 4) * Xn) := by nlinarith [hδ_bound j]
      _ ≤ (1 - δ) * R j := by nlinarith [hR_lower j, hδ_pos]
      _ ≤ ↑(ps j * (ps j + 1) + 1) := hps_lower j
  have hvs_le_real : ∀ j : Fin k, (vs j : ℝ) ≤ (2 * d j - ε) * Xn := by
    intro j; exact Nat.floor_le (le_of_lt (mul_pos (hd_ε_pos j) hXn_pos))
  have hπ_mono : ∀ j : Fin k,
      Nat.primeCounting ⌊a j.val * Real.sqrt n⌋₊ ≤
      Nat.primeCounting ⌊a (j.val + 1) * Real.sqrt n⌋₊ := by
    intro j
    apply Nat.count_monotone Nat.Prime
    apply Nat.succ_le_succ
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_right (le_of_lt (ha_inc j.val j.isLt))
    exact Real.sqrt_nonneg _
  refine ⟨ps, vs, hps_prime, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    apply nat_le_sub_of_real_le (hπ_mono j)
    calc (vs j : ℝ) ≤ (2 * d j - ε) * Xn := hvs_le_real j
      _ ≤ (2 * (a (↑j + 1) - a ↑j) - ε / 2) * (Real.sqrt ↑n / Real.log ↑n) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hXn_pos)
          nlinarith [hε_pos]
      _ = (2 * (a (↑j + 1) - a ↑j) - ε / 2) * Real.sqrt ↑n / Real.log ↑n := by ring
      _ ≤ _ := h_d_large j
  · intro j
    have h1 := hvs_le_real j
    have h2 : (2 * d j - ε) * Xn ≤ (2 * b j - ε / 2) * Xn := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hXn_pos)
      nlinarith [hdb_fin j, hε_pos]
    have h3 := hρ_lower j
    have h4 : (vs j : ℝ) ≤ ↑(ps j * (ps j + 1) + 1) := by
      calc (vs j : ℝ) ≤ (2 * d j - ε) * Xn := h1
        _ ≤ (2 * b j - ε / 2) * Xn := h2
        _ ≤ ↑(ps j * (ps j + 1) + 1) := h3
    exact_mod_cast h4
  · intro j hj
    have h_upper := hps_upper j
    simp only [hR_def, if_pos hj] at h_upper
    apply nat_le_sub_of_real_le
    · apply Nat.count_monotone Nat.Prime
      apply Nat.succ_le_succ
      apply Nat.floor_mono
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      have : 0 < a (↑j + 1) := ha_pos ↑j (by omega)
      have : a (↑j + 1) ≤ a (↑j + 2) := le_of_lt (ha_inc (↑j + 1) (by omega))
      exact one_div_le_one_div_of_le ‹_› ‹_›
    · exact_mod_cast h_upper
  · have h_upper := hps_upper ⟨k - 1, by omega⟩
    simp only [hR_def, show ¬((k - 1 : ℕ) < k - 1) from by omega] at h_upper
    apply nat_le_sub_of_real_le
    · apply Nat.count_monotone Nat.Prime
      apply Nat.succ_le_succ
      apply Nat.floor_mono
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hak_pos : 0 < a k := by
        have h1 := ha_pos (k - 1) (by omega)
        have h2 := ha_inc (k - 1) (by omega)
        have : k - 1 + 1 = k := by omega
        rw [this] at h1; exact h1
      rw [le_div_iff₀ hak_pos]
      nlinarith [hak]
    · exact_mod_cast h_upper
  · have hε_Xn : 1 ≤ ε * Xn := hN₄ n hn₄
    have hvs_floor_lower : ∀ j : Fin k, (vs j : ℝ) ≥ (2 * d j - ε) * Xn - 1 := by
      intro j; exact (Nat.sub_one_lt_floor ((2 * d j - ε) * Xn)).le
    have hps_sqrt_lower : ∀ j : Fin k, (ps j : ℝ) + 1 > Real.sqrt ((2 * b j - ε / 2) * Xn) := by
      intro j
      have h1 := prime_plus_one_gt_sqrt_rho (ps j) (hps_prime j)
      have h2 := hρ_lower j
      calc (ps j : ℝ) + 1 > Real.sqrt (ps j * (ps j + 1) + 1 : ℕ) := h1
        _ ≥ Real.sqrt ((2 * b j - ε / 2) * Xn) := by
            apply Real.sqrt_le_sqrt; exact_mod_cast h2
    exact sum_bound_from_parts k d b vs ps ε Xn L η hXn_pos hε_Xn
      hε_dε hε_b hvs_floor_lower hps_sqrt_lower hε_sum n hn_ge2 rfl

-- ============================================================
-- § 14. Assembly of the product-Sidon set
-- ============================================================

private lemma cutoff_mono {a : ℕ → ℝ} {k : ℕ} (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ k) : a i ≤ a j := by
  induction' hij with j _ ih
  · rfl
  · exact le_trans (ih (Nat.le_of_succ_le hj)) (le_of_lt (ha_inc _ (Nat.lt_of_succ_le hj)))

private lemma exists_finset_superset_card_eq (S : Finset ℕ) (m : ℕ) (hm : S.card ≤ m) :
    ∃ T : Finset ℕ, S ⊆ T ∧ T.card = m :=
  Infinite.exists_superset_card_eq S m hm

private lemma sum_inter_eq_card_mul (I X : Finset ℕ) (D : ℕ → Finset ℕ) (Q : Finset ℕ) (p : ℕ)
    (hQ_sub : Q ⊆ X)
    (_hD_sub : ∀ i ∈ I, D i ⊆ X)
    (hincidence : ∀ x ∈ X, (I.filter (fun i => x ∈ D i)).card = p + 1) :
    ∑ i ∈ I, (D i ∩ Q).card = Q.card * (p + 1) := by
  have hsum_iter : ∑ i ∈ I, #(D i ∩ Q) = ∑ i ∈ I, ∑ x ∈ Q, (if x ∈ D i then 1 else 0) := by
    congr 1; ext i; simp [inter_comm]
  rw [hsum_iter, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun x hx => by simpa using hincidence x (hQ_sub hx)]
  simp

private lemma floor_product_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ⌊x * Real.sqrt ↑n⌋₊ * ⌊(1 / x) * Real.sqrt ↑n⌋₊ ≤ n := by
  have h_mul : (⌊x * Real.sqrt n⌋₊ : ℝ) * (⌊(1 / x) * Real.sqrt n⌋₊ : ℝ) ≤
      (x * Real.sqrt n) * ((1 / x) * Real.sqrt n) :=
    mul_le_mul (Nat.floor_le (by positivity)) (Nat.floor_le (by positivity))
      (by positivity) (by positivity)
  have : x * Real.sqrt ↑n * ((1 / x) * Real.sqrt ↑n) = ↑n := by
    field_simp; ring_nf; exact Real.sq_sqrt (by positivity)
  rw [this] at h_mul
  exact_mod_cast h_mul

private lemma sum_fin_via_orderEmb {S : Finset ℕ} {m : ℕ} (hm : S.card = m)
    (f : ℕ → ℕ) :
    ∑ i : Fin m, f ((S.orderEmbOfFin hm) i) = ∑ i ∈ S, f i := by
  refine' Finset.sum_bij ( fun x _ => S.orderEmbOfFin hm x ) _ _ _ _ <;> simp +decide;
  intro b hb; have := Finset.mem_image.mp ( show b ∈ Finset.image ( fun x : Fin m => S.orderEmbOfFin hm x ) Finset.univ from by aesop ) ; aesop;

noncomputable def rowLo (k : ℕ) (a : ℕ → ℝ) (n : ℕ) (j : ℕ) : ℕ :=
  if j < k - 1 then ⌊(1 / a (j + 2)) * Real.sqrt ↑n⌋₊ else ⌊a k * Real.sqrt ↑n⌋₊

private lemma extract_row_primes_tight
    (k : ℕ) (hk : 2 ≤ k) (a : ℕ → ℝ)
    (ha_pos : ∀ j : ℕ, j < k → 0 < a (j + 1))
    (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    (hak : a k < 1) (n : ℕ)
    (ps : Fin k → ℕ)
    (hR : ∀ j : Fin k, (j : ℕ) < k - 1 →
          ps j * (ps j + 1) + 1 ≤
          Nat.primeCounting ⌊(1 / a (j.val + 1)) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊(1 / a (j.val + 2)) * Real.sqrt n⌋₊)
    (hR_last : ps ⟨k-1, by omega⟩ * (ps ⟨k-1, by omega⟩ + 1) + 1 ≤
          Nat.primeCounting ⌊(1 / a k) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊a k * Real.sqrt n⌋₊)
    (j : Fin k) :
    ∃ Rj : Finset ℕ, Rj.card = ps j * (ps j + 1) + 1 ∧
      (∀ p ∈ Rj, Nat.Prime p ∧ rowLo k a n j.val < p ∧
        p ≤ ⌊(1 / a (j.val + 1)) * Real.sqrt ↑n⌋₊) := by
  by_cases hj : j.val < k - 1 <;> simp_all +decide [ rowLo ];
  · have := hR j hj
    generalize_proofs at *;
    have := extract_primes ( ⌊ ( a ( j + 2 ) ) ⁻¹ * Real.sqrt n⌋₊ ) ( ⌊ ( a ( j + 1 ) ) ⁻¹ * Real.sqrt n⌋₊ ) ( ps j * ( ps j + 1 ) + 1 ) ?_ ?_ <;> norm_num at *;
    · exact this;
    · contrapose! this;
      rw [ Nat.sub_eq_zero_of_le ];
      · bv_omega;
      · exact Nat.monotone_primeCounting this.le;
    · exact this;
  · rcases k <;> simp_all +decide [ Fin.eq_last_of_not_lt ];
    · contradiction;
    · convert extract_primes _ _ _ _ _ using 1;
      · gcongr;
        rw [ inv_eq_one_div, le_div_iff₀ ] <;> nlinarith [ ha_pos _ le_rfl ];
      · exact Nat.succ_le_of_lt hR_last

private lemma rowLo_ge_ak (k : ℕ) (a : ℕ → ℝ) (n : ℕ)
    (ha_pos : ∀ j : ℕ, j < k → 0 < a (j + 1))
    (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    (hak : a k < 1) (hk : 2 ≤ k)
    (j : Fin k) :
    ⌊a k * Real.sqrt ↑n⌋₊ ≤ rowLo k a n j.val := by
  unfold rowLo;
  split_ifs <;> norm_num;
  gcongr;
  have h_inc : a (j + 2) ≤ a k := by
    exact cutoff_mono ha_inc ( by omega ) ( by omega );
  rw [ inv_eq_one_div, le_div_iff₀ ] <;> nlinarith [ ha_pos ( j + 1 ) ( by linarith [ Fin.is_lt j, Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ] ) ]

private lemma row_upper_le_lower (k : ℕ) (a : ℕ → ℝ) (n : ℕ)
    (ha_pos : ∀ j : ℕ, j < k → 0 < a (j + 1))
    (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    (hk : 2 ≤ k)
    (j₁ j₂ : Fin k) (hlt : j₁.val < j₂.val) :
    ⌊(1 / a (↑j₂ + 1)) * Real.sqrt ↑n⌋₊ ≤ rowLo k a n j₁.val := by
  unfold rowLo;
  split_ifs;
  · gcongr;
    · exact ha_pos _ ( by omega );
    · exact cutoff_mono ha_inc ( by linarith ) ( by linarith [ Fin.is_lt j₂ ] );
  · omega

private lemma block_sum_eq
    (Qset PPset : Finset ℕ) (PPblk : ℕ → Finset ℕ) (Xset : Finset ℕ)
    (p v : ℕ)
    (hQ_card : Qset.card = v) (hQ_sub : Qset ⊆ Xset)
    (hPP_card : PPset.card = p * (p + 1) + 1)
    (hPP_sub : ∀ i ∈ PPset, PPblk i ⊆ Xset)
    (hPP_incidence : ∀ x ∈ Xset, (PPset.filter (fun i => x ∈ PPblk i)).card = p + 1) :
    ∑ m : Fin (p * (p + 1) + 1),
      (PPblk ((PPset.orderEmbOfFin hPP_card) m) ∩ Qset).card = v * (p + 1) := by
  have h_sum_eq : ∑ m : Fin (p * (p + 1) + 1), #(PPblk ((PPset.orderEmbOfFin hPP_card) m) ∩ Qset) = ∑ i ∈ PPset, #(PPblk i ∩ Qset) := by
    convert sum_fin_via_orderEmb hPP_card _
    convert rfl
  convert sum_inter_eq_card_mul PPset Xset PPblk Qset p hQ_sub hPP_sub fun x hx => hPP_incidence x hx using 1
  rw [hQ_card]

private lemma primesInRange_card_ge_real (lo hi : ℕ) :
    ((primesInRange lo hi).card : ℝ) ≥
      (Nat.primeCounting hi : ℝ) - (Nat.primeCounting lo : ℝ) := by
  by_cases hlohi : lo ≤ hi
  · rw [primesInRange_card] <;> norm_cast
    rw [Int.subNatNat_of_le (Nat.monotone_primeCounting hlohi)]
  · exact le_trans (sub_nonpos_of_le <| mod_cast Nat.monotone_primeCounting <| le_of_not_ge hlohi) <| Nat.cast_nonneg _

private lemma build_block_product_data
    (k : ℕ) (hk : 2 ≤ k)
    (a : ℕ → ℝ)
    (ha_pos : ∀ j : ℕ, j < k → 0 < a (j + 1))
    (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    (hak : a k < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (ps vs : Fin k → ℕ)
    (hps_prime : ∀ j, Nat.Prime (ps j))
    (hvs_d : ∀ j, vs j ≤ Nat.primeCounting ⌊a (j.val + 1) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊a j.val * Real.sqrt n⌋₊)
    (hvs_rho : ∀ j, vs j ≤ ps j * (ps j + 1) + 1)
    (hR : ∀ j : Fin k, (j : ℕ) < k - 1 →
          ps j * (ps j + 1) + 1 ≤
          Nat.primeCounting ⌊(1 / a (j.val + 1)) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊(1 / a (j.val + 2)) * Real.sqrt n⌋₊)
    (hR_last : ps ⟨k-1, by omega⟩ * (ps ⟨k-1, by omega⟩ + 1) + 1 ≤
          Nat.primeCounting ⌊(1 / a k) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊a k * Real.sqrt n⌋₊) :
    ∃ (D : BlockProductData k),
      D.S = primesInRange ⌊(1 / a 1) * Real.sqrt ↑n⌋₊ n ∧
      (∀ j : Fin k, ∀ q ∈ D.Q j, q ≤ ⌊a (j.val + 1) * Real.sqrt ↑n⌋₊) ∧
      (∀ j : Fin k, ∀ i ∈ D.I j, D.r j i ≤ ⌊(1 / a (j.val + 1)) * Real.sqrt ↑n⌋₊) ∧
      (∀ j : Fin k, ∑ i ∈ D.I j, (D.C j i).card = vs j * (ps j + 1)) := by
  have hQ_exist : ∀ j : Fin k, ∃ Qj : Finset ℕ, Qj.card = vs j ∧
      (∀ p ∈ Qj, Nat.Prime p ∧ ⌊a j.val * Real.sqrt ↑n⌋₊ < p ∧
        p ≤ ⌊a (j.val + 1) * Real.sqrt ↑n⌋₊) := by
    intro j
    exact extract_primes _ _ _ (Nat.floor_le_floor
      (mul_le_mul_of_nonneg_right (le_of_lt (ha_inc j.val j.isLt)) (Real.sqrt_nonneg _))) (hvs_d j)
  choose Qset hQset_card hQset_mem using hQ_exist
  have hX_exist : ∀ j : Fin k, ∃ Xj : Finset ℕ, Qset j ⊆ Xj ∧
      Xj.card = ps j * (ps j + 1) + 1 := by
    intro j; exact exists_finset_superset_card_eq _ _ (by rw [hQset_card]; exact hvs_rho j)
  choose Xset hXset_sub hXset_card using hX_exist
  choose PPset PPblk hPPset_card hPPblk_sub hPPblk_card hPPblk_inter hPPblk_incidence
    using fun j : Fin k =>
      @projective_plane_blocks_nat (ps j) ⟨hps_prime j⟩ (Xset j) (hXset_card j)
  choose Rset hRset_card hRset_mem using fun j : Fin k =>
    extract_row_primes_tight k hk a ha_pos ha_inc hak n ps hR hR_last j
  have hRset_weak : ∀ j : Fin k, ∀ p ∈ Rset j, ⌊a k * Real.sqrt ↑n⌋₊ < p :=
    fun j p hp => lt_of_le_of_lt (rowLo_ge_ak k a n ha_pos ha_inc hak hk j) (hRset_mem j p hp).2.1
  set ρ : Fin k → ℕ := fun j => ps j * (ps j + 1) + 1
  let row : Fin k → ℕ → ℕ := fun j m =>
    if h : m < ρ j then (Rset j).orderEmbOfFin (hRset_card j) ⟨m, h⟩ else 0
  let blk : Fin k → ℕ → Finset ℕ := fun j m =>
    if h : m < ρ j then PPblk j ((PPset j).orderEmbOfFin (hPPset_card j) ⟨m, h⟩) ∩ Qset j
    else ∅
  refine ⟨{
    I := fun j => Finset.range (ρ j)
    Q := Qset
    r := row
    C := blk
    S := primesInRange ⌊(1 / a 1) * Real.sqrt ↑n⌋₊ n
    hS_prime := fun s hs => (primesInRange_mem _ _ hs).1
    hQ_prime := fun j q hq => (hQset_mem j q hq).1
    hr_prime := by
      intro j i hi; simp only [Finset.mem_range] at hi
      have : row j i ∈ Rset j := by
        simp only [row, dif_pos hi]; exact Finset.orderEmbOfFin_mem _ _ _
      exact (hRset_mem j _ this).1
    hr_inj := by
      intro j i₁ hi₁ i₂ hi₂ heq
      simp only [Finset.mem_range] at hi₁ hi₂
      simp only [row, dif_pos hi₁, dif_pos hi₂] at heq
      have hinj := ((Rset j).orderEmbOfFin (hRset_card j)).injective
      have : (⟨i₁, hi₁⟩ : Fin (ρ j)) = ⟨i₂, hi₂⟩ := hinj heq
      exact congr_arg Fin.val this
    hC_sub := by
      intro j i hi; simp only [Finset.mem_range] at hi
      simp only [blk, dif_pos hi]; exact Finset.inter_subset_right
    hC_inter := by
      simp +zetaDelta at *
      intro j i₁ hi₁ i₂ hi₂ hij; split_ifs; simp_all +decide [Finset.inter_comm, Finset.inter_left_comm]
      exact le_trans (Finset.card_le_card (Finset.inter_subset_right)) (hPPblk_inter j _ (Finset.orderEmbOfFin_mem _ _ _) _ (Finset.orderEmbOfFin_mem _ _ _) (by simpa [Fin.ext_iff] using hij))
    hSQ := by
      intro j
      refine' Finset.disjoint_left.mpr fun x hx₁ hx₂ => _
      have hQx := hQset_mem j x hx₂
      have hSx := primesInRange_mem _ _ hx₁
      have h_q_ub := hQx.2.2
      have h_s_lb := hSx.2.1
      have h_floor : ⌊a (j.val + 1) * Real.sqrt n⌋₊ ≤ ⌊1 / a 1 * Real.sqrt n⌋₊ := by
        gcongr
        rw [le_div_iff₀ (ha_pos 0 (by linarith))]
        calc a (j.val + 1) * a 1
            ≤ 1 * 1 := by
              apply mul_le_mul
              · exact le_trans (cutoff_mono ha_inc (by omega : j.val + 1 ≤ k) le_rfl) hak.le
              · exact le_trans (cutoff_mono ha_inc (by omega : 1 ≤ k) le_rfl) hak.le
              · exact le_of_lt (ha_pos 0 (by linarith))
              · positivity
          _ = 1 := one_mul 1
      linarith
    hSR := by
      intro j i hi; simp only [Finset.mem_range] at hi
      have h_mem : row j i ∈ Rset j := by
        simp only [row, dif_pos hi]; exact Finset.orderEmbOfFin_mem _ _ _
      have h_ub := (hRset_mem j _ h_mem).2.2
      intro h_in_S
      have h_S_lb := (primesInRange_mem _ _ h_in_S).2.1
      have h_a_mono : a 1 ≤ a (j.val + 1) :=
        cutoff_mono ha_inc (by omega) (by linarith [j.isLt])
      have ha1_pos : (0 : ℝ) < a 1 := ha_pos 0 (by linarith)
      have haj_pos : (0 : ℝ) < a (j.val + 1) := ha_pos j.val j.isLt
      have h_div_mono : (1 : ℝ) / a (j.val + 1) ≤ 1 / a 1 := by
        rw [div_le_div_iff₀ haj_pos ha1_pos]
        linarith
      have h_floor_mono : ⌊(1 / a (j.val + 1)) * Real.sqrt n⌋₊ ≤ ⌊(1 / a 1) * Real.sqrt n⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_right h_div_mono (Real.sqrt_nonneg _))
      linarith
    hQQ := by
      intros j₁ j₂ hij; rw [Finset.disjoint_left]; intro p hp₁ hp₂; simp_all +decide [Fin.ext_iff]
      wlog hlt : j₁.val < j₂.val generalizing j₁ j₂ p
      · exact this j₂ j₁ (Ne.symm hij) hp₂ hp₁ (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij))
      · have h_floor : ⌊a (j₂.val) * Real.sqrt n⌋₊ ≥ ⌊a (j₁.val + 1) * Real.sqrt n⌋₊ := by
          gcongr
          exact cutoff_mono ha_inc (by linarith) (by linarith [Fin.is_lt j₂])
        linarith [hQset_mem j₁ p hp₁, hQset_mem j₂ p hp₂]
    hQR := by
      intros j₁ j₂ i hi; simp only [Finset.mem_range] at hi
      have h_mem : row j₂ i ∈ Rset j₂ := by
        simp only [row, dif_pos hi]; exact Finset.orderEmbOfFin_mem _ _ _
      have h_row_lb := hRset_weak j₂ _ h_mem
      intro h_in_Q
      have h_q_ub := (hQset_mem j₁ _ h_in_Q).2.2
      have h_floor_le : ⌊a (j₁.val + 1) * Real.sqrt n⌋₊ ≤ ⌊a k * Real.sqrt n⌋₊ := by
        gcongr
        exact cutoff_mono ha_inc (Nat.succ_le_of_lt j₁.isLt) le_rfl
      linarith
    hRR := by
      intro j₁ j₂ hij i₁ hi₁ i₂ hi₂
      simp only [Finset.mem_range] at hi₁ hi₂
      have h₁_mem : row j₁ i₁ ∈ Rset j₁ := by
        simp only [row, dif_pos hi₁]; exact Finset.orderEmbOfFin_mem _ _ _
      have h₂_mem : row j₂ i₂ ∈ Rset j₂ := by
        simp only [row, dif_pos hi₂]; exact Finset.orderEmbOfFin_mem _ _ _
      have h₁_lb := (hRset_mem j₁ _ h₁_mem).2.1
      have h₂_lb := (hRset_mem j₂ _ h₂_mem).2.1
      have h₁_ub := (hRset_mem j₁ _ h₁_mem).2.2
      have h₂_ub := (hRset_mem j₂ _ h₂_mem).2.2
      intro heq
      have hne : j₁.val ≠ j₂.val := Fin.val_ne_of_ne hij
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have h_key := row_upper_le_lower k a n ha_pos ha_inc hk j₁ j₂ hlt
        linarith
      · have h_key := row_upper_le_lower k a n ha_pos ha_inc hk j₂ j₁ hlt
        linarith
  }, rfl, ?_, ?_, ?_⟩
  · intro j q hq; exact (hQset_mem j q hq).2.2
  · intro j i hi; simp only [Finset.mem_range] at hi
    simp only [row, dif_pos hi]
    exact (hRset_mem j _ (Finset.orderEmbOfFin_mem _ (hRset_card j) _)).2.2
  · intro j
    have h_eq : ∑ i ∈ Finset.range (ρ j), (blk j i).card =
        ∑ m : Fin (ρ j), (PPblk j ((PPset j).orderEmbOfFin (hPPset_card j) m) ∩ Qset j).card := by
      rw [← Fin.sum_univ_eq_sum_range]
      congr 1; ext ⟨i, hi⟩
      simp [blk, dif_pos hi]
    rw [h_eq]
    exact block_sum_eq (Qset j) (PPset j) (PPblk j) (Xset j) (ps j) (vs j)
      (hQset_card j) (hXset_sub j) (hPPset_card j) (hPPblk_sub j) (hPPblk_incidence j)

theorem assemble_sidon_set
    (k : ℕ) (hk : 2 ≤ k)
    (a : ℕ → ℝ)
    (ha_pos : ∀ j : ℕ, j < k → 0 < a (j + 1))
    (ha_inc : ∀ j : ℕ, j < k → a j < a (j + 1))
    (hak : a k < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (ps vs : Fin k → ℕ)
    (hps_prime : ∀ j, Nat.Prime (ps j))
    (hvs_d : ∀ j, vs j ≤ Nat.primeCounting ⌊a (j.val + 1) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊a j.val * Real.sqrt n⌋₊)
    (hvs_rho : ∀ j, vs j ≤ ps j * (ps j + 1) + 1)
    (hR : ∀ j : Fin k, (j : ℕ) < k - 1 →
          ps j * (ps j + 1) + 1 ≤
          Nat.primeCounting ⌊(1 / a (j.val + 1)) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊(1 / a (j.val + 2)) * Real.sqrt n⌋₊)
    (hR_last : ps ⟨k-1, by omega⟩ * (ps ⟨k-1, by omega⟩ + 1) + 1 ≤
          Nat.primeCounting ⌊(1 / a k) * Real.sqrt n⌋₊ -
          Nat.primeCounting ⌊a k * Real.sqrt n⌋₊) :
    ∃ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ n) ∧
      IsMultiplicativeSidon A ∧
      (A.card : ℝ) ≥ (Nat.primeCounting n : ℝ) -
        (Nat.primeCounting ⌊(1 / a 1) * Real.sqrt n⌋₊ : ℝ) +
        ∑ j : Fin k, ((vs j : ℝ) * ((ps j : ℝ) + 1)) := by
  obtain ⟨D, hDS, hDQ, hDR, hDsum⟩ :=
    build_block_product_data k hk a ha_pos ha_inc hak n hn ps vs
      hps_prime hvs_d hvs_rho hR hR_last
  refine ⟨D.fullSet, ?_, layered_block_product_sidon D, ?_⟩
  · unfold BlockProductData.fullSet at *
    simp_all +decide [Finset.ext_iff]
    rintro x (hx | hx)
    · exact ⟨Nat.Prime.pos (primesInRange_mem _ _ hx |>.1), primesInRange_mem _ _ hx |>.2.2⟩
    · obtain ⟨j, i, hi, q, hq, rfl⟩ := D.productSet_mem hx
      refine' ⟨Nat.mul_pos (Nat.Prime.pos (D.hr_prime j i hi)) (Nat.Prime.pos (D.hQ_prime j q (D.hC_sub j i hi hq))), _⟩
      refine' le_trans (Nat.mul_le_mul (hDR j i hi) (hDQ j q (D.hC_sub j i hi hq))) _
      convert floor_product_le (show 0 < (a (j + 1))⁻¹ from inv_pos.mpr (ha_pos j (Fin.is_lt j))) n using 1; ring_nf
      norm_num [mul_comm]
  · rw [layered_block_product_card, hDS]
    norm_num [hDsum]
    norm_cast
    convert primesInRange_card_ge_real ⌊(a 1)⁻¹ * Real.sqrt n⌋₊ n using 1
    rw [ge_iff_le, sub_le_iff_le_add]; norm_cast

-- ============================================================
-- § 15. Main theorem
-- ============================================================

/-- The prime number theorem in the form used in this development.
This is an external input that we assume without proof. -/
axiom pi_alt : ∃ c : ℝ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
  ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / Real.log x

lemma pi_sqrt_overhead_absorbed (C : ℝ) (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      (Nat.primeCounting ⌊C * Real.sqrt n⌋₊ : ℝ) ≤
        δ * (n : ℝ) ^ ((3:ℝ)/4) / (Real.log n) ^ ((3:ℝ)/2) := by
  suffices h_equiv : ∀ᶠ n : ℕ in Filter.atTop, C / δ ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) by
    filter_upwards [ h_equiv, Filter.eventually_gt_atTop 1 ] with n hn hn';
    have h_floor : (Nat.primeCounting ⌊C * Real.sqrt n⌋₊ : ℝ) ≤ C * Real.sqrt n := by
      refine' le_trans _ ( Nat.floor_le <| by positivity );
      norm_num [ Nat.primeCounting ];
      rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
      exact le_trans ( Finset.card_le_card ( show Finset.filter Nat.Prime ( Finset.range ( ⌊C * Real.sqrt n⌋₊ + 1 ) ) ⊆ Finset.Ico 2 ( ⌊C * Real.sqrt n⌋₊ + 1 ) from fun x hx => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le ( Finset.mem_filter.mp hx |>.2 ), Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ⟩ ) ) ( by simp +arith +decide );
    convert h_floor.trans _ using 1;
    convert mul_le_mul_of_nonneg_left hn ( show 0 ≤ δ * Real.sqrt n by positivity ) using 1 <;> ring_nf;
    · norm_num [ hδ.ne' ];
    · rw [ show ( 3 / 4 : ℝ ) = 1 / 2 + 1 / 4 by norm_num, Real.sqrt_eq_rpow, Real.rpow_add ] <;> norm_num ; ring ; linarith;
  have h_equiv : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) / (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)) Filter.atTop Filter.atTop := by
    suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp (y / 4) / y ^ (3 / 2 : ℝ)) Filter.atTop Filter.atTop by
      have h_subst : Filter.Tendsto (fun n : ℕ => Real.exp (Real.log (n : ℝ) / 4) / (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)) Filter.atTop Filter.atTop := by
        exact h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      refine h_subst.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
    suffices h_z : Filter.Tendsto (fun z : ℝ => Real.exp z / (4 * z) ^ (3 / 2 : ℝ)) Filter.atTop Filter.atTop by
      convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 4 : ℝ ) ⁻¹ ) ) using 2 ; norm_num ; ring_nf;
    suffices h_factor : Filter.Tendsto (fun z : ℝ => Real.exp z / z ^ (3 / 2 : ℝ)) Filter.atTop Filter.atTop by
      have h_factor : Filter.Tendsto (fun z : ℝ => (Real.exp z / z ^ (3 / 2 : ℝ)) * (1 / 4 ^ (3 / 2 : ℝ))) Filter.atTop Filter.atTop := by
        exact h_factor.atTop_mul_const ( by positivity );
      refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring );
    exact tendsto_exp_div_rpow_atTop (3 / 2);
  exact h_equiv.eventually_ge_atTop _

/-- Main theorem: For every c < 2^(11/4) / 3^(3/4), there exists N such that
for all n ≥ N, there exists a multiplicative Sidon set A ⊆ {1,...,n} with
|A| ≥ π(n) + c · n^(3/4) / (log n)^(3/2). -/
theorem multiplicative_sidon_set_lower_bound
    (c : ℝ)
    (hc_bound : c < Lambda) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ A : Finset ℕ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧
        IsMultiplicativeSidon A ∧
        (A.card : ℝ) ≥ (Nat.primeCounting n : ℝ) +
          c * (n : ℝ) ^ ((3:ℝ)/4) / (Real.log n) ^ ((3:ℝ)/2) := by
  obtain ⟨k, a, hk, ha0, ha_inc, hak, ha_pos, hdb, hsum⟩ :=
    cutoff_constants_exist c hc_bound
  set L := 2 * ∑ j ∈ Finset.range k,
    (a (j + 1) - a j) * Real.sqrt (2 * (
      if j < k - 1
      then 1 / a (j + 1) - 1 / a (j + 2)
      else 1 / a k - a k)) with hL_def
  have hLc : c < L := hsum
  set η := (L - c) / 2 with hη_def
  have hη_pos : 0 < η := by linarith
  have hLηc : c < L - η := by linarith
  obtain ⟨N₀, hN₀⟩ := layered_prime_supply k (by linarith) a ha0 ha_pos ha_inc hak hdb L rfl η hη_pos pi_alt
  have ha1_pos : 0 < a 1 := ha_pos 0 (by omega)
  have h_slack := pi_sqrt_overhead_absorbed (1 / a 1) (by positivity) ((L - η) - c) (by linarith)
  rw [Filter.eventually_atTop] at h_slack
  obtain ⟨N₁, hN₁⟩ := h_slack
  refine ⟨max N₀ (max N₁ 2), fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := by omega
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : 2 ≤ n := by omega
  obtain ⟨ps, vs, hps_prime, hvs_d, hvs_rho, hR, hR_last, hsum_bound⟩ := hN₀ n hn₀
  obtain ⟨A, hA_range, hA_sidon, hA_card⟩ :=
    assemble_sidon_set k hk a  ha_pos ha_inc hak n hn₂ ps vs hps_prime
      hvs_d hvs_rho hR hR_last
  refine ⟨A, hA_range, hA_sidon, ?_⟩
  have h_overhead := hN₁ n hn₁
  calc (A.card : ℝ)
      ≥ (Nat.primeCounting n : ℝ) -
        (Nat.primeCounting ⌊(1 / a 1) * Real.sqrt n⌋₊ : ℝ) +
        ∑ j : Fin k, ((vs j : ℝ) * ((ps j : ℝ) + 1)) := hA_card
    _ ≥ (Nat.primeCounting n : ℝ) -
        ((L - η) - c) * (n : ℝ) ^ ((3:ℝ)/4) / (Real.log n) ^ ((3:ℝ)/2) +
        (L - η) * (n : ℝ) ^ ((3:ℝ)/4) / (Real.log n) ^ ((3:ℝ)/2) := by linarith [hsum_bound, h_overhead]
    _ = (Nat.primeCounting n : ℝ) +
        c * (n : ℝ) ^ ((3:ℝ)/4) / (Real.log n) ^ ((3:ℝ)/2) := by ring

#print axioms multiplicative_sidon_set_lower_bound
