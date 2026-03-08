/-
Yixin He, Yanyang Li and Quanyu Tang used ChatGPT 5.4 Pro in order to prove that for every positive integer $m$ there exists a positive integer $N$, a set $A \subset \{1, 2, \ldots, N\}$ of size $m$ and an interval $I = (x, x + 2N) \subset (1, \infty)$ such that the maximum number of fully disjoint pairs $(a, b)$ with $a \in A$, $b \in I$ and $a | b$ is at most $\lceil 2 \sqrt{m} \rceil$. Moreover, this bound is tight. That is, for every set $A \subset \{1, 2, \ldots, N\}$ of size $m ≥ 4$ and every interval $I = (x, x + 2N) \subset (1, \infty)$ one can find at least $\lceil 2 \sqrt{m} \rceil$ fully disjoint pairs $(a, b)$ with $a \in A$, $b \in I$ and $a | b$.

These bounds solve Erdős Problem #650 (https://www.erdosproblems.com/650), and the write-up can be found here:

https://github.com/QuanyuTang/erdos-problem-650/blob/main/On_Erdos_Problem_650.pdf

Below you can find a formalization of the result in Lean, which was obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
A set of pairs $M$ is a matching if each pair $(a, b) \in M$ satisfies $a \in A$, $b \in I$, $a \mid b$, and no two pairs share an element.
-/
def is_matching (A : Finset ℕ) (I : Set ℝ) (M : Finset (ℕ × ℤ)) : Prop :=
  (∀ p ∈ M, p.1 ∈ A ∧ (p.2 : ℝ) ∈ I ∧ (p.1 : ℤ) ∣ p.2) ∧
  (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2)

/-
The maximum matching size is the largest integer $k$ such that there exists a matching of size $k$.
-/
noncomputable def max_matching_size (A : Finset ℕ) (I : Set ℝ) : ℕ :=
  sSup {k | ∃ M, is_matching A I M ∧ M.card = k}

/-
Property(m, k) holds if for every configuration of size m, there exists a matching of size at least k.
-/
def Property (m k : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (x : ℝ),
    A.card = m →
    (∀ a ∈ A, a > 0) →
    ∀ (hA : A.Nonempty),
    let N := A.max' hA
    let I := Set.Ioo x (x + 2 * N)
    max_matching_size A I ≥ k

/-
f(m) is the largest integer k such that every configuration of size m has a matching of size at least k.
-/
noncomputable def f (m : ℕ) : ℕ :=
  sSup {k | Property m k}

/-
$\gcd(\lcm(a, b), c) = \lcm(\gcd(a, c), \gcd(b, c))$ for natural numbers.
-/
lemma Nat.gcd_lcm_distrib (a b c : ℕ) : Nat.gcd (Nat.lcm a b) c = Nat.lcm (Nat.gcd a c) (Nat.gcd b c) := by
  -- By the properties of prime factorizations, we can show that the exponents of each prime in the gcd of the lcm of a and b and c are equal to the exponents in the lcm of the gcds of a and c, and b and c.
  have h_prime_factors : ∀ p : ℕ, Nat.factorization (Nat.gcd (Nat.lcm a b) c) p = Nat.factorization (Nat.lcm (Nat.gcd a c) (Nat.gcd b c)) p := by
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;> simp_all +decide [ Nat.factorization_gcd, Nat.factorization_lcm ];
    grind;
  by_contra h_contra;
  refine' h_contra ( Nat.factorization_inj _ _ _ ) <;> simp_all +decide;
  · aesop;
  · aesop;
  · ext p; exact h_prime_factors p;

/-
Distributive property of GCD over LCM for a list of natural numbers.
-/
lemma Nat.gcd_list_lcm_distrib (a : ℕ) (l : List ℕ) :
    Nat.gcd a (l.foldr Nat.lcm 1) = (l.map (Nat.gcd a)).foldr Nat.lcm 1 := by
  induction' l with b l ih generalizing a <;> simp_all +decide [ Nat.gcd_comm a ];
  rw [ ← ih, Nat.lcm_comm, Nat.gcd_comm ];
  simp +decide only [lcm_comm, Nat.gcd_comm a];
  exact gcd_lcm_distrib b (List.foldr lcm 1 l) a

/-
Distributive property of GCD over LCM for a list of integers.
-/
lemma Int.gcd_list_lcm_distrib (a : ℤ) (l : List ℤ) :
    Int.gcd a (l.foldr (fun x acc => Int.lcm x acc) 1) =
    (l.map (fun x => Int.gcd a x)).foldr Nat.lcm 1 := by
  convert Nat.gcd_list_lcm_distrib _ _ using 1;
  convert Int.gcd_eq_natAbs .. using 1;
  congr! 1;
  any_goals exact l.map Int.natAbs;
  · induction l <;> aesop;
  · simp +decide;
    congr! 2

/-
Generalized Chinese Remainder Theorem for a list of congruences.
-/
lemma generalized_chinese_remainder_list (l : List (ℤ × ℤ))
    (h : ∀ i j, i ∈ l → j ∈ l → i.2 ≡ j.2 [ZMOD (Int.gcd i.1 j.1)]) :
    ∃ x : ℤ, ∀ i ∈ l, x ≡ i.2 [ZMOD i.1] := by
  induction' l with i l ih ; aesop;
  by_contra! h_contra; simp_all +decide [ Int.ModEq ] ; (
  -- Let $L = \text{lcm}(l.map (fun i => i.1))$.
  set L := l.foldr (fun x acc => Int.lcm x.1 acc) 1 with hL_def
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℤ, ∀ i ∈ l, x₁ ≡ i.2 [ZMOD i.1] := by
    exact Exists.elim ( ih fun a b c d ha hb => h a b c d ( Or.inr ha ) ( Or.inr hb ) ) fun x hx => ⟨ x, fun a ha => hx _ _ ha ⟩ ;
  generalize_proofs at *;
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ℤ, x₂ ≡ i.2 [ZMOD i.1] ∧ x₂ ≡ x₁ [ZMOD L] := by
    -- By the Chinese Remainder Theorem, there exists an integer $x₂$ such that $x₂ ≡ i.2 [ZMOD i.1]$ and $x₂ ≡ x₁ [ZMOD L]$.
    have h_crt : Int.gcd i.1 L ∣ Int.natAbs (i.2 - x₁) := by
      have h_crt : ∀ j ∈ l, Int.gcd i.1 j.1 ∣ Int.natAbs (i.2 - x₁) := by
        intros j hj
        specialize h i.1 i.2 j.1 j.2 (Or.inl rfl) (Or.inr hj)
        generalize_proofs at *; (
        specialize hx₁ j hj; simp_all +decide [ Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero ] ;
        exact Int.natCast_dvd.mp ( by simpa using dvd_sub h ( Int.dvd_trans ( Int.gcd_dvd_right _ _ ) hx₁ ) ) ;)
      generalize_proofs at *; (
      -- Apply the lemma `Int.gcd_list_lcm_distrib` to rewrite the goal in terms of the gcd of `i.1` and each element in `l`.
      have h_gcd_lcm : Int.gcd i.1 L = (l.map (fun j => Int.gcd i.1 j.1)).foldr Nat.lcm 1 := by
        have h_gcd_lcm : ∀ (l : List ℤ), Int.gcd i.1 (l.foldr (fun x acc => Int.lcm x acc) 1) = (l.map (fun x => Int.gcd i.1 x)).foldr Nat.lcm 1 := by
          exact fun l => Int.gcd_list_lcm_distrib i.1 l;
        generalize_proofs at *; (
        convert h_gcd_lcm ( l.map Prod.fst ) using 1 <;> norm_num [ Function.comp ] ; ring_nf!;
        · exact congr_arg _ ( by clear h_crt h_gcd_lcm h_contra hx₁ ih h; induction l <;> aesop ) ;
        · rfl)
      generalize_proofs at *; (
      rw [h_gcd_lcm] at *; simp_all +decide ; (
      -- By definition of lcm, if each element in a list divides a number, then their lcm also divides that number.
      have h_lcm_div : ∀ {l : List ℕ} {n : ℕ}, (∀ x ∈ l, x ∣ n) → List.foldr Nat.lcm 1 l ∣ n := by
        intros l n hn; induction' l with x l ih <;> simp_all +decide [ Nat.lcm_dvd_iff ] ;
      generalize_proofs at *; (
      exact h_lcm_div fun x hx => by obtain ⟨ j, hj, rfl ⟩ := List.mem_map.mp hx; exact h_crt _ _ hj; ;))))
    generalize_proofs at *; (
    obtain ⟨ k, hk ⟩ := Int.natCast_dvd.mpr h_crt; simp_all +decide [ Int.modEq_iff_dvd ] ; (
    -- By Bezout's identity, there exist integers $u$ and $v$ such that $i.1 * u + L * v = \gcd(i.1, L)$.
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, i.1 * u + L * v = Int.gcd i.1 L := by
      exact Int.gcd_eq_gcd_ab i.1 L ▸ ⟨ _, _, rfl ⟩
    generalize_proofs at *; (
    -- Let $x₂ = x₁ + L * v * k$.
    use x₁ + L * v * k
    generalize_proofs at *; (
    exact ⟨ ⟨ u * k, by linear_combination hk - huv * k ⟩, ⟨ -v * k, by ring ⟩ ⟩ ;))) ;);
  generalize_proofs at *;
  have hx₂_congr : ∀ i ∈ l, x₂ ≡ i.2 [ZMOD i.1] := by
    intro j hj
    have h_div : j.1 ∣ L := by
      have h_div : ∀ (l : List (ℤ × ℤ)), ∀ j ∈ l, j.1 ∣ List.foldr (fun x acc => Int.lcm x.1 acc) 1 l := by
        intro l j hj
        induction' l with j l ih generalizing j
        aesop
        generalize_proofs at *; (
        simp +zetaDelta at *; (
        exact hj.elim ( fun hj => hj.symm ▸ Int.dvd_lcm_left _ _ ) fun hj => Int.dvd_trans ( ih _ _ hj ) ( Int.dvd_lcm_right _ _ ) ;))
      generalize_proofs at *;
      convert h_div l j hj using 1
      generalize_proofs at *; (
      clear hx₁ hx₂ h_div h_contra ih hL_def hj h; induction l <;> aesop;)
    generalize_proofs at *;
    have h_congr : x₂ ≡ x₁ [ZMOD j.1] := by
      exact hx₂.2.of_dvd h_div
    generalize_proofs at *;
    have h_final : x₂ ≡ j.2 [ZMOD j.1] := by
      exact Eq.trans h_congr ( hx₁ _ hj )
    generalize_proofs at *;
    exact h_final
  generalize_proofs at *;
  have hx₂_congr' : x₂ ≡ i.2 [ZMOD i.1] := by
    exact hx₂.1
  generalize_proofs at *;
  have hx₂_congr'' : x₂ % i.1 = i.2 % i.1 := by
    exact hx₂_congr' ▸ rfl
  generalize_proofs at *;
  have hx₂_congr''' : ∃ a b : ℤ, (a, b) ∈ l ∧ ¬x₂ % a = b % a := by
    exact h_contra x₂ |> Or.resolve_left <| by tauto;
  generalize_proofs at *;
  obtain ⟨a, b, h_mem, h_not_congr⟩ := hx₂_congr'''; exact h_not_congr (hx₂_congr (a, b) h_mem) ;);

/-
For $D = ((st)!)^s$, the $p$-adic valuation of $D$ is strictly greater than the $p$-adic valuation of any $k \in (0, s)$, for all primes $p \le st$.
-/
lemma valuation_D_gt_valuation_delta (s t : ℕ) (hs : s ≥ 2) :
    let D := (Nat.factorial (s * t)) ^ s
    ∀ p, p.Prime → p ≤ s * t → ∀ k, 0 < k → k < s →
    Nat.factorization D p > Nat.factorization k p := by
  -- By definition of $D$, we know that its $p$-adic valuation is $s$ times the $p$-adic valuation of $(st)!$.
  intro D p hp hpt k hk_pos hk_lt_s
  have h_vp_D : Nat.factorization D p = s * Nat.factorization (Nat.factorial (s * t)) p := by
    aesop;
  -- Since $p \le st$, $p$ divides $(st)!$, so $v_p((st)!) \ge 1$.
  have h_vp_fact : Nat.factorization (Nat.factorial (s * t)) p ≥ 1 := by
    exact Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by exact Nat.mem_primeFactors.mpr ⟨ hp, Nat.dvd_factorial hp.pos hpt, by positivity ⟩ ) );
  -- Since $p^{v_p(k)} \le k < s$, we have $v_p(k) \le \log_p(s-1)$.
  have h_vp_k_le_log : Nat.factorization k p ≤ Nat.log p (s - 1) := by
    exact Nat.le_log_of_pow_le hp.one_lt ( Nat.le_sub_one_of_lt ( Nat.lt_of_le_of_lt ( Nat.le_of_dvd hk_pos ( Nat.ordProj_dvd _ _ ) ) hk_lt_s ) );
  nlinarith [ Nat.log_lt_of_lt_pow ( Nat.sub_ne_zero_of_lt hs ) ( show s - 1 < p ^ s by exact lt_of_lt_of_le ( Nat.sub_lt ( by linarith ) zero_lt_one ) ( Nat.le_of_lt ( Nat.recOn s ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; nlinarith [ Nat.Prime.one_lt hp ] ) ) ) ]

/-
The set of primes $p > st$ dividing $qD + \delta$ for small $q, \delta$ is finite.
-/
def D_val (s t : ℕ) : ℕ := (Nat.factorial (s * t)) ^ s

lemma P_finite (s t : ℕ) (hs : s ≥ 2) (ht : t ≥ 2) :
    let D := D_val s t
    let P := {p : ℕ | p.Prime ∧ p > s * t ∧
      ∃ q ∈ Finset.Ico 1 t, ∃ δ ∈ Finset.Icc (-(s - 1) : ℤ) (s - 1), δ ≠ 0 ∧ (p : ℤ) ∣ q * D + δ}
    P.Finite := by
  -- The set of pairs $(q, \delta)$ is finite.
  have h_pairs_finite : {p : ℕ | Nat.Prime p ∧ ∃ q ∈ Finset.Ico 1 t, ∃ δ ∈ Finset.Icc (-(s - 1) : ℤ) (s - 1), δ ≠ 0 ∧ (p : ℤ) ∣ q * (D_val s t) + δ}.Finite := by
    -- For each pair $(q, \delta)$, the number $qD + \delta$ is non-zero (since $D$ is very large and $\delta$ is small).
    have h_nonzero : ∀ q ∈ Finset.Ico 1 t, ∀ δ ∈ Finset.Icc (-(s - 1) : ℤ) (s - 1), δ ≠ 0 → (q * (D_val s t) + δ : ℤ) ≠ 0 := by
      intro q hq δ hδ hδ_nonzero
      have h_bound : (q * (D_val s t) : ℤ) > (s - 1) := by
        norm_num [ D_val ] at *;
        nlinarith [ show ( ( s * t ).factorial : ℤ ) ^ s > s by exact_mod_cast lt_of_lt_of_le ( by nlinarith [ Nat.self_le_factorial ( s * t ) ] ) ( Nat.le_self_pow ( by linarith ) _ ), show ( q : ℤ ) ≥ 1 by norm_cast; linarith ] ;
      have h_nonzero : (q * (D_val s t) + δ : ℤ) ≠ 0 := by
        cases lt_or_gt_of_ne hδ_nonzero <;> linarith [ Finset.mem_Icc.mp hδ ] ;
      exact h_nonzero;
    refine Set.Finite.subset ( Set.toFinite ( Finset.biUnion ( Finset.Ico 1 t ) fun q => Finset.biUnion ( Finset.Icc ( - ( s - 1 ) : ℤ ) ( s - 1 ) ) fun δ => Nat.primeFactors ( Int.natAbs ( q * ( D_val s t ) + δ ) ) ) ) ?_;
    simp +contextual [ Set.subset_def ];
    exact fun p hp q hq₁ hq₂ r hr₁ hr₂ hr₃ hr₄ => ⟨ q, r, by simpa [ ← Int.natCast_dvd_natCast ] using hr₄, hr₂, ⟨ hq₁, hq₂ ⟩, hr₁, h_nonzero q ( Finset.mem_Ico.mpr ⟨ hq₁, hq₂ ⟩ ) r ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) hr₃ ⟩;
  exact h_pairs_finite.subset fun p hp => ⟨ hp.1, by aesop ⟩

/-
For any prime $p > st$, there exists a residue $r$ modulo $p$ such that $r \not\equiv i - jD \pmod p$ for all $1 \le i \le s$ and $0 \le j < t$.
-/
lemma exists_good_residue (s t : ℕ) (D : ℤ) (p : ℕ) (hp : p.Prime) (hp_gt : p > s * t) :
    ∃ r : ℤ, ∀ i j : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t → ¬(r ≡ i - j * D [ZMOD p]) := by
  -- Let $T = \{i - jD \pmod p \mid 1 \le i \le s, 0 \le j < t\}$.
  set T := Finset.image (fun p' : ℤ × ℤ => (p'.1 - p'.2 * D) : ℤ × ℤ → ZMod p) (Finset.Icc (1 : ℤ) (s : ℤ) ×ˢ Finset.Ico (0 : ℤ) (t : ℤ)) with hT_def
  have hT_card_lt_p : T.card < p := by
    exact lt_of_le_of_lt ( Finset.card_image_le ) ( by simpa [ mul_comm ] using by nlinarith ) ;
  generalize_proofs at *; (
  haveI := Fact.mk hp; obtain ⟨ x, hx ⟩ := Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ T, fun h ↦ hT_card_lt_p.ne <| by rw [ h ] ; simp +decide [ Finset.card_univ ] ⟩ ) ; use x.val; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
  exact fun i j hi hj hi' hj' => Ne.symm ( hx i j hi hj hi' hj' ))

/-
The set of "bad primes" is finite.
-/
def BadPrimes (s t : ℕ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ p > s * t ∧
    ∃ q ∈ Finset.Ico 1 t, ∃ δ ∈ Finset.Icc (-(s - 1) : ℤ) (s - 1), δ ≠ 0 ∧ (p : ℤ) ∣ q * (D_val s t) + δ}

lemma BadPrimes_finite (s t : ℕ) (hs : s ≥ 2) (ht : t ≥ 2) : (BadPrimes s t).Finite := by
  convert P_finite s t hs ht using 1

/-
There exists a large integer $a$ that avoids all "bad" residue classes modulo primes in `BadPrimes`.
-/
def IsGoodA (s t : ℕ) (a : ℤ) : Prop :=
  let D := D_val s t
  ∀ p ∈ BadPrimes s t, ∀ i j : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t → ¬(a ≡ i - j * D [ZMOD p])

lemma exists_good_a (s t : ℕ) (hs : s ≥ 2) (ht : t ≥ 2) :
    ∃ a : ℤ, a > 2 * (t - 1) * (D_val s t) + 4 * s ∧ IsGoodA s t a := by
  -- By `BadPrimes_finite`, there exists a finite set of primes `BadPrimes` such that for all primes `p` not in `BadPrimes`, `a` will satisfy the conditions of `IsGoodA`.
  have h_bad_finite : (BadPrimes s t).Finite := by
    exact BadPrimes_finite s t hs ht;
  obtain ⟨a, ha⟩ : ∃ a : ℤ, ∀ p ∈ BadPrimes s t, ∀ i j : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t → ¬(a ≡ i - j * ((D_val s t) : ℤ) [ZMOD p]) := by
    -- For each prime $p$ in `BadPrimes`, there exists a residue $r_p$ such that $r_p \not\equiv i - jD \pmod p$ for all relevant $i, j$.
    have h_residues : ∀ p ∈ BadPrimes s t, ∃ r_p : ℤ, ∀ i j : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t → ¬(r_p ≡ i - j * ((D_val s t) : ℤ) [ZMOD p]) := by
      exact fun p hp => exists_good_residue s t ( D_val s t ) p hp.1 hp.2.1;
    choose! r hr using h_residues;
    -- Applying the Chinese Remainder Theorem.
    have h_crt : ∀ p ∈ BadPrimes s t, ∃ x : ℤ, x ≡ r p [ZMOD p] ∧ ∀ q ∈ BadPrimes s t, q ≠ p → x ≡ 0 [ZMOD q] := by
      -- For each prime $p \in BadPrimes$, let $y_p$ be the multiplicative inverse of $\prod_{q \in BadPrimes, q \neq p} q$ modulo $p$.
      intros p hp
      obtain ⟨y_p, hy_p⟩ : ∃ y_p : ℤ, y_p * (∏ q ∈ (h_bad_finite.toFinset.erase p), (q : ℤ)) ≡ 1 [ZMOD p] := by
        have h_coprime : Nat.gcd p (∏ q ∈ (h_bad_finite.toFinset.erase p), q) = 1 := by
          refine' Nat.Coprime.prod_right fun q hq => _;
          have := Nat.coprime_primes hp.1 ( show Nat.Prime q from by { exact ( by { have := h_bad_finite.mem_toFinset.mp ( Finset.mem_of_mem_erase hq ) ; exact this.1 } ) } ) ; aesop;
        have := Nat.gcd_eq_gcd_ab p ( ∏ q ∈ h_bad_finite.toFinset.erase p, q );
        exact ⟨ Nat.gcdB p ( ∏ q ∈ h_bad_finite.toFinset.erase p, q ), Int.modEq_iff_dvd.mpr ⟨ Nat.gcdA p ( ∏ q ∈ h_bad_finite.toFinset.erase p, q ), by push_cast at *; linarith ⟩ ⟩;
      use y_p * (∏ q ∈ (h_bad_finite.toFinset.erase p), (q : ℤ)) * r p;
      exact ⟨ by simpa using hy_p.mul_right _, fun q hq hqp => Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩;
    choose! x hx₁ hx₂ using h_crt;
    use ∑ p ∈ h_bad_finite.toFinset, x p; intro p hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
    rw [ Finset.sum_eq_single p ] <;> aesop;
  -- By the Chinese Remainder Theorem, we can choose $a$ such that $a \equiv r_p \pmod p$ for all $p \in \mathcal{P}$.
  obtain ⟨a', ha'⟩ : ∃ a' : ℤ, a' ≡ a [ZMOD (∏ p ∈ h_bad_finite.toFinset, p)] ∧ a' > 2 * ((t : ℤ) - 1) * ((D_val s t) : ℤ) + 4 * s := by
    exact ⟨ a + ( ∏ p ∈ h_bad_finite.toFinset, ( p : ℤ ) ) * ( Int.toNat ( 2 * ( t - 1 ) * D_val s t + 4 * s - a ) + 1 ), by norm_num [ Int.ModEq ], by nlinarith [ Int.self_le_toNat ( 2 * ( t - 1 ) * D_val s t + 4 * s - a ), show 0 < ( ∏ p ∈ h_bad_finite.toFinset, ( p : ℤ ) ) from Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.Prime.pos <| h_bad_finite.mem_toFinset.mp hp |>.1 ] ⟩;
  refine' ⟨ a', ha'.2, fun p hp i j hij => _ ⟩;
  exact fun h => ha p hp i j hij <| Eq.trans ( ha'.1.symm.of_dvd <| mod_cast Finset.dvd_prod_of_mem _ <| h_bad_finite.mem_toFinset.mpr hp ) h

/-
If $a$ is "good", then the sequence $a_{i,j}$ satisfies the GCD property.
-/
lemma gcd_property_of_good_a (s t : ℕ) (hs : s ≥ 2) (ht : t ≥ 2) (a : ℤ) (ha : IsGoodA s t a) :
    let D := D_val s t
    let a_ij (i j : ℤ) := a + j * D - i
    ∀ i j k l : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t →
                   1 ≤ k ∧ k ≤ s ∧ 0 ≤ l ∧ l < t →
                   (Int.gcd (a_ij i j) (a_ij k l) : ℤ) ∣ (k - i) := by
  -- Let $d = \gcd(a_{i,j}, a_{k,l})$. Then $d \mid (a_{i,j} - a_{k,l}) = (j-l)D + (k-i)$.
  intros D a_ij i j k l hi hj
  set d := Int.gcd (a_ij i j) (a_ij k l) with hd
  have hd_div_diff : (d : ℤ) ∣ (j - l) * D + (k - i) := by
    convert dvd_sub ( Int.gcd_dvd_left _ _ ) ( Int.gcd_dvd_right _ _ ) using 1 ; ring;
  -- Let $q = |j-l|$ and $\delta = \pm(k-i)$.
  by_cases hq : j = l; simp_all +decide ;
  -- If $q > 0$, then $1 \le q < t$. Also $|\delta| < s$. Assume $\delta \ne 0$.
  by_cases hδ : k - i = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
  -- Let $q = |j-l|$ and $\delta = \pm(k-i)$. We show no prime $p > st$ divides $d$.
  have h_no_prime_gt_st : ∀ p : ℕ, p.Prime → p > s * t → ¬(p : ℤ) ∣ d := by
    intros p hp hp_gt hp_div_d
    have hp_div_qD_delta : (p : ℤ) ∣ (j - l) * D + (k - i) := by
      exact dvd_trans hp_div_d hd_div_diff;
    have hp_bad : p ∈ BadPrimes s t := by
      refine' ⟨ hp, hp_gt, _ ⟩;
      by_cases hq_pos : j - l > 0;
      · exact ⟨ Int.natAbs ( j - l ), Finset.mem_Ico.mpr ⟨ Int.natAbs_pos.mpr ( sub_ne_zero.mpr hq ), by linarith [ abs_of_pos hq_pos ] ⟩, k - i, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, sub_ne_zero.mpr hδ, by simpa [ abs_of_pos hq_pos ] using hp_div_qD_delta ⟩;
      · refine' ⟨ Int.natAbs ( j - l ), _, - ( k - i ), _, _, _ ⟩ <;> norm_num at * <;> try omega;
        rw [ abs_of_nonpos ( sub_nonpos.mpr hq_pos ) ] ; convert hp_div_qD_delta.neg_right using 1 ; ring;
    have := ha p hp_bad i j ⟨ hi.1, hi.2.1, hi.2.2.1, hi.2.2.2 ⟩;
    exact this <| Int.ModEq.symm <| Int.modEq_of_dvd <| by convert dvd_trans hp_div_d <| Int.gcd_dvd_left _ _ using 1; ring;
  -- For $p \le st$, by `valuation_D_gt_valuation_delta`, $v_p(D) > v_p(\delta)$ (since $0 < |\delta| < s$).
  have h_valuation : ∀ p : ℕ, p.Prime → p ≤ s * t → Nat.factorization d p ≤ Nat.factorization (Int.natAbs (k - i)) p := by
    intros p hp hp_le_st
    have h_valuation_p : Nat.factorization D p > Nat.factorization (Int.natAbs (k - i)) p := by
      apply valuation_D_gt_valuation_delta s t hs p hp hp_le_st (Int.natAbs (k - i)) (by
      exact Int.natAbs_pos.mpr ( sub_ne_zero.mpr hδ )) (by
      grind);
    -- Since $d \mid (j-l)D + (k-i)$, we have $v_p(d) \leq v_p((j-l)D + (k-i))$.
    have h_valuation_div : Nat.factorization d p ≤ Nat.factorization (Int.natAbs ((j - l) * D + (k - i))) p := by
      have h_valuation_div : d ∣ Int.natAbs ((j - l) * D + (k - i)) := by
        exact Int.natCast_dvd.mp hd_div_diff;
      rw [ ← Nat.factorization_le_iff_dvd ] at h_valuation_div <;> norm_num at * ; aesop;
      · intro H; simp_all +decide ;
        norm_num [ ← hd ] at *;
        exact absurd ( h_no_prime_gt_st ( Nat.find ( Nat.exists_infinite_primes ( s * t + 1 ) ) ) ( Nat.find_spec ( Nat.exists_infinite_primes ( s * t + 1 ) ) |>.2 ) ) ( by linarith [ Nat.find_spec ( Nat.exists_infinite_primes ( s * t + 1 ) ) |>.1 ] );
      · intro H; simp_all +decide ;
        -- Since $|j - l| \geq 1$ and $D$ is very large, $|k - i|$ must be at least $D$, which contradicts $|k - i| < s$.
        have h_contradiction : Int.natAbs (k - i) ≥ D := by
          cases abs_cases ( k - i ) <;> cases lt_or_gt_of_ne hq <;> nlinarith [ show ( D : ℤ ) > 0 from Nat.cast_pos.mpr ( pow_pos ( Nat.factorial_pos _ ) _ ) ] ;
        -- Since $D = ((st)!)^s$ and $s \geq 2$, $t \geq 2$, we have $D > s$.
        have h_D_gt_s : D > s := by
          refine' lt_of_lt_of_le _ ( Nat.pow_le_pow_left ( Nat.self_le_factorial _ ) _ );
          exact lt_of_lt_of_le ( by nlinarith ) ( Nat.le_self_pow ( by linarith ) _ );
        cases abs_cases ( k - i ) <;> linarith [ Nat.sub_add_cancel ( show 1 ≤ s from by linarith ) ] ;
    -- Since $p \le st$, we have $v_p((j-l)D + (k-i)) = v_p(k-i)$.
    have h_valuation_eq : Nat.factorization (Int.natAbs ((j - l) * D + (k - i))) p = Nat.factorization (Int.natAbs (k - i)) p := by
      have h_valuation_eq : (p : ℤ) ^ Nat.factorization (Int.natAbs (k - i)) p ∣ (j - l) * D + (k - i) ∧ ¬(p : ℤ) ^ (Nat.factorization (Int.natAbs (k - i)) p + 1) ∣ (j - l) * D + (k - i) := by
        constructor;
        · refine' dvd_add _ _;
          · exact dvd_mul_of_dvd_right ( mod_cast Nat.dvd_trans ( pow_dvd_pow _ h_valuation_p.le ) ( Nat.ordProj_dvd _ _ ) ) _;
          · simpa [ ← Int.natCast_dvd_natCast ] using Int.natCast_dvd.mpr ( Nat.ordProj_dvd _ _ );
        · rw [ Int.dvd_add_right ];
          · exact fun h => absurd ( Int.natAbs_dvd_natAbs.mpr h ) ( by simpa [ Int.natAbs_pow ] using Nat.pow_succ_factorization_not_dvd ( Int.natAbs_ne_zero.mpr ( sub_ne_zero.mpr hδ ) ) hp );
          · exact dvd_mul_of_dvd_right ( mod_cast Nat.dvd_trans ( pow_dvd_pow _ h_valuation_p ) ( Nat.ordProj_dvd _ _ ) ) _;
      obtain ⟨ x, hx ⟩ := h_valuation_eq.1;
      rw [ hx, Int.natAbs_mul, Nat.factorization_mul ] <;> norm_num [ hp.ne_zero ];
      · simp +decide [ hp.factorization ];
        exact Nat.factorization_eq_zero_of_not_dvd fun h => h_valuation_eq.2 <| hx.symm ▸ mul_dvd_mul_left _ ( Int.natCast_dvd.mpr h ) |> fun h => by simpa [ pow_add ] using h;
      · rintro rfl; simp_all +decide ;
    linarith;
  have h_divides_k_i : d ∣ Int.natAbs (k - i) := by
    rw [ ← Nat.factorization_le_iff_dvd ];
    · intro p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ≤ s * t <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, ← Int.natCast_dvd_natCast ] ;
    · simp +zetaDelta at *;
      intro h H; simp_all +decide [ sub_eq_iff_eq_add ] ;
      exact absurd ( h_no_prime_gt_st ( Nat.find ( Nat.exists_infinite_primes ( s * t + 1 ) ) ) ( Nat.find_spec ( Nat.exists_infinite_primes ( s * t + 1 ) ) |>.2 ) ) ( by linarith [ Nat.find_spec ( Nat.exists_infinite_primes ( s * t + 1 ) ) |>.1 ] );
    · exact Int.natAbs_ne_zero.mpr ( sub_ne_zero.mpr hδ )
  exact Int.natCast_dvd.mpr h_divides_k_i |> fun h => Int.dvd_trans h ( by simp +decide ) ;

/-
There exist integers $a$ and $D$ such that the sequence $a_{i,j} = a + jD - i$ satisfies $\gcd(a_{i,j}, a_{k,l}) \mid (k-i)$ for all indices.
-/
lemma exists_sequence_gcd_property (s t : ℕ) (hs : s ≥ 2) (ht : t ≥ 2) :
    ∃ (a D : ℤ), D > 0 ∧ a > 2 * (t - 1) * D + 4 * s ∧
    let a_ij (i j : ℤ) := a + j * D - i
    ∀ i j k l : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t →
                   1 ≤ k ∧ k ≤ s ∧ 0 ≤ l ∧ l < t →
                   (Int.gcd (a_ij i j) (a_ij k l) : ℤ) ∣ (k - i) := by
                     obtain ⟨ a, ha ⟩ := exists_good_a s t hs ht;
                     use a, D_val s t, by
                       exact_mod_cast pow_pos ( Nat.factorial_pos _ ) _;
                     exact ⟨ ha.1, gcd_property_of_good_a s t hs ht a ha.2 ⟩

/-
Given a grid of moduli $a_{i,j}$ satisfying the GCD property, there exists $x_0$ such that $x_0 \equiv -i \pmod{a_{i,j}}$.
-/
lemma exists_solution_for_grid (s t : ℕ) (a D : ℤ)
    (h_gcd : ∀ i j k l : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t →
                            1 ≤ k ∧ k ≤ s ∧ 0 ≤ l ∧ l < t →
                            (Int.gcd (a + j * D - i) (a + l * D - k) : ℤ) ∣ (k - i)) :
    ∃ x₀ : ℤ, ∀ i j : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t → x₀ ≡ -i [ZMOD (a + j * D - i)] := by
  -- Let $L$ be the list of pairs $((a + jD - i), -i)$ for all valid $i, j$.
  set L := Finset.image (fun pq : ℤ × ℤ => ((a + pq.2 * D - pq.1), -pq.1)) (Finset.Icc 1 (s : ℤ) ×ˢ Finset.Ico 0 (t : ℤ)) with hL_def;
  -- By the generalized Chinese Remainder Theorem, there exists $x₀$ such that $x₀ \equiv -i \pmod{a + jD - i}$ for all $(i, j) \in L$.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℤ, ∀ pq ∈ L, x₀ ≡ pq.2 [ZMOD pq.1] := by
    convert generalized_chinese_remainder_list ( L.toList ) _ using 1;
    · simp +decide [ Finset.mem_toList ];
    · simp +zetaDelta at *;
      rintro a b c d x y hx hy hx' hy' rfl rfl u v hu hv hu' hv' rfl rfl; specialize h_gcd x y u v hx hy hx' hy' hu hv hu' hv'; simp_all +decide [ Int.modEq_iff_dvd ] ;
      convert h_gcd.neg_right using 1 ; ring;
  exact ⟨ x₀, fun i j hij => hx₀ _ <| Finset.mem_image.mpr ⟨ ( i, j ), Finset.mem_product.mpr ⟨ Finset.mem_Icc.mpr ⟨ hij.1, hij.2.1 ⟩, Finset.mem_Ico.mpr ⟨ hij.2.2.1, hij.2.2.2 ⟩ ⟩, rfl ⟩ ⟩

/-
The upper bound holds for $s, t \ge 2$.
-/
lemma erdos_650_upper_bound_st_main (s t : ℕ) (hs : s ≥ 2) (ht : t ≥ 2) :
    ∃ (N : ℕ) (A : Finset ℕ) (I : Set ℕ),
      A.card = s * t ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      (∃ x y, I = Set.Ioc x y ∧ y - x = 2 * N) ∧
      (∀ (M : Finset (ℕ × ℕ)),
        (∀ p ∈ M, p.1 ∈ A ∧ p.2 ∈ I ∧ p.1 ∣ p.2) →
        (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) →
        M.card ≤ s + t) := by
  -- Let's choose $N = a + (t-1)D - 1$.
  obtain ⟨a, D, hD_pos, ha_pos, h_gcd_prop⟩ : ∃ a D : ℤ, D > 0 ∧ a > 2 * (t - 1) * D + 4 * s ∧
    let a_ij (i j : ℤ) := a + j * D - i
    ∀ i j k l : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t →
      1 ≤ k ∧ k ≤ s ∧ 0 ≤ l ∧ l < t →
      (Int.gcd (a_ij i j) (a_ij k l) : ℤ) ∣ (k - i) := by
        exact exists_sequence_gcd_property s t hs ht;
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℤ, ∀ i j : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t → x₀ ≡ -i [ZMOD (a + j * D - i)] := by
    apply exists_solution_for_grid s t a D h_gcd_prop;
  -- Let $N = a + (t-1)D - 1$ and $T = a - 2s$.
  set N := Int.toNat (a + (t - 1) * D - 1)
  set T := Int.toNat (a - 2 * s);
  -- Let $x = x₀ + kP$ for a sufficiently large integer $k$ such that $x - T ≥ 0$.
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x - T ≥ 0 ∧ ∀ i j : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t → x ≡ -i [ZMOD (a + j * D - i)] := by
    -- Let $P = \prod_{i,j} (a + jD - i)$.
    set P := Finset.prod (Finset.Icc 1 (s : ℤ) ×ˢ Finset.Ico 0 (t : ℤ)) (fun p => a + p.2 * D - p.1) with hP_def;
    -- Let $x = x₀ + kP$ for a sufficiently large integer $k$ such that $x - T ≥ 0$. We can choose $k$ such that $x₀ + kP ≥ T$.
    obtain ⟨k, hk⟩ : ∃ k : ℤ, x₀ + k * P ≥ T := by
      -- Since $P$ is positive, we can choose $k$ such that $kP \geq T - x₀$.
      have hP_pos : 0 < P := by
        exact Finset.prod_pos fun p hp => by nlinarith [ Finset.mem_Icc.mp ( Finset.mem_product.mp hp |>.1 ), Finset.mem_Ico.mp ( Finset.mem_product.mp hp |>.2 ) ] ;
      exact ⟨ ⌊ ( T : ℤ ) - x₀⌋₊ + 1, by nlinarith [ Nat.lt_floor_add_one ( ( T : ℤ ) - x₀ ) ] ⟩;
    refine' ⟨ x₀ + k * P, by linarith, fun i j hij => _ ⟩;
    simp_all +decide [ Int.ModEq ];
    rw [ Int.add_emod, Int.mul_emod, Finset.prod_eq_prod_diff_singleton_mul <| show ( i, j ) ∈ Finset.Icc 1 ( s : ℤ ) ×ˢ Finset.Ico 0 ( t : ℤ ) from Finset.mem_product.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, Finset.mem_Ico.mpr ⟨ by linarith, by linarith ⟩ ⟩ ] ; aesop;
  -- Let $A$ be the set of integers $a_{i,j} = a + jD - i$ for $1 \leq i \leq s$ and $0 \leq j < t$.
  set A : Finset ℕ := Finset.image (fun p : ℤ × ℤ => Int.toNat (a + p.2 * D - p.1)) (Finset.product (Finset.Icc 1 s) (Finset.Ico 0 t));
  refine' ⟨ N, A, Set.Ioc ( Int.toNat ( x - T ) ) ( Int.toNat ( x - T ) + 2 * N ), _, _, _, _ ⟩;
  · erw [ Finset.card_image_of_injOn, Finset.card_product ] ; aesop;
    norm_num [ Set.InjOn ];
    intro i j hi hj hi' hj' k l hk hl hk' hl' h; rw [ ← Int.ofNat_inj ] at *; simp_all +decide ;
    rw [ max_eq_left, max_eq_left ] at h <;> try nlinarith;
    have := h_gcd_prop i j k l hi hj hi' hj' hk hl hk' hl'; simp_all +decide [ Int.ModEq ] ;
    obtain ⟨ m, hm ⟩ := this;
    rcases lt_trichotomy m 0 with hm' | rfl | hm';
    · nlinarith [ show a + l * D - k > 0 by nlinarith ];
    · exact ⟨ by linarith, by nlinarith ⟩;
    · nlinarith [ show a + l * D - k > 0 by nlinarith ];
  · simp +zetaDelta at *;
    rintro _ i j hi hj hi' hj' rfl; refine' ⟨ _, _ ⟩ <;> norm_num [ Int.toNat_of_nonneg ];
    · exact Nat.pos_of_ne_zero ( by norm_num; nlinarith );
    · rw [ Nat.cast_sub ] <;> norm_num;
      · cases max_cases ( a + ( t - 1 ) * D ) 0 <;> nlinarith;
      · exact Nat.one_le_iff_ne_zero.mpr ( by norm_num; nlinarith );
  · exact ⟨ _, _, rfl, Nat.sub_eq_of_eq_add <| by ring ⟩;
  · intro M hM₁ hM₂;
    -- Let $B$ be the set of multiples of $a_{i,j}$ in $I$.
    set B : Finset ℕ := Finset.image (fun p : ℤ × ℤ => Int.toNat (x + p.1)) (Finset.product (Finset.Icc 1 s) (Finset.Icc 0 0)) ∪ Finset.image (fun p : ℤ × ℤ => Int.toNat (x + a + p.2 * D)) (Finset.product (Finset.Icc 0 0) (Finset.Ico 0 t));
    -- Any matching maps $A$ to $B \cap I$.
    have h_matching : ∀ p ∈ M, p.2 ∈ B := by
      intro p hp
      obtain ⟨hpA, hpI, hp_div⟩ := hM₁ p hp
      obtain ⟨i, j, hi, hj, hp_eq⟩ : ∃ i j : ℤ, 1 ≤ i ∧ i ≤ s ∧ 0 ≤ j ∧ j < t ∧ p.1 = Int.toNat (a + j * D - i) := by
        rw [ Finset.mem_image ] at hpA; obtain ⟨ p, hp, hp' ⟩ := hpA; use p.1, p.2; erw [ Finset.mem_product ] at hp; aesop;
      -- Since $p.1 \mid p.2$, we have $p.2 = x + i + m(a + jD - i)$ for some integer $m$.
      obtain ⟨m, hm⟩ : ∃ m : ℤ, p.2 = x + i + m * (a + j * D - i) := by
        obtain ⟨ m, hm ⟩ := Int.modEq_iff_dvd.mp ( hx.2 i j ⟨ hi, hj, hp_eq.1, hp_eq.2.1 ⟩ |> Int.ModEq.symm );
        obtain ⟨ k, hk ⟩ := hp_div;
        exact ⟨ k - m, by push_cast [ hk, hp_eq.2.2 ] ; nlinarith [ Int.toNat_of_nonneg ( show 0 ≤ a + j * D - i by nlinarith ) ] ⟩;
      -- Since $p.2 \in I$, we have $x - T < p.2 \leq x - T + 2N$.
      have hp_bounds : x - T < p.2 ∧ p.2 ≤ x - T + 2 * N := by
        constructor <;> linarith [ hpI.1, hpI.2, Int.toNat_of_nonneg hx.1 ];
      -- Since $m$ must be $0$ or $1$, we have $p.2 = x + i$ or $p.2 = x + a + jD$.
      have hm_cases : m = 0 ∨ m = 1 := by
        by_cases hm_neg : m < 0;
        · nlinarith [ Int.toNat_of_nonneg ( by nlinarith : 0 ≤ a + j * D - i ), Int.toNat_of_nonneg ( by nlinarith : 0 ≤ a - 2 * s ) ];
        · by_cases hm_pos : m > 1;
          · nlinarith [ Int.toNat_of_nonneg ( by nlinarith : 0 ≤ a + ( t - 1 ) * D - 1 ), Int.toNat_of_nonneg ( by nlinarith : 0 ≤ a - 2 * s ), mul_le_mul_of_nonneg_left hm_pos.le hD_pos.le ];
          · interval_cases m <;> trivial;
      rcases hm_cases with ( rfl | rfl ) <;> norm_num at hm ⊢;
      · simp +zetaDelta at *;
        exact Or.inl ⟨ i, ⟨ hi, hj ⟩, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ x + i ) ] ⟩;
      · simp +zetaDelta at *;
        exact Or.inr ⟨ j, ⟨ hp_eq.1, hp_eq.2.1 ⟩, by omega ⟩;
    have h_card_B : B.card ≤ s + t := by
      refine' le_trans ( Finset.card_union_le _ _ ) _;
      refine' add_le_add _ _;
      · exact Finset.card_image_le.trans ( by erw [ Finset.card_product ] ; norm_num );
      · exact Finset.card_image_le.trans ( by erw [ Finset.card_product ] ; norm_num );
    have h_card_M : M.card ≤ Finset.card (Finset.image (fun p => p.2) M) := by
      rw [ Finset.card_image_of_injOn ];
      exact fun p hp q hq hpq => Classical.not_not.1 fun hpq' => hM₂ p q hp hq hpq' |>.2 hpq;
    exact h_card_M.trans ( le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun p hp => h_matching p hp ) h_card_B )

/-
The upper bound holds for all $s, t \ge 1$.
-/
theorem erdos_650_upper_bound_st (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ 1) :
    ∃ (N : ℕ) (A : Finset ℕ) (I : Set ℕ),
      A.card = s * t ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      (∃ x y, I = Set.Ioc x y ∧ y - x = 2 * N) ∧
      (∀ (M : Finset (ℕ × ℕ)),
        (∀ p ∈ M, p.1 ∈ A ∧ p.2 ∈ I ∧ p.1 ∣ p.2) →
        (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) →
        M.card ≤ s + t) := by
  -- Consider two cases: $s=1$ or $t=1$.
  by_cases hs1 : s = 1 ∨ t = 1;
  · rcases hs1 with ( rfl | rfl );
    · refine' ⟨ t, Finset.Icc 1 t, Set.Ioc 0 ( 2 * t ), _, _, _, _ ⟩ <;> norm_num ; aesop;
      intro M hM₁ hM₂;
      -- Since $M$ is a matching, each element in $M$ must have a unique first component.
      have h_unique_first : (Finset.image Prod.fst M).card ≤ t := by
        exact le_trans ( Finset.card_le_card ( Finset.image_subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ( hM₁ _ _ hx |>.1 ) ) ) ( by simp );
      rw [ Finset.card_image_of_injOn ] at h_unique_first;
      · grind;
      · intro x hx y hy; specialize hM₂ _ _ _ _ hx hy; aesop;
    · norm_num +zetaDelta at *;
      refine' ⟨ s, Finset.Icc 1 s, _, _, _ ⟩ <;> norm_num;
      refine' ⟨ Set.Ioc 0 ( 2 * s ), ⟨ 0, 2 * s, rfl, rfl ⟩, fun M hM₁ hM₂ => _ ⟩;
      -- Since $M$ is a matching, each element in $M$ corresponds to a unique divisor of some element in $A$.
      have h_divisors : M.card ≤ Finset.card (Finset.image (fun p => p.1) M) := by
        rw [ Finset.card_image_of_injOn ] ; intro p hp q hq ; specialize hM₂ _ _ _ _ hp hq ; aesop;
      exact h_divisors.trans ( le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun p hp => Finset.mem_Icc.mpr <| hM₁ _ _ hp |>.1 ) <| by norm_num );
  · convert erdos_650_upper_bound_st_main s t ( Nat.lt_of_le_of_ne hs ( Ne.symm ( by tauto ) ) ) ( Nat.lt_of_le_of_ne ht ( Ne.symm ( by tauto ) ) ) using 1

/-
If a bipartite graph with |U| ≥ 4 satisfies the condition that for every nonempty subset S of U, the size of its neighborhood is at least ⌈2√|S|⌉, then there exists a matching of size at least ⌈2√|U|⌉.
-/
lemma matching_size_from_growth_condition (U V : Finset ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (h_card : U.card ≥ 4)
    (h_growth : ∀ S ⊆ U, S.Nonempty → (S.biUnion (fun u => V.filter (R u))).card ≥ Nat.ceil (2 * Real.sqrt (S.card : ℝ))) :
    ∃ (M : Finset (ℕ × ℕ)),
      (∀ p ∈ M, p.1 ∈ U ∧ p.2 ∈ V ∧ R p.1 p.2) ∧
      (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      M.card ≥ Nat.ceil (2 * Real.sqrt (U.card : ℝ)) := by
        -- Construct a new bipartite graph $G'$ by adding $d$ dummy vertices to $V$, each connected to all vertices in $U$.
        set d := U.card - Nat.ceil (2 * Real.sqrt (U.card : ℝ))
        set V' := V ∪ Finset.image (fun i => V.sup id + i + 1) (Finset.range d) with hV';
        -- By Hall's Marriage Theorem, there exists a matching in $G'$ covering $U$.
        obtain ⟨M', hM'⟩ : ∃ M' : Finset (ℕ × ℕ), (∀ p ∈ M', p.1 ∈ U ∧ p.2 ∈ V' ∧ (if p.2 ∈ V then R p.1 p.2 else True)) ∧ (∀ p q, p ∈ M' → q ∈ M' → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧ M'.card = U.card := by
          have h_hall : ∀ S ⊆ U, S.Nonempty → (Finset.biUnion S (fun u => Finset.filter (fun v => if v ∈ V then R u v else True) V')).card ≥ S.card := by
            intros S hS_sub hS_nonempty
            have h_neighborhood : (Finset.biUnion S (fun u => Finset.filter (fun v => if v ∈ V then R u v else True) V')).card ≥ (Finset.biUnion S (fun u => Finset.filter (R u) V)).card + d := by
              have h_neighborhood : (Finset.biUnion S (fun u => Finset.filter (fun v => if v ∈ V then R u v else True) V')).card ≥ (Finset.biUnion S (fun u => Finset.filter (R u) V)).card + (Finset.biUnion S (fun u => Finset.filter (fun v => v ∉ V) V')).card := by
                rw [ ← Finset.card_union_of_disjoint ];
                · refine Finset.card_mono ?_;
                  simp +decide [ Finset.subset_iff ];
                  grind +ring;
                · simp +contextual [ Finset.disjoint_left ];
              refine le_trans ?_ h_neighborhood;
              refine' add_le_add_left ( le_trans _ ( Finset.card_mono <| show Finset.image ( fun i => V.sup id + i + 1 ) ( Finset.range d ) ⊆ S.biUnion ( fun u => { v ∈ V' | v∉V } ) from _ ) ) _;
              · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
              · simp +decide [ Finset.subset_iff ];
                exact fun a ha => ⟨ hS_nonempty, Finset.mem_union_right _ <| Finset.mem_image_of_mem _ <| Finset.mem_range.mpr ha, fun h => not_lt_of_ge ( Finset.le_sup ( f := id ) h ) <| Nat.lt_succ_of_le <| Nat.le_add_right _ _ ⟩;
            have h_ceil_ge_card : Nat.ceil (2 * Real.sqrt (S.card : ℝ)) + U.card - Nat.ceil (2 * Real.sqrt (U.card : ℝ)) ≥ S.card := by
              have h_ceil_ge_card : Nat.ceil (2 * Real.sqrt (U.card : ℝ)) ≤ Nat.ceil (2 * Real.sqrt (S.card : ℝ)) + U.card - S.card := by
                refine Nat.ceil_le.mpr ?_;
                rw [ Nat.cast_sub ] <;> norm_num;
                · have := Nat.le_ceil ( 2 * Real.sqrt S.card );
                  nlinarith only [ this, show ( S.card : ℝ ) ≤ U.card by exact_mod_cast Finset.card_le_card hS_sub, Real.mul_self_sqrt ( Nat.cast_nonneg S.card ), Real.mul_self_sqrt ( Nat.cast_nonneg U.card ), Real.sqrt_nonneg S.card, Real.sqrt_nonneg U.card, show ( ⌈2 * Real.sqrt S.card⌉₊ : ℝ ) ≥ 2 by exact_mod_cast Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; nlinarith only [ show ( S.card : ℝ ) ≥ 1 by exact_mod_cast Finset.card_pos.mpr hS_nonempty, Real.sqrt_nonneg S.card, Real.sq_sqrt ( Nat.cast_nonneg S.card ) ] ) ) ];
                · exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( Finset.card_le_card hS_sub )
              exact le_tsub_of_add_le_left ( by linarith [ Nat.sub_add_cancel ( show S.card ≤ ⌈2 * Real.sqrt S.card⌉₊ + U.card from by linarith [ show S.card ≤ U.card from Finset.card_le_card hS_sub ] ) ] );
            exact le_trans h_ceil_ge_card ( by rw [ Nat.add_sub_assoc ( show ⌈2 * Real.sqrt U.card⌉₊ ≤ U.card from Nat.ceil_le.mpr <| by nlinarith only [ Real.mul_self_sqrt <| Nat.cast_nonneg U.card, show ( U.card :ℝ ) ≥ 4 by norm_cast ] ) ] ; linarith [ h_growth S hS_sub hS_nonempty ] );
          have h_hall : ∀ S ⊆ U, S.Nonempty → (Finset.biUnion S (fun u => Finset.filter (fun v => if v ∈ V then R u v else True) V')).card ≥ S.card := by
            assumption
          have h_hall_theorem : ∀ (G : ℕ → Finset ℕ), (∀ S ⊆ U, S.Nonempty → (Finset.biUnion S G).card ≥ S.card) → ∃ M : Finset (ℕ × ℕ), (∀ p ∈ M, p.1 ∈ U ∧ p.2 ∈ G p.1) ∧ (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧ M.card = U.card := by
            intros G hG
            obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, (∀ u ∈ U, f u ∈ G u) ∧ (∀ u v, u ∈ U → v ∈ U → u ≠ v → f u ≠ f v) := by
              have h_hall_theorem : ∀ (G : ℕ → Finset ℕ), (∀ S ⊆ U, S.Nonempty → (Finset.biUnion S G).card ≥ S.card) → ∃ f : ℕ → ℕ, (∀ u ∈ U, f u ∈ G u) ∧ (∀ u v, u ∈ U → v ∈ U → u ≠ v → f u ≠ f v) := by
                intros G hG
                have h_hall : ∀ S ⊆ U, S.Nonempty → (Finset.biUnion S G).card ≥ S.card := hG
                have := Finset.all_card_le_biUnion_card_iff_exists_injective ( fun u : U => G u );
                obtain ⟨ f, hf₁, hf₂ ⟩ := this.mp ( fun s => by
                  by_cases hs : s.Nonempty <;> simp_all +decide [Function.Injective];
                  convert h_hall ( s.image Subtype.val ) _ _ using 1 <;> simp_all +decide [ Finset.subset_iff ];
                  · rw [ Finset.card_image_of_injective _ Subtype.coe_injective ];
                  · congr! 1;
                    ext; simp [Finset.mem_biUnion, Finset.mem_image] );
                use fun u => if hu : u ∈ U then f ⟨ u, hu ⟩ else 0;
                simp_all +decide [ Function.Injective ];
                exact fun u v hu hv huv => fun h => huv <| hf₁ u hu v hv h;
              exact h_hall_theorem G hG;
            use Finset.image (fun u => (u, f u)) U;
            simp +zetaDelta at *;
            exact ⟨ fun u hu => ⟨ hu, hf.1 u hu ⟩, by aesop, by rw [ Finset.card_image_of_injOn fun u hu v hv huv => by aesop ] ⟩;
          specialize h_hall_theorem (fun u => Finset.filter (fun v => if v ∈ V then R u v else True) V') h_hall;
          exact ⟨ h_hall_theorem.choose, fun p hp => ⟨ h_hall_theorem.choose_spec.1 p hp |>.1, Finset.mem_filter.mp ( h_hall_theorem.choose_spec.1 p hp |>.2 ) |>.1, Finset.mem_filter.mp ( h_hall_theorem.choose_spec.1 p hp |>.2 ) |>.2 ⟩, h_hall_theorem.choose_spec.2.1, h_hall_theorem.choose_spec.2.2 ⟩;
        -- Let $M$ be the subset of $M'$ consisting of edges where the second element is in $V$.
        set M := M'.filter (fun p => p.2 ∈ V) with hM;
        -- We need to show that $M.card \geq \lceil 2\sqrt{U.card} \rceil$.
        have hM_card : M.card ≥ U.card - d := by
          have hM_card : (M' \ M).card ≤ d := by
            have hM'_not_M : (M' \ M).image Prod.snd ⊆ Finset.image (fun i => V.sup id + i + 1) (Finset.range d) := by
              grind;
            have := Finset.card_le_card hM'_not_M; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
            rwa [ Finset.card_image_of_injOn ] at this ; intro a ha b hb ; specialize hM' ; have := hM'.2.1 _ _ _ _ ( Finset.mem_sdiff.mp ha |>.1 ) ( Finset.mem_sdiff.mp hb |>.1 ) ; aesop;
          grind;
        -- Therefore, $M.card \geq \lceil 2\sqrt{U.card} \rceil$.
        have hM_card_final : M.card ≥ Nat.ceil (2 * Real.sqrt (U.card : ℝ)) := by
          exact le_trans ( by rw [ Nat.sub_sub_self ( show ⌈2 * Real.sqrt U.card⌉₊ ≤ U.card from Nat.ceil_le.mpr <| by nlinarith only [ Real.mul_self_sqrt <| Nat.cast_nonneg U.card, show ( U.card :ℝ ) ≥ 4 by norm_cast ] ) ] ) hM_card;
        exact ⟨ M, fun p hp => by have := hM'.1 p ( Finset.mem_filter.mp hp |>.1 ) ; aesop, fun p q hp hq hpq => hM'.2.1 p q ( Finset.mem_filter.mp hp |>.1 ) ( Finset.mem_filter.mp hq |>.1 ) hpq, hM_card_final ⟩

/-
For any positive integer a <= N and real x not a multiple of N, there is a multiple m of a such that m is in (x, x+N] and m+a is in (x+N, x+2N).
-/
lemma exists_crossing_multiple (N : ℕ) (x : ℝ) (a : ℕ)
    (ha_pos : a > 0)
    (ha_le_N : a ≤ N)
    (hx_not_int_N : ∀ k : ℤ, x ≠ k * N) :
    ∃ m : ℤ, (a : ℤ) ∣ m ∧
             (x < m ∧ m ≤ x + N) ∧
             (x + N < m + a ∧ m + a < x + 2 * N) := by
               -- Let $m = \lfloor x/a \rfloor \cdot a + a$. Then $m$ is a multiple of $a$ and $x < m \le x + a \le x + N$.
               obtain ⟨m, hm⟩ : ∃ m : ℤ, (a : ℤ) ∣ m ∧ x < m ∧ m ≤ x + N := by
                 refine' ⟨ a * ⌊x / a⌋ + a, _, _, _ ⟩ <;> norm_num [ ha_pos ];
                 · nlinarith [ Int.lt_floor_add_one ( x / a ), show ( a : ℝ ) > 0 by positivity, mul_div_cancel₀ x ( by positivity : ( a : ℝ ) ≠ 0 ) ];
                 · nlinarith [ Int.floor_le ( x / a ), show ( a : ℝ ) ≤ N by norm_cast, mul_div_cancel₀ x ( by positivity : ( a : ℝ ) ≠ 0 ) ];
               obtain ⟨hm₁, hm₂, hm₃⟩ : (a : ℤ) ∣ m ∧ x < m ∧ m ≤ x + N := hm;
               -- Let $m$ be the largest multiple of $a$ in $(x, x+N]$.
               obtain ⟨m, hm⟩ : ∃ m : ℤ, (a : ℤ) ∣ m ∧ x < m ∧ m ≤ x + N ∧ ∀ n : ℤ, (a : ℤ) ∣ n → x < n → n ≤ x + N → n ≤ m := by
                 have hm_max : ∃ m ∈ {n : ℤ | (a : ℤ) ∣ n ∧ x < n ∧ n ≤ x + N}, ∀ n ∈ {n : ℤ | (a : ℤ) ∣ n ∧ x < n ∧ n ≤ x + N}, n ≤ m := by
                   apply_rules [ Int.exists_greatest_of_bdd ];
                   · exact ⟨ ⌊x + N⌋, fun z hz => Int.le_floor.2 hz.2.2 ⟩;
                   · exact ⟨ m, hm₁, hm₂, hm₃ ⟩;
                 aesop;
               refine' ⟨ m, hm.1, ⟨ hm.2.1, hm.2.2.1 ⟩, _, _ ⟩;
               · contrapose! hm;
                 exact fun h₁ h₂ h₃ => ⟨ m + a, by simpa using h₁.add ( dvd_refl _ ), by push_cast; linarith, by push_cast; linarith, by linarith ⟩;
               · -- Since $x$ is not a multiple of $N$, $x + 2N$ is not a multiple of $a$ if $a = N$.
                 by_cases ha_eq_N : a = N;
                 · contrapose! hx_not_int_N;
                   obtain ⟨ k, hk ⟩ := hm.1; use k - 1; push_cast [ * ] at *; linarith;
                 · linarith [ show ( a : ℝ ) < N by exact_mod_cast lt_of_le_of_ne ha_le_N ha_eq_N ]

/-
For a nonempty set A of positive integers with max N, and an interval I=(x, x+2N) where x is not a multiple of N, the divisibility graph satisfies the condition that the neighborhood size of any subset S is at least 2*sqrt(|S|).
-/
lemma divisibility_graph_growth (A : Finset ℕ) (N : ℕ) (x : ℝ)
    (hA_nonempty : A.Nonempty)
    (hA_pos : ∀ a ∈ A, a > 0)
    (hN : N = A.max' hA_nonempty)
    (hx_not_int_N : ∀ k : ℤ, x ≠ k * N) :
    let I := Set.Ioo x (x + 2 * N)
    let V : Finset ℤ := (Finset.Ico (Int.floor x + 1) (Int.ceil (x + 2 * N))).filter (fun n => (n : ℝ) ∈ I)
    let R := fun (a : ℕ) (b : ℤ) => (a : ℤ) ∣ b
    ∀ S ⊆ A, S.Nonempty → (S.biUnion (fun a => V.filter (R a))).card ≥ Nat.ceil (2 * Real.sqrt (S.card : ℝ)) := by
      intro I V R S hS hS_nonempty
      have h_map : ∃ f : ℕ → ℤ × ℤ, (∀ a ∈ S, (a : ℤ) ∣ (f a).1 ∧ (a : ℤ) ∣ (f a).2 ∧ (x < (f a).1 ∧ (f a).1 ≤ x + N) ∧ (x + N < (f a).2 ∧ (f a).2 < x + 2 * N)) ∧ (∀ a b, a ∈ S → b ∈ S → a ≠ b → f a ≠ f b) := by
        have h_map : ∀ a ∈ S, ∃ m : ℤ, (a : ℤ) ∣ m ∧ (x < m ∧ m ≤ x + N) ∧ (x + N < m + a ∧ m + a < x + 2 * N) := by
          intro a ha
          apply exists_crossing_multiple N x a (hA_pos a (hS ha)) (by
          exact hN ▸ Finset.le_max' _ _ ( hS ha )) hx_not_int_N;
        choose! f hf using h_map;
        use fun a => ( f a, f a + a ) ; aesop;
      obtain ⟨ f, hf1, hf2 ⟩ := h_map;
      -- Let $\Gamma_-(S) = \bigcup_{a \in S} \{v \in B_- \mid a \mid v\}$ and $\Gamma_+(S) = \bigcup_{a \in S} \{v \in B_+ \mid a \mid v\}$.
      set Γ_minus := Finset.biUnion S (fun a => Finset.filter (fun v => (a : ℤ) ∣ v) (Finset.filter (fun v => v ≤ x + N) V))
      set Γ_plus := Finset.biUnion S (fun a => Finset.filter (fun v => (a : ℤ) ∣ v) (Finset.filter (fun v => v > x + N) V));
      -- By definition of $f$, we know that $|S| \leq |\Gamma_-(S)| \cdot |\Gamma_+(S)|$.
      have h_card : S.card ≤ Γ_minus.card * Γ_plus.card := by
        have h_card : S.card ≤ (Finset.image (fun a => (f a).1) S).card * (Finset.image (fun a => (f a).2) S).card := by
          have h_card : S.card ≤ (Finset.image (fun a => ((f a).1, (f a).2)) S).card := by
            rw [ Finset.card_image_of_injOn fun a ha b hb hab => by contrapose! hab; aesop ];
          exact h_card.trans ( by rw [ ← Finset.card_product ] ; exact Finset.card_le_card <| Finset.image_subset_iff.mpr fun a ha => Finset.mem_product.mpr ⟨ Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ ha ⟩ );
        refine le_trans h_card <| Nat.mul_le_mul ?_ ?_;
        · refine Finset.card_le_card ?_;
          simp +zetaDelta at *;
          simp +decide [ Finset.subset_iff ];
          exact fun a ha => ⟨ a, ha, ⟨ ⟨ ⟨ Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hf1 a ha, Int.floor_le x, Int.lt_floor_add_one x ], Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hf1 a ha, Int.le_ceil ( x + 2 * N ), Int.ceil_lt_add_one ( x + 2 * N ) ] ⟩, hf1 a ha |>.2.2.1.1, by linarith [ hf1 a ha, Int.le_ceil ( x + 2 * N ), Int.ceil_lt_add_one ( x + 2 * N ) ] ⟩, hf1 a ha |>.2.2.1.2 ⟩, hf1 a ha |>.1 ⟩;
        · refine Finset.card_le_card ?_;
          simp +zetaDelta at *;
          simp +decide [ Finset.subset_iff ];
          exact fun a ha => ⟨ a, ha, ⟨ ⟨ ⟨ Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hf1 a ha, Int.floor_le x, Int.lt_floor_add_one x ], Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hf1 a ha, Int.le_ceil ( x + 2 * N ), Int.ceil_lt_add_one ( x + 2 * N ) ] ⟩, by linarith [ hf1 a ha ], by linarith [ hf1 a ha ] ⟩, by linarith [ hf1 a ha ] ⟩, by simpa using hf1 a ha |>.2.1 ⟩;
      -- Since $\Gamma_-(S)$ and $\Gamma_+(S)$ are disjoint subsets of $\Gamma(S)$, we have $|\Gamma(S)| \geq |\Gamma_-(S)| + |\Gamma_+(S)|$.
      have h_card_union : (Finset.biUnion S (fun a => Finset.filter (R a) V)).card ≥ Γ_minus.card + Γ_plus.card := by
        rw [ ← Finset.card_union_of_disjoint ];
        · refine Finset.card_le_card ?_;
          grind;
        · simp +zetaDelta at *;
          simp +contextual [ Finset.disjoint_left ];
      refine Nat.ceil_le.mpr ?_;
      nlinarith only [ show ( S.card : ℝ ) ≤ Γ_minus.card * Γ_plus.card by exact_mod_cast h_card, show ( Γ_minus.card + Γ_plus.card : ℝ ) ≤ ( S.biUnion fun a => Finset.filter ( R a ) V ).card by exact_mod_cast h_card_union, sq_nonneg ( Γ_minus.card - Γ_plus.card : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg S.card ) ]

/-
Generalization of the matching size lemma to arbitrary finite types.
-/
lemma matching_size_general {α β : Type} [DecidableEq α] [DecidableEq β] (U : Finset α) (V : Finset β) (R : α → β → Prop) [DecidableRel R]
    (h_card : U.card ≥ 4)
    (h_growth : ∀ S ⊆ U, S.Nonempty → (S.biUnion (fun u => V.filter (R u))).card ≥ Nat.ceil (2 * Real.sqrt (S.card : ℝ))) :
    ∃ (M : Finset (α × β)),
      (∀ p ∈ M, p.1 ∈ U ∧ p.2 ∈ V ∧ R p.1 p.2) ∧
      (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      M.card ≥ Nat.ceil (2 * Real.sqrt (U.card : ℝ)) := by
        -- Define the function f that maps elements of U to ℕ.
        obtain ⟨f, hf⟩ : ∃ f : α → ℕ, (∀ u ∈ U, f u ∈ Finset.range U.card) ∧ (∀ u v : α, u ∈ U → v ∈ U → u ≠ v → f u ≠ f v) := by
          -- Since $U$ is finite, we can define a bijection $f : U \to \{0, 1, ..., U.card - 1\}$.
          obtain ⟨f, hf⟩ : ∃ f : U ≃ Fin U.card, True := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide, trivial ⟩;
          refine' ⟨ fun u => if hu : u ∈ U then f ⟨ u, hu ⟩ else 0, _, _ ⟩ <;> simp +contextual [ Finset.mem_range ];
          exact fun u v hu hv huv => fun h => huv <| by simpa [ Fin.ext_iff ] using f.injective <| Fin.ext h;
        -- Define the function g that maps elements of V to ℕ.
        obtain ⟨g, hg⟩ : ∃ g : β → ℕ, (∀ v ∈ V, g v ∈ Finset.range V.card) ∧ (∀ v w : β, v ∈ V → w ∈ V → v ≠ w → g v ≠ g w) := by
          have h_equiv : Nonempty (V ≃ Fin V.card) := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
          obtain ⟨ g ⟩ := h_equiv;
          exact ⟨ fun v => if hv : v ∈ V then g ⟨ v, hv ⟩ |> Fin.val else 0, fun v hv => by simp +decide [ hv ], fun v w hv hw h => by simpa [ hv, hw ] using fun h' => h <| by simpa [ hv, hw ] using g.injective <| Fin.ext h' ⟩;
        -- Define the new relation R' on ℕ × ℕ.
        set R' : ℕ → ℕ → Prop := fun u v => ∃ u' ∈ U, ∃ v' ∈ V, f u' = u ∧ g v' = v ∧ R u' v';
        -- Apply the matching size lemma to the new relation R'.
        obtain ⟨M', hM'⟩ : ∃ M' : Finset (ℕ × ℕ),
          (∀ p ∈ M', p.1 ∈ Finset.image f U ∧ p.2 ∈ Finset.image g V ∧ R' p.1 p.2) ∧
          (∀ p q : ℕ × ℕ, p ∈ M' → q ∈ M' → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
          M'.card ≥ Nat.ceil (2 * Real.sqrt (Finset.card (Finset.image f U))) := by
            convert matching_size_from_growth_condition ( Finset.image f U ) ( Finset.image g V ) R' _ _ using 1;
            · rw [ Finset.card_image_of_injOn fun u hu v hv huv => by contrapose! huv; exact hf.2 u v hu hv huv ] ; linarith;
            · intro S hS₁ hS₂; specialize h_growth ( Finset.filter ( fun u => f u ∈ S ) U ) ; simp_all +decide [ Finset.subset_iff ] ;
              convert h_growth _ using 1;
              · rw [ show S = Finset.image f ( Finset.filter ( fun u => f u ∈ S ) U ) from ?_, Finset.card_image_of_injOn ];
                · congr! 3;
                  congr! 1;
                  ext; aesop;
                · exact fun x hx y hy hxy => Classical.not_not.1 fun h => hf.2 x y ( Finset.mem_filter.mp hx |>.1 ) ( Finset.mem_filter.mp hy |>.1 ) h hxy;
                · grind;
              · rw [ show ( S.biUnion fun u => Finset.filter ( R' u ) ( Finset.image g V ) ) = Finset.image ( fun v => g v ) ( Finset.biUnion ( Finset.filter ( fun u => f u ∈ S ) U ) fun u => Finset.filter ( R u ) V ) from ?_, Finset.card_image_of_injOn ];
                · exact fun x hx y hy hxy => Classical.not_not.1 fun h => hg.2 x y ( by aesop ) ( by aesop ) h hxy;
                · ext; simp [R'];
                  grind;
              · exact Exists.elim hS₂ fun x hx => Exists.elim ( hS₁ hx ) fun u hu => ⟨ u, by aesop ⟩;
        -- Define the new matching M in terms of the original sets U and V.
        obtain ⟨M, hM⟩ : ∃ M : Finset (α × β), (∀ p ∈ M, p.1 ∈ U ∧ p.2 ∈ V ∧ R p.1 p.2) ∧ (∀ p q : α × β, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧ M.card = M'.card := by
          choose! u hu v hv huv using fun p hp => hM'.1 p hp |>.2.2;
          use Finset.image (fun p => (u p.1 p.2, v p.1 p.2)) (Finset.attach M');
          simp +zetaDelta at *;
          refine' ⟨ _, _, _ ⟩;
          · grind +ring;
          · grind +ring;
          · rw [ Finset.card_image_of_injOn ];
            · rw [ Finset.card_attach ];
            · intro p hp q hq h_eq; have := huv _ _ p.2; have := huv _ _ q.2; aesop;
        use M;
        exact ⟨ hM.1, hM.2.1, hM.2.2.symm ▸ hM'.2.2.trans' ( by rw [ Finset.card_image_of_injOn fun u hu v hv huv => by contrapose! huv; exact hf.2 u v hu hv huv ] ) ⟩

/-
If x is not a multiple of N, then there exists a matching of size at least ⌈2√m⌉.
-/
lemma erdos_650_lower_bound_case1 (m : ℕ) (hm : m ≥ 4)
    (A : Finset ℕ) (N : ℕ) (hA_card : A.card = m) (hA_pos : ∀ a ∈ A, a > 0) (hN : N = A.max' (by
    exact Finset.card_pos.mp ( by linarith )))
    (x : ℝ) (hx_not_int_N : ∀ k : ℤ, x ≠ k * N) :
    let I := Set.Ioo x (x + 2 * N)
    ∃ (M : Finset (ℕ × ℤ)),
      (∀ p ∈ M, p.1 ∈ A ∧ (p.2 : ℝ) ∈ I ∧ (p.1 : ℤ) ∣ p.2) ∧
      (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      M.card ≥ Nat.ceil (2 * Real.sqrt m) := by
        all_goals generalize_proofs at *;
        obtain ⟨ M, hM ⟩ := matching_size_general A ( Finset.filter ( fun n : ℤ => ( n : ℝ ) ∈ Set.Ioo x ( x + 2 * N ) ) ( Finset.Ico ( Int.floor x + 1 ) ( Int.ceil ( x + 2 * N ) ) ) ) ( fun a b => ( a : ℤ ) ∣ b ) ( by linarith ) ( by
          intros S hS_sub hS_nonempty
          apply divisibility_graph_growth A N x (by
          assumption) (by
          assumption) (by
          exact hN) (by
          assumption) S hS_sub hS_nonempty );
        exact ⟨ M, fun p hp => ⟨ hM.1 p hp |>.1, by simpa using hM.1 p hp |>.2.1 |> fun h => Finset.mem_filter.mp h |>.2, hM.1 p hp |>.2.2 ⟩, hM.2.1, by simpa [ hA_card ] using hM.2.2 ⟩

/-
For m >= 4, ceil(2*sqrt(m)) <= ceil(2*sqrt(m-1)) + 1.
-/
lemma ceil_sqrt_inequality (m : ℕ) (hm : m ≥ 4) :
    Nat.ceil (2 * Real.sqrt m) ≤ Nat.ceil (2 * Real.sqrt (m - 1)) + 1 := by
      have h_diff : 2 * Real.sqrt m - 2 * Real.sqrt (m - 1) < 1 := by
        nlinarith only [ show ( m : ℝ ) ≥ 4 by norm_cast, Real.sqrt_nonneg ( m : ℝ ), Real.sq_sqrt ( show ( m : ℝ ) ≥ 0 by positivity ), Real.sqrt_nonneg ( m - 1 : ℝ ), Real.sq_sqrt ( show ( m - 1 : ℝ ) ≥ 0 by norm_num; linarith ), mul_pos ( Real.sqrt_pos.mpr ( show ( m : ℝ ) > 0 by positivity ) ) ( Real.sqrt_pos.mpr ( show ( m - 1 : ℝ ) > 0 by norm_num; linarith ) ) ];
      exact Nat.ceil_le.mpr ( by norm_num; linarith [ Nat.le_ceil ( 2 * Real.sqrt ( m - 1 ) ) ] )

/-
If there is an injective map from $S$ to pairs of multiples in disjoint sets $V_-$ and $V_+$, then the total number of multiples is at least $\lceil 2\sqrt{|S|} \rceil$.
-/
lemma bipartite_growth_general {α : Type*} [DecidableEq α]
    (S : Finset ℕ) (V_minus V_plus : Finset ℤ)
    (h_disjoint : Disjoint V_minus V_plus)
    (f : ℕ → ℤ × ℤ)
    (h_map : ∀ a ∈ S, let (u, v) := f a; u ∈ V_minus ∧ v ∈ V_plus ∧ (a : ℤ) ∣ u ∧ (a : ℤ) ∣ v)
    (h_inj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b) :
    let V := V_minus ∪ V_plus
    let R := fun (a : ℕ) (b : ℤ) => (a : ℤ) ∣ b
    (S.biUnion (fun a => V.filter (R a))).card ≥ Nat.ceil (2 * Real.sqrt (S.card : ℝ)) := by
      -- Let $\Gamma_-(S) = \bigcup_{a \in S} \{b \in V_- : a \mid b\}$ and $\Gamma_+(S) = \bigcup_{a \in S} \{b \in V_+ : a \mid b\}$.
      set Gamma_minus := S.biUnion (fun a => V_minus.filter (fun b => (a : ℤ) ∣ b))
      set Gamma_plus := S.biUnion (fun a => V_plus.filter (fun b => (a : ℤ) ∣ b));
      -- Since $f$ is injective, $|S| \leq |\Gamma_-(S)| \cdot |\Gamma_+(S)|$.
      have h_card_prod : (S.card : ℝ) ≤ (Gamma_minus.card : ℝ) * (Gamma_plus.card : ℝ) := by
        norm_cast;
        have h_card : S.card ≤ (Gamma_minus ×ˢ Gamma_plus).card := by
          have h_card : Finset.card (Finset.image f S) ≤ Finset.card (Gamma_minus ×ˢ Gamma_plus) := by
            refine Finset.card_le_card ?_;
            grind +ring;
          rwa [ Finset.card_image_of_injOn h_inj ] at h_card;
        rwa [ Finset.card_product ] at h_card;
      -- Since $V_-$ and $V_+$ are disjoint, the union is disjoint, so the size is $x+y$.
      have h_card_union : (S.biUnion (fun a => (V_minus ∪ V_plus).filter (fun b => (a : ℤ) ∣ b))).card = Gamma_minus.card + Gamma_plus.card := by
        rw [ ← Finset.card_union_of_disjoint ];
        · congr with x ; aesop;
        · exact Finset.disjoint_left.mpr fun x hx_minus hx_plus => Finset.disjoint_left.mp h_disjoint ( Finset.mem_biUnion.mp hx_minus |> Classical.choose_spec |> And.right |> Finset.mem_filter.mp |> And.left ) ( Finset.mem_biUnion.mp hx_plus |> Classical.choose_spec |> And.right |> Finset.mem_filter.mp |> And.left );
      simp +zetaDelta at *;
      nlinarith [ sq_nonneg ( Gamma_minus.card - Gamma_plus.card : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg S.card ), show ( Gamma_minus.card : ℝ ) + Gamma_plus.card = ( S.biUnion fun a => { b ∈ V_minus ∪ V_plus | ( a : ℤ ) ∣ b } ).card from mod_cast h_card_union.symm ]

/-
The better pair function maps $a$ to a pair of multiples in $B_- \times B_+$.
-/
def better_pair_func (N : ℕ) (k : ℤ) (a : ℕ) : ℤ × ℤ :=
  let x_int := k * (N : ℤ)
  if (x_int + N) % a = 0 then
    if 2 * a < N ∧ (x_int + N) % (2 * a) ≠ 0 then
      (x_int + N - 2 * a, x_int + N + 2 * a)
    else
      (x_int + N - a, x_int + N + a)
  else
    let u := (x_int + N) / a * a
    (u, u + a)

lemma better_pair_in_parts (N : ℕ) (k : ℤ) (a : ℕ)
    (ha_pos : a > 0)
    (ha_lt_N : a < N) :
    let (u, v) := better_pair_func N k a
    let x_int := k * (N : ℤ)
    let B_minus := Finset.Ico (x_int + 1) (x_int + N)
    let B_plus := Finset.Ico (x_int + N + 1) (x_int + 2 * N)
    u ∈ B_minus ∧ v ∈ B_plus ∧ (a : ℤ) ∣ u ∧ (a : ℤ) ∣ v := by
      unfold better_pair_func; by_cases h : ( k * N + N ) % a = 0 <;> simp +decide [ h ] ;
      · split_ifs <;> simp_all +decide [ dvd_add_right, dvd_sub_right ];
        · exact ⟨ by linarith, by linarith, by linarith ⟩;
        · exact ⟨ by linarith, ha_pos, by linarith ⟩;
      · constructor;
        · constructor <;> cases lt_or_gt_of_ne h <;> nlinarith [ Int.mul_ediv_add_emod ( k * N + N ) a, Int.emod_nonneg ( k * N + N ) ( by positivity : ( a : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( k * N + N ) ( by positivity : ( a : ℤ ) > 0 ) ];
        · constructor <;> nlinarith [ Int.mul_ediv_add_emod ( k * N + N ) a, Int.emod_nonneg ( k * N + N ) ( by positivity : ( a : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( k * N + N ) ( by positivity : ( a : ℤ ) > 0 ) ]

/-
The better pair function is injective on $S$.
-/
lemma better_pair_injectivity (N : ℕ) (k : ℤ) (S : Finset ℕ)
    (hS_sub : S ⊆ Finset.Icc 1 (N - 1))
    (hS_pos : ∀ a ∈ S, a > 0) :
    ∀ a b, a ∈ S → b ∈ S → better_pair_func N k a = better_pair_func N k b → a = b := by
      intro a b ha hb hab
      unfold better_pair_func at hab
      by_contra h_contra
      generalize_proofs at *; (
      by_cases ha' : ( k * N + N ) % a = 0 <;> by_cases hb' : ( k * N + N ) % b = 0 <;> simp +decide [ ha', hb' ] at hab ⊢ <;> try omega;
      · split_ifs at hab <;> simp_all +decide ;
      · split_ifs at hab <;> simp_all +decide ; (
        -- From the equations $k * N + N - 2 * a = (k * N + N) / b * b$ and $k * N + N + 2 * a = (k * N + N) / b * b + b$, we can derive that $b = 4 * a$.
        have hb_eq_4a : b = 4 * a := by
          linarith [ hS_pos a ha, hS_pos b hb ] ;
        generalize_proofs at *; (
        simp_all +decide ;
        exact ‹2 * a < N ∧ ¬2 * ( a : ℤ ) ∣ k * N + N›.2 ( by exact ⟨ ( k * N + N ) / ( 4 * a ) * 2 + 1, by linarith ⟩ ) ;));
        -- From the equations $k * N + N - a = (k * N + N) / b * b$ and $k * N + N + a = (k * N + N) / b * b + b$, we can derive that $b = 2a$.
        have hb_eq_2a : b = 2 * a := by
          linarith [ hS_pos a ha, hS_pos b hb ]
        generalize_proofs at *; (
        simp_all +decide [ Finset.subset_iff ];
        exact absurd ( hS_sub hb ) ( by omega ) ;);
      · split_ifs at hab <;> simp_all +decide ;
        · -- From the equations, we can derive that $a = 4b$.
          have h_eq : a = 4 * b := by
            grind
          generalize_proofs at *; (
          -- Since $b \mid k * N + N$ and $4b \nmid k * N + N$, it follows that $2b \mid k * N + N$.
          have h_div : (2 * b : ℤ) ∣ k * N + N := by
            exact ⟨ ( k * N + N ) / ( 4 * b ) * 2 + 1, by push_cast [ h_eq ] at *; linarith ⟩ ;
          generalize_proofs at *; (
          aesop));
        · -- From the equations, we can derive that $a = 2b$.
          have h_eq : a = 2 * b := by
            grind +ring
          generalize_proofs at *; (
          simp_all +decide [ Finset.subset_iff ];
          exact absurd ( hS_sub ha ) ( by omega )))

/-
The divisibility graph growth condition holds in Case 2.
-/
lemma divisibility_graph_growth_case2 (m : ℕ) (hm : m ≥ 4)
    (A : Finset ℕ) (N : ℕ) (hA_card : A.card = m) (hA_pos : ∀ a ∈ A, a > 0)
    (hN : N = A.max' (by exact Finset.card_pos.mp (by linarith)))
    (x : ℝ) (hx_int_N : ∃ k : ℤ, x = k * N) :
    let I := Set.Ioo x (x + 2 * N)
    let b0 : ℤ := Int.floor (x + N)
    let A0 : Finset ℕ := A.erase N
    let V_all : Finset ℤ := Finset.Ico (Int.floor x + 1) (Int.ceil (x + 2 * N))
    let V_in_I : Finset ℤ := V_all.filter (fun n => (n : ℝ) ∈ I)
    let V0 : Finset ℤ := V_in_I.erase b0
    let R := fun (a : ℕ) (b : ℤ) => (a : ℤ) ∣ b
    ∀ S ⊆ A0, S.Nonempty → (S.biUnion (fun a => V0.filter (R a))).card ≥ Nat.ceil (2 * Real.sqrt (S.card : ℝ)) := by
      obtain ⟨ k, hk ⟩ := hx_int_N;
      -- Apply the bipartite_growth_general lemma to the better_pair_func.
      have h_bipartite_growth : ∀ S ⊆ A.erase N, S.Nonempty → (S.biUnion (fun a => (Finset.Ico (k * N + 1) (k * N + N) ∪ Finset.Ico (k * N + N + 1) (k * N + 2 * N)).filter (fun n => (a : ℤ) ∣ n))).card ≥ Nat.ceil (2 * Real.sqrt (S.card : ℝ)) := by
        intros S hS_sub hS_nonempty
        have h_bipartite_growth : ∃ f : ℕ → ℤ × ℤ,
          (∀ a ∈ S, let (u, v) := f a; u ∈ Finset.Ico (k * N + 1) (k * N + N) ∧ v ∈ Finset.Ico (k * N + N + 1) (k * N + 2 * N) ∧ (a : ℤ) ∣ u ∧ (a : ℤ) ∣ v) ∧
          (∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b) := by
            refine' ⟨ better_pair_func N k, _, _ ⟩;
            · intro a ha
              apply better_pair_in_parts N k a (hA_pos a (Finset.mem_of_mem_erase (hS_sub ha))) (by
              exact lt_of_le_of_ne ( hN.symm ▸ Finset.le_max' _ _ ( hS_sub ha |> Finset.mem_of_mem_erase ) ) fun h => by have := hS_sub ha; aesop;);
            · intros a ha b hb hab;
              apply better_pair_injectivity N k S (fun x hx => by
                exact Finset.mem_Icc.mpr ⟨ hA_pos x ( Finset.mem_of_mem_erase ( hS_sub hx ) ), Nat.le_sub_one_of_lt ( lt_of_le_of_ne ( hN.symm ▸ Finset.le_max' _ _ ( Finset.mem_of_mem_erase ( hS_sub hx ) ) ) ( by intro t; have := hS_sub hx; aesop ) ) ⟩) (fun x hx => by
                exact hA_pos x ( Finset.mem_of_mem_erase ( hS_sub hx ) )) a b ha hb hab;
        obtain ⟨ f, hf1, hf2 ⟩ := h_bipartite_growth;
        convert bipartite_growth_general S ( Finset.Ico ( k * N + 1 ) ( k * N + N ) ) ( Finset.Ico ( k * N + N + 1 ) ( k * N + 2 * N ) ) _ f _ _ using 1;
        exact ℕ;
        · infer_instance;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Ico.mp hx₁, Finset.mem_Ico.mp hx₂ ] ;
        · exact hf1;
        · assumption;
      convert h_bipartite_growth using 6;
      ext; simp [hk];
      intro h; norm_cast; norm_num [ Int.floor_eq_iff, Int.ceil_eq_iff ] ;
      rw [ show ⌊ ( k : ℝ ) * N⌋ = k * N by exact_mod_cast Int.floor_intCast _, show ⌈ ( k : ℝ ) * N + 2 * N⌉ = k * N + 2 * N by exact_mod_cast Int.ceil_intCast _ ] ; omega;

/-
If $m=4$ and $x$ is a multiple of $N$, there exists a matching of size 4.
-/
lemma erdos_650_lower_bound_case2_m4 (A : Finset ℕ) (N : ℕ)
    (hA_card : A.card = 4) (hA_pos : ∀ a ∈ A, a > 0)
    (hN : N = A.max' (by exact Finset.card_pos.mp (by linarith)))
    (x : ℝ) (hx_int_N : ∃ k : ℤ, x = k * N) :
    let I := Set.Ioo x (x + 2 * N)
    ∃ (M : Finset (ℕ × ℤ)),
      (∀ p ∈ M, p.1 ∈ A ∧ (p.2 : ℝ) ∈ I ∧ (p.1 : ℤ) ∣ p.2) ∧
      (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      M.card ≥ 4 := by
        obtain ⟨ k, hk ⟩ := hx_int_N
        generalize_proofs at *;
        -- Let $b_0 = x+N$.
        set b0 : ℤ := k * N + N;
        -- Let $A_0 = A \setminus \{N\}$. $|A_0| = 3$.
        set A0 : Finset ℕ := A.erase N;
        -- Let $V_0 = (I \cap \mathbb{Z}) \setminus \{b_0\}$.
        set V0 : Finset ℤ := (Finset.Ico (Int.floor x + 1) (Int.ceil (x + 2 * N))).filter (fun n => (n : ℝ) ∈ Set.Ioo x (x + 2 * N)) \ {b0};
        -- By `divisibility_graph_growth_case2`, for any $S \subseteq A0$, $|\Gamma_0(S)| \ge \lceil 2\sqrt{|S|} \rceil$.
        have h_div_growth : ∀ S ⊆ A0, S.Nonempty → (S.biUnion (fun a => V0.filter (fun v => (a : ℤ) ∣ v))).card ≥ Nat.ceil (2 * Real.sqrt S.card) := by
          convert divisibility_graph_growth_case2 4 ( by norm_num ) A N hA_card hA_pos hN x ⟨ k, hk ⟩ using 1;
          simp +zetaDelta at *;
          congr! 3;
          congr! 3;
          ext; simp [Finset.mem_erase, Finset.mem_sdiff];
          intro h; rw [ hk ] ; norm_num [ show ⌊ ( k : ℝ ) * N⌋ = k * N from Int.floor_eq_iff.mpr ⟨ by norm_num, by norm_num ⟩ ] ; aesop;
        -- By Hall's theorem, there exists a matching $M_0$ of size 3 in $A_0 \times V_0$.
        obtain ⟨M0, hM0⟩ : ∃ M0 : Finset (ℕ × ℤ), (∀ p ∈ M0, p.1 ∈ A0 ∧ p.2 ∈ V0 ∧ (p.1 : ℤ) ∣ p.2) ∧ (∀ p q, p ∈ M0 → q ∈ M0 → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧ M0.card = 3 := by
          have h_hall : ∀ S ⊆ A0, S.Nonempty → (S.biUnion (fun a => V0.filter (fun v => (a : ℤ) ∣ v))).card ≥ S.card := by
            intro S hS_sub hS_nonempty
            specialize h_div_growth S hS_sub hS_nonempty
            have h_card_ge : Nat.ceil (2 * Real.sqrt S.card) ≥ S.card := by
              have h_card_le : S.card ≤ 3 := by
                exact le_trans ( Finset.card_le_card hS_sub ) ( by rw [ Finset.card_erase_of_mem ( hN.symm ▸ Finset.max'_mem _ _ ) ] ; norm_num [ hA_card ] );
              interval_cases _ : S.card <;> norm_num;
              · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) );
              · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; nlinarith only [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] ) )
            exact le_trans h_card_ge h_div_growth;
          have h_hall : ∃ f : ℕ → ℤ, (∀ a ∈ A0, (a : ℤ) ∣ f a) ∧ (∀ a b, a ∈ A0 → b ∈ A0 → a ≠ b → f a ≠ f b) ∧ (∀ a ∈ A0, f a ∈ V0) := by
            have h_hall : ∀ (G : A0 → Finset ℤ), (∀ a, G a ⊆ V0) → (∀ S : Finset A0, S.Nonempty → (S.biUnion (fun a => G a)).card ≥ S.card) → ∃ f : A0 → ℤ, (∀ a, f a ∈ G a) ∧ (∀ a b, a ≠ b → f a ≠ f b) := by
              intros G hG_sub hG_growth
              have h_hall : ∃ f : A0 → ℤ, (∀ a, f a ∈ G a) ∧ (∀ a b, a ≠ b → f a ≠ f b) := by
                have h_hall : ∀ S : Finset A0, S.Nonempty → (S.biUnion (fun a => G a)).card ≥ S.card := hG_growth
                have := Finset.all_card_le_biUnion_card_iff_exists_injective G; simp_all +decide ;
                exact this.mp ( fun s => if hs : s.Nonempty then h_hall s hs else by aesop ) |> fun ⟨ f, hf₁, hf₂ ⟩ => ⟨ f, hf₂, fun a ha b hb hab => hf₁.ne <| by simpa [ Subtype.ext_iff ] using hab ⟩ ;
              exact h_hall;
            specialize h_hall (fun a => V0.filter (fun v => (a.val : ℤ) ∣ v)) (by
            exact fun a => Finset.filter_subset _ _) (by
            intro S hS_nonempty
            specialize ‹∀ S ⊆ A0, S.Nonempty → (S.biUnion fun a => {v ∈ V0 | ↑a ∣ v}).card ≥ S.card› (S.image Subtype.val) (by
            exact Finset.image_subset_iff.mpr fun x hx => x.2) (by
            exact ⟨ _, Finset.mem_image_of_mem _ hS_nonempty.choose_spec ⟩);
            convert h_hall using 1;
            · congr! 1;
              ext; simp [Finset.mem_biUnion, Finset.mem_image];
            · rw [ Finset.card_image_of_injective _ Subtype.coe_injective ]);
            obtain ⟨ f, hf1, hf2 ⟩ := h_hall; use fun a => if ha : a ∈ A0 then f ⟨ a, ha ⟩ else 0; simp_all +decide [ Finset.subset_iff ] ;
          obtain ⟨ f, hf1, hf2, hf3 ⟩ := h_hall; use Finset.image ( fun a => ( a, f a ) ) A0; simp_all +decide [ Finset.card_image_of_injOn ] ;
          constructor;
          · bound;
          · rw [ Finset.card_erase_of_mem ( hN.symm ▸ Finset.max'_mem _ _ ), hA_card ];
        refine' ⟨ Insert.insert ( N, b0 ) M0, _, _, _ ⟩ <;> norm_num at *;
        · refine' ⟨ ⟨ _, _, _ ⟩, _ ⟩;
          · exact hN.symm ▸ Finset.max'_mem _ _;
          · simp +zetaDelta at *;
            constructor <;> linarith [ show ( N : ℝ ) > 0 from Nat.cast_pos.mpr ( hA_pos _ ( hN.symm ▸ Finset.max'_mem _ _ ) ) ];
          · exact ⟨ k + 1, by ring ⟩;
          · intro a b hab; specialize hM0; have := hM0.1 a b hab; aesop;
        · grind +ring;
        · grind +ring

/-
If $m \ge 5$ and $x$ is a multiple of $N$, there exists a matching of size at least $\lceil 2\sqrt{m} \rceil$.
-/
lemma erdos_650_lower_bound_case2_ge5 (m : ℕ) (hm : m ≥ 5)
    (A : Finset ℕ) (N : ℕ) (hA_card : A.card = m) (hA_pos : ∀ a ∈ A, a > 0)
    (hN : N = A.max' (by exact Finset.card_pos.mp (by linarith)))
    (x : ℝ) (hx_int_N : ∃ k : ℤ, x = k * N) :
    let I := Set.Ioo x (x + 2 * N)
    ∃ (M : Finset (ℕ × ℤ)),
      (∀ p ∈ M, p.1 ∈ A ∧ (p.2 : ℝ) ∈ I ∧ (p.1 : ℤ) ∣ p.2) ∧
      (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      M.card ≥ Nat.ceil (2 * Real.sqrt m) := by
        obtain ⟨k, hk⟩ : ∃ k : ℤ, x = k * N := hx_int_N
        set A0 := A.erase N
        set N0 := A0.max' (by
        exact Finset.card_pos.mp ( by rw [ Finset.card_erase_of_mem ( hN.symm ▸ Finset.max'_mem _ _ ), hA_card ] ; omega ))
        generalize_proofs at *;
        -- Let $b_0 = x + N$.
        set b0 := k * N + N;
        -- By Lemma `divisibility_graph_growth_case2`, for any $S \subseteq A0$, $|\Gamma_0(S)| \ge \lceil 2\sqrt{|S|} \rceil$.
        have h_growth : ∀ S ⊆ A0, S.Nonempty → (S.biUnion (fun a => (Finset.Ico (Int.floor x + 1) (Int.ceil (x + 2 * N))).filter (fun n => (n : ℝ) ∈ Set.Ioo x (x + 2 * N) ∧ (a : ℤ) ∣ n) |> Finset.filter (fun n => n ≠ b0))).card ≥ Nat.ceil (2 * Real.sqrt (S.card : ℝ)) := by
          convert divisibility_graph_growth_case2 m ( by linarith ) A N hA_card hA_pos hN x ⟨ k, hk ⟩ using 1;
          simp +zetaDelta at *;
          congr! 7;
          ext; simp [hk];
          norm_num [ show ⌊ ( k : ℝ ) * N⌋ = k * N by exact_mod_cast Int.floor_intCast _, show ⌈ ( k : ℝ ) * N + 2 * N⌉ = k * N + 2 * N by exact_mod_cast Int.ceil_intCast _ ] ; ring_nf;
          tauto;
        -- By Lemma `matching_size_general`, there exists a matching $M_0$ in $A_0 \times V_0$ of size $\ge \lceil 2\sqrt{m-1} \rceil$.
        obtain ⟨M0, hM0⟩ : ∃ M0 : Finset (ℕ × ℤ),
          (∀ p ∈ M0, p.1 ∈ A0 ∧ (p.2 : ℝ) ∈ Set.Ioo x (x + 2 * N) ∧ (p.1 : ℤ) ∣ p.2 ∧ p.2 ≠ b0) ∧
          (∀ p q, p ∈ M0 → q ∈ M0 → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
          M0.card ≥ Nat.ceil (2 * Real.sqrt (A0.card : ℝ)) := by
            convert matching_size_general A0 ( Finset.filter ( fun n : ℤ => ( n : ℝ ) ∈ Set.Ioo x ( x + 2 * N ) ∧ ( n : ℤ ) ≠ b0 ) ( Finset.Ico ( Int.floor x + 1 ) ( Int.ceil ( x + 2 * N ) ) ) ) ( fun a b => ( a : ℤ ) ∣ b ) _ _ using 1;
            · ext; simp [Finset.mem_filter, Finset.mem_Ico];
              intro h1 h2; constructor <;> intro h3 a b hab <;> specialize h3 a b hab <;> simp_all +decide [Int.lt_ceil] ;
              exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( ( k : ℝ ) * A.max' ‹_› ), Int.lt_floor_add_one ( ( k : ℝ ) * A.max' ‹_› ) ] );
            · rw [ Finset.card_erase_of_mem ( hN ▸ Finset.max'_mem _ _ ) ] ; omega;
            · convert h_growth using 6 ; aesop;
        refine' ⟨ Insert.insert ( N, b0 ) M0, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
        · simp +zetaDelta at *;
          refine' ⟨ ⟨ Finset.max'_mem _ _, _, _ ⟩, _ ⟩ <;> norm_cast at * <;> simp_all +decide [ two_mul ];
          · exact hA_pos _ ( Finset.max'_mem _ _ );
          · exact fun a b hab => ⟨ hM0.1 a b hab |>.1.2, hM0.1 a b hab |>.2.1 ⟩;
        · grind;
        · rw [ Finset.card_insert_of_notMem ];
          · rw [ show A0.card = m - 1 from ?_ ] at hM0;
            · have := ceil_sqrt_inequality m ( by linarith );
              rcases m with ( _ | _ | m ) <;> norm_num at *;
              exact this.trans ( add_le_add_right ( Nat.cast_le.mpr <| Nat.ceil_le.mpr <| by linarith ) _ );
            · rw [ Finset.card_erase_of_mem ( hN.symm ▸ Finset.max'_mem _ _ ), hA_card ];
          · grind +ring

/-
Case 2 of the lower bound: if x is a multiple of N, we have a matching of size at least ceil(2*sqrt(m)).
-/
lemma erdos_650_lower_bound_case2_proven (m : ℕ) (hm : m ≥ 4)
    (A : Finset ℕ) (N : ℕ) (hA_card : A.card = m) (hA_pos : ∀ a ∈ A, a > 0)
    (hN : N = A.max' (by exact Finset.card_pos.mp (by linarith)))
    (x : ℝ) (hx_int_N : ∃ k : ℤ, x = k * N) :
    let I := Set.Ioo x (x + 2 * N)
    ∃ (M : Finset (ℕ × ℤ)),
      (∀ p ∈ M, p.1 ∈ A ∧ (p.2 : ℝ) ∈ I ∧ (p.1 : ℤ) ∣ p.2) ∧
      (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      M.card ≥ Nat.ceil (2 * Real.sqrt m) := by
  by_cases hm4 : m = 4
  · obtain ⟨M, hM⟩ := erdos_650_lower_bound_case2_m4 A N (by rwa [hm4] at hA_card) hA_pos hN x hx_int_N
    refine ⟨M, hM.1, hM.2.1, ?_⟩
    rw [hm4]
    norm_num
    exact hM.2.2
  · have hm_ge_5 : m ≥ 5 := by
      omega
    exact erdos_650_lower_bound_case2_ge5 m hm_ge_5 A N hA_card hA_pos hN x hx_int_N

/-
For any $m \ge 4$, any set $A$ of size $m$, and any $x$, the interval $I=(x, x+2a_m)$ contains a matching of size at least $\lceil 2\sqrt m \rceil$.
-/
theorem erdos_650_lower_bound (m : ℕ) (hm : m ≥ 4)
    (A : Finset ℕ) (N : ℕ) (hA_card : A.card = m) (hA_pos : ∀ a ∈ A, a > 0)
    (hN : N = A.max' (by exact Finset.card_pos.mp (by linarith)))
    (x : ℝ) :
    let I := Set.Ioo x (x + 2 * N)
    ∃ (M : Finset (ℕ × ℤ)),
      (∀ p ∈ M, p.1 ∈ A ∧ (p.2 : ℝ) ∈ I ∧ (p.1 : ℤ) ∣ p.2) ∧
      (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      M.card ≥ Nat.ceil (2 * Real.sqrt m) := by
        by_cases hx_int_N : ∃ k : ℤ, x = k * N;
        · exact
          let I := Set.Ioo x (x + 2 * ↑N);
          erdos_650_lower_bound_case2_proven m hm A N hA_card hA_pos hN x hx_int_N;
        · convert erdos_650_lower_bound_case1 m hm A N hA_card hA_pos hN x _ using 1;
          exact fun k hk => hx_int_N ⟨ k, hk ⟩

/-
If every matching has size at most k, then the maximum matching size is at most k.
-/
lemma max_matching_size_le (A : Finset ℕ) (I : Set ℝ) (k : ℕ) :
    (∀ M, is_matching A I M → M.card ≤ k) → max_matching_size A I ≤ k := by
      intro h; exact csSup_le' fun x hx => by obtain ⟨ M, hM₁, rfl ⟩ := hx; exact h M hM₁;

/-
For any $m \ge 4$, if $n = \lceil 2\sqrt{m} \rceil$, there exist $s, t$ such that $s+t=n$ and $st \ge m$.
-/
lemma exists_st_decomposition (m : ℕ) :
    let n := Nat.ceil (2 * Real.sqrt m)
    ∃ s t : ℕ, s + t = n ∧ s * t ≥ m := by
      use ⌈2 * Real.sqrt m⌉₊ / 2, ⌈2 * Real.sqrt m⌉₊ - ⌈2 * Real.sqrt m⌉₊ / 2, by
        rw [ Nat.add_sub_of_le ( Nat.div_le_self _ _ ) ], by
        -- By definition of $n$, we know that $n^2 \geq 4m$.
        have hn_sq_ge_4m : (Nat.ceil (2 * Real.sqrt m))^2 ≥ 4 * m := by
          exact_mod_cast ( by nlinarith [ Nat.le_ceil ( 2 * Real.sqrt m ), Real.sqrt_nonneg m, Real.sq_sqrt ( Nat.cast_nonneg m ) ] : ( 4 : ℝ ) * m ≤ ⌈2 * Real.sqrt m⌉₊ ^ 2 );
        nlinarith [ Nat.sub_add_cancel ( show ⌈2 * Real.sqrt m⌉₊ / 2 ≤ ⌈2 * Real.sqrt m⌉₊ from Nat.div_le_self _ _ ), Nat.div_mul_le_self ( ⌈2 * Real.sqrt m⌉₊ ) 2, Nat.div_add_mod ( ⌈2 * Real.sqrt m⌉₊ ) 2, Nat.mod_lt ( ⌈2 * Real.sqrt m⌉₊ ) two_pos ] ;;

/-
There exists a configuration of size m where the maximum matching size is at most ceil(2*sqrt(m)).
-/
lemma erdos_650_upper_bound_tight (m : ℕ) (hm : m ≥ 4) :
    ∃ (A : Finset ℕ) (x : ℝ),
      A.card = m ∧
      (∀ a ∈ A, a > 0) ∧
      ∃ (hA : A.Nonempty),
      let N := A.max' hA
      let I := Set.Ioo x (x + 2 * N)
      max_matching_size A I ≤ Nat.ceil (2 * Real.sqrt m) := by
        -- By `exists_st_decomposition`, there exist $s, t$ such that $s+t=n$ and $st \geq m$.
        obtain ⟨s, t, hs_t⟩ : ∃ s t : ℕ, s + t = Nat.ceil (2 * Real.sqrt m) ∧ s * t ≥ m := by
          exact exists_st_decomposition m;
        -- By `erdos_650_upper_bound_st`, there exists a set $A_{st}$ of size $st$ and an interval $I_{st} = (x_{st}, x_{st}+2N_{st}]$ (in $\mathbb{N}$) such that every matching in $A_{st} \times I_{st}$ has size $\le s+t = n$.
        obtain ⟨N, A_st, I_st, hA_st_card, hA_st_pos, hI_st⟩ : ∃ N : ℕ, ∃ A_st : Finset ℕ, ∃ I_st : Set ℕ,
          A_st.card = s * t ∧ (∀ a ∈ A_st, 1 ≤ a ∧ a ≤ N) ∧
          (∃ x y : ℕ, I_st = Set.Ioc x y ∧ y - x = 2 * N) ∧
          (∀ M : Finset (ℕ × ℕ),
            (∀ p ∈ M, p.1 ∈ A_st ∧ p.2 ∈ I_st ∧ p.1 ∣ p.2) →
            (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) →
            M.card ≤ s + t) := by
              have := erdos_650_upper_bound_st s t; (
              exact this ( by nlinarith ) ( by nlinarith ) |> fun ⟨ N, A, I, hA_card, hA_pos, hI, hM ⟩ => ⟨ N, A, I, hA_card, hA_pos, hI, hM ⟩ ;);
        obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A ⊆ A_st ∧ A.card = m ∧ (∀ a ∈ A, 1 ≤ a) := by
          exact Exists.elim ( Finset.exists_subset_card_eq ( by linarith ) ) fun A hA => ⟨ A, hA.1, hA.2, fun a ha => hA_st_pos a ( hA.1 ha ) |>.1 ⟩;
        obtain ⟨x, y, hI_st_eq, hI_st_len⟩ : ∃ x y : ℕ, I_st = Set.Ioc x y ∧ y - x = 2 * N := hI_st.left
        use A, x
        simp [hA];
        refine' ⟨ fun a ha => hA.2.2 a ha, _, _ ⟩
        all_goals generalize_proofs at *;
        · exact Finset.card_pos.mp ( by linarith );
        · refine' max_matching_size_le _ _ _ _;
          intro M hM
          obtain ⟨hM_subset, hM_card⟩ := hM
          have hM_subset_I_st : ∀ p ∈ M, p.2 ∈ Set.Ioc (x : ℤ) (x + 2 * N) := by
            intro p hp
            obtain ⟨hpA, hpI, hp_div⟩ := hM_subset p hp
            have hpI_subset : (p.2 : ℝ) ∈ Set.Ioo (x : ℝ) (x + 2 * N) := by
              exact ⟨ hpI.1, hpI.2.trans_le <| by norm_cast; linarith [ hA_st_pos _ <| hA.1 <| Finset.max'_mem A ‹_› ] ⟩
            generalize_proofs at *;
            exact ⟨ mod_cast hpI_subset.1, mod_cast hpI_subset.2.le ⟩
          generalize_proofs at *;
          have hM_subset_I_st : ∃ M' : Finset (ℕ × ℕ), M'.card = M.card ∧ (∀ p ∈ M', p.1 ∈ A_st ∧ p.2 ∈ I_st ∧ p.1 ∣ p.2) ∧ (∀ p q, p ∈ M' → q ∈ M' → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) := by
            use M.image (fun p => (p.1, Int.toNat p.2));
            rw [ Finset.card_image_of_injOn ] <;> norm_num [ Function.Injective ];
            · constructor <;> intros <;> subst_vars <;> norm_num at *;
              · rename_i a b hab
                generalize_proofs at *; (
                have := hM_subset _ _ hab; specialize hM_subset_I_st _ _ hab; norm_cast at *; simp_all +decide ;
                exact ⟨ hA.1 this.1, by linarith [ Nat.sub_add_cancel ( show x ≤ y from le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith ) ) ) ], by simpa [ ← Int.natCast_dvd_natCast, Int.toNat_of_nonneg ( by linarith : 0 ≤ b ) ] using hM_subset _ _ hab |>.2.2 ⟩ ;);
              · grind +ring;
            · intro p hp q hq; specialize hM_card p q hp hq; aesop;
          generalize_proofs at *; (
          exact hM_subset_I_st.choose_spec.1 ▸ hI_st.2 _ hM_subset_I_st.choose_spec.2.1 hM_subset_I_st.choose_spec.2.2 |> le_trans <| by linarith;)

/-
The function f(m) is equal to ceil(2*sqrt(m)) for all m ≥ 4.
-/
theorem erdos_650_mge4 (m : ℕ) (hm : m ≥ 4) : f m = Nat.ceil (2 * Real.sqrt m) := by
  refine' le_antisymm _ _;
  · -- By definition of $f$, we know that for any $k$ such that $Property m k$ holds, $k \leq \lceil 2 \sqrt{m} \rceil$.
    have h_upper_bound : ∀ k, Property m k → k ≤ Nat.ceil (2 * Real.sqrt m) := by
      intro k hk
      obtain ⟨A, x, hA_card, hA_pos, hA_nonempty, h_max_matching⟩ := erdos_650_upper_bound_tight m hm
      have h_k_le : k ≤ max_matching_size A (Set.Ioo x (x + 2 * (A.max' hA_nonempty))) := by
        exact hk A x hA_card hA_pos hA_nonempty
      have h_max_le : max_matching_size A (Set.Ioo x (x + 2 * (A.max' hA_nonempty))) ≤ Nat.ceil (2 * Real.sqrt m) := by
        exact h_max_matching
      linarith [h_k_le, h_max_le];
    exact csSup_le' h_upper_bound;
  · refine' le_csSup _ _;
    · use Nat.ceil ( 2 * Real.sqrt m );
      intro k hk;
      obtain ⟨ A, x, hA_card, hA_pos, hA_nonempty, hmax ⟩ := erdos_650_upper_bound_tight m hm;
      exact le_trans ( hk A x hA_card hA_pos hA_nonempty ) hmax;
    · intro A x hA hA_pos hA_nonempty;
      apply_rules [ le_csSup ];
      · exact ⟨ _, fun k hk => by rcases hk with ⟨ M, hM₁, rfl ⟩ ; exact Finset.card_le_card ( show M ⊆ A ×ˢ ( Finset.Ico ( ⌊x⌋ + 1 ) ( ⌈x + 2 * ↑ ( A.max' hA_nonempty ) ⌉ ) ) from fun p hp => Finset.mem_product.mpr ⟨ hM₁.1 p hp |>.1, Finset.mem_Ico.mpr ⟨ by exact Int.floor_lt.mpr ( by linarith [ hM₁.1 p hp |>.2.1.1 ] ), by exact Int.lt_ceil.mpr ( by linarith [ hM₁.1 p hp |>.2.1.2 ] ) ⟩ ⟩ ) ⟩;
      · convert erdos_650_lower_bound m hm A ( A.max' hA_nonempty ) hA hA_pos ( rfl ) x using 1;
        constructor <;> intro hM
        all_goals generalize_proofs at *;
        · exact ⟨ hM.choose, hM.choose_spec.1.1, hM.choose_spec.1.2, hM.choose_spec.2.ge ⟩;
        · obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := hM;
          obtain ⟨ M', hM' ⟩ := Finset.exists_subset_card_eq hM₃;
          exact ⟨ M', ⟨ fun p hp => hM₁ p ( hM'.1 hp ), fun p q hp hq hpq => hM₂ p q ( hM'.1 hp ) ( hM'.1 hq ) hpq ⟩, hM'.2 ⟩

/-
If an interval has length $L > nk$, then it contains at least $n$ multiples of $k$.
-/
lemma count_multiples (k : ℕ) (x L : ℝ) (hk : k > 0) (n : ℕ) (hL : L > n * k) :
    ∃ S : Finset ℤ, S.card = n ∧ ∀ m ∈ S, (k : ℤ) ∣ m ∧ x < m ∧ m < x + L := by
  -- Let $q = \lfloor x/k \rfloor + 1$.
  set q := Int.floor (x / k) + 1 with hq_def
  use Finset.image (fun i : ℕ => q * k + i * k) (Finset.range n);
  rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, hk.ne' ];
  intro a ha; constructor <;> push_cast [ hq_def ] <;> nlinarith [ Int.floor_le ( x / k ), Int.lt_floor_add_one ( x / k ), show ( a : ℝ ) + 1 ≤ n by norm_cast, show ( k : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ x ( by positivity : ( k : ℝ ) ≠ 0 ) ] ;

/-
Given three sets $S_a, S_b, S_c$ with $|S_a| \ge 2, |S_b| \ge 2, |S_c| \ge 1$, we can pick distinct elements $a \in S_a, b \in S_b, c \in S_c$ unless $S_a = S_b$, $S_c \subseteq S_a$, and $|S_a| = 2$.
-/
lemma exists_distinct_representatives_of_sets {α : Type*} [DecidableEq α]
    (S_a S_b S_c : Finset α)
    (ha : S_a.card ≥ 2) (hb : S_b.card ≥ 2) (hc : S_c.card ≥ 1) :
    (∃ a ∈ S_a, ∃ b ∈ S_b, ∃ c ∈ S_c, a ≠ b ∧ a ≠ c ∧ b ≠ c) ∨
    (S_a = S_b ∧ S_c ⊆ S_a ∧ S_a.card = 2) := by
  by_cases h : S_a = S_b <;> by_cases h' : S_c ⊆ S_a <;> simp_all +decide;
  · by_cases h'' : S_b.card = 2;
    · exact Or.inr h'';
    · obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.two_lt_card.1 ( lt_of_le_of_ne hb ( Ne.symm h'' ) );
      grind +ring;
  · obtain ⟨ c, hc ⟩ := Finset.not_subset.mp h';
    obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.1 hb; use a, by aesop, b, by aesop, c; aesop;
  · obtain ⟨ c, hc ⟩ := hc;
    by_cases h'' : ∀ a ∈ S_a, a = c ∨ a ∈ S_b;
    · obtain ⟨ a, ha, b, hb, hab ⟩ : ∃ a ∈ S_a, ∃ b ∈ S_b, a ≠ b ∧ a ≠ c := by
        obtain ⟨ a, ha ⟩ := Finset.exists_mem_ne ( lt_of_lt_of_le ( by decide ) ha ) c;
        exact ⟨ a, ha.1, by obtain ⟨ b, hb ⟩ := Finset.exists_mem_ne ( lt_of_lt_of_le ( by decide ) hb ) a; use b; aesop ⟩;
      grind;
    · push_neg at h'';
      obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := h''; obtain ⟨ b, hb₁, hb₂ ⟩ := Finset.exists_mem_ne ( lt_of_lt_of_le ( by decide ) hb ) c; use a, ha₁, b, hb₁, c, hc; aesop;
  · obtain ⟨ c, hc ⟩ := hc.exists_mem; simp_all +decide [ Finset.subset_iff ] ;
    obtain ⟨ x, hx, hx' ⟩ := h';
    obtain ⟨ y, hy ⟩ := Finset.exists_mem_ne ( by linarith ) x;
    obtain ⟨ z, hz ⟩ := Finset.exists_mem_ne ( by linarith : 1 < Finset.card S_a ) y; use z, hz.1, y, hy.1, x, hx; aesop;

/-
If $3a \ge 2c$ and $a < b < c$, then $\text{lcm}(a, b) > 2c$.
-/
lemma lcm_gt_two_c (a b c : ℕ) (ha : 3 * a ≥ 2 * c) (hab : a < b) (hbc : b < c) :
    Nat.lcm a b > 2 * c := by
  -- We have $\text{lcm}(a, b) \ge \frac{ab}{b-a}$.
  have h_lcm_lower_bound : Nat.lcm a b ≥ a * b / (b - a) := by
    refine Nat.div_le_div_left ?_ ?_ <;> norm_num [ Nat.gcd_dvd_left, Nat.gcd_dvd_right ];
    · exact Nat.le_of_dvd ( Nat.sub_pos_of_lt hab ) ( Nat.dvd_sub ( Nat.gcd_dvd_right _ _ ) ( Nat.gcd_dvd_left _ _ ) );
    · exact Or.inr ( pos_of_gt hab );
  refine lt_of_lt_of_le ?_ h_lcm_lower_bound;
  rw [ Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le ];
  · nlinarith only [ Nat.sub_add_cancel hab.le, ha, hab, hbc ];
  · exact Nat.sub_pos_of_lt hab

lemma exists_matching_card_3 (A : Finset ℕ) (x : ℝ)
    (hA : A.Nonempty) (hA_pos : ∀ a ∈ A, a > 0) (h_card : A.card = 3) :
    let N := A.max' hA
    let I := Set.Ioo x (x + 2 * N)
    ∃ M, is_matching A I M ∧ M.card = 3 := by
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : ℕ, a < b ∧ b < c ∧ a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ A = {a, b, c} := by
    obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a < b ∧ b < c ∧ A = {a, b, c} := by
      obtain ⟨ a, b, c, h ⟩ := Finset.card_eq_three.mp h_card;
      cases lt_or_gt_of_ne h.1 <;> cases lt_or_gt_of_ne h.2.1 <;> cases lt_or_gt_of_ne h.2.2.1 <;> simp +decide [ * ] at *;
      all_goals simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
    exact ⟨ a, b, c, habc.1, habc.2.1, ha, hb, hc, habc.2.2 ⟩;
  -- Let $S_a, S_b, S_c$ be the sets of multiples of $a, b, c$ in $I$.
  set N := c
  set I := Set.Ioo x (x + 2 * N)
  set S_a := Finset.filter (fun m => (a : ℤ) ∣ m ∧ x < m ∧ m < x + 2 * N) (Finset.Ico (Int.floor x + 1) (Int.ceil (x + 2 * N)))
  set S_b := Finset.filter (fun m => (b : ℤ) ∣ m ∧ x < m ∧ m < x + 2 * N) (Finset.Ico (Int.floor x + 1) (Int.ceil (x + 2 * N)))
  set S_c := Finset.filter (fun m => (c : ℤ) ∣ m ∧ x < m ∧ m < x + 2 * N) (Finset.Ico (Int.floor x + 1) (Int.ceil (x + 2 * N)));
  -- By `count_multiples`, $|S_c| \ge 1$, $|S_b| \ge 2$, and $|S_a| \ge 2$.
  have hS_c : S_c.card ≥ 1 := by
    -- By `count_multiples`, $|S_c| \ge 1$.
    have hS_c : ∃ m : ℤ, (c : ℤ) ∣ m ∧ x < m ∧ m < x + 2 * N := by
      refine' ⟨ c * ⌊x / c⌋ + c, _, _, _ ⟩ <;> norm_num;
      · nlinarith [ Int.lt_floor_add_one ( x / c ), show ( c : ℝ ) > 0 by norm_cast; linarith, mul_div_cancel₀ x ( show ( c : ℝ ) ≠ 0 by norm_cast; linarith ) ];
      · nlinarith [ Int.floor_le ( x / c ), Int.lt_floor_add_one ( x / c ), show ( c : ℝ ) > 0 by norm_cast; linarith [ hA_pos _ habc.2.1 ], mul_div_cancel₀ x ( show ( c : ℝ ) ≠ 0 by norm_cast; linarith [ hA_pos _ habc.2.1 ] ) ];
    obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := hS_c; exact Finset.card_pos.mpr ⟨ m, Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le x, Int.lt_floor_add_one x ] ), by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.le_ceil ( x + 2 * c ) ] ) ⟩, hm₁, hm₂, hm₃ ⟩ ⟩ ;
  have hS_b : S_b.card ≥ 2 := by
    have hS_b : ∃ S : Finset ℤ, S.card = 2 ∧ ∀ m ∈ S, (b : ℤ) ∣ m ∧ x < m ∧ m < x + 2 * N := by
      apply count_multiples b x (2 * N) (by
      linarith [ hA_pos b habc.1 ]) 2 (by
      exact mul_lt_mul_of_pos_left ( mod_cast hb ) zero_lt_two);
    obtain ⟨ S, hS₁, hS₂ ⟩ := hS_b; refine' le_trans _ ( Finset.card_mono <| show S ⊆ S_b from _ ) ; aesop;
    exact fun m hm => Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hS₂ m hm, Int.floor_le x, Int.lt_floor_add_one x ] ), by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hS₂ m hm, Int.le_ceil ( x + 2 * N ), Int.ceil_lt_add_one ( x + 2 * N ) ] ) ⟩, hS₂ m hm ⟩
  have hS_a : S_a.card ≥ 2 := by
    have h_card_interval : ∃ S : Finset ℤ, S.card = 2 ∧ ∀ m ∈ S, (a : ℤ) ∣ m ∧ x < m ∧ m < x + 2 * (N : ℝ) := by
      apply_rules [ count_multiples ];
      exact mul_lt_mul_of_pos_left ( mod_cast by linarith ) zero_lt_two;
    obtain ⟨ S, hS₁, hS₂ ⟩ := h_card_interval; exact hS₁ ▸ Finset.card_le_card fun m hm => Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hS₂ m hm, Int.floor_le x, Int.lt_floor_add_one x ] ), by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hS₂ m hm, Int.le_ceil ( x + 2 * ( N : ℝ ) ), Int.ceil_lt_add_one ( x + 2 * ( N : ℝ ) ) ] ) ⟩, hS₂ m hm ⟩ ;
  -- By `exists_distinct_representatives_of_sets`, either we have a matching (distinct representatives), or we are in the bad case: $S_a = S_b$, $S_c \subseteq S_a$, and $|S_a| = 2$.
  by_cases h_bad_case : S_a = S_b ∧ S_c ⊆ S_a ∧ S_a.card = 2;
  · -- If $2c > 3a$, then by `count_multiples`, $|S_a| \ge 3$, contradiction.
    by_cases h_case : 2 * c > 3 * a;
    · have hS_a_card : S_a.card ≥ 3 := by
        have hS_a_card : ∃ S : Finset ℤ, S.card = 3 ∧ ∀ m ∈ S, (a : ℤ) ∣ m ∧ x < m ∧ m < x + 2 * c := by
          convert count_multiples a x ( 2 * c ) ( hA_pos a hc ) 3 _ using 1 ; norm_num [ h_case ];
          norm_cast;
        obtain ⟨ S, hS₁, hS₂ ⟩ := hS_a_card; exact hS₁ ▸ Finset.card_le_card ( fun m hm => Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hS₂ m hm, Int.floor_le x, Int.lt_floor_add_one x ] ), by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hS₂ m hm, Int.le_ceil ( x + 2 * c ), Int.ceil_lt_add_one ( x + 2 * c ) ] ) ⟩, hS₂ m hm ⟩ ) ;
      linarith;
    · -- By `lcm_gt_two_c`, $\text{lcm}(a, b) > 2c$.
      have h_lcm_gt_two_c : Nat.lcm a b > 2 * c := by
        apply lcm_gt_two_c a b c (by linarith) ha hb;
      -- Since $S_a = S_b$, any element $u \in S_a$ is a multiple of both $a$ and $b$, hence a multiple of $\text{lcm}(a, b)$.
      have h_lcm_div : ∀ u ∈ S_a, (Nat.lcm a b : ℤ) ∣ u := by
        simp +zetaDelta at *;
        intro u hu₁ hu₂ hu₃ hu₄ hu₅; have := h_bad_case.1.symm; simp_all +decide [ Finset.ext_iff ] ;
        exact Int.coe_lcm_dvd hu₃ ( this u hu₁ hu₂ hu₄ hu₅ |>.2 hu₃ );
      -- Since $|S_a| = 2$, let $S_a = \{u, v\}$ with $u \ne v$.
      obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : ℤ, u ∈ S_a ∧ v ∈ S_a ∧ u ≠ v ∧ S_a = {u, v} := by
        rw [ Finset.card_eq_two ] at h_bad_case; obtain ⟨ u, v, hu, hv ⟩ := h_bad_case.2.2; use u, v; aesop;
      -- Since $u$ and $v$ are multiples of $\text{lcm}(a, b)$, we have $|u - v| \ge \text{lcm}(a, b)$.
      have h_diff_ge_lcm : |u - v| ≥ Nat.lcm a b := by
        exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr huv.1 ) ) ( by simpa using dvd_sub ( h_lcm_div u hu ) ( h_lcm_div v hv ) );
      -- Since $u$ and $v$ are in $I$, we have $|u - v| < 2c$.
      have h_diff_lt_two_c : |u - v| < 2 * c := by
        simp +zetaDelta at *;
        exact abs_sub_lt_iff.mpr ⟨ by exact_mod_cast ( by linarith : ( u : ℝ ) - v < 2 * c ), by exact_mod_cast ( by linarith : ( v : ℝ ) - u < 2 * c ) ⟩;
      linarith;
  · obtain ⟨a', ha', b', hb', c', hc', habc'⟩ : ∃ a' ∈ S_a, ∃ b' ∈ S_b, ∃ c' ∈ S_c, a' ≠ b' ∧ a' ≠ c' ∧ b' ≠ c' := by
      exact ( exists_distinct_representatives_of_sets S_a S_b S_c hS_a hS_b hS_c ) |> fun h => h.resolve_right fun h' => h_bad_case ⟨ h'.1, h'.2.1, h'.2.2 ⟩;
    refine' ⟨ { ( a, a' ), ( b, b' ), ( c, c' ) }, _, _ ⟩ <;> simp_all +decide [ is_matching ];
    grind

lemma exists_matching_of_size_eq_card_of_le_3 (A : Finset ℕ) (x : ℝ)
    (hA : A.Nonempty) (hA_pos : ∀ a ∈ A, a > 0) (h_card : A.card ≤ 3) :
    let N := A.max' hA
    let I := Set.Ioo x (x + 2 * N)
    ∃ M, is_matching A I M ∧ M.card = A.card := by
  interval_cases h_card : A.card <;> simp_all +decide;
  · exact absurd ‹A = ∅› hA.ne_empty;
  · obtain ⟨ a, ha ⟩ := Finset.card_eq_one.mp ‹_›;
    -- Since $a$ is positive and the interval $(x, x + 2a)$ has length $2a$, there must be at least one multiple of $a$ in this interval.
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (a : ℝ) * m ∈ Set.Ioo x (x + 2 * a) := by
      exact ⟨ ⌊x / a⌋ + 1, by push_cast; nlinarith [ Int.lt_floor_add_one ( x / a ), show ( a : ℝ ) > 0 from mod_cast hA_pos a ( ha.symm ▸ Finset.mem_singleton_self _ ), mul_div_cancel₀ x ( show ( a : ℝ ) ≠ 0 from mod_cast ne_of_gt ( hA_pos a ( ha.symm ▸ Finset.mem_singleton_self _ ) ) ) ], by push_cast; nlinarith [ Int.floor_le ( x / a ), show ( a : ℝ ) > 0 from mod_cast hA_pos a ( ha.symm ▸ Finset.mem_singleton_self _ ), mul_div_cancel₀ x ( show ( a : ℝ ) ≠ 0 from mod_cast ne_of_gt ( hA_pos a ( ha.symm ▸ Finset.mem_singleton_self _ ) ) ) ] ⟩;
    use {(a, m * a)};
    simp_all +decide [ Finset.max', is_matching ];
    constructor <;> linarith;
  · obtain ⟨a, b, hab⟩ : ∃ a b, a ∈ A ∧ b ∈ A ∧ a < b ∧ A = {a, b} := by
      have := Finset.card_eq_two.mp ‹_›; obtain ⟨ a, b, hab ⟩ := this; cases lt_trichotomy a b <;> aesop;
    obtain ⟨S_a, hS_a⟩ : ∃ S_a : Finset ℤ, S_a.card = 2 ∧ ∀ m ∈ S_a, (a : ℤ) ∣ m ∧ x < m ∧ m < x + 2 * b := by
      have := @count_multiples a x ( 2 * b ) ?_ 2 ?_ <;> aesop;
    obtain ⟨S_b, hS_b⟩ : ∃ S_b : Finset ℤ, S_b.card = 1 ∧ ∀ m ∈ S_b, (b : ℤ) ∣ m ∧ x < m ∧ m < x + 2 * b := by
      have := count_multiples b x ( 2 * b ) ( by linarith [ hA_pos b hab.2.1 ] ) 1 ; aesop;
    obtain ⟨m_a, hm_a⟩ : ∃ m_a ∈ S_a, ∃ m_b ∈ S_b, m_a ≠ m_b := by
      by_contra h_contra; push_neg at h_contra; (
      obtain ⟨ m, hm ⟩ := Finset.card_eq_one.mp hS_b.1; obtain ⟨ n, hn ⟩ := Finset.card_eq_two.mp hS_a.1; aesop;);
    obtain ⟨ m_b, hm_b, hne ⟩ := hm_a.2; use { ( a, m_a ), ( b, m_b ) } ; simp_all +decide [ is_matching ] ;
    grind;
  · exact exists_matching_card_3 A x hA hA_pos h_card

/-
For all positive integers $m$ we have $f(m) = \min(m, \ceil(2\sqrt{m})$.
-/
theorem erdos_650 (m : ℕ) (hm : m ≥ 1) : f m = Nat.min m (Nat.ceil (2 * Real.sqrt m)) := by
  -- For $m \geq 4$, we have $f(m) = \lceil 2\sqrt{m} \rceil$ by `erdos_650_mge4`.
  have h_ge_4 : m ≥ 4 → f m = Nat.ceil (2 * Real.sqrt m) := by
    exact fun a => erdos_650_mge4 m a;
  -- For $m < 4$, we need to show that $f(m) = m$.
  have h_lt_4 : m < 4 → f m = m := by
    intro hm_lt_4
    have h_le_m : f m ≤ m := by
      refine' csSup_le _ _ <;> norm_num +zetaDelta at *;
      · use 0; simp [Property];
      · intro b hb
        specialize hb (Finset.Icc 1 m) 0
        simp at hb
        generalize_proofs at *; (
        refine' le_trans ( hb ( fun a ha₁ ha₂ => ha₁ ) hm ) _;
        refine' csSup_le _ _ <;> norm_num +zetaDelta at *;
        · exact ⟨ 0, ⟨ ∅, by unfold is_matching; aesop ⟩ ⟩;
        · intro a ha; have := Finset.card_le_card ( show a.image Prod.fst ⊆ Finset.Icc 1 m from Finset.image_subset_iff.mpr fun x hx => ha.1 x hx |>.1 ) ; simp_all +decide ;
          rwa [ Finset.card_image_of_injOn fun x hx y hy hxy => by have := ha.2 x y hx hy; aesop ] at this;)
    have h_ge_m : f m ≥ m := by
      refine' le_csSup _ _ <;> norm_num +zetaDelta at *;
      · -- Since for any configuration $A$ of size $m$ and any $x$, the maximum matching size is at most $m$, we have $k \leq m$ for all $k$ in the set.
        have h_le_m : ∀ k, Property m k → k ≤ m := by
          intro k hk
          specialize hk (Finset.Icc 1 m) 0
          generalize_proofs at *; (
          refine' le_trans ( hk ( by norm_num ) ( fun a ha => by linarith [ Finset.mem_Icc.mp ha ] ) ( Finset.nonempty_Icc.mpr hm ) ) _;
          refine' max_matching_size_le _ _ _ _ ; norm_num +zetaDelta at *;
          intro M hM; have := Finset.card_le_card ( show M.image Prod.fst ⊆ Finset.Icc 1 m from Finset.image_subset_iff.mpr fun p hp => hM.1 p hp |>.1 ) ; simp_all +decide ;
          rwa [ Finset.card_image_of_injOn fun x hx y hy hxy => by have := hM.2 x y hx hy; aesop ] at this;)
        generalize_proofs at *; (exact ⟨m, fun k hk => h_le_m k hk⟩;);
      · intro A x hA hA_pos hA_nonempty
        set N := A.max' hA_nonempty
        set I := Set.Ioo x (x + 2 * N)
        have h_exists_matching : ∃ M : Finset (ℕ × ℤ), is_matching A I M ∧ M.card = m := by
          have := exists_matching_of_size_eq_card_of_le_3 A x hA_nonempty hA_pos ( by linarith ) ; aesop;
        exact (by
        obtain ⟨ M, hM₁, hM₂ ⟩ := h_exists_matching; exact le_trans ( by linarith ) ( le_csSup ⟨ A.card, fun k hk => by obtain ⟨ M, hM₁, rfl ⟩ := hk; exact Finset.card_le_card ( show M.image Prod.fst ⊆ A from Finset.image_subset_iff.mpr fun p hp => hM₁.1 p hp |>.1 ) |> fun h => h.trans' ( by rw [ Finset.card_image_of_injOn ] ; exact fun p hp q hq hpq => by have := hM₁.2 p q hp hq; aesop ) ⟩ ⟨ M, hM₁, rfl ⟩ ) ;)
    exact le_antisymm h_le_m h_ge_m;
  cases le_or_gt m 3 <;> simp_all +decide [ Nat.min ];
  · interval_cases m <;> norm_num [ h_lt_4 ] at *;
    · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) );
    · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] ) );
  · rw [ h_ge_4 ‹_›, min_eq_right ];
    exact Nat.ceil_le.mpr ( by nlinarith only [ show ( m : ℝ ) ≥ 4 by norm_cast, Real.mul_self_sqrt ( Nat.cast_nonneg m ) ] )

#print axioms erdos_650
