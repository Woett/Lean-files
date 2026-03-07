/-
Yixin He, Yanyang Li and Quanyu Tang used ChatGPT 5.4 in order to prove that for every positive integer $m$ there exists a positive integer $N$, a set $A \subset \{1, 2, \ldots, N\}$ and an interval $I \subset [1, \infty)$ with $|I| = 2N$ such that the maximum number of disjoint pairs $(a, b)$ with $a \in A$, $b \in I$ and $a | b$ for all $i$ is at most $2 \lceil \sqrt{m} \rceil$. This solves Erdős Problem #650 (https://www.erdosproblems.com/650).

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
The upper bound for Problem #650 holds for any $m \ge 1$.
-/
theorem erdos_650_upper_bound (m : ℕ) (hm : m ≥ 1) :
    ∃ (N : ℕ) (A : Finset ℕ) (I : Set ℕ),
      A.card = m ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      (∃ x y, I = Set.Ioc x y ∧ y - x = 2 * N) ∧
      (∀ (M : Finset (ℕ × ℕ)),
        (∀ p ∈ M, p.1 ∈ A ∧ p.2 ∈ I ∧ p.1 ∣ p.2) →
        (∀ p q, p ∈ M → q ∈ M → p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) →
        M.card ≤ 2 * Nat.ceil (Real.sqrt m)) := by
  -- Let $n = \lceil \sqrt{m} \rceil$.
  set n := Nat.ceil (Real.sqrt m) with hn_def
  have hn : n ≥ 1 := by
    exact Nat.ceil_pos.mpr <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr hm;
  -- Apply `erdos_650_upper_bound_st` with $s = t = n$.
  obtain ⟨N, A_big, I, hA_big, hI, hM⟩ := erdos_650_upper_bound_st n n (by linarith) (by linarith);
  -- Choose a subset $A \subseteq A_{big}$ with $|A| = m$.
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A ⊆ A_big ∧ A.card = m := by
    exact Finset.exists_subset_card_eq ( by nlinarith [ show m ≤ n * n by have := Nat.le_ceil ( Real.sqrt m ) ; rw [ Real.sqrt_le_iff ] at this ; norm_cast at * ; nlinarith ] );
  exact ⟨ N, A, I, hA.2, fun a ha => hI a ( hA.1 ha ), hM.1, fun M hM₁ hM₂ => by linarith [ hM.2 M ( fun p hp => ⟨ hA.1 ( hM₁ p hp |>.1 ), hM₁ p hp |>.2.1, hM₁ p hp |>.2.2 ⟩ ) hM₂ ] ⟩

#print axioms erdos_650_upper_bound
