/-
Ruzsa answered Erdos Problem #331 (https://www.erdosproblems.com/331) by exhibiting two sets of positive integers $A$ and $B$ such that both $|\{a \in A : a \le x\}| \gg \sqrt{x}$ and $|\{b \in B : b \le x\}| \gg \sqrt{x}$ for large enough $x$ and such that $a_1 - a_2 = b_1 - b_2$ implies $a_1 = a_2$ and $b_1 = b_2$. Indeed, take $A$ and $B$ to be the sets of positive integers whose binary representation only have non-zero digits in even and odd places respectively. A formalization of this result, obtained with the help of Aristotle, can be found below.

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
Define subsets A and B of natural numbers based on their binary expansion. A contains numbers where all odd-indexed bits are 0, and B contains numbers where all even-indexed bits are 0.
-/
def A : Set ℕ := { n | ∀ k, Odd k → n.testBit k = false }

def B : Set ℕ := { n | ∀ k, Even k → n.testBit k = false }

/-
Define helper functions partA and partB to construct the components of n in A and B.
-/
def partA (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (n % 2) + 4 * partA (n / 4)
termination_by n
decreasing_by all_goals
exact Nat.div_lt_self ( Nat.pos_of_ne_zero ‹_› ) ( by decide )

def partB (n : ℕ) : ℕ := 2 * partA (n / 2)

/-
The k-th bit of partA n is the k-th bit of n if k is even, and 0 otherwise.
-/
lemma partA_testBit (n k : ℕ) : (partA n).testBit k = (if Even k then n.testBit k else false) := by
  induction' n using Nat.strong_induction_on with n ih generalizing k;
  rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [*];
  · unfold partA; aesop;
  · rcases k with ( _ | _ | k ) <;> simp +decide [ partA, Nat.testBit ];
    norm_num [ Nat.shiftRight_eq_div_pow ];
    norm_num [ Nat.div_eq_of_lt ];
  · unfold partA; simp +arith +decide [ Nat.testBit ] ;
    unfold partA; simp +arith +decide ;
    rcases k with ( _ | _ | k ) <;> simp +arith +decide [ Nat.shiftRight_eq_div_pow ];
    norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
  · unfold partA; simp +arith +decide [ *, Nat.testBit ] ;
    rcases k with ( _ | _ | k ) <;> simp +arith +decide [*, Nat.shiftRight_eq_div_pow];
    · grind;
    · grind;
    · convert ih ( ( n + 3 ) / 4 ) ( Nat.div_lt_of_lt_mul <| by linarith ) ( k ) using 1 ; norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ; ring_nf;
      · norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod, Nat.div_div_eq_div_mul ];
        cases Nat.mod_two_eq_zero_or_one n <;> simp +decide [*, Nat.add_mod];
        · grind;
        · grind;
      · simp +arith +decide [ Nat.even_add_one, Nat.testBit ];
        norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul, Nat.shiftRight_eq_div_pow ];
        norm_num [ Nat.div_div_eq_div_mul ]

/-
The k-th bit of partB n is the k-th bit of n if k is odd, and 0 otherwise.
-/
lemma partB_testBit (n k : ℕ) : (partB n).testBit k = (if Odd k then n.testBit k else false) := by
  unfold partB;
  rcases k with ( _ | k ) <;> simp_all +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
  convert partA_testBit ( n / 2 ) k using 1 ; norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ; ring_nf;
  · grind;
  · grind

/-
If a is in A and b is in B, then their bitwise AND is 0.
-/
lemma disjoint_bits {a b : ℕ} (ha : a ∈ A) (hb : b ∈ B) : a &&& b = 0 := by
  -- By definition of $A$ and $B$, for any $k$, if $k$ is odd, then $a.testBit k = false$, and if $k$ is even, then $b.testBit k = false$.
  have h_bitwise : ∀ k, (a.testBit k && b.testBit k) = false := by
    intro k; by_cases hk : Even k <;> simp_all +decide [ A, B ] ;
  exact Nat.eq_of_testBit_eq fun k => by simpa using h_bitwise k;

/-
If n = a + b with a in A and b in B, then a must be partA n and b must be partB n.
-/
lemma unique_decomposition {n a b : ℕ} (ha : a ∈ A) (hb : b ∈ B) (h : n = a + b) : a = partA n ∧ b = partB n := by
  -- Since $a \in A$ and $b \in B$, their bitwise AND is 0, so $a + b = a ||| b$.
  have h_or : a + b = a ||| b := by
    have h_or : a &&& b = 0 := by
      exact disjoint_bits ha hb;
    have h_or : ∀ x y : ℕ, x &&& y = 0 → x + y = x ||| y := by
      intro x y hxy; induction' x using Nat.binaryRec with x ih generalizing y <;> induction' y using Nat.binaryRec with y ih' <;> simp_all +decide ;
      cases x <;> cases y <;> simp_all +decide [ Nat.bit ];
      · linarith [ ‹∀ y : ℕ, ih &&& y = 0 → ih + y = ih ||| y› ih' hxy ];
      · grind;
      · linarith [ ‹∀ y : ℕ, ih &&& y = 0 → ih + y = ih ||| y› ih' hxy ];
    apply h_or; assumption;
  -- Since $a$ and $b$ have no overlapping set bits, the k-th bit of $a ||| b$ is the k-th bit of $a$ if $k$ is even, and the k-th bit of $b$ if $k$ is odd.
  have h_bitwise : ∀ k, ((a ||| b).testBit k) = (if Even k then a.testBit k else b.testBit k) := by
    intro k; split_ifs <;> simp_all +decide [ Nat.testBit_or ] ;
    · exact fun h => False.elim <| hb k ( by simpa using ‹Even k› ) |> fun h' => by aesop;
    · exact fun h => False.elim <| absurd ( ha k <| by tauto ) ( by aesop );
  -- Since $a$ and $b$ have no overlapping set bits, the k-th bit of $partA (a ||| b)$ is the k-th bit of $a$ if $k$ is even, and 0 otherwise.
  have h_partA : ∀ k, ((partA (a ||| b)).testBit k) = (if Even k then a.testBit k else false) := by
    intro k; rw [ partA_testBit ] ; aesop;
  -- Since $a$ and $b$ have no overlapping set bits, the k-th bit of $partB (a ||| b)$ is the k-th bit of $b$ if $k$ is odd, and 0 otherwise.
  have h_partB : ∀ k, ((partB (a ||| b)).testBit k) = (if Odd k then b.testBit k else false) := by
    intros k
    rw [partB_testBit];
    grind;
  -- Since $a$ and $b$ have no overlapping set bits, the k-th bit of $partA (a ||| b)$ is the k-th bit of $a$, and the k-th bit of $partB (a ||| b)$ is the k-th bit of $b$.
  have h_partA_eq : partA (a ||| b) = a := by
    refine' Nat.eq_of_testBit_eq fun k => _;
    by_cases hk : Even k <;> simp +decide [ hk, h_partA ];
    exact ha k ( by simpa using hk )
  have h_partB_eq : partB (a ||| b) = b := by
    refine' Nat.eq_of_testBit_eq fun k => _;
    by_cases hk : Even k <;> simp +decide [h_partB];
    · exact fun h => absurd h ( by simpa [ hk ] using hb k hk );
    · exact fun _ => Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => hk <| Nat.even_iff.mpr h );
  grind

/-
Membership in A is decidable because we only need to check bits up to log2(n).
-/
instance decidableA : DecidablePred (· ∈ A) := by
  intro n
  apply decidable_of_iff (∀ k < n.log2 + 1, Odd k → n.testBit k = false)
  -- For the reverse direction, if all odd-indexed bits of $n$ are zero, then for any odd $k$, the $k$-th bit of $n$ is zero. If $k$ is greater than the length of the binary representation, then $n.testBit k$ is also zero. Hence, $n \in A$.
  apply Iff.intro;
  · intro h k hk
    by_cases hk_le : k ≤ n.log2;
    · exact h k ( Nat.lt_succ_of_le hk_le ) hk;
    · rw [ Nat.testBit_eq_false_of_lt ];
      contrapose! hk_le;
      rw [ Nat.le_log2 ] <;> linarith [ Nat.pos_of_ne_zero ( show n ≠ 0 by rintro rfl; norm_num at hk_le ) ];
  · exact fun h k hk hk' => h k hk'

/-
Membership in B is decidable because we only need to check bits up to log2(n).
-/
instance decidableB : DecidablePred (· ∈ B) := by
  intro n
  apply decidable_of_iff (∀ k < n.log2 + 1, Even k → n.testBit k = false)
  constructor <;> intro h;
  · intro k;
    by_cases hk : k < n.log2 + 1;
    · exact h k hk;
    · rw [ Nat.testBit_eq_false_of_lt ];
      · exact fun a => rfl;
      · contrapose! hk;
        rw [ Nat.lt_succ_iff, Nat.le_log2 ] <;> linarith [ Nat.pos_of_ne_zero ( show n ≠ 0 by rintro rfl; norm_num at hk ) ];
  · exact fun k hk₁ hk₂ => h k ( by simpa using hk₂ )

/-
Define expandA and expandB to map dense integers to sparse integers in A and B.
-/
def expandA (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (n % 2) + 4 * expandA (n / 2)
termination_by n
decreasing_by all_goals exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹_›) (by decide)

def expandB (n : ℕ) : ℕ := 2 * expandA n

/-
expandA n is in A.
-/
lemma expandA_in_A (n : ℕ) : expandA n ∈ A := by
  -- By definition of $expandA$, we know that $expandA(n)$ has odd-indexed bits as 0.
  have h_expandA_testBit : ∀ n k, (expandA n).testBit k = if Even k then (n.testBit (k / 2)) else false := by
    -- We'll use induction on $n$ to prove the equivalence.
    intro n k
    induction' n using Nat.strong_induction_on with n ih generalizing k;
    unfold expandA;
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
    · grind;
    · grind;
    · split_ifs <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
      convert ih ( n / 2 ) ( Nat.div_lt_self ( Nat.pos_of_ne_zero ‹_› ) ( by decide ) ) k using 1 ; norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
      · norm_num [ Nat.mul_div_assoc, Nat.mul_mod, Nat.mul_comm ];
        cases Nat.mod_two_eq_zero_or_one n <;> simp +decide [ * ];
        · split_ifs <;> omega;
        · split_ifs <;> omega;
      · norm_num [ Nat.even_add_one, Nat.div_div_eq_div_mul ];
        rw [ show ( k + 1 + 1 ) / 2 = k / 2 + 1 by omega, pow_succ' ];
  exact fun k hk => h_expandA_testBit n k ▸ if_neg ( by simpa using hk )

/-
expandB n is in B.
-/
lemma expandB_in_B (n : ℕ) : expandB n ∈ B := by
  intro k hk;
  rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.testBit ];
  · exact Nat.mod_eq_zero_of_dvd ( dvd_mul_of_dvd_left ( by norm_num ) _ );
  · unfold expandB; simp +arith +decide [ Nat.shiftRight_eq_div_pow ] ;
    -- By definition of expandA, we know that expandA n is in A.
    have h_expandA_in_A : expandA n ∈ A := by
      exact expandA_in_A n;
    -- Since expandA n is in A, all its odd-indexed bits are zero. When we multiply by 2, those bits shift left, but since they were zero, they remain zero. Therefore, the result of the division and modulo operations should also be zero.
    have h_odd_bits_zero : ∀ k, Odd k → (expandA n).testBit k = false := by
      exact fun k hk => h_expandA_in_A k hk;
    convert h_odd_bits_zero ( k + 1 ) ( by simpa [ parity_simps ] using hk ) using 1;
    norm_num [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
    norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]

/-
expandA is strictly monotonic.
-/
lemma expandA_strict_mono : StrictMono expandA := by
  refine' strictMono_nat_of_lt_succ _;
  intro n;
  induction' n using Nat.strong_induction_on with n ih;
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
  · unfold expandA;
    rcases k with ( _ | k ) <;> simp +arith +decide [ Nat.add_div ];
  · unfold expandA; simp +arith +decide [Nat.add_mod] ;
    norm_num [ Nat.add_div ];
    grind

/-
expandB is strictly monotonic.
-/
lemma expandB_strict_mono : StrictMono expandB := by
  exact fun a b hab => mul_lt_mul_of_pos_left ( expandA_strict_mono hab ) zero_lt_two

/-
If n < 2^k, then expandA n < 4^k.
-/
lemma expandA_lt {k n : ℕ} (h : n < 2^k) : expandA n < 4^k := by
  -- By definition of expandA, we know that expandA n is less than 4^(k+1) because each step in the recursion multiplies by 4.
  have h_expandA_le : ∀ k, ∀ n < 2 ^ k, expandA n < 4 ^ k := by
    intro k n hn;
    induction' k with k ih generalizing n <;> norm_num [ Nat.pow_succ' ] at *;
    · unfold expandA; aesop;
    · -- By definition of expandA, we have expandA n = (n % 2) + 4 * expandA (n / 2).
      have h_expandA_def : expandA n = (n % 2) + 4 * expandA (n / 2) := by
        by_cases hn : n = 0;
        · simp +decide [ hn, expandA ];
        · rw [ expandA ];
          aesop;
      grind;
  exact h_expandA_le k n h

/-
If n < 2^((m+1)/2), then expandA n < 2^m.
-/
lemma expandA_lt_pow_two {n m : ℕ} (h : n < 2^((m+1)/2)) : expandA n < 2^m := by
  -- Apply the lemma expandA_lt with k = (m+1)/2.
  have h_expandA_lt : expandA n < 4 ^ ((m + 1) / 2) := by
    convert expandA_lt h using 1;
  -- Since $4^k = 2^{2k}$, we can rewrite $4^{(m+1)/2}$ as $2^{2*(m+1)/2}$.
  have h_exp : 4 ^ ((m + 1) / 2) = 2 ^ (2 * ((m + 1) / 2)) := by
    norm_num [ pow_mul ];
  rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> simp_all +arith +decide;
  · norm_num [ Nat.add_div ] at * ; linarith;
  · -- By definition of $expandA$, we know that $expandA n$ has its binary representation with 1s only in even positions.
    have h_expandA_binary : ∀ n, (expandA n).testBit (2 * k + 1) = false := by
      intro n
      have h_expandA_binary : ∀ n, (expandA n) ∈ A := by
        exact fun n => expandA_in_A n;
      exact h_expandA_binary n ( 2 * k + 1 ) ( by simp +decide [ parity_simps ] );
    contrapose! h_expandA_binary;
    use n;
    norm_num [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
    rw [ Nat.mod_eq_of_lt ];
    · exact Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by ring_nf at *; linarith ) ( Nat.div_pos h_expandA_binary <| by positivity );
    · exact Nat.div_lt_of_lt_mul <| by ring_nf at *; linarith;

/-
If n < 2^(m/2), then expandB n < 2^m.
-/
lemma expandB_lt_pow_two {n m : ℕ} (h : n < 2^(m/2)) : expandB n < 2^m := by
  have h_expandB : expandB n = 2 * expandA n := rfl
  rcases m with ( _ | _ | m )
  · -- m = 0: h : n < 2^(0/2), i.e. n < 1, so n = 0
    have hn : n = 0 := by omega
    subst hn; simp [expandB, expandA]
  · -- m = 1: h : n < 2^(1/2), i.e. n < 1, so n = 0
    have hn : n = 0 := by omega
    subst hn; simp [expandB, expandA]
  · -- m = m + 2: the inductive case, same as before
    simp_all +decide [pow_succ']
    have h_expandA : expandA n < 2 ^ (m + 1) := by
      convert expandA_lt_pow_two _ using 1
      exact h
    rwa [ pow_succ' ] at h_expandA


/-
If 2^m <= N, then the number of elements of A in {1, ..., N} is at least 2^((m+1)/2) - 1.
-/
lemma card_A_ge_of_pow {N m : ℕ} (h : 2^m ≤ N) :
  ((Finset.Icc 1 N).filter (· ∈ A)).card ≥ 2^((m+1)/2) - 1 := by
    -- By Lemma 24, expandA x is in A and less than or equal to N for all x < 2^((m+1)/2).
    have h_expandA_subset : Finset.image (fun x => expandA x) (Finset.Ico 1 (2^((m+1)/2))) ⊆ Finset.filter (fun x => x ∈ A) (Finset.Icc 1 N) := by
      intro;
      norm_num +zetaDelta at *;
      rintro x hx₁ hx₂ rfl;
      refine' ⟨ ⟨ Nat.one_le_iff_ne_zero.mpr _, _ ⟩, expandA_in_A x ⟩;
      · -- By definition of expandA, we know that expandA x is strictly increasing.
        have h_expandA_mono : StrictMono expandA := by
          exact expandA_strict_mono;
        exact Nat.ne_zero_of_lt (h_expandA_mono hx₁);
      · -- By Lemma 25, expandA x < 2^m.
        have h_expandA_lt : expandA x < 2^m := by
          convert expandA_lt_pow_two hx₂ using 1;
        linarith;
    have := Finset.card_mono h_expandA_subset; rw [ Finset.card_image_of_injective _ fun a b h => StrictMono.injective ( expandA_strict_mono ) h ] at this; aesop;

/-
If 2^m <= N, then the number of elements of B in {1, ..., N} is at least 2^(m/2) - 1.
-/
lemma card_B_ge_of_pow {N m : ℕ} (h : 2^m ≤ N) :
  ((Finset.Icc 1 N).filter (· ∈ B)).card ≥ 2^(m/2) - 1 := by
    -- By definition of $B$, the number of elements in $B$ up to $N$ is at least the number of elements in the set $\{ \text{expandB } n \mid n \in \{1, 2, \ldots, 2^{m/2} - 1\} \}$.
    have h_B_ge_expandB : ((Finset.Icc 1 N).filter (· ∈ B)).card ≥ Finset.card (Finset.image expandB (Finset.Icc 1 (2^(m/2)-1))) := by
      refine Finset.card_le_card ?_;
      intro aesop;
      simp +zetaDelta at *;
      rintro x hx₁ hx₂ rfl; refine' ⟨ ⟨ _, _ ⟩, _ ⟩ <;> try linarith [ Nat.sub_add_cancel ( Nat.one_le_pow ( m / 2 ) 2 zero_lt_two ), expandB_lt_pow_two ( show x < 2 ^ ( m / 2 ) from lt_of_le_of_lt hx₂ ( Nat.sub_lt ( by positivity ) ( by positivity ) ) ) ] ;
      · refine' Nat.mul_pos ( by decide ) ( _ );
        -- By definition of $expandA$, we know that $expandA x$ is strictly increasing.
        have h_expandA_mono : StrictMono expandA := by
          exact expandA_strict_mono;
        exact Nat.zero_lt_of_lt (h_expandA_mono hx₁);
      · exact expandB_in_B x;
    rwa [ Finset.card_image_of_injective _ expandB_strict_mono.injective, Nat.card_Icc, Nat.add_sub_cancel ] at h_B_ge_expandB

/-
There exists N0 >= 2 such that for all N >= N0, the number of elements of A in {1, ..., N} is at least (1/4) * sqrt(N), and similarly for B.
-/
lemma density_lemma : ∃ N₀ ≥ 2, ∀ N ≥ N₀,
  ((Finset.Icc 1 N).filter (· ∈ A)).card ≥ (1/4 : ℝ) * Real.sqrt N ∧
  ((Finset.Icc 1 N).filter (· ∈ B)).card ≥ (1/4 : ℝ) * Real.sqrt N := by
    -- Let's choose $N_0 = 64$.
    use 64;
    -- By definition of $A$ and $B$, we know that for all $N \ge 64$, the cardinalities of $A \cap \{1, \ldots, N\}$ and $B \cap \{1, \ldots, N\}$ are at least $(1 / 4) * \sqrt{N}$.
    have h_card_A : ∀ N ≥ 64, ((Finset.Icc 1 N).filter (· ∈ A)).card ≥ (1 / 4 : ℝ) * Real.sqrt N := by
      intro N hN
      have h_card_A_ge : ((Finset.Icc 1 N).filter (· ∈ A)).card ≥ 2^((Nat.log2 N + 1) / 2) - 1 := by
        have h_card_A_ge : ((Finset.Icc 1 N).filter (· ∈ A)).card ≥ 2^((Nat.log2 N + 1) / 2) - 1 := by
          have h_log2 : 2^(Nat.log2 N) ≤ N := by
            rw [ ← Nat.le_log2 ] ; linarith
          convert card_A_ge_of_pow h_log2 using 1;
        assumption;
      -- Using the fact that $2^{(Nat.log2 N + 1) / 2} \geq \sqrt{N} / 2$, we can conclude the proof.
      have h_sqrt : (2 : ℝ) ^ ((Nat.log2 N + 1) / 2) ≥ Real.sqrt N / 2 := by
        have h_sqrt : (2 : ℝ) ^ (Nat.log2 N) ≥ N / 2 := by
          -- By definition of logarithm, we know that $2^{Nat.log2 N} \leq N < 2^{Nat.log2 N + 1}$.
          have h_log : (2 : ℝ) ^ (Nat.log2 N) ≤ N ∧ N < (2 : ℝ) ^ (Nat.log2 N + 1) := by
            norm_cast;
            rw [ ← Nat.le_log2, ← Nat.log2_lt ] <;> norm_num ; linarith;
            linarith;
          norm_num [ pow_succ' ] at * ; linarith;
        have h_sqrt : (2 : ℝ) ^ ((Nat.log2 N + 1) / 2) ≥ Real.sqrt ((2 : ℝ) ^ (Nat.log2 N)) := by
          rw [ ge_iff_le, Real.sqrt_le_left ] <;> norm_cast <;> norm_num [ pow_mul' ];
          rw [ ← pow_mul ] ; exact pow_le_pow_right₀ ( by norm_num ) ( by omega ) ;
        exact le_trans ( Real.le_sqrt_of_sq_le ( by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ ( N : ℝ ) by positivity ) ] ) ) h_sqrt;
      refine' le_trans _ ( Nat.cast_le.mpr h_card_A_ge );
      rw [ Nat.cast_sub ] <;> norm_num;
      · nlinarith [ Real.sqrt_nonneg N, Real.sq_sqrt <| Nat.cast_nonneg N, show ( N : ℝ ) ≥ 64 by norm_cast ];
      · exact one_le_pow₀ ( by norm_num )
    have h_card_B : ∀ N ≥ 64, ((Finset.Icc 1 N).filter (· ∈ B)).card ≥ (1 / 4 : ℝ) * Real.sqrt N := by
      intros N hN_ge
      have h_card_B_ge : ((Finset.Icc 1 N).filter (· ∈ B)).card ≥ 2^(Nat.log2 N / 2) - 1 := by
        -- Apply the lemma that states the cardinality of B in {1, ..., N} is at least 2^(m/2) - 1 when 2^m ≤ N.
        have h_card_B_ge : ∀ m, 2^m ≤ N → ((Finset.Icc 1 N).filter (· ∈ B)).card ≥ 2^(m/2) - 1 := by
          exact fun m a => card_B_ge_of_pow a;
        convert h_card_B_ge ( Nat.log2 N ) _;
        rw [ ← Nat.le_log2 ] ; linarith;
      -- Since $2^{Nat.log2 N / 2} \geq \sqrt{N} / 2$, we have $2^{Nat.log2 N / 2} - 1 \geq \sqrt{N} / 2 - 1$.
      have h_sqrt_B : (2 : ℝ) ^ (Nat.log2 N / 2) ≥ Real.sqrt N / 2 := by
        field_simp;
        rw [ Real.sqrt_le_left ] <;> norm_cast <;> ring_nf <;> norm_num;
        have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) N;
        rw [ Nat.pow_succ ] at this;
        rw [ show Nat.log2 N = Nat.log 2 N from ?_ ] at *;
        · exact le_trans ( Nat.le_of_lt this ) ( by rw [ show 2 ^ Nat.log 2 N = 2 ^ ( Nat.log 2 N / 2 * 2 ) * 2 ^ ( Nat.log 2 N % 2 ) by rw [ ← pow_add, Nat.div_add_mod' ] ] ; nlinarith [ pow_pos ( by decide : 0 < 2 ) ( Nat.log 2 N / 2 * 2 ), pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( show Nat.log 2 N % 2 ≤ 1 by exact Nat.le_of_lt_succ ( Nat.mod_lt _ ( by decide ) ) ) ] );
        · exact Nat.log2_eq_log_two;
        · exact Nat.log2_eq_log_two;
      refine le_trans ?_ ( Nat.cast_le.mpr h_card_B_ge ) ; norm_num ; nlinarith [ Real.sqrt_nonneg N, Real.sq_sqrt <| Nat.cast_nonneg N, ( by norm_cast : ( 64 :ℝ ) ≤ N ) ];
    exact ⟨ by norm_num, fun N hN => ⟨ h_card_A N hN, h_card_B N hN ⟩ ⟩

/-
There exist sets of positive integers A' and B' such that they have density at least (1/4)sqrt(N) and their difference sets are disjoint (except at 0).
-/
theorem main_theorem : ∃ (A' B' : Set ℕ),
  (∀ x ∈ A', x > 0) ∧ (∀ x ∈ B', x > 0) ∧
  (∃ N₀, ∀ N ≥ N₀, ((Finset.Icc 1 N).filter (· ∈ A')).card ≥ (1/4 : ℝ) * Real.sqrt N ∧
                   ((Finset.Icc 1 N).filter (· ∈ B')).card ≥ (1/4 : ℝ) * Real.sqrt N) ∧
  (∀ a₁ ∈ A', ∀ a₂ ∈ A', ∀ b₁ ∈ B', ∀ b₂ ∈ B', a₁ ≠ a₂ → a₁ - (a₂ : ℤ) ≠ b₁ - (b₂ : ℤ)) := by
    -- Let's choose $A' = A \setminus \{0\}$ and $B' = B \setminus \{0\}$.
    use {n | n ∈ A ∧ n > 0}, {n | n ∈ B ∧ n > 0};
    refine' ⟨ _, _, _, _ ⟩;
    · exact fun x hx => hx.2;
    · exact fun x hx => hx.2;
    · obtain ⟨ N₀, hN₀ ⟩ := density_lemma;
      use N₀ + 1;
      intro N hN; specialize hN₀; have := hN₀.2 N ( by linarith ) ; simp_all +decide ;
      exact ⟨ this.1.trans ( mod_cast Finset.card_mono <| fun x hx => by aesop ), this.2.trans ( mod_cast Finset.card_mono <| fun x hx => by aesop ) ⟩;
    · intro a₁ ha₁ a₂ ha₂ b₁ hb₁ b₂ hb₂ hne h;
      -- By uniqueness of representation (Lemma 1), $a_1 + b_2 = a_2 + b_1$ implies $a_1 = a_2$ and $b_2 = b_1$.
      have h_unique : a₁ + b₂ = a₂ + b₁ → a₁ = a₂ ∧ b₂ = b₁ := by
        intros h_eq
        have h_unique : a₁ = partA (a₁ + b₂) ∧ b₂ = partB (a₁ + b₂) ∧ a₂ = partA (a₂ + b₁) ∧ b₁ = partB (a₂ + b₁) := by
          exact ⟨ unique_decomposition ha₁.1 hb₂.1 rfl |>.1, unique_decomposition ha₁.1 hb₂.1 rfl |>.2, unique_decomposition ha₂.1 hb₁.1 rfl |>.1, unique_decomposition ha₂.1 hb₁.1 rfl |>.2 ⟩;
        grind;
      grind

#print axioms main_theorem