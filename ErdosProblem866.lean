/-
For an integer $k \ge 3$ we define $g_k(n)$ as the smallest integer such that for any set $A \subseteq \{1, 2, \ldots, 2n\}$ with $|A| \ge n + g_k(n)$ there exist distinct integers $b_1, b_2 \ldots, b_k$ such that all $\binom{k}{2}$ pairwise sums are in $A$. We further let $h_k(n)$ be the analogous function where we require the $b_i$ to be positive integers. We note that the $b_i$ in the above definition need not be in $A$ themselves.

Since at most one of the $b_i$ can be non-positive (as otherwise we have a negative sum), we note that, in general,

$h_{k-1}(n) ≤ g_k(n) \le h_k(n)$ for all $k$ and $n$.

Estimating $g_k(n)$ is Erdős problem #866 (https://www.erdosproblems.com/866) for which Choi, Erdős, and Szemerédi already claimed the following estimates (where $C_4, c_5, C_5, c_6, C_6$ are all absolute positive constants):

$g_3(n) = 2$ for all $n \ge 4$.
$g_4(n) \le C_4$.
$c_5 \log n \le g_5(n) \le C_5 \log n$ for all $n \ge 2$.
$c_6 \sqrt{n} \le g_6(n) \le C_6 \sqrt{n}$.

Choi, S. L. G. and Erdős, P. and Szemerédi, E., Some additive and multiplicative problems in number theory. Acta Arith., 37--50 (1975).

However, they (inadvertently?) actually proved these bounds for $h_k(n)$ instead of $g_k(n)$, rendering their lower bounds for $g_3(n)$ and $g_5(n)$ incorrect as stated.

Below you can find formalizations of the following bounds:

$h_3(n) = 2$ for all $n \ge 4$.
$g_3(n) = 1$ for all $n \ge 3$.
$g_4(n) \le 2032$.
$g_5(n) \le 10^9 \log n$ for all $n \ge 2$.

These formalizations were obtained with the help of Aristotle from Harmonic (aristotle-harmonic@harmonic.fun). In the proofs I also had to use an explicit upper bound on the size of Sidon sequences by O'Bryant, so his result is included in the formalization as well.

O'Bryant, K. On the Size of Finite Sidon Sets. Ukr. Math. J. 76, 1352–1368 (2025).

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
Sn n is the set {1, ..., 2n}, while Tn n is the set {1, ..., 2n} as a subset of ℕ. HasPairwiseSums k A means there exists a set s of size k such that all pairwise sums of distinct elements in s are in A. PropertyP n k m means that any subset A of Sn n with size at least n + m has pairwise sums of k elements, and PropertyQ n k m is the analogous property for subsets of Tn n where s only contains positive elements.
-/
open Finset

def Sn (n : ℕ) : Finset ℤ := Icc 1 (2 * n)

def Tn (n : ℕ) : Finset ℕ := Icc 1 (2 * n)

def HasPairwiseSums (k : ℕ) (A : Finset ℤ) : Prop :=
  ∃ (s : Finset ℤ), s.card = k ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → x + y ∈ A

def HasPositivePairwiseSums (k : ℕ) (A : Finset ℕ) : Prop :=
  ∃ (s : Finset ℕ), s.card = k ∧ (∀ x ∈ s, 0 < x) ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → x + y ∈ A

def PropertyP (n k m : ℕ) : Prop :=
  ∀ A : Finset ℤ, A ⊆ Sn n → A.card ≥ n + m → HasPairwiseSums k A

def PropertyQ (n k m : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Tn n → A.card ≥ n + m → HasPositivePairwiseSums k A

/-
g k n is the smallest m such that PropertyP n k m holds.
-/
noncomputable def g (k n : ℕ) : ℕ := sInf {m | PropertyP n k m}

/-
h k n is the smallest m such that PropertyQ n k m holds.
-/
noncomputable def h (k n : ℕ) : ℕ := sInf {m | PropertyQ n k m}

/-
Easy lower bound on g 3 n.
-/
lemma g_3_ge_1 (n : ℕ) : ¬ PropertyP n 3 0 := by
  -- Consider the set of all odd integers in $S_n$. It has $n$ elements.
  have h_odd_set : ∃ A : Finset ℤ, A ⊆ Sn n ∧ A.card = n ∧ ∀ a ∈ A, a % 2 = 1 := by
    use Finset.image ( fun i : ℕ => 2 * i + 1 ) ( Finset.range n );
    rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    exact Finset.image_subset_iff.mpr fun i hi => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_range.mp hi ], by linarith [ Finset.mem_range.mp hi ] ⟩;
  obtain ⟨ A, hA₁, hA₂, hA₃ ⟩ := h_odd_set;
  intro hP; obtain ⟨ s, hs₁, hs₂ ⟩ := hP A hA₁ ( by linarith ) ; rcases Finset.card_eq_three.mp hs₁ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hca ⟩ ; simp_all +decide ;
  grind +ring

/-
Counterexample set consisting of 2 and all odd numbers in Tn.
-/
def CounterexampleParity (n : ℕ) : Finset ℕ := {2} ∪ ((Tn n).filter Odd)

/-
Properties of CounterexampleParity: subset of Tn and size n+1.
-/
lemma CounterexampleParity_properties (n : ℕ) (hn : n ≥ 1) :
  CounterexampleParity n ⊆ Tn n ∧ (CounterexampleParity n).card = n + 1 := by
  simp +decide [ CounterexampleParity, Tn ];
  rw [ Finset.card_eq_of_bijective ];
  refine' ⟨ _, rfl ⟩;
  exact Finset.insert_subset_iff.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, Finset.filter_subset _ _ ⟩;
  use fun i hi => 2 * i + 1;
  · exact fun a ha => by rcases Finset.mem_filter.mp ha with ⟨ ha₁, ha₂ ⟩ ; obtain ⟨ k, rfl ⟩ := ha₂; exact ⟨ k, by linarith [ Finset.mem_Icc.mp ha₁ ], rfl ⟩ ;
  · exact fun i hi => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, by simp +decide ⟩;
  · aesop

/-
If the only even element in A is 2, then A cannot have positive pairwise sums for k=3.
-/
lemma no_s_3_if_only_even_is_2 (A : Finset ℕ) (h_even : ∀ x ∈ A, Even x → x = 2) :
  ¬ HasPositivePairwiseSums 3 A := by
  rintro ⟨ s, hs ⟩;
  rcases Finset.card_eq_three.mp hs.1 with ⟨ x, y, z, hx, hy, hz, hs ⟩ ; simp_all +decide;
  grind +ring

/-
The only even element in CounterexampleParity is 2.
-/
lemma CounterexampleParity_even_is_2 (n : ℕ) (x : ℕ) (hx : x ∈ CounterexampleParity n) (heven : Even x) : x = 2 := by
  have h_even_contradiction : ∀ x ∈ CounterexampleParity n, Even x → x = 2 := by
    intro x hx heven
    have h_filter : x ∈ ((Tn n).filter Odd) ∨ x = 2 := by
      unfold CounterexampleParity at hx; aesop;
    grind;
  exact h_even_contradiction x hx heven

/-
CounterexampleParity fails the pairwise sum condition for k=3.
-/
lemma CounterexampleParity_fails (n : ℕ) :
  ¬ HasPositivePairwiseSums 3 (CounterexampleParity n) := by
  apply no_s_3_if_only_even_is_2;
  exact fun x a a_1 => CounterexampleParity_even_is_2 n x a a_1

/-
Easy lower bound on h 3 n.
-/
lemma h_3_ge_2 (n : ℕ) (hn : n ≥ 1) : ¬ PropertyQ n 3 1 := by
  -- Consider the set of all odd integers in $S_n$ and add 2. It has $n+1$ elements.
  simp [PropertyQ];
  use CounterexampleParity n, CounterexampleParity_properties n hn |>.1, CounterexampleParity_properties n hn |>.2.ge, CounterexampleParity_fails n

/-
HasPairwiseSums 3 A is equivalent to the existence of three distinct elements in A whose sum is even.
-/
lemma HasPairwiseSums_iff_exists_even_sum_triple (A : Finset ℤ) : HasPairwiseSums 3 A ↔ ∃ a b c, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Even (a + b + c) := by
  constructor;
  · rintro ⟨ s, hs ⟩;
    obtain ⟨ x, y, z, h ⟩ := Finset.card_eq_three.mp hs.1;
    use x + y, x + z, y + z;
    grind +ring;
  · simp +zetaDelta at *;
    intro a ha b hb c hc hab hbc hca h_even
    use { (a + b + c) / 2 - c, (a + b + c) / 2 - b, (a + b + c) / 2 - a };
    grind

/-
The number of odd integers in {1, ..., 2n} is n, and the number of even integers is n.
-/
lemma card_odd_even_in_Sn (n : ℕ) : ((Sn n).filter Odd).card = n ∧ ((Sn n).filter Even).card = n := by
  constructor <;> rw [ Finset.card_eq_of_bijective ];
  use fun i hi => 2 * i + 1;
  all_goals norm_num [ Sn ];
  any_goals intros; linarith;
  case right.f => exact fun i hi => 2 * i + 2;
  · exact fun a ha₁ ha₂ ha₃ => by obtain ⟨ k, rfl ⟩ := ha₃; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ] ⟩ ;
  · exact fun a ha₁ ha₂ ha₃ => by obtain ⟨ k, rfl ⟩ := even_iff_two_dvd.mp ha₃; exact ⟨ Int.toNat ( k - 1 ), by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k - 1 ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k - 1 ) ] ⟩ ;
  · exact fun i hi => ⟨ ⟨ by linarith, by linarith ⟩, even_iff_two_dvd.mpr ⟨ i + 1, by ring ⟩ ⟩;
  · aesop

/-
Easy upper bound on g 3 n for n ≥ 3.
-/
lemma g_3_le_1 (n : ℕ) (h : n ≥ 3) : PropertyP n 3 1 := by
  intro A hA hA';
  -- Let `E` be the set of even numbers in `A`, and `O` be the set of odd numbers in `A`.
  set E := A.filter Even
  set O := A.filter Odd
  have hE_card : E.card + O.card = A.card := by
    rw [ Finset.card_filter, Finset.card_filter ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_congr rfl fun x hx => by aesop ] ; aesop;
  have hE_le_n : E.card ≤ n := by
    have hE_le_n : E.card ≤ ((Sn n).filter Even).card := by
      exact Finset.card_le_card fun x hx => Finset.mem_filter.mpr ⟨ hA <| Finset.mem_filter.mp hx |>.1, Finset.mem_filter.mp hx |>.2 ⟩;
    exact hE_le_n.trans ( by rw [ card_odd_even_in_Sn n |>.2 ] )
  have hO_le_n : O.card ≤ n := by
    exact le_trans ( Finset.card_le_card <| Finset.filter_subset_filter _ hA ) ( by simpa using card_odd_even_in_Sn n |>.1.le )
  have hE_or_O : E.card ≥ 3 ∨ (E.card ≥ 1 ∧ O.card ≥ 2) := by
    contrapose! hA'; omega;
  -- In either case, we can find three distinct elements in `A` whose sum is even.
  have h_even_sum : ∃ a b c : ℤ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Even (a + b + c) := by
    rcases hE_or_O with ( h | h );
    · obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.two_lt_card.mp h;
      obtain ⟨ c, hc, hab, hac, hbc ⟩ := hab; use a, b, c; simp_all +decide [parity_simps] ;
      aesop;
    · obtain ⟨ a, ha ⟩ := Finset.card_pos.mp h.1; obtain ⟨ b, hb, c, hc, hbc ⟩ := Finset.one_lt_card.mp h.2; use a, b, c; simp_all +decide [ parity_simps ] ;
      grind;
  exact HasPairwiseSums_iff_exists_even_sum_triple A |>.2 h_even_sum

/-
If $s \subseteq \{2m+2, \dots, 2n\}$ contains no consecutive integers, then $|s| \le n - m$.
-/
lemma card_le_of_subset_Icc_no_consecutive (n m : ℕ) (s : Finset ℕ)
    (h_sub : s ⊆ Finset.Icc (2 * m + 2) (2 * n))
    (h_no_cons : ∀ x y, x ∈ s → y ∈ s → x < y → y ≥ x + 2) :
    s.card ≤ n - m := by
  -- The size of the interval $[2m+2, 2n]$ is $2n - (2m+2) + 1 = 2(n-m) - 1$.
  have h_interval_size : Finset.card (Finset.image (fun x => x / 2) (s)) = s.card := by
    rw [ Finset.card_image_of_injOn ];
    intro x hx y hy; have := h_no_cons x y hx hy; have := h_no_cons y x hy hx; ( norm_num at *; omega; );
  have h_interval_subset : Finset.image (fun x => x / 2) s ⊆ Finset.Icc (m + 1) (n) := by
    exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod x 2, Nat.mod_lt x two_pos, Finset.mem_Icc.mp ( h_sub hx ) ], by linarith [ Nat.div_mul_le_self x 2, Finset.mem_Icc.mp ( h_sub hx ) ] ⟩;
  exact h_interval_size ▸ le_trans ( Finset.card_le_card h_interval_subset ) ( by simp )

/-
If $s \subseteq \{2m+2, \dots, 2n\}$ has no consecutive integers and $|s| \ge n-m$, then $s = \{2m+2, 2m+4, \dots, 2n\}$.
-/
lemma eq_of_card_ge_subset_Icc_no_consecutive (n m : ℕ) (s : Finset ℕ)
    (h_sub : s ⊆ Finset.Icc (2 * m + 2) (2 * n))
    (h_no_cons : ∀ x y, x ∈ s → y ∈ s → x < y → y ≥ x + 2)
    (h_card : s.card ≥ n - m) :
    s = Finset.image (fun k => 2 * m + 2 + 2 * k) (Finset.range (n - m)) := by
  -- Let $k = n - m$. The interval $I = [2m+2, 2n]$ has size $2k-1$.
  set k := n - m
  have hk : k = n - m := by
    rfl
  have hk_interval : Finset.card (Finset.Icc (2*m+2) (2*n)) = 2*k - 1 := by
    cases le_total n m <;> simp_all +arith +decide [ Nat.mul_sub_left_distrib ];
    · omega;
    · rw [ Nat.sub_sub ];
  -- Let the elements of $s$ be $x_0 < x_1 < \dots < x_{r-1}$ where $r = |s| \ge k$.
  obtain ⟨x, hx⟩ : ∃ x : Fin s.card → ℕ, StrictMono x ∧ ∀ i, x i ∈ s := by
    exact ⟨ fun i => s.orderEmbOfFin rfl i, by simp +decide [ StrictMono ], fun i => s.orderEmbOfFin_mem rfl _ ⟩;
  -- We know $x_{i+1} \ge x_i + 2$.
  have hx_diff : ∀ i : Fin (s.card - 1), x ⟨i + 1, by
    exact Nat.lt_pred_iff.mp i.2⟩ ≥ x ⟨i, by
    exact lt_of_lt_of_le i.2 ( Nat.pred_le _ )⟩ + 2 := by
    exact fun i => h_no_cons _ _ ( hx.2 _ ) ( hx.2 _ ) ( hx.1 ( Nat.lt_succ_self _ ) )
  generalize_proofs at *;
  -- Since $r \ge k$, we have $r = k$.
  have hr_eq_k : s.card = k := by
    have hr_eq_k : s.card ≤ k := by
      exact card_le_of_subset_Icc_no_consecutive n m s h_sub h_no_cons;
    grind;
  -- Since $x$ is strictly monotone and $x_i \ge 2m+2 + 2i$, we have $x_i = 2m+2 + 2i$ for all $i$.
  have hx_eq : ∀ i : Fin s.card, x i = 2 * m + 2 + 2 * i := by
    have hx_eq : ∀ i : Fin s.card, x i ≥ 2 * m + 2 + 2 * i := by
      intro ⟨ i, hi ⟩ ; induction' i with i ih <;> norm_num at *;
      · exact Finset.mem_Icc.mp ( h_sub ( hx.2 _ ) ) |>.1;
      · linarith! [ ih ( Nat.lt_of_succ_lt hi ), hx_diff ⟨ i, Nat.lt_pred_iff.mpr hi ⟩ ];
    intro i
    by_contra hx_neq;
    -- If $x_i > 2m+2 + 2i$, then since $x$ is strictly monotone, we have $x_j > 2m+2 + 2j$ for all $j \ge i$.
    have hx_gt : ∀ j : Fin s.card, i ≤ j → x j > 2 * m + 2 + 2 * j := by
      intro j hj;
      induction j ; induction i ; norm_num at *;
      induction hj <;> norm_num at *;
      · grind;
      · linarith [ hx_diff ⟨ _, Nat.lt_pred_iff.mpr ‹_› ⟩, ‹∀ ( isLt : _ < s.card ), 2 * m + 2 + 2 * _ < x ⟨ _, isLt ⟩ › ( Nat.lt_of_succ_lt ‹_› ) ];
    specialize hx_gt ⟨ s.card - 1, Nat.sub_lt ( Fin.pos i ) zero_lt_one ⟩ ( Nat.le_sub_one_of_lt ( Fin.is_lt i ) ) ; simp_all +decide ;
    exact hx_gt.not_ge ( by have := Finset.mem_Icc.mp ( h_sub ( hx.2 ⟨ n - m - 1, by omega ⟩ ) ) ; omega );
  refine' Finset.eq_of_subset_of_card_le ( fun y hy => _ ) _;
  · -- Since $y \in s$, there exists some $i$ such that $y = x i$.
    obtain ⟨i, hi⟩ : ∃ i : Fin s.card, y = x i := by
      have := Finset.eq_of_subset_of_card_le ( show Finset.image x Finset.univ ⊆ s from Finset.image_subset_iff.mpr fun i _ => hx.2 i ) ; simp_all +decide [ Finset.card_image_of_injective _ hx.1.injective ] ;
      grind;
    exact hi.symm ▸ Finset.mem_image.mpr ⟨ i, Finset.mem_range.mpr ( by linarith [ Fin.is_lt i ] ), hx_eq i ▸ rfl ⟩;
  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, hr_eq_k ]

/-
If $A$ satisfies the conditions, then $4, 6, 8 \in A$.
-/
lemma even_subset_structure (n m : ℕ) (hn : n ≥ 4) (A : Finset ℕ)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n)) (hA_card : A.card ≥ n + 2)
    (hm : m ≥ 1) (h_odd_in : 2 * m + 1 ∈ A)
    (h_min_odd : ∀ k ∈ A, k % 2 = 1 → k ≥ 2 * m + 1 ∨ k = 1)
    (h_no_cons : ∀ x y, x ∈ A ∩ Finset.Icc (2 * m + 2) (2 * n) → y ∈ A ∩ Finset.Icc (2 * m + 2) (2 * n) → x < y → y ≥ x + 2) :
    4 ∈ A ∧ 6 ∈ A ∧ 8 ∈ A := by
  -- By Lemma 2, $|A \cap \{1, \dots, 2m\}| = m + 1$ and $|A \cap \{2m+2, \dots, 2n\}| = n - m$.
  have h_split_card : (A ∩ Finset.Icc 1 (2 * m)).card = m + 1 ∧ (A ∩ Finset.Icc (2 * m + 2) (2 * n)).card = n - m := by
    -- Let's split the set $A$ into three parts: $A_1 = A \cap \{1, \dots, 2m\}$, $A_2 = A \cap \{2m+2, \dots, 2n\}$, and $A_3 = A \cap \{2m+1\}$.
    set A1 := A ∩ Finset.Icc 1 (2 * m)
    set A2 := A ∩ Finset.Icc (2 * m + 2) (2 * n)
    set A3 := A ∩ {2 * m + 1};
    -- Since $A \subseteq \{1, \dots, 2n\}$, we have $A = A_1 \cup A_2 \cup A_3$.
    have hA_union : A = A1 ∪ A2 ∪ A3 := by
      simp +zetaDelta at *;
      ext x; by_cases hx : x ≤ 2 * m <;> by_cases hx' : x = 2 * m + 1 <;> simp_all +decide [ Finset.subset_iff ] ;
      · grind;
      · grind;
    -- By Lemma 2, $|A_1| \leq m + 1$ and $|A_2| \leq n - m$.
    have hA1_card : A1.card ≤ m + 1 := by
      -- Since $A_1 \subseteq \{1, 2, 4, \dots, 2m\}$, we have $|A_1| \le m + 1$ by definition of $A_1$.
      have hA1_subset : A1 ⊆ Finset.image (fun k => 2 * k) (Finset.Icc 1 m) ∪ {1} := by
        intro x hx; specialize h_min_odd x; rcases Nat.even_or_odd' x with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
        · exact ⟨ by linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.2 ) ], by linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.2 ) ] ⟩;
        · exact Or.inl ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.2 ), h_min_odd ( Finset.mem_inter.mp hx |>.1 ) |> Or.resolve_left <| by linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.2 ) ] ] );
      exact le_trans ( Finset.card_le_card hA1_subset ) ( Finset.card_union_le _ _ ) |> le_trans <| by rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ] ;
    have hA2_card : A2.card ≤ n - m := by
      convert card_le_of_subset_Icc_no_consecutive n m A2 _ _ using 1;
      · exact Finset.inter_subset_right;
      · assumption;
    -- Since $A = A_1 \cup A_2 \cup A_3$, we have $|A| = |A_1| + |A_2| + |A_3|$.
    have hA_card_eq : A.card = A1.card + A2.card + A3.card := by
      rw [ hA_union, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ];
      · exact Finset.disjoint_left.mpr fun x hx1 hx2 => by linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx1 |>.2 ), Finset.mem_Icc.mp ( Finset.mem_inter.mp hx2 |>.2 ) ] ;
      · norm_num [ Finset.disjoint_left ];
        simp +zetaDelta at *;
        rintro a ( ⟨ ha₁, ha₂, ha₃ ⟩ | ⟨ ha₁, ha₂, ha₃ ⟩ ) ha₄ <;> omega;
    constructor <;> linarith [ show Finset.card ( A ∩ { 2 * m + 1 } ) = 1 from Finset.card_eq_one.mpr ⟨ 2 * m + 1, by simp +decide [h_odd_in] ⟩, Nat.sub_add_cancel ( show m ≤ n from by linarith [ Finset.mem_Icc.mp ( hA_subset h_odd_in ) ] ) ];
  -- By Lemma 3, $A \cap \{1, \dots, 2m\} = \{1, 2, 4, \dots, 2m\}$.
  have h_A1 : A ∩ Finset.Icc 1 (2 * m) = Finset.image (fun k => if k = 0 then 1 else 2 * k) (Finset.range (m + 1)) := by
    refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _ <;> simp_all +decide [ Finset.subset_iff ];
    · rcases Nat.even_or_odd' x with ⟨ k, rfl | rfl ⟩ <;> simp_all +arith +decide;
      · exact ⟨ k, hx.2.2, by cases k <;> aesop ⟩;
      · grind;
    · exact Finset.card_image_le.trans ( by norm_num );
  -- By Lemma 4, $A \cap \{2m+2, \dots, 2n\} = \{2m+2, 2m+4, \dots, 2n\}$.
  have h_A2 : A ∩ Finset.Icc (2 * m + 2) (2 * n) = Finset.image (fun k => 2 * m + 2 + 2 * k) (Finset.range (n - m)) := by
    apply eq_of_card_ge_subset_Icc_no_consecutive;
    · exact Finset.inter_subset_right;
    · assumption;
    · linarith;
  simp_all +decide [ Finset.ext_iff ];
  rcases m with ( _ | _ | _ | _ | m ) <;> simp +arith +decide at *;
  · exact ⟨ h_A2 4 |>.2 ⟨ 0, Nat.sub_pos_of_lt ( by linarith ), rfl ⟩ |>.1, h_A2 6 |>.2 ⟨ 1, Nat.le_sub_one_of_lt ( by linarith ), rfl ⟩ |>.1, h_A2 8 |>.2 ⟨ 2, Nat.le_sub_one_of_lt ( by linarith ), rfl ⟩ |>.1 ⟩;
  · exact ⟨ by simpa using h_A1 4 |>.2 ⟨ 2, by norm_num ⟩ |>.1, by simpa using h_A2 6 |>.2 ⟨ 0, Nat.le_sub_of_add_le ( by linarith ), rfl ⟩ |>.1, by simpa using h_A2 8 |>.2 ⟨ 1, Nat.le_sub_of_add_le ( by linarith ), rfl ⟩ |>.1 ⟩;
  · exact ⟨ by specialize h_A1 4; simp +arith +decide at h_A1; tauto, by specialize h_A1 6; simp +arith +decide at h_A1; tauto, by specialize h_A2 8; simp +arith +decide at h_A2; tauto ⟩;
  · exact ⟨ by have := h_A1 4; exact this.mpr ⟨ 2, by linarith, rfl ⟩ |>.1, by have := h_A1 6; exact this.mpr ⟨ 3, by linarith, rfl ⟩ |>.1, by have := h_A1 8; exact this.mpr ⟨ 4, by linarith, rfl ⟩ |>.1 ⟩

/-
Helper Lemma: In a directed graph where each vertex has in-degree at most 1 and out-degree at most 1, and there are no cycles (implied by the order condition), there exists a matching $M$ such that $2|M| \ge |E|$.
-/
theorem exists_disjoint_pairs {α : Type*} [LinearOrder α] [Fintype α] (E : Finset (α × α))
    (h_right_unique : ∀ p ∈ E, ∀ q ∈ E, p.1 = q.1 → p = q)
    (h_left_unique : ∀ p ∈ E, ∀ q ∈ E, p.2 = q.2 → p = q)
    (h_order : ∀ p ∈ E, p.1 < p.2) :
    ∃ M ⊆ E, 2 * M.card ≥ E.card ∧
    ∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset α) ∩ {q.1, q.2} = ∅ := by
  induction' hE : E.card using Nat.strong_induction_on with k ih generalizing E;
  by_cases hE_empty : E = ∅;
  · grind;
  · -- Let $e$ be an edge in $E$ with the smallest first component.
    obtain ⟨e, heE, he_min⟩ : ∃ e ∈ E, ∀ p ∈ E, p.1 ≥ e.1 := by
      exact Finset.exists_min_image _ _ ( Finset.nonempty_of_ne_empty hE_empty );
    -- Let $S$ be the set of edges in $E$ that intersect $e$.
    set S := Finset.filter (fun p => p.1 = e.1 ∨ p.2 = e.1 ∨ p.1 = e.2 ∨ p.2 = e.2) E;
    -- We claim $|S| \le 2$.
    have hS_card : S.card ≤ 2 := by
      -- Edges in $S$ are those incident to $u$ or $v$.
      have hS_incident : S ⊆ {e} ∪ Finset.filter (fun p => p.1 = e.2) E := by
        intro p hp
        simp [S] at hp
        obtain ⟨hpE, hp_cases⟩ := hp
        by_cases hp1 : p.1 = e.1;
        · exact Finset.mem_union_left _ ( Finset.mem_singleton.mpr ( h_right_unique _ hpE _ heE hp1 ) );
        · by_cases hp2 : p.2 = e.1;
          · contrapose! he_min;
            exact ⟨ p, hpE, by simpa [ hp2 ] using h_order p hpE ⟩;
          · by_cases hp3 : p.1 = e.2 <;> simp +decide [ hp1, hp2, hp3 ] at hp_cases ⊢;
            · exact Or.inr hpE;
            · exact h_left_unique _ hpE _ heE hp_cases ▸ rfl;
      refine' le_trans ( Finset.card_le_card hS_incident ) _;
      exact le_trans ( Finset.card_union_le _ _ ) ( by exact le_trans ( add_le_add_left ( Finset.card_le_one.mpr fun p hp q hq => h_right_unique _ ( Finset.mem_filter.mp hp |>.1 ) _ ( Finset.mem_filter.mp hq |>.1 ) <| by simp +decide [ Finset.mem_filter.mp hp |>.2, Finset.mem_filter.mp hq |>.2 ] ) _ ) ( by simp +decide ) );
    -- Let $E' = E \setminus S$.
    set E' := E \ S;
    -- By induction, there exists $M' \subseteq E'$ with $2|M'| \ge |E'|$ and disjoint edges.
    obtain ⟨M', hM'_sub, hM'_card, hM'_disjoint⟩ : ∃ M' ⊆ E', 2 * M'.card ≥ E'.card ∧ ∀ p ∈ M', ∀ q ∈ M', p ≠ q → ({p.1, p.2} : Finset α) ∩ ({q.1, q.2} : Finset α) = ∅ := by
      apply ih (E'.card);
      · grind;
      · exact fun p hp q hq hpq => h_right_unique p ( Finset.mem_sdiff.mp hp |>.1 ) q ( Finset.mem_sdiff.mp hq |>.1 ) hpq;
      · exact fun p hp q hq hpq => h_left_unique p ( Finset.mem_sdiff.mp hp |>.1 ) q ( Finset.mem_sdiff.mp hq |>.1 ) hpq;
      · exact fun p hp => h_order p ( Finset.mem_sdiff.mp hp |>.1 );
      · rfl;
    refine' ⟨ Insert.insert e M', _, _, _ ⟩;
    · exact Finset.insert_subset heE ( hM'_sub.trans ( Finset.sdiff_subset ) );
    · grind;
    · grind

/-
Helper Lemma: There exists a difference $m$ that appears at least the average number of times.
-/
theorem exists_frequent_diff (t : ℕ) (ht : 2 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y) :
    ∃ m ∈ Finset.Icc 1 (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩),
    let E := (Finset.univ : Finset (Fin t)).offDiag.filter (fun p => p.1 < p.2 ∧ y p.2 - y p.1 = m)
    2 * E.card * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩) ≥ t * (t - 1) := by
  by_contra h_contra;
  -- Let's calculate the total number of pairs $(i, j)$ such that $i < j$ and $y_j - y_i = m$ for all $m$ in the range.
  have h_total_pairs : ∑ m ∈ Finset.Icc 1 ((y ⟨t - 1, by omega⟩) - (y ⟨0, by omega⟩)), (Finset.card (Finset.filter (fun p => p.1 < p.2 ∧ y p.2 - y p.1 = m) (Finset.offDiag (Finset.univ : Finset (Fin t))))) = (t * (t - 1)) / 2 := by
    rw [ ← Finset.card_biUnion ];
    · rw [ show ( Finset.biUnion ( Finset.Icc 1 ( y ⟨ t - 1, Nat.sub_lt ( by linarith ) ( by linarith ) ⟩ - y ⟨ 0, by linarith ⟩ ) ) fun m => { p ∈ Finset.univ.offDiag | p.1 < p.2 ∧ y p.2 - y p.1 = m } ) = Finset.filter ( fun p : Fin t × Fin t => p.1 < p.2 ) ( Finset.offDiag ( Finset.univ : Finset ( Fin t ) ) ) from ?_ ];
      · convert Finset.card_filter ( fun p : Fin t × Fin t => p.1 < p.2 ) ( Finset.univ : Finset ( Fin t × Fin t ) ) using 1;
        · exact congr_arg Finset.card ( by ext; aesop );
        · erw [ Finset.sum_product ];
          rw [ ← Finset.sum_range_id ];
          simp +decide [Finset.filter_lt_eq_Ioi];
          rw [ ← Finset.sum_range_reflect, Finset.sum_range ];
      · ext ⟨i, j⟩; simp [Finset.mem_biUnion];
        exact fun hij hij' => ⟨ by linarith [ h_mono hij' ], by linarith [ h_mono.monotone ( show i ≥ ⟨ 0, by linarith ⟩ from Nat.zero_le _ ), h_mono.monotone ( show j ≤ ⟨ t - 1, Nat.sub_lt ( by linarith ) ( by linarith ) ⟩ from Nat.le_pred_of_lt ( Fin.is_lt j ) ) ] ⟩;
    · exact fun m hm n hn hmn => Finset.disjoint_left.mpr fun p hp hp' => hmn <| by aesop;
  rcases t with ( _ | _ | t ) <;> norm_num at *;
  · contradiction;
  · contradiction;
  · have h_total_pairs : ∑ m ∈ Finset.Icc 1 ((y ⟨t + 1, by omega⟩) - (y ⟨0, by omega⟩)), (2 * (Finset.card (Finset.filter (fun p => p.1 < p.2 ∧ y p.2 - y p.1 = m) (Finset.offDiag (Finset.univ : Finset (Fin (t + 2)))))) * ((y ⟨t + 1, by omega⟩) - (y ⟨0, by omega⟩))) < ((t + 1 + 1) * (t + 1)) * ((y ⟨t + 1, by omega⟩) - (y ⟨0, by omega⟩)) := by
      refine' lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty _ fun x hx => h_contra x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ) _;
      · exact Finset.nonempty_Icc.mpr ( by linarith! [ h_mono ( show 0 < ⟨ t + 1, by linarith ⟩ from Nat.zero_lt_succ _ ) ] );
      · norm_num [ mul_comm ];
        rw [ max_eq_left ( sub_nonneg.mpr <| h_mono.monotone <| Nat.zero_le _ ) ];
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    norm_cast at * ; simp_all +decide;
    exact h_total_pairs.not_ge ( by rw [ Int.mul_ediv_cancel' ( even_iff_two_dvd.mp ( by simp +arith +decide [ mul_add, parity_simps ] ) ) ] )

/-
Algebraic helper: The polynomial inequality $(2x^3 + 1.01x^2 + 2)(2x^3 + 1.01x^2 + 1) \ge 4x^6 + 4x^5 + 2x^4$ holds for $x \ge 1$.
-/
theorem gces_bound_poly_corrected (x : ℝ) (hx : 1 ≤ x) :
    let f_x := 2 * x^3 + 1.01 * x^2 + 2
    f_x * (f_x - 1) ≥ 4 * x^6 + 4 * x^5 + 2 * x^4 := by
      by_contra h_contra;
      have h_pos : 0 < x - 1 := by
        exact sub_pos_of_lt ( lt_of_le_of_ne hx ( by rintro rfl; norm_num at h_contra ) );
      nlinarith only [ h_contra, h_pos, pow_pos h_pos 3, pow_pos h_pos 4, pow_pos h_pos 5, pow_pos h_pos 6, pow_pos h_pos 7, pow_pos h_pos 8, pow_pos h_pos 9, pow_pos h_pos 10, pow_pos h_pos 11, pow_pos h_pos 12, pow_pos h_pos 13, pow_pos h_pos 14, pow_pos h_pos 15, pow_pos h_pos 16, pow_pos h_pos 17, pow_pos h_pos 18, pow_pos h_pos 19, pow_pos h_pos 20 ]

/-
For $x \ge 1$, $(2x^3 + 1.01x^2 + 2)(2x^3 + 1.01x^2 + 1) \ge 4x^6 + 4x^5 + 2x^4$.
-/
theorem gces_poly_ineq (x : ℝ) (hx : 1 ≤ x) :
    let f_x := 2 * x^3 + 1.01 * x^2 + 2
    f_x * (f_x - 1) ≥ 4 * x^6 + 4 * x^5 + 2 * x^4 := by
      exact gces_bound_poly_corrected x hx

/-
Algebraic inequality for the Golomb ruler bound.
-/
lemma gces_ineq_x (x : ℝ) (hx : 1 ≤ x) (t : ℝ) (ht : t ≥ 2 * x^3 + 1.01 * x^2 + 2) :
    t * (t - 1) / (4 * x^4) ≥ x^2 + x + 1/2 := by
      rw [ ge_iff_le, le_div_iff₀ ] <;> nlinarith [ pow_pos ( zero_lt_one.trans_le hx ) 3, pow_pos ( zero_lt_one.trans_le hx ) 4, pow_pos ( zero_lt_one.trans_le hx ) 5, pow_pos ( zero_lt_one.trans_le hx ) 6, gces_poly_ineq x hx ]

/-
If $Y \ge 1$ and $t \ge 2Y^{3/4} + 1.01Y^{1/2} + 2$, then $\frac{t(t-1)}{4Y} \ge Y^{1/2} + Y^{1/4} + 1/2$.
-/
theorem gces_step1_ineq (t : ℝ) (Y : ℝ) (hY : Y ≥ 1)
    (ht : t ≥ 2 * Y^(0.75 : ℝ) + 1.01 * Y^(0.5 : ℝ) + 2) :
    t * (t - 1) / (4 * Y) ≥ Y^(0.5 : ℝ) + Y^(0.25 : ℝ) + 0.5 := by
      -- Set $x := Y^{0.25}$, so $x \ge 1$ (since $Y \ge 1$). By definition of $x$, $x^4 = Y$.
      set x : ℝ := Y^(1/4 : ℝ)
      have hx_pos : 1 ≤ x := by
        exact Real.one_le_rpow hY ( by norm_num )
      have hx_pow : x^4 = Y := by
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ; linarith;
      -- The hypothesis is $t \ge 2x^3 + 1.01x^2 + 2$.
      have ht_x : t ≥ 2 * x^3 + 1.01 * x^2 + 2 := by
        exact ht.trans' ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num );
      -- Apply `gces_ineq_x` with this $x$ and $t$.
      have h_apply_ineq : t * (t - 1) / (4 * x^4) ≥ x^2 + x + 0.5 := by
        convert gces_ineq_x x hx_pos t ht_x using 1 ; ring;
      convert h_apply_ineq using 1 <;> norm_num [ ← hx_pow ];
      norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity : 0 ≤ x ) ];
      norm_num

/-
There exists a difference $m$ and a matching $M$ of pairs with difference $m$ such that $|M| \ge \frac{t(t-1)}{4(y_{t-1} - y_0)}$.
-/
lemma gces_matching_size_bound (t : ℕ) (ht : 2 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y) :
    ∃ m : ℤ, m > 0 ∧ ∃ M : Finset (Fin t × Fin t),
      (∀ p ∈ M, y p.2 - y p.1 = m) ∧
      (∀ p ∈ M, p.1 < p.2) ∧
      (∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset (Fin t)) ∩ {q.1, q.2} = ∅) ∧
      (M.card : ℝ) ≥ (t * (t - 1) : ℝ) / (4 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)) := by
        obtain ⟨ m, hm ⟩ := exists_frequent_diff t ht y h_mono;
        obtain ⟨M, hM⟩ : ∃ M : Finset (Fin t × Fin t), M ⊆ Finset.filter (fun p => p.1 < p.2 ∧ y p.2 - y p.1 = m) (Finset.offDiag (Finset.univ : Finset (Fin t))) ∧ 2 * M.card ≥ Finset.card (Finset.filter (fun p => p.1 < p.2 ∧ y p.2 - y p.1 = m) (Finset.offDiag (Finset.univ : Finset (Fin t)))) ∧ ∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset (Fin t)) ∩ {q.1, q.2} = ∅ := by
          apply exists_disjoint_pairs;
          · simp +contextual ;
            intros; subst_vars; exact h_mono.injective ( by linarith ) ;
          · simp +contextual ;
            intros; subst_vars; exact h_mono.injective ( by linarith ) ;
          · grind;
        refine' ⟨ m, _, M, _, _, _, _ ⟩ <;> norm_num at *;
        · linarith;
        · exact fun a b hab => Finset.mem_filter.mp ( hM.1 hab ) |>.2.2;
        · exact fun a b hab => Finset.mem_filter.mp ( hM.1 hab ) |>.2.1;
        · exact hM.2.2;
        · rw [ div_le_iff₀ ] <;> norm_cast;
          · rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith;
          · linarith

/-
Definition of a Sidon sequence (proper definition: unique positive differences) and the intersection count function used in the proof.
-/
def IsSidonProper {t : ℕ} (y : Fin t → ℤ) : Prop :=
  ∀ i₁ j₁ i₂ j₂, i₁ < j₁ → i₂ < j₂ → y j₁ - y i₁ = y j₂ - y i₂ → i₁ = i₂ ∧ j₁ = j₂

def count_intersection {t : ℕ} (y : Fin t → ℤ) (T : ℤ) (j : ℤ) : ℕ :=
  (Finset.univ.filter (fun i => j - T ≤ y i ∧ y i < j)).card

/-
The sum of intersection counts is $tT$. Each element $y_i$ contributes to exactly $T$ intervals $[j-T, j)$.
-/
lemma sum_count_intersection {t : ℕ} (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y) (T : ℕ) :
    ∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), count_intersection y T j = t * T := by
      -- By definition of sum_add_distrib, we can rewrite the left-hand side as a double sum.
      have h_double_sum : ∑ x ∈ Finset.Ioc (y ⟨0, by linarith⟩) (y ⟨t - 1, Nat.sub_lt ht zero_lt_one⟩ + T), ∑ i : Fin t, (if x - T ≤ y i ∧ y i < x then 1 else 0) = ∑ i : Fin t, ∑ x ∈ Finset.Ioc (y ⟨0, by linarith⟩) (y ⟨t - 1, Nat.sub_lt ht zero_lt_one⟩ + T), (if x - T ≤ y i ∧ y i < x then 1 else 0) := by
        exact Finset.sum_comm;
      -- For each $i$, the inner sum counts the number of $x$ in the interval $(y_i, y_i + T]$.
      have h_inner_sum : ∀ i : Fin t, ∑ x ∈ Finset.Ioc (y ⟨0, by linarith⟩) (y ⟨t - 1, Nat.sub_lt ht zero_lt_one⟩ + T), (if x - T ≤ y i ∧ y i < x then 1 else 0) = T := by
        intro i
        have h_inner_sum_eq : Finset.filter (fun x => x - T ≤ y i ∧ y i < x) (Finset.Ioc (y ⟨0, by linarith⟩) (y ⟨t - 1, Nat.sub_lt ht zero_lt_one⟩ + T)) = Finset.Ioc (y i) (y i + T) := by
          ext x; simp [Finset.mem_Ioc];
          exact ⟨ fun h => ⟨ h.2.2, h.2.1 ⟩, fun h => ⟨ ⟨ by linarith [ h_mono.monotone ( show ⟨ 0, by linarith ⟩ ≤ i from Nat.zero_le _ ) ], by linarith [ h_mono.monotone ( show i ≤ ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ from Nat.le_pred_of_lt i.2 ) ] ⟩, h.2, h.1 ⟩ ⟩;
        aesop;
      simp_all +decide [ count_intersection ]

/-
The sum of squared intersection counts is at least $(tT)^2 / (y+T)$. This follows from Cauchy-Schwarz inequality.
-/
lemma sum_sq_count_intersection_ge {t : ℕ} (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y) (T : ℕ) (hT : T > 0) :
    (∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j : ℝ)^2) ≥
    (t * T : ℝ)^2 / (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ + T : ℝ) := by
      have h_cauchy_schwarz : (∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩ : ℤ) (y ⟨t - 1, by omega⟩ + T), (count_intersection y T j : ℝ))^2 ≤ (∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩ : ℤ) (y ⟨t - 1, by omega⟩ + T), (count_intersection y T j : ℝ)^2) * (Finset.card (Finset.Ioc (y ⟨0, by omega⟩ : ℤ) (y ⟨t - 1, by omega⟩ + T))) := by
        have h_cauchy_schwarz : ∀ (u v : Finset ℤ) (f g : ℤ → ℝ), (∑ j ∈ u, f j * g j)^2 ≤ (∑ j ∈ u, f j^2) * (∑ j ∈ u, g j^2) := by
          exact fun u v f g => Finset.sum_mul_sq_le_sq_mul_sq u f g;
        simpa [ mul_comm ] using h_cauchy_schwarz ( Finset.Ioc ( y ⟨ 0, by omega ⟩ ) ( y ⟨ t - 1, by omega ⟩ + T ) ) ( Finset.Ioc ( y ⟨ 0, by omega ⟩ ) ( y ⟨ t - 1, by omega ⟩ + T ) ) ( fun j => count_intersection y T j ) fun _ => 1;
      have h_sum_count : (∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩ : ℤ) (y ⟨t - 1, by omega⟩ + T), (count_intersection y T j : ℝ)) = t * T := by
        exact_mod_cast sum_count_intersection ht y h_mono T;
      simp_all +decide;
      rw [ div_le_iff₀ ];
      · convert h_cauchy_schwarz using 2 ; norm_cast ; ring_nf!;
        rw [ Int.toNat_of_nonneg ( by linarith [ h_mono.monotone ( show ⟨ 0, by linarith ⟩ ≤ ⟨ t - 1, Nat.sub_lt ( by linarith ) ( by linarith ) ⟩ from Nat.zero_le _ ) ] ) ];
      · exact add_pos_of_nonneg_of_pos ( sub_nonneg_of_le <| mod_cast h_mono.monotone <| Nat.zero_le _ ) <| Nat.cast_pos.mpr hT

/-
The sum of binomial coefficients $\binom{Y_j}{2}$ equals the sum of $(T - (y_k - y_i))$ over all pairs $(i, k)$ with difference less than $T$.
-/
lemma sum_binom_count_intersection_eq {t : ℕ} (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y) (T : ℕ) (hT : T > 0) :
    ∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j).choose 2 =
    ∑ p ∈ (Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2 ∧ y p.2 - y p.1 < T), (T - (y p.2 - y p.1)) := by
      -- We swap the summation order.
      have h_swap : ∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j).choose 2 =
        ∑ p ∈ Finset.filter (fun p : Fin t × Fin t => p.1 < p.2 ∧ y p.2 - y p.1 < T) (Finset.univ : Finset (Fin t × Fin t)), ∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (if y p.1 ≥ j - T ∧ y p.1 < j ∧ y p.2 ≥ j - T ∧ y p.2 < j then 1 else 0) := by
          rw [ Finset.sum_comm, Finset.sum_congr rfl ];
          intros j hj
          have h_count : count_intersection y T j = Finset.card (Finset.filter (fun i => y i ≥ j - T ∧ y i < j) Finset.univ) := by
            exact congr_arg Finset.card ( Finset.filter_congr fun i _ => by constructor <;> intro hi <;> constructor <;> linarith );
          have h_binom : ∀ (S : Finset (Fin t)), (S.card.choose 2) = Finset.card (Finset.filter (fun p : Fin t × Fin t => p.1 < p.2 ∧ p.1 ∈ S ∧ p.2 ∈ S) (Finset.univ : Finset (Fin t × Fin t))) := by
            intros S
            have h_binom : Finset.card (Finset.filter (fun p : Fin t × Fin t => p.1 < p.2 ∧ p.1 ∈ S ∧ p.2 ∈ S) (Finset.univ : Finset (Fin t × Fin t))) = Finset.card (Finset.powersetCard 2 S) := by
              refine' Finset.card_bij ( fun p hp => { p.1, p.2 } ) _ _ _;
              · grind;
              · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
                grind;
              · simp +zetaDelta at *;
                intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ a, b, hab, rfl ⟩ := hb'; cases lt_trichotomy a b <;> aesop;
            rw [ h_binom, Finset.card_powersetCard ];
          simp_all +decide;
          congr 1 with p ; simp +contextual [ and_assoc, and_left_comm, and_comm ];
          intros; linarith;
      -- The inner sum counts the number of $j$ such that $j-T \le y_{p.1} < y_{p.2} < j$.
      have h_inner : ∀ p : Fin t × Fin t, p.1 < p.2 ∧ y p.2 - y p.1 < T → ∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (if y p.1 ≥ j - T ∧ y p.1 < j ∧ y p.2 ≥ j - T ∧ y p.2 < j then 1 else 0) = T - (y p.2 - y p.1) := by
        intro p hp
        have h_interval : Finset.filter (fun j => y p.1 ≥ j - T ∧ y p.1 < j ∧ y p.2 ≥ j - T ∧ y p.2 < j) (Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T)) = Finset.Ioc (y p.2) (y p.1 + T) := by
          ext j; simp;
          constructor <;> intro hj <;> constructor <;> try linarith;
          · exact ⟨ lt_of_le_of_lt ( h_mono.monotone ( Nat.zero_le _ ) ) ( lt_of_le_of_lt ( h_mono.monotone hp.1.le ) hj.1 ), le_trans hj.2 ( add_le_add_right ( h_mono.monotone ( Nat.le_sub_one_of_lt ( Fin.is_lt _ ) ) ) _ ) ⟩;
          · exact ⟨ hj.2, by linarith [ h_mono hp.1 ], by linarith [ h_mono hp.1 ], hj.1 ⟩;
        simp_all +decide;
        rw [ max_eq_left ] <;> linarith [ h_mono hp.1 ];
      rw [ h_swap, Nat.cast_sum, Finset.sum_congr rfl ] ; aesop

/-
The sum of binomial coefficients is at most $T(T-1)/2$ for a Sidon set. This uses the fact that differences are unique.
-/
lemma sum_binom_count_intersection_le {t : ℕ} (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y) (T : ℕ) (hT : T > 0)
    (h_sidon : IsSidonProper y) :
    ∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j).choose 2 ≤ T * (T - 1) / 2 := by
      -- By `sum_binom_count_intersection_eq`, the LHS is equal to $\sum_{p \in S} (T - (y_{p.2} - y_{p.1}))$, where $S$ is the set of pairs with difference $< T$.
      have h_sum_eq : ∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j).choose 2 = ∑ p ∈ (Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2 ∧ y p.2 - y p.1 < T), (T - (y p.2 - y p.1)) := by
        convert sum_binom_count_intersection_eq ht y h_mono T hT using 1;
      -- Since $y$ is strictly monotone, $y_{p.2} - y_{p.1} \ge 1$ for $p.1 < p.2$.
      have h_diff_ge_one : ∀ p : Fin t × Fin t, p.1 < p.2 → 1 ≤ y p.2 - y p.1 := by
        exact fun p hp => by linarith [ h_mono hp ] ;
      -- Since $y$ is strictly monotone, the map $p \mapsto y_{p.2} - y_{p.1}$ is injective.
      have h_inj : ∀ p q : Fin t × Fin t, p.1 < p.2 → q.1 < q.2 → y p.2 - y p.1 = y q.2 - y q.1 → p = q := by
        exact fun p q hp hq h => Prod.ext ( h_sidon _ _ _ _ hp hq h |>.1 ) ( h_sidon _ _ _ _ hp hq h |>.2 );
      -- Let $U = \{1, \dots, T-1\}$.
      set U : Finset ℤ := Finset.Ico 1 T;
      -- Since $x_p \in U$ for all $p \in S$, we can bound the sum by the sum over $U$.
      have h_sum_le_sum_U : ∑ p ∈ (Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2 ∧ y p.2 - y p.1 < T), (T - (y p.2 - y p.1)) ≤ ∑ x ∈ U, (T - x) := by
        have h_sum_le_sum_U : ∑ p ∈ (Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2 ∧ y p.2 - y p.1 < T), (T - (y p.2 - y p.1)) ≤ ∑ x ∈ Finset.image (fun p => y p.2 - y p.1) ((Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2 ∧ y p.2 - y p.1 < T)), (T - x) := by
          rw [ Finset.sum_image ];
          exact fun p hp q hq h => h_inj p q ( Finset.mem_filter.mp hp |>.2.1 ) ( Finset.mem_filter.mp hq |>.2.1 ) h;
        exact h_sum_le_sum_U.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.image_subset_iff.mpr fun p hp => Finset.mem_Ico.mpr ⟨ by linarith [ h_diff_ge_one p ( Finset.mem_filter.mp hp |>.2.1 ) ], by linarith [ Finset.mem_filter.mp hp |>.2.2 ] ⟩ ) fun x hx _ => sub_nonneg.mpr <| by linarith [ Finset.mem_Ico.mp hx ] );
      -- The sum $\sum_{x=1}^{T-1} (T - x)$ is equal to $\frac{(T-1)T}{2}$.
      have h_sum_U : ∑ x ∈ U, (T - x) = (T * (T - 1)) / 2 := by
        have h_sum_U : ∑ x ∈ Finset.range (T - 1), (T - (x + 1)) = (T * (T - 1)) / 2 := by
          convert Finset.sum_range_id T using 1;
          rw [ ← Finset.sum_range_reflect ];
          cases T <;> simp +arith +decide [ Finset.sum_range_succ' ];
          exact Finset.sum_congr rfl fun x hx => by rw [ tsub_tsub, tsub_tsub_cancel_of_le ] <;> linarith [ Finset.mem_range.mp hx ] ;
        convert congr_arg Int.ofNat h_sum_U using 1;
        · simp +zetaDelta at *;
          refine' Finset.sum_bij ( fun x hx => Int.toNat ( x - 1 ) ) _ _ _ _ <;> norm_num;
          · intro a ha₁ ha₂; omega;
          · intro a₁ ha₁ ha₁' a₂ ha₂ ha₂' h; omega;
          · exact fun b hb => ⟨ b + 1, ⟨ by linarith, by linarith [ Nat.sub_add_cancel hT ] ⟩, by norm_num ⟩;
          · omega;
        · cases T <;> norm_num;
      norm_num +zetaDelta at *;
      rw [ ← @Nat.cast_le ℤ ] ; aesop

/-
Inequality for the range $y$ of a Sidon set in terms of $t$ and a parameter $T$.
-/
lemma sidon_ineq_y {t : ℕ} (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y) (T : ℕ) (hT : T > 0)
    (h_sidon : IsSidonProper y) :
    (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ) ≥ (t^2 * T : ℝ) / (T + t - 1) - T := by
      have h_combined : (t * T : ℝ)^2 / (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ + T) - (t * T : ℝ) ≤ T * (T - 1) := by
        have h_combined : (∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j : ℝ)^2) - (∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j : ℝ)) ≤ T * (T - 1) := by
          have h_combined : (∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j : ℝ)^2 - ∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j : ℝ)) = 2 * (∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j).choose 2 : ℝ) := by
            rw [ Finset.mul_sum _ _ _ ];
            rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; induction' count_intersection y T x with k hk <;> norm_num [ Nat.choose ] at * ; nlinarith;
          have h_combined : (∑ j ∈ Finset.Ioc (y ⟨0, by omega⟩) (y ⟨t-1, by omega⟩ + T), (count_intersection y T j).choose 2 : ℝ) ≤ T * (T - 1) / 2 := by
            convert sum_binom_count_intersection_le ht y h_mono T hT h_sidon using 1;
            rw [ ← @Nat.cast_le ℝ ] ; norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ];
            cases T <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ];
          linarith;
        refine le_trans ?_ h_combined;
        gcongr;
        · convert sum_sq_count_intersection_ge ht y h_mono T hT using 1;
        · convert sum_count_intersection ht y h_mono T using 1;
          norm_cast;
          exact ⟨ fun h => le_antisymm h ( by simpa using sum_count_intersection ht y h_mono T |> Eq.ge ), fun h => h.le ⟩;
      rw [ div_sub', div_le_iff₀ ] at h_combined <;> norm_num at *;
      · rw [ div_le_iff₀ ] <;> nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ t ), ( by norm_cast : ( 1 : ℝ ) ≤ T ) ];
      · exact add_pos_of_nonneg_of_pos ( sub_nonneg_of_le <| mod_cast h_mono.monotone <| Nat.zero_le _ ) <| Nat.cast_pos.mpr hT;
      · exact ne_of_gt ( add_pos_of_nonneg_of_pos ( sub_nonneg_of_le ( mod_cast h_mono.monotone ( Nat.zero_le _ ) ) ) ( Nat.cast_pos.mpr hT ) )

/-
Lemma 1: The inequality $y < f(y^{1/2} + y^{1/4} + 1/2)$ holds for $y \ge 1$. (Corrected with decimal exponents)
-/
lemma lemma_algebra (y : ℝ) (hy : y ≥ 1) :
    y < (y^(0.5 : ℝ) + y^(0.25 : ℝ) + 0.5)^2 - 2 * (y^(0.5 : ℝ) + y^(0.25 : ℝ) + 0.5)^(1.5 : ℝ) + (y^(0.5 : ℝ) + y^(0.25 : ℝ) + 0.5) + (y^(0.5 : ℝ) + y^(0.25 : ℝ) + 0.5)^(0.5 : ℝ) - 1 := by
      rw [ show ( 1.5 : ℝ ) = 1 + 0.5 by norm_num, Real.rpow_add ] <;> norm_num;
      · norm_num [ ← Real.sqrt_eq_rpow ];
        -- Let $z = y^{1/4}$, so $y = z^4$.
        set z : ℝ := y ^ (1 / 4 : ℝ)
        have hyz : y = z ^ 4 := by
          rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ; linarith;
        rw [ hyz ];
        rw [ show z ^ 4 = ( z ^ 2 ) ^ 2 by ring, Real.sqrt_sq ( by positivity ) ];
        nlinarith only [ show 1 ≤ z by exact Real.one_le_rpow hy ( by norm_num ), sq_nonneg ( z - 1 ), Real.sqrt_nonneg ( z ^ 2 + z + 1 / 2 ), Real.mul_self_sqrt ( show 0 ≤ z ^ 2 + z + 1 / 2 by positivity ) ];
      · positivity

/-
The function $h(x) = x^2 - 2x^{1.5} + x + x^{0.5} - 1$ is strictly monotone for $x \ge 1$.
-/
noncomputable def h_sidon (x : ℝ) : ℝ := x^2 - 2 * x^(1.5 : ℝ) + x + x^(0.5 : ℝ) - 1

lemma h_sidon_strict_mono : StrictMonoOn h_sidon (Set.Ici 1) := by
  -- To prove strict monotonicity, we can take the derivative of $h(x)$ and show it is positive for $x > 1$.
  have h_deriv_pos : ∀ x > 1, deriv h_sidon x > 0 := by
    unfold h_sidon;
    intro x hx; norm_num [ show x ≠ 0 by linarith ] ; ring_nf; norm_num [ hx ] ;
    rw [ Real.rpow_neg ( by linarith ) ] ; norm_num [ ← Real.sqrt_eq_rpow ] ; nlinarith [ sq_nonneg ( Real.sqrt x - 1 ), Real.sqrt_nonneg x, Real.sq_sqrt ( by linarith : 0 ≤ x ), inv_mul_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( by linarith : 0 < x ) ) ) ] ;
  -- Apply the fact that if the derivative of a function is positive on an interval, then the function is strictly increasing on that interval.
  apply strictMonoOn_of_deriv_pos;
  · exact convex_Ici _;
  · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.add ( ContinuousAt.add ( ContinuousAt.add ( ContinuousAt.sub ( continuousAt_id.pow 2 ) ( ContinuousAt.mul continuousAt_const ( continuousAt_id.rpow_const <| by norm_num ) ) ) continuousAt_id ) ( continuousAt_id.rpow_const <| by norm_num ) ) continuousAt_const;
  · aesop

/-
Step 2 of Sidon bound: $y \ge t^2 - 2t^{1.5} + t + t^{0.5} - 1$. This uses the optimal choice of $T$.
-/
lemma sidon_bound_step2 (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y)
    (h_sidon : IsSidonProper y) :
    (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ) ≥ (t : ℝ)^2 - 2 * (t : ℝ)^(1.5 : ℝ) + (t : ℝ) + (t : ℝ)^(0.5 : ℝ) - 1 := by
      -- Applying the inequality `sidon_ineq_y` with $T = \lfloor t^{1.5} - t \rfloor + 1$.
      have h_ineq : (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ) ≥ (t^2 * (⌊(t : ℝ)^(3/2 : ℝ) - t⌋₊ + 1) : ℝ) / ((⌊(t : ℝ)^(3/2 : ℝ) - t⌋₊ + 1) + t - 1) - (⌊(t : ℝ)^(3/2 : ℝ) - t⌋₊ + 1) := by
        have := sidon_ineq_y ht y h_mono ( ⌊ ( t : ℝ ) ^ ( 3 / 2 : ℝ ) - t⌋₊ + 1 ) ?_ h_sidon <;> aesop;
      -- Let $\epsilon = T - (t^{1.5} - t)$. Then $\epsilon \in (0, 1]$.
      set ε : ℝ := (⌊(t : ℝ)^(3/2 : ℝ) - t⌋₊ + 1) - ((t : ℝ)^(3/2 : ℝ) - t)
      have hε_pos : 0 < ε := by
        exact sub_pos_of_lt ( Nat.lt_floor_add_one _ )
      have hε_le_one : ε ≤ 1 := by
        exact sub_le_iff_le_add'.mpr <| by linarith [ Nat.floor_le <| show 0 ≤ ( t : ℝ ) ^ ( 3 / 2 : ℝ ) - t by exact sub_nonneg_of_le <| by exact le_trans ( by norm_num ) <| Real.rpow_le_rpow_of_exponent_le ( mod_cast ht ) <| show ( 3 : ℝ ) / 2 ≥ 1 by norm_num ] ;
      -- Substitute $T = t^{1.5} - t + \epsilon$ into the inequality.
      have h_subst : (t^2 * (t^(3/2 : ℝ) - t + ε) : ℝ) / ((t^(3/2 : ℝ) - t + ε) + t - 1) - (t^(3/2 : ℝ) - t + ε) ≥ t^2 - 2 * t^(3/2 : ℝ) + t + t^(1/2 : ℝ) - 1 := by
        rw [ ge_iff_le, le_sub_iff_add_le, le_div_iff₀ ];
        · rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add' ] <;> norm_num ; ring_nf ; norm_num;
          rw [ ← Real.sqrt_eq_rpow ];
          rw [ Real.sq_sqrt ( Nat.cast_nonneg _ ) ] ; nlinarith [ show ( t : ℝ ) ≥ 1 by norm_cast, Real.sqrt_nonneg t, Real.sq_sqrt ( Nat.cast_nonneg t ), mul_le_mul_of_nonneg_left hε_le_one <| Real.sqrt_nonneg t ];
        · linarith [ show ( t : ℝ ) ≥ 1 by norm_cast ];
      norm_num +zetaDelta at *;
      linarith

/-
The Sidon bound: $t < y^{1/2} + y^{1/4} + 1/2$, assuming $y \ge 1$.
-/
lemma sidon_bound_proper (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y)
    (h_sidon : IsSidonProper y) (h_y_ge_1 : y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ ≥ 1) :
    (t : ℝ) < (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.5 : ℝ) + (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.25 : ℝ) + 0.5 := by
      -- By contradiction, assume $t \ge x$.
      by_contra h_contra;
      -- Let $x = (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ) ^ (0.5 : ℝ) + (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ) ^ (0.25 : ℝ) + 0.5$.
      set x : ℝ := (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ) ^ (0.5 : ℝ) + (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ) ^ (0.25 : ℝ) + 0.5;
      -- Since $t \ge x > 1$, we have $h(t) \ge h(x)$.
      have h_h_t_ge_h_x : (t : ℝ)^2 - 2 * (t : ℝ)^(1.5 : ℝ) + (t : ℝ) + (t : ℝ)^(0.5 : ℝ) - 1 ≥ x^2 - 2 * x^(1.5 : ℝ) + x + x^(0.5 : ℝ) - 1 := by
        have h_h_t_ge_h_x : StrictMonoOn (fun x : ℝ => x^2 - 2 * x^(1.5 : ℝ) + x + x^(0.5 : ℝ) - 1) (Set.Ici 1) := by
          convert h_sidon_strict_mono using 1;
        refine' h_h_t_ge_h_x.le_iff_le _ _ |>.2 ( le_of_not_gt h_contra ) <;> norm_num at *;
        · exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( Real.one_le_rpow ( mod_cast h_y_ge_1 ) ( by norm_num ) ) ( Real.rpow_nonneg ( mod_cast h_y_ge_1.trans' ( by norm_num ) ) _ ) ) ( by norm_num );
        · linarith;
      -- By `lemma_algebra`, $Y < h(x)$.
      have h_Y_lt_h_x : (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ) < x^2 - 2 * x^(1.5 : ℝ) + x + x^(0.5 : ℝ) - 1 := by
        convert lemma_algebra _ _ using 1;
        exact_mod_cast h_y_ge_1;
      linarith [ sidon_bound_step2 t ht y h_mono h_sidon ]

/-
Stronger version of Golomb's lemma: If $t \ge y^{1/2} + y^{1/4} + \frac{1}{2}$ and $y \ge 1$, then there exist non-zero integers $x_2, x_3$ and integer $x_1$ such that the sequence contains all subset sums containing $x_1$.
-/
theorem golomb_nonzero (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y)
    (h_y_ge_1 : y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ ≥ 1)
    (h_bound : (t : ℝ) ≥ (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.5 : ℝ) + (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.25 : ℝ) + 0.5) :
    ∃ x₁ x₂ x₃, x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₂ ≠ x₃ ∧ {x₁, x₁ + x₂, x₁ + x₃, x₁ + x₂ + x₃} ⊆ Set.range y := by
      have h_non_sidon : ¬ IsSidonProper y := by
        contrapose! h_bound; have := sidon_bound_proper t ht y h_mono; aesop;
      generalize_proofs at *; (
      -- By definition of `IsSidonProper`, there exist indices `i1`, `j1`, `i2`, `j2` such that `i1 < j1`, `i2 < j2`, `y j1 - y i1 = y j2 - y i2`, and `(i1, j1) ≠ (i2, j2)`.
      obtain ⟨i1, j1, i2, j2, hij1, hij2, h_eq, h_ne⟩ : ∃ i1 j1 i2 j2 : Fin t, i1 < j1 ∧ i2 < j2 ∧ y j1 - y i1 = y j2 - y i2 ∧ (i1, j1) ≠ (i2, j2) := by
        contrapose! h_non_sidon; aesop;
      by_cases h_cases : i1 < i2;
      · use y i2, y i1 - y i2, y j2 - y i2; simp_all +decide [ Set.insert_subset_iff ] ;
        exact ⟨ by linarith [ h_mono h_cases ], by linarith [ h_mono hij2 ], by linarith [ h_mono h_cases, h_mono hij1, h_mono hij2 ], j1, by linarith ⟩;
      · by_cases h_cases : i1 > i2;
        · use y i1, y i2 - y i1, y j1 - y i1;
          simp_all +decide [ Set.insert_subset_iff, h_mono.injective.eq_iff ];
          exact ⟨ by linarith [ h_mono h_cases ], by linarith [ h_mono hij2 ], by linarith [ h_mono h_cases, h_mono hij1 ], j1, by linarith ⟩;
        · cases lt_or_eq_of_le ( le_of_not_gt h_cases ) <;> simp_all +decide [ h_mono.injective.eq_iff ])

/-
Stronger version of Lemma 4 with non-zero increments.
-/
theorem gces_nonzero (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y)
    (h_bound : (t : ℝ) ≥ 2 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.75 : ℝ) + 1.01 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.5 : ℝ) + 2)
    (h_y_ge_1 : y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ ≥ 1) :
    ∃ x₁ x₂ x₃ x₄, x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₄ ≠ 0 ∧ x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₃ ≠ x₄ ∧
    {x₁, x₁ + x₂, x₁ + x₃, x₁ + x₄, x₁ + x₂ + x₃, x₁ + x₂ + x₄, x₁ + x₃ + x₄, x₁ + x₂ + x₃ + x₄} ⊆ Set.range y := by
      -- By `gces_matching_size_bound`, there exists a difference $m$ and a matching $M$ of pairs with difference $m$ such that $|M| \ge \frac{t(t-1)}{4(y_{t-1} - y_0)}$.
      obtain ⟨m, M, hm_pos, hM⟩ : ∃ m : ℤ, m > 0 ∧ ∃ M : Finset (Fin t × Fin t), (∀ p ∈ M, y p.2 - y p.1 = m) ∧ (∀ p ∈ M, p.1 < p.2) ∧ (∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset (Fin t)) ∩ {q.1, q.2} = ∅) ∧ (M.card : ℝ) ≥ (t * (t - 1) : ℝ) / (4 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)) := by
        convert gces_matching_size_bound t ( show 2 ≤ t from ?_ ) y h_mono using 1;
        contrapose! h_bound; interval_cases t ; norm_num at *;
      have hM_card : (hm_pos.card : ℝ) ≥ (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.5 : ℝ) + (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.25 : ℝ) + 0.5 := by
        refine le_trans ?_ hM.2.2.2;
        convert gces_step1_ineq t ( y ⟨ t - 1, Nat.sub_lt ( by linarith ) ( by linarith ) ⟩ - y ⟨ 0, Nat.zero_lt_of_lt ht ⟩ ) ( mod_cast h_y_ge_1 ) h_bound using 1;
      -- Let $z$ be the subsequence of $y$ corresponding to the first elements of pairs in $M$.
      obtain ⟨z, hz⟩ : ∃ z : Fin hm_pos.card → ℤ, (∀ i, z i ∈ Set.range y) ∧ StrictMono z ∧ (∀ i, z i + m ∈ Set.range y) ∧ (∀ i j, i ≠ j → z i + m ≠ z j) := by
        -- Let $z$ be the subsequence of $y$ corresponding to the first elements of pairs in $M$. Since $M$ is a matching, these elements are distinct.
        obtain ⟨z, hz⟩ : ∃ z : Fin hm_pos.card → Fin t, (∀ i, z i ∈ Finset.image Prod.fst hm_pos) ∧ StrictMono (fun i => y (z i)) := by
          have hz : Finset.card (Finset.image Prod.fst hm_pos) = hm_pos.card := by
            rw [ Finset.card_image_of_injOn ];
            intro p hp q hq; specialize hM; have := hM.2.2.1 p hp q hq; simp_all +decide [ Finset.ext_iff ] ;
            grind;
          have hz : ∃ z : Fin hm_pos.card → Fin t, (∀ i, z i ∈ Finset.image Prod.fst hm_pos) ∧ StrictMono z := by
            exact ⟨ fun i => Finset.orderEmbOfFin _ ( by aesop ) i, fun i => Finset.orderEmbOfFin_mem _ ( by aesop ) _, by simp +decide [ StrictMono ] ⟩;
          exact ⟨ hz.choose, hz.choose_spec.1, h_mono.comp hz.choose_spec.2 ⟩;
        use fun i => y (z i);
        simp_all +decide [ Finset.ext_iff ];
        constructor;
        · exact fun i => by obtain ⟨ x, hx ⟩ := hz.1 i; exact ⟨ x, by linarith [ hM.1 _ _ hx ] ⟩ ;
        · intro i j hij H; have := hM.1 _ _ ( hz.1 i |> Classical.choose_spec ) ; have := hM.1 _ _ ( hz.1 j |> Classical.choose_spec ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
          have := hM.2.2.1 ( z i ) ( Classical.choose ( hz.1 i ) ) ( Classical.choose_spec ( hz.1 i ) ) ( z j ) ( Classical.choose ( hz.1 j ) ) ( Classical.choose_spec ( hz.1 j ) ) ; simp_all +decide [ add_comm, h_mono.injective.eq_iff ] ;
      obtain ⟨x₁, x₂, x₃, hx₂, hx₃, hx₄, hx₁⟩ : ∃ x₁ x₂ x₃ : ℤ, x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₂ ≠ x₃ ∧ {x₁, x₁ + x₂, x₁ + x₃, x₁ + x₂ + x₃} ⊆ Set.range z := by
        have hz_card : (hm_pos.card : ℝ) ≥ (z ⟨hm_pos.card - 1, by
          rcases hm_pos.eq_empty_or_nonempty with ( rfl | ⟨ p, hp ⟩ ) <;> norm_num at *;
          · exact hM_card.not_gt ( by exact add_pos_of_nonneg_of_pos ( add_nonneg ( Real.rpow_nonneg ( by norm_cast; linarith ) _ ) ( Real.rpow_nonneg ( by norm_cast; linarith ) _ ) ) ( by norm_num ) );
          · exact ⟨ p, hp ⟩⟩ - z ⟨0, by
          exact Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at *; linarith [ Real.rpow_pos_of_pos ( show 0 < ( y ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ - y ⟨ 0, by linarith ⟩ : ℝ ) by exact_mod_cast h_y_ge_1.trans_lt' zero_lt_one ) ( 0.5 : ℝ ), Real.rpow_pos_of_pos ( show 0 < ( y ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ - y ⟨ 0, by linarith ⟩ : ℝ ) by exact_mod_cast h_y_ge_1.trans_lt' zero_lt_one ) ( 0.25 : ℝ ) ] )⟩ : ℝ)^(0.5 : ℝ) + (z ⟨hm_pos.card - 1, by
          rcases hm_pos.eq_empty_or_nonempty with ( rfl | ⟨ p, hp ⟩ ) <;> norm_num at *;
          · exact hM_card.not_gt ( by exact add_pos_of_nonneg_of_pos ( add_nonneg ( Real.rpow_nonneg ( by norm_cast; linarith ) _ ) ( Real.rpow_nonneg ( by norm_cast; linarith ) _ ) ) ( by norm_num ) );
          · exact ⟨ p, hp ⟩⟩ - z ⟨0, by
          exact Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at *; linarith [ Real.rpow_pos_of_pos ( show 0 < ( y ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ - y ⟨ 0, by linarith ⟩ : ℝ ) by exact_mod_cast h_y_ge_1.trans_lt' zero_lt_one ) ( 0.5 : ℝ ), Real.rpow_pos_of_pos ( show 0 < ( y ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ - y ⟨ 0, by linarith ⟩ : ℝ ) by exact_mod_cast h_y_ge_1.trans_lt' zero_lt_one ) ( 0.25 : ℝ ) ] )⟩ : ℝ)^(0.25 : ℝ) + 0.5 := by
          all_goals generalize_proofs at *;
          have hz_card : (z ⟨hm_pos.card - 1, by
            (expose_names; exact pf_4)⟩ - z ⟨0, by
            linarith⟩ : ℝ) ≤ (y ⟨t - 1, by
            (expose_names; exact pf_1)⟩ - y ⟨0, by
            grind⟩ : ℝ) := by
            have hz_bounds : ∀ i, z i ∈ Set.range y := by
              exact hz.1
            generalize_proofs at *;
            norm_cast;
            obtain ⟨ i, hi ⟩ := hz_bounds ⟨ hm_pos.card - 1, by assumption ⟩ ; obtain ⟨ j, hj ⟩ := hz_bounds ⟨ 0, by assumption ⟩ ; exact sub_le_sub ( hi.symm ▸ h_mono.monotone ( Nat.le_sub_one_of_lt ( Fin.is_lt _ ) ) ) ( hj.symm ▸ h_mono.monotone ( Nat.zero_le _ ) ) ;
          generalize_proofs at *;
          refine le_trans ?_ hM_card;
          gcongr;
          · exact sub_nonneg_of_le <| mod_cast hz.2.1.monotone <| Nat.zero_le _;
          · exact sub_nonneg_of_le <| mod_cast hz.2.1.monotone <| Nat.zero_le _
        generalize_proofs at *;
        by_cases hz_ge_1 : z ⟨hm_pos.card - 1, by
          (expose_names; exact pf_4)⟩ - z ⟨0, by
          linarith⟩ ≥ 1
        generalize_proofs at *
        all_goals generalize_proofs at *;
        · exact golomb_nonzero _ ( by linarith ) _ hz.2.1 hz_ge_1 hz_card;
        · contrapose! hz_ge_1;
          refine' Int.le_of_lt_add_one _;
          norm_num [ hz.2.1.lt_iff_lt ];
          rcases hm_pos_card : hm_pos.card with ( _ | _ | k ) <;> simp_all +decide;
          · grind;
          · exact hM_card.not_gt ( by exact lt_add_of_le_of_pos ( le_add_of_le_of_nonneg ( Real.one_le_rpow ( by linarith [ show ( y ⟨ t - 1, by omega ⟩ : ℝ ) - y ⟨ 0, by omega ⟩ ≥ 1 by exact_mod_cast h_y_ge_1 ] ) ( by norm_num ) ) ( Real.rpow_nonneg ( by linarith [ show ( y ⟨ t - 1, by omega ⟩ : ℝ ) - y ⟨ 0, by omega ⟩ ≥ 1 by exact_mod_cast h_y_ge_1 ] ) _ ) ) ( by norm_num ) );
      use x₁, x₂, x₃, m;
      simp_all +decide [ Set.insert_subset_iff ];
      rcases hx₁ with ⟨ ⟨ i, rfl ⟩, ⟨ j, hj ⟩, ⟨ k, hk ⟩, ⟨ l, hl ⟩ ⟩ ; simp_all +decide ;
      refine' ⟨ by linarith, _, _, _, _, _, _ ⟩;
      grind +ring;
      · grind;
      · exact hj ▸ hz.1 j;
      · exact ⟨ _, by rw [ ← hk, hz.1 k |> Classical.choose_spec ] ⟩;
      · exact hl ▸ hz.1 l;
      · exact ⟨ by obtain ⟨ y_1, hy_1 ⟩ := hz.2.2.1 j; exact ⟨ y_1, by linarith ⟩, by obtain ⟨ y_1, hy_1 ⟩ := hz.2.2.1 k; exact ⟨ y_1, by linarith ⟩, by obtain ⟨ y_1, hy_1 ⟩ := hz.2.2.1 l; exact ⟨ y_1, by linarith ⟩ ⟩

/-
Lemma 5: If the sequence consists of even integers, we can find distinct $b_1, b_2, b_3, b_4$ such that all pairwise sums are in the sequence.
-/
theorem corro (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y)
    (h_even : ∀ i, Even (y i))
    (h_bound : (t : ℝ) ≥ 2 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.75 : ℝ) + 1.01 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.5 : ℝ) + 2) :
    ∃ b₁ b₂ b₃ b₄,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₃ ≠ b₄ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₂ + b₃, b₂ + b₄, b₃ + b₄} ⊆ Set.range y := by
        by_cases h_y_ge_1 : 1 ≤ y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩;
        · have := gces_nonzero t ht y h_mono h_bound h_y_ge_1;
          obtain ⟨ x₁, x₂, x₃, x₄, h₂, h₃, h₄, h₅, h₆, h₇, h₈ ⟩ := this; use x₁ / 2, x₁ / 2 + x₂, x₁ / 2 + x₃, x₁ / 2 + x₄; simp_all +decide [ Set.subset_def ] ;
          grind;
        · rcases t with ( _ | _ | t ) <;> norm_num at *;
          linarith [ h_mono ( show 0 < ⟨ t + 1, by linarith ⟩ from Nat.succ_pos _ ) ]

/-
Lemma 6: The inequality $1016 + (y-2)/8 \ge 2y^{0.75} + 1.01y^{0.5} + 2$ holds for $y \ge 1$.
-/
lemma ybound (y : ℝ) (hy : y ≥ 1) :
    let C_4 := 2032
    (C_4 : ℝ) / 2 + (y - 2) / 8 ≥ 2 * y^(0.75 : ℝ) + 1.01 * y^(0.5 : ℝ) + 2 := by
      -- Let $z = y^{1/4}$. Then $y = z^4$, $y^{1/2} = z^2$, and $y^{3/4} = z^3$.
      set z : ℝ := y^(1/4 : ℝ)
      have yz : y = z^4 := by
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ; linarith
      have yz2 : y^(1/2 : ℝ) = z^2 := by
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num
      have yz3 : y^(3/4 : ℝ) = z^3 := by
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num;
      nlinarith [ sq_nonneg ( ( y ^ ( 1 / 4 : ℝ ) ) ^ 2 - 152 ), sq_nonneg ( ( y ^ ( 1 / 4 : ℝ ) ) - 12 ), show ( y ^ ( 1 / 4 : ℝ ) ) ≥ 1 by exact Real.one_le_rpow hy ( by norm_num ) ]

lemma upper_case_1_helper (d : ℕ) (A : Finset ℤ) (Y : Finset ℤ)
    (hY_subset : Y ⊆ A)
    (hY_even : ∀ y ∈ Y, Even y)
    (hY_card : (Y.card : ℝ) ≥ 1016 + (d : ℝ) / 2)
    (hY_range : ∃ a, Y ⊆ Finset.Icc a (a + 4 * d)) :
    ∃ b₁ b₂ b₃ b₄ : ℤ,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₃ ≠ b₄ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₂ + b₃, b₂ + b₄, b₃ + b₄} ⊆ A := by
        -- By `ybound`, this implies the condition for `corro`.
        have h_bound : (Y.card : ℝ) ≥ (2 * (4 * d : ℝ)^(0.75 : ℝ) + 1.01 * (4 * d : ℝ)^(0.5 : ℝ) + 2) := by
          -- Apply the `ybound` lemma with $y = 4d$.
          have h_ybound : (2032 : ℝ) / 2 + (4 * d - 2) / 8 ≥ 2 * (4 * d : ℝ)^(0.75 : ℝ) + 1.01 * (4 * d : ℝ)^(0.5 : ℝ) + 2 := by
            by_cases hd : d = 0;
            · subst hd; norm_num;
            · have := ybound ( 4 * d ) ( by norm_cast; linarith [ Nat.pos_of_ne_zero hd ] ) ; norm_num at * ; linarith;
          linarith;
        -- By `corro`, there exist distinct integers $b_1, b_2, b_3, b_4$ such that all their pairwise sums are in $Y$, and thus in $A$.
        obtain ⟨y, hy_mono, hy_even, hy_subset⟩ : ∃ y : Fin Y.card → ℤ, StrictMono y ∧ (∀ i, y i ∈ Y) ∧ (∀ i, Even (y i)) := by
          exact ⟨ fun i => Y.orderEmbOfFin rfl i, by simp +decide [ StrictMono ], fun i => Y.orderEmbOfFin_mem rfl _, fun i => hY_even _ <| Y.orderEmbOfFin_mem rfl _ ⟩;
        have := corro Y.card (by
        exact_mod_cast ( by linarith [ show ( 0 : ℝ ) ≤ d by positivity ] : ( 0 : ℝ ) < Y.card )) y hy_mono hy_subset (by
        all_goals generalize_proofs at *;
        refine le_trans ?_ h_bound;
        gcongr <;> norm_cast;
        · exact sub_nonneg_of_le <| hy_mono.monotone <| Nat.zero_le _;
        · obtain ⟨ a, ha ⟩ := hY_range; have := ha ( hy_even ⟨ Y.card - 1, by omega ⟩ ) ; have := ha ( hy_even ⟨ 0, by omega ⟩ ) ; norm_num at * ; linarith;
        · exact sub_nonneg_of_le <| hy_mono.monotone <| Nat.zero_le _;
        · obtain ⟨ a, ha ⟩ := hY_range; have := ha ( hy_even ⟨ Y.card - 1, by omega ⟩ ) ; have := ha ( hy_even ⟨ 0, by omega ⟩ ) ; norm_num at * ; linarith;);
        simp_all +decide [ Set.subset_def ];
        rcases this with ⟨ b₁, b₂, hne, x, hne', x', hne'', hne''', hne'''', hne''''', ⟨ y₁, hy₁ ⟩, ⟨ y₂, hy₂ ⟩, ⟨ y₃, hy₃ ⟩, ⟨ y₄, hy₄ ⟩, ⟨ y₅, hy₅ ⟩, ⟨ y₆, hy₆ ⟩ ⟩ ; use b₁, b₂, hne, x, hne', x' ; simp_all +decide ;
        grind

/-
The number of odd integers in $[m-4d-2, m-1]$ is $2d+1$.
-/
lemma count_odd_pairs_lemma (m : ℤ) (d : ℕ) :
    ((Finset.Icc (m - 4 * d - 2) (m - 1)).filter Odd).card = 2 * d + 1 := by
      -- Let's count the number of odd integers in the interval [m-4d-2, m-1].
      have h_count : Finset.card (Finset.filter Odd (Finset.Icc (m - 4 * d - 2) (m - 1))) = Finset.card (Finset.filter (fun k => Odd (m - 4 * d - 2 + k)) (Finset.range (4 * d + 2))) := by
        refine' Finset.card_bij ( fun x hx => Int.toNat ( x - ( m - 4 * d - 2 ) ) ) _ _ _;
        · norm_num +zetaDelta at *;
          intro a ha₁ ha₂ ha₃; refine' ⟨ ⟨ Int.toNat ( a - ( m - 4 * d - 2 ) ), _, _ ⟩, _ ⟩ <;> norm_num [ Int.toNat_of_nonneg ( by linarith : 0 ≤ a - ( m - 4 * d - 2 ) ) ] ;
          · linarith;
          · exact ha₁;
          · rw [ max_eq_left ( by linarith ) ] ; simp_all +decide [ parity_simps ];
        · aesop;
        · simp +zetaDelta at *;
          grind;
      by_cases hm : Even m <;> simp_all +decide [ parity_simps ];
      · rw [ Finset.card_eq_of_bijective ];
        use fun i hi => 2 * i + 1;
        · simp +zetaDelta at *;
          intro a ha h; rcases Nat.even_or_odd' a with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ parity_simps ] ;
          · grind;
          · linarith;
        · simp_all +decide [ parity_simps ];
          exact fun i hi => ⟨ 2 * i + 1, by linarith, by norm_cast ⟩;
        · grind;
      · rw [ Finset.card_eq_of_bijective ];
        use fun i hi => 2 * i;
        · simp +zetaDelta at *;
          exact fun a ha₁ ha₂ => by obtain ⟨ k, rfl ⟩ := even_iff_two_dvd.mp ha₂; exact ⟨ k, by linarith, by push_cast; ring ⟩ ;
        · simp +zetaDelta at *;
          exact fun i hi => ⟨ 2 * i, by linarith, by push_cast; ring ⟩;
        · aesop

/-
Given a set of pairs summing to $2m$, and distinct $b_1, b_2$, any integer $x$ can be formed as a sum $b_i + p_j$ by at most 2 pairs.
-/
lemma bad_pairs_card (S : Finset (ℤ × ℤ)) (b₁ b₂ m x : ℤ)
    (hS_sum : ∀ p ∈ S, p.1 + p.2 = 2 * m)
    (hS_ord : ∀ p ∈ S, p.1 < p.2)
    (hb : b₁ ≠ b₂) :
    (S.filter (fun p => b₁ + p.1 = x ∨ b₂ + p.1 = x ∨ b₁ + p.2 = x ∨ b₂ + p.2 = x)).card ≤ 2 := by
      -- Each codition singles out at most one pair. So, there are at most 2 such pairs in $S$.
      have h_card : (Finset.filter (fun p => b₁ + p.1 = x ∨ b₁ + p.2 = x) S).card ≤ 1 ∧ (Finset.filter (fun p => b₂ + p.1 = x ∨ b₂ + p.2 = x) S).card ≤ 1 := by
        constructor <;> rw [ Finset.card_le_one_iff ];
        · grind;
        · grind;
      exact le_trans ( Finset.card_le_card ( show { p ∈ S | b₁ + p.1 = x ∨ b₂ + p.1 = x ∨ b₁ + p.2 = x ∨ b₂ + p.2 = x } ⊆ { p ∈ S | b₁ + p.1 = x ∨ b₁ + p.2 = x } ∪ { p ∈ S | b₂ + p.1 = x ∨ b₂ + p.2 = x } from fun p hp => by aesop ) ) ( Finset.card_union_le _ _ ) |> le_trans <| add_le_add h_card.1 h_card.2 |> le_trans <| by norm_num;

lemma upper_case_2_helper (n d : ℕ) (A : Finset ℤ)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (hA_card : A.card ≥ n + 2032)
    (t : ℕ) (ht : t = (A.filter Even).card)
    (h_t_val : t = 2032 + d)
    (m : ℤ) (hm_in : 2 * m ∈ A)
    (hm_range : 2 * d + 2 ≤ m ∧ m ≤ n - 2 * d - 2) :
    ∃ b₁ b₂ b₃ b₄ : ℤ,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₃ ≠ b₄ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₂ + b₃, b₂ + b₄, b₃ + b₄} ⊆ A := by
        -- Choose $b_1, b_2$ even such that $b_1 + b_2 = 2m$ and $m-2 \le b_1 < b_2 \le m+2$.
        obtain ⟨b₁, b₂, hb₁b₂⟩ : ∃ b₁ b₂ : ℤ, Even b₁ ∧ Even b₂ ∧ b₁ + b₂ = 2 * m ∧ m - 2 ≤ b₁ ∧ b₁ < b₂ ∧ b₂ ≤ m + 2 := by
          by_cases hm_even : Even m;
          · exact ⟨ m - 2, m + 2, by simpa [ parity_simps ] using hm_even, by simpa [ parity_simps ] using hm_even, by ring, by linarith, by linarith, by linarith ⟩;
          · exact ⟨ m - 1, m + 1, by simpa [ parity_simps ] using hm_even, by simpa [ parity_simps ] using hm_even, by ring, by linarith, by linarith, by linarith ⟩;
        -- Let $S$ be the set of pairs $(p, q)$ of odd integers with $p < q$ and $p+q=2m$ in $I = [m-4d-2, m+4d+2]$.
        set S := Finset.filter (fun p => p.1 < p.2 ∧ p.1 + p.2 = 2 * m ∧ Odd p.1 ∧ Odd p.2)
          (Finset.Icc (m - 4 * d - 2) (m + 4 * d + 2) ×ˢ Finset.Icc (m - 4 * d - 2) (m + 4 * d + 2)) with hS_def;
        -- By `pigeonhole_pairs`, there exists $(p, q) \in S$ not in any $bad(x)$.
        obtain ⟨p, hp⟩ : ∃ p ∈ S, ∀ x ∈ Finset.filter (fun x => x ∉ A) (Finset.filter Odd (Finset.Icc 1 (2 * n))), ¬(b₁ + p.1 = x ∨ b₂ + p.1 = x ∨ b₁ + p.2 = x ∨ b₂ + p.2 = x) := by
          have h_card_S : S.card = 2 * d + 1 := by
            -- The set S is in bijection with the set of odd integers in the interval [m - 4d - 2, m - 1].
            have h_bij : S.image Prod.fst = Finset.filter Odd (Finset.Icc (m - 4 * d - 2) (m - 1)) := by
              ext; simp [S];
              constructor <;> intro h;
              · grind +ring;
              · use 2 * m - ‹ℤ›;
                grind;
            have h_card_odd : (Finset.filter Odd (Finset.Icc (m - 4 * d - 2) (m - 1))).card = 2 * d + 1 := by
              convert count_odd_pairs_lemma m d using 1;
            rw [ ← h_card_odd, ← h_bij, Finset.card_image_of_injOn ];
            exact fun x hx y hy hxy => Prod.ext hxy <| by linarith [ Finset.mem_filter.mp hx, Finset.mem_filter.mp hy ] ;
          have h_card_B : (Finset.filter (fun x => x ∉ A) (Finset.filter Odd (Finset.Icc 1 (2 * n)))).card ≤ d := by
            -- Since $A$ contains at least $n + 2032$ elements, and $t = 2032 + d$, the number of odd elements in $A$ is at least $n - d$.
            have h_odd_A : (Finset.filter Odd A).card ≥ n - d := by
              have h_odd_A : (Finset.filter Even A).card + (Finset.filter Odd A).card = A.card := by
                rw [ Finset.card_filter, Finset.card_filter ];
                simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones A ▸ by congr; ext x; aesop;
              omega;
            have h_odd_total : (Finset.filter Odd (Finset.Icc 1 (2 * n))).card = n := by
              rw [ show Finset.filter Odd ( Finset.Icc 1 ( 2 * n ) ) = Finset.image ( fun k => 2 * k + 1 ) ( Finset.range n ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
              ext ; simp +decide [ parity_simps ];
              exact ⟨ fun h => by obtain ⟨ k, rfl ⟩ := h.2; exact ⟨ k, by linarith, rfl ⟩, fun h => by obtain ⟨ k, hk₁, rfl ⟩ := h; exact ⟨ ⟨ by linarith, by linarith ⟩, by simp +decide [ parity_simps ] ⟩ ⟩;
            have h_odd_not_in_A : (Finset.filter Odd (Finset.Icc 1 (2 * n)) \ Finset.image (fun x : ℤ => x.natAbs) (Finset.filter Odd A)).card ≤ d := by
              rw [ Finset.card_sdiff ];
              rw [ Finset.inter_eq_left.mpr ];
              · rw [ Finset.card_image_of_injOn ];
                · omega;
                · exact fun x hx y hy hxy => by cases abs_cases x <;> cases abs_cases y <;> linarith [ Finset.mem_Icc.mp ( hA_subset ( Finset.mem_filter.mp hx |>.1 ) ), Finset.mem_Icc.mp ( hA_subset ( Finset.mem_filter.mp hy |>.1 ) ) ] ;
              · simp_all +decide [ Finset.subset_iff ];
                rintro x y hy hy' rfl; exact ⟨ ⟨ by linarith [ abs_of_nonneg ( by linarith [ hA_subset hy ] : 0 ≤ y ), hA_subset hy ], by linarith [ abs_of_nonneg ( by linarith [ hA_subset hy ] : 0 ≤ y ), hA_subset hy ] ⟩, by simpa [ ← Int.odd_iff ] using hy' ⟩ ;
            refine le_trans ?_ h_odd_not_in_A;
            refine' le_of_eq _;
            refine' Finset.card_bij ( fun x hx => Int.natAbs x ) _ _ _ <;> simp +decide [ Finset.mem_sdiff, Finset.mem_image ];
            · intro a ha₁ ha₂ ha₃ ha₄; refine' ⟨ ⟨ ⟨ by linarith [ abs_of_nonneg ( by linarith : 0 ≤ a ) ], by linarith [ abs_of_nonneg ( by linarith : 0 ≤ a ) ] ⟩, ha₃ ⟩, _ ⟩ ; intro x hx₁ hx₂ hx₃; simp_all +decide [ Int.natAbs_eq_natAbs_iff ] ;
              rcases hx₃ with ( rfl | rfl ) <;> [ exact ha₄ hx₁; exact absurd ( Finset.mem_Icc.mp ( hA_subset hx₁ ) ) ( by intros h; linarith ) ];
            · intros; omega;
            · intro b hb₁ hb₂ hb₃ hb₄; use b; simp_all +decide ;
              exact ⟨ mod_cast hb₂, fun h => hb₄ _ h ( by simpa [ ← Int.odd_iff ] using hb₃ ) ( by simp +decide ) ⟩;
          have h_pigeonhole : ∃ p ∈ S, ∀ x ∈ Finset.filter (fun x => x ∉ A) (Finset.filter Odd (Finset.Icc 1 (2 * n))), ¬(b₁ + p.1 = x ∨ b₂ + p.1 = x ∨ b₁ + p.2 = x ∨ b₂ + p.2 = x) := by
            have h_bad_pairs : ∀ x ∈ Finset.filter (fun x => x ∉ A) (Finset.filter Odd (Finset.Icc 1 (2 * n))), (S.filter (fun p => b₁ + p.1 = x ∨ b₂ + p.1 = x ∨ b₁ + p.2 = x ∨ b₂ + p.2 = x)).card ≤ 2 := by
              intros x hx
              apply bad_pairs_card S b₁ b₂ m x (by
              aesop) (by
              aesop) (by
              linarith)
            have h_pigeonhole : (Finset.biUnion (Finset.filter (fun x => x ∉ A) (Finset.filter Odd (Finset.Icc 1 (2 * n)))) (fun x => S.filter (fun p => b₁ + p.1 = x ∨ b₂ + p.1 = x ∨ b₁ + p.2 = x ∨ b₂ + p.2 = x))).card < S.card := by
              exact lt_of_le_of_lt ( Finset.card_biUnion_le ) ( lt_of_le_of_lt ( Finset.sum_le_sum h_bad_pairs ) ( by norm_num; linarith ) );
            contrapose! h_pigeonhole;
            exact Finset.card_le_card fun x hx => by obtain ⟨ y, hy, hy' ⟩ := h_pigeonhole x hx; aesop;
          exact h_pigeonhole;
        use b₁, b₂, p.1, p.2;
        simp_all +decide [ Finset.subset_iff ];
        refine' ⟨ by linarith, _, _, _, _, _, _ ⟩ <;> try linarith;
        · grind;
        · grind;
        · refine' ⟨ _, _, _, _ ⟩ <;> contrapose! hp;
          · grind;
          · grind;
          · grind;
          · grind

lemma upper_case_no_middle_helper (n d : ℕ) (A : Finset ℤ)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (t : ℕ) (ht : t = (A.filter Even).card)
    (h_t_val : t = 2032 + d)
    (h_no_mid : ∀ x ∈ A, Even x → x ∉ Finset.Icc (4 * d + 4 : ℤ) ((2 * n : ℤ) - 4 * d - 4)) :
    ∃ b₁ b₂ b₃ b₄ : ℤ,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₃ ≠ b₄ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₂ + b₃, b₂ + b₄, b₃ + b₄} ⊆ A := by
        -- By `separation_lemma`, $A \cap Even \subseteq Y_1 \cup Y_2$. So $|Y_1| + |Y_2| \ge |A \cap Even| = t = 2032 + d$.
        set Y1 := Finset.filter Even A ∩ Finset.Icc 2 (4 * d + 2)
        set Y2 := Finset.filter Even A ∩ Finset.Icc ((2 * n : ℤ) - 4 * d - 2) (2 * n : ℤ) with hY2_def
        have hY1Y2_subset : Finset.filter Even A ⊆ Y1 ∪ Y2 := by
          intro x hx; by_cases hx1 : x ≤ 4 * d + 2 <;> by_cases hx2 : x ≥ ( 2 * n : ℤ ) - 4 * d - 2 <;> simp_all +decide ;
          · exact Or.inr ( by linarith [ Finset.mem_Icc.mp ( hA_subset hx.1 ) ] );
          · exact Or.inl <| Finset.mem_inter.mpr ⟨ Finset.mem_filter.mpr ⟨ hx.1, hx.2 ⟩, Finset.mem_Icc.mpr ⟨ by obtain ⟨ k, hk ⟩ := hx.2; linarith [ show k > 0 from by linarith [ Finset.mem_Icc.mp ( hA_subset hx.1 ) ] ], hx1 ⟩ ⟩;
          · exact Or.inr ( by linarith [ Finset.mem_Icc.mp ( hA_subset hx.1 ) ] );
          · grind
        have hY1Y2_card : Y1.card + Y2.card ≥ 2032 + d := by
          linarith [ Finset.card_mono hY1Y2_subset, Finset.card_union_add_card_inter Y1 Y2 ];
        -- By Lemma `upper_case_1_helper`, we can find the desired elements in $A$.
        by_cases hY1 : (Y1.card : ℝ) ≥ 1016 + (d : ℝ) / 2
        by_cases hY2 : (Y2.card : ℝ) ≥ 1016 + (d : ℝ) / 2
        generalize_proofs at *; (
        apply_rules [ upper_case_1_helper ];
        · exact fun x hx => Finset.mem_filter.mp ( Finset.mem_inter.mp hx |>.1 ) |>.1 |> fun hx' => by aesop;
        · aesop;
        · exact ⟨ 2, fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.2 ) ], by linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.2 ) ] ⟩ ⟩);
        · convert upper_case_1_helper d A Y1 _ _ _ _ using 1
          all_goals generalize_proofs at *;
          · exact fun x hx => Finset.mem_filter.mp ( Finset.mem_inter.mp hx |>.1 ) |>.1 |> fun hx' => by aesop;
          · aesop;
          · convert hY1 using 1;
          · exact ⟨ 2, fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.2 ) ], by linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.2 ) ] ⟩ ⟩;
        · -- By Lemma `corro`, we can find the desired elements in $A$.
          have hY2_card : (Y2.card : ℝ) ≥ 2 * (4 * d + 2 : ℝ)^(3 / 4 : ℝ) + 1.01 * (4 * d + 2 : ℝ)^(1 / 2 : ℝ) + 2 := by
            have hY2_card : (Y2.card : ℝ) ≥ 1016 + (d : ℝ) / 2 := by
              linarith [ ( by norm_cast : ( Y1.card : ℝ ) + Y2.card ≥ 2032 + d ) ] ;
            have := ybound ( 4 * d + 2 ) ( by linarith ) ; norm_num at * ; linarith;
          -- By Lemma `corro`, we can find the desired elements in $Y2$.
          obtain ⟨y, hy_range, hy_card⟩ : ∃ y : Fin Y2.card → ℤ, StrictMono y ∧ (∀ i, y i ∈ Y2) ∧ (∀ i, Even (y i)) := by
            exact ⟨ fun i => Y2.orderEmbOfFin rfl i, by simp +decide [ StrictMono ], fun i => Finset.orderEmbOfFin_mem _ _ _, fun i => Finset.mem_filter.mp ( Finset.mem_inter.mp ( Y2.orderEmbOfFin_mem rfl i ) |>.1 ) |>.2 ⟩;
          have := corro Y2.card (by
          exact Nat.one_le_iff_ne_zero.mpr ( by rintro h; norm_num [ h ] at hY2_card; linarith [ Real.rpow_nonneg ( show ( 0 : ℝ ) ≤ 4 * d + 2 by positivity ) ( 3 / 4 : ℝ ), Real.rpow_nonneg ( show ( 0 : ℝ ) ≤ 4 * d + 2 by positivity ) ( 1 / 2 : ℝ ) ] ) ;) y hy_range (fun i => hy_card.2 i) (by
          all_goals generalize_proofs at *;
          refine le_trans ?_ hY2_card;
          gcongr <;> norm_num;
          · exact Real.rpow_le_rpow ( sub_nonneg.mpr <| mod_cast hy_range.monotone <| Nat.zero_le _ ) ( sub_le_iff_le_add'.mpr <| by linarith [ show ( y ⟨ Y2.card - 1, by linarith ⟩ : ℝ ) ≤ 2 * n by exact_mod_cast Finset.mem_Icc.mp ( Finset.mem_inter.mp ( hy_card.1 _ ) |>.2 ) |>.2, show ( y ⟨ 0, by linarith ⟩ : ℝ ) ≥ 2 * n - 4 * d - 2 by exact_mod_cast Finset.mem_Icc.mp ( Finset.mem_inter.mp ( hy_card.1 _ ) |>.2 ) |>.1 ] ) ( by norm_num );
          · gcongr;
            · exact sub_nonneg_of_le <| mod_cast hy_range.monotone <| Nat.zero_le _;
            · norm_cast;
              have := hy_card.1 ⟨ Y2.card - 1, by omega ⟩ ; have := hy_card.1 ⟨ 0, by omega ⟩ ; norm_num at * ; linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp this |>.2 ), Finset.mem_Icc.mp ( Finset.mem_inter.mp ( hy_card.1 ⟨ Y2.card - 1, by omega ⟩ ) |>.2 ) ] ;);
          obtain ⟨ b₁, b₂, b₃, b₄, h₁, h₂, h₃, h₄, h₅, h₆, h₇ ⟩ := this; use b₁, b₂, b₃, b₄; simp_all +decide [ Set.subset_def ] ;
          simp_all +decide [ Finset.subset_iff ];
          exact ⟨ by obtain ⟨ i, hi ⟩ := h₇.1; exact hi ▸ hy_card.1 i |>.1.1, by obtain ⟨ i, hi ⟩ := h₇.2.1; exact hi ▸ hy_card.1 i |>.1.1, by obtain ⟨ i, hi ⟩ := h₇.2.2.1; exact hi ▸ hy_card.1 i |>.1.1, by obtain ⟨ i, hi ⟩ := h₇.2.2.2.1; exact hi ▸ hy_card.1 i |>.1.1, by obtain ⟨ i, hi ⟩ := h₇.2.2.2.2.1; exact hi ▸ hy_card.1 i |>.1.1, by obtain ⟨ i, hi ⟩ := h₇.2.2.2.2.2; exact hi ▸ hy_card.1 i |>.1.1 ⟩

/-
If $y \ge 1$ and $t \ge \sqrt{8}y^{7/8} + y^{5/8} + 2$, then $\frac{t(t-1)}{4y} \ge 2y^{3/4} + 1.01y^{1/2} + 2$.
-/
lemma gcestwo_bound_check (y : ℝ) (hy : y ≥ 1) (t : ℝ) (ht : t ≥ Real.sqrt 8 * y^(0.875 : ℝ) + y^(0.625 : ℝ) + 2) :
    t * (t - 1) / (4 * y) ≥ 2 * y^(0.75 : ℝ) + 1.01 * y^(0.5 : ℝ) + 2 := by
      -- By simplifying, we can see that the inequality holds for all $x \ge 1$.
      have h_simplified : ∀ x : ℝ, x ≥ 1 → (Real.sqrt 8 * x^7 + x^5 + 1) * (Real.sqrt 8 * x^7 + x^5 + 1) / (4 * x^8) ≥ 2 * x^6 + 1.01 * x^4 + 2 := by
        intro x hx; rw [ ge_iff_le ] ; rw [ le_div_iff₀ <| by positivity ] ; ring_nf; norm_num;
        -- Since $x \geq 1$, we can bound the terms involving $\sqrt{8}$.
        have h_bound : x^7 * Real.sqrt 8 * 2 ≥ 5.656 * x^7 ∧ x^10 ≥ x^8 := by
          exact ⟨ by norm_num; nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ), pow_pos ( zero_lt_one.trans_le hx ) 7 ], by exact pow_le_pow_right₀ hx ( by norm_num ) ⟩;
        nlinarith [ pow_le_pow_left₀ ( by positivity ) hx 5, pow_le_pow_left₀ ( by positivity ) hx 6, pow_le_pow_left₀ ( by positivity ) hx 7, pow_le_pow_left₀ ( by positivity ) hx 8, pow_le_pow_left₀ ( by positivity ) hx 9, pow_le_pow_left₀ ( by positivity ) hx 10, pow_le_pow_left₀ ( by positivity ) hx 11, pow_le_pow_left₀ ( by positivity ) hx 12, Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ) ];
      have := h_simplified ( y ^ ( 1/8 : ℝ ) ) ( Real.one_le_rpow hy ( by norm_num ) ) ; rw [ ← Real.rpow_natCast _ 7, ← Real.rpow_mul ( by positivity ), ← Real.rpow_natCast _ 5, ← Real.rpow_mul ( by positivity ), ← Real.rpow_natCast _ 8, ← Real.rpow_mul ( by positivity ) ] at * ; norm_num at *;
      rw [ le_div_iff₀ ( by positivity ) ] at *;
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] at * ; norm_num at *;
      exact this.trans ( by nlinarith [ show 0 < Real.sqrt 8 * y ^ ( 7 / 8 : ℝ ) + y ^ ( 5 / 8 : ℝ ) by positivity ] )

/-
In a disjoint matching with difference $m$, the difference between any two left endpoints is not $m$.
-/
lemma matching_diff_ne_m (t : ℕ) (y : Fin t → ℤ) (m : ℤ) (hm : m ≠ 0)
    (M : Finset (Fin t × Fin t))
    (h_diff : ∀ p ∈ M, y p.2 - y p.1 = m)
    (h_disj : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset (Fin t)) ∩ {q.1, q.2} = ∅)
    (h_mono : StrictMono y)
    (p q : Fin t × Fin t) (hp : p ∈ M) (hq : q ∈ M) :
    y q.1 - y p.1 ≠ m := by
      by_contra h_contra;
      -- Since $y$ is strictly monotone, $y q.1 = y p.2$.
      have h_eq : y q.1 = y p.2 := by
        linarith [ h_diff p hp, h_diff q hq ];
      simp_all +decide [ Finset.ext_iff, h_mono.injective.eq_iff ];
      grind

/-
Helper lemma for `gcestwo`: If there is a large matching with difference $m$, then the conclusion holds.
-/
lemma gcestwo_of_matching (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (m : ℤ) (hm : m ≠ 0)
    (M : Finset (Fin t × Fin t))
    (h_diff : ∀ p ∈ M, y p.2 - y p.1 = m)
    (h_disj : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset (Fin t)) ∩ {q.1, q.2} = ∅)
    (h_card : (M.card : ℝ) ≥ 2 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.75 : ℝ) + 1.01 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.5 : ℝ) + 2)
    (h_y_ge_1 : y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ ≥ 1)
    (h_mono : StrictMono y) :
    ∃ x₁ x₂ x₃ x₄ x₅, x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₄ ≠ 0 ∧ x₅ ≠ 0 ∧
    x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₂ ≠ x₅ ∧ x₃ ≠ x₄ ∧ x₃ ≠ x₅ ∧ x₄ ≠ x₅ ∧
    {x₁, x₁ + x₂, x₁ + x₃, x₁ + x₄, x₁ + x₅,
     x₁ + x₂ + x₃, x₁ + x₂ + x₄, x₁ + x₂ + x₅, x₁ + x₃ + x₄, x₁ + x₃ + x₅, x₁ + x₄ + x₅,
     x₁ + x₂ + x₃ + x₄, x₁ + x₂ + x₃ + x₅, x₁ + x₂ + x₄ + x₅, x₁ + x₃ + x₄ + x₅,
     x₁ + x₂ + x₃ + x₄ + x₅} ⊆ Set.range y := by
       obtain ⟨z, hz_card, hz⟩ : ∃ z : Fin M.card → Fin t, StrictMono z ∧ ∀ i, z i ∈ Finset.image Prod.fst M := by
         have h_order : Finset.card (Finset.image Prod.fst M) = M.card := by
           rw [ Finset.card_image_of_injOn ] ; intro p hp q hq ; specialize h_disj p hp q hq ; aesop;
         generalize_proofs at *; (
         exact ⟨ fun i => Finset.orderEmbOfFin _ ( by aesop ) i, by aesop_cat, fun i => Finset.orderEmbOfFin_mem _ ( by aesop ) _ ⟩)
       generalize_proofs at *; (
       -- By `gces_nonzero`, there exist distinct $x_2, x_3, x_4, x_5$ such that the subset sums containing $x_1$ are in the range of $z$.
       obtain ⟨x₁, x₂, x₃, x₄, hx⟩ : ∃ x₁ x₂ x₃ x₄ : ℤ,
         x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₄ ≠ 0 ∧
         x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₃ ≠ x₄ ∧
         {x₁, x₁ + x₂, x₁ + x₃, x₁ + x₄, x₁ + x₂ + x₃, x₁ + x₂ + x₄, x₁ + x₃ + x₄, x₁ + x₂ + x₃ + x₄} ⊆ Set.range (fun i => y (z i)) := by
           have := gces_nonzero ( M.card ) ?_ ( fun i => y ( z i ) ) ?_ ?_
           generalize_proofs at *; (
           apply this
           generalize_proofs at *; (
           refine' Int.le_of_lt_add_one _;
           exact lt_add_of_pos_left _ ( sub_pos.mpr <| h_mono <| hz_card <| Nat.zero_lt_of_lt <| Nat.sub_pos_of_lt <| Finset.one_lt_card.mpr <| by
             contrapose! h_card;
             rw [ show M.card = 1 by exact le_antisymm ( Finset.card_le_one.mpr fun x hx y hy => h_card x hx y hy ) ( by linarith ) ] ; norm_num ; linarith [ Real.rpow_pos_of_pos ( show 0 < ( y ⟨ t - 1, by omega ⟩ - y ⟨ 0, by omega ⟩ : ℝ ) by exact_mod_cast h_y_ge_1.trans_lt' <| by norm_num ) ( 0.75 : ℝ ), Real.rpow_pos_of_pos ( show 0 < ( y ⟨ t - 1, by omega ⟩ - y ⟨ 0, by omega ⟩ : ℝ ) by exact_mod_cast h_y_ge_1.trans_lt' <| by norm_num ) ( 0.5 : ℝ ) ] ; )));
           any_goals intro i j hij; exact h_mono ( hz_card hij );
           exact Nat.one_le_iff_ne_zero.mpr ( by rintro h; norm_num [ h ] at h_card; linarith [ Real.rpow_nonneg ( show ( y ⟨ t - 1, by omega ⟩ - y ⟨ 0, by omega ⟩ : ℝ ) ≥ 0 by exact_mod_cast Int.sub_nonneg_of_le <| h_mono.monotone <| Nat.zero_le _ ) 0.75, Real.rpow_nonneg ( show ( y ⟨ t - 1, by omega ⟩ - y ⟨ 0, by omega ⟩ : ℝ ) ≥ 0 by exact_mod_cast Int.sub_nonneg_of_le <| h_mono.monotone <| Nat.zero_le _ ) 0.5 ] );
           refine le_trans ?_ h_card
           generalize_proofs at *; (
           gcongr <;> norm_cast;
           any_goals exact h_mono.monotone ( Nat.zero_le _ );
           · exact sub_nonneg_of_le <| h_mono.monotone <| hz_card.monotone <| Nat.zero_le _;
           · exact h_mono.monotone ( Nat.le_pred_of_lt ( Fin.is_lt _ ) );
           · exact sub_nonneg_of_le <| h_mono.monotone <| hz_card.monotone <| Nat.zero_le _;
           · exact h_mono.monotone ( Nat.le_pred_of_lt ( Fin.is_lt _ ) ))
       generalize_proofs at *; (
       -- By `matching_diff_ne_m`, $x_k \ne m$ for $k = 2, 3, 4$.
       have hx_ne_m : x₂ ≠ m ∧ x₃ ≠ m ∧ x₄ ≠ m := by
         have h_diff_ne_m : ∀ p q : Fin M.card, p ≠ q → y (z q) - y (z p) ≠ m := by
           intros p q hpq
           obtain ⟨p', hp'⟩ : ∃ p' ∈ M, z p = p'.1 := by
             simpa [ eq_comm ] using Finset.mem_image.mp ( hz p )
           obtain ⟨q', hq'⟩ : ∃ q' ∈ M, z q = q'.1 := by
             simpa [ eq_comm ] using Finset.mem_image.mp ( hz q )
           generalize_proofs at *; (
           have := matching_diff_ne_m t y m hm M h_diff h_disj h_mono p' q' hp'.1 hq'.1; aesop;)
         generalize_proofs at *; (
         simp_all +decide [ Set.subset_def ];
         grind +ring)
       generalize_proofs at *; (
       use x₁, x₂, x₃, x₄, m
       generalize_proofs at *; (
       simp_all +decide [ Set.insert_subset_iff ];
       -- For any subset sum S involving m, we can write S as S' + m where S' is a subset sum of {x₁, x₂, x₃, x₄} containing x₁.
       have h_subset_sum : ∀ S ∈ ({x₁ + m, x₁ + x₂ + m, x₁ + x₃ + m, x₁ + x₄ + m, x₁ + x₂ + x₃ + m, x₁ + x₂ + x₄ + m, x₁ + x₃ + x₄ + m, x₁ + x₂ + x₃ + x₄ + m} : Finset ℤ), ∃ y_1, y y_1 = S := by
         rcases hx.2.2.2.2.2.2 with ⟨ ⟨ i, hi ⟩, ⟨ j, hj ⟩, ⟨ k, hk ⟩, ⟨ l, hl ⟩, ⟨ m, hm ⟩, ⟨ n, hn ⟩, ⟨ o, ho ⟩, ⟨ p, hp ⟩ ⟩ ; simp_all +decide [ sub_eq_iff_eq_add' ] ;
         exact ⟨ by obtain ⟨ q, hq ⟩ := hz i; exact ⟨ q, by linarith [ h_diff _ _ hq ] ⟩, by obtain ⟨ q, hq ⟩ := hz j; exact ⟨ q, by linarith [ h_diff _ _ hq ] ⟩, by obtain ⟨ q, hq ⟩ := hz k; exact ⟨ q, by linarith [ h_diff _ _ hq ] ⟩, by obtain ⟨ q, hq ⟩ := hz l; exact ⟨ q, by linarith [ h_diff _ _ hq ] ⟩, by obtain ⟨ q, hq ⟩ := hz m; exact ⟨ q, by linarith [ h_diff _ _ hq ] ⟩, by obtain ⟨ q, hq ⟩ := hz n; exact ⟨ q, by linarith [ h_diff _ _ hq ] ⟩, by obtain ⟨ q, hq ⟩ := hz o; exact ⟨ q, by linarith [ h_diff _ _ hq ] ⟩, by obtain ⟨ q, hq ⟩ := hz p; exact ⟨ q, by linarith [ h_diff _ _ hq ] ⟩ ⟩
       generalize_proofs at *; (
       simp_all +decide [Finset.ext_iff];
       tauto)))))

/-
Corrected version of Lemma `gcestwo` with exponent $7/8$.
-/
theorem gcestwo (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y)
    (h_bound : (t : ℝ) ≥ Real.sqrt 8 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.875 : ℝ) + (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.625 : ℝ) + 2)
    (h_y_ge_1 : y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ ≥ 1) :
    ∃ x₁ x₂ x₃ x₄ x₅, x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₄ ≠ 0 ∧ x₅ ≠ 0 ∧
    x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₂ ≠ x₅ ∧ x₃ ≠ x₄ ∧ x₃ ≠ x₅ ∧ x₄ ≠ x₅ ∧
    {x₁, x₁ + x₂, x₁ + x₃, x₁ + x₄, x₁ + x₅,
     x₁ + x₂ + x₃, x₁ + x₂ + x₄, x₁ + x₂ + x₅, x₁ + x₃ + x₄, x₁ + x₃ + x₅, x₁ + x₄ + x₅,
     x₁ + x₂ + x₃ + x₄, x₁ + x₂ + x₃ + x₅, x₁ + x₂ + x₄ + x₅, x₁ + x₃ + x₄ + x₅,
     x₁ + x₂ + x₃ + x₄ + x₅} ⊆ Set.range y := by
       -- Apply `gces_matching_size_bound` to obtain a difference $m$ and a matching $M$ such that $|M| \ge \frac{t(t-1)}{4(y_{t-1}-y_0)}$.
       obtain ⟨m, hm_ne_zero, M, hM_diff, hM_disj, hM_card⟩ : ∃ m : ℤ, m ≠ 0 ∧ ∃ M : Finset (Fin t × Fin t),
         (∀ p ∈ M, y p.2 - y p.1 = m) ∧
         (∀ p ∈ M, p.1 < p.2) ∧
         (∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset (Fin t)) ∩ {q.1, q.2} = ∅) ∧
         (M.card : ℝ) ≥ (t * (t - 1) : ℝ) / (4 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)) := by
           obtain ⟨ m, hm, M, hM₁, hM₂, hM₃, hM₄ ⟩ := gces_matching_size_bound t ( show 2 ≤ t from by
                                                                                     contrapose! h_bound; interval_cases t ; norm_num at *; ) y h_mono
           generalize_proofs at *; (
           exact ⟨ m, ne_of_gt hm, M, hM₁, hM₂, hM₃, hM₄ ⟩);
       apply gcestwo_of_matching t ht y m hm_ne_zero M hM_diff (by
       exact hM_card.1) (by
       refine le_trans ?_ hM_card.2;
       convert gcestwo_bound_check _ _ _ _ using 1;
       · exact_mod_cast h_y_ge_1;
       · convert h_bound using 1) (by
       linarith) h_mono

/-
If the sequence consists of even integers, we can find distinct $b_1, \dots, b_5$ such that all pairwise sums are in the sequence.
-/
theorem corrotwo (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y)
    (h_even : ∀ i, Even (y i))
    (h_bound : (t : ℝ) ≥ Real.sqrt 8 * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.875 : ℝ) + (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.625 : ℝ) + 2)
    (h_y_ge_1 : y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ ≥ 1) :
    ∃ b₁ b₂ b₃ b₄ b₅,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₁ ≠ b₅ ∧
      b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₂ ≠ b₅ ∧
      b₃ ≠ b₄ ∧ b₃ ≠ b₅ ∧
      b₄ ≠ b₅ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₁ + b₅,
       b₂ + b₃, b₂ + b₄, b₂ + b₅,
       b₃ + b₄, b₃ + b₅,
       b₄ + b₅} ⊆ Set.range y := by
         have := @gcestwo t ht y h_mono h_bound h_y_ge_1;
         obtain ⟨ x₁, x₂, x₃, x₄, x₅, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁ ⟩ := this; use x₁ / 2, x₁ / 2 + x₂, x₁ / 2 + x₃, x₁ / 2 + x₄, x₁ / 2 + x₅; simp_all +decide [ Set.subset_def ] ;
         grind

/-
Constant C_5 = 10^9
-/
noncomputable def C_5 : ℝ := 10^9-20

def geom_base : ℝ := 1.03

/-
The number of geometric intervals $[1.03^j, 1.03^{j+1})$ covering $[6.5d, 2n]$ is less than $50 \log n$.
-/
lemma geometric_intervals_count_bound (n d : ℕ) (hn : n ≥ 1) (hd : d ≥ 10) :
    let j₁ := ⌊Real.log (6.5 * d) / Real.log geom_base⌋
    let j₂ := ⌈Real.log (2 * n) / Real.log geom_base⌉
    (j₂ - j₁ : ℝ) < 50 * Real.log n := by
      -- Using the bounds on the logarithms, we can simplify the expression.
      have h_simplify : (Real.log (2 * n / (6.5 * d)) / Real.log geom_base) + 2 < 50 * Real.log n := by
        -- Since $d \geq 10$, we have $\ln(6.5d) \geq \ln(65) > 4$.
        have h_log_bound : Real.log (6.5 * d) > 4 := by
          rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ] <;> norm_num <;> try linarith [ ( by norm_cast : ( 10 :ℝ ) ≤ d ) ] ;
          have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ Real.add_one_le_exp 1, pow_pos ( Real.exp_pos 1 ) 2, pow_pos ( Real.exp_pos 1 ) 3, ( by norm_cast : ( 10 :ℝ ) ≤ d ) ] ;
        -- Using the bounds on the logarithms, we can simplify the expression further.
        have h_simplify_further : Real.log (2 * n / (6.5 * d)) < Real.log n + 0.7 - 4 := by
          rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ) ];
          have := Real.log_two_lt_d9 ; norm_num at * ; linarith;
        rw [ div_add', div_lt_iff₀ ] <;> norm_num [ Real.log_pos ] at *;
        · have h_log_geom_base : Real.log geom_base > 1 / 34 := by
            rw [ gt_iff_lt, div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            rw [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ] <;> norm_num [ geom_base ];
            exact Real.exp_one_lt_d9.trans_le <| by norm_num;
          by_cases hn : n ≥ 2;
          · nlinarith [ show ( Real.log n : ℝ ) ≥ 1 / 2 by exact le_trans ( by norm_num ) ( Real.log_two_gt_d9.le.trans ( Real.log_le_log ( by norm_num ) ( Nat.cast_le.mpr hn ) ) ) ];
          · interval_cases n ; norm_num at *;
            linarith [ show Real.log geom_base ≤ 1 by exact le_trans ( Real.log_le_sub_one_of_pos ( by norm_num [ geom_base ] ) ) ( by norm_num [ geom_base ] ) ];
        · exact Real.log_pos <| by norm_num [ geom_base ] ;
        · norm_num [ geom_base ];
      -- Using the properties of logarithms, we can rewrite the inequality.
      have h_log_prop : (Real.log (2 * n / (6.5 * d)) / Real.log geom_base) = (Real.log (2 * n) / Real.log geom_base) - (Real.log (6.5 * d) / Real.log geom_base) := by
        rw [ Real.log_div ( by positivity ) ( by positivity ), sub_div ];
      linarith [ Int.floor_le ( Real.log ( 6.5 * d ) / Real.log geom_base ), Int.lt_floor_add_one ( Real.log ( 6.5 * d ) / Real.log geom_base ), Int.le_ceil ( Real.log ( 2 * n ) / Real.log geom_base ), Int.ceil_lt_add_one ( Real.log ( 2 * n ) / Real.log geom_base ) ]

/-
If there are many even numbers in the middle range, one geometric interval contains at least 3 of them.
-/
lemma exists_interval_with_three_evens (n d : ℕ) (A : Finset ℤ)
    (hn : n ≥ 2) (hd : d ≥ 10)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (I : Finset ℤ) (hI_def : I = Finset.Icc ⌈6.5 * (d : ℝ)⌉ ⌊2 * (n : ℝ) - 6.5 * (d : ℝ)⌋)
    (h_many_evens : ((A.filter (fun x => x ∈ I ∧ Even x)).card : ℝ) ≥ 100 * Real.log (n : ℝ)) :
    ∃ j : ℕ,
      let lower := (geom_base ^ j : ℝ)
      let upper := (geom_base ^ (j + 1) : ℝ)
      let S := (A.filter (fun x => x ∈ I ∧ Even x)).filter (fun x => (x : ℝ) ≥ lower ∧ (x : ℝ) < upper)
      S.card ≥ 3 := by
        by_contra h_contra;
        -- Let $j₁$ and $j₂$ be the bounds for the geometric intervals covering $[6.5d, 2n]$.
        obtain ⟨j₁, j₂, hj₁, hj₂⟩ : ∃ j₁ j₂ : ℤ, (geom_base ^ j₁ : ℝ) ≤ 6.5 * d ∧ 2 * n < (geom_base ^ j₂ : ℝ) ∧ j₂ - j₁ < 50 * Real.log n := by
          refine' ⟨ ⌊Real.logb geom_base ( 6.5 * d ) ⌋, ⌈Real.logb geom_base ( 2 * n ) ⌉, _, _, _ ⟩;
          · have := Int.floor_le ( Real.logb geom_base ( 6.5 * d ) ) ; rw [ Real.le_logb_iff_rpow_le ] at this <;> norm_cast at * ;
            · exact show ( 1 : ℝ ) < 1.03 by norm_num;
            · positivity;
          · have := Int.le_ceil ( Real.logb geom_base ( 2 * n ) ) ; rw [ Real.logb_le_iff_le_rpow ] at this <;> norm_num at * <;> try linarith;
            · refine' lt_of_le_of_ne this _;
              intro h; norm_num [ geom_base ] at h;
              rcases x : ⌈Real.logb ( 103 / 100 ) ( 2 * n ) ⌉ with ( _ | _ | k ) <;> norm_num [ x ] at *;
              · rw [ div_pow, eq_div_iff ] at h <;> norm_cast at * ; have := congr_arg ( · % 100 ) h ; norm_num [ Nat.mul_mod, Nat.pow_mod ] at this;
                · replace h := congr_arg ( · % 2 ) h ; norm_num [ Nat.mul_mod, Nat.pow_mod ] at h;
                · positivity;
              · linarith [ show ( n : ℝ ) ≥ 2 by norm_cast ];
              · exact absurd h ( by exact ne_of_gt ( lt_of_lt_of_le ( inv_lt_one_of_one_lt₀ ( one_lt_pow₀ ( by norm_num ) ( by linarith ) ) ) ( by norm_cast; linarith ) ) );
            · exact show 1 < 1.03 by norm_num;
          · convert geometric_intervals_count_bound n d ( by linarith ) ( by linarith ) using 1;
        -- Let $U$ be the union of all geometric intervals $J_j$ for $j₁ \le j < j₂$.
        set U := Finset.Ico j₁ j₂;
        -- Since the union of $J_j$ covers $I$, $S_{total} \subseteq \bigcup U$.
        have h_union : (A.filter (fun x => x ∈ I ∧ Even x)) ⊆ Finset.biUnion U (fun j => Finset.filter (fun x => (geom_base ^ j : ℝ) ≤ x ∧ x < (geom_base ^ (j + 1) : ℝ)) (A.filter (fun x => x ∈ I ∧ Even x))) := by
          intro x hx; simp_all +decide [ Finset.subset_iff ] ;
          have h_log : j₁ ≤ Int.floor (Real.logb geom_base x) ∧ Int.floor (Real.logb geom_base x) < j₂ := by
            constructor;
            · refine' Int.le_floor.mpr _;
              rw [ Real.le_logb_iff_rpow_le ] <;> norm_cast;
              · exact le_trans hj₁ ( by exact le_trans ( by norm_num ) ( Int.le_ceil _ |> le_trans <| mod_cast hx.2.1.1 ) );
              · exact show ( 1 : ℝ ) < 1.03 by norm_num;
              · linarith [ hA_subset hx.1 ];
            · rw [ Int.floor_lt, Real.logb_lt_iff_lt_rpow ] <;> norm_num;
              · refine' lt_of_le_of_lt _ hj₂.1;
                exact_mod_cast hA_subset hx.1 |>.2;
              · exact show ( 1 : ℝ ) < 1.03 by norm_num;
              · linarith [ hA_subset hx.1 ];
          use Int.floor (Real.logb geom_base x);
          exact ⟨ Finset.mem_Ico.mpr h_log, by have := Int.floor_le ( Real.logb geom_base x ) ; rw [ Real.le_logb_iff_rpow_le ( by norm_num [ geom_base ] ) ( by norm_cast; linarith [ hA_subset hx.1 ] ) ] at this; exact_mod_cast this, by have := Int.lt_floor_add_one ( Real.logb geom_base x ) ; rw [ Real.logb_lt_iff_lt_rpow ( by norm_num [ geom_base ] ) ( by norm_cast; linarith [ hA_subset hx.1 ] ) ] at this; exact_mod_cast this ⟩;
        have := Finset.card_le_card h_union;
        refine' this.not_gt ( lt_of_le_of_lt ( Finset.card_biUnion_le ) _ );
        refine' lt_of_le_of_lt ( Finset.sum_le_sum fun x hx => show Finset.card _ ≤ 2 from _ ) _;
        · simp +zetaDelta at *;
          convert Nat.le_of_lt_succ ( h_contra ( Int.toNat x ) ) using 1;
          rw [ Finset.card_filter, Finset.card_filter ];
          refine' Finset.sum_bij ( fun y hy => y ) _ _ _ _ <;> norm_num;
          cases x <;> norm_num at *;
          · exact fun a_2 a_3 a_4 a_5 => rfl;
          · norm_num [ Int.negSucc_eq, zpow_add₀, zpow_one ] at *;
            intro x hx₁ hx₂ hx₃; split_ifs <;> norm_num at *;
            · rename_i k hk₁ hk₂;
              exact absurd hk₁.2 ( by exact not_lt_of_ge <| le_trans ( inv_le_one_of_one_le₀ <| one_le_pow₀ <| by norm_num [ geom_base ] ) <| mod_cast Finset.mem_Icc.mp ( hA_subset hx₁ ) |>.1 );
            · norm_num [ hI_def ] at hx₂;
              norm_num [ Int.ceil_le, Int.le_floor ] at hx₂;
              norm_num [ geom_base ] at * ; linarith [ show ( d : ℝ ) ≥ 10 by norm_cast ];
        · norm_num +zetaDelta at *;
          rw [ ← @Nat.cast_lt ℝ ] ; norm_num;
          refine' lt_of_lt_of_le _ h_many_evens;
          cases max_cases ( j₂ - j₁ ) 0 <;> simp_all +decide;
          · rw [ show ( Int.toNat ( j₂ - j₁ ) : ℝ ) = j₂ - j₁ by exact_mod_cast Int.toNat_of_nonneg ( sub_nonneg.mpr ‹_› ) ] ; linarith;
          · norm_num [ Int.toNat_of_nonpos ( by linarith : j₂ - j₁ ≤ 0 ) ];
            exact Real.log_pos <| Nat.one_lt_cast.mpr hn

/-
Given three sorted even integers, we can find $b_1, b_2, b_3$ summing to them.
-/
lemma exists_b_of_a (a₁ a₂ a₃ : ℤ) (h_sort : a₁ < a₂) (h_sort2 : a₂ < a₃)
    (h_even : Even a₁ ∧ Even a₂ ∧ Even a₃) :
    ∃ b₁ b₂ b₃ : ℤ,
      b₁ < b₂ ∧ b₂ < b₃ ∧
      b₁ + b₂ = a₁ ∧ b₁ + b₃ = a₂ ∧ b₂ + b₃ = a₃ ∧
      (b₁ % 2 = b₂ % 2) ∧ (b₂ % 2 = b₃ % 2) := by
        -- By solving the system of linear equations given by the sums, we can find the values of $b₁$, $b₂$, and $b₃$.
        use (a₁ + a₂ - a₃) / 2, (a₁ + a₃ - a₂) / 2, (a₂ + a₃ - a₁) / 2;
        cases h_even.1 ; cases h_even.2.1 ; cases h_even.2.2 ; omega

/-
Each integer appears at most 3 times in the set of sums across all pairs, given $p < q$.
-/
lemma bad_values_bound (b₁ b₂ b₃ a₁ : ℤ) (p_min : ℤ) (d : ℕ) (x : ℤ)
    (hb_distinct : b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃)
    (h_p_lt_q : ∀ k ∈ Finset.range (3 * d + 1), p_min + 2 * k < a₁ - (p_min + 2 * k)) :
    (Finset.filter (fun k => x ∈ ({b₁ + (p_min + 2 * k), b₂ + (p_min + 2 * k), b₃ + (p_min + 2 * k), b₁ + (a₁ - (p_min + 2 * k)), b₂ + (a₁ - (p_min + 2 * k)), b₃ + (a₁ - (p_min + 2 * k))} : Finset ℤ)) (Finset.range (3 * d + 1))).card ≤ 3 := by
      -- Let $K$ be the set of valid $k$.
      set K := Finset.filter (fun k => x ∈ ({b₁ + (p_min + 2 * k), b₂ + (p_min + 2 * k), b₃ + (p_min + 2 * k), b₁ + (a₁ - (p_min + 2 * k)), b₂ + (a₁ - (p_min + 2 * k)), b₃ + (a₁ - (p_min + 2 * k))} : Finset ℤ)) (Finset.range (3 * d + 1));
      -- Let $S_P = \{i \mid 2b_i > 2x - a_1\}$ and $S_Q = \{j \mid 2b_j < 2x - a_1\}$.
      set S_P := Finset.filter (fun i => 2 * (if i = 0 then b₁ else if i = 1 then b₂ else b₃) > 2 * x - a₁) (Finset.range 3)
      set S_Q := Finset.filter (fun j => 2 * (if j = 0 then b₁ else if j = 1 then b₂ else b₃) < 2 * x - a₁) (Finset.range 3);
      -- Each $i \in S_P$ contributes at most 1 $k$ (since $p_k$ is unique).
      have h_S_P : K.card ≤ S_P.card + S_Q.card := by
        have h_S_P : ∀ k ∈ K, ∃ i ∈ S_P ∪ S_Q, (if i = 0 then b₁ else if i = 1 then b₂ else b₃) + (if i ∈ S_P then p_min + 2 * k else a₁ - (p_min + 2 * k)) = x := by
          simp +zetaDelta at *;
          intro a ha hx; use if x = b₁ + ( p_min + 2 * a ) then 0 else if x = b₂ + ( p_min + 2 * a ) then 1 else if x = b₃ + ( p_min + 2 * a ) then 2 else if x = b₁ + ( a₁ - ( p_min + 2 * a ) ) then 0 else if x = b₂ + ( a₁ - ( p_min + 2 * a ) ) then 1 else 2; simp +decide ;
          grind +ring;
        choose! f hf using h_S_P;
        have h_S_P : Finset.card (Finset.image f K) ≤ S_P.card + S_Q.card := by
          exact le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun k hk => hf k hk |>.1 ) ( Finset.card_union_le _ _ );
        rwa [ Finset.card_image_of_injOn ] at h_S_P ; intro k hk l hl hkl ; have := hf k hk ; have := hf l hl ; simp_all +decide [Finset.mem_union] ;
        grind +ring;
      -- Since $S_P$ and $S_Q$ are disjoint subsets of $\{0, 1, 2\}$, their union has cardinality at most 3.
      have h_union_card : S_P.card + S_Q.card ≤ 3 := by
        rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr <| by intros; linarith ) ] ; exact le_trans ( Finset.card_le_card <| Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) ) ( by norm_num ) ;
      linarith

/-
The number of indices $k$ where the sums intersect $M$ is at most $3|M|$.
-/
lemma bad_indices_count (d : ℕ) (b₁ b₂ b₃ a₁ : ℤ) (p_min : ℤ)
    (hb_distinct : b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃)
    (h_p_lt_q : ∀ k ∈ Finset.range (3 * d + 1), p_min + 2 * k < a₁ - (p_min + 2 * k))
    (M : Finset ℤ) :
    (Finset.filter (fun k => ({b₁ + (p_min + 2 * k), b₂ + (p_min + 2 * k), b₃ + (p_min + 2 * k), b₁ + (a₁ - (p_min + 2 * k)), b₂ + (a₁ - (p_min + 2 * k)), b₃ + (a₁ - (p_min + 2 * k))} : Finset ℤ) ∩ M ≠ ∅) (Finset.range (3 * d + 1))).card ≤ 3 * M.card := by
      have h_card : ∀ m ∈ M, (Finset.filter (fun k => m ∈ ({b₁ + (p_min + 2 * k), b₂ + (p_min + 2 * k), b₃ + (p_min + 2 * k), b₁ + (a₁ - (p_min + 2 * k)), b₂ + (a₁ - (p_min + 2 * k)), b₃ + (a₁ - (p_min + 2 * k))} : Finset ℤ)) (Finset.range (3 * d + 1))).card ≤ 3 := by
        intro m hm; convert bad_values_bound b₁ b₂ b₃ a₁ p_min d m hb_distinct h_p_lt_q using 1;
      convert Finset.card_biUnion_le.trans ( Finset.sum_le_card_nsmul _ _ _ h_card ) using 1;
      · congr with k ; simp +decide [ Finset.ext_iff ];
        grind;
      · norm_num [ mul_comm ]

/-
If there are $3d+1$ pairs and at most $d$ missing odd numbers, one pair works.
-/
lemma valid_pair_exists (n d : ℕ) (A : Finset ℤ)
    (_hn : n ≥ 1) (_hd : d ≥ 10)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (hA_odd_count : (A.filter Odd).card ≥ n - d)
    (a₁ : ℤ) (b₁ b₂ b₃ : ℤ)
    (hb_sum : b₁ + b₂ = a₁)
    (hb_ord : b₁ < b₂ ∧ b₂ < b₃)
    (hb_parity : b₁ % 2 = b₂ % 2 ∧ b₂ % 2 = b₃ % 2)
    (p_min p_max : ℤ)
    (hp_range : p_max - p_min + 1 = 3 * d + 1)
    (h_pairs : ∀ k ∈ Finset.range (3 * d + 1),
        let p := p_min + 2 * k
        let q := a₁ - p
        p < q ∧
        p % 2 ≠ b₁ % 2 ∧
        (∀ i ∈ ({b₁, b₂, b₃} : Finset ℤ), 1 ≤ i + p ∧ i + q ≤ 2 * n)) :
    ∃ k ∈ Finset.range (3 * d + 1),
      let p := p_min + 2 * k
      let q := a₁ - p
      {b₁ + p, b₂ + p, b₃ + p, b₁ + q, b₂ + q, b₃ + q} ⊆ A := by
        -- By `bad_indices_count`, $|B| \le 3|M| \le 3d$.
        have h_bad_pairs_card : (Finset.filter (fun k : ℕ => (∃ x ∈ ({b₁ + (p_min + 2 * k), b₂ + (p_min + 2 * k), b₃ + (p_min + 2 * k), b₁ + (a₁ - (p_min + 2 * k)), b₂ + (a₁ - (p_min + 2 * k)), b₃ + (a₁ - (p_min + 2 * k))} : Finset ℤ), ¬x ∈ A)) (Finset.range (3 * d + 1))).card ≤ 3 * d := by
          -- By `bad_indices_count`, $|B| \le 3|M| \le 3d$. Since $|K| = 3d+1$, there exists $k \in K \setminus B$.
          have h_bad_indices_count : (Finset.filter (fun k : ℕ => (∃ x ∈ ({b₁ + (p_min + 2 * k), b₂ + (p_min + 2 * k), b₃ + (p_min + 2 * k), b₁ + (a₁ - (p_min + 2 * k)), b₂ + (a₁ - (p_min + 2 * k)), b₃ + (a₁ - (p_min + 2 * k))} : Finset ℤ), ¬x ∈ A)) (Finset.range (3 * d + 1))).card ≤ 3 * (Finset.filter (fun x => ¬x ∈ A) (Finset.filter Odd (Finset.Icc 1 (2 * n)))).card := by
            convert bad_indices_count d b₁ b₂ b₃ a₁ p_min ⟨ by linarith, by linarith, by linarith ⟩ _ _ using 1;
            · refine' Finset.card_bij ( fun k hk => k ) _ _ _ <;> simp +decide [ Finset.ext_iff ];
              · intro a ha hk; specialize h_pairs a ( Finset.mem_range.mpr ha ) ; simp_all +decide ;
                grind +ring;
              · grind +ring;
            · exact fun k hk => h_pairs k hk |>.1;
          -- The total number of odd integers in the range [1, 2n] is n.
          have h_total_odd : (Finset.filter Odd (Finset.Icc 1 (2 * n))).card = n := by
            rw [ Finset.card_eq_of_bijective ];
            use fun i hi => 2 * i + 1;
            · exact fun x hx => by obtain ⟨ k, rfl ⟩ := Finset.mem_filter.mp hx |>.2; exact ⟨ k, by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ], rfl ⟩ ;
            · exact fun i hi => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, by simp +decide [ parity_simps ] ⟩;
            · grind;
          have h_total_odd : (Finset.filter Odd (Finset.Icc 1 (2 * n))).card = (Finset.filter (fun x => x ∈ A) (Finset.filter Odd (Finset.Icc 1 (2 * n)))).card + (Finset.filter (fun x => ¬x ∈ A) (Finset.filter Odd (Finset.Icc 1 (2 * n)))).card := by
            rw [ Finset.filter_card_add_filter_neg_card_eq_card ];
            refine' Finset.card_bij ( fun x hx => Int.natAbs x ) _ _ _ <;> norm_num;
            · exact fun a ha₁ ha₂ ha₃ => ⟨ ⟨ mod_cast ha₁, mod_cast ha₂ ⟩, mod_cast ha₃ ⟩;
            · exact fun b hb₁ hb₂ hb₃ => ⟨ Int.natAbs b, ⟨ ⟨ by linarith [ abs_of_nonneg ( by linarith : 0 ≤ b ) ], by linarith [ abs_of_nonneg ( by linarith : 0 ≤ b ) ] ⟩, by simpa [ ← Int.odd_iff ] using hb₃ ⟩, by simp +decide [ abs_of_nonneg ( by linarith : 0 ≤ b ) ] ⟩ ;
          have h_total_odd : (Finset.filter (fun x => x ∈ A) (Finset.filter Odd (Finset.Icc 1 (2 * n)))).card = (Finset.filter Odd A).card := by
            congr 1 with x ; simp +contextual;
            exact ⟨ fun hx => ⟨ hx.2, hx.1.2 ⟩, fun hx => ⟨ ⟨ Finset.mem_Icc.mp ( hA_subset hx.1 ), hx.2 ⟩, hx.1 ⟩ ⟩;
          omega;
        contrapose! h_bad_pairs_card;
        rw [ Finset.filter_true_of_mem ] <;> simp_all +decide [ Finset.subset_iff ];
        grind +ring

/-
If $y \ge 1$ and $t \ge 128^{1/4}y^{15/16} + y^{11/16} + 1$, then $\frac{t(t-1)}{4y} \ge \sqrt{8}y^{7/8} + y^{5/8} + 2$.
-/
lemma gcesthree_bound_check (y : ℝ) (hy : y ≥ 1) (t : ℝ)
    (ht : t ≥ 128^(0.25 : ℝ) * y^(0.9375 : ℝ) + y^(0.6875 : ℝ) + 1) :
    t * (t - 1) / (4 * y) ≥ Real.sqrt 8 * y^(0.875 : ℝ) + y^(0.625 : ℝ) + 2 := by
      -- Multiply both sides to clear the fractions.
      suffices h_clear : (t * (t - 1)) ≥ 4 * y * ((Real.sqrt 8) * (y ^ (0.875 : ℝ)) + (y ^ (0.625 : ℝ)) + 2) by
        rwa [ ge_iff_le, le_div_iff₀' ( by positivity ) ];
      -- Let's simplify the inequality. We observe:
      -- $(128^{1/4} y^{15/16} + y^{11/16} + 1)(128^{1/4} y^{15/16} + y^{11/16}) \geq 4y(\sqrt{8} y^{7/8} + y^{5/8} + 2)$.
      have h_simplify : (128^(1 / 4 : ℝ) * y^(15 / 16 : ℝ) + y^(11 / 16 : ℝ) + 1) * (128^(1 / 4 : ℝ) * y^(15 / 16 : ℝ) + y^(11 / 16 : ℝ)) ≥ 4 * y * (Real.sqrt 8 * y^(7 / 8 : ℝ) + y^(5 / 8 : ℝ) + 2) := by
        -- Substitute $z = y^{1/16}$ into the inequality.
        set z : ℝ := y^(1 / 16 : ℝ)
        have hz : z ≥ 1 := by
          exact Real.one_le_rpow hy ( by norm_num )
        have h_sub : (128^(1 / 4 : ℝ) * z^15 + z^11 + 1) * (128^(1 / 4 : ℝ) * z^15 + z^11) ≥ 4 * z^16 * (Real.sqrt 8 * z^14 + z^10 + 2) := by
          rw [ show ( 128 : ℝ ) = 2 ^ 7 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ; ring_nf at * ; norm_num at *;
          rw [ show ( 2 : ℝ ) ^ ( 7 / 4 : ℝ ) = 2 * 2 ^ ( 3 / 4 : ℝ ) by rw [ ← Real.rpow_one_add' ] <;> norm_num ] ; ring_nf ; norm_num;
          rw [ show ( 8 : ℝ ) = 4 * 2 by norm_num, Real.sqrt_mul ( by norm_num ) ] ; ring_nf ; norm_num;
          rw [ show ( 2 : ℝ ) ^ ( 3 / 4 : ℝ ) = 2 ^ ( 1 / 4 : ℝ ) * 2 ^ ( 1 / 2 : ℝ ) by rw [ ← Real.rpow_add ] <;> norm_num ] ; ring_nf ; norm_num;
          norm_num [ sq, ← Real.rpow_add ] ; ring_nf ; norm_num at *;
          norm_num [ ← Real.sqrt_eq_rpow ] at *;
          -- Since $z \geq 1$, we have $2^{1/4} \sqrt{2} \geq 1.68$.
          have h_const : (2 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt 2 ≥ 1.68 := by
            rw [ show ( 2 : ℝ ) ^ ( 1 / 4 : ℝ ) = Real.sqrt ( Real.sqrt 2 ) by rw [ Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ] <;> norm_num ] ; norm_num [ Real.sqrt_le_iff ];
            rw [ ← Real.sqrt_mul <| by positivity ] ; exact Real.le_sqrt_of_sq_le <| by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
          field_simp;
          nlinarith [ pow_le_pow_left₀ zero_le_one hz 4, pow_le_pow_left₀ zero_le_one hz 5, pow_le_pow_left₀ zero_le_one hz 6, pow_le_pow_left₀ zero_le_one hz 7, pow_le_pow_left₀ zero_le_one hz 8, pow_le_pow_left₀ zero_le_one hz 9, pow_le_pow_left₀ zero_le_one hz 10, pow_le_pow_left₀ zero_le_one hz 11, pow_le_pow_left₀ zero_le_one hz 12, pow_le_pow_left₀ zero_le_one hz 13, pow_le_pow_left₀ zero_le_one hz 14, pow_le_pow_left₀ zero_le_one hz 15 ];
        convert h_sub using 1 <;> push_cast [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity : 0 ≤ y ) ] <;> norm_num;
        · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num [ z ] ;
        · repeat rw [ ← Real.rpow_natCast ] ; repeat rw [ ← Real.rpow_mul ( by positivity ) ] ; norm_num;
      generalize_proofs at *; (
      norm_num at * ; nlinarith [ show 0 < ( 128 : ℝ ) ^ ( 1 / 4 : ℝ ) * y ^ ( 15 / 16 : ℝ ) by positivity, show 0 < y ^ ( 11 / 16 : ℝ ) by positivity ] ;)

/-
In a disjoint matching with difference $m$, the difference between any two left endpoints is not $m$.
-/
lemma matching_diff_ne_m_v2 (t : ℕ) (y : Fin t → ℤ) (m : ℤ) (hm : m ≠ 0)
    (M : Finset (Fin t × Fin t))
    (h_diff : ∀ p ∈ M, y p.2 - y p.1 = m)
    (h_disj : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset (Fin t)) ∩ {q.1, q.2} = ∅)
    (h_mono : StrictMono y)
    (p q : Fin t × Fin t) (hp : p ∈ M) (hq : q ∈ M) :
    y q.1 - y p.1 ≠ m := by
      by_contra h_contra;
      -- Since $y$ is strictly monotone, it is injective, so $q.1 = p.2$.
      have h_eq : q.1 = p.2 := by
        exact h_mono.injective ( by linarith [ h_diff p hp, h_diff q hq ] );
      specialize h_disj p hp q hq ; simp_all +decide [ Finset.ext_iff ];
      grind

open Finset

lemma gcesthree_of_matching (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (m : ℤ) (hm : m > 0)
    (M : Finset (Fin t × Fin t))
    (h_diff : ∀ p ∈ M, y p.2 - y p.1 = m)
    (h_ord : ∀ p ∈ M, p.1 < p.2)
    (h_disj : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset (Fin t)) ∩ {q.1, q.2} = ∅)
    (h_card : (M.card : ℝ) ≥ Real.sqrt 8 * (y ⟨t-1, Nat.sub_lt ht zero_lt_one⟩ - y ⟨0, lt_of_lt_of_le zero_lt_one ht⟩ : ℝ)^(0.875 : ℝ) + (y ⟨t-1, Nat.sub_lt ht zero_lt_one⟩ - y ⟨0, lt_of_lt_of_le zero_lt_one ht⟩ : ℝ)^(0.625 : ℝ) + 2)
    (h_mono : StrictMono y)
    (h_y_ge_1 : y ⟨t-1, Nat.sub_lt ht zero_lt_one⟩ - y ⟨0, lt_of_lt_of_le zero_lt_one ht⟩ ≥ 1) :
    ∃ x₁ x₂ x₃ x₄ x₅ x₆, x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₄ ≠ 0 ∧ x₅ ≠ 0 ∧ x₆ ≠ 0 ∧
    x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₂ ≠ x₅ ∧ x₂ ≠ x₆ ∧
    x₃ ≠ x₄ ∧ x₃ ≠ x₅ ∧ x₃ ≠ x₆ ∧
    x₄ ≠ x₅ ∧ x₄ ≠ x₆ ∧
    x₅ ≠ x₆ ∧
    {x₁, x₁ + x₂, x₁ + x₃, x₁ + x₄, x₁ + x₅, x₁ + x₆,
     x₁ + x₂ + x₃, x₁ + x₂ + x₄, x₁ + x₂ + x₅, x₁ + x₂ + x₆,
     x₁ + x₃ + x₄, x₁ + x₃ + x₅, x₁ + x₃ + x₆,
     x₁ + x₄ + x₅, x₁ + x₄ + x₆,
     x₁ + x₅ + x₆,
     x₁ + x₂ + x₃ + x₄, x₁ + x₂ + x₃ + x₅, x₁ + x₂ + x₃ + x₆,
     x₁ + x₂ + x₄ + x₅, x₁ + x₂ + x₄ + x₆,
     x₁ + x₂ + x₅ + x₆,
     x₁ + x₃ + x₄ + x₅, x₁ + x₃ + x₄ + x₆,
     x₁ + x₃ + x₅ + x₆,
     x₁ + x₄ + x₅ + x₆,
     x₁ + x₂ + x₃ + x₄ + x₅, x₁ + x₂ + x₃ + x₄ + x₆,
     x₁ + x₂ + x₃ + x₅ + x₆,
     x₁ + x₂ + x₄ + x₅ + x₆,
     x₁ + x₃ + x₄ + x₅ + x₆,
     x₁ + x₂ + x₃ + x₄ + x₅ + x₆} ⊆ Set.range y := by
       revert @ h_card;
       intro h_card
       set S := M.image Prod.fst with hS_def
       have hS_card : S.card = M.card := by
         rw [ Finset.card_image_of_injOn ] ; intro p hp q hq ; specialize h_disj p hp q hq ; aesop;
       have hS_mono : StrictMono (fun i : Fin S.card => y (S.orderEmbOfFin rfl i)) := by
         exact h_mono.comp ( by aesop_cat )
       have hS_range : (y (S.orderEmbOfFin rfl (Fin.mk (S.card - 1) (by
       exact Nat.pred_lt ( ne_bot_of_gt ( hS_card.symm ▸ Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ( by rintro h; norm_num [ h ] at h_card; nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ), show ( y ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ - y ⟨ 0, by linarith ⟩ : ℝ ) ^ ( 0.875 : ℝ ) > 0 by exact Real.rpow_pos_of_pos ( mod_cast h_y_ge_1.trans_lt' <| by norm_num ) _, show ( y ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ - y ⟨ 0, by linarith ⟩ : ℝ ) ^ ( 0.625 : ℝ ) > 0 by exact Real.rpow_pos_of_pos ( mod_cast h_y_ge_1.trans_lt' <| by norm_num ) _ ] ) ) ) ))) ) - y (S.orderEmbOfFin rfl ⟨0, by
         norm_num +zetaDelta at *;
         exact Finset.card_pos.mp ( Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at h_card; exact absurd h_card ( by nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ), Real.rpow_pos_of_pos ( show 0 < ( y ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ - y ⟨ 0, by linarith ⟩ : ℝ ) by exact_mod_cast h_y_ge_1 ) ( 7 / 8 : ℝ ), Real.rpow_pos_of_pos ( show 0 < ( y ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ - y ⟨ 0, by linarith ⟩ : ℝ ) by exact_mod_cast h_y_ge_1 ) ( 5 / 8 : ℝ ) ] ) ) )⟩) : ℝ) ≤ (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ) := by
         gcongr;
         · exact h_mono.monotone ( Nat.le_pred_of_lt <| Fin.is_lt _ );
         · exact h_mono.monotone ( Nat.zero_le _ )
       generalize_proofs at *;
       -- Apply `gcestwo` to $z$.
       obtain ⟨x₁, x₂, x₃, x₄, x₅, hx⟩ : ∃ x₁ x₂ x₃ x₄ x₅ : ℤ,
         x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₄ ≠ 0 ∧ x₅ ≠ 0 ∧
         x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₂ ≠ x₅ ∧ x₃ ≠ x₄ ∧ x₃ ≠ x₅ ∧ x₄ ≠ x₅ ∧
         {x₁, x₁ + x₂, x₁ + x₃, x₁ + x₄, x₁ + x₅,
          x₁ + x₂ + x₃, x₁ + x₂ + x₄, x₁ + x₂ + x₅, x₁ + x₃ + x₄, x₁ + x₃ + x₅, x₁ + x₄ + x₅,
          x₁ + x₂ + x₃ + x₄, x₁ + x₂ + x₃ + x₅, x₁ + x₂ + x₄ + x₅, x₁ + x₃ + x₄ + x₅,
          x₁ + x₂ + x₃ + x₄ + x₅} ⊆ Set.range (fun i : Fin S.card => y (S.orderEmbOfFin rfl i)) := by
            apply gcestwo;
            any_goals omega;
            · refine le_trans ?_ ( h_card.trans ?_ );
              · gcongr;
                · exact sub_nonneg_of_le <| mod_cast hS_mono.monotone <| Nat.zero_le _;
                · exact sub_nonneg_of_le <| mod_cast hS_mono.monotone <| Nat.zero_le _;
              · rw [ hS_card ];
            · refine' le_tsub_of_add_le_left _;
              refine' h_mono _;
              simp +decide ;
              contrapose! h_card;
              exact lt_add_of_pos_of_le ( by exact add_pos_of_pos_of_nonneg ( mul_pos ( Real.sqrt_pos.mpr ( by norm_num ) ) ( Real.rpow_pos_of_pos ( by norm_cast ) _ ) ) ( Real.rpow_nonneg ( by norm_cast; linarith ) _ ) ) ( by norm_cast; linarith );
       use x₁, x₂, x₃, x₄, x₅, m;
       refine' ⟨ hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hm.ne', hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1, _, hx.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.1, _, hx.2.2.2.2.2.2.2.2.2.1, _, _, _ ⟩;
       · intro h_eq_m
         have h_diff_zero : ∃ p q : Fin S.card, p ≠ q ∧ y (S.orderEmbOfFin rfl p) - y (S.orderEmbOfFin rfl q) = m := by
           obtain ⟨ p, hp ⟩ := hx.2.2.2.2.2.2.2.2.2.2.subset ( show x₁ + x₂ ∈ _ from by simp +decide ) ; obtain ⟨ q, hq ⟩ := hx.2.2.2.2.2.2.2.2.2.2.subset ( show x₁ ∈ _ from by simp +decide ) ; use p, q; aesop;
         generalize_proofs at *;
         obtain ⟨ p, q, hpq, h ⟩ := h_diff_zero;
         have h_diff_zero : ∃ p' q' : Fin t × Fin t, p' ∈ M ∧ q' ∈ M ∧ p' ≠ q' ∧ y p'.1 - y q'.1 = m := by
           obtain ⟨ p', hp' ⟩ := Finset.mem_image.mp ( show ( S.orderEmbOfFin rfl p ) ∈ S from Finset.orderEmbOfFin_mem _ _ _ ) ; obtain ⟨ q', hq' ⟩ := Finset.mem_image.mp ( show ( S.orderEmbOfFin rfl q ) ∈ S from Finset.orderEmbOfFin_mem _ _ _ ) ; use p', q'; aesop;
         generalize_proofs at *;
         obtain ⟨ p', q', hp', hq', hpq', h ⟩ := h_diff_zero; have := matching_diff_ne_m_v2 t y m hm.ne' M h_diff h_disj h_mono p' q'; simp_all +decide [ sub_eq_iff_eq_add ] ;
         specialize h_disj _ _ hp' _ _ hq' ; simp_all +decide [ Finset.ext_iff ];
         specialize h_disj ( by aesop ) ; have := h_mono.injective ( by linarith [ h_diff _ _ hp', h_diff _ _ hq' ] : y p'.1 = y q'.2 ) ; aesop;
       · intro h_eq_m
         generalize_proofs at *;
         -- Since $x₃ = m$, there exist $i, j \in \text{Fin } S.card$ such that $y (S.orderEmbOfFin rfl i) - y (S.orderEmbOfFin rfl j) = m$.
         obtain ⟨i, j, hij, h_diff_eq⟩ : ∃ i j : Fin S.card, i ≠ j ∧ y (S.orderEmbOfFin rfl i) - y (S.orderEmbOfFin rfl j) = m := by
           have h_diff_eq : ∃ i j : Fin S.card, y (S.orderEmbOfFin rfl i) - y (S.orderEmbOfFin rfl j) = x₃ := by
             have := hx.2.2.2.2.2.2.2.2.2.2 ( show x₁ + x₃ ∈ _ from by simp +decide ) ; obtain ⟨ i, hi ⟩ := this; ( have := hx.2.2.2.2.2.2.2.2.2.2 ( show x₁ ∈ _ from by simp +decide ) ; obtain ⟨ j, hj ⟩ := this; use i, j; linarith; )
           generalize_proofs at *;
           obtain ⟨ i, j, h ⟩ := h_diff_eq; exact ⟨ i, j, by rintro rfl; linarith, by linarith ⟩ ;
         generalize_proofs at *;
         -- Since $i \neq j$, we have $y (S.orderEmbOfFin rfl i) \neq y (S.orderEmbOfFin rfl j)$.
         obtain ⟨p, hp⟩ : ∃ p ∈ M, S.orderEmbOfFin rfl i = p.1 := by
           have := Finset.mem_image.mp ( Finset.orderEmbOfFin_mem ( Finset.image Prod.fst M ) ( by aesop ) i ) ; aesop;
         obtain ⟨q, hq⟩ : ∃ q ∈ M, S.orderEmbOfFin rfl j = q.1 := by
           have := Finset.mem_image.mp ( Finset.orderEmbOfFin_mem ( S ) rfl j ) ; aesop;
         generalize_proofs at *;
         have := h_diff p hp.1; have := h_diff q hq.1; simp_all +decide [ sub_eq_iff_eq_add ] ;
         exact absurd ( h_mono.injective ( by linarith : y p.1 = y q.2 ) ) ( by specialize h_disj _ _ hp.1 _ _ hq.1; aesop );
       · intro h_eq_m
         have h_diff_eq_m : ∃ p q : Fin S.card, p ≠ q ∧ y (S.orderEmbOfFin rfl q) - y (S.orderEmbOfFin rfl p) = m := by
           have h_subset_sum : x₁ + x₄ ∈ Set.range (fun i : Fin S.card => y (S.orderEmbOfFin rfl i)) := by
             grind
           generalize_proofs at *;
           have h_subset_sum : x₁ ∈ Set.range (fun i : Fin S.card => y (S.orderEmbOfFin rfl i)) := by
             exact hx.2.2.2.2.2.2.2.2.2.2.subset <| by simp +decide ;
           generalize_proofs at *;
           obtain ⟨ p, hp ⟩ := h_subset_sum
           obtain ⟨ q, hq ⟩ := ‹x₁ + x₄ ∈ Set.range (fun i : Fin S.card => y (S.orderEmbOfFin rfl i))›
           generalize_proofs at *;
           exact ⟨ p, q, by rintro rfl; linarith, by linarith ⟩
         generalize_proofs at *;
         obtain ⟨ p, q, hpq, h ⟩ := h_diff_eq_m
         generalize_proofs at *;
         have h_diff_eq_m : ∃ p' q' : Fin t × Fin t, p' ∈ M ∧ q' ∈ M ∧ p' ≠ q' ∧ y p'.2 - y p'.1 = m ∧ y q'.2 - y q'.1 = m ∧ y q'.1 - y p'.1 = m := by
           obtain ⟨ p', hp' ⟩ := Finset.mem_image.mp ( Finset.orderEmbOfFin_mem ( Finset.image Prod.fst M ) ( by aesop ) p )
           obtain ⟨ q', hq' ⟩ := Finset.mem_image.mp ( Finset.orderEmbOfFin_mem ( Finset.image Prod.fst M ) ( by aesop ) q )
           generalize_proofs at *;
           grind +ring
         generalize_proofs at *;
         obtain ⟨ p', q', hp', hq', hpq', hp, hq, h ⟩ := h_diff_eq_m; specialize h_disj p' hp' q' hq' hpq'; simp_all +decide [ Finset.ext_iff ] ;
         exact absurd ( h_mono.injective ( by linarith [ h_diff _ _ hp', h_diff _ _ hq' ] : y q'.1 = y p'.2 ) ) ( by aesop );
       · intro h_eq_m
         generalize_proofs at *;
         -- Since $x₅ = m$, there exist indices $i$ and $j$ such that $y (S.orderEmbOfFin rfl i) = x₁$ and $y (S.orderEmbOfFin rfl j) = x₁ + m$.
         obtain ⟨i, hi⟩ : ∃ i : Fin S.card, y (S.orderEmbOfFin rfl i) = x₁ := by
           exact hx.2.2.2.2.2.2.2.2.2.2.subset <| by simp +decide ;
         obtain ⟨j, hj⟩ : ∃ j : Fin S.card, y (S.orderEmbOfFin rfl j) = x₁ + m := by
           have := hx.2.2.2.2.2.2.2.2.2.2 ( show x₁ + m ∈ _ from by simp +decide [ h_eq_m ] ) ; aesop;
         generalize_proofs at *;
         -- Since $y$ is strictly monotone, we have $j > i$.
         have h_j_gt_i : j > i := by
           exact hS_mono.lt_iff_lt.mp ( by linarith );
         have h_contradiction : ∃ p q : Fin t × Fin t, p ∈ M ∧ q ∈ M ∧ p ≠ q ∧ y q.1 - y p.1 = m := by
           obtain ⟨p, hp⟩ : ∃ p ∈ M, p.1 = S.orderEmbOfFin rfl i := by
             have := Finset.mem_image.mp ( Finset.orderEmbOfFin_mem ( Finset.image Prod.fst M ) rfl i ) ; aesop;
           obtain ⟨q, hq⟩ : ∃ q ∈ M, q.1 = S.orderEmbOfFin rfl j := by
             have := Finset.mem_image.mp ( show ( S.orderEmbOfFin rfl j ) ∈ S from Finset.orderEmbOfFin_mem _ _ _ ) ; aesop;
           generalize_proofs at *;
           exact ⟨ p, q, hp.1, hq.1, by rintro rfl; exact h_j_gt_i.ne ( by aesop ), by aesop ⟩
         generalize_proofs at *;
         obtain ⟨ p, q, hp, hq, hpq, h ⟩ := h_contradiction; exact matching_diff_ne_m_v2 t y m hm.ne' M h_diff h_disj h_mono p q hp hq h;
       · intro x hx';
         by_cases hx'' : x = x₁ + m ∨ x = x₁ + x₂ + m ∨ x = x₁ + x₃ + m ∨ x = x₁ + x₄ + m ∨ x = x₁ + x₅ + m ∨ x = x₁ + x₂ + x₃ + m ∨ x = x₁ + x₂ + x₄ + m ∨ x = x₁ + x₂ + x₅ + m ∨ x = x₁ + x₃ + x₄ + m ∨ x = x₁ + x₃ + x₅ + m ∨ x = x₁ + x₄ + x₅ + m ∨ x = x₁ + x₂ + x₃ + x₄ + m ∨ x = x₁ + x₂ + x₃ + x₅ + m ∨ x = x₁ + x₂ + x₄ + x₅ + m ∨ x = x₁ + x₃ + x₄ + x₅ + m ∨ x = x₁ + x₂ + x₃ + x₄ + x₅ + m;
         · obtain ⟨ i, hi ⟩ := hx.2.2.2.2.2.2.2.2.2.2.subset ( show x - m ∈ _ from by
                                                                 simp +decide;
                                                                 grind );
           -- Since $S$ is the image of $M$'s first elements, and $M$ is a matching, each element in $S$ corresponds to a pair in $M$. Therefore, there exists some $p \in M$ such that $p.1 = S.orderEmbOfFin rfl i$.
           obtain ⟨ p, hpM, hp_eq ⟩ : ∃ p ∈ M, p.1 = S.orderEmbOfFin rfl i := by
             exact Finset.mem_image.mp ( Finset.orderEmbOfFin_mem ( Finset.image Prod.fst M ) ( by aesop ) i ) |> fun ⟨ p, hp₁, hp₂ ⟩ => ⟨ p, hp₁, hp₂ ⟩;
           exact ⟨ p.2, by linarith [ h_diff p hpM, show y p.1 = x - m from by simpa [ hp_eq ] using hi ] ⟩;
         · simp_all +decide [Set.subset_def];
           rcases hx' with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp_all +decide only;
           grind;
           grind;
           grind;
           grind;
           grind;
           grind;
           grind +ring;
           grind +ring;
           grind +ring;
           grind;
           grind;
           · grind +ring;
           · grind +ring;
           · grind +ring;
           · grind +ring;
           · grind +ring

/-
Let $y_1 < y_2 < \ldots < y_t$ be a sequence of integers and set $y := y_t - y_1$. If $t \ge 128^{1/4}y^{15/16} + y^{11/16} + 1$, then there exist integers $x_1, x_2, x_3, x_4, x_5, x_6$ with $x_2, x_3, x_4, x_5, x_6$ distinct such that the sequence contains all subset sums containing $x_1$.
-/
theorem gcesthree (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y)
    (h_bound : (t : ℝ) ≥ 128^(0.25 : ℝ) * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.9375 : ℝ) + (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.6875 : ℝ) + 1)
    (h_y_ge_1 : y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ ≥ 1) :
    ∃ x₁ x₂ x₃ x₄ x₅ x₆, x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₄ ≠ 0 ∧ x₅ ≠ 0 ∧ x₆ ≠ 0 ∧
    x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₂ ≠ x₅ ∧ x₂ ≠ x₆ ∧
    x₃ ≠ x₄ ∧ x₃ ≠ x₅ ∧ x₃ ≠ x₆ ∧
    x₄ ≠ x₅ ∧ x₄ ≠ x₆ ∧
    x₅ ≠ x₆ ∧
    {x₁, x₁ + x₂, x₁ + x₃, x₁ + x₄, x₁ + x₅, x₁ + x₆,
     x₁ + x₂ + x₃, x₁ + x₂ + x₄, x₁ + x₂ + x₅, x₁ + x₂ + x₆,
     x₁ + x₃ + x₄, x₁ + x₃ + x₅, x₁ + x₃ + x₆,
     x₁ + x₄ + x₅, x₁ + x₄ + x₆,
     x₁ + x₅ + x₆,
     x₁ + x₂ + x₃ + x₄, x₁ + x₂ + x₃ + x₅, x₁ + x₂ + x₃ + x₆,
     x₁ + x₂ + x₄ + x₅, x₁ + x₂ + x₄ + x₆,
     x₁ + x₂ + x₅ + x₆,
     x₁ + x₃ + x₄ + x₅, x₁ + x₃ + x₄ + x₆,
     x₁ + x₃ + x₅ + x₆,
     x₁ + x₄ + x₅ + x₆,
     x₁ + x₂ + x₃ + x₄ + x₅, x₁ + x₂ + x₃ + x₄ + x₆,
     x₁ + x₂ + x₃ + x₅ + x₆,
     x₁ + x₂ + x₄ + x₅ + x₆,
     x₁ + x₃ + x₄ + x₅ + x₆,
     x₁ + x₂ + x₃ + x₄ + x₅ + x₆} ⊆ Set.range y := by
       -- By Lemma `gcesthree_bound_check`, the matching size is at least $\sqrt{8}(y_{t-1}-y_0)^{0.875} + (y_{t-1}-y_0)^{0.625} + 2$.
       obtain ⟨M, m, hm_pos, hM_size⟩ : ∃ M : Finset (Fin t × Fin t), ∃ m : ℤ, m > 0 ∧ (∀ p ∈ M, y p.2 - y p.1 = m) ∧ (∀ p ∈ M, p.1 < p.2) ∧ (∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset (Fin t)) ∩ {q.1, q.2} = ∅) ∧ (M.card : ℝ) ≥ Real.sqrt 8 * (y ⟨t-1, Nat.sub_lt ht zero_lt_one⟩ - y ⟨0, lt_of_lt_of_le zero_lt_one ht⟩ : ℝ)^(0.875 : ℝ) + (y ⟨t-1, Nat.sub_lt ht zero_lt_one⟩ - y ⟨0, lt_of_lt_of_le zero_lt_one ht⟩ : ℝ)^(0.625 : ℝ) + 2 := by
         have h_match : ∃ M : Finset (Fin t × Fin t), ∃ m : ℤ, m > 0 ∧ (∀ p ∈ M, y p.2 - y p.1 = m) ∧ (∀ p ∈ M, p.1 < p.2) ∧ (∀ p ∈ M, ∀ q ∈ M, p ≠ q → ({p.1, p.2} : Finset (Fin t)) ∩ ({q.1, q.2} : Finset (Fin t)) = ∅) ∧ (M.card : ℝ) ≥ (t * (t - 1)) / (4 * (y ⟨t-1, Nat.sub_lt ht zero_lt_one⟩ - y ⟨0, lt_of_lt_of_le zero_lt_one ht⟩ : ℝ)) := by
           have := @gces_matching_size_bound;
           by_cases ht2 : t ≥ 2;
           · obtain ⟨ m, hm₁, M, hm₂, hm₃, hm₄, hm₅ ⟩ := this t ht2 y h_mono;
             exact ⟨ M, m, hm₁, hm₂, hm₃, hm₄, by rw [ ge_iff_le, div_le_iff₀ ] at * <;> nlinarith [ show ( y ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ : ℝ ) - y ⟨ 0, lt_of_lt_of_le zero_lt_one ht ⟩ ≥ 1 by exact_mod_cast h_y_ge_1 ] ⟩;
           · interval_cases t ; norm_num at *;
         have h_bound : (t * (t - 1)) / (4 * (y ⟨t-1, Nat.sub_lt ht zero_lt_one⟩ - y ⟨0, lt_of_lt_of_le zero_lt_one ht⟩ : ℝ)) ≥ Real.sqrt 8 * (y ⟨t-1, Nat.sub_lt ht zero_lt_one⟩ - y ⟨0, lt_of_lt_of_le zero_lt_one ht⟩ : ℝ)^(0.875 : ℝ) + (y ⟨t-1, Nat.sub_lt ht zero_lt_one⟩ - y ⟨0, lt_of_lt_of_le zero_lt_one ht⟩ : ℝ)^(0.625 : ℝ) + 2 := by
           convert gcesthree_bound_check ( y ⟨ t - 1, Nat.sub_lt ht zero_lt_one ⟩ - y ⟨ 0, lt_of_lt_of_le zero_lt_one ht ⟩ ) ( mod_cast h_y_ge_1 ) t ( mod_cast h_bound ) using 1;
         exact ⟨ h_match.choose, h_match.choose_spec.choose, h_match.choose_spec.choose_spec.1, h_match.choose_spec.choose_spec.2.1, h_match.choose_spec.choose_spec.2.2.1, h_match.choose_spec.choose_spec.2.2.2.1, h_bound.trans h_match.choose_spec.choose_spec.2.2.2.2 ⟩;
       apply gcesthree_of_matching t ht y m hm_pos M hM_size.left hM_size.right.left hM_size.right.right.left hM_size.right.right.right h_mono h_y_ge_1

/-
Let $y_1 < y_2 < \ldots < y_t$ be a sequence of even integers and set $y := y_t - y_1$. If $t \ge 128^{1/4}y^{15/16} + y^{11/16} + 1$, then distinct integers $b_1, b_2, b_3, b_4, b_5, b_6$ exist such that the sequence contains all pairwise sums $b_i + b_j$ with $1 \le i < j \le 6$.
-/
theorem corrothree (t : ℕ) (ht : 1 ≤ t) (y : Fin t → ℤ) (h_mono : StrictMono y)
    (h_even : ∀ i, Even (y i))
    (h_bound : (t : ℝ) ≥ 128^(0.25 : ℝ) * (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.9375 : ℝ) + (y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ : ℝ)^(0.6875 : ℝ) + 1)
    (h_y_ge_1 : y ⟨t-1, by omega⟩ - y ⟨0, by omega⟩ ≥ 1) :
    ∃ b₁ b₂ b₃ b₄ b₅ b₆,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₁ ≠ b₅ ∧ b₁ ≠ b₆ ∧
      b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₂ ≠ b₅ ∧ b₂ ≠ b₆ ∧
      b₃ ≠ b₄ ∧ b₃ ≠ b₅ ∧ b₃ ≠ b₆ ∧
      b₄ ≠ b₅ ∧ b₄ ≠ b₆ ∧
      b₅ ≠ b₆ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₁ + b₅, b₁ + b₆,
       b₂ + b₃, b₂ + b₄, b₂ + b₅, b₂ + b₆,
       b₃ + b₄, b₃ + b₅, b₃ + b₆,
       b₄ + b₅, b₄ + b₆,
       b₅ + b₆} ⊆ Set.range y := by
         -- By Lemma gcesthree, there exist integers $x_1, x_2, x_3, x_4, x_5, x_6$ with $x_2, x_3, x_4, x_5, x_6$ distinct such that the sequence contains all subset sums containing $x_1$.
         obtain ⟨x₁, x₂, x₃, x₄, x₅, x₆, hx⟩ := gcesthree t ht y h_mono h_bound h_y_ge_1;
         -- Set $b_1 = \frac{1}{2}x_1$ and $b_i = \frac{1}{2}x_1 + x_i$ for $2 \le i \le 6$.
         use x₁ / 2, x₁ / 2 + x₂, x₁ / 2 + x₃, x₁ / 2 + x₄, x₁ / 2 + x₅, x₁ / 2 + x₆;
         simp_all +decide [ Set.insert_subset_iff ];
         -- By combining the evenness of $x₁$ and the distinctness of $x₂, x₃, x₄, x₅, x₆$, we can conclude the required properties.
         have hx₁_even : Even x₁ := by
           aesop
         have hx_distinct : x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₄ ≠ 0 ∧ x₅ ≠ 0 ∧ x₆ ≠ 0 ∧ x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₂ ≠ x₅ ∧ x₂ ≠ x₆ ∧ x₃ ≠ x₄ ∧ x₃ ≠ x₅ ∧ x₃ ≠ x₆ ∧ x₄ ≠ x₅ ∧ x₄ ≠ x₆ ∧ x₅ ≠ x₆ := by
           grind +ring;
         rcases hx₁_even with ⟨ k, rfl ⟩ ; ring_nf at * ; aesop ( simp_config := { decide := true } ) ;

/-
There exists a subset of even numbers in A, outside the middle interval, with size at least half the remaining even numbers, contained in an interval of length roughly 6.5d.
-/
lemma case1_subset_existence (n : ℕ) (A : Finset ℤ)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (t : ℕ) (ht : t = (A.filter Even).card)
    (d : ℝ) (hd : d = (t : ℝ) - C_5 * Real.log n)
    (I : Finset ℤ) (hI : I = Finset.Icc (⌈6.5 * d⌉) (⌊2 * (n : ℝ) - 6.5 * d⌋))
    (h_few_middle : (A.filter (fun x => x ∈ I ∧ Even x)).card ≤ 100 * Real.log n) :
    ∃ S : Finset ℤ, S ⊆ A ∧ (∀ x ∈ S, Even x) ∧
      (S.card : ℝ) ≥ ((t : ℝ) - 100 * Real.log n) / 2 ∧
      (∃ a, S ⊆ Finset.Icc a (a + ⌈6.5 * d⌉)) := by
        -- Let $E$ be the set of even numbers in $A$.
        set E := A.filter Even;
        -- Let $E_L = E \cap [1, \lceil 6.5d \rceil - 1]$ and $E_R = E \cap [\lfloor 2n - 6.5d \rfloor + 1, 2n]$.
        set EL := E.filter (fun x => x < ⌈6.5 * d⌉)
        set ER := E.filter (fun x => x > ⌊2 * n - 6.5 * d⌋);
        -- Since $EL \cup ER$ contains at least $t - 100 \log n$ elements, one of $EL$ or $ER$ must have at least $(t - 100 \log n) / 2$ elements.
        have h_card_EL_ER : (EL.card : ℝ) + (ER.card : ℝ) ≥ (t - 100 * Real.log n) := by
          have h_card_union : (EL.card : ℝ) + (ER.card : ℝ) ≥ (E.card : ℝ) - (E.filter (fun x => x ∈ I ∧ Even x)).card := by
            have h_card_union : (EL.card : ℝ) + (ER.card : ℝ) ≥ (E.filter (fun x => x ∉ I)).card := by
              norm_cast;
              rw [ ← Finset.card_union_add_card_inter ];
              refine' le_trans _ ( Nat.le_add_right _ _ );
              refine Finset.card_mono ?_;
              intro x hx; contrapose! hx; aesop;
            convert h_card_union using 1;
            rw [ sub_eq_iff_eq_add ];
            rw_mod_cast [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
            rw [ ← Finset.sum_add_distrib, Finset.sum_filter ] ; congr ; ext ; aesop;
          simp +zetaDelta at *;
          convert h_card_union.trans ( add_le_add_left ( le_trans _ h_few_middle ) _ ) using 1;
          · exact_mod_cast ht;
          · exact_mod_cast Finset.card_mono fun x hx => by aesop;
        by_cases hEL : (EL.card : ℝ) ≥ (t - 100 * Real.log n) / 2;
        · refine' ⟨ EL, _, _, hEL, 1, _ ⟩ <;> norm_num +zetaDelta at *;
          · exact fun x hx => Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1;
          · exact fun x a a a_1 => a;
          · exact fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2, Finset.mem_Icc.mp ( hA_subset ( Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ) ], by linarith [ Finset.mem_filter.mp hx |>.2, Int.ceil_lt_add_one ( 13 / 2 * d ) ] ⟩;
        · refine' ⟨ ER, _, _, _, _ ⟩;
          · exact Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.filter_subset _ _;
          · exact fun x hx => Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2;
          · linarith;
          · use ⌊2 * n - 6.5 * d⌋ + 1;
            intro x hx; norm_num [ Int.floor_le, Int.le_floor ] at *;
            norm_num +zetaDelta at *;
            constructor <;> linarith [ show x ≤ 2 * n by linarith [ Finset.mem_Icc.mp ( hA_subset hx.1.1 ) ], show ⌊2 * ( n : ℝ ) - 13 / 2 * d⌋ + ⌈13 / 2 * d⌉ ≥ 2 * n - 1 by exact Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast ; linarith [ Int.floor_le ( 2 * ( n : ℝ ) - 13 / 2 * d ), Int.lt_floor_add_one ( 2 * ( n : ℝ ) - 13 / 2 * d ), Int.le_ceil ( 13 / 2 * d ), Int.ceil_lt_add_one ( 13 / 2 * d ) ] ]

/-
If $2n \ge d + C_5 \log n$ and $d \ge 10$, then $n \ge 10^{10}$.
-/
lemma case1_n_large (n : ℕ) (d : ℝ) (hd : d ≥ 10) (h : (2 * n : ℝ) ≥ d + C_5 * Real.log n) : n ≥ 10^10 := by
  contrapose! h;
  -- We'll use that $Real.log 10 \approx 2.3026$ to conclude the proof.
  have h_log_approx : Real.log 10 > 2.3 := by
    norm_num [ Real.log_lt_log ] at *;
    rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
    have := Real.exp_one_lt_d9.le ; norm_num at * ; rw [ show Real.exp 23 = ( Real.exp 1 ) ^ 23 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
  unfold C_5;
  by_cases hn : n < 10000000000 ∧ n ≥ 1000000000;
  · have h_log_approx : Real.log n ≥ Real.log 1000000000 := by
      exact Real.log_le_log ( by norm_num ) ( mod_cast hn.2 );
    rw [ show ( 1000000000 : ℝ ) = 10 ^ 9 by norm_num, Real.log_pow ] at h_log_approx ; norm_num at * ; linarith [ show ( n : ℝ ) ≤ 9999999999 by exact_mod_cast Nat.le_of_lt_succ ‹_› ] ;
  · by_cases hn : n < 1000000000 ∧ n ≥ 100000000;
    · have h_log_approx : Real.log n ≥ Real.log 100000000 := by
        exact Real.log_le_log ( by norm_num ) ( mod_cast hn.2 );
      rw [ show ( 100000000 : ℝ ) = 10 ^ 8 by norm_num, Real.log_pow ] at h_log_approx ; norm_num at * ; nlinarith [ show ( n : ℝ ) ≤ 999999999 by exact_mod_cast Nat.le_of_lt_succ hn.1 ];
    · by_cases hn : n < 100000000 ∧ n ≥ 10000000;
      · have h_log_approx : Real.log n ≥ Real.log 10000000 := by
          exact Real.log_le_log ( by norm_num ) ( mod_cast hn.2 );
        rw [ show ( 10000000 : ℝ ) = 10 ^ 7 by norm_num, Real.log_pow ] at h_log_approx ; norm_num at * ; linarith [ show ( n : ℝ ) ≤ 99999999 by exact_mod_cast Nat.le_of_lt_succ hn.1 ];
      · by_cases hn : n < 10000000 ∧ n ≥ 1000000;
        · nlinarith [ show ( n : ℝ ) ≥ 1000000 by exact_mod_cast hn.2, show ( n : ℝ ) < 10000000 by exact_mod_cast hn.1, Real.log_two_gt_d9, Real.log_le_log ( by norm_num ) ( show ( n : ℝ ) ≥ 2 by exact_mod_cast by linarith ) ];
        · by_cases hn : n < 1000000 ∧ n ≥ 100000;
          · nlinarith [ show ( n : ℝ ) ≥ 100000 by exact_mod_cast hn.2, show ( n : ℝ ) < 1000000 by exact_mod_cast hn.1, Real.log_two_gt_d9, Real.log_le_log ( by norm_num ) ( show ( n : ℝ ) ≥ 2 by exact_mod_cast by linarith ) ];
          · by_cases hn : n < 100000 ∧ n ≥ 10000;
            · have h_log_approx : Real.log n ≥ Real.log 10000 := by
                exact Real.log_le_log ( by norm_num ) ( mod_cast hn.2 );
              rw [ show ( 10000 : ℝ ) = 10 ^ 4 by norm_num, Real.log_pow ] at h_log_approx ; norm_num at * ; linarith [ show ( n : ℝ ) ≤ 99999 by norm_cast; linarith ];
            · by_cases hn : n < 10000 ∧ n ≥ 1000;
              · nlinarith [ show ( n : ℝ ) ≥ 1000 by exact_mod_cast hn.2, show ( n : ℝ ) < 10000 by exact_mod_cast hn.1, Real.log_inv ( n : ℝ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( show ( n : ℝ ) > 0 by exact_mod_cast hn.2.trans_lt' ( by norm_num ) ) ), mul_inv_cancel₀ ( show ( n : ℝ ) ≠ 0 by exact_mod_cast ne_of_gt ( hn.2.trans_lt' ( by norm_num ) ) ) ];
              · by_cases hn : n < 1000 ∧ n ≥ 100;
                · nlinarith [ show ( n : ℝ ) ≤ 999 by norm_cast; linarith, Real.log_two_gt_d9, Real.log_le_log ( by norm_num ) ( show ( n : ℝ ) ≥ 2 by norm_cast; linarith ) ];
                · by_cases hn : n < 100 ∧ n ≥ 10;
                  · linarith [ show ( n : ℝ ) ≤ 99 by norm_cast; linarith, show Real.log n ≥ 1 by exact Real.le_log_iff_exp_le ( by norm_cast; linarith ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 10 by norm_cast; linarith ] ];
                  · rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;> norm_num at *;
                    any_goals linarith [ Real.log_two_gt_d9, Real.log_le_log ( by norm_num ) ( by linarith : ( 8 : ℝ ) ≥ 2 ), Real.log_le_log ( by norm_num ) ( by linarith : ( 9 : ℝ ) ≥ 8 ) ];
                    any_goals linarith [ Real.log_two_gt_d9, Real.log_le_log ( by norm_num ) ( by linarith : ( 3 : ℝ ) ≥ 2 ), Real.log_le_log ( by norm_num ) ( by linarith : ( 4 : ℝ ) ≥ 3 ), Real.log_le_log ( by norm_num ) ( by linarith : ( 5 : ℝ ) ≥ 4 ), Real.log_le_log ( by norm_num ) ( by linarith : ( 6 : ℝ ) ≥ 5 ), Real.log_le_log ( by norm_num ) ( by linarith : ( 7 : ℝ ) ≥ 6 ) ];
                    grind

lemma case1_large_gap (y : ℝ) (hy : y ≥ 10^13) :
    y / 13 - 1 / 13 ≥ Real.sqrt 8 * y^(0.875 : ℝ) + y^(0.625 : ℝ) + 2 := by
      -- We'll use that $y \geq 10^{13}$ to bound the terms involving $y$.
      have h_bound : Real.sqrt 8 * y^(0.875 : ℝ) ≤ Real.sqrt 8 * y * y^(-0.125 : ℝ) ∧ y^(0.625 : ℝ) ≤ y * y^(-0.375 : ℝ) := by
        norm_num [ mul_assoc, ← Real.rpow_one_add' ( by positivity : 0 ≤ y ) ];
      -- We'll use that $y^{-0.125} \leq 10^{-1.625}$ and $y^{-0.375} \leq 10^{-4.875}$ for $y \geq 10^{13}$.
      have h_inv_bound : y^(-0.125 : ℝ) ≤ 10^(-1.625 : ℝ) ∧ y^(-0.375 : ℝ) ≤ 10^(-4.875 : ℝ) := by
        norm_num [ Real.rpow_def_of_pos ( by linarith : 0 < y ), Real.rpow_def_of_pos ] at *;
        constructor <;> nlinarith [ show Real.log y ≥ 13 * Real.log 10 by rw [ ← Real.log_rpow, ge_iff_le, Real.log_le_log_iff ] <;> norm_num <;> linarith, Real.log_pos ( show 10 > 1 by norm_num ) ];
      -- Substitute the bounds from h_inv_bound into h_bound.
      have h_subst : Real.sqrt 8 * y^(0.875 : ℝ) ≤ Real.sqrt 8 * y * 10^(-1.625 : ℝ) ∧ y^(0.625 : ℝ) ≤ y * 10^(-4.875 : ℝ) := by
        exact ⟨ h_bound.1.trans ( mul_le_mul_of_nonneg_left h_inv_bound.1 <| by positivity ), h_bound.2.trans ( mul_le_mul_of_nonneg_left h_inv_bound.2 <| by positivity ) ⟩;
      refine le_trans ( add_le_add_three h_subst.left h_subst.right le_rfl ) ?_;
      rw [ show ( -1.625 : ℝ ) = -1 - 0.625 by norm_num, show ( -4.875 : ℝ ) = -4 - 0.875 by norm_num, Real.rpow_sub, Real.rpow_sub ] <;> norm_num ; ring_nf ; norm_num;
      rw [ show ( 5 / 8 : ℝ ) = 1 - 3 / 8 by norm_num, show ( 7 / 8 : ℝ ) = 1 - 1 / 8 by norm_num, Real.rpow_sub, Real.rpow_sub ] <;> ring_nf <;> norm_num;
      -- We'll use that $10^{3/8} \approx 2.37$ and $10^{1/8} \approx 1.33$ to conclude the proof.
      have h_approx : (10 : ℝ)^(3 / 8 : ℝ) < 2.4 ∧ (10 : ℝ)^(1 / 8 : ℝ) < 1.4 := by
        norm_num [ Real.rpow_def_of_pos ];
        constructor <;> rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
        · rw [ mul_div, div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_lt_log ];
          norm_num [ mul_comm, ← Real.log_rpow, Real.log_lt_log ];
        · rw [ mul_one_div, div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_lt_log ];
      nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ), mul_le_mul_of_nonneg_left h_approx.1.le ( show 0 ≤ y by positivity ), mul_le_mul_of_nonneg_left h_approx.2.le ( show 0 ≤ y by positivity ) ]

lemma case1_bound_check_small_lo (n : ℕ) (d : ℝ) (hd : d ≥ 10)
    (h_n_large : n ≥ 10^10)
    (hy_small : ⌈6.5 * d⌉ < 10^9) :
    let y := ⌈6.5 * d⌉
    (d + (C_5 - 100) * Real.log n) / 2 ≥ Real.sqrt 8 * (y : ℝ)^(0.875 : ℝ) + (y : ℝ)^(0.625 : ℝ) + 2 := by
      -- Since $n \ge 10^{10}$, we have $\log n \ge \log (10^{10}) = 10 \log 10 \approx 23$.
      have h_log_n_ge_23 : Real.log n ≥ 23 := by
        rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ];
        exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 23 = ( Real.exp 1 ) ^ 23 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) ( Nat.cast_le.mpr h_n_large );
      -- Since $y < 10^9$, we have $y^{0.875} < (10^9)^{0.875} = 10^{7.875} \approx 7.5 \times 10^7$.
      have h_y_0_875_lt_7_5e7 : (Int.ceil (6.5 * d) : ℝ) ^ (0.875 : ℝ) < 7.5e7 := by
        refine' lt_of_lt_of_le ( Real.rpow_lt_rpow ( by positivity ) ( show ( ⌈6.5 * d⌉ : ℝ ) < 10^9 by exact_mod_cast hy_small ) ( by positivity ) ) _ ; norm_num [ Real.rpow_natCast ] ; ring_nf ; norm_num [ Real.rpow_natCast ] ; (
                                                                        rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ] <;> norm_num ; ring_nf ; norm_num [ Real.log_le_log_iff ] ;
                                                                        rw [ mul_div, div_le_iff₀' ] <;> norm_num [ ← Real.log_rpow, mul_comm, Real.log_le_log ])
      have h_y_0_625_lt_1e6 : (Int.ceil (6.5 * d) : ℝ) ^ (0.625 : ℝ) < 1e6 := by
        refine' lt_of_lt_of_le ( Real.rpow_lt_rpow ( by positivity ) ( show ( ⌈6.5 * d⌉ : ℝ ) < 10^9 by exact_mod_cast hy_small ) ( by positivity ) ) _ ; norm_num [ Real.rpow_natCast ] ; ring_nf ; norm_num [ Real.rpow_natCast ] ; (
                                                                        rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ] <;> norm_num ; ring_nf ; norm_num [ Real.log_le_log ] ; (
                                                                        rw [ mul_div, div_le_iff₀' ] <;> norm_num [ ← Real.log_rpow, mul_comm, Real.log_le_log ]))
      norm_num at *; (
      unfold C_5; norm_num at *; nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ) ] ;)

/-
Existence of a range of $p$ values with correct parity and bounds.
-/
lemma case2_p_range (d : ℕ) (a₁ b₁ : ℤ) (ha₁_even : Even a₁) :
    ∃ p_min p_max : ℤ,
      p_max - p_min + 1 = 3 * d + 1 ∧
      (∀ k ∈ Finset.range (3 * d + 1),
         let p := p_min + 2 * k
         p < a₁ - p ∧
         p % 2 ≠ b₁ % 2 ∧
         p ≥ a₁ / 2 - 6 * d - 2 ∧
         a₁ - p ≤ a₁ / 2 + 6 * d + 2) := by
           obtain ⟨ k₁, rfl ⟩ := ha₁_even; norm_num; ring_nf;
           by_cases h₂ : b₁ % 2 = (k₁ - 6 * d - 2) % 2;
           · refine' ⟨ k₁ - 6 * d - 2 + 1, ⟨ k₁ - 6 * d - 2 + 1 + d * 3, by ring ⟩, _ ⟩ ; intros k hk ; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, h₂ ] ; omega;
           · refine' ⟨ k₁ - 6 * d - 2, ⟨ k₁ - 6 * d - 2 + d * 3, by ring ⟩, fun k hk => ⟨ _, _, _, _ ⟩ ⟩ <;> norm_num;
             · linarith;
             · omega;
             · linarith;
             · linarith

/-
Bounds check for the constructed pairs.
-/
lemma case2_bounds (n d : ℕ) (hd : d ≥ 10)
    (a₁ a₂ a₃ : ℤ) (b₁ b₂ b₃ : ℤ)
    (hb_sum : b₁ + b₂ = a₁ ∧ b₁ + b₃ = a₂ ∧ b₂ + b₃ = a₃)
    (ha_sort : a₁ < a₂ ∧ a₂ < a₃)
    (L : ℝ)
    (ha_range : (a₁ : ℝ) ≥ L ∧ (a₃ : ℝ) < 1.03 * L)
    (hI_lower : (a₁ : ℝ) ≥ 6.5 * d)
    (hI_upper : (a₃ : ℝ) ≤ 2 * n - 6.5 * d)
    (p_min : ℤ) (hp_min : p_min ≥ a₁ / 2 - 6 * d - 2) :
    b₁ + p_min ≥ 1 ∧ b₃ + (a₁ - p_min) ≤ 2 * n := by
      constructor <;> norm_num [ ← @Int.cast_le ℝ ] at *;
      · -- Since $a₁$ is even, we have $a₁ / 2 = a₁ / 2$.
        have h_even : 2 * (a₁ / 2 : ℤ) ≥ a₁ - 1 := by
          omega;
        norm_num [ ← @Int.cast_le ℝ ] at *;
        linarith [ ( by norm_cast : ( 10 : ℝ ) ≤ d ), ( by norm_cast : ( a₁ : ℝ ) < a₂ ∧ ( a₂ : ℝ ) < a₃ ), ( by norm_cast : ( b₁ : ℝ ) + b₂ = a₁ ∧ ( b₁ : ℝ ) + b₃ = a₂ ∧ ( b₂ : ℝ ) + b₃ = a₃ ) ];
      · -- By combining terms, we can factor out common factors and simplify the expression.
        field_simp at *; (
        norm_cast at *;
        rw [ Int.subNatNat_eq_coe ] at hI_upper ; push_cast at * ; linarith [ Int.mul_ediv_add_emod a₁ 2, Int.emod_nonneg a₁ two_ne_zero, Int.emod_lt_of_pos a₁ two_pos ] ;)

/-
Existence of 5 elements with pairwise sums in A, given 3 even elements in a small interval (corrected hypotheses).
-/
lemma case2_existence_corrected (n d : ℕ) (A : Finset ℤ)
    (hn : n ≥ 10^10) (hd : d ≥ 10)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (h_odd_count : (A.filter Odd).card ≥ n - d)
    (a₁ a₂ a₃ : ℤ)
    (ha_subset : {a₁, a₂, a₃} ⊆ A)
    (ha_even : Even a₁ ∧ Even a₂ ∧ Even a₃)
    (ha_sort : a₁ < a₂ ∧ a₂ < a₃)
    (L : ℝ)
    (hL_pos : L > 0)
    (ha_range : (a₁ : ℝ) ≥ L ∧ (a₃ : ℝ) < 1.03 * L)
    (hI_lower : (a₁ : ℝ) ≥ 6.5 * d)
    (hI_upper : (a₃ : ℝ) ≤ 2 * n - 6.5 * d) :
    ∃ b₁ b₂ b₃ b₄ b₅ : ℤ,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₁ ≠ b₅ ∧
      b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₂ ≠ b₅ ∧
      b₃ ≠ b₄ ∧ b₃ ≠ b₅ ∧
      b₄ ≠ b₅ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₁ + b₅,
       b₂ + b₃, b₂ + b₄, b₂ + b₅,
       b₃ + b₄, b₃ + b₅,
       b₄ + b₅} ⊆ A := by
         obtain ⟨b₁, b₂, b₃, hb_eq⟩ : ∃ b₁ b₂ b₃ : ℤ, b₁ < b₂ ∧ b₂ < b₃ ∧ b₁ + b₂ = a₁ ∧ b₁ + b₃ = a₂ ∧ b₂ + b₃ = a₃ ∧ (b₁ % 2 = b₂ % 2) ∧ (b₂ % 2 = b₃ % 2) := by
           -- Apply the lemma `exists_b_of_a` to obtain the required $b₁$, $b₂$, and $b₃$.
           apply exists_b_of_a a₁ a₂ a₃ ha_sort.left ha_sort.right ha_even;
         obtain ⟨p_min, p_max, hp_range⟩ : ∃ p_min p_max : ℤ, p_max - p_min + 1 = 3 * d + 1 ∧ (∀ k ∈ Finset.range (3 * d + 1), let p := p_min + 2 * k; p < a₁ - p ∧ p % 2 ≠ b₁ % 2 ∧ p ≥ a₁ / 2 - 6 * d - 2 ∧ a₁ - p ≤ a₁ / 2 + 6 * d + 2) := by
           convert case2_p_range d a₁ b₁ _ using 1 ; aesop;
         obtain ⟨k, hk⟩ : ∃ k ∈ Finset.range (3 * d + 1), let p := p_min + 2 * k; let q := a₁ - p; {b₁ + p, b₂ + p, b₃ + p, b₁ + q, b₂ + q, b₃ + q} ⊆ A := by
           apply valid_pair_exists n d A (by linarith) (by linarith) hA_subset h_odd_count a₁ b₁ b₂ b₃
           generalize_proofs at *; (
           linarith);
           any_goals tauto;
           intro k hk
           obtain ⟨hp_lt_q, hp_not_b₁, hp_bounds⟩ := hp_range.right k hk
           have h_bounds : b₁ + p_min ≥ 1 ∧ b₃ + (a₁ - p_min) ≤ 2 * n := by
             apply case2_bounds n d hd a₁ a₂ a₃ b₁ b₂ b₃ ⟨by linarith, by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ L ⟨by linarith, by linarith⟩ hI_lower hI_upper p_min (by
             have := hp_range.2 0; norm_num at this; linarith;)
           generalize_proofs at *; (
           grind)
         generalize_proofs at *; (
         use b₁, b₂, b₃, p_min + 2 * k, a₁ - (p_min + 2 * k) ; simp_all +decide [ Finset.subset_iff ] ; (
         grind +ring))

/-
Bounds on d and odd cardinality.
-/
lemma d_bounds (n : ℕ) (A : Finset ℤ)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (hA_card : (A.card : ℝ) ≥ n + C_5 * Real.log n + 10) :
    let t := (A.filter Even).card
    let d_real := (t : ℝ) - C_5 * Real.log n
    d_real ≥ 10 ∧ (A.filter Odd).card ≥ n + 10 - d_real := by
      -- From Lemma 2, we have $|A_{odd}| \le n$.
      have h_odd_card : (A.filter Odd).card ≤ n := by
        have h_even_count : (A.filter Odd).card ≤ Finset.card (Finset.filter Odd (Finset.Icc 1 (2 * n))) := by
          convert Finset.card_le_card ( Finset.filter_subset_filter _ hA_subset ) using 1;
          refine' Finset.card_bij ( fun x hx => Int.natAbs x ) _ _ _ <;> norm_num;
          · exact fun a ha₁ ha₂ ha₃ => ⟨ ⟨ ha₁, mod_cast ha₂ ⟩, ha₃ ⟩;
          · exact fun b hb₁ hb₂ hb₃ => ⟨ Int.natAbs b, ⟨ ⟨ by linarith [ abs_of_nonneg ( by linarith : 0 ≤ b ) ], by linarith [ abs_of_nonneg ( by linarith : 0 ≤ b ) ] ⟩, by simpa [ ← Int.odd_iff ] using hb₃ ⟩, by simp +decide [ abs_of_nonneg ( by linarith : 0 ≤ b ) ] ⟩ ;
        refine le_trans h_even_count ?_;
        rw [ Finset.card_eq_of_bijective ];
        use fun i hi => 2 * i + 1;
        · exact fun x hx => by obtain ⟨ k, rfl ⟩ := Finset.mem_filter.mp hx |>.2; exact ⟨ k, by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ], rfl ⟩ ;
        · exact fun i hi => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, by simp +decide [ parity_simps ] ⟩;
        · aesop;
      -- Since $A$ contains both even and odd elements, we have $|A| = |A_{even}| + |A_{odd}|$.
      have h_even_odd_card : A.card = (A.filter Even).card + (A.filter Odd).card := by
        rw [ Finset.card_filter, Finset.card_filter ];
        simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones A ▸ by congr; ext x; aesop;
      constructor <;> push_cast [ h_even_odd_card ] at * <;> linarith [ ( by norm_cast : ( A.filter Odd |> Finset.card :ℝ ) ≤ n ) ]

/-
The function `f_case1_check` is positive at $y=10^{12}$.
-/
noncomputable def f_case1_check (y : ℝ) : ℝ :=
  let d := (y - 1) / 6.5
  let K := (C_5 - 100)
  (d + K * Real.log d) / 2 - (Real.sqrt 8 * y^(0.875 : ℝ) + y^(0.625 : ℝ) + 2)

/-
The second derivative of `f_case1_check` is positive on $[10^{11}, 10^{13}]$.
-/
lemma f_case1_check_second_deriv_pos_inline (y : ℝ) (hy_lo : y ≥ 10^11) :
    - (C_5 - 100) / (2 * (y - 1)^2) + (Real.sqrt 8 * 0.875 * 0.125 * y^(-1.125 : ℝ) + 0.625 * 0.375 * y^(-1.375 : ℝ)) > 0 := by
      unfold C_5;
      -- Simplify the expression by factoring out common terms and combining like terms.
      suffices h_simp : 0.3 * y^(-1.125 : ℝ) > 0.5 * 10^9 * (y - 1)^(-2 : ℝ) by
        norm_num [ Real.rpow_neg ( by linarith : 0 ≤ y - 1 ) ] at *;
        field_simp;
        ring_nf at *;
        nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ), Real.rpow_pos_of_pos ( by linarith : 0 < y ) ( -9 / 8 : ℝ ), Real.rpow_pos_of_pos ( by linarith : 0 < y ) ( -11 / 8 : ℝ ) ];
      norm_num [ Real.rpow_neg ( by linarith : 0 ≤ y ), Real.rpow_neg ( by linarith : 0 ≤ y - 1 ) ] at *;
      field_simp;
      rw [ div_lt_iff₀ ] <;> norm_num at * <;> try nlinarith;
      -- Let's cube both sides to remove the cube root.
      suffices h_cubed : (5000000000 * y ^ (9 / 8 : ℝ))^8 < (3 * (y - 1)^2)^8 by
        contrapose! h_cubed; gcongr;
      ring_nf at *;
      rw [ ← Real.rpow_natCast _ 8, ← Real.rpow_mul ( by positivity ) ] ; norm_num ; nlinarith [ pow_nonneg ( by linarith : 0 ≤ y ) 2, pow_nonneg ( by linarith : 0 ≤ y ) 3, pow_nonneg ( by linarith : 0 ≤ y ) 4, pow_nonneg ( by linarith : 0 ≤ y ) 5, pow_nonneg ( by linarith : 0 ≤ y ) 6, pow_nonneg ( by linarith : 0 ≤ y ) 7, pow_nonneg ( by linarith : 0 ≤ y ) 8, pow_nonneg ( by linarith : 0 ≤ y ) 9, pow_nonneg ( by linarith : 0 ≤ y ) 10, pow_nonneg ( by linarith : 0 ≤ y ) 11, pow_nonneg ( by linarith : 0 ≤ y ) 12, pow_nonneg ( by linarith : 0 ≤ y ) 13, pow_nonneg ( by linarith : 0 ≤ y ) 14, pow_nonneg ( by linarith : 0 ≤ y ) 15, pow_nonneg ( by linarith : 0 ≤ y ) 16 ] ;

/-
The function f_case1_check is positive at y = 10^11.
-/
lemma f_case1_check_at_10_11_pos : f_case1_check (10^11 : ℝ) > 0 := by
  unfold f_case1_check; norm_num; ring_nf; norm_num; (
  -- We'll use that $10^{11}^{0.875} \approx 10^{9.625} = 10^{0.625} \times 10^9 \approx 4.21 \times 10^9$ and $\sqrt{8} \approx 2.828$.
  have h_approx : (10 ^ 11 : ℝ) ^ (7 / 8 : ℝ) < 4.22 * 10 ^ 9 ∧ Real.sqrt 8 < 2.829 := by
    rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ] <;> norm_num [ Real.log_lt_log ] at * ; ring_nf at * ; norm_num at *; (
    exact ⟨ by rw [ mul_div, div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, mul_comm, Real.log_lt_log ], by rw [ Real.sqrt_lt ] <;> norm_num ⟩ ;);
  -- We'll use that $10^{11}^{0.625} \approx 10^{6.875} \approx 7.5 \times 10^6$.
  have h_approx2 : (10 ^ 11 : ℝ) ^ (5 / 8 : ℝ) < 7.5 * 10 ^ 6 := by
    rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ] <;> norm_num [ Real.log_lt_log ] ; ring_nf ; norm_num [ Real.log_pos ] ; (
    rw [ mul_div, div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, mul_comm, Real.log_lt_log ]);
  -- We'll use that $Real.log (199999999998 / 13) \approx 21.4$.
  have h_log_approx : Real.log (199999999998 / 13) > 21 := by
    norm_num [ Real.lt_log_iff_exp_lt ] at *;
    have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 21 = ( Real.exp 1 ) ^ 21 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
  norm_num [ C_5 ] at * ; nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ) ] ;)

/-
The function f_case1_check is positive at y = 10^9.
-/
lemma f_case1_check_at_10_9_pos : f_case1_check (10^9 : ℝ) > 0 := by
  unfold f_case1_check C_5; norm_num;
  -- We'll use that $Real.log (1999999998 / 13) > 18$ to conclude the proof.
  have h_log : Real.log (1999999998 / 13) > 18 := by
    norm_num [ Real.lt_log_iff_exp_lt ] at *;
    have := Real.exp_one_lt_d9.le ; norm_num at * ; rw [ show Real.exp 18 = ( Real.exp 1 ) ^ 18 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
  nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt <| show 0 ≤ 8 by norm_num, Real.rpow_le_rpow_of_exponent_le ( show 1 ≤ 1000000000 by norm_num ) ( show 7 / 8 ≤ 1 by norm_num ), Real.rpow_le_rpow_of_exponent_le ( show 1 ≤ 1000000000 by norm_num ) ( show 5 / 8 ≤ 1 by norm_num ) ]

/-
f_case1_check is bounded below by f_case1_lb for y >= 10^9.
-/
noncomputable def f_case1_lb (y : ℝ) : ℝ :=
  (y - 1) / 13 + (C_5 - 100) / 2 * Real.log ((10^9 - 1) / 6.5) - (Real.sqrt 8 * y^(0.875 : ℝ) + y^(0.625 : ℝ) + 2)

lemma f_case1_check_ge_lb (y : ℝ) (hy : y ≥ 10^9) :
    f_case1_check y ≥ f_case1_lb y := by
      unfold f_case1_check f_case1_lb; ring_nf; norm_num; (
      unfold C_5; ring_nf; norm_num;
      nlinarith [ Real.log_le_log ( by norm_num ) ( by linarith : ( 1999999998 : ℝ ) / 13 ≤ - ( 2 / 13 ) + y * ( 2 / 13 ) ) ]);

/-
f_case1_lb is positive at 10^11.
-/
lemma f_case1_lb_at_10_11_pos : f_case1_lb (10^11) > 0 := by
  unfold f_case1_lb C_5;
  rw [ show ( 10 ^ 11 : ℝ ) = ( 10 ^ 11 : ℝ ) by norm_num, Real.rpow_def_of_pos, Real.rpow_def_of_pos ] <;> ring_nf <;> norm_num;
  rw [ show ( 100000000000 : ℝ ) = 10 ^ 11 by norm_num, Real.log_pow ] ; ring_nf ; norm_num [ Real.exp_mul, Real.exp_log ] ;
  -- We'll use that $Real.log (1999999998 / 13) > 18$ to conclude the proof.
  have h_log : Real.log (1999999998 / 13) > 18 := by
    norm_num [ Real.lt_log_iff_exp_lt ];
    have := Real.exp_one_lt_d9.le ; norm_num at * ; rw [ show Real.exp 18 = ( Real.exp 1 ) ^ 18 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
  rw [ show ( 10 : ℝ ) ^ ( 77 / 8 : ℝ ) = 10 ^ ( 9 : ℝ ) * 10 ^ ( 5 / 8 : ℝ ) by rw [ ← Real.rpow_add ] <;> norm_num, show ( 10 : ℝ ) ^ ( 55 / 8 : ℝ ) = 10 ^ ( 6 : ℝ ) * 10 ^ ( 7 / 8 : ℝ ) by rw [ ← Real.rpow_add ] <;> norm_num ] ; ring_nf ; norm_num;
  -- We'll use that $10^{5/8} < 5$ and $10^{7/8} < 10$ to conclude the proof.
  have h_bounds : (10 : ℝ) ^ (5 / 8 : ℝ) < 5 ∧ (10 : ℝ) ^ (7 / 8 : ℝ) < 10 := by
    rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ] <;> norm_num;
    exact ⟨ by rw [ div_mul_eq_mul_div, div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_lt_log ], by exact lt_of_lt_of_le ( Real.rpow_lt_rpow_of_exponent_lt ( by norm_num ) ( show ( 7 : ℝ ) / 8 < 1 by norm_num ) ) ( by norm_num ) ⟩;
  nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ), Real.rpow_pos_of_pos ( show 0 < 10 by norm_num ) ( 5 / 8 : ℝ ), Real.rpow_pos_of_pos ( show 0 < 10 by norm_num ) ( 7 / 8 : ℝ ) ]

/-
The derivative of f_case1_lb is negative at 10^11.
-/
noncomputable def f_case1_lb_deriv (y : ℝ) : ℝ :=
  1 / 13 - (Real.sqrt 8 * 0.875 * y^(-0.125 : ℝ) + 0.625 * y^(-0.375 : ℝ))

lemma f_case1_lb_deriv_neg_at_10_11 : f_case1_lb_deriv (10^11) < 0 := by
  unfold f_case1_lb_deriv;
  norm_num [ Real.rpow_neg ];
  refine' lt_add_of_lt_of_nonneg _ _ <;> norm_num [ Real.rpow_natCast ];
  · rw [ ← div_eq_mul_inv, lt_div_iff₀ ( by positivity ) ];
    rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_mul, Real.log_mul, Real.log_rpow, Real.log_sqrt ] <;> ring_nf <;> norm_num;
    field_simp;
    norm_num [ mul_comm, ← Real.log_rpow, ← Real.log_mul, Real.log_lt_log ];
  · positivity

/-
f_case1_lb_deriv is negative on the interval [10^9, 10^11].
-/
lemma f_case1_lb_deriv_neg_on_interval (y : ℝ) (hy_lo : y ≥ 10^9) (hy_hi : y ≤ 10^11) :
    f_case1_lb_deriv y < 0 := by
      have h_deriv_neg : StrictMonoOn f_case1_lb_deriv (Set.Ioi 0) := by
        intro x hx y hy hxy; unfold f_case1_lb_deriv; norm_num at *; (
        exact add_lt_add_of_lt_of_le ( mul_lt_mul_of_pos_left ( by rw [ Real.rpow_lt_rpow_iff_of_neg ] <;> linarith ) ( by positivity ) ) ( mul_le_mul_of_nonneg_left ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith ) ( by positivity ) ) ;);
      exact lt_of_le_of_lt ( h_deriv_neg.le_iff_le ( show 0 < y by positivity ) ( show 0 < ( 10^11 : ℝ ) by positivity ) |>.2 hy_hi ) ( f_case1_lb_deriv_neg_at_10_11 )

/-
f_case1_lb is decreasing on the interval [10^9, 10^11], so f_case1_lb y >= f_case1_lb (10^11).
-/
lemma f_case1_lb_ge_at_10_11 (y : ℝ) (hy_lo : y ≥ 10^9) (hy_hi : y ≤ 10^11) :
    f_case1_lb y ≥ f_case1_lb (10^11) := by
      by_contra h_contra;
      -- Apply the Mean Value Theorem to the interval [y, 10^11].
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo y (10^11), deriv f_case1_lb c = (f_case1_lb (10^11) - f_case1_lb y) / (10^11 - y) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact hy_hi.lt_of_ne ( by rintro rfl; norm_num at h_contra );
        · exact ContinuousOn.sub ( ContinuousOn.add ( ContinuousOn.div_const ( continuousOn_id.sub continuousOn_const ) _ ) ( continuousOn_const.mul continuousOn_const ) ) ( ContinuousOn.add ( ContinuousOn.add ( ContinuousOn.mul continuousOn_const ( ContinuousOn.rpow continuousOn_id continuousOn_const <| by norm_num ) ) ( ContinuousOn.rpow continuousOn_id continuousOn_const <| by norm_num ) ) continuousOn_const );
        · refine' DifferentiableOn.sub _ _;
          · exact DifferentiableOn.add ( DifferentiableOn.div_const ( differentiableOn_id.sub_const _ ) _ ) ( differentiableOn_const _ );
          · exact DifferentiableOn.add ( DifferentiableOn.add ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.rpow ( differentiableOn_id ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1 ] ) ) ) ( DifferentiableOn.rpow ( differentiableOn_id ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1 ] ) ) ) ( differentiableOn_const _ );
      -- Since $c \in (y, 10^{11})$, we have $f_case1_lb_deriv c < 0$.
      have h_deriv_neg : f_case1_lb_deriv c < 0 := by
        exact f_case1_lb_deriv_neg_on_interval c ( by linarith [ hc.1.1 ] ) ( by linarith [ hc.1.2 ] );
      -- By definition of $f_case1_lb$, we know that its derivative is $f_case1_lb_deriv$.
      have h_deriv_eq : deriv f_case1_lb c = f_case1_lb_deriv c := by
        unfold f_case1_lb f_case1_lb_deriv; norm_num [ Real.rpow_neg, show c ≠ 0 by linarith [ hc.1.1 ] ] ; ring;
      rw [ eq_div_iff ] at hc <;> nlinarith [ hc.1.1, hc.1.2 ]

lemma f_case1_check_pos_on_small_interval (y : ℝ) (hy_lo : y ≥ 10^9) (hy_hi : y ≤ 10^11) :
    f_case1_check y > 0 := by
      -- By combining the results, we conclude that $f_case1_check y > 0$ for $y \in [10^9, 10^{11}]$.
      have h_final : f_case1_check y ≥ f_case1_lb y ∧ f_case1_lb y ≥ f_case1_lb (10^11) ∧ f_case1_lb (10^11) > 0 := by
        exact ⟨ f_case1_check_ge_lb y hy_lo, f_case1_lb_ge_at_10_11 y hy_lo hy_hi, f_case1_lb_at_10_11_pos ⟩
      generalize_proofs at *;
      linarith

/-
Definition of the derivative of `f_case1_check`.
-/
noncomputable def f_case1_check_deriv (y : ℝ) : ℝ :=
  let K := (C_5 - 100)
  (1 / 13) + K / (2 * (y - 1)) - (Real.sqrt 8 * 0.875 * y^(-0.125 : ℝ) + 0.625 * y^(-0.375 : ℝ))

/-
Lower bound for the derivative of `f_case1_check` at $10^{12}$.
-/
lemma f_case1_check_deriv_bound_10_12 : f_case1_check_deriv (10^12) > -0.001 := by
  unfold f_case1_check_deriv;
  unfold C_5; norm_num;
  rw [ show ( 8 : ℝ ) = 4 * 2 by norm_num, Real.sqrt_mul ] <;> norm_num;
  rw [ show ( 1000000000000 : ℝ ) = 10 ^ 12 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
  rw [ show ( 1000000000000 : ℝ ) = 10 ^ 12 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
  rw [ show ( - ( 3 / 2 : ℝ ) ) = -1 - 1 / 2 by norm_num, show ( - ( 9 / 2 : ℝ ) ) = -4 - 1 / 2 by norm_num, Real.rpow_sub, Real.rpow_sub ] <;> ring_nf <;> norm_num;
  rw [ ← Real.sqrt_eq_rpow ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 10, Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), Real.sq_sqrt ( show 0 ≤ 10 by norm_num ), inv_pos.2 ( Real.sqrt_pos.2 ( show 0 < 10 by norm_num ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.2 ( show 0 < 10 by norm_num ) ) ), mul_pos ( Real.sqrt_pos.2 ( show 0 < 2 by norm_num ) ) ( Real.sqrt_pos.2 ( show 0 < 10 by norm_num ) ) ] ;

/-
Positivity of the derivative of `f_case1_check` at $1.2 \cdot 10^{12}$.
-/
lemma f_case1_check_deriv_pos_1_2 : f_case1_check_deriv (1.2 * 10^12) > 0 := by
  unfold f_case1_check_deriv C_5 ; norm_num;
  rw [ Real.rpow_neg, Real.rpow_neg ] <;> norm_num;
  -- Let's simplify the expression on the left-hand side.
  field_simp;
  -- We'll use that $x = 1200000000000^{1/8}$ to simplify the expression.
  set x : ℝ := 1200000000000^(1 / 8 : ℝ)
  have hx : x^8 = 1200000000000 := by
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
  rw [ show ( 1200000000000 : ℝ ) ^ ( 3 / 8 : ℝ ) = x ^ 3 by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ] ; ring_nf at *;
  -- We'll use that $x \approx 1200000000000^{1/8}$ to simplify the expression.
  have hx_approx : x > 31 := by
    exact lt_of_not_ge fun h => by nlinarith [ pow_le_pow_left₀ ( by positivity ) h 8 ] ;
  nlinarith [ pow_pos ( sub_pos.mpr hx_approx ) 2, pow_pos ( sub_pos.mpr hx_approx ) 3, pow_pos ( sub_pos.mpr hx_approx ) 4, pow_pos ( sub_pos.mpr hx_approx ) 5, pow_pos ( sub_pos.mpr hx_approx ) 6, pow_pos ( sub_pos.mpr hx_approx ) 7, Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ) ]

/-
Lower bound for `f_case1_check` at $10^{12}$.
-/
lemma f_case1_check_val_bound_10_12 : f_case1_check (10^12) > 2.5 * 10^8 := by
  unfold f_case1_check; norm_num [ Real.rpow_def_of_pos ] ; ring_nf; norm_num;
  rw [ show ( 1000000000000 : ℝ ) = 10 ^ 12 by norm_num, Real.log_pow ] ; ring_nf ; norm_num [ Real.exp_mul, Real.exp_log ] ; ring_nf ; norm_num [ C_5 ] ;
  rw [ show ( 10 : ℝ ) ^ ( 21 / 2 : ℝ ) = 10 ^ ( 10 : ℝ ) * 10 ^ ( 1 / 2 : ℝ ) by rw [ ← Real.rpow_add ] <;> norm_num ] ; rw [ show ( 10 : ℝ ) ^ ( 15 / 2 : ℝ ) = 10 ^ ( 7 : ℝ ) * 10 ^ ( 1 / 2 : ℝ ) by rw [ ← Real.rpow_add ] <;> norm_num ] ; norm_num [ ← Real.sqrt_eq_rpow ] ; ring_nf ;
  rw [ show ( 8 : ℝ ) = 4 * 2 by norm_num, Real.sqrt_mul ] <;> norm_num ; ring_nf ;
  rw [ show ( 153846153846 : ℝ ) = 10 ^ 11 * 1.53846153846 by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf <;> norm_num;
  rw [ ← Real.sqrt_mul ] <;> norm_num;
  rw [ show ( 20 : ℝ ) = 4 * 5 by norm_num, Real.sqrt_mul ] <;> norm_num ; ring_nf ; norm_num [ Real.log_pos ] ; ring_nf ; norm_num [ Real.log_pos ] ; (
        -- We'll use that $Real.log 10 > 2.3$ and $Real.log (76923076923 / 50000000000) > 0.4$ to conclude the proof.
        have h_log_bounds : Real.log 10 > 2.3 ∧ Real.log (76923076923 / 50000000000) > 0.4 := by
          norm_num [ Real.lt_log_iff_exp_lt ] at *;
          constructor <;> rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
          · rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            have := Real.exp_one_lt_d9.le ; norm_num at * ; rw [ show Real.exp 23 = ( Real.exp 1 ) ^ 23 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
          · rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show ( 2 : ℝ ) = 1 + 1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ] ;
        nlinarith [ Real.sqrt_nonneg 10, Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 10 by norm_num ), Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 10 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 5 by norm_num ) ) ])

/-
Upper bound for the derivative of `f_case1_check` at $10^{12}$.
-/
lemma f_case1_check_deriv_neg_at_10_12 : f_case1_check_deriv (10^12) < 0 := by
  unfold f_case1_check_deriv; norm_num;
  rw [ show ( 8 : ℝ ) = 4 * 2 by norm_num, Real.sqrt_mul ] <;> norm_num ; ring_nf;
  rw [ show ( 1000000000000 : ℝ ) = ( 10 ^ 12 ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ; ring_nf ; norm_num [ Real.sqrt_eq_rpow ] at *;
  rw [ show ( 1000000000000 : ℝ ) = ( 10 ^ 12 ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ; ring_nf ; norm_num [ Real.sqrt_eq_rpow ] at *;
  rw [ show ( - ( 3 / 2 : ℝ ) ) = -1 - 1 / 2 by norm_num, show ( - ( 9 / 2 : ℝ ) ) = -4 - 1 / 2 by norm_num, Real.rpow_sub, Real.rpow_sub ] <;> ring_nf <;> norm_num [ Real.sqrt_eq_rpow ] at *;
  norm_num [ ← Real.sqrt_eq_rpow ] at *;
  rw [ ← Real.sqrt_div_self ] ; ring_nf ; norm_num [ Real.lt_sqrt, Real.sqrt_lt ] ;
  rw [ show C_5 = 10^9-20 by rfl ] ; norm_num ; nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 10, Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), Real.sq_sqrt ( show 0 ≤ 10 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 10 by norm_num ) ) ] ;

lemma f_case1_check_pos_on_large_interval (y : ℝ) (hy_lo : y ≥ 10^11) (hy_hi : y ≤ 10^13) :
    f_case1_check y > 0 := by
      -- By convexity, $f(y) \ge f(10^{12}) + f'(10^{12})(y - 10^{12})$.
      have h_convex : ∀ y ∈ Set.Icc (10^12 : ℝ) (1.2 * 10^12), f_case1_check y ≥ f_case1_check (10^12) + f_case1_check_deriv (10^12) * (y - 10^12) := by
        intros y hy
        have h_convex : ConvexOn ℝ (Set.Icc (10^11 : ℝ) (10^13)) f_case1_check := by
          apply_rules [ convexOn_of_deriv2_nonneg, convex_Icc ];
          · refine' ContinuousOn.sub _ _ <;> norm_num [ f_case1_check ];
            · exact ContinuousOn.div ( ContinuousOn.add ( ContinuousOn.div_const ( continuousOn_id.sub continuousOn_const ) _ ) ( ContinuousOn.mul continuousOn_const ( ContinuousOn.log ( ContinuousOn.div_const ( continuousOn_id.sub continuousOn_const ) _ ) fun x hx => by linarith [ hx.1 ] ) ) ) continuousOn_const ( by norm_num );
            · exact ContinuousOn.add ( ContinuousOn.add ( continuousOn_const.mul ( continuousOn_id.rpow_const <| by norm_num ) ) ( continuousOn_id.rpow_const <| by norm_num ) ) continuousOn_const;
          · refine' DifferentiableOn.sub _ _ <;> norm_num [ f_case1_check ];
            · exact DifferentiableOn.div_const ( DifferentiableOn.add ( DifferentiableOn.div_const ( differentiableOn_id.sub_const _ ) _ ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.log ( DifferentiableOn.div_const ( differentiableOn_id.sub_const _ ) _ ) ( by intro x hx; linarith [ hx.1, hx.2 ] ) ) ) ) _;
            · exact DifferentiableOn.add ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.rpow ( differentiableOn_id ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1 ] ) ) ) ( DifferentiableOn.rpow ( differentiableOn_id ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1 ] ) );
          · refine' DifferentiableOn.congr _ _;
            use fun x => ( 1 / 13 ) + ( C_5 - 100 ) / ( 2 * ( x - 1 ) ) - ( Real.sqrt 8 * 0.875 * x ^ ( -0.125 : ℝ ) + 0.625 * x ^ ( -0.375 : ℝ ) );
            · exact DifferentiableOn.sub ( DifferentiableOn.add ( differentiableOn_const _ ) ( DifferentiableOn.div ( differentiableOn_const _ ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( differentiableOn_id.sub ( differentiableOn_const _ ) ) ) ( by intro x hx; norm_num at hx; linarith ) ) ) ( DifferentiableOn.add ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.rpow ( differentiableOn_id ) ( differentiableOn_const _ ) ( by intro x hx; norm_num at hx; linarith ) ) ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.rpow ( differentiableOn_id ) ( differentiableOn_const _ ) ( by intro x hx; norm_num at hx; linarith ) ) ) ) ;
            · intro x hx; unfold f_case1_check; norm_num [ show x ≠ 0 by linarith [ Set.mem_Icc.mp ( interior_subset hx ) ], show x - 1 ≠ 0 by linarith [ Set.mem_Icc.mp ( interior_subset hx ) ] ] ; ring_nf;
              grind;
          · intros x hx
            have h_second_deriv : deriv^[2] f_case1_check x = - (C_5 - 100) / (2 * (x - 1)^2) + (Real.sqrt 8 * 0.875 * 0.125 * x^(-1.125 : ℝ) + 0.625 * 0.375 * x^(-1.375 : ℝ)) := by
              have h_second_deriv : deriv^[2] f_case1_check x = deriv (fun x => (1 / 13) + (C_5 - 100) / (2 * (x - 1)) - (Real.sqrt 8 * 0.875 * x^(-0.125 : ℝ) + 0.625 * x^(-0.375 : ℝ))) x := by
                refine' Filter.EventuallyEq.deriv_eq _ ; filter_upwards [ Ioi_mem_nhds ( show x > 1 by linarith [ Set.mem_Icc.mp ( interior_subset hx ) ] ) ] with y hy ; unfold f_case1_check ; norm_num [ show y ≠ 0 by linarith [ Set.mem_Ioi.mp hy ], show y - 1 ≠ 0 by linarith [ Set.mem_Ioi.mp hy ], Real.rpow_neg, mul_comm ] ; ring_nf;
                rw [ show ( -2 / 13 + y * ( 2 / 13 ) ) = ( -2 + y * 2 ) / 13 by ring ] ; norm_num ; ring;
              generalize_proofs at *; (
              rw [ h_second_deriv ] ; norm_num [ show x - 1 ≠ 0 from sub_ne_zero_of_ne <| by rintro rfl; norm_num at hx, show x ≠ 0 from by rintro rfl; norm_num at hx ] ; ring_nf;
              norm_num [ show -2 + x * 2 ≠ 0 from by linarith [ Set.mem_Icc.mp ( interior_subset hx ) ], show x ≠ 0 from by linarith [ Set.mem_Icc.mp ( interior_subset hx ) ] ] ; ring_nf;
              rw [ show ( 4 - x * 8 + x ^ 2 * 4 : ℝ ) = ( 2 - x * 4 + x ^ 2 * 2 ) * 2 by ring ] ; norm_num ; ring;);
            exact h_second_deriv.symm ▸ f_case1_check_second_deriv_pos_inline x ( by linarith [ Set.mem_Icc.mp ( interior_subset hx ) ] ) |> le_of_lt;
        generalize_proofs at *; (
        have h_convex : ∀ y ∈ Set.Ioo (10^11 : ℝ) (10^13), HasDerivAt f_case1_check (f_case1_check_deriv y) y := by
          intro y hy; unfold f_case1_check f_case1_check_deriv; norm_num [ Real.rpow_neg, hy.1.ne', hy.2.ne', Nat.cast_add, Nat.cast_one, Nat.cast_mul ] ; ring_nf; norm_num; (
          convert HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id y ) ( hasDerivAt_const _ _ ) ) ) ( HasDerivAt.sub ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.log ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id y ) ( hasDerivAt_const _ _ ) ) ) _ ) ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.mul ( HasDerivAt.log ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id y ) ( hasDerivAt_const _ _ ) ) ) _ ) ( hasDerivAt_const _ _ ) ) ) ) ( HasDerivAt.sub ( HasDerivAt.neg ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.rpow_const ( hasDerivAt_id y ) _ ) ) ) ( HasDerivAt.rpow_const ( hasDerivAt_id y ) _ ) ) using 1 <;> norm_num <;> ring_nf <;> norm_num at * <;> try linarith [ hy.1, hy.2 ] ;
          grind)
        generalize_proofs at *; (
        have h_convex : ∀ y ∈ Set.Ioo (10^11 : ℝ) (10^13), ∀ z ∈ Set.Ioo (10^11 : ℝ) (10^13), y < z → f_case1_check z ≥ f_case1_check y + f_case1_check_deriv y * (z - y) := by
          intros y hy z hz hyz
          have h_convex : ∀ t ∈ Set.Ioo 0 1, f_case1_check (t * z + (1 - t) * y) ≤ t * f_case1_check z + (1 - t) * f_case1_check y := by
            exact fun t ht => ‹ConvexOn ℝ ( Set.Icc ( 10^11 ) ( 10^13 ) ) f_case1_check›.2 ( show z ∈ Set.Icc ( 10^11 ) ( 10^13 ) from ⟨ by linarith [ hz.1 ], by linarith [ hz.2 ] ⟩ ) ( show y ∈ Set.Icc ( 10^11 ) ( 10^13 ) from ⟨ by linarith [ hy.1 ], by linarith [ hy.2 ] ⟩ ) ( by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) ;
          generalize_proofs at *; (
          have h_convex : Filter.Tendsto (fun t => (f_case1_check (t * z + (1 - t) * y) - f_case1_check y) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f_case1_check_deriv y * (z - y))) := by
            have h_convex : HasDerivAt (fun t => f_case1_check (t * z + (1 - t) * y)) (f_case1_check_deriv y * (z - y)) 0 := by
              convert HasDerivAt.comp _ ( ‹∀ y ∈ Set.Ioo ( 10^11 ) ( 10^13 ), HasDerivAt f_case1_check ( f_case1_check_deriv y ) y› _ _ ) ( HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_id 0 ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.mul ( hasDerivAt_id 0 |> HasDerivAt.const_sub _ ) ( hasDerivAt_const _ _ ) ) ) using 1 <;> norm_num ; ring_nf
              · grind;
              · constructor <;> linarith [ hy.1, hy.2 ]
            generalize_proofs at *; (
            simpa [ div_eq_inv_mul ] using h_convex.tendsto_slope_zero_right)
          generalize_proofs at *; (
          have h_convex : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), (f_case1_check (t * z + (1 - t) * y) - f_case1_check y) / t ≤ f_case1_check z - f_case1_check y := by
            filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with t ht using by rw [ div_le_iff₀ ht.1 ] ; linarith [ ‹∀ t ∈ Set.Ioo 0 1, f_case1_check ( t * z + ( 1 - t ) * y ) ≤ t * f_case1_check z + ( 1 - t ) * f_case1_check y› t ht ] ;
          generalize_proofs at *; (
          have := le_of_tendsto_of_tendsto ‹_› tendsto_const_nhds h_convex; norm_num at *; linarith;)))
        generalize_proofs at *; (
        cases eq_or_lt_of_le hy.1 <;> [ aesop; exact h_convex _ ⟨ by norm_num, by norm_num ⟩ _ ⟨ by linarith [ hy.1 ], by linarith [ hy.2 ] ⟩ ( by linarith [ hy.1, hy.2 ] ) ] ;)));
      by_cases hy : y ≤ 10^12 ∨ y ≥ 1.2 * 10^12;
      · cases hy;
        · -- Since $f_case1_check$ is decreasing on $[10^{11}, 10^{12}]$, we have $f_case1_check y \geq f_case1_check 10^{12}$.
          have h_decreasing : f_case1_check y ≥ f_case1_check (10^12) := by
            have h_decreasing : ∀ y ∈ Set.Icc (10^11 : ℝ) (10^12), deriv f_case1_check y ≤ 0 := by
              intros y hy
              have h_deriv : deriv f_case1_check y = f_case1_check_deriv y := by
                unfold f_case1_check f_case1_check_deriv; norm_num [ Real.rpow_neg, Real.rpow_one, Real.rpow_natCast, Real.rpow_mul, Real.rpow_two, mul_comm, mul_assoc, mul_left_comm, div_eq_mul_inv, differentiableAt_inv, show y ≠ 0 from by linarith [ hy.1 ], show y - 1 ≠ 0 from by linarith [ hy.1 ] ] ; ring;
              have h_deriv_neg : ∀ y ∈ Set.Icc (10^11 : ℝ) (10^12), deriv f_case1_check_deriv y > 0 := by
                intros y hy
                have h_deriv_pos : deriv f_case1_check_deriv y = - (C_5 - 100) / (2 * (y - 1)^2) + (Real.sqrt 8 * 0.875 * 0.125 * y^(-1.125 : ℝ) + 0.625 * 0.375 * y^(-1.375 : ℝ)) := by
                  unfold f_case1_check_deriv; norm_num [ show y ≠ 0 by linarith [ hy.1 ], show y - 1 ≠ 0 by linarith [ hy.1 ] ] ; ring_nf;
                  rw [ show ( 4 - y * 8 + y ^ 2 * 4 : ℝ ) = ( 2 - y * 4 + y ^ 2 * 2 ) * 2 by ring ] ; norm_num ; ring;
                exact h_deriv_pos.symm ▸ f_case1_check_second_deriv_pos_inline y hy.1 ;
              have h_deriv_neg : ∀ y ∈ Set.Icc (10^11 : ℝ) (10^12), f_case1_check_deriv y ≤ f_case1_check_deriv (10^12) := by
                intros y hy
                by_contra h_contra;
                have := exists_deriv_eq_slope f_case1_check_deriv ( show y < 10^12 from lt_of_le_of_ne hy.2 <| by rintro rfl; norm_num at h_contra ) ; norm_num at *;
                exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun x hx => DifferentiableAt.continuousAt <| by exact differentiableAt_of_deriv_ne_zero <| ne_of_gt <| h_deriv_neg x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) ) ( by exact fun x hx => DifferentiableAt.differentiableWithinAt <| by exact differentiableAt_of_deriv_ne_zero <| ne_of_gt <| h_deriv_neg x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) ) ) ( by rintro ⟨ c, ⟨ h₁, h₂ ⟩, h₃ ⟩ ; rw [ eq_div_iff ] at h₃ <;> nlinarith [ h_deriv_neg c ( by linarith ) ( by linarith ) ] );
              exact h_deriv.symm ▸ le_trans ( h_deriv_neg y hy ) ( by linarith [ f_case1_check_deriv_neg_at_10_12 ] );
            by_contra h_contra;
            have := exists_deriv_eq_slope f_case1_check ( show y < 10^12 from lt_of_le_of_ne ‹_› <| by rintro rfl; norm_num at h_contra ) ; norm_num at *;
            apply_mod_cast absurd ( this _ _ ) _;
            · refine' ContinuousOn.sub _ _;
              · exact ContinuousOn.div ( ContinuousOn.add ( ContinuousOn.div_const ( continuousOn_id.sub continuousOn_const ) _ ) ( ContinuousOn.mul continuousOn_const ( ContinuousOn.log ( ContinuousOn.div_const ( continuousOn_id.sub continuousOn_const ) _ ) fun x hx => by norm_num; linarith [ hx.1 ] ) ) ) continuousOn_const ( by norm_num );
              · exact ContinuousOn.add ( ContinuousOn.add ( continuousOn_const.mul ( continuousOn_id.rpow_const <| by norm_num ) ) ( continuousOn_id.rpow_const <| by norm_num ) ) continuousOn_const;
            · refine' fun x hx => DifferentiableAt.differentiableWithinAt _;
              apply_rules [ DifferentiableAt.sub, DifferentiableAt.add, DifferentiableAt.mul, DifferentiableAt.log, DifferentiableAt.rpow ] <;> norm_num <;> linarith [ hx.1, hx.2 ] ;
            · exact fun ⟨ c, hc₁, hc₂ ⟩ => by have := h_decreasing c ( by linarith ) ( by linarith ) ; rw [ hc₂, div_le_iff₀ ] at this <;> linarith;
          exact lt_of_lt_of_le ( by exact lt_of_le_of_lt ( by norm_num ) ( f_case1_check_val_bound_10_12 ) ) h_decreasing;
        · have h_convex : ∀ y ∈ Set.Icc (1.2 * 10^12 : ℝ) (10^13), f_case1_check y ≥ f_case1_check (1.2 * 10^12) + f_case1_check_deriv (1.2 * 10^12) * (y - 1.2 * 10^12) := by
            intros y hy
            have h_convex : ∀ x ∈ Set.Icc (1.2 * 10^12 : ℝ) y, f_case1_check_deriv x ≥ f_case1_check_deriv (1.2 * 10^12) := by
              intros x hx
              have h_deriv_pos : ∀ x ∈ Set.Icc (1.2 * 10^12 : ℝ) (10^13), deriv f_case1_check_deriv x > 0 := by
                intros x hx
                have h_deriv_pos : deriv f_case1_check_deriv x = - (C_5 - 100) / (2 * (x - 1)^2) + (Real.sqrt 8 * 0.875 * 0.125 * x^(-1.125 : ℝ) + 0.625 * 0.375 * x^(-1.375 : ℝ)) := by
                  unfold f_case1_check_deriv; norm_num [ show x ≠ 0 by linarith [ hx.1 ], show x - 1 ≠ 0 by linarith [ hx.1 ] ] ; ring_nf;
                  rw [ show ( 4 - x * 8 + x ^ 2 * 4 : ℝ ) = ( 2 - x * 4 + x ^ 2 * 2 ) * 2 by ring ] ; norm_num ; ring;
                generalize_proofs at *; (
                exact h_deriv_pos.symm ▸ f_case1_check_second_deriv_pos_inline x ( by linarith [ hx.1 ] ) |> fun h => by linarith;)
              generalize_proofs at *; (
              by_contra h_contra
              generalize_proofs at *; (
              have := exists_deriv_eq_slope f_case1_check_deriv ( show x > 1.2 * 10^12 from lt_of_le_of_ne hx.1 <| Ne.symm <| by rintro rfl; norm_num at h_contra ) ; norm_num at * ; (
                                                                    exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun y hy => DifferentiableAt.continuousAt <| by exact differentiableAt_of_deriv_ne_zero <| ne_of_gt <| h_deriv_pos y hy.1 <| by linarith [ hy.2 ] ) ( by exact fun y hy => DifferentiableAt.differentiableWithinAt <| by exact differentiableAt_of_deriv_ne_zero <| ne_of_gt <| h_deriv_pos y hy.1.le <| by linarith [ hy.2 ] ) ) ( by rintro ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ ; rw [ eq_div_iff ] at hc <;> nlinarith [ h_deriv_pos c hc₁.le <| by linarith ] ) ;)))
            generalize_proofs at *; (
            have h_convex : ∫ x in (1.2 * 10^12)..y, f_case1_check_deriv x ≥ ∫ x in (1.2 * 10^12)..y, f_case1_check_deriv (1.2 * 10^12) := by
              apply_rules [ intervalIntegral.integral_mono_on ] <;> norm_num at * ; aesop;
              apply_rules [ ContinuousOn.intervalIntegrable ];
              exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.add continuousAt_const <| ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_const <| continuousAt_id.sub continuousAt_const ) <| by cases Set.mem_uIcc.mp hx <;> linarith ) <| ContinuousAt.add ( ContinuousAt.mul continuousAt_const <| ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> linarith ) <| ContinuousAt.mul continuousAt_const <| ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> linarith;
            generalize_proofs at *; (
            have h_convex : ∫ x in (1.2 * 10^12)..y, f_case1_check_deriv x = f_case1_check y - f_case1_check (1.2 * 10^12) := by
              rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ] <;> norm_num at *;
              · intro x hx; convert HasDerivAt.sub ( HasDerivAt.div_const ( HasDerivAt.add ( HasDerivAt.div_const ( HasDerivAt.sub ( hasDerivAt_id' x ) ( hasDerivAt_const _ _ ) ) _ ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.log ( HasDerivAt.div_const ( HasDerivAt.sub ( hasDerivAt_id' x ) ( hasDerivAt_const _ _ ) ) _ ) _ ) ) ) _ ) ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.rpow_const ( hasDerivAt_id' x ) _ ) ) ( HasDerivAt.rpow_const ( hasDerivAt_id' x ) _ ) ) ( hasDerivAt_const _ _ ) ) using 1 <;> norm_num ; ring_nf;
                · unfold f_case1_check_deriv; norm_num ; ring_nf;
                  rw [ show ( -2 + x * 2 ) = ( -2 / 13 + x * ( 2 / 13 ) ) * 13 by ring ] ; norm_num ; ring;
                · cases Set.mem_uIcc.mp hx <;> linarith [ hy.1, hy.2 ];
                · cases Set.mem_uIcc.mp hx <;> linarith [ hy.1, hy.2 ] ;
                · cases Set.mem_uIcc.mp hx <;> linarith [ hy.1, hy.2 ] ;
              · apply_rules [ ContinuousOn.intervalIntegrable ];
                refine' ContinuousOn.sub _ _;
                · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.add continuousAt_const <| ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_const <| continuousAt_id.sub continuousAt_const ) <| by cases Set.mem_uIcc.mp hx <;> linarith;
                · exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.add ( ContinuousAt.mul continuousAt_const ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> linarith ) ) ( ContinuousAt.mul continuousAt_const ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> linarith ) ) ;
            generalize_proofs at *; (
            norm_num at *; linarith;)));
          have h_pos : f_case1_check (1.2 * 10^12) > 0 := by
            have h_pos : f_case1_check (1.2 * 10^12) ≥ f_case1_check (10^12) + f_case1_check_deriv (10^12) * (1.2 * 10^12 - 10^12) := by
              exact ‹∀ y ∈ Set.Icc ( 10^12 ) ( 1.2 * 10^12 ), f_case1_check y ≥ f_case1_check ( 10^12 ) + f_case1_check_deriv ( 10^12 ) * ( y - 10^12 ) › _ ⟨ by norm_num, by norm_num ⟩;
            exact h_pos.trans_lt' ( by have := f_case1_check_val_bound_10_12; have := f_case1_check_deriv_neg_at_10_12; have := f_case1_check_deriv_bound_10_12; norm_num at *; linarith );
          exact lt_of_lt_of_le h_pos ( le_trans ( by norm_num ) ( h_convex y ⟨ by linarith, by linarith ⟩ |> le_trans ( le_add_of_nonneg_right <| mul_nonneg ( show 0 ≤ f_case1_check_deriv ( 1.2 * 10^12 ) from by
                                                                                                                                                                exact le_of_lt ( by exact
                                                                                                                                                                  f_case1_check_deriv_pos_1_2 ) ) <| by linarith ) ) );
      · push_neg at hy;
        have := h_convex y ⟨ hy.1.le, hy.2.le ⟩ ; norm_num at * ; nlinarith [ f_case1_check_val_bound_10_12, f_case1_check_deriv_bound_10_12 ] ;

lemma f_case1_check_pos_on_combined_interval (y : ℝ) (hy_lo : y ≥ 10^9) (hy_hi : y ≤ 10^13) :
    f_case1_check y > 0 := by
      by_cases hy : y ≤ 10^11;
      · exact f_case1_check_pos_on_small_interval y hy_lo hy;
      · exact f_case1_check_pos_on_large_interval y ( by linarith ) ( by linarith ) |> fun h => by linarith;

/-
Bound check for Case 1.
-/
lemma case1_bound_check (n : ℕ) (d : ℝ) (hd : d ≥ 10) (hn : n ≥ 10^10) (hd_le_n : d ≤ n) :
    let y := ⌈6.5 * d⌉
    (d + (C_5 - 100) * Real.log n) / 2 ≥ Real.sqrt 8 * (y : ℝ)^(0.875 : ℝ) + (y : ℝ)^(0.625 : ℝ) + 2 := by
      by_cases hy : ⌈6.5 * d⌉ ≥ 10^13;
      · have h_case1_large_gap : (⌈6.5 * d⌉ : ℝ) / 13 - 1 / 13 ≥ Real.sqrt 8 * (⌈6.5 * d⌉ : ℝ)^(0.875 : ℝ) + (⌈6.5 * d⌉ : ℝ)^(0.625 : ℝ) + 2 := by
          have := case1_large_gap ( ⌈6.5 * d⌉ : ℝ ) ( mod_cast hy ) ; norm_num at * ; linarith;
        refine le_trans h_case1_large_gap ?_;
        rw [ show C_5 = 10^9-20 by rfl ] ; norm_num ; ring_nf ; norm_num;
        linarith [ Int.ceil_lt_add_one ( d * ( 13 / 2 ) ), show ( Real.log n : ℝ ) ≥ 1 by exact Real.le_log_iff_exp_le ( by positivity ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 10^10 by exact_mod_cast hn ] ];
      · by_cases hy : ⌈6.5 * d⌉ ≥ 10^9;
        · have h_log_bound : Real.log n > Real.log ((⌈6.5 * d⌉ - 1) / 6.5) := by
            gcongr ; norm_num at * ; linarith [ Int.le_ceil ( 6.5 * d ) ] ;
            rw [ div_lt_iff₀ ] <;> norm_num ; linarith [ Int.ceil_lt_add_one ( 6.5 * d ), show ( n : ℝ ) ≥ 10^10 by exact_mod_cast hn ] ;
          have h_f_case1_check_pos : f_case1_check (⌈6.5 * d⌉ : ℝ) > 0 := by
            apply f_case1_check_pos_on_combined_interval;
            · exact_mod_cast hy;
            · exact_mod_cast le_of_not_ge ‹¬⌈6.5 * d⌉ ≥ 10 ^ 13›;
          unfold f_case1_check at h_f_case1_check_pos;
          norm_num [ C_5 ] at *;
          linarith [ show ( ⌈13 / 2 * d⌉ : ℝ ) ≤ 13 / 2 * d + 1 by exact_mod_cast Int.ceil_lt_add_one _ |> le_of_lt ];
        · apply case1_bound_check_small_lo n d hd hn (by
          exact lt_of_not_ge hy)

lemma case1_logic (n : ℕ) (A : Finset ℤ)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (t : ℕ) (ht : t = (A.filter Even).card)
    (d : ℝ) (hd : d = (t : ℝ) - C_5 * Real.log n)
    (hd_ge_10 : d ≥ 10)
    (hn_large : n ≥ 10^10)
    (h_few_middle : (A.filter (fun x => x ∈ Finset.Icc (⌈6.5 * d⌉) (⌊2 * (n : ℝ) - 6.5 * d⌋) ∧ Even x)).card ≤ 100 * Real.log n) :
    ∃ b₁ b₂ b₃ b₄ b₅ : ℤ,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₁ ≠ b₅ ∧
      b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₂ ≠ b₅ ∧
      b₃ ≠ b₄ ∧ b₃ ≠ b₅ ∧
      b₄ ≠ b₅ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₁ + b₅,
       b₂ + b₃, b₂ + b₄, b₂ + b₅,
       b₃ + b₄, b₃ + b₅,
       b₄ + b₅} ⊆ A := by
         obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ := case1_subset_existence n A hA_subset t ht d hd _ rfl h_few_middle;
         have hS_bound : (S.card : ℝ) ≥ Real.sqrt 8 * (⌈6.5 * d⌉ : ℝ)^(0.875 : ℝ) + (⌈6.5 * d⌉ : ℝ)^(0.625 : ℝ) + 2 := by
           have := case1_bound_check n d hd_ge_10 hn_large ( show d ≤ n by
                                                               have h_card_le_n : (A.filter Even).card ≤ n := by
                                                                 have h_card_le_n : (A.filter Even).card ≤ Finset.card (Finset.image (fun x => x / 2) (A.filter Even)) := by
                                                                   rw [ Finset.card_image_of_injOn ];
                                                                   exact fun x hx y hy hxy => by linarith [ Int.ediv_mul_cancel ( even_iff_two_dvd.mp ( Finset.mem_filter.mp hx |>.2 ) ), Int.ediv_mul_cancel ( even_iff_two_dvd.mp ( Finset.mem_filter.mp hy |>.2 ) ) ] ;
                                                                 refine le_trans h_card_le_n ?_;
                                                                 refine' le_trans ( Finset.card_le_card _ ) _;
                                                                 exact Finset.Icc 1 n;
                                                                 · exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp ( hA_subset ( Finset.mem_filter.mp hx |>.1 ) ), Int.mul_ediv_add_emod x 2, Int.emod_nonneg x two_ne_zero, Int.emod_lt_of_pos x two_pos, show x % 2 = 0 from Int.emod_eq_zero_of_dvd <| even_iff_two_dvd.mp <| Finset.mem_filter.mp hx |>.2 ], by linarith [ Finset.mem_Icc.mp ( hA_subset ( Finset.mem_filter.mp hx |>.1 ) ), Int.mul_ediv_add_emod x 2, Int.emod_nonneg x two_ne_zero, Int.emod_lt_of_pos x two_pos, show x % 2 = 0 from Int.emod_eq_zero_of_dvd <| even_iff_two_dvd.mp <| Finset.mem_filter.mp hx |>.2 ] ⟩;
                                                                 · norm_num [ Int.card_Icc ];
                                                               rw [ hd, ht ] ; linarith [ show ( Finset.card ( Finset.filter Even A ) : ℝ ) ≤ n by exact_mod_cast h_card_le_n, show ( C_5 : ℝ ) * Real.log n ≥ 0 by exact mul_nonneg ( by norm_num [ C_5 ] ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ] ; );
           unfold C_5 at *; norm_num at *; linarith;
         obtain ⟨ a, ha ⟩ := hS₄;
         have hS_bound : (S.card : ℝ) ≥ Real.sqrt 8 * ((a + ⌈6.5 * d⌉) - a : ℝ)^(0.875 : ℝ) + ((a + ⌈6.5 * d⌉) - a : ℝ)^(0.625 : ℝ) + 2 := by
           grind;
         have := corrotwo S.card (by
         exact Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at *; nlinarith [ Real.sqrt_nonneg 8, Real.sq_sqrt ( show 0 ≤ 8 by norm_num ), Real.rpow_pos_of_pos ( show 0 < ( ⌈6.5 * d⌉ : ℝ ) by positivity ) ( 0.875 : ℝ ), Real.rpow_pos_of_pos ( show 0 < ( ⌈6.5 * d⌉ : ℝ ) by positivity ) ( 0.625 : ℝ ) ] )) (fun i => S.orderEmbOfFin rfl i) (by
         exact fun i j hij => by simpa using hij;) (by
         exact fun i => hS₂ _ <| Finset.orderEmbOfFin_mem _ _ _) (by
         refine le_trans ?_ hS_bound;
         gcongr <;> norm_num [ ha ];
         · exact_mod_cast Finset.mem_Icc.mp ( ha <| Finset.orderEmbOfFin_mem _ _ _ ) |>.2.trans <| by norm_num [ show ⌈13 / 2 * d⌉ = ⌈6.5 * d⌉ by ring_nf ] ;
         · exact Finset.mem_Icc.mp ( ha <| Finset.orderEmbOfFin_mem _ _ _ ) |>.1;
         · exact_mod_cast Finset.mem_Icc.mp ( ha <| Finset.orderEmbOfFin_mem _ _ _ ) |>.2.trans <| by norm_num [ show ⌈13 / 2 * d⌉ = ⌈6.5 * d⌉ by ring_nf ] ;
         · exact Finset.mem_Icc.mp ( ha <| Finset.orderEmbOfFin_mem _ _ _ ) |>.1) (by
         refine' Int.sub_pos_of_lt _;
         simp +zetaDelta at *;
         exact_mod_cast ( by nlinarith [ show 0 < Real.sqrt 8 * ( ⌈6.5 * d⌉ : ℝ ) ^ ( 0.875 : ℝ ) by exact mul_pos ( Real.sqrt_pos.mpr ( by norm_num ) ) ( Real.rpow_pos_of_pos ( Int.cast_pos.mpr ( Int.ceil_pos.mpr ( by positivity ) ) ) _ ), show 0 < ( ⌈6.5 * d⌉ : ℝ ) ^ ( 0.625 : ℝ ) by exact Real.rpow_pos_of_pos ( Int.cast_pos.mpr ( Int.ceil_pos.mpr ( by positivity ) ) ) _ ] : ( 1 : ℝ ) < #S ));
         obtain ⟨ b₁, b₂, b₃, b₄, b₅, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁ ⟩ := this; use b₁, b₂, b₃, b₄, b₅; simp_all +decide [ Set.subset_def ] ;
         simp_all +decide [Finset.subset_iff]

/-
If a finite set has at least 3 elements, it contains 3 sorted elements.
-/
lemma exists_three_sorted_elements {α : Type*} [LinearOrder α] (s : Finset α) (h : s.card ≥ 3) :
    ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a < b ∧ b < c := by
      obtain ⟨t, ht⟩ : ∃ t : Fin 3 → α, (∀ i, t i ∈ s) ∧ StrictMono t := by
        exact ⟨ fun i => s.orderEmbOfFin rfl ⟨ i, by linarith [ Fin.is_lt i ] ⟩, fun i => by simp, by simp +decide [ StrictMono ] ⟩;
      exact ⟨ t 0, t 1, t 2, ht.1 0, ht.1 1, ht.1 2, ht.2 ( by decide ), ht.2 ( by decide ) ⟩

lemma case2_logic (n : ℕ) (A : Finset ℤ)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (t : ℕ) (ht : t = (A.filter Even).card)
    (d_real : ℝ) (hd_real : d_real = (t : ℝ) - C_5 * Real.log n)
    (hd_bounds : d_real ≥ 10 ∧ (A.filter Odd).card ≥ n + 10 - d_real)
    (hn_large : n ≥ 10^10)
    (I_real : Finset ℤ) (hI_real : I_real = Finset.Icc (⌈6.5 * d_real⌉) (⌊2 * (n : ℝ) - 6.5 * d_real⌋))
    (h_many : (A.filter (fun x => x ∈ I_real ∧ Even x)).card > 100 * Real.log n) :
    ∃ b₁ b₂ b₃ b₄ b₅ : ℤ,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₁ ≠ b₅ ∧
      b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₂ ≠ b₅ ∧
      b₃ ≠ b₄ ∧ b₃ ≠ b₅ ∧
      b₄ ≠ b₅ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₁ + b₅,
       b₂ + b₃, b₂ + b₄, b₂ + b₅,
       b₃ + b₄, b₃ + b₅,
       b₄ + b₅} ⊆ A := by
         -- Let $d_{nat} = \lfloor d_{real} \rfloor$. Since $d_{real} \ge 10$, $d_{nat} \ge 10$ by definition of floor.
         set d_nat := Nat.floor d_real
         have hd_nat : d_nat ≥ 10 := by
           exact Nat.le_floor <| mod_cast hd_bounds.1.trans' <| by norm_num;
         -- Let $I_{nat} = [\lceil 6.5 d_{nat} \rceil, \lfloor 2n - 6.5 d_{nat} \rfloor]$.
         set I_nat := Finset.Icc (Int.ceil (6.5 * d_nat : ℝ)) (Int.floor (2 * n - 6.5 * d_nat : ℝ));
         -- The number of even elements in $I_{nat}$ is at least the number in $I_{real}$, which is $> 100 \log n$.
         have h_even_count_nat : ((A.filter (fun x => x ∈ I_nat ∧ Even x)).card : ℝ) ≥ 100 * Real.log n := by
           refine le_trans h_many.le ?_;
           refine' Nat.cast_le.mpr ( Finset.card_mono _ );
           simp +contextual [ Finset.subset_iff, hI_real ];
           intro x hx hx₁ hx₂ hx₃; refine' Finset.mem_Icc.mpr ⟨ _, _ ⟩ <;> norm_num at *;
           · exact le_trans ( Int.ceil_mono <| mul_le_mul_of_nonneg_left ( Nat.floor_le <| by linarith ) <| by norm_num ) hx₁;
           · exact le_trans hx₂ <| Int.floor_mono <| by linarith [ Nat.floor_le <| show 0 ≤ d_real by linarith ] ;
         -- Apply `exists_interval_with_three_evens` with $d_{nat}$ to find a geometric interval with at least 3 even elements.
         obtain ⟨j, hj⟩ : ∃ j : ℕ, let lower := (geom_base ^ j : ℝ); let upper := (geom_base ^ (j + 1) : ℝ); let S := (A.filter (fun x => x ∈ I_nat ∧ Even x)).filter (fun x => (x : ℝ) ≥ lower ∧ (x : ℝ) < upper); S.card ≥ 3 := by
           apply exists_interval_with_three_evens n d_nat A (by
           grind) hd_nat hA_subset I_nat rfl h_even_count_nat
         -- Let $S$ be the set of these even elements. $|S| \ge 3$.
         obtain ⟨S, hS⟩ : ∃ S : Finset ℤ, S ⊆ A ∧ S.card ≥ 3 ∧ (∀ x ∈ S, x ∈ I_nat ∧ Even x) ∧ (∃ L : ℝ, L > 0 ∧ ∀ x ∈ S, (x : ℝ) ≥ L ∧ (x : ℝ) < 1.03 * L) := by
           refine' ⟨ Finset.image ( fun x : ℤ => x ) ( Finset.filter ( fun x : ℤ => ( x : ℝ ) ≥ geom_base ^ j ∧ ( x : ℝ ) < geom_base ^ ( j + 1 ) ) ( Finset.filter ( fun x : ℤ => x ∈ I_nat ∧ Even x ) A ) ), _, _, _, _ ⟩ <;> norm_num at *;
           · exact fun x hx => Finset.mem_filter.mp hx |>.1 |> Finset.mem_filter.mp |>.1;
           · convert hj using 1;
             refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +contextual [ Finset.mem_filter, Finset.mem_image ];
             exact fun b x hx₁ hx₂ hx₃ hx₄ hx₅ hx₆ => ⟨ x, ⟨ ⟨ hx₁, hx₂, hx₃ ⟩, by simpa [ hx₄ ] using hx₅, by simpa [ hx₄ ] using hx₆ ⟩, hx₄ ⟩;
           · exact fun x hx₁ hx₂ hx₃ hx₄ hx₅ => ⟨ hx₂, hx₃ ⟩;
           · refine' ⟨ geom_base ^ j, by exact pow_pos ( by norm_num [ geom_base ] ) _, fun x hx₁ hx₂ hx₃ hx₄ hx₅ => ⟨ hx₄, _ ⟩ ⟩ ; norm_num [ geom_base ] at * ; linarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 1.03 ) j, pow_succ' ( 1.03 : ℝ ) j ] ;
         -- Apply `exists_three_sorted_elements` to get $a_1 < a_2 < a_3$ in $S$.
         obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, ha_sort⟩ : ∃ a₁ a₂ a₃ : ℤ, a₁ ∈ S ∧ a₂ ∈ S ∧ a₃ ∈ S ∧ a₁ < a₂ ∧ a₂ < a₃ := by
           have := exists_three_sorted_elements S hS.2.1; aesop;
         obtain ⟨ L, hL_pos, hL ⟩ := hS.2.2.2;
         apply case2_existence_corrected n d_nat A hn_large hd_nat hA_subset (by
         exact Nat.sub_le_of_le_add <| by push_cast [ ← @Nat.cast_le ℝ ] ; linarith [ Nat.floor_le ( show 0 ≤ d_real by linarith ), Nat.lt_floor_add_one d_real ] ;) a₁ a₂ a₃ (by
         exact Finset.insert_subset_iff.mpr ⟨ hS.1 ha₁, Finset.insert_subset_iff.mpr ⟨ hS.1 ha₂, Finset.singleton_subset_iff.mpr ( hS.1 ha₃ ) ⟩ ⟩) (by
         exact ⟨ hS.2.2.1 a₁ ha₁ |>.2, hS.2.2.1 a₂ ha₂ |>.2, hS.2.2.1 a₃ ha₃ |>.2 ⟩) (by
         exact ha_sort) L hL_pos (by
         exact ⟨ hL a₁ ha₁ |>.1, hL a₃ ha₃ |>.2 ⟩) (by
         exact le_trans ( Int.le_ceil _ ) ( mod_cast hS.2.2.1 a₁ ha₁ |>.1 |> Finset.mem_Icc.mp |>.1 )) (by
         exact le_trans ( Int.le_floor.mp ( Finset.mem_Icc.mp ( hS.2.2.1 a₃ ha₃ |>.1 ) |>.2 ) ) ( by norm_num ))

/-
If $n \ge 4$ and $A \subseteq \{1, 2, \ldots, 2n\}$ is any set with $|A| \ge n + 2$ elements, then distinct positive integers $b_1, b_2, b_3$ exist with $b_i + b_j \in A$ for $1 \le i < j \le 3$.
-/
theorem pairwise_sums_of_three_positive_elements_fake (n : ℕ) (hn : n ≥ 4) (A : Finset ℕ)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n)) (hA_card : A.card ≥ n + 2) :
    ∃ b₁ b₂ b₃ : ℕ, b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ ∧
    (b₁ + b₂) ∈ A ∧ (b₁ + b₃) ∈ A ∧ (b₂ + b₃) ∈ A ∧ b₁ > 0 ∧ b₂ > 0 ∧ b₃ > 0 := by
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (2 * m + 1 ∈ A ∧ m ≥ 1) ∧ (∀ k ∈ A, k % 2 = 1 → k ≥ 2 * m + 1 ∨ k = 1) := by
        by_cases h_odd : ∃ k ∈ A, k % 2 = 1 ∧ k ≥ 3;
        · obtain ⟨k₀, hk₀⟩ : ∃ k₀ ∈ A, k₀ % 2 = 1 ∧ k₀ ≥ 3 ∧ ∀ k ∈ A, k % 2 = 1 → k ≥ 3 → k₀ ≤ k := by
            exact ⟨ Nat.find h_odd, Nat.find_spec h_odd |>.1, Nat.find_spec h_odd |>.2.1, Nat.find_spec h_odd |>.2.2, fun k hk hk' hk'' => Nat.find_min' h_odd ⟨ hk, hk', hk'' ⟩ ⟩;
          use k₀ / 2;
          grind;
        · have h_subset : A ⊆ {1} ∪ Finset.filter (fun x => x % 2 = 0) (Finset.Icc 1 (2 * n)) := by
            grind;
          have := Finset.card_le_card h_subset; simp_all +arith +decide ;
          rw [ show Finset.filter ( fun x => x % 2 = 0 ) ( Finset.Icc 1 ( 2 * n ) ) = Finset.image ( fun x => 2 * x ) ( Finset.Icc 1 n ) from ?_, Finset.card_image_of_injective ] at this <;> norm_num [ Function.Injective ] at * ; linarith [ Nat.div_mul_le_self ( 2 * n ) 2 ] ;
          apply Finset.ext
          intro x
          simp [Finset.mem_image];
          exact ⟨ fun hx => ⟨ x / 2, ⟨ by linarith [ Nat.mod_add_div x 2 ], by linarith [ Nat.mod_add_div x 2 ] ⟩, by linarith [ Nat.mod_add_div x 2 ] ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by linarith, by linarith ⟩, by norm_num ⟩ ⟩;
      by_cases h_exists_j : ∃ j ∈ Finset.Icc (m + 2) (2 * n - (m + 1)), m + j ∈ A ∧ m + j + 1 ∈ A;
      · norm_num +zetaDelta at *;
        obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := h_exists_j
        have hj_lo : m + 2 ≤ j := hj₁.1
        exact ⟨ m, m + 1, by linarith, j, by linarith, by linarith,
          by convert hm.1.1 using 1; ring,
          hj₂,
          by convert hj₃ using 1; ring,
          by linarith [hm.1.2],
          by omega,
          by omega ⟩
      · have h_even_subset : 4 ∈ A ∧ 6 ∈ A ∧ 8 ∈ A := by
          apply even_subset_structure n m hn A hA_subset hA_card hm.1.2 hm.1.1 hm.2;
          intros x y hx hy hxy
          by_contra h_contra
          have h_consecutive : y = x + 1 := by
            linarith;
          simp_all +decide [ Finset.mem_inter ];
          exact h_exists_j ( x - m ) ( by omega ) ( by omega ) ( by convert hx.1 using 1; omega ) ( by convert hy.1 using 1; omega );
        exact ⟨ 1, 3, 5, by decide, by decide, by decide, by aesop, by aesop, by aesop, by omega, by omega, by omega ⟩

/-
If $A \subseteq \{1, 2, \ldots, 2n\}$ is any set with $|A| \ge n + 2032$ elements, then distinct integers $b_1, b_2, b_3, b_4$ exist with $b_i + b_j \in A$ for $1 \le i < j \le 4$. That is, $g_4(n) ≤ 2032$.
-/
theorem theorem_pairwise_sums_of_four_elements_fake (n : ℕ) (A : Finset ℤ)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (hA_card : A.card ≥ n + 2032) :
    ∃ b₁ b₂ b₃ b₄ : ℤ,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₃ ≠ b₄ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₂ + b₃, b₂ + b₄, b₃ + b₄} ⊆ A := by
        obtain ⟨t, ht, h_t_val, d, hd⟩ : ∃ t : ℕ, t = (A.filter Even).card ∧ t ≥ 2032 ∧ ∃ d : ℕ, t = 2032 + d := by
          have h_even_count : (Finset.filter Even A).card + (Finset.filter Odd A).card = A.card := by
            rw [ Finset.card_filter, Finset.card_filter ];
            simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones A ▸ by congr; ext x; aesop;
          have h_odd_count : (Finset.filter Odd A).card ≤ n := by
            have h_odd_count : (Finset.filter Odd A).card ≤ (Finset.filter Odd (Finset.Icc 1 (2 * n))).card := by
              convert Finset.card_mono <| Finset.filter_subset_filter _ hA_subset using 1;
              refine' Finset.card_bij ( fun x hx => Int.natAbs x ) _ _ _ <;> norm_num;
              · exact fun a ha₁ ha₂ ha₃ => ⟨ ⟨ ha₁, mod_cast ha₂ ⟩, ha₃ ⟩;
              · exact fun b hb₁ hb₂ hb₃ => ⟨ Int.natAbs b, ⟨ ⟨ by linarith [ abs_of_nonneg ( by linarith : 0 ≤ b ) ], by linarith [ abs_of_nonneg ( by linarith : 0 ≤ b ) ] ⟩, by simpa [ ← Int.odd_iff ] using hb₃ ⟩, by simp +decide [ abs_of_nonneg ( by linarith : 0 ≤ b ) ] ⟩ ;
            convert h_odd_count using 1;
            rw [ Finset.card_eq_of_bijective ];
            use fun i hi => 2 * i + 1;
            · simp +zetaDelta at *;
              exact fun a ha₁ ha₂ ha₃ => by obtain ⟨ k, rfl ⟩ := ha₃; exact ⟨ k, by linarith, rfl ⟩ ;
            · exact fun i hi => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, by simp +decide [ parity_simps ] ⟩;
            · grind;
          exact ⟨ _, rfl, by linarith, _, Eq.symm ( Nat.add_sub_of_le ( by linarith ) ) ⟩;
        by_cases h_exists_x : ∃ x ∈ A, Even x ∧ x ∈ Finset.Icc (4 * d + 4 : ℤ) ((2 * n : ℤ) - 4 * d - 4);
        · obtain ⟨x, hx_A, hx_even, hx_range⟩ := h_exists_x
          set m := x / 2 with hm_def
          have hm_in : 2 * m ∈ A := by
            rwa [ Int.mul_ediv_cancel' ( even_iff_two_dvd.mp hx_even ) ]
          have hm_range : 2 * d + 2 ≤ m ∧ m ≤ n - 2 * d - 2 := by
            constructor <;> linarith [ Int.ediv_mul_cancel ( even_iff_two_dvd.mp hx_even ), Finset.mem_Icc.mp hx_range ]
          apply upper_case_2_helper n d A hA_subset hA_card t ht hd m hm_in hm_range;
        · apply upper_case_no_middle_helper n d A hA_subset t ht hd;
          aesop

/-
If $A \subseteq \{1, 2, \ldots, 2n\}$ is any set with $|A| \ge n + (10^9 - 20) \log n + 10$ elements, then distinct integers $b_1, b_2, b_3, b_4, b_5$ exist with $b_i + b_j \in A$ for $1 \le i < j \le 5$.
-/
theorem theorem_pairwise_sums_of_five_elements_fake (n : ℕ) (A : Finset ℤ)
    (hA_subset : A ⊆ Finset.Icc 1 (2 * n))
    (hA_card : (A.card : ℝ) ≥ n + C_5 * Real.log n + 10) :
    ∃ b₁ b₂ b₃ b₄ b₅ : ℤ,
      b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₁ ≠ b₅ ∧
      b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₂ ≠ b₅ ∧
      b₃ ≠ b₄ ∧ b₃ ≠ b₅ ∧
      b₄ ≠ b₅ ∧
      {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₁ + b₅,
       b₂ + b₃, b₂ + b₄, b₂ + b₅,
       b₃ + b₄, b₃ + b₅,
       b₄ + b₅} ⊆ A := by
         by_cases h_case1 : (A.filter (fun x => x ∈ Finset.Icc (⌈6.5 * ((A.filter Even).card - C_5 * Real.log n)⌉) (⌊2 * (n : ℝ) - 6.5 * ((A.filter Even).card - C_5 * Real.log n)⌋) ∧ Even x)).card ≤ 100 * Real.log n;
         · apply case1_logic n A hA_subset (A.filter Even).card rfl ((A.filter Even).card - C_5 * Real.log n) rfl;
           · have := d_bounds n A hA_subset hA_card; aesop;
           · apply case1_n_large n ((A.filter Even).card - C_5 * Real.log n) (by
             have := d_bounds n A hA_subset hA_card; aesop;) (by
             simp +zetaDelta at *;
             exact_mod_cast le_trans ( Finset.card_le_card ( Finset.filter_subset _ _ ) ) ( le_trans ( Finset.card_le_card hA_subset ) ( by norm_num ) ));
           · convert h_case1 using 1;
         · -- Apply the logic from Case 2 to find the required subset.
           apply case2_logic n A hA_subset (A.filter Even).card rfl ((A.filter Even).card - C_5 * Real.log n) rfl (by
           apply d_bounds n A hA_subset hA_card) (by
           apply case1_n_large n ((A.filter Even).card - C_5 * Real.log n) (by
           have := d_bounds n A hA_subset hA_card; aesop;) (by
           simp +zetaDelta at *;
           exact_mod_cast le_trans ( Finset.card_le_card ( Finset.filter_subset _ _ ) ) ( le_trans ( Finset.card_le_card hA_subset ) ( by norm_num ) ))) (Finset.Icc (⌈6.5 * ((A.filter Even).card - C_5 * Real.log n)⌉) (⌊2 * (n : ℝ) - 6.5 * ((A.filter Even).card - C_5 * Real.log n)⌋)) rfl (by
           exact not_le.mp h_case1)

/-
$g_3(n) = 1$ for all $n ≥ 3$.
-/
theorem pairwise_sums_of_three_elements (n : ℕ) (hn : n ≥ 3) : g 3 n = 1 := by
  refine' le_antisymm _ _;
  · exact Nat.sInf_le ( g_3_le_1 n hn );
  · refine' Nat.pos_of_ne_zero _;
    simp_all +decide [ g ];
    exact ⟨ g_3_ge_1 n, Set.Nonempty.ne_empty ⟨ 1, g_3_le_1 n hn ⟩ ⟩

/-
$h_3(n) = 2$ for all $n ≥ 4$.
-/
theorem pairwise_sums_of_three_positive_elements (n : ℕ) (hn : n ≥ 4) : h 3 n = 2 := by
  have h_def : ∀ m, m < 2 → ¬PropertyQ n 3 m := by
    intro m hm h;
    exact h_3_ge_2 n ( by linarith ) ( by exact fun A hA hA' => h A hA ( by linarith ) );
  have h_two : PropertyQ n 3 2 := by
    intro A hA_sub hA_card
    obtain ⟨b₁, b₂, b₃, hb₁b₂, hb₁b₃, hb₂b₃, hb₁, hb₂, hb₃⟩ : ∃ b₁ b₂ b₃ : ℕ, b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ ∧ (b₁ + b₂) ∈ A ∧ (b₁ + b₃) ∈ A ∧ (b₂ + b₃) ∈ A ∧ b₁ > 0 ∧ b₂ > 0 ∧ b₃ > 0 := pairwise_sums_of_three_positive_elements_fake n hn A hA_sub hA_card
    use {b₁, b₂, b₃};
    simp_all +decide [ Finset.subset_iff ];
    exact ⟨ fun _ => by simpa only [ add_comm ] using hb₁, fun _ => by simpa only [ add_comm ] using hb₂, fun _ => by simpa only [ add_comm ] using hb₃.1 ⟩;
  exact le_antisymm ( Nat.sInf_le h_two ) ( le_csInf ⟨ 2, h_two ⟩ fun m hm => not_lt.1 fun contra => h_def m contra hm )

/-
$g_4(n) ≤ 2032$.
-/
theorem theorem_pairwise_sums_of_four_elements (n : ℕ) : g 4 n ≤ 2032 := by
  refine' csInf_le _ _ <;> norm_num;
  intro A hA hA_card
  obtain ⟨b₁, b₂, b₃, b₄, hb₁, hb₂, hb₃, hb₄, hb_distinct, hb_subset⟩ : ∃ b₁ b₂ b₃ b₄ : ℤ, b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₃ ≠ b₄ ∧ {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₂ + b₃, b₂ + b₄, b₃ + b₄} ⊆ A := by
    apply_rules [ theorem_pairwise_sums_of_four_elements_fake ];
  use { b₁, b₂, b₃, b₄ };
  grind +ring

/-
$g_5(n) ≤ 10^9 \log n$ for all $n ≥ 2$.
-/
theorem theorem_pairwise_sums_of_five_elements (n : ℕ) (hn : n ≥ 2) : g 5 n ≤ 10^9 * Real.log n := by
  refine' le_trans ( Nat.cast_le.mpr _ ) _;
  exact ⌊10^9 * Real.log n⌋₊;
  · refine' csInf_le _ _ <;> norm_num;
    intro A hA_sub hA_card
    obtain ⟨b₁, b₂, b₃, b₄, b₅, hb⟩ : ∃ b₁ b₂ b₃ b₄ b₅ : ℤ, b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₁ ≠ b₅ ∧ b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₂ ≠ b₅ ∧ b₃ ≠ b₄ ∧ b₃ ≠ b₅ ∧ b₄ ≠ b₅ ∧ {b₁ + b₂, b₁ + b₃, b₁ + b₄, b₁ + b₅, b₂ + b₃, b₂ + b₄, b₂ + b₅, b₃ + b₄, b₃ + b₅, b₄ + b₅} ⊆ A := by
      convert theorem_pairwise_sums_of_five_elements_fake n A _ _ using 1;
      · exact hA_sub;
      · contrapose! hA_card;
        rw [ ← @Nat.cast_lt ℝ ] ; norm_num [ C_5 ] at *;
        linarith [ Nat.lt_floor_add_one ( 1000000000 * Real.log n ), show ( n : ℝ ) ≥ 2 by norm_cast, Real.log_two_gt_d9, Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≥ 2 by norm_cast ) ];
    use {b₁, b₂, b₃, b₄, b₅};
    simp_all +decide [ Finset.subset_iff ];
    grind;
  · exact Nat.floor_le <| by positivity;

#print axioms pairwise_sums_of_three_elements
#print axioms pairwise_sums_of_three_positive_elements
#print axioms theorem_pairwise_sums_of_four_elements
#print axioms theorem_pairwise_sums_of_five_elements
