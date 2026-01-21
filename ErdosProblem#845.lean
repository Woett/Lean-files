/-
There exists an absolute constant $C$ such that every positive integer can be written as a sum of distinct $3$-smooth integers for which the ratio between the largest and smallest is smaller than $C$. This solves Erdős problem #845 (https://www.erdosproblems.com/845), and was proven by Anneroos Everts and me.

Wouter van Doorn and Anneroos R. F. Everts, Smooth sums with small spacings. arXiv:2511.04585 (2025).

With the help of Aristotle, Boris Alexeev formalized most of the results in the above paper into Lean as can be found here:

https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos845.md

Anneroos and I moreover proved that one can take $C = 6$. The proof of this bound had however not been formalized yet, and this file is here to fill that final remaining gap. This could not have been done without the help of Aristotle, ChatGPT, Google, Gemini and Claude, so I thank and welcome our AI overlords.

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
set_option linter.unusedVariables false
noncomputable section

/-
The set of 3-smooth numbers (numbers whose prime factors are 2 or 3).
-/
def smooth3 : Set ℕ := Nat.smoothNumbers 4

/-
The set of 3-smooth numbers is infinite.
-/
theorem smooth3_infinite : {x | x ∈ smooth3}.Infinite := by
  -- The set of 3-smooth numbers contains all powers of 2.
  have h_pow2 : ∀ k : ℕ, 2 ^ k ∈ smooth3 := by
    intro k;
    apply Nat.mem_smoothNumbers.mpr;
    norm_num [ Nat.primeFactorsList ];
    intro p pp dp; have := pp.dvd_of_dvd_pow dp; ( have := Nat.le_of_dvd ( by decide ) this; interval_cases p <;> trivial; );
  exact Set.infinite_of_injective_forall_mem ( fun a b h => by simpa using h ) h_pow2

/-
`A n` is the `n`-th 3-smooth number.
-/
noncomputable def A (n : ℕ) : ℕ := Nat.nth (· ∈ smooth3) n

/-
`A n` is a 3-smooth number.
-/
theorem A_mem (n : ℕ) : A n ∈ smooth3 := by
  exact Nat.nth_mem_of_infinite ( smooth3_infinite ) _

/-
`A` is strictly monotonic.
-/
theorem A_strictMono : StrictMono A := by
  refine' strictMono_nat_of_lt_succ fun n => _;
  exact Nat.nth_strictMono ( show { x | x ∈ smooth3 }.Infinite from by exact smooth3_infinite ) ( Nat.lt_succ_self _ )

/-
The range of `A` is exactly `smooth3`.
-/
theorem A_range : Set.range A = smooth3 := by
  ext x;
  constructor;
  · exact fun hx => by obtain ⟨ n, rfl ⟩ := hx; exact A_mem n;
  · intro hx;
    -- Since $x$ is a 3-smooth number, there exists some $n$ such that $A n = x$.
    use Nat.count (· ∈ smooth3) x;
    exact Nat.nth_count hx

/-
`sumA k` is the sum of the first `k` 3-smooth numbers.
-/
def sumA (k : ℕ) : ℕ := (Finset.range k).sum A

/-
`sumA` is unbounded.
-/
theorem sumA_unbounded : ∀ N, ∃ k, N < sumA k := by
  intro N;
  -- Since the 3-smooth numbers are infinite, the sum of the first k 3-smooth numbers is unbounded.
  have h_unbounded : ∀ M : ℕ, ∃ k : ℕ, (Finset.range k).sum A > M := by
    -- Since the 3-smooth numbers are infinite and strictly increasing, their sum is also unbounded.
    have h_unbounded : ∀ M : ℕ, ∃ k : ℕ, A k > M := by
      intro M;
      exact ⟨ _, A_strictMono.id_le _ ⟩;
    exact fun M => by rcases h_unbounded M with ⟨ k, hk ⟩ ; exact ⟨ k + 1, by simpa [ Finset.sum_range_succ ] using by linarith [ show ∑ i ∈ Finset.range k, A i ≥ 0 by exact Nat.zero_le _ ] ⟩ ;
  exact h_unbounded N

/-
`m_index n` is the smallest `k` such that `sumA k > n / 2`.
-/
noncomputable def m_index (n : ℕ) : ℕ := Nat.find (sumA_unbounded (n / 2))

/-
`m_index n` is the smallest `k` such that `sumA k > n / 2`.
-/
theorem m_index_spec (n : ℕ) : n / 2 < sumA (m_index n) ∧ ∀ k < m_index n, sumA k ≤ n / 2 := by
  exact ⟨ Nat.find_spec ( sumA_unbounded ( n / 2 ) ), fun k hk => le_of_not_gt fun hk' => Nat.find_min ( sumA_unbounded ( n / 2 ) ) hk hk' ⟩

/-
The sequence `A` is unbounded.
-/
theorem A_unbounded (C : ℕ) : ∃ k, C ≤ A k := by
  use C;
  induction' C with C ih <;> [ norm_num; linarith [ A_strictMono ( Nat.lt_succ_self C ) ] ]

/-
`v1`, `v2`, `v3` are indices such that `A v1` is the largest element in `[1, A m)`, `A v2` in `[A m, 3 A m)`, and `A v3` in `[3 A m, 6 A m)`.
-/
noncomputable def v1 (n : ℕ) : ℕ := m_index n - 1

noncomputable def v2 (n : ℕ) : ℕ := Nat.find (A_unbounded (3 * A (m_index n))) - 1

noncomputable def v3 (n : ℕ) : ℕ := Nat.find (A_unbounded (6 * A (m_index n))) - 1

theorem v_spec (n : ℕ) :
  v1 n = m_index n - 1 ∧
  A (v2 n) < 3 * A (m_index n) ∧ 3 * A (m_index n) ≤ A (v2 n + 1) ∧
  A (v3 n) < 6 * A (m_index n) ∧ 6 * A (m_index n) ≤ A (v3 n + 1) := by
    unfold v1 v2 v3;
    have := Nat.find_spec ( show ∃ m : ℕ, 3 * A ( m_index n ) ≤ A m from by
                              have := A_unbounded ( 3 * A ( m_index n ) ) ; aesop; );
    rcases k : Nat.find ( show ∃ k, 3 * A ( m_index n ) ≤ A k from by
                            exact ⟨ _, this ⟩ ) with ( _ | k ) <;> simp_all +decide;
    · linarith [ A_strictMono.monotone ( show 0 ≤ m_index n from Nat.zero_le _ ), A_mem 0, Nat.pos_of_ne_zero ( show A 0 ≠ 0 from by
                                                                                                                  intro h; have := A_mem 0; simp_all +decide ;
                                                                                                                  exact absurd this ( by rw [ show smooth3 = { x | x ∈ Nat.smoothNumbers 4 } from rfl ] ; exact fun h => by have := Nat.mem_smoothNumbers.mp h; aesop ) ) ];
    · have := Nat.find_spec ( show ∃ k, 6 * A ( m_index n ) ≤ A k from by
                                have h_unbounded : ∀ M : ℕ, ∃ k, A k > M := by
                                  intro M; exact (by
                                  have := A_unbounded ( M + 1 ) ; aesop;);
                                exact Exists.elim ( h_unbounded ( 6 * A ( m_index n ) ) ) fun k hk => ⟨ k, le_of_lt hk ⟩ );
      rcases x : Nat.find ( show ∃ k, 6 * A ( m_index n ) ≤ A k from by
                              exact ⟨ _, this ⟩ ) with ( _ | x ) <;> simp_all +decide [ Nat.find_eq_iff ];
      grind


/-
Here are two lemmas suggested by Claude, in order to get rid of the use of native_decide in the proof of mul_closure. Success!
-/
lemma two_mem_smooth3 : 2 ∈ smooth3 := by
  rw [show smooth3 = Nat.smoothNumbers 4 from rfl]
  refine ⟨by norm_num, fun p hp => ?_⟩
  norm_num [Nat.primeFactorsList] at hp
  omega

lemma three_mem_smooth3 : 3 ∈ smooth3 := by
  rw [show smooth3 = Nat.smoothNumbers 4 from rfl]
  refine ⟨by norm_num, fun p hp => ?_⟩
  norm_num [Nat.primeFactorsList] at hp
  omega

/-
Multiplying an element of $A$ by $2$ or $3$ yields another element of $A$ at a larger index.
-/
theorem mul_closure (k : ℕ) (s : ℕ) (hs : s ∈ ({2, 3} : Set ℕ)) :
  ∃ l > k, s * A k = A l := by
    obtain ⟨l, hl⟩ : ∃ l, (A l) = (s * A k) := by
      have h_smooth : s * A k ∈ smooth3 := by
        have hs_smooth : s ∈ smooth3 := by
          rcases hs with (rfl | rfl)
          · exact two_mem_smooth3
          · exact three_mem_smooth3
        exact Nat.mul_mem_smoothNumbers hs_smooth (A_mem k)
      exact A_range.symm.subset h_smooth
    use l;
    -- Since $s \geq 2$, we have $s * A k > A k$, which implies $l > k$.
    have h_l_gt_k : s * A k > A k := by
      have h_A_k_pos : 0 < A k := by
        apply Nat.pos_of_ne_zero
        intro h_zero
        have := A_mem k
        simp [h_zero] at this;
        exact absurd this ( by rw [ show smooth3 = Nat.smoothNumbers 4 from rfl ] ; decide );
      aesop;
    exact ⟨ Nat.lt_of_not_ge fun h => h_l_gt_k.not_ge <| hl ▸ Nat.le_of_lt_succ ( by linarith [ A_strictMono.monotone h ] ), hl.symm ⟩

/-
If $k \le v_1$, then multiplying $A_k$ by 2 or 3 results in an element $A_l$ with $l \le v_2$.
-/
theorem mul_closure_bound (n : ℕ) (h : 0 < n) (k : ℕ) (s : ℕ) (hs : s ∈ ({2, 3} : Set ℕ)) (l : ℕ) (hl : s * A k = A l) :
  k ≤ v1 n → l ≤ v2 n := by
    -- Assume $k \le v_1$, then $A k \le A (v_1) < A (m)$.
    intro hkv1
    have hAk_lt_Am : A k < A (m_index n) := by
      by_cases hk : k = m_index n - 1;
      · rcases n : m_index n with ( _ | _ | m ) <;> simp_all +decide;
        · unfold m_index at n;
          simp_all +decide [ Nat.find_eq_iff ];
          exact n.not_ge ( Nat.zero_le _ );
        · exact A_strictMono ( by decide );
        · exact A_strictMono ( Nat.lt_succ_self _ );
      · exact lt_of_lt_of_le ( show A k < A ( m_index n - 1 ) from by exact ( A_strictMono <| lt_of_le_of_ne hkv1 hk ) ) ( show A ( m_index n - 1 ) ≤ A ( m_index n ) from by exact ( A_strictMono.monotone <| Nat.pred_le _ ) );
    -- Since $s * A k = A l$ and $A k < A (m_index n)$, we have $A l < 3 * A (m_index n)$.
    have hAl_lt_3Am : A l < 3 * A (m_index n) := by
      grind;
    contrapose! hAl_lt_3Am;
    have hAl_ge_3Am : ∀ m ≥ v2 n + 1, A m ≥ 3 * A (m_index n) := by
      intros m hm
      have hAl_ge_3Am : A (v2 n + 1) ≥ 3 * A (m_index n) := by
        exact v_spec n |>.2.2.1;
      exact le_trans hAl_ge_3Am ( monotone_nat_of_le_succ ( fun n => Nat.le_of_lt ( A_strictMono n.lt_succ_self ) ) hm );
    exact hAl_ge_3Am l hAl_lt_3Am

/-
The potential increase of a coefficient is bounded by 3 (or 2 if $A_l$ is a power of 2).
-/
def potential_increase (n : ℕ) (l : ℕ) : ℕ :=
  (if ∃ k < l, 2 * A k = A l then 2 else 0) + (if ∃ k < l, 3 * A k = A l then 1 else 0)

theorem potential_increase_bound (n : ℕ) (h : 0 < n) (l : ℕ) :
  potential_increase n l ≤ 3 ∧ (A l ∈ {2^j | j : ℕ} → potential_increase n l ≤ 2) := by
    unfold potential_increase;
    split_ifs <;> norm_num;
    -- If $A_l$ is a power of 2, then $3 * A_k$ must also be a power of 2, which is impossible since $3$ is not a power of 2.
    intros x hx
    have h_contra : 3 * A (Classical.choose ‹∃ k < l, 3 * A k = A l›) = 2 ^ x := by
      linarith [ Classical.choose_spec ‹∃ k < l, 3 * A k = A l› ];
    have := congr_arg ( · % 3 ) h_contra; norm_num [ Nat.pow_mod ] at this;
    rw [ eq_comm, ← Nat.dvd_iff_mod_eq_zero ] at this; norm_num [ Nat.Prime.dvd_iff_one_le_factorization ] at this;

/-
Any number $R$ can be written as a sum of distinct elements of $A$ which are powers of 2.
-/
theorem exists_binary_expansion_in_A (R : ℕ) :
  ∃ J : Finset ℕ, R = ∑ j ∈ J, A j ∧ ∀ j ∈ J, ∃ k, A j = 2^k := by
    -- By definition of binary representation, every natural number can be written as a sum of distinct powers of 2.
    have h_binary : ∀ n : ℕ, ∃ J : Finset ℕ, n = ∑ j ∈ J, 2 ^ j := by
      intro n
      induction' n using Nat.strong_induction_on with n ih;
      rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
      · exact Exists.elim ( if h : k = 0 then ⟨ ∅, by aesop ⟩ else ih k ( by linarith [ Nat.pos_of_ne_zero h ] ) ) fun J hJ => ⟨ J.image fun x => x + 1, by simp +arith +decide [ hJ, pow_succ', Finset.mul_sum _ _ _ ] ⟩;
      · obtain ⟨ J, hJ ⟩ := ih k ( by linarith );
        use J.image ( fun j => j + 1 ) ∪ { 0 } ; simp +arith +decide [hJ, Finset.mul_sum _ _ _,
          pow_succ'];
        ring;
    obtain ⟨ J, hJ ⟩ := h_binary R;
    -- Since $A$ is strictly monotonic and covers all powers of 2, for each $j \in J$, there exists $k$ such that $A k = 2^j$.
    have h_exists_k : ∀ j ∈ J, ∃ k, A k = 2 ^ j := by
      -- Since $A$ is strictly monotonic and covers all powers of 2, for each $j \in J$, there exists $k$ such that $A k = 2^j$ by the definition of $A$.
      intro j hj
      have h_exists_k : 2 ^ j ∈ smooth3 := by
        refine' Nat.mem_smoothNumbers.mpr _;
        norm_num [ Nat.primeFactorsList ];
        intro p pp dp; have := pp.dvd_of_dvd_pow dp; ( have := Nat.le_of_dvd ( by decide ) this; interval_cases p <;> trivial; );
      exact ⟨ Nat.count ( · ∈ smooth3 ) ( 2 ^ j ), Nat.nth_count h_exists_k ⟩;
    choose! k hk using h_exists_k;
    use Finset.image k J;
    rw [ Finset.sum_image ] ; aesop;
    intro x hx y hy; have := hk x hx; have := hk y hy; aesop;

/-
If $k \le v_2$, then multiplying $A_k$ by 2 results in an element $A_l$ with $l \le v_3$.
-/
def mul_closure_bound_part2 (n : ℕ) (h : 0 < n) (k : ℕ) (l : ℕ) (hl : 2 * A k = A l) :
  k ≤ v2 n → l ≤ v3 n := by
    intro hk_le;
    -- Since $k \le v_2$, we have $A k \le A (v2 n)$.
    have h_ak_le_av2 : A k ≤ A (v2 n) := by
      exact monotone_nat_of_le_succ ( fun n => A_strictMono.monotone n.le_succ ) hk_le;
    have := v_spec n;
    exact le_of_not_gt fun h => by linarith [ show A l ≥ A ( v3 n + 1 ) from by exact monotone_nat_of_le_succ ( fun n => Nat.le_of_lt <| A_strictMono <| Nat.lt_succ_self n ) h ] ;

/-
For any $l$, there is at most one index $i$ such that $2 A_i = A_l$.
-/
theorem unique_half (l : ℕ) : Set.Subsingleton { i | 2 * A i = A l } := by
  intro i hi j hj; have := A_strictMono.injective; ( have := A_strictMono.injective ( by linarith [ Set.mem_setOf.mp hi, Set.mem_setOf.mp hj ] : A i = A j ) ; aesop; )

/-
`potential_increase` is the sum of `potential_contribution`s.
-/
def potential_contribution (k i : ℕ) : ℕ :=
  (if 2 * A k = A i then 2 else 0) + (if 3 * A k = A i then 1 else 0)

theorem potential_increase_eq_sum (n : ℕ) (l : ℕ) :
  potential_increase n l = (Finset.range l).sum (fun k => potential_contribution k l) := by
    unfold potential_increase potential_contribution;
    split_ifs;
    · rename_i h₁ h₂;
      -- Since there exists a unique $k$ such that $2 * A k = A l$ and a unique $k$ such that $3 * A k = A l$, the sum simplifies to $2 + 1$.
      obtain ⟨k₁, hk₁_lt, hk₁_eq⟩ := h₁
      obtain ⟨k₂, hk₂_lt, hk₂_eq⟩ := h₂
      have h_unique : ∀ k, 2 * A k = A l → k = k₁ := by
        exact fun k hk => by have := unique_half l; have := this ( by aesop : 2 * A k = A l ) ( by aesop : 2 * A k₁ = A l ) ; aesop;
      have h_unique' : ∀ k, 3 * A k = A l → k = k₂ := by
        exact fun k hk => le_antisymm ( le_of_not_gt fun hk' => by linarith [ A_strictMono hk' ] ) ( le_of_not_gt fun hk' => by linarith [ A_strictMono hk' ] );
      rw [ Finset.sum_eq_add ( k₁ ) ( k₂ ) ] <;> norm_num [ hk₁_lt, hk₁_eq, hk₂_lt, hk₂_eq ];
      · grind;
      · grind;
      · exact fun c hc₁ hc₂ hc₃ => ⟨ fun hc₄ => hc₂ <| h_unique c hc₄, fun hc₄ => hc₃ <| h_unique' c hc₄ ⟩;
    · rw [ Finset.sum_eq_single ( Classical.choose ‹∃ k < l, 2 * A k = A l› ) ] <;> simp_all +decide;
      · have := Classical.choose_spec ‹∃ k < l, 2 * A k = A l›; aesop;
      · exact fun x hx₁ hx₂ hx₃ => hx₂ <| by have := Classical.choose_spec ‹∃ k < l, 2 * A k = A l›; exact le_antisymm ( le_of_not_gt fun hx₄ => by linarith [ A_strictMono hx₄ ] ) ( le_of_not_gt fun hx₄ => by linarith [ A_strictMono hx₄ ] ) ;
      · exact fun h => absurd h ( not_le_of_gt ( Classical.choose_spec ‹∃ k < l, 2 * A k = A l› |>.1 ) );
    · rw [ Finset.sum_eq_single ( ‹∃ k < l, 3 * A k = A l›.choose ) ];
      · have := ‹∃ k < l, 3 * A k = A l›.choose_spec; aesop;
      · intro k hk₁ hk₂; split_ifs <;> simp_all +decide ;
        have := ‹∃ k < l, 3 * A k = A l›.choose_spec;
        exact hk₂ ( le_antisymm ( le_of_not_gt fun h => by linarith [ A_strictMono h ] ) ( le_of_not_gt fun h => by linarith [ A_strictMono h ] ) );
      · exact fun h => False.elim <| h <| Finset.mem_range.mpr <| by linarith [ ‹∃ k < l, 3 * A k = A l›.choose_spec ] ;
    · rw [ Finset.sum_eq_zero ] <;> aesop

/-
For any $x \in \{2, 3, 4, 5\}$ and $k \le v_1 n$, we can decompose $x A_k$ into a sum of $A_l$'s where the indices $l$ are in $(k, v_2 n]$ and their multiplicities are bounded by `potential_contribution`.
-/
theorem decomposition_lemma (n : ℕ) (h : 0 < n) (k : ℕ) (hk : k ≤ v1 n) (x : ℕ) (hx : x ∈ ({2, 3, 4, 5} : Set ℕ)) :
  ∃ L : Multiset ℕ,
    (L.map A).sum = x * A k ∧
    (∀ l ∈ L, k < l ∧ l ≤ v2 n) ∧
    (∀ l, L.count l ≤ potential_contribution k l) := by
      -- For each $x \in \{2, 3, 4, 5\}$, we can decompose $x A_k$ into a sum of $A_l$'s where the indices $l$ are in $(k, v_2 n]$ and their multiplicities are bounded by `potential_contribution`.
      obtain ⟨l2, hl2⟩ : ∃ l2, 2 * A k = A l2 ∧ k < l2 ∧ l2 ≤ v2 n := by
        obtain ⟨l2, hl2⟩ : ∃ l2, 2 * A k = A l2 ∧ k < l2 := by
          have := mul_closure k 2 ( by norm_num ) ; aesop;
        exact ⟨ l2, hl2.1, hl2.2, mul_closure_bound n h k 2 ( by norm_num ) l2 hl2.1 hk ⟩
      obtain ⟨l3, hl3⟩ : ∃ l3, 3 * A k = A l3 ∧ k < l3 ∧ l3 ≤ v2 n := by
        obtain ⟨l3, hl3⟩ := mul_closure k 3 (by norm_num);
        exact ⟨ l3, hl3.2, hl3.1, mul_closure_bound n h k 3 ( by norm_num ) l3 hl3.2 hk ⟩;
      by_cases hx2 : x = 2 ∨ x = 4 ∨ x = 5;
      · rcases hx2 with ( rfl | rfl | rfl );
        · use {l2}
          simp [hl2];
          intro l; by_cases h : l = l2 <;> simp_all +decide [ potential_contribution ] ;
          split_ifs <;> norm_num;
        · refine' ⟨ { l2, l2 }, _, _, _ ⟩ <;> simp_all +decide [ potential_contribution ];
          · linarith;
          · intro l; erw [ Multiset.count_cons, Multiset.count_singleton ] ; aesop;
        · refine' ⟨ { l2, l3 }, _, _, _ ⟩ <;> simp_all +decide [ potential_contribution ];
          · grind;
          · intro l; rw [ Multiset.count_cons, Multiset.count_singleton ] ; aesop;
      · use {l3}; simp_all +decide [ potential_contribution ];
        intro l; rw [ Multiset.count_singleton ] ; aesop;

/-
We can reduce a coefficient $c_k \in \{2, 3, 4, 5\}$ (where $k \le v_1$) to 0, and compensate by increasing higher coefficients. The increase at any index $i$ is bounded by `potential_contribution k i`. The indices $i$ where $c'_i > c_i$ satisfy $i \le v_2 n$.
-/
theorem reduction_step_precise (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ)
  (h_sum : n = (Finset.range (v3 n + 1)).sum (fun i => c i * A i))
  (hk_le : k ≤ v1 n)
  (hc_k : c k ∈ ({2, 3, 4, 5} : Set ℕ)) :
  ∃ c' : ℕ → ℕ,
    n = (Finset.range (v3 n + 1)).sum (fun i => c' i * A i) ∧
    c' k = 0 ∧
    (∀ i < k, c' i = c i) ∧
    (∀ i, i ≠ k → c i ≤ c' i) ∧
    (∀ i, c' i > c i → k < i ∧ i ≤ v2 n) ∧
    (∀ i, c' i ≤ c i + potential_contribution k i) := by
      obtain ⟨L, hL_sum, hL_bounds, hL_contribution⟩ : ∃ L : Multiset ℕ, (L.map A).sum = c k * A k ∧ (∀ l ∈ L, k < l ∧ l ≤ v2 n) ∧ (∀ l, L.count l ≤ potential_contribution k l) := by
        exact decomposition_lemma n h k hk_le (c k) hc_k;
      refine' ⟨ fun i => if i = k then 0 else c i + Multiset.count i L, _, _, _, _, _, _ ⟩ <;> simp +contextual [ Finset.sum_ite, Finset.filter_ne' ];
      · have h_sum_eq : ∑ i ∈ Finset.range (v3 n + 1), (if i = k then 0 else c i + Multiset.count i L) * A i = ∑ i ∈ Finset.range (v3 n + 1), c i * A i + ∑ i ∈ Finset.range (v3 n + 1), Multiset.count i L * A i - c k * A k := by
          simp +decide [ Finset.sum_add_distrib, add_mul, Finset.sum_ite, Finset.filter_ne' ];
          rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_range.mpr ( Nat.lt_succ_of_le ( show k ≤ v3 n from le_trans hk_le ( by
                                                                                        refine' Nat.sub_le_sub_right _ _;
                                                                                        refine' Nat.le_of_not_lt fun h => _;
                                                                                        norm_num [ Nat.find_eq_iff ] at h;
                                                                                        exact h.elim fun m hm => by linarith [ hm.2, show A m < A ( m_index n ) from A_strictMono hm.1 ] ; ) ) ) ), ← Finset.sum_erase_add _ _ ( Finset.mem_range.mpr ( Nat.lt_succ_of_le ( show k ≤ v3 n from le_trans hk_le ( by
                                                                                                                                                                                                                      refine' Nat.sub_le_sub_right _ _;
                                                                                                                                                                                                                      refine' Nat.le_of_not_lt fun h => _;
                                                                                                                                                                                                                      norm_num [ Nat.find_eq_iff ] at h;
                                                                                                                                                                                                                      exact h.elim fun m hm => by linarith [ hm.2, show A m < A ( m_index n ) from A_strictMono hm.1 ] ; ) ) ) ) ] ; ring_nf;
          rw [ show Multiset.count k L = 0 from Multiset.count_eq_zero_of_notMem fun h => by linarith [ hL_bounds k h ] ] ; ring_nf;
          grind;
        have h_sum_eq : ∑ i ∈ Finset.range (v3 n + 1), Multiset.count i L * A i = (L.map A).sum := by
          have h_sum_eq : ∑ i ∈ Finset.range (v3 n + 1), Multiset.count i L * A i = ∑ i ∈ L.toFinset, Multiset.count i L * A i := by
            rw [ Finset.sum_subset ( show L.toFinset ⊆ Finset.range ( v3 n + 1 ) from fun x hx => Finset.mem_range.mpr <| Nat.lt_succ_of_le <| by linarith [ hL_bounds x <| Multiset.mem_toFinset.mp hx, show v2 n ≤ v3 n from by
                                                                                                                                                                                                          apply le_of_not_gt; intro h_contra;
                                                                                                                                                                                                          have := v_spec n;
                                                                                                                                                                                                          linarith [ A_strictMono.monotone ( show v3 n + 1 ≤ v2 n from by linarith ) ] ] ) ] ; simp +contextual;
          rw [ h_sum_eq ];
          simp +decide [ Finset.sum_multiset_map_count ];
        norm_num [ Finset.sum_ite, Finset.filter_ne' ] at * ; omega;
      · intro i hi; rw [ if_neg hi.ne ] ; rw [ Multiset.count_eq_zero.mpr ] <;> norm_num ; intro H ; linarith [ hL_bounds _ H ] ;
      · intro i hi; split_ifs at hi <;> simp +decide at hi ⊢ ;
        exact hL_bounds i ( Multiset.count_pos.mp hi );
      · grind

/-
A stronger version of `reduction_step_part2` that ensures the coefficient increase happens exactly at the index `l` where `2 * A k = A l`.
-/
theorem reduction_step_part2_strong (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ)
  (h_sum : n = (Finset.range (v3 n + 1)).sum (fun i => c i * A i))
  (hk_le : k ≤ v2 n)
  (hc_k : c k ∈ ({2, 3} : Set ℕ)) :
  ∃ c' : ℕ → ℕ,
    n = (Finset.range (v3 n + 1)).sum (fun i => c' i * A i) ∧
    c' k = c k - 2 ∧
    (∀ i < k, c' i = c i) ∧
    (∀ i, i ≠ k → c i ≤ c' i) ∧
    (∀ i, c' i > c i → k < i ∧ i ≤ v3 n ∧ 2 * A k = A i) ∧
    (∀ i, c' i ≤ c i + 1) := by
      obtain ⟨l, hl⟩ : ∃ l, 2 * A k = A l ∧ l > k ∧ l ≤ v3 n := by
        have := mul_closure k 2 ( by norm_num );
        exact ⟨ this.choose, this.choose_spec.2, this.choose_spec.1, mul_closure_bound_part2 n h k _ this.choose_spec.2 hk_le ⟩;
      refine' ⟨ fun i => if i = k then c k - 2 else if i = l then c i + 1 else c i, _, _, _, _, _, _ ⟩ <;> simp +contextual [ hl ];
      · convert h_sum using 1;
        simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
        rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_range.mpr ( show k < v3 n + 1 from by linarith ) ), ← Finset.sum_erase_add _ _ ( Finset.mem_erase_of_ne_of_mem ( by linarith ) ( Finset.mem_range.mpr ( show l < v3 n + 1 from by linarith ) ) ) ] ; ring_nf;
        grind;
      · grind;
      · grind;
      · grind;
      · grind

/-
Every element of the sequence A is positive.
-/
theorem A_pos (n : ℕ) : 0 < A n := by
  exact Nat.pos_of_ne_zero fun h => by have := A_mem n; simp_all +decide [ smooth3 ] ;

/-
Defines the transformation of coefficients at step `k`, using the stronger reduction lemma.
-/
noncomputable def step_transform_v2 (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  if h_sum : n = (Finset.range (v3 n + 1)).sum (fun i => c i * A i) then
    if hk : k ≤ v1 n then
      if hc : c k ∈ ({2, 3, 4, 5} : Set ℕ) then
        Classical.choose (reduction_step_precise n h c k h_sum hk hc)
      else c
    else if hk' : k ≤ v2 n then
      if hc : c k ∈ ({2, 3} : Set ℕ) then
        Classical.choose (reduction_step_part2_strong n h c k h_sum hk' hc)
      else c
    else c
  else c

/-
`step_transform_v2` preserves the sum $n = \sum c_i A_i$.
-/
theorem step_transform_v2_sum_preserved (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ)
  (h_sum : n = (Finset.range (v3 n + 1)).sum (fun i => c i * A i)) :
  n = (Finset.range (v3 n + 1)).sum (fun i => (step_transform_v2 n h c k i) * A i) := by
    unfold step_transform_v2;
    split_ifs;
    · exact Classical.choose_spec ( reduction_step_precise n h c k h_sum ‹_› ‹_› ) |>.1;
    · exact h_sum;
    · exact Classical.choose_spec ( reduction_step_part2_strong n h c k h_sum ‹_› ‹_› ) |>.1;
    · exact h_sum;
    · exact h_sum

/-
The coefficients after one step of transformation are bounded by the previous coefficients plus the potential contribution from the current index.
-/
theorem step_transform_v2_bound (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ)
  (h_sum : n = (Finset.range (v3 n + 1)).sum (fun i => c i * A i)) :
  ∀ i, step_transform_v2 n h c k i ≤ c i + potential_contribution k i := by
    unfold step_transform_v2;
    split_ifs <;> norm_num;
    · rename_i hk₁ hk₂;
      exact Classical.choose_spec ( reduction_step_precise n h c k h_sum hk₁ hk₂ ) |>.2.2.2.2.2;
    · rename_i h₁ h₂ h₃;
      have := Classical.choose_spec ( reduction_step_part2_strong n h c k h_sum h₂ h₃ );
      unfold potential_contribution;
      grind

/-
The sequence of coefficients generated by `coeffs_sequence_v2` preserves the sum $n = \sum c_i A_i$ at every step.
-/
noncomputable def coeffs_sequence_v2 (n : ℕ) (h : 0 < n) (c_init : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => c_init
  | k + 1 => step_transform_v2 n h (coeffs_sequence_v2 n h c_init k) k

theorem coeffs_sequence_v2_sum_preserved (n : ℕ) (h : 0 < n) (c_init : ℕ → ℕ) (k : ℕ)
  (h_sum : n = (Finset.range (v3 n + 1)).sum (fun i => c_init i * A i)) :
  n = (Finset.range (v3 n + 1)).sum (fun i => coeffs_sequence_v2 n h c_init k i * A i) := by
    -- We prove by induction on $k$ using the definition of `coeffs_sequence_v2` and the base case.
    suffices h_induction : ∀ k, n = (Finset.range (v3 n + 1)).sum (fun i => (coeffs_sequence_v2 n h c_init k i) * A i) → n = (Finset.range (v3 n + 1)).sum (fun i => (step_transform_v2 n h (coeffs_sequence_v2 n h c_init k) k i) * A i) by
      induction' k with k ih;
      · exact h_sum;
      · exact h_induction k ih;
    exact fun k a => step_transform_v2_sum_preserved n h (coeffs_sequence_v2 n h c_init k) k a

/-
`potential_contribution k i` is 0 if $k \ge i$.
-/
theorem potential_contribution_zero_of_ge (k i : ℕ) (h : i ≤ k) : potential_contribution k i = 0 := by
  unfold potential_contribution
  split_ifs with h_cond <;> norm_num
  · -- Case: i < i (or whatever the first split condition was)
    linarith [A_pos k]
  · -- Case where i ≤ k is relevant
    -- Use A_strictMono to directly prove A i ≤ A k
    have h_le : A i ≤ A k := A_strictMono.monotone h
    linarith [A_pos k, A_pos i, h_le]
  · -- Case where potential_contribution is already 0
    have h_le : A i ≤ A k := A_strictMono.monotone h
    linarith [A_pos k]

/-
The partial sum of potential contributions is bounded by the total potential increase.
-/
theorem sum_potential_contribution_le_potential_increase (n : ℕ) (i : ℕ) (k : ℕ) :
  (Finset.range k).sum (fun j => potential_contribution j i) ≤ potential_increase n i := by
    by_cases hi : i ≤ k <;> simp_all +decide [ potential_increase_eq_sum ];
    · rw [ ← Finset.sum_range_add_sum_Ico _ hi ];
      simp +zetaDelta at *;
      exact fun i_2 a a_1 => potential_contribution_zero_of_ge i_2 i a;
    · exact Finset.sum_le_sum_of_subset ( Finset.range_mono hi.le )

/-
The coefficients in the sequence are bounded by the initial coefficients plus the sum of potential contributions.
-/
theorem coeffs_sequence_v2_bound_sum (n : ℕ) (h : 0 < n) (c_init : ℕ → ℕ) (k : ℕ)
  (h_sum : n = (Finset.range (v3 n + 1)).sum (fun i => c_init i * A i)) :
  ∀ i, coeffs_sequence_v2 n h c_init k i ≤ c_init i + (Finset.range k).sum (fun j => potential_contribution j i) := by
    induction' k with k ih <;> norm_num [ Finset.sum_range_succ ] at *;
    · exact fun i => le_rfl;
    · -- By definition of `coeffs_sequence_v2`, we have:
      have h_step : ∀ i, coeffs_sequence_v2 n h c_init (k + 1) i = step_transform_v2 n h (coeffs_sequence_v2 n h c_init k) k i := by
        exact fun i =>
          Nat.add_zero
            (Decidable.rec (motive := fun x => ℕ → ℕ)
              (fun h_1 => (fun h_sum => coeffs_sequence_v2 n h c_init k) h_1)
              (fun h_1 =>
                (fun h_sum =>
                    if hk : k ≤ v1 n then
                      if hc : coeffs_sequence_v2 n h c_init k k ∈ {2, 3, 4, 5} then
                        Classical.choose
                          (reduction_step_precise n h (coeffs_sequence_v2 n h c_init k) k h_sum hk
                            hc)
                      else coeffs_sequence_v2 n h c_init k
                    else
                      if hk' : k ≤ v2 n then
                        if hc : coeffs_sequence_v2 n h c_init k k ∈ {2, 3} then
                          Classical.choose
                            (reduction_step_part2_strong n h (coeffs_sequence_v2 n h c_init k) k
                              h_sum hk' hc)
                        else coeffs_sequence_v2 n h c_init k
                      else coeffs_sequence_v2 n h c_init k)
                  h_1)
              (instDecidableEqNat n
                (∑ i ∈ Finset.range (v3 n + 1), coeffs_sequence_v2 n h c_init k i * A i))
              i);
      intro i; rw [ h_step i ] ; exact le_trans ( step_transform_v2_bound n h _ _ ( coeffs_sequence_v2_sum_preserved n h c_init k ( by simpa [ Finset.sum_range_succ ] using h_sum ) ) i ) ( by linarith [ ih i ] ) ;

/-
There exists an initial configuration of coefficients satisfying all conditions, including that coefficients 1 and 3 imply the corresponding $A_i$ is a power of 2.
-/
def is_valid_initial (n : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ i < m_index n - 1, c i ∈ ({2, 3} : Set ℕ)) ∧
  (∀ i, m_index n - 1 ≤ i → i ≤ v2 n → c i ∈ ({0, 1} : Set ℕ)) ∧
  (∀ i > v2 n, c i = 0) ∧
  (∀ i, c i = 1 → ∃ k, A i = 2^k) ∧
  (∀ i, c i = 3 → ∃ k, A i = 2^k)

/-
`R_val n` is the remainder of `n` after subtracting `2 * sumA (m_index n - 1)`. It satisfies the equation `n = ... + R_val n` and is bounded by `2 * A (m_index n - 1)`.
-/
def R_val (n : ℕ) : ℕ := n - 2 * sumA (m_index n - 1)

theorem R_val_prop (n : ℕ) (h : 0 < n) :
  n = 2 * sumA (m_index n - 1) + R_val n ∧
  R_val n < 2 * A (m_index n - 1) := by
    unfold R_val;
    have := m_index_spec n;
    rcases k : m_index n with ( _ | k ) <;> simp_all +decide [ sumA ];
    rw [ Finset.sum_range_succ ] at this;
    grind

/-
Definitions for the initial coefficient construction.
-/
noncomputable def J_set (n : ℕ) : Finset ℕ := Classical.choose (exists_binary_expansion_in_A (R_val n))

theorem J_set_spec (n : ℕ) : R_val n = ∑ j ∈ J_set n, A j ∧ ∀ j ∈ J_set n, ∃ k, A j = 2^k := Classical.choose_spec (exists_binary_expansion_in_A (R_val n))

noncomputable def c_initial (n : ℕ) (i : ℕ) : ℕ := (if i < m_index n - 1 then 2 else 0) + (if i ∈ J_set n then 1 else 0)

/-
The transformation at step `k` does not change coefficients at indices `i < k`.
-/
theorem step_transform_v2_stable (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ) (i : ℕ) (hi : i < k) :
  step_transform_v2 n h c k i = c i := by
    revert hi;
    unfold step_transform_v2;
    split_ifs <;> simp +decide [ * ];
    · rename_i h₁ h₂ h₃;
      exact fun hi => Classical.choose_spec ( reduction_step_precise n h c k h₁ h₂ h₃ ) |>.2.2.1 i hi;
    · exact fun hi => Classical.choose_spec ( reduction_step_part2_strong n h c k ‹_› ‹_› ‹_› ) |>.2.2.1 i hi

/-
`c_initial` satisfies the validity conditions.
-/
theorem c_initial_valid (n : ℕ) (h : 0 < n) : is_valid_initial n (c_initial n) := by
  refine' ⟨ _, _, _, _, _ ⟩;
  · unfold c_initial; aesop;
  · unfold c_initial;
    grind;
  · unfold c_initial;
    intro i hi
    have h_J_set : ∀ j ∈ J_set n, j ≤ v2 n := by
      intro j hj
      have h_j_le : A j < 3 * A (m_index n) := by
        have h_j_le : A j ≤ R_val n := by
          have := J_set_spec n;
          exact this.1.symm ▸ Finset.single_le_sum ( fun x _ => Nat.zero_le ( A x ) ) hj;
        have := R_val_prop n h;
        linarith [ A_strictMono.monotone ( show m_index n - 1 ≤ m_index n from Nat.pred_le _ ) ];
      contrapose! h_j_le;
      have := v_spec n;
      exact le_trans this.2.2.1 ( monotone_nat_of_le_succ ( fun k => Nat.le_of_lt_succ <| by linarith [ A_strictMono <| Nat.lt_succ_self k ] ) h_j_le );
    split_ifs <;> norm_num ; linarith [ h_J_set _ ‹_› ];
    · have := v_spec n;
      contrapose! this;
      exact fun h1 h2 h3 h4 => by linarith [ A_strictMono.monotone ( show v2 n + 1 ≤ m_index n from by omega ) ] ;
    · grind;
  · intro i hi;
    unfold c_initial at hi;
    split_ifs at hi <;> norm_num at hi;
    exact J_set_spec n |>.2 i ‹_›;
  · unfold c_initial;
    intro i hi; split_ifs at hi <;> norm_num at hi;
    exact J_set_spec n |>.2 i ‹_›

/-
If $v_1 n < k \le v_2 n$, the transformation at step $k$ increases coefficients by at most 1, and only if $2 A_k = A_i$.
-/
theorem step_transform_v2_growth_part2 (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ) (i : ℕ)
  (h_sum : n = (Finset.range (v3 n + 1)).sum (fun i => c i * A i))
  (hk_gt : v1 n < k) (hk_le : k ≤ v2 n) :
  step_transform_v2 n h c k i ≤ c i + (if 2 * A k = A i then 1 else 0) := by
    unfold step_transform_v2;
    split_ifs <;> norm_num at *;
    · linarith;
    · linarith;
    · have := Classical.choose_spec ( reduction_step_part2_strong n h c k h_sum hk_le ‹_› );
      exact this.2.2.2.2.2 i;
    · have := Classical.choose_spec ( reduction_step_part2_strong n h c k h_sum hk_le ‹_› );
      grind

/-
The coefficients never exceed 5.
-/
theorem c_bound_le_5 (n : ℕ) (h : 0 < n) (k : ℕ) (i : ℕ) :
  coeffs_sequence_v2 n h (c_initial n) k i ≤ 5 := by
    -- By definition of `coeffs_sequence_v2`, we know that `c_final n h i`
    -- is bounded by `c_initial i + potential_increase n i`.
    have h_bound : ∀ i,
        coeffs_sequence_v2 n h (c_initial n) k i ≤
          c_initial n i + potential_increase n i := by
      intro i
      have h_bound' :
          coeffs_sequence_v2 n h (c_initial n) k i ≤
            c_initial n i +
              (Finset.range k).sum (fun j => potential_contribution j i) := by
        have h_bound'' :
            ∀ j,
              coeffs_sequence_v2 n h (c_initial n) j i ≤
                c_initial n i +
                  (Finset.range j).sum (fun k => potential_contribution k i) := by
          intro j
          induction' j with j ih generalizing i
          · aesop
          ·
            have h_step_transform_v2_bound :
                ∀ c : ℕ → ℕ, ∀ k : ℕ, ∀ i : ℕ,
                  step_transform_v2 n h c k i ≤
                    c i + potential_contribution k i := by
              intros c k i
              by_cases h_sum :
                  n = (Finset.range (v3 n + 1)).sum (fun i => c i * A i)
              · exact step_transform_v2_bound n h c k h_sum i
              ·
                unfold step_transform_v2
                aesop

            have h1 :=
              h_step_transform_v2_bound
                (coeffs_sequence_v2 n h (c_initial n) j) j i
            have h2 := ih i

            have hsum :
                (Finset.range (j + 1)).sum (fun k => potential_contribution k i) =
                  (Finset.range j).sum (fun k => potential_contribution k i) +
                    potential_contribution j i := by
              simp [Finset.sum_range_succ]

            -- Replace the failing linarith with a clean monotonicity chain
            calc
              coeffs_sequence_v2 n h (c_initial n) (j + 1) i
                  ≤ coeffs_sequence_v2 n h (c_initial n) j i +
                      potential_contribution j i := h1
              _ ≤ c_initial n i +
                    (Finset.range j).sum (fun k => potential_contribution k i) +
                      potential_contribution j i := by
                    exact Nat.add_le_add_right h2 _
              _ = c_initial n i +
                    (Finset.range (j + 1)).sum
                      (fun k => potential_contribution k i) := by
                    simp [hsum, add_comm, add_left_comm]
        exact h_bound'' k

      -- Add c_initial n i to both sides of the potential-sum bound
      have h_sum_raw :=
        add_le_add_left
          (sum_potential_contribution_le_potential_increase n i k)
          (c_initial n i)

      -- Fix the order mismatch by rewriting
      have h_sum :
          c_initial n i +
              (Finset.range k).sum (fun j => potential_contribution j i) ≤
            c_initial n i + potential_increase n i := by
        simpa [add_comm, add_left_comm, add_assoc] using h_sum_raw

      exact h_bound'.trans h_sum

    have := c_initial_valid n h
    simp_all +decide [is_valid_initial]

    have := h_bound i
    rcases h : c_initial n i with (_ | _ | _ | _ | c) <;>
      simp_all +arith +decide only
    ·
      linarith [potential_increase_bound n ‹_› i]
    ·
      have := potential_increase_bound n ‹_› i
      simp_all +decide
      linarith
    ·
      linarith
        [ show potential_increase n i ≤ 3 by
            exact (potential_increase_bound n ‹_› i).1 ]
    ·
      have := potential_increase_bound n ‹_› i
      obtain ⟨k, hk⟩ :=
        ‹( ∀ i < m_index n - 1, c_initial n i = 2 ∨ c_initial n i = 3 ) ∧
          ( ∀ i, m_index n ≤ i + 1 → i ≤ v2 n →
              c_initial n i = 0 ∨ c_initial n i = 1 ) ∧
          ( ∀ i, v2 n < i → c_initial n i = 0 ) ∧
          ( ∀ i, c_initial n i = 1 → ∃ k, A i = 2 ^ k ) ∧
          ∀ i, c_initial n i = 3 → ∃ k, A i = 2 ^ k ›.2.2.2.2 i h
      simp_all +arith +decide
      linarith
    · grind

/-
The coefficients at index `i` are non-decreasing as long as the step index `k` is less than or equal to `i`.
-/
theorem coeffs_sequence_v2_ge_initial (n : ℕ) (h : 0 < n) (k : ℕ) (i : ℕ) (hk : k ≤ i) :
  c_initial n i ≤ coeffs_sequence_v2 n h (c_initial n) k i := by
    induction' k with k ih generalizing i;
    · rfl;
    · specialize ih i ( by linarith );
      refine' le_trans ih _;
      -- By definition of `coeffs_sequence_v2`, we have:
      have h_step : coeffs_sequence_v2 n h (c_initial n) (k + 1) = step_transform_v2 n h (coeffs_sequence_v2 n h (c_initial n) k) k := by
        exact List.map_inj.mp rfl;
      unfold step_transform_v2 at h_step;
      split_ifs at h_step <;> simp +decide [ h_step ];
      · have := Classical.choose_spec ( reduction_step_precise n h ( coeffs_sequence_v2 n h ( c_initial n ) k ) k ‹_› ‹_› ‹_› );
        exact this.2.2.2.1 i ( by linarith );
      · have := Classical.choose_spec ( reduction_step_part2_strong n h ( coeffs_sequence_v2 n h ( c_initial n ) k ) k ‹_› ‹_› ‹_› );
        exact this.2.2.2.1 i ( by linarith )

/-
For $v_1 < k \le v_2$, the coefficient $c_k$ at the start of step $k$ is at most 3.
-/
theorem c_bound_part2 (n : ℕ) (h : 0 < n) (k : ℕ)
  (hk_gt : v1 n < k) (hk_le : k ≤ v2 n) :
  coeffs_sequence_v2 n h (c_initial n) k k ≤ 3 := by
    have h_coeff_bound : coeffs_sequence_v2 n h (c_initial n) k k ≤ c_initial n k + potential_increase n k := by
      refine' le_trans _ ( Nat.add_le_add_left ( sum_potential_contribution_le_potential_increase n k k ) _ );
      -- Apply the bound on the coefficients from `coeffs_sequence_v2_bound_sum`.
      apply coeffs_sequence_v2_bound_sum;
      have := Classical.choose_spec ( exists_binary_expansion_in_A ( R_val n ) );
      have h_sum : n = 2 * sumA (m_index n - 1) + R_val n := by
        exact R_val_prop n h |>.1;
      have h_sum : n = ∑ i ∈ Finset.range (m_index n - 1), 2 * A i + ∑ i ∈ J_set n, A i := by
        convert h_sum using 1;
        rw [ ← Finset.mul_sum _ _ _, this.1 ];
        rfl;
      have h_sum : n = ∑ i ∈ Finset.range (v2 n + 1), (if i < m_index n - 1 then 2 else 0) * A i + ∑ i ∈ J_set n, A i := by
        convert h_sum using 2;
        rw [ ← Finset.sum_subset ( Finset.range_mono ( show m_index n - 1 ≤ v2 n + 1 from _ ) ) ];
        · exact Finset.sum_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_range.mp hx ) ] ;
        · simp +contextual;
        · linarith [ Nat.sub_le ( m_index n ) 1, v_spec n ];
      have h_sum : n = ∑ i ∈ Finset.range (v3 n + 1), (if i < m_index n - 1 then 2 else 0) * A i + ∑ i ∈ J_set n, A i := by
        refine' h_sum.trans ( congr_arg₂ _ _ rfl );
        rw [ Finset.sum_subset ( Finset.range_mono ( Nat.succ_le_succ ( show v2 n ≤ v3 n from _ ) ) ) ] ; norm_num;
        · intros; linarith [ show v2 n ≥ m_index n - 1 from Nat.sub_le_of_le_add <| by linarith [ v_spec n ] ] ;
        · unfold v2 v3;
          gcongr;
          apply Nat.find_mono;
          grind;
      convert h_sum using 1;
      rw [ ← Finset.sum_sdiff ( show J_set n ⊆ Finset.range ( v3 n + 1 ) from ?_ ) ];
      · rw [ Finset.sum_congr rfl fun x hx => by rw [ c_initial ] ];
        rw [ Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Finset.mem_sdiff.mp hx |>.2 ) ] ] ; norm_num [ Finset.sum_add_distrib, add_mul ];
        rw [ ← Finset.sum_sdiff ( show J_set n ⊆ Finset.range ( v3 n + 1 ) from ?_ ) ];
        · rw [ add_assoc, ← Finset.sum_add_distrib ];
          refine' congr rfl ( Finset.sum_congr rfl fun x hx => _ );
          unfold c_initial; split_ifs <;> ring;
        · intro i hi;
          have := J_set_spec n;
          have h_i_le_v3 : A i ≤ 2 * A (m_index n - 1) := by
            have h_i_le_v3 : A i ≤ R_val n := by
              exact this.1.symm ▸ Finset.single_le_sum ( fun x _ => Nat.zero_le ( A x ) ) hi;
            exact h_i_le_v3.trans ( R_val_prop n h |>.2.le );
          have h_i_le_v3 : A i < A (v3 n + 1) := by
            have := v_spec n;
            linarith [ A_strictMono.monotone ( show m_index n - 1 ≤ m_index n from Nat.pred_le _ ) ];
          exact Finset.mem_range.mpr ( Nat.lt_of_not_ge fun hi' => h_i_le_v3.not_ge <| A_strictMono.monotone hi' );
      · intro i hi;
        have := J_set_spec n;
        have h_i_le_v3 : A i ≤ 2 * A (m_index n - 1) := by
          have h_i_le_v3 : A i ≤ R_val n := by
            exact this.1.symm ▸ Finset.single_le_sum ( fun x _ => Nat.zero_le ( A x ) ) hi;
          exact h_i_le_v3.trans ( R_val_prop n h |>.2.le );
        have h_i_le_v3 : A i < A (v3 n + 1) := by
          have := v_spec n;
          linarith [ A_strictMono.monotone ( show m_index n - 1 ≤ m_index n from Nat.pred_le _ ) ];
        exact Finset.mem_range.mpr ( Nat.lt_of_not_ge fun hi' => h_i_le_v3.not_ge <| A_strictMono.monotone hi' );
    refine le_trans h_coeff_bound <| ?_;
    unfold c_initial;
    split_ifs <;> norm_num;
    · unfold v1 at * ; omega;
    · unfold v1 at hk_gt; omega;
    · have := J_set_spec n;
      -- Since $k \in J_set n$, we have $A k = 2^j$ for some $j$.
      obtain ⟨j, hj⟩ : ∃ j, A k = 2^j := by
        exact this.2 k ‹_›;
      -- Since $A k = 2^j$, the only possible contributions to the potential increase are from $2 * A k = A (k+1)$ and $3 * A k = A (k+1)$.
      have h_contribution : potential_increase n k ≤ 2 := by
        exact le_trans ( potential_increase_bound n h k |>.2 ( by aesop ) ) ( by norm_num );
      linarith;
    · exact potential_increase_bound n h k |>.1

/-
The number of indices $k \le v_2$ such that $2 A_k = A_i$ is at most 1.
-/
theorem sum_indicator_le_one (n : ℕ) (i : ℕ) :
  (Finset.range (v2 n + 1)).sum (fun k => if 2 * A k = A i then 1 else 0) ≤ 1 := by
    have := @unique_half i;
    simp +zetaDelta at *;
    exact Finset.card_le_one.mpr fun x hx y hy => this ( Finset.mem_filter.mp hx |>.2 ) ( Finset.mem_filter.mp hy |>.2 )

/-
For $i > v_2$, the coefficient at step $k$ is bounded by the sum of potential increases from steps $j \in (v_1, v_2]$.
-/
theorem coeffs_bound_large (n : ℕ) (h : 0 < n) (k : ℕ) (i : ℕ) (hi : v2 n < i) :
  coeffs_sequence_v2 n h (c_initial n) k i ≤ (Finset.range k).sum (fun j => if v1 n < j ∧ j ≤ v2 n ∧ 2 * A j = A i then 1 else 0) := by
    induction' k with k ih generalizing i <;> simp_all +decide;
    · exact c_initial_valid n h |>.2.2.1 i hi;
    · -- Apply the step_transform_v2_growth_part2 theorem to bound the coefficient.
      have h_step_bound : coeffs_sequence_v2 n h (c_initial n) (k + 1) i ≤ coeffs_sequence_v2 n h (c_initial n) k i + (if v1 n < k ∧ k ≤ v2 n ∧ 2 * A k = A i then 1 else 0) := by
        rw [ show coeffs_sequence_v2 n h ( c_initial n ) ( k + 1 ) = step_transform_v2 n h ( coeffs_sequence_v2 n h ( c_initial n ) k ) k from rfl ];
        unfold step_transform_v2;
        split_ifs <;> norm_num;
        · linarith;
        · have := Classical.choose_spec ( reduction_step_precise n h ( coeffs_sequence_v2 n h ( c_initial n ) k ) k ‹_› ‹_› ‹_› );
          grind;
        · have := Classical.choose_spec ( reduction_step_part2_strong n h ( coeffs_sequence_v2 n h ( c_initial n ) k ) k ( by linarith ) ( by linarith ) ( by tauto ) );
          exact this.2.2.2.2.2 i;
        · have := Classical.choose_spec ( reduction_step_part2_strong n h ( coeffs_sequence_v2 n h ( c_initial n ) k ) k ( by linarith ) ( by linarith ) ( by tauto ) );
          grind;
      split_ifs at h_step_bound <;> simp_all +decide [ Finset.filter ];
      · linarith [ ih i hi ];
      · exact le_trans h_step_bound ( ih i hi )

/-
For $i < v_1$, the coefficient at the start of step $i$ is at least 2.
-/
theorem c_at_step_ge_2 (n : ℕ) (h : 0 < n) (i : ℕ) (hi : i < v1 n) :
  2 ≤ coeffs_sequence_v2 n h (c_initial n) i i := by
    refine' le_trans _ ( coeffs_sequence_v2_ge_initial _ _ _ _ _ );
    · unfold c_initial;
      unfold v1 at hi; aesop;
    · bound

/-
If the conditions for reduction are met, the coefficient at step $k$ becomes 0.
-/
theorem step_transform_v2_sets_zero (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ)
  (h_sum : n = (Finset.range (v3 n + 1)).sum (fun i => c i * A i))
  (hk : k ≤ v1 n)
  (hc : c k ∈ ({2, 3, 4, 5} : Set ℕ)) :
  step_transform_v2 n h c k k = 0 := by
    unfold step_transform_v2;
    split_ifs;
    have := Classical.choose_spec ( reduction_step_precise n h c k h_sum hk hc );
    exact this.2.1

/-
For $i < v_1$, the coefficient at index $i$ becomes 0 after step $i$.
-/
theorem step_i_sets_zero (n : ℕ) (h : 0 < n) (i : ℕ) (hi : i < v1 n) :
  coeffs_sequence_v2 n h (c_initial n) (i + 1) i = 0 := by
    -- By `c_at_step_ge_2`, $c_i \ge 2$.
    have h_ci_ge_2 : 2 ≤ coeffs_sequence_v2 n h (c_initial n) i i := by
      exact c_at_step_ge_2 n h i hi;
    -- By `c_bound_le_5_general`, $c_i \le 5$.
    have h_ci_le_5 : coeffs_sequence_v2 n h (c_initial n) i i ≤ 5 := by
      apply c_bound_le_5;
    convert step_transform_v2_sets_zero n h _ _ _ _ _ using 1;
    · convert coeffs_sequence_v2_sum_preserved n h ( c_initial n ) i _;
      have h_sum : n = 2 * sumA (m_index n - 1) + ∑ j ∈ J_set n, A j := by
        rw [ ← J_set_spec n |>.1 ];
        exact R_val_prop n h |>.1;
      unfold c_initial; simp +decide [Finset.sum_add_distrib, add_mul] ;
      convert h_sum using 2;
      · rw [ Finset.sum_ite ];
        norm_num [ ← Finset.mul_sum _ _ _, sumA ];
        rcongr x ; simp +arith +decide;
        exact fun hx => le_trans ( Nat.le_of_lt hx ) ( Nat.sub_le_of_le_add <| by linarith [ show v3 n ≥ m_index n from Nat.le_sub_one_of_lt <| by
                                                                                              refine' Nat.lt_of_not_ge fun h => _;
                                                                                              have := Nat.find_spec ( A_unbounded ( 6 * A ( m_index n ) ) );
                                                                                              linarith [ A_strictMono.monotone h, A_pos ( m_index n ) ] ] );
      · rw [ Finset.inter_eq_right.mpr ];
        intro j hj; have := J_set_spec n; norm_num at *;
        have h_j_lt_v3 : A j < 6 * A (m_index n) := by
          have h_j_lt_v3 : A j ≤ R_val n := by
            exact this.1.symm ▸ Finset.single_le_sum ( fun x _ => Nat.zero_le ( A x ) ) hj;
          have h_j_lt_v3 : R_val n < 2 * A (m_index n - 1) := by
            exact R_val_prop n h |>.2;
          linarith [ A_strictMono.monotone ( Nat.sub_le ( m_index n ) 1 ) ];
        contrapose! h_j_lt_v3;
        have h_j_ge_v3 : A j ≥ A (v3 n + 1) := by
          exact monotone_nat_of_le_succ ( fun k => Nat.le_of_lt ( A_strictMono ( Nat.lt_succ_self k ) ) ) h_j_lt_v3;
        exact le_trans ( by linarith [ v_spec n ] ) h_j_ge_v3;
    · exact Nat.le_of_succ_le hi;
    · interval_cases coeffs_sequence_v2 n h ( c_initial n ) i i <;> simp +decide

/-
The initial coefficients `c_initial` sum to `n`.
-/
theorem c_initial_sum (n : ℕ) (h : 0 < n) :
  n = (Finset.range (v3 n + 1)).sum (fun i => c_initial n i * A i) := by
    have := R_val_prop n h;
    -- Since $A$ is strictly increasing and $A (v_3 n) < 6 A (m_index n) \leq A (v_3 n + 1)$, we have $j \leq v_3 n$.
    have h_j_le_v3 : ∀ j ∈ J_set n, j ≤ v3 n := by
      intros j hj
      have h_A_j_le_6A : A j < 6 * A (m_index n) := by
        have h_A_j_le_6A : A j ≤ R_val n := by
          have := J_set_spec n;
          exact this.1.symm ▸ Finset.single_le_sum ( fun x _ => Nat.zero_le ( A x ) ) hj;
        linarith [ A_pos ( m_index n - 1 ), A_pos ( m_index n ), show A ( m_index n - 1 ) ≤ A ( m_index n ) from A_strictMono.monotone ( Nat.pred_le _ ) ];
      have h_A_j_le_6A : A j < A (v3 n + 1) := by
        exact h_A_j_le_6A.trans_le ( v_spec n |>.2.2.2.2 );
      exact le_of_not_gt fun h => h_A_j_le_6A.not_ge <| A_strictMono.monotone h;
    -- The sum of the initial coefficients can be split into two parts: one from the first part and one from the second part.
    have h_split_sum : ∑ i ∈ Finset.range (v3 n + 1), (if i < m_index n - 1 then 2 else 0) * A i = 2 * sumA (m_index n - 1) ∧ ∑ i ∈ Finset.range (v3 n + 1), (if i ∈ J_set n then 1 else 0) * A i = ∑ j ∈ J_set n, A j := by
      constructor;
      · norm_num [ Finset.sum_ite, Finset.mul_sum _ _ _, sumA ];
        refine' Finset.sum_subset _ _ <;> simp +contextual [ Finset.subset_iff ];
        -- Since $x < m_index n - 1$ and $v3 n + 1 \leq x$, this leads to a contradiction because $v3 n$ is defined as the largest index where $A i$ is less than $6 * A (m_index n)$.
        intros x hx_lt hx_ge
        have h_contra : v3 n < m_index n - 1 := by
          linarith;
        have := v_spec n;
        linarith [ A_strictMono.monotone ( show v3 n + 1 ≤ m_index n from by omega ) ];
      · simp +decide;
        rw [ Finset.inter_eq_right.mpr fun x hx => Finset.mem_range.mpr ( Nat.lt_succ_of_le ( h_j_le_v3 x hx ) ) ];
    have := J_set_spec n;
    unfold c_initial; simp +decide [Finset.sum_add_distrib, add_mul]
    rw [ Finset.inter_eq_right.mpr ( Finset.subset_iff.mpr fun x hx => Finset.mem_range.mpr ( Nat.lt_succ_of_le ( h_j_le_v3 x hx ) ) ) ] ; norm_num [ Finset.sum_ite ] at * ; linarith

/-
For $i < v_1$, the coefficient at index $i$ is 0 for all steps $k > i$.
-/
theorem coeffs_sequence_v2_eq_zero_of_gt_i (n : ℕ) (h : 0 < n) (i : ℕ) (hi : i < v1 n) (k : ℕ) (hk : i < k) :
  coeffs_sequence_v2 n h (c_initial n) k i = 0 := by
    induction' hk with k hk ih;
    · exact step_i_sets_zero n h i hi;
    · -- By the properties of the transformation, if $i < k$, then `step_transform_v2` preserves the value of the coefficient at $i$.
      have h_step_transform : step_transform_v2 n h (coeffs_sequence_v2 n h (c_initial n) k) k i = coeffs_sequence_v2 n h (c_initial n) k i := by
        apply_rules [ step_transform_v2_stable ];
      aesop

/-
$v_1 n < v_2 n$.
-/
theorem v1_lt_v2 (n : ℕ) (h : 0 < n) : v1 n < v2 n := by
  -- Since $A$ is strictly increasing, $A(m\_index\ n) < 3 A(m\_index\ n)$.
  have h_A_mono : A (m_index n) < A (v2 n + 1) := by
    have := v_spec n;
    linarith [ A_pos ( m_index n ) ];
  -- Since $A$ is strictly monotonic, $m\_index\ n < v_2 n + 1$.
  have h_m_le_v2 : m_index n < v2 n + 1 := by
    exact A_strictMono.lt_iff_lt.mp h_A_mono;
  -- Since $m\_index\ n < v2 n + 1$ and $m\_index\ n$ is a natural number, it follows that $m\_index\ n \leq v2 n$.
  have h_m_le_v2_nat : m_index n ≤ v2 n := by
    linarith;
  exact Nat.sub_lt ( Nat.pos_of_ne_zero ( by
    rintro h;
    have := m_index_spec n; simp_all +decide ;
    exact this.not_ge ( Nat.zero_le _ ) ) ) zero_lt_one |> lt_of_lt_of_le <| h_m_le_v2_nat

/-
For $v_1 < i \le v_2$, the coefficient at index $i$ becomes $\le 1$ after step $i$.
-/
theorem step_i_le_one (n : ℕ) (h : 0 < n) (i : ℕ) (hi_gt : v1 n < i) (hi_le : i ≤ v2 n) :
  coeffs_sequence_v2 n h (c_initial n) (i + 1) i ≤ 1 := by
    have := @reduction_step_part2_strong n h ( coeffs_sequence_v2 n h ( c_initial n ) i ) i;
    by_cases hi : coeffs_sequence_v2 n h ( c_initial n ) i i ∈ ({2, 3} : Set ℕ);
    · convert this ( coeffs_sequence_v2_sum_preserved n h ( c_initial n ) i _ ) hi_le hi |> Classical.choose_spec |> And.right |> And.left |> fun x => x.le.trans ( Nat.sub_le_sub_right ( show coeffs_sequence_v2 n h ( c_initial n ) i i ≤ 3 by rcases hi with ( hi | hi ) <;> norm_num at hi <;> linarith ) _ ) using 1;
      swap;
      exact c_initial_sum n h;
      rw [ show coeffs_sequence_v2 n h ( c_initial n ) ( i + 1 ) = step_transform_v2 n h ( coeffs_sequence_v2 n h ( c_initial n ) i ) i from rfl ];
      unfold step_transform_v2; simp +decide [hi_le, hi] ;
      split_ifs <;> norm_num at *;
      · grind;
      · grind;
      · rename_i h;
        exact False.elim <| h <| coeffs_sequence_v2_sum_preserved n ‹_› ( c_initial n ) i <| c_initial_sum n ‹_›;
    · -- Since the coefficient at step i is not in {2, 3}, it must be in {0, 1}.
      have h_coeff : coeffs_sequence_v2 n h (c_initial n) i i ∈ ({0, 1} : Set ℕ) := by
        have h_coeff : coeffs_sequence_v2 n h (c_initial n) i i ≤ 3 := by
          exact c_bound_part2 n h i hi_gt hi_le;
        interval_cases coeffs_sequence_v2 n h ( c_initial n ) i i <;> trivial;
      rw [ show coeffs_sequence_v2 n h ( c_initial n ) ( i + 1 ) = step_transform_v2 n h ( coeffs_sequence_v2 n h ( c_initial n ) i ) i from rfl ];
      unfold step_transform_v2;
      grind +ring

/-
The coefficient at index $v_1$ becomes $\le 1$ after step $v_1$.
-/
theorem step_v1_le_one (n : ℕ) (h : 0 < n) :
  coeffs_sequence_v2 n h (c_initial n) (v1 n + 1) (v1 n) ≤ 1 := by
    have h_step_v1 : coeffs_sequence_v2 n h (c_initial n) (v1 n + 1) (v1 n) = step_transform_v2 n h (coeffs_sequence_v2 n h (c_initial n) (v1 n)) (v1 n) (v1 n) := by
      rfl;
    unfold step_transform_v2 at h_step_v1;
    split_ifs at h_step_v1 <;> norm_num at *;
    · have := Classical.choose_spec ( reduction_step_precise n h ( coeffs_sequence_v2 n h ( c_initial n ) ( v1 n ) ) ( v1 n ) ( by linarith ) ( by linarith ) ‹_› );
      linarith;
    · have h_step_v1 : coeffs_sequence_v2 n h (c_initial n) (v1 n) (v1 n) ≤ 5 := by
        exact c_bound_le_5 n h (v1 n) (v1 n);
      grind;
    · exact False.elim <| ‹¬n = ∑ i ∈ Finset.range ( v3 n + 1 ), coeffs_sequence_v2 n h ( c_initial n ) ( v1 n ) i * A i› <| coeffs_sequence_v2_sum_preserved n h ( c_initial n ) ( v1 n ) <| c_initial_sum n h

/-
If $k > i$, the transformation at step $k$ does not change the coefficient at index $i$.
-/
theorem step_transform_v2_stable_of_gt (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ) (i : ℕ) (hk : k > i) :
  step_transform_v2 n h c k i = c i := by
    exact step_transform_v2_stable n h c k i hk

/-
The coefficient at index i stabilizes after step i.
-/
theorem coeffs_sequence_v2_stable_after_step (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (i : ℕ) (k : ℕ) (hk : i < k) :
  coeffs_sequence_v2 n h c k i = coeffs_sequence_v2 n h c (i + 1) i := by
    induction' hk with k hk ih;
    · rfl;
    · -- By definition of `coeffs_sequence_v2`, we have:
      have h_step : coeffs_sequence_v2 n h c (k + 1) i = step_transform_v2 n h (coeffs_sequence_v2 n h c k) k i := by
        exact
          Nat.add_zero
            (Decidable.rec (motive := fun x => ℕ → ℕ)
              (fun h_1 => (fun h_sum => coeffs_sequence_v2 n h c k) h_1)
              (fun h_1 =>
                (fun h_sum =>
                    if hk : k ≤ v1 n then
                      if hc : coeffs_sequence_v2 n h c k k ∈ {2, 3, 4, 5} then
                        Classical.choose
                          (reduction_step_precise n h (coeffs_sequence_v2 n h c k) k h_sum hk hc)
                      else coeffs_sequence_v2 n h c k
                    else
                      if hk' : k ≤ v2 n then
                        if hc : coeffs_sequence_v2 n h c k k ∈ {2, 3} then
                          Classical.choose
                            (reduction_step_part2_strong n h (coeffs_sequence_v2 n h c k) k h_sum
                              hk' hc)
                        else coeffs_sequence_v2 n h c k
                      else coeffs_sequence_v2 n h c k)
                  h_1)
              (instDecidableEqNat n
                (∑ i ∈ Finset.range (v3 n + 1), coeffs_sequence_v2 n h c k i * A i))
              i);
      rw [ h_step, step_transform_v2_stable_of_gt ] <;> aesop

/-
The coefficients of the solution `c_sol` are at most 1.
-/
noncomputable def c_sol (n : ℕ) (h : 0 < n) : ℕ → ℕ := coeffs_sequence_v2 n h (c_initial n) (v2 n + 1)

theorem c_sol_le_one (n : ℕ) (h : 0 < n) (i : ℕ) : c_sol n h i ≤ 1 := by
  convert coeffs_bound_large n h ( v2 n + 1 ) i using 1;
  by_cases hi : v2 n < i <;> simp +decide [ hi ];
  · have h_sum_indicator : (Finset.range (v2 n + 1)).sum (fun j => if v1 n < j ∧ j ≤ v2 n ∧ 2 * A j = A i then 1 else 0) ≤ 1 := by
      have h_sum_indicator : (Finset.range (v2 n + 1)).sum (fun j => if 2 * A j = A i then 1 else 0) ≤ 1 := by
        convert sum_indicator_le_one n i using 1;
      exact le_trans ( Finset.sum_le_sum fun _ _ => by aesop ) h_sum_indicator;
    convert iff_of_true ?_ ?_ using 1;
    · exact le_trans ( coeffs_bound_large n h ( v2 n + 1 ) i hi ) ( h_sum_indicator.trans' ( Finset.sum_le_sum_of_subset ( Finset.range_mono ( by linarith ) ) ) );
    · convert coeffs_bound_large n h ( v2 n + 1 ) i hi using 1;
      rw [ Finset.card_filter ];
  · by_cases hi' : i < v1 n <;> simp +decide [c_sol];
    · rw [ coeffs_sequence_v2_eq_zero_of_gt_i ] <;> norm_num ; linarith;
      linarith;
    ·
      -- Since $i \leq v2 n$, we can apply the bound from `step_i_le_one`.
      have h_step_i_le_one : coeffs_sequence_v2 n h (c_initial n) (i + 1) i ≤ 1 := by
        by_cases hi'' : i = v1 n;
        · -- Substitute hi'' into the goal and apply the step_i_le_one lemma.
          rw [hi'']
          apply step_v1_le_one;
        · exact step_i_le_one n h i ( lt_of_le_of_ne ( le_of_not_gt hi' ) ( Ne.symm hi'' ) ) ( le_of_not_gt hi );
      rw [ coeffs_sequence_v2_stable_after_step ];
      · exact h_step_i_le_one;
      · linarith

/-
The coefficients of the solution `c_sol` are 0 for indices `i < v1 n`.
-/
theorem c_sol_eq_zero_of_lt_v1 (n : ℕ) (h : 0 < n) (i : ℕ) (hi : i < v1 n) : c_sol n h i = 0 := by
  -- Apply the lemma that states the coefficient at index i is 0 for any k > i.
  have := coeffs_sequence_v2_eq_zero_of_gt_i n h i hi (v2 n + 1) (by
  -- Since $v1 n < v2 n$, we have $i < v2 n + 1$.
  have hv1_lt_v2 : v1 n < v2 n := by
    exact v1_lt_v2 n h
  linarith);
  aesop

/-
A coefficient function `c` has support bounded by `B` if `c i = 0` for all `i` such that `A i \ge B`.
-/
def support_bounded (c : ℕ → ℕ) (B : ℕ) : Prop := ∀ i, B ≤ A i → c i = 0

/-
The initial coefficient function `c_initial` has support bounded by `2 * A (v1 n)`.
-/
theorem c_initial_support_bounded (n : ℕ) (h : 0 < n) :
  support_bounded (c_initial n) (2 * A (v1 n)) := by
    intro i hi;
    unfold c_initial;
    split_ifs <;> norm_num at *;
    · -- Since $i < v1 n$, we have $A i < A (v1 n)$ by the monotonicity of $A$.
      have h_ai_lt_av1 : A i < A (v1 n) := by
        exact A_strictMono ( by unfold v1; omega );
      linarith;
    · -- Since $i < v1 n$, we have $A i < A (v1 n)$ by the strict monotonicity of $A$.
      have h_ai_lt_av1 : A i < A (v1 n) := by
        exact A_strictMono ( by unfold v1; omega );
      linarith;
    · have := J_set_spec n |>.1;
      contrapose! hi;
      exact lt_of_le_of_lt ( Finset.single_le_sum ( fun x _ => Nat.zero_le ( A x ) ) ‹_› ) ( this ▸ R_val_prop n h |>.2 )

/-
If the coefficients `c` have support bounded by `B`, then after a transformation step at `k` (where `k \le v1`), the new coefficients have support bounded by `max B (3 * A k + 1)`.
-/
theorem step_transform_support_bounded_part1 (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ) (B : ℕ)
  (hc : support_bounded c B) (hk : k ≤ v1 n) :
  support_bounded (step_transform_v2 n h c k) (max B (3 * A k + 1)) := by
    intro i hi;
    unfold step_transform_v2;
    split_ifs <;> norm_num at *;
    · have := Classical.choose_spec ( reduction_step_precise n h c k ‹_› hk ‹_› );
      by_cases hi' : i = k <;> simp +decide [hi'] at hi ⊢;
      · grind;
      · -- Since $i \neq k$ and $i \geq k$, the potential_contribution $k i$ is zero.
        have h_potential_zero : potential_contribution k i = 0 := by
          unfold potential_contribution; simp +decide ;
          constructor <;> linarith [ A_pos k, A_pos i ];
        linarith [ this.2.2.2.2.2 i, hc i hi.1 ];
    · exact hc i hi.1;
    · exact hc i hi.1

/-
If the coefficients `c` have support bounded by `B`, then after a transformation step at `k` (where `v1 < k \le v2`), the new coefficients have support bounded by `max B (2 * A k + 1)` (if `c k > 0`).
-/
theorem step_transform_support_bounded_part2 (n : ℕ) (h : 0 < n) (c : ℕ → ℕ) (k : ℕ) (B : ℕ)
  (hc : support_bounded c B) (hk_gt : v1 n < k) (hk_le : k ≤ v2 n) :
  support_bounded (step_transform_v2 n h c k) (if c k = 0 then B else max B (2 * A k + 1)) := by
    rcases eq_or_ne ( c k ) 0 with hc0 | hc0 <;> simp +decide [ * ];
    · unfold step_transform_v2;
      grind;
    · -- If $c_k > 0$, then $A_k < B$ (since $c$ is bounded by $B$). The transformation reduces $c_k$ and increases $c_l$ where $A_l = 2 A_k$.
      have h_transform : ∀ i, A i ≥ max B (2 * A k + 1) → step_transform_v2 n h c k i = c i := by
        unfold step_transform_v2;
        split_ifs <;> norm_num at *;
        · grind;
        · have := Classical.choose_spec ( reduction_step_part2_strong n h c k ‹_› hk_le ‹_› );
          grind +ring;
      intro i hi; specialize h_transform i hi; aesop;

/-
The coefficients after the first phase of transformation (up to step `v1`) have support bounded by `3 * A (v1 n) + 1`.
-/
theorem coeffs_sequence_support_bounded_part1 (n : ℕ) (h : 0 < n) :
  support_bounded (coeffs_sequence_v2 n h (c_initial n) (v1 n + 1)) (3 * A (v1 n) + 1) := by
    -- We prove by induction on $k$ that for $k \le v1 + 1$, `support_bounded (coeffs_sequence_v2 ... k) (3 * A (v1 n) + 1)`.
    have h_ind : ∀ k ≤ v1 n + 1, support_bounded (coeffs_sequence_v2 n h (c_initial n) k) (max (2 * A (v1 n)) (3 * A (v1 n) + 1)) := by
      intro k hk_le
      induction' k with k ih;
      · exact fun i hi => by have := c_initial_support_bounded n h; exact this i ( le_trans ( by norm_num ) hi ) |> fun h => by aesop;
      · have := ih ( Nat.le_of_succ_le hk_le );
        convert step_transform_support_bounded_part1 n h _ k _ this ( Nat.le_of_succ_le_succ hk_le ) using 1;
        simp +zetaDelta at *;
        cases max_cases ( A ( v1 n ) ) ( A k ) <;> cases max_cases ( 2 * A ( v1 n ) ) ( 3 * A ( v1 n ) + 1 ) <;> cases max_cases ( 2 * A ( v1 n ) ) ( 3 * max ( A ( v1 n ) ) ( A k ) + 1 ) <;> linarith [ A_strictMono.monotone hk_le ];
    exact fun i hi => h_ind _ le_rfl _ ( le_trans ( max_le ( by linarith ) ( by linarith ) ) hi )

/-
The solution coefficients `c_sol` have support bounded by `6 * A (v1 n + 1)`.
-/
theorem c_sol_support_bounded (n : ℕ) (h : 0 < n) :
  support_bounded (c_sol n h) (6 * A (v1 n + 1)) := by
    -- We prove by induction that for $k$ from $v1+1$ to $v2+1$, the support is bounded by $6 A_{v1+1}$.
    have h_induction : ∀ k, v1 n + 1 ≤ k → k ≤ v2 n + 1 → support_bounded (coeffs_sequence_v2 n h (c_initial n) k) (6 * A (v1 n + 1)) := by
      intro k hk₁ hk₂;
      induction' hk₁ with k hk₁ ih;
      · have := coeffs_sequence_support_bounded_part1 n h;
        refine' fun i hi => this i ( by linarith [ show 3 * A ( v1 n ) + 1 ≤ 6 * A ( v1 n + 1 ) from by linarith [ show A ( v1 n ) ≤ A ( v1 n + 1 ) from Nat.le_of_lt <| A_strictMono <| Nat.lt_succ_self _, A_pos ( v1 n ), A_pos ( v1 n + 1 ) ] ] );
      · -- Apply the step_transform_support_bounded_part2 lemma to conclude the proof.
        have := step_transform_support_bounded_part2 n h (coeffs_sequence_v2 n h (c_initial n) k) k (6 * A (v1 n + 1)) (ih (Nat.le_of_succ_le hk₂)) (by
        exact Nat.lt_of_succ_le hk₁) (by
        linarith);
        convert this using 1;
        split_ifs <;> simp_all +decide;
        have := v_spec n;
        linarith [ show A k ≤ A ( v2 n ) from by exact monotone_nat_of_le_succ ( fun n => Nat.le_of_lt <| A_strictMono <| Nat.lt_succ_self n ) hk₂, show A ( v1 n + 1 ) ≥ A ( m_index n ) from by exact monotone_nat_of_le_succ ( fun n => Nat.le_of_lt <| A_strictMono <| Nat.lt_succ_self n ) <| by omega ];
    exact h_induction _ ( Nat.succ_le_of_lt ( by linarith [ v1_lt_v2 n h ] ) ) ( by linarith [ v1_lt_v2 n h ] )

/-
If the coefficient at `v1` is 1 after the first phase, then all coefficients with non-zero values correspond to `A i < 3 * A (v1 n)`.
-/
theorem part1_bound_if_v1_not_reduced (n : ℕ) (h : 0 < n) :
  coeffs_sequence_v2 n h (c_initial n) (v1 n + 1) (v1 n) = 1 →
  ∀ i, coeffs_sequence_v2 n h (c_initial n) (v1 n + 1) i > 0 → A i < 3 * A (v1 n) := by
    intros h1 i hi
    have h_support : ∀ j, coeffs_sequence_v2 n h (c_initial n) (v1 n) j > 0 → A j < 3 * A (v1 n) := by
      have h_support : ∀ k ≤ v1 n, ∀ j, coeffs_sequence_v2 n h (c_initial n) k j > 0 → A j < 3 * A (v1 n) := by
        intros k hk j hj_pos
        induction' k with k ih generalizing j;
        · have h_support : ∀ j, c_initial n j > 0 → A j < 2 * A (v1 n) := by
            intros j hj_pos
            have h_support : A j < 2 * A (v1 n) := by
              have := c_initial_support_bounded n h;
              exact lt_of_not_ge fun h => hj_pos.ne' <| this j h
            exact h_support;
          exact lt_of_lt_of_le ( h_support j hj_pos ) ( by linarith [ A_pos ( v1 n ) ] );
        · by_cases hj : j = k <;> simp_all +decide [ coeffs_sequence_v2 ];
          · exact lt_of_lt_of_le ( A_strictMono ( Nat.lt_of_succ_le hk ) ) ( by linarith [ A_pos ( v1 n ) ] );
          · rw [ step_transform_v2 ] at hj_pos;
            split_ifs at hj_pos;
            any_goals linarith [ ih ( by linarith ) j hj_pos ];
            · have := Classical.choose_spec ( reduction_step_precise n h ( coeffs_sequence_v2 n h ( c_initial n ) k ) k ‹_› ‹_› ‹_› );
              contrapose! hj_pos;
              have := this.2.2.2.2.2 j; simp +decide [ potential_contribution ] at this;
              split_ifs at this <;> norm_num at this;
              · linarith [ A_pos k ];
              · linarith [ ih ( by linarith ) j ( by linarith [ A_strictMono ( show k < v1 n from by linarith ) ] ) ];
              · linarith [ ih ( by linarith ) k ( by
                  grind ), A_strictMono ( by linarith : k < v1 n ) ];
              · exact le_trans this ( Nat.le_of_not_lt fun h => by linarith [ ih ( by linarith ) j h ] );
            · grind;
      exact h_support _ le_rfl;
    by_cases hi' : i = v1 n <;> simp_all +decide [ coeffs_sequence_v2 ];
    · linarith [ A_pos ( v1 n ) ];
    · contrapose! hi;
      unfold step_transform_v2;
      split_ifs <;> norm_num at *;
      · unfold step_transform_v2 at h1; norm_num at h1;
        split_ifs at h1 <;> norm_num at *;
        · have := Classical.choose_spec ( reduction_step_precise n h ( coeffs_sequence_v2 n h ( c_initial n ) ( v1 n ) ) ( v1 n ) ‹_› ‹_› ‹_› ) ; norm_num at this;
          linarith;
        · grind;
      · grind;
      · exact Classical.not_not.1 fun hi'' => hi.not_gt <| h_support i <| Nat.pos_of_ne_zero hi''

/-
If the coefficient at `v1` is 1 after the first phase, then all coefficients with non-zero values correspond to `A i < 3 * A (v1 n)`.
-/
theorem part1_bound_if_v1_not_reduced_v2 (n : ℕ) (h : 0 < n) :
  coeffs_sequence_v2 n h (c_initial n) (v1 n + 1) (v1 n) = 1 →
  ∀ i, coeffs_sequence_v2 n h (c_initial n) (v1 n + 1) i > 0 → A i < 3 * A (v1 n) := by
    -- Apply the part1_bound_if_v1_not_reduced lemma.
    apply part1_bound_if_v1_not_reduced

/-
The invariant for part 2: for any index `i \le v2`, if `A i \ge 3 * A (v1 n)`, then the coefficient `c i` is at most 1.
-/
def part2_invariant (n : ℕ) (c : ℕ → ℕ) : Prop :=
  ∀ i, i ≤ v2 n → 3 * A (v1 n) ≤ A i → c i ≤ 1

/-
The coefficients at step `k` (where `k \ge v1 + 1`) are bounded by the coefficients at step `v1 + 1` plus the number of indices `j` in `(v1, k)` such that `2 * A j = A i`.
-/
theorem coeffs_sequence_v2_growth_bound (n : ℕ) (h : 0 < n) (k : ℕ) (i : ℕ) (hk : v1 n + 1 ≤ k) :
  coeffs_sequence_v2 n h (c_initial n) k i ≤
  coeffs_sequence_v2 n h (c_initial n) (v1 n + 1) i +
  Finset.card ((Finset.range k).filter (fun j => v1 n < j ∧ 2 * A j = A i)) := by
    induction' hk with k hk ih generalizing i;
    · exact Nat.le_add_right _ _;
    · have h_step_transform : step_transform_v2 n h (coeffs_sequence_v2 n h (c_initial n) k) k i ≤ coeffs_sequence_v2 n h (c_initial n) k i + (if v1 n < k ∧ 2 * A k = A i then 1 else 0) := by
        by_cases hk_le : k ≤ v2 n;
        · convert step_transform_v2_growth_part2 n h ( coeffs_sequence_v2 n h ( c_initial n ) k ) k i _ using 1;
          · grind;
          · exact coeffs_sequence_v2_sum_preserved n h ( c_initial n ) k ( c_initial_sum n h );
        · unfold step_transform_v2;
          split_ifs <;> norm_num;
          · linarith;
          · linarith [ Nat.succ_le_iff.mp hk ];
      refine le_trans ?_ ( h_step_transform.trans ?_ );
      · exact Nat.le_refl (coeffs_sequence_v2 n h (c_initial n) k.succ i);
      · split_ifs <;> simp_all +decide [ Finset.filter ];
        exact Nat.lt_succ_of_le (ih i)

/-
If the coefficients at step `v1 + 1` satisfy the condition that non-zero values imply `A i < 3 * A (v1 n)`, then the invariant `part2_invariant` holds for all steps `k` in part 2.
-/
theorem part2_invariant_holds (n : ℕ) (h : 0 < n) (k : ℕ)
  (hk_gt : v1 n < k) (hk_le : k ≤ v2 n + 1)
  (h_init : ∀ i, coeffs_sequence_v2 n h (c_initial n) (v1 n + 1) i > 0 → A i < 3 * A (v1 n)) :
  part2_invariant n (coeffs_sequence_v2 n h (c_initial n) k) := by
    intro i hi;
    have := coeffs_sequence_v2_growth_bound n h k i ( by linarith );
    -- Since the set {j | v1 n < j ∧ 2 * A j = A i} has at most one element, its cardinality is at most 1.
    have h_card : Finset.card ((Finset.range k).filter (fun j => v1 n < j ∧ 2 * A j = A i)) ≤ 1 := by
      have h_card : ∀ j1 j2, v1 n < j1 → v1 n < j2 → 2 * A j1 = A i → 2 * A j2 = A i → j1 = j2 := by
        intros j1 j2 hj1 hj2 hj1_eq hj2_eq;
        exact StrictMono.injective ( show StrictMono A from by exact A_strictMono ) ( by linarith );
      exact Finset.card_le_one.mpr fun x hx y hy => h_card x y ( Finset.mem_filter.mp hx |>.2.1 ) ( Finset.mem_filter.mp hy |>.2.1 ) ( Finset.mem_filter.mp hx |>.2.2 ) ( Finset.mem_filter.mp hy |>.2.2 );
    grind

/-
If the initial condition holds, then for any `i` with `A i \ge 6 * A (v1 n)`, the final coefficient is 0.
-/
theorem coeffs_stable_large (n : ℕ) (h : 0 < n) (i : ℕ)
  (h_init : ∀ j, coeffs_sequence_v2 n h (c_initial n) (v1 n + 1) j > 0 → A j < 3 * A (v1 n))
  (hi : 6 * A (v1 n) ≤ A i) :
  coeffs_sequence_v2 n h (c_initial n) (v2 n + 1) i = 0 := by
    -- By definition of `coeffs_sequence_v2`, if `A i ≥ 6 * A (v1 n)`, then `coeffs_sequence_v2 n h (c_initial n) (v2 n + 1) i = 0`.
    have h_final_zero : ∀ k ≥ v1 n + 1, k ≤ v2 n + 1 → coeffs_sequence_v2 n h (c_initial n) k i = 0 := by
      intro k hk₁ hk₂;
      induction hk₁ <;> simp_all +decide [ Nat.succ_eq_add_one ];
      · grind;
      · rename_i k hk₁ hk₂;
        by_cases h_case : coeffs_sequence_v2 n h (c_initial n) k k ≥ 2 ∧ 2 * A k = A i;
        · have h_part2_invariant : part2_invariant n (coeffs_sequence_v2 n h (c_initial n) k) := by
            apply part2_invariant_holds n h k hk₁ (by linarith) h_init;
          exact absurd ( h_part2_invariant k ( by linarith ) ( by linarith ) ) ( by linarith );
        · rw [ show coeffs_sequence_v2 n h ( c_initial n ) ( k + 1 ) i = coeffs_sequence_v2 n h ( c_initial n ) k i from ?_ ];
          · exact ‹k ≤ v2 n + 1 → coeffs_sequence_v2 n h ( c_initial n ) k i = 0› ( by linarith );
          · rw [ show coeffs_sequence_v2 n h ( c_initial n ) ( k + 1 ) = step_transform_v2 n h ( coeffs_sequence_v2 n h ( c_initial n ) k ) k from rfl ];
            unfold step_transform_v2;
            split_ifs <;> norm_num;
            · linarith;
            · have := Classical.choose_spec ( reduction_step_part2_strong n h ( coeffs_sequence_v2 n h ( c_initial n ) k ) k ‹_› hk₂ ‹_› );
              grind;
    exact h_final_zero _ ( by linarith [ show v1 n < v2 n from by linarith [ v1_lt_v2 n h ] ] ) ( by linarith )

/-
If the coefficient at `v1` in the solution is 1, then the support of the solution is bounded by `6 * A (v1 n)`.
-/
theorem c_sol_v1_eq_one_implies_support_bounded_tight (n : ℕ) (h : 0 < n) :
  c_sol n h (v1 n) = 1 → support_bounded (c_sol n h) (6 * A (v1 n)) := by
    intro h;
    have h_support_bounded : ∀ i, 6 * A (v1 n) ≤ A i → coeffs_sequence_v2 n ‹_› (c_initial n) (v2 n + 1) i = 0 := by
      have h_support_bounded : ∀ i, coeffs_sequence_v2 n ‹_› (c_initial n) (v1 n + 1) i > 0 → A i < 3 * A (v1 n) := by
        apply part1_bound_if_v1_not_reduced_v2;
        have h_eq : ∀ k, k > v1 n → coeffs_sequence_v2 n ‹_› (c_initial n) k (v1 n) = coeffs_sequence_v2 n ‹_› (c_initial n) (v1 n + 1) (v1 n) := by
          (expose_names;
            exact fun k a => coeffs_sequence_v2_stable_after_step n h_1 (c_initial n) (v1 n) k a);
        exact h_eq ( v2 n + 1 ) ( by linarith [ v1_lt_v2 n ‹_› ] ) ▸ h;
      (expose_names; exact fun i a => coeffs_stable_large n h_1 i h_support_bounded a);
    unfold c_sol; aesop;

/-
There exists an index `i` such that `c_sol n h i = 1`.
-/
theorem exists_c_sol_eq_one (n : ℕ) (h : 0 < n) : ∃ i, c_sol n h i = 1 := by
  -- Since $n > 0$, the sum $\sum_{i=0}^{v_3(n)} c_{sol}(n, h)(i) A(i)$ must be positive. Therefore, there must be some $i$ such that $c_{sol}(n, h)(i) A(i) > 0$.
  have h_pos : ∃ i, c_sol n h i * A i > 0 := by
    have h_pos : ∑ i ∈ Finset.range (v3 n + 1), c_sol n h i * A i > 0 := by
      rw [ show c_sol n h = coeffs_sequence_v2 n h ( c_initial n ) ( v2 n + 1 ) by rfl ];
      -- Apply the sum preservation property to conclude the equality.
      have h_sum : n = ∑ i ∈ Finset.range (v3 n + 1), coeffs_sequence_v2 n h (c_initial n) (v2 n + 1) i * A i := by
        apply coeffs_sequence_v2_sum_preserved;
        exact c_initial_sum n h;
      linarith;
    contrapose! h_pos; aesop;
  contrapose! h_pos;
  -- If $c_sol n h x \neq 1$, then $c_sol n h x = 0$ because $c_sol n h x \leq 1$.
  have h_zero : ∀ x, c_sol n h x ≤ 1 := by
    exact fun x => c_sol_le_one n h x;
  exact fun x => by cases lt_or_eq_of_le ( h_zero x ) <;> aesop;

/-
If `min_i` is the smallest index with coefficient 1, then for any other index `i` with coefficient 1, `A i < 6 * A min_i`.
-/
lemma bound_logic (n : ℕ) (h : 0 < n) (i : ℕ) (min_i : ℕ)
  (h_min : c_sol n h min_i = 1 ∧ ∀ j, c_sol n h j = 1 → min_i ≤ j)
  (hi : c_sol n h i = 1) :
  A i < 6 * A min_i := by
    by_cases h_case : min_i = v1 n;
    · have := c_sol_v1_eq_one_implies_support_bounded_tight n h;
      specialize this ( by aesop ) i ; aesop;
    · -- Since `min_i ≠ v1 n`, we have `min_i > v1 n`.
      have h_min_gt_v1 : v1 n < min_i := by
        exact lt_of_le_of_ne ( by exact le_of_not_gt fun hi' => by have := c_sol_eq_zero_of_lt_v1 n h min_i hi'; aesop ) ( Ne.symm h_case );
      have := c_sol_support_bounded n h;
      exact lt_of_lt_of_le ( lt_of_not_ge fun hi' => by have := this i hi'; aesop ) ( mul_le_mul_of_nonneg_left ( show A ( v1 n + 1 ) ≤ A min_i from monotone_nat_of_le_succ ( fun n => A_strictMono.monotone n.le_succ ) ( by linarith ) ) ( by norm_num ) )

/-
The set `I_sol` sums to `n`.
-/
noncomputable def I_sol (n : ℕ) (h : 0 < n) : Finset ℕ :=
  (Finset.range (v3 n + 1)).filter (fun i => c_sol n h i = 1)

theorem I_sol_sum (n : ℕ) (h : 0 < n) : n = ∑ i ∈ I_sol n h, A i := by
  unfold I_sol;
  have h_sum : n = ∑ i ∈ Finset.range (v3 n + 1), (c_sol n h i) * (A i) := by
    -- Apply the theorem that the sum is preserved through the transformations.
    apply coeffs_sequence_v2_sum_preserved;
    exact c_initial_sum n h;
  have h_c_sol_le_one : ∀ i, c_sol n h i ≤ 1 := by
    exact fun i => c_sol_le_one n h i;
  rw [ Finset.sum_congr rfl fun i hi => by rw [ show c_sol n h i * A i = ( if c_sol n h i = 1 then A i else 0 ) by specialize h_c_sol_le_one i; interval_cases c_sol n h i <;> simp +decide ] ] at h_sum ; simp +decide [ Finset.sum_ite ] at h_sum ⊢ ; linarith

/-
If `c_sol n h i = 1`, then `i` is within the range `v3 n + 1`.
-/
theorem c_sol_subset_range_v3 (n : ℕ) (h : 0 < n) (i : ℕ) (hi : c_sol n h i = 1) : i < v3 n + 1 := by
  have h_bound : A i < 6 * A (v1 n + 1) := by
    have h_support : support_bounded (c_sol n h) (6 * A (v1 n + 1)) := by
      exact c_sol_support_bounded n h;
    exact lt_of_not_ge fun hi' => by have := h_support i hi'; aesop;
  have h_bound : 6 * A (v1 n + 1) ≤ A (v3 n + 1) := by
    have := v_spec n;
    rcases k : m_index n with ( _ | _ | k ) <;> simp_all +decide;
    unfold m_index at k;
    unfold sumA at k; aesop;
  exact Nat.lt_of_not_ge fun hi' => by linarith [ show A i ≥ A ( v3 n + 1 ) from by exact monotone_nat_of_le_succ ( fun n => A_strictMono.monotone n.le_succ ) hi' ] ;

/-
An index `i` is in `I_sol` if and only if `c_sol n h i = 1`.
-/
theorem I_sol_mem_iff (n : ℕ) (h : 0 < n) (i : ℕ) : i ∈ I_sol n h ↔ c_sol n h i = 1 := by
  -- By definition of $I_{\text{sol}}$, we have $i \in I_{\text{sol}}$ if and only if $c_{\text{sol}}(n, h, i) = 1$ and $i < v_3 n + 1$.
  constructor;
  · exact fun hi => Finset.mem_filter.mp hi |>.2;
  · exact fun hi => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( c_sol_subset_range_v3 n h i hi ), hi ⟩

/-
Every positive integer `n` can be written as a sum of distinct 3-smooth numbers `A i` such that the largest element is less than 6 times the smallest element.
-/
theorem main_result_proven (n : ℕ) (h : 0 < n) :
  ∃ I : Finset ℕ, n = ∑ i ∈ I, A i ∧ ∃ min_i ∈ I, ∀ i ∈ I, A min_i ≤ A i ∧ A i < 6 * A min_i := by
    let I := I_sol n h
    exists I
    constructor
    · exact I_sol_sum n h
    · have h_nonempty : I.Nonempty := by
        obtain ⟨i, hi⟩ := exists_c_sol_eq_one n h
        use i
        rw [I_sol_mem_iff n h]
        exact hi
      let min_i := I.min' h_nonempty
      exists min_i
      constructor
      · exact I.min'_mem h_nonempty
      · intro i hi
        constructor
        · apply A_strictMono.monotone
          apply I.min'_le
          exact hi
        · apply bound_logic n h i min_i
          · constructor
            · rw [← I_sol_mem_iff n h]; exact I.min'_mem h_nonempty
            · intro j hj
              rw [← I_sol_mem_iff n h] at hj
              apply I.min'_le _ hj
          · rw [← I_sol_mem_iff n h]; exact hi


#print axioms main_result_proven
