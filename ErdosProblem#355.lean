/-
Vjekoslav Kovač and I proved that there exists a lacunary sequence of positive integers whose reciprocal sums represent all rational numbers in an interval.

W. van Doorn and V. Kovač, Lacunary sequences whose reciprocal sums represent all rationals in an interval. arXiv:2509.24971 (2025).

We thereby solved Erdos Problem #355 (https://www.erdosproblems.com/355).

Below you can find a formalization of this result. Even though the above paper shows that any lacunarity constant smaller than 2 is possible, the formalization below is based on a simplified proof that Vjeko wrote, which has lacunarity constant 1.01. This simplified proof was given to Gemini3 in order to make it more easily formalizable, which was eventually done with the use of Aristotle (and a whole lot of patience on my end).

At the very end you can find the statement of Erdos Problem #355 taken from the Formal Conjectures from Google DeepMind. 

https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/355.lean

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-- Harmonic `generalize_proofs
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
Construction of a valid block using the deterministic strategy.
-/
def get_params (k : ℕ) : ℕ × ℕ :=
  let a := Nat.log 2 k
  if k = 2^a then
    (k, a - 1)
  else if (k : ℚ) / (2 ^ a : ℚ) < 11/10 then
    (3 * k, a + 1)
  else
    (k, a)

def simple_block_data (k : ℕ) : List ℕ :=
  let (M, s) := get_params k
  let a := Nat.log 2 k
  let N := a + 10 -- Sufficiently large
  let powers := (List.range (N + 1)).map (fun i => 2 ^ i)
  let bridge := (List.range (s + 1)).map (fun i => M * 2 ^ (N - s + i))
  powers ++ bridge

lemma simple_block_valid (k : ℕ) (hk : k ≥ 2) :
  let data := simple_block_data k
  data.head? = some 1 ∧
  k ∣ data.getLast! ∧
  (∀ x ∈ data, x ∣ data.getLast!) ∧
  (∀ i, i + 1 < data.length →
    (101 : ℝ) / 100 ≤ (data.get! (i + 1) : ℝ) / data.get! i ∧
    (data.get! (i + 1) : ℝ) / data.get! i ≤ 2) := by
      unfold simple_block_data;
      refine' ⟨ _, _, _, _ ⟩;
      · simp +arith +decide [ List.range_succ_eq_map ];
      · simp +zetaDelta at *;
        unfold get_params;
        norm_num [ List.range_succ ];
        split_ifs <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ];
      · unfold get_params;
        simp +zetaDelta at *;
        rintro x ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ );
        · split_ifs <;> norm_num [ List.range_succ ] at *;
          · exact dvd_mul_of_dvd_right ( pow_dvd_pow _ ( by omega ) ) _;
          · exact dvd_mul_of_dvd_right ( pow_dvd_pow _ ( by linarith ) ) _;
          · exact dvd_mul_of_dvd_right ( pow_dvd_pow _ ( by linarith ) ) _;
        · split_ifs at * <;> norm_num [ List.range_succ ] at *;
          · exact mul_dvd_mul_left _ ( pow_dvd_pow _ ( by omega ) );
          · exact mul_dvd_mul_left _ ( pow_dvd_pow _ ( by omega ) );
          · exact mul_dvd_mul_left _ ( pow_dvd_pow _ ( by linarith ) );
      · intro i hi;
        by_cases hi' : i < Nat.log 2 k + 10 + 1;
        · norm_num [ List.get! ];
          rw [ List.getElem?_append, List.getElem?_append ];
          split_ifs <;> simp_all +decide;
          · norm_num [ pow_succ', mul_div_assoc ];
          · norm_num [ show i = Nat.log 2 k + 10 by linarith ] at *;
            unfold get_params; norm_num [ Nat.log_eq_iff ] at *;
            split_ifs <;> norm_num [ pow_add, pow_one, pow_mul, mul_assoc, div_eq_mul_inv ] at *;
            · rw [ ‹k = 2 ^ Nat.log 2 k› ] ; norm_num [ Nat.succ_sub ] ; ring_nf ; norm_num;
              rw [ show 10 + Nat.log 2 k - ( Nat.log 2 k - 1 ) = 11 by exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 ≤ Nat.log 2 k from Nat.le_log_of_pow_le ( by norm_num ) <| by linarith ] ] ; norm_num [ ← mul_pow ];
            · field_simp at *;
              norm_cast at *;
              norm_num [ Nat.add_sub_add_left, pow_add ] at *;
              constructor <;> nlinarith [ Nat.pow_log_le_self 2 ( by linarith : k ≠ 0 ), Nat.lt_pow_of_log_lt ( by linarith ) ( by linarith : Nat.log 2 k < Nat.log 2 k + 1 ) ];
            · field_simp at *;
              norm_cast at *;
              have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) k;
              rw [ pow_succ' ] at this ; omega;
        · simp_all +decide [List.getElem?_append];
          split_ifs <;> simp_all +arith +decide;
          · linarith;
          · rw [ List.getElem_append ] at * ; norm_num at *;
            split_ifs <;> norm_num at *;
            · linarith;
            · rw [ List.getElem?_range ] ; norm_num;
              · rw [ show i + 1 - ( Nat.log 2 k + 11 ) = i - ( Nat.log 2 k + 11 ) + 1 by omega ] ; norm_num [ pow_add, mul_assoc, mul_div_mul_left ];
                field_simp;
                rw [ le_div_iff₀, div_le_iff₀ ] <;> norm_cast <;> norm_num [ get_params ];
                · split_ifs <;> linarith;
                · split_ifs <;> norm_num ; linarith;
                  · linarith;
                  · linarith;
                · split_ifs <;> norm_num ; linarith;
                  · linarith;
                  · linarith;
              · omega

/-
Definition of the block data selector `D` and the recursive construction of the full sequence list.
-/
def D (k : ℕ) : List ℕ := simple_block_data k

def full_seq_list : ℕ → List ℕ
| 0 => []
| 1 => [1]
| k + 1 =>
  let prev := full_seq_list k
  let L := prev.getLastD 1
  let d := D (k + 1)
  prev ++ d.tail.map (fun x => L * x)

/-
The constructed sequence list is never empty for $k \ge 1$.
-/
lemma full_seq_list_nonempty (k : ℕ) (hk : k ≥ 1) : full_seq_list k ≠ [] := by
  rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
  induction k <;> simp_all +arith +decide [ full_seq_list ]

/-
The infinite sequence `a` is well-defined and consistent with the finite block construction.
-/
def a_seq (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let k := n + 2
  let list := full_seq_list k
  if h : n - 1 < list.length then list.get ⟨n - 1, h⟩ else 0

lemma a_seq_eq_get (n k : ℕ) (hn : n > 0) (hk : n - 1 < (full_seq_list k).length) :
  a_seq n = (full_seq_list k).get! (n - 1) := by
    -- By definition of `a_seq`, since `n > 0`, we have `a_seq n = (full_seq_list (n + 2)).get ⟨n - 1, h⟩`.
    have h_a_seq_def : a_seq n = (full_seq_list (n + 2)).get ⟨n - 1, by
      -- The length of `full_seq_list` is strictly increasing with respect to `k`.
      have h_length_increasing : ∀ k, (full_seq_list (k + 1)).length ≥ (full_seq_list k).length + 1 := by
        intro k;
        induction' k with k ih <;> simp +arith +decide [ *, full_seq_list ];
        unfold D; simp +arith +decide [ simple_block_data ] ;
      -- By induction on $n$, we can show that the length of `full_seq_list` is at least $n + 1$.
      have h_length_ge_n_plus_1 : ∀ n, (full_seq_list (n + 1)).length ≥ n + 1 := by
        exact fun n => Nat.recOn n ( by simp +arith +decide ) fun n ihn => by linarith [ h_length_increasing ( n + 1 ) ] ;
      exact lt_of_lt_of_le ( Nat.sub_lt hn zero_lt_one ) ( by linarith [ h_length_ge_n_plus_1 ( n + 1 ) ] )⟩ := by
      all_goals generalize_proofs at *;
      unfold a_seq; aesop;
    generalize_proofs at *;
    -- By definition of `full_seq_list`, we know that `full_seq_list k` is a prefix of `full_seq_list (n + 2)`.
    have h_prefix : ∀ m n : ℕ, m ≤ n → (full_seq_list m).length ≤ (full_seq_list n).length ∧ ∀ i < (full_seq_list m).length, (full_seq_list m).get! i = (full_seq_list n).get! i := by
      intros m n hmn
      induction' hmn with m n hmn ih;
      · exact ⟨ le_rfl, fun i hi => rfl ⟩;
      · rcases m <;> simp_all +decide [ full_seq_list ];
        grind +ring;
    by_cases h_cases : k ≤ n + 2;
    · specialize h_prefix k ( n + 2 ) h_cases ; aesop;
    · specialize h_prefix ( n + 2 ) k ( by linarith ) ; aesop;

/-
Definitions of the set of subset sums `P` and the lacunarity property `IsLacunary`.
-/
def P (x : ℕ → ℝ) : Set ℝ :=
  { s | ∃ T : Finset ℕ, s = ∑ i ∈ T, x i }

def IsLacunary (a : ℕ → ℕ) : Prop :=
  ∃ lambda_val > 1, ∀ i ≥ 1, (a (i + 1) : ℝ) / a i ≥ lambda_val

/-
The set of sums of all sublists of a list L.
-/
def reachable_sums (L : List ℕ) : Set ℕ := { s | ∃ T, List.Sublist T L ∧ s = T.sum }

/-
The reachable sums of a list with an appended element are the union of the original sums and the original sums shifted by the new element.
-/
lemma reachable_sums_append_singleton (L : List ℕ) (x : ℕ) :
  reachable_sums (L ++ [x]) = reachable_sums L ∪ { y | ∃ s, s ∈ reachable_sums L ∧ y = s + x } := by
    ext y; simp [reachable_sums];
    constructor <;> intro h;
    · refine' if hx : x ∈ h.choose then _ else _ <;> simp_all +decide [ List.sublist_append_iff ];
      · grind;
      · grind;
    · rcases h with ( ⟨ T, hT₁, rfl ⟩ | ⟨ s, ⟨ T, hT₁, rfl ⟩, rfl ⟩ ) <;> [ exact ⟨ T, hT₁.trans ( List.sublist_append_left _ _ ), rfl ⟩ ; exact ⟨ T ++ [ x ], List.Sublist.trans ( List.sublist_append_right _ _ ) ( List.Sublist.append_right _ ( by simp +decide ) ), by simp +decide ⟩ ];
      exact ⟨ T ++ [ x ], List.Sublist.append ( hT₁ ) ( List.Sublist.refl _ ), by simp +decide ⟩

/-
If a list starts with 1 and satisfies the growth condition, its reachable sums cover the full range.
-/
lemma reachability_integers (b : List ℕ) (h_head : b.head? = some 1)
  (h_growth : ∀ i, i + 1 < b.length → b.get! (i + 1) ≤ 1 + (b.take (i + 1)).sum) :
  reachable_sums b = { s | s ≤ b.sum } := by
    induction' b using List.reverseRecOn with b ih;
    · contradiction;
    · by_cases hb : b = [] <;> simp_all +decide [ reachable_sums_append_singleton ];
      · ext ( _ | _ | s ) <;> simp +arith +decide [ reachable_sums ];
      · -- By the induction hypothesis, we know that reachable_sums b is equal to {s | s ≤ b.sum}.
        have h_ind : reachable_sums b = {s | s ≤ b.sum} := by
          apply_assumption;
          · cases b <;> aesop;
          · intro i hi; specialize h_growth i ( by linarith ) ; simp_all +decide [ List.take_append ] ;
            simp_all +decide [ Nat.sub_eq_zero_of_le ( by linarith : i + 1 ≤ b.length ) ];
        -- By the growth condition, we know that ih ≤ b.sum + 1.
        have h_ih_le : ih ≤ b.sum + 1 := by
          specialize h_growth ( b.length - 1 ) ; rcases b with ( _ | ⟨ _, _ | b ⟩ ) <;> simp_all +arith +decide;
        ext s; simp [h_ind];
        exact ⟨ fun hs => hs.elim ( fun hs => by linarith ) fun ⟨ t, ht, ht' ⟩ => by linarith, fun hs => if hs' : s ≤ b.sum then Or.inl hs' else Or.inr ⟨ s - ih, by omega, by omega ⟩ ⟩

/-
A list satisfies the growth condition if every element (except the first) is at most 1 plus the sum of all preceding elements.
-/
def GrowthCondition (b : List ℕ) : Prop :=
  ∀ i, i + 1 < b.length → b.get! (i + 1) ≤ 1 + (b.take (i + 1)).sum

/-
If a list starts with 1 and consecutive elements satisfy $x_{i+1} \le 2 x_i$, then it satisfies the growth condition.
-/
lemma ratio_le_2_implies_growth (b : List ℕ) (h_head : b.head? = some 1)
  (h_ratio : ∀ i, i + 1 < b.length → b.get! (i + 1) ≤ 2 * b.get! i) :
  GrowthCondition b := by
    intro i hi; induction' i with i ih;
    · cases b <;> aesop;
    · simp_all +arith +decide [ List.take_succ ];
      grind

/-
If a list starts with 1 and satisfies the growth condition, its reachable sums cover the full range of integers up to the total sum.
-/
lemma reachability_integers_of_growth (b : List ℕ) (h_head : b.head? = some 1)
  (h_growth : GrowthCondition b) :
  reachable_sums b = { s | s ≤ b.sum } := by
    have h_induction_step : ∀ L : List ℕ, L.head? = some 1 → GrowthCondition L → reachable_sums L = { s : ℕ | s ≤ L.sum } := by
      exact fun L a a_1 => reachability_integers L a a_1;
    apply h_induction_step; assumption; assumption

/-
`ValidPrefix` encapsulates the properties required for the sequence blocks: starting with 1, non-empty, growth ratios in [1.01, 2], and divisibility of all elements into the last.
-/
def ValidPrefix (L : List ℕ) : Prop :=
  L.head? = some 1 ∧
  L ≠ [] ∧
  (∀ i, i + 1 < L.length →
    (101 : ℝ) / 100 ≤ (L.get! (i + 1) : ℝ) / L.get! i ∧
    (L.get! (i + 1) : ℝ) / L.get! i ≤ 2) ∧
  (∀ x ∈ L, x ∣ L.getLast!)

/-
`HasGrowth` asserts that consecutive elements in a list have a ratio between 1.01 and 2.
`growth_map_scale` states that scaling a list by a positive integer preserves this growth property.
-/
def HasGrowth (L : List ℕ) : Prop :=
  ∀ i, i + 1 < L.length →
    (101 : ℝ) / 100 ≤ (L.get! (i + 1) : ℝ) / L.get! i ∧
    (L.get! (i + 1) : ℝ) / L.get! i ≤ 2

lemma growth_map_scale (L : List ℕ) (c : ℕ) (hc : c > 0) (h : HasGrowth L) :
  HasGrowth (L.map (c * ·)) := by
    unfold HasGrowth at *;
    simp +zetaDelta at *;
    intro i hi; convert h i hi using 1 ; cases L[i + 1]? <;> cases L[i]? <;> simp +decide [ *, mul_div_mul_left _ _ ( by positivity : ( c : ℝ ) ≠ 0 ) ] ;
    cases L[i + 1]? <;> cases L[i]? <;> simp_all +decide [ mul_div_mul_left _ _ ( by positivity : ( c : ℝ ) ≠ 0 ) ]

/-
If a list satisfies the growth condition, its tail also satisfies the growth condition.
-/
lemma growth_tail (L : List ℕ) (h : HasGrowth L) : HasGrowth L.tail := by
  intro i hi; have := h ( i + 1 ) ; aesop;

/-
`growth_append` states that concatenating two lists that satisfy the growth condition results in a list that satisfies the growth condition, provided the boundary transition also satisfies the condition.
-/
lemma growth_append (L1 L2 : List ℕ) (h1 : HasGrowth L1) (h2 : HasGrowth L2)
  (hne1 : L1 ≠ []) (hne2 : L2 ≠ [])
  (h_boundary : (101 : ℝ) / 100 ≤ (L2.head! : ℝ) / L1.getLast! ∧ (L2.head! : ℝ) / L1.getLast! ≤ 2) :
  HasGrowth (L1 ++ L2) := by
    intro i hi; rcases lt_trichotomy i ( List.length L1 - 1 ) with hi' | rfl | hi' <;> norm_num at *;
    · convert h1 i ( by omega ) using 1;
      · simp +decide [List.getElem?_append,
        show i < L1.length from lt_of_lt_of_le hi' (Nat.pred_le _)];
        rw [ if_pos ( by omega ) ];
      · simp +decide [List.getElem?_append,
        show i < L1.length from lt_of_lt_of_le hi' (Nat.pred_le _)];
        rw [ if_pos ( by omega ) ];
    · rcases L1 <;> rcases L2 <;> simp_all +arith +decide [ List.getLast? ];
      simp_all +decide [ List.getLast_eq_getElem ];
      grind +ring;
    · convert h2 ( i - List.length L1 ) ( by omega ) using 1 <;> norm_num [ List.getElem?_append, Nat.sub_add_cancel ( show List.length L1 ≤ i + 1 from by omega ) ];
      · split_ifs <;> try omega;
        rw [ show i + 1 - L1.length = i - L1.length + 1 by omega ];
      · split_ifs <;> simp_all +decide;
        · omega;
        · omega;
        · omega;
        · rw [ show i + 1 - L1.length = i - L1.length + 1 by omega ]

/-
If a list is a valid prefix, it satisfies the growth condition.
-/
lemma valid_prefix_growth (L : List ℕ) (h : ValidPrefix L) : HasGrowth L := by
  exact h.2.2.1

/-
`divisibility_merge` proves that if we merge two valid prefixes (scaling the second one), the divisibility property is preserved.
-/
lemma divisibility_merge (L1 L2 : List ℕ) (h1 : ValidPrefix L1) (h2 : ValidPrefix L2) :
  ∀ x ∈ L1 ++ L2.tail.map (fun x => L1.getLast! * x), x ∣ (L1 ++ L2.tail.map (fun x => L1.getLast! * x)).getLast! := by
    simp_all +decide [ ValidPrefix, List.getLast! ];
    rcases L1 <;> rcases L2 <;> simp_all +decide;
    simp_all +decide [ List.getLast_eq_getElem ];
    simp_all +decide [List.getElem_cons];
    intro x hx; split_ifs at hx ⊢ <;> simp_all +decide [ List.getElem_append ] ;
    · grind +ring;
    · rcases hx with ( ( rfl | hx ) | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
      · split_ifs <;> simp_all +decide [Nat.mul_mod];
        cases ‹List ℕ› <;> simp_all +decide [ Nat.add_sub_assoc ];
        grind;
      · split_ifs <;> simp_all +decide [Nat.mul_mod_mul_left];
        · grind +ring;
        · simp_all +decide [ Nat.sub_sub, add_comm ];
          simp_all +decide [Nat.add_sub_add_left];
          grind +ring

/-
If a list is a valid prefix, its last element is positive.
-/
lemma valid_prefix_last_pos (L : List ℕ) (h : ValidPrefix L) : L.getLast! > 0 := by
  -- Since `L` is a valid prefix, its last element is positive.
  cases' L with x L <;> simp_all +decide [ List.getLast! ];
  · cases h.2.1 rfl;
  · have := h.2.2.1 ( List.length L - 1 ) ; rcases L with ( _ | ⟨ y, L ⟩ ) <;> simp_all +decide [ List.getLast_eq_getElem ];
    · cases h ; aesop;
    · exact Nat.pos_of_ne_zero fun h' => by norm_num [ h' ] at this;

/-
If a list is a valid prefix and has at least two elements, the second element must be 2.
-/
lemma valid_prefix_second_eq_two (L : List ℕ) (h : ValidPrefix L) (hne : L.tail ≠ []) :
  L.tail.head! = 2 := by
    have h_ratio : (L.tail.head! : ℝ) / 1 ≥ 1.01 ∧ (L.tail.head! : ℝ) / 1 ≤ 2 := by
      rcases L with ( _ | ⟨ x, _ | ⟨ y, L ⟩ ⟩ ) <;> norm_num at *;
      have := h.2.2.1 0; norm_num at this;
      have := h.1; aesop;
    norm_num at h_ratio; rcases n : L.tail.head! with ( _ | _ | _ | k ) <;> simp_all +decide ; linarith;
    norm_num at h_ratio

/-
`valid_prefix_merge_growth` proves that the merged list satisfies the growth condition.
-/
lemma valid_prefix_merge_growth (L1 L2 : List ℕ) (h1 : ValidPrefix L1) (h2 : ValidPrefix L2) :
  HasGrowth (L1 ++ L2.tail.map (fun x => L1.getLast! * x)) := by
    by_cases hL2 : L2.tail = [];
    · -- Since L2.tail is empty, the list simplifies to L1. Therefore, HasGrowth (L1 ++ []) is just HasGrowth L1, which is true by h1.
      simp [hL2, HasGrowth];
      have := h1.2.2.1; aesop;
    · have h_growth_L1 : HasGrowth L1 := by
        exact valid_prefix_growth L1 h1;
      convert growth_append _ _ h_growth_L1 _ _ _ _ using 1;
      · convert growth_map_scale _ _ _ _;
        · exact valid_prefix_last_pos L1 h1;
        · exact growth_tail _ ( valid_prefix_growth _ h2 );
      · exact h1.2.1;
      · grind;
      · field_simp;
        rw [ show ( List.map ( fun x => L1.getLast! * x ) L2.tail ).head! = L1.getLast! * L2.tail.head! from ?_ ];
        · have h_ratio : L2.tail.head! = 2 := by
            exact valid_prefix_second_eq_two L2 h2 hL2;
          rw [ h_ratio ] ; norm_num [ mul_div_cancel_left₀, show L1.getLast! ≠ 0 from Nat.ne_of_gt ( valid_prefix_last_pos L1 h1 ) ];
          rw [ mul_div_assoc ] ; norm_num [ show L1.getLast?.getD 0 ≠ 0 from by { have := valid_prefix_last_pos L1 h1; aesop } ];
        · cases h : L2.tail <;> aesop

/-
`valid_prefix_merge` proves that merging two valid prefixes (with the second scaled) preserves validity.
-/
lemma valid_prefix_merge (L1 L2 : List ℕ) (h1 : ValidPrefix L1) (h2 : ValidPrefix L2) :
  ValidPrefix (L1 ++ L2.tail.map (fun x => L1.getLast! * x)) := by
    unfold ValidPrefix at *;
    refine' ⟨ _, _, _, _ ⟩;
    · cases L1 <;> aesop;
    · aesop;
    · convert valid_prefix_merge_growth L1 L2 h1 h2 using 1;
    · -- By definition of `divisibility_merge`, we know that every element in the merged list divides the last element.
      apply divisibility_merge L1 L2 h1 h2

/-
`simple_block_valid_prefix` states that the blocks `D k` generated by `simple_block_data` are valid prefixes for $k \ge 2$.
-/
lemma simple_block_valid_prefix (k : ℕ) (hk : k ≥ 2) : ValidPrefix (D k) := by
  -- By definition of `D`, we know that `D k` satisfies the conditions of being a valid prefix except for ending in a multiple of `k`.
  have h_D_valid : ∀ i, i + 1 < (D k).length → (101 : ℝ) / 100 ≤ ((D k).get! (i + 1) : ℝ) / (D k).get! i ∧ ((D k).get! (i + 1) : ℝ) / (D k).get! i ≤ 2 := by
    convert simple_block_valid k hk |>.2.2.2 using 1;
  refine' ⟨ _, _, h_D_valid, _ ⟩;
  · convert simple_block_valid k hk |>.1 using 1;
  · exact ne_of_apply_ne List.length ( by erw [ show D k = simple_block_data k from rfl ] ; unfold simple_block_data; aesop_cat );
  · convert simple_block_valid k hk |>.2.2.1 using 1

/-
`full_seq_valid` proves that the constructed sequence prefix `full_seq_list k` is always a valid prefix for $k \ge 1$.
-/
lemma full_seq_valid (k : ℕ) (hk : k ≥ 1) : ValidPrefix (full_seq_list k) := by
  induction' k, hk using Nat.le_induction with k ih;
  · constructor <;> norm_num [ full_seq_list ];
  · convert valid_prefix_merge _ _ ‹_› ( simple_block_valid_prefix ( k + 1 ) ( by linarith ) ) using 1;
    -- By definition of `full_seq_list`, we have `full_seq_list (k + 1) = full_seq_list k ++ (D (k + 1)).tail.map (fun x => (full_seq_list k).getLast! * x)`.
    rw [show full_seq_list (k + 1) = full_seq_list k ++ (D (k + 1)).tail.map (fun x => (full_seq_list k).getLastD 1 * x) from by
          rcases k with ( _ | _ | k ) <;> tauto];
    cases h : full_seq_list k <;> simp_all +decide [ List.getLast? ];
    cases ‹ValidPrefix []›.1

/-
`full_seq_divisible` proves that the last element of `full_seq_list k` is divisible by `k`.
-/
lemma full_seq_divisible (k : ℕ) (hk : k ≥ 1) : k ∣ (full_seq_list k).getLast! := by
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ full_seq_list ];
  convert Nat.dvd_mul_left ( k + 1 + 1 ) ( ( full_seq_list ( k + 1 ) ).getLast?.getD 1 * ( D ( k + 1 + 1 ) ).getLast! / ( k + 1 + 1 ) ) using 1;
  rw [ Nat.div_mul_cancel ];
  · unfold D; simp +decide [ List.getLast? ] ;
    rcases h : simple_block_data ( k + 1 + 1 ) with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide [ List.getLast ];
    · exact absurd h ( by exact ne_of_apply_ne List.length ( by simp +arith +decide [ simple_block_data ] ) );
    · unfold simple_block_data at h; simp_all +decide [ List.range_succ ] ;
      replace h := congr_arg List.length h ; simp +arith +decide at h;
    · induction l using List.reverseRecOn <;> aesop;
  · have := simple_block_valid ( k + 1 + 1 ) ( by linarith );
    exact dvd_mul_of_dvd_right this.2.1 _

/-
The set of reachable sums of a list is the same as the set of reachable sums of its reverse.
-/
lemma reachable_sums_reverse (L : List ℕ) : reachable_sums L.reverse = reachable_sums L := by
  unfold reachable_sums;
  grind

/-
`inv_scaled_reverse_ratio` proves that the reversed inverse scaled list starts with 1 and satisfies the ratio condition $\le 2$.
-/
lemma inv_scaled_reverse_ratio (x : List ℕ) (hx_len : x.length > 0)
  (h_div : ∀ y ∈ x, y ∣ x.getLast!)
  (h_growth : ∀ i, i + 1 < x.length → (x.get! (i + 1) : ℝ) / x.get! i ≤ 2)
  (h_pos : ∀ y ∈ x, y > 0) :
  let b := (x.map (fun z => x.getLast! / z)).reverse
  b.head? = some 1 ∧
  ∀ i, i + 1 < b.length → b.get! (i + 1) ≤ 2 * b.get! i := by
    -- Show that the head of the reversed list is 1.
    have h_head : (List.map (fun z => x.getLast! / z) x).reverse.head? = some 1 := by
      induction x using List.reverseRecOn <;> aesop;
    refine And.intro h_head ( fun j hj ↦ ?_ );
    -- By definition of `b`, we know that `b.get! (j + 1) = x.getLast! / x.get! (x.length - 2 - j)` and `b.get! j = x.getLast! / x.get! (x.length - 1 - j)`.
    have h_b_values : (List.map (fun z => x.getLast! / z) x).reverse.get! (j + 1) = x.getLast! / x.get! (x.length - 2 - j) ∧ (List.map (fun z => x.getLast! / z) x).reverse.get! j = x.getLast! / x.get! (x.length - 1 - j) := by
      simp +zetaDelta at *;
      grind;
    have := h_growth ( x.length - 2 - j ) ?_ <;> simp_all +decide [ Nat.sub_sub ];
    · rw [ div_le_iff₀ ] at this <;> norm_cast at * <;> simp_all +decide [add_comm,
      add_left_comm];
      rw [ ← Nat.mul_div_assoc ];
      · rw [ Nat.le_div_iff_mul_le ];
        · convert Nat.mul_le_mul_left ( x.getLast?.getD 0 / x[x.length - ( j + 2 ) ] ) this using 1 ; ring_nf;
          · rw [ show 1 + ( x.length - ( 2 + j ) ) = x.length - ( 1 + j ) by omega ];
            rw [ List.getElem?_eq_getElem ];
            rw [ Option.getD_some ];
          · rw [ mul_left_comm, Nat.div_mul_cancel ( h_div _ <| by simp ) ];
        · exact h_pos _ ( by simp );
      · convert h_div _ _;
        grind;
    · omega

/-
The sequence `a_seq` is lacunary.
-/
theorem a_seq_is_lacunary : IsLacunary a_seq := by
  -- By definition of `a_seq`, we know that for all `n ≥ 1`, `(a_seq (n + 1)) / (a_seq n) ≥ 1.01`.
  have h_lacunary : ∀ n ≥ 1, (a_seq (n + 1) : ℝ) / (a_seq n) ≥ 1.01 := by
    -- By definition of `a_seq`, we know that for all `n`, `(a_seq (n + 1))` and `(a_seq n)` are elements of the same block `D k`.
    intro n hn
    have h_block : ∃ k ≥ 1, n + 1 ≤ (full_seq_list k).length ∧ n ≤ (full_seq_list k).length := by
      use n + 1;
      -- By definition of `full_seq_list`, we know that its length is at least `n + 1`.
      have h_length : ∀ k ≥ 1, (full_seq_list k).length ≥ k := by
        intro k hk
        induction' k with k ih
        aesop
        generalize_proofs at *;
        rcases k with ( _ | k ) <;> simp_all +arith +decide [ full_seq_list ];
        unfold D; simp +arith +decide [ simple_block_data ] ;
        linarith [ Nat.zero_le ( Nat.log 2 ( k + 2 ) ), Nat.zero_le ( ( get_params ( k + 2 ) ).2 ) ];
      grind;
    obtain ⟨ k, hk₁, hk₂, hk₃ ⟩ := h_block;
    -- By definition of `a_seq`, we know that for all `n`, `(a_seq (n + 1))` and `(a_seq n)` are elements of the same block `D k`, and the ratio between consecutive elements in `D k` is at least 1.01.
    have h_ratio : ∀ i, i + 1 < (full_seq_list k).length → ((full_seq_list k).get! (i + 1) : ℝ) / ((full_seq_list k).get! i) ≥ 1.01 := by
      intro i hi; have := full_seq_valid k hk₁; have := this.2.2.1 i hi; norm_num at * ; aesop;
    convert h_ratio ( n - 1 ) _ using 1;
    · rw [ a_seq_eq_get, a_seq_eq_get ];
      any_goals omega;
      cases n <;> aesop;
    · omega;
  exact ⟨ 1.01, by norm_num, fun i hi => h_lacunary i hi ⟩

/-
The first term of `a_seq` is 1.
-/
lemma a_seq_one : a_seq 1 = 1 := by
  simp [a_seq]
  -- 'split' will generate two goals. 
  -- We use 'next' to name the hypothesis 'h' in each branch.
  split
  · next h => 
    -- Case: 1 - 1 < (full_seq_list 3).length
    -- We need to simplify full_seq_list enough to show the 0th element is 1
    simp [full_seq_list]
  · next h =>
    -- Case: ¬(1 - 1 < (full_seq_list 3).length)
    -- This hypothesis 'h' is what we simplify 'at'
    simp [full_seq_list] at h

/-
The ratio of consecutive terms in `a_seq` is at most 2.
-/
lemma a_seq_ratio_le_2 : ∀ n ≥ 1, (a_seq (n + 1) : ℝ) / a_seq n ≤ 2 := by
  -- Let $n \ge 1$. Consider $L = \text{full\_seq\_list} (n+2)$.
  intro n hn
  set L := full_seq_list (n + 2) with hL;
  -- By `full_seq_valid`, $L$ is a `ValidPrefix`, so it satisfies `HasGrowth`.
  have h_growth : HasGrowth L := by
    exact valid_prefix_growth _ <| full_seq_valid _ <| Nat.le_add_left _ _;
  -- The length of $L$ is at least $n+2$, so indices $n-1$ and $n$ are valid.
  have h_len : n + 2 ≤ L.length := by
    -- By definition of `full_seq_list`, we know that `full_seq_list (n + 2)` has length at least `n + 2`.
    have h_len : ∀ k ≥ 1, (full_seq_list k).length ≥ k := by
      intro k hk;
      -- We proceed by induction on $k$.
      induction' k with k ih;
      · contradiction;
      · rcases k with ( _ | k ) <;> simp_all +arith +decide [ full_seq_list ];
        unfold D; norm_num [ simple_block_data ] ;
        linarith [ Nat.zero_le ( Nat.log 2 ( k + 2 ) ), Nat.zero_le ( ( get_params ( k + 2 ) ).2 ) ];
    grind;
  -- By construction of `a_seq`, `a_seq n` is the element at index $n-1$ of $L$, and `a_seq (n+1)` is the element at index $n$ of $L$.
  have h_an : a_seq n = L.get! (n - 1) := by
    convert a_seq_eq_get n ( n + 2 ) hn _;
    grind
  have h_an1 : a_seq (n + 1) = L.get! n := by
    convert a_seq_eq_get ( n + 1 ) ( n + 2 ) ( Nat.succ_pos _ ) _ using 1;
    exact lt_of_lt_of_le ( by omega ) h_len;
  have := h_growth ( n - 1 ) ?_ <;> rcases n with ( _ | _ | n ) <;> norm_num at *;
  · aesop;
  · aesop;
  · grind;
  · linarith

/-
The n-th term of `a_seq` is at most `2^(n-1)`.
-/
theorem a_seq_le_pow2 (n : ℕ) (hn : n ≥ 1) : a_seq n ≤ 2^(n-1) := by
  -- By induction on $n$, we can show that $a_n \leq 2^{n-1}$ for all $n \geq 1$.
  induction' n with n ih;
  · contradiction;
  · by_cases hn : n ≥ 1 <;> simp_all +decide;
    · have h_ratio : (a_seq (n + 1) : ℝ) / a_seq n ≤ 2 := by
        exact a_seq_ratio_le_2 n hn
      have h_pos : 0 < a_seq n := by
        -- Since `a_seq` is lacunary, the ratio of consecutive terms is at least 1.
        have h_ratio_ge_one : ∀ n ≥ 1, (a_seq (n + 1) : ℝ) / a_seq n ≥ 1 := by
          intro n hn; have := a_seq_is_lacunary; obtain ⟨ lambda_val, hlambda_val₁, hlambda_val₂ ⟩ := this; exact le_trans ( by linarith ) ( hlambda_val₂ n hn ) ;
        contrapose! h_ratio_ge_one;
        use n;
        exact ⟨ hn, lt_of_le_of_lt ( div_nonpos_of_nonneg_of_nonpos ( mod_cast by
          unfold a_seq; aesop; ) ( mod_cast h_ratio_ge_one ) ) ( by norm_num ) ⟩
      have h_div : a_seq (n + 1) ≤ 2 * a_seq n := by
        rw [ div_le_iff₀ ] at h_ratio <;> norm_cast at *
      have h_final : a_seq (n + 1) ≤ 2 ^ n := by
        cases n <;> norm_num [ pow_succ' ] at * ; linarith
      exact h_final;
    · exact a_seq_one.le

/-
The sum of reciprocals of elements in a subset $T$ of $L$ is equal to the sum of the dual elements divided by the last element of $L$.
-/
lemma sum_recip_eq_sum_dual_div_last (L : List ℕ) (T : Finset ℕ) (hT : T ⊆ L.toFinset) (h_div : ∀ x ∈ L, x ∣ L.getLast!) (h_pos : ∀ x ∈ L, x > 0) :
  ∑ x ∈ T, (1:ℚ)/x = (∑ x ∈ T, (L.getLast! / x : ℕ)) / L.getLast! := by
    rw [ Nat.cast_sum, Finset.sum_div _ _ _ ];
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ Nat.cast_div ( h_div x ( by simpa using hT hx ) ) ] <;> norm_num [ ne_of_gt ( h_pos x ( by simpa using hT hx ) ) ];
    rw [ div_right_comm, div_self ] ; aesop;
    have h_last_pos : 0 < L.getLast! := by
      induction L using List.reverseRecOn <;> aesop;
    cases L <;> aesop

/-
The set of reciprocal sums of `L` is a subset of the set of reachable sums of the dual sequence scaled by `1/L.getLast!`.
-/
lemma reciprocal_sums_subset_scaled_dual_sums (L : List ℕ) (h_sorted : L.Sorted (· < ·)) (h_pos : ∀ x ∈ L, x > 0) (h_div : ∀ x ∈ L, x ∣ L.getLast!) :
  { s : ℚ | ∃ T : Finset ℕ, T ⊆ L.toFinset ∧ s = ∑ x ∈ T, (1:ℚ)/x } ⊆
  { q : ℚ | ∃ u ∈ reachable_sums (L.map (fun x => L.getLast! / x)), q = (u : ℚ) / L.getLast! } := by
    intro s hs
    obtain ⟨T, hT_sub, rfl⟩ := hs
    have h_sum_recip : ∑ x ∈ T, (1 : ℚ) / x = (∑ x ∈ T, (L.getLast! / x : ℕ)) / L.getLast! := by
      exact sum_recip_eq_sum_dual_div_last L T hT_sub h_div h_pos;
    have h_sum_recip_dual : ∑ x ∈ T, (L.getLast! / x : ℕ) ∈ reachable_sums (List.map (fun x => L.getLast! / x) L) := by
      -- Since $T$ is a subset of $L$, we can construct a sublist of $L$ whose elements are precisely those in $T$.
      obtain ⟨sublist, hsublist⟩ : ∃ sublist : List ℕ, sublist.Sublist L ∧ sublist.toFinset = T := by
        use List.filter (fun x => x ∈ T) L;
        simp +zetaDelta at *;
        grind;
      use sublist.map (fun x => L.getLast! / x);
      rw [ ← hsublist.2, List.sum_toFinset ];
      · exact ⟨ hsublist.1.map _, rfl ⟩;
      · exact h_sorted.nodup.sublist hsublist.1;
    exact ⟨ _, h_sum_recip_dual, h_sum_recip ⟩

/-
The set of reachable sums of the dual sequence scaled by `1/L.getLast!` is a subset of the set of reciprocal sums of `L`.
-/
lemma scaled_dual_sums_subset_reciprocal_sums (L : List ℕ) (h_sorted : L.Sorted (· < ·)) (h_pos : ∀ x ∈ L, x > 0) (h_div : ∀ x ∈ L, x ∣ L.getLast!) :
  { q : ℚ | ∃ u ∈ reachable_sums (L.map (fun x => L.getLast! / x)), q = (u : ℚ) / L.getLast! } ⊆
  { s : ℚ | ∃ T : Finset ℕ, T ⊆ L.toFinset ∧ s = ∑ x ∈ T, (1:ℚ)/x } := by
    rintro q ⟨ u, ⟨ T, hT₁, rfl ⟩, rfl ⟩;
    -- Since $T$ is a sublist of $L.map (fun x => L.getLast! / x)$, there exists a sublist $S$ of $L$ such that $T = S.map (fun x => L.getLast! / x)$.
    obtain ⟨ S, hS₁, hS₂ ⟩ : ∃ S : List ℕ, S.Sublist L ∧ T = S.map (fun x => L.getLast! / x) := by
      grind;
    -- Since $S$ is a sublist of $L$, the sum of the reciprocals of the elements in $S$ is equal to the sum of the reciprocals of the elements in $T$ divided by $L.getLast!$.
    have h_sum_recip : ∑ x ∈ S.toFinset, (1 / x : ℚ) = (List.map (fun x => L.getLast! / x) S).sum / L.getLast! := by
      convert sum_recip_eq_sum_dual_div_last L ( S.toFinset ) _ _ _ using 1;
      · rw [ List.sum_toFinset ];
        exact h_sorted.nodup.sublist hS₁;
      · exact fun x hx => List.mem_toFinset.mpr ( hS₁.subset ( List.mem_toFinset.mp hx ) );
      · assumption;
      · assumption;
    exact ⟨ S.toFinset, fun x hx => by have := hS₁.subset ( List.mem_toFinset.mp hx ) ; aesop, by aesop ⟩

/-
The set of reciprocal sums of `L` is equal to the set of reachable sums of the dual sequence scaled by `1/L.getLast!`.
-/
lemma reciprocal_sums_eq_scaled_dual_sums (L : List ℕ) (h_sorted : L.Sorted (· < ·)) (h_pos : ∀ x ∈ L, x > 0) (h_div : ∀ x ∈ L, x ∣ L.getLast!) :
  { s : ℚ | ∃ T : Finset ℕ, T ⊆ L.toFinset ∧ s = ∑ x ∈ T, (1:ℚ)/x } =
  { q : ℚ | ∃ u ∈ reachable_sums (L.map (fun x => L.getLast! / x)), q = (u : ℚ) / L.getLast! } := by
    apply Set.eq_of_subset_of_subset;
    · exact fun s hs => by rcases hs with ⟨ T, hT₁, rfl ⟩ ; exact reciprocal_sums_subset_scaled_dual_sums L h_sorted h_pos h_div ⟨ T, hT₁, rfl ⟩ ;
    · convert scaled_dual_sums_subset_reciprocal_sums L h_sorted h_pos h_div using 1

/-
The sum of the dual sequence divided by the last element is equal to the sum of reciprocals.
-/
lemma sum_dual_div_last_eq_sum_recip (L : List ℕ) (h_pos : ∀ x ∈ L, x > 0) (h_div : ∀ x ∈ L, x ∣ L.getLast!) :
  (List.map (fun x => L.getLast! / x) L).sum / (L.getLast! : ℚ) = (L.map (fun x => (1:ℚ)/x)).sum := by
    induction L <;> simp_all +decide;
    rename_i k hk ih; specialize ih ( fun x hx => ?_ ) ; simp_all +decide [List.getLast?] ;
    · cases hk <;> aesop;
    · by_cases hk0 : hk = [] <;> simp_all +decide [ add_div ];
      · norm_num [ h_pos.ne' ];
      · simp_all +decide [ List.getLast? ];
        convert congr_arg₂ ( · + · ) _ ih using 1;
        congr! 1;
        · cases hk <;> aesop;
        · rw [ div_right_comm, div_self ] ; aesop;
          exact Nat.cast_ne_zero.mpr ( ne_of_gt ( h_pos.2 _ ( List.getLast_mem hk0 ) ) )

/-
The reachable sums of the dual sequence form a complete interval from 0 to the total sum.
-/
lemma reachable_sums_dual_eq_interval (L : List ℕ) (h_nonempty : L ≠ [])
  (h_pos : ∀ x ∈ L, x > 0)
  (h_div : ∀ x ∈ L, x ∣ L.getLast!)
  (h_ratio : ∀ i, i + 1 < L.length → (L.get! (i + 1) : ℝ) / L.get! i ≤ 2) :
  reachable_sums (L.map (fun x => L.getLast! / x)) = { u | u ≤ (L.map (fun x => L.getLast! / x)).sum } := by
    -- By `inv_scaled_reverse_ratio`, we know that the reversed dual sequence starts with 1 and satisfies the ratio condition $\le 2$.
    have h_rev_dual_ratio : let b := (L.map (fun x => L.getLast! / x)).reverse;
      b.head? = some 1 ∧
      (∀ i, i + 1 < b.length → b.get! (i + 1) ≤ 2 * b.get! i) := by
        convert inv_scaled_reverse_ratio L _ _ _ _;
        · exact List.length_pos_iff.mpr h_nonempty;
        · assumption;
        · convert h_ratio using 1;
        · assumption;
    -- By `ratio_le_2_implies_growth`, we know that the reversed dual sequence satisfies the growth condition.
    have h_rev_dual_growth : GrowthCondition ((L.map (fun x => L.getLast! / x)).reverse) := by
      apply ratio_le_2_implies_growth; aesop;
      aesop;
    -- By `reachability_integers_of_growth`, we know that the reachable sums of the reversed dual sequence form a complete interval from 0 to the total sum.
    have h_rev_dual_reachable : reachable_sums ((L.map (fun x => L.getLast! / x)).reverse) = { u | u ≤ ((L.map (fun x => L.getLast! / x)).reverse).sum } := by
      apply reachability_integers_of_growth;
      · exact h_rev_dual_ratio.1;
      · assumption;
    convert h_rev_dual_reachable using 1;
    · exact Eq.symm (reachable_sums_reverse (List.map (fun x => L.getLast! / x) L));
    · rw [ List.sum_reverse ]

/-
The set of reciprocal sums of a finite sequence satisfying the divisibility and growth conditions contains all rationals of the form $u/x_N$ up to the total sum.
-/
lemma finite_reach (L : List ℕ) (h_nonempty : L ≠ []) (h_sorted : L.Sorted (· < ·)) (h_pos : ∀ x ∈ L, x > 0)
  (h_div : ∀ x ∈ L, x ∣ L.getLast!)
  (h_ratio : ∀ i, i + 1 < L.length → (L.get! (i + 1) : ℝ) / L.get! i ≤ 2) :
  { s : ℚ | ∃ T : Finset ℕ, T ⊆ L.toFinset ∧ s = ∑ x ∈ T, (1:ℚ)/x } =
  { q : ℚ | ∃ u : ℕ, q = u / L.getLast! ∧ q ≤ (L.map (fun x => (1:ℚ)/x)).sum } := by
    -- By Lemma 25, the set of reciprocal sums of `L` is equal to the set of reachable sums of the dual sequence scaled by `1/L.getLast!`.
    have h_reciprocal_sums_eq_scaled_dual_sums : {s : ℚ | ∃ T : Finset ℕ, T ⊆ L.toFinset ∧ s = ∑ x ∈ T, (1 : ℚ) / x} = {q : ℚ | ∃ u ∈ reachable_sums (L.map (fun x => L.getLast! / x)), q = (u : ℚ) / L.getLast!} := by
      exact reciprocal_sums_eq_scaled_dual_sums L h_sorted h_pos h_div;
    -- By Lemma 24, the reachable sums of the dual sequence form a complete interval from 0 to the total sum.
    have h_reachable_sums_dual_eq_interval : reachable_sums (L.map (fun x => L.getLast! / x)) = {u | u ≤ (L.map (fun x => L.getLast! / x)).sum} := by
      apply reachable_sums_dual_eq_interval L h_nonempty h_pos h_div h_ratio;
    -- By Lemma 23, the sum of the dual sequence divided by the last element is equal to the sum of reciprocals.
    have h_sum_dual_div_last_eq_sum_recip : (L.map (fun x => L.getLast! / x)).sum / (L.getLast! : ℚ) = (L.map (fun x => (1 : ℚ) / x)).sum := by
      convert sum_dual_div_last_eq_sum_recip L h_pos h_div using 1;
    simp_all +decide [ Set.ext_iff ];
    intro x; constructor <;> intro hx;
    · obtain ⟨ u, hu, rfl ⟩ := hx;
      refine' ⟨ ⟨ u, rfl ⟩, _ ⟩;
      rw [ ← h_sum_dual_div_last_eq_sum_recip ];
      gcongr;
      convert Nat.cast_le.mpr hu using 1;
      · induction L <;> aesop;
      · infer_instance;
      · infer_instance;
      · infer_instance;
    · rcases hx with ⟨ ⟨ u, rfl ⟩, hu ⟩;
      refine' ⟨ u, _, _ ⟩;
      · rw [ ← h_sum_dual_div_last_eq_sum_recip ] at hu;
        rw [ div_le_div_iff_of_pos_right ] at hu <;> norm_cast at *;
        · rw [ ← @Nat.cast_le ℚ ] ; aesop;
        · induction L using List.reverseRecOn <;> aesop;
      · norm_cast

/-
The set of reciprocal sums of a finite sequence satisfying the divisibility and growth conditions contains all rationals of the form $u/x_N$ up to the total sum.
-/
lemma finite_reach_thm (L : List ℕ) (h_nonempty : L ≠ []) (h_sorted : L.Sorted (· < ·)) (h_pos : ∀ x ∈ L, x > 0)
  (h_div : ∀ x ∈ L, x ∣ L.getLast!)
  (h_ratio : ∀ i, i + 1 < L.length → (L.get! (i + 1) : ℝ) / L.get! i ≤ 2) :
  { s : ℚ | ∃ T : Finset ℕ, T ⊆ L.toFinset ∧ s = ∑ x ∈ T, (1:ℚ)/x } =
  { q : ℚ | ∃ u : ℕ, q = u / L.getLast! ∧ q ≤ (L.map (fun x => (1:ℚ)/x)).sum } := by
    convert finite_reach L h_nonempty h_sorted h_pos h_div h_ratio using 1

/-
The sequence `full_seq_list k` is strictly increasing and consists of positive integers.
-/
lemma full_seq_properties (k : ℕ) (hk : k ≥ 1) :
  (full_seq_list k).Sorted (· < ·) ∧
  (∀ x ∈ full_seq_list k, x > 0) := by
    -- Prove that `full_seq_list k` is strictly increasing and consists of positive integers.
    have h_sorted : List.Sorted (· < ·) (full_seq_list k) := by
      -- By definition of `full_seq_list`, it is constructed by appending blocks that satisfy the growth condition.
      have h_growth : ∀ k ≥ 1, HasGrowth (full_seq_list k) := by
        exact fun k hk => valid_prefix_growth _ ( full_seq_valid k hk ) |> fun h => by simpa using h;
      -- Since the ratios are all at least 1.01, each element is strictly greater than the previous one.
      have h_strict_mono : ∀ k ≥ 1, ∀ i < (full_seq_list k).length - 1, (full_seq_list k).get! i < (full_seq_list k).get! (i + 1) := by
        intros k hk i hi
        have h_ratio : (101 : ℝ) / 100 ≤ (full_seq_list k).get! (i + 1) / (full_seq_list k).get! i := by
          exact h_growth k hk i ( by omega ) |>.1;
        rw [ div_le_div_iff₀ ] at h_ratio <;> norm_cast at *;
        · linarith [ show 0 < ( full_seq_list k |> List.get! ) i from Nat.pos_of_dvd_of_pos ( show ( full_seq_list k |> List.get! ) i ∣ ( full_seq_list k |> List.getLast! ) from by
                                                                                                have h_div : ∀ k ≥ 1, ∀ x ∈ full_seq_list k, x ∣ (full_seq_list k).getLast! := by
                                                                                                  intros k hk x hx;
                                                                                                  have := full_seq_valid k hk;
                                                                                                  exact this.2.2.2 x hx;
                                                                                                convert h_div k hk _ _;
                                                                                                simp +decide [hi.trans_le
                                                                                                      (Nat.sub_le
                                                                                                        _
                                                                                                        _)] ) ( show 0 < ( full_seq_list k |> List.getLast! ) from by
                                                                                                                                                                                                have := full_seq_valid k hk;
                                                                                                                                                                                                exact
                                                                                                                                                                                                  valid_prefix_last_pos
                                                                                                                                                                                                    (full_seq_list
                                                                                                                                                                                                      k)
                                                                                                                                                                                                    this ) ];
        · contrapose! h_ratio; aesop;
      refine' List.pairwise_iff_get.mpr _;
      intro i j hij;
      induction' j with j hj generalizing i;
      induction' j with j ih generalizing i;
      · tauto;
      · rcases eq_or_lt_of_le ( show i ≤ ⟨ j, by linarith ⟩ from Nat.le_of_lt_succ hij ) with rfl | hi <;> simp_all +decide;
        · convert h_strict_mono k hk j ( Nat.lt_pred_iff.mpr hj ) using 1;
          · grind;
          · rw [ List.getElem?_eq_getElem ];
            rw [ Option.getD_some ];
        · refine' lt_trans ( ih _ _ hi ) _;
          convert h_strict_mono k hk j ( Nat.lt_pred_iff.mpr hj ) using 1;
          · grind;
          · grind;
    have h_pos : ∀ x ∈ full_seq_list k, x > 0 := by
      have h_valid : ValidPrefix (full_seq_list k) := by
        exact full_seq_valid k hk
      exact fun x hx => Nat.pos_of_dvd_of_pos ( h_valid.2.2.2 x hx ) ( valid_prefix_last_pos _ h_valid );
    exact ⟨ h_sorted, h_pos ⟩

/-
The partial sum of reciprocals of the sequence up to block $k$ is at least $2 - 1/2^{N-1}$, where $N$ is the length of the sequence.
-/
def partial_sum (k : ℕ) : ℚ := ((full_seq_list k).map (fun x => (1:ℚ)/x)).sum

lemma partial_sum_ge (k : ℕ) (hk : k ≥ 1) : partial_sum k ≥ 2 - (1:ℚ)/(2^((full_seq_list k).length - 1)) := by
  -- Apply the lemma that states the partial sum is at least the difference of the geometric series sum formula.
  have h_partial_sum_ge : partial_sum k ≥ ∑ i ∈ Finset.range (full_seq_list k).length, (1 : ℚ) / (2^i) := by
    have h_partial_sum_ge : ∀ i ∈ Finset.range (full_seq_list k).length, (1 : ℚ) / (full_seq_list k).get! i ≥ (1 : ℚ) / (2^i) := by
      intro i hi;
      gcongr ; norm_cast;
      · have := full_seq_properties k hk; aesop;
      · convert a_seq_le_pow2 ( i + 1 ) ( by linarith ) using 1;
        norm_num +zetaDelta at *;
        rw [ a_seq_eq_get ];
        norm_num +zetaDelta at *;
        norm_cast;
        · linarith;
        · exact hi;
    refine' le_trans ( Finset.sum_le_sum h_partial_sum_ge ) _;
    convert rfl.le using 1;
    unfold partial_sum;
    induction ( full_seq_list k ) <;> simp_all +decide [ Finset.sum_range_succ' ];
    ring;
  convert h_partial_sum_ge using 1 ; ring_nf;
  rw [ geom_sum_eq ] <;> ring_nf ; norm_num;
  · cases h : List.length ( full_seq_list k ) <;> simp_all +decide [pow_succ];
    exact absurd h ( full_seq_list_nonempty k hk );
  · norm_num

/-
Any reciprocal sum of a subset of `full_seq_list k` is in the set `P` of the sequence `a_seq`.
-/
lemma finite_sums_in_P (k : ℕ) (hk : k ≥ 1) :
  ∀ s : ℚ, (∃ T : Finset ℕ, T ⊆ (full_seq_list k).toFinset ∧ s = ∑ x ∈ T, (1:ℚ)/x) →
  (s : ℝ) ∈ P (fun i => 1 / (a_seq i : ℝ)) := by
    intro s hs
    obtain ⟨T, hT_sub, hs_eq⟩ := hs
    have h_finset : ∀ x ∈ T, ∃ i, x = a_seq i := by
      intro x hx
      have hx_seq : x ∈ (full_seq_list k).toFinset := by
        exact hT_sub hx;
      -- By definition of `a_seq`, every element in `full_seq_list k` is of the form `a_seq i` for some `i`.
      have hx_seq_def : ∀ x ∈ (full_seq_list k).toFinset, ∃ i, x = a_seq i := by
        intro x hx_seq
        have hx_seq_def : x ∈ List.map (fun i => a_seq (i + 1)) (List.range (full_seq_list k).length) := by
          have hx_seq_def : ∀ i < (full_seq_list k).length, (full_seq_list k).get! i = a_seq (i + 1) := by
            intro i hi;
            rw [ a_seq_eq_get ];
            exacts [ rfl, Nat.succ_pos _, hi ];
          norm_num +zetaDelta at *;
          obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hx_seq; use i; aesop;
        aesop;
      exact hx_seq_def x hx_seq;
    choose! f hf using h_finset;
    use T.image f;
    rw [ Finset.sum_image ] <;> norm_num [ hs_eq ];
    · exact Finset.sum_congr rfl fun x hx => hf x hx ▸ rfl;
    · intro x hx y hy; have := hf x hx; have := hf y hy; simp +decide [ ← this ] at *;
      grind

/-
For any rational $q < 2$ and positive integer $v$, there exists a block index $k$ divisible by $v$ such that the partial sum up to block $k$ is at least $q$.
-/
lemma exists_valid_k (q : ℚ) (hq : q < 2) (v : ℕ) (hv : v > 0) :
  ∃ k ≥ 1, v ∣ k ∧ q ≤ partial_sum k := by
    -- Since $q < 2$, we have $2 - q > 0$. Choose $N$ large enough such that $1/2^{N-1} \le 2 - q$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / (2^N : ℚ) ≤ 2 - q ∧ N ≥ 1 := by
      -- By the Archimedean property, there exists an $N$ such that $1 / 2^N \leq 2 - q$.
      have h_archimedean : ∃ N : ℕ, (1 : ℚ) / 2^N ≤ 2 - q := by
        -- By the Archimedean property, there exists an $N$ such that $1 / 2^N < 2 - q$.
        have h_archimedean : ∃ N : ℕ, (1 : ℚ) / 2^N < 2 - q := by
          simpa using exists_pow_lt_of_lt_one ( sub_pos.mpr hq ) one_half_lt_one;
        exact ⟨ h_archimedean.choose, le_of_lt h_archimedean.choose_spec ⟩;
      exact ⟨ h_archimedean.choose + 1, le_trans ( by gcongr <;> norm_num ) h_archimedean.choose_spec, Nat.succ_pos _ ⟩;
    -- Choose $k$ such that $(full\_seq\_list k).length \ge N$ and $v \mid k$.
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k ≥ 1, v ∣ k ∧ (full_seq_list k).length ≥ N + 1 := by
      use v * (N + 1);
      -- By definition of `full_seq_list`, we know that its length is at least `k`.
      have h_length : ∀ k ≥ 1, (full_seq_list k).length ≥ k := by
        intro k hk;
        -- By definition of `full_seq_list`, we know that its length is at least `k` because each step adds at least one element.
        induction' k with k ih;
        · contradiction;
        · rcases k with ( _ | k ) <;> simp_all +decide [ full_seq_list ];
          refine' le_trans _ ( add_le_add ih le_rfl );
          unfold D; norm_num;
          unfold simple_block_data; norm_num;
          exact Nat.one_le_iff_ne_zero.mpr ( by positivity );
      exact ⟨ Nat.mul_pos hv ( Nat.succ_pos _ ), dvd_mul_right _ _, le_trans ( by nlinarith ) ( h_length _ ( Nat.mul_pos hv ( Nat.succ_pos _ ) ) ) ⟩;
    refine' ⟨ k, hk₁, hk₂.1, _ ⟩;
    have := partial_sum_ge k hk₁;
    exact le_trans ( by linarith [ show ( 1 : ℚ ) / 2 ^ ( ( full_seq_list k ).length - 1 ) ≤ 1 / 2 ^ N by exact one_div_le_one_div_of_le ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_sub_one_of_lt hk₂.2 ) ) ] ) this

/-
The sequence `a_seq` represents all rational numbers in the interval $(0, 2)$.
-/
theorem main_result_a_seq : ∀ q : ℚ, 0 < q → q < 2 → (q : ℝ) ∈ P (fun i => 1 / (a_seq i : ℝ)) := by
  intro q hq_pos hq_lt_two
  obtain ⟨k, hk_ge_one, hk_div_v, hk_partial_sum⟩ : ∃ k ≥ 1, q.den ∣ k ∧ q ≤ partial_sum k := by
    exact exists_valid_k q hq_lt_two q.den q.pos;
  -- By `finite_reach_thm`, the set of reciprocal sums of `full_seq_list k` equals `{ q' | ∃ U, q' = U / L.getLast! ∧ q' ≤ partial_sum k }`.
  have h_reciprocal_sums : { s : ℚ | ∃ T : Finset ℕ, T ⊆ (full_seq_list k).toFinset ∧ s = ∑ x ∈ T, (1:ℚ)/x } = { q' : ℚ | ∃ U : ℕ, q' = U / (full_seq_list k).getLast! ∧ q' ≤ partial_sum k } := by
    convert finite_reach_thm ( full_seq_list k ) _ _ _ _ _ using 1;
    · exact full_seq_list_nonempty k hk_ge_one;
    · exact full_seq_properties k hk_ge_one |>.1;
    · exact full_seq_properties k hk_ge_one |>.2;
    · have := full_seq_valid k hk_ge_one; unfold ValidPrefix at this; aesop;
    · have := full_seq_valid k hk_ge_one; unfold ValidPrefix at this; aesop;
  -- Since $q$ is in the set of reciprocal sums of $full_seq_list k$, by `finite_sums_in_P`, $q$ is in $P((1/a_i))$.
  have h_q_in_P : (q : ℚ) ∈ { s : ℚ | ∃ T : Finset ℕ, T ⊆ (full_seq_list k).toFinset ∧ s = ∑ x ∈ T, (1:ℚ)/x } := by
    refine h_reciprocal_sums.symm.subset ⟨ q.num.natAbs * ( ( full_seq_list k ).getLast! / q.den ), ?_, ?_ ⟩;
    · rw [ Nat.cast_mul, Nat.cast_div ];
      · field_simp;
        rw [ mul_div_cancel_right₀ _ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by
          exact ne_of_gt <| valid_prefix_last_pos _ <| full_seq_valid _ hk_ge_one ) ];
        simp +decide [abs_of_pos, hq_pos];
      · exact dvd_trans hk_div_v ( full_seq_divisible k hk_ge_one );
      · exact Nat.cast_ne_zero.mpr q.pos.ne';
    · exact hk_partial_sum;
  have := finite_sums_in_P k hk_ge_one q h_q_in_P; aesop;

/-
The terms of `a_seq` are positive for $n \ge 1$.
-/
lemma a_seq_pos (n : ℕ) (hn : n ≥ 1) : a_seq n > 0 := by
  unfold a_seq;
  field_simp;
  split_ifs <;> norm_cast ; aesop;
  · exact full_seq_properties ( n + 2 ) ( by linarith ) |>.2 _ ( by simp );
  · -- By definition of `full_seq_list`, its length is at least `n + 2`.
    have h_len : ∀ k ≥ 1, (full_seq_list k).length ≥ k := by
      intro k hk; induction' k with k ih <;> simp_all +arith +decide ;
      rcases k with ( _ | k ) <;> simp_all +arith +decide [ full_seq_list ];
      refine' le_trans _ ( Nat.add_le_add_left ( Nat.sub_pos_of_lt _ ) _ );
      · linarith;
      · unfold D; simp +arith +decide;
        unfold simple_block_data; simp +arith +decide;
    grind

/-
Shifted sequence of a_seq to avoid the zero index.
-/
def a_shifted (n : ℕ) : ℕ := a_seq (n + 1)

/-
The shifted sequence consists of positive integers.
-/
lemma a_shifted_pos (n : ℕ) : a_shifted n > 0 := by
  exact a_seq_pos _ ( Nat.succ_pos _ )

lemma P_a_seq_eq_P_a_shifted : P (fun i => 1 / (a_seq i : ℝ)) = P (fun i => 1 / (a_shifted i : ℝ)) := by
  apply Set.ext;
  intro x;
  constructor <;> rintro ⟨ T, rfl ⟩;
  · -- By definition of $a_shifted$, we know that $a_shifted i = a_seq (i + 1)$. Therefore, we can rewrite the sum over $T$ as a sum over $T' = \{i - 1 \mid i \in T, i \neq 0\}$.
    obtain ⟨T', hT'⟩ : ∃ T' : Finset ℕ, T = T'.image (fun i => i + 1) ∪ (if 0 ∈ T then {0} else ∅) := by
      use T.image (fun i => i - 1) |> Finset.filter (fun i => i + 1 ∈ T);
      ext ( _ | i ) <;> aesop;
    split_ifs at hT' <;> simp_all +decide [Finset.sum_image];
    · exact ⟨ T', rfl ⟩;
    · exact ⟨ T', rfl ⟩;
  · use T.image ( fun i => i + 1 );
    rw [ Finset.sum_image ] <;> aesop

/-
There exists a lacunary sequence of positive integers and an interval $(\alpha, \beta)$ such that the set of reciprocal sums contains all rationals in the interval.
-/
theorem maintheorem : ∃ (a : ℕ → ℕ) (α β : ℝ),
  (∀ n, a n > 0) ∧
  (∃ lambda_val > 1, ∀ i, (a (i + 1) : ℝ) / a i ≥ lambda_val) ∧
  0 ≤ α ∧ α < β ∧
  ∀ q : ℚ, α < q → q < β → (q : ℝ) ∈ P (fun i => 1 / (a i : ℝ)) := by
    -- Choose the sequence `a` to be `a_shifted`, and the interval `(0, 2)`.
    use a_shifted, 0, 2;
    refine' ⟨ _, _, _, _, _ ⟩;
    · exact fun n => a_shifted_pos n;
    · exact a_seq_is_lacunary |> fun ⟨ lambda, hlambda₁, hlambda₂ ⟩ => ⟨ lambda, hlambda₁, fun i => hlambda₂ ( i + 1 ) ( by linarith ) ⟩;
    · norm_num;
    · grind;
    · intro q hq₁ hq₂;
      convert main_result_a_seq q ( by exact_mod_cast hq₁ ) ( by exact_mod_cast hq₂ ) using 1;
      exact Eq.symm P_a_seq_eq_P_a_shifted

theorem erdos_355 :
    ∃ A : ℕ → ℕ, IsLacunary A ∧ ∃ u v : ℝ, u < v ∧ ∀ q : ℚ, ↑q ∈ Set.Ioo u v →
      q ∈ {∑ a ∈ A', (1 / a : ℚ) | (A' : Finset ℕ) (_ : A'.toSet ⊆ Set.range A)} := by
  -- Apply the main theorem to obtain the lacunary sequence A and the interval (α, β).
  obtain ⟨A, hA_lacunary, α, β, hαβ⟩ := maintheorem;
  -- Use the existence of lambda_val from hαβ.left to conclude that A is lacunary.
  use A, by
    -- By definition of IsLacunary, we need to show that there exists a lambda_val > 1 such that for all i, (A (i + 1) : ℝ) / A i ≥ lambda_val.
    obtain ⟨lambda_val, hlambda_val_gt1, hlambda_val⟩ := hαβ.left;
    use lambda_val;
    aesop, hA_lacunary, α, by
    -- By definition of $hαβ$, we know that $hA_lacunary < α$.
    apply hαβ.right.right.left
  generalize_proofs at *;
  -- Apply the hypothesis `hαβ` to conclude the proof.
  intros q hq; exact (by
  -- By definition of $P$, there exists a finite subset $T$ of $\mathbb{N}$ such that $q = \sum_{i \in T} \frac{1}{A i}$.
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, (q : ℝ) = ∑ i ∈ T, (1 / (A i : ℝ)) := by
    exact hαβ.2.2.2 q hq.1 hq.2 |> fun ⟨ T, hT ⟩ => ⟨ T, by simpa using hT ⟩
  generalize_proofs at *; (
  -- Let $A'$ be the image of $T$ under $A$.
  use Finset.image A T; simp;
  -- Since $A$ is injective, the image of $T$ under $A$ is just a reordering of the elements in $T$.
  have h_inj : Function.Injective A := by
    -- Since $A$ is lacunary, we have $A (i + 1) > A i$ for all $i$.
    have h_increasing : ∀ i, A (i + 1) > A i := by
      -- Since $\lambda_val > 1$, we have $A (i + 1) \geq \lambda_val \cdot A i > A i$ for all $i$.
      intros i
      obtain ⟨lambda_val, hlambda_val_gt1, hlambda_val⟩ := hαβ.left
      have h_ratio : (A (i + 1) : ℝ) / (A i : ℝ) ≥ lambda_val := hlambda_val i
      have h_gt : (A (i + 1) : ℝ) > (A i : ℝ) := by
        exact_mod_cast ( by nlinarith [ show ( A i : ℝ ) > 0 from Nat.cast_pos.mpr ( β i ), show ( A ( i + 1 ) : ℝ ) > 0 from Nat.cast_pos.mpr ( β ( i + 1 ) ), div_mul_cancel₀ ( A ( i + 1 ) : ℝ ) ( show ( A i : ℝ ) ≠ 0 from Nat.cast_ne_zero.mpr ( ne_of_gt ( β i ) ) ) ] : ( A i : ℝ ) < A ( i + 1 ) ) ;
      exact_mod_cast h_gt
    generalize_proofs at *; (
    exact ( StrictMono.injective ( strictMono_nat_of_lt_succ h_increasing ) ))
  generalize_proofs at *; (
  rw [ Finset.sum_image <| by tauto ] ; norm_num [ ← @Rat.cast_inj ℝ, hT ] ;)))

  #print axioms maintheorem
  #print axioms erdos_355