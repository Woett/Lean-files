import Mathlib

/-!
# The Coin Setting-Aside Game: Optimal Strategy for p ≥ 1/2

A player starts with `n` coins, each independently landing heads with
probability `p`. Each round: toss all remaining coins, observe the outcome, set
aside at least one coin (permanently keeping its face value), and repeat until
all coins are set aside. The score is the total number of heads you end up with.
The goal is to maximize the expected score.

## Main result

Assume that you have n ≥ 3 remaining coins and, after you toss them all, j of
those turn up heads. Further assume that the probability of heads is p, with 1/2
≤ p < 1. It is then always optimal to follow one of these two strategies:

(A) Set aside exactly one coin, unless j = n, in which case you take all of them.
(B) Set aside exactly one coin, unless j = n or j = n-1. In both of these
cases you take all heads.

Moreover, there are two constants φ = (√5 - 1)/2 ≈ 0.618 and p_0 ≈
0.5495021777642, such that there are only three possibilities that can occur for
a given p ∈ [1/2, 1):

(1) For φ ≤ p < 1 it is optimal to follow strategy A for all n ≥ 3.
(2) For p_0 < p < φ there exists an absolute constant s'(p_0) > 0 and a positive integer

n(p) = ⌊ \frac{\log(p - p_0) + \log(s'(p_0))}{\log(p_0)} + o(1) ⌋

such that it is optimal to follow strategy A when n > n(p), but one should
switch to strategy B when the remaining number of coins becomes smaller than or
equal to n(p).
(3) For 1/2 ≤ p ≤ p_0 it is optimal to follow strategy B for all n ≥ 3.

W. van Doorn, On maximizing the number of heads when you need to set aside at
least one coin every round. arXiv:2406.14700 (2024).

Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) did the formalization.

Lean version: leanprover/lean4:v4.28.0
-/

set_option maxHeartbeats 1600000

open Finset BigOperators Filter

namespace CoinGame

/-! ### Binomial probability -/

noncomputable def binomProb (n : ℕ) (p : ℝ) (h : ℕ) : ℝ :=
  (n.choose h : ℝ) * p ^ h * (1 - p) ^ (n - h)

/-! ### The optimal value function -/

def bestHeadsAside (n h r : ℕ) : ℕ := min h (n - r)

noncomputable def v (p : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      ∑ h ∈ range (n + 2),
        binomProb (n + 1) p h *
        (Finset.univ : Finset (Fin (n + 1))).sup' ⟨0, Finset.mem_univ _⟩
          (fun r => (bestHeadsAside (n + 1) h r : ℝ) + v p r)

/-! ### Basic properties -/

lemma binomProb_nonneg (n : ℕ) (p : ℝ) (h : ℕ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ binomProb n p h := by
      exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp₀ _ ) ) ( pow_nonneg ( sub_nonneg.mpr hp₁ ) _ )

@[simp]
lemma v_zero (p : ℝ) : v p 0 = 0 := by unfold v; rfl

lemma v_one (p : ℝ) : v p 1 = p := by
  unfold v
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [binomProb, bestHeadsAside]

lemma binomProb_sum (n : ℕ) (p : ℝ) :
    ∑ h ∈ range (n + 1), binomProb n p h = 1 := by
  have := add_pow p (1 - p) n
  simpa [mul_assoc, mul_comm, mul_left_comm, binomProb] using this.symm

lemma v_nonneg (n : ℕ) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ v p n := by
  induction' n using Nat.case_strong_induction_on with n ih
  · simp
  · unfold v
    refine' Finset.sum_nonneg fun h hh => mul_nonneg (binomProb_nonneg _ _ _ hp₀ hp₁) _
    simp +zetaDelta at *
    exact ⟨0, add_nonneg (Nat.cast_nonneg _) (ih _ (Nat.zero_le _))⟩

lemma v_le_n (n : ℕ) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : v p n ≤ n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with (_ | n) <;> simp_all +decide [v]
  refine' le_trans (Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
    (Finset.sup'_le _ _ fun j hj => _) <| binomProb_nonneg _ _ _ hp₀ hp₁) _
  use fun _ => n + 1
  · refine' le_trans (add_le_add (Nat.cast_le.mpr <| min_le_right _ _)
      (ih _ <| Fin.is_le _)) _; norm_num
  · rw [← Finset.sum_mul _ _ _, binomProb_sum]; norm_num

lemma v_two (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : v p 2 = -p ^ 3 + 3 * p := by
  unfold CoinGame.v
  norm_num [range_add_one, Finset.sum_range_succ', Finset.sup'_insert, Finset.sup'_singleton]
  norm_num [Fin.univ_succ, bestHeadsAside]
  unfold binomProb; rw [v_one]; norm_num; ring_nf
  rw [max_eq_right, max_eq_right, max_eq_left] <;> nlinarith

noncomputable def s_n (p : ℝ) (n : ℕ) : ℝ := v p n - n + 1 - p

lemma v_step_lower_bound (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) :
    v p n + 1 - (1 - p) ^ (n + 1) ≤ v p (n + 1) := by
  rw [v]
  refine' le_trans _ (Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left
    (_ : _ ≤ _) (binomProb_nonneg _ _ _ hp₀ hp₁))
  case refine'_2 => exact fun h => min h 1 + v p n
  · have h_sum : ∑ h ∈ Finset.range (n + 2), binomProb (n + 1) p h * min h 1 =
        1 - (1 - p) ^ (n + 1) := by
      have h_sum : ∑ h ∈ Finset.range (n + 2), binomProb (n + 1) p h * (min h 1) =
          ∑ h ∈ Finset.range (n + 2), binomProb (n + 1) p h - binomProb (n + 1) p 0 := by
        norm_num [Finset.sum_range_succ']
      rw [h_sum, binomProb_sum]
      unfold binomProb; norm_num
    simp_all +decide [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul _ _ _]; rw [binomProb_sum]; ring_nf; norm_num
  · refine' le_trans _ (Finset.le_sup' _ <| Finset.mem_univ ⟨n, Nat.lt_succ_self _⟩)
    norm_num [bestHeadsAside]


/-! ### Monotonicity of v in n -/

lemma v_mono_n (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) : v p n ≤ v p (n + 1) := by
  have h1 := v_step_lower_bound p hp₀ hp₁ n
  have h2 : (1 - p) ^ (n + 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  linarith

/-! ### Sup' optimality lemmas -/

lemma bellman_opt_r_of_step_ge_one (p : ℝ) (hp₀ : 0 ≤ p)
    (m : ℕ) (hm : 1 ≤ m)
    (hstep : ∀ k, 2 ≤ k → k ≤ m → v p (k - 1) + 1 ≤ v p k) :
    ∀ (h : ℕ), 1 ≤ h → h ≤ m →
    ∀ (r : Fin (m + 1)), (bestHeadsAside (m + 1) h r : ℝ) + v p r ≤ 1 + v p m := by
  intro h hh₁ hh₂ r;
  have h_r_ge_1 : ∀ r : ℕ, 1 ≤ r → r ≤ m → v p r ≥ v p 1 + (r - 1) := by
    intro r hr₁ hr₂; induction hr₁ <;> norm_num at *;
    grind;
  by_cases hr : 1 ≤ r.val <;> simp_all +decide [ bestHeadsAside ];
  · have h_r_ge_1 : v p m ≥ v p r + (m - r.val) := by
      have h_r_ge_1 : ∀ k : ℕ, r.val ≤ k → k ≤ m → v p k ≥ v p r.val + (k - r.val) := by
        intro k hk₁ hk₂; induction hk₁ <;> norm_num at *;
        grind;
      exact h_r_ge_1 m ( Nat.le_of_lt_succ r.2 ) le_rfl;
    cases min_cases ( h : ℝ ) ( m + 1 - r ) <;> linarith [ show ( h : ℝ ) ≤ m by norm_cast ];
  · exact Or.inl ( by linarith [ show ( h : ℝ ) ≤ m by norm_cast, h_r_ge_1 m hm le_rfl, show ( v p 1 : ℝ ) = p by exact_mod_cast v_one p ] )

lemma bellman_sup_h_zero (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (m : ℕ) (_hm : 1 ≤ m) :
    (Finset.univ : Finset (Fin (m + 1))).sup' ⟨0, Finset.mem_univ _⟩
      (fun r => (bestHeadsAside (m + 1) 0 r : ℝ) + v p r) = v p m := by
  refine' le_antisymm _ _ <;> norm_num [ bestHeadsAside ];
  · intro b; exact (by
    exact monotone_nat_of_le_succ ( fun n => v_mono_n p hp₀ hp₁ n ) ( Fin.is_le b ));
  · exact ⟨ ⟨ m, by linarith ⟩, le_rfl ⟩

lemma bellman_sup_h_mid (p : ℝ) (hp₀ : 0 ≤ p)
    (m : ℕ) (hm : 1 ≤ m)
    (hstep : ∀ k, 2 ≤ k → k ≤ m → v p (k - 1) + 1 ≤ v p k) :
    ∀ (h : ℕ), 1 ≤ h → h ≤ m →
    (Finset.univ : Finset (Fin (m + 1))).sup' ⟨0, Finset.mem_univ _⟩
      (fun r => (bestHeadsAside (m + 1) h r : ℝ) + v p r) = 1 + v p m := by
  intros h hh₁ hh₂; refine' le_antisymm _ _;
  · exact Finset.sup'_le _ _ fun x hx => bellman_opt_r_of_step_ge_one p hp₀ m hm hstep h hh₁ hh₂ x;
  · refine' le_trans _ ( Finset.le_sup' _ <| Finset.mem_univ ⟨ m, by linarith ⟩ ) ; norm_num [ bestHeadsAside ];
    linarith

lemma bellman_sup_h_all (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (m : ℕ) :
    (Finset.univ : Finset (Fin (m + 1))).sup' ⟨0, Finset.mem_univ _⟩
      (fun r => (bestHeadsAside (m + 1) (m + 1) r : ℝ) + v p r) = ↑(m + 1) := by
  refine' le_antisymm _ _;
  · simp +decide [ bestHeadsAside ];
    exact fun b => by linarith [ show ( v p b : ℝ ) ≤ b from mod_cast v_le_n b p hp₀ hp₁, Nat.sub_add_cancel ( show ( b : ℕ ) ≤ m + 1 from by linarith [ Fin.is_lt b ] ) ] ;
  · refine' le_trans _ ( Finset.le_sup' _ ( Finset.mem_univ 0 ) ) ; norm_num [ bestHeadsAside ]

/-! ### The simplified recurrence -/

lemma v_simplified_recurrence (p : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hstep : ∀ k, 2 ≤ k → k ≤ n - 1 → v p (k - 1) + 1 ≤ v p k)
    (hs : 0 ≤ s_n p (n - 1)) :
    v p n = v p (n - 1) + 1 + p ^ n * (↑(n - 1) - v p (n - 1)) - (1 - p) ^ n := by
  rcases n with ( _ | _ | n ) <;> simp_all +decide;
  -- Apply the lemmas to split the sum into three parts.
  have h_split : ∑ h ∈ range (n + 3), binomProb (n + 2) p h * (Finset.univ : Finset (Fin (n + 2))).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside (n + 2) h r : ℝ) + v p r) =
    binomProb (n + 2) p 0 * v p (n + 1) +
    (∑ h ∈ Finset.Ico 1 (n + 2), binomProb (n + 2) p h * (1 + v p (n + 1))) +
    binomProb (n + 2) p (n + 2) * (n + 2) := by
      have h_split : ∀ h ∈ Finset.range (n + 3), binomProb (n + 2) p h * (Finset.univ : Finset (Fin (n + 2))).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside (n + 2) h r : ℝ) + v p r) =
        if h = 0 then binomProb (n + 2) p 0 * v p (n + 1) else
        if h = n + 2 then binomProb (n + 2) p (n + 2) * (n + 2) else binomProb (n + 2) p h * (1 + v p (n + 1)) := by
          intro h hh; split_ifs <;> simp_all +decide ;
          · exact Or.inl ( by simpa using bellman_sup_h_zero p hp₀ hp₁ ( n + 1 ) ( by linarith ) );
          · exact Or.inl <| mod_cast bellman_sup_h_all p hp₀ hp₁ _;
          · exact Or.inl <| bellman_sup_h_mid p hp₀ ( n + 1 ) ( by linarith ) ( fun k hk₁ hk₂ => hstep k hk₁ <| by linarith ) h ( Nat.pos_of_ne_zero ‹_› ) ( Nat.le_of_lt_succ <| lt_of_le_of_ne ( by linarith ) ‹_› );
      rw [ Finset.sum_congr rfl h_split, Finset.sum_range_succ ];
      rw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
      rw [ Finset.sum_congr rfl fun x hx => if_neg ( by linarith [ Finset.mem_range.mp hx ] ) ] ; ring;
  -- Apply the binomial probability sum lemma to simplify the expression.
  have h_binom_sum : ∑ h ∈ Finset.Ico 1 (n + 2), binomProb (n + 2) p h = 1 - binomProb (n + 2) p 0 - binomProb (n + 2) p (n + 2) := by
    have h_binom_sum : ∑ h ∈ Finset.range (n + 3), binomProb (n + 2) p h = 1 := by
      convert binomProb_sum ( n + 2 ) p using 1;
    rw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ ] at * ; linarith;
  simp_all +decide [ binomProb ];
  simp_all +decide [ ← Finset.sum_mul _ _ _, v ];
  convert h_split using 1 ; ring!

/-! ### Bounds for φ ≤ p -/

lemma lemma1_base_lower (p : ℝ) (hp : (Real.sqrt 5 - 1) / 2 ≤ p) (hp₁ : p < 1) :
    v p 1 + 1 ≤ v p 2 := by
  rw [ v_one, v_two ];
  · nlinarith [ mul_le_mul_of_nonneg_left hp <| sub_nonneg.mpr hp₁.le, Real.sqrt_nonneg 5, Real.sq_sqrt <| show 0 ≤ 5 by norm_num ];
  · nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
  · linarith

lemma lemma1_base_upper (p : ℝ) (hp : (Real.sqrt 5 - 1) / 2 ≤ p) (hp₁ : p < 1) :
    v p 2 < 2 - ((1 - p) / p) ^ 3 := by
  rw [ v_two p ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ];
  rw [ div_pow, sub_div', lt_div_iff₀ ];
  · have h_pos : p ^ 4 + 2 * p ^ 3 + p - 1 > 0 := by
      have h_poly_nonneg : p^2 + p - 1 ≥ 0 := by
        nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      nlinarith [ show 0 < p by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ];
    nlinarith [ pow_pos ( sub_pos.mpr hp₁ ) 3 ];
  · exact pow_pos ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) _;
  · exact pow_ne_zero _ ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] )

lemma lemma1_combined (p : ℝ) (hp : (Real.sqrt 5 - 1) / 2 ≤ p) (hp₁ : p < 1)
    (n : ℕ) (hn : 2 ≤ n) :
    v p (n - 1) + 1 ≤ v p n ∧ v p n < ↑n - ((1 - p) / p) ^ (n + 1) := by
  have hp₀ : 0 < p := by nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)]
  have hp_half : (1:ℝ)/2 < p := by nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)]
  have hqp : (1 - p) / p < 1 := by rw [div_lt_one hp₀]; linarith
  have hqp_pos : 0 < (1 - p) / p := div_pos (by linarith) hp₀
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | _ | n
  · omega
  · omega
  · rcases n with _ | n
    · exact ⟨lemma1_base_lower p hp hp₁, lemma1_base_upper p hp hp₁⟩
    · have ih_all : ∀ k, 2 ≤ k → k ≤ n + 2 →
          v p (k - 1) + 1 ≤ v p k ∧ v p k < ↑k - ((1 - p) / p) ^ (k + 1) :=
        fun k hk1 hk2 => ih k (by omega) hk1
      have hstep : ∀ k, 2 ≤ k → k ≤ n + 2 → v p (k - 1) + 1 ≤ v p k :=
        fun k hk1 hk2 => (ih_all k hk1 hk2).1
      have hs : 0 ≤ s_n p (n + 2) := by
        unfold s_n
        suffices h : v p (n + 2) ≥ v p 1 + (n + 1) by rw [v_one] at h; push_cast; linarith
        have : ∀ k, 1 ≤ k → k ≤ n + 2 → v p k ≥ v p 1 + (k - 1) := by
          intro k hk1 hk2
          induction k with
          | zero => omega
          | succ k ikh =>
            rcases k with _ | k
            · simp
            · have := ikh (by omega : 1 ≤ k + 1) (by omega)
              have := hstep (k + 2) (by omega) (by omega)
              push_cast at *; linarith
        have := this (n + 2) (by omega) le_rfl
        push_cast at *; linarith
      have hrec := v_simplified_recurrence p (n + 3) (by omega) hp₀.le hp₁.le
        (fun k hk1 hk2 => hstep k hk1 (by omega)) hs
      have ih_upper : v p (n + 2) < ↑(n + 2) - ((1 - p) / p) ^ (n + 3) :=
        (ih_all (n + 2) (by omega) le_rfl).2
      simp only [show n + 3 - 1 = n + 2 by omega] at hrec ⊢
      have hpq_eq : p ^ (n + 3) * ((1 - p) / p) ^ (n + 3) = (1 - p) ^ (n + 3) := by
        rw [div_pow, mul_div_cancel₀]; exact pow_ne_zero _ (ne_of_gt hp₀)
      have h_gap : (↑(n + 2) : ℝ) - v p (n + 2) > ((1 - p) / p) ^ (n + 3) := by
        push_cast at ih_upper ⊢; linarith
      constructor
      · -- Lower bound
        rw [hrec]
        have : p ^ (n + 3) * (↑(n + 2) - v p (n + 2)) > (1 - p) ^ (n + 3) := by
          calc p ^ (n + 3) * (↑(n + 2) - v p (n + 2))
              > p ^ (n + 3) * ((1 - p) / p) ^ (n + 3) :=
                mul_lt_mul_of_pos_left h_gap (pow_pos hp₀ _)
            _ = (1 - p) ^ (n + 3) := hpq_eq
        linarith
      · -- Upper bound
        rw [hrec]
        have h_upper_step : v p (n + 2) + 1 + p ^ (n + 3) * (↑(n + 2) - v p (n + 2)) -
            (1 - p) ^ (n + 3) < ↑(n + 2) + 1 - ((1 - p) / p) ^ (n + 3) := by
          nlinarith [pow_pos hp₀ (n+3),
            mul_lt_mul_of_pos_left h_gap
              (show 0 < 1 - p ^ (n+3) from by
                have := pow_lt_one₀ hp₀.le hp₁ (by omega : n + 3 ≠ 0); linarith),
            hpq_eq]
        have hqp_pow : ((1 - p) / p) ^ (n + 4) < ((1 - p) / p) ^ (n + 3) := by
          have : ((1 - p) / p) ^ (n + 4) = ((1 - p) / p) ^ (n + 3) * ((1 - p) / p) := by ring
          rw [this]; exact mul_lt_of_lt_one_right (pow_pos hqp_pos _) hqp
        push_cast at h_upper_step hqp_pow ⊢; linarith


/-! ### Auxiliary definitions -/

noncomputable def D (p : ℝ) (n : ℕ) : ℝ := ↑(n - 1) - v p (n - 1)
noncomputable def eta (p : ℝ) (n : ℕ) : ℝ := ↑(n - 2) + p - v p (n - 1)
noncomputable def alpha (p : ℝ) (n : ℕ) : ℝ := p ^ n + ↑n * p ^ (n - 1) * (1 - p)
noncomputable def C_aux (p : ℝ) (n : ℕ) : ℝ := ↑n * p ^ (n - 1) * (1 - p) ^ 2 + (1 - p) ^ n
noncomputable def R (p : ℝ) (n : ℕ) : ℝ := (1 - p) ^ (n - 1) - p ^ n
noncomputable def delta (p : ℝ) (n : ℕ) : ℝ := v p n - v p (n - 1) - 1

/-! ### Basic identities -/

lemma eta_eq_D_sub_q (p : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    eta p n = D p n - (1 - p) := by
  simp only [eta, D]
  have h1 : (n - 2 : ℕ) = n - 1 - 1 := by omega
  have h2 : (↑(n - 1 - 1 : ℕ) : ℝ) = ↑(n - 1 : ℕ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - 1)]; simp
  rw [h1, h2]; ring

lemma D_succ_eq_D_sub_delta (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    D p (n + 1) = D p n - delta p n := by
  simp only [D, delta]
  have h1 : n + 1 - 1 = n := Nat.succ_sub_one n
  rw [h1]
  have h2 : (↑(n - 1) : ℝ) = (↑n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  rw [h2]; ring

/-! ### v(2) ≥ 1 for p ≥ 1/2 -/

lemma v_two_ge_one (p : ℝ) (hp : 1 / 2 ≤ p) (hp₁ : p ≤ 1) :
    v p 2 ≥ 1 := by
  rw [v_two p (by linarith) hp₁]
  nlinarith [sq_nonneg (p - 1/2), sq_nonneg (1 - p)]

lemma v_ge_n_sub_one (p : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p ≤ 1)
    (hstep : ∀ k, 3 ≤ k → k ≤ n → delta p k ≥ 0) :
    v p n ≥ ↑n - 1 := by
  induction' n, hn using Nat.le_induction with n hn ih;
  · exact le_trans ( by norm_num ) ( v_two_ge_one p hp hp₁ );
  · have h_step : v p (n + 1) ≥ v p n + 1 := by
      exact le_of_sub_nonneg ( by linarith! [ hstep ( n + 1 ) ( by linarith ) ( by linarith ), show delta p ( n + 1 ) = v p ( n + 1 ) - v p n - 1 from rfl ] );
    grind

/-! ### Sup computation helpers for the reduced recurrence -/

lemma bellman_sup_mid_weak (p : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p ≤ 1)
    (hstep : ∀ k, 3 ≤ k → k ≤ n → delta p k ≥ 0)
    (h : ℕ) (hh₁ : 1 ≤ h) (hh₂ : h ≤ n - 1) :
    (Finset.univ : Finset (Fin (n + 1))).sup' ⟨0, Finset.mem_univ _⟩
      (fun r => (bestHeadsAside (n + 1) h r : ℝ) + v p r) = 1 + v p n := by
  refine' le_antisymm _ _;
  · simp +zetaDelta at *;
    intro b
    by_cases hb : b.val ≥ 2;
    · have h_step : v p n ≥ v p b.val + (n - b.val) := by
        have h_step : ∀ k, b.val < k → k ≤ n → v p k ≥ v p (k - 1) + 1 := by
          intros k hk₁ hk₂;
          have := hstep k ( by linarith ) hk₂; unfold delta at this; linarith;
        have h_step : ∀ k, b.val ≤ k → k ≤ n → v p k ≥ v p b.val + (k - b.val) := by
          intro k hk₁ hk₂; induction hk₁ <;> norm_num at *;
          grind;
        exact h_step n ( Nat.le_of_lt_succ b.2 ) le_rfl;
      unfold bestHeadsAside;
      rw [ min_def ];
      split_ifs <;> norm_num at *;
      · rw [ Nat.le_sub_iff_add_le ] at * <;> try linarith [ Fin.is_lt b ];
        linarith [ show ( h : ℝ ) + b ≤ n + 1 by norm_cast ];
      · grind +locals;
    · interval_cases _ : ( b : ℕ ) <;> simp_all +decide [ bestHeadsAside ];
      · exact Or.inl ( by linarith [ show ( h : ℝ ) ≤ n - 1 by exact le_tsub_of_add_le_right ( by norm_cast; omega ), show ( v p n : ℝ ) ≥ n - 1 by exact_mod_cast v_ge_n_sub_one p n hn ( by norm_num at *; linarith ) hp₁ hstep ] );
      · rw [ min_eq_left ( by norm_cast; omega ) ];
        have := v_ge_n_sub_one p n hn ( by norm_num at *; linarith ) hp₁ hstep;
        linarith [ show ( h : ℝ ) ≤ n - 1 by exact le_tsub_of_add_le_right ( by norm_cast; omega ), show ( v p 1 : ℝ ) = p by exact_mod_cast v_one p ];
  · refine' le_trans _ ( Finset.le_sup' _ <| Finset.mem_univ ⟨ n, by linarith ⟩ );
    unfold bestHeadsAside; aesop;

lemma bellman_sup_second_last (p : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hp : 1 / 2 ≤ p)
    (hstep : ∀ k, 3 ≤ k → k ≤ n → delta p k ≥ 0) :
    (Finset.univ : Finset (Fin (n + 1))).sup' ⟨0, Finset.mem_univ _⟩
      (fun r => (bestHeadsAside (n + 1) n r : ℝ) + v p r) = max (1 + v p n) (↑n + p) := by
  refine' le_antisymm (Finset.sup'_le _ _ _) _;
  · intro r hr;
    rcases r with ⟨ _ | r, hr ⟩ <;> norm_num [ bestHeadsAside ];
    · exact Or.inr ( by linarith );
    · by_cases hr : r + 1 ≥ 2;
      · have h_step : ∀ k, 3 ≤ k → k ≤ n → v p k ≥ v p (k - 1) + 1 := by
          exact fun k hk₁ hk₂ => by linarith [ hstep k hk₁ hk₂, show delta p k = v p k - v p ( k - 1 ) - 1 from rfl ] ;
        have h_step : ∀ k, r + 1 ≤ k → k ≤ n → v p k ≥ v p (r + 1) + (k - (r + 1)) := by
          intro k hk₁ hk₂; induction hk₁ <;> norm_num at *;
          grind;
        exact Or.inl ( by have := h_step n ( by linarith ) ( by linarith ) ; rw [ Nat.cast_sub ( by linarith ) ] at *; push_cast at *; linarith );
      · interval_cases _ : r + 1 <;> simp_all +decide;
        exact Or.inr ( by rw [ v_one ] );
  · refine' max_le_iff.mpr ⟨ _, _ ⟩;
    · refine' le_trans _ ( Finset.le_sup' _ <| Finset.mem_univ ⟨ n, by linarith ⟩ ) ; norm_num [ bestHeadsAside ];
      linarith;
    · refine' le_trans _ ( Finset.le_sup' _ ( Finset.mem_univ ⟨ 1, by linarith ⟩ ) ) ; norm_num [ bestHeadsAside ];
      rw [ v_one ]

/-! ### The reduced recurrence -/

lemma reduced_recurrence (p : ℝ) (m : ℕ) (hm : 3 ≤ m)
    (hp : 1 / 2 ≤ p) (hp₁ : p ≤ 1)
    (hstep : ∀ k, 3 ≤ k → k ≤ m - 1 → delta p k ≥ 0) :
    v p m = v p (m - 1) + 1 + p ^ m * D p m +
    ↑m * p ^ (m - 1) * (1 - p) * max 0 (eta p m) - (1 - p) ^ m := by
  obtain ⟨ n, rfl ⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero ( by linarith );
  have h_split : v p (n + 1) = (1 - p) ^ (n + 1) * v p n + (∑ h ∈ Finset.Ico 1 n, binomProb (n + 1) p h * (1 + v p n)) + binomProb (n + 1) p n * max (1 + v p n) (n + p) + p ^ (n + 1) * (n + 1) := by
    have h_split : v p (n + 1) = ∑ h ∈ Finset.range (n + 2), binomProb (n + 1) p h * (Finset.univ : Finset (Fin (n + 1))).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside (n + 1) h r : ℝ) + v p r) := by
      rw [CoinGame.v];
    rw [ h_split, Finset.sum_range_succ, Finset.sum_range_succ ];
    rw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num;
    · rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_range.mpr ( Nat.pos_of_ne_zero ( by linarith ) ) ) ];
      rw [ Finset.sum_congr rfl fun x hx => by rw [ bellman_sup_mid_weak p n ( by linarith ) ( by linarith ) ( by linarith ) hstep x ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.le_sub_one_of_lt ( Finset.mem_range.mp ( Finset.mem_sdiff.mp hx |>.1 ) ) ) ] ];
      rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_range.mpr ( Nat.pos_of_ne_zero ( by linarith ) ) ) ];
      rw [ bellman_sup_h_zero p ( by linarith ) ( by linarith ) n ( by linarith ), bellman_sup_second_last p n ( by linarith ) ( by linarith ) hstep, bellman_sup_h_all p ( by linarith ) ( by linarith ) n ] ; ring_nf;
      unfold binomProb; norm_num [ Nat.choose ] ; ring;
    · linarith;
  have h_binom_sum : ∑ h ∈ Finset.Ico 1 n, binomProb (n + 1) p h = 1 - (1 - p) ^ (n + 1) - (n + 1) * p ^ n * (1 - p) - p ^ (n + 1) := by
    have h_binom_sum : ∑ h ∈ Finset.range (n + 2), binomProb (n + 1) p h = 1 := by
      convert binomProb_sum ( n + 1 ) p using 1;
    rw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ ] at *;
    · unfold binomProb at *; norm_num [ Nat.choose_succ_succ, pow_succ' ] at *; linarith;
    · linarith;
  simp_all +decide [ ← Finset.sum_mul _ _ _, D, eta ];
  unfold binomProb; norm_num [ Nat.cast_sub ( by linarith : 1 ≤ n ) ] ; ring_nf;
  grind

/-! ### Active-inactive lemma -/

lemma delta_of_eta_nonneg (p : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p ≤ 1)
    (hstep : ∀ k, 3 ≤ k → k ≤ n - 1 → delta p k ≥ 0)
    (heta : eta p n ≥ 0) :
    delta p n = D p n * alpha p n - C_aux p n := by
  have hrec := reduced_recurrence p n hn hp hp₁ hstep
  have heta_eq : eta p n = D p n - (1 - p) := eta_eq_D_sub_q p n (by omega)
  simp only [delta]
  rw [hrec, show max 0 (eta p n) = eta p n from max_eq_right heta, heta_eq]
  simp only [D, alpha, C_aux]; ring

lemma delta_of_eta_nonpos (p : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p ≤ 1)
    (hstep : ∀ k, 3 ≤ k → k ≤ n - 1 → delta p k ≥ 0)
    (heta : eta p n ≤ 0) :
    delta p n = p ^ n * D p n - (1 - p) ^ n := by
  have hrec := reduced_recurrence p n hn hp hp₁ hstep
  simp only [delta]
  rw [hrec, show max 0 (eta p n) = 0 from max_eq_left heta]; ring

lemma D_succ_of_eta_nonneg (p : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p ≤ 1)
    (hstep : ∀ k, 3 ≤ k → k ≤ n - 1 → delta p k ≥ 0)
    (heta : eta p n ≥ 0) :
    D p (n + 1) = D p n * (1 - alpha p n) + C_aux p n := by
  rw [D_succ_eq_D_sub_delta p n (by omega), delta_of_eta_nonneg p n hn hp hp₁ hstep heta]; ring

lemma D_succ_of_eta_nonpos (p : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p ≤ 1)
    (hstep : ∀ k, 3 ≤ k → k ≤ n - 1 → delta p k ≥ 0)
    (heta : eta p n ≤ 0) :
    D p (n + 1) = D p n * (1 - p ^ n) + (1 - p) ^ n := by
  rw [D_succ_eq_D_sub_delta p n (by omega), delta_of_eta_nonpos p n hn hp hp₁ hstep heta]; ring

/-! ### Alpha bounds -/

lemma alpha_pos (p : ℝ) (n : ℕ) (hp₀ : 0 < p) (_hp₁ : p < 1) (_hn : 2 ≤ n) :
    0 < alpha p n := by
  unfold alpha
  have h1 : 0 < p ^ n := pow_pos hp₀ n
  have : (0 : ℝ) ≤ ↑n * p ^ (n - 1) * (1 - p) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hp₀.le (n - 1))) (by linarith)
  linarith

lemma alpha_lt_one (p : ℝ) (n : ℕ) (hp₀ : 0 < p) (hp₁ : p < 1) (hn : 2 ≤ n) :
    alpha p n < 1 := by
  induction hn <;> simp_all +decide [pow_succ, alpha]
  · nlinarith
  · cases ‹2 ≤ _› <;> simp_all +decide [pow_succ']
    · nlinarith [mul_pos hp₀ (sub_pos.mpr hp₁)]
    · nlinarith [mul_pos hp₀ (pow_pos hp₀ ‹_›),
        mul_pos hp₀ (mul_pos (pow_pos hp₀ ‹_›) (sub_pos.mpr hp₁)),
        mul_pos (sub_pos.mpr hp₁) (pow_pos hp₀ ‹_›),
        mul_pos (sub_pos.mpr hp₁) (mul_pos (pow_pos hp₀ ‹_›) (sub_pos.mpr hp₁))]

/-! ### Algebraic core -/

lemma algebraic_core (D' α' C' α_val C : ℝ)
    (hα'_pos : 0 < α') (hα'_lt : α' < 1)
    (hα_nn : 0 ≤ α_val)
    (hD : D' * α' ≥ C')
    (hC : C' * α_val ≥ C * α') :
    (D' * (1 - α') + C') * α_val ≥ C := by
  nlinarith [mul_le_mul_of_nonneg_left hα'_lt.le hα_nn,
    mul_le_mul_of_nonneg_left hα'_pos.le hα_nn]

/-! ### The ratio bound -/

lemma ratio_bound (p : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (hR : R p n > 0) :
    R p n * alpha p (n - 1) ≤ R p (n - 1) * alpha p n := by
  unfold R alpha at *;
  rcases n with ( _ | _ | n ) <;> norm_num [ pow_succ' ] at *;
  nlinarith [ mul_le_mul_of_nonneg_left hp ( show 0 ≤ p * p ^ n by positivity ), mul_le_mul_of_nonneg_left hp ( show 0 ≤ p ^ n * ( 1 - p ) by exact mul_nonneg ( pow_nonneg ( by linarith ) _ ) ( by linarith ) ), mul_le_mul_of_nonneg_left hp ( show 0 ≤ p ^ n * n by positivity ), pow_nonneg ( by linarith : 0 ≤ p ) n, pow_nonneg ( by linarith : 0 ≤ 1 - p ) n ]

/-! ### C-alpha ratio -/

lemma C_alpha_ratio (p : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (hR : R p n > 0) :
    C_aux p (n - 1) * alpha p n ≥ C_aux p n * alpha p (n - 1) := by
  have hC_def : ∀ m : ℕ, m ≥ 2 → C_aux p m = (1 - p) * alpha p m + (1 - p) * R p m := by
    intro m hm; unfold C_aux alpha R; ring_nf;
    cases m <;> norm_num [ pow_succ' ] at * ; linarith;
  rw [ hC_def, hC_def ] <;> try omega;
  nlinarith [ ratio_bound p n hn hp hp₁ hR, show 0 ≤ 1 - p by linarith ]

/-! ### Transition bound -/

lemma transition_bound (p : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (htrans : p ^ (n - 1) > (1 - p) ^ (n - 2)) :
    p ^ n * C_aux p (n - 1) ≥ (1 - p) ^ n * alpha p (n - 1) := by
  unfold C_aux alpha;
  suffices h_simp : (n - 1) * p ^ (n - 2) * (1 - p) ^ 2 * (p ^ n - (1 - p) ^ (n - 1)) + p ^ (n - 1) * (1 - p) ^ (n - 1) * (2 * p - 1) ≥ 0 by
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
    linarith;
  refine add_nonneg ?_ ?_;
  · refine mul_nonneg ?_ ?_;
    · exact mul_nonneg ( mul_nonneg ( sub_nonneg_of_le ( by norm_cast; linarith ) ) ( pow_nonneg ( by linarith ) _ ) ) ( sq_nonneg _ );
    · rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
      nlinarith [ pow_nonneg ( by linarith : 0 ≤ 1 - p ) n ];
  · exact mul_nonneg ( mul_nonneg ( pow_nonneg ( by linarith ) _ ) ( pow_nonneg ( by linarith ) _ ) ) ( by linarith )

/-! ### Transition condition -/

lemma transition_condition (p : ℝ) (n : ℕ) (hn : 4 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (_hphi : p < (Real.sqrt 5 - 1) / 2)
    (hstep : ∀ k, 3 ≤ k → k ≤ n - 2 → delta p k ≥ 0)
    (heta_prev : eta p (n - 1) ≥ 0)
    (heta_curr : eta p n < 0) :
    p ^ (n - 1) > (1 - p) ^ (n - 2) := by
  have h_delta : delta p (n - 1) = D p (n - 1) * alpha p (n - 1) - C_aux p (n - 1) := by
    apply_rules [ delta_of_eta_nonneg ];
    · omega;
    · linarith;
  have h_eta_neg : -eta p n = -eta p (n - 1) + delta p (n - 1) := by
    rcases n with ( _ | _ | n ) <;> norm_num [ delta, eta, D ] at *;
    rw [ Nat.cast_sub ] <;> push_cast <;> linarith;
  have h_D : D p (n - 1) = (1 - p) + eta p (n - 1) := by
    rcases n with ( _ | _ | n ) <;> norm_num [ D, eta ] at *;
    rw [ Nat.cast_sub ] <;> push_cast <;> linarith;
  have h_q_alpha_C : (1 - p) * alpha p (n - 1) - C_aux p (n - 1) = (1 - p) * (p ^ (n - 1) - (1 - p) ^ (n - 2)) := by
    rcases n with ( _ | _ | n ) <;> norm_num [ alpha, C_aux ] at *;
    ring!;
  have h_alpha_lt_one : alpha p (n - 1) < 1 := by
    apply alpha_lt_one;
    · linarith;
    · linarith;
    · omega;
  nlinarith [ mul_pos ( sub_pos.mpr hp₁ ) ( sub_pos.mpr h_alpha_lt_one ) ]

/-! ### Case lemmas -/

lemma active_R_nonpos (p : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (_hphi : p < (Real.sqrt 5 - 1) / 2)
    (hstep : ∀ k, 3 ≤ k → k ≤ n - 1 → delta p k ≥ 0)
    (heta : eta p n ≥ 0)
    (hR : R p n ≤ 0) :
    delta p n ≥ 0 := by
  rw [ delta_of_eta_nonneg p n hn ( by linarith ) ( by linarith ) hstep heta ];
  unfold D alpha C_aux R at *;
  rcases n with ( _ | _ | n ) <;> norm_num at *;
  unfold eta at heta;
  norm_num [ Nat.succ_eq_add_one, pow_add ] at *;
  nlinarith [ show 0 ≤ p ^ n * p by positivity, show 0 ≤ ( n + 1 + 1 ) * ( p ^ n * p ) * ( 1 - p ) by exact mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( by linarith ), show 0 ≤ ( 1 - p ) ^ n * ( 1 - p ) by exact mul_nonneg ( pow_nonneg ( by linarith ) _ ) ( by linarith ) ]

lemma active_R_pos (p : ℝ) (n : ℕ) (hn : 4 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (_hphi : p < (Real.sqrt 5 - 1) / 2)
    (hstep : ∀ k, 3 ≤ k → k ≤ n - 1 → delta p k ≥ 0)
    (heta : eta p n ≥ 0)
    (hR : R p n > 0) :
    delta p n ≥ 0 := by
  have h_delta : delta p n = D p n * alpha p n - C_aux p n := by
    apply delta_of_eta_nonneg p n (by linarith) hp (by linarith) (fun k hk1 hk2 => hstep k hk1 (by omega)) heta;
  have h_delta_n_minus_1 : delta p (n - 1) = D p (n - 1) * alpha p (n - 1) - C_aux p (n - 1) := by
    apply delta_of_eta_nonneg p (n - 1) (by
    omega) hp (by
    linarith) (by
    exact fun k hk₁ hk₂ => hstep k hk₁ ( Nat.le_trans hk₂ ( Nat.pred_le _ ) )) (by
    rcases n with ( _ | _ | _ | n ) <;> norm_num at *;
    unfold eta at *;
    unfold delta at * ; norm_num at *;
    grind +revert)
  have h_D_n_minus_1 : D p (n - 1) * alpha p (n - 1) ≥ C_aux p (n - 1) := by
    linarith [ hstep ( n - 1 ) ( Nat.le_sub_one_of_lt hn ) ( Nat.sub_le_sub_left ( by norm_num ) _ ) ];
  have h_D_n : D p n = D p (n - 1) * (1 - alpha p (n - 1)) + C_aux p (n - 1) := by
    apply D_succ_of_eta_nonneg;
    · exact Nat.le_sub_one_of_lt hn;
    · linarith;
    · lia;
    · exact fun k hk₁ hk₂ => hstep k hk₁ ( Nat.le_trans hk₂ ( Nat.pred_le _ ) );
    · grind +suggestions;
  have h_C_alpha_ratio : C_aux p (n - 1) * alpha p n ≥ C_aux p n * alpha p (n - 1) := by
    apply C_alpha_ratio p n (by linarith) hp hp₁ hR;
  have h_alpha_pos : 0 < alpha p (n - 1) := by
    exact alpha_pos p ( n - 1 ) ( by linarith ) ( by linarith ) ( Nat.le_sub_one_of_lt ( by linarith ) )
  have h_alpha_lt_one : alpha p (n - 1) < 1 := by
    apply alpha_lt_one p (n - 1) (by linarith) (by linarith) (by omega)
  have h_alpha_n_nonneg : 0 ≤ alpha p n := by
    exact add_nonneg ( pow_nonneg ( by linarith ) _ ) ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by linarith ) _ ) ) ( by linarith ) );
  nlinarith [ algebraic_core ( D p ( n - 1 ) ) ( alpha p ( n - 1 ) ) ( C_aux p ( n - 1 ) ) ( alpha p n ) ( C_aux p n ) h_alpha_pos h_alpha_lt_one h_alpha_n_nonneg h_D_n_minus_1 h_C_alpha_ratio ]

lemma inactive_inactive (p : ℝ) (n : ℕ) (hn : 4 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (hstep : ∀ k, 3 ≤ k → k ≤ n - 1 → delta p k ≥ 0)
    (heta_prev : eta p (n - 1) < 0)
    (heta_curr : eta p n < 0) :
    delta p n ≥ 0 := by
  have h_trans : p ^ (n - 1) * D p (n - 1) - (1 - p) ^ (n - 1) ≥ 0 := by
    have h_trans : delta p (n - 1) = p ^ (n - 1) * D p (n - 1) - (1 - p) ^ (n - 1) := by
      exact delta_of_eta_nonpos p ( n - 1 ) ( Nat.le_sub_one_of_lt ( by linarith ) ) ( by linarith ) ( by linarith ) ( fun k hk₁ hk₂ => hstep k hk₁ ( by omega ) ) heta_prev.le;
    exact h_trans ▸ hstep _ ( Nat.le_sub_one_of_lt hn ) le_rfl;
  have h_trans : D p n ≥ (1 - p) ^ (n - 1) / p ^ (n - 1) := by
    have h_trans : D p n = D p (n - 1) * (1 - p ^ (n - 1)) + (1 - p) ^ (n - 1) := by
      convert D_succ_of_eta_nonpos p ( n - 1 ) ( by omega ) ( by linarith ) ( by linarith ) _ _ using 1;
      · exact fun k hk₁ hk₂ => hstep k hk₁ ( Nat.le_trans hk₂ ( Nat.pred_le _ ) );
      · linarith;
    rw [ h_trans, ge_iff_le, div_le_iff₀ ] <;> nlinarith [ pow_pos ( by linarith : 0 < p ) ( n - 1 ), pow_pos ( by linarith : 0 < 1 - p ) ( n - 1 ), pow_le_pow_of_le_one ( by linarith : 0 ≤ p ) hp₁.le ( show n - 1 ≥ 1 from Nat.sub_pos_of_lt ( by linarith ) ) ];
  have h_trans : p ^ n * D p n - (1 - p) ^ n ≥ 0 := by
    rcases n <;> simp_all +decide [ pow_succ' ];
    rw [ div_le_iff₀ ( pow_pos ( by positivity ) _ ) ] at h_trans ; nlinarith [ pow_pos ( by positivity : 0 < p ) ‹_›, pow_pos ( by linarith : 0 < 1 - p ) ‹_› ];
  grind +suggestions

lemma inactive_active (p : ℝ) (n : ℕ) (hn : 4 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (hphi : p < (Real.sqrt 5 - 1) / 2)
    (hstep : ∀ k, 3 ≤ k → k ≤ n - 1 → delta p k ≥ 0)
    (heta_prev : eta p (n - 1) ≥ 0)
    (heta_curr : eta p n < 0) :
    delta p n ≥ 0 := by
  unfold delta;
  have h_delta_nonpos : v p n - v p (n - 1) - 1 = p ^ n * D p n - (1 - p) ^ n := by
    convert delta_of_eta_nonpos p n ( by linarith ) hp ( by linarith ) ( fun k hk₁ hk₂ => hstep k hk₁ ( by omega ) ) ( by linarith ) using 1;
  have h_algebraic_core : p ^ n * D p n ≥ (1 - p) ^ n := by
    have h_algebraic_core : p ^ n * (D p (n - 1) * (1 - alpha p (n - 1)) + C_aux p (n - 1)) ≥ (1 - p) ^ n := by
      have h_algebraic_core : D p (n - 1) * alpha p (n - 1) ≥ C_aux p (n - 1) := by
        have := delta_of_eta_nonneg p ( n - 1 ) ( by omega ) hp hp₁.le ( fun k hk₁ hk₂ => hstep k hk₁ ( by omega ) ) heta_prev;
        linarith [ hstep ( n - 1 ) ( by omega ) ( by omega ) ];
      have h_algebraic_core : p ^ n * C_aux p (n - 1) ≥ (1 - p) ^ n * alpha p (n - 1) := by
        apply transition_bound p n (by omega) hp hp₁ (transition_condition p n (by omega) hp hp₁ hphi (fun k hk₁ hk₂ => hstep k hk₁ (by omega)) heta_prev heta_curr);
      have h_algebraic_core : p ^ n * D p (n - 1) * alpha p (n - 1) ≥ (1 - p) ^ n * alpha p (n - 1) := by
        nlinarith [ pow_pos ( by linarith : 0 < p ) n ];
      nlinarith [ pow_pos ( by linarith : 0 < p ) n, pow_pos ( by linarith : 0 < 1 - p ) n, alpha_pos p ( n - 1 ) ( by linarith ) ( by linarith ) ( by omega ), alpha_lt_one p ( n - 1 ) ( by linarith ) ( by linarith ) ( by omega ) ];
    convert h_algebraic_core using 1;
    exact congrArg _ ( D_succ_of_eta_nonneg p ( n - 1 ) ( by omega ) hp hp₁.le ( fun k hk₁ hk₂ => hstep k hk₁ ( by omega ) ) heta_prev );
  linarith

/-! ### Main inductive step -/

theorem inductive_step (p : ℝ) (n : ℕ) (hn : 4 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (hphi : p < (Real.sqrt 5 - 1) / 2)
    (hstep : ∀ k, 3 ≤ k → k ≤ n - 1 → delta p k ≥ 0) :
    delta p n ≥ 0 := by
  by_cases heta : eta p n ≥ 0
  · by_cases hR : R p n ≤ 0
    · exact active_R_nonpos p n (by omega) hp hp₁ hphi hstep heta hR
    · push_neg at hR
      exact active_R_pos p n hn hp hp₁ hphi hstep heta hR
  · push_neg at heta
    by_cases heta_prev : eta p (n - 1) ≥ 0
    · exact inactive_active p n hn hp hp₁ hphi hstep heta_prev heta
    · push_neg at heta_prev
      exact inactive_inactive p n hn hp hp₁ hstep heta_prev heta

/-! ### Base cases -/

lemma v_three_minus_v_two_eq (p : ℝ) (hp₀ : 1 / 2 ≤ p) (hp₁ : p ≤ 1)
    (hphi : p ≤ (Real.sqrt 5 - 1) / 2) :
    v p 3 - v p 2 - 1 = (1 - p) ^ 3 * (p + 1) ^ 2 * (2 * p - 1) := by
  have hv2_le_v1_plus_1 : v p 2 ≤ v p 1 + 1 := by
    have hv2_le_v1_plus_1 : v p 2 - v p 1 - 1 = (1 - p) * (p ^ 2 + p - 1) := by
      rw [ v_two, v_one ] ; ring;
      · linarith;
      · linarith;
    nlinarith [ mul_le_mul_of_nonneg_left hphi ( sub_nonneg.mpr hp₁ ), Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
  have hv3_h2 : ∀ h : Fin 3, (Finset.univ : Finset (Fin 3)).sup' ⟨0, Finset.mem_univ _⟩ (fun r : Fin 3 => (bestHeadsAside 3 (h + 1) r : ℝ) + v p r) = if h = 0 then 1 + v p 2 else if h = 1 then 2 + p else 3 := by
    intro h; fin_cases h <;> simp +decide [ Fin.univ_succ ] ;
    · unfold bestHeadsAside; norm_num;
      rw [ max_eq_right ];
      · exact max_eq_right ( by linarith [ v_mono_n p ( by linarith ) ( by linarith ) 1 ] );
      · exact le_max_of_le_left ( by linarith [ show 0 ≤ v p 1 from by rw [ v_one ] ; linarith ] );
    · unfold bestHeadsAside; norm_num [ v_one, v_two ] ;
      rw [ max_eq_right ];
      · exact max_eq_left ( by linarith [ show v p 1 = p from v_one p ] );
      · exact le_max_of_le_left ( by linarith );
    · unfold bestHeadsAside; norm_num;
      constructor <;> linarith [ show v p 1 ≤ 1 by exact le_trans ( v_le_n 1 p ( by linarith ) ( by linarith ) ) ( by norm_num ), show v p 2 ≤ 2 by exact le_trans ( v_le_n 2 p ( by linarith ) ( by linarith ) ) ( by norm_num ) ];
  have hv2 : v p 2 = -p ^ 3 + 3 * p := by
    exact v_two p ( by linarith ) ( by linarith )
  have hv1 : v p 1 = p := v_one p
  simp_all +decide;
  unfold v; norm_num [ Finset.sum_range_succ, hv2, hv1, hv3_h2 ] ; ring_nf;
  simp_all +decide [ Fin.forall_fin_succ, Fin.univ_succ ] ; ring_nf;
  unfold binomProb; norm_num [ Nat.choose ] ; ring_nf;
  rw [ max_eq_right ] <;> norm_num at *;
  · rw [ max_eq_right ] <;> nlinarith [ pow_two_nonneg ( p - 1 / 2 ) ];
  · exact Or.inl ( by linarith )

lemma v_three_ge_v_two_plus_one (p : ℝ) (hp : 1 / 2 ≤ p) (hp₁ : p < 1) :
    v p 2 + 1 ≤ v p 3 := by
  have h_nonneg : (1 - p) ^ 3 * (p + 1) ^ 2 * (2 * p - 1) ≥ 0 := by
    exact mul_nonneg ( mul_nonneg ( pow_nonneg ( by linarith ) _ ) ( pow_nonneg ( by linarith ) _ ) ) ( by linarith );
  by_cases hphi : p ≤ (Real.sqrt 5 - 1) / 2;
  · linarith [ v_three_minus_v_two_eq p hp hp₁.le hphi ];
  · exact lemma1_combined p ( le_of_not_ge hphi ) hp₁ 3 ( by norm_num ) |>.1

set_option maxHeartbeats 1600000 in
lemma v_four_ge_v_three_plus_one (p : ℝ) (hp : 1 / 2 ≤ p) (hp₁ : p < 1) :
    v p 3 + 1 ≤ v p 4 := by
  have h_lower_bound : v p 4 ≥ (1 - p) ^ 4 * v p 3 + (4 * p * (1 - p) ^ 3 + 6 * p ^ 2 * (1 - p) ^ 2) * (1 + v p 3) + 4 * p ^ 3 * (1 - p) * max (1 + v p 3) (3 + p) + p ^ 4 * 4 := by
    have h_lower_bound : v p 4 ≥ (1 - p) ^ 4 * v p 3 + (4 * p * (1 - p) ^ 3 + 6 * p ^ 2 * (1 - p) ^ 2) * (1 + v p 3) + 4 * p ^ 3 * (1 - p) * (Finset.univ : Finset (Fin 4)).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside 4 3 r : ℝ) + v p r) + p ^ 4 * 4 := by
      have h_lower_bound : v p 4 = (1 - p) ^ 4 * v p 3 + 4 * p * (1 - p) ^ 3 * (Finset.univ : Finset (Fin 4)).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside 4 1 r : ℝ) + v p r) + 6 * p ^ 2 * (1 - p) ^ 2 * (Finset.univ : Finset (Fin 4)).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside 4 2 r : ℝ) + v p r) + 4 * p ^ 3 * (1 - p) * (Finset.univ : Finset (Fin 4)).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside 4 3 r : ℝ) + v p r) + p ^ 4 * 4 := by
        rw [ show v p 4 = ∑ h ∈ Finset.range 5, binomProb 4 p h * ( Finset.univ : Finset ( Fin 4 ) ).sup' ⟨ 0, Finset.mem_univ _ ⟩ ( fun r => ( bestHeadsAside 4 h r : ℝ ) + v p r ) from ?_ ];
        · norm_num [ Finset.sum_range_succ, binomProb ];
          congr;
          · refine' le_antisymm _ _ <;> norm_num [ Fin.univ_succ ];
            exact ⟨ v_nonneg 3 p ( by linarith ) ( by linarith ), by linarith [ v_mono_n p ( by linarith ) ( by linarith ) 1, v_mono_n p ( by linarith ) ( by linarith ) 2, v_three_ge_v_two_plus_one p hp hp₁ ], by linarith [ v_mono_n p ( by linarith ) ( by linarith ) 2, v_three_ge_v_two_plus_one p hp hp₁ ] ⟩;
          · refine' le_antisymm _ _ <;> norm_num [ Fin.univ_succ ];
            · refine' ⟨ _, _, _, _ ⟩ <;> norm_num [ bestHeadsAside ];
              · rw [ v_one ] ; linarith;
              · rw [ v_two ] <;> nlinarith [ sq_nonneg ( p - 1 ) ];
              · have := v_le_n 3 p ( by linarith ) ( by linarith ) ; norm_num at * ; linarith;
            · unfold bestHeadsAside; norm_num;
        · rw [CoinGame.v];
      have h_sup_ge : (Finset.univ : Finset (Fin 4)).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside 4 1 r : ℝ) + v p r) ≥ 1 + v p 3 ∧ (Finset.univ : Finset (Fin 4)).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside 4 2 r : ℝ) + v p r) ≥ 1 + v p 3 := by
        constructor <;> refine' le_trans _ ( Finset.le_sup' _ <| Finset.mem_univ 3 ) <;> norm_num [ bestHeadsAside ];
      nlinarith [ show 0 ≤ 4 * p * ( 1 - p ) ^ 3 by exact mul_nonneg ( by positivity ) ( pow_nonneg ( by linarith ) _ ), show 0 ≤ 6 * p ^ 2 * ( 1 - p ) ^ 2 by exact mul_nonneg ( by positivity ) ( pow_nonneg ( by linarith ) _ ) ];
    have h_lower_bound : (Finset.univ : Finset (Fin 4)).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside 4 3 r : ℝ) + v p r) ≥ max (1 + v p 3) (3 + p) := by
      simp +decide [ Fin.univ_succ ];
      norm_num [ bestHeadsAside ];
      rw [ v_two, v_one ] ; norm_num;
      · grind;
      · linarith;
      · linarith;
    nlinarith [ show 0 ≤ 4 * p ^ 3 * ( 1 - p ) by exact mul_nonneg ( mul_nonneg zero_le_four ( pow_nonneg ( by linarith ) _ ) ) ( by linarith ) ];
  cases max_cases ( 1 + v p 3 ) ( 3 + p ) <;> simp_all +decide;
  · have := v_three_minus_v_two_eq p ( by norm_num at *; linarith ) ( by norm_num at *; linarith );
    by_cases h_case : p ≤ (Real.sqrt 5 - 1) / 2;
    · rw [ show v p 2 = -p ^ 3 + 3 * p by exact v_two p ( by norm_num at *; linarith ) ( by norm_num at *; linarith ) ] at this;
      have := this h_case;
      nlinarith [ pow_pos ( sub_pos.mpr hp₁ ) 3, pow_pos ( sub_pos.mpr hp₁ ) 4, pow_pos ( sub_pos.mpr hp₁ ) 5, pow_pos ( sub_pos.mpr hp₁ ) 6, pow_pos ( sub_pos.mpr hp₁ ) 7, pow_pos ( sub_pos.mpr hp₁ ) 8, pow_pos ( sub_pos.mpr hp₁ ) 9, pow_pos ( sub_pos.mpr hp₁ ) 10 ];
    · have := lemma1_combined p ( by linarith ) hp₁ 3 ( by norm_num );
      norm_num [ v_two p ( by linarith ) ( by linarith ) ] at *;
      field_simp at this;
      grind;
  · have h_v3 : v p 3 = -p ^ 3 + 3 * p + (1 - p) ^ 3 * (p + 1) ^ 2 * (2 * p - 1) + 1 := by
      have h_v3 : v p 3 - v p 2 - 1 = (1 - p) ^ 3 * (p + 1) ^ 2 * (2 * p - 1) := by
        by_cases hphi : p ≤ (Real.sqrt 5 - 1) / 2;
        · exact v_three_minus_v_two_eq p ( by norm_num at *; linarith ) ( by linarith ) hphi;
        · have := lemma1_combined p ( by linarith ) hp₁ 3 ( by norm_num );
          norm_num [ v_two p ( by positivity ) ( by linarith ) ] at *;
          have h_p4 : p ^ 4 ≥ (Real.sqrt 5 - 1) ^ 4 / 16 := by
            exact le_trans ( by nlinarith only [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( pow_le_pow_left₀ ( by nlinarith only [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) hphi.le 4 );
          rw [ show ( Real.sqrt 5 - 1 ) ^ 4 = ( Real.sqrt 5 ^ 2 - 2 * Real.sqrt 5 + 1 ) ^ 2 by ring, Real.sq_sqrt ] at h_p4 <;> nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      rw [ ← h_v3, CoinGame.v_two ] ; ring;
      · positivity;
      · linarith;
    nlinarith [ pow_nonneg ( sub_nonneg.mpr hp ) 3, pow_nonneg ( sub_nonneg.mpr hp ) 4, pow_nonneg ( sub_nonneg.mpr hp ) 5, pow_nonneg ( sub_nonneg.mpr hp ) 6, pow_nonneg ( sub_nonneg.mpr hp ) 7, pow_nonneg ( sub_nonneg.mpr hp ) 8, pow_nonneg ( sub_nonneg.mpr hp ) 9, pow_nonneg ( sub_nonneg.mpr hp ) 10 ]

/-
For every `n ≥ 3` and `p ∈ [1/2, 1)`, `v(n, p) ≥ v(n-1, p) + 1`.
-/
theorem v_sub_v_sub_one_ge_one_of_half_le (p : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hp : 1 / 2 ≤ p) (hp₁ : p < 1) :
    v p (n - 1) + 1 ≤ v p n := by
  by_cases hphi : (Real.sqrt 5 - 1) / 2 ≤ p
  · exact lemma1_combined p hphi hp₁ n (by omega) |>.1
  · push_neg at hphi
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    rcases n with _ | _ | _ | _ | _ | n
    · omega
    · omega
    · omega
    · exact v_three_ge_v_two_plus_one p hp hp₁
    · exact v_four_ge_v_three_plus_one p hp hp₁
    · have h := inductive_step p (n + 5) (by omega) hp hp₁ hphi
        (fun k hk₁ hk₂ => by
          simp only [delta]
          linarith [ih k (by omega) (by omega)])
      simp only [delta] at h
      linarith

/-! ## sqrt 5 bounds -/

lemma sqrt5_gt_1 : (1 : ℝ) < Real.sqrt 5 := by
  rw [show (1:ℝ) = Real.sqrt 1 from by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
lemma sqrt5_gt_2 : Real.sqrt 5 > 2 := by
  rw [show (2:ℝ) = Real.sqrt 4 from by
    rw [show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
lemma sqrt5_lt_3 : Real.sqrt 5 < 3 := by
  rw [show (3:ℝ) = Real.sqrt 9 from by
    rw [show (9:ℝ) = 3^2 from by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
lemma phi_pos' : 0 < (Real.sqrt 5 - 1) / 2 := by linarith [sqrt5_gt_1]
lemma phi_lt_one' : (Real.sqrt 5 - 1) / 2 < 1 := by linarith [sqrt5_lt_3]
lemma half_lt_phi' : 1 / 2 < (Real.sqrt 5 - 1) / 2 := by linarith [sqrt5_gt_2]
lemma phi_sq_eq' : ((Real.sqrt 5 - 1) / 2) ^ 2 + (Real.sqrt 5 - 1) / 2 - 1 = 0 := by
  field_simp; nlinarith [sqrt5_sq]

/-! ## Monotonicity and convergence of s_n -/

lemma s_n_mono (p : ℝ) (hp : 1 / 2 ≤ p) (hp₁ : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    s_n p n ≤ s_n p (n + 1) := by
  simp only [s_n]
  have h := v_sub_v_sub_one_ge_one_of_half_le p (n + 1) (by omega) hp hp₁
  simp only [Nat.add_sub_cancel] at h; push_cast; linarith

lemma s_n_upper (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) :
    s_n p n ≤ 1 - p := by
  simp only [s_n]; have := v_le_n n p hp₀ hp₁; linarith

lemma s_n_nonneg_of_phi_le (p : ℝ) (hp : (Real.sqrt 5 - 1) / 2 ≤ p) (hp₁ : p < 1)
    (n : ℕ) (hn : 2 ≤ n) : 0 ≤ s_n p n := by
  simp only [s_n]
  suffices h : v p n ≥ ↑n - 1 + p by linarith
  induction n, hn using Nat.le_induction with
  | base => have := lemma1_base_lower p hp hp₁; rw [v_one] at this; push_cast; linarith
  | succ n _ ih =>
    have := (lemma1_combined p hp hp₁ (n + 1) (by omega)).1
    simp only [Nat.add_sub_cancel] at this; push_cast at *; linarith

lemma s_n_bddAbove_from2 (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    BddAbove (Set.range (fun n => s_n p (n + 2))) :=
  ⟨1 - p, fun _ ⟨n, hn⟩ => hn ▸ s_n_upper p hp₀ hp₁ (n + 2)⟩

/-- s(p) = lim_{n→∞} s_n(p) = sup_{n ≥ 2} s_n(p). -/
noncomputable def s (p : ℝ) : ℝ := ⨆ n, s_n p (n + 2)

lemma s_le_one_sub (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : s p ≤ 1 - p :=
  ciSup_le fun n => s_n_upper p hp₀ hp₁ (n + 2)

lemma s_n_le_s (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    s_n p n ≤ s p := by
  show s_n p n ≤ ⨆ k, s_n p (k + 2)
  convert le_ciSup (s_n_bddAbove_from2 p hp₀ hp₁) (n - 2) using 1; congr 1; omega

lemma s_nonneg_of_phi_le (p : ℝ) (hp : (Real.sqrt 5 - 1) / 2 ≤ p) (hp₁ : p < 1) :
    0 ≤ s p :=
  le_trans (s_n_nonneg_of_phi_le p hp hp₁ 2 le_rfl)
    (s_n_le_s p (by linarith [phi_pos']) hp₁.le 2 le_rfl)

/-- s_2(p) = -p³ + 2p - 1. -/
lemma s_n_two_val (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    s_n p 2 = -p ^ 3 + 2 * p - 1 := by
  simp only [s_n]; rw [v_two p hp₀ hp₁]; push_cast; ring

lemma s_n_two_neg (p : ℝ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hphi : p < (Real.sqrt 5 - 1) / 2) : s_n p 2 < 0 := by
  have h_eq := s_n_two_val p (by linarith) hp₁.le
  rw [h_eq]
  have h1 : 0 < 1 - p := by linarith
  have h2 : p ^ 2 + p - 1 < 0 := by nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]
  linarith [mul_neg_of_pos_of_neg h1 h2,
    show -p ^ 3 + 2 * p - 1 = (1 - p) * (p ^ 2 + p - 1) from by ring]

lemma s_pos_of_phi_lt (p : ℝ) (hp : (Real.sqrt 5 - 1) / 2 < p) (hp₁ : p < 1) :
    0 < s p := by
  have hp₀ : 0 < p := by linarith [phi_pos']
  have h2 : 0 < s_n p 2 := by
    have h_eq := s_n_two_val p hp₀.le hp₁.le
    rw [h_eq]
    have hp2 : p ^ 2 + p - 1 > 0 := by nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]
    nlinarith [hp2, sq_nonneg p, sq_nonneg (p - 1)]
  exact lt_of_lt_of_le h2 (s_n_le_s p hp₀.le hp₁.le 2 le_rfl)

lemma s_pos_at_phi : 0 < s ((Real.sqrt 5 - 1) / 2) := by
  refine' lt_of_lt_of_le _ ( le_ciSup _ 1 );
  · unfold s_n;
    rw [ v_simplified_recurrence ] <;> norm_num;
    · rw [ v_two ] <;> ring_nf <;> norm_num;
      · nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), pow_pos ( Real.sqrt_pos.mpr ( show 0 < 5 by norm_num ) ) 3, pow_pos ( Real.sqrt_pos.mpr ( show 0 < 5 by norm_num ) ) 4, pow_pos ( Real.sqrt_pos.mpr ( show 0 < 5 by norm_num ) ) 5 ];
      · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
    · nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
    · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
    · intro k hk₁ hk₂; interval_cases k ; norm_num [ v_one, v_two ] ;
      rw [ v_two ] <;> nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
    · unfold s_n; norm_num [ v_two ] ; ring_nf; norm_num;
      rw [ v_two ] <;> ring_nf <;> norm_num;
      · nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
  · exact s_n_bddAbove_from2 _ ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] )

/-! ### eta = -s_n relation -/

lemma eta_neg_s_n (p : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    eta p n = -(s_n p (n - 1)) := by
  simp only [eta, s_n]
  push_cast [Nat.cast_sub (show 2 ≤ n from hn), Nat.cast_sub (show 1 ≤ n from by omega)]
  ring

lemma tendsto_s_n (p : ℝ) (hp : 1 / 2 ≤ p) (hp₁ : p < 1) :
    Filter.Tendsto (fun n => s_n p (n + 2)) Filter.atTop (nhds (s p)) := by
      apply_rules [ tendsto_atTop_ciSup ];
      · exact monotone_nat_of_le_succ fun n => s_n_mono p hp hp₁ _ ( by linarith );
      · exact s_n_bddAbove_from2 p ( by linarith ) ( by linarith )

/-! ## s_n recurrence under strategy B -/

/-- D(p, n) = (1-p) - s_n(p, n-1), relating D to s_n. -/
lemma D_eq_one_sub_p_sub_s_n (p : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    D p n = (1 - p) - s_n p (n - 1) := by
  simp only [D, s_n]
  push_cast [Nat.cast_sub (show 1 ≤ n from by omega)]
  ring

/-
The recurrence for s_n when strategy B is used (s_n(n-1) < 0).
-/
lemma s_n_recurrence_stratB (p : ℝ) (n : ℕ) (hn : 3 ≤ n) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hs : s_n p (n - 1) < 0) :
    s_n p n = s_n p (n - 1) * (1 - alpha p n) + p ^ n * (1 - p) - (1 - p) ^ n := by
  unfold s_n alpha;
  -- Expand the right-hand side of the equation.
  unfold s_n at hs;
  rcases n <;> simp_all +decide [ pow_succ' ];
  rename_i n;
  rw [ reduced_recurrence ] <;> try linarith;
  · unfold D eta; norm_num [ pow_succ' ] ; ring_nf;
    rw [ max_eq_right ] <;> norm_num [ Nat.cast_sub ( by linarith : 2 ≤ 1 + n ) ] <;> nlinarith;
  · intro k hk₁ hk₂;
    apply v_sub_v_sub_one_ge_one_of_half_le p k (by linarith) (by linarith) (by linarith) |> fun h => by
      exact sub_nonneg_of_le ( by linarith! )

/-- At p = 1/2, the constant term p^n*(1-p) - (1-p)^n = -(1/2)^{n+1}. -/
lemma half_const_term (n : ℕ) :
    (1/2 : ℝ) ^ n * (1 - 1/2) - (1 - 1/2) ^ n = -(1/2 : ℝ) ^ (n + 1) := by
  ring

/-
At p = 1/2, alpha(1/2, n) = (n+1) * (1/2)^n.
-/
lemma alpha_half (n : ℕ) :
    alpha (1/2 : ℝ) n = (↑n + 1) * (1/2 : ℝ) ^ n := by
  unfold alpha;
  cases n <;> norm_num [ pow_succ' ] ; ring

/-
For n ≥ 2, (n+1) * (1/2)^n < 1, so 1 - alpha(1/2, n) > 0.
-/
lemma one_sub_alpha_half_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < 1 - (↑n + 1 : ℝ) * (1/2 : ℝ) ^ n := by
  induction hn <;> norm_num [ pow_succ' ] at *;
  nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ ↑‹ℕ› ) ]

/-
s_n(1/2, n) < 0 for all n ≥ 2.
-/
lemma s_n_half_neg (n : ℕ) (hn : 2 ≤ n) :
    s_n (1/2 : ℝ) n < 0 := by
  induction' n using Nat.strong_induction_on with n ih;
  by_cases hn3 : 3 ≤ n;
  · have := ih ( n - 1 ) ( Nat.sub_lt ( by linarith ) ( by linarith ) ) ( Nat.le_sub_one_of_lt hn3 );
    rw [ s_n_recurrence_stratB ] <;> norm_num at *;
    · rw [ alpha_half ];
      nlinarith [ one_sub_alpha_half_pos n hn, pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) n ];
    · linarith;
    · linarith;
  · interval_cases n ; norm_num [ s_n, v_two ]

/-
s_n(1/2, n) ≥ s_n(1/2, 2) = -1/8, from monotonicity.
-/
lemma s_n_half_ge_neg_eighth (n : ℕ) (hn : 2 ≤ n) :
    -1/8 ≤ s_n (1/2 : ℝ) n := by
  induction hn <;> norm_num at *;
  · unfold s_n;
    norm_num [ v_two ];
  · exact le_trans ‹_› ( s_n_mono _ ( by norm_num ) ( by norm_num ) _ ( by linarith ) )

/-
Partial sum identity: ∑_{j=0}^{m} j * (1/2)^j = 2 - (m+2) * (1/2)^m.
-/
lemma partial_sum_identity (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (↑j : ℝ) * (1/2 : ℝ) ^ j = 2 - (↑m + 2) * (1/2 : ℝ) ^ m := by
  induction m <;> norm_num [ Finset.sum_range_succ, pow_succ' ] at * ; linarith

/-
Uniform upper bound: s_n(1/2, n) ≤ -3/32 for all n ≥ 2.
-/
lemma s_n_half_le_neg (n : ℕ) (hn : 2 ≤ n) :
    s_n (1/2 : ℝ) n ≤ -3/32 := by
  -- By the recurrence relation, we have $s_n(n+1) = s_n(n) + (n-2)/(8*2^{n+1})$.
  have h_recurrence : ∀ n ≥ 2, s_n (1 / 2) (n + 1) ≤ s_n (1 / 2) n + (n - 2 : ℝ) / (8 * 2 ^ (n + 1)) := by
    intros n hn
    have h_s_n_recurrence : s_n (1 / 2) (n + 1) = s_n (1 / 2) n * (1 - alpha (1 / 2) (n + 1)) + (1 / 2 : ℝ) ^ (n + 1) * (1 - 1 / 2) - (1 - 1 / 2) ^ (n + 1) := by
      convert s_n_recurrence_stratB ( 1 / 2 ) ( n + 1 ) ( by linarith ) ( by norm_num ) ( by norm_num ) _ using 1;
      exact s_n_half_neg _ hn;
    rw [ h_s_n_recurrence, alpha_half ] ; ring_nf ; norm_num;
    nlinarith only [ show ( 0 : ℝ ) ≤ ( 1 / 2 ) ^ n by positivity, show ( n : ℝ ) ≥ 2 by norm_cast, show ( s_n ( 1 / 2 ) n : ℝ ) ≥ -1 / 8 by exact_mod_cast s_n_half_ge_neg_eighth n hn, show ( s_n ( 1 / 2 ) n : ℝ ) ≤ 0 by exact_mod_cast s_n_half_neg n hn |> le_of_lt, pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) n, mul_le_mul_of_nonneg_right ( show ( n : ℝ ) ≥ 2 by norm_cast ) ( pow_nonneg ( by norm_num : ( 0 : ℝ ) ≤ 1 / 2 ) n ) ];
  -- By induction, we can show that $s_n(n) \leq -1/8 + (1/64) \sum_{j=0}^{n-3} j/2^j$.
  have h_induction : ∀ n ≥ 2, s_n (1 / 2) n ≤ -1 / 8 + (1 / 64) * ∑ j ∈ Finset.range (n - 2), (j : ℝ) / 2 ^ j := by
    intro n hn
    induction' n, hn using Nat.le_induction with n hn ih;
    · unfold s_n; norm_num [ v_two ] ;
    · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finset.sum_range_succ ];
      convert le_trans ( h_recurrence ( n + 2 ) ( by linarith ) ) ( add_le_add ih le_rfl ) using 1 ; ring_nf;
      norm_num [ mul_comm ] ; ring;
  -- By the partial sum identity, we have $\sum_{j=0}^{n-3} j/2^j \leq 2$.
  have h_partial_sum : ∀ n ≥ 2, ∑ j ∈ Finset.range (n - 2), (j : ℝ) / 2 ^ j ≤ 2 := by
    intro n hn;
    have := partial_sum_identity ( n - 2 );
    simp_all +decide [ div_eq_mul_inv, Finset.sum_range_succ ];
    nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, inv_pos.mpr ( pow_pos ( zero_lt_two' ℝ ) ( n - 2 ) ) ];
  linarith [ h_induction n hn, h_partial_sum n hn ]

lemma s_neg_at_half : s (1/2 : ℝ) < 0 := by
  have h : s (1/2 : ℝ) ≤ -3/32 := ciSup_le fun n => s_n_half_le_neg (n + 2) (by omega)
  linarith

/-
v(·, n) is continuous for each fixed n.
-/
lemma v_continuous (n : ℕ) : Continuous (fun p => v p n) := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | n ) <;> simp_all +decide [ v ];
  · exact continuous_const;
  · refine' continuous_finset_sum _ fun h _ => Continuous.mul _ _;
    · exact Continuous.mul ( Continuous.mul ( continuous_const ) ( continuous_pow _ ) ) ( continuous_const.sub continuous_id' |> Continuous.pow <| _ );
    · refine' continuous_iff_continuousAt.mpr _;
      intro x;
      refine' tendsto_order.2 ⟨ _, _ ⟩;
      · intro a' ha';
        simp_all +decide;
        obtain ⟨ b, hb ⟩ := ha';
        exact Filter.eventually_of_mem ( IsOpen.mem_nhds ( isOpen_lt continuous_const ( show Continuous fun p => ↑ ( bestHeadsAside ( n + 1 ) h ↑b ) + v p ↑b from Continuous.add continuous_const ( ih _ ( by linarith [ Fin.is_lt b ] ) ) ) ) hb ) fun p hp => ⟨ b, hp ⟩;
      · intro a ha;
        simp_all +decide [ Finset.sup'_lt_iff ];
        exact fun i => ContinuousAt.preimage_mem_nhds ( show ContinuousAt ( fun p => ↑ ( bestHeadsAside ( n + 1 ) h ↑i ) + v p ↑i ) x from ContinuousAt.add continuousAt_const <| ih _ ( by linarith [ Fin.is_lt i ] ) |> Continuous.continuousAt ) <| Iio_mem_nhds <| ha i

/-
s_n(·, k) is continuous for each fixed k.
-/
lemma s_n_continuous (k : ℕ) : Continuous (fun p => s_n p k) := by
  exact Continuous.sub ( Continuous.add ( Continuous.sub ( v_continuous k ) continuous_const ) continuous_const ) continuous_id

/-
Upper bound on delta: 0 ≤ delta(p, k) ≤ (k-1) for p ∈ [0,1].
-/
set_option maxHeartbeats 1600000 in
lemma delta_le_D (p : ℝ) (k : ℕ) (hk : 3 ≤ k) (hp : 1/2 ≤ p) (hp₁ : p < 1) :
    v p k - v p (k-1) - 1 ≤ p ^ k * (↑(k-1)) + ↑k * p ^ (k-1) * (1-p) * (↑(k-1)) := by
  -- By definition of $D$ and $eta$, we know that $D p k \leq (k - 1)$ and $max 0 (eta p k) \leq (k - 1)$.
  have hD_eta_bounds : D p k ≤ (k - 1 : ℝ) ∧ max 0 (eta p k) ≤ (k - 1 : ℝ) := by
    unfold D eta;
    rcases k with ( _ | _ | k ) <;> norm_num at *;
    have hv := v_nonneg (k + 1) p (by linarith) hp₁.le
    exact ⟨by norm_cast, by
      grind⟩
  -- Apply the reduced_recurrence lemma to express v p k in terms of v p (k-1) and other terms.
  have h_recurrence : v p k = v p (k - 1) + 1 + p ^ k * D p k + k * p ^ (k - 1) * (1 - p) * max 0 (eta p k) - (1 - p) ^ k := by
    apply reduced_recurrence p k (by linarith) (by linarith) (by linarith);
    intro n hn hn'; exact sub_nonneg_of_le <| by linarith [ v_sub_v_sub_one_ge_one_of_half_le p n hn ( by linarith ) ( by linarith ) ] ;
  rw [ Nat.cast_pred ( by linarith ) ];
  nlinarith [ show 0 ≤ p ^ k by positivity, show 0 ≤ p ^ ( k - 1 ) * ( 1 - p ) by exact mul_nonneg ( pow_nonneg ( by linarith ) _ ) ( by linarith ), show 0 ≤ ( k : ℝ ) * p ^ ( k - 1 ) * ( 1 - p ) by exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by linarith ) _ ) ) ( by linarith ), pow_nonneg ( by linarith : 0 ≤ 1 - p ) k ]

lemma s_continuousOn : ContinuousOn s (Set.Ioo (1/2) 1) := by
  intro p hp;
  -- Let's choose any two points $a, b \in (1/2, 1)$ with $a < b$.
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℝ, 1 / 2 < a ∧ a < p ∧ p < b ∧ b < 1 := by
    exact ⟨ ( p + 1 / 2 ) / 2, ( p + 1 ) / 2, by linarith [ hp.1 ], by linarith [ hp.1 ], by linarith [ hp.2 ], by linarith [ hp.2 ] ⟩;
  -- By the properties of the supremum and the fact that $s_n$ is monotone increasing, we have $s(p) - s_n(p, n+2) \leq \sum_{k=n+2}^\infty \delta_k$.
  have h_tail_bound : ∀ n : ℕ, ∀ p ∈ Set.Icc a b, s p - s_n p (n + 2) ≤ ∑' k : ℕ, (k + n + 3 : ℝ) ^ 2 * b ^ (k + n + 2) * 2 := by
    intros n p hp
    have h_tail_bound : s p - s_n p (n + 2) ≤ ∑' k : ℕ, (delta p (k + n + 3)) := by
      have h_tail_bound : ∀ m : ℕ, s_n p (m + n + 3) - s_n p (n + 2) = ∑ k ∈ Finset.range (m + 1), delta p (k + n + 3) := by
        intro m
        induction' m with m ih;
        · unfold s_n delta; norm_num; ring;
        · rw [ Finset.sum_range_succ, ← ih ];
          unfold delta s_n; ring_nf;
          rw [ show 4 + m + n - 1 = 3 + m + n by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; push_cast ; ring;
      have h_tail_bound : Filter.Tendsto (fun m => s_n p (m + n + 3) - s_n p (n + 2)) Filter.atTop (nhds (s p - s_n p (n + 2))) := by
        have h_tail_bound : Filter.Tendsto (fun m => s_n p (m + 2)) Filter.atTop (nhds (s p)) := by
          exact tendsto_s_n p ( by linarith [ hp.1 ] ) ( by linarith [ hp.2 ] );
        exact Filter.Tendsto.sub ( h_tail_bound.comp ( Filter.tendsto_add_atTop_nat ( n + 1 ) ) ) tendsto_const_nhds;
      have h_tail_bound : Summable (fun k : ℕ => delta p (k + n + 3)) := by
        rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
        · exact fun h => not_tendsto_atTop_of_tendsto_nhds h_tail_bound <| by simpa only [ * ] using h.comp <| Filter.tendsto_add_atTop_nat 1;
        · intros m
          apply v_sub_v_sub_one_ge_one_of_half_le p (m + n + 3) (by linarith) (by linarith [hp.1]) (by linarith [hp.2]) |> fun h => by
            exact sub_nonneg_of_le <| by linarith!;
      exact le_of_tendsto_of_tendsto' ‹_› ( h_tail_bound.hasSum.tendsto_sum_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) ) fun m => by aesop;
    have h_delta_bound : ∀ k : ℕ, delta p (k + n + 3) ≤ (k + n + 3 : ℝ) ^ 2 * b ^ (k + n + 2) * 2 := by
      intros k
      have h_delta_bound : delta p (k + n + 3) ≤ p ^ (k + n + 3) * (k + n + 2) + (k + n + 3) * p ^ (k + n + 2) * (1 - p) * (k + n + 2) := by
        have := delta_le_D p ( k + n + 3 ) ( by linarith ) ( by linarith [ hp.1 ] ) ( by linarith [ hp.2 ] );
        convert this using 1 ; norm_cast;
      refine le_trans h_delta_bound ?_;
      refine' le_trans ( add_le_add ( mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by linarith [ hp.1 ] ) hp.2 _ ) ( by positivity ) ) ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by linarith [ hp.1 ] ) hp.2 _ ) ( by linarith [ hp.1 ] ) ) ( by linarith [ hp.1, hp.2 ] ) ) ( by positivity ) ) ) _;
      rw [ show b ^ ( k + n + 3 ) = b ^ ( k + n + 2 ) * b by ring ];
      nlinarith [ show 0 ≤ b ^ ( k + n + 2 ) * ( k + n + 2 ) by exact mul_nonneg ( pow_nonneg ( by linarith [ hp.1 ] ) _ ) ( by positivity ), show 0 ≤ b ^ ( k + n + 2 ) * ( k + n + 3 ) by exact mul_nonneg ( pow_nonneg ( by linarith [ hp.1 ] ) _ ) ( by positivity ), show 0 ≤ b ^ ( k + n + 2 ) * ( k + n + 2 ) * ( k + n + 3 ) by exact mul_nonneg ( mul_nonneg ( pow_nonneg ( by linarith [ hp.1 ] ) _ ) ( by positivity ) ) ( by positivity ), hp.1, hp.2 ];
    refine' le_trans h_tail_bound ( Summable.tsum_le_tsum h_delta_bound _ _ );
    · have h_summable : Summable (fun k : ℕ => (k + n + 3 : ℝ) ^ 2 * b ^ (k + n + 2)) := by
        have h_summable : Summable (fun k : ℕ => (k : ℝ) ^ 2 * b ^ k) := by
          refine' summable_of_ratio_norm_eventually_le _ _;
          exact ( 1 + b ) / 2;
          · linarith;
          · -- We'll use the fact that |b| < 1 to find such an N.
            have h_eventually : ∃ N, ∀ n ≥ N, (n + 1 : ℝ) ^ 2 * b ≤ (1 + b) / 2 * n ^ 2 := by
              exact ⟨ 2 * ( 1 + b ) / ( 1 - b ), fun n hn => by nlinarith [ mul_div_cancel₀ ( 2 * ( 1 + b ) ) ( by linarith : ( 1 - b ) ≠ 0 ), sq_nonneg ( n - 2 * ( 1 + b ) / ( 1 - b ) ) ] ⟩;
            norm_num +zetaDelta at *;
            obtain ⟨ N, hN ⟩ := h_eventually; exact ⟨ ⌈N⌉₊, fun n hn => by rw [ abs_of_nonneg ( by linarith ) ] ; convert mul_le_mul_of_nonneg_right ( hN n ( Nat.le_of_ceil_le hn ) ) ( pow_nonneg ( by linarith : 0 ≤ b ) n ) using 1 <;> ring ⟩ ;
        have h_summable : Summable (fun k : ℕ => (k + n + 3 : ℝ) ^ 2 * b ^ (k + n + 3)) := by
          convert h_summable.comp_injective ( add_left_injective ( n + 3 ) ) using 2 ; norm_num ; ring;
        convert h_summable.mul_left ( 1 / b ) using 2 ; ring_nf;
        grind;
      refine' Summable.of_nonneg_of_le ( fun k => _ ) ( fun k => h_delta_bound k ) ( h_summable.mul_right 2 );
      apply v_sub_v_sub_one_ge_one_of_half_le p (k + n + 3) (by linarith) (by linarith [hp.1]) (by linarith [hp.2]) |> fun h => by
        exact sub_nonneg_of_le <| by linarith!;
    · have h_summable : Summable (fun k : ℕ => (k : ℝ) ^ 2 * b ^ k) := by
        refine' summable_of_ratio_norm_eventually_le _ _;
        exact ( 1 + b ) / 2;
        · linarith;
        · -- We'll use the fact that |b| < 1 to find such an N.
          have h_eventually : ∃ N, ∀ n ≥ N, (n + 1 : ℝ) ^ 2 * b ≤ (1 + b) / 2 * n ^ 2 := by
            exact ⟨ 2 * ( 1 + b ) / ( 1 - b ), fun n hn => by nlinarith [ mul_div_cancel₀ ( 2 * ( 1 + b ) ) ( by linarith : ( 1 - b ) ≠ 0 ), sq_nonneg ( n - 2 * ( 1 + b ) / ( 1 - b ) ) ] ⟩;
          norm_num +zetaDelta at *;
          obtain ⟨ N, hN ⟩ := h_eventually; exact ⟨ ⌈N⌉₊, fun n hn => by rw [ abs_of_nonneg ( by linarith ) ] ; convert mul_le_mul_of_nonneg_right ( hN n ( Nat.le_of_ceil_le hn ) ) ( pow_nonneg ( by linarith : 0 ≤ b ) n ) using 1 <;> ring ⟩ ;
      have h_summable : Summable (fun k : ℕ => (k + n + 3 : ℝ) ^ 2 * b ^ (k + n + 2)) := by
        have h_summable : Summable (fun k : ℕ => (k + n + 3 : ℝ) ^ 2 * b ^ (k + n + 3)) := by
          convert h_summable.comp_injective ( add_left_injective ( n + 3 ) ) using 2 ; norm_num ; ring;
        convert h_summable.mul_left ( 1 / b ) using 2 ; ring_nf;
        grind;
      exact h_summable.mul_right 2;
  -- The series $\sum_{k=n+2}^\infty (k+n+3)^2 b^{k+n+2}$ converges to 0 as $n \to \infty$.
  have h_series_zero : Filter.Tendsto (fun n : ℕ => ∑' k : ℕ, (k + n + 3 : ℝ) ^ 2 * b ^ (k + n + 2) * 2) Filter.atTop (nhds 0) := by
    convert tendsto_sum_nat_add fun k => ( k + 3 : ℝ ) ^ 2 * b ^ ( k + 2 ) * 2 using 1;
    norm_cast;
  -- By the properties of the supremum and the fact that $s_n$ is monotone increasing, we have $|s(p) - s_n(p, n+2)| \leq \sum_{k=n+2}^\infty \delta_k$.
  have h_abs_tail_bound : ∀ n : ℕ, ∀ p ∈ Set.Icc a b, |s p - s_n p (n + 2)| ≤ ∑' k : ℕ, (k + n + 3 : ℝ) ^ 2 * b ^ (k + n + 2) * 2 := by
    intros n p hp
    have h_abs : s p - s_n p (n + 2) ≥ 0 := by
      apply_rules [ sub_nonneg_of_le, s_n_le_s ];
      · linarith [ hp.1 ];
      · linarith [ hp.2 ];
      · linarith;
    rw [ abs_of_nonneg h_abs ] ; exact h_tail_bound n p hp;
  -- By the properties of the supremum and the fact that $s_n$ is monotone increasing, we have $s_n(p, n+2) \to s(p)$ uniformly on $[a, b]$.
  have h_uniform_converge : TendstoUniformlyOn (fun n : ℕ => fun p : ℝ => s_n p (n + 2)) s Filter.atTop (Set.Icc a b) := by
    rw [ Metric.tendstoUniformlyOn_iff ];
    exact fun ε ε_pos => by rcases Metric.tendsto_atTop.mp h_series_zero ε ε_pos with ⟨ N, hN ⟩ ; exact Filter.eventually_atTop.mpr ⟨ N, fun n hn x hx => lt_of_le_of_lt ( h_abs_tail_bound n x hx ) ( by linarith [ abs_lt.mp ( hN n hn ) ] ) ⟩ ;
  have h_cont : ContinuousOn s (Set.Icc a b) := by
    apply_rules [ h_uniform_converge.continuousOn ];
    exact Filter.Eventually.frequently ( Filter.Eventually.of_forall fun n => s_n_continuous ( n + 2 ) |> Continuous.continuousOn );
  exact h_cont.continuousAt ( Icc_mem_nhds ( by linarith ) ( by linarith ) ) |> ContinuousAt.continuousWithinAt

/-
s is continuous on [1/2, 1), extending s_continuousOn to the left endpoint.
-/
lemma s_continuousOn_Ico : ContinuousOn s (Set.Ico (1/2 : ℝ) 1) := by
  have hs_cont : ContinuousOn s (Set.Ioo (1 / 2) 1) := s_continuousOn
  have hs_cont_at_half : ContinuousWithinAt s (Set.Ici (1 / 2)) (1 / 2) := by
    -- We show TendstoUniformlyOn (fun n p => s_n p (n+2)) s atTop (Set.Icc (1/2) (3/4)).
    have hs_unif_cont : TendstoUniformlyOn (fun n p => s_n p (n + 2)) s Filter.atTop (Set.Icc (1 / 2 : ℝ) (3 / 4)) := by
      -- We use the fact that the series $\sum_{k=0}^{\infty} \delta_k(p)$ converges uniformly on $[1/2, 3/4]$.
      have h_series_uniform : TendstoUniformlyOn (fun n p => ∑ k ∈ Finset.range n, (v p (k + 3) - v p (k + 2) - 1)) (fun p => s p - s_n p 2) Filter.atTop (Set.Icc (1 / 2 : ℝ) (3 / 4)) := by
        -- We use the Weierstrass M-test to show uniform convergence.
        have h_weierstrass : ∀ k : ℕ, ∀ p ∈ Set.Icc (1 / 2 : ℝ) (3 / 4), abs (v p (k + 3) - v p (k + 2) - 1) ≤ (k + 3) ^ 2 * (3 / 4) ^ (k + 2) := by
          intros k p hp
          have h_delta_le : v p (k + 3) - v p (k + 2) - 1 ≤ p ^ (k + 3) * (k + 2) + (k + 3) * p ^ (k + 2) * (1 - p) * (k + 2) := by
            have := delta_le_D p ( k + 3 ) ( by linarith ) hp.1 ( by linarith [ hp.2 ] ) ; aesop;
          rw [ abs_of_nonneg ];
          · refine le_trans h_delta_le ?_;
            refine' le_trans ( add_le_add ( mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by linarith [ hp.1 ] ) hp.2 _ ) ( by positivity ) ) ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by linarith [ hp.1 ] ) hp.2 _ ) ( by positivity ) ) ( by linarith [ hp.1, hp.2 ] ) ) ( by positivity ) ) ) _;
            norm_num [ pow_succ' ];
            nlinarith [ hp.1, hp.2, show ( 0 : ℝ ) ≤ ( 3 / 4 ) ^ k * ( k + 2 ) by positivity, show ( 0 : ℝ ) ≤ ( 3 / 4 ) ^ k * ( k + 3 ) by positivity, show ( 0 : ℝ ) ≤ ( 3 / 4 ) ^ k * ( k + 2 ) * ( k + 3 ) by positivity ];
          · have := v_sub_v_sub_one_ge_one_of_half_le p ( k + 3 ) ( by linarith ) hp.1 ( by linarith [ hp.2 ] ) ; norm_num at * ; linarith;
        have h_series_uniform : Summable (fun k : ℕ => (k + 3 : ℝ) ^ 2 * (3 / 4) ^ (k + 2)) := by
          refine' summable_of_ratio_norm_eventually_le _ _;
          exact 7 / 8;
          · norm_num;
          · norm_num +zetaDelta at *;
            exact ⟨ 20, fun n hn => by induction hn <;> norm_num [ pow_succ' ] at * ; nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 3 / 4 ) ‹_› ] ⟩;
        have h_uniform_converges : ∀ p ∈ Set.Icc (1 / 2 : ℝ) (3 / 4), Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (v p (k + 3) - v p (k + 2) - 1)) Filter.atTop (nhds (s p - s_n p 2)) := by
          intro p hp
          have h_series_converges : Filter.Tendsto (fun n => s_n p (n + 2)) Filter.atTop (nhds (s p)) := by
            apply tendsto_s_n; exact hp.left; exact hp.right.trans_lt (by norm_num);
          convert h_series_converges.sub_const ( s_n p 2 ) using 2 ; norm_num [ s_n ] ; ring_nf;
          induction ‹_› <;> simp_all +decide [ add_comm, add_left_comm, Finset.sum_range_succ ] ; ring_nf;
          grind;
        rw [ Metric.tendstoUniformlyOn_iff ];
        intro ε hε;
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, ∀ p ∈ Set.Icc (1 / 2 : ℝ) (3 / 4), abs (∑ k ∈ Finset.Ico n m, (v p (k + 3) - v p (k + 2) - 1)) < ε / 2 := by
          have h_uniform_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, ∑ k ∈ Finset.Ico n m, (k + 3 : ℝ) ^ 2 * (3 / 4) ^ (k + 2) < ε / 2 := by
            intro ε hε;
            have := Metric.tendsto_atTop.mp h_series_uniform.hasSum.tendsto_sum_nat;
            obtain ⟨ N, HN ⟩ := this ( ε / 4 ) ( by positivity );
            exact ⟨ N, fun n hn m hm => by rw [ Finset.sum_Ico_eq_sub _ hm ] ; linarith [ abs_lt.mp ( HN n hn ), abs_lt.mp ( HN m ( by linarith ) ) ] ⟩;
          exact Exists.elim ( h_uniform_converges ε hε ) fun N hN => ⟨ N, fun n hn m hm p hp => lt_of_le_of_lt ( Finset.abs_sum_le_sum_abs _ _ ) ( lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => h_weierstrass _ _ hp ) ( hN n hn m hm ) ) ⟩;
        filter_upwards [ Filter.eventually_ge_atTop N ] with n hn p hp;
        have := h_uniform_converges p hp;
        rcases Metric.tendsto_atTop.mp this ( ε / 2 ) ( half_pos hε ) with ⟨ m, hm ⟩;
        have := hN n hn ( Max.max n m ) ( le_max_left _ _ ) p hp;
        rw [ Finset.sum_Ico_eq_sub _ ( by linarith [ le_max_left n m, le_max_right n m ] ) ] at this;
        exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp this, abs_lt.mp ( hm ( Max.max n m ) ( le_max_right n m ) ) ], by linarith [ abs_lt.mp this, abs_lt.mp ( hm ( Max.max n m ) ( le_max_right n m ) ) ] ⟩;
      rw [ Metric.tendstoUniformlyOn_iff ] at *;
      intro ε hε; filter_upwards [ h_series_uniform ε hε ] with n hn; intro x hx; convert hn x hx using 1; simp +decide [s_n] ;
      rw [ show ( ∑ k ∈ Finset.range n, v x ( k + 3 ) ) = ( ∑ k ∈ Finset.range n, v x ( k + 2 ) ) + v x ( n + 2 ) - v x 2 by exact Nat.recOn n ( by norm_num ) fun n ihn => by norm_num [ Finset.sum_range_succ ] at * ; linarith ] ; ring_nf;
      rw [ dist_eq_norm, dist_eq_norm ] ; ring_nf;
    have hs_cont_at_half : ContinuousOn s (Set.Icc (1 / 2 : ℝ) (3 / 4)) := by
      apply_rules [ hs_unif_cont.continuousOn ];
      exact Filter.Eventually.frequently ( Filter.Eventually.of_forall fun n => s_n_continuous _ |> Continuous.continuousOn );
    have := hs_cont_at_half ( 1 / 2 ) ⟨ by norm_num, by norm_num ⟩ ; norm_num at *;
    exact this;
  intro x hx; cases hx.1.eq_or_lt <;> simp_all +decide [ ContinuousWithinAt ] ;
  exact hs_cont.continuousAt ( Ioo_mem_nhds ‹_› hx.2 ) |> fun h => h.mono_left inf_le_left

/-
Existence of a zero of s in (1/2, φ) via IVT.
-/
lemma prop2_existence :
    ∃ p₀ : ℝ, 1/2 < p₀ ∧ p₀ < (Real.sqrt 5 - 1) / 2 ∧ s p₀ = 0 := by
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ ∈ Set.Ioo (1 / 2 : ℝ) ((Real.sqrt 5 - 1) / 2), s p₀ = 0 := by
    apply_rules [ intermediate_value_Ioo, ContinuousOn.continuousWithinAt ] <;> norm_num [ * ];
    · nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
    · exact s_continuousOn_Ico.mono ( Set.Icc_subset_Ico_right ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) );
    · exact ⟨ s_neg_at_half, s_pos_at_phi ⟩;
  exact ⟨ p₀, hp₀.1.1, hp₀.1.2, hp₀.2 ⟩

/-! ### Recurrence for s_n when s_{n-1} ≤ 0 (includes equality case) -/

lemma s_n_recurrence_nonpos (p : ℝ) (n : ℕ) (hn : 3 ≤ n) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hs : s_n p (n - 1) ≤ 0) :
    s_n p n = s_n p (n - 1) * (1 - alpha p n) + p ^ n * (1 - p) - (1 - p) ^ n := by
      -- By definition of $s_n$, we have $s_n p n = v p n - n + 1 - p$.
      unfold s_n;
      rcases n with ( _ | _ | n ) <;> norm_num at *;
      rw [ reduced_recurrence ];
      · unfold alpha D eta s_n at *;
        grind;
      · linarith;
      · finiteness;
      · linarith;
      · exact fun k hk₁ hk₂ => v_sub_v_sub_one_ge_one_of_half_le p k hk₁ hp hp₁ |> fun h => by unfold delta; linarith;

/-! ### Comparison lemma infrastructure -/

/-
α(p,n) is strictly increasing in p for 0 < q < p < 1 and n ≥ 2.
-/
lemma alpha_strict_mono {q p : ℝ} {n : ℕ} (hq₀ : 0 < q) (hqp : q < p) (hp₁ : p < 1)
    (hn : 2 ≤ n) : alpha q n < alpha p n := by
      unfold alpha;
      -- We'll use the fact that the derivative of $f(x) = x^n + n x^{n-1}(1-x)$ is positive on $(0,1)$ for $n \geq 2$.
      have h_deriv_pos : ∀ x : ℝ, 0 < x → x < 1 → deriv (fun x : ℝ => x ^ n + n * x ^ (n - 1) * (1 - x)) x > 0 := by
        intro x hx₀ hx₁; rcases n with ( _ | _ | n ) <;> norm_num [ mul_assoc, mul_sub ] at *;
        nlinarith [ show 0 < ( n + 1 + 1 : ℝ ) * x ^ n by positivity, show 0 < ( n + 1 + 1 : ℝ ) * ( n + 1 ) * x ^ n by positivity, show 0 < ( n + 1 + 1 : ℝ ) * x ^ ( n + 1 ) by positivity, show 0 < ( n + 1 + 1 : ℝ ) * ( n + 1 ) * x ^ ( n + 1 ) by positivity, pow_pos hx₀ n, pow_succ' x n ];
      -- Apply the mean value theorem to the interval [q, p].
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo q p, deriv (fun x : ℝ => x ^ n + n * x ^ (n - 1) * (1 - x)) c = ( (fun x : ℝ => x ^ n + n * x ^ (n - 1) * (1 - x)) p - (fun x : ℝ => x ^ n + n * x ^ (n - 1) * (1 - x)) q ) / (p - q) := by
        apply_rules [ exists_deriv_eq_slope ];
        · fun_prop;
        · fun_prop;
      have := h_deriv_pos c ( by linarith [ hc.1.1 ] ) ( by linarith [ hc.1.2 ] ) ; rw [ hc.2, gt_iff_lt ] at this; rw [ lt_div_iff₀ ] at this <;> linarith;

/-
The "constant term" g(x) = x^n(1-x) - (1-x)^n is increasing on [1/2, φ] for n ≥ 2.
-/
lemma const_term_strict_mono {q p : ℝ} {n : ℕ} (hq : 1/2 ≤ q) (hqp : q < p)
    (hp : p ≤ (Real.sqrt 5 - 1) / 2) (hn : 2 ≤ n) :
    q ^ n * (1 - q) - (1 - q) ^ n < p ^ n * (1 - p) - (1 - p) ^ n := by
      -- By the mean value theorem, there exists $c \in (q, p)$ such that $g(p) - g(q) = g'(c)(p-q)$.
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo q p, deriv (fun x => x^n * (1 - x) - (1 - x)^n) c = (p^n * (1 - p) - (1 - p)^n - (q^n * (1 - q) - (1 - q)^n)) / (p - q) := by
        apply_rules [ exists_deriv_eq_slope ];
        · fun_prop;
        · fun_prop;
      have h_deriv_pos : deriv (fun x => x^n * (1 - x) - (1 - x)^n) c > 0 := by
        -- We'll use that $c \in (q, p)$ and $q, p \in [1/2, \phi]$ to show that the derivative is positive.
        have h_deriv_pos : deriv (fun x => x^n * (1 - x) - (1 - x)^n) c = c^(n-1) * (n - (n+1)*c) + n * (1 - c)^(n-1) := by
          norm_num [ mul_sub, sub_mul, mul_comm ];
          convert HasDerivAt.deriv ( HasDerivAt.sub ( HasDerivAt.sub ( hasDerivAt_pow n c ) ( HasDerivAt.mul ( hasDerivAt_id c ) ( hasDerivAt_pow n c ) ) ) ( HasDerivAt.comp c ( hasDerivAt_pow n ( 1 - c ) ) ( hasDerivAt_id c |> HasDerivAt.const_sub 1 ) ) ) using 1 ; ring_nf;
          cases n <;> norm_num [ pow_succ' ] at * ; linarith;
        -- Since $c \in (q, p)$ and $q, p \in [1/2, \phi]$, we have $c < \phi < 1$.
        have hc_lt_one : c < 1 := by
          nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), hc.1.2 ];
        exact h_deriv_pos.symm ▸ add_pos_of_nonneg_of_pos ( mul_nonneg ( pow_nonneg ( by linarith [ hc.1.1 ] ) _ ) ( by nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), hc.1.2 ] ) ) ( mul_pos ( by positivity ) ( pow_pos ( by linarith [ hc.1.1 ] ) _ ) );
      rw [ hc.2, gt_iff_lt, lt_div_iff₀ ] at h_deriv_pos <;> linarith

/-
For q < φ and n ≥ 2, α(q,n) < (n+1)·φ^n.
-/
lemma alpha_lt_succ_mul_phi_pow {q : ℝ} {n : ℕ} (hq₀ : 0 < q)
    (hq : q < (Real.sqrt 5 - 1) / 2) (hn : 2 ≤ n) :
    alpha q n < (↑n + 1) * ((Real.sqrt 5 - 1) / 2) ^ n := by
      refine lt_of_lt_of_le ( alpha_strict_mono hq₀ hq ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) hn ) ?_;
      unfold alpha;
      rcases n <;> simp_all +decide [ pow_succ' ];
      nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), pow_pos ( show 0 < ( Real.sqrt 5 - 1 ) / 2 by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ‹_›, mul_le_mul_of_nonneg_right ( show ( ↑‹ℕ› : ℝ ) ≥ 1 by norm_cast ) ( pow_nonneg ( show 0 ≤ ( Real.sqrt 5 - 1 ) / 2 by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ‹_› ) ]

/-
(n+1)·φ^n < 1 for n ≥ 3
-/
lemma succ_mul_phi_pow_lt_one (n : ℕ) (hn : 3 ≤ n) :
    (↑n + 1) * ((Real.sqrt 5 - 1) / 2) ^ n < 1 := by
      induction hn <;> norm_num [ pow_succ' ];
      · nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      · rename_i k hk ih;
        have h_frac_lt_one : ((k + 2) / (k + 1) : ℝ) * ((Real.sqrt 5 - 1) / 2) < 1 := by
          rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), show ( k : ℝ ) ≥ 3 by norm_cast ];
        rw [ div_mul_eq_mul_div, div_lt_iff₀ ] at h_frac_lt_one <;> nlinarith [ pow_pos ( show 0 < ( Real.sqrt 5 - 1 ) / 2 by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) k ]

/-! ### The dipvsdiq comparison lemma -/

/-- C_n = (5/6) * ∏_{j=3}^{n} (1 - (j+1)φ^j) -/
noncomputable def C_prod (n : ℕ) : ℝ :=
  (5/6 : ℝ) * ∏ j ∈ Finset.Icc 3 n, (1 - (↑j + 1) * ((Real.sqrt 5 - 1) / 2) ^ j)

lemma C_prod_two : C_prod 2 = 5/6 := by
  simp [C_prod]

lemma C_prod_pos (n : ℕ) (_hn : 2 ≤ n) : 0 < C_prod n := by
  exact mul_pos ( by norm_num ) ( Finset.prod_pos fun x hx => sub_pos_of_lt ( by have := succ_mul_phi_pow_lt_one x ( Finset.mem_Icc.mp hx |>.1 ) ; nlinarith ) )

/-
Key comparison: for 1/2 ≤ q < p < φ, if s_{n-1}(p) ≤ 0 then
    s_n(p) > s_n(q) + C_n(p - q).
-/
lemma dipvsdiq (q p : ℝ) (n : ℕ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hp : p < (Real.sqrt 5 - 1) / 2) (hn : 2 ≤ n)
    (hs_all : ∀ k, 2 ≤ k → k ≤ n → s_n p (k - 1) ≤ 0) :
    s_n p n > s_n q n + C_prod n * (p - q) := by
      induction hn <;> simp_all +decide [ C_prod ];
      · unfold s_n at *;
        rw [ v_two, v_two ] <;> try linarith;
        · nlinarith [ mul_pos ( sub_pos.mpr hqp ) ( sub_pos.mpr hp ), mul_pos ( sub_pos.mpr hqp ) ( sub_pos.mpr ( show q > 0 by linarith ) ), mul_pos ( sub_pos.mpr hp ) ( sub_pos.mpr ( show q > 0 by linarith ) ), sq_nonneg ( p - q ), sq_nonneg ( p + q - 1 ), Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
        · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
        · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      · rename_i k hk ih;
        -- Since $s_{k}(p) \leq 0$ and $s_{k}(q) < s_{k}(p) - C_{k}(p-q) \leq -C_{k}(p-q) < 0$, both $s_{k}(p) \leq 0$ and $s_{k}(q) < 0$.
        have hs_k_p : s_n p k ≤ 0 := by
          exact hs_all ( k + 1 ) ( by linarith ) ( by linarith )
        have hs_k_q : s_n q k < 0 := by
          nlinarith [ ih fun n hn₁ hn₂ => hs_all n hn₁ ( by linarith ), show 0 < ( 5 / 6 * ∏ j ∈ Icc 3 k, ( 1 - ( j + 1 ) * ( ( Real.sqrt 5 - 1 ) / 2 ) ^ j ) ) by exact mul_pos ( by norm_num ) ( Finset.prod_pos fun j hj => sub_pos.mpr <| by
                                                                          exact succ_mul_phi_pow_lt_one j ( by linarith [ Finset.mem_Icc.mp hj ] ) ) ];
        -- By `s_n_recurrence_nonpos` (for p) and `s_n_recurrence_stratB` (for q, since $s_{k}(q) < 0$):
        have h_recurrence_p : s_n p (k + 1) = s_n p k * (1 - alpha p (k + 1)) + p ^ (k + 1) * (1 - p) - (1 - p) ^ (k + 1) := by
          apply s_n_recurrence_nonpos;
          · linarith;
          · grind;
          · exact hp.trans_le <| by nlinarith [ Real.sq_sqrt <| show 0 ≤ 5 by norm_num ] ;
          · exact hs_k_p
        have h_recurrence_q : s_n q (k + 1) = s_n q k * (1 - alpha q (k + 1)) + q ^ (k + 1) * (1 - q) - (1 - q) ^ (k + 1) := by
          apply s_n_recurrence_stratB;
          · linarith;
          · exact le_trans ( by norm_num ) hq;
          · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
          · exact hs_k_q;
        -- Since $s_{k}(p) \leq 0$ and $1 - \alpha(p, k+1) > 0$, we have $s_{k}(p) * (1 - \alpha(p, k+1)) \geq s_{k}(p) * (1 - \alpha(q, k+1))$.
        have h_ineq1 : s_n p k * (1 - alpha p (k + 1)) ≥ s_n p k * (1 - alpha q (k + 1)) := by
          have h_ineq1 : alpha p (k + 1) ≥ alpha q (k + 1) := by
            apply le_of_lt; exact alpha_strict_mono (by
            positivity) (by
            linarith) (by
            exact hp.trans_le <| by nlinarith only [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ;) (by
            linarith);
          exact mul_le_mul_of_nonpos_left ( by linarith ) hs_k_p;
        -- Since $1 - \alpha(q, k+1) > 0$, we can divide both sides of the inequality by it.
        have h_div : s_n p k * (1 - alpha q (k + 1)) > (s_n q k + (5 / 6 * ∏ j ∈ Icc 3 k, (1 - (j + 1) * ((Real.sqrt 5 - 1) / 2) ^ j)) * (p - q)) * (1 - alpha q (k + 1)) := by
          apply mul_lt_mul_of_pos_right (ih (fun k hk₁ hk₂ => hs_all k hk₁ (by linarith))) (by
          apply_rules [ sub_pos.mpr, alpha_lt_one ];
          · positivity;
          · exact hqp.trans_le ( hp.le.trans ( by nlinarith only [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) );
          · linarith);
        -- Since $1 - \alpha(q, k+1) > 0$, we can divide both sides of the inequality by it and simplify.
        have h_div_simplified : p ^ (k + 1) * (1 - p) - (1 - p) ^ (k + 1) ≥ q ^ (k + 1) * (1 - q) - (1 - q) ^ (k + 1) := by
          have := const_term_strict_mono ( show 1 / 2 ≤ q by linarith ) hqp ( show p ≤ ( Real.sqrt 5 - 1 ) / 2 by linarith ) ( show 2 ≤ k + 1 by linarith ) ; norm_num at * ; linarith;
        rw [ show ( Finset.Icc 3 ( k + 1 ) ) = Finset.Icc 3 k ∪ { ( k + 1 ) } from ?_, Finset.prod_union ] <;> norm_num at *;
        · have h_alpha_lt : alpha q (k + 1) < (k + 1 + 1) * ((Real.sqrt 5 - 1) / 2) ^ (k + 1) := by
            convert alpha_lt_succ_mul_phi_pow ( show 0 < q by linarith ) ( show q < ( Real.sqrt 5 - 1 ) / 2 by linarith ) ( show 2 ≤ k + 1 by linarith ) using 1 ; norm_num [ alpha ];
          nlinarith [ show 0 < ( 5 / 6 : ℝ ) * ( ∏ j ∈ Icc 3 k, ( 1 - ( j + 1 ) * ( ( Real.sqrt 5 - 1 ) / 2 ) ^ j ) ) * ( p - q ) by exact mul_pos ( mul_pos ( by norm_num ) ( Finset.prod_pos fun x hx => sub_pos.mpr <| by
                        exact lt_of_lt_of_le ( succ_mul_phi_pow_lt_one x ( by linarith [ Finset.mem_Icc.mp hx ] ) ) ( by norm_num ) ) ) ( sub_pos.mpr hqp ) ];
        · grind

/-! ### Uniform lower bound for C_prod -/

lemma C_prod_antitone : Antitone C_prod := by
  refine' antitone_nat_of_succ_le _;
  intro n; unfold C_prod; simp +decide [(Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)] ;
  rcases n with ( _ | _ | n ) <;> norm_num [ Finset.prod_Ioc_succ_top ];
  refine' mul_le_of_le_one_right ( Finset.prod_nonneg fun x hx => sub_nonneg.2 _ ) _;
  · exact le_of_lt ( succ_mul_phi_pow_lt_one x ( by linarith [ Finset.mem_Ioc.mp hx ] ) );
  · exact sub_le_self _ ( mul_nonneg ( by positivity ) ( pow_nonneg ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) _ ) )

/-
The Weierstrass product inequality: ∏(1-x_j) ≥ 1 - ∑x_j for x_j ∈ [0,1].
-/
lemma weierstrass_prod_bound (s : Finset ℕ) (f : ℕ → ℝ)
    (hf0 : ∀ j ∈ s, 0 ≤ f j) (hf1 : ∀ j ∈ s, f j ≤ 1) :
    1 - s.sum f ≤ ∏ j ∈ s, (1 - f j) := by
      induction s using Finset.induction <;> simp_all +decide [ Finset.sum_insert, Finset.prod_insert ];
      nlinarith [ hf0.1, hf1.1, show ∑ x ∈ ‹Finset ℕ›, f x ≥ 0 from Finset.sum_nonneg fun x hx => hf0.2 x hx, show ∏ x ∈ ‹Finset ℕ›, ( 1 - f x ) ≤ 1 from Finset.prod_le_one ( fun x hx => sub_nonneg.2 ( hf1.2 x hx ) ) fun x hx => sub_le_self _ ( hf0.2 x hx ) ]

/-
For all n ≥ 8: ∑_{j=8}^{n} (j+1)φ^j < 2/3.
-/
lemma tail_phi_sum_bound (n : ℕ) :
    ∑ j ∈ Finset.Icc 8 n, (↑j + 1) * ((Real.sqrt 5 - 1) / 2) ^ j ≤ 2/3 := by
      by_contra h;
      -- We can bound the sum by noting that $(j + 1) \phi^j \leq (j + 1) \left(\frac{5}{8}\right)^j$ for all $j \geq 8$.
      have h_bound : ∀ j ∈ Finset.Icc 8 n, (j + 1) * ((Real.sqrt 5 - 1) / 2) ^ j ≤ (j + 1) * (5 / 8) ^ j := by
        exact fun j hj => mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) _ ) ( by positivity );
      -- We can bound the sum $\sum_{j=0}^{n} (j + 1) \left(\frac{5}{8}\right)^j$ by noting that it is a geometric series.
      have h_geo_sum : ∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), (j + 1) * (5 / 8 : ℝ) ^ j ≤ 64 / 9 := by
        intro n
        have h_geo_sum : ∑ j ∈ Finset.range (n + 1), (j + 1) * (5 / 8 : ℝ) ^ j = (1 - (5 / 8 : ℝ) ^ (n + 1)) / (1 - 5 / 8) ^ 2 - (n + 1) * (5 / 8 : ℝ) ^ (n + 1) / (1 - 5 / 8) := by
          induction n <;> norm_num [ pow_succ, Finset.sum_range_succ ] at * ; linarith;
        rw [ h_geo_sum ] ; ring_nf ; norm_num;
        nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 5 / 8 ) n ];
      -- Applying the bound to the sum, we get $\sum_{j=8}^{n} (j + 1) \left(\frac{5}{8}\right)^j \leq \sum_{j=0}^{n} (j + 1) \left(\frac{5}{8}\right)^j - \sum_{j=0}^{7} (j + 1) \left(\frac{5}{8}\right)^j$.
      have h_sum_bound : ∑ j ∈ Finset.Icc 8 n, (j + 1) * (5 / 8 : ℝ) ^ j ≤ ∑ j ∈ Finset.range (n + 1), (j + 1) * (5 / 8 : ℝ) ^ j - ∑ j ∈ Finset.range 8, (j + 1) * (5 / 8 : ℝ) ^ j := by
        erw [ Finset.sum_Ico_eq_sub _ _ ];
        exact Nat.succ_le_succ ( le_of_not_gt fun hn => h <| by interval_cases n <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at * );
      exact h ( le_trans ( Finset.sum_le_sum h_bound ) ( h_sum_bound.trans ( by have := h_geo_sum n; norm_num at *; linarith ) ) )

/-
C_prod(n) is uniformly bounded below by a positive constant.
-/
lemma C_prod_uniform_lower : ∃ C > 0, ∀ n, 2 ≤ n → C ≤ C_prod n := by
  -- Let's choose $C = \frac{C_{prod}(7)}{3}$.
  use C_prod 7 / 3;
  refine' ⟨ div_pos ( C_prod_pos 7 ( by norm_num ) ) ( by norm_num ), _ ⟩;
  intro n hn
  by_cases hn_le_7 : n ≤ 7;
  · exact le_trans ( div_le_self ( by exact C_prod_pos _ ( by linarith ) |> le_of_lt ) ( by norm_num ) ) ( C_prod_antitone hn_le_7 );
  · -- Since $n \geq 8$, we can write $C_prod n$ as $C_prod 7 * \prod_{j=8}^{n} (1 - (j+1)φ^j)$.
    have h_prod : C_prod n = C_prod 7 * ∏ j ∈ Finset.Icc 8 n, (1 - (j + 1) * ((Real.sqrt 5 - 1) / 2) ^ j) := by
      unfold C_prod;
      rw [ mul_assoc, ← Finset.prod_union ( Finset.disjoint_right.mpr fun x hx => by aesop ), ];
      rw [ show ( Icc 3 n : Finset ℕ ) = Icc 3 7 ∪ Icc 8 n from ?_ ];
      exact Eq.symm ( Finset.Ico_union_Ico_eq_Ico ( by norm_num ) ( by linarith ) );
    -- By weierstrass_prod_bound, we have $\prod_{j=8}^{n} (1 - (j+1)φ^j) \geq 1 - \sum_{j=8}^{n} (j+1)φ^j$.
    have h_weierstrass : ∏ j ∈ Finset.Icc 8 n, (1 - (j + 1) * ((Real.sqrt 5 - 1) / 2) ^ j) ≥ 1 - ∑ j ∈ Finset.Icc 8 n, (j + 1) * ((Real.sqrt 5 - 1) / 2) ^ j := by
      apply weierstrass_prod_bound;
      · exact fun j hj => mul_nonneg ( by positivity ) ( pow_nonneg ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) _ );
      · exact fun j hj => le_of_lt ( succ_mul_phi_pow_lt_one j ( by linarith [ Finset.mem_Icc.mp hj ] ) );
    nlinarith [ C_prod_pos 7 ( by norm_num ), tail_phi_sum_bound n ]

/-! ### Uniqueness of zero -/

lemma s_n_neg_of_s_zero (p : ℝ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hs : s p ≤ 0)
    (n : ℕ) (hn : 2 ≤ n) : s_n p n ≤ 0 :=
  le_trans (s_n_le_s p (by linarith) hp₁.le n hn) hs

lemma s_zero_unique (p₁ p₂ : ℝ) (hp₁ : 1/2 ≤ p₁) (hp₂ : p₂ < 1)
    (_hphi₁ : p₁ < (Real.sqrt 5 - 1) / 2)
    (hphi₂ : p₂ < (Real.sqrt 5 - 1) / 2)
    (hs₁ : s p₁ = 0) (hs₂ : s p₂ = 0)
    (hlt : p₁ < p₂) : False := by
      have hC_prod_uniform_lower : ∃ C > 0, ∀ n, 2 ≤ n → C ≤ C_prod n := by
        exact C_prod_uniform_lower
      -- Apply the dipvsdiq lemma to get the contradiction.
      obtain ⟨C, hC_pos, hC⟩ := hC_prod_uniform_lower;
      have h_contradiction : ∀ n, 2 ≤ n → s_n p₂ n > s_n p₁ n + C * (p₂ - p₁) := by
        intros n hn
        have h_dipvsdiq_step : s_n p₂ n > s_n p₁ n + C_prod n * (p₂ - p₁) := by
          apply_rules [ dipvsdiq ];
          intros k hk₁ hk₂;
          by_cases hk : k = 2;
          · unfold s_n; norm_num [ hk, v_one ] ;
          · exact s_n_le_s p₂ ( by linarith ) ( by linarith ) ( k - 1 ) ( Nat.le_sub_one_of_lt ( lt_of_le_of_ne hk₁ ( Ne.symm hk ) ) ) |> le_trans <| by linarith;
        exact lt_of_le_of_lt ( by nlinarith [ hC n hn ] ) h_dipvsdiq_step;
      have h_contradiction : ∀ n, 2 ≤ n → s_n p₁ n < -C * (p₂ - p₁) := by
        intros n hn
        have h_s_n_p2 : s_n p₂ n ≤ 0 := by
          exact hs₂ ▸ s_n_le_s p₂ ( by linarith ) ( by linarith ) n hn;
        linarith [ h_contradiction n hn ];
      have h_contradiction : Filter.Tendsto (fun n => s_n p₁ (n + 2)) Filter.atTop (nhds (s p₁)) := by
        apply tendsto_s_n;
        · linarith;
        · linarith;
      exact absurd ( le_of_tendsto_of_tendsto' h_contradiction tendsto_const_nhds fun n => le_of_lt ( by solve_by_elim [ Nat.le_add_left ] ) ) ( by nlinarith )

theorem prop2 :
    ∃ p₀ : ℝ, 1/2 < p₀ ∧ p₀ < (Real.sqrt 5 - 1) / 2 ∧ s p₀ = 0 ∧
    (∀ p, 1/2 ≤ p → p < p₀ → s p < 0) ∧
    (∀ p, p₀ < p → p < 1 → 0 < s p) := by
      obtain ⟨ p₀, hp₀₁, hp₀₂, hp₀₃ ⟩ := prop2_existence;
      refine' ⟨ p₀, hp₀₁, hp₀₂, hp₀₃, _, _ ⟩;
      · intro p hp₁ hp₂; contrapose! hp₂;
        by_cases hp₃ : p < 1;
        · contrapose! hp₂;
          apply lt_of_not_ge; intro h_nonneg;
          have h_ivt : ∃ c ∈ Set.Icc (1 / 2) p, s c = 0 := by
            apply_rules [ intermediate_value_Icc ];
            · exact s_continuousOn_Ico.mono ( Set.Icc_subset_Ico_right hp₃ );
            · exact ⟨ by linarith [ s_neg_at_half ], h_nonneg ⟩;
          grind +suggestions;
        · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      · intro p hp₁ hp₂;
        -- By contradiction, assume $s(p) \leq 0$.
        by_contra h_neg;
        -- Since $s$ is continuous on $[p, \phi]$ and $s(p) \leq 0$ while $s(\phi) > 0$, by the Intermediate Value Theorem, there exists some $c \in [p, \phi]$ such that $s(c) = 0$.
        obtain ⟨c, hc⟩ : ∃ c ∈ Set.Icc p ((Real.sqrt 5 - 1) / 2), s c = 0 := by
          apply_rules [ intermediate_value_Icc ] <;> norm_num;
          · exact le_of_not_gt fun h => h_neg <| s_pos_of_phi_lt p h hp₂;
          · exact s_continuousOn.mono ( Set.Icc_subset_Ioo ( by linarith ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) );
          · exact ⟨ le_of_not_gt h_neg, le_of_lt ( s_pos_at_phi ) ⟩;
        apply s_zero_unique p₀ c (by linarith) (by
        nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), hc.1.2 ]) (by
        linarith) (by
        cases lt_or_eq_of_le hc.1.2 <;> simp_all +decide;
        exact absurd hc.2 ( ne_of_gt ( s_pos_at_phi ) )) hp₀₃ hc.right (by
        linarith [ hc.1.1 ])

/-
Monotonicity of v in p: higher coin-flip probability gives higher expected heads.
-/
lemma v_mono_p (q p : ℝ) (n : ℕ) (hq₀ : 0 ≤ q) (hqp : q ≤ p) (hp₁ : p ≤ 1) :
    v q n ≤ v p n := by
      -- By the stochastic dominance of binomials for nondecreasing functions, we have:
      have h_stochastic : ∀ (n : ℕ) (f : ℕ → ℝ), (∀ h k, h ≤ k → f h ≤ f k) → (∑ h ∈ Finset.range (n + 1), binomProb n q h * f h) ≤ (∑ h ∈ Finset.range (n + 1), binomProb n p h * f h) := by
        intros n f hf_mono
        have h_convolution : ∀ (n : ℕ) (f : ℕ → ℝ), (∀ h k, h ≤ k → f h ≤ f k) → (∑ h ∈ Finset.range (n + 1), binomProb n q h * f h) ≤ (∑ h ∈ Finset.range (n + 1), binomProb n p h * f h) := by
          intros n f hf_mono
          have h_induction_step : ∀ (n : ℕ) (f : ℕ → ℝ), (∀ h k, h ≤ k → f h ≤ f k) → (∑ h ∈ Finset.range (n + 1), binomProb n q h * f h) ≤ (∑ h ∈ Finset.range (n + 1), binomProb n p h * f h) := by
            intros n f hf_mono
            induction' n with n ih generalizing f
            ·
              unfold binomProb; norm_num;
            ·
              -- By the convolution identity for binomials, we have:
              have h_convolution : ∀ (n : ℕ) (f : ℕ → ℝ), (∑ h ∈ Finset.range (n + 2), binomProb (n + 1) q h * f h) = q * (∑ h ∈ Finset.range (n + 1), binomProb n q h * f (h + 1)) + (1 - q) * (∑ h ∈ Finset.range (n + 1), binomProb n q h * f h) := by
                intros n f
                have h_convolution : ∀ (h : ℕ), h ≤ n + 1 → binomProb (n + 1) q h = q * binomProb n q (h - 1) * (if h > 0 then 1 else 0) + (1 - q) * binomProb n q h * (if h ≤ n then 1 else 0) := by
                  intro h hh; rcases h with ( _ | h ) <;> simp +decide [ *, binomProb ] ; ring;
                  split_ifs <;> simp_all +decide [ Nat.choose_succ_succ, pow_succ', mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
                  · rw [ show n - h = n - ( 1 + h ) + 1 by omega ] ; ring;
                  · exact Or.inl <| Or.inl <| Nat.choose_eq_zero_of_lt <| by linarith;
                rw [ Finset.sum_congr rfl fun x hx => by rw [ h_convolution x ( Finset.mem_range_succ_iff.mp hx ) ] ] ; simp +decide [Finset.sum_add_distrib, add_mul, Finset.mul_sum _ _ _] ; ring_nf;
                rw [ show 2 + n = 1 + n + 1 by ring, Finset.sum_range_succ' ] ; norm_num [ add_comm, add_left_comm, Finset.sum_range_succ ] ; ring_nf;
                exact congrArg₂ _ ( congrArg₂ _ ( congrArg₂ _ rfl rfl ) rfl ) ( Finset.sum_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_range_le hx ) ] );
              have h_convolution_p : ∀ (n : ℕ) (f : ℕ → ℝ), (∑ h ∈ Finset.range (n + 2), binomProb (n + 1) p h * f h) = p * (∑ h ∈ Finset.range (n + 1), binomProb n p h * f (h + 1)) + (1 - p) * (∑ h ∈ Finset.range (n + 1), binomProb n p h * f h) := by
                intros n f
                simp [binomProb];
                rw [ Finset.sum_range_succ', Finset.sum_range_succ ] ; norm_num [ Nat.choose_succ_succ, pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring_nf;
                rw [ add_comm 1 n, Finset.sum_range_succ, Finset.sum_range_succ' ] ; norm_num [ Nat.choose_succ_succ, pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring_nf;
                norm_num [ add_tsub_add_eq_tsub_left, Finset.sum_add_distrib, Finset.sum_sub_distrib ] ; ring_nf;
                norm_num [ add_comm 1, Finset.sum_add_distrib, mul_assoc, mul_left_comm, pow_succ' ] ; ring_nf;
                rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ show n - x = n - ( 1 + x ) + 1 by rw [ tsub_add_eq_add_tsub ( by linarith [ Finset.mem_range.mp hx ] ) ] ; simp +decide [ add_comm ] ] ; ring;
              rw [ h_convolution, h_convolution_p ];
              have := ih ( fun h => f ( h + 1 ) ) ( fun h k hk => hf_mono _ _ ( by linarith ) );
              have := ih f hf_mono;
              nlinarith [ show ∑ h ∈ Finset.range ( n + 1 ), binomProb n q h * f ( h + 1 ) ≥ ∑ h ∈ Finset.range ( n + 1 ), binomProb n q h * f h from Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left ( hf_mono _ _ ( Nat.le_succ _ ) ) ( binomProb_nonneg _ _ _ hq₀ ( by linarith ) ) ]
          exact h_induction_step n f hf_mono;
        exact h_convolution n f hf_mono;
      induction' n using Nat.strong_induction_on with n ih;
      rcases n with ( _ | n ) <;> simp_all +decide [ v ];
      refine' le_trans _ ( h_stochastic _ _ _ );
      · gcongr;
        · exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hq₀ _ ) ) ( pow_nonneg ( sub_nonneg.mpr ( by linarith ) ) _ );
        · exact ih _ ( Nat.le_of_lt_succ ( Fin.is_lt _ ) );
      · intro h k hk;
        simp +decide [ Finset.sup'_le_iff, bestHeadsAside ];
        -- Let's choose any $b$ such that $b = \arg\max_{r \in \{0, 1, \ldots, n\}} (min(k, n+1-r) + v(p, r))$.
        obtain ⟨b, hb⟩ : ∃ b : Fin (n + 1), ∀ r : Fin (n + 1), min (k : ℝ) (n + 1 - r) + v p r ≤ min (k : ℝ) (n + 1 - b) + v p b := by
          simpa using Finset.exists_max_image Finset.univ ( fun r : Fin ( n + 1 ) => min ( k : ℝ ) ( n + 1 - r ) + v p r ) ⟨ 0, Finset.mem_univ 0 ⟩;
        exact ⟨ b, fun r => le_trans ( add_le_add ( min_le_min ( Nat.cast_le.mpr hk ) le_rfl ) le_rfl ) ( hb r ) ⟩

/-
D(p,k) ≤ 1 for p ≥ 1/2 and k ≥ 1. Equivalently, v(p,k-1) ≥ k-2.
-/
lemma D_le_one (p : ℝ) (k : ℕ) (hp : 1/2 ≤ p) (hp₁ : p < 1) (hk : 1 ≤ k) :
    D p k ≤ 1 := by
      rcases k with ( _ | _ | _ | k ) <;> norm_num at *;
      · unfold D; norm_num;
      · unfold D; norm_num [ v_one ] ; linarith;
      · -- By induction on $k$, we can show that $v p (k + 2) \geq k + 1$.
        have h_ind : ∀ k : ℕ, v p (k + 2) ≥ k + 1 := by
          intro k; exact (by
          induction' k with k ih;
          · exact le_trans ( by norm_num ) ( v_two_ge_one p hp hp₁.le );
          · have := v_sub_v_sub_one_ge_one_of_half_le p ( k + 3 ) ( by linarith ) hp hp₁; norm_num at * ; linarith;);
        generalize_proofs at *; simp_all +decide [ D ] ;
        linarith [ h_ind k ]

/-
s_n(p, n) ≥ -1 for p ≥ 1/2 and n ≥ 2.
-/
lemma s_n_ge_neg_one (p : ℝ) (n : ℕ) (hp : 1/2 ≤ p) (hp₁ : p < 1) (hn : 2 ≤ n) :
    s_n p n ≥ -1 := by
      induction hn <;> norm_num [ Finset.sum_range_succ ] at *;
      · unfold s_n;
        rw [ v_two ] <;> norm_num <;> nlinarith [ sq_nonneg ( p - 1 / 2 ) ];
      · exact le_trans ‹_› ( s_n_mono p hp hp₁ _ ( by linarith ) )

/-
Numerical bound: -1 + 2/((1-p)(1-q)) + 1/(pq) < 17 for 1/2 ≤ q < p < φ.
-/
lemma dipvsdiq_upper_numerical (q p : ℝ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hp : p < (Real.sqrt 5 - 1) / 2) :
    -1 + 2 / ((1 - p) * (1 - q)) + 1 / (p * q) < 17 := by
      rw [ add_div', add_div', div_lt_iff₀ ] <;> try nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      rw [ div_mul_eq_mul_div, div_add_one, div_lt_iff₀ ] <;> try nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      nlinarith [ mul_le_mul_of_nonneg_left hq ( sub_nonneg.mpr hqp.le ), mul_le_mul_of_nonneg_left hqp.le ( sub_nonneg.mpr hp.le ), Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), pow_two_nonneg ( p - 1 / 2 ), pow_two_nonneg ( q - 1 / 2 ), pow_two_nonneg ( p - q ), pow_two_nonneg ( p - ( Real.sqrt 5 - 1 ) / 2 ), pow_two_nonneg ( q - ( Real.sqrt 5 - 1 ) / 2 ) ]

/-
For k ≥ 3 and 0 < q < p < (k-1)/k, we have kp^{k-1}(1-p) ≥ kq^{k-1}(1-q).
-/
lemma alpha_coeff_mono {q p : ℝ} {k : ℕ} (hq₀ : 0 < q) (hqp : q ≤ p)
    (hp₁ : p < 1) (hk : 3 ≤ k)
    (hpk : p < (↑k - 1) / ↑k) :
    k * q ^ (k - 1) * (1 - q) ≤ k * p ^ (k - 1) * (1 - p) := by
      -- Consider the function \( f(x) = x^{k-1}(1-x) \).
      set f : ℝ → ℝ := fun x => x ^ (k - 1) * (1 - x);
      -- We need to show that the derivative of $f$ is non-negative on $[0, \frac{k-1}{k}]$.
      have h_deriv_nonneg : ∀ x ∈ Set.Ioo 0 ((k - 1 : ℝ) / k), 0 ≤ deriv f x := by
        rcases k with ( _ | _ | k ) <;> norm_num at *;
        intro x hx₁ hx₂; norm_num [ f, mul_sub ] ; ring_nf;
        rw [ lt_div_iff₀ ] at hx₂ <;> nlinarith [ pow_pos hx₁ k, mul_le_mul_of_nonneg_right hx₂.le ( pow_nonneg hx₁.le k ) ];
      -- Since $f$ is differentiable and its derivative is non-negative on $[q, p]$, we can apply the Mean Value Theorem to $f$ on this interval.
      by_cases h_eq : q = p;
      · rw [ h_eq ];
      · have := exists_deriv_eq_slope f ( lt_of_le_of_ne hqp h_eq );
        simp +zetaDelta at *;
        exact this ( Continuous.continuousOn <| by continuity ) ( Differentiable.differentiableOn <| by ring_nf; norm_num ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by have := h_deriv_nonneg c ( by linarith ) ( by linarith ) ; rw [ hc₂, le_div_iff₀ ] at this <;> nlinarith;

/-
For k ≥ 3, 1/2 ≤ q < p < φ: kp^{k-1}(1-p) ≥ kq^{k-1}(1-q).
-/
lemma alpha_coeff_mono_phi {q p : ℝ} {k : ℕ} (hq : 1/2 ≤ q) (hqp : q ≤ p)
    (hp : p < (Real.sqrt 5 - 1) / 2) (hk : 3 ≤ k) :
    k * q ^ (k - 1) * (1 - q) ≤ k * p ^ (k - 1) * (1 - p) := by
      convert alpha_coeff_mono ?_ ?_ ?_ ?_ ?_ using 1;
      · linarith;
      · linarith;
      · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      · linarith;
      · exact hp.trans_le ( by rw [ le_div_iff₀ ] <;> nlinarith only [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), show ( k : ℝ ) ≥ 3 by norm_cast ] )

/-
For 1/2 ≤ q < p < φ and k ≥ 2 with s_k(p) ≤ 0:
all s_j(p) are ≤ 0 for j ≤ k (by s_n_mono), and dipvsdiq gives s_k(p) > s_k(q).
-/
lemma s_mono_p_neg (q p : ℝ) (k : ℕ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hp : p < (Real.sqrt 5 - 1) / 2) (hk : 2 ≤ k) (hs : s_n p k ≤ 0) :
    s_n q k < s_n p k := by
      -- By induction on $j$, we show that for all $j$ with $1 \le j \le k$, $s_n(p, j) \le 0$.
      have h_ind : ∀ j, 1 ≤ j → j ≤ k → s_n p j ≤ 0 := by
        intro j hj₁ hj₂;
        -- Since $s_n$ is increasing in $n$, we have $s_n p j \le s_n p k$ for $j \le k$.
        have h_mono : ∀ j k, 2 ≤ j → j ≤ k → s_n p j ≤ s_n p k := by
          intros j k hj₁ hj₂;
          induction hj₂ <;> norm_num at *;
          exact le_trans ‹_› ( s_n_mono p ( by linarith ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) _ ( by linarith ) );
        by_cases hj : 2 ≤ j;
        · exact le_trans ( h_mono j k hj hj₂ ) hs;
        · interval_cases j ; norm_num [ s_n ];
          rw [ v_one ];
      contrapose! hs;
      -- Apply dipvsdiq to get s_k(p) > s_k(q).
      have h_dipvsdiq : s_n p k > s_n q k + C_prod k * (p - q) := by
        grind +suggestions;
      nlinarith [ show 0 < C_prod k from C_prod_pos k hk ]

/-
max(0, -s_k(p)) ≤ max(0, -s_k(q)) for 1/2 ≤ q < p < φ and k ≥ 2.
When s_k(p) < 0, dipvsdiq gives s_k(p) > s_k(q), so -s_k(p) < -s_k(q).
When s_k(p) ≥ 0, max(0,-s_k(p)) = 0 ≤ max(0,-s_k(q)).
-/
lemma max_neg_s_antitone (q p : ℝ) (k : ℕ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hp : p < (Real.sqrt 5 - 1) / 2) (hk : 2 ≤ k) :
    max 0 (-s_n p k) ≤ max 0 (-s_n q k) := by
      by_cases hs : s_n p k ≤ 0 <;> simp_all +decide;
      · exact Or.inr ( le_of_lt ( s_mono_p_neg q p k ( by norm_num at *; linarith ) hqp hp hk hs ) );
      · exact Or.inl hs.le

/-
The combined three-series term is nonneg: for 0 < q < p < 1 and k ≥ 1,
  (p^k - q^k) + k(p^{k-1}(1-p) - q^{k-1}(1-q)) + ((1-q)^k - (1-p)^k) ≥ 0.
This equals [α(p,k) - (1-p)^k] - [α(q,k) - (1-q)^k], and g(x) = α(x,k) - (1-x)^k is increasing.
-/
lemma three_series_term_nonneg {q p : ℝ} {k : ℕ} (hq₀ : 0 < q) (hqp : q < p) (hp₁ : p < 1)
    (hk : 1 ≤ k) :
    0 ≤ (p ^ k - q ^ k) + (↑k * (p ^ (k-1) * (1-p) - q ^ (k-1) * (1-q))) +
    ((1-q) ^ k - (1-p) ^ k) := by
      -- The function $g(x) = \alpha(x,k) - (1-x)^k$ is increasing for $0 < x < 1$.
      have h_g_inc : StrictMonoOn (fun x : ℝ => x^k + k * x^(k-1) * (1 - x) - (1 - x)^k) (Set.Ioo 0 1) := by
        -- The derivative of $g(x)$ is $g'(x) = kx^{k-1} + k(k-1)x^{k-2}(1-x) - kx^{k-1} + k(1-x)^{k-1} = k(k-1)x^{k-2}(1-x) + k(1-x)^{k-1}$.
        have h_deriv : ∀ x ∈ Set.Ioo 0 1, deriv (fun x : ℝ => x^k + k * x^(k-1) * (1 - x) - (1 - x)^k) x = k * (k - 1) * x^(k - 2) * (1 - x) + k * (1 - x)^(k - 1) := by
          intro x hx; rcases k with ( _ | _ | k ) <;> norm_num [ Nat.succ_eq_add_one, mul_assoc, mul_comm, mul_left_comm, sub_mul ] at *;
          apply_rules [ HasDerivAt.deriv ];
          convert HasDerivAt.sub ( HasDerivAt.add ( hasDerivAt_pow ( k + 1 + 1 ) x ) ( HasDerivAt.mul ( hasDerivAt_pow ( k + 1 ) x ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id' x |> HasDerivAt.const_sub _ ) ) ) ) ( HasDerivAt.comp x ( hasDerivAt_pow ( k + 1 + 1 ) _ ) ( hasDerivAt_id' x |> HasDerivAt.const_sub _ ) ) using 1 ; norm_num ; ring!;
        apply_rules [ strictMonoOn_of_deriv_pos ];
        · exact convex_Ioo _ _;
        · fun_prop;
        · rcases k with ( _ | _ | k ) <;> norm_num at *;
          exact fun x hx₁ hx₂ => h_deriv x hx₁ hx₂ ▸ by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( pow_nonneg hx₁.le _ ) ) ( by linarith ) ) ( mul_pos ( by positivity ) ( pow_pos ( by linarith ) _ ) ) ;
      have := h_g_inc ⟨ hq₀, by linarith ⟩ ⟨ by linarith, hp₁ ⟩ hqp; norm_num at this; linarith;

/-
Partial sum bound: Σ_{k=1}^n [three series terms] ≤ 2(p-q)/((1-p)(1-q)) + (p-q)/(pq).
-/
lemma partial_sum_le_series (q p : ℝ) (n : ℕ) (hq₀ : 0 < q) (hqp : q < p) (hp₁ : p < 1) :
    ∑ k ∈ Finset.Icc 1 n,
      ((p ^ k - q ^ k) + (↑k * (p ^ (k-1) * (1-p) - q ^ (k-1) * (1-q))) +
      ((1-q) ^ k - (1-p) ^ k))
    ≤ 2 * (p - q) / ((1-p) * (1-q)) + (p - q) / (p * q) := by
      convert le_of_tendsto_of_tendsto tendsto_const_nhds ( show Filter.Tendsto ( fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ( p ^ k - q ^ k + k * ( p ^ ( k - 1 ) * ( 1 - p ) - q ^ ( k - 1 ) * ( 1 - q ) ) + ( ( 1 - q ) ^ k - ( 1 - p ) ^ k ) ) ) Filter.atTop ( nhds ( 2 * ( p - q ) / ( ( 1 - p ) * ( 1 - q ) ) + ( p - q ) / ( p * q ) ) ) from ?_ ) ( Filter.eventually_atTop.mpr ⟨ n, fun m hm => ?_ ⟩ ) using 1;
      · have h_partial_sum_split : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (p ^ (k + 1) - q ^ (k + 1) + (k + 1) * (p ^ k * (1 - p) - q ^ k * (1 - q)) + ((1 - q) ^ (k + 1) - (1 - p) ^ (k + 1)))) Filter.atTop (nhds (2 * (p - q) / ((1 - p) * (1 - q)) + (p - q) / (p * q))) := by
          have h_partial_sum_split : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (p ^ (k + 1) - q ^ (k + 1))) Filter.atTop (nhds ((p / (1 - p)) - (q / (1 - q)))) ∧ Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, ((k + 1) * (p ^ k * (1 - p) - q ^ k * (1 - q)))) Filter.atTop (nhds ((1 / (1 - p)) - (1 / (1 - q)))) ∧ Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, ((1 - q) ^ (k + 1) - (1 - p) ^ (k + 1))) Filter.atTop (nhds (((1 - q) / q) - ((1 - p) / p))) := by
            refine' ⟨ _, _, _ ⟩;
            · convert Filter.Tendsto.sub ( HasSum.tendsto_sum_nat <| HasSum.mul_left p <| hasSum_geometric_of_lt_one ( by linarith ) hp₁ ) ( HasSum.tendsto_sum_nat <| HasSum.mul_left q <| hasSum_geometric_of_lt_one ( by linarith ) <| show q < 1 by linarith ) using 2 ; norm_num [ pow_succ', div_eq_mul_inv ];
            · have h_partial_sum_split : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (k + 1) * p ^ k * (1 - p)) Filter.atTop (nhds (1 / (1 - p))) ∧ Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (k + 1) * q ^ k * (1 - q)) Filter.atTop (nhds (1 / (1 - q))) := by
                have h_partial_sum_split : ∀ x : ℝ, 0 < x ∧ x < 1 → Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (k + 1) * x ^ k) Filter.atTop (nhds (1 / (1 - x) ^ 2)) := by
                  intros x hx
                  have h_partial_sum_split : ∀ n : ℕ, ∑ k ∈ Finset.range n, (k + 1) * x ^ k = (1 - (n + 1) * x ^ n + n * x ^ (n + 1)) / (1 - x) ^ 2 := by
                    intro n; rw [ eq_div_iff ( pow_ne_zero 2 <| by linarith ) ] ; induction n <;> norm_num [ pow_succ, Finset.sum_range_succ ] at * ; nlinarith;
                  -- We'll use the fact that $(n + 1) * x^n$ and $n * x^{n + 1}$ tend to $0$ as $n$ tends to infinity.
                  have h_tendsto_zero : Filter.Tendsto (fun n : ℕ => (n + 1) * x ^ n) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun n : ℕ => n * x ^ (n + 1)) Filter.atTop (nhds 0) := by
                    have h_tendsto_zero : Filter.Tendsto (fun n : ℕ => (n : ℝ) * x ^ n) Filter.atTop (nhds 0) := by
                      have h_lim : Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-n * Real.log (1 / x))) Filter.atTop (nhds 0) := by
                        -- Let $y = n \log(1/x)$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{y}{e^y}$.
                        suffices h_log : Filter.Tendsto (fun y : ℝ => y * Real.exp (-y)) Filter.atTop (nhds 0) by
                          have h_subst : Filter.Tendsto (fun n : ℕ => (n * Real.log (1 / x)) * Real.exp (-(n * Real.log (1 / x)))) Filter.atTop (nhds 0) := by
                            exact h_log.comp <| tendsto_natCast_atTop_atTop.atTop_mul_const <| Real.log_pos <| one_lt_one_div hx.1 hx.2;
                          convert h_subst.div_const ( Real.log ( 1 / x ) ) using 2 <;> ring_nf;
                          exact eq_div_of_mul_eq ( ne_of_gt <| Real.log_pos <| by rw [ inv_eq_one_div, lt_div_iff₀ ] <;> linarith ) <| by ring;
                        convert ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 ) using 2 ; norm_num;
                      convert h_lim using 2 ; norm_num [ Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx.1 ];
                    exact ⟨ by simpa [ add_mul ] using h_tendsto_zero.add ( tendsto_pow_atTop_nhds_zero_of_lt_one hx.1.le hx.2 ), by simpa [ pow_succ, mul_assoc, mul_comm, mul_left_comm ] using h_tendsto_zero.mul_const x ⟩;
                  simpa only [ h_partial_sum_split ] using Filter.Tendsto.div_const ( by simpa using Filter.Tendsto.add ( tendsto_const_nhds.sub h_tendsto_zero.1 ) h_tendsto_zero.2 ) _;
                simp_all +decide [ ← Finset.sum_mul _ _ _ ];
                exact ⟨ by convert Filter.Tendsto.mul ( h_partial_sum_split p ( by linarith ) ( by linarith ) ) tendsto_const_nhds using 2 ; simp +decide [ sq, ne_of_gt ( by linarith : 0 < 1 - p ) ], by convert Filter.Tendsto.mul ( h_partial_sum_split q ( by linarith ) ( by linarith ) ) tendsto_const_nhds using 2 ; simp +decide [ sq, ne_of_gt ( by linarith : 0 < 1 - q ) ] ⟩;
              convert h_partial_sum_split.1.sub h_partial_sum_split.2 using 2 ; norm_num [ mul_sub, ← mul_assoc, Finset.sum_sub_distrib ];
            · have h_partial_sum_split : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (1 - q) ^ (k + 1)) Filter.atTop (nhds ((1 - q) / q)) ∧ Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (1 - p) ^ (k + 1)) Filter.atTop (nhds ((1 - p) / p)) := by
                have h_partial_sum_split : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (1 - q) ^ k) Filter.atTop (nhds (1 / q)) ∧ Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (1 - p) ^ k) Filter.atTop (nhds (1 / p)) := by
                  exact ⟨ by simpa using hasSum_geometric_of_lt_one ( by linarith ) ( by linarith : 1 - q < 1 ) |> HasSum.tendsto_sum_nat |> fun h => h.trans ( by norm_num [ show q ≠ 0 by linarith ] ), by simpa using hasSum_geometric_of_lt_one ( by linarith ) ( by linarith : 1 - p < 1 ) |> HasSum.tendsto_sum_nat |> fun h => h.trans ( by norm_num [ show p ≠ 0 by linarith ] ) ⟩;
                simp_all +decide [pow_succ', ← Finset.mul_sum _ _ _];
                exact ⟨ by simpa only [ div_eq_mul_inv ] using h_partial_sum_split.1.const_mul _, by simpa only [ div_eq_mul_inv ] using h_partial_sum_split.2.const_mul _ ⟩;
              simpa only [ Finset.sum_sub_distrib ] using h_partial_sum_split.1.sub h_partial_sum_split.2;
          convert Filter.Tendsto.add ( Filter.Tendsto.add h_partial_sum_split.1 h_partial_sum_split.2.1 ) h_partial_sum_split.2.2 using 2 ; norm_num [ Finset.sum_add_distrib ] ; ring_nf;
          grind;
        exact h_partial_sum_split.congr fun n => by erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ] ;
      · exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc_right hm ) fun _ _ _ => three_series_term_nonneg hq₀ hqp hp₁ ( by linarith [ Finset.mem_Icc.mp ‹_› ] )

/-
The step formula: v(p,k) - v(p,k-1) - 1 in terms of D and max(0,-s_{k-1}).
-/
lemma step_formula (p : ℝ) (k : ℕ) (hp : 1/2 ≤ p) (hp₁ : p < 1) (hk : 3 ≤ k) :
    v p k - v p (k-1) - 1 = p^k * D p k + ↑k * p^(k-1) * (1-p) * max 0 (-s_n p (k-1)) - (1-p)^k := by
      rw [ ← eta_neg_s_n p k ( by linarith ) ];
      nontriviality;
      have := reduced_recurrence p k hk hp ( by linarith );
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ delta ];
      linarith [ this fun n hn₁ hn₂ => by linarith [ v_sub_v_sub_one_ge_one_of_half_le p n ( by linarith ) ( by linarith ) ( by linarith ) ] ]

/-
Per-term bound for the telescoping sum: for k ≥ 3, the k-th step difference is bounded.
-/
lemma step_diff_bound_k3 (q p : ℝ) (k : ℕ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hp : p < (Real.sqrt 5 - 1) / 2) (hk : 3 ≤ k) :
    (v p k - v p (k-1)) - (v q k - v q (k-1)) ≤
    (p^k - q^k) + ↑k * (p^(k-1) * (1-p) - q^(k-1) * (1-q)) + ((1-q)^k - (1-p)^k) := by
      have h_step_formula_p : v p k - v p (k - 1) - 1 = p^k * D p k + k * p^(k-1) * (1-p) * max 0 (-s_n p (k-1)) - (1-p)^k := by
        convert step_formula p k ( by linarith ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) hk using 1
      have h_step_formula_q : v q k - v q (k - 1) - 1 = q^k * D q k + k * q^(k-1) * (1-q) * max 0 (-s_n q (k-1)) - (1-q)^k := by
        apply step_formula q k hq (by
        nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]) hk;
      -- For the D terms: D(q,k) ≥ D(p,k) since v(q,k-1) ≤ v(p,k-1) by v_mono_p. And D(p,k) ≤ 1 by D_le_one, D(p,k) ≥ 0 since v p (k-1) ≤ k-1 by v_le_n. So p^k D(p,k) - q^k D(q,k) ≤ (p^k-q^k) D(p,k) ≤ p^k-q^k.
      have hD_bound : p^k * D p k - q^k * D q k ≤ p^k - q^k := by
        have hD_bound : D p k ≤ 1 ∧ D q k ≥ D p k := by
          apply And.intro;
          · apply D_le_one; linarith; linarith [ show p < 1 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ] ; linarith;
          · exact sub_le_sub_left ( v_mono_p q p ( k - 1 ) ( by linarith ) ( by linarith ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ) _;
        nlinarith [ pow_pos ( by linarith : 0 < p ) k, pow_le_pow_left₀ ( by linarith ) hqp.le k, show 0 ≤ q ^ k by positivity, show 0 ≤ p ^ k by exact pow_nonneg ( by linarith ) _ ];
      -- For the alpha terms: let M_p = max(0,-s_{k-1}(p)), M_q = max(0,-s_{k-1}(q)).
      set Mp := max 0 (-s_n p (k-1))
      set Mq := max 0 (-s_n q (k-1));
      -- By definition of $Mp$ and $Mq$, we know that $Mp \leq 1$ and $Mp \leq Mq$.
      have hMp_le_one : Mp ≤ 1 := by
        have hMp_le_one : s_n p (k - 1) ≥ -1 := by
          apply s_n_ge_neg_one p (k - 1) (by linarith) (by
          nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]) (by
          exact Nat.le_sub_one_of_lt hk);
        exact max_le ( by norm_num ) ( by linarith )
      have hMp_le_Mq : Mp ≤ Mq := by
        apply max_neg_s_antitone q p (k - 1) hq hqp hp (by omega);
      -- By definition of $Mp$ and $Mq$, we know that $k * p^(k-1) * (1-p) ≥ k * q^(k-1) * (1-q)$.
      have h_alpha_coeff_mono : k * p^(k-1) * (1-p) ≥ k * q^(k-1) * (1-q) := by
        apply_rules [ alpha_coeff_mono_phi ];
        linarith;
      nlinarith [ show ( k : ℝ ) * q ^ ( k - 1 ) * ( 1 - q ) ≥ 0 by exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by linarith ) _ ) ) ( by linarith [ show p < 1 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ] ) ]

/-
Upper bound on s_n differences (Lemma 15 in the paper): s_n(p) < s_n(q) + 17(p-q).
-/
lemma dipvsdiq_upper (q p : ℝ) (n : ℕ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hp : p < (Real.sqrt 5 - 1) / 2) (hn : 2 ≤ n) :
    s_n p n < s_n q n + 17 * (p - q) := by
      -- We'll use the fact that $s_n p n - s_n q n = (q - p) + \sum_{k=1}^n (\Delta_k(p) - \Delta_k(q))$ where $\Delta_k(x) = v x k - v x (k-1)$.
      have h_telescope : s_n p n - s_n q n = (q - p) + ∑ k ∈ Finset.Icc 1 n, (v p k - v p (k - 1)) - ∑ k ∈ Finset.Icc 1 n, (v q k - v q (k - 1)) := by
        unfold s_n; induction hn <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at * ; linarith;
        linarith;
      -- For k ≥ 3, use step_diff_bound_k3.
      have h_step_diff_bound_k3 : ∀ k ∈ Finset.Icc 3 n, (v p k - v p (k - 1)) - (v q k - v q (k - 1)) ≤ (p^k - q^k) + k * (p^(k-1) * (1-p) - q^(k-1) * (1-q)) + ((1-q)^k - (1-p)^k) := by
        exact fun k hk => step_diff_bound_k3 q p k hq hqp hp ( Finset.mem_Icc.mp hk |>.1 );
      -- For k=2, compute Δ_2 directly.
      have h_step_diff_bound_k2 : (v p 2 - v p 1) - (v q 2 - v q 1) ≤ (p^2 - q^2) + 2 * (p * (1 - p) - q * (1 - q)) + ((1 - q)^2 - (1 - p)^2) := by
        rw [ v_two, v_two, v_one, v_one ] <;> try nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
        nlinarith [ sq_nonneg ( p - q ), mul_le_mul_of_nonneg_left hqp.le ( sub_nonneg.mpr hq ) ];
      -- Combine the bounds for k=1, k=2, and k ≥ 3.
      have h_combined_bound : ∑ k ∈ Finset.Icc 1 n, (v p k - v p (k - 1)) - ∑ k ∈ Finset.Icc 1 n, (v q k - v q (k - 1)) ≤ ∑ k ∈ Finset.Icc 1 n, ((p^k - q^k) + k * (p^(k-1) * (1-p) - q^(k-1) * (1-q)) + ((1-q)^k - (1-p)^k)) := by
        have h_combined_bound : ∀ k ∈ Finset.Icc 1 n, (v p k - v p (k - 1)) - (v q k - v q (k - 1)) ≤ (p^k - q^k) + k * (p^(k-1) * (1-p) - q^(k-1) * (1-q)) + ((1-q)^k - (1-p)^k) := by
          intro k hk; rcases k with ( _ | _ | _ | k ) <;> simp_all +decide ;
          · rw [ v_one, v_one ] ; linarith;
          · exact_mod_cast h_step_diff_bound_k3 _ le_add_self ( by linarith );
        simpa only [ ← Finset.sum_sub_distrib ] using Finset.sum_le_sum h_combined_bound;
      -- Apply the partial_sum_le_series lemma to bound the sum.
      have h_partial_sum_bound : ∑ k ∈ Finset.Icc 1 n, ((p^k - q^k) + k * (p^(k-1) * (1-p) - q^(k-1) * (1-q)) + ((1-q)^k - (1-p)^k)) ≤ 2 * (p - q) / ((1 - p) * (1 - q)) + (p - q) / (p * q) := by
        apply partial_sum_le_series;
        · linarith;
        · linarith;
        · nlinarith only [ hp, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      -- Apply the dipvsdiq_upper_numerical lemma to bound the expression.
      have h_dipvsdiq_upper_numerical : -1 + 2 / ((1 - p) * (1 - q)) + 1 / (p * q) < 17 := by
        apply_rules [ dipvsdiq_upper_numerical ];
      ring_nf at *; nlinarith;

/-
s is Lipschitz from above: s(p) ≤ s(q) + 17*(p-q) for 1/2 ≤ q < p < φ.
-/
lemma s_lipschitz_upper (q p : ℝ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hp : p < (Real.sqrt 5 - 1) / 2) :
    s p ≤ s q + 17 * (p - q) := by
      apply ciSup_le;
      exact fun x => le_of_lt ( by linarith [ dipvsdiq_upper q p ( x + 2 ) hq hqp hp ( by linarith ), s_n_le_s q ( by linarith ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( x + 2 ) ( by linarith ) ] )

/-
s is Lipschitz from below: s(p) ≥ s(q) + C*(p-q) for 1/2 ≤ q < p < φ with s(q) ≤ 0, s(p) ≤ 0.
-/
lemma s_lipschitz_lower (q p : ℝ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hp : p < (Real.sqrt 5 - 1) / 2)
    (_hsq : s q ≤ 0) (hsp : s p ≤ 0) :
    ∃ C > 0, s p ≥ s q + C * (p - q) := by
      -- From Lemma 15, we have $s_n(p) > s_n(q) + C_prod(n)*(p-q)$ for all $n \ge 2$.
      have h_lemma15 : ∀ n ≥ 2, s_n p n > s_n q n + (C_prod n) * (p - q) := by
        intro n hn;
        apply_rules [ dipvsdiq ];
        have h_s_n_le_s : ∀ k, 2 ≤ k → s_n p k ≤ s p := by
          exact fun k hk => s_n_le_s p ( by linarith ) ( by linarith [ show p < 1 from hp.trans_le ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ] ) k hk;
        intros k hk hk_le_n
        by_cases hk_ge_2 : 2 ≤ k - 1;
        · exact le_trans ( h_s_n_le_s _ hk_ge_2 ) hsp;
        · rcases k with ( _ | _ | _ | k ) <;> norm_num at *;
          unfold s_n; norm_num; nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), v_one p ] ;
      obtain ⟨ C, hC₀, hC ⟩ := C_prod_uniform_lower;
      -- Taking the limit as $n \to \infty$, we get $s(p) \ge s(q) + C(p-q)$.
      have h_limit : Filter.Tendsto (fun n => s_n p (n + 2)) Filter.atTop (nhds (s p)) ∧ Filter.Tendsto (fun n => s_n q (n + 2)) Filter.atTop (nhds (s q)) := by
        apply And.intro;
        · apply tendsto_s_n;
          · linarith;
          · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
        · apply tendsto_s_n;
          · exact RCLike.ofReal_le_ofReal.mp hq
          · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      exact ⟨ C, hC₀, le_of_tendsto_of_tendsto' ( h_limit.2.add_const ( C * ( p - q ) ) ) h_limit.1 fun n => by nlinarith [ h_lemma15 ( n + 2 ) ( by linarith ), hC ( n + 2 ) ( by linarith ) ] ⟩

/-
s_n(p₀) < 0 for all n ≥ 2 when s(p₀) = 0 and p₀ < φ.
-/
set_option maxHeartbeats 3200000 in
lemma s_n_strict_neg_at_zero (p₀ : ℝ) (hp₀_s : s p₀ = 0) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2) (n : ℕ) (hn : 2 ≤ n) :
    s_n p₀ n < 0 := by
      -- By contradiction, assume $s_n(p₀, n) \geq 0$ for some $n \geq 2$.
      by_contra h_contra;
      -- Since $s_n(p₀, n) \geq 0$, we have $s_n(p₀, k) \geq 0$ for all $k \geq n$ by monotonicity.
      have h_monotone : ∀ k ≥ n, s_n p₀ k ≥ 0 := by
        intro k hk
        induction' hk with k hk ih;
        · linarith;
        · exact le_trans ih ( s_n_mono p₀ ( by linarith ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) k ( by linarith [ Nat.succ_le_succ hk ] ) );
      -- Since $s_n(p₀, k) \geq 0$ for all $k \geq n$, we have $s_n(p₀, k) = 0$ for all $k \geq n$.
      have h_zero : ∀ k ≥ n, s_n p₀ k = 0 := by
        intros k hk
        have h_le : s_n p₀ k ≤ s p₀ := by
          apply s_n_le_s;
          · linarith;
          · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
          · grind;
        linarith [ h_monotone k hk ];
      -- Since $s_n(p₀, k) = 0$ for all $k \geq n$, we have $p₀^{k+1} = (1-p₀)^k$ for all $k \geq n$.
      have h_eq : ∀ k ≥ n, p₀ ^ (k + 1) = (1 - p₀) ^ k := by
        intros k hk
        have h_step' : s_n p₀ (k + 1) - s_n p₀ k = p₀ ^ (k + 1) * (1 - p₀) - (1 - p₀) ^ (k + 1) := by
          have := @step_formula p₀ ( k + 1 ) ?_ ?_ ?_ <;> norm_num at *;
          · unfold D s_n at * ; norm_num at *;
            grind;
          · linarith;
          · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
          · linarith
        have h0k := h_zero k hk; have h1k := h_zero (k + 1) (by omega)
        have : p₀ ^ (k + 1) * (1 - p₀) = (1 - p₀) ^ (k + 1) := by linarith
        have hq_pos : (0 : ℝ) < 1 - p₀ := by nlinarith [Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
        have hfact : (1 - p₀) ^ (k + 1) = (1 - p₀) ^ k * (1 - p₀) := pow_succ (1 - p₀) k
        rw [hfact] at this
        exact mul_right_cancel₀ hq_pos.ne' this;
      have := h_eq n le_rfl; have := h_eq ( n + 1 ) ( by linarith ) ; simp_all +decide [ pow_succ' ] ;
      cases this <;> norm_num at * ; linarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]

/-
For every N, ∃ δ > 0 s.t. for p ∈ (p₀, p₀+δ), s_k(p) < 0 for all k ∈ [2,N].
-/
lemma crossing_time_large (p₀ : ℝ) (hp₀_s : s p₀ = 0) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2) (N : ℕ) (hN : 2 ≤ N) :
    ∃ δ > 0, ∀ p, p₀ < p → p < p₀ + δ → ∀ k, 2 ≤ k → k ≤ N → s_n p k < 0 := by
      -- By induction on $N$, we can show that for any $N \geq 2$, there exists a $\delta > 0$ such that for all $p \in (p₀, p₀ + \delta)$, $s_k(p) < 0$ for all $k \in [2, N]$.
      induction' N, Nat.succ_le_iff.mpr hN using Nat.le_induction with N ihN N hN ihN generalizing p₀;
      · have := s_n_strict_neg_at_zero p₀ hp₀_s hp₀_half hp₀_phi 2 (by linarith);
        obtain ⟨ δ, hδ_pos, hδ ⟩ := Metric.mem_nhds_iff.mp ( s_n_continuous 2 |> Continuous.continuousAt |> fun h => h.eventually ( gt_mem_nhds this ) );
        exact ⟨ δ, hδ_pos, fun p hp₁ hp₂ k hk₁ hk₂ => by interval_cases k ; exact hδ <| mem_ball_iff_norm.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩ ⟩;
      · obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ > 0, ∀ p, p₀ < p → p < p₀ + δ₁ → s_n p (Nat.succ ‹_›) < 0 := by
          have h_cont : ContinuousAt (fun p => s_n p (Nat.succ ‹_›)) p₀ := by
            exact ContinuousAt.comp ( s_n_continuous _ |> Continuous.continuousAt ) ( continuousAt_id );
          have := Metric.continuousAt_iff.mp h_cont;
          exact Exists.elim ( this ( -s_n p₀ ( Nat.succ _ ) ) ( neg_pos.mpr ( s_n_strict_neg_at_zero p₀ hp₀_s hp₀_half hp₀_phi _ ( Nat.succ_le_succ ( by linarith ) ) ) ) ) fun δ hδ => ⟨ δ, hδ.1, fun p hp₁ hp₂ => by linarith [ abs_lt.mp ( hδ.2 ( show |p - p₀| < δ from abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ) ] ⟩;
        grind

/-
Strategy A increment: when s_{n-1}(p) ≥ 0, the step s_n - s_{n-1} equals p^n * D_n - (1-p)^n.
-/
lemma step_increment_A (p : ℝ) (n : ℕ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hn : 3 ≤ n) (hs : 0 ≤ s_n p (n - 1)) :
    s_n p n - s_n p (n - 1) = p ^ n * D p n - (1 - p) ^ n := by
      rcases n <;> simp_all +decide [pow_succ'];
      rename_i k;
      have := @CoinGame.step_formula p ( k + 1 ) ?_ ?_ ?_ <;> norm_num at *;
      · unfold D s_n at *;
        norm_num [ Nat.succ_eq_add_one, pow_add ] at *;
        rw [ max_eq_left ] at this <;> nlinarith [ pow_pos ( by linarith : 0 < p ) k, pow_pos ( by linarith : 0 < 1 - p ) k ];
      · linarith;
      · linarith;
      · linarith

/-
D(p,n) ≤ 1-p when s_{n-1}(p) ≥ 0.
-/
lemma D_le_one_sub_p_of_nonneg (p : ℝ) (n : ℕ) (hn : 2 ≤ n) (hs : 0 ≤ s_n p (n - 1)) :
    D p n ≤ 1 - p := by
      exact D_eq_one_sub_p_sub_s_n p n hn ▸ sub_le_self _ hs

/-
D(p,n) ≥ (1-p) - s(p) when s_{n-1}(p) ≥ 0 and s_{n-1}(p) ≤ s(p).
-/
lemma D_ge_of_nonneg (p : ℝ) (n : ℕ) (hn : 2 ≤ n) (_hs : 0 ≤ s_n p (n - 1))
    (hs_le : s_n p (n - 1) ≤ s p) :
    D p n ≥ (1 - p) - s p := by
      linarith [ D_eq_one_sub_p_sub_s_n p n hn ]

/-
Finite accumulation: for K ≤ N, s_N(p) ≥ s_K(p) + Σ_{n=K+1}^{N} (p^n*(1-p-s(p)) - (1-p)^n).
-/
lemma finite_sum_lower (p : ℝ) (K N : ℕ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hK : 3 ≤ K) (hKN : K ≤ N) (hsK : 0 ≤ s_n p K) :
    s_n p N ≥ s_n p K +
      ∑ n ∈ Finset.Ico (K + 1) (N + 1), (p ^ n * ((1 - p) - s p) - (1 - p) ^ n) := by
        induction' hKN with N hKN ih;
        · norm_num;
        · -- By the properties of the supremum and the recurrence relation, we have:
          have h_step : s_n p (N + 1) ≥ s_n p N + (p^(N + 1) * (1 - p - s p) - (1 - p)^(N + 1)) := by
            have h_step : s_n p (N + 1) - s_n p N = p^(N + 1) * D p (N + 1) - (1 - p)^(N + 1) := by
              apply step_increment_A p (N + 1) hp hp₁ (by
              linarith [ Nat.succ_le_succ hKN ]) (by
              have h_nonneg : ∀ m, K ≤ m → 0 ≤ s_n p m := by
                intro m hm; induction hm <;> simp_all +decide [ Nat.succ_eq_add_one, s_n ] ;
                have := v_sub_v_sub_one_ge_one_of_half_le p ( ‹_› + 1 ) ( by linarith ) ( by norm_num at *; linarith ) ( by linarith ) ; norm_num at * ; linarith;
              exact h_nonneg _ hKN);
            have h_D_ge : D p (N + 1) ≥ (1 - p) - s p := by
              apply D_ge_of_nonneg;
              · linarith [ Nat.succ_le_succ hKN ];
              · refine' le_trans hsK _;
                have h_monotone : ∀ n ≥ 2, s_n p n ≤ s_n p (n + 1) := by
                  intros n hn
                  apply s_n_mono p hp hp₁ n hn;
                exact Nat.le_induction ( by norm_num ) ( fun n hn ih => by simpa using le_trans ih ( h_monotone n ( by linarith ) ) ) N ( show K ≤ N from hKN );
              · exact s_n_le_s p ( by linarith ) ( by linarith ) N ( by linarith [ Nat.succ_le_succ hKN ] );
            nlinarith [ pow_nonneg ( by linarith : 0 ≤ p ) ( N + 1 ) ];
          rw [ Finset.sum_Ico_succ_top ] <;> linarith! [ Nat.succ_le_succ hKN ]

/-
Each term in the sum is bounded below by p^n * (1-p) * (1-ε) under conditions.
-/
lemma term_lower_bound (p : ℝ) (n K : ℕ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hn : K + 1 ≤ n)
    (hs_small : s p < (1 - p) / 2 * ε)
    (_hε : 0 < ε)
    (h_ratio : ((1 - p) / p) ^ K < (1 - p) / 2 * ε) :
    p ^ n * ((1 - p) - s p) - (1 - p) ^ n > p ^ n * (1 - p) * (1 - ε) := by
      -- Since $n \geq K + 1$, we have $((1 - p) / p) ^ n \leq ((1 - p) / p) ^ K$.
      have h_pow : ((1 - p) / p) ^ n ≤ ((1 - p) / p) ^ K := by
        exact pow_le_pow_of_le_one ( div_nonneg ( by linarith ) ( by linarith ) ) ( div_le_one_of_le₀ ( by linarith ) ( by linarith ) ) ( by linarith );
      rw [ div_pow, div_le_iff₀ ] at h_pow <;> nlinarith [ pow_pos ( by linarith : 0 < p ) n ]

/-
Limit accumulation: s(p) ≥ s_K(p) + (1-ε)·p^{K+1} when tail terms are bounded below.
-/
lemma tail_ge_limit (p : ℝ) (K : ℕ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hK : 3 ≤ K) (hsK : 0 ≤ s_n p K)
    (h_term_ge : ∀ n, K + 1 ≤ n →
      p ^ n * ((1 - p) - s p) - (1 - p) ^ n ≥ p ^ n * (1 - p) * (1 - ε)) :
    s p ≥ s_n p K + (1 - ε) * p ^ (K + 1) := by
      -- From finite_sum_lower, for N ≥ K: s_N ≥ s_K + Σ (p^n((1-p)-s(p)) - (1-p)^n).
      have h_sum_lower (N : ℕ) (hN : K ≤ N) :
          s_n p N ≥ s_n p K + ∑ n ∈ Finset.Ico (K + 1) (N + 1), (p ^ n * ((1 - p) - s p) - (1 - p) ^ n) := by
            exact finite_sum_lower p K N hp hp₁ hK hN hsK;
      -- The geometric sum Σ p^n over Ico(K+1,N+1) can be computed as p^{K+1} * (1-p^{N-K})/(1-p).
      have h_geo_sum (N : ℕ) (hN : K ≤ N) :
          ∑ n ∈ Finset.Ico (K + 1) (N + 1), p ^ n = p ^ (K + 1) * (1 - p ^ (N - K)) / (1 - p) := by
            erw [ geom_sum_Ico ] <;> ring_nf;
            · rw [ show p ^ N = p ^ K * p ^ ( N - K ) by rw [ ← pow_add, Nat.add_sub_of_le hN ] ] ; rw [ show ( -1 + p ) = - ( 1 - p ) by ring, inv_neg ] ; ring;
            · linarith;
            · linarith;
      -- So for all N ≥ K: s(p) ≥ s_K + (1-ε)p^{K+1}(1-p^{N-K}).
      have h_limit_lower (N : ℕ) (hN : K ≤ N) :
          s p ≥ s_n p K + (1 - ε) * p ^ (K + 1) * (1 - p ^ (N - K)) := by
            have h_sum_ge : ∑ n ∈ Finset.Ico (K + 1) (N + 1), (p ^ n * ((1 - p) - s p) - (1 - p) ^ n) ≥ ∑ n ∈ Finset.Ico (K + 1) (N + 1), (p ^ n * (1 - p) * (1 - ε)) := by
              exact Finset.sum_le_sum fun n hn => h_term_ge n <| Finset.mem_Ico.mp hn |>.1;
            have h_sum_ge : ∑ n ∈ Finset.Ico (K + 1) (N + 1), (p ^ n * (1 - p) * (1 - ε)) = (1 - ε) * p ^ (K + 1) * (1 - p ^ (N - K)) := by
              simp_all +decide [ ← Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
              exact Or.inl <| Or.inl <| mul_div_cancel₀ _ <| by linarith;
            linarith [ h_sum_lower N hN, s_n_le_s p ( by linarith ) ( by linarith ) N ( by linarith ) ];
      -- The RHS is increasing in N and → s_K + (1-ε)p^{K+1}. Use ge_of_tendsto:
      have h_tendsto : Filter.Tendsto (fun N => s_n p K + (1 - ε) * p ^ (K + 1) * (1 - p ^ (N - K))) Filter.atTop (nhds (s_n p K + (1 - ε) * p ^ (K + 1))) := by
        exact le_trans ( tendsto_const_nhds.add <| tendsto_const_nhds.mul <| tendsto_const_nhds.sub <| tendsto_pow_atTop_nhds_zero_of_lt_one ( by linarith ) ( by linarith ) |> Filter.Tendsto.comp <| Filter.tendsto_sub_atTop_nat _ ) <| by norm_num;
      exact le_of_tendsto h_tendsto ( Filter.eventually_atTop.mpr ⟨ K, fun N hN => h_limit_lower N hN ⟩ )

/-
Tail sum lower bound: for p with s_K(p) ≥ 0, p > 1/2, s(p) small, and
    ((1-p)/p)^K small, we have s(p) ≥ (1-ε)·p^{K+1}.
-/
lemma prop3_lower (p : ℝ) (K : ℕ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hK : 3 ≤ K)
    (hsK : 0 ≤ s_n p K)
    (hs_small : s p < (1 - p) / 2 * ε)
    (hε : 0 < ε) (hε₁ : ε < 1)
    (h_ratio : ((1 - p) / p) ^ K < (1 - p) / 2 * ε) :
    (1 - ε) * p ^ (K + 1) < s p := by
      -- By term_lower_bound, we have:
      have h_lower_bound : ∀ n ≥ K + 1, p^n * ((1 - p) - s p) - (1 - p)^n > p^n * (1 - p) * (1 - ε) := by
        exact fun n a => term_lower_bound p n K hp hp₁ a hs_small hε h_ratio;
      -- From finite_sum_lower with N = K+1 (single term at n = K+1):
      have h_finite : s_n p (K + 1) ≥ s_n p K + (p^(K + 1) * ((1 - p) - s p) - (1 - p)^(K + 1)) := by
        have h_finite : s_n p (K + 1) ≥ s_n p K + (p^(K + 1) * ((1 - p) - s p) - (1 - p)^(K + 1)) := by
          have h_finite_step : s_n p (K + 1) = s_n p K + p^(K + 1) * D p (K + 1) - (1 - p)^(K + 1) := by
            grind +suggestions
          rw [h_finite_step];
          rw [ show D p ( K + 1 ) = ( 1 - p ) - s_n p K from ?_ ];
          · nlinarith [ pow_pos ( by linarith : 0 < p ) ( K + 1 ), pow_pos ( by linarith : 0 < 1 - p ) ( K + 1 ), show s_n p K ≤ s p from s_n_le_s p ( by linarith ) ( by linarith ) K ( by linarith ) ];
          · exact D_eq_one_sub_p_sub_s_n p ( K + 1 ) ( by linarith );
        exact h_finite;
      -- From term_lower_bound: the term > p^{K+1}(1-p)(1-ε).
      have h_term_lower_bound : p^(K + 1) * ((1 - p) - s p) - (1 - p)^(K + 1) > p^(K + 1) * (1 - p) * (1 - ε) := by
        exact h_lower_bound _ le_rfl;
      -- From tail_ge_limit with K' = K+1 (starting from K+1 instead of K) to get:
      have h_tail : s p ≥ s_n p (K + 1) + (1 - ε) * p^(K + 2) := by
        apply tail_ge_limit;
        · linarith;
        · linarith;
        · grind;
        · exact le_trans hsK ( by linarith [ show 0 ≤ p ^ ( K + 1 ) * ( 1 - p ) * ( 1 - ε ) by exact mul_nonneg ( mul_nonneg ( pow_nonneg ( by linarith ) _ ) ( by linarith ) ) ( by linarith ) ] );
        · grind;
      ring_nf at *;
      nlinarith [ show 0 < p * p ^ K by positivity, show 0 < p ^ 2 * p ^ K by positivity, show 0 < p ^ 3 * p ^ K by positivity, show 0 < p ^ 4 * p ^ K by positivity, show 0 < p ^ 5 * p ^ K by positivity, show 0 < p ^ 6 * p ^ K by positivity, show 0 < p ^ 7 * p ^ K by positivity, show 0 < p ^ 8 * p ^ K by positivity, show 0 < p ^ 9 * p ^ K by positivity, show 0 < p ^ 10 * p ^ K by positivity ]

/-
Tail sum upper bound: for n ≥ K+1 with s_K(p) ≥ 0, each step is ≤ p^n(1-p).
-/
set_option maxHeartbeats 1600000 in
lemma step_increment_upper (p : ℝ) (n : ℕ) (K : ℕ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hK : 3 ≤ K) (hn : K + 1 ≤ n) (hsK : 0 ≤ s_n p K) :
    s_n p n - s_n p (n - 1) ≤ p ^ n * (1 - p) := by
      -- By definition of $s_n$, we know that $s_{n-1}(p) \ge 0$.
      have hs_n_minus_one_nonneg : ∀ m, K ≤ m → 0 ≤ s_n p m := by
        intros m hmK; exact (by
        have h_persist : ∀ m, K ≤ m → 0 ≤ s_n p m := by
          intro m hmK
          have h_step : ∀ k, K ≤ k → 0 ≤ s_n p k → 0 ≤ s_n p (k + 1) := by
            intro k' hk' hsk'; linarith [s_n_mono p hp hp₁ k' (by omega)]
          exact Nat.le_induction hsK ( fun k hk ih => h_step k hk ih ) m hmK;
        exact h_persist m hmK);
      specialize hs_n_minus_one_nonneg ( n - 1 ) ( Nat.le_sub_one_of_lt hn );
      -- Apply step_increment_A with s_{n-1}(p) ≥ 0.
      have h_step : s_n p n - s_n p (n - 1) = p ^ n * D p n - (1 - p) ^ n := by
        apply step_increment_A p n hp hp₁ (by linarith) hs_n_minus_one_nonneg;
      exact h_step.symm ▸ sub_le_iff_le_add'.mpr ( by nlinarith [ show ( 0 : ℝ ) ≤ p ^ n by positivity, show ( 0 : ℝ ) ≤ ( 1 - p ) ^ n by exact pow_nonneg ( by linarith ) _, show D p n ≤ 1 - p by exact D_le_one_sub_p_of_nonneg p n ( by linarith ) hs_n_minus_one_nonneg ] )

/-
Upper bound: s(p) < (1+ε)·p^K when s_{K-1}(p) < 0, s_K(p) ≥ 0,
    and (K+1)²·p^K < ε.
-/
lemma prop3_upper (p : ℝ) (K : ℕ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hK : 3 ≤ K)
    (hsK : 0 ≤ s_n p K)
    (hsK_prev : s_n p (K - 1) < 0)
    (h_sq_bound : (↑K + 1) ^ 2 * p ^ K < ε)
    (_hε : 0 < ε) :
    s p < (1 + ε) * p ^ K := by
      -- By definition of $D$, we know that $D p K = (1 - p) - s_n p (K - 1)$.
      have hD : D p K = (1 - p) - s_n p (K - 1) := by
        exact D_eq_one_sub_p_sub_s_n p K ( by linarith ) ▸ rfl;
      -- By definition of $s$, we know that $s p \leq s_n p K + p^{K+1}$.
      have hs_le : s p ≤ s_n p K + p ^ (K + 1) := by
        have hs_le : ∀ N ≥ K + 1, s_n p N ≤ s_n p K + p ^ (K + 1) := by
          intro N hN
          have h_step : ∀ n ≥ K + 1, s_n p n - s_n p (n - 1) ≤ p ^ n * (1 - p) := by
            intros n hn
            apply step_increment_upper p n K hp hp₁ hK hn hsK;
          have h_sum : s_n p N - s_n p K ≤ ∑ n ∈ Finset.Icc (K + 1) N, p ^ n * (1 - p) := by
            have h_sum : s_n p N - s_n p K = ∑ n ∈ Finset.Icc (K + 1) N, (s_n p n - s_n p (n - 1)) := by
              erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ hN ];
              · exact Nat.recOn N ( Nat.recOn K ( by norm_num ) fun n ihn => by norm_num [ Finset.sum_range_succ ] at * ; linarith ) fun n ihn => by norm_num [ Finset.sum_range_succ ] at * ; linarith;
              · grind;
            exact h_sum.symm ▸ Finset.sum_le_sum fun n hn => h_step n <| Finset.mem_Icc.mp hn |>.1;
          have h_sum_bound : ∑ n ∈ Finset.Icc (K + 1) N, p ^ n * (1 - p) ≤ p ^ (K + 1) * (1 - p) / (1 - p) := by
            have h_sum_bound : ∑ n ∈ Finset.Icc (K + 1) N, p ^ n * (1 - p) ≤ p ^ (K + 1) * (1 - p) * (∑ n ∈ Finset.range (N - K), p ^ n) := by
              erw [ Finset.mul_sum _ _ _, Finset.sum_Ico_eq_sum_range ];
              simp +decide [pow_add, mul_assoc, mul_comm, mul_left_comm];
            exact h_sum_bound.trans ( by rw [ div_eq_mul_inv ] ; exact mul_le_mul_of_nonneg_left ( by rw [ ← tsum_geometric_of_lt_one ( by linarith ) ( by linarith ) ] ; exact Summable.sum_le_tsum ( Finset.range ( N - K ) ) ( fun _ _ => by positivity ) ( by exact summable_geometric_of_lt_one ( by linarith ) ( by linarith ) ) ) ( by exact mul_nonneg ( pow_nonneg ( by linarith ) _ ) ( by linarith ) ) );
          rw [ mul_div_cancel_right₀ ] at h_sum_bound <;> linarith;
        refine' ciSup_le fun N => _;
        by_cases hN : N + 2 ≥ K + 1;
        · exact hs_le _ hN;
        · have h_mono : ∀ n m, 2 ≤ n → n ≤ m → s_n p n ≤ s_n p m := by
            intros n m hn hnm
            have h_mono : ∀ k, 2 ≤ k → s_n p k ≤ s_n p (k + 1) := by
              intros k hk
              apply s_n_mono p hp hp₁ k hk;
            exact Nat.le_induction ( by norm_num ) ( fun k hk ih => by linarith [ h_mono k ( by linarith ) ] ) m hnm;
          exact le_add_of_le_of_nonneg ( h_mono _ _ ( by linarith ) ( by linarith ) ) ( by positivity );
      -- By definition of $s_n$, we know that $s_n p K = s_n p (K - 1) + p^K * D p K + K * p^(K - 1) * (1 - p) * (-s_n p (K - 1)) - (1 - p)^K$.
      have hs_n_K : s_n p K = s_n p (K - 1) + p^K * D p K + K * p^(K - 1) * (1 - p) * (-s_n p (K - 1)) - (1 - p)^K := by
        have := step_formula p K ( show 1 / 2 ≤ p by linarith ) ( show p < 1 by linarith ) ( show 3 ≤ K by linarith ) ; simp_all +decide ; ring_nf;
        unfold s_n at * ; simp_all +decide [ Nat.cast_sub ( show 1 ≤ K from by linarith ) ] ; ring_nf;
        grind +splitIndPred;
      rcases K with ( _ | K ) <;> simp_all +decide [ pow_succ' ];
      refine' lt_of_le_of_lt _ ( mul_lt_mul_of_pos_right ( show 1 + ε > 1 + ( K + 1 + 1 ) * ( K + 1 + 1 ) * p ^ ( K + 1 ) by nlinarith [ pow_pos ( show 0 < p by positivity ) K, pow_succ' p K ] ) ( mul_pos ( show 0 < p by positivity ) ( pow_pos ( show 0 < p by positivity ) K ) ) );
      -- Since $s_n p K$ is negative, we can factor it out and simplify the expression.
      have h_factor : s_n p K * (1 - p * p^K - (K + 1) * p^K * (1 - p)) ≤ 0 := by
        refine mul_nonpos_of_nonpos_of_nonneg hsK_prev.le ?_;
        refine' Nat.recOn K _ _ <;> norm_num [ pow_succ' ] at *;
        intro n hn; nlinarith [ mul_le_mul_of_nonneg_left hp ( show 0 ≤ p ^ n by positivity ), mul_le_mul_of_nonneg_left hp₁.le ( show 0 ≤ p ^ n by positivity ), pow_nonneg ( show 0 ≤ p by linarith ) n, pow_le_pow_of_le_one ( show 0 ≤ p by linarith ) hp₁.le ( show n ≥ 0 by linarith ) ] ;
      ring_nf at *;
      norm_num [ pow_mul ] at *;
      nlinarith [ show 0 ≤ p ^ 2 * ( p ^ K ) ^ 2 by positivity, show 0 ≤ p ^ 2 * ( p ^ K ) ^ 2 * K by positivity, show 0 ≤ p ^ 2 * ( p ^ K ) ^ 2 * K ^ 2 by positivity, show 0 ≤ p * p ^ K by positivity, show 0 ≤ p * p ^ K * K by positivity, show 0 ≤ p * p ^ K * K ^ 2 by positivity, show 0 ≤ p ^ 2 * p ^ K by positivity, show 0 ≤ p ^ 2 * p ^ K * K by positivity, show 0 ≤ p ^ 2 * p ^ K * K ^ 2 by positivity, show 0 ≤ p * ( 1 - p ) ^ K by exact mul_nonneg ( by linarith ) ( pow_nonneg ( by linarith ) _ ), show 0 ≤ ( 1 - p ) ^ K by exact pow_nonneg ( by linarith ) _ ]

/-
Helper: K-1 is negative at the crossing time.
-/
lemma crossing_time_prev_neg (p : ℝ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hphi : p < (Real.sqrt 5 - 1) / 2)
    (hex : ∃ n, 3 ≤ n ∧ 0 ≤ s_n p n) :
    s_n p (Nat.find hex - 1) < 0 := by
      by_cases hK : Nat.find hex = 3;
      · exact hK.symm ▸ s_n_two_neg p hp hp₁ hphi;
      · have hK_ge_4 : 4 ≤ Nat.find hex := by
          exact Nat.succ_le_of_lt ( lt_of_le_of_ne ( Nat.find_spec hex |>.1 ) ( Ne.symm hK ) );
        exact lt_of_not_ge fun h => Nat.find_min hex ( Nat.sub_lt ( by linarith ) zero_lt_one ) ⟨ by omega, h ⟩

/-
Helper: polynomial * geometric tends to 0. For r ∈ (0,1), (n+1)^2 * r^n → 0.
-/
lemma sq_mul_pow_tendsto_zero (r : ℝ) (hr₀ : 0 < r) (hr₁ : r < 1) :
    Filter.Tendsto (fun n : ℕ => (↑n + 1) ^ 2 * r ^ n) Filter.atTop (nhds 0) := by
      -- We can factor out $r^n$ and use the fact that $(n+1)^2$ grows polynomially.
      suffices h_poly : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) Filter.atTop (nhds 0) by
        convert h_poly.add ( Filter.Tendsto.const_mul 2 ( show Filter.Tendsto ( fun n : ℕ => ( n : ℝ ) * r ^ n ) Filter.atTop ( nhds 0 ) from ?_ ) ) |> ( ·.add ( show Filter.Tendsto ( fun n : ℕ => r ^ n ) Filter.atTop ( nhds 0 ) from ?_ ) ) using 2 <;> ring_nf;
        · refine' squeeze_zero_norm' _ h_poly;
          filter_upwards [ Filter.eventually_ge_atTop 1 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_right ( by norm_cast; nlinarith ) ( by positivity ) ;
        · exact tendsto_pow_atTop_nhds_zero_of_lt_one hr₀.le hr₁;
      -- Let $y = n \ln(1/r)$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{y^2}{e^y}$.
      suffices h_log : Filter.Tendsto (fun y : ℝ => y ^ 2 * Real.exp (-y)) Filter.atTop (nhds 0) by
        have h_subst : Filter.Tendsto (fun n : ℕ => (n * Real.log (1 / r)) ^ 2 * Real.exp (-n * Real.log (1 / r))) Filter.atTop (nhds 0) := by
          convert h_log.comp ( tendsto_natCast_atTop_atTop.atTop_mul_const ( Real.log_pos <| one_lt_one_div hr₀ hr₁ ) ) using 2 ; norm_num;
        convert h_subst.div_const ( Real.log ( 1 / r ) ^ 2 ) using 2 <;> norm_num [ Real.exp_neg, Real.exp_nat_mul, Real.exp_log, hr₀, hr₁ ] ; ring_nf;
        norm_num [ show Real.log r ≠ 0 by linarith [ Real.log_le_sub_one_of_pos hr₀ ] ];
      exact ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2 )

/-
Helper: for any M > 0, ∃ N such that for all K ≥ N, (K+1)^2 * r^K < M.
-/
lemma sq_mul_pow_eventually_small (r : ℝ) (hr₀ : 0 < r) (hr₁ : r < 1)
    (M : ℝ) (hM : 0 < M) :
    ∃ N : ℕ, ∀ K : ℕ, N ≤ K → (↑K + 1) ^ 2 * r ^ K < M := by
      -- By the definition of limit, for any ε > 0, there exists an N such that for all K ≥ N, (K+1)^2 * r^K < ε.
      have h_limit : Filter.Tendsto (fun K : ℕ => (K + 1 : ℝ) ^ 2 * r ^ K) Filter.atTop (nhds 0) := by
        -- Apply the lemma sq_mul_pow_tendsto_zero with r.
        apply sq_mul_pow_tendsto_zero r hr₀ hr₁;
      simpa using h_limit.eventually ( gt_mem_nhds hM )

/-
Helper: geometric sequence tends to 0, so eventually small.
-/
lemma pow_eventually_small (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (M : ℝ) (hM : 0 < M) :
    ∃ N : ℕ, ∀ K : ℕ, N ≤ K → r ^ K < M := by
      simpa using ( tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁ ) |> ( fun h => h.eventually ( gt_mem_nhds hM ) ) |> fun h => Filter.eventually_atTop.mp h

set_option maxHeartbeats 800000 in
theorem prop3 (p₀ : ℝ) (hp₀_s : s p₀ = 0) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2)
    (hp₀_right : ∀ p, p₀ < p → p < 1 → 0 < s p) :
    ∀ ε > 0, ∃ δ > 0, ∀ p, p₀ < p → p < p₀ + δ →
      ∀ (hex : ∃ n, 3 ≤ n ∧ 0 ≤ s_n p n),
      let K := Nat.find hex
      (1 - ε) * p ^ (K + 1) < s p ∧ s p < (1 + ε) * p ^ K := by
        intro ε hε_pos
        set ε' := min ε (1 / 2) with hε'_def
        have hε'_pos : 0 < ε' := by
          positivity
        have hε'_le_one : ε' ≤ 1 := by
          exact le_trans ( min_le_right _ _ ) ( by norm_num )
        set r := (p₀ + 1) / 2 with hr_def
        have hr_lt_one : r < 1 := by
          nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]
        have hr_gt_p₀ : p₀ < r := by
          grind +extAll
        obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ K ≥ N₁, (K + 1) ^ 2 * r ^ K < ε' := by
          have := sq_mul_pow_eventually_small r ( by linarith ) hr_lt_one ε' hε'_pos; aesop;
        obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ K ≥ N₂, ((1 - p₀) / p₀) ^ K < (1 - p₀) / 4 * ε' := by
          exact pow_eventually_small _ ( by exact div_nonneg ( by linarith [ show p₀ < 1 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ] ) ( by linarith ) ) ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) _ ( by nlinarith [ show p₀ < 1 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ] )
        obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ p, abs (p - p₀) < δ₂ → abs (s p - s p₀) < (1 - p₀) / 4 * ε' := by
          have h_cont : ContinuousAt s p₀ := by
            exact s_continuousOn.continuousAt <| Ioo_mem_nhds hp₀_half <| by linarith [ Real.sq_sqrt <| show 0 ≤ 5 by norm_num ] ;
          exact Metric.continuousAt_iff.mp h_cont _ ( mul_pos ( div_pos ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) zero_lt_four ) hε'_pos )
        have hδ₂_pos' : 0 < δ₂ := by
          exact hδ₂_pos
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ p, p₀ < p → p < p₀ + δ₁ → ∀ k, 2 ≤ k → k ≤ max N₁ (max N₂ 3) → s_n p k < 0 := by
          apply_rules [ crossing_time_large ];
          exact le_trans ( by norm_num ) ( le_max_right _ _ |> le_trans ( le_max_right _ _ ) )
        have hδ₁_pos' : 0 < δ₁ := by
          exact hδ₁_pos
        use min (min δ₁ δ₂) ((1 - p₀) / 2);
        refine' ⟨ lt_min ( lt_min hδ₁_pos' hδ₂_pos' ) ( by linarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ), fun p hp₁ hp₂ hex => _ ⟩;
        -- Let $K$ be the crossing time for $p$.
        set K := Nat.find hex with hK_def
        have hK_ge : K > max N₁ (max N₂ 3) := by
          grind +splitImp
        have hK_prev_neg : s_n p (K - 1) < 0 := by
          have := Nat.find_min hex ( Nat.sub_lt ( by linarith [ Nat.le_max_right N₁ ( Max.max N₂ 3 ), Nat.le_max_right N₂ 3 ] ) zero_lt_one ) ; simp_all +decide ;
          grind +suggestions
        generalize_proofs at *; (
        -- Apply the results from prop3_lower and prop3_upper.
        have h_lower : (1 - ε') * p ^ (K + 1) < s p := by
          apply prop3_lower p K (by linarith) (by
          linarith [ min_le_left ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_right ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]) (by
          exact le_trans ( by norm_num ) ( le_trans ( le_max_right _ _ ) ( le_max_right _ _ ) ) |> le_trans <| hK_ge.le) (by
          exact Nat.find_spec hex |>.2) (by
          have := hδ₂ p ( abs_lt.mpr ⟨ by linarith [ min_le_left ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_right ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂ ], by linarith [ min_le_left ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_right ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂ ] ⟩ ) ; simp_all +decide [ abs_lt ] ;
          nlinarith [ min_le_left ε 2⁻¹, min_le_right ε 2⁻¹, show ( 2⁻¹ : ℝ ) = 1 / 2 by norm_num, show ( p₀ : ℝ ) > 1 / 2 by exact lt_of_le_of_lt ( by norm_num ) hp₀_half, show ( p : ℝ ) > p₀ by exact hp₁, min_le_left ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_right ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂ ] ;) (by
          exact hε'_pos) (by
          grind +extAll) (by
          refine' lt_of_le_of_lt _ ( hN₂ K ( by linarith [ Nat.le_max_left N₁ ( max N₂ 3 ), Nat.le_max_right N₁ ( max N₂ 3 ), Nat.le_max_left N₂ 3, Nat.le_max_right N₂ 3 ] ) ) |> lt_of_lt_of_le <| _;
          · exact pow_le_pow_left₀ ( div_nonneg ( by linarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂, min_le_left ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_right ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ) ] ) ( by linarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂, min_le_left ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_right ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ) ] ) ) ( by rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂, min_le_left ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_right ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ) ] ) _;
          · exact mul_le_mul_of_nonneg_right ( by linarith [ min_le_left ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_right ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂ ] ) hε'_pos.le)
        have h_upper : s p < (1 + ε') * p ^ K := by
          apply prop3_upper p K (by linarith) (by
          linarith [ min_le_left ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_right ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]) (by
          exact le_trans ( by norm_num ) ( le_trans ( le_max_right _ _ ) ( le_max_right _ _ ) ) |> le_trans <| hK_ge.le) (by
          exact Nat.find_spec hex |>.2) (by
          exact hK_prev_neg) (by
          refine' lt_of_le_of_lt _ ( hN₁ K ( by linarith [ Nat.le_max_left N₁ ( max N₂ 3 ) ] ) );
          exact mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by linarith ) ( by linarith [ min_le_left ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_right ( min δ₁ δ₂ ) ( ( 1 - p₀ ) / 2 ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂ ] ) _ ) ( sq_nonneg _ )) (by
          exact hε'_pos)
        generalize_proofs at *; (
        exact ⟨ by exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_right ( sub_le_sub_left ( min_le_left _ _ ) _ ) ( pow_nonneg ( by linarith ) _ ) ) h_lower, by exact lt_of_lt_of_le h_upper ( mul_le_mul_of_nonneg_right ( by linarith [ min_le_left ε ( 1 / 2 ), min_le_right ε ( 1 / 2 ) ] ) ( pow_nonneg ( by linarith ) _ ) ) ⟩))

-- The right derivative of s at p₀ exists and is positive.
lemma s_n_nonneg_persist (p : ℝ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (n : ℕ) (hn : 2 ≤ n) (h : 0 ≤ s_n p n) (m : ℕ) (hm : n ≤ m) :
    0 ≤ s_n p m := by
  induction hm with
  | refl => exact h
  | step hm' ih => exact le_trans ih (s_n_mono p hp hp₁ _ (le_trans hn hm'))

/-- The delta condition needed for reduced_recurrence follows from Prop 1. -/
lemma delta_nonneg_of_prop1 (p : ℝ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (k : ℕ) (hk : 3 ≤ k) : delta p k ≥ 0 := by
  unfold delta; linarith [v_sub_v_sub_one_ge_one_of_half_le p k hk hp hp₁]

lemma strategy_A (p : ℝ) (n : ℕ) (hn : 3 ≤ n) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hs : 0 ≤ s_n p (n - 1)) :
    v p n = v p (n - 1) + 1 + p ^ n * D p n - (1 - p) ^ n := by
  have hrec := reduced_recurrence p n hn hp hp₁.le
    (fun k hk₁ hk₂ => delta_nonneg_of_prop1 p hp hp₁ k hk₁)
  rw [hrec]
  have heta : eta p n ≤ 0 := by
    have := eta_neg_s_n p n (show 2 ≤ n by omega); linarith
  rw [max_eq_left heta]; ring

lemma strategy_B (p : ℝ) (n : ℕ) (hn : 3 ≤ n) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hs : s_n p (n - 1) < 0) :
    v p n = v p (n - 1) + 1 + p ^ n * D p n +
    ↑n * p ^ (n - 1) * (1 - p) * eta p n - (1 - p) ^ n := by
  have hrec := reduced_recurrence p n hn hp hp₁.le
    (fun k hk₁ hk₂ => delta_nonneg_of_prop1 p hp hp₁ k hk₁)
  rw [hrec]
  have heta : 0 ≤ eta p n := by
    have := eta_neg_s_n p n (show 2 ≤ n by omega); linarith
  rw [max_eq_right heta]

/-- Recurrence formula in the A-case. -/
lemma step_formula_A : ∀ (p : ℝ) (n : ℕ), 3 ≤ n → 1/2 ≤ p → p < 1 →
    0 ≤ s_n p (n - 1) →
    v p n = v p (n - 1) + 1 + p ^ n * D p n - (1 - p) ^ n := strategy_A

/-- Recurrence formula in the B-case. -/
lemma step_formula_B : ∀ (p : ℝ) (n : ℕ), 3 ≤ n → 1/2 ≤ p → p < 1 →
    s_n p (n - 1) < 0 →
    v p n = v p (n - 1) + 1 + p ^ n * D p n +
    ↑n * p ^ (n - 1) * (1 - p) * eta p n - (1 - p) ^ n := strategy_B

theorem step_formula_main (p : ℝ) (hp : 1/2 ≤ p) (hp₁ : p < 1) (n : ℕ) (hn : 3 ≤ n) :
    v p (n - 1) + 1 ≤ v p n
    ∧ (0 ≤ s_n p (n - 1) →
        v p n = v p (n - 1) + 1 + p ^ n * D p n - (1 - p) ^ n)
    ∧ (s_n p (n - 1) < 0 →
        v p n = v p (n - 1) + 1 + p ^ n * D p n +
        ↑n * p ^ (n - 1) * (1 - p) * eta p n - (1 - p) ^ n) :=
  ⟨v_sub_v_sub_one_ge_one_of_half_le p n hn hp hp₁,
   strategy_A p n hn hp hp₁,
   strategy_B p n hn hp hp₁⟩

theorem regime1 (p : ℝ) (hp : (Real.sqrt 5 - 1) / 2 ≤ p) (hp₁ : p < 1)
    (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ s_n p (n - 1) ∧
    v p n = v p (n - 1) + 1 + p ^ n * D p n - (1 - p) ^ n := by
  have hs := s_n_nonneg_of_phi_le p hp hp₁ (n - 1) (by omega)
  exact ⟨hs, strategy_A p n hn (by linarith [half_lt_phi']) hp₁ hs⟩

theorem regime3 (p : ℝ) (hp : 1/2 ≤ p) (hp₁ : p < 1) (hs : s p ≤ 0)
    (n : ℕ) (hn : 2 ≤ n) : s_n p n ≤ 0 :=
  le_trans (s_n_le_s p (by linarith) hp₁.le n hn) hs

theorem regime2 (p : ℝ) (hp : 1/2 ≤ p) (hp₁ : p < 1)
    (hphi : p < (Real.sqrt 5 - 1) / 2) (hs_pos : 0 < s p) :
    ∃ K, 3 ≤ K ∧
    (∀ m, 2 ≤ m → m < K → s_n p m < 0) ∧
    (∀ m, K ≤ m → 0 ≤ s_n p m) := by
  have hs2_neg := s_n_two_neg p hp hp₁ hphi
  obtain ⟨k, hk⟩ : ∃ k, 0 < s_n p (k + 2) := by
    by_contra h; push_neg at h
    exact absurd (ciSup_le fun n => h n) (not_le.mpr hs_pos)
  have hk_pos : 1 ≤ k := by
    rcases k with _ | k
    · exact absurd hk (not_lt.mpr hs2_neg.le)
    · omega
  have hex : ∃ n, 3 ≤ n ∧ 0 ≤ s_n p n := ⟨k + 2, by omega, hk.le⟩
  set K := Nat.find hex
  have hK_spec := Nat.find_spec hex
  refine ⟨K, hK_spec.1, ?_, ?_⟩
  · intro m hm₁ hm₂
    rcases Nat.lt_or_ge m 3 with hlt | hge
    · interval_cases m; exact hs2_neg
    · have : ¬ (3 ≤ m ∧ 0 ≤ s_n p m) := Nat.find_min hex hm₂
      push_neg at this; exact this hge
  · exact fun m hm => s_n_nonneg_persist p hp hp₁ K (by omega) hK_spec.2 m hm

/-
p^k - q^k ≤ k · r^{k-1} · (p - q) for 0 ≤ q ≤ p ≤ r
-/
lemma pow_diff_le_bound (p q r : ℝ) (k : ℕ) (_hk : 1 ≤ k)
    (hq : 0 ≤ q) (hqp : q ≤ p) (hpr : p ≤ r) :
    p ^ k - q ^ k ≤ ↑k * r ^ (k - 1) * (p - q) := by
      have h_factor : p^k - q^k = (p - q) * ∑ i ∈ Finset.range k, p^i * q^(k - 1 - i) := by
        rw [ ← geom_sum₂_mul, mul_comm ];
      -- Each term $p^i q^{k-1-i}$ is less than or equal to $r^{k-1}$ since $p, q \leq r$.
      have h_term : ∀ i ∈ Finset.range k, p^i * q^(k - 1 - i) ≤ r^(k - 1) := by
        intro i hi; rw [ show r ^ ( k - 1 ) = r ^ i * r ^ ( k - 1 - i ) by rw [ ← pow_add, Nat.add_sub_of_le ( Nat.le_sub_one_of_lt ( Finset.mem_range.mp hi ) ) ] ] ; gcongr;
        · exact pow_nonneg ( by linarith ) _;
        · linarith;
        · linarith;
      simpa [ mul_assoc, mul_comm, mul_left_comm, h_factor ] using mul_le_mul_of_nonneg_left ( Finset.sum_le_sum h_term ) ( sub_nonneg.mpr hqp )

/-- (1-q)^k - (1-p)^k ≤ k · (1/2)^{k-1} · (p - q) for 1/2 ≤ q ≤ p ≤ 1 -/
lemma one_sub_pow_diff_le_bound (p q : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hq : 1/2 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1) :
    (1 - q) ^ k - (1 - p) ^ k ≤ ↑k * (1/2) ^ (k - 1) * (p - q) := by
  have := pow_diff_le_bound (1 - q) (1 - p) (1/2) k hk (by linarith) (by linarith) (by linarith)
  linarith

/-
|max(0,-a) - max(0,-b)| ≤ |a - b|
-/
lemma abs_max_neg_sub_le (a b : ℝ) :
    |max 0 (-a) - max 0 (-b)| ≤ |a - b| := by
      grind +qlia

/-
|x^{k-1}(1-x) - y^{k-1}(1-y)| ≤ k · r^{k-2} · |x-y| for x, y ∈ [0, r], r < 1, k ≥ 2
-/
lemma alpha_coeff_diff_bound (p q r : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hq : 0 ≤ q) (hqp : q ≤ p) (hpr : p ≤ r) (_hr : r < 1) :
    p ^ (k - 1) * (1 - p) - q ^ (k - 1) * (1 - q) ≤ ↑k * r ^ (k - 2) * (p - q) := by
      have h_diff_bound : p ^ (k - 1) * (1 - p) - q ^ (k - 1) * (1 - q) = (p ^ (k - 1) - q ^ (k - 1)) - (p ^ k - q ^ k) := by
        cases k <;> norm_num [ pow_succ' ] at * ; linarith;
      have h_pow_diff_bound : p ^ (k - 1) - q ^ (k - 1) ≤ (k - 1) * r ^ (k - 2) * (p - q) := by
        convert pow_diff_le_bound p q r ( k - 1 ) ( Nat.sub_pos_of_lt hk ) hq hqp hpr using 1 ; cases k <;> norm_num at *;
        grind;
      nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast, show 0 ≤ ( k - 1 : ℝ ) * r ^ ( k - 2 ) * ( p - q ) by exact mul_nonneg ( mul_nonneg ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) <| pow_nonneg ( by linarith ) _ ) <| sub_nonneg.mpr hqp, show p ^ k - q ^ k ≥ 0 by exact sub_nonneg.mpr <| pow_le_pow_left₀ ( by linarith ) hqp _ ]

/-
Absolute bound on per-step difference: for k ≥ 3 and p > q in [1/2, r] with r < φ,
    |(s_k(p) - s_{k-1}(p)) - (s_k(q) - s_{k-1}(q))| ≤ A · k² · r^{k-2} · (p - q)
    where A = 50 is a safe constant.
-/
set_option maxHeartbeats 400000 in
lemma step_diff_abs_bound (q p r : ℝ) (k : ℕ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hpr : p ≤ r) (hr : r < (Real.sqrt 5 - 1) / 2) (hk : 3 ≤ k) :
    |((v p k - v p (k-1)) - (v q k - v q (k-1)))| ≤ 50 * ↑k ^ 2 * r ^ (k - 2) * (p - q) := by
  -- Upper bound from step_diff_bound_k3
  have h_upper := step_diff_bound_k3 q p k hq hqp (by linarith [phi_lt_one']) hk
  have h_lower : v p k - v p (k - 1) - (v q k - v q (k - 1)) ≥ -18 * r ^ k * (p - q) - k * r ^ (k - 1) * (1 / 2) * 17 * (p - q) := by
    have h_lower_bound : v p k - v p (k - 1) - (v q k - v q (k - 1)) ≥ -r ^ k * 18 * (p - q) + k * p ^ (k - 1) * (1 - p) * (max 0 (-s_n p (k - 1)) - max 0 (-s_n q (k - 1))) := by
      have h_lower_bound : v p k - v p (k - 1) - 1 = p ^ k * D p k + k * p ^ (k - 1) * (1 - p) * max 0 (-s_n p (k - 1)) - (1 - p) ^ k := by
        apply step_formula;
        · grobner;
        · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
        · linarith
      have h_lower_bound_q : v q k - v q (k - 1) - 1 = q ^ k * D q k + k * q ^ (k - 1) * (1 - q) * max 0 (-s_n q (k - 1)) - (1 - q) ^ k := by
        apply step_formula q k hq (by
        nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]) hk
      simp_all +decide [ sub_eq_iff_eq_add ];
      have h_lower_bound : p ^ k * D p k - q ^ k * D q k ≥ -r ^ k * 18 * (p - q) := by
        have h_lower_bound : D p k - D q k ≥ -18 * (p - q) := by
          have h_lower_bound : v p (k - 1) - v q (k - 1) ≤ 18 * (p - q) := by
            have h_lower_bound : s_n p (k - 1) - s_n q (k - 1) < 17 * (p - q) := by
              have := dipvsdiq_upper q p ( k - 1 ) ( by norm_num at *; linarith ) ( by linarith ) ( by linarith ) ( by omega ) ; norm_num at * ; linarith;
            unfold s_n at *;
            linarith;
          unfold D; linarith;
        have h_lower_bound : p ^ k * (D p k - D q k) ≥ -r ^ k * 18 * (p - q) := by
          have h_lower_bound : p ^ k ≥ 0 := by
            exact pow_nonneg ( by linarith [ inv_pos.mpr ( by norm_num : ( 0 : ℝ ) < 2 ) ] ) _;
          have h_lower_bound : p ^ k ≤ r ^ k := by
            exact pow_le_pow_left₀ ( by linarith [ inv_pos.mpr ( by norm_num : ( 0 : ℝ ) < 2 ) ] ) hpr _;
          nlinarith [ pow_nonneg ( by linarith : 0 ≤ p ) k, pow_nonneg ( by linarith : 0 ≤ r ) k ];
        refine le_trans h_lower_bound ?_;
        rw [ mul_sub ];
        nontriviality;
        gcongr;
        exact sub_nonneg_of_le <| by exact le_trans ( v_le_n _ _ ( by positivity ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ) <| by norm_num;
      have h_lower_bound : k * q ^ (k - 1) * (1 - q) * max 0 (-s_n q (k - 1)) ≤ k * p ^ (k - 1) * (1 - p) * max 0 (-s_n q (k - 1)) := by
        apply_rules [ mul_le_mul_of_nonneg_right, mul_le_mul_of_nonneg_left ];
        · apply_rules [ alpha_coeff_mono_phi ];
          · exact le_trans ( by norm_num ) hq;
          · linarith;
          · linarith;
        · positivity;
      have h_lower_bound : (1 - q) ^ k - (1 - p) ^ k ≥ 0 := by
        exact sub_nonneg_of_le ( pow_le_pow_left₀ ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( by linarith ) _ );
      grind;
    have h_lower_bound : max 0 (-s_n p (k - 1)) - max 0 (-s_n q (k - 1)) ≥ -17 * (p - q) := by
      have h_lower_bound : s_n p (k - 1) - s_n q (k - 1) < 17 * (p - q) := by
        have := dipvsdiq_upper q p ( k - 1 ) hq hqp ( by linarith ) ( Nat.le_sub_one_of_lt hk ) ; rcases k with ( _ | _ | k ) <;> norm_num at * ; linarith;
      cases max_cases ( 0 : ℝ ) ( -s_n p ( k - 1 ) ) <;> cases max_cases ( 0 : ℝ ) ( -s_n q ( k - 1 ) ) <;> linarith;
    have h_lower_bound : k * p ^ (k - 1) * (1 - p) ≤ k * r ^ (k - 1) * (1 / 2) := by
      gcongr;
      · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      · exact mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by linarith ) _ );
      · linarith;
      · grind;
    nlinarith [ show 0 ≤ ( k : ℝ ) * p ^ ( k - 1 ) * ( 1 - p ) by exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by linarith ) _ ) ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ];
  refine' abs_le.mpr ⟨ _, _ ⟩;
  · have h_neg : -(50 * k ^ 2 * r ^ (k - 2) * (p - q)) ≤ -(18 * r ^ k * (p - q)) - (k * r ^ (k - 1) * (1 / 2) * 17 * (p - q)) := by
      have h_neg : 18 * r ^ 2 + (k : ℝ) * r * (1 / 2) * 17 ≤ 50 * k ^ 2 := by
        nlinarith only [ show ( k : ℝ ) ≥ 3 by norm_cast, show r ≤ 1 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ], show r ≥ 0 by linarith, hr, Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ' ] at *;
      convert mul_le_mul_of_nonneg_right h_neg ( show 0 ≤ r ^ k * ( p - q ) by exact mul_nonneg ( pow_nonneg ( by linarith ) _ ) ( by linarith ) ) using 1 ; ring!;
      ring!;
    linarith;
  · -- Apply the bounds from `pow_diff_le_bound` and `alpha_coeff_diff_bound`.
    have h_pow_diff : p ^ k - q ^ k ≤ k * r ^ (k - 1) * (p - q) := by
      apply pow_diff_le_bound p q r k (by linarith) (by linarith) (by linarith) (by linarith)
    have h_alpha_coeff_diff : p ^ (k - 1) * (1 - p) - q ^ (k - 1) * (1 - q) ≤ k * r ^ (k - 2) * (p - q) := by
      apply alpha_coeff_diff_bound p q r k (by linarith) (by linarith) (by linarith) (by linarith) (by
      nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]);
    have h_one_sub_pow_diff : (1 - q) ^ k - (1 - p) ^ k ≤ k * (1 / 2) ^ (k - 1) * (p - q) := by
      convert one_sub_pow_diff_le_bound p q k ( by linarith ) hq hqp.le ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) using 1;
    -- Since $r < \phi$, we have $(1/2)^{k-1} \leq r^{k-2}$.
    have h_half_pow_le_r_pow : (1 / 2 : ℝ) ^ (k - 1) ≤ r ^ (k - 2) := by
      exact le_trans ( pow_le_pow_left₀ ( by norm_num ) ( show ( 1 / 2 : ℝ ) ≤ r by linarith ) _ ) ( pow_le_pow_of_le_one ( by linarith ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( by omega ) );
    refine' le_trans h_upper _;
    nontriviality;
    refine' le_trans ( add_le_add_three h_pow_diff ( mul_le_mul_of_nonneg_left h_alpha_coeff_diff <| Nat.cast_nonneg _ ) h_one_sub_pow_diff ) _;
    rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ' ] at *;
    refine' le_trans ( add_le_add_three le_rfl le_rfl ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_half_pow_le_r_pow <| by positivity ) <| by linarith ) ) _;
    nontriviality;
    norm_num [ Nat.succ_eq_add_one, add_assoc ] at *;
    nlinarith [ show 0 ≤ ( k + 2 : ℝ ) * r ^ k * ( p - q ) by exact mul_nonneg ( mul_nonneg ( by positivity ) ( pow_nonneg ( by linarith ) _ ) ) ( by linarith ), show r ≤ 1 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ]

/-
Each step s_k(p) - s_{k-1}(p) is bounded by (k+1)*r^{k-1}
-/
lemma step_size_bound (p r : ℝ) (k : ℕ) (hp : 1/2 ≤ p) (hpr : p ≤ r) (hr : r < 1)
    (hk : 3 ≤ k) :
    |s_n p k - s_n p (k - 1)| ≤ (↑k + 1) * r ^ (k - 1) := by
  have h_bound : s_n p k - s_n p (k - 1) = p ^ k * D p k + k * p ^ (k - 1) * (1 - p) * max 0 (-s_n p (k - 1)) - (1 - p) ^ k := by
    unfold s_n D; rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ' ] at *;
    convert step_formula p ( k + 2 ) hp ( by linarith ) ( by linarith ) using 1 ; ring_nf;
    · rw [ show 2 + k - 1 = 1 + k by rw [ Nat.sub_eq_of_eq_add ] ; ring ];
    · unfold D s_n; norm_num [ pow_succ' ] ; ring_nf;
      norm_num;
  have h_bound : p ^ k * D p k + k * p ^ (k - 1) * (1 - p) * max 0 (-s_n p (k - 1)) - (1 - p) ^ k ≤ (k + 1) * r ^ (k - 1) := by
    have h_bound : p ^ k * D p k + k * p ^ (k - 1) * (1 - p) * max 0 (-s_n p (k - 1)) ≤ r ^ k + k * r ^ (k - 1) * (1 / 2) := by
      refine' add_le_add _ _;
      · refine' le_trans ( mul_le_mul_of_nonneg_left ( D_le_one p k hp ( by linarith ) ( by linarith ) ) ( by positivity ) ) _;
        simpa using pow_le_pow_left₀ ( by linarith ) hpr k;
      · refine' le_trans ( mul_le_mul_of_nonneg_left ( show max 0 ( -s_n p ( k - 1 ) ) ≤ 1 by exact max_le ( by norm_num ) ( by linarith [ s_n_ge_neg_one p ( k - 1 ) ( by linarith ) ( by linarith ) ( Nat.le_sub_one_of_lt ( by linarith ) ) ] ) ) ( by exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by linarith ) _ ) ) ( by linarith ) ) ) _;
        norm_num [ mul_assoc ];
        exact mul_le_mul_of_nonneg_left ( mul_le_mul ( pow_le_pow_left₀ ( by linarith ) hpr _ ) ( by linarith ) ( by linarith ) ( by exact pow_nonneg ( by linarith ) _ ) ) ( by positivity );
    rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ' ] at *;
    exact le_add_of_le_of_nonneg ( by nlinarith [ show 0 ≤ r * r ^ k by exact mul_nonneg ( by linarith ) ( pow_nonneg ( by linarith ) _ ) ] ) ( mul_nonneg ( by linarith ) ( mul_nonneg ( by linarith ) ( pow_nonneg ( by linarith ) _ ) ) );
  have h_bound_neg : p ^ k * D p k + k * p ^ (k - 1) * (1 - p) * max 0 (-s_n p (k - 1)) - (1 - p) ^ k ≥ -(k + 1) * r ^ (k - 1) := by
    nontriviality;
    have h_bound_neg : p ^ k * D p k + k * p ^ (k - 1) * (1 - p) * max 0 (-s_n p (k - 1)) ≥ 0 := by
      have h_bound_neg : D p k ≥ 0 := by
        have h_bound_neg : v p (k - 1) ≤ k - 1 := by
          convert v_le_n ( k - 1 ) p ( by linarith ) ( by linarith ) using 1 ; cases k <;> norm_num at *;
        exact sub_nonneg_of_le ( by cases k <;> norm_num at * ; linarith );
      exact add_nonneg ( mul_nonneg ( pow_nonneg ( by linarith ) _ ) h_bound_neg ) ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by linarith ) _ ) ) ( by linarith ) ) ( le_max_left _ _ ) );
    have h_bound_neg : (1 - p) ^ k ≤ (k + 1) * r ^ (k - 1) := by
      have h_bound_neg : (1 - p) ^ k ≤ (1 / 2) ^ k := by
        exact pow_le_pow_left₀ ( by linarith ) ( by linarith ) _;
      refine le_trans h_bound_neg ?_;
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by linarith ) ( show r ≥ 1 / 2 by linarith ) _ ) ( by positivity ) );
      rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ' ] at *;
      linarith;
    linarith;
  grind

/-
The tail sum Σ_{k=n+1}^m of step differences is bounded by the sum of absolute bounds
-/
lemma finite_tail_diff_bound (q p r : ℝ) (n m : ℕ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hpr : p ≤ r) (hr : r < (Real.sqrt 5 - 1) / 2) (hn : 2 ≤ n) (hnm : n ≤ m) :
    |s_n p m - s_n p n - (s_n q m - s_n q n)| ≤
    50 * (p - q) * ∑ k ∈ Finset.Icc (n + 1) m, ↑k ^ 2 * r ^ (k - 2) := by
  -- By induction on m, telescoping using step_diff_abs_bound.
  induction' hnm with m hm ih <;> norm_num at *;
  -- By the properties of the absolute value and the triangle inequality, we can split the sum into two parts.
  have h_split : |s_n p (m + 1) - s_n p n - (s_n q (m + 1) - s_n q n)| ≤ |s_n p m - s_n p n - (s_n q m - s_n q n)| + |(s_n p (m + 1) - s_n p m) - (s_n q (m + 1) - s_n q m)| := by
    grind;
  -- Apply the induction hypothesis to bound the first part of the sum.
  have h_ind : |s_n p m - s_n p n - (s_n q m - s_n q n)| ≤ 50 * (p - q) * ∑ k ∈ Finset.Icc (n + 1) m, (k : ℝ) ^ 2 * r ^ (k - 2) := by
    exact ih;
  -- Apply the step_diff_abs_bound lemma to bound the second part of the sum.
  have h_step : |(s_n p (m + 1) - s_n p m) - (s_n q (m + 1) - s_n q m)| ≤ 50 * (m + 1 : ℝ) ^ 2 * r ^ (m - 1) * (p - q) := by
    have h_step : |(v p (m + 1) - v p m) - (v q (m + 1) - v q m)| ≤ 50 * (m + 1 : ℝ) ^ 2 * r ^ (m - 1) * (p - q) := by
      have := step_diff_abs_bound q p r ( m + 1 ) hq hqp hpr hr ( by linarith ) ; aesop;
    convert h_step using 1;
    unfold s_n; ring_nf;
  erw [ Finset.sum_Ico_succ_top ( by linarith ), mul_add ];
  convert h_split.trans ( add_le_add h_ind h_step ) using 1 ; push_cast ; ring!

/-
Tail of the series Σ_{k=N}^∞ k² r^k converges and is bounded
-/
lemma sq_pow_series_tail_bound (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
    ∑' (k : ℕ), (↑(k + n + 1)) ^ 2 * r ^ (k + n - 1) ≤ C * (↑n + 1) ^ 2 * r ^ (n - 1) := by
  -- Using k² ≤ 2(n+1)² + 2(k-n-1)² and geometric series formulas.
  -- We can use the fact that Σ k^2 r^k converges and is bounded.
  have h_series_conv : Summable (fun k : ℕ => (k : ℝ) ^ 2 * r ^ k) := by
    refine' summable_of_ratio_norm_eventually_le _ _;
    exact ( 1 + r ) / 2;
    · linarith;
    · -- We'll use the fact that |r| < 1 to find such an N.
      have h_eventually : ∃ N, ∀ n ≥ N, (n + 1 : ℝ) ^ 2 * r ≤ (1 + r) / 2 * n ^ 2 := by
        exact ⟨ 2 * ( 1 + r ) / ( 1 - r ), fun n hn => by nlinarith [ mul_div_cancel₀ ( 2 * ( 1 + r ) ) ( by linarith : ( 1 - r ) ≠ 0 ), sq_nonneg ( n - 2 * ( 1 + r ) / ( 1 - r ) ) ] ⟩;
      norm_num +zetaDelta at *;
      obtain ⟨ N, hN ⟩ := h_eventually; exact ⟨ ⌈N⌉₊, fun n hn => by rw [ abs_of_pos hr0 ] ; convert mul_le_mul_of_nonneg_right ( hN n ( Nat.le_of_ceil_le hn ) ) ( pow_nonneg hr0.le n ) using 1 <;> ring ⟩ ;
  -- We can use the fact that Σ (k + n + 1)^2 r^(k + n - 1) is bounded above by a constant multiple of (n + 1)^2 r^(n - 1).
  have h_sum_bound : ∃ C > 0, ∀ n : ℕ, 2 ≤ n → ∑' k : ℕ, ((k + n + 1 : ℝ) ^ 2) * r ^ (k + n - 1) ≤ C * (n + 1) ^ 2 * r ^ (n - 1) := by
    have h_series_bound : ∃ C > 0, ∀ n : ℕ, ∑' k : ℕ, ((k + n + 1 : ℝ) ^ 2) * r ^ k ≤ C * (n + 1) ^ 2 := by
      -- We can use the fact that $(k + n + 1)^2 \leq 4(n + 1)^2 + 4k^2$ for all $k$ and $n$.
      have h_bound : ∀ n k : ℕ, ((k + n + 1 : ℝ) ^ 2) ≤ 4 * (n + 1) ^ 2 + 4 * (k : ℝ) ^ 2 := by
        exact fun n k => by nlinarith only [ sq ( k - n : ℝ ) ] ;
      -- Using the bound, we can show that the sum is bounded above by a constant multiple of $(n + 1)^2$.
      have h_sum_bound : ∀ n : ℕ, ∑' k : ℕ, ((k + n + 1 : ℝ) ^ 2) * r ^ k ≤ 4 * (n + 1) ^ 2 * ∑' k : ℕ, r ^ k + 4 * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k := by
        intro n; rw [ ← tsum_mul_left, ← tsum_mul_left ] ; rw [ ← Summable.tsum_add ] ; refine' Summable.tsum_le_tsum _ _ _;
        · exact fun k => by nlinarith only [ h_bound n k, pow_nonneg hr0.le k ] ;
        · refine' Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => mul_le_mul_of_nonneg_right ( h_bound n k ) ( by positivity ) ) _;
          ring_nf;
          exact Summable.add ( Summable.add ( Summable.add ( Summable.mul_right _ <| Summable.mul_left _ <| summable_geometric_of_lt_one hr0.le hr1 ) <| Summable.mul_right _ <| Summable.mul_left _ <| summable_geometric_of_lt_one hr0.le hr1 ) <| Summable.mul_right _ h_series_conv ) <| Summable.mul_right _ <| summable_geometric_of_lt_one hr0.le hr1;
        · exact Summable.add ( Summable.mul_left _ ( summable_geometric_of_lt_one hr0.le hr1 ) ) ( Summable.mul_left _ h_series_conv );
        · exact Summable.mul_left _ ( summable_geometric_of_lt_one hr0.le hr1 );
        · exact Summable.mul_left _ h_series_conv;
      refine' ⟨ 4 * ( ∑' k : ℕ, r ^ k ) + 4 * ( ∑' k : ℕ, ( k : ℝ ) ^ 2 * r ^ k ) + 1, _, _ ⟩;
      · exact add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg zero_le_four ( tsum_nonneg fun _ => pow_nonneg hr0.le _ ) ) ( mul_nonneg zero_le_four ( tsum_nonneg fun _ => mul_nonneg ( sq_nonneg _ ) ( pow_nonneg hr0.le _ ) ) ) ) zero_lt_one;
      · intro n; nlinarith [ h_sum_bound n, show ( n : ℝ ) ^ 2 ≥ 0 by positivity, show ( n : ℝ ) ≥ 0 by positivity, show ( ∑' k : ℕ, r ^ k ) ≥ 0 by exact tsum_nonneg fun _ => pow_nonneg hr0.le _, show ( ∑' k : ℕ, ( k : ℝ ) ^ 2 * r ^ k ) ≥ 0 by exact tsum_nonneg fun _ => mul_nonneg ( sq_nonneg _ ) ( pow_nonneg hr0.le _ ) ] ;
    obtain ⟨ C, hC_pos, hC ⟩ := h_series_bound; use C, hC_pos; intro n hn; convert mul_le_mul_of_nonneg_right ( hC n ) ( pow_nonneg hr0.le ( n - 1 ) ) using 1 ; rw [ ← tsum_mul_right ] ; congr ; ext k ; rcases n with ( _ | n ) <;> simp_all +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm ] ;
  grind

/-
One-sided tail bound: for q < p in [1/2, r], r < φ, n ≥ 2:
    |s(p) - s_n(p,n) - (s(q) - s_n(q,n))| ≤ 50*(p-q) * tsum_bound
-/
lemma tail_lipschitz_one_sided (q p r : ℝ) (n : ℕ) (hq : 1/2 ≤ q) (hqp : q < p)
    (hpr : p ≤ r) (hr : r < (Real.sqrt 5 - 1) / 2) (hn : 2 ≤ n) :
    |s p - s_n p n - (s q - s_n q n)| ≤
    50 * (p - q) * ∑' k : ℕ, (↑(k + n + 1)) ^ 2 * r ^ (k + n - 1) := by
      -- By definition of $s$, we know that $s p = \lim_{m \to \infty} s_n p m$ and $s q = \lim_{m \to \infty} s_n q m$.
      have h_lim : Filter.Tendsto (fun m => s_n p m) Filter.atTop (nhds (s p)) ∧ Filter.Tendsto (fun m => s_n q m) Filter.atTop (nhds (s q)) := by
        constructor;
        · have h_tendsto_p : Filter.Tendsto (fun m => s_n p (m + 2)) Filter.atTop (nhds (s p)) := by
            apply tendsto_s_n;
            · linarith;
            · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
          rw [ ← Filter.tendsto_add_atTop_iff_nat 2 ] ; aesop;
        · have := tendsto_s_n q ( by linarith ) ( by linarith [ show ( Real.sqrt 5 - 1 ) / 2 < 1 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ] );
          rw [ ← Filter.tendsto_add_atTop_iff_nat 2 ] ; aesop;
      have h_bound : ∀ m ≥ n, |s_n p m - s_n p n - (s_n q m - s_n q n)| ≤ 50 * (p - q) * ∑ k ∈ Finset.Icc (n + 1) m, (k : ℝ) ^ 2 * r ^ (k - 2) := by
        intros m hm
        apply finite_tail_diff_bound q p r n m hq hqp hpr hr hn hm;
      have h_sum_bound : Filter.Tendsto (fun m => ∑ k ∈ Finset.Icc (n + 1) m, (k : ℝ) ^ 2 * r ^ (k - 2)) Filter.atTop (nhds (∑' k : ℕ, (k + n + 1 : ℝ) ^ 2 * r ^ (k + n - 1))) := by
        have h_sum_bound : Filter.Tendsto (fun m => ∑ k ∈ Finset.range (m - n), (k + n + 1 : ℝ) ^ 2 * r ^ (k + n - 1)) Filter.atTop (nhds (∑' k : ℕ, (k + n + 1 : ℝ) ^ 2 * r ^ (k + n - 1))) := by
          refine' ( Summable.hasSum _ ) |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_sub_atTop_nat n;
          have h_summable : Summable (fun k : ℕ => (k + 1 : ℝ) ^ 2 * r ^ k) := by
            refine' summable_of_ratio_norm_eventually_le _ _;
            exact ( 1 + r ) / 2;
            · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
            · -- We'll use the fact that |r| < 1 to find such an N.
              have h_ratio : ∃ N, ∀ n ≥ N, |r| * (n + 2 : ℝ) ^ 2 ≤ (1 + r) / 2 * (n + 1 : ℝ) ^ 2 := by
                use Nat.ceil (2 * (1 + r) / (1 - r)), fun n hn => by
                  rw [ abs_of_nonneg ( by linarith ) ];
                  have := Nat.le_ceil ( 2 * ( 1 + r ) / ( 1 - r ) );
                  rw [ div_le_iff₀ ] at this <;> nlinarith [ show r < 1 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ], pow_two_nonneg ( n - 1 ) ];
              norm_num +zetaDelta at *;
              obtain ⟨ N, hN ⟩ := h_ratio; exact ⟨ ⌈N⌉₊, fun n hn => by have := hN n ( Nat.le_of_ceil_le hn ) ; ring_nf at this ⊢; nlinarith [ pow_nonneg ( abs_nonneg r ) n ] ⟩ ;
          have h_summable : Summable (fun k : ℕ => (k + n + 1 : ℝ) ^ 2 * r ^ (k + n - 1)) := by
            have : Summable (fun k : ℕ => (k + n + 1 : ℝ) ^ 2 * r ^ (k + n)) := by
              convert h_summable.comp_injective ( add_left_injective n ) using 2 ; aesop
            convert this.mul_left ( 1 / r ) using 2 ; ring_nf;
            cases n <;> simp_all +decide [pow_add] ; ring_nf;
            grind;
          convert h_summable using 1;
        refine h_sum_bound.congr' ?_;
        filter_upwards [ Filter.eventually_ge_atTop n ] with m hm;
        erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
        rw [ Nat.add_sub_add_right ] ; rfl;
      have h_lim_bound : Filter.Tendsto (fun m => |s_n p m - s_n p n - (s_n q m - s_n q n)|) Filter.atTop (nhds (|s p - s_n p n - (s q - s_n q n)|)) := by
        exact Filter.Tendsto.abs ( Filter.Tendsto.sub ( h_lim.1.sub_const _ ) ( h_lim.2.sub_const _ ) );
      exact le_of_tendsto_of_tendsto h_lim_bound ( by simpa using h_sum_bound.const_mul _ ) ( Filter.eventually_atTop.mpr ⟨ n, fun m hm => h_bound m hm ⟩ )

/-
The tail s(p) - s_n(p) satisfies a Lipschitz estimate with vanishing constant.
-/
theorem tail_lipschitz_estimate' (r : ℝ) (hr_pos : 1/2 < r) (hr_lt : r < (Real.sqrt 5 - 1) / 2) :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n → ∀ p q : ℝ, 1/2 ≤ p → p ≤ r → 1/2 ≤ q → q ≤ r →
    |s p - s_n p n - (s q - s_n q n)| ≤ C * (↑n + 1) ^ 2 * r ^ n * |p - q| := by
      -- Set C = 50 * C_series / r. This is positive since r > 0 and C_series > 0.
      obtain ⟨C_series, hC_series_pos, hC_series⟩ : ∃ C_series > 0, ∀ n : ℕ, 2 ≤ n → ∑' k : ℕ, (↑(k + n + 1)) ^ 2 * r ^ (k + n - 1) ≤ C_series * (↑n + 1) ^ 2 * r ^ (n - 1) := by
        apply sq_pow_series_tail_bound r (by linarith) (by nlinarith [Real.sq_sqrt (show 0 ≤ 5 by norm_num)]);
      refine' ⟨ 50 * C_series / r, _, _ ⟩;
      · exact div_pos ( mul_pos ( by norm_num ) hC_series_pos ) ( by linarith );
      · intro n hn p q hp hp' hq hq'_r
        by_cases hpq : p = q;
        · aesop;
        · by_cases hpq' : p < q;
          · have := tail_lipschitz_one_sided p q r n ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith );
            convert this.trans _ using 1;
            · rw [ abs_sub_comm ];
            · convert mul_le_mul_of_nonneg_left ( hC_series n hn ) ( show 0 ≤ 50 * ( q - p ) by linarith ) using 1 ; ring_nf;
              rw [ abs_of_neg ( by linarith : p - q < 0 ) ] ; cases n <;> norm_num [ pow_succ' ] at * ; ring_nf;
              grind;
          · have := tail_lipschitz_one_sided q p r n hq ( lt_of_le_of_ne ( le_of_not_gt hpq' ) ( Ne.symm hpq ) ) hp' hr_lt hn;
            refine le_trans this ?_;
            convert mul_le_mul_of_nonneg_left ( hC_series n hn ) ( show 0 ≤ 50 * ( p - q ) by linarith ) using 1 ; ring_nf;
            rw [ abs_of_nonneg ( by linarith : 0 ≤ p - q ) ] ; cases n <;> norm_num [ pow_succ' ] at * ; ring_nf;
            grind

/-- The tail s(p) - s_n(p) satisfies a Lipschitz estimate with vanishing
  constant. -/
lemma tail_lipschitz_estimate (r : ℝ) (hr_pos : 1/2 < r) (hr_lt : r < (Real.sqrt 5 - 1) / 2) :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n → ∀ p q : ℝ, 1/2 ≤ p → p ≤ r → 1/2 ≤ q → q ≤ r →
    |s p - s_n p n - (s q - s_n q n)| ≤ C * (↑n + 1) ^ 2 * r ^ n * |p - q| :=
  tail_lipschitz_estimate' r hr_pos hr_lt

/-
s_n(·, k) is differentiable at p₀ (by induction using strategy B recurrence).
-/
lemma s_n_differentiableAt_p0 (p₀ : ℝ) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2) (hp₀_s : s p₀ = 0)
    (k : ℕ) (hk : 2 ≤ k) :
    DifferentiableAt ℝ (fun p => s_n p k) p₀ := by
  -- By induction on $k \geq 2$, we can show that $s_n(·, k)$ is differentiable at $p₀$.
  induction' k, Nat.succ_le_iff.mpr hk using Nat.le_induction with k ih;
  · unfold s_n; norm_num [ v_two ] ; ring_nf;
    refine' DifferentiableAt.congr_of_eventuallyEq _ _;
    exact fun p => -p ^ 3 + 3 * p;
    · norm_num [ mul_comm ];
    · filter_upwards [ Ioo_mem_nhds hp₀_half ( show p₀ < 1 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ] with p hp using v_two p ( by linarith [ hp.1 ] ) ( by linarith [ hp.2 ] ) ▸ by ring;
  · -- Since $s_n(p₀, k) < 0$, we can use the recurrence relation for $s_n$ in the case where $s_n(p, k) < 0$.
    have h_recurrence : ∀ᶠ p in nhds p₀, s_n p (k + 1) = s_n p k * (1 - alpha p (k + 1)) + p ^ (k + 1) * (1 - p) - (1 - p) ^ (k + 1) := by
      have h_recurrence : ∀ᶠ p in nhds p₀, s_n p k < 0 := by
        have h_recurrence : s_n p₀ k < 0 := by
          apply s_n_strict_neg_at_zero p₀ hp₀_s hp₀_half hp₀_phi k ih;
        exact ( ‹2 ≤ k → DifferentiableAt ℝ ( fun p => s_n p k ) p₀› ih |> DifferentiableAt.continuousAt |> ContinuousAt.preimage_mem_nhds <| Iio_mem_nhds h_recurrence );
      filter_upwards [ h_recurrence, Ioo_mem_nhds hp₀_half ( show p₀ < 1 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ] with p hp₁ hp₂ using by simpa using s_n_recurrence_stratB p ( k + 1 ) ( by linarith ) ( by linarith [ hp₂.1 ] ) ( by linarith [ hp₂.2 ] ) hp₁;
    refine' DifferentiableAt.congr_of_eventuallyEq _ h_recurrence;
    apply_rules [ DifferentiableAt.sub, DifferentiableAt.add, DifferentiableAt.mul, DifferentiableAt.pow, differentiableAt_id, differentiableAt_const ]

/-
Each s_n(·, k) has a derivative at p₀ bounded between C_prod(k) and 17.
-/
lemma s_n_deriv_exists_bounded (p₀ : ℝ) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2) (hp₀_s : s p₀ = 0)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ d : ℝ, HasDerivAt (fun p => s_n p k) d p₀ ∧
    C_prod k ≤ d ∧ d ≤ 17 := by
  -- From s_n_differentiableAt_p0, s_n(·, k) is differentiable at p₀.
  obtain ⟨d, hd⟩ : ∃ d, HasDerivAt (fun p : ℝ => s_n p k) d p₀ := by
    exact ⟨ _, DifferentiableAt.hasDerivAt ( s_n_differentiableAt_p0 p₀ hp₀_half hp₀_phi hp₀_s k hk ) ⟩;
  have h_lower_bound : ∀ᶠ p in nhdsWithin p₀ (Set.Ioi p₀), (s_n p k - s_n p₀ k) / (p - p₀) ≥ C_prod k := by
    have h_lower_bound : ∀ᶠ p in nhdsWithin p₀ (Set.Ioi p₀), ∀ m, 2 ≤ m → m ≤ k → s_n p (m - 1) ≤ 0 := by
      have h_lower_bound : ∀ᶠ p in nhdsWithin p₀ (Set.Ioi p₀), ∀ m, 2 ≤ m → m ≤ k → s_n p m < 0 := by
        have := crossing_time_large p₀ hp₀_s hp₀_half hp₀_phi k hk
        obtain ⟨ δ, hδ_pos, hδ ⟩ := this; filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, lt_add_of_pos_right p₀ hδ_pos ⟩ ] with p hp using fun m hm₁ hm₂ => hδ p hp.1 hp.2 m hm₁ hm₂;
      filter_upwards [ h_lower_bound, self_mem_nhdsWithin ] with p hp hp' m hm₁ hm₂;
      rcases m with ( _ | _ | m ) <;> simp_all +decide;
      by_cases hm : 2 ≤ m + 1;
      · linarith [ hp ( m + 1 ) hm ( by linarith ) ];
      · interval_cases _ : m + 1 <;> simp_all +decide [ s_n ];
        rw [ v_one ];
    have h_lower_bound : ∀ᶠ p in nhdsWithin p₀ (Set.Ioi p₀), s_n p k > s_n p₀ k + C_prod k * (p - p₀) := by
      have h_lower_bound : ∀ᶠ p in nhdsWithin p₀ (Set.Ioi p₀), p > p₀ ∧ p < (Real.sqrt 5 - 1) / 2 := by
        exact mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨ ( Real.sqrt 5 - 1 ) / 2, by norm_num; linarith, fun x hx => ⟨ hx.1, hx.2 ⟩ ⟩;
      filter_upwards [ h_lower_bound, ‹∀ᶠ p in nhdsWithin p₀ ( Set.Ioi p₀ ), ∀ m : ℕ, 2 ≤ m → m ≤ k → s_n p ( m - 1 ) ≤ 0› ] with p hp₁ hp₂ using by have := dipvsdiq p₀ p k ( by linarith ) hp₁.1 hp₁.2 ( by linarith ) ( by aesop ) ; linarith;
    filter_upwards [ h_lower_bound, self_mem_nhdsWithin ] with p hp hp' using by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;> linarith [ hp'.out ] ;
  have h_upper_bound : ∀ᶠ p in nhdsWithin p₀ (Set.Ioi p₀), (s_n p k - s_n p₀ k) / (p - p₀) < 17 := by
    have h_upper_bound : ∀ᶠ p in nhdsWithin p₀ (Set.Ioi p₀), s_n p k < s_n p₀ k + 17 * (p - p₀) := by
      have := @dipvsdiq_upper p₀;
      exact Filter.mem_of_superset ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, hp₀_phi ⟩ ) fun p hp => this p k ( by linarith ) hp.1 hp.2 hk;
    filter_upwards [ h_upper_bound, self_mem_nhdsWithin ] with p hp hp' using by rw [ div_lt_iff₀ ] <;> linarith [ Set.mem_Ioi.mp hp' ] ;
  have h_slope_limit : Filter.Tendsto (fun p => (s_n p k - s_n p₀ k) / (p - p₀)) (nhdsWithin p₀ (Set.Ioi p₀)) (nhds d) := by
    rw [ hasDerivAt_iff_tendsto_slope ] at hd;
    convert hd.mono_left <| nhdsWithin_mono _ _ using 2 <;> norm_num [ div_eq_inv_mul, slope_def_field ];
  exact ⟨ d, hd, le_of_tendsto_of_tendsto tendsto_const_nhds h_slope_limit h_lower_bound, le_of_tendsto_of_tendsto h_slope_limit tendsto_const_nhds ( Filter.eventually_of_mem h_upper_bound fun x hx => le_of_lt hx ) ⟩

noncomputable def s_n_deriv (p₀ : ℝ) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2) (hp₀_s : s p₀ = 0)
    (n : ℕ) : ℝ :=
  if h : 2 ≤ n then (s_n_deriv_exists_bounded p₀ hp₀_half hp₀_phi hp₀_s n h).choose
  else 0

lemma s_n_deriv_spec (p₀ : ℝ) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2) (hp₀_s : s p₀ = 0)
    (n : ℕ) (hn : 2 ≤ n) :
    HasDerivAt (fun p => s_n p n) (s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s n) p₀ ∧
    C_prod n ≤ s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s n ∧
    s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s n ≤ 17 := by
  unfold s_n_deriv; simp [hn]
  exact (s_n_deriv_exists_bounded p₀ hp₀_half hp₀_phi hp₀_s n hn).choose_spec

/-
The slope of s_n approximates its derivative.
-/
lemma s_n_slope_approx (p₀ : ℝ) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2) (hp₀_s : s p₀ = 0)
    (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p, 0 < |p - p₀| → |p - p₀| < δ →
    |(s_n p n - s_n p₀ n) / (p - p₀) -
      s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s n| < ε := by
  have := s_n_deriv_spec p₀ hp₀_half hp₀_phi hp₀_s n hn;
  rw [ hasDerivAt_iff_tendsto_slope ] at this;
  rcases Metric.tendsto_nhdsWithin_nhds.mp this.1 ε hε with ⟨ δ, hδ₁, hδ₂ ⟩ ; use δ; simp_all +decide [ div_eq_inv_mul, slope_def_field ];
  exact fun p hp₁ hp₂ => hδ₂ ( sub_ne_zero.mp hp₁ ) hp₂

/-
The slope of s is close to the slope of s_n, uniformly.
-/
lemma s_slope_close_to_s_n (p₀ r : ℝ) (hp₀_half : 1/2 < p₀) (_hp₀_r : p₀ ≤ r)
    (_hr_pos : 1/2 < r) (_hr_lt : r < 1) (C : ℝ) (_hC : 0 < C)
    (hTail : ∀ n : ℕ, 2 ≤ n → ∀ p q : ℝ, 1/2 ≤ p → p ≤ r → 1/2 ≤ q → q ≤ r →
      |s p - s_n p n - (s q - s_n q n)| ≤ C * (↑n + 1) ^ 2 * r ^ n * |p - q|)
    (_hp₀_s : s p₀ = 0)
    (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp₁ : p₀ < p) (hp₂ : p ≤ r) :
    |(s p - s p₀) / (p - p₀) - (s_n p n - s_n p₀ n) / (p - p₀)| ≤
    C * (↑n + 1) ^ 2 * r ^ n := by
  rw [ div_sub_div_same, abs_div ];
  rw [ div_le_iff₀ ( abs_pos.mpr ( sub_ne_zero.mpr hp₁.ne' ) ) ];
  convert hTail n hn p p₀ ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) using 1 ; ring_nf

/-
The derivative sequence d_n is Cauchy (using the tail estimate).
-/
lemma deriv_seq_cauchy (p₀ r : ℝ) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2) (hp₀_s : s p₀ = 0)
    (hp₀_r : p₀ < r) (hr_lt : r < 1)
    (C : ℝ) (hC : 0 < C)
    (hTail : ∀ n : ℕ, 2 ≤ n → ∀ p q : ℝ, 1/2 ≤ p → p ≤ r → 1/2 ≤ q → q ≤ r →
      |s p - s_n p n - (s q - s_n q n)| ≤ C * (↑n + 1) ^ 2 * r ^ n * |p - q|) :
    CauchySeq (fun n => s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (n + 2)) := by
  have h_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → n < m → |s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (n + 2) - s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (m + 2)| < ε := by
    -- By the properties of the derivative sequence and the tail estimate, we can bound the difference between $d_n$ and $d_m$.
    intros ε hε_pos
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, C * (n + 3) ^ 2 * r ^ (n + 2) < ε / 4 := by
      -- Apply the fact that $(n + 1)^2 * r^n$ tends to $0$ as $n$ tends to infinity.
      have h_lim : Filter.Tendsto (fun n : ℕ => C * (n + 3) ^ 2 * r ^ (n + 2)) Filter.atTop (nhds 0) := by
        have h_lim : Filter.Tendsto (fun n : ℕ => (n + 3) ^ 2 * r ^ (n + 2)) Filter.atTop (nhds 0) := by
          convert sq_mul_pow_tendsto_zero r ( show 0 < r by linarith ) ( show r < 1 by linarith ) |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 2 using 2 ; norm_num ; ring_nf;
          norm_num;
        simpa [ mul_assoc ] using h_lim.const_mul C;
      simpa using h_lim.eventually ( gt_mem_nhds <| by positivity );
    -- By the properties of the derivative sequence and the tail estimate, we can bound the difference between $d_n$ and $d_m$ for $n \geq N$.
    use N + 2;
    intros n m hn hm
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ p, 0 < |p - p₀| → |p - p₀| < δ → |(s_n p (n + 2) - s_n p₀ (n + 2)) / (p - p₀) - s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (n + 2)| < ε / 4 ∧ |(s_n p (m + 2) - s_n p₀ (m + 2)) / (p - p₀) - s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (m + 2)| < ε / 4 := by
      obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ p, 0 < |p - p₀| → |p - p₀| < δ₁ → |(s_n p (n + 2) - s_n p₀ (n + 2)) / (p - p₀) - s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (n + 2)| < ε / 4 := by
        exact s_n_slope_approx p₀ hp₀_half hp₀_phi hp₀_s ( n + 2 ) ( by linarith ) ( ε / 4 ) ( by linarith );
      obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ p, 0 < |p - p₀| → |p - p₀| < δ₂ → |(s_n p (m + 2) - s_n p₀ (m + 2)) / (p - p₀) - s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (m + 2)| < ε / 4 := by
        exact s_n_slope_approx p₀ hp₀_half hp₀_phi hp₀_s ( m + 2 ) ( by linarith ) ( ε / 4 ) ( by linarith );
      exact ⟨ Min.min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun p hp₁ hp₂ => ⟨ hδ₁ p hp₁ ( lt_of_lt_of_le hp₂ ( min_le_left _ _ ) ), hδ₂ p hp₁ ( lt_of_lt_of_le hp₂ ( min_le_right _ _ ) ) ⟩ ⟩;
    -- Choose $p$ such that $p₀ < p < \min(r, p₀ + δ)$.
    obtain ⟨p, hp₁, hp₂⟩ : ∃ p, p₀ < p ∧ p < min r (p₀ + δ) := by
      exact exists_between ( lt_min hp₀_r ( lt_add_of_pos_right _ hδ_pos ) );
    have h_bound : |(s p - s p₀) / (p - p₀) - (s_n p (n + 2) - s_n p₀ (n + 2)) / (p - p₀)| ≤ C * (n + 3) ^ 2 * r ^ (n + 2) ∧ |(s p - s p₀) / (p - p₀) - (s_n p (m + 2) - s_n p₀ (m + 2)) / (p - p₀)| ≤ C * (m + 3) ^ 2 * r ^ (m + 2) := by
      apply And.intro;
      · have := s_slope_close_to_s_n p₀ r hp₀_half ( by linarith ) ( by linarith ) ( by linarith ) C hC hTail hp₀_s ( n + 2 ) ( by linarith ) p hp₁ ( by linarith [ min_le_left r ( p₀ + δ ), min_le_right r ( p₀ + δ ) ] );
        exact this.trans_eq ( by push_cast; ring );
      · have := s_slope_close_to_s_n p₀ r hp₀_half ( by linarith ) ( by linarith ) ( by linarith ) C hC hTail hp₀_s ( m + 2 ) ( by linarith ) p ( by linarith ) ( by linarith [ min_le_left r ( p₀ + δ ), min_le_right r ( p₀ + δ ) ] ) ; simp_all +decide [ abs_div, div_sub_div_same ] ;
        exact this.trans_eq ( by ring );
    grind +splitImp;
  refine' Metric.cauchySeq_iff'.mpr _;
  exact fun ε hε => by obtain ⟨ N, hN ⟩ := h_cauchy ε hε; exact ⟨ N, fun n hn => if h : n = N then by simpa [ h ] else by simpa [ dist_comm, abs_sub_comm ] using hN N n le_rfl ( lt_of_le_of_ne hn ( Ne.symm h ) ) ⟩ ;

theorem prop4_proof (p₀ : ℝ) (hp₀_s : s p₀ = 0) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2) :
    ∃ L > 0, Tendsto (fun p => (s p - s p₀) / (p - p₀))
      (nhdsWithin p₀ (Set.Ioi p₀)) (nhds L) := by
  -- Choose r = (p₀ + (Real.sqrt 5 - 1) / 2) / 2.
  set r : ℝ := (p₀ + (Real.sqrt 5 - 1) / 2) / 2;
  -- Choose C, hC_pos, hTail from tail_lipschitz_estimate r.
  obtain ⟨C, hC_pos, hTail⟩ : ∃ C > 0, ∀ n : ℕ, 2 ≤ n → ∀ p q : ℝ, 1/2 ≤ p → p ≤ r → 1/2 ≤ q → q ≤ r →
    |s p - s_n p n - (s q - s_n q n)| ≤ C * (↑n + 1) ^ 2 * r ^ n * |p - q| := by
      apply tail_lipschitz_estimate r ?_ ?_ <;> norm_num at *;
      · exact lt_div_iff₀' ( by norm_num ) |>.2 ( by linarith );
      · exact div_lt_iff₀' ( by norm_num ) |>.2 ( by linarith );
  -- Choose L from the Cauchy sequence d_n.
  obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto (fun n => s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (n + 2)) Filter.atTop (nhds L) := by
    have h_cauchy : CauchySeq (fun n => s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (n + 2)) := by
      apply deriv_seq_cauchy p₀ r hp₀_half hp₀_phi hp₀_s (by
      exact lt_div_iff₀' ( by positivity ) |>.2 ( by linarith )) (by
      simp +zetaDelta at *;
      nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]) C hC_pos hTail;
    exact cauchySeq_tendsto_of_complete h_cauchy;
  -- Show that L > 0.
  have hL_pos : 0 < L := by
    have hL_pos : ∀ n : ℕ, C_prod (n + 2) ≤ s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (n + 2) := by
      exact fun n => s_n_deriv_spec p₀ hp₀_half hp₀_phi hp₀_s ( n + 2 ) ( by linarith ) |>.2.1;
    have hL_pos : ∃ C₀ > 0, ∀ n : ℕ, C₀ ≤ C_prod (n + 2) := by
      exact ⟨ _, C_prod_uniform_lower.choose_spec.1, fun n => C_prod_uniform_lower.choose_spec.2 _ le_add_self ⟩;
    exact lt_of_lt_of_le hL_pos.choose_spec.1 ( le_of_tendsto_of_tendsto' tendsto_const_nhds hL fun n => le_trans ( hL_pos.choose_spec.2 n ) ( by solve_by_elim ) );
  -- Show that the limit of the slope of s as p approaches p₀ from the right is L.
  have h_slope_limit : ∀ ε > 0, ∃ δ > 0, ∀ p, p₀ < p → p < p₀ + δ → |(s p - s p₀) / (p - p₀) - L| < ε := by
    intro ε hε_pos
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, |s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (n + 2) - L| < ε / 3 ∧ C * (n + 3) ^ 2 * r ^ (n + 2) < ε / 3 := by
      have h_lim_zero : Filter.Tendsto (fun n : ℕ => C * (n + 3) ^ 2 * r ^ (n + 2)) Filter.atTop (nhds 0) := by
        have h_lim_zero : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ 2 * r ^ n) Filter.atTop (nhds 0) := by
          convert sq_mul_pow_tendsto_zero r _ _ using 1;
          · exact div_pos ( add_pos ( by linarith ) ( by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ) zero_lt_two;
          · exact div_lt_one ( by positivity ) |>.2 ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] );
        convert h_lim_zero.const_mul C |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 2 using 2 <;> norm_num ; ring;
      exact Filter.eventually_atTop.mp ( hL.eventually ( Metric.ball_mem_nhds _ ( by positivity ) ) |> Filter.Eventually.and <| h_lim_zero.eventually ( gt_mem_nhds <| by positivity ) );
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ p, 0 < |p - p₀| → |p - p₀| < δ → |(s_n p (N + 2) - s_n p₀ (N + 2)) / (p - p₀) - s_n_deriv p₀ hp₀_half hp₀_phi hp₀_s (N + 2)| < ε / 3 := by
      exact s_n_slope_approx p₀ hp₀_half hp₀_phi hp₀_s ( N + 2 ) ( by linarith ) ( ε / 3 ) ( by linarith );
    use Min.min δ (r - p₀);
    refine' ⟨ lt_min hδ_pos ( sub_pos.mpr <| by rw [ show r = ( p₀ + ( Real.sqrt 5 - 1 ) / 2 ) / 2 by rfl ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ), fun p hp₁ hp₂ => _ ⟩;
    have := s_slope_close_to_s_n p₀ r hp₀_half ( by rw [ show r = ( p₀ + ( Real.sqrt 5 - 1 ) / 2 ) / 2 by rfl ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( by rw [ show r = ( p₀ + ( Real.sqrt 5 - 1 ) / 2 ) / 2 by rfl ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ( by rw [ show r = ( p₀ + ( Real.sqrt 5 - 1 ) / 2 ) / 2 by rfl ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) C hC_pos hTail hp₀_s ( N + 2 ) ( by linarith ) p hp₁ ( by linarith [ min_le_left δ ( r - p₀ ), min_le_right δ ( r - p₀ ) ] );
    grind;
  use L, hL_pos;
  rw [ Metric.tendsto_nhdsWithin_nhds ];
  exact fun ε hε => by obtain ⟨ δ, hδ_pos, hδ ⟩ := h_slope_limit ε hε; exact ⟨ δ, hδ_pos, fun x hx₁ hx₂ => hδ x hx₁ ( by linarith [ abs_lt.mp hx₂ ] ) ⟩ ;

/-- The right derivative of s at p₀ exists and is positive. -/
theorem prop4 (p₀ : ℝ) (hp₀_s : s p₀ = 0) (hp₀_half : 1/2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2) :
    ∃ L > 0, Filter.Tendsto (fun p => (s p - s p₀) / (p - p₀))
      (nhdsWithin p₀ (Set.Ioi p₀)) (nhds L) :=
  prop4_proof p₀ hp₀_s hp₀_half hp₀_phi

/-! ## Optimal Strategy Definitions and Theorems -/

/-- Local payoff after seeing `h` heads among `n` coins and choosing to leave `r` coins. -/
noncomputable def localPayoff (p : ℝ) (n h r : ℕ) : ℝ :=
  (bestHeadsAside n h r : ℝ) + v p r

/-- `r` is an optimal remaining-coin count after seeing `h` heads among `n` coins. -/
def IsOptimalRem (p : ℝ) (n h r : ℕ) : Prop :=
  r < n ∧ ∀ r' : ℕ, r' < n → localPayoff p n h r' ≤ localPayoff p n h r

/--
Strategy A as a remaining-coin count:
leave no coins if all coins are heads, otherwise leave `n - 1` coins.
-/
def remA (n h : ℕ) : ℕ :=
  if h = n then 0 else n - 1

/--
Strategy B as a remaining-coin count:
leave no coins if all coins are heads;
leave one coin if exactly one coin is a tail;
otherwise leave `n - 1` coins.
-/
def remB (n h : ℕ) : ℕ :=
  if h = n then 0 else if h = n - 1 then 1 else n - 1

lemma remA_lt (n h : ℕ) (hn : 0 < n) : remA n h < n := by
  unfold remA
  split_ifs <;> omega

lemma remB_lt (n h : ℕ) (hn : 2 ≤ n) : remB n h < n := by
  unfold remB
  split_ifs <;> omega

/-- Every term in the finite set is bounded above by the finite supremum. -/
lemma IsOptimalRem.of_sup_eq
    (p : ℝ) {n h r : ℕ} (hr : r < n)
    (hsup :
      (Finset.univ : Finset (Fin n)).sup'
        ⟨⟨r, hr⟩, Finset.mem_univ _⟩
        (fun ρ : Fin n => localPayoff p n h ρ.val)
        =
      localPayoff p n h r) :
    IsOptimalRem p n h r := by
  constructor
  · exact hr
  · intro r' hr'
    have hle : localPayoff p n h r' ≤
          (Finset.univ : Finset (Fin n)).sup'
            ⟨⟨r, hr⟩, Finset.mem_univ _⟩
            (fun ρ : Fin n => localPayoff p n h ρ.val) :=
      Finset.le_sup' (fun ρ : Fin n => localPayoff p n h ρ.val)
        (Finset.mem_univ (⟨r', hr'⟩ : Fin n))
    rw [hsup] at hle
    exact hle

/-- The bellman sup over Fin (n+1) in terms of localPayoff equals the sup over Fin (n+1). -/
lemma bellman_sup_eq_localPayoff_sup (p : ℝ) (n h : ℕ) :
    (Finset.univ : Finset (Fin (n + 1))).sup'
      ⟨0, Finset.mem_univ _⟩
      (fun r => (bestHeadsAside (n + 1) h r : ℝ) + v p r)
    =
    (Finset.univ : Finset (Fin (n + 1))).sup'
      ⟨0, Finset.mem_univ _⟩
      (fun r => localPayoff p (n + 1) h r.val) := by
  simp only [localPayoff]

/-
Optimality of `remA` for all observable head counts.
Strategy A: leave `n-1` coins unless all heads, then leave 0.
-/
theorem remA_optimal
    (p : ℝ) (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (n : ℕ) (hn : 3 ≤ n)
    (hs : 0 ≤ s_n p (n - 1))
    (h : ℕ) (hh : h ≤ n) :
    IsOptimalRem p n h (remA n h) := by
      -- Let's obtain m such that n = m + 1.
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        exact Nat.exists_eq_succ_of_ne_zero ( by linarith );
      by_cases h_cases : h = m + 1 ∨ h = 0 ∨ 1 ≤ h ∧ h ≤ m - 1 ∨ h = m;
      · rcases h_cases with ( rfl | rfl | ⟨ h₁, h₂ ⟩ | rfl ) <;> simp_all +decide;
        · constructor <;> norm_num [ remA ];
          unfold localPayoff bestHeadsAside; norm_num;
          -- By definition of $v$, we know that $v p r' \leq r'$ for all $r' \leq m$.
          have hv_le_r : ∀ r' ≤ m, v p r' ≤ r' := by
            intro r' _; exact le_trans (v_le_n r' p (by linarith) (by linarith)) (by exact_mod_cast Nat.le_of_lt_succ (by omega));
          intro r' hr'; specialize hv_le_r r' hr'; rw [ Nat.cast_sub ( by linarith ) ] ; push_cast; linarith;
        · convert IsOptimalRem.of_sup_eq p ( show m < m + 1 from Nat.lt_succ_self m ) _ using 1;
          convert bellman_sup_h_zero p ( by positivity ) ( by linarith ) m ( by linarith ) using 1;
          unfold localPayoff bestHeadsAside; aesop;
        · have := bellman_sup_mid_weak p m ( by linarith ) ( by norm_num at *; linarith ) ( by linarith ) ( fun k hk₁ hk₂ => delta_nonneg_of_prop1 p ( by norm_num at *; linarith ) ( by linarith ) k hk₁ ) h h₁ ( by omega );
          convert IsOptimalRem.of_sup_eq p _ _ using 1;
          all_goals norm_num [ remA ];
          lia;
          convert this using 1;
          unfold localPayoff bestHeadsAside; split_ifs <;> norm_num ; omega;
          linarith;
        · refine' IsOptimalRem.of_sup_eq _ _ _;
          all_goals norm_num [ remA ];
          have := bellman_sup_second_last p h ( by linarith ) ( by linarith ) ( fun k hk₁ hk₂ => delta_nonneg_of_prop1 p ( by linarith ) ( by linarith ) k hk₁ );
          convert this using 1;
          unfold localPayoff bestHeadsAside; norm_num;
          rw [ min_eq_right ( by norm_cast; linarith ) ] ; rw [ max_eq_left ] ; linarith [ show ( h : ℝ ) ≥ 2 by norm_cast, show ( s_n p h : ℝ ) = v p h - h + 1 - p by rfl ] ;
      · omega

/-
Optimality of `remB` for all observable head counts.
Strategy B: leave `n-1` coins unless all heads (leave 0) or one tail (leave 1).
-/
set_option maxHeartbeats 16000000 in
theorem remB_optimal
    (p : ℝ) (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (n : ℕ) (hn : 3 ≤ n)
    (hs : s_n p (n - 1) ≤ 0)
    (h : ℕ) (hh : h ≤ n) :
    IsOptimalRem p n h (remB n h) := by
      rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ remB ] at *;
      rcases h with ( _ | _ | h ) <;> simp_all +arith +decide [ IsOptimalRem ];
      · unfold localPayoff bestHeadsAside; norm_num;
        intro r' hr'
        have h_v_mono : ∀ m n : ℕ, m ≤ n → v p m ≤ v p n := by
          intros m n hmn
          induction' hmn with n hn ih;
          · rfl;
          · refine le_trans ih ?_;
            -- By definition of $v$, we know that $v p (n + 1) \geq v p n$.
            have h_v_mono : ∀ n : ℕ, v p (n + 1) ≥ v p n := by
              intro n; exact v_mono_n p (by linarith) (by linarith) n;
            exact h_v_mono n;
        exact h_v_mono _ _ hr';
      · intro r' hr'
        simp [localPayoff, bestHeadsAside];
        -- Since $v p$ is non-decreasing, we have $v p r' \leq v p (n + 2)$.
        have h_v_mono : v p r' ≤ v p (n + 2) := by
          exact monotone_nat_of_le_succ (fun n => v_mono_n p (by linarith) (by linarith) n) hr';
        exact add_le_add ( min_le_left _ _ ) h_v_mono;
      · split_ifs <;> simp_all +arith +decide [ localPayoff ];
        · unfold bestHeadsAside; simp +arith +decide;
          intro r' hr'
          have h_v_le : v p r' ≤ r' := by
            -- By definition of $v$, we know that $v p r' \leq r'$ for any $r'$.
            apply v_le_n;
            · positivity;
            · linarith;
          rw [ Nat.cast_sub ] <;> push_cast <;> linarith;
        · intro r' hr'
          have h_sup : (Finset.univ : Finset (Fin (n + 3))).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside (n + 3) (n + 2) r : ℝ) + v p r) = ↑(n + 2) + p := by
            have h_sup : (Finset.univ : Finset (Fin (n + 3))).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside (n + 3) (n + 2) r : ℝ) + v p r) = max (1 + v p (n + 2)) (↑(n + 2) + p) := by
              apply bellman_sup_second_last;
              · linarith;
              · exact le_trans ( by norm_num ) hp;
              · exact fun k hk₁ hk₂ => delta_nonneg_of_prop1 p ( by norm_num at *; linarith ) ( by linarith ) k hk₁;
            rw [ h_sup, max_eq_right ];
            unfold s_n at hs; norm_num at *; linarith;
          have h_sup : ∀ r : Fin (n + 3), (bestHeadsAside (n + 3) (n + 2) r : ℝ) + v p r ≤ ↑(n + 2) + p := by
            exact fun r => h_sup ▸ Finset.le_sup' ( fun r : Fin ( n + 3 ) => ( bestHeadsAside ( n + 3 ) ( n + 2 ) r : ℝ ) + v p r ) ( Finset.mem_univ r );
          convert h_sup ⟨ r', by linarith ⟩ using 1;
          unfold bestHeadsAside; norm_num [ v_one ] ;
        · intro r' hr'
          have h_sup : (Finset.univ : Finset (Fin (n + 3))).sup' ⟨0, Finset.mem_univ _⟩ (fun r => (bestHeadsAside (n + 3) (h + 2) r.val : ℝ) + v p r.val) = 1 + v p (n + 2) := by
            apply bellman_sup_mid_weak;
            all_goals norm_num at * ; try linarith;
            · exact fun k hk₁ hk₂ => delta_nonneg_of_prop1 p hp hp₁ k hk₁;
            · omega;
          have h_sup : (bestHeadsAside (n + 3) (h + 2) r' : ℝ) + v p r' ≤ 1 + v p (n + 2) := by
            exact h_sup ▸ Finset.le_sup' ( fun r : Fin ( n + 3 ) => ( bestHeadsAside ( n + 3 ) ( h + 2 ) r.val : ℝ ) + v p r.val ) ( Finset.mem_univ ⟨ r', by linarith ⟩ );
          unfold bestHeadsAside at * ; simp_all +arith +decide

/-- Local optimality: one of strategy A or strategy B is optimal for every state. -/
theorem local_main_theorem
    (p : ℝ) (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (n : ℕ) (hn : 3 ≤ n) :
    v p (n - 1) + 1 ≤ v p n ∧
    (
      (∀ h : ℕ, h ≤ n → IsOptimalRem p n h (remA n h)) ∨
      (∀ h : ℕ, h ≤ n → IsOptimalRem p n h (remB n h))
    ) := by
  constructor
  · exact v_sub_v_sub_one_ge_one_of_half_le p n hn hp hp₁
  · rcases le_total 0 (s_n p (n - 1)) with hs | hs
    · left
      intro h hh
      exact remA_optimal p hp hp₁ n hn hs h hh
    · right
      intro h hh
      exact remB_optimal p hp hp₁ n hn hs h hh

/-! ### Regime-specific optimality theorems -/

theorem regime1_strategyA
    (p : ℝ) (hp : (Real.sqrt 5 - 1) / 2 ≤ p) (hp₁ : p < 1)
    (n : ℕ) (hn : 3 ≤ n)
    (h : ℕ) (hh : h ≤ n) :
    IsOptimalRem p n h (remA n h) := by
  have hs : 0 ≤ s_n p (n - 1) :=
    s_n_nonneg_of_phi_le p hp hp₁ (n - 1) (by omega)
  exact remA_optimal p (by linarith [half_lt_phi']) hp₁ n hn hs h hh

theorem regime3_strategyB
    (p : ℝ) (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (hs : s p ≤ 0)
    (n : ℕ) (hn : 3 ≤ n)
    (h : ℕ) (hh : h ≤ n) :
    IsOptimalRem p n h (remB n h) := by
  have hs_n : s_n p (n - 1) ≤ 0 :=
    regime3 p hp hp₁ hs (n - 1) (by omega)
  exact remB_optimal p hp hp₁ n hn hs_n h hh

theorem regime_le_p₀_strategyB
    (p₀ : ℝ)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2)
    (hp₀_s : s p₀ = 0)
    (hneg : ∀ p, 1 / 2 ≤ p → p < p₀ → s p < 0)
    (p : ℝ) (hp : 1 / 2 ≤ p) (hpp₀ : p ≤ p₀)
    (n : ℕ) (hn : 3 ≤ n)
    (h : ℕ) (hh : h ≤ n) :
    IsOptimalRem p n h (remB n h) := by
  have hp₁ : p < 1 := by
    linarith [hpp₀, hp₀_phi, phi_lt_one']
  have hs : s p ≤ 0 := by
    rcases lt_or_eq_of_le hpp₀ with hp_lt | hp_eq
    · exact le_of_lt (hneg p hp hp_lt)
    · simp [hp_eq, hp₀_s]
  exact regime3_strategyB p hp hp₁ hs n hn h hh

theorem regime2_strategy_switch
    (p : ℝ) (hp : 1 / 2 ≤ p) (hp₁ : p < 1)
    (hphi : p < (Real.sqrt 5 - 1) / 2)
    (hs_pos : 0 < s p) :
    ∃ K : ℕ,
      3 ≤ K ∧
      (∀ n : ℕ, 3 ≤ n → n ≤ K →
        ∀ h : ℕ, h ≤ n → IsOptimalRem p n h (remB n h)) ∧
      (∀ n : ℕ, K < n →
        ∀ h : ℕ, h ≤ n → IsOptimalRem p n h (remA n h)) := by
  obtain ⟨K, hK, hneg, hnonneg⟩ :=
    regime2 p hp hp₁ hphi hs_pos
  refine ⟨K, hK, ?_, ?_⟩
  · intro n hn hnK h hh
    have hs : s_n p (n - 1) ≤ 0 := by
      have hlt : n - 1 < K := by omega
      exact le_of_lt (hneg (n - 1) (by omega) hlt)
    exact remB_optimal p hp hp₁ n hn hs h hh
  · intro n hKn h hh
    have hn : 3 ≤ n := by omega
    have hs : 0 ≤ s_n p (n - 1) := by
      exact hnonneg (n - 1) (by omega)
    exact remA_optimal p hp hp₁ n hn hs h hh

/-! ### Switch-index asymptotics -/

noncomputable def switchCenter (p₀ L p : ℝ) : ℝ :=
  (Real.log (p - p₀) + Real.log L) / Real.log p₀

def SwitchAsymptoticBounds (p₀ L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ p : ℝ,
    p₀ < p → p < p₀ + δ →
    ∀ hex : ∃ K : ℕ, 3 ≤ K ∧ 0 ≤ s_n p K,
      let K := Nat.find hex
      switchCenter p₀ L p - 1 - ε < (K : ℝ) ∧
      (K : ℝ) < switchCenter p₀ L p + ε

/-
From the derivative limit, extract slope bounds on s(p) near p₀.
-/
lemma slope_bounds_from_deriv
    (p₀ L : ℝ)
    (hp₀_s : s p₀ = 0)
    (hL : Filter.Tendsto (fun p => (s p - s p₀) / (p - p₀))
        (nhdsWithin p₀ (Set.Ioi p₀)) (nhds L))
    (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ δ > 0, ∀ p, p₀ < p → p < p₀ + δ →
      (L - ε₁) * (p - p₀) < s p ∧ s p < (L + ε₁) * (p - p₀) := by
        have := Metric.tendsto_nhdsWithin_nhds.mp hL ε₁ hε₁;
        obtain ⟨ δ, hδ_pos, H ⟩ := this; exact ⟨ δ, hδ_pos, fun p hp₁ hp₂ => ⟨ by have := abs_lt.mp ( H hp₁ ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ) ; rw [ div_eq_inv_mul ] at this; nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( p - p₀ ) ≠ 0 ) ( s p ), inv_mul_cancel₀ ( by linarith : ( p - p₀ ) ≠ 0 ) ], by have := abs_lt.mp ( H hp₁ ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ) ; rw [ div_eq_inv_mul ] at this; nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( p - p₀ ) ≠ 0 ) ( s p ), inv_mul_cancel₀ ( by linarith : ( p - p₀ ) ≠ 0 ) ] ⟩ ⟩ ;

/-
Key log ratio bound: from a < b * p^K and p^K > 0, derive K < log(a/b) / log(p) when log(p) < 0.
-/
lemma K_upper_from_exp_ineq (p a b : ℝ) (K : ℕ)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (h : a < b * p ^ K) :
    (K : ℝ) < Real.log (a / b) / Real.log p := by
      rw [ lt_div_iff_of_neg ( Real.log_neg hp_pos hp_lt_one ) ];
      simpa [ Real.log_pow, Real.log_div, ha_pos.ne', hb_pos.ne' ] using Real.log_lt_log ( div_pos ha_pos hb_pos ) ( show a / b < p ^ K by rwa [ div_lt_iff₀' hb_pos ] )

/-
Key log ratio bound: from b * p^(K+1) < a, derive (log(a/b) / log(p)) - 1 < K when log(p) < 0.
-/
lemma K_lower_from_exp_ineq (p a b : ℝ) (K : ℕ)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (_ha_pos : 0 < a) (hb_pos : 0 < b)
    (h : b * p ^ (K + 1) < a) :
    Real.log (a / b) / Real.log p - 1 < (K : ℝ) := by
      -- From $b * p^{K+1} < a$, we get $p^{K+1} < a/b$.
      have h_exp : p ^ (K + 1) < a / b := by
        rwa [ lt_div_iff₀' hb_pos ];
      -- From $p^{K+1} < a/b$, we get $(K+1) * \log p < \log (a/b)$.
      have h_log : (K + 1) * Real.log p < Real.log (a / b) := by
        simpa using Real.log_lt_log ( by positivity ) h_exp;
      rw [ div_sub_one, div_lt_iff_of_neg ] <;> nlinarith [ Real.log_le_sub_one_of_pos hp_pos ]

/-
As p → p₀⁺, (log(δ) + C) / log(p) converges to (log(δ) + C) / log(p₀) where δ = p - p₀.
-/
lemma log_ratio_tendsto (p₀ C : ℝ) (hp₀_pos : 0 < p₀) (hp₀_lt_one : p₀ < 1) :
    Filter.Tendsto
      (fun p => (Real.log (p - p₀) + C) / Real.log p -
               (Real.log (p - p₀) + C) / Real.log p₀)
      (nhdsWithin p₀ (Set.Ioi p₀))
      (nhds 0) := by
        -- We can factor out $(\ln(p-p₀) + C)$ and use the fact that $(\log(p₀) - \log(p)) / (\log(p) \log(p₀))$ tends to $0$ as $p$ approaches $p₀$ from the right.
        have h_factor : Filter.Tendsto (fun p => (Real.log (p - p₀) + C) * (Real.log p₀ - Real.log p) / (Real.log p * Real.log p₀)) (nhdsWithin p₀ (Set.Ioi p₀)) (nhds 0) := by
          -- We'll use the fact that $x \ln x \to 0$ as $x \to 0^+$.
          have h_log_mul : Filter.Tendsto (fun x => x * Real.log x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.tendsto 0 );
          -- We'll use the fact that $Real.log p₀ - Real.log p$ is bounded.
          have h_log_diff_bounded : Filter.Tendsto (fun p => (Real.log p₀ - Real.log p) / (p - p₀)) (nhdsWithin p₀ (Set.Ioi p₀)) (nhds (-1 / p₀)) := by
            have h_log_diff_bounded : HasDerivAt (fun p => Real.log p) (1 / p₀) p₀ := by
              simpa using Real.hasDerivAt_log hp₀_pos.ne';
            rw [ hasDerivAt_iff_tendsto_slope ] at h_log_diff_bounded;
            convert h_log_diff_bounded.neg.mono_left <| nhdsWithin_mono _ _ using 2 <;> norm_num [ div_eq_inv_mul, slope_def_field ] ; ring;
          -- We'll use the fact that $(Real.log (p - p₀) + C) * (p - p₀)$ tends to $0$ as $p$ approaches $p₀$ from the right.
          have h_log_mul_zero : Filter.Tendsto (fun p => (Real.log (p - p₀) + C) * (p - p₀)) (nhdsWithin p₀ (Set.Ioi p₀)) (nhds 0) := by
            have h_log_mul_zero : Filter.Tendsto (fun p => (p - p₀) * Real.log (p - p₀)) (nhdsWithin p₀ (Set.Ioi p₀)) (nhds 0) := by
              exact h_log_mul.comp <| Filter.Tendsto.inf ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) <| Filter.tendsto_principal_principal.2 fun x hx => by aesop;
            convert h_log_mul_zero.add ( Continuous.continuousWithinAt ( show Continuous fun p : ℝ => C * ( p - p₀ ) by continuity ) ) using 2 <;> ring;
          have := h_log_mul_zero.mul h_log_diff_bounded;
          convert this.div ( ContinuousAt.continuousWithinAt ( show ContinuousAt ( fun p => Real.log p * Real.log p₀ ) p₀ from ContinuousAt.mul ( Real.continuousAt_log hp₀_pos.ne' ) continuousAt_const ) ) _ using 2 <;> norm_num;
          · grind +splitImp;
          · exact ⟨ hp₀_pos.ne', hp₀_lt_one.ne, by linarith ⟩;
        refine' h_factor.congr' _;
        filter_upwards [ self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ( Iio_mem_nhds hp₀_lt_one ) ] with p hp₁ hp₂ using by rw [ div_sub_div ] <;> ring_nf <;> nlinarith [ Real.log_le_sub_one_of_pos hp₀_pos, Real.log_le_sub_one_of_pos ( show 0 < p by linarith [ hp₁.out ] ), Real.log_le_sub_one_of_pos ( show 0 < p₀ by linarith [ hp₁.out ] ), hp₁.out, hp₂.out ] ;

/-
Upper bound half of the switch asymptotic.
-/
lemma switch_upper_bound
    (p₀ L : ℝ)
    (hp₀_s : s p₀ = 0)
    (hp₀_half : 1 / 2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2)
    (hpos_right : ∀ p, p₀ < p → p < 1 → 0 < s p)
    (hLpos : 0 < L)
    (hL : Filter.Tendsto (fun p => (s p - s p₀) / (p - p₀))
        (nhdsWithin p₀ (Set.Ioi p₀)) (nhds L)) :
    ∀ ε > 0, ∃ δ > 0, ∀ p, p₀ < p → p < p₀ + δ →
      ∀ hex : ∃ K : ℕ, 3 ≤ K ∧ 0 ≤ s_n p K,
        (Nat.find hex : ℝ) < switchCenter p₀ L p + ε := by
          intro ε hε
          obtain ⟨ε₁, hε₁_pos, hε₁L⟩ : ∃ ε₁ > 0, ε₁ < L ∧ ε₁ < 1 / 2 ∧ (Real.log L - Real.log (L - ε₁) + Real.log (1 + ε₁)) / (-Real.log p₀) < ε / 2 := by
            have h_cont : Filter.Tendsto (fun ε₁ => (Real.log L - Real.log (L - ε₁) + Real.log (1 + ε₁)) / (-Real.log p₀)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
              convert Filter.Tendsto.div_const ( Filter.Tendsto.add ( tendsto_const_nhds.sub ( Filter.Tendsto.log ( tendsto_const_nhds.sub ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) ) ( Filter.Tendsto.log ( tendsto_const_nhds.add ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) ) _ using 2 <;> norm_num [ hLpos.ne' ];
            have := h_cont.eventually ( gt_mem_nhds <| half_pos hε ) ; have := this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, show 0 < Min.min L ( 1 / 2 ) from lt_min hLpos <| by norm_num ⟩ ) ; obtain ⟨ ε₁, hε₁₁, hε₁₂ ⟩ := this.exists; use ε₁; aesop;
          generalize_proofs at *;
          -- Choose δ such that for p in (p₀, p₀ + δ), the conditions hold.
          obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ p, p₀ < p → p < p₀ + δ₁ → (L - ε₁) * (p - p₀) < s p ∧ s p < (L + ε₁) * (p - p₀) := by
            apply slope_bounds_from_deriv p₀ L hp₀_s hL ε₁ hε₁_pos
          generalize_proofs at *;
          obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ p, p₀ < p → p < p₀ + δ₂ → ∀ (hex : ∃ K, 3 ≤ K ∧ 0 ≤ s_n p K), (1 - ε₁) * p ^ (Nat.find hex + 1) < s p ∧ s p < (1 + ε₁) * p ^ (Nat.find hex) := by
            apply prop3 p₀ hp₀_s hp₀_half hp₀_phi hpos_right ε₁ hε₁_pos |> fun ⟨δ₂, hδ₂_pos, hδ₂⟩ => ⟨δ₂, hδ₂_pos, fun p hp₁ hp₂ hex => hδ₂ p hp₁ hp₂ hex⟩
          generalize_proofs at *;
          obtain ⟨δ₃, hδ₃_pos, hδ₃⟩ : ∃ δ₃ > 0, ∀ p, p₀ < p → p < p₀ + δ₃ → |(Real.log (p - p₀) + Real.log (L - ε₁) - Real.log (1 + ε₁)) / Real.log p - (Real.log (p - p₀) + Real.log (L - ε₁) - Real.log (1 + ε₁)) / Real.log p₀| < ε / 2 := by
            have := log_ratio_tendsto p₀ ( Real.log ( L - ε₁ ) - Real.log ( 1 + ε₁ ) ) ( by linarith ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] );
            have := Metric.tendsto_nhdsWithin_nhds.mp this ( ε / 2 ) ( half_pos hε ) ; simp_all +decide [ abs_lt ] ;
            exact ⟨ this.choose, this.choose_spec.1, fun p hp₁ hp₂ => by simpa only [ add_sub_assoc ] using this.choose_spec.2 hp₁ ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ⟩
          generalize_proofs at *;
          use min (min δ₁ δ₂) (min δ₃ ((1 - p₀) / 2))
          simp [hδ₁_pos, hδ₂_pos, hδ₃_pos];
          refine' ⟨ _, _ ⟩
          all_goals generalize_proofs at *;
          · nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
          · intro p hp₁ hp₂ x hx₁ hx₂
            have h_bound : (Nat.find (show ∃ K, 3 ≤ K ∧ 0 ≤ s_n p K from ⟨x, hx₁, hx₂⟩) : ℝ) < Real.log ((L - ε₁) * (p - p₀) / (1 + ε₁)) / Real.log p := by
                                        apply K_upper_from_exp_ineq p ((L - ε₁) * (p - p₀)) (1 + ε₁) (Nat.find (show ∃ K, 3 ≤ K ∧ 0 ≤ s_n p K from ⟨x, hx₁, hx₂⟩)) (by
                                        linarith [ show 0 < p₀ by linarith ]) (by
                                        nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), min_le_left ( min δ₁ δ₂ ) ( min δ₃ ( ( 1 - p₀ ) / 2 ) ), min_le_right ( min δ₁ δ₂ ) ( min δ₃ ( ( 1 - p₀ ) / 2 ) ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂, min_le_left δ₃ ( ( 1 - p₀ ) / 2 ), min_le_right δ₃ ( ( 1 - p₀ ) / 2 ) ]) (by
                                        exact mul_pos ( by linarith ) ( by linarith )) (by
                                        lia) (by
                                        have := hδ₂ p hp₁ ( by linarith [ min_le_left ( min δ₁ δ₂ ) ( min δ₃ ( ( 1 - p₀ ) / 2 ) ), min_le_right ( min δ₁ δ₂ ) ( min δ₃ ( ( 1 - p₀ ) / 2 ) ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂, min_le_left δ₃ ( ( 1 - p₀ ) / 2 ), min_le_right δ₃ ( ( 1 - p₀ ) / 2 ) ] ) ( show ∃ K, 3 ≤ K ∧ 0 ≤ s_n p K from ⟨ x, hx₁, hx₂ ⟩ ) ; nlinarith [ hδ₁ p hp₁ ( by linarith [ min_le_left ( min δ₁ δ₂ ) ( min δ₃ ( ( 1 - p₀ ) / 2 ) ), min_le_right ( min δ₁ δ₂ ) ( min δ₃ ( ( 1 - p₀ ) / 2 ) ), min_le_left δ₁ δ₂, min_le_right δ₁ δ₂, min_le_left δ₃ ( ( 1 - p₀ ) / 2 ), min_le_right δ₃ ( ( 1 - p₀ ) / 2 ) ] ) ] ;)
            generalize_proofs at *;
            have h_bound : Real.log ((L - ε₁) * (p - p₀) / (1 + ε₁)) / Real.log p < switchCenter p₀ L p + ε / 2 + ε / 2 := by
              have h_bound : Real.log ((L - ε₁) * (p - p₀) / (1 + ε₁)) / Real.log p = (Real.log (p - p₀) + Real.log (L - ε₁) - Real.log (1 + ε₁)) / Real.log p := by
                rw [ Real.log_div ( mul_ne_zero ( by linarith ) ( by linarith ) ) ( by linarith ), Real.log_mul ( by linarith ) ( by linarith ), add_comm ]
              generalize_proofs at *;
              have h_bound : (Real.log (p - p₀) + Real.log (L - ε₁) - Real.log (1 + ε₁)) / Real.log p₀ < switchCenter p₀ L p + ε / 2 := by
                unfold switchCenter; ring_nf at *; linarith;
              generalize_proofs at *;
              linarith [ abs_lt.mp ( hδ₃ p hp₁ ( by linarith [ min_le_left ( min δ₁ δ₂ ) ( min δ₃ ( ( 1 - p₀ ) / 2 ) ), min_le_right ( min δ₁ δ₂ ) ( min δ₃ ( ( 1 - p₀ ) / 2 ) ), min_le_left δ₃ ( ( 1 - p₀ ) / 2 ), min_le_right δ₃ ( ( 1 - p₀ ) / 2 ) ] ) ) ]
            generalize_proofs at *;
            linarith

/-
Lower bound half of the switch asymptotic.
-/
lemma switch_lower_bound
    (p₀ L : ℝ)
    (hp₀_s : s p₀ = 0)
    (hp₀_half : 1 / 2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2)
    (hpos_right : ∀ p, p₀ < p → p < 1 → 0 < s p)
    (hLpos : 0 < L)
    (hL : Filter.Tendsto (fun p => (s p - s p₀) / (p - p₀))
        (nhdsWithin p₀ (Set.Ioi p₀)) (nhds L)) :
    ∀ ε > 0, ∃ δ > 0, ∀ p, p₀ < p → p < p₀ + δ →
      ∀ hex : ∃ K : ℕ, 3 ≤ K ∧ 0 ≤ s_n p K,
        switchCenter p₀ L p - 1 - ε < (Nat.find hex : ℝ) := by
          intro ε hε
          obtain ⟨ε₁, hε₁_pos, hε₁L⟩ : ∃ ε₁ > 0, ε₁ < L ∧ ε₁ < 1 / 2 ∧ (Real.log (L + ε₁) - Real.log (1 - ε₁) - Real.log L) / (-Real.log p₀) < ε / 2 := by
            have h_log_bound : Filter.Tendsto (fun ε₁ => (Real.log (L + ε₁) - Real.log (1 - ε₁) - Real.log L) / (-Real.log p₀)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
              convert Filter.Tendsto.div_const ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( Filter.Tendsto.log ( tendsto_const_nhds.add ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) ( Filter.Tendsto.log ( tendsto_const_nhds.sub ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) ) tendsto_const_nhds ) _ using 2 <;> norm_num [ hLpos.ne' ];
            have := h_log_bound.eventually ( gt_mem_nhds <| show 0 < ε / 2 by positivity ) ; have := this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, show 0 < Min.min L ( 1 / 2 ) by positivity ⟩ ) ; obtain ⟨ ε₁, hε₁₁, hε₁₂ ⟩ := this.exists; use ε₁; aesop;
          -- Choose δ such that for p in (p₀, p₀ + δ), the conditions hold.
          obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ p, p₀ < p → p < p₀ + δ₁ → (L - ε₁) * (p - p₀) < s p ∧ s p < (L + ε₁) * (p - p₀) := by
            apply slope_bounds_from_deriv p₀ L hp₀_s hL ε₁ hε₁_pos;
          obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ p, p₀ < p → p < p₀ + δ₂ → ∀ hex : ∃ K : ℕ, 3 ≤ K ∧ 0 ≤ s_n p K, let K := Nat.find hex; (1 - ε₁) * p ^ (K + 1) < s p ∧ s p < (1 + ε₁) * p ^ K := by
            have := prop3 p₀ hp₀_s hp₀_half hp₀_phi hpos_right ε₁ hε₁_pos;
            exact this;
          obtain ⟨δ₃, hδ₃_pos, hδ₃⟩ : ∃ δ₃ > 0, ∀ p, p₀ < p → p < p₀ + δ₃ → |(Real.log (p - p₀) + (Real.log (L + ε₁) - Real.log (1 - ε₁))) / Real.log p - (Real.log (p - p₀) + (Real.log (L + ε₁) - Real.log (1 - ε₁))) / Real.log p₀| < ε / 2 := by
            have := Metric.tendsto_nhdsWithin_nhds.mp ( show Filter.Tendsto ( fun p => ( Real.log ( p - p₀ ) + ( Real.log ( L + ε₁ ) - Real.log ( 1 - ε₁ ) ) ) / Real.log p - ( Real.log ( p - p₀ ) + ( Real.log ( L + ε₁ ) - Real.log ( 1 - ε₁ ) ) ) / Real.log p₀ ) ( nhdsWithin p₀ ( Set.Ioi p₀ ) ) ( nhds 0 ) from ?_ ) ( ε / 2 ) ( half_pos hε );
            · exact ⟨ this.choose, this.choose_spec.1, fun p hp₁ hp₂ => by simpa using this.choose_spec.2 hp₁ ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ⟩;
            · convert log_ratio_tendsto p₀ ( Real.log ( L + ε₁ ) - Real.log ( 1 - ε₁ ) ) ( by linarith ) ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) using 1;
          refine' ⟨ Min.min δ₁ ( Min.min δ₂ ( Min.min δ₃ ( 1 - p₀ ) ) ), _, _ ⟩ <;> norm_num;
          · exact ⟨ hδ₁_pos, hδ₂_pos, hδ₃_pos, by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ⟩;
          · intro p hp₁ hp₂ x hx₁ hx₂; specialize hδ₁ p hp₁ ( by linarith [ min_le_left δ₁ ( min δ₂ ( min δ₃ ( 1 - p₀ ) ) ) ] ) ; specialize hδ₂ p hp₁ ( by linarith [ min_le_right δ₁ ( min δ₂ ( min δ₃ ( 1 - p₀ ) ) ), min_le_left δ₂ ( min δ₃ ( 1 - p₀ ) ) ] ) ⟨ x, hx₁, hx₂ ⟩ ; specialize hδ₃ p hp₁ ( by linarith [ min_le_right δ₁ ( min δ₂ ( min δ₃ ( 1 - p₀ ) ) ), min_le_right δ₂ ( min δ₃ ( 1 - p₀ ) ), min_le_left δ₃ ( 1 - p₀ ) ] ) ; norm_num [ abs_lt ] at *;
            have h_log_ratio : Real.log ((L + ε₁) * (p - p₀) / (1 - ε₁)) / Real.log p - 1 < (Nat.find (show ∃ K : ℕ, 3 ≤ K ∧ 0 ≤ s_n p K from ⟨ x, hx₁, hx₂ ⟩) : ℝ) := by
                                                                                                        apply K_lower_from_exp_ineq;
                                                                                                        · grind;
                                                                                                        · linarith [ min_le_right δ₁ ( min δ₂ ( min δ₃ ( 1 - p₀ ) ) ), min_le_right δ₂ ( min δ₃ ( 1 - p₀ ) ), min_le_right δ₃ ( 1 - p₀ ) ];
                                                                                                        · exact mul_pos ( by linarith ) ( by linarith );
                                                                                                        · linarith;
                                                                                                        · linarith;
            rw [ Real.log_div ( by nlinarith ) ( by nlinarith ), Real.log_mul ( by nlinarith ) ( by nlinarith ) ] at h_log_ratio;
            unfold switchCenter; ring_nf at *; linarith;

theorem switch_asymptotic_from_prop3_prop4
    (p₀ L : ℝ)
    (hp₀_s : s p₀ = 0)
    (hp₀_half : 1 / 2 < p₀)
    (hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2)
    (hpos_right : ∀ p, p₀ < p → p < 1 → 0 < s p)
    (hLpos : 0 < L)
    (hL :
      Filter.Tendsto
        (fun p => (s p - s p₀) / (p - p₀))
        (nhdsWithin p₀ (Set.Ioi p₀))
        (nhds L)) :
    SwitchAsymptoticBounds p₀ L := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, hup⟩ := switch_upper_bound p₀ L hp₀_s hp₀_half hp₀_phi hpos_right hLpos hL ε hε
  obtain ⟨δ₂, hδ₂, hlo⟩ := switch_lower_bound p₀ L hp₀_s hp₀_half hp₀_phi hpos_right hLpos hL ε hε
  exact ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun p hp hpd hex =>
    ⟨hlo p hp (by linarith [min_le_right δ₁ δ₂]) hex,
     hup p hp (by linarith [min_le_left δ₁ δ₂]) hex⟩⟩

/-! ### Main Theorem -/

structure MainTheoremData where
  p₀ : ℝ
  L : ℝ

  hp₀_half : 1 / 2 < p₀
  hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2
  hp₀_zero : s p₀ = 0

  hLpos : 0 < L
  hL :
    Filter.Tendsto
      (fun p => (s p - s p₀) / (p - p₀))
      (nhdsWithin p₀ (Set.Ioi p₀))
      (nhds L)

  prop1 :
    ∀ p : ℝ, 1 / 2 ≤ p → p < 1 →
    ∀ n : ℕ, 3 ≤ n →
      v p (n - 1) + 1 ≤ v p n

  unique_zero :
    ∀ q : ℝ, 1 / 2 ≤ q → q < 1 →
      (s q = 0 ↔ q = p₀)

  local_strategy :
    ∀ p : ℝ, 1 / 2 ≤ p → p < 1 →
    ∀ n : ℕ, 3 ≤ n →
      (
        (∀ h : ℕ, h ≤ n → IsOptimalRem p n h (remA n h)) ∨
        (∀ h : ℕ, h ≤ n → IsOptimalRem p n h (remB n h))
      )

  regime_A :
    ∀ p : ℝ, (Real.sqrt 5 - 1) / 2 ≤ p → p < 1 →
    ∀ n : ℕ, 3 ≤ n →
    ∀ h : ℕ, h ≤ n →
      IsOptimalRem p n h (remA n h)

  regime_B :
    ∀ p : ℝ, 1 / 2 ≤ p → p ≤ p₀ →
    ∀ n : ℕ, 3 ≤ n →
    ∀ h : ℕ, h ≤ n →
      IsOptimalRem p n h (remB n h)

  regime_switch :
    ∀ p : ℝ, p₀ < p → p < (Real.sqrt 5 - 1) / 2 →
      ∃ K : ℕ,
        3 ≤ K ∧
        (∀ n : ℕ, 3 ≤ n → n ≤ K →
          ∀ h : ℕ, h ≤ n →
            IsOptimalRem p n h (remB n h)) ∧
        (∀ n : ℕ, K < n →
          ∀ h : ℕ, h ≤ n →
            IsOptimalRem p n h (remA n h))

  switch_asymptotic :
    SwitchAsymptoticBounds p₀ L

private lemma unique_zero_of_prop2 (p₀ : ℝ)
    (_hp₀_half : 1 / 2 < p₀) (_hp₀_phi : p₀ < (Real.sqrt 5 - 1) / 2)
    (hp₀_zero : s p₀ = 0)
    (hneg : ∀ p, 1 / 2 ≤ p → p < p₀ → s p < 0)
    (hpos : ∀ p, p₀ < p → p < 1 → 0 < s p)
    (q : ℝ) (hq_half : 1 / 2 ≤ q) (hq_lt_one : q < 1) :
    s q = 0 ↔ q = p₀ := by
  constructor
  · intro hq_zero
    rcases lt_trichotomy q p₀ with hlt | heq | hgt
    · linarith [hneg q hq_half hlt]
    · exact heq
    · linarith [hpos q hgt hq_lt_one]
  · intro hq; simp [hq, hp₀_zero]

open Classical in
noncomputable def main_theorem : MainTheoremData :=
  have h := prop2
  let p₀ := h.choose
  have hp := h.choose_spec
  have hp₀_half := hp.1
  have hp₀_phi := hp.2.1
  have hp₀_zero := hp.2.2.1
  have hneg := hp.2.2.2.1
  have hpos := hp.2.2.2.2
  have h4 := prop4 p₀ hp₀_zero hp₀_half hp₀_phi
  let L := h4.choose
  have hL_spec := h4.choose_spec
  have hLpos := hL_spec.1
  have hL := hL_spec.2
  { p₀ := p₀
    L := L
    hp₀_half := hp₀_half
    hp₀_phi := hp₀_phi
    hp₀_zero := hp₀_zero
    hLpos := hLpos
    hL := hL
    prop1 := fun p hp hp₁ n hn => v_sub_v_sub_one_ge_one_of_half_le p n hn hp hp₁
    unique_zero := unique_zero_of_prop2 p₀ hp₀_half hp₀_phi hp₀_zero hneg hpos
    local_strategy := fun p hp hp₁ n hn => (local_main_theorem p hp hp₁ n hn).2
    regime_A := fun p hp_phi hp_lt_one n hn h hh =>
      regime1_strategyA p hp_phi hp_lt_one n hn h hh
    regime_B := fun p hp_half hp_le n hn h hh =>
      regime_le_p₀_strategyB p₀ hp₀_phi hp₀_zero hneg p hp_half hp_le n hn h hh
    regime_switch := fun p hp₀p hp_phi =>
      have hp_half : 1 / 2 ≤ p := by linarith
      have hp_lt_one : p < 1 := by linarith [hp_phi, phi_lt_one']
      regime2_strategy_switch p hp_half hp_lt_one hp_phi (hpos p hp₀p hp_lt_one)
    switch_asymptotic :=
      switch_asymptotic_from_prop3_prop4 p₀ L hp₀_zero hp₀_half hp₀_phi hpos hLpos hL
  }

#print axioms main_theorem

end CoinGame
