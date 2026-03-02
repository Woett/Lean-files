/-
Define a red/blue-colouring of $\mathbb{R}^2$ to be unit-distance-avoiding if no two blue points are distance $1$ apart. Solving Erdős Problem #214 (https://www.erdosproblems.com/214), Juhász proved that for any unit-distance-avoiding two-colouring, there must be four red points forming a unit square. More generally, she proved that for any configuration $K$ of four points and any unit-distance-avoiding two-colouring, there must be a red congruent copy of $K$.

R. Juhász, Ramsey type theorems in the plane. J. Combin. Theory Ser. A (1979), 152-160.

The proof (of the existence of a red copy of any arbitrary four-point configuration) was formalized by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), the result of which can be found below.

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
A circle of radius r centered at O is t-alternating if any two points on it at distance t have different colors.
-/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

inductive Color
| Red
| Blue
deriving DecidableEq

def t_alternating (c : Point → Color) (O : Point) (r t : ℝ) : Prop :=
  ∀ P Q : Point, dist P O = r → dist Q O = r → dist P Q = t → c P ≠ c Q

/-
Two circles of radius r centered at P and Q form a complementary pair if for any red point on one circle, the corresponding point on the other circle (via translation by Q - P) is blue.
-/
def complementary_pair (c : Point → Color) (P Q : Point) (r : ℝ) : Prop :=
  (∀ X : Point, dist X P = r → c X = Color.Red → c (X + (Q - P)) = Color.Blue) ∧
  (∀ Y : Point, dist Y Q = r → c Y = Color.Red → c (Y - (Q - P)) = Color.Blue)

/-
Given any coloring without blue points of distance t, both members of a complementary pair of radius r (r >= t/2) are t-alternating.
-/
lemma lemma1 (c : Point → Color) (t r : ℝ) (P Q : Point)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_pair : complementary_pair c P Q r)
  (h_r : r ≥ t / 2) :
  t_alternating c P r t ∧ t_alternating c Q r t := by
    constructor <;> intro A B hA hB hAB <;> contrapose! h_blue;
    · -- Consider two cases: $c A = \text{Color.Red}$ and $c A = \text{Color.Blue}$.
      by_cases hRed : c A = Color.Red;
      · use A + (Q - P), B + (Q - P);
        have := h_pair.1 A hA; have := h_pair.1 B hB; aesop;
      · cases h : c A <;> cases h' : c B <;> aesop;
    · cases h : c A <;> cases h' : c B <;> simp_all +decide;
      · use A - ( Q - P ), B - ( Q - P );
        have := h_pair.2 A ; have := h_pair.2 B ; aesop;
      · use A, B

/-
Rotation by 90 degrees preserves the norm of a vector.
-/
def rotate90 (v : Point) : Point :=
  (fun i => if i = 0 then -v 1 else v 0)

lemma rotate90_norm (v : Point) : ‖rotate90 v‖ = ‖v‖ := by
  simp [rotate90, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  ring_nf

/-
The inner product of a vector and its 90-degree rotation is zero.
-/
lemma rotate90_inner (v : Point) : inner ℝ v (rotate90 v) = (0 : ℝ) := by
  simp [rotate90, inner, Fin.sum_univ_two]
  ring

/-
Explicit construction for lemma2_geom using rotation.
-/
lemma lemma2_geom_explicit (r t : ℝ) (O P : Point)
  (h_r : r ≥ t / 2)
  (h_t_pos : t ≥ 0)
  (h_r1 : dist P O = (Real.sqrt (4 * r^2 - t^2) + t * Real.sqrt 3) / 2) :
  ∃ A B : Point, dist A O = r ∧ dist B O = r ∧ dist A B = t ∧ dist P A = t ∧ dist P B = t := by
    by_contra! h_contra;
    -- Let $v = P - O$. Let $L = \|v\| = r_1$.
    set v : EuclideanSpace ℝ (Fin 2) := P - O
    set L : ℝ := ‖v‖
    have hL : L = (Real.sqrt (4 * r ^ 2 - t ^ 2) + t * Real.sqrt 3) / 2 := by
      aesop;
    -- Let $M = O + \frac{h}{L} v$. Then $d(M, O) = h$.
    set h : ℝ := (Real.sqrt (4 * r ^ 2 - t ^ 2)) / 2
    set M : EuclideanSpace ℝ (Fin 2) := O + (h / L) • v
    have hM : ‖M - O‖ = h := by
      by_cases hL : L = 0 <;> simp_all +decide;
      · norm_num [ show t = 0 by nlinarith [ Real.sqrt_nonneg ( 4 * r ^ 2 - t ^ 2 ), Real.sqrt_nonneg 3, Real.mul_self_sqrt ( show 0 ≤ 3 by norm_num ) ] ] at *;
        rw [ eq_comm, Real.sqrt_eq_zero' ] at * ; aesop;
      · rw [ show M - O = ( h / L ) • v by rw [ add_sub_cancel_left ] ] ; rw [ norm_smul, Real.norm_of_nonneg ( div_nonneg ( div_nonneg ( Real.sqrt_nonneg _ ) zero_le_two ) ( norm_nonneg _ ) ) ] ; aesop;
    -- Let $u = \text{rotate90}(v)$. Let $A = M + \frac{t/2}{L} u$ and $B = M - \frac{t/2}{L} u$.
    set u : EuclideanSpace ℝ (Fin 2) := rotate90 v
    set A : EuclideanSpace ℝ (Fin 2) := M + (t / (2 * L)) • u
    set B : EuclideanSpace ℝ (Fin 2) := M - (t / (2 * L)) • u
    have hA : ‖A - O‖ = r := by
      have hA : ‖A - O‖ ^ 2 = h ^ 2 + (t / 2) ^ 2 := by
        have hA : ‖A - O‖ ^ 2 = ‖(h / L) • v‖ ^ 2 + ‖(t / (2 * L)) • u‖ ^ 2 := by
          have hA : ‖A - O‖ ^ 2 = ‖(h / L) • v + (t / (2 * L)) • u‖ ^ 2 := by
            simp [A, M];
            norm_num [ add_assoc ];
          rw [ hA, @norm_add_sq ℝ ];
          norm_num [ inner_smul_left, inner_smul_right ];
          exact Or.inr <| Or.inr <| by simpa [ mul_comm ] using rotate90_inner v;
        simp_all +decide [ norm_smul, mul_pow ];
        rw [ show ‖u‖ = ‖v‖ from ?_ ];
        · field_simp [hL]
          ring_nf;
          by_cases h : Real.sqrt ( 4 * r ^ 2 - t ^ 2 ) + t * Real.sqrt 3 = 0 <;> simp_all +decide [abs_of_nonneg];
          · norm_num [ show t = 0 by nlinarith [ Real.sqrt_nonneg ( 4 * r ^ 2 - t ^ 2 ), Real.sqrt_nonneg 3, Real.mul_self_sqrt ( show 0 ≤ 3 by norm_num ) ] ] at *;
            specialize h_contra O O ; aesop;
          · grind;
        · exact rotate90_norm v;
      rw [ ← sq_eq_sq₀ ] <;> try linarith;
      · rw [ hA ] ; ring_nf;
        rw [ div_pow, Real.sq_sqrt ] <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ];
      · positivity
    have hB : ‖B - O‖ = r := by
      convert hA using 1;
      norm_num [ EuclideanSpace.norm_eq, A, B ];
      ring_nf!;
      unfold rotate90; norm_num ; ring_nf;
    have hAB : ‖A - B‖ = t := by
      -- The norm of $A - B$ is the norm of $(t / (2 * L)) • u - (-(t / (2 * L)) • u)$, which simplifies to $(t / L) • u$.
      have h_norm : ‖A - B‖ = ‖(t / L) • u‖ := by
        rw [ show A - B = ( t / L ) • u by ext i; norm_num [ A, B ] ; ring ];
      rw [ h_norm, norm_smul, Real.norm_of_nonneg ( by exact div_nonneg h_t_pos ( norm_nonneg _ ) ) ];
      rw [ div_mul_eq_mul_div, div_eq_iff ] <;> norm_num [ hL ];
      · exact Or.inl <| hL ▸ rotate90_norm v;
      · by_cases ht : t = 0;
        · specialize h_contra P P ; aesop;
        · positivity
    have hPA : ‖P - A‖ = t := by
      -- Then $d(A, P)^2 = d(A, M)^2 + d(M, P)^2$ by the Pythagorean theorem.
      have hAP_sq : ‖P - A‖^2 = ‖A - M‖^2 + ‖M - P‖^2 := by
        norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_two ] at *;
        rw [ Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity ] ; ring_nf!;
        unfold rotate90; norm_num; ring;
      -- Then $d(A, M) = t/2$ and $d(M, P) = L - h = \frac{t\sqrt{3}}{2}$.
      have hAM : ‖A - M‖ = t / 2 := by
        norm_num +zetaDelta at *;
        norm_num [ ← two_smul ℝ, norm_smul ] at * ; linarith
      have hMP : ‖M - P‖ = t * Real.sqrt 3 / 2 := by
        norm_num +zetaDelta at *;
        rw [ show O + ( Real.sqrt ( 4 * r ^ 2 - t ^ 2 ) / 2 / ‖P - O‖ ) • ( P - O ) - P = ( Real.sqrt ( 4 * r ^ 2 - t ^ 2 ) / 2 / ‖P - O‖ - 1 ) • ( P - O ) by ext ; simpa using by ring ] ; norm_num [ norm_smul, hL ] ; ring_nf;
        rw [ abs_of_nonpos ] <;> norm_num;
        · field_simp;
          rw [ neg_add_eq_sub, mul_sub, mul_div_cancel₀ ] <;> ring_nf ; norm_num;
          by_cases ht : t = 0;
          · specialize h_contra P P ; aesop;
          · positivity;
        · field_simp;
          exact div_le_one_of_le₀ ( by nlinarith [ Real.sqrt_nonneg ( r ^ 2 * 4 - t ^ 2 ), Real.sqrt_nonneg 3, Real.mul_self_sqrt ( show 0 ≤ 3 by norm_num ) ] ) ( by positivity );
      rw [ ← sq_eq_sq₀ ( norm_nonneg _ ) ( by positivity ), hAP_sq, hAM, hMP ] ; ring_nf ; norm_num ; ring;
    have hPB : ‖P - B‖ = t := by
      norm_num [ EuclideanSpace.norm_eq ] at *;
      convert hPA using 2 ; ring_nf!;
      unfold rotate90; norm_num ; ring;
    exact h_contra A B hA hB hAB hPA hPB

/-
Lemma 2: If a circle of radius r is t-alternating, then the circle of radius r1 consists of red points only.
-/
lemma lemma2 (c : Point → Color) (t r : ℝ) (O : Point)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_alt : t_alternating c O r t)
  (h_r : r ≥ t / 2)
  (h_t : t ≥ 0) :
  let r1 := (Real.sqrt (4 * r^2 - t^2) + t * Real.sqrt 3) / 2
  ∀ P : Point, dist P O = r1 → c P = Color.Red := by
    intro r1 P hP;
    -- By `lemma2_geom_explicit`, there exist $A, B$ such that $d(A, O) = r$, $d(B, O) = r$, $d(A, B) = t$, $d(P, A) = t$, and $d(P, B) = t$.
    obtain ⟨A, B, hA, hB, hAB, hPA, hPB⟩ : ∃ A B : Point, dist A O = r ∧ dist B O = r ∧ dist A B = t ∧ dist P A = t ∧ dist P B = t := by
      apply lemma2_geom_explicit r t O P h_r h_t hP;
    cases h : c A <;> cases h' : c B <;> cases h'' : c P <;> specialize h_alt A B <;> aesop

/-
A regular t-rhombus is a configuration of four points {A, B, C, D} such that {A, B, C} and {B, C, D} are equilateral triangles of side length t.
-/
def regular_t_rhombus (t : ℝ) (A B C D : Point) : Prop :=
  dist A B = t ∧ dist B C = t ∧ dist C A = t ∧
  dist B D = t ∧ dist D C = t ∧ dist C B = t ∧
  dist A D = t * Real.sqrt 3

/-
If no red regular t-rhombus exists, then the circles around C and D form a complementary pair.
-/
lemma lemma3_step1 (c : Point → Color) (t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_t : t > 0)
  (A B C D : Point)
  (h_rhombus : regular_t_rhombus t A C D B)
  (hA : c A = Color.Blue)
  (hB : c B = Color.Blue)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red) :
  complementary_pair c C D t := by
    contrapose! h_no_red_rhombus with h_no_red_rhombus;
    -- By definition of complementary_pair, if ¬complementary_pair c C D t, then there exists a point X on γ_C(t) such that X is red and X + (D - C) is also red.
    obtain ⟨X, hX⟩ : ∃ X : Point, dist X C = t ∧ c X = Color.Red ∧ c (X + (D - C)) = Color.Red := by
      by_cases hX : ∃ X : Point, dist X C = t ∧ c X = Color.Red ∧ c (X + (D - C)) = Color.Red;
      · exact hX;
      · refine' False.elim ( h_no_red_rhombus ⟨ _, _ ⟩ ) <;> simp_all +decide [ dist_eq_norm ];
        · exact fun X hX₁ hX₂ => Or.resolve_left ( by cases h : c ( X + ( D - C ) ) <;> tauto ) ( hX X hX₁ hX₂ );
        · intro Y hy hy'; specialize hX ( Y - ( D - C ) ) ; simp_all +decide ;
          exact Or.resolve_left ( by cases h : c ( Y - ( D - C ) ) <;> tauto ) ( hX ( by simpa [ sub_sub ] using hy ) );
    -- Let's choose points $P$, $Q$, $R$, and $S$ as follows:
    -- $P = X + (A - C)$, $Q = X$, $R = X + (D - C)$, $S = X + (B - C)$.
    use X + (A - C), X, X + (D - C), X + (B - C);
    unfold regular_t_rhombus at *; simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
    constructor <;> have := h_blue ( X + ( A - C ) ) A <;> have := h_blue ( X + ( B - C ) ) B <;> simp_all +decide;
    · exact Classical.not_not.1 fun h => ‹Real.sqrt ( ( X 0 + ( A 0 - C 0 ) - A 0 ) ^ 2 + ( X 1 + ( A 1 - C 1 ) - A 1 ) ^ 2 ) = t → ¬c ( X + ( A - C ) ) = Color.Blue› ( by rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> linarith ) ( by cases h : c ( X + ( A - C ) ) <;> tauto );
    · exact Or.resolve_left ( by cases c ( X + ( B - C ) ) <;> tauto ) ( this ( by convert hX.1 using 1 ; ring_nf ) )

/-
Diametrically opposite points on a t-alternating circle of radius t have different colors.
-/
lemma lemma3_step3 (c : Point → Color) (O : Point) (t : ℝ)
  (h_alt : t_alternating c O t t)
  (h_t : t > 0) :
  ∀ P : Point, dist P O = t → c P ≠ c (2 • O - P) := by
    -- Let $P$ be a point on the circle with radius $t$ centered at $O$.
    intro P hP
    -- Consider the sequence of points $P_0 = P$, $P_1$, $P_2$, $P_3 = 2O - P$ on the circle such that $d(P_i, P_{i+1}) = t$.
    obtain ⟨P1, P2, hP1, hP2⟩ : ∃ P1 P2 : Point, dist P O = t ∧ dist P1 O = t ∧ dist P2 O = t ∧ dist P P1 = t ∧ dist P1 P2 = t ∧ dist P2 (2 • O - P) = t := by
      simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
      refine' ⟨ fun i => if i = 0 then O 0 + ( P 0 - O 0 ) * Real.cos ( Real.pi / 3 ) - ( P 1 - O 1 ) * Real.sin ( Real.pi / 3 ) else O 1 + ( P 0 - O 0 ) * Real.sin ( Real.pi / 3 ) + ( P 1 - O 1 ) * Real.cos ( Real.pi / 3 ), _, fun i => if i = 0 then O 0 + ( P 0 - O 0 ) * Real.cos ( 2 * Real.pi / 3 ) - ( P 1 - O 1 ) * Real.sin ( 2 * Real.pi / 3 ) else O 1 + ( P 0 - O 0 ) * Real.sin ( 2 * Real.pi / 3 ) + ( P 1 - O 1 ) * Real.cos ( 2 * Real.pi / 3 ), _, _, _, _ ⟩ <;> norm_num [ Real.sin_two_mul, Real.cos_two_mul, mul_div_assoc ] <;> ring_nf <;> norm_num [ hP ];
      · rw [ ← hP ] ; ring_nf;
      · rw [ ← hP ] ; ring_nf;
      · exact Eq.trans ( by ring_nf ) hP;
      · convert hP using 2 ; ring;
      · rw [ ← hP ] ; ring_nf;
    cases h : c P <;> cases h' : c ( 2 • O - P ) <;> simp_all +decide [ t_alternating ];
    · cases h'' : c P1 <;> cases h''' : c P2 <;> have := h_alt _ _ hP1 hP2.1 hP2.2.2.1 <;> have := h_alt _ _ hP2.1 hP2.2.1 hP2.2.2.2.1 <;> have := h_alt _ _ hP2.2.1 ( show Dist.dist ( 2 • O - P ) O = t from ?_ ) ( show Dist.dist P2 ( 2 • O - P ) = t from ?_ ) <;> simp_all +decide [ two_smul ];
      rwa [ dist_comm ];
    · have := h_alt P P1 hP1 hP2.1 hP2.2.2.1; have := h_alt P1 P2 hP2.1 hP2.2.1 hP2.2.2.2.1; have := h_alt P2 ( 2 • O - P ) hP2.2.1 ( by
        simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
        exact Eq.trans ( by ring_nf ) hP1 ) ( by
        convert hP2.2.2.2.2 using 1 ; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf!; ) ; simp_all +decide ;
      cases h'' : c P1 <;> cases h''' : c P2 <;> simp_all +decide [ two_smul ];
      exact h_alt P1 P2 hP2.1 hP2.2.1 hP2.2.2.2.1 ( by aesop )

/-
If A and B are blue points at distance t*sqrt(3) and M is their common neighbor, then the circle of radius t*sqrt(3) around M is red.
-/
lemma blue_pair_implies_red_circle (c : Point → Color) (t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_t : t > 0)
  (A B M : Point)
  (h_dist : dist A B = t * Real.sqrt 3)
  (hA : c A = Color.Blue)
  (hB : c B = Color.Blue)
  (hM_A : dist M A = t)
  (hM_B : dist M B = t)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red) :
  ∀ P : Point, dist P M = t * Real.sqrt 3 → c P = Color.Red := by
    -- Since $A$ and $B$ are blue points at distance $t\sqrt{3}$ and $M$ is their common neighbor, by `lemma3_step1`, the circles $\gamma_M(t)$ and $\gamma_{M'}(t)$ are complementary.
    obtain ⟨M', hM'_dist, hM'_blue⟩ : ∃ M' : Point, dist M' M = t ∧ dist M' A = t ∧ dist M' B = t ∧ c M' = Color.Red := by
      obtain ⟨M', hM'_dist, hM'_blue⟩ : ∃ M' : Point, dist M' M = t ∧ dist M' A = t ∧ dist M' B = t := by
        -- By definition of $M'$, we know that $M'$ is the reflection of $M$ over the line $AB$.
        use 2 • (midpoint ℝ A B) - M;
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
        norm_num [ midpoint_eq_smul_add ] at *;
        rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> ring_nf at * <;> norm_num at *;
        · exact ⟨ by linarith, by rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] <;> linarith, by rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] <;> linarith ⟩;
        · positivity;
        · positivity;
        · positivity;
        · positivity;
      exact ⟨ M', hM'_dist, hM'_blue.1, hM'_blue.2, by cases h : c M' <;> tauto ⟩;
    intro P hP
    have h_complementary : complementary_pair c M M' t := by
      apply lemma3_step1 c t h_blue h_t A B M M';
      · unfold regular_t_rhombus;
        simp_all +decide [ dist_comm ];
      · assumption;
      · assumption;
      · exact h_no_red_rhombus;
    -- By `lemma1`, $\gamma_M(t)$ is alternating.
    have h_alternating : t_alternating c M t t := by
      have := lemma1 c t t M M' h_blue h_complementary ( by linarith ) ; aesop;
    -- By `lemma2`, $\gamma_M(t\sqrt{3})$ is red.
    have h_red : ∀ P : Point, dist P M = t * Real.sqrt 3 → c P = Color.Red := by
      convert lemma2 c t t M h_blue h_alternating _ _ using 1 <;> norm_num [ h_t.le ];
      rw [ show 4 * t ^ 2 - t ^ 2 = 3 * t ^ 2 by ring, Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ) ] ; ring_nf;
    exact h_red P hP

/-
A circle of radius R contains a chord of length d for any 0 <= d <= 2R.
-/
lemma circle_has_chord (R d : ℝ) (O : Point)
  (h_R : R > 0)
  (h_d : 0 ≤ d ∧ d ≤ 2 * R) :
  ∃ X Y : Point, dist X O = R ∧ dist Y O = R ∧ dist X Y = d := by
    obtain ⟨X, Y, hXY⟩ : ∃ X Y : ℂ, ‖X‖ = R ∧ ‖Y‖ = R ∧ ‖X - Y‖ = d := by
      -- By the properties of the circle, we can find points $X$ and $Y$ on the circle such that $|X - Y| = d$.
      obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, d = 2 * R * Real.sin (θ / 2) := by
        exact ⟨ 2 * Real.arcsin ( d / ( 2 * R ) ), by rw [ mul_div_cancel_left₀ _ two_ne_zero, Real.sin_arcsin ] <;> nlinarith [ mul_div_cancel₀ d ( by positivity : ( 2 * R ) ≠ 0 ) ] ⟩;
      refine' ⟨ R * Complex.exp ( θ * Complex.I / 2 ), R * Complex.exp ( -θ * Complex.I / 2 ), _, _, _ ⟩ <;> norm_num [ Complex.norm_exp, hθ ];
      · linarith;
      · linarith;
      · norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im, neg_div ];
        rw [ Real.sqrt_mul_self ] <;> nlinarith [ Real.sin_sq_le_one ( θ / 2 ) ];
    use fun i => O i + X.re * ( if i = 0 then 1 else 0 ) + X.im * ( if i = 1 then 1 else 0 ), fun i => O i + Y.re * ( if i = 0 then 1 else 0 ) + Y.im * ( if i = 1 then 1 else 0 );
    simp_all +decide [ Complex.norm_def, Complex.normSq_apply, dist_eq_norm, EuclideanSpace.norm_eq ];
    simpa only [ sq ] using hXY

/-
If dist(O, P) = 2t, there exist P1, P2, P3 such that P1, P2 are at distance t*sqrt(3) from O and t from P, P3 is at distance t from O and P, and {P1, P, P3, P2} form a regular t-rhombus.
-/
lemma lemma3_case2_geom_corrected (t : ℝ) (O P : Point)
  (h_t : t > 0)
  (h_dist : dist O P = 2 * t) :
  ∃ P1 P2 P3 : Point,
    dist P1 O = t * Real.sqrt 3 ∧ dist P1 P = t ∧
    dist P2 O = t * Real.sqrt 3 ∧ dist P2 P = t ∧
    dist P3 O = t ∧ dist P3 P = t ∧
    regular_t_rhombus t P1 P P3 P2 := by
      unfold regular_t_rhombus;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
      -- Let's choose the points P1, P2, and P3 as follows:
      -- P1 = (O + 3P)/4 + (P - O)⊥ * (sqrt(3)/4)
      -- P2 = (O + 3P)/4 - (P - O)⊥ * (sqrt(3)/4)
      -- P3 = (O + P)/2
      -- where (P - O)⊥ is the perpendicular vector to (P - O).
      set P3 : Point := fun i => (O i + P i) / 2
      set P1 : Point := fun i => (O i + 3 * P i) / 4 + (if i = 0 then -(P 1 - O 1) * (Real.sqrt 3 / 4) else (P 0 - O 0) * (Real.sqrt 3 / 4))
      set P2 : Point := fun i => (O i + 3 * P i) / 4 - (if i = 0 then -(P 1 - O 1) * (Real.sqrt 3 / 4) else (P 0 - O 0) * (Real.sqrt 3 / 4));
      refine' ⟨ P1, _, _, P2, _, _, P3, _, _ ⟩ <;> norm_num [ Real.sqrt_eq_iff_mul_self_eq_of_pos, h_t ];
      all_goals norm_num [ P1, P2, P3 ] ; ring_nf at * ; norm_num at *;
      all_goals rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at h_dist <;> try linarith;
      exact ⟨ by linarith, by linarith, by linarith, by linarith, by linarith, by linarith ⟩

/-
Helper lemma for Case 1: Contradiction from alternating circle and red circles.
-/
lemma lemma3_case1_helper (c : Point → Color) (t : ℝ)
  (h_t : t > 0)
  (C E N : Point)
  (h_sym : N = 2 • C - E)
  (h_dist_NC : dist N C = t * Real.sqrt 3)
  (h_gamma_N_red : ∀ P, dist P N = t * Real.sqrt 3 → c P = Color.Red)
  (h_gamma_E_red : ∀ P, dist P E = t * Real.sqrt 3 → c P = Color.Red)
  (h_gamma_C_alt : t_alternating c C t t) :
  False := by
    -- By Lemma 3_step3, since there exist points X and Y on gamma_C(t) such that dist(X, Y) = t and Y = 2C - X, we conclude c(X) ≠ c(Y).
    have h_gamma_C_neq : ∀ X : Point, dist X C = t → c X ≠ c (2 • C - X) := by
      exact fun X a => lemma3_step3 c C t h_gamma_C_alt h_t X a;
    -- Let's choose any point X on the circle gamma_C(t).
    obtain ⟨X, hX⟩ : ∃ X : Point, dist X C = t ∧ dist X N = t * Real.sqrt 3 := by
      obtain ⟨V, W, X, hX⟩ : ∃ V W X : Point, V = N - C ∧ W = rotate90 V ∧ X = C + (1/6 : ℝ) • V + (Real.sqrt 11 / 6) • W ∧ dist X C = t ∧ dist X N = t * Real.sqrt 3 := by
        refine' ⟨ _, _, _, rfl, rfl, rfl, _, _ ⟩ <;> norm_num [ dist_eq_norm ] at *;
        · norm_num [ EuclideanSpace.norm_eq, rotate90 ] at *;
          rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> ring_nf at * <;> norm_num at * <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] ;
        · norm_num [ EuclideanSpace.norm_eq, rotate90 ] at *;
          rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> ring_nf at * <;> norm_num at * <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] ;
      exact ⟨ X, hX.2.2.2 ⟩;
    specialize h_gamma_C_neq X hX.1; simp_all +decide [ two_smul ] ;
    specialize h_gamma_E_red ( C + C - X ) ; simp_all +decide [ dist_eq_norm ] ;
    exact h_gamma_C_neq <| Eq.symm <| h_gamma_E_red <| by rw [ show C + C - X - E = - ( X + E - ( C + C ) ) by abel1 ] ; rw [ norm_neg ] ; exact hX.2;

/-
Any two subsets of {0, 1, 2} with size at least 2 must have a non-empty intersection.
-/
def regular_triangle_side_1 (p : Fin 3 → Point) : Prop :=
  dist (p 0) (p 1) = 1 ∧ dist (p 1) (p 2) = 1 ∧ dist (p 2) (p 0) = 1

/-
Given a configuration of 4 points and a target pair of points P, Q with the same distance as two points in the configuration, we can find a congruent configuration that maps those two points to P and Q.
-/
lemma exists_congruent_embedding (cfg : Fin 4 → Point) (i j : Fin 4) (P Q : Point)
  (h_dist : dist (cfg i) (cfg j) = dist P Q) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ cfg' i = P ∧ cfg' j = Q := by
    by_contra h_contra;
    -- Let $v = cfg j - cfg i$ and $w = Q - P$. Since $dist (cfg i) (cfg j) = dist P Q$, we have $\|v\| = \|w\|$.
    set v : EuclideanSpace ℝ (Fin 2) := cfg j - cfg i
    set w : EuclideanSpace ℝ (Fin 2) := Q - P
    have hvw : ‖v‖ = ‖w‖ := by
      simp +zetaDelta at *;
      convert h_dist using 1 <;> norm_num [ dist_eq_norm' ];
    -- Since $v$ and $w$ have the same length, there exists a rotation $R$ such that $R(v) = w$.
    obtain ⟨R, hR⟩ : ∃ R : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2), R v = w := by
      by_cases hv : v = 0 <;> by_cases hw : w = 0 <;> simp_all +decide [ EuclideanSpace.norm_eq ];
      · exact False.elim <| hw <| by ext x; fin_cases x <;> norm_num <;> rw [ eq_comm, Real.sqrt_eq_zero' ] at hvw <;> nlinarith!;
      · exact False.elim <| hvw.not_gt <| Real.sqrt_pos.mpr <| not_le.mp fun h => hv <| by ext x; fin_cases x <;> norm_num <;> nlinarith!;
      · -- Since $v$ and $w$ are non-zero and have the same length, we can construct a rotation matrix $R$ such that $R(v) = w$.
        obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, w = ![v 0 * Real.cos θ - v 1 * Real.sin θ, v 0 * Real.sin θ + v 1 * Real.cos θ] := by
          -- Since $v$ and $w$ are non-zero and have the same length, we can use the fact that any two vectors with the same length can be rotated into each other.
          have h_rotate : ∃ θ : ℝ, w 0 = v 0 * Real.cos θ - v 1 * Real.sin θ ∧ w 1 = v 0 * Real.sin θ + v 1 * Real.cos θ := by
            have h_rotate : ∃ θ : ℝ, w 0 = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) * Real.cos θ ∧ w 1 = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) * Real.sin θ := by
              use ( Complex.arg ( w 0 + w 1 * Complex.I ) ) ; rw [ hvw ] ; rw [ Complex.cos_arg, Complex.sin_arg ] <;> simp_all +decide [ Complex.ext_iff ] ;
              · norm_num [ Complex.normSq, Complex.norm_def ] ; ring_nf ;
                exact ⟨ by rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( by exact not_le.mp fun h => hw <| by ext x; fin_cases x <;> norm_num <;> nlinarith! ) ) ), mul_one ], by rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( by exact not_le.mp fun h => hw <| by ext x; fin_cases x <;> norm_num <;> nlinarith! ) ) ), mul_one ] ⟩;
              · exact fun h₀ h₁ => hw <| by ext x; fin_cases x <;> aesop;
            obtain ⟨ θ, hθ ⟩ := h_rotate;
            -- Since $v$ and $w$ are non-zero and have the same length, we can use the fact that any two vectors in $\mathbb{R}^2$ with the same length can be rotated into each other. Hence, there exists a rotation matrix $R$ such that $R(v) = w$.
            obtain ⟨θ', hθ'⟩ : ∃ θ' : ℝ, v 0 = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) * Real.cos θ' ∧ v 1 = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) * Real.sin θ' := by
              use Complex.arg (v 0 + v 1 * Complex.I);
              rw [ Complex.cos_arg, Complex.sin_arg ] <;> norm_num [ Complex.ext_iff, hv ];
              · norm_num [ Complex.normSq, Complex.norm_def, ← sq ];
                exact ⟨ by rw [ mul_div_cancel₀ _ ( ne_of_gt ( Real.sqrt_pos.mpr ( by exact not_le.mp fun h => hv <| by ext x; fin_cases x <;> norm_num <;> nlinarith! ) ) ) ], by rw [ mul_div_cancel₀ _ ( ne_of_gt ( Real.sqrt_pos.mpr ( by exact not_le.mp fun h => hv <| by ext x; fin_cases x <;> norm_num <;> nlinarith! ) ) ) ] ⟩;
              · exact fun h => fun h' => hv <| by ext x; fin_cases x <;> aesop;
            generalize_proofs at *; (
            use θ - θ';
            rw [ hθ.1, hθ.2, hθ'.1, hθ'.2 ] ; rw [ Real.cos_sub, Real.sin_sub ] ; ring_nf ;
            grind);
          exact ⟨ h_rotate.choose, by ext i; fin_cases i <;> [ exact h_rotate.choose_spec.1; exact h_rotate.choose_spec.2 ] ⟩;
        refine' ⟨ _, _ ⟩;
        refine' { toFun := fun x => ![x 0 * Real.cos θ - x 1 * Real.sin θ, x 0 * Real.sin θ + x 1 * Real.cos θ], map_add' := _, map_smul' := _, norm_map' := _ };
        all_goals norm_num [ EuclideanSpace.norm_eq ];
        · exact fun x y => by ext i; fin_cases i <;> norm_num <;> ring;
        · exact fun m x => by ext i; fin_cases i <;> norm_num <;> ring;
        · exact fun x => congr_arg Real.sqrt ( by nlinarith only [ Real.sin_sq_add_cos_sq θ ] );
        · exact hθ.symm;
    refine' h_contra ⟨ fun k => R ( cfg k - cfg i ) + P, _, _, _ ⟩ <;> simp_all +decide [ dist_eq_norm' ];
    · refine' fun k l => _ ; aesop;
    · rw [ ← map_sub ] at * ; aesop

/-
Given two regular unit triangles R and S, and a coloring with no two blue points at distance 1, there exists an index i such that both R_i and S_i are red.
-/
lemma lemma4_pigeonhole (c : Point → Color) (R S : Fin 3 → Point)
  (hR : ∀ i j : Fin 3, i ≠ j → dist (R i) (R j) = 1)
  (hS : ∀ i j : Fin 3, i ≠ j → dist (S i) (S j) = 1)
  (h_blue : ∀ x y : Point, dist x y = 1 → ¬ (c x = Color.Blue ∧ c y = Color.Blue)) :
  ∃ i : Fin 3, c (R i) = Color.Red ∧ c (S i) = Color.Red := by
    -- By the pigeonhole principle, since there are three points in each triangle and at most one can be blue, there must be at least two points in each triangle that are red.
    have h_pigeonhole : ∀ (T : Fin 3 → Point), (∀ i j : Fin 3, i ≠ j → dist (T i) (T j) = 1) → ∃ i j : Fin 3, i ≠ j ∧ c (T i) = Color.Red ∧ c (T j) = Color.Red := by
      intro T hT
      by_cases h_blue_count : ∃ i j : Fin 3, i ≠ j ∧ c (T i) = Color.Blue ∧ c (T j) = Color.Blue;
      · grind +ring;
      · simp_all +decide [ Fin.exists_fin_succ ];
        cases h : c ( T 0 ) <;> cases h' : c ( T 1 ) <;> cases h'' : c ( T 2 ) <;> simp_all +decide only;
    obtain ⟨ i, j, hij, hi, hj ⟩ := h_pigeonhole R hR;
    obtain ⟨ k, l, hkl, hk, hl ⟩ := h_pigeonhole S hS;
    grind

/-
Given a family of configurations where two points are always red and the others form regular triangles, there is a configuration where all points are red.
-/
lemma lemma4_helper (c : Point → Color) (cfgk : Fin 3 → Fin 4 → Point) (i j : Fin 4)
  (h_neq : i ≠ j)
  (h_red_i : ∀ k, c (cfgk k i) = Color.Red)
  (h_red_j : ∀ k, c (cfgk k j) = Color.Red)
  (h_triangle : ∀ m, regular_triangle_side_1 (fun k => cfgk k m))
  (h_blue : ∀ x y : Point, dist x y = 1 → ¬ (c x = Color.Blue ∧ c y = Color.Blue)) :
  ∃ k, ∀ m, c (cfgk k m) = Color.Red := by
    obtain ⟨x, y, hxy⟩ : ∃ x y : Fin 4, x ≠ i ∧ x ≠ j ∧ y ≠ i ∧ y ≠ j ∧ x ≠ y := by
      fin_cases i <;> fin_cases j <;> trivial;
    -- By `lemma4_pigeonhole`, there exists an index $k$ such that $cfgk(k, x)$ and $cfgk(k, y)$ are both red.
    obtain ⟨k, hk⟩ : ∃ k : Fin 3, c (cfgk k x) = Color.Red ∧ c (cfgk k y) = Color.Red := by
      apply lemma4_pigeonhole c (fun k => cfgk k x) (fun k => cfgk k y) (fun k l hkl => h_triangle x |>.1 |> fun h => by
        fin_cases k <;> fin_cases l <;> simp_all +decide [ regular_triangle_side_1 ];
        · simpa only [ dist_comm ] using h_triangle x |>.2.2;
        · rw [ dist_comm, h_triangle x |>.1 ];
        · rw [ dist_comm, h_triangle x |>.2.1 ]) (fun k l hkl => h_triangle y |>.1 |> fun h => by
        fin_cases k <;> fin_cases l <;> simp_all +decide only [regular_triangle_side_1];
        all_goals simp_all +decide [ dist_comm ] ;
        · rw [ dist_comm, h_triangle y |>.1 ];
        · rw [ dist_comm, h_triangle y |>.1 ]) h_blue;
    use k; intro m; fin_cases m <;> simp_all +decide ;
    · fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y <;> simp_all ( config := { decide := Bool.true } ) only [ ] ;
      all_goals tauto;
    · fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y <;> simp_all ( config := { decide := Bool.true } ) only [ ] ;
      all_goals tauto;
    · fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y <;> simp_all ( config := { decide := Bool.true } ) only [ ] ;
      all_goals tauto;
    · fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y <;> simp_all ( config := { decide := Bool.true } ) only [ ] ;
      all_goals tauto;

/-
Let $\{A, B, C, D\}$ be a configuration having two points with distance $a$. Given any coloring without blue points of distance $1$, if there exists a red configuration $\{P_{1}, P_{2}, P_{3}, Q_{1}, Q_{2}, Q_{3}\}$ such that $\{P_{1}, P_{2}, P_{3}\}$ is a regular triangle with unit side and $\{Q_{1}, Q_{2}, Q_{3}\}$ arises from $\{P_{1}, P_{2}, P_{3}\}$ by a translation by distance $a$, then we can find a red configuration congruent to $\{A, B, C, D\}$.
-/
lemma lemma4 (c : Point → Color) (a : ℝ) (cfg : Fin 4 → Point)
  (h_blue : ∀ x y : Point, dist x y = 1 → ¬ (c x = Color.Blue ∧ c y = Color.Blue))
  (h_dist_a : ∃ i j, i ≠ j ∧ dist (cfg i) (cfg j) = a)
  (h_exists_red : ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∃ v : Point, ‖v‖ = a ∧ ∀ i, q i = p i + v) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red)) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
    have := @lemma4_helper;
    contrapose! this;
    obtain ⟨ p, q, hp, ⟨ v, hv, hv' ⟩, hp', hq' ⟩ := h_exists_red;
    obtain ⟨ i, j, hij, h ⟩ := h_dist_a;
    obtain ⟨ cfg0, hcfg0 ⟩ := exists_congruent_embedding cfg i j ( p 0 ) ( q 0 ) ( by aesop );
    refine' ⟨ c, fun k m => cfg0 m + ( p k - p 0 ), i, j, hij, _, _, _, _ ⟩ <;> simp_all +decide [ dist_eq_norm ];
    · intro k; convert hq' k using 1; abel_nf;
    · intro m; unfold regular_triangle_side_1; simp +decide [dist_eq_norm] ;
      exact ⟨ by simpa [ dist_eq_norm ] using hp.1, by simpa [ dist_eq_norm ] using hp.2.1, by simpa [ dist_eq_norm ] using hp.2.2 ⟩;
    · refine' ⟨ h_blue, fun x => _ ⟩;
      specialize this ( fun m => cfg0 m + ( p x - p 0 ) ) ; simp_all +decide [ Congruent ]

/-
Under the given conditions, G must be Blue.
-/
lemma lemma_G_blue (t : ℝ) (h_t : t > 0)
  (c : Point → Color)
  (h_blue_t : ∀ x y : Point, dist x y = t → ¬ (c x = Color.Blue ∧ c y = Color.Blue))
  (h_no_red_rhombus : ¬ ∃ P Q R S, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (A C E F G K_G : Point)
  (hA : A = ![0, 0])
  (hC : C = ![0.5 * t, t * Real.sqrt 3 / 2])
  (hE : E = ![-0.5 * t, t * Real.sqrt 3 / 2])
  (hF : F = ![-1 * t, 0])
  (hG : G = ![-1.5 * t, t * Real.sqrt 3 / 2])
  (hK_G : K_G = ![-1 * t, t * Real.sqrt 3])
  (hA_blue : c A = Color.Blue)
  (h_dist_C_red : ∀ X, dist X C = t * Real.sqrt 3 → c X = Color.Red) :
  c G = Color.Blue := by
    -- Since $K_G$ is at distance $t\sqrt{3}$ from $C$, and $C$ is red, $K_G$ must also be red.
    have hK_G_red : c K_G = Color.Red := by
      convert h_dist_C_red K_G _ ; norm_num [ *, EuclideanSpace.norm_eq, dist_eq_norm ] ; ring_nf ; norm_num [ h_t.le ] ;
      rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] ;
    -- By contradiction, assume $G$ is Red.
    by_contra hG_red;
    -- Since $E$ is at distance $t$ from $A$, and $A$ is Blue, $E$ must be Red.
    have hE_red : c E = Color.Red := by
      have hE_red : dist A E = t := by
        norm_num [ hA, hE, dist_eq_norm, EuclideanSpace.norm_eq ];
        rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ];
      cases h : c E <;> tauto;
    -- Since $F$ is at distance $t$ from $A$, and $A$ is Blue, $F$ must be Red.
    have hF_red : c F = Color.Red := by
      specialize h_dist_C_red F ; simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
      exact h_dist_C_red ( by rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] );
    -- By `lemma_rhombus_FGEK_aux`, {F, G, E, K_G} is a regular t-rhombus.
    have h_rhombus_FGEK : regular_t_rhombus t F G E K_G := by
      unfold regular_t_rhombus; norm_num [ hF, hG, hE, hK_G ] ; ring_nf ; norm_num [ h_t.le ] ;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf ; norm_num [ h_t.le ] ;
      rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith;
    exact h_no_red_rhombus ⟨ F, G, E, K_G, h_rhombus_FGEK, hF_red, by cases h : c G <;> tauto, hE_red, hK_G_red ⟩

/-
The points O, L, M1, N form a regular t-rhombus.
-/
lemma lemma_rhombus_OLM1N_aux (t : ℝ) (h_t : t > 0)
  (O L M1 N : Point)
  (hO : O = ![0.5 * t, 1.5 * t * Real.sqrt 3])
  (hL : L = ![1.5 * t, 1.5 * t * Real.sqrt 3])
  (hM1 : M1 = ![1 * t, t * Real.sqrt 3])
  (hN : N = ![2 * t, t * Real.sqrt 3]) :
  regular_t_rhombus t O L M1 N := by
    constructor <;> norm_num [ EuclideanSpace.norm_eq, dist_eq_norm, hO, hL, hM1, hN ];
    · rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith;
    · repeat ring_nf <;> norm_num [ h_t.le ] ;

/-
Under the given conditions, L must be Blue.
-/
lemma lemma_L_blue (t : ℝ) (h_t : t > 0)
  (c : Point → Color)
  (h_blue_t : ∀ x y : Point, dist x y = t → ¬ (c x = Color.Blue ∧ c y = Color.Blue))
  (h_no_red_rhombus : ¬ ∃ P Q R S, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (B C L M1 N O : Point)
  (hB : B = ![1.5 * t, t * Real.sqrt 3 / 2])
  (hC : C = ![0.5 * t, t * Real.sqrt 3 / 2])
  (hL : L = ![1.5 * t, 1.5 * t * Real.sqrt 3])
  (hM1 : M1 = ![1 * t, t * Real.sqrt 3])
  (hN : N = ![2 * t, t * Real.sqrt 3])
  (hO : O = ![0.5 * t, 1.5 * t * Real.sqrt 3])
  (hB_blue : c B = Color.Blue)
  (h_dist_C_red : ∀ X, dist X C = t * Real.sqrt 3 → c X = Color.Red) :
  c L = Color.Blue := by
    -- By assumption, $L$ must be Blue.
    by_contra hL_red;
    -- Since $L$ is Red, and $B$ is Blue, their neighbors $N$ and $M1$ (at distance $t$) must be Red.
    have hN_red : c N = Color.Red := by
      convert h_dist_C_red _ _ using 2 ; norm_num [ *, dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf ; norm_num [ h_t.le ] ;
      rw [ show t ^ 2 * ( 9 / 4 ) + t ^ 2 * 3 * ( 1 / 4 ) = t ^ 2 * 3 by ring, Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ) ]
    have hM1_red : c M1 = Color.Red := by
      apply Classical.byContradiction
      intro hM1_blue;
      exact h_blue_t M1 B ( by
        norm_num [ *, dist_eq_norm, EuclideanSpace.norm_eq ];
        rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] ) ⟨ by
        cases h : c M1 <;> tauto, hB_blue ⟩
    have hO_red : c O = Color.Red := by
      apply h_dist_C_red;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, hO, hC ];
      rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ];
    -- By `lemma_rhombus_OLM1N_aux`, {O, L, M1, N} is a regular t-rhombus.
    have h_rhombus : regular_t_rhombus t O L M1 N := by
      exact lemma_rhombus_OLM1N_aux t h_t O L M1 N hO hL hM1 hN;
    exact h_no_red_rhombus ⟨ O, L, M1, N, h_rhombus, hO_red, by cases h : c L <;> tauto, hM1_red, hN_red ⟩

/-
The points K, N, P, K' form a regular t-rhombus.
-/
lemma lemma_rhombus_KNPK_prime_aux (t : ℝ) (h_t : t > 0)
  (P N K K_prime : Point)
  (hP : P = ![3 * t, t * Real.sqrt 3])
  (hN : N = ![2 * t, t * Real.sqrt 3])
  (hK : K = ![2.5 * t, t * Real.sqrt 3 / 2])
  (hK_prime : K_prime = ![2.5 * t, 1.5 * t * Real.sqrt 3]) :
  regular_t_rhombus t K N P K_prime := by
    constructor <;> norm_num [ ← List.ofFn_inj, dist_eq_norm, EuclideanSpace.norm_eq, * ] <;> ring_nf <;> norm_num [ h_t.le ] ;
    · rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith;
    · rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith

/-
Under the given conditions, P must be Blue.
-/
lemma lemma_P_blue_aux (t : ℝ) (h_t : t > 0)
  (c : Point → Color)
  (h_blue_t : ∀ x y : Point, dist x y = t → ¬ (c x = Color.Blue ∧ c y = Color.Blue))
  (h_no_red_rhombus : ¬ ∃ P Q R S, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (B L N K K_prime P : Point)
  (hB : B = ![1.5 * t, t * Real.sqrt 3 / 2])
  (hL : L = ![1.5 * t, 1.5 * t * Real.sqrt 3])
  (hN : N = ![2 * t, t * Real.sqrt 3])
  (hK : K = ![2.5 * t, t * Real.sqrt 3 / 2])
  (hK_prime : K_prime = ![2.5 * t, 1.5 * t * Real.sqrt 3])
  (hP : P = ![3 * t, t * Real.sqrt 3])
  (hB_blue : c B = Color.Blue)
  (hL_blue : c L = Color.Blue) :
  c P = Color.Blue := by
    have hN_red : c N = Color.Red := by
      contrapose! h_blue_t;
      use N, B; simp_all +decide [ dist_eq_norm ];
      norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_two ];
      exact ⟨ by rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ], by cases h : c ![ 2 * t, t * Real.sqrt 3 ] <;> tauto ⟩
    have hK_red : c K = Color.Red := by
      have hK_red : dist K B = t := by
        norm_num [ hB, hK, dist_eq_norm, EuclideanSpace.norm_eq ];
        rw [ Real.sqrt_sq ] <;> linarith;
      exact Or.resolve_left ( by cases h : c K <;> tauto ) fun h => h_blue_t _ _ hK_red ⟨ h, hB_blue ⟩
    have hK_prime_red : c K_prime = Color.Red := by
      have := h_blue_t L K_prime ?_ <;> simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
      · cases h : c ![2.5 * t, 1.5 * t * Real.sqrt 3] <;> tauto;
      · rw [ Real.sqrt_sq_eq_abs, abs_of_nonpos ] <;> linarith;
    contrapose! h_no_red_rhombus with h_no_red_rhombus
    generalize_proofs at *;
    use K, N, P, K_prime
    generalize_proofs at *;
    exact ⟨ by simpa only [ hN, hK, hK_prime, hP ] using lemma_rhombus_KNPK_prime_aux t h_t P N K K_prime hP hN hK hK_prime, hK_red, hN_red, by cases h : c P <;> tauto, hK_prime_red ⟩ ;

/-
If A and B are blue and form a regular t-rhombus with C and D, and no red regular t-rhombus exists, then the circles of radius t*sqrt(3) around C and D are entirely red.
-/
lemma lemma3_case1_deduction (c : Point → Color) (t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_t : t > 0)
  (A B C D : Point)
  (h_rhombus : regular_t_rhombus t A C D B)
  (hA : c A = Color.Blue)
  (hB : c B = Color.Blue)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red) :
  (∀ P, dist P C = t * Real.sqrt 3 → c P = Color.Red) ∧
  (∀ P, dist P D = t * Real.sqrt 3 → c P = Color.Red) := by
    have h_pair_C_D : complementary_pair c C D t := by
      apply_rules [ lemma3_step1 ]
    have h_alt_C : t_alternating c C t t := by
      apply lemma1 c t t C D h_blue h_pair_C_D (by linarith) |>.1
    have h_alt_D : t_alternating c D t t := by
      convert lemma1 c t t C D h_blue h_pair_C_D ( by linarith ) |> And.right using 1;
    apply And.intro;
    · have := lemma2 c t t C h_blue h_alt_C ( by linarith ) ( by linarith );
      convert this using 3 ; ring_nf;
      norm_num [ h_t.le ] ; ring;
    · convert lemma2 c t t D h_blue h_alt_D _ _ using 1;
      · rw [ show 4 * t ^ 2 - t ^ 2 = 3 * t ^ 2 by ring, Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ) ] ; ring_nf;
      · linarith;
      · linarith

/-
Given the configuration and coloring, we derive a contradiction.
-/
lemma lemma3_case1_coloring_contradiction (c : Point → Color) (t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_t : t > 0)
  (A B C D E N G L P : Point)
  (h_rhombus : regular_t_rhombus t A C D B)
  (hA : c A = Color.Blue)
  (hB : c B = Color.Blue)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (h_E : dist E A = t ∧ dist E G = t ∧ dist A G = t * Real.sqrt 3)
  (h_N : dist N L = t ∧ dist N P = t ∧ dist L P = t * Real.sqrt 3)
  (h_sym : N = 2 • C - E)
  (h_dist_NC : dist N C = t * Real.sqrt 3)
  (hG : c G = Color.Blue)
  (hL : c L = Color.Blue)
  (hP : c P = Color.Blue) :
  False := by
    have h_gamma_E_red : ∀ X, dist X E = t * Real.sqrt 3 → c X = Color.Red := by
      apply blue_pair_implies_red_circle c t h_blue h_t A G E h_E.2.2 hA hG h_E.1 h_E.2.1 h_no_red_rhombus
    have h_gamma_N_red : ∀ X, dist X N = t * Real.sqrt 3 → c X = Color.Red := by
      apply blue_pair_implies_red_circle c t h_blue h_t L P N h_N.2.2 hL hP h_N.1 h_N.2.1 h_no_red_rhombus
    have h_pair : complementary_pair c C D t := by
      apply lemma3_step1 c t h_blue h_t A B C D h_rhombus hA hB h_no_red_rhombus
    have h_alt : t_alternating c C t t := by
      have h_r : t ≥ t / 2 := by linarith
      exact (lemma1 c t t C D h_blue h_pair h_r).1
    apply lemma3_case1_helper c t h_t C E N h_sym h_dist_NC h_gamma_N_red h_gamma_E_red h_alt

/-
Definition of the sequence r_n used in the proof of Case 3. Note that r_seq n corresponds to r_{n+1} in the text.
-/
def r_seq : ℕ → ℝ
| 0 => 1
| (n + 1) => (Real.sqrt (4 * (r_seq n)^2 - 1) + Real.sqrt 3) / 2

/-
Definition of a red circle: all points on the circle are red.
-/
def is_red_circle (c : Point → Color) (O : Point) (r : ℝ) : Prop :=
  ∀ P : Point, dist P O = r → c P = Color.Red

/-
The sequence r_n is always at least 1.
-/
lemma lemma_r_seq_ge_1 (n : ℕ)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2) :
  r_seq n ≥ 1 := by
    induction' n with n ih;
    · exact le_rfl;
    · rw [ h_r_seq_def ] ; nlinarith [ show Real.sqrt ( 4 * r_seq n ^ 2 - 1 ) ≥ 1 by exact Real.le_sqrt_of_sq_le ( by nlinarith ), show Real.sqrt 3 ≥ 1 by exact Real.le_sqrt_of_sq_le ( by norm_num ) ] ;

/-
If there are no blue points at distance t and no blue points at distance t*sqrt(3), then there exists a red regular t-rhombus.
-/
lemma lemma3_case2 (c : Point → Color) (t : ℝ)
  (h_blue : ∀ P Q, dist P Q = t → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_t : t > 0)
  (h_no_blue_sqrt3 : ∀ P Q, dist P Q = t * Real.sqrt 3 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue)) :
  ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red := by
    contrapose! h_blue;
    have := @lemma3_case2_geom_corrected;
    obtain ⟨O, hO⟩ : ∃ O : Point, c O = Color.Blue := by
      by_cases h_exists_blue : ∃ O : Point, c O = Color.Blue;
      · exact h_exists_blue;
      · -- If there are no blue points, then every point is red.
        have h_all_red : ∀ P : Point, c P = Color.Red := by
          exact fun P => Or.resolve_left ( by cases h : c P <;> tauto ) fun h' => h_exists_blue ⟨ P, h' ⟩;
        specialize this t 0 ( EuclideanSpace.single 0 ( 2 * t ) ) h_t ; simp_all +decide [ dist_eq_norm ];
        linarith;
    -- If there is a red point P on γ_O(2t), then by lemma3_case2_geom_corrected, there exist P1, P2, P3 forming a regular t-rhombus with P.
    by_cases h_red : ∃ P : Point, dist P O = 2 * t ∧ c P = Color.Red;
    · obtain ⟨ P, hP₁, hP₂ ⟩ := h_red;
      obtain ⟨ P1, P2, P3, hP1, hP2, hP3 ⟩ := this t O P h_t ( by simpa [ dist_comm ] using hP₁ );
      specialize h_blue P1 P P3 P2 ; simp_all +decide [ regular_t_rhombus ];
      cases h : c P1 <;> cases h' : c P2 <;> cases h'' : c P3 <;> simp_all +decide only;
      all_goals have := h_no_blue_sqrt3 P1 P2; simp_all +decide [ dist_comm ];
      · specialize this t O P3 h_t ; aesop;
      · specialize h_no_blue_sqrt3 P2 O ; simp_all +decide [ dist_comm ];
      · exact ⟨ P2, P3, by linarith, h', h'' ⟩;
      · exact False.elim (h_no_blue_sqrt3 O P1 hP1 hO h);
      · exact ⟨ P1, P3, by linarith, h, h'' ⟩;
    · -- By Lemma circle_has_chord, for any t > 0 and any circle of radius 2t, there exists a chord AX of length t.
      obtain ⟨X, Y, hXY⟩ : ∃ X Y : Point, dist X O = 2 * t ∧ dist Y O = 2 * t ∧ dist X Y = t := by
        have := @circle_has_chord;
        exact this ( 2 * t ) t O ( by positivity ) ⟨ by positivity, by linarith ⟩;
      exact ⟨ X, Y, hXY.2.2, by_contradiction fun h => h_red ⟨ X, hXY.1, by cases h : c X <;> tauto ⟩, by_contradiction fun h => h_red ⟨ Y, hXY.2.1, by cases h : c Y <;> tauto ⟩ ⟩

/-
Under the Case 1 configuration, the circle around C of radius t*sqrt(3) is entirely red.
-/
lemma lemma_case1_C_red_condition (c : Point → Color) (t : ℝ)
  (h_blue : ∀ P Q, dist P Q = t → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_t : t > 0)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (A B C D : Point)
  (hA : A = ![0, 0])
  (hB : B = ![1.5 * t, t * Real.sqrt 3 / 2])
  (hC : C = ![0.5 * t, t * Real.sqrt 3 / 2])
  (hD : D = ![t, 0])
  (hA_blue : c A = Color.Blue)
  (hB_blue : c B = Color.Blue) :
  ∀ X, dist X C = t * Real.sqrt 3 → c X = Color.Red := by
    intro X hX;
    have := @lemma3_case1_deduction;
    apply (this c t h_blue h_t A B C D _ hA_blue hB_blue h_no_red_rhombus).left X hX;
    constructor <;> norm_num [ *, dist_eq_norm, EuclideanSpace.norm_eq ] <;> ring_nf;
    · rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> norm_num <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ];
    · norm_num [ h_t.le ] ; ring_nf ; norm_num [ h_t.le ]

/-
The specific coordinate configuration satisfies the required geometric properties.
-/
lemma lemma_case1_geometry (t : ℝ) (h_t : t > 0)
  (A B C D E G N L P : Point)
  (hA : A = ![0, 0])
  (hB : B = ![1.5 * t, t * Real.sqrt 3 / 2])
  (hC : C = ![0.5 * t, t * Real.sqrt 3 / 2])
  (hD : D = ![t, 0])
  (hE : E = ![-t, 0])
  (hG : G = ![-1.5 * t, t * Real.sqrt 3 / 2])
  (hN : N = ![2 * t, t * Real.sqrt 3])
  (hL : L = ![1.5 * t, 1.5 * t * Real.sqrt 3])
  (hP : P = ![3 * t, t * Real.sqrt 3]) :
  regular_t_rhombus t A C D B ∧
  dist E A = t ∧ dist E G = t ∧ dist A G = t * Real.sqrt 3 ∧
  dist N L = t ∧ dist N P = t ∧ dist L P = t * Real.sqrt 3 ∧
  N = 2 • C - E ∧
  dist N C = t * Real.sqrt 3 := by
    unfold regular_t_rhombus at *;
    norm_num [ EuclideanSpace.dist_eq, hA, hB, hC, hD, hE, hG, hN, hL, hP ] ; ring_nf ; norm_num [ h_t.le ] ;
    norm_num [ dist_eq_norm ] ; ring_nf ; norm_num [ h_t.le ] ;
    ring_nf;
    norm_num [ ← List.ofFn_inj, h_t.le ] ; ring_nf;
    ext i ; fin_cases i <;> norm_num <;> ring

/-
The specific coordinate configuration leads to a contradiction under the Case 1 assumptions.
-/
lemma lemma_case1_explicit_contradiction (c : Point → Color) (t : ℝ)
  (h_blue : ∀ P Q, dist P Q = t → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_t : t > 0)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (A B C D E F G N L P K O M1 K_prime K_G : Point)
  (hA : A = ![0, 0])
  (hB : B = ![1.5 * t, t * Real.sqrt 3 / 2])
  (hC : C = ![0.5 * t, t * Real.sqrt 3 / 2])
  (hD : D = ![t, 0])
  (hE : E = ![-t, 0])
  (hF : F = ![-0.5 * t, t * Real.sqrt 3 / 2])
  (hG : G = ![-1.5 * t, t * Real.sqrt 3 / 2])
  (hN : N = ![2 * t, t * Real.sqrt 3])
  (hL : L = ![1.5 * t, 1.5 * t * Real.sqrt 3])
  (hP : P = ![3 * t, t * Real.sqrt 3])
  (hK : K = ![2.5 * t, t * Real.sqrt 3 / 2])
  (hO : O = ![0.5 * t, 1.5 * t * Real.sqrt 3])
  (hM1 : M1 = ![1 * t, t * Real.sqrt 3])
  (hK_prime : K_prime = ![2.5 * t, 1.5 * t * Real.sqrt 3])
  (hK_G : K_G = ![-1 * t, t * Real.sqrt 3])
  (hA_blue : c A = Color.Blue)
  (hB_blue : c B = Color.Blue) :
  False := by
    -- Apply the lemma_case1_geometry to establish the geometric properties of the points and the distances.
    obtain ⟨h_dist_C_red, h_dist_C_red_cases⟩ : regular_t_rhombus t A C D B ∧
      dist E A = t ∧ dist E G = t ∧ dist A G = t * Real.sqrt 3 ∧
      dist N L = t ∧ dist N P = t ∧ dist L P = t * Real.sqrt 3 ∧
      N = 2 • C - E ∧
      dist N C = t * Real.sqrt 3 := by
        apply lemma_case1_geometry t h_t A B C D E G N L P hA hB hC hD hE hG hN hL hP;
    apply lemma3_case1_coloring_contradiction c t;
    exact fun A B a => h_blue A B a;
    exact h_t;
    exact h_dist_C_red;
    all_goals norm_num [ hA_blue, hB_blue ];
    grind;
    exact ⟨ h_dist_C_red_cases.1, h_dist_C_red_cases.2.1, h_dist_C_red_cases.2.2.1 ⟩;
    exact ⟨ h_dist_C_red_cases.2.2.2.1, h_dist_C_red_cases.2.2.2.2.1, h_dist_C_red_cases.2.2.2.2.2.1 ⟩;
    · exact h_dist_C_red_cases.2.2.2.2.2.2.1;
    · exact h_dist_C_red_cases.2.2.2.2.2.2.2;
    · apply_rules [ lemma_G_blue ];
      apply_rules [ lemma_case1_C_red_condition ];
    · apply_rules [ lemma_L_blue ];
      apply_rules [ lemma_case1_C_red_condition ];
    · apply lemma_P_blue_aux;
      exact h_t;
      exact h_blue;
      exact h_no_red_rhombus;
      exact hB;
      exact hL;
      exact hN;
      exact hK;
      exact hK_prime;
      · exact hP;
      · exact hB_blue;
      · apply lemma_L_blue;
        exact h_t;
        exact h_blue;
        exact h_no_red_rhombus;
        exact hB;
        exact hC;
        exact hL;
        exact hM1;
        exact hN;
        exact hO;
        · exact hB_blue;
        · apply lemma_case1_C_red_condition c t h_blue h_t h_no_red_rhombus A B C D hA hB hC hD hA_blue hB_blue

/-
If there exist two blue points at distance t*sqrt(3), and no red regular t-rhombus exists, then we have a contradiction.
-/
lemma lemma3_case1_complete (c : Point → Color) (t : ℝ)
  (h_blue : ∀ P Q, dist P Q = t → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_t : t > 0)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (A B : Point)
  (h_dist : dist A B = t * Real.sqrt 3)
  (hA : c A = Color.Blue)
  (hB : c B = Color.Blue) :
  False := by
    -- Let's choose any two points $A$ and $B$ such that $\|A - B\| = t\sqrt{3}$ and both $A$ and $B$ are blue.
    obtain ⟨f, hf⟩ : ∃ f : Point ≃ᵃⁱ[ℝ] Point, f 0 = A ∧ f (EuclideanSpace.single 0 (3 * t / 2) + EuclideanSpace.single 1 (t * Real.sqrt 3 / 2)) = B := by
      -- Let's choose any two points $A$ and $B$ such that $\|A - B\| = t\sqrt{3}$ and both $A$ and $B$ are blue. We can construct an isometry $f$ that maps $0$ to $A$ and $B_{can}$ to $B$.
      obtain ⟨f, hf⟩ : ∃ f : Point ≃ᵃⁱ[ℝ] Point, f 0 = 0 ∧ f (EuclideanSpace.single 0 (3 * t / 2) + EuclideanSpace.single 1 (t * Real.sqrt 3 / 2)) = B - A := by
        have h_isometry : ∀ (v w : Point), ‖v‖ = ‖w‖ → ∃ f : Point ≃ₗᵢ[ℝ] Point, f v = w := by
          intros v w hvw
          have h_exists_isometry : ∃ f : ℂ ≃ₗᵢ[ℝ] ℂ, f (v 0 + v 1 * Complex.I) = w 0 + w 1 * Complex.I := by
            have h_exists_isometry : ∀ (z w : ℂ), ‖z‖ = ‖w‖ → ∃ f : ℂ ≃ₗᵢ[ℝ] ℂ, f z = w := by
              intros z w hvw
              by_cases hz : z = 0;
              · simp_all +decide;
                rw [ eq_comm, norm_eq_zero ] at hvw ; aesop;
              · -- Since $z \neq 0$, we can construct a linear isometry $f$ that maps $z$ to $w$ by rotating $z$ to $w$.
                obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, w = z * Complex.exp (θ * Complex.I) := by
                  rw [ ← Complex.norm_mul_exp_arg_mul_I z, ← Complex.norm_mul_exp_arg_mul_I w ];
                  exact ⟨ w.arg - z.arg, by push_cast [ hvw ] ; rw [ mul_assoc, ← Complex.exp_add ] ; ring_nf ⟩;
                refine' ⟨ _, _ ⟩;
                refine' { Equiv.ofBijective ( fun x => x * Complex.exp ( θ * Complex.I ) ) ⟨ fun x y hxy => _, fun x => _ ⟩ with .. } <;> norm_num [ Complex.exp_ne_zero ] at *;
                all_goals norm_num [ mul_assoc, hθ ];
                · exact hxy;
                · exact ⟨ x / Complex.exp ( θ * Complex.I ), div_mul_cancel₀ _ ( Complex.exp_ne_zero _ ) ⟩;
                · exact fun x y => by ring;
            apply h_exists_isometry;
            convert hvw using 1 <;> norm_num [ EuclideanSpace.norm_eq ];
            · norm_num [ Complex.normSq, Complex.norm_def, sq ];
            · norm_num [ Complex.normSq, Complex.norm_def, sq ];
          obtain ⟨ f, hf ⟩ := h_exists_isometry;
          refine' ⟨ _, _ ⟩;
          refine' { Equiv.ofBijective ( fun x => fun i => if i = 0 then ( f ( x 0 + x 1 * Complex.I ) |> Complex.re ) else ( f ( x 0 + x 1 * Complex.I ) |> Complex.im ) ) ⟨ _, _ ⟩ with .. };
          all_goals norm_num [ Function.Injective, Function.Surjective, EuclideanSpace.norm_eq ] at *;
          all_goals norm_num [ funext_iff, Fin.forall_fin_two ] at *;
          any_goals ext i; fin_cases i <;> simp +decide [ Complex.ext_iff ] at hf ⊢ ; linarith!;
          any_goals linarith;
          · intro a₁ a₂ h₁ h₂; have := f.injective; simp_all +decide [Complex.ext_iff] ;
            have := @this ( a₁ 0 + a₁ 1 * Complex.I ) ( a₂ 0 + a₂ 1 * Complex.I ) ; simp_all +decide [ Complex.ext_iff ] ;
            exact funext fun i => by fin_cases i <;> tauto;
          · intro b;
            obtain ⟨ a, ha ⟩ := f.surjective ( b 0 + b 1 * Complex.I );
            use fun i => if i = 0 then a.re else a.im;
            have := f.map_add ( a.re : ℂ ) ( a.im * Complex.I ) ; simp_all +decide [ Complex.ext_iff ] ;
          · intro x y; ext i; fin_cases i <;> simp +decide [add_mul] ; ring;
            ring;
          · intro m x; ext i; fin_cases i <;> simp +decide [ mul_assoc ] ;
            · have := f.map_smul m ( x 0 : ℂ ) ; have := f.map_smul m ( x 1 * Complex.I ) ; simp_all +decide [ Complex.ext_iff, mul_add ] ;
            · have := f.map_smul m ( x 0 : ℂ ) ; have := f.map_smul m ( x 1 * Complex.I ) ; simp_all +decide [ Complex.ext_iff, mul_add ] ;
          · intro x; have := f.norm_map ( x 0 + x 1 * Complex.I ) ; simp_all +decide [ Complex.normSq, Complex.norm_def ] ;
            simpa only [ sq ] using this;
        obtain ⟨f, hf⟩ : ∃ f : Point ≃ₗᵢ[ℝ] Point, f (EuclideanSpace.single 0 (3 * t / 2) + EuclideanSpace.single 1 (t * Real.sqrt 3 / 2)) = B - A := by
          apply h_isometry;
          norm_num [ EuclideanSpace.norm_eq, dist_eq_norm' ] at *;
          rw [ h_dist ] ; ring_nf ; norm_num ; ring_nf;
          rw [ Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ) ];
        exact ⟨ f.toAffineIsometryEquiv, by simp +decide, hf ⟩;
      refine' ⟨ _, _, _ ⟩;
      refine' f.trans ( _ );
      refine' ⟨ _, _ ⟩;
      exact ( AffineEquiv.constVAdd ℝ ( EuclideanSpace ℝ ( Fin 2 ) ) A );
      all_goals norm_num [ hf ];
    -- By definition of $f$, we know that $c'(x) = c(f(x))$ satisfies the conditions of `lemma_case1_explicit_contradiction`.
    set c' : Point → Color := fun x => c (f x)
    have h_c'_blue : c' 0 = Color.Blue ∧ c' (EuclideanSpace.single 0 (3 * t / 2) + EuclideanSpace.single 1 (t * Real.sqrt 3 / 2)) = Color.Blue := by
      aesop
    have h_c'_no_blue_dist : ∀ P Q, dist P Q = t → ¬ (c' P = Color.Blue ∧ c' Q = Color.Blue) := by
      intros P Q hPQ h_blue_PQ
      apply h_blue (f P) (f Q) (by
      exact f.isometry.dist_eq P Q ▸ hPQ ▸ rfl) h_blue_PQ
    have h_c'_no_red_rhombus : ¬∃ P Q R S, regular_t_rhombus t P Q R S ∧ c' P = Color.Red ∧ c' Q = Color.Red ∧ c' R = Color.Red ∧ c' S = Color.Red := by
      norm_num +zetaDelta at *;
      intro x y z w h₁ h₂ h₃ h₄ h₅; specialize h_no_red_rhombus ( f x ) ( f y ) ( f z ) ( f w ) ; simp_all +decide [ regular_t_rhombus ] ;
    apply lemma_case1_explicit_contradiction c' t h_c'_no_blue_dist h_t h_c'_no_red_rhombus;
    any_goals tauto;
    · convert h_c'_blue.1 using 1;
      exact congr_arg _ ( by ext i; fin_cases i <;> rfl );
    · convert h_c'_blue.2 using 2 ; ext i ; fin_cases i <;> norm_num ; ring

/-
Given two pairs of points with the same distance, there exists an isometry mapping the first pair to the second.
-/
lemma exists_isometry_mapping_pair (A B P Q : Point)
  (h_dist : dist A B = dist P Q) :
  ∃ f : Point ≃ᵃⁱ[ℝ] Point, f A = P ∧ f B = Q := by
    -- Let $v = B - A$ and $w = Q - P$. Since $||v|| = ||w||$, there exists a linear isometry $L$ such that $L(v) = w$.
    obtain ⟨L, hL⟩ : ∃ L : (EuclideanSpace ℝ (Fin 2)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 2)), L (B - A) = Q - P := by
      -- By the properties of the Euclidean space, we can construct such a linear map.
      have h_linear_map : ∃ L : Matrix (Fin 2) (Fin 2) ℝ, L.mulVec (B - A) = Q - P ∧ L.transpose * L = 1 := by
        by_cases h : B - A = 0 <;> by_cases h' : Q - P = 0 <;> simp_all +decide [ dist_eq_norm' ];
        · exact ⟨ 1, by norm_num ⟩;
        · exact False.elim <| h' <| norm_eq_zero.mp h_dist.symm;
        · -- Since $B - A$ and $Q - P$ are non-zero and have the same norm, we can construct a rotation matrix $L$ such that $L(B - A) = Q - P$.
          obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, (Q - P) 0 = (B - A) 0 * Real.cos θ - (B - A) 1 * Real.sin θ ∧ (Q - P) 1 = (B - A) 0 * Real.sin θ + (B - A) 1 * Real.cos θ := by
            have h_rotation : ∃ θ : ℝ, (Q - P) 0 = ‖B - A‖ * Real.cos θ ∧ (Q - P) 1 = ‖B - A‖ * Real.sin θ := by
              use ( Complex.arg ( ( Q - P ) 0 + ( Q - P ) 1 * Complex.I ) );
              rw [ Complex.cos_arg, Complex.sin_arg ] <;> simp_all +decide [ Complex.ext_iff ];
              · norm_num [ Complex.normSq, Complex.norm_def, EuclideanSpace.norm_eq ] at *;
                norm_num [ ← sq, mul_div_cancel₀, Real.sqrt_ne_zero'.mpr ( show 0 < ( Q 0 - P 0 ) ^ 2 + ( Q 1 - P 1 ) ^ 2 from not_le.mp fun h'' => h' <| by ext i; fin_cases i <;> norm_num <;> nlinarith! ) ];
              · exact fun h₀ h₁ => h' <| by ext i; fin_cases i <;> simp +decide [ h₀, h₁ ] ;
            obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, (B - A) 0 = ‖B - A‖ * Real.cos θ ∧ (B - A) 1 = ‖B - A‖ * Real.sin θ := by
              use ( Complex.arg ( ( B - A ) 0 + ( B - A ) 1 * Complex.I ) );
              rw [ Complex.cos_arg, Complex.sin_arg ] <;> norm_num [ Complex.ext_iff, h ];
              · norm_num [ Complex.normSq, Complex.norm_def, EuclideanSpace.norm_eq ];
                norm_num [ ← sq, mul_div_cancel₀ _ ( ne_of_gt ( Real.sqrt_pos.mpr ( show 0 < ( B 0 - A 0 ) ^ 2 + ( B 1 - A 1 ) ^ 2 from not_le.mp fun h'' => h <| by ext i; fin_cases i <;> norm_num <;> nlinarith! ) ) ) ];
              · exact fun h₀ h₁ => h <| by ext i; fin_cases i <;> aesop;
            obtain ⟨ θ', hθ' ⟩ := h_rotation; use θ' - θ; simp_all +decide [ Real.sin_sub, Real.cos_sub ] ; ring_nf;
            exact ⟨ by rw [ Real.cos_sq' ] ; ring, by rw [ Real.cos_sq' ] ; ring ⟩;
          refine' ⟨ Matrix.of fun i j => if i = 0 then if j = 0 then Real.cos θ else -Real.sin θ else if j = 0 then Real.sin θ else Real.cos θ, _, _ ⟩ <;> simp_all +decide [ ← List.ofFn_inj, Matrix.mulVec ];
          · constructor <;> ring;
          · ext i j; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Matrix.transpose_apply ] <;> ring_nf <;> norm_num [ Real.sin_sq, Real.cos_sq ] ;
      obtain ⟨ L, hL₁, hL₂ ⟩ := h_linear_map;
      refine' ⟨ _, _ ⟩;
      refine' { Equiv.ofBijective ( fun x => L.mulVec x ) ⟨ fun x y hxy => _, fun x => _ ⟩ with .. };
      all_goals simp_all +decide [ EuclideanSpace.norm_eq ];
      · apply_fun L.transpose.mulVec at hxy ; simp_all +decide;
      · exact ⟨ L⁻¹.mulVec x, by simp +decide [isUnit_iff_ne_zero,
        show L.det ≠ 0 from fun h => by simpa [h] using congr_arg Matrix.det hL₂] ⟩;
      · exact fun x y => Matrix.mulVec_add _ _ _;
      · exact fun m x => by rw [ Matrix.mulVec_smul ] ;
      · intro x; rw [ ← Matrix.ext_iff ] at *; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
        simp_all +decide [ Matrix.mul_apply, Fin.sum_univ_two ];
        exact congrArg Real.sqrt ( by linear_combination' hL₂.1.1 * x 0 ^ 2 + hL₂.1.2 * x 0 * x 1 + hL₂.2.1 * x 0 * x 1 + hL₂.2.2 * x 1 ^ 2 );
    refine' ⟨ _, _, _ ⟩;
    refine' { Equiv.ofBijective ( fun x => L ( x - A ) + P ) ⟨ fun x y hxy => _, fun x => _ ⟩ with .. } <;> norm_num;
    any_goals intro x; simp +decide [ add_sub, sub_add ];
    any_goals intro v; exact L.norm_map v;
    all_goals simp_all +decide [ sub_eq_iff_eq_add ];
    exact ⟨ L.symm ( x - P + L A ), by simp +decide ⟩

/-
Given any coloring without blue points of distance t, there exists a red regular t-rhombus.
-/
lemma lemma3 (c : Point → Color) (t : ℝ)
  (h_blue : ∀ P Q, dist P Q = t → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_t : t > 0) :
  ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red := by
    by_contra h_contra;
    have h_no_blue_sqrt3 : ∀ P Q, dist P Q = t * Real.sqrt 3 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue) := by
      intro P Q hPQ h_blue_PQ
      apply lemma3_case1_complete c t h_blue h_t h_contra P Q hPQ h_blue_PQ.left h_blue_PQ.right;
    exact h_contra <| lemma3_case2 c t h_blue h_t h_no_blue_sqrt3

def has_blue_dist (c : Point → Color) (d : ℝ) : Prop :=
  ∃ P Q, c P = Color.Blue ∧ c Q = Color.Blue ∧ dist P Q = d

def segments_bisect (A B C D : Point) : Prop :=
  midpoint ℝ A B = midpoint ℝ C D

def Case1 (c : Point → Color) (cfg : Fin 4 → Point) : Prop :=
  ∃ i j k l, {i, j, k, l} = ({0, 1, 2, 3} : Finset (Fin 4)) ∧
    segments_bisect (cfg i) (cfg j) (cfg k) (cfg l) ∧
    ¬ has_blue_dist c (dist (cfg i) (cfg k)) ∧
    ¬ has_blue_dist c (dist (cfg i) (cfg l))

def Case2 (c : Point → Color) (cfg : Fin 4 → Point) : Prop :=
  ∀ i j, i ≠ j → ¬ has_blue_dist c (dist (cfg i) (cfg j))

def Case3 (c : Point → Color) (cfg : Fin 4 → Point) : Prop :=
  ∃ i j k l, {i, j, k, l} = ({0, 1, 2, 3} : Finset (Fin 4)) ∧
    has_blue_dist c (dist (cfg i) (cfg j)) ∧
    ¬ segments_bisect (cfg i) (cfg j) (cfg k) (cfg l)

lemma lemma_cases_exhaustive (c : Point → Color) (cfg : Fin 4 → Point)
  (h_distinct : Function.Injective cfg) :
  Case1 c cfg ∨ Case2 c cfg ∨ Case3 c cfg := by
    by_cases h_case2 : ∀ i j, i ≠ j → ¬has_blue_dist c ( dist ( cfg i ) ( cfg j ) );
    · exact Or.inr <| Or.inl h_case2;
    · obtain ⟨i, j, hij, h_blue⟩ : ∃ i j, i ≠ j ∧ has_blue_dist c (dist (cfg i) (cfg j)) := by
        aesop;
      obtain ⟨k, l, hk⟩ : ∃ k l, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ {i, j, k, l} = ({0, 1, 2, 3} : Finset (Fin 4)) := by
        fin_cases i <;> fin_cases j <;> simp +decide at hij ⊢;
      by_cases h_bisect : segments_bisect (cfg i) (cfg j) (cfg k) (cfg l);
      · by_cases h_bisect_ik : has_blue_dist c (dist (cfg i) (cfg k));
        · by_cases h_bisect_ik : segments_bisect (cfg i) (cfg k) (cfg j) (cfg l);
          · simp_all +decide [ segments_bisect, midpoint ];
            exact False.elim <| hk.2.2.1 <| h_distinct <| by ext x; have := congr_fun h_bisect x; have := congr_fun h_bisect_ik x; norm_num [ AffineMap.lineMap_apply ] at *; linarith;
          · right;
            right;
            use i, k, j, l;
            grind;
        · by_cases h_bisect_il : has_blue_dist c (dist (cfg i) (cfg l));
          · refine Or.inr <| Or.inr <| ⟨ i, l, j, k, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ segments_bisect ];
            · grind;
            · intro h; simp_all +decide [ midpoint_eq_smul_add ] ;
              -- Subtracting the two equations h_bisect and h, we get cfg j - cfg l = cfg l - cfg j, which simplifies to 2*cfg j = 2*cfg l, hence cfg j = cfg l.
              have h_eq : cfg j = cfg l := by
                ext x; have := congr_fun h_bisect x; have := congr_fun h x; norm_num at *; linarith;
              exact absurd ( h_distinct h_eq ) ( by aesop );
          · exact Or.inl ⟨ i, j, k, l, by aesop ⟩;
      · exact Or.inr <| Or.inr <| ⟨ i, j, k, l, by aesop ⟩

lemma lemma_case1_Y_blue (c : Point → Color) (a : ℝ) (P Q R S X Y : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (h_parallelogram : X - P = Y - Q)
  (h_dist_PQ : dist P Q = a)
  (h_dist_XY : dist X Y = a)
  (h_blue_Y : c Y = Color.Blue)
  (h_no_blue_a : ∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_red_rhombus : c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (h_a : a > 0) :
  ∃ P' Q' R' S', Congruent (fun i : Fin 4 => ![P, Q, Y, X] i) (fun i => ![P', Q', R', S'] i) ∧
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red := by
      -- By translating the configuration by the vector v = S - P, we map X to Z and Y to V. Since Y is blue, Z and V must be red.
      have h_translation : ∃ f : Point ≃ᵃⁱ[ℝ] Point, f P = S ∧ f Q = R ∧ f Y = (S - P) + Y ∧ f X = (S - P) + X := by
        obtain ⟨v, hv⟩ : ∃ v : Point, R = Q + v ∧ S = P + v := by
          obtain ⟨h₁, h₂, h₃, h₄⟩ := h_rhombus;
          use S - P;
          simp_all +decide [ dist_eq_norm', EuclideanSpace.norm_eq ];
          rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> try linarith;
          rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> try linarith;
          rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at h₄ <;> try linarith;
          rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at h₄ <;> ring_nf at * <;> norm_num at *;
          · ext i; fin_cases i <;> norm_num <;> nlinarith! only [ h₄, h₃, h₂, h_dist_PQ, h_dist_XY, h_a, sq_nonneg ( R 0 - Q 0 - ( S 0 - P 0 ) ), sq_nonneg ( R 1 - Q 1 - ( S 1 - P 1 ) ) ] ;
          · positivity;
        use (AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 2)) v);
        simp_all +decide [add_comm, add_assoc, sub_eq_add_neg];
      obtain ⟨ f, hfP, hfQ, hfY, hfX ⟩ := h_translation; use S, R, ( S - P ) + Y, ( S - P ) + X; simp_all +decide [ Congruent ] ;
      refine' ⟨ _, _, _ ⟩;
      · simp +decide [← hfP, ← hfQ, edist_dist];
        simp +decide [ Fin.forall_fin_succ, dist_eq_norm ];
        -- Since $f$ is an isometry, it preserves distances. Therefore, the norms of the differences between the points and their images under $f$ are equal.
        have h_isometry : ∀ A B : Point, ‖f A - f B‖ = ‖A - B‖ := by
          intro A B; exact (by
          convert f.isometry.dist_eq A B using 1);
        grind;
      · have h_dist_eq : dist (S - P + Y) Y = a := by
          cases h_rhombus ; aesop;
        cases h : c ( S - P + Y ) <;> tauto;
      · contrapose! h_no_blue_a;
        use Y, S - P + X;
        unfold regular_t_rhombus at h_rhombus; unfold dist at *; simp_all +decide [ sub_eq_iff_eq_add ] ;
        simp_all +decide [ PiLp.instDist, dist_eq_norm ];
        exact ⟨ by ring_nf at *; linarith, by cases h : c ( S + ( Y - Q ) ) <;> aesop ⟩

lemma lemma_rhombus_properties (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q S R) :
  S - P = R - Q ∧ dist Q S = a := by
    obtain ⟨ hPQ, hPS, hQS, hRS, hPR ⟩ := h_rhombus;
    -- By definition of distance, we know that ‖P - Q‖ = a, ‖Q - S‖ = a, ‖S - P‖ = a, ‖Q - R‖ = a, and ‖R - S‖ = a.
    have h_dist_eq : ‖P - Q‖^2 = a^2 ∧ ‖Q - S‖^2 = a^2 ∧ ‖S - P‖^2 = a^2 ∧ ‖Q - R‖^2 = a^2 ∧ ‖R - S‖^2 = a^2 ∧ ‖P - R‖^2 = (a * Real.sqrt 3)^2 := by
      aesop;
    norm_num [ EuclideanSpace.norm_eq, dist_eq_norm ] at *;
    norm_num [ mul_pow, Real.sq_sqrt ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ] at *;
    -- By combining the equations from h_dist_eq, we can derive that S - P = R - Q.
    have h_eq : (S 0 - P 0) = (R 0 - Q 0) ∧ (S 1 - P 1) = (R 1 - Q 1) := by
      constructor <;> nlinarith only [ h_dist_eq, sq_nonneg ( S 0 - P 0 - ( R 0 - Q 0 ) ), sq_nonneg ( S 1 - P 1 - ( R 1 - Q 1 ) ) ];
    exact ⟨ by ext i; fin_cases i <;> tauto, hPS ⟩

def rotate_point (theta : ℝ) (P : Point) : Point :=
  ![P 0 * Real.cos theta - P 1 * Real.sin theta, P 0 * Real.sin theta + P 1 * Real.cos theta]

def rotate_around (C : Point) (theta : ℝ) (P : Point) : Point :=
  C + rotate_point theta (P - C)

lemma rotate_around_isometry (C : Point) (theta : ℝ) :
  Isometry (rotate_around C theta) := by
    refine' Isometry.of_dist_eq fun P Q => _;
    -- By definition of rotation, we have that the distance between the rotated points is the same as the distance between the original points.
    simp [rotate_around, dist_eq_norm];
    unfold rotate_point;
    norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_two ];
    exact congrArg Real.sqrt ( by nlinarith [ Real.sin_sq_add_cos_sq theta ] )

lemma lemma_rhombus_rotation (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (h_a : a > 0) :
  ∃ theta : ℝ, (theta = Real.pi / 3 ∨ theta = -Real.pi / 3) ∧
    rotate_around P theta Q = S := by
      obtain ⟨h_dist_PQ, h_dist_PQ_S, h_dist_PS⟩ := h_rhombus;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
      -- By the properties of the rotation and the given distances, we can conclude that either rotating Q by π/3 or -π/3 around P will result in S.
      have h_rotation : (S 0 - P 0) = (Q 0 - P 0) * Real.cos (Real.pi / 3) - (Q 1 - P 1) * Real.sin (Real.pi / 3) ∧ (S 1 - P 1) = (Q 0 - P 0) * Real.sin (Real.pi / 3) + (Q 1 - P 1) * Real.cos (Real.pi / 3) ∨ (S 0 - P 0) = (Q 0 - P 0) * Real.cos (-Real.pi / 3) - (Q 1 - P 1) * Real.sin (-Real.pi / 3) ∧ (S 1 - P 1) = (Q 0 - P 0) * Real.sin (-Real.pi / 3) + (Q 1 - P 1) * Real.cos (-Real.pi / 3) := by
        norm_num [ neg_div, Real.sin_pi_div_three, Real.cos_pi_div_three ] at *;
        rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> try linarith;
        by_cases h_case : S 0 - P 0 = (Q 0 - P 0) * (1 / 2) - (Q 1 - P 1) * (Real.sqrt 3 / 2);
        · grind;
        · by_cases h_case2 : S 0 - P 0 = (Q 0 - P 0) * (1 / 2) + (Q 1 - P 1) * (Real.sqrt 3 / 2);
          · grind;
          · exact False.elim <| h_case <| mul_left_cancel₀ ( sub_ne_zero_of_ne h_case2 ) <| by ring_nf; norm_num; nlinarith;
      unfold rotate_around;
      unfold rotate_point; norm_num [ neg_div ] at *;
      exact Or.imp ( fun h => by ext i; fin_cases i <;> norm_num <;> linarith! ) ( fun h => by ext i; fin_cases i <;> norm_num <;> linarith! ) h_rotation

lemma lemma_case1_X_blue (c : Point → Color) (a b : ℝ) (P Q R S X Y : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (h_parallelogram : X - P = Y - Q)
  (h_dist_PQ : dist P Q = a)
  (h_dist_PX : dist P X = b)
  (h_blue_X : c X = Color.Blue)
  (h_no_blue_b : ∀ A B, dist A B = b → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_red_rhombus : c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (h_a : a > 0)
  (h_b : b > 0)
  (h_case1_Y_blue : ∀ (P' Q' R' S' X' Y' : Point),
    regular_t_rhombus a P' Q' S' R' →
    X' - P' = Y' - Q' →
    dist P' Q' = a →
    dist X' Y' = a →
    c Y' = Color.Blue →
    (∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue)) →
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red →
    ∃ P'' Q'' R'' S'', Congruent (fun i : Fin 4 => ![P', Q', Y', X'] i) (fun i => ![P'', Q'', R'', S''] i) ∧
      c P'' = Color.Red ∧ c Q'' = Color.Red ∧ c R'' = Color.Red ∧ c S'' = Color.Red)
  (h_no_blue_a : ∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue)) :
  ∃ P' Q' R' S', Congruent (fun i : Fin 4 => ![P, Q, Y, X] i) (fun i => ![P', Q', R', S'] i) ∧
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red := by
      obtain ⟨theta, htheta⟩ : ∃ theta : ℝ, (theta = Real.pi / 3 ∨ theta = -Real.pi / 3) ∧ rotate_around P theta Q = S := by
        exact lemma_rhombus_rotation a P Q R S h_rhombus h_a
      generalize_proofs at *; (
      obtain ⟨htheta1, htheta2⟩ := htheta;
      set X' := rotate_around P theta X;
      set Y' := rotate_around P theta Y;
      have h_dist_XY' : dist X' Y' = a := by
        have h_dist_XY' : dist X' Y' = dist X Y := by
          convert dist_eq_norm ( X' - Y' ) using 1 ; ring_nf!;
          exact iff_of_true ( by simpa [ dist_eq_norm ] using ( rotate_around_isometry P theta |> Isometry.dist_eq ) X Y ) fun b => by simp +decide [ dist_eq_norm ] ;
        generalize_proofs at *; (
        have h_dist_XY : dist X Y = dist P Q := by
          rw [ show X = P + ( Y - Q ) by ext i; have := congr_fun h_parallelogram i; norm_num at *; linarith, dist_eq_norm, dist_eq_norm ] ; norm_num [ EuclideanSpace.norm_eq ] ; ring_nf
        generalize_proofs at *; (
        rw [h_dist_XY', h_dist_XY, h_dist_PQ]));
      have h_dist_X'X : dist X' X = b := by
        have h_dist_X'X : dist X' X = dist (X - P) (rotate_point theta (X - P)) := by
          simp +zetaDelta at *;
          unfold rotate_around; simp +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf;
        generalize_proofs at *; (
        rcases htheta1 with ( rfl | rfl ) <;> norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
        · rw [ h_dist_X'X, ← h_dist_PX ] ; ring_nf; norm_num [ Real.sin_pi_div_three, Real.cos_pi_div_three ] ; ring_nf;
          unfold rotate_point; norm_num [ mul_div ] ; ring_nf;
          norm_num ; ring_nf;
        · rw [ h_dist_X'X, h_dist_PX.symm ] ; norm_num [ neg_div, rotate_point ] ; ring_nf;
          norm_num ; ring_nf);
      have h_congruent : Congruent (fun i => ![P, Q, Y, X] i) (fun i => ![P, S, Y', X'] i) := by
        have h_congruent : ∀ i j : Fin 4, dist ( ![P, Q, Y, X] i ) ( ![P, Q, Y, X] j ) = dist ( ![P, S, Y', X'] i ) ( ![P, S, Y', X'] j ) := by
          have h_congruent : Isometry (rotate_around P theta) := by
            exact rotate_around_isometry P theta
          generalize_proofs at *; (
          intro i j; fin_cases i <;> fin_cases j <;> simp +decide [← htheta2] ;
          all_goals rw [ ← h_congruent.dist_eq ] ;
          all_goals unfold rotate_around; norm_num [ dist_eq_norm ] ;
          all_goals unfold rotate_point; norm_num [ EuclideanSpace.norm_eq ] ;
          · ring_nf;
          · unfold Y'; norm_num [ rotate_around ] ; ring_nf;
            unfold rotate_point; norm_num; ring_nf;
          · unfold X'; norm_num [ rotate_around ] ; ring_nf;
            unfold rotate_point; norm_num; ring_nf;
          · field_simp;
            unfold Y'; norm_num [ rotate_around, rotate_point ] ; ring_nf;
          · unfold X'; norm_num [ rotate_around ] ; ring_nf;
            unfold rotate_point; norm_num; ring_nf;)
        generalize_proofs at *; (
        simp +decide [ Fin.forall_fin_succ, Congruent ] at h_congruent ⊢;
        simp_all +decide [ edist_dist ]);
      have h_red_X' : c X' = Color.Red := by
        cases h' : c X' <;> tauto;
      by_cases h_blue_Y' : c Y' = Color.Blue;
      · obtain ⟨ P'', Q'', R'', S'', h_congruent'', h_red'' ⟩ := h_case1_Y_blue P S R Q X' Y' ( by
          unfold regular_t_rhombus at *; simp_all +decide [ dist_eq_norm', EuclideanSpace.norm_eq ] ;
          grind +ring ) ( by
          rw [ ← htheta2 ];
          simp +zetaDelta at *;
          convert congr_arg ( fun v => rotate_point theta v ) h_parallelogram using 1 <;> norm_num [ rotate_point, rotate_around ] ; ring_nf;
          ext i; fin_cases i <;> norm_num <;> ring; ) ( by
          convert h_rhombus.2.2.1 using 1;
          exact dist_comm _ _ ) ( by
          exact h_dist_XY' ) h_blue_Y' h_no_blue_a ( by
          tauto ) ; use P'', Q'', R'', S'' ; (
        exact ⟨ h_congruent.trans h_congruent'', h_red'' ⟩);
      · use P, S, Y', X';
        cases h : c Y' <;> tauto)

lemma lemma_case1_X_blue_v2 (c : Point → Color) (a b : ℝ) (P Q R S X Y : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (h_parallelogram : X - P = Y - Q)
  (h_dist_PQ : dist P Q = a)
  (h_dist_PX : dist P X = b)
  (h_blue_X : c X = Color.Blue)
  (h_no_blue_b : ∀ A B, dist A B = b → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_red_rhombus : c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (h_a : a > 0)
  (h_b : b > 0)
  (h_case1_Y_blue : ∀ (P' Q' R' S' X' Y' : Point),
    regular_t_rhombus a P' Q' S' R' →
    X' - P' = Y' - Q' →
    dist P' Q' = a →
    dist X' Y' = a →
    c Y' = Color.Blue →
    (∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue)) →
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red →
    ∃ P'' Q'' R'' S'', Congruent (fun i : Fin 4 => ![P', Q', Y', X'] i) (fun i => ![P'', Q'', R'', S''] i) ∧
      c P'' = Color.Red ∧ c Q'' = Color.Red ∧ c R'' = Color.Red ∧ c S'' = Color.Red)
  (h_no_blue_a : ∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue)) :
  ∃ P' Q' R' S', Congruent (fun i : Fin 4 => ![P, Q, Y, X] i) (fun i => ![P', Q', R', S'] i) ∧
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red := by
      -- Apply `lemma_case1_X_blue` to the configuration `{P, Q, Y, X}` and the regular t-rhombus `{P, Q, S, R}`.
      apply lemma_case1_X_blue c a b P Q R S X Y h_rhombus h_parallelogram h_dist_PQ h_dist_PX h_blue_X h_no_blue_b h_red_rhombus h_a h_b (by
      exact h_case1_Y_blue) h_no_blue_a

lemma lemma_case1_X_blue_v3 (c : Point → Color) (a b : ℝ) (P Q R S X Y : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (h_parallelogram : X - P = Y - Q)
  (h_dist_PQ : dist P Q = a)
  (h_dist_PX : dist P X = b)
  (h_blue_X : c X = Color.Blue)
  (h_no_blue_b : ∀ A B, dist A B = b → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_red_rhombus : c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (h_a : a > 0)
  (h_b : b > 0)
  (h_no_blue_a : ∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue)) :
  ∃ P' Q' R' S', Congruent (fun i : Fin 4 => ![P, Q, Y, X] i) (fun i => ![P', Q', R', S'] i) ∧
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red := by
      have := @lemma_case1_X_blue_v2 c a b P Q R S X Y h_rhombus h_parallelogram h_dist_PQ h_dist_PX h_blue_X h_no_blue_b h_red_rhombus h_a h_b ?_ h_no_blue_a;
      · exact this;
      · intros P' Q' R' S' X' Y' h_rhombus' h_parallelogram' h_dist_PQ' h_dist_XY' h_blue_Y' h_no_blue_a' h_red_rhombus';
        apply_rules [ lemma_case1_Y_blue ]

lemma lemma_case1_geometric_step (c : Point → Color) (a b : ℝ) (P Q X Y : Point)
  (h_parallelogram : X - P = Y - Q)
  (h_dist_PQ : dist P Q = a)
  (h_dist_PX : dist P X = b)
  (h_no_blue_a : ∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_blue_b : ∀ A B, dist A B = b → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_rhombus : ∃ P_r Q_r R_r S_r, regular_t_rhombus a P_r Q_r S_r R_r ∧ c P_r = Color.Red ∧ c Q_r = Color.Red ∧ c R_r = Color.Red ∧ c S_r = Color.Red)
  (h_a : a > 0)
  (h_b : b > 0) :
  ∃ P' Q' Y' X', Congruent (fun i : Fin 4 => ![P, Q, Y, X] i) (fun i => ![P', Q', Y', X'] i) ∧
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c Y' = Color.Red ∧ c X' = Color.Red := by
      revert h_rhombus;
      intro h_rhombus
      obtain ⟨P_r, Q_r, R_r, S_r, h_rhombus_def, h_rhombus_red⟩ := h_rhombus;
      -- Apply `exists_isometry_mapping_pair` to find an isometry `f` such that `f P = P_r` and `f Q = Q_r`.
      obtain ⟨f, hf⟩ : ∃ f : Point ≃ᵃⁱ[ℝ] Point, f P = P_r ∧ f Q = Q_r := by
        apply exists_isometry_mapping_pair;
        cases h_rhombus_def ; aesop;
      by_cases hY : c ( f Y ) = Color.Blue;
      · have h_case1_Y_blue : ∃ P' Q' R' S', Congruent (fun i : Fin 4 => ![P_r, Q_r, f Y, f X] i) (fun i => ![P', Q', R', S'] i) ∧ c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red := by
          apply lemma_case1_Y_blue;
          any_goals tauto;
          · have h_affine : ∀ (v w : Point), f (v + w) = f v + f w - f 0 := by
              intro v w; exact (by
              have h_affine : ∀ (v w : Point), f (v + w) = f v + f w - f 0 := by
                intro v w
                have h_linear : ∀ (v w : Point), f (v + w) - f 0 = (f v - f 0) + (f w - f 0) := by
                  intro v w; exact (by
                  have h_linear : ∀ (v w : Point), f (v + w) - f 0 = (f v - f 0) + (f w - f 0) := by
                    intro v w
                    have h_linear_map : ∃ L : Point →ₗ[ℝ] Point, ∀ v, f v = L v + f 0 := by
                      use f.linear;
                      intro v; exact (by
                      convert f.map_vadd 0 v using 1 ; norm_num)
                    obtain ⟨ L, hL ⟩ := h_linear_map; simp +decide [ hL v, hL w, hL ( v + w ) ] ;
                  exact h_linear v w)
                exact eq_of_sub_eq_zero ( by ext i; have := congr_fun ( h_linear v w ) i; norm_num at *; linarith );
              exact h_affine v w);
            have := h_affine ( X - P ) P; have := h_affine ( Y - Q ) Q; simp_all +decide [ sub_eq_iff_eq_add ] ;
            abel1;
          · exact hf.1 ▸ hf.2 ▸ by simpa using h_dist_PQ;
          · have h_dist_XY : dist (f X) (f Y) = dist X Y := by
              exact f.isometry.dist_eq _ _;
            have h_dist_XY : dist X Y = dist P Q := by
              rw [ dist_eq_norm, dist_eq_norm ];
              rw [ show X - Y = P - Q by ext i; have := congr_fun h_parallelogram i; norm_num at *; linarith ];
            grind;
        obtain ⟨ P', Q', R', S', h₁, h₂, h₃, h₄, h₅ ⟩ := h_case1_Y_blue; use P', Q', R', S'; simp_all +decide [ Congruent ] ;
        intro i₁ i₂; specialize h₁ i₁ i₂; simp_all +decide [ edist_dist ] ;
        fin_cases i₁ <;> fin_cases i₂ <;> simp_all +decide [ dist_comm ];
        all_goals have := f.isometry.dist_eq P Q; have := f.isometry.dist_eq P X; have := f.isometry.dist_eq Q X; have := f.isometry.dist_eq P Y; have := f.isometry.dist_eq Q Y; have := f.isometry.dist_eq X Y; simp_all +decide [ dist_eq_norm ] ;
      · by_cases hX : c ( f X ) = Color.Blue;
        · -- Apply `lemma_case1_X_blue_v3` to `P_r, Q_r, R_r, S_r, f X, f Y`.
          obtain ⟨P', Q', Y', X', h_congr, h_red⟩ : ∃ P' Q' Y' X', Congruent (fun i => ![P_r, Q_r, f Y, f X] i) (fun i => ![P', Q', Y', X'] i) ∧ c P' = Color.Red ∧ c Q' = Color.Red ∧ c Y' = Color.Red ∧ c X' = Color.Red := by
            apply lemma_case1_X_blue_v3;
            any_goals assumption;
            · have h_f_parallelogram : ∀ (u v : Point), f (u + v) = f u + f v - f 0 := by
                intro u v; exact (by
                have := f.map_vadd 0 ( u + v ) ; have := f.map_vadd 0 u; have := f.map_vadd 0 v; simp_all +decide [ add_assoc ] ;
                ext i; norm_num; ring;);
              rw [ sub_eq_sub_iff_add_eq_add ] at *;
              grind;
            · have := f.dist_map P Q; aesop;
            · rw [ ← hf.1, ← h_dist_PX ];
              exact f.isometry.dist_eq _ _;
          unfold Congruent at *;
          simp_all +decide [ Fin.forall_fin_succ ];
          have := f.isometry.dist_eq P Y; have := f.isometry.dist_eq Q Y; have := f.isometry.dist_eq P X; have := f.isometry.dist_eq Q X; aesop;
        · use P_r, Q_r, f Y, f X;
          unfold Congruent;
          simp_all +decide [ Fin.forall_fin_succ, edist_dist ];
          have := f.isometry.dist_eq P Q; have := f.isometry.dist_eq P X; have := f.isometry.dist_eq Q Y; have := f.isometry.dist_eq Q X; have := f.isometry.dist_eq Y P; have := f.isometry.dist_eq Y Q; have := f.isometry.dist_eq X P; have := f.isometry.dist_eq X Q; simp_all +decide [ dist_comm ] ;
          exact ⟨ Or.resolve_left ( by cases h : c ( f Y ) <;> tauto ) hY, Or.resolve_left ( by cases h : c ( f X ) <;> tauto ) hX ⟩

lemma lemma_case1 (c : Point → Color) (cfg : Fin 4 → Point)
  (h_case1 : Case1 c cfg) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
    obtain ⟨ i, j, k, l, h₁, h₂, h₃, h₄ ⟩ := h_case1;
    -- Apply the lemma_case1_geometric_step to find the required configuration cfg'.
    obtain ⟨cfg', hcfg'_congr, hcfg'_red⟩ : ∃ cfg' : Fin 4 → Point, Congruent (fun m => if m = 0 then cfg i else if m = 1 then cfg k else if m = 2 then cfg j else cfg l) cfg' ∧ ∀ m, c (cfg' m) = Color.Red := by
      by_cases ha : dist ( cfg i ) ( cfg k ) = 0 <;> by_cases hb : dist ( cfg i ) ( cfg l ) = 0 <;> simp_all +decide [ has_blue_dist ];
      · use fun m => if m = 0 then cfg l else if m = 1 then cfg l else if m = 2 then cfg l else cfg l; simp_all +decide [ Congruent ] ;
        cases h : c ( cfg l ) <;> simp_all +decide [ segments_bisect ];
      · simp_all +decide [ segments_bisect ];
        simp_all +decide [ midpoint_eq_iff ];
        cases h : c ( cfg k ) <;> cases h' : c ( cfg j ) <;> aesop;
      · cases h : c ( cfg l ) <;> cases h' : c ( cfg k ) <;> cases h'' : c ( cfg j ) <;> aesop;
      · have := @lemma_case1_geometric_step;
        specialize this c (dist (cfg i) (cfg k)) (dist (cfg i) (cfg l)) (cfg i) (cfg k) (cfg l) (cfg j);
        contrapose! this;
        refine' ⟨ _, rfl, rfl, _, _, _, _ ⟩;
        · unfold segments_bisect at h₂; simp_all +decide [ midpoint_eq_smul_add ] ;
          ext x ; have := congr_fun h₂ x ; norm_num at * ; linarith;
        · exact fun A B hAB hA hB => h₃ A hA B hB hAB;
        · exact fun A B hAB hA hB => h₄ A hA B hB hAB;
        · have := @lemma3 c (dist (cfg i) (cfg k));
          specialize this ( by aesop ) ( dist_pos.mpr ha ) ; aesop;
        · refine' ⟨ dist_pos.mpr ha, dist_pos.mpr hb, _ ⟩;
          intro x y z t h₁ h₂ h₃ h₄ h₅; specialize this ( fun m => if m = 0 then x else if m = 1 then y else if m = 2 then z else t ) ; simp_all +decide [ Congruent ] ;
          simp_all +decide [ Fin.forall_fin_succ ];
          rcases this with ⟨ m, hm ⟩ ; fin_cases m <;> simp_all +decide ;
    use fun m => cfg' ( if m = i then 0 else if m = k then 1 else if m = j then 2 else 3 );
    refine' ⟨ _, _ ⟩;
    · intro m₁ m₂; specialize hcfg'_congr ( if m₁ = i then 0 else if m₁ = k then 1 else if m₁ = j then 2 else 3 ) ( if m₂ = i then 0 else if m₂ = k then 1 else if m₂ = j then 2 else 3 ) ; simp_all +decide [ Finset.ext_iff ] ;
      convert hcfg'_congr using 2;
      · fin_cases m₁ <;> simp +decide [ Fin.forall_fin_succ ] at h₁ ⊢;
        · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp +decide at h₁ ⊢;
        · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp +decide at h₁ ⊢;
        · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp +decide at h₁ ⊢;
        · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> trivial;
      · fin_cases m₂ <;> simp +decide [ * ];
        · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> trivial;
        · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> trivial;
        · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> trivial;
        · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> trivial;
    · exact fun m => hcfg'_red _

lemma lemma_exists_red_point (c : Point → Color)
  (h_blue : ∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue)) :
  ∃ P, c P = Color.Red := by
    obtain ⟨ P, hP ⟩ := lemma3 c 1 h_blue zero_lt_one; use P;
    exact hP.choose_spec.choose_spec.choose_spec.2.1

/-
Rotating a point P around C by 60 degrees results in a point at the same distance from P as P is from C.
-/
lemma rotate_equilateral (C P : Point) (theta : ℝ)
  (h_theta : theta = Real.pi / 3 ∨ theta = -Real.pi / 3) :
  dist P (rotate_around C theta P) = dist P C := by
    cases h_theta <;> subst_vars <;> norm_num [ dist_eq_norm, Point ];
    · unfold rotate_around;
      unfold rotate_point; norm_num [ EuclideanSpace.norm_eq ] ; ring_nf;
      norm_num ; ring_nf;
    · unfold rotate_around;
      unfold rotate_point; norm_num [ neg_div, EuclideanSpace.norm_eq ] ; ring_nf;
      norm_num ; ring_nf

/-
If ABC is an equilateral triangle with side length t, then C is obtained by rotating A around B by 60 degrees or -60 degrees.
-/
lemma equilateral_triangle_rotation (A B C : Point) (t : ℝ)
  (h_AB : dist A B = t)
  (h_BC : dist B C = t)
  (h_CA : dist C A = t) :
  rotate_around B (Real.pi / 3) A = C ∨ rotate_around B (-Real.pi / 3) A = C := by
    -- Since $dist A B = t$ and $dist B C = t$, we have $‖A - B‖ = t$ and $‖C - B‖ = t$.
    have h_norm_AB : ‖A - B‖ = t := by
      exact h_AB ▸ rfl
    have h_norm_BC : ‖C - B‖ = t := by
      rw [ ← h_BC, dist_eq_norm' ]
    have h_norm_CA : ‖C - A‖ = t := by
      exact h_CA ▸ rfl;
    -- By definition of rotation, we have that $rotate_around B (π / 3) A = B + rotate_point (π / 3) (A - B)$ and $rotate_around B (-π / 3) A = B + rotate_point (-π / 3) (A - B)$.
    unfold rotate_around rotate_point at *; simp_all +decide [ dist_eq_norm' ] ;
    -- By definition of rotation, we have that $rotate_around B (π / 3) A = B + rotate_point (π / 3) (A - B)$ and $rotate_around B (-π / 3) A = B + rotate_point (-π / 3) (A - B)$. Therefore, we need to show that $C = B + rotate_point (π / 3) (A - B)$ or $C = B + rotate_point (-π / 3) (A - B)$.
    have h_rotation : (C 0 - B 0)^2 + (C 1 - B 1)^2 = t^2 ∧ ((C 0 - B 0) - (A 0 - B 0) * 2⁻¹ + (A 1 - B 1) * (Real.sqrt 3 / 2))^2 + ((C 1 - B 1) - (A 0 - B 0) * (Real.sqrt 3 / 2) - (A 1 - B 1) * 2⁻¹)^2 = 0 ∨ (C 0 - B 0)^2 + (C 1 - B 1)^2 = t^2 ∧ ((C 0 - B 0) - (A 0 - B 0) * 2⁻¹ - (A 1 - B 1) * (Real.sqrt 3 / 2))^2 + ((C 1 - B 1) + (A 0 - B 0) * (Real.sqrt 3 / 2) - (A 1 - B 1) * 2⁻¹)^2 = 0 := by
      field_simp;
      have h_rotation : (C 0 - B 0)^2 + (C 1 - B 1)^2 = t^2 ∧ (C 0 - A 0)^2 + (C 1 - A 1)^2 = t^2 ∧ (B 0 - A 0)^2 + (B 1 - A 1)^2 = t^2 := by
        simp_all +decide [ EuclideanSpace.norm_eq ];
        exact ⟨ by rw [ ← h_norm_BC, Real.sq_sqrt ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ], by rw [ ← h_norm_CA, Real.sq_sqrt ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ], by rw [ ← h_AB, Real.sq_sqrt ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ] ⟩;
      grind +ring;
    rcases h_rotation with h | h <;> norm_num [ neg_div ] at * <;> simp_all +decide ;
    · exact Or.inl <| by ext i; fin_cases i <;> norm_num <;> nlinarith! only [ h.2, Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] ;
    · exact Or.inr <| by ext i; fin_cases i <;> norm_num <;> nlinarith! only [ h.2, Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] ;

/-
For a regular rhombus PQRS, rotating P around Q by 60 degrees (or -60 degrees) yields R, and similarly for R to S.
-/
lemma rhombus_vertex_rotation (a : ℝ) (P Q R S : Point) (h_rhombus : regular_t_rhombus a P Q R S) :
  (rotate_around Q (Real.pi / 3) P = R ∨ rotate_around Q (-Real.pi / 3) P = R) ∧
  (rotate_around Q (Real.pi / 3) R = S ∨ rotate_around Q (-Real.pi / 3) R = S) := by
    apply And.intro;
    · apply equilateral_triangle_rotation P Q R a h_rhombus.1 h_rhombus.2.1 h_rhombus.2.2.1;
    · obtain ⟨h_dist_PQ, h_dist_QS, h_eq⟩ := h_rhombus;
      convert equilateral_triangle_rotation R Q S a _ _ _ using 1 <;> aesop

/-
For a regular rhombus PQRS, there exists an angle theta (+/ - 60 degrees) such that rotating P around Q by theta gives R, and rotating Q around R by -theta gives S.
-/
lemma rhombus_rotation_angles (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q R S) :
  ∃ theta, (theta = Real.pi / 3 ∨ theta = -Real.pi / 3) ∧
  rotate_around Q theta P = R ∧
  rotate_around R (-theta) Q = S := by
    obtain ⟨hPQ, hQR, hRS, hPS⟩ := h_rhombus;
    have h_rotate_P : rotate_around Q (Real.pi / 3) P = R ∨ rotate_around Q (-Real.pi / 3) P = R := by
      apply rhombus_vertex_rotation a P Q R S ⟨hPQ, hQR, hRS, hPS⟩ |>.1
    have h_rotate_Q : rotate_around R (Real.pi / 3) Q = S ∨ rotate_around R (-Real.pi / 3) Q = S := by
      apply equilateral_triangle_rotation;
      exacts [ hQR, by simpa only [ dist_comm ] using hPS.2.1, by simpa only [ dist_comm ] using hPS.1 ];
    unfold rotate_around at *;
    unfold rotate_point at *;
    norm_num [ neg_div ] at *;
    rcases h_rotate_P with h|h <;> rcases h_rotate_Q with j|j <;> simp_all +decide;
    · simp_all +decide [dist_eq_norm];
      norm_num [ ← h, ← j ] at *;
      norm_num [ Norm.norm ] at *;
      ring_nf at * ; norm_num at *;
      rw [ show ( Real.sqrt 3 ) ^ 4 = ( Real.sqrt 3 ^ 2 ) ^ 2 by ring, Real.sq_sqrt ] at * <;> norm_num at *;
      rw [ ← Real.sqrt_eq_rpow ] at * ; ring_nf at * ; norm_num at *;
      norm_num [ ← Real.sqrt_eq_rpow, hPS.2.2 ] at *;
      rw [ Real.sqrt_eq_zero' ] at *;
      norm_num [ show P 0 = Q 0 by nlinarith [ sq_nonneg ( P 0 - Q 0 ), sq_nonneg ( P 1 - Q 1 ) ], show P 1 = Q 1 by nlinarith [ sq_nonneg ( P 0 - Q 0 ), sq_nonneg ( P 1 - Q 1 ) ] ] at *;
    · exact Or.inr ( by ext i; have := congr_fun j i; fin_cases i <;> norm_num at * <;> linarith! );
    · simp_all +decide [dist_eq_norm];
      norm_num [ ← h, ← j, Norm.norm ] at *;
      ring_nf at *; norm_num at *;
      norm_num [ show ( Real.sqrt 3 ) ^ 4 = ( Real.sqrt 3 ^ 2 ) ^ 2 by ring ] at * ; ring_nf at * ; norm_num at *;
      norm_num [ ← Real.sqrt_eq_rpow, hPS.2 ] at *;
      rw [ Real.sqrt_eq_zero' ] at hPQ ; exact Or.inl <| by ext i ; fin_cases i <;> norm_num <;> nlinarith! [ sq_nonneg ( P 0 - Q 0 ), sq_nonneg ( P 1 - Q 1 ), Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] ;

/-
Existence of compatible rotations for the rhombus.
-/
lemma lemma_rhombus_rotation_existence (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q S R) :
  ∃ theta : ℝ, (theta = Real.pi / 3 ∨ theta = -Real.pi / 3) ∧
    rotate_around Q theta P = S ∧
    rotate_around S (-theta) Q = R := by
      have := @rhombus_rotation_angles;
      convert this a P Q S R h_rhombus using 1

/-
The composition of a rotation by theta around C1 and a rotation by -theta around C2 is a translation by the vector R2(C1) - C1.
-/
lemma lemma_rotation_composition_formula (C1 C2 : Point) (theta : ℝ) :
  ∀ X, rotate_around C2 (-theta) (rotate_around C1 theta X) = X + (rotate_around C2 (-theta) C1 - C1) := by
    -- By definition of rotation, we can rewrite the left-hand side.
    simp [rotate_around, rotate_point];
    intro X; ext i; fin_cases i <;> norm_num <;> ring_nf;
    · rw [ Real.sin_sq, Real.cos_sq ] ; ring!;
    · rw [ Real.sin_sq ] ; ring!

/-
Inverse property of rotation.
-/
lemma rotate_around_inverse (C : Point) (theta : ℝ) (P : Point) :
  rotate_around C (-theta) (rotate_around C theta P) = P := by
    unfold rotate_around; ext; norm_num [ Real.sin_add, Real.cos_add ] ; ring_nf;
    rename_i i; fin_cases i <;> unfold rotate_point <;> norm_num [ Real.sin_add, Real.cos_add ] <;> ring_nf;
    · rw [ Real.sin_sq, Real.cos_sq ] ; ring!;
    · rw [ Real.sin_sq, Real.cos_sq ] ; ring!

/-
Definition of rotation as an IsometryEquiv.
-/
def rotate_around_iso_equiv (C : Point) (theta : ℝ) : Point ≃ᵢ Point where
  toFun := rotate_around C theta
  invFun := rotate_around C (-theta)
  left_inv := rotate_around_inverse C theta
  right_inv := fun P => by
    have := rotate_around_inverse C (-theta) P
    rwa [neg_neg] at this
  isometry_toFun := rotate_around_isometry C theta

/-
Given the correct angle, the composition of rotations is the desired translation.
-/
lemma lemma_case2_geometry_explicit_theta (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (theta : ℝ)
  (htheta_P : rotate_around Q theta P = S)
  (htheta_Q : rotate_around S (-theta) Q = R) :
  let rot1 := (rotate_around_iso_equiv Q theta).toRealAffineIsometryEquiv
  let rot2 := (rotate_around_iso_equiv S (-theta)).toRealAffineIsometryEquiv
  ∀ X, rot2 (rot1 X) = X + (S - P) := by
    have h_composition : ∀ X, rotate_around S (-theta) (rotate_around Q theta X) = X + (rotate_around S (-theta) Q - Q) := by
      apply_rules [ lemma_rotation_composition_formula ];
    -- By `lemma_rhombus_properties`, `R - Q = S - P`.
    have h_rhombus_prop : R - Q = S - P := by
      -- By definition of `regular_t_rhombus`, we know that `S - P = R - Q`.
      apply (lemma_rhombus_properties a P Q R S h_rhombus).left.symm;
    aesop

/-
Stronger version of the geometry lemma that explicitly guarantees the distance properties of the rotations.
-/
lemma lemma_case2_geometry_strong (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q S R):
  ∃ (rot1 rot2 : Point ≃ᵃⁱ[ℝ] Point),
    rot1 Q = Q ∧ rot1 P = S ∧
    rot2 S = S ∧ rot2 Q = R ∧
    (∀ X, rot2 (rot1 X) = X + (S - P)) ∧
    (∀ X, dist X (rot1 X) = dist X Q) ∧
    (∀ X, dist X (rot2 X) = dist X S) := by
      -- By the properties of the rhombus and the rotations, we can show that the second part of the conjunction holds.
      obtain ⟨theta, htheta⟩ : ∃ theta : ℝ, (theta = Real.pi / 3 ∨ theta = -Real.pi / 3) ∧ rotate_around Q theta P = S ∧ rotate_around S (-theta) Q = R := by
        -- Apply the lemma that states the existence of such a theta.
        obtain ⟨theta, htheta⟩ := lemma_rhombus_rotation_existence a P Q R S h_rhombus;
        use theta;
      refine' ⟨ _, _, _, _, _, _, _, _ ⟩;
      exact ( rotate_around_iso_equiv Q theta ).toRealAffineIsometryEquiv;
      exact ( rotate_around_iso_equiv S ( -theta ) ).toRealAffineIsometryEquiv;
      all_goals norm_num [ rotate_around_iso_equiv ] at *;
      any_goals tauto;
      · unfold rotate_around; norm_num;
        unfold rotate_point; ext i; fin_cases i <;> norm_num;
      · unfold rotate_around; norm_num;
        unfold rotate_point; norm_num;
        ext i; fin_cases i <;> norm_num;
      · convert lemma_case2_geometry_explicit_theta a P Q R S h_rhombus theta htheta.2.1 htheta.2.2 using 1;
      · constructor <;> intro X <;> apply_rules [ rotate_equilateral ];
        · exact htheta.1;
        · rcases htheta.1 with ( rfl | rfl ) <;> ring_nf <;> norm_num

/-
Given the points and distances matching the configuration, one of the three pairs must be Red, otherwise we get a contradiction with Case 2.
-/
lemma lemma_case2_pair_selection (c : Point → Color) (cfg : Fin 4 → Point)
  (h_case2 : Case2 c cfg)
  (Y X Y' X' Y_star X_star : Point)
  (h_dist_Y_Y' : dist Y Y' = dist (cfg 2) (cfg 1))
  (h_dist_X_X' : dist X X' = dist (cfg 3) (cfg 1))
  (h_dist_Y'_Y_star : dist Y' Y_star = dist (cfg 2) (cfg 0))
  (h_dist_X'_X_star : dist X' X_star = dist (cfg 3) (cfg 0))
  (h_dist_Y_Y_star : dist Y Y_star = dist (cfg 0) (cfg 1))
  (h_dist_X_X_star : dist X X_star = dist (cfg 0) (cfg 1)) :
  (c Y = Color.Red ∧ c X = Color.Red) ∨
  (c Y' = Color.Red ∧ c X' = Color.Red) ∨
  (c Y_star = Color.Red ∧ c X_star = Color.Red) := by
    have h_C1 : ¬ (c Y = Color.Blue ∧ c Y' = Color.Blue) := by
      exact fun h => h_case2 2 1 ( by decide ) ⟨ Y, Y', h.1, h.2, h_dist_Y_Y' ⟩
    have h_C2 : ¬ (c X = Color.Blue ∧ c X' = Color.Blue) := by
      exact fun h => h_case2 3 1 ( by decide ) ⟨ X, X', h.1, h.2, by linarith ⟩ ;
    have h_C3 : ¬ (c Y' = Color.Blue ∧ c Y_star = Color.Blue) := by
      intro h_blue_pair;
      exact h_case2 2 0 ( by decide ) ⟨ Y', Y_star, h_blue_pair.1, h_blue_pair.2, by aesop ⟩ ;
    have h_C4 : ¬ (c X' = Color.Blue ∧ c X_star = Color.Blue) := by
      intro h; specialize h_case2 3 0; simp_all +decide ;
      exact h_case2 ⟨ X', X_star, h.1, h.2, h_dist_X'_X_star ⟩
    have h_C5 : ¬ (c Y = Color.Blue ∧ c Y_star = Color.Blue) := by
      exact fun h => h_case2 0 1 ( by decide ) ⟨ Y, Y_star, h.1, h.2, h_dist_Y_Y_star ⟩ ;
    have h_C6 : ¬ (c X = Color.Blue ∧ c X_star = Color.Blue) := by
      exact fun h => h_case2 0 1 ( by decide ) ⟨ X, X_star, h.1, h.2, by linarith ⟩ |> fun h => by tauto;
    generalize_proofs at *; (
    cases h : c Y <;> cases h' : c X <;> cases h'' : c Y' <;> cases h''' : c X' <;> cases h'''' : c Y_star <;> cases h''''' : c X_star <;> simp_all +decide only ;)

/-
Helper lemma: if one of the candidate pairs is red, we can construct a fully red configuration.
-/
lemma lemma_case2_red_copy_from_selection (c : Point → Color) (cfg : Fin 4 → Point)
  (P Q R S : Point)
  (h_red_rhombus : c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (f : Point ≃ᵃⁱ[ℝ] Point)
  (hf0 : f (cfg 0) = P)
  (hf1 : f (cfg 1) = Q)
  (rot1 rot2 : Point ≃ᵃⁱ[ℝ] Point)
  (h_rot : rot1 Q = Q ∧ rot1 P = R ∧
           rot2 R = R ∧ rot2 Q = S)
  (Y X : Point) (hY : Y = f (cfg 2)) (hX : X = f (cfg 3))
  (Y' X' : Point) (hY' : Y' = rot1 Y) (hX' : X' = rot1 X)
  (Y_star X_star : Point) (hY_star : Y_star = rot2 Y') (hX_star : X_star = rot2 X')
  (h_red_pair : (c Y = Color.Red ∧ c X = Color.Red) ∨
                (c Y' = Color.Red ∧ c X' = Color.Red) ∨
                (c Y_star = Color.Red ∧ c X_star = Color.Red)) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
    rcases h_red_pair with ( h | h | h ) <;> simp_all +decide [ Fin.forall_fin_succ ];
    · -- Define the new configuration cfg' as f ∘ cfg.
      use f ∘ cfg;
      unfold Congruent; aesop;
    · refine' ⟨ fun i => rot1 ( f ( cfg i ) ), _, _, _, _, _ ⟩ <;> simp_all +decide [Congruent];
    · refine' ⟨ fun i => rot2 ( rot1 ( f ( cfg i ) ) ), _, _, _, _, _ ⟩ <;> simp_all +decide [ Congruent ]

/-
Proof of Case 2, handling the degenerate case and using helper lemmas for the main case.
-/
lemma lemma_case2_proven (c : Point → Color) (cfg : Fin 4 → Point)
  (h_blue : ∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_case2 : Case2 c cfg) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
    revert c cfg h_blue h_case2;
    intros c cfg h_blue h_case2
    by_cases ha : ∃ i j, dist (cfg i) (cfg j) > 0;
    · -- Assume there exists $i, j$ such that $dist(cfg(i), cfg(j)) > 0$. Reindex so that $dist(cfg(0), cfg(1)) > 0$.
      obtain ⟨i, j, hij⟩ : ∃ i j, i ≠ j ∧ dist (cfg i) (cfg j) > 0 := by
        obtain ⟨ i, j, h ⟩ := ha; use i, j; aesop;
      obtain ⟨σ, hσ⟩ : ∃ σ : Fin 4 ≃ Fin 4, dist (cfg (σ 0)) (cfg (σ 1)) > 0 := by
        -- Since $i \neq j$, we can construct a permutation $\sigma$ such that $\sigma(0) = i$ and $\sigma(1) = j$.
        obtain ⟨σ, hσ⟩ : ∃ σ : Fin 4 ≃ Fin 4, σ 0 = i ∧ σ 1 = j := by
          fin_cases i <;> fin_cases j <;> simp +decide at hij ⊢
        generalize_proofs at *; (
        exact ⟨ σ, by simpa only [ hσ ] using hij.2 ⟩)
      set cfg' : Fin 4 → Point := cfg ∘ σ
      have h_case2' : Case2 c cfg' := by
        intro i j hij; specialize h_case2 ( σ i ) ( σ j ) ; aesop;
      have h_dist_pos : dist (cfg' 0) (cfg' 1) > 0 := by
        exact hσ
      generalize_proofs at *; (
      -- Apply `lemma3` with $t = dist(cfg'(0), cfg'(1))$ to get a red rhombus $P, Q, R, S$.
      obtain ⟨P, Q, R, S, h_rhombus, h_red_rhombus⟩ : ∃ P Q R S : Point, regular_t_rhombus (dist (cfg' 0) (cfg' 1)) P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red := by
        apply_rules [ lemma3 ];
        intros P Q h_dist_eq
        by_contra h_contra
        have h_blue_dist : has_blue_dist c (dist (cfg' 0) (cfg' 1)) := by
          exact ⟨ P, Q, h_contra.1, h_contra.2, h_dist_eq ⟩
        generalize_proofs at *; (
        exact h_case2' 0 1 ( by simp +decide ) h_blue_dist)
      generalize_proofs at *; (
      -- Use `exists_isometry_mapping_pair` to find $f$ such that $f(cfg'(0)) = P$ and $f(cfg'(1)) = Q$.
      obtain ⟨f, hf⟩ : ∃ f : Point ≃ᵃⁱ[ℝ] Point, f (cfg' 0) = P ∧ f (cfg' 1) = Q := by
        apply exists_isometry_mapping_pair; exact (by
        exact h_rhombus.1.symm ▸ rfl)
      generalize_proofs at *; (
      -- Apply `lemma_case2_geometry_strong` to get `rot1`, `rot2`.
      obtain ⟨rot1, rot2, hrot⟩ : ∃ rot1 rot2 : Point ≃ᵃⁱ[ℝ] Point,
        rot1 Q = Q ∧ rot1 P = R ∧
        rot2 R = R ∧ rot2 Q = S ∧
        (∀ X, rot2 (rot1 X) = X + (R - P)) ∧
        (∀ X, dist X (rot1 X) = dist X Q) ∧
        (∀ X, dist X (rot2 X) = dist X R) := by
          apply lemma_case2_geometry_strong; assumption;
      generalize_proofs at *; (
      -- Apply `lemma_case2_pair_selection` to find a red pair.
      obtain ⟨Y, X, Y', X', Y_star, X_star, hY, hX, hY', hX', hY_star, hX_star, h_red_pair⟩ : ∃ Y X Y' X' Y_star X_star : Point,
        Y = f (cfg' 2) ∧ X = f (cfg' 3) ∧
        Y' = rot1 Y ∧ X' = rot1 X ∧
        Y_star = rot2 Y' ∧ X_star = rot2 X' ∧
        ((c Y = Color.Red ∧ c X = Color.Red) ∨
         (c Y' = Color.Red ∧ c X' = Color.Red) ∨
         (c Y_star = Color.Red ∧ c X_star = Color.Red)) := by
           have h_dist_Y_Y' : dist (f (cfg' 2)) (rot1 (f (cfg' 2))) = dist (cfg' 2) (cfg' 1) := by
             have := f.isometry.dist_eq ( cfg' 2 ) ( cfg' 1 ) ; aesop;
           have h_dist_X_X' : dist (f (cfg' 3)) (rot1 (f (cfg' 3))) = dist (cfg' 3) (cfg' 1) := by
             have := hrot.2.2.2.2.2.1 ( f ( cfg' 3 ) ) ; aesop;
           have h_dist_Y'_Y_star : dist (rot1 (f (cfg' 2))) (rot2 (rot1 (f (cfg' 2)))) = dist (cfg' 2) (cfg' 0) := by
             have := hrot.2.2.2.2.2.2 ( rot1 ( f ( cfg' 2 ) ) ) ; aesop;
           have h_dist_X'_X_star : dist (rot1 (f (cfg' 3))) (rot2 (rot1 (f (cfg' 3)))) = dist (cfg' 3) (cfg' 0) := by
             have := hrot.2.2.2.2.2.2 ( rot1 ( f ( cfg' 3 ) ) ) ; aesop;
           have h_dist_Y_Y_star : dist (f (cfg' 2)) (rot2 (rot1 (f (cfg' 2)))) = dist (cfg' 0) (cfg' 1) := by
             have := h_rhombus.2.2.2.1; simp_all +decide [ dist_eq_norm ] ;
             have := h_rhombus.2.2.1; simp_all +decide [ dist_eq_norm ] ;
             rw [ ← this, norm_sub_rev ]
           have h_dist_X_X_star : dist (f (cfg' 3)) (rot2 (rot1 (f (cfg' 3)))) = dist (cfg' 0) (cfg' 1) := by
             have := hrot.2.2.2.2.1 ( f ( cfg' 3 ) ) ; simp_all +decide [ dist_eq_norm ] ;
           generalize_proofs at *; (
           have := lemma_case2_pair_selection c cfg' h_case2' ( f ( cfg' 2 ) ) ( f ( cfg' 3 ) ) ( rot1 ( f ( cfg' 2 ) ) ) ( rot1 ( f ( cfg' 3 ) ) ) ( rot2 ( rot1 ( f ( cfg' 2 ) ) ) ) ( rot2 ( rot1 ( f ( cfg' 3 ) ) ) ) ; simp_all +decide ;)
      generalize_proofs at *; (
      -- Apply `lemma_case2_red_copy_from_selection` to construct the red copy.
      obtain ⟨cfg'', hcfg''⟩ : ∃ cfg'' : Fin 4 → Point, Congruent cfg' cfg'' ∧ ∀ i, c (cfg'' i) = Color.Red := by
        apply_rules [ lemma_case2_red_copy_from_selection ];
        · exact hf.1;
        · exact hf.2;
        · tauto
      generalize_proofs at *; (
      use cfg'' ∘ σ.symm; simp_all +decide [ Congruent ] ;
      intro i₁ i₂; specialize hcfg''; have := hcfg''.1 ( σ.symm i₁ ) ( σ.symm i₂ ) ; aesop;))))));
    · obtain ⟨P, hP⟩ : ∃ P, c P = Color.Red := by
        exact lemma_exists_red_point c h_blue;
      unfold Congruent; aesop;

/-
Definition of reflection of a point P across a point F.
-/
def reflection (F P : Point) : Point := 2 • F - P

/-
Definition of the sequence of points $P_k, Q_k, R_k, S_k$ obtained by translating the initial configuration by multiples of $v = 2(F - M)$.
-/
def sequence_points (P0 Q0 R0 S0 : Point) (k : ℤ) : Point × Point × Point × Point :=
  let F := midpoint ℝ P0 Q0
  let M := midpoint ℝ R0 S0
  let v := 2 • (F - M)
  (P0 + k • v, Q0 + k • v, R0 + k • v, S0 + k • v)

/-
If circles around P and Q are red, and no red configuration exists, then circles around R and S form a complementary pair.
-/
lemma lemma_red_pair_implies_complementary (c : Point → Color) (r : ℝ)
  (P Q R S : Point)
  (h_red_P : is_red_circle c P r)
  (h_red_Q : is_red_circle c Q r)
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P, Q, R, S] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red) :
  complementary_pair c R S r := by
    unfold complementary_pair is_red_circle at *;
    constructor <;> intro X hX hX' <;> contrapose! h_no_red_config;
    · use X + (P - R), X + (Q - R), X, X + (S - R);
      unfold Congruent;
      simp_all +decide [ edist_dist, dist_eq_norm ];
      refine' ⟨ _, _, _, _ ⟩;
      · simp +decide [ Fin.forall_fin_succ ];
      · convert h_red_P ( X + ( P - R ) ) _ using 1;
        convert hX using 2 ; abel_nf;
      · convert h_red_Q _ _ using 1;
        convert hX using 1 ; abel_nf;
      · cases h : c ( X + ( S - R ) ) <;> tauto;
    · unfold Congruent at *; simp_all +decide [ dist_eq_norm ] ;
      use X - ( S - P ), X - ( S - Q ), X - ( S - R ), X; simp_all +decide [ edist_dist ] ;
      refine' ⟨ _, _, _, _ ⟩;
      · simp +decide [ Fin.forall_fin_succ, dist_eq_norm ];
      · convert h_red_P ( X - ( S - P ) ) _ using 1 ; simp_all +decide [ sub_eq_add_neg, add_assoc ];
      · convert h_red_Q _ _ using 1;
        convert hX using 1 ; abel_nf;
      · cases h : c ( X - ( S - R ) ) <;> tauto

/-
With the correct translation vector, the sequence configuration is congruent to a permutation of the original.
-/
def sequence_points_v2 (P0 Q0 R0 S0 : Point) (k : ℤ) : Point × Point × Point × Point :=
  let F := midpoint ℝ P0 Q0
  let M := midpoint ℝ R0 S0
  let v := 2 • (M - F)
  (P0 + k • v, Q0 + k • v, R0 + k • v, S0 + k • v)

/-
The sequence of points Pk, Qk, Rk, Sk is congruent to the original configuration P0, Q0, R0, S0.
-/
lemma lemma_sequence_congruence (P0 Q0 R0 S0 : Point) (k : ℤ) :
  let (Pk, Qk, Rk, Sk) := sequence_points P0 Q0 R0 S0 k
  Congruent (fun i : Fin 4 => ![Pk, Qk, Rk, Sk] i) (fun i => ![P0, Q0, R0, S0] i) := by
    intro i₁ i₂; fin_cases i₁ <;> fin_cases i₂ <;> norm_num [ dist_eq_norm, Pi.norm_def ] ;

/-
The reflected configuration has no red copy if the original one doesn't.
-/
def reflected_points (P0 Q0 R0 S0 : Point) : Point × Point × Point × Point :=
  let F := midpoint ℝ P0 Q0
  (Q0, P0, reflection F R0, reflection F S0)

lemma lemma_reflected_no_red_copy (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red) :
  let (P0', Q0', R0', S0') := reflected_points P0 Q0 R0 S0
  ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0', Q0', R0', S0'] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red := by
      contrapose! h_no_red_config;
      obtain ⟨ p, q, r, s, h₁, h₂, h₃, h₄, h₅ ⟩ := h_no_red_config; use p, q, r, s; simp_all +decide [ Congruent ] ;
      simp_all +decide [ edist_dist, Fin.forall_fin_succ, reflected_points ];
      unfold reflection at *; simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
      norm_num [ midpoint_eq_smul_add ] at * ; ring_nf at * ; aesop ( simp_config := { decide := true } ) ;

/-
Generalized Step 1: If Pk, Qk are red at radius r, then Rk, Sk are red at the next radius.
-/
lemma lemma_step_1_gen (c : Point → Color) (P0 Q0 R0 S0 : Point) (k : ℤ) (r : ℝ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (Pk Qk Rk Sk : Point)
  (h_seq_k : (Pk, Qk, Rk, Sk) = sequence_points P0 Q0 R0 S0 k)
  (h_red_Pk : is_red_circle c Pk r)
  (h_red_Qk : is_red_circle c Qk r)
  (h_r_ge_1 : r ≥ 1) :
  let r_next := (Real.sqrt (4 * r^2 - 1) + Real.sqrt 3) / 2
  is_red_circle c Rk r_next ∧ is_red_circle c Sk r_next := by
    have := @lemma_red_pair_implies_complementary;
    field_simp;
    convert this c r Pk Qk Rk Sk h_red_Pk h_red_Qk _ using 1;
    · constructor <;> intro h <;> have := @lemma1;
      · rename_i h';
        convert h' c r Pk Qk Rk Sk h_red_Pk h_red_Qk _ using 1;
        intro h''; obtain ⟨ p, q, r, s, h₁, h₂, h₃, h₄, h₅ ⟩ := h''; exact h_no_red_config ⟨ p, q, r, s, by
          have h_congr : Congruent (fun i => ![Pk, Qk, Rk, Sk] i) (fun i => ![P0, Q0, R0, S0] i) := by
            convert lemma_sequence_congruence P0 Q0 R0 S0 k using 1;
            exact funext fun i => by fin_cases i <;> simp +decide [ ← h_seq_k ] ;
          exact h_congr.symm.trans h₁, h₂, h₃, h₄, h₅ ⟩ ;
      · specialize this c 1 r Rk Sk h_blue h ( by linarith );
        convert this using 1;
        · constructor <;> intro h <;> have := @lemma2;
          · tauto;
          · exact fun P hP => this c 1 r Rk h_blue h ( by linarith ) ( by linarith ) P ( by simpa using hP );
        · constructor <;> intro h <;> have := @lemma2;
          · grind;
          · specialize this c 1 r Sk h_blue h ( by linarith ) ( by linarith ) ; aesop;
    · -- Apply the lemma_sequence_congruence to show that the sequence points are congruent to the original points.
      have h_congruent : Congruent (fun i => ![Pk, Qk, Rk, Sk] i) (fun i => ![P0, Q0, R0, S0] i) := by
        convert lemma_sequence_congruence P0 Q0 R0 S0 k using 1;
        exact funext fun i => by fin_cases i <;> simp +decide [ ← h_seq_k ] ;
      rintro ⟨ p, q, r, s, h₁, h₂, h₃, h₄, h₅ ⟩;
      exact h_no_red_config ⟨ p, q, r, s, by exact h_congruent.symm.trans h₁, h₂, h₃, h₄, h₅ ⟩

/-
The configuration {P_{k+1}, Q_{k+1}, R_k, S_k} is congruent to {Q_0, P_0, S_0, R_0}.
-/
lemma lemma_sequence_congruence_step2_correct (P0 Q0 R0 S0 : Point) (k : ℤ) :
  let (_, _, Rk, Sk) := sequence_points_v2 P0 Q0 R0 S0 k
  let (Pk_next, Qk_next, _, _ ) := sequence_points_v2 P0 Q0 R0 S0 (k + 1)
  Congruent (fun i : Fin 4 => ![Pk_next, Qk_next, Rk, Sk] i) (fun i => ![Q0, P0, S0, R0] i) := by
    unfold sequence_points_v2;
    unfold Congruent; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
    simp +decide [ Fin.forall_fin_succ, edist_dist ];
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf ; norm_num;
    norm_num [ midpoint_eq_smul_add ] ; ring_nf ; norm_num;

/-
The configuration {Rk, Sk, Pk_next, Qk_next} has no red copy.
-/
lemma lemma_step_2_no_red_copy (c : Point → Color) (P0 Q0 R0 S0 : Point) (k : ℤ)
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (Pk Qk Rk Sk : Point)
  (h_seq_k : (Pk, Qk, Rk, Sk) = sequence_points_v2 P0 Q0 R0 S0 k)
  (Pk_next Qk_next Rk_next Sk_next : Point)
  (h_seq_k_next : (Pk_next, Qk_next, Rk_next, Sk_next) = sequence_points_v2 P0 Q0 R0 S0 (k + 1)) :
  ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![Rk, Sk, Pk_next, Qk_next] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red := by
      have := ( @lemma_sequence_congruence_step2_correct ) P0 Q0 R0 S0 k; simp_all +decide [ Prod.ext_iff ] ;
      intro p q r s h_congr h_p h_q h_r h_s; have := h_no_red_config p q r s; simp_all +decide ;
      contrapose! this; unfold Congruent at *; simp_all +decide [Fin.forall_fin_succ] ;
      grind

/-
Generalized Step 2: If Rk, Sk are red at radius r, then P_{k+1}, Q_{k+1} are red at the next radius.
-/
lemma lemma_step_2_gen (c : Point → Color) (P0 Q0 R0 S0 : Point) (k : ℤ) (r : ℝ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (Pk Qk Rk Sk : Point)
  (h_seq_k : (Pk, Qk, Rk, Sk) = sequence_points_v2 P0 Q0 R0 S0 k)
  (Pk_next Qk_next Rk_next Sk_next : Point)
  (h_seq_k_next : (Pk_next, Qk_next, Rk_next, Sk_next) = sequence_points_v2 P0 Q0 R0 S0 (k + 1))
  (h_red_Rk : is_red_circle c Rk r)
  (h_red_Sk : is_red_circle c Sk r)
  (h_r_ge_1 : r ≥ 1) :
  let r_next := (Real.sqrt (4 * r^2 - 1) + Real.sqrt 3) / 2
  is_red_circle c Pk_next r_next ∧ is_red_circle c Qk_next r_next := by
    convert lemma_step_1_gen c Rk Sk Pk_next Qk_next 0 r h_blue _ _ _ _ _ _ _ _ _ using 1 <;> norm_num at *;
    any_goals rfl;
    · aesop;
    · intro x x_1 x_2 x_3 h_congr h_x h_x_1 h_x_2 h_x_3;
      have h_no_red_copy_permuted_specific : ¬∃ p q r s : Point, Congruent (fun i => ![Rk, Sk, Pk_next, Qk_next] i) (fun i => ![p, q, r, s] i) ∧ c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red := by
        apply lemma_step_2_no_red_copy;
        exact fun ⟨ p, q, r, s, h_congr, h_p, h_q, h_r, h_s ⟩ => h_no_red_config p q r s h_congr h_p h_q h_r h_s;
        exact h_seq_k;
        exact h_seq_k_next;
      exact h_no_red_copy_permuted_specific ⟨ x, x_1, x_2, x_3, h_congr, h_x, h_x_1, h_x_2, h_x_3 ⟩;
    · exact fun k => h_r_seq_def k;
    · assumption;
    · simpa using h_red_Rk

/-
Generalized Step 2: If Rk, Sk are red at radius r, then P_{k+1}, Q_{k+1} are red at the next radius.
-/
lemma lemma_step_2_gen_renamed (c : Point → Color) (P0 Q0 R0 S0 : Point) (k : ℤ) (r : ℝ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (Pk Qk Rk Sk : Point)
  (h_seq_k : (Pk, Qk, Rk, Sk) = sequence_points_v2 P0 Q0 R0 S0 k)
  (Pk_next Qk_next Rk_next Sk_next : Point)
  (h_seq_k_next : (Pk_next, Qk_next, Rk_next, Sk_next) = sequence_points_v2 P0 Q0 R0 S0 (k + 1))
  (h_red_Rk : is_red_circle c Rk r)
  (h_red_Sk : is_red_circle c Sk r)
  (h_r_ge_1 : r ≥ 1) :
  let r_next := (Real.sqrt (4 * r^2 - 1) + Real.sqrt 3) / 2
  is_red_circle c Pk_next r_next ∧ is_red_circle c Qk_next r_next := by
    apply_rules [ lemma_step_2_gen ]

/-
For all k, the circles around Pk, Qk, Rk, Sk with radii from the sequence are red.
-/
lemma lemma_case3_induction (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0)) :
  ∀ k : ℕ,
    let (Pk, Qk, Rk, Sk) := sequence_points_v2 P0 Q0 R0 S0 k
    is_red_circle c Pk (r_seq (2 * k)) ∧ is_red_circle c Qk (r_seq (2 * k)) ∧
    is_red_circle c Rk (r_seq (2 * k + 1)) ∧ is_red_circle c Sk (r_seq (2 * k + 1)) := by
      intros k
      generalize_proofs at *;
      induction' k with k ih;
      · obtain ⟨h_red_P0, h_red_Q0⟩ := h_red_0
        have h_red_R0_S0 : is_red_circle c R0 (r_seq 1) ∧ is_red_circle c S0 (r_seq 1) := by
          apply lemma_step_1_gen c P0 Q0 R0 S0 0 (r_seq 0) h_blue h_no_red_config h_r_seq_def h_ge_1 P0 Q0 R0 S0 (by
          unfold sequence_points; norm_num;) h_red_P0 h_red_Q0 (by
          exact h_ge_1 0)
        generalize_proofs at *; (
        unfold sequence_points_v2; aesop;);
      · -- Apply the lemma_step_2_gen_renamed to get the red circles for P_{k+1} and Q_{k+1}.
        have h_step2 : let (Pk, Qk, Rk, Sk) := sequence_points_v2 P0 Q0 R0 S0 k
          let (Pk_next, Qk_next, Rk_next, Sk_next) := sequence_points_v2 P0 Q0 R0 S0 (k + 1)
          is_red_circle c Pk_next (r_seq (2 * k + 2)) ∧ is_red_circle c Qk_next (r_seq (2 * k + 2)) := by
            apply_rules [ lemma_step_2_gen_renamed ];
            · exact ih.2.2.1;
            · exact ih.2.2.2;
        have h_step1 : let (Pk, Qk, Rk, Sk) := sequence_points_v2 P0 Q0 R0 S0 k
          let (Pk_next, Qk_next, Rk_next, Sk_next) := sequence_points_v2 P0 Q0 R0 S0 (k + 1)
          is_red_circle c Rk_next (r_seq (2 * k + 3)) ∧ is_red_circle c Sk_next (r_seq (2 * k + 3)) := by
            apply_rules [ lemma_step_1_gen ];
            any_goals exact - ( k + 1 );
            · norm_num [ sub_eq_add_neg, add_assoc, add_left_comm, add_comm ];
              ext ; norm_num ; ring;
            · convert h_step2.1 using 1;
              ext ; norm_num ; ring;
            · convert h_step2.2 using 1;
              ext ; norm_num ; ring;
        generalize_proofs at *; (
        exact ⟨ h_step2.1, h_step2.2, h_step1.1, h_step1.2 ⟩)

/-
The reflected points R0' and S0' are red circles of radius r_seq 1 (sqrt 3).
-/
lemma lemma_reflected_red_sqrt3 (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0)) :
  let (_, _, R0', S0') := reflected_points P0 Q0 R0 S0
  is_red_circle c R0' (r_seq 1) ∧ is_red_circle c S0' (r_seq 1) := by
    convert lemma_step_1_gen c Q0 P0 ( reflection ( midpoint ℝ P0 Q0 ) R0 ) ( reflection ( midpoint ℝ P0 Q0 ) S0 ) 0 ( r_seq 0 ) _ _ _ _ _ _ using 1 <;> norm_num [ * ];
    rotate_left;
    exact fun A B hAB hA hB => h_blue A B hAB ⟨ hA, hB ⟩;
    convert lemma_reflected_no_red_copy c P0 Q0 R0 S0 h_no_red_config using 1;
    simp +decide [reflected_points];
    exact Q0;
    exact P0;
    unfold sequence_points; aesop;

/-
Two circles intersect if the distance between their centers is between the difference and sum of their radii.
-/
lemma lemma_circles_intersect (C1 C2 : Point) (r1 r2 : ℝ)
  (h_triangle_ineq : abs (r1 - r2) ≤ dist C1 C2 ∧ dist C1 C2 ≤ r1 + r2) :
  ∃ X, dist X C1 = r1 ∧ dist X C2 = r2 := by
    -- By the properties of the Euclidean distance, we can construct such a point X.
    have h_exists_X : ∃ X : EuclideanSpace ℝ (Fin 2), dist X C1 = r1 ∧ dist X C2 = r2 := by
      have h_dist : dist C1 C2 = ‖C1 - C2‖ := by
        exact rfl
      by_cases h : C1 = C2;
      · simp_all +decide [ sub_eq_zero ];
        use C2 + EuclideanSpace.single 0 r2; simp [dist_eq_norm];
        linarith;
      · -- Let $d = \|C1 - C2\|$. We can write $C2 = C1 + d \cdot u$ for some unit vector $u$.
        set d := ‖C1 - C2‖ with hd
        obtain ⟨u, hu⟩ : ∃ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 ∧ C2 = C1 + d • u := by
          refine' ⟨ ( 1 / d ) • ( C2 - C1 ), _, _ ⟩ <;> norm_num [ hd, norm_smul, h ];
          · rw [ norm_sub_rev, inv_mul_cancel₀ ( norm_ne_zero_iff.mpr ( sub_ne_zero.mpr ( Ne.symm h ) ) ) ];
          · simp +decide [← smul_assoc, show C1 - C2 ≠ 0 from sub_ne_zero.mpr h];
        -- Let $X = C1 + x \cdot u + y \cdot v$ where $v$ is a unit vector perpendicular to $u$.
        obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧ inner ℝ u v = 0 := by
          norm_num [ EuclideanSpace.norm_eq, inner ] at *;
          exact ⟨ fun i => if i = 0 then -u 1 else u 0, by norm_num; linarith, by norm_num; linarith ⟩
        obtain ⟨x, y, hx, hy⟩ : ∃ x y : ℝ, x^2 + y^2 = r1^2 ∧ (x - d)^2 + y^2 = r2^2 := by
          -- By solving the system of equations, we can find $x$ and $y$.
          use (r1^2 - r2^2 + d^2) / (2 * d), Real.sqrt (r1^2 - ((r1^2 - r2^2 + d^2) / (2 * d))^2);
          rw [ Real.sq_sqrt ] <;> norm_num [ abs_le ] at *;
          · grind;
          · rw [ div_pow, div_le_iff₀ ] <;> try nlinarith [ norm_pos_iff.mpr ( sub_ne_zero.mpr h ) ];
            rw [ h_dist ] at *;
            nlinarith [ mul_le_mul_of_nonneg_left h_triangle_ineq.1.1 ( sub_nonneg.2 h_triangle_ineq.1.2 ), mul_le_mul_of_nonneg_left h_triangle_ineq.1.2 ( sub_nonneg.2 h_triangle_ineq.2 ), mul_le_mul_of_nonneg_left h_triangle_ineq.2 ( sub_nonneg.2 h_triangle_ineq.1.1 ) ]
        use C1 + x • u + y • v;
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
        norm_num [ hu.2, inner ] at *;
        constructor <;> rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> try nlinarith [ abs_le.mp h_triangle_ineq.1 ];
        · grind;
        · grind +ring;
    exact h_exists_X

/-
The step size of the sequence r_{n} (every two steps) is less than sqrt(3).
-/
lemma lemma_r_seq_step_bound (n : ℕ)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1) :
  r_seq (n + 2) - r_seq n < Real.sqrt 3 := by
    -- By definition of $r_{n+1}$, we know that $r_{n+1} < r_n + \frac{\sqrt{3}}{2}$ for all $n$.
    have h_lt_add : ∀ k, r_seq (k + 1) < r_seq k + Real.sqrt 3 / 2 := by
      intro k; rw [ h_r_seq_def ] ; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sqrt_nonneg ( 4 * r_seq k ^ 2 - 1 ), Real.sq_sqrt ( show 0 ≤ 4 * r_seq k ^ 2 - 1 by nlinarith [ h_ge_1 k ] ), h_ge_1 k ] ;
    linarith [ h_lt_add n, h_lt_add ( n + 1 ) ]

/-
The sequence r_n is unbounded.
-/
lemma lemma_r_seq_unbounded
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2) :
  ∀ M : ℝ, ∃ n, r_seq n > M := by
    -- By induction, we can show that $r_{n+1} - r_n$ is bounded below by a positive constant.
    have h_diff_bound : ∃ c > 0, ∀ n, r_seq (n + 1) - r_seq n ≥ c := by
      use (Real.sqrt 3 - 1 / (2 + Real.sqrt 3)) / 2, by
        exact div_pos ( sub_pos_of_lt ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 3 ≥ 0 by norm_num ) ] ) ) zero_lt_two;
      intro n
      rw [h_r_seq_def]
      have h_bound : Real.sqrt (4 * (r_seq n)^2 - 1) ≥ 2 * r_seq n - 1 / (2 + Real.sqrt 3) := by
        refine Real.le_sqrt_of_sq_le ?_;
        field_simp;
        nlinarith [ show 1 ≤ r_seq n from Nat.recOn n ( by norm_num [ show r_seq 0 = 1 from rfl ] ) fun n ih => by rw [ h_r_seq_def ] ; exact by nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 3 ≥ 0 by norm_num ), Real.sqrt_nonneg ( 4 * r_seq n ^ 2 - 1 ), Real.sq_sqrt ( show 0 ≤ 4 * r_seq n ^ 2 - 1 by nlinarith [ show 1 ≤ r_seq n from ih ] ) ], Real.sqrt_nonneg 3, Real.sq_sqrt ( show 3 ≥ 0 by norm_num ) ]
      linarith [h_bound];
    -- By induction, we can show that $r_n \geq r_0 + nc$ for some $c > 0$.
    obtain ⟨c, hc_pos, hc_bound⟩ : ∃ c > 0, ∀ n, r_seq (n + 1) - r_seq n ≥ c := h_diff_bound;
    have h_induction : ∀ n, r_seq n ≥ r_seq 0 + n * c := by
      exact fun n => Nat.recOn n ( by norm_num ) fun n ih => by norm_num; linarith [ hc_bound n ] ;
    exact fun M => ⟨ ⌊ ( M - r_seq 0 ) / c⌋₊ + 1, by have := Nat.lt_floor_add_one ( ( M - r_seq 0 ) / c ) ; have := h_induction ( ⌊ ( M - r_seq 0 ) / c⌋₊ + 1 ) ; push_cast at *; nlinarith [ mul_div_cancel₀ ( M - r_seq 0 ) hc_pos.ne' ] ⟩

lemma lemma_circle_intersection_exists_even_constrained (d : ℝ)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_d_large : d ≥ r_seq 2 - Real.sqrt 3) :
  ∃ k ≥ 1, let r := r_seq (2 * k)
       abs (r - Real.sqrt 3) ≤ d ∧ d ≤ r + Real.sqrt 3 := by
         -- Since the sequence $r_{2k}$ is unbounded and has a step size less than $\sqrt{3}$, there must exist some $k$ such that $r_{2k}$ is within the interval $[d - \sqrt{3}, d + \sqrt{3}]$.
         obtain ⟨k, hk⟩ : ∃ k, r_seq (2 * k) ≥ d - Real.sqrt 3 ∧ r_seq (2 * k) ≤ d + Real.sqrt 3 := by
           -- By the properties of the sequence $r_{2k}$, it is unbounded and has a step size less than $\sqrt{3}$.
           have h_unbounded : ∀ M, ∃ k, r_seq (2 * k) > M := by
             have h_unbounded : ∀ M, ∃ k, r_seq k > M := by
               exact fun M => lemma_r_seq_unbounded h_r_seq_def M;
             exact fun M => by obtain ⟨ k, hk ⟩ := h_unbounded M; exact ⟨ k, hk.trans_le <| by exact monotone_nat_of_le_succ ( fun n => by rw [ h_r_seq_def ] ; nlinarith [ Real.sqrt_nonneg ( 4 * r_seq n ^ 2 - 1 ), Real.sqrt_nonneg 3, Real.mul_self_sqrt ( show 0 <= 4 * r_seq n ^ 2 - 1 by nlinarith [ h_ge_1 n ] ), Real.mul_self_sqrt ( show 0 <= 3 by norm_num ) ] ) <| by linarith ⟩ ;
           have h_step : ∀ k, r_seq (2 * (k + 1)) - r_seq (2 * k) < Real.sqrt 3 := by
             intros k
             have h_step : r_seq (2 * k + 2) - r_seq (2 * k) < Real.sqrt 3 := by
               convert lemma_r_seq_step_bound ( 2 * k ) h_r_seq_def h_ge_1 using 1
             exact h_step;
           obtain ⟨ k, hk ⟩ := h_unbounded ( d + Real.sqrt 3 );
           induction' k with k ih;
           · norm_num [ h_r_seq_def ] at *;
             norm_num [ show r_seq 0 = 1 by rfl ] at *;
             nlinarith [ Real.sqrt_nonneg 11, Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 11 by norm_num ), Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
           · exact if h : r_seq ( 2 * k ) > d + Real.sqrt 3 then ih h else ⟨ k, by linarith [ h_step k, Real.sqrt_nonneg 3 ], by linarith [ h_step k, Real.sqrt_nonneg 3 ] ⟩;
         by_cases hk1 : k ≥ 1;
         · norm_num +zetaDelta at *;
           by_cases h_case : d ≥ Real.sqrt 3;
           · exact ⟨ k, hk1, abs_le.mpr ⟨ by linarith [ h_ge_1 ( 2 * k ) ], by linarith [ h_ge_1 ( 2 * k ) ] ⟩, hk.1 ⟩;
           · use 1;
             norm_num [ h_r_seq_def ] at *;
             norm_num [ show r_seq 0 = 1 by rfl ] at *;
             constructor <;> cases abs_cases ( ( Real.sqrt 11 + Real.sqrt 3 ) / 2 - Real.sqrt 3 ) <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sqrt_nonneg 11, Real.sq_sqrt ( show 0 ≤ 11 by norm_num ) ];
         · interval_cases k ; norm_num at *;
           refine' ⟨ 1, _, _, _ ⟩ <;> norm_num [ h_r_seq_def, show r_seq 0 = 1 from rfl ] at *;
           · exact abs_le.mpr ⟨ by nlinarith [ Real.sqrt_nonneg 11, Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 11 by norm_num ), Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 11 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ], by nlinarith [ Real.sqrt_nonneg 11, Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 11 by norm_num ), Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 11 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ] ⟩;
           · nlinarith [ Real.sqrt_nonneg 11, Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 11 by norm_num ), Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 11 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ]

lemma lemma_r_seq_triangle (n : ℕ) (O : Point) (P : Point)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (hP : dist P O = r_seq (n + 1)) :
  ∃ Y Z : Point, dist Y O = r_seq n ∧ dist Z O = r_seq n ∧
    regular_triangle_side_1 (fun i => match i with | 0 => P | 1 => Y | 2 => Z) := by
      -- By definition of $r_seq$, we know that $P$ is a vertex of a regular unit triangle whose other vertices are on the $n$-th circle.
      have h_triangle : ∃ Y Z : Point, dist Y O = r_seq n ∧ dist Z O = r_seq n ∧ dist P Y = 1 ∧ dist P Z = 1 ∧ dist Y Z = 1 := by
        -- By definition of $r_seq$, we know that $P$ is a vertex of a regular unit triangle whose other vertices are on the $n$-th circle. Use this fact.
        have h_triangle : ∀ (r : ℝ) (O P : Point), r ≥ 1 / 2 → dist P O = (Real.sqrt (4 * r^2 - 1) + Real.sqrt 3) / 2 → ∃ Y Z : Point, dist Y O = r ∧ dist Z O = r ∧ dist P Y = 1 ∧ dist P Z = 1 ∧ dist Y Z = 1 := by
          intros r O P hr hP
          obtain ⟨Y, Z, hY, hZ, hP_Y, hP_Z, hYZ⟩ : ∃ Y Z : Point, dist Y O = r ∧ dist Z O = r ∧ dist P Y = 1 ∧ dist P Z = 1 ∧ dist Y Z = 1 := by
            have := lemma2_geom_explicit r 1 O P (by
            linarith) (by
            norm_num) (by
            aesop)
            exact ⟨ this.choose, this.choose_spec.choose, this.choose_spec.choose_spec.1, this.choose_spec.choose_spec.2.1, this.choose_spec.choose_spec.2.2.2.1, this.choose_spec.choose_spec.2.2.2.2, this.choose_spec.choose_spec.2.2.1 ⟩;
          use Y, Z;
        apply h_triangle; exact (by
        exact Nat.recOn n ( by norm_num [ show r_seq 0 = 1 from rfl ] ) fun n ihn => by rw [ h_r_seq_def ] ; exact le_div_iff₀' ( by positivity ) |>.2 ( by nlinarith [ Real.sqrt_nonneg ( 4 * r_seq n ^ 2 - 1 ), Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] ) ;); exact hP.trans (h_r_seq_def n).symm;
      obtain ⟨ Y, Z, hY, hZ, hPY, hPZ, hYZ ⟩ := h_triangle; use Y, Z; simp_all +decide [ regular_triangle_side_1 ] ;
      rwa [ dist_comm ]

/-
If the n-th circle is 1-alternating, then the (n+1)-th circle is red.
-/
lemma lemma_alt_implies_red_next (c : Point → Color) (O : Point) (n : ℕ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_alt : t_alternating c O (r_seq n) 1)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2) :
  is_red_circle c O (r_seq (n + 1)) := by
    have h_r_ge_half : r_seq n ≥ 1 / 2 := by
      exact le_trans ( by norm_num ) ( lemma_r_seq_ge_1 n h_r_seq_def );
    convert lemma2 c 1 ( r_seq n ) O h_blue h_alt h_r_ge_half zero_le_one using 1;
    aesop

lemma lemma_complementary_next (c : Point → Color) (R0 S0 : Point) (n : ℕ)
  (h_no_red_pair : ¬ ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∀ i, q i = p i + (S0 - R0)) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red))
  (h_red_n : is_red_circle c R0 (r_seq n) ∧ is_red_circle c S0 (r_seq n))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2) :
  complementary_pair c R0 S0 (r_seq (n + 1)) := by
    constructor <;> intro x hx hx' <;> contrapose! h_no_red_pair;
    · -- By Lemma~\ref{lem:r_seq_triangle}, $x$ is a vertex of a regular unit triangle $T$ with base on $\gamma_{R0}(r_n)$.
      obtain ⟨Y, Z, hY, hZ, hT⟩ : ∃ Y Z : Point, dist Y R0 = r_seq n ∧ dist Z R0 = r_seq n ∧ regular_triangle_side_1 (fun i => match i with | 0 => x | 1 => Y | 2 => Z) := by
        apply_rules [ lemma_r_seq_triangle ];
      refine' ⟨ fun i => if i = 0 then x else if i = 1 then Y else Z, fun i => if i = 0 then x + ( S0 - R0 ) else if i = 1 then Y + ( S0 - R0 ) else Z + ( S0 - R0 ), _, _, _, _ ⟩ <;> simp_all +decide [ Fin.forall_fin_succ ];
      · exact hT;
      · exact ⟨ h_red_n.1 Y hY, h_red_n.1 Z hZ ⟩;
      · refine' ⟨ _, _, _ ⟩ <;> contrapose! h_no_red_pair <;> have := h_red_n.2 ( x + ( S0 - R0 ) ) <;> have := h_red_n.2 ( Y + ( S0 - R0 ) ) <;> have := h_red_n.2 ( Z + ( S0 - R0 ) ) <;> simp_all +decide [ dist_eq_norm ];
        · cases h : c ( x + ( S0 - R0 ) ) <;> tauto;
        · simp_all +decide [ add_sub_assoc ];
          exact False.elim <| ‹¬‖Y + -R0‖ = r_seq n› <| by simpa [ add_comm ] using hY;
        · exact False.elim <| this <| by rw [ show Z + ( S0 - R0 ) - S0 = Z - R0 by abel1 ] ; exact hZ;
    · -- By Lemma~\ref{lem:r_seq_triangle}, we can form a regular triangle T with x as a vertex and Y, Z on gamma_R0(r_n).
      obtain ⟨Y, Z, hY, hZ, hT⟩ : ∃ Y Z : Point, dist Y R0 = r_seq n ∧ dist Z R0 = r_seq n ∧ regular_triangle_side_1 (fun i => match i with | 0 => x - (S0 - R0) | 1 => Y | 2 => Z) := by
        apply lemma_r_seq_triangle n;
        · assumption;
        · simp_all +decide [ dist_eq_norm, sub_sub ];
      refine' ⟨ _, _, hT, fun i => rfl, _, _ ⟩;
      · exact fun i => by fin_cases i <;> [ exact Or.resolve_right ( by cases h : c ( x - ( S0 - R0 ) ) <;> tauto ) h_no_red_pair; exact h_red_n.1 _ hY; exact h_red_n.1 _ hZ ] ;
      · intro i; fin_cases i <;> simp_all +decide [ dist_eq_norm ] ;
        · convert h_red_n.2 ( Y + ( S0 - R0 ) ) _ using 1;
          rw [ dist_eq_norm ] ; simp_all +decide [ sub_eq_add_neg, add_assoc ] ;
        · convert h_red_n.2 ( Z + ( S0 - R0 ) ) _ using 1;
          rw [ ← hZ, dist_eq_norm ] ; simp +decide [ sub_eq_add_neg, add_assoc ]

/-
If the n-th circles are red, and there are no red pairs of triangles, then the (n+1)-th circles are 1-alternating.
-/
lemma lemma_red_implies_alt_next (c : Point → Color) (_t : ℝ) (R0 S0 : Point) (n : ℕ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_pair : ¬ ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∀ i, q i = p i + (S0 - R0)) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red))
  (h_red_n : is_red_circle c R0 (r_seq n) ∧ is_red_circle c S0 (r_seq n))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2) :
  t_alternating c R0 (r_seq (n + 1)) 1 ∧ t_alternating c S0 (r_seq (n + 1)) 1 := by
    apply lemma1 c 1 ( r_seq ( n + 1 ) ) R0 S0 h_blue ( by
      apply lemma_complementary_next c R0 S0 n h_no_red_pair h_red_n h_r_seq_def ) ( by
      exact le_trans ( by norm_num ) ( lemma_r_seq_ge_1 ( n + 1 ) h_r_seq_def ) )

/-
If $r_1$ circles are red, then all odd $r_{2k+1}$ circles are red.
-/
lemma lemma_odd_seq_red_from_1 (c : Point → Color) (R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_pair_general : ∀ _n : ℕ, ¬ ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∀ i, q i = p i + (S0 - R0)) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_red_1 : is_red_circle c R0 (r_seq 1) ∧ is_red_circle c S0 (r_seq 1)) :
  ∀ k, is_red_circle c R0 (r_seq (2 * k + 1)) ∧ is_red_circle c S0 (r_seq (2 * k + 1)) := by
    -- By induction on $k$, we can show that for all $k$, the circles of radius $r_{2k+1}$ are red.
    intro k
    induction' k with k ih;
    · exact h_red_1;
    · -- By `lemma_red_implies_alt_next`, the circles of radius $r_{2k+2}$ are 1-alternating.
      have h_alt : t_alternating c R0 (r_seq (2 * k + 2)) 1 ∧ t_alternating c S0 (r_seq (2 * k + 2)) 1 := by
        apply lemma_red_implies_alt_next;
        exact r_seq k;
        · assumption;
        · exact h_no_red_pair_general ( 2 * k + 1 );
        · exact ih;
        · assumption;
      exact ⟨ lemma_alt_implies_red_next c R0 ( 2 * k + 2 ) h_blue h_alt.1 h_r_seq_def, lemma_alt_implies_red_next c S0 ( 2 * k + 2 ) h_blue h_alt.2 h_r_seq_def ⟩

lemma lemma3_case3_contradiction_final_v3_proven (c : Point → Color) (_t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (R0 S0 R0' S0' : Point)
  (h_red_circles_1 : is_red_circle c R0 (r_seq 1) ∧ is_red_circle c S0 (r_seq 1))
  (h_red_circles'_1 : is_red_circle c R0' (r_seq 1) ∧ is_red_circle c S0' (r_seq 1))
  (h_dist_S0_R0' : dist S0 R0' > r_seq 2 - Real.sqrt 3)
  (h_vec : R0' - S0' = S0 - R0)
  (h_no_red_pair : ¬ ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∀ i, q i = p i + (R0 - S0)) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1) :
  False := by
    -- By `lemma_odd_seq_red_from_1`, $R_0$ and $S_0$ are red circles at radius $r_{2k-1}$ for all $k \ge 1$.
    have h_odd_seq_red : ∀ k : ℕ, k ≥ 1 → is_red_circle c R0 (r_seq (2 * k - 1)) ∧ is_red_circle c S0 (r_seq (2 * k - 1)) := by
      have h_odd_seq_red : ∀ k : ℕ, is_red_circle c R0 (r_seq (2 * k + 1)) ∧ is_red_circle c S0 (r_seq (2 * k + 1)) := by
        apply_rules [ lemma_odd_seq_red_from_1 ];
        intro n hn
        obtain ⟨p, q, hp, hq, hp_red, hq_red⟩ := hn
        have h_contradiction : ∃ p' q' : Fin 3 → Point, regular_triangle_side_1 p' ∧ (∀ i, q' i = p' i + (R0 - S0)) ∧ (∀ i, c (p' i) = Color.Red) ∧ (∀ i, c (q' i) = Color.Red) := by
          use q, p; simp_all +decide [ regular_triangle_side_1 ] ;
          exact fun i => by ext j; norm_num; ring;
        exact h_no_red_pair h_contradiction;
      intro k hk; specialize h_odd_seq_red ( k - 1 ) ; cases k <;> tauto;
    -- By `lemma_complementary_next`, this implies that $R_0$ and $S_0$ form a complementary pair at radius $r_{2k}$.
    have h_complementary : ∀ k : ℕ, k ≥ 1 → complementary_pair c R0 S0 (r_seq (2 * k)) := by
      intros k hk
      specialize h_odd_seq_red k hk
      have h_complementary_step : complementary_pair c R0 S0 (r_seq (2 * k)) := by
        have h_no_red_pair : ¬ ∃ (p q : Fin 3 → Point),
          regular_triangle_side_1 p ∧
          (∀ i, q i = p i + (S0 - R0)) ∧
          (∀ i, c (p i) = Color.Red) ∧
          (∀ i, c (q i) = Color.Red) := by
            contrapose! h_no_red_pair;
            obtain ⟨ p, q, hp, hq, hp', hq' ⟩ := h_no_red_pair; use q, p; simp_all +decide [ regular_triangle_side_1 ] ;
            exact fun i => by abel1;
        apply lemma_complementary_next c R0 S0 (2 * k - 1) h_no_red_pair h_odd_seq_red (fun k => h_r_seq_def k) |> fun h => by
          rwa [ Nat.sub_add_cancel ( by linarith ) ] at h;
      exact h_complementary_step;
    -- By `lemma_circle_intersection_exists_even_constrained`, there exists $k \ge 1$ such that the circle around $S_0$ of radius $r_{2k}$ intersects the circle around $R_0'$ of radius $r_1 = \sqrt{3}$. Let $P$ be an intersection point.
    obtain ⟨k, hk_ge_1, hk_intersect⟩ : ∃ k : ℕ, k ≥ 1 ∧ let r := r_seq (2 * k)
        abs (r - Real.sqrt 3) ≤ dist S0 R0' ∧ dist S0 R0' ≤ r + Real.sqrt 3 := by
          exact lemma_circle_intersection_exists_even_constrained _ h_r_seq_def h_ge_1 h_dist_S0_R0'.le;
    -- Let $P$ be an intersection point of the circles around $S_0$ and $R_0'$.
    obtain ⟨P, hP⟩ : ∃ P : Point, dist P S0 = r_seq (2 * k) ∧ dist P R0' = r_seq 1 := by
      apply lemma_circles_intersect S0 R0' (r_seq (2 * k)) (r_seq 1);
      convert hk_intersect using 2 <;> norm_num [ h_r_seq_def 0 ];
      · rw [ show r_seq 0 = 1 by rfl ] ; norm_num;
      · norm_num [ show r_seq 0 = 1 by rfl ];
    -- Since $P$ is on the circle around $R_0'$ of radius $r_1$, and $R_0'$ is a red circle (hypothesis), $c(P) = Red$.
    have hP_red : c P = Color.Red := by
      exact h_red_circles'_1.1 P hP.2 ▸ rfl;
    -- Since $P$ is on the circle around $S_0$ of radius $r_{2k}$ and is Red, by the complementary pair property, $Q = P - (S_0 - R_0)$ must be Blue.
    have hQ_blue : c (P - (S0 - R0)) = Color.Blue := by
      specialize h_complementary k hk_ge_1;
      unfold complementary_pair at h_complementary; aesop;
    -- Since $Q$ is on the circle around $S_0'$ of radius $r_1$, and $S_0'$ is a red circle (hypothesis), $c(Q) = Red$.
    have hQ_red : c (P - (S0 - R0)) = Color.Red := by
      have hQ_red : dist (P - (S0 - R0)) S0' = r_seq 1 := by
        rw [ ← hP.2, show P - ( S0 - R0 ) = P - ( R0' - S0' ) by rw [ h_vec ] ] ; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf;
      exact h_red_circles'_1.2 _ hQ_red;
    cases hQ_red.symm.trans hQ_blue

lemma lemma_two_circles_contain_triangle_aux_intersection (O1 O2 : Point) (r : ℝ)
  (h_dist_ge : dist O1 O2 >= Real.sqrt 3 / 2)
  (h_dist_le : dist O1 O2 <= r)
  (h_r : r >= 2) :
  ∃ V : Point, dist V O1 = r ∧ dist V O2 = Real.sqrt (r^2 - 1/4) + Real.sqrt 3 / 2 := by
    have h_intersect : |r - (Real.sqrt (r^2 - 1 / 4) + Real.sqrt 3 / 2)| ≤ dist O1 O2 ∧ dist O1 O2 ≤ r + (Real.sqrt (r^2 - 1 / 4) + Real.sqrt 3 / 2) := by
      constructor <;> cases abs_cases ( r - ( Real.sqrt ( r^2 - 1/4 ) + Real.sqrt 3 / 2 ) ) <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sqrt_nonneg ( r^2 - 1/4 ), Real.sq_sqrt ( show 0 ≤ r^2 - 1/4 by nlinarith ) ] ;
    convert lemma_circles_intersect O1 O2 r ( Real.sqrt ( r^2 - 1/4 ) + Real.sqrt 3 / 2 ) _ using 1 ; norm_num at * ; aesop;

lemma lemma_chord_from_midpoint (O : Point) (M : Point) (r : ℝ)
  (h_dist : dist M O = Real.sqrt (r^2 - 1/4))
  (h_r : r ≥ 0.5) :
  ∃ B1 B2 : Point, midpoint ℝ B1 B2 = M ∧ dist B1 B2 = 1 ∧ dist B1 O = r ∧ dist B2 O = r := by
    -- Let $d = dist(M, O) = \sqrt{r^2 - 1/4}$. Since $r \ge 0.5$, $r^2 \ge 0.25$, so $r^2 - 1/4 \ge 0$.
    set d := Real.sqrt (r^2 - 1 / 4)
    have hd_nonneg : 0 ≤ d := by
      exact Real.sqrt_nonneg _;
    -- Consider the line passing through $M$ perpendicular to $OM$.
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧ inner ℝ v (O - M) = 0 := by
      by_cases h : O - M = 0 <;> simp_all +decide [ EuclideanSpace.norm_eq, dist_eq_norm ];
      · exact ⟨ fun i => if i = 0 then 1 else 0, by norm_num ⟩;
      · refine' ⟨ fun i => if i = 0 then ( O 1 - M 1 ) / Real.sqrt ( ( O 0 - M 0 ) ^ 2 + ( O 1 - M 1 ) ^ 2 ) else - ( O 0 - M 0 ) / Real.sqrt ( ( O 0 - M 0 ) ^ 2 + ( O 1 - M 1 ) ^ 2 ), _, _ ⟩ <;> norm_num [ Fin.sum_univ_two ];
        · field_simp;
          rw [ Real.sq_sqrt ( by positivity ), div_eq_iff ] <;> ring_nf ; contrapose! h ; ext i ; fin_cases i <;> norm_num <;> nlinarith! [ Real.sqrt_nonneg ( ( O 0 - M 0 ) ^ 2 + ( O 1 - M 1 ) ^ 2 ), Real.mul_self_sqrt ( by positivity : 0 ≤ ( O 0 - M 0 ) ^ 2 + ( O 1 - M 1 ) ^ 2 ) ] ;
        · norm_num [ Fin.sum_univ_two, inner ] ; ring!;
    refine' ⟨ M + ( 1 / 2 : ℝ ) • v, M - ( 1 / 2 : ℝ ) • v, _, _, _, _ ⟩ <;> norm_num [ EuclideanSpace.norm_eq, dist_eq_norm ] at *;
    · linarith;
    · rw [ Real.sqrt_eq_iff_mul_self_eq ] at * <;> try nlinarith [ Real.mul_self_sqrt ( show 0 ≤ r ^ 2 - 1 / 4 by nlinarith ) ];
      norm_num [ Fin.sum_univ_two, inner ] at * ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ r ^ 2 - 1 / 4 by nlinarith ) ] ;
    · rw [ Real.sqrt_eq_iff_mul_self_eq ] at * <;> try nlinarith;
      rw [ Real.mul_self_sqrt ( by nlinarith ) ] at h_dist ; norm_num [ Fin.sum_univ_two, inner ] at * ; nlinarith

lemma lemma_segment_partition (A B : Point) (a b : ℝ)
  (ha : a ≥ 0) (hb : b ≥ 0)
  (h_dist : dist A B = a + b) :
  ∃ M : Point, M ∈ segment ℝ A B ∧ dist M A = a ∧ dist M B = b := by
    by_cases hab : a + b = 0 <;> simp_all +decide [ segment_eq_image ];
    · constructor <;> linarith;
    · refine' ⟨ a / ( a + b ), ⟨ by positivity, by rw [ div_le_iff₀ ( by positivity ) ] ; linarith ⟩, _, _ ⟩ <;> simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
      · field_simp;
        rw [ Real.sqrt_eq_iff_mul_self_eq ] at * <;> try positivity;
        rw [ div_eq_iff ] <;> first | positivity | nlinarith;
      · rw [ Real.sqrt_eq_iff_mul_self_eq ] at * <;> try positivity;
        grind

lemma lemma_two_circles_contain_triangle (O1 O2 : Point) (r : ℝ)
  (h_dist_ge : dist O1 O2 >= Real.sqrt 3 / 2)
  (h_dist_le : dist O1 O2 <= r)
  (h_r : r >= 2) :
  ∃ T : Fin 3 → Point, regular_triangle_side_1 T ∧ (∀ i, dist (T i) O1 = r ∨ dist (T i) O2 = r) := by
    -- Let $R' = \sqrt{r^2 - 1/4}$.
    set R' : ℝ := Real.sqrt (r^2 - 1/4) with hR';
    -- Use `lemma_two_circles_contain_triangle_aux_intersection` to find $V$ on $C_1$ such that $dist(V, O_2) = R' + \sqrt{3}/2$.
    obtain ⟨V, hV⟩ : ∃ V : Point, dist V O1 = r ∧ dist V O2 = R' + Real.sqrt 3 / 2 := by
      apply_rules [ lemma_two_circles_contain_triangle_aux_intersection ];
    -- Let $M$ be the midpoint of $B_1 B_2$. We have $dist(M, O_2) = R'$ and $dist(M, V) = \sqrt{3}/2$.
    obtain ⟨M, B1, B2, hM, hB1, hB2, h_dist_M⟩ : ∃ M B1 B2 : Point, midpoint ℝ B1 B2 = M ∧ dist B1 B2 = 1 ∧ dist B1 O2 = r ∧ dist B2 O2 = r ∧ dist M O2 = R' ∧ dist M V = Real.sqrt 3 / 2 := by
      obtain ⟨M, hM⟩ : ∃ M : Point, M ∈ segment ℝ O2 V ∧ dist M O2 = R' ∧ dist M V = Real.sqrt 3 / 2 := by
        apply lemma_segment_partition O2 V R' (Real.sqrt 3 / 2) (by
        positivity) (by
        positivity) (by
        rw [ ← hV.2, dist_comm ]);
      have := @lemma_chord_from_midpoint O2 M r ?_ ?_ <;> norm_num at *;
      · grind +ring;
      · linarith;
      · linarith;
    -- To show that $V B_1 B_2$ is a regular unit triangle, we need to verify that $dist(V, B_1) = dist(V, B_2) = 1$.
    have h_dist_VB1 : dist V B1 = 1 := by
      have h_dist_VB1_sq : dist V B1 ^ 2 = dist V M ^ 2 + dist M B1 ^ 2 := by
        have h_perpendicular : (V 0 - M 0) * (B1 0 - M 0) + (V 1 - M 1) * (B1 1 - M 1) = 0 := by
          have h_collinear : V 0 * O2 1 + O2 0 * M 1 + M 0 * V 1 - V 0 * M 1 - M 0 * O2 1 - O2 0 * V 1 = 0 := by
            have h_collinear : (V 0 - O2 0) * (M 1 - O2 1) = (V 1 - O2 1) * (M 0 - O2 0) := by
              have h_dist_V_O2 : (V 0 - O2 0)^2 + (V 1 - O2 1)^2 = (R' + Real.sqrt 3 / 2)^2 := by
                rw [ ← hV.2, dist_eq_norm, EuclideanSpace.norm_eq ];
                norm_num [ Fin.sum_univ_two, Real.sq_sqrt ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ]
              have h_dist_M_O2 : (M 0 - O2 0)^2 + (M 1 - O2 1)^2 = R'^2 := by
                simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
                rw [ ← h_dist_M.2.1, Real.sq_sqrt ( by positivity ) ]
              have h_dist_M_V : (M 0 - V 0)^2 + (M 1 - V 1)^2 = (Real.sqrt 3 / 2)^2 := by
                convert congr_arg ( · ^ 2 ) h_dist_M.2.2 using 1 ; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf;
                rw [ Real.sq_sqrt ( by nlinarith only [ sq_nonneg ( M 0 - V 0 ), sq_nonneg ( M 1 - V 1 ) ] ) ]
              nlinarith only [ h_dist_V_O2, h_dist_M_O2, h_dist_M_V, Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ];
            linarith
          have h_symmetric : (B1 0 - M 0) * (O2 0 - M 0) + (B1 1 - M 1) * (O2 1 - M 1) = 0 := by
            norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
            rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> try linarith;
            · rw [ ← hM ] ; norm_num [ midpoint_eq_smul_add ] ; ring_nf;
              linarith;
            · exact Real.sqrt_pos.mpr ( by nlinarith only [ h_r ] );
          by_cases h_cases : O2 0 - M 0 = 0 ∧ O2 1 - M 1 = 0;
          · norm_num [ show M = O2 by ext i; fin_cases i <;> linarith! ] at *;
            exact absurd h_dist_M.2.1 ( by linarith [ Real.sqrt_pos.mpr ( show 0 < r ^ 2 - 1 / 4 by nlinarith ) ] );
          · grind;
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
        rw [ Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity ] ; linarith;
      -- Since $M$ is the midpoint of $B_1 B_2$, we have $dist(M, B_1) = dist(M, B_2) = 1/2$.
      have h_dist_MB1 : dist M B1 = 1 / 2 := by
        norm_num [ ← hM, dist_eq_norm ] at *;
        norm_num [ norm_smul, hB1 ];
        rwa [ norm_sub_rev ];
      rw [ ← sq_eq_sq₀ ] <;> norm_num [ h_dist_VB1_sq, h_dist_MB1, h_dist_M.2.2 ] ; ring_nf ; norm_num;
      rw [ show dist V M = Real.sqrt 3 / 2 by rw [ ← h_dist_M.2.2, dist_comm ] ] ; ring_nf ; norm_num;
    have h_dist_VB2 : dist V B2 = 1 := by
      simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
      norm_num [ Real.sqrt_eq_iff_mul_self_eq_of_pos ( show 0 < Real.sqrt 3 / 2 by positivity ), Real.sqrt_eq_iff_mul_self_eq_of_pos ( show 0 < Real.sqrt ( r^2 - 4⁻¹ ) by exact Real.sqrt_pos.mpr ( by norm_num; nlinarith ) ) ] at *;
      norm_num [ midpoint_eq_smul_add ] at *;
      norm_num [ ← hM ] at * ; ring_nf at * ; norm_num at * ; linarith;
    use ![V, B1, B2];
    unfold regular_triangle_side_1; simp_all +decide [ Fin.forall_fin_succ ] ;
    rw [ dist_comm, h_dist_VB2 ]

/-
The backward sequence of circles P_{-k}, Q_{-k} are red with radii r_{2k}.
-/
lemma lemma_backward_red_circles (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0)) :
  ∀ k : ℕ,
    let (Pk, Qk, _, _ ) := sequence_points_v2 P0 Q0 R0 S0 (-k)
    is_red_circle c Pk (r_seq (2 * k)) ∧ is_red_circle c Qk (r_seq (2 * k)) := by
      have h_reflected_induction : ∀ k : ℕ,
        let (Pk, Qk, Rk, Sk) := sequence_points_v2 (reflected_points P0 Q0 R0 S0).1 (reflected_points P0 Q0 R0 S0).2.1 (reflected_points P0 Q0 R0 S0).2.2.1 (reflected_points P0 Q0 R0 S0).2.2.2 k;
        is_red_circle c Pk (r_seq (2 * k)) ∧ is_red_circle c Qk (r_seq (2 * k)) ∧ is_red_circle c Rk (r_seq (2 * k + 1)) ∧ is_red_circle c Sk (r_seq (2 * k + 1)) := by
          apply_rules [ lemma_case3_induction ];
          convert lemma_reflected_no_red_copy c P0 Q0 R0 S0 h_no_red_config using 1;
      intro k
      specialize h_reflected_induction k
      simp_all +decide [ sequence_points_v2, reflected_points ];
      convert h_reflected_induction.2.1 |> fun h => And.intro h h_reflected_induction.1 using 2 <;> norm_num [ midpoint_eq_smul_add, reflection ] <;> ring_nf;
      · ext ; norm_num ; ring;
      · ext ; norm_num ; ring;

/-
The distance between P_k and P_{-k} is 2*k*|v|.
-/
lemma lemma_sequence_dist (P0 Q0 R0 S0 : Point) (k : ℕ) :
  let (Pk, _, _, _ ) := sequence_points_v2 P0 Q0 R0 S0 k
  let (Pk_neg, _, _, _) := sequence_points_v2 P0 Q0 R0 S0 (-k)
  let F := midpoint ℝ P0 Q0
  let M := midpoint ℝ R0 S0
  let v := 2 • (M - F)
  dist Pk Pk_neg = 2 * k * ‖v‖ := by
    unfold sequence_points_v2; norm_num [ dist_eq_norm, midpoint_eq_smul_add ] ; ring_nf;
    convert norm_smul ( k : ℝ ) ( 2 • ( ( 1 / 2 : ℝ ) • R0 + ( 1 / 2 : ℝ ) • S0 - ( ( 1 / 2 : ℝ ) • P0 + ( 1 / 2 : ℝ ) • Q0 ) ) + 2 • ( ( 1 / 2 : ℝ ) • R0 + ( 1 / 2 : ℝ ) • S0 - ( ( 1 / 2 : ℝ ) • P0 + ( 1 / 2 : ℝ ) • Q0 ) ) ) using 1 <;> norm_num ; ring_nf!;
    · norm_cast;
    · rw [ ← two_smul ℝ ] ; norm_num [ norm_smul ] ; ring;

/-
If 2*|v| < sqrt(3), then there exists k such that 2*k*|v| is in [sqrt(3)/2, r_seq(2k)].
-/
lemma lemma_large_k_exists_constrained (v : Point) (hv : v ≠ 0)
  (h_v_bound : 2 * ‖v‖ < Real.sqrt 3)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1) :
  ∃ k : ℕ,
    let d := 2 * (k : ℝ) * ‖v‖
    d ≥ Real.sqrt 3 / 2 ∧ d ≤ r_seq (2 * k) ∧ r_seq (2 * k) ≥ 2 := by
      -- By induction, we can show that $r_{2k}$ grows without bound as $k$ increases.
      have h_r_bound : ∀ k : ℕ, r_seq (2 * k) ≥ k + 1 := by
        intro k; induction k <;> simp_all +decide [ Nat.mul_succ ] ; ring_nf ; norm_num; (
        rename_i k hk; rw [ Nat.mul_comm k 2 ] ; ring_nf at *; norm_num at *; (
        rw [ Real.sq_sqrt ( by nlinarith [ h_ge_1 ( k * 2 ) ] ) ] ; ring_nf ; norm_num [ Real.le_sqrt, Real.sqrt_le_iff ] at * ; (
        -- By simplifying, we can see that the inequality holds for $k \geq 1$.
        have h_simplify : Real.sqrt (1 + Real.sqrt 3 * Real.sqrt (-1 + r_seq (k * 2) ^ 2 * 4) * 2 + r_seq (k * 2) ^ 2 * 4) ≥ 2 * k + 3 := by
          refine Real.le_sqrt_of_sq_le ?_ ; ring_nf at * ; norm_num at * ; (
          nlinarith [ show Real.sqrt 3 * Real.sqrt ( -1 + r_seq ( k * 2 ) ^ 2 * 4 ) ≥ 2 * k + 2 by rw [ ← Real.sqrt_mul <| by positivity ] ; exact Real.le_sqrt_of_sq_le <| by nlinarith [ show ( k : ℝ ) ≥ 0 by positivity ] ] ;)
        generalize_proofs at *; (
        nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ]));););
      obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * k * ‖v‖ ≥ Real.sqrt 3 / 2 ∧ 2 * k * ‖v‖ ≤ k + 1 := by
        have h_exists_k : ∃ k : ℕ, 2 * k * ‖v‖ ≥ Real.sqrt 3 / 2 ∧ 2 * k * ‖v‖ ≤ k + 1 := by
          have h_pos : 0 < ‖v‖ := by
            exact norm_pos_iff.mpr hv
          by_cases h_case : ‖v‖ ≤ 1 / 2;
          · exact ⟨ ⌈Real.sqrt 3 / 2 / ‖v‖⌉₊, by nlinarith [ Nat.le_ceil ( Real.sqrt 3 / 2 / ‖v‖ ), mul_div_cancel₀ ( Real.sqrt 3 / 2 ) h_pos.ne' ], by nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ Real.sqrt 3 / 2 / ‖v‖ by positivity ), mul_div_cancel₀ ( Real.sqrt 3 / 2 ) h_pos.ne' ] ⟩;
          · exact ⟨ 1, by norm_num; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ], by norm_num; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] ⟩;
        exact h_exists_k;
      exact ⟨ k, hk.1, hk.2.trans ( h_r_bound k ), by linarith [ show ( k : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hk; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] ) ), h_r_bound k ] ⟩

/-
Final contradiction for Case 3 (large distance subcase).
-/
lemma lemma3_case3_contradiction_final_v3_proof (c : Point → Color) (t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (R0 S0 R0' S0' : Point)
  (h_red_circles_1 : is_red_circle c R0 (r_seq 1) ∧ is_red_circle c S0 (r_seq 1))
  (h_red_circles'_1 : is_red_circle c R0' (r_seq 1) ∧ is_red_circle c S0' (r_seq 1))
  (_h_dist_R0_S0 : dist R0 S0 = t)
  (h_dist_S0_R0' : dist S0 R0' > r_seq 2 - Real.sqrt 3)
  (h_vec : R0' - S0' = S0 - R0)
  (h_no_red_pair : ¬ ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∀ i, q i = p i + (R0 - S0)) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1) :
  False := by
    -- Apply the lemma lemma3_case3_contradiction_final_v3_proven with the given hypotheses.
    apply lemma3_case3_contradiction_final_v3_proven c t h_blue R0 S0 R0' S0' h_red_circles_1 h_red_circles'_1 h_dist_S0_R0' h_vec h_no_red_pair h_r_seq_def h_ge_1

/-
Contradiction for Case 3 (small distance subcase).
-/
lemma lemma3_case3_small_dist_contradiction (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (v : Point)
  (hv_def : v = 2 • (midpoint ℝ P0 Q0 - midpoint ℝ R0 S0))
  (hv_nonzero : v ≠ 0)
  (hv_small : 2 * ‖v‖ < Real.sqrt 3) :
  False := by
    -- Use `lemma_large_k_exists_constrained` with $v$ to find $k$ such that $d = 2k\|v\| \in [\sqrt{3}/2, r_{seq}(2k)]$ and $r_{seq}(2k) \ge 2$.
    obtain ⟨k, hd, hrk⟩ : ∃ k : ℕ, let d := 2 * (k : ℝ) * ‖v‖; d ≥ Real.sqrt 3 / 2 ∧ d ≤ r_seq (2 * k) ∧ r_seq (2 * k) ≥ 2 := by
      apply_rules [ lemma_large_k_exists_constrained ];
    -- Apply `lemma_two_circles_contain_triangle` to $P_k, P_{-k}$ with radius $r_{seq}(2k)$.
    obtain ⟨T, hT⟩ : ∃ T : Fin 3 → Point, regular_triangle_side_1 T ∧ (∀ i, dist (T i) (sequence_points_v2 P0 Q0 R0 S0 k |>.1) = r_seq (2 * k) ∨ dist (T i) (sequence_points_v2 P0 Q0 R0 S0 (-k) |>.1) = r_seq (2 * k)) := by
      have h_dist : dist (sequence_points_v2 P0 Q0 R0 S0 k |>.1) (sequence_points_v2 P0 Q0 R0 S0 (-k) |>.1) = 2 * (k : ℝ) * ‖v‖ := by
        convert lemma_sequence_dist P0 Q0 R0 S0 k using 1 ; norm_num [ hv_def ] ; ring_nf!;
        exact Or.inl ( by rw [ ← norm_neg ] ; abel_nf ) ;
      apply_rules [ lemma_two_circles_contain_triangle ];
      · linarith;
      · linarith;
      · linarith;
    -- Since both circles are red, $T$ is red.
    have hT_red : ∀ i, c (T i) = Color.Red := by
      have hT_red : is_red_circle c (sequence_points_v2 P0 Q0 R0 S0 k |>.1) (r_seq (2 * k)) ∧ is_red_circle c (sequence_points_v2 P0 Q0 R0 S0 (-k) |>.1) (r_seq (2 * k)) := by
        apply And.intro;
        · apply (lemma_case3_induction c P0 Q0 R0 S0 h_blue h_no_red_config (by
          exact fun k => h_r_seq_def k) (by
          exact h_ge_1) h_red_0 k).left
        · apply (lemma_backward_red_circles c P0 Q0 R0 S0 h_blue h_no_red_config h_r_seq_def h_ge_1 h_red_0) k |>.1;
      intro i; specialize hT; specialize hT_red; cases hT.2 i <;> simp_all +decide [ is_red_circle ] ;
    -- Let $T' = T + (Q_0 - P_0)$.
    set T' : Fin 3 → Point := fun i => T i + (Q0 - P0);
    -- Show that $T'$ is red.
    have hT'_red : ∀ i, c (T' i) = Color.Red := by
      intro i
      have hT'_red_i : dist (T' i) (sequence_points_v2 P0 Q0 R0 S0 k |>.2.1) = r_seq (2 * k) ∨ dist (T' i) (sequence_points_v2 P0 Q0 R0 S0 (-k) |>.2.1) = r_seq (2 * k) := by
        convert hT.2 i using 1 <;> norm_num [ dist_eq_norm ];
        · unfold T' sequence_points_v2; norm_num [ midpoint_eq_smul_add ] ;
          rw [ show T i + ( Q0 - P0 ) - ( Q0 + k • 2 • ( ( 1 / 2 : ℝ ) • R0 + ( 1 / 2 : ℝ ) • S0 - ( ( 1 / 2 : ℝ ) • P0 + ( 1 / 2 : ℝ ) • Q0 ) ) ) = T i - ( P0 + k • 2 • ( ( 1 / 2 : ℝ ) • R0 + ( 1 / 2 : ℝ ) • S0 - ( ( 1 / 2 : ℝ ) • P0 + ( 1 / 2 : ℝ ) • Q0 ) ) ) by ext ; norm_num ; ring ];
        · unfold sequence_points_v2; norm_num; ring_nf;
          exact iff_of_eq ( by rw [ show T' i - ( Q0 + - ( k • 2 • ( midpoint ℝ R0 S0 - midpoint ℝ P0 Q0 ) ) ) = T i - ( P0 + - ( k • 2 • ( midpoint ℝ R0 S0 - midpoint ℝ P0 Q0 ) ) ) by ext ; norm_num [ T' ] ; ring ] );
      cases' hT'_red_i with hT'_red_i hT'_red_i <;> have := lemma_case3_induction c P0 Q0 R0 S0 h_blue h_no_red_config h_r_seq_def h_ge_1 h_red_0 k <;> have := lemma_backward_red_circles c P0 Q0 R0 S0 h_blue h_no_red_config h_r_seq_def h_ge_1 h_red_0 k <;> simp_all +decide [ is_red_circle ] ;
    apply h_no_red_config;
    -- Apply `lemma4` with configuration $\{P_0, Q_0, R_0, S_0\}$ and distance $a = dist(P_0, Q_0)$.
    have h_lemma4 : ∃ cfg' : Fin 4 → Point, Congruent (fun i => ![P0, Q0, R0, S0] i) cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
      apply lemma4;
      any_goals exact ‖Q0 - P0‖;
      · exact h_blue;
      · exact ⟨ 0, 1, by decide, by simp +decide [ dist_eq_norm' ] ⟩;
      · exact ⟨ T, T', hT.1, ⟨ Q0 - P0, rfl, fun i => rfl ⟩, hT_red, hT'_red ⟩;
    obtain ⟨ cfg', hcfg', hcfg'' ⟩ := h_lemma4; use cfg' 0, cfg' 1, cfg' 2, cfg' 3; simp_all +decide [ Fin.forall_fin_succ ] ;
    convert hcfg' using 1;
    exact funext fun i => by fin_cases i <;> rfl;

/-
The distance between $S_0$ and $R_0'$ is equal to the norm of $v$.
-/
lemma lemma_dist_S0_R0_prime (P0 Q0 R0 S0 : Point)
  (v : Point)
  (hv_def : v = 2 • (midpoint ℝ P0 Q0 - midpoint ℝ R0 S0)) :
  dist S0 (reflected_points P0 Q0 R0 S0).2.2.1 = ‖v‖ := by
    convert dist_eq_norm S0 ( reflection ( midpoint ℝ P0 Q0 ) R0 ) using 1;
    rw [ hv_def, reflection ];
    norm_num [ two_smul, midpoint_eq_smul_add ] ; ring_nf;
    rw [ ← norm_neg ] ; congr ; ext ; norm_num ; ring;

/-
Under Case 3 conditions, R0, S0, R0', S0' are red circles of radius sqrt(3).
-/
lemma lemma_case3_red_circles_sqrt3 (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_P0_blue : c P0 = Color.Blue)
  (h_Q0_blue : c Q0 = Color.Blue)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_r_seq_0 : r_seq 0 = 1)
  (h_r_seq_1 : r_seq 1 = Real.sqrt 3) :
  is_red_circle c R0 (Real.sqrt 3) ∧ is_red_circle c S0 (Real.sqrt 3) ∧
  is_red_circle c (reflected_points P0 Q0 R0 S0).2.2.1 (Real.sqrt 3) ∧
  is_red_circle c (reflected_points P0 Q0 R0 S0).2.2.2 (Real.sqrt 3) := by
    -- Apply the lemma_step_1_gen with k=0 and r=1 to conclude that R0 and S0 are red circles of radius sqrt(3).
    have h_red_R0_S0 : is_red_circle c R0 (Real.sqrt 3) ∧ is_red_circle c S0 (Real.sqrt 3) := by
      have h_red_R0_S0 : ∀ X, dist X P0 = 1 → c X = Color.Red ∧ dist X Q0 = 1 → c X = Color.Red := by
        tauto;
      have h_red_R0_S0 : is_red_circle c P0 1 ∧ is_red_circle c Q0 1 := by
        constructor <;> intro X hX <;> simp_all +decide;
        · cases h : c X <;> specialize h_blue X P0 hX <;> aesop;
        · cases h : c X <;> specialize h_blue _ _ hX <;> aesop;
      have := lemma_step_1_gen c P0 Q0 R0 S0 0 1 h_blue h_no_red_config ( fun k => ?_ ) ( fun k => ?_ ) P0 Q0 R0 S0 ?_ h_red_R0_S0.1 h_red_R0_S0.2 ?_ <;> norm_num at *;
      · exact this;
      · exact h_r_seq_def k;
      · exact h_ge_1 k;
      · unfold sequence_points; aesop;
    have h_red_R0'_S0'_v3 := @lemma_reflected_red_sqrt3;
    specialize h_red_R0'_S0'_v3 c P0 Q0 R0 S0 h_blue h_no_red_config (fun k => h_r_seq_def k) (fun k => h_ge_1 k) (by
    exact ⟨ fun P hP => Or.resolve_left ( by cases h : c P <;> tauto ) fun hP' => h_blue P P0 hP ⟨ hP', h_P0_blue ⟩, fun P hP => Or.resolve_left ( by cases h : c P <;> tauto ) fun hP' => h_blue P Q0 hP ⟨ hP', h_Q0_blue ⟩ ⟩);
    aesop

/-
Contradiction for Case 3 (large distance subcase).
-/
lemma lemma_case3_large_dist_contradiction (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_P0_blue : c P0 = Color.Blue)
  (h_Q0_blue : c Q0 = Color.Blue)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k)^2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_r_seq_0 : r_seq 0 = 1)
  (h_r_seq_1 : r_seq 1 = Real.sqrt 3)
  (v : Point)
  (hv_def : v = 2 • (midpoint ℝ P0 Q0 - midpoint ℝ R0 S0))
  (hv_large : ‖v‖ ≥ Real.sqrt 3 / 2) :
  False := by
    -- Apply `lemma_case3_red_circles_sqrt3` to show that $R_0, S_0, R_0', S_0'$ are red circles of radius $\sqrt{3}$ (which is $r_{seq}(1)$).
    have h_red_circles_sqrt3 : is_red_circle c R0 (Real.sqrt 3) ∧ is_red_circle c S0 (Real.sqrt 3) ∧ is_red_circle c (reflected_points P0 Q0 R0 S0).2.2.1 (Real.sqrt 3) ∧ is_red_circle c (reflected_points P0 Q0 R0 S0).2.2.2 (Real.sqrt 3) := by
      apply_rules [ lemma_case3_red_circles_sqrt3 ]
    generalize_proofs at *; (
    -- Apply `lemma_dist_S0_R0_prime` to show $dist(S_0, R_0') = \|v\|$.
    have h_dist_S0_R0_prime : dist S0 (reflected_points P0 Q0 R0 S0).2.2.1 = ‖v‖ := by
      convert lemma_dist_S0_R0_prime P0 Q0 R0 S0 v hv_def using 1
    generalize_proofs at *; (
    -- Apply `lemma_case3_large_dist_inequality` to show $\|v\| > r_{seq}(2) - \sqrt{3}$.
    have h_dist_S0_R0_prime_gt : ‖v‖ > r_seq 2 - Real.sqrt 3 := by
      rw [ h_r_seq_def, h_r_seq_1 ] ; norm_num ; ring_nf ; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sqrt_nonneg 11, Real.sq_sqrt ( show 0 ≤ 11 by norm_num ), mul_inv_cancel₀ ( show Real.sqrt 3 ≠ 0 by norm_num ) ] ;
    generalize_proofs at *; (
    -- Apply `lemma3_case3_contradiction_final_v3` with `t = dist R0 S0`.
    apply lemma3_case3_contradiction_final_v3_proof c (dist R0 S0) h_blue R0 S0 (reflected_points P0 Q0 R0 S0).2.2.1 (reflected_points P0 Q0 R0 S0).2.2.2
    generalize_proofs at *; (
    grind);
    any_goals assumption;
    · aesop ( simp_config := { singlePass := true } ) ;
    · rfl;
    · linarith! [ h_r_seq_def 0, h_r_seq_def 1, h_r_seq_def 2 ] ;
    · unfold reflected_points; norm_num [ midpoint_eq_smul_add ] ; ring_nf;
      unfold reflection; norm_num [ sub_eq_add_neg ] ; ring_nf;
      ext ; norm_num ; ring;
    · intro h
      obtain ⟨p, q, hp, hq, hp_red, hq_red⟩ := h
      have h_contradiction : ∃ (p' q' r' s' : Point), Congruent (fun i => ![P0, Q0, R0, S0] i) (fun i => ![p', q', r', s'] i) ∧ c p' = Color.Red ∧ c q' = Color.Red ∧ c r' = Color.Red ∧ c s' = Color.Red := by
        have := @lemma4
        generalize_proofs at *; (
        specialize this c (dist R0 S0) (fun i => ![P0, Q0, R0, S0] i) h_blue ⟨2, 3, by decide, rfl⟩ ⟨p, q, hp, ⟨R0 - S0, by
          exact rfl, hq⟩, hp_red, hq_red⟩
        generalize_proofs at *; (
        obtain ⟨ cfg', hcfg', hcfg'' ⟩ := this; use cfg' 0, cfg' 1, cfg' 2, cfg' 3; simp_all +decide [ Fin.forall_fin_succ ] ;
        convert hcfg' using 1
        generalize_proofs at *; (
        exact funext fun i => by fin_cases i <;> rfl;)))
      generalize_proofs at *; (
      exact h_no_red_config h_contradiction))))

/-
If a permuted isometric copy of a configuration has a red copy, then the original configuration has a red copy.
-/
lemma lemma_permutation_congruence (c : Point → Color) (cfg : Fin 4 → Point)
  (i j k l : Fin 4) (h_perm : {i, j, k, l} = ({0, 1, 2, 3} : Finset (Fin 4)))
  (P0 Q0 R0 S0 : Point)
  (f : Point ≃ᵃⁱ[ℝ] Point)
  (hP0 : P0 = f (cfg i)) (hQ0 : Q0 = f (cfg j)) (hR0 : R0 = f (cfg k)) (hS0 : S0 = f (cfg l))
  (h_red_copy : ∃ (p q r s : Point),
    Congruent (fun i => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ m, c (cfg' m) = Color.Red := by
    simp_all +decide [Finset.ext_iff];
    obtain ⟨ p, q, r, s, h₁, h₂, h₃, h₄, h₅ ⟩ := h_red_copy; use fun m => if m = i then p else if m = j then q else if m = k then r else s; simp_all +decide [ Congruent ] ;
    refine' ⟨ fun i₁ i₂ => _, fun m => _ ⟩;
    · -- Since $P0, Q0, R0, S0$ is a permutation of $cfg$, we can express the edist between $cfg i₁$ and $cfg i₂$ in terms of the edist between the corresponding points in $P0, Q0, R0, S0$.
      have h_perm_edist : edist (cfg i₁) (cfg i₂) = edist (![f (cfg i), f (cfg j), f (cfg k), f (cfg l)] (if i₁ = i then 0 else if i₁ = j then 1 else if i₁ = k then 2 else 3)) (![f (cfg i), f (cfg j), f (cfg k), f (cfg l)] (if i₂ = i then 0 else if i₂ = j then 1 else if i₂ = k then 2 else 3)) := by
        have h_perm_edist : ∀ m : Fin 4, cfg m = f.symm (![f (cfg i), f (cfg j), f (cfg k), f (cfg l)] (if m = i then 0 else if m = j then 1 else if m = k then 2 else 3)) := by
          intro m; specialize h_perm m; fin_cases m <;> simp +decide at h_perm ⊢ <;> aesop;
        rw [ h_perm_edist i₁, h_perm_edist i₂ ] ; simp +decide [ edist_dist ] ;
      aesop;
    · split_ifs <;> tauto

/-
Proof of Case 3.
-/
lemma lemma_case3 (c : Point → Color) (cfg : Fin 4 → Point)
  (h_blue : ∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_case3 : Case3 c cfg) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
    revert h_case3;
    unfold Case3;
    intro h;
    obtain ⟨ i, j, k, l, h₁, ⟨ P_blue, Q_blue, hP, hQ, h_dist ⟩, h₂ ⟩ := h;
    -- Apply `exists_isometry_mapping_pair` to find an isometry $f$ such that $f(cfg(i)) = P_blue$ and $f(cfg(j)) = Q_blue$.
    obtain ⟨f, hf⟩ : ∃ f : Point ≃ᵃⁱ[ℝ] Point, f (cfg i) = P_blue ∧ f (cfg j) = Q_blue := by
      convert exists_isometry_mapping_pair ( cfg i ) ( cfg j ) P_blue Q_blue _ using 1;
      exact h_dist.symm;
    -- Define $P_0 = P_blue$, $Q_0 = Q_blue$, $R_0 = f(cfg(k))$, $S_0 = f(cfg(l))$.
    set P0 := P_blue
    set Q0 := Q_blue
    set R0 := f (cfg k)
    set S0 := f (cfg l);
    by_cases h_no_red_config : ¬∃ p q r s : Point, Congruent (fun i => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧ c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red;
    · -- Since $P_0, Q_0$ are blue, $\gamma_{P_0}(1)$ and $\gamma_{Q_0}(1)$ are red (by `h_blue`).
      have h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0) := by
        have h_red_0 : is_red_circle c P0 1 ∧ is_red_circle c Q0 1 := by
          unfold is_red_circle;
          exact ⟨ fun P hP' => Or.resolve_left ( by cases h : c P <;> aesop ) fun hP'' => h_blue _ _ hP' ⟨ hP'', hP ⟩, fun P hP' => Or.resolve_left ( by cases h : c P <;> aesop ) fun hP'' => h_blue _ _ hP' ⟨ hP'', hQ ⟩ ⟩;
        convert h_red_0 using 1;
      -- Let $F = midpoint(P_0, Q_0)$ and $M = midpoint(R_0, S_0)$.
      set F := midpoint ℝ P0 Q0
      set M := midpoint ℝ R0 S0
      set v := 2 • (F - M);
      by_cases hv : ‖v‖ ≥ Real.sqrt 3 / 2;
      · apply False.elim;
        apply lemma_case3_large_dist_contradiction c P0 Q0 R0 S0 h_blue h_no_red_config hP hQ (fun k => by
          exact rfl) (fun k => by
          induction' k with k ih;
          · exact le_rfl;
          · exact le_div_iff₀' ( by positivity ) |>.2 ( by nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sqrt_nonneg ( 4 * r_seq k ^ 2 - 1 ), Real.sq_sqrt ( show 0 ≤ 4 * r_seq k ^ 2 - 1 by nlinarith ) ] )) (by
        exact rfl) (by
        exact show r_seq 1 = Real.sqrt 3 from by rw [ show r_seq 1 = ( Real.sqrt ( 4 * r_seq 0 ^ 2 - 1 ) + Real.sqrt 3 ) / 2 from rfl ] ; norm_num [ show r_seq 0 = 1 from rfl ] ;) v (by
        rfl) hv;
      · -- Since $v \neq 0$, we have $2 * ‖v‖ < \sqrt{3}$.
        have hv_nonzero : v ≠ 0 := by
          contrapose! h₂; simp_all +decide [ segments_bisect ] ;
          have h_midpoint_eq : midpoint ℝ (f (cfg i)) (f (cfg j)) = midpoint ℝ (f (cfg k)) (f (cfg l)) := by
            simp +zetaDelta at *;
            rw [ hf.1, hf.2, sub_eq_zero.mp h₂ ];
          have h_midpoint_eq : f (midpoint ℝ (cfg i) (cfg j)) = f (midpoint ℝ (cfg k) (cfg l)) := by
            convert h_midpoint_eq using 1;
            · exact f.map_midpoint _ _;
            · exact f.map_midpoint _ _;
          exact f.injective h_midpoint_eq;
        have := lemma3_case3_small_dist_contradiction c P0 Q0 R0 S0 h_blue h_no_red_config h_red_0 ( show ∀ k, r_seq ( k + 1 ) = ( Real.sqrt ( 4 * ( r_seq k ) ^ 2 - 1 ) + Real.sqrt 3 ) / 2 from fun k => ?_ ) ( show ∀ k, 1 ≤ r_seq k from fun k => ?_ ) v ( show v = 2 • ( F - M ) from rfl ) hv_nonzero ( by linarith );
        · contradiction;
        · exact rfl;
        · field_simp;
          exact lemma_r_seq_ge_1 k (congrFun rfl);
    · apply lemma_permutation_congruence c cfg i j k l h₁ P0 Q0 R0 S0 f hf.left.symm hf.right.symm rfl rfl (by push_neg at h_no_red_config; exact h_no_red_config)

/-
Theorem 1 for distinct configurations.
-/
lemma theorem_1_distinct (c : Point → Color) (cfg : Fin 4 → Point)
  (h_blue : ∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_inj : Function.Injective cfg) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
    have h_cases := lemma_cases_exhaustive c cfg h_inj
    rcases h_cases with h1 | h2 | h3
    · apply lemma_case1 c cfg h1
    · apply lemma_case2_proven c cfg h_blue h2
    · apply lemma_case3 c cfg h_blue h3

/-
Any configuration of 4 points can be extended to a configuration of 4 distinct points.
-/
lemma lemma_config_extension (cfg : Fin 4 → Point) :
  ∃ (cfg' : Fin 4 → Point), Function.Injective cfg' ∧ (Set.range cfg ⊆ Set.range cfg') := by
    -- Let $S = range(cfg)$. Since the domain is finite, $S$ is finite and $|S| \le 4$. Since the plane is infinite (or at least has more than 4 points), we can find a set $S'$ such that $S \subseteq S'$ and $|S'| = 4$.
    obtain ⟨S', hS'⟩ : ∃ S' : Finset Point, S'.card = 4 ∧ ∀ x ∈ Set.range cfg, x ∈ S' := by
      by_contra h_contra;
      -- Since $S$ is finite, we can choose $4 - |S|$ additional points from the plane to form a set $S'$ with $|S'| = 4$.
      obtain ⟨S', hS'⟩ : ∃ S' : Finset Point, S'.card = 4 - (Finset.image cfg Finset.univ).card ∧ ∀ x ∈ S', x ∉ Finset.image cfg Finset.univ := by
        have h_infinite : Set.Infinite {x : Point | x∉Finset.image cfg Finset.univ} := by
          have h_infinite : Set.Infinite (Set.univ : Set Point) := by
            exact Set.infinite_univ_iff.mpr ( by exact Infinite.of_injective ( fun x => EuclideanSpace.single 0 x ) fun x y hxy => by simpa using congr_fun hxy 0 );
          exact Set.Infinite.diff h_infinite ( Finset.finite_toSet ( Finset.image cfg Finset.univ ) ) |> Set.Infinite.mono fun x hx => by aesop;
        have := h_infinite.exists_subset_card_eq ( 4 - Finset.card ( Finset.image cfg Finset.univ ) ) ; tauto;
      refine' h_contra ⟨ S' ∪ Finset.image cfg Finset.univ, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
      rw [ Nat.sub_add_cancel ( show ( Finset.image cfg Finset.univ ).card ≤ 4 from Finset.card_image_le.trans ( by decide ) ) ];
    -- Let $cfg'$ be a bijection from $Fin 4$ to $S'$.
    obtain ⟨cfg', hcfg'⟩ : ∃ cfg' : Fin 4 ≃ S', True := by
      exact ⟨ Fintype.equivOfCardEq ( by aesop ), trivial ⟩;
    exact ⟨ fun i => cfg' i |>.1, Subtype.coe_injective.comp cfg'.injective, fun x hx => by rcases hS'.2 x hx with hx'; exact ⟨ cfg'.symm ⟨ x, hx' ⟩, by simp +decide ⟩ ⟩

/-
Theorem 1: Any configuration of 4 points has a red copy.
-/
theorem theorem_1 (c : Point → Color) (cfg : Fin 4 → Point)
  (h_blue : ∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue)) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
    -- Apply the lemma_config_extension to extend `cfg` to an injective configuration `cfg_ext`.
    obtain ⟨cfg_ext, hcfg_ext_inj, hcfg_ext_range⟩ := lemma_config_extension cfg;
    -- Apply theorem_1_distinct to cfg_ext to get a red configuration cfg_ext_red congruent to cfg_ext via isometry f.
    obtain ⟨cfg_ext_red, hcfg_ext_red_congr, hcfg_ext_red_red⟩ := theorem_1_distinct c cfg_ext h_blue hcfg_ext_inj;
    -- Define cfg' as cfg_ext_red composed with the function that maps i to j where cfg i = cfg_ext j.
    obtain ⟨f, hf⟩ : ∃ f : Fin 4 → Fin 4, ∀ i, cfg i = cfg_ext (f i) := by
      exact ⟨ fun i => Classical.choose ( hcfg_ext_range ( Set.mem_range_self i ) ), fun i => Eq.symm ( Classical.choose_spec ( hcfg_ext_range ( Set.mem_range_self i ) ) ) ⟩;
    unfold Congruent at *; aesop;

#print axioms theorem_1
