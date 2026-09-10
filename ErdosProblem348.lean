import Mathlib

/-!
In a preprint posted by Jesse Geneson, a solution of Erdőss Problem #348
(https://www.erdosproblems.com/348) is given, showing that for any sequence `A`
of positive integers for which `A \ {a, b}` is complete for any two elements
`a, b ∈ A`, one can find arbitrarily large finite subsets `S ⊆ A` such that `A \ S`
is still complete.

https://www.researchgate.net/publication/414128757_Deletion_thresholds_for_complete_sequences

Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) managed to formalize 
the proof, which can be found below.

Lean version: leanprover/lean4:v4.28.0
-/

open Finset

/-- `FS X` is the set of sums of finite subsets of `X`. -/
def FS (X : Set ℕ) : Set ℕ := {n | ∃ F : Finset ℕ, ↑F ⊆ X ∧ ∑ x ∈ F, x = n}

/-- `X ⊆ ℕ` is *complete* if every sufficiently large natural number lies in `FS X`. -/
def Complete (X : Set ℕ) : Prop := ∃ T : ℕ, ∀ n, T ≤ n → n ∈ FS X

lemma zero_mem_FS (X : Set ℕ) : 0 ∈ FS X := ⟨∅, by simp, by simp⟩

/-- Monotonicity of `FS`. -/
lemma FS_mono {X Y : Set ℕ} (h : X ⊆ Y) : FS X ⊆ FS Y := by
  rintro n ⟨F, hF, rfl⟩
  exact ⟨F, hF.trans h, rfl⟩

/-- A superset of a complete set is complete. -/
lemma Complete.mono {X Y : Set ℕ} (hX : Complete X) (h : X ⊆ Y) : Complete Y := by
  obtain ⟨T, hT⟩ := hX
  exact ⟨T, fun n hn => FS_mono h (hT n hn)⟩

lemma mem_FS_self {X : Set ℕ} {x : ℕ} (hx : x ∈ X) : x ∈ FS X :=
  ⟨{x}, by simpa using hx, by simp⟩

/-- An element of `FS ↑G` is bounded by the sum over the finset `G`. -/
lemma FS_finset_le {G : Finset ℕ} {n : ℕ} (hn : n ∈ FS ↑G) : n ≤ ∑ x ∈ G, x := by
  obtain ⟨F, hF, rfl⟩ := hn
  exact Finset.sum_le_sum_of_subset (by exact_mod_cast hF)

/-- Every element of `FS X` for finite `X` is bounded by the total sum. -/
lemma FS_le_of_finite {X : Set ℕ} (hX : X.Finite) {n : ℕ} (hn : n ∈ FS X) :
    n ≤ ∑ x ∈ hX.toFinset, x := by
  obtain ⟨F, hF, rfl⟩ := hn
  refine Finset.sum_le_sum_of_subset ?_
  intro x hx
  simpa using hF hx

/-- Every complete subset of `ℕ` is infinite. -/
lemma Complete.infinite {X : Set ℕ} (hX : Complete X) : X.Infinite := by
  by_contra hcon
  rw [Set.not_infinite] at hcon
  set hfin := hcon
  obtain ⟨T, hT⟩ := hX
  set N := ∑ x ∈ hfin.toFinset, x with hN
  have := FS_le_of_finite hfin (hT (max T (N + 1)) (le_max_left _ _))
  have h2 : N + 1 ≤ max T (N + 1) := le_max_right _ _
  omega

/-- Splitting finite sums along a disjoint union. -/
lemma FS_union_disjoint {Y Z : Set ℕ} (h : Disjoint Y Z) :
    FS (Y ∪ Z) = {n | ∃ a ∈ FS Y, ∃ b ∈ FS Z, a + b = n} := by
  ext n
  constructor
  · rintro ⟨F, hF, rfl⟩
    classical
    refine ⟨∑ x ∈ F.filter (· ∈ Y), x, ⟨F.filter (· ∈ Y), ?_, rfl⟩,
      ∑ x ∈ F.filter (fun x => x ∉ Y), x, ⟨F.filter (fun x => x ∉ Y), ?_, rfl⟩, ?_⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      exact hx.2
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      rcases hF hx.1 with h1 | h1
      · exact absurd h1 hx.2
      · exact h1
    · rw [← Finset.sum_filter_add_sum_filter_not F (· ∈ Y)]
  · rintro ⟨a, ⟨F, hF, rfl⟩, b, ⟨G, hG, rfl⟩, rfl⟩
    classical
    have hdisj : Disjoint F G := by
      rw [Finset.disjoint_left]
      intro x hxF hxG
      exact Set.disjoint_left.mp h (hF hxF) (hG hxG)
    exact ⟨F ∪ G, by
      simpa using Set.union_subset (hF.trans Set.subset_union_left)
        (hG.trans Set.subset_union_right), by
      rw [Finset.sum_union hdisj]⟩

/-! ### Prefixes -/

open Classical in
/-- `pre X m` is the finite set of elements of `X` strictly below `m`. -/
noncomputable def pre (X : Set ℕ) (m : ℕ) : Finset ℕ := (Finset.range m).filter (· ∈ X)

@[simp] lemma mem_pre {X : Set ℕ} {m y : ℕ} : y ∈ pre X m ↔ y ∈ X ∧ y < m := by
  classical
  simp [pre, and_comm]

lemma pre_coe (X : Set ℕ) (m : ℕ) : (↑(pre X m) : Set ℕ) = {x | x ∈ X ∧ x < m} := by
  ext y; simp

/-- `Ssum X m` is the sum of the elements of `X` below `m`. -/
noncomputable def Ssum (X : Set ℕ) (m : ℕ) : ℕ := ∑ x ∈ pre X m, x

/-- `Pset X m` is the set of subset sums of the elements of `X` below `m`. -/
def Pset (X : Set ℕ) (m : ℕ) : Set ℕ := FS {x | x ∈ X ∧ x < m}

lemma Pset_eq_FS_pre (X : Set ℕ) (m : ℕ) : Pset X m = FS ↑(pre X m) := by
  rw [Pset, pre_coe]

lemma pre_mono {X : Set ℕ} {m m' : ℕ} (h : m ≤ m') : pre X m ⊆ pre X m' := by
  intro x hx; simp only [mem_pre] at hx ⊢; exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

lemma Ssum_mono {X : Set ℕ} {m m' : ℕ} (h : m ≤ m') : Ssum X m ≤ Ssum X m' :=
  Finset.sum_le_sum_of_subset (pre_mono h)

lemma Pset_mono {X : Set ℕ} {m m' : ℕ} (h : m ≤ m') : Pset X m ⊆ Pset X m' :=
  FS_mono (fun _ hx => ⟨hx.1, lt_of_lt_of_le hx.2 h⟩)

lemma Pset_subset_FS (X : Set ℕ) (m : ℕ) : Pset X m ⊆ FS X :=
  FS_mono (fun _ hx => hx.1)

@[simp] lemma Ssum_zero (X : Set ℕ) : Ssum X 0 = 0 := by simp [Ssum, pre]

/-- Adding one element to a prefix. -/
lemma Ssum_succ_of_mem {X : Set ℕ} {a : ℕ} (ha : a ∈ X) :
    Ssum X (a + 1) = Ssum X a + a := by
  classical
  have : pre X (a + 1) = insert a (pre X a) := by
    ext y
    simp only [mem_pre, Finset.mem_insert]
    constructor
    · rintro ⟨hy, hlt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
      · exact Or.inr ⟨hy, h⟩
      · exact Or.inl h
    · rintro (rfl | ⟨hy, hlt⟩)
      · exact ⟨ha, by omega⟩
      · exact ⟨hy, by omega⟩
  rw [Ssum, this, Finset.sum_insert (by simp), Ssum]
  omega

lemma Ssum_succ_of_notMem {X : Set ℕ} {a : ℕ} (ha : a ∉ X) :
    Ssum X (a + 1) = Ssum X a := by
  have : pre X (a + 1) = pre X a := by
    ext y
    simp only [mem_pre]
    constructor
    · rintro ⟨hy, hlt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
      · exact ⟨hy, h⟩
      · exact absurd (h ▸ hy) ha
    · rintro ⟨hy, hlt⟩; exact ⟨hy, by omega⟩
  rw [Ssum, this, Ssum]

/-- If `a ∈ X` and `a < m` then the prefix at `m` picks up `a`. -/
lemma Ssum_add_le {X : Set ℕ} {a m : ℕ} (ha : a ∈ X) (h : a < m) :
    Ssum X a + a ≤ Ssum X m := by
  calc Ssum X a + a = Ssum X (a + 1) := (Ssum_succ_of_mem ha).symm
  _ ≤ Ssum X m := Ssum_mono h

/-- Reflection inside a prefix. -/
lemma Pset_reflect {X : Set ℕ} {m x : ℕ} (hx : x ∈ Pset X m) :
    x ≤ Ssum X m ∧ Ssum X m - x ∈ Pset X m := by
  classical
  rw [Pset_eq_FS_pre] at hx ⊢
  obtain ⟨G, hG, rfl⟩ := hx
  have hGsub : G ⊆ pre X m := by exact_mod_cast hG
  have hle : ∑ x ∈ G, x ≤ Ssum X m := Finset.sum_le_sum_of_subset hGsub
  refine ⟨hle, ⟨pre X m \ G, by exact_mod_cast Finset.sdiff_subset, ?_⟩⟩
  have h2 : ∑ x ∈ pre X m \ G, x + ∑ x ∈ G, x = Ssum X m := Finset.sum_sdiff hGsub
  omega

lemma le_Ssum_of_mem_Pset {X : Set ℕ} {m x : ℕ} (hx : x ∈ Pset X m) : x ≤ Ssum X m :=
  (Pset_reflect hx).1

lemma Pset_reflect' {X : Set ℕ} {m x : ℕ} (hx : x ∈ Pset X m) :
    Ssum X m - x ∈ Pset X m := (Pset_reflect hx).2

/-- If `x` is a finite subset sum of `X` and every element of `X` at least `m`
already exceeds `x`, then `x` is a subset sum of the prefix below `m`. -/
lemma mem_Pset_of_mem_FS {X : Set ℕ} {m x : ℕ} (hx : x ∈ FS X)
    (h : ∀ y ∈ X, m ≤ y → x < y) : x ∈ Pset X m := by
  obtain ⟨F, hF, rfl⟩ := hx
  refine ⟨F, ?_, rfl⟩
  intro y hy
  refine ⟨hF hy, ?_⟩
  by_contra hlt
  push_neg at hlt
  have := h y (hF hy) hlt
  have hle : y ≤ ∑ x ∈ F, x := Finset.single_le_sum (f := fun x => x) (by simp) hy
  omega

/-- Extending a prefix representation by the element `a`. -/
lemma mem_Pset_add_elt {X : Set ℕ} {a x : ℕ} (ha : a ∈ X) (hx : x ∈ Pset X a) :
    x + a ∈ Pset X (a + 1) := by
  classical
  rw [Pset_eq_FS_pre] at hx
  obtain ⟨G, hG, rfl⟩ := hx
  have hGsub : G ⊆ pre X a := by exact_mod_cast hG
  have hanot : a ∉ G := fun h => by simpa using (mem_pre.mp (hGsub h)).2
  refine ⟨insert a G, ?_, ?_⟩
  · intro y hy
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hy
    rcases hy with rfl | hy
    · exact ⟨ha, by omega⟩
    · have := mem_pre.mp (hGsub hy)
      exact ⟨this.1, by omega⟩
  · rw [Finset.sum_insert hanot]; omega

/-! ### Prefix slack -/

/-- The prefix slack of `X` tends to infinity. -/
def SlackDiv (X : Set ℕ) : Prop := ∀ C : ℕ, ∃ M : ℕ, ∀ a ∈ X, M ≤ a → a + C ≤ Ssum X a

/-- For an infinite `X`, the prefix sums tend to infinity. -/
lemma Ssum_large {X : Set ℕ} (hX : X.Infinite) (B : ℕ) :
    ∃ M : ℕ, ∀ m, M ≤ m → B ≤ Ssum X m := by
  obtain ⟨a, haX, ha⟩ := hX.exists_gt B
  refine ⟨a + 1, fun m hm => ?_⟩
  have h1 : Ssum X a + a ≤ Ssum X m := by
    calc Ssum X a + a = Ssum X (a + 1) := (Ssum_succ_of_mem haX).symm
    _ ≤ Ssum X m := Ssum_mono hm
  omega

/-- The prefix below `a` with the element `x` removed. -/
lemma sum_pre_erase {X : Set ℕ} {a x : ℕ} (hx : x ∈ X) (hxa : x < a) :
    ∑ y ∈ (pre X a).erase x, y + x = Ssum X a := by
  classical
  have hmem : x ∈ pre X a := mem_pre.mpr ⟨hx, hxa⟩
  have h3 : x + ∑ y ∈ (pre X a).erase x, y = ∑ y ∈ pre X a, y := by
    simpa using Finset.add_sum_erase (pre X a) (fun y : ℕ => y) hmem
  rw [Ssum]
  omega

/-- One-term deletions force diverging slack. -/
theorem slackDiv_of_one_deletions {X : Set ℕ} (hX : X.Infinite)
    (h : ∀ x ∈ X, Complete (X \ {x})) : SlackDiv X := by
  classical
  intro C
  obtain ⟨x, hxX, hxC⟩ := hX.exists_gt C
  obtain ⟨T, hT⟩ := h x hxX
  obtain ⟨M₀, hM₀⟩ := Ssum_large hX (T + x)
  refine ⟨max M₀ (x + 1), fun a haX ha => ?_⟩
  have hxa : x < a := by omega
  have hsum : T + x ≤ Ssum X a := hM₀ a (by omega)
  set A := ∑ y ∈ (pre X a).erase x, y with hA
  have hAx : A + x = Ssum X a := sum_pre_erase hxX hxa
  have hAT : T ≤ A + 1 := by omega
  obtain ⟨F, hF, hFsum⟩ := hT (A + 1) hAT
  -- some element of `F` must be at least `a`
  have hex : ∃ y ∈ F, a ≤ y := by
    by_contra hcon
    push_neg at hcon
    have hsub : F ⊆ (pre X a).erase x := by
      intro y hy
      have hyX : y ∈ X ∧ y ∉ ({x} : Set ℕ) := hF hy
      refine Finset.mem_erase.mpr ⟨?_, mem_pre.mpr ⟨hyX.1, hcon y hy⟩⟩
      simpa using hyX.2
    have : ∑ y ∈ F, y ≤ A := Finset.sum_le_sum_of_subset hsub
    omega
  obtain ⟨y, hyF, hya⟩ := hex
  have hyle : y ≤ ∑ z ∈ F, z := Finset.single_le_sum (f := fun z => z) (by simp) hyF
  omega

/-- Finite deletion preserves diverging slack. -/
theorem slackDiv_diff_finite {X : Set ℕ} (h : SlackDiv X) (D : Finset ℕ) :
    SlackDiv (X \ ↑D) := by
  classical
  intro C
  obtain ⟨M, hM⟩ := h (C + ∑ d ∈ D, d)
  refine ⟨M, fun a ha hMa => ?_⟩
  have haX : a ∈ X := ha.1
  have h1 : a + (C + ∑ d ∈ D, d) ≤ Ssum X a := hM a haX hMa
  have hpre : pre (X \ ↑D) a = (pre X a) \ D := by
    ext y
    simp only [mem_pre, Finset.mem_sdiff, Set.mem_diff, Finset.mem_coe]
    tauto
  have h2 : Ssum X a ≤ Ssum (X \ ↑D) a + ∑ d ∈ D, d := by
    simp only [Ssum, hpre]
    have hsplit : ∑ y ∈ (pre X a) \ D, y + ∑ y ∈ (pre X a) ∩ D, y = ∑ y ∈ pre X a, y := by
      rw [← Finset.sdiff_inter_self_left (pre X a) D]
      exact Finset.sum_sdiff Finset.inter_subset_left
    have hinter : ∑ y ∈ (pre X a) ∩ D, y ≤ ∑ d ∈ D, d :=
      Finset.sum_le_sum_of_subset Finset.inter_subset_right
    omega
  omega

/-! ### Successor element and rounding up a cut value -/

/-- The least element of `X` strictly greater than `a`. -/
noncomputable def nxt (X : Set ℕ) (a : ℕ) : ℕ := sInf {y | y ∈ X ∧ a < y}

/-- The least element of `X` which is at least `m`. -/
noncomputable def cutUp (X : Set ℕ) (m : ℕ) : ℕ := sInf {y | y ∈ X ∧ m ≤ y}

lemma nxt_spec {X : Set ℕ} (hX : X.Infinite) (a : ℕ) : nxt X a ∈ X ∧ a < nxt X a := by
  have hne : {y | y ∈ X ∧ a < y}.Nonempty := by
    obtain ⟨y, hy, hy'⟩ := hX.exists_gt a
    exact ⟨y, hy, hy'⟩
  exact Nat.sInf_mem hne

lemma nxt_mem {X : Set ℕ} (hX : X.Infinite) (a : ℕ) : nxt X a ∈ X := (nxt_spec hX a).1

lemma lt_nxt {X : Set ℕ} (hX : X.Infinite) (a : ℕ) : a < nxt X a := (nxt_spec hX a).2

lemma nxt_le {X : Set ℕ} {a y : ℕ} (hy : y ∈ X) (hay : a < y) : nxt X a ≤ y :=
  Nat.sInf_le ⟨hy, hay⟩

lemma cutUp_spec {X : Set ℕ} (hX : X.Infinite) (m : ℕ) : cutUp X m ∈ X ∧ m ≤ cutUp X m := by
  have hne : {y | y ∈ X ∧ m ≤ y}.Nonempty := by
    obtain ⟨y, hy, hy'⟩ := hX.exists_gt m
    exact ⟨y, hy, hy'.le⟩
  exact Nat.sInf_mem hne

lemma cutUp_le {X : Set ℕ} {m y : ℕ} (hy : y ∈ X) (hmy : m ≤ y) : cutUp X m ≤ y :=
  Nat.sInf_le ⟨hy, hmy⟩

lemma pre_cutUp {X : Set ℕ} (hX : X.Infinite) (m : ℕ) : pre X (cutUp X m) = pre X m := by
  ext y
  simp only [mem_pre]
  constructor
  · rintro ⟨hy, hlt⟩
    refine ⟨hy, ?_⟩
    by_contra hcon
    push_neg at hcon
    have := cutUp_le hy hcon
    omega
  · rintro ⟨hy, hlt⟩
    exact ⟨hy, lt_of_lt_of_le hlt (cutUp_spec hX m).2⟩

lemma Ssum_cutUp {X : Set ℕ} (hX : X.Infinite) (m : ℕ) : Ssum X (cutUp X m) = Ssum X m := by
  rw [Ssum, pre_cutUp hX, Ssum]

lemma Pset_cutUp {X : Set ℕ} (hX : X.Infinite) (m : ℕ) : Pset X (cutUp X m) = Pset X m := by
  rw [Pset_eq_FS_pre, pre_cutUp hX, Pset_eq_FS_pre]

/-- Splitting a prefix at its top element. -/
lemma Pset_succ_of_mem {X : Set ℕ} {a : ℕ} (ha : a ∈ X) :
    Pset X (a + 1) = Pset X a ∪ (fun y => y + a) '' (Pset X a) := by
  classical
  have hpre : pre X (a + 1) = insert a (pre X a) := by
    ext y
    simp only [mem_pre, Finset.mem_insert]
    constructor
    · rintro ⟨hy, hlt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
      · exact Or.inr ⟨hy, h⟩
      · exact Or.inl h
    · rintro (rfl | ⟨hy, hlt⟩)
      · exact ⟨ha, by omega⟩
      · exact ⟨hy, by omega⟩
  apply Set.Subset.antisymm
  · rw [Pset_eq_FS_pre]
    rintro x ⟨F, hF, rfl⟩
    have hFsub : F ⊆ pre X (a + 1) := by exact_mod_cast hF
    by_cases hmem : a ∈ F
    · right
      refine ⟨∑ y ∈ F.erase a, y, ⟨F.erase a, ?_, rfl⟩, ?_⟩
      · intro y hy
        have hy' : y ∈ F ∧ y ≠ a := by
          have := Finset.mem_erase.mp (by exact_mod_cast hy)
          exact ⟨this.2, this.1⟩
        have := mem_pre.mp (hFsub hy'.1)
        exact ⟨this.1, by omega⟩
      · have h4 : a + ∑ y ∈ F.erase a, y = ∑ y ∈ F, y := by
          simpa using Finset.add_sum_erase F (fun y : ℕ => y) hmem
        show (∑ y ∈ F.erase a, y) + a = ∑ y ∈ F, y
        omega
    · left
      refine ⟨F, ?_, rfl⟩
      intro y hy
      have hy' : y ∈ F := by exact_mod_cast hy
      have h1 := mem_pre.mp (hFsub hy')
      have : y ≠ a := by rintro rfl; exact hmem hy'
      exact ⟨h1.1, by omega⟩
  · rintro x (hx | ⟨y, hy, rfl⟩)
    · exact Pset_mono (by omega) hx
    · exact mem_Pset_add_elt ha hy

/-- Extending a prefix representation by a larger element of `X`. -/
lemma mem_Pset_add_elt' {X : Set ℕ} {b m y : ℕ} (hb : b ∈ X) (hm : m ≤ b)
    (hy : y ∈ Pset X m) : y + b ∈ Pset X (b + 1) :=
  mem_Pset_add_elt hb (Pset_mono hm hy)

/-! ### Localization -/

/-- Localization. -/
theorem localization {X : Set ℕ} {T : ℕ} (hTFS : ∀ n, T ≤ n → n ∈ FS X) (hT1 : 1 ≤ T)
    {m x : ℕ} (hxT : T ≤ x) (hx2 : x + T ≤ Ssum X m) (hxP : x ∉ Pset X m) :
    ∃ a ∈ X, a < m ∧ ∃ u, u < T ∧ x + u = Ssum X a := by
  classical
  have hex : ∃ c, x + T ≤ Ssum X c := ⟨m, hx2⟩
  set c := Nat.find hex with hc
  have hcspec : x + T ≤ Ssum X c := Nat.find_spec hex
  have hcm : c ≤ m := Nat.find_le hx2
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, Ssum_zero] at hcspec
    omega
  obtain ⟨a, ha1⟩ : ∃ a, c = a + 1 := ⟨c - 1, by omega⟩
  rw [ha1] at hcspec hcm
  have hamin : ¬ (x + T ≤ Ssum X a) := Nat.find_min hex (by omega)
  have haX : a ∈ X := by
    by_contra hcon
    rw [Ssum_succ_of_notMem hcon] at hcspec
    omega
  have hstep : Ssum X (a + 1) = Ssum X a + a := Ssum_succ_of_mem haX
  have ham : a < m := by omega
  -- `y` is the complement of `x` in the prefix ending at `a`
  by_cases hy : Ssum X a + a < x + a
  · -- then `x > Ssum X a`, i.e. `y < a`; we derive a contradiction
    exfalso
    set y := Ssum X a + a - x with hydef
    have hxle : x ≤ Ssum X a + a := by omega
    have hyT : T ≤ y := by omega
    have hya : y < a := by omega
    have hyFS : y ∈ FS X := hTFS y hyT
    have hyP : y ∈ Pset X (a + 1) := by
      refine mem_Pset_of_mem_FS hyFS ?_
      intro z _ hz
      omega
    have hxP' : x ∈ Pset X (a + 1) := by
      have := Pset_reflect' hyP
      rw [hstep] at this
      have heq : Ssum X a + a - y = x := by omega
      rwa [heq] at this
    exact hxP (Pset_mono (by omega) hxP')
  · push_neg at hy
    have hxle : x ≤ Ssum X a := by omega
    exact ⟨a, haX, ham, Ssum X a - x, by omega, by omega⟩

/-! ### Global holes -/

open Classical in
/-- The set of "holes": natural numbers below `T` which are not finite subset sums. -/
noncomputable def Hset (X : Set ℕ) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun u => u ∉ FS X)

@[simp] lemma mem_Hset {X : Set ℕ} {T u : ℕ} : u ∈ Hset X T ↔ u < T ∧ u ∉ FS X := by
  classical
  simp [Hset]

/-- A bound for all holes. -/
noncomputable def hbnd (X : Set ℕ) (T : ℕ) : ℕ := (Hset X T).sup id

lemma le_hbnd {X : Set ℕ} {T u : ℕ} (hu : u ∈ Hset X T) : u ≤ hbnd X T :=
  Finset.le_sup (f := id) hu

/-- Every element of `FS X` lies in some prefix. -/
lemma exists_Pset_of_mem_FS {X : Set ℕ} {u : ℕ} (hu : u ∈ FS X) : ∃ J, u ∈ Pset X J := by
  classical
  obtain ⟨F, hF, rfl⟩ := hu
  refine ⟨F.sup id + 1, ⟨F, ?_, rfl⟩⟩
  intro y hy
  have hy' : y ∈ F := by exact_mod_cast hy
  exact ⟨hF hy, Nat.lt_succ_of_le (Finset.le_sup (f := id) hy')⟩

/-- There is a prefix containing all representable numbers below `T`. -/
lemma exists_prefix_bound (X : Set ℕ) (T : ℕ) :
    ∃ J, ∀ u, u < T → u ∈ FS X → u ∈ Pset X J := by
  induction T with
  | zero => exact ⟨0, fun u hu => absurd hu (by omega)⟩
  | succ T ih =>
      obtain ⟨J, hJ⟩ := ih
      by_cases hT : T ∈ FS X
      · obtain ⟨J', hJ'⟩ := exists_Pset_of_mem_FS hT
        refine ⟨max J J', fun u hu hu' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with h | h
        · exact Pset_mono (le_max_left _ _) (hJ u h hu')
        · subst h; exact Pset_mono (le_max_right _ _) hJ'
      · refine ⟨J, fun u hu hu' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with h | h
        · exact hJ u h hu'
        · exact absurd (h ▸ hu') hT

/-- Late labels are global holes: if a missing element of a prefix is localized at a
late cut `a` with label `u`, then `u` is a global hole. -/
theorem late_label {X : Set ℕ} {T Jst : ℕ}
    (hJ1 : ∀ u, u < T → u ∈ FS X → u ∈ Pset X Jst)
    {a c u x : ℕ} (hJa : Jst ≤ a) (hac : a ≤ c) (huT : u < T)
    (hxu : x + u = Ssum X a) (hxP : x ∉ Pset X c) : u ∈ Hset X T := by
  rw [mem_Hset]
  refine ⟨huT, fun huFS => ?_⟩
  have h1 : u ∈ Pset X a := Pset_mono hJa (hJ1 u huT huFS)
  have h2 := Pset_reflect' h1
  have heq : Ssum X a - u = x := by omega
  rw [heq] at h2
  exact hxP (Pset_mono hac h2)

/-! ### Minimum and maximum of a finite set of naturals -/

/-- The minimum of a finite set of naturals (`0` if empty). -/
noncomputable def fmin (E : Finset ℕ) : ℕ := sInf (↑E : Set ℕ)

/-- The maximum of a finite set of naturals (`0` if empty). -/
noncomputable def fmax (E : Finset ℕ) : ℕ := E.sup id

lemma fmin_mem {E : Finset ℕ} (h : E.Nonempty) : fmin E ∈ E := by
  obtain ⟨x, hx⟩ := h
  have hne : (↑E : Set ℕ).Nonempty := ⟨x, hx⟩
  simpa [fmin] using Nat.sInf_mem hne

lemma fmin_le {E : Finset ℕ} {x : ℕ} (hx : x ∈ E) : fmin E ≤ x := Nat.sInf_le hx

lemma le_fmax {E : Finset ℕ} {x : ℕ} (hx : x ∈ E) : x ≤ fmax E :=
  Finset.le_sup (f := id) hx

lemma fmax_mem {E : Finset ℕ} (h : E.Nonempty) : fmax E ∈ E := by
  obtain ⟨b, hb, hEb⟩ := Finset.exists_mem_eq_sup E h id
  simpa [fmax, hEb] using hb

/-! ### Prefix sums at the successor element -/

lemma pre_nxt {X : Set ℕ} (hX : X.Infinite) {l : ℕ} (hl : l ∈ X) :
    pre X (nxt X l) = insert l (pre X l) := by
  ext y
  simp only [mem_pre, Finset.mem_insert]
  constructor
  · rintro ⟨hy, hlt⟩
    rcases lt_trichotomy y l with h | h | h
    · exact Or.inr ⟨hy, h⟩
    · exact Or.inl h
    · exact absurd (nxt_le hy h) (by omega)
  · rintro (rfl | ⟨hy, hlt⟩)
    · exact ⟨hl, lt_nxt hX _⟩
    · exact ⟨hy, lt_trans hlt (lt_nxt hX l)⟩

lemma Ssum_nxt {X : Set ℕ} (hX : X.Infinite) {l : ℕ} (hl : l ∈ X) :
    Ssum X (nxt X l) = Ssum X l + l := by
  classical
  rw [Ssum, pre_nxt hX hl, Finset.sum_insert (by simp), Ssum]
  omega

/-! ### States -/

/-- `(a, c, E)` is a *state* when `a < c` are elements of `X`, `E` is a
nonempty set of holes, and `Ssum X a - e` is missing from the prefix below `c` for
every `e ∈ E`. -/
def IsState (X : Set ℕ) (T : ℕ) (a c : ℕ) (E : Finset ℕ) : Prop :=
  a ∈ X ∧ c ∈ X ∧ a < c ∧ E.Nonempty ∧ E ⊆ Hset X T ∧ ∀ e ∈ E, Ssum X a - e ∉ Pset X c

lemma one_le_of_mem_Hset {X : Set ℕ} {T u : ℕ} (hu : u ∈ Hset X T) : 1 ≤ u := by
  rcases Nat.eq_zero_or_pos u with h | h
  · exact absurd (h ▸ zero_mem_FS X) (mem_Hset.mp hu).2
  · exact h

/-- The potential of a state. -/
noncomputable def Phi (X : Set ℕ) (T : ℕ) (a c : ℕ) (E : Finset ℕ) : ℕ :=
  if c = nxt X a then (hbnd X T + 1) * E.card + fmin E
  else (hbnd X T + 1) * (E.card + 1)

lemma one_le_Phi {X : Set ℕ} {T a c : ℕ} {E : Finset ℕ} (hs : IsState X T a c E) :
    1 ≤ Phi X T a c E := by
  obtain ⟨_, _, _, hEne, hEH, _⟩ := hs
  have hcard : 1 ≤ E.card := Finset.card_pos.mpr hEne
  rw [Phi]
  split
  · nlinarith
  · nlinarith

lemma Phi_le {X : Set ℕ} {T a c : ℕ} {E : Finset ℕ} (hs : IsState X T a c E) :
    Phi X T a c E ≤ (hbnd X T + 1) * ((Hset X T).card + 1) := by
  obtain ⟨_, _, _, hEne, hEH, _⟩ := hs
  have hcard : E.card ≤ (Hset X T).card := Finset.card_le_card hEH
  have hmin : fmin E ≤ hbnd X T := le_hbnd (hEH (fmin_mem hEne))
  rw [Phi]
  split
  · nlinarith
  · nlinarith

/-- Gap after a state cut: the next element after the cut of a state is at most
`a + e` for every label `e` of the state. -/
theorem next_gap {X : Set ℕ} {T : ℕ}
    (hTFS : ∀ n, T ≤ n → n ∈ FS X) {a c : ℕ} {E : Finset ℕ}
    (hs : IsState X T a c E) (hTa : T ≤ a) {e : ℕ} (he : e ∈ E) :
    nxt X a ≤ a + e := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨haX, hcX, hac, hEne, hEH, hE⟩ := hs
  have heH := hEH he
  have heFS : e ∉ FS X := (mem_Hset.mp heH).2
  have hFS : a + e ∈ FS X := hTFS _ (by omega)
  have hP1 : a + e ∈ Pset X (a + 1) := by
    refine mem_Pset_of_mem_FS hFS ?_
    intro z hz hz1
    have := nxt_le hz (show a < z by omega)
    omega
  rw [Pset_succ_of_mem haX] at hP1
  rcases hP1 with hP1 | ⟨y, hy, hy2⟩
  · have hle : a + e ≤ Ssum X a := le_Ssum_of_mem_Pset hP1
    have h2 := mem_Pset_add_elt haX (Pset_reflect' hP1)
    have heq : Ssum X a - (a + e) + a = Ssum X a - e := by omega
    rw [heq] at h2
    exact hE e he (Pset_mono (by omega) h2)
  · have hy3 : y + a = a + e := hy2
    have : y = e := by omega
    subst this
    exact heFS (Pset_subset_FS _ _ hy)

/-- Regrouping missing sums. -/
theorem regroup {X : Set ℕ} {T : ℕ} (hTFS : ∀ n, T ≤ n → n ∈ FS X) (hT1 : 1 ≤ T)
    {Jst : ℕ} (hJ1 : ∀ u, u < T → u ∈ FS X → u ∈ Pset X Jst)
    (hJ3 : 3 * hbnd X T < Jst)
    {K a : ℕ} (hK : Jst ≤ K)
    {R : Finset ℕ} (hRne : R.Nonempty)
    (hRP : ∀ x ∈ R, x ∉ Pset X a)
    (hRminT : T < fmin R) (hRminK : Ssum X K < fmin R)
    (hRmax : fmax R + T ≤ Ssum X a)
    (hRdiam : fmax R ≤ fmin R + 2 * hbnd X T) :
    ∃ l ∈ X, K < l ∧ l < a ∧ ∃ E' : Finset ℕ, E' ⊆ Hset X T ∧ E'.card = R.card ∧
      (∀ x ∈ R, ∃ e ∈ E', x + e = Ssum X l) ∧ (∀ e ∈ E', ∃ x ∈ R, x + e = Ssum X l) := by
  classical
  -- every element of `R` is localized at some cut `l` with a hole label
  have key : ∀ x ∈ R, ∃ l, l ∈ X ∧ K < l ∧ l < a ∧ ∃ u, u ∈ Hset X T ∧ x + u = Ssum X l := by
    intro x hx
    have hxmin : fmin R ≤ x := fmin_le hx
    have hxmax : x ≤ fmax R := le_fmax hx
    have hxT : T ≤ x := by omega
    have hx2 : x + T ≤ Ssum X a := by omega
    obtain ⟨l, hlX, hla, u, huT, hxu⟩ := localization hTFS hT1 hxT hx2 (hRP x hx)
    have hlK : K < l := by
      by_contra hcon
      push_neg at hcon
      have : Ssum X l ≤ Ssum X K := Ssum_mono hcon
      omega
    exact ⟨l, hlX, hlK, hla, u,
      late_label hJ1 (by omega : Jst ≤ l) (le_of_lt hla) huT hxu (hRP x hx), hxu⟩
  -- all these cuts agree
  set x₀ := fmin R with hx₀
  obtain ⟨l, hlX, hlK, hla, u₀, hu₀, hxu₀⟩ := key x₀ (fmin_mem hRne)
  have hall : ∀ x ∈ R, ∃ u, u ∈ Hset X T ∧ x + u = Ssum X l := by
    intro x hx
    obtain ⟨l', hl'X, hl'K, hl'a, u, hu, hxu⟩ := key x hx
    have hbu : u ≤ hbnd X T := le_hbnd hu
    have hbu₀ : u₀ ≤ hbnd X T := le_hbnd hu₀
    have hxmax : x ≤ fmax R := le_fmax hx
    have hxmin : fmin R ≤ x := fmin_le hx
    have hll : l' = l := by
      rcases lt_trichotomy l' l with h | h | h
      · have h1 : Ssum X l' + l' ≤ Ssum X l := Ssum_add_le hl'X h
        have h2 : 3 * hbnd X T < l' := by omega
        omega
      · exact h
      · have h1 : Ssum X l + l ≤ Ssum X l' := Ssum_add_le hlX h
        have h2 : 3 * hbnd X T < l := by omega
        omega
    exact ⟨u, hu, hll ▸ hxu⟩
  refine ⟨l, hlX, hlK, hla, R.image (fun x => Ssum X l - x), ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [Finset.mem_image] at he
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨u, hu, hxu⟩ := hall x hx
    have : Ssum X l - x = u := by omega
    rwa [this]
  · refine Finset.card_image_of_injOn ?_
    intro x hx y hy hxy
    obtain ⟨u, hu, hxu⟩ := hall x hx
    obtain ⟨v, hv, hyv⟩ := hall y hy
    simp only at hxy
    omega
  · intro x hx
    refine ⟨Ssum X l - x, Finset.mem_image_of_mem _ hx, ?_⟩
    obtain ⟨u, hu, hxu⟩ := hall x hx
    omega
  · intro e he
    simp only [Finset.mem_image] at he
    obtain ⟨x, hx, rfl⟩ := he
    refine ⟨x, hx, ?_⟩
    obtain ⟨u, hu, hxu⟩ := hall x hx
    omega

/-- Uniform state transition. -/
theorem transition {X : Set ℕ} {T : ℕ} (hXinf : X.Infinite)
    (hTFS : ∀ n, T ≤ n → n ∈ FS X) (hT1 : 1 ≤ T) (hslack : SlackDiv X)
    {Jst : ℕ} (hJ1 : ∀ u, u < T → u ∈ FS X → u ∈ Pset X Jst) (hJ2 : T ≤ Jst)
    (hJ3 : 3 * hbnd X T < Jst) {K : ℕ} (hK : Jst ≤ K) :
    ∃ J, K < J ∧ ∀ a c E, IsState X T a c E → J ≤ a →
      ∃ l E', IsState X T l a E' ∧ K < l ∧ Phi X T a c E < Phi X T l a E' := by
  classical
  obtain ⟨M, hM⟩ := hslack (2 * hbnd X T + T + Ssum X K + 1)
  refine ⟨max M (K + 1), by omega, ?_⟩
  intro a c E hs hJa
  obtain ⟨haX, hcX, hac, hEne, hEH, hEmiss⟩ := id hs
  have hTa : T ≤ a := by omega
  have hKa : K < a := by omega
  set W := Ssum X a with hWdef
  have hW : a + (2 * hbnd X T + T + Ssum X K + 1) ≤ W := hM a haX (by omega)
  set B := nxt X a with hBdef
  have hBX : B ∈ X := nxt_mem hXinf a
  have haB : a < B := lt_nxt hXinf a
  have hBc : B ≤ c := nxt_le hcX hac
  have hfmaxE : fmax E ≤ hbnd X T := le_hbnd (hEH (fmax_mem hEne))
  have hfminE1 : 1 ≤ fmin E := one_le_of_mem_Hset (hEH (fmin_mem hEne))
  have hfminmax : fmin E ≤ fmax E := fmin_le (fmax_mem hEne)
  have hBgap : B ≤ a + fmin E := next_gap hTFS hs hTa (fmin_mem hEne)
  -- elements of the translates are missing from the prefix below `a`
  have missing : ∀ d, d ∈ X → a ≤ d → d + 1 ≤ c → d + fmax E ≤ W →
      ∀ e ∈ E, W - d - e ∉ Pset X a := by
    intro d hdX had hdc hdW e he hmem
    have hle : e ≤ fmax E := le_fmax he
    have h2 := mem_Pset_add_elt' hdX had hmem
    have heq : W - d - e + d = W - e := by omega
    rw [heq] at h2
    exact hEmiss e he (Pset_mono hdc h2)
  by_cases hshort : c = B
  · -- the state is short
    set R := E.image (fun e => W - a - e) with hRdef
    have hRne : R.Nonempty := hEne.image _
    have hRmem : ∀ x ∈ R, ∃ e ∈ E, x = W - a - e := by
      intro x hx
      simp only [hRdef, Finset.mem_image] at hx
      obtain ⟨e, he, rfl⟩ := hx
      exact ⟨e, he, rfl⟩
    have hRP : ∀ x ∈ R, x ∉ Pset X a := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := hRmem x hx
      exact missing a haX le_rfl (by omega) (by omega) e he
    have hbounds : ∀ x ∈ R, W - a - fmax E ≤ x ∧ x ≤ W - a - fmin E := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := hRmem x hx
      have h1 : e ≤ fmax E := le_fmax he
      have h2 : fmin E ≤ e := fmin_le he
      omega
    have hminR := hbounds _ (fmin_mem hRne)
    have hmaxR := hbounds _ (fmax_mem hRne)
    have hRminT : T < fmin R := by omega
    have hRminK : Ssum X K < fmin R := by omega
    have hRmax : fmax R + T ≤ W := by omega
    have hRdiam : fmax R ≤ fmin R + 2 * hbnd X T := by omega
    obtain ⟨l, hlX, hlK, hla, E', hE'H, hcard, hA, hBd⟩ :=
      regroup hTFS hT1 hJ1 (by omega) hK hRne hRP hRminT hRminK hRmax hRdiam
    have hcardR : R.card = E.card := by
      rw [hRdef]
      refine Finset.card_image_of_injOn ?_
      intro x hx y hy hxy
      have h1 : x ≤ fmax E := le_fmax hx
      have h2 : y ≤ fmax E := le_fmax hy
      simp only at hxy
      omega
    have hE'ne : E'.Nonempty := by
      rw [← Finset.card_pos, hcard, hcardR, Finset.card_pos]
      exact hEne
    have hstate' : IsState X T l a E' := by
      refine ⟨hlX, haX, hla, hE'ne, hE'H, ?_⟩
      intro e he hmem
      obtain ⟨x, hx, hxe⟩ := hBd e he
      have : Ssum X l - e = x := by omega
      rw [this] at hmem
      exact hRP x hx hmem
    refine ⟨l, E', hstate', hlK, ?_⟩
    have hPhi : Phi X T a c E = (hbnd X T + 1) * E.card + fmin E := by
      rw [Phi, if_pos (by rw [hshort])]
    rw [hPhi, Phi]
    have hfminE' : 1 ≤ fmin E' := one_le_of_mem_Hset (hE'H (fmin_mem hE'ne))
    have hcardE' : E'.card = E.card := by rw [hcard, hcardR]
    split
    · -- the new state is short as well
      rename_i hnew
      have hWl : W = Ssum X l + l := by
        rw [hWdef, hnew, Ssum_nxt hXinf hlX]
      -- `fmax R = W - a - fmin E`
      have h1 : W - a - fmin E ∈ R := by
        simp only [hRdef, Finset.mem_image]
        exact ⟨fmin E, fmin_mem hEne, rfl⟩
      have h2 : W - a - fmin E ≤ fmax R := le_fmax h1
      have hfmaxR : fmax R + (a + fmin E) = W := by omega
      -- `fmax R + fmin E' = Ssum X l`
      obtain ⟨e₁, he₁, he₁eq⟩ := hA _ (fmax_mem hRne)
      obtain ⟨x₁, hx₁, hx₁eq⟩ := hBd _ (fmin_mem hE'ne)
      have h3 : fmin E' ≤ e₁ := fmin_le he₁
      have h4 : x₁ ≤ fmax R := le_fmax hx₁
      have hrel : fmax R + fmin E' = Ssum X l := by omega
      have : fmin E < fmin E' := by omega
      rw [hcardE']
      omega
    · rw [hcardE']
      have : (hbnd X T + 1) * (E.card + 1) = (hbnd X T + 1) * E.card + hbnd X T + 1 := by ring
      omega
  · -- the state is long
    have hBc' : B < c := lt_of_le_of_ne hBc (fun h => hshort h.symm)
    set R := E.image (fun e => W - a - e) ∪ E.image (fun e => W - B - e) with hRdef
    have hRne : R.Nonempty := Finset.Nonempty.inl (hEne.image _)
    have hRmem : ∀ x ∈ R, ∃ e ∈ E, x = W - a - e ∨ x = W - B - e := by
      intro x hx
      simp only [hRdef, Finset.mem_union, Finset.mem_image] at hx
      rcases hx with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · exact ⟨e, he, Or.inl rfl⟩
      · exact ⟨e, he, Or.inr rfl⟩
    have hRP : ∀ x ∈ R, x ∉ Pset X a := by
      intro x hx
      obtain ⟨e, he, hx'⟩ := hRmem x hx
      rcases hx' with rfl | rfl
      · exact missing a haX le_rfl (by omega) (by omega) e he
      · exact missing B hBX (by omega) (by omega) (by omega) e he
    have hbounds : ∀ x ∈ R, W - B - fmax E ≤ x ∧ x ≤ W - a - fmin E := by
      intro x hx
      obtain ⟨e, he, hx'⟩ := hRmem x hx
      have h1 : e ≤ fmax E := le_fmax he
      have h2 : fmin E ≤ e := fmin_le he
      rcases hx' with rfl | rfl <;> omega
    have hminR := hbounds _ (fmin_mem hRne)
    have hmaxR := hbounds _ (fmax_mem hRne)
    have hRminT : T < fmin R := by omega
    have hRminK : Ssum X K < fmin R := by omega
    have hRmax : fmax R + T ≤ W := by omega
    have hRdiam : fmax R ≤ fmin R + 2 * hbnd X T := by omega
    obtain ⟨l, hlX, hlK, hla, E', hE'H, hcard, hA, hBd⟩ :=
      regroup hTFS hT1 hJ1 (by omega) hK hRne hRP hRminT hRminK hRmax hRdiam
    -- the two translates make `R` strictly bigger than `E`
    have hcardR : E.card + 1 ≤ R.card := by
      have himg : (E.image (fun e => W - a - e)).card = E.card := by
        refine Finset.card_image_of_injOn ?_
        intro x hx y hy hxy
        have h1 : x ≤ fmax E := le_fmax hx
        have h2 : y ≤ fmax E := le_fmax hy
        simp only at hxy
        omega
      have hz : W - B - fmax E ∈ R := by
        simp only [hRdef, Finset.mem_union, Finset.mem_image]
        exact Or.inr ⟨fmax E, fmax_mem hEne, rfl⟩
      have hznot : W - B - fmax E ∉ E.image (fun e => W - a - e) := by
        simp only [Finset.mem_image, not_exists]
        rintro e ⟨he, heq⟩
        have h1 : e ≤ fmax E := le_fmax he
        omega
      have hsub : insert (W - B - fmax E) (E.image (fun e => W - a - e)) ⊆ R := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hz
        · exact Finset.mem_union_left _ hx
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hznot, himg] at this
      omega
    have hE'ne : E'.Nonempty := by
      rw [← Finset.card_pos, hcard]
      have := Finset.card_pos.mpr hRne
      omega
    have hstate' : IsState X T l a E' := by
      refine ⟨hlX, haX, hla, hE'ne, hE'H, ?_⟩
      intro e he hmem
      obtain ⟨x, hx, hxe⟩ := hBd e he
      have : Ssum X l - e = x := by omega
      rw [this] at hmem
      exact hRP x hx hmem
    refine ⟨l, E', hstate', hlK, ?_⟩
    have hPhi : Phi X T a c E = (hbnd X T + 1) * (E.card + 1) := by
      rw [Phi, if_neg hshort]
    rw [hPhi, Phi]
    have hfminE' : 1 ≤ fmin E' := one_le_of_mem_Hset (hE'H (fmin_mem hE'ne))
    have hcardE' : E.card + 1 ≤ E'.card := by omega
    have h5 : (hbnd X T + 1) * (E.card + 1) ≤ (hbnd X T + 1) * E'.card :=
      Nat.mul_le_mul (le_refl _) hcardE'
    have h6 : (hbnd X T + 1) * (E'.card + 1) = (hbnd X T + 1) * E'.card + (hbnd X T + 1) := by
      ring
    split
    · omega
    · omega

/-! ### The central interval theorem -/

/-- A cut value beyond all holes and all representable numbers below `T`. -/
lemma exists_Jst (X : Set ℕ) (T : ℕ) :
    ∃ Jst, (∀ u, u < T → u ∈ FS X → u ∈ Pset X Jst) ∧ T ≤ Jst ∧ 3 * hbnd X T < Jst := by
  obtain ⟨J, hJ⟩ := exists_prefix_bound X T
  refine ⟨max J (max T (3 * hbnd X T + 1)), fun u hu hu' => ?_, ?_, ?_⟩
  · exact Pset_mono (le_max_left _ _) (hJ u hu hu')
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · have : 3 * hbnd X T + 1 ≤ max T (3 * hbnd X T + 1) := le_max_right _ _
    have h2 : max T (3 * hbnd X T + 1) ≤ max J (max T (3 * hbnd X T + 1)) := le_max_right _ _
    omega

/-- Bad central prefixes give arbitrarily late cuts. -/
theorem late_cuts {X : Set ℕ} {T : ℕ} (hXinf : X.Infinite) (hT1 : 1 ≤ T)
    (hTFS : ∀ n, T ≤ n → n ∈ FS X)
    {Jst : ℕ} (hJ1 : ∀ u, u < T → u ∈ FS X → u ∈ Pset X Jst)
    (hbad : ∀ M, ∃ m, M ≤ m ∧ ∃ x, T ≤ x ∧ x + T ≤ Ssum X m ∧ x ∉ Pset X m)
    (K : ℕ) : ∃ a c E, IsState X T a c E ∧ K < a := by
  classical
  set J0 := max K Jst with hJ0
  obtain ⟨m, hm, x, hxT, hxS, hxP⟩ := hbad (Ssum X J0 + 1)
  set c := cutUp X m with hcdef
  have hcX : c ∈ X := (cutUp_spec hXinf m).1
  have hmc : m ≤ c := (cutUp_spec hXinf m).2
  have hSc : Ssum X c = Ssum X m := Ssum_cutUp hXinf m
  have hPc : Pset X c = Pset X m := Pset_cutUp hXinf m
  have hxPc : x ∉ Pset X c := by rw [hPc]; exact hxP
  have hxSc : x + T ≤ Ssum X c := by rw [hSc]; exact hxS
  have hcJ0 : Ssum X J0 < c := by omega
  -- `x` is at least `c`
  have hxc : c ≤ x := by
    have hxFS : x ∈ FS X := hTFS x hxT
    by_contra hcon
    push_neg at hcon
    refine hxPc (mem_Pset_of_mem_FS hxFS ?_)
    intro y hy hcy
    by_contra hcon2
    push_neg at hcon2
    have hle : y ≤ x := hcon2
    -- `y ∈ X`, `c ≤ y ≤ x < c` is impossible
    omega
  obtain ⟨a, haX, hac, u, huT, hxu⟩ := localization hTFS hT1 hxT hxSc hxPc
  have haJ0 : J0 < a := by
    by_contra hcon
    push_neg at hcon
    have : Ssum X a ≤ Ssum X J0 := Ssum_mono hcon
    omega
  have huH : u ∈ Hset X T :=
    late_label hJ1 (by omega : Jst ≤ a) (le_of_lt hac) huT hxu hxPc
  refine ⟨a, c, {u}, ⟨haX, hcX, hac, ⟨u, by simp⟩, by simpa using huH, ?_⟩, by omega⟩
  intro e he
  have : e = u := by simpa using he
  subst this
  have heq : Ssum X a - e = x := by omega
  rw [heq]
  exact hxPc

/-- The central interval theorem. -/
theorem central_interval {X : Set ℕ} (hXinf : X.Infinite) {T : ℕ} (hT1 : 1 ≤ T)
    (hTFS : ∀ n, T ≤ n → n ∈ FS X) (hslack : SlackDiv X) :
    ∃ M, ∀ m, M ≤ m → ∀ x, T ≤ x → x + T ≤ Ssum X m → x ∈ Pset X m := by
  classical
  by_contra hcon
  push_neg at hcon
  have hbad : ∀ M, ∃ m, M ≤ m ∧ ∃ x, T ≤ x ∧ x + T ≤ Ssum X m ∧ x ∉ Pset X m := by
    intro M
    obtain ⟨m, hm, x, hx1, hx2, hx3⟩ := hcon M
    exact ⟨m, hm, x, hx1, hx2, hx3⟩
  obtain ⟨Jst, hJ1, hJ2, hJ3⟩ := exists_Jst X T
  -- a choice of thresholds for the transition lemma
  have hex : ∀ K, ∃ J, Jst ≤ K → (K < J ∧ ∀ a c E, IsState X T a c E → J ≤ a →
      ∃ l E', IsState X T l a E' ∧ K < l ∧ Phi X T a c E < Phi X T l a E') := by
    intro K
    by_cases hK : Jst ≤ K
    · obtain ⟨J, hJ⟩ := transition hXinf hTFS hT1 hslack hJ1 hJ2 hJ3 hK
      exact ⟨J, fun _ => hJ⟩
    · exact ⟨0, fun h => absurd h hK⟩
  choose f hf using hex
  set Kseq : ℕ → ℕ := fun r => f^[r] Jst with hKseq
  have hKmono : ∀ r, Jst ≤ Kseq r := by
    intro r
    induction r with
    | zero => simp [hKseq]
    | succ r ih =>
        have : Kseq (r + 1) = f (Kseq r) := by
          simp [hKseq, Function.iterate_succ_apply']
        rw [this]
        exact le_trans ih (le_of_lt (hf (Kseq r) ih).1)
  have hstep : ∀ r, Kseq r < Kseq (r + 1) := by
    intro r
    have : Kseq (r + 1) = f (Kseq r) := by
      simp [hKseq, Function.iterate_succ_apply']
    rw [this]
    exact (hf (Kseq r) (hKmono r)).1
  -- iterating the transition lemma raises the potential arbitrarily
  have main : ∀ r a c E, IsState X T a c E → Kseq r ≤ a →
      ∃ a' c' E', IsState X T a' c' E' ∧ Phi X T a c E + r ≤ Phi X T a' c' E' := by
    intro r
    induction r with
    | zero => intro a c E hs _; exact ⟨a, c, E, hs, by omega⟩
    | succ r ih =>
        intro a c E hs hle
        have heq : Kseq (r + 1) = f (Kseq r) := by
          simp [hKseq, Function.iterate_succ_apply']
        rw [heq] at hle
        obtain ⟨l, E', hs', hlK, hPhi⟩ := (hf (Kseq r) (hKmono r)).2 a c E hs hle
        obtain ⟨a', c', E'', hs'', hPhi'⟩ := ih l a E' hs' (le_of_lt hlK)
        exact ⟨a', c', E'', hs'', by omega⟩
  set Mb := (hbnd X T + 1) * ((Hset X T).card + 1) with hMb
  obtain ⟨a, c, E, hs, ha⟩ := late_cuts hXinf hT1 hTFS hJ1 hbad (Kseq Mb)
  obtain ⟨a', c', E', hs', hPhi⟩ := main Mb a c E hs (by omega)
  have h1 : 1 ≤ Phi X T a c E := one_le_Phi hs
  have h2 : Phi X T a' c' E' ≤ Mb := Phi_le hs'
  omega

/-! ### Deletion extension -/

/-- A missing translate forces a tail gap. -/
theorem tail_gap {P Q : Set ℕ} {S T : ℕ}
    (hPfull : ∀ n, T ≤ n → n + T ≤ S → n ∈ P)
    (hS : 2 * T ≤ S) (hT1 : 1 ≤ T)
    (hQunb : ∀ n, ∃ q ∈ Q, n ≤ q)
    (hmiss : ∀ N, ∃ x, N ≤ x ∧ ∀ p ∈ P, ∀ t ∈ Q, p + t ≠ x)
    (M₀ : ℕ) :
    ∃ q ∈ Q, ∃ q' ∈ Q, M₀ ≤ q ∧ q < q' ∧ (∀ z ∈ Q, z ≤ q ∨ q' ≤ z) ∧
      q + S + 2 ≤ q' + 2 * T := by
  classical
  obtain ⟨r, hrQ, hr⟩ := hQunb (max M₀ 1)
  obtain ⟨x, hx, hxmiss⟩ := hmiss (r + S + 1)
  -- no element of `Q` lies in the window `[x + T - S, x - T]`
  have hwindow : ∀ z ∈ Q, ¬ (x + T ≤ z + S ∧ z + T ≤ x) := by
    rintro z hz ⟨h1, h2⟩
    have hn1 : T ≤ x - z := by omega
    have hn2 : (x - z) + T ≤ S := by omega
    exact hxmiss (x - z) (hPfull _ hn1 hn2) z hz (by omega)
  set bnd := x + T - S - 1 with hbnd
  have hrbnd : r ≤ bnd := by omega
  -- the largest element of `Q` below the window
  set q := Nat.findGreatest (· ∈ Q) bnd with hq
  have hqQ : q ∈ Q := Nat.findGreatest_spec (m := r) hrbnd hrQ
  have hrq : r ≤ q := Nat.le_findGreatest hrbnd hrQ
  have hqbnd : q ≤ bnd := Nat.findGreatest_le bnd
  have hqmax : ∀ z, q < z → z ≤ bnd → z ∉ Q := by
    intro z h1 h2
    exact Nat.findGreatest_is_greatest h1 h2
  -- the least element of `Q` above the window
  have hne : {z | z ∈ Q ∧ x + 1 ≤ z + T}.Nonempty := by
    obtain ⟨z, hzQ, hz⟩ := hQunb (x + 1)
    exact ⟨z, hzQ, by omega⟩
  set q' := sInf {z | z ∈ Q ∧ x + 1 ≤ z + T} with hq'
  have hq'spec : q' ∈ Q ∧ x + 1 ≤ q' + T := Nat.sInf_mem hne
  have hq'min : ∀ z, z ∈ Q → x + 1 ≤ z + T → q' ≤ z := fun z h1 h2 => Nat.sInf_le ⟨h1, h2⟩
  refine ⟨q, hqQ, q', hq'spec.1, by omega, by omega, ?_, by omega⟩
  intro z hz
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- `z` lies strictly between `q` and `q'`
  by_cases hzb : z ≤ bnd
  · exact hqmax z h1 hzb hz
  · by_cases hzup : x + 1 ≤ z + T
    · exact absurd (hq'min z hz hzup) (by omega)
    · exact hwindow z hz ⟨by omega, by omega⟩

/-- Restoring a bounded finite deletion. -/
theorem restore_gap {R : Set ℕ} {D : Finset ℕ} {u len : ℕ}
    (hgap : ∀ n, u ≤ n → n < u + len → n ∉ R) :
    ∀ n, u + (∑ d ∈ D, d) ≤ n → n < u + len → ∀ p ∈ R, ∀ t ∈ FS (↑D : Set ℕ), p + t ≠ n := by
  intro n h1 h2 p hp t ht heq
  have hle : t ≤ ∑ d ∈ D, d := FS_finset_le ht
  exact hgap p (by omega) (by omega) hp

/-- Two deletions create arbitrarily late long gaps. -/
theorem two_gap {Y : Set ℕ} (hYinf : Y.Infinite)
    (hmin : ∀ r ∈ Y, ¬ Complete (Y \ {r}))
    {T : ℕ} (hT1 : 1 ≤ T)
    {M₀ : ℕ} (hcentral : ∀ m, M₀ ≤ m → ∀ x, T ≤ x → x + T ≤ Ssum Y m → x ∈ Pset Y m)
    (C : ℕ) :
    ∃ i ∈ Y, ∃ j ∈ Y, i ≠ j ∧
      ∀ N, ∃ u, N ≤ u ∧ ∀ n, u ≤ n → n ≤ u + C → n ∉ FS (Y \ {i, j}) := by
  classical
  obtain ⟨i, hiY, hi⟩ := hYinf.exists_gt (2 * T + C)
  obtain ⟨Mk, hMk⟩ := Ssum_large hYinf (2 * T)
  set k := max (max M₀ Mk) (i + 1) with hkdef
  have hk1 : M₀ ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
  have hk2 : 2 * T ≤ Ssum Y k := hMk k (le_trans (le_max_right _ _) (le_max_left _ _))
  have hik : i < k := lt_of_lt_of_le (by omega) (le_max_right _ _)
  set S := Ssum Y k with hSdef
  have hPfull : ∀ n, T ≤ n → n + T ≤ S → n ∈ Pset Y k := hcentral k hk1
  obtain ⟨j, hjY, hjk⟩ := hYinf.exists_gt k
  have hij : i ≠ j := by omega
  refine ⟨i, hiY, j, hjY, hij, ?_⟩
  -- the tail of `Y` beyond `k`, with `j` removed
  set tail : Set ℕ := {y | y ∈ Y ∧ k ≤ y} \ {j} with htaildef
  set Q := FS tail with hQdef
  have hQunb : ∀ n, ∃ q ∈ Q, n ≤ q := by
    intro n
    obtain ⟨y, hyY, hy⟩ := hYinf.exists_gt (max (max n k) j)
    refine ⟨y, mem_FS_self ⟨⟨hyY, by omega⟩, by simp; omega⟩, by omega⟩
  -- splitting `Y \ {j}`
  have hsplitj : Y \ {j} = {y | y ∈ Y ∧ y < k} ∪ tail := by
    ext y
    simp only [htaildef, Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hyj⟩
      rcases lt_or_ge y k with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨⟨hy, h⟩, hyj⟩
    · rintro (⟨hy, hlt⟩ | ⟨⟨hy, hge⟩, hyj⟩)
      · exact ⟨hy, by omega⟩
      · exact ⟨hy, hyj⟩
  have hdisj : Disjoint {y | y ∈ Y ∧ y < k} tail := by
    rw [Set.disjoint_left]
    rintro y ⟨_, hlt⟩ ⟨⟨_, hge⟩, _⟩
    omega
  have hFSj : FS (Y \ {j}) = {n | ∃ p ∈ Pset Y k, ∃ t ∈ Q, p + t = n} := by
    rw [hsplitj, FS_union_disjoint hdisj]
    rfl
  -- `Y \ {j}` is incomplete
  have hmiss : ∀ N, ∃ x, N ≤ x ∧ ∀ p ∈ Pset Y k, ∀ t ∈ Q, p + t ≠ x := by
    intro N
    have := hmin j hjY
    rw [Complete] at this
    push_neg at this
    obtain ⟨x, hx, hxn⟩ := this N
    refine ⟨x, hx, ?_⟩
    intro p hp t ht heq
    exact hxn (by rw [hFSj]; exact ⟨p, hp, t, ht, heq⟩)
  -- the prefix below `k` with `i` deleted
  set G := (pre Y k).erase i with hGdef
  set SG := ∑ y ∈ G, y with hSGdef
  have hSG : SG + i = S := sum_pre_erase hiY hik
  set Gset : Set ℕ := {y | y ∈ Y ∧ y < k ∧ y ≠ i} with hGsetdef
  have hGcoe : (↑G : Set ℕ) = Gset := by
    ext y
    simp only [hGdef, hGsetdef, Finset.coe_erase, Set.mem_diff, Finset.mem_coe, mem_pre,
      Set.mem_singleton_iff, Set.mem_setOf_eq]
    tauto
  have hsplitij : Y \ {i, j} = Gset ∪ tail := by
    ext y
    simp only [hGsetdef, htaildef, Set.mem_diff, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hy, hyij⟩
      simp only [not_or] at hyij
      rcases lt_or_ge y k with h | h
      · exact Or.inl ⟨hy, h, hyij.1⟩
      · exact Or.inr ⟨⟨hy, h⟩, hyij.2⟩
    · rintro (⟨hy, hlt, hyi⟩ | ⟨⟨hy, hge⟩, hyj⟩)
      · refine ⟨hy, ?_⟩
        simp only [not_or]
        exact ⟨hyi, by omega⟩
      · refine ⟨hy, ?_⟩
        simp only [not_or]
        exact ⟨by omega, hyj⟩
  have hdisj2 : Disjoint Gset tail := by
    rw [Set.disjoint_left]
    rintro y ⟨_, hlt, _⟩ ⟨⟨_, hge⟩, _⟩
    omega
  have hFSij : FS (Y \ {i, j}) = {n | ∃ p ∈ FS Gset, ∃ t ∈ Q, p + t = n} := by
    rw [hsplitij, FS_union_disjoint hdisj2]
  have hGbound : ∀ p ∈ FS Gset, p ≤ SG := by
    intro p hp
    rw [← hGcoe] at hp
    exact FS_finset_le hp
  intro N
  obtain ⟨q, hqQ, q', hq'Q, hNq, hqq', hbetween, hlen⟩ :=
    tail_gap hPfull hk2 hT1 hQunb hmiss N
  refine ⟨q + SG + 1, by omega, ?_⟩
  intro n hn1 hn2 hmem
  rw [hFSij] at hmem
  obtain ⟨p, hp, t, ht, hpt⟩ := hmem
  have hple : p ≤ SG := hGbound p hp
  rcases hbetween t ht with h | h
  · omega
  · omega

/-- Deletion extension. -/
theorem extension {X : Set ℕ} (hXinf : X.Infinite)
    (hpair : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → Complete (X \ {i, j}))
    {D : Finset ℕ} (hDX : ↑D ⊆ X) (hcomp : Complete (X \ ↑D)) :
    ∃ r ∈ X, r ∉ D ∧ Complete (X \ ↑(insert r D)) := by
  classical
  -- one-term deletions are complete, hence the slack of `X` diverges
  have hone : ∀ x ∈ X, Complete (X \ {x}) := by
    intro x hx
    obtain ⟨j, hjX, hj⟩ := hXinf.exists_gt x
    refine (hpair x hx j hjX (by omega)).mono ?_
    intro y hy
    obtain ⟨hyX, hyij⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hyij
    exact ⟨hyX, by simpa using hyij.1⟩
  have hslackX : SlackDiv X := slackDiv_of_one_deletions hXinf hone
  set Y := X \ (↑D : Set ℕ) with hYdef
  have hYinf : Y.Infinite := hcomp.infinite
  have hslackY : SlackDiv Y := slackDiv_diff_finite hslackX D
  obtain ⟨T₀, hT₀⟩ := hcomp
  set T := max T₀ 1 with hTdef
  have hT1 : 1 ≤ T := le_max_right _ _
  have hTFS : ∀ n, T ≤ n → n ∈ FS Y := fun n hn => hT₀ n (le_trans (le_max_left _ _) hn)
  obtain ⟨M₀, hcentral⟩ := central_interval hYinf hT1 hTFS hslackY
  by_contra hcon
  push_neg at hcon
  -- `Y` is deletion-minimal
  have hmin : ∀ r ∈ Y, ¬ Complete (Y \ {r}) := by
    intro r hr
    have hrX : r ∈ X := hr.1
    have hrD : r ∉ D := by simpa using hr.2
    have heq : X \ ↑(insert r D) = Y \ {r} := by
      rw [Finset.coe_insert]
      ext y
      simp only [hYdef, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
        Finset.mem_coe]
      tauto
    have := hcon r hrX hrD
    rwa [heq] at this
  set C := ∑ d ∈ D, d with hCdef
  obtain ⟨i, hiY, j, hjY, hij, hgaps⟩ := two_gap hYinf hmin hT1 hcentral C
  -- restoring `D` keeps arbitrarily large numbers missing
  have hsplit : X \ {i, j} = (Y \ {i, j}) ∪ (↑D : Set ℕ) := by
    ext y
    simp only [hYdef, Set.mem_diff, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro ⟨hy, hyij⟩
      by_cases hyD : y ∈ D
      · exact Or.inr hyD
      · exact Or.inl ⟨⟨hy, hyD⟩, hyij⟩
    · rintro (⟨⟨hy, hyD⟩, hyij⟩ | hyD)
      · exact ⟨hy, hyij⟩
      · refine ⟨?_, ?_⟩
        · exact hDX (by simpa using hyD)
        · have hiD : i ∉ D := by simpa using hiY.2
          have hjD : j ∉ D := by simpa using hjY.2
          rintro (rfl | rfl)
          · exact hiD hyD
          · exact hjD hyD
  have hdisj : Disjoint (Y \ {i, j}) (↑D : Set ℕ) := by
    rw [Set.disjoint_left]
    rintro y ⟨⟨_, hyD⟩, _⟩ hy
    exact hyD hy
  have hFS : FS (X \ {i, j}) = {n | ∃ p ∈ FS (Y \ {i, j}), ∃ t ∈ FS (↑D : Set ℕ), p + t = n} := by
    rw [hsplit, FS_union_disjoint hdisj]
  have hincomp : ¬ Complete (X \ {i, j}) := by
    rintro ⟨N, hN⟩
    obtain ⟨u, hu, hgap⟩ := hgaps N
    have hmem := hN (u + C) (by omega)
    rw [hFS] at hmem
    obtain ⟨p, hp, t, ht, hpt⟩ := hmem
    exact restore_gap (R := FS (Y \ {i, j})) (D := D) (u := u) (len := C + 1)
      (fun n h1 h2 => hgap n h1 (by omega)) (u + C) (by omega) (by omega) p hp t ht hpt
  exact hincomp (hpair i hiY.1 j hjY.1 hij)

/-- A complete deletion of any prescribed finite size. -/
theorem exists_deletion_card {X : Set ℕ} (hXinf : X.Infinite)
    (hpair : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → Complete (X \ {i, j})) (s : ℕ) :
    ∃ D : Finset ℕ, ↑D ⊆ X ∧ D.card = s ∧ Complete (X \ ↑D) := by
  classical
  induction s with
  | zero =>
      refine ⟨∅, by simp, by simp, ?_⟩
      obtain ⟨i, hiX, -⟩ := hXinf.exists_gt 0
      obtain ⟨j, hjX, hj⟩ := hXinf.exists_gt i
      have := hpair i hiX j hjX (by omega)
      have hsub : X \ {i, j} ⊆ X := Set.diff_subset
      simpa using this.mono hsub
  | succ s ih =>
      obtain ⟨D, hDX, hDcard, hDcomp⟩ := ih
      obtain ⟨r, hrX, hrD, hcomp⟩ := extension hXinf hpair hDX hDcomp
      refine ⟨insert r D, ?_, ?_, hcomp⟩
      · rw [Finset.coe_insert]
        exact Set.insert_subset hrX hDX
      · rw [Finset.card_insert_of_notMem hrD, hDcard]

/-! ### The main theorem -/

/-- **Main theorem.**  Let `A ⊆ ℕ` be nonempty and suppose that for all `a₁, a₂ ∈ A` every
sufficiently large natural number is a sum of a finite subset of `A \ {a₁, a₂}`.  Then for
every `s` there is an `s`-element subset `S ⊆ A` such that every sufficiently large natural
number is a sum of a finite subset of `A \ S`. -/
theorem main {A : Set ℕ} (hA : A.Nonempty)
    (h : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ B : Finset ℕ, ↑B ⊆ A \ {a₁, a₂} ∧ ∑ b ∈ B, b = n)
    (s : ℕ) :
    ∃ S : Finset ℕ, ↑S ⊆ A ∧ S.card = s ∧
      ∃ N : ℕ, ∀ n, N ≤ n → ∃ B : Finset ℕ, ↑B ⊆ A \ ↑S ∧ ∑ b ∈ B, b = n := by
  have hcomp : ∀ a₁ ∈ A, ∀ a₂ ∈ A, Complete (A \ {a₁, a₂}) := h
  obtain ⟨a, ha⟩ := hA
  have hAcomp : Complete A := (hcomp a ha a ha).mono Set.diff_subset
  have hAinf : A.Infinite := hAcomp.infinite
  obtain ⟨D, hDA, hDcard, hDcomp⟩ :=
    exists_deletion_card hAinf (fun i hi j hj _ => hcomp i hi j hj) s
  exact ⟨D, hDA, hDcard, hDcomp⟩

#print axioms main
